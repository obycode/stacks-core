// Copyright (C) 2025 Stacks Open Internet Foundation
//
// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
// You should have received a copy of the GNU General Public License
// along with this program.  If not, see <http://www.gnu.org/licenses/>.

use std::path::PathBuf;
use std::sync::Arc;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::time::{Duration, Instant};
use std::{fs, process, thread};

use clarity::types::chainstate::SortitionId;
use clarity::util::hash::{Sha512Trunc256Sum, to_hex};
use regex::Regex;
use rusqlite::{Connection, OpenFlags};
use stacks_common::types::chainstate::{BlockHeaderHash, StacksBlockId};
use stacks_common::types::sqlite::NO_PARAMS;
use stacks_common::util::hash::Hash160;
use stacks_common::util::vrf::VRFProof;
use stacks_common::{debug, info, warn};
use stackslib::burnchains::Burnchain;
use stackslib::chainstate::burn::ConsensusHash;
use stackslib::chainstate::burn::db::sortdb::{
    SortitionDB, SortitionHandleContext, get_ancestor_sort_id,
};
use stackslib::chainstate::coordinator::OnChainRewardSetProvider;
use stackslib::chainstate::nakamoto::miner::{
    BlockMetadata, NakamotoBlockBuilder, NakamotoTenureInfo,
};
use stackslib::chainstate::nakamoto::{NakamotoBlock, NakamotoChainState};
use stackslib::chainstate::stacks::db::blocks::DummyEventDispatcher;
use stackslib::chainstate::stacks::db::{
    ChainstateTx, StacksBlockHeaderTypes, StacksChainState, StacksHeaderInfo,
};
use stackslib::chainstate::stacks::miner::*;
use stackslib::chainstate::stacks::{Error as ChainstateError, *};
use stackslib::clarity_vm::clarity::ClarityInstance;
use stackslib::clarity_vm::database::GetTenureStartId;
use stackslib::config::{Config, ConfigFile, DEFAULT_MAINNET_CONFIG};
use stackslib::core::*;
use stackslib::cost_estimates::UnitEstimator;
use stackslib::cost_estimates::metrics::UnitMetric;
use stackslib::util_lib::db::IndexDBTx;

/// Options common to many `stacks-inspect` subcommands
/// Returned by `process_common_opts()`
#[derive(Debug, Default)]
pub struct CommonOpts {
    pub config: Option<Config>,
}

fn replay_block(
    sort_tx: IndexDBTx<SortitionHandleContext, SortitionId>,
    chainstate_tx: ChainstateTx,
    clarity_instance: &mut ClarityInstance,
    parent_header_info: &StacksHeaderInfo,
    parent_microblock_hash: &BlockHeaderHash,
    parent_microblock_seq: u16,
    block_id: &StacksBlockId,
    block: &StacksBlock,
    block_size: u64,
    block_consensus_hash: &ConsensusHash,
    block_hash: &BlockHeaderHash,
    block_commit_burn: u64,
    block_sortition_burn: u64,
) {
    replay_block_with_mode(
        sort_tx,
        chainstate_tx,
        clarity_instance,
        parent_header_info,
        parent_microblock_hash,
        parent_microblock_seq,
        block_id,
        block,
        block_size,
        block_consensus_hash,
        block_hash,
        block_commit_burn,
        block_sortition_burn,
        false,
    )
}

fn replay_block_ephemeral(
    sort_tx: IndexDBTx<SortitionHandleContext, SortitionId>,
    chainstate_tx: ChainstateTx,
    clarity_instance: &mut ClarityInstance,
    parent_header_info: &StacksHeaderInfo,
    parent_microblock_hash: &BlockHeaderHash,
    parent_microblock_seq: u16,
    block_id: &StacksBlockId,
    block: &StacksBlock,
    block_size: u64,
    block_consensus_hash: &ConsensusHash,
    block_hash: &BlockHeaderHash,
    block_commit_burn: u64,
    block_sortition_burn: u64,
) {
    replay_block_with_mode(
        sort_tx,
        chainstate_tx,
        clarity_instance,
        parent_header_info,
        parent_microblock_hash,
        parent_microblock_seq,
        block_id,
        block,
        block_size,
        block_consensus_hash,
        block_hash,
        block_commit_burn,
        block_sortition_burn,
        true,
    )
}

#[derive(Default, Clone)]
struct ReplayTimings {
    chainstate_open: Duration,
    sortdb_connect: Duration,
    staging_block_load: Duration,
    block_bytes_load: Duration,
    parent_lookup: Duration,
    append_block: Duration,
    total: Duration,
}

impl ReplayTimings {
    fn add_assign(&mut self, other: &ReplayTimings) {
        self.chainstate_open += other.chainstate_open;
        self.sortdb_connect += other.sortdb_connect;
        self.staging_block_load += other.staging_block_load;
        self.block_bytes_load += other.block_bytes_load;
        self.parent_lookup += other.parent_lookup;
        self.append_block += other.append_block;
        self.total += other.total;
    }
}

#[derive(Default)]
struct ReplayProfiler {
    fetch_duration: Duration,
    block_totals: ReplayTimings,
    blocks_processed: usize,
}

impl ReplayProfiler {
    fn maybe_enabled() -> Option<Self> {
        match std::env::var("VALIDATE_PROF") {
            Ok(val) if val == "0" || val.eq_ignore_ascii_case("false") => None,
            Ok(_) => Some(Self::default()),
            Err(_) => None,
        }
    }

    fn record_fetch(&mut self, duration: Duration) {
        self.fetch_duration += duration;
    }

    fn record_block(&mut self, timings: ReplayTimings) {
        self.blocks_processed += 1;
        self.block_totals.add_assign(&timings);
    }

    fn merge(&mut self, other: &ReplayProfiler) {
        self.fetch_duration += other.fetch_duration;
        self.block_totals.add_assign(&other.block_totals);
        self.blocks_processed += other.blocks_processed;
    }

    fn print_summary(&self, planned_blocks: usize) {
        if self.blocks_processed == 0 {
            println!(
                "[validate-block profiler] No blocks processed; fetch_time={:.3}s",
                self.fetch_duration.as_secs_f64()
            );
            return;
        }

        let blocks = self.blocks_processed as f64;
        let fmt = |d: Duration| -> f64 { d.as_secs_f64() * 1_000.0 };

        println!(
            "[validate-block profiler] planned_blocks={planned_blocks}, processed_blocks={}",
            self.blocks_processed
        );
        println!(
            "[validate-block profiler] fetch_index_ms={:.3}",
            fmt(self.fetch_duration)
        );
        println!(
            "[validate-block profiler] avg_ms_per_block: chainstate_open={:.3}, sortdb_connect={:.3}, staging_block_load={:.3}, block_bytes_load={:.3}, parent_lookup={:.3}, append_block={:.3}, total={:.3}",
            fmt(self.block_totals.chainstate_open) / blocks,
            fmt(self.block_totals.sortdb_connect) / blocks,
            fmt(self.block_totals.staging_block_load) / blocks,
            fmt(self.block_totals.block_bytes_load) / blocks,
            fmt(self.block_totals.parent_lookup) / blocks,
            fmt(self.block_totals.append_block) / blocks,
            fmt(self.block_totals.total) / blocks,
        );
    }
}

/// Process arguments common to many `stacks-inspect` subcommands and drain them from `argv`
///
/// Args:
///  - `argv`: Full CLI args `Vec`
///  - `start_at`: Position in args vec where to look for common options.
///    For example, if `start_at` is `1`, then look for these options **before** the subcommand:
///    ```console
///    stacks-inspect --config testnet.toml replay-block path/to/chainstate
///    ```
pub fn drain_common_opts(argv: &mut Vec<String>, start_at: usize) -> CommonOpts {
    let mut i = start_at;
    let mut opts = CommonOpts::default();
    while let Some(arg) = argv.get(i) {
        let (prefix, opt) = arg.split_at(2);
        if prefix != "--" {
            // No args left to take
            break;
        }
        // "Take" arg
        i += 1;
        match opt {
            "config" => {
                let path = &argv[i];
                i += 1;
                let config_file = ConfigFile::from_path(path).unwrap_or_else(|e| {
                    panic!("Failed to read '{path}' as stacks-node config: {e}")
                });
                let config = Config::from_config_file(config_file, false).unwrap_or_else(|e| {
                    panic!("Failed to convert config file into node config: {e}")
                });
                opts.config.replace(config);
            }
            "network" => {
                let network = &argv[i];
                i += 1;
                let config_file = match network.to_lowercase().as_str() {
                    "helium" => ConfigFile::helium(),
                    "mainnet" => ConfigFile::mainnet(),
                    "mocknet" => ConfigFile::mocknet(),
                    "xenon" => ConfigFile::xenon(),
                    other => {
                        eprintln!("Unknown network choice `{other}`");
                        process::exit(1);
                    }
                };
                let config = Config::from_config_file(config_file, false).unwrap_or_else(|e| {
                    panic!("Failed to convert config file into node config: {e}")
                });
                opts.config.replace(config);
            }
            _ => panic!("Unrecognized option: {opt}"),
        }
    }
    // Remove options processed
    argv.drain(start_at..i);
    opts
}

/// Replay blocks from chainstate database
/// Terminates on error using `process::exit()`
///
/// Arguments:
///  - `argv`: Args in CLI format: `<command-name> [args...]`
pub fn command_validate_block(argv: &[String], conf: Option<&Config>) {
    let print_help_and_exit = || -> ! {
        let n = &argv[0];
        eprintln!("Usage:");
        eprintln!("  {n} <database-path> [--threads N]");
        eprintln!("  {n} <database-path> [--threads N] prefix <index-block-hash-prefix>");
        eprintln!("  {n} <database-path> [--threads N] index-range <start-block> <end-block>");
        eprintln!("  {n} <database-path> [--threads N] range <start-block> <end-block>");
        eprintln!("  {n} <database-path> [--threads N] <first|last> <block-count>");
        process::exit(1);
    };
    let start = Instant::now();
    let db_path = argv.get(1).unwrap_or_else(|| print_help_and_exit());
    let mut thread_count = 1;
    let mut idx = 2;
    let mut mode_index: Option<usize> = None;
    while let Some(arg) = argv.get(idx) {
        if arg == "--threads" {
            let value = argv
                .get(idx + 1)
                .unwrap_or_else(|| print_help_and_exit())
                .parse::<usize>()
                .unwrap_or_else(|_| {
                    eprintln!("Invalid value for --threads: {}", argv[idx + 1]);
                    process::exit(1);
                });
            thread_count = value;
            idx += 2;
            continue;
        }
        mode_index = Some(idx);
        break;
    }
    let mode = mode_index.map(|i| argv[i].as_str());
    let mode_idx = mode_index.unwrap_or(idx);
    let staging_blocks_db_path = format!("{db_path}/chainstate/vm/index.sqlite");
    let conn =
        Connection::open_with_flags(&staging_blocks_db_path, OpenFlags::SQLITE_OPEN_READ_ONLY)
            .unwrap();

    let query = match mode {
        Some("prefix") => {
            let prefix = argv
                .get(mode_idx + 1)
                .unwrap_or_else(|| print_help_and_exit());
            format!(
                "SELECT index_block_hash FROM staging_blocks WHERE orphaned = 0 AND index_block_hash LIKE \"{}%\"",
                prefix
            )
        }
        Some("first") => {
            let limit = argv
                .get(mode_idx + 1)
                .unwrap_or_else(|| print_help_and_exit());
            format!(
                "SELECT index_block_hash FROM staging_blocks WHERE orphaned = 0 ORDER BY height ASC LIMIT {}",
                limit
            )
        }
        Some("range") => {
            let arg4 = argv
                .get(mode_idx + 1)
                .unwrap_or_else(|| print_help_and_exit())
                .parse::<u64>()
                .expect("<start_block> not a valid u64");
            let arg5 = argv
                .get(mode_idx + 2)
                .unwrap_or_else(|| print_help_and_exit())
                .parse::<u64>()
                .expect("<end-block> not a valid u64");
            let start = arg4.saturating_sub(1);
            let blocks = arg5.saturating_sub(arg4);
            format!(
                "SELECT index_block_hash FROM staging_blocks WHERE orphaned = 0 ORDER BY height ASC LIMIT {start}, {blocks}"
            )
        }
        Some("index-range") => {
            let start = argv
                .get(mode_idx + 1)
                .unwrap_or_else(|| print_help_and_exit())
                .parse::<u64>()
                .expect("<start_block> not a valid u64");
            let end = argv
                .get(mode_idx + 2)
                .unwrap_or_else(|| print_help_and_exit())
                .parse::<u64>()
                .expect("<end-block> not a valid u64");
            let blocks = end.saturating_sub(start);
            format!(
                "SELECT index_block_hash FROM staging_blocks WHERE orphaned = 0 ORDER BY index_block_hash ASC LIMIT {start}, {blocks}"
            )
        }
        Some("last") => {
            let limit = argv
                .get(mode_idx + 1)
                .unwrap_or_else(|| print_help_and_exit());
            format!(
                "SELECT index_block_hash FROM staging_blocks WHERE orphaned = 0 ORDER BY height DESC LIMIT {}",
                limit
            )
        }
        Some(_) => print_help_and_exit(),
        // Default to ALL blocks
        None => "SELECT index_block_hash FROM staging_blocks WHERE orphaned = 0".into(),
    };

    let fetch_start = Instant::now();
    let mut stmt = conn.prepare(&query).unwrap();
    let mut hashes_set = stmt.query(NO_PARAMS).unwrap();

    let mut index_block_hashes: Vec<String> = vec![];
    while let Ok(Some(row)) = hashes_set.next() {
        index_block_hashes.push(row.get(0).unwrap());
    }
    let fetch_duration = fetch_start.elapsed();

    let mut profiler = ReplayProfiler::maybe_enabled();
    if let Some(ref mut prof) = profiler {
        prof.record_fetch(fetch_duration);
    }

    let available_threads = thread::available_parallelism()
        .map(|n| n.get())
        .unwrap_or(1);
    if thread_count == 0 {
        thread_count = available_threads;
    }
    if thread_count > available_threads {
        thread_count = available_threads;
    }
    if thread_count == 1 {
        if let Ok(env_threads) = std::env::var("VALIDATE_THREADS") {
            if let Ok(val) = env_threads.parse::<usize>() {
                thread_count = if val == 0 {
                    available_threads
                } else {
                    val.min(available_threads).max(1)
                };
            }
        }
    }

    let index_block_hashes = Arc::new(index_block_hashes);
    let total = index_block_hashes.len();
    println!("Will check {total} blocks");

    let profiling_enabled = profiler.is_some();
    let conf_owned = conf.cloned();

    if thread_count <= 1 {
        let mut worker = StagingValidationWorker::new(db_path.as_str(), conf_owned.clone())
            .unwrap_or_else(|e| {
                eprintln!("Failed to initialize validator: {e}");
                process::exit(1);
            });
        for (i, index_block_hash) in index_block_hashes.iter().enumerate() {
            if i % 100 == 0 {
                println!("Checked {i}...");
            }
            let timings = worker.validate_block(index_block_hash, profiling_enabled);
            if let (Some(prof), Some(sample)) = (&mut profiler, timings) {
                prof.record_block(sample);
            }
        }
    } else {
        println!("Using {thread_count} threads (max {})", available_threads);
        let next_index = Arc::new(AtomicUsize::new(0));
        let processed = Arc::new(AtomicUsize::new(0));
        let db_path_arc = Arc::new(db_path.to_string());

        let handles: Vec<_> = (0..thread_count)
            .map(|_| {
                let hashes = Arc::clone(&index_block_hashes);
                let next = Arc::clone(&next_index);
                let processed_ctr = Arc::clone(&processed);
                let db_path = Arc::clone(&db_path_arc);
                let conf_clone = conf_owned.clone();

                thread::spawn(move || {
                    let mut worker = StagingValidationWorker::new(db_path.as_str(), conf_clone)
                        .unwrap_or_else(|e| {
                            eprintln!("Failed to initialize validator: {e}");
                            process::exit(1);
                        });
                    let mut local_profiler = profiling_enabled.then_some(ReplayProfiler::default());

                    loop {
                        let idx = next.fetch_add(1, Ordering::Relaxed);
                        if idx >= hashes.len() {
                            break;
                        }
                        let block_hash = &hashes[idx];
                        let timings = worker.validate_block(block_hash, profiling_enabled);
                        if let (Some(prof), Some(sample)) = (&mut local_profiler, timings) {
                            prof.record_block(sample);
                        }

                        let current = processed_ctr.fetch_add(1, Ordering::Relaxed) + 1;
                        if current % 100 == 0 {
                            println!("Checked {current}...");
                        }
                    }

                    local_profiler
                })
            })
            .collect();

        for handle in handles {
            if let Some(worker_profiler) = handle.join().unwrap() {
                if let Some(ref mut prof) = profiler {
                    prof.merge(&worker_profiler);
                }
            }
        }
    }
    println!("Finished. run_time_seconds = {}", start.elapsed().as_secs());

    if let Some(ref profiler) = profiler {
        profiler.print_summary(total);
    }
}

/// Replay blocks from chainstate database
/// Terminates on error using `process::exit()`
///
/// Arguments:
///  - `argv`: Args in CLI format: `<command-name> [args...]`
pub fn command_validate_block_nakamoto(argv: &[String], conf: Option<&Config>) {
    let print_help_and_exit = || -> ! {
        let n = &argv[0];
        eprintln!("Usage:");
        eprintln!("  {n} <database-path>");
        eprintln!("  {n} <database-path> prefix <index-block-hash-prefix>");
        eprintln!("  {n} <database-path> index-range <start-block> <end-block>");
        eprintln!("  {n} <database-path> range <start-block> <end-block>");
        eprintln!("  {n} <database-path> <first|last> <block-count>");
        process::exit(1);
    };
    let start = Instant::now();
    let db_path = argv.get(1).unwrap_or_else(|| print_help_and_exit());
    let mode = argv.get(2).map(String::as_str);

    let chain_state_path = format!("{db_path}/chainstate/");

    let conf = conf.unwrap_or(&DEFAULT_MAINNET_CONFIG);

    let (chainstate, _) = StacksChainState::open(
        conf.is_mainnet(),
        conf.burnchain.chain_id,
        &chain_state_path,
        None,
    )
    .unwrap();

    let conn = chainstate.nakamoto_blocks_db();

    let query = match mode {
        Some("prefix") => format!(
            "SELECT index_block_hash FROM nakamoto_staging_blocks WHERE orphaned = 0 AND index_block_hash LIKE \"{}%\"",
            argv[3]
        ),
        Some("first") => format!(
            "SELECT index_block_hash FROM nakamoto_staging_blocks WHERE orphaned = 0 ORDER BY height ASC LIMIT {}",
            argv[3]
        ),
        Some("range") => {
            let arg4 = argv[3]
                .parse::<u64>()
                .expect("<start_block> not a valid u64");
            let arg5 = argv[4].parse::<u64>().expect("<end-block> not a valid u64");
            let start = arg4.saturating_sub(1);
            let blocks = arg5.saturating_sub(arg4);
            format!(
                "SELECT index_block_hash FROM nakamoto_staging_blocks WHERE orphaned = 0 ORDER BY height ASC LIMIT {start}, {blocks}"
            )
        }
        Some("index-range") => {
            let start = argv[3]
                .parse::<u64>()
                .expect("<start_block> not a valid u64");
            let end = argv[4].parse::<u64>().expect("<end-block> not a valid u64");
            let blocks = end.saturating_sub(start);
            format!(
                "SELECT index_block_hash FROM nakamoto_staging_blocks WHERE orphaned = 0 ORDER BY index_block_hash ASC LIMIT {start}, {blocks}"
            )
        }
        Some("last") => format!(
            "SELECT index_block_hash FROM nakamoto_staging_blocks WHERE orphaned = 0 ORDER BY height DESC LIMIT {}",
            argv[3]
        ),
        Some(_) => print_help_and_exit(),
        // Default to ALL blocks
        None => "SELECT index_block_hash FROM nakamoto_staging_blocks WHERE orphaned = 0".into(),
    };

    let mut stmt = conn.prepare(&query).unwrap();
    let mut hashes_set = stmt.query(NO_PARAMS).unwrap();

    let mut index_block_hashes: Vec<String> = vec![];
    while let Ok(Some(row)) = hashes_set.next() {
        index_block_hashes.push(row.get(0).unwrap());
    }

    let total = index_block_hashes.len();
    println!("Will check {total} blocks");
    for (i, index_block_hash) in index_block_hashes.iter().enumerate() {
        if i % 100 == 0 {
            println!("Checked {i}...");
        }
        replay_naka_staging_block(db_path, index_block_hash, conf);
    }
    println!("Finished. run_time_seconds = {}", start.elapsed().as_secs());
}

/// Replay mock mined blocks from JSON files
/// Terminates on error using `process::exit()`
///
/// Arguments:
///  - `argv`: Args in CLI format: `<command-name> [args...]`
///  - `conf`: Optional config for running on non-mainnet chainstate
pub fn command_replay_mock_mining(argv: &[String], conf: Option<&Config>) {
    let print_help_and_exit = || -> ! {
        let n = &argv[0];
        eprintln!("Usage:");
        eprintln!("  {n} <database-path> <mock-mined-blocks-path>");
        process::exit(1);
    };

    // Process CLI args
    let db_path = argv.get(1).unwrap_or_else(|| print_help_and_exit());

    let blocks_path = argv
        .get(2)
        .map(PathBuf::from)
        .map(fs::canonicalize)
        .transpose()
        .unwrap_or_else(|e| panic!("Not a valid path: {e}"))
        .unwrap_or_else(|| print_help_and_exit());

    // Validate directory path
    if !blocks_path.is_dir() {
        panic!("{blocks_path:?} is not a valid directory");
    }

    // Read entries in directory
    let dir_entries = blocks_path
        .read_dir()
        .unwrap_or_else(|e| panic!("Failed to read {blocks_path:?}: {e}"))
        .filter_map(|e| e.ok());

    // Get filenames, filtering out anything that isn't a regular file
    let filenames = dir_entries.filter_map(|e| match e.file_type() {
        Ok(t) if t.is_file() => e.file_name().into_string().ok(),
        _ => None,
    });

    // Get vec of (block_height, filename), to prepare for sorting
    //
    // NOTE: Trusting the filename is not ideal. We could sort on data read from the file,
    // but that requires reading all files
    let re = Regex::new(r"^([0-9]+)\.json$").unwrap();
    let mut indexed_files = filenames
        .filter_map(|filename| {
            // Use regex to extract block number from filename
            let Some(cap) = re.captures(&filename) else {
                debug!("Regex capture failed on {filename}");
                return None;
            };
            // cap.get(0) return entire filename
            // cap.get(1) return block number
            let i = 1;
            let Some(m) = cap.get(i) else {
                debug!("cap.get({i}) failed on {filename} match");
                return None;
            };
            let Ok(bh) = m.as_str().parse::<u64>() else {
                debug!("parse::<u64>() failed on '{}'", m.as_str());
                return None;
            };
            Some((bh, filename))
        })
        .collect::<Vec<_>>();

    // Sort by block height
    indexed_files.sort_by_key(|(bh, _)| *bh);

    if indexed_files.is_empty() {
        panic!("No block files found in {blocks_path:?}");
    }

    info!(
        "Replaying {} blocks starting at {}",
        indexed_files.len(),
        indexed_files[0].0
    );

    for (bh, filename) in indexed_files {
        let filepath = blocks_path.join(filename);
        let block = AssembledAnchorBlock::deserialize_from_file(&filepath)
            .unwrap_or_else(|e| panic!("Error reading block {bh} from file: {e}"));
        info!("Replaying block from {filepath:?}";
            "block_height" => bh,
            "block" => ?block
        );
        replay_mock_mined_block(db_path, block, conf);
    }
}

/// Replay mock mined blocks from JSON files
/// Terminates on error using `process::exit()`
///
/// Arguments:
///  - `argv`: Args in CLI format: `<command-name> [args...]`
///  - `conf`: Optional config for running on non-mainnet chainstate
pub fn command_try_mine(argv: &[String], conf: Option<&Config>) {
    let print_help_and_exit = || {
        let n = &argv[0];
        eprintln!("Usage: {n} <working-dir> [min-fee [max-time]]");
        eprintln!("");
        eprintln!(
            "Given a <working-dir>, try to ''mine'' an anchored block. This invokes the miner block"
        );
        eprintln!(
            "assembly, but does not attempt to broadcast a block commit. This is useful for determining"
        );
        eprintln!("what transactions a given chain state would include in an anchor block,");
        eprintln!("or otherwise simulating a miner.");
        process::exit(1);
    };

    // Parse subcommand-specific args
    let db_path = argv.get(1).unwrap_or_else(print_help_and_exit);
    let min_fee = argv
        .get(2)
        .map(|arg| arg.parse().expect("Could not parse min_fee"))
        .unwrap_or(u64::MAX);
    let max_time = argv
        .get(3)
        .map(|arg| arg.parse().expect("Could not parse max_time"))
        .unwrap_or(u64::MAX);

    let start = Instant::now();

    let conf = conf.unwrap_or(&DEFAULT_MAINNET_CONFIG);

    let burnchain_path = format!("{db_path}/burnchain");
    let sort_db_path = format!("{db_path}/burnchain/sortition");
    let chain_state_path = format!("{db_path}/chainstate/");

    let burnchain = conf.get_burnchain();
    let sort_db = SortitionDB::open(&sort_db_path, false, burnchain.pox_constants.clone())
        .unwrap_or_else(|e| panic!("Failed to open {sort_db_path}: {e}"));
    let (chainstate, _) = StacksChainState::open(
        conf.is_mainnet(),
        conf.burnchain.chain_id,
        &chain_state_path,
        None,
    )
    .unwrap_or_else(|e| panic!("Failed to open stacks chain state: {e}"));
    let chain_tip = SortitionDB::get_canonical_burn_chain_tip(sort_db.conn())
        .unwrap_or_else(|e| panic!("Failed to get sortition chain tip: {e}"));

    let estimator = Box::new(UnitEstimator);
    let metric = Box::new(UnitMetric);

    let mut mempool_db = MemPoolDB::open(
        conf.is_mainnet(),
        conf.burnchain.chain_id,
        &chain_state_path,
        estimator,
        metric,
    )
    .unwrap_or_else(|e| panic!("Failed to open mempool db: {e}"));

    // Parent Stacks header for block we are going to mine
    let parent_stacks_header =
        NakamotoChainState::get_canonical_block_header(chainstate.db(), &sort_db)
            .unwrap_or_else(|e| panic!("Error looking up chain tip: {e}"))
            .expect("No chain tip found");

    let burn_dbconn = sort_db.index_handle(&chain_tip.sortition_id);

    let mut settings = BlockBuilderSettings::limited();
    settings.max_miner_time_ms = max_time;

    let result = match &parent_stacks_header.anchored_header {
        StacksBlockHeaderTypes::Epoch2(..) => {
            let sk = StacksPrivateKey::random();
            let mut tx_auth = TransactionAuth::from_p2pkh(&sk).unwrap();
            tx_auth.set_origin_nonce(0);

            let mut coinbase_tx = StacksTransaction::new(
                TransactionVersion::Mainnet,
                tx_auth,
                TransactionPayload::Coinbase(CoinbasePayload([0u8; 32]), None, None),
            );

            coinbase_tx.chain_id = conf.burnchain.chain_id;
            coinbase_tx.anchor_mode = TransactionAnchorMode::OnChainOnly;
            let mut tx_signer = StacksTransactionSigner::new(&coinbase_tx);
            tx_signer.sign_origin(&sk).unwrap();
            let coinbase_tx = tx_signer.get_tx().unwrap();

            StacksBlockBuilder::build_anchored_block(
                &chainstate,
                &burn_dbconn,
                &mut mempool_db,
                &parent_stacks_header,
                chain_tip.total_burn,
                &VRFProof::empty(),
                &Hash160([0; 20]),
                &coinbase_tx,
                settings,
                None,
                &Burnchain::new(
                    &burnchain_path,
                    &burnchain.chain_name,
                    &burnchain.network_name,
                )
                .unwrap_or_else(|e| panic!("Failed to instantiate burnchain: {e}")),
            )
            .map(|(block, cost, size)| (block.block_hash(), block.txs, cost, size))
        }
        StacksBlockHeaderTypes::Nakamoto(..) => {
            NakamotoBlockBuilder::build_nakamoto_block(
                &chainstate,
                &burn_dbconn,
                &mut mempool_db,
                &parent_stacks_header,
                // tenure ID consensus hash of this block
                &parent_stacks_header.consensus_hash,
                // the burn so far on the burnchain (i.e. from the last burnchain block)
                chain_tip.total_burn,
                NakamotoTenureInfo::default(),
                settings,
                None,
                0,
                &[],
            )
            .map(
                |BlockMetadata {
                     block,
                     tenure_consumed,
                     tenure_size,
                     ..
                 }| {
                    (
                        block.header.block_hash(),
                        block.txs,
                        tenure_consumed,
                        tenure_size,
                    )
                },
            )
        }
    };

    let elapsed = start.elapsed();
    let summary = format!(
        "block @ height = {h} off of {pid} ({pch}/{pbh}) in {t}ms. Min-fee: {min_fee}, Max-time: {max_time}",
        h = parent_stacks_header.stacks_block_height + 1,
        pid = &parent_stacks_header.index_block_hash(),
        pch = &parent_stacks_header.consensus_hash,
        pbh = &parent_stacks_header.anchored_header.block_hash(),
        t = elapsed.as_millis(),
    );

    let code = match result {
        Ok((block_hash, txs, cost, size)) => {
            let total_fees: u64 = txs.iter().map(|tx| tx.get_tx_fee()).sum();

            println!("Successfully mined {summary}");
            println!("Block {block_hash}: {total_fees} uSTX, {size} bytes, cost {cost:?}");
            0
        }
        Err(e) => {
            println!("Failed to mine {summary}");
            println!("Error: {e}");
            1
        }
    };

    process::exit(code);
}

/// Compute the contract hash for a given contract
///
/// Arguments:
///  - `argv`: Args in CLI format: `<command-name> [args...]`
pub fn command_contract_hash(argv: &[String], _conf: Option<&Config>) {
    let print_help_and_exit = || -> ! {
        let n = &argv[0];
        eprintln!("Usage:");
        eprintln!("  {n} <path-to-contract>");
        process::exit(1);
    };

    // Process CLI args
    let contract_path = argv.get(1).unwrap_or_else(|| print_help_and_exit());
    let contract_source = fs::read_to_string(contract_path)
        .unwrap_or_else(|e| panic!("Failed to read contract file {contract_path:?}: {e}"));

    let hash = Sha512Trunc256Sum::from_data(contract_source.as_bytes());
    let hex_string = to_hex(hash.as_bytes());
    println!("Contract hash for {contract_path}:\n{hex_string}");
}

/// Fetch and process `StagingBlock`s using reusable database handles.
struct StagingValidationWorker {
    chainstate: StacksChainState,
    sortdb: SortitionDB,
    blocks_path: String,
}

impl StagingValidationWorker {
    fn new(db_path: &str, conf: Option<Config>) -> Result<Self, String> {
        let conf = conf.unwrap_or_else(|| (*DEFAULT_MAINNET_CONFIG).clone());
        let chain_state_path = format!("{db_path}/chainstate/");
        let sort_db_path = format!("{db_path}/burnchain/sortition");

        let (chainstate, _) = StacksChainState::open(
            conf.is_mainnet(),
            conf.burnchain.chain_id,
            &chain_state_path,
            None,
        )
        .map_err(|e| format!("Failed to open Stacks chainstate: {e:?}"))?;

        let burnchain = conf.get_burnchain();
        let epochs = conf.burnchain.get_epoch_list();
        let sortdb = SortitionDB::connect(
            &sort_db_path,
            burnchain.first_block_height,
            &burnchain.first_block_hash,
            u64::from(burnchain.first_block_timestamp),
            &epochs,
            burnchain.pox_constants.clone(),
            None,
            true,
        )
        .map_err(|e| format!("Failed to connect SortitionDB: {e:?}"))?;

        Ok(Self {
            blocks_path: chainstate.blocks_path.clone(),
            chainstate,
            sortdb,
        })
    }

    fn validate_block(
        &mut self,
        index_block_hash_hex: &str,
        profiling: bool,
    ) -> Option<ReplayTimings> {
        let block_id = StacksBlockId::from_hex(index_block_hash_hex).unwrap();

        let total_start = Instant::now();
        let mut timings = profiling.then_some(ReplayTimings::default());

        let chainstate_start = Instant::now();
        let (mut chainstate_tx, clarity_instance) = self
            .chainstate
            .chainstate_tx_begin()
            .expect("Failed to start chainstate tx");
        if let Some(ref mut sample) = timings {
            sample.chainstate_open = chainstate_start.elapsed();
        }

        let staging_load_start = Instant::now();
        let mut next_staging_block =
            StacksChainState::load_staging_block_info(&chainstate_tx.tx, &block_id)
                .expect("Failed to load staging block data")
                .expect("No such index block hash in block database");
        if let Some(ref mut sample) = timings {
            sample.staging_block_load = staging_load_start.elapsed();
        }

        let block_bytes_start = Instant::now();
        next_staging_block.block_data = StacksChainState::load_block_bytes(
            &self.blocks_path,
            &next_staging_block.consensus_hash,
            &next_staging_block.anchored_block_hash,
        )
        .unwrap()
        .unwrap_or_default();
        if let Some(ref mut sample) = timings {
            sample.block_bytes_load = block_bytes_start.elapsed();
        }

        let parent_lookup_start = Instant::now();
        let Some(parent_header_info) =
            StacksChainState::get_parent_header_info(&mut chainstate_tx, &next_staging_block)
                .unwrap()
        else {
            println!("Failed to load parent head info for block: {index_block_hash_hex}");
            if let Some(ref mut sample) = timings {
                sample.total = total_start.elapsed();
            }
            return timings;
        };
        if let Some(ref mut sample) = timings {
            sample.parent_lookup = parent_lookup_start.elapsed();
        }

        let sortdb_start = Instant::now();
        let sort_tx = self.sortdb.tx_begin_at_tip();
        if let Some(ref mut sample) = timings {
            sample.sortdb_connect = sortdb_start.elapsed();
        }

        let block = StacksChainState::extract_stacks_block(&next_staging_block)
            .expect("Failed to get block");
        let block_size = next_staging_block.block_data.len() as u64;

        let append_start = Instant::now();
        replay_block_ephemeral(
            sort_tx,
            chainstate_tx,
            clarity_instance,
            &parent_header_info,
            &next_staging_block.parent_microblock_hash,
            next_staging_block.parent_microblock_seq,
            &block_id,
            &block,
            block_size,
            &next_staging_block.consensus_hash,
            &next_staging_block.anchored_block_hash,
            next_staging_block.commit_burn,
            next_staging_block.sortition_burn,
        );
        if let Some(ref mut sample) = timings {
            sample.append_block = append_start.elapsed();
            sample.total = total_start.elapsed();
        }

        timings
    }
}

/// Process a mock mined block and call `replay_block()` to validate
fn replay_mock_mined_block(db_path: &str, block: AssembledAnchorBlock, conf: Option<&Config>) {
    let chain_state_path = format!("{db_path}/chainstate/");
    let sort_db_path = format!("{db_path}/burnchain/sortition");

    let conf = conf.unwrap_or(&DEFAULT_MAINNET_CONFIG);

    let (mut chainstate, _) = StacksChainState::open(
        conf.is_mainnet(),
        conf.burnchain.chain_id,
        &chain_state_path,
        None,
    )
    .unwrap();

    let burnchain = conf.get_burnchain();
    let epochs = conf.burnchain.get_epoch_list();
    let mut sortdb = SortitionDB::connect(
        &sort_db_path,
        burnchain.first_block_height,
        &burnchain.first_block_hash,
        u64::from(burnchain.first_block_timestamp),
        &epochs,
        burnchain.pox_constants.clone(),
        None,
        true,
    )
    .unwrap();
    let sort_tx = sortdb.tx_begin_at_tip();

    let (chainstate_tx, clarity_instance) = chainstate
        .chainstate_tx_begin()
        .expect("Failed to start chainstate tx");

    let block_consensus_hash = &block.consensus_hash;
    let block_hash = block.anchored_block.block_hash();
    let block_id = StacksBlockId::new(block_consensus_hash, &block_hash);
    let block_size = block
        .anchored_block
        .block_size()
        .map(u64::try_from)
        .unwrap_or_else(|e| panic!("Error serializing block {block_hash}: {e}"))
        .expect("u64 overflow");

    let Some(parent_header_info) = StacksChainState::get_anchored_block_header_info(
        &chainstate_tx,
        &block.parent_consensus_hash,
        &block.anchored_block.header.parent_block,
    )
    .unwrap() else {
        println!("Failed to load parent head info for block: {block_hash}");
        return;
    };

    replay_block(
        sort_tx,
        chainstate_tx,
        clarity_instance,
        &parent_header_info,
        &block.anchored_block.header.parent_microblock,
        block.anchored_block.header.parent_microblock_sequence,
        &block_id,
        &block.anchored_block,
        block_size,
        block_consensus_hash,
        &block_hash,
        // I think the burn is used for miner rewards but not necessary for validation
        0,
        0,
    );
}

/// Validate a block against chainstate
fn replay_block_with_mode(
    mut sort_tx: IndexDBTx<SortitionHandleContext, SortitionId>,
    mut chainstate_tx: ChainstateTx,
    clarity_instance: &mut ClarityInstance,
    parent_header_info: &StacksHeaderInfo,
    parent_microblock_hash: &BlockHeaderHash,
    parent_microblock_seq: u16,
    block_id: &StacksBlockId,
    block: &StacksBlock,
    block_size: u64,
    block_consensus_hash: &ConsensusHash,
    block_hash: &BlockHeaderHash,
    block_commit_burn: u64,
    block_sortition_burn: u64,
    use_ephemeral: bool,
) {
    let parent_block_header = match &parent_header_info.anchored_header {
        StacksBlockHeaderTypes::Epoch2(bh) => bh,
        StacksBlockHeaderTypes::Nakamoto(_) => panic!("Nakamoto blocks not supported yet"),
    };
    let parent_block_hash = parent_block_header.block_hash();

    let Some(cost) =
        StacksChainState::get_stacks_block_anchored_cost(chainstate_tx.conn(), block_id).unwrap()
    else {
        println!("No header info found for {block_id}");
        return;
    };

    let Some(next_microblocks) = StacksChainState::inner_find_parent_microblock_stream(
        &chainstate_tx.tx,
        block_hash,
        &parent_block_hash,
        &parent_header_info.consensus_hash,
        parent_microblock_hash,
        parent_microblock_seq,
    )
    .unwrap() else {
        println!("No microblock stream found for {block_id}");
        return;
    };

    let (burn_header_hash, burn_header_height, burn_header_timestamp, _winning_block_txid) =
        match SortitionDB::get_block_snapshot_consensus(&sort_tx, block_consensus_hash).unwrap() {
            Some(sn) => (
                sn.burn_header_hash,
                sn.block_height as u32,
                sn.burn_header_timestamp,
                sn.winning_block_txid,
            ),
            None => {
                // shouldn't happen
                panic!(
                    "CORRUPTION: staging block {block_consensus_hash}/{block_hash} does not correspond to a burn block"
                );
            }
        };

    info!(
        "Process block {}/{} = {} in burn block {}, parent microblock {}",
        block_consensus_hash, block_hash, &block_id, &burn_header_hash, parent_microblock_hash,
    );

    if !StacksChainState::check_block_attachment(parent_block_header, &block.header) {
        let msg = format!(
            "Invalid stacks block {}/{} -- does not attach to parent {}/{}",
            block_consensus_hash,
            block.block_hash(),
            parent_block_header.block_hash(),
            &parent_header_info.consensus_hash
        );
        println!("{msg}");
        return;
    }

    // validation check -- validate parent microblocks and find the ones that connect the
    // block's parent to this block.
    let next_microblocks = StacksChainState::extract_connecting_microblocks(
        parent_header_info,
        block_consensus_hash,
        block_hash,
        block,
        next_microblocks,
    )
    .unwrap();
    let (last_microblock_hash, last_microblock_seq) = match next_microblocks.len() {
        0 => (EMPTY_MICROBLOCK_PARENT_HASH.clone(), 0),
        _ => {
            let l = next_microblocks.len();
            (
                next_microblocks[l - 1].block_hash(),
                next_microblocks[l - 1].header.sequence,
            )
        }
    };
    assert_eq!(*parent_microblock_hash, last_microblock_hash);
    assert_eq!(parent_microblock_seq, last_microblock_seq);

    let pox_constants = sort_tx.context.pox_constants.clone();

    let append_result = if use_ephemeral {
        StacksChainState::append_block_ephemeral(
            &mut chainstate_tx,
            clarity_instance,
            &mut sort_tx,
            &pox_constants,
            parent_header_info,
            block_consensus_hash,
            &burn_header_hash,
            burn_header_height,
            burn_header_timestamp,
            block,
            block_size,
            &next_microblocks,
            block_commit_burn,
            block_sortition_burn,
            true,
        )
    } else {
        StacksChainState::append_block(
            &mut chainstate_tx,
            clarity_instance,
            &mut sort_tx,
            &pox_constants,
            parent_header_info,
            block_consensus_hash,
            &burn_header_hash,
            burn_header_height,
            burn_header_timestamp,
            block,
            block_size,
            &next_microblocks,
            block_commit_burn,
            block_sortition_burn,
            true,
        )
    };

    match append_result {
        Ok((receipt, _, _)) => {
            if receipt.anchored_block_cost != cost {
                println!(
                    "Failed processing block! block = {block_id}. Unexpected cost. expected = {cost}, evaluated = {}",
                    receipt.anchored_block_cost
                );
                process::exit(1);
            }

            info!("Block processed successfully! block = {block_id}");
        }
        Err(e) => {
            println!("Failed processing block! block = {block_id}, error = {e:?}");
            process::exit(1);
        }
    };
}

/// Fetch and process a NakamotoBlock from database and call `replay_block_nakamoto()` to validate
fn replay_naka_staging_block(db_path: &str, index_block_hash_hex: &str, conf: &Config) {
    let block_id = StacksBlockId::from_hex(index_block_hash_hex).unwrap();
    let chain_state_path = format!("{db_path}/chainstate/");
    let sort_db_path = format!("{db_path}/burnchain/sortition");

    let (mut chainstate, _) = StacksChainState::open(
        conf.is_mainnet(),
        conf.burnchain.chain_id,
        &chain_state_path,
        None,
    )
    .unwrap();

    let burnchain = conf.get_burnchain();
    let epochs = conf.burnchain.get_epoch_list();
    let mut sortdb = SortitionDB::connect(
        &sort_db_path,
        burnchain.first_block_height,
        &burnchain.first_block_hash,
        u64::from(burnchain.first_block_timestamp),
        &epochs,
        burnchain.pox_constants.clone(),
        None,
        true,
    )
    .unwrap();

    let (block, block_size) = chainstate
        .nakamoto_blocks_db()
        .get_nakamoto_block(&block_id)
        .unwrap()
        .unwrap();
    replay_block_nakamoto(&mut sortdb, &mut chainstate, &block, block_size).unwrap();
}

fn replay_block_nakamoto(
    sort_db: &mut SortitionDB,
    stacks_chain_state: &mut StacksChainState,
    block: &NakamotoBlock,
    block_size: u64,
) -> Result<(), ChainstateError> {
    // find corresponding snapshot
    let next_ready_block_snapshot =
        SortitionDB::get_block_snapshot_consensus(sort_db.conn(), &block.header.consensus_hash)?
            .unwrap_or_else(|| {
                panic!(
                    "CORRUPTION: staging Nakamoto block {}/{} does not correspond to a burn block",
                    &block.header.consensus_hash,
                    &block.header.block_hash()
                )
            });

    info!("Process staging Nakamoto block";
           "consensus_hash" => %block.header.consensus_hash,
           "stacks_block_hash" => %block.header.block_hash(),
           "stacks_block_id" => %block.header.block_id(),
           "burn_block_hash" => %next_ready_block_snapshot.burn_header_hash
    );

    let Some(mut expected_total_tenure_cost) = NakamotoChainState::get_total_tenure_cost_at(
        stacks_chain_state.db(),
        &block.header.block_id(),
    )
    .unwrap() else {
        println!("Failed to find cost for block {}", block.header.block_id());
        return Ok(());
    };

    let expected_cost = if block.get_tenure_tx_payload().is_some() {
        expected_total_tenure_cost
    } else {
        let Some(expected_parent_total_tenure_cost) = NakamotoChainState::get_total_tenure_cost_at(
            stacks_chain_state.db(),
            &block.header.parent_block_id,
        )
        .unwrap() else {
            println!(
                "Failed to find cost for parent of block {}",
                block.header.block_id()
            );
            return Ok(());
        };
        expected_total_tenure_cost.sub(&expected_parent_total_tenure_cost).expect("FATAL: failed to subtract parent total cost from self total cost in non-tenure-changing block");
        expected_total_tenure_cost
    };

    let elected_height = sort_db
        .get_consensus_hash_height(&block.header.consensus_hash)?
        .ok_or_else(|| ChainstateError::NoSuchBlockError)?;
    let elected_in_cycle = sort_db
        .pox_constants
        .block_height_to_reward_cycle(sort_db.first_block_height, elected_height)
        .ok_or_else(|| {
            ChainstateError::InvalidStacksBlock(
                "Elected in block height before first_block_height".into(),
            )
        })?;
    let active_reward_set = OnChainRewardSetProvider::<DummyEventDispatcher>(None)
        .read_reward_set_nakamoto_of_cycle(
            elected_in_cycle,
            stacks_chain_state,
            sort_db,
            &block.header.parent_block_id,
            true,
        )
        .map_err(|e| {
            warn!(
                "Cannot process Nakamoto block: could not load reward set that elected the block";
                "err" => ?e,
                "consensus_hash" => %block.header.consensus_hash,
                "stacks_block_hash" => %block.header.block_hash(),
                "stacks_block_id" => %block.header.block_id(),
                "parent_block_id" => %block.header.parent_block_id,
            );
            ChainstateError::NoSuchBlockError
        })?;
    let (mut chainstate_tx, clarity_instance) = stacks_chain_state.chainstate_tx_begin()?;

    // find parent header
    let Some(parent_header_info) =
        NakamotoChainState::get_block_header(&chainstate_tx.tx, &block.header.parent_block_id)?
    else {
        // no parent; cannot process yet
        info!("Cannot process Nakamoto block: missing parent header";
               "consensus_hash" => %block.header.consensus_hash,
               "stacks_block_hash" => %block.header.block_hash(),
               "stacks_block_id" => %block.header.block_id(),
               "parent_block_id" => %block.header.parent_block_id
        );
        return Ok(());
    };

    // sanity check -- must attach to parent
    let parent_block_id = StacksBlockId::new(
        &parent_header_info.consensus_hash,
        &parent_header_info.anchored_header.block_hash(),
    );
    if parent_block_id != block.header.parent_block_id {
        drop(chainstate_tx);

        let msg = "Discontinuous Nakamoto Stacks block";
        warn!("{}", &msg;
              "child parent_block_id" => %block.header.parent_block_id,
              "expected parent_block_id" => %parent_block_id,
              "consensus_hash" => %block.header.consensus_hash,
              "stacks_block_hash" => %block.header.block_hash(),
              "stacks_block_id" => %block.header.block_id()
        );
        return Err(ChainstateError::InvalidStacksBlock(msg.into()));
    }

    // set the sortition handle's pointer to the block's burnchain view.
    //   this is either:
    //    (1)  set by the tenure change tx if one exists
    //    (2)  the same as parent block id

    let burnchain_view = if let Some(tenure_change) = block.get_tenure_tx_payload() {
        if let Some(ref parent_burn_view) = parent_header_info.burn_view {
            // check that the tenure_change's burn view descends from the parent
            let parent_burn_view_sn = SortitionDB::get_block_snapshot_consensus(
                sort_db.conn(),
                parent_burn_view,
            )?
            .ok_or_else(|| {
                warn!(
                    "Cannot process Nakamoto block: could not find parent block's burnchain view";
                    "consensus_hash" => %block.header.consensus_hash,
                    "stacks_block_hash" => %block.header.block_hash(),
                    "stacks_block_id" => %block.header.block_id(),
                    "parent_block_id" => %block.header.parent_block_id
                );
                ChainstateError::InvalidStacksBlock(
                    "Failed to load burn view of parent block ID".into(),
                )
            })?;
            let handle = sort_db.index_handle_at_ch(&tenure_change.burn_view_consensus_hash)?;
            let connected_sort_id = get_ancestor_sort_id(
                &handle,
                parent_burn_view_sn.block_height,
                &handle.context.chain_tip,
            )?
            .ok_or_else(|| {
                warn!(
                    "Cannot process Nakamoto block: could not find parent block's burnchain view";
                    "consensus_hash" => %block.header.consensus_hash,
                    "stacks_block_hash" => %block.header.block_hash(),
                    "stacks_block_id" => %block.header.block_id(),
                    "parent_block_id" => %block.header.parent_block_id
                );
                ChainstateError::InvalidStacksBlock(
                    "Failed to load burn view of parent block ID".into(),
                )
            })?;
            if connected_sort_id != parent_burn_view_sn.sortition_id {
                warn!(
                    "Cannot process Nakamoto block: parent block's burnchain view does not connect to own burn view";
                    "consensus_hash" => %block.header.consensus_hash,
                    "stacks_block_hash" => %block.header.block_hash(),
                    "stacks_block_id" => %block.header.block_id(),
                    "parent_block_id" => %block.header.parent_block_id
                );
                return Err(ChainstateError::InvalidStacksBlock(
                    "Does not connect to burn view of parent block ID".into(),
                ));
            }
        }
        &tenure_change.burn_view_consensus_hash
    } else {
        parent_header_info.burn_view.as_ref().ok_or_else(|| {
                warn!(
                    "Cannot process Nakamoto block: parent block does not have a burnchain view and current block has no tenure tx";
                    "consensus_hash" => %block.header.consensus_hash,
                    "stacks_block_hash" => %block.header.block_hash(),
                    "stacks_block_id" => %block.header.block_id(),
                    "parent_block_id" => %block.header.parent_block_id
                );
                ChainstateError::InvalidStacksBlock("Failed to load burn view of parent block ID".into())
            })?
    };
    let Some(burnchain_view_sn) =
        SortitionDB::get_block_snapshot_consensus(sort_db.conn(), burnchain_view)?
    else {
        // This should be checked already during block acceptance and parent block processing
        //   - The check for expected burns returns `NoSuchBlockError` if the burnchain view
        //      could not be found for a block with a tenure tx.
        // We error here anyways, but the check during block acceptance makes sure that the staging
        //  db doesn't get into a situation where it continuously tries to retry such a block (because
        //  such a block shouldn't land in the staging db).
        warn!(
            "Cannot process Nakamoto block: failed to find Sortition ID associated with burnchain view";
            "consensus_hash" => %block.header.consensus_hash,
            "stacks_block_hash" => %block.header.block_hash(),
            "stacks_block_id" => %block.header.block_id(),
            "burn_view_consensus_hash" => %burnchain_view,
        );
        return Ok(());
    };

    // find commit and sortition burns if this is a tenure-start block
    let new_tenure = block.is_wellformed_tenure_start_block()?;
    let (commit_burn, sortition_burn) = if new_tenure {
        // find block-commit to get commit-burn
        let block_commit = SortitionDB::get_block_commit(
            sort_db.conn(),
            &next_ready_block_snapshot.winning_block_txid,
            &next_ready_block_snapshot.sortition_id,
        )?
        .expect("FATAL: no block-commit for tenure-start block");

        let sort_burn =
            SortitionDB::get_block_burn_amount(sort_db.conn(), &next_ready_block_snapshot)?;
        (block_commit.burn_fee, sort_burn)
    } else {
        (0, 0)
    };

    // attach the block to the chain state and calculate the next chain tip.
    let pox_constants = sort_db.pox_constants.clone();

    // NOTE: because block status is updated in a separate transaction, we need `chainstate_tx`
    // and `clarity_instance` to go out of scope before we can issue the it (since we need a
    // mutable reference to `stacks_chain_state` to start it).  This means ensuring that, in the
    // `Ok(..)` case, the `clarity_commit` gets dropped beforehand.  In order to do this, we first
    // run `::append_block()` here, and capture both the Ok(..) and Err(..) results as
    // Option<..>'s.  Then, if we errored, we can explicitly drop the `Ok(..)` option (even
    // though it will always be None), which gets the borrow-checker to believe that it's safe
    // to access `stacks_chain_state` again.  In the `Ok(..)` case, it's instead sufficient so
    // simply commit the block before beginning the second transaction to mark it processed.
    let block_id = block.block_id();
    let mut burn_view_handle = sort_db.index_handle(&burnchain_view_sn.sortition_id);
    let (ok_opt, err_opt) = match NakamotoChainState::append_block(
        &mut chainstate_tx,
        clarity_instance,
        &mut burn_view_handle,
        &burnchain_view,
        &pox_constants,
        &parent_header_info,
        &next_ready_block_snapshot.burn_header_hash,
        next_ready_block_snapshot
            .block_height
            .try_into()
            .expect("Failed to downcast u64 to u32"),
        next_ready_block_snapshot.burn_header_timestamp,
        block,
        block_size,
        commit_burn,
        sortition_burn,
        &active_reward_set,
        true,
    ) {
        Ok((receipt, _, _, _)) => (Some(receipt), None),
        Err(e) => (None, Some(e)),
    };

    if let Some(receipt) = ok_opt {
        // check the cost
        let evaluated_cost = receipt.anchored_block_cost.clone();
        if evaluated_cost != expected_cost {
            println!(
                "Failed processing block! block = {block_id}. Unexpected cost. expected = {expected_cost}, evaluated = {evaluated_cost}"
            );
            process::exit(1);
        }
    }

    if let Some(e) = err_opt {
        // force rollback
        drop(chainstate_tx);

        warn!(
            "Failed to append {}/{}: {:?}",
            &block.header.consensus_hash,
            &block.header.block_hash(),
            &e;
            "stacks_block_id" => %block.header.block_id()
        );

        // as a separate transaction, mark this block as processed and orphaned.
        // This is done separately so that the staging blocks DB, which receives writes
        // from the network to store blocks, will be available for writes while a block is
        // being processed. Therefore, it's *very important* that block-processing happens
        // within the same, single thread.  Also, it's *very important* that this update
        // succeeds, since *we have already processed* the block.
        return Err(e);
    };

    Ok(())
}

#[cfg(test)]
pub mod test {
    use super::*;

    fn parse_cli_command(s: &str) -> Vec<String> {
        s.split(' ').map(String::from).collect()
    }

    #[test]
    pub fn test_drain_common_opts() {
        // Should find/remove no options
        let mut argv = parse_cli_command(
            "stacks-inspect try-mine --config my_config.toml /tmp/chainstate/mainnet",
        );
        let argv_init = argv.clone();
        let _opts = drain_common_opts(&mut argv, 0);
        let opts = drain_common_opts(&mut argv, 1);

        assert_eq!(argv, argv_init);
        assert!(opts.config.is_none());

        // Should find config opts and remove from vec
        let mut argv = parse_cli_command(
            "stacks-inspect --network mocknet --network mainnet try-mine /tmp/chainstate/mainnet",
        );
        let opts = drain_common_opts(&mut argv, 1);
        let argv_expected = parse_cli_command("stacks-inspect try-mine /tmp/chainstate/mainnet");

        assert_eq!(argv, argv_expected);
        assert!(opts.config.is_some());
    }
}
