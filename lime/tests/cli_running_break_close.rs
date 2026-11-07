//! **A block closed while a logged break runs reads, now, what it will read once the break's line arrives** — README
//! gap 5180 (stage 6 W-49 track L; the owner's D94 and D100: a block and a break are read one way on every log; parity
//! **P124**).
//!
//! The world is W-48 track G's drive (README "Stage 6 — W-48 track G" §2): two machines on one synced plan directory.
//! Machine A runs `lime break 15m` at 07:30 while `^t1` runs; machine B, which has not seen A's line, runs `lime done` at
//! 08:05; the sync appends B's line after A's. Driven on `eef6732`'s binary, `lime review day` counted `^t1` sixty minutes
//! and `lime plan` drew it 07:05–08:05 across the break drawn from 07:30 — one span read as block AND as break — until
//! the break's own line arrived and D100 netted the block to twenty-five. Here the line B wrote is appended by hand,
//! which is what the sync does to A's file, and the replay nets the running break from the closed block at once
//! (`Replay.runNet`); the order a sync can append the two lines in the other way round (the `done` first, then A's
//! `break_start`) is the second test.

mod cli_common;

use cli_common::Lime;
use std::io::Write;

const WED: &str = "2026-09-09";

fn at(hm: &str) -> String {
    format!("{WED}T{hm}:00-05:00")
}

fn tree() -> Lime {
    let lime = Lime::empty();
    lime.ok_at(&at("06:00"), &["init", "--example"]);
    lime.ok_at(&at("06:30"), &["wake", "06:30"]);
    lime.ok_at(&at("07:00"), &["arrive", "lounge"]);
    lime.ok_at(&at("07:05"), &["start", "^t1"]);
    lime
}

/// Append one log line as a sync (or a hand edit) would, and drop this machine's cache of the runtime state, as the
/// drive did (D42 rebuilds it from the log).
fn append(lime: &Lime, line: &str) {
    let mut f = std::fs::OpenOptions::new().append(true).open(lime.plan.join(".tm/log.jsonl")).expect("log");
    writeln!(f, "{line}").expect("append");
    let _ = std::fs::remove_file(lime.plan.join(".tm/state.json"));
}

const B_DONE: &str = r#"{"t":"2026-09-09T08:05:00-05:00","ev":"done","id":"t1","est_min":60,"actual_min":60,"tags":[],"ci":5}"#;
const A_BREAK_START: &str = r#"{"t":"2026-09-09T07:30:00-05:00","ev":"break_start","planned_min":15}"#;

fn block_min(lime: &Lime, now: &str) -> u64 {
    let v = lime.json_at(now, &["review", "day"]);
    v["review"]["block_min"].as_u64().unwrap_or_else(|| panic!("block_min: {v}"))
}

/// **The driven world** (P124's behaviour row): while A's break still runs, B's `done` reads twenty-five minutes — the
/// review's block minutes and the plan's `✓` row — not sixty; and ending the break (A's `lime break`, which writes the
/// `break` line stamped at its start) moves nothing: twenty-five before and after.
#[test]
fn a_done_under_a_running_break_reads_what_it_will_read_once_the_break_ends() {
    let lime = tree();
    lime.ok_at(&at("07:30"), &["break", "15m"]);
    append(&lime, B_DONE);
    assert_eq!(block_min(&lime, &at("09:00")), 25, "the running break nets 07:30-08:05 from the closed block");
    let plan = lime.ok_at(&at("09:00"), &["plan"]);
    assert!(plan.stdout.contains("(25m)"), "the done row reads its twenty-five minutes:\n{}", plan.stdout);
    assert!(!plan.stdout.contains("(60m)"), "no row credits the span the break holds:\n{}", plan.stdout);
    let rows = lime.json_at(&at("09:00"), &["plan"]);
    let segs = rows["segments"].as_array().expect("segments");
    let block = segs.iter().find(|s| s["kind"] == "block" && s["item"] == "t1").expect("t1's past row");
    assert_eq!(block["end"].as_str().map(|e| e.contains("07:30")), Some(true), "drawn up to the break: {block}");
    // The break's own line arrives: nothing it netted moves.
    lime.ok_at(&at("09:00"), &["break"]);
    assert_eq!(block_min(&lime, &at("09:01")), 25, "the break's line moves nothing it netted");
}

/// **The other order a sync can append the two lines in**: B's `done` first, then A's `break_start` stamped inside
/// the block — the `break_start` nets the held block at once (`Replay.runNet` in its arm).
#[test]
fn a_break_start_appended_after_the_done_nets_the_block() {
    let lime = tree();
    lime.ok_at(&at("08:05"), &["done"]);
    assert_eq!(block_min(&lime, &at("08:06")), 60);
    append(&lime, A_BREAK_START);
    assert_eq!(block_min(&lime, &at("09:00")), 25);
}

/// **The rule's boundary** (AGENTS §5.8): a break begun after the block closed nets nothing of it.
#[test]
fn a_break_after_the_done_nets_nothing() {
    let lime = tree();
    lime.ok_at(&at("08:05"), &["done"]);
    lime.ok_at(&at("08:30"), &["break", "15m"]);
    assert_eq!(block_min(&lime, &at("09:00")), 60);
}
