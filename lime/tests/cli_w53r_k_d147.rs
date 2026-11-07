//! **D147's replay half through the binary** — stage 6 W-53 repair track K (P143).
//!
//! * **D147's replay half (parity P143): the later-logged `break` line at one stamp is that break's reading.** A
//!   `break` line stamped at a finished break's start (a plain line, or a line that ended a D129 ending) and ending
//!   before it re-times it: what the longer reading took is given back, and only the new span is drawn and recorded
//!   (`Replay.brkLine`, `Replay.findFin`).  A later line that is not shorter reads as D142's union, as before.
//!
//! Every log here is written by hand into a fresh `tm init --example` tree, so each test's subject is the kernel's
//! reading of the lines and not a verb; track H's verbs write these shapes.

mod cli_common;

use std::fs::OpenOptions;
use std::io::Write;

use cli_common::Tm;

const TUE: &str = "2026-09-08";

fn at(hm: &str) -> String {
    format!("{TUE}T{hm}:00-05:00")
}

/// The example tree, woken at 07:00 and arrived home at 08:00 on Tuesday.
fn tree() -> Tm {
    let tm = Tm::empty();
    tm.ok_at(&at("06:00"), &["init", "--example"]);
    tm.ok_at(&at("07:00"), &["wake", "07:00"]);
    tm.ok_at(&at("08:00"), &["arrive", "home"]);
    tm
}

/// Append raw lines to the tree's log, as a sync or a hand edit would.
fn append(tm: &Tm, lines: &[String]) {
    let mut f = OpenOptions::new().append(true).open(tm.plan.join(".tm/log.jsonl")).expect("the log");
    for l in lines {
        writeln!(f, "{l}").expect("append a line");
    }
}

fn brk(hm: &str, planned: u32, actual: u32) -> String {
    format!(r#"{{"t":"{}","ev":"break","planned_min":{planned},"actual_min":{actual}}}"#, at(hm))
}

fn brk_start(hm: &str, planned: u32) -> String {
    format!(r#"{{"t":"{}","ev":"break_start","planned_min":{planned}}}"#, at(hm))
}

/// The day's worked minutes and each recorded break's (planned, actual), from `tm review day` at `now`.
fn review(tm: &Tm, now: &str) -> (u64, Vec<(u64, u64)>) {
    let v = tm.json_at(&at(now), &["review", "day"]);
    let r = &v["review"];
    let mut breaks: Vec<(u64, u64)> = r["breaks"]["breaks"]
        .as_array()
        .unwrap_or_else(|| panic!("{v}"))
        .iter()
        .map(|b| (b["planned_min"].as_u64().unwrap_or_default(), b["actual_min"].as_u64().unwrap_or_default()))
        .collect();
    breaks.sort();
    (r["block_min"].as_u64().unwrap_or_else(|| panic!("{v}")), breaks)
}

/// The plan's break rows before noon, as `HH:MM break Nm`.
fn break_rows(tm: &Tm, now: &str) -> Vec<String> {
    let out = tm.ok_at(&at(now), &["plan"]);
    out.stdout
        .lines()
        .filter(|l| l.contains("break") && l.trim_start().starts_with(['0', '1']))
        .map(|l| l.split_whitespace().filter(|w| *w != "·").collect::<Vec<_>>().join(" "))
        .collect()
}

/// The J tree: `^t1` 09:00–10:00 and `^t4` 10:10–11:10 done.
fn j_tree() -> Tm {
    let tm = tree();
    tm.ok_at(&at("09:00"), &["start", "^t1"]);
    tm.ok_at(&at("10:00"), &["done"]);
    tm.ok_at(&at("10:10"), &["start", "^t4"]);
    tm.ok_at(&at("11:10"), &["done"]);
    tm
}

/// **D147's replay half (P143), a plain line**: `break` 09:30 for ten, then a later `break` 09:30 with four — the
/// second is the break's reading: `^t1` gets back the six minutes it no longer covers (56, 116 with `^t4`), one break
/// of four is recorded, and the plan draws `09:30 break 4m`.  Until this step the second line was a break of its own
/// under D142's union: covered whole, recorded at zero, `^t1` at fifty.
#[test]
fn a_later_shorter_line_at_a_finished_breaks_stamp_re_times_it_p143() {
    let tm = j_tree();
    append(&tm, &[brk("09:30", 10, 10), brk("09:30", 10, 4)]);
    let (block, breaks) = review(&tm, "11:30");
    assert_eq!((block, breaks.clone()), (116, vec![(10, 4)]), "{breaks:?}");
    let rows = break_rows(&tm, "11:30");
    assert!(rows.iter().any(|r| r.starts_with("09:30 break 4m")), "{rows:?}");
}

/// **D147's replay half (P143) on a D141 ending**: `break_start` 09:30 (D129 ends it at 10:10), its line for ten (D141
/// ends it at 09:40), then a later line at 09:30 with four — re-timed again: `^t1` 56, one break of four.
#[test]
fn a_later_shorter_line_re_times_a_break_d141_ended_p143() {
    let tm = j_tree();
    append(&tm, &[brk_start("09:30", 10), brk("09:30", 10, 10), brk("09:30", 10, 4)]);
    let (block, breaks) = review(&tm, "11:30");
    assert_eq!((block, breaks.clone()), (116, vec![(10, 4)]), "{breaks:?}");
}

/// **A later line that is not shorter reads as D142's union** (P143's boundary): `break` 09:30 for four, then 09:30
/// for ten — the day reads ten minutes of break (`^t1` fifty), the later line drawn from 09:34.
#[test]
fn a_later_longer_line_reads_as_the_union() {
    let tm = j_tree();
    append(&tm, &[brk("09:30", 4, 4), brk("09:30", 10, 10)]);
    let (block, breaks) = review(&tm, "11:30");
    assert_eq!(block, 110, "{breaks:?}");
    assert_eq!(breaks.iter().map(|b| b.1).sum::<u64>(), 10, "{breaks:?}");
}


/// **Two finished breaks typed with a length at one stamp stay two** (P143 narrowed by planned minutes): `tm break --now
/// 09:50 30m` then `tm break --now 09:50 10m` log two plain lines, planned 30 and planned 10 — the second is a new D143
/// break (track H's gap 5849), not a re-timing, which would carry the break's own planned 30.  The day reads thirty minutes
/// of break over two records, D142's union.
#[test]
fn two_finished_breaks_typed_at_one_stamp_stay_two_p143() {
    let tm = tree();
    append(&tm, &[brk("09:50", 30, 30), brk("09:50", 10, 10)]);
    let (_, breaks) = review(&tm, "11:30");
    assert_eq!(breaks.len(), 2, "{breaks:?}");
    assert_eq!(breaks.iter().map(|b| b.1).sum::<u64>(), 30, "{breaks:?}");
    let rows = break_rows(&tm, "11:30");
    assert!(rows.iter().any(|r| r.starts_with("09:50 break 30m")), "{rows:?}");
}
