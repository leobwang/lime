//! **A re-time through the binary** — stage 6 W-54 track K (P143 restated; README gaps 5870-5876).
//!
//! * **A re-time gives back what the break took from a block that was OPEN when it netted** (gap 5870): `^t1`
//!   running, `tm break 10m` at 09:20, `tm done` (or `tm stop`) at 10:00 ending the break at forty minutes, then the
//!   line re-timing the break to 09:30 — `^t1` reads fifty, where the W-53 repair's kernel read twenty.
//! * **A re-time keeps every later break's netting** (gap 5871): the J day, 09:20 and 09:40 for five, 09:20
//!   re-timed to 09:22 — the plan draws `^t1` around the 09:40 break, not through it.
//! * **Identical twins re-time as one, and a longer line re-times too** (gaps 5875, 5876).
//!
//! The setup runs the verbs; the re-timing line is appended by hand, the shape track H's D147 verb writes (a
//! `break` line at the finished break's start carrying its planned minutes), so the subject is the kernel's reading.

mod cli_common;

use std::fs::OpenOptions;
use std::io::Write;

use cli_common::Tm;

const TUE: &str = "2026-09-08";

fn at(hm: &str) -> String {
    format!("{TUE}T{hm}:00-05:00")
}

fn tree() -> Tm {
    let tm = Tm::empty();
    tm.ok_at(&at("06:00"), &["init", "--example"]);
    tm.ok_at(&at("07:00"), &["wake", "07:00"]);
    tm.ok_at(&at("08:00"), &["arrive", "home"]);
    tm
}

fn append(tm: &Tm, lines: &[String]) {
    let mut f = OpenOptions::new().append(true).open(tm.plan.join(".tm/log.jsonl")).expect("the log");
    for l in lines {
        writeln!(f, "{l}").expect("append a line");
    }
}

fn brk(hm: &str, planned: u32, actual: u32) -> String {
    format!(r#"{{"t":"{}","ev":"break","planned_min":{planned},"actual_min":{actual}}}"#, at(hm))
}

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

/// The plan's rows from 09:00 to 10:59, as `HH:MM … (Nm)` words.
fn rows(tm: &Tm, now: &str) -> Vec<String> {
    let out = tm.ok_at(&at(now), &["plan"]);
    out.stdout
        .lines()
        .filter(|l| l.trim_start().starts_with("09:") || l.trim_start().starts_with("10:"))
        .map(|l| l.split_whitespace().filter(|w| *w != "·").collect::<Vec<_>>().join(" "))
        .collect()
}

fn open_block_tree(close: &str) -> Tm {
    let tm = tree();
    tm.ok_at(&at("09:00"), &["start", "^t1"]);
    tm.ok_at(&at("09:20"), &["break", "10m"]);
    tm.ok_at(&at("10:00"), &[close]);
    tm.ok_at(&at("10:10"), &["start", "^t4"]);
    tm.ok_at(&at("11:10"), &["done"]);
    tm
}

#[test]
fn a_retime_gives_back_what_the_break_took_from_a_block_it_netted_open_done() {
    let tm = open_block_tree("done");
    assert_eq!(review(&tm, "12:30"), (80, vec![(10, 40)]), "the break ran to the `done`");
    append(&tm, &[brk("09:20", 10, 10)]);
    assert_eq!(review(&tm, "12:30"), (110, vec![(10, 10)]), "the W-53 repair's kernel read (80, [(10, 10)])");
    let r = rows(&tm, "12:30");
    assert!(r.iter().any(|l| l.starts_with("09:30") && l.contains("(30m)")), "{r:?}");
    std::fs::remove_dir_all(tm.plan.join(".tm/cache")).ok();
    assert_eq!(review(&tm, "12:30"), (110, vec![(10, 10)]), "a cold replay reads the same");
}

#[test]
fn a_retime_gives_back_what_the_break_took_from_a_block_it_netted_open_stop() {
    let tm = open_block_tree("stop");
    assert_eq!(review(&tm, "12:30").0, 80);
    append(&tm, &[brk("09:20", 10, 10)]);
    assert_eq!(review(&tm, "12:30"), (110, vec![(10, 10)]), "the W-53 repair's kernel read 80");
}

#[test]
fn a_retime_keeps_a_later_breaks_netting_in_the_drawing() {
    let tm = tree();
    tm.ok_at(&at("09:00"), &["start", "^t1"]);
    tm.ok_at(&at("10:00"), &["done"]);
    tm.ok_at(&at("10:10"), &["start", "^t4"]);
    tm.ok_at(&at("11:10"), &["done"]);
    append(&tm, &[brk("09:20", 5, 5), brk("09:40", 5, 5), brk("09:20", 5, 2)]);
    assert_eq!(review(&tm, "12:30"), (113, vec![(5, 2), (5, 5)]));
    let r = rows(&tm, "12:30");
    assert!(r.iter().any(|l| l.starts_with("09:22") && l.contains("(18m)")), "drawn up to the 09:40 break: {r:?}");
    assert!(!r.iter().any(|l| l.contains("(38m)")), "the W-53 repair drew 09:22 (38m) through it: {r:?}");
}

#[test]
fn twins_re_time_as_one_and_a_longer_line_re_times_out() {
    let tm = tree();
    tm.ok_at(&at("09:00"), &["start", "^t1"]);
    tm.ok_at(&at("10:00"), &["done"]);
    tm.ok_at(&at("10:10"), &["start", "^t4"]);
    tm.ok_at(&at("11:10"), &["done"]);
    append(&tm, &[brk("09:20", 10, 10), brk("09:20", 10, 10), brk("09:20", 10, 5)]);
    assert_eq!(review(&tm, "12:30"), (115, vec![(10, 5)]), "the W-53 repair read (110, [(10, 0), (10, 10)])");
    append(&tm, &[brk("09:20", 10, 8)]);
    assert_eq!(review(&tm, "12:30"), (112, vec![(10, 8)]), "a longer line is the break's reading too");
}
