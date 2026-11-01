//! **D144 through the binary** (stage 6 W-53 track H, README gap 5750, parity **P141**): `tm now` READS A RUNNING
//! BREAK — its header `on break since 10:10 · 65m of 20m` (the place when its `break_start` logged one), `--json`'s
//! `break` object (`start`, `planned_min`, `elapsed_min`, `place`; `null` when none runs), and the current row the
//! break's row, kept current past its planned end with `(overrun 45m)` under it — read off the kernel's replay (the
//! `break_start` it holds open), never `.tm/state.json` (D42, D133).
//!
//! Gap 5750's two drives: a break left running from 10:10 read at 10:20 and 11:15 (`tm now` said `nothing running`
//! and, past the break's planned end, `— nothing running (11:15)` while `tm plan` drew `10:10 · break 1h5m`); and the
//! tie, `^t4` started 10:10 and `tm break --now 10:10` at its stamp.

mod cli_common;

use cli_common::Tm;
use serde_json::Value;

const TUE: &str = "2026-09-08";

fn at(hm: &str) -> String {
    format!("{TUE}T{hm}:00-05:00")
}

/// The example tree, woken at 07:00 and arrived home at 08:00 on Tuesday.
fn day() -> Tm {
    let tm = Tm::empty();
    tm.ok_at(&at("06:00"), &["init", "--example"]);
    tm.ok_at(&at("07:00"), &["wake", "07:00"]);
    tm.ok_at(&at("08:00"), &["arrive", "home"]);
    tm
}

fn now_text(tm: &Tm, hm: &str) -> String {
    tm.ok_at(&at(hm), &["now"]).stdout
}

/// **A break left running reads as one, inside its planned minutes and past them** (P141). At 10:20 the header is
/// `on break since 10:10 · 10m of 20m` and the break's row is current with `elapsed 10m · left 10m`; at 11:15 it is
/// `65m of 20m`, the row `10:10 · break 1h5m` is still current, and the line under it says `(overrun 45m)`. Until D144
/// the header said `nothing running` both times and, at 11:15, the row `— nothing running (11:15)`.
#[test]
fn a_running_break_is_tm_nows_header_and_current_row_p141() {
    let tm = day();
    tm.ok_at(&at("10:10"), &["break"]);
    let early = now_text(&tm, "10:20");
    assert!(early.starts_with("on break since 10:10 · 10m of 20m\n10:10  ·      break 20m\n"), "{early}");
    assert!(early.contains("  10:10–10:30 · elapsed 10m · left 10m\n"), "{early}");
    assert!(!early.contains("nothing running"), "{early}");
    let late = now_text(&tm, "11:15");
    assert!(late.starts_with("on break since 10:10 · 65m of 20m\n10:10  ·      break 1h5m\n"), "{late}");
    assert!(late.contains("  10:10–11:15 · elapsed 1h5m · left 0m (overrun 45m)\n"), "{late}");
    assert!(!late.contains("nothing running"), "{late}");
    let plan = tm.ok_at(&at("11:15"), &["plan"]).stdout;
    assert!(plan.contains("10:10  ·      break 1h5m"), "`tm plan` draws the same break:\n{plan}");
}

/// **`--json`'s `break`**: the start, the planned and the elapsed minutes and the place, and `current` the break's
/// row; `null` when no break runs.
#[test]
fn tm_now_json_carries_the_running_break_p141() {
    let tm = day();
    let none = tm.json_at(&at("09:00"), &["now"]);
    assert!(none.get("break").is_some_and(Value::is_null), "`break` is null when none runs: {none}");
    tm.ok_at(&at("10:10"), &["break", "--where", "walk"]);
    let v = tm.json_at(&at("11:15"), &["now"]);
    assert_eq!(v["break"]["start"], "10:10", "{v}");
    assert_eq!(v["break"]["planned_min"], 20, "{v}");
    assert_eq!(v["break"]["elapsed_min"], 65, "{v}");
    assert_eq!(v["break"]["place"], "walk", "{v}");
    assert_eq!(v["current"]["kind"], "break", "{v}");
    assert_eq!(v["current"]["start"], "10:10", "{v}");
    assert_eq!(v["current"]["end"], "11:15", "{v}");
}

/// **The tie** (gap 5750's second drive): `^t4` started 10:10, then `tm break --now 10:10 --where walk` at its own
/// stamp — the break runs (the start ends nothing, W-50 repair track R's strict tie) and pauses `^t4`. The block's
/// header line is unchanged (`· paused`); the break's follows it, with its place; the break's row is current at 10:20
/// and at 11:15.
#[test]
fn the_tie_shows_the_block_and_the_break_p141() {
    let tm = day();
    tm.ok_at(&at("09:00"), &["start", "^t1"]);
    tm.ok_at(&at("10:00"), &["done"]);
    tm.ok_at(&at("10:10"), &["start", "^t4"]);
    tm.ok_at(&at("10:10"), &["break", "--where", "walk"]);
    let early = now_text(&tm, "10:20");
    assert!(
        early.starts_with(
            "▶ ^t4 Claude Code drafts tests · started 10:10 · 0m of 60m · paused\non break since 10:10 (walk) · 10m of 20m\n10:10  ·      break 20m"
        ),
        "{early}"
    );
    let late = now_text(&tm, "11:15");
    assert!(late.contains("on break since 10:10 (walk) · 65m of 20m\n10:10  ·      break 1h5m"), "{late}");
    assert!(late.contains("(overrun 45m)"), "{late}");
}

/// **A block a break pauses** (D114's shape): `^t4` begun 10:10, `tm break 15m` at 10:30. The header is the block's
/// line, unchanged, then the break's; at 11:00, past the break's fifteen, the break's row stays current ahead of the
/// routine that starts at 11:00.
#[test]
fn a_block_paused_by_a_break_reads_both_p141() {
    let tm = day();
    tm.ok_at(&at("10:10"), &["start", "^t4"]);
    tm.ok_at(&at("10:30"), &["break", "15m"]);
    let early = now_text(&tm, "10:35");
    assert!(
        early.starts_with(
            "▶ ^t4 Claude Code drafts tests · started 10:10 · 20m of 60m · paused\non break since 10:30 · 5m of 15m\n10:30  ·      break 15m\n"
        ),
        "{early}"
    );
    let late = now_text(&tm, "11:00");
    assert!(late.contains("on break since 10:30 · 30m of 15m\n10:30  ·      break 30m\n"), "{late}");
    assert!(late.contains("  10:30–11:00 · elapsed 30m · left 0m (overrun 15m)\n"), "{late}");
    let v = tm.json_at(&at("11:00"), &["now"]);
    assert_eq!(v["active"]["id"], "t4", "{v}");
    assert_eq!(v["active"]["paused"], true, "{v}");
    assert_eq!(v["current"]["kind"], "break", "{v}");
}

/// **A running block with no break is unchanged**: its header, its row, and `break` null.
#[test]
fn a_running_block_without_a_break_is_unchanged() {
    let tm = day();
    tm.ok_at(&at("10:10"), &["start", "^t4"]);
    let text = now_text(&tm, "10:30");
    assert!(text.starts_with("▶ ^t4 Claude Code drafts tests · started 10:10 · 20m of 60m\n"), "{text}");
    assert!(!text.contains("on break"), "{text}");
    let v = tm.json_at(&at("10:30"), &["now"]);
    assert!(v["break"].is_null(), "{v}");
}

/// **The break is the replay's, not the cache's** (D42, D133): deleting `.tm/state.json` mid-break leaves `tm now`'s
/// header, row and JSON as they were.
#[test]
fn tm_nows_break_survives_the_cache_deletion() {
    let tm = day();
    tm.ok_at(&at("10:10"), &["break"]);
    let text = now_text(&tm, "11:15");
    let v = tm.json_at(&at("11:15"), &["now"]);
    std::fs::remove_file(tm.plan.join(".tm/state.json")).expect("the cache");
    assert_eq!(now_text(&tm, "11:15"), text);
    assert_eq!(tm.json_at(&at("11:15"), &["now"]), v);
}
