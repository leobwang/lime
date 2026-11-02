//! **D147's verb through the binary** (stage 6 W-53 repair track H, parity **P145**, README gaps 5772 and 5810): a
//! `tm break` with NO length typed at an instant INSIDE a break already logged finished RE-TIMES it — one more `break`
//! line in the fork's shape, `t` that break's own start, its planned minutes, `actual_min` the typed instant less its
//! start, its place — which the kernel reads as that break's reading (track K's P143: the later line at one stamp
//! wins); AT its end it changes nothing and says so; AT its own start it is refused by name (the campaign's call
//! inside D147, as P139 refuses at a D129-ended break's start); a LENGTH typed there keeps D143 (a new finished break).
//!
//! The finished breaks the verb gates on are the kernel's own fact (track K's wire fact, W-53 repair track K item 3),
//! never re-derived from the log's lines (§5.3).

mod cli_common;

use cli_common::Tm;
use serde_json::Value;

const TUE: &str = "2026-09-08";

fn at(hm: &str) -> String {
    format!("{TUE}T{hm}:00-05:00")
}

/// The J drive's day — `^t1` 09:00–10:00 and `^t4` 10:10–11:10 done — with `tm break --now 09:20 10m`, which D143
/// logs finished, 09:20–09:30, in one plain `break` line.
fn finished_tree() -> Tm {
    let tm = Tm::empty();
    tm.ok_at(&at("06:00"), &["init", "--example"]);
    tm.ok_at(&at("07:00"), &["wake", "07:00"]);
    tm.ok_at(&at("08:00"), &["arrive", "home"]);
    tm.ok_at(&at("09:00"), &["start", "^t1"]);
    tm.ok_at(&at("10:00"), &["done"]);
    tm.ok_at(&at("10:10"), &["start", "^t4"]);
    tm.ok_at(&at("11:10"), &["done"]);
    let out = tm.ok_at(&at("09:20"), &["break", "10m"]);
    assert!(out.stdout.contains("09:20–09:30 · logged finished"), "{}", out.stdout);
    tm
}

fn breaks(tm: &Tm) -> Vec<Value> {
    tm.log().into_iter().filter(|e| e["ev"] == "break" || e["ev"] == "break_start").collect()
}

/// The day's worked minutes and each break's minutes, from `tm review day` at 12:30.
fn review(tm: &Tm) -> (u64, Vec<u64>) {
    let v = tm.json_at(&at("12:30"), &["review", "day"]);
    let r = &v["review"];
    let breaks = r["breaks"]["breaks"]
        .as_array()
        .unwrap_or_else(|| panic!("{v}"))
        .iter()
        .map(|b| b["actual_min"].as_u64().unwrap_or_default())
        .collect();
    (r["block_min"].as_u64().unwrap_or_else(|| panic!("{v}")), breaks)
}

/// **Inside: re-timed** (P145). `tm break --now 09:24` writes one `break` line stamped 09:20 with `planned_min` ten
/// and `actual_min` four, says `break 09:20–09:30 re-timed to end at 09:24 (D147)`, journals the end, and the day
/// reads the break at four and `^t1` at fifty-six (116). Until D147 the instant began a second break that D129 ran to
/// the 10:10 start (gap 5772: the union `[10, 40]`, `^t1` at twenty).
#[test]
#[ignore = "P145: needs track K's finished-break wire fact (W-53 repair track K item 3) and its P143 reading; the land un-ignores it"]
fn a_no_length_break_inside_a_finished_break_retimes_it_p145() {
    let tm = finished_tree();
    let out = tm.ok_at(&at("09:24"), &["break"]);
    assert_eq!(out.stdout.trim(), "break 09:20–09:30 re-timed to end at 09:24 (D147) · 4m of 10m", "{}", out.stderr);
    let b = breaks(&tm);
    assert_eq!(b.len(), 2, "{b:?}");
    assert_eq!((b[1]["ev"].as_str(), b[1]["t"].as_str()), (Some("break"), Some(at("09:20").as_str())), "{b:?}");
    assert_eq!((b[1]["planned_min"].as_u64(), b[1]["actual_min"].as_u64()), (Some(10), Some(4)), "{b:?}");
    assert_eq!(review(&tm), (116, vec![4]), "the break at four, ^t1 at fifty-six");
    assert!(tm.read(&format!("day/{TUE}.md")).contains("09:24 break ended 4m/10m"));
    let v = tm.json_at(&at("09:26"), &["break"]);
    assert_eq!(v["action"], "started", "09:26 is outside the re-timed break: {v}");
}

/// **`--json`**: `action` `retimed`, the new minutes, and `superseded_end` the end it replaced.
#[test]
#[ignore = "P145: needs track K's finished-break wire fact (W-53 repair track K item 3); the land un-ignores it"]
fn a_retimed_break_reports_the_end_it_replaced_p145() {
    let tm = finished_tree();
    let v = tm.json_at(&at("09:24"), &["break"]);
    assert_eq!(v["action"], "retimed", "{v}");
    assert_eq!(v["actual_min"], 4, "{v}");
    assert_eq!(v["planned_min"], 10, "{v}");
    assert_eq!(v["superseded_end"], "09:30", "{v}");
}

/// **At its end: nothing written**, and the verb says so; scenario C's typed ends (gap 5810) are this case.
#[test]
#[ignore = "P145: needs track K's finished-break wire fact (W-53 repair track K item 3); the land un-ignores it"]
fn a_no_length_break_at_a_finished_breaks_end_changes_nothing_p145() {
    let tm = finished_tree();
    let log = tm.read(".tm/log.jsonl");
    let out = tm.ok_at(&at("09:30"), &["break"]);
    assert_eq!(out.stdout.trim(), "break 09:20–09:30 already ends at 09:30 — nothing written (D147)");
    assert_eq!(tm.read(".tm/log.jsonl"), log, "nothing written");
    assert_eq!(review(&tm), (110, vec![10]));
    assert!(tm.state()["break"].is_null(), "{}", tm.state());
}

/// **At its own start: refused by name**, nothing written (the campaign's call inside D147; gap 5772 closed).
#[test]
#[ignore = "P145: needs track K's finished-break wire fact (W-53 repair track K item 3); the land un-ignores it"]
fn a_no_length_break_at_a_finished_breaks_start_is_refused_p145() {
    let tm = finished_tree();
    let log = tm.read(".tm/log.jsonl");
    let out = tm.run_at(&at("09:20"), &["break"]);
    assert_ne!(out.code, 0, "{}", out.stdout);
    assert!(out.stderr.contains("logged finished 09:20–09:30") && out.stderr.contains("(D147)"), "{}", out.stderr);
    assert_eq!(tm.read(".tm/log.jsonl"), log, "nothing written");
}

/// **A length typed inside a finished break keeps D143**: a new finished break of its own (README gap 5849), read
/// with the first as their union (D142).
#[test]
#[ignore = "P145: needs track K's finished-break wire fact (W-53 repair track K item 3); the land un-ignores it"]
fn a_length_typed_inside_a_finished_break_logs_a_new_finished_break_p145() {
    let tm = finished_tree();
    let v = tm.json_at(&at("09:24"), &["break", "3m"]);
    assert_eq!(v["action"], "finished", "{v}");
    let b = breaks(&tm);
    assert_eq!(b.len(), 2, "{b:?}");
    assert_eq!((b[1]["t"].as_str(), b[1]["actual_min"].as_u64()), (Some(at("09:24").as_str()), Some(3)), "{b:?}");
    assert_eq!(review(&tm).0, 110, "covered whole by the first: the union is 09:20–09:30");
}

/// **Scenario C reads 140 → 140** (gap 5810): two late breaks with a length, logged finished, then each typed end —
/// at each break's own end — changes nothing.
#[test]
#[ignore = "P145: needs track K's finished-break wire fact (W-53 repair track K item 3); the land un-ignores it"]
fn scenario_c_typed_ends_change_nothing_p145() {
    let tm = finished_tree();
    tm.ok_at(&at("11:20"), &["start", "^t5"]);
    tm.ok_at(&at("12:00"), &["done"]);
    // The 09:20 10m break is the tree's; C's second is at 10:30.
    tm.ok_at(&at("10:30"), &["break", "10m"]);
    let before = review(&tm);
    for hm in ["09:30", "10:40"] {
        let out = tm.ok_at(&at(hm), &["break"]);
        assert!(out.stdout.contains("nothing written (D147)"), "{hm}: {}", out.stdout);
    }
    assert_eq!(review(&tm), before);
    assert_eq!(before.1, vec![10, 10], "{before:?}");
}

/// **`tm undo` takes a re-timing back**: the day reads the break at ten again.
#[test]
#[ignore = "P145: needs track K's finished-break wire fact (W-53 repair track K item 3) and its P143 reading; the land un-ignores it"]
fn undo_takes_a_retiming_back_p145() {
    let tm = finished_tree();
    tm.ok_at(&at("09:24"), &["break"]);
    let out = tm.ok_at(&at("11:20"), &["undo"]);
    assert!(out.stdout.contains("undid break (break retimed)"), "{}", out.stdout);
    assert_eq!(review(&tm), (110, vec![10]));
}
