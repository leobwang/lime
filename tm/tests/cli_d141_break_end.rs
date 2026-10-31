//! **D141 through the binary, the verb's half** (stage 6 W-52 track H, README gap 5633, parity **P138**): a `tm break`
//! typed at an instant INSIDE a logged break that D129 already ended at a later block's `start`, and that no `break`
//! line has ended yet, ENDS THAT BREAK THERE — one `break` line in the shape every break end has (`t` the break's start,
//! `actual_min` the typed instant less it), the journal line and the human clause every break end writes (D97, D101),
//! a one-line notice naming the end D129 had given it, and never a second `break_start` inside the first.
//!
//! The W-51 auditor's J drive (README gaps 5633 and 5634): `^t1` 09:00–10:00 and `^t4` 10:10–11:10 done; `tm break
//! --now 09:30 10m` (D129 ends it at 10:10, `^t1` netted to thirty); `tm break --now 09:40`, meant to end it, logged a
//! SECOND `break_start`, and `tm plan` drew `09:30 break 40m` and `09:40 break 30m`.
//!
//! The block minutes that follow from the line (`^t1` fifty) are the replay's, W-52 track K's half of D141: that test
//! is written whole and ignored until the land.

mod cli_common;

use cli_common::Tm;
use serde_json::Value;

const TUE: &str = "2026-09-08";

fn at(hm: &str) -> String {
    format!("{TUE}T{hm}:00-05:00")
}

/// The example tree, woken at 07:00 and arrived home at 08:00 on Tuesday, with `^t1` 09:00–10:00 and `^t4`
/// 10:10–11:10 done — the J drive's day.
fn j_tree() -> Tm {
    let tm = Tm::empty();
    tm.ok_at(&at("06:00"), &["init", "--example"]);
    tm.ok_at(&at("07:00"), &["wake", "07:00"]);
    tm.ok_at(&at("08:00"), &["arrive", "home"]);
    tm.ok_at(&at("09:00"), &["start", "^t1"]);
    tm.ok_at(&at("10:00"), &["done"]);
    tm.ok_at(&at("10:10"), &["start", "^t4"]);
    tm.ok_at(&at("11:10"), &["done"]);
    tm
}

/// [`j_tree`] with `tm break --now 09:30 10m` taken — the break D129 ends at `^t4`'s start, 10:10.
fn j_tree_with_the_late_break() -> Tm {
    let tm = j_tree();
    let out = tm.ok_at(&at("09:30"), &["break", "10m"]);
    assert!(out.stderr.contains("ended at 10:10") && out.stderr.contains("(D129)"), "{}", out.stderr);
    tm
}

/// Every `break` and `break_start` line of the log, in file order.
fn breaks(tm: &Tm) -> Vec<Value> {
    tm.log().into_iter().filter(|e| e["ev"] == "break" || e["ev"] == "break_start").collect()
}

fn evs(b: &[Value]) -> Vec<String> {
    b.iter().map(|e| e["ev"].as_str().unwrap_or_default().to_string()).collect()
}

/// **D141 (P138): typed inside the break D129 ended, `tm break` ends it there.** One `break` line — `t` the break's
/// start, 09:30, `actual_min` ten, its planned ten — and no second `break_start`; the notice names the end D129 had
/// given it (10:10); the human clause is a break end's; the day file's journal holds `break ended` at 09:40. Until
/// D141 the verb logged a second `break_start` at 09:40.
#[test]
fn a_break_typed_inside_a_break_a_later_start_ended_ends_it_there_p138() {
    let tm = j_tree_with_the_late_break();
    let out = tm.ok_at(&at("09:40"), &["break"]);
    let b = breaks(&tm);
    assert_eq!(evs(&b), ["break_start", "break"], "one break line and no second break_start: {b:?}");
    assert_eq!(b[1]["t"], "2026-09-08T09:30:00-05:00", "the line is stamped at the break's start: {b:?}");
    assert_eq!(b[1]["actual_min"], 10, "the typed instant less the break's start: {b:?}");
    assert_eq!(b[1]["planned_min"], 10, "its own planned minutes: {b:?}");
    assert!(b[1].get("where").is_none(), "no place was logged for it: {b:?}");
    assert_eq!(out.stdout.trim(), "break ended · 10m of 10m", "a break end's clause (D101)");
    assert!(
        out.stderr.contains("began at 09:30")
            && out.stderr.contains("at 09:40")
            && out.stderr.contains("at 10:10")
            && out.stderr.contains("(D141)"),
        "the one-line notice: {}",
        out.stderr
    );
    assert!(!out.stderr.contains("it is not running"), "no D129 notice for a break never opened: {}", out.stderr);
    let journal = tm.read(&format!("day/{TUE}.md"));
    assert!(journal.contains("09:40 break ended 10m/10m"), "the break end's journal line (D97):\n{journal}");
    assert!(!journal.contains("09:40 break 20m"), "no journal line of a break begun at 09:40:\n{journal}");
}

/// **`--json`, and D20 in the D141 arm.** The report is a break end's (`action` `ended`, the minutes), with the end it
/// replaced; a valid duration does to this break what it does to a running one — nothing: `tm break --now 09:40 25m`
/// ends it after ten minutes and its planned minutes stay ten. An invalid one is refused here as in both other arms.
#[test]
fn the_d141_arm_reports_a_break_end_and_does_not_retime_p138() {
    let tm = j_tree_with_the_late_break();
    let refused = tm.run_at(&at("09:40"), &["break", "zzzz"]);
    assert_ne!(refused.code, 0, "an invalid duration is refused (D20): {}", refused.stdout);
    let moon = tm.run_at(&at("09:40"), &["break", "--where", "moon"]);
    assert_ne!(moon.code, 0, "an unknown place is refused (P75): {}", moon.stdout);
    assert_eq!(evs(&breaks(&tm)), ["break_start"], "a refusal writes nothing");
    let v = tm.json_at(&at("09:40"), &["break", "25m"]);
    assert_eq!(v["action"], "ended", "{v}");
    assert_eq!(v["actual_min"], 10, "{v}");
    assert_eq!(v["planned_min"], 10, "not retimed (D20): {v}");
    assert_eq!(v["superseded_end"], "10:10", "the end D129 had given it: {v}");
    let b = breaks(&tm);
    assert_eq!(evs(&b), ["break_start", "break"], "{b:?}");
    assert_eq!(b[1]["planned_min"], 10, "{b:?}");
}

/// The JSON of the two arms D141 does not change carries no `superseded_end`.
#[test]
fn a_plain_break_end_carries_no_superseded_end() {
    let tm = Tm::empty();
    tm.ok_at(&at("06:00"), &["init", "--example"]);
    tm.ok_at(&at("07:00"), &["wake", "07:00"]);
    let started = tm.json_at(&at("09:00"), &["break", "10m"]);
    assert!(started.get("superseded_end").is_none(), "{started}");
    let ended = tm.json_at(&at("09:12"), &["break"]);
    assert_eq!(ended["action"], "ended", "{ended}");
    assert!(ended.get("superseded_end").is_none(), "{ended}");
}

/// **At or after D129's end, the verb keeps its behaviour before D141.** Typed at 10:10 — the `start` that ended the
/// break — or at 10:20, the instant lies outside the break, so `tm break` begins a break as it always has: a
/// `break_start`, and no `break` line.
#[test]
fn a_break_typed_at_or_after_the_end_d129_gave_begins_a_break() {
    for hm in ["10:10", "10:20"] {
        let tm = j_tree_with_the_late_break();
        let out = tm.ok_at(&at(hm), &["break"]);
        assert!(!out.stderr.contains("(D141)"), "{hm}: {}", out.stderr);
        let b = breaks(&tm);
        assert_eq!(evs(&b), ["break_start", "break_start"], "{hm}: {b:?}");
        assert_eq!(b[1]["t"], format!("{TUE}T{hm}:00-05:00"), "{hm}: {b:?}");
    }
}

/// **At the break's own start the instant is not inside it** (the span is half-open at its end and the typed instant
/// must lie strictly after its start): `tm break --now 09:30` again begins a break, as before D141, and writes no
/// `break` line of zero minutes.
#[test]
fn a_break_typed_at_the_breaks_own_start_begins_a_break() {
    let tm = j_tree_with_the_late_break();
    let out = tm.ok_at(&at("09:30"), &["break"]);
    assert!(!out.stderr.contains("(D141)"), "{}", out.stderr);
    assert_eq!(evs(&breaks(&tm)), ["break_start", "break_start"]);
}

/// **A break its own line already ended keeps the behaviour before D141**, twice over. After D141 ended the J break at
/// 09:40, a `tm break --now 09:35` begins a break (the break has its line); and a break that ended while it ran —
/// `^t1` 09:00–10:00 done, `tm break --now 09:30 10m`, ended by `tm break --now 09:40` with no later start, D137's day —
/// is not ended a second time by a `tm break --now 09:35` inside it.
#[test]
fn a_break_its_own_line_ended_is_not_ended_again() {
    let tm = j_tree_with_the_late_break();
    tm.ok_at(&at("09:40"), &["break"]);
    let out = tm.ok_at(&at("09:35"), &["break"]);
    assert!(!out.stderr.contains("(D141)"), "{}", out.stderr);
    assert_eq!(evs(&breaks(&tm)), ["break_start", "break", "break_start"]);

    let tm = Tm::empty();
    tm.ok_at(&at("06:00"), &["init", "--example"]);
    tm.ok_at(&at("07:00"), &["wake", "07:00"]);
    tm.ok_at(&at("08:00"), &["arrive", "home"]);
    tm.ok_at(&at("09:00"), &["start", "^t1"]);
    tm.ok_at(&at("10:00"), &["done"]);
    tm.ok_at(&at("09:30"), &["break", "10m"]);
    let ended = tm.ok_at(&at("09:40"), &["break"]);
    assert!(!ended.stderr.contains("(D141)"), "a running break is ended by the ending arm: {}", ended.stderr);
    assert_eq!(evs(&breaks(&tm)), ["break_start", "break"]);
    let out = tm.ok_at(&at("09:35"), &["break"]);
    assert!(!out.stderr.contains("(D141)"), "{}", out.stderr);
    assert_eq!(evs(&breaks(&tm)), ["break_start", "break", "break_start"]);
}

/// **`tm undo` takes the line back**, and the journal line with it; the break is then again one D129 ended, and
/// D141 ends it again.
#[test]
fn undo_takes_the_d141_line_back() {
    let tm = j_tree_with_the_late_break();
    tm.ok_at(&at("09:40"), &["break"]);
    let undone = tm.ok_at(&at("11:15"), &["undo"]);
    assert!(undone.stdout.contains("undid break (break ended)"), "{}", undone.stdout);
    let last = tm.log().pop().expect("a log");
    assert_eq!(last["ev"], "undo", "{last}");
    assert_eq!(last["of"], "break", "{last}");
    let journal = tm.read(&format!("day/{TUE}.md"));
    assert!(!journal.contains("break ended 10m/10m"), "the journal line goes with the undo:\n{journal}");
    let again = tm.ok_at(&at("09:40"), &["break"]);
    assert!(again.stderr.contains("(D141)"), "{}", again.stderr);
}

/// **The replay's half (W-52 track K): the line ends the break at 09:40.** `^t1` reads fifty — the block less the
/// break's own ten minutes, the rest given back (D137) — so the day is 110; the plan draws one break 09:30–09:40;
/// `tm review day` counts it at ten. Until D141 the replay read no end in a `break` line stamped at a break D129 had
/// ended (P127), and the J day read ninety with a forty-minute break.
#[test]
#[ignore = "needs W-52 track K's replay (D141); the land un-ignores it"]
fn the_d141_line_ends_the_break_in_the_replay_p138() {
    let tm = j_tree_with_the_late_break();
    tm.ok_at(&at("09:40"), &["break"]);
    let now = at("11:15");
    let review = tm.json_at(&now, &["review", "day"]);
    assert_eq!(review["review"]["block_min"], 110, "^t1 fifty and ^t4 sixty: {review}");
    let rb = &review["review"]["breaks"];
    assert_eq!(rb["actual_min"], 10, "{rb}");
    assert_eq!(rb["breaks"].as_array().map(Vec::len), Some(1), "{rb}");
    let plan = tm.json_at(&now, &["plan"]);
    let drawn: Vec<(String, String)> = plan["segments"]
        .as_array()
        .cloned()
        .unwrap_or_default()
        .iter()
        .filter(|s| s["kind"] == "break" && s["start"].as_str() < Some("11:00"))
        .map(|s| (s["start"].as_str().unwrap_or_default().to_string(), s["end"].as_str().unwrap_or_default().to_string()))
        .collect();
    assert_eq!(drawn, [("09:30".to_string(), "09:40".to_string())], "{plan}");
}
