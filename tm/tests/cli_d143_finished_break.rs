//! **D143 through the binary** (stage 6 W-53 track H, README gaps 5682 and 5770, parity **P140**): a BACKDATED
//! `tm break --now <past> <length>` — its length typed — that a later logged block `start` already follows is LOGGED
//! FINISHED: its `break_start` and the `break` line that ends it after the typed length (the fork's shape, D105: `t`
//! the start, `actual_min` and `planned_min` the typed length, its place), journalled as a break taken and ended, said
//! as a finished break, and nothing left running in `.tm/state.json`. So it neither runs to that start (D129) nor is
//! ended by the next `tm break` (D141).
//!
//! The W-52 critic's note 3: inside a block worked 09:00–10:00 (`^t4` begun at 10:10 after it), `tm break --now 09:20
//! 5m` then `tm break --now 09:40 5m` — two five-minute breaks meant — read as one break of `20m of 5m`, `^t1` at
//! forty where fifty were worked, the second length and start discarded.
//!
//! D129 still governs a break typed with NO length (it runs until the later start), and a length that would run PAST
//! that start (the kernel would read the line two ways, README gap 5770): both keep the behaviour before D143.

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

/// Every `break` and `break_start` line of the log, in file order.
fn breaks(tm: &Tm) -> Vec<Value> {
    tm.log().into_iter().filter(|e| e["ev"] == "break" || e["ev"] == "break_start").collect()
}

fn evs(b: &[Value]) -> Vec<String> {
    b.iter().map(|e| e["ev"].as_str().unwrap_or_default().to_string()).collect()
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

/// **D143 (P140): the critic's sequence reads two five-minute breaks.** Each `tm break --now <past> 5m` writes its
/// `break_start` and its `break` line, stamped at its start with `actual_min` five; the day reads `^t1` at fifty
/// (110 with `^t4`'s sixty) and two breaks of five; `tm plan` draws `09:20 break 5m` and `09:40 break 5m`; nothing is
/// left running in `.tm/state.json`. Until D143 the second `tm break` ended the first at 09:40 (D141): one break of
/// twenty, `^t1` at forty.
#[test]
fn two_backdated_breaks_with_a_length_read_as_two_finished_breaks_p140() {
    let tm = j_tree();
    let first = tm.ok_at(&at("09:20"), &["break", "5m"]);
    assert_eq!(
        first.stdout.trim(),
        "break 5m · 09:20–09:25 · logged finished (a later start follows it, D143)",
        "said as a finished break"
    );
    assert!(!first.stderr.contains("(D129)"), "no D129 notice: {}", first.stderr);
    assert!(tm.state()["break"].is_null(), "nothing left running: {}", tm.state());
    tm.ok_at(&at("09:40"), &["break", "5m"]);
    let b = breaks(&tm);
    assert_eq!(evs(&b), ["break_start", "break", "break_start", "break"], "{b:?}");
    for (i, hm) in [(1, "09:20"), (3, "09:40")] {
        assert_eq!(b[i]["t"], at(hm), "the line is stamped at its break's start: {b:?}");
        assert_eq!(b[i]["actual_min"], 5, "{b:?}");
        assert_eq!(b[i]["planned_min"], 5, "{b:?}");
    }
    assert_eq!(review(&tm), (110, vec![5, 5]), "two breaks of five, ^t1 fifty");
    let plan = tm.ok_at(&at("11:15"), &["plan"]).stdout;
    assert!(plan.contains("09:20  ·      break 5m") && plan.contains("09:40  ·      break 5m"), "{plan}");
    assert!(tm.state()["break"].is_null(), "nothing left running: {}", tm.state());
    let journal = tm.read(&format!("day/{TUE}.md"));
    for line in ["09:20 break 5m", "09:25 break ended 5m/5m", "09:40 break 5m", "09:45 break ended 5m/5m"] {
        assert!(journal.contains(line), "the journal holds {line:?}:\n{journal}");
    }
}

/// **`--json`, and the place.** `action` is `finished`, with the typed minutes as both `planned_min` and `actual_min`
/// and the place typed; the log's two lines carry the place; no `superseded_end` (D141's key).
#[test]
fn a_finished_break_reports_itself_and_keeps_its_place_p140() {
    let tm = j_tree();
    let v = tm.json_at(&at("09:20"), &["break", "5m", "--where", "walk"]);
    assert_eq!(v["action"], "finished", "{v}");
    assert_eq!(v["planned_min"], 5, "{v}");
    assert_eq!(v["actual_min"], 5, "{v}");
    assert_eq!(v["place"], "walk", "{v}");
    assert!(v.get("superseded_end").is_none(), "{v}");
    let b = breaks(&tm);
    assert_eq!(evs(&b), ["break_start", "break"], "{b:?}");
    assert!(b.iter().all(|e| e["where"] == "walk"), "{b:?}");
}

/// **A length that reaches exactly to the later start is logged finished too**: `--now 09:50 20m` before 10:10's
/// start writes both lines, and the day reads the break at twenty, as the length says (`^t1`'s last ten minutes
/// netted).
#[test]
fn a_length_that_ends_at_the_later_start_is_logged_finished_p140() {
    let tm = j_tree();
    let out = tm.ok_at(&at("09:50"), &["break", "20m"]);
    assert!(out.stdout.contains("09:50–10:10 · logged finished"), "{}", out.stdout);
    assert_eq!(evs(&breaks(&tm)), ["break_start", "break"]);
    assert_eq!(review(&tm), (110, vec![20]), "^t1's last ten minutes netted, ^t4 whole");
}

/// **D129 still governs a break typed with no length, and one whose length runs past the later start** (README gap
/// 5770): one `break_start`, the D129 notice (with the typed length named when it runs past), the break read to the
/// start — the behaviour before D143.
#[test]
fn no_length_or_a_length_past_the_start_keeps_d129() {
    let tm = j_tree();
    let out = tm.ok_at(&at("09:50"), &["break"]);
    assert!(out.stderr.contains("ended at 10:10") && out.stderr.contains("(D129)"), "{}", out.stderr);
    assert_eq!(evs(&breaks(&tm)), ["break_start"]);
    assert_eq!(review(&tm), (110, vec![20]), "^t1's last ten minutes netted, ^t4 whole");

    let tm = j_tree();
    let out = tm.ok_at(&at("09:50"), &["break", "30m"]);
    assert!(
        out.stderr.contains("ended at 10:10")
            && out.stderr.contains("the 30m typed would run past that start")
            && out.stderr.contains("(D143)"),
        "{}",
        out.stderr
    );
    assert_eq!(out.stdout.trim(), "break 30m", "the reply before D143");
    assert_eq!(evs(&breaks(&tm)), ["break_start"], "no line the kernel would read two ways");
    assert_eq!(review(&tm), (110, vec![20]), "read to the start, as D129 reads it: ^t4 keeps its sixty");
}

/// **A live break is unchanged**: with no later `start` logged, `tm break 20m` begins a break that runs.
#[test]
fn a_break_with_no_later_start_still_runs() {
    let tm = j_tree();
    let v = tm.json_at(&at("11:20"), &["break", "15m"]);
    assert_eq!(v["action"], "started", "{v}");
    assert_eq!(evs(&breaks(&tm)), ["break_start"]);
    assert_eq!(tm.state()["break"]["planned_min"], 15, "{}", tm.state());
}

/// **D141's arm does not reach a finished break**: `tm break --now 09:22`, inside the 09:20–09:25 break D143 logged,
/// is no end — the break's own line ended it, so the kernel's fact (`Replay.endable`) leaves it out — and begins a
/// break of its own, which D129 ends at 10:10; the day reads the two as their union (D142).
#[test]
fn a_tm_break_inside_a_finished_break_is_not_its_end() {
    let tm = j_tree();
    tm.ok_at(&at("09:20"), &["break", "5m"]);
    let out = tm.ok_at(&at("09:22"), &["break"]);
    assert!(!out.stderr.contains("(D141)"), "{}", out.stderr);
    assert!(out.stderr.contains("ended at 10:10"), "{}", out.stderr);
    let b = breaks(&tm);
    assert_eq!(evs(&b), ["break_start", "break", "break_start"], "{b:?}");
    assert_eq!(b[1]["actual_min"], 5, "the finished break keeps its five: {b:?}");
    assert_eq!(review(&tm), (80, vec![5, 45]), "the union 09:20–10:10, the later break drawn after 09:25");
}

/// **`tm undo` takes both lines back as one step**: the step's two events are each cancelled (the log gains two
/// `undo` lines) and the day reads as before the break.
#[test]
fn undo_takes_a_finished_break_back_in_one_step() {
    let tm = j_tree();
    tm.ok_at(&at("09:20"), &["break", "5m"]);
    let before = tm.log().len();
    let out = tm.ok_at(&at("11:20"), &["undo"]);
    assert!(out.stdout.contains("undid break (break finished)"), "{}", out.stdout);
    let log = tm.log();
    let undos: Vec<&Value> = log[before..].iter().filter(|e| e["ev"] == "undo").collect();
    assert_eq!(undos.len(), 2, "one undo per line of the step: {undos:?}");
    assert_eq!(review(&tm), (120, vec![]));
}

/// **Deleting `.tm/state.json` changes nothing** (D42): the finished break is the log's alone.
#[test]
fn a_finished_break_survives_the_cache_deletion() {
    let tm = j_tree();
    tm.ok_at(&at("09:20"), &["break", "5m"]);
    let plan = tm.ok_at(&at("11:15"), &["plan"]).stdout;
    let now = tm.json_at(&at("11:15"), &["now"]);
    let rev = review(&tm);
    std::fs::remove_file(tm.plan.join(".tm/state.json")).expect("the cache");
    assert_eq!(review(&tm), rev);
    assert_eq!(tm.ok_at(&at("11:15"), &["plan"]).stdout, plan);
    assert_eq!(tm.json_at(&at("11:15"), &["now"]), now);
}
