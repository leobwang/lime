//! **D143 through the binary** (stage 6 W-53 track H, README gaps 5682 and 5770, parity **P140**): a BACKDATED
//! `tm break --now <past> <length>` — its length typed — that a later logged block `start` already follows is LOGGED
//! FINISHED, in ONE plain `break` line (the fork's shape: `t` the start, `actual_min` and `planned_min` the typed
//! length, its place) and NO `break_start` — P140 as restated at stage 6 W-53 repair track H; until then it was a
//! `break_start` and that line, the pair the kernel read P127's way —, journalled as a break taken and ended, said as a
//! finished break, and nothing left running in `.tm/state.json`. So it neither runs to that start (D129) nor is ended
//! by the next `tm break` (D141). **Since the owner's D148 (parity P146) the length is logged whatever start it runs
//! past**: the replay nets the later block by the minutes the break runs into it (D92).
//!
//! The W-52 critic's note 3: inside a block worked 09:00–10:00 (`^t4` begun at 10:10 after it), `tm break --now 09:20
//! 5m` then `tm break --now 09:40 5m` — two five-minute breaks meant — read as one break of `20m of 5m`, `^t1` at
//! forty where fifty were worked, the second length and start discarded.
//!
//! D129 still governs a break typed with NO length (it runs until the later start).

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

/// **D143 (P140): the critic's sequence reads two five-minute breaks.** Each `tm break --now <past> 5m` writes one
/// plain `break` line and no `break_start`, stamped at its start with `actual_min` five (120 → 115 → 110); the day
/// reads `^t1` at fifty (110 with `^t4`'s sixty) and two breaks of five; `tm plan` draws `09:20 break 5m` and `09:40
/// break 5m`; nothing is left running in `.tm/state.json`. Until D143 the second `tm break` ended the first at 09:40
/// (D141): one break of twenty, `^t1` at forty.
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
    assert_eq!(review(&tm), (115, vec![5]), "one break of five");
    tm.ok_at(&at("09:40"), &["break", "5m"]);
    let b = breaks(&tm);
    assert_eq!(evs(&b), ["break", "break"], "one plain line each, no break_start: {b:?}");
    for (i, hm) in [(0, "09:20"), (1, "09:40")] {
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
/// and the place typed, and `finished` its span; the log's one line carries the place; no `superseded_end` (D141's
/// key).
#[test]
fn a_finished_break_reports_itself_and_keeps_its_place_p140() {
    let tm = j_tree();
    let v = tm.json_at(&at("09:20"), &["break", "5m", "--where", "walk"]);
    assert_eq!(v["action"], "finished", "{v}");
    assert_eq!(v["planned_min"], 5, "{v}");
    assert_eq!(v["actual_min"], 5, "{v}");
    assert_eq!(v["place"], "walk", "{v}");
    assert!(v.get("superseded_end").is_none(), "{v}");
    assert_eq!(v["finished"]["start"], "09:20", "{v}");
    assert_eq!(v["finished"]["end"], "09:25", "{v}");
    assert_eq!(v["finished"]["actual_min"], 5, "{v}");
    assert!(v["finished"].get("into_start").is_none(), "it ends before the later start: {v}");
    let b = breaks(&tm);
    assert_eq!(evs(&b), ["break"], "{b:?}");
    assert!(b.iter().all(|e| e["where"] == "walk"), "{b:?}");
}

/// **A length that reaches exactly to the later start is logged finished too**: `--now 09:50 20m` before 10:10's
/// start writes its one line, and the day reads the break at twenty, as the length says (`^t1`'s last ten minutes
/// netted).
#[test]
fn a_length_that_ends_at_the_later_start_is_logged_finished_p140() {
    let tm = j_tree();
    let out = tm.ok_at(&at("09:50"), &["break", "20m"]);
    assert!(out.stdout.contains("09:50–10:10 · logged finished"), "{}", out.stdout);
    assert_eq!(evs(&breaks(&tm)), ["break"]);
    assert_eq!(review(&tm), (110, vec![20]), "^t1's last ten minutes netted, ^t4 whole");
}

/// **D129 still governs a break typed with no length**: one `break_start`, the D129 notice, the break read to the
/// start — the behaviour before D143.
#[test]
fn no_length_keeps_d129() {
    let tm = j_tree();
    let out = tm.ok_at(&at("09:50"), &["break"]);
    assert!(out.stderr.contains("ended at 10:10") && out.stderr.contains("(D129)"), "{}", out.stderr);
    assert_eq!(evs(&breaks(&tm)), ["break_start"]);
    assert_eq!(review(&tm), (110, vec![20]), "^t1's last ten minutes netted, ^t4 whole");
}

/// **D148 (P146, README gap 5770): a length that runs PAST the later start is logged finished at its typed length**,
/// and the replay nets the later block by the minutes the break runs into it (D92): `tm break --now 09:50 30m` with
/// `^t4` started at 10:10 writes one plain `break` line of thirty, says so naming the start it runs past, and the day
/// reads the break at thirty and `^t4` at fifty — `tm plan` draws `09:50 break 30m` and `^t4` from 10:20. Until D148
/// the verb wrote the `break_start` alone, D129 ended it at 10:10 (twenty), `^t4` kept sixty and the reply was
/// `break 30m`, a running break's.
#[test]
fn a_length_past_the_later_start_is_logged_finished_and_nets_the_block_p146() {
    let tm = j_tree();
    let out = tm.ok_at(&at("09:50"), &["break", "30m"]);
    assert_eq!(
        out.stdout.trim(),
        "break 30m · 09:50–10:20 · logged finished (it runs past the `start` at 10:10, whose block it nets, D148)",
        "{}",
        out.stderr
    );
    assert!(!out.stderr.contains("(D129)"), "no D129 notice: {}", out.stderr);
    let b = breaks(&tm);
    assert_eq!(evs(&b), ["break"], "one plain line: {b:?}");
    assert_eq!((b[0]["actual_min"].as_u64(), b[0]["planned_min"].as_u64()), (Some(30), Some(30)), "{b:?}");
    assert_eq!(review(&tm), (100, vec![30]), "^t1 fifty, ^t4 fifty — the ten minutes the break runs into it netted");
    let plan = tm.ok_at(&at("12:30"), &["plan"]).stdout;
    assert!(plan.contains("09:50  ·      break 30m"), "{plan}");
    assert!(plan.lines().any(|l| l.starts_with("10:20") && l.contains("(50m)")), "{plan}");
    assert!(tm.state()["break"].is_null(), "nothing left running: {}", tm.state());

    let tm = j_tree();
    let v = tm.json_at(&at("09:50"), &["break", "30m"]);
    assert_eq!(v["action"], "finished", "{v}");
    assert_eq!(v["finished"]["end"], "10:20", "{v}");
    assert_eq!(v["finished"]["into_start"], "10:10", "{v}");
}

/// **D148 reaches D126**: when the block the line nets was STOPPED, its `est:` is rewritten as `stop` would have
/// written it with the minutes the log now counts, and the correction is logged as an `edit` — `^t4` stopped at 11:10
/// with `5m` left, then `tm break --now 09:50 30m`: `15m`, ten minutes more, the ten the break ran into the block.
#[test]
fn a_finished_break_that_nets_a_stopped_block_corrects_its_estimate_p146() {
    let tm = Tm::empty();
    tm.ok_at(&at("06:00"), &["init", "--example"]);
    tm.ok_at(&at("07:00"), &["wake", "07:00"]);
    tm.ok_at(&at("08:00"), &["arrive", "home"]);
    tm.ok_at(&at("09:00"), &["start", "^t1"]);
    tm.ok_at(&at("10:00"), &["done"]);
    tm.ok_at(&at("10:10"), &["start", "^t4"]);
    tm.ok_at(&at("11:10"), &["stop"]);
    let line = |tm: &Tm| {
        tm.read("week/2026-W37.md").lines().find(|l| l.ends_with("^t4")).unwrap_or_default().to_string()
    };
    assert!(line(&tm).contains(" 5m "), "{}", line(&tm));
    let out = tm.ok_at(&at("09:50"), &["break", "30m"]);
    assert!(out.stderr.contains("^t4's estimate is now 15m (was 5m)") && out.stderr.contains("(D126)"), "{}", out.stderr);
    assert!(line(&tm).contains(" 15m "), "{}", line(&tm));
    let edit = tm.log().into_iter().rfind(|e| e["ev"] == "edit").expect("the correction is logged");
    assert_eq!((edit["id"].as_str(), edit["to"].as_str()), (Some("t4"), Some("15m")), "{edit}");
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

/// **D141's arm does not reach a finished break; D147 re-times it** (parity P145): `tm break --now 09:22`, inside the
/// 09:20–09:25 break D143 logged, is no D141 end — the break's own line ended it, so `Replay.endable` leaves it out —
/// and re-times the break to end at 09:22: one more `break` line at 09:20 carrying its planned 5 and `actual_min` 2,
/// which the kernel reads as that break's end (P143). Until the W-53 repair's land it began a break of its own that
/// D129 ended at 10:10 (the test was `a_tm_break_inside_a_finished_break_is_not_its_end`).
#[test]
fn a_tm_break_inside_a_finished_break_retimes_it_p145() {
    let tm = j_tree();
    tm.ok_at(&at("09:20"), &["break", "5m"]);
    let out = tm.ok_at(&at("09:22"), &["break"]);
    let said = format!("{}{}", out.stdout, out.stderr);
    assert!(!said.contains("(D141)") && !said.contains("(D129)") && said.contains("(D147)"), "{said}");
    let b = breaks(&tm);
    assert_eq!(evs(&b), ["break", "break"], "{b:?}");
    assert_eq!((b[1]["t"].as_str(), b[1]["planned_min"].as_u64(), b[1]["actual_min"].as_u64()), (b[0]["t"].as_str(), Some(5), Some(2)), "{b:?}");
    assert_eq!(review(&tm), (118, vec![2]), "the break 09:20–09:22 alone, the block netted by it");
}

/// **`tm undo` takes the finished break back**: the step's one line is cancelled (one `undo` line; two while the step
/// was a `break_start` and its line) and the day reads as before the break.
#[test]
fn undo_takes_a_finished_break_back_in_one_step() {
    let tm = j_tree();
    tm.ok_at(&at("09:20"), &["break", "5m"]);
    let before = tm.log().len();
    let out = tm.ok_at(&at("11:20"), &["undo"]);
    assert!(out.stdout.contains("undid break (break finished)"), "{}", out.stdout);
    let log = tm.log();
    let undos: Vec<&Value> = log[before..].iter().filter(|e| e["ev"] == "undo").collect();
    assert_eq!(undos.len(), 1, "one undo per line of the step: {undos:?}");
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

/// The F1 tree (the W-53 critic's first finding): `^t4` started at 10:10 after `^t1` 09:00–10:00, and a break of
/// twenty begun at 10:30 left running.
fn f1_tree() -> Tm {
    let tm = Tm::empty();
    tm.ok_at(&at("06:00"), &["init", "--example"]);
    tm.ok_at(&at("07:00"), &["wake", "07:00"]);
    tm.ok_at(&at("08:00"), &["arrive", "home"]);
    tm.ok_at(&at("09:00"), &["start", "^t1"]);
    tm.ok_at(&at("10:00"), &["done"]);
    tm.ok_at(&at("10:10"), &["start", "^t4"]);
    tm.ok_at(&at("10:30"), &["break", "20m"]);
    tm
}

/// **D145's host half: a backdated finished break does not touch the running break's cache** (stage 6 W-53 repair
/// track H). With a break running since 10:30, `tm break --now 09:20 5m` writes its one plain `break` line and nothing
/// else — no `break_start` at 09:20 — and `.tm/state.json` still holds the 10:30 break, its planned twenty minutes and
/// the running block paused under it. Until the repair the verb wrote a `break_start` at 09:20 over the cache's running
/// break and then dropped it ("the cache this verb just wrote is put right"), the 10:30 break lost from the cache.
#[test]
fn a_backdated_finished_break_leaves_the_running_breaks_cache_p140() {
    let tm = f1_tree();
    let before = breaks(&tm);
    let out = tm.ok_at(&at("09:20"), &["break", "5m"]);
    assert!(out.stdout.contains("09:20–09:25 · logged finished"), "{}", out.stdout);
    let after = breaks(&tm);
    assert_eq!(after.len(), before.len() + 1, "{after:?}");
    let last = &after[after.len() - 1];
    assert_eq!((last["ev"].as_str(), last["t"].as_str()), (Some("break"), Some(at("09:20").as_str())), "{after:?}");
    let state = tm.state();
    assert_eq!(state["break"]["started"], "10:30", "the running break stays in the cache: {state}");
    assert_eq!(state["break"]["planned_min"], 20, "{state}");
    assert_eq!(state["active"]["paused"], true, "{state}");
}

/// **D145 end to end** (parity **P142**, track K's): after that backdated break, the replay keeps the 10:30 break
/// running — `tm now` at 10:40 reads `^t4` paused and `on break since 10:30 · 10m of 20m`, no verb re-logs the cached
/// break (D133 has nothing to log), `tm check` is silent, and deleting `.tm/state.json` changes nothing (D42).
#[test]
#[ignore = "P142: D145 (a finished break's `break` line ends only its own break) is unbuilt -- README gap 5820; un-ignore when it lands"]
fn a_backdated_finished_break_leaves_a_running_break_running_p142() {
    let tm = f1_tree();
    tm.ok_at(&at("09:20"), &["break", "5m"]);
    let now = tm.ok_at(&at("10:40"), &["now"]);
    assert!(!now.stderr.contains("(D133)"), "nothing to re-log: {}", now.stderr);
    assert!(now.stdout.contains("· paused\non break since 10:30 · 10m of 20m\n"), "{}", now.stdout);
    let starts = tm.log().into_iter().filter(|e| e["ev"] == "break_start").count();
    assert_eq!(starts, 1, "the 10:30 break's one break_start");
    assert!(tm.ok_at(&at("10:40"), &["check"]).stdout.contains("no problems"));
    let json = tm.json_at(&at("10:40"), &["now"]);
    std::fs::remove_file(tm.plan.join(".tm/state.json")).expect("the cache");
    assert_eq!(tm.json_at(&at("10:40"), &["now"]), json);
}
