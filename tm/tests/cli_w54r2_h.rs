//! **Stage 6 W-54 second repair track H, through the binary** — the W-54 repair's verifiers' defects on the host:
//!
//! * **The gate's one rule** (D-1, D-2, D-3; README gaps 5990-5992, the campaign's call, revisable by the owner): a
//!   no-length `tm break --now <t>` reads every held break's span. Inside exactly one break at an instant the kernel reads,
//!   or at its end: D147 (re-time / "already ends"); past its current end inside `out_to`: D150's Out; at the start, end or
//!   inside of MORE than one held break: refused by name, naming them; at the start of every break holding the instant:
//!   refused (D147); and never a new break where a held break's closed span holds the instant. Since the W-54 third repair
//!   the spans and ranges are track K's fact, `Replay::held_breaks`; `cli_w54r3_h.rs` carries what that moved.
//! * **D153** (D-4, parity P149 restated): D152's "already over" is the log's LATEST surviving stamp, never the last
//!   line in file order.
//! * **D-5** (README gap 5997): a running break's cache is compared with the log at the cache's resolution, the minute.
//!
//!
//! The day is the example tree, woken 07:00, home 08:00, `TZ` the plan's (America/Chicago), Tuesday 2026-09-08; the
//! "J day" adds `^t1` 09:00–10:00 and `^t4` 10:10–11:10, both done (`tm review day` 120 with no break).

mod cli_common;

use cli_common::Tm;
use serde_json::Value;

const TUE: &str = "2026-09-08";
const WEEK: &str = "week/2026-W37.md";

fn at(hm: &str) -> String {
    if hm.len() == 5 {
        format!("{TUE}T{hm}:00-05:00")
    } else {
        format!("{TUE}T{hm}-05:00")
    }
}

fn fresh() -> Tm {
    let tm = Tm::empty();
    tm.ok_at(&at("06:00"), &["init", "--example"]);
    tm.ok_at(&at("07:00"), &["wake", "07:00"]);
    tm.ok_at(&at("08:00"), &["arrive", "home"]);
    tm
}

/// The J day, then each `(at, length)` typed as `tm break --now <at> [length]` (`""` for none).
fn j_day(breaks: &[(&str, &str)]) -> Tm {
    let tm = fresh();
    tm.ok_at(&at("09:00"), &["start", "^t1"]);
    tm.ok_at(&at("10:00"), &["done"]);
    tm.ok_at(&at("10:10"), &["start", "^t4"]);
    tm.ok_at(&at("11:10"), &["done"]);
    for (t, len) in breaks {
        if len.is_empty() {
            tm.ok_at(&at(t), &["break"]);
        } else {
            tm.ok_at(&at(t), &["break", len]);
        }
    }
    tm
}

/// `tm review day` at 12:30: block minutes and each break's minutes, sorted (the records' order is the kernel's).
fn review(tm: &Tm) -> (u64, Vec<u64>) {
    let v = tm.json_at(&at("12:30"), &["review", "day"]);
    let r = &v["review"];
    let mut breaks: Vec<u64> = r["breaks"]["breaks"]
        .as_array()
        .unwrap_or_else(|| panic!("{v}"))
        .iter()
        .map(|b| b["actual_min"].as_u64().unwrap_or_default())
        .collect();
    breaks.sort_unstable();
    (r["block_min"].as_u64().unwrap_or_else(|| panic!("{v}")), breaks)
}

/// Nothing written: the log, the day file and `.tm/state.json` byte for byte as they were around `f`.
fn unchanged<T>(tm: &Tm, f: impl FnOnce() -> T) -> T {
    let (log0, day0, state0) = (tm.read(".tm/log.jsonl"), tm.read(&format!("day/{TUE}.md")), tm.read(".tm/state.json"));
    let r = f();
    assert_eq!(tm.read(".tm/log.jsonl"), log0, "nothing logged");
    assert_eq!(tm.read(&format!("day/{TUE}.md")), day0, "nothing journalled");
    assert_eq!(tm.read(".tm/state.json"), state0, "the cache untouched");
    r
}

/// A no-length `tm break --now <hm>` refused: non-zero, nothing written, the review as it was. The message.
fn refused(tm: &Tm, hm: &str) -> String {
    let r0 = review(tm);
    let out = unchanged(tm, || tm.run_at(&at(hm), &["break"]));
    assert_ne!(out.code, 0, "refused: {}", out.stdout);
    assert_eq!(review(tm), r0, "the review unchanged");
    out.stderr
}

/// A no-length `tm break --now <hm>` that changes nothing and says so: exit 0, nothing written. Its reply.
fn already_ends(tm: &Tm, hm: &str) -> String {
    let r0 = review(tm);
    let out = unchanged(tm, || tm.ok_at(&at(hm), &["break"]));
    assert_eq!(review(tm), r0, "the review unchanged");
    out.stdout.trim().to_string()
}

// ---------------------------------------------------------------------------------------------------------------
// D-1: never a new break at the edge of an overlapped break

/// **E1** (`09:20 10m`, `09:25 10m`, then `--now 09:35`): 09:35 is the end of the 09:25 break and of no other — "already
/// ends", nothing written, `105`. On ba525fa: a new break D129 ran to 10:10 (`80`); on 263010a's kernel the fact omits
/// both breaks, and this host refuses by name (the 09:25 break unlisted), never beginning a break.
#[test]
fn e1_at_the_end_of_an_overlapped_break_it_already_ends() {
    let tm = j_day(&[("09:20", "10m"), ("09:25", "10m")]);
    assert_eq!(review(&tm), (105, vec![5, 10]));
    assert_eq!(already_ends(&tm, "09:35"), "break 09:25–09:35 already ends at 09:35 — nothing written (D147)");
}

/// **E1 on 263010a's kernel**: whatever the fact lists, no break begins at the end of a held break (rule 3) — refused or
/// "already ends", never a `break_start`, the review `105`.
#[test]
fn e1_never_begins_a_break_at_the_end_of_an_overlapped_break() {
    let tm = j_day(&[("09:20", "10m"), ("09:25", "10m")]);
    let n0 = tm.log().len();
    let out = tm.run_at(&at("09:35"), &["break"]);
    assert_eq!(tm.log().len(), n0, "nothing logged: {}{}", out.stdout, out.stderr);
    assert!(!out.stderr.contains("(D129)"), "{}", out.stderr);
    assert_eq!(review(&tm), (105, vec![5, 10]));
}

/// **E3** (`10:30 10m`, `10:30 15m`, then `--now 10:45`): the fifteen-minute break's end alone — "already ends", `105`.
/// On ba525fa: "break 20m" and no notice, `80`.
#[test]
fn e3_at_the_end_of_the_longer_of_two_breaks_of_one_start_it_already_ends() {
    let tm = j_day(&[("10:30", "10m"), ("10:30", "15m")]);
    assert_eq!(review(&tm), (105, vec![5, 10]));
    assert_eq!(already_ends(&tm, "10:45"), "break 10:30–10:45 already ends at 10:45 — nothing written (D147)");
}

/// **F3** (E3's day, `--now 10:30`): the start of both breaks — refused at its start (D147), naming them.
#[test]
fn f3_at_the_start_of_two_breaks_is_refused() {
    let tm = j_day(&[("10:30", "10m"), ("10:30", "15m")]);
    let said = refused(&tm, "10:30");
    assert!(said.contains("10:30–10:40") && said.contains("own start") && said.contains("(D147)"), "{said}");
}

/// **F5** (E1's day, `--now 09:30`) — the campaign's call: 09:30 is the 09:20 break's end and inside the 09:25 break, so
/// which break the instant names is not clear: refused by name, naming both (418e5d5 re-timed the 09:25 break to 09:30;
/// ba525fa began a break to 10:10).
#[test]
fn f5_at_one_breaks_end_inside_another_is_refused_as_ambiguous() {
    let tm = j_day(&[("09:20", "10m"), ("09:25", "10m")]);
    let said = refused(&tm, "09:30");
    assert!(said.contains("more than one logged break") && said.contains("09:20–09:30 (its end)"), "{said}");
}

/// **F1** (E1's day, `--now 09:20`): the 09:20 break's own start — refused (D147).
#[test]
fn f1_at_the_start_of_an_overlapped_break_is_refused() {
    let tm = j_day(&[("09:20", "10m"), ("09:25", "10m")]);
    let said = refused(&tm, "09:20");
    assert!(said.contains("a break is logged 09:20–09:30") && said.contains("own start"), "{said}");
}

/// **F2** (nested: `09:20 30m`, `09:30 5m`, then `--now 09:20`): the outer break's own start — refused (D147).
#[test]
fn f2_at_the_start_of_a_break_that_nests_another_is_refused() {
    let tm = j_day(&[("09:20", "30m"), ("09:30", "5m")]);
    let said = refused(&tm, "09:20");
    assert!(said.contains("a break is logged 09:20–09:50") && said.contains("own start"), "{said}");
}

/// **Adjoining** (`09:20 10m`, `09:30 10m`, then `--now 09:30`): one break's end and the other's start — refused by name.
/// This is the AtEnd guard's binary row (README gap 5993): with `retime_in_the_way`'s AtEnd branch planted to `None` it
/// says "already ends" and exits 0.
#[test]
fn at_one_breaks_end_and_anothers_start_is_refused() {
    let tm = j_day(&[("09:20", "10m"), ("09:30", "10m")]);
    let said = refused(&tm, "09:30");
    assert!(said.contains("09:20–09:30 (its end), 09:30–09:40 (its start)"), "{said}");
}

// ---------------------------------------------------------------------------------------------------------------
// D-2: ambiguous instants are refused. (E2, B, C, C2 and D-3 were refused here from the W-54 second repair's land; since the
// W-54 third repair they read off track K's fact, and their rows are `cli_w54r3_h.rs`'s.)

/// **Nested at 09:32** (the critic's d9: inside both the outer and the nested break) — refused by name, naming both. The
/// Inside guard's binary row once K's fact lists the outer break (README gap 5993): with `retime_in_the_way`'s Inside
/// branch planted to `None` the outer break is re-timed to 09:32 while the nested one keeps the drawn break to 09:35.
#[test]
fn inside_a_break_and_the_break_it_nests_is_refused_naming_both() {
    let tm = j_day(&[("09:20", "30m"), ("09:30", "5m")]);
    let said = refused(&tm, "09:32");
    assert!(said.contains("more than one logged break — 09:20–09:50 (inside it), 09:30–09:35 (inside it)"), "{said}");
}

/// **E** (near-twins: `09:20 10m`, `09:21 10m`, then `--now 09:27`): inside both — refused by name.
#[test]
fn e_inside_near_twins_is_refused() {
    let tm = j_day(&[("09:20", "10m"), ("09:21", "10m")]);
    let said = refused(&tm, "09:27");
    assert!(said.contains("09:20–09:30 (inside it)") && said.contains("(D147)"), "{said}");
}

// ---------------------------------------------------------------------------------------------------------------
// D153 (parity P149 restated): "already over" is the log's latest surviving stamp

/// `^t4` running since 10:10, paused and unpaused at 10:50 (o.sh's tree).
fn o_tree() -> Tm {
    let tm = fresh();
    tm.ok_at(&at("10:10"), &["start", "^t4"]);
    tm.ok_at(&at("10:50"), &["pause"]);
    tm.ok_at(&at("10:50"), &["pause"]);
    tm
}

fn logged_finished(tm: &Tm, hm: &str, len: &str) {
    let out = tm.ok_at(&at(hm), &["break", len]);
    assert!(out.stdout.contains("logged finished (it lies inside ^t4, which is running"), "{hm}: {}{}", out.stdout, out.stderr);
}

fn stop_writes_ten_left(tm: &Tm) {
    let out = tm.ok_at(&at("11:10"), &["stop"]);
    assert!(out.stdout.contains("stopped ^t4 after 50m · 10m left"), "{}{}", out.stdout, out.stderr);
    assert!(tm.line(WEEK, "t4").contains(" 10m "), "{}", tm.line(WEEK, "t4"));
}

/// **o.sh, the first order** (`10:15 5m`, then `10:40 5m`): the second break's end, 10:45, is before the 10:50 unpause,
/// so both are logged finished, and `stop` writes `10m` left into the week file. On 263010a the 10:15 line was the last
/// in FILE order, so the second began a running break and `stop` wrote `35m`.
#[test]
fn d153_a_retro_line_does_not_hide_the_latest_stamp() {
    let tm = o_tree();
    logged_finished(&tm, "10:15", "5m");
    logged_finished(&tm, "10:40", "5m");
    stop_writes_ten_left(&tm);
}

/// **o.sh, the reverse order** (`10:40 5m`, then `10:15 5m`): both logged finished, `10m` left — as on 263010a.
#[test]
fn d153_the_reverse_order_logs_both_finished() {
    let tm = o_tree();
    logged_finished(&tm, "10:40", "5m");
    logged_finished(&tm, "10:15", "5m");
    stop_writes_ten_left(&tm);
}

/// **The owner's D152 drive with nothing after the block's start** (README gap 5892, reopened narrowed by D153): `^t4`
/// running since 10:10 and no later line, `tm break --now 10:20 10m` — no surviving line has reached 10:30, so the break
/// may still be running: it BEGINS (a `break_start`), as before D152.
#[test]
fn d153_with_nothing_logged_past_the_typed_end_a_break_begins() {
    let tm = fresh();
    tm.ok_at(&at("10:10"), &["start", "^t4"]);
    let out = tm.ok_at(&at("10:20"), &["break", "10m"]);
    assert!(!out.stdout.contains("logged finished"), "{}", out.stdout);
    assert_eq!(tm.last()["ev"], "break_start");
}

/// **An undone line witnesses "already over"** (restated at W-54 third repair track K for the owner's D154, which reverses D153
/// here: the instant was reached either way): `^t4` running since 10:10, a `pause` at 10:50 undone (the `undo` typed at 10:21),
/// then `tm break --now 10:20 10m` — the cancelled line is past 10:30, so the break is logged finished.
#[test]
fn d154_an_undone_line_past_the_typed_end_witnesses_it() {
    let tm = fresh();
    tm.ok_at(&at("10:10"), &["start", "^t4"]);
    tm.ok_at(&at("10:50"), &["pause"]);
    tm.ok_at(&at("10:21"), &["undo"]);
    assert_eq!(tm.last()["ev"], "undo");
    let out = tm.ok_at(&at("10:20"), &["break", "10m"]);
    assert!(out.stdout.contains("logged finished"), "{}", out.stdout);
    assert_eq!(tm.last()["ev"], "break");
}

// ---------------------------------------------------------------------------------------------------------------
// D-5: the running break's cache compared at the minute

/// **A break begun at a second past the minute** (`--now 09:20:44`): the log's `break_start` holds the seconds and
/// `.tm/state.json` holds `09:20`; a later verb says nothing about them (they agree to the minute). Until this repair
/// every later verb said "… a break began at 09:20 (20m, no place) and .tm/log.jsonl says one began at 09:20 (20m, no
/// place) — the log decides".
#[test]
fn a_break_begun_mid_minute_agrees_with_its_cache() {
    let tm = fresh();
    tm.ok_at(&at("09:00"), &["start", "^t1"]);
    tm.ok_at(&at("09:20:44"), &["break"]);
    assert_eq!(tm.last()["t"], at("09:20:44"));
    assert_eq!(tm.state()["break"]["started"], "09:20");
    for hm in ["09:25", "09:26"] {
        let out = tm.ok_at(&at(hm), &["now"]);
        assert!(!out.stderr.contains("the log decides"), "{hm}: {}", out.stderr);
        assert!(out.stdout.contains("on break since 09:20"), "{}", out.stdout);
    }
}

/// **The other direction (§5.8): a cache a minute off is still corrected, and said** — `.tm/state.json`'s break edited to
/// begin at 09:21: the log decides, by name.
#[test]
fn a_cache_a_minute_off_is_still_corrected() {
    let tm = fresh();
    tm.ok_at(&at("09:00"), &["start", "^t1"]);
    tm.ok_at(&at("09:20:44"), &["break"]);
    let path = tm.plan.join(".tm/state.json");
    let mut v: Value = serde_json::from_str(&std::fs::read_to_string(&path).expect("the cache")).expect("JSON");
    v["break"]["started"] = Value::from("09:21");
    std::fs::write(&path, serde_json::to_string_pretty(&v).expect("JSON")).expect("edit the cache");
    let out = tm.ok_at(&at("09:25"), &["now"]);
    assert!(
        out.stderr.contains("said a break began at 09:21") && out.stderr.contains("says one began at 09:20"),
        "{}",
        out.stderr
    );
}
