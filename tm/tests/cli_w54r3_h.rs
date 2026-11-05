//! **Stage 6 W-54 third repair track H, through the binary** (README gaps 6040-6059): the gate reads track K's fact,
//! `Replay::held_breaks`, per typed instant — every shape of the brief, each refusal's advice driven and not only said —
//! and the owner's **D154** through the verb (`inside_running_block` over `Replay::latest_t`, the kernel's `log.latestTyped`).
//!
//! The day is the example tree, woken 07:00, home 08:00, `TZ` the plan's (America/Chicago), Tuesday 2026-09-08; the
//! "J day" adds `^t1` 09:00–10:00 and `^t4` 10:10–11:10, both done (`tm review day` 120 with no break).

mod cli_common;

use std::fs;

use cli_common::Tm;

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
    typed(&tm, breaks);
    tm
}

fn typed(tm: &Tm, breaks: &[(&str, &str)]) {
    for (t, len) in breaks {
        if len.is_empty() {
            tm.ok_at(&at(t), &["break"]);
        } else {
            tm.ok_at(&at(t), &["break", len]);
        }
    }
}

/// A copy of the tree at `tm`, so what a read logs does not reach the tree under test.
fn copied(tm: &Tm) -> Tm {
    fn copy(from: &std::path::Path, to: &std::path::Path) {
        fs::create_dir_all(to).expect("a directory");
        for e in fs::read_dir(from).expect("a directory") {
            let e = e.expect("an entry");
            let target = to.join(e.file_name());
            if e.file_type().expect("a type").is_dir() {
                copy(&e.path(), &target);
            } else {
                fs::copy(e.path(), &target).expect("a copy");
            }
        }
    }
    let c = Tm::empty();
    copy(&tm.plan, &c.plan);
    c
}

/// `tm review day`'s block minutes at 12:30, on a copy.
fn review(tm: &Tm) -> u64 {
    let v = copied(tm).json_at(&at("12:30"), &["review", "day"]);
    v["review"]["block_min"].as_u64().unwrap_or_else(|| panic!("{v}"))
}

/// The minutes of `^t1`'s and `^t4`'s block rows `tm plan` draws at 12:30, on a copy.
fn plan_minutes(tm: &Tm) -> u64 {
    let v = copied(tm).json_at(&at("12:30"), &["plan"]);
    let hm = |s: &str| s[..2].parse::<u64>().expect("an hour") * 60 + s[3..5].parse::<u64>().expect("a minute");
    v["segments"]
        .as_array()
        .unwrap_or_else(|| panic!("{v}"))
        .iter()
        .filter(|s| s["kind"] == "block" && (s["item"] == "t1" || s["item"] == "t4"))
        .map(|s| hm(s["end"].as_str().expect("an end")) - hm(s["start"].as_str().expect("a start")))
        .sum()
}

/// A cold rebuild's review and plan, on a copy: `.tm/state.json` and the cache deleted.
fn cold(tm: &Tm) -> (u64, u64) {
    let c = copied(tm);
    fs::remove_file(c.plan.join(".tm/state.json")).expect("the cache");
    let _ = fs::remove_dir_all(c.plan.join(".tm/cache"));
    (review(&c), plan_minutes(&c))
}

/// One reading of the day: review, plan and a cold rebuild, all `want`.
fn reads(tm: &Tm, want: u64) {
    assert_eq!((review(tm), plan_minutes(tm), cold(tm)), (want, want, (want, want)), "review, plan, cold");
}

/// A no-length `tm break --now <hm>` refused: non-zero, nothing written, the review as it was. The message.
fn refused(tm: &Tm, hm: &str) -> String {
    refused_with(tm, hm, &["break"])
}

fn refused_with(tm: &Tm, hm: &str, args: &[&str]) -> String {
    let day = format!("day/{TUE}.md");
    let (log0, day0, state0, r0) = (tm.read(".tm/log.jsonl"), tm.read(&day), tm.read(".tm/state.json"), review(tm));
    let out = tm.run_at(&at(hm), args);
    assert_ne!(out.code, 0, "refused: {}", out.stdout);
    assert_eq!(tm.read(".tm/log.jsonl"), log0, "nothing logged: {}", out.stderr);
    assert_eq!(tm.read(&day), day0, "nothing journalled");
    assert_eq!(tm.read(".tm/state.json"), state0, "the cache untouched");
    assert_eq!(review(tm), r0);
    out.stderr
}

/// A no-length `tm break --now <hm>` that re-times the break begun at `from`, one plain `break` line at its own start.
fn retimes(tm: &Tm, hm: &str, from: &str) -> String {
    let n0 = tm.log().len();
    let out = tm.ok_at(&at(hm), &["break"]);
    let log = tm.log();
    assert_eq!(log.len(), n0 + 1, "one line: {}{}", out.stdout, out.stderr);
    assert_eq!((log[n0]["ev"].as_str(), log[n0]["t"].as_str()), (Some("break"), Some(at(from).as_str())), "{}", log[n0]);
    format!("{}{}", out.stdout, out.stderr)
}

/// A no-length `tm break --now <hm>` that begins a break: one `break_start` at the instant.
fn begins(tm: &Tm, hm: &str) -> String {
    let out = tm.ok_at(&at(hm), &["break"]);
    let last = tm.last();
    assert_eq!((last["ev"].as_str(), last["t"].as_str()), (Some("break_start"), Some(at(hm).as_str())), "{last}");
    format!("{}{}", out.stdout, out.stderr)
}

fn already_ends(tm: &Tm, hm: &str) -> String {
    let log0 = tm.read(".tm/log.jsonl");
    let out = tm.ok_at(&at(hm), &["break"]);
    assert_eq!(tm.read(".tm/log.jsonl"), log0, "nothing logged");
    out.stdout.trim().to_string()
}

// ---------------------------------------------------------------------------------------------------------------
// The defects' shapes

/// **A** (blocker; K's `Closed.restored`): the fifth line re-times the 09:40 break alone. Review 88, plan 88, cold 88. On
/// 213e827: review 98, plan 88, `tm check` "no problems"; on ba525fa refused.
#[test]
fn a_reads_88_on_the_review_the_plan_and_a_cold_rebuild() {
    let tm = j_day(&[("09:20", "30m"), ("09:30", ""), ("09:40", "15m"), ("09:20", "30m")]);
    reads(&tm, 85);
    assert!(retimes(&tm, "09:52", "09:40").contains("break 09:40–09:55 re-timed to end at 09:52 (D147)"));
    reads(&tm, 88);
}

/// **B's first** (`09:35 5m`, `09:30` D129, `09:45` D141's end): 09:47 is past the end a line stated and past the 09:35
/// break — D151 says a break begins, which D129 runs to 10:10. On 213e827's land: refused "inside the length typed for
/// it" (gap 6010's typed end).
#[test]
fn b_past_a_stated_end_a_break_begins() {
    let tm = j_day(&[("09:35", "5m"), ("09:30", ""), ("09:45", "")]);
    reads(&tm, 105);
    assert!(begins(&tm, "09:47").contains("began at 09:47 ended at 10:10"));
    reads(&tm, 92);
}

/// **B's second** (`09:20 10m`, `09:25 10m`, `09:31 2m`): 09:37 is outside every held break — a break begins. On 213e827's
/// land: refused, naming a break 09:30–09:35 the log does not hold.
#[test]
fn b_outside_every_held_break_a_break_begins() {
    let tm = j_day(&[("09:20", "10m"), ("09:25", "10m"), ("09:31", "2m")]);
    reads(&tm, 105);
    assert!(begins(&tm, "09:37").contains("began at 09:37 ended at 10:10"));
    reads(&tm, 82);
}

/// **C, the auditor's d5** (`09:27 10m`, re-timed to 09:30, `09:20 10m`, `09:25 10m`, then `--now 09:33`): on 213e827's land
/// refused, naming a phantom 09:30–09:35 (the second matching loop of held_spans handed one break's record to another).
/// The fact names no such break: only the 09:25 break's closed span holds 09:33, so it is re-timed, 107.
#[test]
fn c_d5_names_no_phantom_break() {
    let tm = j_day(&[("09:27", "10m"), ("09:30", ""), ("09:20", "10m"), ("09:25", "10m")]);
    reads(&tm, 105);
    assert!(retimes(&tm, "09:33", "09:25").contains("break 09:25–09:35 re-timed to end at 09:33 (D147)"));
    reads(&tm, 107);
}

/// **C2** (nested `09:20 30m`, `09:30 5m`, `--now 09:40`): past the nested break, inside the outer alone — re-timed, 100.
/// On 213e827: refused (gap 5974).
#[test]
fn c2_inside_the_outer_break_past_the_nested_one_is_re_timed() {
    let tm = j_day(&[("09:20", "30m"), ("09:30", "5m")]);
    assert!(retimes(&tm, "09:40", "09:20").contains("break 09:20–09:50 re-timed to end at 09:40 (D147)"));
    reads(&tm, 100);
}

/// **D-3** (`09:20 30m` → 09:40, `09:35 5m`, `--now 09:45`): past its end, inside `out_to` — D150, 95. On 213e827: refused
/// (gap 6010); on ba525fa a new break D129 ran to 10:10 (85).
#[test]
fn d3_past_a_nested_breaks_cover_is_re_timed_out() {
    let tm = j_day(&[("09:20", "30m"), ("09:40", ""), ("09:35", "5m")]);
    reads(&tm, 100);
    assert!(retimes(&tm, "09:45", "09:20").contains("break 09:20–09:40 re-timed out to end at 09:45 (D150)"));
    reads(&tm, 95);
}

/// **E2** (nested, `--now 09:50`, the outer break's own end): "already ends" — no fact is needed for it. On 213e827:
/// refused (the outer break unlisted).
#[test]
fn e2_at_the_end_of_a_break_that_nests_another_it_already_ends() {
    let tm = j_day(&[("09:20", "30m"), ("09:30", "5m")]);
    assert_eq!(already_ends(&tm, "09:50"), "break 09:20–09:50 already ends at 09:50 — nothing written (D147)");
    reads(&tm, 90);
}

/// **Gap 5971's B** (`09:20 10m`, `09:25 10m`, `--now 09:22`): inside the 09:20 break alone — re-timed, 108. On 213e827:
/// refused. Then the 09:25 break is frozen: `--now 09:28` is refused by name, the reason true (the 09:20 break let go of
/// 09:22–09:30), and the advice true: `tm undo` takes the 09:22 line back and 09:28 then meets both, refused as before it.
#[test]
fn gap_5971_b_is_re_timed_and_the_break_it_leaves_short_is_refused() {
    let tm = j_day(&[("09:20", "10m"), ("09:25", "10m")]);
    assert!(retimes(&tm, "09:22", "09:20").contains("re-timed to end at 09:22 (D147)"));
    reads(&tm, 108);
    let said = refused(&tm, "09:28");
    assert!(
        said.contains("lies in the break 09:25–09:35 (inside it)") && said.contains("the break 09:20–09:22, logged after it"),
        "{said}"
    );
    reads(&tm, 108);
    tm.ok_at(&at("09:29"), &["undo"]);
    reads(&tm, 105);
    assert!(refused(&tm, "09:28").contains("more than one logged break"));
}

/// **Gap 5971's C** (nested, `--now 09:25`): before the nested break, inside the outer alone — re-timed, 110. On 213e827:
/// refused.
#[test]
fn gap_5971_c_is_re_timed() {
    let tm = j_day(&[("09:20", "30m"), ("09:30", "5m")]);
    assert!(retimes(&tm, "09:25", "09:20").contains("re-timed to end at 09:25 (D147)"));
    reads(&tm, 110);
}

/// **E1's day at 09:28** (K's table: a line there reads, 110): two closed spans hold the instant, and the line may mean
/// either, so the gate refuses it — the correction's one rule. The kernel reading the line is K's; the verb does not write it.
#[test]
fn an_instant_two_spans_hold_stays_refused() {
    let tm = j_day(&[("09:20", "10m"), ("09:25", "10m")]);
    let said = refused(&tm, "09:28");
    assert!(said.contains("more than one logged break — 09:20–09:30 (inside it), 09:25–09:35 (inside it)"), "{said}");
}

/// **Gap 5973** (`09:40 5m`, `09:30` D129, `09:42` D141's end, then `--now 09:43`): the 09:40 break is frozen by the
/// stretch the 09:30 break let go of, so it is refused by name, where 213e827 replied "re-timed" and moved nothing. Review
/// and plan 105. K's second shape (D141's end 09:35, then 09:42): 110, refused.
#[test]
fn gap_5973_a_retime_that_would_move_nothing_is_refused() {
    let tm = j_day(&[("09:40", "5m"), ("09:30", ""), ("09:42", "")]);
    reads(&tm, 105);
    let said = refused(&tm, "09:43");
    assert!(said.contains("lies in the break 09:40–09:45 (inside it)") && said.contains("09:30–09:42, logged after it"), "{said}");
    reads(&tm, 105);
    let tm = j_day(&[("09:40", "5m"), ("09:30", ""), ("09:35", "")]);
    reads(&tm, 110);
    assert!(refused(&tm, "09:42").contains("lies in the break 09:40–09:45 (inside it)"));
    reads(&tm, 110);
}

/// **Gap 6024** (`09:20 30m`, `--now 09:30`, `09:40 15m`, `--now 09:32`, then `--now 09:45`): K's `frozen` is conservative
/// here, so it stays refused by name. **Both pieces of its advice are driven:** a length logs a finished break (D143), and
/// `tm undo` takes the 09:32 line back, after which 09:45 re-times the 09:40 break.
#[test]
fn gap_6024_is_refused_and_its_advice_does_what_it_says() {
    let keys = [("09:20", "30m"), ("09:30", ""), ("09:40", "15m"), ("09:32", "")];
    let tm = j_day(&keys);
    reads(&tm, 93);
    let said = refused(&tm, "09:45");
    assert!(
        said.contains("lies in the break 09:40–09:55 (inside it)")
            && said.contains("the break 09:20–09:32, logged after it")
            && said.contains("type a length to log a finished break beside it (D143)")
            && said.contains("`tm undo`"),
        "{said}"
    );
    let out = tm.ok_at(&at("09:45"), &["break", "2m"]);
    assert!(out.stdout.contains("logged finished"), "{}{}", out.stdout, out.stderr);
    reads(&tm, 93);

    let tm = j_day(&keys);
    tm.ok_at(&at("09:46"), &["undo"]);
    reads(&tm, 95);
    assert!(retimes(&tm, "09:45", "09:40").contains("break 09:40–09:55 re-timed to end at 09:45 (D147)"));
    reads(&tm, 105);
}

/// **A frozen break, past its end inside the end its own lines gave it**: the gate's OutNotRead arm. `09:40 15m` re-timed to
/// 09:45 (widest 09:55); `--now 09:30` (D129 to 10:10), ended at 09:33 (D141): what the 09:30 break let go of meets the 09:40
/// one, so a line for it is not read. At 09:50, which no closed span holds and only its widest end reaches: refused, saying
/// what is in the way. `tm undo` of the 09:33 line un-freezes it (a D129 ending reads again): D150 re-times it out.
#[test]
fn past_a_frozen_breaks_end_inside_its_widest_end_is_refused() {
    let tm = j_day(&[("09:40", "15m"), ("09:45", ""), ("09:30", ""), ("09:33", "")]);
    reads(&tm, 112);
    let said = refused(&tm, "09:50");
    assert!(said.contains("lies past the end of the break 09:40–09:45, inside the 09:55 its own lines gave it"), "{said}");
    assert!(said.contains("the break 09:30–09:33, logged after it") && said.contains("(D150)"), "{said}");
    reads(&tm, 112);
}

/// **A D129 ending a later break let go over: the D141 arm reads the fact too** (README gap 6041). `--now 09:35` (D129 to
/// 10:10), `09:20 30m`, `--now 09:25` — that re-time lets go of 09:25–09:50, which meets the ending, so a line ending it is
/// read as a break of its own. Until this repair `tm break --now 09:40` said "ends here" and nothing moved. At its own start
/// (P139) the advice is not "give a later instant" either.
#[test]
fn a_frozen_ending_is_refused_at_d141s_instant_and_at_its_start() {
    let tm = j_day(&[("09:35", ""), ("09:20", "30m"), ("09:25", "")]);
    let r0 = review(&tm);
    assert_eq!(r0, plan_minutes(&tm));
    let said = refused(&tm, "09:40");
    assert!(said.contains("lies in the break 09:35–10:10 (inside it)") && !said.contains("ends here"), "{said}");
    let said = refused(&tm, "09:35");
    assert!(said.contains("(D129)") && said.contains("a line would not end it") && !said.contains("give a later instant"), "{said}");
    tm.ok_at(&at("09:41"), &["undo"]);
    tm.ok_at(&at("09:41"), &["undo"]);
    assert!(tm.ok_at(&at("09:40"), &["break"]).stderr.contains("ends here"), "both lines back, the D141 end reads");
}

/// **After the blocks, a length is not offered** (README gap 6044): the frozen break's refusal says only `tm undo`, for a
/// length there would begin a running break inside it, not log a finished one. `11:20`–`11:45`, re-timed to 11:40; `11:42 3m`
/// ended at 11:45; the first re-timed to 11:30 — its let-go meets the second.
#[test]
fn past_the_last_block_the_refusal_offers_no_length() {
    let tm = j_day(&[("11:20", ""), ("11:45", ""), ("11:40", ""), ("11:42", "3m"), ("11:45", ""), ("11:30", "")]);
    let said = refused(&tm, "11:43");
    assert!(said.contains("lies in the break 11:42–11:45 (inside it)"), "{said}");
    assert!(!said.contains("type a length") && said.contains("`tm undo`"), "{said}");
}

/// **A length with nothing to end it begins a running break, inside a held span too** (README gap 6044: the invariant's
/// fourth clause, read literally, refuses this, and three rows that predate it pin it — `cli_d144_now_break.rs`'s gap 5775,
/// `cli_w54_h_breaks.rs`'s F3, `cli_week_grid.rs`'s union; so the behaviour stands and the shape goes to the owner). No start
/// follows, so D129's loss cannot happen: the break runs, drawn after the held one, the review and the plan agree.
#[test]
fn a_length_with_nothing_to_end_it_begins_a_running_break_inside_a_held_span() {
    let tm = j_day(&[("11:20", ""), ("11:30", "")]);
    let out = tm.ok_at(&at("11:25"), &["break", "5m"]);
    assert!(!out.stdout.contains("logged finished"), "{}{}", out.stdout, out.stderr);
    assert_eq!(tm.last()["ev"], "break_start");
    reads(&tm, 120);
}

/// **A twin the fact cannot show: "re-timed" would move nothing, so it is refused** (README gap 6045; the sweep's first seed).
/// `09:35 15m`, `09:15` (D129 to 10:10), `09:35 15m` (D146 ends it at 09:35 and logs a second 09:35–09:50, read as a break of
/// its own because the 09:15 break let go of the stretch): the fact holds one entry, the newest, and a line at 09:40 moves
/// only that one. Until the probe: "re-timed", review 85 before and after.
#[test]
fn a_hidden_twin_is_refused_rather_than_said_re_timed() {
    let tm = j_day(&[("09:35", "15m"), ("09:15", ""), ("09:35", "15m")]);
    reads(&tm, 85);
    let said = refused(&tm, "09:40");
    assert!(said.contains("would re-time the break 09:35–09:50") && said.contains("holds that break twice"), "{said}");
    reads(&tm, 85);
}

/// **Under a minute** (README gap 6042): a re-timing line carries whole minutes. `--now 09:20:30` would end the 09:20 break
/// at its start (refused, as at its start); `--now 09:30:30` past its end changes nothing, inside the widest end it gave
/// itself ("already ends"); `--now 09:24:30` ends it at 09:24.
#[test]
fn an_instant_with_seconds_reads_the_end_its_line_gives() {
    let tm = j_day(&[("09:20", "30m"), ("09:30", "")]);
    assert!(refused(&tm, "09:20:30").contains("own start"));
    assert_eq!(already_ends(&tm, "09:30:30"), "break 09:20–09:30 already ends at 09:30 — nothing written (D147)");
    assert!(retimes(&tm, "09:24:30", "09:20").contains("re-timed to end at 09:24"));
    reads(&tm, 116);
}

/// **Past the ends of two breaks, inside both widest ends** (`at_finished`'s last arm through the binary; until this repair the
/// latest begun went out): `09:20 30m` to 09:25, `09:26 30m` to 09:28, then `--now 09:40`: refused, naming each.
#[test]
fn past_two_breaks_ends_inside_both_widest_ends_is_refused_naming_both() {
    let tm = j_day(&[("09:20", "30m"), ("09:25", ""), ("09:26", "30m"), ("09:28", "")]);
    let said = refused(&tm, "09:40");
    assert!(said.contains("more than one logged break") && said.contains("09:20–09:25 (past its end") && said.contains("09:26–09:28 (past its end"), "{said}");
}

/// **A line whose whole minute another break holds** (`at_finished`'s seconds arm through the binary): `09:20 30m` to 09:30
/// (widest 09:50), `09:35 5m`, then `--now 09:40:30`: no closed span holds the instant, but the line would end the 09:20
/// break at 09:40, the 09:35 break's end. Refused, naming both.
#[test]
fn a_line_whose_whole_minute_another_break_holds_is_refused() {
    let tm = j_day(&[("09:20", "30m"), ("09:30", ""), ("09:35", "5m")]);
    let said = refused(&tm, "09:40:30");
    assert!(said.contains("more than one logged break") && said.contains("09:20–09:30") && said.contains("09:35–09:40"), "{said}");
}

/// **A length is offered where it logs a finished break, and does it** (Many's advice, driven): nested at 09:32, `3m`, D143
/// (the 10:10 start follows).
#[test]
fn a_many_refusals_length_does_what_it_says() {
    let tm = j_day(&[("09:20", "30m"), ("09:30", "5m")]);
    let said = refused(&tm, "09:32");
    assert!(said.contains("type a length to log a finished break beside it (D143)"), "{said}");
    let out = tm.ok_at(&at("09:32"), &["break", "3m"]);
    assert!(out.stdout.contains("logged finished"), "{}{}", out.stdout, out.stderr);
    reads(&tm, 90);
}

/// **A break past D94's bound is drawn and no longer held** (README gap 6043, the defence `drawn_break_at` is): a break on
/// 07-01, breaks on 08-20 and 08-21, then `tm break --now 07-01 09:10` — the kernel's held list has let the July break go, its
/// day is still in the replay's rows, and a break must not begin inside it. Refused by name. With the guard planted off a
/// `break_start` lands here.
#[test]
fn a_break_past_the_bound_of_held_breaks_is_refused_by_what_is_drawn() {
    let tm = Tm::empty();
    let on = |d: &str, hm: &str| format!("2026-{d}T{hm}:00-05:00");
    tm.ok_at(&on("07-01", "06:00"), &["init", "--example"]);
    tm.ok_at(&on("07-01", "07:00"), &["wake", "07:00"]);
    tm.ok_at(&on("07-01", "09:00"), &["break", "30m"]);
    tm.ok_at(&on("07-01", "09:30"), &["break"]);
    for d in ["08-20", "08-21"] {
        tm.ok_at(&on(d, "07:00"), &["wake", "07:00"]);
        tm.ok_at(&on(d, "09:00"), &["break", "30m"]);
        tm.ok_at(&on(d, "09:30"), &["break"]);
    }
    let log0 = tm.read(".tm/log.jsonl");
    let out = tm.run_at(&on("07-01", "09:10"), &["break"]);
    assert_ne!(out.code, 0, "{}", out.stdout);
    assert!(out.stderr.contains("a break is drawn 09:00–09:30 here that the kernel no longer holds"), "{}", out.stderr);
    assert_eq!(tm.read(".tm/log.jsonl"), log0, "nothing logged");
}

// ---------------------------------------------------------------------------------------------------------------
// D154 through the verb (`inside_running_block` over `Replay::latest_t`)

/// `^t4` running since 10:10.
fn running_t4() -> Tm {
    let tm = fresh();
    tm.ok_at(&at("10:10"), &["start", "^t4"]);
    tm
}

fn begins_a_running_break(tm: &Tm, hm: &str, len: &str) {
    let out = tm.ok_at(&at(hm), &["break", len]);
    assert!(!out.stdout.contains("logged finished"), "{}{}", out.stdout, out.stderr);
    assert_eq!(tm.last()["ev"], "break_start");
    let now = tm.ok_at(&at(hm), &["now"]).stdout;
    assert!(now.contains("on break since"), "{now}");
}

/// **A stated instant ahead of the clock is no witness** (D154): `tm energy 3 --at 18:00` at 10:12, then `tm break 5m` at
/// 10:15 begins a running break, and `tm now` agrees. On 213e827: logged finished while `tm now` showed the block running.
#[test]
fn d154_an_energy_at_ahead_of_the_clock_is_no_witness() {
    let tm = running_t4();
    tm.ok_at(&at("10:12"), &["energy", "3", "--at", "18:00"]);
    begins_a_running_break(&tm, "10:15", "5m");
}

/// **Nor is a far-future line** (D154, D18): a `plan` line dated 2027-01-01 by hand. On 213e827: logged finished.
#[test]
fn d154_a_far_future_line_is_no_witness() {
    let tm = running_t4();
    let path = tm.plan.join(".tm/log.jsonl");
    let mut text = fs::read_to_string(&path).expect("the log");
    text.push_str("{\"t\":\"2027-01-01T09:00:00-06:00\",\"ev\":\"plan\",\"hash\":\"x\",\"dropped\":[]}\n");
    fs::write(&path, text).expect("the log");
    begins_a_running_break(&tm, "10:15", "5m");
}

/// **An undone line and its `undo` witness it** (D154): pause and unpause at 10:50, both undone at 10:51, `--now 10:15 5m`
/// and `--now 10:40 5m` both logged finished, `stop` at 11:10 writes `10m` left. On 213e827 the second began a running
/// break and `stop` wrote `25m`.
#[test]
fn d154_undone_lines_witness_the_instant() {
    let tm = running_t4();
    tm.ok_at(&at("10:50"), &["pause"]);
    tm.ok_at(&at("10:50"), &["pause"]);
    tm.ok_at(&at("10:51"), &["undo"]);
    tm.ok_at(&at("10:51"), &["undo"]);
    for hm in ["10:15", "10:40"] {
        let out = tm.ok_at(&at(hm), &["break", "5m"]);
        assert!(out.stdout.contains("logged finished (it lies inside ^t4, which is running"), "{hm}: {}{}", out.stdout, out.stderr);
    }
    let out = tm.ok_at(&at("11:10"), &["stop"]);
    assert!(out.stdout.contains("after 50m · 10m left"), "{}{}", out.stdout, out.stderr);
    assert!(tm.line(WEEK, "t4").contains(" 10m "), "{}", tm.line(WEEK, "t4"));
}

/// **What witnesses it, and what does not** (README gaps 6031 and 5998 restated): a plain `tm energy` and a `tm wake` are no
/// witness (the log cannot say which were typed with a stated instant); a later verb helps only if it logs a line stamped
/// past the typed end — a `tm plan` does; `tm now` at 10:55 logs nothing, so it does not.
#[test]
fn d154_which_later_verbs_witness_the_typed_end() {
    let tm = running_t4();
    tm.ok_at(&at("10:50"), &["energy", "3"]);
    begins_a_running_break(&tm, "10:20", "10m");

    let tm = running_t4();
    tm.ok_at(&at("10:55"), &["now"]);
    begins_a_running_break(&tm, "10:20", "10m");

    let tm = running_t4();
    tm.ok_at(&at("10:50"), &["plan"]);
    let out = tm.ok_at(&at("10:20"), &["break", "10m"]);
    assert!(out.stdout.contains("logged finished"), "{}{}", out.stdout, out.stderr);
}

/// **Gap 5998's later verb, on a day with a wall** (Monday 2026-09-07's `^g1`, 12:50–13:50; D61): `tm now` at 14:10 writes
/// the marks at 12:50 and 13:50. They are the log's stamps, so they witness a typed end at or before 13:50 — and no later one,
/// though the verb ran at 14:10: `--now 13:55 10m` (typed end 14:05) begins a running break.
#[test]
fn d154_d61s_marks_witness_their_own_stamps_and_no_later() {
    let mon = |hm: &str| format!("2026-09-07T{hm}:00-05:00");
    let tree = || {
        let tm = Tm::empty();
        tm.ok_at(&mon("06:00"), &["init", "--example"]);
        tm.ok_at(&mon("07:00"), &["wake", "07:00"]);
        tm.ok_at(&mon("08:00"), &["arrive", "home"]);
        tm.ok_at(&mon("10:10"), &["start", "^t4"]);
        tm.ok_at(&mon("14:10"), &["now"]);
        assert_eq!(tm.last()["ev"], "unpause");
        tm
    };
    let tm = tree();
    let out = tm.ok_at(&mon("10:20"), &["break", "10m"]);
    assert!(out.stdout.contains("logged finished"), "{}{}", out.stdout, out.stderr);
    let tm = tree();
    let out = tm.ok_at(&mon("13:55"), &["break", "10m"]);
    assert!(!out.stdout.contains("logged finished"), "{}{}", out.stdout, out.stderr);
    assert_eq!(tm.last()["ev"], "break_start");
}
