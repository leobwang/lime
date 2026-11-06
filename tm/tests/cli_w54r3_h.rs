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
/// 213e827: review 98, plan 88, `tm check` "no problems"; on ba525fa refused. **Since README gap 6062 the verb refuses the fourth
/// keystroke** (a length with the break's own stamp and planned minutes is that break's own line, not "logged finished"), so the shape
/// reaches the kernel as a line from elsewhere; and with the keystroke refused the day reads 98 on all three.
#[test]
fn a_reads_88_on_the_review_the_plan_and_a_cold_rebuild() {
    let tm = j_day(&[("09:20", "30m"), ("09:30", ""), ("09:40", "15m")]);
    reads(&tm, 95);
    let s = refused_with(&tm, "09:20", &["break", "30m"]);
    assert!(s.contains("09:20–09:30") && s.contains("from this very instant"), "{s}");
    let refused_day = copied(&tm);
    assert!(retimes(&refused_day, "09:52", "09:40").contains("re-timed to end at 09:52 (D147)"));
    reads(&refused_day, 98);
    let mut log = fs::read_to_string(tm.plan.join(".tm/log.jsonl")).expect("the log");
    log.push_str(&format!("{{\"t\":\"{}\",\"ev\":\"break\",\"planned_min\":30,\"actual_min\":30}}\n", at("09:20")));
    fs::write(tm.plan.join(".tm/log.jsonl"), log).expect("the log");
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
/// what is in the way. The refusal's `tm undo` is driven, one line at a time: undoing the 09:33 line re-opens the 09:30 break,
/// D129 to 10:10, so 09:50 lies inside it and D141 ends THAT break there (review 100), not D150; undoing the 09:30 line too
/// takes the break in the way off the log, and only then does D150 re-time the 09:40 one out (review 110).
#[test]
fn past_a_frozen_breaks_end_inside_its_widest_end_is_refused() {
    let tm = j_day(&[("09:40", "15m"), ("09:45", ""), ("09:30", ""), ("09:33", "")]);
    reads(&tm, 112);
    let said = refused(&tm, "09:50");
    assert!(said.contains("lies past the end of the break 09:40–09:45, inside the 09:55 its own lines gave it"), "{said}");
    assert!(said.contains("the break 09:30–09:33, logged after it") && said.contains("(D150)") && said.contains("`tm undo`"), "{said}");
    reads(&tm, 112);

    tm.ok_at(&at("12:00"), &["undo"]);
    let one = copied(&tm);
    let out = one.ok_at(&at("09:50"), &["break"]);
    assert!(out.stderr.contains("the break that began at 09:30 ends here, at 09:50") && !out.stdout.contains("re-timed"), "{}{}", out.stdout, out.stderr);
    reads(&one, 100);

    tm.ok_at(&at("12:00"), &["undo"]);
    let out = tm.ok_at(&at("09:50"), &["break"]);
    assert!(out.stdout.contains("break 09:40–09:45 re-timed out to end at 09:50 (D150)"), "{}{}", out.stdout, out.stderr);
    reads(&tm, 110);
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

/// **A length with nothing at stake begins a running break, inside a held span too** (README gap 6044: the invariant's fourth
/// clause, read literally, refuses this, and three rows that predate it pin it — `cli_d144_now_break.rs`'s gap 5775,
/// `cli_w54_h_breaks.rs`'s F3, `cli_week_grid.rs`'s union; so the behaviour stands and the shape goes to the owner). No block is
/// open at the instant and no typed-time line lies at or past it, so no block's minutes can go: the break runs, drawn after the
/// held one, the review and the plan agree. Gaps 6050's rows are where a block IS at stake.
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
    text.push_str("{\"t\":\"2027-01-01T09:00:00-06:00\",\"ev\":\"plan\",\"hash\":\"6e147b39012b85f2\",\"replans_today\":0,\"drift_min\":0}\n");
    fs::write(&path, text).expect("the log");
    begins_a_running_break(&tm, "10:15", "5m");
    // The line is READ, as a far-future line: until the attackers' re-drive this row wrote a line the reader refuses
    // (`missing field replans_today`), which passed on 213e827 too (README gap 6054).
    let check = tm.run_at(&at("10:16"), &["check"]);
    assert!(check.stdout.contains("warning[log-future]") && !check.stdout.contains("warning[log-line]"), "{}{}", check.stdout, check.stderr);
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

// ---------------------------------------------------------------------------------------------------------------
// The attackers' five (README gaps 6050-6054)

/// The R day: `^t1` 09:00–10:00 done, `^t4` started 10:10 and running, then each break typed.
fn r_day(breaks: &[(&str, &str)]) -> Tm {
    let tm = fresh();
    tm.ok_at(&at("09:00"), &["start", "^t1"]);
    tm.ok_at(&at("10:00"), &["done"]);
    tm.ok_at(&at("10:10"), &["start", "^t4"]);
    typed(&tm, breaks);
    tm
}

fn no_break_start_at(tm: &Tm, hm: &str) {
    let t = at(hm);
    let bad = tm.log().into_iter().find(|l| l["ev"] == "break_start" && l["t"] == t.as_str());
    assert!(bad.is_none(), "a `break_start` at {hm}: {bad:?}");
}

/// **R: a length inside a closed span, the block still running, is a break already over** (README gap 6050; clause 4). The break
/// 10:15–10:40 the user ended is the log's own witness that 10:25 is past, and `latestTyped` cannot see it (a `break` line
/// counts at its start stamp). Until this row: `break_start` at 10:20, `tm now` at 12:30 `5m of 60m · paused`, `on break since
/// 10:20 · 110m of 5m`, `tm stop` `after 5m`: the 110 minutes after the user ended the break gone from the block.
#[test]
fn r_a_length_ending_inside_the_held_span_is_logged_finished_and_the_block_keeps_running() {
    let tm = r_day(&[("10:15", ""), ("10:40", "")]);
    let out = tm.ok_at(&at("10:20"), &["break", "5m"]);
    assert!(out.stdout.contains("logged finished (it lies inside the break 10:15–10:40 the log holds)"), "{}{}", out.stdout, out.stderr);
    no_break_start_at(&tm, "10:20");
    let last = tm.last();
    assert_eq!((last["ev"].as_str(), last["actual_min"].as_u64()), (Some("break"), Some(5)), "{last}");
    let now = copied(&tm).ok_at(&at("12:30"), &["now"]).stdout;
    assert!(now.contains("115m of 60m") && !now.contains("paused") && !now.contains("on break since"), "{now}");
    let c = copied(&tm);
    fs::remove_file(c.plan.join(".tm/state.json")).expect("the cache");
    let _ = fs::remove_dir_all(c.plan.join(".tm/cache"));
    let cold_now = c.ok_at(&at("12:30"), &["now"]).stdout;
    assert!(cold_now.contains("115m of 60m") && !cold_now.contains("on break since"), "{cold_now}");
    let stop = tm.ok_at(&at("12:30"), &["stop"]);
    assert!(stop.stdout.contains("stopped ^t4 after 115m"), "{}{}", stop.stdout, stop.stderr);
}

/// **R, a length past the span: refused by name, and the advice is driven** (README gap 6050). `10:20 30m` ends at 10:50, past
/// the break and past the log's latest stamp, so nothing says it is over, and a break begun there would lose every minute after
/// 10:40. The refusal offers a length that ends by 10:40, and that length does log finished.
#[test]
fn r_a_length_past_the_held_span_is_refused_and_its_advice_works() {
    let tm = r_day(&[("10:15", ""), ("10:40", "")]);
    let said = refused_with(&tm, "10:20", &["break", "30m"]);
    assert!(said.contains("10:15–10:40") && said.contains("10:50") && said.contains("by 10:40"), "{said}");
    let out = tm.ok_at(&at("10:20"), &["break", "20m"]);
    assert!(out.stdout.contains("10:20–10:40 · logged finished"), "{}{}", out.stdout, out.stderr);
    no_break_start_at(&tm, "10:20");
}

/// **R, a length at the break's own start with its planned minutes: the kernel reads it as that break's line** (README gap 6050).
/// So it is refused, not said as a finished break "that nets nothing" while the break moved under it; both ways out are driven.
#[test]
fn r_a_length_with_the_breaks_own_start_and_planned_minutes_is_refused() {
    let tm = r_day(&[("10:15", ""), ("10:40", "")]);
    let said = refused_with(&tm, "10:15", &["break", "20m"]);
    assert!(said.contains("10:15–10:40") && said.contains("typed from 10:16 to 10:39 re-times it (D147)") && said.contains("at most 25m, not 20m"), "{said}");
    let other = copied(&tm).ok_at(&at("10:15"), &["break", "5m"]);
    assert!(other.stdout.contains("10:15–10:20 · logged finished"), "{}{}", other.stdout, other.stderr);
    assert!(copied(&tm).ok_at(&at("10:35"), &["break"]).stdout.contains("re-timed to end at 10:35"));
}

/// **J: a length inside a closed span over a closed block** (README gap 6050). `10:30 90m` netted `^t4` from 10:30, so
/// `10:35 5m` nets nothing further and `netted_closed_block` cannot see the block. The `done` at 11:10 has passed 10:40: logged
/// finished, drawn inside the break. Until this row: `break_start` at 10:35, `tm now` reading `on break since 10:35`.
#[test]
fn j_a_length_inside_a_span_over_a_closed_block_is_logged_finished() {
    let tm = j_day(&[("10:30", "90m")]);
    reads(&tm, 80);
    let out = tm.ok_at(&at("10:35"), &["break", "5m"]);
    assert!(out.stdout.contains("10:35–10:40 · logged finished (it lies inside the break 10:30–12:00"), "{}{}", out.stdout, out.stderr);
    no_break_start_at(&tm, "10:35");
    let now = copied(&tm).ok_at(&at("12:30"), &["now"]).stdout;
    assert!(!now.contains("on break since"), "{now}");
    reads(&tm, 80);
}

/// **J, a length past the span and past the log: refused, and the advice is driven** (README gap 6050).
#[test]
fn j_a_length_past_the_span_over_a_closed_block_is_refused_and_its_advice_works() {
    let tm = j_day(&[("10:30", "90m")]);
    let said = refused_with(&tm, "10:35", &["break", "90m"]);
    assert!(said.contains("10:30–12:00") && said.contains("12:05") && said.contains("by 12:00"), "{said}");
    let out = tm.ok_at(&at("10:35"), &["break", "85m"]);
    assert!(out.stdout.contains("logged finished"), "{}{}", out.stdout, out.stderr);
    no_break_start_at(&tm, "10:35");
    reads(&tm, 80);
}

/// **A D129 ending's own start, unlisted: a length is refused, never swallowed** (README gap 6051). `09:42` (D129 to 10:10),
/// `09:25 30m`: the newer break overlaps it, so `ended_breaks` omits it and P139's guard does not fire. The kernel takes a
/// `break` line at that stamp as P127's own line and keeps D129's span. Until this row: `break 60m · 09:42–10:42 · logged
/// finished (… whose block it nets, D148)`, review 85 before and after, the length gone.
#[test]
fn a_length_at_an_unlisted_d129_endings_start_is_refused_never_swallowed() {
    let tm = j_day(&[("09:42", ""), ("09:25", "30m")]);
    reads(&tm, 85);
    for len in ["60m", "30m", "5m"] {
        let said = refused_with(&tm, "09:42", &["break", len]);
        assert!(said.contains("09:42–10:10") && said.contains("own line") && said.contains("another instant"), "{len}: {said}");
    }
    reads(&tm, 85);
    // The refusal's advice: another instant logs a finished break of its own.
    let out = tm.ok_at(&at("09:43"), &["break", "5m"]);
    assert!(out.stdout.contains("09:43–09:48 · logged finished (a later start follows it, D143)"), "{}{}", out.stdout, out.stderr);
    assert_eq!(tm.last()["t"], at("09:43").as_str());
    reads(&tm, 85);
}

/// **The no-length refusal there does not offer the length a line cannot carry** (README gap 6051). Following the old advice
/// literally logged `09:42–09:47` while the kernel kept 09:42–10:10; re-timing the outer break then drew `09:42 break 28m`.
#[test]
fn the_refusal_at_an_unlisted_d129_endings_start_does_not_offer_a_length() {
    let tm = j_day(&[("09:42", ""), ("09:25", "30m")]);
    let said = refused(&tm, "09:42");
    assert!(said.contains("09:25–09:55 (inside it)") && said.contains("09:42–10:10 (its start)"), "{said}");
    assert!(!said.contains("type a length"), "{said}");
    assert!(said.contains("`tm undo`"), "{said}");
    // Inside both, the advice stands, and it is true: a length there logs a finished break of its own.
    let said = refused(&tm, "09:45");
    assert!(said.contains("type a length to log a finished break beside it (D143)"), "{said}");
    let out = tm.ok_at(&at("09:45"), &["break", "5m"]);
    assert!(out.stdout.contains("09:45–09:50 · logged finished (a later start follows it, D143)"), "{}{}", out.stdout, out.stderr);
    reads(&tm, 85);
}

/// **D141's arm keeps the one-instant rule** (README gap 6052). `09:40` and `09:30` both run to 10:10 (D129); 09:45 lies in both.
/// Until this row the verb said `the break that began at 09:30 ends here` and no minute came back: review 90 before and after,
/// 09:30–09:45 and 09:45–10:10 drawn. It is refused as the finished arm refuses it, and a length logs a break of its own.
#[test]
fn d141_is_refused_at_an_instant_another_break_also_holds() {
    for setup in [[("09:40", ""), ("09:30", "")], [("09:40", "30m"), ("09:30", "")]] {
        let tm = j_day(&setup);
        reads(&tm, 90);
        let said = refused(&tm, "09:45");
        assert!(said.contains("meets more than one logged break") && said.contains("09:30–10:10") && said.contains("09:40–10:10"), "{said}");
        assert!(said.contains("type a length to log a finished break beside it (D143)"), "{said}");
        reads(&tm, 90);
        let n = tm.log().len();
        let out = tm.ok_at(&at("09:45"), &["break", "5m"]);
        assert!(out.stdout.contains("09:45–09:50 · logged finished (a later start follows it, D143)"), "{}{}", out.stdout, out.stderr);
        assert_eq!(tm.log().len(), n + 1, "one line, no D141 end beside it");
        reads(&tm, 90);
    }
}

/// **D141 still ends a break alone holding the instant** (README gap 6052).
#[test]
fn d141_still_ends_a_break_no_other_span_holds() {
    let tm = j_day(&[("09:30", "")]);
    reads(&tm, 90);
    let out = tm.ok_at(&at("09:45"), &["break"]);
    assert!(out.stderr.contains("ends here, at 09:45") && !out.stderr.contains("also holds"), "{}{}", out.stdout, out.stderr);
    reads(&tm, 105);
}

/// **A D141 end that does give minutes back stands, and the reply says what still holds the instant** (README gap 6052): a shorter
/// break nested inside (`09:40 5m`), the outer D129 to 10:10, `--now 09:42`: 09:45–10:10 comes back, 09:40–09:45 stays drawn.
#[test]
fn d141_that_moves_with_another_span_holding_says_so() {
    let tm = j_day(&[("09:40", "5m"), ("09:30", "")]);
    reads(&tm, 90);
    let out = tm.ok_at(&at("09:42"), &["break"]);
    assert!(out.stderr.contains("ends here, at 09:42") && out.stderr.contains("the logged break 09:40–09:45 also holds this instant"), "{}{}", out.stdout, out.stderr);
    reads(&tm, 105);
}

/// **Under a minute past the start of a break D129 ended: at its start, as P139 refuses** (README gap 6056; `at_finished`'s rule
/// for a logged break). D141's arm wrote `actual_min: 0` for `09:20`, then `--now 09:20:30`: the break gone (review 120), under a
/// reply that said it ended here at 09:20. With a length, D146 lost it the same way. A whole minute past the start still ends it.
#[test]
fn under_a_minute_past_a_d129_breaks_start_is_refused_as_at_its_start() {
    let tm = j_day(&[("09:20", "")]);
    reads(&tm, 80);
    let exactly = refused(&tm, "09:20");
    assert!(exactly.contains("(D129)") && exactly.contains("give an instant from 09:21 to 10:09"), "{exactly}");
    assert_eq!(refused(&tm, "09:20:30"), exactly);
    assert_eq!(refused_with(&tm, "09:20:30", &["break", "5m"]), exactly);
    reads(&tm, 80);
    let out = tm.ok_at(&at("09:21"), &["break"]);
    assert!(out.stderr.contains("ends here, at 09:21"), "{}{}", out.stdout, out.stderr);
    reads(&tm, 119);
}

/// **A break too short to hold an instant a line could end it at is not told to give one** (README gap 6056). A line carries
/// whole minutes from the start: under a minute past the start is at the start, under a minute before the end is at the end, so
/// a logged break under two minutes has no instant that re-times it. `09:20 1m`, then `09:20` or `09:20:30`: the advice is
/// `tm undo` or a length, both driven. Two minutes do have one: `--now 09:21` moves it. The same for a D129 ending one minute long.
#[test]
fn a_break_too_short_for_a_line_is_given_advice_that_works() {
    let tm = j_day(&[("09:20", "1m")]);
    reads(&tm, 119);
    let said = refused(&tm, "09:20");
    assert!(!said.contains("give an instant inside it") && said.contains("no instant inside it"), "{said}");
    assert!(said.contains("type a length") && said.contains("`tm undo`"), "{said}");
    assert!(refused(&tm, "09:20:30").contains("no instant inside it"));
    let length = copied(&tm);
    let out = length.ok_at(&at("09:20"), &["break", "5m"]);
    assert!(out.stdout.contains("09:20–09:25 · logged finished"), "{}{}", out.stdout, out.stderr);
    reads(&length, 115);
    tm.ok_at(&at("09:21"), &["undo"]);
    reads(&tm, 120);

    // Past the blocks, the break's own stamp is the log's latest: at 11:20:30 a length would begin a running break, so it is not
    // offered and `tm undo` is what there is; at 11:20 the log has reached the instant, and the length it offers logs finished.
    let tm = j_day(&[("11:20", ""), ("11:21", "")]);
    let said = refused(&tm, "11:20:30");
    assert!(said.contains("no instant inside it") && !said.contains("type a length") && said.contains("`tm undo`"), "{said}");
    let said = refused(&tm, "11:20");
    assert!(said.contains("no instant inside it") && said.contains("type a length that ends by 11:21"), "{said}");
    let out = tm.ok_at(&at("11:20"), &["break", "1m"]);
    assert!(out.stdout.contains("11:20–11:21 · logged finished"), "{}{}", out.stdout, out.stderr);
    assert!(!copied(&tm).ok_at(&at("12:00"), &["now"]).stdout.contains("on break since"));

    // Two minutes hold one, and the advice stands.
    let tm = j_day(&[("09:20", "2m")]);
    let said = refused(&tm, "09:20");
    assert!(said.contains("give an instant at 09:21"), "{said}");
    assert!(tm.ok_at(&at("09:21"), &["break"]).stdout.contains("re-timed to end at 09:21 (D147) · 1m of 2m"));
    reads(&tm, 119);

    // A D129 ending a minute long: no later instant before its end is a whole minute past its start.
    let tm = j_day(&[("10:09", "")]);
    let said = refused(&tm, "10:09");
    assert!(!said.contains("give a later instant") && said.contains("no instant before 10:10") && said.contains("`tm undo`"), "{said}");
    assert_eq!(refused(&tm, "10:09:30"), said);
    tm.ok_at(&at("11:30"), &["undo"]);
    reads(&tm, 120);
    let v = copied(&tm).json_at(&at("12:30"), &["review", "day"]);
    assert_eq!(v["review"]["breaks"]["breaks"].as_array().map(Vec::len), Some(0), "the break is gone: {v}");
}

/// **Under a minute before a break's end: it already ends there** (README gap 6053). A break has seconds on both ends: typing the
/// displayed end used to say `break 11:30–11:40 re-timed to end at 11:40 · 9m of 20m` and write `actual_min: 9`, a minute lost
/// under a reply whose old span and new end read the same.
#[test]
fn under_a_minute_before_a_breaks_end_it_already_ends_there() {
    let tm = j_day(&[("11:30:30", ""), ("11:40:45", "")]);
    let n = tm.log().len();
    let out = tm.ok_at(&at("11:40"), &["break"]);
    assert!(out.stdout.contains("break 11:30–11:40 already ends at 11:40"), "{}{}", out.stdout, out.stderr);
    assert_eq!(tm.log().len(), n, "nothing written");

    let tm = j_day(&[("09:20:30", "10m")]);
    let n = tm.log().len();
    let r = review(&tm);
    let out = tm.ok_at(&at("09:30"), &["break"]);
    assert!(out.stdout.contains("break 09:20–09:30 already ends at 09:30"), "{}{}", out.stdout, out.stderr);
    assert_eq!(tm.log().len(), n, "nothing written");
    assert_eq!(review(&tm), r);
}

/// **"re-timed" says the end its line gives** (README gap 6053): a line carries whole minutes from the break's start, so
/// `--now 09:25` in a break begun 09:20:30 gives 09:24:30, and the plan draws 09:24.
#[test]
fn the_reply_prints_the_end_the_line_gives() {
    let tm = j_day(&[("09:20:30", "10m")]);
    let out = tm.ok_at(&at("09:25"), &["break"]);
    assert!(out.stdout.contains("re-timed to end at 09:24 (D147) · 4m of 10m"), "{}{}", out.stdout, out.stderr);
    assert_eq!((review(&tm), cold(&tm).0), (115, 115), "20m to 09:20:30, 35m from 09:24:30, ^t4's 60m");
}

/// **D141 says the end its line gives, too** (README gap 6053).
#[test]
fn the_d141_reply_prints_the_end_the_line_gives() {
    let tm = j_day(&[("09:30:30", "")]);
    let out = tm.ok_at(&at("09:45"), &["break"]);
    assert!(out.stderr.contains("ends here, at 09:44"), "{}{}", out.stdout, out.stderr);
}

// ---- The last host round (README §10): replies that say what fired. ----

/// `tm break --now <hm> <args>`, its stdout and stderr together.
fn said(tm: &Tm, hm: &str, args: &[&str]) -> String {
    let out = tm.ok_at(&at(hm), args);
    format!("{}{}", out.stdout, out.stderr)
}

/// **"The log has passed" only when its latest typed-time stamp has reached the typed end** (README gap 6060). `11:05 60m`, `^t4`
/// stopped at 11:10: `11:08 5m` ends at 11:13, inside the span, and no stamp has reached it. Until this row every such reply said
/// the log had passed its end.
#[test]
fn a_reply_says_the_log_has_passed_only_when_it_has() {
    let tm = fresh();
    tm.ok_at(&at("09:00"), &["start", "^t1"]);
    tm.ok_at(&at("10:00"), &["done"]);
    tm.ok_at(&at("10:10"), &["start", "^t4"]);
    tm.ok_at(&at("11:10"), &["stop"]);
    tm.ok_at(&at("11:05"), &["break", "60m"]);
    let s = said(&tm, "11:08", &["break", "5m"]);
    assert!(s.contains("(it lies inside the break 11:05–12:05 the log holds)") && !s.contains("passed"), "{s}");
    let tm = j_day(&[("11:30", ""), ("11:40", "")]);
    tm.ok_at(&at("11:33"), &["plan"]);
    let s = said(&tm, "11:32", &["break", "5m"]);
    assert!(s.contains("(it lies inside the break 11:30–11:40 the log holds)") && !s.contains("passed"), "{s}");
    let tm = j_day(&[("11:09", "20m")]);
    let s = said(&tm, "11:09", &["break", "19m", "--where", "bed"]);
    assert!(s.contains("(it lies inside the break 11:09–11:29 the log holds)") && !s.contains("passed"), "{s}");
    // Where a stamp has reached it, the reply still says so: the `done` at 11:10 against 10:40.
    let tm = j_day(&[("10:30", "90m")]);
    let s = said(&tm, "10:35", &["break", "5m"]);
    assert!(s.contains("(it lies inside the break 10:30–12:00 the log holds, and the log has passed its end)"), "{s}");
}

/// **A length past the named span says so, and what it adds** (README gap 6060). `11:35 15m` ends at 11:50, ten minutes past the
/// 11:30–11:40 it begins inside: review 10 to 20. Until this row: "it lies inside the break 11:30–11:40", and no word of the ten.
#[test]
fn a_length_past_the_named_span_says_what_it_adds() {
    let day = || {
        let tm = j_day(&[("11:30", ""), ("11:40", "")]);
        tm.ok_at(&at("12:00"), &["plan"]);
        tm
    };
    let tm = day();
    let s = said(&tm, "11:35", &["break", "15m"]);
    assert!(s.contains("it begins inside the break 11:30–11:40 the log holds and runs past its end, adding 10m; the log has passed 11:50"), "{s}");
    let v = copied(&tm).json_at(&at("12:30"), &["review", "day"]);
    assert_eq!(v["review"]["breaks"]["actual_min"].as_u64(), Some(20), "{v}");
    let v = day().json_at(&at("11:35"), &["break", "15m"]);
    assert_eq!((v["finished"]["inside_break"].as_str(), v["finished"]["adds_min"].as_u64()), (Some("11:30–11:40"), Some(10)), "{v}");
    // Read off the day and not off the arithmetic: what another logged break already covers it does not add.
    let tm = day();
    tm.ok_at(&at("11:35"), &["break", "15m"]);
    let s = said(&tm, "11:32", &["break", "15m"]);
    assert!(s.contains("it begins inside the break 11:30–11:40") && s.contains("adding 0m"), "{s}");
}

/// **D152 is cited only when D152 fired** (README gap 6060). `^t4` running, `10:15`, `10:40`, `10:20 5m`: gap 6050's rule logged it, no
/// stamp has reached 10:25. Until this row the JSON carried `inside_running` beside `inside_break`, and the reply cited D152.
#[test]
fn d152_is_cited_only_when_it_fired() {
    let tm = r_day(&[("10:15", ""), ("10:40", "")]);
    let s = said(&tm, "10:20", &["break", "5m"]);
    assert!(!s.contains("D152") && !s.contains("^t4"), "{s}");
    let tm = r_day(&[("10:15", ""), ("10:40", "")]);
    let v = tm.json_at(&at("10:20"), &["break", "5m"]);
    let f = &v["finished"];
    assert_eq!((f["inside_break"].as_str(), f.get("inside_running"), f.get("nets")), (Some("10:15–10:40"), None, None), "{v}");
    // Where it did fire, it stays: a pause's stamp has passed 10:25, and the break lies inside ^t4.
    let tm = r_day(&[]);
    tm.ok_at(&at("10:50"), &["pause"]);
    tm.ok_at(&at("10:50"), &["pause"]);
    let s = said(&tm, "10:20", &["break", "5m"]);
    assert!(s.contains("it lies inside ^t4, which is running; it nets it, D152"), "{s}");
}

/// **The cost sentence, only when a block is open past the span** (README gap 6060). `^t4` closed at 11:10 with `10:20 50m`
/// holding the rest: no minute is left to take. Until this row: "would take every minute after 11:10 (D152)".
#[test]
fn a_past_refusal_states_a_cost_only_when_there_are_minutes_to_take() {
    let tm = j_day(&[("10:20", "50m")]);
    let s = refused_with(&tm, "10:25", &["break", "50m"]);
    assert!(!s.contains("every minute") && !s.contains("D152") && s.contains("run on from inside that break"), "{s}");
    let tm = r_day(&[("10:15", ""), ("10:40", "")]);
    let s = refused_with(&tm, "10:20", &["break", "30m"]);
    assert!(s.contains("would take every minute of ^t4 after 10:40") && !s.contains("D152"), "{s}");
}

/// **"Also holds" reads the half-open rule** (README gap 6060). At 09:50 the 09:45–09:50 break ends; it holds no instant there, and the
/// plan draws nothing of its own. At 09:47 it does hold it, and the sentence stands.
#[test]
fn also_holds_is_not_said_at_that_breaks_own_end() {
    let tm = j_day(&[("09:45", "5m"), ("09:40", "")]);
    let s = said(&tm, "09:50", &["break"]);
    assert!(s.contains("ends here, at 09:50") && !s.contains("also holds"), "{s}");
    let tm = j_day(&[("09:45", "5m"), ("09:40", "")]);
    let s = said(&tm, "09:47", &["break"]);
    assert!(s.contains("the logged break 09:45–09:50 also holds this instant, and stays"), "{s}");
}

/// **Under a minute past a D129 ending's start reads only inside its span** (README gap 6061). `10:09:30`, ended at 10:10 by `^t4`'s
/// `start`, is thirty seconds long. Until this row `10:10`, `10:10:15` and `10:10:15 5m` were each refused as "at its own start",
/// though the first is its end and the others lie outside it: at its end it already ends, and outside it a break begins.
#[test]
fn the_under_a_minute_rule_stops_at_a_short_d129_breaks_end() {
    let day = || j_day(&[("10:09:30", "")]);
    let tm = day();
    let n0 = tm.log().len();
    let s = said(&tm, "10:10", &["break"]);
    assert!(s.contains("already ends at 10:10 — nothing written"), "{s}");
    assert_eq!(tm.log().len(), n0, "nothing written");
    let tm = day();
    let t = at("10:10:15");
    tm.ok_at(&t, &["break"]);
    let last = tm.last();
    assert_eq!((last["ev"].as_str(), last["t"].as_str()), (Some("break_start"), Some(t.as_str())), "{last}");
    let tm = day();
    let s = said(&tm, "10:10:15", &["break", "5m"]);
    assert!(s.contains("logged finished"), "{s}");
    // Inside it, the rule stands.
    let s = refused_with(&day(), "10:09:50", &["break"]);
    assert!(s.contains("own start"), "{s}");
}

/// `tm review day`'s break records at 12:30, on a copy: `(planned, actual, place)`, and the place table.
fn break_records(tm: &Tm) -> (Vec<(u64, u64, Option<String>)>, serde_json::Value) {
    let v = copied(tm).json_at(&at("12:30"), &["review", "day"]);
    let rows = v["review"]["breaks"]["breaks"].as_array().unwrap_or_else(|| panic!("{v}"));
    let rows = rows
        .iter()
        .map(|b| (b["planned_min"].as_u64().expect("planned"), b["actual_min"].as_u64().expect("actual"), b["place"].as_str().map(str::to_string)))
        .collect();
    (rows, v["review"]["breaks"]["by_where"].clone())
}

/// **One question: is the line read as a break of its own?** (README gap 6062). A length landing exactly on a D129 ending's own end
/// passed the old check, for a held break already ended there: `09:42 28m --where walk` said "logged finished", place walk, and the
/// kernel kept D129's span and dropped both. Refused now, by name. A stamp a minute on is a break of its own.
#[test]
fn a_length_landing_on_a_d129_endings_own_end_is_refused() {
    let tm = j_day(&[("09:42", ""), ("09:25", "30m")]);
    let s = refused_with(&tm, "09:42", &["break", "28m", "--where", "walk"]);
    assert!(s.contains("09:42–10:10") && s.contains("own line"), "{s}");
    let tm = j_day(&[("09:40", ""), ("09:30", "")]);
    let s = refused_with(&tm, "09:40", &["break", "30m", "--where", "walk"]);
    assert!(s.contains("09:40–10:10") && s.contains("own line"), "{s}");
    let tm = j_day(&[("09:42", ""), ("09:25", "30m")]);
    let s = said(&tm, "09:43", &["break", "27m", "--where", "walk"]);
    assert!(s.contains("09:43–10:10 · logged finished"), "{s}");
    let (rows, _) = break_records(&tm);
    assert!(rows.iter().any(|r| r.0 == 27 && r.2.as_deref() == Some("walk")), "{rows:?}");
}

/// **The own-stamp guard covers every arm that logs a length finished** (README gap 6062). Each of these is D149, D143 or D152: the
/// kernel reads the line as the held break's own, so the reply said "logged finished" while the break fell, the block's minutes came
/// back, or its place went. One guard now, and the review stands.
#[test]
fn a_length_with_a_held_breaks_stamp_and_planned_minutes_is_refused_in_every_arm() {
    // D149: `10:15` (ended at 11:09), its planned 20m at its own stamp.
    let tm = j_day(&[("10:15", ""), ("11:09", "")]);
    let s = refused_with(&tm, "10:15", &["break", "20m", "--where", "bed"]);
    assert!(s.contains("10:15–11:09") && s.contains("from this very instant"), "{s}");
    // D143: `09:20` ended at 09:50, with `^t4`'s `start` after it.
    let tm = j_day(&[("09:20", ""), ("09:50", "")]);
    let s = refused_with(&tm, "09:20", &["break", "20m"]);
    assert!(s.contains("09:20–09:50") && s.contains("from this very instant"), "{s}");
    // D152: `^t4` running, its pause's stamps past the typed end.
    let tm = r_day(&[]);
    tm.ok_at(&at("10:50"), &["pause"]);
    tm.ok_at(&at("10:50"), &["pause"]);
    typed(&tm, &[("10:15", ""), ("10:40", "")]);
    let s = refused_with(&tm, "10:15", &["break", "20m"]);
    assert!(s.contains("10:15–10:40") && s.contains("from this very instant"), "{s}");
    // The place alone: the second line's span and minutes are the first's, and it would erase `walk`.
    let tm = j_day(&[]);
    tm.ok_at(&at("09:50"), &["break", "30m", "--where", "walk"]);
    let s = refused_with(&tm, "09:50", &["break", "30m"]);
    assert!(s.contains("09:50–10:20") && s.contains("from this very instant"), "{s}");
    let (rows, _) = break_records(&tm);
    assert_eq!(rows, vec![(30, 30, Some("walk".to_string()))]);
}

/// **A D141 line that moves only a place is a line that moves** (README gap 6063). Two D129 endings to 10:10, `walk` and `bed`, and
/// `--now 09:45`: no drawn minute moves, but the review's `by_where` does. Until this row: refused "meets more than one logged break",
/// because the merged spans discarded each piece's place. With no place on either, it still moves nothing and stays refused.
#[test]
fn a_d141_line_that_moves_only_a_place_ends_the_break() {
    let tm = j_day(&[]);
    tm.ok_at(&at("09:40"), &["break", "--where", "walk"]);
    tm.ok_at(&at("09:30"), &["break", "--where", "bed"]);
    let s = said(&tm, "09:45", &["break"]);
    assert!(s.contains("the break that began at 09:30 ends here, at 09:45") && s.contains("09:40–10:10 also holds this instant"), "{s}");
    let (_, by) = break_records(&tm);
    assert_eq!((by["bed"].clone(), by["walk"].clone()), (serde_json::json!([1, 15]), serde_json::json!([1, 25])), "{by}");
    reads(&tm, 90);
    let tm = j_day(&[("09:40", ""), ("09:30", "")]);
    let s = refused(&tm, "09:45");
    assert!(s.contains("meets more than one logged break"), "{s}");
}

/// **One instant, one answer, a whole minute before the end** (README gap 6064). 09:30–10:10 logged finished and the same span by D129:
/// at 10:09:30 both now end at 10:09. Until this row the finished one "already ended at 10:10". And `09:29:01` in 09:20–09:30 is inside
/// by 59 seconds: until this row "already ends", a whole minute kept the instant did not ask for.
#[test]
fn an_instant_a_clock_minute_before_the_end_re_times_in_both_arms() {
    let tm = j_day(&[("09:30", "")]);
    let s = said(&tm, "10:09:30", &["break"]);
    assert!(s.contains("ends here, at 10:09"), "{s}");
    reads(&tm, 90);
    let tm = j_day(&[("09:30", "40m")]);
    let s = said(&tm, "10:09:30", &["break"]);
    assert!(s.contains("re-timed to end at 10:09 (D147)"), "{s}");
    reads(&tm, 90);
    let tm = j_day(&[("09:20", "10m")]);
    let s = said(&tm, "09:29:01", &["break"]);
    assert!(s.contains("re-timed to end at 09:29 (D147) · 9m of 10m"), "{s}");
    assert_eq!(review(&tm), 111);
}

/// **The clock's minute of the end is one answer in both arms** (README gaps 6053 and 6064): `^t4` started 10:10:30, so 09:30:30–10:10:30
/// by D129 and by a typed length read the same at `--now 10:10`: it already ends there, nothing written.
#[test]
fn the_clock_minute_of_the_end_already_ends_in_both_arms() {
    let day = || {
        let tm = fresh();
        tm.ok_at(&at("09:00"), &["start", "^t1"]);
        tm.ok_at(&at("10:00"), &["done"]);
        tm.ok_at(&at("10:10:30"), &["start", "^t4"]);
        tm.ok_at(&at("11:10"), &["done"]);
        tm
    };
    for len in [None, Some("40m")] {
        let tm = day();
        match len {
            Some(l) => tm.ok_at(&at("09:30:30"), &["break", l]),
            None => tm.ok_at(&at("09:30:30"), &["break"]),
        };
        let n = tm.log().len();
        let s = said(&tm, "10:10", &["break"]);
        assert!(s.contains("already ends at 10:10 — nothing written"), "{len:?}: {s}");
        assert_eq!(tm.log().len(), n, "nothing written");
    }
}

// ---- The last host round: advice that works when followed (README gap 6065). Each sentence's advice is driven in its row. ----

/// A finished line typed on a copy, its reply.
fn logs_finished(tm: &Tm, hm: &str, len: &str) -> String {
    let s = said(&copied(tm), hm, &["break", len]);
    assert!(s.contains("logged finished"), "{hm} {len}: {s}");
    s
}

/// **No whole minute fits: the refusal says so, to the second, and names the instant that works.** `10:39:30` is thirty seconds from
/// 10:40. Until this row: "ends at 10:40, which neither that break nor the log has reached … type a length that ends by 10:40", naming
/// one instant as both, with no length that fits. `0m` is never offered.
#[test]
fn a_past_refusal_where_no_length_fits_offers_none() {
    let tm = r_day(&[("10:15", ""), ("10:40", "")]);
    for (len, end) in [("5m", "10:44:30"), ("1m", "10:40:30")] {
        let s = refused_with(&tm, "10:39:30", &["break", len]);
        assert!(s.contains("at 10:39:30 lies inside the logged break 10:15–10:40") && s.contains(&format!("ends at {end},")), "{s}");
        assert!(s.contains("no whole-minute length") && s.contains("a length typed at 10:40 lies outside every logged break"), "{s}");
        assert!(!s.contains("type a length") && !s.contains("0m"), "{s}");
    }
    let followed = copied(&tm);
    let t = at("10:40");
    followed.ok_at(&t, &["break", "5m"]);
    let last = followed.last();
    assert_eq!((last["ev"].as_str(), last["t"].as_str()), (Some("break_start"), Some(t.as_str())), "outside every span: {last}");
}

/// **The length a refusal names is one that fits**, with seconds on the instant: `10:20:30` has nineteen whole minutes to 10:40.
#[test]
fn a_past_refusal_names_the_longest_length_that_fits() {
    let tm = r_day(&[("10:15", ""), ("10:40", "")]);
    let s = refused_with(&tm, "10:20:30", &["break", "20m"]);
    assert!(s.contains("ends at 10:40:30,") && s.contains("ends by 10:40, at most 19m"), "{s}");
    logs_finished(&tm, "10:20:30", "19m");
}

/// **Not the length the guard refuses.** At a held break's own start, the length ending exactly at the limit is that break's own line.
/// Until this row: "ends by 11:10", and `50m` refused "from this very instant".
#[test]
fn a_past_refusal_at_a_breaks_own_start_excludes_its_planned_minutes() {
    let tm = j_day(&[("10:20", "50m")]);
    let s = refused_with(&tm, "10:20", &["break", "60m"]);
    assert!(s.contains("ends by 11:10, at most 49m"), "{s}");
    logs_finished(&tm, "10:20", "49m");
    let refused_again = refused_with(&tm, "10:20", &["break", "50m"]);
    assert!(refused_again.contains("from this very instant"), "{refused_again}");
}

/// **`tm undo` is not offered where it brings the loss the refusal names, and is plain where it is offered.** Past: following "`tm undo`"
/// used to set the 10:15 break running again (`paused · on break since 10:15`) with a reply saying only that it undid a break. Many: the
/// sentence now says so, and two undos do it.
#[test]
fn the_undo_half_is_dropped_or_says_a_break_runs_again() {
    let tm = r_day(&[("10:15", ""), ("10:40", "")]);
    let s = refused_with(&tm, "10:20", &["break", "30m"]);
    assert!(!s.contains("tm undo"), "{s}");
    let tm = r_day(&[("10:15", ""), ("10:40", ""), ("10:20", "5m")]);
    let s = refused(&tm, "10:22");
    assert!(s.contains("`tm undo` takes the last line back, one line at a time (undoing the line that ended a running break sets it running again)"), "{s}");
    tm.ok_at(&at("10:23"), &["undo"]);
    tm.ok_at(&at("10:23"), &["undo"]);
    let now = tm.ok_at(&at("10:24"), &["now"]).stdout;
    assert!(now.contains("on break since 10:15"), "{now}");
}

/// **The own-stamp refusal names planned minutes as planned, and the instants and lengths that work** (11:30–11:40 is ten minutes, and
/// the 20m is its planned default). Until this row "`tm break` at the instant it should end re-times it": at 11:50 that began a second
/// running break, and every instant of a nested break was refused.
#[test]
fn the_own_stamp_refusal_names_what_works() {
    let tm = j_day(&[("11:30", ""), ("11:40", "")]);
    tm.ok_at(&at("12:00"), &["plan"]);
    let s = refused_with(&tm, "11:30", &["break", "20m"]);
    assert!(s.contains("a break planned 20m is logged 11:30–11:40"), "{s}");
    assert!(s.contains("typed from 11:31 to 11:39 re-times it (D147)") && s.contains("ends by 12:00, at most 30m, not 20m"), "{s}");
    for hm in ["11:31", "11:39"] {
        assert!(said(&copied(&tm), hm, &["break"]).contains("re-timed to end at"), "{hm}");
    }
    logs_finished(&tm, "11:30", "30m");
    logs_finished(&tm, "11:30", "19m");
    // Nested, so no instant of the inner break is its alone: no re-time offered, and the length is driven.
    let tm = r_day(&[("10:15", ""), ("10:40", ""), ("10:20", "5m")]);
    let s = refused_with(&tm, "10:20", &["break", "5m"]);
    assert!(!s.contains("re-times it") && s.contains("ends by 10:40, at most 20m, not 5m"), "{s}");
    logs_finished(&tm, "10:20", "20m");
    // Two at the stamp: neither's planned minutes, and no instant that names one.
    let tm = j_day(&[("11:09", "20m")]);
    tm.ok_at(&at("11:09"), &["break", "19m", "--where", "bed"]);
    let s = refused_with(&tm, "11:09", &["break", "20m"]);
    assert!(!s.contains("re-times it") && s.contains("ends by 11:29, at most 18m"), "{s}");
    logs_finished(&tm, "11:09", "18m");
}

/// **A break running: `tm break` ends that one, so no re-time is offered** (until this row it was, and the keystroke ended the running
/// break). The stopped day: `11:10 20m` runs, `11:00 40m` is logged beside it.
#[test]
fn the_own_stamp_refusal_offers_no_re_time_while_a_break_runs() {
    let tm = fresh();
    tm.ok_at(&at("09:00"), &["start", "^t1"]);
    tm.ok_at(&at("10:00"), &["done"]);
    tm.ok_at(&at("10:10"), &["start", "^t4"]);
    tm.ok_at(&at("11:10"), &["stop"]);
    tm.ok_at(&at("11:10"), &["break", "20m"]);
    tm.ok_at(&at("11:00"), &["break", "40m"]);
    let s = refused_with(&tm, "11:00", &["break", "40m"]);
    assert!(s.contains("a break planned 40m is logged 11:00–11:40") && !s.contains("re-times it"), "{s}");
    // With another place the kernel, a break running, reads the line as a break of its own: logged, and the first keeps its span.
    let s = said(&tm, "11:00", &["break", "40m", "--where", "bed"]);
    assert!(s.contains("11:00–11:40 · logged finished (it lies inside the break 11:00–11:40 the log holds)"), "{s}");
    let (rows, _) = break_records(&tm);
    assert!(rows.contains(&(40, 40, None)) && rows.contains(&(40, 0, Some("bed".to_string()))), "{rows:?}");
}

/// **A break one minute long, its own length guarded: only `tm undo`, then the first free instant** (until this row each refusal named
/// the other: "a different length", and "ends by 11:10", whose only length is the guarded one).
#[test]
fn where_no_length_and_no_instant_works_neither_is_offered() {
    let tm = fresh();
    tm.ok_at(&at("09:00"), &["start", "^t1"]);
    tm.ok_at(&at("10:00"), &["done"]);
    tm.ok_at(&at("10:10"), &["start", "^t4"]);
    tm.ok_at(&at("11:10"), &["stop"]);
    tm.ok_at(&at("11:09"), &["break", "1m"]);
    let s = refused_with(&tm, "11:09", &["break", "1m"]);
    assert!(!s.contains("re-times it") && !s.contains("type a length") && s.contains("`tm undo`"), "{s}");
    let s = refused_with(&tm, "11:09", &["break", "2m"]);
    assert!(s.contains("no whole-minute length") && s.contains("a length typed at 11:10 lies outside every logged break"), "{s}");
    let followed = copied(&tm);
    followed.ok_at(&at("11:10"), &["break", "2m"]);
    let tm = j_day(&[("11:09", "1m")]);
    let s = refused(&tm, "11:09");
    assert!(!s.contains("type a length") && s.contains("`tm undo`"), "{s}");
}

/// **The instants a refusal names are the ones that act** (until this row "give a later instant, before 10:10" where 30 of 39 were refused,
/// "give an instant inside it" where 6 of 24 were, and at 09:40:30 "a later instant" whose next thirty seconds were refused the same way).
#[test]
fn the_refusals_name_the_range_of_instants_that_works() {
    let tm = j_day(&[("09:40", ""), ("09:30", "")]);
    let s = refused(&tm, "09:30");
    assert!(s.contains("give an instant from 09:31 to 09:39 to end it there (D141)"), "{s}");
    assert!(said(&copied(&tm), "09:39", &["break"]).contains("ends here, at 09:39"));
    assert!(refused(&tm, "09:41").contains("meets more than one logged break"));

    let tm = r_day(&[("10:15", ""), ("10:40", ""), ("10:20", "5m")]);
    let s = refused(&tm, "10:15");
    assert!(s.contains("give an instant from 10:16 to 10:19 or from 10:26 to 10:39 to end it there"), "{s}");
    for hm in ["10:16", "10:19", "10:26", "10:39"] {
        assert!(said(&copied(&tm), hm, &["break"]).contains("re-timed to end at"), "{hm}");
    }
    for hm in ["10:20", "10:22", "10:25"] {
        assert!(refused(&tm, hm).contains("meets more than one logged break"), "{hm}");
    }

    let tm = j_day(&[("09:40", "")]);
    let s = refused(&tm, "09:40:30");
    assert!(s.contains("give an instant from 09:41 to 10:09 to end it there"), "{s}");
    assert_eq!(refused(&tm, "09:40:45"), s);
    assert!(said(&copied(&tm), "09:41", &["break"]).contains("ends here, at 09:41"));
}

/// **Every instant inside is another break's too: none is offered.** `09:30 30m`, `09:31 29m`: until this row "give an instant inside it",
/// and each one was refused. A length is offered, and driven.
#[test]
fn an_at_start_refusal_offers_no_instant_when_none_exists() {
    let tm = j_day(&[("09:30", "30m"), ("09:31", "29m")]);
    let s = refused(&tm, "09:30");
    assert!(!s.contains("give an instant") && s.contains("every instant inside it meets another logged break"), "{s}");
    assert!(s.contains("type a length") && s.contains("(D143)"), "{s}");
    logs_finished(&tm, "09:30", "5m");
}

/// **D157: a re-time out over a logged break stands, and the reply names what it covers**, each by its own span, `--json` too (README
/// gap 6066). Until this row a user lengthening a break swallowed the break between with no word of it. A re-time out over nothing and
/// a re-time in name nothing.
#[test]
fn a_re_time_out_names_each_logged_break_it_covers() {
    let day = || {
        let tm = j_day(&[("09:20", "30m"), ("09:30", ""), ("09:35", "5m")]);
        tm.ok_at(&at("09:42"), &["break", "2m"]);
        tm
    };
    let s = said(&day(), "09:45", &["break"]);
    assert!(s.contains("re-timed out to end at 09:45 (D150) · 25m of 30m · it now covers the logged breaks 09:35–09:40, 09:42–09:44"), "{s}");
    let v = day().json_at(&at("09:45"), &["break"]);
    assert_eq!(v["covers"], serde_json::json!(["09:35–09:40", "09:42–09:44"]), "{v}");
    let tm = day();
    tm.ok_at(&at("09:45"), &["break"]);
    reads(&tm, 95);
    // Up to the break between and no further: nothing covered, nothing said, no key.
    let tm = j_day(&[("09:20", "30m"), ("09:30", ""), ("09:45", "5m")]);
    let v = tm.json_at(&at("09:40"), &["break"]);
    assert_eq!((v["action"].as_str(), v.get("covers")), (Some("retimed"), None), "{v}");
    let tm = j_day(&[("09:20", "30m")]);
    let s = said(&tm, "09:30", &["break"]);
    assert!(s.contains("re-timed to end at 09:30") && !s.contains("covers"), "{s}");
}
