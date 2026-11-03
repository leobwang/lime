//! **Stage 6 W-54 track H, through the binary**: the owner's **D149** (parity **P147**: a backdated `tm break --now
//! <past> <length>` typed inside a block a later logged `done` or `stop` closed is logged finished), the owner's
//! **D150** (parity **P148**: a no-length `tm break` past a shortened finished break's current end but inside the
//! widest span the log has held for it re-times it OUT), and the campaign's calls on the re-time gate's honesty (README
//! gaps 5895 and 5896: refused by name inside a drawn break the fact omits, and before a running break's start).
//!
//! Every reply that says "re-timed" is checked here against the review and the drawn rows after it, so a reply the
//! kernel does not bear out fails a test (the W-53 repair auditor's second note).
//!
//! The day is the J drive's: the example tree, woken 07:00, home 08:00, `^t1` 09:00–10:00 and `^t4` 10:10–11:10 done.

mod cli_common;

use cli_common::Tm;
use serde_json::Value;

const TUE: &str = "2026-09-08";

fn at(hm: &str) -> String {
    format!("{TUE}T{hm}:00-05:00")
}

fn fresh() -> Tm {
    let tm = Tm::empty();
    tm.ok_at(&at("06:00"), &["init", "--example"]);
    tm.ok_at(&at("07:00"), &["wake", "07:00"]);
    tm.ok_at(&at("08:00"), &["arrive", "home"]);
    tm
}

/// The J drive's day: `^t1` 09:00–10:00 and `^t4` 10:10–11:10 done.
fn j_tree() -> Tm {
    let tm = fresh();
    tm.ok_at(&at("09:00"), &["start", "^t1"]);
    tm.ok_at(&at("10:00"), &["done"]);
    tm.ok_at(&at("10:10"), &["start", "^t4"]);
    tm.ok_at(&at("11:10"), &["done"]);
    tm
}

fn append(tm: &Tm, line: &str) {
    let log = tm.plan.join(".tm/log.jsonl");
    let mut text = std::fs::read_to_string(&log).expect("the log");
    text.push_str(line);
    text.push('\n');
    std::fs::write(&log, &text).expect("write the log");
}

fn breaks(tm: &Tm) -> Vec<Value> {
    tm.log().into_iter().filter(|e| e["ev"] == "break" || e["ev"] == "break_start").collect()
}

/// `tm review day`'s block minutes and each break's minutes, at 12:30.
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

/// `tm plan`'s rows at 12:30 between 09:00 and 11:59, each with its runs of spaces collapsed to one.
fn rows(tm: &Tm) -> Vec<String> {
    tm.ok_at(&at("12:30"), &["plan"])
        .stdout
        .lines()
        .map(|l| l.split_whitespace().collect::<Vec<_>>().join(" "))
        .filter(|l| ["09:", "10:", "11:"].iter().any(|h| l.starts_with(h)))
        .collect()
}

fn has_row(rows: &[String], row: &str) {
    assert!(rows.iter().any(|r| r == row), "the plan draws {row:?}: {rows:#?}");
}

// ---------------------------------------------------------------------------------------------------------------
// D149 (parity P147, README gap 5860 closed)

/// **A length inside a block a later `done` closed is logged finished** (P147). `tm break --now 10:30 10m` inside
/// `^t4` (10:10–11:10 done, no later start) writes ONE plain `break` line — `t` 10:30, planned and actual ten — and no
/// `break_start`; the reply names D149; `^t4` reads fifty (110); the plan draws the break and `^t4` around it; nothing
/// runs; `tm check` is silent. Until D149 the line was a `break_start` that ran to the next verb, netted 40 of `^t4`'s
/// 60 minutes and was drawn `10:30 · break 2h` (gap 5860).
#[test]
fn a_length_inside_a_done_block_is_logged_finished_p147() {
    let tm = j_tree();
    let out = tm.ok_at(&at("10:30"), &["break", "10m"]);
    assert_eq!(
        out.stdout.trim(),
        "break 10m · 10:30–10:40 · logged finished (it lies inside the block of ^t4 a later `done` or `stop` closed, \
         which it nets, D149)",
        "{}",
        out.stderr
    );
    let b = breaks(&tm);
    assert_eq!(b.len(), 1, "{b:?}");
    assert_eq!((b[0]["ev"].as_str(), b[0]["t"].as_str()), (Some("break"), Some(at("10:30").as_str())), "{b:?}");
    assert_eq!((b[0]["planned_min"].as_u64(), b[0]["actual_min"].as_u64()), (Some(10), Some(10)), "{b:?}");
    assert_eq!(review(&tm), (110, vec![10]), "^t4 fifty, the break ten");
    let r = rows(&tm);
    has_row(&r, "10:30 · break 10m");
    has_row(&r, "10:40 3 ✓ Claude Code drafts tests @m2 1b (30m)");
    assert!(tm.state()["break"].is_null(), "nothing left running: {}", tm.state());
    assert!(tm.ok_at(&at("12:30"), &["check"]).stdout.contains("no problems"));
    let journal = tm.read(&format!("day/{TUE}.md"));
    assert!(journal.contains("10:30 break 10m") && journal.contains("10:40 break ended 10m/10m"), "{journal}");
}

/// **`--json`**: `action` `finished`, its span, and `finished.inside_block` the closed block's item.
#[test]
fn a_d149_break_reports_the_block_it_lies_inside_p147() {
    let tm = j_tree();
    let v = tm.json_at(&at("10:30"), &["break", "10m"]);
    assert_eq!(v["action"], "finished", "{v}");
    assert_eq!(v["finished"]["start"], "10:30", "{v}");
    assert_eq!(v["finished"]["end"], "10:40", "{v}");
    assert_eq!(v["finished"]["inside_block"], "t4", "{v}");
    assert!(v["finished"].get("into_start").is_none(), "{v}");
}

/// **A length running past the `done` is logged at its typed length** (P147, D148's rule): `tm break --now 11:00 20m`
/// is one plain line of twenty, and the kernel nets `^t4` by the ten minutes the break overlaps it (D100): `^t4` fifty,
/// the break twenty, drawn whole.
#[test]
fn a_length_past_the_done_is_logged_at_its_length_and_nets_the_overlap_p147() {
    let tm = j_tree();
    let out = tm.ok_at(&at("11:00"), &["break", "20m"]);
    assert!(out.stdout.contains("11:00–11:20 · logged finished") && out.stdout.contains("D149"), "{}", out.stdout);
    let b = breaks(&tm);
    assert_eq!((b.len(), b[0]["actual_min"].as_u64()), (1, Some(20)), "{b:?}");
    assert_eq!(review(&tm), (110, vec![20]));
    let r = rows(&tm);
    has_row(&r, "10:10 3 ✓ Claude Code drafts tests @m2 1b (50m)");
    has_row(&r, "11:00 · break 20m");
}

/// **A STOPPED block the line nets has its `est:` corrected** (D126, as D148 does): `^t4` stopped at 11:10 with `5m`
/// left, then `tm break --now 10:30 10m` — the block reads fifty, and the line `15m`, the `edit` logged. Until D149
/// the running break netted forty and the correction wrote `45m`.
#[test]
fn a_d149_break_inside_a_stopped_block_corrects_its_estimate_p147() {
    let tm = fresh();
    tm.ok_at(&at("09:00"), &["start", "^t1"]);
    tm.ok_at(&at("10:00"), &["done"]);
    tm.ok_at(&at("10:10"), &["start", "^t4"]);
    tm.ok_at(&at("11:10"), &["stop"]);
    assert!(tm.line("week/2026-W37.md", "t4").contains(" 5m "), "{}", tm.line("week/2026-W37.md", "t4"));
    let out = tm.ok_at(&at("10:30"), &["break", "10m"]);
    assert!(out.stdout.contains("D149"), "{}", out.stdout);
    assert!(out.stderr.contains("^t4's estimate is now 15m (was 5m)"), "{}", out.stderr);
    assert!(tm.line("week/2026-W37.md", "t4").contains(" 15m "), "{}", tm.line("week/2026-W37.md", "t4"));
    let edit = tm.last_ev("edit");
    assert_eq!((edit["from"].as_str(), edit["to"].as_str()), (Some("5m"), Some("15m")), "{edit}");
    assert_eq!(review(&tm), (110, vec![10]));
}

/// **After every block, a length still begins a break** (D149 is about a block a later line CLOSED): with `^t4` done at
/// 11:10, `tm break --now 11:30 10m` begins the running break it always did.
#[test]
fn a_length_after_every_block_still_begins_a_break() {
    let tm = j_tree();
    let v = tm.json_at(&at("11:30"), &["break", "10m"]);
    assert_eq!(v["action"], "started", "{v}");
    assert!(!tm.state()["break"].is_null(), "{}", tm.state());
}

// ---------------------------------------------------------------------------------------------------------------
// D150 (parity P148) — the widest end is track K's fact (W-54 track K item 6), stubbed on this branch

/// The D150 day: `tm break --now 09:20 30m` (D143, 09:20–09:50), re-timed to 09:40 and then to 09:30 (D147).
fn shortened_tree() -> Tm {
    let tm = j_tree();
    tm.ok_at(&at("09:20"), &["break", "30m"]);
    assert!(tm.ok_at(&at("09:40"), &["break"]).stdout.contains("re-timed to end at 09:40 (D147)"));
    assert!(tm.ok_at(&at("09:30"), &["break"]).stdout.contains("re-timed to end at 09:30 (D147)"));
    assert_eq!(review(&tm), (110, vec![10]));
    tm
}

/// **Past the current end, inside the widest span: re-timed OUT** (P148). `tm break --now 09:45` writes one `break`
/// line at 09:20, planned thirty, actual twenty-five, says `re-timed out to end at 09:45 (D150)`, and the day reads the
/// break at twenty-five (`^t1` thirty-five, 95), drawn 09:20–09:45. Before D150 the instant began a break D129 ran to
/// 10:10 (`^t1` lost fifteen more minutes, D129's notice the only signal).
#[test]
fn a_no_length_break_past_a_shortened_breaks_end_retimes_it_out_p148() {
    let tm = shortened_tree();
    let out = tm.ok_at(&at("09:45"), &["break"]);
    assert_eq!(out.stdout.trim(), "break 09:20–09:30 re-timed out to end at 09:45 (D150) · 25m of 30m", "{}", out.stderr);
    assert!(!out.stderr.contains("(D129)"), "{}", out.stderr);
    let b = breaks(&tm);
    let last = b.last().expect("a break line");
    assert_eq!((last["ev"].as_str(), last["t"].as_str()), (Some("break"), Some(at("09:20").as_str())), "{b:?}");
    assert_eq!((last["planned_min"].as_u64(), last["actual_min"].as_u64()), (Some(30), Some(25)), "{b:?}");
    assert!(b.iter().all(|e| e["ev"] == "break"), "no break_start: {b:?}");
    assert_eq!(review(&tm), (95, vec![25]));
    let r = rows(&tm);
    has_row(&r, "09:20 · break 25m");
    has_row(&r, "09:45 5 ✓ Read ch.6 §1–2 @m3 1b (15m)");
    let v = tm.json_at(&at("09:45"), &["break"]);
    assert_eq!(v["action"], "unchanged", "at its new end: {v}");
}

/// **D147's own row, one instant on** (`cli_d147_retime.rs`'s first row typed 09:26 here until W-54): `09:20 10m`
/// re-timed to 09:24, then `tm break --now 09:26` — inside the widest span (09:30) — re-times it OUT to 09:26: the
/// break six, `^t1` fifty-four.
#[test]
fn a_break_retimed_in_is_retimed_out_inside_its_old_span_p148() {
    let tm = j_tree();
    tm.ok_at(&at("09:20"), &["break", "10m"]);
    assert!(tm.ok_at(&at("09:24"), &["break"]).stdout.contains("re-timed to end at 09:24 (D147)"));
    let v = tm.json_at(&at("09:26"), &["break"]);
    assert_eq!((v["action"].as_str(), v["actual_min"].as_u64()), (Some("retimed"), Some(6)), "{v}");
    assert_eq!(review(&tm), (114, vec![6]));
    has_row(&rows(&tm), "09:20 · break 6m");
}

/// **`--json`**: `action` `retimed`, `superseded_end` the end it replaced.
#[test]
fn a_break_retimed_out_reports_the_end_it_replaced_p148() {
    let tm = shortened_tree();
    let v = tm.json_at(&at("09:45"), &["break"]);
    assert_eq!(v["action"], "retimed", "{v}");
    assert_eq!((v["actual_min"].as_u64(), v["planned_min"].as_u64()), (Some(25), Some(30)), "{v}");
    assert_eq!(v["superseded_end"], "09:30", "{v}");
}

/// **Past the widest end, D147 stands: a break begins** — at 09:55, past 09:50, D129 runs it to the 10:10 start.
#[test]
fn past_the_widest_end_a_break_begins_p148() {
    let tm = shortened_tree();
    let out = tm.ok_at(&at("09:55"), &["break"]);
    assert!(out.stderr.contains("began at 09:55 ended at 10:10") && out.stderr.contains("(D129)"), "{}", out.stderr);
}

/// **Out and back** (track K's item 6 witness): 09:20 30m → 09:40 → 09:30 → out to 09:45 → back to 09:35 — one break
/// 09:20–09:35: the review records fifteen, `^t1` forty-five.
#[test]
fn a_break_retimed_out_and_back_reads_its_last_end_p148() {
    let tm = shortened_tree();
    assert!(tm.ok_at(&at("09:45"), &["break"]).stdout.contains("(D150)"));
    let out = tm.ok_at(&at("09:35"), &["break"]);
    assert!(out.stdout.contains("re-timed to end at 09:35 (D147)"), "{}", out.stdout);
    assert_eq!(review(&tm), (105, vec![15]));
    has_row(&rows(&tm), "09:20 · break 15m");
}

// ---------------------------------------------------------------------------------------------------------------
// The re-time gate's honesty (README gaps 5895, 5896)

/// **Inside a drawn break the fact omits: refused by name** (the campaign's call, gap 5895). `09:20 20m`, then `09:30
/// 20m` (both D143), then `tm break --now 09:25`: since W-54 track K the fact lists only breaks a re-time line will
/// re-time, the 09:20 break another overlaps is absent, and the instant is inside its drawn 09:20–09:40 — refused,
/// nothing written. On the W-53 repair's kernel it said "re-timed" while the kernel added a zero-minute break.
#[test]
fn inside_an_overlapped_break_the_verb_refuses_by_name() {
    let tm = j_tree();
    tm.ok_at(&at("09:20"), &["break", "20m"]);
    tm.ok_at(&at("09:30"), &["break", "20m"]);
    let log = tm.read(".tm/log.jsonl");
    let out = tm.run_at(&at("09:25"), &["break"]);
    assert_ne!(out.code, 0, "{}", out.stdout);
    assert!(out.stderr.contains("drawn 09:20–09:40") && out.stderr.contains("overlaps"), "{}", out.stderr);
    assert_eq!(tm.read(".tm/log.jsonl"), log, "nothing written");
    assert_eq!(review(&tm), (90, vec![20, 10]));
}

/// **Nested: likewise** — `09:20 30m`, `09:30 5m`, then `tm break --now 09:45` inside the outer break's drawn span.
#[test]
fn inside_a_break_another_nests_in_the_verb_refuses_by_name() {
    let tm = j_tree();
    tm.ok_at(&at("09:20"), &["break", "30m"]);
    tm.ok_at(&at("09:30"), &["break", "5m"]);
    let log = tm.read(".tm/log.jsonl");
    let out = tm.run_at(&at("09:45"), &["break"]);
    assert_ne!(out.code, 0, "{}", out.stdout);
    assert!(out.stderr.contains("drawn 09:20–09:50"), "{}", out.stderr);
    assert_eq!(tm.read(".tm/log.jsonl"), log, "nothing written");
}

/// The J day with a finished break 09:20–09:30 and a break running since 11:30.
fn running_tree() -> Tm {
    let tm = j_tree();
    tm.ok_at(&at("09:20"), &["break", "10m"]);
    assert_eq!(tm.json_at(&at("11:30"), &["break", "20m"])["action"], "started");
    tm
}

/// **With a break RUNNING, a no-length `tm break` before its start is refused by name** (the campaign's call, gap
/// 5896): inside the finished 09:20–09:30 break it said "re-timed" while the kernel re-timed nothing and the line
/// cleared the running break (D145, not built; gap 5820's damage) — nothing is written now, and the break still runs.
#[test]
fn a_no_length_break_inside_a_finished_break_while_one_runs_is_refused() {
    let tm = running_tree();
    let (log, state) = (tm.read(".tm/log.jsonl"), tm.read(".tm/state.json"));
    let out = tm.run_at(&at("09:25"), &["break"]);
    assert_ne!(out.code, 0, "{}", out.stdout);
    assert!(
        out.stderr.contains("a break is running since 11:30") && out.stderr.contains("D145") && out.stderr.contains("not built"),
        "{}",
        out.stderr
    );
    assert_eq!(tm.read(".tm/log.jsonl"), log, "nothing written");
    assert_eq!(tm.read(".tm/state.json"), state, "the cache untouched");
    let now = tm.ok_at(&at("11:40"), &["now"]).stdout;
    assert!(now.contains("on break since 11:30 · 10m of 20m"), "{now}");
    assert_eq!(review(&tm).1[0], 10, "the finished break is not re-timed");
}

/// **Outside every break, likewise**: before this call a no-length `tm break --now 09:45` with a break running since
/// 11:30 began a second `break_start` that D129 ran to 10:10, and the running break was dropped from the cache (`tm
/// now` then "nothing running").
#[test]
fn a_no_length_break_before_a_running_breaks_start_is_refused() {
    let tm = running_tree();
    let log = tm.read(".tm/log.jsonl");
    let out = tm.run_at(&at("09:45"), &["break"]);
    assert_ne!(out.code, 0, "{}", out.stdout);
    assert!(out.stderr.contains("running since 11:30") && out.stderr.contains("D145"), "{}", out.stderr);
    assert_eq!(tm.read(".tm/log.jsonl"), log, "nothing written");
    assert!(tm.ok_at(&at("11:40"), &["now"]).stdout.contains("on break since 11:30"));
}

/// **A length that would BEGIN a break while one runs is refused too**: `tm break --now 11:15 5m` (after `^t4`'s
/// `done`, no later start, before the 11:30 break) is logged finished by none of D143, D148 and D149.
#[test]
fn a_length_that_would_begin_a_second_running_break_is_refused() {
    let tm = running_tree();
    let log = tm.read(".tm/log.jsonl");
    let out = tm.run_at(&at("11:15"), &["break", "5m"]);
    assert_ne!(out.code, 0, "{}", out.stdout);
    assert!(out.stderr.contains("running since 11:30") && out.stderr.contains("D145"), "{}", out.stderr);
    assert_eq!(tm.read(".tm/log.jsonl"), log, "nothing written");
}

/// **A length that is logged finished while a break runs keeps D143** (D145's host half, P140): `tm break --now 10:30
/// 5m` inside `^t4` (D149) writes its one plain line and the 11:30 break still runs.
#[test]
fn a_finished_break_while_one_runs_is_still_logged() {
    let tm = running_tree();
    let v = tm.json_at(&at("10:30"), &["break", "5m"]);
    assert_eq!(v["action"], "finished", "{v}");
    assert_eq!(v["finished"]["inside_block"], "t4", "{v}");
    assert!(tm.read(".tm/state.json").contains("11:30"), "{}", tm.read(".tm/state.json"));
}

// ---------------------------------------------------------------------------------------------------------------
// The gate's order: D129-ended FIRST (the W-53 repair auditor's eighth note)

/// **Row G3**: `09:20 20m` (D143, 09:20–09:40), then `09:10` (a break D129 ends at 10:10), then `09:35` — an instant
/// inside BOTH the finished 09:20 break and the 09:10 break D129 ended. D141 comes first: the 09:10 break ends at
/// 09:35 (its `break` line at 09:10, actual twenty-five), the finished break is not re-timed. Removing the gate's
/// `superseded.is_none() &&` (README §8's plant) re-times the 09:20 break instead, and this row fails.
#[test]
fn inside_a_d129_ended_break_and_a_finished_one_d141_comes_first() {
    let tm = j_tree();
    tm.ok_at(&at("09:20"), &["break", "20m"]);
    let out = tm.ok_at(&at("09:10"), &["break"]);
    assert!(out.stderr.contains("began at 09:10 ended at 10:10"), "{}", out.stderr);
    let v = tm.json_at(&at("09:35"), &["break"]);
    assert_eq!(v["action"], "ended", "D141, not D147: {v}");
    assert_eq!(v["superseded_end"], "10:10", "{v}");
    assert_eq!(v["actual_min"], 25, "{v}");
    let b = breaks(&tm);
    let last = b.last().expect("a break line");
    assert_eq!((last["t"].as_str(), last["actual_min"].as_u64()), (Some(at("09:10").as_str()), Some(25)), "{b:?}");
    assert_eq!(review(&tm), (90, vec![25, 5]));
    let r = rows(&tm);
    has_row(&r, "09:10 · break 25m");
    has_row(&r, "09:35 · break 5m");
}

// ---------------------------------------------------------------------------------------------------------------
// A re-time over a block that was RUNNING when the break netted it (the W-53 repair auditor's first note; K's item 1)

/// `start ^t1` 09:00, `break 10m` 09:20, `done` 10:00 (`break ended · 40m of 10m`), `^t4` 10:10–11:10, then `tm break
/// --now 09:30` re-times the break to 09:20–09:30.
fn running_block_tree(close: &str) -> Tm {
    let tm = fresh();
    tm.ok_at(&at("09:00"), &["start", "^t1"]);
    tm.ok_at(&at("09:20"), &["break", "10m"]);
    tm.ok_at(&at("10:00"), &[close]);
    tm.ok_at(&at("10:10"), &["start", "^t4"]);
    tm.ok_at(&at("11:10"), &["done"]);
    let out = tm.ok_at(&at("09:30"), &["break"]);
    assert!(out.stdout.contains("re-timed to end at 09:30 (D147)"), "{}", out.stdout);
    tm
}

/// **The re-time gives back what the break took** (`done`): `^t1` fifty (09:00–09:20 and 09:30–10:00), 110, the plan
/// drawing `09:20 · break 10m` and then `^t1` from 09:30 — on the W-53 repair's kernel the review stayed 80 and the plan
/// drew a thirty-minute hole until 10:10.
#[test]
fn a_retime_over_a_block_that_ran_gives_its_minutes_back() {
    let tm = running_block_tree("done");
    assert_eq!(review(&tm), (110, vec![10]));
    let r = rows(&tm);
    has_row(&r, "09:20 · break 10m");
    has_row(&r, "09:30 5 ✓ Read ch.6 §1–2 @m3 1b (30m)");
}

/// **`stop`: the `est:` D126 writes once the kernel's facts net the block** — `^t1` stopped at 10:00 with `40m` left
/// (twenty worked), re-timed: fifty worked, so `take_break`'s correction (it runs after the re-time line too) writes
/// `10m`.
#[test]
fn a_retime_over_a_stopped_block_that_ran_corrects_its_estimate() {
    let tm = running_block_tree("stop");
    assert!(tm.line("week/2026-W37.md", "t1").contains(" 10m "), "{}", tm.line("week/2026-W37.md", "t1"));
    let edit = tm.last_ev("edit");
    assert_eq!((edit["from"].as_str(), edit["to"].as_str()), (Some("40m"), Some("10m")), "{edit}");
}

// ---------------------------------------------------------------------------------------------------------------
// The ending reply reads the drawn minutes (the W-53 repair critic's sixth note, README gap 5898)

/// **F3**: a break logged by hand 10:20–10:40, `tm break 20m` at 10:30 (drawn from 10:40 — `tm now` at 11:00 reads
/// `20m of 20m`), then `tm break` at 11:05: the reply and the journal say twenty-five, as the review records it; the
/// log's `actual_min` stays the wall-clock thirty-five (the fork's shape, which the kernel's union reads, D142). Until
/// this call the reply read `break ended · 35m of 20m` beside a review of 25.
#[test]
fn a_running_break_an_earlier_one_covers_ends_with_its_drawn_minutes() {
    let tm = fresh();
    append(&tm, r#"{"t":"2026-09-08T10:20:00-05:00","ev":"break","planned_min":20,"actual_min":20}"#);
    tm.ok_at(&at("10:30"), &["break", "20m"]);
    assert!(tm.ok_at(&at("11:00"), &["now"]).stdout.contains("on break since 10:30 · 20m of 20m"));
    let out = tm.ok_at(&at("11:05"), &["break"]);
    assert_eq!(out.stdout.trim(), "break ended · 25m of 20m", "{}", out.stderr);
    let last = tm.log().pop().expect("a log");
    assert_eq!((last["ev"].as_str(), last["actual_min"].as_u64()), (Some("break"), Some(35)), "{last}");
    assert!(tm.read(&format!("day/{TUE}.md")).contains("11:05 break ended 25m/20m"));
    assert_eq!(review(&tm).1, vec![20, 25]);
}

/// **An ordinary ending is unchanged**: the drawn minutes are the wall clock's when no earlier break covers the break.
#[test]
fn an_uncovered_running_break_ends_with_its_wall_clock_minutes() {
    let tm = fresh();
    tm.ok_at(&at("10:30"), &["break", "20m"]);
    let v = tm.json_at(&at("11:05"), &["break"]);
    assert_eq!((v["action"].as_str(), v["actual_min"].as_u64()), (Some("ended"), Some(35)), "{v}");
}
