//! **Stage 6 W-54 repair track H, through the binary**: the owner's **D152** (parity **P149**, closing README gap 5892:
//! a backdated `tm break --now <past> <length>` typed inside the RUNNING block, whose typed end the log has already
//! passed, is logged finished — one plain `break` line, the block netted and left running, not paused); the re-time
//! gate's honesty (README gap 5941: a re-time the drawn rows would not bear out is refused by name, and D150's Out never
//! swallows another logged break); D149's and D152's replies saying "nets" only when the block's minutes fell (the W-54
//! critic's fourth note); the gate's arm order through the binary (the W-54 auditor's missing row); and D151's rows
//! (parity P148 restated), which wait on track K's item 2 and are ignored for the land, named.
//!
//! The day is the example tree, woken 07:00, home 08:00, `TZ` the plan's (America/Chicago), Tuesday 2026-09-08.

mod cli_common;

use cli_common::Tm;
use serde_json::Value;

const TUE: &str = "2026-09-08";
const WEEK: &str = "week/2026-W37.md";

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

/// `^t1` 09:00–10:00 done, `^t4` started at 10:10 and still running.
fn running_t4() -> Tm {
    let tm = fresh();
    tm.ok_at(&at("09:00"), &["start", "^t1"]);
    tm.ok_at(&at("10:00"), &["done"]);
    tm.ok_at(&at("10:10"), &["start", "^t4"]);
    tm
}

/// The critic's d17 tree: `running_t4` with a pause 10:40–10:45, so the log's last line is the 10:45 unpause.
fn d17_tree() -> Tm {
    let tm = running_t4();
    tm.ok_at(&at("10:40"), &["pause"]);
    tm.ok_at(&at("10:45"), &["pause"]);
    tm
}

fn breaks(tm: &Tm) -> Vec<Value> {
    tm.log().into_iter().filter(|e| e["ev"] == "break" || e["ev"] == "break_start").collect()
}

/// `tm review day`'s block minutes and each break's minutes, at `hm`.
fn review_at(tm: &Tm, hm: &str) -> (u64, Vec<u64>) {
    let v = tm.json_at(&at(hm), &["review", "day"]);
    let r = &v["review"];
    let breaks = r["breaks"]["breaks"]
        .as_array()
        .unwrap_or_else(|| panic!("{v}"))
        .iter()
        .map(|b| b["actual_min"].as_u64().unwrap_or_default())
        .collect();
    (r["block_min"].as_u64().unwrap_or_else(|| panic!("{v}")), breaks)
}

fn review(tm: &Tm) -> (u64, Vec<u64>) {
    review_at(tm, "12:30")
}

/// `tm plan`'s rows at `hm` between 09:00 and 11:59, each with its runs of spaces collapsed to one.
fn rows_at(tm: &Tm, hm: &str) -> Vec<String> {
    tm.ok_at(&at(hm), &["plan"])
        .stdout
        .lines()
        .map(|l| l.split_whitespace().collect::<Vec<_>>().join(" "))
        .filter(|l| ["09:", "10:", "11:"].iter().any(|h| l.starts_with(h)))
        .collect()
}

fn rows(tm: &Tm) -> Vec<String> {
    rows_at(tm, "12:30")
}

fn has_row(rows: &[String], row: &str) {
    assert!(rows.iter().any(|r| r == row), "the plan draws {row:?}: {rows:#?}");
}

/// `tm now`'s first two lines at `hm`.
fn now_at(tm: &Tm, hm: &str) -> String {
    tm.ok_at(&at(hm), &["now"]).stdout.lines().take(2).collect::<Vec<_>>().join("\n")
}

/// A refusal: non-zero, and the log, the day file and `.tm/state.json` byte for byte as they were.
fn refused(tm: &Tm, hm: &str, args: &[&str]) -> String {
    let (log0, day0, state0) = (tm.read(".tm/log.jsonl"), tm.read(&format!("day/{TUE}.md")), tm.read(".tm/state.json"));
    let out = tm.run_at(&at(hm), args);
    assert_ne!(out.code, 0, "refused: {}", out.stdout);
    assert_eq!(tm.read(".tm/log.jsonl"), log0, "nothing logged: {}", out.stderr);
    assert_eq!(tm.read(&format!("day/{TUE}.md")), day0, "nothing journalled");
    assert_eq!(tm.read(".tm/state.json"), state0, "the cache untouched");
    format!("{}{}", out.stdout, out.stderr)
}

// ---------------------------------------------------------------------------------------------------------------
// D152 (parity P149, README gap 5892 closed)

/// **The critic's d17, after D152** (P149). `^t4` runs since 10:10 (paused 10:40–10:45); `tm break --now 10:20 10m`
/// lies inside it and the log has passed 10:30 (its last line is the 10:45 unpause), so the break is over: ONE plain
/// `break` line (`t` 10:20, planned and actual ten, no `break_start`), the reply names the running block, `.tm/state.json`
/// keeps `^t4` running and unpaused with no break, `tm now` at 10:55 reads `30m of 60m` (the break netted, not paused),
/// and the plan draws `10:20 · break 10m` with `^t4` around it. Until D152 the line was a `break_start`: `tm now` read
/// `^t4 … 10m of 60m · paused` and `on break since 10:20 · 35m of 10m`, the plan `10:20 · break 35m`, the reply only
/// `break 10m`.
#[test]
fn a_length_inside_the_running_block_already_over_is_logged_finished_p149() {
    let tm = d17_tree();
    let out = tm.ok_at(&at("10:20"), &["break", "10m"]);
    assert_eq!(
        out.stdout.trim(),
        "break 10m · 10:20–10:30 · logged finished (it lies inside ^t4, which is running; it nets it, D152)",
        "{}",
        out.stderr
    );
    let b = breaks(&tm);
    assert_eq!(b.len(), 1, "{b:?}");
    assert_eq!((b[0]["ev"].as_str(), b[0]["t"].as_str()), (Some("break"), Some(at("10:20").as_str())), "{b:?}");
    assert_eq!((b[0]["planned_min"].as_u64(), b[0]["actual_min"].as_u64()), (Some(10), Some(10)), "{b:?}");
    let s = tm.state();
    assert!(s["break"].is_null(), "no running break: {s}");
    assert_eq!((s["active"]["id"].as_str(), s["active"]["paused"].as_bool()), (Some("t4"), Some(false)), "{s}");
    let now = now_at(&tm, "10:55");
    assert!(now.contains("started 10:10 · 30m of 60m") && !now.contains("paused") && !now.contains("on break"), "{now}");
    assert_eq!(review_at(&tm, "10:55"), (60, vec![10]), "^t1's sixty closed; the break ten");
    let r = rows_at(&tm, "10:55");
    has_row(&r, "10:20 · break 10m");
    has_row(&r, "10:30 3 p3 Claude Code drafts tests @m2 1b");
    assert!(!r.iter().any(|x| x.contains("break 35m")), "{r:#?}");
    assert!(tm.ok_at(&at("10:55"), &["check"]).stdout.contains("no problems"));
    let journal = tm.read(&format!("day/{TUE}.md"));
    assert!(journal.contains("10:20 break 10m") && journal.contains("10:30 break ended 10m/10m"), "{journal}");
}

/// **`--json`**: `action` `finished`, its span, `finished.inside_running` the running block's item and `nets` true;
/// no `inside_block` (that is D149's, a closed block).
#[test]
fn a_d152_break_reports_the_running_block_it_lies_inside_p149() {
    let tm = d17_tree();
    let v = tm.json_at(&at("10:20"), &["break", "10m"]);
    assert_eq!(v["action"], "finished", "{v}");
    assert_eq!((v["finished"]["start"].as_str(), v["finished"]["end"].as_str()), (Some("10:20"), Some("10:30")), "{v}");
    assert_eq!(v["finished"]["inside_running"], "t4", "{v}");
    assert_eq!(v["finished"]["nets"], true, "{v}");
    assert!(v["finished"].get("inside_block").is_none() && v["finished"].get("into_start").is_none(), "{v}");
}

/// **With no pause marks, a later line is what says the break is over** (P149): `^t4` runs since 10:10 with no mark;
/// a `tm plan` at 10:50 is the log's last line, so `tm break --now 10:20 10m --where walk` is logged finished,
/// its place on the line and in the reply; `tm now` at 10:55 reads `35m of 60m`. (Restated at W-54 third repair track K for the
/// owner's D154: the later line was a plain `tm energy`, and no `energy` line witnesses an instant since the log cannot say
/// which were typed with `--at`; README gap 6031.)
#[test]
fn a_later_line_with_no_pause_marks_and_a_place_p149() {
    let tm = running_t4();
    tm.ok_at(&at("10:50"), &["plan"]);
    let out = tm.ok_at(&at("10:20"), &["break", "10m", "--where", "walk"]);
    assert_eq!(
        out.stdout.trim(),
        "break 10m (walk) · 10:20–10:30 · logged finished (it lies inside ^t4, which is running; it nets it, D152)",
        "{}",
        out.stderr
    );
    let b = breaks(&tm);
    assert_eq!((b.len(), b[0]["ev"].as_str(), b[0]["where"].as_str()), (1, Some("break"), Some("walk")), "{b:?}");
    let now = now_at(&tm, "10:55");
    assert!(now.contains("35m of 60m") && !now.contains("on break"), "{now}");
}

/// **A typed end the log has not reached is a break that may still run — unchanged** (P149's boundary): on the d17 tree
/// `tm break --now 10:40 10m` ends at 10:50, past the 10:45 unpause, so it begins a running break as before (a
/// `break_start`, the block paused); and on a tree whose last line is `^t4`'s own 10:10 start, `--now 10:20 10m` too.
#[test]
fn a_typed_end_the_log_has_not_reached_still_begins_a_break_p149() {
    let tm = d17_tree();
    let out = tm.ok_at(&at("10:40"), &["break", "10m"]);
    assert_eq!(out.stdout.trim(), "break 10m", "{}", out.stderr);
    assert_eq!(breaks(&tm).last().and_then(|e| e["ev"].as_str()), Some("break_start"));
    assert_eq!(tm.state()["active"]["paused"], true, "{}", tm.state());
    let tm = running_t4();
    let out = tm.ok_at(&at("10:20"), &["break", "10m"]);
    assert_eq!(out.stdout.trim(), "break 10m", "{}", out.stderr);
    assert_eq!(breaks(&tm).last().and_then(|e| e["ev"].as_str()), Some("break_start"));
}

/// **Inside the running block's pause it nets nothing, and says so** (P149, the critic's fourth note): on the d17 tree
/// `tm break --now 10:40 5m` (10:40–10:45, the pause) is logged finished — the log has reached 10:45 — and the reply
/// says the block was not running there; the minutes do not move (`nets` false).
#[test]
fn a_d152_break_inside_the_pause_nets_nothing_and_says_so_p149() {
    let tm = d17_tree();
    let before = now_at(&tm, "10:55");
    let v = tm.json_at(&at("10:40"), &["break", "5m"]);
    assert_eq!((v["action"].as_str(), v["finished"]["nets"].as_bool()), (Some("finished"), Some(false)), "{v}");
    assert_eq!(now_at(&tm, "10:55").lines().next(), before.lines().next(), "the block's minutes did not move");
    let tm = d17_tree();
    let out = tm.ok_at(&at("10:40"), &["break", "5m"]);
    assert!(
        out.stdout.contains("it lies inside ^t4, which is running; ^t4 was not running there (a pause, or another break), \
             so it nets nothing, D152"),
        "{}",
        out.stdout
    );
}

/// **`tm undo` takes the line back** (P149): after the d17 break, `tm undo` at 10:56 cancels the `break` line, and
/// `tm now` reads `^t4` as before it (`41m of 60m` at 10:56: 46 minutes since 10:10 less the 5-minute pause), running.
#[test]
fn undo_takes_a_d152_break_back_p149() {
    let tm = d17_tree();
    let before = now_at(&tm, "10:56");
    tm.ok_at(&at("10:20"), &["break", "10m"]);
    assert_ne!(now_at(&tm, "10:56").lines().next(), before.lines().next(), "the break netted ^t4");
    let out = tm.ok_at(&at("10:56"), &["undo"]);
    assert!(out.stdout.contains("undid break"), "{}", out.stdout);
    assert_eq!(tm.last_ev("undo")["of"], "break", "{:?}", tm.last());
    assert_eq!(now_at(&tm, "10:56").lines().next(), before.lines().next(), "^t4 as before the break");
    assert!(before.contains("41m of 60m") && !before.contains("paused"), "{before}");
}

/// **Deleting `.tm/state.json` changes nothing** (D42, P149): after the d17 break, the cache is rebuilt from the log —
/// `^t4` running, unpaused, no break — and `tm now` reads the same.
#[test]
fn a_d152_break_survives_the_cache_deletion_p149() {
    let tm = d17_tree();
    tm.ok_at(&at("10:20"), &["break", "10m"]);
    let before = now_at(&tm, "10:55");
    std::fs::remove_file(tm.plan.join(".tm/state.json")).expect("remove the cache");
    assert_eq!(now_at(&tm, "10:55"), before);
    let s = tm.state();
    assert!(s["break"].is_null() && s["active"]["paused"] == false, "{s}");
}

/// **The later `stop` writes the estimate from the netted minutes, and the later `done` logs them** (P149, D95): after
/// the d17 break, `tm stop` at 11:00 worked 35 minutes (50 since 10:10, less the pause and the break) and leaves `25m`;
/// on a second tree `tm done` at 11:00 logs `actual_min` 35. Until D152 the running break ended at the stop and `^t4`
/// got 10 minutes and `50m` left.
#[test]
fn the_later_stop_and_done_read_the_netted_minutes_p149() {
    let tm = d17_tree();
    tm.ok_at(&at("10:20"), &["break", "10m"]);
    let out = tm.ok_at(&at("11:00"), &["stop"]);
    assert!(out.stdout.contains("stopped ^t4 after 35m · 25m left"), "{}", out.stdout);
    assert_eq!(tm.line(WEEK, "t4"), "- [ ] 3 25m Claude Code drafts tests     @m2 ^t4");
    assert_eq!(review_at(&tm, "11:30"), (95, vec![10]));
    let tm = d17_tree();
    tm.ok_at(&at("10:20"), &["break", "10m"]);
    tm.ok_at(&at("11:00"), &["done"]);
    assert_eq!(tm.last_ev("done")["actual_min"], 35, "{:?}", tm.last_ev("done"));
}

// ---------------------------------------------------------------------------------------------------------------
// D149's reply (the W-54 critic's fourth note)

/// **D149 says "nets" only when the block's minutes fell**: the critic's d19 — `^t1` 09:00, paused 09:50–10:10, done
/// 10:30 (70) — then `tm break --now 09:55 5m`, inside the pause: logged finished (D149), but `^t1` stays 70 and the
/// reply says it nets nothing; `nets` false. Until this repair it said "which it nets".
#[test]
fn a_d149_break_inside_the_blocks_pause_says_it_nets_nothing() {
    let d19 = || {
        let tm = fresh();
        tm.ok_at(&at("09:00"), &["start", "^t1"]);
        tm.ok_at(&at("09:50"), &["pause"]);
        tm.ok_at(&at("10:10"), &["pause"]);
        tm.ok_at(&at("10:30"), &["done"]);
        tm
    };
    let tm = d19();
    assert_eq!(review(&tm).0, 70);
    let out = tm.ok_at(&at("09:55"), &["break", "5m"]);
    assert_eq!(
        out.stdout.trim(),
        "break 5m · 09:55–10:00 · logged finished (it lies inside the block of ^t1 a later `done` or `stop` closed, where \
         ^t1 was not running (a pause, or another break), so it nets nothing, D149)",
        "{}",
        out.stderr
    );
    assert_eq!(review(&tm), (70, vec![5]));
    let tm = d19();
    let v = tm.json_at(&at("09:55"), &["break", "5m"]);
    assert_eq!((v["finished"]["inside_block"].as_str(), v["finished"]["nets"].as_bool()), (Some("t1"), Some(false)), "{v}");
    // Where it does net, it still says so.
    let tm = j_tree();
    let v = tm.json_at(&at("10:30"), &["break", "10m"]);
    assert_eq!(v["finished"]["nets"], true, "{v}");
}

// ---------------------------------------------------------------------------------------------------------------
// The re-time gate's honesty (README gap 5941)

/// **Nested** (`09:20 30m`, `09:30 5m`, then `--now 09:32`): the 09:30 break is drawn nowhere (the 09:20 one covers it),
/// so re-timing it changes nothing — refused by name, nothing written, the review unchanged. Until this repair: "break
/// 09:30–09:35 re-timed to end at 09:32 (D147)" and the review the same (`90`, `[30, 0]`).
#[test]
fn a_retime_inside_a_nested_break_is_refused() {
    let tm = j_tree();
    tm.ok_at(&at("09:20"), &["break", "30m"]);
    tm.ok_at(&at("09:30"), &["break", "5m"]);
    let r0 = review(&tm);
    let said = refused(&tm, "09:32", &["break"]);
    // Restated at the W-54 second repair (README gap 5990): the refusal names each held break by its own span.
    assert!(said.contains("more than one logged break — 09:20–09:50 (inside it), 09:30–09:35 (inside it)") && said.contains("(D147)"), "{said}");
    assert_eq!(review(&tm), r0);
}

/// **Twins at one stamp** (`09:20 20m`, `09:20 10m`, then `--now 09:25`): refused, nothing written. Until this repair:
/// "re-timed to end at 09:25" and the 09:20–09:40 break drawn as before.
#[test]
fn a_retime_inside_twins_at_one_stamp_is_refused() {
    let tm = j_tree();
    tm.ok_at(&at("09:20"), &["break", "20m"]);
    tm.ok_at(&at("09:20"), &["break", "10m"]);
    let r0 = review(&tm);
    let said = refused(&tm, "09:25", &["break"]);
    // Restated at the W-54 second repair (README gap 5990): both breaks named by their own spans.
    assert!(said.contains("more than one logged break") && said.contains("09:20–09:40 (inside it)"), "{said}");
    assert_eq!(review(&tm), r0);
}

/// **Two breaks of one start, the longer chosen** (`10:30 10m`, `10:30 15m`, then `--now 10:35`): the piece drawn at
/// 10:35 is the ten-minute break's, which a re-time of the fifteen-minute one leaves in place — refused. Until this
/// repair: "re-timed to end at 10:35" while the plan still drew `10:30 · break 10m` (to 10:40, not 10:35).
#[test]
fn a_retime_the_shorter_twin_keeps_drawn_is_refused() {
    let tm = j_tree();
    tm.ok_at(&at("10:30"), &["break", "10m"]);
    tm.ok_at(&at("10:30"), &["break", "15m"]);
    let r0 = review(&tm);
    let said = refused(&tm, "10:35", &["break"]);
    // Restated at the W-54 second repair (README gap 5990): the ten-minute break named by its own span.
    assert!(said.contains("10:30–10:40 (inside it)") && said.contains("(D147)"), "{said}");
    assert_eq!(review(&tm), r0);
}

/// **Overlapping** (`10:30 10m`, `10:31 10m`, then `--now 10:33`): the 10:30 break covers 10:33, so re-timing the
/// 10:31 one there leaves it drawn — refused.
#[test]
fn a_retime_inside_an_overlapping_break_is_refused() {
    let tm = j_tree();
    tm.ok_at(&at("10:30"), &["break", "10m"]);
    tm.ok_at(&at("10:31"), &["break", "10m"]);
    let r0 = review(&tm);
    let said = refused(&tm, "10:33", &["break"]);
    // Restated at the W-54 second repair (README gap 5990): the 10:30 break named by its own span.
    assert!(said.contains("10:30–10:40 (inside it)") && said.contains("(D147)"), "{said}");
    assert_eq!(review(&tm), r0);
}

/// **"Already ends here" while another break is drawn across the instant** (`09:20 30m`, `09:25 5m`, then `--now
/// 09:30`): refused — the plan draws a break past 09:30. Until this repair: "break 09:25–09:30 already ends at 09:30 —
/// nothing written (D147)".
#[test]
fn already_ends_here_inside_another_drawn_break_is_refused() {
    let tm = j_tree();
    tm.ok_at(&at("09:20"), &["break", "30m"]);
    tm.ok_at(&at("09:25"), &["break", "5m"]);
    let said = refused(&tm, "09:30", &["break"]);
    // Restated at the W-54 second repair (README gap 5990): both breaks named, the 09:25 one at its end.
    assert!(said.contains("09:20–09:50 (inside it), 09:25–09:30 (its end)") && !said.contains("already ends"), "{said}");
}

/// **D150's Out never swallows another logged break** (the owner's shape under D151): `09:20 30m`, re-timed to 09:30,
/// `09:35 5m`, then `--now 09:45` — the 09:20 break's widest end is its own 09:50, but re-timing it out to 09:45 would
/// run across the 09:35 break: refused, naming it; nothing written. Until this repair: "re-timed out to end at 09:45
/// (D150)", the 09:35 break drawn 0 (`95`, `[25, 0]`).
#[test]
fn a_retime_out_across_another_logged_break_is_refused() {
    let tm = j_tree();
    tm.ok_at(&at("09:20"), &["break", "30m"]);
    tm.ok_at(&at("09:30"), &["break"]);
    tm.ok_at(&at("09:35"), &["break", "5m"]);
    assert_eq!(review(&tm), (105, vec![10, 5]));
    let said = refused(&tm, "09:45", &["break"]);
    assert!(
        // Restated at the W-54 second repair (README gap 5994): the break in the way named by its own span, not by a
        // drawn piece's start read as a stamp.
        said.contains("would re-time the break 09:20–09:30 out across the break drawn 09:35–09:40 (logged 09:35–09:40)")
            && said.contains("D150"),
        "{said}"
    );
    assert_eq!(review(&tm), (105, vec![10, 5]));
    // Before the other break, the re-time out still goes (D150's arm stands).
    let out = tm.ok_at(&at("09:33"), &["break"]);
    assert!(out.stdout.contains("re-timed out to end at 09:33 (D150)"), "{}{}", out.stdout, out.stderr);
    let (block, mut b) = review(&tm);
    b.sort_unstable();
    assert_eq!((block, b), (102, vec![5, 13]), "the 09:20 break thirteen, the 09:35 one five (the records' order is the kernel's)");
}

/// **The other direction (§5.8): a head another break clipped still re-times** — `09:20 10m`, `09:25 10m`, then
/// `--now 09:33`: the 09:25 break is drawn 09:30–09:35 (its own piece, ending at its own end), so the re-time moves the
/// drawn end to 09:33 (`107`, `[10, 3]`, the plan `09:30 · break 3m`). A guard reading "the drawn span is the break's
/// whole span" would refuse it.
///
/// *Ignored from the W-54 repair land to the W-54 second repair's land* (README gap 5962): track K's old filter
/// (`Replay.otherMeets`, gap 5925) omitted from the finished-break fact every break another held break overlaps at all,
/// so the verb refused at 09:33 by name — though the re-time would move the drawn piece. The second repair's fact lists
/// a break whose drawn piece no other break meets (`Replay.ownDrawn`, gap 5970) — the 09:25 break's 09:30–09:35 — and
/// the row runs again.
#[test]
fn a_retime_of_a_head_clipped_break_still_goes() {
    let tm = j_tree();
    tm.ok_at(&at("09:20"), &["break", "10m"]);
    tm.ok_at(&at("09:25"), &["break", "10m"]);
    let out = tm.ok_at(&at("09:33"), &["break"]);
    assert!(out.stdout.contains("break 09:25–09:35 re-timed to end at 09:33 (D147)"), "{}{}", out.stdout, out.stderr);
    assert_eq!(review(&tm), (107, vec![10, 3]));
    has_row(&rows(&tm), "09:30 · break 3m");
}

// ---------------------------------------------------------------------------------------------------------------
// The gate's arm order through the binary (the W-54 auditor's missing row; the critic's d13)

/// **Inside a finished break before D150's Out of another** — `09:20 30m` re-timed to 09:30 (its widest end 09:50),
/// `09:35 10m`, then `--now 09:40`: inside the 09:35 break (D147) and inside the 09:20 break's widest span (D150); D147
/// comes first, so the 09:35 break is re-timed to 09:40 and the 09:20 one keeps its end (`105`, `[10, 5]`). A plant
/// putting Out before Inside fails here, not only in the unit test.
#[test]
fn inside_a_finished_break_comes_before_d150s_out() {
    let tm = j_tree();
    tm.ok_at(&at("09:20"), &["break", "30m"]);
    tm.ok_at(&at("09:30"), &["break"]);
    tm.ok_at(&at("09:35"), &["break", "10m"]);
    let out = tm.ok_at(&at("09:40"), &["break"]);
    assert!(out.stdout.contains("break 09:35–09:45 re-timed to end at 09:40 (D147)"), "{}{}", out.stdout, out.stderr);
    assert_eq!(review(&tm), (105, vec![10, 5]));
    let r = rows(&tm);
    has_row(&r, "09:20 · break 10m");
    has_row(&r, "09:35 · break 5m");
}

/// **At a finished break's end before D150's Out of another** (the critic's d13, the campaign's call, revisable):
/// `09:20 30m` re-timed to 09:30, `09:40 5m`, then `--now 09:45` — the 09:40 break already ends there, nothing written,
/// and the 09:20 break is not re-timed out.
#[test]
fn at_a_finished_breaks_end_comes_before_d150s_out() {
    let tm = j_tree();
    tm.ok_at(&at("09:20"), &["break", "30m"]);
    tm.ok_at(&at("09:30"), &["break"]);
    tm.ok_at(&at("09:40"), &["break", "5m"]);
    let log0 = tm.read(".tm/log.jsonl");
    let out = tm.ok_at(&at("09:45"), &["break"]);
    assert_eq!(out.stdout.trim(), "break 09:40–09:45 already ends at 09:45 — nothing written (D147)", "{}", out.stderr);
    assert_eq!(tm.read(".tm/log.jsonl"), log0);
    assert_eq!(review(&tm), (105, vec![10, 5]));
}

// ---------------------------------------------------------------------------------------------------------------
// D151 (parity P148 restated) — track K's item 2; un-ignored at the W-54 repair land

/// **The critic's d6: a stated end is not re-timed out to D129's far end** (D151). `^t1` 09:00–10:00, `^t4`
/// 13:00–14:00; `tm break --now 09:30` (D129 ends it at 13:00), `--now 09:40` (D141 ends it: `110`, `[10]`), then `--now
/// 11:00` begins a NEW break (D129 ends it at 13:00) — the ten-minute break kept, `^t1` still sixty. On 418e5d5 the
/// 09:30 break was re-timed out to 11:00 (`90`, `[90]`).
#[test]
fn a_stated_end_is_not_retimed_out_to_d129s_far_end_p148() {
    let tm = fresh();
    tm.ok_at(&at("09:00"), &["start", "^t1"]);
    tm.ok_at(&at("10:00"), &["done"]);
    tm.ok_at(&at("13:00"), &["start", "^t4"]);
    tm.ok_at(&at("14:00"), &["done"]);
    tm.ok_at(&at("09:30"), &["break"]);
    tm.ok_at(&at("09:40"), &["break"]);
    assert_eq!(review_at(&tm, "14:30"), (110, vec![10]));
    let out = tm.ok_at(&at("11:00"), &["break"]);
    let said = format!("{}{}", out.stdout, out.stderr);
    assert!(said.contains("began at 11:00 ended at 13:00") && !said.contains("(D150)"), "{said}");
    assert_eq!(breaks(&tm).last().and_then(|e| e["ev"].as_str()), Some("break_start"));
    assert_eq!(review_at(&tm, "14:30"), (110, vec![10, 120]));
}

/// **The critic's d14: a D146 break is not swallowed** (D151). On the J day `tm break --now 09:30` (D129 ends it at
/// 10:10), `--now 09:40 5m` (D146: ended at 09:40, a five-minute break logged from it), then `--now 09:50` begins a
/// new break D129 ends at 10:10 — the five-minute break kept (`95`, `[10, 5, 20]`). On 418e5d5 the 09:30 break was
/// re-timed out to 09:50 across it (`100`, `[20, 0]`); on this repair's host alone it is refused by name (gap 5941's
/// Out guard), since the kernel still holds D129's end as the widest.
#[test]
fn a_d146_break_is_not_swallowed_by_a_retime_out_p148() {
    let tm = j_tree();
    tm.ok_at(&at("09:30"), &["break"]);
    tm.ok_at(&at("09:40"), &["break", "5m"]);
    assert_eq!(review(&tm), (105, vec![10, 5]));
    let out = tm.ok_at(&at("09:50"), &["break"]);
    let said = format!("{}{}", out.stdout, out.stderr);
    assert!(said.contains("began at 09:50 ended at 10:10") && !said.contains("(D150)"), "{said}");
    assert_eq!(review(&tm), (95, vec![10, 5, 20]));
}

/// **While a break runs too** (README gap 5942, lifted at the W-54 repair's land once D145 is in): with `^t4` running
/// and a break running since 10:30, `tm break --now 10:20 5m` is logged finished as one plain `break` line — the block
/// netted by its five minutes and still paused by the running break, which keeps running (D145, `Replay.brkPark`).
/// Until the land this keystroke kept gap 5896's refusal, because the kernel's `break` arm cleared the running break.
#[test]
fn a_d152_break_is_logged_finished_while_a_break_runs() {
    let tm = running_t4();
    tm.ok_at(&at("10:30"), &["break"]);
    let out = tm.ok_at(&at("10:20"), &["break", "5m"]);
    assert!(out.stdout.contains("logged finished") && out.stdout.contains("D152"), "{}", out.stdout);
    let evs: Vec<_> = breaks(&tm).iter().map(|e| e["ev"].as_str().unwrap_or_default().to_string()).collect();
    assert_eq!(evs, ["break_start", "break"], "one break_start, the finished line");
    let now = now_at(&tm, "10:40");
    assert!(now.contains("15m of 60m · paused") && now.contains("on break since 10:30 · 10m of 20m"), "{now}");
    tm.ok_at(&at("10:40"), &["break"]);
    let out = tm.ok_at(&at("11:10"), &["stop"]);
    assert!(out.stdout.contains("after 45m"), "{}", out.stdout);
    assert_eq!(review_at(&tm, "11:20"), (105, vec![5, 10]));
}
