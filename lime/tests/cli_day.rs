//! §13's clock verbs against a temp `plan/` (§17 M5).
//!
//! One test per verb: the exit code, the files it changed (read back), the
//! `.tm/log.jsonl` line it appended (§10.1), the `.tm/state.json` field it
//! set (§10.2) and an `insta` snapshot of the `--json` schema.

mod cli_common;

use cli_common::{scrub, Lime, NOW};

#[test]
fn wake_starts_the_day_and_logs_it() {
    let lime = Lime::new();
    let out = lime.run(&["wake", "06:05", "--slept", "8h10m", "--onset", "25m"]);
    assert_eq!(out.code, 0, "{}", out.stderr);

    assert_eq!(lime.state()["wake"], "06:05");
    assert_eq!(lime.state()["date"], "2026-09-07");
    let last = lime.last();
    assert_eq!(last["ev"], "wake");
    assert_eq!(last["slept_min"], 490);
    assert_eq!(last["onset_min"], 25);
    // §10.1: `t` is the wake time, not the moment the command ran.
    assert_eq!(last["t"], "2026-09-07T06:05:00-05:00");

    let lime = Lime::new();
    insta::assert_json_snapshot!(
        "wake_json",
        lime.json(&["wake", "06:05", "--slept", "8h10m"])
    );
}

#[test]
fn arrive_computes_window_and_budget_and_plans() {
    let lime = Lime::new();
    lime.ok(&["wake", "06:05", "--slept", "8h10m"]);
    let out = lime.run(&["arrive", "lounge"]);
    assert_eq!(out.code, 0, "{}", out.stderr);

    // §8.1: end = min(arrival + 8h, 19:00) + walls inside; budget = 6.
    let state = lime.state();
    assert_eq!(state["window"][0], "09:00");
    assert_eq!(state["window"][1], "18:00");
    assert_eq!(state["budget"], 6);
    assert_eq!(state["loc"], "lounge");
    assert_eq!(state["arrival"], "09:00");

    let events = lime.events();
    assert!(events.contains(&"arrive".to_string()), "{events:?}");
    assert!(events.contains(&"plan".to_string()), "{events:?}");

    // The plan was written where §4.3 says.
    assert!(lime.read("day/2026-09-07.md").contains("<!-- tm:plan start"));
    assert!(lime.exists("day/2026-09-07.svg"));
    // The block starts as they stood at arrival (§12.1's ghost row).
    assert!(lime.exists(".tm/arrival_plan.json"));

    let mut json = lime.json_at("2026-09-07T09:30:00-05:00", &["arrive", "home"]);
    scrub(&mut json, "plan_hash", "[hash]");
    insta::assert_json_snapshot!("arrive_json", json);
}

#[test]
fn start_marks_the_line_active_and_logs_energy() {
    let lime = Lime::new();
    lime.ok(&["wake", "06:05", "--slept", "8h10m"]);
    lime.ok(&["arrive", "lounge"]);
    let out = lime.run(&["start", "^t4", "--energy", "4"]);
    assert_eq!(out.code, 0, "{}", out.stderr);

    assert!(lime.line("week/2026-W37.md", "t4").starts_with("- [>]"));
    let last = lime.last();
    assert_eq!(last["ev"], "start");
    assert_eq!(last["id"], "t4");
    assert_eq!(last["rep"], 4);
    assert_eq!(lime.state()["active"]["id"], "t4");
    assert_eq!(lime.state()["active"]["started"], "09:00");

    let lime = Lime::new();
    lime.ok(&["wake", "06:05", "--slept", "8h10m"]);
    insta::assert_json_snapshot!("start_json", lime.json(&["start", "^t4", "--energy", "4"]));
}

#[test]
fn done_closes_the_block_and_the_line() {
    let lime = Lime::new();
    lime.ok(&["wake", "06:05", "--slept", "8h10m"]);
    lime.ok(&["start", "^t4", "--energy", "4"]);
    let out = lime.run_at("2026-09-07T10:00:00-05:00", &["done", "--went", "1"]);
    assert_eq!(out.code, 0, "{}", out.stderr);

    assert!(lime.line("week/2026-W37.md", "t4").starts_with("- [x]"));
    let last = lime.last();
    assert_eq!(last["ev"], "done");
    assert_eq!(last["id"], "t4");
    assert_eq!(last["actual_min"], 60);
    assert_eq!(last["went"], 1);
    assert_eq!(lime.state()["active"], serde_json::Value::Null);

    insta::assert_json_snapshot!(
        "done_json",
        {
            let lime2 = Lime::new();
            lime2.ok(&["wake", "06:05", "--slept", "8h10m"]);
            lime2.ok(&["start", "^t4", "--energy", "4"]);
            lime2.json_at("2026-09-07T10:00:00-05:00", &["done"])
        }
    );
}

#[test]
fn done_partial_keeps_the_line_open_with_a_remainder() {
    let lime = Lime::new();
    lime.ok(&["wake", "06:05", "--slept", "8h10m"]);
    lime.ok(&["start", "^t3", "--energy", "4"]);
    let json = lime.json_at("2026-09-07T09:30:00-05:00", &["done", "--partial"]);
    assert_eq!(json["partial"], true);

    // ^t3 is `- [>] 4 1b …` since the owner's D127 (parity P126): 60 remaining − 30 worked = 30m
    // left, written in the one slot `remaining` reads (D62) — the line carries one estimate.
    let line = lime.line("week/2026-W37.md", "t3");
    assert_eq!(line, "- [ ] 4 30m Exercises 5.3–5.5            @m1 ^t3");
    assert_eq!(lime.last()["partial"], true);

    // D56's case stays tested: on a hand-typed `- [>] 4 2b … est:1b` the slot is the `est:` token.
    let two = Lime::with_two_estimate_t3();
    two.ok(&["wake", "06:05", "--slept", "8h10m"]);
    two.ok(&["start", "^t3", "--energy", "4"]);
    two.json_at("2026-09-07T09:30:00-05:00", &["done", "--partial"]);
    let line = two.line("week/2026-W37.md", "t3");
    assert!(line.starts_with("- [ ] 4 2b"), "{line}");
    assert!(line.contains("est:30m"), "{line}");
}

#[test]
fn done_with_an_id_and_no_block_is_retro() {
    let lime = Lime::new();
    let json = lime.json(&["done", "^t1"]);
    assert_eq!(json["actual_min"], 0);
    assert!(lime.line("week/2026-W37.md", "t1").starts_with("- [x]"));
    assert_eq!(lime.last()["ev"], "done");
    assert_eq!(lime.last()["actual_min"], 0);
}

/// **The owner's D62 (W-36 track T, a registered divergence) — a behaviour row.** `^t4` is
/// `- [ ] 3 1b Claude Code drafts tests @m2 ^t4`: its one estimate is the
/// LEADING one. Fork 4748911's `tm extend` appended `est:2b` beside it, so the
/// line carried `1b` and `est:2b` — two estimates, the row printing one and the
/// planner reading the other (README gap 2926), and this test pinned exactly
/// that. D56's one-estimate rule reaches `lime extend` now: the kernel's `est` op
/// rewrites the leading estimate in place, as typed, and writes no token.
#[test]
fn extend_adds_a_block_to_the_estimate() {
    let lime = Lime::new();
    lime.ok(&["wake", "06:05", "--slept", "8h10m"]);
    lime.ok(&["start", "^t4", "--energy", "4"]);
    let json = lime.json(&["extend", "1b"]);
    assert_eq!(json["by_min"], 60);
    assert_eq!(json["est_min"], 120);
    let line = lime.line("week/2026-W37.md", "t4");
    assert_eq!(
        line, "- [>] 3 2b Claude Code drafts tests     @m2 ^t4",
        "one estimate, the leading one, rewritten in place as typed (D62)"
    );
    assert!(!line.contains("est:"), "no second estimate beside the leading one: {line}");
    assert_eq!(lime.last()["ev"], "extend");
    assert_eq!(lime.last()["by_min"], 60);
    assert_eq!(lime.state()["active"]["est_min"], 120);
    insta::assert_json_snapshot!("extend_json", json);
}

/// **D62's second behaviour row** (W-36 track T): fork `tm stop` wrote
/// `est:40m` beside `^t4`'s leading `1b`; the remainder now replaces the
/// leading estimate, as typed (`40m`), and the line carries one estimate.
#[test]
fn stop_writes_the_remaining_estimate_back() {
    let lime = Lime::new();
    lime.ok(&["wake", "06:05", "--slept", "8h10m"]);
    lime.ok(&["start", "^t4", "--energy", "4"]);
    let json = lime.json_at("2026-09-07T09:20:00-05:00", &["stop"]);
    assert_eq!(json["worked_min"], 20);
    assert_eq!(json["remaining_min"], 40);

    let line = lime.line("week/2026-W37.md", "t4");
    assert_eq!(
        line, "- [ ] 3 40m Claude Code drafts tests     @m2 ^t4",
        "the box moved and the leading estimate is the remainder, one estimate (D62)"
    );
    assert!(!line.contains("est:"), "{line}");
    assert_eq!(lime.last()["ev"], "stop");
    assert_eq!(lime.last()["remaining_min"], 40);
    assert_eq!(lime.state()["active"], serde_json::Value::Null);
    insta::assert_json_snapshot!("stop_json", json);
}

#[test]
fn break_starts_then_ends_with_its_actual_length() {
    let lime = Lime::new();
    let start = lime.json(&["break", "20m", "--where", "walk"]);
    assert_eq!(start["action"], "started");
    assert_eq!(lime.state()["break"]["planned_min"], 20);
    assert_eq!(lime.state()["break"]["where"], "walk");

    let end = lime.json_at("2026-09-07T09:25:00-05:00", &["break"]);
    assert_eq!(end["action"], "ended");
    assert_eq!(end["actual_min"], 25);
    let last = lime.last();
    assert_eq!(last["ev"], "break");
    assert_eq!(last["planned_min"], 20);
    assert_eq!(last["actual_min"], 25);
    assert_eq!(last["where"], "walk");
    // §10.1: `t` is the break's start.
    assert_eq!(last["t"], "2026-09-07T09:00:00-05:00");
    assert_eq!(lime.state()["break"], serde_json::Value::Null);
    insta::assert_json_snapshot!("break_json", end);
}

#[test]
fn interrupt_and_resume_account_for_the_lost_minutes() {
    let lime = Lime::new();
    lime.ok(&["wake", "06:05", "--slept", "8h10m"]);
    lime.ok(&["start", "^t4", "--energy", "4"]);
    let i = lime.json_at("2026-09-07T09:10:00-05:00", &["interrupt"]);
    assert_eq!(i["id"], "t4");
    assert_eq!(lime.state()["interrupt"]["id"], "t4");
    assert_eq!(lime.state()["active"]["paused"], true);
    assert_eq!(lime.last()["ev"], "interrupt");

    let r = lime.json_at("2026-09-07T10:05:00-05:00", &["resume"]);
    assert_eq!(r["lost_min"], 55);
    assert_eq!(lime.state()["interrupt"], serde_json::Value::Null);
    assert_eq!(lime.state()["active"]["paused"], false);
    let events = lime.events();
    assert!(events.contains(&"resume".to_string()), "{events:?}");
    insta::assert_json_snapshot!("resume_json", r);

    // §9: "segments after t_r shift; tail drops". §10.1's `resume{dropped}`
    // names what the lost minutes cost — each item once, however many blocks
    // it held (the morning plan gives `^m4` three).
    let lime = Lime::new();
    lime.ok(&["arrive", "lounge"]);
    lime.ok_at("2026-09-07T09:30:00-05:00", &["interrupt"]);
    let r = lime.json_at("2026-09-07T15:30:00-05:00", &["resume"]);
    let dropped: Vec<&str> = r["dropped"]
        .as_array()
        .expect("dropped")
        .iter()
        .filter_map(|v| v.as_str())
        .collect();
    assert!(!dropped.is_empty(), "six hours cost the day its tail: {r}");
    let mut once = dropped.clone();
    once.sort_unstable();
    once.dedup();
    assert_eq!(dropped.len(), once.len(), "each item once: {r}");
    assert_eq!(lime.last_ev("resume")["dropped"], r["dropped"]);
}

#[test]
fn pause_toggles_the_timer() {
    let lime = Lime::new();
    lime.ok(&["wake", "06:05", "--slept", "8h10m"]);
    lime.ok(&["start", "^t4", "--energy", "4"]);
    let p = lime.json(&["pause"]);
    assert_eq!(p["paused"], true);
    assert_eq!(lime.last()["ev"], "pause");
    assert_eq!(lime.state()["active"]["paused"], true);

    let u = lime.json_at("2026-09-07T09:05:00-05:00", &["pause"]);
    assert_eq!(u["paused"], false);
    assert_eq!(lime.last()["ev"], "unpause");
    insta::assert_json_snapshot!("pause_json", p);
}

#[test]
fn energy_logs_a_report_against_the_prediction() {
    let lime = Lime::new();
    lime.ok(&["wake", "06:05", "--slept", "8h10m"]);
    lime.ok(&["arrive", "lounge"]);
    let json = lime.json(&["energy", "3", "--at", "10:30"]);
    assert_eq!(json["rep"], 3);
    assert_eq!(json["at"], "10:30");
    // A non-zero delta re-plans (§8.5), so a `plan` entry follows the report;
    // assert on the `energy` entry itself rather than on the last line.
    let last = lime.last_ev("energy");
    assert_eq!(last["rep"], 3);
    assert_eq!(last["t"], "2026-09-07T10:30:00-05:00");
    assert!(
        lime.events().contains(&"energy".to_string()),
        "the report is logged: {:?}",
        lime.events()
    );
    insta::assert_json_snapshot!("energy_json", json);
}

#[test]
fn energy_above_five_is_an_error() {
    let lime = Lime::new();
    let out = lime.run(&["energy", "9"]);
    assert_eq!(out.code, 1);
    assert!(out.stderr.contains("0–5"), "{}", out.stderr);
}

/// `lime start --help` says `--energy` is 0–5, the same §8.5 scale `lime energy`
/// takes and rejects out of range. `start` used to filter an out-of-range
/// value away instead: `--energy 9` fell back to the prediction, logged no
/// `rep` at all, and said nothing — the report the user typed, thrown away.
#[test]
fn start_refuses_an_energy_outside_the_scale() {
    let lime = Lime::new();
    let out = lime.run(&["start", "^t4", "--energy", "9"]);
    assert_eq!(out.code, 1, "{}{}", out.stdout, out.stderr);
    assert!(out.stderr.contains("0–5"), "{}", out.stderr);

    // Refused before anything ran: the line is untouched and no block opened.
    assert!(lime.line("week/2026-W37.md", "t4").starts_with("- [ ]"));
    assert!(lime.events().is_empty(), "{:?}", lime.events());

    // The scale itself is unchanged, both ends of it.
    let lime = Lime::new();
    lime.ok(&["start", "^t4", "--energy", "0"]);
    assert_eq!(lime.last_ev("start")["rep"], 0);
    let lime = Lime::new();
    lime.ok(&["start", "^t4", "--energy", "5"]);
    assert_eq!(lime.last_ev("start")["rep"], 5);
}

/// §10.1's `went` is 1, 2 or 3 (§8.5), which is what `lime done --help` says.
/// An out-of-range value used to be filtered out of the log event but *not*
/// out of the day file's `## Log` note, so the two records of one `done`
/// disagreed: `went=7` in `day/2026-09-07.md`, no `went` at all in
/// `.tm/log.jsonl`, and §8.5 never saw the report.
#[test]
fn done_refuses_a_went_outside_the_scale() {
    let lime = Lime::new();
    lime.ok(&["start", "^t4", "--energy", "4"]);
    let out = lime.run_at("2026-09-07T10:00:00-05:00", &["done", "--went", "7"]);
    assert_eq!(out.code, 1, "{}{}", out.stdout, out.stderr);
    assert!(out.stderr.contains("--went is 1"), "{}", out.stderr);

    // Refused before anything ran: neither record mentions it, and the block
    // is still running.
    assert!(!lime.read("day/2026-09-07.md").contains("went=7"));
    assert_eq!(lime.last_ev("start")["ev"], "start");
    assert_eq!(lime.state()["active"]["id"], "t4");

    // The scale itself still works, at both ends.
    for went in ["1", "3"] {
        let lime = Lime::new();
        lime.ok(&["start", "^t4", "--energy", "4"]);
        let json = lime.json_at("2026-09-07T10:00:00-05:00", &["done", "--went", went]);
        assert_eq!(json["id"], "t4");
        assert_eq!(lime.last_ev("done")["went"].to_string(), went);
        assert!(lime.read("day/2026-09-07.md").contains(&format!("went={went}")));
    }
}

#[test]
fn idle_attributes_the_gap() {
    let lime = Lime::new();
    lime.ok(&["wake", "06:05", "--slept", "8h10m"]);
    let json = lime.json_at("2026-09-07T09:14:00-05:00", &["idle", "l"]);
    assert_eq!(json["attributed"], "leak");
    // The gap runs from the last logged event (the wake at 06:05).
    assert_eq!(json["min"], 189);
    let last = lime.last();
    assert_eq!(last["ev"], "idle");
    assert_eq!(last["attributed"], "leak");
    insta::assert_json_snapshot!("idle_json", lime.json(&["idle", "b", "--min", "14"]));
}

#[test]
fn ending_a_break_unpauses_the_block() {
    // §10.2's `active.paused`: the break paused the block, ending it must
    // clear the flag — otherwise the next `lime pause` unpauses.
    let lime = Lime::new();
    lime.ok(&["wake", "06:05", "--slept", "8h10m"]);
    lime.ok(&["start", "^t4", "--energy", "4"]);
    lime.ok_at("2026-09-07T10:00:00-05:00", &["break", "20m", "--where", "walk"]);
    assert_eq!(lime.state()["active"]["paused"], true);

    lime.ok_at("2026-09-07T10:22:00-05:00", &["break"]);
    assert_eq!(lime.state()["active"]["paused"], false);
    assert!(!lime.run_at("2026-09-07T10:23:00-05:00", &["now"]).stdout.contains("paused"));

    // …so `lime pause` pauses.
    let p = lime.json_at("2026-09-07T10:24:00-05:00", &["pause"]);
    assert_eq!(p["paused"], true);
}

#[test]
fn stop_ends_a_running_break() {
    // §11's break integrity needs every break in the log; §10.1's `break`
    // entry is written when the break ends, so `lime stop` has to end it.
    let lime = Lime::new();
    lime.ok(&["wake", "06:05", "--slept", "8h10m"]);
    lime.ok(&["start", "^t4", "--energy", "4"]);
    lime.ok_at("2026-09-07T10:00:00-05:00", &["break", "20m"]);
    lime.ok_at("2026-09-07T10:30:00-05:00", &["stop"]);

    assert_eq!(lime.state()["break"], serde_json::Value::Null);
    let br = lime
        .log()
        .into_iter()
        .find(|e| e["ev"] == "break")
        .expect("the break reached the log");
    assert_eq!(br["planned_min"], 20);
    assert_eq!(br["actual_min"], 30);
}

#[test]
fn worked_minutes_exclude_interrupted_and_paused_time() {
    // §9: an interruption pauses the block and its minutes are logged once,
    // as `resume{lost_min}`. Counting them in `done.actual_min` too would
    // inflate §8.5's duration multiplier and §11's ledgers.
    let lime = Lime::new();
    lime.ok(&["wake", "06:05", "--slept", "8h10m"]);
    lime.ok(&["start", "^t4", "--energy", "4"]);
    lime.ok_at("2026-09-07T10:00:00-05:00", &["interrupt"]);
    lime.ok_at("2026-09-07T10:30:00-05:00", &["resume"]);
    let json = lime.json_at("2026-09-07T11:00:00-05:00", &["done"]);
    // 09:00 → 11:00 is 120 minutes, 30 of them interrupted.
    assert_eq!(json["actual_min"], 90);
    let done = lime
        .log()
        .into_iter()
        .find(|e| e["ev"] == "done")
        .expect("a done");
    assert_eq!(done["actual_min"], 90);

    // The same for a pause and for `lime stop`.
    let lime = Lime::new();
    lime.ok(&["wake", "06:05", "--slept", "8h10m"]);
    lime.ok(&["start", "^t4", "--energy", "4"]);
    lime.ok_at("2026-09-07T09:30:00-05:00", &["pause"]);
    lime.ok_at("2026-09-07T09:50:00-05:00", &["pause"]);
    let json = lime.json_at("2026-09-07T10:00:00-05:00", &["stop"]);
    assert_eq!(json["worked_min"], 40);
}

#[test]
fn a_routine_line_is_never_rewritten() {
    // §5.1: "a recurring item never changes its line"; §4.3: in `routines.md`
    // the state is omitted and instances live in the log. A `[x]` there would
    // end the recurrence for good.
    let lime = Lime::new();
    let before = lime.read("routines.md");
    lime.ok(&["start", "lunch", "--energy", "3"]);
    assert_eq!(lime.read("routines.md"), before, "start rewrote routines.md");
    assert_eq!(lime.state()["active"]["id"], "lunch");

    lime.ok_at("2026-09-07T09:40:00-05:00", &["done"]);
    assert_eq!(lime.read("routines.md"), before, "done rewrote routines.md");

    // §10.1: the occurrence is a `routine` event, not a `done{id}`.
    let last = lime.last();
    assert_eq!(last["ev"], "routine");
    assert_eq!(last["item"], "lunch");
    assert_eq!(last["inst"], "2026-09-07");
    assert_eq!(last["status"], "done");
    assert_eq!(last["actual_min"], 40);
    assert!(!lime.events().contains(&"done".to_string()), "{:?}", lime.events());
}

#[test]
fn since_break_min_is_measured_from_the_end_of_the_break() {
    // §10.1's `start{since_break_min}`: `break.t` is when the break *began*
    // (the entry is appended when it ends, carrying `actual_min`), so the
    // working gap starts at `t + actual_min`.
    let lime = Lime::new();
    lime.ok(&["wake", "06:05", "--slept", "8h10m"]);
    lime.ok(&["break", "20m", "--where", "walk"]);
    lime.ok_at("2026-09-07T09:25:00-05:00", &["break"]);
    lime.ok_at("2026-09-07T09:30:00-05:00", &["start", "^t4", "--energy", "4"]);
    let start = lime
        .log()
        .into_iter()
        .find(|e| e["ev"] == "start")
        .expect("a start");
    assert_eq!(start["since_break_min"], 5);

    // With no break all day the gap runs from the first block, not from 0.
    let lime = Lime::new();
    lime.ok(&["wake", "06:05", "--slept", "8h10m"]);
    lime.ok(&["start", "^t4", "--energy", "4"]);
    lime.ok_at("2026-09-07T11:00:00-05:00", &["done"]);
    lime.ok_at("2026-09-07T11:00:00-05:00", &["start", "^t5", "--energy", "4"]);
    let second = lime.last_ev("start");
    assert_eq!(second["since_break_min"], 120);
}

#[test]
fn the_block_machine_survives_a_line_another_writer_removed() {
    // §1.3: three writers, one file set. If the running block's line is gone,
    // `lime done` must still close the block — there is no other way out.
    let lime = Lime::new();
    lime.ok(&["wake", "06:05", "--slept", "8h10m"]);
    lime.ok(&["start", "^t4", "--energy", "4"]);

    let path = lime.plan.join("week/2026-W37.md");
    let text = std::fs::read_to_string(&path).expect("read week");
    let kept: Vec<&str> = text.lines().filter(|l| !l.contains("^t4")).collect();
    std::fs::write(&path, format!("{}\n", kept.join("\n"))).expect("write week");

    let out = lime.run_at("2026-09-07T10:00:00-05:00", &["done"]);
    assert_eq!(out.code, 0, "{}{}", out.stdout, out.stderr);
    assert_eq!(lime.state()["active"], serde_json::Value::Null);
    assert_eq!(lime.last()["ev"], "done");
    assert_eq!(lime.last()["actual_min"], 60);
}

#[test]
fn a_non_zero_energy_delta_replans() {
    // §8.5: "Non-zero δ triggers a replan"; §9's table: "slots re-energised".
    let lime = Lime::new();
    lime.ok(&["wake", "06:05", "--slept", "8h10m"]);
    lime.ok(&["arrive", "lounge"]);
    let plans = lime.events().iter().filter(|e| *e == "plan").count();

    let same = lime.json_at("2026-09-07T10:30:00-05:00", &["energy", "5"]);
    assert_eq!(same["delta"], 0);
    assert_eq!(same["replanned"], false);

    let json = lime.json_at("2026-09-07T10:31:00-05:00", &["energy", "3"]);
    assert_eq!(json["delta"], -2);
    assert_eq!(json["replanned"], true);
    // The plan was rewritten from `now`: §4.3's generated block is re-stamped.
    assert!(
        lime.read("day/2026-09-07.md").contains("<!-- tm:plan start 10:31 -->"),
        "{}",
        lime.read("day/2026-09-07.md")
    );
    assert!(lime.exists(".tm/last_plan.json"));
    // The re-energised slots move the day, so §10.1's `plan` event is appended
    // (a replan that changes nothing does not log one — see the delta-0 case
    // above, which left the count where it was).
    assert_eq!(
        lime.events().iter().filter(|e| *e == "plan").count(),
        plans + 1
    );
}

#[test]
fn the_day_file_carries_the_runtime_front_matter_and_the_log() {
    // §4.3's day file: `wake`, `slept`, `loc`, `window`, `budget` in the
    // front matter and an append-only `## Log`. §14 forbids Claude Code from
    // writing `## Log` and §1.2 gives `emit.rs` only the generated section,
    // so the CLI is the only writer of either.
    let lime = Lime::new();
    lime.ok_at("2026-09-07T08:15:00-05:00", &["wake", "08:15", "--slept", "6h"]);
    lime.ok_at("2026-09-07T08:30:00-05:00", &["arrive", "home"]);
    lime.ok_at("2026-09-07T08:35:00-05:00", &["start", "^t4", "--energy", "4"]);
    lime.ok_at("2026-09-07T09:35:00-05:00", &["done", "--went", "1"]);

    let day = lime.read("day/2026-09-07.md");
    let front: Vec<&str> = day
        .split("---")
        .nth(1)
        .unwrap_or_default()
        .lines()
        .filter(|l| !l.trim().is_empty())
        .collect();
    // §4.3's own order: date, wake, slept, loc, window, budget.
    assert_eq!(
        front,
        [
            "date: 2026-09-07",
            "wake: 08:15",
            "slept: 6h",
            "loc: home",
            "window: 08:30..17:30",
            "budget: 6",
        ],
        "{day}"
    );

    let log = day.split("## Log").nth(1).unwrap_or_default();
    assert!(log.contains("08:15 wake slept=6h"), "{day}");
    assert!(log.contains("08:30 arrive home"), "{day}");
    assert!(log.contains("08:35 start ^t4 pred="), "{day}");
    assert!(log.contains("09:35 done ^t4 60m/60m went=1"), "{day}");

    // A day file the CLI creates has the whole §4.3 skeleton.
    let lime = Lime::new();
    lime.ok_at("2026-09-08T08:30:00-05:00", &["arrive", "lounge"]);
    let day = lime.read("day/2026-09-08.md");
    for section in ["# Pinned", "## Log", "## Notes", "<!-- tm:plan start"] {
        assert!(day.contains(section), "missing {section} in {day}");
    }
}

#[test]
fn starting_a_second_block_is_refused() {
    let lime = Lime::new();
    lime.ok(&["wake", "06:05", "--slept", "8h10m"]);
    lime.ok(&["start", "^t4", "--energy", "4"]);
    let out = lime.run(&["start", "^t5"]);
    assert_eq!(out.code, 1);
    assert!(out.stderr.contains("running"), "{}", out.stderr);
}

#[test]
fn an_unknown_id_is_an_error() {
    let lime = Lime::new();
    let out = lime.run_at(NOW, &["start", "^zzzz"]);
    assert_eq!(out.code, 1);
    assert!(out.stderr.contains("no such item"), "{}", out.stderr);
}

#[test]
fn an_append_after_a_torn_line_starts_a_new_line() {
    // Parity P19 (G9's writer half, design §14.3 row R10): a log whose last
    // line has no final `\n` (a write cut short, a hand edit) used to have the
    // next event glued onto the fragment, so both lines were lost to every
    // reader. The append now writes the `\n` first.
    let lime = Lime::new();
    lime.ok(&["wake", "06:05", "--slept", "8h10m"]);
    let path = lime.plan.join(".tm/log.jsonl");
    let mut text = std::fs::read_to_string(&path).expect("read log");
    let fragment = r#"{"t":"2026-09-07T06:30:00-05:00","ev":"no"#;
    text.push_str(fragment);
    std::fs::write(&path, &text).expect("write log");

    lime.ok(&["start", "^t4", "--energy", "4"]);
    let after = lime.read(".tm/log.jsonl");
    assert!(after.ends_with('\n'), "every appended line is terminated");
    let lines: Vec<&str> = after.strip_suffix('\n').unwrap_or(&after).split('\n').collect();
    let at = lines.iter().position(|l| *l == fragment).expect("the fragment stays a line of its own");
    let appended: Vec<serde_json::Value> = lines[at + 1..]
        .iter()
        .map(|l| serde_json::from_str(l).expect("each appended line is JSON on its own"))
        .collect();
    assert!(appended.iter().any(|e| e["ev"] == "start" && e["id"] == "t4"), "{appended:?}");
    // The reader sees the start (and not the fragment): `lime log --json`.
    assert_eq!(lime.state()["active"]["id"], "t4");
    let shown = lime.json(&["log", "--item", "^t4"]);
    let shown = shown["entries"].as_array().expect("entries").clone();
    assert!(shown.iter().any(|e| e["ev"] == "start" && e["id"] == "t4"), "{shown:?}");
    lime.ok_at("2026-09-07T09:20:00-05:00", &["stop"]);
    assert_eq!(lime.state()["active"], serde_json::Value::Null, "the stop found the block the start opened");
    let parsed: Vec<serde_json::Value> =
        lime.read(".tm/log.jsonl").lines().filter_map(|l| serde_json::from_str(l).ok()).collect();
    assert_eq!(parsed.last().map(|e| e["ev"].clone()), Some(serde_json::json!("stop")));

    // A log that already ends in `\n` gains no blank line.
    let before = lime.read(".tm/log.jsonl");
    lime.ok_at("2026-09-07T09:25:00-05:00", &["start", "^t4", "--energy", "4"]);
    let now = lime.read(".tm/log.jsonl");
    assert!(now.starts_with(&before) && !now[before.len()..].starts_with('\n'), "no repair on a whole line");
}

/// Break `^m1`'s `@parent` so the kernel refuses the whole tree
/// (`itemCheck`/`danglingParent`, the owner's D6). Returns the text as it was.
fn break_tree(lime: &Lime) -> String {
    let path = lime.plan.join("week/2026-W37.md");
    let text = std::fs::read_to_string(&path).expect("read week");
    let broken = text.replace("@O1 ^m1", "@O9 ^m1");
    assert_ne!(broken, text, "the fixture no longer carries `@O1 ^m1`");
    std::fs::write(&path, &broken).expect("write week");
    text
}

fn restore_tree(lime: &Lime, text: &str) {
    std::fs::write(lime.plan.join("week/2026-W37.md"), text).expect("restore week");
}

/// **A tree the kernel refuses stops `arrive`, `resume` and `energy` before
/// they write, and the same verb runs once the tree is fixed** — gap 115,
/// closed here. These three write `state.json` and the log *before* the
/// planning call that sends the tree, so each used to fail *after* its own
/// write. Driven at `89ead46`, each on a copy of `plan-basic` with a typo'd
/// `@parent`: `arrive` left an `arrive` line and a written `state.json`,
/// `energy 3` left an `energy` line, and `resume` left `state.json` with the
/// interruption **cleared** and no log line naming it — the interruption was
/// simply lost. Both orders are checked: refused writes nothing, fixed runs.
#[test]
fn a_refused_tree_stops_the_writing_verbs_before_they_write() {
    // (a) `arrive`, from a fresh tree: it wrote both the log line and the state.
    {
        let lime = Lime::new();
        let text = break_tree(&lime);
        let before = lime.events();
        let out = lime.run(&["arrive", "lounge"]);
        assert_eq!(out.code, 1, "arrive: {}{}", out.stdout, out.stderr);
        assert!(out.stderr.contains("danglingParent"), "arrive: {}", out.stderr);
        assert_eq!(lime.events(), before, "arrive logged on a refused tree");
        assert!(
            !lime.exists(".tm/state.json") || lime.state()["arrival"].is_null(),
            "arrive wrote its arrival on a refused tree"
        );

        restore_tree(&lime, &text);
        let ok = lime.run(&["arrive", "lounge"]);
        assert_eq!(ok.code, 0, "arrive, fixed: {}{}", ok.stdout, ok.stderr);
        assert!(lime.events().contains(&"arrive".to_string()), "arrive did not log once fixed");
        assert_eq!(lime.state()["arrival"], "09:00");
    }

    // (b) `energy`: a non-zero delta replans (§8.5), which is the refused call.
    {
        let lime = Lime::new();
        let text = break_tree(&lime);
        let before = lime.events();
        let out = lime.run(&["energy", "3"]);
        assert_eq!(out.code, 1, "energy: {}{}", out.stdout, out.stderr);
        assert!(out.stderr.contains("danglingParent"), "energy: {}", out.stderr);
        assert_eq!(lime.events(), before, "energy logged on a refused tree");

        restore_tree(&lime, &text);
        let ok = lime.run(&["energy", "3"]);
        assert_eq!(ok.code, 0, "energy, fixed: {}{}", ok.stdout, ok.stderr);
        assert!(lime.events().contains(&"energy".to_string()), "energy did not log once fixed");
    }

    // (c) `resume`: the worst shape — no log line, but the interruption was
    // cleared out of `state.json` by a command that then failed.
    {
        let lime = Lime::new();
        lime.ok(&["arrive", "lounge"]);
        lime.ok(&["start", "^t3"]);
        lime.ok(&["interrupt"]);
        assert!(!lime.state()["interrupt"].is_null(), "the setup left no interruption");
        let state_before = lime.read(".tm/state.json");
        let events_before = lime.events();

        let text = break_tree(&lime);
        let out = lime.run(&["resume"]);
        assert_eq!(out.code, 1, "resume: {}{}", out.stdout, out.stderr);
        assert!(out.stderr.contains("danglingParent"), "resume: {}", out.stderr);
        assert_eq!(lime.events(), events_before, "resume logged on a refused tree");
        assert_eq!(
            lime.read(".tm/state.json"),
            state_before,
            "resume rewrote state.json on a refused tree — the interruption was lost"
        );

        restore_tree(&lime, &text);
        let ok = lime.run(&["resume"]);
        assert_eq!(ok.code, 0, "resume, fixed: {}{}", ok.stdout, ok.stderr);
        assert!(lime.events().contains(&"resume".to_string()), "resume did not log once fixed");
        assert!(lime.state()["interrupt"].is_null(), "the interruption is closed once fixed");
    }
}

/// **One day has ONE window** — the owner's **D45**, README gap **1530**,
/// D9's "a named fact of one reader".
///
/// Two rules existed. The runtime state's window is the day's **last**
/// `arrive` (`lime arrive` overwrites it, and `Ctx::derived_state` rebuilds it
/// that way); `DayReplay::window` is the day's **first**, which is the fork's
/// derivation and `Replay.lean`'s proved C5. `lime plan` and the day file quoted
/// the former, `lime review day` the latter, and **no surface said which**.
///
/// `--at` is §13's own flag and exists precisely so an arrival can be logged
/// out of order. Driven on the shipped binary before the repair, on this
/// fixture: `lime arrive home --at 16:00` then `lime arrive home --at 08:00` left
/// `.tm/state.json`, `lime plan --json` and `day/2026-09-07.md` all saying
/// `08:00..17:00` while `lime review day` said `window 16:00–19:00` — two
/// surfaces of one day, eight hours apart, with nothing to tell a reader which
/// was the answer.
///
/// The bite is asserted first: the two arrivals must disagree, or every line
/// below holds for the wrong reason.
#[test]
fn every_surface_of_one_day_quotes_the_same_window() {
    let lime = Lime::new();
    lime.ok(&["arrive", "home", "--at", "16:00"]);
    lime.ok(&["arrive", "home", "--at", "08:00"]);

    let arrivals: Vec<_> = lime
        .log()
        .into_iter()
        .filter(|e| e["ev"] == "arrive")
        .map(|e| e["window"][0].as_str().unwrap_or_default().to_string())
        .collect();
    assert_eq!(arrivals, vec!["16:00".to_string(), "08:00".to_string()],
        "the two arrivals no longer differ, so this test proves nothing");

    let state = lime.state();
    let want = ["08:00", "17:00"];
    assert_eq!(state["window"][0], want[0], "the cache is not the LAST arrival (D45)");
    assert_eq!(state["window"][1], want[1]);

    let plan = lime.json(&["plan"]);
    assert_eq!(plan["window"][0], want[0], "`lime plan` disagrees with the cache");
    assert_eq!(plan["window"][1], want[1]);

    assert!(
        lime.read("day/2026-09-07.md").contains(&format!("window: {}..{}", want[0], want[1])),
        "the day file disagrees: {}",
        lime.read("day/2026-09-07.md")
    );

    // The one that moved. `DayReview::window` is `NaiveTime`, so `--json`
    // spells it with seconds.
    let review = lime.json(&["review", "day"]);
    assert_eq!(
        review["review"]["window"][0], format!("{}:00", want[0]),
        "`lime review day` quotes a different window from `lime plan` (README gap 1530)"
    );
    assert_eq!(review["review"]["window"][1], format!("{}:00", want[1]));
    assert!(
        lime.run(&["review", "day"]).stdout.contains(&format!("window {}–{}", want[0], want[1])),
        "the rendered review disagrees with its own `--json`"
    );
}

/// The fallback half, so the repair above is not a rule that only ever reads
/// the cache: a review of a day the runtime is **not** about still answers from
/// the replay's own payload, which is the only window the log carries for it.
#[test]
fn a_review_of_another_day_still_reads_the_logs_own_window() {
    let lime = Lime::new();
    lime.ok(&["arrive", "home", "--at", "08:00"]);
    // **Asked on the NEXT day**, where `roll_day` has cleared the runtime's
    // window and `DayExtras::window` is therefore `None`: the answer has to
    // come from `DayReplay::window`, the only window the log carries for a day
    // that is over. A `window_now` that read the runtime alone answers `null`
    // here and loses the field.
    let review = lime.json_at(
        "2026-09-08T09:00:00-05:00",
        &["review", "day", "--date", "2026-09-07"],
    );
    assert_eq!(
        review["review"]["window"][0], "08:00:00",
        "a past day lost its window: {}", review["review"]["window"]
    );
    // And a day the log knows nothing about still has none, so the line above
    // is the fallback firing and not a default.
    let none = lime.json_at(NOW, &["review", "day", "--date", "2026-09-05"]);
    assert!(none["review"]["window"].is_null(), "{}", none["review"]["window"]);
}
