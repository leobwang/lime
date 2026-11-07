//! **`lime start ^id` on the block already running CONTINUES it** — the owner's **D107** (README gap
//! 4892, parity **P110**, W-47 track H), driven through the binary.
//!
//! Fork 4748911 accepted `tm start ^t3` on the running `^t3` and logged a second `start`: the
//! replay closed the first stretch at it, so `lime review day` and the drawn rows counted both
//! stretches, while `lime stop` and `lime done` computed from the second start and wrote `est:` less
//! only that stretch. Gap 4892's two worlds, on the example tree: `start ^t3` at 09:00 and 09:30,
//! `stop` at 09:50 said `after 20m · 40m left` with 50 minutes worked; and "resume after a break"
//! (`start` 09:00, `break` 09:30, `start ^t3` 09:50, `stop` 10:20) wrote `30m left` where 60 were
//! worked — a silently wrong estimate in the user's file.
//!
//! Now the re-start ends a running break if one runs (the one body every verb that ends a break
//! runs, D97's journal line and D101's clause), logs NOTHING else, and says `^t3 is already running
//! since 09:00` — so the estimate `lime stop` writes is the estimate less the minutes `lime review day`
//! counts, in both worlds. Both directions: another id is still refused by name while a block runs.

mod cli_common;

use cli_common::Lime;
use serde_json::Value;

/// `HH:MM` on Monday 2026-09-07, Chicago.
fn at(hhmm: &str) -> String {
    format!("2026-09-07T{hhmm}:00-05:00")
}

/// The example tree (`lime init --example`, §4.3's), untouched.
fn example() -> Lime {
    let lime = Lime::empty();
    assert_eq!(lime.run(&["init", "--example"]).code, 0);
    lime
}

/// The log's lines, as written.
fn log(lime: &Lime) -> Vec<String> {
    lime.read(".tm/log.jsonl").lines().map(str::to_string).collect()
}

/// The `ev` tags of the log, in order.
fn tags(lime: &Lime) -> Vec<String> {
    log(lime)
        .iter()
        .map(|l| {
            let v: Value = serde_json::from_str(l).expect("a log line is JSON");
            v["ev"].as_str().unwrap_or_default().to_string()
        })
        .collect()
}

/// `^t3`'s line in the week file.
fn t3_line(lime: &Lime) -> String {
    lime.read("week/2026-W37.md")
        .lines()
        .find(|l| l.ends_with("^t3"))
        .expect("^t3's line")
        .to_string()
}

/// `lime review day --json`'s minutes worked on the day (§11's energy mix total).
fn reviewed_minutes(lime: &Lime, now: &str) -> u64 {
    let v = lime.json_at(now, &["review", "day"]);
    v["review"]["mix"]["total_min"].as_u64().unwrap_or_else(|| panic!("a reviewed total: {v}"))
}

/// **Gap 4892's first world**: `start ^t3` at 09:00 and again at 09:30, `stop` at 09:50. The
/// re-start says so and logs nothing; the stop counts the fifty minutes the review counts and
/// writes the estimate less them.
#[test]
fn a_restart_of_the_running_block_continues_it_and_the_stop_counts_both_stretches() {
    let lime = example();
    lime.ok_at(&at("09:00"), &["start", "^t3", "--energy", "3"]);
    let lines = log(&lime);
    let again = lime.ok_at(&at("09:30"), &["start", "^t3"]);
    assert_eq!(again.stdout.trim(), "^t3 is already running since 09:00", "{}", again.stdout);
    assert_eq!(log(&lime), lines, "a continuation logs nothing");
    let stop = lime.ok_at(&at("09:50"), &["stop"]);
    assert_eq!(stop.stdout.trim(), "stopped ^t3 after 50m · 10m left", "{}", stop.stdout);
    assert_eq!(tags(&lime), ["start", "stop"], "one block, one start");
    assert_eq!(reviewed_minutes(&lime, &at("09:51")), 50, "the review counts what the stop counted");
    // The leading estimate rewritten in place (D62): the example `^t3` carries one since D127 (P126).
    assert_eq!(t3_line(&lime), "- [ ] 4 10m Exercises 5.3–5.5            @m1 ^t3", "the estimate less the fifty minutes");
}

/// **Gap 4892's second world, "resume after a break"**: `start` 09:00, `break` 09:30, `start ^t3`
/// 09:50, `stop` 10:20. The re-start ends the break — its line, `lime break`'s journal line and
/// clause (D97, D101) — and logs nothing else; the stop counts the sixty minutes the review counts.
#[test]
fn resuming_after_a_break_by_starting_the_block_ends_the_break_and_continues_it() {
    let lime = example();
    lime.ok_at(&at("09:00"), &["start", "^t3", "--energy", "3"]);
    lime.ok_at(&at("09:30"), &["break"]);
    let again = lime.ok_at(&at("09:50"), &["start", "^t3"]);
    assert_eq!(
        again.stdout.trim(),
        "break ended · 20m of 20m · ^t3 is already running since 09:00",
        "{}",
        again.stdout
    );
    assert_eq!(tags(&lime), ["start", "break_start", "break"], "the break's end, and no second start");
    assert!(lime.state()["break"].is_null(), "the break is over: {}", lime.state());
    assert_eq!(lime.state()["active"]["paused"], false, "and the block runs: {}", lime.state());
    let day = lime.read("day/2026-09-07.md");
    assert!(day.contains("\n09:50 break ended 20m/20m\n"), "the break's journal line: {day}");
    assert!(!day.contains("09:50 start"), "no start line for a continuation: {day}");

    let stop = lime.ok_at(&at("10:20"), &["stop"]);
    assert!(stop.stdout.starts_with("stopped ^t3 after 60m · "), "{}", stop.stdout);
    assert_eq!(reviewed_minutes(&lime, &at("10:21")), 60, "the review counts what the stop counted");
    // Sixty of sixty minutes worked: §6.4's floor, not the thirty the fork wrote.
    assert_eq!(t3_line(&lime), "- [ ] 4 5m Exercises 5.3–5.5            @m1 ^t3", "one estimate (D127, P126)");
}

/// **Nothing is written by a continuation with no break running** — not the log, not
/// `.tm/state.json`, not the day file, not the undo stack: every byte of the tree stands.
#[test]
fn a_continuation_with_no_break_running_writes_nothing() {
    let lime = example();
    lime.ok_at(&at("09:00"), &["start", "^t3", "--energy", "3"]);
    let snapshot = |lime: &Lime| -> Vec<(String, Vec<u8>)> {
        let mut out = Vec::new();
        let mut stack = vec![lime.plan.clone()];
        while let Some(dir) = stack.pop() {
            for e in std::fs::read_dir(&dir).expect("a directory").flatten() {
                let p = e.path();
                if p.is_dir() {
                    stack.push(p);
                } else {
                    out.push((p.display().to_string(), std::fs::read(&p).expect("a file")));
                }
            }
        }
        out.sort();
        out
    };
    let before = snapshot(&lime);
    lime.ok_at(&at("09:30"), &["start", "^t3"]);
    assert!(before == snapshot(&lime), "a continuation with no break running wrote a byte");
}

/// **Both directions**: another id is still refused by name while a block runs, writing nothing,
/// and `--json` carries the continuation's shape — `already_running`, the log's start, and
/// `break_ended` exactly when a break was ended.
#[test]
fn another_id_is_refused_and_the_json_says_already_running() {
    let lime = example();
    lime.ok_at(&at("09:00"), &["start", "^t3", "--energy", "3"]);
    let lines = log(&lime);
    let other = lime.run_at(&at("09:30"), &["start", "^t4"]);
    assert_eq!(other.code, 1, "{}{}", other.stdout, other.stderr);
    assert!(other.stderr.contains("^t3 is running"), "{}", other.stderr);
    assert_eq!(log(&lime), lines);

    let v = lime.json_at(&at("09:30"), &["start", "^t3"]);
    assert_eq!(v["already_running"], true, "{v}");
    assert_eq!(v["id"], "t3", "{v}");
    assert_eq!(v["started"], "09:00", "{v}");
    assert!(v.get("break_ended").is_none(), "{v}");
    assert!(v.get("energy_not_recorded").is_none(), "{v}");

    lime.ok_at(&at("09:40"), &["break", "10m"]);
    let v = lime.json_at(&at("09:45"), &["start", "^t3"]);
    assert_eq!(
        v["break_ended"],
        serde_json::json!({"action": "ended", "planned_min": 10, "actual_min": 5, "place": null}),
        "{v}"
    );
}

/// **An `--energy` report on a continuation is not recorded, and the line says so** — no `start`
/// is logged, so the report has no line to ride on; `lime energy` is named as the verb that records
/// one. A paused block stays paused, and the line says that too.
#[test]
fn a_continuation_names_what_it_did_not_record_and_a_pause_it_kept() {
    let lime = example();
    lime.ok_at(&at("09:00"), &["start", "^t3", "--energy", "3"]);
    let out = lime.ok_at(&at("09:30"), &["start", "^t3", "--energy", "4"]);
    assert_eq!(
        out.stdout.trim(),
        "^t3 is already running since 09:00 · --energy 4 not recorded: no `start` is logged (`lime energy 4` reports it)",
        "{}",
        out.stdout
    );
    lime.ok_at(&at("09:35"), &["pause"]);
    let out = lime.ok_at(&at("09:40"), &["start", "^t3"]);
    assert_eq!(out.stdout.trim(), "^t3 is already running since 09:00 · paused (`lime pause` starts the timer)", "{}", out.stdout);
    assert_eq!(lime.state()["active"]["paused"], true, "{}", lime.state());
}

/// **`lime undo` of a continuation that ended a break puts the break back**: the day file and the
/// running break, as before the re-start.
#[test]
fn undo_of_a_continuation_puts_the_break_back() {
    let lime = example();
    lime.ok_at(&at("09:00"), &["start", "^t3", "--energy", "3"]);
    lime.ok_at(&at("09:30"), &["break"]);
    let day = lime.read("day/2026-09-07.md");
    lime.ok_at(&at("09:50"), &["start", "^t3"]);
    lime.ok_at(&at("09:51"), &["undo"]);
    assert_eq!(lime.read("day/2026-09-07.md"), day);
    assert!(!lime.state()["break"].is_null(), "the break runs again: {}", lime.state());
    assert_eq!(lime.state()["active"]["id"], "t3", "{}", lime.state());
}
