//! **§6.3's close STOPS a block still running on an item it is about to take** — the owner's **D130**
//! (README gap 5413, stage 6 W-50 track C, parity **P128**).
//!
//! Gap 5413 was driven by the W-49 repair on §4.3's tree: `^t3` started Monday 2026-09-07 10:20 and left
//! running; the first verb of Monday 2026-09-14 week-closed W37 and dropped `^t3` (`[~]`) while its block kept
//! running, `tm now` showed `10060m of 60m`, `tm stop --at 10:20` credited 10,080 minutes and rewrote the dropped
//! line as an open `[ ] 5m` inside the closed W37, and `tm check` said no problems. D130: before the close drops,
//! files or carries the item, the block is ended — at its LAST LOGGED ACTIVITY, never later than the closed period's
//! last instant, or, for a block started on the period's last day, at that last instant — logged as `tm stop` logs
//! it, the estimate written as `tm stop` writes it, and SAID in one line; `tm check` names a running block whose
//! item a close has already taken (a log written before D130, a sync, a hand edit).

mod cli_common;

use cli_common::Tm;
use serde_json::Value;

fn at(day: &str, hm: &str) -> String {
    format!("{day}T{hm}:00-05:00")
}

/// §4.3's tree, woken and arrived on `day`, with `id` started at `hm` and left running.
fn running(day: &str, hm: &str, id: &str) -> Tm {
    let tm = Tm::new();
    tm.ok_at(&at(day, "06:05"), &["wake", "06:05"]);
    tm.ok_at(&at(day, "07:00"), &["arrive", "lounge"]);
    tm.ok_at(&at(day, hm), &["start", id]);
    tm
}

fn t3(tm: &Tm) -> String {
    tm.line("week/2026-W37.md", "t3")
}

/// The log's `stop` lines, in order.
fn stops(tm: &Tm) -> Vec<Value> {
    tm.log().into_iter().filter(|e| e["ev"] == "stop").collect()
}

/// **Gap 5413, reversed.** The first verb of 2026-09-14 stops `^t3` at its start (its last logged activity — it
/// began on Monday 09-07, not on W37's last day), logs the `stop` there with `tm stop`'s remainder, says so, and
/// only then week-closes W37, which drops `^t3` with the estimate the stop wrote. The later `tm stop` has nothing
/// to stop, no closed file is edited after its close, and `tm check` is clean.
#[test]
fn gap_5413_reversed_the_close_stops_the_block_at_its_last_logged_activity_p128() {
    let tm = running("2026-09-07", "10:20", "^t3");
    let out = tm.ok_at(&at("2026-09-14", "10:00"), &["now"]);
    assert!(
        out.stderr.contains(
            "stopped ^t3 at 2026-09-07 10:20, its last logged activity, before the close of 2026-W37 took it · 0m worked · 60m left"
        ),
        "the one line D130 says: {}",
        out.stderr
    );
    assert!(out.stdout.starts_with("nothing running"), "{}", out.stdout);
    let log = tm.log();
    let stop = log.iter().position(|e| e["ev"] == "stop").expect("a stop");
    assert_eq!(log[stop]["t"], "2026-09-07T10:20:00-05:00", "at the block's start");
    assert_eq!(log[stop]["remaining_min"], 60);
    let close = log.iter().position(|e| e["ev"] == "close" && e["key"] == "2026-W37").expect("the week close");
    assert!(stop < close, "the stop is logged before the close's lines");
    assert!(log[stop + 1..close].iter().all(|e| e["ev"] != "start"), "nothing restarts it");
    let line = t3(&tm);
    assert!(line.starts_with("- [~] 4 1b Exercises"), "dropped by the close, with the stop's remainder: {line}");
    assert!(tm.state()["active"].is_null(), "nothing is running");

    let week = tm.read("week/2026-W37.md");
    let again = tm.run_at(&at("2026-09-14", "10:30"), &["stop", "--at", "10:20"]);
    assert_eq!(again.code, 1, "{}{}", again.stdout, again.stderr);
    assert!(again.stderr.contains("nothing is running"), "{}", again.stderr);
    assert_eq!(tm.read("week/2026-W37.md"), week, "the closed week is not edited after its close");
    let check = tm.ok_at(&at("2026-09-14", "10:31"), &["check"]);
    assert!(check.stdout.contains("no problems"), "{}", check.stdout);
}

/// **A block started on the closed period's last day is stopped at that period's last instant** (D130's
/// 2026-10-27 refinement): begun Sunday 23:30, running at Monday 00:30's first verb, it is ended at Sunday
/// 23:59:59 — 29 whole minutes and 59 seconds, which `tm stop` logs as 29 (its minutes are whole and floored) —
/// never at its start (0 minutes) and never at Monday's verb (an hour).
#[test]
fn a_block_started_on_the_periods_last_day_is_stopped_at_its_last_instant() {
    let tm = running("2026-09-13", "23:30", "^t3");
    let out = tm.ok_at(&at("2026-09-14", "00:30"), &["now"]);
    assert!(
        out.stderr.contains("stopped ^t3 at 2026-09-13 23:59, the end of 2026-W37, before the close of 2026-W37 took it · 29m worked · 31m left"),
        "{}",
        out.stderr
    );
    let s = stops(&tm);
    assert_eq!(s.len(), 1);
    assert_eq!(s[0]["t"], "2026-09-13T23:59:59-05:00");
    assert_eq!(s[0]["remaining_min"], 31);
    assert!(t3(&tm).starts_with("- [~] 4 31m Exercises"), "{}", t3(&tm));
}

/// **A paused block's last activity is the instant it stopped** — its minutes are already net, so the stop at its
/// `pause` logs exactly the minutes worked before it; and a block resumed afterwards is stopped at the resume.
#[test]
fn a_paused_block_is_stopped_at_its_pause_and_a_resumed_one_at_its_unpause() {
    let paused = running("2026-09-07", "10:20", "^t3");
    paused.ok_at(&at("2026-09-07", "11:00"), &["pause"]);
    let out = paused.ok_at(&at("2026-09-14", "10:00"), &["now"]);
    assert!(out.stderr.contains("stopped ^t3 at 2026-09-07 11:00, its last logged activity"), "{}", out.stderr);
    assert!(out.stderr.contains("40m worked · 20m left"), "{}", out.stderr);
    assert_eq!(stops(&paused)[0]["t"], "2026-09-07T11:00:00-05:00");

    let resumed = running("2026-09-07", "10:20", "^t3");
    resumed.ok_at(&at("2026-09-07", "11:00"), &["pause"]);
    resumed.ok_at(&at("2026-09-07", "11:30"), &["pause"]);
    let out = resumed.ok_at(&at("2026-09-14", "10:00"), &["now"]);
    assert!(out.stderr.contains("stopped ^t3 at 2026-09-07 11:30, its last logged activity"), "{}", out.stderr);
    assert!(out.stderr.contains("40m worked · 20m left"), "the pause is netted: {}", out.stderr);
}

/// **The explicit `tm close week` follows the same rule** (one close, one rule — the campaign's call under D130),
/// and its `--json` report carries the stop.
#[test]
fn the_explicit_close_stops_the_block_too_and_reports_it() {
    let tm = running("2026-09-07", "10:20", "^t3");
    let doc = tm.json_at(&at("2026-09-14", "10:00"), &["close", "week"]);
    let stopped = &doc["report"]["stopped"];
    assert_eq!(stopped["id"], "t3", "{doc}");
    assert_eq!(stopped["rule"], "lastActivity");
    assert_eq!(stopped["period"], "2026-W37");
    assert_eq!(stopped["at"], "2026-09-07T10:20:00-05:00");
    assert_eq!((stopped["worked_min"].as_u64(), stopped["remaining_min"].as_u64()), (Some(0), Some(60)));
    assert!(t3(&tm).starts_with("- [~]"), "{}", t3(&tm));
    assert!(tm.state()["active"].is_null());
}

/// **A block on an item the close does not take is untouched** — a backlog item is in no closed period, so the
/// week close leaves the block running, logs no `stop`, and `tm check` names no taken block.
#[test]
fn a_block_on_an_item_the_close_does_not_take_keeps_running() {
    let tm = running("2026-09-07", "10:20", "^a1");
    let out = tm.ok_at(&at("2026-09-14", "10:00"), &["now"]);
    assert!(!out.stderr.contains("stopped ^"), "{}", out.stderr);
    assert!(stops(&tm).is_empty());
    assert_eq!(tm.state()["active"]["id"], "a1", "still running");
    let check = tm.run_at(&at("2026-09-14", "10:01"), &["check"]);
    assert!(!check.stdout.contains("log-taken-block"), "{}", check.stdout);
}

/// **`tm check` names a running block whose item a close has already taken** (D130's `tm check` half, D18's
/// warning family): the log a binary before D130 wrote — the close's lines after the block's `start`, and no
/// `stop` — reached here by removing the stop D130 wrote, as a hand edit or a sync would leave it, and the cache
/// with it (D42 rebuilds the running block from the log).
#[test]
fn tm_check_names_a_running_block_whose_item_a_close_took() {
    let tm = running("2026-09-07", "10:20", "^t3");
    tm.ok_at(&at("2026-09-14", "10:00"), &["now"]);
    let path = tm.plan.join(".tm/log.jsonl");
    let text = std::fs::read_to_string(&path).expect("the log");
    let kept: Vec<&str> = text.lines().filter(|l| !l.contains("\"ev\":\"stop\"")).collect();
    assert_eq!(kept.len() + 1, text.lines().count(), "one stop removed");
    std::fs::write(&path, kept.join("\n") + "\n").expect("the log, as before D130");
    let _ = std::fs::remove_file(tm.plan.join(".tm/state.json"));
    let check = tm.run_at(&at("2026-09-14", "10:05"), &["check"]);
    assert_eq!(check.code, 0, "a warning moves no exit code: {}{}", check.stdout, check.stderr);
    assert!(check.stdout.contains("warning[log-taken-block]: a block on ^t3 has been running since 2026-09-07 10:20"), "{}", check.stdout);
    assert!(check.stdout.contains("the week close of 2026-W37"), "{}", check.stdout);
    assert!(check.stdout.contains("the close settled it"), "{}", check.stdout);
}
