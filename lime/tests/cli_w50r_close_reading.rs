//! **The W-50 repair's host half** (README "Stage 6 — W-50 repair, track R"): `tm check`'s
//! `log-taken-block` reads a close's batch by its own instant (gap 5503), `tm stop` on a settled line
//! leaves the line (the owner's **D132**, gap 5471, parity **P129**), and D130's stop goes at the
//! latest mark logged after the closed period's end (the owner's **D134**, gap 5470, P128 restated).

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

fn stops(tm: &Tm) -> Vec<Value> {
    tm.log().into_iter().filter(|e| e["ev"] == "stop").collect()
}

/// The log as a binary before D130 left it: the first verb of 2026-09-14 closes W37 with `^t3`'s block
/// running, and the `stop` D130 wrote is removed (a hand edit, a sync), the cache with it (D42).
fn taken_before_d130() -> Tm {
    let tm = running("2026-09-07", "10:20", "^t3");
    tm.ok_at(&at("2026-09-14", "10:00"), &["now"]);
    let path = tm.plan.join(".tm/log.jsonl");
    let text = std::fs::read_to_string(&path).expect("the log");
    let kept: Vec<&str> = text.lines().filter(|l| !l.contains("\"ev\":\"stop\"")).collect();
    assert_eq!(kept.len() + 1, text.lines().count(), "one stop removed");
    std::fs::write(&path, kept.join("\n") + "\n").expect("the log, as before D130");
    let _ = std::fs::remove_file(tm.plan.join(".tm/state.json"));
    tm
}

/// **Gap 5503 — a user's own `move` before the next close is not that close's batch.** `^t3` started
/// 09-08 10:20 and moved to the backlog by hand at 10:30 while it runs; the first verb of 09-14
/// week-closes W37, which no longer holds `^t3`, so D130 rightly keeps the block running. Until the
/// W-50 repair `tm check` read the `move` (10:30) and the close's lines (09-14) as one batch and said
/// the week close took the item.
#[test]
fn a_users_own_move_before_the_next_close_is_not_that_closes_batch() {
    let tm = running("2026-09-08", "10:20", "^t3");
    tm.ok_at(&at("2026-09-08", "10:30"), &["move", "^t3", "backlog"]);
    let check = tm.run_at(&at("2026-09-14", "10:05"), &["check"]);
    assert!(!check.stdout.contains("log-taken-block"), "{}{}", check.stdout, check.stderr);
    assert_eq!(tm.state()["active"]["id"], "t3", "D130 kept the block running");
}

/// **Gap 5503 — only the close that took the item is named.** On a pre-D130 log the automatic close of
/// 2026-09-14 logged the day close of 2026-09-13 and the week close of 2026-W37 at one instant; `^t3`
/// is a child the week close dropped into its parent (gap 5474: it logs nothing), so the week close —
/// the only grain that drops a child — is named, and the day close is not.
#[test]
fn only_the_close_that_took_the_item_is_named() {
    let tm = taken_before_d130();
    let log = tm.log();
    assert!(log.iter().any(|e| e["ev"] == "close" && e["period"] == "day"), "a day close at that instant too");
    let check = tm.run_at(&at("2026-09-14", "10:05"), &["check"]);
    assert!(check.stdout.contains("warning[log-taken-block]"), "{}", check.stdout);
    assert!(check.stdout.contains("(the week close of 2026-W37)"), "{}", check.stdout);
    assert!(!check.stdout.contains("day close"), "{}", check.stdout);
    assert!(check.stdout.contains("a settled line is left as it stands, D132"), "{}", check.stdout);
}

/// **D132 (gap 5471, parity P129).** Following the warning — `tm stop --at 10:20` — logs the `stop` and
/// leaves the dropped line as it stands: no remainder written, no box reopened, the closed week's file
/// byte for byte. Until D132 the stop wrote `[ ] 5m` back into the closed W37.
#[test]
fn tm_stop_on_a_settled_line_logs_the_stop_and_leaves_the_line_p129() {
    let tm = taken_before_d130();
    let week = tm.read("week/2026-W37.md");
    assert!(tm.line("week/2026-W37.md", "t3").starts_with("- [~]"), "dropped by the close");
    let out = tm.ok_at(&at("2026-09-14", "10:30"), &["stop", "--at", "10:20"]);
    assert_eq!(tm.read("week/2026-W37.md"), week, "the closed week is not edited: {}", out.stderr);
    assert!(out.stdout.contains("its line is settled and left as it stands (D132)"), "{}", out.stdout);
    let s = stops(&tm);
    assert_eq!(s.len(), 1, "the stop is logged");
    assert_eq!(s[0]["id"], "t3");
    assert!(tm.state()["active"].is_null(), "nothing runs");
    let check = tm.run_at(&at("2026-09-14", "10:31"), &["check"]);
    assert!(!check.stdout.contains("log-taken-block"), "{}", check.stdout);
}

/// **D134 (gap 5470).** The log already holds marks of the running block stamped after W37's end — a
/// `pause` 09-14 09:00 and an `unpause` 09:30 a synced machine wrote before any verb here ran the close —
/// so D130's stop goes at the latest of them, 09:30, and not at W37's last instant (stamped before marks
/// the file holds). Said as `its latest mark`.
#[test]
fn the_stop_goes_at_the_latest_mark_logged_after_the_period_s_end() {
    let tm = running("2026-09-07", "10:20", "^t3");
    let path = tm.plan.join(".tm/log.jsonl");
    let mut text = std::fs::read_to_string(&path).expect("the log");
    text.push_str("{\"t\":\"2026-09-14T09:00:00-05:00\",\"ev\":\"pause\",\"id\":\"t3\"}\n");
    text.push_str("{\"t\":\"2026-09-14T09:30:00-05:00\",\"ev\":\"unpause\",\"id\":\"t3\"}\n");
    std::fs::write(&path, text).expect("the synced marks");
    let _ = std::fs::remove_file(tm.plan.join(".tm/state.json"));
    let out = tm.ok_at(&at("2026-09-14", "10:00"), &["now"]);
    assert!(
        out.stderr.contains("stopped ^t3 at 2026-09-14 09:30, its latest mark, logged after the end of 2026-W37"),
        "{}",
        out.stderr
    );
    let s = stops(&tm);
    assert_eq!(s.len(), 1);
    assert_eq!(s[0]["t"], "2026-09-14T09:30:00-05:00");
    let log = tm.log();
    let stop = log.iter().position(|e| e["ev"] == "stop").expect("a stop");
    let close = log.iter().position(|e| e["ev"] == "close" && e["key"] == "2026-W37").expect("the week close");
    assert!(stop < close);
}

/// **D134, the other side: with no mark after the period's end the cap stands** — the pause and unpause
/// on 09-07 keep D130's last-activity rule (`its last logged activity`, 09-07 11:30).
#[test]
fn with_no_later_mark_the_cap_stands() {
    let tm = running("2026-09-07", "10:20", "^t3");
    tm.ok_at(&at("2026-09-07", "11:00"), &["pause"]);
    tm.ok_at(&at("2026-09-07", "11:30"), &["pause"]);
    let out = tm.ok_at(&at("2026-09-14", "10:00"), &["now"]);
    assert!(out.stderr.contains("stopped ^t3 at 2026-09-07 11:30, its last logged activity"), "{}", out.stderr);
}
