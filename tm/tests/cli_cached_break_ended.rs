//! **A running break `.tm/state.json` holds and the log has ENDED is dropped, however long ago it began**
//! (README "Stage 6 — W-50 repair, track B", gaps 5520-5522; the W-50 critic's blocker).
//!
//! The cache stores a break's start as a bare `HH:MM`, and the log's record of it sits at its real start
//! (the `break_start` `tm break` logged, ended by a `break` line or, since the owner's D129, by a
//! `start` stamped after it). The reconcile looked for that record only at D81's "latest instant at or
//! before `now` with the cached clock", which is the real start only until `now` passes the next
//! occurrence of that clock: from about a day on, a break the log ended survived in the cache — drawn
//! from midnight while `.tm/state.json` existed and gone without it (D42), and logged with every hour
//! since by the next verb that ended it (`break ended · 630m of 15m`, a break nobody took). Each test
//! drives the built binary on a fresh `tm init --example` tree (America/Chicago).

mod cli_common;

use std::fs;

use serde_json::Value;

use cli_common::Tm;

/// Copy a plan directory (the sync's snapshot).
fn copy(from: &std::path::Path, to: &std::path::Path) {
    fs::create_dir_all(to).expect("create");
    for entry in fs::read_dir(from).expect("read") {
        let entry = entry.expect("entry");
        let target = to.join(entry.file_name());
        if entry.file_type().expect("type").is_dir() {
            copy(&entry.path(), &target);
        } else {
            fs::copy(entry.path(), &target).expect("copy");
        }
    }
}

/// **D129's two machines, A's cache kept**: A's `tm break 15m` at 23:00 on 09-08, never ended; B, which
/// had not seen it, works `^t1` 07:05-08:05 on 09-09; the sync appends B's lines after A's, and A keeps
/// its own `.tm/state.json` (its break running at 23:00) — the world the critic drove.
fn merged() -> Tm {
    let a = Tm::empty();
    assert_eq!(a.run(&["init", "--example"]).code, 0);
    a.ok_at("2026-09-08T06:05:00-05:00", &["wake"]);
    let b = Tm::empty();
    copy(&a.plan, &b.plan);
    a.ok_at("2026-09-08T23:00:00-05:00", &["break", "15m"]);
    assert!(!a.state()["break"].is_null(), "A's cache holds its break: {}", a.state());
    let before = fs::read_to_string(b.plan.join(".tm/log.jsonl")).expect("B's log");
    b.ok_at("2026-09-09T06:05:00-05:00", &["wake"]);
    b.ok_at("2026-09-09T07:00:00-05:00", &["arrive", "lounge"]);
    b.ok_at("2026-09-09T07:05:00-05:00", &["start", "^t1"]);
    b.ok_at("2026-09-09T08:05:00-05:00", &["done"]);
    let after = fs::read_to_string(b.plan.join(".tm/log.jsonl")).expect("B's log");
    let mine = fs::read_to_string(a.plan.join(".tm/log.jsonl")).expect("A's log");
    fs::write(a.plan.join(".tm/log.jsonl"), format!("{mine}{}", &after[before.len()..])).expect("merge");
    let _ = fs::remove_dir_all(a.plan.join(".tm/cache"));
    a
}

/// The `break` segments of `tm plan --json`, as `(start, end)`.
fn breaks(plan: &Value) -> Vec<(String, String)> {
    plan["segments"]
        .as_array()
        .unwrap_or_else(|| panic!("no segments: {plan}"))
        .iter()
        .filter(|s| s["kind"] == "break")
        .map(|s| (s["start"].as_str().unwrap_or_default().to_string(), s["end"].as_str().unwrap_or_default().to_string()))
        .collect()
}

/// **Two days on, the cache and the rebuilt runtime plan one day** (D42): no break is drawn, with the
/// file or without it, and the verb drops the cache's break.
#[test]
fn a_break_a_start_ended_two_days_ago_does_not_survive_in_the_cache() {
    let with = merged();
    let without = merged();
    let _ = fs::remove_file(without.plan.join(".tm/state.json"));
    let at = "2026-09-11T09:00:00-05:00";
    let out = with.run_at(at, &["plan"]);
    assert_eq!(out.code, 0, "{}", out.stderr);
    assert!(out.stderr.contains("ended it"), "the reconcile did not say the log ended the break: {}", out.stderr);
    assert!(with.state()["break"].is_null(), "the cache still holds the break: {}", with.state());
    let a = breaks(&with.json_at(at, &["plan"]));
    let b = breaks(&without.json_at(at, &["plan"]));
    assert!(a.iter().all(|(s, _)| s.as_str() >= "09:00"), "a break nobody took is drawn from the night: {a:?}");
    assert_eq!(a, b, "the cache and the rebuilt runtime plan different days");
}

/// **Ending it two days later logs no break nobody took**: `tm start ^t4` at 09-11 09:30 writes no
/// `break` line and says no break ended (the critic's `break ended · 630m of 15m`).
#[test]
fn starting_a_block_two_days_later_logs_no_break_nobody_took() {
    let tm = merged();
    let breaks_before = tm.events().iter().filter(|e| *e == "break").count();
    let out = tm.ok_at("2026-09-11T09:30:00-05:00", &["start", "^t4"]);
    assert!(!out.stdout.contains("break ended"), "the start ended a break nobody took: {}", out.stdout);
    let breaks_after = tm.events().iter().filter(|e| *e == "break").count();
    assert_eq!(breaks_before, breaks_after, "a `break` line was logged: {:?}", tm.log().last());
    assert!(tm.state()["break"].is_null(), "{}", tm.state());
}

/// **Through a D130 stop** (the critic's `d/IA`): A's break at 09:00 on 09-10, B's `start ^t3` at
/// 10:20 the same morning (D129 ends A's break there), A's cache kept; the first verb of 09-14
/// week-closes W37 and stops `^t3` (D130) — and logs no `break` line for A's break.
#[test]
fn a_close_that_stops_a_block_logs_no_break_the_log_ended() {
    let a = Tm::empty();
    assert_eq!(a.run(&["init", "--example"]).code, 0);
    a.ok_at("2026-09-10T06:05:00-05:00", &["wake"]);
    let b = Tm::empty();
    copy(&a.plan, &b.plan);
    a.ok_at("2026-09-10T09:00:00-05:00", &["break", "15m"]);
    let before = fs::read_to_string(b.plan.join(".tm/log.jsonl")).expect("B's log");
    b.ok_at("2026-09-10T10:20:00-05:00", &["start", "^t3"]);
    let after = fs::read_to_string(b.plan.join(".tm/log.jsonl")).expect("B's log");
    let mine = fs::read_to_string(a.plan.join(".tm/log.jsonl")).expect("A's log");
    fs::write(a.plan.join(".tm/log.jsonl"), format!("{mine}{}", &after[before.len()..])).expect("merge");
    let _ = fs::remove_dir_all(a.plan.join(".tm/cache"));
    let out = a.ok_at("2026-09-14T10:00:00-05:00", &["now"]);
    assert!(
        a.log().iter().all(|e| e["ev"] != "break"),
        "a `break` line was logged for the break the log ended: {:?} — {}",
        a.log().iter().filter(|e| e["ev"] == "break").collect::<Vec<_>>(),
        out.stderr
    );
    assert!(a.state()["break"].is_null(), "{}", a.state());
}

/// **An old cache a newer binary meets** (the critic's `d/N1`): an older binary kept a break running
/// in `.tm/state.json` for weeks, rolling its date, while the log's `break_start` was ended by the
/// next morning's `start` (D129). The record is past the verb's scoped replay — the whole log is asked
/// for it — and the cache is dropped with nothing logged.
#[test]
fn an_old_cache_rolled_for_weeks_is_put_right_from_the_whole_log() {
    let tm = Tm::empty();
    assert_eq!(tm.run(&["init", "--example"]).code, 0);
    let mut log = String::new();
    let mut day = chrono::NaiveDate::from_ymd_opt(2026, 9, 8).expect("date");
    let last = chrono::NaiveDate::from_ymd_opt(2026, 11, 29).expect("date");
    while day <= last {
        log.push_str(&format!("{{\"t\":\"{day}T06:05:00-06:00\",\"ev\":\"wake\",\"slept_min\":0}}\n").replace(
            "-06:00",
            if day < chrono::NaiveDate::from_ymd_opt(2026, 11, 1).expect("date") { "-05:00" } else { "-06:00" },
        ));
        if day == chrono::NaiveDate::from_ymd_opt(2026, 9, 10).expect("date") {
            log.push_str("{\"t\":\"2026-09-10T23:00:00-05:00\",\"ev\":\"break_start\",\"planned_min\":15}\n");
        }
        if day == chrono::NaiveDate::from_ymd_opt(2026, 9, 11).expect("date") {
            log.push_str("{\"t\":\"2026-09-11T09:00:00-05:00\",\"ev\":\"start\",\"id\":\"t1\",\"pred\":4,\"hsw\":2.92,\"slept_min\":0,\"loc\":\"lounge\",\"blocks_done\":0,\"since_break_min\":0}\n");
            log.push_str("{\"t\":\"2026-09-11T10:00:00-05:00\",\"ev\":\"stop\",\"id\":\"t1\",\"remaining_min\":60}\n");
        }
        // A block late in the log, so the ledger day moves past the break's month (a stop pins it, README gap 190).
        if day == chrono::NaiveDate::from_ymd_opt(2026, 11, 28).expect("date") {
            log.push_str("{\"t\":\"2026-11-28T09:00:00-06:00\",\"ev\":\"start\",\"id\":\"t1\",\"pred\":4,\"hsw\":2.92,\"slept_min\":0,\"loc\":\"lounge\",\"blocks_done\":0,\"since_break_min\":0}\n");
            log.push_str("{\"t\":\"2026-11-28T10:00:00-06:00\",\"ev\":\"stop\",\"id\":\"t1\",\"remaining_min\":60}\n");
        }
        day = day.succ_opt().expect("date");
    }
    fs::write(tm.plan.join(".tm/log.jsonl"), log).expect("the log");
    let mut state = tm.state();
    state["date"] = Value::from("2026-11-29");
    state["break"] = serde_json::json!({"started": "23:00", "planned_min": 15, "where": null});
    fs::write(tm.plan.join(".tm/state.json"), serde_json::to_string_pretty(&state).expect("json")).expect("state");
    let _ = fs::remove_dir_all(tm.plan.join(".tm/cache"));
    // A read verb first: it seals the log's months into `.tm/cache/replay` (a genesis answers every day) and
    // writes no `.tm/state.json`, so the verb below reads the open days only, as every later verb does.
    let warm = tm.run_at("2026-11-29T09:00:00-06:00", &["log"]);
    assert_eq!(warm.code, 0, "{}", warm.stderr);
    assert!(!tm.state()["break"].is_null(), "a read verb wrote the cache: {}", tm.state());
    let out = tm.run_env_at("2026-11-29T09:00:00-06:00", &[("TM_TRACE_REPLAY_SCOPE", "1")], &["now"]);
    assert_eq!(out.code, 0, "{}", out.stderr);
    assert!(out.stderr.contains("replay scope: all"), "the whole log was not asked: {}", out.stderr);
    assert!(out.stderr.contains("ended it"), "the reconcile did not drop the break: {}", out.stderr);
    assert!(tm.state()["break"].is_null(), "the cache still holds the break: {}", tm.state());
    assert!(tm.log().iter().all(|e| e["ev"] != "break" && e["ev"] != "break_start" || e["t"] == "2026-09-10T23:00:00-05:00"),
        "a break line was logged: {:?}", tm.log().iter().filter(|e| e["ev"] == "break").collect::<Vec<_>>());
}
