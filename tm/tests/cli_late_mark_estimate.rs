//! **A late mark that nets a stopped block corrects the `est:` the block's `stop` wrote** — the owner's **D126**
//! (stage 6 W-49 track L; the W-48 recheck's fourth finding; parity **P125**).
//!
//! Reproduced on the W-48 repair's binary (the recheck's `d115stop` and `lb` worlds): `start ^t1` 09:00, `stop` 10:00
//! (`5m left`), then `--now 09:30 start ^t3` — the replay nets `^t1` to thirty minutes (D115) while the week file kept
//! `- [ ] 5 5m Read ch.6`, and `tm check` said `no problems`: the planner and `tm review day` read one block two ways.
//! The verb that logs the late mark now rewrites the estimate as `stop` would have with the netted minutes, and logs
//! the rewrite as an `edit`; a late line no verb wrote (a sync, a hand edit) is named by `tm check` (`log-stale-est`,
//! D18's warning family).

mod cli_common;

use cli_common::Tm;
use std::io::Write;

fn at(hm: &str) -> String {
    format!("2026-09-07T{hm}:00-05:00")
}

/// The example tree, woken 07:00, arrived 08:00, `^t1` worked 09:00-10:00 and stopped with `5m left`.
fn stopped() -> Tm {
    let tm = Tm::empty();
    tm.ok_at(&at("06:00"), &["init", "--example"]);
    tm.ok_at(&at("07:00"), &["wake", "07:00"]);
    tm.ok_at(&at("08:00"), &["arrive"]);
    tm.ok_at(&at("09:00"), &["start", "^t1", "--energy", "4"]);
    let stop = tm.ok_at(&at("10:00"), &["stop"]);
    assert!(stop.stdout.contains("5m left"), "{}", stop.stdout);
    assert!(tm.line("week/2026-W37.md", "t1").contains(" 5m "), "{}", tm.line("week/2026-W37.md", "t1"));
    tm
}

fn problems(tm: &Tm, now: &str) -> Vec<(String, u64)> {
    let v = tm.json_at(now, &["check"]);
    v["problems"]
        .as_array()
        .expect("problems")
        .iter()
        .map(|p| (p["code"].as_str().unwrap_or_default().to_string(), p["line"].as_u64().unwrap_or_default()))
        .collect()
}

/// **The driven world, a late `start`** (P125's behaviour row): the late `start` at 09:30 nets thirty minutes from
/// `^t1`, so its estimate reads `35m` — the `5m` the stop wrote plus the thirty — the log holds the rewrite as an
/// `edit`, and `tm check` names nothing.
#[test]
fn a_late_start_corrects_the_estimate_its_stop_wrote() {
    let tm = stopped();
    let late = tm.ok_at(&at("09:30"), &["start", "^t3", "--energy", "4"]);
    assert!(late.stderr.contains("^t1's estimate is now 35m (was 5m)"), "{}", late.stderr);
    assert!(tm.line("week/2026-W37.md", "t1").contains(" 35m "), "{}", tm.line("week/2026-W37.md", "t1"));
    let edit = tm.last_ev("edit");
    assert_eq!((edit["id"].as_str(), edit["from"].as_str(), edit["to"].as_str()), (Some("t1"), Some("5m"), Some("35m")));
    assert!(problems(&tm, &at("10:31")).is_empty(), "{:?}", problems(&tm, &at("10:31")));
}

/// **The recheck's `lb` world, a late break**: `--now 09:30 break 30m` logs a `break_start` inside the stopped block,
/// which nets it at once (README gap 5180), and the estimate reads `35m`; ending the break moves nothing further.
#[test]
fn a_late_break_corrects_the_estimate_its_stop_wrote() {
    let tm = stopped();
    tm.ok_at(&at("09:30"), &["break", "30m"]);
    tm.ok_at(&at("10:00"), &["break"]);
    assert!(tm.line("week/2026-W37.md", "t1").contains(" 35m "), "{}", tm.line("week/2026-W37.md", "t1"));
    assert!(problems(&tm, &at("10:31")).is_empty());
}

/// **The boundary** (AGENTS §5.8): a `start` after the stop nets nothing and rewrites nothing.
#[test]
fn a_start_after_the_stop_rewrites_nothing() {
    let tm = stopped();
    let next = tm.ok_at(&at("10:05"), &["start", "^t3", "--energy", "4"]);
    assert!(!next.stderr.contains("estimate is now"), "{}", next.stderr);
    assert!(tm.line("week/2026-W37.md", "t1").contains(" 5m "), "{}", tm.line("week/2026-W37.md", "t1"));
}

/// **A late line no verb wrote** (a sync appending another machine's line, or a hand edit) is named by `tm check`, at
/// its own line, with the estimate the log now reads; `tm edit` with that value takes the name away.
#[test]
fn a_late_line_no_verb_wrote_is_named_by_tm_check() {
    let tm = stopped();
    let mut f = std::fs::OpenOptions::new().append(true).open(tm.plan.join(".tm/log.jsonl")).expect("log");
    writeln!(
        f,
        r#"{{"t":"2026-09-07T09:30:00-05:00","ev":"start","id":"t3","pred":4,"rep":4,"hsw":2.5,"slept_min":0,"loc":"lounge","blocks_done":0,"since_break_min":30}}"#
    )
    .expect("append");
    drop(f);
    let _ = std::fs::remove_file(tm.plan.join(".tm/state.json"));
    let check = tm.run_at(&at("10:31"), &["check"]);
    assert_eq!(check.code, 0, "a warning moves no exit code: {}", check.stdout);
    assert!(check.stdout.contains("log-stale-est") && check.stdout.contains("est=35m"), "{}", check.stdout);
    assert_eq!(problems(&tm, &at("10:31")), vec![("log-stale-est".to_string(), 6)]);
    tm.ok_at(&at("10:32"), &["edit", "^t1", "est=35m"]);
    assert!(problems(&tm, &at("10:33")).is_empty(), "{:?}", problems(&tm, &at("10:33")));
}
