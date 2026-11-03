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

// ---------------------------------------------------------------------------------------------------------------
// W-51 repair track H (README gaps 5610, 5611): D126 follows the minutes in BOTH directions. The critic's blocker,
// driven on the W-51 land's binary: `--now 09:30 break 10m` inside the stopped block nets it (`5m` -> `35m`), and
// ending the break at 09:40 gives back what the running took outside its own span (D137) — the log counts fifty
// minutes — while the line kept `35m` and `tm check` said `no problems`.
// ---------------------------------------------------------------------------------------------------------------

/// Appends raw lines to the log, as a sync or a hand edit would, and drops the cache (D42 rebuilds it).
fn append(tm: &Tm, lines: &[&str]) {
    let mut f = std::fs::OpenOptions::new().append(true).open(tm.plan.join(".tm/log.jsonl")).expect("log");
    for l in lines {
        writeln!(f, "{l}").expect("append");
    }
    drop(f);
    let _ = std::fs::remove_file(tm.plan.join(".tm/state.json"));
}

const BREAK_0930_10M: &str = r#"{"t":"2026-09-07T09:30:00-05:00","ev":"break","planned_min":10,"actual_min":10}"#;

/// The end of a running break begun by a no-length `tm break --now 09:30` (planned the example's twenty), ten minutes
/// on — as another machine would log it.
const BREAK_0930_20P_10M: &str = r#"{"t":"2026-09-07T09:30:00-05:00","ev":"break","planned_min":20,"actual_min":10}"#;

// **Restated at stage 6 W-54 track H with the owner's D149 (parity P147), a behaviour row, never a silent
// re-bless.** The three rows below typed `tm break --now 09:30 10m` inside the block `tm stop` closed at 10:00: a
// break that RAN (a `break_start`), whose start netted the stopped block and whose end gave back (D137). Under D149
// that keystroke is logged finished in one plain line and the block's `est:` is corrected once, to `15m`, so the rows'
// subject — a running break's two corrections — is now typed with NO length (`tm break --now 09:30`, which still
// begins a running break there), and the synced end carries that break's planned twenty. The readings asserted are
// unchanged.

/// **The critic's world, through the verbs**: the late break's start corrects `5m` to `35m`, and its end — which
/// gives back twenty minutes — corrects `35m` to `15m`, what `tm stop` would have written with the fifty minutes the
/// log now counts (`5m` written + 60 counted at the stop − 50 counted now). The second correction is logged as an
/// `edit`, and `tm check` names nothing.
#[test]
fn a_give_back_corrects_the_estimate_again() {
    let tm = stopped();
    tm.ok_at(&at("09:30"), &["break"]);
    assert!(tm.line("week/2026-W37.md", "t1").contains(" 35m "), "{}", tm.line("week/2026-W37.md", "t1"));
    let end = tm.ok_at(&at("09:40"), &["break"]);
    assert!(end.stderr.contains("^t1's estimate is now 15m (was 35m)"), "{}", end.stderr);
    assert!(tm.line("week/2026-W37.md", "t1").contains(" 15m "), "{}", tm.line("week/2026-W37.md", "t1"));
    let edit = tm.last_ev("edit");
    assert_eq!((edit["id"].as_str(), edit["from"].as_str(), edit["to"].as_str()), (Some("t1"), Some("35m"), Some("15m")));
    assert!(problems(&tm, &at("10:31")).is_empty(), "{:?}", problems(&tm, &at("10:31")));
}

/// **The same give-back with no verb to correct it** (the break's end synced from another machine): `tm check`
/// names the `break` line, after D126's own correction `edit`, with the estimate the log now reads; `tm edit` with
/// that value takes the name away.
#[test]
fn a_give_back_no_verb_corrected_is_named_by_tm_check() {
    let tm = stopped();
    tm.ok_at(&at("09:30"), &["break"]);
    append(&tm, &[BREAK_0930_20P_10M]);
    let check = tm.run_at(&at("10:31"), &["check"]);
    assert_eq!(check.code, 0, "a warning moves no exit code: {}", check.stdout);
    assert!(check.stdout.contains("log-stale-est") && check.stdout.contains("est=15m"), "{}", check.stdout);
    let lines = tm.read(".tm/log.jsonl").lines().count() as u64;
    assert_eq!(problems(&tm, &at("10:31")), vec![("log-stale-est".to_string(), lines)]);
    tm.ok_at(&at("10:32"), &["edit", "^t1", "est=15m"]);
    assert!(problems(&tm, &at("10:33")).is_empty(), "{:?}", problems(&tm, &at("10:33")));
}

/// **The critic's second shape, a synced log** (pre-existing): `start 09:00`, another machine's `break_start 09:30`
/// merged in before the `stop 10:00` that wrote `5m` — its author never saw the break, or the stop would have ended
/// it (D97) — and the break's own `break 09:30 10m` after. The log counts fifty minutes and the line reads `5m`; the
/// old baseline, the replay up to the `stop` with that `break_start` in it, counted thirty and read the block as
/// already netted. `tm check` names the `break` line with `est=15m`.
#[test]
fn a_synced_break_its_stop_never_saw_is_named_by_tm_check() {
    let tm = stopped();
    let log = tm.plan.join(".tm/log.jsonl");
    let text = std::fs::read_to_string(&log).expect("log");
    let mut lines: Vec<&str> = text.lines().collect();
    let stop = lines.iter().rposition(|l| l.contains(r#""ev":"stop""#)).expect("the stop");
    lines.insert(stop, r#"{"t":"2026-09-07T09:30:00-05:00","ev":"break_start","planned_min":10}"#);
    std::fs::write(&log, lines.join("\n") + "\n").expect("log");
    append(&tm, &[BREAK_0930_10M]);
    assert!(tm.line("week/2026-W37.md", "t1").contains(" 5m "), "{}", tm.line("week/2026-W37.md", "t1"));
    let check = tm.run_at(&at("10:31"), &["check"]);
    assert!(check.stdout.contains("log-stale-est") && check.stdout.contains("est=15m"), "{}", check.stdout);
    let n = tm.read(".tm/log.jsonl").lines().count() as u64;
    assert_eq!(problems(&tm, &at("10:31")), vec![("log-stale-est".to_string(), n)]);
}

/// **The boundary** (AGENTS §5.8): an estimate the user typed after the late mark is theirs — a later give-back
/// rewrites nothing, and `tm check` names nothing, because the typed `edit` is not one D126 would have written.
#[test]
fn a_typed_estimate_after_the_mark_is_not_rewritten() {
    let tm = stopped();
    tm.ok_at(&at("09:30"), &["break"]);
    tm.ok_at(&at("09:35"), &["edit", "^t1", "est=50m"]);
    let end = tm.ok_at(&at("09:40"), &["break"]);
    assert!(!end.stderr.contains("estimate is now"), "{}", end.stderr);
    assert!(tm.line("week/2026-W37.md", "t1").contains(" 50m"), "{}", tm.line("week/2026-W37.md", "t1"));
    assert!(problems(&tm, &at("10:31")).is_empty(), "{:?}", problems(&tm, &at("10:31")));
}
