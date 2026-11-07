//! **The W-51 repair's host half** (README "Stage 6 — W-51 repair, track H"): D132's rule reaches `lime
//! done` and `--partial` (the owner's **D135**, gap 5505, parity **P131**); a block ended on a settled line
//! journals no remainder (the owner's **D136**, gap 5540, parity **P132**); a cache-only break placed before
//! the day's logged wake is dropped, not logged (the owner's **D138**, parity **P133**); D133 holds when the
//! automatic close's D130 stop meets a cache-only break (the W-50 repair critic's first finding); `lime
//! check`'s `log-taken-block` and D130's last activity read the rows a reseal folded (gap 5509); and D133's
//! refusal guard and its one whole-log replay per verb (gap 5523 corrected). Each test drives the built
//! binary on a fresh tree (America/Chicago).

mod cli_common;

use std::fs;

use cli_common::Lime;
use serde_json::Value;

fn at(day: &str, hm: &str) -> String {
    format!("{day}T{hm}:00-05:00")
}

/// `lime init --example`, woken at 08:00 on 2026-09-07.
fn example() -> Lime {
    let lime = Lime::empty();
    assert_eq!(lime.run(&["init", "--example"]).code, 0);
    lime.ok_at(&at("2026-09-07", "08:00"), &["wake"]);
    lime
}

/// Set `.tm/state.json`'s running break by hand — one a binary before the owner's D105 began, which logged no
/// `break_start` (the critic's `setbrk.py`).
fn cache_break(lime: &Lime, started: &str, planned: u32, place: Option<&str>) {
    let mut state = lime.state();
    state["break"] = serde_json::json!({"started": started, "planned_min": planned, "where": place});
    fs::write(lime.plan.join(".tm/state.json"), serde_json::to_string_pretty(&state).expect("json")).expect("state");
    assert!(lime.log().iter().all(|e| e["ev"] != "break_start"), "the log holds a break_start already");
}

fn of(lime: &Lime, ev: &str) -> Vec<Value> {
    lime.log().into_iter().filter(|e| e["ev"] == ev).collect()
}

/// The log as a binary before D130 left it: `^t3` started 09-07 10:20 and left running, the first verb of
/// 2026-09-14 closes W37 (dropping `^t3` into its parent, `[~]`), and the `stop` D130 wrote is removed with the
/// cache (a sync, a hand edit) — the critic's d/T0 world.
fn taken_before_d130() -> Lime {
    let lime = example();
    lime.ok_at(&at("2026-09-07", "10:20"), &["start", "^t3"]);
    lime.ok_at(&at("2026-09-14", "10:00"), &["now"]);
    let path = lime.plan.join(".tm/log.jsonl");
    let text = fs::read_to_string(&path).expect("the log");
    let kept: Vec<&str> = text.lines().filter(|l| !l.contains("\"ev\":\"stop\"")).collect();
    assert_eq!(kept.len() + 1, text.lines().count(), "one stop removed");
    fs::write(&path, kept.join("\n") + "\n").expect("the log, as before D130");
    let _ = fs::remove_file(lime.plan.join(".tm/state.json"));
    assert!(lime.line("week/2026-W37.md", "t3").starts_with("- [~]"), "dropped by the close");
    lime
}

/// **D135 inside a closed week (P131)**: `lime done --at 10:20` on the block a pre-D130 close left running on a
/// dropped `^t3` logs its `done` and leaves the closed week's file byte for byte. Until D135 it set `[x]`.
#[test]
fn d135_done_on_a_dropped_line_in_a_closed_week_leaves_the_file() {
    let lime = taken_before_d130();
    let week = lime.read("week/2026-W37.md");
    let out = lime.ok_at(&at("2026-09-14", "10:30"), &["done", "--at", "10:20"]);
    assert_eq!(lime.read("week/2026-W37.md"), week, "the closed week is not edited: {}", out.stdout);
    assert!(out.stdout.contains("its line is settled and left as it stands (D135)"), "{}", out.stdout);
    let done = of(&lime, "done");
    assert_eq!(done.len(), 1, "the done is logged");
    assert_eq!(done[0]["id"], "t3");
    assert!(lime.state()["active"].is_null(), "nothing runs");
    let json = lime.json_at(&at("2026-09-14", "10:31"), &["log", "--json"]);
    assert!(json.to_string().contains("\"done\""), "{json}");
}

/// **D135 for `--partial` inside a closed week (P131)**: no remainder written, no box reopened — the critic's
/// d/Rdrop, where `[~]` became `[ ] 5m` inside the closed W37.
#[test]
fn d135_done_partial_on_a_dropped_line_in_a_closed_week_reopens_nothing() {
    let lime = taken_before_d130();
    let week = lime.read("week/2026-W37.md");
    let out = lime.ok_at(&at("2026-09-14", "10:30"), &["done", "--partial", "--at", "10:20"]);
    assert_eq!(lime.read("week/2026-W37.md"), week, "the closed week is not edited: {}", out.stdout);
    assert!(!out.stdout.contains("m left"), "a remainder is claimed: {}", out.stdout);
    let done = of(&lime, "done");
    assert_eq!((done.len(), &done[0]["partial"]), (1, &Value::Bool(true)), "{done:?}");
    assert!(of(&lime, "edit").iter().all(|e| e["id"] != "t3"), "an estimate was written");
}

/// A live week: `^t3` started at 10:20, then its line made `glyph` (`lime drop` for `[~]`, a hand edit for
/// `[x]`), the block still running.
fn running_on(glyph: &str) -> Lime {
    let lime = example();
    lime.ok_at(&at("2026-09-07", "10:20"), &["start", "^t3"]);
    match glyph {
        "~" => {
            lime.ok_at(&at("2026-09-07", "10:40"), &["drop", "^t3"]);
        }
        _ => {
            let p = lime.plan.join("week/2026-W37.md");
            let text = fs::read_to_string(&p).expect("week");
            let line = text.lines().find(|l| l.ends_with("^t3")).expect("^t3").to_string();
            let done = line.replacen("- [>]", "- [x]", 1).replacen("- [ ]", "- [x]", 1);
            assert_ne!(line, done, "the box changed: {line}");
            fs::write(&p, text.replacen(&line, &done, 1)).expect("week");
        }
    }
    assert_eq!(lime.state()["active"]["id"], "t3", "the block still runs");
    lime
}

/// **D135 on both glyphs, both verbs, a live week (P131)**: the line is byte for byte what it was, the event is
/// logged, and the journal names no remainder (D136, P132).
#[test]
fn d135_done_and_done_partial_leave_a_dropped_or_done_line_as_it_stands_p131() {
    for glyph in ["~", "x"] {
        for partial in [false, true] {
            let lime = running_on(glyph);
            let before = lime.line("week/2026-W37.md", "t3");
            let args: &[&str] = if partial { &["done", "--partial"] } else { &["done"] };
            let out = lime.ok_at(&at("2026-09-07", "10:50"), args);
            assert_eq!(lime.line("week/2026-W37.md", "t3"), before, "[{glyph}] partial={partial}: {}", out.stdout);
            assert!(out.stdout.contains("(D135)"), "[{glyph}] partial={partial}: {}", out.stdout);
            let done = of(&lime, "done");
            assert_eq!(done.len(), 1, "[{glyph}] partial={partial}");
            let journal = lime.read("day/2026-09-07.md");
            let line = journal.lines().find(|l| l.starts_with("10:50 done ^t3")).expect("the journal line");
            assert!(line.ends_with("· line settled, left as it stands") && !line.contains("left ·"), "{line}");
        }
    }
}

/// **A retro `lime done ^id` on a settled line is REFUSED by name** — the owner's **D140** (the W-51 critic's second
/// finding, parity **P135**; README "Stage 6 — W-51 repair track H"). This test pinned the old behaviour as
/// d135_a_retro_done_still_sets_the_box (a retro done set `[x]` on a dropped line, inside a week a close had already
/// taken) and changes with P135's behaviour row. The orchestrator's `Q2` world: `^t3` dropped in W37, the week closed
/// at 09-14, then `lime done ^t3` — nothing is written (no line, no log line, no journal), the message names the line as
/// settled and says to edit it, and `--json` carries the refusal in the shape of the verb's other refusals.
#[test]
fn d140_a_retro_done_on_a_settled_line_is_refused_p135() {
    for glyph in ["~", "x"] {
        let lime = example();
        if glyph == "~" {
            lime.ok_at(&at("2026-09-07", "10:40"), &["drop", "^t3"]);
        } else {
            lime.ok_at(&at("2026-09-07", "10:40"), &["done", "^t3"]);
        }
        lime.ok_at(&at("2026-09-14", "09:00"), &["plan"]);
        let line = lime.line("week/2026-W37.md", "t3");
        assert!(line.starts_with(&format!("- [{glyph}]")), "{line}");
        let (log, week, journal) = (lime.read(".tm/log.jsonl"), lime.read("week/2026-W37.md"), lime.read("day/2026-09-14.md"));
        let out = lime.run_at(&at("2026-09-14", "09:05"), &["done", "^t3"]);
        assert_eq!(out.code, 1, "[{glyph}] {}{}", out.stdout, out.stderr);
        assert!(out.stderr.contains("^t3 is settled") && out.stderr.contains("week/2026-W37.md"), "{}", out.stderr);
        assert!(out.stderr.contains("nothing was written") && out.stderr.contains("(D140)"), "{}", out.stderr);
        if glyph == "~" {
            assert!(out.stderr.contains("edit its line's box to `[x]`"), "{}", out.stderr);
        }
        let json = lime.run_at(&at("2026-09-14", "09:05"), &["done", "^t3", "--json"]);
        // A refusal's JSON is on stderr, as every verb's (`out::CliError`).
        let v: Value = serde_json::from_str(&json.stderr).expect("json");
        assert_eq!((v["ok"].as_bool(), v["kind"].as_str(), json.code), (Some(false), Some("error"), 1), "{v}");
        // The verb's other refusals have the same shape: `--went 7` is one.
        let other = lime.run_at(&at("2026-09-14", "09:05"), &["done", "^t3", "--went", "7", "--json"]);
        let o: Value = serde_json::from_str(&other.stderr).expect("json");
        let keys = |v: &Value| v.as_object().map(|m| m.keys().cloned().collect::<Vec<_>>()).unwrap_or_default();
        assert_eq!(keys(&v), keys(&o), "{v} vs {o}");
        assert_eq!(lime.read(".tm/log.jsonl"), log, "[{glyph}] a log line was written");
        assert_eq!(lime.read("week/2026-W37.md"), week, "[{glyph}] the week file was written");
        assert_eq!(lime.read("day/2026-09-14.md"), journal, "[{glyph}] the journal was written");
    }
}

/// **D140's boundary** (AGENTS §5.8): a retro `lime done ^id` on an OPEN line still sets the box, as before.
#[test]
fn d140_a_retro_done_on_an_open_line_still_sets_the_box() {
    let lime = example();
    lime.ok_at(&at("2026-09-07", "10:50"), &["done", "^t3"]);
    assert!(lime.line("week/2026-W37.md", "t3").starts_with("- [x]"), "{}", lime.line("week/2026-W37.md", "t3"));
}

/// **D136 (P132)**: `lime stop` on a dropped line journals `stop ^t3 30m · line settled, left as it stands` — no
/// `5m left`. The log's `stop` keeps `remaining_min`: the log's grammar and fork 4748911's serde both require it
/// (README gap 5560).
#[test]
fn d136_stop_on_a_settled_line_journals_no_remainder_p132() {
    let lime = running_on("~");
    lime.ok_at(&at("2026-09-07", "10:50"), &["stop"]);
    let journal = lime.read("day/2026-09-07.md");
    let line = journal.lines().find(|l| l.starts_with("10:50 stop ^t3")).expect("the journal line");
    assert_eq!(line, "10:50 stop ^t3 30m · line settled, left as it stands", "{journal}");
    let stop = of(&lime, "stop");
    assert!(stop[0].get("remaining_min").is_some(), "the field the grammar requires: {stop:?}");
}

/// **D138 (P133)**: a cache woken at 08:00 (logged) holding a break started `11:00`, read at 10:05 — D81 places
/// it at yesterday's 11:00, before the logged wake — is not logged: the verb clears it from the cache and says why
/// in one line, and the plan draws no ten-hour break. The critic's d/K5.
#[test]
fn d138_a_cached_break_before_the_logged_wake_is_dropped_not_logged_p133() {
    let lime = Lime::empty();
    assert_eq!(lime.run(&["init", "--example"]).code, 0);
    lime.ok_at(&at("2026-09-08", "08:00"), &["wake"]);
    cache_break(&lime, "11:00", 15, Some("walk"));
    let out = lime.ok_at(&at("2026-09-08", "10:05"), &["plan"]);
    assert!(out.stderr.contains("(D138)") && out.stderr.contains("2026-09-07 11:00"), "not said: {}", out.stderr);
    assert!(of(&lime, "break_start").is_empty() && of(&lime, "break").is_empty(), "a break line was logged");
    assert!(lime.state()["break"].is_null(), "the cache still holds it: {}", lime.state());
    let again = lime.ok_at(&at("2026-09-08", "10:06"), &["plan"]);
    assert!(!again.stderr.contains("D138"), "said twice: {}", again.stderr);
}

/// **D138 does not reach a break placed after the logged wake** — D133 logs it, as before.
#[test]
fn d138_a_cached_break_after_the_logged_wake_is_still_logged() {
    let lime = Lime::empty();
    assert_eq!(lime.run(&["init", "--example"]).code, 0);
    lime.ok_at(&at("2026-09-08", "08:00"), &["wake"]);
    cache_break(&lime, "09:30", 15, None);
    lime.ok_at(&at("2026-09-08", "10:05"), &["plan"]);
    let logged = of(&lime, "break_start");
    assert_eq!(logged.len(), 1, "{logged:?}");
    assert_eq!(logged[0]["t"], "2026-09-08T09:30:00-05:00");
}

/// **D133 against D130** (the W-50 repair critic's first finding, the orchestrator's re-drive `v/I`): `^t3`
/// started 09-07 10:20 and left running, the cache holding a break `10:40` 15m at `walk` no `break_start` was
/// logged for; the first verb of 09-14 week-closes W37. D130's stop goes at the block's last logged activity, its
/// start (the logged `break_start` moves nothing: it is written after the close), the break is logged as D133
/// says at D81's instant, and no `break` line is stamped after the stop or before the break's start. Until the
/// repair the stop ended the break first: an orphan `{"ev":"break","actual_min":0}` at 09-13 10:40 after the
/// 09-07 stop, the journal's `10:20 break ended 0m/15m`, and no `break_start`.
#[test]
fn d133_holds_when_the_close_stops_a_block_beside_a_cache_only_break() {
    let lime = example();
    lime.ok_at(&at("2026-09-07", "10:20"), &["start", "^t3"]);
    cache_break(&lime, "10:40", 15, Some("walk"));
    let out = lime.ok_at(&at("2026-09-14", "10:00"), &["plan"]);
    assert!(out.stderr.contains("stopped ^t3 at 2026-09-07 10:20"), "{}", out.stderr);
    assert!(out.stderr.contains("(D133)"), "the break was not logged: {}", out.stderr);
    let stop = of(&lime, "stop");
    assert_eq!((stop.len(), stop[0]["t"].as_str()), (1, Some("2026-09-07T10:20:00-05:00")), "{stop:?}");
    assert!(of(&lime, "break").is_empty(), "a break line: {:?}", of(&lime, "break"));
    let started = of(&lime, "break_start");
    assert_eq!(started.len(), 1, "{started:?}");
    assert_eq!(started[0]["t"], "2026-09-13T10:40:00-05:00");
    assert_eq!(started[0]["where"], "walk");
    assert!(!lime.read("day/2026-09-07.md").contains("break ended"), "{}", lime.read("day/2026-09-07.md"));
    // D42: the break is the log's now, so deleting the cache draws the same day.
    let with = lime.json_at(&at("2026-09-14", "10:01"), &["plan"]);
    let _ = fs::remove_file(lime.plan.join(".tm/state.json"));
    let without = lime.json_at(&at("2026-09-14", "10:01"), &["plan"]);
    assert_eq!(with["segments"], without["segments"], "deleting the cache moved the day");
}

/// The duplicate `^t3` the W-50 repair auditor planted: a copy of the week's line in `backlog.md`, which the
/// kernel refuses as `notADemotion`.
fn refuse(lime: &Lime) {
    let line = lime.read("week/2026-W37.md").lines().find(|l| l.ends_with("^t3")).expect("^t3").to_string();
    let p = lime.plan.join("backlog.md");
    let text = fs::read_to_string(&p).expect("backlog");
    fs::write(&p, format!("{text}{line}\n")).expect("backlog");
}

/// **D133's refusal guard** (the W-50 repair auditor's drive): on a tree the kernel refuses, the verb that would
/// log a cache-only break writes nothing — no `break_start` — and asks the whole log once (gap 5523 as corrected:
/// it asked twice, from the reconcile and again from the logging step, on every verb, forever).
#[test]
fn d133_a_refused_tree_logs_no_cached_break_and_asks_the_whole_log_once() {
    let lime = Lime::empty();
    assert_eq!(lime.run(&["init", "--example"]).code, 0);
    lime.ok_at(&at("2026-09-08", "08:00"), &["wake"]);
    cache_break(&lime, "10:00", 15, None);
    refuse(&lime);
    let log = lime.read(".tm/log.jsonl");
    for verb in [&["plan"][..], &["now"][..], &["start", "^t1"][..]] {
        let out = lime.run_env_at(&at("2026-09-08", "10:05"), &[("LIME_TRACE_REPLAY_SCOPE", "1")], verb);
        assert!(out.stderr.contains("notADemotion"), "not refused: {}", out.stderr);
        assert_eq!(out.stderr.matches("replay scope: all").count(), 1, "`lime {}`: {}", verb.join(" "), out.stderr);
        assert_eq!(lime.read(".tm/log.jsonl"), log, "`lime {}` wrote the log", verb.join(" "));
    }
    assert!(of(&lime, "break_start").is_empty(), "a break_start was logged on a refused tree");
}

/// **The one whole-log replay on a tree that is not refused**: the verb that logs a cache-only break asks every
/// month once (it asked twice until the W-51 repair).
#[test]
fn d133_the_verb_that_logs_a_cached_break_asks_the_whole_log_once() {
    let lime = Lime::empty();
    assert_eq!(lime.run(&["init", "--example"]).code, 0);
    lime.ok_at(&at("2026-09-08", "08:00"), &["wake"]);
    cache_break(&lime, "10:00", 15, None);
    let out = lime.run_env_at(&at("2026-09-08", "10:05"), &[("LIME_TRACE_REPLAY_SCOPE", "1")], &["plan"]);
    assert_eq!(out.code, 0, "{}", out.stderr);
    assert!(out.stderr.contains("(D133)"), "{}", out.stderr);
    assert_eq!(out.stderr.matches("replay scope: all").count(), 1, "{}", out.stderr);
}

/// **A cache place the kernel's table does not know** (the critic's d/K3, README gap 5561): the break is logged
/// without it, and the next verb's reconcile names both places rather than printing two equal halves.
#[test]
fn d133_an_unknown_cached_place_is_named_by_the_next_reconcile() {
    let lime = Lime::empty();
    assert_eq!(lime.run(&["init", "--example"]).code, 0);
    lime.ok_at(&at("2026-09-08", "08:00"), &["wake"]);
    cache_break(&lime, "10:00", 15, Some("moon"));
    let first = lime.ok_at(&at("2026-09-08", "10:05"), &["plan"]);
    assert!(first.stderr.contains("its place \"moon\" is no word of the table"), "{}", first.stderr);
    let next = lime.ok_at(&at("2026-09-08", "10:06"), &["now"]);
    assert!(next.stderr.contains("(15m, moon)") && next.stderr.contains("(15m, no place)"), "{}", next.stderr);
}

/// **Gap 5509 — `log-taken-block` holds across runs.** The critic's C8: `^t3` started 09-07 10:20 (no wake
/// logged), a pre-D130 close of W37 took it, and the cache is gone. The first `lime check` is a genesis; the next
/// two are served from the checkpoint it wrote, whose `Hot` rows no longer hold the block's `start` (09-07 is
/// sealed). Until the repair they printed `no problems`.
#[test]
fn gap5509_three_checks_in_a_row_all_name_the_taken_block() {
    let lime = Lime::empty();
    assert_eq!(lime.run(&["init", "--example"]).code, 0);
    lime.ok_at(&at("2026-09-07", "10:20"), &["start", "^t3"]);
    lime.ok_at(&at("2026-09-14", "10:00"), &["now"]);
    let path = lime.plan.join(".tm/log.jsonl");
    let text = fs::read_to_string(&path).expect("the log");
    let kept: Vec<&str> = text.lines().filter(|l| !l.contains("\"ev\":\"stop\"") && !l.contains("\"ev\":\"wake\"")).collect();
    fs::write(&path, kept.join("\n") + "\n").expect("the log, as before D130");
    let _ = fs::remove_dir_all(lime.plan.join(".tm/cache"));
    let mut traces = Vec::new();
    for i in 1..=3 {
        let out = lime.run_env_at(&at("2026-09-14", "10:10"), &[("LIME_TRACE_REPLAY_SCOPE", "1")], &["check"]);
        assert!(out.stdout.contains("warning[log-taken-block]"), "run {i}: {}{}", out.stdout, out.stderr);
        traces.push(out.stderr);
    }
    assert!(traces[1].contains("replay scope: dates 2026-09-07..2026-09-14"), "the served run did not widen: {}", traces[1]);
}
