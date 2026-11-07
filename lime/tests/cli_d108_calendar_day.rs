//! **The owner's D108 over a calendar day's plans, wherever the replay files them** (the W-48 repair, README gaps
//! 5210 and 5211).
//!
//! * **Midnight to the wake** (gap 5210). Driven by the W-48 auditor and critic on the landed binary (`4aa44da`): a
//!   `plan` written after local midnight and before the next wake is filed by the replay under the previous ledger
//!   day, while `.tm/state.json` keeps its plan facts by calendar day. So every such `plan` was written as the day's
//!   first (each carried the whole hysteresis map), and D42's rebuild, reading the calendar date's ledger day, found
//!   none of them: deleting the cache at 00:35 re-ranked `^x2` (`p5` damped → `p3`), moved the plan's hash, logged a
//!   `plan` line and said nothing — and the next whole day lost its damping.
//! * **Two machines on one synced log** (gap 5211). The template syncs `.tm/log.jsonl` and the Markdown and keeps
//!   `.tm/state.json` and `.tm/last_plan.json` per machine. The rebuild read the log's input, but §7.4's ranking read
//!   each machine's cache, so one log ranked `^hy1` `p3` on the machine that planned and `p5` on the other.

mod cli_common;

use cli_common::Lime;
use std::path::Path;

fn at(day: &str, hm: &str) -> String {
    format!("{day}T{hm}:00-05:00")
}

const MON: &str = "2026-09-07";
const TUE: &str = "2026-09-08";

/// Copy a plan directory, leaving out the per-machine files the template does not sync when `sync` is set.
fn copy(from: &Path, to: &Path, sync: bool) {
    std::fs::create_dir_all(to).expect("create");
    for e in std::fs::read_dir(from).expect("read") {
        let e = e.expect("entry");
        let rel = e.file_name().into_string().expect("utf-8");
        let (src, dst) = (e.path(), to.join(&rel));
        if sync && (rel == "state.json" || rel == "last_plan.json" || rel == "cache") {
            continue;
        }
        if e.file_type().expect("type").is_dir() {
            copy(&src, &dst, sync);
        } else {
            std::fs::copy(&src, &dst).expect("copy");
        }
    }
}

/// `(p, raw_p, hysteresis_applied)` of `id` in `lime --json plan` at `now`.
fn rank(lime: &Lime, now: &str, id: &str) -> (u64, u64, bool) {
    let v = lime.json_at(now, &["plan"]);
    let p = v["priorities"].as_array().expect("priorities").iter().find(|p| p["id"] == id).unwrap_or_else(|| panic!("{id}: {v}"));
    (p["p"].as_u64().expect("p"), p["raw_p"].as_u64().expect("raw_p"), p["hysteresis_applied"].as_bool().expect("flag"))
}

/// The plan lines of the log, raw.
fn plan_lines(lime: &Lime) -> Vec<String> {
    lime.read(".tm/log.jsonl").lines().filter(|l| l.contains("\"ev\":\"plan\"")).map(str::to_string).collect()
}

/// The auditor's world: the example tree woken 07:00 and arrived 08:00 on Monday, planned 08:05 and 22:00, then planned
/// at 00:26 on Tuesday and `^x2`'s due moved at 00:30 — before Tuesday's wake.
fn midnight() -> Lime {
    let lime = Lime::empty();
    lime.ok_at(&at(MON, "06:00"), &["init", "--example"]);
    lime.ok_at(&at(MON, "07:00"), &["wake", "07:00"]);
    lime.ok_at(&at(MON, "08:00"), &["arrive"]);
    lime.ok_at(&at(MON, "08:05"), &["plan"]);
    lime.ok_at(&at(MON, "22:00"), &["plan"]);
    lime.ok_at(&at(TUE, "00:26"), &["plan"]);
    lime.ok_at(&at(TUE, "00:30"), &["edit", "^x2", "due=2026-09-12T20:00"]);
    lime
}

/// **The driven reproduction** (gap 5210): with the cache and without it, at 00:40, `^x2` ranks one way, the two trees
/// log the same `plan` line, and the rebuilt state holds the same input — and the next day, after its wake, still
/// ranks one way.
#[test]
fn deleting_the_cache_before_the_wake_moves_nothing() {
    let a = midnight();
    let b = Lime::empty();
    copy(&a.plan, &b.plan, false);
    std::fs::remove_file(b.plan.join(".tm/state.json")).expect("delete the cache");
    let now = at(TUE, "00:40");
    assert_eq!(rank(&a, &now, "x2"), rank(&b, &now, "x2"), "one ranking with the cache and without it");
    assert_eq!(plan_lines(&a), plan_lines(&b), "the two trees log the same plan lines");
    assert_eq!(a.state()["priorities_yesterday"], b.state()["priorities_yesterday"]);
    for lime in [&a, &b] {
        lime.ok_at(&at(TUE, "07:00"), &["wake", "07:00"]);
        lime.ok_at(&at(TUE, "08:00"), &["arrive"]);
    }
    let later = at(TUE, "08:30");
    assert_eq!(rank(&a, &later, "x2"), rank(&b, &later, "x2"), "and the next day after its wake");
}

/// **A calendar day's input is written once** (gap 5210): of Tuesday's `plan` lines before its wake, the first carries
/// the hysteresis input and no later one does — they used to carry it on every one.
#[test]
fn a_calendar_days_input_is_written_on_its_first_plan_only() {
    let lime = midnight();
    lime.ok_at(&at(TUE, "01:30"), &["plan"]);
    lime.ok_at(&at(TUE, "02:30"), &["edit", "^x2", "due=2026-09-13T20:00"]);
    lime.ok_at(&at(TUE, "02:31"), &["plan"]);
    let tuesday: Vec<String> = plan_lines(&lime).into_iter().filter(|l| l.contains(TUE)).collect();
    assert!(tuesday.len() >= 2, "{tuesday:#?}");
    assert!(tuesday[0].contains("\"yesterday\""), "{}", tuesday[0]);
    assert!(tuesday[1..].iter().all(|l| !l.contains("\"yesterday\"")), "{tuesday:#?}");
}

/// The critic's world: `^hy1` added to the example's backlog, planned Monday 09:00 on machine A, copied to B; A makes
/// it 9b at 20:00 and plans; on Tuesday A wakes, arrives and plans at 09:00, and the log and the Markdown are synced to
/// B.
fn two_machines() -> (Lime, Lime) {
    let a = Lime::empty();
    a.ok_at(&at(MON, "06:00"), &["init", "--example"]);
    let backlog = a.read("backlog.md").replacen("# Untied\n", "# Untied\n- [ ] 3 1b Grant report  due:2026-09-11 ^hy1\n", 1);
    std::fs::write(a.plan.join("backlog.md"), backlog).expect("backlog");
    a.ok_at(&at(MON, "07:00"), &["wake", "07:00"]);
    a.ok_at(&at(MON, "08:00"), &["arrive"]);
    a.ok_at(&at(MON, "09:00"), &["plan"]);
    let b = Lime::empty();
    copy(&a.plan, &b.plan, false);
    a.ok_at(&at(MON, "20:00"), &["edit", "^hy1", "est=9b"]);
    a.ok_at(&at(MON, "20:00"), &["plan"]);
    a.ok_at(&at(TUE, "07:00"), &["wake", "07:00"]);
    a.ok_at(&at(TUE, "08:00"), &["arrive"]);
    a.ok_at(&at(TUE, "09:00"), &["plan"]);
    copy(&a.plan, &b.plan, true);
    (a, b)
}

/// **The driven reproduction** (gap 5211): one synced log ranks `^hy1` one way on both machines — and deleting the
/// second machine's cache moves nothing.
#[test]
fn two_machines_on_one_synced_log_rank_one_way() {
    let (a, b) = two_machines();
    let now = at(TUE, "09:30");
    let ranked = rank(&a, &now, "hy1");
    assert_eq!(rank(&b, &now, "hy1"), ranked, "the second machine ranks as the first");
    std::fs::remove_file(b.plan.join(".tm/state.json")).expect("delete the cache");
    assert_eq!(rank(&b, &at(TUE, "09:31"), "hy1"), rank(&a, &at(TUE, "09:31"), "hy1"), "and without its cache");
}
