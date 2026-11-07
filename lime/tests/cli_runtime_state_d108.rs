//! **`.tm/state.json`'s two remaining host-only values are derived from the log** — the owner's
//! **D108** (README gaps 4893 and 4876, parity **P119**, W-48 track A), driven through the binary.
//! These are P119's behaviour rows.
//!
//! Fork 4748911 rebuilt no `.tm/state.json`; this branch has since D42, and until D108 two values
//! came back as other values: `priorities_yesterday` (§7.4's hysteresis input after the day's first
//! plan) came back empty, so a damped item re-ranked and a `plan` line was logged; and
//! `active.est_min` after `lime extend` came back as the extended line times the learned multiplier,
//! `round((r + by)·m)`, where the verbs had written `round(r·m) + by`. Now the day's first `plan`
//! line carries the hysteresis input and the replay holds the open block's own extends, so deleting
//! the file after the day's first plan, mid-extend or mid-break moves nothing: the rebuilt file is
//! the deleted one, and `lime now`, `lime plan --json` and the log are byte-identical across the
//! deletion.

mod cli_common;

use cli_common::Lime;
use serde_json::Value;

/// A stamp on 2026-09-07 or 08, Chicago.
fn at(day: u32, hhmm: &str) -> String {
    format!("2026-09-{day:02}T{hhmm}:00-05:00")
}

/// The example tree (`lime init --example`, §4.3's), initialised at 08:00 on 2026-09-07.
fn example() -> Lime {
    let lime = Lime::empty();
    assert_eq!(lime.run_at(&at(7, "08:00"), &["init", "--example"]).code, 0);
    lime
}

fn state(lime: &Lime) -> Value {
    serde_json::from_str(&lime.read(".tm/state.json")).expect(".tm/state.json is JSON")
}

/// What a deletion must not move, asked at `now`: `lime now`'s text, `lime plan --json`'s bytes.
fn answers(lime: &Lime, now: &str) -> (String, String) {
    let now_text = lime.ok_at(now, &["now"]).stdout;
    let plan = lime.ok_at(now, &["--json", "plan"]).stdout;
    (now_text, plan)
}

/// Delete `.tm/state.json` and assert the rebuild is the deleted file, the answers and the log
/// unchanged; returns the first verb's stderr (the rebuild's notice).
fn delete_and_compare(lime: &Lime, now: &str) -> String {
    // Settle first: the answers above are asked twice so a first-call housekeeping write is
    // not mistaken for the deletion's.
    let _ = answers(lime, now);
    let before_state = state(lime);
    let before = answers(lime, now);
    let before_log = lime.read(".tm/log.jsonl");
    std::fs::remove_file(lime.plan.join(".tm/state.json")).expect("delete the runtime state");
    let first = lime.run_at(now, &["--json", "now"]);
    assert_eq!(first.code, 0, "the first verb after the deletion failed: {}{}", first.stdout, first.stderr);
    assert!(first.stderr.contains("rebuilt from .tm/log.jsonl"), "the rebuild said nothing: {}", first.stderr);
    assert_eq!(state(lime), before_state, "the rebuilt runtime state is not the deleted one");
    let after = answers(lime, now);
    assert_eq!(after.0, before.0, "`lime now` moved across the deletion");
    assert_eq!(after.1, before.1, "`lime plan --json` moved across the deletion");
    assert_eq!(lime.read(".tm/log.jsonl"), before_log, "the deletion wrote to the log");
    first.stderr
}

/// **After the day's first plan, the damping binding** (gap 4893's world): `^hy1`, 1 block on
/// day 1, grows to 9 blocks overnight (a hand edit); the day's first plan holds it at p5 against
/// yesterday's p6. The plan line carries the map; the deletion keeps p5, the hash and the log.
#[test]
fn deleting_the_runtime_state_after_the_days_first_plan_keeps_the_hysteresis_p119() {
    let lime = example();
    let backlog = lime.read("backlog.md").replace(
        "# Untied\n",
        "# Untied\n- [ ] 3 1b Grant report  due:2026-09-11 ^hy1\n",
    );
    std::fs::write(lime.plan.join("backlog.md"), backlog).expect("write backlog.md");
    lime.ok_at(&at(7, "09:00"), &["plan"]);
    let grown = lime.read("backlog.md").replace("- [ ] 3 1b Grant report", "- [ ] 3 9b Grant report");
    std::fs::write(lime.plan.join("backlog.md"), grown).expect("write backlog.md");
    lime.ok_at(&at(8, "09:00"), &["plan"]);

    // The bite: the day's first plan line carries the map, the cache holds it, and it binds.
    let plans: Vec<Value> = lime
        .read(".tm/log.jsonl")
        .lines()
        .map(|l| serde_json::from_str::<Value>(l).expect("a log line"))
        .filter(|v| v["ev"] == "plan")
        .collect();
    assert_eq!(plans.len(), 2, "one plan a day: {plans:?}");
    assert!(plans[0].get("yesterday").is_none(), "day 1's first plan had no yesterday to carry: {}", plans[0]);
    assert_eq!(plans[1]["yesterday"]["hy1"], 6, "day 2's first plan carries day 1's p: {}", plans[1]);
    assert_eq!(state(&lime)["priorities_yesterday"]["hy1"], 6);
    let p = lime.json_at(&at(8, "09:00"), &["plan"]);
    let hy1 = p["priorities"].as_array().expect("priorities").iter().find(|x| x["id"] == "hy1").expect("hy1");
    assert_eq!(hy1["p"], 5, "§7.4 holds ^hy1 one bin better than yesterday's 6: {hy1}");

    let notice = delete_and_compare(&lime, &at(8, "09:00"));
    assert!(
        notice.contains("RESTORED from the log: `priorities_yesterday`"),
        "the notice does not say the hysteresis map came back: {notice}"
    );
}

/// **Mid-extend, under a learned multiplier** (gap 4876's world): `^t3` (`1b`, 78 minutes at
/// ×1.3) started at 09:00 and extended 25 minutes and 1 block: `lime extend` says `now 163m`, and the
/// rebuild says 163 (`round(60 × 1.3) + 85`), not `round(145 × 1.3)` = 189.
#[test]
fn deleting_the_runtime_state_mid_extend_keeps_the_planned_minutes_p119() {
    let lime = example();
    std::fs::write(lime.plan.join(".tm/model.json"), r#"{"duration": {"_default": 1.3}}"#).expect("model");
    lime.ok_at(&at(7, "09:00"), &["start", "^t3"]);
    let one = lime.ok_at(&at(7, "09:20"), &["extend", "25m"]);
    assert!(one.stdout.contains("now 103m"), "{}", one.stdout);
    let two = lime.ok_at(&at(7, "09:40"), &["extend", "1b"]);
    assert!(two.stdout.contains("now 163m"), "{}", two.stdout);
    assert_eq!(state(&lime)["active"]["est_min"], 163);
    // One estimate since the owner's D127 (parity P126): `lime extend` rewrites the leading `1b` (D62).
    assert_eq!(lime.line("week/2026-W37.md", "t3"), "- [>] 4 2h25m Exercises 5.3–5.5            @m1 ^t3");

    let notice = delete_and_compare(&lime, &at(7, "09:50"));
    assert!(
        notice.contains("RESTORED from the log: `active.est_min` is 163m")
            && notice.contains("plus the 85m its logged `extend` lines added"),
        "the notice does not say the planned minutes came back: {notice}"
    );
}

/// **Mid-break**: the extend world with one extend, then `lime break 15m` at 09:30 — the break and
/// its pause come back from the `break_start` (D105) and the planned minutes from the extend (D108).
#[test]
fn deleting_the_runtime_state_mid_break_keeps_the_planned_minutes_p119() {
    let lime = example();
    std::fs::write(lime.plan.join(".tm/model.json"), r#"{"duration": {"_default": 1.3}}"#).expect("model");
    lime.ok_at(&at(7, "09:00"), &["start", "^t3"]);
    lime.ok_at(&at(7, "09:20"), &["extend", "25m"]);
    lime.ok_at(&at(7, "09:30"), &["break", "15m"]);
    let s = state(&lime);
    assert_eq!(s["active"]["est_min"], 103);
    assert_eq!(s["active"]["paused"], true);
    assert_eq!(s["break"]["planned_min"], 15);

    let notice = delete_and_compare(&lime, &at(7, "09:35"));
    assert!(notice.contains("RESTORED from the log: `break`"), "{notice}");
    assert!(notice.contains("RESTORED from the log: `active.est_min` is 103m"), "{notice}");
}
