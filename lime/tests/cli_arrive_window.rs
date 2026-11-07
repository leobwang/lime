//! **The window `lime arrive` stores is the KERNEL's** — README gap **4746** (parity **P113**, W-47
//! track H), driven through the binary.
//!
//! Until W-47 `Ctx::arrival_window` was the host's `capacity::window_and_budget` over
//! `Tree::walls_on` (fork `Ctx::walls_on`), and once stored the kernel's day read that window back
//! (gap 320's reading) — so the walls that decided the day's window after an arrive were the host's
//! reading beside the kernel's. It is the kernel's day now: the request every planning verb sends,
//! over the state the arrival leaves, and the window (`Planner.PlanReq.window`, `Look.windowEnd` over
//! the day's walls clipped to it) and budget (`Look.budgetOf`) the kernel plans that day by.
//!
//! **What moves, measured**: nothing on the repository's four plan fixtures (152 arrivals, every
//! half hour from 05:00 to 23:30 — README "Stage 6 — W-47 track H" §4). A wall that runs past
//! midnight moves it: the host extended the window by the wall's whole span into tomorrow, the
//! kernel by its part of the day — an overnight shift from 18:30 to 01:30, arrived at at 11:00,
//! stored `11:00–03:00` on fork 4748911 and `11:00–01:30` here, and `lime plan` plans the day by the
//! window stored, so the two now say one thing.

mod cli_common;

use cli_common::Lime;
use serde_json::Value;

/// `HH:MM` on Monday 2026-09-07, Chicago.
fn at(hhmm: &str) -> String {
    format!("2026-09-07T{hhmm}:00-05:00")
}

/// The example tree (`lime init --example`), with `wall` appended to this week's calendar.
fn example_with(wall: Option<&str>) -> Lime {
    let lime = Lime::empty();
    assert_eq!(lime.run(&["init", "--example"]).code, 0);
    if let Some(w) = wall {
        let mut cal = lime.read("calendar/2026-W37.md");
        cal.push_str(w);
        cal.push('\n');
        std::fs::write(lime.plan.join("calendar/2026-W37.md"), cal).expect("write the calendar");
    }
    lime
}

/// An overnight shift, from 18:30 today to 01:30 tomorrow.
const OVERNIGHT: &str = "- [ ] 1 Overnight shift          at:2026-09-07T18:30/01:30 ^g8";

/// `.tm/state.json`'s window and budget.
fn stored(lime: &Lime) -> (Value, Value) {
    let s = lime.state();
    (s["window"].clone(), s["budget"].clone())
}

/// **The behaviour row**: an arrival at 11:00 before an overnight shift stores the kernel's window,
/// `11:00–01:30` (the shift's part of the day), where fork 4748911's host formula stored
/// `11:00–03:00` — and the log's `arrive` line, `lime arrive`'s own line and `lime plan`'s window all
/// say the one window.
#[test]
fn an_overnight_wall_extends_the_stored_window_by_its_part_of_the_day() {
    let lime = example_with(Some(OVERNIGHT));
    let out = lime.ok_at(&at("11:00"), &["arrive", "lounge"]);
    assert_eq!(out.stdout.trim(), "arrive lounge 11:00 · window 11:00–01:30 · budget 6 blocks", "{}", out.stdout);
    assert_eq!(stored(&lime), (serde_json::json!(["11:00", "01:30"]), serde_json::json!(6)));
    let arrive = lime.last_ev("arrive");
    assert_eq!(arrive["window"], serde_json::json!(["11:00", "01:30"]), "{arrive}");
    let plan = lime.json_at(&at("11:05"), &["plan"]);
    assert_eq!(plan["window"], serde_json::json!(["11:00", "01:30"]), "the day is planned by the window stored");
    assert_eq!(plan["budget_blocks"], 6);
}

/// **No over-bite**: with no wall past midnight the kernel's window is the one the host formula
/// gave — the example tree's 12:50 meeting extends an 07:00 arrival's eight hours to 16:00, and an
/// arrival after `window_cap` (19:00) gets an empty window.
#[test]
fn without_a_wall_past_midnight_the_window_is_the_formulas() {
    let lime = example_with(None);
    lime.ok_at(&at("07:00"), &["arrive", "lounge"]);
    assert_eq!(stored(&lime), (serde_json::json!(["07:00", "16:00"]), serde_json::json!(6)));
    let lime = example_with(None);
    lime.ok_at(&at("20:00"), &["arrive", "lounge"]);
    assert_eq!(stored(&lime).0, serde_json::json!(["20:00", "20:00"]));
}

/// **D42's rebuild derives the kernel's window too** (D45: one definition for the writer and the
/// derivation): on a day of two arrivals the log carries only the first one's payload, so deleting
/// `.tm/state.json` recomputes the second's — and it is the window the second `lime arrive` stored.
#[test]
fn the_rebuild_of_a_two_arrival_day_recomputes_the_kernels_window() {
    let lime = example_with(Some(OVERNIGHT));
    lime.ok_at(&at("09:00"), &["arrive", "home"]);
    lime.ok_at(&at("11:00"), &["arrive", "lounge"]);
    let before = stored(&lime);
    assert_eq!(before.0, serde_json::json!(["11:00", "01:30"]), "{:?}", before);
    std::fs::remove_file(lime.plan.join(".tm/state.json")).expect("delete the runtime state");
    let now = lime.run_at(&at("11:10"), &["--json", "now"]);
    assert_eq!(now.code, 0, "{}{}", now.stdout, now.stderr);
    assert!(now.stderr.contains("RECOMPUTED rather than restored: `window` and `budget`"), "{}", now.stderr);
    assert_eq!(stored(&lime), before, "the rebuild recomputed another window than `lime arrive` stored");
}

/// **A day the kernel refuses gets no window back, and the rebuild says so by the refusal** (the
/// other direction of the test above): since the recompute is the kernel's day request, on a tree
/// whose capacity input the kernel refuses by file and key (P26 — a `.tm/model.json` weight above
/// one) the rebuild of a two-arrival day stores no window and no budget, names the refusal on
/// stderr, and does not claim to have recomputed them; a verb that computes no capacity still runs.
#[test]
fn a_refused_day_recomputes_no_window_and_names_the_refusal() {
    let lime = example_with(None);
    lime.ok_at(&at("09:00"), &["arrive", "home"]);
    lime.ok_at(&at("11:00"), &["arrive", "lounge"]);
    std::fs::write(lime.plan.join(".tm/model.json"), r#"{"p_lounge": {"Mon": 1.2}}"#).expect("model");
    std::fs::remove_file(lime.plan.join(".tm/state.json")).expect("delete the runtime state");
    let out = lime.run_at(&at("11:10"), &["add", "Buy stamps", "--to", "week"]);
    assert_eq!(out.code, 0, "{}{}", out.stdout, out.stderr);
    assert!(
        out.stderr.contains(
            "lime: NOT recomputed: `window` and `budget` — the kernel refused the day's request \
             (.tm/model.json: p_lounge.Mon = 1.2 is outside [0, 1]"
        ),
        "{}",
        out.stderr
    );
    assert!(!out.stderr.contains("RECOMPUTED rather than restored: `window`"), "{}", out.stderr);
    let (window, budget) = stored(&lime);
    assert!(window.is_null() && budget.is_null(), "nothing stands for them: {window} {budget}");
    assert_eq!(lime.state()["arrival"], "11:00", "the arrival is the log's: {}", lime.state());
}
