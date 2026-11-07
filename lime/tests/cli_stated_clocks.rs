//! **Hours since wake count from the wake that HAPPENED** — the W-41 repair
//! (README gap 4140; parity P79): `Ctx::woke_before_now`, the LATEST instant at
//! or before now with the wake's clock, the rule the campaign's D81 call (gap
//! 3820, P73) set for a running break's start. `.tm/state.json`'s `wake`
//! survives the midnight roll, so after local midnight fork 4748911 counted from
//! TONIGHT's wake and `lime energy` at 00:30 logged `hsw: -6.5` for a day woken at
//! 07:00 — a wrong fact the fit reads (D75's reason).
//!
//! `lime energy --at HH:MM` names today's clock unless that is more than twelve
//! hours after now, then yesterday's — the owner's D86 (README gap 4135, W-42
//! track H, parity P82; `cli_energy_at.rs`), which keeps fork 4748911's forward
//! report on the same day (`cli_day.rs`' pinned
//! `energy_logs_a_report_against_the_prediction` and its snapshot); a report it
//! dates yesterday counts its hours since that day's wake (`Ctx::woke_before`).

mod cli_common;

use cli_common::Lime;

/// A tree woken at 07:00 on Monday 2026-09-07.
fn woken_monday() -> Lime {
    let lime = Lime::new();
    lime.ok_at("2026-09-07T07:00:00-05:00", &["wake", "07:00"]);
    lime
}

/// Every `energy` line of the log, as JSON.
fn energy_lines(lime: &Lime) -> Vec<serde_json::Value> {
    lime.read(".tm/log.jsonl")
        .lines()
        .filter_map(|l| serde_json::from_str::<serde_json::Value>(l).ok())
        .filter(|v| v["ev"] == "energy")
        .collect()
}

/// **Hours since wake is counted from the wake that has happened** (P79): at
/// 23:30 Monday 16.5, and at 00:30 Tuesday — the state rolled, its `wake` kept —
/// 17.5, where fork 4748911 logged −6.5 (Tuesday's 07:00, still to come).
#[test]
fn hours_since_wake_after_midnight_count_from_the_wake_that_happened() {
    let lime = woken_monday();
    lime.ok_at("2026-09-07T23:30:00-05:00", &["energy", "3"]);
    lime.ok_at("2026-09-08T00:30:00-05:00", &["energy", "3"]);
    let lines = energy_lines(&lime);
    assert_eq!(lines.len(), 2, "{lines:?}");
    assert_eq!((lines[0]["t"].as_str(), lines[0]["hsw"].as_f64()), (Some("2026-09-07T23:30:00-05:00"), Some(16.5)));
    assert_eq!((lines[1]["t"].as_str(), lines[1]["hsw"].as_f64()), (Some("2026-09-08T00:30:00-05:00"), Some(17.5)));
    assert_eq!(lime.state()["wake"], "07:00", "the roll kept the wake: {}", lime.state());
}
