//! **The running break drawn from where the logged breaks stop** — stage 6 W-53 repair track K, the W-53 critic's F3
//! (D142; P136's register row corrected).
//!
//! A hand-written `break` 10:20 for twenty, then a break begun at 10:30 for twenty (`lime break 20m`'s `break_start`): until this step `lime plan` drew `10:20 break
//! 20m` and `10:30 break …`, the stretch 10:30–10:40 twice.  The planner now draws the running break from 10:40, where the
//! logged break stops (`Planner.brkCover`).

mod cli_common;

use std::fs::OpenOptions;
use std::io::Write;

use cli_common::Lime;

const TUE: &str = "2026-09-08";

fn at(hm: &str) -> String {
    format!("{TUE}T{hm}:00-05:00")
}

/// The plan's break rows, as `HH:MM break …` with the `·` separators dropped.
fn break_rows(lime: &Lime, now: &str) -> Vec<String> {
    let out = lime.ok_at(&at(now), &["plan"]);
    out.stdout
        .lines()
        .filter(|l| l.contains("break") && l.trim_start().starts_with(['0', '1']))
        .map(|l| l.split_whitespace().filter(|w| *w != "·").collect::<Vec<_>>().join(" "))
        .collect()
}

#[test]
fn a_running_break_begun_inside_a_logged_one_is_drawn_from_where_it_stops() {
    let lime = Lime::empty();
    lime.ok_at(&at("06:00"), &["init", "--example"]);
    lime.ok_at(&at("07:00"), &["wake", "07:00"]);
    lime.ok_at(&at("08:00"), &["arrive", "home"]);
    let mut f = OpenOptions::new().append(true).open(lime.plan.join(".tm/log.jsonl")).expect("the log");
    writeln!(f, r#"{{"t":"{}","ev":"break","planned_min":20,"actual_min":20}}"#, at("10:20")).expect("append");
    // the running break as `lime break 20m` at 10:30 logs it (D105), written by hand so the subject is the kernel's reading
    writeln!(f, r#"{{"t":"{}","ev":"break_start","planned_min":20}}"#, at("10:30")).expect("append");
    drop(f);
    let rows = break_rows(&lime, "10:45");
    assert!(rows.iter().any(|r| r.starts_with("10:20 break 20m")), "{rows:?}");
    assert!(rows.iter().any(|r| r.starts_with("10:40 break")), "{rows:?}");
    assert!(!rows.iter().any(|r| r.starts_with("10:30 break")), "{rows:?}");
}
