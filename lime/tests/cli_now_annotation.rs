//! **`lime now`'s line under the running block's row reads the BLOCK** — the owner's **D109** (README
//! gap 4894, parity **P111**, W-47 track H), driven through the binary.
//!
//! The line under the current row was the SEGMENT's span on every row: `elapsed` since the segment
//! began and `left` until it ends. A running block's current segment begins at `now`, so beside
//! the header's `30m of 60m` it said `elapsed 0m`; and in overtime P46's reservation to the end of
//! its block made the segment 45 minutes long, so under a row whose own note said `running · 0m
//! left` it said `left 45m` — two readings of one block on one screen (AGENTS §5.3). Now it reads
//! the header's two numbers: `elapsed` the minutes worked, `left` the estimate less them. Under
//! any other row (nothing running, a wall, a routine) the segment's span is what elapses, and it
//! is read as before.

mod cli_common;

use cli_common::Lime;

/// `HH:MM` on Monday 2026-09-07, Chicago.
fn at(hhmm: &str) -> String {
    format!("2026-09-07T{hhmm}:00-05:00")
}

/// The example tree with `^t3` running from 09:50 — gap 4894's world.
fn running() -> Lime {
    let lime = Lime::empty();
    assert_eq!(lime.run(&["init", "--example"]).code, 0);
    lime.ok_at(&at("09:50"), &["start", "^t3", "--energy", "3"]);
    lime
}

/// `lime now`'s lines.
fn now(lime: &Lime, hhmm: &str) -> Vec<String> {
    lime.ok_at(&at(hhmm), &["now"]).stdout.lines().map(str::to_string).collect()
}

/// **Outside overtime**: `30m of 60m` in the header, and `elapsed 30m · left 30m` under the
/// running row — where the segment's span said `elapsed 0m`.
#[test]
fn the_running_rows_line_reads_the_minutes_worked() {
    let lime = running();
    let lines = now(&lime, "10:20");
    assert_eq!(lines[0], "▶ ^t3 Exercises 5.3–5.5 · started 09:50 · 30m of 60m", "{lines:#?}");
    assert!(lines[1].contains("▶ Exercises 5.3–5.5") && lines[1].ends_with("running · 30m left"), "{lines:#?}");
    assert_eq!(lines[2], "  10:20–10:50 · elapsed 30m · left 30m", "{lines:#?}");
}

/// **In overtime**: `75m of 60m`, the row's `running · 0m left` (P46), and `left 0m` under it —
/// where the reservation's span said `left 45m`.
#[test]
fn in_overtime_the_line_says_nothing_is_left_as_the_row_does() {
    let lime = running();
    let lines = now(&lime, "11:05");
    assert_eq!(lines[0], "▶ ^t3 Exercises 5.3–5.5 · started 09:50 · 75m of 60m", "{lines:#?}");
    assert!(lines[1].ends_with("running · 0m left"), "{lines:#?}");
    assert_eq!(lines[2], "  11:05–11:50 · elapsed 1h15m · left 0m", "{lines:#?}");
}

/// **No over-bite**: with nothing running, the current row is no block's, and its line is the
/// segment's span, as it was — and so is a wall's row over a running block (D61's meeting).
#[test]
fn with_nothing_running_the_line_reads_the_segment() {
    let lime = Lime::empty();
    assert_eq!(lime.run(&["init", "--example"]).code, 0);
    let lines = now(&lime, "13:10");
    assert_eq!(lines[0], "nothing running", "{lines:#?}");
    assert!(lines[1].contains("Meeting w/ host"), "the 12:50 meeting is current: {lines:#?}");
    assert_eq!(lines[2], "  12:50–13:50 · elapsed 20m · left 40m", "{lines:#?}");
    // And a running block whose row is not the current one: the meeting's span is read.
    let lime = running();
    let lines = now(&lime, "13:10");
    assert!(lines[1].contains("Meeting w/ host"), "the meeting is current over ^t3: {lines:#?}");
    assert_eq!(lines[2], "  12:50–13:50 · elapsed 20m · left 40m", "{lines:#?}");
}
