//! §13 `lime now`, §12.1's diagnostics pane, §7.3's impossible banner, §11's
//! energy mix (the day bar's legend) and §16's palette.
//!
//! Moved from `lime-core/tests/` at W-47 with the fixture it shares: since the
//! owner's D112 a day's rows are the kernel's cells (`emit_fixture::with_rows`),
//! and `lime now` prints a window of them. The snapshots are unchanged — the
//! Rust builder wrote them, the kernel's rows meet them. The test of
//! render_now, the default-config variant, went with that function: `lime now`
//! takes no config since its rows stopped needing one.

mod emit_fixture;

use emit_fixture::{at, config, plan, prio, tree, with_rows};
use lime_core::emit;
use lime_core::model::{Dep, Id};
use lime_core::dayplan::{DayPlan, Diagnostics, SegKind};
use lime_core::priority::PrioClass;

#[test]
fn now_shows_the_current_block_and_the_next_three() {
    let day = plan();
    let now = at(10, 42);
    let out = emit::render_now_with(&day, now, None);
    // 09:20 → 11:20, so at 10:42: 1h22m gone, 38m left.
    assert!(out.contains("▶ Exercises 5.3–5.5"));
    assert!(out.contains("elapsed 1h22m · left 38m"));

    // **D30 Q5 (a), W-23**: `lime now` SELECTS rows, it does not render them.
    // Every line but the two annotations is a row of the day file, byte for
    // byte — and it is taken by POSITION out of `plan_rows`, never looked up
    // by what it says, because two items with one title give byte-identical
    // rows (README gap **1197**).
    //
    // This assertion used to count lines beginning `"  1"`, which is what a
    // second renderer's indentation looked like; three such lines is a fact
    // about a format string and not about agreement between two surfaces.
    let rows = emit::plan_rows(&day, &emit::Layout::default());
    let (current, next) = emit::now_window(&day, now);
    assert_eq!(next.len(), 3, "§13: the current block and the next three");
    let printed: Vec<&str> = out
        .lines()
        .filter(|l| !l.starts_with("  ") && *l != "next")
        .collect();
    let want: Vec<&str> = current
        .into_iter()
        .chain(next)
        .map(|i| rows[i].as_str())
        .collect();
    assert_eq!(printed, want, "`lime now` printed something that is not a row");
    insta::assert_snapshot!("now_current", out);
}

/// **The owner's D109 (README gap 4894, parity P111): the line under the running block's row
/// reads the BLOCK** — `elapsed` the minutes worked, `left` the estimate less them, the two
/// numbers `lime now`'s header prints (`75m of 192m`) — and not the segment's span. Both
/// directions: under the running block's row the block is read; under any other row (here the
/// running item is another one) the segment's span still elapses; in overtime `left` is `0m`, as
/// the row's own `running · 0m left` (P46) says.
#[test]
fn the_line_under_the_running_row_reads_the_block() {
    let day = plan();
    let now = at(10, 42);
    let t3 = Id::new("t3");
    let running = emit::Running { id: &t3, worked_min: 75, est_min: 192 };
    let out = emit::render_now_with(&day, now, Some(&running));
    assert!(out.contains("▶ Exercises 5.3–5.5"), "{out}");
    assert!(
        out.contains("  09:20–11:20 · elapsed 1h15m · left 1h57m\n"),
        "the running row's line reads the block's 75m of 192m: {out}"
    );
    assert!(!out.contains("elapsed 1h22m"), "the segment's span is not read under the running row: {out}");
    // The rows are untouched: the same selection as without a running block, line for line.
    let plain = emit::render_now_with(&day, now, None);
    let rows = |s: &str| s.lines().filter(|l| !l.starts_with("  ")).map(str::to_string).collect::<Vec<_>>();
    assert_eq!(rows(&out), rows(&plain), "D109 moves the annotation and nothing else");
    assert!(plain.contains("elapsed 1h22m · left 38m"), "with nothing running the span is read: {plain}");

    // Another item running: the current row is not its row, so the segment's span is read.
    let t4 = Id::new("t4");
    let other = emit::Running { id: &t4, worked_min: 75, est_min: 192 };
    assert_eq!(emit::render_now_with(&day, now, Some(&other)), plain);

    // Overtime: worked past the estimate, nothing is left.
    let over = emit::Running { id: &t3, worked_min: 200, est_min: 192 };
    assert_eq!(over.minutes_left(), 0);
    assert!(
        emit::render_now_with(&day, now, Some(&over)).contains("· elapsed 3h20m · left 0m\n"),
        "overtime reads 0m left"
    );
}

#[test]
fn now_says_so_when_nothing_is_running() {
    let mut day = plan();
    day.segments.retain(|s| !matches!(s.kind, SegKind::Wall));
    let day = with_rows(day);
    let out = emit::render_now_with(&day, at(13, 20), None);
    assert!(out.starts_with("— nothing running (13:20)"));
    insta::assert_snapshot!("now_idle", out);

    // Past the last segment there is nothing to come either.
    let out = emit::render_now_with(&day, at(23, 0), None);
    assert_eq!(out, "— nothing running (23:00)\nnext   —\n");
}

#[test]
fn diagnostics_read_like_the_tui_pane() {
    let cfg = config();
    let tree = tree(&cfg);
    let mut diag = Diagnostics {
        underused: vec![(Id::new("t4"), 4, 3)],
        blocked: vec![(Id::new("t5"), vec![Dep::Item(Id::new("t4"))])],
        ..Diagnostics::default()
    };
    let lines = emit::render_diagnostics(&diag, &tree, &cfg);
    // §12.1's two example lines.
    assert_eq!(lines[0], "1 underused (4→3) · 0 ci-5 lost");
    assert_eq!(lines[1], "t5 blocked by t4");

    diag.a_capacity_lost = 120;
    diag.hot = vec![Id::new("a3")];
    diag.impossible = vec![(
        Id::new("d1"),
        180,
        chrono::NaiveDate::from_ymd_opt(2026, 9, 11).expect("date"),
    )];
    diag.conflicts = vec![(Id::new("g1"), Id::new("g2"))];
    diag.waiting = vec![Id::new("a4")];
    diag.deferred = vec![Id::new("x2")];
    diag.dropped_tail = vec![Id::new("t5")];
    diag.rest_debt_min = 40;
    diag.plan_honesty = Some(1.25);
    diag.notes = vec!["replans 4 · drift 75m".to_string()];
    insta::assert_snapshot!(
        "diagnostics",
        emit::render_diagnostics(&diag, &tree, &cfg).join("\n")
    );
}

#[test]
fn the_impossible_banner_names_the_shortfall() {
    let cfg = config();
    let tree = tree(&cfg);
    let mut day = DayPlan::empty(emit_fixture::date(), (at(7, 0), at(16, 0)), 6);
    day.diagnostics.impossible = vec![(
        Id::new("d1"),
        180,
        chrono::NaiveDate::from_ymd_opt(2026, 9, 11).expect("date"),
    )];
    // Without the `Prio` numbers only the shortfall can be stated.
    assert_eq!(
        emit::render_banners(&day, &tree, &cfg),
        vec!["d1: short by 3b at Fri".to_string()]
    );
    // With them, §7.3's own wording.
    let (id, mut p) = prio("d1", 0, PrioClass::Impossible);
    p.need_min = 480;
    p.avail_min = 300;
    p.shortfall_min = 180;
    day.priorities = vec![(id, p)];
    assert_eq!(
        emit::render_banners(&day, &tree, &cfg),
        vec!["d1: needs 8b, 5b available by Fri".to_string()]
    );
    // A deadline further out reads as a date, not a weekday.
    day.diagnostics.impossible[0].2 = chrono::NaiveDate::from_ymd_opt(2026, 11, 20).expect("date");
    assert_eq!(
        emit::render_banners(&day, &tree, &cfg),
        vec!["d1: needs 8b, 5b available by 2026-11-20".to_string()]
    );
}

#[test]
fn the_legend_counts_minutes_at_each_ci() {
    let cfg = config();
    let tree = tree(&cfg);
    let day = plan();
    let mix = emit::legend(&day, &tree, &cfg);
    // t1 67m + t2 58m at ci5, t3 120m at ci4, t4 60m + t5 60m at ci3,
    // a3 20m at ci1.
    assert_eq!(mix.minutes_at_ci, [0, 20, 0, 120, 120, 125]);
    assert_eq!(mix.total_min, 385);
    // §11 is a share *of the budget*: 6 blocks × 60m = 360m, of which 245m are
    // at ci ≥ 4. (Regression: this divided by the 385 planned minutes, giving
    // 64% where the spec's definition gives 68%.)
    assert_eq!(mix.budget_min, 360);
    assert!((mix.share_ci4_plus - 245.0 / 360.0).abs() < 1e-12);
    assert_eq!(mix.underused_count, 1);
    assert_eq!(mix.optional_min, 60, "Severance S3E4, one hour");
    assert_eq!(
        mix.line(),
        "ci5 125m · ci4 120m · ci3 120m · ci1 20m · ci≥4 68% · ↓1 · ○ 60m"
    );

    // A day that fills its budget with ci-5 work reads 100%, and one that
    // overruns it reads above 100% — that is what "share of budget" means.
    let mut full = DayPlan::empty(emit_fixture::date(), (at(7, 0), at(13, 0)), 6);
    full.segments = plan()
        .segments
        .iter()
        .filter(|s| matches!(s.kind, SegKind::Block))
        .cloned()
        .collect();
    full.budget_blocks = 4;
    let mix = emit::legend(&full, &tree, &cfg);
    assert_eq!(mix.budget_min, 240);
    assert!((mix.share_ci4_plus - 245.0 / 240.0).abs() < 1e-12);

    // An empty day has no share at all (no division by zero).
    let empty = DayPlan::empty(emit_fixture::date(), (at(7, 0), at(16, 0)), 6);
    let mix = emit::legend(&empty, &tree, &cfg);
    assert_eq!(mix.total_min, 0);
    assert_eq!(mix.share_ci4_plus, 0.0);
    assert_eq!(mix.line(), "ci≥4 0% · ↓0");

    // With no budget at all the plan's own block minutes stand in.
    let mut budgetless = plan();
    budgetless.budget_blocks = 0;
    let mix = emit::legend(&budgetless, &tree, &cfg);
    assert_eq!(mix.budget_min, 0);
    assert!((mix.share_ci4_plus - 245.0 / 385.0).abs() < 1e-12);
}

#[test]
fn a_malformed_palette_entry_is_reportable() {
    // Regression: `EmitError` was unreachable — `palette_rgb` swallowed every
    // parse failure into mid-grey, so a `#ff00` typo in `config.toml` was
    // indistinguishable from a legitimately grey palette entry.
    let cfg = config();
    assert_eq!(
        emit::palette_colours(&cfg).expect("the §16 palette parses").len(),
        cfg.tui.palette.len()
    );
    assert_eq!(emit::parse_hex_colour("#3cb44b"), Ok((0x3c, 0xb4, 0x4b)));
    assert_eq!(emit::parse_hex_colour("3cb44b"), Ok((0x3c, 0xb4, 0x4b)));

    let mut bad = config();
    bad.tui.palette = vec!["#3cb44b".to_string(), "#ff00".to_string()];
    assert_eq!(
        emit::palette_colours(&bad),
        Err(emit::EmitError::BadColour("#ff00".to_string()))
    );
    assert_eq!(
        emit::parse_hex_colour("oops"),
        Err(emit::EmitError::BadColour("oops".to_string()))
    );
    assert_eq!(
        emit::parse_hex_colour("#gggggg"),
        Err(emit::EmitError::BadColour("#gggggg".to_string()))
    );
    // Rendering still never fails: the bad entry falls back to mid-grey.
    assert_eq!(emit::palette_rgb(&bad, 1), (0x88, 0x88, 0x88));
    assert_eq!(emit::palette_rgb(&bad, 0), (0x3c, 0xb4, 0x4b));
}

/// **The owner's D144 (README gap 5750, parity P141): a running break past its planned end stays
/// current.** The kernel draws it as an OPEN Break row up to `now` exactly, so its half-open span
/// no longer contains `now`; `now_window` keeps it current — ahead of a row that starts at `now` —
/// and the line under it reads the break (`emit::OnBreak`): `elapsed`, `left` and `(overrun 45m)`.
/// Both directions: a Break row that is not open (a break that ended at `now`) is not current, and
/// inside its planned minutes the line reads `left` with no overrun.
#[test]
fn a_running_break_past_its_planned_end_stays_current() {
    use lime_core::dayplan::{SegFlags, Segment};
    let mut day = plan();
    let now = at(11, 15);
    let open = SegFlags { open: true, ..SegFlags::default() };
    day.segments = vec![
        Segment { start: at(10, 10), end: now, kind: SegKind::Break, energy: None, item: None, instance: None, flags: open },
        Segment {
            start: now,
            end: at(11, 45),
            kind: SegKind::Routine,
            energy: None,
            item: Some(Id::new("laundry")),
            instance: None,
            flags: SegFlags::default(),
        },
    ];
    let (current, next) = emit::now_window(&day, now);
    assert_eq!(current, Some(0), "the open break is current");
    assert_eq!(next, vec![1], "the routine at `now` is next");
    let b = emit::OnBreak::new(at(10, 10), 20, &day.segments, now);
    assert_eq!(b.drawn_from, at(10, 10), "drawn from its start");
    assert_eq!(
        emit::now_annotation(&day.segments[0], now, None, Some(&b)),
        "  10:10–11:15 · elapsed 1h5m · left 0m (overrun 45m)\n"
    );
    assert_eq!(b.overrun_min(now), 45);
    assert_eq!(b.elapsed_min(now), 65);
    // A Break row that is NOT open ended at `now`: the routine is current.
    day.segments[0].flags.open = false;
    assert_eq!(emit::now_window(&day, now).0, Some(1), "a closed break that ended at `now` is not current");
    // Inside its planned minutes: no overrun, `left` the break's.
    day.segments[0].end = at(10, 30);
    assert_eq!(
        emit::now_annotation(&day.segments[0], at(10, 20), None, Some(&b)),
        "  10:10–10:30 · elapsed 10m · left 10m\n"
    );
}
