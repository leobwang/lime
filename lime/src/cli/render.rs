//! A [`DayPlan`] as the CLI writes it (lime-spec-v1.md §4.3, §12.1).
//!
//! # API overview
//!
//! * [`timeline`] — the body of the `<!-- tm:plan … -->` section of the day
//!   file: §4.3's `HH:MM  ci  pN  mark  title  @parent  est  (actual)  note`
//!   grid, with the `───  window ends HH:MM` divider.
//! * [`svg`] — `day/<date>.svg`: §12.1's day bar, 24 h from wake to wake,
//!   with the ghost row beneath.
//! * [`rows`] — the same rows as data, which `lime plan --json` emits. (`lime now`
//!   selects from `emit::plan_rows` directly; this sentence said it "reuses"
//!   [`rows`] and it never did — `lime now` had its own renderer until W-23.)
//! The `SegKind` word the JSON and `.tm/last_plan.json` use is
//! [`lime_core::dayplan::kind_label`] — through [`lime_core::emit::row_kind`] in the
//! JSON, which calls a replayed pause `pause` (D68). This module declared a second, byte-for-byte
//! identical kind_name until W-23 (AGENTS §5.3). A deleted name loses its
//! backticks, here as in the README (gap 1313).
//!
//! §1.2 puts the renderer itself in `lime-core/src/emit.rs`, and that is where
//! it is: everything here delegates, so `lime plan`, `lime tui` and the M4
//! snapshots print one text for one [`DayPlan`].

use chrono::DateTime;
use chrono_tz::Tz;
use serde::Serialize;
use lime_core::config::Config;
use lime_core::emit;
use lime_core::model::Id;
use lime_core::dayplan::DayPlan;
use lime_core::tree::Tree;

/// Pixels of `day/<date>.svg` (§12.1's bar is a wide, short strip; the ghost
/// row is drawn inside this height).
const SVG_WIDTH: u32 = 960;
/// Height in pixels.
const SVG_HEIGHT: u32 = 64;
/// Cells the day bar is cut into for the file. One cell is 15 minutes over
/// the 24 h span, which is finer than any segment boundary the planner emits.
const SVG_COLS: usize = 96;

/// One rendered row of the timeline.
#[derive(Clone, Debug, Serialize)]
pub struct Row {
    /// `HH:MM` — the row's time cell, the kernel's (D112).
    pub time: String,
    /// Predicted slot energy, when the segment has one.
    pub energy: Option<u8>,
    /// The §4.3 mark (`✓`, `▶`, `⚠`), or empty — the row's mark cell, the
    /// kernel's (D112), trimmed.
    pub mark: String,
    /// The whole §4.3 row, exactly as the day file has it.
    pub text: String,
    /// The item, when the segment has one.
    pub item: Option<Id>,
    /// The segment kind, lowercased — [`emit::row_kind`]'s word, which is
    /// `pause` for a replayed pause (D68, P59) and `kind_label`'s otherwise.
    pub kind: String,
}

/// The rows of a plan, in start order — one per segment, each carrying the
/// §4.3 row `emit` writes into the day file.
///
/// **Zipped by position** (README gap **1197**): `emit::plan_rows` answers one
/// row per segment in the same order, and `rows[i].text` is `segments[i]`'s row
/// because it is taken at `i` — not because it was looked up by anything the row
/// says. Two items with one title give byte-identical rows, so a by-value
/// lookup here would have more than one witness. This used to call
/// emit::render_segment_row(seg, …), which rebuilt the priority map once per
/// row and was the by-value form; `plan_rows` replaced it and it is gone.
///
/// **`time` and `mark` are the row's own cells** (the owner's **D112**, W-47):
/// the kernel's, the cells `text` is padded from, read at the same position.
/// They were the segment's start through `fmt_clock` and the Rust mark_of
/// until the Rust builder was deleted — the same bytes, from a second reader.
pub fn rows(plan: &DayPlan) -> Vec<Row> {
    plan.segments
        .iter()
        .zip(&plan.cells)
        .zip(emit::plan_rows(plan, &emit::Layout::default()))
        .map(|((seg, cells), text)| Row {
            time: cells.time.clone(),
            energy: seg.energy,
            mark: cells.mark.trim().to_string(),
            text,
            item: seg.item.clone(),
            kind: emit::row_kind(seg).to_string(),
        })
        .collect()
}

/// **The `window ends` divider, as `lime plan --json` carries it** (README gap 1301, W-48
/// track R): the day section's one line that is no segment's. Until W-48 `--json` had no
/// counterpart, so a consumer could rebuild every line of the section but this one.
#[derive(Clone, Debug, Serialize)]
pub struct DividerOut {
    /// The position among `segments` it stands before — their number when it comes last.
    pub before: usize,
    /// `HH:MM` — the instant the budget runs out or the window ends, the kernel's.
    pub time: String,
    /// The whole line, exactly as the day file has it.
    pub text: String,
}

/// The divider of a plan, from the day section's own lines ([`emit::day_lines`]): its
/// position, its time cell and its text, so `lime plan --json` and the day file print one line.
pub fn divider(plan: &DayPlan) -> Option<DividerOut> {
    let (before, cells) = plan.divider.as_ref()?;
    let text = emit::day_lines(plan, &emit::Layout::default()).into_iter().find(|l| l.segment.is_none())?.text;
    Some(DividerOut { before: *before, time: cells.time.clone(), text })
}

/// The body of the day file's `tm:plan` section (§4.3) — the timeline, and
/// only the timeline. §8.2 step 8's diagnostics and §11's warnings go to
/// `lime plan`'s own output ([`diagnostics`]), not into the file.
pub fn timeline(plan: &DayPlan, now: DateTime<Tz>) -> String {
    emit::render_plan_section(plan, now).1
}

/// §8.2 step 8's diagnostics and §11's warnings — the "plan honesty {h} —
/// planned above a realistic budget" line among them — as `lime plan` prints
/// them under the timeline.
pub fn diagnostics(plan: &DayPlan, tree: &Tree, cfg: &Config) -> Vec<String> {
    emit::render_diagnostics(&plan.diagnostics, tree, cfg)
}

/// `day/<date>.svg`: §12.1's day bar — 24 h from wake to wake, the log left
/// of the cursor and the plan right of it, the ghost row beneath.
pub fn svg(
    plan: &DayPlan,
    ghost: Option<&DayPlan>,
    tree: &Tree,
    cfg: &Config,
    wake: DateTime<Tz>,
    now: DateTime<Tz>,
) -> String {
    let bar = emit::daybar_cells(plan, ghost, tree, cfg, SVG_COLS, wake, now);
    emit::render_svg(&bar, plan, cfg, SVG_WIDTH, SVG_HEIGHT)
}
