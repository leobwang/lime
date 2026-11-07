//! `lime init [dir] [--example] [--force]` (lime-spec-v1.md §13, §14, §17 M9).
//!
//! # API overview
//!
//! Wiring only: this file resolves the target directory and the flags, calls
//! [`crate::init::write`] — which owns every byte of the generated tree (the
//! §16 config, §14's `CLAUDE.md`, skills and hooks, and §2's starting files,
//! all embedded from `lime/templates/`) — and reports the result as [`InitOut`]
//! (`--json`) or two lines of prose ending in the one-line
//! `git config core.hooksPath …` instruction (§1.3: `lime init` never rewrites
//! the user's git config).

use std::path::PathBuf;

use serde::Serialize;

use crate::init;

use super::ctx::Globals;
use super::out::{emit, CliError};

/// `lime init --json`.
#[derive(Debug, Serialize)]
pub struct InitOut {
    /// The directory created.
    pub dir: String,
    /// Files written.
    pub created: Vec<String>,
    /// Files that were already there and were left byte for byte as they
    /// were. Empty on a fresh tree; under `--force` it holds the files whose
    /// content is the user's — §2's items, `config.toml`, and a `.gitignore`
    /// that already carries the lime block — because `--force` refreshes the
    /// generated integration (`CLAUDE.md`, the skills, the hooks) without
    /// touching the database.
    pub skipped: Vec<String>,
    /// Under `--force`: the old command's generated hook, removed (D160). Absent when there was none.
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub removed: Vec<String>,
    /// Under `--force`: the old command's hook, left because it is not the script the old `init`
    /// wrote (D160). Absent when there was none.
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub left_edited: Vec<String>,
    /// How to enable the git pre-commit hook (§1.3).
    pub hook_hint: String,
}

/// Map an [`init::InitError`] onto the CLI's errors (§13: exit 1).
fn cli_error(e: init::InitError) -> CliError {
    match e {
        init::InitError::NotEmpty { .. } => CliError::Msg(e.to_string()),
        init::InitError::Io { path, source } => CliError::io(path, source),
    }
}

/// `lime init [dir] [--example] [--force]`.
pub fn run(g: &Globals, args: &super::InitArgs) -> Result<i32, CliError> {
    let root: PathBuf = args
        .dir
        .clone()
        .or_else(|| g.dir.clone())
        .unwrap_or_else(|| PathBuf::from("plan"));

    // §17.2: the day is `now` in the tree's own timezone (§16 `tz`), which is
    // what every other verb plans in — not the machine's offset, which would
    // give the fresh tree a `week/` file for a different day than `lime plan`.
    let now = g
        .now
        .unwrap_or_else(|| chrono::Local::now().fixed_offset());
    let today = init::today(&root, now);
    let opts = init::Options {
        example: args.example,
        force: args.force,
        ..init::Options::new(today)
    };
    let written = init::write(&root, &opts).map_err(cli_error)?;

    let out = InitOut {
        dir: root.display().to_string(),
        created: written.created,
        skipped: written.unchanged,
        removed: written.old_hook_removed,
        left_edited: written.old_hook_left,
        hook_hint: init::hook_hint(&root),
    };
    let example = args.example;
    emit(
        g.json,
        || {
            let mut s = format!("created {} file(s) in {}", out.created.len(), out.dir);
            if example {
                s.push_str("\nthe example tree is §4.3's, dated 2026-09-07 (week 2026-W37)");
            }
            if !out.skipped.is_empty() {
                s.push_str(&format!(
                    "\nleft alone, already there ({}): {}",
                    out.skipped.len(),
                    out.skipped.join(", ")
                ));
            }
            for path in &out.removed {
                s.push_str(&format!("\nremoved {path}: the old command's generated hook; {} replaces it", init::HOOK_SCRIPT_PATH));
            }
            for path in &out.left_edited {
                s.push_str(&format!(
                    "\nleft {path}: it is not the script the old command's init wrote, so it may be yours, and nothing runs it now; delete it when you are done with it"
                ));
            }
            s.push_str(&format!(
                "\nenable the pre-commit hook with:\n  {}",
                out.hook_hint
            ));
            s
        },
        &out,
    )?;
    Ok(0)
}
