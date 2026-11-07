//! What `lime init` generates: the plan skeleton of lime-spec-v1.md §2 and the
//! Claude Code integration of §14.
//!
//! # API overview
//!
//! The content lives in `lime/templates/` and is embedded with `include_str!`,
//! so the binary carries the whole skeleton and `lime init` needs no data files:
//!
//! * [`CLAUDE_MD`] — §14's rules for Claude Code, verbatim (6 lines).
//! * [`SKILLS`] — one `(name, SKILL.md)` pair per row of §14's skill table:
//!   `plan-week`, `plan-month`, `triage`, `capture`, `replan`, `review-day`,
//!   `review-week`, `explain`. Each has YAML front matter (`name`,
//!   `description` = when to use it) and the `lime … --json` commands it runs.
//! * [`SETTINGS_JSON`] — `.claude/settings.json`: the §14 `PostToolUse` hook
//!   on `Edit|MultiEdit|Write`, plus a `deny` rule for `.tm/**` (§14: Claude
//!   never touches the runtime state). A hook matcher matches tool *names*,
//!   not paths, so the "under `plan/`" half of §14 lives in the command:
//! * [`HOOK_SCRIPT`] — `.claude/hooks/lime-check.sh`, what that hook runs. It
//!   checks the payload's `file_path` against this plan tree (an edit
//!   anywhere else is a no-op) and re-emits `lime check`'s diagnostics on
//!   *stderr* before exiting 2, because that is the only stream Claude Code
//!   feeds back to the model on a blocking hook.
//! * [`PRE_COMMIT`] — `.githooks/pre-commit`, the same check as a git hook
//!   (§1.3). `lime init` never rewrites the user's git config; it prints
//!   [`hook_hint`] instead.
//! * [`GITIGNORE`] — the `.tm/state.json` line and the CLI's other caches.
//!
//! Three entry points:
//!
//! * [`files`]`(&`[`Options`]`)` — the whole tree as [`InitFile`] values
//!   (relative path, text, [`Mode`]), pure and testable; [`DIRS`] lists the
//!   directories that carry no file of their own (`calendar/`, `.tm/`).
//! * [`write`]`(root, &`[`Options`]`)` — creates them, returning [`Written`]
//!   (what was created, what was left alone). It refuses a non-empty
//!   directory unless [`Options::force`]; even then it only ever *adds* to
//!   the user's own files: every §2 content file and `config.toml` is
//!   [`Mode::Preserve`] (kept exactly as it is when it already exists) and
//!   `.gitignore` is [`Mode::Merge`] (the lime block appended when missing).
//!   `--force` rewrites the generated integration — `CLAUDE.md`, the skills,
//!   the settings and the two hooks — which is what makes it an upgrade path
//!   rather than a way to lose a week of items.
//! * [`today`]`(root, now)` — the date the fresh `month/` and `week/` files
//!   are for: `now` resolved in the timezone the tree's config declares (§16
//!   `tz`), which is the timezone every other verb resolves `--now` in.
//!
//! [`Options::example`] swaps the guidance files for §4.3's populated tree
//! (the `plan-basic` fixture, byte for byte), so a new user can run `lime plan`
//! immediately. Either way the result passes `lime check` (§17 M9).

use std::fs;
use std::io;
use std::path::Path;

use chrono::{DateTime, FixedOffset, NaiveDate};
use thiserror::Error;
use lime_core::config::Config;
use lime_core::model::{Horizon, IsoWeek, YearMonth};
use lime_core::store;

/// §14's `plan/CLAUDE.md`, verbatim.
pub const CLAUDE_MD: &str = include_str!("../../templates/CLAUDE.md");

/// `.claude/settings.json`: the §14 `PostToolUse` hook running [`HOOK_SCRIPT`].
pub const SETTINGS_JSON: &str = include_str!("../../templates/settings.json");

/// `.claude/hooks/lime-check.sh`: what the `PostToolUse` hook runs — `lime check`
/// for edits inside this plan tree, with the diagnostics on stderr (§14).
pub const HOOK_SCRIPT: &str = include_str!("../../templates/hooks/lime-check.sh");

/// Where [`HOOK_SCRIPT`] lives, relative to the plan root.
pub const HOOK_SCRIPT_PATH: &str = ".claude/hooks/lime-check.sh";

/// `.githooks/pre-commit`: `lime check` before every commit (§1.3).
pub const PRE_COMMIT: &str = include_str!("../../templates/pre-commit");

/// The `.gitignore` block for the runtime state (§10.2).
pub const GITIGNORE: &str = include_str!("../../templates/gitignore");

/// The path whose presence means the [`GITIGNORE`] block is already there.
const GITIGNORE_MARKER: &str = ".tm/state.json";

/// §14's skills, as `(name, SKILL.md text)`, in table order.
pub const SKILLS: &[(&str, &str)] = &[
    (
        "plan-week",
        include_str!("../../templates/skills/plan-week.md"),
    ),
    (
        "plan-month",
        include_str!("../../templates/skills/plan-month.md"),
    ),
    ("triage", include_str!("../../templates/skills/triage.md")),
    ("capture", include_str!("../../templates/skills/capture.md")),
    ("replan", include_str!("../../templates/skills/replan.md")),
    (
        "review-day",
        include_str!("../../templates/skills/review-day.md"),
    ),
    (
        "review-week",
        include_str!("../../templates/skills/review-week.md"),
    ),
    ("explain", include_str!("../../templates/skills/explain.md")),
];

/// The guidance an empty tree carries: `(relative path, text)`.
const STARTER: &[(&str, &str)] = &[
    ("inbox.md", include_str!("../../templates/starter/inbox.md")),
    (
        "backlog.md",
        include_str!("../../templates/starter/backlog.md"),
    ),
    (
        "routines.md",
        include_str!("../../templates/starter/routines.md"),
    ),
    (
        "optional.md",
        include_str!("../../templates/starter/optional.md"),
    ),
];

/// The body of a fresh `month/<YYYY-MM>.md`, after its front matter.
const MONTH_BODY: &str = include_str!("../../templates/starter/month-body.md");

/// The body of a fresh `week/<YYYY-Www>.md`, after its front matter.
const WEEK_BODY: &str = include_str!("../../templates/starter/week-body.md");

/// `--example`: §4.3's tree, `(relative path, text)`. The dates are the
/// spec's (Monday 2026-09-07, week 2026-W37), so the example reads exactly
/// like §4.3 and like the `plan-basic` fixture.
const EXAMPLE: &[(&str, &str)] = &[
    ("inbox.md", include_str!("../../templates/example/inbox.md")),
    (
        "backlog.md",
        include_str!("../../templates/example/backlog.md"),
    ),
    (
        "routines.md",
        include_str!("../../templates/example/routines.md"),
    ),
    (
        "optional.md",
        include_str!("../../templates/example/optional.md"),
    ),
    (
        "month/2026-09.md",
        include_str!("../../templates/example/month.md"),
    ),
    (
        "week/2026-W37.md",
        include_str!("../../templates/example/week.md"),
    ),
    (
        "calendar/2026-W37.md",
        include_str!("../../templates/example/calendar.md"),
    ),
    (
        "day/2026-09-07.md",
        include_str!("../../templates/example/day.md"),
    ),
];

/// Directories §2 wants that no generated file creates on its own.
pub const DIRS: &[&str] = &["calendar", ".tm"];

/// Where the git hook lives, relative to the plan root (§1.3).
pub const HOOKS_DIR: &str = ".githooks";

/// What `lime init` should generate.
#[derive(Debug, Clone)]
pub struct Options {
    /// Today, for `month/<YYYY-MM>.md` and `week/<YYYY-Www>.md` (injected,
    /// never read from a clock in here).
    pub today: NaiveDate,
    /// Write §4.3's populated tree instead of the guidance files.
    pub example: bool,
    /// Overwrite an existing tree (without it, a non-empty directory is
    /// [`InitError::NotEmpty`]).
    pub force: bool,
}

impl Options {
    /// The default options for `today`: guidance files, no overwriting.
    pub fn new(today: NaiveDate) -> Options {
        Options {
            today,
            example: false,
            force: false,
        }
    }
}

/// How one generated file is written.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Mode {
    /// lime owns the file: written as generated (existing content is replaced
    /// only under `--force`, which is the only way to reach an existing tree).
    Managed,
    /// [`Mode::Managed`], plus the executable bit on unix (the two hooks).
    Executable,
    /// The user owns the file's *content*: created when absent, and left
    /// exactly as it is when it already exists — §2's "horizon is the file"
    /// files are the database, and `config.toml` is the user's settings, so
    /// not even `--force` overwrites one.
    Preserve,
    /// The user owns the file and lime owns one block of it: created when
    /// absent, otherwise extended with the missing block, never rewritten —
    /// `.gitignore` may hold their own entries.
    Merge,
}

/// One file `lime init` generates.
#[derive(Debug, Clone)]
pub struct InitFile {
    /// Path relative to the plan root, `/`-separated.
    pub path: String,
    /// The whole file.
    pub text: String,
    /// How to write it.
    pub mode: Mode,
}

impl InitFile {
    /// A file lime owns.
    fn managed(path: impl Into<String>, text: impl Into<String>) -> InitFile {
        InitFile {
            path: path.into(),
            text: text.into(),
            mode: Mode::Managed,
        }
    }

    /// A file whose content is the user's: written once, never overwritten.
    fn preserve(path: impl Into<String>, text: impl Into<String>) -> InitFile {
        InitFile {
            path: path.into(),
            text: text.into(),
            mode: Mode::Preserve,
        }
    }
}

/// Where `init` wrote its Claude Code hook while the command was called `tm` (D160).
pub const OLD_HOOK_SCRIPT_PATH: &str = ".claude/hooks/tm-check.sh";

/// That hook's bytes as the old `init` wrote them: blob `c13343c`, the one version the file ever
/// had in this repository's history. `lime/tests/cli_old_hooks.rs` holds this copy to that blob.
const OLD_HOOK_SCRIPT: &[u8] = include_bytes!("old-tm-check.sh");

/// **The script the old `init` wrote, or that script with nothing a user wrote in it.** Byte for
/// byte, but for line endings, which a checkout can turn to CRLF on its own. The name alone is not
/// enough: a user's edit to the file is theirs.
pub fn is_old_generated_hook(bytes: &[u8]) -> bool {
    let lf: Vec<u8> = bytes.iter().enumerate().filter(|&(i, b)| !(*b == b'\r' && bytes.get(i + 1) == Some(&b'\n'))).map(|(_, b)| *b).collect();
    lf == OLD_HOOK_SCRIPT
}

/// **Does this line of a shell script run `tm check`?** The old command, as a command: the word
/// `tm` then the word `check`, where the shell would start a command — the line's start, after
/// `exec`, `if`, `then`, `do`, `else`, `!`, or a `;`, `|`, `&` or `(` outside quotes, or just inside a
/// `"$(`. A comment, a word in an `echo`, `lime check`, `tm-check` and `tm checkout` are not
/// matches: a user's hook that merely mentions the letters is left alone.
pub fn calls_old_command(line: &str) -> bool {
    let line = line.trim_start();
    if line.starts_with('#') {
        return false;
    }
    let (mut single, mut double) = (false, false);
    let mut chars = line.char_indices();
    while let Some((i, c)) = chars.next() {
        match c {
            '\\' if !single => {
                chars.next();
                continue;
            }
            '\'' if !double => single = !single,
            '"' if !single => double = !double,
            '#' if !single && !double && line[..i].ends_with(char::is_whitespace) => return false,
            _ => {}
        }
        if !single && line[i..].starts_with("tm") && runs_check(&line[i + 2..]) && command_position(&line[..i], double) {
            return true;
        }
    }
    false
}

/// `check` as the next word.
fn runs_check(rest: &str) -> bool {
    let word = rest.trim_start();
    word.len() < rest.len()
        && word.strip_prefix("check").is_some_and(|after| !after.starts_with(|c: char| c.is_ascii_alphanumeric() || "_-.".contains(c)))
}

/// Whether what stands before a word leaves it where the shell starts a command.
fn command_position(before: &str, in_double_quotes: bool) -> bool {
    if in_double_quotes {
        return before.ends_with("$(");
    }
    let before = before.trim_end();
    if before.is_empty() || before.ends_with(['(', ';', '|', '&', '!', '{']) {
        return true;
    }
    matches!(before.rsplit(|c: char| c.is_whitespace()).next(), Some("exec" | "then" | "do" | "else" | "if" | "while" | "until"))
}

/// **The command that brings the tree at `root` up to date, with the tree named** (D160). `init` does
/// not look for the plan as every other verb does (`--dir`, else `./plan`), so a bare `lime init --force`
/// typed inside a tree makes a second tree at `./plan` and leaves this one as it was. The path is
/// absolute, so the command works pasted anywhere, and so is the path in the `git config` line the
/// reply prints ([`hook_hint`]), which git reads from the repository's top and not from where it was typed.
pub fn force_command(root: &Path) -> String {
    let root = fs::canonicalize(root).unwrap_or_else(|_| root.to_path_buf());
    format!("lime init {} --force", shell_word(&root.display().to_string()))
}

/// `word` as one word of a POSIX shell: as it stands if nothing in it is special, else single-quoted.
fn shell_word(word: &str) -> String {
    if !word.is_empty() && word.chars().all(|c| c.is_ascii_alphanumeric() || "/._-+=:@%,".contains(c)) {
        return word.to_string();
    }
    format!("'{}'", word.replace('\'', "'\\''"))
}

/// One hook of a tree that still runs the old command.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct OldHook {
    /// Its path under the plan root.
    pub path: String,
    /// The 1-based line that runs it.
    pub line: usize,
    /// True when [`force_command`] can bring it up to date: the pre-commit, which it rewrites, or
    /// the old script as generated, which it removes. False for the old script with a user's edit.
    pub force_clears: bool,
}

/// **The hooks under `root` that still call the old command** (D160): the two paths the old `init`
/// wrote, [`OLD_HOOK_SCRIPT_PATH`] and `.githooks/pre-commit`, each only when a line of it runs the old
/// command ([`calls_old_command`]). A file absent, or not text, is no match.
pub fn old_hooks(root: &Path) -> Vec<OldHook> {
    let pre_commit = format!("{HOOKS_DIR}/pre-commit");
    let mut out = Vec::new();
    for rel in [OLD_HOOK_SCRIPT_PATH, pre_commit.as_str()] {
        let Ok(bytes) = fs::read(root.join(rel)) else { continue };
        let Ok(text) = std::str::from_utf8(&bytes) else { continue };
        if let Some(at) = text.lines().position(calls_old_command) {
            out.push(OldHook {
                path: rel.to_string(),
                line: at + 1,
                force_clears: rel != OLD_HOOK_SCRIPT_PATH || is_old_generated_hook(&bytes),
            });
        }
    }
    out
}

/// `--force`'s one removal (D160): [`OLD_HOOK_SCRIPT_PATH`], only a regular file, and only as generated.
fn remove_old_hook(root: &Path, written: &mut Written) -> Result<(), InitError> {
    let path = root.join(OLD_HOOK_SCRIPT_PATH);
    let is_file = fs::symlink_metadata(&path).is_ok_and(|m| m.file_type().is_file());
    if !is_file {
        if path.symlink_metadata().is_ok() {
            written.old_hook_left.push(OLD_HOOK_SCRIPT_PATH.to_string());
        }
        return Ok(());
    }
    let bytes = fs::read(&path).map_err(|e| InitError::io(path.display().to_string(), e))?;
    if is_old_generated_hook(&bytes) {
        fs::remove_file(&path).map_err(|e| InitError::io(path.display().to_string(), e))?;
        written.old_hook_removed.push(OLD_HOOK_SCRIPT_PATH.to_string());
    } else {
        written.old_hook_left.push(OLD_HOOK_SCRIPT_PATH.to_string());
    }
    Ok(())
}

/// What [`write`] did.
#[derive(Debug, Clone, Default)]
pub struct Written {
    /// Files created (or, for `.gitignore`, extended), in generation order.
    pub created: Vec<String>,
    /// Under `--force`: the old command's generated hook, removed (D160).
    pub old_hook_removed: Vec<String>,
    /// Under `--force`: the old command's hook, left because it is not as generated (D160).
    pub old_hook_left: Vec<String>,
    /// Files that were already there and were left byte for byte as they
    /// were: every [`Mode::Preserve`] file that exists (the §2 content files
    /// and `config.toml` under `--force`) and a [`Mode::Merge`] file that
    /// already carries lime's block.
    pub unchanged: Vec<String>,
}

/// Everything `lime init` can fail with.
#[derive(Debug, Error)]
pub enum InitError {
    /// The target directory already holds something and `--force` was not
    /// given.
    #[error("{dir} is not empty — refusing to overwrite it (use --force)")]
    NotEmpty {
        /// The directory.
        dir: String,
    },
    /// Creating a directory or writing a file failed.
    #[error("{path}: {source}")]
    Io {
        /// The path being written.
        path: String,
        /// The underlying error.
        source: io::Error,
    },
}

impl InitError {
    /// An [`InitError::Io`] for `path`.
    fn io(path: impl Into<String>, source: io::Error) -> InitError {
        InitError::Io {
            path: path.into(),
            source,
        }
    }
}

/// The one-line instruction `lime init` prints instead of rewriting the user's
/// git config (§1.3, §14).
pub fn hook_hint(root: &Path) -> String {
    format!(
        "git config core.hooksPath {}",
        root.join(HOOKS_DIR).display()
    )
}

/// One `SKILL.md`'s path and text.
fn skill_file(name: &str, text: &str) -> InitFile {
    InitFile::managed(format!(".claude/skills/{name}/SKILL.md"), text)
}

/// Every file `lime init` writes, in the order it writes them.
///
/// Pure: the only inputs are [`Options::today`] and the two flags, so the
/// whole tree can be snapshotted without touching the filesystem.
pub fn files(opts: &Options) -> Vec<InitFile> {
    let mut out = Vec::new();

    // §16: the complete config, with `ics_urls = []` and the example URL as a
    // comment (§15). It parses to `Config::default()`. The user edits it, so
    // `--force` leaves an existing one alone.
    out.push(InitFile::preserve(
        store::CONFIG_PATH,
        Config::default_toml(),
    ));

    // §14: the rules, the skills and the two hooks — lime's own, rewritten by
    // `--force` so an old tree can be brought up to date.
    out.push(InitFile::managed("CLAUDE.md", CLAUDE_MD));
    out.push(InitFile::managed(".claude/settings.json", SETTINGS_JSON));
    out.push(InitFile {
        path: HOOK_SCRIPT_PATH.to_string(),
        text: HOOK_SCRIPT.to_string(),
        mode: Mode::Executable,
    });
    for (name, text) in SKILLS {
        out.push(skill_file(name, text));
    }
    out.push(InitFile {
        path: format!("{HOOKS_DIR}/pre-commit"),
        text: PRE_COMMIT.to_string(),
        mode: Mode::Executable,
    });
    out.push(InitFile {
        path: ".gitignore".to_string(),
        text: GITIGNORE.to_string(),
        mode: Mode::Merge,
    });

    // §2: the files themselves — the database. Written once; never rewritten,
    // with or without `--force`.
    if opts.example {
        for (path, text) in EXAMPLE {
            out.push(InitFile::preserve(*path, *text));
        }
    } else {
        for (path, text) in STARTER {
            out.push(InitFile::preserve(*path, *text));
        }
        let month = Horizon::Month(YearMonth::from_date(opts.today));
        let week = Horizon::Week(IsoWeek::from_date(opts.today));
        out.push(InitFile::preserve(
            month.path(),
            format!("{}{MONTH_BODY}", store::initial_text(&month)),
        ));
        out.push(InitFile::preserve(
            week.path(),
            format!("{}{WEEK_BODY}", store::initial_text(&week)),
        ));
    }
    out
}

/// The date `lime init` builds the fresh `month/` and `week/` files for: `now`
/// resolved in the timezone the tree's config declares (§16 `tz`, default
/// `America/Chicago`).
///
/// Every other verb resolves `--now` in `cfg.tz` (§17.2), so reading the
/// machine's own offset here would give a new tree a `week/` file for a
/// different day than `lime plan` looks for. An existing `config.toml` — the
/// `--force` case — wins over the default; an unreadable or unparsable one
/// falls back to it.
pub fn today(root: &Path, now: DateTime<FixedOffset>) -> NaiveDate {
    let cfg = fs::read_to_string(root.join(store::CONFIG_PATH))
        .ok()
        .and_then(|text| Config::parse(&text).ok())
        .unwrap_or_default();
    now.with_timezone(&cfg.tz).date_naive()
}

/// True when `dir` exists and holds at least one entry.
fn is_non_empty(dir: &Path) -> bool {
    fs::read_dir(dir)
        .map(|mut entries| entries.next().is_some())
        .unwrap_or(false)
}

/// Give the file the executable bit (unix only; a no-op elsewhere).
#[cfg(unix)]
fn make_executable(path: &Path) -> Result<(), InitError> {
    use std::os::unix::fs::PermissionsExt;
    let mut perms = fs::metadata(path)
        .map_err(|e| InitError::io(path.display().to_string(), e))?
        .permissions();
    perms.set_mode(0o755);
    fs::set_permissions(path, perms).map_err(|e| InitError::io(path.display().to_string(), e))
}

/// Give the file the executable bit (unix only; a no-op elsewhere).
#[cfg(not(unix))]
fn make_executable(_path: &Path) -> Result<(), InitError> {
    Ok(())
}

/// The text a `.gitignore` should end up with: the existing one plus the lime
/// block, or `None` when it already has it. A `.gitignore` holding an older lime
/// block (the marker, without an entry the block has since gained, such as
/// `.tm/cache/`, D13) gets the missing entries appended, and nothing else.
fn merged_gitignore(existing: &str, block: &str) -> Option<String> {
    if existing.lines().any(|l| l.trim() == GITIGNORE_MARKER) {
        let have: std::collections::BTreeSet<&str> = existing.lines().map(str::trim).collect();
        let missing: Vec<&str> = block
            .lines()
            .map(str::trim)
            .filter(|l| !l.is_empty() && !l.starts_with('#') && !have.contains(l))
            .collect();
        if missing.is_empty() {
            return None;
        }
        let mut out = String::from(existing);
        if !out.is_empty() && !out.ends_with('\n') {
            out.push('\n');
        }
        for l in missing {
            out.push_str(l);
            out.push('\n');
        }
        return Some(out);
    }
    let mut out = String::from(existing);
    if !out.is_empty() && !out.ends_with('\n') {
        out.push('\n');
    }
    if !out.is_empty() {
        out.push('\n');
    }
    out.push_str(block);
    Some(out)
}

/// Create the tree under `root` (§2, §14, §17 M9).
///
/// Refuses a directory that already holds something unless
/// [`Options::force`]; creates `root` and [`DIRS`] otherwise. Returns what
/// was written: a file the user owns — every §2 content file, `config.toml`,
/// a `.gitignore` that already carries the lime block — appears in
/// [`Written::unchanged`] and keeps every byte it had, so `--force` can
/// refresh the generated integration without ever costing the user an item.
pub fn write(root: &Path, opts: &Options) -> Result<Written, InitError> {
    if !opts.force && is_non_empty(root) {
        return Err(InitError::NotEmpty {
            dir: root.display().to_string(),
        });
    }
    fs::create_dir_all(root).map_err(|e| InitError::io(root.display().to_string(), e))?;
    for dir in DIRS {
        let path = root.join(dir);
        fs::create_dir_all(&path).map_err(|e| InitError::io(path.display().to_string(), e))?;
    }

    let mut written = Written::default();
    for file in files(opts) {
        let path = root.join(&file.path);
        if let Some(parent) = path.parent() {
            fs::create_dir_all(parent)
                .map_err(|e| InitError::io(parent.display().to_string(), e))?;
        }
        let text = match file.mode {
            Mode::Preserve if path.exists() => {
                written.unchanged.push(file.path.clone());
                continue;
            }
            Mode::Merge if path.exists() => {
                let existing = fs::read_to_string(&path)
                    .map_err(|e| InitError::io(path.display().to_string(), e))?;
                match merged_gitignore(&existing, &file.text) {
                    Some(text) => text,
                    None => {
                        written.unchanged.push(file.path.clone());
                        continue;
                    }
                }
            }
            _ => file.text.clone(),
        };
        fs::write(&path, &text).map_err(|e| InitError::io(path.display().to_string(), e))?;
        if file.mode == Mode::Executable {
            make_executable(&path)?;
        }
        written.created.push(file.path.clone());
    }
    if opts.force {
        remove_old_hook(root, &mut written)?;
    }
    Ok(written)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn opts() -> Options {
        Options::new(NaiveDate::from_ymd_opt(2026, 9, 7).expect("date"))
    }

    #[test]
    fn the_generated_config_is_the_default_one() {
        let files = files(&opts());
        let cfg = &files[0];
        assert_eq!(cfg.path, "config.toml");
        assert_eq!(Config::parse(&cfg.text).expect("parse"), Config::default());
        assert!(cfg.text.contains("ics_urls       = []"));
    }

    #[test]
    fn every_skill_has_front_matter_and_is_short() {
        for (name, text) in SKILLS {
            let mut lines = text.lines();
            assert_eq!(lines.next(), Some("---"), "{name}");
            let front: Vec<&str> = lines.by_ref().take_while(|l| *l != "---").collect();
            assert!(
                front.iter().any(|l| *l == format!("name: {name}")),
                "{name} front matter: {front:?}"
            );
            let description = front
                .iter()
                .find_map(|l| l.strip_prefix("description: "))
                .unwrap_or_else(|| panic!("{name} has no description"));
            // The front matter is one plain YAML scalar per key: no `: ` and
            // no ` #`, either of which would truncate it.
            assert!(!description.contains(": "), "{name}: {description}");
            assert!(!description.contains(" #"), "{name}: {description}");
            assert!(front.len() == 2, "{name} front matter: {front:?}");
            assert!(text.lines().count() < 60, "{name} is too long");
            // The commands live in fenced blocks, so `lime/tests/init_skills.rs`
            // can extract and actually run every one of them.
            assert!(
                fenced_commands(text).next().is_some(),
                "{name} documents no `lime …` command in a fenced block"
            );
        }
    }

    /// Every line of a fenced code block that starts a `lime` command — the
    /// same extraction `lime/tests/init_skills.rs` runs against the binary.
    fn fenced_commands(text: &str) -> impl Iterator<Item = &str> {
        let mut fenced = false;
        text.lines().filter_map(move |line| {
            if line.starts_with("```") {
                fenced = !fenced;
                return None;
            }
            (fenced && line.starts_with("lime ")).then_some(line)
        })
    }

    #[test]
    fn no_skill_documents_an_add_that_the_cli_would_reject() {
        // `lime add`'s line is a positional: a value starting with `- ` is read
        // as a flag and the command exits 1, so the `- [ ] ` prefix must not
        // appear in a documented command (§4.1: the prefix is optional).
        for (name, text) in SKILLS {
            for cmd in fenced_commands(text) {
                assert!(
                    !cmd.contains("\"- ") && !cmd.contains("'- "),
                    "{name}: `{cmd}` passes a line starting with `- `"
                );
            }
        }
    }

    #[test]
    fn the_users_own_files_are_never_overwritten() {
        // §2's content files are the database and `config.toml` is the user's
        // settings: `--force` refreshes lime's own files around them.
        let by_path = |opts: &Options| -> Vec<(String, Mode)> {
            files(opts)
                .into_iter()
                .map(|f| (f.path, f.mode))
                .collect()
        };
        for opts in [
            opts(),
            Options {
                example: true,
                ..opts()
            },
        ] {
            for (path, mode) in by_path(&opts) {
                let owned_by_lime = path == "CLAUDE.md"
                    || path.starts_with(".claude/")
                    || path.starts_with(HOOKS_DIR);
                let expected = match path.as_str() {
                    ".gitignore" => Mode::Merge,
                    _ if !owned_by_lime => Mode::Preserve,
                    _ if path == HOOK_SCRIPT_PATH || path.ends_with("pre-commit") => {
                        Mode::Executable
                    }
                    _ => Mode::Managed,
                };
                assert_eq!(mode, expected, "{path}");
            }
        }
    }

    #[test]
    fn today_is_resolved_in_the_configs_timezone() {
        // §16's default tz is America/Chicago: 08:00 in Tokyo on the 14th is
        // still the 13th there, which is the day `lime plan` would work on.
        let now: DateTime<FixedOffset> = "2026-09-14T08:00:00+09:00".parse().expect("instant");
        let empty = Path::new("/nonexistent-plan-dir");
        assert_eq!(
            today(empty, now),
            NaiveDate::from_ymd_opt(2026, 9, 13).expect("date")
        );

        // An existing tree's own `tz` wins (the `--force` case).
        let dir = tempfile::TempDir::new().expect("temp dir");
        fs::write(dir.path().join(store::CONFIG_PATH), "tz = \"Asia/Tokyo\"\n").expect("write");
        assert_eq!(
            today(dir.path(), now),
            NaiveDate::from_ymd_opt(2026, 9, 14).expect("date")
        );
    }

    #[test]
    fn the_month_and_week_files_keep_their_front_matter_first() {
        let files = files(&opts());
        let month = files
            .iter()
            .find(|f| f.path == "month/2026-09.md")
            .expect("month");
        assert!(month.text.starts_with("---\nmonth: 2026-09\n---\n"));
        let week = files
            .iter()
            .find(|f| f.path == "week/2026-W37.md")
            .expect("week");
        assert!(week.text.starts_with("---\nweek: 2026-W37\n"));
        assert!(week.text.contains("window: 2026-09-07..2026-09-13"));
    }

    #[test]
    fn the_gitignore_is_merged_not_rewritten() {
        assert_eq!(merged_gitignore(GITIGNORE, GITIGNORE), None);
        let merged = merged_gitignore("target/", GITIGNORE).expect("merged");
        assert!(merged.starts_with("target/\n\n"));
        assert!(merged.ends_with(GITIGNORE));
        assert_eq!(merged_gitignore("", GITIGNORE).as_deref(), Some(GITIGNORE));
        // D13: the kernel's cache is ignored, and a block from before it gains the line.
        assert!(GITIGNORE.lines().any(|l| l == ".tm/cache/"), "{GITIGNORE}");
        let old = "target/\n.tm/state.json\n.tm/last_plan.json\n.tm/arrival_plan.json\n.tm/undo.json";
        assert_eq!(merged_gitignore(old, GITIGNORE).as_deref(), Some(format!("{old}\n.tm/cache/\n").as_str()));
        assert_eq!(merged_gitignore(&format!("{old}\n.tm/cache/\n"), GITIGNORE), None);
    }
}
