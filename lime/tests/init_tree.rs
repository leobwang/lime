//! `lime init`: the generated tree and the Claude Code integration
//! (lime-spec-v1.md §2, §14, §16; §17 M9 — "`lime init` produces a tree that
//! passes `lime check`").
//!
//! Every test runs the real binary against a fresh temporary directory, at
//! the fixed instant `cli_common::NOW` (Monday 2026-09-07), so the month and
//! week files are `month/2026-09.md` and `week/2026-W37.md`.

mod cli_common;

use std::path::{Path, PathBuf};
use std::process::Command;

use cli_common::Lime;
use lime_core::config::Config;

/// §14's skills, in table order.
const SKILLS: &[&str] = &[
    "plan-week",
    "plan-month",
    "triage",
    "capture",
    "replan",
    "review-day",
    "review-week",
    "explain",
];

/// Every file §2 and §14 promise, besides the skills.
const FILES: &[&str] = &[
    "config.toml",
    "CLAUDE.md",
    ".claude/settings.json",
    ".claude/hooks/lime-check.sh",
    ".githooks/pre-commit",
    ".gitignore",
    "inbox.md",
    "backlog.md",
    "routines.md",
    "optional.md",
    "month/2026-09.md",
    "week/2026-W37.md",
];

/// `lime/templates/…`.
fn template(rel: &str) -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("templates")
        .join(rel)
}

/// A fresh tree at [`cli_common::NOW`].
fn init() -> Lime {
    let lime = Lime::empty();
    let out = lime.run(&["init"]);
    assert_eq!(out.code, 0, "{}{}", out.stdout, out.stderr);
    lime
}

#[test]
fn init_writes_every_file_and_directory_the_layout_names() {
    let lime = init();
    for rel in FILES {
        assert!(lime.exists(rel), "missing {rel}");
    }
    for name in SKILLS {
        let rel = format!(".claude/skills/{name}/SKILL.md");
        assert!(lime.exists(&rel), "missing {rel}");
    }
    // §2's two directories that carry no generated file of their own.
    assert!(lime.plan.join("calendar").is_dir());
    assert!(lime.plan.join(".tm").is_dir());
    // §13 prints the git instruction instead of rewriting the user's config.
    let out = Lime::empty();
    let human = out.run(&["init"]);
    assert!(
        human.stdout.contains("git config core.hooksPath"),
        "{}",
        human.stdout
    );
}

#[test]
fn the_generated_config_is_the_default_config() {
    // §16, and §15: no calendar URL, the example one as a comment.
    let lime = init();
    let text = lime.read("config.toml");
    assert_eq!(Config::parse(&text).expect("parses"), Config::default());
    assert!(text.contains("ics_urls       = []"), "{text}");
    assert!(
        text.contains("# e.g. [\"https://calendar.google.com/"),
        "{text}"
    );
    assert_eq!(text, Config::default_toml());
}

#[test]
fn the_generated_tree_passes_check() {
    // §17 M9's definition of done.
    let lime = init();
    let check = lime.run(&["check"]);
    assert_eq!(check.code, 0, "{}{}", check.stdout, check.stderr);
    assert!(check.stdout.contains("no problems"), "{}", check.stdout);

    // The starting files are guidance only: nothing to triage, nothing to do.
    let triage = lime.json(&["triage"]);
    assert_eq!(
        triage["lines"].as_array().expect("lines").len(),
        0,
        "the inbox guidance must not parse as captures: {triage}"
    );
    assert_eq!(lime.run(&["plan"]).code, 0);
}

#[test]
fn the_month_and_week_files_are_todays() {
    let lime = init();
    let month = lime.read("month/2026-09.md");
    assert!(month.starts_with("---\nmonth: 2026-09\n---\n"), "{month}");
    assert!(month.contains("# Outcomes"), "{month}");
    let week = lime.read("week/2026-W37.md");
    assert!(
        week.starts_with("---\nweek: 2026-W37\nwindow: 2026-09-07..2026-09-13\n---\n"),
        "{week}"
    );
    assert!(week.contains("# Milestones"), "{week}");
    assert!(week.contains("# Tasks"), "{week}");
}

#[test]
fn claude_md_is_the_section_14_text() {
    let lime = init();
    let text = lime.read("CLAUDE.md");
    assert!(text.lines().count() < 100, "§14: keep it under ~100 lines");
    insta::assert_snapshot!("claude_md", text);
}

/// Run a hook script with `payload` on stdin and the binary under test on
/// `PATH` — what Claude Code and git do.
fn run_hook(script: &Path, payload: Option<&str>) -> std::process::Output {
    let bin = Path::new(env!("CARGO_BIN_EXE_lime"));
    let path = format!(
        "{}:{}",
        bin.parent().expect("bin dir").display(),
        lime_core::devenv::var("PATH").unwrap_or_default()
    );
    let mut cmd = Command::new("sh");
    cmd.arg(script)
        .env("PATH", &path)
        .stdin(std::process::Stdio::piped())
        .stdout(std::process::Stdio::piped())
        .stderr(std::process::Stdio::piped());
    let mut child = cmd.spawn().expect("run the hook");
    {
        use std::io::Write;
        let mut stdin = child.stdin.take().expect("stdin");
        stdin
            .write_all(payload.unwrap_or("").as_bytes())
            .expect("write the payload");
    }
    child.wait_with_output().expect("hook output")
}

/// A `PostToolUse` payload for an edit to `file`.
fn payload(file: &Path) -> String {
    format!(
        "{{\"hook_event_name\":\"PostToolUse\",\"tool_name\":\"Edit\",\
         \"tool_input\":{{\"file_path\":\"{}\"}}}}",
        file.display()
    )
}

#[test]
fn the_settings_hook_checks_the_tree_after_every_edit() {
    let lime = init();
    let text = lime.read(".claude/settings.json");
    let json: serde_json::Value = serde_json::from_str(&text).expect("settings.json is JSON");
    let hook = &json["hooks"]["PostToolUse"][0];
    assert_eq!(hook["matcher"], "Edit|MultiEdit|Write");
    // §14's "under `plan/`": a matcher matches tool names, so the scoping and
    // the reporting live in the script the command runs.
    let command = hook["hooks"][0]["command"].as_str().expect("a command");
    assert!(command.contains(".claude/hooks/lime-check.sh"), "{command}");
    assert!(lime.exists(".claude/hooks/lime-check.sh"));
    insta::assert_snapshot!("settings_json", text);
}

#[test]
fn the_post_tool_use_hook_only_fires_for_the_plan_tree() {
    let lime = init();
    let script = lime.plan.join(".claude/hooks/lime-check.sh");
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        let mode = std::fs::metadata(&script)
            .expect("hook")
            .permissions()
            .mode();
        assert!(mode & 0o111 != 0, "the hook is not executable: {mode:o}");
    }

    // A clean tree: nothing to say, nothing blocked.
    let clean = run_hook(&script, Some(&payload(&lime.plan.join("backlog.md"))));
    assert_eq!(clean.status.code(), Some(0), "{clean:?}");

    // A broken one: exit 2 (Claude Code's blocking code) with the diagnostics
    // on *stderr*, the only stream it feeds back to the model — `lime check`
    // itself prints them on stdout, so a bare `lime check` would block the turn
    // with an empty message.
    std::fs::write(
        lime.plan.join("backlog.md"),
        "# Untied\n- [ ] 3 1b Orphan @nope ^zzz9\n",
    )
    .expect("write");
    let dirty = run_hook(&script, Some(&payload(&lime.plan.join("backlog.md"))));
    assert_eq!(dirty.status.code(), Some(2), "{dirty:?}");
    let stderr = String::from_utf8_lossy(&dirty.stderr);
    assert!(stderr.contains("dangling-parent"), "stderr was: {stderr:?}");
    assert!(
        String::from_utf8_lossy(&dirty.stdout).trim().is_empty(),
        "the diagnostics must not go to stdout: {:?}",
        dirty.stdout
    );

    // The same broken tree, but the edit was somewhere else: not our business
    // (§14 scopes the hook to `plan/`), so no turn is blocked by it.
    for outside in [
        lime.tmp.path().join("README.md"),
        lime.plan.join(".tm/state.json"),
    ] {
        let out = run_hook(&script, Some(&payload(&outside)));
        assert_eq!(out.status.code(), Some(0), "{}: {out:?}", outside.display());
    }

    // A payload with no `file_path` (or no payload at all) is not a reason to
    // block anything either.
    let empty = run_hook(&script, None);
    assert_eq!(empty.status.code(), Some(0), "{empty:?}");
}

#[test]
fn every_skill_declares_its_name_and_trigger() {
    let lime = init();
    for name in SKILLS {
        let text = lime.read(&format!(".claude/skills/{name}/SKILL.md"));
        assert!(text.starts_with("---\n"), "{name} has no front matter");
        assert!(
            text.contains(&format!("\nname: {name}\n")),
            "{name}: {text}"
        );
        let description = text
            .lines()
            .find(|l| l.starts_with("description: "))
            .unwrap_or_else(|| panic!("{name} has no description"));
        assert!(
            description.contains("Use when")
                || description.contains("Use at")
                || description.contains("Use after"),
            "{name}'s description states no trigger: {description}"
        );
        assert!(text.lines().count() < 60, "{name} is longer than ~60 lines");
        // Every verb it names lives in a fenced block, so `init_skills.rs`
        // can run it: prose mentioning "lime" is not a documented command.
        let mut fenced = false;
        let commands = text.lines().filter(|line| {
            if line.starts_with("```") {
                fenced = !fenced;
                return false;
            }
            fenced && line.starts_with("lime ")
        });
        assert!(
            commands.count() > 0,
            "{name} documents no `lime …` command in a fenced block"
        );
    }
    // One in full: the Sunday planning conversation, with its confirmation rule.
    let plan_week = lime.read(".claude/skills/plan-week/SKILL.md");
    // §14's confirmation rule: it writes `week/<next>.md` only after a yes.
    assert!(plan_week.contains("only after confirmation"), "{plan_week}");
    assert!(
        plan_week.contains("before the user says yes"),
        "{plan_week}"
    );
    insta::assert_snapshot!("skill_plan_week", plan_week);
}

#[test]
fn the_pre_commit_hook_runs_lime_check_and_fails_the_commit() {
    let lime = init();
    let hook = lime.plan.join(".githooks/pre-commit");
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        let mode = std::fs::metadata(&hook).expect("hook").permissions().mode();
        assert!(mode & 0o111 != 0, "the hook is not executable: {mode:o}");
    }
    assert!(lime.read(".githooks/pre-commit").contains("lime check"));

    // Run it with the binary under test on PATH: clean tree → 0.
    let bin = Path::new(env!("CARGO_BIN_EXE_lime"));
    let path = format!(
        "{}:{}",
        bin.parent().expect("bin dir").display(),
        lime_core::devenv::var("PATH").unwrap_or_default()
    );
    let run = |hook: &Path| {
        Command::new("sh")
            .arg(hook)
            .env("PATH", &path)
            .output()
            .expect("run the hook")
    };
    let clean = run(&hook);
    assert_eq!(clean.status.code(), Some(0), "{clean:?}");

    // A dangling parent is a §13 exit-2 problem, so the commit is refused.
    let backlog = lime.plan.join("backlog.md");
    std::fs::write(&backlog, "# Untied\n- [ ] 3 1b Orphan @nope ^zzz9\n").expect("write");
    let dirty = run(&hook);
    assert_eq!(dirty.status.code(), Some(2), "{dirty:?}");
}

#[test]
fn the_gitignore_keeps_the_runtime_state_out_of_git() {
    let lime = init();
    let text = lime.read(".gitignore");
    assert!(text.lines().any(|l| l == ".tm/state.json"), "{text}");

    // It belongs to the user: `--force` extends it, never rewrites it.
    std::fs::write(lime.plan.join(".gitignore"), "target/\n").expect("write");
    let json = lime.json(&["init", "--force"]);
    let created: Vec<&str> = json["created"]
        .as_array()
        .expect("created")
        .iter()
        .map(|v| v.as_str().unwrap_or_default())
        .collect();
    assert!(created.contains(&".gitignore"), "{created:?}");
    let text = lime.read(".gitignore");
    assert!(text.starts_with("target/\n"), "{text}");
    assert!(text.lines().any(|l| l == ".tm/state.json"), "{text}");

    // A second `--force` finds its block already there and changes nothing.
    let before = lime.read(".gitignore");
    let json = lime.json(&["init", "--force"]);
    assert_eq!(lime.read(".gitignore"), before);
    let created: Vec<&str> = json["created"]
        .as_array()
        .expect("created")
        .iter()
        .map(|v| v.as_str().unwrap_or_default())
        .collect();
    assert!(!created.contains(&".gitignore"), "{created:?}");

    // D13: the kernel's cache stays out of git, and a plan initialised before the
    // cache existed gains the line on `--force`, keeping every line it had.
    assert!(lime.read(".gitignore").lines().any(|l| l == ".tm/cache/"));
    let old = "target/\n.tm/state.json\n.tm/last_plan.json\n.tm/arrival_plan.json\n.tm/undo.json\n";
    std::fs::write(lime.plan.join(".gitignore"), old).expect("write");
    lime.json(&["init", "--force"]);
    assert_eq!(lime.read(".gitignore"), format!("{old}.tm/cache/\n"));
}

#[test]
fn init_takes_the_directory_as_a_flag_or_a_positional() {
    // `--dir` is global (§13: every verb takes it), and `lime init --help`
    // promises it. `lime init [dir]` used to shadow it — the positional's clap
    // id was the global's — so `lime init --dir X` died with "unexpected
    // argument '--dir' found" while `lime --dir X init` worked.
    let lime = Lime::empty();
    let root = lime.tmp.path();
    let run = |args: &[&str]| {
        let out = Command::new(env!("CARGO_BIN_EXE_lime"))
            .args(args)
            .arg("--now")
            .arg(cli_common::NOW)
            .env_remove("LIME_DIR")
            .env_remove("TM_DIR")
            .output()
            .expect("run lime");
        assert!(
            out.status.success(),
            "`lime {}` failed: {}",
            args.join(" "),
            String::from_utf8_lossy(&out.stderr)
        );
        serde_json::from_slice::<serde_json::Value>(&out.stdout).expect("JSON")
    };
    let path = |name: &str| root.join(name).to_str().expect("utf-8").to_string();
    let (flag, global, positional) = (path("flag"), path("global"), path("positional"));
    let (winner, loser) = (path("winner"), path("loser"));

    // All three spellings work…
    let after = run(&["init", "--dir", &flag, "--json"]);
    let before = run(&["--dir", &global, "init", "--json"]);
    let bare = run(&["init", &positional, "--json"]);
    for dir in [&flag, &global, &positional] {
        assert!(
            Path::new(dir).join("config.toml").is_file(),
            "no tree in {dir}"
        );
    }
    // …and agree, down to the files they wrote.
    assert_eq!(after["dir"], flag);
    assert_eq!(before["dir"], global);
    assert_eq!(bare["dir"], positional);
    assert_eq!(after["created"], before["created"]);
    assert_eq!(after["created"], bare["created"]);

    // Given both, the positional wins (`lime init --help`, README).
    let both = run(&["init", &winner, "--dir", &loser, "--json"]);
    assert_eq!(both["dir"], winner);
    assert!(Path::new(&winner).join("config.toml").is_file());
    assert!(!Path::new(&loser).exists(), "--dir was used after all");
}

#[test]
fn init_refuses_a_non_empty_directory_without_force() {
    let lime = Lime::empty();
    std::fs::create_dir_all(&lime.plan).expect("mkdir");
    std::fs::write(lime.plan.join("notes.md"), "mine\n").expect("write");

    let refused = lime.run(&["init"]);
    assert_eq!(refused.code, 1, "{}{}", refused.stdout, refused.stderr);
    assert!(refused.stderr.contains("not empty"), "{}", refused.stderr);
    assert!(refused.stderr.contains("--force"), "{}", refused.stderr);
    assert!(!lime.exists("config.toml"), "nothing was written");
    assert_eq!(lime.read("notes.md"), "mine\n");

    let forced = lime.run(&["init", "--force"]);
    assert_eq!(forced.code, 0, "{}{}", forced.stdout, forced.stderr);
    assert!(lime.exists("config.toml"));
    assert_eq!(
        lime.read("notes.md"),
        "mine\n",
        "--force adds, it does not clear"
    );
}

#[test]
fn the_month_and_week_files_follow_the_configs_timezone() {
    // §16's `tz` (default America/Chicago) is what every other verb resolves
    // `--now` in, so the fresh tree must be dated in it and not in whatever
    // offset the machine (or `--now`) happens to carry: 08:00 in Tokyo on the
    // 14th is still Sunday the 13th in Chicago, ISO week 2026-W37.
    let lime = Lime::empty();
    let now = "2026-09-14T08:00:00+09:00";
    let out = lime.run_at(now, &["init"]);
    assert_eq!(out.code, 0, "{}{}", out.stdout, out.stderr);
    assert_eq!(lime.json_at(now, &["plan"])["date"], "2026-09-13");
    assert!(lime.exists("week/2026-W37.md"), "the current week is missing");
    assert!(!lime.exists("week/2026-W38.md"), "a stray next-week file");
    assert!(lime.exists("month/2026-09.md"));
}

#[test]
fn force_refreshes_limes_files_and_never_the_users() {
    // §2: the item files are the database. `--force` is the upgrade path for
    // the generated integration, not a way to lose a week of work.
    let lime = init();
    lime.ok(&["add", "5 6b Finish ch.5 exercises", "--to", "week"]);
    lime.ok(&["add", "3 2b Renew insurance", "--to", "backlog"]);
    let week = lime.read("week/2026-W37.md");
    let backlog = lime.read("backlog.md");
    std::fs::write(lime.plan.join("config.toml"), "tz = \"Europe/Berlin\"\n").expect("write");
    std::fs::write(lime.plan.join("CLAUDE.md"), "stale\n").expect("write");

    let json = lime.json(&["init", "--force"]);
    let names = |key: &str| -> Vec<String> {
        json[key]
            .as_array()
            .expect(key)
            .iter()
            .map(|v| v.as_str().unwrap_or_default().to_string())
            .collect()
    };
    let (created, skipped) = (names("created"), names("skipped"));

    // Every file whose content is the user's survives, and is reported.
    assert_eq!(lime.read("week/2026-W37.md"), week);
    assert_eq!(lime.read("backlog.md"), backlog);
    assert_eq!(lime.read("config.toml"), "tz = \"Europe/Berlin\"\n");
    for kept in [
        "config.toml",
        "backlog.md",
        "inbox.md",
        "routines.md",
        "optional.md",
        "month/2026-09.md",
        "week/2026-W37.md",
    ] {
        assert!(skipped.contains(&kept.to_string()), "{kept}: {skipped:?}");
        assert!(!created.contains(&kept.to_string()), "{kept}: {created:?}");
    }
    // And lime's own files are brought up to date.
    assert!(lime.read("CLAUDE.md").starts_with("# lime — rules for Claude Code"));
    for refreshed in [
        "CLAUDE.md",
        ".claude/settings.json",
        ".claude/hooks/lime-check.sh",
        ".claude/skills/capture/SKILL.md",
        ".githooks/pre-commit",
    ] {
        assert!(created.contains(&refreshed.to_string()), "{created:?}");
    }
    // The human output says what it left alone.
    let human = lime.run(&["init", "--force"]);
    assert!(human.stdout.contains("left alone"), "{}", human.stdout);
    assert!(human.stdout.contains("backlog.md"), "{}", human.stdout);
}

#[test]
fn example_writes_the_spec_tree_and_plans() {
    let lime = Lime::empty();
    assert_eq!(lime.run(&["init", "--example"]).code, 0);

    // §4.3's tree, so a new user sees the grammar working.
    assert!(lime.read("week/2026-W37.md").contains("^m1"));
    assert!(lime.read("month/2026-09.md").contains("# Demoted"));
    assert!(lime.read("calendar/2026-W37.md").contains("Meeting w/ host"));
    assert!(lime.read("day/2026-09-07.md").contains("# Pinned"));
    assert!(lime.read("routines.md").contains("- lunch"));
    assert!(lime.read("optional.md").contains("Severance"));
    assert!(lime.read("inbox.md").contains("pset2"));

    let check = lime.run(&["check"]);
    assert_eq!(check.code, 0, "{}{}", check.stdout, check.stderr);

    let plan = lime.run(&["plan"]);
    assert_eq!(plan.code, 0, "{}{}", plan.stdout, plan.stderr);
    // The wall from `calendar/` lands in the day (§8.2 step 1).
    assert!(plan.stdout.contains("Meeting w/ host"), "{}", plan.stdout);
    assert!(lime.read("day/2026-09-07.md").contains("<!-- tm:plan start"));
    assert_eq!(lime.run(&["triage"]).code, 0);
}

#[test]
fn the_example_templates_are_the_plan_basic_fixture() {
    // §17.1: `--example` is the fixture, byte for byte, so the tree a new
    // user gets is the tree the planner's tests run against.
    let fixture =
        Path::new(env!("CARGO_MANIFEST_DIR")).join("../lime-core/tests/fixtures/plan-basic");
    for (t, f) in [
        ("example/inbox.md", "inbox.md"),
        ("example/backlog.md", "backlog.md"),
        ("example/routines.md", "routines.md"),
        ("example/optional.md", "optional.md"),
        ("example/month.md", "month/2026-09.md"),
        ("example/week.md", "week/2026-W37.md"),
        ("example/calendar.md", "calendar/2026-W37.md"),
        ("example/day.md", "day/2026-09-07.md"),
    ] {
        let ours = std::fs::read_to_string(template(t)).expect(t);
        let theirs = std::fs::read_to_string(fixture.join(f)).expect(f);
        assert_eq!(ours, theirs, "{t} has drifted from {f}");
    }
}

/// **No item line of a shipped template carries two estimates — but the one D127 left** (the owner's D127,
/// parity P126; W-49 track E). A line with a leading estimate AND an `est:` key is D56's two-estimates
/// class: the row prints one and the planner reads the other. Asked of EVERY markdown file under
/// `lime/templates/` (the class, not the `^t3` line D127 names), the set of such lines is exactly the one
/// `# Demoted` record `^m2` in `example/month.md`, whose two estimates are equal and which no decision
/// has reached (README gap 5383); `^t3` left the set at D127, and a template line that joins it fails here.
#[test]
fn no_item_line_of_a_shipped_template_carries_two_estimates_but_the_demoted_record() {
    fn is_duration(t: &str) -> bool {
        t.starts_with(|c: char| c.is_ascii_digit())
            && t.ends_with(|c: char| "bmhd".contains(c))
            && t.chars().all(|c| c.is_ascii_digit() || "bmhd".contains(c))
    }
    // `- [x] [ci] [!k] <estimate> …` with an `est:` key on the same line.
    fn two_estimates(line: &str) -> bool {
        let Some(rest) = line.trim_start().strip_prefix("- [").and_then(|r| r.get(1..)).and_then(|r| r.strip_prefix("] ")) else {
            return false;
        };
        let mut words = rest.split_whitespace().peekable();
        if words.peek().is_some_and(|w| w.len() == 1 && w.chars().all(|c| c.is_ascii_digit())) {
            words.next();
        }
        if words.peek().is_some_and(|w| w.starts_with('!')) {
            words.next();
        }
        words.next().is_some_and(is_duration) && rest.split_whitespace().any(|w| w.starts_with("est:"))
    }
    assert!(two_estimates("- [>] 4 2b Exercises 5.3–5.5            @m1 est:1b ^t3"), "the reader sees D56's class");
    assert!(!two_estimates("- [>] 4 1b Exercises 5.3–5.5            @m1 ^t3"), "and not a line with one estimate");
    assert!(!two_estimates("- [ ] 3 Write the intro est:1b ^t9"), "nor an `est:` key alone");
    let mut found = Vec::new();
    let mut files = 0usize;
    let mut stack = vec![template("")];
    while let Some(dir) = stack.pop() {
        for e in std::fs::read_dir(&dir).expect("the templates") {
            let path = e.expect("an entry").path();
            if path.is_dir() {
                stack.push(path);
            } else if path.extension().is_some_and(|x| x == "md") {
                files += 1;
                let text = std::fs::read_to_string(&path).expect("a template");
                found.extend(text.lines().filter(|l| two_estimates(l)).map(|l| l.trim().to_string()));
            }
        }
    }
    assert!(files >= 8, "the walk read {files} template file(s)");
    assert_eq!(found, ["- [-] 4 3b Rollback path passes tests @O2 est:3b demoted:W37 ^m2"], "two-estimate template lines");
}

/// **The bare-`lime init` landmine, cleared at the kernel** (kernel/README.md,
/// 2026-09-12 "a comment is prose" block).  The starter templates' guidance
/// comments carry their natural `- [ ]` example lines again — ids, an
/// `@parent` and an `after:` dependency on ids that exist only inside
/// `<!-- -->` — and a fresh tree still loads: every kernel-backed verb
/// (`add`, the keyed `edit`, `rank`, `move`, `demote`, `readopt`, `drop`)
/// succeeds on it, and every comment comes back byte for byte.  Before the
/// kernel read comments as prose, the first of these exited 1 with
/// `itemCheck: danglingDep`.
#[test]
fn every_kernel_backed_verb_works_on_a_bare_init_tree() {
    let lime = init();
    let week = lime.read("week/2026-W37.md");
    assert!(
        week.contains("    - [ ] 3 1b Review the drafts            @m2 after:^t4 ^t5"),
        "the landmine must be armed for this test to mean anything: {week}"
    );
    assert!(
        lime.read("month/2026-09.md")
            .contains("    - [ ] 5 !1 Lean: through ch.8 of the tutorial          ^O1")
    );
    assert!(lime
        .read("backlog.md")
        .contains("    - [ ] 2 30m Insurance claim for the bike  ^a1"));
    let comment = |text: &str| -> String {
        let start = text.find("<!--").expect("a comment");
        let end = text.find("-->").expect("closed") + 3;
        text[start..end].to_string()
    };
    let before: Vec<(&str, String)> = ["week/2026-W37.md", "month/2026-09.md", "backlog.md"]
        .into_iter()
        .map(|f| (f, comment(&lime.read(f))))
        .collect();

    let first = lime.json(&["add", "4 2b Write the release notes", "--to", "week"]);
    let first = first["id"].as_str().expect("an id").to_string();
    let second = lime.json(&["add", "3 1b Second task", "--to", "week"]);
    let second = second["id"].as_str().expect("an id").to_string();
    let (first, second) = (format!("^{first}"), format!("^{second}"));

    lime.ok(&["edit", &first, "est=3b"]);
    // D56 (W-35): the line's leading `2b` is the slot, so it is rewritten in
    // place as written — `3b`, one estimate — where `est:180m` used to be
    // appended beside it.
    let week = lime.read("week/2026-W37.md");
    assert!(week.contains("- [ ] 4 3b Write the release notes"), "{week}");
    assert!(!week.contains("est:180m"), "{week}");
    assert_eq!(lime.json(&["rank", &second, "1"])["moved"], true);
    lime.ok(&["move", &second, "backlog"]);
    assert!(lime.read("backlog.md").contains(&second));
    lime.ok(&["demote", &first]);
    lime.ok_at(
        "2026-09-07T09:01:00-05:00",
        &["readopt", &first, "--to", "week/2026-W38.md"],
    );
    assert!(lime.read("week/2026-W38.md").contains(&first));
    lime.ok(&["drop", &second]);
    assert!(lime.read("backlog.md").contains("- [~] 3 1b Second task"));

    for (f, c) in before {
        assert_eq!(comment(&lime.read(f)), c, "{f}'s guidance comment changed");
    }
    let check = lime.run(&["check"]);
    assert_eq!(check.code, 0, "{}{}", check.stdout, check.stderr);
}
