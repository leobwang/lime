//! **A tree whose hooks still call the old command** (the owner's D160, parity P151): `lime check` names the hook, and
//! `lime init <the tree> --force` removes the old script. Every row runs through the binary, and the rows that
//! follow the advice run it as a user types it: with no `--dir`, from where the user stands.

mod cli_common;

use std::fs;
use std::path::Path;
use std::process::Command;

use cli_common::Lime;
use serde_json::Value;

/// The old `init`'s pre-commit, as it wrote it: blob `f68d74a`, the one version the file ever had.
const OLD_PRE_COMMIT: &str = "#!/bin/sh\n\
# tm \u{2014} validate the plan tree before every commit (tm-spec-v1.md \u{a7}1.3, \u{a7}14).\n\
#\n\
# Enable it once, from the repository root:\n\
#\n\
#     git config core.hooksPath plan/.githooks\n\
#\n\
# `tm check` exits 0 when the tree is clean and 2 when it has validation\n\
# problems (duplicate ids, dangling parents, cycles, bad values); anything\n\
# non-zero aborts the commit. Bypass one commit with `git commit --no-verify`.\n\
\n\
set -u\n\
\n\
plan=$(CDPATH='' cd -- \"$(dirname -- \"$0\")/..\" && pwd) || exit 1\n\
\n\
if ! command -v tm >/dev/null 2>&1; then\n\
\techo \"pre-commit: tm is not on PATH \u{2014} skipping tm check\" >&2\n\
\texit 0\n\
fi\n\
\n\
exec tm check --dir \"$plan\"\n";

/// The old script, from the binary's own copy.
const OLD_SCRIPT: &str = include_str!("../src/init/old-tm-check.sh");
const SCRIPT: &str = ".claude/hooks/tm-check.sh";
const NEW_SCRIPT: &str = ".claude/hooks/lime-check.sh";
const PRE_COMMIT: &str = ".githooks/pre-commit";

fn git_blob(bytes: &str) -> String {
    use std::io::Write;
    use std::process::{Command, Stdio};
    let mut child = Command::new("git").args(["hash-object", "--stdin"]).stdin(Stdio::piped()).stdout(Stdio::piped()).spawn().expect("git");
    child.stdin.take().expect("stdin").write_all(bytes.as_bytes()).expect("write");
    String::from_utf8(child.wait_with_output().expect("git hash-object").stdout).expect("utf-8").trim().to_string()
}

/// The two copies are the old `init`'s bytes, by the blob history holds and not by this file's say-so.
#[test]
fn the_old_bytes_here_are_the_blobs_history_holds() {
    assert_eq!(git_blob(OLD_SCRIPT), "c13343ce621288cb3ab479110263581d52e5557f");
    assert_eq!(git_blob(OLD_PRE_COMMIT), "f68d74a5ee8f5053fdd454bb045a34cd713dda3e");
}

/// A tree `lime init` wrote, with the old command's hooks in place of the new ones, as a tree the old binary wrote has them.
fn old_tree() -> Lime {
    let lime = Lime::empty();
    lime.ok(&["init", "--example"]);
    write(&lime, SCRIPT, OLD_SCRIPT);
    write(&lime, PRE_COMMIT, OLD_PRE_COMMIT);
    fs::remove_file(lime.plan.join(NEW_SCRIPT)).expect("the new script");
    lime
}

fn write(lime: &Lime, rel: &str, text: &str) {
    let path = lime.plan.join(rel);
    fs::create_dir_all(path.parent().expect("a parent")).expect("mkdir");
    fs::write(path, text).expect("write");
}

fn old_hook_rows(json: &Value) -> Vec<(String, u64)> {
    json["problems"]
        .as_array()
        .expect("problems")
        .iter()
        .filter(|p| p["code"] == "old-hook")
        .map(|p| (p["file"].as_str().expect("file").to_string(), p["line"].as_u64().expect("line")))
        .collect()
}

#[test]
fn check_names_both_old_hooks_and_the_exit_code_does_not_move() {
    let lime = old_tree();
    let out = lime.ok(&["check"]);
    for name in [SCRIPT, PRE_COMMIT] {
        assert!(out.stdout.contains(name), "{}", out.stdout);
    }
    assert!(out.stdout.contains("lime init "), "{}", out.stdout);
    assert!(out.stdout.contains(" --force`"), "{}", out.stdout);
    assert!(out.stdout.contains("tm check"), "{}", out.stdout);
    let json = lime.json(&["check"]);
    let rows = old_hook_rows(&json);
    let pre_commit_line = OLD_PRE_COMMIT.lines().position(|l| l.starts_with("exec tm check")).expect("the exec line") as u64 + 1;
    let script_line = OLD_SCRIPT.lines().position(|l| l.contains("$(tm check")).expect("the check line") as u64 + 1;
    assert_eq!(rows, vec![(SCRIPT.to_string(), script_line), (PRE_COMMIT.to_string(), pre_commit_line)]);
    assert_eq!(json["exit_code"], 0);
    assert!(json["problems"].as_array().expect("problems").iter().all(|p| p["code"] != "old-hook" || p["severity"] == "warning"));
}

/// Silent where there is nothing to name: a tree `lime init` wrote, and a tree with no hooks at all.
#[test]
fn check_is_silent_on_a_tree_init_wrote_and_on_one_with_no_hooks() {
    let lime = Lime::empty();
    lime.ok(&["init", "--example"]);
    assert_eq!(old_hook_rows(&lime.json(&["check"])), vec![]);
    fs::remove_dir_all(lime.plan.join(".claude")).expect("no .claude");
    fs::remove_dir_all(lime.plan.join(".githooks")).expect("no .githooks");
    assert_eq!(old_hook_rows(&lime.json(&["check"])), vec![]);
}

/// **The match**: a user's own hook that merely mentions the letters is not named, at either path.
#[test]
fn a_hook_that_merely_mentions_the_letters_is_not_named() {
    let lime = Lime::empty();
    lime.ok(&["init", "--example"]);
    let mentions = "#!/bin/sh\n\
# tm check is gone, this runs lime instead\n\
echo \"tm check is gone\"\n\
echo tm check\n\
echo 'a; tm check'\n\
tm-check --all\n\
atm check\n\
tm checkout\n\
tm plan\n\
command -v tm\n\
lime check\n";
    write(&lime, PRE_COMMIT, mentions);
    write(&lime, SCRIPT, mentions);
    assert_eq!(old_hook_rows(&lime.json(&["check"])), vec![]);
}

/// A hook of the user's that does run the old command is named, in each shape a shell starts a command.
#[test]
fn a_hook_that_runs_the_old_command_is_named_in_each_shape() {
    for line in ["tm check", "  tm  check --dir .", "exec tm check", "out=$(tm check 2>&1)", "x=\"$(tm check)\"", "true && tm check", "true; tm check", "if tm check; then :; fi", "! tm check"] {
        let lime = Lime::empty();
        lime.ok(&["init", "--example"]);
        write(&lime, PRE_COMMIT, &format!("#!/bin/sh\n{line}\n"));
        assert_eq!(old_hook_rows(&lime.json(&["check"])), vec![(PRE_COMMIT.to_string(), 2)], "{line}");
    }
}

#[test]
fn force_removes_the_generated_script_says_so_and_check_goes_silent() {
    let lime = old_tree();
    let out = lime.ok(&["init", "--force"]);
    assert!(!lime.exists(SCRIPT));
    assert!(lime.exists(NEW_SCRIPT));
    assert!(out.stdout.contains(&format!("removed {SCRIPT}")), "{}", out.stdout);
    assert!(!lime.read(PRE_COMMIT).contains("tm check"));
    assert_eq!(old_hook_rows(&lime.json(&["check"])), vec![]);
}

#[test]
fn force_reports_the_removal_in_json() {
    let lime = old_tree();
    let json = lime.json(&["init", "--force"]);
    assert_eq!(json["removed"], serde_json::json!([SCRIPT]));
    assert!(json.get("left_edited").is_none(), "{json}");
}

/// Line endings a checkout changed are nothing a user wrote.
#[test]
fn force_removes_the_generated_script_with_crlf_line_endings() {
    let lime = old_tree();
    write(&lime, SCRIPT, &OLD_SCRIPT.replace('\n', "\r\n"));
    lime.ok(&["init", "--force"]);
    assert!(!lime.exists(SCRIPT));
}

/// **An edit is the user's**: the file stays, byte for byte, the reply says so, and `check` keeps naming it while it runs the old command.
#[test]
fn force_leaves_an_edited_script_and_says_so() {
    let lime = old_tree();
    let edited = format!("{OLD_SCRIPT}# mine\n");
    write(&lime, SCRIPT, &edited);
    let out = lime.ok(&["init", "--force"]);
    assert_eq!(lime.read(SCRIPT), edited);
    assert!(out.stdout.contains(&format!("left {SCRIPT}")), "{}", out.stdout);
    let json = lime.json(&["init", "--force"]);
    assert_eq!(json["left_edited"], serde_json::json!([SCRIPT]));
    assert!(json.get("removed").is_none(), "{json}");
    assert_eq!(old_hook_rows(&lime.json(&["check"])).len(), 1);
    assert!(lime.ok(&["check"]).stdout.contains("you edited this file"));
}

/// Only that file: another file beside it, whatever it is called, is not touched.
#[test]
fn force_removes_only_that_file() {
    let lime = old_tree();
    write(&lime, ".claude/hooks/tm-other.sh", OLD_SCRIPT);
    write(&lime, ".claude/tm-check.sh", OLD_SCRIPT);
    lime.ok(&["init", "--force"]);
    assert!(lime.exists(".claude/hooks/tm-other.sh"));
    assert!(lime.exists(".claude/tm-check.sh"));
}

/// A tree with no old script: `--force` removes nothing, says nothing about it, and its `--json` has no new key.
#[test]
fn force_on_a_tree_with_no_old_script_says_nothing_of_it() {
    let lime = Lime::empty();
    lime.ok(&["init", "--example"]);
    let out = lime.ok(&["init", "--force"]);
    assert!(!out.stdout.contains("removed") && !out.stdout.contains("tm-check"), "{}", out.stdout);
    let json = lime.json(&["init", "--force"]);
    assert!(json.get("removed").is_none() && json.get("left_edited").is_none(), "{json}");
}

/// A plain `init` removes nothing: only `--force` touches an existing tree.
#[test]
fn init_without_force_still_refuses_a_tree_with_the_old_script() {
    let lime = old_tree();
    let out = lime.run(&["init"]);
    assert_ne!(out.code, 0);
    assert!(lime.exists(SCRIPT));
}

/// The binary as a user types it: no `--dir`, no `--now`, at `cwd`, with exactly `envs` answering the lookup and
/// the binary's own directory first on `PATH`, so a command the warning or the README prints runs by name.
fn shell(cwd: &Path, envs: &[(&str, &Path)], line: &str) -> std::process::Output {
    let bin = Path::new(env!("CARGO_BIN_EXE_lime")).parent().expect("the binary's directory");
    let mut cmd = Command::new("sh");
    cmd.arg("-c").arg(line).current_dir(cwd).env_remove("LIME_DIR").env_remove("TM_DIR");
    cmd.env("PATH", format!("{}:/usr/bin:/bin", bin.display()));
    for (k, v) in envs {
        cmd.env(k, v);
    }
    cmd.output().expect("sh")
}

/// The command each `old-hook` of `lime check --json` says to run, read off its message.
fn advice(cwd: &Path, envs: &[(&str, &Path)]) -> Vec<String> {
    let out = shell(cwd, envs, "lime --json check");
    let json: Value = serde_json::from_slice(&out.stdout).unwrap_or_else(|e| panic!("{e}: {}", String::from_utf8_lossy(&out.stdout)));
    json["problems"]
        .as_array()
        .expect("problems")
        .iter()
        .filter(|p| p["code"] == "old-hook")
        .map(|p| {
            let message = p["message"].as_str().expect("message");
            let (_, after) = message.split_once("run `").or_else(|| message.split_once("so `")).unwrap_or_else(|| panic!("{message}"));
            after.split_once('`').expect("the closing backtick").0.to_string()
        })
        .collect()
}

/// `dir`'s entries, sorted: what a stray tree would show up in.
fn entries(dir: &Path) -> Vec<String> {
    let mut names: Vec<String> = fs::read_dir(dir).expect("read_dir").map(|e| e.expect("entry").file_name().to_string_lossy().into_owned()).collect();
    names.sort();
    names
}

/// The tree is up to date, and no second tree was made inside it or at `cwd`. (`init` may add this week's file under
/// `week/`, so a working directory is held to `./plan` and not to its whole listing.)
fn assert_upgraded(lime: &Lime, cwd: &Path, cwd_before: &[String], said: &std::process::Output) {
    let stdout = String::from_utf8_lossy(&said.stdout);
    assert_eq!(said.status.code(), Some(0), "{stdout} {}", String::from_utf8_lossy(&said.stderr));
    assert!(stdout.contains(&format!("removed {SCRIPT}")), "{stdout}");
    assert!(!lime.exists(SCRIPT), "{stdout}");
    assert!(lime.exists(NEW_SCRIPT), "{stdout}");
    assert!(!lime.exists("plan"), "a nested tree: {stdout}");
    assert_eq!(entries(cwd).contains(&"plan".to_string()), cwd_before.contains(&"plan".to_string()), "a stray tree at the working directory: {stdout}");
    assert_eq!(old_hook_rows(&lime.json(&["check"])), vec![]);
}

/// **The warning's advice, typed where the warning was read**: inside the tree, below it, above it, under `$LIME_DIR`
/// or `$TM_DIR` from elsewhere. The advice brings the tree up to date from each, and makes no second tree.
#[test]
fn the_warnings_advice_upgrades_the_tree_from_wherever_check_found_it() {
    for place in ["inside", "below", "above", "LIME_DIR", "TM_DIR"] {
        let lime = old_tree();
        let elsewhere = lime.tmp.path().join("elsewhere");
        fs::create_dir(&elsewhere).expect("elsewhere");
        let (cwd, envs): (std::path::PathBuf, Vec<(&str, &Path)>) = match place {
            "inside" => (lime.plan.clone(), vec![]),
            "below" => (lime.plan.join("week"), vec![]),
            "above" => (lime.tmp.path().to_path_buf(), vec![]),
            var => (elsewhere.clone(), vec![(var, lime.plan.as_path())]),
        };
        let commands = advice(&cwd, &envs);
        assert_eq!(commands.len(), 2, "{place}: {commands:?}");
        assert_eq!(commands[0], commands[1], "{place}");
        let before = entries(&cwd);
        let said = shell(&cwd, &envs, &commands[0]);
        assert_upgraded(&lime, &cwd, &before, &said);
    }
}

/// `--dir` with a relative path: the advice is absolute, so it works pasted anywhere and not only where `check` ran.
#[test]
fn the_warnings_advice_works_pasted_away_from_a_relative_dir() {
    let lime = old_tree();
    let elsewhere = lime.tmp.path().join("elsewhere");
    fs::create_dir(&elsewhere).expect("elsewhere");
    let out = shell(lime.tmp.path(), &[], "lime --dir plan --json check");
    let json: Value = serde_json::from_slice(&out.stdout).expect("json");
    let message = json["problems"].as_array().expect("problems").iter().find(|p| p["code"] == "old-hook").expect("a row")["message"].as_str().expect("message").to_string();
    let command = message.split_once("run `").expect("run").1.split_once('`').expect("the backtick").0.to_string();
    let before = entries(&elsewhere);
    assert_upgraded(&lime, &elsewhere, &before, &shell(&elsewhere, &[], &command));
}

/// A tree whose path a shell would split or trip on: the command is still one command.
#[test]
fn the_warnings_advice_quotes_a_path_a_shell_would_split() {
    for name in ["my plan", "it's mine", "a$b"] {
        let lime = old_tree();
        let renamed = lime.tmp.path().join(name);
        fs::rename(&lime.plan, &renamed).expect("rename");
        let moved = Lime { tmp: lime.tmp, plan: renamed };
        let commands = advice(&moved.plan, &[]);
        assert_eq!(commands.len(), 2, "{name}: {commands:?}");
        let before = entries(&moved.plan);
        let said = shell(&moved.plan, &[], &commands[0]);
        assert_eq!(said.status.code(), Some(0), "{name}: {}", String::from_utf8_lossy(&said.stderr));
        assert!(!moved.exists(SCRIPT), "{name}");
        assert_eq!(entries(&moved.plan).len(), before.len(), "{name}: {:?}", entries(&moved.plan));
    }
}

/// An edited script: the message names the same command, and that command leaves the file and clears the pre-commit.
#[test]
fn the_advice_on_an_edited_script_names_the_same_command() {
    let lime = old_tree();
    let edited = format!("{OLD_SCRIPT}# mine\n");
    write(&lime, SCRIPT, &edited);
    let commands = advice(&lime.plan, &[]);
    assert_eq!(commands.len(), 2, "{commands:?}");
    assert_eq!(commands[0], commands[1]);
    let said = shell(&lime.plan, &[], &commands[0]);
    assert_eq!(said.status.code(), Some(0));
    assert_eq!(lime.read(SCRIPT), edited);
    assert!(!lime.exists("plan"));
    assert_eq!(old_hook_rows(&lime.json(&["check"])), vec![(SCRIPT.to_string(), OLD_SCRIPT.lines().position(|l| l.contains("$(tm check")).expect("the line") as u64 + 1)]);
}

/// The fenced command under the root README's "Upgrading a tree from `tm`", as it stands in the file.
fn the_notes_command() -> String {
    let readme = include_str!("../../README.md");
    let (_, note) = readme.split_once("### Upgrading a tree from `tm`").expect("the note");
    let (_, fenced) = note.split_once("```sh\n").expect("the fence");
    fenced.split_once("\n```").expect("the closing fence").0.to_string()
}

/// **The README's note, followed literally, in a plan directory**, whatever the directory is called.
#[test]
fn the_readmes_note_followed_literally_upgrades_the_tree() {
    let command = the_notes_command();
    let lime = old_tree();
    let before = entries(&lime.plan);
    let said = shell(&lime.plan, &[], &command);
    assert_eq!(said.status.code(), Some(0), "{command}: {}", String::from_utf8_lossy(&said.stderr));
    assert!(!lime.exists(SCRIPT), "{command}");
    assert!(!lime.exists("plan"), "{command}: a nested tree");
    assert_eq!(entries(&lime.plan), before, "{command}");
    assert_eq!(old_hook_rows(&lime.json(&["check"])), vec![]);
    let other = old_tree();
    let notes = other.tmp.path().join("notes");
    fs::rename(&other.plan, &notes).expect("rename");
    let other = Lime { tmp: other.tmp, plan: notes };
    let said = shell(&other.plan, &[], &command);
    assert_eq!(said.status.code(), Some(0), "{command}: {}", String::from_utf8_lossy(&said.stderr));
    assert!(!other.exists(SCRIPT), "{command}");
    assert!(!other.exists("plan"), "{command}: a nested tree");
}

/// A duplicate of the example's `^t1`, staged, and a commit of it with only `lime` on `PATH`; the commit's exit code.
fn commit_a_broken_tree(repo: &Path, plan: &Path) -> Option<i32> {
    let backlog = plan.join("backlog.md");
    let text = fs::read_to_string(&backlog).expect("the backlog");
    fs::write(&backlog, format!("{text}- [ ] 2 30m a duplicate ^t1\n")).expect("the backlog");
    assert!(shell(repo, &[], "git add -A").status.success());
    shell(repo, &[], "git -c user.name=a -c user.email=a@b commit -q -m broken").status.code()
}

/// **The net comes back on**: an old tree in a repository, its `core.hooksPath` set as the old reply said, a broken commit
/// passing; then the note's command typed in the plan directory and the reply's own `git config` line followed; then the
/// same commit refused. At a tree in a subdirectory of the repository, where a relative hint would point at nothing, and at
/// its top.
#[test]
fn the_note_and_the_replys_hint_put_the_validation_net_back_on() {
    let command = the_notes_command();
    for at_top in [false, true] {
        let lime = old_tree();
        let repo = if at_top { lime.plan.clone() } else { lime.tmp.path().to_path_buf() };
        let hooks = if at_top { ".githooks" } else { "plan/.githooks" };
        for line in ["git init -q .".to_string(), format!("git config core.hooksPath {hooks}"), "git add -A".to_string(), "git -c user.name=a -c user.email=a@b commit -q --no-verify -m one".to_string()] {
            assert!(shell(&repo, &[], &line).status.success(), "{line}");
        }
        let said = shell(&lime.plan, &[], &command);
        assert_eq!(said.status.code(), Some(0), "{command}");
        let stdout = String::from_utf8_lossy(&said.stdout).into_owned();
        let hint = stdout.lines().find(|l| l.trim_start().starts_with("git config core.hooksPath")).expect("the hint").trim().to_string();
        assert!(shell(&lime.plan, &[], &hint).status.success(), "{hint}");
        assert_ne!(commit_a_broken_tree(&repo, &lime.plan), Some(0), "at_top {at_top}: the hook let a broken tree through after `{hint}`");
    }
}

/// What the note warns of, as it stands (README gap 6103, the owner's): a bare `lime init --force` does not look for the
/// plan, so inside a tree it makes a second tree at `./plan` and leaves this one as it was.
#[test]
fn a_bare_force_inside_a_tree_makes_a_new_tree_as_the_note_warns() {
    let lime = old_tree();
    let said = shell(&lime.plan, &[], "lime init --force");
    assert_eq!(said.status.code(), Some(0));
    assert!(lime.exists("plan/config.toml"));
    assert!(lime.exists(SCRIPT));
    assert_eq!(old_hook_rows(&lime.json(&["check"])).len(), 2);
}
