//! **An old developer variable fails the arm that would have gone quiet** (AGENTS §4 D159; kernel/README.md's rename block).
//!
//! The frozen record spells `TM_ORACLE`, `TM_FORK_BLESS` and the rest. Under one of those a differential arm that reads only
//! the new name compares nothing and passes, so the arm is refused by name: `lime_core::devenv`, driven here through a real
//! test process. The second half holds new arms to it: a read in a test that goes around the helper, or an old spelling written
//! anew, is named here.

use std::path::Path;
use std::process::{Command, Output};

/// What an arm does: it asks for its variable, and under no variable it would return and pass.
#[test]
#[ignore = "run by the tests below, in its own process"]
fn an_arm_that_asks_for_its_variable() {
    if lime_core::devenv::var_os("LIME_ORACLE").is_none() {
        eprintln!("INERT");
    }
}

/// The same arm through `var`, as a bless asks.
#[test]
#[ignore = "run by the tests below, in its own process"]
fn a_bless_that_asks_for_its_variable() {
    if lime_core::devenv::var("LIME_FORK_BLESS").is_err() {
        eprintln!("INERT");
    }
}

fn run_arm(arm: &str, set: &[(&str, &str)]) -> Output {
    let mut cmd = Command::new(std::env::current_exe().expect("this test binary"));
    cmd.args(["--ignored", "--exact", arm, "--nocapture"]);
    for (k, _) in std::env::vars_os().filter(|(k, _)| k.to_string_lossy().starts_with(concat!("TM", "_"))) {
        cmd.env_remove(k);
    }
    cmd.envs(set.iter().copied());
    cmd.output().expect("run the arm")
}

fn said(o: &Output) -> String {
    format!("{}{}", String::from_utf8_lossy(&o.stdout), String::from_utf8_lossy(&o.stderr))
}

#[test]
fn an_old_oracle_variable_fails_the_arm_and_names_both_spellings() {
    let o = run_arm("an_arm_that_asks_for_its_variable", &[("TM_ORACLE", "/nonexistent")]);
    assert!(!o.status.success(), "the arm passed under the old name:\n{}", said(&o));
    assert!(said(&o).contains("TM_ORACLE") && said(&o).contains("LIME_ORACLE"), "{}", said(&o));
}

#[test]
fn an_old_bless_variable_fails_the_arm_and_names_both_spellings() {
    let o = run_arm("a_bless_that_asks_for_its_variable", &[("TM_FORK_BLESS", "1")]);
    assert!(!o.status.success(), "the bless passed under the old name:\n{}", said(&o));
    assert!(said(&o).contains("TM_FORK_BLESS") && said(&o).contains("LIME_FORK_BLESS"), "{}", said(&o));
}

/// Any old developer variable, whichever one the arm itself reads: a reader who set `TM_PLANNER_BLESS` for a
/// `LIME_ORACLE` arm is told too.
#[test]
fn an_arm_is_refused_under_an_old_name_it_does_not_read_itself() {
    let o = run_arm("an_arm_that_asks_for_its_variable", &[("TM_PLANNER_BLESS", "1")]);
    assert!(!o.status.success(), "{}", said(&o));
    assert!(said(&o).contains("LIME_PLANNER_BLESS"), "{}", said(&o));
}

/// The other direction (AGENTS §5.8): the arm still runs with nothing set, under a user's `TM_DIR`, and under the new name.
#[test]
fn the_arm_runs_with_no_old_name_set() {
    for set in [&[][..], &[("TM_DIR", "/somewhere")][..], &[("LIME_ORACLE", "/nonexistent")][..]] {
        let o = run_arm("an_arm_that_asks_for_its_variable", set);
        assert!(o.status.success(), "{set:?}\n{}", said(&o));
    }
}

fn walk(dir: &Path, out: &mut Vec<std::path::PathBuf>) {
    for entry in std::fs::read_dir(dir).expect("read_dir").flatten() {
        let p = entry.path();
        if p.is_dir() {
            if !matches!(p.file_name().and_then(|n| n.to_str()), Some("fixtures" | "snapshots" | "target")) {
                walk(&p, out);
            }
        } else {
            out.push(p);
        }
    }
}

fn repo() -> std::path::PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).parent().expect("the workspace").to_path_buf()
}

fn test_sources() -> Vec<(String, String)> {
    let root = repo();
    let mut files = Vec::new();
    for d in ["lime/tests", "lime-core/tests", "kernel/lime-kernel-ffi/tests"] {
        walk(&root.join(d), &mut files);
    }
    // This file spells both on purpose, to set them.
    files.retain(|p| p.extension().is_some_and(|e| e == "rs") && p.file_name().is_some_and(|n| n != "old_developer_names.rs"));
    files.sort();
    files
        .into_iter()
        .map(|p| (p.strip_prefix(&root).expect("under the repo").display().to_string(), std::fs::read_to_string(&p).expect("read")))
        .collect()
}

/// **A new arm's read goes through the helper.** A read that goes around it is an arm an old name can quieten. The text of a
/// read inside a string literal (`fork_rebless_history.rs`' specimens) reads no variable, and says so by its `\"`.
#[test]
fn every_read_in_a_test_goes_through_the_helper() {
    let needle = concat!("env", "::var");
    let mut around = Vec::new();
    for (name, text) in test_sources() {
        for (n, line) in text.lines().enumerate() {
            let mut from = 0;
            while let Some(i) = line[from..].find(needle) {
                let at = from + i;
                from = at + needle.len();
                let helper = line[..at].ends_with("dev");
                let specimen = line[from..].trim_start_matches("_os").starts_with("(\\\"");
                if !helper && !specimen && !line.trim_start().starts_with("//") {
                    around.push(format!("{name}:{}: {}", n + 1, line.trim()));
                }
            }
        }
    }
    assert!(around.is_empty(), "a read around lime_core::devenv:\n{}", around.join("\n"));
}

/// **An old spelling is not written anew** in a test or in the oracle's scripts: `TM_DIR` is a user's and every other
/// `TM_<NAME>` in them is a variable nothing reads.
#[test]
fn no_test_or_script_writes_an_old_developer_variable() {
    let prefix = concat!("TM", "_");
    let mut named = Vec::new();
    let mut check = |name: &str, text: &str| {
        for (n, line) in text.lines().enumerate() {
            for (i, _) in line.match_indices(prefix) {
                let boundary = !line[..i].ends_with(|c: char| c.is_ascii_alphanumeric() || c == '_');
                let word: String = line[i..].chars().take_while(|c| c.is_ascii_alphanumeric() || *c == '_').collect();
                if boundary && word.len() > prefix.len() && word != concat!("TM", "_DIR") {
                    named.push(format!("{name}:{}: {word}", n + 1));
                }
            }
        }
    };
    for (name, text) in test_sources() {
        check(&name, &text);
    }
    let oracle = repo().join("kernel/lime-kernel-ffi/examples/oracle");
    let mut files = Vec::new();
    walk(&oracle, &mut files);
    files.sort();
    for p in files {
        let name = p.strip_prefix(repo()).expect("under the repo").display().to_string();
        // The refusal itself names the variables it refuses.
        if p.extension().is_some_and(|e| e == "sh" || e == "py") && p.file_name().is_some_and(|n| n != "refuse-old-names.sh") {
            check(&name, &std::fs::read_to_string(&p).expect("read"));
        }
    }
    assert!(named.is_empty(), "an old developer variable, written anew:\n{}", named.join("\n"));
}
