//! **A developer variable, read so that its old spelling cannot go quiet** (AGENTS §4 D159; kernel/README.md's
//! rename block).
//!
//! The rename turned every `TM_*` developer variable into `LIME_*`, and the frozen record still spells the old one:
//! `TM_ORACLE=... cargo test` is what a reader of the ledger types. An arm that reads only `LIME_ORACLE` then goes
//! inert and passes, having compared nothing, which is AGENTS §9.2's disguised gap. So every read in a test goes
//! through here (`lime/tests/old_developer_names.rs` holds them to it), and any `TM_*` in the environment fails the
//! arm by name. `TM_DIR` is a user's, in a shell profile, and still answers (`resolve_dir`); it is the one exception.
//!
//! Nothing in the binary calls this. `kernel/lime-kernel-ffi/tests/corpus.rs` includes this file by `#[path]`, since
//! that crate cannot depend on this one, so there is one definition.

use std::env::VarError;
use std::ffi::{OsStr, OsString};

/// A variable with this prefix is an old developer variable, unless it is the one a user holds.
const OLD_PREFIX: &str = "TM_";
const A_USERS: &str = "TM_DIR";

/// The refusal, when an old developer variable is set. `old_names`, so that a test can read it without a panic.
pub fn refusal(old_names: impl IntoIterator<Item = String>) -> Option<String> {
    let mut old: Vec<String> = old_names.into_iter().filter(|k| k.starts_with(OLD_PREFIX) && k != A_USERS).collect();
    old.sort();
    let first = old.first()?;
    let new = format!("LIME_{}", &first[OLD_PREFIX.len()..]);
    Some(format!(
        "{first} is the old spelling of {new}: this arm reads {new}, so under {first} it would compare nothing and pass. \
         Unset {first} and set {new} (old developer variables set: {}; AGENTS.md's precedence paragraph)",
        old.join(" ")
    ))
}

/// Fails the running test when an old developer variable is set.
pub fn refuse_old_names() {
    let names = std::env::vars_os().map(|(k, _)| k.to_string_lossy().into_owned());
    if let Some(why) = refusal(names) {
        panic!("{why}");
    }
}

/// `std::env::var`, after [`refuse_old_names`].
pub fn var(name: impl AsRef<OsStr>) -> Result<String, VarError> {
    refuse_old_names();
    std::env::var(name)
}

/// `std::env::var_os`, after [`refuse_old_names`].
pub fn var_os(name: impl AsRef<OsStr>) -> Option<OsString> {
    refuse_old_names();
    std::env::var_os(name)
}
