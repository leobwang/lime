//! **A frozen comparand's COMMITTED history — what every bless holds its lines against**
//! (stage 6 W-42 track C; README gaps 4139, 4151 and 4280).
//!
//! # The finding
//!
//! Every bless of a frozen fork comparand held each line it was about to write against the
//! line the file already held — and it read "the file already held" off the WORKING COPY. So
//! the working copy decided what was a re-bless (held to the owner's D64) and what was a fresh
//! freeze (held to nothing): delete the file, or one line of it, and every recomputed line is
//! "added". W-41's land step did exactly that to the TUI file — it froze it FRESH, the fixture
//! absent, over a line a track had committed with other answers (README gaps 4123 and 4139) —
//! and the working copy can be bent the same way by anything that writes it: a hand edit, an
//! earlier bless in the same session, a clean checkout of another branch.
//!
//! # The rule this module is the one definition of
//!
//! A bless takes the lines it HOLDS from the file's committed history: the file at the base
//! `kernel/ratchet.py` names and at every commit after it on HEAD's FIRST-PARENT line, oldest
//! first — the walk `ratchet.py` holds the exemption files to (README gap 4132), read from that
//! file so the base has one home. For every key a bless writes, the line it is held against is
//! the LATEST committed version of that key — HEAD's where HEAD holds it, else the last commit
//! since the base that did — so deleting a file or a line, in the working copy or in a commit,
//! cannot turn a re-bless into a fresh freeze. A key no committed version holds is new. And a
//! bless that refuses "a frozen line it no longer writes" asks that of the keys at HEAD
//! ([`Held::head`]): a line a COMMIT removed was reviewed in that commit's diff.
//!
//! **And a merge in progress** ([`merge_heads`], README gap 4286): a key no first-parent version
//! holds is held against the line the commit being merged holds — the window W-41's land froze the
//! TUI file fresh in (gaps 4123 and 4139), which the first-parent walk alone does not reach.
//!
//! **UNCHECKED fails, as `ratchet.py`'s does**: a history git cannot read — a `git archive`
//! copy, a shallow clone without the base, a base that is not an ancestor of HEAD — or a
//! committed version that does not parse is an `Err`, and the bless FAILS and writes nothing
//! rather than holding its lines against nothing.
//!
//! # What it cannot see, declared
//!
//! A commit before the base (the owner moves it, in `ratchet.py`, by D88's rule). A track's own
//! commit off the first-parent line once its merge is committed (it is judged by the merge that
//! brings it — `ratchet.py`'s blind spot, the same walk) — and, during a merge, a key BOTH sides
//! hold differently is held against the first-parent side only. And what a bless does with its
//! INPUT: a bless whose worlds come
//! from the file (the classes' re-bless, the grid's `p63` mode, the classes' re-draw) still
//! reads them from the working copy, where a pending re-draw lives; what this module decides is
//! what each written line is HELD AGAINST, never where its world came from.

#![allow(dead_code)]

use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};
use std::process::Command;

use serde_json::Value;

/// `kernel/ratchet.py`, whose `BASE` is the base of the walk.
pub fn ratchet_path() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../kernel/ratchet.py")
}

/// **The base of the walk**: `kernel/ratchet.py`'s `BASE = "<sha>"`, read from that file (one
/// home: the owner moves it there and every walk moves with it). A file that does not name a
/// forty-digit hex sha is an `Err`.
pub fn base() -> Result<String, String> {
    let path = ratchet_path();
    let text = std::fs::read_to_string(&path).map_err(|e| format!("UNCHECKED: {}: {e}", path.display()))?;
    base_of(&text).ok_or_else(|| format!("UNCHECKED: {} names no `BASE = \"<sha>\"`", path.display()))
}

/// [`base`] over a file's text: the first column-zero `BASE = "<40 hex digits>"`.
pub fn base_of(text: &str) -> Option<String> {
    text.lines().find_map(|l| {
        let sha = l.strip_prefix("BASE = \"")?.strip_suffix('"')?;
        (sha.len() == 40 && sha.bytes().all(|c| c.is_ascii_hexdigit())).then(|| sha.to_string())
    })
}

/// `git -C dir args…`'s stdout, `None` when git cannot say (it is not there, or it exits non-zero).
fn git(dir: &Path, args: &[&str]) -> Option<String> {
    let out = Command::new("git").arg("-C").arg(dir).args(args).output().ok()?;
    out.status.success().then(|| String::from_utf8_lossy(&out.stdout).into_owned())
}

/// **The file's text at `rev`**: `Some("")` when that commit does not hold it, `None` when git
/// cannot say — `ratchet.py`'s `show`, the same two git calls.
pub fn show(path: &Path, rev: &str) -> Option<String> {
    let dir = path.parent()?;
    let name = path.file_name()?.to_str()?;
    let listed = git(dir, &["ls-tree", rev, "--", name])?;
    if listed.trim().is_empty() {
        return Some(String::new());
    }
    git(dir, &["show", &format!("{rev}:./{name}")])
}

/// One committed line: the commit whose file last held its key, its bytes, and its value.
#[derive(Clone, Debug, PartialEq)]
pub struct Committed {
    pub sha: String,
    pub raw: String,
    pub line: Value,
}

/// **What a bless holds**, read off the file's committed history.
#[derive(Clone, Debug, Default, PartialEq)]
pub struct Held {
    /// Every key any committed version since the base holds, with its LATEST committed line.
    pub ever: BTreeMap<String, Committed>,
    /// The keys the file at HEAD holds, in its order.
    pub head: Vec<String>,
    /// The distinct versions read, oldest first: the commit and its number of lines.
    pub versions: Vec<(String, usize)>,
}

impl Held {
    /// The committed line `key` is held against, if any commit since the base held it.
    pub fn get(&self, key: &str) -> Option<&Value> {
        self.ever.get(key).map(|c| &c.line)
    }

    /// The keys a committed version held that HEAD does not — what deleting a line would have
    /// turned into a fresh freeze before this module.
    pub fn only_in_history(&self) -> Vec<&str> {
        self.ever.keys().filter(|k| !self.head.contains(k)).map(String::as_str).collect()
    }

    /// One census line for a bless's report.
    pub fn census(&self, what: &str) -> String {
        format!(
            "{what}: held against {} committed line(s) from {} version(s) since the base ({} at HEAD, {} only in history: {:?})",
            self.ever.len(),
            self.versions.len(),
            self.head.len(),
            self.ever.len() - self.head.iter().filter(|k| self.ever.contains_key(*k)).count(),
            self.only_in_history()
        )
    }
}

/// **The lines a bless of `path` holds**, keyed by `key` — over the base [`base`] reads.
pub fn held(path: &Path, key: impl Fn(&Value) -> Option<String>) -> Result<Held, String> {
    held_since(path, &base()?, key)
}

/// [`held`] over an explicit base (a test's own repository).
pub fn held_since(path: &Path, base: &str, key: impl Fn(&Value) -> Option<String>) -> Result<Held, String> {
    let dir = path.parent().ok_or_else(|| format!("UNCHECKED: {} has no directory", path.display()))?;
    let unchecked = |why: &str| format!("UNCHECKED: {}: {why} — a bless that cannot read the committed history writes nothing", path.display());
    git(dir, &["merge-base", "--is-ancestor", base, "HEAD"])
        .ok_or_else(|| unchecked(&format!("the base {base} is not an ancestor of HEAD, or git cannot say (a `git archive` copy, a shallow clone)")))?;
    let revs = git(dir, &["rev-list", "--first-parent", "--reverse", &format!("{base}..HEAD")]).ok_or_else(|| unchecked("git rev-list failed"))?;
    let mut out = Held::default();
    let mut last: Option<String> = None;
    for rev in std::iter::once(base.to_string()).chain(revs.split_whitespace().map(str::to_string)) {
        let text = show(path, &rev).ok_or_else(|| unchecked(&format!("git cannot show it at {rev}")))?;
        let mut keys = Vec::new();
        for raw in text.lines().filter(|l| !l.trim().is_empty()) {
            let line: Value = serde_json::from_str(raw).map_err(|e| unchecked(&format!("its line at {rev} is not JSON ({e}): {raw:.80}")))?;
            let k = key(&line).ok_or_else(|| unchecked(&format!("a line at {rev} has no key: {raw:.80}")))?;
            if keys.contains(&k) {
                return Err(unchecked(&format!("two lines at {rev} carry the key {k}")));
            }
            keys.push(k.clone());
            out.ever.insert(k, Committed { sha: rev.clone(), raw: raw.to_string(), line });
        }
        if last.as_deref() != Some(text.as_str()) {
            out.versions.push((rev.clone(), keys.len()));
        }
        out.head = keys;
        last = Some(text);
    }
    // **A merge in progress** (README gap 4286): the branch being merged has committed lines the
    // first-parent walk does not reach, and resolving the merge is when a land re-blesses — W-41's
    // land froze the TUI file FRESH there, over a line track H had committed (gaps 4123, 4139). So
    // a key no first-parent version holds is held against the incoming commit's line.
    for rev in merge_heads(dir) {
        let text = show(path, &rev).ok_or_else(|| unchecked(&format!("git cannot show it at the merge head {rev}")))?;
        let mut keys = Vec::new();
        for raw in text.lines().filter(|l| !l.trim().is_empty()) {
            let line: Value = serde_json::from_str(raw).map_err(|e| unchecked(&format!("its line at {rev} is not JSON ({e}): {raw:.80}")))?;
            let k = key(&line).ok_or_else(|| unchecked(&format!("a line at {rev} has no key: {raw:.80}")))?;
            if keys.contains(&k) {
                return Err(unchecked(&format!("two lines at {rev} carry the key {k}")));
            }
            keys.push(k.clone());
            out.ever.entry(k).or_insert(Committed { sha: rev.clone(), raw: raw.to_string(), line });
        }
        out.versions.push((rev, keys.len()));
    }
    Ok(out)
}

/// **What a bless of a WHOLE-FILE comparand holds** (W-45 track C, README gap 4680): a committed
/// snapshot — `emit_planner.rs`' renderings of the fork's fixture days, which a surviving test reads
/// as the fork's frozen answer — is held as [`held`] holds a line: its latest committed text since
/// the base on HEAD's first-parent line (HEAD's where HEAD holds it), else the text the commit being
/// merged holds; `Ok(None)` when no committed version holds the file. The working copy is never
/// what is held, and a history git cannot read is UNCHECKED, an `Err`.
pub fn held_text(path: &Path) -> Result<Option<(String, String)>, String> {
    held_text_since(path, &base()?)
}

/// [`held_text`] over an explicit base (a test's own repository).
pub fn held_text_since(path: &Path, base: &str) -> Result<Option<(String, String)>, String> {
    let dir = path.parent().ok_or_else(|| format!("UNCHECKED: {} has no directory", path.display()))?;
    let unchecked = |why: &str| format!("UNCHECKED: {}: {why} — a bless that cannot read the committed history writes nothing", path.display());
    git(dir, &["merge-base", "--is-ancestor", base, "HEAD"])
        .ok_or_else(|| unchecked(&format!("the base {base} is not an ancestor of HEAD, or git cannot say (a `git archive` copy, a shallow clone)")))?;
    let revs = git(dir, &["rev-list", "--first-parent", "--reverse", &format!("{base}..HEAD")]).ok_or_else(|| unchecked("git rev-list failed"))?;
    let mut latest: Option<(String, String)> = None;
    for rev in std::iter::once(base.to_string()).chain(revs.split_whitespace().map(str::to_string)) {
        let text = show(path, &rev).ok_or_else(|| unchecked(&format!("git cannot show it at {rev}")))?;
        if !text.is_empty() {
            latest = Some((rev, text));
        }
    }
    if latest.is_none() {
        for rev in merge_heads(dir) {
            let text = show(path, &rev).ok_or_else(|| unchecked(&format!("git cannot show it at the merge head {rev}")))?;
            if !text.is_empty() {
                latest = Some((rev, text));
            }
        }
    }
    Ok(latest)
}

/// **Every committed version of the file since the base, oldest first, then the working copy**
/// (the W-42 repair, README gap 4341): `(sha, {key: line})` per first-parent commit — the walk
/// [`held_since`] reads — and `("WORKTREE", …)` last, read off the disk. What a PLAIN run holds the
/// history to, with no fork planner: R3 deleted eight of the eleven blesses that ask the gate, so
/// after it a frozen line can change only by hand, and this is what still sees the change.
pub fn versions(path: &Path, key: impl Fn(&Value) -> Option<String>) -> Result<Vec<(String, BTreeMap<String, Value>)>, String> {
    versions_since(path, &base()?, key)
}

/// [`versions`] over an explicit base (a test's own repository).
pub fn versions_since(path: &Path, base: &str, key: impl Fn(&Value) -> Option<String>) -> Result<Vec<(String, BTreeMap<String, Value>)>, String> {
    let dir = path.parent().ok_or_else(|| format!("UNCHECKED: {} has no directory", path.display()))?;
    let unchecked = |why: &str| format!("UNCHECKED: {}: {why}", path.display());
    git(dir, &["merge-base", "--is-ancestor", base, "HEAD"])
        .ok_or_else(|| unchecked(&format!("the base {base} is not an ancestor of HEAD, or git cannot say")))?;
    let revs = git(dir, &["rev-list", "--first-parent", "--reverse", &format!("{base}..HEAD")]).ok_or_else(|| unchecked("git rev-list failed"))?;
    let parse = |rev: &str, text: &str| -> Result<BTreeMap<String, Value>, String> {
        let mut out = BTreeMap::new();
        for raw in text.lines().filter(|l| !l.trim().is_empty()) {
            let line: Value = serde_json::from_str(raw).map_err(|e| unchecked(&format!("its line at {rev} is not JSON ({e}): {raw:.80}")))?;
            let k = key(&line).ok_or_else(|| unchecked(&format!("a line at {rev} has no key: {raw:.80}")))?;
            if out.insert(k.clone(), line).is_some() {
                return Err(unchecked(&format!("two lines at {rev} carry the key {k}")));
            }
        }
        Ok(out)
    };
    let mut out = Vec::new();
    for rev in std::iter::once(base.to_string()).chain(revs.split_whitespace().map(str::to_string)) {
        let text = show(path, &rev).ok_or_else(|| unchecked(&format!("git cannot show it at {rev}")))?;
        out.push((rev.clone(), parse(&rev, &text)?));
    }
    let text = std::fs::read_to_string(path).unwrap_or_default();
    out.push(("WORKTREE".to_string(), parse("WORKTREE", &text)?));
    Ok(out)
}

/// **The answer a frozen line holds for the SHIPPED fork**, whatever its file: a comparand line's
/// `shipped` day where the comparand departs, its `day`'s day otherwise (`forkclass::shipped_of`,
/// the gate's own reading); a grid line's `fork`; a fixture day's `day` and `hash`, which ARE the
/// shipped fork's answer (those files carry no comparand).
pub fn shipped_answer(line: &Value) -> Value {
    if line.get("shipped").is_some() {
        if line["shipped"].is_null() { line["day"]["day"].clone() } else { line["shipped"]["day"].clone() }
    } else if line.get("fork").is_some() {
        line["fork"].clone()
    } else {
        serde_json::json!([line["day"], line["hash"]])
    }
}

/// **A line's answers**, by a property of the key and never a list of files: the comparand's and
/// the fork's days (`day`, `shipped`, `whatif`, `hash`, `fork`), every key named by a parity
/// number (`p45` .. `p69`, `p63`: a departure's own answer), and every object the line carries a
/// parity flag in (`d57`, `d60`: `forkclass::flag_homes`' rule). Everything else is the line's
/// WORLD and PROVENANCE.
pub fn is_answer(line: &Value, k: &str) -> bool {
    let numbered = |s: &str| s.strip_prefix('p').is_some_and(|d| !d.is_empty() && d.bytes().all(|c| c.is_ascii_digit()));
    matches!(k, "day" | "shipped" | "whatif" | "hash" | "fork")
        || numbered(k)
        || line[k].as_object().is_some_and(|o| o.iter().any(|(f, v)| numbered(f) && v.is_boolean()))
}

/// **The D64(b) reason a line carries**: its `d64b` when that is a string, else `d64b.why`; `""` for none.
pub fn d64b_why(line: &Value) -> &str {
    line["d64b"]["why"].as_str().or_else(|| line["d64b"].as_str()).unwrap_or_default()
}

/// **A re-draw's reason KEEPS every earlier one** (the W-48 repair, README gap 5216): the new reason first —
/// dated and naming D64(b), as [`redrawn`] reads it — then `— earlier:` and the reason the committed line
/// carried, which carries its own earlier ones. Until then every bless that re-drew a line wrote the new
/// reason OVER the old, so a line re-drawn twice named only the last number that moved it: W-48's land
/// replaced 27 week-grid reasons (P101, P103, P106-P107, P115-P116, R3) with one P119 sentence, two of them
/// on lines whose FORK answers P115/P116 had moved — and the line no longer said which number did.
pub fn redraw_why(why: &str, old: &Value) -> String {
    let was = d64b_why(old);
    if was.is_empty() || why.contains(was) {
        why.to_string()
    } else {
        format!("{why} — earlier: {was}")
    }
}

/// **Every reason a line was ever re-drawn for is still on it** (the W-48 repair, README gap 5216): over
/// every committed version of `path` since the base on HEAD's first-parent line, and then the working copy,
/// each key's distinct D64(b) reasons in order; a reason an earlier version carried that the line's LATEST
/// version (the working copy's, else the last committed) does not contain is named, `<key>: <reason>`. A
/// history git cannot read is UNCHECKED, an `Err`.
pub fn dropped_reasons(path: &Path, key: &dyn Fn(&Value) -> Option<String>) -> Result<Vec<String>, String> {
    dropped_reasons_since(path, &base()?, key)
}

/// [`dropped_reasons`] over an explicit base (a test's own repository).
pub fn dropped_reasons_since(path: &Path, base: &str, key: &dyn Fn(&Value) -> Option<String>) -> Result<Vec<String>, String> {
    let dir = path.parent().ok_or_else(|| format!("UNCHECKED: {} has no directory", path.display()))?;
    let unchecked = |why: &str| format!("UNCHECKED: {}: {why}", path.display());
    let revs = git(dir, &["rev-list", "--first-parent", "--reverse", &format!("{base}..HEAD")]).ok_or_else(|| unchecked("git rev-list failed"))?;
    let mut texts = Vec::new();
    for rev in std::iter::once(base.to_string()).chain(revs.split_whitespace().map(str::to_string)) {
        texts.push(show(path, &rev).ok_or_else(|| unchecked(&format!("git cannot show it at {rev}")))?);
    }
    if let Ok(work) = std::fs::read_to_string(path) {
        texts.push(work);
    }
    let mut seen: BTreeMap<String, Vec<String>> = BTreeMap::new();
    for text in &texts {
        for raw in text.lines().filter(|l| !l.trim().is_empty()) {
            let line: Value = serde_json::from_str(raw).map_err(|e| unchecked(&format!("a line is not JSON ({e})")))?;
            let Some(k) = key(&line) else { continue };
            let why = d64b_why(&line);
            if why.is_empty() {
                continue;
            }
            let reasons = seen.entry(k).or_default();
            if reasons.last().map(String::as_str) != Some(why) {
                reasons.push(why.to_string());
            }
        }
    }
    let mut out = Vec::new();
    for (k, reasons) in &seen {
        let last = reasons.last().map(String::as_str).unwrap_or_default();
        for r in &reasons[..reasons.len().saturating_sub(1)] {
            if !last.contains(r.as_str()) {
                out.push(format!("{k}: {r:.120}"));
            }
        }
    }
    Ok(out)
}

/// **A D64(b) re-draw between two versions of one line**: the newer carries a `d64b` the older
/// does not, its reason dated and naming D64(b) (`forkclass::is_d64b_reason`'s rule).
pub fn redrawn(old: &Value, new: &Value) -> bool {
    let why = new["d64b"]["why"].as_str().or_else(|| new["d64b"].as_str()).unwrap_or_default();
    new["d64b"] != old["d64b"] && why.starts_with("20") && why.contains("D64(b)")
}

// ---------------------------------------------------------------------------------------------
// **D64(d) — a frozen world that IS a shipped template** (the owner's D127; W-49 track E, README
// gaps 5131, 4976 and 4749). A frozen comparand line whose world was built over the shipped example
// template (`tm/templates/example/`, which IS `plan-basic`, §17.1) may be recomputed when that
// template changes under a registered behaviour change. D64(b) does not reach it — the committed
// world is one a user can still type, and the binary can still hold it — so the clause is its own,
// and it is held to three facts, every one checked here and never declared by a caller:
//
// 1. **the reason**: dated (`20…`), naming `D64(d)`, and naming the registered parity number the
//    template's change is (`P<n>`, a row of `kernel/parity.txt` whose own line names `tm init
//    --example` or `tm/templates/example` — [`TemplateParity`], [`is_d64d_reason`]; since the W-49
//    repair, README gap 5410, any registered number was enough); and in the history check, a number
//    NOT yet registered at the commit the line's older version stands at ([`d64d_reason_new_since`]);
// 2. **the template moved**: the shipped template's files differ between the committed version the
//    line was frozen over and the version it is recomputed over, LINE FOR LINE (the same files, the
//    same number of lines) — [`template_pairs`], whose pairs are the template's own moved lines;
// 3. **the world moved by those lines and nothing else**: every string the two worlds hold is the
//    same but for whole lines, and every line that moved is one of the template's pairs — an item
//    line's state box aside, which a verb the world ran may have set — [`moved_only_by_template`].
//    So a world that is NOT the shipped template's (a line it holds that the template does not, a
//    hand-typed two-estimate line, a world whose template did not move) is refused by name.
//
// The steps, the provenance and every key but the world and the answers stay byte for byte; the
// answers (the fork's days) move with the world, as a D64(b) re-draw's do: the fork is asked again.
// ---------------------------------------------------------------------------------------------

/// The shipped example template, `tm/templates/example/`.
pub fn template_dir() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("templates/example")
}

/// **The shipped template's files at `rev`** — `"WORKTREE"` for the working copy — by file name.
/// What git cannot read is an `Err` (UNCHECKED), never an empty template.
pub fn template_at(rev: &str) -> Result<BTreeMap<String, String>, String> {
    let dir = template_dir();
    let unchecked = |why: String| format!("UNCHECKED: the shipped template at {rev}: {why}");
    let mut out = BTreeMap::new();
    if rev == "WORKTREE" {
        for e in std::fs::read_dir(&dir).map_err(|e| unchecked(e.to_string()))? {
            let e = e.map_err(|e| unchecked(e.to_string()))?;
            let name = e.file_name().into_string().map_err(|_| unchecked("a file name that is not UTF-8".into()))?;
            out.insert(name, std::fs::read_to_string(e.path()).map_err(|e| unchecked(e.to_string()))?);
        }
    } else {
        let names = git(&dir, &["ls-tree", "--name-only", rev, "--", "./"]).ok_or_else(|| unchecked("git ls-tree failed".into()))?;
        for name in names.lines().filter(|n| !n.trim().is_empty()) {
            let text = show(&dir.join(name), rev).ok_or_else(|| unchecked(format!("git cannot show {name}")))?;
            out.insert(name.to_string(), text);
        }
    }
    if out.is_empty() {
        return Err(unchecked("no file".into()));
    }
    Ok(out)
}

/// **The shipped template's own moved lines, `old` → `new`**: every `(old line, new line)` pair of a
/// file both versions hold, in file order. The change must be LINE FOR LINE — the same files and, in
/// each, the same number of lines — or it is no template change clause (d) can follow: an `Err`.
pub fn template_pairs(old: &BTreeMap<String, String>, new: &BTreeMap<String, String>) -> Result<Vec<(String, String)>, String> {
    if old.keys().ne(new.keys()) {
        return Err("the shipped template gained or lost a file — not a line-for-line change".into());
    }
    let mut out = Vec::new();
    for (name, a) in old {
        let (la, lb): (Vec<&str>, Vec<&str>) = (a.lines().collect(), new[name].lines().collect());
        if la.len() != lb.len() {
            return Err(format!("the shipped template's {name} gained or lost a line — not a line-for-line change"));
        }
        out.extend(la.iter().zip(&lb).filter(|(x, y)| x != y).map(|(x, y)| (x.to_string(), y.to_string())));
    }
    Ok(out)
}

/// **A D64(d) reason, as the owner's D127 demands it**: dated (`20…`), naming `D64(d)`, and naming
/// a parity number whose `kernel/parity.txt` row is THE TEMPLATE'S CHANGE ([`TemplateParity`]: the
/// row names `tm init --example` or `tm/templates/example`) — "under a registered behaviour change"
/// read as the template change's own number, never any registered one (the W-49 repair, README gap
/// 5410: a reason naming `P1`, the capacity mixture's number, licensed a re-bless of all 68 frozen
/// template lines over an unregistered template edit). `Ok(n)`, the first such number named; an
/// `Err` says which part is missing.
pub fn is_d64d_reason(why: &str, template: &TemplateParity) -> Result<u32, String> {
    d64d_numbers(why, template)?
        .first()
        .copied()
        .ok_or_else(|| format!("`{why:.80}` names no parity number (P<n>) whose kernel/parity.txt row is the shipped template's change (`tm init --example`, `tm/templates/example`)"))
}

/// Every parity number a D64(d) reason names whose register row is the template's change, in the
/// order named; `Err` when the reason is not dated or names no `D64(d)`.
pub fn d64d_numbers(why: &str, template: &TemplateParity) -> Result<Vec<u32>, String> {
    if !why.starts_with("20") || !why.contains("D64(d)") {
        return Err(format!("`{why:.80}` is not a D64(d) reason — dated (20…), naming D64(d)"));
    }
    Ok(why
        .split(|c: char| !c.is_ascii_alphanumeric())
        .filter_map(|w| w.strip_prefix('P'))
        .filter_map(|d| d.parse().ok())
        .filter(|n| template.0.contains(n))
        .collect())
}

/// **The parity numbers that ARE a change of the shipped example template** — the rows of a
/// `kernel/parity.txt` text (not `hole`s) whose own line names `tm init --example` or
/// `tm/templates/example`. Built only from a register's text, so no caller can hand D64(d) a plain
/// set of every registered number (W-49 repair, gap 5410).
#[derive(Clone, Debug, Default, PartialEq)]
pub struct TemplateParity(BTreeSet<u32>);

impl TemplateParity {
    /// The template's numbers in a register's text.
    pub fn of_register(text: &str) -> TemplateParity {
        TemplateParity(
            text.lines()
                .filter(|l| l.contains("tm init --example") || l.contains("tm/templates/example"))
                .filter_map(|l| l.split_whitespace().next())
                .filter_map(|w| w.strip_prefix('P'))
                .filter_map(|d| d.parse().ok())
                .collect(),
        )
    }

    /// The template's numbers in the working copy's `kernel/parity.txt`.
    pub fn read() -> Result<TemplateParity, String> {
        let text = std::fs::read_to_string(parity_path()).map_err(|e| format!("UNCHECKED: {}: {e}", parity_path().display()))?;
        Ok(TemplateParity::of_register(&text))
    }

    /// Does the register hold `n` as a template change?
    pub fn contains(&self, n: u32) -> bool {
        self.0.contains(&n)
    }
}

/// `kernel/parity.txt`.
fn parity_path() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../kernel/parity.txt")
}

/// The parity numbers a register's text registers (every row that is not a `hole`).
fn registered_in(text: &str) -> BTreeSet<u32> {
    text.lines()
        .filter_map(|l| l.split_whitespace().next())
        .filter_map(|w| w.strip_prefix('P'))
        .filter_map(|d| d.parse().ok())
        .collect()
}

/// The parity numbers `kernel/parity.txt` registers (every row that is not a `hole`).
pub fn registered_parity() -> Result<BTreeSet<u32>, String> {
    let text = std::fs::read_to_string(parity_path()).map_err(|e| format!("UNCHECKED: {}: {e}", parity_path().display()))?;
    Ok(registered_in(&text))
}

/// The parity numbers `kernel/parity.txt` registers at commit `rev` (empty when that commit holds no
/// register); `Err` when git cannot say.
pub fn registered_parity_at(rev: &str) -> Result<BTreeSet<u32>, String> {
    show(&parity_path(), rev).map(|t| registered_in(&t)).ok_or_else(|| format!("UNCHECKED: kernel/parity.txt at {rev}"))
}

/// **A D64(d) reason is NEW at the re-draw** (the history half, W-49 repair, gap 5410): some number
/// it names that is the template's change ([`d64d_numbers`]) was NOT yet registered at `was`, the
/// commit the line's older version stands at — so a template change registered once licenses the
/// re-draw it came with, and a later template edit cannot ride on it. `Ok(n)`, that number.
pub fn d64d_reason_new_since(why: &str, template: &TemplateParity, was: &str) -> Result<u32, String> {
    let before = registered_parity_at(was)?;
    let named = d64d_numbers(why, template)?;
    named
        .iter()
        .copied()
        .find(|n| !before.contains(n))
        .ok_or_else(|| format!("`{why:.80}` names no template parity number that was new since {} (named {named:?}, every one registered there already)", &was[..was.len().min(9)]))
}

/// An item line's state box and the rest of it: `- [x] rest` → `('x', "rest")`.
fn boxed(line: &str) -> Option<(char, &str)> {
    let rest = line.strip_prefix("- [")?;
    let mut cs = rest.chars();
    let b = cs.next()?;
    let tail = cs.as_str().strip_prefix("] ")?;
    Some((b, tail))
}

/// One moved line `a` → `b` is the template's pair `ta` → `tb`: byte for byte, or both item lines
/// whose state boxes agree with each other and whose rest is the template pair's rest.
fn is_template_move(a: &str, b: &str, pairs: &[(String, String)]) -> bool {
    pairs.iter().any(|(ta, tb)| {
        (a == ta && b == tb)
            || match (boxed(a), boxed(b), boxed(ta), boxed(tb)) {
                (Some((x, ra)), Some((y, rb)), Some((_, rta)), Some((_, rtb))) => x == y && ra == rta && rb == rtb,
                _ => false,
            }
    })
}

/// **A world moved by the shipped template's own lines and nothing else** — [`template_redraw_allows`]'
/// third fact. `Ok(n)`, the number of lines that moved (at least one); an `Err` names the first
/// place the two worlds differ otherwise: a key, a value that is not a string, a string whose lines
/// do not pair, or a moved line that is none of the template's.
pub fn moved_only_by_template(old: &Value, new: &Value, pairs: &[(String, String)]) -> Result<usize, String> {
    fn walk(at: &str, a: &Value, b: &Value, pairs: &[(String, String)], n: &mut usize) -> Result<(), String> {
        match (a, b) {
            (Value::Object(x), Value::Object(y)) => {
                if x.keys().ne(y.keys()) {
                    return Err(format!("{at}: its keys moved"));
                }
                x.iter().try_for_each(|(k, v)| walk(&format!("{at}.{k}"), v, &y[k], pairs, n))
            }
            (Value::Array(x), Value::Array(y)) => {
                if x.len() != y.len() {
                    return Err(format!("{at}: its length moved"));
                }
                x.iter().zip(y).enumerate().try_for_each(|(i, (v, w))| walk(&format!("{at}[{i}]"), v, w, pairs, n))
            }
            (Value::String(x), Value::String(y)) if x != y => {
                let (lx, ly): (Vec<&str>, Vec<&str>) = (x.split_inclusive('\n').collect(), y.split_inclusive('\n').collect());
                if lx.len() != ly.len() {
                    return Err(format!("{at}: it gained or lost a line"));
                }
                for (i, (p, q)) in lx.iter().zip(&ly).enumerate() {
                    if p == q {
                        continue;
                    }
                    let (pe, qe) = (p.strip_suffix('\n'), q.strip_suffix('\n'));
                    if pe.is_some() != qe.is_some() || !is_template_move(pe.unwrap_or(p), qe.unwrap_or(q), pairs) {
                        return Err(format!("{at}, line {}: `{}` → `{}` is not one of the shipped template's own lines", i + 1, p.trim_end(), q.trim_end()));
                    }
                    *n += 1;
                }
                Ok(())
            }
            _ if a == b => Ok(()),
            _ => Err(format!("{at}: a value that is not a string's lines moved")),
        }
    }
    let mut n = 0usize;
    walk("world", old, new, pairs, &mut n)?;
    if n == 0 {
        return Err("no line of the world moved, so there is nothing for D64(d) to license".into());
    }
    Ok(n)
}

/// The D64(d) reason a line carries: its `d64d.why`, `""` for none.
pub fn d64d_why(line: &Value) -> &str {
    line["d64d"]["why"].as_str().unwrap_or_default()
}

/// **A template re-draw's reason keeps an earlier one**, as [`redraw_why`] does for D64(b).
pub fn template_redraw_why(why: &str, old: &Value) -> String {
    let was = d64d_why(old);
    if was.is_empty() || why.contains(was) {
        why.to_string()
    } else {
        format!("{why} — earlier: {was}")
    }
}

/// **The owner's D64(d), as a gate** (D127): may the committed line `old` be recomputed as `new`,
/// for the reason `why`, over the shipped template's moved lines `pairs`? The three facts this
/// section's head names; and every key of the line but its world, its answers ([`is_answer`]) and
/// the two re-draw records (`d64b`, `d64d`) byte for byte — the steps the world was built by
/// included, so a world built by other verbs is no template re-draw. `Ok(n)`, the lines that moved.
pub fn template_redraw_allows(old: &Value, new: &Value, why: &str, template: &TemplateParity, pairs: &[(String, String)]) -> Result<usize, String> {
    let who = old["name"].as_str().or_else(|| old["class"].as_str()).unwrap_or("<unnamed>");
    is_d64d_reason(why, template).map_err(|e| format!("{who}: {e}"))?;
    if pairs.is_empty() {
        return Err(format!("{who}: the shipped template did not move, so D64(d) does not reach this line"));
    }
    let keys: BTreeSet<&String> = old.as_object().into_iter().flatten().chain(new.as_object().into_iter().flatten()).map(|(k, _)| k).collect();
    for k in keys {
        let k = k.as_str();
        if k == "world" || k == "d64b" || k == "d64d" || is_answer(old, k) || is_answer(new, k) {
            continue;
        }
        if old[k] != new[k] {
            return Err(format!("{who}: `{k}` moved, which is its provenance — D64(d) moves the world alone"));
        }
    }
    moved_only_by_template(&old["world"], &new["world"], pairs).map_err(|e| format!("{who}: {e}"))
}

/// **A D64(d) re-draw between two committed versions of one line** — the plain history check's
/// reading (`fork_rebless_history.rs`): the newer version carries a `d64d` the older does not, and
/// [`template_redraw_allows`] holds over the shipped template's move between the two commits
/// (`"WORKTREE"` for the working copy), and the reason's template number is new since `was`
/// ([`d64d_reason_new_since`]). A history git cannot read is no re-draw.
pub fn template_redrawn(old: &Value, new: &Value, was: &str, now: &str) -> bool {
    if new["d64d"] == old["d64d"] {
        return false;
    }
    let (Ok(a), Ok(b), Ok(reg)) = (template_at(was), template_at(now), TemplateParity::read()) else { return false };
    let Ok(pairs) = template_pairs(&a, &b) else { return false };
    template_redraw_allows(old, new, d64d_why(new), &reg, &pairs).is_ok() && d64d_reason_new_since(d64d_why(new), &reg, was).is_ok()
}

/// **The template's move a bless recomputes over**: the shipped template committed at HEAD → the
/// working copy's. A bless that re-draws under D64(d) runs before the commit that moves the template.
pub fn template_pairs_since_head() -> Result<Vec<(String, String)>, String> {
    template_pairs(&template_at("HEAD")?, &template_at("WORKTREE")?)
}

/// **A bless's D64(d) reason, read strictly**: `TM_TEMPLATE_REDRAW`, absent → `None`; present, it
/// must be a D64(d) reason ([`is_d64d_reason`]) or the bless FAILS rather than skipping it.
pub fn template_redraw_reason() -> Option<String> {
    let why = std::env::var("TM_TEMPLATE_REDRAW").ok()?;
    let reg = TemplateParity::read().unwrap_or_else(|e| panic!("{e}"));
    if let Err(e) = is_d64d_reason(&why, &reg) {
        panic!("TM_TEMPLATE_REDRAW: {e}");
    }
    Some(why)
}

/// **One bless's D64(d) decision for one line, the same in every bless**: with `why` set and the
/// committed line's world moved, the recomputed line `new` is admitted when [`template_redraw_allows`]
/// holds over [`template_pairs_since_head`], and then carries `d64d` (the reason, kept with any
/// earlier one, and what moved); `Err` names why it is refused. A line that already carries a
/// `d64d` keeps it while its world stands (call [`keep_template_record`]).
pub fn template_redraw(old: &Value, new: &mut Value, why: &str) -> Result<usize, String> {
    let reg = TemplateParity::read()?;
    let pairs = template_pairs_since_head()?;
    let n = template_redraw_allows(old, new, why, &reg, &pairs)?;
    new["d64d"] = serde_json::json!({
        "why": template_redraw_why(why, old),
        "moved": format!("{n} line(s), each one of the shipped example template's own moved lines (tm/templates/example), and nothing else"),
    });
    if !old["d64b"].is_null() && new["d64b"].is_null() {
        new["d64b"] = old["d64b"].clone();
    }
    Ok(n)
}

/// A line whose world stands keeps the `d64d` record the committed line carries.
pub fn keep_template_record(old: &Value, new: &mut Value) {
    if !old["d64d"].is_null() {
        new["d64d"] = old["d64d"].clone();
    }
}

/// **The commits a merge in progress is merging** — `MERGE_HEAD`'s lines (an octopus names
/// several), empty when no merge is in progress.
pub fn merge_heads(dir: &Path) -> Vec<String> {
    let Some(file) = git(dir, &["rev-parse", "--git-path", "MERGE_HEAD"]) else { return Vec::new() };
    let file = dir.join(file.trim());
    std::fs::read_to_string(file).map(|t| t.split_whitespace().map(str::to_string).collect()).unwrap_or_default()
}

/// **A frozen class line's key** (`fork-4748911-planner-classes.jsonl`, whose lines carry no name):
/// its class, its secondary floor and its derivation — together they name one line of the file (a
/// re-draw keeps all three; the world is the line's VALUE). One definition, for the classes'
/// re-bless, their re-draw and the reader's own test.
pub fn class_key(l: &Value) -> Option<String> {
    Some(format!("{} | {} | {}", l["class"].as_str()?, l["secondary"], l["derived"]))
}

/// **A line's key, read as a bless reads it**: the string at `field`, or a number's digits.
pub fn key_of(field: &'static str) -> impl Fn(&Value) -> Option<String> {
    move |v: &Value| match &v[field] {
        Value::String(s) => Some(s.clone()),
        Value::Number(n) => Some(n.to_string()),
        _ => None,
    }
}

// ---------------------------------------------------------------------------
// Every frozen file, by a property; and a line that moves to a new KEY (W-43 track C)
// ---------------------------------------------------------------------------

/// A line's key reader, as a bless and the history gates hold its file by.
pub type KeyFn = Box<dyn Fn(&Value) -> Option<String>>;

/// `tm/tests/fixtures`.
pub fn fixtures_dir() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures")
}

/// **Does a line carry a fork DAY** — a frozen planner or grid answer: a comparand's `shipped`, a
/// grid's `fork`, or a fixture day's `day` beside its `hash` ([`shipped_answer`]'s three shapes)?
pub fn carries_a_fork_day(line: &Value) -> bool {
    line.get("shipped").is_some() || line.get("fork").is_some() || (line.get("day").is_some() && line.get("hash").is_some())
}

/// **Every frozen fork comparand file, and the key its lines are held by — by a PROPERTY of the
/// file, never a list** (W-43 track C, README gap 4461; the campaign's lesson 2). Until W-43 the
/// history gates named ten files by hand, so a comparand frozen after them (W-43's separator days)
/// would have been held by no plain run. A file of [`fixtures_dir`] named `fork-4748911-*.jsonl`
/// whose every line [`carries_a_fork_day`] is one; its key is the lines' `name` where every line
/// carries one, else [`class_key`] where every line carries a `class` (the classes file, whose lines
/// carry no name). The D21 family — the replay and log-line fixtures `TM_FORK_BLESS` rewrites from
/// the oracle, whose lines carry a `replay` or a verdict and no fork day — is not one, by the same
/// property (README gap 4285). A file that is one and has neither key FAILS: an `Err`, never skipped.
pub fn frozen_files() -> Result<Vec<(String, KeyFn)>, String> {
    let dir = fixtures_dir();
    let mut names: Vec<String> = std::fs::read_dir(&dir)
        .map_err(|e| format!("{}: {e}", dir.display()))?
        .filter_map(|e| e.ok().and_then(|e| e.file_name().into_string().ok()))
        .filter(|n| n.starts_with("fork-4748911-") && n.ends_with(".jsonl"))
        .collect();
    names.sort();
    let mut out: Vec<(String, KeyFn)> = Vec::new();
    for name in names {
        let text = std::fs::read_to_string(dir.join(&name)).map_err(|e| format!("{name}: {e}"))?;
        let lines: Vec<Value> = text
            .lines()
            .filter(|l| !l.trim().is_empty())
            .map(|l| serde_json::from_str(l).map_err(|e| format!("{name}: a line that is not JSON ({e})")))
            .collect::<Result<_, _>>()?;
        if lines.is_empty() || !lines.iter().all(carries_a_fork_day) {
            continue;
        }
        let key: KeyFn = if lines.iter().all(|l| l["name"].is_string()) {
            Box::new(key_of("name"))
        } else if lines.iter().all(|l| l["class"].is_string()) {
            Box::new(class_key)
        } else {
            return Err(format!("{name}: a frozen fork comparand whose lines carry neither a `name` nor a `class` to be held by"));
        };
        out.push((name, key));
    }
    Ok(out)
}

/// **The parity numbers a line carries a flag of, and of those the ones SET** — every `p<n>`
/// with a boolean value in an object the line carries beside its world and its days
/// (`forkclass::flag_homes`' reading, which the re-bless gate reads; [`is_answer`] reads the
/// same objects as answers).
pub fn flags(line: &Value) -> (BTreeSet<u32>, BTreeSet<u32>) {
    let (mut all, mut set) = (BTreeSet::new(), BTreeSet::new());
    for (k, v) in line.as_object().into_iter().flatten() {
        if matches!(k.as_str(), "world" | "day" | "shipped" | "whatif") {
            continue;
        }
        for (f, b) in v.as_object().into_iter().flatten() {
            let n = f.strip_prefix('p').filter(|d| !d.is_empty() && d.bytes().all(|c| c.is_ascii_digit())).and_then(|d| d.parse::<u32>().ok());
            if let (Some(n), Some(b)) = (n, b.as_bool()) {
                all.insert(n);
                if b {
                    set.insert(n);
                }
            }
        }
    }
    (all, set)
}

/// **The fields a file's key is made of** — what may move when a line moves to a new key: a
/// `name`-keyed file's `name`; the classes file's class, secondary floor and derivation
/// ([`class_key`]).
pub fn key_fields(line: &Value) -> &'static [&'static str] {
    if line["name"].is_string() {
        &["name"]
    } else {
        &["class", "secondary", "derived"]
    }
}

/// **The lines that left between two versions, paired with the line that holds each one's WORLD
/// in the newer** (W-43 track C, README gap 4320's key-change half): a frozen line's key is a
/// label — the classes file's is its class, which is a FUNCTION of the world through the kernel's
/// reading (`forkclass::class_of`), so a registered number that moves the kernel's reading moves
/// the key (the owner's D87 re-filed two `worked` lines) — and until W-43 a key that left and a key
/// that arrived were two lines to every gate: the old one judged by nothing, the new one a fresh
/// freeze. `(paired, unpaired)`: `paired` is `(old key, new key)` where exactly one ARRIVED line
/// carries the departed line's world byte for byte; `unpaired` is every departed key no arrived
/// line, or more than one, holds the world of, with why — each a finding for the caller to judge
/// ([`left_with_a_redrawn_parent`] says which the owner's D64(b) lets go).
pub fn refiles(old: &BTreeMap<String, Value>, new: &BTreeMap<String, Value>) -> (Vec<(String, String)>, Vec<(String, String)>) {
    let arrived: Vec<&String> = new.keys().filter(|k| !old.contains_key(*k)).collect();
    let (mut paired, mut unpaired) = (Vec::new(), Vec::new());
    for (k, line) in old.iter().filter(|(k, _)| !new.contains_key(*k)) {
        let world = line.get("world").map(|w| serde_json::to_string(w).expect("a value serialises"));
        let twins: Vec<&&String> = arrived
            .iter()
            .filter(|a| world.is_some() && new[a.as_str()].get("world").map(|w| serde_json::to_string(w).expect("a value serialises")) == world)
            .collect();
        match twins.as_slice() {
            [one] => paired.push((k.clone(), (**one).clone())),
            [] => unpaired.push((k.clone(), format!("`{k}` left the file and no line that arrived holds its world"))),
            many => unpaired.push((k.clone(), format!("`{k}` left the file and {} lines that arrived hold its world", many.len()))),
        }
    }
    (paired, unpaired)
}

/// **A derived line that left with its parent re-drawn** — the one deletion a history gate lets
/// through: the classes' re-draw (the owner's D64(b)) drops a derived line its re-drawn parent's rule
/// no longer derives. `k` names a line of `old` carrying a `derived`, and its parent — the primary
/// line of the same `seed` and `draw` — carries a new D64(b) reason in `new` ([`redrawn`]). Since the
/// W-47 land (README gap 5011) a primary line may be re-drawn at ANOTHER index of its seed
/// (`TM_PLANNER_DRAW_AT`), keeping its class: its parent in `new` is then the primary line of the
/// same seed and the old parent's class (one primary line per class), held to the same reason.
pub fn left_with_a_redrawn_parent(k: &str, old: &BTreeMap<String, Value>, new: &BTreeMap<String, Value>) -> bool {
    let Some(line) = old.get(k).filter(|l| !l["derived"].is_null()) else { return false };
    let primary = |p: &&Value| p["secondary"].is_null() && p["derived"].is_null() && p["seed"] == line["seed"];
    let Some(a) = old.values().find(|p| primary(p) && p["draw"] == line["draw"]).cloned() else { return false };
    let b = new
        .values()
        .find(|p| primary(p) && p["draw"] == line["draw"])
        .or_else(|| new.values().find(|p| primary(p) && p["class"] == a["class"]))
        .cloned();
    matches!(b, Some(b) if redrawn(&a, &b))
}

/// **May a line move from `old` to `new`, a new key?** (W-43 track C, README gap 4320.) Held as an
/// in-place line is held ([`shipped_answer`] byte for byte; every key of the world and the
/// provenance byte for byte) but for the fields its key is made of ([`key_fields`]) — and those may
/// move only when `new` carries a SET parity flag of a number `old` carries no flag of at all: the
/// number whose rule moved the kernel's reading, and with it the key (D64(a)'s licence, read off the
/// line as the re-bless gate reads it; the number's registration is `planner_classes.rs`'
/// `every_parity_flag_names_a_registered_number`'s, on every run). `Ok` names the licensing
/// numbers (empty when no key field moved); `Err` says what moved that may not.
pub fn refiled_allows(old: &Value, new: &Value) -> Result<Vec<u32>, String> {
    if shipped_answer(old) != shipped_answer(new) {
        return Err("it moved the SHIPPED fork's answer".to_string());
    }
    let fields = key_fields(old);
    let keys: BTreeSet<&String> = old.as_object().into_iter().flatten().chain(new.as_object().into_iter().flatten()).map(|(k, _)| k).collect();
    let mut key_moved = false;
    for k in keys {
        if is_answer(old, k) || is_answer(new, k) || old[k.as_str()] == new[k.as_str()] {
            continue;
        }
        if fields.contains(&k.as_str()) {
            key_moved = true;
            continue;
        }
        return Err(format!("it moved `{k}`, which is its world or provenance"));
    }
    if !key_moved {
        return Ok(Vec::new());
    }
    let (old_all, _) = flags(old);
    let licence: Vec<u32> = flags(new).1.into_iter().filter(|n| !old_all.contains(n)).collect();
    if licence.is_empty() {
        return Err(format!(
            "its key moved ({}) and it carries no newly set parity flag — a key moves only with the number whose rule moved it",
            fields.join(", ")
        ));
    }
    Ok(licence)
}
