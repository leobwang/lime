"""The exemption ratchets' second comparand: the file's COMMITTED HISTORY.

**THE FINDING** (W-41's verifier; the W-41 repair, README gap 4132).  Every
exemption file under `kernel/` "may only SHRINK" (the owner's D51, strict since
the campaign's D81 call on README gap 3953), and every gate that reads one held
it against the file at HEAD -- `reach.committed_exemptions`, and its copies in
`fields.py`, `twins.py` and `totality.py`.  HEAD is the right comparand for a
working copy and the wrong one for a commit: once the growth is COMMITTED, HEAD
holds it, and the next run compares the file with itself.  Driven by the
verifier in a clone: a `def` no export reaches, added to `reach-exempt.txt` and
committed on a throwaway branch, gave `reach.py` rc=0 and `EXEMPT 1200` (was
1199) -- so an auditor, or the next `check.sh` on the committed tree, could not
see the growth the working-copy run refused.

**THE RULE THIS ADDS.**  Since `BASE` -- `17a13c2` (`122e153` before D88), the commit W-41's four
tracks branched from, before the strict rule took effect -- every commit on HEAD's FIRST-PARENT line that
changed the file is held against its own first parent by the gate's own key
reader: a key the commit's file holds and its parent's did not is growth, and
FAILS, naming the commit.  First-parent, so a track merged in is judged by the
merge (the net change it brought to the line); every commit, so it does not
matter whether the growth arrived in the commit that changed the gate or in a
later one.  A commit whose growth the owner grants is the owner's to grant by
moving `BASE` past it, in the commit that does -- a line in a diff, as a
heading never was.

**"SHRINK" IS MEASURED BY SCOPE, NEVER BY LINE** (the owner's D121, W-48 track
H, README gap 5037).  A file shrinks when the SET it exempts -- definitions,
fields, key paths, pairs -- is no larger; its line count is formatting.  So every
gate's key reader returns SCOPE ATOMS, and a commit's `allowed` hook answers an
atom its parent's file already covered by a wider line.  The seven files, found
by the property "a gate holds it against itself at HEAD" (`git show HEAD:`
beside this module's walk), and what one line of each exempts:

  reach-exempt.txt       an entry: one definition; a `CLASS` line: every
                         definition its class answers, measured on this tree
                         (the class scope reach.py's `main` computes).  An entry
                         a class held is not growth; a
                         NEW class line is, because a class is a rule that answers
                         definitions not yet written.
  twins-exempt.txt       a NOT ONE CONCEPT verdict: every PAIR of its members
                         (`twins.not_one_pairs`); a ONE CONCEPT line is a debt
                         with an EXIT and exempts nothing permanently.
  written-exempt.txt,    a key path and every path under it (`fields.under`):
  sent-exempt.txt        `plan` -> `plan.segments` + `plan.priorities` is narrower.
  fields-exempt.txt,     one line, one field / one declaration: the key IS the
  inputs-exempt.txt,     scope, and no line can be split.
  kernel-decide-exempt.txt

**WHAT IT CANNOT SEE, declared.**  A step BEFORE `BASE`, when growth under a
dated section was the rule (W-31 to W-40).  A track's own commit off the line
(it is judged by the merge that brings it, the net change).  A history git
cannot read (a `git archive` copy, a shallow clone without `BASE`) answers
`None`, and every gate then FAILS as UNCHECKED rather than passing on nothing,
exactly as its HEAD comparand already did.
"""

import re
import subprocess

#: **THE RENAME, SPELT ONCE** (tm -> lime, step 1).  Every gate that compares this tree with an older commit
#: reads that commit in its OLD spelling and under its OLD paths: the exemption files name `Tm.Planner.x` where
#: they now name `Lime.Planner.x`, and `kernel/TmKernel/Goals.lean` is where `kernel/LimeKernel/Goals.lean` was.
#: Spelling is not scope (D121), so `respell` is applied to whatever a commit is read as, and a key that only
#: changed its spelling is the key its parent held; a key the parent held under NO spelling is still growth.
#: `old_path` answers the second half.  Checked by planting a real new exempt line in a scratch copy of each
#: file (kernel/README.md's rename block): every plant still FAILS.
RENAMED_PATHS = (
    ("kernel/LimeKernel/LimeKernel/", "kernel/TmKernel/TmKernel/"),
    ("kernel/LimeKernel/LimeKernel.lean", "kernel/TmKernel/TmKernel.lean"),
    ("kernel/LimeKernel/", "kernel/TmKernel/"),
    ("kernel/lime-kernel-ffi/", "kernel/tm-kernel-ffi/"),
    ("lime-core/", "tm-core/"),
    ("lime/", "tm/"),
)
_ATOM = re.compile(r"TmKernel|TmArch|(?<![A-Za-z0-9])(?:tm|Tm|TM)(?![A-Za-z0-9])")
_IDENTISH = re.compile(r"[A-Za-z0-9_)\]>]")
_REV_BEFORE = re.compile(r"(?:\b[0-9a-f]{7,40}|<[A-Za-z_-]+>):$")


def _is_dot_tm(text, s):
    """`.tm` the directory, and not `x.tm` a field: the character before the dot is no identifier, or it is the
    last character of an escape (`"\\n.tm/state.json"`)."""
    if text[s - 1:s] != ".":
        return False
    if s < 2 or not _IDENTISH.match(text[s - 2]):
        return True
    return s >= 3 and text[s - 3] == "\\"


def respell(text):
    """`text` in the new spelling.  It keeps what the rename keeps: `.tm`, `tm:<marker>`, `-//tm//`, `<rev>:tm...`,
    `tm-tmp`.  A text already in the new spelling comes back unchanged."""
    def one(m):
        tok, s, e = m.group(0), m.start(), m.end()
        if tok == "TmKernel":
            return "LimeKernel"
        if tok == "TmArch":
            return "LimeArch"
        if tok == "Tm":
            return "Lime"
        if tok == "TM":
            return "LIME" if text[e:e + 1] == "_" else tok
        if text[e:e + 1] != "_" and _is_dot_tm(text, s):
            return tok
        if text[max(0, s - 6):s] in ("--- a/", "+++ b/"):
            return tok
        if text[s - 2:s] == "//" and text[e:e + 2] == "//":
            return tok
        if text[e:e + 1] == ":" and text[e + 1:e + 2] not in ("", ":", " ", "\n", "\t"):
            return tok
        if _REV_BEFORE.search(text[max(0, s - 44):s]):
            return tok
        if text.startswith(("tm-tmp", "tm-spec.md"), s):
            return tok
        return "lime"
    return _ATOM.sub(one, text)


def old_path(rel):
    """The repository-relative path `rel` had before the rename, or None when it has not moved."""
    for new, old in RENAMED_PATHS:
        if rel == new or (new.endswith("/") and rel.startswith(new)):
            return old + rel[len(new):]
    return None


#: **GROWTH THE OWNER GRANTED, NAMED** (W-49 track P; the owner's D124, README gap 5130).
#: "Growth is the owner's to grant, in the commit that changes this script" was a sentence in
#: every gate's header and no gate had a place to read a grant from: the only route was moving
#: `BASE` past the commit that grew a file, which no commit can do for itself (its own hash is
#: not known until it is made), and the HEAD comparand refuses the growth before it is
#: committed at all.  So a grant is a ROW HERE, keyed by the file and the gate's own key
#: spelling (`reach.py`'s `CLASS <key>`, `fields.py`'s key path), carrying the decision that
#: grants it -- and the line it licenses must cite that decision in its own reason
#: (`granted`), so a grant licenses ONE line with ONE reason and not a key whatever it says.
#: Every gate that holds a file against HEAD or against its history asks `granted` before it
#: calls a new key growth.  WHAT IT CANNOT SEE, declared: a granted line deleted and later
#: re-added with the same citation passes again -- the row is a standing grant until a commit
#: deletes it, which is the owner's too.
GRANTS = {
    ("reach-exempt.txt", "CLASS plan"): "D124",
    ("written-exempt.txt", "plan.bed"): "D124",
    # D124 named `plan.bed`, measured by the W-48 probe on a tree where `plan.segments` and
    # `plan.priorities` still had lines of their own and the divider's two keys did not exist;
    # on W-49's tree the section's other four keys are unwritten with it, and the grant's stated
    # scope -- the `plan` section as the harness's door -- covers them (README gap 5260, which
    # asks the owner to confirm it).
    ("written-exempt.txt", "plan.segments"): "D124",
    ("written-exempt.txt", "plan.priorities"): "D124",
    ("written-exempt.txt", "plan.budgetBlocks"): "D124",
    ("written-exempt.txt", "plan.windowEnd"): "D124",
}


def granted(path, key, reason=None):
    """Whether the owner granted `key` in `path` (a row of `GRANTS`), and -- when `reason` is
    given -- whether that line's own reason cites the granting decision."""
    d = GRANTS.get((path.name, key))
    if d is None:
        return False
    return reason is None or d in reason

#: `17a13c2`, the commit every W-41 track branched from: the strict rule (D81, gap
#: 3953) took effect inside W-41, so the walk covers the whole of it.  It was
#: `122e153` until the owner's D88 rewrote W-40's and W-41's lands into single
#: measured commits (2026-10-02): `17a13c2` is that commit with its tree
#: byte-identical, at the same place on the first-parent line, so the walk is the
#: one it was -- the base is RE-POINTED, not moved past anything.
BASE = "17a13c234547a409a352d1ac15d2d62d2110f01c"


def _git(path, *args):
    try:
        out = subprocess.run(["git", "-C", str(path.parent)] + list(args),
                             capture_output=True, text=True, timeout=120)
    except (OSError, subprocess.SubprocessError):
        return None
    return out.stdout if out.returncode == 0 else None


def show(path, rev):
    """`path`'s text at `rev`, IN THE NEW SPELLING and read from the path the file had in that commit (`respell`,
    `old_path`): `""` when the file is not in that commit under either path, `None` when git cannot say."""
    listed = _git(path, "ls-tree", rev, "--", path.name)
    if listed is None:
        return None
    if listed.strip():
        text = _git(path, "show", "%s:./%s" % (rev, path.name))
    else:
        prefix = _git(path, "rev-parse", "--show-prefix")
        if prefix is None:
            return None
        old = old_path(prefix.strip() + path.name)
        if old is None:
            return ""
        listed = _git(path, "ls-tree", "--full-tree", rev, "--", old)
        if listed is None:
            return None
        if not listed.strip():
            return ""
        text = _git(path, "show", "%s:%s" % (rev, old))
    return None if text is None else respell(text)


def committed(path, rev="HEAD"):
    """`show`, for a caller to whom a file absent at `rev` and a git that cannot say are one answer: `None`."""
    text = show(path, rev)
    return text if text else None


def history(path):
    """`[(sha, parent_text, text)]` for every commit after `BASE` on HEAD's
    first-parent line whose `path` differs from its first parent's, oldest
    first; `None` when git cannot say (no repository, or `BASE` is not an
    ancestor of HEAD)."""
    if _git(path, "merge-base", "--is-ancestor", BASE, "HEAD") is None:
        return None
    revs = _git(path, "rev-list", "--first-parent", "--reverse", "%s..HEAD" % BASE)
    if revs is None:
        return None
    out = []
    for sha in revs.split():
        cur = show(path, sha)
        prev = show(path, sha + "^1")
        if cur is None or prev is None:
            return None
        if cur != prev:
            out.append((sha, prev, cur))
    return out


def grown(path, keys, allowed=None):
    """The complaints for every key a committed step ADDED: `keys(text)` is the
    gate's own reader of the file's entries as a set; `allowed(sha, key, prev)`,
    when given, answers a key the gate's rule lets a commit add (a field the
    structure did not have, a key under one already exempt).  `None` when git
    cannot say -- the caller fails as UNCHECKED."""
    steps = history(path)
    if steps is None:
        return None
    out = []
    for sha, prev, cur in steps:
        held = keys(prev)
        for key in sorted(keys(cur) - held, key=str):
            if allowed is not None and allowed(sha, key, held):
                continue
            if granted(path, key):
                continue
            out.append("RATCHET (committed): %s grew at %s -- `%s` is held by no entry of its "
                       "first parent, and this file may only SHRINK (D51; README gap 4132: "
                       "growth that reached a commit is growth HEAD can no longer see)"
                       % (path.name, sha[:9], key))
    return out
