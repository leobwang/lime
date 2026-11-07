#!/usr/bin/env python3
"""CHECK 15: THE KERNEL'S SEVEN FOLDERS ARE A ONE-WAY TABLE, AND AN IMPORT AGAINST IT FAILS.

The owner queued the regroup on 2026-11-05, on the main session's seven-folder proposal ("queue grouping after
rename", AGENTS D162): the 97 library modules live in `Base/`, `Plan/`, `Log/`, `Seal/`, `Planner/`, `Wire/` and
`Laws/`, and each folder imports only from itself and the folders above it.  The folders are the owner's.  This gate
is the campaign's call, revisable as D39's was: nothing else in `check.sh` holds the direction (`replay.py` reads the whole
graph for a memo key, `totality.py` one file's imports, the leaf rules in `mutate.py` and `reach.py` one module's
importers), so the direction the folders were chosen for would be true on the day of the move and held by nothing after it.

THE TABLE IS DATA: `kernel/layers.txt`, one line per folder, top first, and a `PREFIX` line for a family of modules a
folder owns.  This file holds no folder's name.

THE PROPERTY.  For every library module (`leanfiles.library_files`, Lake's library target, less the
root module), and every import it declares (`leanfiles.imports`), this fails, by name, on:

  AGAINST   a module importing a module of a folder below its own in the table;
  OUTSIDE   a library module directly under the library directory, or two folders down;
  FOLDER    a library module in a folder the table does not name;
  STALE     a folder the table names that holds no module (a table that describes nothing gates nothing);
  PREFIX    a module whose name carries a `PREFIX` line's prefix, outside that line's folder (`Seal*` outside `Seal/`);
  UNPLACED  an import that is not a library module: `import LimeKernel`, a folder (`import LimeKernel.Plan`), or
            anything outside the kernel.  The table cannot place it, and an arm that skipped it would be the way round
            the other arms.
  NAMESAKE  a `.lean` file whose name another file of the package also has: `Wire/PlannerWit.lean` beside
            `Laws/PlannerWit.lean`, or `Wire/Check.lean` beside `Check.lean`.

NAMESAKE IS HERE BECAUSE THE FOLDERS OPENED IT.  One flat directory could not hold two files of one name, so every gate
was free to key a module by its file name, and they do: `reach.py`'s definitions, witness class, proof class and exemption
sections, `mutate.py`'s error sites, `totality.py`'s `kernel-decide-exempt.txt` keys, `twins.py`'s search for a module's C.
Driven before this arm, each with `check.sh` otherwise green: an unreached `def` in a new `Wire/PlannerWit.lean` or
`Wire/PlanCheck.lean` read as the witness or proof class, and `reach.py` passed it (the same text in `Wire/W55Dead.lean`
failed checks 9 and 12); `mutate.py` placed a failure at `Wire/PlannerWit.lean:3` in `Laws/PlannerWit.lean`, where no
declaration encloses that line, and called the definition PINNED; `decide +kernel` passed `totality.py` in a new
`Laws/Planner.lean` under a theorem name `Planner.lean`'s line exempts; a second `PlanWire.lean`'s `def` was counted in the
real module's census.  So the premise those readers rest on is stated here, once, rather than each being rewritten: a file
name names one file.  Run alone, each still reads two namesakes as one (README gap 6120).

THE ROOT MODULE IS NOT READ AGAINST THE TABLE, by a property and not by its name: it is the module beside the library
directory, it must import every module for Lake to build it (AGENTS 2.3), and `replay.py` already fails if it holds
anything but imports.  `Check.lean`, `Negative.lean` and `Goals.lean` import the root and are not library modules.

THE IMPORTS ARE READ FROM THE HEADER AS LEAN READS IT, never by a line pattern.  `leanfiles.imports` strips comments and
string bodies with the scanner check 2 uses, then walks the header's words, so a comment or a string cannot fake an
import, and `public import X`, `import all X`, `import X import Y` on one line and an `import` whose module is on the
next line each count.  Lean 4.33.1 accepts those last two and refuses `import X Y` and an `import` below the header.  It
refuses the first two without `module`, and a `module` cannot import a non-module, which every module here is; they are
read anyway, so the day one is a `module` this gate already sees it.

WHAT IT CANNOT SEE, declared.  Whether a module is in the RIGHT folder: the table states a direction, so a module moved
down the table passes while nothing above imports it.  A folder's internal order.  What `Check.lean`, `Negative.lean`
and `Goals.lean` import (each reads the whole library through the root, and check 2 reads their import lines).  A
non-`Seal*` module in `Seal/`: the prefix rule reads one way.

A TABLE OR A WALK THAT READS NOTHING IS A HARD ERROR, never a green line: no folder, no module or no import read.
"""
import pathlib
import sys

import leanfiles

HERE = pathlib.Path(__file__).resolve().parent
PKG = HERE / "LimeKernel"
TABLE = HERE / "layers.txt"


def read_table(text):
    """`(folders, prefixes, bad)`: the folders in order, `{prefix: folder}`, and each line this cannot read."""
    folders, prefixes, bad = [], {}, []
    for lineno, raw in enumerate(text.split("\n"), 1):
        line = raw.strip()
        if not line or line.startswith("#"):
            continue
        words = line.split()
        if words[0] == "PREFIX":
            if len(words) != 3:
                bad.append("%s:%d  a prefix line is `PREFIX <prefix> <folder>`" % (TABLE.name, lineno))
            else:
                prefixes[words[1]] = words[2]
        elif len(words) >= 3 and words[1] == "--":
            if words[0] in folders:
                bad.append("%s:%d  `%s` is listed twice" % (TABLE.name, lineno, words[0]))
            folders.append(words[0])
        else:
            bad.append("%s:%d  a folder line is `<folder> -- <what it holds>`" % (TABLE.name, lineno))
    for prefix, folder in prefixes.items():
        if folder not in folders:
            bad.append("%s  `PREFIX %s` names `%s`, which is no folder of the table" % (TABLE.name, prefix, folder))
    return folders, prefixes, bad


def check(pkg, table_text):
    """`(summary, complaints)` for the package at `pkg` under the table's text."""
    folders, prefixes, bad = read_table(table_text)
    if not folders:
        raise SystemExit("layers.py: %s names no folder -- this check would gate nothing" % TABLE.name)
    rank = {f: i for i, f in enumerate(folders)}
    lib = pkg / pkg.name
    root_file = pkg / (pkg.name + ".lean")
    mods = {}
    for p in leanfiles.library_files(pkg):
        if p == root_file:
            continue
        parts = p.relative_to(lib).with_suffix("").parts
        mods[".".join((pkg.name,) + parts)] = (p, parts)
    if not mods:
        raise SystemExit("layers.py: no library module under %s -- this check would gate nothing" % lib)
    held = {f: 0 for f in folders}
    folder_of = {}
    for name, (p, parts) in sorted(mods.items()):
        if len(parts) != 2:
            bad.append("OUTSIDE: %s is %s, and a library module sits in exactly one folder of %s"
                       % (p.relative_to(pkg), "directly under the library" if len(parts) == 1 else
                          "%d folders down" % (len(parts) - 1), TABLE.name))
        elif parts[0] not in rank:
            bad.append("FOLDER: %s is in `%s/`, which %s does not name" % (p.relative_to(pkg), parts[0], TABLE.name))
        else:
            folder_of[name] = parts[0]
            held[parts[0]] += 1
        for prefix, folder in prefixes.items():
            if parts[-1].startswith(prefix) and parts[:-1] != (folder,):
                bad.append("PREFIX: %s is outside `%s/`, which holds every `%s*` module"
                           % (p.relative_to(pkg), folder, prefix))
    for f in folders:
        if not held[f]:
            bad.append("STALE: %s names `%s/`, which holds no module" % (TABLE.name, f))
    read = 0
    for name, (p, _parts) in sorted(mods.items()):
        for target in leanfiles.imports(p.read_text(encoding="utf-8")):
            read += 1
            if target not in mods:
                bad.append("UNPLACED: %s imports %s, which is no library module, so the table cannot place it"
                           % (p.relative_to(pkg), target))
            elif name in folder_of and target in folder_of \
                    and rank[folder_of[target]] > rank[folder_of[name]]:
                bad.append("AGAINST: %s (%s/) imports %s (%s/), and %s/ is below %s/ in %s"
                           % (p.relative_to(pkg), folder_of[name], target, folder_of[target],
                              folder_of[target], folder_of[name], TABLE.name))
    named = {}
    for p in leanfiles.lean_files(pkg):
        named.setdefault(p.name, []).append(p)
    for fname, paths in sorted(named.items()):
        if len(paths) > 1:
            bad.append("NAMESAKE: %s share the file name `%s`, and the gates key a module by its file name, so they "
                       "would read these as one" % (" and ".join(str(q.relative_to(pkg)) for q in sorted(paths)), fname))
    if not read:
        raise SystemExit("layers.py: not one import read from %d modules -- this check would gate nothing" % len(mods))
    summary = "%d modules in %d folders (%s), %d imports read, 0 against the table" % (
        len(mods), len(folders), ", ".join("%s %d" % (f, held[f]) for f in folders), read)
    return summary, bad


def main():
    summary, bad = check(PKG, TABLE.read_text(encoding="utf-8"))
    if bad:
        for line in bad:
            print(line)
        print("%d complaint(s) from %s" % (len(bad), TABLE.name))
        return 1
    print(summary)
    return 0


if __name__ == "__main__":
    sys.exit(main())
