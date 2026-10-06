#!/usr/bin/env python3
"""What every capacity arm asked the oracle, read off the census its store writes.

run-oracle.sh's input set 7 runs the whole workspace under TM_ORACLE, and every
test target whose comparand W-46 track C moved to `tm-oracle capacity` asks the
oracle live there.  Until W-47 only T13 (`kernel_lookahead_parity`) printed what
it asked, so a sweep's figure for the others was a count of tests, not of
requests -- a target whose tests stopped asking would still have reported its
pass count (W-47 track C, README gap 4998).

So `tm/tests/support/forkcap.rs` writes a census when TM_FORKCAP_CENSUS names a
directory: every store appends one line per request it answers to
`<dir>/<its frozen file>.asks`, `<mode>\t<op>\t<key>` (a fresh request's op is
suffixed ` (live)` and its key is `-`, `Store::ask_live`).  This reads that
directory against the CLASS of frozen capacity files -- every
`tm/tests/fixtures/fork-4748911-capacity-*.jsonl`, by no list: a binary that
includes the store and is blessed is counted by being blessed -- and prints, per
file, the requests its binary asked the oracle by op, how many distinct frozen
answer lines that was out of how many the file holds, and the fresh requests.

It FAILS (exit 1), naming the file, when
  * the binary asked the oracle none of its frozen answer lines -- the case gap
    4998 says nothing reported: its tests stopped asking, or stopped running;
  * a request was answered from the frozen file alone (mode `Frozen`): the
    binary did not see TM_ORACLE, so nothing was compared with the fork today;
  * an asked frozen-held key is not in the file -- `Store::ask` refuses such a
    request, so either a test already failed on it by name or the census is not
    the store's;
  * a census file pairs with no frozen file and asked anything but fresh
    requests (the same refusal, from the other side).
A frozen line no test asks any more is printed, not failed: it leaves at the
next bless, as the store's module doc declares.

    capacity-census.py <census-dir>
"""
import json
import sys
from collections import Counter
from pathlib import Path

ROOT = Path(__file__).resolve().parents[4]
FIXTURES = ROOT / "tm" / "tests" / "fixtures"
PREFIX = "fork-4748911-capacity-"
SUFFIX = ".jsonl"
LIVE = " (live)"
ASKED_OF_THE_ORACLE = ("Oracle", "Record")


def frozen_keys(path: Path) -> set:
    """The answer lines' keys (a configuration line carries `config` and no `op`)."""
    keys = set()
    for raw in path.read_text().splitlines():
        if raw.strip():
            v = json.loads(raw)
            if "op" in v:
                keys.add(v["key"])
    return keys


def read_census(path: Path, failures: list, who: str) -> list:
    rows = []
    if path.exists():
        for raw in path.read_text().splitlines():
            if not raw:
                continue
            parts = raw.split("\t")
            if len(parts) != 3:
                failures.append(f"{who}: a census line that is not three fields: {raw!r}")
                continue
            rows.append(tuple(parts))
    return rows


def ops_text(counter: Counter) -> str:
    return ", ".join(f"{op} {n}" for op, n in sorted(counter.items())) or "nothing"


def main(argv) -> int:
    if len(argv) != 2:
        print(__doc__.strip().splitlines()[-1].strip(), file=sys.stderr)
        return 2
    census = Path(argv[1])
    if not census.is_dir():
        print(f"capacity census: {census} is not a directory -- was TM_FORKCAP_CENSUS set?", file=sys.stderr)
        return 1
    frozen = sorted(FIXTURES.glob(PREFIX + "*" + SUFFIX))
    failures = []
    if not frozen:
        failures.append(f"no frozen capacity file under {FIXTURES}")
    print(f"capacity census ({census}): {len(frozen)} frozen capacity file(s), the class "
          f"tm/tests/fixtures/{PREFIX}*{SUFFIX}")
    paired = set()
    total_asked = total_distinct = total_lines = total_live = 0
    for f in frozen:
        target = f.name[len(PREFIX):-len(SUFFIX)]
        asks = census / (f.name + ".asks")
        paired.add(asks.name)
        keys = frozen_keys(f)
        rows = read_census(asks, failures, target)
        held = [r for r in rows if not r[1].endswith(LIVE)]
        live = [r for r in rows if r[1].endswith(LIVE)]
        oracle_held = [r for r in held if r[0] in ASKED_OF_THE_ORACLE]
        frozen_only = [r for r in rows if r[0] == "Frozen"]
        asked_keys = {k for _, _, k in oracle_held}
        met = asked_keys & keys
        foreign = {k for _, _, k in held} - keys
        stale = keys - met
        print(
            f"  {target}: asked the oracle {len(oracle_held)} frozen-held request(s) ({ops_text(Counter(op for _, op, _ in oracle_held))}); "
            f"{len(met)} of {len(keys)} frozen answer line(s) asked"
            + (f", {len(stale)} no test asks (they leave at the next bless)" if stale and met else "")
            + (f"; {len(live)} fresh ({ops_text(Counter(op for _, op, _ in live))})" if live else "")
        )
        total_asked += len(oracle_held)
        total_distinct += len(met)
        total_lines += len(keys)
        total_live += len(live)
        if frozen_only:
            failures.append(
                f"{target}: {len(frozen_only)} request(s) answered from {f.name} alone (mode Frozen) -- the binary did not "
                f"see TM_ORACLE, so nothing it asked met the fork today"
            )
        elif not met:
            failures.append(
                f"{target}: its binary asked the oracle NONE of the {len(keys)} answer line(s) frozen in {f.name} "
                f"({'no census file' if not asks.exists() else f'{len(rows)} census line(s)'}) -- its tests stopped asking, "
                f"or did not run (README gap 4998)"
            )
        if foreign:
            failures.append(
                f"{target}: {len(foreign)} asked key(s) {sorted(foreign)[:3]} that {f.name} does not hold -- the store refuses "
                f"such a request: a test failed on it by name, or this census is not the store's"
            )
    for extra in sorted(census.glob("*.asks")):
        if extra.name in paired:
            continue
        rows = read_census(extra, failures, extra.name)
        held = [r for r in rows if not r[1].endswith(LIVE)]
        print(f"  {extra.name}: no frozen capacity file; {len(rows)} request(s) ({ops_text(Counter(op for _, op, _ in rows))})")
        total_live += len(rows) - len(held)
        if held:
            failures.append(
                f"{extra.name}: {len(held)} frozen-held request(s) and no frozen file to hold them -- the store refuses such a request"
            )
    print(
        f"capacity census: {total_asked} frozen-held request(s) asked of the oracle, {total_distinct} of {total_lines} "
        f"frozen answer line(s) asked, {total_live} fresh request(s); {len(failures)} failure(s)"
    )
    for msg in failures:
        print(f"FAILED: {msg}")
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
