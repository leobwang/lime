#!/usr/bin/env python3
"""A capacity file RE-KEYED by the model wire's move, not RE-ANSWERED — checked by value.

W-47 track C (README gap 4891): `lime-oracle capacity` reads a model as `.tm/model.json`'s TEXT
through fork 4748911's own loader, where it read three hand-crossed tables (`energy`,
`p_lounge` as each weight's display text, `expected_arrival`) with a parse of its own.  Every
`today` and `lookahead` request therefore has a new canonical text and a new key, and the file
`support/forkcap.rs` reads was re-blessed (`forkcap::the_frozen_fork_capacity_answers_are_
reblessed_from_the_oracle`).  A re-bless is a decision and never a repair (AGENTS §7.2), so this
says what moved, by value:

  * the configuration lines are byte-identical, and so is every line of an op that carries no
    model (`cut`, `rank`, ...): key, request and answer;
  * every model-carrying request of the old file matches exactly ONE of the new, equal but for
    the model, whose tables are the same exact decimals (weights compared as decimals, so
    `1` and `1.0` are one weight), and the new file adds no request;
  * each matched answer is the old one plus `model_read_by` naming the fork's loader, and
    nothing else.

Usage, from the repository root:

    python3 kernel/lime-kernel-ffi/examples/oracle/model-rekey.py \\
        <(git show <before>:tm/tests/fixtures/fork-4748911-capacity-kernel_lookahead_parity.jsonl) \\
        lime/tests/fixtures/fork-4748911-capacity-kernel_lookahead_parity.jsonl

Exits non-zero, by name, on the first rule that fails.
"""
import collections
import json
import sys
from decimal import Decimal

READ_BY = "store::StoreExt::read_json::<energy::Model>(MODEL_PATH)"
MODEL_OPS = ("today", "lookahead")


def lines(path):
    return [json.loads(l) for l in open(path) if l.strip()]


def split(rows):
    return {l["key"]: l["config"] for l in rows if "config" in l}, [l for l in rows if "config" not in l]


def canon(d):
    return str(Decimal(d).normalize())


def tables(m):
    return {
        "energy": {k: [int(x) for x in v] for k, v in (m.get("energy") or {}).items()},
        "p_lounge": {k: canon(v) for k, v in (m.get("p_lounge") or {}).items()},
        "expected_arrival": m.get("expected_arrival") or {},
    }


def old_model(m):
    return tables(m)


def new_model(text):
    m = json.loads(text, parse_float=str)
    extra = set(m) - {"energy", "duration", "p_lounge", "expected_arrival", "n_obs"}
    if extra or m.get("duration") != {} or m.get("n_obs") != 0:
        sys.exit(f"a re-keyed model carries a table the old wire could not: {sorted(extra)}, duration {m.get('duration')}, n_obs {m.get('n_obs')}")
    return tables(m)


def match_key(line, read):
    req = dict(line["req"])
    model = req.pop("model", None)
    return (line["op"], json.dumps(req, sort_keys=True), json.dumps(None if model is None else read(model), sort_keys=True))


def main():
    oc, oa = split(lines(sys.argv[1]))
    nc, na = split(lines(sys.argv[2]))
    if oc != nc:
        sys.exit("the configuration lines moved")
    plain = lambda rows: {l["key"]: l for l in rows if l["op"] not in MODEL_OPS}
    if plain(oa) != plain(na):
        sys.exit("a line of an op that carries no model moved")
    olds, news = collections.defaultdict(list), collections.defaultdict(list)
    for l in oa:
        if l["op"] in MODEL_OPS:
            olds[match_key(l, old_model)].append(l["answer"])
    for l in na:
        if l["op"] in MODEL_OPS:
            a = dict(l["answer"])
            if a.pop("model_read_by", None) != READ_BY:
                sys.exit(f"{l['key']}: an answer that does not name the fork's loader")
            news[match_key(l, new_model)].append(a)
    if any(len(v) != 1 for v in olds.values()) or any(len(v) != 1 for v in news.values()):
        sys.exit("a model-carrying request is held twice")
    if set(olds) != set(news):
        sys.exit(f"{len(set(olds) - set(news))} old request(s) with no new twin, {len(set(news) - set(olds))} new one(s) with no old")
    moved = [k for k in olds if olds[k] != news[k]]
    if moved:
        sys.exit(f"{len(moved)} answer(s) moved beyond `model_read_by`")
    print(
        f"configurations {len(oc)} byte-identical; {len(plain(oa))} model-free answer line(s) byte-identical; "
        f"{len(olds)} today/lookahead request(s) re-keyed, each matched to one old request by value, "
        f"0 answers moved beyond `model_read_by`"
    )


if __name__ == "__main__":
    main()
