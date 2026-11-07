//! **Parity P104, carried by value** — the owner's **D99** (README gap 4520a, W-47 track K): one reading of a
//! block whatever order its marks are logged in.
//!
//! The kernel's replay holds an open block's own idle spans and the pieces it drew, and re-draws it at every mark
//! (`Replay.settle`): a `pause` or an `interrupt` logged after a stretch it lies across was closed is netted from that
//! stretch where it lies, and the block's pieces are the complement of its NONEMPTY idle spans, so a pause and its
//! unpause stamped at one instant leave one piece.  Fork point `4748911`'s machine credited and drew each stretch when
//! its clock stopped and never moved it again, and split a stretch at every stop, empty or not.
//!
//! **What this carries, and why by value.**  Among the frozen fork answers T5 and the door compare, P104 moves exactly
//! one input — the representative generated month (`loggen`, 40 a day) — at exactly two places, each found by the
//! comparison and read off the log by hand (README "Stage 6 — W-47 track K", §5):
//!
//! * **2026-01-01, `^667`**: `start` 07:02, `pause` 07:30, `unpause` 07:35, then an `interrupt` stamped **07:22** logged
//!   after them (the generator's clock behind its log) and its `resume` at 07:37, `stop` 08:16.  The fork drew and
//!   credited `[07:02, 07:30]` at the pause and kept it; the kernel nets the interruption's `[07:22, 07:30]` from it —
//!   the first piece ends at 07:22, and the cut's credit is 59, the host's union (elapsed 74 less the union 07:22-07:37,
//!   15), not 67.
//! * **2026-01-06, `^255`**: `pause` and `unpause` both stamped 11:59 — an empty stop.  The fork split the stretch at
//!   it, `[11:47, 11:59]` and `[11:59, 12:35]`; the kernel draws the one piece `[11:47, 12:35]` (the same minutes).
//!
//! Each move names the fork's value it replaces (after P81's and P85's carries, which run first) and the value it
//! carries, and **a fork value that is not the named one is refused by name** — so the carry cannot move a leaf the
//! frozen answer no longer holds, and a re-blessed fixture that moved under it is a finding, not a silent pass.  A
//! rule over the fork's answer alone cannot see which marks were logged out of order (the answer holds no line
//! order), which is why this carry is a list and P81's and P85's are rules.  **The live oracle arm (`TM_ORACLE`) asks
//! P104 by a rule since the W-47 repair** (`late.rs`, README gap 5028, which closes gap 4912), and holds this list to
//! the fork's own answer asked that day on the one frozen input it moves.

use serde_json::Value;

/// What [`carry`] moved, so a comparison can say how much P104 it carried rather than claim it.
#[derive(Default, Debug)]
pub struct P104Tally {
    /// Leaves replaced or segments removed.
    pub moves: usize,
}

/// One move: the input, the path under the answer's `replay`, the fork's value there, and the kernel's — `None` for
/// a segment the kernel does not draw (removed from its list).
struct Move {
    input: &'static str,
    path: &'static [&'static str],
    fork: &'static str,
    kernel: Option<&'static str>,
}

const MONTH: &str = "generated 1mo (40 a day)";

const MOVES: &[Move] = &[
    Move { input: MONTH, path: &["days", "2026-01-01", "block_min"], fork: "471", kernel: Some("463") },
    Move { input: MONTH, path: &["days", "2026-01-01", "ci_unknown", "667"], fork: "67", kernel: Some("59") },
    Move {
        input: MONTH,
        path: &["days", "2026-01-01", "segments", "0", "end"],
        fork: "\"2026-01-01T07:30:00-06:00\"",
        kernel: Some("\"2026-01-01T07:22:00-06:00\""),
    },
    Move { input: MONTH, path: &["items", "667", "minutes"], fork: "67", kernel: Some("59") },
    Move { input: MONTH, path: &["items", "667", "minutes_by_day", "2026-01-01"], fork: "67", kernel: Some("59") },
    // The empty stop at 11:59: the second piece goes first (its index is read before the first piece moves), then
    // the first runs to the second's end.
    Move {
        input: MONTH,
        path: &["days", "2026-01-06", "segments", "9"],
        fork: "{\"end\":\"2026-01-06T12:35:00-06:00\",\"kind\":{\"Block\":{\"id\":\"255\"}},\"start\":\"2026-01-06T11:59:00-06:00\"}",
        kernel: None,
    },
    Move {
        input: MONTH,
        path: &["days", "2026-01-06", "segments", "8", "end"],
        fork: "\"2026-01-06T11:59:00-06:00\"",
        kernel: Some("\"2026-01-06T12:35:00-06:00\""),
    },
];

fn step<'a>(v: &'a mut Value, key: &str) -> Option<&'a mut Value> {
    match v {
        Value::Object(m) => m.get_mut(key),
        Value::Array(a) => key.parse::<usize>().ok().and_then(|i| a.get_mut(i)),
        _ => None,
    }
}

/// **The fork's frozen answer for `name`, moved by P104's named leaves and nothing else** — after P81's and P85's
/// carries.  An input P104 does not move comes back unchanged with a zero tally.
pub fn carry(name: &str, answer: &Value) -> Result<(Value, P104Tally), String> {
    let mut out = answer.clone();
    let mut t = P104Tally::default();
    for m in MOVES.iter().filter(|m| m.input == name) {
        let want: Value = serde_json::from_str(m.fork).map_err(|e| format!("P104: a move's fork value: {e}"))?;
        let path = m.path.join(".");
        let (last, parent) = m.path.split_last().ok_or("P104: an empty path")?;
        let mut node = out.get_mut("replay").ok_or_else(|| format!("P104 ({name}): the answer has no `replay`"))?;
        for k in parent {
            node = step(node, k).ok_or_else(|| format!("P104 ({name}): `{path}` is not in the fork's answer"))?;
        }
        let here = step(node, last).ok_or_else(|| format!("P104 ({name}): `{path}` is not in the fork's answer"))?;
        if *here != want {
            return Err(format!("P104 ({name}): `{path}` is {here}, not the fork's value this carry names ({want})"));
        }
        match m.kernel {
            Some(k) => *here = serde_json::from_str(k).map_err(|e| format!("P104: a move's kernel value: {e}"))?,
            None => {
                let i: usize = last.parse().map_err(|_| format!("P104 ({name}): `{path}` removes a non-index"))?;
                match node {
                    Value::Array(a) => {
                        a.remove(i);
                    }
                    _ => return Err(format!("P104 ({name}): `{path}` removes from a non-list")),
                }
            }
        }
        t.moves += 1;
    }
    Ok((out, t))
}
