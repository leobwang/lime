//! **Parities P104 and P105, asked of fork 4748911** — the owner's **D99** (README gap 4520a: one reading of an open
//! block whatever order its marks are logged in) and **D100** (gap 4520b: a break logged AFTER a block's `done` or
//! `stop` but stamped inside it is netted from the block, the later break winning).  W-47 repair, README gap 5028,
//! which closes track K's gaps 4912 and 4919: until this module the T5 `LIME_ORACLE` arm held both numbers by no rule,
//! and `run-oracle.sh` stopped red at input set 3 (92 disagreements).
//!
//! **What the kernel does.**  Its replay draws an open block's pieces as the complement of its idle spans (every
//! pause and interruption, nonempty) and the breaks held on its ledger days, from its start (`Replay.settle`,
//! `Replay.cutPieces`) — so a mark logged after the stretch it lies in was closed is netted where it lies, and an empty
//! stop (a pause and its unpause at one instant) leaves one piece.  It holds the blocks it closed (`Replay.Machine.closed`,
//! within 31 ledger days of the newest held, `Replay.pruneClosed`) and, at every `break` it steps, cuts each held block
//! it meets on a ledger day not before the block's (`Replay.netOne`): what that takes — the pieces' whole minutes before
//! less after, per piece (site R8), never more than the credit still standing — comes off the block's credit, its
//! item's minutes and its `done`'s duration observation.  Fork 4748911 drew and credited each stretch when its clock
//! stopped, split a stretch at every stop, and touched no block for a `break`.
//!
//! **The rule: the fork is ASKED the log the kernel reads**, as P81's and P85's arms ask it — never carried by a
//! model of the fork's answer.  [`nets`] walks the log in file order over the undo mask's survivors and the fork's
//! own refusals, two ways at once: the pieces fork 4748911's clock draws in the asked log (P81's and P85's marks
//! included), each with the line that closed it, and the pieces the kernel's machine draws.  At each block's close,
//! every part of a fork piece the kernel does not draw is a `pause` and an `unpause` placed before the line that
//! closed that piece (P104), every fork boundary inside one kernel piece is a merge the answer is read with (P104's
//! empty stop), and a part the kernel draws the fork does not is a finding.  At each `break`, every held closed block
//! it nets gets a pair before the line that closed the piece it lies in, and a `done`'s `actual_min` is lowered by what
//! it took (P105) — a `done`'s credit and duration observation are its logged minutes, not the clock's.  The ledger
//! days are read off the fork's own wakes.  [`as_asked_answer`] reads the answer back as the answer to the log as
//! given: every inserted pair's `Pause` taken off (the break's or the mark's own segment is the span, drawn alone),
//! each empty stop's two pieces merged (refused by name where the merge would move a whole minute), the entry count
//! less the lines inserted and refused lines renumbered.
//!
//! **This is the kernel's block machine read in Rust, as `p81::clock_read` is** (the campaign's lesson 5 says so out
//! loud): the PIECES are the model's, and everything the fork computes from them — credits, the day's minutes by ci,
//! the load, the fit's observations, the segments' days — is the fork's own answer.  A kernel that drew other pieces
//! than this model fails by name, and so does a model that drew pieces the fork's clock, paused, cannot.

use chrono::{DateTime, FixedOffset, NaiveDate};
use serde_json::{Map, Value};

/// One `pause`/`unpause` pair given to the fork for a break D100 nets: the block, the original line it is placed
/// before (the line that closed the piece the break lies in), and the span `[at, until)` it pauses.
#[derive(Clone, Debug, PartialEq)]
pub struct Pair {
    pub id: String,
    pub before: u64,
    pub at: DateTime<FixedOffset>,
    pub at_text: String,
    pub until: DateTime<FixedOffset>,
}

/// A `done` line whose `actual_min` the fork is given lowered by what D100's breaks took from its block.
#[derive(Clone, Debug, PartialEq)]
pub struct Lower {
    pub line: u64,
    pub by: u64,
}

/// What [`nets`] read off a log.
#[derive(Clone, Debug, Default, PartialEq)]
pub struct Nets {
    pub pairs: Vec<Pair>,
    pub lowers: Vec<Lower>,
    /// Breaks that netted a held closed block (each a sighting of P105).
    pub breaks: usize,
    /// Fork boundaries the kernel draws one piece across, `(id, x, t, y)`: the answer's `[x, t]` and `[t, y]` merged.
    pub merges: Vec<(String, DateTime<FixedOffset>, DateTime<FixedOffset>, DateTime<FixedOffset>)>,
    /// Pairs and merges D99 gave the fork (each a sighting of P104).
    pub p104: usize,
}

fn stamp(s: &str) -> Option<DateTime<FixedOffset>> {
    DateTime::parse_from_rfc3339(s).ok().or_else(|| DateTime::parse_from_str(s, "%Y-%m-%dT%H:%M%:z").ok())
}

fn at(v: &Value) -> Option<DateTime<FixedOffset>> {
    v.as_str().and_then(|s| DateTime::parse_from_rfc3339(s).ok())
}

/// Whole minutes from `a` to `b`, truncated and at least 0 — site R8, per piece.
fn mins(a: DateTime<FixedOffset>, b: DateTime<FixedOffset>) -> u64 {
    (b - a).num_seconds().max(0) as u64 / 60
}

/// The ledger day the replay files an instant under — the latest day whose wake is at or before it, within a day;
/// else its own local date (`p81.rs`' rule, off the fork's own wakes).
fn day_of(days: &Map<String, Value>, t: DateTime<FixedOffset>) -> NaiveDate {
    let mut best: Option<(DateTime<FixedOffset>, String)> = None;
    for (d, day) in days {
        let Some(w) = at(&day["wake"]) else { continue };
        if w <= t && (t - w).num_seconds() < 86_400 && best.as_ref().is_none_or(|(b, _)| w > *b) {
            best = Some((w, d.clone()));
        }
    }
    best.and_then(|(_, d)| NaiveDate::parse_from_str(&d, "%Y-%m-%d").ok()).unwrap_or_else(|| t.date_naive())
}

/// A piece a block's clock drew: `[x, y)` and the original line that closed it.
#[derive(Clone, Debug)]
struct Piece {
    x: DateTime<FixedOffset>,
    y: DateTime<FixedOffset>,
    close: u64,
}

type Span = (DateTime<FixedOffset>, DateTime<FixedOffset>);

/// **`Replay.pieces`**: the complement of the NONEMPTY spans in `[a, b)` — maximal, nonempty.
fn complement(spans: &[Span], a: DateTime<FixedOffset>, b: DateTime<FixedOffset>) -> Vec<Span> {
    let mut h: Vec<Span> = spans.iter().filter(|(s, e)| s < e && *s < b && a < *e).map(|(s, e)| ((*s).max(a), (*e).min(b))).collect();
    h.sort();
    let mut out = Vec::new();
    let mut x = a;
    for (s, e) in h {
        if x < s {
            out.push((x, s));
        }
        if x < e {
            x = e;
        }
    }
    if x < b {
        out.push((x, b));
    }
    out
}

/// The open block, two ways: as fork 4748911 draws it in the asked log (`drawn`, each piece with the line that closed
/// it — P81's and P85's marks included, which the asked log carries), and what the kernel's machine holds to draw it
/// (`Replay.Block`: its start, its idle spans, its open pause).
#[derive(Clone, Debug)]
struct Open {
    id: String,
    day: NaiveDate,
    started: DateTime<FixedOffset>,
    drawn: Vec<Piece>,
    since: Option<DateTime<FixedOffset>>,
    paused: bool,
    pause_from: Option<DateTime<FixedOffset>>,
    idle: Vec<Span>,
}

/// A closed block the machine holds (`Replay.Closed`): its id, its ledger day, its pieces as the kernel drew them
/// (each with the line that closed the fork's piece holding it), its credit still standing, and the `done` line whose
/// duration observation carries it.
#[derive(Clone, Debug)]
struct Closed {
    id: String,
    day: NaiveDate,
    pieces: Vec<Piece>,
    credit: u64,
    done_line: Option<u64>,
}

/// `Replay.pruneClosed`: the head, and every other within 31 ledger days of the newest held.
fn prune(l: Vec<Closed>) -> Vec<Closed> {
    let Some(hi) = l.iter().map(|c| c.day).max() else { return l };
    let mut out = Vec::new();
    for (k, c) in l.into_iter().enumerate() {
        if k == 0 || (hi - c.day).num_days() <= 31 {
            out.push(c);
        }
    }
    out
}

/// `Replay.pruneBrks`: the held breaks within 31 ledger days of the newest held.
fn prune_brks(l: &mut Vec<(Span, NaiveDate)>) {
    if let Some(hi) = l.iter().map(|(_, d)| *d).max() {
        l.retain(|(_, d)| (hi - *d).num_days() <= 31);
    }
}

/// One survivor of the undo mask that moves a block's clock, or a `break`.
struct Entry {
    line: u64,
    tag: String,
    id: Option<String>,
    t: DateTime<FixedOffset>,
    t_text: String,
    minutes: i64,
    actual: Option<u64>,
}

/// A text for an instant: the log's own spelling where it is a line's stamp, else chrono's.
fn text_of(t: DateTime<FixedOffset>, line_t: DateTime<FixedOffset>, line_text: &str) -> String {
    if t == line_t {
        line_text.to_string()
    } else {
        serde_json::to_value(t).expect("an instant").as_str().unwrap_or_default().to_string()
    }
}

/// **The kernel's pieces against the fork's, at a block's close** (the owner's D99): every part of a piece the fork
/// drew that the kernel does not draw is given to the fork as a pair before the line that closed that piece; every
/// boundary the fork drew where the kernel draws one piece across it (an empty stop) is a merge the answer is read
/// with; and a part the kernel draws that the fork does not is a finding.  The kernel's pieces, each carrying the
/// closing line of the fork's piece holding its start, are returned.
fn reconcile(id: &str, drawn: &[Piece], kernel: &[Span], out: &mut Nets) -> Result<Vec<Piece>, String> {
    let mut kept: Vec<Piece> = Vec::new();
    for p in drawn {
        // The kernel's parts inside this piece that no earlier piece of the fork already holds: a stretch the fork's
        // clock restarted before a stretch it had closed (a `resume` stamped behind a later `pause`) drew one span
        // twice, and the kernel draws it once.
        let held: Vec<Span> = kept.iter().map(|k| (k.x, k.y)).collect();
        let inside: Vec<Span> = kernel
            .iter()
            .filter(|(a, b)| *a < p.y && p.x < *b)
            .flat_map(|(a, b)| complement(&held, (*a).max(p.x), (*b).min(p.y)))
            .collect();
        // The fork's piece less the kernel's: each gap a pause and an unpause before the piece's closing line.
        for (a, b) in complement(&inside, p.x, p.y) {
            out.pairs.push(Pair { id: id.to_string(), before: p.close, at: a, at_text: serde_json::to_value(a).expect("an instant").as_str().unwrap_or_default().to_string(), until: b });
            out.p104 += 1;
        }
        for (a, b) in inside {
            kept.push(Piece { x: a, y: b, close: p.close });
        }
    }
    // The kernel's pieces must be covered by the fork's; where two fork pieces meet inside one of the kernel's, merge.
    kept.sort_by_key(|p| p.x);
    let mut merged: Vec<Piece> = Vec::new();
    for k in kept {
        match merged.last_mut() {
            Some(m) if m.y == k.x && kernel.iter().any(|(a, b)| *a <= m.x && k.y <= *b) => {
                out.merges.push((id.to_string(), m.x, m.y, k.y));
                out.p104 += 1;
                m.y = k.y;
            }
            _ => merged.push(k),
        }
    }
    let got: Vec<Span> = merged.iter().map(|p| (p.x, p.y)).collect();
    if got != kernel {
        return Err(format!("P104: the kernel draws `{id}` as {kernel:?} where the fork's pieces, paused, can draw only {got:?}"));
    }
    Ok(merged)
}

/// **The breaks and late marks D99 and D100 move in a log, by the kernel's block machine** — read off the log, the
/// fork's own refusals (`refused`) and the fork's own answer's wakes (`answer`, for the ledger days), never the
/// kernel's answer.
pub fn nets(text: &str, refused: &[u64], answer: &Value) -> Result<Nets, String> {
    let empty = Map::new();
    let days = answer["replay"]["days"].as_object().unwrap_or(&empty);
    const TAGS: [&str; 8] = ["start", "pause", "unpause", "interrupt", "resume", "stop", "done", "break"];
    let mut stack: Vec<Entry> = Vec::new();
    for (i, raw) in text.split('\n').enumerate() {
        let line = i as u64 + 1;
        if raw.trim().is_empty() || refused.contains(&line) {
            continue;
        }
        let e: Value = serde_json::from_str(raw).map_err(|err| format!("P105: line {line} is not JSON the fork accepted: {err}"))?;
        let tag = e["ev"].as_str().unwrap_or_default().to_string();
        if tag == "undo" {
            let of = e["of"].as_str().unwrap_or_default();
            let id = e["id"].as_str();
            if let Some(k) = stack.iter().rposition(|c| c.tag == of && id.is_none_or(|x| c.id.as_deref() == Some(x))) {
                stack.remove(k);
            }
            continue;
        }
        if !TAGS.contains(&tag.as_str()) {
            continue;
        }
        let t_text = e["t"].as_str().unwrap_or_default().to_string();
        let t = stamp(&t_text).ok_or_else(|| format!("P105: line {line}'s stamp `{t_text}` does not read"))?;
        let minutes = e["actual_min"].as_i64().or_else(|| e["planned_min"].as_i64()).unwrap_or(0);
        stack.push(Entry { line, tag, id: e["id"].as_str().map(str::to_string), t, t_text, minutes, actual: e["actual_min"].as_u64() });
    }

    let mut out = Nets::default();
    let mut block: Option<Open> = None;
    // The open interruption's start (the machine's, whatever block it began beside).
    let mut interrupt: Option<DateTime<FixedOffset>> = None;
    let mut last: Option<Span> = None;
    let mut brks: Vec<(Span, NaiveDate)> = Vec::new();
    let mut closed: Vec<Closed> = Vec::new();
    let mut last_cut: Option<String> = None;
    // Replay.restartAt (deleted at D99; the fork-asked clock keeps its rule): the end of the last break when it began at or before `t` and ends after it.
    let restart = |last: &Option<Span>, t: DateTime<FixedOffset>| last.filter(|(s, e)| *s <= t && t < *e).map(|(_, e)| e).unwrap_or(t);
    // The fork's running stretch closed at `t` by `line`.
    let close_drawn = |b: &mut Open, t: DateTime<FixedOffset>, line: u64| {
        if let Some(x) = b.since.take() {
            if x < t {
                b.drawn.push(Piece { x, y: t, close: line });
            }
        }
    };
    // The kernel's pieces of the block closed at `t` (`Replay.cutPieces`): the complement of its idle spans and the
    // held breaks on its ledger days, from its start to `t` or its open stop, whichever is earlier.
    let kernel_pieces = |b: &Open, brks: &[(Span, NaiveDate)], interrupt: Option<DateTime<FixedOffset>>, t: DateTime<FixedOffset>| {
        let mut spans = b.idle.clone();
        spans.extend(brks.iter().filter(|(_, d)| b.day <= *d).map(|(sp, _)| *sp));
        let stop = [if b.paused { b.pause_from } else { None }, interrupt].into_iter().flatten().min();
        complement(&spans, b.started, stop.map_or(t, |q| q.min(t)))
    };
    for c in &stack {
        match c.tag.as_str() {
            "start" => {
                // A start cuts any open block, even one of the same id: the cut's credit is its pieces' minutes.
                if let Some(mut b) = block.take() {
                    close_drawn(&mut b, c.t, c.line);
                    let k = kernel_pieces(&b, &brks, interrupt, c.t);
                    let pieces = reconcile(&b.id, &b.drawn, &k, &mut out)?;
                    let credit = pieces.iter().map(|p| mins(p.x, p.y)).sum();
                    closed.insert(0, Closed { id: b.id.clone(), day: b.day, pieces, credit, done_line: None });
                    closed = prune(closed);
                }
                let id = c.id.clone().unwrap_or_default();
                let since = if interrupt.is_some() { None } else { Some(restart(&last, c.t)) };
                block = Some(Open { id, day: day_of(days, c.t), started: c.t, drawn: Vec::new(), since, paused: false, pause_from: None, idle: Vec::new() });
                last_cut = None;
            }
            "pause" => {
                if let Some(b) = block.as_mut().filter(|b| Some(b.id.as_str()) == c.id.as_deref() && !b.paused) {
                    close_drawn(b, c.t, c.line);
                    b.paused = true;
                    b.pause_from = Some(c.t);
                }
            }
            "unpause" => {
                if let Some(b) = block.as_mut().filter(|b| Some(b.id.as_str()) == c.id.as_deref() && b.paused) {
                    b.paused = false;
                    if let Some(p) = b.pause_from.take() {
                        if p < c.t {
                            b.idle.push((p, c.t));
                        }
                    }
                    if interrupt.is_none() {
                        b.since = Some(restart(&last, c.t));
                    }
                }
            }
            "interrupt" => {
                if let Some(b) = block.as_mut() {
                    close_drawn(b, c.t, c.line);
                    if let Some(p) = b.pause_from.take() {
                        if p < c.t {
                            b.idle.push((p, c.t));
                        }
                    }
                }
                if interrupt.is_none() {
                    interrupt = Some(c.t);
                }
            }
            "resume" => {
                let span = interrupt.take().map(|s| (s, c.t));
                if let Some(b) = block.as_mut() {
                    if let Some((s, e)) = span {
                        if s < e {
                            b.idle.push((s, e));
                        }
                    }
                    if b.paused {
                        b.pause_from = b.pause_from.or(Some(c.t));
                    } else if b.since.is_none() {
                        b.since = Some(restart(&last, c.t));
                    }
                }
            }
            "stop" => {
                if block.as_ref().is_some_and(|b| Some(b.id.as_str()) == c.id.as_deref()) {
                    let mut b = block.take().expect("checked");
                    close_drawn(&mut b, c.t, c.line);
                    let k = kernel_pieces(&b, &brks, interrupt, c.t);
                    let pieces = reconcile(&b.id, &b.drawn, &k, &mut out)?;
                    let credit = pieces.iter().map(|p| mins(p.x, p.y)).sum();
                    last_cut = Some(b.id.clone());
                    closed.insert(0, Closed { id: b.id, day: b.day, pieces, credit, done_line: None });
                    closed = prune(closed);
                }
            }
            "done" => {
                let actual = c.actual.unwrap_or(0);
                if block.as_ref().is_some_and(|b| Some(b.id.as_str()) == c.id.as_deref()) {
                    let mut b = block.take().expect("checked");
                    close_drawn(&mut b, c.t, c.line);
                    let k = kernel_pieces(&b, &brks, interrupt, c.t);
                    let pieces = reconcile(&b.id, &b.drawn, &k, &mut out)?;
                    last_cut = None;
                    closed.insert(0, Closed { id: b.id, day: b.day, pieces, credit: actual, done_line: (actual > 0).then_some(c.line) });
                    closed = prune(closed);
                } else if block.is_none() && actual > 0 && last_cut.is_some() && last_cut.as_deref() == c.id.as_deref() {
                    // The stop-then-done replacement: the last cut's block carries the done's credit.
                    if let Some(h) = closed.first_mut() {
                        h.credit = actual;
                        h.done_line = Some(c.line);
                    }
                    last_cut = None;
                }
            }
            "break" => {
                let (s, e) = (c.t, c.t + chrono::Duration::minutes(c.minutes));
                let d = day_of(days, s);
                brks.insert(0, ((s, e), d));
                prune_brks(&mut brks);
                // P81: the fork, asked, closes the running stretch at the break and restarts it at its end.
                if let Some(b) = block.as_mut() {
                    if let Some(x) = b.since {
                        if x < s {
                            b.drawn.push(Piece { x, y: s, close: c.line });
                        }
                        b.since = Some(if x < e { e } else { x });
                    }
                }
                // D100: every held closed block the break meets, on a ledger day not before the block's.
                let mut netted = false;
                for k in closed.iter_mut() {
                    if d < k.day || k.pieces.iter().all(|p| p.y <= s || e <= p.x) {
                        continue;
                    }
                    let before: u64 = k.pieces.iter().map(|p| mins(p.x, p.y)).sum();
                    let mut cut: Vec<Piece> = Vec::new();
                    for p in &k.pieces {
                        let (a, z) = (s.max(p.x), e.min(p.y));
                        if a < z {
                            out.pairs.push(Pair { id: k.id.clone(), before: p.close, at: a, at_text: text_of(a, s, &c.t_text), until: z });
                            if p.x < a {
                                cut.push(Piece { x: p.x, y: a, close: p.close });
                            }
                            if z < p.y {
                                cut.push(Piece { x: z, y: p.y, close: p.close });
                            }
                        } else {
                            cut.push(p.clone());
                        }
                    }
                    let after: u64 = cut.iter().map(|p| mins(p.x, p.y)).sum();
                    let net = (before - after).min(k.credit);
                    k.pieces = cut;
                    k.credit -= net;
                    if net > 0 {
                        if let Some(l) = k.done_line {
                            match out.lowers.iter_mut().find(|w| w.line == l) {
                                Some(w) => w.by += net,
                                None => out.lowers.push(Lower { line: l, by: net }),
                            }
                        }
                    }
                    netted = true;
                }
                if netted {
                    out.breaks += 1;
                }
                last = Some((s, e));
            }
            _ => {}
        }
    }
    Ok(out)
}

/// **The log fork 4748911 is asked P81's, P85's and P105's day in**: P81's and P85's insertions as
/// `p85::as_asked_log` makes them, and before each line a P105 pair closes a piece at, that pair's `pause` and
/// `unpause` (in stamp order), with each `done` [`Lower`] names given its `actual_min` less what D100 took.  The lines
/// inserted, 1-based in the new log.  **Refused by name: an `undo` that would take an inserted line back.**
pub fn as_asked_log(
    text: &str,
    n81: &[super::p81::Netted],
    r85: &[super::p85::Restart],
    n105: &Nets,
) -> Result<(String, Vec<u64>), String> {
    let mut out: Vec<String> = Vec::new();
    let mut inserted = Vec::new();
    for (i, raw) in text.split('\n').enumerate() {
        let line = i as u64 + 1;
        let mut mine: Vec<&Pair> = n105.pairs.iter().filter(|p| p.before == line).collect();
        mine.sort_by_key(|p| p.at);
        for p in mine {
            out.push(serde_json::json!({"t": p.at_text, "ev": "pause", "id": p.id}).to_string());
            inserted.push(out.len() as u64);
            out.push(serde_json::json!({"t": serde_json::to_value(p.until).expect("an instant"), "ev": "unpause", "id": p.id}).to_string());
            inserted.push(out.len() as u64);
        }
        let raw = match n105.lowers.iter().find(|w| w.line == line) {
            Some(w) => {
                let mut e: Value = serde_json::from_str(raw).map_err(|err| format!("P105: line {line}: {err}"))?;
                let a = e["actual_min"].as_u64().ok_or_else(|| format!("P105: line {line} carries no actual_min"))?;
                // The field is rewritten in place, so the line keeps its keys' order (serde_json's preserve_order feature
                // is off: a `Value` would re-sort them, which the fork reads the same either way).
                let lowered = a.saturating_sub(w.by);
                e["actual_min"] = Value::from(lowered);
                let needle = format!("\"actual_min\":{a}");
                if raw.contains(&needle) {
                    raw.replacen(&needle, &format!("\"actual_min\":{lowered}"), 1)
                } else {
                    e.to_string()
                }
            }
            None => raw.to_string(),
        };
        if let Some(n) = n81.iter().find(|n| n.line == line) {
            out.push(serde_json::json!({"t": n.at_text, "ev": "pause", "id": n.id}).to_string());
            inserted.push(out.len() as u64);
            out.push(raw);
            let r = serde_json::to_value(n.restart).expect("an instant serialises");
            out.push(serde_json::json!({"t": r, "ev": "unpause", "id": n.id}).to_string());
            inserted.push(out.len() as u64);
        } else if let Some(r) = r85.iter().find(|r| r.line == line) {
            out.push(raw);
            out.push(serde_json::json!({"t": r.at_text, "ev": "pause", "id": r.id}).to_string());
            inserted.push(out.len() as u64);
            let e = serde_json::to_value(r.restart).expect("an instant serialises");
            out.push(serde_json::json!({"t": e, "ev": "unpause", "id": r.id}).to_string());
            inserted.push(out.len() as u64);
        } else {
            out.push(raw);
        }
    }
    let mut stack: Vec<(u64, String, Option<String>)> = Vec::new();
    for (i, raw) in out.iter().enumerate() {
        let Ok(e) = serde_json::from_str::<Value>(raw) else { continue };
        let tag = e["ev"].as_str().unwrap_or_default();
        match tag {
            "undo" => {
                let of = e["of"].as_str().unwrap_or_default();
                let id = e["id"].as_str();
                if let Some(k) = stack.iter().rposition(|c| c.1 == of && id.is_none_or(|x| c.2.as_deref() == Some(x))) {
                    if inserted.contains(&stack[k].0) {
                        return Err(format!("P105: an undo at line {} of the asked log would take back the {of} inserted at line {}", i + 1, stack[k].0));
                    }
                    stack.remove(k);
                }
            }
            "pause" | "unpause" => stack.push((i as u64 + 1, tag.to_string(), e["id"].as_str().map(str::to_string))),
            _ => {}
        }
    }
    Ok((out.join("\n"), inserted))
}

/// **The fork's answer to that log, read as its answer to the log as given**: `p85::as_asked_answer`'s reading, the
/// `Pause` each P104 and P105 pair drew taken off, and each D99 empty stop's two pieces merged into the kernel's one.
pub fn as_asked_answer(
    answer: &Value,
    n81: &[super::p81::Netted],
    r85: &[super::p85::Restart],
    n105: &Nets,
    inserted: &[u64],
) -> Result<Value, String> {
    let mut a = super::p85::as_asked_answer(answer, n81, r85, inserted)?;
    let days = a["replay"]["days"].as_object_mut().ok_or("P105: the asked answer has no days")?;
    for p in n105.pairs.iter().filter(|p| p.at < p.until) {
        let mut hit = false;
        for day in days.values_mut() {
            if let Some(segs) = day["segments"].as_array_mut() {
                let before = segs.len();
                segs.retain(|g| {
                    !(g["kind"]["Pause"]["id"] == p.id.as_str() && at(&g["start"]) == Some(p.at) && at(&g["end"]) == Some(p.until))
                });
                hit |= segs.len() < before;
            }
        }
        if !hit {
            return Err(format!("P105: the fork drew no Pause for the pair inserted for `{}` at {}", p.id, p.at));
        }
    }
    // D99's empty stops: the fork's `[x, t]` and `[t, y]` are the kernel's one piece `[x, y]` — and only where the
    // fork's per-piece whole minutes are the one piece's (site R8), or the merge would move a minute this cannot carry.
    for (id, x, t, y) in &n105.merges {
        if mins(*x, *t) + mins(*t, *y) != mins(*x, *y) {
            return Err(format!("P104: the empty stop of `{id}` at {t} splits a minute ({x} to {y}): the fork's minutes are not the kernel's"));
        }
        let mut done = false;
        for day in days.values_mut() {
            let Some(segs) = day["segments"].as_array_mut() else { continue };
            let is = |g: &Value, a: DateTime<FixedOffset>, b: DateTime<FixedOffset>| {
                g["kind"]["Block"]["id"] == id.as_str() && at(&g["start"]) == Some(a) && at(&g["end"]) == Some(b)
            };
            if let (Some(i), Some(j)) = (segs.iter().position(|g| is(g, *x, *t)), segs.iter().position(|g| is(g, *t, *y))) {
                segs[i]["end"] = segs[j]["end"].clone();
                segs.remove(j);
                done = true;
                break;
            }
        }
        if !done {
            return Err(format!("P104: the fork drew no pieces `{id}` [{x}, {t}] and [{t}, {y}] on one day to merge"));
        }
    }
    Ok(a)
}
