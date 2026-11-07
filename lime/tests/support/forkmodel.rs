//! **How fork 4748911 reads a learned model, as the oracle names it** (stage 6 W-47 track C;
//! README gap 4891). One definition, for the two harnesses that ask the oracle about a model:
//! `support/forkplan.rs` (`tm-oracle plan`, a world carrying `.tm/model.json`) and
//! `support/forkcap.rs` (`tm-oracle capacity`'s `today` and `lookahead`, whose model crosses as
//! `.tm/model.json`'s text since W-47).
//!
//! Until W-47 the oracle read no model file at all: `plan` planned every world at
//! `Model::default()` but for one table (the class worlds' `_default` duration multiplier), and
//! `capacity` read three tables by hand (cap_model, deleted at W-47: a `NaiveTime` parse standing in for the fork's
//! `Hhmm`, a `str::parse` for each weight). Both now read the text through `fork_model` — fork
//! `Ctx::load`'s own expression, `store.read_json::<Model>(MODEL_PATH)?.unwrap_or_default()`, over
//! the fork's own memory store — and every answer that read one says so. An oracle built before
//! W-47 would answer a request carrying the text as if no model were written — silently, the
//! freshness hazard of README gap 196 — so each harness refuses an answer that does not name
//! [`MODEL_READ_BY`], by name.

/// **The fork's loader of `.tm/model.json`, as the oracle's answers name it** (`tm-oracle`'s own
/// `MODEL_READ_BY`, which this must equal: the two sides of one wire).
pub const MODEL_READ_BY: &str = "store::StoreExt::read_json::<energy::Model>(MODEL_PATH)";
