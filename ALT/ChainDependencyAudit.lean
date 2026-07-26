/-
Copyright (c) 2026 Mykola Palamarchuk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mykola Palamarchuk
-/
import Mathlib.Tactic.Linter.Header

-- Formal-check file, not Mathlib-destined: opt out of the house-style header linter.
set_option linter.style.header false

/-!
# Reflection-chain dependency audit (structural DAG check)

A machine-checked audit of which imports the corpus's reflection chain actually consumes: which
named edges compose into which conclusions, and — via unused-binder marking — which edges a
given conclusion demonstrably does NOT need. "Off the critical path" is then a property the
compiler checks (a proof that never references a hypothesis cannot depend on it), not a claim
asserted in prose.

The chain assembles five named edges — [Discovery] Prop 3.2 + Prop 3.3 (discovery), [Discovery]
Proposition 4.2 (retention), [SQ] Theorem 4.1 (tractability), [Decoupling] Theorem 6.2 (the Gödel
threshold), and [SQ] Corollary 4.4 (the steady-state bound) — over two structural premises: a
decoupled substrate (`Decoupled`) and the capacity regime (`Regime`, [Decoupling] Theorem 6.2's
`r ≪ K_max` condition).

Status: PROVED as pure propositional logic. This is a STRUCTURAL check of the dependency DAG only.

## What this DOES establish
* `chain_complete`: all five edges compose into the three terminal claims (reflection, retention,
  tractability) with no missing link — the proof uses EVERY hypothesis, so a clean build certifies
  the assembly has no gap.
* `reflection_off_sq_and_retention`: bare reflection follows from discovery + the threshold edge
  ALONE. `_hRetention`, `_hTractability`, and `_sq` are `_`-marked — the proof never references
  them, so the compiler certifies SQ-learnability, the tractability edge, and the retention edge
  are OFF the critical path to reflection: they sharpen the bound to polynomial time and give
  persistence, but reflection itself does not depend on them.
* `steady_state_on_retention_off_sq`: the steady-state per-step bound follows WITHOUT the
  tractability edge and WITHOUT SQ-learnability (`_hTractability`, `_sq` unused, exactly as above).
  It DOES consume retention, and must — the bound is a claim about the prediction phase, and a
  prediction phase presupposes that the committed rule STAYS put; strike retention and there is no
  prediction phase at all, only a search cost again. `_hThreshold` and `_reg` are also unused, so
  the bare per-step cost needs no capacity regime — but that mark must NOT be read as "the
  quantitative resource bound is regime-free": the `O(poly(r))` sharpening of [SQ] Cor 4.4(i)
  quantifies over the rule's description length, exactly `Regime`'s parameter, and it is not this
  node.

## What this does NOT establish (purely structural; no content)
* It proves NO import — all are abstract `Prop`s. Zero content: not the Decoupling Lemma, not the
  [Discovery] / [SQ] bounds, not the categorical threshold of [Decoupling] Thm 6.2.
* It does not validate that the corpus's informal edges are the right ones to draw — only that,
  taken as stated, they compose into the conclusions.
* The `Prop` implications are the papers' claimed entailments asserted as hypotheses; their truth
  lives in the cited companion papers, untouched here.
-/

-- "It proves NO import — all are abstract `Prop`s … not the Decoupling Lemma, not the
-- [Discovery] / [SQ] bounds, not the categorical threshold of [Decoupling] Thm 6.2." One witness
-- per territory the docstring disclaims.
assert_not_exists Decoupling.decoupling_iff_persists_all
assert_not_exists SampleComplexity.sample_complexity_r2
assert_not_exists SQEnvelope.version_space_card_le
assert_not_exists CategoricalThreshold.categorical_threshold

namespace ChainDependencyAudit

variable
  (Decoupled Regime Realizable SQLearnable : Prop)
  (EncodedRule RuleRetained PolyTimeCompute Reflective SteadyStateBounded : Prop)

/-- All five named edges compose into the three terminal claims with no missing link: the proof
uses EVERY hypothesis, so a clean build certifies the assembly has no gap. -/
theorem chain_complete
    (hDiscovery : Realizable → Decoupled → EncodedRule) -- [Discovery] Prop 3.2 + Prop 3.3
    (hRetention : Decoupled → EncodedRule → RuleRetained) -- [Discovery] Proposition 4.2
    (hTractability : SQLearnable → EncodedRule → PolyTimeCompute) -- [SQ] Theorem 4.1
    (hThreshold : Regime → EncodedRule → Reflective) -- [Decoupling] Theorem 6.2
    (dec : Decoupled) (reg : Regime) (real : Realizable) (sq : SQLearnable) :
    Reflective ∧ RuleRetained ∧ PolyTimeCompute := by
  have encoded : EncodedRule := hDiscovery real dec
  exact ⟨hThreshold reg encoded, hRetention dec encoded, hTractability sq encoded⟩

/-- Bare reflection follows from discovery + the threshold edge ALONE. `_hRetention`,
`_hTractability`, and `_sq` are `_`-marked — the proof never references them, so the compiler
certifies SQ-learnability, the tractability edge, and the retention edge are OFF the critical path
to reflection. -/
theorem reflection_off_sq_and_retention
    (hDiscovery : Realizable → Decoupled → EncodedRule)
    (_hRetention : Decoupled → EncodedRule → RuleRetained) -- off critical path
    (_hTractability : SQLearnable → EncodedRule → PolyTimeCompute) -- off critical path
    (hThreshold : Regime → EncodedRule → Reflective)
    (dec : Decoupled) (reg : Regime) (real : Realizable) (_sq : SQLearnable) : -- SQLearnable unused
    Reflective :=
  hThreshold reg (hDiscovery real dec)

/-- The **steady-state resource bound** ([SQ] Cor 4.4): follows WITHOUT the tractability edge and
WITHOUT SQ-learnability (`_hTractability`, `_sq` unused, as in `reflection_off_sq_and_retention`).

The edge CONSUMES RETENTION, and must: the bound is a claim about the prediction phase, which
presupposes the committed rule STAYS put. Strike retention and there is no prediction phase at
all — the subsystem re-enters search and its per-step cost is a search cost again. So `hRetention`
is on this path, not off it.

`_hThreshold` and `_reg` are also unused, so the bare per-step cost needs no capacity regime — but
that mark must NOT be read as "the quantitative resource bound is regime-free": the `O(poly(r))`
sharpening of [SQ] Cor 4.4(i) quantifies over the rule's description length, exactly `Regime`'s
parameter, and it is not this node. -/
theorem steady_state_on_retention_off_sq
    (hDiscovery : Realizable → Decoupled → EncodedRule)
    (hRetention : Decoupled → EncodedRule → RuleRetained) -- [Discovery] Proposition 4.2
    (hSteadyState : Decoupled → RuleRetained → SteadyStateBounded) -- [SQ] Corollary 4.4
    (_hTractability : SQLearnable → EncodedRule → PolyTimeCompute) -- off critical path
    (_hThreshold : Regime → EncodedRule → Reflective) -- off critical path
    (dec : Decoupled) (_reg : Regime) (real : Realizable)
    (_sq : SQLearnable) : -- SQLearnable unused
    SteadyStateBounded :=
  let encoded : EncodedRule := hDiscovery real dec
  hSteadyState dec (hRetention dec encoded)

end ChainDependencyAudit
