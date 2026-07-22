/-
Copyright (c) 2026 Mykola Palamarchuk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mykola Palamarchuk
-/
import Mathlib

-- Formal-check file, not Mathlib-destined: opt out of the house-style header linter.
set_option linter.style.header false

/-!
# [Inevitability] proof-chain skeleton (§6 Main Theorem + Appendix table)

Provenance: [Inevitability], §2 (axioms A1–A5),
§3 (physical lemmas L1–L5), §4 ([Discovery] import: discovery), §5 ([SQ] import: tractability),
§6 (Theorem 6.1 + its proof), and the Appendix ("The Proof Chain in One Table"), the source of
truth for the dependency edges.

Status: PROVED as pure propositional logic. This is a STRUCTURAL check of the dependency DAG only.

## What this DOES establish
* `inevitability_full`: the §6 assembly is logically connected with no missing link — every node's
  antecedents are discharged from exactly the stated axioms + lemma/import edges. The proof uses
  EVERY hypothesis, so a clean build certifies there is no gap in the chain as the paper states it.
* `reflective_core`: bare representational reflection ([Decoupling] Def 6.1) follows from A1–A5 +
  realizability + the physical/[Decoupling]/[Discovery] edges ALONE. The [SQ] tractability edge, the
  SQ-learnability premise, and the retention edge are `_`-marked: the proof literally cannot
  reference them, so the compiler certifies they are OFF the critical path: they sharpen the bound
  to polynomial time and give persistence, but bare representational reflection does not depend on
  them (exactly §5 / caveat 1).
* `steady_state_bounded`: the *steady-state* per-step resource bound ([SQ] Cor 4.4 — in the
  prediction phase no version space is maintained, so the per-step cost is one model-evaluation)
  follows WITHOUT the [SQ] tractability edge and WITHOUT the SQ-learnability premise
  (`_hTractability` and `_sq` `_`-marked, as in `reflective_core`). It does, however, CONSUME the
  retention edge — unlike `reflective_core`, which is off it — because a prediction phase exists
  only if the committed rule stays put. Together the two theorems certify that bare representational
  reflection AND the steady-state resource bound both sit off the SQ path ([Inevitability] §5,
  §6.2): SQ-learnability sharpens the SEARCH phase only.
* A5's independence is structural: `A5` occurs only as a free atomic premise feeding `hL4`; no
  hypothesis concludes `A5`, so "A5 not derivable from A1–A4" (caveat 2 / §9) is a checkable
  property of the encoding, not a comment.

## What this does NOT establish (purely structural; no content)
* It proves NO axiom, NO lemma (L1–L5), and NO import — all are abstract `Prop`s. Zero physical or
  mathematical content: not Jeans instability, not Kauffman–Mossel–Steel, not the Decoupling Lemma,
  not the [Discovery] / [SQ] bounds, not the categorical threshold of [Decoupling] Thm 6.2.
* It does not validate that the paper's informal edges are the right physics — only that, taken as
  stated, they compose into the conclusion.
* The `Prop` implications are the paper's claimed entailments asserted as hypotheses; their truth
  lives in the companion papers / physics, untouched here.

## Modeling notes (paper-stated vs added)
* All nodes and edges are paper-stated. The only ADDED structure: (a) threading L1's conclusion
  into `hL2` and L3's into `hL4` — faithful to the §3.2/§3.4 lemma statements ("exceeds the falling
  average"; "compacted regions with sustained energy flux") and §6's "these regions", though the
  appendix lists only the new axiom each lemma adds; (b) the conjunctive `inevitability_full`
  conclusion bundles the three terminal appendix rows (representational reflection, retention,
  tractability); (c) `SteadyStateBounded` is a separate terminal node, not folded into that bundle —
  Theorem 6.1 states three terminal claims, and the steady-state bound is proved on its own edge.
* The Discovery edge's premise list here — realizability alone — matches the paper's imports
  EXACTLY. §4 discharges the edge with [Discovery] Prop 3.2 (extensional [R]-concentration) and
  Prop 3.3 (the bounded-surprise event bound) ALONE. Those imports need only realizability (and a
  Kraft-summable prior, a fixture of the learner's setup rather than a chain premise): NO per-step
  separation, NO ergodic observability. This is a strengthening of the model, not a patch — the
  older route through a chronological discovery rate required a per-step separation hypothesis that
  is vacuous on a near-twin-rich physical class, where such a rate is in any case unavailable.
* [Decoupling] Prop 3.4 (the Relativized Decoupling Lemma) is cited by the paper, but for a
  different job, and it is NOT part of the Discovery edge. Its role is the phase/installation
  reading of its Remark (ii): taking `Ω` to be the forward orbit of the SUBSYSTEM'S OWN MEMORY
  states from some time `t₀` on, the read-only ⟺ model-persists equivalence governs each
  CODE-FROZEN STRETCH separately — the search phase writes, and every frozen stretch is governed.
  That is the learn-then-freeze licence. It says nothing about the learned model's correctness:
  [Decoupling]'s faithfulness condition constrains the DECODER'S INJECTIVITY (states decode alike
  exactly when they agree on the read-only region), never whether the decoded model is true of the
  environment. So Prop 3.4 is not a faithfulness bridge for the Discovery edge, and none is needed.
-/

namespace ProofChainSkeleton

variable
  -- §2 axioms A1–A5 (atomic, abstract)
  (A1 A2 A3 A4 A5 : Prop)
  -- §6 additional conditional premises
  (Realizable SQLearnable : Prop)
  -- conclusions of each lemma / import (abstract nodes)
  (DensityDilution GradientFormation CapacityConcentration
   CompositionalSubsystems CausalDecoupling EncodedRule
   RuleRetained PolyTimeCompute Reflective : Prop)
  -- `SteadyStateBounded`: in the PREDICTION phase the per-step cost is one model-evaluation, with
  -- no version space maintained (hence no maintainer hypothesis). This is the BARE cost claim, and
  -- only that. It is NOT the `O(poly(r))` sharpening of [SQ] Cor 4.4(i): that bound quantifies over
  -- the rule's description length `r`, which is A3's parameter, so reading it into this node would
  -- turn the `_a3` marking of `steady_state_bounded` below into a misclaim.
  (SteadyStateBounded : Prop)

/-- Full §6 chain. Every lemma/import edge is exercised, so a clean build certifies the assembly
has no missing link. The conclusion bundles the three terminal claims of Theorem 6.1 + appendix
(representational reflection, retention, polynomial-time tractability). -/
theorem inevitability_full
    (hL1 : A1 → A2 → DensityDilution) -- L1 §3.1 (from A1, A2)
    (hL2 : A4 → DensityDilution → GradientFormation) -- L2 §3.2 (A4; uses L1 "falling average")
    (hL3 : GradientFormation → CapacityConcentration) -- L3 §3.3 (from L2)
    (hL4 : CapacityConcentration → A5 → CompositionalSubsystems) -- L4 §3.4 (A5 + L3's regions)
    (hL5 : CompositionalSubsystems → CausalDecoupling) -- L5 §3.5 = [Decoupling] Lemma 3.1
    (hDiscovery : Realizable → CausalDecoupling → EncodedRule)
      -- [Discovery] Prop 3.2 + Prop 3.3 alone: realizability and a Kraft-summable prior suffice —
      -- no per-step separation, no ergodic observability
    (hRetention : CausalDecoupling → EncodedRule → RuleRetained) -- [Discovery] Proposition 4.2
    (hTractability : SQLearnable → EncodedRule → PolyTimeCompute) -- [SQ] Theorem 4.1
    (hThreshold : A3 → EncodedRule → Reflective) -- [Decoupling] Theorem 6.2 (A3 = regime r ≪ K_max)
    (a1 : A1) (a2 : A2) (a3 : A3) (a4 : A4) (a5 : A5)
    (real : Realizable) (sq : SQLearnable) :
    Reflective ∧ RuleRetained ∧ PolyTimeCompute := by
  have decoupled : CausalDecoupling := hL5 (hL4 (hL3 (hL2 a4 (hL1 a1 a2))) a5)
  have encoded : EncodedRule := hDiscovery real decoupled
  exact ⟨hThreshold a3 encoded, hRetention decoupled encoded, hTractability sq encoded⟩

/-- Bare representational reflection ([Decoupling] Def 6.1): follows from A1–A5 + realizability
+ the physical / [Decoupling] / [Discovery] edges ALONE. `_hRetention`, `_hTractability`, and
`_sq` are `_`-marked — the proof never references them, so the compiler certifies SQ-learnability,
the [SQ] tractability edge, and the retention edge are OFF the critical path. -/
theorem reflective_core
    (hL1 : A1 → A2 → DensityDilution)
    (hL2 : A4 → DensityDilution → GradientFormation)
    (hL3 : GradientFormation → CapacityConcentration)
    (hL4 : CapacityConcentration → A5 → CompositionalSubsystems)
    (hL5 : CompositionalSubsystems → CausalDecoupling)
    (hDiscovery : Realizable → CausalDecoupling → EncodedRule)
    (_hRetention : CausalDecoupling → EncodedRule → RuleRetained) -- off critical path
    (_hTractability : SQLearnable → EncodedRule → PolyTimeCompute) -- off critical path
    (hThreshold : A3 → EncodedRule → Reflective)
    (a1 : A1) (a2 : A2) (a3 : A3) (a4 : A4) (a5 : A5)
    (real : Realizable) (_sq : SQLearnable) : -- SQLearnable unused
    Reflective :=
  hThreshold a3 (hDiscovery real (hL5 (hL4 (hL3 (hL2 a4 (hL1 a1 a2))) a5)))

/-- The **steady-state resource bound** ([SQ] Cor 4.4): in the prediction phase the subsystem
maintains no version space, so its per-step cost is one model-evaluation.

The edge CONSUMES RETENTION ([Discovery] Prop 4.2), and must: the bound is a claim about the
prediction phase, which presupposes that the committed rule STAYS in the persistent code region.
Strike retention and there is no prediction phase at all — the subsystem re-enters search and its
per-step cost is a search cost again. So `hRetention` is on this path, not off it.

What the `_`-marks certify: `_hTractability` and `_sq` are unused, so neither the [SQ] tractability
edge nor SQ-learnability is on this path — SQ-learnability bounds the SEARCH phase, not the steady
state. `_hThreshold` and `_a3` are unused, so the BARE cost claim (one model-evaluation per step, no
version space maintained) needs no capacity regime. That last mark must NOT be read as "some
quantitative resource bound is regularity-free": the `O(poly(r))` sharpening of [SQ] Cor 4.4(i)
quantifies over the rule's description length `r`, which is exactly A3's parameter, and it is not
this node. -/
theorem steady_state_bounded
    (hL1 : A1 → A2 → DensityDilution)
    (hL2 : A4 → DensityDilution → GradientFormation)
    (hL3 : GradientFormation → CapacityConcentration)
    (hL4 : CapacityConcentration → A5 → CompositionalSubsystems)
    (hL5 : CompositionalSubsystems → CausalDecoupling)
    (hDiscovery : Realizable → CausalDecoupling → EncodedRule)
    (hRetention : CausalDecoupling → EncodedRule → RuleRetained) -- [Discovery] Proposition 4.2
    (hSteadyState : CausalDecoupling → RuleRetained → SteadyStateBounded) -- [SQ] Corollary 4.4
    (_hTractability : SQLearnable → EncodedRule → PolyTimeCompute) -- off critical path
    (_hThreshold : A3 → EncodedRule → Reflective) -- off critical path
    (a1 : A1) (a2 : A2) (_a3 : A3) (a4 : A4) (a5 : A5)
    (real : Realizable) (_sq : SQLearnable) : -- SQLearnable unused
    SteadyStateBounded :=
  let decoupled : CausalDecoupling := hL5 (hL4 (hL3 (hL2 a4 (hL1 a1 a2))) a5)
  hSteadyState decoupled (hRetention decoupled (hDiscovery real decoupled))

end ProofChainSkeleton
