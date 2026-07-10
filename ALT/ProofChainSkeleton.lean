/-
Copyright (c) 2026 Mykola Palamarchuk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mykola Palamarchuk
-/
import Mathlib

-- Formal-check file, not Mathlib-destined: opt out of the house-style header linter.
set_option linter.style.header false

/-!
# Paper IV proof-chain skeleton (§6 Main Theorem + Appendix table)

Provenance: Paper IV, §2 (axioms A1–A5),
§3 (physical lemmas L1–L5), §4 (Paper II import: discovery), §5 (Paper III import: tractability),
§6 (Theorem 6.1 + its proof), and the Appendix ("The Proof Chain in One Table"), the source of
truth for the dependency edges.

Status: PROVED as pure propositional logic. This is a STRUCTURAL check of the dependency DAG only.

## What this DOES establish
* `inevitability_full`: the §6 assembly is logically connected with no missing link — every node's
  antecedents are discharged from exactly the stated axioms + lemma/import edges. The proof uses
  EVERY hypothesis, so a clean build certifies there is no gap in the chain as the paper states it.
* `reflective_core`: bare representational reflection (Paper I Def 6.1) follows from A1–A5 +
  realizability + the physical/Paper-I/Paper-II edges ALONE. The Paper III tractability edge, the
  SQ-learnability premise, and the retention edge are `_`-marked: the proof literally cannot
  reference them, so the compiler certifies they are OFF the critical path: they sharpen the bound
  to polynomial time and give persistence, but bare representational reflection does not depend on
  them (exactly §5 / caveat 1).
* A5's independence is structural: `A5` occurs only as a free atomic premise feeding `hL4`; no
  hypothesis concludes `A5`, so "A5 not derivable from A1–A4" (caveat 2 / §9) is a checkable
  property of the encoding, not a comment.

## What this does NOT establish (purely structural; no content)
* It proves NO axiom, NO lemma (L1–L5), and NO import — all are abstract `Prop`s. Zero physical or
  mathematical content: not Jeans instability, not Kauffman–Mossel–Steel, not the Decoupling Lemma,
  not the Paper II/III bounds, not the categorical threshold of Paper I Thm 6.2.
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
  tractability).
* Elision flagged (not a logic gap): §4 imports Paper II Thm 3.1 under realizability AND ergodic
  observability, but Theorem 6.1's premise list and the appendix Discovery row carry only
  realizability (the paper treats ergodic observability as auto-satisfied by L4's molecular
  subsystems). We model the §6/appendix chain — realizability only — and do not invent the dropped
  condition.
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

/-- Full §6 chain. Every lemma/import edge is exercised, so a clean build certifies the assembly
has no missing link. The conclusion bundles the three terminal claims of Theorem 6.1 + appendix
(representational reflection, retention, polynomial-time tractability). -/
theorem inevitability_full
    (hL1 : A1 → A2 → DensityDilution) -- L1 §3.1 (from A1, A2)
    (hL2 : A4 → DensityDilution → GradientFormation) -- L2 §3.2 (A4; uses L1 "falling average")
    (hL3 : GradientFormation → CapacityConcentration) -- L3 §3.3 (from L2)
    (hL4 : CapacityConcentration → A5 → CompositionalSubsystems) -- L4 §3.4 (A5 + L3's regions)
    (hL5 : CompositionalSubsystems → CausalDecoupling) -- L5 §3.5 = Paper I Lemma 3.1
    (hDiscovery : Realizable → CausalDecoupling → EncodedRule) -- Paper II Theorem 3.1
    (hRetention : CausalDecoupling → EncodedRule → RuleRetained) -- Paper II Proposition 4.2
    (hTractability : SQLearnable → EncodedRule → PolyTimeCompute) -- Paper III Theorem 4.1
    (hThreshold : A3 → EncodedRule → Reflective) -- Paper I Theorem 6.2 (A3 = regime r ≪ K_max)
    (a1 : A1) (a2 : A2) (a3 : A3) (a4 : A4) (a5 : A5)
    (real : Realizable) (sq : SQLearnable) :
    Reflective ∧ RuleRetained ∧ PolyTimeCompute := by
  have decoupled : CausalDecoupling := hL5 (hL4 (hL3 (hL2 a4 (hL1 a1 a2))) a5)
  have encoded : EncodedRule := hDiscovery real decoupled
  exact ⟨hThreshold a3 encoded, hRetention decoupled encoded, hTractability sq encoded⟩

/-- Bare representational reflection (Paper I Def 6.1): follows from A1–A5 + realizability + the
physical / Paper-I / Paper-II edges ALONE. `_hRetention`, `_hTractability`, and `_sq` are `_`-marked
— the proof never references them, so the compiler certifies SQ-learnability, the Paper III
tractability edge, and the retention edge are OFF the critical path. -/
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

end ProofChainSkeleton
