/-
Copyright (c) 2026 Mykola Palamarchuk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mykola Palamarchuk
-/
module

public import ALT.GodelChecker
public import ALT.GodelCheckerAutomaton
public import ALT.GodelCheckerComplete
public import ALT.GodelComplete
public import ALT.ExcessOrderComplete
public import ALT.AccretingExcess
public import ALT.DeepLadder
public import ALT.GrowingCoreCrossing
public import ALT.SubstrateEmergence
public import ALT.BlockPairOverlap
public import ALT.TapeHostOverlap
public import ALT.BlockPairCriterion
public import ALT.BlockPairFamilyCriterion
public import ALT.MinimalityWitness
public import ALT.TapeHostSurvival
public import ALT.ChaitinIncompleteness
public import ALT.ChaitinLadder
public import ALT.ChaitinPrefix
public import ALT.ChaitinPrefixLadder
public import ALT.KBEnumerable
public import ALT.PrefixInvarianceKB
public import ALT.PrefixEliasKB
public import ALT.PrefixModelCost
public import ALT.PrefixPairKB
public import ALT.PrefixCounting
public import ALT.IndexCost

-- Formal-check file, not Mathlib-destined: opt out of the house-style linters.
set_option linter.style.header false
set_option linter.style.longLine false

/-!
# Axiom audit (Foundation side) — machine-ENFORCED axiom-cleanliness ([Decoupling] appendix)

Provenance: [Decoupling] appendix ("Every theorem is `#print axioms`
-clean"). This file turns that prose claim into a build-time guarantee: each `#guard_msgs in
#print axioms …` below **fails `lake build`** if the theorem's axiom set ever drifts from the
asserted one. Reached from the root `ALT` umbrella, so a routine `lake build` enforces it.

Every guarded theorem is fully axiom-clean — `[propext, Classical.choice, Quot.sound]`, the standard
triple, with **no named axioms anywhere**. This now includes the parallel `𝗜𝚺₁` witnesses:
Foundation's `𝗜𝚺₁`/`𝗣𝗔` `Δ₁`-definability is a *theorem* (an anonymous instance in its
`Incompleteness/Definability.lean`, discharged upstream), so the `𝗜𝚺₁` capstones are axiom-clean
alongside the `𝗣𝗔⁻` ones (finite theory, `Δ₁` via
`Theory.Δ₁.ofFinite`) and the generic adapter. So a guard here breaks the build if *any* axiom —
standard or named — is ever added. `(whitespace := lax)` normalizes the pretty-printer's line wrapping
of the axiom list.
-/

-- FV-8 (sound concrete checker) — fully axiom-clean for the finite witness 𝗣𝗔⁻

@[expose] public section

/-- info: 'GodelChecker.paMinus_decides_bounded_nonprovability' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GodelChecker.paMinus_decides_bounded_nonprovability

/-- info: 'GodelChecker.Prf_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GodelChecker.Prf_sound

/-- info: 'GodelChecker.prf_nondegenerate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GodelChecker.prf_nondegenerate

/-- info: 'GodelChecker.prf_accepts_mp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GodelChecker.prf_accepts_mp

-- FV-8 / Proposition 4.5 (minimality) — the fragment-witness re-exports: the same internalization
-- capstones, re-stated over an import closure the `assert_not_exists` guards prove exponential-free.
/-- info: 'MinimalityWitness.fragment_internalization' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MinimalityWitness.fragment_internalization

/-- info: 'MinimalityWitness.fragment_decides_godel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MinimalityWitness.fragment_decides_godel

-- FV-19 (§6.5 Proposition 6.5, concrete): the reflective decision automaton run over the executable
-- checker, halting `true` on the actual 𝗣𝗔⁻ Gödel sentence — fully axiom-clean for the finite witness.
/-- info: 'GodelCheckerAutomaton.paMinus_automaton_decides' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GodelCheckerAutomaton.paMinus_automaton_decides

/-- info: 'GodelCheckerAutomaton.step_readonly_code' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GodelCheckerAutomaton.step_readonly_code

-- FV-9 (sound-and-complete bounded decision) — fully axiom-clean for 𝗣𝗔⁻
/-- info: 'GodelCheckerComplete.paMinus_complete_decides' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GodelCheckerComplete.paMinus_complete_decides

/-- info: 'GodelCheckerComplete.decide_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GodelCheckerComplete.decide_correct

/-- info: 'GodelCheckerComplete.Prf_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GodelCheckerComplete.Prf_complete

/-- info: 'GodelCheckerComplete.provable_of_decide_false' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GodelCheckerComplete.provable_of_decide_false

/-- info: 'GodelCheckerComplete.decide_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GodelCheckerComplete.decide_nonvacuous

-- The parallel `𝗜𝚺₁` witnesses — now axiom-clean, since Foundation's `𝗜𝚺₁`/`𝗣𝗔` `Δ₁`-definability
-- is a theorem (an anonymous instance in its `Incompleteness/Definability.lean`, discharged
-- upstream). Guarded alongside the `𝗣𝗔⁻`
-- capstones, which stay the more faithful (§5.3-class) witnesses (`𝗣𝗔⁻ ⊊ 𝗜𝚺₁`).
/-- info: 'GodelChecker.isigma1_decides_bounded_nonprovability'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GodelChecker.isigma1_decides_bounded_nonprovability'

/-- info: 'GodelCheckerComplete.isigma1_complete_decides' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GodelCheckerComplete.isigma1_complete_decides

-- The decision is `ComputablePred` (Mathlib's sense), and the convenience `Computable` form.
/-- info: 'GodelCheckerComplete.computablePred_decide' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GodelCheckerComplete.computablePred_decide

/-- info: 'GodelCheckerComplete.computable_decide' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GodelCheckerComplete.computable_decide

/-! ## Guard-gap closure — the §5.3/§6 incompleteness discharge (`ALT/GodelComplete.lean`)

The axiom-clean generic adapter that discharges the imported `GodelThreshold.Incompleteness`
hypothesis via upstream `FormalizedFormalLogic/Foundation` (first discharged at rev `b47cf447`,
re-verified at each pin bump since), plus its two concrete `𝗜𝚺₁` witnesses. Per that file's BAR
the adapter is axiom-clean, and the `𝗜𝚺₁` witnesses are too — Foundation's `𝗜𝚺₁`/`𝗣𝗔`
`Δ₁`-definability is a theorem (an anonymous instance in its `Incompleteness/Definability.lean`,
discharged upstream) — so nothing here carries a named axiom. -/

-- Generic §5.3-class adapter — axiom-clean: for any `[T.Δ₁] [𝗥₀ ⪯ T] [ℕ↓[ℒₒᵣ] ⊧* T]`, Foundation's first
-- incompleteness theorem discharges the literal `GodelThreshold.Incompleteness`.
/-- info: 'GodelComplete.incompleteness_of_arith' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GodelComplete.incompleteness_of_arith

-- The two concrete `𝗜𝚺₁` witnesses — axiom-clean via the upstream `Δ₁`-definability theorem.
/-- info: 'GodelComplete.isigma1_represents_underivable_truth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GodelComplete.isigma1_represents_underivable_truth

/-- info: 'GodelComplete.isigma1_decides_bounded_nonprovability' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GodelComplete.isigma1_decides_bounded_nonprovability

/-! ## The unconditional excess order (`ALT/ExcessOrderComplete.lean`)

Composing the discharge above with the [Decoupling] §6.4 threshold removes the incompleteness
antecedent from `ExcessOrder.Outgrows`: at a concrete arithmetic there is a Gödel size where the
delivered reflective object represents an underivable truth outright. The `𝗣𝗔⁻` route is
axiom-clean via finiteness (`Theory.Δ₁.ofFinite`), so no named axiom appears. -/

-- The generic adapter — `Outgrows` at any `[T.Δ₁] [𝗥₀ ⪯ T] [ℕ↓[ℒₒᵣ] ⊧* T]`, antecedent discharged.
/-- info: 'ExcessOrder.outgrows_arith' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ExcessOrder.outgrows_arith

-- The concrete `𝗣𝗔⁻` instance — the most faithful witness (finite theory, `Δ₁` via `ofFinite`).
/-- info: 'ExcessOrder.outgrows_paMinus' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ExcessOrder.outgrows_paMinus

-- The capstone — the cheaply-owned Witness World guest unconditionally outgrows its host at `𝗣𝗔⁻`.
/-- info: 'ExcessOrder.witness_outgrows_paMinus' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ExcessOrder.witness_outgrows_paMinus

/-! ## The accreting crossing package (`ALT/AccretingExcess.lean`)

The accreting healer world's guest ([Guests] §3/§5) composed with the uniform `𝗣𝗔⁻` excess above: a
Gödel size fixed with the theory that every stage past some `t₀` hosts, with the reflective object
delivered at that stage's own budget. Axiom-clean via the same `𝗣𝗔⁻` finiteness route. -/

-- The uniform excess — one Gödel size served across every hosting budget, not one per budget.
/-- info: 'AccretingWitness.outgrows_paMinus_uniform' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AccretingWitness.outgrows_paMinus_uniform

-- Eventual hosting — the crossing stage `t₀` made explicit. Constructive: no `Classical.choice`.
/-- info: 'AccretingWitness.eventually_hostsAt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AccretingWitness.eventually_hostsAt

-- The package — the accreting skeleton's landed clauses beside the eventual-hosting crossing.
/-- info: 'AccretingWitness.accreting_outgrows_paMinus' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AccretingWitness.accreting_outgrows_paMinus

/-! ## The deep ladder (`ALT/DeepLadder.lean`)

The crossing recurrence over each rung of the deep ladder — both at the hidden selector (chosen via
`Classical.epsilon`) and at the explicit selector (Foundation's own Gödel sentence, exhibited). -/

-- The recurrence at an arbitrary rung selector.
/-- info: 'DeepLadder.accreting_ladder' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeepLadder.accreting_ladder

-- The recurrence at the explicit selector, base `𝗜𝚺₁`.
/-- info: 'DeepLadder.explicit_accreting_ladder' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeepLadder.explicit_accreting_ladder

-- The explicit ladder's step IS the consistency step, at each theory's own predicate.
/-- info: 'DeepLadder.explicitLadder_succ_equiv_con' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeepLadder.explicitLadder_succ_equiv_con

-- The Ehrenfeucht–Mycielski speedup at the explicit ladder.
/-- info: 'DeepLadder.explicitLadder_speedup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeepLadder.explicitLadder_speedup

/-! ## The generalized crossing (`ALT/GrowingCoreCrossing.lean`)

`eventually_hostsAt`'s fixed budget `t + 1` pulled back to an arbitrary monotone unbounded budget
profile — `hostsAt_mono` is the whole glue, so this needs nothing beyond the package above. -/

-- Eventual hosting at an arbitrary monotone unbounded budget. Constructive, like its `t + 1` case.
/-- info: 'AccretingWitness.eventually_hostsAt_ofBudget' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms AccretingWitness.eventually_hostsAt_ofBudget

-- The generalized package — one Gödel size, threaded through `κ` in place of the witness's `t + 1`.
/-- info: 'AccretingWitness.eventually_hosts_uniform' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AccretingWitness.eventually_hosts_uniform

-- [Inevitability] §2 Definition 2.3, the class-level `𝒮_E` constructor's crossing clause: a
-- Gödel size fixed once, that every sufficiently hosting capacity represents — routes through
-- `𝗣𝗔⁻` via `AccretingWitness.outgrows_paMinus_uniform`, same finiteness route as the packages
-- above.
/-- info: 'SubstrateEmergence.grownGuestReachesThresholdAt_uniform' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SubstrateEmergence.grownGuestReachesThresholdAt_uniform

/-! ## The block-pair host's `𝒮_E` overlap (`ALT/BlockPairOverlap.lean`)

The certified block-pair host, packed onto its numeral carrier and read through its own counter
register, is simultaneously a member of `𝒮_E` and of `𝒮_L` — one update, one code region, one
numeral set. Axiom-clean via the same `𝗣𝗔⁻` finiteness route as the packages above. -/

-- The overlap capstone — the SAME host is a member of both route-classes at once.
/-- info: 'BlockPairOverlap.hostWitness_overlap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms BlockPairOverlap.hostWitness_overlap

/-! ## The class-level overlap (`ALT/TapeHostOverlap.lean`, `ALT/BlockPairCriterion.lean`)

The class-level overlap over an arbitrary host and profile, at IN-24's coupling standard (one
Gödel size shared by the class's own capacity clause and the crossing clause), and the certified
block-pair sequence's own instance of it. Both route through `SubstrateEmergence.
grownGuestReachesThresholdAt_uniform`, hence `𝗣𝗔⁻`, the same finiteness route as the packages
above — not `BlockPairOverlap.hostWitness_overlap`'s own decoupled numerals, which stay
untouched. -/

/-- info: 'TapeHostOverlap.tapeHost_overlap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TapeHostOverlap.tapeHost_overlap

/-- info: 'BlockPairCriterion.blockPair_overlap_coupled' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms BlockPairCriterion.blockPair_overlap_coupled

-- The profile-class family's own class-level overlap (`ALT/BlockPairFamilyCriterion.lean`): every
-- member with `r ≥ 2` is simultaneously in `𝒮_E` and `𝒮_L`, at the same coupled numeral standard —
-- the certified pair's own `blockPair_overlap_coupled` above is the `r = 3` instance.
/-- info: 'BlockPairFamilyCriterion.blockPairFamily_overlap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms BlockPairFamilyCriterion.blockPairFamily_overlap

/-! ## A member of both route-classes carries survival, by redundancy (`ALT/TapeHostSurvival.lean`)

The base-plus-fiber composite (the tape host's own substrate with a `P`-copy redundant floored
fiber added as extra memory) is a member of `𝒮_E`, via `SubstrateEmergence.
grownGuestReachesThresholdAt_uniform`, the same `𝗣𝗔⁻` finiteness route as the packages above. The
capstone bundles that membership with the composite's `𝒮_L` membership and its own survival by
redundancy, so it routes through `𝗣𝗔⁻` too. -/

/-- info: 'TapeHostSurvival.comp_substrateE' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TapeHostSurvival.comp_substrateE

-- The survival capstone — a member of both route-classes carries survival by redundancy.
/-- info: 'TapeHostSurvival.tapeHost_carries_survival' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TapeHostSurvival.tapeHost_carries_survival

/-! ## Chaitin's incompleteness theorem over `K_bitlen` (`ALT/ChaitinIncompleteness.lean`)

The generic adapter (`Δ₁`-axiomatized consistent extensions of `𝗥₀`) is axiom-clean: the hypotheses
`[T.Δ₁] [𝗥₀ ⪯ T] [FFL.Entailment.Consistent T]` are typeclass premises, nothing concrete is
synthesized. -/

/-- info: 'KolmogorovComplexity.chaitin_theorem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KolmogorovComplexity.chaitin_theorem

-- The transport to recursively enumerable theories, via Craig's trick — axiom-clean, same reason.
/-- info: 'KolmogorovComplexity.chaitin_theorem_of_RE' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KolmogorovComplexity.chaitin_theorem_of_RE

/-- info: 'KolmogorovComplexity.chaitin_true_unprovable_of_RE' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KolmogorovComplexity.chaitin_true_unprovable_of_RE

/-! ## Chaitin's incompleteness theorem, additive form on `KB` (`ALT/ChaitinPrefix.lean`)

The two leaf propositions `EParserSpec` and `REPred kleB` are explicit hypotheses of each
theorem below, so these guards pin the proofs FROM those hypotheses; the axioms of the leaves'
own proofs are audited where they are proved. -/

/-- info: 'KolmogorovComplexity.chaitin_bound_KB_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KolmogorovComplexity.chaitin_bound_KB_of

/-- info: 'KolmogorovComplexity.chaitin_bound_KB_of_min' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KolmogorovComplexity.chaitin_bound_KB_of_min

/-- info: 'KolmogorovComplexity.chaitin_theoremB_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KolmogorovComplexity.chaitin_theoremB_of

-- The transport to recursively enumerable theories, via Craig's trick — same reason.
/-- info: 'KolmogorovComplexity.chaitin_theoremB_of_RE' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KolmogorovComplexity.chaitin_theoremB_of_RE

/-! ## The assembly, both leaves proved (`ALT/KBEnumerable.lean`)

`EParserSpec` and `REPred kleB` are proved, not hypotheses, from here on: the guards below pin
the UNCONDITIONAL forms of the bounds above, applied to those proofs. -/

/-- info: 'KolmogorovComplexity.chaitin_bound_KB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KolmogorovComplexity.chaitin_bound_KB

/-- info: 'KolmogorovComplexity.chaitin_bound_KB_min' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KolmogorovComplexity.chaitin_bound_KB_min

/-- info: 'KolmogorovComplexity.chaitin_theoremB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KolmogorovComplexity.chaitin_theoremB

/-- info: 'KolmogorovComplexity.chaitin_theoremB_RE' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KolmogorovComplexity.chaitin_theoremB_RE

-- The enumerator is exhibited, not merely asserted to exist — `rePred_provable_chaitinB` unpacked
-- through `REPred.iff'` and `Nat.Partrec.Code.exists_code`.
/-- info: 'KolmogorovComplexity.exists_enumerator_chaitinB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KolmogorovComplexity.exists_enumerator_chaitinB

-- Non-vacuity: `𝗣𝗔⁻` meets every instance binder `chaitin_theoremB` asks for, at once.
/-- info: 'KolmogorovComplexity.chaitin_theoremB_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KolmogorovComplexity.chaitin_theoremB_nonvacuous

-- `KB`'s counting bound and its true-and-unprovable family, at the additive constant.
/-- info: 'KolmogorovComplexity.setOf_KB_le_finite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KolmogorovComplexity.setOf_KB_le_finite

/-- info: 'KolmogorovComplexity.chaitin_true_unprovableB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KolmogorovComplexity.chaitin_true_unprovableB

/-! ## Chaitin's incompleteness theorem as a deep-ladder rung selector (`ALT/ChaitinLadder.lean`)

`chaitinSelector` instantiates `DeepLadder.RungSelector` at base `𝗥₀` from `chaitin_theorem`; the
capstone recurrence restated at it is axiom-clean too. -/

/-- info: 'DeepLadder.chaitin_accreting_ladder' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeepLadder.chaitin_accreting_ladder

/-! ## The prefix-Chaitin ladder's rate (`ALT/ChaitinPrefixLadder.lean`)

`prefixChaitinSelector` places the Chaitin sentence on `KB` at each theory's own additive
threshold; the strict-increase theorems and the no-uniform-naming corollary are axiom-clean. -/

/-- info: 'DeepLadder.KB_enumerator_succ_gt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeepLadder.KB_enumerator_succ_gt

/-- info: 'DeepLadder.KB_enumeratorB_lt_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeepLadder.KB_enumeratorB_lt_succ

/-- info: 'DeepLadder.KB_enumeratorB_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeepLadder.KB_enumeratorB_ge

/-- info: 'DeepLadder.KB_enumeratorB_lt_succ_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeepLadder.KB_enumeratorB_lt_succ_nonvacuous

/-- info: 'DeepLadder.prefixChaitinLadder_not_uniform_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeepLadder.prefixChaitinLadder_not_uniform_of

/-! ## `KB`'s invariance under computable maps (`ALT/PrefixInvarianceKB.lean`)

The universal prefix machine `univPrefix`, its own halting domain prefix-free, and the invariance
bound `KB_map_le` it carries — one of `prefixChaitinLadder_not_uniform_of`'s two leaf hypotheses —
now a corollary of the partial-map generalization `KB_partial_map_le`. -/

/-- info: 'PrefixMachine.prefixFree_univPrefix_dom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PrefixMachine.prefixFree_univPrefix_dom

/-- info: 'PrefixMachine.KB_partial_map_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PrefixMachine.KB_partial_map_le

/-- info: 'PrefixMachine.KB_map_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PrefixMachine.KB_map_le

/-- info: 'PrefixMachine.KB_pair_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PrefixMachine.KB_pair_le

/-! ## `KB`'s Elias bound and the ladder's assembly (`ALT/PrefixEliasKB.lean`)

The Elias decoder `eliasDecoder`, its own halting domain prefix-free, the unabsorbed Elias bound
`KB_le_size_add_two_mul_size_size`, its corollary `KB_le_two_mul_size` — the other of
`prefixChaitinLadder_not_uniform_of`'s two hypotheses — and the ladder's non-uniformity theorem
put together from both, with its non-vacuity witness. -/

/-- info: 'PrefixMachine.prefixFree_eliasDecoder_dom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PrefixMachine.prefixFree_eliasDecoder_dom

/-- info: 'PrefixMachine.KB_le_size_add_two_mul_size_size' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PrefixMachine.KB_le_size_add_two_mul_size_size

/-- info: 'PrefixMachine.KB_le_two_mul_size' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PrefixMachine.KB_le_two_mul_size

/-- info: 'DeepLadder.prefixChaitinLadder_not_uniform' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeepLadder.prefixChaitinLadder_not_uniform

/-- info: 'DeepLadder.prefixChaitinLadder_not_uniform_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeepLadder.prefixChaitinLadder_not_uniform_nonvacuous

/-! ## The model cost on the prefix machine (`ALT/PrefixModelCost.lean`)

`KB` related to `K_bitlen`, `KP`, and `ruleComplexity`, each over a partial-map invariance and/or
an unabsorbed Elias bound for `KB` taken as hypotheses, and each with an unconditional corollary
discharging every one of those hypotheses at a landed statement. -/

/-- info: 'PrefixMachine.KB_le_K_bitlen_add_two_mul_size_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PrefixMachine.KB_le_K_bitlen_add_two_mul_size_of

/-- info: 'PrefixMachine.KB_le_K_bitlen_add_two_mul_size' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PrefixMachine.KB_le_K_bitlen_add_two_mul_size

/-- info: 'PrefixMachine.KB_le_KP_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PrefixMachine.KB_le_KP_of

/-- info: 'PrefixMachine.KB_le_KP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PrefixMachine.KB_le_KP

/-- info: 'PrefixMachine.KB_le_ruleComplexity_add_two_mul_size_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PrefixMachine.KB_le_ruleComplexity_add_two_mul_size_of

/-- info: 'PrefixMachine.KB_le_ruleComplexity_add_two_mul_size' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PrefixMachine.KB_le_ruleComplexity_add_two_mul_size

/-! ## Counting bounds on `KB` and `K_bitlen`, and `KB`'s non-computability
(`ALT/PrefixCounting.lean`)

The counting bound `kraft_KB` buys on `KB`, the same constant on `K_bitlen` by injectivity instead,
and `KB`'s non-computability via the already-landed partial-map invariance, no fixed point needed. -/

/-- info: 'PrefixMachine.finset_card_KB_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PrefixMachine.finset_card_KB_le

/-- info: 'PrefixMachine.card_KB_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PrefixMachine.card_KB_le

/-- info: 'PrefixMachine.finset_card_K_bitlen_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PrefixMachine.finset_card_K_bitlen_le

/-- info: 'PrefixMachine.card_K_bitlen_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PrefixMachine.card_K_bitlen_le

/-- info: 'PrefixMachine.KB_not_computable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PrefixMachine.KB_not_computable

/-! ## The index cost of a description (`ALT/IndexCost.lean`)

`SizeLaw` (`codelen'`'s growth law at `pair`/`comp`), `Code.const`'s own growth law proved from it,
`NestSpec` and `DecoderSpec` (the nest's own facts and a decoder reading it back through
`univPrefix`, both proved outright), the conditional theorem assembling all three into
`K_bitlen x ≤ 32 * KB x + c`, and that bound unconditional — guarded here rather than in
`ALT/AxiomAuditMathlib.lean` because `ALT.IndexCost`'s import closure reaches Foundation through
`ALT.PrefixInvarianceKB`. -/

/-- info: 'IndexCost.sizeLaw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms IndexCost.sizeLaw

/-- info: 'IndexCost.codelen'_const_add_three_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms IndexCost.codelen'_const_add_three_le

/-- info: 'IndexCost.nestSpec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms IndexCost.nestSpec

/-- info: 'IndexCost.K_bitlen_le_32_mul_KB_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms IndexCost.K_bitlen_le_32_mul_KB_of

/-- info: 'IndexCost.decoderSpec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms IndexCost.decoderSpec

/-- info: 'IndexCost.K_bitlen_le_32_mul_KB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms IndexCost.K_bitlen_le_32_mul_KB
