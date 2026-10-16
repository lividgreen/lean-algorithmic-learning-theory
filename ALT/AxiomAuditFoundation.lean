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
public import ChaitinIncompleteness.ChaitinIncompleteness
public import ALT.ChaitinLadder
public import ChaitinIncompleteness.ChaitinPrefix
public import ALT.ChaitinPrefixLadder
public import ChaitinIncompleteness.KBEnumerable
public import AIT.PrefixInvarianceKB
public import ALT.PrefixEliasKB
public import AIT.PrefixModelCost
public import ALT.KReconnection
public import AIT.PrefixPairKB
public import AIT.PrefixCounting
public import ALT.IndexCost


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
standard or named — is ever added. `(whitespace := lax)` normalizes the pretty-printer's line
wrapping of the axiom list.
-/

-- FV-8 (sound concrete checker) — fully axiom-clean for the finite witness 𝗣𝗔⁻

@[expose] public section

set_option linter.style.longLine false in
/-- info: 'ALT.HilbertChecker.paMinus_decides_bounded_nonprovability' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.HilbertChecker.paMinus_decides_bounded_nonprovability

set_option linter.style.longLine false in
/-- info: 'ALT.HilbertChecker.Prf_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.HilbertChecker.Prf_sound

set_option linter.style.longLine false in
/-- info: 'ALT.HilbertChecker.prf_nondegenerate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.HilbertChecker.prf_nondegenerate

set_option linter.style.longLine false in
/-- info: 'ALT.HilbertChecker.prf_accepts_mp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.HilbertChecker.prf_accepts_mp

-- FV-8 / Proposition 4.5 (minimality) — the fragment-witness re-exports: the same internalization
-- capstones, re-stated over an import closure the `assert_not_exists` guards prove
-- exponential-free.
set_option linter.style.longLine false in
/-- info: 'ALT.fragment_internalization' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.fragment_internalization

/-- info: 'ALT.fragment_decides_godel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.fragment_decides_godel

-- FV-19 (§6.5 Proposition 6.5, concrete): the reflective decision automaton run over the executable
-- checker, halting `true` on the actual 𝗣𝗔⁻ Gödel sentence — fully axiom-clean for the finite
-- witness.
set_option linter.style.longLine false in
/-- info: 'ALT.HilbertCheckerAutomaton.paMinus_automaton_decides' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.HilbertCheckerAutomaton.paMinus_automaton_decides

set_option linter.style.longLine false in
/-- info: 'ALT.HilbertCheckerAutomaton.step_readonly_code' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.HilbertCheckerAutomaton.step_readonly_code

-- FV-9 (sound-and-complete bounded decision) — fully axiom-clean for 𝗣𝗔⁻
set_option linter.style.longLine false in
/-- info: 'ALT.ArithmetizedChecker.paMinus_complete_decides' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.ArithmetizedChecker.paMinus_complete_decides

set_option linter.style.longLine false in
/-- info: 'ALT.ArithmetizedChecker.decide_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.ArithmetizedChecker.decide_correct

set_option linter.style.longLine false in
/-- info: 'ALT.ArithmetizedChecker.Prf_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.ArithmetizedChecker.Prf_complete

set_option linter.style.longLine false in
/-- info: 'ALT.ArithmetizedChecker.provable_of_decide_false' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.ArithmetizedChecker.provable_of_decide_false

set_option linter.style.longLine false in
/-- info: 'ALT.ArithmetizedChecker.decide_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.ArithmetizedChecker.decide_nonvacuous

-- The parallel `𝗜𝚺₁` witnesses — now axiom-clean, since Foundation's `𝗜𝚺₁`/`𝗣𝗔` `Δ₁`-definability
-- is a theorem (an anonymous instance in its `Incompleteness/Definability.lean`, discharged
-- upstream). Guarded alongside the `𝗣𝗔⁻`
-- capstones, which stay the more faithful (§5.3-class) witnesses (`𝗣𝗔⁻ ⊊ 𝗜𝚺₁`).
set_option linter.style.longLine false in
/-- info: 'ALT.HilbertChecker.isigma1_decides_bounded_nonprovability'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.HilbertChecker.isigma1_decides_bounded_nonprovability'

set_option linter.style.longLine false in
/-- info: 'ALT.ArithmetizedChecker.isigma1_complete_decides' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.ArithmetizedChecker.isigma1_complete_decides

-- The decision is `ComputablePred` (Mathlib's sense), and the convenience `Computable` form.
set_option linter.style.longLine false in
/-- info: 'ALT.ArithmetizedChecker.computablePred_decide' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.ArithmetizedChecker.computablePred_decide

set_option linter.style.longLine false in
/-- info: 'ALT.ArithmetizedChecker.computable_decide' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.ArithmetizedChecker.computable_decide

/-! ## Guard-gap closure — the §5.3/§6 incompleteness discharge (`ALT/GodelComplete.lean`)

The axiom-clean generic adapter that discharges the imported `ALT.Incompleteness`
hypothesis via upstream `FormalizedFormalLogic/Foundation` (first discharged at rev `b47cf447`,
re-verified at each pin bump since), plus its two concrete `𝗜𝚺₁` witnesses. Per that file's BAR
the adapter is axiom-clean, and the `𝗜𝚺₁` witnesses are too — Foundation's `𝗜𝚺₁`/`𝗣𝗔`
`Δ₁`-definability is a theorem (an anonymous instance in its `Incompleteness/Definability.lean`,
discharged upstream) — so nothing here carries a named axiom. -/

-- Generic §5.3-class adapter — axiom-clean: for any `[T.Δ₁] [𝗥₀ ⪯ T] [ℕ↓[ℒₒᵣ] ⊧* T]`, Foundation's
-- first
-- incompleteness theorem discharges the literal `ALT.Incompleteness`.
set_option linter.style.longLine false in
/-- info: 'ALT.incompleteness_of_arith' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.incompleteness_of_arith

-- The two concrete `𝗜𝚺₁` witnesses — axiom-clean via the upstream `Δ₁`-definability theorem.
set_option linter.style.longLine false in
/-- info: 'ALT.isigma1_represents_underivable_truth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.isigma1_represents_underivable_truth

set_option linter.style.longLine false in
/-- info: 'ALT.isigma1_decides_bounded_nonprovability' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.isigma1_decides_bounded_nonprovability

/-! ## The unconditional excess order (`ALT/ExcessOrderComplete.lean`)

Composing the discharge above with the [Decoupling] §6.4 threshold removes the incompleteness
antecedent from `ALT.Outgrows`: at a concrete arithmetic there is a Gödel size where the
delivered reflective object represents an underivable truth outright. The `𝗣𝗔⁻` route is
axiom-clean via finiteness (`Theory.Δ₁.ofFinite`), so no named axiom appears. -/

-- The generic adapter — `Outgrows` at any `[T.Δ₁] [𝗥₀ ⪯ T] [ℕ↓[ℒₒᵣ] ⊧* T]`, antecedent discharged.
/-- info: 'ALT.outgrows_arith' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.outgrows_arith

-- The concrete `𝗣𝗔⁻` instance — the most faithful witness (finite theory, `Δ₁` via `ofFinite`).
/-- info: 'ALT.outgrows_paMinus' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.outgrows_paMinus

-- The capstone — the cheaply-owned Witness World guest unconditionally outgrows its host at `𝗣𝗔⁻`.
set_option linter.style.longLine false in
/-- info: 'ALT.witness_outgrows_paMinus' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.witness_outgrows_paMinus

/-! ## The accreting crossing package (`ALT/AccretingExcess.lean`)

The accreting healer world's guest ([Guests] §3/§5) composed with the uniform `𝗣𝗔⁻` excess above: a
Gödel size fixed with the theory that every stage past some `t₀` hosts, with the reflective object
delivered at that stage's own budget. Axiom-clean via the same `𝗣𝗔⁻` finiteness route. -/

-- The uniform excess — one Gödel size served across every hosting budget, not one per budget.
set_option linter.style.longLine false in
/-- info: 'ALT.outgrows_paMinus_uniform' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.outgrows_paMinus_uniform

-- Eventual hosting — the crossing stage `t₀` made explicit. Constructive: no `Classical.choice`.
/-- info: 'ALT.eventually_hostsAt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.eventually_hostsAt

-- The package — the accreting skeleton's landed clauses beside the eventual-hosting crossing.
set_option linter.style.longLine false in
/-- info: 'ALT.accreting_outgrows_paMinus' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.accreting_outgrows_paMinus

/-! ## The deep ladder (`ALT/DeepLadder.lean`)

The crossing recurrence over each rung of the deep ladder — both at the hidden selector (chosen via
`Classical.epsilon`) and at the explicit selector (Foundation's own Gödel sentence, exhibited). -/

-- The recurrence at an arbitrary rung selector.
/-- info: 'ALT.accreting_ladder' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.accreting_ladder

-- The recurrence at the explicit selector, base `𝗜𝚺₁`.
set_option linter.style.longLine false in
/-- info: 'ALT.explicit_accreting_ladder' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.explicit_accreting_ladder

-- The explicit ladder's step IS the consistency step, at each theory's own predicate.
set_option linter.style.longLine false in
/-- info: 'ALT.explicitLadder_succ_equiv_con' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.explicitLadder_succ_equiv_con

-- The Ehrenfeucht–Mycielski speedup at the explicit ladder.
/-- info: 'ALT.explicitLadder_speedup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.explicitLadder_speedup

/-! ## The generalized crossing (`ALT/GrowingCoreCrossing.lean`)

`eventually_hostsAt`'s fixed budget `t + 1` pulled back to an arbitrary monotone unbounded budget
profile — `hostsAt_mono` is the whole glue, so this needs nothing beyond the package above. -/

-- Eventual hosting at an arbitrary monotone unbounded budget. Constructive, like its `t + 1` case.
/-- info: 'ALT.eventually_hostsAt_ofBudget' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.eventually_hostsAt_ofBudget

-- The generalized package — one Gödel size, threaded through `κ` in place of the witness's `t + 1`.
set_option linter.style.longLine false in
/-- info: 'ALT.eventually_hosts_uniform' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.eventually_hosts_uniform

-- [Inevitability] §2 Definition 2.3, the class-level `𝒮_E` constructor's crossing clause: a
-- Gödel size fixed once, that every sufficiently hosting capacity represents — routes through
-- `𝗣𝗔⁻` via `ALT.outgrows_paMinus_uniform`, same finiteness route as the packages
-- above.
set_option linter.style.longLine false in
/-- info: 'ALT.grownGuestReachesThresholdAt_uniform' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.grownGuestReachesThresholdAt_uniform

/-! ## The block-pair host's `𝒮_E` overlap (`ALT/BlockPairOverlap.lean`)

The certified block-pair host, packed onto its numeral carrier and read through its own counter
register, is simultaneously a member of `𝒮_E` and of `𝒮_L` — one update, one code region, one
numeral set. Axiom-clean via the same `𝗣𝗔⁻` finiteness route as the packages above. -/

-- The overlap capstone — the SAME host is a member of both route-classes at once.
set_option linter.style.longLine false in
/-- info: 'ALT.BlockPairHost.witness_overlap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.BlockPairHost.witness_overlap

/-! ## The class-level overlap (`ALT/TapeHostOverlap.lean`, `ALT/BlockPairCriterion.lean`)

The class-level overlap over an arbitrary host and profile, at IN-24's coupling standard (one
Gödel size shared by the class's own capacity clause and the crossing clause), and the certified
block-pair sequence's own instance of it. Both route through
`ALT.grownGuestReachesThresholdAt_uniform`, hence `𝗣𝗔⁻`, the same finiteness route as the packages
above — not `ALT.BlockPairHost.witness_overlap`'s own decoupled numerals, which stay untouched.
-/

/-- info: 'ALT.TapeHost.overlap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.TapeHost.overlap

set_option linter.style.longLine false in
/-- info: 'ALT.blockPair_overlap_coupled' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.blockPair_overlap_coupled

-- The profile-class family's own class-level overlap (`ALT/BlockPairFamilyCriterion.lean`): every
-- member with `r ≥ 2` is simultaneously in `𝒮_E` and `𝒮_L`, at the same coupled numeral standard —
-- the certified pair's own `blockPair_overlap_coupled` above is the `r = 3` instance.
set_option linter.style.longLine false in
/-- info: 'ALT.blockPairFamily_overlap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.blockPairFamily_overlap

/-! ## A member of both route-classes carries survival, by redundancy (`ALT/TapeHostSurvival.lean`)

The base-plus-fiber composite (the tape host's own substrate with a `P`-copy redundant floored
fiber added as extra memory) is a member of `𝒮_E`, via `ALT.grownGuestReachesThresholdAt_uniform`,
the same `𝗣𝗔⁻` finiteness route as the packages above. The capstone bundles that membership with the
composite's `𝒮_L` membership and its own survival by redundancy, so it routes through `𝗣𝗔⁻` too. -/

set_option linter.style.longLine false in
/-- info: 'ALT.TapeHost.comp_substrateE' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.TapeHost.comp_substrateE

-- The survival capstone — a member of both route-classes carries survival by redundancy.
set_option linter.style.longLine false in
/-- info: 'ALT.TapeHost.carries_survival' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.TapeHost.carries_survival

/-! ## Chaitin's incompleteness theorem as a deep-ladder rung selector (`ALT/ChaitinLadder.lean`)

`chaitinSelector` instantiates `TheoryProgression.SentenceSelector` at base `𝗥₀` from
`chaitin_theorem`; the
capstone recurrence restated at it (`ALT.chaitin_accreting_ladder`, in
`ALT/DeepLadder.lean`) is axiom-clean too. -/

set_option linter.style.longLine false in
/-- info: 'ALT.chaitin_accreting_ladder' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.chaitin_accreting_ladder

/-! ## The prefix-Chaitin ladder's rate (`ALT/ChaitinPrefixLadder.lean`)

`prefixChaitinSelector` places the Chaitin sentence on `KB` at each theory's own additive
threshold; the strict-increase theorems and the no-uniform-naming corollary are axiom-clean. -/

/-- info: 'ALT.KB_enumerator_succ_gt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.KB_enumerator_succ_gt

/-- info: 'ALT.KB_enumeratorB_lt_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.KB_enumeratorB_lt_succ

/-- info: 'ALT.KB_enumeratorB_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.KB_enumeratorB_ge

set_option linter.style.longLine false in
/-- info: 'ALT.KB_enumeratorB_lt_succ_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.KB_enumeratorB_lt_succ_nonvacuous

set_option linter.style.longLine false in
/-- info: 'ALT.prefixChaitinLadder_not_uniform_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.prefixChaitinLadder_not_uniform_of

/-! ## `KB`'s Elias bound and the ladder's assembly (`AIT/EliasBound.lean`,
`ALT/PrefixEliasKB.lean`)

The Elias decoder `eliasDecoder`, its own halting domain prefix-free, the unabsorbed Elias bound
`KB_le_size_add_two_mul_size_size`, its corollary `KB_le_two_mul_size` — the other of
`prefixChaitinLadder_not_uniform_of`'s two hypotheses — and the ladder's non-uniformity theorem
put together from both, with its non-vacuity witness. -/

set_option linter.style.longLine false in
/-- info: 'ALT.prefixChaitinLadder_not_uniform' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.prefixChaitinLadder_not_uniform

set_option linter.style.longLine false in
/-- info: 'ALT.prefixChaitinLadder_not_uniform_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.prefixChaitinLadder_not_uniform_nonvacuous

/-! ## The model cost on the prefix machine (`AIT/PrefixModelCost.lean`)

`KB` related to `K_bitlen`, `KP`, and `ruleComplexity`, each over a partial-map invariance and/or
an unabsorbed Elias bound for `KB` taken as hypotheses, and each with an unconditional corollary
discharging every one of those hypotheses at a landed statement. -/

set_option linter.style.longLine false in
/-- info: 'ALT.KB_le_ruleComplexity_add_two_mul_size_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.KB_le_ruleComplexity_add_two_mul_size_of

set_option linter.style.longLine false in
/-- info: 'ALT.KB_le_ruleComplexity_add_two_mul_size' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.KB_le_ruleComplexity_add_two_mul_size

/-! ## The index cost of a description (`ALT/IndexCost.lean`)

`SizeLaw` (`codelen'`'s growth law at `pair`/`comp`), `Code.const`'s own growth law proved from it,
`NestSpec` and `DecoderSpec` (the nest's own facts and a decoder reading it back through
`univPrefix`, both proved outright), the conditional theorem assembling all three into
`K_bitlen x ≤ 32 * KB x + c`, and that bound unconditional — guarded here rather than in
`ALT/AxiomAuditMathlib.lean` because `ALT.IndexCost`'s import closure reaches Foundation through
`AIT.PrefixInvarianceKB`. -/

/-- info: 'ALT.sizeLaw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.sizeLaw

set_option linter.style.longLine false in
/-- info: 'ALT.codelen'_const_add_three_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.codelen'_const_add_three_le

/-- info: 'ALT.nestSpec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.nestSpec

set_option linter.style.longLine false in
/-- info: 'ALT.K_bitlen_le_32_mul_KB_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.K_bitlen_le_32_mul_KB_of

/-- info: 'ALT.decoderSpec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.decoderSpec

/-- info: 'ALT.K_bitlen_le_32_mul_KB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.K_bitlen_le_32_mul_KB
