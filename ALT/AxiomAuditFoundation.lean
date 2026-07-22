/-
Copyright (c) 2026 Mykola Palamarchuk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mykola Palamarchuk
-/
import ALT.GodelChecker
import ALT.GodelCheckerAutomaton
import ALT.GodelCheckerComplete
import ALT.GodelComplete
import ALT.ExcessOrderComplete

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
Foundation's `𝗜𝚺₁`/`𝗣𝗔` `Δ₁`-definability is a *theorem* (`ISigma1_delta1Definable`, discharged
upstream), so the `𝗜𝚺₁` capstones are axiom-clean alongside the `𝗣𝗔⁻` ones (finite theory, `Δ₁` via
`Theory.Δ₁.ofFinite`) and the generic adapter. So a guard here breaks the build if *any* axiom —
standard or named — is ever added. `(whitespace := lax)` normalizes the pretty-printer's line wrapping
of the axiom list.
-/

-- FV-8 (sound concrete checker) — fully axiom-clean for the finite witness 𝗣𝗔⁻
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
-- is a theorem (`ISigma1_delta1Definable`, discharged upstream). Guarded alongside the `𝗣𝗔⁻`
-- capstones, which stay the more faithful (§5.3-class) witnesses (`𝗣𝗔⁻ ⊊ 𝗜𝚺₁`).
/-- info: 'GodelChecker.isigma1_decides_bounded_nonprovability'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GodelChecker.isigma1_decides_bounded_nonprovability'

/-- info: 'GodelCheckerComplete.isigma1_complete_decides' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GodelCheckerComplete.isigma1_complete_decides

/-! ## Guard-gap closure — the §5.3/§6 incompleteness discharge (`ALT/GodelComplete.lean`)

The axiom-clean generic adapter that discharges the imported `GodelThreshold.Incompleteness`
hypothesis via upstream `FormalizedFormalLogic/Foundation` (pinned rev `b47cf447`), plus its two
concrete `𝗜𝚺₁` witnesses. Per that file's BAR the adapter is axiom-clean, and the `𝗜𝚺₁` witnesses are
too — Foundation's `𝗜𝚺₁`/`𝗣𝗔` `Δ₁`-definability is a theorem (`ISigma1_delta1Definable`, discharged
upstream) — so nothing here carries a named axiom. -/

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
