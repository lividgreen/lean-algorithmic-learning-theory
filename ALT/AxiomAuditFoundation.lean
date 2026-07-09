import ALT.GodelChecker
import ALT.GodelCheckerComplete
import ALT.GodelComplete

-- Tier-1 formal check, not Mathlib-destined: opt out of the house-style linters.
set_option linter.style.header false
set_option linter.style.longLine false

/-!
# Axiom audit (Foundation side) — machine-ENFORCED axiom-cleanliness (Paper I appendix)

Provenance: `01_decoupling_and_categorical_threshold.md` appendix ("Every theorem is `#print axioms`
-clean"). This file turns that prose claim into a build-time guarantee: each `#guard_msgs in
#print axioms …` below **fails `lake build`** if the theorem's axiom set ever drifts from the
asserted one. Built automatically by the `globs = ["ALT.+"]` target, so CI enforces it.

Every guarded theorem is fully axiom-clean — `[propext, Classical.choice, Quot.sound]`, the standard
triple, with **no named axioms anywhere** (Paper I item 1). The parallel `𝗜𝚺₁` witnesses that once
carried Foundation's `ISigma1_delta1Definable` (its own declared Δ₁ TODO) are **retired**; only the
`𝗣𝗔⁻` capstones (finite theory, `Δ₁` via `Theory.Δ₁.ofFinite`) and the generic axiom-clean adapter
remain. So a guard here breaks the build if *any* axiom — standard or named — is ever added.
`(whitespace := lax)` normalizes the pretty-printer's line wrapping of the axiom list.
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

-- (The `𝗜𝚺₁` witnesses `GodelChecker.isigma1_decides_bounded_nonprovability'` and
-- `GodelCheckerComplete.isigma1_complete_decides` — which carried Foundation's named
-- `ISigma1_delta1Definable` — are retired (Paper I item 1); their guards are removed. The axiom-clean
-- `𝗣𝗔⁻` capstones above are the surviving, more faithful (§5.3-class) witnesses.)

/-! ## Guard-gap closure — the §5.3/§6 incompleteness discharge (`ALT/GodelComplete.lean`)

The axiom-clean generic adapter that discharges the imported `GodelThreshold.Incompleteness`
hypothesis via upstream `FormalizedFormalLogic/Foundation` (pinned rev `f6eed55`). Per that file's
BAR the adapter is axiom-clean; the concrete `𝗜𝚺₁` witness that once carried Foundation's named
`ISigma1_delta1Definable` is retired (Paper I item 1), so nothing here carries a named axiom. -/

-- Generic §5.3-class adapter — axiom-clean: for any `[T.Δ₁] [𝗥₀ ⪯ T] [ℕ↓[ℒₒᵣ] ⊧* T]`, Foundation's first
-- incompleteness theorem discharges the literal `GodelThreshold.Incompleteness`.
/-- info: 'GodelComplete.incompleteness_of_arith' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GodelComplete.incompleteness_of_arith
