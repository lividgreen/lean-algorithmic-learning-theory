/-
Copyright (c) 2026 Mykola Palamarchuk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mykola Palamarchuk
-/
import Foundation.FirstOrder.Incompleteness.Examples
import ALT.GodelCore

-- Formal-check file, not Mathlib-destined: opt out of the house-style linters.
set_option linter.style.header false
set_option linter.style.longLine false

/-!
# Discharging the Gödel `Incompleteness` hypothesis via Foundation

Provenance: closes the imported hypothesis of `ALT/GodelCore.lean` (D4) — and hence the capstone
`ALT/Reflective.lean` — using upstream `FormalizedFormalLogic/Foundation` (pinned rev `b47cf447`,
Lean 4.31 + Mathlib v4.31), via `LO.FirstOrder.Arithmetic.exists_true_but_unprovable_sentence` (Gödel's first
incompleteness theorem for arithmetic theories `T` with `[T.Δ₁] [𝗥₀ ⪯ T] [T.SoundOnHierarchy 𝚺 1]`).

## The shared `Incompleteness` symbol
This file discharges the **literal** `GodelThreshold.Incompleteness` symbol — that is why D4's core
was factored into the lightweight `ALT/GodelCore.lean`, which both this file and
`ALT/GodelThreshold.lean` import, so the hypothesis assumed there is exactly the one proved here.
The two halves stay distinct terms by design:
* the **NNO-object** version (`reflective_of_depth`, depth = `cyclicParamNNO (gTS+1).depth`) stays
  on the Mathlib side, conditional on a hypothesis we PROVE satisfiable here;
* the **Foundation** side below uses a bare `M = gTS + 1` (= `cyclicParamNNO (gTS+1).depth`)
  and the shared `GodelCore.godel_threshold`.
`ALT/ExcessOrderComplete.lean` is where the two are finally composed, feeding this file's
discharge into the Mathlib-side excess statement.

## BAR / axioms — a ZERO-named-axiom core
`incompleteness_of_arith` (generic adapter) uses **standard axioms only** (`propext`,
`Classical.choice`, `Quot.sound`) — `Δ₁`/`𝗥₀ ⪯`/`ℕ↓[ℒₒᵣ] ⊧*` are HYPOTHESES, nothing concrete is
synthesized. This is the faithful §5.3-class statement: it applies to ANY `T` with `[T.Δ₁] [𝗥₀ ⪯ T]`
and `ℕ`-soundness (which covers §5.3's IΔ₀ abstractly). The two concrete `𝗜𝚺₁` witnesses below are
axiom-clean too — Foundation's `𝗜𝚺₁.Δ₁` definability is a theorem (`ISigma1_delta1Definable`) — so
this file, and with the `𝗣𝗔⁻`/`𝗜𝚺₁` capstones of `ALT/GodelChecker.lean` /
`ALT/GodelCheckerComplete.lean` the whole Foundation side, carries **no named axioms**.

## The concrete `𝗜𝚺₁` witnesses (also axiom-clean)
This file also ships two concrete `𝗜𝚺₁` witnesses: `isigma1_represents_underivable_truth`, and a
bounded-decision witness `isigma1_decides_bounded_nonprovability` over an abstract sound checker. Both
instantiate `exists_true_but_unprovable_sentence 𝗜𝚺₁`, whose `𝗜𝚺₁.Δ₁` requirement is met by
Foundation's `Δ₁`-definability *theorem* `LO.FirstOrder.Arithmetic.ISigma1_delta1Definable` (the
`𝗜𝚺₁`/`𝗣𝗔` `Δ₁`-definability, discharged upstream), so both are **fully axiom-clean**
(`#print axioms` = `propext, Classical.choice, Quot.sound`). They sit beside the `𝗣𝗔⁻` capstones
(`GodelChecker.paMinus_decides_bounded_nonprovability`,
`GodelCheckerComplete.paMinus_complete_decides`): since `𝗣𝗔⁻ ⊊ 𝗜𝚺₁`, unprovability in `𝗣𝗔⁻` is the
*weaker, more faithful* (§5.3-class) consequence, obtained without even the `Δ₁`-definability result
because `𝗣𝗔⁻` is finite (`Theory.Δ₁.ofFinite PeanoMinus.finite`); the `𝗜𝚺₁` forms are the parallel
witnesses at Foundation's canonical Σ₁-induction theory.

## Faithfulness to §5.3
`incompleteness_of_arith` is the general (§5.3-class) claim, instantiable at any Δ₁ arithmetic theory
with `𝗥₀ ⪯` and `ℕ`-soundness. Incompleteness holds all the way down `R₀ ⊊ Q ⊊ IΔ₀ ⊊ IΣ₁ ⊊ PA`; the
most faithful axiom-clean non-vacuity *witness* is `𝗣𝗔⁻` (finite, Δ₁ via `ofFinite`, on the
`GodelChecker` side), with `𝗜𝚺₁` the parallel witness one step up.

## What this does NOT establish (flagged)
* The generic adapter is a HYPOTHETICAL implication (it consumes `[T.Δ₁] [𝗥₀ ⪯ T]` and
  `ℕ`-soundness); the axiom-clean concrete non-vacuity witnesses are the finite `𝗣𝗔⁻` (most faithful)
  and its `𝗜𝚺₁` parallel.
* The NNO/CCC side keeps its D1/D2 stand-in caveats (combinatorial `ParamNNO` on finite `W`; CCC on
  `Type`) — not a unified `Rep(S)`; not a claim about a physical `Rep(S)`.
-/

namespace GodelComplete

open LO.FirstOrder LO.FirstOrder.Arithmetic

/-- Adapter (axiom-clean): for any arithmetic theory `T` with `Δ₁`-definability, `𝗥₀ ⪯ T`, and truth
in `ℕ` (which gives `SoundOnHierarchy 𝚺 1` for free), Foundation's first incompleteness theorem
discharges the literal `GodelThreshold.Incompleteness` — a sentence true in `ℕ` but unprovable in
`T`, with Gödel number its `Encodable.encode`. -/
theorem incompleteness_of_arith (T : ArithmeticTheory) [T.Δ₁] [𝗥₀ ⪯ T] [ℕ↓[ℒₒᵣ] ⊧* T] :
    ∃ gTS, GodelThreshold.Incompleteness (Encodable.encode : Sentence ℒₒᵣ → ℕ)
      (fun δ => T ⊢ δ) (fun δ => ℕ↓[ℒₒᵣ] ⊧ δ) gTS := by
  obtain ⟨δ, htrue, hunprov⟩ := exists_true_but_unprovable_sentence T
  exact ⟨Encodable.encode δ, δ, rfl, htrue, hunprov⟩

/-! ## The concrete `𝗜𝚺₁` witnesses (axiom-clean via the upstream `Δ₁`-definability theorem) -/

/-- Concrete chain result for `T = 𝗜𝚺₁`: a Gödel sentence of `𝗜𝚺₁`, true in `ℕ` but unprovable in
`𝗜𝚺₁`, is represented at depth `gTS + 1` — discharging the `GodelThreshold.Incompleteness` hypothesis
with NO remaining hypothesis. The depth `gTS + 1` equals
`(ParameterizedNNO.cyclicParamNNO (gTS + 1)).depth` (D1); the NNO-object form is
`GodelThreshold.reflective_of_depth` on the Mathlib side, kept a separate term here (see the
shared-symbol note above). Foundation's `𝗜𝚺₁.Δ₁` instance is a theorem
(`ISigma1_delta1Definable`, discharged upstream), so this witness is **fully axiom-clean**. -/
theorem isigma1_represents_underivable_truth :
    ∃ gTS : ℕ, GodelThreshold.RepresentsUnderivableTruth (Encodable.encode : Sentence ℒₒᵣ → ℕ)
      (fun δ => (𝗜𝚺₁ : ArithmeticTheory) ⊢ δ) (fun δ => ℕ↓[ℒₒᵣ] ⊧ δ) (gTS + 1) := by
  obtain ⟨gTS, hInc⟩ := incompleteness_of_arith 𝗜𝚺₁
  exact ⟨gTS, GodelThreshold.godel_threshold _ _ _ (gTS + 1) gTS (Nat.le_succ gTS) hInc⟩

/-- §6.3 L2b for the concrete `𝗜𝚺₁` witness, over an ABSTRACT sound checker. For any sound bounded
proof relation `Prf` on `Sentence ℒₒᵣ` (`sound`: accepts ⇒ `𝗜𝚺₁ ⊢`), the actual `𝗜𝚺₁` Gödel sentence
`G` (true in `ℕ`, unprovable in `𝗜𝚺₁`) is decided as bounded-non-provable — nothing within budget is
accepted (NO `sorry`, NO degenerate always-`false` checker). `ALT/GodelChecker.lean` supplies a
*concrete* computable `Prf` discharging the hypothesis (`isigma1_decides_bounded_nonprovability'`).
Foundation's `𝗜𝚺₁.Δ₁` instance is a theorem (`ISigma1_delta1Definable`, discharged upstream), so this
witness is **fully axiom-clean**. -/
theorem isigma1_decides_bounded_nonprovability
    (Prf : Sentence ℒₒᵣ → ℕ → Bool) (Mchk : ℕ)
    (sound : ∀ φ p, Prf φ p = true → (𝗜𝚺₁ : ArithmeticTheory) ⊢ φ) :
    ∃ G : Sentence ℒₒᵣ, (ℕ↓[ℒₒᵣ] ⊧ G) ∧ ((𝗜𝚺₁ : ArithmeticTheory) ⊬ G) ∧
      ∀ p, p ≤ Mchk → Prf G p = false := by
  obtain ⟨δ, htrue, hunprov⟩ := exists_true_but_unprovable_sentence 𝗜𝚺₁
  refine ⟨δ, htrue, hunprov, fun p _ => ?_⟩
  by_contra h
  rw [Bool.not_eq_false] at h
  exact hunprov (sound δ p h)

end GodelComplete
