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
# Discharging the Gödel `Incompleteness` hypothesis via Foundation (opt-in)

Provenance: closes the imported hypothesis of `ALT/GodelCore.lean` (D4) — and hence the capstone
`ALT/Reflective.lean` — using upstream `FormalizedFormalLogic/Foundation` (pinned rev `f6eed55`,
Lean 4.31 + Mathlib v4.31), via `LO.FirstOrder.Arithmetic.exists_true_but_unprovable_sentence` (Gödel's first
incompleteness theorem for arithmetic theories `T` with `[T.Δ₁] [𝗥₀ ⪯ T] [T.SoundOnHierarchy 𝚺 1]`).

**Opt-in / NOT wired into root `ALT.lean`.** Build explicitly with
`lake build ALT.GodelComplete`; routine formal builds stay Foundation-free.

## The import divide (an honest architectural fact, not a weakness)
This file discharges the **literal** `GodelThreshold.Incompleteness` symbol — that is why D4's core
was factored into the Mathlib-free `ALT/GodelCore.lean`, which both this file and
`ALT/GodelThreshold.lean` import. The two halves CANNOT be combined into one term:
`GodelComplete` (Foundation) and `GodelThreshold.reflective_of_depth` (Mathlib umbrella, via D1's
`ParamNNO`) can't co-exist in a single file: `Foundation.Vorspiel.Matrix`'s root `Matrix.map`
collides with the umbrella-Mathlib `Matrix.map`. So:
* the **NNO-object** version (`reflective_of_depth`, depth = `cyclicParamNNO (gTS+1).depth`) stays
  on the Mathlib side, now conditional on a hypothesis we PROVE satisfiable here;
* the **Foundation** side below uses a bare `M = gTS + 1` (= `cyclicParamNNO (gTS+1).depth`)
  and the shared `GodelCore.godel_threshold`.
Both halves share the `GodelThreshold.Incompleteness` symbol; they are just not one Lean term.

## BAR / axioms — a ZERO-named-axiom core (re-stated for this opt-in file)
`incompleteness_of_arith` (generic adapter) uses **standard axioms only** (`propext`,
`Classical.choice`, `Quot.sound`) — `Δ₁`/`𝗥₀ ⪯`/`ℕ↓[ℒₒᵣ] ⊧*` are HYPOTHESES, nothing concrete is
synthesized. This is the faithful §5.3-class statement: it applies to ANY `T` with `[T.Δ₁] [𝗥₀ ⪯ T]`
and `ℕ`-soundness (which covers §5.3's IΔ₀ abstractly). It is the sole `theorem` this file now ships,
so the file — and, with the `𝗣𝗔⁻` capstones of `ALT/GodelChecker.lean` /
`ALT/GodelCheckerComplete.lean`, the whole Foundation side — is axiom-clean.

## The retired `𝗜𝚺₁` witnesses (the zero-named-axiom hardening)
This file formerly also shipped a concrete `𝗜𝚺₁` witness (`isigma1_represents_underivable_truth`,
and a bounded-decision witness `isigma1_decides_bounded_nonprovability`). Both instantiated
`exists_true_but_unprovable_sentence 𝗜𝚺₁`, so both carried the single named axiom
`LO.FirstOrder.Arithmetic.ISigma1_delta1Definable` — Foundation's declared `axiom` for `𝗜𝚺₁.Δ₁` (its
explicit TODO "Prove `𝗜𝚺₁` and `𝗣𝗔` are Δ₁-definable"). They are **retired** so that the entire
built development contains **zero named axioms** anywhere. Nothing is lost: the axiom-clean `𝗣𝗔⁻`
capstones (`GodelChecker.paMinus_decides_bounded_nonprovability`,
`GodelCheckerComplete.paMinus_complete_decides`) are the *stronger, more faithful* (§5.3-class)
statements — `𝗣𝗔⁻ ⊊ 𝗜𝚺₁`, so unprovability in `𝗣𝗔⁻` is the weaker consequence — and are obtained
with **no** named axiom because `𝗣𝗔⁻` is finite (`Theory.Δ₁.ofFinite PeanoMinus.finite`). The `𝗜𝚺₁`
route remains fully reproducible from git history and is one-line restorable if upstream ever proves
`ISigma1_delta1Definable` (Foundation's TODO); an upstream-PR target.

## Faithfulness to §5.3
`incompleteness_of_arith` is the general (§5.3-class) claim, instantiable at any Δ₁ arithmetic theory
with `𝗥₀ ⪯` and `ℕ`-soundness. Incompleteness holds all the way down `R₀ ⊊ Q ⊊ IΔ₀ ⊊ IΣ₁ ⊊ PA`; the
axiom-clean non-vacuity *witness* is now `𝗣𝗔⁻` (finite, Δ₁ via `ofFinite`), on the `GodelChecker`
side.

## What this does NOT establish (flagged)
* The generic adapter is a HYPOTHETICAL implication (it consumes `[T.Δ₁] [𝗥₀ ⪯ T]` and
  `ℕ`-soundness); the axiom-clean concrete non-vacuity witness lives on the `𝗣𝗔⁻` side.
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

/-! ## Retired: the concrete `𝗜𝚺₁` witnesses

Two `𝗜𝚺₁` witnesses were retired here to keep the built development free of named axioms:

* `isigma1_represents_underivable_truth` — a Gödel sentence of `𝗜𝚺₁`, true in `ℕ` but unprovable in
  `𝗜𝚺₁`, represented at depth `gTS + 1` (discharging `GodelThreshold.Incompleteness` with no
  remaining hypothesis);
* `isigma1_decides_bounded_nonprovability` — the §6.3 L2b bounded-decision witness for the
  actual `𝗜𝚺₁` Gödel sentence (for any sound checker `Prf`, `Decide(G_{𝗜𝚺₁}) = true`).

Both went through `exists_true_but_unprovable_sentence 𝗜𝚺₁`, hence carried Foundation's single named
axiom `ISigma1_delta1Definable`. Their content is preserved, axiom-clean, by the `𝗣𝗔⁻` capstones on
the `GodelChecker`/`GodelCheckerComplete` sides (`𝗣𝗔⁻ ⊊ 𝗜𝚺₁`: the weaker, more faithful §5.3-class
consequence, `Δ₁` via `Theory.Δ₁.ofFinite`). Restore from git history if upstream proves
`ISigma1_delta1Definable` (an upstream-PR target). -/

end GodelComplete
