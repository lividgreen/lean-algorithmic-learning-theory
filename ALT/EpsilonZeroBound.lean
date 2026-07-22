/-
Copyright (c) 2026 Mykola Palamarchuk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mykola Palamarchuk
-/
import Mathlib

-- Formal-check file, not Mathlib-destined: opt out of the house-style header linter.
set_option linter.style.header false

/-!
# The explicit ε₀ lower bound ([Discovery] §3.3 / Theorem 3.1)

Provenance: [Discovery], §3.3 / Theorem 3.1. `ε₀` is the minimum
squared-Hellinger separation between the true rule `R` and any competitor in the model class; it
sits in `T_discover = O(r · log(1/δ) / ε₀²)` and is inherited by [SQ].

There is NO universal lower bound on `ε₀` — parity-type classes drive it to zero (that is
`ALT/ParityCounterexample.lean` / FV-A3). So this module does not bound `ε₀` in general; it
DEMOTES `ε₀` from a factor hidden in the big-O to an explicit, named class parameter: `ε₀` as a
minimum over the class, its strict positivity, an explicit lower bound for "well-separated"
classes, and the
resulting conditional polynomial discovery bound.

Status: PROVED as pure `Finset` / real arithmetic. A thin supporting win (cf. `PolyTimeAccounting`).

## What this DOES establish
* `eps0 := M.inf' hM sep`: `ε₀` as the least separation over a finite nonempty model class.
* `eps0_pos`: `ε₀ > 0` when every competitor is strictly separated from `R` (realizability +
  distinctness).
* `eps0_ge_of_separated`: for a `γ`-separated class, the explicit lower bound `ε₀ ≥ γ` — the
  demotion of `ε₀` to a named class parameter. Plus `eps0_le_sep` (`ε₀ ≤ sep i` per competitor `i`).
* `Tdiscover` + `Tdiscover_le_of_separated`: discovery time as an EXPLICIT function of `ε₀` (the
  `1/ε₀²` in the open, not hidden in the big-O), bounded by its value at the floor `γ` for a
  `γ`-separated class — polynomial in `r` when `γ = Ω(1/poly r)`. Plus `Tdiscover_antitone`.

## What this does NOT establish (flagged)
* NO universal `ε₀` lower bound is claimed — none exists; parity-type classes drive `ε₀ → 0`
  (`ALT/ParityCounterexample.lean` / FV-A3). This file only demotes `ε₀` to an explicit class
  parameter `γ` and gives the CONDITIONAL bound.
* `sep : ι → ℝ` abstractly models the squared-Hellinger separation `d_H²(P_R, P_{R_i})` as a real
  per competitor; the measure-theoretic Hellinger distance is NOT constructed here (deferred — would
  need probability machinery).
* Ties to [Discovery] Theorem 3.1 by making the `ε₀`-dependence explicit; the constant `c` and the
  discovery / concentration analysis itself (Grünwald–Mehta) stay IMPORTED (the FV-7 / §3 boundary),
  not re-proved.
* Pure arithmetic / reparametrization-level; no new learning-theory content.

## Hypotheses: paper-stated vs added
* Paper-stated / faithful: `ε₀` as the min separation; `T_discover ∝ 1/ε₀²` (Thm 3.1); the
  separated-class regime.
* Added / modeling: `M : Finset ι` (finite class), `sep : ι → ℝ` (abstract separation); the
  `γ`-separation floor and nonnegativity hypotheses are named, not derived.
-/

namespace EpsilonZeroBound

open Real Finset

/-- ε₀ ([Discovery] §3.3): the least squared-Hellinger separation between the true rule `R` and any
competitor in the finite nonempty model class.
`sep i` models `d_H²(P_R, P_{R_i})`; ε₀ is its infimum over the class. -/
noncomputable def eps0 {ι : Type*} (M : Finset ι) (hM : M.Nonempty) (sep : ι → ℝ) : ℝ :=
  M.inf' hM sep

/-- ε₀ is strictly positive when every competitor is strictly separated from `R` (realizability +
distinctness). -/
theorem eps0_pos {ι : Type*} {M : Finset ι} (hM : M.Nonempty) {sep : ι → ℝ}
    (h : ∀ i ∈ M, 0 < sep i) : 0 < eps0 M hM sep :=
  (Finset.lt_inf'_iff hM).mpr h

/-- A `γ`-separated class ⇒ the explicit lower bound `ε₀ ≥ γ`: this is the demotion of ε₀ from a
hidden factor to a named class parameter. -/
theorem eps0_ge_of_separated {ι : Type*} {M : Finset ι} (hM : M.Nonempty) {sep : ι → ℝ} {γ : ℝ}
    (h : ∀ i ∈ M, γ ≤ sep i) : γ ≤ eps0 M hM sep :=
  (Finset.le_inf'_iff hM sep).mpr h

/-- ε₀ is at most every competitor's separation. -/
theorem eps0_le_sep {ι : Type*} {M : Finset ι} (hM : M.Nonempty) {sep : ι → ℝ} {i : ι}
    (hi : i ∈ M) : eps0 M hM sep ≤ sep i :=
  Finset.inf'_le sep hi

/-- Discovery time as an EXPLICIT function of ε₀ ([Discovery] Thm 3.1): the `1/ε₀²` is in the
open, not hidden in the big-O. -/
noncomputable def Tdiscover (c r δ ε0 : ℝ) : ℝ :=
  c * (r * Real.log 2 + Real.log (1 / δ)) / ε0 ^ 2

/-- The hidden cost made explicit and conditionally polynomial: for a `γ`-separated class
(`ε₀ ≥ γ > 0`), the discovery time is bounded by its value at the floor `γ` — i.e.
`c·(r·ln2 + log(1/δ))/γ²`, polynomial in `r` when `γ = Ω(1/poly r)`. -/
theorem Tdiscover_le_of_separated {c r δ ε0 γ : ℝ} (hc : 0 ≤ c)
    (hnum : 0 ≤ r * Real.log 2 + Real.log (1 / δ)) (hγ : 0 < γ) (hε : γ ≤ ε0) :
    Tdiscover c r δ ε0 ≤ Tdiscover c r δ γ := by
  unfold Tdiscover
  gcongr

/-- `Tdiscover` is antitone in `ε₀` on `(0, ∞)` (when the numerator is nonnegative). -/
theorem Tdiscover_antitone {c r δ : ℝ} (hc : 0 ≤ c)
    (hnum : 0 ≤ r * Real.log 2 + Real.log (1 / δ)) :
    AntitoneOn (fun ε0 => Tdiscover c r δ ε0) (Set.Ioi 0) := by
  intro a ha _ _ hab
  exact Tdiscover_le_of_separated hc hnum ha hab

end EpsilonZeroBound
