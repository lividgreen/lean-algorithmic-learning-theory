/-
Copyright (c) 2026 Mykola Palamarchuk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mykola Palamarchuk
-/
import Mathlib
import ALT.Ville

-- Formal-check file, not Mathlib-destined: opt out of the house-style header linter.
set_option linter.style.header false

/-!
# Search-phase pruned mass: the log-Bayes potential (Paper III Appendix A, Claim 2, search half)

Provenance: Paper III, Appendix A "Soundness of SQ pruning", Claim 2,
the **search-phase** (`t < T_discover`) residual gap. Companion to
`ALT/SQPrunedMass.lean` (FV-F), which handles only the post-discovery half.

The prose flags the search phase open because the per-competitor bound
`w_t(R') ≤ w(R')·2^{K(R)}·exp(−2tε₀)` keeps an un-killed `2^{K(R)}` prefactor there. The resolution
is a **log-Bayes potential** the naive bound ignores: with
`Φ_t := −ln w_t(R)` (truth's normalized-posterior potential, in nats), `Φ_0 ≤ ln2·K(R)` (Kraft) and
`Φ_t ≥ 0`; a renormalization-prune of a competitor with normalized mass `m` drops `Φ` by
`−ln(1 − m) ≥ m`. Summing, the accumulated pruned mass is `≤ Φ_0 ≤ ln2·K(R) = O(r)` — the RIGHT
order (discovery regret), not `δ/2`.

`C` below is the potential range in nats, `= ln2·K(R) = O(r)`.

## What this DOES establish
* `search_phase_pruned_mass_le`: given the per-prune charge to a bounded potential `Φ` on `[0,K]`
  (hypotheses `hΦ0`, `hΦn`, `hcharge`), the accumulated pruned mass `∑ m i ≤ K`. The NEW elementary
  content is the pointwise `m ≤ −ln(1 − m)` (mass ≤ its log-drop) summed over the pruned set, then
  charged to the potential's total decrease.
* `potential_range`: the telescoping `∑ (Φ k − Φ (k+1)) = Φ 0 − Φ n ≤ K` for a potential with
  `Φ 0 ≤ K`, `Φ n ≥ 0` — the "potential lies in `[0,K]`" half, elementary.
* `pruned_mass_le_budget`: the slack form — the per-prune charge may exceed the telescoped
  potential drop by an additive budget `B` (the between-pruning Bayesian-update net rise); the mass
  bound degrades to `C + B`. This is the deterministic core the Ville chain rests on, with
  `B = ln(1/δ)`.
* `search_phase_mass_ville_chain`: the chained probabilistic capstone. With `Z_t` a non-negative
  supermartingale (`𝔼[Z_0] ≤ 1`; realizable likelihood-ratio mixture) and the per-path charge
  valid on the no-excursion event `{∀ t, Z_t < 1/δ}`, the accumulated pruned mass exceeds
  `C + ln(1/δ)` only on the Ville excursion event, so `μ{mass > C + ln(1/δ)} ≤ δ` — the paper's
  `O(r + log(1/δ))` w.h.p. bound. The `ln(1/δ)` term is DERIVED from `Ville.ville_potential_budget`,
  not assumed: the two cores (log-Bayes potential drop and Ville excursion control) are now
  formally chained.

## What this does NOT establish (stays modeled / imported; no overclaiming)
The two cores ARE now chained (`search_phase_mass_ville_chain`); the `ln(1/δ)` excursion term is
derived from the proved `Ville.ville_potential_budget` (`ALT/Ville.lean`): for a non-negative
supermartingale `Z_t` with `𝔼[Z_0] ≤ 1`, `μ{∃ t, 1/δ ≤ Z_t} ≤ δ` (Ville at `λ = 1/δ`). What stays
modeled shrinks to:
* (i) the **supermartingale premise** on `Z_t`: that `Z_t = ∑ w(R')·L_t(R')` is a non-negative
  supermartingale with `𝔼[Z_0] ≤ 1` (realizability) — passed as `hsuper`,
  `hnn`, `hZ0`.
* (ii) the **Kraft bound** `Φ_0 ≤ ln2·K(R)` (from `∑ w ≤ 1`, a Paper II fact) and the identification
  `C = ln2·K(R)` — supplied numerically by the caller (`hΦ0`).
* (iii) the **conditional per-path charge** `hcharge` (per-prune log-drop `+` the Bayes-update net
  rise `≤ ln(1/δ)`, VALID ON the no-excursion event `{∀ t, Z_t < 1/δ}`) and the predictive-transfer
  semantics ("`O(r)` pruned mass is absorbed into the `O(r)` regret", the Bayes-mixture argument of
  Paper II).
-/

namespace SQSearchPhaseMass

/-- The potential range: for a real potential `Φ` with `Φ 0 ≤ K` and `Φ n ≥ 0`, the telescoped
total of its per-step drops is `≤ K`. (No monotonicity needed for the bound itself.) -/
theorem potential_range (Φ : ℕ → ℝ) (n : ℕ) (K : ℝ)
    (hΦ0 : Φ 0 ≤ K) (hΦn : 0 ≤ Φ n) :
    ∑ k ∈ Finset.range n, (Φ k - Φ (k + 1)) ≤ K := by
  have htel : ∑ k ∈ Finset.range n, (Φ k - Φ (k + 1)) = Φ 0 - Φ n := by
    -- primary: `Finset.sum_range_sub' Φ n`
    -- fallback if the name/direction is off:
    --   induction n with
    --   | zero => simp
    --   | succ n ih => rw [Finset.sum_range_succ, ih]; ring
    simpa using Finset.sum_range_sub' Φ n
  rw [htel]; linarith

/-- FV-G (Appendix A Claim 2, search-phase half): the accumulated search-phase pruned mass is
`≤ K` (`= ln2·K(R) = O(r)`), by the log-Bayes potential. Each pruned competitor's normalized mass
`m i` is `≤ −ln(1 − m i)` (its potential drop, in nats); these are charged to the truth-potential
`Φ` on `[0,K]` (`hcharge`), whose total decrease telescopes to `≤ K` (`potential_range`). -/
theorem search_phase_pruned_mass_le
    {ι : Type*} (pruned : Finset ι) (m : ι → ℝ) (Φ : ℕ → ℝ) (n : ℕ) (K : ℝ)
    (hm1 : ∀ i ∈ pruned, m i < 1)
    (hΦ0 : Φ 0 ≤ K) (hΦn : 0 ≤ Φ n)
    (hcharge : ∑ i ∈ pruned, (-Real.log (1 - m i))
                 ≤ ∑ k ∈ Finset.range n, (Φ k - Φ (k + 1))) :
    ∑ i ∈ pruned, m i ≤ K := by
  have hstep : ∀ i ∈ pruned, m i ≤ -Real.log (1 - m i) := by
    intro i hi
    have hpos : (0:ℝ) < 1 - m i := by linarith [hm1 i hi]
    have hlog : Real.log (1 - m i) ≤ (1 - m i) - 1 := Real.log_le_sub_one_of_pos hpos
    linarith
  calc ∑ i ∈ pruned, m i
      ≤ ∑ i ∈ pruned, (-Real.log (1 - m i)) := Finset.sum_le_sum hstep
    _ ≤ ∑ k ∈ Finset.range n, (Φ k - Φ (k + 1)) := hcharge
    _ ≤ K := potential_range Φ n K hΦ0 hΦn

/-- Slack form of `search_phase_pruned_mass_le`: the charge may exceed the telescoped potential
drop by an additive budget `B` (the Bayesian-update net rise); the mass bound degrades to `C + B`.
The deterministic core the Ville chain rests on — with `B = ln(1/δ)` supplying the between-pruning
net rise valid on the no-excursion event. -/
theorem pruned_mass_le_budget
    {ι : Type*} (pruned : Finset ι) (m : ι → ℝ) (Φ : ℕ → ℝ) (n : ℕ) (C B : ℝ)
    (hm1 : ∀ i ∈ pruned, m i < 1)
    (hΦ0 : Φ 0 ≤ C) (hΦn : 0 ≤ Φ n)
    (hcharge : ∑ i ∈ pruned, (-Real.log (1 - m i))
                 ≤ (∑ k ∈ Finset.range n, (Φ k - Φ (k + 1))) + B) :
    ∑ i ∈ pruned, m i ≤ C + B := by
  have hstep : ∀ i ∈ pruned, m i ≤ -Real.log (1 - m i) := by
    intro i hi
    have hpos : (0:ℝ) < 1 - m i := by linarith [hm1 i hi]
    have hlog : Real.log (1 - m i) ≤ (1 - m i) - 1 := Real.log_le_sub_one_of_pos hpos
    linarith
  have hpot : ∑ k ∈ Finset.range n, (Φ k - Φ (k + 1)) ≤ C := potential_range Φ n C hΦ0 hΦn
  calc ∑ i ∈ pruned, m i
      ≤ ∑ i ∈ pruned, (-Real.log (1 - m i)) := Finset.sum_le_sum hstep
    _ ≤ (∑ k ∈ Finset.range n, (Φ k - Φ (k + 1))) + B := hcharge
    _ ≤ C + B := by linarith

section VilleChain

open MeasureTheory
open scoped ProbabilityTheory

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} {ℱ : Filtration ℕ m0}

/-- FV-G chained (Appendix A Claim 2, search phase, w.h.p. form): the accumulated search-phase
pruned mass exceeds `C + ln(1/δ)` only on the Ville excursion event, so with probability `≥ 1−δ`
it is `≤ C + ln(1/δ)` (`C = ln2·K(R)`, giving the paper's `O(r + log(1/δ))`). The `ln(1/δ)` term
is DERIVED from `Ville.ville_potential_budget`, not assumed. Modeled premises, now minimal and
named: `Z_t` is a non-negative supermartingale with `𝔼[Z_0] ≤ 1` (realizable likelihood-ratio
mixture), the Kraft bound `hΦ0`, and the per-path charge `hcharge` — the
per-prune log-drop plus the Bayes-update net rise `≤ ln(1/δ)` VALID ON the no-excursion event,
which is exactly the paper's "w.p. ≥ 1−δ (Ville)" semantics. -/
theorem search_phase_mass_ville_chain [IsFiniteMeasure μ]
    (Z : ℕ → Ω → ℝ) (hsuper : Supermartingale Z ℱ μ) (hnn : ∀ n ω, 0 ≤ Z n ω)
    (hZ0 : μ[Z 0] ≤ 1) (δ : ℝ) (hδ0 : 0 < δ)
    {ι : Type*} (pruned : Ω → Finset ι) (m : Ω → ι → ℝ) (Φ : Ω → ℕ → ℝ) (n : ℕ) (C : ℝ)
    (hm1 : ∀ ω, ∀ i ∈ pruned ω, m ω i < 1)
    (hΦ0 : ∀ ω, Φ ω 0 ≤ C) (hΦn : ∀ ω, 0 ≤ Φ ω n)
    (hcharge : ∀ ω, (∀ t, Z t ω < 1 / δ) →
        ∑ i ∈ pruned ω, (-Real.log (1 - m ω i))
          ≤ (∑ k ∈ Finset.range n, (Φ ω k - Φ ω (k + 1))) + Real.log (1 / δ)) :
    μ {ω | C + Real.log (1 / δ) < ∑ i ∈ pruned ω, m ω i} ≤ ENNReal.ofReal δ := by
  have hsub : {ω | C + Real.log (1 / δ) < ∑ i ∈ pruned ω, m ω i}
              ⊆ {ω | ∃ t, 1 / δ ≤ Z t ω} := by
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω ⊢
    by_contra h
    simp only [not_exists, not_le] at h
    have hbound := pruned_mass_le_budget (pruned ω) (m ω) (Φ ω) n C (Real.log (1 / δ))
      (hm1 ω) (hΦ0 ω) (hΦn ω) (hcharge ω h)
    linarith
  exact (measure_mono hsub).trans (Ville.ville_potential_budget Z hsuper hnn hZ0 δ hδ0)

end VilleChain

end SQSearchPhaseMass
