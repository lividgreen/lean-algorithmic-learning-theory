/-
Copyright (c) 2026 Mykola Palamarchuk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mykola Palamarchuk
-/
import ALT.BinaryKraft
import ALT.Ville

-- Formal-check file, not Mathlib-destined: opt out of the house-style header linter.
set_option linter.style.header false

/-!
# Search-phase pruned mass: the log-Bayes potential ([SQ] Appendix A, Claim 2, search half)

Provenance: [SQ], Appendix A "Soundness of SQ pruning", Claim 2,
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
* `search_phase_mass_charged`: the same bound with the chain's two remaining inputs — the initial
  potential bound and the per-path charge — themselves DERIVED, not assumed. `kraft_potential_init`
  gets `Φ_0 ≤ ln2·K(R)` from Kraft: the truth's *normalised* prior weight is `2^{−K(R)}/S` with
  total mass `S ≤ 1` (`BinaryKraft.indexed_tsum_le_one`), so dividing only raises it.
  `charge_identity` + `charge_of_posterior_model` get the charge as an *identity*: under the
  posterior step model (prune a normalised mass, renormalise, Bayes-update) the per-prune
  `−ln(1−m)` is exactly the potential drop plus the net Bayes rise, which telescopes to `ln(Z_n)`
  and is `< ln(1/δ)` on the no-excursion event.

## What this does NOT establish (stays modeled / imported; no overclaiming)
`search_phase_mass_charged` reduces the modeled content to a single **identification**: that the
`w, m, b, Z` of the posterior step model ARE the algorithm's own posterior weight, pruned masses,
Bayes factors, and renormalised survivor mixture. That is a modeling step, not an inequality — the
initial bound and the charge, formerly hypotheses, are now theorems of the model. The predictive
transfer of the pruned mass into regret ("`O(r)` pruned mass is absorbed into the `O(r)` regret",
the Bayes-mixture argument of [Discovery]) is machine-checked separately in `SQPredictiveTransfer`.
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

/-! ## The two modeled inputs, closed

The chain above takes the initial potential bound `hΦ0` and the per-path charge `hcharge` as
hypotheses.  Both are consequences of the posterior's own dynamics, and this section derives them.

**The initialization is Kraft.**  The truth's *normalized* prior weight is `w₀(R) = 2^{−K(R)}/S`,
where `S = ∑_{R'} 2^{−K(R')}` is the total mass of the unnormalized `2^{−K}` prior.  Kraft–McMillan
says `S ≤ 1` (`BinaryKraft`), so dividing by it can only *raise* the truth's weight:
`w₀(R) ≥ 2^{−K(R)}`, hence `Φ₀ = −ln w₀(R) ≤ ln2·K(R)`.

**The charge is a log identity plus Ville.**  Model one step of the truth's normalized posterior
weight as it actually moves: prune a normalized mass `m k` (renormalizing the survivors by
`1/(1−m k)`), then Bayes-update by the factor `b k`, so `w (k+1) = w k / (1 − m k) * b k`.  Taking
`−ln` turns that product into a sum, and the per-step identity

    −ln(1 − m k)  =  (Φ k − Φ (k+1))  +  (−ln (b k))

says exactly what the potential argument claims: *the charge of a prune is its potential drop plus
whatever the Bayes update gave back.*  Summing over the phase (`charge_identity`) leaves the net
Bayes rise `∑ (−ln (b k))` as the only slack — and that is what Ville controls.  In
likelihood-ratio units the Bayes factor is the reciprocal of the mixture's ratio-growth,
`b k = Z k / Z (k+1)`, so the rise telescopes to `ln (Z n) − ln (Z 0) = ln (Z n)`
(`bayes_rise_telescope`), which on the no-excursion event `{∀ t, Z t < 1/δ}` is `< ln(1/δ)`.

`Z` here is the mixture the pruning algorithm actually carries: the *renormalized* mass of the
surviving candidates (`Z 0 = 1`, and `Z (k+1) / Z k` is the survivors' Bayes growth).  It is the
same `Z` in all three roles — Ville's supermartingale, the no-excursion event, and the Bayes
factors — which is what makes the capstone a single coherent statement.  The unpruned mixture
`Σ w(R')·L_t(R')` is the `m ≡ 0` case of that shape.

## What remains modeled

Only the *identification*: that the algorithm's posterior weight, pruned masses, Bayes factors and
mixture are the `w`, `m`, `b`, `Z` of this model.  The inequalities themselves are no longer
assumed. -/

/-- `Φ₀ ≤ ln2·K` whenever the truth's normalized prior weight is at least `2^{−K}`: the potential
is a `−ln` of a weight, and `−ln` is antitone. -/
theorem potential_init_le (K : ℕ) (w₀ : ℝ) (hw₀ : (1 / 2 : ℝ) ^ K ≤ w₀) :
    -Real.log w₀ ≤ Real.log 2 * K := by
  have hpos : (0 : ℝ) < (1 / 2 : ℝ) ^ K := by positivity
  have hlog : Real.log ((1 / 2 : ℝ) ^ K) ≤ Real.log w₀ := Real.log_le_log hpos hw₀
  have hval : Real.log ((1 / 2 : ℝ) ^ K) = -(Real.log 2 * K) := by
    rw [Real.log_pow, one_div, Real.log_inv]; ring
  rw [hval] at hlog
  linarith

/-- **The Kraft initialization.**  Normalizing the unnormalized `2^{−K}` prior by its total mass
`S` gives the truth weight `2^{−K(R)}/S`; Kraft–McMillan says `S ≤ 1`, so the division only raises
it, and `Φ₀ = −ln(2^{−K(R)}/S) ≤ ln2·K(R)`.  Sub-normalization is the whole content: a prior that
summed to more than `1` could leave the truth with a weight below `2^{−K(R)}`, and the bound would
fail. -/
theorem kraft_potential_init (K : ℕ) (S : ℝ) (hS0 : 0 < S) (hS1 : S ≤ 1) :
    -Real.log ((1 / 2 : ℝ) ^ K / S) ≤ Real.log 2 * K := by
  refine potential_init_le K _ ?_
  have hpos : (0 : ℝ) < (1 / 2 : ℝ) ^ K := by positivity
  rw [le_div_iff₀ hS0]
  nlinarith

/-- **The Kraft initialization, with Kraft supplied.**  For a hypothesis class presented by an
injective, uniquely-decodable binary code, the `2^{−ℓ}` prior's total mass lies in `(0,1]` by
Kraft–McMillan (`BinaryKraft.indexed_tsum_pos`, `BinaryKraft.indexed_tsum_le_one`), so the
initial-potential bound `Φ₀ ≤ ln2·ℓ(R)` is *derived*, with no assumed normalizer. -/
theorem kraft_potential_init_of_code {ι : Type*} (code : ι → List Bool)
    (hinj : Function.Injective code)
    (hUD : InformationTheory.UniquelyDecodable (Set.range code)) (R : ι) :
    -Real.log ((1 / 2 : ℝ) ^ (code R).length / ∑' i, (1 / 2 : ℝ) ^ (code i).length)
      ≤ Real.log 2 * (code R).length :=
  kraft_potential_init _ _
    (BinaryKraft.indexed_tsum_pos code hinj hUD R)
    (BinaryKraft.indexed_tsum_le_one code hinj hUD)

/-- **The charge identity.**  Under the posterior step model — prune a normalized mass `m k`
(renormalizing by `1/(1−m k)`), then Bayes-update by `b k` — the accumulated charge of the prunes
is *exactly* the telescoped potential drop plus the net Bayes rise.  No inequality is involved: the
step is a product, and `−ln` turns it into a sum. -/
theorem charge_identity (w m b : ℕ → ℝ) (n : ℕ)
    (hw : ∀ k, 0 < w k) (hm : ∀ k, m k < 1) (hb : ∀ k, 0 < b k)
    (hstep : ∀ k, w (k + 1) = w k / (1 - m k) * b k) :
    ∑ k ∈ Finset.range n, (-Real.log (1 - m k))
      = (∑ k ∈ Finset.range n, (-Real.log (w k) - -Real.log (w (k + 1))))
        + ∑ k ∈ Finset.range n, (-Real.log (b k)) := by
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  have h1m : (0 : ℝ) < 1 - m k := by linarith [hm k]
  have hquot : w k / (1 - m k) ≠ 0 := ne_of_gt (div_pos (hw k) h1m)
  have hlog : Real.log (w (k + 1))
      = Real.log (w k) - Real.log (1 - m k) + Real.log (b k) := by
    rw [hstep k, Real.log_mul hquot (ne_of_gt (hb k)),
      Real.log_div (ne_of_gt (hw k)) (ne_of_gt h1m)]
  linarith

/-- **The net Bayes rise telescopes.**  In likelihood-ratio units the truth's own likelihood is `1`,
so the Bayes factor is the reciprocal of the mixture's ratio-growth, `b k = Z k / Z (k+1)`, and the
accumulated rise collapses to `ln (Z n) − ln (Z 0)`. -/
theorem bayes_rise_telescope (Z b : ℕ → ℝ) (n : ℕ) (hZ : ∀ k, 0 < Z k)
    (hb : ∀ k, b k = Z k / Z (k + 1)) :
    ∑ k ∈ Finset.range n, (-Real.log (b k)) = Real.log (Z n) - Real.log (Z 0) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih, hb n,
        Real.log_div (ne_of_gt (hZ n)) (ne_of_gt (hZ (n + 1)))]
      ring

/-- **The net Bayes rise is `≤ ln(1/δ)` on the no-excursion event.**  The rise telescopes to
`ln (Z n)` (the mixture starts normalized, `Z 0 = 1`), and on `{∀ t, Z t < 1/δ}` that is
`< ln(1/δ)`.  This is the *only* place the probabilistic input enters the charge. -/
theorem bayes_rise_le_of_no_excursion (Z b : ℕ → ℝ) (n : ℕ) (δ : ℝ)
    (hZ : ∀ k, 0 < Z k) (hZ0 : Z 0 = 1) (hb : ∀ k, b k = Z k / Z (k + 1))
    (hno : ∀ t, Z t < 1 / δ) :
    ∑ k ∈ Finset.range n, (-Real.log (b k)) ≤ Real.log (1 / δ) := by
  rw [bayes_rise_telescope Z b n hZ hb, hZ0, Real.log_one, sub_zero]
  exact Real.log_le_log (hZ n) (hno n).le

/-- **The per-path charge, derived.**  The hypothesis `hcharge` of `search_phase_mass_ville_chain`
— assumed until now — follows from the posterior step model: the charge identity accounts for every
prune exactly (`charge_identity`), and the leftover net Bayes rise is `≤ ln(1/δ)` on the
no-excursion event (`bayes_rise_le_of_no_excursion`). -/
theorem charge_of_posterior_model (w m b Z : ℕ → ℝ) (n : ℕ) (δ : ℝ)
    (hw : ∀ k, 0 < w k) (hm : ∀ k, m k < 1)
    (hZ : ∀ k, 0 < Z k) (hZ0 : Z 0 = 1) (hb : ∀ k, b k = Z k / Z (k + 1))
    (hstep : ∀ k, w (k + 1) = w k / (1 - m k) * b k)
    (hno : ∀ t, Z t < 1 / δ) :
    ∑ k ∈ Finset.range n, (-Real.log (1 - m k))
      ≤ (∑ k ∈ Finset.range n, (-Real.log (w k) - -Real.log (w (k + 1))))
        + Real.log (1 / δ) := by
  have hbpos : ∀ k, 0 < b k := fun k => by rw [hb k]; exact div_pos (hZ k) (hZ (k + 1))
  rw [charge_identity w m b n hw hm hbpos hstep]
  have := bayes_rise_le_of_no_excursion Z b n δ hZ hZ0 hb hno
  linarith

section ChargedChain

open MeasureTheory
open scoped ProbabilityTheory

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} {ℱ : Filtration ℕ m0}

/-- **The search-phase mass bound, with both modeled inputs discharged** (Appendix A Claim 2, search
phase).  With probability `≥ 1−δ`, the accumulated search-phase pruned mass is at most
`ln2·K(R) + ln(1/δ)` — the paper's `O(r + log(1/δ))`.

Against `search_phase_mass_ville_chain`, the two hypotheses that were *inequalities about the
potential* are gone, replaced by the posterior's dynamics:

* the initial bound `Φ₀ ≤ ln2·K(R)` is now `hinit` — the truth's normalized prior weight is at
  least `2^{−K(R)}`, which is Kraft (`kraft_potential_init`, `kraft_potential_init_of_code`);
* the per-path charge is now `hstep` + `hbayes` — the posterior prunes-then-updates, and the Bayes
  factor is the surviving mixture's reciprocal ratio-growth (`charge_of_posterior_model`).

What is left is the identification of `w`, `m`, `b`, `Z` with the algorithm's posterior, pruned
masses, Bayes factors and renormalized survivor mixture — a modeling step, not an inequality. -/
theorem search_phase_mass_charged [IsProbabilityMeasure μ]
    (Z : ℕ → Ω → ℝ) (hsuper : Supermartingale Z ℱ μ)
    (hZpos : ∀ k ω, 0 < Z k ω) (hZone : ∀ ω, Z 0 ω = 1)
    (δ : ℝ) (hδ0 : 0 < δ)
    (w m b : Ω → ℕ → ℝ) (n K : ℕ)
    (hw : ∀ ω k, 0 < w ω k) (hw1 : ∀ ω k, w ω k ≤ 1)
    (hinit : ∀ ω, (1 / 2 : ℝ) ^ K ≤ w ω 0)
    (hm : ∀ ω k, m ω k < 1)
    (hstep : ∀ ω k, w ω (k + 1) = w ω k / (1 - m ω k) * b ω k)
    (hbayes : ∀ ω k, b ω k = Z k ω / Z (k + 1) ω) :
    μ {ω | Real.log 2 * K + Real.log (1 / δ) < ∑ k ∈ Finset.range n, m ω k}
      ≤ ENNReal.ofReal δ := by
  have hnn : ∀ k ω, 0 ≤ Z k ω := fun k ω => (hZpos k ω).le
  have hZ0 : μ[Z 0] ≤ 1 := by
    have hcongr : ∫ ω, Z 0 ω ∂μ = ∫ _ω, (1 : ℝ) ∂μ :=
      integral_congr_ae (Filter.Eventually.of_forall hZone)
    rw [hcongr, integral_const]
    simp
  exact search_phase_mass_ville_chain Z hsuper hnn hZ0 δ hδ0
    (fun _ => Finset.range n) m (fun ω k => -Real.log (w ω k)) n (Real.log 2 * K)
    (fun ω i _ => hm ω i)
    (fun ω => potential_init_le K (w ω 0) (hinit ω))
    (fun ω => neg_nonneg.mpr (Real.log_nonpos (hw ω n).le (hw1 ω n)))
    (fun ω hno =>
      charge_of_posterior_model (w ω) (m ω) (b ω) (fun k => Z k ω) n δ
        (hw ω) (hm ω) (fun k => hZpos k ω) (hZone ω) (hbayes ω) (hstep ω) hno)

end ChargedChain

end SQSearchPhaseMass
