/-
Copyright (c) 2026 Mykola Palamarchuk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mykola Palamarchuk
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic

-- Formal-check file, not Mathlib-destined: opt out of the house-style header linter.
set_option linter.style.header false

/-!
# Post-discovery pruned mass: competitor-decay + Kraft ([SQ] Appendix A, Claim 2)

Provenance: [SQ], Appendix A "Soundness of SQ pruning", Claim 2
(the accumulated pruned mass is `≤ δ/2`).  This file supplies the **post-discovery half** of that
claim: once the search has run past `T_discover`, the total posterior mass ever assigned to pruned
competitors is `≤ δ/2`, established by competitor decay + the Kraft inequality **alone** — with *no*
maximal inequality (Doob/Ville), which is the part the prose defers to a martingale tail bound.

This is the companion to `ALT/SQVersionSpace.lean` (FV-A4, "truth survives pruning") and
`ALT/SQOracle.lean` (FV-E, the empirical-answer concentration): there the geometry of a *single*
pruning step is proved; here the *accumulated* mass across the whole pruned set is summed & bounded.

Like `ALT/SampleComplexity.lean` (FV-B2) this file reuses [Discovery] as **imported hypotheses**
rather than re-deriving it: the per-competitor posterior bound
`wt i ≤ w i · 2^K · exp(−2tε₀)` is taken as the hypothesis `hdecay`, which bundles two cited facts —
the likelihood decay `L_t(R') ≤ exp(−2tε₀)` ([Discovery] `DeterministicDiscovery`) and the
normaliser lower bound `Z_t ≥ w(R) = 2^{−K}`.  The NEW content proved here is exactly the two steps
the paper leaves implicit:

* `prefactor_le`: killing the `2^K` prefactor past `T_discover` — for
  `t ≥ (K·log 2 + log(2/δ))/(2ε₀)`, geometric decay drives `2^K · exp(−2tε₀) ≤ δ/2`.
* `accumulated_pruned_mass_le`: the Kraft sum — the prefactor bound is *uniform in `t`* across the
  pruned set, so summing the per-competitor decay over `pruned` with Kraft `∑ w ≤ 1` gives
  `∑ wt ≤ δ/2`.

Notational note: `2^K` is written `Real.exp (K * Real.log 2)` throughout, so that `K : ℝ` (the
description length in nats-vs-bits is absorbed into `K`) and the algebra stays inside the
`Real.exp`/`Real.log` API.

## What this DOES establish
* The post-discovery accumulated pruned mass is `≤ δ/2`, from `hdecay` (decay × normaliser) and
  `hkraft` (`∑ w ≤ 1`) — i.e. Appendix A Claim 2's second half, with no maximal inequality.

## What this does NOT establish (stays in prose; no overclaiming)
* Not the pre-discovery half of Claim 2 (the transient `t < T_discover` mass), which is the
  martingale / maximal-inequality argument the paper cites — this file is explicitly the
  *post-`T_discover`* contribution.
* Not the decay `L_t(R') ≤ exp(−2tε₀)` nor the normaliser `Z_t ≥ 2^{−K}`: those are the [Discovery]
  `DeterministicDiscovery` facts, imported here pre-bundled as the single hypothesis `hdecay`.
* Not the union with `ALT/SQOracle.lean`'s `1−δ` truth-survival into a single `1−δ` soundness
  statement: that final assembly stays in prose (it is the Bayes-mixture argument of [Discovery]).
-/

namespace SQPrunedMass

/-- Past `T_discover`, geometric decay kills the `2^K` prefactor: for
`t ≥ (K·log 2 + log(2/δ))/(2ε₀)`, `2^K · exp(−2tε₀) ≤ δ/2` (with `2^K = exp(K·log 2)`). -/
theorem prefactor_le
    (K t ε₀ δ : ℝ) (hδ0 : 0 < δ) (hε₀ : 0 < ε₀)
    (ht : (K * Real.log 2 + Real.log (2 / δ)) / (2 * ε₀) ≤ t) :
    Real.exp (K * Real.log 2) * Real.exp (-2 * t * ε₀) ≤ δ / 2 := by
  have h2ε : 0 < 2 * ε₀ := by positivity
  rw [div_le_iff₀ h2ε] at ht
  have hmul : t * (2 * ε₀) = 2 * t * ε₀ := by ring
  have hlogdiv : Real.log (2 / δ) = - Real.log (δ / 2) := by
    rw [← Real.log_inv, inv_div]
  have hlog : K * Real.log 2 - 2 * t * ε₀ ≤ Real.log (δ / 2) := by
    linarith [ht, hmul, hlogdiv]
  calc Real.exp (K * Real.log 2) * Real.exp (-2 * t * ε₀)
      = Real.exp (K * Real.log 2 + (-2 * t * ε₀)) := (Real.exp_add _ _).symm
    _ = Real.exp (K * Real.log 2 - 2 * t * ε₀) := by ring_nf
    _ ≤ Real.exp (Real.log (δ / 2)) := Real.exp_le_exp.mpr hlog
    _ = δ / 2 := Real.exp_log (by positivity)

/-- FV-F (Appendix A Claim 2, post-discovery half): the accumulated post-discovery pruned mass is
`≤ δ/2`, by competitor decay + Kraft alone — no maximal inequality. The per-competitor bound
`wt i ≤ w i · 2^K · exp(−2tε₀)` (decay + normaliser, [Discovery]) is uniform in `t` past
`T_discover`, so summing over the pruned set with Kraft `∑ w ≤ 1` gives `∑ wt ≤ δ/2`. -/
theorem accumulated_pruned_mass_le
    {ι : Type*} (pruned : Finset ι) (w wt : ι → ℝ) (K t ε₀ δ : ℝ)
    (hw0 : ∀ i ∈ pruned, 0 ≤ w i)
    (hkraft : ∑ i ∈ pruned, w i ≤ 1)
    (hδ0 : 0 < δ) (hε₀ : 0 < ε₀)
    (hdecay : ∀ i ∈ pruned, wt i ≤ w i * Real.exp (K * Real.log 2) * Real.exp (-2 * t * ε₀))
    (ht : (K * Real.log 2 + Real.log (2 / δ)) / (2 * ε₀) ≤ t) :
    ∑ i ∈ pruned, wt i ≤ δ / 2 := by
  have hpre : Real.exp (K * Real.log 2) * Real.exp (-2 * t * ε₀) ≤ δ / 2 :=
    prefactor_le K t ε₀ δ hδ0 hε₀ ht
  have hδ2 : 0 ≤ δ / 2 := by positivity
  calc ∑ i ∈ pruned, wt i
      ≤ ∑ i ∈ pruned, w i * (δ / 2) := by
          apply Finset.sum_le_sum
          intro i hi
          calc wt i ≤ w i * Real.exp (K * Real.log 2) * Real.exp (-2 * t * ε₀) := hdecay i hi
            _ = w i * (Real.exp (K * Real.log 2) * Real.exp (-2 * t * ε₀)) := by ring
            _ ≤ w i * (δ / 2) := mul_le_mul_of_nonneg_left hpre (hw0 i hi)
    _ = (∑ i ∈ pruned, w i) * (δ / 2) := by rw [← Finset.sum_mul]
    _ ≤ 1 * (δ / 2) := mul_le_mul_of_nonneg_right hkraft hδ2
    _ = δ / 2 := by ring

end SQPrunedMass
