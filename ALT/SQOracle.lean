/-
Copyright (c) 2026 Mykola Palamarchuk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mykola Palamarchuk
-/
import Mathlib
import ALT.SQObjects
import ALT.SQVersionSpace

-- Formal-check file, not Mathlib-destined: opt out of the house-style header linter.
set_option linter.style.header false
-- `hδ1 : δ ≤ 1` is kept in the signatures for faithfulness to [SQ] §3, though the proof only
-- needs it via the trivial `1 - δ ≤ 0` branch; long doc-comment lines are intentional.
set_option linter.style.longLine false
set_option linter.unusedVariables false

/-!
# The i.i.d.-ensemble SQ oracle: Hoeffding concentration + sample complexity ([SQ] §3)

Provenance: [SQ], §3 "Tool (ii)" (the statistical-query oracle
realised on the i.i.d. ensemble of trajectories) and the `O(1/√n)` query estimate that §4(b) /
Appendix A consume.  This file supplies the *probabilistic core* that `ALT/SQVersionSpace.lean`
(FV-A4) takes as the bare hypothesis `hemp : |emp − predR| ≤ τ`: it DERIVES, by Hoeffding, that the
empirical SQ answer concentrates around the true answer, and threads that through to the
"truth survives pruning" guarantee.

This is the quantitative complement to `ALT/SQVersionSpace.lean`: there the `2τ` geometry is
proved assuming the empirical answer is within `τ` of the truth's mean; here that very assumption is
*discharged* with an explicit sample complexity `n ≥ (2/τ²)·log(2/δ)`.

Status: PROVED as a probability statement over an i.i.d. ensemble.  The single load-bearing import is
Mathlib's Hoeffding inequality for sub-Gaussian MGFs
(`ProbabilityTheory.HasSubgaussianMGF.measure_sum_range_ge_le_of_iIndepFun` together with
`hasSubgaussianMGF_of_mem_Icc`).

## What this DOES establish
* `sq_oracle_concentration` (§3 Tool (ii), Hoeffding): the empirical mean `emp` of `n` i.i.d.
  bounded query-values `Z i` deviates from the true answer `predZ = 𝔼φ` by `≥ τ` with probability
  `≤ 2·exp(−nτ²/2)`.  Two-sided, via the right tail on the centred family and the left tail on its
  negation.
* `sq_oracle_sample_complexity` (the `O(1/√n)` estimate, solved for `n`): once
  `n ≥ (2/τ²)·log(2/δ)`, the empirical answer is within `τ` of the truth with probability `≥ 1−δ`.
* `sq_oracle_truth_survives` (§3 → FV-A4 wiring): chaining the sample complexity through
  `SQVersionSpace.truth_survives_pruning`, with `n ≥ (2/τ²)·log(2/δ)` the truth's predicted
  statistic lies within `2τ` of the empirical answer with probability `≥ 1−δ` — so the SQ-pruning
  rule of `SQVersionSpace.lean` never discards the truth.
* `sq_oracle_uniform_tail`, `empirical_isSQOracle` (FV-E → FV-J glue): the finite-query
  union bound. If each query `φ ∈ Qs` has small tail `μ{τ < |empᵩ − truᵩ|} ≤ δ` (the FV-E
  conclusion shape), then `μ{∃ φ ∈ Qs, τ < |…|} ≤ |Qs|·δ`, and off that event — w.p. `≥ 1 − |Qs|·δ`
  — the empirical answers restricted to `Qs` satisfy FV-J's genuine `SQObjects.IsSQOracle` predicate.
  This is the glue from FV-E's per-query concentration to FV-J's oracle object, at the union-bound
  level.
* `empirical_isSQOracle_of_iid`: the per-query INSTANTIATION — a
  query-indexed i.i.d. family `Zq : Q → ℕ → Ω → ℝ` (each query's values i.i.d. in `[−1,1]` with mean
  `tru φ`, per `sq_oracle_concentration`) DISCHARGES `sq_oracle_uniform_tail`'s `htail` with
  `δ_φ = 2·exp(−nτ²/2)`, giving the end-to-end corollary: `n ≥ (2/τ²)·log(2·|Qs|/δ)` samples per
  query ⇒ the empirical answers fail `SQObjects.IsSQOracle` on `↥Qs` with probability `≤ δ`.

## What this does NOT establish (stays in prose; no overclaiming)
* Not the single-trajectory → i.i.d.-ensemble reduction, ergodicity (E1), or Birkhoff's theorem: the
  ensemble is *modeled* directly as an i.i.d. family `Z : ℕ → Ω → ℝ` of query-values, and the
  per-trajectory query `φ` is taken already composed into `Z i = φ ∘ Xᵢ`.  Independence is the
  hypothesis `hindep`, identical means the hypothesis `hmean`.
* Not the SQ statistical dimension `d_SQ`, the concept class `M`, or the version-space envelope:
  those are the subject of `ALT/SQVersionSpace.lean` (FV-A4) and `ALT/SQObjects.lean` (FV-J).
* Not the negligible-pruned-mass / competitor-decay half of Appendix A's soundness: that is the
  [Discovery] Bayes-mixture argument and stays in prose.

## Hypotheses: paper-stated vs added/strengthened
* Paper-stated / faithful: i.i.d. ensemble (`hindep` + common mean `hmean`); bounded query-values
  (`hbdd`, the `φ : · → [−1,1]` normalisation of the SQ model); the empirical-mean estimator `emp`;
  the `O(1/√n)` rate solved as `n ≥ (2/τ²)·log(2/δ)`.
* Added/strengthened (flagged): the query-values are taken in the *concrete* interval `[−1,1]`
  (giving the sub-Gaussian proxy `1`); independence and the common mean are stated separately
  (`hindep`, `hmean`) rather than as a single `IdentDistrib` family — `hmean` only constrains the
  first moment, which is all Hoeffding needs.
-/

namespace SQOracle

open MeasureTheory ProbabilityTheory

/-- Empirical SQ answer: the mean of the query-values `Z i ω = φ(Xᵢ ω)` over the first `n`
ensemble trajectories. -/
noncomputable def emp {Ω : Type*} (Z : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, Z i ω

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- **One-sided Hoeffding tail** for the SQ oracle: the empirical mean exceeds the true answer
`predZ` by `≥ τ` with probability `≤ exp(−nτ²/2)`.  This is the right tail; the left tail of
`sq_oracle_concentration` is obtained by applying this lemma to the negated ensemble. -/
private theorem tail_le
    (Z : ℕ → Ω → ℝ) (predZ : ℝ) (n : ℕ) (τ : ℝ)
    (hmeas : ∀ i, Measurable (Z i))
    (hbdd : ∀ i, ∀ ω, Z i ω ∈ Set.Icc (-1 : ℝ) 1)
    (hindep : iIndepFun Z μ)
    (hmean : ∀ i, μ[Z i] = predZ)
    (hn : 1 ≤ n) (hτ : 0 ≤ τ) :
    μ.real {ω | τ ≤ emp Z n ω - predZ} ≤ Real.exp (-(n : ℝ) * τ ^ 2 / 2) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hnpos
  have hnτ : (0 : ℝ) ≤ (n : ℝ) * τ := mul_nonneg hnpos.le hτ
  -- The centred family `Z i − predZ` is sub-Gaussian with proxy `1` (Hoeffding's lemma on `[−1,1]`).
  have hsgW : ∀ i, HasSubgaussianMGF (fun ω => Z i ω - predZ) 1 μ := by
    intro i
    have h := hasSubgaussianMGF_of_mem_Icc (μ := μ) (X := Z i)
      (hmeas i).aemeasurable (ae_of_all _ (hbdd i))
    rw [hmean i] at h
    have hc : ((‖(1 : ℝ) - (-1)‖₊ / 2) ^ 2 : NNReal) = 1 := by norm_num
    rwa [hc] at h
  -- and independent, being a measurable post-composition of the independent `Z`.
  have hWindep : iIndepFun (fun i ω => Z i ω - predZ) μ :=
    hindep.comp (fun _ x => x - predZ) (fun _ => by fun_prop)
  -- Hoeffding bound on the sum of the centred family.
  have hb := HasSubgaussianMGF.measure_sum_range_ge_le_of_iIndepFun hWindep
    (c := 1) (n := n) (fun i _ => hsgW i) hnτ
  -- `∑ (Z i ω − predZ) = n·(emp − predZ)`, so the empirical event sits inside the sum event.
  have hTeq : ∀ ω, ∑ i ∈ Finset.range n, (Z i ω - predZ) = (n : ℝ) * (emp Z n ω - predZ) := by
    intro ω
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    simp only [emp]
    rw [mul_sub, ← mul_assoc, mul_inv_cancel₀ hn0, one_mul]
  have hsub : {ω | τ ≤ emp Z n ω - predZ} ⊆
      {ω | (n : ℝ) * τ ≤ ∑ i ∈ Finset.range n, (Z i ω - predZ)} := by
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω ⊢
    rw [hTeq ω]
    exact mul_le_mul_of_nonneg_left hω hnpos.le
  refine le_trans (measureReal_mono hsub (measure_ne_top μ _)) (hb.trans_eq ?_)
  congr 1
  push_cast
  field_simp

/-- **§3 Tool (ii), Hoeffding concentration of the SQ oracle.**  The empirical mean of `n` i.i.d.
bounded query-values is within `τ` of the true answer `predZ = 𝔼φ` except with probability
`≤ 2·exp(−nτ²/2)`. -/
theorem sq_oracle_concentration
    (Z : ℕ → Ω → ℝ) (predZ : ℝ) (n : ℕ) (τ : ℝ)
    (hmeas : ∀ i, Measurable (Z i))
    (hbdd : ∀ i, ∀ ω, Z i ω ∈ Set.Icc (-1 : ℝ) 1)
    (hindep : iIndepFun Z μ)
    (hmean : ∀ i, μ[Z i] = predZ)
    (hn : 1 ≤ n) (hτ : 0 ≤ τ) :
    μ.real {ω | τ ≤ |emp Z n ω - predZ|} ≤ 2 * Real.exp (-(n : ℝ) * τ ^ 2 / 2) := by
  -- Right tail directly from `tail_le`.
  have hR := tail_le Z predZ n τ hmeas hbdd hindep hmean hn hτ
  -- Left tail: apply `tail_le` to the negated ensemble `Y i = -(Z i)`.
  have hmeasY : ∀ i, Measurable (fun ω => -(Z i ω)) := fun i => (hmeas i).neg
  have hbddY : ∀ i, ∀ ω, -(Z i ω) ∈ Set.Icc (-1 : ℝ) 1 := by
    intro i ω
    obtain ⟨h1, h2⟩ := hbdd i ω
    exact ⟨by linarith, by linarith⟩
  have hindepY : iIndepFun (fun i ω => -(Z i ω)) μ :=
    hindep.comp (fun _ x => -x) (fun _ => by fun_prop)
  have hmeanY : ∀ i, μ[fun ω => -(Z i ω)] = -predZ := by
    intro i
    rw [integral_neg, hmean i]
  have hL0 := tail_le (fun i ω => -(Z i ω)) (-predZ) n τ hmeasY hbddY hindepY hmeanY hn hτ
  -- `emp` of the negated ensemble is `-emp`, so the left tail set is `{τ ≤ predZ − emp}`.
  have hempneg : ∀ ω, emp (fun i ω => -(Z i ω)) n ω = - emp Z n ω := by
    intro ω
    simp only [emp, Finset.sum_neg_distrib, mul_neg]
  have hLset : {ω | τ ≤ emp (fun i ω => -(Z i ω)) n ω - -predZ}
      = {ω | τ ≤ predZ - emp Z n ω} := by
    ext ω
    simp only [Set.mem_setOf_eq, hempneg ω]
    constructor <;> intro h <;> linarith
  rw [hLset] at hL0
  -- Union bound: `{τ ≤ |emp − predZ|} ⊆ {τ ≤ emp − predZ} ∪ {τ ≤ predZ − emp}`.
  have hsubU : {ω | τ ≤ |emp Z n ω - predZ|} ⊆
      {ω | τ ≤ emp Z n ω - predZ} ∪ {ω | τ ≤ predZ - emp Z n ω} := by
    intro ω hω
    simp only [Set.mem_setOf_eq, Set.mem_union] at hω ⊢
    rcases abs_choice (emp Z n ω - predZ) with h | h
    · left; rwa [h] at hω
    · right; rw [h] at hω; linarith
  calc μ.real {ω | τ ≤ |emp Z n ω - predZ|}
      ≤ μ.real ({ω | τ ≤ emp Z n ω - predZ} ∪ {ω | τ ≤ predZ - emp Z n ω}) :=
        measureReal_mono hsubU (measure_ne_top μ _)
    _ ≤ μ.real {ω | τ ≤ emp Z n ω - predZ} + μ.real {ω | τ ≤ predZ - emp Z n ω} :=
        measureReal_union_le _ _
    _ ≤ Real.exp (-(n : ℝ) * τ ^ 2 / 2) + Real.exp (-(n : ℝ) * τ ^ 2 / 2) := add_le_add hR hL0
    _ = 2 * Real.exp (-(n : ℝ) * τ ^ 2 / 2) := by ring

/-- **Sample complexity of the SQ oracle.**  `n ≥ (2/τ²)·log(2/δ)` i.i.d. ensemble trajectories
answer the SQ query to tolerance `τ` with probability `≥ 1−δ`. -/
theorem sq_oracle_sample_complexity
    (Z : ℕ → Ω → ℝ) (predZ : ℝ) (n : ℕ) (τ δ : ℝ)
    (hmeas : ∀ i, Measurable (Z i)) (hbdd : ∀ i, ∀ ω, Z i ω ∈ Set.Icc (-1 : ℝ) 1)
    (hindep : iIndepFun Z μ) (hmean : ∀ i, μ[Z i] = predZ)
    (hn1 : 1 ≤ n) (hτ : 0 < τ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hn : (2 / τ ^ 2) * Real.log (2 / δ) ≤ (n : ℝ)) :
    1 - δ ≤ μ.real {ω | |emp Z n ω - predZ| < τ} := by
  have hconc := sq_oracle_concentration Z predZ n τ hmeas hbdd hindep hmean hn1 hτ.le
  have hτ0 : τ ≠ 0 := ne_of_gt hτ
  -- `n ≥ (2/τ²)·log(2/δ)` ⟹ `log(2/δ) ≤ nτ²/2`.
  have hlogle : Real.log (2 / δ) ≤ (n : ℝ) * τ ^ 2 / 2 := by
    have hpos : (0 : ℝ) < τ ^ 2 / 2 := by positivity
    have h := mul_le_mul_of_nonneg_left hn hpos.le
    have e1 : (τ ^ 2 / 2) * ((2 / τ ^ 2) * Real.log (2 / δ)) = Real.log (2 / δ) := by
      field_simp
    have e2 : (τ ^ 2 / 2) * (n : ℝ) = (n : ℝ) * τ ^ 2 / 2 := by ring
    rw [e1, e2] at h
    exact h
  -- hence `2·exp(−nτ²/2) ≤ δ`.
  have hδ2 : (0 : ℝ) < δ / 2 := by linarith
  have hexple : 2 * Real.exp (-(n : ℝ) * τ ^ 2 / 2) ≤ δ := by
    have hlog2 : Real.log (δ / 2) = - Real.log (2 / δ) := by
      rw [← Real.log_inv]
      congr 1
      rw [inv_div]
    have h1 : Real.exp (-(n : ℝ) * τ ^ 2 / 2) ≤ δ / 2 := by
      rw [show -(n : ℝ) * τ ^ 2 / 2 = -((n : ℝ) * τ ^ 2 / 2) by ring, ← Real.exp_log hδ2]
      apply Real.exp_le_exp.mpr
      rw [hlog2]
      linarith
    linarith
  -- complement of the tail event.
  have hempmeas : Measurable (emp Z n) := by
    unfold emp
    exact (Finset.measurable_fun_sum (Finset.range n) (fun i _ => hmeas i)).const_mul _
  have hsetmeas : MeasurableSet {ω | τ ≤ |emp Z n ω - predZ|} :=
    measurableSet_le measurable_const ((hempmeas.sub_const predZ).abs)
  have hcompl : μ.real {ω | |emp Z n ω - predZ| < τ}
      = 1 - μ.real {ω | τ ≤ |emp Z n ω - predZ|} := by
    have hset : {ω | |emp Z n ω - predZ| < τ} = {ω | τ ≤ |emp Z n ω - predZ|}ᶜ := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_compl_iff, not_le]
    rw [hset, measureReal_compl hsetmeas, probReal_univ]
  rw [hcompl]
  linarith [hconc, hexple]

/-- **§3 → FV-A4 wiring: the SQ oracle discharges `SQVersionSpace.truth_survives_pruning`'s
hypothesis.**  With `n ≥ (2/τ²)·log(2/δ)` ensemble trajectories, with probability `≥ 1−δ` the
truth's predicted statistic `predZ` is within `2τ` of the empirical answer — i.e. it is never pruned
by the `2τ`-rule of `ALT/SQVersionSpace.lean`. -/
theorem sq_oracle_truth_survives
    (Z : ℕ → Ω → ℝ) (predZ : ℝ) (n : ℕ) (τ δ : ℝ)
    (hmeas : ∀ i, Measurable (Z i)) (hbdd : ∀ i, ∀ ω, Z i ω ∈ Set.Icc (-1 : ℝ) 1)
    (hindep : iIndepFun Z μ) (hmean : ∀ i, μ[Z i] = predZ)
    (hn1 : 1 ≤ n) (hτ : 0 < τ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hn : (2 / τ ^ 2) * Real.log (2 / δ) ≤ (n : ℝ)) :
    1 - δ ≤ μ.real {ω | |predZ - emp Z n ω| ≤ 2 * τ} := by
  have hsc := sq_oracle_sample_complexity Z predZ n τ δ hmeas hbdd hindep hmean hn1 hτ hδ0 hδ1 hn
  refine hsc.trans (measureReal_mono ?_ (measure_ne_top μ _))
  intro ω hω
  simp only [Set.mem_setOf_eq] at hω ⊢
  exact SQVersionSpace.truth_survives_pruning predZ (emp Z n ω) τ hτ.le hω.le

/-! ### The W-attack: window-noise budget `2η ≤ τ` ([SQ] §3.1)

The window-sufficiency assumption (W) of [SQ] §3.1 — "the window determines the next observation
under R" — is the *determinism* of the one-step predictor `f_R`; it weakens gracefully to the
window-noise rate `η := μ(o_{t+1} ≠ f_R(w_t))` (the Bayes error of the window predictor under the
invariant measure; W is `η = 0`).  `noise_gap_integral` is the genuine content — a `[−1,1]`-valued
query answer is distorted by at most `2η` — and `sq_oracle_truth_survives_noisy` threads it, with the
arithmetic siblings in `SQVersionSpace`, into the FV-A4 guarantee: the deterministic truth survives
the *unchanged* `2τ`-pruning rule with probability `≥ 1−δ` exactly when the window-noise budget
`2η ≤ τ` holds. -/

/-- **A1 — the window-noise integral gap** ([SQ] §3.1).  Two `[−1,1]`-valued measurable observables
`f`, `g` that agree off a measurable event `E` have integrals differing by at most `2·μ(E)`.  Applied
to a `[−1,1]`-valued SQ query answer, the realized-next-observation value `φ(w, o_next)` and the
deterministic-prediction value `φ(w, f_R(w))` agree off the window-noise event `E = {o_next ≠ f_R(w)}`
of mass `η := μ(E)`, so the query answer is distorted by at most `2η`.  Boundedness on the
probability measure discharges integrability; the majorant is the indicator `2·𝟙_E`. -/
theorem noise_gap_integral
    (f g : Ω → ℝ) (E : Set Ω)
    (hf : ∀ ω, f ω ∈ Set.Icc (-1 : ℝ) 1) (hg : ∀ ω, g ω ∈ Set.Icc (-1 : ℝ) 1)
    (hfm : Measurable f) (hgm : Measurable g) (hE : MeasurableSet E)
    (hagree : ∀ ω, ω ∉ E → f ω = g ω) :
    |∫ ω, f ω ∂μ - ∫ ω, g ω ∂μ| ≤ 2 * μ.real E := by
  have hfi : Integrable f μ :=
    Integrable.of_bound hfm.aestronglyMeasurable 1
      (ae_of_all _ fun ω => by rw [Real.norm_eq_abs, abs_le]; exact Set.mem_Icc.mp (hf ω))
  have hgi : Integrable g μ :=
    Integrable.of_bound hgm.aestronglyMeasurable 1
      (ae_of_all _ fun ω => by rw [Real.norm_eq_abs, abs_le]; exact Set.mem_Icc.mp (hg ω))
  -- Off `E` the difference vanishes; on `E` it is at most `2`, so `2·𝟙_E` dominates `|f − g|`.
  have hbound : ∀ ω, |f ω - g ω| ≤ E.indicator (fun _ => (2 : ℝ)) ω := by
    intro ω
    by_cases hω : ω ∈ E
    · have hval : E.indicator (fun _ => (2 : ℝ)) ω = 2 := Set.indicator_of_mem hω _
      rw [hval, abs_le]
      obtain ⟨hf1, hf2⟩ := Set.mem_Icc.mp (hf ω)
      obtain ⟨hg1, hg2⟩ := Set.mem_Icc.mp (hg ω)
      exact ⟨by linarith, by linarith⟩
    · simp [Set.indicator_of_notMem hω, hagree ω hω]
  calc |∫ ω, f ω ∂μ - ∫ ω, g ω ∂μ|
      = |∫ ω, (f ω - g ω) ∂μ| := by rw [integral_sub hfi hgi]
    _ ≤ ∫ ω, |f ω - g ω| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ ω, E.indicator (fun _ => (2 : ℝ)) ω ∂μ :=
        integral_mono (hfi.sub hgi).abs ((integrable_const (2 : ℝ)).indicator hE) hbound
    _ = μ.real E • (2 : ℝ) := integral_indicator_const (2 : ℝ) hE
    _ = 2 * μ.real E := by rw [smul_eq_mul]; ring

/-- **A3 — §3 → FV-A4 wiring under window noise: the SQ oracle survives a `2η ≤ τ` budget.**
Mirror of `sq_oracle_truth_survives` that keeps the empirical mean's target `a = 𝔼φ` (the joint
window/next-observation answer, on which the time-average concentrates) distinct from the
deterministic-prediction truth `predR`: the two differ by the window-noise gap `|a − predR| ≤ 2η`
(bounded by `noise_gap_integral` at the call site).  With `n ≥ (2/τ²)·log(2/δ)` ensemble trajectories
and window-noise budget `2η ≤ τ`, the truth's predicted statistic `predR` lies within `2τ` of the
empirical answer with probability `≥ 1−δ` — so the `2τ`-pruning rule never discards it.  At `η = 0`
(so `a = predR`) this is exactly `sq_oracle_truth_survives`. -/
theorem sq_oracle_truth_survives_noisy
    (Z : ℕ → Ω → ℝ) (predR a : ℝ) (n : ℕ) (τ δ η : ℝ)
    (hmeas : ∀ i, Measurable (Z i)) (hbdd : ∀ i, ∀ ω, Z i ω ∈ Set.Icc (-1 : ℝ) 1)
    (hindep : iIndepFun Z μ) (hmean : ∀ i, μ[Z i] = a)
    (hn1 : 1 ≤ n) (hτ : 0 < τ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hn : (2 / τ ^ 2) * Real.log (2 / δ) ≤ (n : ℝ))
    (hη : 0 ≤ η) (hbudget : 2 * η ≤ τ) (hnoise : |a - predR| ≤ 2 * η) :
    1 - δ ≤ μ.real {ω | |predR - emp Z n ω| ≤ 2 * τ} := by
  have hsc := sq_oracle_sample_complexity Z a n τ δ hmeas hbdd hindep hmean hn1 hτ hδ0 hδ1 hn
  refine hsc.trans (measureReal_mono ?_ (measure_ne_top μ _))
  intro ω hω
  simp only [Set.mem_setOf_eq] at hω ⊢
  exact SQVersionSpace.truth_survives_pruning_noisy predR a (emp Z n ω) τ η hτ.le hη hbudget hω.le
    hnoise

/-! ### FV-E → FV-J union-bound glue

The finite-query union bound that carries the per-query concentration of `sq_oracle_concentration`
to FV-J's genuine oracle object `SQObjects.IsSQOracle`: given a `Finset` of queries `Qs`, empirical
answers `emp : Q → Ω → ℝ`, truth `tru : Q → ℝ`, and a per-query tail bound (the FV-E conclusion
shape), the empirical answers restricted to `Qs` satisfy the oracle predicate off an event of measure
`≤ |Qs|·δ`. -/

variable {Q : Type*}

omit [IsProbabilityMeasure μ] in
/-- **Finite-query union bound.**  If each query `φ ∈ Qs` fails the tolerance `τ` with probability
`≤ δ`, then SOME query in `Qs` fails with probability `≤ |Qs|·δ` — the union bound over the finite
query set (`measure_biUnion_finset_le`). -/
theorem sq_oracle_uniform_tail (Qs : Finset Q) (emp : Q → Ω → ℝ) (tru : Q → ℝ) (τ δ : ℝ)
    (htail : ∀ φ ∈ Qs, μ {ω | τ < |emp φ ω - tru φ|} ≤ ENNReal.ofReal δ) :
    μ {ω | ∃ φ ∈ Qs, τ < |emp φ ω - tru φ|} ≤ Qs.card * ENNReal.ofReal δ := by
  have hset : {ω | ∃ φ ∈ Qs, τ < |emp φ ω - tru φ|}
      = ⋃ φ ∈ Qs, {ω | τ < |emp φ ω - tru φ|} := by
    ext ω; simp only [Set.mem_setOf_eq, Set.mem_iUnion, exists_prop]
  rw [hset]
  calc μ (⋃ φ ∈ Qs, {ω | τ < |emp φ ω - tru φ|})
      ≤ ∑ φ ∈ Qs, μ {ω | τ < |emp φ ω - tru φ|} := measure_biUnion_finset_le Qs _
    _ ≤ ∑ _φ ∈ Qs, ENNReal.ofReal δ := Finset.sum_le_sum htail
    _ = Qs.card * ENNReal.ofReal δ := by rw [Finset.sum_const, nsmul_eq_mul]

omit [IsProbabilityMeasure μ] in
/-- **FV-E → FV-J oracle-object glue.**  Off an event of measure `≤ |Qs|·δ` — i.e. with probability
`≥ 1 − |Qs|·δ` — the empirical answers restricted to `Qs` satisfy FV-J's genuine oracle predicate
`SQObjects.IsSQOracle` (over the subtype `↥Qs`).  The complement of the good event is exactly the
"some query fails" event of `sq_oracle_uniform_tail`. -/
theorem empirical_isSQOracle (Qs : Finset Q) (emp : Q → Ω → ℝ) (tru : Q → ℝ) (τ δ : ℝ)
    (htail : ∀ φ ∈ Qs, μ {ω | τ < |emp φ ω - tru φ|} ≤ ENNReal.ofReal δ) :
    μ ({ω | SQObjects.IsSQOracle (fun φ : ↥Qs => emp (↑φ) ω) (fun φ : ↥Qs => tru (↑φ)) τ}ᶜ)
      ≤ Qs.card * ENNReal.ofReal δ := by
  have hcompl :
      ({ω | SQObjects.IsSQOracle (fun φ : ↥Qs => emp (↑φ) ω) (fun φ : ↥Qs => tru (↑φ)) τ}ᶜ)
        = {ω | ∃ φ ∈ Qs, τ < |emp φ ω - tru φ|} := by
    ext ω
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq, SQObjects.IsSQOracle, not_forall, not_le,
      Subtype.exists, exists_prop]
  rw [hcompl]
  exact sq_oracle_uniform_tail Qs emp tru τ δ htail

/-- **Per-query i.i.d. instantiation.**  A query-indexed i.i.d. family
`Zq : Q → ℕ → Ω → ℝ` — each query's values i.i.d. in `[−1,1]` with mean `tru φ`, per
`sq_oracle_concentration`'s hypotheses — DISCHARGES `sq_oracle_uniform_tail`'s per-query tail with
`δ_φ = 2·exp(−nτ²/2)`, giving the end-to-end bound: with `n ≥ (2/τ²)·log(2·|Qs|/δ)` samples per
query, the empirical answers fail FV-J's `SQObjects.IsSQOracle` on `↥Qs` with probability `≤ δ`. -/
theorem empirical_isSQOracle_of_iid (Qs : Finset Q) (hQs : Qs.Nonempty)
    (Zq : Q → ℕ → Ω → ℝ) (tru : Q → ℝ) (τ δ : ℝ) (n : ℕ)
    (hmeas : ∀ φ ∈ Qs, ∀ i, Measurable (Zq φ i))
    (hbdd : ∀ φ ∈ Qs, ∀ i, ∀ ω, Zq φ i ω ∈ Set.Icc (-1 : ℝ) 1)
    (hindep : ∀ φ ∈ Qs, iIndepFun (Zq φ) μ)
    (hmean : ∀ φ ∈ Qs, ∀ i, μ[Zq φ i] = tru φ)
    (hn1 : 1 ≤ n) (hτ : 0 < τ) (hδ0 : 0 < δ)
    (hn : (2 / τ ^ 2) * Real.log (2 * (Qs.card : ℝ) / δ) ≤ (n : ℝ)) :
    μ ({ω | SQObjects.IsSQOracle (fun φ : ↥Qs => emp (Zq ↑φ) n ω) (fun φ : ↥Qs => tru ↑φ) τ}ᶜ)
      ≤ ENNReal.ofReal δ := by
  have hMpos : (0 : ℝ) < (Qs.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hQs
  -- Each query's tail is small (concentration ⇒ the `<`/`ENNReal.ofReal` shape `htail` needs).
  have htail : ∀ φ ∈ Qs, μ {ω | τ < |emp (Zq φ) n ω - tru φ|}
      ≤ ENNReal.ofReal (2 * Real.exp (-(n : ℝ) * τ ^ 2 / 2)) := by
    intro φ hφ
    have hconc := sq_oracle_concentration (Zq φ) (tru φ) n τ (hmeas φ hφ) (hbdd φ hφ)
      (hindep φ hφ) (hmean φ hφ) hn1 hτ.le
    calc μ {ω | τ < |emp (Zq φ) n ω - tru φ|}
        ≤ μ {ω | τ ≤ |emp (Zq φ) n ω - tru φ|} :=
          measure_mono (Set.setOf_subset_setOf.mpr fun ω h => le_of_lt h)
      _ = ENNReal.ofReal (μ.real {ω | τ ≤ |emp (Zq φ) n ω - tru φ|}) :=
          (ENNReal.ofReal_toReal (measure_ne_top μ _)).symm
      _ ≤ ENNReal.ofReal (2 * Real.exp (-(n : ℝ) * τ ^ 2 / 2)) := ENNReal.ofReal_le_ofReal hconc
  -- `n ≥ (2/τ²)·log(2|Qs|/δ)` ⟹ `|Qs|·2·exp(−nτ²/2) ≤ δ`.
  have hlogle : Real.log (2 * (Qs.card : ℝ) / δ) ≤ (n : ℝ) * τ ^ 2 / 2 := by
    have hpos : (0 : ℝ) < τ ^ 2 / 2 := by positivity
    have h := mul_le_mul_of_nonneg_left hn hpos.le
    have e1 : (τ ^ 2 / 2) * ((2 / τ ^ 2) * Real.log (2 * (Qs.card : ℝ) / δ))
        = Real.log (2 * (Qs.card : ℝ) / δ) := by field_simp
    have e2 : (τ ^ 2 / 2) * (n : ℝ) = (n : ℝ) * τ ^ 2 / 2 := by ring
    rw [e1, e2] at h; exact h
  have hexple : (Qs.card : ℝ) * (2 * Real.exp (-(n : ℝ) * τ ^ 2 / 2)) ≤ δ := by
    have hstep : Real.exp (-(n : ℝ) * τ ^ 2 / 2) ≤ δ / (2 * (Qs.card : ℝ)) := by
      rw [show -(n : ℝ) * τ ^ 2 / 2 = -((n : ℝ) * τ ^ 2 / 2) by ring,
          show δ / (2 * (Qs.card : ℝ)) = Real.exp (Real.log (δ / (2 * (Qs.card : ℝ))))
            from (Real.exp_log (by positivity)).symm]
      apply Real.exp_le_exp.mpr
      have hlog : Real.log (δ / (2 * (Qs.card : ℝ))) = - Real.log (2 * (Qs.card : ℝ) / δ) := by
        rw [← Real.log_inv]; congr 1; rw [inv_div]
      rw [hlog]; linarith
    calc (Qs.card : ℝ) * (2 * Real.exp (-(n : ℝ) * τ ^ 2 / 2))
        = (2 * (Qs.card : ℝ)) * Real.exp (-(n : ℝ) * τ ^ 2 / 2) := by ring
      _ ≤ (2 * (Qs.card : ℝ)) * (δ / (2 * (Qs.card : ℝ))) :=
          mul_le_mul_of_nonneg_left hstep (by positivity)
      _ = δ := by field_simp
  -- assemble: union bound to FV-J's oracle object, then the `|Qs|·δ_φ ≤ δ` collapse.
  calc μ ({ω | SQObjects.IsSQOracle (fun φ : ↥Qs => emp (Zq ↑φ) n ω) (fun φ : ↥Qs => tru ↑φ) τ}ᶜ)
      ≤ (Qs.card : ENNReal) * ENNReal.ofReal (2 * Real.exp (-(n : ℝ) * τ ^ 2 / 2)) :=
        empirical_isSQOracle Qs (fun φ => emp (Zq φ) n) tru τ
          (2 * Real.exp (-(n : ℝ) * τ ^ 2 / 2)) htail
    _ = ENNReal.ofReal ((Qs.card : ℝ) * (2 * Real.exp (-(n : ℝ) * τ ^ 2 / 2))) := by
        rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
    _ ≤ ENNReal.ofReal δ := ENNReal.ofReal_le_ofReal hexple

end SQOracle
