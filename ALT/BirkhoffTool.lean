/-
Copyright (c) 2026 Mykola Palamarchuk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mykola Palamarchuk
-/
/-
# Birkhoff Tool: single-orbit SQ oracle from the pointwise ergodic theorem

This module restates the vendored pointwise Birkhoff ergodic theorem
(`ALT/Birkhoff/PointwiseBirkhoff.lean`) in the trajectory-space vocabulary of the
statistical-query (SQ) development (`ALT/SQOracle.lean`, `ALT/SQMixtureSupermartingale.lean`)
and connects it to the FV-E oracle interface.

## What is proved here (all machine-checked, axioms = the standard triple)

* `BirkhoffTool.shift` — the left shift on the trajectory space `ℕ → X`; a shift-invariant
  probability measure is a *stationary trajectory law*, and `Ergodic shift μ` an *ergodic* one.
* `birkhoffAverage_eq_emp` — the Birkhoff time-average along one orbit *is* the single-orbit
  empirical mean `SQOracle.emp`, definitionally.  This is the bridge between the two developments.
* `timeAverage_tendsto_expectation` — **Tool (i), qualitative.**  For an ergodic stationary
  trajectory law and an integrable observable, the single-orbit time-average converges `μ`-a.e.
  to the mean `∫ φ ∂μ`.  (Pointwise Birkhoff, then ergodicity collapses the invariant conditional
  expectation to the constant mean.)

## What is imported as a named hypothesis (NOT proved here)

* `MixingHoeffding` — the FJS-shaped (Fan–Jiang–Sun, JMLR 22(139), 2021, Thm 1) *quantitative*
  single-orbit Hoeffding tail with the variance proxy inflated by a spectral-gap constant `c ≥ 1`.
  Proving `MixingHoeffding` from a spectral gap (i.e. proving FJS) is registered as its own future
  target; here it is a named premise, exactly as the qualitative Tool (i) does not by itself give a
  rate.  At `c = 1` (`λ = 0`, i.i.d.) it is exactly `SQOracle.sq_oracle_concentration`.
* `mixing_oracle_sample_complexity`, `mixing_oracle_tail` — the oracle-error corollaries derived
  *from* `MixingHoeffding`: `n ≥ (2c/τ²)·log(2/δ)` single-orbit steps answer an SQ query to
  tolerance `τ` with confidence `≥ 1 − δ`, in the exact shapes the FV-E interface
  (`SQOracle.sq_oracle_sample_complexity` / `SQOracle.empirical_isSQOracle`) consumes.
-/
import Mathlib.Dynamics.BirkhoffSum.Average
import Mathlib.Dynamics.Ergodic.Ergodic
import ALT.Birkhoff.PointwiseBirkhoff
import ALT.SQOracle

set_option linter.style.header false
set_option linter.style.longLine false

open MeasureTheory Filter Topology MeasurableSpace SQOracle

namespace BirkhoffTool

variable {X : Type*} [MeasurableSpace X]

/-! ## Trajectory space and the shift -/

/-- The left shift on the trajectory space `ℕ → X`: `(shift ω) i = ω (i + 1)`.
A probability measure with `MeasurePreserving shift μ μ` is a *stationary* trajectory law;
`Ergodic shift μ` is an *ergodic* stationary trajectory law. -/
def shift : (ℕ → X) → (ℕ → X) := fun ω i => ω (i + 1)

omit [MeasurableSpace X] in
/-- **The bridge.**  The Birkhoff time-average of `φ` along the shift orbit through `ω` is exactly
the single-orbit empirical mean `SQOracle.emp` of the query-ensemble `i ↦ φ ∘ shift^[i]`.
Definitional up to `smul = mul` on `ℝ`. -/
lemma birkhoffAverage_eq_emp (φ : (ℕ → X) → ℝ) (n : ℕ) (ω : ℕ → X) :
    birkhoffAverage ℝ shift φ n ω = emp (fun i => φ ∘ shift^[i]) n ω := by
  simp only [birkhoffAverage, birkhoffSum, emp, smul_eq_mul, Function.comp_apply]

/-! ## Tool (i): the single-orbit law of large numbers (qualitative) -/

/-- **Tool (i), qualitative — single-orbit LLN from the pointwise ergodic theorem.**
For an ergodic, measure-preserving (stationary) trajectory law `μ` on `ℕ → X` and an integrable
observable `φ`, the single-orbit time-average of `φ` converges `μ`-a.e. to the mean `∫ φ ∂μ`.

Proof: the vendored pointwise Birkhoff theorem gives a.e. convergence to the invariant conditional
expectation `μ[φ | invariants shift]`; ergodicity (`Ergodic.ae_eq_const_of_ae_eq_comp₀`) collapses
that invariant function to a constant, which `integral_condExp` identifies as the mean `∫ φ ∂μ`. -/
theorem timeAverage_tendsto_expectation
    (μ : Measure (ℕ → X)) [IsProbabilityMeasure μ]
    (herg : Ergodic (shift : (ℕ → X) → ℕ → X) μ) (φ : (ℕ → X) → ℝ) (hφ : Integrable φ μ) :
    ∀ᵐ ω ∂μ, Tendsto (fun n => emp (fun i => φ ∘ shift^[i]) n ω) atTop (𝓝 (∫ x, φ x ∂μ)) := by
  have hmp : MeasurePreserving shift μ μ := herg.toMeasurePreserving
  -- Pointwise Birkhoff: time-average → the invariant conditional expectation, a.e.
  have hbirk := birkhoffErgodicTheorem' μ hmp hφ
  -- The invariant conditional expectation is genuinely shift-invariant.
  have hmeasInv : Measurable[invariants shift] (invCondexp μ shift φ) := by
    unfold invCondexp
    exact MeasureTheory.stronglyMeasurable_condExp.measurable
  have hinv : invCondexp μ shift φ ∘ shift = invCondexp μ shift φ :=
    MeasurableSpace.invariant_of_measurable_invariants hmeasInv
  -- Ergodicity ⇒ it is a.e. equal to some constant `c`.
  obtain ⟨c, hc⟩ := herg.ae_eq_const_of_ae_eq_comp₀
    (hmeasInv.le (invariants_le shift)).nullMeasurable
    (Filter.Eventually.of_forall fun x => congrFun hinv x)
  -- `c` is the mean, since the conditional expectation preserves the integral.
  have hcval : c = ∫ x, φ x ∂μ := by
    have h1 : ∫ x, invCondexp μ shift φ x ∂μ = ∫ x, φ x ∂μ := by
      unfold invCondexp; exact integral_condExp (invariants_le shift)
    have h2 : ∫ x, invCondexp μ shift φ x ∂μ = c := by
      rw [integral_congr_ae hc]; simp
    rw [← h1, h2]
  -- Assemble: rewrite the limit through the bridge and the constant.
  filter_upwards [hbirk, hc] with ω hω hcω
  have hfun : (fun n => emp (fun i => φ ∘ shift^[i]) n ω) = (birkhoffAverage ℝ shift φ · ω) := by
    funext n; exact (birkhoffAverage_eq_emp φ n ω).symm
  have hval : invCondexp μ shift φ ω = ∫ x, φ x ∂μ := by
    rw [hcω]; simpa using hcval
  rw [hfun, ← hval]
  exact hω

/-! ## Tool (i), quantitative: the FJS-shaped mixing Hoeffding hypothesis and its oracle corollaries

The qualitative Tool (i) above gives no *rate*.  The single-orbit rate is supplied by one named
hypothesis in the citable spectral-gap Hoeffding shape, from which the FV-E oracle-error interface
is reached by the same real-analysis as `SQOracle.sq_oracle_sample_complexity`. -/

/-- **FJS-shaped mixing Hoeffding hypothesis** (Fan–Jiang–Sun, JMLR 22(139), 2021, Thm 1).
For a stationary Markov trajectory law with absolute spectral gap `1 − λ ∈ (0, 1]` — where
`λ = ‖P − Π‖` is the operator norm of the transition operator on the mean-zero subspace of `L²(π)`,
so that reversibility is NOT required — the single-orbit empirical mean of a bounded query-ensemble
`Z` concentrates around its stationary mean `predZ` with the Hoeffding variance proxy inflated by
the mixing constant `c = (1 + λ)/(1 − λ) ≥ 1`.  (For a query bounded in `[a, b]` the constant is
`((b − a)²/4)·(1 + λ)/(1 − λ)`; the `[−1, 1]` normalization used throughout here makes the leading
factor `1`.)

This is the single-orbit analogue of `SQOracle.sq_oracle_concentration`; at `c = 1` (`λ = 0`,
the i.i.d. case) the two coincide.  It is stated as a *hypothesis*: deriving it from a spectral gap
(i.e. proving FJS) is a separate future target, not attempted here. -/
def MixingHoeffding (μ : Measure (ℕ → X)) (Z : ℕ → (ℕ → X) → ℝ) (predZ c : ℝ) : Prop :=
  ∀ (n : ℕ) (τ : ℝ), 1 ≤ n → 0 ≤ τ →
    μ.real {ω | τ ≤ |emp Z n ω - predZ|} ≤ 2 * Real.exp (-(n : ℝ) * τ ^ 2 / (2 * c))

/-- The FJS tail estimate meets the `δ`-budget once `n ≥ (2c/τ²)·log(2/δ)`. -/
private lemma mixing_exp_le_delta {c : ℝ} (hc : 0 < c) {n : ℕ} {τ δ : ℝ} (hτ : 0 < τ) (hδ0 : 0 < δ)
    (hn : (2 * c / τ ^ 2) * Real.log (2 / δ) ≤ (n : ℝ)) :
    2 * Real.exp (-(n : ℝ) * τ ^ 2 / (2 * c)) ≤ δ := by
  have hδ2 : (0 : ℝ) < δ / 2 := by linarith
  -- `n ≥ (2c/τ²)·log(2/δ)` ⟹ `log(2/δ) ≤ nτ²/(2c)`.
  have hlogle : Real.log (2 / δ) ≤ (n : ℝ) * τ ^ 2 / (2 * c) := by
    have hpos : (0 : ℝ) < τ ^ 2 / (2 * c) := by positivity
    have h := mul_le_mul_of_nonneg_left hn hpos.le
    have e1 : (τ ^ 2 / (2 * c)) * ((2 * c / τ ^ 2) * Real.log (2 / δ)) = Real.log (2 / δ) := by
      field_simp
    have e2 : (τ ^ 2 / (2 * c)) * (n : ℝ) = (n : ℝ) * τ ^ 2 / (2 * c) := by ring
    rw [e1, e2] at h
    exact h
  have hlog2 : Real.log (δ / 2) = - Real.log (2 / δ) := by
    rw [← Real.log_inv]; congr 1; rw [inv_div]
  have h1 : Real.exp (-(n : ℝ) * τ ^ 2 / (2 * c)) ≤ δ / 2 := by
    rw [show -(n : ℝ) * τ ^ 2 / (2 * c) = -((n : ℝ) * τ ^ 2 / (2 * c)) by ring, ← Real.exp_log hδ2]
    apply Real.exp_le_exp.mpr
    rw [hlog2]; linarith
  linarith

/-- **Single-orbit oracle sample complexity** (from `MixingHoeffding`).
`n ≥ (2c/τ²)·log(2/δ)` single-orbit steps answer the SQ query to tolerance `τ` with confidence
`≥ 1 − δ` — the same conclusion shape as the i.i.d. `SQOracle.sq_oracle_sample_complexity`, with
the mixing constant `c` inflating the sample size by exactly the factor `c`. -/
theorem mixing_oracle_sample_complexity
    (μ : Measure (ℕ → X)) [IsProbabilityMeasure μ]
    (Z : ℕ → (ℕ → X) → ℝ) (predZ c : ℝ) (n : ℕ) (τ δ : ℝ)
    (hmix : MixingHoeffding μ Z predZ c) (hc : 0 < c) (hmeas : ∀ i, Measurable (Z i))
    (hn1 : 1 ≤ n) (hτ : 0 < τ) (hδ0 : 0 < δ)
    (hn : (2 * c / τ ^ 2) * Real.log (2 / δ) ≤ (n : ℝ)) :
    1 - δ ≤ μ.real {ω | |emp Z n ω - predZ| < τ} := by
  have hconc := hmix n τ hn1 hτ.le
  have hexple := mixing_exp_le_delta hc hτ hδ0 hn
  have hempmeas : Measurable (emp Z n) := by
    unfold emp
    exact (Finset.measurable_fun_sum (Finset.range n) (fun i _ => hmeas i)).const_mul _
  have hsetmeas : MeasurableSet {ω | τ ≤ |emp Z n ω - predZ|} :=
    measurableSet_le measurable_const ((hempmeas.sub_const predZ).abs)
  have hcompl : μ.real {ω | |emp Z n ω - predZ| < τ}
      = 1 - μ.real {ω | τ ≤ |emp Z n ω - predZ|} := by
    have hset : {ω | |emp Z n ω - predZ| < τ} = {ω | τ ≤ |emp Z n ω - predZ|}ᶜ := by
      ext ω; simp only [Set.mem_setOf_eq, Set.mem_compl_iff, not_le]
    rw [hset, measureReal_compl hsetmeas, probReal_univ]
  rw [hcompl]; linarith

/-- **Single-orbit oracle tail bound** (from `MixingHoeffding`), in the exact shape the FV-E oracle
object `SQOracle.empirical_isSQOracle` consumes: with `n ≥ (2c/τ²)·log(2/δ)`, the single-orbit
empirical answer fails tolerance `τ` with probability `≤ δ`. -/
theorem mixing_oracle_tail
    (μ : Measure (ℕ → X)) [IsProbabilityMeasure μ]
    (Z : ℕ → (ℕ → X) → ℝ) (predZ c : ℝ) (n : ℕ) (τ δ : ℝ)
    (hmix : MixingHoeffding μ Z predZ c) (hc : 0 < c)
    (hn1 : 1 ≤ n) (hτ : 0 < τ) (hδ0 : 0 < δ)
    (hn : (2 * c / τ ^ 2) * Real.log (2 / δ) ≤ (n : ℝ)) :
    μ {ω | τ < |emp Z n ω - predZ|} ≤ ENNReal.ofReal δ := by
  have hconc := hmix n τ hn1 hτ.le
  have hexple := mixing_exp_le_delta hc hτ hδ0 hn
  -- The strict-tail event sits inside the closed-tail event of `MixingHoeffding`.
  have hsub : {ω | τ < |emp Z n ω - predZ|} ⊆ {ω | τ ≤ |emp Z n ω - predZ|} :=
    Set.setOf_subset_setOf.2 fun _ => le_of_lt
  have hle : μ.real {ω | τ < |emp Z n ω - predZ|} ≤ δ :=
    le_trans (measureReal_mono hsub (measure_ne_top μ _)) (by linarith)
  -- Convert the real-valued bound back to `ℝ≥0∞`.
  rw [← ENNReal.ofReal_toReal (measure_ne_top μ {ω | τ < |emp Z n ω - predZ|})]
  exact ENNReal.ofReal_le_ofReal hle

end BirkhoffTool
