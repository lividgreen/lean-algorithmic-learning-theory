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
* `birkhoffAverage_eq_empiricalMean` — the Birkhoff time-average along one orbit *is* the
  single-orbit empirical mean `SQOracle.empiricalMean`, definitionally.  This is the bridge between
  the two developments.
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
the single-orbit empirical mean `SQOracle.empiricalMean` of the query-ensemble `i ↦ φ ∘ shift^[i]`.
Definitional up to `smul = mul` on `ℝ`. -/
lemma birkhoffAverage_eq_empiricalMean (φ : (ℕ → X) → ℝ) (n : ℕ) (ω : ℕ → X) :
    birkhoffAverage ℝ shift φ n ω = empiricalMean (fun i => φ ∘ shift^[i]) n ω := by
  simp only [birkhoffAverage, birkhoffSum, empiricalMean, smul_eq_mul, Function.comp_apply]

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
    ∀ᵐ ω ∂μ,
      Tendsto (fun n => empiricalMean (fun i => φ ∘ shift^[i]) n ω) atTop (𝓝 (∫ x, φ x ∂μ)) := by
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
  have hfun : (fun n => empiricalMean (fun i => φ ∘ shift^[i]) n ω)
      = (birkhoffAverage ℝ shift φ · ω) := by
    funext n; exact (birkhoffAverage_eq_empiricalMean φ n ω).symm
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
    μ.real {ω | τ ≤ |empiricalMean Z n ω - predZ|} ≤ 2 * Real.exp (-(n : ℝ) * τ ^ 2 / (2 * c))

/-- **`MixingHoeffding` at `c = 1` is the i.i.d. case, genuinely** ([SQ] §3.2, Tool (i); FV-M).
The FJS-shaped hypothesis above is exactly `SQOracle.sq_oracle_concentration`'s conclusion once
`c = 1` collapses the denominator `2 * c` to `2`: an i.i.d. ensemble of trajectories satisfies
`MixingHoeffding` at the constant its own Hoeffding bound gives, with no mixing hypothesis needed. -/
theorem mixingHoeffding_of_iid
    (μ : Measure (ℕ → X)) [IsProbabilityMeasure μ]
    (Z : ℕ → (ℕ → X) → ℝ) (predZ : ℝ)
    (hmeas : ∀ i, Measurable (Z i))
    (hbdd : ∀ i, ∀ ω, Z i ω ∈ Set.Icc (-1 : ℝ) 1)
    (hindep : ProbabilityTheory.iIndepFun Z μ)
    (hmean : ∀ i, ∫ ω, Z i ω ∂μ = predZ) :
    MixingHoeffding μ Z predZ 1 := by
  intro n τ hn hτ
  simpa using SQOracle.sq_oracle_concentration Z predZ n τ hmeas hbdd hindep hmean hn hτ

/-- **The `c ≤ 0` vacuity of `MixingHoeffding`** ([Inevitability] §2, Definition 2.3's `e1` field —
the existential there quantifies `c` away). `MixingHoeffding μ Z predZ c` holds trivially whenever
`c ≤ 0`, for EVERY probability law `μ`, query ensemble `Z`, and target `predZ`: the mixing constant
carries the hypothesis's entire content, and this is the boundary at which it carries none. Real
division's `x / 0 = 0` convention pins the exponent at `0` when `c = 0`; at `c < 0` the exponent is
nonnegative for the opposite reason (a nonpositive numerator over a negative denominator). Either
way the right-hand side is `≥ 2`, dominating any probability. -/
theorem mixingHoeffding_of_nonpos
    (μ : Measure (ℕ → X)) [IsProbabilityMeasure μ]
    (Z : ℕ → (ℕ → X) → ℝ) (predZ c : ℝ) (hc : c ≤ 0) :
    MixingHoeffding μ Z predZ c := by
  intro n τ hn hτ
  have hnum : -(n : ℝ) * τ ^ 2 ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Nat.cast_nonneg n)) (sq_nonneg τ)
  have hden : 2 * c ≤ 0 := by linarith
  have hexpnonneg : 0 ≤ -(n : ℝ) * τ ^ 2 / (2 * c) := div_nonneg_of_nonpos hnum hden
  have hexp1 : (1 : ℝ) ≤ Real.exp (-(n : ℝ) * τ ^ 2 / (2 * c)) := Real.one_le_exp hexpnonneg
  have hmeasle : μ.real {ω | τ ≤ |empiricalMean Z n ω - predZ|} ≤ 1 :=
    MeasureTheory.measureReal_le_one
  linarith

/-- **`MixingHoeffding` at positive `c` is refutable: a frozen orbit is not mixing** ([Inevitability]
§5, Theorem 5.1(a): "the update is a permutation, so E1 fails"). The constant query ensemble
`Z i ≡ 1` against the declared answer `predZ = 0` witnesses this at every positive mixing constant
`c`: the empirical mean never moves off `1`, so the deviation event at tolerance `τ = 1` is the whole
space, and no exponential tail bound with a fixed positive `c` can dominate a probability pinned at
`1` for arbitrarily large `n`. `c ≤ 0` is excluded by hypothesis, as it must be — see
`mixingHoeffding_of_nonpos`. -/
theorem not_mixingHoeffding_pinned
    (μ : Measure (ℕ → X)) [IsProbabilityMeasure μ] {c : ℝ} (hc : 0 < c) :
    ¬ MixingHoeffding μ (fun (_ : ℕ) (_ : ℕ → X) => (1 : ℝ)) 0 c := by
  intro hmix
  set n₀ : ℕ := ⌈2 * c * Real.log 2⌉₊ + 1 with hn0def
  have hn0_ge : 1 ≤ n₀ := by omega
  have hb := hmix n₀ 1 hn0_ge (by norm_num)
  have hn0ne : n₀ ≠ 0 := by omega
  have hn0Rne : (n₀ : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn0ne
  have hempval : ∀ ω : ℕ → X, empiricalMean (fun (_ : ℕ) (_ : ℕ → X) => (1 : ℝ)) n₀ ω = 1 := by
    intro ω
    unfold empiricalMean
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    exact inv_mul_cancel₀ hn0Rne
  have hsetuniv :
      {ω : ℕ → X | (1 : ℝ) ≤ |empiricalMean (fun (_ : ℕ) (_ : ℕ → X) => (1 : ℝ)) n₀ ω - 0|}
        = Set.univ := by
    ext ω; simp [hempval ω]
  rw [hsetuniv, probReal_univ] at hb
  have hb' : (1 : ℝ) ≤ 2 * Real.exp (-(n₀ : ℝ) / (2 * c)) := by
    have heq : -(n₀ : ℝ) * (1 : ℝ) ^ 2 / (2 * c) = -(n₀ : ℝ) / (2 * c) := by ring
    rwa [heq] at hb
  have hexp_ge : (1 : ℝ) / 2 ≤ Real.exp (-(n₀ : ℝ) / (2 * c)) := by linarith
  have hcpos : (0 : ℝ) < 2 * c := by linarith
  have hgt : Real.log 2 * (2 * c) < (n₀ : ℝ) := by
    have h1 : (2 * c * Real.log 2 : ℝ) ≤ (⌈2 * c * Real.log 2⌉₊ : ℝ) := Nat.le_ceil _
    have heq2 : Real.log 2 * (2 * c) = 2 * c * Real.log 2 := by ring
    rw [heq2]
    calc (2 * c * Real.log 2 : ℝ) ≤ (⌈2 * c * Real.log 2⌉₊ : ℝ) := h1
      _ < (n₀ : ℝ) := by rw [hn0def]; push_cast; linarith
  have hkey : -(n₀ : ℝ) / (2 * c) < -Real.log 2 := by
    have heq : -(n₀ : ℝ) / (2 * c) = -((n₀ : ℝ) / (2 * c)) := by ring
    rw [heq]
    have hlog2c : Real.log 2 < (n₀ : ℝ) / (2 * c) := by
      rw [lt_div_iff₀ hcpos]; linarith [hgt]
    linarith [hlog2c]
  have hlt : Real.exp (-(n₀ : ℝ) / (2 * c)) < 1 / 2 := by
    have hlog2 : Real.log (1 / 2 : ℝ) = -Real.log 2 := by
      rw [show (1 : ℝ) / 2 = 2⁻¹ by norm_num, Real.log_inv]
    rw [show (1 : ℝ) / 2 = Real.exp (Real.log (1 / 2)) from (Real.exp_log (by norm_num)).symm,
      hlog2]
    exact Real.exp_lt_exp.mpr hkey
  linarith

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
    1 - δ ≤ μ.real {ω | |empiricalMean Z n ω - predZ| < τ} := by
  have hconc := hmix n τ hn1 hτ.le
  have hexple := mixing_exp_le_delta hc hτ hδ0 hn
  have hempmeas : Measurable (empiricalMean Z n) := by
    unfold empiricalMean
    exact (Finset.measurable_fun_sum (Finset.range n) (fun i _ => hmeas i)).const_mul _
  have hsetmeas : MeasurableSet {ω | τ ≤ |empiricalMean Z n ω - predZ|} :=
    measurableSet_le measurable_const ((hempmeas.sub_const predZ).abs)
  have hcompl : μ.real {ω | |empiricalMean Z n ω - predZ| < τ}
      = 1 - μ.real {ω | τ ≤ |empiricalMean Z n ω - predZ|} := by
    have hset : {ω | |empiricalMean Z n ω - predZ| < τ}
        = {ω | τ ≤ |empiricalMean Z n ω - predZ|}ᶜ := by
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
    μ {ω | τ < |empiricalMean Z n ω - predZ|} ≤ ENNReal.ofReal δ := by
  have hconc := hmix n τ hn1 hτ.le
  have hexple := mixing_exp_le_delta hc hτ hδ0 hn
  -- The strict-tail event sits inside the closed-tail event of `MixingHoeffding`.
  have hsub : {ω | τ < |empiricalMean Z n ω - predZ|} ⊆ {ω | τ ≤ |empiricalMean Z n ω - predZ|} :=
    Set.setOf_subset_setOf.2 fun _ => le_of_lt
  have hle : μ.real {ω | τ < |empiricalMean Z n ω - predZ|} ≤ δ :=
    le_trans (measureReal_mono hsub (measure_ne_top μ _)) (by linarith)
  -- Convert the real-valued bound back to `ℝ≥0∞`.
  rw [← ENNReal.ofReal_toReal (measure_ne_top μ {ω | τ < |empiricalMean Z n ω - predZ|})]
  exact ENNReal.ofReal_le_ofReal hle

/-- **Single-orbit noisy truth-survival** (from `MixingHoeffding`; [SQ] §3.1's window-noise budget,
carried to the single-trajectory route). Mirrors `SQOracle.sq_oracle_truth_survives_noisy`, with the
i.i.d.-ensemble sample complexity replaced by the single-orbit `mixing_oracle_sample_complexity`:
with `n ≥ (2c/τ²)·log(2/δ)` single-orbit steps and window-noise budget `2η ≤ τ`, the
deterministic-prediction truth `predR`'s statistic lies within `2τ` of the empirical answer with
probability `≥ 1 − δ` — so the *unchanged* `2τ`-pruning rule never discards it, on a mixing
trajectory rather than an i.i.d. ensemble. At `η = 0` (forcing `a = predR`) this composes
`mixing_oracle_sample_complexity` with `SQVersionSpace.truth_survives_pruning`. -/
theorem mixing_oracle_truth_survives_noisy
    (μ : Measure (ℕ → X)) [IsProbabilityMeasure μ]
    (Z : ℕ → (ℕ → X) → ℝ) (predR a c : ℝ) (n : ℕ) (τ δ η : ℝ)
    (hmix : MixingHoeffding μ Z a c) (hc : 0 < c)
    (hmeas : ∀ i, Measurable (Z i))
    (hn1 : 1 ≤ n) (hτ : 0 < τ) (hδ0 : 0 < δ)
    (hn : (2 * c / τ ^ 2) * Real.log (2 / δ) ≤ (n : ℝ))
    (hη : 0 ≤ η) (hbudget : 2 * η ≤ τ) (hnoise : |a - predR| ≤ 2 * η) :
    1 - δ ≤ μ.real {ω | |predR - empiricalMean Z n ω| ≤ 2 * τ} := by
  have hsc := mixing_oracle_sample_complexity μ Z a c n τ δ hmix hc hmeas hn1 hτ hδ0 hn
  refine hsc.trans (measureReal_mono ?_ (measure_ne_top μ _))
  intro ω hω
  simp only [Set.mem_setOf_eq] at hω ⊢
  exact SQVersionSpace.truth_survives_pruning_noisy predR a (empiricalMean Z n ω) τ η hτ.le hη
    hbudget hω.le hnoise

end BirkhoffTool
