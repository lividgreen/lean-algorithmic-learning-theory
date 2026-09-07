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
  `ALT.MarkovHoeffding.mixingHoeffding_of_gap` DERIVES it, for a finite-state chain, from an
  operator-norm spectral gap (`GapContraction`) and a chain trajectory law (`IsChainMeasure`), at
  an explicit constant `cGap lam`; here it stays a named premise, exactly as the qualitative
  Tool (i) does not by itself give a rate.  The derivation's own `IsChainMeasure` hypothesis is
  now discharged unconditionally too: `ALT.MarkovHoeffding.exists_mixingHoeffding_of_gap` supplies
  a chain measure for every `Stochastic`/`GapContraction` pair, via Mathlib's Ionescu-Tulcea
  construction.  At `c = 1` (`λ = 0`, i.i.d.) it is exactly `SQOracle.sq_oracle_concentration`.
* `mixing_oracle_sample_complexity`, `mixing_oracle_tail` — the oracle-error corollaries derived
  *from* `MixingHoeffding`: `n ≥ (2c/τ²)·log(2/δ)` single-orbit steps answer an SQ query to
  tolerance `τ` with confidence `≥ 1 − δ`, in the exact shapes the FV-E interface
  (`SQOracle.sq_oracle_sample_complexity` / `SQOracle.empirical_isSQOracle`) consumes.  Each is now
  a one-liner off its own finite-horizon `MixingHoeffdingTo` twin, below.
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
the i.i.d. case) the two coincide.  It is stated as a *hypothesis*: `ALT.MarkovHoeffding.
mixingHoeffding_of_gap` derives it, for a finite-state chain, from an operator-norm spectral gap
and a chain trajectory law, at an explicit (non-sharp) constant `cGap lam`; `ALT.MarkovHoeffding.
exists_mixingHoeffding_of_gap` supplies that chain trajectory law too, unconditionally. -/
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

/-! ## `MixingHoeffding` from a deterministic deviation envelope, measure-agnostic

No probability computation is needed: a deterministic bound on how far the empirical mean can
stray from the declared answer, at every sample size, already forces the FJS tail bound at every
probability law supported on the trajectories obeying it — the vacuity lemma above is this
lemma's `E = 0` case, and a Dirac law is its single-point case. -/

/-- The arithmetic core, shared by the measure-agnostic lemma and its Dirac corollary: once
`n * τ² ≤ E²`, the FJS tail bound's own right side is already at least `1`. -/
private lemma one_le_two_exp_of_deviation {n : ℕ} {τ E : ℝ} (_hn : 1 ≤ n) (_hτnn : 0 ≤ τ)
    (_hE : 0 ≤ E) (hnτ2 : (n : ℝ) * τ ^ 2 ≤ E ^ 2) :
    (1 : ℝ) ≤ 2 * Real.exp (-(n : ℝ) * τ ^ 2 / (2 * (E ^ 2 / (2 * Real.log 2)))) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set c := E ^ 2 / (2 * Real.log 2) with hcdef
  have hc2 : 2 * c * Real.log 2 = E ^ 2 := by rw [hcdef]; field_simp
  rcases eq_or_lt_of_le (show (0 : ℝ) ≤ c from by rw [hcdef]; positivity) with hc0 | hcpos
  · rw [← hc0, mul_zero, div_zero, Real.exp_zero]
    norm_num
  · have hstep : (n : ℝ) * τ ^ 2 / (2 * c) ≤ Real.log 2 := by
      rw [div_le_iff₀ (by linarith)]
      nlinarith [hnτ2, hc2]
    have hle : -Real.log 2 ≤ -(n : ℝ) * τ ^ 2 / (2 * c) := by
      have heq : -(n : ℝ) * τ ^ 2 / (2 * c) = -((n : ℝ) * τ ^ 2 / (2 * c)) := by ring
      rw [heq]; linarith
    have hexp := Real.exp_le_exp.mpr hle
    have heq2 : Real.exp (-Real.log 2) = 1 / 2 := by
      rw [Real.exp_neg, Real.exp_log (by norm_num)]; norm_num
    rw [heq2] at hexp
    linarith

/-- **`MixingHoeffding` from a deterministic deviation envelope** ([Inevitability]'s membership
endgame; the measure-form reading over a finite host's phase law). For ANY probability law `μ`,
once a deviation bound `n * |empiricalMean Z n ω - predZ| ≤ E` holds `μ`-a.e. at every sample size
`n ≥ 1`, `μ` satisfies `MixingHoeffding` at the constant `E² / (2 ln 2)` — no probability
computation, measurability, or independence assumption needed.

Proof: fix `n ≥ 1`, `τ ≥ 0`. Past `τ = E/n` the deviation event is `μ`-a.e. empty (the envelope
already keeps `|empiricalMean Z n ω - predZ| ≤ E/n < τ`), so its measure is `0`. Below `τ = E/n`,
`n·τ² ≤ E²`, and `one_le_two_exp_of_deviation` shows this already forces the tail bound's own right
side above `1`, which dominates any probability. -/
theorem mixingHoeffding_of_deviation_bound
    (μ : Measure (ℕ → X)) [IsProbabilityMeasure μ]
    (Z : ℕ → (ℕ → X) → ℝ) (predZ E : ℝ) (hE : 0 ≤ E)
    (hbound : ∀ᵐ ω ∂μ, ∀ n : ℕ, 1 ≤ n → (n : ℝ) * |empiricalMean Z n ω - predZ| ≤ E) :
    MixingHoeffding μ Z predZ (E ^ 2 / (2 * Real.log 2)) := by
  intro n τ hn hτ
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  by_cases hτlarge : E / (n : ℝ) < τ
  · have hnull : μ {ω | ¬ ∀ k : ℕ, 1 ≤ k → (k : ℝ) * |empiricalMean Z k ω - predZ| ≤ E} = 0 :=
      MeasureTheory.ae_iff.mp hbound
    have hsub : {ω | τ ≤ |empiricalMean Z n ω - predZ|} ⊆
        {ω | ¬ ∀ k : ℕ, 1 ≤ k → (k : ℝ) * |empiricalMean Z k ω - predZ| ≤ E} := by
      intro ω hω hcon
      have hb := hcon n hn
      have hle : |empiricalMean Z n ω - predZ| ≤ E / n := by
        rw [le_div_iff₀ hnR, mul_comm]; exact hb
      have hτle := le_trans hω hle
      linarith [hτlarge]
    have hSz : μ {ω | τ ≤ |empiricalMean Z n ω - predZ|} = 0 := measure_mono_null hsub hnull
    have hSreal : μ.real {ω | τ ≤ |empiricalMean Z n ω - predZ|} = 0 := by
      simp [Measure.real, hSz]
    rw [hSreal]
    positivity
  · push Not at hτlarge
    have hb2 : (n : ℝ) * τ ≤ E := by rw [mul_comm]; exact (le_div_iff₀ hnR).mp hτlarge
    have hnτnn : 0 ≤ (n : ℝ) * τ := mul_nonneg (Nat.cast_nonneg n) hτ
    have hsq : (n : ℝ) * τ * ((n : ℝ) * τ) ≤ E * E := mul_le_mul hb2 hb2 hnτnn hE
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hnτ2 : (n : ℝ) * τ ^ 2 ≤ E ^ 2 := by
      nlinarith [hsq, hn1, sq_nonneg τ, mul_nonneg (sub_nonneg.mpr hn1) (sq_nonneg τ)]
    have h1 := one_le_two_exp_of_deviation hn hτ hE hnτ2
    linarith [measureReal_le_one (μ := μ) (s := {ω | τ ≤ |empiricalMean Z n ω - predZ|})]

/-- **The Dirac corollary of `mixingHoeffding_of_deviation_bound`.** At a single fixed trajectory
`ω₀`, the a.e. hypothesis collapses to a pointwise one: `MixingHoeffding` at `Measure.dirac ω₀`
follows directly from the deviation bound holding at `ω₀` itself. Needs measurability of the
query ensemble to compute the Dirac measure of the (possibly non-open/closed) deviation event,
the same requirement `GrowingComposite.mixingHoeffding_dirac_iff` carries. -/
theorem mixingHoeffding_dirac_of_deviation_bound
    (ω₀ : ℕ → X) (Z : ℕ → (ℕ → X) → ℝ) (predZ E : ℝ) (hE : 0 ≤ E)
    (hmeas : ∀ i, Measurable (Z i))
    (hbound : ∀ n : ℕ, 1 ≤ n → (n : ℝ) * |empiricalMean Z n ω₀ - predZ| ≤ E) :
    MixingHoeffding (Measure.dirac ω₀) Z predZ (E ^ 2 / (2 * Real.log 2)) := by
  intro n τ hn hτ
  have hempmeas : Measurable (empiricalMean Z n) :=
    (Finset.measurable_fun_sum (Finset.range n) fun i _ => hmeas i).const_mul _
  have hAmeas : MeasurableSet {ω | τ ≤ |empiricalMean Z n ω - predZ|} :=
    measurableSet_le measurable_const ((hempmeas.sub_const predZ).abs)
  by_cases hmem : τ ≤ |empiricalMean Z n ω₀ - predZ|
  · have hval : (Measure.dirac ω₀).real {ω | τ ≤ |empiricalMean Z n ω - predZ|} = 1 := by
      rw [Measure.real, Measure.dirac_apply' ω₀ hAmeas]
      simp [Set.indicator, hmem]
    rw [hval]
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have hb := hbound n hn
    have hle : |empiricalMean Z n ω₀ - predZ| ≤ E / n := by
      rw [le_div_iff₀ hnR, mul_comm]; exact hb
    have hτEn : τ ≤ E / n := le_trans hmem hle
    have hb2 : (n : ℝ) * τ ≤ E := by rw [mul_comm]; exact (le_div_iff₀ hnR).mp hτEn
    have hnτnn : 0 ≤ (n : ℝ) * τ := mul_nonneg (Nat.cast_nonneg n) hτ
    have hsq : (n : ℝ) * τ * ((n : ℝ) * τ) ≤ E * E := mul_le_mul hb2 hb2 hnτnn hE
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hnτ2 : (n : ℝ) * τ ^ 2 ≤ E ^ 2 := by
      nlinarith [hsq, hn1, sq_nonneg τ, mul_nonneg (sub_nonneg.mpr hn1) (sq_nonneg τ)]
    exact one_le_two_exp_of_deviation hn hτ hE hnτ2
  · have hval : (Measure.dirac ω₀).real {ω | τ ≤ |empiricalMean Z n ω - predZ|} = 0 := by
      rw [Measure.real, Measure.dirac_apply' ω₀ hAmeas]
      simp [Set.indicator, hmem]
    rw [hval]
    positivity

/-! ## Finite-horizon `MixingHoeffding`: the predicate `MixingHoeffdingTo`

No consumer of `MixingHoeffding` above uses more than one sample size — verified at the three
oracle corollaries and at `not_mixingHoeffding_pinned`'s own witness: each applies the hypothesis
at exactly the `n` its own bound names.  `MixingHoeffdingTo`
restricts the quantifier to a finite horizon `N` and changes nothing else, so every conclusion above
is available verbatim for a run whose sample size clears its own bound inside the horizon.  All
three oracle corollaries below now carry exactly that bounded twin (`mixing_oracle_tail_to`,
`mixing_oracle_sample_complexity_to`, `mixing_oracle_truth_survives_noisy_to`), each unbounded form
recovered from its own twin at `N := n`. -/

/-- **`MixingHoeffding` bounded to a finite horizon `N`.**  `MixingHoeffding` with its `∀ n`
quantifier restricted to `n ≤ N`, and nothing else moved: the reference answer stays the declared
stationary `predZ`, not the orbit's own cycle average — against the cycle average the predicate
would hold trivially at any horizon past the period while delivering nothing a consumer uses — and
the constant keeps the FJS shape and the `[−1, 1]` normalization, so every consumer of
`MixingHoeffding` above applies verbatim at `n ≤ N`.
`mixingHoeffding_iff_forall_mixingHoeffdingTo` recovers `MixingHoeffding` as the quantifier over
every horizon. -/
def MixingHoeffdingTo (N : ℕ) (μ : Measure (ℕ → X)) (Z : ℕ → (ℕ → X) → ℝ) (predZ c : ℝ) : Prop :=
  ∀ (n : ℕ) (τ : ℝ), 1 ≤ n → n ≤ N → 0 ≤ τ →
    μ.real {ω | τ ≤ |empiricalMean Z n ω - predZ|} ≤ 2 * Real.exp (-(n : ℝ) * τ ^ 2 / (2 * c))

/-- The unbounded hypothesis implies the bounded one at every horizon: dropping `n ≤ N` only widens
the universal it must satisfy. -/
theorem mixingHoeffdingTo_of_mixingHoeffding (N : ℕ) (μ : Measure (ℕ → X))
    (Z : ℕ → (ℕ → X) → ℝ) (predZ c : ℝ) (h : MixingHoeffding μ Z predZ c) :
    MixingHoeffdingTo N μ Z predZ c :=
  fun n τ hn _ hτ => h n τ hn hτ

/-- **`MixingHoeffding` is the bounded predicate at every horizon.**  The unbounded hypothesis holds
iff the bounded one holds at every `N`: the forward direction drops `n ≤ N`
(`mixingHoeffdingTo_of_mixingHoeffding`), and the converse instantiates at `N := n` via `le_rfl`. -/
theorem mixingHoeffding_iff_forall_mixingHoeffdingTo (μ : Measure (ℕ → X))
    (Z : ℕ → (ℕ → X) → ℝ) (predZ c : ℝ) :
    MixingHoeffding μ Z predZ c ↔ ∀ N, MixingHoeffdingTo N μ Z predZ c :=
  ⟨fun h N => mixingHoeffdingTo_of_mixingHoeffding N μ Z predZ c h,
    fun h n τ hn hτ => h n n τ hn le_rfl hτ⟩

/-- **The vacuity floor for `MixingHoeffdingTo`.**  Below the horizon `N ≤ c·log 2 / 2`, every
`[−1, 1]`-normalized law satisfies the predicate — the finite-horizon sibling of
`mixingHoeffding_of_nonpos`'s `c ≤ 0` vacuity, and the reason a finite-horizon E1 claim must travel
with its horizon stated against its constant. At tolerance `τ ≤ 2` the tail bound's right side is
already `≥ 1`, since `n·τ² ≤ 4n ≤ 4N ≤ 2c·log 2`; past `τ = 2` the deviation event is empty outright,
since a `[−1, 1]`-bounded ensemble's empirical mean, against a `[−1, 1]`-bounded declared answer,
never strays more than `2`. -/
theorem mixingHoeffdingTo_of_le_floor
    (μ : Measure (ℕ → X)) [IsProbabilityMeasure μ]
    (Z : ℕ → (ℕ → X) → ℝ) (predZ c : ℝ) (N : ℕ) (hc : 0 < c)
    (hZ : ∀ i ω, Z i ω ∈ Set.Icc (-1 : ℝ) 1) (hpred : predZ ∈ Set.Icc (-1 : ℝ) 1)
    (hN : (N : ℝ) ≤ c * Real.log 2 / 2) :
    MixingHoeffdingTo N μ Z predZ c := by
  intro n τ hn hnN hτ
  have hnR : (n : ℝ) ≤ (N : ℝ) := by exact_mod_cast hnN
  by_cases hτ2 : τ ≤ 2
  · -- below tolerance `2` the bound's own right side has not yet dropped under `1`
    have hτsq : τ ^ 2 ≤ 4 := by nlinarith [hτ, hτ2]
    have hbound : (n : ℝ) * τ ^ 2 ≤ 2 * c * Real.log 2 := by
      have h4n : (n : ℝ) * τ ^ 2 ≤ 4 * (n : ℝ) :=
        by nlinarith [mul_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ (n : ℝ)) (by linarith : (0:ℝ) ≤ 4 - τ ^ 2)]
      linarith [hnR, hN]
    have hstep : (n : ℝ) * τ ^ 2 / (2 * c) ≤ Real.log 2 := by
      rw [div_le_iff₀ (by positivity)]; nlinarith [hbound]
    have hle : -Real.log 2 ≤ -(n : ℝ) * τ ^ 2 / (2 * c) := by
      have heq : -(n : ℝ) * τ ^ 2 / (2 * c) = -((n : ℝ) * τ ^ 2 / (2 * c)) := by ring
      rw [heq]; linarith [hstep]
    have hexp := Real.exp_le_exp.mpr hle
    have heq2 : Real.exp (-Real.log 2) = 1 / 2 := by
      rw [Real.exp_neg, Real.exp_log (by norm_num)]; norm_num
    rw [heq2] at hexp
    have hrhs : (1 : ℝ) ≤ 2 * Real.exp (-(n : ℝ) * τ ^ 2 / (2 * c)) := by linarith
    exact le_trans MeasureTheory.measureReal_le_one hrhs
  · -- past tolerance `2` the deviation event is empty outright
    replace hτ2 : 2 < τ := not_le.mp hτ2
    have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hempty : {ω : ℕ → X | τ ≤ |empiricalMean Z n ω - predZ|} = ∅ := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_le]
      have hZbound : |empiricalMean Z n ω| ≤ 1 := by
        unfold empiricalMean
        rw [abs_mul, abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg n))]
        have hsum : |∑ i ∈ Finset.range n, Z i ω| ≤ (n : ℝ) := by
          calc |∑ i ∈ Finset.range n, Z i ω| ≤ ∑ i ∈ Finset.range n, |Z i ω| :=
                Finset.abs_sum_le_sum_abs _ _
            _ ≤ ∑ i ∈ Finset.range n, (1 : ℝ) :=
                Finset.sum_le_sum fun i _ => abs_le.mpr (Set.mem_Icc.mp (hZ i ω))
            _ = (n : ℝ) := by simp
        calc (n : ℝ)⁻¹ * |∑ i ∈ Finset.range n, Z i ω| ≤ (n : ℝ)⁻¹ * (n : ℝ) :=
              mul_le_mul_of_nonneg_left hsum (by positivity)
          _ = 1 := inv_mul_cancel₀ hn0
      have hpredbound : |predZ| ≤ 1 := abs_le.mpr (Set.mem_Icc.mp hpred)
      have htri : |empiricalMean Z n ω - predZ| ≤ |empiricalMean Z n ω| + |predZ| := by
        have h := abs_add_le (empiricalMean Z n ω) (-predZ)
        simpa [sub_eq_add_neg, abs_neg] using h
      linarith [htri, hZbound, hpredbound]
    rw [hempty, measureReal_empty]
    positivity

/-- **`MixingHoeffdingTo` at positive `c` is refutable past its own vacuity floor.**  The same
pinned witness as `not_mixingHoeffding_pinned` — the constant ensemble `Z i ≡ 1` against
`predZ = 0` — refutes the bounded predicate at every horizon `N ≥ ⌈2c·log 2⌉₊ + 1`: that is the same
`n₀` the unbounded refutation fixes, so instantiating `hmix` there needs only `n₀ ≤ N`.  Below that
horizon `mixingHoeffdingTo_of_le_floor` already covers every law, so the two results meet exactly at
the threshold the floor names — a large enough `c` drops `N` under the floor and every law passes,
which is the floor working rather than the guard failing. -/
theorem not_mixingHoeffdingTo_pinned
    (μ : Measure (ℕ → X)) [IsProbabilityMeasure μ] {c : ℝ} (hc : 0 < c) {N : ℕ}
    (hN : ⌈2 * c * Real.log 2⌉₊ + 1 ≤ N) :
    ¬ MixingHoeffdingTo N μ (fun (_ : ℕ) (_ : ℕ → X) => (1 : ℝ)) 0 c := by
  intro hmix
  set n₀ : ℕ := ⌈2 * c * Real.log 2⌉₊ + 1 with hn0def
  have hn0_ge : 1 ≤ n₀ := by omega
  have hb := hmix n₀ 1 hn0_ge hN (by norm_num)
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

/-- **`MixingHoeffding` at positive `c` is refutable: a frozen orbit is not mixing** ([Inevitability]
§5, Theorem 5.1(a): "the update is a permutation, so E1 fails"). The constant query ensemble
`Z i ≡ 1` against the declared answer `predZ = 0` witnesses this at every positive mixing constant
`c`: the empirical mean never moves off `1`, so the deviation event at tolerance `τ = 1` is the whole
space, and no exponential tail bound with a fixed positive `c` can dominate a probability pinned at
`1` for arbitrarily large `n`. `c ≤ 0` is excluded by hypothesis, as it must be — see
`mixingHoeffding_of_nonpos`. See `not_mixingHoeffdingTo_pinned` for the finite-horizon form this
specializes. -/
theorem not_mixingHoeffding_pinned
    (μ : Measure (ℕ → X)) [IsProbabilityMeasure μ] {c : ℝ} (hc : 0 < c) :
    ¬ MixingHoeffding μ (fun (_ : ℕ) (_ : ℕ → X) => (1 : ℝ)) 0 c := fun hmix =>
  not_mixingHoeffdingTo_pinned μ hc le_rfl
    (mixingHoeffdingTo_of_mixingHoeffding _ μ (fun (_ : ℕ) (_ : ℕ → X) => (1 : ℝ)) 0 c hmix)

/-- **A periodic empirical mean, disagreeing with the declared answer, refutes `MixingHoeffding`.**
A process whose empirical mean is a constant `avg` at every positive multiple of a period `Pd` —
the observation process of any deterministic finite host, whose orbit must eventually repeat —
refutes the unbounded predicate at every positive mixing constant `c`: the deviation from the
declared answer `predZ` is the fixed gap `|avg − predZ|` at every one of those `n`, so the tail
event is the whole space at tolerance `τ = |avg − predZ| / 2`, and no fixed positive `c` can keep
the exponential bound below `1` for arbitrarily large `n`. `not_mixingHoeffding_pinned` is the
`Pd = 1`, `avg = 1`, `predZ = 0` case; stating this one beside it is the point.

This is the exact obstruction a periodic host faces: a finite deterministic system's observation
process is periodic, so unless its declared answers are its own period averages, no positive
constant saves it — a guard family in the corpus's usual sense, kept beside the theorem whose
`e1` hypothesis it makes load-bearing. -/
theorem not_mixingHoeffding_of_periodic_ne
    (μ : Measure (ℕ → X)) [IsProbabilityMeasure μ] (Z : ℕ → (ℕ → X) → ℝ) (predZ c avg : ℝ)
    (hc : 0 < c) (Pd : ℕ) (hPd : 0 < Pd)
    (hper : ∀ ω, ∀ m : ℕ, 0 < m → empiricalMean Z (m * Pd) ω = avg)
    (hne : avg ≠ predZ) :
    ¬ MixingHoeffding μ Z predZ c := by
  intro hmix
  have hgap : (0 : ℝ) < |avg - predZ| := abs_pos.mpr (sub_ne_zero.mpr hne)
  set τ : ℝ := |avg - predZ| / 2 with hτdef
  have hτpos : 0 < τ := by rw [hτdef]; linarith
  set n₀ : ℕ := ⌈2 * c * Real.log 2 / τ ^ 2⌉₊ + 1 with hn0def
  have hn0_pos : 0 < n₀ := by omega
  have hn_ge_n0 : n₀ ≤ n₀ * Pd := Nat.le_mul_of_pos_right n₀ hPd
  have hn1 : 1 ≤ n₀ * Pd := le_trans hn0_pos hn_ge_n0
  have hb := hmix (n₀ * Pd) τ hn1 hτpos.le
  have hval : empiricalMean Z (n₀ * Pd) = fun _ => avg := funext fun ω => hper ω n₀ hn0_pos
  have hsetuniv : {ω : ℕ → X | τ ≤ |empiricalMean Z (n₀ * Pd) ω - predZ|} = Set.univ := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true, hval, hτdef]
    linarith [hgap]
  rw [hsetuniv, probReal_univ] at hb
  have hgt : (2 * c * Real.log 2 : ℝ) < (n₀ : ℝ) * τ ^ 2 := by
    have hlt : (2 * c * Real.log 2 / τ ^ 2 : ℝ) < (n₀ : ℝ) := by
      rw [hn0def]; push_cast
      exact lt_of_le_of_lt (Nat.le_ceil _) (by linarith)
    calc (2 * c * Real.log 2 : ℝ) = (2 * c * Real.log 2 / τ ^ 2) * τ ^ 2 := by
          field_simp
      _ < (n₀ : ℝ) * τ ^ 2 := mul_lt_mul_of_pos_right hlt (by positivity)
  have hnR : (n₀ : ℝ) ≤ ((n₀ * Pd : ℕ) : ℝ) := by exact_mod_cast hn_ge_n0
  have hgt' : (2 * c * Real.log 2 : ℝ) < ((n₀ * Pd : ℕ) : ℝ) * τ ^ 2 :=
    lt_of_lt_of_le hgt (mul_le_mul_of_nonneg_right hnR (sq_nonneg τ))
  have hcpos : (0 : ℝ) < 2 * c := by linarith
  have hkey : -(((n₀ * Pd : ℕ) : ℝ)) * τ ^ 2 / (2 * c) < -Real.log 2 := by
    have heq : -(((n₀ * Pd : ℕ) : ℝ)) * τ ^ 2 / (2 * c)
        = -(((n₀ * Pd : ℕ) : ℝ) * τ ^ 2 / (2 * c)) := by ring
    rw [heq]
    have hlog2c : Real.log 2 < ((n₀ * Pd : ℕ) : ℝ) * τ ^ 2 / (2 * c) := by
      rw [lt_div_iff₀ hcpos]; linarith [hgt']
    linarith [hlog2c]
  have hlt2 : Real.exp (-(((n₀ * Pd : ℕ) : ℝ)) * τ ^ 2 / (2 * c)) < 1 / 2 := by
    have hlog2 : Real.log (1 / 2 : ℝ) = -Real.log 2 := by
      rw [show (1 : ℝ) / 2 = 2⁻¹ by norm_num, Real.log_inv]
    rw [show (1 : ℝ) / 2 = Real.exp (Real.log (1 / 2)) from (Real.exp_log (by norm_num)).symm,
      hlog2]
    exact Real.exp_lt_exp.mpr hkey
  linarith

/-- **`MixingHoeffdingTo` is monotone in the mixing constant.** A schedule's queries carry
different mixing constants (`LearningWitness.scheduledConst` branches between `samePairConst` and
`pairConst`); this lifts a per-query `MixingHoeffdingTo` at its own constant `c` to any larger
constant `c'`, since widening the FJS variance proxy only weakens the tail bound. -/
theorem mixingHoeffdingTo_mono_const
    (μ : Measure (ℕ → X)) (Z : ℕ → (ℕ → X) → ℝ) (predZ : ℝ) {c c' : ℝ} (N : ℕ)
    (hcc : c ≤ c') (hc : 0 < c) (h : MixingHoeffdingTo N μ Z predZ c) :
    MixingHoeffdingTo N μ Z predZ c' := by
  intro n τ hn1 hnN hτ
  refine (h n τ hn1 hnN hτ).trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by norm_num))
  have hc' : 0 < c' := lt_of_lt_of_le hc hcc
  have hx : (0 : ℝ) ≤ (n : ℝ) * τ ^ 2 := mul_nonneg (Nat.cast_nonneg n) (sq_nonneg τ)
  have hdiv : (n : ℝ) * τ ^ 2 / (2 * c') ≤ (n : ℝ) * τ ^ 2 / (2 * c) :=
    div_le_div_of_nonneg_left hx (by linarith) (by linarith)
  have heq1 : -(n : ℝ) * τ ^ 2 / (2 * c) = -((n : ℝ) * τ ^ 2 / (2 * c)) := by ring
  have heq2 : -(n : ℝ) * τ ^ 2 / (2 * c') = -((n : ℝ) * τ ^ 2 / (2 * c')) := by ring
  rw [heq1, heq2]
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

/-- **Single-orbit oracle sample complexity, finite horizon** (from `MixingHoeffdingTo`), in the
exact shape `mixing_oracle_truth_survives_noisy_to` consumes: with `n ≥ (2c/τ²)·log(2/δ)` and
`n ≤ N`, `n` single-orbit steps answer the SQ query to tolerance `τ` with confidence `≥ 1 − δ`. The
bounded twin of `mixing_oracle_sample_complexity`, which is recovered from it below via
`mixingHoeffdingTo_of_mixingHoeffding`, the same pattern as `mixing_oracle_tail_to`. -/
theorem mixing_oracle_sample_complexity_to
    (μ : Measure (ℕ → X)) [IsProbabilityMeasure μ]
    (Z : ℕ → (ℕ → X) → ℝ) (predZ c : ℝ) (N n : ℕ) (τ δ : ℝ)
    (hmix : MixingHoeffdingTo N μ Z predZ c) (hc : 0 < c) (hmeas : ∀ i, Measurable (Z i))
    (hn1 : 1 ≤ n) (hnN : n ≤ N) (hτ : 0 < τ) (hδ0 : 0 < δ)
    (hn : (2 * c / τ ^ 2) * Real.log (2 / δ) ≤ (n : ℝ)) :
    1 - δ ≤ μ.real {ω | |empiricalMean Z n ω - predZ| < τ} := by
  have hconc := hmix n τ hn1 hnN hτ.le
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
      ext ω; simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, not_le]
    rw [hset, measureReal_compl hsetmeas, probReal_univ]
  rw [hcompl]; linarith

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
    1 - δ ≤ μ.real {ω | |empiricalMean Z n ω - predZ| < τ} :=
  mixing_oracle_sample_complexity_to μ Z predZ c n n τ δ
    (mixingHoeffdingTo_of_mixingHoeffding n μ Z predZ c hmix) hc hmeas hn1 le_rfl hτ hδ0 hn

/-- **Single-orbit oracle tail bound, finite horizon** (from `MixingHoeffdingTo`), in the exact
shape the FV-E oracle object `SQOracle.empirical_isSQOracle` consumes: with `n ≥ (2c/τ²)·log(2/δ)`
and `n ≤ N`, the single-orbit empirical answer fails tolerance `τ` with probability `≤ δ`. The
bounded twin of `mixing_oracle_tail`, which is recovered from it below via
`mixingHoeffdingTo_of_mixingHoeffding`. -/
theorem mixing_oracle_tail_to
    (μ : Measure (ℕ → X)) [IsProbabilityMeasure μ]
    (Z : ℕ → (ℕ → X) → ℝ) (predZ c : ℝ) (N n : ℕ) (τ δ : ℝ)
    (hmix : MixingHoeffdingTo N μ Z predZ c) (hc : 0 < c)
    (hn1 : 1 ≤ n) (hnN : n ≤ N) (hτ : 0 < τ) (hδ0 : 0 < δ)
    (hn : (2 * c / τ ^ 2) * Real.log (2 / δ) ≤ (n : ℝ)) :
    μ {ω | τ < |empiricalMean Z n ω - predZ|} ≤ ENNReal.ofReal δ := by
  have hconc := hmix n τ hn1 hnN hτ.le
  have hexple := mixing_exp_le_delta hc hτ hδ0 hn
  -- The strict-tail event sits inside the closed-tail event of `MixingHoeffdingTo`.
  have hsub : {ω | τ < |empiricalMean Z n ω - predZ|} ⊆ {ω | τ ≤ |empiricalMean Z n ω - predZ|} :=
    Set.ofPred_subset_ofPred.2 fun _ => le_of_lt
  have hle : μ.real {ω | τ < |empiricalMean Z n ω - predZ|} ≤ δ :=
    le_trans (measureReal_mono hsub (measure_ne_top μ _)) (by linarith)
  -- Convert the real-valued bound back to `ℝ≥0∞`.
  rw [← ENNReal.ofReal_toReal (measure_ne_top μ {ω | τ < |empiricalMean Z n ω - predZ|})]
  exact ENNReal.ofReal_le_ofReal hle

/-- **Single-orbit oracle tail bound** (from `MixingHoeffding`), in the exact shape the FV-E oracle
object `SQOracle.empirical_isSQOracle` consumes: with `n ≥ (2c/τ²)·log(2/δ)`, the single-orbit
empirical answer fails tolerance `τ` with probability `≤ δ`. -/
theorem mixing_oracle_tail
    (μ : Measure (ℕ → X)) [IsProbabilityMeasure μ]
    (Z : ℕ → (ℕ → X) → ℝ) (predZ c : ℝ) (n : ℕ) (τ δ : ℝ)
    (hmix : MixingHoeffding μ Z predZ c) (hc : 0 < c)
    (hn1 : 1 ≤ n) (hτ : 0 < τ) (hδ0 : 0 < δ)
    (hn : (2 * c / τ ^ 2) * Real.log (2 / δ) ≤ (n : ℝ)) :
    μ {ω | τ < |empiricalMean Z n ω - predZ|} ≤ ENNReal.ofReal δ :=
  mixing_oracle_tail_to μ Z predZ c n n τ δ
    (mixingHoeffdingTo_of_mixingHoeffding n μ Z predZ c hmix) hc hn1 le_rfl hτ hδ0 hn

/-- **Single-orbit noisy truth-survival, finite horizon** (from `MixingHoeffdingTo`; [SQ] §3.1's
window-noise budget, carried to the single-trajectory route). The bounded twin of
`mixing_oracle_truth_survives_noisy`, which is recovered from it below via
`mixingHoeffdingTo_of_mixingHoeffding`: with `n ≥ (2c/τ²)·log(2/δ)`, `n ≤ N`, and window-noise
budget `2η ≤ τ`, the deterministic-prediction truth `predR`'s statistic lies within `2τ` of the
empirical answer with probability `≥ 1 − δ`. Consumes `mixing_oracle_sample_complexity_to` for the
concentration half and passes the mixing hypothesis down without applying it itself, which is why
the horizon threads through unused past the first line. -/
theorem mixing_oracle_truth_survives_noisy_to
    (μ : Measure (ℕ → X)) [IsProbabilityMeasure μ]
    (Z : ℕ → (ℕ → X) → ℝ) (predR a c : ℝ) (N n : ℕ) (τ δ η : ℝ)
    (hmix : MixingHoeffdingTo N μ Z a c) (hc : 0 < c)
    (hmeas : ∀ i, Measurable (Z i))
    (hn1 : 1 ≤ n) (hnN : n ≤ N) (hτ : 0 < τ) (hδ0 : 0 < δ)
    (hn : (2 * c / τ ^ 2) * Real.log (2 / δ) ≤ (n : ℝ))
    (hη : 0 ≤ η) (hbudget : 2 * η ≤ τ) (hnoise : |a - predR| ≤ 2 * η) :
    1 - δ ≤ μ.real {ω | |predR - empiricalMean Z n ω| ≤ 2 * τ} := by
  have hsc := mixing_oracle_sample_complexity_to μ Z a c N n τ δ hmix hc hmeas hn1 hnN hτ hδ0 hn
  refine hsc.trans (measureReal_mono ?_ (measure_ne_top μ _))
  intro ω hω
  simp only [Set.mem_ofPred_eq] at hω ⊢
  exact SQVersionSpace.truth_survives_pruning_noisy predR a (empiricalMean Z n ω) τ η hτ.le hη
    hbudget hω.le hnoise

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
    1 - δ ≤ μ.real {ω | |predR - empiricalMean Z n ω| ≤ 2 * τ} :=
  mixing_oracle_truth_survives_noisy_to μ Z predR a c n n τ δ η
    (mixingHoeffdingTo_of_mixingHoeffding n μ Z a c hmix) hc hmeas hn1 le_rfl hτ hδ0 hn hη hbudget
    hnoise

/-! ### FV-E → FV-J union-bound glue, mixing case: a finite schedule over one orbit segment

The finite-horizon composition ([SQ] §3.3; FV-M): `sq_oracle_uniform_tail`'s union bound applied to
a schedule of queries each satisfying `MixingHoeffdingTo` at one shared constant `c`, giving FV-J's
oracle object off an event of measure `≤ δ` at a single sample size `n ≤ N` — the mixing,
finite-horizon twin of `SQOracle.empirical_isSQOracle_of_iid`, which is its `c = 1`, `N = n` case. -/

/-- **Finite-horizon mixing oracle over a schedule** ([SQ] §3.3; FV-M). A schedule of queries `Qs`,
each representative below the horizon `N` at one shared mixing constant `c`
(`MixingHoeffdingTo N μ (Z φ) (tru φ) c` for every `φ ∈ Qs`), gives FV-J's genuine oracle object
`SQObjects.IsSQOracle` off an event of measure `≤ δ`, at `n ≤ N` single-orbit steps of one orbit
segment — the schedule entering only as `log |Qs|` in the sample size, exactly as
`empirical_isSQOracle_of_iid` does at `c = 1`. Composes `mixing_oracle_tail_to`'s per-query bound at
`δ' := δ/|Qs|` with `sq_oracle_uniform_tail`'s union bound. -/
theorem empirical_isSQOracle_of_mixingTo
    (μ : Measure (ℕ → X)) [IsProbabilityMeasure μ]
    {Q : Type*} (Qs : Finset Q) (hQs : Qs.Nonempty)
    (Z : Q → ℕ → (ℕ → X) → ℝ) (tru : Q → ℝ) (c : ℝ) (N n : ℕ) (τ δ : ℝ)
    (hmix : ∀ φ ∈ Qs, MixingHoeffdingTo N μ (Z φ) (tru φ) c) (hc : 0 < c)
    (hn1 : 1 ≤ n) (hnN : n ≤ N) (hτ : 0 < τ) (hδ0 : 0 < δ)
    (hn : (2 * c / τ ^ 2) * Real.log (2 * (Qs.card : ℝ) / δ) ≤ (n : ℝ)) :
    μ ({ω | SQObjects.IsSQOracle (fun φ : ↥Qs => empiricalMean (Z ↑φ) n ω)
        (fun φ : ↥Qs => tru ↑φ) τ}ᶜ) ≤ ENNReal.ofReal δ := by
  have hMpos : (0 : ℝ) < (Qs.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hQs
  set δ' : ℝ := δ / (Qs.card : ℝ) with hδ'def
  have hδ'0 : 0 < δ' := by positivity
  -- `n ≥ (2c/τ²)·log(2|Qs|/δ)` is exactly `n ≥ (2c/τ²)·log(2/δ')` after `2/δ' = 2|Qs|/δ`.
  have hn' : (2 * c / τ ^ 2) * Real.log (2 / δ') ≤ (n : ℝ) := by
    have heq : (2 : ℝ) / δ' = 2 * (Qs.card : ℝ) / δ := by rw [hδ'def]; field_simp
    rwa [heq]
  have htail : ∀ φ ∈ Qs, μ {ω | τ < |empiricalMean (Z φ) n ω - tru φ|} ≤ ENNReal.ofReal δ' :=
    fun φ hφ =>
      mixing_oracle_tail_to μ (Z φ) (tru φ) c N n τ δ' (hmix φ hφ) hc hn1 hnN hτ hδ'0 hn'
  have hstep := empirical_isSQOracle Qs (fun φ => empiricalMean (Z φ) n) tru τ δ' htail
  refine hstep.trans (le_of_eq ?_)
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
  congr 1
  rw [hδ'def]
  field_simp

end BirkhoffTool

/-! ## Axiom audit

`not_mixingHoeffding_of_periodic_ne` is `#print axioms`-clean on the standard triple, and the guard
below makes that build-enforced. -/

/-- info: 'BirkhoffTool.not_mixingHoeffding_of_periodic_ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms BirkhoffTool.not_mixingHoeffding_of_periodic_ne

/-- info: 'BirkhoffTool.mixingHoeffding_of_deviation_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms BirkhoffTool.mixingHoeffding_of_deviation_bound

/-- info: 'BirkhoffTool.mixingHoeffding_dirac_of_deviation_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms BirkhoffTool.mixingHoeffding_dirac_of_deviation_bound
