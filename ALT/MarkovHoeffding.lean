/-
Copyright (c) 2026 Mykola Palamarchuk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mykola Palamarchuk
-/
import ALT.BirkhoffTool
import Mathlib.Probability.Kernel.IonescuTulcea.Traj

set_option linter.style.header false
set_option linter.style.longLine false

/-!
# Markov Hoeffding: a finite-state spectral-gap route toward `BirkhoffTool.MixingHoeffding`

Provenance: the finite-state spectral-gap concentration inequality for Markov chains
(Gillman 1993; León and Perron 2004; Fan, Jiang and Sun, JMLR 22(139), 2021, Thm 1 — the FJS
shape `BirkhoffTool.MixingHoeffding` restates).  `BirkhoffTool.MixingHoeffding` is imported there
as a named hypothesis; this module DERIVES it from a spectral gap on a finite-state chain.

## What is proved here (machine-checked, axioms = the standard triple)

* `Stochastic`, `Stationary`, `GapContraction`, `IsChainMeasure` — the chain data: a stochastic
  matrix, its stationary law, the operator-norm spectral gap (reversibility-free, no eigenvalues
  named), and the trajectory law's cylinder pricing.
* **`mixingHoeffding_of_gap` — THE WORKHORSE TARGET.**  `BirkhoffTool.MixingHoeffding` derived from
  `GapContraction` at the explicit constant `cGap lam`, for every `lam ∈ [0, 1)`, guarded by
  `#print axioms`.  Built from a Cauchy-Schwarz/Young's-inequality transfer-operator induction
  (`transferIter_invariant`), instantiated at closed forms (`gapA`, `gapEps`, `gapTm`, `gapK`,
  `cGap`), a two-branch Chernoff optimisation (`chernoff_exponent_le`), an MGF bridge to
  `IsChainMeasure`'s path-sum pricing (`transferIter_mean_eq_iterMean`,
  `chainMeasure_cylinder_sum`), and two-sided symmetrisation.  See the module's closing section
  for the full route and the sharp-constant residue this round did not chase.
* `chainMeasure_cylinder_sum` — **the cylinder-to-path-sum reduction.** Any event on finitely many
  leading coordinates has `IsChainMeasure`-measure the sum, over the realising paths, of that
  path's chain probability: the finite-additivity bridge a spectral-gap argument needs before any
  probabilistic estimate can start.
* `witnessP`, `witnessPi`, `witness_gapContraction` — **the satisfiability witness.** A concrete
  lazy two-state walk discharging `Stochastic`, `Stationary`, positivity, and `GapContraction` at
  a genuine positive gap `lam = 1/2`, guarded by `#print axioms`.
* **`exists_chainMeasure` — TARGET B, THE EXISTENCE TARGET.**  Every `(P, pi)` satisfying
  `Stochastic P` and a genuine probability law has SOME `IsChainMeasure P pi μ`, guarded by
  `#print axioms`.  Built from Mathlib's Ionescu-Tulcea construction (`ProbabilityTheory.Kernel.
  traj`/`Kernel.trajMeasure`) instantiated at the constant type family and the finite-state kernel
  `stepKernel P`, with the cylinder-pricing induction (`chainMeasure_singleton`) bridging the
  construction's `Finset.Iic n`-indexed finite-dimensional laws to `IsChainMeasure`'s own
  `Fin (n + 1) → V` pricing via the reindexing equivalence `iicFinEquiv`.  See the module's closing
  section for the route.
* **`exists_mixingHoeffding_of_gap` — the fully unconditional package.**  `exists_chainMeasure`
  plus `mixingHoeffding_of_gap` in one theorem: every `Stochastic`/`GapContraction` pair at a
  genuine gap `lam ∈ [0, 1)` has an `IsChainMeasure` witness satisfying
  `BirkhoffTool.MixingHoeffding` at `cGap lam`, with no hypothesis left for a caller to discharge.
-/

namespace MarkovHoeffding

variable {V : Type*} [Fintype V] [Nonempty V] [MeasurableSpace V] [DiscreteMeasurableSpace V]

/-! ## Chain data: a stochastic matrix, its stationary law, and the operator-norm gap -/

/-- A stochastic (row-substochastic-nonneg, row-sum-one) transition matrix on a finite state
space. -/
def Stochastic (P : V → V → ℝ) : Prop := (∀ x y, 0 ≤ P x y) ∧ ∀ x, ∑ y, P x y = 1

/-- `pi` is a stationary law for `P`: `pi` is a LEFT fixed point of `P`, `pi * P = pi`. -/
def Stationary (P : V → V → ℝ) (pi : V → ℝ) : Prop := ∀ y, ∑ x, pi x * P x y = pi y

/-- **The spectral-gap hypothesis, operator-form.**  `P` contracts every `pi`-mean-zero function
by a factor `lam` in the `pi`-weighted `ℓ²` norm: no eigenvalues, no reversibility.  A reversible
chain with second-largest eigenvalue magnitude `lam`, or an expander's random-walk operator,
satisfies this; consumers may derive it from spectral data later. -/
def GapContraction (P : V → V → ℝ) (pi : V → ℝ) (lam : ℝ) : Prop :=
  ∀ g : V → ℝ, ∑ x, pi x * g x = 0 →
    ∑ x, pi x * (∑ y, P x y * g y) ^ 2 ≤ lam ^ 2 * ∑ x, pi x * g x ^ 2

/-- `μ` is the trajectory law of the Markov chain `(P, pi)`: every finite-horizon cylinder has
probability `pi(w 0) · ∏ P(w i, w (i+1))`. -/
def IsChainMeasure (P : V → V → ℝ) (pi : V → ℝ) (μ : MeasureTheory.Measure (ℕ → V)) : Prop :=
  ∀ (n : ℕ) (w : Fin (n + 1) → V),
    μ.real {ω | ∀ i : Fin (n + 1), ω (i : ℕ) = w i} =
      pi (w 0) * ∏ i : Fin n, P (w i.castSucc) (w i.succ)

/-! ## Structural facts shared by every target below -/

omit [Nonempty V] [MeasurableSpace V] [DiscreteMeasurableSpace V] in
/-- **Stationarity, dual form.** For ANY function `h`, `pi`-averaging `P h` gives back the
`pi`-average of `h` itself: `Stationary` is exactly the statement that `pi` is a left fixed
point, restated as duality with the (right) action of `P` on functions. -/
private theorem stationary_dual {P : V → V → ℝ} {pi : V → ℝ} (hst : Stationary P pi) (h : V → ℝ) :
    ∑ x, pi x * (∑ y, P x y * h y) = ∑ x, pi x * h x := by
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => ?_
  simp_rw [show ∀ x : V, pi x * (P x y * h y) = (pi x * P x y) * h y from fun x => by ring]
  rw [← Finset.sum_mul, hst y]

omit [Nonempty V] [MeasurableSpace V] [DiscreteMeasurableSpace V] in
/-- `P` maps a `pi`-mean-zero function to a `pi`-mean-zero function: the mean-zero subspace
`GapContraction` acts on is genuinely `P`-invariant. -/
private theorem mean_zero_of_Pmap {P : V → V → ℝ} {pi : V → ℝ} (hst : Stationary P pi)
    {g : V → ℝ} (hg : ∑ x, pi x * g x = 0) :
    ∑ x, pi x * (∑ y, P x y * g y) = 0 := by
  rw [stationary_dual hst g, hg]

/-! ## The cylinder-to-path-sum reduction

The workhorse target's deviation event at horizon `n` depends only on the coordinates below `n`,
so it is a finite union of the horizon-`n` cylinders `IsChainMeasure` prices directly. -/

omit [Fintype V] [Nonempty V] in
/-- **The cylinder-to-path-sum reduction.** Any FINITE-horizon event `S` on the first `m + 1`
coordinates has `μ`-measure the sum, over the paths `w` realising it, of that path's chain
probability — the bridge from `IsChainMeasure`'s per-path pricing to a probability of an event
depending on finitely many coordinates. -/
theorem chainMeasure_cylinder_sum {P : V → V → ℝ} {pi : V → ℝ}
    {μ : MeasureTheory.Measure (ℕ → V)} [MeasureTheory.IsProbabilityMeasure μ]
    (hμ : IsChainMeasure P pi μ) (m : ℕ) (S : Finset (Fin (m + 1) → V)) :
    μ.real {ω : ℕ → V | (fun i : Fin (m + 1) => ω (i : ℕ)) ∈ S} =
      ∑ w ∈ S, pi (w 0) * ∏ i : Fin m, P (w i.castSucc) (w i.succ) := by
  have hcyl : ∀ w : Fin (m + 1) → V,
      MeasurableSet {ω : ℕ → V | ∀ i : Fin (m + 1), ω (i : ℕ) = w i} := by
    intro w
    have : {ω : ℕ → V | ∀ i : Fin (m + 1), ω (i : ℕ) = w i}
        = ⋂ i : Fin (m + 1), (fun ω : ℕ → V => ω (i : ℕ)) ⁻¹' {w i} := by
      ext ω; simp
    rw [this]
    exact MeasurableSet.iInter fun i =>
      (measurable_pi_apply (i : ℕ)) MeasurableSet.of_discrete
  have hset : {ω : ℕ → V | (fun i : Fin (m + 1) => ω (i : ℕ)) ∈ S} =
      ⋃ w ∈ S, {ω : ℕ → V | ∀ i : Fin (m + 1), ω (i : ℕ) = w i} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
    constructor
    · intro h; exact ⟨_, h, fun _ => rfl⟩
    · rintro ⟨w, hw, hweq⟩
      rwa [show (fun i : Fin (m + 1) => ω (i : ℕ)) = w from funext hweq]
  rw [hset, MeasureTheory.measureReal_biUnion_finset]
  · exact Finset.sum_congr rfl fun w _ => hμ m w
  · intro w _ w' _ hne
    simp only [Function.onFun, Set.disjoint_left, Set.mem_ofPred_eq]
    intro ω hω hω'
    exact hne (funext fun i => (hω i).symm.trans (hω' i))
  · exact fun w _ => hcyl w

/-! ## Target C: a satisfiability witness

A concrete two-state chain discharging every hypothesis of the workhorse target's premises at a
genuine positive gap `lam = 1/2` (not the degenerate `lam ≤ 0` case, where `GapContraction` is
either vacuous or forces `P` itself to fix every mean-zero function).  The lazy walk on `Bool`:
stay with probability `3/4`, flip with probability `1/4`; uniform on `Bool` is stationary since
the chain is doubly stochastic. -/

/-- The lazy two-state walk: stay put with probability `3/4`, flip with probability `1/4`. -/
noncomputable def witnessP : Bool → Bool → ℝ := fun x y => if y = x then 3 / 4 else 1 / 4

/-- The uniform law on `Bool`. -/
noncomputable def witnessPi : Bool → ℝ := fun _ => 1 / 2

private theorem witnessP_stochastic : Stochastic witnessP := by
  refine ⟨fun x y => ?_, fun x => ?_⟩
  · unfold witnessP; split <;> norm_num
  · unfold witnessP; rw [Fintype.sum_bool]; fin_cases x <;> norm_num

private theorem witnessPi_pos : ∀ x : Bool, 0 < witnessPi x := fun _ => by unfold witnessPi; norm_num

private theorem witnessPi_sum : ∑ x : Bool, witnessPi x = 1 := by
  unfold witnessPi; rw [Fintype.sum_bool]; norm_num

private theorem witnessP_stationary : Stationary witnessP witnessPi := by
  intro y
  unfold witnessP witnessPi
  rw [Fintype.sum_bool]
  fin_cases y <;> norm_num

/-- **Target C.** The lazy two-state walk realises `GapContraction` at the genuine gap `1/2`. -/
theorem witness_gapContraction : GapContraction witnessP witnessPi (1 / 2) := by
  intro g hg
  simp only [witnessPi, witnessP, Fintype.sum_bool] at hg ⊢
  norm_num at hg ⊢
  nlinarith [hg, sq_nonneg (g true), sq_nonneg (g false)]

/-- info: 'MarkovHoeffding.witness_gapContraction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms witness_gapContraction

/-! ## Toward the workhorse: the transfer operator and its single-step exponential bound

`transferIter` is the Chernoff transfer iterate:
`h 0 := 1`, `h (k + 1) x := exp (t g x) · (P h k)(x)`.
`∑ x, pi x * h n x` is exactly `𝔼[exp (t * ∑_{i < n} g(X_i))]` for the chain started at `pi`
(`transferIter_mean_eq_iterMean` below makes this precise via `SQOracle.empiricalMean`-style sums).

The single-step bound `expBound_meanZero` is the fix over a coarser, linear elementary bound: for
mean-zero `g`, the FIRST-order term in `∑ π(x) exp(t g x)` cancels exactly (`hg0`), so the
deviation from `1` is second order in `t`, not first — this is what makes a genuine Chernoff rate
possible at all; the earlier (linear) bound was too lossy to ever recover a `t²`-shaped tail. -/

noncomputable def transferIter (P : V → V → ℝ) (t : ℝ) (g : V → ℝ) : ℕ → V → ℝ
  | 0 => fun _ => 1
  | (k + 1) => fun x => Real.exp (t * g x) * ∑ y, P x y * transferIter P t g k y

omit [Nonempty V] [MeasurableSpace V] [DiscreteMeasurableSpace V] in
/-- **The sharpened single-step exponential bound.** For `pi`-mean-zero `g` bounded by `2` and
`|t| ≤ 1/2`, `∑ x, pi x * exp (t * g x)` deviates from `1` by at most `4 * t ^ 2` — QUADRATIC in
`t`, because the mean-zero hypothesis kills the linear term in the Taylor expansion of `exp`
exactly (`Real.abs_exp_sub_one_sub_id_le`), leaving only the quadratic remainder. -/
private theorem expBound_meanZero {pi : V → ℝ} {g : V → ℝ} (hpinn : ∀ x, 0 ≤ pi x)
    (hg0 : ∑ x, pi x * g x = 0)
    (hgbd : ∀ x, g x ∈ Set.Icc (-2 : ℝ) 2) (hpisum : ∑ x, pi x = 1)
    {t : ℝ} (ht : |t| ≤ 1 / 2) :
    |(∑ x, pi x * Real.exp (t * g x)) - 1| ≤ 4 * t ^ 2 := by
  have hstep : ∀ x, |Real.exp (t * g x) - 1 - t * g x| ≤ (t * g x) ^ 2 := by
    intro x
    apply Real.abs_exp_sub_one_sub_id_le
    have hgx := hgbd x
    calc |t * g x| ≤ (1/2) * 2 := by
          rw [abs_mul]
          exact mul_le_mul ht (abs_le.mpr ⟨by linarith [hgx.1], hgx.2⟩) (abs_nonneg _) (by norm_num)
      _ = 1 := by norm_num
  have hrw : (∑ x, pi x * Real.exp (t * g x)) - 1
      = ∑ x, pi x * (Real.exp (t * g x) - 1 - t * g x) := by
    have expand : ∀ x, pi x * (Real.exp (t * g x) - 1 - t * g x)
        = pi x * Real.exp (t * g x) - pi x - t * (pi x * g x) := fun x => by ring
    simp_rw [expand]
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, hg0, hpisum]
    ring
  rw [hrw]
  calc |∑ x, pi x * (Real.exp (t * g x) - 1 - t * g x)|
      ≤ ∑ x, |pi x * (Real.exp (t * g x) - 1 - t * g x)| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ x, pi x * |Real.exp (t * g x) - 1 - t * g x| := by
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [abs_mul, abs_of_nonneg (hpinn x)]
    _ ≤ ∑ x, pi x * (t * g x) ^ 2 :=
        Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (hstep x) (hpinn x)
    _ ≤ ∑ x, pi x * (4 * t ^ 2) := by
        refine Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left ?_ (hpinn x)
        have hgx := hgbd x
        have hgsq : g x ^ 2 ≤ 4 := by nlinarith [hgx.1, hgx.2]
        nlinarith [sq_nonneg t, hgsq]
    _ = 4 * t ^ 2 := by rw [← Finset.sum_mul, hpisum]; ring

omit [Nonempty V] [MeasurableSpace V] [DiscreteMeasurableSpace V] in
/-- **The Cauchy-Schwarz cross-term bound.** For `pi`-mean-zero `r`, the `pi`-weighted inner
product of any `w` against `P r` is controlled by `GapContraction`'s gap `lam`, via
Cauchy-Schwarz (`Finset.sum_mul_sq_le_sq_mul_sq`) applied to the pair
`(√(pi ·) · w ·, √(pi ·) · (P r) ·)`. This is `Cov_n(t)`'s bound in the route above, with
`w := fun x => Real.exp (t * g x) - 1` at the call site. -/
private theorem crossTerm_bound {P : V → V → ℝ} {pi : V → ℝ} {lam : ℝ} (hlam0 : 0 ≤ lam)
    (hpinn : ∀ x, 0 ≤ pi x) (hgap : GapContraction P pi lam)
    {r : V → ℝ} (hr0 : ∑ x, pi x * r x = 0) (w : V → ℝ) :
    |∑ x, pi x * w x * (∑ y, P x y * r y)| ≤
      Real.sqrt (∑ x, pi x * w x ^ 2) * (lam * Real.sqrt (∑ x, pi x * r x ^ 2)) := by
  set f : V → ℝ := fun x => Real.sqrt (pi x) * w x with hf
  set g' : V → ℝ := fun x => Real.sqrt (pi x) * (∑ y, P x y * r y) with hg'
  have hfg : ∀ x, f x * g' x = pi x * w x * (∑ y, P x y * r y) := by
    intro x
    simp only [hf, hg']
    rw [show Real.sqrt (pi x) * w x * (Real.sqrt (pi x) * (∑ y, P x y * r y))
        = (Real.sqrt (pi x) * Real.sqrt (pi x)) * (w x * (∑ y, P x y * r y)) from by ring,
      Real.mul_self_sqrt (hpinn x)]
    ring
  have hf2 : ∀ x, f x ^ 2 = pi x * w x ^ 2 := by
    intro x; simp only [hf, mul_pow, Real.sq_sqrt (hpinn x)]
  have hg2 : ∀ x, g' x ^ 2 = pi x * (∑ y, P x y * r y) ^ 2 := by
    intro x; simp only [hg', mul_pow, Real.sq_sqrt (hpinn x)]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ f g'
  simp only [hfg, hf2, hg2] at hcs
  have hgapbd : ∑ x, pi x * (∑ y, P x y * r y) ^ 2 ≤ lam ^ 2 * ∑ x, pi x * r x ^ 2 := hgap r hr0
  have hsq : (∑ x, pi x * w x * (∑ y, P x y * r y)) ^ 2 ≤
      (∑ x, pi x * w x ^ 2) * (lam ^ 2 * ∑ x, pi x * r x ^ 2) :=
    hcs.trans (mul_le_mul_of_nonneg_left hgapbd
      (Finset.sum_nonneg fun x _ => mul_nonneg (hpinn x) (sq_nonneg _)))
  have hrhs_nonneg :
      0 ≤ Real.sqrt (∑ x, pi x * w x ^ 2) * (lam * Real.sqrt (∑ x, pi x * r x ^ 2)) :=
    mul_nonneg (Real.sqrt_nonneg _) (mul_nonneg hlam0 (Real.sqrt_nonneg _))
  refine abs_le_of_sq_le_sq ?_ hrhs_nonneg
  have hw2nn : (0:ℝ) ≤ ∑ x, pi x * w x ^ 2 :=
    Finset.sum_nonneg fun x _ => mul_nonneg (hpinn x) (sq_nonneg _)
  have hr2nn : (0:ℝ) ≤ ∑ x, pi x * r x ^ 2 :=
    Finset.sum_nonneg fun x _ => mul_nonneg (hpinn x) (sq_nonneg _)
  calc (∑ x, pi x * w x * (∑ y, P x y * r y)) ^ 2
      ≤ (∑ x, pi x * w x ^ 2) * (lam ^ 2 * ∑ x, pi x * r x ^ 2) := hsq
    _ = (Real.sqrt (∑ x, pi x * w x ^ 2) * (lam * Real.sqrt (∑ x, pi x * r x ^ 2))) ^ 2 := by
        rw [mul_pow, mul_pow, Real.sq_sqrt hw2nn, Real.sq_sqrt hr2nn]

omit [Fintype V] [Nonempty V] [MeasurableSpace V] [DiscreteMeasurableSpace V] in
/-- **The pointwise `F`-term envelope.** For `g` bounded by `2` and `|t| ≤ 1 / 4`,
`Real.exp (2 * t * g x)` is pointwise at most `1 + 8 * |t|` — the elementary bound
(`Real.abs_exp_sub_one_le`) applied at the doubled argument, feeding the `F`-term in the route
above (`∑ x, pi x * Real.exp (2 * t * g x) * ρ x ^ 2 ≤ (1 + 8 * |t|) * ∑ x, pi x * ρ x ^ 2`,
the crude but sufficient companion to `crossTerm_bound`'s sharper Cauchy-Schwarz route). -/
private theorem expBound_sup {g : V → ℝ} (hgbd : ∀ x, g x ∈ Set.Icc (-2 : ℝ) 2)
    {t : ℝ} (ht : |t| ≤ 1 / 4) (x : V) :
    Real.exp (2 * t * g x) ≤ 1 + 8 * |t| := by
  have hgx := hgbd x
  have habs : |2 * t * g x| ≤ 1 := by
    have h1 : |2 * t * g x| = 2 * |t| * |g x| := by
      rw [abs_mul, abs_mul]; norm_num
    rw [h1]
    have h2 : |g x| ≤ 2 := abs_le.mpr ⟨by linarith [hgx.1], hgx.2⟩
    calc 2 * |t| * |g x| ≤ 2 * |t| * 2 := by
          apply mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = 4 * |t| := by ring
      _ ≤ 4 * (1/4) := by linarith [ht]
      _ = 1 := by norm_num
  have hb := Real.abs_exp_sub_one_le habs
  have heq : |2 * t * g x| = 2 * |t| * |g x| := by rw [abs_mul, abs_mul]; norm_num
  have hgx2 : |g x| ≤ 2 := abs_le.mpr ⟨by linarith [hgx.1], hgx.2⟩
  have : Real.exp (2 * t * g x) - 1 ≤ 2 * |2 * t * g x| := (abs_le.mp hb).2
  rw [heq] at this
  nlinarith [this, hgx2, abs_nonneg t]

omit [Fintype V] [Nonempty V] [MeasurableSpace V] [DiscreteMeasurableSpace V] in
/-- **The pointwise squared-deviation envelope.** For `g` bounded by `2` and `|t| ≤ 1 / 2`,
`(Real.exp (t * g x) - 1) ^ 2 ≤ 16 * t ^ 2` pointwise — the `pi`-weighted variance bound
`Var_π (exp (t · g)) ≤ ∑ x, pi x * (exp (t * g x) - 1) ^ 2` (variance is at most the second
moment about ANY constant, here `1`) collapses to this SAME numeral after weighted averaging,
since the bound does not depend on `x`. Feeds the route's `m ^ 2 · Var_π(exp(t·g))` term. -/
private theorem expBound_sq {g : V → ℝ} (hgbd : ∀ x, g x ∈ Set.Icc (-2 : ℝ) 2)
    {t : ℝ} (ht : |t| ≤ 1 / 2) (x : V) :
    (Real.exp (t * g x) - 1) ^ 2 ≤ 16 * t ^ 2 := by
  have hgx := hgbd x
  have hgx2 : |g x| ≤ 2 := abs_le.mpr ⟨by linarith [hgx.1], hgx.2⟩
  have habs : |t * g x| ≤ 1 := by
    rw [abs_mul]
    calc |t| * |g x| ≤ (1/2) * 2 := mul_le_mul ht hgx2 (abs_nonneg _) (by norm_num)
      _ = 1 := by norm_num
  have hb := Real.abs_exp_sub_one_le habs
  have hsq : (Real.exp (t * g x) - 1) ^ 2 ≤ (2 * |t * g x|) ^ 2 :=
    sq_le_sq' (by linarith [abs_le.mp hb, neg_abs_le (Real.exp (t * g x) - 1)])
      (le_of_abs_le hb)
  have htgx2 : |t * g x| ^ 2 = t ^ 2 * g x ^ 2 := by
    rw [sq_abs]; ring
  have hgx4 : g x ^ 2 ≤ 4 := by nlinarith [hgx.1, hgx.2]
  nlinarith [hsq, htgx2, hgx4, sq_nonneg t]

/-- The `pi`-weighted mean of a function; `∑ x, pi x * h n x` for `h n := transferIter P t g n`
is `𝔼[exp (t * ∑_{i < n} g(X_i))]`. -/
noncomputable def iterMean (pi h : V → ℝ) : ℝ := ∑ x, pi x * h x

/-- The `pi`-weighted second moment of `h` about its own `iterMean` — `R` in the route above. -/
noncomputable def iterVar (pi h : V → ℝ) : ℝ := ∑ x, pi x * (h x - iterMean pi h) ^ 2

omit [Nonempty V] [MeasurableSpace V] [DiscreteMeasurableSpace V] in
/-- **Variance is at most the second moment about ANY point.** The `pi`-weighted second moment
of `Y` about its own mean never exceeds its second moment about an arbitrary `c`; the gap is
exactly `(mean - c) ^ 2`. Feeds both variance bounds in the route above (`c = 1` for
`Var_π(exp(t·g))`, `c = 0` for `Var_π(exp(t·g)·ρ)`). -/
private theorem var_le_secondMoment {pi : V → ℝ} (hpisum : ∑ x, pi x = 1) (Y : V → ℝ) (c : ℝ) :
    ∑ x, pi x * (Y x - ∑ x, pi x * Y x) ^ 2 ≤ ∑ x, pi x * (Y x - c) ^ 2 := by
  set μ : ℝ := ∑ x, pi x * Y x with hμ_def
  have hinner : ∑ x, pi x * (2 * Y x - c - μ) = μ - c := by
    have hrhs : 2 * (∑ x, pi x * Y x) - c * (∑ x, pi x) - μ * (∑ x, pi x)
        = ∑ x, pi x * (2 * Y x - c - μ) := by
      rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
        ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun x _ => by ring
    rw [← hrhs, ← hμ_def, hpisum]; ring
  have key : ∑ x, pi x * (Y x - c) ^ 2
      = (∑ x, pi x * (Y x - μ) ^ 2) + (μ - c) ^ 2 := by
    have expand : ∀ x, pi x * (Y x - c) ^ 2
        = pi x * (Y x - μ) ^ 2 + pi x * (2 * Y x - c - μ) * (μ - c) := by
      intro x; ring
    simp_rw [expand]
    rw [Finset.sum_add_distrib, ← Finset.sum_mul, hinner]
    ring
  linarith [key, sq_nonneg (μ - c)]

omit [Nonempty V] [MeasurableSpace V] [DiscreteMeasurableSpace V] in
/-- **The core invariant, machine-checked.** Under `GapContraction` at gap `lam`, a mean-zero
bounded `g`, and a tilt `t` small enough that a fixed-point inequality `hFP` holds, the transfer
iterate's mean stays nonnegative and its second moment about the mean stays within `A * t ^ 2`
times the mean squared, at every horizon `n` — the Cauchy-Schwarz/Young's-inequality induction the
route above describes, abstracted over the constants `A`, `ε` it needs.  A CLOSED FORM for `A`,
`ε`, and a `t`-range on which `hFP` and `hL0` hold for every `lam < 1` is recorded (checked
numerically, not yet machine-verified as an instance of THIS lemma) in the module's closing
section; instantiating it here is the remaining step toward the workhorse target. -/
theorem transferIter_invariant
    {P : V → V → ℝ} {pi : V → ℝ} {lam : ℝ}
    (hP : Stochastic P) (hst : Stationary P pi) (hpinn : ∀ x, 0 ≤ pi x) (hpisum : ∑ x, pi x = 1)
    (hlam0 : 0 ≤ lam) (hgap : GapContraction P pi lam)
    {g : V → ℝ} (hg0 : ∑ x, pi x * g x = 0) (hgbd : ∀ x, g x ∈ Set.Icc (-2 : ℝ) 2)
    {t : ℝ} (ht0 : 0 ≤ t) (ht4 : t ≤ 1 / 4)
    {A ε : ℝ} (hA0 : 0 ≤ A) (hε0 : 0 < ε)
    (hFP : 16 * (1 + ε) + (1 + 1 / ε) * (1 + 8 * t) * lam ^ 2 * A
        ≤ A * (1 - 4 * t ^ 2 * (1 + lam * Real.sqrt A)) ^ 2)
    (hL0 : 0 ≤ 1 - 4 * t ^ 2 * (1 + lam * Real.sqrt A))
    (n : ℕ) :
    0 ≤ iterMean pi (transferIter P t g n) ∧
    iterVar pi (transferIter P t g n) ≤ A * t ^ 2 * (iterMean pi (transferIter P t g n)) ^ 2 := by
  induction n with
  | zero =>
    have hm0 : iterMean pi (transferIter P t g 0) = 1 := by
      unfold iterMean
      have : transferIter P t g 0 = fun _ => (1:ℝ) := rfl
      rw [this]
      simp only [mul_one]
      exact hpisum
    rw [hm0]
    refine ⟨by norm_num, ?_⟩
    have hv0 : iterVar pi (transferIter P t g 0) = 0 := by
      unfold iterVar
      rw [hm0]
      have heq : transferIter P t g 0 = fun _ => (1:ℝ) := rfl
      rw [heq]
      simp
    rw [hv0]; positivity
  | succ n ih =>
    obtain ⟨ihm, ihR⟩ := ih
    set h : V → ℝ := transferIter P t g n with hh_def
    set m : ℝ := iterMean pi h with hm_def
    set R : ℝ := iterVar pi h with hR_def
    set r : V → ℝ := fun x => h x - m with hr_def
    have hm_sum : m = ∑ x, pi x * h x := hm_def
    have hR_sum : R = ∑ x, pi x * r x ^ 2 := by
      rw [hR_def]; unfold iterVar; rw [← hm_def]
    -- `r` is `pi`-mean-zero.
    have hr0 : ∑ x, pi x * r x = 0 := by
      simp only [hr_def, mul_sub]
      rw [Finset.sum_sub_distrib, ← Finset.sum_mul, ← hm_sum, hpisum, one_mul, sub_self]
    -- `h = r + (const m)`, so `P h = m + P r` pointwise.
    have hPh : ∀ x, (∑ y, P x y * h y) = m + ∑ y, P x y * r y := by
      intro x
      have hsplit : ∀ y, P x y * h y = P x y * r y + P x y * m := by
        intro y; simp only [hr_def]; ring
      simp_rw [hsplit]
      rw [Finset.sum_add_distrib, ← Finset.sum_mul, (hP.2 x), one_mul]
      ring
    -- `ρ := P r` is `pi`-mean-zero and `GapContraction`-bounded.
    have hρ0 : ∑ x, pi x * (∑ y, P x y * r y) = 0 := mean_zero_of_Pmap hst hr0
    have hρbd : ∑ x, pi x * (∑ y, P x y * r y) ^ 2 ≤ lam ^ 2 * R := by
      rw [hR_sum]; exact hgap r hr0
    -- unfold `h (n + 1)` via `hPh`.
    have hnext : ∀ x,
        transferIter P t g (n + 1) x = Real.exp (t * g x) * (m + ∑ y, P x y * r y) := by
      intro x
      change Real.exp (t * g x) * (∑ y, P x y * transferIter P t g n y) = _
      rw [← hh_def, hPh x]
    -- the scalars driving the recursion
    set E : ℝ := ∑ x, pi x * Real.exp (t * g x) with hE_def
    set Cov : ℝ := ∑ x, pi x * (Real.exp (t * g x) - 1) * (∑ y, P x y * r y) with hCov_def
    have ht2 : |t| ≤ 1 / 2 := by rw [abs_of_nonneg ht0]; linarith
    have ht4' : |t| ≤ 1 / 4 := by rw [abs_of_nonneg ht0]; exact ht4
    have hEbd : |E - 1| ≤ 4 * t ^ 2 := expBound_meanZero hpinn hg0 hgbd hpisum ht2
    have hmnext : iterMean pi (transferIter P t g (n + 1)) = m * E + Cov := by
      unfold iterMean
      have step : ∀ x, pi x * transferIter P t g (n + 1) x
          = pi x * Real.exp (t * g x) * m + pi x * (Real.exp (t * g x) - 1) * (∑ y, P x y * r y)
            + pi x * (∑ y, P x y * r y) := by
        intro x; rw [hnext x]; ring
      simp_rw [step]
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.sum_mul, hρ0, add_zero, hE_def]
      ring
    -- bound `Cov` via Cauchy-Schwarz + `GapContraction`
    have hwbd : ∑ x, pi x * (Real.exp (t * g x) - 1) ^ 2 ≤ 16 * t ^ 2 := by
      calc ∑ x, pi x * (Real.exp (t * g x) - 1) ^ 2
          ≤ ∑ x, pi x * (16 * t ^ 2) := Finset.sum_le_sum fun x _ =>
              mul_le_mul_of_nonneg_left (expBound_sq hgbd ht2 x) (hpinn x)
        _ = 16 * t ^ 2 := by rw [← Finset.sum_mul, hpisum]; ring
    have hRnn : 0 ≤ R := hR_sum ▸ Finset.sum_nonneg fun x _ => mul_nonneg (hpinn x) (sq_nonneg _)
    have hCovbd : |Cov| ≤ 4 * t * (lam * Real.sqrt R) := by
      have hcs := crossTerm_bound hlam0 hpinn hgap hr0 (fun x => Real.exp (t * g x) - 1)
      rw [← hR_sum] at hcs
      have hsqrt_le : Real.sqrt (∑ x, pi x * (Real.exp (t * g x) - 1) ^ 2) ≤ 4 * t := by
        rw [show (4 : ℝ) * t = Real.sqrt ((4 * t) ^ 2) from (Real.sqrt_sq (by linarith)).symm]
        apply Real.sqrt_le_sqrt
        calc ∑ x, pi x * (Real.exp (t * g x) - 1) ^ 2 ≤ 16 * t ^ 2 := hwbd
          _ = (4 * t) ^ 2 := by ring
      calc |Cov| ≤ Real.sqrt (∑ x, pi x * (Real.exp (t * g x) - 1) ^ 2) * (lam * Real.sqrt R) := hcs
        _ ≤ 4 * t * (lam * Real.sqrt R) := by
            apply mul_le_mul_of_nonneg_right hsqrt_le
            exact mul_nonneg hlam0 (Real.sqrt_nonneg _)
    -- the `L`-lower bound on `m_{n+1}` and its nonnegativity
    set L : ℝ := 1 - 4 * t ^ 2 * (1 + lam * Real.sqrt A) with hL_def
    have hAsqrt_nn : 0 ≤ Real.sqrt A := Real.sqrt_nonneg _
    have hsqrtR_le : Real.sqrt R ≤ Real.sqrt A * t * m := by
      have heq : Real.sqrt (A * t ^ 2 * m ^ 2) = Real.sqrt A * t * m := by
        rw [mul_assoc, Real.sqrt_mul hA0, Real.sqrt_mul (sq_nonneg t), Real.sqrt_sq ht0,
          Real.sqrt_sq ihm, mul_assoc]
      rw [← heq]
      exact Real.sqrt_le_sqrt ihR
    have hmL : m * L ≤ m * E + Cov := by
      have h1 : m * (1 - 4 * t ^ 2) ≤ m * E := by
        have := (abs_le.mp hEbd).1
        nlinarith [ihm]
      have h2 : -(4 * t * (lam * Real.sqrt R)) ≤ Cov := (abs_le.mp hCovbd).1
      have h3 : -(4 * t * (lam * (Real.sqrt A * t * m))) ≤ -(4 * t * (lam * Real.sqrt R)) := by
        have hcoef : 0 ≤ 4 * t * lam :=
          mul_nonneg (mul_nonneg (by norm_num) ht0) hlam0
        have := mul_le_mul_of_nonneg_left hsqrtR_le hcoef
        linarith [this]
      have h4 : m * L = m * (1 - 4 * t ^ 2) - 4 * t * (lam * (Real.sqrt A * t * m)) := by
        rw [hL_def]; ring
      linarith [h1, h2, h3, h4.le, h4.ge]
    have hmnext_ge : m * L ≤ iterMean pi (transferIter P t g (n + 1)) := by rw [hmnext]; exact hmL
    have hmnext_nn : 0 ≤ iterMean pi (transferIter P t g (n + 1)) := by
      have : 0 ≤ m * L := mul_nonneg ihm hL0
      linarith [hmnext_ge, this]
    -- Young's inequality with the tunable parameter `ε`
    have young : ∀ a b : ℝ, (a + b) ^ 2 ≤ (1 + ε) * a ^ 2 + (1 + 1 / ε) * b ^ 2 := by
      intro a b
      have hkey : ε * (a + b) ^ 2 ≤ ε * ((1 + ε) * a ^ 2 + (1 + 1 / ε) * b ^ 2) := by
        have expand : ε * ((1 + ε) * a ^ 2 + (1 + 1 / ε) * b ^ 2)
            = ε * (1 + ε) * a ^ 2 + ε * b ^ 2 + b ^ 2 := by field_simp; ring
        rw [expand]
        nlinarith [sq_nonneg (ε * a - b), hε0]
      exact le_of_mul_le_mul_left hkey hε0
    -- `∑ π (exp(tg) - E)² ≤ ∑ π (exp(tg) - 1)²` (variance is at most 2nd moment about any point)
    have hvar_le : ∑ x, pi x * (Real.exp (t * g x) - E) ^ 2
        ≤ ∑ x, pi x * (Real.exp (t * g x) - 1) ^ 2 := by
      have := var_le_secondMoment hpisum (fun x => Real.exp (t * g x)) 1
      rwa [← hE_def] at this
    -- `Cov` is also the raw mean of `exp(tg) · ρ` (via `ρ`'s own mean-zero-ness)
    have hCov_eq : Cov = ∑ x, pi x * (Real.exp (t * g x) * (∑ y, P x y * r y)) := by
      have expand : ∀ x, pi x * (Real.exp (t * g x) * (∑ y, P x y * r y))
          = pi x * (Real.exp (t * g x) - 1) * (∑ y, P x y * r y) + pi x * (∑ y, P x y * r y) := by
        intro x; ring
      simp_rw [expand]
      rw [Finset.sum_add_distrib, hρ0, add_zero, hCov_def]
    -- `Var(exp(tg)·ρ) ≤ 𝔼[(exp(tg)·ρ)²]` (variance is at most the raw second moment)
    have hvar2_le : ∑ x, pi x * (Real.exp (t * g x) * (∑ y, P x y * r y) - Cov) ^ 2
        ≤ ∑ x, pi x * (Real.exp (t * g x) * (∑ y, P x y * r y)) ^ 2 := by
      have hv := var_le_secondMoment hpisum (fun x => Real.exp (t * g x) * (∑ y, P x y * r y)) 0
      simp only [sub_zero] at hv
      rwa [← hCov_eq] at hv
    -- the `F`-term: `∑ π (exp(tg)·ρ)² ≤ (1 + 8t) · lam² · R`
    have hFterm : ∑ x, pi x * (Real.exp (t * g x) * (∑ y, P x y * r y)) ^ 2
        ≤ (1 + 8 * t) * (lam ^ 2 * R) := by
      have hpt : ∀ x, pi x * (Real.exp (t * g x) * (∑ y, P x y * r y)) ^ 2
          ≤ pi x * ((1 + 8 * t) * (∑ y, P x y * r y) ^ 2) := by
        intro x
        have hexp2 : (Real.exp (t * g x) * (∑ y, P x y * r y)) ^ 2
            = Real.exp (2 * t * g x) * (∑ y, P x y * r y) ^ 2 := by
          rw [mul_pow, sq (Real.exp (t * g x)), ← Real.exp_add]
          ring_nf
        rw [hexp2]
        apply mul_le_mul_of_nonneg_left _ (hpinn x)
        apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
        have := expBound_sup hgbd ht4' x
        rwa [abs_of_nonneg ht0] at this
      calc ∑ x, pi x * (Real.exp (t * g x) * (∑ y, P x y * r y)) ^ 2
          ≤ ∑ x, pi x * ((1 + 8 * t) * (∑ y, P x y * r y) ^ 2) := Finset.sum_le_sum fun x _ => hpt x
        _ = (1 + 8 * t) * ∑ x, pi x * (∑ y, P x y * r y) ^ 2 := by
            rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun x _ => by ring
        _ ≤ (1 + 8 * t) * (lam ^ 2 * R) := by
            apply mul_le_mul_of_nonneg_left hρbd
            linarith [ht0]
    -- assemble the `R_{n+1}` bound via Young's inequality
    have hrnext_eq : ∀ x, transferIter P t g (n + 1) x - iterMean pi (transferIter P t g (n + 1))
        = m * (Real.exp (t * g x) - E) + (Real.exp (t * g x) * (∑ y, P x y * r y) - Cov) := by
      intro x; rw [hnext x, hmnext]; ring
    have hRnext_sum : iterVar pi (transferIter P t g (n + 1))
        ≤ (1 + ε) * (m ^ 2 * ∑ x, pi x * (Real.exp (t * g x) - E) ^ 2)
          + (1 + 1 / ε) * ∑ x, pi x * (Real.exp (t * g x) * (∑ y, P x y * r y) - Cov) ^ 2 := by
      unfold iterVar
      calc ∑ x, pi x * (transferIter P t g (n + 1) x
              - iterMean pi (transferIter P t g (n + 1))) ^ 2
          = ∑ x, pi x * (m * (Real.exp (t * g x) - E)
              + (Real.exp (t * g x) * (∑ y, P x y * r y) - Cov)) ^ 2 := by
            exact Finset.sum_congr rfl fun x _ => by rw [hrnext_eq x]
        _ ≤ ∑ x, pi x * ((1 + ε) * (m * (Real.exp (t * g x) - E)) ^ 2
              + (1 + 1 / ε) * (Real.exp (t * g x) * (∑ y, P x y * r y) - Cov) ^ 2) :=
            Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (young _ _) (hpinn x)
        _ = (1 + ε) * (m ^ 2 * ∑ x, pi x * (Real.exp (t * g x) - E) ^ 2)
              + (1 + 1 / ε) * ∑ x, pi x * (Real.exp (t * g x) * (∑ y, P x y * r y) - Cov) ^ 2 := by
            have expand2 : ∀ x, pi x * ((1 + ε) * (m * (Real.exp (t * g x) - E)) ^ 2
                + (1 + 1 / ε) * (Real.exp (t * g x) * (∑ y, P x y * r y) - Cov) ^ 2)
                = (1 + ε) * (m ^ 2 * (pi x * (Real.exp (t * g x) - E) ^ 2))
                  + (1 + 1 / ε) * (pi x * (Real.exp (t * g x) * (∑ y, P x y * r y) - Cov) ^ 2) := by
              intro x; ring
            simp_rw [expand2]
            rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
    have hRnext_le : iterVar pi (transferIter P t g (n + 1))
        ≤ t ^ 2 * m ^ 2 * (16 * (1 + ε) + (1 + 1 / ε) * (1 + 8 * t) * lam ^ 2 * A) := by
      have step1 : (1 + ε) * (m ^ 2 * ∑ x, pi x * (Real.exp (t * g x) - E) ^ 2)
          ≤ (1 + ε) * (m ^ 2 * (16 * t ^ 2)) := by
        apply mul_le_mul_of_nonneg_left _ (by linarith [hε0])
        exact mul_le_mul_of_nonneg_left (hvar_le.trans hwbd) (sq_nonneg m)
      have step2 : (1 + 1 / ε) * ∑ x, pi x * (Real.exp (t * g x) * (∑ y, P x y * r y) - Cov) ^ 2
          ≤ (1 + 1 / ε) * ((1 + 8 * t) * (lam ^ 2 * R)) := by
        apply mul_le_mul_of_nonneg_left (hvar2_le.trans hFterm)
        positivity
      have step3 : (1 + 1 / ε) * ((1 + 8 * t) * (lam ^ 2 * R))
          ≤ (1 + 1 / ε) * ((1 + 8 * t) * (lam ^ 2 * (A * t ^ 2 * m ^ 2))) := by
        have hε' : (0:ℝ) ≤ 1 + 1 / ε := by positivity
        have h8t : (0:ℝ) ≤ 1 + 8 * t := by linarith [ht0]
        have hlam2 : (0:ℝ) ≤ lam ^ 2 := sq_nonneg lam
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ihR hlam2) h8t) hε'
      have hcombine := hRnext_sum.trans (add_le_add step1 (step2.trans step3))
      calc iterVar pi (transferIter P t g (n + 1))
          ≤ (1 + ε) * (m ^ 2 * (16 * t ^ 2))
            + (1 + 1 / ε) * ((1 + 8 * t) * (lam ^ 2 * (A * t ^ 2 * m ^ 2))) := hcombine
        _ = t ^ 2 * m ^ 2 * (16 * (1 + ε) + (1 + 1 / ε) * (1 + 8 * t) * lam ^ 2 * A) := by ring
    have hmL_sq : (m * L) ^ 2 ≤ (iterMean pi (transferIter P t g (n + 1))) ^ 2 := by
      have h1 : (0:ℝ) ≤ m * L := mul_nonneg ihm hL0
      exact sq_le_sq' (by linarith [hmnext_nn]) hmnext_ge
    refine ⟨hmnext_nn, hRnext_le.trans ?_⟩
    calc t ^ 2 * m ^ 2 * (16 * (1 + ε) + (1 + 1 / ε) * (1 + 8 * t) * lam ^ 2 * A)
        ≤ t ^ 2 * m ^ 2 * (A * L ^ 2) := by
          apply mul_le_mul_of_nonneg_left hFP (by positivity)
      _ = A * t ^ 2 * (m * L) ^ 2 := by ring
      _ ≤ A * t ^ 2 * (iterMean pi (transferIter P t g (n + 1))) ^ 2 := by
          apply mul_le_mul_of_nonneg_left hmL_sq (by positivity)

/-- info: 'MarkovHoeffding.transferIter_invariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms transferIter_invariant

/-! ## Closed forms instantiating `transferIter_invariant`

`gapA` is chosen as a perfect square in `12 / (1 - lam ^ 2)` specifically so `Real.sqrt (gapA lam)`
is the RATIONAL `gapSqrtA lam`, not a further nested root — `transferIter_invariant`'s `hFP`/`hL0`
then reduce to polynomial inequalities in `lam` alone once `Real.sqrt (gapA lam)` is rewritten
away, which is what makes them tractable for `nlinarith`. -/

/-- The invariant's `A`, at a genuine square `(12 / (1 - lam ^ 2)) ^ 2`. -/
noncomputable def gapA (lam : ℝ) : ℝ := (12 / (1 - lam ^ 2)) ^ 2

/-- `Real.sqrt (gapA lam)`, computed in closed form (see `gapSqrtA_eq`). -/
noncomputable def gapSqrtA (lam : ℝ) : ℝ := 12 / (1 - lam ^ 2)

/-- The invariant's tunable Young's-inequality parameter `ε`. -/
private noncomputable def gapEps (lam : ℝ) : ℝ := 2 * lam ^ 2 / (1 - lam ^ 2)

/-- The `t`-range on which `hFP`/`hL0` are discharged; `transferIter_invariant` is used at
`t := min (τ / (2 * gapK lam)) (gapTm lam)` for the Chernoff optimum `τ / (2 * gapK lam)`. -/
noncomputable def gapTm (lam : ℝ) : ℝ := (1 - lam ^ 2) / 50

/-- The transfer-iterate growth rate: `iterMean pi (transferIter P t g n) ≤ Real.exp (n * t ^ 2 *
gapK lam)` for `0 ≤ t ≤ gapTm lam` (see `transferIter_invariant` and the Chernoff step). -/
noncomputable def gapK (lam : ℝ) : ℝ := 4 * (1 + lam * gapSqrtA lam)

/-- **The workhorse target's constant.** A safety factor of `4` over the value exactly tight at
`τ = 2`, `lam → 1` (see the module's closing section for the two-branch Chernoff derivation). -/
noncomputable def cGap (lam : ℝ) : ℝ := 4 * max (2 * gapK lam) (2 / (gapK lam * gapTm lam ^ 2))

omit [Fintype V] [Nonempty V] [MeasurableSpace V] [DiscreteMeasurableSpace V] in
/-- `Real.sqrt (gapA lam) = gapSqrtA lam`, for any `lam` with `1 - lam ^ 2 ≥ 0`
(`gapSqrtA lam ≥ 0` then, so `gapA lam`'s square root is exactly its positive root). -/
private theorem gapSqrtA_eq {lam : ℝ} (hlam : lam ^ 2 ≤ 1) : Real.sqrt (gapA lam) = gapSqrtA lam := by
  unfold gapA gapSqrtA
  rw [Real.sqrt_sq (div_nonneg (by norm_num) (by linarith))]

omit [Fintype V] [Nonempty V] [MeasurableSpace V] [DiscreteMeasurableSpace V] in
/-- **Monotonicity: `hFP`/`hL0` at the worst case `t = Tm` propagate to every `t ∈ [0, Tm]`.**
`hFP`'s left side is affine INCREASING in `t` and its right side `A * (1 - 4 t² c) ²` (`c := 1 +
lam * s ≥ 0`) is DECREASING on `[0, Tm]` once `1 - 4 Tm² c ≥ 0` (`hL0` at `Tm`), since the base
`1 - 4 t² c` then stays in `[0, 1]` throughout and is itself decreasing. -/
private theorem hFP_hL0_of_le_Tm {lam A ε Tm t s : ℝ} (hA0 : 0 ≤ A) (hε0 : 0 < ε) (hlam0 : 0 ≤ lam)
    (hs0 : 0 ≤ s) (ht0 : 0 ≤ t) (htTm : t ≤ Tm)
    (hFPTm : 16 * (1 + ε) + (1 + 1 / ε) * (1 + 8 * Tm) * lam ^ 2 * A
        ≤ A * (1 - 4 * Tm ^ 2 * (1 + lam * s)) ^ 2)
    (hL0Tm : 0 ≤ 1 - 4 * Tm ^ 2 * (1 + lam * s)) :
    (16 * (1 + ε) + (1 + 1 / ε) * (1 + 8 * t) * lam ^ 2 * A
        ≤ A * (1 - 4 * t ^ 2 * (1 + lam * s)) ^ 2) ∧
    (0 ≤ 1 - 4 * t ^ 2 * (1 + lam * s)) := by
  have hTm0 : 0 ≤ Tm := le_trans ht0 htTm
  have hc0 : 0 ≤ 1 + lam * s := by positivity
  have ht2Tm2 : t ^ 2 ≤ Tm ^ 2 := by nlinarith [ht0, htTm]
  have hL0t : 0 ≤ 1 - 4 * t ^ 2 * (1 + lam * s) := by nlinarith [ht2Tm2, hc0, hL0Tm]
  refine ⟨?_, hL0t⟩
  have hLHSmono : 16 * (1 + ε) + (1 + 1 / ε) * (1 + 8 * t) * lam ^ 2 * A
      ≤ 16 * (1 + ε) + (1 + 1 / ε) * (1 + 8 * Tm) * lam ^ 2 * A := by
    have hcoef : (0:ℝ) ≤ (1 + 1 / ε) * lam ^ 2 * A := by positivity
    nlinarith [mul_le_mul_of_nonneg_left htTm hcoef]
  have hRHSmono : A * (1 - 4 * Tm ^ 2 * (1 + lam * s)) ^ 2
      ≤ A * (1 - 4 * t ^ 2 * (1 + lam * s)) ^ 2 := by
    have hbase : 1 - 4 * Tm ^ 2 * (1 + lam * s) ≤ 1 - 4 * t ^ 2 * (1 + lam * s) := by
      nlinarith [ht2Tm2, hc0]
    have hsq : (1 - 4 * Tm ^ 2 * (1 + lam * s)) ^ 2 ≤ (1 - 4 * t ^ 2 * (1 + lam * s)) ^ 2 :=
      sq_le_sq' (by linarith [hL0Tm, hL0t]) hbase
    exact mul_le_mul_of_nonneg_left hsq hA0
  linarith [hLHSmono, hRHSmono, hFPTm]

omit [Fintype V] [Nonempty V] [MeasurableSpace V] [DiscreteMeasurableSpace V] in
/-- `hL0` at the closed forms, at the worst case `t = gapTm lam`. -/
private theorem gapL0_at_Tm {lam : ℝ} (hlam0 : 0 ≤ lam) (hlam1 : lam < 1) :
    0 ≤ 1 - 4 * gapTm lam ^ 2 * (1 + lam * gapSqrtA lam) := by
  have hu : 0 < 1 - lam ^ 2 := by nlinarith
  unfold gapTm gapSqrtA
  have key : 1 - 4 * ((1 - lam ^ 2) / 50) ^ 2 * (1 + lam * (12 / (1 - lam ^ 2)))
      = 1 - (1 - lam ^ 2) * (1 - lam ^ 2 + 12 * lam) / 625 := by
    field_simp
    ring
  rw [key, le_sub_iff_add_le, zero_add, div_le_one (by norm_num : (0:ℝ) < 625)]
  nlinarith [sq_nonneg lam, sq_nonneg (lam - 1), hlam0, hlam1, hu]

omit [Fintype V] [Nonempty V] [MeasurableSpace V] [DiscreteMeasurableSpace V] in
/-- `hFP` at the closed forms, at the worst case `t = gapTm lam`. -/
private theorem gapFP_at_Tm {lam : ℝ} (hlam0 : 0 < lam) (hlam1 : lam < 1) :
    16 * (1 + gapEps lam) + (1 + 1 / gapEps lam) * (1 + 8 * gapTm lam) * lam ^ 2 * gapA lam
      ≤ gapA lam * (1 - 4 * gapTm lam ^ 2 * (1 + lam * gapSqrtA lam)) ^ 2 := by
  have hu : 0 < 1 - lam ^ 2 := by nlinarith
  have hune : (1 - lam ^ 2) ≠ 0 := ne_of_gt hu
  have hlamne : lam ≠ 0 := ne_of_gt hlam0
  unfold gapEps gapTm gapA gapSqrtA
  have hLHS_eq : 16 * (1 + 2 * lam ^ 2 / (1 - lam ^ 2))
      + (1 + 1 / (2 * lam ^ 2 / (1 - lam ^ 2))) * (1 + 8 * ((1 - lam ^ 2) / 50)) * lam ^ 2
        * (12 / (1 - lam ^ 2)) ^ 2
      = (1 + lam ^ 2) * (688 * (1 - lam ^ 2) + 1800) / (25 * (1 - lam ^ 2) ^ 2) := by
    field_simp
    ring
  have hRHS_eq : (12 / (1 - lam ^ 2)) ^ 2
      * (1 - 4 * ((1 - lam ^ 2) / 50) ^ 2 * (1 + lam * (12 / (1 - lam ^ 2)))) ^ 2
      = (144 * (625 - (1 - lam ^ 2) ^ 2 - 12 * lam * (1 - lam ^ 2)) ^ 2 / 15625)
        / (25 * (1 - lam ^ 2) ^ 2) := by
    field_simp
    ring
  rw [hLHS_eq, hRHS_eq, div_le_div_iff_of_pos_right (by positivity), le_div_iff₀ (by norm_num)]
  nlinarith [sq_nonneg lam, sq_nonneg (1 - lam), sq_nonneg (1 + lam), sq_nonneg (lam - 1 / 2),
    sq_nonneg ((1 - lam ^ 2) - 1), mul_pos hlam0 hu, hlam0, hlam1, hu,
    sq_nonneg (625 - (1 - lam ^ 2) ^ 2 - 12 * lam * (1 - lam ^ 2)),
    mul_nonneg hlam0.le hu.le, sq_nonneg (lam ^ 2), sq_nonneg (lam ^ 3), sq_nonneg (lam * (1 - lam))]

omit [Fintype V] [Nonempty V] [MeasurableSpace V] [DiscreteMeasurableSpace V] in
/-- **`hFP`/`hL0` at the closed forms, for every `lam ∈ [0, 1)`.** `lam = 0` needs its own witness
`ε := 1` (`gapEps 0 = 0` is not itself a valid Young's parameter): `GapContraction` at `0` makes
the `lam ^ 2`-weighted terms in `hFP` vanish identically regardless of `ε`, so ANY positive `ε`
discharges it there. -/
private theorem gap_exists_FP_hL0 {lam : ℝ} (hlam0 : 0 ≤ lam) (hlam1 : lam < 1) :
    ∃ ε : ℝ, 0 < ε ∧
      16 * (1 + ε) + (1 + 1 / ε) * (1 + 8 * gapTm lam) * lam ^ 2 * gapA lam
        ≤ gapA lam * (1 - 4 * gapTm lam ^ 2 * (1 + lam * gapSqrtA lam)) ^ 2 := by
  rcases eq_or_lt_of_le hlam0 with h0 | h0
  · refine ⟨1, by norm_num, ?_⟩
    rw [← h0]
    unfold gapA gapTm gapSqrtA
    norm_num
  · refine ⟨gapEps lam, ?_, gapFP_at_Tm h0 hlam1⟩
    have hu : 0 < 1 - lam ^ 2 := by nlinarith
    unfold gapEps
    positivity

omit [Nonempty V] [MeasurableSpace V] [DiscreteMeasurableSpace V] in
/-- **The instantiated invariant.** `transferIter_invariant`, specialised to the closed forms
`gapA`, `gapTm`: for every `lam ∈ [0, 1)` and `t ∈ [0, gapTm lam]`, the transfer iterate's mean
stays nonnegative and its second moment about the mean stays within `gapA lam * t ^ 2` times the
mean squared. -/
private theorem transferIter_gapBound
    {P : V → V → ℝ} {pi : V → ℝ} {lam : ℝ}
    (hP : Stochastic P) (hst : Stationary P pi) (hpinn : ∀ x, 0 ≤ pi x) (hpisum : ∑ x, pi x = 1)
    (hlam0 : 0 ≤ lam) (hlam1 : lam < 1) (hgap : GapContraction P pi lam)
    {g : V → ℝ} (hg0 : ∑ x, pi x * g x = 0) (hgbd : ∀ x, g x ∈ Set.Icc (-2 : ℝ) 2)
    {t : ℝ} (ht0 : 0 ≤ t) (htTm : t ≤ gapTm lam) (n : ℕ) :
    0 ≤ iterMean pi (transferIter P t g n) ∧
    iterVar pi (transferIter P t g n) ≤ gapA lam * t ^ 2 * (iterMean pi (transferIter P t g n)) ^ 2 := by
  obtain ⟨ε, hε0, hFPTm⟩ := gap_exists_FP_hL0 hlam0 hlam1
  have hL0Tm := gapL0_at_Tm hlam0 hlam1
  have hu : 0 < 1 - lam ^ 2 := by nlinarith
  have hA0 : 0 ≤ gapA lam := by unfold gapA; positivity
  have hs0 : 0 ≤ gapSqrtA lam := by unfold gapSqrtA; positivity
  obtain ⟨hFPt, hL0t⟩ :=
    hFP_hL0_of_le_Tm hA0 hε0 hlam0 hs0 ht0 htTm hFPTm hL0Tm
  have ht4 : t ≤ 1 / 4 := by
    have hTm4 : gapTm lam ≤ 1 / 4 := by unfold gapTm; nlinarith [sq_nonneg lam]
    linarith [htTm, hTm4]
  rw [← gapSqrtA_eq (by nlinarith : lam ^ 2 ≤ 1)] at hFPt hL0t
  exact transferIter_invariant hP hst hpinn hpisum hlam0 hgap hg0 hgbd ht0 ht4 hA0 hε0 hFPt hL0t n

omit [Nonempty V] [MeasurableSpace V] [DiscreteMeasurableSpace V] in
/-- **The growth bound.** `iterMean pi (transferIter P t g n) ≤ (1 + t ^ 2 * gapK lam) ^ n`, at
every `lam ∈ [0, 1)` and `t ∈ [0, gapTm lam]` — the Chernoff step's `m_n ≤ μ ^ n` fact, with
`transferIter_gapBound`'s `R ≤ A t ^ 2 m ^ 2` supplying the residual bound at each step fresh
(so this induction, unlike `transferIter_invariant`'s, does not need to propagate it itself). -/
private theorem transferIter_mean_le
    {P : V → V → ℝ} {pi : V → ℝ} {lam : ℝ}
    (hP : Stochastic P) (hst : Stationary P pi) (hpinn : ∀ x, 0 ≤ pi x) (hpisum : ∑ x, pi x = 1)
    (hlam0 : 0 ≤ lam) (hlam1 : lam < 1) (hgap : GapContraction P pi lam)
    {g : V → ℝ} (hg0 : ∑ x, pi x * g x = 0) (hgbd : ∀ x, g x ∈ Set.Icc (-2 : ℝ) 2)
    {t : ℝ} (ht0 : 0 ≤ t) (htTm : t ≤ gapTm lam) (n : ℕ) :
    iterMean pi (transferIter P t g n) ≤ (1 + t ^ 2 * gapK lam) ^ n := by
  have hu : 0 < 1 - lam ^ 2 := by nlinarith
  have hs0 : 0 ≤ gapSqrtA lam := by unfold gapSqrtA; positivity
  have ht4 : t ≤ 1 / 4 := by
    have hTm4 : gapTm lam ≤ 1 / 4 := by unfold gapTm; nlinarith [sq_nonneg lam]
    linarith [htTm, hTm4]
  have ht2 : |t| ≤ 1 / 2 := by rw [abs_of_nonneg ht0]; linarith
  induction n with
  | zero =>
    have heq0 : iterMean pi (transferIter P t g 0) = 1 := by
      unfold iterMean
      have heq : transferIter P t g 0 = fun _ => (1:ℝ) := rfl
      rw [heq]; simp only [mul_one]; exact hpisum
    rw [heq0]; simp
  | succ n ih =>
    obtain ⟨ihm0, ihR⟩ :=
      transferIter_gapBound hP hst hpinn hpisum hlam0 hlam1 hgap hg0 hgbd ht0 htTm n
    set h : V → ℝ := transferIter P t g n with hh_def
    set m : ℝ := iterMean pi h with hm_def
    set R : ℝ := iterVar pi h with hR_def
    have hm_sum : m = ∑ x, pi x * h x := hm_def
    have hR_sum : R = ∑ x, pi x * (h x - m) ^ 2 := by rw [hR_def]; unfold iterVar; rw [← hm_def]
    have hr0 : ∑ x, pi x * (h x - m) = 0 := by
      simp only [mul_sub]
      rw [Finset.sum_sub_distrib, ← Finset.sum_mul, ← hm_sum, hpisum, one_mul, sub_self]
    have hPh : ∀ x, (∑ y, P x y * h y) = m + ∑ y, P x y * (h y - m) := by
      intro x
      have hsplit : ∀ y, P x y * h y = P x y * (h y - m) + P x y * m := fun y => by ring
      simp_rw [hsplit]
      rw [Finset.sum_add_distrib, ← Finset.sum_mul, hP.2 x, one_mul]
      ring
    have hnext : ∀ x, transferIter P t g (n + 1) x
        = Real.exp (t * g x) * (m + ∑ y, P x y * (h y - m)) := by
      intro x
      change Real.exp (t * g x) * (∑ y, P x y * transferIter P t g n y) = _
      rw [← hh_def, hPh x]
    set E : ℝ := ∑ x, pi x * Real.exp (t * g x) with hE_def
    have hρ0 : ∑ x, pi x * (∑ y, P x y * (h y - m)) = 0 := mean_zero_of_Pmap hst hr0
    have hEbd : |E - 1| ≤ 4 * t ^ 2 := expBound_meanZero hpinn hg0 hgbd hpisum ht2
    have hmnext : iterMean pi (transferIter P t g (n + 1)) = m * E
        + ∑ x, pi x * (Real.exp (t * g x) - 1) * (∑ y, P x y * (h y - m)) := by
      unfold iterMean
      have step : ∀ x, pi x * transferIter P t g (n + 1) x
          = pi x * Real.exp (t * g x) * m
            + pi x * (Real.exp (t * g x) - 1) * (∑ y, P x y * (h y - m))
            + pi x * (∑ y, P x y * (h y - m)) := by
        intro x; rw [hnext x]; ring
      simp_rw [step]
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.sum_mul, hρ0, add_zero, hE_def]
      ring
    have hRnn : 0 ≤ R := hR_sum ▸ Finset.sum_nonneg fun x _ => mul_nonneg (hpinn x) (sq_nonneg _)
    have hCovbd :
        |∑ x, pi x * (Real.exp (t * g x) - 1) * (∑ y, P x y * (h y - m))|
          ≤ 4 * t * (lam * Real.sqrt R) := by
      have hcs := crossTerm_bound hlam0 hpinn hgap hr0 (fun x => Real.exp (t * g x) - 1)
      rw [← hR_sum] at hcs
      have hwbd : ∑ x, pi x * (Real.exp (t * g x) - 1) ^ 2 ≤ 16 * t ^ 2 := by
        calc ∑ x, pi x * (Real.exp (t * g x) - 1) ^ 2
            ≤ ∑ x, pi x * (16 * t ^ 2) := Finset.sum_le_sum fun x _ =>
                mul_le_mul_of_nonneg_left (expBound_sq hgbd ht2 x) (hpinn x)
          _ = 16 * t ^ 2 := by rw [← Finset.sum_mul, hpisum]; ring
      have hsqrt_le : Real.sqrt (∑ x, pi x * (Real.exp (t * g x) - 1) ^ 2) ≤ 4 * t := by
        rw [show (4 : ℝ) * t = Real.sqrt ((4 * t) ^ 2) from (Real.sqrt_sq (by linarith)).symm]
        exact Real.sqrt_le_sqrt (by nlinarith [hwbd])
      calc |∑ x, pi x * (Real.exp (t * g x) - 1) * (∑ y, P x y * (h y - m))|
          ≤ Real.sqrt (∑ x, pi x * (Real.exp (t * g x) - 1) ^ 2) * (lam * Real.sqrt R) := hcs
        _ ≤ 4 * t * (lam * Real.sqrt R) := by
            exact mul_le_mul_of_nonneg_right hsqrt_le (mul_nonneg hlam0 (Real.sqrt_nonneg _))
    have hsqrtR_le : Real.sqrt R ≤ gapSqrtA lam * t * m := by
      have heq : Real.sqrt (gapA lam * t ^ 2 * m ^ 2) = gapSqrtA lam * t * m := by
        have hA0 : 0 ≤ gapA lam := by unfold gapA; positivity
        rw [mul_assoc, Real.sqrt_mul hA0, Real.sqrt_mul (sq_nonneg t), Real.sqrt_sq ht0,
          Real.sqrt_sq ihm0, mul_assoc, gapSqrtA_eq (by nlinarith : lam ^ 2 ≤ 1)]
      rw [← heq]
      exact Real.sqrt_le_sqrt ihR
    have hmstep : m * E + ∑ x, pi x * (Real.exp (t * g x) - 1) * (∑ y, P x y * (h y - m))
        ≤ m * (1 + t ^ 2 * gapK lam) := by
      have h1 : m * E ≤ m * (1 + 4 * t ^ 2) := by nlinarith [(abs_le.mp hEbd).2, ihm0]
      have h2 : ∑ x, pi x * (Real.exp (t * g x) - 1) * (∑ y, P x y * (h y - m))
          ≤ 4 * t * (lam * (gapSqrtA lam * t * m)) := by
        have hle := (abs_le.mp hCovbd).2
        have hcoef : 0 ≤ 4 * t * lam := mul_nonneg (mul_nonneg (by norm_num) ht0) hlam0
        have := mul_le_mul_of_nonneg_left hsqrtR_le hcoef
        nlinarith [hle, this]
      have hK : m * (1 + t ^ 2 * gapK lam)
          = m * (1 + 4 * t ^ 2) + 4 * t * (lam * (gapSqrtA lam * t * m)) := by
        unfold gapK; ring
      rw [hK]; linarith [h1, h2]
    calc iterMean pi (transferIter P t g (n + 1))
        = m * E + ∑ x, pi x * (Real.exp (t * g x) - 1) * (∑ y, P x y * (h y - m)) := hmnext
      _ ≤ m * (1 + t ^ 2 * gapK lam) := hmstep
      _ ≤ (1 + t ^ 2 * gapK lam) ^ n * (1 + t ^ 2 * gapK lam) := by
          apply mul_le_mul_of_nonneg_right ih
          have hK0 : 0 ≤ gapK lam := by unfold gapK; positivity
          positivity
      _ = (1 + t ^ 2 * gapK lam) ^ (n + 1) := by ring

omit [Nonempty V] [MeasurableSpace V] [DiscreteMeasurableSpace V] in
/-- Splitting a sum over ALL paths `Fin (m + 1) → V` off its first coordinate, via `Fin.cons`. -/
private theorem sum_fin_succ_eq_sum_cons {M : Type*} [AddCommMonoid M] (m : ℕ) (F : (Fin (m + 1) → V) → M) :
    ∑ w : Fin (m + 1) → V, F w = ∑ x : V, ∑ p : Fin m → V, F (Fin.cons x p) := by
  have h1 : ∑ p : V × (Fin m → V), F ((Fin.consEquiv (fun _ => V)) p)
      = ∑ w : Fin (m + 1) → V, F w :=
    Fintype.sum_equiv (Fin.consEquiv (fun _ => V)) _ F fun p => rfl
  rw [← h1, Fintype.sum_prod_type]
  rfl

omit [Nonempty V] [MeasurableSpace V] [DiscreteMeasurableSpace V] in
/-- **The MGF bridge, pointwise.** `transferIter P t g (k + 1) x` is exactly the path-sum, over
`k`-step continuations `q` from `x`, of the transition weight times `exp (t * (sum of g along the
whole path))` — the finite-horizon MGF conditioned on starting at `x`. -/
private theorem transferIter_eq_pathSum (P : V → V → ℝ) (hP : Stochastic P) (t : ℝ) (g : V → ℝ)
    (k : ℕ) (x : V) :
    transferIter P t g (k + 1) x = ∑ q : Fin k → V,
      (∏ i : Fin k, P ((Fin.cons x q : Fin (k + 1) → V) i.castSucc)
          ((Fin.cons x q : Fin (k + 1) → V) i.succ))
        * Real.exp (t * (g x + ∑ i : Fin k, g (q i))) := by
  induction k generalizing x with
  | zero => simp [transferIter, hP.2 x]
  | succ k ih =>
    have step : transferIter P t g (k + 2) x
        = Real.exp (t * g x) * ∑ y, P x y * transferIter P t g (k + 1) y := rfl
    rw [step]
    simp_rw [ih]
    rw [sum_fin_succ_eq_sum_cons k
      (fun q => (∏ i : Fin (k + 1), P ((Fin.cons x q : Fin (k + 2) → V) i.castSucc)
          ((Fin.cons x q : Fin (k + 2) → V) i.succ))
        * Real.exp (t * (g x + ∑ i : Fin (k + 1), g (q i))))]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    have hprod : ∏ i : Fin (k + 1), P ((Fin.cons x (Fin.cons y q) : Fin (k + 2) → V) i.castSucc)
        ((Fin.cons x (Fin.cons y q) : Fin (k + 2) → V) i.succ)
        = P x y * ∏ i : Fin k, P ((Fin.cons y q : Fin (k + 1) → V) i.castSucc)
            ((Fin.cons y q : Fin (k + 1) → V) i.succ) := by
      rw [Fin.prod_univ_succ]
      norm_num
    have hsum : ∑ i : Fin (k + 1), g ((Fin.cons y q : Fin (k + 1) → V) i)
        = g y + ∑ i : Fin k, g (q i) := by
      have heq : (fun i : Fin (k + 1) => g ((Fin.cons y q : Fin (k + 1) → V) i))
          = Fin.cons (g y) (fun i => g (q i)) := by
        funext i
        refine Fin.cases ?_ ?_ i
        · simp
        · intro j; simp
      calc ∑ i : Fin (k + 1), g ((Fin.cons y q : Fin (k + 1) → V) i)
          = ∑ i : Fin (k + 1), Fin.cons (g y) (fun j => g (q j)) i := by rw [heq]
        _ = g y + ∑ i : Fin k, g (q i) := Fin.sum_cons _ _
    rw [hprod, hsum,
      show t * (g x + (g y + ∑ i : Fin k, g (q i)))
          = t * g x + t * (g y + ∑ i : Fin k, g (q i)) from by ring,
      Real.exp_add]
    ring

omit [Nonempty V] [MeasurableSpace V] [DiscreteMeasurableSpace V] in
/-- **The MGF bridge.** `iterMean pi (transferIter P t g (m + 1))` is exactly the path-sum, over
ALL `Fin (m + 1) → V` paths, of `IsChainMeasure`'s own per-path pricing
(`pi (w 0) * ∏ P`-steps, `chainMeasure_cylinder_sum`'s shape) times `exp (t * ∑ g (w i))` — the
single-orbit MGF `𝔼_μ [exp (t * ∑_{i < m + 1} g (X_i))]`, restated over the finite path space. -/
private theorem transferIter_mean_eq_iterMean
    {P : V → V → ℝ} (hP : Stochastic P) {pi : V → ℝ} {t : ℝ} {g : V → ℝ} (m : ℕ) :
    iterMean pi (transferIter P t g (m + 1)) = ∑ w : Fin (m + 1) → V,
      pi (w 0) * (∏ i : Fin m, P (w i.castSucc) (w i.succ)) * Real.exp (t * ∑ i : Fin (m + 1), g (w i)) := by
  unfold iterMean
  simp_rw [transferIter_eq_pathSum P hP t g m]
  rw [sum_fin_succ_eq_sum_cons m
    (fun w => pi (w 0) * (∏ i : Fin m, P (w i.castSucc) (w i.succ))
      * Real.exp (t * ∑ i : Fin (m + 1), g (w i)))]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  have hsum : ∑ i : Fin (m + 1), g ((Fin.cons x q : Fin (m + 1) → V) i) = g x + ∑ i : Fin m, g (q i) := by
    have heq : (fun i : Fin (m + 1) => g ((Fin.cons x q : Fin (m + 1) → V) i))
        = Fin.cons (g x) (fun j => g (q j)) := by
      funext i
      refine Fin.cases ?_ ?_ i
      · simp
      · intro j; simp
    calc ∑ i : Fin (m + 1), g ((Fin.cons x q : Fin (m + 1) → V) i)
        = ∑ i : Fin (m + 1), Fin.cons (g x) (fun j => g (q j)) i := by rw [heq]
      _ = g x + ∑ i : Fin m, g (q i) := Fin.sum_cons _ _
  rw [hsum]
  simp only [Fin.cons_zero]
  ring

omit [Nonempty V] in
/-- **The one-sided exponential-Markov bound.** For the chain's own path measure, the tail event
`(m + 1) * τ ≤ ∑ g (X_i)` has probability at most `exp (-t * (m + 1) * τ + t ^ 2 * (m + 1) *
gapK lam)`, for ANY tilt `t ∈ [0, gapTm lam]` — Markov's inequality applied to
`exp (t * ∑ g (X_i))`, dominating the restricted path-sum by the full one
(`transferIter_mean_eq_iterMean`) and bounding that by `transferIter_mean_le`. -/
private theorem one_sided_exp_markov
    {P : V → V → ℝ} {pi : V → ℝ} {lam : ℝ}
    (hP : Stochastic P) (hst : Stationary P pi) (hpinn : ∀ x, 0 ≤ pi x) (hpisum : ∑ x, pi x = 1)
    (hlam0 : 0 ≤ lam) (hlam1 : lam < 1) (hgap : GapContraction P pi lam)
    {g : V → ℝ} (hg0 : ∑ x, pi x * g x = 0) (hgbd : ∀ x, g x ∈ Set.Icc (-2 : ℝ) 2)
    {μ : MeasureTheory.Measure (ℕ → V)} [MeasureTheory.IsProbabilityMeasure μ]
    (hμ : IsChainMeasure P pi μ)
    (m : ℕ) {t : ℝ} (ht0 : 0 ≤ t) (htTm : t ≤ gapTm lam) (τ : ℝ) :
    μ.real {ω : ℕ → V | ((m + 1 : ℕ) : ℝ) * τ ≤ ∑ i : Fin (m + 1), g (ω i)}
      ≤ Real.exp (-t * ((m + 1 : ℕ) : ℝ) * τ + t ^ 2 * ((m + 1 : ℕ) : ℝ) * gapK lam) := by
  classical
  set S : Finset (Fin (m + 1) → V) :=
    Finset.univ.filter (fun w => ((m + 1 : ℕ) : ℝ) * τ ≤ ∑ i, g (w i)) with hS_def
  have hset : {ω : ℕ → V | ((m + 1 : ℕ) : ℝ) * τ ≤ ∑ i : Fin (m + 1), g (ω i)}
      = {ω : ℕ → V | (fun i : Fin (m + 1) => ω (i : ℕ)) ∈ S} := by
    ext ω; simp [hS_def]
  rw [hset, chainMeasure_cylinder_sum hμ m S]
  have hdom : ∑ w ∈ S, pi (w 0) * ∏ i : Fin m, P (w i.castSucc) (w i.succ)
      ≤ Real.exp (-t * ((m + 1 : ℕ) : ℝ) * τ)
        * ∑ w : Fin (m + 1) → V, pi (w 0) * (∏ i : Fin m, P (w i.castSucc) (w i.succ))
          * Real.exp (t * ∑ i : Fin (m + 1), g (w i)) := by
    rw [Finset.mul_sum]
    have hnn : ∀ w : Fin (m + 1) → V, 0 ≤ pi (w 0) * ∏ i : Fin m, P (w i.castSucc) (w i.succ) := by
      intro w
      exact mul_nonneg (hpinn _) (Finset.prod_nonneg fun i _ => hP.1 _ _)
    have hterm : ∀ w ∈ S, pi (w 0) * ∏ i : Fin m, P (w i.castSucc) (w i.succ)
        ≤ Real.exp (-t * ((m + 1 : ℕ) : ℝ) * τ)
          * (pi (w 0) * (∏ i : Fin m, P (w i.castSucc) (w i.succ))
            * Real.exp (t * ∑ i : Fin (m + 1), g (w i))) := by
      intro w hw
      simp only [hS_def, Finset.mem_filter, Finset.mem_univ, true_and] at hw
      have hexp1 : (1:ℝ) ≤ Real.exp (-t * ((m + 1 : ℕ) : ℝ) * τ)
          * Real.exp (t * ∑ i : Fin (m + 1), g (w i)) := by
        rw [← Real.exp_add]
        have : (0:ℝ) ≤ -t * ((m + 1 : ℕ) : ℝ) * τ + t * ∑ i : Fin (m + 1), g (w i) := by
          nlinarith [mul_le_mul_of_nonneg_left hw ht0]
        linarith [Real.add_one_le_exp (-t * ((m + 1 : ℕ) : ℝ) * τ + t * ∑ i : Fin (m + 1), g (w i)), this]
      nlinarith [hnn w, hexp1]
    calc ∑ w ∈ S, pi (w 0) * ∏ i : Fin m, P (w i.castSucc) (w i.succ)
        ≤ ∑ w ∈ S, Real.exp (-t * ((m + 1 : ℕ) : ℝ) * τ)
            * (pi (w 0) * (∏ i : Fin m, P (w i.castSucc) (w i.succ))
              * Real.exp (t * ∑ i : Fin (m + 1), g (w i))) :=
          Finset.sum_le_sum hterm
      _ ≤ ∑ w : Fin (m + 1) → V, Real.exp (-t * ((m + 1 : ℕ) : ℝ) * τ)
            * (pi (w 0) * (∏ i : Fin m, P (w i.castSucc) (w i.succ))
              * Real.exp (t * ∑ i : Fin (m + 1), g (w i))) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          intro w _ _
          exact mul_nonneg (Real.exp_pos _).le
            (mul_nonneg (hnn w) (Real.exp_pos _).le)
  refine hdom.trans ?_
  rw [← transferIter_mean_eq_iterMean hP m]
  have hgrowth := transferIter_mean_le hP hst hpinn hpisum hlam0 hlam1 hgap hg0 hgbd ht0 htTm (m + 1)
  have hexp_le : (1 + t ^ 2 * gapK lam) ^ (m + 1) ≤ Real.exp (((m + 1 : ℕ) : ℝ) * (t ^ 2 * gapK lam)) := by
    rw [Real.exp_nat_mul]
    have h1 : (1:ℝ) + t ^ 2 * gapK lam ≤ Real.exp (t ^ 2 * gapK lam) := by
      rw [add_comm]; exact Real.add_one_le_exp _
    have hu : 0 < 1 - lam ^ 2 := by nlinarith
    have hK0 : 0 ≤ gapK lam := by
      unfold gapK gapSqrtA
      have : 0 ≤ lam * (12 / (1 - lam ^ 2)) := mul_nonneg hlam0 (by positivity)
      linarith
    have h0le : (0:ℝ) ≤ 1 + t ^ 2 * gapK lam := by positivity
    exact pow_le_pow_left₀ h0le h1 (m + 1)
  calc Real.exp (-t * ((m + 1 : ℕ) : ℝ) * τ) * iterMean pi (transferIter P t g (m + 1))
      ≤ Real.exp (-t * ((m + 1 : ℕ) : ℝ) * τ) * (1 + t ^ 2 * gapK lam) ^ (m + 1) :=
        mul_le_mul_of_nonneg_left hgrowth (Real.exp_pos _).le
    _ ≤ Real.exp (-t * ((m + 1 : ℕ) : ℝ) * τ) * Real.exp (((m + 1 : ℕ) : ℝ) * (t ^ 2 * gapK lam)) :=
        mul_le_mul_of_nonneg_left hexp_le (Real.exp_pos _).le
    _ = Real.exp (-t * ((m + 1 : ℕ) : ℝ) * τ + t ^ 2 * ((m + 1 : ℕ) : ℝ) * gapK lam) := by
        rw [← Real.exp_add]; ring_nf

omit [Fintype V] [MeasurableSpace V] [DiscreteMeasurableSpace V] [Nonempty V] in
/-- `gapK lam > 0`, for any `lam ∈ [0, 1)`. -/
private theorem gapK_pos {lam : ℝ} (hlam0 : 0 ≤ lam) (hlam1 : lam < 1) : 0 < gapK lam := by
  have hu : 0 < 1 - lam ^ 2 := by nlinarith
  unfold gapK gapSqrtA
  have : 0 ≤ lam * (12 / (1 - lam ^ 2)) := mul_nonneg hlam0 (by positivity)
  linarith

omit [Fintype V] [MeasurableSpace V] [DiscreteMeasurableSpace V] [Nonempty V] in
/-- `gapTm lam > 0`, for any `lam ∈ [0, 1)`. -/
private theorem gapTm_pos {lam : ℝ} (hlam0 : 0 ≤ lam) (hlam1 : lam < 1) : 0 < gapTm lam := by
  have hu : 0 < 1 - lam ^ 2 := by nlinarith
  unfold gapTm; positivity

omit [Fintype V] [MeasurableSpace V] [DiscreteMeasurableSpace V] [Nonempty V] in
/-- **The Chernoff exponent comparison.** At the two-branch choice
`t := min (τ / (2 * gapK lam)) (gapTm lam)`, the achieved exponent beats the target
`-τ ^ 2 / (2 * cGap lam)`, for every `τ ∈ [0, 2]`. -/
private theorem chernoff_exponent_le {lam : ℝ} (hlam0 : 0 ≤ lam) (hlam1 : lam < 1) {τ : ℝ}
    (hτ0 : 0 ≤ τ) (hτ2 : τ ≤ 2) :
    -(min (τ / (2 * gapK lam)) (gapTm lam)) * τ
        + (min (τ / (2 * gapK lam)) (gapTm lam)) ^ 2 * gapK lam
      ≤ -τ ^ 2 / (2 * cGap lam) := by
  have hK0 : 0 < gapK lam := gapK_pos hlam0 hlam1
  have hTm0 : 0 < gapTm lam := gapTm_pos hlam0 hlam1
  have hcGap1 : 8 * gapK lam ≤ cGap lam := by
    unfold cGap; nlinarith [le_max_left (2 * gapK lam) (2 / (gapK lam * gapTm lam ^ 2))]
  have hcGap2 : 8 / (gapK lam * gapTm lam ^ 2) ≤ cGap lam := by
    unfold cGap
    have hmax := le_max_right (2 * gapK lam) (2 / (gapK lam * gapTm lam ^ 2))
    have heq : (4:ℝ) * (2 / (gapK lam * gapTm lam ^ 2)) = 8 / (gapK lam * gapTm lam ^ 2) := by
      ring
    nlinarith [mul_le_mul_of_nonneg_left hmax (by norm_num : (0:ℝ) ≤ 4), heq]
  have hcGap0 : 0 < cGap lam := lt_of_lt_of_le (by positivity) hcGap1
  have hcGapTm2 : 8 ≤ gapK lam * gapTm lam ^ 2 * cGap lam := by
    have h' : 8 / (gapK lam * gapTm lam ^ 2) * (gapK lam * gapTm lam ^ 2) ≤ cGap lam * (gapK lam * gapTm lam ^ 2) :=
      mul_le_mul_of_nonneg_right hcGap2 (by positivity)
    rw [div_mul_cancel₀] at h'
    · linarith [h']
    · positivity
  rcases lt_or_ge (gapTm lam) (τ / (2 * gapK lam)) with h | h
  · rw [min_eq_right h.le]
    have hτ_ge : 2 * gapK lam * gapTm lam ≤ τ := by
      have := (lt_div_iff₀ (by positivity : (0:ℝ) < 2 * gapK lam)).mp h
      linarith [this]
    have step1 : -gapTm lam * τ + gapTm lam ^ 2 * gapK lam ≤ -(gapK lam * gapTm lam ^ 2) := by
      nlinarith [hτ_ge]
    have step2 : τ ^ 2 / (2 * cGap lam) ≤ gapK lam * gapTm lam ^ 2 := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith [hcGapTm2, sq_nonneg τ, hτ2, hτ0]
    have step2' : -(gapK lam * gapTm lam ^ 2) ≤ -τ ^ 2 / (2 * cGap lam) := by
      rw [neg_div]; linarith [step2]
    linarith [step1, step2']
  · rw [min_eq_left h]
    have key : -(τ / (2 * gapK lam)) * τ + (τ / (2 * gapK lam)) ^ 2 * gapK lam
        = -(τ ^ 2 / (4 * gapK lam)) := by
      field_simp; ring
    rw [key]
    have hle : τ ^ 2 / (2 * cGap lam) ≤ τ ^ 2 / (4 * gapK lam) := by
      apply div_le_div_of_nonneg_left (sq_nonneg τ) (by positivity)
      linarith [hcGap1]
    rw [neg_div]; linarith [hle]

omit [Nonempty V] in
/-- **The one-sided tail bound, combining the Chernoff bound with its exponent optimisation.** -/
private theorem one_sided_tail_bound
    {P : V → V → ℝ} {pi : V → ℝ} {lam : ℝ}
    (hP : Stochastic P) (hst : Stationary P pi) (hpinn : ∀ x, 0 ≤ pi x) (hpisum : ∑ x, pi x = 1)
    (hlam0 : 0 ≤ lam) (hlam1 : lam < 1) (hgap : GapContraction P pi lam)
    {g : V → ℝ} (hg0 : ∑ x, pi x * g x = 0) (hgbd : ∀ x, g x ∈ Set.Icc (-2 : ℝ) 2)
    {μ : MeasureTheory.Measure (ℕ → V)} [MeasureTheory.IsProbabilityMeasure μ]
    (hμ : IsChainMeasure P pi μ)
    (m : ℕ) {τ : ℝ} (hτ0 : 0 ≤ τ) (hτ2 : τ ≤ 2) :
    μ.real {ω : ℕ → V | ((m + 1 : ℕ) : ℝ) * τ ≤ ∑ i : Fin (m + 1), g (ω i)}
      ≤ Real.exp (-((m + 1 : ℕ) : ℝ) * τ ^ 2 / (2 * cGap lam)) := by
  set t : ℝ := min (τ / (2 * gapK lam)) (gapTm lam) with ht_def
  have hK0 : 0 < gapK lam := gapK_pos hlam0 hlam1
  have hTm0 : 0 < gapTm lam := gapTm_pos hlam0 hlam1
  have ht0 : 0 ≤ t := le_min (by positivity) hTm0.le
  have htTm : t ≤ gapTm lam := min_le_right _ _
  have hstep := one_sided_exp_markov hP hst hpinn hpisum hlam0 hlam1 hgap hg0 hgbd hμ m ht0 htTm τ
  refine hstep.trans ?_
  have hexp := chernoff_exponent_le hlam0 hlam1 hτ0 hτ2
  rw [← ht_def] at hexp
  apply Real.exp_le_exp.mpr
  have hmnn : (0:ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by positivity
  have hmul := mul_le_mul_of_nonneg_left hexp hmnn
  have heq1 : ((m + 1 : ℕ) : ℝ) * (-t * τ + t ^ 2 * gapK lam)
      = -t * ((m + 1 : ℕ) : ℝ) * τ + t ^ 2 * ((m + 1 : ℕ) : ℝ) * gapK lam := by ring
  have heq2 : ((m + 1 : ℕ) : ℝ) * (-τ ^ 2 / (2 * cGap lam))
      = -((m + 1 : ℕ) : ℝ) * τ ^ 2 / (2 * cGap lam) := by ring
  rw [heq1, heq2] at hmul
  exact hmul

omit [Nonempty V] in
/-- **The two-sided tail bound.** Symmetrising `one_sided_tail_bound` over `g` and `-g`, then
union-bounding, gives `BirkhoffTool.MixingHoeffding`'s exact shape: neither one-sided bound used
`g`'s sign, so `-g` satisfies the same `hg0`/`hgbd` hypotheses without any extra work. -/
private theorem two_sided_tail_bound
    {P : V → V → ℝ} {pi : V → ℝ} {lam : ℝ}
    (hP : Stochastic P) (hst : Stationary P pi) (hpinn : ∀ x, 0 ≤ pi x) (hpisum : ∑ x, pi x = 1)
    (hlam0 : 0 ≤ lam) (hlam1 : lam < 1) (hgap : GapContraction P pi lam)
    {g : V → ℝ} (hg0 : ∑ x, pi x * g x = 0) (hgbd : ∀ x, g x ∈ Set.Icc (-2 : ℝ) 2)
    {μ : MeasureTheory.Measure (ℕ → V)} [MeasureTheory.IsProbabilityMeasure μ]
    (hμ : IsChainMeasure P pi μ)
    (m : ℕ) {τ : ℝ} (hτ0 : 0 ≤ τ) (hτ2 : τ ≤ 2) :
    μ.real {ω : ℕ → V | ((m + 1 : ℕ) : ℝ) * τ ≤ |∑ i : Fin (m + 1), g (ω i)|}
      ≤ 2 * Real.exp (-((m + 1 : ℕ) : ℝ) * τ ^ 2 / (2 * cGap lam)) := by
  have hg0' : ∑ x, pi x * (-g x) = 0 := by
    have : ∑ x, pi x * (-g x) = -∑ x, pi x * g x := by
      rw [← Finset.sum_neg_distrib]; exact Finset.sum_congr rfl fun x _ => by ring
    rw [this, hg0, neg_zero]
  have hgbd' : ∀ x, (-g x) ∈ Set.Icc (-2 : ℝ) 2 := fun x => by
    have := hgbd x; constructor <;> [linarith [this.2]; linarith [this.1]]
  have hset : {ω : ℕ → V | ((m + 1 : ℕ) : ℝ) * τ ≤ |∑ i : Fin (m + 1), g (ω i)|}
      = {ω : ℕ → V | ((m + 1 : ℕ) : ℝ) * τ ≤ ∑ i : Fin (m + 1), g (ω i)}
        ∪ {ω : ℕ → V | ((m + 1 : ℕ) : ℝ) * τ ≤ ∑ i : Fin (m + 1), -g (ω i)} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_union, le_abs, Finset.sum_neg_distrib]
  rw [hset]
  refine (MeasureTheory.measureReal_union_le _ _).trans ?_
  have h1 := one_sided_tail_bound hP hst hpinn hpisum hlam0 hlam1 hgap hg0 hgbd hμ m hτ0 hτ2
  have h2 := one_sided_tail_bound hP hst hpinn hpisum hlam0 hlam1 hgap hg0' hgbd' hμ m hτ0 hτ2
  linarith [h1, h2]

omit [Nonempty V] in
/-- **The workhorse target, machine-checked.** `BirkhoffTool.MixingHoeffding` — the FJS-shaped
single-orbit Hoeffding tail — derived from `GapContraction`, a finite-state spectral gap, with the
explicit constant `cGap lam`. -/
theorem mixingHoeffding_of_gap
    (P : V → V → ℝ) (pi : V → ℝ) (lam : ℝ)
    (hP : Stochastic P) (hst : Stationary P pi)
    (hpos : ∀ x, 0 < pi x) (hsum : ∑ x, pi x = 1)
    (hlam0 : 0 ≤ lam) (hlam1 : lam < 1) (hgap : GapContraction P pi lam)
    (μ : MeasureTheory.Measure (ℕ → V)) [MeasureTheory.IsProbabilityMeasure μ]
    (hμ : IsChainMeasure P pi μ)
    (f : V → ℝ) (hf : ∀ x, f x ∈ Set.Icc (-1 : ℝ) 1) :
    BirkhoffTool.MixingHoeffding μ (fun i ω => f (ω i)) (∑ x, pi x * f x) (cGap lam) := by
  set mean : ℝ := ∑ x, pi x * f x with hmean_def
  set g : V → ℝ := fun x => f x - mean with hg_def
  have hpinn : ∀ x, 0 ≤ pi x := fun x => (hpos x).le
  have hmean_bd : mean ∈ Set.Icc (-1 : ℝ) 1 := by
    constructor
    · have : ∀ x, -pi x ≤ pi x * f x := fun x => by
        nlinarith [(hf x).1, hpinn x]
      have hsum' : ∑ x, -pi x ≤ ∑ x, pi x * f x := Finset.sum_le_sum fun x _ => this x
      rw [Finset.sum_neg_distrib, hsum] at hsum'
      linarith [hsum']
    · have : ∀ x, pi x * f x ≤ pi x := fun x => by nlinarith [(hf x).2, hpinn x]
      have hsum' : ∑ x, pi x * f x ≤ ∑ x, pi x := Finset.sum_le_sum fun x _ => this x
      rw [hsum] at hsum'
      linarith [hsum']
  have hgbd : ∀ x, g x ∈ Set.Icc (-2 : ℝ) 2 := fun x => by
    have h1 := hf x; have h2 := hmean_bd
    constructor <;> [linarith [h1.1, h2.2]; linarith [h1.2, h2.1]]
  have hg0 : ∑ x, pi x * g x = 0 := by
    have : ∑ x, pi x * g x = ∑ x, pi x * f x - mean * ∑ x, pi x := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun x _ => by rw [hg_def]; ring
    rw [this, hsum, mul_one, ← hmean_def]; ring
  intro n τ hn hτ
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  simp only [add_comm 1 m]
  by_cases hτ2 : τ ≤ 2
  · have hbd := two_sided_tail_bound hP hst hpinn hsum hlam0 hlam1 hgap hg0 hgbd hμ m hτ hτ2
    have hset : {ω : ℕ → V | τ ≤ |SQOracle.empiricalMean (fun i ω => f (ω i)) (m + 1) ω - mean|}
        = {ω : ℕ → V | ((m + 1 : ℕ) : ℝ) * τ ≤ |∑ i : Fin (m + 1), g (ω i)|} := by
      ext ω
      simp only [Set.mem_ofPred_eq, SQOracle.empiricalMean]
      have hne : ((m + 1 : ℕ) : ℝ) ≠ 0 := by positivity
      have heq : (((m + 1 : ℕ) : ℝ))⁻¹ * ∑ i ∈ Finset.range (m + 1), f (ω i) - mean
          = ((m + 1 : ℕ) : ℝ)⁻¹ * ∑ i : Fin (m + 1), g (ω i) := by
        rw [Fin.sum_univ_eq_sum_range (fun i => g (ω i)) (m + 1)]
        have : ∑ i ∈ Finset.range (m + 1), g (ω i)
            = ∑ i ∈ Finset.range (m + 1), f (ω i) - ((m + 1 : ℕ) : ℝ) * mean := by
          rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        rw [this]
        field_simp
      rw [heq]
      rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ (((m + 1 : ℕ) : ℝ))⁻¹)]
      constructor
      · intro h
        have h2 := mul_le_mul_of_nonneg_left h (by positivity : (0:ℝ) ≤ ((m + 1 : ℕ) : ℝ))
        rwa [← mul_assoc, mul_inv_cancel₀ hne, one_mul] at h2
      · intro h
        have h2 := mul_le_mul_of_nonneg_left h (by positivity : (0:ℝ) ≤ (((m + 1 : ℕ) : ℝ))⁻¹)
        rwa [← mul_assoc, inv_mul_cancel₀ hne, one_mul] at h2
    rw [hset]
    exact hbd
  · push Not at hτ2
    have hempty : {ω : ℕ → V | τ ≤ |SQOracle.empiricalMean (fun i ω => f (ω i)) (m + 1) ω - mean|}
        = ∅ := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_le]
      have hbound : |SQOracle.empiricalMean (fun i ω => f (ω i)) (m + 1) ω - mean| ≤ 2 := by
        unfold SQOracle.empiricalMean
        have hne : ((m + 1 : ℕ) : ℝ) ≠ 0 := by positivity
        have hsum_bd : |∑ i ∈ Finset.range (m + 1), f (ω i) - ((m + 1 : ℕ) : ℝ) * mean| ≤ 2 * ((m + 1 : ℕ) : ℝ) := by
          have heq2 : ∑ i ∈ Finset.range (m + 1), f (ω i) - ((m + 1 : ℕ) : ℝ) * mean
              = ∑ i ∈ Finset.range (m + 1), g (ω i) := by
            rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          rw [heq2]
          calc |∑ i ∈ Finset.range (m + 1), g (ω i)|
              ≤ ∑ i ∈ Finset.range (m + 1), |g (ω i)| := Finset.abs_sum_le_sum_abs _ _
            _ ≤ ∑ i ∈ Finset.range (m + 1), (2:ℝ) := by
                apply Finset.sum_le_sum
                intro i _
                exact abs_le.mpr (hgbd (ω i))
            _ = 2 * ((m + 1 : ℕ) : ℝ) := by
                rw [Finset.sum_const, Finset.card_range]; push_cast; ring
        have heq3 : (((m + 1 : ℕ) : ℝ))⁻¹ * ∑ i ∈ Finset.range (m + 1), f (ω i) - mean
            = ((m + 1 : ℕ) : ℝ)⁻¹ * (∑ i ∈ Finset.range (m + 1), f (ω i) - ((m + 1 : ℕ) : ℝ) * mean) := by
          field_simp
        rw [heq3, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ (((m + 1 : ℕ) : ℝ))⁻¹)]
        rw [inv_mul_le_iff₀ (by positivity)]
        linarith [hsum_bd]
      linarith [hbound]
    rw [hempty, MeasureTheory.measureReal_empty]
    positivity

/-- info: 'MarkovHoeffding.mixingHoeffding_of_gap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms mixingHoeffding_of_gap

/-! ## The workhorse target: delivered

**`mixingHoeffding_of_gap` derives `BirkhoffTool.MixingHoeffding` — the FJS-shaped single-orbit
Hoeffding tail — from `GapContraction`, a finite-state operator-norm spectral gap, at the explicit
constant `cGap lam`, machine-checked and guarded above.**  The route: the Cauchy-Schwarz/Young's-
inequality transfer-operator induction (`transferIter_invariant`) closes for every `lam ∈ [0, 1)`
at the closed forms `gapA`, `gapEps`, `gapTm` (`gapFP_at_Tm`, `gapL0_at_Tm`, propagated to every
`t ≤ gapTm lam` by `hFP_hL0_of_le_Tm`'s monotonicity); the resulting growth bound
(`transferIter_mean_le`) feeds a two-branch Chernoff optimisation
(`chernoff_exponent_le`, `t := min (τ / (2 · gapK lam)) (gapTm lam)`) via the MGF bridge
(`transferIter_mean_eq_iterMean`) and `IsChainMeasure`'s cylinder pricing
(`chainMeasure_cylinder_sum`, `one_sided_exp_markov`); symmetrising over `g` and `-g`
(`two_sided_tail_bound`) and handling `τ > 2` by the deterministic envelope
(`MixingHoeffding`'s event is empty there) assembles the target.

**The sharp-constant residue.**  `cGap := 4 * max (2 * gapK lam) (2 / (gapK lam * gapTm lam ^ 2))`
is not the aspirational `(1 + lam) / (1 - lam)`: `gapA`, and hence `gapK`, carries a `1 /
(1 - lam ^ 2) ^ 2` rate rather than FJS's `1 / (1 - lam)`, and the safety factor `4` and the
`gapTm := (1 - lam ^ 2) / 50` range both trade sharpness for an elementary, machine-checkable
argument (no Hoeffding's-Lemma import, no Jensen, `Real.sqrt` appearing only where `gapA` is a
literal square) — exactly the freedom the target's existential `e1` field in `SubstrateClass`
absorbs.  Tightening the constant, should a future use case need it, is a distinct, well-scoped
target from what closes here.

**A second, independent route toward Target B below was checked and set aside.**  Mathlib's
conditional sub-Gaussian machinery
(`ProbabilityTheory.HasSubgaussianMGF.sum_of_hasCondSubgaussianMGF`) gives an Azuma-Hoeffding bound
from a Poisson-equation martingale decomposition (`g = ĝ - P ĝ`, `ĝ := ∑ k, (P ^ [k]) g`,
convergent since `GapContraction` gives a `pi`-weighted `ℓ²` bound `lam ^ k` on the `k`-th
iterate).  It needs the martingale increments POINTWISE (`L^∞`) bounded, uniformly over the state
visited; `GapContraction` bounds only an `ℓ²` norm, and for a non-reversible chain that does not
transfer to a uniform `L^∞` bound without a constant depending on `pi`'s minimum value or
`Fintype.card V` — which the target's `cGap : ℝ → ℝ`, a function of `lam` alone, cannot carry.
This is why the transfer-operator route above, which never leaves the `pi`-weighted `ℓ²` norm, is
the right shape of proof for a dimension-free constant. -/

/-! ## Target B: the chain-measure existence theorem

An arbitrary `(P, pi)` pair, `P` merely `Stochastic` and `pi` a genuine probability law, has SOME
`IsChainMeasure P pi μ`: Mathlib's Ionescu-Tulcea construction (`ProbabilityTheory.Kernel.traj`,
`Kernel.trajMeasure`, in `Mathlib.Probability.Kernel.IonescuTulcea.Traj`) instantiated at the
constant type family `fun _ : ℕ => V` and the constant finite-state kernel `stepKernel P` built
from `P`.  The construction indexes finite trajectories by `Π i : (Finset.Iic n : Finset ℕ), V`
rather than `Fin (n + 1) → V`; `iicFinEquiv` is the reindexing equivalence, and the cylinder-pricing
induction below (`chainMeasure_singleton`) carries the construction's own recursive law
(`ProbabilityTheory.Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure`, restated here
as `master_step`) across it. -/

/-- The finite-state step kernel `Kernel V V` built from a transition function `P`: `stepKernel P
x` draws the next state from `P x ·`, as the `ENNReal.ofReal`-weighted sum of Dirac masses. -/
private noncomputable def stepKernel (P : V → V → ℝ) : ProbabilityTheory.Kernel V V :=
  ProbabilityTheory.Kernel.ofFunOfCountable
    (fun x => ∑ y, ENNReal.ofReal (P x y) • MeasureTheory.Measure.dirac y)

omit [Nonempty V] in
/-- `stepKernel P` prices a singleton exactly by `P`. -/
private theorem stepKernel_apply_singleton (P : V → V → ℝ) (x y : V) :
    stepKernel P x {y} = ENNReal.ofReal (P x y) := by
  unfold stepKernel ProbabilityTheory.Kernel.ofFunOfCountable
  simp only [ProbabilityTheory.Kernel.coe_mk, MeasureTheory.Measure.finsetSum_apply,
    MeasureTheory.Measure.smul_apply, smul_eq_mul,
    MeasureTheory.Measure.dirac_apply' _ (MeasurableSet.of_discrete)]
  rw [Finset.sum_eq_single y]
  · simp
  · intro b _ hby
    simp [hby]
  · simp

omit [Nonempty V] in
/-- `stepKernel P` is a Markov kernel whenever `P` is stochastic. -/
private theorem stepKernel_isMarkov (P : V → V → ℝ) (hP : Stochastic P) :
    ProbabilityTheory.IsMarkovKernel (stepKernel P) := by
  refine ⟨fun x => ⟨?_⟩⟩
  unfold stepKernel ProbabilityTheory.Kernel.ofFunOfCountable
  simp only [ProbabilityTheory.Kernel.coe_mk, MeasureTheory.Measure.finsetSum_apply,
    MeasureTheory.Measure.smul_apply, smul_eq_mul,
    MeasureTheory.Measure.dirac_apply' _ (MeasurableSet.of_discrete), Set.indicator_univ,
    Pi.one_apply, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun y _ => hP.1 x y), hP.2 x, ENNReal.ofReal_one]

/-- `P` restated as a kernel `Kernel (Π _ : (Finset.Iic n : Finset ℕ), V) V` depending only on the
input's coordinate at `n`: the `n`-th step of the Ionescu-Tulcea family iterating `P`. -/
private noncomputable def chainKappa (P : V → V → ℝ) (n : ℕ) :
    ProbabilityTheory.Kernel (Π _ : (Finset.Iic n : Finset ℕ), V) V :=
  (stepKernel P).comap (fun x => x ⟨n, Finset.mem_Iic.2 le_rfl⟩) (measurable_pi_apply _)

omit [Nonempty V] in
/-- `chainKappa P n` unfolds to `stepKernel P` at the input's `n`-th coordinate. -/
private theorem chainKappa_apply (P : V → V → ℝ) (n : ℕ) (x : Π _ : (Finset.Iic n : Finset ℕ), V) :
    chainKappa P n x = stepKernel P (x ⟨n, Finset.mem_Iic.2 le_rfl⟩) := rfl

omit [Nonempty V] in
/-- `chainKappa P n` is a Markov kernel whenever `P` is stochastic. -/
private theorem chainKappa_isMarkov (P : V → V → ℝ) (hP : Stochastic P) (n : ℕ) :
    ProbabilityTheory.IsMarkovKernel (chainKappa P n) :=
  haveI := stepKernel_isMarkov P hP
  ProbabilityTheory.Kernel.IsMarkovKernel.comap (stepKernel P) _

/-- The initial law `pi` restated as a `Measure V`. -/
private noncomputable def piMeasure (pi : V → ℝ) : MeasureTheory.Measure V :=
  ∑ x, ENNReal.ofReal (pi x) • MeasureTheory.Measure.dirac x

omit [Nonempty V] in
/-- `piMeasure pi` prices a singleton exactly by `pi`. -/
private theorem piMeasure_apply_singleton (pi : V → ℝ) (x : V) :
    piMeasure pi {x} = ENNReal.ofReal (pi x) := by
  unfold piMeasure
  simp only [MeasureTheory.Measure.finsetSum_apply, MeasureTheory.Measure.smul_apply,
    smul_eq_mul, MeasureTheory.Measure.dirac_apply' _ (MeasurableSet.of_discrete)]
  rw [Finset.sum_eq_single x]
  · simp
  · intro b _ hbx
    simp [hbx]
  · simp

omit [Nonempty V] [DiscreteMeasurableSpace V] in
/-- `piMeasure pi` is a probability measure whenever `pi` is a genuine law. -/
private theorem piMeasure_isProb (pi : V → ℝ) (hpos : ∀ x, 0 < pi x) (hsum : ∑ x, pi x = 1) :
    MeasureTheory.IsProbabilityMeasure (piMeasure pi) := by
  constructor
  unfold piMeasure
  simp only [MeasureTheory.Measure.finsetSum_apply, MeasureTheory.Measure.smul_apply,
    smul_eq_mul, MeasureTheory.Measure.dirac_apply' _ MeasurableSet.univ, Set.indicator_univ,
    Pi.one_apply, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun x _ => (hpos x).le), hsum, ENNReal.ofReal_one]

/-- **The constructed chain measure.**  `Kernel.trajMeasure`, instantiated at `piMeasure pi` and
the constant kernel family `chainKappa P`: the Ionescu-Tulcea distribution of the trajectory that
starts at `pi` and iterates `P`. -/
private noncomputable def chainMeasure (P : V → V → ℝ) (pi : V → ℝ) (hP : Stochastic P) :
    MeasureTheory.Measure (ℕ → V) :=
  haveI := fun n => chainKappa_isMarkov P hP n
  ProbabilityTheory.Kernel.trajMeasure (X := fun _ : ℕ => V) (piMeasure pi) (chainKappa P)

omit [Nonempty V] in
/-- `chainMeasure P pi hP` is a probability measure whenever `pi` is a genuine law. -/
private theorem chainMeasure_isProb (P : V → V → ℝ) (pi : V → ℝ) (hP : Stochastic P)
    (hpos : ∀ x, 0 < pi x) (hsum : ∑ x, pi x = 1) :
    MeasureTheory.IsProbabilityMeasure (chainMeasure P pi hP) := by
  have := fun n => chainKappa_isMarkov P hP n
  have := piMeasure_isProb pi hpos hsum
  unfold chainMeasure
  infer_instance

/-! ### The reindexing bridge and the cylinder-pricing induction -/

/-- The Ionescu-Tulcea family's finite index `Finset.Iic n`, reindexed to `Fin (n + 1)`. -/
private noncomputable def iicFinEquiv (n : ℕ) :
    (Π _ : (Finset.Iic n : Finset ℕ), V) ≃ (Fin (n + 1) → V) where
  toFun x j := x ⟨j.1, Finset.mem_Iic.2 (Nat.lt_succ_iff.mp j.2)⟩
  invFun w i := w ⟨i.1, Nat.lt_succ_iff.mpr (Finset.mem_Iic.mp i.2)⟩
  left_inv x := by funext i; rfl
  right_inv w := by funext j; rfl

/-- A trajectory's first `n + 1` coordinates, restated in `Fin (n + 1) → V` via `iicFinEquiv`. -/
private noncomputable def restrictFin (n : ℕ) : (ℕ → V) → (Fin (n + 1) → V) :=
  fun ω => iicFinEquiv n (Preorder.frestrictLe n ω)

omit [Nonempty V] in
private theorem measurable_restrictFin (n : ℕ) : Measurable (restrictFin (V := V) n) :=
  Measurable.of_discrete.comp (Preorder.measurable_frestrictLe n)

omit [Fintype V] [Nonempty V] [MeasurableSpace V] [DiscreteMeasurableSpace V] in
/-- `restrictFin n ω` unfolds pointwise to `ω`. -/
private theorem restrictFin_apply (n : ℕ) (ω : ℕ → V) (j : Fin (n + 1)) :
    restrictFin n ω j = ω j := by
  simp [restrictFin, iicFinEquiv, Preorder.frestrictLe_apply]

omit [Fintype V] [Nonempty V] [MeasurableSpace V] [DiscreteMeasurableSpace V] in
/-- `restrictFin` extends by one coordinate via `Fin.snoc`. -/
private theorem restrictFin_snoc (n : ℕ) (ω : ℕ → V) :
    restrictFin (n + 1) ω = Fin.snoc (restrictFin n ω) (ω (n + 1)) := by
  have ha : Fin.init (restrictFin (n + 1) ω) = restrictFin n ω := by
    funext i
    rw [Fin.init, restrictFin_apply, restrictFin_apply, Fin.val_castSucc]
  have hb : restrictFin (n + 1) ω (Fin.last (n + 1)) = ω (n + 1) := by
    rw [restrictFin_apply, Fin.val_last]
  rw [← ha, ← hb, Fin.snoc_init_self]

omit [Fintype V] [Nonempty V] [MeasurableSpace V] [DiscreteMeasurableSpace V] in
/-- `restrictFin`'s one-step extension, restated as a pointwise `iff` matching the shape
`master_step`'s `compProd` needs (the pair of the restriction and the new coordinate). -/
private theorem restrictFin_succ_eq_iff (n : ℕ) (ω : ℕ → V) (w' : Fin (n + 2) → V) :
    restrictFin (n + 1) ω = w' ↔
      (Preorder.frestrictLe n ω, ω (n + 1))
        = ((iicFinEquiv n).symm (Fin.init w'), w' (Fin.last (n + 1))) := by
  rw [restrictFin_snoc, Prod.mk.injEq, Equiv.eq_symm_apply, ← restrictFin]
  constructor
  · intro h
    exact ⟨by rw [← h, Fin.init_snoc], by rw [← h, Fin.snoc_last]⟩
  · rintro ⟨h1, h2⟩
    rw [h1, h2, Fin.snoc_init_self]

omit [Fintype V] [Nonempty V] [MeasurableSpace V] [DiscreteMeasurableSpace V] in
/-- `restrictFin n ω = w` restated coordinatewise: the cylinder-membership form
`exists_chainMeasure` needs. -/
private theorem restrictFin_eq_iff (n : ℕ) (ω : ℕ → V) (w : Fin (n + 1) → V) :
    restrictFin n ω = w ↔ ∀ j : Fin (n + 1), ω (j : ℕ) = w j := by
  constructor
  · intro h j; rw [← h, restrictFin_apply]
  · intro h; funext j; rw [restrictFin_apply]; exact h j

omit [Nonempty V] in
open scoped ProbabilityTheory in
/-- **The one-step recursion, restated from `Kernel.map_frestrictLe_trajMeasure_compProd_eq_
map_trajMeasure`.**  The joint law of (trajectory up to `n`, value at `n + 1`) is the `compProd` of
the law up to `n` and `chainKappa P n`. -/
private theorem master_step (P : V → V → ℝ) (pi : V → ℝ) (hP : Stochastic P)
    (hpos : ∀ x, 0 < pi x) (hsum : ∑ x, pi x = 1) (n : ℕ) :
    haveI := fun n => chainKappa_isMarkov P hP n
    (chainMeasure P pi hP).map (Preorder.frestrictLe n) ⊗ₘ (chainKappa P n)
      = (chainMeasure P pi hP).map (fun x => (Preorder.frestrictLe n x, x (n + 1))) := by
  have := fun n => chainKappa_isMarkov P hP n
  have := piMeasure_isProb pi hpos hsum
  unfold chainMeasure
  exact ProbabilityTheory.Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure

omit [Nonempty V] in
open scoped ProbabilityTheory in
/-- A `compProd`'s measure of a singleton point, over discrete measurable spaces, factors as the
product of the base measure's and the kernel's singleton prices. -/
private theorem compProd_singleton {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [DiscreteMeasurableSpace α] [DiscreteMeasurableSpace β]
    (μ : MeasureTheory.Measure α) (κ : ProbabilityTheory.Kernel α β) [MeasureTheory.SFinite μ]
    [ProbabilityTheory.IsSFiniteKernel κ] (a₀ : α) (b₀ : β) :
    (μ ⊗ₘ κ) {(a₀, b₀)} = μ {a₀} * κ a₀ {b₀} := by
  classical
  have hs : MeasurableSet (({a₀} : Set α) ×ˢ ({b₀} : Set β)) :=
    MeasurableSet.prod MeasurableSet.of_discrete MeasurableSet.of_discrete
  rw [show ({(a₀, b₀)} : Set (α × β)) = ({a₀} : Set α) ×ˢ ({b₀} : Set β) from by simp,
    MeasureTheory.Measure.compProd_apply hs]
  have step : ∀ x, (κ x) (Prod.mk x ⁻¹' (({a₀} : Set α) ×ˢ ({b₀} : Set β)))
      = ({a₀} : Set α).indicator (fun _ => κ a₀ {b₀}) x := by
    intro x
    by_cases h : x = a₀
    · subst h
      rw [show Prod.mk x ⁻¹' (({x} : Set α) ×ˢ ({b₀} : Set β)) = {b₀} from by ext b; simp,
        Set.indicator_of_mem (Set.mem_singleton x)]
    · rw [show Prod.mk x ⁻¹' (({a₀} : Set α) ×ˢ ({b₀} : Set β)) = ∅ from by
        ext b; simp [h],
        Set.indicator_of_notMem (by simpa using h), MeasureTheory.measure_empty]
  simp_rw [step]
  rw [MeasureTheory.lintegral_indicator_const MeasurableSet.of_discrete, mul_comm]

omit [Nonempty V] in
/-- **The cylinder-pricing base case.**  `chainMeasure`'s law at horizon `0` is `pi` itself. -/
private theorem chainMeasure_restrictFin_zero (P : V → V → ℝ) (pi : V → ℝ) (hP : Stochastic P)
    (hpos : ∀ x, 0 < pi x) (hsum : ∑ x, pi x = 1) (w : Fin 1 → V) :
    (chainMeasure P pi hP).map (restrictFin 0) {w} = ENNReal.ofReal (pi (w 0)) := by
  have := fun n => chainKappa_isMarkov P hP n
  have hstep : (chainMeasure P pi hP).map (restrictFin 0)
      = ((chainMeasure P pi hP).map (Preorder.frestrictLe 0)).map (iicFinEquiv 0) :=
    (MeasureTheory.Measure.map_map Measurable.of_discrete
      (Preorder.measurable_frestrictLe 0)).symm
  rw [hstep, MeasureTheory.Measure.map_apply Measurable.of_discrete (MeasurableSet.of_discrete),
    show (iicFinEquiv (V := V) 0) ⁻¹' {w} = {(iicFinEquiv (V := V) 0).symm w} from by
      ext g; simp only [Set.mem_preimage, Set.mem_singleton_iff, Equiv.eq_symm_apply, eq_comm]]
  have hQ0 : (chainMeasure P pi hP).map (Preorder.frestrictLe 0)
      = (piMeasure pi).map
          (MeasurableEquiv.piUnique (fun _ : (Finset.Iic 0 : Finset ℕ) => V)).symm := by
    unfold chainMeasure
    rw [ProbabilityTheory.Kernel.trajMeasure,
      MeasureTheory.Measure.map_comp _ _ (Preorder.measurable_frestrictLe 0),
      ProbabilityTheory.Kernel.traj_map_frestrictLe, ProbabilityTheory.Kernel.partialTraj_self,
      MeasureTheory.Measure.id_comp]
  rw [hQ0, MeasureTheory.Measure.map_apply Measurable.of_discrete (MeasurableSet.of_discrete)]
  rw [show (MeasurableEquiv.piUnique (fun _ : (Finset.Iic 0 : Finset ℕ) => V)).symm
        ⁻¹' {(iicFinEquiv (V := V) 0).symm w}
      = {(iicFinEquiv (V := V) 0).symm w ⟨0, Finset.mem_Iic.2 le_rfl⟩} from by
        ext v
        simp only [Set.mem_preimage, Set.mem_singleton_iff]
        constructor
        · intro h; rw [← h]; simp [MeasurableEquiv.piUnique]
        · intro h
          funext i
          have hi : i = ⟨0, Finset.mem_Iic.2 le_rfl⟩ := Subsingleton.elim _ _
          rw [hi]; exact h.symm ▸ rfl]
  rw [show (iicFinEquiv (V := V) 0).symm w ⟨0, Finset.mem_Iic.2 le_rfl⟩ = w 0 from by
    simp [iicFinEquiv]]
  exact piMeasure_apply_singleton pi (w 0)

omit [Nonempty V] in
/-- **The cylinder-pricing recursive step.**  `chainMeasure`'s law at horizon `n + 1` is its law
at horizon `n`, times one further `P`-step, via `master_step` and `compProd_singleton`. -/
private theorem chainMeasure_restrictFin_succ (P : V → V → ℝ) (pi : V → ℝ) (hP : Stochastic P)
    (hpos : ∀ x, 0 < pi x) (hsum : ∑ x, pi x = 1) (n : ℕ) (w' : Fin (n + 2) → V) :
    (chainMeasure P pi hP).map (restrictFin (n + 1)) {w'}
      = (chainMeasure P pi hP).map (restrictFin n) {Fin.init w'}
        * ENNReal.ofReal (P (w' (Fin.castSucc (Fin.last n))) (w' (Fin.last (n + 1)))) := by
  have := fun n => chainKappa_isMarkov P hP n
  have := piMeasure_isProb pi hpos hsum
  set μ := chainMeasure P pi hP
  set a0 : Π _ : (Finset.Iic n : Finset ℕ), V := (iicFinEquiv n).symm (Fin.init w') with ha0
  set b0 : V := w' (Fin.last (n + 1)) with hb0
  have hset1 : restrictFin (n + 1) ⁻¹' ({w'} : Set (Fin (n + 2) → V))
      = (fun x : ℕ → V => (Preorder.frestrictLe n x, x (n + 1)))
        ⁻¹' ({(a0, b0)} : Set (_ × V)) := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    exact restrictFin_succ_eq_iff n ω w'
  rw [MeasureTheory.Measure.map_apply (measurable_restrictFin (n + 1)) MeasurableSet.of_discrete,
    hset1,
    ← MeasureTheory.Measure.map_apply
      ((Preorder.measurable_frestrictLe n).prodMk (measurable_pi_apply (n + 1)))
      MeasurableSet.of_discrete,
    ← master_step P pi hP hpos hsum n, compProd_singleton]
  congr 1
  · rw [MeasureTheory.Measure.map_apply (measurable_restrictFin n) MeasurableSet.of_discrete,
      MeasureTheory.Measure.map_apply (Preorder.measurable_frestrictLe n) MeasurableSet.of_discrete]
    congr 1
    ext ω
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    rw [show restrictFin n ω = iicFinEquiv n (Preorder.frestrictLe n ω) from rfl, ha0,
      Equiv.eq_symm_apply]
  · rw [chainKappa_apply, stepKernel_apply_singleton]
    congr 2

omit [Fintype V] [Nonempty V] [MeasurableSpace V] [DiscreteMeasurableSpace V] in
/-- Splitting a `Fin (n + 1)`-product off its last term, matched to `chainMeasure_restrictFin_
succ`'s new factor via `Fin.castSucc_succ`/`Fin.succ_last` (both hold by `rfl` on `Fin`, up to
proof irrelevance). -/
private theorem prod_castSucc_step (n : ℕ) (P : V → V → ℝ) (w' : Fin (n + 2) → V) :
    (∏ i : Fin n, ENNReal.ofReal (P ((Fin.init w') i.castSucc) ((Fin.init w') i.succ)))
      * ENNReal.ofReal (P (w' (Fin.castSucc (Fin.last n))) (w' (Fin.last (n + 1))))
    = ∏ i : Fin (n + 1), ENNReal.ofReal (P (w' i.castSucc) (w' i.succ)) :=
  (Fin.prod_univ_castSucc
    (fun i : Fin (n + 1) => ENNReal.ofReal (P (w' i.castSucc) (w' i.succ)))).symm

omit [Fintype V] [Nonempty V] [MeasurableSpace V] [DiscreteMeasurableSpace V] in
private theorem init_apply_zero (n : ℕ) (w' : Fin (n + 2) → V) : (Fin.init w') 0 = w' 0 := by
  rw [Fin.init]; congr 1

omit [Nonempty V] in
/-- **The cylinder-pricing induction.**  `chainMeasure`'s law at every horizon `n` is exactly
`IsChainMeasure`'s own product formula, in `ENNReal`: the induction combining
`chainMeasure_restrictFin_zero` and `chainMeasure_restrictFin_succ`. -/
private theorem chainMeasure_singleton (P : V → V → ℝ) (pi : V → ℝ) (hP : Stochastic P)
    (hpos : ∀ x, 0 < pi x) (hsum : ∑ x, pi x = 1) :
    ∀ (n : ℕ) (w : Fin (n + 1) → V),
      (chainMeasure P pi hP).map (restrictFin n) {w}
        = ENNReal.ofReal (pi (w 0))
          * ∏ i : Fin n, ENNReal.ofReal (P (w i.castSucc) (w i.succ)) := by
  intro n
  induction n with
  | zero =>
    intro w
    rw [chainMeasure_restrictFin_zero P pi hP hpos hsum w]
    simp
  | succ n ih =>
    intro w'
    rw [chainMeasure_restrictFin_succ P pi hP hpos hsum n w', ih (Fin.init w'), init_apply_zero]
    rw [mul_assoc, prod_castSucc_step]

/-! ### The existence theorems -/

omit [Nonempty V] in
/-- **Target B, closed.**  Every `Stochastic` `P` and genuine probability law `pi` has SOME
`IsChainMeasure P pi μ`: `chainMeasure P pi hP`, priced by `chainMeasure_singleton` and converted
from `ENNReal` to `ℝ` via `ENNReal.toReal_ofReal` at each nonnegative factor. -/
theorem exists_chainMeasure
    (P : V → V → ℝ) (pi : V → ℝ) (hP : Stochastic P) (hst : Stationary P pi)
    (hpos : ∀ x, 0 < pi x) (hsum : ∑ x, pi x = 1) :
    ∃ μ : MeasureTheory.Measure (ℕ → V),
      MeasureTheory.IsProbabilityMeasure μ ∧ IsChainMeasure P pi μ := by
  refine ⟨chainMeasure P pi hP, chainMeasure_isProb P pi hP hpos hsum, ?_⟩
  intro n w
  have heq : {ω : ℕ → V | ∀ i : Fin (n + 1), ω (i : ℕ) = w i} = restrictFin n ⁻¹' {w} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_singleton_iff]
    exact (restrictFin_eq_iff n ω w).symm
  rw [heq, show (chainMeasure P pi hP).real (restrictFin n ⁻¹' {w})
      = ((chainMeasure P pi hP).map (restrictFin n) {w}).toReal from by
    rw [MeasureTheory.Measure.map_apply (measurable_restrictFin n) MeasurableSet.of_discrete]; rfl,
    chainMeasure_singleton P pi hP hpos hsum n w, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (hpos (w 0)).le, ENNReal.toReal_prod]
  congr 1
  exact Finset.prod_congr rfl fun i _ => ENNReal.toReal_ofReal (hP.1 (w i.castSucc) (w i.succ))

/-- info: 'MarkovHoeffding.exists_chainMeasure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms exists_chainMeasure

omit [Nonempty V] in
/-- **The workhorse target, unconditional.**  `exists_chainMeasure` plus `mixingHoeffding_of_gap`:
every `Stochastic`/`GapContraction` pair at a genuine gap has an `IsChainMeasure` witness
satisfying `BirkhoffTool.MixingHoeffding` at `cGap lam` — no hypothesis left for a caller to
discharge. -/
theorem exists_mixingHoeffding_of_gap
    (P : V → V → ℝ) (pi : V → ℝ) (lam : ℝ)
    (hP : Stochastic P) (hst : Stationary P pi)
    (hpos : ∀ x, 0 < pi x) (hsum : ∑ x, pi x = 1)
    (hlam0 : 0 ≤ lam) (hlam1 : lam < 1) (hgap : GapContraction P pi lam)
    (f : V → ℝ) (hf : ∀ x, f x ∈ Set.Icc (-1 : ℝ) 1) :
    ∃ μ : MeasureTheory.Measure (ℕ → V), MeasureTheory.IsProbabilityMeasure μ ∧
      IsChainMeasure P pi μ ∧
      BirkhoffTool.MixingHoeffding μ (fun i ω => f (ω i)) (∑ x, pi x * f x) (cGap lam) := by
  obtain ⟨μ, hμprob, hμchain⟩ := exists_chainMeasure P pi hP hst hpos hsum
  have := hμprob
  exact ⟨μ, hμprob, hμchain,
    mixingHoeffding_of_gap P pi lam hP hst hpos hsum hlam0 hlam1 hgap μ hμchain f hf⟩

/-- info: 'MarkovHoeffding.exists_mixingHoeffding_of_gap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms exists_mixingHoeffding_of_gap

end MarkovHoeffding
