/-
Copyright (c) 2026 Mykola Palamarchuk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mykola Palamarchuk
-/
import Mathlib.Probability.Independence.ZeroOne
import Mathlib.Probability.Independence.Integration
import Mathlib.Probability.Moments.SubGaussian

/-!
# The two-state parity walk and its sign-weighted Azuma bound

The **parity walk** is the two-state chain `x ↦ ¬x ⊕ ξ` driven by independent noise bits `ξ`.
It is the smallest genuinely *dependent* stationary source: the uniform law on `Bool` is stationary
for it, and consecutive states are perfectly anti-correlated up to the noise rate.

This module supplies the analytic engine a single-orbit Hoeffding bound for such a chain needs.
The engine is one theorem:

> `hasSubgaussianMGF_signedSum` — if `ξ` is an independent family of noise bits whose character
> `zeta ∘ ξ` has a common mean `m` from index `d` on, and `σ u` is any `Bool`-valued observable of
> the *strict past* `ξ 0, …, ξ (u + d - 1)`, then `∑_{u < n} χ(σ u) · (ζ(ξ (u+d)) − m)` has a
> sub-Gaussian moment-generating function with parameter `n` — the same parameter an i.i.d. sum of
> `[−1,1]`-valued centred variables gets.

The point is the *sign weighting*: the multiplier `χ(σ u) ∈ {±1}` may depend arbitrarily on the
past, so a dependent chain's Birkhoff sum falls into this shape whenever the chain's character
obeys a multiplicative recursion at some lag.  The proof is Hoeffding's lemma applied one step at a
time, with the past factored out by independence — no conditional expectations, no filtration, and
no general dependent-process concentration.

The second half of the module cashes the recursion in.  `lagSum_telescope` rewrites the Birkhoff
sum of the character as one signed sum plus a boundary term, and the denominator that appears there
is `1 − m` with `m ≤ 0` — *not* the spectral gap `1 + m`.  That is the whole point of the
alternating sign: the summands cancel in pairs, so the boundary term stays `O(lag)` and the
constant that comes out carries **no dependence on the noise rate**.

## Main results

* `chi`, `zeta` — the nontrivial character of `(Bool, xor)` and its negative, with the
  multiplicativity `chi_xor` that makes the whole development algebraic.
* `walk`, `par`, `walk_eq_xor_par` — the parity-walk orbit, the noise parity that drives it, and
  the identity showing the orbit is the initial state xor-shifted by that parity.
* `hasSubgaussianMGF_signedSum` — **the engine** (above).
* `measureReal_abs_ge_le` — the two-sided Chernoff bound for a sub-Gaussian variable, in the
  `2·exp(−ε²/(2c))` shape the SQ-oracle interface consumes.
* `lagSum_telescope` / `abs_chiSum_le` — the telescoping identity and the resulting deterministic
  bound `|Birkhoff sum| ≤ |signed sum| + 2·lag`.
* `chiSum_tail` — **the single-orbit tail**, for any `Bool` process whose character satisfies the
  lag-`k` recursion against an independent noise family.
-/

namespace ParityWalk

open MeasureTheory ProbabilityTheory Real

/-! ## The character of `(Bool, xor)` -/

/-- The nontrivial character of the group `(Bool, xor)`, valued in `{±1} ⊆ ℝ`. -/
def chi (b : Bool) : ℝ := if b then -1 else 1

/-- The parity walk's per-step multiplier `ζ = −χ`: it is `+1` exactly when the noise bit fires.
The sign is what distinguishes the parity walk from a lazy random walk — the deterministic
complement `¬` contributes the `−`, and makes consecutive states anti-correlated. -/
def zeta (b : Bool) : ℝ := if b then 1 else -1

@[simp] lemma chi_false : chi false = 1 := rfl
@[simp] lemma chi_true : chi true = -1 := rfl
@[simp] lemma zeta_false : zeta false = -1 := rfl
@[simp] lemma zeta_true : zeta true = 1 := rfl

lemma zeta_eq_neg_chi (b : Bool) : zeta b = -chi b := by cases b <;> simp [chi, zeta]

/-- **Multiplicativity of the character.**  This single identity turns the parity walk's Birkhoff
sums into products, and products into telescoping sums. -/
lemma chi_xor (a b : Bool) : chi (xor a b) = chi a * chi b := by
  cases a <;> cases b <;> norm_num [chi]

lemma chi_not (b : Bool) : chi (!b) = -chi b := by cases b <;> norm_num [chi]

@[simp] private lemma abs_chi (b : Bool) : |chi b| = 1 := by cases b <;> norm_num [chi]

@[simp] private lemma abs_zeta (b : Bool) : |zeta b| = 1 := by cases b <;> norm_num [zeta]

private lemma chi_mem_Icc (b : Bool) : chi b ∈ Set.Icc (-1 : ℝ) 1 := by cases b <;> norm_num [chi]

private lemma zeta_sub_mem_Icc (b : Bool) (m : ℝ) : zeta b - m ∈ Set.Icc (-1 - m) (1 - m) := by
  cases b <;> norm_num [zeta]

@[fun_prop] private lemma measurable_chi : Measurable chi := measurable_from_top

@[fun_prop] private lemma measurable_zeta : Measurable zeta := measurable_from_top

@[fun_prop] private lemma measurable_not : Measurable (not) := measurable_from_top

/-- `xor` of two measurable `Bool`-valued maps is measurable, for an arbitrary σ-algebra on the
domain — stated without the ambient instance so that it applies to a sub-σ-algebra such as
`pastAlg`. -/
private lemma measurable_xor {Ω : Type*} {m : MeasurableSpace Ω} {a b : Ω → Bool}
    (ha : Measurable[m] a) (hb : Measurable[m] b) :
    Measurable[m] (fun ω => xor (a ω) (b ω)) := by
  have hre : (fun ω => xor (a ω) (b ω)) = fun ω => if a ω = true then !(b ω) else b ω := by
    funext ω; cases a ω <;> simp
  rw [hre]
  exact Measurable.ite (ha (measurableSet_singleton true)) (measurable_not.comp hb) hb

/-! ## The parity walk -/

/-- One step of the parity walk: `x ↦ ¬x ⊕ ξ`. -/
def step (x b : Bool) : Bool := !(xor x b)

/-- The parity walk's orbit from `x₀` under the noise word `ξ`: the step into time `s+1` reads the
noise bit `ξ s`. -/
def walk (x₀ : Bool) (ξ : ℕ → Bool) : ℕ → Bool
  | 0 => x₀
  | s + 1 => step (walk x₀ ξ s) (ξ s)

@[simp] lemma walk_zero (x₀ : Bool) (ξ : ℕ → Bool) : walk x₀ ξ 0 = x₀ := rfl

@[simp] lemma walk_succ (x₀ : Bool) (ξ : ℕ → Bool) (s : ℕ) :
    walk x₀ ξ (s + 1) = !(xor (walk x₀ ξ s) (ξ s)) := rfl

/-- The parity of the noise prefix, with each bit complemented — the deterministic part of the
walk's drift folded in. -/
def par (ξ : ℕ → Bool) : ℕ → Bool
  | 0 => false
  | s + 1 => xor (par ξ s) (!(ξ s))

@[simp] lemma par_zero (ξ : ℕ → Bool) : par ξ 0 = false := rfl

@[simp] lemma par_succ (ξ : ℕ → Bool) (s : ℕ) : par ξ (s + 1) = xor (par ξ s) (!(ξ s)) := rfl

/-- **The walk is its initial state shifted by the noise parity.**  The two-state chain has no
dynamics beyond this: the whole trajectory is one bit of initial condition xor a running parity of
complemented noise bits. -/
lemma walk_eq_xor_par (x₀ : Bool) (ξ : ℕ → Bool) (s : ℕ) : walk x₀ ξ s = xor x₀ (par ξ s) := by
  induction s with
  | zero => simp
  | succ s ih => rw [walk_succ, ih, par_succ]; cases x₀ <;> cases par ξ s <;> cases ξ s <;> rfl

/-- **The one-step character recursion.**  This is the property that makes the parity walk fit the
signed-sum engine: its character multiplies by the noise character at every step. -/
lemma chi_walk_succ (x₀ : Bool) (ξ : ℕ → Bool) (s : ℕ) :
    chi (walk x₀ ξ s) * zeta (ξ s) = chi (walk x₀ ξ (s + 1)) := by
  rw [walk_succ, chi_not, chi_xor, zeta_eq_neg_chi]; ring

/-- The noise parity is measurable once the noise bits it reads are. -/
private lemma measurable_par {Ω : Type*} {m : MeasurableSpace Ω} {ζ : ℕ → Ω → Bool} (s : ℕ)
    (hζ : ∀ j, j < s → Measurable[m] (ζ j)) :
    Measurable[m] (fun ω => par (fun j => ζ j ω) s) := by
  induction s with
  | zero => exact measurable_const
  | succ s ih =>
    have hre : (fun ω => par (fun j => ζ j ω) (s + 1))
        = fun ω => xor (par (fun j => ζ j ω) s) (!(ζ s ω)) := by funext ω; rw [par_succ]
    rw [hre]
    exact measurable_xor (ih fun j hj => hζ j (by omega))
      (measurable_not.comp (hζ s (by omega)))

/-- A parity-walk orbit is measurable once its initial state and the noise bits it reads are. -/
lemma measurable_walk {Ω : Type*} {m : MeasurableSpace Ω} {x₀ : Ω → Bool} {ζ : ℕ → Ω → Bool}
    (hx : Measurable[m] x₀) (s : ℕ) (hζ : ∀ j, j < s → Measurable[m] (ζ j)) :
    Measurable[m] (fun ω => walk (x₀ ω) (fun j => ζ j ω) s) := by
  have hre : (fun ω => walk (x₀ ω) (fun j => ζ j ω) s)
      = fun ω => xor (x₀ ω) (par (fun j => ζ j ω) s) := by
    funext ω; rw [walk_eq_xor_par]
  rw [hre]
  exact measurable_xor hx (measurable_par s hζ)

/-! ## The noise σ-algebra of the strict past -/

section Past

variable {Ω : Type*}

/-- The σ-algebra generated by the noise bits indexed by a set `t`. -/
@[reducible] def noiseAlg (ξ : ℕ → Ω → Bool) (t : Set ℕ) : MeasurableSpace Ω :=
  ⨆ i ∈ t, MeasurableSpace.comap (ξ i) inferInstance

/-- The σ-algebra generated by the noise bits `ξ 0, …, ξ (n-1)` — the *strict* past at time `n`. -/
@[reducible] def pastAlg (ξ : ℕ → Ω → Bool) (n : ℕ) : MeasurableSpace Ω :=
  noiseAlg ξ {i : ℕ | i < n}

lemma measurable_noiseAlg_xi {ξ : ℕ → Ω → Bool} {t : Set ℕ} {i : ℕ} (hi : i ∈ t) :
    Measurable[noiseAlg ξ t] (ξ i) :=
  Measurable.of_comap_le (le_biSup (fun j => MeasurableSpace.comap (ξ j) inferInstance) hi)

private lemma pastAlg_mono (ξ : ℕ → Ω → Bool) {a b : ℕ} (h : a ≤ b) : pastAlg ξ a ≤ pastAlg ξ b :=
  iSup₂_mono' fun i hi => ⟨i, lt_of_lt_of_le hi h, le_rfl⟩

lemma pastAlg_le [MeasurableSpace Ω] {ξ : ℕ → Ω → Bool} (hmeas : ∀ i, Measurable (ξ i)) (n : ℕ) :
    pastAlg ξ n ≤ (inferInstance : MeasurableSpace Ω) :=
  iSup₂_le fun i _ => (hmeas i).comap_le

lemma measurable_pastAlg_xi {ξ : ℕ → Ω → Bool} {i n : ℕ} (hi : i < n) :
    Measurable[pastAlg ξ n] (ξ i) :=
  Measurable.of_comap_le (le_biSup (fun j => MeasurableSpace.comap (ξ j) inferInstance) hi)

/-- Any real-valued reading of a past noise bit is measurable for the past σ-algebra. -/
private lemma measurable_pastAlg_comp {ξ : ℕ → Ω → Bool} {i n : ℕ} (hi : i < n) (f : Bool → ℝ) :
    Measurable[pastAlg ξ n] (fun ω => f (ξ i ω)) :=
  measurable_from_top.comp (measurable_pastAlg_xi hi)

variable [MeasurableSpace Ω] {P : Measure Ω} {ξ : ℕ → Ω → Bool}

/-- **Disjoint noise sets read independent things.**  Under mutual independence of the noise bits,
anything read off the coordinates in `t` is independent of anything read off the coordinates outside
`t`.  This is the only probabilistic input the rest of the file needs; it comes from Mathlib's
`indep_biSup_compl`, so no filtration or conditional expectation appears anywhere here. -/
lemma indepFun_noiseAlg_compl (hmeas : ∀ i, Measurable (ξ i)) (hindep : iIndepFun ξ P) (t : Set ℕ)
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B] {F : Ω → A} {G : Ω → B}
    (hF : Measurable[noiseAlg ξ t] F) (hG : Measurable[noiseAlg ξ tᶜ] G) :
    IndepFun F G P := by
  have hbase : Indep (noiseAlg ξ t) (noiseAlg ξ tᶜ) P :=
    indep_biSup_compl (fun i => (hmeas i).comap_le) hindep _
  exact indep_of_indep_of_le_left (indep_of_indep_of_le_right hbase hG.comap_le) hF.comap_le

/-- **Past ⟂ present.**  The special case the signed-sum engine consumes: anything read off the
strict past at time `n` is independent of the bit `ξ n`. -/
private lemma indepFun_past_present (hmeas : ∀ i, Measurable (ξ i)) (hindep : iIndepFun ξ P) (n : ℕ)
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B] {F : Ω → A} {G : Ω → B}
    (hF : Measurable[pastAlg ξ n] F)
    (hG : Measurable[MeasurableSpace.comap (ξ n) inferInstance] G) :
    IndepFun F G P :=
  indepFun_noiseAlg_compl hmeas hindep _ hF
    (hG.mono (le_biSup (fun j => MeasurableSpace.comap (ξ j) inferInstance) (by simp)) le_rfl)

end Past

/-! ## The engine: a sub-Gaussian bound for sign-weighted noise sums -/

section SignedSum

variable {Ω : Type*}

/-- The sign-weighted partial sum: the multiplier `χ(σ u)` is an arbitrary `{±1}`-valued reading of
the strict past, the increment `ζ(ξ (u+d)) − m` a centred noise character. -/
noncomputable def signedSum (ξ σ : ℕ → Ω → Bool) (m : ℝ) (d n : ℕ) (ω : Ω) : ℝ :=
  ∑ u ∈ Finset.range n, chi (σ u ω) * (zeta (ξ (u + d) ω) - m)

@[simp] private lemma signedSum_zero (ξ σ : ℕ → Ω → Bool) (m : ℝ) (d : ℕ) :
    signedSum ξ σ m d 0 = fun _ => 0 := by funext ω; simp [signedSum]

private lemma signedSum_succ (ξ σ : ℕ → Ω → Bool) (m : ℝ) (d n : ℕ) (ω : Ω) :
    signedSum ξ σ m d (n + 1) ω
      = signedSum ξ σ m d n ω + chi (σ n ω) * (zeta (ξ (n + d) ω) - m) := by
  simp [signedSum, Finset.sum_range_succ]

variable [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {ξ : ℕ → Ω → Bool} {σ : ℕ → Ω → Bool} {m : ℝ} {d : ℕ}

omit [MeasurableSpace Ω] in
/-- The partial sum through time `n` reads only the strict past at time `n + d`. -/
private lemma measurable_signedSum (hσ : ∀ u, Measurable[pastAlg ξ (u + d)] (σ u)) (n : ℕ) :
    Measurable[pastAlg ξ (n + d)] (signedSum ξ σ m d n) := by
  change Measurable[pastAlg ξ (n + d)]
    fun ω => ∑ u ∈ Finset.range n, chi (σ u ω) * (zeta (ξ (u + d) ω) - m)
  refine Finset.measurable_fun_sum (Finset.range n) ?_
  intro u hu
  simp only [Finset.mem_range] at hu
  refine Measurable.mul ?_ (measurable_pastAlg_comp (by omega) (fun b => zeta b - m))
  have h : Measurable[pastAlg ξ (n + d)] (σ u) := (hσ u).mono (pastAlg_mono ξ (by omega)) le_rfl
  exact measurable_chi.comp h

/-- The one-step increment is centred and lives in an interval of length `2`, so Hoeffding's lemma
gives it a sub-Gaussian mgf with parameter `1`. -/
private lemma hasSubgaussianMGF_increment (hmeas : ∀ i, Measurable (ξ i))
    (hmean : ∀ u, ∫ ω, zeta (ξ (u + d) ω) ∂P = m) (n : ℕ) :
    HasSubgaussianMGF (fun ω => zeta (ξ (n + d) ω) - m) 1 P := by
  have hz : Measurable fun ω => zeta (ξ (n + d) ω) := measurable_zeta.comp (hmeas (n + d))
  have hm : Measurable fun ω => zeta (ξ (n + d) ω) - m := hz.sub measurable_const
  have hint : Integrable (fun ω => zeta (ξ (n + d) ω)) P := by
    refine (integrable_const (1 : ℝ)).mono' hz.aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => ?_)
    simp
  have h0 : ∫ ω, (zeta (ξ (n + d) ω) - m) ∂P = 0 := by
    rw [integral_sub hint (integrable_const _), hmean n]; simp
  have h := hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero (μ := P)
    (X := fun ω => zeta (ξ (n + d) ω) - m) (a := -1 - m) (b := 1 - m) hm.aemeasurable
    (Filter.Eventually.of_forall fun ω => zeta_sub_mem_Icc _ _) h0
  have hc : ((‖(1 - m) - (-1 - m)‖₊ / 2 : NNReal) ^ 2) = 1 := by
    norm_num
  rwa [hc] at h

/-- The pointwise split of the exponential at one step: two products of a *past* factor and a
*present* factor, selected by the sign bit through the projectors `(1 ± χ)/2`. -/
private lemma exp_split (t : ℝ) (S y : ℝ) (b : Bool) :
    Real.exp (t * (S + chi b * y))
      = (Real.exp (t * S) * ((1 + chi b) / 2)) * Real.exp (t * y)
        + (Real.exp (t * S) * ((1 - chi b) / 2)) * Real.exp (-t * y) := by
  rw [mul_add, Real.exp_add]
  cases b
  · simp [chi]
  · rw [chi_true, show t * (-1 * y) = -t * y by ring]; norm_num

/-- **The engine.**  A sum of `n` sign-weighted, centred noise characters has a sub-Gaussian
moment-generating function with parameter `n` — the parameter an i.i.d. `[−1,1]` sum would get —
even though the signs may depend arbitrarily on the past.

At step `n` the exponential factors as `exp(t·Sₙ)·exp(t·χ(σ n)·y)`; splitting on the two values of
`σ n` writes it as a sum of two products of a past factor and a present factor, independence
factors each integral, and the two present factors are the mgfs of `±y`, both bounded by
`exp(t²/2)` by Hoeffding's lemma.  The two past factors add back up to `exp(t·Sₙ)`, so the
induction hypothesis closes the step. -/
theorem hasSubgaussianMGF_signedSum (hmeas : ∀ i, Measurable (ξ i)) (hindep : iIndepFun ξ P)
    (hσ : ∀ u, Measurable[pastAlg ξ (u + d)] (σ u))
    (hmean : ∀ u, ∫ ω, zeta (ξ (u + d) ω) ∂P = m) (n : ℕ) :
    HasSubgaussianMGF (signedSum ξ σ m d n) n P := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hstep : HasSubgaussianMGF (fun ω => zeta (ξ (n + d) ω) - m) 1 P :=
      hasSubgaussianMGF_increment hmeas hmean n
    have hSmeas : Measurable[pastAlg ξ (n + d)] (signedSum ξ σ m d n) :=
      measurable_signedSum hσ n
    have hxipres : Measurable[MeasurableSpace.comap (ξ (n + d)) inferInstance] (ξ (n + d)) :=
      Measurable.of_comap_le le_rfl
    have hzpres : Measurable[MeasurableSpace.comap (ξ (n + d)) inferInstance]
        (fun ω => zeta (ξ (n + d) ω)) := measurable_zeta.comp hxipres
    have hymeas : Measurable[MeasurableSpace.comap (ξ (n + d)) inferInstance]
        (fun ω => zeta (ξ (n + d) ω) - m) := hzpres.sub measurable_const
    -- the four factors, at a given `t`
    have main : ∀ t : ℝ,
        Integrable (fun ω => Real.exp (t * signedSum ξ σ m d (n + 1) ω)) P ∧
          mgf (signedSum ξ σ m d (n + 1)) P t
            ≤ Real.exp ((n : ℝ) * t ^ 2 / 2) * Real.exp (t ^ 2 / 2) := by
      intro t
      set F₀ : Ω → ℝ :=
        fun ω => Real.exp (t * signedSum ξ σ m d n ω) * ((1 + chi (σ n ω)) / 2) with hF₀
      set F₁ : Ω → ℝ :=
        fun ω => Real.exp (t * signedSum ξ σ m d n ω) * ((1 - chi (σ n ω)) / 2) with hF₁
      set G₀ : Ω → ℝ := fun ω => Real.exp (t * (zeta (ξ (n + d) ω) - m)) with hG₀
      set G₁ : Ω → ℝ := fun ω => Real.exp (-t * (zeta (ξ (n + d) ω) - m)) with hG₁
      have hsplit : ∀ ω, Real.exp (t * signedSum ξ σ m d (n + 1) ω)
          = F₀ ω * G₀ ω + F₁ ω * G₁ ω := by
        intro ω
        rw [signedSum_succ]
        exact exp_split t _ _ _
      -- integrability of the four factors
      have hexpS : Integrable (fun ω => Real.exp (t * signedSum ξ σ m d n ω)) P :=
        ih.integrable_exp_mul t
      have hchi : Measurable[pastAlg ξ (n + d)] fun ω => chi (σ n ω) := measurable_chi.comp (hσ n)
      have hF₀meas : Measurable[pastAlg ξ (n + d)] F₀ :=
        (Measurable.exp (hSmeas.const_mul t)).mul ((measurable_const.add hchi).div_const 2)
      have hF₁meas : Measurable[pastAlg ξ (n + d)] F₁ :=
        (Measurable.exp (hSmeas.const_mul t)).mul ((measurable_const.sub hchi).div_const 2)
      have hF₀int : Integrable F₀ P := by
        refine hexpS.mono'
          (hF₀meas.mono (pastAlg_le hmeas (n + d)) le_rfl).aestronglyMeasurable
          (Filter.Eventually.of_forall fun ω => ?_)
        rw [hF₀]
        cases hb : σ n ω <;>
          simp [hb, abs_of_nonneg (Real.exp_nonneg (t * signedSum ξ σ m d n ω)),
            Real.exp_nonneg (t * signedSum ξ σ m d n ω)]
      have hF₁int : Integrable F₁ P := by
        refine hexpS.mono'
          (hF₁meas.mono (pastAlg_le hmeas (n + d)) le_rfl).aestronglyMeasurable
          (Filter.Eventually.of_forall fun ω => ?_)
        rw [hF₁]
        cases hb : σ n ω <;>
          simp [hb, abs_of_nonneg (Real.exp_nonneg (t * signedSum ξ σ m d n ω)),
            Real.exp_nonneg (t * signedSum ξ σ m d n ω)]
      have hG₀int : Integrable G₀ P := hstep.integrable_exp_mul t
      have hG₁int : Integrable G₁ P := hstep.integrable_exp_mul (-t)
      -- independence of past factors from present factors
      have hind₀ : IndepFun F₀ G₀ P :=
        indepFun_past_present hmeas hindep (n + d) hF₀meas (Measurable.exp (hymeas.const_mul t))
      have hind₁ : IndepFun F₁ G₁ P :=
        indepFun_past_present hmeas hindep (n + d) hF₁meas (Measurable.exp (hymeas.const_mul (-t)))
      have hint₀ : Integrable (fun ω => F₀ ω * G₀ ω) P := hind₀.integrable_mul hF₀int hG₀int
      have hint₁ : Integrable (fun ω => F₁ ω * G₁ ω) P := hind₁.integrable_mul hF₁int hG₁int
      constructor
      · exact (hint₀.add hint₁).congr (Filter.Eventually.of_forall fun ω => (hsplit ω).symm)
      · -- the mgf bound
        have hmgfsum : mgf (signedSum ξ σ m d (n + 1)) P t
            = (∫ ω, F₀ ω ∂P) * (∫ ω, G₀ ω ∂P) + (∫ ω, F₁ ω ∂P) * (∫ ω, G₁ ω ∂P) := by
          rw [mgf, integral_congr_ae (Filter.Eventually.of_forall hsplit),
            integral_add hint₀ hint₁,
            hind₀.integral_fun_mul_eq_mul_integral hF₀int.1 hG₀int.1,
            hind₁.integral_fun_mul_eq_mul_integral hF₁int.1 hG₁int.1]
        have hG₀le : (∫ ω, G₀ ω ∂P) ≤ Real.exp (t ^ 2 / 2) := by
          have := hstep.mgf_le t
          simpa [mgf, hG₀] using this
        have hG₁le : (∫ ω, G₁ ω ∂P) ≤ Real.exp (t ^ 2 / 2) := by
          have h := hstep.mgf_le (-t)
          have he : ((1 : NNReal) : ℝ) * (-t) ^ 2 / 2 = t ^ 2 / 2 := by push_cast; ring
          rw [he] at h
          simpa [mgf, hG₁] using h
        have hF₀nn : 0 ≤ ∫ ω, F₀ ω ∂P := by
          refine integral_nonneg fun ω => ?_
          rw [hF₀]; cases hb : σ n ω <;> simp [hb, Real.exp_nonneg (t * signedSum ξ σ m d n ω)]
        have hF₁nn : 0 ≤ ∫ ω, F₁ ω ∂P := by
          refine integral_nonneg fun ω => ?_
          rw [hF₁]; cases hb : σ n ω <;> simp [hb, Real.exp_nonneg (t * signedSum ξ σ m d n ω)]
        have hFsum : (∫ ω, F₀ ω ∂P) + (∫ ω, F₁ ω ∂P) = mgf (signedSum ξ σ m d n) P t := by
          rw [mgf, ← integral_add hF₀int hF₁int]
          refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
          rw [hF₀, hF₁]; ring
        have hSle : mgf (signedSum ξ σ m d n) P t ≤ Real.exp ((n : ℝ) * t ^ 2 / 2) := by
          simpa using ih.mgf_le t
        rw [hmgfsum]
        calc (∫ ω, F₀ ω ∂P) * (∫ ω, G₀ ω ∂P) + (∫ ω, F₁ ω ∂P) * (∫ ω, G₁ ω ∂P)
            ≤ (∫ ω, F₀ ω ∂P) * Real.exp (t ^ 2 / 2) + (∫ ω, F₁ ω ∂P) * Real.exp (t ^ 2 / 2) := by
              gcongr
          _ = ((∫ ω, F₀ ω ∂P) + (∫ ω, F₁ ω ∂P)) * Real.exp (t ^ 2 / 2) := by ring
          _ ≤ Real.exp ((n : ℝ) * t ^ 2 / 2) * Real.exp (t ^ 2 / 2) := by
              rw [hFsum]; gcongr
    refine ⟨fun t => (main t).1, fun t => ?_⟩
    refine (main t).2.trans_eq ?_
    rw [← Real.exp_add]
    congr 1
    push_cast
    ring

end SignedSum

/-! ## The two-sided Chernoff bound -/

/-- Two-sided Chernoff: a sub-Gaussian variable with parameter `c` leaves `[-ε, ε]` with
probability at most `2·exp(−ε²/(2c))`, the shape the SQ-oracle interface consumes. -/
lemma measureReal_abs_ge_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X : Ω → ℝ} {c : NNReal} (h : HasSubgaussianMGF X c P) {ε : ℝ}
    (hε : 0 ≤ ε) :
    P.real {ω | ε ≤ |X ω|} ≤ 2 * Real.exp (-ε ^ 2 / (2 * c)) := by
  have h1 := h.measure_ge_le hε
  have h2 := h.neg.measure_ge_le hε
  have hsub : {ω | ε ≤ |X ω|} ⊆ {ω | ε ≤ X ω} ∪ {ω | ε ≤ (-X) ω} := by
    intro ω hω
    simp only [Set.mem_setOf_eq, Set.mem_union, Pi.neg_apply] at hω ⊢
    rcases abs_choice (X ω) with hc | hc
    · exact Or.inl (hc ▸ hω)
    · exact Or.inr (hc ▸ hω)
  calc P.real {ω | ε ≤ |X ω|}
      ≤ P.real ({ω | ε ≤ X ω} ∪ {ω | ε ≤ (-X) ω}) := measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ P.real {ω | ε ≤ X ω} + P.real {ω | ε ≤ (-X) ω} := measureReal_union_le _ _
    _ ≤ 2 * Real.exp (-ε ^ 2 / (2 * c)) := by linarith

/-! ## Cashing in the recursion: the telescoping bound -/

/-- Reindexing a shifted range sum. -/
private lemma sum_range_shift (f : ℕ → ℝ) (k N : ℕ) :
    ∑ u ∈ Finset.range N, f (u + k)
      = (∑ u ∈ Finset.range (N + k), f u) - ∑ u ∈ Finset.range k, f u := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih, show N + 1 + k = (N + k) + 1 by omega, Finset.sum_range_succ]
    ring

/-- **The telescope.**  For any `Bool` sequence `o` whose character obeys the lag-`k` recursion
`χ(o u)·ζ(ζw (u+k)) = χ(o (u+k))`, the signed sum of the noise characters is the Birkhoff sum of
`χ ∘ o` weighted by `1 − m`, up to two boundary blocks of length `k`. -/
lemma lagSum_telescope (o ζw : ℕ → Bool) (k : ℕ) (m : ℝ)
    (hrec : ∀ u, chi (o u) * zeta (ζw (u + k)) = chi (o (u + k))) (N : ℕ) :
    ∑ u ∈ Finset.range N, chi (o u) * (zeta (ζw (u + k)) - m)
      = (∑ u ∈ Finset.range (N + k), chi (o u)) - (∑ u ∈ Finset.range k, chi (o u))
        - m * ∑ u ∈ Finset.range N, chi (o u) := by
  have hexp : ∀ u, chi (o u) * (zeta (ζw (u + k)) - m) = chi (o (u + k)) - m * chi (o u) := by
    intro u; rw [mul_sub, hrec u]; ring
  rw [Finset.sum_congr rfl fun u _ => hexp u, Finset.sum_sub_distrib, ← Finset.mul_sum,
    sum_range_shift (fun u => chi (o u)) k N]

/-- A Birkhoff block of length `b` has absolute value at most `b`. -/
lemma abs_chiSum_le_card (o : ℕ → Bool) (b : ℕ) :
    |∑ u ∈ Finset.range b, chi (o u)| ≤ (b : ℝ) := by
  calc |∑ u ∈ Finset.range b, chi (o u)| ≤ ∑ u ∈ Finset.range b, |chi (o u)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ = (b : ℝ) := by simp

/-- **The deterministic half of the tail bound.**  Under the lag-`k` recursion and `-1 ≤ m ≤ 0`,
the Birkhoff sum of the character through time `N + k` exceeds the signed sum by at most `2k`.

This inequality is where the parity walk's anti-correlation is cashed in.  The telescope's
denominator is `1 − m ≥ 1`, so it *helps*: no spectral gap is divided by, and the boundary term
does not grow with the noise rate. -/
lemma abs_chiSum_le (o ζw : ℕ → Bool) (k : ℕ) (m : ℝ) (hm0 : -1 ≤ m) (hm : m ≤ 0)
    (hrec : ∀ u, chi (o u) * zeta (ζw (u + k)) = chi (o (u + k))) (N : ℕ) :
    |∑ u ∈ Finset.range (N + k), chi (o u)|
      ≤ |∑ u ∈ Finset.range N, chi (o u) * (zeta (ζw (u + k)) - m)| + 2 * k := by
  set A : ℝ := ∑ u ∈ Finset.range (N + k), chi (o u) with hA
  set B : ℝ := ∑ u ∈ Finset.range k, chi (o u) with hB
  set C : ℝ := ∑ u ∈ Finset.range N, chi (o u) with hC
  set S : ℝ := ∑ u ∈ Finset.range N, chi (o u) * (zeta (ζw (u + k)) - m) with hS
  have htel : S = A - B - m * C := lagSum_telescope o ζw k m hrec N
  have hBk : |B| ≤ (k : ℝ) := abs_chiSum_le_card o k
  have hAC : |A - C| ≤ (k : ℝ) := by
    have : A - C = ∑ u ∈ Finset.range k, chi (o (u + N)) := by
      rw [hA, hC, sum_range_shift (fun u => chi (o u)) N k, show k + N = N + k by omega]
    rw [this]
    exact abs_chiSum_le_card (fun u => o (u + N)) k
  -- `(1 − m)·A = S + B − m·(A − C)`
  have hkey : (1 - m) * A = S + B - m * (A - C) := by rw [htel]; ring
  have h1m : (1 : ℝ) ≤ 1 - m := by linarith
  have habs : |A| ≤ (1 - m) * |A| := by nlinarith [abs_nonneg A]
  have hmabs : |m| ≤ 1 := abs_le.mpr ⟨hm0, by linarith⟩
  have : (1 - m) * |A| = |S + B - m * (A - C)| := by
    rw [← hkey, abs_mul, abs_of_nonneg (by linarith : (0:ℝ) ≤ 1 - m)]
  calc |A| ≤ (1 - m) * |A| := habs
    _ = |S + B - m * (A - C)| := this
    _ ≤ |S| + |B| + |m| * |A - C| := by
        have e : S + B - m * (A - C) = (S + B) + -(m * (A - C)) := by ring
        have h₁ : |(S + B) + -(m * (A - C))| ≤ |S + B| + |-(m * (A - C))| := abs_add_le _ _
        have h₂ : |S + B| ≤ |S| + |B| := abs_add_le _ _
        have h₃ : |-(m * (A - C))| = |m| * |A - C| := by rw [abs_neg, abs_mul]
        rw [e]; linarith
    _ ≤ |S| + 2 * k := by nlinarith [abs_nonneg (A - C), abs_nonneg B]

/-! ## The single-orbit tail -/

section Tail

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {ξ : ℕ → Ω → Bool} {m : ℝ} {k : ℕ}

/-- **The single-orbit tail.**  Let `ξ` be a mutually independent family of noise bits whose
character has common mean `m ∈ [−1, 0]` from index `k` on, and let `o` be any `Bool` process read
off the strict past whose character obeys the lag-`k` recursion `χ(o u)·ζ(ξ (u+k)) = χ(o (u+k))`.
Then the Birkhoff sum of `χ ∘ o` through time `N + k` obeys a genuine exponential tail, with the
boundary allowance `2k` and the sub-Gaussian parameter `N`.

For `k = 1` this is the parity walk `x ↦ ¬x ⊕ ξ` itself; larger `k` is the noisy window chain
(`ALT/NoisyWindowChain.lean`).  Note what does *not* appear: the noise rate.  The bound is uniform
over `m ∈ [−1, 0]`, i.e. over every noise level from deterministic alternation to unbiased. -/
theorem chiSum_tail (hmeas : ∀ i, Measurable (ξ i)) (hindep : iIndepFun ξ P)
    (hmean : ∀ u, ∫ ω, zeta (ξ (u + k) ω) ∂P = m) (hm0 : -1 ≤ m) (hm : m ≤ 0)
    (o : ℕ → Ω → Bool) (hom : ∀ u, Measurable[pastAlg ξ (u + k)] (o u))
    (hrec : ∀ u ω, chi (o u ω) * zeta (ξ (u + k) ω) = chi (o (u + k) ω))
    (N : ℕ) {ε : ℝ} (hε : 0 ≤ ε) :
    P.real {ω | ε + 2 * k ≤ |∑ u ∈ Finset.range (N + k), chi (o u ω)|}
      ≤ 2 * Real.exp (-ε ^ 2 / (2 * N)) := by
  have hsg : HasSubgaussianMGF (signedSum ξ o m k N) N P :=
    hasSubgaussianMGF_signedSum hmeas hindep hom hmean N
  have hsub : {ω | ε + 2 * k ≤ |∑ u ∈ Finset.range (N + k), chi (o u ω)|}
      ⊆ {ω | ε ≤ |signedSum ξ o m k N ω|} := by
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω ⊢
    have := abs_chiSum_le (fun u => o u ω) (fun u => ξ u ω) k m hm0 hm (fun u => hrec u ω) N
    simp only [signedSum]
    linarith
  calc P.real {ω | ε + 2 * k ≤ |∑ u ∈ Finset.range (N + k), chi (o u ω)|}
      ≤ P.real {ω | ε ≤ |signedSum ξ o m k N ω|} := measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ 2 * Real.exp (-ε ^ 2 / (2 * N)) := by
        simpa using measureReal_abs_ge_le hsg hε

end Tail

end ParityWalk

/-! ## Axiom audit

Both capstones are `#print axioms`-clean on the standard triple, and the guards below make that
build-enforced. -/

set_option linter.style.longLine false

/-- info: 'ParityWalk.hasSubgaussianMGF_signedSum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ParityWalk.hasSubgaussianMGF_signedSum

/-- info: 'ParityWalk.chiSum_tail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ParityWalk.chiSum_tail
