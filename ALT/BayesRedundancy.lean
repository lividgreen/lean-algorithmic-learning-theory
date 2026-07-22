/-
Copyright (c) 2026 Mykola Palamarchuk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mykola Palamarchuk
-/
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.SpecialFunctions.Pow.Real

-- Formal-check file, not Mathlib-destined: opt out of the house-style linters.
set_option linter.style.header false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Bayes-mixture redundancy — [Discovery] §3, Sub-problem B (toward an unconditional Theorem 3.1)

Provenance: [Discovery] §3. Theorem 3.1's rate (3) is the classical
Bayes-mixture redundancy bound (Hutter 2003, 2005; in the discrete-class concentration form,
Lattimore–Hutter–Sunehag 2013), here *proved* directly in the **realizable-deterministic** case —
no Grünwald–Mehta import. (Grünwald–Mehta 2020 Thm 22 enters only in
`ALT/GrunwaldMehtaDiscovery.lean`, as the named hypothesis `hrate`, for the separate general
stochastic / aggregate-separation case.) The redundancy argument:

> `P̄(o₁:ₙ) = Σ_i 2^{−K(i)} L_i(o₁:ₙ)`, `L_i = ∏_t q_i(oₜ | o_{<t})`. Then
> (1) `−log P̄(o₁:ₙ) ≤ K(R)·ln 2` (mixture ≥ the `R`-term, `L_R = 1` deterministically);
> (2) telescoping `−log P̄ = Σ_t −log P̄(oₜ | o_{<t})`;
> (3) per step `−log P̄(oₜ | o_{<t}) ≥ 2·D_H²(δ_{oₜ}, P̄(· | o_{<t}))`;
> (4) sum + average ⇒ `avg_t D_H²_t ≤ K(R)·ln 2 / (2n)`.

This file proves the **two elementary core lemmas** (later prompts assemble (2),(4)):

* **(A)** the calculus inequality of step (3), `2·(1 − √a) ≤ −log a`, and the
  squared-Hellinger-to-point-mass identity `D_H²(δ_o, q) = 1 − √(q o)` — together giving step (3):
  `−log (q o) ≥ 2·(1 − √(q o)) = 2·D_H²(δ_o, q)`.
* **(B)** the mixture-regret bound of step (1): `w_R · L_R ≤ P̄` (a single nonneg term of the
  mixture), its log form, and the realizable / Kolmogorov-weight specialisations.

## Model (stated explicitly)
* A **mixture** over a finite hypothesis class `ι`: `Pbar L w = Σ_i w i · L i`, with per-hypothesis
  likelihood `L i ≥ 0` and prior weight `w i ≥ 0`. The intended reading: `w i = 2^{−K(i)}` (a Kraft
  sub-distribution, `ALT/PriorNormalization.lean`) and `L i` the realised likelihood of the data
  under hypothesis `i`; `R` is the true rule, `L R = 1` in the realizable-deterministic case.
* **Squared Hellinger** of two finite "distributions" `p, q : α → ℝ`:
  `sqHellinger p q = (1/2) Σ_x (√(p x) − √(q x))²`. (`δ_o` is the point mass `x ↦ if x = o then 1 else 0`.)

Everything here is elementary (Mathlib calculus + `Finset`); no `sorry`. The deep GM Thm 22 is
*not* used — this is the realizable-deterministic route that will let §3 drop `hrate`.
-/

namespace BayesRedundancy

open scoped BigOperators

/-! ## (A) Log-vs-Hellinger inequality and the point-mass identity (step 3) -/

/-- **Log ≥ twice the Hellinger affinity gap.** `2·(1 − √a) ≤ −log a` for `0 < a ≤ 1`. (In fact it
holds for all `a > 0`; `a ≤ 1` records the intended domain — `a = q o` a probability.) Decisive step:
substitute `a = (√a)²`, so `−log a = −2·log √a`, and `log √a ≤ √a − 1` (`Real.log_le_sub_one_of_pos`)
gives `−log √a ≥ 1 − √a`. -/
theorem log_le_hellinger {a : ℝ} (ha : 0 < a) (_ha1 : a ≤ 1) :
    2 * (1 - Real.sqrt a) ≤ - Real.log a := by
  have ht : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha
  have hkey : Real.log (Real.sqrt a) ≤ Real.sqrt a - 1 := Real.log_le_sub_one_of_pos ht
  have hloga : Real.log a = 2 * Real.log (Real.sqrt a) := by
    conv_lhs => rw [← Real.sq_sqrt ha.le]
    rw [Real.log_pow]; push_cast; ring
  rw [hloga]; linarith [hkey]

/-- Squared Hellinger distance of two finite "distributions": `(1/2) Σ_x (√(p x) − √(q x))²`. -/
noncomputable def sqHellinger {α : Type*} [Fintype α] (p q : α → ℝ) : ℝ :=
  (1 / 2) * ∑ x, (Real.sqrt (p x) - Real.sqrt (q x)) ^ 2

/-- Squared Hellinger distance is nonnegative (a half-sum of squares); no hypothesis on `p`, `q`. -/
theorem sqHellinger_nonneg {α : Type*} [Fintype α] (p q : α → ℝ) : 0 ≤ sqHellinger p q := by
  unfold sqHellinger
  exact mul_nonneg (by norm_num) (Finset.sum_nonneg fun x _ => sq_nonneg _)

/-- **Point-mass identity.** For a pmf `q` (`q ≥ 0`, `Σ q = 1`) and a point `o`, the squared Hellinger
distance to the point mass `δ_o` is `D_H²(δ_o, q) = 1 − √(q o)`. Combined with `log_le_hellinger`
this is step (3): `−log (q o) ≥ 2·(1 − √(q o)) = 2·D_H²(δ_o, q)`. -/
theorem hellinger_point_mass {α : Type*} [Fintype α] [DecidableEq α] (q : α → ℝ) (o : α)
    (hq : ∀ x, 0 ≤ q x) (hsum : ∑ x, q x = 1) :
    sqHellinger (fun x => if x = o then 1 else 0) q = 1 - Real.sqrt (q o) := by
  unfold sqHellinger
  have hrest : ∀ x ∈ Finset.univ.erase o,
      (Real.sqrt (if x = o then (1 : ℝ) else 0) - Real.sqrt (q x)) ^ 2 = q x := by
    intro x hx
    rw [if_neg (Finset.ne_of_mem_erase hx), Real.sqrt_zero, zero_sub, neg_sq, Real.sq_sqrt (hq x)]
  have hsumeq : ∑ x, (Real.sqrt (if x = o then (1 : ℝ) else 0) - Real.sqrt (q x)) ^ 2
      = 2 - 2 * Real.sqrt (q o) := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ o), Finset.sum_congr rfl hrest]
    rw [if_pos rfl, Real.sqrt_one]
    rw [Finset.sum_erase_eq_sub (Finset.mem_univ o), hsum]
    linear_combination Real.sq_sqrt (hq o)
  rw [hsumeq]; ring

/-- **Step (3), assembled.** For a pmf `q` and a realised symbol `o`, the prequential log-loss
dominates twice the squared Hellinger distance to the point mass:
`2·D_H²(δ_o, q) ≤ −log (q o)` (when `0 < q o`). -/
theorem neg_log_ge_two_hellinger {α : Type*} [Fintype α] [DecidableEq α] (q : α → ℝ) (o : α)
    (hq : ∀ x, 0 ≤ q x) (hsum : ∑ x, q x = 1) (hpos : 0 < q o) :
    2 * sqHellinger (fun x => if x = o then 1 else 0) q ≤ - Real.log (q o) := by
  rw [hellinger_point_mass q o hq hsum]
  exact log_le_hellinger hpos (hsum ▸ Finset.single_le_sum (fun i _ => hq i) (Finset.mem_univ o))

/-! ## (B) Bayes-mixture regret (step 1) -/

/-- The (sub-)mixture likelihood `P̄ = Σ_i w i · L i` over a finite hypothesis class. -/
noncomputable def Pbar {ι : Type*} [Fintype ι] (L w : ι → ℝ) : ℝ := ∑ i, w i * L i

/-- **Mixture dominates a single term.** `w_R · L_R ≤ P̄` — the mixture is at least the true rule's
contribution (one nonnegative term of the sum). -/
theorem mixture_regret {ι : Type*} [Fintype ι] (L w : ι → ℝ) (R : ι)
    (hL : ∀ i, 0 ≤ L i) (hw : ∀ i, 0 ≤ w i) : w R * L R ≤ Pbar L w :=
  Finset.single_le_sum (fun i _ => mul_nonneg (hw i) (hL i)) (Finset.mem_univ R)

/-- **Mixture regret (log form).** `−log P̄ ≤ −log w_R − log L_R`. (Note: the all-nonneg hypotheses
`hL, hw` are needed — `mixture_regret` requires every term `≥ 0` for `P̄ ≥ w_R·L_R`.) -/
theorem mixture_regret_log {ι : Type*} [Fintype ι] (L w : ι → ℝ) (R : ι)
    (hL : ∀ i, 0 ≤ L i) (hw : ∀ i, 0 ≤ w i) (hwR : 0 < w R) (hLR : 0 < L R) :
    - Real.log (Pbar L w) ≤ - Real.log (w R) - Real.log (L R) := by
  have hge := mixture_regret L w R hL hw
  have hpos : 0 < w R * L R := mul_pos hwR hLR
  have hlog : Real.log (w R * L R) ≤ Real.log (Pbar L w) := Real.log_le_log hpos hge
  rw [Real.log_mul (ne_of_gt hwR) (ne_of_gt hLR)] at hlog
  linarith

/-- **Realizable-deterministic specialisation.** With `L_R = 1` (the true rule predicts the data with
likelihood 1), the regret is `−log P̄ ≤ −log w_R`. -/
theorem mixture_regret_log_realizable {ι : Type*} [Fintype ι] (L w : ι → ℝ) (R : ι)
    (hL : ∀ i, 0 ≤ L i) (hw : ∀ i, 0 ≤ w i) (hwR : 0 < w R) (hLR : L R = 1) :
    - Real.log (Pbar L w) ≤ - Real.log (w R) := by
  have h := mixture_regret_log L w R hL hw hwR (by rw [hLR]; norm_num)
  rw [hLR, Real.log_one] at h; linarith

/-- **Kolmogorov-weight specialisation (step 1, final form).** With the prior weight `w_R = 2^{−k}`
(`k = K(R)`, a Kraft sub-distribution) and `L_R = 1`, the mixture regret is the codelength bound
`−log P̄ ≤ k · log 2 = K(R) · ln 2`. -/
theorem mixture_regret_kolmogorov {ι : Type*} [Fintype ι] (L w : ι → ℝ) (R : ι) (k : ℕ)
    (hL : ∀ i, 0 ≤ L i) (hw : ∀ i, 0 ≤ w i)
    (hwR : w R = (2 : ℝ) ^ (-(k : ℝ))) (hLR : L R = 1) :
    - Real.log (Pbar L w) ≤ (k : ℝ) * Real.log 2 := by
  have h := mixture_regret_log_realizable L w R hL hw (by rw [hwR]; positivity) hLR
  rw [hwR, Real.log_rpow (by norm_num)] at h
  linarith

/-! ## (C) Prequential telescoping + averaging ⇒ the Bayes-mixture redundancy rate (eq. 3) (steps 2 + 4)

The realizable-deterministic route to rate (3), assembling steps 1 and 3.

### Prequential model (stated precisely)
* An observation **sequence** `ω : ℕ → A` (only the first `n` symbols matter); `A` a finite alphabet.
* A finite class `ι` of hypotheses with **prior weights** `w : ι → ℝ` (`w ≥ 0`, `∑ w = 1`; intended
  `w R = 2^{−K(R)}`, a normalised Kraft prior).
* Each hypothesis's **conditional next-symbol pmf** `q : ι → ℕ → A → ℝ`: `q i t x` is `i`'s
  probability of symbol `x` at step `t` — the history `ω_{<t}` is carried by the time index `t`
  (`q i t · ` is a genuine pmf: `q ≥ 0`, `∑ₓ q i t x = 1`). This curries the prefix into `t`,
  avoiding `Fin`-index bookkeeping.
* **Prefix likelihood** `Lik i t = ∏_{s<t} q i s (ω s)`, **mixture prefix mass**
  `Pbarₚ t = ∑ᵢ w i · Lik i t`, **conditional predictive**
  `condPred t x = (∑ᵢ w i · Lik i t · q i t x) / Pbarₚ t`.
* **Realizable-deterministic**: `q R s (ω s) = 1` for all `s` (the true rule predicts the realised
  symbol with certainty), so `Lik R t = 1` and `Pbarₚ t ≥ w R > 0`.

### What is proved (no `sorry`)
`telescope` (step 2): `−log Pbarₚ n = ∑_{t<n} −log condPred t (ω t)` (log-ratios telescope, `Pbarₚ 0 =
∑ w = 1`); `cumulative_hellinger` and `average_hellinger_rate` (step 4): combining step 3 per `t` with
step 1, `∑_{t<n} D_H²_t ≤ K(R)·ln2 / 2`, hence some step has `D_H²_t ≤ K(R)·ln2 / (2n)` — **rate (3),
proved**, not assumed. -/

section Prequential

variable {A : Type*} [Fintype A] [DecidableEq A] {ι : Type*} [Fintype ι]

/-- Prefix likelihood `L_i(t) = ∏_{s<t} q_i(ω_s | ω_{<s})`. -/
noncomputable def Lik (q : ι → ℕ → A → ℝ) (ω : ℕ → A) (i : ι) (t : ℕ) : ℝ :=
  ∏ s ∈ Finset.range t, q i s (ω s)

/-- Mixture prefix mass `P̄(t) = ∑_i w_i L_i(t)`. -/
noncomputable def Pbarₚ (q : ι → ℕ → A → ℝ) (w : ι → ℝ) (ω : ℕ → A) (t : ℕ) : ℝ :=
  ∑ i, w i * Lik q ω i t

/-- Conditional predictive pmf `cond_t(x) = [∑_i w_i L_i(t) q_i(x)] / P̄(t)`. -/
noncomputable def condPred (q : ι → ℕ → A → ℝ) (w : ι → ℝ) (ω : ℕ → A) (t : ℕ) (x : A) : ℝ :=
  (∑ i, w i * Lik q ω i t * q i t x) / Pbarₚ q w ω t

variable {q : ι → ℕ → A → ℝ} {w : ι → ℝ} {ω : ℕ → A} {R : ι}

/-- The likelihood extends by the step-`t` conditional. -/
lemma Lik_succ (i : ι) (t : ℕ) : Lik q ω i (t + 1) = Lik q ω i t * q i t (ω t) := by
  unfold Lik; rw [Finset.prod_range_succ]

lemma Lik_nonneg (hq : ∀ i s x, 0 ≤ q i s x) (i : ι) (t : ℕ) : 0 ≤ Lik q ω i t :=
  Finset.prod_nonneg (fun s _ => hq i s (ω s))

/-- Realizable-deterministic: the true rule's likelihood is identically `1`. -/
lemma Lik_realizable (hreal : ∀ s, q R s (ω s) = 1) (t : ℕ) : Lik q ω R t = 1 :=
  Finset.prod_eq_one (fun s _ => hreal s)

/-- `P̄(t+1) = ∑_i w_i L_i(t) q_i(ω_t)` — the mixture mass extends by the realised conditional. -/
lemma Pbarₚ_succ (t : ℕ) : Pbarₚ q w ω (t + 1) = ∑ i, w i * Lik q ω i t * q i t (ω t) := by
  unfold Pbarₚ
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Lik_succ]; ring

/-- The conditional predictive at the realised symbol is the mixture-mass ratio. -/
lemma condPred_self_ratio (t : ℕ) :
    condPred q w ω t (ω t) = Pbarₚ q w ω (t + 1) / Pbarₚ q w ω t := by
  unfold condPred; rw [← Pbarₚ_succ]

/-- `P̄(t) > 0` (it dominates the true rule's term `w R · L_R(t) = w R > 0`). -/
lemma Pbarₚ_pos (hq : ∀ i s x, 0 ≤ q i s x) (hw : ∀ i, 0 ≤ w i) (hwR : 0 < w R)
    (hreal : ∀ s, q R s (ω s) = 1) (t : ℕ) : 0 < Pbarₚ q w ω t := by
  have hge : w R * Lik q ω R t ≤ Pbarₚ q w ω t :=
    Finset.single_le_sum (fun i _ => mul_nonneg (hw i) (Lik_nonneg hq i t)) (Finset.mem_univ R)
  rw [Lik_realizable hreal t, mul_one] at hge
  linarith

lemma condPred_nonneg (hq : ∀ i s x, 0 ≤ q i s x) (hw : ∀ i, 0 ≤ w i) (hwR : 0 < w R)
    (hreal : ∀ s, q R s (ω s) = 1) (t : ℕ) (x : A) : 0 ≤ condPred q w ω t x := by
  unfold condPred
  refine div_nonneg ?_ (le_of_lt (Pbarₚ_pos hq hw hwR hreal t))
  exact Finset.sum_nonneg (fun i _ => mul_nonneg (mul_nonneg (hw i) (Lik_nonneg hq i t)) (hq i t x))

/-- **`condPred` is a pmf** (pmf-propagation): `∑_x cond_t(x) = 1`, since `∑_x P̄(ω⌢x at t) = P̄(t)`. -/
lemma condPred_sum (hq : ∀ i s x, 0 ≤ q i s x) (hw : ∀ i, 0 ≤ w i) (hwR : 0 < w R)
    (hreal : ∀ s, q R s (ω s) = 1) (hqsum : ∀ i s, ∑ x, q i s x = 1) (t : ℕ) :
    ∑ x, condPred q w ω t x = 1 := by
  have hpos := Pbarₚ_pos hq hw hwR hreal t
  simp only [condPred]
  rw [← Finset.sum_div, div_eq_one_iff_eq (ne_of_gt hpos), Finset.sum_comm]
  unfold Pbarₚ
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← Finset.mul_sum, hqsum i t, mul_one]

lemma condPred_self_pos (hq : ∀ i s x, 0 ≤ q i s x) (hw : ∀ i, 0 ≤ w i) (hwR : 0 < w R)
    (hreal : ∀ s, q R s (ω s) = 1) (t : ℕ) : 0 < condPred q w ω t (ω t) := by
  rw [condPred_self_ratio]
  exact div_pos (Pbarₚ_pos hq hw hwR hreal (t + 1)) (Pbarₚ_pos hq hw hwR hreal t)

/-- **Step 2 — telescoping.** `−log P̄(n) = ∑_{t<n} −log cond_t(ω_t)`. The per-step log-ratios
`log cond_t(ω_t) = log P̄(t+1) − log P̄(t)` telescope; `P̄(0) = ∑ w = 1` normalises. -/
theorem telescope (hq : ∀ i s x, 0 ≤ q i s x) (hw : ∀ i, 0 ≤ w i) (hwR : 0 < w R)
    (hreal : ∀ s, q R s (ω s) = 1) (hsumw : ∑ i, w i = 1) (n : ℕ) :
    - Real.log (Pbarₚ q w ω n)
      = ∑ t ∈ Finset.range n, - Real.log (condPred q w ω t (ω t)) := by
  have hP0 : Pbarₚ q w ω 0 = 1 := by
    unfold Pbarₚ Lik
    simp only [Finset.range_zero, Finset.prod_empty, mul_one]
    exact hsumw
  have hstep : ∀ t, Real.log (condPred q w ω t (ω t))
      = Real.log (Pbarₚ q w ω (t + 1)) - Real.log (Pbarₚ q w ω t) := by
    intro t
    rw [condPred_self_ratio, Real.log_div (ne_of_gt (Pbarₚ_pos hq hw hwR hreal (t + 1)))
      (ne_of_gt (Pbarₚ_pos hq hw hwR hreal t))]
  calc - Real.log (Pbarₚ q w ω n)
      = - (Real.log (Pbarₚ q w ω n) - Real.log (Pbarₚ q w ω 0)) := by rw [hP0, Real.log_one]; ring
    _ = - ∑ t ∈ Finset.range n,
          (Real.log (Pbarₚ q w ω (t + 1)) - Real.log (Pbarₚ q w ω t)) := by
        rw [Finset.sum_range_sub (fun t => Real.log (Pbarₚ q w ω t))]
    _ = - ∑ t ∈ Finset.range n, Real.log (condPred q w ω t (ω t)) := by
        rw [Finset.sum_congr rfl (fun t _ => (hstep t).symm)]
    _ = ∑ t ∈ Finset.range n, - Real.log (condPred q w ω t (ω t)) := by
        rw [Finset.sum_neg_distrib]

/-- **Step 4 — cumulative rate.** Combining step 3 (`2·D_H²_t ≤ −log cond_t(ω_t)`) per step with the
telescope and step 1 (`−log P̄(n) ≤ K(R)·ln2`), the cumulative squared Hellinger is bounded:
`∑_{t<n} D_H²(δ_{ω_t}, cond_t) ≤ K(R)·ln2 / 2`. This is the Bayes-mixture redundancy rate (eq. 3),
proved. -/
theorem cumulative_hellinger (hq : ∀ i s x, 0 ≤ q i s x) (hw : ∀ i, 0 ≤ w i)
    (hreal : ∀ s, q R s (ω s) = 1) (hsumw : ∑ i, w i = 1) (hqsum : ∀ i s, ∑ x, q i s x = 1)
    (k : ℕ) (hwR : w R = (2 : ℝ) ^ (-(k : ℝ))) (n : ℕ) :
    ∑ t ∈ Finset.range n,
        sqHellinger (fun x => if x = ω t then 1 else 0) (condPred q w ω t)
      ≤ (k : ℝ) * Real.log 2 / 2 := by
  have hwRpos : 0 < w R := by rw [hwR]; positivity
  have h3 : ∀ t, 2 * sqHellinger (fun x => if x = ω t then 1 else 0) (condPred q w ω t)
      ≤ - Real.log (condPred q w ω t (ω t)) := fun t =>
    neg_log_ge_two_hellinger (condPred q w ω t) (ω t)
      (fun x => condPred_nonneg hq hw hwRpos hreal t x)
      (condPred_sum hq hw hwRpos hreal hqsum t) (condPred_self_pos hq hw hwRpos hreal t)
  have hsum3 := Finset.sum_le_sum (fun t (_ : t ∈ Finset.range n) => h3 t)
  rw [← telescope hq hw hwRpos hreal hsumw n, ← Finset.mul_sum] at hsum3
  have h1 : - Real.log (Pbarₚ q w ω n) ≤ (k : ℝ) * Real.log 2 :=
    mixture_regret_kolmogorov (fun i => Lik q ω i n) w R k
      (fun i => Lik_nonneg hq i n) hw hwR (Lik_realizable hreal n)
  linarith [hsum3, h1]

/-- **Step 4 — averaged rate (3).** Some step has small squared Hellinger:
`∃ t < n, D_H²(δ_{ω_t}, cond_t) ≤ K(R)·ln2 / (2n)` (a minimal term is below the average). -/
theorem average_hellinger_rate (hq : ∀ i s x, 0 ≤ q i s x) (hw : ∀ i, 0 ≤ w i)
    (hreal : ∀ s, q R s (ω s) = 1) (hsumw : ∑ i, w i = 1) (hqsum : ∀ i s, ∑ x, q i s x = 1)
    (k : ℕ) (hwR : w R = (2 : ℝ) ^ (-(k : ℝ))) (n : ℕ) (hn : 0 < n) :
    ∃ t ∈ Finset.range n,
      sqHellinger (fun x => if x = ω t then 1 else 0) (condPred q w ω t)
        ≤ (k : ℝ) * Real.log 2 / (2 * n) := by
  have hcum := cumulative_hellinger hq hw hreal hsumw hqsum k hwR n
  have hne : (Finset.range n).Nonempty := Finset.nonempty_range_iff.mpr (by omega)
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  refine Finset.exists_le_of_sum_le hne ?_
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have heq : (n : ℝ) * ((k : ℝ) * Real.log 2 / (2 * n)) = (k : ℝ) * Real.log 2 / 2 := by
    field_simp
  rw [heq]; exact hcum

/-! ## (D) Bounded surprise: an `n`-free ceiling on the number of high-error steps

A pigeonhole on top of the cumulative bound. Since the *total* squared Hellinger error over the first
`n` steps is at most `K(R)·ln2 / 2` — a quantity that does not grow with `n` — the steps at which the
predictor errs by more than a fixed `ε` cannot be many: there are fewer than `K(R)·ln2 / (2ε)` of
them, **uniformly in `n`**. Beyond that finite budget of "surprises" the mixture predicts within `ε`
forever after; the exceptional steps may, however, occur anywhere in time.

The bound carries **no separation hypothesis** — that is its entire point. On hypothesis classes where
per-step separation is vacuous, and a *chronological* discovery rate is provably unavailable (no bound
of the form "after step `T` all steps are good"), this counting statement is what survives: the
surprises are budgeted, but not scheduled. -/

/-- The **surprise set**: the steps `t < n` at which the mixture's one-step squared Hellinger error
against the realised symbol exceeds `ε`. -/
noncomputable def surpriseSet (q : ι → ℕ → A → ℝ) (w : ι → ℝ) (ω : ℕ → A) (ε : ℝ) (n : ℕ) :
    Finset ℕ :=
  (Finset.range n).filter fun t =>
    ε < sqHellinger (fun x => if x = ω t then 1 else 0) (condPred q w ω t)

lemma surpriseSet_subset (ε : ℝ) (n : ℕ) : surpriseSet q w ω ε n ⊆ Finset.range n :=
  Finset.filter_subset _ _

lemma lt_of_mem_surpriseSet {ε : ℝ} {n t : ℕ} (ht : t ∈ surpriseSet q w ω ε n) :
    ε < sqHellinger (fun x => if x = ω t then 1 else 0) (condPred q w ω t) :=
  (Finset.mem_filter.mp ht).2

/-- **Bounded surprise ([Discovery] §3.3, Proposition 3.3) — robust form.** The number of steps at
which the one-step squared Hellinger error exceeds `ε`, times `ε`, is at most the description length
`K(R)·ln2 / 2`:  `|{t < n : D_H²ₜ > ε}| · ε ≤ K(R)·ln2 / 2`.

The right-hand side is free of `n`, so the count is bounded uniformly in the horizon. Proof: every
term of the surprise set exceeds `ε` (pigeonhole), the omitted terms are nonnegative
(`sqHellinger_nonneg`), and the total is bounded by the cumulative redundancy bound
([Discovery] §3.2 eq. (4)). No hypothesis on `ε`, and — crucially — **no separation hypothesis**. -/
theorem surprise_card_mul_le (hq : ∀ i s x, 0 ≤ q i s x) (hw : ∀ i, 0 ≤ w i)
    (hreal : ∀ s, q R s (ω s) = 1) (hsumw : ∑ i, w i = 1) (hqsum : ∀ i s, ∑ x, q i s x = 1)
    (k : ℕ) (hwR : w R = (2 : ℝ) ^ (-(k : ℝ))) (ε : ℝ) (n : ℕ) :
    ((surpriseSet q w ω ε n).card : ℝ) * ε ≤ (k : ℝ) * Real.log 2 / 2 := by
  have hlow : ((surpriseSet q w ω ε n).card : ℝ) * ε
      ≤ ∑ t ∈ surpriseSet q w ω ε n,
          sqHellinger (fun x => if x = ω t then 1 else 0) (condPred q w ω t) := by
    have h := Finset.card_nsmul_le_sum (surpriseSet q w ω ε n)
      (fun t => sqHellinger (fun x => if x = ω t then 1 else 0) (condPred q w ω t)) ε
      (fun t ht => le_of_lt (lt_of_mem_surpriseSet ht))
    simpa [nsmul_eq_mul] using h
  have hmono : ∑ t ∈ surpriseSet q w ω ε n,
        sqHellinger (fun x => if x = ω t then 1 else 0) (condPred q w ω t)
      ≤ ∑ t ∈ Finset.range n,
          sqHellinger (fun x => if x = ω t then 1 else 0) (condPred q w ω t) :=
    Finset.sum_le_sum_of_subset_of_nonneg (surpriseSet_subset ε n)
      (fun t _ _ => sqHellinger_nonneg _ _)
  have hcum := cumulative_hellinger hq hw hreal hsumw hqsum k hwR n
  linarith

/-- **Bounded surprise ([Discovery] §3.3, Proposition 3.3) — quantitative form.** For `ε > 0`,

`|{t < n : D_H²(δ_{ωₜ}, condₜ) > ε}| ≤ K(R)·ln2 / (2ε)`,

uniformly in `n`. The predictor's stock of `ε`-surprises is finite and paid for by the description
length of the true rule alone; nothing is asserted about *when* they occur. Carries **no separation
hypothesis**. -/
theorem surprise_card_le (hq : ∀ i s x, 0 ≤ q i s x) (hw : ∀ i, 0 ≤ w i)
    (hreal : ∀ s, q R s (ω s) = 1) (hsumw : ∑ i, w i = 1) (hqsum : ∀ i s, ∑ x, q i s x = 1)
    (k : ℕ) (hwR : w R = (2 : ℝ) ^ (-(k : ℝ))) {ε : ℝ} (hε : 0 < ε) (n : ℕ) :
    ((surpriseSet q w ω ε n).card : ℝ) ≤ (k : ℝ) * Real.log 2 / (2 * ε) := by
  have h := surprise_card_mul_le hq hw hreal hsumw hqsum k hwR ε n
  have h2 : (0 : ℝ) < 2 * ε := by linarith
  rw [le_div_iff₀ h2]
  have hring : ((surpriseSet q w ω ε n).card : ℝ) * (2 * ε)
      = 2 * (((surpriseSet q w ω ε n).card : ℝ) * ε) := by ring
  rw [hring]; linarith

/-- **Bounded surprise ([Discovery] §3.3, Proposition 3.3) — strict form.** For `ε > 0` and a true
rule of positive description length `k = K(R) > 0`, the count is *strictly* below the budget:

`|{t < n : D_H²(δ_{ωₜ}, condₜ) > ε}| < K(R)·ln2 / (2ε)`,

uniformly in `n`. Strictness comes from the defining inequality of the surprise set being strict when
the set is nonempty; when it is empty the count is `0`, below the positive right-hand side. Carries
**no separation hypothesis**. -/
theorem surprise_card_lt (hq : ∀ i s x, 0 ≤ q i s x) (hw : ∀ i, 0 ≤ w i)
    (hreal : ∀ s, q R s (ω s) = 1) (hsumw : ∑ i, w i = 1) (hqsum : ∀ i s, ∑ x, q i s x = 1)
    (k : ℕ) (hk : 0 < k) (hwR : w R = (2 : ℝ) ^ (-(k : ℝ))) {ε : ℝ} (hε : 0 < ε) (n : ℕ) :
    ((surpriseSet q w ω ε n).card : ℝ) < (k : ℝ) * Real.log 2 / (2 * ε) := by
  have h2 : (0 : ℝ) < 2 * ε := by linarith
  have hk' : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hlog : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  rcases Finset.eq_empty_or_nonempty (surpriseSet q w ω ε n) with hS | hS
  · rw [hS]
    simpa using div_pos (mul_pos hk' hlog) h2
  · have hstrict : ((surpriseSet q w ω ε n).card : ℝ) * ε
        < ∑ t ∈ surpriseSet q w ω ε n,
            sqHellinger (fun x => if x = ω t then 1 else 0) (condPred q w ω t) := by
      have hcst : ∑ _t ∈ surpriseSet q w ω ε n, ε
          < ∑ t ∈ surpriseSet q w ω ε n,
              sqHellinger (fun x => if x = ω t then 1 else 0) (condPred q w ω t) :=
        Finset.sum_lt_sum_of_nonempty hS (fun t ht => lt_of_mem_surpriseSet ht)
      simpa [Finset.sum_const, nsmul_eq_mul] using hcst
    have hmono : ∑ t ∈ surpriseSet q w ω ε n,
          sqHellinger (fun x => if x = ω t then 1 else 0) (condPred q w ω t)
        ≤ ∑ t ∈ Finset.range n,
            sqHellinger (fun x => if x = ω t then 1 else 0) (condPred q w ω t) :=
      Finset.sum_le_sum_of_subset_of_nonneg (surpriseSet_subset ε n)
        (fun t _ _ => sqHellinger_nonneg _ _)
    have hcum := cumulative_hellinger hq hw hreal hsumw hqsum k hwR n
    rw [lt_div_iff₀ h2]
    have hring : ((surpriseSet q w ω ε n).card : ℝ) * (2 * ε)
        = 2 * (((surpriseSet q w ω ε n).card : ℝ) * ε) := by ring
    rw [hring]; linarith

end Prequential

/-! ## Axiom audit

Each guard **fails `lake build`** if the theorem's axiom set ever drifts from the standard
`[propext, Classical.choice, Quot.sound]`. -/

/-- info: 'BayesRedundancy.sqHellinger_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sqHellinger_nonneg

/-- info: 'BayesRedundancy.surprise_card_mul_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms surprise_card_mul_le

/-- info: 'BayesRedundancy.surprise_card_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms surprise_card_le

/-- info: 'BayesRedundancy.surprise_card_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms surprise_card_lt

end BayesRedundancy
