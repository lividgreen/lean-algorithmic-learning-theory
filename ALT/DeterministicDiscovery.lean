/-
Copyright (c) 2026 Mykola Palamarchuk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mykola Palamarchuk
-/
import Mathlib
import ALT.BayesRedundancy

-- Formal-check file, not Mathlib-destined: opt out of the house-style linters.
set_option linter.style.header false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

/-!
# Unconditional posterior concentration — Paper II Theorem 3.1 (realizable-deterministic)

Provenance: Paper II §3. This gives a **direct, fully unconditional** proof
of Theorem 3.1 (the prequential posterior concentrates on the true rule) in the
realizable-deterministic case — **no Grünwald–Mehta import, no Markov inequality, no
posterior-of-close hypothesis**. It replaces the whole `GrunwaldMehtaDiscovery` chain by an
elementary competitor-likelihood-decay argument, reusing the Bayes-mixture model of
`ALT/BayesRedundancy.lean`.

## The argument
The posterior weight on the true rule `R` is `wpost = w R · Lik R n / P̄(n)` (`= w R / P̄(n)` since
`Lik R n = 1` deterministically). A competitor `i ≠ R` decays:
`Lik i n = ∏_{t<n} q_i(ω_t) ≤ ∏_{t<n} exp(−2 D_H²_{i,t}) = exp(−2 ∑_t D_H²_{i,t})`, because per step
`q_i(ω_t) = (1 − D_H²_{i,t})² ≤ exp(−2 D_H²_{i,t})` (from `1 − x ≤ exp(−x)` and
`hellinger_point_mass`: `D_H²_{i,t} = 1 − √(q_i(ω_t))`). With per-step separation `ε₀`, the
cumulative separation is `n·ε₀`, so `Lik i n ≤ exp(−2 n ε₀)`, and
`1 − wpost ≤ 2^{K(R)}·exp(−2 n ε₀) ≤ δ/2` once `n ≥ T_discover`.

## What is PROVED (no `sorry`, no deep import)
* `q_self_le_exp`, `competitor_likelihood_decay`, `posterior_lower_bound`, and the capstone
  `deterministic_discovery`. The **only** hypotheses are the model (pmf `q`, prior `w` with
  `w R = 2^{−K(R)}`, `∑ w ≤ 1`), realizability (`q R s (ω s) = 1`), and **separation**
  (`hsep`, per step). No `hrate` (GM Thm 7.4), no Markov, no `posterior_of_close`.

## Separation form and discovery time
* **Separation (per-step):** `hsep : ∀ i ≠ R, ∀ t < n, ε₀ ≤ D_H²(δ_{ω_t}, q_i(·|ω_{<t}))`.
* **Discovery time:** `T_discover = (K(R)·ln 2 + ln(2/δ)) / (2 ε₀)`; `n ≥ T_discover ⇒ wpost ≥ 1 − δ/2`.
-/

namespace DeterministicDiscovery

open scoped BigOperators
open BayesRedundancy

variable {A : Type*} [Fintype A] [DecidableEq A] {ι : Type*} [Fintype ι] [DecidableEq ι]
  {q : ι → ℕ → A → ℝ} {w : ι → ℝ} {ω : ℕ → A} {R : ι}

/-- **Per-step likelihood decay.** `q_i(ω_t) ≤ exp(−2·D_H²_{i,t})`, where
`D_H²_{i,t} = sqHellinger (δ_{ω_t}) (q_i(·))`. Since `√(q_i(ω_t)) = 1 − D_H²_{i,t}`
(`hellinger_point_mass`), `q_i(ω_t) = (1−D)² ≤ exp(−D)² = exp(−2D)` using `1 − D ≤ exp(−D)`. -/
theorem q_self_le_exp (hnn : ∀ i s x, 0 ≤ q i s x) (hpmf : ∀ i s, ∑ x, q i s x = 1)
    (i : ι) (t : ℕ) :
    q i t (ω t) ≤ Real.exp (-2 * sqHellinger (fun x => if x = ω t then 1 else 0) (q i t)) := by
  set D := sqHellinger (fun x => if x = ω t then 1 else 0) (q i t) with hD
  have hsqrt : Real.sqrt (q i t (ω t)) = 1 - D := by
    rw [hD, hellinger_point_mass (q i t) (ω t) (fun x => hnn i t x) (hpmf i t)]; ring
  have hq_eq : q i t (ω t) = (1 - D) * (1 - D) := by
    rw [← hsqrt, Real.mul_self_sqrt (hnn i t (ω t))]
  have h0 : 0 ≤ 1 - D := hsqrt ▸ Real.sqrt_nonneg _
  have h1 : 1 - D ≤ Real.exp (-D) := by have := Real.add_one_le_exp (-D); linarith
  rw [hq_eq]
  calc (1 - D) * (1 - D) ≤ Real.exp (-D) * Real.exp (-D) := mul_le_mul h1 h1 h0 (Real.exp_pos _).le
    _ = Real.exp (-2 * D) := by rw [← Real.exp_add]; congr 1; ring

/-- **Competitor likelihood decay.** `Lik i n ≤ exp(−2 ∑_{t<n} D_H²_{i,t})` — the product of the
per-step bounds (`Finset.prod_le_prod`, `Real.exp_sum`). No separation assumed yet. -/
theorem competitor_likelihood_decay (hnn : ∀ i s x, 0 ≤ q i s x) (hpmf : ∀ i s, ∑ x, q i s x = 1)
    (i : ι) (n : ℕ) :
    Lik q ω i n
      ≤ Real.exp (-2 * ∑ t ∈ Finset.range n,
          sqHellinger (fun x => if x = ω t then 1 else 0) (q i t)) := by
  unfold Lik
  calc ∏ s ∈ Finset.range n, q i s (ω s)
      ≤ ∏ s ∈ Finset.range n,
          Real.exp (-2 * sqHellinger (fun x => if x = ω s then 1 else 0) (q i s)) :=
        Finset.prod_le_prod (fun s _ => hnn i s (ω s)) (fun s _ => q_self_le_exp hnn hpmf i s)
    _ = Real.exp (∑ s ∈ Finset.range n,
          -2 * sqHellinger (fun x => if x = ω s then 1 else 0) (q i s)) := (Real.exp_sum _ _).symm
    _ = Real.exp (-2 * ∑ t ∈ Finset.range n,
          sqHellinger (fun x => if x = ω t then 1 else 0) (q i t)) := by rw [← Finset.mul_sum]

/-- **Posterior lower bound.** Under realizability and a cumulative separation `S` of every competitor
(`hsep : ∀ i ≠ R, S ≤ ∑_{t<n} D_H²_{i,t}`), the posterior shortfall is exponentially small:
`1 − wpost ≤ 2^{K(R)}·exp(−2 S)`. Uses `1 − wpost = (∑_{i≠R} w_i Lik_i n)/P̄(n)`, the decay
`Lik_i n ≤ exp(−2 S)`, `∑ w ≤ 1`, and `P̄(n) ≥ w R = 2^{−K(R)}` (`mixture_regret`). -/
theorem posterior_lower_bound (hnn : ∀ i s x, 0 ≤ q i s x) (hpmf : ∀ i s, ∑ x, q i s x = 1)
    (hw : ∀ i, 0 ≤ w i) (k : ℕ) (hwR : w R = (2 : ℝ) ^ (-(k : ℝ))) (hsumw : ∑ i, w i ≤ 1)
    (hreal : ∀ s, q R s (ω s) = 1) (n : ℕ) (S : ℝ)
    (hsep : ∀ i, i ≠ R →
      S ≤ ∑ t ∈ Finset.range n, sqHellinger (fun x => if x = ω t then 1 else 0) (q i t)) :
    1 - w R * Lik q ω R n / Pbarₚ q w ω n ≤ (2 : ℝ) ^ (k : ℝ) * Real.exp (-2 * S) := by
  have hwRpos : 0 < w R := by rw [hwR]; positivity
  have hPwR : w R ≤ Pbarₚ q w ω n := by
    have := mixture_regret (fun i => Lik q ω i n) w R (fun i => Lik_nonneg hnn i n) hw
    rwa [Lik_realizable hreal n, mul_one] at this
  have hPpos : 0 < Pbarₚ q w ω n := lt_of_lt_of_le hwRpos hPwR
  have hsplit : Pbarₚ q w ω n = w R + ∑ i ∈ Finset.univ.erase R, w i * Lik q ω i n := by
    unfold Pbarₚ
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ R), Lik_realizable hreal n, mul_one]
  have hwpost : 1 - w R * Lik q ω R n / Pbarₚ q w ω n
      = (∑ i ∈ Finset.univ.erase R, w i * Lik q ω i n) / Pbarₚ q w ω n := by
    rw [Lik_realizable hreal n, mul_one, eq_comm, div_eq_iff (ne_of_gt hPpos), sub_mul, one_mul,
        div_mul_cancel₀ _ (ne_of_gt hPpos)]
    linarith [hsplit]
  have hnum : ∑ i ∈ Finset.univ.erase R, w i * Lik q ω i n ≤ Real.exp (-2 * S) := by
    calc ∑ i ∈ Finset.univ.erase R, w i * Lik q ω i n
        ≤ ∑ i ∈ Finset.univ.erase R, w i * Real.exp (-2 * S) := by
          refine Finset.sum_le_sum (fun i hi => ?_)
          have hdecay : Lik q ω i n ≤ Real.exp (-2 * S) :=
            le_trans (competitor_likelihood_decay hnn hpmf i n)
              (Real.exp_le_exp.mpr (by linarith [hsep i (Finset.ne_of_mem_erase hi)]))
          exact mul_le_mul_of_nonneg_left hdecay (hw i)
      _ = (∑ i ∈ Finset.univ.erase R, w i) * Real.exp (-2 * S) := by rw [← Finset.sum_mul]
      _ ≤ 1 * Real.exp (-2 * S) := by
          refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
          exact le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
            (fun i _ _ => hw i)) hsumw
      _ = Real.exp (-2 * S) := one_mul _
  rw [hwpost]
  calc (∑ i ∈ Finset.univ.erase R, w i * Lik q ω i n) / Pbarₚ q w ω n
      ≤ Real.exp (-2 * S) / w R := div_le_div₀ (Real.exp_pos _).le hnum hwRpos hPwR
    _ = (2 : ℝ) ^ (k : ℝ) * Real.exp (-2 * S) := by
        rw [hwR, Real.rpow_neg (by norm_num), div_eq_mul_inv, inv_inv, mul_comm]

/-- **Theorem 3.1 (unconditional, realizable-deterministic).** For per-step separation `ε₀` and
`n ≥ T_discover = (K(R)·ln 2 + ln(2/δ)) / (2 ε₀)`, the prequential posterior concentrates on the true
rule: `wpost = w R · Lik R n / P̄(n) ≥ 1 − δ/2`. The hypotheses are **only** the model + realizability
+ separation — no Grünwald–Mehta, no Markov, no posterior-of-close. -/
theorem deterministic_discovery (hnn : ∀ i s x, 0 ≤ q i s x) (hpmf : ∀ i s, ∑ x, q i s x = 1)
    (hw : ∀ i, 0 ≤ w i) (k : ℕ) (hwR : w R = (2 : ℝ) ^ (-(k : ℝ))) (hsumw : ∑ i, w i ≤ 1)
    (hreal : ∀ s, q R s (ω s) = 1) (δ ε₀ : ℝ) (hδ : 0 < δ) (hε : 0 < ε₀) (n : ℕ)
    (hsep : ∀ i, i ≠ R → ∀ t ∈ Finset.range n,
      ε₀ ≤ sqHellinger (fun x => if x = ω t then 1 else 0) (q i t))
    (hT : ((k : ℝ) * Real.log 2 + Real.log (2 / δ)) / (2 * ε₀) ≤ (n : ℝ)) :
    1 - δ / 2 ≤ w R * Lik q ω R n / Pbarₚ q w ω n := by
  -- per-step separation ⇒ cumulative `≥ n·ε₀`.
  have hcum : ∀ i, i ≠ R → (n : ℝ) * ε₀
      ≤ ∑ t ∈ Finset.range n, sqHellinger (fun x => if x = ω t then 1 else 0) (q i t) := by
    intro i hiR
    calc (n : ℝ) * ε₀ = ∑ _t ∈ Finset.range n, ε₀ := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ ≤ ∑ t ∈ Finset.range n, sqHellinger (fun x => if x = ω t then 1 else 0) (q i t) :=
          Finset.sum_le_sum (fun t ht => hsep i hiR t ht)
  have hpost := posterior_lower_bound hnn hpmf hw k hwR hsumw hreal n ((n : ℝ) * ε₀) hcum
  have hbound : (2 : ℝ) ^ (k : ℝ) * Real.exp (-2 * ((n : ℝ) * ε₀)) ≤ δ / 2 := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2), ← Real.exp_add,
        show δ / 2 = Real.exp (Real.log (δ / 2)) from (Real.exp_log (by positivity)).symm]
    apply Real.exp_le_exp.mpr
    have h2 := (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * ε₀)).mp hT
    have hlog : Real.log (δ / 2) = - Real.log (2 / δ) := by
      rw [Real.log_div (ne_of_gt hδ) (by norm_num), Real.log_div (by norm_num) (ne_of_gt hδ)]; ring
    rw [hlog]; nlinarith [h2]
  linarith [hpost, hbound]

end DeterministicDiscovery
