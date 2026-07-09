import Mathlib
import ALT.BayesRedundancy

-- Tier-1 formal check, not Mathlib-destined: opt out of the house-style linters.
set_option linter.style.header false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

/-!
# Countable discovery — Paper II Theorem 3.1 over a countable hypothesis class

Provenance: `02_mdl_dominance_and_discovery.md` §1.1, §3. `ALT/DeterministicDiscovery.lean` proves
the unconditional realizable-deterministic discovery theorem for a **finite** hypothesis class
(`ι : Fintype`). The paper's actual setting (§1.1) is a **countable** class with the
Kolmogorov-weighted prior `w(R') = 2^{−K(R')}` over all programs. This file lifts the discovery
theorem to a countable `ι`: the sums over the hypothesis index become `tsum`/`∑'`, the prior is a
**Kraft-summable sub-distribution** (`Summable w`, `∑' w ≤ 1`), and the observation alphabet `A`
stays genuinely finite (`[Fintype A]`).

## What carries over and what is re-proved
The mathematics is the finite argument with `∑'` for `∑` over `ι`; the finite `deterministic_discovery`
is untouched and still builds (this file is strictly additive). The genuinely index-free ingredient
`Lik` (`ALT/BayesRedundancy.lean`) and the alphabet-only facts `sqHellinger`,
`hellinger_point_mass` are reused as-is. The small per-hypothesis facts (`lik_nonneg`,
`lik_realizable`, `q_self_le_exp`, `competitor_likelihood_decay`) are **re-proved here verbatim**:
their finite-file counterparts sit under that file's `[Fintype ι]` section variable, which Lean's
section-variable auto-inclusion bakes into their signatures (the `unusedSectionVars` linter is off
there), so they are not directly applicable to a non-finite `ι`. The proofs are unchanged — only the
ambient `[Fintype ι]` is dropped. (The interpretive companions `telescope` / `cumulative_hellinger`,
eq. 4, are off the discovery critical path and are left in the finite file.)

## What is PROVED (no `sorry`, no deep import)
* `Lik_le_one`, `summable_w_lik`, `countable_posterior_lower_bound`, and the capstone
  `countable_discovery` — the exact analogue of `DeterministicDiscovery.deterministic_discovery` over a
  countable `ι`. The hypotheses are **only** the model (pmf `q`, prior `w` with `w R = 2^{−K(R)}`,
  `Summable w`, `∑' w ≤ 1`), realizability (`q R s (ω s) = 1`), and per-step `ε₀`-separation. No
  Grünwald–Mehta import, no Markov, no posterior-of-close.

## The countability ingredients (everything else is the finite argument verbatim)
* `Lik_le_one` + `Summable w` ⇒ `Summable (i ↦ w_i · Lik_i n)` (`Summable.of_nonneg_of_le`).
* the mixture mass splits off the true term: `P̄(n) = w_R + ∑'_i ite (i=R) 0 (w_i Lik_i n)`
  (`Summable.tsum_eq_add_tsum_ite`), so `P̄(n) ≥ w_R = 2^{−K(R)} > 0`.
* the competitor tail is bounded termwise by `w_i · exp(−2 S)` and summed via `Summable.tsum_le_tsum`
  + `tsum_mul_right`, using `∑' w ≤ 1` — exactly the finite `Finset.sum_le_sum` chain with `∑'`.
-/

namespace CountableDiscovery

open scoped BigOperators
open BayesRedundancy

variable {A : Type*} [Fintype A] [DecidableEq A] {ι : Type*} [DecidableEq ι]
  {q : ι → ℕ → A → ℝ} {w : ι → ℝ} {ω : ℕ → A} {R : ι}

/-! ## Per-hypothesis facts (re-proved without `[Fintype ι]`; proofs identical to the finite file) -/

/-- `0 ≤ Lik i n` (every factor is a probability). Verbatim `BayesRedundancy.Lik_nonneg`, without the
ambient `[Fintype ι]`. -/
lemma lik_nonneg (hnn : ∀ i s x, 0 ≤ q i s x) (i : ι) (n : ℕ) : 0 ≤ Lik q ω i n :=
  Finset.prod_nonneg (fun s _ => hnn i s (ω s))

/-- Realizable-deterministic: the true rule's likelihood is identically `1`. Verbatim
`BayesRedundancy.Lik_realizable`, without the ambient `[Fintype ι]`. -/
lemma lik_realizable (hreal : ∀ s, q R s (ω s) = 1) (n : ℕ) : Lik q ω R n = 1 :=
  Finset.prod_eq_one (fun s _ => hreal s)

/-- **Per-step likelihood decay.** `q_i(ω_t) ≤ exp(−2·D_H²_{i,t})`. Verbatim
`DeterministicDiscovery.q_self_le_exp`, without the ambient `[Fintype ι]`. -/
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

/-- **Competitor likelihood decay.** `Lik i n ≤ exp(−2 ∑_{t<n} D_H²_{i,t})`. Verbatim
`DeterministicDiscovery.competitor_likelihood_decay`, without the ambient `[Fintype ι]`. -/
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

/-! ## Countable mixture mass and the discovery theorem -/

/-- **Each prefix likelihood is `≤ 1`.** Every factor `q_i(ω_s | ω_{<s})` is a pmf value, hence
`≤ 1` (`Finset.single_le_sum` against `∑_x q = 1`); the product over `s < n` is therefore `≤ 1`
(`Finset.prod_le_one`). This is the only new fact the countable comparison test needs. -/
theorem Lik_le_one (hnn : ∀ i s x, 0 ≤ q i s x) (hpmf : ∀ i s, ∑ x, q i s x = 1)
    (i : ι) (n : ℕ) : Lik q ω i n ≤ 1 := by
  unfold Lik
  refine Finset.prod_le_one (fun s _ => hnn i s (ω s)) (fun s _ => ?_)
  calc q i s (ω s) ≤ ∑ x, q i s x := Finset.single_le_sum (fun x _ => hnn i s x) (Finset.mem_univ _)
    _ = 1 := hpmf i s

/-- Countable mixture prefix mass `P̄(t) = ∑'_i w_i L_i(t)` over a countable hypothesis class. The
countable analogue of `BayesRedundancy.Pbarₚ` (a `tsum` over `ι` in place of the `Finset` sum). -/
noncomputable def Pbarₚ' (q : ι → ℕ → A → ℝ) (w : ι → ℝ) (ω : ℕ → A) (t : ℕ) : ℝ :=
  ∑' i, w i * Lik q ω i t

/-- **The mixture summand is summable.** `0 ≤ w_i · L_i(n) ≤ w_i` (since `0 ≤ L_i ≤ 1`,
`Lik_le_one`), so summability follows from the Kraft-summable prior `Summable w` by comparison
(`Summable.of_nonneg_of_le`). -/
theorem summable_w_lik (hnn : ∀ i s x, 0 ≤ q i s x) (hpmf : ∀ i s, ∑ x, q i s x = 1)
    (hw : ∀ i, 0 ≤ w i) (hsumw : Summable w) (n : ℕ) :
    Summable (fun i => w i * Lik q ω i n) :=
  hsumw.of_nonneg_of_le
    (fun i => mul_nonneg (hw i) (lik_nonneg hnn i n))
    (fun i => mul_le_of_le_one_right (hw i) (Lik_le_one hnn hpmf i n))

/-- **Posterior lower bound (countable).** The countable analogue of
`DeterministicDiscovery.posterior_lower_bound`: under realizability and a cumulative separation `S`
of every competitor, the posterior shortfall is exponentially small,
`1 − wpost ≤ 2^{K(R)}·exp(−2 S)`. The proof is the finite one with `∑'` for `∑`: the true term is
split off by `Summable.tsum_eq_add_tsum_ite` (giving `P̄(n) = w_R + N` with `N ≥ 0`, so `P̄(n) ≥ w_R`),
and the competitor tail `N` is bounded termwise by `w_i·exp(−2 S)` and summed (`Summable.tsum_le_tsum`,
`tsum_mul_right`, `∑' w ≤ 1`). -/
theorem countable_posterior_lower_bound
    (hnn : ∀ i s x, 0 ≤ q i s x) (hpmf : ∀ i s, ∑ x, q i s x = 1)
    (hw : ∀ i, 0 ≤ w i) (k : ℕ) (hwR : w R = (2 : ℝ) ^ (-(k : ℝ)))
    (hsumw : Summable w) (hsumw1 : ∑' i, w i ≤ 1)
    (hreal : ∀ s, q R s (ω s) = 1) (n : ℕ) (S : ℝ)
    (hsep : ∀ i, i ≠ R →
      S ≤ ∑ t ∈ Finset.range n, sqHellinger (fun x => if x = ω t then 1 else 0) (q i t)) :
    1 - w R * Lik q ω R n / Pbarₚ' q w ω n ≤ (2 : ℝ) ^ (k : ℝ) * Real.exp (-2 * S) := by
  have hwRpos : 0 < w R := by rw [hwR]; positivity
  have hLikR : Lik q ω R n = 1 := lik_realizable hreal n
  have hsummable := summable_w_lik (w := w) (ω := ω) hnn hpmf hw hsumw n
  -- The competitor tail `N = ∑'_i ite (i=R) 0 (w_i L_i n)`: nonneg, summable, ≤ exp(−2S).
  have hite_nonneg : ∀ i, 0 ≤ ite (i = R) 0 (w i * Lik q ω i n) := fun i => by
    by_cases hiR : i = R
    · simp [hiR]
    · rw [if_neg hiR]; exact mul_nonneg (hw i) (lik_nonneg hnn i n)
  have hite_le : ∀ i, ite (i = R) 0 (w i * Lik q ω i n) ≤ w i * Lik q ω i n := fun i => by
    by_cases hiR : i = R
    · rw [if_pos hiR]; exact mul_nonneg (hw i) (lik_nonneg hnn i n)
    · exact le_of_eq (if_neg hiR)
  have hsumite : Summable (fun i => ite (i = R) 0 (w i * Lik q ω i n)) :=
    hsummable.of_nonneg_of_le hite_nonneg hite_le
  set N : ℝ := ∑' i, ite (i = R) 0 (w i * Lik q ω i n) with hN
  -- `P̄(n) = w_R + N` (true term split off), hence `w_R ≤ P̄(n)` and `P̄(n) > 0`.
  have hsplit : Pbarₚ' q w ω n = w R + N := by
    rw [hN]; unfold Pbarₚ'
    rw [Summable.tsum_eq_add_tsum_ite hsummable R, hLikR, mul_one]
  have hN0 : 0 ≤ N := by rw [hN]; exact tsum_nonneg hite_nonneg
  have hPwR : w R ≤ Pbarₚ' q w ω n := by rw [hsplit]; linarith [hN0]
  have hPpos : 0 < Pbarₚ' q w ω n := lt_of_lt_of_le hwRpos hPwR
  -- `1 − wpost = N / P̄(n)` (using `L_R(n) = 1`).
  have hwpost : 1 - w R * Lik q ω R n / Pbarₚ' q w ω n = N / Pbarₚ' q w ω n := by
    rw [hLikR, mul_one, eq_div_iff (ne_of_gt hPpos), sub_mul, one_mul,
        div_mul_cancel₀ _ (ne_of_gt hPpos)]
    linarith [hsplit]
  -- `N ≤ exp(−2S)`: competitor decay termwise, then `∑' w ≤ 1`.
  have hnum : N ≤ Real.exp (-2 * S) := by
    rw [hN]
    calc ∑' i, ite (i = R) 0 (w i * Lik q ω i n)
        ≤ ∑' i, w i * Real.exp (-2 * S) := by
          refine Summable.tsum_le_tsum (fun i => ?_) hsumite (hsumw.mul_right _)
          by_cases hiR : i = R
          · rw [if_pos hiR]; exact mul_nonneg (hw i) (Real.exp_pos _).le
          · rw [if_neg hiR]
            have hdecay : Lik q ω i n ≤ Real.exp (-2 * S) :=
              le_trans (competitor_likelihood_decay hnn hpmf i n)
                (Real.exp_le_exp.mpr (by linarith [hsep i hiR]))
            exact mul_le_mul_of_nonneg_left hdecay (hw i)
      _ = (∑' i, w i) * Real.exp (-2 * S) := tsum_mul_right
      _ ≤ 1 * Real.exp (-2 * S) := mul_le_mul_of_nonneg_right hsumw1 (Real.exp_pos _).le
      _ = Real.exp (-2 * S) := one_mul _
  rw [hwpost]
  calc N / Pbarₚ' q w ω n
      ≤ Real.exp (-2 * S) / w R := div_le_div₀ (Real.exp_pos _).le hnum hwRpos hPwR
    _ = (2 : ℝ) ^ (k : ℝ) * Real.exp (-2 * S) := by
        rw [hwR, Real.rpow_neg (by norm_num), div_eq_mul_inv, inv_inv, mul_comm]

/-- **Theorem 3.1 (unconditional, realizable-deterministic) — countable hypothesis class.** The
countable analogue of `DeterministicDiscovery.deterministic_discovery`, over the Kolmogorov-weighted
prior `w(R') = 2^{−K(R')}` of §1.1 (`Summable w`, `∑' w ≤ 1`). For per-step separation `ε₀` and
`n ≥ T_discover = (K(R)·ln 2 + ln(2/δ)) / (2 ε₀)`, the prequential posterior concentrates on the true
rule: `wpost = w R · Lik R n / P̄(n) ≥ 1 − δ/2`. Hypotheses are **only** the model + realizability +
separation — no Grünwald–Mehta, no Markov, no posterior-of-close. -/
theorem countable_discovery (hnn : ∀ i s x, 0 ≤ q i s x) (hpmf : ∀ i s, ∑ x, q i s x = 1)
    (hw : ∀ i, 0 ≤ w i) (k : ℕ) (hwR : w R = (2 : ℝ) ^ (-(k : ℝ)))
    (hsumw : Summable w) (hsumw1 : ∑' i, w i ≤ 1)
    (hreal : ∀ s, q R s (ω s) = 1) (δ ε₀ : ℝ) (hδ : 0 < δ) (hε : 0 < ε₀) (n : ℕ)
    (hsep : ∀ i, i ≠ R → ∀ t ∈ Finset.range n,
      ε₀ ≤ sqHellinger (fun x => if x = ω t then 1 else 0) (q i t))
    (hT : ((k : ℝ) * Real.log 2 + Real.log (2 / δ)) / (2 * ε₀) ≤ (n : ℝ)) :
    1 - δ / 2 ≤ w R * Lik q ω R n / Pbarₚ' q w ω n := by
  -- per-step separation ⇒ cumulative `≥ n·ε₀`.
  have hcum : ∀ i, i ≠ R → (n : ℝ) * ε₀
      ≤ ∑ t ∈ Finset.range n, sqHellinger (fun x => if x = ω t then 1 else 0) (q i t) := by
    intro i hiR
    calc (n : ℝ) * ε₀ = ∑ _t ∈ Finset.range n, ε₀ := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ ≤ ∑ t ∈ Finset.range n, sqHellinger (fun x => if x = ω t then 1 else 0) (q i t) :=
          Finset.sum_le_sum (fun t ht => hsep i hiR t ht)
  have hpost :=
    countable_posterior_lower_bound hnn hpmf hw k hwR hsumw hsumw1 hreal n ((n : ℝ) * ε₀) hcum
  have hbound : (2 : ℝ) ^ (k : ℝ) * Real.exp (-2 * ((n : ℝ) * ε₀)) ≤ δ / 2 := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2), ← Real.exp_add,
        show δ / 2 = Real.exp (Real.log (δ / 2)) from (Real.exp_log (by positivity)).symm]
    apply Real.exp_le_exp.mpr
    have h2 := (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * ε₀)).mp hT
    have hlog : Real.log (δ / 2) = - Real.log (2 / δ) := by
      rw [Real.log_div (ne_of_gt hδ) (by norm_num), Real.log_div (by norm_num) (ne_of_gt hδ)]; ring
    rw [hlog]; nlinarith [h2]
  linarith [hpost, hbound]

end CountableDiscovery
