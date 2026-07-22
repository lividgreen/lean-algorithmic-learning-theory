/-
Copyright (c) 2026 Mykola Palamarchuk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mykola Palamarchuk
-/
import ALT.DeterministicDiscovery

-- Formal-check file, not Mathlib-destined: opt out of the house-style linters.
set_option linter.style.header false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

/-!
# Genuine ε₀-Hellinger + the ε₀→query-separation bridge — [Discovery] §3.3 (FV-15)

Provenance: [Discovery] §3.3 (ε₀ as the squared-Hellinger separation, the
inherited `1/ε₀` factor) and [SQ] §3 / Appendix A Claim 1 (the SQ mean-gap `> 2τ` separation
rule). Two micro-targets, both routed in-house on `BayesRedundancy.sqHellinger`:

## Target A — ε₀ as a GENUINE Hellinger quantity
Where `EpsilonZeroBound.eps0 = M.inf' hM sep` carries an ABSTRACT real `sep : ι → ℝ` (the
measure-theoretic Hellinger deferred, FV-8), here `sep` is *instantiated* with the real
`sqHellinger`, and the positive-definiteness the abstract route could not state is now proved:

* `sqHellinger_pos_of_ne` — for finite nonneg `p ≠ q`, `0 < sqHellinger p q` (square-root injectivity,
  pointwise). This is the fact `EpsilonZeroBound.eps0_pos` had to *assume* as `0 < sep i`.
* `eps0H M hM truth P := M.inf' hM (fun i => sqHellinger truth (P i))` — ε₀ instantiated: the least
  squared-Hellinger separation of the truth's predictive pmf from each competitor's, over the class.
  `eps0H_pos` (from `sqHellinger_pos_of_ne`, under pairwise-distinctness — no assumed `0 < sep`),
  `eps0H_le` (`ε₀ ≤` each competitor's separation, `Finset.inf'_le`).
* `hsep_of_eps0H` — the reconnection to `DeterministicDiscovery.deterministic_discovery`'s `hsep`
  shape: a per-step `eps0H`-floor `ε₀ ≤ eps0H (univ.erase R) … (δ_{ω t}) (q · t)` at every step
  discharges the per-instance `∀ i ≠ R, ∀ t, ε₀ ≤ sqHellinger (δ_{ω t}) (q i t)` (in the
  realizable-deterministic case the truth's step-`t` pmf IS the point mass `δ_{ω t}`). `discovery_of_eps0H`
  then feeds it straight into Theorem 3.1 — so `eps0H` genuinely drives discovery, not merely mirrors
  the shape of `eps0`.

`EpsilonZeroBound.eps0` is UNTOUCHED (its FV-8 guards stay intact); `eps0H` supersedes it by
instantiation.

## Target B — the ε₀ → query-separation bridge ([SQ] §3 / App A grounding)
The chain `squared-Hellinger ≥ ε₀  ⟹  a [−1,1] query with mean gap ≥ 2·ε₀`:

* `tv p q := (1/2)·∑ₓ |p x − q x|` (total variation) and `sqHellinger_le_tv` — `D_H² ≤ TV`, the
  pointwise `(√a − √b)² ≤ |a − b|`.
* `exists_separating_query` — the sign-set query realizes the TV gap: a `[−1,1]` query with
  `2·TV ≤ |E_p[φ] − E_q[φ]|` (equality holds; `≤` suffices).
* `identifiable_of_sqHellinger` — the bridge: `sqHellinger p q ≥ ε₀ ⟹ ∃` a `[−1,1]` query with
  `mean gap ≥ 2·ε₀`. Hence `separates_of_sqHellinger`: distinct rules with squared-Hellinger
  separation `ε₀` are **2τ-identifiable for any `τ < ε₀`** — i.e.
  `SQObjects.Separates (2τ) meanAns φ p q` (`2τ < |meanAns φ p − meanAns φ q|`), stated in FV-J/FV-L's
  answer-functional vocabulary via the local `meanAns φ p = E_p[φ] = ∑ₓ p x·φ x`.

## FIDELITY BOUNDARY — the √ε₀ ("mean-level") reading vs. the certified ε₀
[SQ]'s Remark on ε₀ (§4) and Appendix A Claim 1 match the SQ tolerance as `τ ≲ √ε₀`
("mean-level"), and read the resulting sample factor as `1/τ² ≈ 1/ε₀`. **This bridge certifies
identifiability only at `τ < ε₀`** — the guaranteed mean gap is `2·ε₀`, not `2·√ε₀` — because the
only *lower* bound available from squared Hellinger is `TV ≥ D_H² = ε₀` (`sqHellinger_le_tv`). The
`√ε₀` scale is the OTHER direction, `TV ≤ √2·√(D_H²)` (an *upper* bound on TV), which coincides with
the TV scale only in the local / small-perturbation regime `TV ≈ √(D_H²)`; it is NOT derivable from
`D_H² ≥ ε₀` in general (e.g. one pmf placing ≈0 mass where the other places `ε` gives `TV ≈ D_H² ≈ ε`,
so `mean gap ≈ 2ε₀`, quadratically below `√ε₀`). So the `τ ≲ √ε₀` matching — and the `1/ε₀` sample
factor it yields — genuinely rests on a **mean-level separation assumption**, not on the
squared-Hellinger `ε₀` alone. From `ε₀` alone the honest certified matching is `τ < ε₀` (sample
factor `1/ε₀²`). Everything below is proved at the honest `2·ε₀` / `τ < ε₀` scale; the papers' `√ε₀`
reading is stated with exactly that mean-level qualifier ([SQ] §4, Remark on ε₀).

Everything is elementary (Mathlib calculus + `Finset`); no `sorry`.
-/

namespace HellingerBridge

open scoped BigOperators
open BayesRedundancy DeterministicDiscovery

/-! ## Target A — ε₀ as a genuine Hellinger quantity -/

/-- **Positive-definiteness of squared Hellinger.** For finite nonnegative `p ≠ q`,
`0 < sqHellinger p q`. This is what the abstract-`sep` route (`EpsilonZeroBound.eps0_pos`) had to
*assume* (`0 < sep i`): a competitor with a distinct predictive pmf is strictly separated. Proof:
at a point `x₀` where `p x₀ ≠ q x₀`, square-root injectivity on `[0,∞)` gives
`√(p x₀) ≠ √(q x₀)`, so that summand `(√p − √q)²` is strictly positive; the rest are `≥ 0`. -/
theorem sqHellinger_pos_of_ne {α : Type*} [Fintype α] (p q : α → ℝ)
    (hp : ∀ x, 0 ≤ p x) (hq : ∀ x, 0 ≤ q x) (hpq : p ≠ q) :
    0 < sqHellinger p q := by
  obtain ⟨x₀, hx₀⟩ := Function.ne_iff.mp hpq
  unfold sqHellinger
  refine mul_pos (by norm_num) ?_
  refine Finset.sum_pos' (fun x _ => sq_nonneg _) ⟨x₀, Finset.mem_univ x₀, ?_⟩
  have hs : Real.sqrt (p x₀) ≠ Real.sqrt (q x₀) := by
    rw [Ne, Real.sqrt_inj (hp x₀) (hq x₀)]; exact hx₀
  have hne : Real.sqrt (p x₀) - Real.sqrt (q x₀) ≠ 0 := sub_ne_zero.mpr hs
  exact lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hne))

/-- **ε₀ as a genuine squared-Hellinger quantity** (mirrors `EpsilonZeroBound.eps0`'s `Finset.inf'`
shape, truth-vs-competitor): the least squared-Hellinger separation of the truth's predictive pmf
`truth` from each competitor's `P i`, over the finite nonempty class `M`. Where `eps0` carries an
abstract `sep : ι → ℝ`, this instantiates `sep i := sqHellinger truth (P i)`. -/
noncomputable def eps0H {α ι : Type*} [Fintype α] (M : Finset ι) (hM : M.Nonempty)
    (truth : α → ℝ) (P : ι → α → ℝ) : ℝ :=
  M.inf' hM (fun i => sqHellinger truth (P i))

/-- `eps0H > 0` under **pairwise-distinctness** of the predictive pmfs — the genuine
positive-definiteness (`sqHellinger_pos_of_ne`), replacing `eps0_pos`'s assumed `0 < sep i`. -/
theorem eps0H_pos {α ι : Type*} [Fintype α] {M : Finset ι} (hM : M.Nonempty)
    {truth : α → ℝ} {P : ι → α → ℝ} (hnnT : ∀ x, 0 ≤ truth x) (hnnP : ∀ i x, 0 ≤ P i x)
    (hdist : ∀ i ∈ M, truth ≠ P i) :
    0 < eps0H M hM truth P :=
  (Finset.lt_inf'_iff hM).mpr
    (fun i hi => sqHellinger_pos_of_ne truth (P i) hnnT (hnnP i) (hdist i hi))

/-- `eps0H` is at most every competitor's squared-Hellinger separation (`Finset.inf'_le`). -/
theorem eps0H_le {α ι : Type*} [Fintype α] {M : Finset ι} (hM : M.Nonempty)
    {truth : α → ℝ} {P : ι → α → ℝ} {i : ι} (hi : i ∈ M) :
    eps0H M hM truth P ≤ sqHellinger truth (P i) :=
  Finset.inf'_le _ hi

/-- **Reconnection to `DeterministicDiscovery`.** A per-step `eps0H`-floor over the competitors
(`univ.erase R`), with the truth's step-`t` pmf the realized point mass `δ_{ω t}`, discharges the
per-instance separation hypothesis `hsep` of `deterministic_discovery` — the honest form: the
per-step floor `ε₀ ≤ eps0H … (δ_{ω t}) (q · t)` at every `t < n` gives
`∀ i ≠ R, ∀ t < n, ε₀ ≤ sqHellinger (δ_{ω t}) (q i t)`. -/
theorem hsep_of_eps0H {A ι : Type*} [Fintype A] [DecidableEq A] [Fintype ι] [DecidableEq ι]
    (q : ι → ℕ → A → ℝ) (ω : ℕ → A) (R : ι) (ε₀ : ℝ) (n : ℕ)
    (hne : (Finset.univ.erase R).Nonempty)
    (hfloor : ∀ t ∈ Finset.range n,
      ε₀ ≤ eps0H (Finset.univ.erase R) hne
        (fun x => if x = ω t then (1 : ℝ) else 0) (fun i => q i t)) :
    ∀ i, i ≠ R → ∀ t ∈ Finset.range n,
      ε₀ ≤ sqHellinger (fun x => if x = ω t then (1 : ℝ) else 0) (q i t) := by
  intro i hi t ht
  exact le_trans (hfloor t ht) (eps0H_le hne (Finset.mem_erase.mpr ⟨hi, Finset.mem_univ i⟩))

/-- **`eps0H` drives Theorem 3.1.** With a per-step `eps0H`-floor `ε₀` (via `hsep_of_eps0H`) and
`n ≥ T_discover`, the prequential posterior concentrates on the true rule: `wpost ≥ 1 − δ/2`. This
is `deterministic_discovery` with its `hsep` supplied by the genuine ε₀-Hellinger floor. -/
theorem discovery_of_eps0H {A ι : Type*} [Fintype A] [DecidableEq A] [Fintype ι] [DecidableEq ι]
    {q : ι → ℕ → A → ℝ} {w : ι → ℝ} {ω : ℕ → A} {R : ι}
    (hnn : ∀ i s x, 0 ≤ q i s x) (hpmf : ∀ i s, ∑ x, q i s x = 1)
    (hw : ∀ i, 0 ≤ w i) (k : ℕ) (hwR : w R = (2 : ℝ) ^ (-(k : ℝ))) (hsumw : ∑ i, w i ≤ 1)
    (hreal : ∀ s, q R s (ω s) = 1) (δ ε₀ : ℝ) (hδ : 0 < δ) (hε : 0 < ε₀) (n : ℕ)
    (hne : (Finset.univ.erase R).Nonempty)
    (hfloor : ∀ t ∈ Finset.range n,
      ε₀ ≤ eps0H (Finset.univ.erase R) hne
        (fun x => if x = ω t then (1 : ℝ) else 0) (fun i => q i t))
    (hT : ((k : ℝ) * Real.log 2 + Real.log (2 / δ)) / (2 * ε₀) ≤ (n : ℝ)) :
    1 - δ / 2 ≤ w R * Lik q ω R n / Pbarₚ q w ω n :=
  deterministic_discovery hnn hpmf hw k hwR hsumw hreal δ ε₀ hδ hε n
    (hsep_of_eps0H q ω R ε₀ n hne hfloor) hT

/-! ## Target B — the ε₀ → query-separation bridge -/

/-- **Total variation** of two finite "distributions": `TV(p,q) = (1/2)·∑ₓ |p x − q x|`. -/
noncomputable def tv {α : Type*} [Fintype α] (p q : α → ℝ) : ℝ :=
  (1 / 2) * ∑ x, |p x - q x|

/-- **Squared Hellinger dominated by TV.** `D_H²(p,q) ≤ TV(p,q)` for finite nonnegative `p, q` — the
pointwise `(√a − √b)² ≤ |a − b|` (`|a − b| = |√a − √b|·(√a + √b) ≥ |√a − √b|² = (√a − √b)²`, the
triangle bound `|√a − √b| ≤ √a + √b`). This is the *lower* bound `TV ≥ D_H²` used by the bridge. -/
theorem sqHellinger_le_tv {α : Type*} [Fintype α] (p q : α → ℝ)
    (hp : ∀ x, 0 ≤ p x) (hq : ∀ x, 0 ≤ q x) :
    sqHellinger p q ≤ tv p q := by
  unfold sqHellinger tv
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
  refine Finset.sum_le_sum (fun x _ => ?_)
  have ha : Real.sqrt (p x) ^ 2 = p x := Real.sq_sqrt (hp x)
  have hb : Real.sqrt (q x) ^ 2 = q x := Real.sq_sqrt (hq x)
  rcases le_total (q x) (p x) with h | h
  · rw [abs_of_nonneg (by linarith)]
    have hsqle : Real.sqrt (q x) ≤ Real.sqrt (p x) := Real.sqrt_le_sqrt h
    nlinarith [mul_nonneg (Real.sqrt_nonneg (q x)) (sub_nonneg.mpr hsqle), ha, hb]
  · rw [abs_of_nonpos (by linarith), neg_sub]
    have hsqle : Real.sqrt (p x) ≤ Real.sqrt (q x) := Real.sqrt_le_sqrt h
    nlinarith [mul_nonneg (Real.sqrt_nonneg (p x)) (sub_nonneg.mpr hsqle), ha, hb]

/-- **The sign-set query realizes the TV gap.** There is a `[−1,1]`-valued query `φ` with
`2·TV(p,q) ≤ |E_p[φ] − E_q[φ]|` — take `φ = sign(p − q)`, for which the gap equals `∑ₓ|p x − q x| =
2·TV` exactly (`≤` suffices). This is `TV = (1/2)·sup_{|φ|≤1}|∑(p−q)φ|` in the direction we need. -/
theorem exists_separating_query {α : Type*} [Fintype α] (p q : α → ℝ) :
    ∃ φ : α → ℝ, (∀ x, |φ x| ≤ 1) ∧
      2 * tv p q ≤ |∑ x, p x * φ x - ∑ x, q x * φ x| := by
  refine ⟨fun x => if 0 ≤ p x - q x then (1 : ℝ) else -1,
    fun x => by dsimp only; split_ifs <;> norm_num, ?_⟩
  have hpt : ∀ x, (p x - q x) * (if 0 ≤ p x - q x then (1 : ℝ) else -1) = |p x - q x| := by
    intro x; split_ifs with h
    · rw [mul_one, abs_of_nonneg h]
    · rw [mul_neg_one, abs_of_neg (not_le.mp h)]
  have hgap : (∑ x, p x * (if 0 ≤ p x - q x then (1 : ℝ) else -1))
        - (∑ x, q x * (if 0 ≤ p x - q x then (1 : ℝ) else -1)) = ∑ x, |p x - q x| := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun x _ => by rw [← sub_mul]; exact hpt x)
  have hpos : (0 : ℝ) ≤ ∑ x, |p x - q x| := Finset.sum_nonneg (fun x _ => abs_nonneg _)
  have htv2 : 2 * tv p q = ∑ x, |p x - q x| := by unfold tv; ring
  rw [hgap, abs_of_nonneg hpos]; linarith [htv2]

/-- **The bridge.** Finite nonnegative pmfs with `sqHellinger p q ≥ ε₀` admit a `[−1,1]` query whose
mean gap is `≥ 2·ε₀`: `D_H² ≥ ε₀ ⟹ TV ≥ ε₀` (`sqHellinger_le_tv`) ⟹ the sign query's `2·TV`-gap is
`≥ 2·ε₀`. NOTE (fidelity): the certified gap is `2·ε₀`, at the squared-Hellinger scale — NOT the
`2·√ε₀` a "mean-level" reading would assume; see the module boundary note. -/
theorem identifiable_of_sqHellinger {α : Type*} [Fintype α] (p q : α → ℝ)
    (hp : ∀ x, 0 ≤ p x) (hq : ∀ x, 0 ≤ q x) (ε₀ : ℝ) (hsep : ε₀ ≤ sqHellinger p q) :
    ∃ φ : α → ℝ, (∀ x, |φ x| ≤ 1) ∧
      2 * ε₀ ≤ |∑ x, p x * φ x - ∑ x, q x * φ x| := by
  obtain ⟨φ, hφ, hgap⟩ := exists_separating_query p q
  have htv : ε₀ ≤ tv p q := le_trans hsep (sqHellinger_le_tv p q hp hq)
  exact ⟨φ, hφ, by linarith [hgap]⟩

/-- The mean-level answer functional `meanAns φ p = E_p[φ] = ∑ₓ p x · φ x`. Instantiates
`SQObjects.ans : Q → ι → ℝ` with queries `Q = α → ℝ` and candidate pmfs `ι = α → ℝ`. -/
noncomputable def meanAns {α : Type*} [Fintype α] (φ p : α → ℝ) : ℝ := ∑ x, p x * φ x

/-- **Identifiability in FV-J/FV-L's vocabulary.** Distinct rules with squared-Hellinger separation
`ε₀` are `2τ`-identifiable for any `τ < ε₀`: there is a `[−1,1]` query `φ` with
`2τ < |meanAns φ p − meanAns φ q|` — i.e. `SQObjects.Separates (2*τ) meanAns φ p q` (definitionally,
since `Separates c ans φ i j := c < |ans φ i − ans φ j|`). The honest `τ < ε₀` threshold: the
guaranteed gap is `2ε₀`, so `2τ < 2ε₀ ≤` gap. (A `τ ≲ √ε₀` claim would need the mean-level
assumption; see the boundary note.) -/
theorem separates_of_sqHellinger {α : Type*} [Fintype α] (p q : α → ℝ)
    (hp : ∀ x, 0 ≤ p x) (hq : ∀ x, 0 ≤ q x) (ε₀ τ : ℝ)
    (hsep : ε₀ ≤ sqHellinger p q) (hτ : τ < ε₀) :
    ∃ φ : α → ℝ, (∀ x, |φ x| ≤ 1) ∧
      2 * τ < |meanAns φ p - meanAns φ q| := by
  obtain ⟨φ, hφ, hgap⟩ := identifiable_of_sqHellinger p q hp hq ε₀ hsep
  refine ⟨φ, hφ, ?_⟩
  unfold meanAns
  linarith [hgap]

end HellingerBridge
