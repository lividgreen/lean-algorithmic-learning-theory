/-
Copyright (c) 2026 Mykola Palamarchuk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mykola Palamarchuk
-/
import Mathlib

-- Formal-check file, not Mathlib-destined: opt out of the house-style linters.
set_option linter.style.header false
set_option linter.style.longLine false

/-!
# Finite-discrete Shannon information theory — scaffolding toward Cheng's Theorem 4

Provenance: the information-theoretic core of `Cheng, R. (2026)` Theorem 4 ([Discovery] §4 retention),
re-checked in `ALT/ChengCCC.lean`. That file machine-checks the misidentification / forgetting
lower bounds *modulo* two named hypotheses — the **data-processing inequality** (`I(T;θ) ≤ C_ctx`)
and **Fano's inequality** (`P_e ≥ (H(T|θ) − 1)/log(K−1)`). Mathlib has neither (only
`Real.negMulLog`, the binary-entropy *function*, and topological entropy), so discharging them
requires building a small finite-discrete information-theory library. This file builds it bottom-up.

## Status (honest)
Done here (all `sorry`-free):
* the entropy definition and its nonnegativity for a pmf (`entropy`, `entropy_nonneg`);
* **mutual information** of a joint pmf and its **nonnegativity** (`mutualInfo`, `mutualInfo_nonneg`),
  via the finite Gibbs inequality (`gibbs_term`, from `Real.log_le_sub_one_of_pos`);
* **joint/conditional entropy** and the entropy form of MI — `I(X;Y) = H(X) − H(X|Y)`
  (`Hjoint`, `condEntropy`, `mutualInfo_eq_entropy`, `mutualInfo_eq_sub_condEntropy`): this
  **discharges the `hCond` identity** of `ChengCCC.misid_lower_bound`;
* **conditional mutual information** `I(X;Z|Y)`, `I(X;Y|Z)` and their **nonnegativity**
  (`condMutualInfo`, `condMutualInfo_nonneg`, `condMutualInfoZ`, `condMutualInfoZ_nonneg`);
* the two **chain-rule halves** `I(X;Y)+I(X;Z|Y) = I(X;(Y,Z)) = I(X;Z)+I(X;Y|Z)`
  (`mi_add_condMutualInfo`, `mi_add_condMutualInfoZ`) and the Markov-zero step
  (`MarkovCI`, `markov_condMutualInfo_zero`);
* the **data-processing inequality** `I(X;Z) ≤ I(X;Y)` for a Markov chain `X → Y → Z`
  (`dataProcessing`): this is the rigorous content **discharging `hDPI`** at the chain `T → c → θ`;
* **Fano's inequality** for a decoder `g : β → α` with error probability `Pe`: the core bound
  `H(X|Y) ≤ log 2 + Pe·log(K−1)` (`condEntropy_le_log2`) and the rearranged
  `(condEntropy μ − 1)/log(K−1) ≤ Pe` (`fano'`) — this is exactly **`ChengCCC`'s `hFano`**. The
  single analytic input is the unnormalised max-entropy bound `entropy_masses_le` (finite Gibbs),
  used both for the `K−1` error symbols and (via `negMulLog_add_le`) the binary split.

**Not yet done** (the remaining Mathlib-gap frontier): the *tight* Fano constant
`Real.binEntropy Pe` (≤ `log 2`) in place of `log 2` — that refinement needs Jensen on the concavity
of `binEntropy` (and a per-`y` normalisation); the looser `log 2` is all `fano'`/`ChengCCC` consume.
`ChengCCC`'s abstract arithmetic skeletons (`misid_lower_bound`, `forgetting_lower_bound`) still take
Fano/DPI/`hCond` as explicit hypotheses, but the wiring IS done: `cheng_misid_bound_discharged`
and `cheng_forgetting_bound_discharged` discharge all three against these theorems for the Markov
chain `T → c → θ`, leaving only the modelling setup (and, for forgetting, Cheng's informal Step-4
link `hConn`). No `sorry` is used; missing results are simply absent.
-/

namespace FiniteInfoTheory

open scoped BigOperators

variable {α : Type*} [Fintype α]

/-- Shannon entropy of a pmf `p : α → ℝ` in natural-log units: `H(p) = ∑ a, negMulLog (p a)`,
where `negMulLog x = -x * log x`. (Mathlib has `Real.negMulLog` and its analytic API, but not the
random-variable entropy/mutual-information layer this builds toward.) -/
noncomputable def entropy (p : α → ℝ) : ℝ := ∑ a, Real.negMulLog (p a)

/-- Entropy is nonnegative for any pmf valued in `[0,1]` (each summand `negMulLog (p a) ≥ 0`). -/
theorem entropy_nonneg {p : α → ℝ} (h0 : ∀ a, 0 ≤ p a) (h1 : ∀ a, p a ≤ 1) :
    0 ≤ entropy p := by
  refine Finset.sum_nonneg (fun a _ => ?_)
  exact Real.negMulLog_nonneg (h0 a) (h1 a)

/-! ## Mutual information of a joint pmf, and its nonnegativity (finite Gibbs)

A joint distribution of two finite random variables is a function `μ : α → β → ℝ` with
`μ ≥ 0` and `∑_{a,b} μ(a,b) = 1`. Its marginals are `μ₁(a) = ∑_b μ(a,b)` and `μ₂(b) = ∑_a μ(a,b)`,
and the mutual information is the Kullback–Leibler divergence of `μ` from the product `μ₁ ⊗ μ₂`. -/

variable {β : Type*} [Fintype β]

/-- First marginal `μ₁(a) = ∑_b μ(a,b)` of a joint pmf `μ : α → β → ℝ`. -/
noncomputable def marg₁ (μ : α → β → ℝ) (a : α) : ℝ := ∑ b, μ a b

/-- Second marginal `μ₂(b) = ∑_a μ(a,b)` of a joint pmf `μ : α → β → ℝ`. -/
noncomputable def marg₂ (μ : α → β → ℝ) (b : β) : ℝ := ∑ a, μ a b

/-- Shannon mutual information of a joint pmf `μ`, in nats:
`I(μ) = ∑_{a,b} μ(a,b) · log( μ(a,b) / (μ₁(a)·μ₂(b)) )` — the KL divergence `D(μ ‖ μ₁ ⊗ μ₂)`. -/
noncomputable def mutualInfo (μ : α → β → ℝ) : ℝ :=
  ∑ a, ∑ b, μ a b * Real.log (μ a b / (marg₁ μ a * marg₂ μ b))

/-- Per-term Gibbs bound `x − r ≤ x · log(x / r)`, valid for `x ≥ 0`, `r ≥ 0`, with the proviso
that `r > 0` whenever `x > 0` (so `log` is applied to a positive argument where it matters).
This is the single analytic fact behind nonnegativity of KL divergence / mutual information. -/
theorem gibbs_term {x r : ℝ} (hx : 0 ≤ x) (hr : 0 ≤ r) (hxr : 0 < x → 0 < r) :
    x - r ≤ x * Real.log (x / r) := by
  rcases eq_or_lt_of_le hx with hx0 | hx0
  · -- x = 0: LHS = -r ≤ 0 = RHS.
    rw [← hx0]; simp only [zero_div, zero_mul, zero_sub]; linarith
  · -- x > 0, hence r > 0.
    have hr0 : 0 < r := hxr hx0
    have hkey : Real.log (r / x) ≤ r / x - 1 := Real.log_le_sub_one_of_pos (by positivity)
    have hneg : Real.log (x / r) = - Real.log (r / x) := by
      rw [← Real.log_inv, inv_div]
    have hmul : x * (r / x) = r := by field_simp
    rw [hneg]
    nlinarith [mul_le_mul_of_nonneg_left hkey (le_of_lt hx0), hmul]

/-- **Mutual information is nonnegative.** For any joint pmf `μ` (nonnegative, summing to `1`),
`I(μ) ≥ 0`. Proof: the finite Gibbs/log-sum inequality bounds each summand below by
`μ(a,b) − μ₁(a)·μ₂(b)`, whose total is `1 − 1 = 0`. This is the discharged nonnegativity half of
the data-processing inequality interface required by `ChengCCC`. -/
theorem mutualInfo_nonneg (μ : α → β → ℝ) (hnn : ∀ a b, 0 ≤ μ a b)
    (hsum : ∑ a, ∑ b, μ a b = 1) : 0 ≤ mutualInfo μ := by
  have hp : ∀ a, 0 ≤ marg₁ μ a := fun a => Finset.sum_nonneg (fun b _ => hnn a b)
  have hq : ∀ b, 0 ≤ marg₂ μ b := fun b => Finset.sum_nonneg (fun a _ => hnn a b)
  -- Per-term lower bound via Gibbs.
  have hterm : ∀ a b,
      μ a b - marg₁ μ a * marg₂ μ b ≤ μ a b * Real.log (μ a b / (marg₁ μ a * marg₂ μ b)) := by
    intro a b
    refine gibbs_term (hnn a b) (mul_nonneg (hp a) (hq b)) (fun hpos => ?_)
    have h1 : μ a b ≤ marg₁ μ a := Finset.single_le_sum (fun i _ => hnn a i) (Finset.mem_univ b)
    have h2 : μ a b ≤ marg₂ μ b := Finset.single_le_sum (fun i _ => hnn i b) (Finset.mem_univ a)
    exact mul_pos (lt_of_lt_of_le hpos h1) (lt_of_lt_of_le hpos h2)
  -- Sum the per-term bound.
  have hsumbound :
      ∑ a, ∑ b, (μ a b - marg₁ μ a * marg₂ μ b) ≤ mutualInfo μ := by
    refine Finset.sum_le_sum (fun a _ => Finset.sum_le_sum (fun b _ => hterm a b))
  -- The lower-bound sum telescopes to 0.
  have hlhs : ∑ a, ∑ b, (μ a b - marg₁ μ a * marg₂ μ b) = 0 := by
    have hb : ∑ b, marg₂ μ b = 1 := by
      unfold marg₂; rw [Finset.sum_comm]; exact hsum
    have ha : ∑ a, marg₁ μ a = 1 := by unfold marg₁; exact hsum
    have hprod : ∑ a, ∑ b, marg₁ μ a * marg₂ μ b = 1 := by
      have : ∀ a, ∑ b, marg₁ μ a * marg₂ μ b = marg₁ μ a := by
        intro a; rw [← Finset.mul_sum, hb, mul_one]
      simp_rw [this]; exact ha
    calc ∑ a, ∑ b, (μ a b - marg₁ μ a * marg₂ μ b)
        = (∑ a, ∑ b, μ a b) - ∑ a, ∑ b, marg₁ μ a * marg₂ μ b := by
          simp_rw [Finset.sum_sub_distrib]
      _ = 1 - 1 := by rw [hsum, hprod]
      _ = 0 := by ring
  linarith [hsumbound, hlhs.ge]

/-! ## Entropy form of mutual information (the `hCond` identity)

`I(X;Y) = H(X) + H(Y) − H(X,Y) = H(X) − H(X|Y)`. This discharges the `hCond` hypothesis of
`ChengCCC.misid_lower_bound` (`condEnt = H(T) − I(T;θ)`, with `X = T`, `Y = θ`). The proof splits
`log(μ/(μ₁μ₂)) = log μ − log μ₁ − log μ₂` on the support and collapses each marginal sum; the only
hypothesis is nonnegativity `μ ≥ 0` (the identity needs no `∑ μ = 1`). -/

/-- Joint entropy `H(X,Y) = ∑_{a,b} negMulLog (μ a b)`. -/
noncomputable def Hjoint (μ : α → β → ℝ) : ℝ := ∑ a, ∑ b, Real.negMulLog (μ a b)

/-- Conditional entropy `H(X | Y) = H(X,Y) − H(Y)` (here `Y` is the second coordinate). -/
noncomputable def condEntropy (μ : α → β → ℝ) : ℝ := Hjoint μ - entropy (marg₂ μ)

/-- `∑ p·log p = −H(p)`: the entropy is minus the (signed) sum, since `negMulLog x = −(x·log x)`. -/
private lemma sum_mul_log_eq_neg_entropy (p : α → ℝ) :
    ∑ a, p a * Real.log (p a) = - entropy p := by
  unfold entropy
  simp only [Real.negMulLog_eq_neg, Finset.sum_neg_distrib, neg_neg]

/-- Two-variable version: `∑∑ μ·log μ = −H(X,Y)`. -/
private lemma sum_sum_mul_log_eq_neg_Hjoint (μ : α → β → ℝ) :
    ∑ a, ∑ b, μ a b * Real.log (μ a b) = - Hjoint μ := by
  unfold Hjoint
  simp only [Real.negMulLog_eq_neg, Finset.sum_neg_distrib, neg_neg]

/-- **Mutual information as a difference of entropies.** `I(μ) = H(X) + H(Y) − H(X,Y)`.
Needs only nonnegativity of `μ` (no normalization). -/
theorem mutualInfo_eq_entropy (μ : α → β → ℝ) (hnn : ∀ a b, 0 ≤ μ a b) :
    mutualInfo μ = entropy (marg₁ μ) + entropy (marg₂ μ) - Hjoint μ := by
  -- Per-term split of the log, valid everywhere thanks to the `μ a b` factor at the zeros.
  have hsplit : ∀ a b, μ a b * Real.log (μ a b / (marg₁ μ a * marg₂ μ b))
      = μ a b * Real.log (μ a b) - μ a b * Real.log (marg₁ μ a) - μ a b * Real.log (marg₂ μ b) := by
    intro a b
    rcases eq_or_lt_of_le (hnn a b) with h0 | hpos
    · rw [← h0]; ring
    · have h1 : 0 < marg₁ μ a :=
        lt_of_lt_of_le hpos (Finset.single_le_sum (fun i _ => hnn a i) (Finset.mem_univ b))
      have h2 : 0 < marg₂ μ b :=
        lt_of_lt_of_le hpos (Finset.single_le_sum (fun i _ => hnn i b) (Finset.mem_univ a))
      rw [Real.log_div (ne_of_gt hpos) (ne_of_gt (mul_pos h1 h2)),
          Real.log_mul (ne_of_gt h1) (ne_of_gt h2)]
      ring
  have S1 : ∑ a, ∑ b, μ a b * Real.log (μ a b) = - Hjoint μ :=
    sum_sum_mul_log_eq_neg_Hjoint μ
  have S2 : ∑ a, ∑ b, μ a b * Real.log (marg₁ μ a) = - entropy (marg₁ μ) := by
    have h : ∀ a, ∑ b, μ a b * Real.log (marg₁ μ a) = (∑ b, μ a b) * Real.log (marg₁ μ a) :=
      fun a => by rw [Finset.sum_mul]
    simp_rw [h]; exact sum_mul_log_eq_neg_entropy (marg₁ μ)
  have S3 : ∑ a, ∑ b, μ a b * Real.log (marg₂ μ b) = - entropy (marg₂ μ) := by
    rw [Finset.sum_comm]
    have h : ∀ b, ∑ a, μ a b * Real.log (marg₂ μ b) = (∑ a, μ a b) * Real.log (marg₂ μ b) :=
      fun b => by rw [Finset.sum_mul]
    simp_rw [h]; exact sum_mul_log_eq_neg_entropy (marg₂ μ)
  have hdistr :
      ∑ a, ∑ b, (μ a b * Real.log (μ a b) - μ a b * Real.log (marg₁ μ a)
          - μ a b * Real.log (marg₂ μ b))
        = (∑ a, ∑ b, μ a b * Real.log (μ a b)) - (∑ a, ∑ b, μ a b * Real.log (marg₁ μ a))
          - ∑ a, ∑ b, μ a b * Real.log (marg₂ μ b) := by
    simp_rw [Finset.sum_sub_distrib]
  unfold mutualInfo
  simp_rw [hsplit]
  rw [hdistr, S1, S2, S3]; ring

/-- **Mutual information as entropy minus conditional entropy:** `I(X;Y) = H(X) − H(X|Y)`.
This is exactly the `hCond` identity (`condEnt = H(T) − I(T;θ)` rearranged). -/
theorem mutualInfo_eq_sub_condEntropy (μ : α → β → ℝ) (hnn : ∀ a b, 0 ≤ μ a b) :
    mutualInfo μ = entropy (marg₁ μ) - condEntropy μ := by
  rw [mutualInfo_eq_entropy μ hnn, condEntropy]; ring

/-! ## Conditional mutual information and the data-processing inequality

For three finite variables `(X,Y,Z)` with joint pmf `ν : α → β → γ → ℝ`, the conditional mutual
information `I(X;Z | Y)` is nonnegative, and vanishes under the Markov condition `X → Y → Z`
(conditional independence of `X` and `Z` given `Y`). These are the ingredients of the
data-processing inequality `I(X;Z) ≤ I(X;Y)` (attempted below). The proofs reuse `gibbs_term`. -/

variable {γ : Type*} [Fintype γ]

/-- `p(x,y) = ∑_z ν(x,y,z)`. -/
noncomputable def margXY (ν : α → β → γ → ℝ) (a : α) (b : β) : ℝ := ∑ c, ν a b c

/-- `p(y,z) = ∑_x ν(x,y,z)`. -/
noncomputable def margYZ (ν : α → β → γ → ℝ) (b : β) (c : γ) : ℝ := ∑ a, ν a b c

/-- `p(y) = ∑_{x,z} ν(x,y,z)`. -/
noncomputable def margY (ν : α → β → γ → ℝ) (b : β) : ℝ := ∑ a, ∑ c, ν a b c

/-- `p(x) = ∑_{y,z} ν(x,y,z)`. -/
noncomputable def margX (ν : α → β → γ → ℝ) (a : α) : ℝ := ∑ b, ∑ c, ν a b c

/-- `p(x,z) = ∑_y ν(x,y,z)`. -/
noncomputable def margXZ (ν : α → β → γ → ℝ) (a : α) (c : γ) : ℝ := ∑ b, ν a b c

/-- `p(z) = ∑_{x,y} ν(x,y,z)`. -/
noncomputable def margZ (ν : α → β → γ → ℝ) (c : γ) : ℝ := ∑ a, ∑ b, ν a b c

/-- Conditional mutual information `I(X;Z | Y) = ∑_{x,y,z} ν·log( ν·p(y) / (p(x,y)·p(y,z)) )`. -/
noncomputable def condMutualInfo (ν : α → β → γ → ℝ) : ℝ :=
  ∑ a, ∑ b, ∑ c, ν a b c * Real.log (ν a b c * margY ν b / (margXY ν a b * margYZ ν b c))

-- `∑_x p(x,y) = p(y)` (definitional).
omit [Fintype β] in
private lemma sum_margXY (ν : α → β → γ → ℝ) (b : β) : ∑ a, margXY ν a b = margY ν b := rfl

-- `∑_z p(y,z) = p(y)`.
omit [Fintype β] in
private lemma sum_margYZ (ν : α → β → γ → ℝ) (b : β) : ∑ c, margYZ ν b c = margY ν b := by
  unfold margYZ margY; rw [Finset.sum_comm]

/-- **Conditional mutual information is nonnegative**, `I(X;Z|Y) ≥ 0`. Per `Y`-slice this is a KL
divergence; the finite Gibbs bound makes each summand `≥ ν − p(x,y)p(y,z)/p(y)`, summing to `0`. -/
theorem condMutualInfo_nonneg (ν : α → β → γ → ℝ) (hnn : ∀ a b c, 0 ≤ ν a b c)
    (hsum : ∑ a, ∑ b, ∑ c, ν a b c = 1) : 0 ≤ condMutualInfo ν := by
  have hXYnn : ∀ a b, 0 ≤ margXY ν a b := fun a b => Finset.sum_nonneg fun c _ => hnn a b c
  have hYZnn : ∀ b c, 0 ≤ margYZ ν b c := fun b c => Finset.sum_nonneg fun a _ => hnn a b c
  have hYnn : ∀ b, 0 ≤ margY ν b :=
    fun b => Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun c _ => hnn a b c
  -- Per-term Gibbs lower bound.
  have hterm : ∀ a b c,
      ν a b c - margXY ν a b * margYZ ν b c / margY ν b
        ≤ ν a b c * Real.log (ν a b c * margY ν b / (margXY ν a b * margYZ ν b c)) := by
    intro a b c
    rcases eq_or_lt_of_le (hnn a b c) with h0 | hpos
    · rw [← h0]
      have hr : 0 ≤ margXY ν a b * margYZ ν b c / margY ν b :=
        div_nonneg (mul_nonneg (hXYnn a b) (hYZnn b c)) (hYnn b)
      simp only [zero_mul, zero_sub, zero_div]; linarith
    · have hXY : 0 < margXY ν a b :=
        lt_of_lt_of_le hpos (Finset.single_le_sum (fun c _ => hnn a b c) (Finset.mem_univ c))
      have hYZ : 0 < margYZ ν b c :=
        lt_of_lt_of_le hpos (Finset.single_le_sum (fun a _ => hnn a b c) (Finset.mem_univ a))
      have hY : 0 < margY ν b :=
        lt_of_lt_of_le hXY (Finset.single_le_sum (fun a _ => hXYnn a b) (Finset.mem_univ a))
      have harg : ν a b c * margY ν b / (margXY ν a b * margYZ ν b c)
          = ν a b c / (margXY ν a b * margYZ ν b c / margY ν b) := by
        rw [div_div_eq_mul_div]
      rw [harg]
      exact gibbs_term (le_of_lt hpos) (le_of_lt (div_pos (mul_pos hXY hYZ) hY))
        (fun _ => div_pos (mul_pos hXY hYZ) hY)
  -- Sum the bound.
  have hsumbound :
      ∑ a, ∑ b, ∑ c, (ν a b c - margXY ν a b * margYZ ν b c / margY ν b) ≤ condMutualInfo ν := by
    unfold condMutualInfo
    exact Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ =>
      Finset.sum_le_sum fun c _ => hterm a b c
  -- Per-`y` collapse of the product term.
  have hperb : ∀ b, ∑ a, ∑ c, (margXY ν a b * margYZ ν b c / margY ν b) = margY ν b := by
    intro b
    rcases eq_or_lt_of_le (hYnn b) with hY0 | hYpos
    · have hall : ∀ a, margXY ν a b = 0 := by
        intro a
        have hle : margXY ν a b ≤ margY ν b :=
          Finset.single_le_sum (fun i _ => hXYnn i b) (Finset.mem_univ a)
        exact le_antisymm (by linarith) (hXYnn a b)
      rw [← hY0]
      simp only [hall, zero_mul, zero_div, Finset.sum_const_zero]
    · have hmm : ∑ a, ∑ c, margXY ν a b * margYZ ν b c = margY ν b * margY ν b := by
        rw [← Finset.sum_mul_sum, sum_margXY, sum_margYZ]
      rw [show (∑ a, ∑ c, (margXY ν a b * margYZ ν b c / margY ν b))
            = (∑ a, ∑ c, margXY ν a b * margYZ ν b c) / margY ν b by simp_rw [← Finset.sum_div]]
      rw [hmm, mul_div_assoc, div_self hYpos.ne', mul_one]
  have hrsum : ∑ a, ∑ b, ∑ c, (margXY ν a b * margYZ ν b c / margY ν b) = 1 := by
    rw [Finset.sum_comm]
    simp_rw [hperb]
    unfold margY; rw [Finset.sum_comm]; exact hsum
  have hlhs : ∑ a, ∑ b, ∑ c, (ν a b c - margXY ν a b * margYZ ν b c / margY ν b) = 0 := by
    calc ∑ a, ∑ b, ∑ c, (ν a b c - margXY ν a b * margYZ ν b c / margY ν b)
        = (∑ a, ∑ b, ∑ c, ν a b c)
          - ∑ a, ∑ b, ∑ c, (margXY ν a b * margYZ ν b c / margY ν b) := by
          simp_rw [Finset.sum_sub_distrib]
      _ = 1 - 1 := by rw [hsum, hrsum]
      _ = 0 := by ring
  linarith [hsumbound, hlhs.ge]

/-- Markov condition `X → Y → Z`, stated as conditional independence of `X` and `Z` given `Y`:
`ν(x,y,z)·p(y) = p(x,y)·p(y,z)`. (Well-posed at `p(y)=0`: both sides vanish there.) -/
def MarkovCI (ν : α → β → γ → ℝ) : Prop :=
  ∀ a b c, ν a b c * margY ν b = margXY ν a b * margYZ ν b c

/-- **Markov ⟹ `I(X;Z|Y) = 0`.** Under the conditional-independence condition every summand's
log-argument is `1`, so the conditional mutual information vanishes. -/
theorem markov_condMutualInfo_zero (ν : α → β → γ → ℝ) (hnn : ∀ a b c, 0 ≤ ν a b c)
    (hM : MarkovCI ν) : condMutualInfo ν = 0 := by
  unfold condMutualInfo
  refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => Finset.sum_eq_zero fun c _ => ?_
  rcases eq_or_lt_of_le (hnn a b c) with h0 | hpos
  · rw [← h0, zero_mul]
  · have hXY : 0 < margXY ν a b :=
      lt_of_lt_of_le hpos (Finset.single_le_sum (fun c _ => hnn a b c) (Finset.mem_univ c))
    have hYZ : 0 < margYZ ν b c :=
      lt_of_lt_of_le hpos (Finset.single_le_sum (fun a _ => hnn a b c) (Finset.mem_univ a))
    have harg : ν a b c * margY ν b / (margXY ν a b * margYZ ν b c) = 1 := by
      rw [hM a b c]; exact div_self (ne_of_gt (mul_pos hXY hYZ))
    rw [harg, Real.log_one, mul_zero]

/-- **Chain rule, one half:** `I(X;Y) + I(X;Z|Y) = ∑_{x,y,z} ν·log( ν / (p(x)·p(y,z)) ) = I(X;(Y,Z))`.
The per-term log identity `log(p(x,y)/(p(x)p(y))) + log(ν p(y)/(p(x,y)p(y,z))) = log(ν/(p(x)p(y,z)))`
holds on the support (and trivially at the zeros). No Markov assumption. -/
theorem mi_add_condMutualInfo (ν : α → β → γ → ℝ) (hnn : ∀ a b c, 0 ≤ ν a b c) :
    mutualInfo (margXY ν) + condMutualInfo ν
      = ∑ a, ∑ b, ∑ c, ν a b c * Real.log (ν a b c / (margX ν a * margYZ ν b c)) := by
  have hXYnn : ∀ a b, 0 ≤ margXY ν a b := fun a b => Finset.sum_nonneg fun c _ => hnn a b c
  -- Lift `I(X;Y)` to a triple sum over `ν`.
  have L1 : mutualInfo (margXY ν)
      = ∑ a, ∑ b, ∑ c, ν a b c * Real.log (margXY ν a b / (margX ν a * margY ν b)) := by
    unfold mutualInfo
    refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
    change margXY ν a b * Real.log (margXY ν a b / (margX ν a * margY ν b))
        = ∑ c, ν a b c * Real.log (margXY ν a b / (margX ν a * margY ν b))
    rw [← Finset.sum_mul]
    rfl
  rw [L1, condMutualInfo, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  rcases eq_or_lt_of_le (hnn a b c) with h0 | hpos
  · rw [← h0]; simp
  · have hXY : 0 < margXY ν a b :=
      lt_of_lt_of_le hpos (Finset.single_le_sum (fun c _ => hnn a b c) (Finset.mem_univ c))
    have hYZ : 0 < margYZ ν b c :=
      lt_of_lt_of_le hpos (Finset.single_le_sum (fun a _ => hnn a b c) (Finset.mem_univ a))
    have hY : 0 < margY ν b :=
      lt_of_lt_of_le hXY (Finset.single_le_sum (fun a _ => hXYnn a b) (Finset.mem_univ a))
    have hX : 0 < margX ν a :=
      lt_of_lt_of_le hXY (Finset.single_le_sum (fun b _ => hXYnn a b) (Finset.mem_univ b))
    have hP : (0:ℝ) < margXY ν a b / (margX ν a * margY ν b) := div_pos hXY (mul_pos hX hY)
    have hQ : (0:ℝ) < ν a b c * margY ν b / (margXY ν a b * margYZ ν b c) :=
      div_pos (mul_pos hpos hY) (mul_pos hXY hYZ)
    have hPQ : margXY ν a b / (margX ν a * margY ν b)
          * (ν a b c * margY ν b / (margXY ν a b * margYZ ν b c))
        = ν a b c / (margX ν a * margYZ ν b c) := by
      field_simp
    rw [← mul_add, ← Real.log_mul hP.ne' hQ.ne', hPQ]

/-- Conditional mutual information `I(X;Y | Z)` (conditioning on the *third* variable). -/
noncomputable def condMutualInfoZ (ν : α → β → γ → ℝ) : ℝ :=
  ∑ a, ∑ b, ∑ c, ν a b c * Real.log (ν a b c * margZ ν c / (margXZ ν a c * margYZ ν b c))

-- `∑_x p(x,z) = p(z)` (definitional).
omit [Fintype γ] in
private lemma sum_margXZ (ν : α → β → γ → ℝ) (c : γ) : ∑ a, margXZ ν a c = margZ ν c := rfl

-- `∑_y p(y,z) = p(z)`.
omit [Fintype γ] in
private lemma sum_margYZ_c (ν : α → β → γ → ℝ) (c : γ) : ∑ b, margYZ ν b c = margZ ν c := by
  unfold margYZ margZ; rw [Finset.sum_comm]

/-- **`I(X;Y|Z) ≥ 0`** (same finite-Gibbs proof as `condMutualInfo_nonneg`, conditioning on `Z`). -/
theorem condMutualInfoZ_nonneg (ν : α → β → γ → ℝ) (hnn : ∀ a b c, 0 ≤ ν a b c)
    (hsum : ∑ a, ∑ b, ∑ c, ν a b c = 1) : 0 ≤ condMutualInfoZ ν := by
  have hXZnn : ∀ a c, 0 ≤ margXZ ν a c := fun a c => Finset.sum_nonneg fun b _ => hnn a b c
  have hYZnn : ∀ b c, 0 ≤ margYZ ν b c := fun b c => Finset.sum_nonneg fun a _ => hnn a b c
  have hZnn : ∀ c, 0 ≤ margZ ν c :=
    fun c => Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => hnn a b c
  have hterm : ∀ a b c,
      ν a b c - margXZ ν a c * margYZ ν b c / margZ ν c
        ≤ ν a b c * Real.log (ν a b c * margZ ν c / (margXZ ν a c * margYZ ν b c)) := by
    intro a b c
    rcases eq_or_lt_of_le (hnn a b c) with h0 | hpos
    · rw [← h0]
      have hr : 0 ≤ margXZ ν a c * margYZ ν b c / margZ ν c :=
        div_nonneg (mul_nonneg (hXZnn a c) (hYZnn b c)) (hZnn c)
      simp only [zero_mul, zero_sub, zero_div]; linarith
    · have hXZ : 0 < margXZ ν a c :=
        lt_of_lt_of_le hpos (Finset.single_le_sum (fun b _ => hnn a b c) (Finset.mem_univ b))
      have hYZ : 0 < margYZ ν b c :=
        lt_of_lt_of_le hpos (Finset.single_le_sum (fun a _ => hnn a b c) (Finset.mem_univ a))
      have hZ : 0 < margZ ν c :=
        lt_of_lt_of_le hXZ (Finset.single_le_sum (fun a _ => hXZnn a c) (Finset.mem_univ a))
      have harg : ν a b c * margZ ν c / (margXZ ν a c * margYZ ν b c)
          = ν a b c / (margXZ ν a c * margYZ ν b c / margZ ν c) := by rw [div_div_eq_mul_div]
      rw [harg]
      exact gibbs_term (le_of_lt hpos) (le_of_lt (div_pos (mul_pos hXZ hYZ) hZ))
        (fun _ => div_pos (mul_pos hXZ hYZ) hZ)
  have hsumbound :
      ∑ a, ∑ b, ∑ c, (ν a b c - margXZ ν a c * margYZ ν b c / margZ ν c) ≤ condMutualInfoZ ν := by
    unfold condMutualInfoZ
    exact Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ =>
      Finset.sum_le_sum fun c _ => hterm a b c
  have hperc : ∀ c, ∑ a, ∑ b, (margXZ ν a c * margYZ ν b c / margZ ν c) = margZ ν c := by
    intro c
    rcases eq_or_lt_of_le (hZnn c) with hZ0 | hZpos
    · have hall : ∀ a, margXZ ν a c = 0 := by
        intro a
        have hle : margXZ ν a c ≤ margZ ν c :=
          Finset.single_le_sum (fun i _ => hXZnn i c) (Finset.mem_univ a)
        exact le_antisymm (by linarith) (hXZnn a c)
      rw [← hZ0]
      simp only [hall, zero_mul, zero_div, Finset.sum_const_zero]
    · have hmm : ∑ a, ∑ b, margXZ ν a c * margYZ ν b c = margZ ν c * margZ ν c := by
        rw [← Finset.sum_mul_sum, sum_margXZ, sum_margYZ_c]
      rw [show (∑ a, ∑ b, (margXZ ν a c * margYZ ν b c / margZ ν c))
            = (∑ a, ∑ b, margXZ ν a c * margYZ ν b c) / margZ ν c by simp_rw [← Finset.sum_div]]
      rw [hmm, mul_div_assoc, div_self hZpos.ne', mul_one]
  have hrsum : ∑ a, ∑ b, ∑ c, (margXZ ν a c * margYZ ν b c / margZ ν c) = 1 := by
    rw [Finset.sum_congr rfl fun a _ => Finset.sum_comm]
    rw [Finset.sum_comm]
    simp_rw [hperc]
    unfold margZ
    rw [Finset.sum_comm, Finset.sum_congr rfl fun a _ => Finset.sum_comm]
    exact hsum
  have hlhs : ∑ a, ∑ b, ∑ c, (ν a b c - margXZ ν a c * margYZ ν b c / margZ ν c) = 0 := by
    calc ∑ a, ∑ b, ∑ c, (ν a b c - margXZ ν a c * margYZ ν b c / margZ ν c)
        = (∑ a, ∑ b, ∑ c, ν a b c)
          - ∑ a, ∑ b, ∑ c, (margXZ ν a c * margYZ ν b c / margZ ν c) := by
          simp_rw [Finset.sum_sub_distrib]
      _ = 1 - 1 := by rw [hsum, hrsum]
      _ = 0 := by ring
  linarith [hsumbound, hlhs.ge]

/-- **Chain rule, other half:** `I(X;Z) + I(X;Y|Z) = ∑_{x,y,z} ν·log( ν / (p(x)·p(y,z)) )`, the same
`I(X;(Y,Z))` as `mi_add_condMutualInfo`. No Markov assumption. -/
theorem mi_add_condMutualInfoZ (ν : α → β → γ → ℝ) (hnn : ∀ a b c, 0 ≤ ν a b c) :
    mutualInfo (margXZ ν) + condMutualInfoZ ν
      = ∑ a, ∑ b, ∑ c, ν a b c * Real.log (ν a b c / (margX ν a * margYZ ν b c)) := by
  have hXZnn : ∀ a c, 0 ≤ margXZ ν a c := fun a c => Finset.sum_nonneg fun b _ => hnn a b c
  have hm1 : ∀ a, marg₁ (margXZ ν) a = margX ν a := by
    intro a; unfold marg₁ margXZ margX; rw [Finset.sum_comm]
  have L2 : mutualInfo (margXZ ν)
      = ∑ a, ∑ c, ∑ b, ν a b c * Real.log (margXZ ν a c / (margX ν a * margZ ν c)) := by
    unfold mutualInfo
    refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun c _ => ?_))
    rw [hm1 a]
    change margXZ ν a c * Real.log (margXZ ν a c / (margX ν a * margZ ν c))
        = ∑ b, ν a b c * Real.log (margXZ ν a c / (margX ν a * margZ ν c))
    rw [← Finset.sum_mul]
    rfl
  rw [L2, Finset.sum_congr rfl fun a _ => Finset.sum_comm, condMutualInfoZ, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  rcases eq_or_lt_of_le (hnn a b c) with h0 | hpos
  · rw [← h0]; simp
  · have hXZ : 0 < margXZ ν a c :=
      lt_of_lt_of_le hpos (Finset.single_le_sum (fun b _ => hnn a b c) (Finset.mem_univ b))
    have hYZ : 0 < margYZ ν b c :=
      lt_of_lt_of_le hpos (Finset.single_le_sum (fun a _ => hnn a b c) (Finset.mem_univ a))
    have hZ : 0 < margZ ν c :=
      lt_of_lt_of_le hXZ (Finset.single_le_sum (fun a _ => hXZnn a c) (Finset.mem_univ a))
    have hX : 0 < margX ν a := by
      have h1 : ν a b c ≤ ∑ c', ν a b c' :=
        Finset.single_le_sum (fun i _ => hnn a b i) (Finset.mem_univ c)
      have h2 : (∑ c', ν a b c') ≤ margX ν a :=
        Finset.single_le_sum (fun i _ => Finset.sum_nonneg fun c' _ => hnn a i c') (Finset.mem_univ b)
      linarith
    have hP : (0:ℝ) < margXZ ν a c / (margX ν a * margZ ν c) := div_pos hXZ (mul_pos hX hZ)
    have hQ : (0:ℝ) < ν a b c * margZ ν c / (margXZ ν a c * margYZ ν b c) :=
      div_pos (mul_pos hpos hZ) (mul_pos hXZ hYZ)
    have hPQ : margXZ ν a c / (margX ν a * margZ ν c)
          * (ν a b c * margZ ν c / (margXZ ν a c * margYZ ν b c))
        = ν a b c / (margX ν a * margYZ ν b c) := by
      field_simp
    rw [← mul_add, ← Real.log_mul hP.ne' hQ.ne', hPQ]

/-- **Data-processing inequality.** For a Markov chain `X → Y → Z` (conditional independence
`MarkovCI`), `I(X;Z) ≤ I(X;Y)`. Proof: the two chain-rule halves give `I(X;Y) + I(X;Z|Y) =
I(X;(Y,Z)) = I(X;Z) + I(X;Y|Z)`; Markov makes `I(X;Z|Y) = 0` and `I(X;Y|Z) ≥ 0`. This discharges
`hDPI` of `ChengCCC.misid_lower_bound` at the Markov chain `T → c → θ` (with `C_ctx ≥ I(c;θ)`). -/
theorem dataProcessing (ν : α → β → γ → ℝ) (hnn : ∀ a b c, 0 ≤ ν a b c)
    (hsum : ∑ a, ∑ b, ∑ c, ν a b c = 1) (hM : MarkovCI ν) :
    mutualInfo (margXZ ν) ≤ mutualInfo (margXY ν) := by
  have k1 := mi_add_condMutualInfo ν hnn
  have k2 := mi_add_condMutualInfoZ ν hnn
  have h0 : condMutualInfo ν = 0 := markov_condMutualInfo_zero ν hnn hM
  have hpos : 0 ≤ condMutualInfoZ ν := condMutualInfoZ_nonneg ν hnn hsum
  linarith [k1, k2, h0, hpos]

/-- Mutual information is symmetric in its two variables, `I(X;Y) = I(Y;X)` (swap the sum order and
the product of marginals). -/
theorem mutualInfo_comm (μ : α → β → ℝ) : mutualInfo μ = mutualInfo (fun b a => μ a b) := by
  unfold mutualInfo
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun a _ => ?_))
  change μ a b * Real.log (μ a b / (marg₁ μ a * marg₂ μ b))
      = μ a b * Real.log (μ a b / (marg₂ μ b * marg₁ μ a))
  rw [mul_comm (marg₁ μ a) (marg₂ μ b)]

/-- **The other DPI direction** `I(X;Z) ≤ I(Y;Z)` under the same Markov chain `X → Y → Z`. Obtained
from `dataProcessing` by reindexing the (symmetric) chain as `Z → Y → X` (`ν' z y x = ν x y z`) and
transporting through `mutualInfo_comm`. This is the form `ChengCCC` needs: with the capacity bound
`I(Y;Z) ≤ C_ctx` it gives `I(X;Z) ≤ C_ctx` (here `X = T`, `Y = c`, `Z = θ`). -/
theorem dataProcessing' (ν : α → β → γ → ℝ) (hnn : ∀ a b c, 0 ≤ ν a b c)
    (hsum : ∑ a, ∑ b, ∑ c, ν a b c = 1) (hM : MarkovCI ν) :
    mutualInfo (margXZ ν) ≤ mutualInfo (margYZ ν) := by
  have hnn' : ∀ z y x, 0 ≤ (fun z y x => ν x y z) z y x := fun z y x => hnn x y z
  have hsum' : ∑ z, ∑ y, ∑ x, (fun z y x => ν x y z) z y x = 1 := by
    change ∑ z, ∑ y, ∑ x, ν x y z = 1
    rw [Finset.sum_congr rfl fun z _ => Finset.sum_comm, Finset.sum_comm,
        Finset.sum_congr rfl fun x _ => Finset.sum_comm]
    exact hsum
  have hM' : MarkovCI (fun z y x => ν x y z) := by
    intro z y x
    have hY : margY (fun z y x => ν x y z) y = margY ν y := by
      unfold margY; rw [Finset.sum_comm]
    change ν x y z * margY (fun z y x => ν x y z) y
        = margXY (fun z y x => ν x y z) z y * margYZ (fun z y x => ν x y z) y x
    rw [hY, hM x y z]
    change margXY ν x y * margYZ ν y z = margYZ ν y z * margXY ν x y
    ring
  have key := dataProcessing (fun z y x => ν x y z) hnn' hsum' hM'
  rw [mutualInfo_comm (margXZ ν), mutualInfo_comm (margYZ ν)]
  exact key

/-! ## Fano's inequality

Setup: a finite source `X : α` with `Fintype.card α = K`, side information `Y : β`, joint pmf
`μ : α → β → ℝ` (`≥ 0`, summing to `1`), a **decoder** `g : β → α`, and error probability
`Pe = ∑_{a,b} (if a = g b then 0 else μ a b)` (the joint mass off the decoder's guess). Fano bounds
the conditional entropy `H(X|Y) = condEntropy μ` by `log 2 + Pe·log(K−1)`, hence (rearranged)
`(condEntropy μ − 1)/log(K−1) ≤ Pe` — exactly `ChengCCC`'s `hFano`. -/

/-- **Unnormalised max-entropy bound** `∑_{s∈T} negMulLog(f s) ≤ negMulLog(M) + M·log|T|` where
`M = ∑_{s∈T} f s` (nonneg masses). Equality for the uniform split; proof is the finite Gibbs
inequality against the uniform reference `M/|T|`. The single analytic input to Fano. -/
private lemma entropy_masses_le {S : Type*} (T : Finset S) (f : S → ℝ) (hf : ∀ s ∈ T, 0 ≤ f s) :
    ∑ s ∈ T, Real.negMulLog (f s)
      ≤ Real.negMulLog (∑ s ∈ T, f s) + (∑ s ∈ T, f s) * Real.log (T.card) := by
  rcases eq_or_lt_of_le (Finset.sum_nonneg hf) with hM0 | hMpos
  · have hLHS : ∑ s ∈ T, Real.negMulLog (f s) = 0 :=
      Finset.sum_eq_zero fun s hs => by
        rw [(Finset.sum_eq_zero_iff_of_nonneg hf).mp hM0.symm s hs, Real.negMulLog_zero]
    rw [hLHS, ← hM0, Real.negMulLog_zero]; simp
  · have hTne : T.Nonempty := Finset.nonempty_of_sum_ne_zero hMpos.ne'
    have hcard : (0:ℝ) < T.card := by exact_mod_cast Finset.card_pos.mpr hTne
    have hMr : 0 < (∑ s ∈ T, f s) / T.card := div_pos hMpos hcard
    have key : 0 ≤ ∑ s ∈ T, f s * Real.log (f s / ((∑ s ∈ T, f s) / T.card)) := by
      have h2 : ∑ s ∈ T, (f s - (∑ s ∈ T, f s) / T.card) = 0 := by
        rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]; field_simp; ring
      calc (0:ℝ) = ∑ s ∈ T, (f s - (∑ s ∈ T, f s) / T.card) := h2.symm
        _ ≤ ∑ s ∈ T, f s * Real.log (f s / ((∑ s ∈ T, f s) / T.card)) :=
            Finset.sum_le_sum fun s hs => gibbs_term (hf s hs) hMr.le (fun _ => hMr)
    have hexpand : ∑ s ∈ T, f s * Real.log (f s / ((∑ s ∈ T, f s) / T.card))
        = -(∑ s ∈ T, Real.negMulLog (f s)) + Real.negMulLog (∑ s ∈ T, f s)
          + (∑ s ∈ T, f s) * Real.log (T.card) := by
      calc ∑ s ∈ T, f s * Real.log (f s / ((∑ s ∈ T, f s) / T.card))
          = ∑ s ∈ T, (f s * Real.log (f s)
              - f s * Real.log ((∑ s ∈ T, f s) / T.card)) :=
            Finset.sum_congr rfl fun s hs => by
              rcases eq_or_lt_of_le (hf s hs) with h0 | hpos
              · rw [← h0]; ring
              · rw [Real.log_div (ne_of_gt hpos) (ne_of_gt hMr)]; ring
        _ = (∑ s ∈ T, f s * Real.log (f s))
              - (∑ s ∈ T, f s) * Real.log ((∑ s ∈ T, f s) / T.card) := by
            rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
        _ = -(∑ s ∈ T, Real.negMulLog (f s))
              - (∑ s ∈ T, f s) * Real.log ((∑ s ∈ T, f s) / T.card) := by
            congr 1
            rw [← Finset.sum_neg_distrib]
            exact Finset.sum_congr rfl fun s _ => by rw [Real.negMulLog_eq_neg]; ring
        _ = -(∑ s ∈ T, Real.negMulLog (f s)) + Real.negMulLog (∑ s ∈ T, f s)
              + (∑ s ∈ T, f s) * Real.log (T.card) := by
            have hlogdiv : Real.log ((∑ s ∈ T, f s) / T.card)
                = Real.log (∑ s ∈ T, f s) - Real.log T.card :=
              Real.log_div hMpos.ne' (by exact_mod_cast hcard.ne')
            have hnml : Real.negMulLog (∑ s ∈ T, f s)
                = -((∑ s ∈ T, f s) * Real.log (∑ s ∈ T, f s)) := by
              rw [Real.negMulLog_eq_neg]
            rw [hlogdiv, hnml]; ring
    linarith [key, hexpand]

/-- Binary instance of `entropy_masses_le`: `negMulLog s + negMulLog m ≤ negMulLog(s+m) + (s+m)·log 2`.
This is the per-symbol "binary entropy ≤ log 2" bound (unnormalised). -/
private lemma negMulLog_add_le {s m : ℝ} (hs : 0 ≤ s) (hm : 0 ≤ m) :
    Real.negMulLog s + Real.negMulLog m ≤ Real.negMulLog (s + m) + (s + m) * Real.log 2 := by
  have H := entropy_masses_le (Finset.univ : Finset (Fin 2)) (fun i => ![s, m] i)
    (fun i _ => by fin_cases i <;> simp [hs, hm])
  simpa [Fin.sum_univ_two] using H

/-- **Fano core (in nats):** `H(X|Y) ≤ log 2 + Pe·log(K−1)`. Decompose `condEntropy μ = ∑_b D_b`
with `D_b = ∑_a negMulLog(μ a b) − negMulLog(p_Y b)`; split off the decoded symbol `g b`, bound the
remaining `K−1` masses by `entropy_masses_le` and the binary split by `negMulLog_add_le`. The looser
`log 2` (vs. the tight `binEntropy Pe`) avoids Jensen and is all `fano'`/`ChengCCC` needs. -/
theorem condEntropy_le_log2 [DecidableEq α] (μ : α → β → ℝ) (g : β → α)
    (hnn : ∀ a b, 0 ≤ μ a b) (hsum : ∑ a, ∑ b, μ a b = 1) (hK : 1 ≤ Fintype.card α) :
    condEntropy μ ≤ Real.log 2
      + (∑ a, ∑ b, (if a = g b then 0 else μ a b)) * Real.log ((Fintype.card α : ℝ) - 1) := by
  have hKcast : ((Fintype.card α - 1 : ℕ) : ℝ) = (Fintype.card α : ℝ) - 1 := by
    rw [Nat.cast_sub hK, Nat.cast_one]
  -- condEntropy regrouped by `b`.
  have hCE : condEntropy μ
      = ∑ b, ((∑ a, Real.negMulLog (μ a b)) - Real.negMulLog (marg₂ μ b)) := by
    unfold condEntropy Hjoint entropy
    rw [Finset.sum_comm, ← Finset.sum_sub_distrib]
  -- Per-`b` Fano bound.
  have hDb : ∀ b, (∑ a, Real.negMulLog (μ a b)) - Real.negMulLog (marg₂ μ b)
      ≤ marg₂ μ b * Real.log 2
        + (∑ a ∈ Finset.univ.erase (g b), μ a b) * Real.log ((Fintype.card α : ℝ) - 1) := by
    intro b
    have hsplit : (∑ a, Real.negMulLog (μ a b))
        = Real.negMulLog (μ (g b) b) + ∑ a ∈ Finset.univ.erase (g b), Real.negMulLog (μ a b) :=
      (Finset.add_sum_erase _ _ (Finset.mem_univ (g b))).symm
    have hpY : marg₂ μ b = μ (g b) b + ∑ a ∈ Finset.univ.erase (g b), μ a b := by
      unfold marg₂; exact (Finset.add_sum_erase _ _ (Finset.mem_univ (g b))).symm
    have herr : ∑ a ∈ Finset.univ.erase (g b), Real.negMulLog (μ a b)
        ≤ Real.negMulLog (∑ a ∈ Finset.univ.erase (g b), μ a b)
          + (∑ a ∈ Finset.univ.erase (g b), μ a b) * Real.log ((Fintype.card α : ℝ) - 1) := by
      have h := entropy_masses_le (Finset.univ.erase (g b)) (fun a => μ a b) (fun a _ => hnn a b)
      rwa [Finset.card_erase_of_mem (Finset.mem_univ (g b)), Finset.card_univ, hKcast] at h
    have hbin := negMulLog_add_le (hnn (g b) b)
      (Finset.sum_nonneg (fun a _ => hnn a b) :
        0 ≤ ∑ a ∈ Finset.univ.erase (g b), μ a b)
    rw [hsplit, hpY]; linarith [herr, hbin]
  -- erase-sum ↔ if-sum, and the two total sums.
  have hconv : ∀ b, ∑ a, (if a = g b then 0 else μ a b)
      = ∑ a ∈ Finset.univ.erase (g b), μ a b := by
    intro b
    have hpe : ∑ a, (if a = g b then 0 else μ a b)
        = (if g b = g b then 0 else μ (g b) b)
          + ∑ a ∈ Finset.univ.erase (g b), (if a = g b then 0 else μ a b) :=
      (Finset.add_sum_erase Finset.univ (fun a => if a = g b then 0 else μ a b)
        (Finset.mem_univ (g b))).symm
    rw [hpe, if_pos rfl, zero_add]
    exact Finset.sum_congr rfl (fun a ha => if_neg (Finset.ne_of_mem_erase ha))
  have hmarg : ∑ b, marg₂ μ b = 1 := by unfold marg₂; rw [Finset.sum_comm]; exact hsum
  have hPe : ∑ b, (∑ a ∈ Finset.univ.erase (g b), μ a b)
      = ∑ a, ∑ b, (if a = g b then 0 else μ a b) := by
    simp_rw [← hconv]; rw [Finset.sum_comm]
  rw [hCE]
  calc ∑ b, ((∑ a, Real.negMulLog (μ a b)) - Real.negMulLog (marg₂ μ b))
      ≤ ∑ b, (marg₂ μ b * Real.log 2
          + (∑ a ∈ Finset.univ.erase (g b), μ a b) * Real.log ((Fintype.card α : ℝ) - 1)) :=
        Finset.sum_le_sum (fun b _ => hDb b)
    _ = Real.log 2
          + (∑ a, ∑ b, (if a = g b then 0 else μ a b)) * Real.log ((Fintype.card α : ℝ) - 1) := by
        rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul, hmarg, one_mul, hPe]

/-- **Fano's inequality (rearranged), the form `ChengCCC.misid_lower_bound` consumes as `hFano`.**
For `K = Fintype.card α ≥ 3`, `(condEntropy μ − 1) / log(K−1) ≤ Pe`, with `Pe` the error
probability of the decoder `g`. Follows from `condEntropy_le_log2` and `log 2 ≤ 1`. -/
theorem fano' [DecidableEq α] (μ : α → β → ℝ) (g : β → α)
    (hnn : ∀ a b, 0 ≤ μ a b) (hsum : ∑ a, ∑ b, μ a b = 1) (hK : 3 ≤ Fintype.card α) :
    (condEntropy μ - 1) / Real.log ((Fintype.card α : ℝ) - 1)
      ≤ ∑ a, ∑ b, (if a = g b then 0 else μ a b) := by
  have hcard : (3:ℝ) ≤ (Fintype.card α : ℝ) := by exact_mod_cast hK
  have hlogpos : 0 < Real.log ((Fintype.card α : ℝ) - 1) := Real.log_pos (by linarith)
  have hlog2 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 2 by norm_num); linarith
  have hcore := condEntropy_le_log2 μ g hnn hsum (by omega)
  rw [div_le_iff₀ hlogpos]; linarith [hcore, hlog2]

end FiniteInfoTheory
