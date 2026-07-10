/-
Copyright (c) 2026 Mykola Palamarchuk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mykola Palamarchuk
-/
import Mathlib

-- Formal-check file, not Mathlib-destined: opt out of the house-style header linter.
set_option linter.style.header false

/-!
# Regime consistency (Paper II, §1.2)

Provenance: Paper II, §1.2 (the regime constants C1–C3). The regime
`r ≪ K ≪ L` is load-bearing in Papers II–IV; this file certifies it is internally consistent in
the ordering sense.

Status: PROVED as pure real-arithmetic statements. This is the *arithmetic core* of the §1.2
regime only.

## What this DOES establish
* `regime_strict_ordering`: under C1 (`K ≥ c₀·r·log(r/δ)`), C2 (`L ≥ c₁·K`), C3 (`r ≥ c₂`) and
  explicit NAMED constant conditions, the strict ordering `r < K ∧ K < L` holds. This underwrites
  every II–IV result that assumes the regime `r ≪ K ≪ L`.
* `regime_satisfiable`: the premise set of `regime_strict_ordering` is satisfiable — concrete
  values (`r=3, δ=1/2, c₀=1, c₁=2, c₂=3, K=100, L=200`) meet C1–C3 and all constant conditions.
  Together with the implication this shows the regime is genuinely *non-empty* (not vacuously
  certified): the constraints are consistent AND force `r < K < L`.

## What this does NOT establish (stays in prose; no overclaiming)
* No Kolmogorov complexity: `r`, `K`, `L`, `δ` are abstract reals; `r` is not `K(R)`, `K` is not a
  machine-relative memory in bits.
* Proves only the arithmetic ordering — NOT that any physical system realizes constants satisfying
  C1–C3 (§1.2's "we assume there exist…" is an empirical input, untouched).
* Renders the paper's "≪" as strict `<` with a concrete constant gap (`c₁>1`, `c₀≥1`), a
  *sufficient concrete instance*, not §1.2's asymptotic "`K,L,r→∞` with ratios fixed" limit.
* Does not claim joint satisfiability with the other II–IV conditions (e.g. `L = n·log|O|`, `n≥2`)
  — only the C1–C3 ordering.

## Hypotheses: paper-stated vs added/strengthened
* Paper-stated / faithful: C1, C2, C3 verbatim; `δ ∈ (0,1)`.
* Strengthened (flagged):
  - `c₁ > 1` is load-bearing: bare `c₁ > 0` with C2's `≥` permits `L = K`, so strict `K < L`
    genuinely needs `c₁ > 1`. This is the concrete-instance form of the regularity "≪".
  - `c₀ ≥ 1` (paper: `c₀ > 0`): with bare `c₀ > 0` the strict `r < K` holds only asymptotically;
    `c₀ ≥ 1` with `log(r/δ) > 1` gives it non-asymptotically.
  - `c₂ ≥ 3` (paper: `c₂ > 0`, practically `≈10³`): the minimal value forcing `log(r/δ) > 1`,
    far below the paper's buffer, so no real restriction.

`Real.log` is the natural logarithm, as in the companion files.
-/

namespace RegimeConsistency

/-- The regime `r ≪ K ≪ L` is internally consistent: under C1–C3 with explicit named constant
conditions, the strict ordering `r < K < L` holds. The two estimates are independent — `r < K`
from C1 (`c₀·r·log(r/δ) > r`, since `c₀ ≥ 1` and `log(r/δ) > 1`) and `K < L` from C2
(`c₁·K > K`, since `c₁ > 1` and `K > 0`). (Paper II §1.2.) -/
theorem regime_strict_ordering
    (r K L c₀ c₁ c₂ δ : ℝ)
    (hC1 : c₀ * r * Real.log (r / δ) ≤ K) -- C1 capacity above threshold
    (hC2 : c₁ * K ≤ L) -- C2 regularity
    (hC3 : c₂ ≤ r) -- C3 UTM-invariance buffer (r ≥ c₂)
    (hc₀ : 1 ≤ c₀) -- discovery slack (paper: c₀>0; STRENGTHENED ≥1 for strict r<K)
    (hc₁ : 1 < c₁) -- regularity ratio (paper: c₁>0; STRENGTHENED >1 for strict K<L)
    (hc₂ : 3 ≤ c₂) -- buffer ≥ 3 (paper: c₂>0, ≈10³; gives log(r/δ)>1)
    (hδ0 : 0 < δ) (hδ1 : δ < 1) : -- confidence δ ∈ (0,1)
    r < K ∧ K < L := by
  have hr3 : (3 : ℝ) ≤ r := le_trans hc₂ hC3
  have hr0 : 0 < r := by linarith
  -- `r/δ ≥ 3 > e`, hence `1 < log(r/δ)`.
  have h3rd : (3 : ℝ) ≤ r / δ := by
    rw [le_div_iff₀ hδ0]; linarith
  have hlog1 : 1 < Real.log (r / δ) := by
    rw [Real.lt_log_iff_exp_lt (by positivity)]
    have he : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
    linarith
  -- `r < K`: C1 dominates `r` since `c₀·log(r/δ) ≥ log(r/δ) > 1`.
  have hrK : r < K := by
    nlinarith [hC1, mul_pos hr0 (by linarith : (0 : ℝ) < Real.log (r / δ) - 1),
               mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ c₀ - 1) hr0.le)
                 (by linarith : (0 : ℝ) ≤ Real.log (r / δ))]
  have hK0 : 0 < K := by linarith
  -- `K < L`: C2 with the strict ratio `c₁ > 1`.
  have hKL : K < L := by
    nlinarith [hC2, mul_pos (by linarith : (0 : ℝ) < c₁ - 1) hK0]
  exact ⟨hrK, hKL⟩

/-- The premises of `regime_strict_ordering` are satisfiable: `r=3, δ=1/2, c₀=1, c₁=2, c₂=3,
K=100, L=200` meet C1–C3 and all constant conditions. The C1 check uses only the crude bound
`log 6 ≤ 5` (`Real.log_le_sub_one_of_pos`), so `c₀·r·log(r/δ) = 3·log 6 ≤ 15 ≤ 100 = K`. This
makes the regime genuinely non-empty, so the implication is not vacuous. -/
theorem regime_satisfiable :
    ∃ r K L c₀ c₁ c₂ δ : ℝ,
      c₀ * r * Real.log (r / δ) ≤ K ∧
        c₁ * K ≤ L ∧
          c₂ ≤ r ∧
            1 ≤ c₀ ∧ 1 < c₁ ∧ 3 ≤ c₂ ∧ 0 < δ ∧ δ < 1 := by
  refine ⟨3, 100, 200, 1, 2, 3, 1 / 2, ?_, by norm_num, by norm_num,
          by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
  -- C1: `1 * 3 * log (3 / (1/2)) ≤ 100`, via `log 6 ≤ 6 - 1 = 5`.
  have h : Real.log (3 / (1 / 2)) ≤ 3 / (1 / 2) - 1 :=
    Real.log_le_sub_one_of_pos (by norm_num)
  nlinarith [h]

end RegimeConsistency
