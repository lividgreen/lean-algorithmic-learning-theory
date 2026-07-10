/-
Copyright (c) 2026 Mykola Palamarchuk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mykola Palamarchuk
-/
import Mathlib

-- Formal-check file, not Mathlib-destined: opt out of the house-style header linter.
set_option linter.style.header false

/-!
# Sample complexity (Paper III, §4 Theorem 4.1(i)) — the ε₀-absorption

Provenance: Paper III, §4 (Theorem 4.1 part (i) and the
"Remark on ε₀").

Status: PROVED as a pure real-arithmetic bound. **This is the part-(i) *sample-count* absorption
that the companion `PolyTimeAccounting` (FV-B1) explicitly does NOT cover.** B1 does the step-(c)
total-work product (`O(r·log(1/δ))` window × `O(r)` per-step); this does the part-(i) observation
count (the "Remark on ε₀" collapse). All real content (the algorithm, SQ pruning, the impossibility
bypasses) is taken as GIVEN and stays prose.

## What this DOES establish
* `sample_complexity_r2`: the imported Paper II Thm 3.1 discovery bound `O((r + log(1/δ))/ε₀)`
  (proof step (a)) collapses to the *stated* `O(r²·log(1/δ))` under the benign-class assumption
  `ε₀ = Ω(1/r)` (modeled `ε₀ ≥ 1/(a·r)`), with explicit witness constant `2·a·c`.

## Relationship to PolyTimeAccounting (FV-B1)
B1 = step-(c) total work (search-window length × per-step cost). This = part-(i) sample count (the
ε₀-absorption). Together they discharge the two distinct routes to the `O(r²·log(1/δ))` order in
Theorem 4.1: B1 multiplies an `O(r)` cost into an already-`O(r·log(1/δ))` window, whereas here the
`r²` arises from absorbing `1/ε₀ = O(r)` into the `O((r+log(1/δ)))` discovery numerator.

## What this does NOT establish (stays in prose; the substance)
* No algorithm: not the time-bounded prequential MDL, posterior concentration, or SQ pruning.
* No SQ machinery: not the SQ oracle, the statistical dimension `d_SQ`, or the candidate-enumeration
  bound.
* No impossibility bypasses: not Miyabe, Raz, or Farr–Wallace.
* It takes the Paper II Thm 3.1 discovery bound (step (a)) as GIVEN and proves only the arithmetic
  absorption of `ε₀` into the `r²` factor. Bookkeeping, not the Paper III theorem.

## Hypotheses: paper-stated vs added
* Paper-stated / faithful: the step-(a) discovery bound `O((r + log(1/δ))/ε₀)`; `r ≥ 1`; positivity
  of the `O`-constants; nonnegativity of `c`.
* Added / modeling: `ε₀ ≥ 1/(a·r)` models the benign-class `ε₀ = Ω(1/r)` (the exact instance the
  "Remark on ε₀" invokes), with explicit witness constant `2·a·c`. **Sharper than B1's `δ ∈ (0,1)`:
  this needs the confidence regime `δ ≤ 1/e` (modeled `δ ≤ exp(-1)`) so that `log(1/δ) ≥ 1`** — the
  `r² + r·L ≤ 2·r²·L` absorption step requires `L ≥ 1`, not merely `L ≥ 0`. (`O`-notation hides
  this: for the *order* `O(r²·log(1/δ))` any `δ` away from `1` works; the explicit-constant
  version records the threshold it actually uses.)

`Real.log` is the natural logarithm, as in the companion files.
-/

namespace SampleComplexity

/-- Theorem 4.1(i) sample complexity, via the §4 "Remark on ε₀" absorption: the imported Paper II
Thm 3.1 discovery bound `O((r + log(1/δ))/ε₀)` (proof step (a)) collapses to the *stated*
`O(r²·log(1/δ))` under the benign-class assumption `ε₀ = Ω(1/r)` (modeled `ε₀ ≥ 1/(a·r)`), with
explicit witness constant `2·a·c`. This is the part-(i) claim `PolyTimeAccounting` (FV-B1) flags as
NOT covered (it does the step-(c) total-work product). `Real.log` is the natural log. -/
theorem sample_complexity_r2
    (Tdiscover ε₀ r c a δ : ℝ)
    (hImport : Tdiscover ≤ c * (r + Real.log (1 / δ)) / ε₀) -- step (a): Paper II Thm 3.1 import
    (hε₀ : 1 / (a * r) ≤ ε₀) -- benign class: ε₀ = Ω(1/r)
    (ha : 0 < a) (hc : 0 ≤ c) (hr : 1 ≤ r)
    (hδ0 : 0 < δ) (hδe : δ ≤ Real.exp (-1)) : -- confidence regime δ ≤ 1/e ⇒ log(1/δ) ≥ 1
    Tdiscover ≤ 2 * a * c * r ^ 2 * Real.log (1 / δ) := by
  have hr0 : 0 < r := lt_of_lt_of_le one_pos hr
  have har : 0 < a * r := mul_pos ha hr0
  have hε₀0 : 0 < ε₀ := lt_of_lt_of_le (by positivity) hε₀
  have hrecip : 1 / ε₀ ≤ a * r := by
    rw [div_le_iff₀ hε₀0]
    rw [div_le_iff₀ har] at hε₀
    nlinarith [hε₀]
  have hLpos : (1 : ℝ) ≤ Real.log (1 / δ) := by
    rw [one_div, Real.log_inv]
    have hlogδ : Real.log δ ≤ -1 := by
      have h := Real.log_le_log hδ0 hδe
      rwa [Real.log_exp] at h
    linarith
  set L := Real.log (1 / δ) with hLdef
  have hL0 : 0 ≤ L := le_trans zero_le_one hLpos
  have hrL : 0 ≤ r + L := by linarith
  have hcRL : 0 ≤ c * (r + L) := mul_nonneg hc hrL
  have hac : 0 ≤ a * c := mul_nonneg ha.le hc
  have hquad : r ^ 2 + r * L ≤ 2 * r ^ 2 * L := by
    nlinarith [mul_nonneg (sq_nonneg r) (sub_nonneg.mpr hLpos),
               mul_nonneg (mul_nonneg hr0.le hL0) (sub_nonneg.mpr hr)]
  calc Tdiscover
      ≤ c * (r + L) / ε₀ := hImport
    _ = c * (r + L) * (1 / ε₀) := by rw [mul_one_div]
    _ ≤ c * (r + L) * (a * r) := mul_le_mul_of_nonneg_left hrecip hcRL
    _ = a * c * (r ^ 2 + r * L) := by ring
    _ ≤ a * c * (2 * r ^ 2 * L) := mul_le_mul_of_nonneg_left hquad hac
    _ = 2 * a * c * r ^ 2 * L := by ring

end SampleComplexity
