/-
Copyright (c) 2026 Mykola Palamarchuk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mykola Palamarchuk
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic

-- Formal-check file, not Mathlib-destined: opt out of the house-style header linter.
set_option linter.style.header false

/-!
# Poly-time accounting ([SQ], §4 Theorem 4.1) — thin bookkeeping

Provenance: [SQ], §4 (Theorem 4.1, parts (i)–(iv) and proof
step (c)).

Status: PROVED as a pure real-arithmetic product bound. **This is deliberately THIN bookkeeping —
"an `O(r·log(1/δ))` bound times an `O(r)` bound is `O(r²·log(1/δ))`" — NOT the substantive Paper
III result.** All real content (the algorithm, SQ pruning, the impossibility bypasses) is taken as
GIVEN and stays prose.

## What this DOES establish
* `polytime_accounting`: the §4 proof-step-(c) total-work bound — a search window bounded by
  `O(r·log(1/δ))` (part iii) times a per-step cost bounded by `O(r)` gives total work
  `O(r²·log(1/δ))`, with explicit witness constant `a*b`. Part (iv) (`L`-independence) holds
  structurally: no `L` variable appears in the statement.

## Precision note on part (i) vs step (c)
Part (i) names `O(r²·log(1/δ))` the *sample complexity* (observation count); step (c) derives the
same order as the *total work* (search-window length × per-step cost). The paper treats both as the
same order. What is formalized here is the **total-work product** of step (c), which the paper
equates to the part-(i) order — not the sample-complexity claim of part (i) directly.

## What this does NOT establish (stays in prose; the substance)
* No algorithm: not the time-bounded prequential MDL, posterior concentration, or SQ pruning.
* No SQ machinery: not the SQ oracle, the statistical dimension `d_SQ`, or the BFJKMR `poly(r)`
  candidate-enumeration bound (step (b)).
* No impossibility bypasses: not Miyabe, Raz, or Farr–Wallace.
* It takes the sample bound (part iii, from [Discovery] Thm 3.1) and the per-step bound as GIVEN and
  proves only that their product is `O(r²·log(1/δ))`. Bookkeeping, not the [SQ] theorem.

## Hypotheses: paper-stated vs added
* Paper-stated / faithful: the part-(iii) window bound; the per-step compute bound; the total;
  `δ ∈ (0,1)`; `r ≥ 1`.
* Added / modeling: `cstep ≤ b·r` models the LINEAR instance of part (iii)'s `poly(r)` — the exact
  factor step (c)'s `r²` accounting multiplies ("the r factor of posterior-update cost"), not the
  general `poly(r)`. Explicit witness constant `a·b`. Nonnegativity of counts/costs (implicit in
  the paper).

`Real.log` is the natural logarithm, as in the companion files.
-/

namespace PolyTimeAccounting

/-- Theorem 4.1 complexity accounting (§4 proof step (c)): a search window bounded by
`O(r·log(1/δ))` times a per-step cost bounded by `O(r)` gives total work `O(r²·log(1/δ))`, with
explicit witness constant `a*b`. Pure bookkeeping — `_hb` and `_hT0` are genuinely nonneg but the
linear-bound product does not need them, so they are `_`-marked (documented, not deleted). -/
theorem polytime_accounting
    (Tsearch cstep r a b δ : ℝ)
    (hT : Tsearch ≤ a * r * Real.log (1 / δ)) -- part iii: T_search = O(r·log(1/δ))
    (hc : cstep ≤ b * r) -- per-step compute = O(r) (the (c) linear factor)
    (ha : 0 ≤ a) (_hb : 0 ≤ b) -- named O-constants (≥0); _hb documented, unused
    (hr : 1 ≤ r) -- rule complexity ≥ 1
    (_hT0 : 0 ≤ Tsearch) (hc0 : 0 ≤ cstep) -- counts/costs ≥ 0; _hT0 documented, unused
    (hδ0 : 0 < δ) (hδ1 : δ < 1) : -- confidence δ ∈ (0,1) → log(1/δ) ≥ 0
    Tsearch * cstep ≤ a * b * r ^ 2 * Real.log (1 / δ) := by
  have hr0 : (0 : ℝ) ≤ r := by linarith
  -- `1/δ ≥ 1`, so `log(1/δ) ≥ 0`.
  have h1d : (1 : ℝ) ≤ 1 / δ := by rw [le_div_iff₀ hδ0]; linarith
  have hlog : 0 ≤ Real.log (1 / δ) := Real.log_nonneg h1d
  -- the `O(r·log(1/δ))` bound is itself nonnegative
  have hA : 0 ≤ a * r * Real.log (1 / δ) := mul_nonneg (mul_nonneg ha hr0) hlog
  calc Tsearch * cstep
      ≤ (a * r * Real.log (1 / δ)) * (b * r) := mul_le_mul hT hc hc0 hA
    _ = a * b * r ^ 2 * Real.log (1 / δ) := by ring

end PolyTimeAccounting
