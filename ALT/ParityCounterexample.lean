/-
Copyright (c) 2026 Mykola Palamarchuk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mykola Palamarchuk
-/
import Mathlib

-- Formal-check file, not Mathlib-destined: opt out of the house-style header linter.
set_option linter.style.header false

/-!
# Parity counterexample to Assumption A ([SQ], §5)

Provenance: [SQ], §3.4 (statistical dimension + Assumption A),
§4 (Theorem 4.1, which assumes `d_SQ = poly(r)`), and §5 ("What about Parity?"). The mathematical
content is the elementary "exponential beats every polynomial".

Status: PROVED as pure real-asymptotics statements. This is the *arithmetic core* of §5 only.

## What this DOES establish
* `poly_isLittleO_dSQ`: every (real) power of `r` is little-o of the modeled exponential
  statistical dimension `dSQ ε` — the "exp beats poly" fact, in Mathlib asymptotics.
* `dSQ_not_polyBounded`: the modeled `d_SQ` admits NO polynomial bound. Hence **Assumption A**
  (`d_SQ = poly(r)`, §3.4/§4) **fails** for parity, so **Theorem 4.1 does not apply** to it —
  the §5 "theorem operating within its correct scope" point, formalized.

## What this does NOT establish (stays in prose; no overclaiming)
* Not the SQ statistical dimension `d_SQ` itself: no SQ oracle, no concept class, no query
  machinery. `dSQ ε` is a bare exponential standing in for it.
* Not the identification `r ≈ n`, and not that parity's `d_SQ` really *is* `2^Ω(n)` (the
  Blum–Furst–Jackson–Kearns–Mansour–Rudich fact). We take "`d_SQ` is exponential in `r`" as the
  MODELED PREMISE.
* Not Raz's `Ω(r²)` memory lower bound, not that it violates [Discovery]'s C1, and not that
  `g(r,δ) = O(r·log(r/δ))` is "false for parity" — those §5 consequences stay in prose.
* We prove ONLY the arithmetic: exponential ⇏ polynomial, hence Assumption A fails.

## Hypotheses: paper-stated vs added/strengthened
* Paper-stated / faithful: Assumption A as a polynomial bound (`∃ C, k`); the regime `r → ∞`
  (`Filter.atTop`).
* Added/strengthened (flagged): modeling `2^Ω(n)` as `Real.exp (ε·r)` with a CONCRETE `ε > 0`
  and an EXACT exponent in place of `Ω(·)`. Since `2^{c·r} = exp((c·ln 2)·r)`, base-`e` with a
  positive `ε` is fully general (the base is absorbed into `ε`); this is precisely the exponential
  lower bound on `d_SQ` the paper asserts, made concrete.
-/

namespace ParityCounterexample

open Asymptotics Filter

/-- Modeled parity statistical dimension: exponential in the rule complexity `r`
(`2^{Ω(n)}` with `r ≈ n`, the base folded into `ε > 0`). -/
noncomputable def dSQ (ε r : ℝ) : ℝ := Real.exp (ε * r)

/-- "Assumption A" ([SQ] §3.4 / §4): `d_SQ` is polynomially bounded in `r`. The weakest
reasonable form of "poly-bounded" (genuine natural-number degree `k`), so its negation is the
strongest faithful "not polynomial" claim. -/
def PolyBounded (f : ℝ → ℝ) : Prop :=
  ∃ (C : ℝ) (k : ℕ), ∀ᶠ r in atTop, f r ≤ C * r ^ k

/-- Exponential beats every polynomial (faithful Mathlib-asymptotics core): every real power of
`r` is little-o of the modeled exponential `d_SQ`. Direct from
`isLittleO_rpow_exp_pos_mul_atTop`. -/
theorem poly_isLittleO_dSQ (ε : ℝ) (hε : 0 < ε) (k : ℝ) :
    (fun r => r ^ k) =o[atTop] dSQ ε :=
  isLittleO_rpow_exp_pos_mul_atTop k hε

/-- §5 arithmetic core: the modeled parity statistical dimension is NOT polynomially bounded, so
Assumption A fails (hence Theorem 4.1 does not apply to parity). Strategy: a polynomial bound
makes `d_SQ = O(r^k)`; composing with `poly_isLittleO_dSQ` gives `d_SQ =o d_SQ`, forcing
`d_SQ ≤ 0` somewhere in `atTop`, contradicting `Real.exp_pos`. -/
theorem dSQ_not_polyBounded (ε : ℝ) (hε : 0 < ε) : ¬ PolyBounded (dSQ ε) := by
  rintro ⟨C, k, hCk⟩
  -- The polynomial bound, with `r ^ (k : ℕ)` rewritten as the real power `r ^ (k : ℝ)`,
  -- and bounded by its norm, witnesses `dSQ ε =O[atTop] (fun r => r ^ (k : ℝ))`.
  have hO : dSQ ε =O[atTop] (fun r => r ^ (k : ℝ)) := by
    rw [isBigO_iff]
    refine ⟨C, ?_⟩
    filter_upwards [hCk, eventually_ge_atTop (0 : ℝ)] with r hr hr0
    simp only [dSQ] at hr ⊢
    have hrk : r ^ (k : ℝ) = r ^ k := Real.rpow_natCast r k
    rw [hrk, Real.norm_of_nonneg (Real.exp_pos _).le,
        Real.norm_of_nonneg (pow_nonneg hr0 k)]
    exact hr
  -- Compose with the little-o: `dSQ ε =o[atTop] dSQ ε`.
  have hself : dSQ ε =o[atTop] dSQ ε :=
    hO.trans_isLittleO (poly_isLittleO_dSQ ε hε (k : ℝ))
  -- A self-little-o forces the function ≤ half its own norm somewhere in `atTop`.
  have hhalf : ∀ᶠ r in atTop, ‖dSQ ε r‖ ≤ (1 / 2) * ‖dSQ ε r‖ :=
    (hself.bound (by norm_num : (0 : ℝ) < 1 / 2))
  obtain ⟨r, hr⟩ := hhalf.exists
  -- But `dSQ ε r = Real.exp _ > 0`, so `exp ≤ exp / 2` is impossible.
  simp only [dSQ] at hr
  rw [Real.norm_of_nonneg (Real.exp_pos _).le] at hr
  have hpos : 0 < Real.exp (ε * r) := Real.exp_pos _
  linarith

end ParityCounterexample
