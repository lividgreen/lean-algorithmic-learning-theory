import Mathlib
import ALT.CapacityThreshold

-- Tier-1 formal check, not Mathlib-destined: opt out of the house-style header linter.
set_option linter.style.header false

/-!
# Retention capacity overhead (Paper II, §4.4 eq. (4))

Provenance: `02_mdl_dominance_and_discovery.md`, §4.3 (conditional-regeneration architecture,
Def 4.1 / Prop 4.2) and §4.4 (capacity overhead, eq. (4)), with the persistent-code cost
`|s_code| = r + 2 log r` reused from `CapacityThreshold.Kmin` (the §2.2 model cost at `c₃ = 0`).

Status: PROVED as pure real-arithmetic statements. This is the *arithmetic core* of the §4.4
capacity-overhead claim only.

## What this DOES establish
* `overhead_eq`: eq. (4)'s decomposition — the overhead is the persistent code
  `|s_code| = Kmin r 0 = r + 2 log r`, plus the working-memory term `c₆·r` and the consolidated
  routing/quantization term `c₇·log(r/δ)`. Pure algebra; reuses the warm-up's `Kmin`.
* `overhead_bigO`: under an explicit NAMED regime, the overhead is bounded by the explicit
  constant `c₆ + c₇ + 3` times `r·log(r/δ)` — a concrete-constant instance of eq. (4)'s
  `g(r,δ) = O(r·log(r/δ))` claim, completing the static Paper II arithmetic picture.

## What this does NOT establish (stays in prose; no overclaiming)
* No Kolmogorov complexity: `r`, `δ`, `c₆`, `c₇` are abstract reals; we do not formalize `r = K(R)`.
* No Cheng (2026) context-channel-capacity bound; in particular NOT Prop 4.2's `δ/2` retention
  probability — that is the prose content of §4.1–§4.3.
* We do not derive the three §4.4 component bounds (context-routing `O(log r)`, MML quantization
  `O(log(1/δ))`, working memory `O(r)`) FROM the architecture. We take eq. (4)'s *form* as given
  and prove only the resulting arithmetic. The two §4.4 bullets `O(log r)` and `O(log(1/δ))` are
  consolidated into the single `c₇·log(r/δ)` term, since `log(r/δ) = log r + log(1/δ)`, exactly
  as eq. (4) writes them.
* One-sided **upper** bound only: no matching lower bound (the paper's "matches the conjectured
  capacity bound" is the C1 side, handled separately/in prose). A pointwise explicit-constant
  bound, NOT a `Filter`/`Asymptotics.IsBigO` limit statement.

## Hypotheses: paper-stated vs added/strengthened
* Paper-stated / faithful: the eq. (4) term structure; `c₆, c₇ ≥ 0`; `0 < δ < 1` (confidence
  parameter).
* Added (concrete instance): `3 ≤ r` is the concrete C3 buffer (`r ≥ c₂ ≥ 3`, same as the
  warm-up), which forces `log(r/δ) ≥ 1`. The explicit constant `c₆ + c₇ + 3` is a concrete
  witness for the `O(·)`; the paper asserts only the *existence* of such a constant. Same
  concrete-instance pattern as `CapacityThreshold.representable_of_C1`.

`Real.log` is the natural logarithm; constant base-change factors are absorbed into `c₆, c₇`,
as in the paper's "O(·) with constants traceable in principle" convention.
-/

namespace RetentionOverhead

open CapacityThreshold

/-- Capacity overhead of the conditional-regeneration architecture (Paper II §4.4 eq. (4)):
the persistent code `|s_code| = r + 2 log r = Kmin r 0`, plus working memory `c₆·r` (sufficient
to simulate one step of a length-`r` program) and the consolidated routing/quantization term
`c₇·log(r/δ)` (context-routing `O(log r)` and MML quantization `O(log(1/δ))`, since
`log(r/δ) = log r + log(1/δ)`). -/
noncomputable def g (r δ c₆ c₇ : ℝ) : ℝ :=
  r + 2 * Real.log r + c₆ * r + c₇ * Real.log (r / δ)

/-- Eq. (4), decomposition form: the overhead is `|s_code|` (= `Kmin r 0`) plus the
working-memory term `c₆·r` and the routing/quantization term `c₇·log(r/δ)`. Pure algebra;
reuses the warm-up's `Kmin`. -/
theorem overhead_eq (r δ c₆ c₇ : ℝ) :
    g r δ c₆ c₇ = Kmin r 0 + c₆ * r + c₇ * Real.log (r / δ) := by
  simp only [g, Kmin]; ring

/-- Eq. (4), `O(r·log(r/δ))` form (arithmetic core): in the regime the overhead is bounded by
the explicit constant `c₆ + c₇ + 3` times `r·log(r/δ)`. The four terms of `g` are each dominated
by their `r·log(r/δ)` counterpart: `r ≤ r·ℓ` and `c₆·r ≤ c₆·r·ℓ` (since `ℓ := log(r/δ) ≥ 1`),
`2 log r ≤ 2·r·ℓ` (since `log r ≤ ℓ` and `r ≥ 1`), and `c₇·ℓ ≤ c₇·r·ℓ` (since `r ≥ 1`). All five
hypotheses are load-bearing. (Paper II §1.2 C3 buffer + §4.4 eq. (4).) -/
theorem overhead_bigO (r δ c₆ c₇ : ℝ)
    (hr : 3 ≤ r) -- C3 buffer r ≥ c₂ ≥ 3 (concrete instance; gives log(r/δ) ≥ 1)
    (hδ0 : 0 < δ) (hδ1 : δ < 1) -- confidence parameter in (0,1) → r ≤ r/δ
    (hc₆ : 0 ≤ c₆) (hc₇ : 0 ≤ c₇) : -- nonneg architecture constants
    g r δ c₆ c₇ ≤ (c₆ + c₇ + 3) * r * Real.log (r / δ) := by
  have hr0 : 0 < r := by linarith
  -- `r ≤ r/δ`, since `0 < δ < 1`.
  have hrd : r ≤ r / δ := by
    rw [le_div_iff₀ hδ0]; nlinarith
  -- `r/δ ≥ 3 > e`, hence `1 ≤ log(r/δ)`.
  have hℓ1 : 1 ≤ Real.log (r / δ) := by
    rw [Real.le_log_iff_exp_le (by positivity)]
    have he : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
    linarith
  -- monotonicity of `log`: `log r ≤ log(r/δ)`.
  have hlog : Real.log r ≤ Real.log (r / δ) := Real.log_le_log hr0 hrd
  unfold g
  nlinarith [mul_nonneg hc₆ (mul_nonneg hr0.le (by linarith : (0 : ℝ) ≤ Real.log (r / δ) - 1)),
             mul_nonneg hc₇ (mul_nonneg (by linarith : (0 : ℝ) ≤ Real.log (r / δ))
               (by linarith : (0 : ℝ) ≤ r - 1)),
             mul_nonneg hr0.le (by linarith : (0 : ℝ) ≤ Real.log (r / δ) - 1),
             mul_nonneg (by linarith : (0 : ℝ) ≤ Real.log (r / δ)) (by linarith : (0 : ℝ) ≤ r - 1),
             hlog, hℓ1]

end RetentionOverhead
