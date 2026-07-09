import Mathlib

-- Tier-1 formal check, not Mathlib-destined: opt out of the house-style linters.
set_option linter.style.header false
set_option linter.style.longLine false

/-!
# Capacity threshold for rule-based encodings (Paper II, Corollary 2.2)

Provenance: `02_mdl_dominance_and_discovery.md`, §1.2 (regime constants C1–C3) and
§2.4 (Corollary 2.2), with the model-cost form `r + 2 log r + O(1)` from §2.2 eq. (1).

Status: PROVED as a pure real-arithmetic statement. This is the *arithmetic core* of
Corollary 2.2 only.

## What this DOES establish
* `Kmin r c₃ = r + 2·log r + c₃` names the representability threshold (Cor 2.2).
* `representable_of_C1`: the regime hypothesis **C1** (`K ≥ c₀·r·log(r/δ)`), under explicit
  NAMED constant conditions (`c₀ ≥ 3`, `0 < δ < 1`, the C3 buffer `r ≥ c₂ ≥ 3`,
  and `0 ≤ c₃ ≤ c₂`), entails `K ≥ Kmin` — i.e. in the regime the rule-based encoding
  is representable.
* `KminBits r c₃ = r + 2·log₂ r + c₃` is the bits-faithful threshold (matching §2.2's base-2
  coding); `MDLCoding.selfDelim_realizes_KminBits` proves it is *realized* by an actual
  self-delimiting code (`|selfDelim p| ≤ KminBits |p| 1`), so the `2 log r` framing overhead is a
  derived code length, not an assertion — content-checking Cor 2.2 as eq.(1)/eq.(2) ground Thm 2.1.

## What this does NOT establish (stays in prose; no overclaiming)
* No Kolmogorov complexity: `r`, `c₃`, `K` are abstract reals; we do not formalize `r = K(R)`.
* We derive only the *upper* bound `|selfDelim p| ≤ KminBits |p| 1` (above), not a matching lower
  bound, and not the natural-log `Kmin` as a literal code length (it is `KminBits` with the constant
  `1/log 2` absorbed into `c₀`).
* The part-(a) `iff` is *definitional* (`Iff.rfl`): it documents the threshold, it does not
  derive it from a coding model.
* Constants: the paper requires only `c₀,c₂ > 0` in the asymptotic regime `r → ∞`. This theorem
  fixes concrete bounds (`c₀ ≥ 3`, `c₂ ≥ 3`) and adds the coupling `c₃ ≤ c₂` (load-bearing),
  giving a concrete, non-asymptotic *sufficient* instance of Cor 2.2, not its asymptotic statement.

`Real.log` is the natural logarithm; constant base-change factors are absorbed into `c₀`,
exactly as in the paper's "O(·) with constants traceable in principle" convention.
-/

namespace CapacityThreshold

/-- Minimal model-description cost of the rule-based two-part encoding, in bits:
program length `r`, the Elias-δ self-delimiting overhead `2 log r`, and the
universal-evaluator overhead `c₃`. (Paper II §2.2 eq. (1), §2.4 Cor 2.2.) -/
noncomputable def Kmin (r c₃ : ℝ) : ℝ := r + 2 * Real.log r + c₃

/-- Bits-form capacity threshold (Cor 2.2), matching §2.2's base-2 coding: program length `r`
plus the Elias self-delimiting framing `2·log₂ r` plus `c₃`. The natural-log `Kmin` above is the
same threshold with the constant base-change `1/log 2` absorbed into `c₀` (paper's O(·) convention). -/
noncomputable def KminBits (r c₃ : ℝ) : ℝ := r + 2 * Real.logb 2 r + c₃

/-- A capacity `K` is *representable* (can host the rule-based encoding) iff it meets the
threshold `Kmin`. (Paper II, Corollary 2.2.) -/
def Representable (K r c₃ : ℝ) : Prop := Kmin r c₃ ≤ K

/-- Part (a): representability is exactly the capacity threshold. Definitional — this records
the statement of Corollary 2.2, it does not derive the threshold value. -/
theorem representable_iff_ge_Kmin (K r c₃ : ℝ) :
    Representable K r c₃ ↔ Kmin r c₃ ≤ K := Iff.rfl

/-- Part (b): in the regime, C1 entails representability.

Given the C1 capacity bound `K ≥ c₀·r·log(r/δ)`, the NAMED constant conditions force
`K ≥ Kmin r c₃`, i.e. the rule-based encoding is representable. The proof splits the
slack `c₀ ≥ 3` as `1 + 1 + 1` to dominate the three terms `r`, `2 log r`, and `c₃` of
`Kmin`. (Paper II, §1.2 C1/C3 + §2.4 Cor 2.2.) -/
theorem representable_of_C1
    (K r c₀ c₂ c₃ δ : ℝ)
    (hC1 : c₀ * r * Real.log (r / δ) ≤ K) -- C1 capacity bound
    (hc₀ : 3 ≤ c₀) -- discovery/retention slack (named)
    (hδ0 : 0 < δ) (hδ1 : δ < 1) -- confidence parameter in (0,1)
    (hC3 : c₂ ≤ r) -- C3 buffer: r above the invariance constant
    (hc₂ : 3 ≤ c₂) -- the buffer itself is ≥ 3
    (_hc₃0 : 0 ≤ c₃) (hc₃ : c₃ ≤ c₂) : -- evaluator cost ≥ 0 (documented) and below the buffer
    Representable K r c₃ := by
  have hr3 : (3 : ℝ) ≤ r := le_trans hc₂ hC3
  have hr0 : 0 < r := by linarith
  -- `1 ≤ log r`, since `r ≥ 3 > e`.
  have h1 : 1 ≤ Real.log r := by
    rw [Real.le_log_iff_exp_le hr0]
    have he : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
    linarith
  -- `r ≤ r/δ`, since `0 < δ < 1`.
  have hrd : r ≤ r / δ := by
    rw [le_div_iff₀ hδ0]
    nlinarith
  -- monotonicity of `log`
  have h2 : Real.log r ≤ Real.log (r / δ) := Real.log_le_log hr0 hrd
  -- the arithmetic core: `c₀·r·log(r/δ) ≥ r + 2 log r + c₃`
  have key : r + 2 * Real.log r + c₃ ≤ c₀ * r * Real.log (r / δ) := by
    nlinarith [mul_nonneg hr0.le (by linarith : (0 : ℝ) ≤ Real.log (r / δ) - 1),
               mul_le_mul_of_nonneg_left h2 hr0.le,
               mul_nonneg (by linarith : (0 : ℝ) ≤ r - 2) (by linarith : (0 : ℝ) ≤ Real.log r),
               mul_nonneg (by linarith : (0 : ℝ) ≤ c₀ - 3)
                 (mul_nonneg hr0.le (by linarith : (0 : ℝ) ≤ Real.log (r / δ)))]
  unfold Representable Kmin
  linarith [key, hC1]

end CapacityThreshold
