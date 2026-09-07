/-
Copyright (c) 2026 Mykola Palamarchuk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mykola Palamarchuk
-/
import ALT.PrefixMachine

-- Formal-check file, not Mathlib-destined: opt out of the house-style header linter.
set_option linter.style.header false

/-!
# The algorithmic probability on the universal prefix machine ([Discovery] §1.1, FV-21)

Provenance: [Discovery] §1.1 and FV-21, over the universal prefix machine `PrefixMachine.KB`.
Extends `ALT/PrefixMachine.lean` (`pfy`, `KB`, `kbWeight`, `kraft_KB`).

## What this establishes

* `QB`: the algorithmic probability — the total Kraft weight of the descriptions decoding to `x`
  on the universal prefix machine.
* `two_pow_neg_KB_le_QB`: the shortest description is one term of the sum, so `2⁻ᴷᴮ⁽ˣ⁾ ≤ QB x`.
* `sum_QB_le_one`, `tsum_QB_le_one`: `QB` is a semimeasure.
* `LowerSemicomputable`: a computable, monotone, rational (here: `ℕ`-over-`2^t`) approximation
  rising to the limit — the definition the coding theorem is stated for.

## What this does NOT establish (flagged)

`QB_lsc` (`LowerSemicomputable QB`) — the boundary this module once flagged — is established in
`ALT/CodingTheoremBitwise.lean`, over the bit-string computability layer of
`ALT/BitStringPrimrec.lean`.
-/

namespace PrefixMachine

open Nat.Partrec Nat.Partrec.Code AdditiveComplexity CodeEvalLaws KolmogorovComplexity

/-! ## `QB`: the algorithmic probability -/

open scoped Classical in
/-- **The algorithmic probability of `x`** on the universal prefix machine: the total Kraft weight
of the descriptions decoding to `x`. -/
noncomputable def QB (x : ℕ) : ℝ :=
  ∑' cp : Code × List Bool, if x ∈ pfy cp.1 (bitsToNat cp.2) then kbWeight cp else 0

open scoped Classical in
theorem summable_QB_term (x : ℕ) :
    Summable fun cp : Code × List Bool =>
      if x ∈ pfy cp.1 (bitsToNat cp.2) then kbWeight cp else 0 := by
  apply summable_kbWeight.of_nonneg_of_le
  · intro cp
    by_cases h : x ∈ pfy cp.1 (bitsToNat cp.2) <;> simp [h, kbWeight_nonneg]
  · intro cp
    by_cases h : x ∈ pfy cp.1 (bitsToNat cp.2) <;> simp [h, kbWeight_nonneg]

theorem QB_nonneg (x : ℕ) : 0 ≤ QB x := by
  unfold QB
  apply tsum_nonneg
  intro cp
  by_cases h : x ∈ pfy cp.1 (bitsToNat cp.2) <;> simp [h, kbWeight_nonneg]

open scoped Classical in
/-- The shortest description is one term of the sum. -/
theorem two_pow_neg_KB_le_QB (x : ℕ) : (1 / 2 : ℝ) ^ KB x ≤ QB x := by
  set cp₀ : Code × List Bool := (minDescCode x, minDescArg x) with hcp₀
  have hspec := minDesc_spec x
  have hmemS : minDescArg x ∈ natToBits '' (pfy (minDescCode x)).Dom :=
    ⟨bitsToNat (minDescArg x), Part.dom_iff_mem.mpr ⟨x, hspec.1⟩, natToBits_bitsToNat _⟩
  have hterm :
      (if x ∈ pfy cp₀.1 (bitsToNat cp₀.2) then kbWeight cp₀ else 0) = (1 / 2 : ℝ) ^ KB x := by
    rw [if_pos hspec.1]
    unfold kbWeight
    simp only [hcp₀]
    rw [if_pos hmemS, hspec.2]
  calc (1 / 2 : ℝ) ^ KB x
      = (if x ∈ pfy cp₀.1 (bitsToNat cp₀.2) then kbWeight cp₀ else 0) := hterm.symm
    _ ≤ QB x := (summable_QB_term x).le_tsum cp₀ (fun cp' _ => by
        by_cases h : x ∈ pfy cp'.1 (bitsToNat cp'.2) <;> simp [h, kbWeight_nonneg])

/-- `QB` is a semimeasure: the descriptions witnessing distinct `x` are disjoint (a fixed
description decodes to at most one value), so a finite sum of `QB` values is a genuine subsum of
the pair-indexed Kraft sum, bounded as `kraft_KB` bounds it. -/
theorem sum_QB_le_one (F : Finset ℕ) : ∑ x ∈ F, QB x ≤ 1 := by
  classical
  have hswap : ∑ x ∈ F, QB x =
      ∑' cp : Code × List Bool, ∑ x ∈ F,
        (if x ∈ pfy cp.1 (bitsToNat cp.2) then kbWeight cp else 0) :=
    (Summable.tsum_finsetSum (fun x _ => summable_QB_term x)).symm
  rw [hswap]
  have hcol : ∀ cp : Code × List Bool,
      ∑ x ∈ F, (if x ∈ pfy cp.1 (bitsToNat cp.2) then kbWeight cp else 0) ≤ kbWeight cp := by
    intro cp
    by_cases hex : ∃ x ∈ F, x ∈ pfy cp.1 (bitsToNat cp.2)
    · obtain ⟨x₀, hx₀F, hx₀⟩ := hex
      rw [Finset.sum_eq_single x₀]
      · simp [hx₀]
      · intro x _ hxne
        by_cases hx : x ∈ pfy cp.1 (bitsToNat cp.2)
        · exact absurd (Part.mem_unique hx hx₀) hxne
        · simp [hx]
      · exact fun hx₀F' => absurd hx₀F hx₀F'
    · push Not at hex
      have hzero : ∑ x ∈ F, (if x ∈ pfy cp.1 (bitsToNat cp.2) then kbWeight cp else 0) = 0 :=
        Finset.sum_eq_zero (fun x hx => if_neg (hex x hx))
      rw [hzero]
      exact kbWeight_nonneg cp
  have hsummableCol : Summable fun cp : Code × List Bool =>
      ∑ x ∈ F, (if x ∈ pfy cp.1 (bitsToNat cp.2) then kbWeight cp else 0) :=
    summable_sum (fun x _ => summable_QB_term x)
  calc ∑' cp : Code × List Bool, ∑ x ∈ F,
        (if x ∈ pfy cp.1 (bitsToNat cp.2) then kbWeight cp else 0)
      ≤ ∑' cp : Code × List Bool, kbWeight cp :=
        Summable.tsum_le_tsum hcol hsummableCol summable_kbWeight
    _ ≤ 1 := by
        rw [summable_kbWeight.tsum_prod' summable_row]
        calc ∑' c : Code, ∑' p, kbWeight (c, p) ≤ ∑' c : Code, (1 / 2 : ℝ) ^ elen c :=
              Summable.tsum_le_tsum tsum_row_le summable_tsum_row summable_elen
          _ ≤ 1 := by simpa [elen] using kraft_KP_E

private theorem summable_QB : Summable QB :=
  summable_of_sum_le QB_nonneg sum_QB_le_one

theorem tsum_QB_le_one : ∑' x : ℕ, QB x ≤ 1 :=
  tsum_le_of_sum_le' zero_le_one sum_QB_le_one

/-! ## Lower-semicomputability -/

/-- A function is lower-semicomputable when a computable dyadic approximation `a t x / 2 ^ t` rises
to it from below: monotone in the stage, always a lower bound, and reaching arbitrarily close. -/
def LowerSemicomputable (μ : ℕ → ℝ) : Prop :=
  ∃ a : ℕ → ℕ → ℕ, Computable₂ a ∧
    (∀ t x, (a t x : ℝ) / 2 ^ t ≤ (a (t + 1) x : ℝ) / 2 ^ (t + 1)) ∧
    (∀ t x, (a t x : ℝ) / 2 ^ t ≤ μ x) ∧
    (∀ x (q : ℝ), q < μ x → ∃ t, q < (a t x : ℝ) / 2 ^ t)

end PrefixMachine
