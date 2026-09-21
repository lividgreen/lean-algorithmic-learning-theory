/-
Copyright (c) 2026 Mykola Palamarchuk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mykola Palamarchuk
-/
module

public import ALT.AlgorithmicProbability

-- Formal-check file, not Mathlib-destined: opt out of the house-style header linter.
set_option linter.style.header false

/-!
# Toward the coding theorem with a logarithmic loss ([Discovery] §1.1, FV-21)

Provenance: [Discovery] §1.1 and FV-21, over the universal prefix machine `PrefixMachine.KB` and
the algorithmic probability `PrefixMachine.QB`. Extends `ALT/AlgorithmicProbability.lean`.

## What this establishes

The two combinatorial ingredients of the weak coding theorem's codeword and Markov's bound on the
number of level-`k` requests, none of which needs the decoder's effectiveness:

* `gammaCode`, `gammaCode_injective`, `gammaCode_prefixFree`, `length_gammaCode`: a self-delimiting
  unary-length header code — a bit-string's own leading run of `false`s recovers its own length, so
  no `gammaCode k` is a proper prefix of another's extension.
* `bitsFixed`, `ofBitsFixed`, `length_bitsFixed`, `ofBitsFixed_bitsFixed`: a fixed-width binary code
  and its inverse.
* `card_exceeds_lt`: Markov's bound — fewer than `2 ^ k` objects carry mass above `2 ^ (-k)` under a
  semimeasure.

## What this does NOT establish (flagged)

* The `O(1)` coding theorem and the online Kraft–Chaitin invariant it needs are not attempted here.

The coding theorem itself (`coding_theorem_weak`) and `QB_lsc` — the boundaries this module once
flagged, over the bit-string computability layer of `ALT/BitStringPrimrec.lean` — are established
in `ALT/CodingTheoremBitwise.lean` and `ALT/CodingTheoremDecoder.lean`.
-/


@[expose] public section

namespace PrefixMachine

open Nat.Partrec Nat.Partrec.Code AdditiveComplexity CodeEvalLaws KolmogorovComplexity

/-! ## A self-delimiting unary-length header code -/

/-- A self-delimiting code of a natural: a unary length header (as many `false`s as `natToBits k`
is long), a `true` stop bit, then the binary digits of `k` themselves. -/
def gammaCode (k : ℕ) : List Bool :=
  List.replicate (natToBits k).length false ++ [true] ++ natToBits k

theorem length_gammaCode_eq (k : ℕ) : (gammaCode k).length = 2 * (natToBits k).length + 1 := by
  simp [gammaCode]; omega

/-- At its own header length, `gammaCode k` (extended by anything) reads the stop bit. -/
private theorem gammaCode_getElem_length (k : ℕ) (r : List Bool) :
    (gammaCode k ++ r)[(natToBits k).length]? = some true := by
  simp [gammaCode, List.append_assoc]

/-- Before its header length, `gammaCode k` (extended by anything) reads a header `false`. -/
private theorem gammaCode_getElem_lt {k i : ℕ} (h : i < (natToBits k).length) (r : List Bool) :
    (gammaCode k ++ r)[i]? = some false := by
  simp [gammaCode, List.append_assoc, List.getElem?_append, h]

/-- **Parse uniqueness for `gammaCode`.** No `gammaCode k` is a proper prefix of another's
extension: the leading run of `false`s recovers its own length exactly. -/
theorem gammaCode_append_inj (k₁ k₂ : ℕ) (r₁ r₂ : List Bool)
    (h : gammaCode k₁ ++ r₁ = gammaCode k₂ ++ r₂) : k₁ = k₂ ∧ r₁ = r₂ := by
  have hLeq : (natToBits k₁).length = (natToBits k₂).length := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · have h1 : (gammaCode k₁ ++ r₁)[(natToBits k₁).length]? = some true :=
        gammaCode_getElem_length k₁ r₁
      have h2 : (gammaCode k₂ ++ r₂)[(natToBits k₁).length]? = some false :=
        gammaCode_getElem_lt hlt r₂
      rw [← h, h1] at h2
      exact absurd h2 (by simp)
    · have h1 : (gammaCode k₂ ++ r₂)[(natToBits k₂).length]? = some true :=
        gammaCode_getElem_length k₂ r₂
      have h2 : (gammaCode k₁ ++ r₁)[(natToBits k₂).length]? = some false :=
        gammaCode_getElem_lt hlt r₁
      rw [h, h1] at h2
      exact absurd h2 (by simp)
  have hhead' : (List.replicate (natToBits k₁).length false ++ [true]) ++ (natToBits k₁ ++ r₁)
      = (List.replicate (natToBits k₁).length false ++ [true]) ++ (natToBits k₂ ++ r₂) := by
    have e1 : gammaCode k₁ ++ r₁
        = (List.replicate (natToBits k₁).length false ++ [true]) ++ (natToBits k₁ ++ r₁) := by
      simp [gammaCode, List.append_assoc]
    have e2 : gammaCode k₂ ++ r₂
        = (List.replicate (natToBits k₁).length false ++ [true]) ++ (natToBits k₂ ++ r₂) := by
      simp [gammaCode, ← hLeq, List.append_assoc]
    rw [← e1, ← e2]
    exact h
  have htail : natToBits k₁ ++ r₁ = natToBits k₂ ++ r₂ :=
    (List.append_inj hhead' rfl).2
  obtain ⟨hnk, hr⟩ := List.append_inj htail hLeq
  refine ⟨?_, hr⟩
  have := congrArg bitsToNat hnk
  simpa [bitsToNat_natToBits] using this

/-- **The serialization is injective.** -/
theorem gammaCode_injective : Function.Injective gammaCode := fun k₁ k₂ h =>
  (gammaCode_append_inj k₁ k₂ [] [] (by simpa using h)).1

/-- **The serialization is prefix-free.** -/
theorem gammaCode_prefixFree : PrefixFree (Set.range gammaCode) := by
  rintro p ⟨k₁, rfl⟩ q ⟨k₂, rfl⟩ ⟨r, hr⟩
  obtain ⟨hk, hr0⟩ := gammaCode_append_inj k₁ k₂ r [] (by simpa using hr)
  rw [hk]

theorem length_gammaCode (k : ℕ) : (gammaCode k).length ≤ 2 * Nat.size k + 1 := by
  rw [length_gammaCode_eq]
  have h1 : (natToBits k).length + 1 = Nat.size (k + 1) := length_natToBits k
  have h2 : Nat.size (k + 1) ≤ Nat.size k + 1 := by
    rw [Nat.size_le]
    calc k + 1 ≤ 2 ^ Nat.size k := Nat.lt_size_self k
      _ < 2 ^ Nat.size k + 2 ^ Nat.size k := by
          have : 0 < 2 ^ Nat.size k := Nat.two_pow_pos _
          omega
      _ = 2 ^ (Nat.size k + 1) := by rw [pow_succ]; ring
  omega

/-! ## A fixed-width binary code -/

/-- The `k`-bit binary representation of `i`, most-significant-bit first, padded with leading
zeros to width `k` (unlike `natToBits`, which drops them). -/
def bitsFixed : ℕ → ℕ → List Bool
  | 0, _ => []
  | k + 1, i => bitsFixed k (i / 2) ++ [decide (i % 2 = 1)]

theorem length_bitsFixed (k i : ℕ) : (bitsFixed k i).length = k := by
  induction k generalizing i with
  | zero => simp [bitsFixed]
  | succ k ih => simp [bitsFixed, ih]

/-- The inverse of `bitsFixed`: read a bit-string as a natural, most-significant-bit first. -/
def ofBitsFixed (l : List Bool) : ℕ := l.foldl (fun acc b => 2 * acc + b.toNat) 0

theorem ofBitsFixed_bitsFixed {k i : ℕ} (h : i < 2 ^ k) : ofBitsFixed (bitsFixed k i) = i := by
  induction k generalizing i with
  | zero =>
      have : i = 0 := by simpa using h
      simp [bitsFixed, ofBitsFixed, this]
  | succ k ih =>
      have hi2 : i / 2 < 2 ^ k := by
        rw [pow_succ] at h
        omega
      unfold bitsFixed
      unfold ofBitsFixed
      rw [List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      have : (bitsFixed k (i / 2)).foldl (fun acc b => 2 * acc + b.toNat) 0 = i / 2 :=
        ih hi2
      rw [this]
      rcases Nat.mod_two_eq_zero_or_one i with hmod | hmod <;> simp [hmod] <;> omega

/-! ## Markov's bound -/

/-- **Markov's bound**: fewer than `2 ^ k` objects carry mass above `2 ^ (-k)` under a
semimeasure. -/
theorem card_exceeds_lt {μ : ℕ → ℝ} (_hnn : ∀ x, 0 ≤ μ x) (hsum : ∀ F : Finset ℕ, ∑ x ∈ F, μ x ≤ 1)
    (k : ℕ) (F : Finset ℕ) (hF : ∀ x ∈ F, (1 / 2 : ℝ) ^ k < μ x) : F.card < 2 ^ k := by
  by_contra hle
  push Not at hle
  have hFne : F.Nonempty := Finset.card_pos.mp (lt_of_lt_of_le (Nat.two_pow_pos k) hle)
  have hlt : ∑ x ∈ F, (1 / 2 : ℝ) ^ k < ∑ x ∈ F, μ x :=
    Finset.sum_lt_sum_of_nonempty hFne hF
  rw [Finset.sum_const, nsmul_eq_mul] at hlt
  have heq : (F.card : ℝ) * (1 / 2 : ℝ) ^ k ≥ 1 := by
    have h2 : ((2 ^ k : ℕ) : ℝ) * (1 / 2 : ℝ) ^ k = 1 := by
      push_cast
      rw [mul_comm, ← mul_pow]
      norm_num
    have hcard : ((2 ^ k : ℕ) : ℝ) ≤ (F.card : ℝ) := by exact_mod_cast hle
    have hpos : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ k := by positivity
    calc (1 : ℝ) = ((2 ^ k : ℕ) : ℝ) * (1 / 2 : ℝ) ^ k := h2.symm
      _ ≤ (F.card : ℝ) * (1 / 2 : ℝ) ^ k := by
          apply mul_le_mul_of_nonneg_right hcard hpos
  have := hsum F
  linarith

end PrefixMachine
