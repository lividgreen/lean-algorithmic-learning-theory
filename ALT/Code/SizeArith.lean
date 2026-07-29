/-
Copyright (c) 2026 Mykola Palamarchuk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mykola Palamarchuk
-/
import Mathlib.Data.Nat.Pairing
import Mathlib.Data.Nat.Size
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Bit-length arithmetic for size accounts

Bounding how much room a computation needs comes down, over and over, to two facts about
`Nat.size` that Mathlib does not state: what pairing costs in bits, and how a bit-length compares
with the value it measures. Mathlib bounds `Nat.pair` monotonically, but says nothing about its
bit-length.

* `size_pair_le_max` — pairing costs at most twice the wider component. `Nat.pair x y` is Cantor's
  square pairing, so it lands strictly below `(2 ^ M) ^ 2` where `M` is the larger of the two
  bit-lengths. The constant `2` is attained: `Nat.pair 1 0 = 2`, of size `2 = 2 · 1`.
* `size_pair_le` — pairing costs at most twice each component, plus two. The `max`-free shape,
  which is what an additive account of a polynomial bound composes with.
* `size_le_self` — a bit-length never exceeds the value it measures. Available at zero, where the
  `max`-form bounds are not.

The module is deliberately a leaf: it is arithmetic on bit-lengths, and knows nothing about the
programs whose sizes are being counted.
-/

-- "knows nothing about the programs whose sizes are being counted"
assert_not_exists Nat.Partrec.Code

namespace CodeSizeArith

/-- **Square pairing costs at most twice the wider component.** `Nat.pair x y` is Cantor's square
pairing (`y² + x` or `x² + x + y`), so it lands strictly below `(2^M)²` where `M` is the larger of
the two bit-lengths: `Nat.size (Nat.pair x y) ≤ 2M`. The constant `2` is attained (`x = 1, y = 0`
gives `Nat.pair 1 0 = 2`, of size `2 = 2·1`). Mathlib bounds `Nat.pair` monotonically but does not
state its bit-length. -/
theorem size_pair_le_max (x y : ℕ) :
    Nat.size (Nat.pair x y) ≤ 2 * max (Nat.size x) (Nat.size y) := by
  set M := max (Nat.size x) (Nat.size y) with hM
  have hx : x < 2 ^ M :=
    Nat.lt_of_lt_of_le (Nat.lt_size_self x)
      (Nat.pow_le_pow_right (by norm_num) (le_max_left _ _))
  have hy : y < 2 ^ M :=
    Nat.lt_of_lt_of_le (Nat.lt_size_self y)
      (Nat.pow_le_pow_right (by norm_num) (le_max_right _ _))
  rw [Nat.size_le]
  have hpow : (2 : ℕ) ^ (2 * M) = 2 ^ M * 2 ^ M := by rw [two_mul, pow_add]
  rw [hpow, Nat.pair]
  split
  · next h => nlinarith
  · next h => nlinarith

/-- `Nat.size (Nat.pair a b) ≤ 2·Nat.size a + 2·Nat.size b + 2`: the pairing's output bit-length is
linear in the inputs' bit-lengths (so pairing preserves poly output size). -/
theorem size_pair_le (a b : ℕ) :
    Nat.size (Nat.pair a b) ≤ 2 * Nat.size a + 2 * Nat.size b + 2 := by
  rw [Nat.size_le]
  have ha : a < 2 ^ Nat.size a := Nat.lt_size_self a
  have hb : b < 2 ^ Nat.size b := Nat.lt_size_self b
  have hpair : Nat.pair a b ≤ (a + b + 1) ^ 2 := by
    unfold Nat.pair; split_ifs <;> nlinarith
  have hab : a + b + 1 < 2 ^ (Nat.size a + Nat.size b + 1) := by
    have e1 : (2 : ℕ) ^ Nat.size a ≤ 2 ^ (Nat.size a + Nat.size b) :=
      Nat.pow_le_pow_right (by norm_num) (Nat.le_add_right _ _)
    have e2 : (2 : ℕ) ^ Nat.size b ≤ 2 ^ (Nat.size a + Nat.size b) :=
      Nat.pow_le_pow_right (by norm_num) (Nat.le_add_left _ _)
    have e3 : (2 : ℕ) ^ (Nat.size a + Nat.size b + 1)
        = 2 ^ (Nat.size a + Nat.size b) + 2 ^ (Nat.size a + Nat.size b) := by
      rw [pow_succ]; ring
    omega
  calc Nat.pair a b ≤ (a + b + 1) ^ 2 := hpair
    _ < (2 ^ (Nat.size a + Nat.size b + 1)) ^ 2 := by
        exact Nat.pow_lt_pow_left hab (by norm_num)
    _ = 2 ^ (2 * Nat.size a + 2 * Nat.size b + 2) := by rw [← pow_mul]; ring_nf

/-- Widths never exceed the value. Safe at zero, unlike the `max`-form bounds. -/
theorem size_le_self (n : ℕ) : Nat.size n ≤ n := Nat.size_le.mpr Nat.lt_two_pow_self

end CodeSizeArith
