/-
Copyright (c) 2026 Mykola Palamarchuk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mykola Palamarchuk
-/
import Mathlib.Tactic.IntervalCases
import ALT.PolyTime

/-!
# A native bit-logic gate library

The native cost model charges one step per AST unfolding and runs every bounded recursion for its
full iteration count, so arithmetic on a magnitude-`v` operand costs `Θ(v)` — linear in the
*value*, not in the number of bits. Equality of general natural-number labels is therefore out of
reach in polynomial time on this model.

Computing with bits is not. Each gate below recurses on a bit rather than on a value, and each is
**bit-closed**: its `val` is `0` or `1` whatever the input. Every gate comes with a `val` law, an
`RfindFree` certificate (no unbounded search: the gates are total), and a `tc` bound linear in the
input value — hence constant on bits, which is what the `tc_*_bit` bricks at the end state
outright.

`cShape0` is the reshaping `n ↦ ⟨0, n⟩` that lets a bounded recursion recurse on a bare input.
`cIsPos` and `cNot` are the two gates that recurse; `cSwap` is a pure rewiring; and `cOr`, `cAnd`
and `cEqBit` are composed over those, the last two by De Morgan, so they carry no recursion of
their own. The `tc` bounds all go through the uniform `tc_prec_le`.

The module is deliberately a leaf over the cost model: these are Boolean primitives, and know
nothing of the learners and arithmetic codes assembled from them.
-/

-- "deliberately a leaf … knows nothing of the learners … assembled from them"
assert_not_exists OneDL.solve_decides

namespace OneDL

open Nat.Partrec (Code)
open Nat.Partrec.Code
open TimeCost

/-- Reshape `n ↦ ⟨0, n⟩` so a `prec` recurses on the value `n` (seed `0`). -/
def cShape0 : Code := pair zero (pair left right)

theorem rfindFree_cShape0 : RfindFree cShape0 := ⟨trivial, trivial, trivial⟩

theorem val_cShape0 (n : ℕ) : val cShape0 n = Nat.pair 0 n := by
  simp only [cShape0, val_pair, val_zero, val_left, val_right, Nat.pair_unpair]

theorem tc_cShape0 (n : ℕ) : tc cShape0 n = 5 := by
  simp only [cShape0, tc_pair, tc_zero, tc_left, tc_right]

/-- `[n ≠ 0]` as a `prec` recursing on the value: base `0`, step `1`. -/
def isPosCore : Code := prec zero (constCode 1)
/-- Positivity indicator `n ↦ [n ≠ 0]` (bit-closed). -/
def cIsPos : Code := comp isPosCore cShape0

theorem rfindFree_isPosCore : RfindFree isPosCore := ⟨trivial, rfindFree_constCode 1⟩
theorem rfindFree_cIsPos : RfindFree cIsPos := ⟨rfindFree_isPosCore, rfindFree_cShape0⟩

theorem val_isPosCore (a n : ℕ) : val isPosCore (Nat.pair a n) = if n = 0 then 0 else 1 := by
  unfold isPosCore
  cases n with
  | zero => rw [val_prec_zero]; simp [val_zero]
  | succ k => rw [val_prec_succ, val_constCode]; simp

theorem val_cIsPos (n : ℕ) : val cIsPos n = if n = 0 then 0 else 1 := by
  rw [cIsPos, val_comp, val_cShape0, val_isPosCore]

theorem tc_isPosCore_le (a n : ℕ) : tc isPosCore (Nat.pair a n) ≤ 4 * n + 2 := by
  unfold isPosCore
  have h := tc_prec_le (cf := zero) (cg := constCode 1) (B := 3)
    (fun x => tc_constCode_le 1 x) a n
  simp only [tc_zero] at h
  omega

theorem tc_cIsPos_le (n : ℕ) : tc cIsPos n ≤ 4 * n + 8 := by
  rw [cIsPos, tc_comp, tc_cShape0, val_cShape0]
  have := tc_isPosCore_le 0 n
  omega

/-- Negation `n ↦ [n = 0]` (bit-closed). -/
def notCore : Code := prec (constCode 1) zero

/-- `notCore` on a bare input: `cShape0` reshapes `n ↦ ⟨0, n⟩` so the `prec` recurses on `n`
itself, giving `val cNot n = [n = 0]`. -/
def cNot : Code := comp notCore cShape0

theorem rfindFree_notCore : RfindFree notCore := ⟨rfindFree_constCode 1, trivial⟩
theorem rfindFree_cNot : RfindFree cNot := ⟨rfindFree_notCore, rfindFree_cShape0⟩

theorem val_notCore (a n : ℕ) : val notCore (Nat.pair a n) = if n = 0 then 1 else 0 := by
  unfold notCore
  cases n with
  | zero => rw [val_prec_zero, val_constCode]; simp
  | succ k => rw [val_prec_succ]; simp [val_zero]

theorem val_cNot (n : ℕ) : val cNot n = if n = 0 then 1 else 0 := by
  rw [cNot, val_comp, val_cShape0, val_notCore]

theorem tc_notCore_le (a n : ℕ) : tc notCore (Nat.pair a n) ≤ 2 * n + 4 := by
  unfold notCore
  have h := tc_prec_le (cf := constCode 1) (cg := zero) (B := 1)
    (fun x => (tc_zero x).le) a n
  have hb := tc_constCode_le 1 a
  omega

theorem tc_cNot_le (n : ℕ) : tc cNot n ≤ 2 * n + 10 := by
  rw [cNot, tc_comp, tc_cShape0, val_cShape0]
  have := tc_notCore_le 0 n
  omega

/-- Swap `⟨a,b⟩ ↦ ⟨b,a⟩`. -/
def cSwap : Code := pair right left
theorem rfindFree_cSwap : RfindFree cSwap := ⟨trivial, trivial⟩
theorem val_cSwap (a b : ℕ) : val cSwap (Nat.pair a b) = Nat.pair b a := by
  simp only [cSwap, val_pair, val_left, val_right, Nat.unpair_pair]
theorem tc_cSwap (n : ℕ) : tc cSwap n = 3 := by simp only [cSwap, tc_pair, tc_left, tc_right]

/-- Disjunction `⟨a,b⟩ ↦ a ∨ b` (bit-closed): recurse on `a`, seed `b`. -/
def orCore : Code := prec cIsPos (constCode 1)

/-- `orCore` after `cSwap`. A `prec` recurses on its input's *second* component, so the swap puts
`a` there and `cOr ⟨a, b⟩` is the disjunction in the natural argument order. -/
def cOr : Code := comp orCore cSwap

theorem rfindFree_orCore : RfindFree orCore := ⟨rfindFree_cIsPos, rfindFree_constCode 1⟩
theorem rfindFree_cOr : RfindFree cOr := ⟨rfindFree_orCore, rfindFree_cSwap⟩

theorem val_orCore (b a : ℕ) :
    val orCore (Nat.pair b a) = if a = 0 then (if b = 0 then 0 else 1) else 1 := by
  unfold orCore
  cases a with
  | zero => rw [val_prec_zero, val_cIsPos]; simp
  | succ k => rw [val_prec_succ, val_constCode]; simp

theorem val_cOr (a b : ℕ) :
    val cOr (Nat.pair a b) = if a = 0 then (if b = 0 then 0 else 1) else 1 := by
  rw [cOr, val_comp, val_cSwap, val_orCore]

theorem tc_orCore_le (b a : ℕ) : tc orCore (Nat.pair b a) ≤ 4 * b + 4 * a + 9 := by
  unfold orCore
  have h := tc_prec_le (cf := cIsPos) (cg := constCode 1) (B := 3)
    (fun x => tc_constCode_le 1 x) b a
  have hb := tc_cIsPos_le b
  omega

theorem tc_cOr_le (a b : ℕ) : tc cOr (Nat.pair a b) ≤ 4 * a + 4 * b + 13 := by
  rw [cOr, tc_comp, tc_cSwap, val_cSwap]
  have := tc_orCore_le b a
  omega

/-- Conjunction `⟨a,b⟩ ↦ a ∧ b` via De Morgan (prec-free, bit-closed). -/
def cAnd : Code := comp cNot (comp cOr (pair (comp cNot left) (comp cNot right)))

theorem rfindFree_cAnd : RfindFree cAnd :=
  ⟨rfindFree_cNot, ⟨rfindFree_cOr, ⟨rfindFree_cNot, trivial⟩, ⟨rfindFree_cNot, trivial⟩⟩⟩

theorem val_cAnd (a b : ℕ) :
    val cAnd (Nat.pair a b) = if a = 0 then 0 else (if b = 0 then 0 else 1) := by
  simp only [cAnd, val_comp, val_pair, val_left, val_right, val_cNot, val_cOr, Nat.unpair_pair]
  by_cases ha : a = 0 <;> by_cases hb : b = 0 <;> simp [ha, hb]

/-- Bit-equality `⟨a,b⟩ ↦ [a = b]` on bits, via `(a ∧ b) ∨ (¬a ∧ ¬b)` (prec-free, bit-closed).
The general `val` law is "both zero, or both nonzero"; it coincides with equality exactly on the
binary regime `a, b ∈ {0,1}` (`val_cEqBit_bit`). -/
def cEqBit : Code :=
  comp cOr (pair cAnd (comp cAnd (pair (comp cNot left) (comp cNot right))))

theorem rfindFree_cEqBit : RfindFree cEqBit :=
  ⟨rfindFree_cOr, rfindFree_cAnd,
    ⟨rfindFree_cAnd, ⟨rfindFree_cNot, trivial⟩, ⟨rfindFree_cNot, trivial⟩⟩⟩

theorem val_cEqBit (a b : ℕ) :
    val cEqBit (Nat.pair a b)
      = if a = 0 then (if b = 0 then 1 else 0) else (if b = 0 then 0 else 1) := by
  simp only [cEqBit, val_comp, val_pair, val_left, val_right, val_cNot, val_cAnd, val_cOr,
    Nat.unpair_pair]
  by_cases ha : a = 0 <;> by_cases hb : b = 0 <;> simp [ha, hb]

/-- On bits, `cEqBit` genuinely tests equality. -/
theorem val_cEqBit_bit {a b : ℕ} (ha : a ≤ 1) (hb : b ≤ 1) :
    val cEqBit (Nat.pair a b) = if a = b then 1 else 0 := by
  interval_cases a <;> interval_cases b <;> simp [val_cEqBit]

/-- Every gate is **bit-closed**: `cIsPos` outputs a bit. -/
theorem val_cIsPos_le_one (n : ℕ) : val cIsPos n ≤ 1 := by rw [val_cIsPos]; split <;> simp
theorem val_cNot_le_one (n : ℕ) : val cNot n ≤ 1 := by rw [val_cNot]; split <;> simp
theorem val_cOr_le_one (a b : ℕ) : val cOr (Nat.pair a b) ≤ 1 := by
  rw [val_cOr]; split <;> [split <;> simp; simp]
theorem val_cAnd_le_one (a b : ℕ) : val cAnd (Nat.pair a b) ≤ 1 := by
  rw [val_cAnd]; split <;> [simp; split <;> simp]
theorem val_cEqBit_le_one (a b : ℕ) : val cEqBit (Nat.pair a b) ≤ 1 := by
  rw [val_cEqBit]; split <;> split <;> simp

/-- `tc` of the composite conjunction gate — linear in the input values (`O(1)` on bits). -/
theorem tc_cAnd_le (a b : ℕ) : tc cAnd (Nat.pair a b) ≤ 2 * a + 2 * b + 200 := by
  have e := tc_cNot_le a
  have f := tc_cNot_le b
  have g := tc_cOr_le (val cNot a) (val cNot b)
  have g' := tc_cNot_le (val cOr (Nat.pair (val cNot a) (val cNot b)))
  have ha := val_cNot_le_one a
  have hb := val_cNot_le_one b
  have hor := val_cOr_le_one (val cNot a) (val cNot b)
  simp only [cAnd, tc_comp, tc_pair, tc_left, tc_right, val_comp, val_left, val_right, val_pair,
    Nat.unpair_pair]
  omega

/-- `tc` of the composite bit-equality gate — linear in the input values (`O(1)` on bits). -/
theorem tc_cEqBit_le (a b : ℕ) : tc cEqBit (Nat.pair a b) ≤ 4 * a + 4 * b + 2000 := by
  have hA := tc_cAnd_le a b
  have hA2 := tc_cAnd_le (val cNot a) (val cNot b)
  have e := tc_cNot_le a
  have f := tc_cNot_le b
  have ha := val_cNot_le_one a
  have hb := val_cNot_le_one b
  have hAnd1 := val_cAnd_le_one a b
  have hAnd2 := val_cAnd_le_one (val cNot a) (val cNot b)
  have g := tc_cOr_le (val cAnd (Nat.pair a b))
    (val cAnd (Nat.pair (val cNot a) (val cNot b)))
  simp only [cEqBit, tc_comp, tc_pair, tc_left, tc_right, val_comp, val_left, val_right, val_pair,
    Nat.unpair_pair]
  omega

/-! ### Gate `tc`-on-bits bricks

On bit operands every gate runs a constant number of steps: the `prec`-based gates unfold `≤ 1`
times, the De-Morgan compositions are `prec`-free. -/

theorem tc_cIsPos_bit {x : ℕ} (h : x ≤ 1) : tc cIsPos x ≤ 12 := by
  have := tc_cIsPos_le x; omega
theorem tc_cNot_bit {x : ℕ} (h : x ≤ 1) : tc cNot x ≤ 12 := by
  have := tc_cNot_le x; omega
theorem tc_cOr_bit {a b : ℕ} (ha : a ≤ 1) (hb : b ≤ 1) : tc cOr (Nat.pair a b) ≤ 21 := by
  have := tc_cOr_le a b; omega
theorem tc_cAnd_bit {a b : ℕ} (ha : a ≤ 1) (hb : b ≤ 1) : tc cAnd (Nat.pair a b) ≤ 204 := by
  have := tc_cAnd_le a b; omega
theorem tc_cEqBit_bit {a b : ℕ} (ha : a ≤ 1) (hb : b ≤ 1) : tc cEqBit (Nat.pair a b) ≤ 2008 := by
  have := tc_cEqBit_le a b; omega

end OneDL
