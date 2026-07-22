/-
Copyright (c) 2026 Mykola Palamarchuk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mykola Palamarchuk
-/
import ALT.DecisionListSolver

-- Formal-check file, not Mathlib-destined: opt out of the house-style header linter.
set_option linter.style.header false

/-!
# Arithmetic as explicit codes

`Nat.Partrec.Code` has eight constructors and no arithmetic primitive beyond `succ`: addition of two
variables, multiplication, truncated subtraction, powers and comparisons must each be built from
bounded recursion. This file builds them, each as a named code with its value equation.

## What is reused
The Boolean layer is already in the tree and is not rebuilt here — `cIsPos`, `cNot`, `cAnd`, `cOr`,
`cEqBit`, `cSwap` and `cShape0` come from the decision-list solver's bit-gate library, together with
their `≤ 1` bounds, and `constCode` from the polynomial-time layer. What is new here is the
numeric layer above them.

## The shape of every construction
Bounded recursion `prec cf cg` on input `Nat.pair a n` runs `cf` on `a` and then folds `cg` over
`n`, each step seeing `Nat.pair a (Nat.pair y acc)` — the original first argument, the counter, and
the accumulator. Every definition below is that fold: addition counts successors, multiplication
counts additions, powers count doublings, subtraction counts predecessors. The value laws are the
corresponding inductions, and each is stated at `Nat.pair`-shaped input because that is the shape
bounded recursion consumes.

No step-count facts are stated. Bounded recursion charges by the *value* of its counter in the
native step model, so an addition built this way costs steps proportional to the number it adds;
that is a property of the cost model, not of these codes, and the workspace account — which is what
consumes them — is unaffected.
-/

namespace CodeArith

open Nat.Partrec (Code)
open Nat.Partrec.Code
open TimeCost
open OneDL

/-! ## Projections and identity -/

@[simp] theorem val_left' (n : ℕ) : val left n = n.unpair.1 := rfl
@[simp] theorem val_right' (n : ℕ) : val right n = n.unpair.2 := rfl
@[simp] theorem val_zero' (n : ℕ) : val zero n = 0 := rfl
@[simp] theorem val_succ' (n : ℕ) : val succ n = n + 1 := rfl

/-- The identity code. -/
def cId : Code := pair left right

@[simp] theorem val_cId (n : ℕ) : val cId n = n := by
  rw [cId, val_pair, val_left', val_right', Nat.pair_unpair]

theorem rfindFree_cId : RfindFree cId := ⟨trivial, trivial⟩

/-- The accumulator of a bounded-recursion step: the third slot of `⟨a, ⟨y, acc⟩⟩`. -/
def cAcc : Code := comp right right

@[simp] theorem val_cAcc (a y m : ℕ) : val cAcc (Nat.pair a (Nat.pair y m)) = m := by
  rw [cAcc, val_comp, val_right', val_right', Nat.unpair_pair, Nat.unpair_pair]

theorem rfindFree_cAcc : RfindFree cAcc := ⟨trivial, trivial⟩

/-- The counter of a bounded-recursion step: the second slot of `⟨a, ⟨y, acc⟩⟩`. -/
def cCtr : Code := comp left right

@[simp] theorem val_cCtr (a y m : ℕ) : val cCtr (Nat.pair a (Nat.pair y m)) = y := by
  rw [cCtr, val_comp, val_right', val_left', Nat.unpair_pair, Nat.unpair_pair]

theorem rfindFree_cCtr : RfindFree cCtr := ⟨trivial, trivial⟩

/-! ## Addition -/

/-- Addition: `⟨x, y⟩ ↦ x + y`, counting `y` successors from `x`. -/
def cAdd : Code := prec cId (comp succ cAcc)

theorem val_cAdd (x y : ℕ) : val cAdd (Nat.pair x y) = x + y := by
  induction y with
  | zero =>
      change val (prec cId (comp succ cAcc)) (Nat.pair x 0) = x + 0
      rw [val_prec_zero, val_cId]
      omega
  | succ m ih =>
      change val (prec cId (comp succ cAcc)) (Nat.pair x (m + 1)) = x + (m + 1)
      rw [val_prec_succ]
      change val (comp succ cAcc) (Nat.pair x (Nat.pair m (val cAdd (Nat.pair x m)))) = x + (m + 1)
      rw [val_comp, val_cAcc, val_succ', ih]
      omega

theorem rfindFree_cAdd : RfindFree cAdd := ⟨rfindFree_cId, trivial, rfindFree_cAcc⟩

/-- Doubling, as an addition. -/
def cDbl : Code := comp cAdd (pair cId cId)

@[simp] theorem val_cDbl (n : ℕ) : val cDbl n = 2 * n := by
  rw [cDbl, val_comp, val_pair, val_cId, val_cAdd]
  omega

theorem rfindFree_cDbl : RfindFree cDbl := ⟨rfindFree_cAdd, rfindFree_cId, rfindFree_cId⟩

/-! ## Predecessor and truncated subtraction -/

/-- Predecessor, folded: at counter `y + 1` the answer is `y`. -/
def cPredCore : Code := prec zero cCtr

theorem val_cPredCore (a n : ℕ) : val cPredCore (Nat.pair a n) = n - 1 := by
  cases n with
  | zero =>
      change val (prec zero cCtr) (Nat.pair a 0) = 0 - 1
      rw [val_prec_zero, val_zero']
  | succ m =>
      change val (prec zero cCtr) (Nat.pair a (m + 1)) = m + 1 - 1
      rw [val_prec_succ]
      rw [val_cCtr]
      omega

/-- Predecessor as a one-argument code. -/
def cPred : Code := comp cPredCore cShape0

@[simp] theorem val_cPred (n : ℕ) : val cPred n = n - 1 := by
  rw [cPred, val_comp, val_cShape0, val_cPredCore]

theorem rfindFree_cPredCore : RfindFree cPredCore := ⟨trivial, rfindFree_cCtr⟩

theorem rfindFree_cShape0 : RfindFree cShape0 := ⟨trivial, trivial, trivial⟩

theorem rfindFree_cPred : RfindFree cPred := ⟨rfindFree_cPredCore, rfindFree_cShape0⟩

/-- Truncated subtraction: `⟨x, y⟩ ↦ x - y`, counting `y` predecessors from `x`. -/
def cSub : Code := prec cId (comp cPred cAcc)

theorem val_cSub (x y : ℕ) : val cSub (Nat.pair x y) = x - y := by
  induction y with
  | zero =>
      change val (prec cId (comp cPred cAcc)) (Nat.pair x 0) = x - 0
      rw [val_prec_zero, val_cId]
      omega
  | succ m ih =>
      change val (prec cId (comp cPred cAcc)) (Nat.pair x (m + 1)) = x - (m + 1)
      rw [val_prec_succ]
      change val (comp cPred cAcc) (Nat.pair x (Nat.pair m (val cSub (Nat.pair x m)))) = x - (m + 1)
      rw [val_comp, val_cAcc, val_cPred, ih]
      omega

theorem rfindFree_cSub : RfindFree cSub := ⟨rfindFree_cId, rfindFree_cPred, rfindFree_cAcc⟩

/-! ## Multiplication -/

/-- Multiplication: `⟨x, y⟩ ↦ x * y`, counting `y` additions of `x`. -/
def cMul : Code := prec zero (comp cAdd (pair left cAcc))

theorem val_cMul (x y : ℕ) : val cMul (Nat.pair x y) = x * y := by
  induction y with
  | zero =>
      change val (prec zero (comp cAdd (pair left cAcc))) (Nat.pair x 0) = x * 0
      rw [val_prec_zero, val_zero']
      omega
  | succ m ih =>
      change val (prec zero (comp cAdd (pair left cAcc))) (Nat.pair x (m + 1)) = x * (m + 1)
      rw [val_prec_succ]
      change val (comp cAdd (pair left cAcc))
          (Nat.pair x (Nat.pair m (val cMul (Nat.pair x m)))) = x * (m + 1)
      rw [val_comp, val_pair, val_left', val_cAcc, Nat.unpair_pair, val_cAdd, ih]
      ring

theorem rfindFree_cMul : RfindFree cMul := ⟨trivial, rfindFree_cAdd, trivial, rfindFree_cAcc⟩

/-! ## Powers of two -/

/-- Powers of two, folded: `⟨a, n⟩ ↦ 2 ^ n`, counting `n` doublings from `1`. -/
def cPow2Core : Code := prec (constCode 1) (comp cDbl cAcc)

theorem val_cPow2Core (a n : ℕ) : val cPow2Core (Nat.pair a n) = 2 ^ n := by
  induction n with
  | zero =>
      change val (prec (constCode 1) (comp cDbl cAcc)) (Nat.pair a 0) = 2 ^ 0
      rw [val_prec_zero, val_constCode]
      simp
  | succ m ih =>
      change val (prec (constCode 1) (comp cDbl cAcc)) (Nat.pair a (m + 1)) = 2 ^ (m + 1)
      rw [val_prec_succ]
      change val (comp cDbl cAcc)
          (Nat.pair a (Nat.pair m (val cPow2Core (Nat.pair a m)))) = 2 ^ (m + 1)
      rw [val_comp, val_cAcc, val_cDbl, ih, pow_succ]
      ring

/-- Powers of two as a one-argument code. -/
def cPow2 : Code := comp cPow2Core cShape0

@[simp] theorem val_cPow2 (n : ℕ) : val cPow2 n = 2 ^ n := by
  rw [cPow2, val_comp, val_cShape0, val_cPow2Core]

theorem rfindFree_cPow2Core : RfindFree cPow2Core :=
  ⟨rfindFree_constCode 1, rfindFree_cDbl, rfindFree_cAcc⟩

theorem rfindFree_cPow2 : RfindFree cPow2 := ⟨rfindFree_cPow2Core, rfindFree_cShape0⟩

/-! ## Comparison and equality

Truncated subtraction turns order into a zero test, which the bit-gate library already decides. -/

/-- `⟨x, y⟩ ↦ 1` when `x ≤ y`, else `0`. -/
def cLe : Code := comp cNot cSub

theorem val_cLe (x y : ℕ) : val cLe (Nat.pair x y) = if x ≤ y then 1 else 0 := by
  rw [cLe, val_comp, val_cSub, val_cNot]
  by_cases h : x ≤ y
  · rw [if_pos (by omega), if_pos h]
  · rw [if_neg (by omega), if_neg h]

theorem rfindFree_cLe : RfindFree cLe := ⟨rfindFree_cNot, rfindFree_cSub⟩

/-- `⟨x, y⟩ ↦ 1` when `x = y`, else `0`. -/
def cEq : Code := comp cAnd (pair cLe (comp cLe cSwap))

theorem val_cEq (x y : ℕ) : val cEq (Nat.pair x y) = if x = y then 1 else 0 := by
  rw [cEq, val_comp, val_pair, val_cLe, val_comp, val_cSwap, val_cLe, val_cAnd]
  by_cases h : x = y
  · subst h; simp
  · by_cases h1 : x ≤ y
    · rw [if_pos h1, if_neg (by omega : ¬ y ≤ x), if_neg h]
      simp
    · rw [if_neg h1, if_neg h]
      simp

theorem rfindFree_cEq : RfindFree cEq :=
  ⟨rfindFree_cAnd, rfindFree_cLe, rfindFree_cLe, rfindFree_cSwap⟩

/-! ## Selection

With a `{0,1}`-valued guard, selection is arithmetic: multiply each branch by its indicator and add.
This is the form the machine's branch conditions will take once they are decided by `cEq`. -/

/-- `⟨b, ⟨t, f⟩⟩ ↦ t` when `b ≠ 0`, else `f`. -/
def cIte : Code :=
  comp cAdd (pair (comp cMul (pair (comp cIsPos left) cCtr))
    (comp cMul (pair (comp cNot left) cAcc)))

theorem val_cIte (b t f : ℕ) :
    val cIte (Nat.pair b (Nat.pair t f)) = if b = 0 then f else t := by
  simp only [cIte, val_comp, val_pair, val_left', val_cCtr, val_cAcc, Nat.unpair_pair,
    val_cIsPos, val_cNot, val_cMul, val_cAdd]
  by_cases h : b = 0 <;> simp [h]

theorem rfindFree_cIte : RfindFree cIte :=
  ⟨rfindFree_cAdd,
    ⟨rfindFree_cMul, ⟨rfindFree_cIsPos, trivial⟩, rfindFree_cCtr⟩,
    ⟨rfindFree_cMul, ⟨rfindFree_cNot, trivial⟩, rfindFree_cAcc⟩⟩

/-! ## Bit-length

`Nat.size n` is the least `k` with `n < 2 ^ k`, so it is found by raising an accumulator while
`2 ^ acc` still fits below `n`. Folding that step `n` times is enough, since `Nat.size n ≤ n`. -/

/-- The `Nat.size` fold's step: raise the accumulator while `2 ^ acc` still fits. -/
def sizeStep : Code :=
  comp cIte (pair (comp cLe (pair (comp cPow2 cAcc) left)) (pair (comp succ cAcc) cAcc))

theorem val_sizeStep (a y m : ℕ) :
    val sizeStep (Nat.pair a (Nat.pair y m)) = if 2 ^ m ≤ a then m + 1 else m := by
  simp only [sizeStep, val_comp, val_pair, val_cPow2, val_cAcc, val_left', Nat.unpair_pair,
    val_cLe, val_succ', val_cIte]
  by_cases h : 2 ^ m ≤ a <;> simp [h]

theorem rfindFree_sizeStep : RfindFree sizeStep :=
  ⟨rfindFree_cIte, ⟨rfindFree_cLe, ⟨rfindFree_cPow2, rfindFree_cAcc⟩, trivial⟩,
    ⟨trivial, rfindFree_cAcc⟩, rfindFree_cAcc⟩

/-- The bit-length fold, run `m` times from zero. -/
def sizeCore : Code := prec zero sizeStep

theorem val_sizeCore (n : ℕ) : ∀ m, val sizeCore (Nat.pair n m) = min (Nat.size n) m := by
  intro m
  induction m with
  | zero =>
      change val (prec zero sizeStep) (Nat.pair n 0) = min (Nat.size n) 0
      rw [val_prec_zero, val_zero']
      omega
  | succ j ih =>
      change val (prec zero sizeStep) (Nat.pair n (j + 1)) = min (Nat.size n) (j + 1)
      rw [val_prec_succ]
      change val sizeStep (Nat.pair n (Nat.pair j (val sizeCore (Nat.pair n j))))
        = min (Nat.size n) (j + 1)
      rw [val_sizeStep, ih]
      by_cases h : Nat.size n ≤ j
      · have hmin : min (Nat.size n) j = Nat.size n := by omega
        rw [hmin, if_neg (by have := Nat.lt_size_self n; omega)]
        omega
      · have hmin : min (Nat.size n) j = j := by omega
        rw [hmin, if_pos (Nat.lt_size.1 (by omega))]
        omega

/-- Bit-length as a one-argument code. -/
def cSize : Code := comp sizeCore (pair cId cId)

@[simp] theorem val_cSize (n : ℕ) : val cSize n = Nat.size n := by
  rw [cSize, val_comp, val_pair, val_cId, val_sizeCore]
  have : Nat.size n ≤ n := Nat.size_le.2 (Nat.lt_two_pow_self)
  omega

theorem rfindFree_sizeCore : RfindFree sizeCore := ⟨trivial, rfindFree_sizeStep⟩

theorem rfindFree_cSize : RfindFree cSize :=
  ⟨rfindFree_sizeCore, rfindFree_cId, rfindFree_cId⟩

/-! ## Division and remainder

`n / d` is the number of `y` with `(y + 1) * d ≤ n`, so it too is a fold that raises an accumulator
while the next multiple still fits — guarded by `d > 0`, which makes the fold agree with the
convention `n / 0 = 0` rather than running away. Folding `n` times is enough. -/

/-- Inside the division fold, the two components of the original argument `⟨n, d⟩`. -/
def cArgN : Code := comp left left

/-- The divisor slot of the division fold's argument. -/
def cArgD : Code := comp right left

@[simp] theorem val_cArgN (n d y m : ℕ) :
    val cArgN (Nat.pair (Nat.pair n d) (Nat.pair y m)) = n := by
  rw [cArgN, val_comp, val_left', val_left', Nat.unpair_pair, Nat.unpair_pair]

@[simp] theorem val_cArgD (n d y m : ℕ) :
    val cArgD (Nat.pair (Nat.pair n d) (Nat.pair y m)) = d := by
  rw [cArgD, val_comp, val_left', val_right', Nat.unpair_pair, Nat.unpair_pair]

/-- The division fold's step: raise the quotient while the next multiple still fits. -/
def divStep : Code :=
  comp cIte
    (pair (comp cAnd (pair (comp cIsPos cArgD)
      (comp cLe (pair (comp cMul (pair (comp succ cAcc) cArgD)) cArgN))))
      (pair (comp succ cAcc) cAcc))

theorem val_divStep (n d y m : ℕ) :
    val divStep (Nat.pair (Nat.pair n d) (Nat.pair y m))
      = if 0 < d ∧ (m + 1) * d ≤ n then m + 1 else m := by
  simp only [divStep, val_comp, val_pair, val_cArgD, val_cArgN, val_cAcc, val_succ', val_cMul,
    val_cLe, val_cIsPos, val_cAnd, val_cIte]
  by_cases hd : d = 0
  · simp [hd]
  · by_cases hm : (m + 1) * d ≤ n <;> simp [hd, hm, Nat.pos_of_ne_zero hd]

theorem rfindFree_divStep : RfindFree divStep :=
  ⟨rfindFree_cIte,
    ⟨rfindFree_cAnd, ⟨rfindFree_cIsPos, trivial, trivial⟩,
      ⟨rfindFree_cLe, ⟨rfindFree_cMul, ⟨trivial, rfindFree_cAcc⟩, trivial, trivial⟩,
        trivial, trivial⟩⟩,
    ⟨trivial, rfindFree_cAcc⟩, rfindFree_cAcc⟩

/-- The division fold, run `m` times from zero. -/
def divCore : Code := prec zero divStep

theorem val_divCore (n d : ℕ) : ∀ m,
    val divCore (Nat.pair (Nat.pair n d) m) = min (n / d) m := by
  intro m
  induction m with
  | zero =>
      change val (prec zero divStep) (Nat.pair (Nat.pair n d) 0) = min (n / d) 0
      rw [val_prec_zero, val_zero']
      simp
  | succ j ih =>
      change val (prec zero divStep) (Nat.pair (Nat.pair n d) (j + 1)) = min (n / d) (j + 1)
      rw [val_prec_succ]
      change val divStep
          (Nat.pair (Nat.pair n d) (Nat.pair j (val divCore (Nat.pair (Nat.pair n d) j))))
        = min (n / d) (j + 1)
      rw [val_divStep, ih]
      rcases Nat.eq_zero_or_pos d with rfl | hd
      · simp
      · by_cases h : n / d ≤ j
        · have hmin : min (n / d) j = n / d := by omega
          have hno : ¬ (0 < d ∧ (n / d + 1) * d ≤ n) := by
            rintro ⟨-, hle⟩
            have := (Nat.le_div_iff_mul_le hd).2 hle
            omega
          rw [hmin, if_neg hno]
          omega
        · have hmin : min (n / d) j = j := by omega
          have hlt : (j + 1) * d ≤ n := (Nat.le_div_iff_mul_le hd).1 (by omega)
          rw [hmin, if_pos ⟨hd, hlt⟩]
          omega

/-- Division. -/
def cDiv : Code := comp divCore (pair cId left)

@[simp] theorem val_cDiv (n d : ℕ) : val cDiv (Nat.pair n d) = n / d := by
  rw [cDiv, val_comp, val_pair, val_cId, val_left', Nat.unpair_pair, val_divCore]
  have : n / d ≤ n := Nat.div_le_self n d
  omega

theorem rfindFree_divCore : RfindFree divCore := ⟨trivial, rfindFree_divStep⟩

theorem rfindFree_cDiv : RfindFree cDiv := ⟨rfindFree_divCore, rfindFree_cId, trivial⟩

/-- Remainder, from division and multiplication. -/
def cMod : Code := comp cSub (pair left (comp cMul (pair right cDiv)))

@[simp] theorem val_cMod (n d : ℕ) : val cMod (Nat.pair n d) = n % d := by
  rw [cMod, val_comp, val_pair, val_left', val_comp, val_pair, val_right', Nat.unpair_pair,
    val_cDiv, val_cMul, val_cSub]
  change n - d * (n / d) = n % d
  have h1 := Nat.div_add_mod n d
  omega

theorem rfindFree_cMod : RfindFree cMod :=
  ⟨rfindFree_cSub, trivial, rfindFree_cMul, trivial, rfindFree_cDiv⟩

end CodeArith
