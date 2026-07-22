/-
Copyright (c) 2026 Mykola Palamarchuk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mykola Palamarchuk
-/
import ALT.CodeArith
import ALT.BoundedInterp

-- Formal-check file, not Mathlib-destined: opt out of the house-style header linter.
set_option linter.style.header false

/-!
# The interpreter's configuration layer, as explicit codes

The small-step interpreter reads and builds configurations. This file realizes the part of that
work which needs no arithmetic — the projections out of a configuration or a frame, and the
constructors that assemble one — as codes over `Nat.Partrec.Code`, each proved to agree with the
function the mathematical layer uses.

## The split, and why it falls here
The configuration layout nests `Nat.pair`, so every accessor is a composition of `left` and `right`
and every constructor a nest of `pair`: no bounded recursion is involved, and these codes cost a
number of steps independent of their input. The stack *cell* layout is different — it concatenates
bits behind a unary header, so reading or building one needs bit-length, powers, division and
remainder. That half is built on the arithmetic layer and is not here; this file stays on the
arithmetic-free side of that boundary.
-/

namespace CodePacking

open Nat.Partrec (Code)
open Nat.Partrec.Code
open TimeCost
open CodeArith

/-! ## Reading a configuration -/

/-- The configuration's mode. -/
def cCfMode : Code := left

@[simp] theorem val_cCfMode (s : ℕ) : val cCfMode s = BoundedInterp.cfMode s := rfl

/-- The configuration's current object. -/
def cCfCur : Code := comp left right

@[simp] theorem val_cCfCur (s : ℕ) : val cCfCur s = BoundedInterp.cfCur s := rfl

/-- The configuration's stack. -/
def cCfStk : Code := comp right right

@[simp] theorem val_cCfStk (s : ℕ) : val cCfStk s = BoundedInterp.cfStk s := rfl

theorem rfindFree_cCfMode : RfindFree cCfMode := trivial
theorem rfindFree_cCfCur : RfindFree cCfCur := ⟨trivial, trivial⟩
theorem rfindFree_cCfStk : RfindFree cCfStk := ⟨trivial, trivial⟩

/-! ## Reading a frame -/

/-- A frame's tag. -/
def cFrTag : Code := left

@[simp] theorem val_cFrTag (f : ℕ) : val cFrTag f = BoundedInterp.frTag f := rfl

/-- A frame's payload. -/
def cFrPay : Code := right

@[simp] theorem val_cFrPay (f : ℕ) : val cFrPay f = BoundedInterp.frPay f := rfl

theorem rfindFree_cFrTag : RfindFree cFrTag := trivial
theorem rfindFree_cFrPay : RfindFree cFrPay := trivial

/-! ## Building a configuration

Each constructor takes its components already packed, in the order the step function supplies them:
a returning configuration from `⟨v, k⟩`, a descending one from `⟨c, ⟨n, k⟩⟩`, a frame from
`⟨tag, payload⟩`. -/

/-- A frame, from `⟨tag, payload⟩` — the identity, since a frame *is* that pair. -/
def cFrame : Code := cId

@[simp] theorem val_cFrame (tg pay : ℕ) :
    val cFrame (Nat.pair tg pay) = BoundedInterp.frame tg pay := by
  rw [cFrame, val_cId, BoundedInterp.frame]

theorem rfindFree_cFrame : RfindFree cFrame := rfindFree_cId

/-- A returning configuration, from `⟨v, k⟩`. -/
def cRet : Code := pair (constCode 1) cId

@[simp] theorem val_cRet (v k : ℕ) : val cRet (Nat.pair v k) = BoundedInterp.ret v k := by
  rw [cRet, val_pair, val_constCode, val_cId, BoundedInterp.ret, BoundedInterp.config]

theorem rfindFree_cRet : RfindFree cRet := ⟨rfindFree_constCode 1, rfindFree_cId⟩

/-- A descending configuration, from `⟨c, ⟨n, k⟩⟩`. -/
def cDescend : Code :=
  pair zero (pair (pair left (comp left right)) (comp right right))

@[simp] theorem val_cDescend (c n k : ℕ) :
    val cDescend (Nat.pair c (Nat.pair n k)) = BoundedInterp.descend c n k := by
  rw [cDescend, val_pair, val_pair, val_pair, val_comp, val_comp, val_zero', val_left',
    val_left', val_right', val_right', Nat.unpair_pair, Nat.unpair_pair,
    BoundedInterp.descend, BoundedInterp.config]

theorem rfindFree_cDescend : RfindFree cDescend :=
  ⟨trivial, ⟨trivial, trivial, trivial⟩, trivial, trivial⟩

/-! ## The halt value

`haltVal` is the current object of a halted configuration, so it is the same projection as `cCfCur`.
The halt *test* compares the mode and the stack against constants and so belongs with the
arithmetic layer, not here. -/

/-- The answer of a halted configuration. -/
def cHaltVal : Code := cCfCur

@[simp] theorem val_cHaltVal (s : ℕ) : val cHaltVal s = BoundedInterp.haltVal s := rfl

theorem rfindFree_cHaltVal : RfindFree cHaltVal := rfindFree_cCfCur

/-! ## The stack cell's packing

A cell concatenates a unary header, the frame and the tail, so building or reading one needs the
arithmetic layer: bit-length for the header's width, powers of two for the shifts, division and
remainder to undo them. Every code below is a composition of the arithmetic layer with the
projections above, and every value law is the corresponding `BoundedInterp` definition. -/

/-- The width a frame occupies in a cell. -/
def cFrameBits : Code := cSize

@[simp] theorem val_cFrameBits (f : ℕ) : val cFrameBits f = BoundedInterp.frameBits f := by
  rw [cFrameBits, val_cSize, BoundedInterp.frameBits]

theorem rfindFree_cFrameBits : RfindFree cFrameBits := rfindFree_cSize

/-- `2 ^ (frameBits f)`, from `⟨f, k⟩`. -/
def cP0 : Code := comp cPow2 (comp cFrameBits left)

/-- `2 ^ (frameBits f + 1)`, from `⟨f, k⟩`. -/
def cP1 : Code := comp cPow2 (comp succ (comp cFrameBits left))

/-- `2 ^ (2 * frameBits f + 1)`, from `⟨f, k⟩`. -/
def cP2 : Code := comp cPow2 (comp succ (comp cDbl (comp cFrameBits left)))

/-- A stack cell, from `⟨f, k⟩`. -/
def cStkCons : Code :=
  comp succ (comp cDbl
    (comp cAdd (pair
      (comp cAdd (pair
        (comp cSub (pair cP0 (constCode 1)))
        (comp cMul (pair left cP1))))
      (comp cMul (pair right cP2)))))

@[simp] theorem val_cStkCons (f k : ℕ) :
    val cStkCons (Nat.pair f k) = BoundedInterp.stkCons f k := by
  simp only [cStkCons, cP0, cP1, cP2, val_comp, val_pair, val_left', val_right', val_succ',
    val_cDbl, val_cAdd, val_cSub, val_cMul, val_cPow2, val_cFrameBits, val_constCode,
    Nat.unpair_pair, BoundedInterp.stkCons, BoundedInterp.frameBits]

theorem rfindFree_cP0 : RfindFree cP0 :=
  ⟨rfindFree_cPow2, rfindFree_cFrameBits, trivial⟩

theorem rfindFree_cP1 : RfindFree cP1 :=
  ⟨rfindFree_cPow2, trivial, rfindFree_cFrameBits, trivial⟩

theorem rfindFree_cP2 : RfindFree cP2 :=
  ⟨rfindFree_cPow2, trivial, rfindFree_cDbl, rfindFree_cFrameBits, trivial⟩

theorem rfindFree_cStkCons : RfindFree cStkCons :=
  ⟨trivial, rfindFree_cDbl,
    rfindFree_cAdd,
    ⟨rfindFree_cAdd, ⟨rfindFree_cSub, rfindFree_cP0, rfindFree_constCode 1⟩,
      rfindFree_cMul, trivial, rfindFree_cP1⟩,
    rfindFree_cMul, trivial, rfindFree_cP2⟩

/-- A cell with its flag bit removed. -/
def cStkBody : Code := comp cDiv (pair cId (constCode 2))

@[simp] theorem val_cStkBody (s : ℕ) : val cStkBody s = BoundedInterp.stkBody s := by
  rw [cStkBody, val_comp, val_pair, val_cId, val_constCode, val_cDiv, BoundedInterp.stkBody]

theorem rfindFree_cStkBody : RfindFree cStkBody :=
  ⟨rfindFree_cDiv, rfindFree_cId, rfindFree_constCode 2⟩

/-! ### The header's length

The fold raises its accumulator while the bottom `acc + 1` bits are all ones, which
`BoundedInterp.trailOnes_lt_iff` identifies with `acc < trailOnes n`. So the fold computes
`min (trailOnes n) m`, exactly as the bit-length fold does. -/

/-- `2 ^ (acc + 1)` inside the header fold. -/
def cHdrPow : Code := comp cPow2 (comp succ cAcc)

/-- The header fold's step: raise the accumulator while the bottom bits are all ones. -/
def trailStep : Code :=
  comp cIte (pair
    (comp cEq (pair (comp cMod (pair left cHdrPow)) (comp cSub (pair cHdrPow (constCode 1)))))
    (pair (comp succ cAcc) cAcc))

theorem val_trailStep (a y m : ℕ) :
    val trailStep (Nat.pair a (Nat.pair y m))
      = if a % 2 ^ (m + 1) = 2 ^ (m + 1) - 1 then m + 1 else m := by
  simp only [trailStep, cHdrPow, val_comp, val_pair, val_left', val_succ', val_cAcc, val_cPow2,
    val_cMod, val_cSub, val_constCode, val_cEq, val_cIte, Nat.unpair_pair]
  by_cases h : a % 2 ^ (m + 1) = 2 ^ (m + 1) - 1 <;> simp [h]

/-- The header fold, run `m` times from zero. -/
def trailCore : Code := prec zero trailStep

theorem val_trailCore (n : ℕ) : ∀ m,
    val trailCore (Nat.pair n m) = min (BoundedInterp.trailOnes n) m := by
  intro m
  induction m with
  | zero =>
      change val (prec zero trailStep) (Nat.pair n 0) = _
      rw [val_prec_zero, val_zero']
      omega
  | succ j ih =>
      change val (prec zero trailStep) (Nat.pair n (j + 1)) = _
      rw [val_prec_succ]
      change val trailStep (Nat.pair n (Nat.pair j (val trailCore (Nat.pair n j)))) = _
      rw [val_trailStep, ih]
      by_cases h : BoundedInterp.trailOnes n ≤ j
      · have hmin : min (BoundedInterp.trailOnes n) j = BoundedInterp.trailOnes n := by omega
        rw [hmin, if_neg ?_]
        · omega
        · intro hc
          have := (BoundedInterp.trailOnes_lt_iff n (BoundedInterp.trailOnes n)).2 hc
          omega
      · have hmin : min (BoundedInterp.trailOnes n) j = j := by omega
        rw [hmin, if_pos ((BoundedInterp.trailOnes_lt_iff n j).1 (by omega))]
        omega

/-- The header's length never exceeds the numeral it reads. -/
theorem trailOnes_le (n : ℕ) : BoundedInterp.trailOnes n ≤ n := by
  rcases Nat.eq_zero_or_pos (BoundedInterp.trailOnes n) with h | h
  · omega
  · have hlt : BoundedInterp.trailOnes n - 1 < BoundedInterp.trailOnes n := by omega
    have hb := (BoundedInterp.trailOnes_lt_iff n (BoundedInterp.trailOnes n - 1)).1 hlt
    have hle : n % 2 ^ (BoundedInterp.trailOnes n - 1 + 1) ≤ n := Nat.mod_le _ _
    have hgrow : BoundedInterp.trailOnes n - 1 + 1 < 2 ^ (BoundedInterp.trailOnes n - 1 + 1) :=
      Nat.lt_two_pow_self
    omega

/-- The header's length as a one-argument code. -/
def cTrailOnes : Code := comp trailCore (pair cId cId)

@[simp] theorem val_cTrailOnes (n : ℕ) : val cTrailOnes n = BoundedInterp.trailOnes n := by
  rw [cTrailOnes, val_comp, val_pair, val_cId, val_trailCore]
  have := trailOnes_le n
  omega

theorem rfindFree_cHdrPow : RfindFree cHdrPow := ⟨rfindFree_cPow2, trivial, rfindFree_cAcc⟩

theorem rfindFree_trailStep : RfindFree trailStep :=
  ⟨rfindFree_cIte,
    ⟨rfindFree_cEq, ⟨rfindFree_cMod, trivial, rfindFree_cHdrPow⟩,
      rfindFree_cSub, rfindFree_cHdrPow, rfindFree_constCode 1⟩,
    ⟨trivial, rfindFree_cAcc⟩, rfindFree_cAcc⟩

theorem rfindFree_trailCore : RfindFree trailCore := ⟨trivial, rfindFree_trailStep⟩

theorem rfindFree_cTrailOnes : RfindFree cTrailOnes :=
  ⟨rfindFree_trailCore, rfindFree_cId, rfindFree_cId⟩

/-! ### Reading a cell -/

/-- The frame width a cell declares. -/
def cStkLen : Code := comp cTrailOnes cStkBody

@[simp] theorem val_cStkLen (s : ℕ) : val cStkLen s = BoundedInterp.stkLen s := by
  rw [cStkLen, val_comp, val_cStkBody, val_cTrailOnes, BoundedInterp.stkLen]

theorem rfindFree_cStkLen : RfindFree cStkLen := ⟨rfindFree_cTrailOnes, rfindFree_cStkBody⟩

/-- The tail of a stack cell. -/
def cStkTail : Code :=
  comp cDiv (pair cStkBody (comp cPow2 (comp succ (comp cDbl cStkLen))))

@[simp] theorem val_cStkTail (s : ℕ) : val cStkTail s = BoundedInterp.stkTail s := by
  rw [cStkTail, val_comp, val_pair, val_cStkBody, val_comp, val_comp, val_comp, val_succ',
    val_cDbl, val_cStkLen, val_cPow2, val_cDiv, BoundedInterp.stkTail]

theorem rfindFree_cStkTail : RfindFree cStkTail :=
  ⟨rfindFree_cDiv, rfindFree_cStkBody, rfindFree_cPow2, trivial, rfindFree_cDbl,
    rfindFree_cStkLen⟩

/-- The frame of a stack cell. -/
def cStkHead : Code :=
  comp cMod (pair (comp cDiv (pair cStkBody (comp cPow2 (comp succ cStkLen))))
    (comp cPow2 cStkLen))

@[simp] theorem val_cStkHead (s : ℕ) : val cStkHead s = BoundedInterp.stkHead s := by
  rw [cStkHead, val_comp, val_pair, val_comp, val_pair, val_cStkBody, val_comp, val_comp,
    val_succ', val_cStkLen, val_cPow2, val_cDiv, val_comp, val_cStkLen, val_cPow2, val_cMod,
    BoundedInterp.stkHead]

theorem rfindFree_cStkHead : RfindFree cStkHead :=
  ⟨rfindFree_cMod,
    ⟨rfindFree_cDiv, rfindFree_cStkBody, rfindFree_cPow2, trivial, rfindFree_cStkLen⟩,
    rfindFree_cPow2, rfindFree_cStkLen⟩

/-- The cell test: does this numeral re-pack to itself? -/
def cStkIsCons : Code := comp cEq (pair (comp cStkCons (pair cStkHead cStkTail)) cId)

@[simp] theorem val_cStkIsCons (s : ℕ) :
    val cStkIsCons s = if BoundedInterp.stkIsCons s then 1 else 0 := by
  rw [cStkIsCons, val_comp, val_pair, val_comp, val_pair, val_cStkHead, val_cStkTail,
    val_cStkCons, val_cId, val_cEq, BoundedInterp.stkIsCons]
  by_cases h : BoundedInterp.stkCons (BoundedInterp.stkHead s) (BoundedInterp.stkTail s) = s
  · rw [if_pos h]; simp [h]
  · rw [if_neg h]; simp [h]

theorem rfindFree_cStkIsCons : RfindFree cStkIsCons :=
  ⟨rfindFree_cEq, ⟨rfindFree_cStkCons, rfindFree_cStkHead, rfindFree_cStkTail⟩, rfindFree_cId⟩

/-! ### The halt test -/

/-- Has the machine finished? -/
def cIsHalt : Code :=
  comp OneDL.cAnd (pair (comp cEq (pair cCfMode (constCode 1)))
    (comp cEq (pair cCfStk (constCode 0))))

@[simp] theorem val_cIsHalt (s : ℕ) :
    val cIsHalt s = if BoundedInterp.isHalt s then 1 else 0 := by
  rw [cIsHalt, val_comp, val_pair, val_comp, val_comp, val_pair, val_pair, val_cCfMode,
    val_cCfStk, val_constCode, val_constCode, val_cEq, val_cEq, OneDL.val_cAnd,
    BoundedInterp.isHalt]
  by_cases h1 : BoundedInterp.cfMode s = 1 <;> by_cases h2 : BoundedInterp.cfStk s = 0 <;>
    simp [h1, h2]

theorem rfindFree_cIsHalt : RfindFree cIsHalt :=
  ⟨OneDL.rfindFree_cAnd,
    ⟨rfindFree_cEq, rfindFree_cCfMode, rfindFree_constCode 1⟩,
    rfindFree_cEq, rfindFree_cCfStk, rfindFree_constCode 0⟩

/-! ## The dispatch seam

`stepUFn` decides which constructor it is looking at by decoding a numeral into a `Code` and
matching on it. A realization cannot match on a `Code` — it has only arithmetic — so it reads the
constructor off the numeral instead. The two dispatches agree, and this is where that is proved.

For `c < 4` the numeral *is* the constructor. For `c ≥ 4`, writing `n = c - 4`, the constructor is
determined by `n % 4` and the children's numerals are the two halves of `n / 4`:

| `n % 4` | constructor |
| --- | --- |
| `0` | `pair` |
| `1` | `prec` |
| `2` | `comp` |
| `3` | `rfind'` (one child, the whole of `n / 4`) |

Mathlib's decoder branches on the low two bits through `Nat.bodd` and `Nat.div2`; the content of the
lemma is that those are the same two bits `n % 4` names. -/

theorem ofNat_dispatch (n : ℕ) :
    Denumerable.ofNat Code (n + 4) =
      (if n % 4 = 0 then
        Code.pair (Denumerable.ofNat Code (n / 4).unpair.1)
          (Denumerable.ofNat Code (n / 4).unpair.2)
      else if n % 4 = 1 then
        Code.prec (Denumerable.ofNat Code (n / 4).unpair.1)
          (Denumerable.ofNat Code (n / 4).unpair.2)
      else if n % 4 = 2 then
        Code.comp (Denumerable.ofNat Code (n / 4).unpair.1)
          (Denumerable.ofNat Code (n / 4).unpair.2)
      else Code.rfind' (Denumerable.ofNat Code (n / 4))) := by
  have hdiv : n.div2.div2 = n / 4 := by
    rw [Nat.div2_val, Nat.div2_val, Nat.div_div_eq_div_mul]
  have hsplit : n % 4 = n % 2 + 2 * ((n / 2) % 2) := by omega
  have hof : Denumerable.ofNat Code (n + 4) = ofNatCode (n + 4) := rfl
  rw [hof]
  simp only [ofNatCode.eq_5, hdiv]
  cases hb0 : n.bodd <;> cases hb1 : n.div2.bodd
  · have e0 : n % 2 = 0 := by rw [Nat.mod_two_of_bodd, hb0]; rfl
    have e1 : n / 2 % 2 = 0 := by rw [← Nat.div2_val, Nat.mod_two_of_bodd, hb1]; rfl
    rw [if_pos (by omega)]
    rfl
  · have e0 : n % 2 = 0 := by rw [Nat.mod_two_of_bodd, hb0]; rfl
    have e1 : n / 2 % 2 = 1 := by rw [← Nat.div2_val, Nat.mod_two_of_bodd, hb1]; rfl
    rw [if_neg (by omega), if_neg (by omega), if_pos (by omega)]
    rfl
  · have e0 : n % 2 = 1 := by rw [Nat.mod_two_of_bodd, hb0]; rfl
    have e1 : n / 2 % 2 = 0 := by rw [← Nat.div2_val, Nat.mod_two_of_bodd, hb1]; rfl
    rw [if_neg (by omega), if_pos (by omega)]
    rfl
  · have e0 : n % 2 = 1 := by rw [Nat.mod_two_of_bodd, hb0]; rfl
    have e1 : n / 2 % 2 = 1 := by rw [← Nat.div2_val, Nat.mod_two_of_bodd, hb1]; rfl
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    rfl

/-! ### The dispatch table's leaves

Below four the numeral names its constructor outright, so these complete the table
`ofNat_dispatch` starts. Together the five are the whole of what a realization needs to know about
decoding: which constructor, and where its children's numerals are. -/

@[simp] theorem ofNat_zero : Denumerable.ofNat Code 0 = Code.zero := by
  have h : Denumerable.ofNat Code 0 = ofNatCode 0 := rfl
  rw [h, ofNatCode]

@[simp] theorem ofNat_one : Denumerable.ofNat Code 1 = Code.succ := by
  have h : Denumerable.ofNat Code 1 = ofNatCode 1 := rfl
  rw [h, ofNatCode]

@[simp] theorem ofNat_two : Denumerable.ofNat Code 2 = Code.left := by
  have h : Denumerable.ofNat Code 2 = ofNatCode 2 := rfl
  rw [h, ofNatCode]

@[simp] theorem ofNat_three : Denumerable.ofNat Code 3 = Code.right := by
  have h : Denumerable.ofNat Code 3 = ofNatCode 3 := rfl
  rw [h, ofNatCode]

/-- A child's numeral reads back exactly: the realization never needs to decode further than the
tag, because the children are already numerals. -/
theorem encode_child (j : ℕ) : Encodable.encode (Denumerable.ofNat Code j) = j :=
  Denumerable.encode_ofNat j

/-! ## The descending step, arithmetically

`BoundedInterp.stepDescend` decides its branch by decoding. `stepDescendArith` decides the same
branch from the numeral, using the dispatch table above, and `stepDescendArith_eq` says the two
agree. Splitting the work this way applies the seam **once** rather than once per branch: what is
left for the realization is a selection tree over the arithmetic layer, with no decoding in it. -/

/-- The descending step, with the constructor read off the numeral instead of decoded. -/
def stepDescendArith (c n k : ℕ) : ℕ :=
  if c = 0 then BoundedInterp.ret 0 k
  else if c = 1 then BoundedInterp.ret (n + 1) k
  else if c = 2 then BoundedInterp.ret n.unpair.1 k
  else if c = 3 then BoundedInterp.ret n.unpair.2 k
  else if (c - 4) % 4 = 0 then
    BoundedInterp.descend ((c - 4) / 4).unpair.1 n
      (BoundedInterp.stkCons (BoundedInterp.frame 0 (Nat.pair ((c - 4) / 4).unpair.2 n)) k)
  else if (c - 4) % 4 = 1 then
    BoundedInterp.descend ((c - 4) / 4).unpair.1 n.unpair.1
      (BoundedInterp.stkCons (BoundedInterp.frame 3 (Nat.pair ((c - 4) / 4).unpair.2
        (Nat.pair n.unpair.1 (Nat.pair 0 n.unpair.2)))) k)
  else if (c - 4) % 4 = 2 then
    BoundedInterp.descend ((c - 4) / 4).unpair.2 n
      (BoundedInterp.stkCons (BoundedInterp.frame 2 ((c - 4) / 4).unpair.1) k)
  else
    BoundedInterp.descend ((c - 4) / 4) n
      (BoundedInterp.stkCons (BoundedInterp.frame 4 (Nat.pair ((c - 4) / 4) n)) k)

/-- **The arithmetic dispatch is the constructor dispatch.** Every branch of the descending step is
selected by the same numeral arithmetic the realization can perform, and the children it passes on
are already the numerals it has. -/
theorem stepDescendArith_eq (c n k : ℕ) :
    stepDescendArith c n k = BoundedInterp.stepDescend c n k := by
  match c with
  | 0 => simp [stepDescendArith, BoundedInterp.stepDescend]
  | 1 => simp [stepDescendArith, BoundedInterp.stepDescend]
  | 2 => simp [stepDescendArith, BoundedInterp.stepDescend]
  | 3 => simp [stepDescendArith, BoundedInterp.stepDescend]
  | (m + 4) =>
      have hsub : m + 4 - 4 = m := by omega
      have hd := ofNat_dispatch m
      simp only [stepDescendArith, hsub, if_neg (by omega : m + 4 ≠ 0),
        if_neg (by omega : m + 4 ≠ 1), if_neg (by omega : m + 4 ≠ 2),
        if_neg (by omega : m + 4 ≠ 3)]
      by_cases h0 : m % 4 = 0
      · rw [if_pos h0]
        rw [if_pos h0] at hd
        rw [BoundedInterp.stepDescend, hd]
        simp
      · by_cases h1 : m % 4 = 1
        · rw [if_neg h0, if_pos h1]
          rw [if_neg h0, if_pos h1] at hd
          rw [BoundedInterp.stepDescend, hd]
          simp
        · by_cases h2 : m % 4 = 2
          · rw [if_neg h0, if_neg h1, if_pos h2]
            rw [if_neg h0, if_neg h1, if_pos h2] at hd
            rw [BoundedInterp.stepDescend, hd]
            simp
          · rw [if_neg h0, if_neg h1, if_neg h2]
            rw [if_neg h0, if_neg h1, if_neg h2] at hd
            rw [BoundedInterp.stepDescend, hd]
            simp

/-! ## The descending step, realized

A selection tree over the arithmetic layer. There is no decoding in it: `stepDescendArith` already
turned the constructor dispatch into numeral arithmetic, so what is left is eight branches chosen by
equality tests on the numeral and on its tag. -/

/-- Selection: run `x` when the guard is nonzero, `y` when it is zero. -/
def cSel (b x y : Code) : Code := comp cIte (pair b (pair x y))

@[simp] theorem val_cSel (b x y : Code) (v : ℕ) :
    val (cSel b x y) v = if val b v = 0 then val y v else val x v := by
  rw [cSel, val_comp, val_pair, val_pair, val_cIte]

theorem rfindFree_cSel {b x y : Code} (hb : RfindFree b) (hx : RfindFree x) (hy : RfindFree y) :
    RfindFree (cSel b x y) := ⟨rfindFree_cIte, hb, hx, hy⟩

/-- The guard "this code's value is the constant `j`". -/
def cEqK (j : ℕ) (x : Code) : Code := comp cEq (pair x (constCode j))

@[simp] theorem val_cEqK (j : ℕ) (x : Code) (v : ℕ) :
    val (cEqK j x) v = if val x v = j then 1 else 0 := by
  rw [cEqK, val_comp, val_pair, val_constCode, val_cEq]

theorem rfindFree_cEqK (j : ℕ) {x : Code} (hx : RfindFree x) : RfindFree (cEqK j x) :=
  ⟨rfindFree_cEq, hx, rfindFree_constCode j⟩

/-! ### The descending step's slots, read from `⟨c, ⟨n, k⟩⟩` -/

/-- The code numeral. -/ def dC : Code := left
/-- The input. -/ def dN : Code := comp left right
/-- The stack. -/ def dK : Code := comp right right
/-- The numeral above the four leaves. -/
def dM : Code := comp cSub (pair dC (constCode 4))
/-- The children's packed numeral. -/
def dP : Code := comp cDiv (pair dM (constCode 4))
/-- The constructor tag. -/
def dT : Code := comp cMod (pair dM (constCode 4))
/-- The first child's numeral. -/ def dP1 : Code := comp left dP
/-- The second child's numeral. -/ def dP2 : Code := comp right dP
/-- The input's first component. -/ def dN1 : Code := comp left dN
/-- The input's second component. -/ def dN2 : Code := comp right dN

@[simp] theorem val_dC (c n k : ℕ) : val dC (Nat.pair c (Nat.pair n k)) = c := by
  rw [dC, val_left', Nat.unpair_pair]

@[simp] theorem val_dN (c n k : ℕ) : val dN (Nat.pair c (Nat.pair n k)) = n := by
  rw [dN, val_comp, val_right', val_left', Nat.unpair_pair, Nat.unpair_pair]

@[simp] theorem val_dK (c n k : ℕ) : val dK (Nat.pair c (Nat.pair n k)) = k := by
  rw [dK, val_comp, val_right', val_right', Nat.unpair_pair, Nat.unpair_pair]

@[simp] theorem val_dM (c n k : ℕ) : val dM (Nat.pair c (Nat.pair n k)) = c - 4 := by
  rw [dM, val_comp, val_pair, val_dC, val_constCode, val_cSub]

@[simp] theorem val_dP (c n k : ℕ) : val dP (Nat.pair c (Nat.pair n k)) = (c - 4) / 4 := by
  rw [dP, val_comp, val_pair, val_dM, val_constCode, val_cDiv]

@[simp] theorem val_dT (c n k : ℕ) : val dT (Nat.pair c (Nat.pair n k)) = (c - 4) % 4 := by
  rw [dT, val_comp, val_pair, val_dM, val_constCode, val_cMod]

@[simp] theorem val_dP1 (c n k : ℕ) :
    val dP1 (Nat.pair c (Nat.pair n k)) = ((c - 4) / 4).unpair.1 := by
  rw [dP1, val_comp, val_dP, val_left']

@[simp] theorem val_dP2 (c n k : ℕ) :
    val dP2 (Nat.pair c (Nat.pair n k)) = ((c - 4) / 4).unpair.2 := by
  rw [dP2, val_comp, val_dP, val_right']

@[simp] theorem val_dN1 (c n k : ℕ) : val dN1 (Nat.pair c (Nat.pair n k)) = n.unpair.1 := by
  rw [dN1, val_comp, val_dN, val_left']

@[simp] theorem val_dN2 (c n k : ℕ) : val dN2 (Nat.pair c (Nat.pair n k)) = n.unpair.2 := by
  rw [dN2, val_comp, val_dN, val_right']

/-! ### The eight branches -/

/-- `zero`'s branch. -/ def dB0 : Code := comp cRet (pair (constCode 0) dK)
/-- `succ`'s branch. -/ def dB1 : Code := comp cRet (pair (comp succ dN) dK)
/-- `left`'s branch. -/ def dB2 : Code := comp cRet (pair dN1 dK)
/-- `right`'s branch. -/ def dB3 : Code := comp cRet (pair dN2 dK)

/-- `pair`'s branch. -/
def dBpair : Code :=
  comp cDescend (pair dP1 (pair dN
    (comp cStkCons (pair (pair (constCode 0) (pair dP2 dN)) dK))))

/-- `prec`'s branch. -/
def dBprec : Code :=
  comp cDescend (pair dP1 (pair dN1
    (comp cStkCons (pair (pair (constCode 3)
      (pair dP2 (pair dN1 (pair (constCode 0) dN2)))) dK))))

/-- `comp`'s branch. -/
def dBcomp : Code :=
  comp cDescend (pair dP2 (pair dN (comp cStkCons (pair (pair (constCode 2) dP1) dK))))

/-- `rfind'`'s branch. -/
def dBrfind : Code :=
  comp cDescend (pair dP (pair dN (comp cStkCons (pair (pair (constCode 4) (pair dP dN)) dK))))

/-! ### Each branch's value, computed once

Reducing the branches separately keeps the tree's proof to a case analysis over already-reduced
arms; folding them all into one simp call runs the elaborator out of heartbeats. -/

@[simp] theorem val_dB0 (c n k : ℕ) :
    val dB0 (Nat.pair c (Nat.pair n k)) = BoundedInterp.ret 0 k := by
  rw [dB0, val_comp, val_pair, val_constCode, val_dK, val_cRet]

@[simp] theorem val_dB1 (c n k : ℕ) :
    val dB1 (Nat.pair c (Nat.pair n k)) = BoundedInterp.ret (n + 1) k := by
  rw [dB1, val_comp, val_pair, val_comp, val_succ', val_dN, val_dK, val_cRet]

@[simp] theorem val_dB2 (c n k : ℕ) :
    val dB2 (Nat.pair c (Nat.pair n k)) = BoundedInterp.ret n.unpair.1 k := by
  rw [dB2, val_comp, val_pair, val_dN1, val_dK, val_cRet]

@[simp] theorem val_dB3 (c n k : ℕ) :
    val dB3 (Nat.pair c (Nat.pair n k)) = BoundedInterp.ret n.unpair.2 k := by
  rw [dB3, val_comp, val_pair, val_dN2, val_dK, val_cRet]

@[simp] theorem val_dBpair (c n k : ℕ) :
    val dBpair (Nat.pair c (Nat.pair n k)) =
      BoundedInterp.descend ((c - 4) / 4).unpair.1 n
        (BoundedInterp.stkCons (BoundedInterp.frame 0 (Nat.pair ((c - 4) / 4).unpair.2 n)) k) := by
  rw [dBpair, val_comp, val_pair, val_pair, val_comp, val_pair, val_pair, val_pair,
    val_constCode, val_dP1, val_dP2, val_dN, val_dK, val_cStkCons, val_cDescend,
    BoundedInterp.frame]

@[simp] theorem val_dBprec (c n k : ℕ) :
    val dBprec (Nat.pair c (Nat.pair n k)) =
      BoundedInterp.descend ((c - 4) / 4).unpair.1 n.unpair.1
        (BoundedInterp.stkCons (BoundedInterp.frame 3 (Nat.pair ((c - 4) / 4).unpair.2
          (Nat.pair n.unpair.1 (Nat.pair 0 n.unpair.2)))) k) := by
  rw [dBprec, val_comp, val_pair, val_pair, val_comp, val_pair, val_pair, val_pair, val_pair,
    val_pair, val_constCode, val_constCode, val_dP1, val_dP2, val_dN1, val_dN2, val_dK,
    val_cStkCons, val_cDescend, BoundedInterp.frame]

@[simp] theorem val_dBcomp (c n k : ℕ) :
    val dBcomp (Nat.pair c (Nat.pair n k)) =
      BoundedInterp.descend ((c - 4) / 4).unpair.2 n
        (BoundedInterp.stkCons (BoundedInterp.frame 2 ((c - 4) / 4).unpair.1) k) := by
  rw [dBcomp, val_comp, val_pair, val_pair, val_comp, val_pair, val_pair, val_constCode,
    val_dP1, val_dP2, val_dN, val_dK, val_cStkCons, val_cDescend, BoundedInterp.frame]

@[simp] theorem val_dBrfind (c n k : ℕ) :
    val dBrfind (Nat.pair c (Nat.pair n k)) =
      BoundedInterp.descend ((c - 4) / 4) n
        (BoundedInterp.stkCons
          (BoundedInterp.frame 4 (Nat.pair ((c - 4) / 4) n)) k) := by
  rw [dBrfind, val_comp, val_pair, val_pair, val_comp, val_pair, val_pair, val_pair,
    val_constCode, val_dP, val_dN, val_dK, val_cStkCons, val_cDescend, BoundedInterp.frame]

theorem rfindFree_dC : RfindFree dC := trivial
theorem rfindFree_dN : RfindFree dN := ⟨trivial, trivial⟩
theorem rfindFree_dK : RfindFree dK := ⟨trivial, trivial⟩
theorem rfindFree_dM : RfindFree dM :=
  ⟨rfindFree_cSub, rfindFree_dC, rfindFree_constCode 4⟩
theorem rfindFree_dP : RfindFree dP := ⟨rfindFree_cDiv, rfindFree_dM, rfindFree_constCode 4⟩
theorem rfindFree_dT : RfindFree dT := ⟨rfindFree_cMod, rfindFree_dM, rfindFree_constCode 4⟩
theorem rfindFree_dP1 : RfindFree dP1 := ⟨trivial, rfindFree_dP⟩
theorem rfindFree_dP2 : RfindFree dP2 := ⟨trivial, rfindFree_dP⟩
theorem rfindFree_dN1 : RfindFree dN1 := ⟨trivial, rfindFree_dN⟩
theorem rfindFree_dN2 : RfindFree dN2 := ⟨trivial, rfindFree_dN⟩

theorem rfindFree_dB0 : RfindFree dB0 :=
  ⟨rfindFree_cRet, rfindFree_constCode 0, rfindFree_dK⟩
theorem rfindFree_dB1 : RfindFree dB1 :=
  ⟨rfindFree_cRet, ⟨trivial, rfindFree_dN⟩, rfindFree_dK⟩
theorem rfindFree_dB2 : RfindFree dB2 := ⟨rfindFree_cRet, rfindFree_dN1, rfindFree_dK⟩
theorem rfindFree_dB3 : RfindFree dB3 := ⟨rfindFree_cRet, rfindFree_dN2, rfindFree_dK⟩
theorem rfindFree_dBpair : RfindFree dBpair :=
  ⟨rfindFree_cDescend, rfindFree_dP1, rfindFree_dN,
    rfindFree_cStkCons, ⟨rfindFree_constCode 0, rfindFree_dP2, rfindFree_dN⟩, rfindFree_dK⟩
theorem rfindFree_dBprec : RfindFree dBprec :=
  ⟨rfindFree_cDescend, rfindFree_dP1, rfindFree_dN1,
    rfindFree_cStkCons,
    ⟨rfindFree_constCode 3, rfindFree_dP2, rfindFree_dN1,
      rfindFree_constCode 0, rfindFree_dN2⟩,
    rfindFree_dK⟩
theorem rfindFree_dBcomp : RfindFree dBcomp :=
  ⟨rfindFree_cDescend, rfindFree_dP2, rfindFree_dN,
    rfindFree_cStkCons, ⟨rfindFree_constCode 2, rfindFree_dP1⟩, rfindFree_dK⟩
theorem rfindFree_dBrfind : RfindFree dBrfind :=
  ⟨rfindFree_cDescend, rfindFree_dP, rfindFree_dN,
    rfindFree_cStkCons, ⟨rfindFree_constCode 4, rfindFree_dP, rfindFree_dN⟩, rfindFree_dK⟩

attribute [local irreducible] dB0 dB1 dB2 dB3 dBpair dBprec dBcomp dBrfind

/-- **The descending step as a code.** -/
def stepDescendU : Code :=
  cSel (cEqK 0 dC) dB0
    (cSel (cEqK 1 dC) dB1
      (cSel (cEqK 2 dC) dB2
        (cSel (cEqK 3 dC) dB3
          (cSel (cEqK 0 dT) dBpair
            (cSel (cEqK 1 dT) dBprec
              (cSel (cEqK 2 dT) dBcomp dBrfind))))))

theorem val_stepDescendU (c n k : ℕ) :
    val stepDescendU (Nat.pair c (Nat.pair n k)) = stepDescendArith c n k := by
  simp only [stepDescendU, val_cSel, val_cEqK, val_dC, val_dT, val_dB0, val_dB1, val_dB2,
    val_dB3, val_dBpair, val_dBprec, val_dBcomp, val_dBrfind, stepDescendArith]
  by_cases h0 : c = 0
  · simp [h0]
  · by_cases h1 : c = 1
    · simp [h1]
    · by_cases h2 : c = 2
      · simp [h2]
      · by_cases h3 : c = 3
        · simp [h3]
        · by_cases t0 : (c - 4) % 4 = 0
          · simp [h0, h1, h2, h3, t0]
          · by_cases t1 : (c - 4) % 4 = 1
            · simp [h0, h1, h2, h3, t1]
            · by_cases t2 : (c - 4) % 4 = 2
              · simp [h0, h1, h2, h3, t2]
              · simp [h0, h1, h2, h3, t0, t1, t2]

theorem rfindFree_stepDescendU : RfindFree stepDescendU :=
  rfindFree_cSel (rfindFree_cEqK 0 rfindFree_dC) rfindFree_dB0
    (rfindFree_cSel (rfindFree_cEqK 1 rfindFree_dC) rfindFree_dB1
      (rfindFree_cSel (rfindFree_cEqK 2 rfindFree_dC) rfindFree_dB2
        (rfindFree_cSel (rfindFree_cEqK 3 rfindFree_dC) rfindFree_dB3
          (rfindFree_cSel (rfindFree_cEqK 0 rfindFree_dT) rfindFree_dBpair
            (rfindFree_cSel (rfindFree_cEqK 1 rfindFree_dT) rfindFree_dBprec
              (rfindFree_cSel (rfindFree_cEqK 2 rfindFree_dT) rfindFree_dBcomp
                rfindFree_dBrfind))))))

/-- **The brief's law, as a corollary.** Composing the realization with the arithmetic dispatch's
agreement gives the descending step directly. -/
theorem val_stepDescendU_eq (c n k : ℕ) :
    val stepDescendU (Nat.pair c (Nat.pair n k)) = BoundedInterp.stepDescend c n k := by
  rw [val_stepDescendU, stepDescendArith_eq]

/-! ## The returning step, arithmetically

`BoundedInterp.stepReturn` dispatches on `frTag f`, which is already an accessor — no decoding, and
so no seam. `stepReturnArith` writes the same dispatch as explicit tag comparisons, and
`stepReturnArith_eq` is its agreement. The two inner `if`s (the loop's "turns left" test at tag 3
and the search's "found" test at tag 4) carry over unchanged. -/

/-- The returning step, with the tag dispatch written as numeral comparisons. -/
def stepReturnArith (v f k : ℕ) : ℕ :=
  if f.unpair.1 = 0 then
    BoundedInterp.descend (BoundedInterp.frPay f).unpair.1 (BoundedInterp.frPay f).unpair.2
      (BoundedInterp.stkCons (BoundedInterp.frame 1 v) k)
  else if f.unpair.1 = 1 then
    BoundedInterp.ret (Nat.pair (BoundedInterp.frPay f) v) k
  else if f.unpair.1 = 2 then
    BoundedInterp.descend (BoundedInterp.frPay f) v k
  else if f.unpair.1 = 3 then
    (if (BoundedInterp.frPay f).unpair.2.unpair.2.unpair.2 = 0 then BoundedInterp.ret v k
     else
      BoundedInterp.descend (BoundedInterp.frPay f).unpair.1
        (Nat.pair (BoundedInterp.frPay f).unpair.2.unpair.1
          (Nat.pair (BoundedInterp.frPay f).unpair.2.unpair.2.unpair.1 v))
        (BoundedInterp.stkCons (BoundedInterp.frame 3 (Nat.pair (BoundedInterp.frPay f).unpair.1
          (Nat.pair (BoundedInterp.frPay f).unpair.2.unpair.1
            (Nat.pair ((BoundedInterp.frPay f).unpair.2.unpair.2.unpair.1 + 1)
              ((BoundedInterp.frPay f).unpair.2.unpair.2.unpair.2 - 1))))) k))
  else if f.unpair.1 = 4 then
    (if v = 0 then BoundedInterp.ret (BoundedInterp.frPay f).unpair.2.unpair.2 k
     else
      BoundedInterp.descend (BoundedInterp.frPay f).unpair.1
        (Nat.pair (BoundedInterp.frPay f).unpair.2.unpair.1
          ((BoundedInterp.frPay f).unpair.2.unpair.2 + 1))
        (BoundedInterp.stkCons (BoundedInterp.frame 4 (Nat.pair (BoundedInterp.frPay f).unpair.1
          (Nat.pair (BoundedInterp.frPay f).unpair.2.unpair.1
            ((BoundedInterp.frPay f).unpair.2.unpair.2 + 1)))) k))
  else BoundedInterp.ret v (BoundedInterp.stkCons f k)

/-- **The tag dispatch is the frame dispatch.** No seam is involved — the tag is an accessor — so
this is the pure case analysis, one branch per frame plus the stuck default. -/
theorem stepReturnArith_eq (v f k : ℕ) :
    stepReturnArith v f k = BoundedInterp.stepReturn v f k := by
  unfold stepReturnArith
  rw [BoundedInterp.stepReturn, BoundedInterp.frTag]
  rcases ht : f.unpair.1 with _ | _ | _ | _ | _ | tg <;>
    simp only [Nat.reduceEqDiff, reduceIte, Nat.add_eq_zero_iff, and_false, reduceCtorEq,
      Nat.reduceAdd, if_false]

/-! ## The returning step, realized

A selection tree over the tag, with the two inner tests (loop's "turns left", search's "found") as
their own selections. Same recipe as the descending step: per-branch `@[simp]` value lemmas by
explicit `rw`, the wide branch codes made `local irreducible` so the tree's proof never descends
into them. The input is `⟨v, ⟨f, k⟩⟩`. -/

/-- The returned value. -/ def rV : Code := left
/-- The top frame. -/ def rF : Code := comp left right
/-- The stack tail. -/ def rK : Code := comp right right
/-- The frame's tag. -/ def rTag : Code := comp left rF
/-- The frame's payload. -/ def rPay : Code := comp right rF
/-- Payload slots. -/
def rPay1 : Code := comp left rPay
def rPay2 : Code := comp right rPay
def rPay21 : Code := comp left rPay2
def rPay22 : Code := comp right rPay2
def rPay221 : Code := comp left rPay22
def rPay222 : Code := comp right rPay22

@[simp] theorem val_rV (v f k : ℕ) : val rV (Nat.pair v (Nat.pair f k)) = v := by
  rw [rV, val_left', Nat.unpair_pair]

@[simp] theorem val_rF (v f k : ℕ) : val rF (Nat.pair v (Nat.pair f k)) = f := by
  rw [rF, val_comp, val_right', val_left', Nat.unpair_pair, Nat.unpair_pair]

@[simp] theorem val_rK (v f k : ℕ) : val rK (Nat.pair v (Nat.pair f k)) = k := by
  rw [rK, val_comp, val_right', val_right', Nat.unpair_pair, Nat.unpair_pair]

@[simp] theorem val_rTag (v f k : ℕ) : val rTag (Nat.pair v (Nat.pair f k)) = f.unpair.1 := by
  rw [rTag, val_comp, val_left', val_rF]

@[simp] theorem val_rPay (v f k : ℕ) : val rPay (Nat.pair v (Nat.pair f k)) = f.unpair.2 := by
  rw [rPay, val_comp, val_right', val_rF]

@[simp] theorem val_rPay1 (v f k : ℕ) :
    val rPay1 (Nat.pair v (Nat.pair f k)) = f.unpair.2.unpair.1 := by
  rw [rPay1, val_comp, val_left', val_rPay]

@[simp] theorem val_rPay2 (v f k : ℕ) :
    val rPay2 (Nat.pair v (Nat.pair f k)) = f.unpair.2.unpair.2 := by
  rw [rPay2, val_comp, val_right', val_rPay]

@[simp] theorem val_rPay21 (v f k : ℕ) :
    val rPay21 (Nat.pair v (Nat.pair f k)) = f.unpair.2.unpair.2.unpair.1 := by
  rw [rPay21, val_comp, val_left', val_rPay2]

@[simp] theorem val_rPay22 (v f k : ℕ) :
    val rPay22 (Nat.pair v (Nat.pair f k)) = f.unpair.2.unpair.2.unpair.2 := by
  rw [rPay22, val_comp, val_right', val_rPay2]

@[simp] theorem val_rPay221 (v f k : ℕ) :
    val rPay221 (Nat.pair v (Nat.pair f k)) = f.unpair.2.unpair.2.unpair.2.unpair.1 := by
  rw [rPay221, val_comp, val_left', val_rPay22]

@[simp] theorem val_rPay222 (v f k : ℕ) :
    val rPay222 (Nat.pair v (Nat.pair f k)) = f.unpair.2.unpair.2.unpair.2.unpair.2 := by
  rw [rPay222, val_comp, val_right', val_rPay22]

theorem rfindFree_rV : RfindFree rV := trivial
theorem rfindFree_rF : RfindFree rF := ⟨trivial, trivial⟩
theorem rfindFree_rK : RfindFree rK := ⟨trivial, trivial⟩
theorem rfindFree_rTag : RfindFree rTag := ⟨trivial, rfindFree_rF⟩
theorem rfindFree_rPay : RfindFree rPay := ⟨trivial, rfindFree_rF⟩
theorem rfindFree_rPay1 : RfindFree rPay1 := ⟨trivial, rfindFree_rPay⟩
theorem rfindFree_rPay2 : RfindFree rPay2 := ⟨trivial, rfindFree_rPay⟩
theorem rfindFree_rPay21 : RfindFree rPay21 := ⟨trivial, rfindFree_rPay2⟩
theorem rfindFree_rPay22 : RfindFree rPay22 := ⟨trivial, rfindFree_rPay2⟩
theorem rfindFree_rPay221 : RfindFree rPay221 := ⟨trivial, rfindFree_rPay22⟩
theorem rfindFree_rPay222 : RfindFree rPay222 := ⟨trivial, rfindFree_rPay22⟩

/-! ### The frames' branches -/

/-- Tag 0 — a pair's left value. -/
def rB0 : Code :=
  comp cDescend (pair rPay1 (pair rPay2
    (comp cStkCons (pair (pair (constCode 1) rV) rK))))

/-- Tag 1 — a pair's right value. -/
def rB1 : Code := comp cRet (pair (pair rPay rV) rK)

/-- Tag 2 — a composition's inner value. -/
def rB2 : Code := comp cDescend (pair rPay (pair rV rK))

/-- Tag 3's else — the loop takes another turn. -/
def rB3loop : Code :=
  comp cDescend (pair rPay1 (pair (pair rPay21 (pair rPay221 rV))
    (comp cStkCons (pair (pair (constCode 3)
      (pair rPay1 (pair rPay21
        (pair (comp succ rPay221) (comp cPred rPay222))))) rK))))

/-- Tag 4's else — the search probes again. -/
def rB4search : Code :=
  comp cDescend (pair rPay1 (pair (pair rPay21 (comp succ rPay22))
    (comp cStkCons (pair (pair (constCode 4)
      (pair rPay1 (pair rPay21 (comp succ rPay22)))) rK))))

/-- The default — a stuck frame. -/
def rBdef : Code := comp cRet (pair rV (comp cStkCons (pair rF rK)))

/-! ### Each frame branch's value -/

@[simp] theorem val_rB0 (v f k : ℕ) :
    val rB0 (Nat.pair v (Nat.pair f k)) =
      BoundedInterp.descend f.unpair.2.unpair.1 f.unpair.2.unpair.2
        (BoundedInterp.stkCons (BoundedInterp.frame 1 v) k) := by
  rw [rB0, val_comp, val_pair, val_pair, val_comp, val_pair, val_pair, val_constCode,
    val_rPay1, val_rPay2, val_rV, val_rK, val_cStkCons, val_cDescend, BoundedInterp.frame]

@[simp] theorem val_rB1 (v f k : ℕ) :
    val rB1 (Nat.pair v (Nat.pair f k)) = BoundedInterp.ret (Nat.pair f.unpair.2 v) k := by
  rw [rB1, val_comp, val_pair, val_pair, val_rPay, val_rV, val_rK, val_cRet]

@[simp] theorem val_rB2 (v f k : ℕ) :
    val rB2 (Nat.pair v (Nat.pair f k)) = BoundedInterp.descend f.unpair.2 v k := by
  rw [rB2, val_comp, val_pair, val_pair, val_rPay, val_rV, val_rK, val_cDescend]

@[simp] theorem val_rB3loop (v f k : ℕ) :
    val rB3loop (Nat.pair v (Nat.pair f k)) =
      BoundedInterp.descend f.unpair.2.unpair.1
        (Nat.pair f.unpair.2.unpair.2.unpair.1
          (Nat.pair f.unpair.2.unpair.2.unpair.2.unpair.1 v))
        (BoundedInterp.stkCons (BoundedInterp.frame 3 (Nat.pair f.unpair.2.unpair.1
          (Nat.pair f.unpair.2.unpair.2.unpair.1
            (Nat.pair (f.unpair.2.unpair.2.unpair.2.unpair.1 + 1)
              (f.unpair.2.unpair.2.unpair.2.unpair.2 - 1))))) k) := by
  simp only [rB3loop, val_comp, val_pair, val_constCode, val_succ', val_cPred, val_rPay1,
    val_rPay21, val_rPay221, val_rPay222, val_rV, val_rK, val_cStkCons, val_cDescend,
    BoundedInterp.frame]

@[simp] theorem val_rB4search (v f k : ℕ) :
    val rB4search (Nat.pair v (Nat.pair f k)) =
      BoundedInterp.descend f.unpair.2.unpair.1
        (Nat.pair f.unpair.2.unpair.2.unpair.1 (f.unpair.2.unpair.2.unpair.2 + 1))
        (BoundedInterp.stkCons (BoundedInterp.frame 4 (Nat.pair f.unpair.2.unpair.1
          (Nat.pair f.unpair.2.unpair.2.unpair.1 (f.unpair.2.unpair.2.unpair.2 + 1)))) k) := by
  simp only [rB4search, val_comp, val_pair, val_constCode, val_succ', val_rPay1, val_rPay21,
    val_rPay22, val_rK, val_cStkCons, val_cDescend, BoundedInterp.frame]

@[simp] theorem val_rBdef (v f k : ℕ) :
    val rBdef (Nat.pair v (Nat.pair f k)) = BoundedInterp.ret v (BoundedInterp.stkCons f k) := by
  rw [rBdef, val_comp, val_pair, val_comp, val_pair, val_rV, val_rF, val_rK, val_cStkCons,
    val_cRet]

theorem rfindFree_rB0 : RfindFree rB0 :=
  ⟨rfindFree_cDescend, rfindFree_rPay1, rfindFree_rPay2,
    rfindFree_cStkCons, ⟨rfindFree_constCode 1, rfindFree_rV⟩, rfindFree_rK⟩

theorem rfindFree_rB1 : RfindFree rB1 :=
  ⟨rfindFree_cRet, ⟨rfindFree_rPay, rfindFree_rV⟩, rfindFree_rK⟩

theorem rfindFree_rB2 : RfindFree rB2 :=
  ⟨rfindFree_cDescend, rfindFree_rPay, rfindFree_rV, rfindFree_rK⟩

theorem rfindFree_rB3loop : RfindFree rB3loop :=
  ⟨rfindFree_cDescend, rfindFree_rPay1,
    ⟨rfindFree_rPay21, rfindFree_rPay221, rfindFree_rV⟩,
    rfindFree_cStkCons,
    ⟨rfindFree_constCode 3, rfindFree_rPay1, rfindFree_rPay21,
      ⟨trivial, rfindFree_rPay221⟩, rfindFree_cPred, rfindFree_rPay222⟩,
    rfindFree_rK⟩

theorem rfindFree_rB4search : RfindFree rB4search :=
  ⟨rfindFree_cDescend, rfindFree_rPay1,
    ⟨rfindFree_rPay21, trivial, rfindFree_rPay22⟩,
    rfindFree_cStkCons,
    ⟨rfindFree_constCode 4, rfindFree_rPay1, rfindFree_rPay21, trivial, rfindFree_rPay22⟩,
    rfindFree_rK⟩

theorem rfindFree_rBdef : RfindFree rBdef :=
  ⟨rfindFree_cRet, rfindFree_rV, rfindFree_cStkCons, rfindFree_rF, rfindFree_rK⟩

attribute [local irreducible] rB0 rB1 rB2 rB3loop rB4search rBdef

/-! ### The two inner selections, then the tag tree -/

/-- Tag 3's branch: the loop, done or turning. -/
def rB3 : Code := cSel (cEqK 0 rPay222) (comp cRet (pair rV rK)) rB3loop

@[simp] theorem val_rB3 (v f k : ℕ) :
    val rB3 (Nat.pair v (Nat.pair f k)) =
      (if f.unpair.2.unpair.2.unpair.2.unpair.2 = 0 then BoundedInterp.ret v k
       else val rB3loop (Nat.pair v (Nat.pair f k))) := by
  rw [rB3, val_cSel, val_cEqK, val_rPay222, val_comp, val_pair, val_rV, val_rK, val_cRet]
  by_cases h : f.unpair.2.unpair.2.unpair.2.unpair.2 = 0 <;>
    simp only [h, reduceCtorEq, if_true, if_false]

/-- Tag 4's branch: the search, found or probing. -/
def rB4 : Code := cSel (cEqK 0 rV) (comp cRet (pair rPay22 rK)) rB4search

@[simp] theorem val_rB4 (v f k : ℕ) :
    val rB4 (Nat.pair v (Nat.pair f k)) =
      (if v = 0 then BoundedInterp.ret f.unpair.2.unpair.2.unpair.2 k
       else val rB4search (Nat.pair v (Nat.pair f k))) := by
  rw [rB4, val_cSel, val_cEqK, val_rV, val_comp, val_pair, val_rPay22, val_rK, val_cRet]
  by_cases h : v = 0 <;>
    simp only [h, reduceCtorEq, if_true, if_false]

theorem rfindFree_rB3 : RfindFree rB3 :=
  rfindFree_cSel (rfindFree_cEqK 0 rfindFree_rPay222)
    ⟨rfindFree_cRet, rfindFree_rV, rfindFree_rK⟩ rfindFree_rB3loop

theorem rfindFree_rB4 : RfindFree rB4 :=
  rfindFree_cSel (rfindFree_cEqK 0 rfindFree_rV)
    ⟨rfindFree_cRet, rfindFree_rPay22, rfindFree_rK⟩ rfindFree_rB4search

attribute [local irreducible] rB3 rB4

/-- **The returning step as a code.** -/
def stepReturnU : Code :=
  cSel (cEqK 0 rTag) rB0
    (cSel (cEqK 1 rTag) rB1
      (cSel (cEqK 2 rTag) rB2
        (cSel (cEqK 3 rTag) rB3
          (cSel (cEqK 4 rTag) rB4 rBdef))))

theorem val_stepReturnU (v f k : ℕ) :
    val stepReturnU (Nat.pair v (Nat.pair f k)) = stepReturnArith v f k := by
  simp only [stepReturnU, val_cSel, val_cEqK, val_rTag, val_rB0, val_rB1, val_rB2, val_rB3,
    val_rB4, val_rB3loop, val_rB4search, val_rBdef, stepReturnArith, BoundedInterp.frPay]
  by_cases h0 : f.unpair.1 = 0
  · simp [h0]
  · by_cases h1 : f.unpair.1 = 1
    · simp [h1]
    · by_cases h2 : f.unpair.1 = 2
      · simp [h2]
      · by_cases h3 : f.unpair.1 = 3
        · simp only [h3, Nat.reduceEqDiff, reduceIte]
        · by_cases h4 : f.unpair.1 = 4
          · simp only [h4, Nat.reduceEqDiff, reduceIte]
          · simp only [h0, h1, h2, h3, h4, reduceIte]

theorem rfindFree_stepReturnU : RfindFree stepReturnU :=
  rfindFree_cSel (rfindFree_cEqK 0 rfindFree_rTag) rfindFree_rB0
    (rfindFree_cSel (rfindFree_cEqK 1 rfindFree_rTag) rfindFree_rB1
      (rfindFree_cSel (rfindFree_cEqK 2 rfindFree_rTag) rfindFree_rB2
        (rfindFree_cSel (rfindFree_cEqK 3 rfindFree_rTag) rfindFree_rB3
          (rfindFree_cSel (rfindFree_cEqK 4 rfindFree_rTag) rfindFree_rB4 rfindFree_rBdef))))

/-- **The brief's law, as a corollary.** -/
theorem val_stepReturnU_eq (v f k : ℕ) :
    val stepReturnU (Nat.pair v (Nat.pair f k)) = BoundedInterp.stepReturn v f k := by
  rw [val_stepReturnU, stepReturnArith_eq]

/-! ## The step function, assembled

Three outer tests and two group codes. The capstone's proof is a five-way composition — halt, mode,
cell test, and the two group laws — rather than a walk over sixteen leaves; that reduction is what
splitting the step into `stepDescendU` and `stepReturnU` bought. -/

/-- The current object's first component. -/ def uCur1 : Code := comp left cCfCur
/-- The current object's second component. -/ def uCur2 : Code := comp right cCfCur
/-- The stack's top frame. -/ def uHead : Code := comp cStkHead cCfStk
/-- The stack's tail. -/ def uTail : Code := comp cStkTail cCfStk

@[simp] theorem val_uCur1 (s : ℕ) : val uCur1 s = (BoundedInterp.cfCur s).unpair.1 := by
  rw [uCur1, val_comp, val_left', val_cCfCur]

@[simp] theorem val_uCur2 (s : ℕ) : val uCur2 s = (BoundedInterp.cfCur s).unpair.2 := by
  rw [uCur2, val_comp, val_right', val_cCfCur]

@[simp] theorem val_uHead (s : ℕ) :
    val uHead s = BoundedInterp.stkHead (BoundedInterp.cfStk s) := by
  rw [uHead, val_comp, val_cCfStk, val_cStkHead]

@[simp] theorem val_uTail (s : ℕ) :
    val uTail s = BoundedInterp.stkTail (BoundedInterp.cfStk s) := by
  rw [uTail, val_comp, val_cCfStk, val_cStkTail]

/-- The descending arm, fed the step's three slots. -/
def uDescend : Code := comp stepDescendU (pair uCur1 (pair uCur2 cCfStk))

/-- The returning arm, fed the value, the top frame and the tail. -/
def uReturn : Code := comp stepReturnU (pair cCfCur (pair uHead uTail))

@[simp] theorem val_uDescend (s : ℕ) :
    val uDescend s = BoundedInterp.stepDescend (BoundedInterp.cfCur s).unpair.1
      (BoundedInterp.cfCur s).unpair.2 (BoundedInterp.cfStk s) := by
  rw [uDescend, val_comp, val_pair, val_pair, val_uCur1, val_uCur2, val_cCfStk,
    val_stepDescendU_eq]

@[simp] theorem val_uReturn (s : ℕ) :
    val uReturn s = BoundedInterp.stepReturn (BoundedInterp.cfCur s)
      (BoundedInterp.stkHead (BoundedInterp.cfStk s))
      (BoundedInterp.stkTail (BoundedInterp.cfStk s)) := by
  rw [uReturn, val_comp, val_pair, val_pair, val_cCfCur, val_uHead, val_uTail,
    val_stepReturnU_eq]

theorem rfindFree_uCur1 : RfindFree uCur1 := ⟨trivial, rfindFree_cCfCur⟩
theorem rfindFree_uCur2 : RfindFree uCur2 := ⟨trivial, rfindFree_cCfCur⟩
theorem rfindFree_uHead : RfindFree uHead := ⟨rfindFree_cStkHead, rfindFree_cCfStk⟩
theorem rfindFree_uTail : RfindFree uTail := ⟨rfindFree_cStkTail, rfindFree_cCfStk⟩
theorem rfindFree_uDescend : RfindFree uDescend :=
  ⟨rfindFree_stepDescendU, rfindFree_uCur1, rfindFree_uCur2, rfindFree_cCfStk⟩
theorem rfindFree_uReturn : RfindFree uReturn :=
  ⟨rfindFree_stepReturnU, rfindFree_cCfCur, rfindFree_uHead, rfindFree_uTail⟩

attribute [local irreducible] uDescend uReturn

/-- **The interpreter's step function, as a code.** -/
def stepU : Code :=
  cSel cIsHalt cId
    (cSel (cEqK 0 cCfMode) uDescend
      (cSel (comp cStkIsCons cCfStk) uReturn cId))

/-- **The capstone value law.** The code computes the mathematical layer's step function, on every
numeral — halted and stuck configurations included. -/
theorem val_stepU (s : ℕ) : val stepU s = BoundedInterp.stepUFn s := by
  rw [stepU, BoundedInterp.stepUFn]
  simp only [val_cSel, val_cIsHalt, val_cEqK, val_cCfMode, val_comp, val_cCfStk, val_cStkIsCons,
    val_cId, val_uDescend, val_uReturn]
  by_cases hh : BoundedInterp.isHalt s = true
  · simp [hh]
  · by_cases hm : BoundedInterp.cfMode s = 0
    · simp [hh, hm]
    · by_cases hc : BoundedInterp.stkIsCons (BoundedInterp.cfStk s) = true
      · simp [hh, hm, hc]
      · simp [hh, hm, hc]

/-- **Nothing in the step searches.** The realization is built from bounded recursion and the
constructors alone, so it lies in the fragment on which the workspace account is total. -/
theorem rfindFree_stepU : RfindFree stepU :=
  rfindFree_cSel rfindFree_cIsHalt rfindFree_cId
    (rfindFree_cSel (rfindFree_cEqK 0 rfindFree_cCfMode) rfindFree_uDescend
      (rfindFree_cSel ⟨rfindFree_cStkIsCons, rfindFree_cCfStk⟩ rfindFree_uReturn rfindFree_cId))

/-! ## Workspace: the shape a bound can take

The target shape for one step is "the wider of the input and the output, plus a constant" — the
form `TimeCost.spaceCost_prec_le` receives. `SpaceIO c K` names it.

Whether a composite meets it is not automatic. `TimeCost.spaceCost_comp` charges a composition the
workspace of the *intermediate* value as well, and an intermediate is bounded by neither the input
nor the output in general. What rescues a composition is that its intermediates are no larger than
its input — `Shrinking` names that — or that they are sub-objects of its output. -/

/-- A code whose workspace is the wider of its input and output, plus `K`. -/
def SpaceIO (c : Code) (K : ℕ) : Prop :=
  ∀ x, spaceCost c x ≤ max (Nat.size x) (Nat.size (val c x)) + K

/-- A code whose output is never wider than its input. -/
def Shrinking (c : Code) : Prop := ∀ x, Nat.size (val c x) ≤ Nat.size x

theorem shrinking_left : Shrinking left := fun x =>
  Nat.size_le_size (Nat.unpair_left_le x)

theorem shrinking_right : Shrinking right := fun x =>
  Nat.size_le_size (Nat.unpair_right_le x)

theorem spaceIO_left : SpaceIO left 0 := fun x => by
  rw [spaceCost_left, val_left']
  omega

theorem spaceIO_right : SpaceIO right 0 := fun x => by
  rw [spaceCost_right, val_right']
  omega

/-- **Composition preserves the shape when the inner code shrinks.** The intermediate is then no
wider than the input, so it is already inside the bound. -/
theorem spaceIO_comp {f g : Code} {Kf Kg : ℕ}
    (hf : SpaceIO f Kf) (hg : SpaceIO g Kg) (hsg : Shrinking g) :
    SpaceIO (comp f g) (max Kf Kg) := by
  intro x
  rw [spaceCost_comp, val_comp]
  have h1 := hg x
  have h2 := hf (val g x)
  have h3 := hsg x
  omega

theorem shrinking_comp {f g : Code} (hf : Shrinking f) (hg : Shrinking g) :
    Shrinking (comp f g) := by
  intro x
  rw [val_comp]
  exact le_trans (hf (val g x)) (hg x)

/-! ### The projection group

Every configuration and frame accessor is a composition of `left` and `right`, so each shrinks and
each meets the shape with no constant at all. -/

theorem shrinking_cCfMode : Shrinking cCfMode := shrinking_left
theorem shrinking_cCfCur : Shrinking cCfCur := shrinking_comp shrinking_left shrinking_right
theorem shrinking_cCfStk : Shrinking cCfStk := shrinking_comp shrinking_right shrinking_right
theorem shrinking_cFrTag : Shrinking cFrTag := shrinking_left
theorem shrinking_cFrPay : Shrinking cFrPay := shrinking_right

theorem spaceIO_cCfMode : SpaceIO cCfMode 0 := spaceIO_left
theorem spaceIO_cFrTag : SpaceIO cFrTag 0 := spaceIO_left
theorem spaceIO_cFrPay : SpaceIO cFrPay 0 := spaceIO_right

theorem spaceIO_cCfCur : SpaceIO cCfCur 0 := by
  have h := spaceIO_comp spaceIO_left spaceIO_right shrinking_right
  simpa [cCfCur] using h

theorem spaceIO_cCfStk : SpaceIO cCfStk 0 := by
  have h := spaceIO_comp spaceIO_right spaceIO_right shrinking_right
  simpa [cCfStk] using h

theorem spaceIO_cHaltVal : SpaceIO cHaltVal 0 := spaceIO_cCfCur

/-! ### Where the shape breaks: forming a pair

The projection group meets the shape because everything it computes is a piece of what it was given.
The arithmetic layer does not, and the reason is visible in the smallest possible instance.

`TimeCost.spaceCost_pair` charges a `pair` node the width of the pair it *forms*, and Cantor pairing
of a value with itself is twice as wide as the value. `cDbl` — doubling, the shortest arithmetic
code there is — forms `⟨n, n⟩` on the way to producing `2 * n`. Its input is `n` bits wide, its
output one bit more, and its workspace is `2n` bits: **no constant closes that gap**, because the
gap grows with the input.

`not_spaceIO_cDbl` proves it. Every arithmetic code above `cDbl` inherits the problem — `cMul`'s
bounded-recursion step forms `⟨x, acc⟩`, `cStkCons` forms the pairs feeding its shifts — so the
workspace of the realized step is bounded by a *multiple* of the wider of its input and output, not
by that width plus a constant. The multiple is absolute (the code is fixed, so its pair-nesting
depth is), but it is a multiple. -/

private theorem size_two_pow (m : ℕ) : Nat.size (2 ^ m) = m + 1 := by
  have h1 : m < Nat.size (2 ^ m) := Nat.lt_size.2 (le_refl _)
  have h2 : Nat.size (2 ^ m) ≤ m + 1 :=
    Nat.size_le.2 (Nat.pow_lt_pow_right (by norm_num) (by omega))
  omega

/-- Doubling forms the pair of its input with itself, so that pair's width is a lower bound on
doubling's workspace. -/
private theorem size_pair_le_spaceCost_cDbl (x : ℕ) :
    Nat.size (Nat.pair x x) ≤ spaceCost cDbl x := by
  rw [cDbl, spaceCost_comp]
  refine le_trans ?_ (le_max_left (spaceCost (pair cId cId) x) _)
  rw [spaceCost_pair]
  simp only [val_cId]
  exact le_max_right (max (spaceCost cId x) (spaceCost cId x)) _

/-- **The shape fails already at doubling.** For every constant `K` there is an input on which
`cDbl`'s workspace exceeds the wider of its input and output by more than `K` — because forming
`⟨n, n⟩` costs twice `n`'s width while the output costs one bit more than it. -/
theorem not_spaceIO_cDbl : ∀ K, ¬ SpaceIO cDbl K := by
  intro K h
  have hn := h (2 ^ (K + 3))
  have hsz : Nat.size (2 ^ (K + 3)) = K + 4 := size_two_pow (K + 3)
  have hval : val cDbl (2 ^ (K + 3)) = 2 * 2 ^ (K + 3) := val_cDbl _
  have hval2 : (2 : ℕ) * 2 ^ (K + 3) = 2 ^ (K + 4) := by ring
  have hvsz : Nat.size (val cDbl (2 ^ (K + 3))) = K + 5 := by
    rw [hval, hval2, size_two_pow]
  -- the formed pair is a lower bound on the workspace
  have hlow := size_pair_le_spaceCost_cDbl (2 ^ (K + 3))
  -- and that pair is at least the square
  have hsq : (2 : ℕ) ^ (2 * K + 6) ≤ Nat.pair (2 ^ (K + 3)) (2 ^ (K + 3)) := by
    rw [Nat.pair, if_neg (by omega)]
    have : (2 : ℕ) ^ (2 * K + 6) = 2 ^ (K + 3) * 2 ^ (K + 3) := by
      rw [← pow_add]; ring_nf
    omega
  have hbig : 2 * K + 6 < Nat.size (Nat.pair (2 ^ (K + 3)) (2 ^ (K + 3))) := Nat.lt_size.2 hsq
  rw [hsz, hvsz] at hn
  omega

/-! ### The prec-free builders

`spaceCost` is a maximum over the widths of the values a code's nodes touch, so a bound on those
widths *is* the workspace bound. For the codes that only take a configuration apart and put one back
together, every value touched is a piece either of the input or of the output — so the shape holds
with no constant. -/

@[simp] theorem spaceCost_cId (v : ℕ) : spaceCost cId v = Nat.size v := by
  rw [cId, spaceCost_pair, spaceCost_left, spaceCost_right, val_left', val_right',
    Nat.pair_unpair]
  have h1 : Nat.size v.unpair.1 ≤ Nat.size v := Nat.size_le_size (Nat.unpair_left_le v)
  have h2 : Nat.size v.unpair.2 ≤ Nat.size v := Nat.size_le_size (Nat.unpair_right_le v)
  omega

theorem spaceIO_cId : SpaceIO cId 0 := by
  intro x
  rw [spaceCost_cId, val_cId]
  omega

theorem shrinking_cId : Shrinking cId := by
  intro x
  rw [val_cId]

theorem spaceCost_constCode (c v : ℕ) :
    spaceCost (constCode c) v ≤ max (Nat.size v) (Nat.size c) := by
  induction c with
  | zero => rw [constCode, spaceCost_zero]
  | succ d ih =>
      rw [constCode, spaceCost_comp, val_constCode, spaceCost_succ]
      have hd : Nat.size d ≤ Nat.size (d + 1) := Nat.size_le_size (by omega)
      omega

/-- A value that a pairing contains is no wider than the pairing. -/
private theorem size_le_of_pair_left (a b : ℕ) : Nat.size a ≤ Nat.size (Nat.pair a b) :=
  Nat.size_le_size (Nat.left_le_pair a b)

private theorem size_le_of_pair_right (a b : ℕ) : Nat.size b ≤ Nat.size (Nat.pair a b) :=
  Nat.size_le_size (Nat.right_le_pair a b)

/-- **A returning configuration is built within its own width.** -/
theorem spaceIO_cRet : SpaceIO cRet 0 := by
  intro x
  simp only [cRet, spaceCost_pair, val_pair, val_constCode, val_cId]
  have hc := spaceCost_constCode 1 x
  have hi : spaceCost cId x = Nat.size x := spaceCost_cId x
  have h1 : Nat.size (1 : ℕ) ≤ Nat.size (Nat.pair 1 x) := size_le_of_pair_left 1 x
  omega

/-! ### Selection is strict: both arms are charged

A selection is `comp cIte (pair b (pair x y))`. The arithmetic that picks a branch runs *after* the
triple `⟨guard, ⟨then, else⟩⟩` has been built, so building it evaluates **both** arms. There is no
laziness to exploit: the workspace of a selection is at least the workspace of each arm, taken and
untaken alike.

That is load-bearing for the total. The interpreter's step evaluates all sixteen of its branches on
every input, including the ones whose guard is false — a returning configuration still runs the
descending code on whatever its slots happen to hold. Those runs compute nonsense, but they compute
it from pieces of the input, so their widths are still bounded in terms of the input's; the bound
survives, and the constant has to cover them. -/

theorem spaceCost_cSel_ge (b x y : Code) (n : ℕ) :
    max (spaceCost x n) (spaceCost y n) ≤ spaceCost (cSel b x y) n := by
  rw [cSel, spaceCost_comp]
  refine le_trans ?_ (le_max_left (spaceCost (pair b (pair x y)) n) _)
  rw [spaceCost_pair]
  refine le_trans ?_ (le_max_left (max (spaceCost b n) (spaceCost (pair x y) n)) _)
  refine le_trans ?_ (le_max_right (spaceCost b n) _)
  rw [spaceCost_pair]
  exact le_max_left (max (spaceCost x n) (spaceCost y n)) _

/-! ### The bounded-recursion projections

Both projections a fold's step uses read their whole input, so each costs exactly the input's width
and nothing more — the first place a value bound is exact rather than estimated. -/

theorem spaceCost_cAcc (I : ℕ) : spaceCost cAcc I = Nat.size I := by
  rw [cAcc, spaceCost_comp, spaceCost_right, spaceCost_right, val_right']
  have h1 : Nat.size I.unpair.2 ≤ Nat.size I := Nat.size_le_size (Nat.unpair_right_le I)
  have h2 : Nat.size I.unpair.2.unpair.2 ≤ Nat.size I.unpair.2 :=
    Nat.size_le_size (Nat.unpair_right_le _)
  omega

theorem spaceCost_cCtr (I : ℕ) : spaceCost cCtr I = Nat.size I := by
  rw [cCtr, spaceCost_comp, spaceCost_right, spaceCost_left, val_right']
  have h1 : Nat.size I.unpair.2 ≤ Nat.size I := Nat.size_le_size (Nat.unpair_right_le I)
  have h2 : Nat.size I.unpair.2.unpair.1 ≤ Nat.size I.unpair.2 :=
    Nat.size_le_size (Nat.unpair_left_le _)
  omega

/-! ### Width arithmetic for the folds -/

private theorem size_pair_le' (x y : ℕ) :
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

private theorem size_add_le (a b : ℕ) :
    Nat.size (a + b) ≤ max (Nat.size a) (Nat.size b) + 1 := by
  have ha : a < 2 ^ max (Nat.size a) (Nat.size b) :=
    Nat.lt_of_lt_of_le (Nat.lt_size_self a)
      (Nat.pow_le_pow_right (by norm_num) (le_max_left _ _))
  have hb : b < 2 ^ max (Nat.size a) (Nat.size b) :=
    Nat.lt_of_lt_of_le (Nat.lt_size_self b)
      (Nat.pow_le_pow_right (by norm_num) (le_max_right _ _))
  rw [Nat.size_le, pow_succ]
  omega

/-! ### The additive fold

Addition's fold holds `⟨x, ⟨counter, accumulator⟩⟩`. Two pairings sit between the accumulator and
that triple, so the widest value the fold touches is four times the wider operand, plus a constant
for the carry. That factor of four is a property of how the fold's step reads its argument, not of
how big the numbers are — the same four will appear in every fold below. -/

theorem spaceCost_cAdd (x y : ℕ) :
    spaceCost cAdd (Nat.pair x y) ≤ 4 * max (Nat.size x) (Nat.size y) + 8 := by
  simp only [cAdd]
  induction y with
  | zero =>
      rw [spaceCost_prec_zero, spaceCost_cId]
      omega
  | succ m ih =>
      rw [spaceCost_prec_succ]
      have hval : val (prec cId (comp succ cAcc)) (Nat.pair x m) = x + m := val_cAdd x m
      rw [hval]
      have hmono : Nat.size m ≤ Nat.size (m + 1) := Nat.size_le_size (by omega)
      have hstep : spaceCost (comp succ cAcc) (Nat.pair x (Nat.pair m (x + m)))
          ≤ 4 * max (Nat.size x) (Nat.size (m + 1)) + 8 := by
        rw [spaceCost_comp, spaceCost_cAcc, val_cAcc, spaceCost_succ]
        have hacc : Nat.size (x + m) ≤ max (Nat.size x) (Nat.size m) + 1 := size_add_le x m
        have hacc1 : Nat.size (x + m + 1) ≤ max (Nat.size (x + m)) (Nat.size 1) + 1 :=
          size_add_le (x + m) 1
        have hinner : Nat.size (Nat.pair m (x + m))
            ≤ 2 * max (Nat.size m) (Nat.size (x + m)) := size_pair_le' m (x + m)
        have houter : Nat.size (Nat.pair x (Nat.pair m (x + m)))
            ≤ 2 * max (Nat.size x) (Nat.size (Nat.pair m (x + m))) :=
          size_pair_le' x (Nat.pair m (x + m))
        have hs1 : Nat.size (1 : ℕ) = 1 := by decide
        omega
      omega

/-! ### The predecessor chain, and subtraction

Subtraction counts predecessors, so its bound rests on the predecessor's, which in turn rests on the
re-shaping code that hands a one-argument value to a fold. Each layer adds a pairing, and each
pairing doubles — the same accounting as addition, one level deeper. -/

theorem spaceCost_cShape0 (v : ℕ) : spaceCost OneDL.cShape0 v ≤ 2 * Nat.size v := by
  simp only [OneDL.cShape0, spaceCost_pair, spaceCost_zero, spaceCost_left, spaceCost_right,
    val_zero', val_pair, val_left', val_right', Nat.pair_unpair]
  have h1 : Nat.size v.unpair.1 ≤ Nat.size v := Nat.size_le_size (Nat.unpair_left_le v)
  have h2 : Nat.size v.unpair.2 ≤ Nat.size v := Nat.size_le_size (Nat.unpair_right_le v)
  have h3 : Nat.size (Nat.pair 0 v) ≤ 2 * max (Nat.size 0) (Nat.size v) := size_pair_le' 0 v
  have h0 : Nat.size (0 : ℕ) = 0 := by decide
  omega

theorem spaceCost_cPredCore (a n : ℕ) :
    spaceCost cPredCore (Nat.pair a n) ≤ 4 * max (Nat.size a) (Nat.size n) + 4 := by
  simp only [cPredCore]
  induction n with
  | zero =>
      rw [spaceCost_prec_zero, spaceCost_zero]
      have h0 : Nat.size (0 : ℕ) = 0 := by decide
      omega
  | succ m ih =>
      rw [spaceCost_prec_succ]
      have hval : val (prec zero cCtr) (Nat.pair a m) = m - 1 := val_cPredCore a m
      rw [hval, spaceCost_cCtr]
      have hmono : Nat.size m ≤ Nat.size (m + 1) := Nat.size_le_size (by omega)
      have hpm : Nat.size (m - 1) ≤ Nat.size m := Nat.size_le_size (by omega)
      have hinner : Nat.size (Nat.pair m (m - 1)) ≤ 2 * max (Nat.size m) (Nat.size (m - 1)) :=
        size_pair_le' m (m - 1)
      have houter : Nat.size (Nat.pair a (Nat.pair m (m - 1)))
          ≤ 2 * max (Nat.size a) (Nat.size (Nat.pair m (m - 1))) :=
        size_pair_le' a (Nat.pair m (m - 1))
      omega

theorem spaceCost_cPred (v : ℕ) : spaceCost cPred v ≤ 4 * Nat.size v + 4 := by
  rw [cPred, spaceCost_comp, OneDL.val_cShape0]
  have h1 := spaceCost_cShape0 v
  have h2 := spaceCost_cPredCore 0 v
  have h0 : Nat.size (0 : ℕ) = 0 := by decide
  omega

theorem spaceCost_cSub (x y : ℕ) :
    spaceCost cSub (Nat.pair x y) ≤ 8 * max (Nat.size x) (Nat.size y) + 16 := by
  simp only [cSub]
  induction y with
  | zero =>
      rw [spaceCost_prec_zero, spaceCost_cId]
      omega
  | succ m ih =>
      rw [spaceCost_prec_succ]
      have hval : val (prec cId (comp cPred cAcc)) (Nat.pair x m) = x - m := val_cSub x m
      rw [hval, spaceCost_comp, spaceCost_cAcc, val_cAcc]
      have hmono : Nat.size m ≤ Nat.size (m + 1) := Nat.size_le_size (by omega)
      have hsub : Nat.size (x - m) ≤ Nat.size x := Nat.size_le_size (by omega)
      have hp := spaceCost_cPred (x - m)
      have hinner : Nat.size (Nat.pair m (x - m)) ≤ 2 * max (Nat.size m) (Nat.size (x - m)) :=
        size_pair_le' m (x - m)
      have houter : Nat.size (Nat.pair x (Nat.pair m (x - m)))
          ≤ 2 * max (Nat.size x) (Nat.size (Nat.pair m (x - m))) :=
        size_pair_le' x (Nat.pair m (x - m))
      omega

/-! ### Multiplication

Multiplication counts additions, so its fold carries an accumulator as wide as the product — the
first place the accumulator is genuinely wider than either operand. The bound is stated in the sum
of the operands' widths rather than their maximum, because that is what a product costs. -/

private theorem size_mul_le (a b : ℕ) : Nat.size (a * b) ≤ Nat.size a + Nat.size b := by
  rw [Nat.size_le, pow_add]
  have ha := Nat.lt_size_self a
  have hb := Nat.lt_size_self b
  have hpa : (0 : ℕ) < 2 ^ Nat.size a := by positivity
  have hpb : (0 : ℕ) < 2 ^ Nat.size b := by positivity
  nlinarith

theorem spaceCost_cMul (x y : ℕ) :
    spaceCost cMul (Nat.pair x y) ≤ 8 * (Nat.size x + Nat.size y) + 16 := by
  simp only [cMul]
  induction y with
  | zero =>
      rw [spaceCost_prec_zero, spaceCost_zero]
      have h0 : Nat.size (0 : ℕ) = 0 := by decide
      omega
  | succ m ih =>
      rw [spaceCost_prec_succ]
      have hval : val (prec zero (comp cAdd (pair left cAcc))) (Nat.pair x m) = x * m :=
        val_cMul x m
      rw [hval, spaceCost_comp, spaceCost_pair, spaceCost_left, spaceCost_cAcc, val_pair,
        val_left', val_cAcc, Nat.unpair_pair]
      have hmono : Nat.size m ≤ Nat.size (m + 1) := Nat.size_le_size (by omega)
      have hprod : Nat.size (x * m) ≤ Nat.size x + Nat.size m := size_mul_le x m
      have hinner : Nat.size (Nat.pair m (x * m)) ≤ 2 * max (Nat.size m) (Nat.size (x * m)) :=
        size_pair_le' m (x * m)
      have houter : Nat.size (Nat.pair x (Nat.pair m (x * m)))
          ≤ 2 * max (Nat.size x) (Nat.size (Nat.pair m (x * m))) :=
        size_pair_le' x (Nat.pair m (x * m))
      have hxp : Nat.size (Nat.pair x (x * m)) ≤ 2 * max (Nat.size x) (Nat.size (x * m)) :=
        size_pair_le' x (x * m)
      have hadd := spaceCost_cAdd x (x * m)
      have hl1 : Nat.size (Nat.pair x (Nat.pair m (x * m))).unpair.1
          ≤ Nat.size (Nat.pair x (Nat.pair m (x * m))) :=
        Nat.size_le_size (Nat.unpair_left_le _)
      -- collapse the nested maxima before the final arithmetic
      have hI : Nat.size (Nat.pair x (Nat.pair m (x * m))) ≤ 4 * (Nat.size x + Nat.size m) := by
        omega
      have hXP : Nat.size (Nat.pair x (x * m)) ≤ 2 * (Nat.size x + Nat.size m) := by omega
      have hA : spaceCost cAdd (Nat.pair x (x * m)) ≤ 4 * (Nat.size x + Nat.size m) + 8 := by
        omega
      dsimp only
      omega

/-! ### Doubling and powers of two

A power of two is exponentially wider than its exponent, so there is no bound on `cPow2` in terms of
its input's *width*: the honest statement is in terms of the exponent's *value*. That is not a
weakness — every call site in the packing layer applies `cPow2` to a width (`frameBits f`, or a
shift exponent built from it), so the value-shaped bound is exactly what composes there. -/

theorem spaceCost_cDbl (v : ℕ) : spaceCost cDbl v ≤ 4 * Nat.size v + 8 := by
  rw [cDbl, spaceCost_comp, spaceCost_pair, spaceCost_cId, val_pair, val_cId]
  have hp : Nat.size (Nat.pair v v) ≤ 2 * max (Nat.size v) (Nat.size v) := size_pair_le' v v
  have ha := spaceCost_cAdd v v
  omega

theorem spaceCost_cPow2Core (a n : ℕ) :
    spaceCost cPow2Core (Nat.pair a n) ≤ 4 * max (Nat.size a) (n + 1) + 8 := by
  simp only [cPow2Core]
  induction n with
  | zero =>
      rw [spaceCost_prec_zero]
      have h := spaceCost_constCode 1 a
      have h1 : Nat.size (1 : ℕ) = 1 := by decide
      omega
  | succ m ih =>
      rw [spaceCost_prec_succ]
      have hval : val (prec (constCode 1) (comp cDbl cAcc)) (Nat.pair a m) = 2 ^ m :=
        val_cPow2Core a m
      rw [hval, spaceCost_comp, spaceCost_cAcc, val_cAcc]
      have hpm : Nat.size (2 ^ m) = m + 1 := size_two_pow m
      have hdb := spaceCost_cDbl (2 ^ m)
      have hms : Nat.size m ≤ m + 1 := le_trans (Nat.size_le.2 Nat.lt_two_pow_self) (by omega)
      have hinner : Nat.size (Nat.pair m (2 ^ m)) ≤ 2 * max (Nat.size m) (Nat.size (2 ^ m)) :=
        size_pair_le' m (2 ^ m)
      have houter : Nat.size (Nat.pair a (Nat.pair m (2 ^ m)))
          ≤ 2 * max (Nat.size a) (Nat.size (Nat.pair m (2 ^ m))) :=
        size_pair_le' a (Nat.pair m (2 ^ m))
      omega

theorem spaceCost_cPow2 (v : ℕ) : spaceCost cPow2 v ≤ 4 * v + 12 := by
  rw [cPow2, spaceCost_comp, OneDL.val_cShape0]
  have h1 := spaceCost_cShape0 v
  have h2 := spaceCost_cPow2Core 0 v
  have h0 : Nat.size (0 : ℕ) = 0 := by decide
  have hsv : Nat.size v ≤ v := Nat.size_le.2 Nat.lt_two_pow_self
  omega

/-! ### The bit gates

The Boolean layer's folds carry a `{0,1}` accumulator, so their step inputs are narrow: the width
comes entirely from the argument being tested, two pairings deep as before. -/

theorem spaceCost_cSwap (v : ℕ) : spaceCost OneDL.cSwap v ≤ 2 * Nat.size v := by
  simp only [OneDL.cSwap, spaceCost_pair, spaceCost_left, spaceCost_right, val_left', val_right']
  have h1 : Nat.size v.unpair.1 ≤ Nat.size v := Nat.size_le_size (Nat.unpair_left_le v)
  have h2 : Nat.size v.unpair.2 ≤ Nat.size v := Nat.size_le_size (Nat.unpair_right_le v)
  have h3 : Nat.size (Nat.pair v.unpair.2 v.unpair.1)
      ≤ 2 * max (Nat.size v.unpair.2) (Nat.size v.unpair.1) :=
    size_pair_le' _ _
  omega

theorem spaceCost_isPosCore (a n : ℕ) :
    spaceCost OneDL.isPosCore (Nat.pair a n) ≤ 4 * max (Nat.size a) (Nat.size n) + 8 := by
  simp only [OneDL.isPosCore]
  induction n with
  | zero =>
      rw [spaceCost_prec_zero, spaceCost_zero]
      have h0 : Nat.size (0 : ℕ) = 0 := by decide
      omega
  | succ m ih =>
      rw [spaceCost_prec_succ]
      have hbit : Nat.size (val (prec zero (constCode 1)) (Nat.pair a m)) ≤ 1 := by
        have := OneDL.val_isPosCore a m
        simp only [OneDL.isPosCore] at this
        rw [this]
        split <;> decide
      have hmono : Nat.size m ≤ Nat.size (m + 1) := Nat.size_le_size (by omega)
      have hcc := spaceCost_constCode 1
        (Nat.pair a (Nat.pair m (val (prec zero (constCode 1)) (Nat.pair a m))))
      have hinner : Nat.size (Nat.pair m (val (prec zero (constCode 1)) (Nat.pair a m)))
          ≤ 2 * max (Nat.size m)
              (Nat.size (val (prec zero (constCode 1)) (Nat.pair a m))) := size_pair_le' _ _
      have houter : Nat.size (Nat.pair a
            (Nat.pair m (val (prec zero (constCode 1)) (Nat.pair a m))))
          ≤ 2 * max (Nat.size a)
              (Nat.size (Nat.pair m (val (prec zero (constCode 1)) (Nat.pair a m)))) :=
        size_pair_le' _ _
      have h1 : Nat.size (1 : ℕ) = 1 := by decide
      omega

theorem spaceCost_cIsPos (v : ℕ) : spaceCost OneDL.cIsPos v ≤ 4 * Nat.size v + 8 := by
  rw [OneDL.cIsPos, spaceCost_comp, OneDL.val_cShape0]
  have h1 := spaceCost_cShape0 v
  have h2 := spaceCost_isPosCore 0 v
  have h0 : Nat.size (0 : ℕ) = 0 := by decide
  omega

theorem spaceCost_notCore (a n : ℕ) :
    spaceCost OneDL.notCore (Nat.pair a n) ≤ 4 * max (Nat.size a) (Nat.size n) + 8 := by
  simp only [OneDL.notCore]
  induction n with
  | zero =>
      rw [spaceCost_prec_zero]
      have h := spaceCost_constCode 1 a
      have h1 : Nat.size (1 : ℕ) = 1 := by decide
      omega
  | succ m ih =>
      rw [spaceCost_prec_succ, spaceCost_zero]
      have hbit : Nat.size (val (prec (constCode 1) zero) (Nat.pair a m)) ≤ 1 := by
        have := OneDL.val_notCore a m
        simp only [OneDL.notCore] at this
        rw [this]
        split <;> decide
      have hmono : Nat.size m ≤ Nat.size (m + 1) := Nat.size_le_size (by omega)
      have hinner : Nat.size (Nat.pair m (val (prec (constCode 1) zero) (Nat.pair a m)))
          ≤ 2 * max (Nat.size m)
              (Nat.size (val (prec (constCode 1) zero) (Nat.pair a m))) := size_pair_le' _ _
      have houter : Nat.size (Nat.pair a
            (Nat.pair m (val (prec (constCode 1) zero) (Nat.pair a m))))
          ≤ 2 * max (Nat.size a)
              (Nat.size (Nat.pair m (val (prec (constCode 1) zero) (Nat.pair a m)))) :=
        size_pair_le' _ _
      have h0 : Nat.size (0 : ℕ) = 0 := by decide
      omega

theorem spaceCost_cNot (v : ℕ) : spaceCost OneDL.cNot v ≤ 4 * Nat.size v + 8 := by
  rw [OneDL.cNot, spaceCost_comp, OneDL.val_cShape0]
  have h1 := spaceCost_cShape0 v
  have h2 := spaceCost_notCore 0 v
  have h0 : Nat.size (0 : ℕ) = 0 := by decide
  omega

/-- Comparison is subtraction followed by a zero test, so it costs what subtraction costs. -/
theorem spaceCost_cLe (x y : ℕ) :
    spaceCost cLe (Nat.pair x y) ≤ 8 * max (Nat.size x) (Nat.size y) + 16 := by
  rw [cLe, spaceCost_comp, val_cSub]
  have h1 := spaceCost_cSub x y
  have h2 := spaceCost_cNot (x - y)
  have h3 : Nat.size (x - y) ≤ Nat.size x := Nat.size_le_size (by omega)
  omega

/-! ### Disjunction and conjunction

Both gates thread `{0,1}` values, so every pair they form is one of four tiny numerals. The width
of a bit gate's workspace therefore comes only from the argument being tested — the gate's own
plumbing is constant. -/

private theorem size_pair_bit {a b : ℕ} (ha : a ≤ 1) (hb : b ≤ 1) :
    Nat.size (Nat.pair a b) ≤ 2 := by
  interval_cases a <;> interval_cases b <;> decide

theorem val_orCore_le_one (a m : ℕ) : val OneDL.orCore (Nat.pair a m) ≤ 1 := by
  cases m with
  | zero =>
      simp only [OneDL.orCore]
      rw [val_prec_zero]
      exact OneDL.val_cIsPos_le_one a
  | succ j =>
      simp only [OneDL.orCore]
      rw [val_prec_succ, val_constCode]

theorem spaceCost_orCore (a n : ℕ) :
    spaceCost OneDL.orCore (Nat.pair a n) ≤ 4 * max (Nat.size a) (Nat.size n) + 16 := by
  simp only [OneDL.orCore]
  induction n with
  | zero =>
      rw [spaceCost_prec_zero]
      have h := spaceCost_cIsPos a
      omega
  | succ m ih =>
      rw [spaceCost_prec_succ]
      have hbit : Nat.size (val (prec OneDL.cIsPos (constCode 1)) (Nat.pair a m)) ≤ 1 := by
        have hb := val_orCore_le_one a m
        simp only [OneDL.orCore] at hb
        exact le_trans (Nat.size_le_size hb) (by decide)
      have hmono : Nat.size m ≤ Nat.size (m + 1) := Nat.size_le_size (by omega)
      have hcc := spaceCost_constCode 1
        (Nat.pair a (Nat.pair m (val (prec OneDL.cIsPos (constCode 1)) (Nat.pair a m))))
      have hinner : Nat.size (Nat.pair m
            (val (prec OneDL.cIsPos (constCode 1)) (Nat.pair a m)))
          ≤ 2 * max (Nat.size m)
              (Nat.size (val (prec OneDL.cIsPos (constCode 1)) (Nat.pair a m))) :=
        size_pair_le' _ _
      have houter : Nat.size (Nat.pair a (Nat.pair m
            (val (prec OneDL.cIsPos (constCode 1)) (Nat.pair a m))))
          ≤ 2 * max (Nat.size a) (Nat.size (Nat.pair m
              (val (prec OneDL.cIsPos (constCode 1)) (Nat.pair a m)))) :=
        size_pair_le' _ _
      have h1 : Nat.size (1 : ℕ) = 1 := by decide
      omega

theorem spaceCost_cOr (v : ℕ) : spaceCost OneDL.cOr v ≤ 4 * Nat.size v + 16 := by
  have hsw : val OneDL.cSwap v = Nat.pair v.unpair.2 v.unpair.1 := by
    conv_lhs => rw [← Nat.pair_unpair v]
    rw [OneDL.val_cSwap]
  rw [OneDL.cOr, spaceCost_comp, hsw]
  have h1 := spaceCost_cSwap v
  have h2 := spaceCost_orCore v.unpair.2 v.unpair.1
  have hl : Nat.size v.unpair.1 ≤ Nat.size v := Nat.size_le_size (Nat.unpair_left_le v)
  have hr : Nat.size v.unpair.2 ≤ Nat.size v := Nat.size_le_size (Nat.unpair_right_le v)
  omega

theorem spaceCost_cAnd (v : ℕ) : spaceCost OneDL.cAnd v ≤ 4 * Nat.size v + 40 := by
  have hl : Nat.size v.unpair.1 ≤ Nat.size v := Nat.size_le_size (Nat.unpair_left_le v)
  have hr : Nat.size v.unpair.2 ≤ Nat.size v := Nat.size_le_size (Nat.unpair_right_le v)
  -- the two negated projections, and the tiny pair they form
  have hb1 : val OneDL.cNot v.unpair.1 ≤ 1 := OneDL.val_cNot_le_one _
  have hb2 : val OneDL.cNot v.unpair.2 ≤ 1 := OneDL.val_cNot_le_one _
  have hpair : Nat.size (Nat.pair (val OneDL.cNot v.unpair.1) (val OneDL.cNot v.unpair.2)) ≤ 2 :=
    size_pair_bit hb1 hb2
  have hn1 := spaceCost_cNot v.unpair.1
  have hn2 := spaceCost_cNot v.unpair.2
  have hinner : spaceCost (pair (comp OneDL.cNot left) (comp OneDL.cNot right)) v
      ≤ 4 * Nat.size v + 8 := by
    rw [spaceCost_pair, spaceCost_comp, spaceCost_comp, spaceCost_left, spaceCost_right,
      val_left', val_right', val_comp, val_comp, val_left', val_right']
    omega
  have hvinner : val (pair (comp OneDL.cNot left) (comp OneDL.cNot right)) v
      = Nat.pair (val OneDL.cNot v.unpair.1) (val OneDL.cNot v.unpair.2) := by
    rw [val_pair, val_comp, val_comp, val_left', val_right']
  have hmid : spaceCost (comp OneDL.cOr (pair (comp OneDL.cNot left) (comp OneDL.cNot right))) v
      ≤ 4 * Nat.size v + 24 := by
    rw [spaceCost_comp, hvinner]
    have := spaceCost_cOr (Nat.pair (val OneDL.cNot v.unpair.1) (val OneDL.cNot v.unpair.2))
    omega
  have hbor : val OneDL.cOr (Nat.pair (val OneDL.cNot v.unpair.1)
      (val OneDL.cNot v.unpair.2)) ≤ 1 := OneDL.val_cOr_le_one _ _
  have hvmid : val (comp OneDL.cOr (pair (comp OneDL.cNot left) (comp OneDL.cNot right))) v
      = val OneDL.cOr (Nat.pair (val OneDL.cNot v.unpair.1) (val OneDL.cNot v.unpair.2)) := by
    rw [val_comp, hvinner]
  rw [OneDL.cAnd, spaceCost_comp, hvmid]
  have hout := spaceCost_cNot (val OneDL.cOr (Nat.pair (val OneDL.cNot v.unpair.1)
    (val OneDL.cNot v.unpair.2)))
  have hs : Nat.size (val OneDL.cOr (Nat.pair (val OneDL.cNot v.unpair.1)
      (val OneDL.cNot v.unpair.2))) ≤ 1 := le_trans (Nat.size_le_size hbor) (by decide)
  omega

theorem spaceCost_cEq (x y : ℕ) :
    spaceCost cEq (Nat.pair x y) ≤ 8 * max (Nat.size x) (Nat.size y) + 64 := by
  have hsw : val OneDL.cSwap (Nat.pair x y) = Nat.pair y x := OneDL.val_cSwap x y
  have hle1 := spaceCost_cLe x y
  have hle2 := spaceCost_cLe y x
  have hsw0 := spaceCost_cSwap (Nat.pair x y)
  have hpv : Nat.size (Nat.pair x y) ≤ 2 * max (Nat.size x) (Nat.size y) := size_pair_le' x y
  have hb1 : val cLe (Nat.pair x y) ≤ 1 := by
    rw [val_cLe]; split <;> decide
  have hb2 : val cLe (Nat.pair y x) ≤ 1 := by
    rw [val_cLe]; split <;> decide
  have hpair : Nat.size (Nat.pair (val cLe (Nat.pair x y)) (val cLe (Nat.pair y x))) ≤ 2 :=
    size_pair_bit hb1 hb2
  have hp : spaceCost (pair cLe (comp cLe OneDL.cSwap)) (Nat.pair x y)
      ≤ 8 * max (Nat.size x) (Nat.size y) + 16 := by
    simp only [spaceCost_pair, spaceCost_comp, val_comp, hsw]
    omega
  have hvp : val (pair cLe (comp cLe OneDL.cSwap)) (Nat.pair x y)
      = Nat.pair (val cLe (Nat.pair x y)) (val cLe (Nat.pair y x)) := by
    rw [val_pair, val_comp, hsw]
  rw [cEq, spaceCost_comp, hvp]
  have hand := spaceCost_cAnd (Nat.pair (val cLe (Nat.pair x y)) (val cLe (Nat.pair y x)))
  omega

/-! ### Selection's own cost

`cIte` multiplies each arm by an indicator and adds. Both products are formed, so both arms' widths
are charged — the arithmetic counterpart of `cSel`'s strictness. The indicators are bits, so each
product is no wider than its arm. -/

theorem val_cCtr' (v : ℕ) : val cCtr v = v.unpair.2.unpair.1 := by
  rw [cCtr, val_comp, val_right', val_left']

theorem val_cAcc' (v : ℕ) : val cAcc v = v.unpair.2.unpair.2 := by
  rw [cAcc, val_comp, val_right', val_right']

private theorem mul_bit_le {a b : ℕ} (ha : a ≤ 1) : a * b ≤ b := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 ha with rfl | rfl <;> simp

attribute [local irreducible] cAdd cMul cSub cPred cPow2 OneDL.cIsPos OneDL.cNot

theorem spaceCost_cIte (v : ℕ) : spaceCost cIte v ≤ 8 * Nat.size v + 32 := by
  have hb : Nat.size v.unpair.1 ≤ Nat.size v := Nat.size_le_size (Nat.unpair_left_le v)
  have hr : Nat.size v.unpair.2 ≤ Nat.size v := Nat.size_le_size (Nat.unpair_right_le v)
  have ht : Nat.size v.unpair.2.unpair.1 ≤ Nat.size v :=
    le_trans (Nat.size_le_size (Nat.unpair_left_le _)) hr
  have hf : Nat.size v.unpair.2.unpair.2 ≤ Nat.size v :=
    le_trans (Nat.size_le_size (Nat.unpair_right_le _)) hr
  have hip : val OneDL.cIsPos v.unpair.1 ≤ 1 := OneDL.val_cIsPos_le_one _
  have hnt : val OneDL.cNot v.unpair.1 ≤ 1 := OneDL.val_cNot_le_one _
  have hsip : Nat.size (val OneDL.cIsPos v.unpair.1) ≤ 1 :=
    le_trans (Nat.size_le_size hip) (by decide)
  have hsnt : Nat.size (val OneDL.cNot v.unpair.1) ≤ 1 :=
    le_trans (Nat.size_le_size hnt) (by decide)
  have hA : spaceCost (comp cMul (pair (comp OneDL.cIsPos left) cCtr)) v
      ≤ 8 * Nat.size v + 24 := by
    simp only [spaceCost_comp, spaceCost_pair, spaceCost_left, spaceCost_cCtr, val_comp,
      val_pair, val_left', val_cCtr']
    have h1 := spaceCost_cIsPos v.unpair.1
    have h2 := spaceCost_cMul (val OneDL.cIsPos v.unpair.1) v.unpair.2.unpair.1
    have hp := size_pair_le' (val OneDL.cIsPos v.unpair.1) v.unpair.2.unpair.1
    omega
  have hB : spaceCost (comp cMul (pair (comp OneDL.cNot left) cAcc)) v
      ≤ 8 * Nat.size v + 24 := by
    simp only [spaceCost_comp, spaceCost_pair, spaceCost_left, spaceCost_cAcc, val_comp,
      val_pair, val_left', val_cAcc']
    have h1 := spaceCost_cNot v.unpair.1
    have h2 := spaceCost_cMul (val OneDL.cNot v.unpair.1) v.unpair.2.unpair.2
    have hp := size_pair_le' (val OneDL.cNot v.unpair.1) v.unpair.2.unpair.2
    omega
  have hprodA : Nat.size (val OneDL.cIsPos v.unpair.1 * v.unpair.2.unpair.1) ≤ Nat.size v :=
    le_trans (Nat.size_le_size (mul_bit_le hip)) ht
  have hprodB : Nat.size (val OneDL.cNot v.unpair.1 * v.unpair.2.unpair.2) ≤ Nat.size v :=
    le_trans (Nat.size_le_size (mul_bit_le hnt)) hf
  have hvA : val (comp cMul (pair (comp OneDL.cIsPos left) cCtr)) v
      = val OneDL.cIsPos v.unpair.1 * v.unpair.2.unpair.1 := by
    rw [val_comp, val_pair, val_comp, val_left', val_cCtr', val_cMul]
  have hvB : val (comp cMul (pair (comp OneDL.cNot left) cAcc)) v
      = val OneDL.cNot v.unpair.1 * v.unpair.2.unpair.2 := by
    rw [val_comp, val_pair, val_comp, val_left', val_cAcc', val_cMul]
  have hred : spaceCost cIte v
      = max (max (max (spaceCost (comp cMul (pair (comp OneDL.cIsPos left) cCtr)) v)
            (spaceCost (comp cMul (pair (comp OneDL.cNot left) cAcc)) v))
          (Nat.size (Nat.pair (val OneDL.cIsPos v.unpair.1 * v.unpair.2.unpair.1)
            (val OneDL.cNot v.unpair.1 * v.unpair.2.unpair.2))))
        (spaceCost cAdd (Nat.pair (val OneDL.cIsPos v.unpair.1 * v.unpair.2.unpair.1)
          (val OneDL.cNot v.unpair.1 * v.unpair.2.unpair.2))) := by
    rw [cIte, spaceCost_comp, spaceCost_pair, val_pair, hvA, hvB]
  rw [hred]
  have hadd := spaceCost_cAdd (val OneDL.cIsPos v.unpair.1 * v.unpair.2.unpair.1)
    (val OneDL.cNot v.unpair.1 * v.unpair.2.unpair.2)
  have hpp := size_pair_le' (val OneDL.cIsPos v.unpair.1 * v.unpair.2.unpair.1)
    (val OneDL.cNot v.unpair.1 * v.unpair.2.unpair.2)
  omega

/-! ## The shape layer

Every code in this development is `comp` and `pair` nested over leaves. Reducing such a term with
`simp only` is what went wrong before: a `pair` of a `pair` has no stable normal form, so an outer
rewrite re-expands the inner one and the composite bounds stop matching.

The fix is to stop rewriting. Each lemma below takes **bounds on the parts and returns a bound on
the whole**, so it is *applied* rather than unfolded — an outer application never touches an inner
one, and a walk down a code is a walk down a proof term of the same shape. This is the recipe that
worked for selection, as infrastructure.

A guard-rail for widths comes with it: state size facts through `size n ≤ n` where a zero case
exists. The `max`-form route (`size (m+1) ≤ max (size m) (size 1) + 1`) is unprovable at zero. -/

/-- Widths never exceed the value. Safe at zero, unlike the `max`-form bounds. -/
theorem size_le_self (n : ℕ) : Nat.size n ≤ n := Nat.size_le.2 Nat.lt_two_pow_self

theorem size_succ_le {m B : ℕ} (h : m ≤ B) : Nat.size (m + 1) ≤ B + 1 :=
  le_trans (size_le_self (m + 1)) (by omega)

/-- Widths of a successor, against a bound on the *value*. Safe at zero, where the `max`-form
route (`Nat.size (m+1) ≤ max (Nat.size m) 1 + 1`) is not available. -/
theorem size_succ_le_size {m n : ℕ} (h : m ≤ n) : Nat.size (m + 1) ≤ Nat.size n + 1 := by
  refine Nat.size_le.2 ?_
  have h1 : n < 2 ^ Nat.size n := Nat.lt_size_self n
  have h2 : (2 : ℕ) ^ Nat.size n < 2 ^ (Nat.size n + 1) :=
    Nat.pow_lt_pow_right (by norm_num) (Nat.lt_succ_self _)
  omega

/-- **Composition, bound form.** -/
theorem spaceCost_comp_bound {f g : Code} {n B : ℕ}
    (hg : spaceCost g n ≤ B) (hf : spaceCost f (val g n) ≤ B) :
    spaceCost (comp f g) n ≤ B := by
  rw [spaceCost_comp]; omega

/-- **Pairing, bound form.** The third hypothesis is the width of the pair actually formed — the
only place a `pair` node can cost more than its parts. -/
theorem spaceCost_pair_bound {f g : Code} {n B : ℕ}
    (hf : spaceCost f n ≤ B) (hg : spaceCost g n ≤ B)
    (hv : Nat.size (Nat.pair (val f n) (val g n)) ≤ B) :
    spaceCost (pair f g) n ≤ B := by
  rw [spaceCost_pair]; omega

theorem spaceCost_left_bound {n B : ℕ} (h : Nat.size n ≤ B) : spaceCost left n ≤ B := by
  rw [spaceCost_left]
  have := Nat.size_le_size (Nat.unpair_left_le n)
  omega

theorem spaceCost_right_bound {n B : ℕ} (h : Nat.size n ≤ B) : spaceCost right n ≤ B := by
  rw [spaceCost_right]
  have := Nat.size_le_size (Nat.unpair_right_le n)
  omega

theorem spaceCost_zero_bound {n B : ℕ} (h : Nat.size n ≤ B) : spaceCost zero n ≤ B := by
  rw [spaceCost_zero]
  have h0 : Nat.size (0 : ℕ) = 0 := by decide
  omega

theorem spaceCost_succ_bound {n B : ℕ} (h1 : Nat.size n ≤ B) (h2 : Nat.size (n + 1) ≤ B) :
    spaceCost succ n ≤ B := by
  rw [spaceCost_succ]; omega

/-! ### The bit-length fold

The first walk carried out entirely on the shape layer: the proof term below has the same tree
shape as `sizeStep` itself, one `bound` application per node, and no rewriting of a composite by
its parts. The hypothesis `m ≤ Nat.size a` is what keeps the exponentiation affordable — `cPow2`
costs linearly in its *argument*, so the fold's counter must stay inside the answer's width. -/

theorem spaceCost_sizeStep (a y m : ℕ) (hm : m ≤ Nat.size a) :
    spaceCost sizeStep (Nat.pair a (Nat.pair y m))
      ≤ 32 * max (Nat.size a) (Nat.size y) + 128 := by
  -- widths: the counter stays inside the answer's, via the `size n ≤ n` route (safe at zero)
  have hsm : Nat.size m ≤ Nat.size a := le_trans (size_le_self m) hm
  have hsm1 : Nat.size (m + 1) ≤ Nat.size a + 1 := size_succ_le hm
  have hI : Nat.size (Nat.pair a (Nat.pair y m)) ≤ 4 * max (Nat.size a) (Nat.size y) := by
    have h1 := size_pair_le' a (Nat.pair y m)
    have h2 := size_pair_le' y m
    omega
  have hSApair : Nat.size (Nat.pair (m + 1) m) ≤ 2 * Nat.size a + 2 := by
    have := size_pair_le' (m + 1) m
    omega
  -- the values the step forms, each named once so no outer step re-expands an inner one
  have hA : val cAcc (Nat.pair a (Nat.pair y m)) = m := val_cAcc a y m
  have hL : val left (Nat.pair a (Nat.pair y m)) = a := by rw [val_left', Nat.unpair_pair]
  have hPow : val (comp cPow2 cAcc) (Nat.pair a (Nat.pair y m)) = 2 ^ m := by
    rw [val_comp, hA, val_cPow2]
  have hInner : val (pair (comp cPow2 cAcc) left) (Nat.pair a (Nat.pair y m))
      = Nat.pair (2 ^ m) a := by rw [val_pair, hPow, hL]
  have hS : val (comp succ cAcc) (Nat.pair a (Nat.pair y m)) = m + 1 := by
    rw [val_comp, hA, val_succ']
  have hSA : val (pair (comp succ cAcc) cAcc) (Nat.pair a (Nat.pair y m))
      = Nat.pair (m + 1) m := by rw [val_pair, hS, hA]
  -- the guard's value is a bit; its width is bounded without computing it
  have hGsize : Nat.size (val (comp cLe (pair (comp cPow2 cAcc) left))
      (Nat.pair a (Nat.pair y m))) ≤ 1 := by
    rw [val_comp, hInner, val_cLe]
    split <;> simp
  have hW : Nat.size (Nat.pair (val (comp cLe (pair (comp cPow2 cAcc) left))
      (Nat.pair a (Nat.pair y m))) (Nat.pair (m + 1) m)) ≤ 4 * Nat.size a + 4 := by
    have := size_pair_le' (val (comp cLe (pair (comp cPow2 cAcc) left))
      (Nat.pair a (Nat.pair y m))) (Nat.pair (m + 1) m)
    omega
  rw [sizeStep]
  refine spaceCost_comp_bound (spaceCost_pair_bound ?_ ?_ ?_) ?_
  · -- the guard `2 ^ acc ≤ a`
    refine spaceCost_comp_bound (spaceCost_pair_bound ?_ ?_ ?_) ?_
    · refine spaceCost_comp_bound ?_ ?_
      · rw [spaceCost_cAcc]; omega
      · rw [hA]
        have := spaceCost_cPow2 m
        omega
    · exact spaceCost_left_bound (by omega)
    · rw [hPow, hL]
      have h := size_pair_le' (2 ^ m) a
      rw [size_two_pow] at h
      omega
    · rw [hInner]
      have h := spaceCost_cLe (2 ^ m) a
      rw [size_two_pow] at h
      omega
  · -- the two arms, both charged: selection is strict
    refine spaceCost_pair_bound ?_ ?_ ?_
    · refine spaceCost_comp_bound ?_ ?_
      · rw [spaceCost_cAcc]; omega
      · rw [hA]; exact spaceCost_succ_bound (by omega) (by omega)
    · rw [spaceCost_cAcc]; omega
    · rw [hS, hA]; omega
  · rw [hSA]; omega
  · rw [val_pair, hSA]
    have := spaceCost_cIte (Nat.pair (val (comp cLe (pair (comp cPow2 cAcc) left))
      (Nat.pair a (Nat.pair y m))) (Nat.pair (m + 1) m))
    omega

/-- The fold itself. The generic `prec` bound does not apply here: it offers only a *width* bound
on the accumulator, while exponentiation is priced by its argument's *value*. The induction below
supplies the missing fact — the accumulator is `min (Nat.size n) j`, so it never leaves the
answer's width. -/
theorem spaceCost_sizeCore (n : ℕ) : ∀ m,
    spaceCost sizeCore (Nat.pair n m) ≤ 32 * max (Nat.size n) (Nat.size m) + 128 := by
  have hz : spaceCost sizeCore (Nat.pair n 0) = spaceCost zero n :=
    spaceCost_prec_zero zero sizeStep n
  have hs : ∀ j, spaceCost sizeCore (Nat.pair n (j + 1))
      = max (spaceCost sizeCore (Nat.pair n j))
          (spaceCost sizeStep (Nat.pair n (Nat.pair j (val sizeCore (Nat.pair n j))))) :=
    fun j => spaceCost_prec_succ zero sizeStep n j
  intro m
  induction m with
  | zero =>
      rw [hz, spaceCost_zero]
      have h0 : Nat.size (0 : ℕ) = 0 := by decide
      omega
  | succ j ih =>
      rw [hs j, val_sizeCore]
      have hstep := spaceCost_sizeStep n j (min (Nat.size n) j) (min_le_left _ _)
      have hmono : Nat.size j ≤ Nat.size (j + 1) := Nat.size_le_size (Nat.le_succ j)
      omega

/-- **Bit-length runs in workspace linear in its own argument's width.** -/
theorem spaceCost_cSize (v : ℕ) : spaceCost cSize v ≤ 32 * Nat.size v + 128 := by
  have hv : val (pair cId cId) v = Nat.pair v v := by rw [val_pair, val_cId]
  rw [cSize]
  refine spaceCost_comp_bound (spaceCost_pair_bound ?_ ?_ ?_) ?_
  · rw [spaceCost_cId]; omega
  · rw [spaceCost_cId]; omega
  · rw [val_cId]
    have := size_pair_le' v v
    omega
  · rw [hv]
    have := spaceCost_sizeCore v v
    omega

/-! ### The division fold

Same walk, one level deeper: the guard is a conjunction of two tests, one of which multiplies. The
accumulator hypothesis `m ≤ n` is what bounds the product's width — the quotient never exceeds the
dividend, so the trial multiple stays inside the input's width plus one. -/

theorem spaceCost_divStep (n d y m : ℕ) (hm : m ≤ n) :
    spaceCost divStep (Nat.pair (Nat.pair n d) (Nat.pair y m))
      ≤ 32 * max (max (Nat.size n) (Nat.size d)) (Nat.size y) + 128 := by
  have hsm : Nat.size m ≤ Nat.size n := Nat.size_le_size hm
  have hsm1 : Nat.size (m + 1) ≤ Nat.size n + 1 := size_succ_le_size hm
  have hArg : Nat.size (Nat.pair n d) ≤ 2 * max (Nat.size n) (Nat.size d) := size_pair_le' n d
  have hI : Nat.size (Nat.pair (Nat.pair n d) (Nat.pair y m))
      ≤ 4 * max (max (Nat.size n) (Nat.size d)) (Nat.size y) := by
    have h1 := size_pair_le' (Nat.pair n d) (Nat.pair y m)
    have h2 := size_pair_le' y m
    omega
  -- the values, each named once
  have hN : val cArgN (Nat.pair (Nat.pair n d) (Nat.pair y m)) = n := val_cArgN n d y m
  have hD : val cArgD (Nat.pair (Nat.pair n d) (Nat.pair y m)) = d := val_cArgD n d y m
  have hA : val cAcc (Nat.pair (Nat.pair n d) (Nat.pair y m)) = m := val_cAcc (Nat.pair n d) y m
  have hL : val left (Nat.pair (Nat.pair n d) (Nat.pair y m)) = Nat.pair n d := by
    rw [val_left', Nat.unpair_pair]
  have hSucc : val (comp succ cAcc) (Nat.pair (Nat.pair n d) (Nat.pair y m)) = m + 1 := by
    rw [val_comp, hA, val_succ']
  have hRpair : val (pair (comp succ cAcc) cArgD) (Nat.pair (Nat.pair n d) (Nat.pair y m))
      = Nat.pair (m + 1) d := by rw [val_pair, hSucc, hD]
  have hR : val (comp cMul (pair (comp succ cAcc) cArgD))
      (Nat.pair (Nat.pair n d) (Nat.pair y m)) = (m + 1) * d := by
    rw [val_comp, hRpair, val_cMul]
  have hProd : Nat.size ((m + 1) * d) ≤ Nat.size n + 1 + Nat.size d :=
    le_trans (size_mul_le (m + 1) d) (by omega)
  have hARMS : val (pair (comp succ cAcc) cAcc) (Nat.pair (Nat.pair n d) (Nat.pair y m))
      = Nat.pair (m + 1) m := by rw [val_pair, hSucc, hA]
  have hARMSsize : Nat.size (Nat.pair (m + 1) m) ≤ 2 * Nat.size n + 2 := by
    have := size_pair_le' (m + 1) m
    omega
  -- the two tests and the conjunction are bits; their widths are bounded without computing them
  have hPle : val (comp OneDL.cIsPos cArgD) (Nat.pair (Nat.pair n d) (Nat.pair y m)) ≤ 1 := by
    rw [val_comp]; exact OneDL.val_cIsPos_le_one _
  have hQle : val (comp cLe (pair (comp cMul (pair (comp succ cAcc) cArgD)) cArgN))
      (Nat.pair (Nat.pair n d) (Nat.pair y m)) ≤ 1 := by
    rw [val_comp, val_pair, hR, hN, val_cLe]
    split <;> simp
  have hGle : val (comp OneDL.cAnd (pair (comp OneDL.cIsPos cArgD)
      (comp cLe (pair (comp cMul (pair (comp succ cAcc) cArgD)) cArgN))))
      (Nat.pair (Nat.pair n d) (Nat.pair y m)) ≤ 1 := by
    rw [val_comp, val_pair]; exact OneDL.val_cAnd_le_one _ _
  have hGsz := size_le_self (val (comp OneDL.cAnd (pair (comp OneDL.cIsPos cArgD)
      (comp cLe (pair (comp cMul (pair (comp succ cAcc) cArgD)) cArgN))))
      (Nat.pair (Nat.pair n d) (Nat.pair y m)))
  rw [divStep]
  refine spaceCost_comp_bound (spaceCost_pair_bound ?_ ?_ ?_) ?_
  · -- the guard: positivity of the divisor, and the trial multiple still fitting
    refine spaceCost_comp_bound (spaceCost_pair_bound ?_ ?_ ?_) ?_
    · refine spaceCost_comp_bound ?_ ?_
      · refine spaceCost_comp_bound (spaceCost_left_bound (by omega)) ?_
        rw [hL]; exact spaceCost_right_bound (by omega)
      · rw [hD]
        have := spaceCost_cIsPos d
        omega
    · -- the trial multiple still fitting under the dividend
      refine spaceCost_comp_bound (spaceCost_pair_bound ?_ ?_ ?_) ?_
      · refine spaceCost_comp_bound (spaceCost_pair_bound ?_ ?_ ?_) ?_
        · refine spaceCost_comp_bound ?_ ?_
          · rw [spaceCost_cAcc]; omega
          · rw [hA]; exact spaceCost_succ_bound (by omega) (by omega)
        · refine spaceCost_comp_bound (spaceCost_left_bound (by omega)) ?_
          rw [hL]; exact spaceCost_right_bound (by omega)
        · rw [hSucc, hD]
          have := size_pair_le' (m + 1) d
          omega
        · rw [hRpair]
          have := spaceCost_cMul (m + 1) d
          omega
      · refine spaceCost_comp_bound (spaceCost_left_bound (by omega)) ?_
        rw [hL]; exact spaceCost_left_bound (by omega)
      · rw [hR, hN]
        have := size_pair_le' ((m + 1) * d) n
        omega
      · rw [val_pair, hR, hN]
        have := spaceCost_cLe ((m + 1) * d) n
        omega
    · have h1 := size_le_self _ |>.trans hPle
      have h2 := size_le_self _ |>.trans hQle
      have h3 := size_pair_le' (val (comp OneDL.cIsPos cArgD)
        (Nat.pair (Nat.pair n d) (Nat.pair y m)))
        (val (comp cLe (pair (comp cMul (pair (comp succ cAcc) cArgD)) cArgN))
        (Nat.pair (Nat.pair n d) (Nat.pair y m)))
      omega
    · rw [val_pair]
      have h1 := size_le_self _ |>.trans hPle
      have h2 := size_le_self _ |>.trans hQle
      have h3 := size_pair_le' (val (comp OneDL.cIsPos cArgD)
        (Nat.pair (Nat.pair n d) (Nat.pair y m)))
        (val (comp cLe (pair (comp cMul (pair (comp succ cAcc) cArgD)) cArgN))
        (Nat.pair (Nat.pair n d) (Nat.pair y m)))
      have h4 := spaceCost_cAnd (Nat.pair (val (comp OneDL.cIsPos cArgD)
        (Nat.pair (Nat.pair n d) (Nat.pair y m)))
        (val (comp cLe (pair (comp cMul (pair (comp succ cAcc) cArgD)) cArgN))
        (Nat.pair (Nat.pair n d) (Nat.pair y m))))
      omega
  · -- the two arms, both charged
    refine spaceCost_pair_bound ?_ ?_ ?_
    · refine spaceCost_comp_bound ?_ ?_
      · rw [spaceCost_cAcc]; omega
      · rw [hA]; exact spaceCost_succ_bound (by omega) (by omega)
    · rw [spaceCost_cAcc]; omega
    · rw [hSucc, hA]; omega
  · rw [hARMS]
    have := size_pair_le' (val (comp OneDL.cAnd (pair (comp OneDL.cIsPos cArgD)
      (comp cLe (pair (comp cMul (pair (comp succ cAcc) cArgD)) cArgN))))
      (Nat.pair (Nat.pair n d) (Nat.pair y m))) (Nat.pair (m + 1) m)
    omega
  · rw [val_pair, hARMS]
    have h1 := size_pair_le' (val (comp OneDL.cAnd (pair (comp OneDL.cIsPos cArgD)
      (comp cLe (pair (comp cMul (pair (comp succ cAcc) cArgD)) cArgN))))
      (Nat.pair (Nat.pair n d) (Nat.pair y m))) (Nat.pair (m + 1) m)
    have h2 := spaceCost_cIte (Nat.pair (val (comp OneDL.cAnd (pair (comp OneDL.cIsPos cArgD)
      (comp cLe (pair (comp cMul (pair (comp succ cAcc) cArgD)) cArgN))))
      (Nat.pair (Nat.pair n d) (Nat.pair y m))) (Nat.pair (m + 1) m))
    omega

/-- The division fold. As with the bit-length fold, the accumulator's *value* is what has to be
tracked — it is `min (n / d) j`, hence never above the dividend. -/
theorem spaceCost_divCore (n d : ℕ) : ∀ m,
    spaceCost divCore (Nat.pair (Nat.pair n d) m)
      ≤ 32 * max (max (Nat.size n) (Nat.size d)) (Nat.size m) + 128 := by
  have hz : spaceCost divCore (Nat.pair (Nat.pair n d) 0) = spaceCost zero (Nat.pair n d) :=
    spaceCost_prec_zero zero divStep (Nat.pair n d)
  have hs : ∀ j, spaceCost divCore (Nat.pair (Nat.pair n d) (j + 1))
      = max (spaceCost divCore (Nat.pair (Nat.pair n d) j))
          (spaceCost divStep (Nat.pair (Nat.pair n d)
            (Nat.pair j (val divCore (Nat.pair (Nat.pair n d) j))))) :=
    fun j => spaceCost_prec_succ zero divStep (Nat.pair n d) j
  have hArg : Nat.size (Nat.pair n d) ≤ 2 * max (Nat.size n) (Nat.size d) := size_pair_le' n d
  intro m
  induction m with
  | zero =>
      rw [hz, spaceCost_zero]
      have h0 : Nat.size (0 : ℕ) = 0 := by decide
      omega
  | succ j ih =>
      rw [hs j, val_divCore]
      have hacc : min (n / d) j ≤ n := le_trans (min_le_left _ _) (Nat.div_le_self n d)
      have hstep := spaceCost_divStep n d j (min (n / d) j) hacc
      have hmono : Nat.size j ≤ Nat.size (j + 1) := Nat.size_le_size (Nat.le_succ j)
      omega

/-- **Division runs in workspace linear in its arguments' widths.** -/
theorem spaceCost_cDiv (n d : ℕ) :
    spaceCost cDiv (Nat.pair n d) ≤ 32 * max (Nat.size n) (Nat.size d) + 128 := by
  have hArg : Nat.size (Nat.pair n d) ≤ 2 * max (Nat.size n) (Nat.size d) := size_pair_le' n d
  have hL : val left (Nat.pair n d) = n := by rw [val_left', Nat.unpair_pair]
  have hv : val (pair cId left) (Nat.pair n d) = Nat.pair (Nat.pair n d) n := by
    rw [val_pair, val_cId, hL]
  rw [cDiv]
  refine spaceCost_comp_bound (spaceCost_pair_bound ?_ ?_ ?_) ?_
  · rw [spaceCost_cId]; omega
  · exact spaceCost_left_bound (by omega)
  · rw [val_cId, hL]
    have := size_pair_le' (Nat.pair n d) n
    omega
  · rw [hv]
    have := spaceCost_divCore n d n
    omega

/-- **Remainder runs in workspace linear in its arguments' widths.** -/
theorem spaceCost_cMod (n d : ℕ) :
    spaceCost cMod (Nat.pair n d) ≤ 32 * max (Nat.size n) (Nat.size d) + 128 := by
  have hArg : Nat.size (Nat.pair n d) ≤ 2 * max (Nat.size n) (Nat.size d) := size_pair_le' n d
  have hL : val left (Nat.pair n d) = n := by rw [val_left', Nat.unpair_pair]
  have hR : val right (Nat.pair n d) = d := by rw [val_right', Nat.unpair_pair]
  have hQ : Nat.size (n / d) ≤ Nat.size n := Nat.size_le_size (Nat.div_le_self n d)
  have hMulPair : val (pair right cDiv) (Nat.pair n d) = Nat.pair d (n / d) := by
    rw [val_pair, hR, val_cDiv]
  have hMul : val (comp cMul (pair right cDiv)) (Nat.pair n d) = d * (n / d) := by
    rw [val_comp, hMulPair, val_cMul]
  have hProd : Nat.size (d * (n / d)) ≤ Nat.size d + Nat.size n :=
    le_trans (size_mul_le d (n / d)) (by omega)
  rw [cMod]
  refine spaceCost_comp_bound (spaceCost_pair_bound ?_ ?_ ?_) ?_
  · exact spaceCost_left_bound (by omega)
  · refine spaceCost_comp_bound (spaceCost_pair_bound ?_ ?_ ?_) ?_
    · exact spaceCost_right_bound (by omega)
    · have := spaceCost_cDiv n d
      omega
    · rw [hR, val_cDiv]
      have := size_pair_le' d (n / d)
      omega
    · rw [hMulPair]
      have := spaceCost_cMul d (n / d)
      omega
  · rw [hL, hMul]
    have := size_pair_le' n (d * (n / d))
    omega
  · rw [val_pair, hL, hMul]
    have := spaceCost_cSub n (d * (n / d))
    omega

/-! ### The stack cell's workspace

The cell constructor is where the interpreter's absolute constant is actually set: it is the widest
composition the step runs, and every one of its parts is charged. The three shift codes each carry
a bit-length call, so bit-length's own bound is what dominates — which is why the constant below is
the same `32` that bit-length pays, rather than a product of the nesting depth. -/

theorem size_two_mul_succ_le (S : ℕ) : Nat.size (2 * S + 1) ≤ Nat.size S + 1 := by
  refine Nat.size_le.2 ?_
  have h := Nat.lt_size_self S
  have hp : (2 : ℕ) ^ (Nat.size S + 1) = 2 * 2 ^ Nat.size S := by rw [pow_succ]; ring
  omega

@[simp] theorem val_cFrameBits_left (f k : ℕ) :
    val (comp cFrameBits left) (Nat.pair f k) = Nat.size f := by
  rw [val_comp, val_left', Nat.unpair_pair, val_cFrameBits]
  rfl

theorem spaceCost_cFrameBits_left (f k : ℕ) :
    spaceCost (comp cFrameBits left) (Nat.pair f k)
      ≤ 32 * max (Nat.size f) (Nat.size k) + 128 := by
  have hI : Nat.size (Nat.pair f k) ≤ 2 * max (Nat.size f) (Nat.size k) := size_pair_le' f k
  refine spaceCost_comp_bound (spaceCost_left_bound (by omega)) ?_
  rw [val_left', Nat.unpair_pair, cFrameBits]
  change spaceCost cSize f ≤ _
  have := spaceCost_cSize f
  omega

@[simp] theorem val_cP0 (f k : ℕ) : val cP0 (Nat.pair f k) = 2 ^ Nat.size f := by
  rw [cP0, val_comp, val_cFrameBits_left, val_cPow2]

@[simp] theorem val_cP1 (f k : ℕ) : val cP1 (Nat.pair f k) = 2 ^ (Nat.size f + 1) := by
  rw [cP1, val_comp, val_comp, val_cFrameBits_left, val_succ', val_cPow2]

@[simp] theorem val_cP2 (f k : ℕ) : val cP2 (Nat.pair f k) = 2 ^ (2 * Nat.size f + 1) := by
  rw [cP2, val_comp, val_comp, val_comp, val_cFrameBits_left, val_cDbl, val_succ', val_cPow2]

theorem spaceCost_cP0 (f k : ℕ) :
    spaceCost cP0 (Nat.pair f k) ≤ 32 * max (Nat.size f) (Nat.size k) + 128 := by
  rw [cP0]
  refine spaceCost_comp_bound (spaceCost_cFrameBits_left f k) ?_
  rw [val_cFrameBits_left]
  have := spaceCost_cPow2 (Nat.size f)
  have hM : Nat.size f ≤ max (Nat.size f) (Nat.size k) := le_max_left _ _
  omega

theorem spaceCost_cP1 (f k : ℕ) :
    spaceCost cP1 (Nat.pair f k) ≤ 32 * max (Nat.size f) (Nat.size k) + 128 := by
  have hM : Nat.size f ≤ max (Nat.size f) (Nat.size k) := le_max_left _ _
  have hsf : Nat.size (Nat.size f) ≤ Nat.size f := size_le_self _
  have hsf1 : Nat.size (Nat.size f + 1) ≤ Nat.size (Nat.size f) + 1 :=
    size_succ_le_size (le_refl _)
  rw [cP1]
  refine spaceCost_comp_bound ?_ ?_
  · refine spaceCost_comp_bound (spaceCost_cFrameBits_left f k) ?_
    rw [val_cFrameBits_left]
    exact spaceCost_succ_bound (by omega) (by omega)
  · rw [val_comp, val_cFrameBits_left, val_succ']
    have := spaceCost_cPow2 (Nat.size f + 1)
    omega

theorem spaceCost_cP2 (f k : ℕ) :
    spaceCost cP2 (Nat.pair f k) ≤ 32 * max (Nat.size f) (Nat.size k) + 128 := by
  have hM : Nat.size f ≤ max (Nat.size f) (Nat.size k) := le_max_left _ _
  have hsf : Nat.size (Nat.size f) ≤ Nat.size f := size_le_self _
  have hd1 : Nat.size (2 * Nat.size f + 1) ≤ Nat.size (Nat.size f) + 1 :=
    size_two_mul_succ_le _
  have hd0 : Nat.size (2 * Nat.size f) ≤ Nat.size (2 * Nat.size f + 1) :=
    Nat.size_le_size (Nat.le_succ _)
  rw [cP2]
  refine spaceCost_comp_bound ?_ ?_
  · refine spaceCost_comp_bound ?_ ?_
    · refine spaceCost_comp_bound (spaceCost_cFrameBits_left f k) ?_
      rw [val_cFrameBits_left]
      have := spaceCost_cDbl (Nat.size f)
      omega
    · rw [val_comp, val_cFrameBits_left, val_cDbl]
      exact spaceCost_succ_bound (by omega) (by omega)
  · rw [val_comp, val_comp, val_cFrameBits_left, val_cDbl, val_succ']
    have := spaceCost_cPow2 (2 * Nat.size f + 1)
    omega

/-- **Building a stack cell runs in workspace linear in the frame's and tail's widths.** -/
theorem spaceCost_cStkCons (f k : ℕ) :
    spaceCost cStkCons (Nat.pair f k) ≤ 32 * max (Nat.size f) (Nat.size k) + 128 := by
  have hM1 : Nat.size f ≤ max (Nat.size f) (Nat.size k) := le_max_left _ _
  have hM2 : Nat.size k ≤ max (Nat.size f) (Nat.size k) := le_max_right _ _
  have hI : Nat.size (Nat.pair f k) ≤ 2 * max (Nat.size f) (Nat.size k) := size_pair_le' f k
  have hL : val left (Nat.pair f k) = f := by rw [val_left', Nat.unpair_pair]
  have hR : val right (Nat.pair f k) = k := by rw [val_right', Nat.unpair_pair]
  -- the widths of the three shifted numerals
  have hz1 : Nat.size (2 ^ Nat.size f) = Nat.size f + 1 := size_two_pow _
  have hz2 : Nat.size (2 ^ (Nat.size f + 1)) = Nat.size f + 2 := size_two_pow _
  have hz3 : Nat.size (2 ^ (2 * Nat.size f + 1)) = 2 * Nat.size f + 2 := size_two_pow _
  have hz0 : Nat.size (2 ^ Nat.size f - 1) ≤ Nat.size f := by
    refine Nat.size_le.2 ?_
    have : 0 < (2 : ℕ) ^ Nat.size f := by positivity
    omega
  have hb1 : Nat.size (f * 2 ^ (Nat.size f + 1)) ≤ Nat.size f + (Nat.size f + 2) :=
    le_trans (size_mul_le f _) (by omega)
  have hb2 : Nat.size (k * 2 ^ (2 * Nat.size f + 1)) ≤ Nat.size k + (2 * Nat.size f + 2) :=
    le_trans (size_mul_le k _) (by omega)
  have ha2 : Nat.size (2 ^ Nat.size f - 1 + f * 2 ^ (Nat.size f + 1))
      ≤ max (Nat.size (2 ^ Nat.size f - 1)) (Nat.size (f * 2 ^ (Nat.size f + 1))) + 1 :=
    size_add_le _ _
  have hsum : Nat.size (2 ^ Nat.size f - 1 + f * 2 ^ (Nat.size f + 1)
        + k * 2 ^ (2 * Nat.size f + 1))
      ≤ max (Nat.size (2 ^ Nat.size f - 1 + f * 2 ^ (Nat.size f + 1)))
          (Nat.size (k * 2 ^ (2 * Nat.size f + 1))) + 1 := size_add_le _ _
  -- the values the cell's tree forms, named bottom-up
  have hvA1 : val (comp cSub (pair cP0 (constCode 1))) (Nat.pair f k)
      = 2 ^ Nat.size f - 1 := by rw [val_comp, val_pair, val_cP0, val_constCode, val_cSub]
  have hvB1 : val (comp cMul (pair left cP1)) (Nat.pair f k)
      = f * 2 ^ (Nat.size f + 1) := by rw [val_comp, val_pair, hL, val_cP1, val_cMul]
  have hvB2 : val (comp cMul (pair right cP2)) (Nat.pair f k)
      = k * 2 ^ (2 * Nat.size f + 1) := by rw [val_comp, val_pair, hR, val_cP2, val_cMul]
  have hvA2 : val (comp cAdd (pair (comp cSub (pair cP0 (constCode 1)))
        (comp cMul (pair left cP1)))) (Nat.pair f k)
      = 2 ^ Nat.size f - 1 + f * 2 ^ (Nat.size f + 1) := by
    rw [val_comp, val_pair, hvA1, hvB1, val_cAdd]
  have hvSum : val (comp cAdd (pair (comp cAdd (pair (comp cSub (pair cP0 (constCode 1)))
        (comp cMul (pair left cP1)))) (comp cMul (pair right cP2)))) (Nat.pair f k)
      = 2 ^ Nat.size f - 1 + f * 2 ^ (Nat.size f + 1)
        + k * 2 ^ (2 * Nat.size f + 1) := by
    rw [val_comp, val_pair, hvA2, hvB2, val_cAdd]
  have hdbl := size_two_mul_succ_le (2 ^ Nat.size f - 1 + f * 2 ^ (Nat.size f + 1)
    + k * 2 ^ (2 * Nat.size f + 1))
  have hdbl0 : Nat.size (2 * (2 ^ Nat.size f - 1 + f * 2 ^ (Nat.size f + 1)
      + k * 2 ^ (2 * Nat.size f + 1)))
      ≤ Nat.size (2 * (2 ^ Nat.size f - 1 + f * 2 ^ (Nat.size f + 1)
        + k * 2 ^ (2 * Nat.size f + 1)) + 1) := Nat.size_le_size (Nat.le_succ _)
  rw [cStkCons]
  refine spaceCost_comp_bound (spaceCost_comp_bound
    (spaceCost_comp_bound (spaceCost_pair_bound ?_ ?_ ?_) ?_) ?_) ?_
  · -- the header-and-frame half
    refine spaceCost_comp_bound (spaceCost_pair_bound ?_ ?_ ?_) ?_
    · -- the unary header `2 ^ L - 1`
      refine spaceCost_comp_bound (spaceCost_pair_bound ?_ ?_ ?_) ?_
      · exact spaceCost_cP0 f k
      · have := spaceCost_constCode 1 (Nat.pair f k)
        have h1 : Nat.size (1 : ℕ) = 1 := by decide
        omega
      · rw [val_cP0, val_constCode]
        have := size_pair_le' (2 ^ Nat.size f) 1
        have h1 : Nat.size (1 : ℕ) = 1 := by decide
        omega
      · rw [val_pair, val_cP0, val_constCode]
        have := spaceCost_cSub (2 ^ Nat.size f) 1
        have h1 : Nat.size (1 : ℕ) = 1 := by decide
        omega
    · -- the frame, shifted above the header
      refine spaceCost_comp_bound (spaceCost_pair_bound ?_ ?_ ?_) ?_
      · exact spaceCost_left_bound (by omega)
      · exact spaceCost_cP1 f k
      · rw [hL, val_cP1]
        have := size_pair_le' f (2 ^ (Nat.size f + 1))
        omega
      · rw [val_pair, hL, val_cP1]
        have := spaceCost_cMul f (2 ^ (Nat.size f + 1))
        omega
    · rw [hvA1, hvB1]
      have := size_pair_le' (2 ^ Nat.size f - 1) (f * 2 ^ (Nat.size f + 1))
      omega
    · rw [val_pair, hvA1, hvB1]
      have := spaceCost_cAdd (2 ^ Nat.size f - 1) (f * 2 ^ (Nat.size f + 1))
      omega
  · -- the tail, shifted above both
    refine spaceCost_comp_bound (spaceCost_pair_bound ?_ ?_ ?_) ?_
    · exact spaceCost_right_bound (by omega)
    · exact spaceCost_cP2 f k
    · rw [hR, val_cP2]
      have := size_pair_le' k (2 ^ (2 * Nat.size f + 1))
      omega
    · rw [val_pair, hR, val_cP2]
      have := spaceCost_cMul k (2 ^ (2 * Nat.size f + 1))
      omega
  · rw [hvA2, hvB2]
    have := size_pair_le' (2 ^ Nat.size f - 1 + f * 2 ^ (Nat.size f + 1))
      (k * 2 ^ (2 * Nat.size f + 1))
    omega
  · rw [val_pair, hvA2, hvB2]
    have := spaceCost_cAdd (2 ^ Nat.size f - 1 + f * 2 ^ (Nat.size f + 1))
      (k * 2 ^ (2 * Nat.size f + 1))
    omega
  · rw [hvSum]
    have := spaceCost_cDbl (2 ^ Nat.size f - 1 + f * 2 ^ (Nat.size f + 1)
      + k * 2 ^ (2 * Nat.size f + 1))
    omega
  · rw [val_comp, hvSum, val_cDbl]
    exact spaceCost_succ_bound (by omega) (by omega)

/-- Stripping the flag bit. -/
theorem spaceCost_cStkBody (s : ℕ) : spaceCost cStkBody s ≤ 32 * Nat.size s + 192 := by
  have h2 : Nat.size (2 : ℕ) = 2 := by decide
  have hp : Nat.size (Nat.pair s 2) ≤ 2 * max (Nat.size s) (Nat.size 2) := size_pair_le' s 2
  rw [cStkBody]
  refine spaceCost_comp_bound (spaceCost_pair_bound ?_ ?_ ?_) ?_
  · rw [spaceCost_cId]; omega
  · have := spaceCost_constCode 2 s
    omega
  · rw [val_cId, val_constCode]; omega
  · rw [val_pair, val_cId, val_constCode]
    have := spaceCost_cDiv s 2
    omega

/-- **The header is no longer than the numeral carrying it.** The header fold's accumulator is
priced by its *value* — it drives an exponentiation — so the walk needs this in place of the
cruder bound by the numeral itself. -/
theorem trailOnes_le_size (n : ℕ) : BoundedInterp.trailOnes n ≤ Nat.size n := by
  rcases Nat.eq_zero_or_pos (BoundedInterp.trailOnes n) with h | h
  · omega
  · have hb := (BoundedInterp.trailOnes_lt_iff n (BoundedInterp.trailOnes n - 1)).1 (by omega)
    have hmod : n % 2 ^ (BoundedInterp.trailOnes n - 1 + 1) ≤ n := Nat.mod_le _ _
    have hstep : (2 : ℕ) ^ (BoundedInterp.trailOnes n - 1 + 1)
        = 2 * 2 ^ (BoundedInterp.trailOnes n - 1) := by rw [pow_succ]; ring
    have hpos : 0 < (2 : ℕ) ^ (BoundedInterp.trailOnes n - 1) := by positivity
    have hle : (2 : ℕ) ^ (BoundedInterp.trailOnes n - 1) ≤ n := by omega
    have hsz := Nat.size_le_size hle
    rw [size_two_pow] at hsz
    omega

theorem spaceCost_trailStep (a y m : ℕ) (hm : m ≤ Nat.size a) :
    spaceCost trailStep (Nat.pair a (Nat.pair y m))
      ≤ 32 * max (Nat.size a) (Nat.size y) + 256 := by
  have hsm : Nat.size m ≤ Nat.size a := le_trans (Nat.size_le_size hm) (size_le_self _)
  have hsm1 : Nat.size (m + 1) ≤ Nat.size a + 1 :=
    le_trans (size_succ_le_size hm) (by have := size_le_self (Nat.size a); omega)
  have hI : Nat.size (Nat.pair a (Nat.pair y m))
      ≤ 4 * max (Nat.size a) (Nat.size y) := by
    have h1 := size_pair_le' a (Nat.pair y m)
    have h2 := size_pair_le' y m
    omega
  have hpow : Nat.size (2 ^ (m + 1)) = m + 2 := size_two_pow (m + 1)
  have hmodsz : Nat.size (a % 2 ^ (m + 1)) ≤ Nat.size a := Nat.size_le_size (Nat.mod_le _ _)
  have hsubsz : Nat.size (2 ^ (m + 1) - 1) ≤ m + 1 := by
    refine Nat.size_le.2 ?_
    have : 0 < (2 : ℕ) ^ (m + 1) := by positivity
    omega
  have h1sz : Nat.size (1 : ℕ) = 1 := by decide
  -- the values, bottom-up
  have hA : val cAcc (Nat.pair a (Nat.pair y m)) = m := val_cAcc a y m
  have hL : val left (Nat.pair a (Nat.pair y m)) = a := by rw [val_left', Nat.unpair_pair]
  have hSucc : val (comp succ cAcc) (Nat.pair a (Nat.pair y m)) = m + 1 := by
    rw [val_comp, hA, val_succ']
  have hHdr : val cHdrPow (Nat.pair a (Nat.pair y m)) = 2 ^ (m + 1) := by
    rw [cHdrPow, val_comp, hSucc, val_cPow2]
  have hMod : val (comp cMod (pair left cHdrPow)) (Nat.pair a (Nat.pair y m))
      = a % 2 ^ (m + 1) := by rw [val_comp, val_pair, hL, hHdr, val_cMod]
  have hSub : val (comp cSub (pair cHdrPow (constCode 1))) (Nat.pair a (Nat.pair y m))
      = 2 ^ (m + 1) - 1 := by rw [val_comp, val_pair, hHdr, val_constCode, val_cSub]
  have hARMS : val (pair (comp succ cAcc) cAcc) (Nat.pair a (Nat.pair y m))
      = Nat.pair (m + 1) m := by rw [val_pair, hSucc, hA]
  have hGle : val (comp cEq (pair (comp cMod (pair left cHdrPow))
      (comp cSub (pair cHdrPow (constCode 1))))) (Nat.pair a (Nat.pair y m)) ≤ 1 := by
    rw [val_comp, val_pair, hMod, hSub, val_cEq]
    split <;> simp
  have hGsz := size_le_self (val (comp cEq (pair (comp cMod (pair left cHdrPow))
    (comp cSub (pair cHdrPow (constCode 1))))) (Nat.pair a (Nat.pair y m)))
  -- the exponentiation, charged by the accumulator's value
  have hHdrCost : spaceCost cHdrPow (Nat.pair a (Nat.pair y m))
      ≤ 32 * max (Nat.size a) (Nat.size y) + 256 := by
    rw [cHdrPow]
    refine spaceCost_comp_bound ?_ ?_
    · refine spaceCost_comp_bound ?_ ?_
      · rw [spaceCost_cAcc]; omega
      · rw [hA]; exact spaceCost_succ_bound (by omega) (by omega)
    · rw [hSucc]
      have := spaceCost_cPow2 (m + 1)
      omega
  rw [trailStep]
  refine spaceCost_comp_bound (spaceCost_pair_bound ?_ ?_ ?_) ?_
  · -- the guard: are the bottom `acc + 1` bits all ones?
    refine spaceCost_comp_bound (spaceCost_pair_bound ?_ ?_ ?_) ?_
    · refine spaceCost_comp_bound (spaceCost_pair_bound ?_ ?_ ?_) ?_
      · exact spaceCost_left_bound (by omega)
      · exact hHdrCost
      · rw [hL, hHdr]
        have := size_pair_le' a (2 ^ (m + 1))
        omega
      · rw [val_pair, hL, hHdr]
        have := spaceCost_cMod a (2 ^ (m + 1))
        omega
    · refine spaceCost_comp_bound (spaceCost_pair_bound ?_ ?_ ?_) ?_
      · exact hHdrCost
      · have := spaceCost_constCode 1 (Nat.pair a (Nat.pair y m))
        omega
      · rw [hHdr, val_constCode]
        have := size_pair_le' (2 ^ (m + 1)) 1
        omega
      · rw [val_pair, hHdr, val_constCode]
        have := spaceCost_cSub (2 ^ (m + 1)) 1
        omega
    · rw [hMod, hSub]
      have := size_pair_le' (a % 2 ^ (m + 1)) (2 ^ (m + 1) - 1)
      omega
    · rw [val_pair, hMod, hSub]
      have := spaceCost_cEq (a % 2 ^ (m + 1)) (2 ^ (m + 1) - 1)
      omega
  · refine spaceCost_pair_bound ?_ ?_ ?_
    · refine spaceCost_comp_bound ?_ ?_
      · rw [spaceCost_cAcc]; omega
      · rw [hA]; exact spaceCost_succ_bound (by omega) (by omega)
    · rw [spaceCost_cAcc]; omega
    · rw [hSucc, hA]
      have := size_pair_le' (m + 1) m
      omega
  · rw [hARMS]
    have := size_pair_le' (val (comp cEq (pair (comp cMod (pair left cHdrPow))
      (comp cSub (pair cHdrPow (constCode 1))))) (Nat.pair a (Nat.pair y m)))
      (Nat.pair (m + 1) m)
    have h2 := size_pair_le' (m + 1) m
    omega
  · rw [val_pair, hARMS]
    have h1 := size_pair_le' (val (comp cEq (pair (comp cMod (pair left cHdrPow))
      (comp cSub (pair cHdrPow (constCode 1))))) (Nat.pair a (Nat.pair y m)))
      (Nat.pair (m + 1) m)
    have h2 := size_pair_le' (m + 1) m
    have h3 := spaceCost_cIte (Nat.pair (val (comp cEq (pair (comp cMod (pair left cHdrPow))
      (comp cSub (pair cHdrPow (constCode 1))))) (Nat.pair a (Nat.pair y m)))
      (Nat.pair (m + 1) m))
    omega

theorem spaceCost_trailCore (n : ℕ) : ∀ m,
    spaceCost trailCore (Nat.pair n m) ≤ 32 * max (Nat.size n) (Nat.size m) + 256 := by
  have hz : spaceCost trailCore (Nat.pair n 0) = spaceCost zero n :=
    spaceCost_prec_zero zero trailStep n
  have hs : ∀ j, spaceCost trailCore (Nat.pair n (j + 1))
      = max (spaceCost trailCore (Nat.pair n j))
          (spaceCost trailStep (Nat.pair n (Nat.pair j (val trailCore (Nat.pair n j))))) :=
    fun j => spaceCost_prec_succ zero trailStep n j
  intro m
  induction m with
  | zero =>
      rw [hz, spaceCost_zero]
      have h0 : Nat.size (0 : ℕ) = 0 := by decide
      omega
  | succ j ih =>
      rw [hs j, val_trailCore]
      have hacc : min (BoundedInterp.trailOnes n) j ≤ Nat.size n :=
        le_trans (min_le_left _ _) (trailOnes_le_size n)
      have hstep := spaceCost_trailStep n j (min (BoundedInterp.trailOnes n) j) hacc
      have hmono : Nat.size j ≤ Nat.size (j + 1) := Nat.size_le_size (Nat.le_succ j)
      omega

/-- **Reading the header's length runs in workspace linear in the cell's width.** -/
theorem spaceCost_cTrailOnes (n : ℕ) :
    spaceCost cTrailOnes n ≤ 32 * Nat.size n + 256 := by
  have hv : val (pair cId cId) n = Nat.pair n n := by rw [val_pair, val_cId]
  rw [cTrailOnes]
  refine spaceCost_comp_bound (spaceCost_pair_bound ?_ ?_ ?_) ?_
  · rw [spaceCost_cId]; omega
  · rw [spaceCost_cId]; omega
  · rw [val_cId]
    have := size_pair_le' n n
    omega
  · rw [hv]
    have := spaceCost_trailCore n n
    omega

/-! ### Reading a cell's workspace

The readers pay twice what building one does: undoing the frame's shift needs the divisor
`2 ^ (2 * stkLen s + 1)`, which on a numeral that is not a well-formed cell can be about twice as
wide as the numeral itself. That doubling is real, so it is carried rather than assumed away. -/

theorem stkLen_le_size (s : ℕ) : BoundedInterp.stkLen s ≤ Nat.size s := by
  have hbody : BoundedInterp.stkBody s ≤ s := by
    rw [BoundedInterp.stkBody]; exact Nat.div_le_self s 2
  rw [BoundedInterp.stkLen]
  exact le_trans (trailOnes_le_size _) (Nat.size_le_size hbody)

theorem size_stkBody_le (s : ℕ) : Nat.size (BoundedInterp.stkBody s) ≤ Nat.size s := by
  refine Nat.size_le_size ?_
  rw [BoundedInterp.stkBody]; exact Nat.div_le_self s 2

/-- **The declared frame width is read in workspace linear in the cell's width.** -/
theorem spaceCost_cStkLen (s : ℕ) : spaceCost cStkLen s ≤ 32 * Nat.size s + 256 := by
  have hb := size_stkBody_le s
  rw [cStkLen]
  refine spaceCost_comp_bound ?_ ?_
  · have := spaceCost_cStkBody s
    omega
  · rw [val_cStkBody]
    have := spaceCost_cTrailOnes (BoundedInterp.stkBody s)
    omega

/-- **The tail is read in workspace linear in the cell's width.** -/
theorem spaceCost_cStkTail (s : ℕ) : spaceCost cStkTail s ≤ 64 * Nat.size s + 256 := by
  have hb := size_stkBody_le s
  have hL := stkLen_le_size s
  have hLs : Nat.size (BoundedInterp.stkLen s) ≤ Nat.size s :=
    le_trans (size_le_self _) hL
  have hd1 : Nat.size (2 * BoundedInterp.stkLen s + 1)
      ≤ Nat.size (BoundedInterp.stkLen s) + 1 := size_two_mul_succ_le _
  have hd0 : Nat.size (2 * BoundedInterp.stkLen s)
      ≤ Nat.size (2 * BoundedInterp.stkLen s + 1) := Nat.size_le_size (Nat.le_succ _)
  have hpow : Nat.size (2 ^ (2 * BoundedInterp.stkLen s + 1))
      = 2 * BoundedInterp.stkLen s + 2 := size_two_pow _
  have hvShift : val (comp cPow2 (comp succ (comp cDbl cStkLen))) s
      = 2 ^ (2 * BoundedInterp.stkLen s + 1) := by
    rw [val_comp, val_comp, val_comp, val_cStkLen, val_cDbl, val_succ', val_cPow2]
  rw [cStkTail]
  refine spaceCost_comp_bound (spaceCost_pair_bound ?_ ?_ ?_) ?_
  · have := spaceCost_cStkBody s
    omega
  · refine spaceCost_comp_bound ?_ ?_
    · refine spaceCost_comp_bound ?_ ?_
      · refine spaceCost_comp_bound ?_ ?_
        · have := spaceCost_cStkLen s
          omega
        · rw [val_cStkLen]
          have := spaceCost_cDbl (BoundedInterp.stkLen s)
          omega
      · rw [val_comp, val_cStkLen, val_cDbl]
        exact spaceCost_succ_bound (by omega) (by omega)
    · rw [val_comp, val_comp, val_cStkLen, val_cDbl, val_succ']
      have := spaceCost_cPow2 (2 * BoundedInterp.stkLen s + 1)
      omega
  · rw [val_cStkBody, hvShift]
    have := size_pair_le' (BoundedInterp.stkBody s) (2 ^ (2 * BoundedInterp.stkLen s + 1))
    omega
  · rw [val_pair, val_cStkBody, hvShift]
    have := spaceCost_cDiv (BoundedInterp.stkBody s) (2 ^ (2 * BoundedInterp.stkLen s + 1))
    omega

/-- **The frame is read in workspace linear in the cell's width.** -/
theorem spaceCost_cStkHead (s : ℕ) : spaceCost cStkHead s ≤ 64 * Nat.size s + 256 := by
  have hb := size_stkBody_le s
  have hL := stkLen_le_size s
  have hLs : Nat.size (BoundedInterp.stkLen s) ≤ Nat.size s :=
    le_trans (size_le_self _) hL
  have hL1 : Nat.size (BoundedInterp.stkLen s + 1)
      ≤ Nat.size (BoundedInterp.stkLen s) + 1 := size_succ_le_size (le_refl _)
  have hpow1 : Nat.size (2 ^ (BoundedInterp.stkLen s + 1))
      = BoundedInterp.stkLen s + 2 := size_two_pow _
  have hpow0 : Nat.size (2 ^ BoundedInterp.stkLen s)
      = BoundedInterp.stkLen s + 1 := size_two_pow _
  have hvShift : val (comp cPow2 (comp succ cStkLen)) s
      = 2 ^ (BoundedInterp.stkLen s + 1) := by
    rw [val_comp, val_comp, val_cStkLen, val_succ', val_cPow2]
  have hvMask : val (comp cPow2 cStkLen) s = 2 ^ BoundedInterp.stkLen s := by
    rw [val_comp, val_cStkLen, val_cPow2]
  have hvDiv : val (comp cDiv (pair cStkBody (comp cPow2 (comp succ cStkLen)))) s
      = BoundedInterp.stkBody s / 2 ^ (BoundedInterp.stkLen s + 1) := by
    rw [val_comp, val_pair, val_cStkBody, hvShift, val_cDiv]
  have hvDivSz : Nat.size (BoundedInterp.stkBody s / 2 ^ (BoundedInterp.stkLen s + 1))
      ≤ Nat.size s :=
    le_trans (Nat.size_le_size (Nat.div_le_self _ _)) hb
  rw [cStkHead]
  refine spaceCost_comp_bound (spaceCost_pair_bound ?_ ?_ ?_) ?_
  · refine spaceCost_comp_bound (spaceCost_pair_bound ?_ ?_ ?_) ?_
    · have := spaceCost_cStkBody s
      omega
    · refine spaceCost_comp_bound ?_ ?_
      · refine spaceCost_comp_bound ?_ ?_
        · have := spaceCost_cStkLen s
          omega
        · rw [val_cStkLen]
          exact spaceCost_succ_bound (by omega) (by omega)
      · rw [val_comp, val_cStkLen, val_succ']
        have := spaceCost_cPow2 (BoundedInterp.stkLen s + 1)
        omega
    · rw [val_cStkBody, hvShift]
      have := size_pair_le' (BoundedInterp.stkBody s) (2 ^ (BoundedInterp.stkLen s + 1))
      omega
    · rw [val_pair, val_cStkBody, hvShift]
      have := spaceCost_cDiv (BoundedInterp.stkBody s) (2 ^ (BoundedInterp.stkLen s + 1))
      omega
  · refine spaceCost_comp_bound ?_ ?_
    · have := spaceCost_cStkLen s
      omega
    · rw [val_cStkLen]
      have := spaceCost_cPow2 (BoundedInterp.stkLen s)
      omega
  · rw [hvDiv, hvMask]
    have := size_pair_le' (BoundedInterp.stkBody s / 2 ^ (BoundedInterp.stkLen s + 1))
      (2 ^ BoundedInterp.stkLen s)
    omega
  · rw [val_pair, hvDiv, hvMask]
    have := spaceCost_cMod (BoundedInterp.stkBody s / 2 ^ (BoundedInterp.stkLen s + 1))
      (2 ^ BoundedInterp.stkLen s)
    omega

/-- **A cell is only a constant factor wider than what it packs.** The frame is stored twice over
— once as the unary header's length, once as its own bits — so three times the wider part, plus a
fixed margin, is the honest figure. -/
theorem size_stkCons_le (f k : ℕ) :
    Nat.size (BoundedInterp.stkCons f k) ≤ 3 * max (Nat.size f) (Nat.size k) + 5 := by
  have hM1 : Nat.size f ≤ max (Nat.size f) (Nat.size k) := le_max_left _ _
  have hM2 : Nat.size k ≤ max (Nat.size f) (Nat.size k) := le_max_right _ _
  have hz2 : Nat.size (2 ^ (Nat.size f + 1)) = Nat.size f + 2 := size_two_pow _
  have hz3 : Nat.size (2 ^ (2 * Nat.size f + 1)) = 2 * Nat.size f + 2 := size_two_pow _
  have hz0 : Nat.size (2 ^ Nat.size f - 1) ≤ Nat.size f := by
    refine Nat.size_le.2 ?_
    have : 0 < (2 : ℕ) ^ Nat.size f := by positivity
    omega
  have hb1 : Nat.size (f * 2 ^ (Nat.size f + 1)) ≤ Nat.size f + (Nat.size f + 2) :=
    le_trans (size_mul_le f _) (by omega)
  have hb2 : Nat.size (k * 2 ^ (2 * Nat.size f + 1)) ≤ Nat.size k + (2 * Nat.size f + 2) :=
    le_trans (size_mul_le k _) (by omega)
  have ha2 := size_add_le (2 ^ Nat.size f - 1) (f * 2 ^ (Nat.size f + 1))
  have hsum := size_add_le (2 ^ Nat.size f - 1 + f * 2 ^ (Nat.size f + 1))
    (k * 2 ^ (2 * Nat.size f + 1))
  have hdbl := size_two_mul_succ_le (2 ^ Nat.size f - 1 + f * 2 ^ (Nat.size f + 1)
    + k * 2 ^ (2 * Nat.size f + 1))
  rw [BoundedInterp.stkCons, BoundedInterp.frameBits]
  omega

theorem stkHead_le (s : ℕ) : BoundedInterp.stkHead s ≤ s := by
  rw [BoundedInterp.stkHead]
  refine le_trans (Nat.mod_le _ _) (le_trans (Nat.div_le_self _ _) ?_)
  rw [BoundedInterp.stkBody]; exact Nat.div_le_self s 2

theorem stkTail_le (s : ℕ) : BoundedInterp.stkTail s ≤ s := by
  rw [BoundedInterp.stkTail]
  refine le_trans (Nat.div_le_self _ _) ?_
  rw [BoundedInterp.stkBody]; exact Nat.div_le_self s 2

/-- **The cell test runs in workspace linear in the numeral's width.** -/
theorem spaceCost_cStkIsCons (s : ℕ) : spaceCost cStkIsCons s ≤ 64 * Nat.size s + 256 := by
  have hh : Nat.size (BoundedInterp.stkHead s) ≤ Nat.size s := Nat.size_le_size (stkHead_le s)
  have ht : Nat.size (BoundedInterp.stkTail s) ≤ Nat.size s := Nat.size_le_size (stkTail_le s)
  have hc := size_stkCons_le (BoundedInterp.stkHead s) (BoundedInterp.stkTail s)
  have hvPair : val (pair cStkHead cStkTail) s
      = Nat.pair (BoundedInterp.stkHead s) (BoundedInterp.stkTail s) := by
    rw [val_pair, val_cStkHead, val_cStkTail]
  have hvCons : val (comp cStkCons (pair cStkHead cStkTail)) s
      = BoundedInterp.stkCons (BoundedInterp.stkHead s) (BoundedInterp.stkTail s) := by
    rw [val_comp, hvPair, val_cStkCons]
  rw [cStkIsCons]
  refine spaceCost_comp_bound (spaceCost_pair_bound ?_ ?_ ?_) ?_
  · refine spaceCost_comp_bound (spaceCost_pair_bound ?_ ?_ ?_) ?_
    · have := spaceCost_cStkHead s
      omega
    · have := spaceCost_cStkTail s
      omega
    · rw [val_cStkHead, val_cStkTail]
      have := size_pair_le' (BoundedInterp.stkHead s) (BoundedInterp.stkTail s)
      omega
    · rw [hvPair]
      have := spaceCost_cStkCons (BoundedInterp.stkHead s) (BoundedInterp.stkTail s)
      omega
  · rw [spaceCost_cId]; omega
  · rw [hvCons, val_cId]
    have := size_pair_le' (BoundedInterp.stkCons (BoundedInterp.stkHead s)
      (BoundedInterp.stkTail s)) s
    omega
  · rw [val_pair, hvCons, val_cId]
    have := spaceCost_cEq (BoundedInterp.stkCons (BoundedInterp.stkHead s)
      (BoundedInterp.stkTail s)) s
    omega

/-- **The halt test runs in workspace linear in the configuration's width.** -/
theorem spaceCost_cIsHalt (s : ℕ) : spaceCost cIsHalt s ≤ 8 * Nat.size s + 128 := by
  have hmode : Nat.size (BoundedInterp.cfMode s) ≤ Nat.size s :=
    Nat.size_le_size (Nat.unpair_left_le s)
  have hstk : Nat.size (BoundedInterp.cfStk s) ≤ Nat.size s := by
    refine Nat.size_le_size ?_
    exact le_trans (Nat.unpair_right_le _) (Nat.unpair_right_le s)
  have h1sz : Nat.size (1 : ℕ) = 1 := by decide
  have h0sz : Nat.size (0 : ℕ) = 0 := by decide
  have hvA : val (comp cEq (pair cCfMode (constCode 1))) s
      = if BoundedInterp.cfMode s = 1 then 1 else 0 := by
    rw [val_comp, val_pair, val_cCfMode, val_constCode, val_cEq]
  have hvB : val (comp cEq (pair cCfStk (constCode 0))) s
      = if BoundedInterp.cfStk s = 0 then 1 else 0 := by
    rw [val_comp, val_pair, val_cCfStk, val_constCode, val_cEq]
  have hAle : val (comp cEq (pair cCfMode (constCode 1))) s ≤ 1 := by
    rw [hvA]; split <;> simp
  have hBle : val (comp cEq (pair cCfStk (constCode 0))) s ≤ 1 := by
    rw [hvB]; split <;> simp
  have hAsz := size_le_self (val (comp cEq (pair cCfMode (constCode 1))) s)
  have hBsz := size_le_self (val (comp cEq (pair cCfStk (constCode 0))) s)
  rw [cIsHalt]
  refine spaceCost_comp_bound (spaceCost_pair_bound ?_ ?_ ?_) ?_
  · refine spaceCost_comp_bound (spaceCost_pair_bound ?_ ?_ ?_) ?_
    · rw [cCfMode]; exact spaceCost_left_bound (by omega)
    · have := spaceCost_constCode 1 s
      omega
    · rw [val_cCfMode, val_constCode]
      have := size_pair_le' (BoundedInterp.cfMode s) 1
      omega
    · rw [val_pair, val_cCfMode, val_constCode]
      have := spaceCost_cEq (BoundedInterp.cfMode s) 1
      omega
  · refine spaceCost_comp_bound (spaceCost_pair_bound ?_ ?_ ?_) ?_
    · rw [cCfStk]
      refine spaceCost_comp_bound (spaceCost_right_bound (by omega)) ?_
      exact spaceCost_right_bound (Nat.size_le_size (Nat.unpair_right_le s) |>.trans (by omega))
    · have := spaceCost_constCode 0 s
      omega
    · rw [val_cCfStk, val_constCode]
      have := size_pair_le' (BoundedInterp.cfStk s) 0
      omega
    · rw [val_pair, val_cCfStk, val_constCode]
      have := spaceCost_cEq (BoundedInterp.cfStk s) 0
      omega
  · have := size_pair_le' (val (comp cEq (pair cCfMode (constCode 1))) s)
      (val (comp cEq (pair cCfStk (constCode 0))) s)
    omega
  · rw [val_pair]
    have h1 := size_pair_le' (val (comp cEq (pair cCfMode (constCode 1))) s)
      (val (comp cEq (pair cCfStk (constCode 0))) s)
    have h2 := spaceCost_cAnd (Nat.pair (val (comp cEq (pair cCfMode (constCode 1))) s)
      (val (comp cEq (pair cCfStk (constCode 0))) s))
    omega

/-! ## Growth bounds

The walks so far bounded one code at a time. The branches cannot be done that way — there are
fourteen of them, each a nest of pairings over slots — so the bound is made compositional instead.

A growth bound records two things about `g`: the workspace it uses, and the width of the value it
returns. Both are needed, because a pair node's cost is exactly the width of the pair it forms, so
bounding cost alone is not closed under pairing.

They are recorded **separately**. Division costs thirty-two times its argument's width yet returns
something no wider than its argument; carrying one figure for both would let that thirty-two enter
the width, and a nest of pairings would then double it at every level for no reason. Keeping the
two apart is what holds the coefficients down. -/

/-- Workspace `cc * size I + dc`, and output width `cw * size I + dw`. -/
def GrowBound (g : Code) (cc dc cw dw : ℕ) : Prop :=
  ∀ I, spaceCost g I ≤ cc * Nat.size I + dc ∧ Nat.size (val g I) ≤ cw * Nat.size I + dw

namespace GrowBound

theorem cost {g : Code} {cc dc cw dw : ℕ} (h : GrowBound g cc dc cw dw) (I : ℕ) :
    spaceCost g I ≤ cc * Nat.size I + dc := (h I).1

theorem width {g : Code} {cc dc cw dw : ℕ} (h : GrowBound g cc dc cw dw) (I : ℕ) :
    Nat.size (val g I) ≤ cw * Nat.size I + dw := (h I).2

theorem mono {g : Code} {cc dc cw dw cc' dc' cw' dw' : ℕ} (h : GrowBound g cc dc cw dw)
    (h1 : cc ≤ cc') (h2 : dc ≤ dc') (h3 : cw ≤ cw') (h4 : dw ≤ dw') :
    GrowBound g cc' dc' cw' dw' := by
  intro I
  have e1 := h.cost I
  have e2 := h.width I
  have m1 : cc * Nat.size I ≤ cc' * Nat.size I := Nat.mul_le_mul h1 (le_refl _)
  have m2 : cw * Nat.size I ≤ cw' * Nat.size I := Nat.mul_le_mul h3 (le_refl _)
  exact ⟨by omega, by omega⟩

end GrowBound

/-- Composition: the outer code's coefficients apply to the inner code's *output* width, and the
cost is the larger of the two stages. -/
theorem growBound_comp {f g : Code} {cc₁ dc₁ cw₁ dw₁ cc₂ dc₂ cw₂ dw₂ : ℕ}
    (hg : GrowBound g cc₁ dc₁ cw₁ dw₁) (hf : GrowBound f cc₂ dc₂ cw₂ dw₂) :
    GrowBound (comp f g) (max cc₁ (cc₂ * cw₁)) (max dc₁ (cc₂ * dw₁ + dc₂))
      (cw₂ * cw₁) (cw₂ * dw₁ + dw₂) := by
  intro I
  have hg1 := hg.cost I
  have hg2 := hg.width I
  have hf1 := hf.cost (val g I)
  have hf2 := hf.width (val g I)
  have kc : cc₂ * Nat.size (val g I) ≤ cc₂ * (cw₁ * Nat.size I + dw₁) :=
    Nat.mul_le_mul (le_refl _) hg2
  have kw : cw₂ * Nat.size (val g I) ≤ cw₂ * (cw₁ * Nat.size I + dw₁) :=
    Nat.mul_le_mul (le_refl _) hg2
  have ec : cc₂ * (cw₁ * Nat.size I + dw₁) + dc₂ = cc₂ * cw₁ * Nat.size I + (cc₂ * dw₁ + dc₂) := by
    ring
  have ew : cw₂ * (cw₁ * Nat.size I + dw₁) + dw₂ = cw₂ * cw₁ * Nat.size I + (cw₂ * dw₁ + dw₂) := by
    ring
  have b1 : cc₁ * Nat.size I ≤ max cc₁ (cc₂ * cw₁) * Nat.size I :=
    Nat.mul_le_mul (le_max_left _ _) (le_refl _)
  have b2 : cc₂ * cw₁ * Nat.size I ≤ max cc₁ (cc₂ * cw₁) * Nat.size I :=
    Nat.mul_le_mul (le_max_right _ _) (le_refl _)
  have d1 : dc₁ ≤ max dc₁ (cc₂ * dw₁ + dc₂) := le_max_left _ _
  have d2 : cc₂ * dw₁ + dc₂ ≤ max dc₁ (cc₂ * dw₁ + dc₂) := le_max_right _ _
  constructor
  · rw [spaceCost_comp]
    refine max_le (by omega) ?_
    calc spaceCost f (val g I) ≤ cc₂ * Nat.size (val g I) + dc₂ := hf1
      _ ≤ cc₂ * (cw₁ * Nat.size I + dw₁) + dc₂ := Nat.add_le_add_right kc dc₂
      _ = cc₂ * cw₁ * Nat.size I + (cc₂ * dw₁ + dc₂) := ec
      _ ≤ max cc₁ (cc₂ * cw₁) * Nat.size I + max dc₁ (cc₂ * dw₁ + dc₂) := by omega
  · rw [val_comp]
    calc Nat.size (val f (val g I)) ≤ cw₂ * Nat.size (val g I) + dw₂ := hf2
      _ ≤ cw₂ * (cw₁ * Nat.size I + dw₁) + dw₂ := Nat.add_le_add_right kw dw₂
      _ = cw₂ * cw₁ * Nat.size I + (cw₂ * dw₁ + dw₂) := ew

/-- Pairing: the width doubles, and the cost is the larger of the parts' costs and the width of the
pair actually formed. -/
theorem growBound_pair {f g : Code} {cc₁ dc₁ cw₁ dw₁ cc₂ dc₂ cw₂ dw₂ : ℕ}
    (hf : GrowBound f cc₁ dc₁ cw₁ dw₁) (hg : GrowBound g cc₂ dc₂ cw₂ dw₂) :
    GrowBound (pair f g) (max (max cc₁ cc₂) (2 * max cw₁ cw₂))
      (max (max dc₁ dc₂) (2 * max dw₁ dw₂)) (2 * max cw₁ cw₂) (2 * max dw₁ dw₂) := by
  intro I
  have hf1 := hf.cost I
  have hf2 := hf.width I
  have hg1 := hg.cost I
  have hg2 := hg.width I
  have hp := size_pair_le' (val f I) (val g I)
  have b1 : cw₁ * Nat.size I ≤ max cw₁ cw₂ * Nat.size I :=
    Nat.mul_le_mul (le_max_left _ _) (le_refl _)
  have b2 : cw₂ * Nat.size I ≤ max cw₁ cw₂ * Nat.size I :=
    Nat.mul_le_mul (le_max_right _ _) (le_refl _)
  have c1 : cc₁ * Nat.size I ≤ max (max cc₁ cc₂) (2 * max cw₁ cw₂) * Nat.size I :=
    Nat.mul_le_mul (le_trans (le_max_left _ _) (le_max_left _ _)) (le_refl _)
  have c2 : cc₂ * Nat.size I ≤ max (max cc₁ cc₂) (2 * max cw₁ cw₂) * Nat.size I :=
    Nat.mul_le_mul (le_trans (le_max_right _ _) (le_max_left _ _)) (le_refl _)
  have c3 : 2 * max cw₁ cw₂ * Nat.size I ≤ max (max cc₁ cc₂) (2 * max cw₁ cw₂) * Nat.size I :=
    Nat.mul_le_mul (le_max_right _ _) (le_refl _)
  have hd1 : dw₁ ≤ max dw₁ dw₂ := le_max_left _ _
  have hd2 : dw₂ ≤ max dw₁ dw₂ := le_max_right _ _
  have he1 : dc₁ ≤ max (max dc₁ dc₂) (2 * max dw₁ dw₂) :=
    le_trans (le_max_left _ _) (le_max_left _ _)
  have he2 : dc₂ ≤ max (max dc₁ dc₂) (2 * max dw₁ dw₂) :=
    le_trans (le_max_right _ _) (le_max_left _ _)
  have he3 : 2 * max dw₁ dw₂ ≤ max (max dc₁ dc₂) (2 * max dw₁ dw₂) := le_max_right _ _
  have hexp : 2 * max cw₁ cw₂ * Nat.size I + 2 * max dw₁ dw₂
      = 2 * (max cw₁ cw₂ * Nat.size I + max dw₁ dw₂) := by ring
  have hpp : Nat.size (Nat.pair (val f I) (val g I))
      ≤ 2 * (max cw₁ cw₂ * Nat.size I + max dw₁ dw₂) := by omega
  constructor
  · rw [spaceCost_pair]
    refine max_le (max_le (by omega) (by omega)) ?_
    omega
  · rw [val_pair]; omega

/-! ### The leaves -/

theorem growBound_left : GrowBound left 1 0 1 0 := by
  intro I
  have h := Nat.size_le_size (Nat.unpair_left_le I)
  exact ⟨by rw [spaceCost_left]; omega, by rw [val_left']; omega⟩

theorem growBound_right : GrowBound right 1 0 1 0 := by
  intro I
  have h := Nat.size_le_size (Nat.unpair_right_le I)
  exact ⟨by rw [spaceCost_right]; omega, by rw [val_right']; omega⟩

theorem growBound_zero : GrowBound zero 1 0 0 0 := by
  intro I
  have h0 : Nat.size (0 : ℕ) = 0 := by decide
  exact ⟨by rw [spaceCost_zero]; omega, by rw [val_zero']; omega⟩

theorem growBound_succ : GrowBound succ 1 1 1 1 := by
  intro I
  have h := size_succ_le_size (le_refl I)
  have hs := size_le_self I
  exact ⟨by rw [spaceCost_succ]; omega, by rw [val_succ']; omega⟩

theorem growBound_cId : GrowBound cId 1 0 1 0 := by
  intro I
  exact ⟨by rw [spaceCost_cId]; omega, by rw [val_cId]; omega⟩

theorem growBound_constCode (j : ℕ) : GrowBound (constCode j) 1 (Nat.size j) 0 (Nat.size j) := by
  intro I
  have := spaceCost_constCode j I
  exact ⟨by omega, by rw [val_constCode]; omega⟩

/-! ### The composite codes

Each entry pairs a workspace bound already proved above with a width fact. The width facts are the
cheap half — most of these codes return something no wider than what they were given — and keeping
them out of the cost column is exactly what stops the coefficients compounding. -/

theorem left_le_pair (x y : ℕ) : x ≤ Nat.pair x y := by
  have := Nat.unpair_left_le (Nat.pair x y); rwa [Nat.unpair_pair] at this

theorem right_le_pair (x y : ℕ) : y ≤ Nat.pair x y := by
  have := Nat.unpair_right_le (Nat.pair x y); rwa [Nat.unpair_pair] at this

/-- A constant's width, given as a numeral rather than as `Nat.size` of one. -/
theorem growBound_constCode' (j b : ℕ) (h : Nat.size j ≤ b) :
    GrowBound (constCode j) 1 b 0 b :=
  (growBound_constCode j).mono (le_refl _) h (le_refl _) h

theorem growBound_cSub : GrowBound cSub 8 16 1 0 := by
  intro I
  obtain ⟨x, y, rfl⟩ : ∃ x y, I = Nat.pair x y :=
    ⟨I.unpair.1, I.unpair.2, (Nat.pair_unpair I).symm⟩
  have hx : Nat.size x ≤ Nat.size (Nat.pair x y) := Nat.size_le_size (left_le_pair x y)
  have hy : Nat.size y ≤ Nat.size (Nat.pair x y) := Nat.size_le_size (right_le_pair x y)
  refine ⟨by have := spaceCost_cSub x y; omega, ?_⟩
  rw [val_cSub]
  exact le_trans (Nat.size_le_size (Nat.sub_le x y)) (by omega)

theorem growBound_cDiv : GrowBound cDiv 32 128 1 0 := by
  intro I
  obtain ⟨x, y, rfl⟩ : ∃ x y, I = Nat.pair x y :=
    ⟨I.unpair.1, I.unpair.2, (Nat.pair_unpair I).symm⟩
  have hx : Nat.size x ≤ Nat.size (Nat.pair x y) := Nat.size_le_size (left_le_pair x y)
  have hy : Nat.size y ≤ Nat.size (Nat.pair x y) := Nat.size_le_size (right_le_pair x y)
  refine ⟨by have := spaceCost_cDiv x y; omega, ?_⟩
  rw [val_cDiv]
  exact le_trans (Nat.size_le_size (Nat.div_le_self x y)) (by omega)

theorem growBound_cMod : GrowBound cMod 32 128 1 0 := by
  intro I
  obtain ⟨x, y, rfl⟩ : ∃ x y, I = Nat.pair x y :=
    ⟨I.unpair.1, I.unpair.2, (Nat.pair_unpair I).symm⟩
  have hx : Nat.size x ≤ Nat.size (Nat.pair x y) := Nat.size_le_size (left_le_pair x y)
  have hy : Nat.size y ≤ Nat.size (Nat.pair x y) := Nat.size_le_size (right_le_pair x y)
  refine ⟨by have := spaceCost_cMod x y; omega, ?_⟩
  rw [val_cMod]
  exact le_trans (Nat.size_le_size (Nat.mod_le x y)) (by omega)

theorem growBound_cEq : GrowBound cEq 8 64 0 1 := by
  intro I
  obtain ⟨x, y, rfl⟩ : ∃ x y, I = Nat.pair x y :=
    ⟨I.unpair.1, I.unpair.2, (Nat.pair_unpair I).symm⟩
  have hx : Nat.size x ≤ Nat.size (Nat.pair x y) := Nat.size_le_size (left_le_pair x y)
  have hy : Nat.size y ≤ Nat.size (Nat.pair x y) := Nat.size_le_size (right_le_pair x y)
  refine ⟨by have := spaceCost_cEq x y; omega, ?_⟩
  rw [val_cEq]
  split <;> simp

theorem growBound_cSize : GrowBound cSize 32 128 1 0 := by
  intro I
  refine ⟨by have := spaceCost_cSize I; omega, ?_⟩
  rw [val_cSize]
  have := Nat.size_le_size (size_le_self I)
  omega

theorem growBound_cStkCons : GrowBound cStkCons 32 128 3 5 := by
  intro I
  obtain ⟨f, k, rfl⟩ : ∃ f k, I = Nat.pair f k :=
    ⟨I.unpair.1, I.unpair.2, (Nat.pair_unpair I).symm⟩
  have hf : Nat.size f ≤ Nat.size (Nat.pair f k) := Nat.size_le_size (left_le_pair f k)
  have hk : Nat.size k ≤ Nat.size (Nat.pair f k) := Nat.size_le_size (right_le_pair f k)
  refine ⟨by have := spaceCost_cStkCons f k; omega, ?_⟩
  rw [val_cStkCons]
  have := size_stkCons_le f k
  omega

theorem growBound_cIte : GrowBound cIte 8 32 1 0 := by
  intro I
  obtain ⟨b, r, rfl⟩ : ∃ b r, I = Nat.pair b r :=
    ⟨I.unpair.1, I.unpair.2, (Nat.pair_unpair I).symm⟩
  obtain ⟨u, v, rfl⟩ : ∃ u v, r = Nat.pair u v :=
    ⟨r.unpair.1, r.unpair.2, (Nat.pair_unpair r).symm⟩
  have hr : Nat.size (Nat.pair u v) ≤ Nat.size (Nat.pair b (Nat.pair u v)) :=
    Nat.size_le_size (right_le_pair _ _)
  have hu : Nat.size u ≤ Nat.size (Nat.pair u v) := Nat.size_le_size (left_le_pair u v)
  have hv : Nat.size v ≤ Nat.size (Nat.pair u v) := Nat.size_le_size (right_le_pair u v)
  refine ⟨by have := spaceCost_cIte (Nat.pair b (Nat.pair u v)); omega, ?_⟩
  rw [val_cIte]
  split <;> omega

theorem growBound_cStkHead : GrowBound cStkHead 64 256 1 0 := by
  intro I
  refine ⟨by have := spaceCost_cStkHead I; omega, ?_⟩
  rw [val_cStkHead]
  have := Nat.size_le_size (stkHead_le I)
  omega

theorem growBound_cStkTail : GrowBound cStkTail 64 256 1 0 := by
  intro I
  refine ⟨by have := spaceCost_cStkTail I; omega, ?_⟩
  rw [val_cStkTail]
  have := Nat.size_le_size (stkTail_le I)
  omega

theorem growBound_cStkIsCons : GrowBound cStkIsCons 64 256 0 1 := by
  intro I
  refine ⟨by have := spaceCost_cStkIsCons I; omega, ?_⟩
  rw [val_cStkIsCons]
  split <;> simp

theorem growBound_cIsHalt : GrowBound cIsHalt 8 128 0 1 := by
  intro I
  refine ⟨by have := spaceCost_cIsHalt I; omega, ?_⟩
  rw [val_cIsHalt]
  split <;> simp

/-- The returning constructor and the descending one are pure pair-trees over leaves, so the
algebra alone settles them. -/
theorem growBound_cRet : GrowBound cRet 2 2 2 2 := by
  rw [cRet]
  exact growBound_pair (growBound_constCode' 1 1 (by decide)) growBound_cId

theorem growBound_cDescend : GrowBound cDescend 8 0 8 0 := by
  rw [cDescend]
  exact growBound_pair growBound_zero
    (growBound_pair (growBound_pair growBound_left (growBound_comp growBound_right growBound_left))
      (growBound_comp growBound_right growBound_right))

/-! ### The slots

The dispatch's slots read parts of the input, so none of them grows what it was given. The
projections cost nothing beyond their argument's width; the three arithmetic slots pay for the
subtraction and division that split a code numeral into its tag and children, but still return
something no wider than the input, which is what the branches above them need. -/

/-- Improve a growth bound's width column, leaving its cost column alone. -/
theorem GrowBound.tightenWidth {g : Code} {cc dc cw dw cw' dw' : ℕ}
    (h : GrowBound g cc dc cw dw)
    (hw : ∀ I, Nat.size (val g I) ≤ cw' * Nat.size I + dw') : GrowBound g cc dc cw' dw' :=
  fun I => ⟨h.cost I, hw I⟩

/-- A projection composed onto a projection is again one. -/
theorem growBound_projComp {f g : Code} (hg : GrowBound g 1 0 1 0) (hf : GrowBound f 1 0 1 0) :
    GrowBound (comp f g) 1 0 1 0 :=
  (growBound_comp hg hf).mono (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem growBound_dC : GrowBound dC 1 0 1 0 := by rw [dC]; exact growBound_left
theorem growBound_dN : GrowBound dN 1 0 1 0 := by
  rw [dN]; exact growBound_projComp growBound_right growBound_left
theorem growBound_dK : GrowBound dK 1 0 1 0 := by
  rw [dK]; exact growBound_projComp growBound_right growBound_right
theorem growBound_dN1 : GrowBound dN1 1 0 1 0 := by
  rw [dN1]; exact growBound_projComp growBound_dN growBound_left
theorem growBound_dN2 : GrowBound dN2 1 0 1 0 := by
  rw [dN2]; exact growBound_projComp growBound_dN growBound_right

theorem growBound_rV : GrowBound rV 1 0 1 0 := by rw [rV]; exact growBound_left
theorem growBound_rF : GrowBound rF 1 0 1 0 := by
  rw [rF]; exact growBound_projComp growBound_right growBound_left
theorem growBound_rK : GrowBound rK 1 0 1 0 := by
  rw [rK]; exact growBound_projComp growBound_right growBound_right
theorem growBound_rTag : GrowBound rTag 1 0 1 0 := by
  rw [rTag]; exact growBound_projComp growBound_rF growBound_left
theorem growBound_rPay : GrowBound rPay 1 0 1 0 := by
  rw [rPay]; exact growBound_projComp growBound_rF growBound_right
theorem growBound_rPay1 : GrowBound rPay1 1 0 1 0 := by
  rw [rPay1]; exact growBound_projComp growBound_rPay growBound_left
theorem growBound_rPay2 : GrowBound rPay2 1 0 1 0 := by
  rw [rPay2]; exact growBound_projComp growBound_rPay growBound_right
theorem growBound_rPay21 : GrowBound rPay21 1 0 1 0 := by
  rw [rPay21]; exact growBound_projComp growBound_rPay2 growBound_left
theorem growBound_rPay22 : GrowBound rPay22 1 0 1 0 := by
  rw [rPay22]; exact growBound_projComp growBound_rPay2 growBound_right
theorem growBound_rPay221 : GrowBound rPay221 1 0 1 0 := by
  rw [rPay221]; exact growBound_projComp growBound_rPay22 growBound_left
theorem growBound_rPay222 : GrowBound rPay222 1 0 1 0 := by
  rw [rPay222]; exact growBound_projComp growBound_rPay22 growBound_right

/-- Splitting off the four leaf codes. -/
theorem growBound_dM : GrowBound dM 16 64 1 0 := by
  refine GrowBound.tightenWidth (?_ : GrowBound dM 16 64 2 6) ?_
  · rw [dM, dC]
    exact (growBound_comp
      (growBound_pair growBound_left (growBound_constCode' 4 3 (by decide)))
      growBound_cSub).mono (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · intro I
    rw [dM, dC, val_comp, val_pair, val_left', val_constCode, val_cSub]
    have h1 : I.unpair.1 - 4 ≤ I := le_trans (Nat.sub_le _ _) (Nat.unpair_left_le I)
    have := Nat.size_le_size h1
    omega

/-- The children's packed numeral. -/
theorem growBound_dP : GrowBound dP 64 320 1 0 := by
  refine GrowBound.tightenWidth (?_ : GrowBound dP 64 320 2 6) ?_
  · rw [dP]
    exact (growBound_comp
      (growBound_pair growBound_dM (growBound_constCode' 4 3 (by decide)))
      growBound_cDiv).mono (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · intro I
    rw [dP, val_comp, val_pair, val_constCode, val_cDiv]
    have hm := growBound_dM.width I
    have h1 : val dM I / 4 ≤ val dM I := Nat.div_le_self _ _
    have := Nat.size_le_size h1
    omega

/-- The constructor tag. -/
theorem growBound_dT : GrowBound dT 64 320 1 0 := by
  refine GrowBound.tightenWidth (?_ : GrowBound dT 64 320 2 6) ?_
  · rw [dT]
    exact (growBound_comp
      (growBound_pair growBound_dM (growBound_constCode' 4 3 (by decide)))
      growBound_cMod).mono (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · intro I
    rw [dT, val_comp, val_pair, val_constCode, val_cMod]
    have hm := growBound_dM.width I
    have h1 : val dM I % 4 ≤ val dM I := Nat.mod_le _ _
    have := Nat.size_le_size h1
    omega

theorem growBound_dP1 : GrowBound dP1 64 320 1 0 := by
  rw [dP1]
  exact (growBound_comp growBound_dP growBound_left).mono
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem growBound_dP2 : GrowBound dP2 64 320 1 0 := by
  rw [dP2]
  exact (growBound_comp growBound_dP growBound_right).mono
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-! ### The fourteen branches

Each branch is now a single composition term: the proof mirrors the code's own tree, and the
coefficients follow from the laws rather than from a hand walk. They are then brought to one
common pair of columns, which is what the selection laws consume.

The common figures are set by `prec`'s descending branch and by the loop's returning branch, the
two deepest: both build a stack cell over a payload that is itself four pairings deep. -/

theorem growBound_cPred : GrowBound cPred 4 4 1 0 := by
  intro I
  refine ⟨by have := spaceCost_cPred I; omega, ?_⟩
  rw [val_cPred]
  have := Nat.size_le_size (Nat.sub_le I 1)
  omega

/-- The common columns every branch is brought to. -/
abbrev branchC : ℕ := 4096

theorem growBound_dB0 : GrowBound dB0 branchC branchC branchC branchC := by
  rw [dB0]
  exact (growBound_comp
    (growBound_pair (growBound_constCode' 0 0 (by decide)) growBound_dK)
    growBound_cRet).mono (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem growBound_dB1 : GrowBound dB1 branchC branchC branchC branchC := by
  rw [dB1]
  exact (growBound_comp
    (growBound_pair (growBound_comp growBound_dN growBound_succ) growBound_dK)
    growBound_cRet).mono (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem growBound_dB2 : GrowBound dB2 branchC branchC branchC branchC := by
  rw [dB2]
  exact (growBound_comp (growBound_pair growBound_dN1 growBound_dK)
    growBound_cRet).mono (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem growBound_dB3 : GrowBound dB3 branchC branchC branchC branchC := by
  rw [dB3]
  exact (growBound_comp (growBound_pair growBound_dN2 growBound_dK)
    growBound_cRet).mono (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem growBound_dBpair : GrowBound dBpair branchC branchC branchC branchC := by
  rw [dBpair]
  exact (growBound_comp
    (growBound_pair growBound_dP1
      (growBound_pair growBound_dN
        (growBound_comp
          (growBound_pair
            (growBound_pair (growBound_constCode' 0 0 (by decide))
              (growBound_pair growBound_dP2 growBound_dN))
            growBound_dK)
          growBound_cStkCons)))
    growBound_cDescend).mono (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem growBound_dBprec : GrowBound dBprec branchC branchC branchC branchC := by
  rw [dBprec]
  exact (growBound_comp
    (growBound_pair growBound_dP1
      (growBound_pair growBound_dN1
        (growBound_comp
          (growBound_pair
            (growBound_pair (growBound_constCode' 3 2 (by decide))
              (growBound_pair growBound_dP2
                (growBound_pair growBound_dN1
                  (growBound_pair (growBound_constCode' 0 0 (by decide)) growBound_dN2))))
            growBound_dK)
          growBound_cStkCons)))
    growBound_cDescend).mono (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem growBound_dBcomp : GrowBound dBcomp branchC branchC branchC branchC := by
  rw [dBcomp]
  exact (growBound_comp
    (growBound_pair growBound_dP2
      (growBound_pair growBound_dN
        (growBound_comp
          (growBound_pair
            (growBound_pair (growBound_constCode' 2 2 (by decide)) growBound_dP1)
            growBound_dK)
          growBound_cStkCons)))
    growBound_cDescend).mono (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem growBound_dBrfind : GrowBound dBrfind branchC branchC branchC branchC := by
  rw [dBrfind]
  exact (growBound_comp
    (growBound_pair growBound_dP
      (growBound_pair growBound_dN
        (growBound_comp
          (growBound_pair
            (growBound_pair (growBound_constCode' 4 3 (by decide))
              (growBound_pair growBound_dP growBound_dN))
            growBound_dK)
          growBound_cStkCons)))
    growBound_cDescend).mono (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem growBound_rB0 : GrowBound rB0 branchC branchC branchC branchC := by
  rw [rB0]
  exact (growBound_comp
    (growBound_pair growBound_rPay1
      (growBound_pair growBound_rPay2
        (growBound_comp
          (growBound_pair
            (growBound_pair (growBound_constCode' 1 1 (by decide)) growBound_rV)
            growBound_rK)
          growBound_cStkCons)))
    growBound_cDescend).mono (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem growBound_rB1 : GrowBound rB1 branchC branchC branchC branchC := by
  rw [rB1]
  exact (growBound_comp
    (growBound_pair (growBound_pair growBound_rPay growBound_rV) growBound_rK)
    growBound_cRet).mono (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem growBound_rB2 : GrowBound rB2 branchC branchC branchC branchC := by
  rw [rB2]
  exact (growBound_comp
    (growBound_pair growBound_rPay (growBound_pair growBound_rV growBound_rK))
    growBound_cDescend).mono (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem growBound_rB3loop : GrowBound rB3loop branchC branchC branchC branchC := by
  rw [rB3loop]
  exact (growBound_comp
    (growBound_pair growBound_rPay1
      (growBound_pair
        (growBound_pair growBound_rPay21 (growBound_pair growBound_rPay221 growBound_rV))
        (growBound_comp
          (growBound_pair
            (growBound_pair (growBound_constCode' 3 2 (by decide))
              (growBound_pair growBound_rPay1
                (growBound_pair growBound_rPay21
                  (growBound_pair (growBound_comp growBound_rPay221 growBound_succ)
                    (growBound_comp growBound_rPay222 growBound_cPred)))))
            growBound_rK)
          growBound_cStkCons)))
    growBound_cDescend).mono (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem growBound_rB4search : GrowBound rB4search branchC branchC branchC branchC := by
  rw [rB4search]
  exact (growBound_comp
    (growBound_pair growBound_rPay1
      (growBound_pair
        (growBound_pair growBound_rPay21 (growBound_comp growBound_rPay22 growBound_succ))
        (growBound_comp
          (growBound_pair
            (growBound_pair (growBound_constCode' 4 3 (by decide))
              (growBound_pair growBound_rPay1
                (growBound_pair growBound_rPay21
                  (growBound_comp growBound_rPay22 growBound_succ))))
            growBound_rK)
          growBound_cStkCons)))
    growBound_cDescend).mono (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem growBound_rBdef : GrowBound rBdef branchC branchC branchC branchC := by
  rw [rBdef]
  exact (growBound_comp
    (growBound_pair growBound_rV
      (growBound_comp (growBound_pair growBound_rF growBound_rK) growBound_cStkCons))
    growBound_cRet).mono (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-! ### The trees

Selection in growth-bound form. The point of the law is visible in the arithmetic: the width
columns pass through unchanged, so the cost columns stop climbing after the first selection and the
seven nested ones cost exactly what one does. Both arms are charged at every level. -/

theorem growBound_cSel {b x y : Code} {ccb dcb cc dc cw dw : ℕ}
    (hb : GrowBound b ccb dcb 0 1)
    (hx : GrowBound x cc dc cw dw) (hy : GrowBound y cc dc cw dw) :
    GrowBound (cSel b x y) (max (max ccb cc) (32 * cw))
      (max (max dcb dc) (32 * dw + 48)) cw dw := by
  intro I
  have hb1 := hb.cost I
  have hb2 := hb.width I
  have hx1 := hx.cost I
  have hx2 := hx.width I
  have hy1 := hy.cost I
  have hy2 := hy.width I
  have hp1 := size_pair_le' (val x I) (val y I)
  have hp2 := size_pair_le' (val b I) (Nat.pair (val x I) (val y I))
  have hcite := spaceCost_cIte (Nat.pair (val b I) (Nat.pair (val x I) (val y I)))
  have e32 : 32 * cw * Nat.size I = 32 * (cw * Nat.size I) := by ring
  have m1 : ccb * Nat.size I ≤ max (max ccb cc) (32 * cw) * Nat.size I :=
    Nat.mul_le_mul (le_trans (le_max_left _ _) (le_max_left _ _)) (le_refl _)
  have m2 : cc * Nat.size I ≤ max (max ccb cc) (32 * cw) * Nat.size I :=
    Nat.mul_le_mul (le_trans (le_max_right _ _) (le_max_left _ _)) (le_refl _)
  have m3 : 32 * cw * Nat.size I ≤ max (max ccb cc) (32 * cw) * Nat.size I :=
    Nat.mul_le_mul (le_max_right _ _) (le_refl _)
  have n1 : dcb ≤ max (max dcb dc) (32 * dw + 48) := le_trans (le_max_left _ _) (le_max_left _ _)
  have n2 : dc ≤ max (max dcb dc) (32 * dw + 48) := le_trans (le_max_right _ _) (le_max_left _ _)
  have n3 : 32 * dw + 48 ≤ max (max dcb dc) (32 * dw + 48) := le_max_right _ _
  have w1 : Nat.size (Nat.pair (val x I) (val y I)) ≤ 2 * (cw * Nat.size I + dw) := by omega
  have w2 : Nat.size (Nat.pair (val b I) (Nat.pair (val x I) (val y I)))
      ≤ 4 * (cw * Nat.size I + dw) + 2 := by omega
  have w3 : spaceCost cIte (Nat.pair (val b I) (Nat.pair (val x I) (val y I)))
      ≤ 32 * (cw * Nat.size I) + (32 * dw + 48) := by omega
  constructor
  · simp only [cSel, spaceCost_comp, spaceCost_pair, val_pair]
    omega
  · rw [val_cSel]
    split <;> omega

/-- The columns a whole selection tree sits in. The cost is thirty-two times the arms' width, the
price of the test the selection performs on the triple it forms; it does not climb with nesting. -/
abbrev treeC : ℕ := 131072
abbrev treeD : ℕ := 131120

theorem GrowBound.toTree {g : Code} (h : GrowBound g branchC branchC branchC branchC) :
    GrowBound g treeC treeD branchC branchC :=
  h.mono (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- One level of a selection tree: the conclusion re-enters as the hypothesis above it. -/
theorem growBound_selStep {b x y : Code} (hb : GrowBound b branchC branchC 0 1)
    (hx : GrowBound x treeC treeD branchC branchC)
    (hy : GrowBound y treeC treeD branchC branchC) :
    GrowBound (cSel b x y) treeC treeD branchC branchC :=
  (growBound_cSel hb hx hy).mono (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- An equality test against a small constant, on a slot that does not grow its argument. -/
theorem growBound_guard {x : Code} {ccx dcx : ℕ} (hx : GrowBound x ccx dcx 1 0)
    (hcc : ccx ≤ branchC) (hdc : dcx ≤ branchC) (j : ℕ) (hj : Nat.size j ≤ 3) :
    GrowBound (cEqK j x) branchC branchC 0 1 := by
  have hx' : GrowBound x branchC branchC 1 0 := hx.mono hcc hdc (le_refl _) (le_refl _)
  rw [cEqK]
  exact (growBound_comp (growBound_pair hx' (growBound_constCode' j 3 hj))
    growBound_cEq).mono (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem growBound_stepDescendU : GrowBound stepDescendU treeC treeD branchC branchC := by
  rw [stepDescendU]
  exact growBound_selStep (growBound_guard growBound_dC (by norm_num) (by norm_num) 0 (by decide))
    growBound_dB0.toTree
    (growBound_selStep (growBound_guard growBound_dC (by norm_num) (by norm_num) 1 (by decide))
      growBound_dB1.toTree
      (growBound_selStep (growBound_guard growBound_dC (by norm_num) (by norm_num) 2 (by decide))
        growBound_dB2.toTree
        (growBound_selStep (growBound_guard growBound_dC (by norm_num) (by norm_num) 3 (by decide))
          growBound_dB3.toTree
          (growBound_selStep
            (growBound_guard growBound_dT (by norm_num) (by norm_num) 0 (by decide))
            growBound_dBpair.toTree
            (growBound_selStep
              (growBound_guard growBound_dT (by norm_num) (by norm_num) 1 (by decide))
              growBound_dBprec.toTree
              (growBound_selStep
                (growBound_guard growBound_dT (by norm_num) (by norm_num) 2 (by decide))
                growBound_dBcomp.toTree growBound_dBrfind.toTree))))))

theorem growBound_rB3 : GrowBound rB3 treeC treeD branchC branchC := by
  rw [rB3]
  refine growBound_selStep
    (growBound_guard growBound_rPay222 (by norm_num) (by norm_num) 0 (by decide)) ?_
    growBound_rB3loop.toTree
  exact ((growBound_comp (growBound_pair growBound_rV growBound_rK)
    growBound_cRet).mono (by norm_num) (by norm_num) (by norm_num) (by norm_num)).toTree

theorem growBound_rB4 : GrowBound rB4 treeC treeD branchC branchC := by
  rw [rB4]
  refine growBound_selStep
    (growBound_guard growBound_rV (by norm_num) (by norm_num) 0 (by decide)) ?_
    growBound_rB4search.toTree
  exact ((growBound_comp (growBound_pair growBound_rPay22 growBound_rK)
    growBound_cRet).mono (by norm_num) (by norm_num) (by norm_num) (by norm_num)).toTree

theorem growBound_stepReturnU : GrowBound stepReturnU treeC treeD branchC branchC := by
  rw [stepReturnU]
  exact growBound_selStep
    (growBound_guard growBound_rTag (by norm_num) (by norm_num) 0 (by decide))
    growBound_rB0.toTree
    (growBound_selStep (growBound_guard growBound_rTag (by norm_num) (by norm_num) 1 (by decide))
      growBound_rB1.toTree
      (growBound_selStep (growBound_guard growBound_rTag (by norm_num) (by norm_num) 2 (by decide))
        growBound_rB2.toTree
        (growBound_selStep
          (growBound_guard growBound_rTag (by norm_num) (by norm_num) 3 (by decide))
          growBound_rB3
          (growBound_selStep
            (growBound_guard growBound_rTag (by norm_num) (by norm_num) 4 (by decide))
            growBound_rB4 growBound_rBdef.toTree))))

/-! ### The step

The configuration's accessors, the two arms, and the outer selection tree. -/

theorem growBound_cCfMode : GrowBound cCfMode 1 0 1 0 := by rw [cCfMode]; exact growBound_left
theorem growBound_cCfCur : GrowBound cCfCur 1 0 1 0 := by
  rw [cCfCur]; exact growBound_projComp growBound_right growBound_left
theorem growBound_cCfStk : GrowBound cCfStk 1 0 1 0 := by
  rw [cCfStk]; exact growBound_projComp growBound_right growBound_right
theorem growBound_uCur1 : GrowBound uCur1 1 0 1 0 := by
  rw [uCur1]; exact growBound_projComp growBound_cCfCur growBound_left
theorem growBound_uCur2 : GrowBound uCur2 1 0 1 0 := by
  rw [uCur2]; exact growBound_projComp growBound_cCfCur growBound_right

theorem growBound_uHead : GrowBound uHead 64 256 1 0 := by
  rw [uHead]
  exact (growBound_comp growBound_cCfStk growBound_cStkHead).mono
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem growBound_uTail : GrowBound uTail 64 256 1 0 := by
  rw [uTail]
  exact (growBound_comp growBound_cCfStk growBound_cStkTail).mono
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- The columns the whole step sits in. -/
abbrev stepC : ℕ := 524288
abbrev stepD : ℕ := 131120
abbrev stepW : ℕ := 16384
abbrev stepE : ℕ := 4096

theorem growBound_uDescend : GrowBound uDescend stepC stepD stepW stepE := by
  rw [uDescend]
  exact (growBound_comp
    (growBound_pair growBound_uCur1 (growBound_pair growBound_uCur2 growBound_cCfStk))
    growBound_stepDescendU).mono (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem growBound_uReturn : GrowBound uReturn stepC stepD stepW stepE := by
  rw [uReturn]
  exact (growBound_comp
    (growBound_pair growBound_cCfCur (growBound_pair growBound_uHead growBound_uTail))
    growBound_stepReturnU).mono (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem growBound_stepU : GrowBound stepU stepC stepD stepW stepE := by
  have hId : GrowBound cId stepC stepD stepW stepE :=
    growBound_cId.mono (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hCons : GrowBound (comp cStkIsCons cCfStk) 64 256 0 1 :=
    (growBound_comp growBound_cCfStk growBound_cStkIsCons).mono
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  rw [stepU]
  refine (growBound_cSel growBound_cIsHalt hId
    ((growBound_cSel (growBound_guard growBound_cCfMode (by norm_num) (by norm_num) 0 (by decide))
      growBound_uDescend
      ((growBound_cSel hCons growBound_uReturn hId).mono
        (by norm_num) (by norm_num) (by norm_num) (by norm_num))).mono
      (by norm_num) (by norm_num) (by norm_num) (by norm_num))).mono
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-! ## The interpreter's workspace law

**The step runs in workspace a fixed multiple of the wider of its input and its output**, with both
the multiple and the offset absolute — independent of the code being interpreted, of the input, and
of how far the run has progressed. That independence is the whole content: it is what lets a bound
on one step become a bound on a whole run.

The constants are the honest output of the walk above, and they are far larger than the individual
codes' own figures. Nothing about the interpreter demands that; it is the price of the two bounds
the method leans on. `Nat.pair` is a squaring pairing, so a pair is charged twice its wider
component, and the branches nest pairings six deep over a stack cell that is itself charged three
times its frame; a selection is then charged thirty-two times its arms' width. Those factors
multiply where the true widths would add. The figures below are upper bounds, and are not claimed
to be tight. -/

/-- **The bounded interpreter's step is workspace-bounded by an absolute constant.** -/
theorem spaceCost_stepU_le (x : ℕ) :
    spaceCost stepU x
      ≤ 524288 * max (Nat.size x) (Nat.size (BoundedInterp.stepUFn x)) + 131120 := by
  have h : spaceCost stepU x ≤ 524288 * Nat.size x + 131120 := growBound_stepU.cost x
  have hm : (524288 : ℕ) * Nat.size x
      ≤ 524288 * max (Nat.size x) (Nat.size (BoundedInterp.stepUFn x)) :=
    Nat.mul_le_mul (le_refl _) (le_max_left _ _)
  omega

/-! ### Selection

Selection is where a multiplicative bound would go badly wrong. Composing the growth laws through
the descending step's seven nested selections multiplies the coefficient seven times over, for a
figure with no bearing on what the code does.

The reason is that the laws above charge a selection as a composition, and so let its *output*
width grow with its cost. It does not: a selection returns one of its arms unchanged. Stating the
two separately — every arm inside one budget `B`, every arm's value inside one width `W` — makes
nesting free, since the conclusion is again `B` and `W`. Both arms are charged in `B`, selection
being strict; there is no laziness discount anywhere in this development. -/

/-- **A selection costs no more than its widest arm**, provided the budget covers the test the
selection itself performs on the triple it forms. -/
theorem spaceCost_cSel_bound {b x y : Code} {I B W : ℕ}
    (hb : spaceCost b I ≤ B) (hx : spaceCost x I ≤ B) (hy : spaceCost y I ≤ B)
    (hwb : Nat.size (val b I) ≤ W) (hwx : Nat.size (val x I) ≤ W) (hwy : Nat.size (val y I) ≤ W)
    (hfit : 32 * W + 32 ≤ B) :
    spaceCost (cSel b x y) I ≤ B := by
  have hp1 := size_pair_le' (val x I) (val y I)
  have hp2 := size_pair_le' (val b I) (Nat.pair (val x I) (val y I))
  rw [cSel]
  refine spaceCost_comp_bound
    (spaceCost_pair_bound hb (spaceCost_pair_bound hx hy (by omega)) ?_) ?_
  · rw [val_pair]; omega
  rw [val_pair, val_pair]
  have := spaceCost_cIte (Nat.pair (val b I) (Nat.pair (val x I) (val y I)))
  omega

/-- **A selection returns an arm unchanged**, so its output stays inside the arms' width. This is
what keeps nesting free. -/
theorem size_val_cSel_le {b x y : Code} {I W : ℕ}
    (hwx : Nat.size (val x I) ≤ W) (hwy : Nat.size (val y I) ≤ W) :
    Nat.size (val (cSel b x y) I) ≤ W := by
  rw [val_cSel]
  split <;> omega

/-! ## The run

The step's law becomes the run's. The run is the bounded recursor whose step is the interpreter's
step, so the iterate is a `prec` over a counter, starting from the initial configuration.

Two things about the shape below are worth stating plainly, because the obvious form of this
theorem is not the one that is true.

**The workspace figure is a hypothesis, not a derived quantity.** The natural reading — bound the
run by `codeDepth · (2F + 2)` for a frame width `F` read off the invariant — does not survive
contact with what the invariant says. `StackOK` charges each cell `framePend + stkDepth + 1 ≤ D`:
both summands are *depths*, and `framePend` is itself a `codeDepth`. It constrains how deeply the
machine can still descend. It says nothing whatever about `Nat.size` of any frame, and no theorem
here bounds `stkMaxFrame` along a run. Nor could one: a frame stores the values a recursion has
accumulated, and those are outputs of the computation being simulated, not functions of the code's
shape. So the width enters as a named hypothesis on the run, which is where the honest content is.

**The iteration count cannot be absent.** It appears as `Nat.size τ` — logarithmically — because
the recursor carries its own counter, and the workspace measure charges the width of every value a
node touches. What *is* absent, and is the point, is any dependence of the leading term on how far
the run has gone. -/

/-- The initial configuration, from `⟨p, x⟩`. -/
def cInit : Code := pair zero (pair cId (constCode 0))

@[simp] theorem val_cInit (p x : ℕ) :
    val cInit (Nat.pair p x) = BoundedInterp.initConfig p x := by
  rw [cInit, val_pair, val_pair, val_zero', val_cId, val_constCode,
    BoundedInterp.initConfig, BoundedInterp.descend, BoundedInterp.config]

theorem rfindFree_cInit : RfindFree cInit :=
  ⟨trivial, rfindFree_cId, rfindFree_constCode 0⟩

theorem growBound_cInit : GrowBound cInit 4 0 4 0 := by
  rw [cInit]
  exact (growBound_pair growBound_zero
    (growBound_pair growBound_cId (growBound_constCode' 0 0 (by decide)))).mono
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- **The run**: iterate the step, from the initial configuration, a stated number of times. -/
def runU : Code := prec cInit (comp stepU cAcc)

theorem rfindFree_runU : RfindFree runU := ⟨rfindFree_cInit, rfindFree_stepU, rfindFree_cAcc⟩

/-- **The run computes the mathematical layer's iterate.** -/
theorem val_runU (p x : ℕ) : ∀ τ,
    val runU (Nat.pair (Nat.pair p x) τ)
      = BoundedInterp.stepUFn^[τ] (BoundedInterp.initConfig p x) := by
  intro τ
  induction τ with
  | zero =>
      have h : val runU (Nat.pair (Nat.pair p x) 0) = val cInit (Nat.pair p x) :=
        val_prec_zero cInit (comp stepU cAcc) (Nat.pair p x)
      rw [h, val_cInit, Function.iterate_zero_apply]
  | succ j ih =>
      have h : val runU (Nat.pair (Nat.pair p x) (j + 1))
          = val (comp stepU cAcc)
              (Nat.pair (Nat.pair p x) (Nat.pair j (val runU (Nat.pair (Nat.pair p x) j)))) :=
        val_prec_succ cInit (comp stepU cAcc) (Nat.pair p x) j
      rw [h, val_comp, val_cAcc, ih, val_stepU, Function.iterate_succ_apply']

/-- **The run's workspace is bounded by the step's constant times the widest configuration it
passes through**, plus the width of the argument and of the counter — with no dependence of the
leading term on how many steps were taken.

`W` is the run's own width bound, supplied as a hypothesis for the reason given above: nothing in
the invariant bounds a frame's *width*, only how deep the machine may still descend.

The constants are inherited from the step's law and carry its looseness; they are upper bounds and
are not claimed to be tight. -/
theorem spaceCost_runU_le (p x W : ℕ) : ∀ τ,
    (∀ σ, σ ≤ τ →
      Nat.size (BoundedInterp.stepUFn^[σ] (BoundedInterp.initConfig p x)) ≤ W) →
    spaceCost runU (Nat.pair (Nat.pair p x) τ)
      ≤ 524288 * W + 131120 + 4 * Nat.size (Nat.pair p x) + 4 * Nat.size τ + 4 * W := by
  intro τ
  induction τ with
  | zero =>
      intro _
      have h : spaceCost runU (Nat.pair (Nat.pair p x) 0) = spaceCost cInit (Nat.pair p x) :=
        spaceCost_prec_zero cInit (comp stepU cAcc) (Nat.pair p x)
      have hc : spaceCost cInit (Nat.pair p x) ≤ 4 * Nat.size (Nat.pair p x) + 0 :=
        growBound_cInit.cost (Nat.pair p x)
      omega
  | succ j ih =>
      intro hW
      have h : spaceCost runU (Nat.pair (Nat.pair p x) (j + 1))
          = max (spaceCost runU (Nat.pair (Nat.pair p x) j))
              (spaceCost (comp stepU cAcc)
                (Nat.pair (Nat.pair p x)
                  (Nat.pair j (val runU (Nat.pair (Nat.pair p x) j))))) :=
        spaceCost_prec_succ cInit (comp stepU cAcc) (Nat.pair p x) j
      have hprev : val runU (Nat.pair (Nat.pair p x) j)
          = BoundedInterp.stepUFn^[j] (BoundedInterp.initConfig p x) := val_runU p x j
      have hpw : Nat.size (BoundedInterp.stepUFn^[j] (BoundedInterp.initConfig p x)) ≤ W :=
        hW j (Nat.le_succ j)
      -- the step, at the configuration actually reached
      have hstep : spaceCost stepU
          (BoundedInterp.stepUFn^[j] (BoundedInterp.initConfig p x))
            ≤ 524288 * W + 131120 := by
        have hs : spaceCost stepU
            (BoundedInterp.stepUFn^[j] (BoundedInterp.initConfig p x))
              ≤ 524288 * Nat.size
                  (BoundedInterp.stepUFn^[j] (BoundedInterp.initConfig p x)) + 131120 :=
          growBound_stepU.cost _
        have hm : (524288 : ℕ) * Nat.size
            (BoundedInterp.stepUFn^[j] (BoundedInterp.initConfig p x)) ≤ 524288 * W :=
          Nat.mul_le_mul (le_refl _) hpw
        omega
      -- the recursor's own spine: the argument, the counter and the accumulator
      have hspine : Nat.size (Nat.pair (Nat.pair p x)
          (Nat.pair j (BoundedInterp.stepUFn^[j] (BoundedInterp.initConfig p x))))
            ≤ 4 * Nat.size (Nat.pair p x) + 4 * Nat.size j + 4 * W := by
        have h1 := size_pair_le' (Nat.pair p x)
          (Nat.pair j (BoundedInterp.stepUFn^[j] (BoundedInterp.initConfig p x)))
        have h2 := size_pair_le' j
          (BoundedInterp.stepUFn^[j] (BoundedInterp.initConfig p x))
        omega
      have hcomp : spaceCost (comp stepU cAcc)
          (Nat.pair (Nat.pair p x)
            (Nat.pair j (val runU (Nat.pair (Nat.pair p x) j))))
            ≤ 524288 * W + 131120 + 4 * Nat.size (Nat.pair p x)
              + 4 * Nat.size (j + 1) + 4 * W := by
        rw [spaceCost_comp, hprev, spaceCost_cAcc, val_cAcc]
        have hmono : Nat.size j ≤ Nat.size (j + 1) := Nat.size_le_size (Nat.le_succ j)
        omega
      have hih := ih (fun σ hσ => hW σ (le_trans hσ (Nat.le_succ j)))
      have hmono : Nat.size j ≤ Nat.size (j + 1) := Nat.size_le_size (Nat.le_succ j)
      omega

end CodePacking
