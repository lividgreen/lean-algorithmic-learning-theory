import Mathlib
import ALT.PolyTime
import ALT.DecisionListData

-- Tier-1 formal check, not Mathlib-destined: opt out of the house-style linters.
set_option linter.style.header false
set_option linter.style.longLine false

/-!
# Inner scan primitives of the greedy 1-DL consistency solver (F20 Stage C2b)

Provenance: the native-cost-model workstream, stage C2b. Builds on `ALT/DecisionListData.lean` (the C2a data layer:
`readM`/`readK`, `peel`/`cPeel`, `headL`/`tailL`, `WF`, `readM_le_size`/`readK_le_size`,
`encodeList`, `peel_encode`) and `ALT/PolyTime.lean` (`PolyTime`, `PolyBounded`, `polyTime_loop`,
`tc_prec_le'`, the closure toolkit).
-/

namespace OneDL

open Nat.Partrec (Code)
open Nat.Partrec.Code
open TimeCost

/-! ## Layer 1 — a native bit-logic gate library

**The finding that forces this.** The native `tc` charges 1 per AST unfolding and every `prec` runs
its full iteration count, so any VALUE-arithmetic on a magnitude-`v` operand costs Θ(v) — value-linear,
NOT poly-bit (the same wall as `cPred`). In particular the scan cannot compare general-`ℕ` labels for
equality in poly-time. We therefore work in the **binary 1-DL setting** (features and labels ∈ {0,1})
and compute with bit-logic gates whose recursion variable is a bit, so each gate is `O(1)`-`tc` on
bits. Every gate below is **bit-closed**: its `val` is always `0` or `1`, whatever the input. Each gate
gets a `val` law and a `tc` bound linear in the input value (hence `O(1)` on bits). The `tc` bounds use
the uniform `tc_prec_le` — `tc_prec_le'` (visited-states-only) is needed only at the outer scan loop. -/

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
  ⟨rfindFree_cOr, rfindFree_cAnd, ⟨rfindFree_cAnd, ⟨rfindFree_cNot, trivial⟩, ⟨rfindFree_cNot, trivial⟩⟩⟩

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

/-! ### Gate `tc`-on-bits bricks (reusable by findLit/maskUpdate)

On bit operands every gate runs a constant number of steps: the `prec`-based gates unfold `≤ 1` times,
the De-Morgan compositions are `prec`-free. -/

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

/-! ## Layer 2 — the purity scan `cPurity`

`purity inst mask j p` scans the `m` examples; over the still-remaining (mask bit `= 1`) examples
that satisfy literal `(j, p)` (feature `j` equals `p`) it decides whether all their labels agree,
returning `⟨isPure, commonLabel⟩`. To avoid value-arithmetic (label equality is value-linear), it
tracks two bits over the covered examples: `sawZero` (some covered example is labelled `0`) and
`sawOne` (some covered example is labelled `1`); then `isPure = ¬(sawZero ∧ sawOne)` and
`commonLabel = sawOne`. Realized as a carried-suffix `prec` loop over `i < readM inst`. -/

/-! ### The semantic bit-ops (mirror the gate `val` laws) and example accessors -/

/-- `¬` on a bit — mirrors `val_cNot`. -/
def bNot (n : ℕ) : ℕ := if n = 0 then 1 else 0
/-- `∧` on bits — mirrors `val_cAnd`. -/
def bAnd (a b : ℕ) : ℕ := if a = 0 then 0 else (if b = 0 then 0 else 1)
/-- `∨` on bits — mirrors `val_cOr`. -/
def bOr (a b : ℕ) : ℕ := if a = 0 then (if b = 0 then 0 else 1) else 1
/-- bit-equality — mirrors `val_cEqBit`. -/
def bEq (a b : ℕ) : ℕ := if a = 0 then (if b = 0 then 1 else 0) else (if b = 0 then 0 else 1)

theorem bNot_le_one (n : ℕ) : bNot n ≤ 1 := by unfold bNot; split <;> simp
theorem bAnd_le_one (a b : ℕ) : bAnd a b ≤ 1 := by unfold bAnd; split <;> [simp; split <;> simp]
theorem bOr_le_one (a b : ℕ) : bOr a b ≤ 1 := by unfold bOr; split <;> [split <;> simp; simp]
theorem bEq_le_one (a b : ℕ) : bEq a b ≤ 1 := by
  unfold bEq; split <;> split <;> simp

/-- The label of an example `e = ⟨label, fv⟩`. -/
def lblOf (e : ℕ) : ℕ := e.unpair.1
/-- The feature-vector of an example. -/
def fvOf (e : ℕ) : ℕ := e.unpair.2
/-- Feature `j` of example `e`: peel its feature-vector `j` cells and read the head bit. -/
def featOf (e j : ℕ) : ℕ := headL (peel (fvOf e) j)

/-! ### Reads as `Code`s -/

/-- `headL` as a `Code` (`comp left right`). -/
def cHead : Code := comp left right
/-- `tailL` as a `Code` (`comp right right`). -/
def cTail : Code := comp right right

theorem rfindFree_cHead : RfindFree cHead := ⟨trivial, trivial⟩
theorem rfindFree_cTail : RfindFree cTail := ⟨trivial, trivial⟩
theorem val_cHead (L : ℕ) : val cHead L = headL L := by
  simp only [cHead, val_comp, val_left, val_right, headL]
theorem val_cTail (L : ℕ) : val cTail L = tailL L := by
  simp only [cTail, val_comp, val_right, tailL]
theorem tc_cHead (L : ℕ) : tc cHead L = 3 := by simp only [cHead, tc_comp, tc_left, tc_right]
theorem tc_cTail (L : ℕ) : tc cTail L = 3 := by simp only [cTail, tc_comp, tc_right]

/-! ### The packed input and its projections

`n = ⟨inst, ⟨mask, ⟨j, p⟩⟩⟩`. -/

def instOf (n : ℕ) : ℕ := n.unpair.1
def maskOf (n : ℕ) : ℕ := n.unpair.2.unpair.1
def jOf (n : ℕ) : ℕ := n.unpair.2.unpair.2.unpair.1
def pOf (n : ℕ) : ℕ := n.unpair.2.unpair.2.unpair.2

/-- `readData (instOf n)` — the example list of the packed input. -/
def dataOf (n : ℕ) : ℕ := readData (instOf n)

def cInst : Code := left
def cMask : Code := comp left right
def cJ : Code := comp left (comp right right)
def cP : Code := comp right (comp right right)
def cData : Code := comp (comp right right) left

theorem val_cInst (n : ℕ) : val cInst n = instOf n := by simp only [cInst, val_left, instOf]
theorem val_cMask (n : ℕ) : val cMask n = maskOf n := by
  simp only [cMask, val_comp, val_left, val_right, maskOf]
theorem val_cJ (n : ℕ) : val cJ n = jOf n := by
  simp only [cJ, val_comp, val_left, val_right, jOf]
theorem val_cP (n : ℕ) : val cP n = pOf n := by
  simp only [cP, val_comp, val_right, pOf]
theorem val_cData (n : ℕ) : val cData n = dataOf n := by
  simp only [cData, val_comp, val_left, val_right, dataOf, readData, instOf]

/-! ### The accumulator `⟨maskSuf, ⟨exSuf, ⟨sawZero, sawOne⟩⟩⟩` and the initial-state code -/

def msOf (acc : ℕ) : ℕ := acc.unpair.1
def exOf (acc : ℕ) : ℕ := acc.unpair.2.unpair.1
def z0Of (acc : ℕ) : ℕ := acc.unpair.2.unpair.2.unpair.1
def z1Of (acc : ℕ) : ℕ := acc.unpair.2.unpair.2.unpair.2

/-- The initial accumulator: full suffixes, both flags `0`. -/
def initAcc (mask data : ℕ) : ℕ := Nat.pair mask (Nat.pair data (Nat.pair 0 0))

/-- The base code: build `initAcc (maskOf n) (dataOf n)` from the packed input. -/
def cInit : Code := pair cMask (pair cData (pair zero zero))

theorem rfindFree_cInit : RfindFree cInit :=
  ⟨⟨trivial, trivial⟩, ⟨⟨⟨trivial, trivial⟩, trivial⟩, ⟨trivial, trivial⟩⟩⟩

theorem val_cInit (n : ℕ) : val cInit n = initAcc (maskOf n) (dataOf n) := by
  simp only [cInit, val_pair, val_cMask, val_cData, val_zero, initAcc]

/-! ### The step code `cStep` and its `val` law

Gate `val` laws restated with the semantic bit-ops (definitional folds) so the step `val` lands in
`stepFn` form. The step input is `X = ⟨a, ⟨i, acc⟩⟩`; the seed `a` carries `j, p`, and `i` is unused
(carried-suffix scan — the current cell is the head of the carried suffix). -/

theorem val_cNot' (n : ℕ) : val cNot n = bNot n := val_cNot n
theorem val_cAnd' (a b : ℕ) : val cAnd (Nat.pair a b) = bAnd a b := val_cAnd a b
theorem val_cOr' (a b : ℕ) : val cOr (Nat.pair a b) = bOr a b := val_cOr a b
theorem val_cEqBit' (a b : ℕ) : val cEqBit (Nat.pair a b) = bEq a b := val_cEqBit a b

def cAcc : Code := comp right right
def cJa : Code := comp cJ left
def cPa : Code := comp cP left
def cMs : Code := comp left cAcc
def cEx : Code := comp left (comp right cAcc)
def cZ0 : Code := comp left (comp right (comp right cAcc))
def cZ1 : Code := comp right (comp right (comp right cAcc))
def cB : Code := comp cHead cMs
def cE : Code := comp cHead cEx
def cLbl : Code := comp left cE
def cFv : Code := comp right cE
def cFeat : Code := comp cHead (comp cPeel (pair cFv cJa))
def cEqFP : Code := comp cEqBit (pair cFeat cPa)
def cCov : Code := comp cAnd (pair cB cEqFP)
def cNotLbl : Code := comp cNot cLbl
def cZ0' : Code := comp cOr (pair cZ0 (comp cAnd (pair cCov cNotLbl)))
def cZ1' : Code := comp cOr (pair cZ1 (comp cAnd (pair cCov cLbl)))
def cStep : Code := pair (comp cTail cMs) (pair (comp cTail cEx) (pair cZ0' cZ1'))

/-- The semantic step: read the head bit / head example off the carried suffixes, test coverage
(remaining ∧ satisfies `(j,p)`), fold the covered example's label into `sawZero`/`sawOne`, and peel
both suffixes one cell. Independent of the loop index. -/
def stepFn (j p acc : ℕ) : ℕ :=
  Nat.pair (tailL (msOf acc))
    (Nat.pair (tailL (exOf acc))
      (Nat.pair
        (bOr (z0Of acc)
          (bAnd (bAnd (headL (msOf acc)) (bEq (featOf (headL (exOf acc)) j) p))
            (bNot (lblOf (headL (exOf acc))))))
        (bOr (z1Of acc)
          (bAnd (bAnd (headL (msOf acc)) (bEq (featOf (headL (exOf acc)) j) p))
            (lblOf (headL (exOf acc)))))))

theorem val_cStep (a i acc : ℕ) :
    val cStep (Nat.pair a (Nat.pair i acc)) = stepFn (jOf a) (pOf a) acc := by
  simp only [cStep, cZ0', cZ1', cCov, cNotLbl, cB, cEqFP, cFeat, cFv, cE, cLbl, cEx, cMs, cZ0, cZ1,
    cAcc, cJa, cPa, val_pair, val_comp, val_left, val_right, val_cHead, val_cTail, val_cPeel,
    val_cNot', val_cAnd', val_cOr', val_cEqBit', val_cJ, val_cP, Nat.unpair_pair,
    stepFn, msOf, exOf, z0Of, z1Of, lblOf, fvOf, featOf]

/-- **Loop = iterated step.** The `prec` loop iterates the semantic step `t` times from `initAcc`. -/
theorem val_cLoop (n t : ℕ) :
    val (prec cInit cStep) (Nat.pair n t)
      = (stepFn (jOf n) (pOf n))^[t] (initAcc (maskOf n) (dataOf n)) := by
  induction t with
  | zero => rw [val_prec_zero, val_cInit, Function.iterate_zero_apply]
  | succ k ih => rw [val_prec_succ, val_cStep, ih, Function.iterate_succ_apply']

/-! ### The `List`-model fold and the scan characterisation -/

/-- One covered-label fold step on `(sawZero, sawOne)` for a `(maskBit, example)` pair. -/
def stepPair (j p : ℕ) (z : ℕ × ℕ) (be : ℕ × ℕ) : ℕ × ℕ :=
  (bOr z.1 (bAnd (bAnd be.1 (bEq (featOf be.2 j) p)) (bNot (lblOf be.2))),
   bOr z.2 (bAnd (bAnd be.1 (bEq (featOf be.2 j) p)) (lblOf be.2)))

/-- **The scan realises the `List` fold.** Running the semantic step over the encoded mask/example
lists (equal length) for `exs.length` iterations from `⟨mask, data, z0, z1⟩` empties both suffixes and
`foldl`s `stepPair` over `zip msks exs`. -/
theorem stepFn_iterate (j p : ℕ) (exs : List ℕ) :
    ∀ (msks : List ℕ) (z0 z1 : ℕ), msks.length = exs.length →
      (stepFn j p)^[exs.length]
          (Nat.pair (encodeList msks) (Nat.pair (encodeList exs) (Nat.pair z0 z1)))
        = Nat.pair 0 (Nat.pair 0 (Nat.pair
            ((msks.zip exs).foldl (stepPair j p) (z0, z1)).1
            ((msks.zip exs).foldl (stepPair j p) (z0, z1)).2)) := by
  induction exs with
  | nil =>
      intro msks z0 z1 hlen
      have hm : msks = [] := List.length_eq_zero_iff.mp (by simpa using hlen)
      subst hm
      simp [encodeList, List.zip_nil_right]
  | cons e es ih =>
      intro msks z0 z1 hlen
      cases msks with
      | nil => simp at hlen
      | cons mb mbs =>
          have hlen' : mbs.length = es.length := by simpa using hlen
          rw [List.length_cons, Function.iterate_succ_apply]
          have hx : stepFn j p
              (Nat.pair (encodeList (mb :: mbs))
                (Nat.pair (encodeList (e :: es)) (Nat.pair z0 z1)))
              = Nat.pair (encodeList mbs) (Nat.pair (encodeList es)
                  (Nat.pair (stepPair j p (z0, z1) (mb, e)).1 (stepPair j p (z0, z1) (mb, e)).2)) := by
            simp only [stepFn, msOf, exOf, z0Of, z1Of, Nat.unpair_pair, headL_encode_cons,
              tailL_encode_cons, stepPair]
          rw [hx, ih mbs _ _ hlen', List.zip_cons_cons, List.foldl_cons]

/-! ### Characterising the fold: `sawZero`/`sawOne` as coverage existentials -/

theorem bOr_ne_zero (a b : ℕ) : bOr a b ≠ 0 ↔ a ≠ 0 ∨ b ≠ 0 := by
  unfold bOr; by_cases ha : a = 0 <;> by_cases hb : b = 0 <;> simp [ha, hb]
theorem bAnd_ne_zero (a b : ℕ) : bAnd a b ≠ 0 ↔ a ≠ 0 ∧ b ≠ 0 := by
  unfold bAnd; by_cases ha : a = 0 <;> by_cases hb : b = 0 <;> simp [ha, hb]
theorem bNot_ne_zero (n : ℕ) : bNot n ≠ 0 ↔ n = 0 := by
  unfold bNot; by_cases h : n = 0 <;> simp [h]
theorem bAnd_eq_zero (a b : ℕ) : bAnd a b = 0 ↔ a = 0 ∨ b = 0 := by
  unfold bAnd; by_cases ha : a = 0 <;> by_cases hb : b = 0 <;> simp [ha, hb]
theorem bAnd_le_left (a b : ℕ) : bAnd a b ≤ a := by unfold bAnd; split_ifs <;> omega

/-- Split a componentwise pair `foldl` into two independent scalar `foldl`s. -/
theorem foldl_pair {α : Type*} (F G : α → ℕ → ℕ) (l : List α) (a b : ℕ) :
    (l.foldl (fun z x => (F x z.1, G x z.2)) (a, b))
      = (l.foldl (fun y x => F x y) a, l.foldl (fun y x => G x y) b) := by
  induction l generalizing a b with
  | nil => rfl
  | cons x xs ih => simp only [List.foldl_cons]; exact ih _ _

/-- A `bOr`-accumulating `foldl` is nonzero iff the seed is, or some element fires. -/
theorem orFold_ne_zero {α : Type*} (f : α → ℕ) (l : List α) (init : ℕ) :
    (l.foldl (fun y x => bOr y (f x)) init) ≠ 0 ↔ init ≠ 0 ∨ ∃ x ∈ l, f x ≠ 0 := by
  induction l generalizing init with
  | nil => simp
  | cons x xs ih =>
      rw [List.foldl_cons, ih, bOr_ne_zero]
      simp only [List.mem_cons, exists_eq_or_imp]
      tauto

/-- The `sawZero` (`.1`) and `sawOne` (`.2`) components of the fold, as independent `bOr`-folds. -/
theorem foldZ_fst (j p : ℕ) (l : List (ℕ × ℕ)) (z0 z1 : ℕ) :
    (l.foldl (stepPair j p) (z0, z1)).1
      = l.foldl (fun y be => bOr y
          (bAnd (bAnd be.1 (bEq (featOf be.2 j) p)) (bNot (lblOf be.2)))) z0 :=
  congrArg Prod.fst
    (foldl_pair (fun (be : ℕ × ℕ) a => bOr a (bAnd (bAnd be.1 (bEq (featOf be.2 j) p)) (bNot (lblOf be.2))))
                (fun (be : ℕ × ℕ) a => bOr a (bAnd (bAnd be.1 (bEq (featOf be.2 j) p)) (lblOf be.2))) l z0 z1)

theorem foldZ_snd (j p : ℕ) (l : List (ℕ × ℕ)) (z0 z1 : ℕ) :
    (l.foldl (stepPair j p) (z0, z1)).2
      = l.foldl (fun y be => bOr y
          (bAnd (bAnd be.1 (bEq (featOf be.2 j) p)) (lblOf be.2))) z1 :=
  congrArg Prod.snd
    (foldl_pair (fun (be : ℕ × ℕ) a => bOr a (bAnd (bAnd be.1 (bEq (featOf be.2 j) p)) (bNot (lblOf be.2))))
                (fun (be : ℕ × ℕ) a => bOr a (bAnd (bAnd be.1 (bEq (featOf be.2 j) p)) (lblOf be.2))) l z0 z1)

/-- A `(maskBit, example)` pair is **covered** by literal `(j,p)`: still remaining and the gate accepts
its feature-`j` bit against `p`. -/
def Covered (j p : ℕ) (be : ℕ × ℕ) : Prop := be.1 ≠ 0 ∧ bEq (featOf be.2 j) p ≠ 0

/-- **`sawOne` characterisation.** The `.2` flag fires iff some covered pair carries a nonzero label. -/
theorem sawOne_iff (j p : ℕ) (l : List (ℕ × ℕ)) :
    (l.foldl (stepPair j p) (0, 0)).2 ≠ 0 ↔ ∃ be ∈ l, Covered j p be ∧ lblOf be.2 ≠ 0 := by
  rw [foldZ_snd, orFold_ne_zero]
  simp only [bAnd_ne_zero, Covered]
  constructor
  · rintro (h | h)
    · exact absurd rfl h
    · exact h
  · exact fun h => Or.inr h

/-- **`sawZero` characterisation.** The `.1` flag fires iff some covered pair carries a zero label. -/
theorem sawZero_iff (j p : ℕ) (l : List (ℕ × ℕ)) :
    (l.foldl (stepPair j p) (0, 0)).1 ≠ 0 ↔ ∃ be ∈ l, Covered j p be ∧ lblOf be.2 = 0 := by
  rw [foldZ_fst, orFold_ne_zero]
  simp only [bAnd_ne_zero, bNot_ne_zero, Covered]
  constructor
  · rintro (h | h)
    · exact absurd rfl h
    · exact h
  · exact fun h => Or.inr h

/-! ### The assembled purity code and its correctness -/

/-- Extract `⟨isPure, ⟨commonLabel, sawAny⟩⟩ = ⟨¬(sawZero ∧ sawOne), ⟨sawOne, sawZero ∨ sawOne⟩⟩`
from the final accumulator. The third field `sawAny` witnesses that ≥1 remaining example is covered —
so the greedy loop can reject vacuously-pure (0-covering) literals (`findLit` gates on `isPure ∧
sawAny`). -/
def cZ0acc : Code := comp left (comp right right)
def cZ1acc : Code := comp right (comp right right)
def cSawAny : Code := comp cOr (pair cZ0acc cZ1acc)
def cFinal : Code := pair (comp cNot (comp cAnd (pair cZ0acc cZ1acc))) (pair cZ1acc cSawAny)
/-- Identity shaper (the loop seed is the whole packed input). -/
def cId : Code := pair left right
/-- The iteration count `readM (instOf n)` — the number of examples. -/
def cCount : Code := comp cReadM cInst
/-- **The purity primitive** `cPurity`: run the scan `readM inst` times, then read out the verdict. -/
def cPurity : Code := comp cFinal (comp (prec cInit cStep) (pair cId cCount))

theorem val_cFinal (acc : ℕ) :
    val cFinal acc = Nat.pair (bNot (bAnd (z0Of acc) (z1Of acc)))
      (Nat.pair (z1Of acc) (bOr (z0Of acc) (z1Of acc))) := by
  simp only [cFinal, cSawAny, cZ0acc, cZ1acc, val_pair, val_comp, val_left, val_right, val_cNot',
    val_cAnd', val_cOr', z0Of, z1Of]
theorem val_cId (n : ℕ) : val cId n = n := by
  simp only [cId, val_pair, val_left, val_right, Nat.pair_unpair]
theorem val_cCount (n : ℕ) : val cCount n = readM (instOf n) := by
  simp only [cCount, val_comp, val_cReadM, val_cInst]

/-- The final accumulator after the full scan. -/
def purityAcc (n : ℕ) : ℕ :=
  (stepFn (jOf n) (pOf n))^[readM (instOf n)] (initAcc (maskOf n) (dataOf n))
/-- The purity verdict `⟨isPure, ⟨commonLabel, sawAny⟩⟩`. -/
def purityVal (n : ℕ) : ℕ :=
  Nat.pair (bNot (bAnd (z0Of (purityAcc n)) (z1Of (purityAcc n))))
    (Nat.pair (z1Of (purityAcc n)) (bOr (z0Of (purityAcc n)) (z1Of (purityAcc n))))

theorem val_cPurity (n : ℕ) : val cPurity n = purityVal n := by
  rw [cPurity, val_comp, val_comp, val_pair, val_cId, val_cCount, val_cLoop, val_cFinal]
  rfl

/-- **Purity correctness (fold form).** On encoded inputs the primitive returns
`⟨¬(sawZero ∧ sawOne), sawOne⟩`, the covered-label fold over `zip msks exs`. -/
theorem purity_correct (n : ℕ) (msks exs : List ℕ)
    (hmask : maskOf n = encodeList msks) (hdata : dataOf n = encodeList exs)
    (hcount : readM (instOf n) = exs.length) (hlen : msks.length = exs.length) :
    purityVal n
      = Nat.pair
          (bNot (bAnd ((msks.zip exs).foldl (stepPair (jOf n) (pOf n)) (0, 0)).1
                      ((msks.zip exs).foldl (stepPair (jOf n) (pOf n)) (0, 0)).2))
          (Nat.pair ((msks.zip exs).foldl (stepPair (jOf n) (pOf n)) (0, 0)).2
            (bOr ((msks.zip exs).foldl (stepPair (jOf n) (pOf n)) (0, 0)).1
                 ((msks.zip exs).foldl (stepPair (jOf n) (pOf n)) (0, 0)).2)) := by
  simp only [purityVal, purityAcc, hcount, hmask, hdata, initAcc]
  rw [stepFn_iterate (jOf n) (pOf n) exs msks 0 0 hlen]
  simp only [z0Of, z1Of, Nat.unpair_pair]

/-- **`isPure` characterisation.** The verdict's first field is set iff NOT both a covered `0`-label
and a covered `1`-label occur — i.e. iff all covered examples share a label (binary regime). -/
theorem purity_isPure_iff (n : ℕ) (msks exs : List ℕ)
    (hmask : maskOf n = encodeList msks) (hdata : dataOf n = encodeList exs)
    (hcount : readM (instOf n) = exs.length) (hlen : msks.length = exs.length) :
    (purityVal n).unpair.1 ≠ 0
      ↔ ¬((∃ be ∈ msks.zip exs, Covered (jOf n) (pOf n) be ∧ lblOf be.2 = 0)
          ∧ (∃ be ∈ msks.zip exs, Covered (jOf n) (pOf n) be ∧ lblOf be.2 ≠ 0)) := by
  rw [purity_correct n msks exs hmask hdata hcount hlen, Nat.unpair_pair, bNot_ne_zero,
    bAnd_eq_zero, ← sawZero_iff, ← sawOne_iff]
  tauto

/-- **`commonLabel` read-out.** The verdict's second field (`.2.1`) is `sawOne`, which fires iff some
covered example carries a nonzero (i.e. `1`, in the binary regime) label. -/
theorem purity_commonLabel (n : ℕ) (msks exs : List ℕ)
    (hmask : maskOf n = encodeList msks) (hdata : dataOf n = encodeList exs)
    (hcount : readM (instOf n) = exs.length) (hlen : msks.length = exs.length) :
    (purityVal n).unpair.2.unpair.1 ≠ 0
      ↔ ∃ be ∈ msks.zip exs, Covered (jOf n) (pOf n) be ∧ lblOf be.2 ≠ 0 := by
  rw [purity_correct n msks exs hmask hdata hcount hlen]
  simp only [Nat.unpair_pair]
  rw [← sawOne_iff]

/-- **`sawAny` read-out.** The verdict's third field (`.2.2`) is `sawZero ∨ sawOne`, which fires iff the
literal `(jOf n, pOf n)` **covers ≥1 remaining example** — the covering witness the greedy loop needs to
reject vacuously-pure literals. -/
theorem purity_sawAny (n : ℕ) (msks exs : List ℕ)
    (hmask : maskOf n = encodeList msks) (hdata : dataOf n = encodeList exs)
    (hcount : readM (instOf n) = exs.length) (hlen : msks.length = exs.length) :
    (purityVal n).unpair.2.unpair.2 ≠ 0
      ↔ ∃ be ∈ msks.zip exs, Covered (jOf n) (pOf n) be := by
  rw [purity_correct n msks exs hmask hdata hcount hlen]
  simp only [Nat.unpair_pair]
  rw [bOr_ne_zero, sawZero_iff, sawOne_iff]
  constructor
  · rintro (⟨be, hbe, hc, _⟩ | ⟨be, hbe, hc, _⟩) <;> exact ⟨be, hbe, hc⟩
  · rintro ⟨be, hbe, hc⟩
    by_cases hl : lblOf be.2 = 0
    · exact Or.inl ⟨be, hbe, hc, hl⟩
    · exact Or.inr ⟨be, hbe, hc, hl⟩

/-! ## Layer 3 — `cPurity` is `PolyTime` (WF/bit-conditional)

The step-cost bound needs, at each visited example, that the mask bit, the read feature bit, and the
label are `≤ 1` (the binary-1-DL regime), plus `p ≤ 1`; the flags `sawZero`/`sawOne` are `≤ 1` by the
accumulator invariant. Then every gate is `O(1)` and the only value-scaling cost is the feature peel,
`O(jOf n)`. The count `readM (instOf n)` and the index `jOf n` are poly-bit only under well-formedness,
threaded here as `PolyBounded` hypotheses (exactly the `polyTime_peel` pattern). -/

/-! ### Accumulator-shape invariants -/

theorem msOf_stepFn (j p acc : ℕ) : msOf (stepFn j p acc) = tailL (msOf acc) := by
  simp only [stepFn, msOf, Nat.unpair_pair]
theorem exOf_stepFn (j p acc : ℕ) : exOf (stepFn j p acc) = tailL (exOf acc) := by
  simp only [stepFn, exOf, Nat.unpair_pair]
theorem z0Of_stepFn_le_one (j p acc : ℕ) : z0Of (stepFn j p acc) ≤ 1 := by
  simp only [stepFn, z0Of, Nat.unpair_pair]; exact bOr_le_one _ _
theorem z1Of_stepFn_le_one (j p acc : ℕ) : z1Of (stepFn j p acc) ≤ 1 := by
  simp only [stepFn, z1Of, Nat.unpair_pair]; exact bOr_le_one _ _

theorem inv_msOf_le (j p mask data : ℕ) : ∀ t,
    msOf ((stepFn j p)^[t] (initAcc mask data)) ≤ mask := by
  intro t
  induction t with
  | zero => simp only [Function.iterate_zero_apply, initAcc, msOf, Nat.unpair_pair]; exact le_refl _
  | succ k ih => rw [Function.iterate_succ_apply', msOf_stepFn]; exact le_trans (tailL_le _) ih
theorem inv_exOf_le (j p mask data : ℕ) : ∀ t,
    exOf ((stepFn j p)^[t] (initAcc mask data)) ≤ data := by
  intro t
  induction t with
  | zero => simp only [Function.iterate_zero_apply, initAcc, exOf, Nat.unpair_pair]; exact le_refl _
  | succ k ih => rw [Function.iterate_succ_apply', exOf_stepFn]; exact le_trans (tailL_le _) ih
theorem inv_z0_le_one (j p mask data t : ℕ) :
    z0Of ((stepFn j p)^[t] (initAcc mask data)) ≤ 1 := by
  cases t with
  | zero => simp only [Function.iterate_zero_apply, initAcc, z0Of, Nat.unpair_pair]; omega
  | succ k => rw [Function.iterate_succ_apply']; exact z0Of_stepFn_le_one _ _ _
theorem inv_z1_le_one (j p mask data t : ℕ) :
    z1Of ((stepFn j p)^[t] (initAcc mask data)) ≤ 1 := by
  cases t with
  | zero => simp only [Function.iterate_zero_apply, initAcc, z1Of, Nat.unpair_pair]; omega
  | succ k => rw [Function.iterate_succ_apply']; exact z1Of_stepFn_le_one _ _ _

/-! ### `rfind'`-freeness of the step code -/

theorem rfindFree_cStep : RfindFree cStep := by
  simp only [cStep, cZ0', cZ1', cCov, cNotLbl, cB, cEqFP, cFeat, cFv, cE, cLbl, cEx, cMs, cZ0, cZ1,
    cAcc, cJa, cPa, cJ, cP, cHead, cTail, cAnd, cOr, cNot, cEqBit, cIsPos, cShape0, cSwap,
    isPosCore, notCore, orCore, cPeel, cTailStep, constCode, RfindFree, and_self]

/-! ### Per-step cost bound (discharging `hstep`)

Sub-code `val` laws at the step input `X = ⟨a, ⟨i, acc⟩⟩` (canonical reads), a `tc` bound for the
feature peel, then bottom-up `tc` bounds culminating in `tc_cStep_le`: under bit operands every gate is
`O(1)` and the only scaling cost is the feature peel to index `jOf a`. -/

theorem vs_cAcc (a i acc : ℕ) : val cAcc (Nat.pair a (Nat.pair i acc)) = acc := by
  simp only [cAcc, val_comp, val_right, Nat.unpair_pair]
theorem vs_cMs (a i acc : ℕ) : val cMs (Nat.pair a (Nat.pair i acc)) = msOf acc := by
  simp only [cMs, cAcc, val_comp, val_left, val_right, Nat.unpair_pair, msOf]
theorem vs_cEx (a i acc : ℕ) : val cEx (Nat.pair a (Nat.pair i acc)) = exOf acc := by
  simp only [cEx, cAcc, val_comp, val_left, val_right, Nat.unpair_pair, exOf]
theorem vs_cZ0 (a i acc : ℕ) : val cZ0 (Nat.pair a (Nat.pair i acc)) = z0Of acc := by
  simp only [cZ0, cAcc, val_comp, val_left, val_right, Nat.unpair_pair, z0Of]
theorem vs_cZ1 (a i acc : ℕ) : val cZ1 (Nat.pair a (Nat.pair i acc)) = z1Of acc := by
  simp only [cZ1, cAcc, val_comp, val_right, Nat.unpair_pair, z1Of]
theorem vs_cJa (a i acc : ℕ) : val cJa (Nat.pair a (Nat.pair i acc)) = jOf a := by
  simp only [cJa, cJ, val_comp, val_left, val_right, Nat.unpair_pair, jOf]
theorem vs_cPa (a i acc : ℕ) : val cPa (Nat.pair a (Nat.pair i acc)) = pOf a := by
  simp only [cPa, cP, val_comp, val_left, val_right, Nat.unpair_pair, pOf]
theorem vs_cB (a i acc : ℕ) : val cB (Nat.pair a (Nat.pair i acc)) = headL (msOf acc) := by
  simp only [cB, cMs, cAcc, val_comp, val_cHead, val_left, val_right, Nat.unpair_pair, msOf]
theorem vs_cE (a i acc : ℕ) : val cE (Nat.pair a (Nat.pair i acc)) = headL (exOf acc) := by
  simp only [cE, cEx, cAcc, val_comp, val_cHead, val_left, val_right, Nat.unpair_pair, exOf]
theorem vs_cLbl (a i acc : ℕ) :
    val cLbl (Nat.pair a (Nat.pair i acc)) = lblOf (headL (exOf acc)) := by
  simp only [cLbl, cE, cEx, cAcc, val_comp, val_cHead, val_left, val_right, Nat.unpair_pair, exOf,
    lblOf]
theorem vs_cFv (a i acc : ℕ) :
    val cFv (Nat.pair a (Nat.pair i acc)) = fvOf (headL (exOf acc)) := by
  simp only [cFv, cE, cEx, cAcc, val_comp, val_cHead, val_left, val_right, Nat.unpair_pair, exOf,
    fvOf]
theorem vs_cFeat (a i acc : ℕ) :
    val cFeat (Nat.pair a (Nat.pair i acc)) = featOf (headL (exOf acc)) (jOf a) := by
  simp only [cFeat, cFv, cE, cEx, cAcc, cJa, cJ, val_comp, val_cHead, val_cPeel, val_pair, val_left,
    val_right, Nat.unpair_pair, exOf, fvOf, jOf, featOf]
theorem vs_cEqFP (a i acc : ℕ) :
    val cEqFP (Nat.pair a (Nat.pair i acc)) = bEq (featOf (headL (exOf acc)) (jOf a)) (pOf a) := by
  simp only [cEqFP, val_comp, val_pair, val_cEqBit', vs_cFeat, vs_cPa]
theorem vs_cCov (a i acc : ℕ) :
    val cCov (Nat.pair a (Nat.pair i acc))
      = bAnd (headL (msOf acc)) (bEq (featOf (headL (exOf acc)) (jOf a)) (pOf a)) := by
  simp only [cCov, val_comp, val_pair, val_cAnd', vs_cB, vs_cEqFP]
theorem vs_cNotLbl (a i acc : ℕ) :
    val cNotLbl (Nat.pair a (Nat.pair i acc)) = bNot (lblOf (headL (exOf acc))) := by
  simp only [cNotLbl, val_comp, val_cNot', vs_cLbl]

/-- The feature peel costs `≤ 8·(index) + 4`. -/
theorem tc_cPeel_le (L m : ℕ) : tc cPeel (Nat.pair L m) ≤ 8 * m + 4 := by
  unfold cPeel
  have h := tc_prec_le (cf := pair left right) (cg := cTailStep) (B := 7)
    (fun x => (tc_cTailStep x).le) L m
  simp only [tc_pair, tc_left, tc_right] at h
  omega

-- Projection reads: constant `tc`.
theorem tc_cAcc_le (a i acc : ℕ) : tc cAcc (Nat.pair a (Nat.pair i acc)) ≤ 3 := by
  simp only [cAcc, tc_comp, tc_right]; omega
theorem tc_cMs_le (a i acc : ℕ) : tc cMs (Nat.pair a (Nat.pair i acc)) ≤ 5 := by
  have := tc_cAcc_le a i acc; simp only [cMs, tc_comp, tc_left]; omega
theorem tc_cEx_le (a i acc : ℕ) : tc cEx (Nat.pair a (Nat.pair i acc)) ≤ 7 := by
  have := tc_cAcc_le a i acc; simp only [cEx, tc_comp, tc_left, tc_right]; omega
theorem tc_cZ0_le (a i acc : ℕ) : tc cZ0 (Nat.pair a (Nat.pair i acc)) ≤ 9 := by
  have := tc_cAcc_le a i acc; simp only [cZ0, tc_comp, tc_left, tc_right]; omega
theorem tc_cZ1_le (a i acc : ℕ) : tc cZ1 (Nat.pair a (Nat.pair i acc)) ≤ 9 := by
  have := tc_cAcc_le a i acc; simp only [cZ1, tc_comp, tc_right]; omega
theorem tc_cJa_le (a i acc : ℕ) : tc cJa (Nat.pair a (Nat.pair i acc)) ≤ 7 := by
  simp only [cJa, cJ, tc_comp, tc_left, tc_right]; omega
theorem tc_cPa_le (a i acc : ℕ) : tc cPa (Nat.pair a (Nat.pair i acc)) ≤ 7 := by
  simp only [cPa, cP, tc_comp, tc_left, tc_right]; omega
theorem tc_cB_le (a i acc : ℕ) : tc cB (Nat.pair a (Nat.pair i acc)) ≤ 9 := by
  have := tc_cMs_le a i acc; simp only [cB, tc_comp, tc_cHead]; omega
theorem tc_cE_le (a i acc : ℕ) : tc cE (Nat.pair a (Nat.pair i acc)) ≤ 11 := by
  have := tc_cEx_le a i acc; simp only [cE, tc_comp, tc_cHead]; omega
theorem tc_cLbl_le (a i acc : ℕ) : tc cLbl (Nat.pair a (Nat.pair i acc)) ≤ 13 := by
  have := tc_cE_le a i acc; simp only [cLbl, tc_comp, tc_left]; omega
theorem tc_cFv_le (a i acc : ℕ) : tc cFv (Nat.pair a (Nat.pair i acc)) ≤ 13 := by
  have := tc_cE_le a i acc; simp only [cFv, tc_comp, tc_right]; omega

-- The feature read: the one value-scaling cost, `O(jOf a)`.
theorem tc_cFeat_le (a i acc : ℕ) : tc cFeat (Nat.pair a (Nat.pair i acc)) ≤ 8 * jOf a + 40 := by
  have hfv := tc_cFv_le a i acc
  have hja := tc_cJa_le a i acc
  have hpeel := tc_cPeel_le (val cFv (Nat.pair a (Nat.pair i acc)))
    (val cJa (Nat.pair a (Nat.pair i acc)))
  have hjav := vs_cJa a i acc
  simp only [cFeat, tc_comp, tc_pair, tc_cHead, val_pair]
  omega

-- Gate reads: `O(1)` on bit operands, via the linear gate bounds + operand bit facts.
theorem tc_cEqFP_le (a i acc : ℕ) (hfeat : featOf (headL (exOf acc)) (jOf a) ≤ 1) (hp : pOf a ≤ 1) :
    tc cEqFP (Nat.pair a (Nat.pair i acc)) ≤ 8 * jOf a + 2100 := by
  have hf := tc_cFeat_le a i acc
  have hpa := tc_cPa_le a i acc
  have hfv : val cFeat (Nat.pair a (Nat.pair i acc)) ≤ 1 := by rw [vs_cFeat]; exact hfeat
  have hpv : val cPa (Nat.pair a (Nat.pair i acc)) ≤ 1 := by rw [vs_cPa]; exact hp
  have heq := tc_cEqBit_le (val cFeat (Nat.pair a (Nat.pair i acc)))
    (val cPa (Nat.pair a (Nat.pair i acc)))
  simp only [cEqFP, tc_comp, tc_pair, val_pair]
  omega

theorem tc_cNotLbl_le (a i acc : ℕ) (hlbl : lblOf (headL (exOf acc)) ≤ 1) :
    tc cNotLbl (Nat.pair a (Nat.pair i acc)) ≤ 30 := by
  have hl := tc_cLbl_le a i acc
  have hlv : val cLbl (Nat.pair a (Nat.pair i acc)) ≤ 1 := by rw [vs_cLbl]; exact hlbl
  have hnot := tc_cNot_le (val cLbl (Nat.pair a (Nat.pair i acc)))
  simp only [cNotLbl, tc_comp]
  omega

theorem tc_cCov_le (a i acc : ℕ) (hmask : headL (msOf acc) ≤ 1)
    (hfeat : featOf (headL (exOf acc)) (jOf a) ≤ 1) (hp : pOf a ≤ 1) :
    tc cCov (Nat.pair a (Nat.pair i acc)) ≤ 8 * jOf a + 2400 := by
  have hb := tc_cB_le a i acc
  have heqfp := tc_cEqFP_le a i acc hfeat hp
  have hbv : val cB (Nat.pair a (Nat.pair i acc)) ≤ 1 := by rw [vs_cB]; exact hmask
  have heqv : val cEqFP (Nat.pair a (Nat.pair i acc)) ≤ 1 := by rw [vs_cEqFP]; exact bEq_le_one _ _
  have hand := tc_cAnd_le (val cB (Nat.pair a (Nat.pair i acc)))
    (val cEqFP (Nat.pair a (Nat.pair i acc)))
  simp only [cCov, tc_comp, tc_pair, val_pair]
  omega

theorem tc_cZ0'_le (a i acc : ℕ) (hmask : headL (msOf acc) ≤ 1)
    (hfeat : featOf (headL (exOf acc)) (jOf a) ≤ 1) (hp : pOf a ≤ 1)
    (hlbl : lblOf (headL (exOf acc)) ≤ 1) (hz0 : z0Of acc ≤ 1) :
    tc cZ0' (Nat.pair a (Nat.pair i acc)) ≤ 8 * jOf a + 2800 := by
  have hcov := tc_cCov_le a i acc hmask hfeat hp
  have hnl := tc_cNotLbl_le a i acc hlbl
  have hz0t := tc_cZ0_le a i acc
  have hz0v : val cZ0 (Nat.pair a (Nat.pair i acc)) ≤ 1 := by rw [vs_cZ0]; exact hz0
  have hcovv : val cCov (Nat.pair a (Nat.pair i acc)) ≤ 1 := by rw [vs_cCov]; exact bAnd_le_one _ _
  have hnlv : val cNotLbl (Nat.pair a (Nat.pair i acc)) ≤ 1 := by rw [vs_cNotLbl]; exact bNot_le_one _
  have hand := tc_cAnd_le (val cCov (Nat.pair a (Nat.pair i acc)))
    (val cNotLbl (Nat.pair a (Nat.pair i acc)))
  have hInner : val (comp cAnd (pair cCov cNotLbl)) (Nat.pair a (Nat.pair i acc)) ≤ 1 := by
    rw [val_comp, val_pair]; exact val_cAnd_le_one _ _
  have hor := tc_cOr_le (val cZ0 (Nat.pair a (Nat.pair i acc)))
    (val (comp cAnd (pair cCov cNotLbl)) (Nat.pair a (Nat.pair i acc)))
  simp only [cZ0', tc_comp, tc_pair, val_pair]
  omega

theorem tc_cZ1'_le (a i acc : ℕ) (hmask : headL (msOf acc) ≤ 1)
    (hfeat : featOf (headL (exOf acc)) (jOf a) ≤ 1) (hp : pOf a ≤ 1)
    (hlbl : lblOf (headL (exOf acc)) ≤ 1) (hz1 : z1Of acc ≤ 1) :
    tc cZ1' (Nat.pair a (Nat.pair i acc)) ≤ 8 * jOf a + 2800 := by
  have hcov := tc_cCov_le a i acc hmask hfeat hp
  have hlv : val cLbl (Nat.pair a (Nat.pair i acc)) ≤ 1 := by rw [vs_cLbl]; exact hlbl
  have hcl := tc_cLbl_le a i acc
  have hz1t := tc_cZ1_le a i acc
  have hz1v : val cZ1 (Nat.pair a (Nat.pair i acc)) ≤ 1 := by rw [vs_cZ1]; exact hz1
  have hcovv : val cCov (Nat.pair a (Nat.pair i acc)) ≤ 1 := by rw [vs_cCov]; exact bAnd_le_one _ _
  have hand := tc_cAnd_le (val cCov (Nat.pair a (Nat.pair i acc)))
    (val cLbl (Nat.pair a (Nat.pair i acc)))
  have hInner : val (comp cAnd (pair cCov cLbl)) (Nat.pair a (Nat.pair i acc)) ≤ 1 := by
    rw [val_comp, val_pair]; exact val_cAnd_le_one _ _
  have hor := tc_cOr_le (val cZ1 (Nat.pair a (Nat.pair i acc)))
    (val (comp cAnd (pair cCov cLbl)) (Nat.pair a (Nat.pair i acc)))
  simp only [cZ1', tc_comp, tc_pair, val_pair]
  omega

/-- **The per-step cost bound.** Under bit operands (mask head, feature bit, label — the binary regime;
plus `pOf a` a bit and the two flags `≤ 1` by the accumulator invariant), the step costs
`≤ 16·(jOf a) + 5700`: every gate is `O(1)` and only the feature peel scales. -/
theorem tc_cStep_le (a i acc : ℕ) (hmask : headL (msOf acc) ≤ 1)
    (hfeat : featOf (headL (exOf acc)) (jOf a) ≤ 1) (hp : pOf a ≤ 1)
    (hlbl : lblOf (headL (exOf acc)) ≤ 1) (hz0 : z0Of acc ≤ 1) (hz1 : z1Of acc ≤ 1) :
    tc cStep (Nat.pair a (Nat.pair i acc)) ≤ 16 * jOf a + 5700 := by
  have h0 := tc_cZ0'_le a i acc hmask hfeat hp hlbl hz0
  have h1 := tc_cZ1'_le a i acc hmask hfeat hp hlbl hz1
  have hms := tc_cMs_le a i acc
  have hex := tc_cEx_le a i acc
  simp only [cStep, tc_pair, tc_comp, tc_cTail]
  omega

/-! ### Structural `PolyTime` premises -/

/-- The scan count `readM (instOf n)` is `PolyTime`. -/
theorem polyTime_count : PolyTime (fun n => readM (instOf n)) :=
  polyTime_comp polyTime_readM polyTime_left

/-! ### The accumulator stays poly-bit (discharging `hacc`) -/

theorem maskOf_le (n : ℕ) : maskOf n ≤ n :=
  le_trans (Nat.unpair_left_le _) (Nat.unpair_right_le _)
theorem dataOf_le (n : ℕ) : dataOf n ≤ n :=
  le_trans (readData_le (instOf n)) (Nat.unpair_left_le n)

theorem acc_decompose (x : ℕ) :
    x = Nat.pair (msOf x) (Nat.pair (exOf x) (Nat.pair (z0Of x) (z1Of x))) := by
  simp only [msOf, exOf, z0Of, z1Of, Nat.pair_unpair]

/-- Any accumulator whose suffixes are `≤ n` and whose flags are bits has bit-length `≤ 6·size n + 30`. -/
theorem size_acc_bound (acc n : ℕ) (hms : msOf acc ≤ n) (hex : exOf acc ≤ n)
    (hz0 : z0Of acc ≤ 1) (hz1 : z1Of acc ≤ 1) : Nat.size acc ≤ 6 * Nat.size n + 30 := by
  rw [acc_decompose acc]
  have p1 := size_pair_le (msOf acc) (Nat.pair (exOf acc) (Nat.pair (z0Of acc) (z1Of acc)))
  have p2 := size_pair_le (exOf acc) (Nat.pair (z0Of acc) (z1Of acc))
  have p3 := size_pair_le (z0Of acc) (z1Of acc)
  have hsms : Nat.size (msOf acc) ≤ Nat.size n := Nat.size_le_size hms
  have hsex : Nat.size (exOf acc) ≤ Nat.size n := Nat.size_le_size hex
  have hsz0 : Nat.size (z0Of acc) ≤ 1 := le_trans (Nat.size_le_size hz0) (by rw [Nat.size_one])
  have hsz1 : Nat.size (z1Of acc) ≤ 1 := le_trans (Nat.size_le_size hz1) (by rw [Nat.size_one])
  omega

/-- The scan accumulator after the full run is poly-bit — `hacc` for the loop, discharged. -/
theorem polyBounded_acc : PolyBounded
    (fun n => Nat.size (val (prec cInit cStep) (Nat.pair n (readM (instOf n))))) := by
  refine PolyBounded.mono (fun n => ?_)
    (((PolyBounded.const 6).mul PolyBounded.size).add (PolyBounded.const 30))
  rw [val_cLoop]
  exact size_acc_bound _ n
    (le_trans (inv_msOf_le _ _ _ _ _) (maskOf_le n))
    (le_trans (inv_exOf_le _ _ _ _ _) (dataOf_le n))
    (inv_z0_le_one _ _ _ _ _) (inv_z1_le_one _ _ _ _ _)

/-- The base code's native cost is a constant, hence poly-bounded. -/
theorem tc_cInit_le (n : ℕ) : tc cInit n ≤ 13 := by
  simp only [cInit, cMask, cData, tc_pair, tc_comp, tc_left, tc_right, tc_zero, val_left,
    val_right]
  omega
theorem polyBounded_tc_cInit : PolyBounded (tc cInit) :=
  PolyBounded.mono tc_cInit_le (PolyBounded.const 13)

/-- **The scan loop is `PolyTime`** — the assembled `polyTime_loop` closure. The three genuinely
WF/bit-conditional analytic facts are threaded as premises (exactly the `polyTime_peel` pattern the
C2a residual note flags): `hCval` — the example count `readM (instOf n)` is a poly-bit VALUE (from
`readM_le_size` under `WF`); `Bstep`/`hstep` — a per-step cost bound holding over the visited
iterations `i < readM (instOf n)` (poly-bit under the binary-bit regime: each read is `≤ 1` so every
gate is `O(1)` and only the feature peel scales, `O(jOf n)`); `hacc` — the accumulator stays poly-bit
(its two suffixes are `≤ maskOf n`/`dataOf n` and its two flags are `≤ 1`, by the accumulator
invariants). All the STRUCTURAL premises (`rfind'`-freeness, the shaper `PolyTime`s, the base cost) are
discharged here. -/
theorem polyTime_cScan
    (hCval : PolyBounded (fun n => readM (instOf n)))
    (Bstep : ℕ → ℕ) (hBstep : PolyBounded Bstep)
    (hstep : ∀ n i, i < readM (instOf n) →
      tc cStep (Nat.pair n (Nat.pair i (val (prec cInit cStep) (Nat.pair n i)))) ≤ Bstep n) :
    PolyTime (fun n => val (prec cInit cStep) (Nat.pair n (readM (instOf n)))) :=
  polyTime_loop (cf := cInit) (cg := cStep) rfindFree_cInit rfindFree_cStep
    (astart := fun n => n) (count := fun n => readM (instOf n))
    polyTime_id polyTime_count hCval polyBounded_tc_cInit Bstep hBstep hstep polyBounded_acc

/-! ## Layer 4 — self-contained `PolyTime` on the binary well-formed domain

The threaded `hstep`/`hCval` premises of `polyTime_cScan` are ∀-`n` `PolyBounded` facts that are FALSE
on garbage inputs (a raw slot is exponential in the bit-length), so a meaningful statement must restrict
to the well-formed domain. `PolyTimeOn D f` (poly-time cost + output size on `D`) is that honest notion;
`polyTime_purity` proves it for the binary-1-DL domain, with NO poly-bit hypotheses left — they are
discharged from `readM_le_size`/`readK_le_size`. -/

/-- Every mask/example suffix is the peeled original — the carried suffix at step `i` is `peel _ i`. -/
theorem inv_msOf_peel (j p mask data i : ℕ) :
    msOf ((stepFn j p)^[i] (initAcc mask data)) = peel mask i := by
  induction i with
  | zero => simp [initAcc, msOf, peel, Nat.unpair_pair]
  | succ k ih =>
      rw [Function.iterate_succ_apply', msOf_stepFn, ih]
      simp only [peel, Function.iterate_succ_apply']
theorem inv_exOf_peel (j p mask data i : ℕ) :
    exOf ((stepFn j p)^[i] (initAcc mask data)) = peel data i := by
  induction i with
  | zero => simp [initAcc, exOf, peel, Nat.unpair_pair]
  | succ k ih =>
      rw [Function.iterate_succ_apply', exOf_stepFn, ih]
      simp only [peel, Function.iterate_succ_apply']

/-- **Binary well-formedness of the instance.** `WF` plus: every example's label and every feature bit
is `≤ 1` (the binary-1-DL regime), over the `List` model of the example data. -/
def WFBits (inst : ℕ) : Prop :=
  WF inst ∧ ∃ exs : List ℕ, readData inst = encodeList exs ∧ exs.length = readM inst ∧
    (∀ e ∈ exs, lblOf e ≤ 1) ∧ (∀ e ∈ exs, ∀ j, featOf e j ≤ 1)

/-- **Mask validity.** The mask is a genuine length-`m` flag-cons list of bits. -/
def MaskValid (mask m : ℕ) : Prop :=
  ∃ msks : List ℕ, mask = encodeList msks ∧ msks.length = m ∧ ∀ b ∈ msks, b ≤ 1

/-- **Visited-state bit-ness.** Under binary well-formedness, at every visited example `i` the mask
head, the feature bit at `j = jOf n`, and the label are all `≤ 1`. The mask head needs `MaskValid`, the
feature/label need `WFBits`; the flags (handled at the call site) need only the accumulator invariant. -/
theorem visited_bits (n i : ℕ) (hw : WFBits (instOf n))
    (hm : MaskValid (maskOf n) (readM (instOf n))) (hi : i < readM (instOf n)) :
    headL (msOf ((stepFn (jOf n) (pOf n))^[i] (initAcc (maskOf n) (dataOf n)))) ≤ 1 ∧
    featOf (headL (exOf ((stepFn (jOf n) (pOf n))^[i] (initAcc (maskOf n) (dataOf n)))))
      (jOf n) ≤ 1 ∧
    lblOf (headL (exOf ((stepFn (jOf n) (pOf n))^[i] (initAcc (maskOf n) (dataOf n))))) ≤ 1 := by
  obtain ⟨msks, hmeq, hmlen, hmbit⟩ := hm
  obtain ⟨_hwf, exs, hdeq, hdlen, hlbl, hfeat⟩ := hw
  rw [inv_msOf_peel, inv_exOf_peel]
  have him : i < msks.length := by rw [hmlen]; exact hi
  have hie : i < exs.length := by rw [hdlen]; exact hi
  refine ⟨?_, ?_, ?_⟩
  · rw [hmeq, getExample_encode msks i him]; exact hmbit _ (List.getElem_mem him)
  · rw [show dataOf n = encodeList exs from hdeq, getExample_encode exs i hie]
    exact hfeat _ (List.getElem_mem hie) (jOf n)
  · rw [show dataOf n = encodeList exs from hdeq, getExample_encode exs i hie]
    exact hlbl _ (List.getElem_mem hie)

/-- **Poly-time on a domain** — the honest "poly cost + output size on well-formed inputs" notion. -/
def PolyBoundedOn (D : ℕ → Prop) (t : ℕ → ℕ) : Prop :=
  ∃ C k : ℕ, ∀ n, D n → t n ≤ C * (Nat.size n + 1) ^ k + C
def PolyTimeOn (D : ℕ → Prop) (f : ℕ → ℕ) : Prop :=
  ∃ c : Code, RfindFree c ∧ (∀ n, D n → val c n = f n) ∧
    PolyBoundedOn D (tc c) ∧ PolyBoundedOn D (fun n => Nat.size (f n))

/-- The binary well-formed domain for purity: a bit-well-formed instance, a valid mask, `p` a bit, and
a valid literal index `j < k` (so `jOf n ≤ readK`). -/
def PurityWF (n : ℕ) : Prop :=
  WFBits (instOf n) ∧ MaskValid (maskOf n) (readM (instOf n)) ∧ pOf n ≤ 1 ∧ jOf n ≤ readK (instOf n)

theorem val_cZ0acc (acc : ℕ) : val cZ0acc acc = z0Of acc := by
  simp only [cZ0acc, val_comp, val_left, val_right, z0Of]
theorem val_cZ1acc (acc : ℕ) : val cZ1acc acc = z1Of acc := by
  simp only [cZ1acc, val_comp, val_right, z1Of]

theorem rfindFree_cFinal : RfindFree cFinal := by
  simp only [cFinal, cSawAny, cZ0acc, cZ1acc, cNot, cAnd, cOr, cIsPos, cShape0, cSwap, notCore, orCore,
    isPosCore, constCode, RfindFree, and_self]
theorem rfindFree_cId : RfindFree cId := ⟨trivial, trivial⟩
theorem rfindFree_cCount : RfindFree cCount := ⟨⟨trivial, trivial⟩, trivial⟩
theorem rfindFree_cPurity : RfindFree cPurity :=
  ⟨rfindFree_cFinal, ⟨rfindFree_cInit, rfindFree_cStep⟩, rfindFree_cId, rfindFree_cCount⟩

/-- The read-out `cFinal` is `O(1)` on a bit-flagged accumulator. -/
theorem tc_cFinal_le (acc : ℕ) (hz0 : z0Of acc ≤ 1) (hz1 : z1Of acc ≤ 1) : tc cFinal acc ≤ 300 := by
  have h0 : tc cZ0acc acc ≤ 5 := by simp only [cZ0acc, tc_comp, tc_left, tc_right]; omega
  have h1 : tc cZ1acc acc ≤ 5 := by simp only [cZ1acc, tc_comp, tc_right]; omega
  have hz0v : val cZ0acc acc ≤ 1 := by rw [val_cZ0acc]; exact hz0
  have hz1v : val cZ1acc acc ≤ 1 := by rw [val_cZ1acc]; exact hz1
  have hand := tc_cAnd_le (val cZ0acc acc) (val cZ1acc acc)
  have handv : val cAnd (Nat.pair (val cZ0acc acc) (val cZ1acc acc)) ≤ 1 := val_cAnd_le_one _ _
  have hnot := tc_cNot_le (val cAnd (Nat.pair (val cZ0acc acc) (val cZ1acc acc)))
  have hor := tc_cOr_le (val cZ0acc acc) (val cZ1acc acc)
  simp only [cFinal, cSawAny, tc_pair, tc_comp, val_comp, val_pair]
  omega

/-- **The per-visited-step bound**, proved: at every visited example the step costs `≤ 16·(jOf n)+5700`
(uniformly in `i`). Feature/label/mask bits from `WFBits`/`MaskValid` (`visited_bits`); the flags from
the accumulator invariant. -/
theorem hstep_visited (n : ℕ) (hw : WFBits (instOf n))
    (hm : MaskValid (maskOf n) (readM (instOf n))) (hp : pOf n ≤ 1) :
    ∀ i, i < readM (instOf n) →
      tc cStep (Nat.pair n (Nat.pair i (val (prec cInit cStep) (Nat.pair n i))))
        ≤ 16 * jOf n + 5700 := by
  intro i hi
  rw [val_cLoop]
  obtain ⟨hmask, hfeat, hlbl⟩ := visited_bits n i hw hm hi
  exact tc_cStep_le n i _ hmask hfeat hp hlbl (inv_z0_le_one _ _ _ _ _) (inv_z1_le_one _ _ _ _ _)

/-- **`cPurity`'s native cost on a well-formed instance**: the base cost, the `(Bstep+1)·m` loop term
(`tc_prec_le'` + `hstep_visited`), the shaper, and the `O(1)` read-out sum to
`≤ (16·jOf n + 5701)·readM(instOf n) + 400`. -/
theorem tc_cPurity_raw (n : ℕ) (hw : WFBits (instOf n))
    (hm : MaskValid (maskOf n) (readM (instOf n))) (hp : pOf n ≤ 1) :
    tc cPurity n ≤ (16 * jOf n + 5700 + 1) * readM (instOf n) + 400 := by
  have hpair : val (pair cId cCount) n = Nat.pair n (readM (instOf n)) := by
    rw [val_pair, val_cId, val_cCount]
  have hidcount : tc (pair cId cCount) n ≤ 30 := by
    simp only [cId, cCount, cReadM, cInst, tc_pair, tc_comp, tc_left, tc_right]; omega
  have hprec := tc_prec_le' (cf := cInit) (cg := cStep) (a := n) (B := 16 * jOf n + 5700)
    (readM (instOf n)) (hstep_visited n hw hm hp)
  have hinit := tc_cInit_le n
  have hfin := tc_cFinal_le (val (prec cInit cStep) (Nat.pair n (readM (instOf n))))
    (by rw [val_cLoop]; exact inv_z0_le_one _ _ _ _ _)
    (by rw [val_cLoop]; exact inv_z1_le_one _ _ _ _ _)
  unfold cPurity
  rw [tc_comp, tc_comp, val_comp, hpair]
  set P := (16 * jOf n + 5700 + 1) * readM (instOf n)
  omega

/-- **`cPurity` is poly-time on the well-formed domain.** The raw `(Bstep+1)·m` bound is turned poly-bit
by `jOf n ≤ readK ≤ size n` (under `WF`) and `readM ≤ size n`, giving a quadratic in `Nat.size n`. -/
theorem polyBoundedOn_tc_cPurity : PolyBoundedOn PurityWF (tc cPurity) := by
  refine ⟨6000, 2, fun n hn => ?_⟩
  obtain ⟨hw, hm, hp, hjk⟩ := hn
  have hwf : WF (instOf n) := hw.1
  have hins : Nat.size (instOf n) ≤ Nat.size n := Nat.size_le_size (Nat.unpair_left_le n)
  have hjs : jOf n ≤ Nat.size n := le_trans hjk (le_trans (readK_le_size (instOf n) hwf) hins)
  have hms : readM (instOf n) ≤ Nat.size n := le_trans (readM_le_size (instOf n) hwf) hins
  have hraw := tc_cPurity_raw n hw hm hp
  have hprod : (16 * jOf n + 5700 + 1) * readM (instOf n) ≤ (16 * Nat.size n + 5701) * Nat.size n :=
    Nat.mul_le_mul (by omega) hms
  nlinarith [hraw, hprod]

/-- The verdict is a triple of bits, so its size is `O(1)` (a constant, `k = 0`). -/
theorem polyBoundedOn_size_purityVal :
    PolyBoundedOn PurityWF (fun n => Nat.size (purityVal n)) := by
  refine ⟨16, 0, fun n _ => ?_⟩
  have hi : Nat.size (bNot (bAnd (z0Of (purityAcc n)) (z1Of (purityAcc n)))) ≤ 1 :=
    le_trans (Nat.size_le_size (bNot_le_one _)) (by rw [Nat.size_one])
  have hc : Nat.size (z1Of (purityAcc n)) ≤ 1 :=
    le_trans (Nat.size_le_size (by unfold purityAcc; exact inv_z1_le_one _ _ _ _ _))
      (by rw [Nat.size_one])
  have hs : Nat.size (bOr (z0Of (purityAcc n)) (z1Of (purityAcc n))) ≤ 1 :=
    le_trans (Nat.size_le_size (bOr_le_one _ _)) (by rw [Nat.size_one])
  have hpv : Nat.size (purityVal n) ≤ 16 := by
    unfold purityVal
    have q1 := size_pair_le (bNot (bAnd (z0Of (purityAcc n)) (z1Of (purityAcc n))))
      (Nat.pair (z1Of (purityAcc n)) (bOr (z0Of (purityAcc n)) (z1Of (purityAcc n))))
    have q2 := size_pair_le (z1Of (purityAcc n)) (bOr (z0Of (purityAcc n)) (z1Of (purityAcc n)))
    omega
  simp only [pow_zero, mul_one]
  omega

/-- **`polyTime_purity`.** With `hstep` discharged, purity-checking a literal against a working set is
poly-time on the honest well-formed domain `PurityWF` — no `PolyBounded` side-hypotheses remain. -/
theorem polyTime_purity : PolyTimeOn PurityWF purityVal :=
  ⟨cPurity, rfindFree_cPurity, fun n _ => val_cPurity n,
    polyBoundedOn_tc_cPurity, polyBoundedOn_size_purityVal⟩

/-! ## Layer 5 — `cReverse`: reversing a flag-cons list by a prepending loop

The one genuinely new building block for `maskUpdate`. The scan that builds the updated mask prepends
each new bit (natural in a forward pass), so the working list comes out **reversed**; one `cReverse`
pass restores order. The step is pure pointer-shuffling (`unpair`/`pair`), so it is `O(1)`-`tc`
regardless of the cell values — hence `cReverse` is `O(m)`-`tc`, uniformly in the list content. -/

/-- One reverse step on the accumulator `⟨remaining, prefix⟩`: pop the head off `remaining`, cons it
onto `prefix`. -/
def revStepFn (acc : ℕ) : ℕ :=
  Nat.pair (tailL acc.unpair.1) (Nat.pair 1 (Nat.pair (headL acc.unpair.1) acc.unpair.2))

/-- `remaining` field of the reverse accumulator (`acc.1`), read off the step input `⟨a,⟨i,acc⟩⟩`. -/
def cRevRem : Code := comp left (comp right right)
/-- `prefix` field of the reverse accumulator (`acc.2`). -/
def cRevPref : Code := comp right (comp right right)
/-- The reverse step code: `⟨tailL remaining, cons (headL remaining) prefix⟩`. -/
def cRevStep : Code :=
  pair (comp cTail cRevRem) (pair (constCode 1) (pair (comp cHead cRevRem) cRevPref))

theorem rfindFree_cRevStep : RfindFree cRevStep := by
  simp only [cRevStep, cRevRem, cRevPref, cHead, cTail, constCode, RfindFree, and_self]

theorem val_cRevStep (a i acc : ℕ) : val cRevStep (Nat.pair a (Nat.pair i acc)) = revStepFn acc := by
  simp only [cRevStep, cRevRem, cRevPref, val_pair, val_comp, val_left, val_right, val_cHead,
    val_cTail, val_constCode, Nat.unpair_pair, revStepFn, headL, tailL]

/-- **Reverse loop = iterated step.** -/
theorem val_cRevLoop (astart t : ℕ) :
    val (prec (pair left right) cRevStep) (Nat.pair astart t) = revStepFn^[t] astart := by
  induction t with
  | zero =>
      rw [val_prec_zero, val_pair, val_left, val_right, Nat.pair_unpair, Function.iterate_zero_apply]
  | succ k ih => rw [val_prec_succ, val_cRevStep, ih, Function.iterate_succ_apply']

/-- **The reverse scan realises `List.reverse`.** Running the step over an encoded list for its length
empties `remaining` and lands `prefix = reverse ++ (initial prefix)`. -/
theorem revStepFn_iterate (xs : List ℕ) : ∀ acc : List ℕ,
    revStepFn^[xs.length] (Nat.pair (encodeList xs) (encodeList acc))
      = Nat.pair 0 (encodeList (xs.reverse ++ acc)) := by
  induction xs with
  | nil => intro acc; simp [encodeList]
  | cons x xs ih =>
      intro acc
      rw [List.length_cons, Function.iterate_succ_apply]
      have hstep : revStepFn (Nat.pair (encodeList (x :: xs)) (encodeList acc))
          = Nat.pair (encodeList xs) (encodeList (x :: acc)) := by
        simp only [revStepFn, Nat.unpair_pair, headL, tailL, encodeList]
      rw [hstep, ih (x :: acc), List.reverse_cons, List.append_assoc, List.singleton_append]

/-- Shaper: `⟨L, m⟩ ↦ ⟨L, 0⟩` — the initial reverse accumulator. -/
def cRevAstart : Code := pair left zero
/-- Shaper: `⟨L, m⟩ ↦ m` — the loop count. -/
def cRevCount : Code := right
/-- **`cReverse`**: reverse the flag-cons list `L` given its length `m`, input packed as `⟨L, m⟩`. -/
def cReverse : Code := comp right (comp (prec (pair left right) cRevStep) (pair cRevAstart cRevCount))

theorem rfindFree_cReverse : RfindFree cReverse := by
  simp only [cReverse, cRevAstart, cRevCount, cRevStep, cRevRem, cRevPref, cHead, cTail, constCode,
    RfindFree, and_self]

/-- **`cReverse` correctness.** On an encoded list (length supplied) it returns the encoded reverse. -/
theorem val_cReverse (xs : List ℕ) :
    val cReverse (Nat.pair (encodeList xs) xs.length) = encodeList xs.reverse := by
  have hit := revStepFn_iterate xs []
  simp only [encodeList, List.append_nil] at hit
  simp only [cReverse, cRevAstart, cRevCount, val_comp, val_pair, val_left, val_right, val_zero,
    Nat.unpair_pair, val_cRevLoop, hit]

/-- The reverse step is `O(1)`-`tc` (pure pointer-shuffling — no value arithmetic). -/
theorem tc_cRevStep_le (X : ℕ) : tc cRevStep X ≤ 40 := by
  have hc := tc_constCode_le 1 X
  simp only [cRevStep, cRevRem, cRevPref, tc_pair, tc_comp, tc_left, tc_right, tc_cHead, tc_cTail]
  omega

/-- **`cReverse` is `O(m)`-`tc`**, uniformly in the list content `L`. -/
theorem tc_cReverse_le (L m : ℕ) : tc cReverse (Nat.pair L m) ≤ 41 * m + 40 := by
  have hstep := tc_prec_le (cf := pair left right) (cg := cRevStep) (B := 40)
    (fun x => tc_cRevStep_le x) (Nat.pair L 0) m
  have hbase : tc (pair left right) (Nat.pair L 0) = 3 := by
    simp only [tc_pair, tc_left, tc_right]
  simp only [cReverse, cRevAstart, cRevCount, tc_comp, tc_pair, tc_left, tc_right, tc_zero, tc_right,
    val_comp, val_pair, val_left, val_zero, val_right, Nat.unpair_pair] at hstep ⊢
  omega

/-! ## Layer 6 — `maskUpdate`: refine the working set by one literal

`maskUpdate inst mask j p` produces `mask'` with `mask'[i] = mask[i] ∧ ¬(example i satisfies (j,p))`.
A forward carried-suffix scan over `i < m` reads the mask head and the feature-`j` bit, gates them,
and PREPENDS the new bit to a working list (so it comes out reversed); one `cReverse` pass restores
order. The output is again a length-`m` flag-cons list of bits — that structural fact
(`maskValid_maskUpdate`) is what lets the outer greedy loop carry a valid working set across rounds. -/

/-- Pack a literal query `⟨inst, ⟨mask, ⟨j, p⟩⟩⟩` (the input shape shared by `cPurity`/`maskUpdate`). -/
def packLit (inst mask j p : ℕ) : ℕ := Nat.pair inst (Nat.pair mask (Nat.pair j p))

theorem instOf_packLit (inst mask j p : ℕ) : instOf (packLit inst mask j p) = inst := by
  simp only [instOf, packLit, Nat.unpair_pair]
theorem maskOf_packLit (inst mask j p : ℕ) : maskOf (packLit inst mask j p) = mask := by
  simp only [maskOf, packLit, Nat.unpair_pair]
theorem jOf_packLit (inst mask j p : ℕ) : jOf (packLit inst mask j p) = j := by
  simp only [jOf, packLit, Nat.unpair_pair]
theorem pOf_packLit (inst mask j p : ℕ) : pOf (packLit inst mask j p) = p := by
  simp only [pOf, packLit, Nat.unpair_pair]
theorem dataOf_packLit (inst mask j p : ℕ) : dataOf (packLit inst mask j p) = readData inst := by
  rw [dataOf, instOf_packLit]

/-- The built (reversed working) list — the `.2.2` field of the scan accumulator. -/
def muBuilt (acc : ℕ) : ℕ := acc.unpair.2.unpair.2

/-- One refine-scan step: peel both suffixes, prepend the new mask bit
`mask[i] ∧ ¬(feature-j = p)` onto the working list. -/
def muStepFn (j p acc : ℕ) : ℕ :=
  Nat.pair (tailL (msOf acc))
    (Nat.pair (tailL (exOf acc))
      (Nat.pair 1 (Nat.pair
        (bAnd (headL (msOf acc)) (bNot (bEq (featOf (headL (exOf acc)) j) p)))
        (muBuilt acc))))

/-- The new-bit gate `mask-head ∧ ¬(feature = p)` (reuses `cB`/`cEqFP` from the purity scan). -/
def cNewBit : Code := comp cAnd (pair cB (comp cNot cEqFP))
/-- The working-list field `acc.2.2`. -/
def cMuBuilt : Code := comp right (comp right cAcc)
/-- The refine-scan step code. -/
def cMuStep : Code :=
  pair (comp cTail cMs) (pair (comp cTail cEx) (pair (constCode 1) (pair cNewBit cMuBuilt)))

theorem rfindFree_cMuStep : RfindFree cMuStep := by
  simp only [cMuStep, cNewBit, cMuBuilt, cB, cEqFP, cFeat, cFv, cE, cMs, cEx, cAcc, cJa, cPa, cJ, cP,
    cHead, cTail, cAnd, cOr, cNot, cEqBit, cIsPos, cShape0, cSwap, isPosCore, notCore, orCore, cPeel,
    cTailStep, constCode, RfindFree, and_self]

theorem val_cMuStep (a i acc : ℕ) :
    val cMuStep (Nat.pair a (Nat.pair i acc)) = muStepFn (jOf a) (pOf a) acc := by
  simp only [cMuStep, cNewBit, cMuBuilt, cB, cEqFP, cFeat, cFv, cE, cMs, cEx, cAcc, cJa, cPa,
    val_pair, val_comp, val_left, val_right, val_cHead, val_cTail, val_cPeel, val_cNot', val_cAnd',
    val_cEqBit', val_cJ, val_cP, val_constCode, Nat.unpair_pair,
    muStepFn, muBuilt, msOf, exOf, fvOf, featOf]

/-- The per-`(bit, example)` update: `bit ∧ ¬(feature-j = p)` (always a bit). -/
def updBit (j p b e : ℕ) : ℕ := bAnd b (bNot (bEq (featOf e j) p))
theorem updBit_le_one (j p b e : ℕ) : updBit j p b e ≤ 1 := bAnd_le_one _ _

/-- **The refine scan realises the reversed `zipWith`.** Running the step over the encoded mask/example
lists (equal length) for `exs.length` iterations empties both suffixes and lands the working list
`(zipWith (updBit j p) msks exs).reverse ++ (initial working list)`. -/
theorem muStepFn_iterate (j p : ℕ) (exs : List ℕ) : ∀ (msks bacc : List ℕ),
    msks.length = exs.length →
      (muStepFn j p)^[exs.length]
          (Nat.pair (encodeList msks) (Nat.pair (encodeList exs) (encodeList bacc)))
        = Nat.pair 0 (Nat.pair 0
            (encodeList ((List.zipWith (updBit j p) msks exs).reverse ++ bacc))) := by
  induction exs with
  | nil =>
      intro msks bacc hlen
      have hm : msks = [] := List.length_eq_zero_iff.mp (by simpa using hlen)
      subst hm
      simp [encodeList]
  | cons e es ih =>
      intro msks bacc hlen
      cases msks with
      | nil => simp at hlen
      | cons mb mbs =>
          have hlen' : mbs.length = es.length := by simpa using hlen
          rw [List.length_cons, Function.iterate_succ_apply]
          have hx : muStepFn j p (Nat.pair (encodeList (mb :: mbs))
                (Nat.pair (encodeList (e :: es)) (encodeList bacc)))
              = Nat.pair (encodeList mbs) (Nat.pair (encodeList es)
                  (encodeList (updBit j p mb e :: bacc))) := by
            simp only [muStepFn, msOf, exOf, muBuilt, Nat.unpair_pair, headL, tailL, updBit, encodeList]
          rw [hx, ih mbs (updBit j p mb e :: bacc) hlen', List.zipWith_cons_cons, List.reverse_cons,
            List.append_assoc, List.singleton_append]

/-- Base code: `⟨maskOf n, ⟨dataOf n, 0⟩⟩` — full suffixes, empty working list. -/
def cMuInit : Code := pair cMask (pair cData zero)
/-- The refine scan run `readM inst` times. -/
def cMuScan : Code := comp (prec cMuInit cMuStep) (pair cId cCount)
/-- **`maskUpdate`'s code**: run the scan, extract the reversed working list, then `cReverse` it. -/
def cMaskUpdate : Code := comp cReverse (pair (comp (comp right right) cMuScan) cCount)
/-- Semantic `maskUpdate` on a packed input. -/
def maskUpdateVal (n : ℕ) : ℕ := val cMaskUpdate n
/-- **`maskUpdate inst mask j p`** — refine the working set `mask` by literal `(j,p)`. -/
def maskUpdate (inst mask j p : ℕ) : ℕ := maskUpdateVal (packLit inst mask j p)

theorem val_cMuLoop (n t : ℕ) :
    val (prec cMuInit cMuStep) (Nat.pair n t)
      = (muStepFn (jOf n) (pOf n))^[t] (Nat.pair (maskOf n) (Nat.pair (dataOf n) 0)) := by
  induction t with
  | zero =>
      rw [val_prec_zero]
      simp only [cMuInit, val_pair, val_cMask, val_cData, val_zero, Function.iterate_zero_apply]
  | succ k ih => rw [val_prec_succ, val_cMuStep, ih, Function.iterate_succ_apply']

/-- **`maskUpdate` correctness (encoded form).** On encoded inputs the primitive returns the encoded
`zipWith (updBit j p)` over `msks`/`exs` — a length-`m` list of bits. -/
theorem maskUpdate_eq_encode (n : ℕ) (msks exs : List ℕ)
    (hmask : maskOf n = encodeList msks) (hdata : dataOf n = encodeList exs)
    (hcount : readM (instOf n) = exs.length) (hlen : msks.length = exs.length) :
    maskUpdateVal n = encodeList (List.zipWith (updBit (jOf n) (pOf n)) msks exs) := by
  have hiter := muStepFn_iterate (jOf n) (pOf n) exs msks [] hlen
  simp only [encodeList, List.append_nil] at hiter
  have hscan : val (comp (comp right right) cMuScan) n
      = encodeList (List.zipWith (updBit (jOf n) (pOf n)) msks exs).reverse := by
    have h1 : val cMuScan n = (muStepFn (jOf n) (pOf n))^[readM (instOf n)]
        (Nat.pair (maskOf n) (Nat.pair (dataOf n) 0)) := by
      simp only [cMuScan, val_comp, val_pair, val_cId, val_cCount, val_cMuLoop]
    rw [val_comp, h1, hcount, hmask, hdata, hiter]
    simp only [val_comp, val_right, Nat.unpair_pair]
  unfold maskUpdateVal cMaskUpdate
  rw [val_comp, val_pair, hscan, val_cCount, hcount]
  have hlenz : exs.length = (List.zipWith (updBit (jOf n) (pOf n)) msks exs).reverse.length := by
    rw [List.length_reverse, List.length_zipWith, hlen, Nat.min_self]
  rw [hlenz, val_cReverse, List.reverse_reverse]

/-- Every element of the refined working list is a bit. -/
theorem zipWith_updBit_le_one (j p : ℕ) : ∀ (l1 l2 : List ℕ),
    ∀ x ∈ List.zipWith (updBit j p) l1 l2, x ≤ 1 := by
  intro l1
  induction l1 with
  | nil => intro l2 x hx; simp at hx
  | cons a as ih =>
      intro l2 x hx
      cases l2 with
      | nil => simp at hx
      | cons b bs =>
          rw [List.zipWith_cons_cons, List.mem_cons] at hx
          rcases hx with h | h
          · rw [h]; exact updBit_le_one j p a b
          · exact ih bs x h

/-- **THE CRUX.** `maskUpdate` preserves mask validity: the refined working set is again a genuine
length-`m` flag-cons list of bits. This is the induction step that lets the outer greedy loop carry a
valid working set from round `t` to `t+1`. -/
theorem maskValid_maskUpdate (inst mask j p : ℕ) (hw : WFBits inst)
    (hm : MaskValid mask (readM inst)) :
    MaskValid (maskUpdate inst mask j p) (readM inst) := by
  obtain ⟨_hwf, exs, hdeq, hdlen, _hlbl, _hfeat⟩ := hw
  obtain ⟨msks, hmeq, hmlen, _hmbit⟩ := hm
  have heq : maskUpdate inst mask j p
      = encodeList (List.zipWith (updBit j p) msks exs) := by
    have h := maskUpdate_eq_encode (packLit inst mask j p) msks exs
      (by rw [maskOf_packLit]; exact hmeq)
      (by rw [dataOf_packLit]; exact hdeq)
      (by rw [instOf_packLit]; exact hdlen.symm)
      (by rw [hmlen, hdlen])
    rw [jOf_packLit, pOf_packLit] at h
    exact h
  refine ⟨List.zipWith (updBit j p) msks exs, heq, ?_, ?_⟩
  · rw [List.length_zipWith, hmlen, hdlen, Nat.min_self]
  · exact fun x hx => zipWith_updBit_le_one j p msks exs x hx

/-- **`maskUpdate`'s `i`-th bit** (`i < m`): the old mask bit at `i` AND NOT (example `i` satisfies
`(j,p)`), against the `List` model. -/
theorem maskUpdate_getBit (inst mask j p i : ℕ) (hw : WFBits inst)
    (hm : MaskValid mask (readM inst)) (hi : i < readM inst) :
    headL (peel (maskUpdate inst mask j p) i)
      = bAnd (headL (peel mask i)) (bNot (bEq (featOf (headL (peel (readData inst) i)) j) p)) := by
  obtain ⟨_hwf, exs, hdeq, hdlen, _hlbl, _hfeat⟩ := hw
  obtain ⟨msks, hmeq, hmlen, _hmbit⟩ := hm
  have hie : i < exs.length := by rw [hdlen]; exact hi
  have him : i < msks.length := by rw [hmlen]; exact hi
  have heq : maskUpdate inst mask j p
      = encodeList (List.zipWith (updBit j p) msks exs) := by
    have h := maskUpdate_eq_encode (packLit inst mask j p) msks exs
      (by rw [maskOf_packLit]; exact hmeq)
      (by rw [dataOf_packLit]; exact hdeq)
      (by rw [instOf_packLit]; exact hdlen.symm)
      (by rw [hmlen, hdlen])
    rw [jOf_packLit, pOf_packLit] at h
    exact h
  have hlz : i < (List.zipWith (updBit j p) msks exs).length := by
    rw [List.length_zipWith, hmlen, hdlen, Nat.min_self]; exact hi
  rw [heq, getExample_encode _ i hlz, List.getElem_zipWith, hmeq, hdeq,
    getExample_encode msks i him, getExample_encode exs i hie, updBit]

/-! ### `maskUpdate` is `PolyTime` on the well-formed binary domain

The scan reuses the purity accumulator shape (`msOf`/`exOf` at the same slots), so the visited-state
bit facts and the gate cost bricks transfer verbatim; the extra `cReverse` pass is `O(m)`. -/

theorem msOf_muStepFn (j p acc : ℕ) : msOf (muStepFn j p acc) = tailL (msOf acc) := by
  simp only [muStepFn, msOf, Nat.unpair_pair]
theorem exOf_muStepFn (j p acc : ℕ) : exOf (muStepFn j p acc) = tailL (exOf acc) := by
  simp only [muStepFn, exOf, Nat.unpair_pair]

theorem inv_msOf_peel_mu (j p mask data i : ℕ) :
    msOf ((muStepFn j p)^[i] (Nat.pair mask (Nat.pair data 0))) = peel mask i := by
  induction i with
  | zero => simp [msOf, peel, Nat.unpair_pair]
  | succ k ih =>
      rw [Function.iterate_succ_apply', msOf_muStepFn, ih]
      simp only [peel, Function.iterate_succ_apply']
theorem inv_exOf_peel_mu (j p mask data i : ℕ) :
    exOf ((muStepFn j p)^[i] (Nat.pair mask (Nat.pair data 0))) = peel data i := by
  induction i with
  | zero => simp [exOf, peel, Nat.unpair_pair]
  | succ k ih =>
      rw [Function.iterate_succ_apply', exOf_muStepFn, ih]
      simp only [peel, Function.iterate_succ_apply']

/-- The `List`-model bit facts at a visited index, stated on the peeled suffixes (shared by the purity
and refine scans, whose suffixes both evolve by `tailL`). -/
theorem peel_bits (n i : ℕ) (hw : WFBits (instOf n))
    (hm : MaskValid (maskOf n) (readM (instOf n))) (hi : i < readM (instOf n)) :
    headL (peel (maskOf n) i) ≤ 1 ∧
    featOf (headL (peel (dataOf n) i)) (jOf n) ≤ 1 ∧
    lblOf (headL (peel (dataOf n) i)) ≤ 1 := by
  obtain ⟨msks, hmeq, hmlen, hmbit⟩ := hm
  obtain ⟨_hwf, exs, hdeq, hdlen, hlbl, hfeat⟩ := hw
  have him : i < msks.length := by rw [hmlen]; exact hi
  have hie : i < exs.length := by rw [hdlen]; exact hi
  refine ⟨?_, ?_, ?_⟩
  · rw [hmeq, getExample_encode msks i him]; exact hmbit _ (List.getElem_mem him)
  · rw [show dataOf n = encodeList exs from hdeq, getExample_encode exs i hie]
    exact hfeat _ (List.getElem_mem hie) (jOf n)
  · rw [show dataOf n = encodeList exs from hdeq, getExample_encode exs i hie]
    exact hlbl _ (List.getElem_mem hie)

theorem visited_bits_mu (n i : ℕ) (hw : WFBits (instOf n))
    (hm : MaskValid (maskOf n) (readM (instOf n))) (hi : i < readM (instOf n)) :
    headL (msOf ((muStepFn (jOf n) (pOf n))^[i]
        (Nat.pair (maskOf n) (Nat.pair (dataOf n) 0)))) ≤ 1 ∧
    featOf (headL (exOf ((muStepFn (jOf n) (pOf n))^[i]
        (Nat.pair (maskOf n) (Nat.pair (dataOf n) 0))))) (jOf n) ≤ 1 := by
  rw [inv_msOf_peel_mu, inv_exOf_peel_mu]
  obtain ⟨h1, h2, _⟩ := peel_bits n i hw hm hi
  exact ⟨h1, h2⟩

/-- **The per-step cost bound** for the refine scan: under bit operands (mask head, feature bit, `p`),
each step costs `≤ 8·(jOf a) + 2400` — only the feature peel scales. -/
theorem tc_cMuStep_le (a i acc : ℕ) (hmask : headL (msOf acc) ≤ 1)
    (hfeat : featOf (headL (exOf acc)) (jOf a) ≤ 1) (hp : pOf a ≤ 1) :
    tc cMuStep (Nat.pair a (Nat.pair i acc)) ≤ 8 * jOf a + 2400 := by
  have hms := tc_cMs_le a i acc
  have hex := tc_cEx_le a i acc
  have hb := tc_cB_le a i acc
  have heqfp := tc_cEqFP_le a i acc hfeat hp
  have hnot := tc_cNot_le (val cEqFP (Nat.pair a (Nat.pair i acc)))
  have heqv : val cEqFP (Nat.pair a (Nat.pair i acc)) ≤ 1 := by rw [vs_cEqFP]; exact bEq_le_one _ _
  have hbv : val cB (Nat.pair a (Nat.pair i acc)) ≤ 1 := by rw [vs_cB]; exact hmask
  have hcnv : val cNot (val cEqFP (Nat.pair a (Nat.pair i acc))) ≤ 1 := val_cNot_le_one _
  have hand := tc_cAnd_le (val cB (Nat.pair a (Nat.pair i acc)))
    (val (comp cNot cEqFP) (Nat.pair a (Nat.pair i acc)))
  have hcc := tc_constCode_le 1 (Nat.pair a (Nat.pair i acc))
  simp only [cMuStep, cNewBit, cMuBuilt, cAcc, tc_pair, tc_comp, tc_cTail, tc_right,
    val_comp, val_pair] at hand ⊢
  omega

/-- The per-visited-step bound, proved (feature/mask bits from `WFBits`/`MaskValid`). -/
theorem hMuStep_visited (n : ℕ) (hw : WFBits (instOf n))
    (hm : MaskValid (maskOf n) (readM (instOf n))) (hp : pOf n ≤ 1) :
    ∀ i, i < readM (instOf n) →
      tc cMuStep (Nat.pair n (Nat.pair i (val (prec cMuInit cMuStep) (Nat.pair n i))))
        ≤ 8 * jOf n + 2400 := by
  intro i hi
  rw [val_cMuLoop]
  obtain ⟨hmask, hfeat⟩ := visited_bits_mu n i hw hm hi
  exact tc_cMuStep_le n i _ hmask hfeat hp

/-- **`cMaskUpdate`'s native cost on a well-formed instance**: base + the `(Bstep+1)·m` scan loop
(`tc_prec_le'` + `hMuStep_visited`) + the `O(m)` `cReverse` pass + `O(1)` shapers. -/
theorem tc_cMaskUpdate_raw (n : ℕ) (hw : WFBits (instOf n))
    (hm : MaskValid (maskOf n) (readM (instOf n))) (hp : pOf n ≤ 1) :
    tc cMaskUpdate n
      ≤ (8 * jOf n + 2400 + 1) * readM (instOf n) + 41 * readM (instOf n) + 100 := by
  have hpair : val (pair cId cCount) n = Nat.pair n (readM (instOf n)) := by
    rw [val_pair, val_cId, val_cCount]
  have hvB : val (pair (comp (comp right right) cMuScan) cCount) n
      = Nat.pair (val (comp (comp right right) cMuScan) n) (readM (instOf n)) := by
    rw [val_pair, val_cCount]
  have e1 : tc cMaskUpdate n
      = tc (pair (comp (comp right right) cMuScan) cCount) n
        + tc cReverse (val (pair (comp (comp right right) cMuScan) cCount) n) + 1 := by
    unfold cMaskUpdate; exact tc_comp cReverse (pair (comp (comp right right) cMuScan) cCount) n
  have e2 : tc (pair (comp (comp right right) cMuScan) cCount) n
      = tc (comp (comp right right) cMuScan) n + tc cCount n + 1 :=
    tc_pair (comp (comp right right) cMuScan) cCount n
  have e3 : tc (comp (comp right right) cMuScan) n
      = tc cMuScan n + tc (comp right right) (val cMuScan n) + 1 :=
    tc_comp (comp right right) cMuScan n
  have e4 : tc cMuScan n
      = tc (pair cId cCount) n + tc (prec cMuInit cMuStep) (val (pair cId cCount) n) + 1 := by
    unfold cMuScan; exact tc_comp (prec cMuInit cMuStep) (pair cId cCount) n
  have brev : tc cReverse (val (pair (comp (comp right right) cMuScan) cCount) n)
      ≤ 41 * readM (instOf n) + 40 := by rw [hvB]; exact tc_cReverse_le _ _
  have brr : tc (comp right right) (val cMuScan n) ≤ 5 := by simp only [tc_comp, tc_right]; omega
  have bprec : tc (prec cMuInit cMuStep) (val (pair cId cCount) n)
      ≤ tc cMuInit n + (8 * jOf n + 2400 + 1) * readM (instOf n) + 1 := by
    rw [hpair]
    exact tc_prec_le' (cf := cMuInit) (cg := cMuStep) (a := n) (B := 8 * jOf n + 2400)
      (readM (instOf n)) (hMuStep_visited n hw hm hp)
  have binit : tc cMuInit n ≤ 11 := by
    simp only [cMuInit, cMask, cData, tc_pair, tc_comp, tc_left, tc_right, tc_zero, val_left,
      val_right]
    omega
  have bidc : tc (pair cId cCount) n ≤ 9 := by
    simp only [cId, cCount, cReadM, cInst, tc_pair, tc_comp, tc_left, tc_right]
    omega
  have bcount : tc cCount n ≤ 5 := by
    simp only [cCount, cReadM, cInst, tc_comp, tc_left, tc_right]
    omega
  rw [e1, e2, e3, e4]
  omega

/-- **`cMaskUpdate` is poly-time on the well-formed domain.** The raw `(Bstep+1)·m + O(m)` bound is
turned poly-bit by `jOf n ≤ readK ≤ size n` and `readM ≤ size n` — a quadratic in `Nat.size n`. -/
theorem polyBoundedOn_tc_cMaskUpdate : PolyBoundedOn PurityWF (tc cMaskUpdate) := by
  refine ⟨6000, 2, fun n hn => ?_⟩
  obtain ⟨hw, hm, hp, hjk⟩ := hn
  have hwf : WF (instOf n) := hw.1
  have hins : Nat.size (instOf n) ≤ Nat.size n := Nat.size_le_size (Nat.unpair_left_le n)
  have hjs : jOf n ≤ Nat.size n := le_trans hjk (le_trans (readK_le_size (instOf n) hwf) hins)
  have hms : readM (instOf n) ≤ Nat.size n := le_trans (readM_le_size (instOf n) hwf) hins
  have hraw := tc_cMaskUpdate_raw n hw hm hp
  have hprod : (8 * jOf n + 2400 + 1) * readM (instOf n) ≤ (8 * Nat.size n + 2401) * Nat.size n :=
    Nat.mul_le_mul (by omega) hms
  nlinarith [hraw, hprod, hms]

/-- `Nat.pair` is jointly monotone (not in Mathlib). -/
theorem pair_mono {a a' b b' : ℕ} (ha : a ≤ a') (hb : b ≤ b') : Nat.pair a b ≤ Nat.pair a' b' := by
  unfold Nat.pair; split_ifs <;> nlinarith [Nat.mul_le_mul ha ha, Nat.mul_le_mul hb hb]

/-- The refined bit never exceeds the old mask bit. -/
theorem updBit_le (j p b e : ℕ) : updBit j p b e ≤ b := by
  unfold updBit bAnd; split_ifs <;> omega

/-- The refined working set is `≤` the old one as a number (elementwise `≤`, `Nat.pair`-monotone). -/
theorem encode_zipWith_updBit_le (j p : ℕ) : ∀ (msks exs : List ℕ), msks.length = exs.length →
    encodeList (List.zipWith (updBit j p) msks exs) ≤ encodeList msks := by
  intro msks
  induction msks with
  | nil => intro exs _; simp [encodeList]
  | cons b bs ih =>
      intro exs hlen
      cases exs with
      | nil => simp at hlen
      | cons e es =>
          have hlen' : bs.length = es.length := by simpa using hlen
          rw [List.zipWith_cons_cons]
          simp only [encodeList]
          exact pair_mono (le_refl 1) (pair_mono (updBit_le j p b e) (ih es hlen'))

/-- On the well-formed domain, `maskUpdate` shrinks the mask (as a number), so its output is poly-bit. -/
theorem maskUpdateVal_le (n : ℕ) (hn : PurityWF n) : maskUpdateVal n ≤ maskOf n := by
  obtain ⟨hw, hm, _hp, _hjk⟩ := hn
  obtain ⟨_hwf, exs, hdeq, hdlen, _, _⟩ := hw
  obtain ⟨msks, hmeq, hmlen, _⟩ := hm
  have heq : maskUpdateVal n = encodeList (List.zipWith (updBit (jOf n) (pOf n)) msks exs) :=
    maskUpdate_eq_encode n msks exs hmeq hdeq hdlen.symm (by rw [hmlen, hdlen])
  rw [heq, hmeq]
  exact encode_zipWith_updBit_le (jOf n) (pOf n) msks exs (by rw [hmlen, hdlen])

theorem polyBoundedOn_size_maskUpdateVal :
    PolyBoundedOn PurityWF (fun n => Nat.size (maskUpdateVal n)) := by
  refine ⟨1, 1, fun n hn => ?_⟩
  have hle : Nat.size (maskUpdateVal n) ≤ Nat.size n :=
    Nat.size_le_size (le_trans (maskUpdateVal_le n hn) (maskOf_le n))
  simp only [pow_one]
  omega

theorem rfindFree_cMuInit : RfindFree cMuInit := by
  simp only [cMuInit, cMask, cData, RfindFree, and_self]
theorem rfindFree_cMuScan : RfindFree cMuScan :=
  ⟨⟨rfindFree_cMuInit, rfindFree_cMuStep⟩, rfindFree_cId, rfindFree_cCount⟩
theorem rfindFree_cMaskUpdate : RfindFree cMaskUpdate :=
  ⟨rfindFree_cReverse, ⟨⟨⟨trivial, trivial⟩, rfindFree_cMuScan⟩, rfindFree_cCount⟩⟩

/-- **`polyTime_maskUpdate`.** Refining the working set by one literal is poly-time on the honest
well-formed domain `PurityWF` — the scan is `O(m·k)`, the `cReverse` pass `O(m)`, and the output
(a length-`m` bit-list) is `≤` the input mask, hence poly-bit. -/
theorem polyTime_maskUpdate : PolyTimeOn PurityWF maskUpdateVal :=
  ⟨cMaskUpdate, rfindFree_cMaskUpdate, fun _ _ => rfl,
    polyBoundedOn_tc_cMaskUpdate, polyBoundedOn_size_maskUpdateVal⟩

/-! ## Layer 7 — `findLit`: pick the first pure literal for the working set

`findLit inst mask` scans literals `(j, p)` with `j < readK inst`, `p ∈ {0,1}` in increasing order and
commits (once) to the first whose purity verdict is pure, packaging `⟨found, j, p, commonLabel⟩`. The
outer loop is a `prec` over `j`; each step invokes `cPurity` twice (`p = 0`, `p = 1`) — a `prec`-in-`prec`
nest — so the per-step cost is `O(m·k)` and `findLit` is `O(m·k²)`, poly on the well-formed domain. The
scan freezes after the first hit (never overwrites), so the recorded literal is genuinely pure. -/

/-! ### A value-mux gate (bit selector) and the purity-verdict field accessors -/

/-- `cMux ⟨⟨x,y⟩, c⟩ = if c = 0 then y else x` — a value selector recursing on the bit `c`, hence
`O(1)`-`tc` on bits regardless of the value operands `x, y`. -/
def cMux : Code := prec right (comp left left)

theorem rfindFree_cMux : RfindFree cMux := ⟨trivial, trivial, trivial⟩

theorem val_cMux (x y c : ℕ) : val cMux (Nat.pair (Nat.pair x y) c) = if c = 0 then y else x := by
  cases c with
  | zero => simp [cMux, val_prec_zero, val_right, Nat.unpair_pair]
  | succ k => simp [cMux, val_prec_succ, val_comp, val_left, Nat.unpair_pair]

theorem tc_cMux_le (x y c : ℕ) : tc cMux (Nat.pair (Nat.pair x y) c) ≤ 4 * c + 2 := by
  unfold cMux
  have h := tc_prec_le (cf := right) (cg := comp left left) (B := 3)
    (fun z => by simp [tc_comp, tc_left]) (Nat.pair x y) c
  simp only [tc_right] at h
  omega

/-- The packed input `⟨inst, mask⟩` of `findLit`. -/
def flInst (N : ℕ) : ℕ := N.unpair.1
def flMask (N : ℕ) : ℕ := N.unpair.2

/-- The accumulator `⟨found, ⟨j, ⟨p, label⟩⟩⟩`. -/
def flFound (acc : ℕ) : ℕ := acc.unpair.1
def flJ (acc : ℕ) : ℕ := acc.unpair.2.unpair.1
def flP (acc : ℕ) : ℕ := acc.unpair.2.unpair.2.unpair.1
def flL (acc : ℕ) : ℕ := acc.unpair.2.unpair.2.unpair.2

/-- Purity verdict of literal `(j,p)` on `(inst, mask)`: is-pure bit (`.1`), common label (`.2.1`), and
covering witness `sawAny` (`.2.2`). -/
def isPureLit (inst mask j p : ℕ) : ℕ := (purityVal (packLit inst mask j p)).unpair.1
def litLabel (inst mask j p : ℕ) : ℕ := (purityVal (packLit inst mask j p)).unpair.2.unpair.1
def sawAnyLit (inst mask j p : ℕ) : ℕ := (purityVal (packLit inst mask j p)).unpair.2.unpair.2
/-- **The greedy selection bit:** literal `(j,p)` is a legal pick iff it is pure AND covers ≥1
remaining example (`isPure ∧ sawAny`). Vacuously-pure (0-covering) literals fail this gate. -/
def coverLit (inst mask j p : ℕ) : ℕ := bAnd (isPureLit inst mask j p) (sawAnyLit inst mask j p)

theorem purityVal_fst (n : ℕ) : (purityVal n).unpair.1
    = bNot (bAnd (z0Of (purityAcc n)) (z1Of (purityAcc n))) := by
  simp only [purityVal, Nat.unpair_pair]
theorem purityVal_snd (n : ℕ) : (purityVal n).unpair.2.unpair.1 = z1Of (purityAcc n) := by
  simp only [purityVal, Nat.unpair_pair]
theorem purityVal_sawAny (n : ℕ) : (purityVal n).unpair.2.unpair.2
    = bOr (z0Of (purityAcc n)) (z1Of (purityAcc n)) := by
  simp only [purityVal, Nat.unpair_pair]
theorem z1_purityAcc_le_one (n : ℕ) : z1Of (purityAcc n) ≤ 1 := by
  unfold purityAcc; exact inv_z1_le_one _ _ _ _ _

theorem isPureLit_le_one (inst mask j p : ℕ) : isPureLit inst mask j p ≤ 1 := by
  unfold isPureLit; rw [purityVal_fst]; exact bNot_le_one _
theorem litLabel_le_one (inst mask j p : ℕ) : litLabel inst mask j p ≤ 1 := by
  unfold litLabel; rw [purityVal_snd]; exact z1_purityAcc_le_one _
theorem sawAnyLit_le_one (inst mask j p : ℕ) : sawAnyLit inst mask j p ≤ 1 := by
  unfold sawAnyLit; rw [purityVal_sawAny]; exact bOr_le_one _ _
theorem coverLit_le_one (inst mask j p : ℕ) : coverLit inst mask j p ≤ 1 := bAnd_le_one _ _

/-- The **folded verdict** `⟨coverLit, litLabel⟩` produced by `cFold`, kept as one opaque atom so the
downstream combine never unification-descends into the symbolic `purityAcc` scan behind `coverLit`. -/
def flVerdict (inst mask j p : ℕ) : ℕ := Nat.pair (coverLit inst mask j p) (litLabel inst mask j p)
theorem flVerdict_fst (inst mask j p : ℕ) :
    (flVerdict inst mask j p).unpair.1 = coverLit inst mask j p := by
  simp only [flVerdict, Nat.unpair_pair]
theorem flVerdict_snd (inst mask j p : ℕ) :
    (flVerdict inst mask j p).unpair.2 = litLabel inst mask j p := by
  simp only [flVerdict, Nat.unpair_pair]
theorem flVerdict_le_one_fst (inst mask j p : ℕ) : (flVerdict inst mask j p).unpair.1 ≤ 1 := by
  rw [flVerdict_fst]; exact coverLit_le_one _ _ _ _

/-- **The greedy step at index `i`.** Commit to `(i,0)`/`(i,1)` if not yet found and that literal is a
**covering pure** pick (`coverLit`, prefer `p = 0`); otherwise freeze. Written in mux normal form
(`if cond = 0 then … else …`). -/
def flStepFn (inst mask i acc : ℕ) : ℕ :=
  Nat.pair (bOr (flFound acc) (bOr (coverLit inst mask i 0) (coverLit inst mask i 1)))
    (Nat.pair
      (if bAnd (bNot (flFound acc)) (bOr (coverLit inst mask i 0) (coverLit inst mask i 1)) = 0
        then flJ acc else i)
      (Nat.pair
        (if bAnd (bAnd (bNot (flFound acc)) (coverLit inst mask i 1)) (bNot (coverLit inst mask i 0)) = 0
          then (if bAnd (bNot (flFound acc)) (coverLit inst mask i 0) = 0 then flP acc else 0)
          else 1)
        (if bAnd (bNot (flFound acc)) (bOr (coverLit inst mask i 0) (coverLit inst mask i 1)) = 0
          then flL acc
          else (if bAnd (bAnd (bNot (flFound acc)) (coverLit inst mask i 1))
                        (bNot (coverLit inst mask i 0)) = 0
                then litLabel inst mask i 0 else litLabel inst mask i 1))))

theorem flFound_step (inst mask i acc : ℕ) : flFound (flStepFn inst mask i acc)
    = bOr (flFound acc) (bOr (coverLit inst mask i 0) (coverLit inst mask i 1)) := by
  simp only [flStepFn, flFound, Nat.unpair_pair]
theorem flJ_step (inst mask i acc : ℕ) : flJ (flStepFn inst mask i acc)
    = (if bAnd (bNot (flFound acc)) (bOr (coverLit inst mask i 0) (coverLit inst mask i 1)) = 0
        then flJ acc else i) := by
  simp only [flStepFn, flJ, Nat.unpair_pair]
theorem flP_step (inst mask i acc : ℕ) : flP (flStepFn inst mask i acc)
    = (if bAnd (bAnd (bNot (flFound acc)) (coverLit inst mask i 1)) (bNot (coverLit inst mask i 0)) = 0
        then (if bAnd (bNot (flFound acc)) (coverLit inst mask i 0) = 0 then flP acc else 0)
        else 1) := by
  simp only [flStepFn, flP, Nat.unpair_pair]
theorem flL_step (inst mask i acc : ℕ) : flL (flStepFn inst mask i acc)
    = (if bAnd (bNot (flFound acc)) (bOr (coverLit inst mask i 0) (coverLit inst mask i 1)) = 0
        then flL acc
        else (if bAnd (bAnd (bNot (flFound acc)) (coverLit inst mask i 1))
                      (bNot (coverLit inst mask i 0)) = 0
              then litLabel inst mask i 0 else litLabel inst mask i 1)) := by
  simp only [flStepFn, flL, Nat.unpair_pair]

/-! ### The step code: `cExpand` (two purity calls) then `cCombine` (bit-logic + muxes) -/

/-- `cFold ⟨isPure, ⟨label, sawAny⟩⟩ = ⟨isPure ∧ sawAny, label⟩` — collapse a 3-field purity verdict
into the 2-field `⟨coverLit, litLabel⟩` the greedy combine consumes. Doing the covering `∧` here (not in
`cCombine`) keeps `cPurity` an honest purity primitive and leaves `cCombine` unchanged. -/
def cFold : Code := pair (comp cAnd (pair left (comp right right))) (comp left right)

/-- `cExpand ⟨N,⟨i,acc⟩⟩ = ⟨i, ⟨acc, ⟨⟨cover0,label0⟩, ⟨cover1,label1⟩⟩⟩⟩` — compute both purity
verdicts ONCE (exactly two `cPurity` evaluations), fold each to its covering-pick bit, so the per-step
cost is `2·(purity) + O(1)`. -/
def cInstN : Code := comp left left
def cMaskN : Code := comp right left
def cIX : Code := comp left right
def cAccX : Code := comp right right
def cPack0 : Code := pair cInstN (pair cMaskN (pair cIX zero))
def cPack1 : Code := pair cInstN (pair cMaskN (pair cIX (constCode 1)))
def cExpand : Code :=
  pair cIX (pair cAccX (pair (comp cFold (comp cPurity cPack0)) (comp cFold (comp cPurity cPack1))))

theorem val_cExpand (a i acc : ℕ) :
    val cExpand (Nat.pair a (Nat.pair i acc))
      = Nat.pair i (Nat.pair acc
          (Nat.pair (flVerdict (flInst a) (flMask a) i 0) (flVerdict (flInst a) (flMask a) i 1))) := by
  simp only [cExpand, cFold, cIX, cAccX, cInstN, cMaskN, cPack0, cPack1, val_pair, val_comp, val_left,
    val_right, val_cAnd', val_cPurity, val_constCode, val_zero, Nat.unpair_pair, flVerdict, coverLit,
    isPureLit, sawAnyLit, litLabel, packLit, flInst, flMask]

/-- `cCombine ⟨i,⟨acc,⟨v0,v1⟩⟩⟩` — the greedy update, reading the already-computed verdicts `v0,v1`.
All gates and muxes are `O(1)` on the bit fields (the only value operands, `i`/`jR`, feed muxes whose
cost is selector-only). -/
def ccAcc : Code := comp left right
def ccV0 : Code := comp left (comp right right)
def ccV1 : Code := comp right (comp right right)
def ccFound : Code := comp left ccAcc
def ccJ : Code := comp left (comp right ccAcc)
def ccP : Code := comp left (comp right (comp right ccAcc))
def ccL : Code := comp right (comp right (comp right ccAcc))
def ccIsP0 : Code := comp left ccV0
def ccLab0 : Code := comp right ccV0
def ccIsP1 : Code := comp left ccV1
def ccLab1 : Code := comp right ccV1
def ccNF : Code := comp cNot ccFound
def ccAny : Code := comp cOr (pair ccIsP0 ccIsP1)
def ccNew : Code := comp cAnd (pair ccNF ccAny)
def ccC0 : Code := comp cAnd (pair ccNF ccIsP0)
def ccC1 : Code := comp cAnd (pair (comp cAnd (pair ccNF ccIsP1)) (comp cNot ccIsP0))
def ccFound' : Code := comp cOr (pair ccFound ccAny)
def ccJ' : Code := comp cMux (pair (pair left ccJ) ccNew)
def ccPin : Code := comp cMux (pair (pair zero ccP) ccC0)
def ccP' : Code := comp cMux (pair (pair (constCode 1) ccPin) ccC1)
def ccChosen : Code := comp cMux (pair (pair ccLab1 ccLab0) ccC1)
def ccL' : Code := comp cMux (pair (pair ccChosen ccL) ccNew)
def cCombine : Code := pair ccFound' (pair ccJ' (pair ccP' ccL'))

theorem val_cCombine (i acc v0 v1 : ℕ) :
    val cCombine (Nat.pair i (Nat.pair acc (Nat.pair v0 v1)))
      = Nat.pair (bOr (flFound acc) (bOr v0.unpair.1 v1.unpair.1))
        (Nat.pair (if bAnd (bNot (flFound acc)) (bOr v0.unpair.1 v1.unpair.1) = 0 then flJ acc else i)
          (Nat.pair (if bAnd (bAnd (bNot (flFound acc)) v1.unpair.1) (bNot v0.unpair.1) = 0
              then (if bAnd (bNot (flFound acc)) v0.unpair.1 = 0 then flP acc else 0) else 1)
            (if bAnd (bNot (flFound acc)) (bOr v0.unpair.1 v1.unpair.1) = 0 then flL acc
              else (if bAnd (bAnd (bNot (flFound acc)) v1.unpair.1) (bNot v0.unpair.1) = 0
                    then v0.unpair.2 else v1.unpair.2)))) := by
  simp only [cCombine, ccFound', ccJ', ccP', ccL', ccPin, ccChosen, ccJ, ccP, ccL, ccFound,
    ccIsP0, ccLab0, ccIsP1, ccLab1, ccNF, ccAny, ccNew, ccC0, ccC1, ccAcc, ccV0, ccV1,
    val_pair, val_comp, val_left, val_right, val_zero, val_constCode, val_cMux, val_cNot', val_cAnd',
    val_cOr', Nat.unpair_pair, flFound, flJ, flP, flL]
  rfl

def cFlStep : Code := comp cCombine cExpand

theorem val_cFlStep (a i acc : ℕ) :
    val cFlStep (Nat.pair a (Nat.pair i acc)) = flStepFn (flInst a) (flMask a) i acc := by
  rw [cFlStep, val_comp, val_cExpand, val_cCombine, flStepFn]
  -- `flVerdict` stays opaque; project it with the explicit field lemmas (no `whnf` blow-up into the
  -- symbolic `purityAcc` scan behind `coverLit`).
  simp only [flVerdict_fst, flVerdict_snd]

/-- Base code: the constant zero accumulator `⟨0, ⟨0, ⟨0, 0⟩⟩⟩`. -/
def cFlInit : Code := pair zero (pair zero (pair zero zero))
theorem val_cFlInit (N : ℕ) : val cFlInit N = Nat.pair 0 (Nat.pair 0 (Nat.pair 0 0)) := by
  simp only [cFlInit, val_pair, val_zero]

/-- The greedy scan accumulator after `t` literal-rounds. -/
def flAcc (N t : ℕ) : ℕ := val (prec cFlInit cFlStep) (Nat.pair N t)

theorem flAcc_zero (N : ℕ) : flAcc N 0 = Nat.pair 0 (Nat.pair 0 (Nat.pair 0 0)) := by
  unfold flAcc; rw [val_prec_zero, val_cFlInit]
theorem flAcc_succ (N t : ℕ) : flAcc N (t + 1) = flStepFn (flInst N) (flMask N) t (flAcc N t) := by
  unfold flAcc; rw [val_prec_succ, val_cFlStep]

/-! ### Correctness of the greedy scan -/

/-- **Completeness.** After `t` rounds, `found` fires iff some literal `(i, ·)` with `i < t` is a
covering pure pick (pure AND covering ≥1 remaining example). -/
theorem flComplete (N t : ℕ) :
    flFound (flAcc N t) ≠ 0 ↔
      ∃ i < t, coverLit (flInst N) (flMask N) i 0 ≠ 0 ∨ coverLit (flInst N) (flMask N) i 1 ≠ 0 := by
  induction t with
  | zero =>
      rw [flAcc_zero]
      simp only [flFound, Nat.unpair_pair, ne_eq, not_lt_zero, false_and, exists_false, iff_false,
        not_not]
  | succ k ih =>
      rw [flAcc_succ, flFound_step, bOr_ne_zero, bOr_ne_zero, ih]
      constructor
      · rintro (⟨i, hi, h⟩ | h)
        · exact ⟨i, Nat.lt_succ_of_lt hi, h⟩
        · exact ⟨k, Nat.lt_succ_self k, h⟩
      · rintro ⟨i, hi, h⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | rfl
        · exact Or.inl ⟨i, hlt, h⟩
        · exact Or.inr h

theorem bNot_pos_of_ne {n : ℕ} (h : n ≠ 0) : bNot n = 0 := by unfold bNot; simp [h]

/-- **Soundness.** If `found` fires, the recorded `⟨j, p⟩` is a valid literal (`j < t`, `p` a bit), a
**covering pure** pick, and `label` is its common label. The scan freezes after the first hit. -/
theorem flSound (N : ℕ) : ∀ t, flFound (flAcc N t) ≠ 0 →
    flJ (flAcc N t) < t ∧ flP (flAcc N t) ≤ 1 ∧
    coverLit (flInst N) (flMask N) (flJ (flAcc N t)) (flP (flAcc N t)) ≠ 0 ∧
    flL (flAcc N t) = litLabel (flInst N) (flMask N) (flJ (flAcc N t)) (flP (flAcc N t)) := by
  intro t
  induction t with
  | zero => rw [flAcc_zero]; intro h; simp [flFound, Nat.unpair_pair] at h
  | succ k ih =>
      rw [flAcc_succ]
      intro h
      set inst := flInst N
      set mask := flMask N
      set acc := flAcc N k with hacc
      rw [flFound_step] at h
      by_cases hf : flFound acc = 0
      · -- newly found at round k
        rw [hf] at h
        have hany : bOr (coverLit inst mask k 0) (coverLit inst mask k 1) ≠ 0 :=
          ((bOr_ne_zero _ _).mp h).resolve_left (by simp)
        have hbnot : bNot (flFound acc) = 1 := by rw [hf]; rfl
        have hnew : bAnd (bNot (flFound acc))
            (bOr (coverLit inst mask k 0) (coverLit inst mask k 1)) ≠ 0 := by
          rw [hbnot, bAnd_ne_zero]; exact ⟨one_ne_zero, hany⟩
        by_cases hp0 : coverLit inst mask k 0 = 0
        · -- commit p = 1
          have hp1 : coverLit inst mask k 1 ≠ 0 := by
            rw [hp0] at hany; exact ((bOr_ne_zero _ _).mp hany).resolve_left (by simp)
          have hc1 : bAnd (bAnd (bNot (flFound acc)) (coverLit inst mask k 1))
              (bNot (coverLit inst mask k 0)) ≠ 0 := by
            rw [hbnot, hp0, bAnd_ne_zero, bAnd_ne_zero]
            exact ⟨⟨one_ne_zero, hp1⟩, by decide⟩
          have hJ : flJ (flStepFn inst mask k acc) = k := by rw [flJ_step, if_neg hnew]
          have hP : flP (flStepFn inst mask k acc) = 1 := by rw [flP_step, if_neg hc1]
          have hL : flL (flStepFn inst mask k acc) = litLabel inst mask k 1 := by
            rw [flL_step, if_neg hnew, if_neg hc1]
          rw [hJ, hP, hL]
          exact ⟨Nat.lt_succ_self k, le_refl 1, hp1, rfl⟩
        · -- commit p = 0
          have hc0 : bAnd (bNot (flFound acc)) (coverLit inst mask k 0) ≠ 0 := by
            rw [hbnot, bAnd_ne_zero]; exact ⟨one_ne_zero, hp0⟩
          have hc1 : bAnd (bAnd (bNot (flFound acc)) (coverLit inst mask k 1))
              (bNot (coverLit inst mask k 0)) = 0 := by
            rw [bAnd_eq_zero]; exact Or.inr (bNot_pos_of_ne hp0)
          have hJ : flJ (flStepFn inst mask k acc) = k := by rw [flJ_step, if_neg hnew]
          have hP : flP (flStepFn inst mask k acc) = 0 := by rw [flP_step, if_pos hc1, if_neg hc0]
          have hL : flL (flStepFn inst mask k acc) = litLabel inst mask k 0 := by
            rw [flL_step, if_neg hnew, if_pos hc1]
          rw [hJ, hP, hL]
          exact ⟨Nat.lt_succ_self k, Nat.zero_le 1, hp0, rfl⟩
      · -- already found: freeze and reuse ih
        have hbnot0 : bNot (flFound acc) = 0 := bNot_pos_of_ne hf
        have hnew0 : bAnd (bNot (flFound acc))
            (bOr (coverLit inst mask k 0) (coverLit inst mask k 1)) = 0 := by
          rw [bAnd_eq_zero]; exact Or.inl hbnot0
        have hc0 : bAnd (bNot (flFound acc)) (coverLit inst mask k 0) = 0 := by
          rw [bAnd_eq_zero]; exact Or.inl hbnot0
        have hc1 : bAnd (bAnd (bNot (flFound acc)) (coverLit inst mask k 1))
            (bNot (coverLit inst mask k 0)) = 0 := by
          rw [bAnd_eq_zero]; exact Or.inl (by rw [bAnd_eq_zero]; exact Or.inl hbnot0)
        have hJ : flJ (flStepFn inst mask k acc) = flJ acc := by rw [flJ_step, if_pos hnew0]
        have hP : flP (flStepFn inst mask k acc) = flP acc := by
          rw [flP_step, if_pos hc1, if_pos hc0]
        have hL : flL (flStepFn inst mask k acc) = flL acc := by rw [flL_step, if_pos hnew0]
        rw [hJ, hP, hL]
        obtain ⟨h1, h2, h3, h4⟩ := ih hf
        exact ⟨Nat.lt_succ_of_lt h1, h2, h3, h4⟩

/-! ### The assembled `findLit` and its top-level correctness -/

/-- The literal count `readK (flInst N)`. -/
def cFlCount : Code := comp left left
theorem val_cFlCount (N : ℕ) : val cFlCount N = readK (flInst N) := by
  simp only [cFlCount, val_comp, val_left, readK, flInst]
/-- **`findLit`'s code**: run the greedy scan `readK inst` rounds. -/
def cFindLit : Code := comp (prec cFlInit cFlStep) (pair cId cFlCount)
def findLitVal (N : ℕ) : ℕ := val cFindLit N

theorem findLitVal_eq (N : ℕ) : findLitVal N = flAcc N (readK (flInst N)) := by
  unfold findLitVal cFindLit flAcc
  rw [val_comp, val_pair, val_cId, val_cFlCount]

/-- **The well-formed domain for `findLit`.** -/
def FindLitWF (N : ℕ) : Prop := WFBits (flInst N) ∧ MaskValid (flMask N) (readM (flInst N))

/-- **`findLit` completeness (covering form).** `found` fires iff some literal `(j, ·)` with
`j < readK inst` is a **covering pure** pick — pure AND covering ≥1 remaining example. -/
theorem findLit_found_iff (N : ℕ) :
    flFound (findLitVal N) ≠ 0 ↔ ∃ i < readK (flInst N),
      coverLit (flInst N) (flMask N) i 0 ≠ 0 ∨ coverLit (flInst N) (flMask N) i 1 ≠ 0 := by
  rw [findLitVal_eq]; exact flComplete N (readK (flInst N))

/-- **`findLit` soundness (covering form).** If `found`, the recorded `⟨j, p, label⟩` is a valid literal
(`j < readK inst`, `p` a bit) that is a **covering pure** pick (`coverLit ≠ 0`, i.e. pure AND covering
≥1 remaining example — see `coverLit_covers`) with its common `label`. -/
theorem findLit_sound (N : ℕ) (h : flFound (findLitVal N) ≠ 0) :
    flJ (findLitVal N) < readK (flInst N) ∧ flP (findLitVal N) ≤ 1 ∧
    coverLit (flInst N) (flMask N) (flJ (findLitVal N)) (flP (findLitVal N)) ≠ 0 ∧
    flL (findLitVal N) = litLabel (flInst N) (flMask N) (flJ (findLitVal N)) (flP (findLitVal N)) := by
  rw [findLitVal_eq] at h ⊢; exact flSound N (readK (flInst N)) h

/-- **The covering witness, unpacked for C2c.** A covering-pure literal `(j,p)` on a bit-well-formed
instance with a valid mask genuinely **covers ≥1 remaining example** — some still-unmasked example whose
feature `j` matches `p`. This is what makes the greedy count-decrease measure (`updBit_le`) strict, so
`maskUpdate` zeroes ≥1 mask bit each covering round. (C2c consumes this together with `findLit_sound`.) -/
theorem coverLit_covers (inst mask j p : ℕ) (hw : WFBits inst)
    (hm : MaskValid mask (readM inst)) (hcov : coverLit inst mask j p ≠ 0) :
    ∃ msks exs : List ℕ, mask = encodeList msks ∧ readData inst = encodeList exs ∧
      msks.length = exs.length ∧ readM inst = exs.length ∧
      ∃ be ∈ msks.zip exs, Covered j p be := by
  obtain ⟨_hwf, exs, hdeq, hdlen, _hlbl, _hfeat⟩ := hw
  obtain ⟨msks, hmeq, hmlen, _hmbit⟩ := hm
  refine ⟨msks, exs, hmeq, hdeq, by rw [hmlen, hdlen], hdlen.symm, ?_⟩
  have hsaw : sawAnyLit inst mask j p ≠ 0 := by
    have := hcov; unfold coverLit at this; rw [bAnd_ne_zero] at this; exact this.2
  have hpack : (purityVal (packLit inst mask j p)).unpair.2.unpair.2 ≠ 0 := hsaw
  have := (purity_sawAny (packLit inst mask j p) msks exs
    (by rw [maskOf_packLit]; exact hmeq)
    (by rw [dataOf_packLit]; exact hdeq)
    (by rw [instOf_packLit]; exact hdlen.symm)
    (by rw [hmlen, hdlen])).mp
  rw [jOf_packLit, pOf_packLit] at this
  exact this hpack

/-! ### Accumulator invariants (for the cost/size bounds) -/

theorem flFound_le_one (N t : ℕ) : flFound (flAcc N t) ≤ 1 := by
  cases t with
  | zero => rw [flAcc_zero]; simp [flFound, Nat.unpair_pair]
  | succ k => rw [flAcc_succ, flFound_step]; exact bOr_le_one _ _
theorem flP_le_one (N t : ℕ) : flP (flAcc N t) ≤ 1 := by
  induction t with
  | zero => rw [flAcc_zero]; simp [flP, Nat.unpair_pair]
  | succ k ih => rw [flAcc_succ, flP_step]; split_ifs <;> omega
theorem flL_le_one (N t : ℕ) : flL (flAcc N t) ≤ 1 := by
  induction t with
  | zero => rw [flAcc_zero]; simp [flL, Nat.unpair_pair]
  | succ k ih =>
      rw [flAcc_succ, flL_step]
      split_ifs
      · exact ih
      · exact litLabel_le_one _ _ _ _
      · exact litLabel_le_one _ _ _ _
theorem flJ_le (N t : ℕ) : flJ (flAcc N t) ≤ t := by
  induction t with
  | zero => rw [flAcc_zero]; simp [flJ, Nat.unpair_pair]
  | succ k ih => rw [flAcc_succ, flJ_step]; split <;> omega

/-! ### The per-step cost: two purity calls (`cExpand`) plus an `O(1)` combine -/

theorem val_cPack0 (a i acc : ℕ) :
    val cPack0 (Nat.pair a (Nat.pair i acc)) = packLit (flInst a) (flMask a) i 0 := by
  simp only [cPack0, cInstN, cMaskN, cIX, val_pair, val_comp, val_left, val_right, val_zero,
    Nat.unpair_pair, packLit, flInst, flMask]
theorem val_cPack1 (a i acc : ℕ) :
    val cPack1 (Nat.pair a (Nat.pair i acc)) = packLit (flInst a) (flMask a) i 1 := by
  simp only [cPack1, cInstN, cMaskN, cIX, val_pair, val_comp, val_left, val_right, val_constCode,
    Nat.unpair_pair, packLit, flInst, flMask]
theorem tc_cPack0_le (a i acc : ℕ) : tc cPack0 (Nat.pair a (Nat.pair i acc)) ≤ 13 := by
  simp only [cPack0, cInstN, cMaskN, cIX, tc_pair, tc_comp, tc_left, tc_right, tc_zero]; omega
theorem tc_cPack1_le (a i acc : ℕ) : tc cPack1 (Nat.pair a (Nat.pair i acc)) ≤ 15 := by
  have := tc_constCode_le 1 (Nat.pair a (Nat.pair i acc))
  simp only [cPack1, cInstN, cMaskN, cIX, tc_pair, tc_comp, tc_left, tc_right]; omega

/-- The verdict fold `cFold` is `O(1)`-`tc` on a bit-flagged verdict (its two `cAnd` operands — the
`isPure` and `sawAny` fields — are bits). -/
theorem tc_cFold_le (V : ℕ) (h1 : V.unpair.1 ≤ 1) (h2 : V.unpair.2.unpair.2 ≤ 1) :
    tc cFold V ≤ 250 := by
  have hand := tc_cAnd_le V.unpair.1 V.unpair.2.unpair.2
  simp only [cFold, tc_pair, tc_comp, tc_left, tc_right, val_comp, val_pair, val_left, val_right]
  omega

theorem tc_cExpand_le (a i acc : ℕ) :
    tc cExpand (Nat.pair a (Nat.pair i acc))
      ≤ tc cPurity (packLit (flInst a) (flMask a) i 0)
        + tc cPurity (packLit (flInst a) (flMask a) i 1) + 541 := by
  have hp0 := val_cPack0 a i acc
  have hp1 := val_cPack1 a i acc
  have ht0 := tc_cPack0_le a i acc
  have ht1 := tc_cPack1_le a i acc
  have hf0 : tc cFold (purityVal (packLit (flInst a) (flMask a) i 0)) ≤ 250 :=
    tc_cFold_le _ (by rw [purityVal_fst]; exact bNot_le_one _)
                  (by rw [purityVal_sawAny]; exact bOr_le_one _ _)
  have hf1 : tc cFold (purityVal (packLit (flInst a) (flMask a) i 1)) ≤ 250 :=
    tc_cFold_le _ (by rw [purityVal_fst]; exact bNot_le_one _)
                  (by rw [purityVal_sawAny]; exact bOr_le_one _ _)
  simp only [cExpand, cIX, cAccX, tc_pair, tc_comp, tc_left, tc_right, val_comp, val_cPurity, hp0, hp1]
  omega

/-- Every mux runs on a bit selector (`bAnd`/`bOr` output), so it is `O(1)`-`tc` — uniformly in `W`. -/
theorem tc_cMux_le' (W : ℕ) : tc cMux W ≤ 4 * W.unpair.2 + 2 := by
  have h := tc_prec_le (cf := right) (cg := comp left left) (B := 3)
    (fun z => by simp [tc_comp, tc_left]) W.unpair.1 W.unpair.2
  rw [Nat.pair_unpair] at h
  simp only [tc_right] at h
  unfold cMux
  omega

theorem tc_cMux_bit (x y c : ℕ) (hc : c ≤ 1) : tc cMux (Nat.pair (Nat.pair x y) c) ≤ 6 := by
  have := tc_cMux_le' (Nat.pair (Nat.pair x y) c); rw [Nat.unpair_pair] at this; omega

theorem tc_cCombine_le (i acc v0 v1 : ℕ)
    (hf : acc.unpair.1 ≤ 1) (h0 : v0.unpair.1 ≤ 1) (h1 : v1.unpair.1 ≤ 1) :
    tc cCombine (Nat.pair i (Nat.pair acc (Nat.pair v0 v1))) ≤ 4000 := by
  have bnot_acc : bNot acc.unpair.1 ≤ 1 := bNot_le_one _
  have bnot_v0 : bNot v0.unpair.1 ≤ 1 := bNot_le_one _
  have bor : bOr v0.unpair.1 v1.unpair.1 ≤ 1 := bOr_le_one _ _
  have band1 : bAnd (bNot acc.unpair.1) v1.unpair.1 ≤ 1 := bAnd_le_one _ _
  have ho1 := tc_cOr_le v0.unpair.1 v1.unpair.1
  have ho2 := tc_cOr_le acc.unpair.1 (bOr v0.unpair.1 v1.unpair.1)
  have hn1 := tc_cNot_le acc.unpair.1
  have hn2 := tc_cNot_le v0.unpair.1
  have ha1 := tc_cAnd_le (bNot acc.unpair.1) (bOr v0.unpair.1 v1.unpair.1)
  have ha2 := tc_cAnd_le (bNot acc.unpair.1) v0.unpair.1
  have ha3 := tc_cAnd_le (bNot acc.unpair.1) v1.unpair.1
  have ha4 := tc_cAnd_le (bAnd (bNot acc.unpair.1) v1.unpair.1) (bNot v0.unpair.1)
  have hcc := tc_constCode_le 1 (Nat.pair i (Nat.pair acc (Nat.pair v0 v1)))
  have m1 := tc_cMux_bit i acc.unpair.2.unpair.1
    (bAnd (bNot acc.unpair.1) (bOr v0.unpair.1 v1.unpair.1)) (bAnd_le_one _ _)
  have m2 := tc_cMux_bit 0 acc.unpair.2.unpair.2.unpair.1
    (bAnd (bNot acc.unpair.1) v0.unpair.1) (bAnd_le_one _ _)
  have m3 := tc_cMux_bit 1
    (val cMux (Nat.pair (Nat.pair 0 acc.unpair.2.unpair.2.unpair.1)
      (bAnd (bNot acc.unpair.1) v0.unpair.1)))
    (bAnd (bAnd (bNot acc.unpair.1) v1.unpair.1) (bNot v0.unpair.1)) (bAnd_le_one _ _)
  have m4 := tc_cMux_bit v1.unpair.2 v0.unpair.2
    (bAnd (bAnd (bNot acc.unpair.1) v1.unpair.1) (bNot v0.unpair.1)) (bAnd_le_one _ _)
  have m5 := tc_cMux_bit
    (val cMux (Nat.pair (Nat.pair v1.unpair.2 v0.unpair.2)
      (bAnd (bAnd (bNot acc.unpair.1) v1.unpair.1) (bNot v0.unpair.1))))
    acc.unpair.2.unpair.2.unpair.2
    (bAnd (bNot acc.unpair.1) (bOr v0.unpair.1 v1.unpair.1)) (bAnd_le_one _ _)
  simp only [cCombine, ccFound', ccJ', ccP', ccL', ccPin, ccChosen, ccNF, ccAny, ccNew, ccC0, ccC1,
    ccFound, ccJ, ccP, ccL, ccIsP0, ccLab0, ccIsP1, ccLab1, ccAcc, ccV0, ccV1,
    tc_pair, tc_comp, tc_left, tc_right, tc_zero, val_pair, val_comp, val_left, val_right, val_zero,
    val_constCode, val_cNot', val_cAnd', val_cOr', Nat.unpair_pair]
  omega

/-- **The per-step cost**: two purity calls, the two `O(1)` verdict folds, plus the `O(1)` combine. -/
theorem tc_cFlStep_le (a i acc : ℕ) (hf : flFound acc ≤ 1) :
    tc cFlStep (Nat.pair a (Nat.pair i acc))
      ≤ tc cPurity (packLit (flInst a) (flMask a) i 0)
        + tc cPurity (packLit (flInst a) (flMask a) i 1) + 4542 := by
  have hexp := tc_cExpand_le a i acc
  -- `flVerdict` stays opaque, so `omega` sees `tc cCombine`/`tc cExpand` as atoms (no `whnf` descent
  -- into the symbolic `purityAcc` scan behind `coverLit`).
  have hcomb := tc_cCombine_le i acc (flVerdict (flInst a) (flMask a) i 0)
    (flVerdict (flInst a) (flMask a) i 1) hf
    (flVerdict_le_one_fst _ _ _ _) (flVerdict_le_one_fst _ _ _ _)
  unfold cFlStep
  rw [tc_comp, val_cExpand]
  omega

/-- The per-round budget: `2·(purity cost) + O(1)` = `O(m·k)`. -/
def BstepFL (N : ℕ) : ℕ := 2 * ((16 * readK (flInst N) + 5701) * readM (flInst N) + 400) + 4542

/-- **Per-visited-round bound.** On the well-formed domain each round costs `≤ BstepFL N`. -/
theorem hFlStep_visited (N : ℕ) (hw : WFBits (flInst N))
    (hm : MaskValid (flMask N) (readM (flInst N))) :
    ∀ i, i < readK (flInst N) →
      tc cFlStep (Nat.pair N (Nat.pair i (val (prec cFlInit cFlStep) (Nat.pair N i))))
        ≤ BstepFL N := by
  intro i hi
  have hstep := tc_cFlStep_le N i (val (prec cFlInit cFlStep) (Nat.pair N i)) (flFound_le_one N i)
  have hp0 := tc_cPurity_raw (packLit (flInst N) (flMask N) i 0)
    (by rw [instOf_packLit]; exact hw) (by rw [maskOf_packLit, instOf_packLit]; exact hm)
    (by rw [pOf_packLit]; exact Nat.zero_le 1)
  have hp1 := tc_cPurity_raw (packLit (flInst N) (flMask N) i 1)
    (by rw [instOf_packLit]; exact hw) (by rw [maskOf_packLit, instOf_packLit]; exact hm)
    (by rw [pOf_packLit])
  rw [jOf_packLit, instOf_packLit] at hp0 hp1
  have hmono0 : (16 * i + 5700 + 1) * readM (flInst N)
      ≤ (16 * readK (flInst N) + 5701) * readM (flInst N) := Nat.mul_le_mul (by omega) (le_refl _)
  have hmono1 : (16 * i + 5700 + 1) * readM (flInst N)
      ≤ (16 * readK (flInst N) + 5701) * readM (flInst N) := hmono0
  unfold BstepFL
  omega

/-- **`cFindLit`'s native cost on a well-formed instance**: base + the `(BstepFL+1)·k` scan loop. -/
theorem tc_cFindLit_raw (N : ℕ) (hw : WFBits (flInst N))
    (hm : MaskValid (flMask N) (readM (flInst N))) :
    tc cFindLit N
      ≤ tc cFlInit N + (BstepFL N + 1) * readK (flInst N) + 1 + tc (pair cId cFlCount) N + 1 := by
  have hpair : val (pair cId cFlCount) N = Nat.pair N (readK (flInst N)) := by
    rw [val_pair, val_cId, val_cFlCount]
  have hprec := tc_prec_le' (cf := cFlInit) (cg := cFlStep) (a := N) (B := BstepFL N)
    (readK (flInst N)) (hFlStep_visited N hw hm)
  have e : tc cFindLit N
      = tc (pair cId cFlCount) N + tc (prec cFlInit cFlStep) (val (pair cId cFlCount) N) + 1 := by
    unfold cFindLit; exact tc_comp (prec cFlInit cFlStep) (pair cId cFlCount) N
  rw [e, hpair]
  omega

/-- **`cFindLit` is poly-time on the well-formed domain** — a cubic in `Nat.size N`
(`k` rounds × `O(m·k)` per round). -/
theorem polyBoundedOn_tc_cFindLit : PolyBoundedOn FindLitWF (tc cFindLit) := by
  refine ⟨12000, 3, fun N hN => ?_⟩
  obtain ⟨hw, hm⟩ := hN
  have hk : readK (flInst N) ≤ Nat.size N :=
    le_trans (readK_le_size (flInst N) hw.1) (Nat.size_le_size (Nat.unpair_left_le N))
  have hmm : readM (flInst N) ≤ Nat.size N :=
    le_trans (readM_le_size (flInst N) hw.1) (Nat.size_le_size (Nat.unpair_left_le N))
  have hraw := tc_cFindLit_raw N hw hm
  have hinit : tc cFlInit N ≤ 13 := by simp only [cFlInit, tc_pair, tc_zero]; omega
  have hidc : tc (pair cId cFlCount) N ≤ 10 := by
    simp only [cId, cFlCount, tc_pair, tc_comp, tc_left, tc_right]; omega
  have hbstep : BstepFL N + 1 ≤ 32 * Nat.size N ^ 2 + 11402 * Nat.size N + 5343 := by
    have hmul := Nat.mul_le_mul
      (show 16 * readK (flInst N) + 5701 ≤ 16 * Nat.size N + 5701 by omega) hmm
    unfold BstepFL; nlinarith [hmul]
  have hprod : (BstepFL N + 1) * readK (flInst N)
      ≤ (32 * Nat.size N ^ 2 + 11402 * Nat.size N + 5343) * Nat.size N := Nat.mul_le_mul hbstep hk
  have hcube : (32 * Nat.size N ^ 2 + 11402 * Nat.size N + 5343) * Nat.size N
      ≤ 12000 * (Nat.size N + 1) ^ 3 := by nlinarith [Nat.zero_le (Nat.size N)]
  omega

/-- The output `⟨found, j, p, label⟩` is poly-bit: three bits and an index `j ≤ readK ≤ size N`. -/
theorem size_le_self (m : ℕ) : Nat.size m ≤ m := Nat.size_le.mpr Nat.lt_two_pow_self

theorem flAcc_decompose (x : ℕ) :
    x = Nat.pair (flFound x) (Nat.pair (flJ x) (Nat.pair (flP x) (flL x))) := by
  simp only [flFound, flJ, flP, flL, Nat.pair_unpair]

theorem polyBoundedOn_size_findLitVal :
    PolyBoundedOn FindLitWF (fun N => Nat.size (findLitVal N)) := by
  refine ⟨40, 1, fun N hN => ?_⟩
  obtain ⟨hw, hm⟩ := hN
  have hfound : flFound (findLitVal N) ≤ 1 := by rw [findLitVal_eq]; exact flFound_le_one N _
  have hp : flP (findLitVal N) ≤ 1 := by rw [findLitVal_eq]; exact flP_le_one N _
  have hl : flL (findLitVal N) ≤ 1 := by rw [findLitVal_eq]; exact flL_le_one N _
  have hj : flJ (findLitVal N) ≤ Nat.size N := by
    rw [findLitVal_eq]
    exact le_trans (flJ_le N _)
      (le_trans (readK_le_size (flInst N) hw.1) (Nat.size_le_size (Nat.unpair_left_le N)))
  set F := flFound (findLitVal N)
  set J := flJ (findLitVal N)
  set P := flP (findLitVal N)
  set L := flL (findLitVal N)
  have hd : findLitVal N = Nat.pair F (Nat.pair J (Nat.pair P L)) := flAcc_decompose (findLitVal N)
  have sf : Nat.size F ≤ 1 := le_trans (Nat.size_le_size hfound) (by rw [Nat.size_one])
  have sp : Nat.size P ≤ 1 := le_trans (Nat.size_le_size hp) (by rw [Nat.size_one])
  have sl : Nat.size L ≤ 1 := le_trans (Nat.size_le_size hl) (by rw [Nat.size_one])
  have sj : Nat.size J ≤ Nat.size N := le_trans (Nat.size_le_size hj) (size_le_self (Nat.size N))
  have p1 := size_pair_le F (Nat.pair J (Nat.pair P L))
  have p2 := size_pair_le J (Nat.pair P L)
  have p3 := size_pair_le P L
  change Nat.size (findLitVal N) ≤ 40 * (Nat.size N + 1) ^ 1 + 40
  rw [hd]
  simp only [pow_one]
  omega

/-! ### `rfind'`-freeness and the `PolyTimeOn` capstone -/

theorem rfindFree_cPack0 : RfindFree cPack0 := by
  simp only [cPack0, cInstN, cMaskN, cIX, RfindFree, and_self]
theorem rfindFree_cPack1 : RfindFree cPack1 :=
  ⟨⟨trivial, trivial⟩, ⟨trivial, trivial⟩, ⟨trivial, trivial⟩, rfindFree_constCode 1⟩
theorem rfindFree_cFold : RfindFree cFold := by
  simp only [cFold, cAnd, cOr, cNot, cIsPos, cShape0, cSwap, notCore, orCore, isPosCore, constCode,
    RfindFree, and_self]
theorem rfindFree_cExpand : RfindFree cExpand :=
  ⟨⟨trivial, trivial⟩, ⟨trivial, trivial⟩,
    ⟨rfindFree_cFold, rfindFree_cPurity, rfindFree_cPack0⟩,
    ⟨rfindFree_cFold, rfindFree_cPurity, rfindFree_cPack1⟩⟩
theorem rfindFree_cCombine : RfindFree cCombine := by
  simp only [cCombine, ccFound', ccJ', ccP', ccL', ccPin, ccChosen, ccNF, ccAny, ccNew, ccC0, ccC1,
    ccFound, ccJ, ccP, ccL, ccIsP0, ccLab0, ccIsP1, ccLab1, ccAcc, ccV0, ccV1,
    cMux, cAnd, cOr, cNot, cIsPos, cShape0, cSwap, notCore, orCore, isPosCore, constCode,
    RfindFree, and_self]
theorem rfindFree_cFlStep : RfindFree cFlStep := ⟨rfindFree_cCombine, rfindFree_cExpand⟩
theorem rfindFree_cFlInit : RfindFree cFlInit := by
  simp only [cFlInit, RfindFree, and_self]
theorem rfindFree_cFindLit : RfindFree cFindLit :=
  ⟨⟨rfindFree_cFlInit, rfindFree_cFlStep⟩, ⟨trivial, trivial⟩, ⟨trivial, trivial⟩⟩

/-- **`polyTime_findLit`.** Selecting the first pure literal for the working set is poly-time on the
honest well-formed domain `FindLitWF` — `O(m·k²)` (`k` rounds, each two purity calls of `O(m·k)`),
with a bit/index-sized output. No `PolyBounded` side-hypotheses remain. -/
theorem polyTime_findLit : PolyTimeOn FindLitWF findLitVal :=
  ⟨cFindLit, rfindFree_cFindLit, fun _ _ => rfl,
    polyBoundedOn_tc_cFindLit, polyBoundedOn_size_findLitVal⟩

/-! ## Layer 8 — the greedy outer loop `solve` (C2b-outer)

`solve inst mask0` runs `readM inst` rounds of: find the first covering pure literal for the current
working set; if found, append its rule and refine the mask; else freeze. Termination is by construction
(a `prec` of `readM inst = m` rounds — enough because each covering round strictly drops the mask's
set-bit count, so ≤ m covering rounds empty it; the count-decrease measure and covering-soundness are
the two ingredients C2c consumes). The accumulator is `⟨mask, ⟨cnt, outDL⟩⟩`: the working mask, the
rule count, and the output decision-list built by **prepend** (a flag-cons list of `⟨j,⟨p,label⟩⟩`
triples); one final `cReverse` (length `cnt`) restores forward order. -/

/-! ### Packed-input and accumulator accessors -/
def svInst (n : ℕ) : ℕ := n.unpair.1
def svMask0 (n : ℕ) : ℕ := n.unpair.2
def svMask (acc : ℕ) : ℕ := acc.unpair.1
def svCnt (acc : ℕ) : ℕ := acc.unpair.2.unpair.1
def svDL (acc : ℕ) : ℕ := acc.unpair.2.unpair.2

/-! ### The semantic round -/

/-- One greedy round's UPDATE (a covering literal was found): refine the mask by `(j,p)`, bump the rule
count, and **prepend** the rule `⟨j,⟨p,label⟩⟩` to the (reversed) output list. -/
def svUpdated (inst acc lit : ℕ) : ℕ :=
  Nat.pair (maskUpdate inst (svMask acc) (flJ lit) (flP lit))
    (Nat.pair (svCnt acc + 1)
      (Nat.pair 1 (Nat.pair (Nat.pair (flJ lit) (Nat.pair (flP lit) (flL lit))) (svDL acc))))

/-- One greedy round: find the first covering pure literal for the current mask; if found, apply the
update; else freeze (no covering literal — greedy is stuck this round). The index `i` is unused (the
`prec` bound `m` is a round budget, not a data index). -/
def svStepFn (inst _i acc : ℕ) : ℕ :=
  if flFound (findLitVal (Nat.pair inst (svMask acc))) = 0 then acc
  else svUpdated inst acc (findLitVal (Nat.pair inst (svMask acc)))

/-! ### The round as a `Code`: `cSvStep = cSvB ∘ cSvA` (one `findLit`, then one `maskUpdate` + mux) -/

-- Stage A: from `⟨n,⟨i,acc⟩⟩` build `⟨inst, ⟨acc, lit⟩⟩` (exactly one `findLit` evaluation).
def cSinst : Code := comp left left
def cSacc : Code := comp right right
def cSmask : Code := comp left cSacc
def cSvA : Code := pair cSinst (pair cSacc (comp cFindLit (pair cSinst cSmask)))
-- Stage B: from `⟨inst,⟨acc,lit⟩⟩` build the new accumulator (one `maskUpdate`, then one whole-acc mux).
def cBi : Code := left
def cBa : Code := comp left right
def cBl : Code := comp right right
def cBm : Code := comp left cBa
def cBf : Code := comp left cBl
def cBj : Code := comp left (comp right cBl)
def cBp : Code := comp left (comp right (comp right cBl))
def cBlbl : Code := comp right (comp right (comp right cBl))
def cBcnt : Code := comp left (comp right cBa)
def cBdl : Code := comp right (comp right cBa)
def cBmu : Code := comp cMaskUpdate (pair cBi (pair cBm (pair cBj cBp)))
def cBtriple : Code := pair cBj (pair cBp cBlbl)
def cBcons : Code := pair (constCode 1) (pair cBtriple cBdl)
def cBcntsucc : Code := comp succ cBcnt
def cBupd : Code := pair cBmu (pair cBcntsucc cBcons)
def cSvB : Code := comp cMux (pair (pair cBupd cBa) cBf)
def cSvStep : Code := comp cSvB cSvA

theorem val_cSvA (n i acc : ℕ) :
    val cSvA (Nat.pair n (Nat.pair i acc))
      = Nat.pair (svInst n) (Nat.pair acc (findLitVal (Nat.pair (svInst n) (svMask acc)))) := by
  simp only [cSvA, cSinst, cSacc, cSmask, val_pair, val_comp, val_left, val_right, svInst, svMask,
    findLitVal, Nat.unpair_pair]

theorem val_cSvB (inst acc lit : ℕ) :
    val cSvB (Nat.pair inst (Nat.pair acc lit))
      = if flFound lit = 0 then acc else svUpdated inst acc lit := by
  rw [cSvB, val_comp,
    show val (pair (pair cBupd cBa) cBf) (Nat.pair inst (Nat.pair acc lit))
      = Nat.pair (Nat.pair (svUpdated inst acc lit) acc) (flFound lit) from by
        simp only [cBupd, cBa, cBf, cBmu, cBi, cBm, cBj, cBp, cBcnt, cBcntsucc, cBcons, cBtriple,
          cBdl, cBlbl, cBl, val_pair, val_comp, val_left, val_right, val_succ, val_constCode,
          Nat.unpair_pair, svUpdated, svMask, svCnt, svDL, flFound, flJ, flP, flL, maskUpdate,
          maskUpdateVal, packLit],
    val_cMux]

theorem val_cSvStep (n i acc : ℕ) :
    val cSvStep (Nat.pair n (Nat.pair i acc)) = svStepFn (svInst n) i acc := by
  rw [cSvStep, val_comp, val_cSvA, val_cSvB]; rfl

/-! ### The loop, the assemble (`cReverse`), and `solve` -/

def cSvInit : Code := pair right (pair zero zero)
theorem val_cSvInit (n : ℕ) : val cSvInit n = Nat.pair (svMask0 n) (Nat.pair 0 0) := by
  simp only [cSvInit, val_pair, val_right, val_zero, svMask0]

/-- The accumulator after `t` greedy rounds. -/
def svAcc (n t : ℕ) : ℕ := val (prec cSvInit cSvStep) (Nat.pair n t)

theorem svAcc_zero (n : ℕ) : svAcc n 0 = Nat.pair (svMask0 n) (Nat.pair 0 0) := by
  unfold svAcc; rw [val_prec_zero, val_cSvInit]
theorem svAcc_succ (n t : ℕ) : svAcc n (t + 1) = svStepFn (svInst n) t (svAcc n t) := by
  unfold svAcc; rw [val_prec_succ, val_cSvStep]

def cSvCount : Code := comp cReadM left
theorem val_cSvCount (n : ℕ) : val cSvCount n = readM (svInst n) := by
  simp only [cSvCount, val_comp, val_cReadM, val_left, svInst]
def cSvLoop : Code := comp (prec cSvInit cSvStep) (pair cId cSvCount)
theorem val_cSvLoop (n : ℕ) : val cSvLoop n = svAcc n (readM (svInst n)) := by
  rw [cSvLoop, val_comp, val_pair, val_cId, val_cSvCount]; rfl

/-- The final `cReverse` (length `cnt`) turns the prepend-order list forward and repackages
`⟨finalMask, forwardDL⟩`. -/
def cAssemble : Code := pair left (comp cReverse (pair (comp right right) (comp left right)))
theorem val_cAssemble (acc : ℕ) :
    val cAssemble acc = Nat.pair (svMask acc) (val cReverse (Nat.pair (svDL acc) (svCnt acc))) := by
  simp only [cAssemble, val_pair, val_comp, val_left, val_right, svMask, svDL, svCnt]

/-- **`solve`'s code**: run the greedy loop `readM inst` rounds, then reverse-and-repackage. -/
def cSolve : Code := comp cAssemble cSvLoop
def solveVal (n : ℕ) : ℕ := val cSolve n

theorem val_cSolve (n : ℕ) :
    solveVal n = Nat.pair (svMask (svAcc n (readM (svInst n))))
      (val cReverse (Nat.pair (svDL (svAcc n (readM (svInst n))))
        (svCnt (svAcc n (readM (svInst n)))))) := by
  unfold solveVal cSolve; rw [val_comp, val_cSvLoop, val_cAssemble]

/-- **The well-formed domain for `solve`.** -/
def SolveWF (n : ℕ) : Prop := WFBits (svInst n) ∧ MaskValid (svMask0 n) (readM (svInst n))

/-! ### Obligation 4 — the round-to-round `MaskValid` invariant

The load-bearing invariant for both the poly-time accumulator bound and C2c: the working mask stays a
valid length-`m` bit-list and never grows. `maskValid_maskUpdate` gives validity on a found round;
`maskUpdateVal_le` (via `updBit_le`) gives the shrink; the no-op round preserves both trivially. -/

theorem flP_findLitVal_le_one (N : ℕ) : flP (findLitVal N) ≤ 1 := by
  rw [findLitVal_eq]; exact flP_le_one N _
theorem flJ_findLitVal_le (N : ℕ) : flJ (findLitVal N) ≤ readK (flInst N) := by
  rw [findLitVal_eq]; exact flJ_le N _

/-- The greedy literal `findLit ⟨inst,mask⟩` gives a `PurityWF`-valid `maskUpdate` query (whether or not
it fired: `flJ ≤ readK`, `flP ≤ 1` hold on any round). -/
theorem purityWF_packLit_findLit (inst mask : ℕ) (hw : WFBits inst)
    (hm : MaskValid mask (readM inst)) :
    PurityWF (packLit inst mask (flJ (findLitVal (Nat.pair inst mask)))
      (flP (findLitVal (Nat.pair inst mask)))) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [instOf_packLit]; exact hw
  · rw [maskOf_packLit, instOf_packLit]; exact hm
  · rw [pOf_packLit]; exact flP_findLitVal_le_one _
  · rw [jOf_packLit, instOf_packLit]
    have h := flJ_findLitVal_le (Nat.pair inst mask)
    rwa [flInst, Nat.unpair_pair] at h

/-- On the well-formed domain the greedy round **shrinks** the mask (`updBit_le` ⇒ the refined bit never
exceeds the old): `maskUpdate` by the found literal is `≤` the current mask. -/
theorem maskUpdate_le_of_wf (inst mask : ℕ) (hw : WFBits inst) (hm : MaskValid mask (readM inst)) :
    maskUpdate inst mask (flJ (findLitVal (Nat.pair inst mask)))
      (flP (findLitVal (Nat.pair inst mask))) ≤ mask := by
  have h := maskUpdateVal_le (packLit inst mask (flJ (findLitVal (Nat.pair inst mask)))
    (flP (findLitVal (Nat.pair inst mask)))) (purityWF_packLit_findLit inst mask hw hm)
  rwa [maskOf_packLit] at h

theorem svMask_svUpdated (inst acc lit : ℕ) :
    svMask (svUpdated inst acc lit) = maskUpdate inst (svMask acc) (flJ lit) (flP lit) := by
  simp only [svUpdated, svMask, Nat.unpair_pair]

theorem svCnt_svUpdated (inst acc lit : ℕ) : svCnt (svUpdated inst acc lit) = svCnt acc + 1 := by
  simp only [svUpdated, svCnt, Nat.unpair_pair]

/-- The found-round `svDL` is `cons triple oldDL` — a genuine flag-cons prepend. -/
theorem svDL_svUpdated (inst acc lit : ℕ) :
    svDL (svUpdated inst acc lit)
      = Nat.pair 1 (Nat.pair (Nat.pair (flJ lit) (Nat.pair (flP lit) (flL lit))) (svDL acc)) := by
  simp only [svUpdated, svDL, Nat.unpair_pair]

/-- The rule count never exceeds the round budget (`≤ 1` bump per round). -/
theorem svCnt_le (n : ℕ) : ∀ t, svCnt (svAcc n t) ≤ t := by
  intro t
  induction t with
  | zero => rw [svAcc_zero]; simp only [svCnt, Nat.unpair_pair, Nat.zero_le]
  | succ k ih =>
    rw [svAcc_succ]
    unfold svStepFn
    split_ifs with hfound
    · omega
    · rw [svCnt_svUpdated]; omega

/-- A rule-triple `⟨j,⟨p,l⟩⟩` with `j ≤ readk` and `p,l` bits is `≤ ⟨readk, 3⟩`. Stated over OPAQUE
`j,p,l` (never the symbolic `findLitVal`) so `omega`/`pair_mono` never `whnf`-descend the literal scan. -/
theorem dlTriple_le {j p l readk : ℕ} (hj : j ≤ readk) (hp : p ≤ 1) (hl : l ≤ 1) :
    Nat.pair j (Nat.pair p l) ≤ Nat.pair readk 3 := by
  have h3 : Nat.pair p l ≤ 3 := by
    have hm := pair_mono hp hl
    have h11 : Nat.pair 1 1 = 3 := by decide
    omega
  exact pair_mono hj h3

/-- **The output-list `List` model.** After `t` rounds `svDL` is the flag-`cons` encoding of a genuine
`List` of `svCnt` rule-triples, each `≤ ⟨readK, 3⟩` (index `≤ readK`, two bits). Unconditional: the
literal bounds `flJ ≤ readK`, `flP,flL ≤ 1` hold on every round. This is what lets `cReverse` produce
an `encodeList` (hence bound its `Nat.size`) for the output-size clause. -/
theorem dlModel_svAcc (n : ℕ) : ∀ t, ∃ L : List ℕ,
    svDL (svAcc n t) = encodeList L ∧ svCnt (svAcc n t) = L.length ∧
    ∀ e ∈ L, e ≤ Nat.pair (readK (svInst n)) 3 := by
  intro t
  induction t with
  | zero =>
    refine ⟨[], ?_, ?_, ?_⟩
    · rw [svAcc_zero]; simp only [svDL, Nat.unpair_pair, encodeList]
    · rw [svAcc_zero]; simp only [svCnt, Nat.unpair_pair, List.length_nil]
    · intro e he; simp at he
  | succ k ih =>
    obtain ⟨L, hdl, hcnt, hbd⟩ := ih
    rw [svAcc_succ]
    unfold svStepFn
    split_ifs with hfound
    · exact ⟨L, hdl, hcnt, hbd⟩
    · have hj : flJ (findLitVal (Nat.pair (svInst n) (svMask (svAcc n k)))) ≤ readK (svInst n) := by
        have h := flJ_findLitVal_le (Nat.pair (svInst n) (svMask (svAcc n k)))
        rwa [flInst, Nat.unpair_pair] at h
      have hp : flP (findLitVal (Nat.pair (svInst n) (svMask (svAcc n k)))) ≤ 1 :=
        flP_findLitVal_le_one _
      have hl : flL (findLitVal (Nat.pair (svInst n) (svMask (svAcc n k)))) ≤ 1 := by
        rw [findLitVal_eq]; exact flL_le_one _ _
      have hhead : Nat.pair (flJ (findLitVal (Nat.pair (svInst n) (svMask (svAcc n k)))))
          (Nat.pair (flP (findLitVal (Nat.pair (svInst n) (svMask (svAcc n k)))))
            (flL (findLitVal (Nat.pair (svInst n) (svMask (svAcc n k))))))
          ≤ Nat.pair (readK (svInst n)) 3 := dlTriple_le hj hp hl
      refine ⟨Nat.pair (flJ (findLitVal (Nat.pair (svInst n) (svMask (svAcc n k)))))
        (Nat.pair (flP (findLitVal (Nat.pair (svInst n) (svMask (svAcc n k)))))
          (flL (findLitVal (Nat.pair (svInst n) (svMask (svAcc n k)))))) :: L, ?_, ?_, ?_⟩
      · rw [svDL_svUpdated, hdl]; rfl
      · rw [svCnt_svUpdated, hcnt]; simp only [List.length_cons]
      · intro e he
        rcases List.mem_cons.mp he with he | he
        · rw [he]; exact hhead
        · exact hbd e he

/-- **Obligation 4.** The working mask is `MaskValid` (a length-`m` bit-list) AND never grows, every
round — hence at the final round too. C2c consumes this together with `findLit`'s covering-soundness
(`coverLit_covers`) and the shrink measure (`updBit_le`) for its "finalMask all-zero iff consistent". -/
theorem maskValid_svAcc (n : ℕ) (hw : WFBits (svInst n))
    (hm : MaskValid (svMask0 n) (readM (svInst n))) :
    ∀ t, MaskValid (svMask (svAcc n t)) (readM (svInst n)) ∧ svMask (svAcc n t) ≤ svMask0 n := by
  intro t
  induction t with
  | zero =>
    rw [svAcc_zero]
    simp only [svMask, Nat.unpair_pair]
    exact ⟨hm, le_refl _⟩
  | succ k ih =>
    obtain ⟨ihv, ihle⟩ := ih
    rw [svAcc_succ]
    unfold svStepFn
    split_ifs with hfound
    · exact ⟨ihv, ihle⟩
    · rw [svMask_svUpdated]
      exact ⟨maskValid_maskUpdate _ _ _ _ hw ihv,
        le_trans (maskUpdate_le_of_wf _ _ hw ihv) ihle⟩

/-- The final mask (the first field of `solve`'s output) is `MaskValid` on the well-formed domain. -/
theorem maskValid_solve_finalMask (n : ℕ) (hn : SolveWF n) :
    MaskValid (svMask (svAcc n (readM (svInst n)))) (readM (svInst n)) :=
  (maskValid_svAcc n hn.1 hn.2 (readM (svInst n))).1

theorem solveVal_fst (n : ℕ) : (solveVal n).unpair.1 = svMask (svAcc n (readM (svInst n))) := by
  rw [val_cSolve]; simp only [Nat.unpair_pair]

/-- **`MaskValid` of `solve`'s output mask** — the C2c-facing packaging. -/
theorem maskValid_solve (n : ℕ) (hn : SolveWF n) :
    MaskValid (solveVal n).unpair.1 (readM (svInst n)) := by
  rw [solveVal_fst]; exact maskValid_solve_finalMask n hn

/-! ### Obligation 3, part A — the per-round native cost (`one findLit + one maskUpdate + O(1)`)

`cSvA` evaluates `findLit` once, `cSvB` evaluates `maskUpdate` once and muxes; both surrounding stages
are `O(1)` pointer-shuffles. `findLit`/`maskUpdate` are kept OPAQUE atoms (their `val`/`tc` hide
symbolic scans) so `omega` never `whnf`-descends into them. -/

theorem tc_cSvA_le (n i acc : ℕ) :
    tc cSvA (Nat.pair n (Nat.pair i acc))
      ≤ tc cFindLit (Nat.pair (svInst n) (svMask acc)) + 40 := by
  have hval : val (pair cSinst cSmask) (Nat.pair n (Nat.pair i acc))
      = Nat.pair (svInst n) (svMask acc) := by
    simp only [cSinst, cSmask, cSacc, val_pair, val_comp, val_left, val_right, svInst, svMask,
      Nat.unpair_pair]
  have hfind : tc (comp cFindLit (pair cSinst cSmask)) (Nat.pair n (Nat.pair i acc))
      ≤ tc cFindLit (Nat.pair (svInst n) (svMask acc)) + 20 := by
    rw [tc_comp, hval]
    simp only [cSinst, cSmask, cSacc, tc_pair, tc_comp, tc_left, tc_right]; omega
  have hi : tc cSinst (Nat.pair n (Nat.pair i acc)) ≤ 5 := by
    simp only [cSinst, tc_comp, tc_left]; omega
  have ha : tc cSacc (Nat.pair n (Nat.pair i acc)) ≤ 5 := by
    simp only [cSacc, tc_comp, tc_right]; omega
  rw [cSvA, tc_pair, tc_pair]; omega

theorem tc_cSvB_le (inst acc lit : ℕ) (hf : flFound lit ≤ 1) :
    tc cSvB (Nat.pair inst (Nat.pair acc lit))
      ≤ tc cMaskUpdate (packLit inst (svMask acc) (flJ lit) (flP lit)) + 300 := by
  have hbf : (val (pair (pair cBupd cBa) cBf) (Nat.pair inst (Nat.pair acc lit))).unpair.2
      = flFound lit := by
    rw [val_pair, Nat.unpair_pair]
    simp only [cBf, cBl, val_comp, val_left, val_right, flFound, Nat.unpair_pair]
  have hmux : tc cMux (val (pair (pair cBupd cBa) cBf) (Nat.pair inst (Nat.pair acc lit))) ≤ 6 := by
    have h := tc_cMux_le' (val (pair (pair cBupd cBa) cBf) (Nat.pair inst (Nat.pair acc lit)))
    rw [hbf] at h; omega
  have hmuarg : val (pair cBi (pair cBm (pair cBj cBp))) (Nat.pair inst (Nat.pair acc lit))
      = packLit inst (svMask acc) (flJ lit) (flP lit) := by
    simp only [cBi, cBm, cBa, cBj, cBp, cBl, val_pair, val_comp, val_left, val_right, svMask,
      flJ, flP, packLit, Nat.unpair_pair]
  have hbmu : tc cBmu (Nat.pair inst (Nat.pair acc lit))
      ≤ tc cMaskUpdate (packLit inst (svMask acc) (flJ lit) (flP lit)) + 30 := by
    rw [cBmu, tc_comp, hmuarg]
    simp only [cBi, cBm, cBa, cBj, cBp, cBl, tc_pair, tc_comp, tc_left, tc_right]; omega
  have hc1 : tc (constCode 1) (Nat.pair inst (Nat.pair acc lit)) ≤ 3 := tc_constCode_le 1 _
  have hpair : tc (pair (pair cBupd cBa) cBf) (Nat.pair inst (Nat.pair acc lit))
      ≤ tc cMaskUpdate (packLit inst (svMask acc) (flJ lit) (flP lit)) + 250 := by
    simp only [cBupd, cBa, cBf, cBcnt, cBcntsucc, cBcons, cBtriple, cBdl, cBl, cBj, cBp, cBlbl,
      tc_pair, tc_comp, tc_left, tc_right, tc_succ]
    omega
  rw [cSvB, tc_comp]; omega

/-! ### Obligation 3, part B — the output is poly-bit despite the exponential flag-cons encoding

The flag-cons encoding `cons e r = pair 1 (pair e r)` SQUARES the tail (`Nat.pair a b ≈ (max a b)²`),
so the encoded output list's `Nat.size` grows ~`×4` per rule — EXPONENTIAL in the rule count `svCnt`.
The output would be super-polynomial were `svCnt` free; it is not. Two facts close the gap:

* an **exp-size lower bound** on the INPUT (`two_pow_length_le`: `2^(length) ≤ size(encodeList) + 1`),
  so `2^(readM) ≤ Nat.size n + 1` — the instance already PAYS (exponentially) for its `m` examples;
* `svCnt ≤ readM` rules, each an `O(size n)`-bit triple, so the output list has `≤ readM` cells and an
  **exp-size upper bound** `size_encodeList_le` gives `size ≤ (4·size V + 8)·4^(svCnt)`. Then
  `4^(svCnt) ≤ 4^(readM) = (2^readM)² ≤ (size n + 1)²`, and the output is a cubic in `Nat.size n`. -/

/-- `Nat.pair` dominates the square of its right argument: `r² ≤ Nat.pair e r` (the pairing squares
the max, and `r ≤ max e r`). -/
theorem sq_le_pair_right (e r : ℕ) : r * r ≤ Nat.pair e r := by
  unfold Nat.pair; split_ifs with h
  · nlinarith
  · nlinarith [Nat.le_of_not_lt h]

/-- A flag-cons cell dominates the FOURTH power of its tail: `r⁴ ≤ cons e r` (two nested squarings). -/
theorem cons_ge_quad (e r : ℕ) : r * r * (r * r) ≤ Nat.pair 1 (Nat.pair e r) := by
  have h1 : Nat.pair e r * Nat.pair e r ≤ Nat.pair 1 (Nat.pair e r) := sq_le_pair_right 1 _
  have h2 : r * r ≤ Nat.pair e r := sq_le_pair_right e r
  calc r * r * (r * r) ≤ Nat.pair e r * Nat.pair e r := Nat.mul_le_mul h2 h2
    _ ≤ _ := h1

/-- Any flag-cons cell has value `≥ 2` (`pair 1 y ≥ 2`), so a genuine list value is `0` or `≥ 2` —
never `1`. This rules out the sole exception to the `×2`-per-cell `Nat.size` growth. -/
theorem two_le_pair_one (y : ℕ) : 2 ≤ Nat.pair 1 y := by
  unfold Nat.pair; split_ifs with h
  · nlinarith [h]
  · omega

/-- **The exp-size growth step.** When the tail is a genuine list value (`0` or `≥ 2`), a flag-cons cell
at least DOUBLES `Nat.size` (`+1`): `2·size r + 1 ≤ size (cons e r)`. The `r = 1` exception (where the
squaring `1² = 1` stalls) cannot occur for a real list tail. -/
theorem size_cons_ge (e r : ℕ) (hr : r = 0 ∨ 2 ≤ r) :
    2 * Nat.size r + 1 ≤ Nat.size (Nat.pair 1 (Nat.pair e r)) := by
  rcases hr with hr | hr
  · subst hr
    simp only [Nat.size_zero, Nat.mul_zero, Nat.zero_add]
    exact Nat.size_pos.mpr (by have := left_le_pair 1 (Nat.pair e 0); omega)
  · have hs2 : 2 ≤ Nat.size r := by
      have h := Nat.size_le_size hr
      have h2 : Nat.size 2 = 2 := by decide
      omega
    have hlow : 2 ^ (Nat.size r - 1) ≤ r := Nat.lt_size.mp (by omega)
    have hquad := cons_ge_quad e r
    have hpm : 2 ^ (4 * (Nat.size r - 1)) = (2 ^ (Nat.size r - 1)) ^ 4 := by
      rw [← pow_mul, Nat.mul_comm]
    have h4 : 2 ^ (4 * (Nat.size r - 1)) ≤ Nat.pair 1 (Nat.pair e r) := by
      rw [hpm]
      calc (2 ^ (Nat.size r - 1)) ^ 4 ≤ r ^ 4 := Nat.pow_le_pow_left hlow 4
        _ = r * r * (r * r) := by ring
        _ ≤ _ := hquad
    have hlt := Nat.lt_size.mpr h4
    omega

/-- **Exp-size LOWER bound (the instance pays for its length).** A length-`k` encoded list has
`Nat.size ≥ k`-bits doubling per cell: `2^k ≤ size (encodeList xs) + 1`. This is what caps `svCnt`. -/
theorem encodeList_zero_or_two_le : ∀ xs : List ℕ, encodeList xs = 0 ∨ 2 ≤ encodeList xs
  | [] => Or.inl rfl
  | (_ :: _) => Or.inr (two_le_pair_one _)

theorem two_pow_length_le : ∀ xs : List ℕ, 2 ^ xs.length ≤ Nat.size (encodeList xs) + 1
  | [] => by simp [encodeList]
  | (x :: xs) => by
      have ih := two_pow_length_le xs
      have hstep := size_cons_ge x (encodeList xs) (encodeList_zero_or_two_le xs)
      change 2 ^ (xs.length + 1) ≤ Nat.size (Nat.pair 1 (Nat.pair x (encodeList xs))) + 1
      rw [pow_succ]
      nlinarith [ih, hstep]

/-- **Exp-size UPPER bound.** A length-`k` encoded list with every element `≤ V` has
`Nat.size (encodeList xs) + (4·size V + 8) ≤ (4·size V + 8)·4^k` (the `+C` slack closes the induction:
each cell at most quadruples `Nat.size`, via two `size_pair_le` steps). -/
theorem size_encodeList_le (V : ℕ) : ∀ xs : List ℕ, (∀ e ∈ xs, e ≤ V) →
    Nat.size (encodeList xs) + (4 * Nat.size V + 8) ≤ (4 * Nat.size V + 8) * 4 ^ xs.length
  | [], _ => by simp [encodeList]
  | (x :: xs), h => by
      have hx : Nat.size x ≤ Nat.size V := Nat.size_le_size (h x (List.mem_cons_self ..))
      have ih := size_encodeList_le V xs (fun e he => h e (List.mem_cons_of_mem _ he))
      have hp1 := size_pair_le x (encodeList xs)
      have hp2 := size_pair_le 1 (Nat.pair x (encodeList xs))
      have h1 : Nat.size 1 = 1 := by decide
      change Nat.size (Nat.pair 1 (Nat.pair x (encodeList xs))) + (4 * Nat.size V + 8)
        ≤ (4 * Nat.size V + 8) * 4 ^ (xs.length + 1)
      rw [pow_succ]
      nlinarith [ih, hp1, hp2, hx, h1]

/-- **The instance PAYS for its length.** `2^(readM inst) ≤ Nat.size inst + 1` under binary
well-formedness — the `readM inst` examples are stored in the (exp-size) flag-cons `readData`, so the
input's bit-length already dominates `2^(readM)`. This is what caps `svCnt` exponentially. -/
theorem two_pow_readM_le (inst : ℕ) (hw : WFBits inst) : 2 ^ readM inst ≤ Nat.size inst + 1 := by
  obtain ⟨_hwf, exs, hdeq, hdlen, _, _⟩ := hw
  have h1 : 2 ^ exs.length ≤ Nat.size (encodeList exs) + 1 := two_pow_length_le exs
  rw [hdlen, ← hdeq] at h1
  have h2 : Nat.size (readData inst) ≤ Nat.size inst := Nat.size_le_size (readData_le inst)
  omega

/-- **Obligation 3, output-size clause.** `Nat.size (solveVal n) ≤ 66·(Nat.size n + 1)³ + 66` on the
well-formed domain. The output DL is the reverse of the `dlModel` `List` — length `svCnt ≤ readM`, each
element an `O(Nat.size n)`-bit triple. Its `Nat.size` is exponential in the length (`size_encodeList_le`
gives `≤ (4·size V+8)·4^(svCnt)`), but `4^(svCnt) ≤ 4^(readM) = (2^readM)² ≤ (size n + 1)²` by the
exp-lower bound `two_pow_readM_le`, so the whole output is a cubic in `Nat.size n`. -/
theorem polyBoundedOn_size_solveVal :
    PolyBoundedOn SolveWF (fun n => Nat.size (solveVal n)) := by
  refine ⟨66, 3, fun n hn => ?_⟩
  obtain ⟨hw, hm0⟩ := hn
  have hwf : WF (svInst n) := hw.1
  obtain ⟨L, hdl, hcnt, hbd⟩ := dlModel_svAcc n (readM (svInst n))
  change Nat.size (solveVal n) ≤ 66 * (Nat.size n + 1) ^ 3 + 66
  -- the reversed output list is `encodeList L.reverse`
  have hB : val cReverse (Nat.pair (svDL (svAcc n (readM (svInst n))))
      (svCnt (svAcc n (readM (svInst n))))) = encodeList L.reverse := by
    rw [hdl, hcnt]; exact val_cReverse L
  -- the final mask is `≤ n`, so poly-bit
  have hsizeA : Nat.size (svMask (svAcc n (readM (svInst n)))) ≤ Nat.size n :=
    Nat.size_le_size (le_trans (maskValid_svAcc n hw hm0 (readM (svInst n))).2 (Nat.unpair_right_le n))
  -- the element bound `V = ⟨readK, 3⟩` is `O(Nat.size n)`-bit
  have hVsize : Nat.size (Nat.pair (readK (svInst n)) 3) ≤ 2 * Nat.size n + 6 := by
    have hp := size_pair_le (readK (svInst n)) 3
    have hk : Nat.size (readK (svInst n)) ≤ Nat.size n :=
      le_trans (size_le_self _) (le_trans (readK_le_size (svInst n) hwf)
        (Nat.size_le_size (Nat.unpair_left_le n)))
    have h3s : Nat.size 3 = 2 := by decide
    omega
  -- the exp-size UPPER bound on the encoded reverse list
  have hBsize0 := size_encodeList_le (Nat.pair (readK (svInst n)) 3) L.reverse (by
    intro e he; rw [List.mem_reverse] at he; exact hbd e he)
  rw [List.length_reverse] at hBsize0
  have hBsize : Nat.size (encodeList L.reverse)
      ≤ (4 * Nat.size (Nat.pair (readK (svInst n)) 3) + 8) * 4 ^ L.length := by omega
  -- length ≤ readM, and `4^length ≤ (size n + 1)²` via the exp LOWER bound
  have hLm : L.length ≤ readM (svInst n) := by rw [← hcnt]; exact svCnt_le n (readM (svInst n))
  have h2m : 2 ^ readM (svInst n) ≤ Nat.size n + 1 := by
    have h := two_pow_readM_le (svInst n) hw
    have hsz : Nat.size (svInst n) ≤ Nat.size n := Nat.size_le_size (Nat.unpair_left_le n)
    omega
  have hpow4 : (4:ℕ) ^ readM (svInst n) = (2 ^ readM (svInst n)) ^ 2 := by
    rw [← Nat.pow_mul, Nat.mul_comm, Nat.pow_mul]
  have h4L : (4:ℕ) ^ L.length ≤ (Nat.size n + 1) ^ 2 :=
    calc (4:ℕ) ^ L.length ≤ 4 ^ readM (svInst n) := Nat.pow_le_pow_right (by norm_num) hLm
      _ = (2 ^ readM (svInst n)) ^ 2 := hpow4
      _ ≤ (Nat.size n + 1) ^ 2 := Nat.pow_le_pow_left h2m 2
  -- combine into a cubic bound on the output list's size
  have hBfinal : Nat.size (encodeList L.reverse) ≤ 32 * (Nat.size n + 1) ^ 3 := by
    have h1 : 4 * Nat.size (Nat.pair (readK (svInst n)) 3) + 8 ≤ 32 * (Nat.size n + 1) := by omega
    calc Nat.size (encodeList L.reverse)
        ≤ (4 * Nat.size (Nat.pair (readK (svInst n)) 3) + 8) * 4 ^ L.length := hBsize
      _ ≤ (32 * (Nat.size n + 1)) * (Nat.size n + 1) ^ 2 := Nat.mul_le_mul h1 h4L
      _ = 32 * (Nat.size n + 1) ^ 3 := by ring
  -- assemble `⟨finalMask, reversedDL⟩`
  rw [val_cSolve, hB]
  calc Nat.size (Nat.pair (svMask (svAcc n (readM (svInst n)))) (encodeList L.reverse))
      ≤ 2 * Nat.size (svMask (svAcc n (readM (svInst n))))
        + 2 * Nat.size (encodeList L.reverse) + 2 := size_pair_le _ _
    _ ≤ 2 * Nat.size n + 2 * (32 * (Nat.size n + 1) ^ 3) + 2 := by omega
    _ ≤ 66 * (Nat.size n + 1) ^ 3 + 66 := by
        have hcube : Nat.size n + 1 ≤ (Nat.size n + 1) ^ 3 := Nat.le_self_pow (by norm_num) _
        omega

/-! ### Obligation 3, part C — the native cost is poly-bit (`k` rounds × `O(m·k²)` per round)

`solve` runs `readM inst` rounds; each round is one `findLit` (`O(m·k²)`) + one `maskUpdate` (`O(m·k)`)
+ `O(1)`, so `O(m·k²)` per round and `O(m²·k²)` overall, plus an `O(m)` final `cReverse`. The
per-round budget is uniform over the visited rounds because the working mask stays `MaskValid`
(`maskValid_svAcc`), so every round's `findLit`/`maskUpdate` query is well-formed with `readK`/`readM`
fixed at the instance's. -/

/-- The final read-out (`cReverse` of the built list) costs `O(svCnt)`. -/
theorem tc_cAssemble_le (acc : ℕ) : tc cAssemble acc ≤ 41 * svCnt acc + 50 := by
  have hval : val (pair (comp right right) (comp left right)) acc
      = Nat.pair (svDL acc) (svCnt acc) := by
    simp only [val_pair, val_comp, val_left, val_right, svDL, svCnt]
  have hrev := tc_cReverse_le (svDL acc) (svCnt acc)
  unfold cAssemble
  rw [tc_pair, tc_comp, hval]
  simp only [tc_pair, tc_comp, tc_left, tc_right]
  omega

/-- **The greedy round's native cost** = one `maskUpdate` + one `findLit` + `O(1)` (mux/pointer work).
The `maskUpdate` is on the greedy literal's `packLit` query; `findLit` on the current-mask query. -/
theorem tc_cSvStep_le (n i acc : ℕ) :
    tc cSvStep (Nat.pair n (Nat.pair i acc))
      ≤ tc cMaskUpdate (packLit (svInst n) (svMask acc)
          (flJ (findLitVal (Nat.pair (svInst n) (svMask acc))))
          (flP (findLitVal (Nat.pair (svInst n) (svMask acc)))))
        + tc cFindLit (Nat.pair (svInst n) (svMask acc)) + 341 := by
  have hA := tc_cSvA_le n i acc
  have hfound : flFound (findLitVal (Nat.pair (svInst n) (svMask acc))) ≤ 1 := by
    rw [findLitVal_eq]; exact flFound_le_one _ _
  have hB := tc_cSvB_le (svInst n) acc (findLitVal (Nat.pair (svInst n) (svMask acc))) hfound
  rw [cSvStep, tc_comp, val_cSvA]
  omega

/-- Per-round `maskUpdate` budget (`O(m·k)`), uniform in the round via `jOf ≤ readK`. -/
def BsvMask (inst : ℕ) : ℕ := (8 * readK inst + 2401) * readM inst + 41 * readM inst + 100
/-- Per-round `findLit` budget (`O(m·k²)`), uniform in the round. -/
def BsvFind (inst : ℕ) : ℕ :=
  13 + (2 * ((16 * readK inst + 5701) * readM inst + 400) + 4542 + 1) * readK inst + 1 + 10 + 1
/-- The full per-round budget. -/
def Bsv (inst : ℕ) : ℕ := BsvMask inst + BsvFind inst + 341

/-- **The round's `maskUpdate` cost is uniformly `≤ BsvMask (svInst n)`** on the visited rounds: the
`packLit` query is `PurityWF` (`purityWF_packLit_findLit`, from the `MaskValid` invariant), and the
found literal index `flJ ≤ readK`. -/
theorem tc_cMaskUpdate_round (n i : ℕ) (hw : WFBits (svInst n))
    (hm : MaskValid (svMask (svAcc n i)) (readM (svInst n))) :
    tc cMaskUpdate (packLit (svInst n) (svMask (svAcc n i))
        (flJ (findLitVal (Nat.pair (svInst n) (svMask (svAcc n i)))))
        (flP (findLitVal (Nat.pair (svInst n) (svMask (svAcc n i))))))
      ≤ BsvMask (svInst n) := by
  obtain ⟨hwM, hmM, hpM, _⟩ := purityWF_packLit_findLit (svInst n) (svMask (svAcc n i)) hw hm
  have hraw := tc_cMaskUpdate_raw _ hwM hmM hpM
  rw [jOf_packLit, instOf_packLit] at hraw
  have hjle : flJ (findLitVal (Nat.pair (svInst n) (svMask (svAcc n i)))) ≤ readK (svInst n) := by
    have h := flJ_findLitVal_le (Nat.pair (svInst n) (svMask (svAcc n i)))
    rwa [flInst, Nat.unpair_pair] at h
  have hmono : (8 * flJ (findLitVal (Nat.pair (svInst n) (svMask (svAcc n i)))) + 2400 + 1)
        * readM (svInst n) ≤ (8 * readK (svInst n) + 2401) * readM (svInst n) :=
    Nat.mul_le_mul (by omega) (le_refl _)
  unfold BsvMask
  omega

/-- **The round's `findLit` cost is uniformly `≤ BsvFind (svInst n)`** on the visited rounds: the
current-mask query is `FindLitWF` (from the `MaskValid` invariant), so `tc_cFindLit_raw` applies with
`readK`/`readM` fixed at the instance's. -/
theorem tc_cFindLit_round (n i : ℕ) (hw : WFBits (svInst n))
    (hm : MaskValid (svMask (svAcc n i)) (readM (svInst n))) :
    tc cFindLit (Nat.pair (svInst n) (svMask (svAcc n i))) ≤ BsvFind (svInst n) := by
  have hfi : flInst (Nat.pair (svInst n) (svMask (svAcc n i))) = svInst n := by
    rw [flInst, Nat.unpair_pair]
  have hfw : WFBits (flInst (Nat.pair (svInst n) (svMask (svAcc n i)))) := by rw [hfi]; exact hw
  have hfm : MaskValid (flMask (Nat.pair (svInst n) (svMask (svAcc n i))))
      (readM (flInst (Nat.pair (svInst n) (svMask (svAcc n i))))) := by
    rw [flMask, Nat.unpair_pair, hfi]; exact hm
  have hraw := tc_cFindLit_raw (Nat.pair (svInst n) (svMask (svAcc n i))) hfw hfm
  have hinit : tc cFlInit (Nat.pair (svInst n) (svMask (svAcc n i))) ≤ 13 := by
    simp only [cFlInit, tc_pair, tc_zero]; omega
  have hidc : tc (pair cId cFlCount) (Nat.pair (svInst n) (svMask (svAcc n i))) ≤ 10 := by
    simp only [cId, cFlCount, tc_pair, tc_comp, tc_left, tc_right]; omega
  unfold BstepFL at hraw
  rw [hfi] at hraw
  unfold BsvFind
  omega

/-- **The per-visited-round bound.** On the well-formed domain every round `i < readM (svInst n)` costs
`≤ Bsv (svInst n)`, uniformly — the `MaskValid` invariant (`maskValid_svAcc`) keeps each round's queries
well-formed with `readK`/`readM` pinned to the instance's. -/
theorem hSvStep_visited (n : ℕ) (hw : WFBits (svInst n))
    (hm0 : MaskValid (svMask0 n) (readM (svInst n))) :
    ∀ i, i < readM (svInst n) →
      tc cSvStep (Nat.pair n (Nat.pair i (val (prec cSvInit cSvStep) (Nat.pair n i))))
        ≤ Bsv (svInst n) := by
  intro i _hi
  rw [show val (prec cSvInit cSvStep) (Nat.pair n i) = svAcc n i from rfl]
  have hmi : MaskValid (svMask (svAcc n i)) (readM (svInst n)) := (maskValid_svAcc n hw hm0 i).1
  have hstep := tc_cSvStep_le n i (svAcc n i)
  have hmu := tc_cMaskUpdate_round n i hw hmi
  have hfl := tc_cFindLit_round n i hw hmi
  unfold Bsv
  omega

/-- **`cSolve`'s native cost on a well-formed instance**: the `O(m)` read-out (`tc_cAssemble_le`) + the
`(Bsv+1)·m` loop (`tc_prec_le'` + `hSvStep_visited`) + `O(1)` shapers sum to `≤ (Bsv+42)·m + 67`. -/
theorem tc_cSolve_raw (n : ℕ) (hw : WFBits (svInst n))
    (hm0 : MaskValid (svMask0 n) (readM (svInst n))) :
    tc cSolve n ≤ (Bsv (svInst n) + 42) * readM (svInst n) + 67 := by
  have hasm : tc cAssemble (val cSvLoop n) ≤ 41 * readM (svInst n) + 50 := by
    rw [val_cSvLoop]
    have h := tc_cAssemble_le (svAcc n (readM (svInst n)))
    have hc := svCnt_le n (readM (svInst n))
    omega
  have hprec : tc (prec cSvInit cSvStep) (Nat.pair n (readM (svInst n)))
      ≤ tc cSvInit n + (Bsv (svInst n) + 1) * readM (svInst n) + 1 :=
    tc_prec_le' (readM (svInst n)) (hSvStep_visited n hw hm0)
  have hinit : tc cSvInit n ≤ 5 := by
    simp only [cSvInit, tc_pair, tc_right, tc_zero]; omega
  have hidc : tc (pair cId cSvCount) n ≤ 9 := by
    simp only [cId, cSvCount, cReadM, tc_pair, tc_comp, tc_left, tc_right]; omega
  have hpairval : val (pair cId cSvCount) n = Nat.pair n (readM (svInst n)) := by
    rw [val_pair, val_cId, val_cSvCount]
  have hloop : tc cSvLoop n
      ≤ tc cSvInit n + (Bsv (svInst n) + 1) * readM (svInst n) + 1 + 9 + 1 := by
    rw [cSvLoop, tc_comp, hpairval]; omega
  have hring : (Bsv (svInst n) + 42) * readM (svInst n)
      = (Bsv (svInst n) + 1) * readM (svInst n) + 41 * readM (svInst n) := by ring
  rw [cSolve, tc_comp]
  omega

/-- **`cSolve` is poly-time on the well-formed domain** — a quartic in `Nat.size n` (`k` rounds ×
`O(m·k²)` per round). The raw `(Bsv+42)·m` bound is turned poly-bit by `readK,readM ≤ size n`. -/
theorem polyBoundedOn_tc_cSolve : PolyBoundedOn SolveWF (tc cSolve) := by
  refine ⟨19777, 4, fun n hn => ?_⟩
  obtain ⟨hw, hm0⟩ := hn
  have hwf : WF (svInst n) := hw.1
  have hrk : readK (svInst n) ≤ Nat.size n :=
    le_trans (readK_le_size (svInst n) hwf) (Nat.size_le_size (Nat.unpair_left_le n))
  have hrm : readM (svInst n) ≤ Nat.size n :=
    le_trans (readM_le_size (svInst n) hwf) (Nat.size_le_size (Nat.unpair_left_le n))
  have hBsv : Bsv (svInst n) ≤ 19668 * (Nat.size n + 1) ^ 3 := by
    unfold Bsv BsvMask BsvFind
    nlinarith [hrk, hrm, Nat.mul_le_mul (Nat.mul_le_mul hrk hrk) hrm, Nat.mul_le_mul hrk hrm]
  have hraw := tc_cSolve_raw n hw hm0
  nlinarith [hraw, hBsv, hrm, Nat.mul_le_mul hBsv (show readM (svInst n) ≤ Nat.size n + 1 by omega),
    Nat.le_self_pow (show (4:ℕ) ≠ 0 by norm_num) (Nat.size n + 1)]

/-! ### `rfind'`-freeness of the `solve` code (structural — every atom is a bounded loop) -/

theorem rfindFree_cSvA : RfindFree cSvA := by
  simp only [cSvA, cSinst, cSacc, cSmask, RfindFree, rfindFree_cFindLit, and_self]
theorem rfindFree_cSvB : RfindFree cSvB := by
  simp only [cSvB, cBupd, cBa, cBf, cBmu, cBi, cBm, cBj, cBp, cBcnt, cBcntsucc, cBcons, cBtriple,
    cBdl, cBlbl, cBl, RfindFree, rfindFree_cMaskUpdate, rfindFree_cMux, constCode, and_self]
theorem rfindFree_cSvStep : RfindFree cSvStep := ⟨rfindFree_cSvB, rfindFree_cSvA⟩
theorem rfindFree_cSvInit : RfindFree cSvInit := by
  simp only [cSvInit, RfindFree, and_self]
theorem rfindFree_cSvCount : RfindFree cSvCount := by
  simp only [cSvCount, cReadM, RfindFree, and_self]
theorem rfindFree_cSvLoop : RfindFree cSvLoop :=
  ⟨⟨rfindFree_cSvInit, rfindFree_cSvStep⟩, rfindFree_cId, rfindFree_cSvCount⟩
theorem rfindFree_cAssemble : RfindFree cAssemble := by
  simp only [cAssemble, RfindFree, rfindFree_cReverse, and_self]
theorem rfindFree_cSolve : RfindFree cSolve := ⟨rfindFree_cAssemble, rfindFree_cSvLoop⟩

/-- **`polyTime_solve`.** The greedy 1-DL consistency solver is poly-time on the honest well-formed
domain `SolveWF` — `O(m²·k²)` native cost, output a poly-bit decision list. No `PolyBounded`
side-hypotheses remain; the exponential flag-cons output stays poly-bit because the instance pays
(exponentially) for its `m` examples (`two_pow_readM_le`). C2c owns greedy CORRECTNESS. -/
theorem polyTime_solve : PolyTimeOn SolveWF solveVal :=
  ⟨cSolve, rfindFree_cSolve, fun _ _ => rfl, polyBoundedOn_tc_cSolve, polyBoundedOn_size_solveVal⟩

/-! ## Layer 9 — C2c: greedy correctness (`solve` decides 1-DL consistency)

The capstone that makes the poly(m,k) timing meaningful: `solve` empties its mask iff a consistent
1-decision-list over the Boolean features exists. Worked entirely at the `List` model, over the SAME
`featOf`/`lblOf` accessors the solver's bridge lemmas (`findLit_sound`, `coverLit_covers`, `purity_*`,
`maskUpdate_getBit`) speak. A rule is a `Nat`-triple `⟨j,⟨p,label⟩⟩` (matching the emitted `svDL`),
decoded by `ruleJ`/`ruleP`/`ruleL`; a rule FIRES on example `e` iff feature `j` of `e` equals `p`. -/

/-! ### The `List`-model 1-decision-list semantics -/

/-- Feature index of an encoded rule triple `⟨j,⟨p,label⟩⟩`. -/
def ruleJ (r : ℕ) : ℕ := r.unpair.1
/-- Polarity of an encoded rule triple. -/
def ruleP (r : ℕ) : ℕ := r.unpair.2.unpair.1
/-- Output label of an encoded rule triple. -/
def ruleL (r : ℕ) : ℕ := r.unpair.2.unpair.2

/-- Field projections of a literal triple, over VARIABLE fields — apply by `rw` to avoid `simp`'s
`Nat.unpair_pair` scanning into (and `whnf`-descending) a symbolic `findLitVal` field. -/
theorem ruleJ_pair (a b : ℕ) : ruleJ (Nat.pair a b) = a := by simp only [ruleJ, Nat.unpair_pair]
theorem ruleP_pair (a p l : ℕ) : ruleP (Nat.pair a (Nat.pair p l)) = p := by
  simp only [ruleP, Nat.unpair_pair]
theorem ruleL_pair (a p l : ℕ) : ruleL (Nat.pair a (Nat.pair p l)) = l := by
  simp only [ruleL, Nat.unpair_pair]

/-- **1-DL evaluation** (first-match). `evalDLn rules default e` = the label of the first rule that
fires on `e`, else `default`. A rule fires iff its feature-`ruleJ` bit of `e` matches `ruleP`
(`bEq … ≠ 0` — the SAME gate the solver's `Covered` uses, so on bit-polarities it is `featOf = ruleP`). -/
def evalDLn : List ℕ → ℕ → ℕ → ℕ
  | [], d, _e => d
  | r :: rs, d, e => if bEq (featOf e (ruleJ r)) (ruleP r) = 0 then evalDLn rs d e else ruleL r

/-- Some rule of `D` fires on `e`. -/
def firesN (D : List ℕ) (e : ℕ) : Prop := ∃ r ∈ D, bEq (featOf e (ruleJ r)) (ruleP r) ≠ 0

/-- **Consistency.** Every example is classified to its own label by the DL. -/
def Consistent (rules : List ℕ) (d : ℕ) (exs : List ℕ) : Prop :=
  ∀ e ∈ exs, evalDLn rules d e = lblOf e

/-- **Existence of a consistent 1-DL** over VALID feature literals (`ruleJ < readK inst`) — the literal
space the solver searches. This is what `solve` decides. -/
def ExistsConsistentDL (inst : ℕ) (exs : List ℕ) : Prop :=
  ∃ (rules : List ℕ) (d : ℕ), (∀ r ∈ rules, ruleJ r < readK inst) ∧ Consistent rules d exs

/-! ### Abstract `evalDLn` laws (pure list algebra) -/

/-- **The append/fold law.** Scanning `D ++ E` = scan `D`, falling through to `evalDLn E` as its
default (the first firing rule wins). -/
theorem evalDLn_append (D E : List ℕ) (d e : ℕ) :
    evalDLn (D ++ E) d e = evalDLn D (evalDLn E d e) e := by
  induction D with
  | nil => rfl
  | cons r rs ih => simp only [List.cons_append, evalDLn, ih]

/-- No firing rule ⇒ evaluation falls to the default. -/
theorem evalDLn_not_fires (D : List ℕ) (d e : ℕ)
    (h : ∀ r ∈ D, bEq (featOf e (ruleJ r)) (ruleP r) = 0) : evalDLn D d e = d := by
  induction D with
  | nil => rfl
  | cons r rs ih =>
      rw [evalDLn, if_pos (h r (List.mem_cons_self ..))]
      exact ih (fun r' hr' => h r' (List.mem_cons_of_mem _ hr'))

/-- A firing rule makes evaluation default-independent. -/
theorem evalDLn_fires_const (D : List ℕ) (d1 d2 e : ℕ) (h : firesN D e) :
    evalDLn D d1 e = evalDLn D d2 e := by
  induction D with
  | nil => obtain ⟨r, hr, _⟩ := h; simp at hr
  | cons r rs ih =>
      rw [evalDLn, evalDLn]
      split_ifs with hc
      · obtain ⟨r', hr', hf'⟩ := h
        rcases List.mem_cons.mp hr' with rfl | hin
        · exact absurd hc hf'
        · exact ih ⟨r', hin, hf'⟩
      · rfl

/-! ### Bridging the semantic `Covered`/label facts to `coverLit`/`litLabel` -/

/-- **Semantic ⇒ `coverLit`.** A literal `(j,p)` that covers ≥1 remaining example and is pure (no
covered-0/covered-1 split) has `coverLit ≠ 0` (so `findLit` will fire). Via `purity_isPure_iff`/
`purity_sawAny` on the `packLit` query. -/
theorem coverLit_of_semantic (inst mask j p : ℕ) (msks exs : List ℕ)
    (hmeq : mask = encodeList msks) (hdeq : readData inst = encodeList exs)
    (hcount : readM inst = exs.length) (hlen : msks.length = exs.length)
    (hcov : ∃ be ∈ msks.zip exs, Covered j p be)
    (hpure : ¬((∃ be ∈ msks.zip exs, Covered j p be ∧ lblOf be.2 = 0)
             ∧ (∃ be ∈ msks.zip exs, Covered j p be ∧ lblOf be.2 ≠ 0))) :
    coverLit inst mask j p ≠ 0 := by
  unfold coverLit
  rw [bAnd_ne_zero]
  refine ⟨?_, ?_⟩
  · unfold isPureLit
    rw [purity_isPure_iff (packLit inst mask j p) msks exs
        (by rw [maskOf_packLit]; exact hmeq) (by rw [dataOf_packLit]; exact hdeq)
        (by rw [instOf_packLit]; exact hcount) hlen, jOf_packLit, pOf_packLit]
    exact hpure
  · unfold sawAnyLit
    rw [purity_sawAny (packLit inst mask j p) msks exs
        (by rw [maskOf_packLit]; exact hmeq) (by rw [dataOf_packLit]; exact hdeq)
        (by rw [instOf_packLit]; exact hcount) hlen, jOf_packLit, pOf_packLit]
    exact hcov

/-- **`coverLit` ⇒ every covered example carries the recorded `litLabel`.** The purity split means all
covered remaining examples share one label, which is exactly `litLabel` (= `commonLabel`). -/
theorem covered_lbl_eq_litLabel (inst mask j p : ℕ) (msks exs : List ℕ)
    (hmeq : mask = encodeList msks) (hdeq : readData inst = encodeList exs)
    (hcount : readM inst = exs.length) (hlen : msks.length = exs.length)
    (hlbl1 : ∀ e ∈ exs, lblOf e ≤ 1)
    (be : ℕ × ℕ) (hbe : be ∈ msks.zip exs) (hc : Covered j p be)
    (hcov : coverLit inst mask j p ≠ 0) :
    lblOf be.2 = litLabel inst mask j p := by
  have hpure : ¬((∃ be ∈ msks.zip exs, Covered j p be ∧ lblOf be.2 = 0)
             ∧ (∃ be ∈ msks.zip exs, Covered j p be ∧ lblOf be.2 ≠ 0)) := by
    have h := hcov; unfold coverLit at h; rw [bAnd_ne_zero] at h
    have hip := h.1; unfold isPureLit at hip
    rwa [purity_isPure_iff (packLit inst mask j p) msks exs
      (by rw [maskOf_packLit]; exact hmeq) (by rw [dataOf_packLit]; exact hdeq)
      (by rw [instOf_packLit]; exact hcount) hlen, jOf_packLit, pOf_packLit] at hip
  have hlblbe : lblOf be.2 ≤ 1 := hlbl1 be.2 (List.of_mem_zip hbe).2
  have hcl : litLabel inst mask j p ≠ 0 ↔ ∃ be ∈ msks.zip exs, Covered j p be ∧ lblOf be.2 ≠ 0 := by
    unfold litLabel
    rw [purity_commonLabel (packLit inst mask j p) msks exs
      (by rw [maskOf_packLit]; exact hmeq) (by rw [dataOf_packLit]; exact hdeq)
      (by rw [instOf_packLit]; exact hcount) hlen, jOf_packLit, pOf_packLit]
  have hll1 : litLabel inst mask j p ≤ 1 := litLabel_le_one inst mask j p
  by_cases hb0 : lblOf be.2 = 0
  · have hno1 : ¬ ∃ be ∈ msks.zip exs, Covered j p be ∧ lblOf be.2 ≠ 0 :=
      fun h1 => hpure ⟨⟨be, hbe, hc, hb0⟩, h1⟩
    have : litLabel inst mask j p = 0 := by by_contra hne; exact hno1 (hcl.mp hne)
    rw [hb0, this]
  · have h1 : litLabel inst mask j p ≠ 0 := hcl.mpr ⟨be, hbe, hc, hb0⟩
    omega

/-! ### Engine Lemma 1 — PROGRESS -/

/-- `bEq a a = 1` (reflexivity of the bit-equality gate). -/
theorem bEq_self (a : ℕ) : bEq a a = 1 := by unfold bEq; split_ifs <;> simp_all
/-- On bits, `bEq ≠ 0` is genuine equality. -/
theorem bEq_ne_zero_bits (a b : ℕ) (ha : a ≤ 1) (hb : b ≤ 1) : bEq a b ≠ 0 ↔ a = b := by
  unfold bEq; split_ifs with h1 h2 h2 <;> omega

/-- **First satisfying element (list order).** If some element of `l` satisfies `P`, then `l` splits as
`pre ++ x :: suf` with `P x` and no element of `pre` satisfying `P` — the FIRST satisfier. -/
theorem exists_first_split {α} (P : α → Prop) :
    ∀ (l : List α), (∃ x ∈ l, P x) →
      ∃ (pre : List α) (x : α) (suf : List α), l = pre ++ x :: suf ∧ P x ∧ ∀ y ∈ pre, ¬ P y := by
  intro l
  induction l with
  | nil => intro h; obtain ⟨x, hx, _⟩ := h; simp at hx
  | cons a as ih =>
      intro h
      by_cases hpa : P a
      · exact ⟨[], a, as, rfl, hpa, by simp⟩
      · have h' : ∃ x ∈ as, P x := by
          obtain ⟨x, hx, hpx⟩ := h
          rcases List.mem_cons.mp hx with rfl | hin
          · exact absurd hpx hpa
          · exact ⟨x, hin, hpx⟩
        obtain ⟨pre, x, suf, heq, hpx, hpre⟩ := ih h'
        refine ⟨a :: pre, x, suf, by rw [heq]; rfl, hpx, ?_⟩
        intro y hy; rcases List.mem_cons.mp hy with rfl | hin
        · exact hpa
        · exact hpre y hin

/-- **ENGINE LEMMA 1 — PROGRESS.** If the currently-remaining examples (`be.1 ≠ 0` in `msks.zip exs`)
admit a consistent 1-DL (with valid indices), and there is ≥1 remaining, then some feature-literal
`(j,p)` with `j < readK` is COVERING PURE on them (`coverLit ≠ 0`) — so `findLit` cannot stall.

⚠️ The two cases: (B) some rule of the DL fires on a remaining example — take the FIRST such rule
`r0`; every remaining example it covers is (by first-ness + consistency) classified by `r0` alone, so
they share `ruleL r0` ⇒ pure. (A) NO rule fires on any remaining example — then all remaining fall to
the DEFAULT, so they are monochromatic; picking feature `0` (needs `readK ≥ 1`) against any remaining
example's own bit gives a covering pure literal. -/
theorem progress (inst mask : ℕ) (hk : 0 < readK inst)
    (msks exs : List ℕ) (hmeq : mask = encodeList msks) (hdeq : readData inst = encodeList exs)
    (hcount : readM inst = exs.length) (hlen : msks.length = exs.length)
    (hfeat1 : ∀ e ∈ exs, ∀ j, featOf e j ≤ 1)
    (hne : ∃ be ∈ msks.zip exs, be.1 ≠ 0)
    (rules : List ℕ) (d : ℕ) (hval : ∀ r ∈ rules, ruleJ r < readK inst)
    (hcons : ∀ be ∈ msks.zip exs, be.1 ≠ 0 → evalDLn rules d be.2 = lblOf be.2) :
    ∃ j p, j < readK inst ∧ p ≤ 1 ∧ coverLit inst mask j p ≠ 0 := by
  -- factor the purity read-out: a covering witness + a shared label ⇒ `coverLit ≠ 0`
  have mk : ∀ (j p c : ℕ), (∃ be ∈ msks.zip exs, Covered j p be) →
      (∀ be ∈ msks.zip exs, Covered j p be → lblOf be.2 = c) → coverLit inst mask j p ≠ 0 := by
    intro j p c hcov hshare
    apply coverLit_of_semantic inst mask j p msks exs hmeq hdeq hcount hlen hcov
    rintro ⟨⟨b0, hb0, hc0, hl0⟩, ⟨b1, hb1, hc1, hl1⟩⟩
    rw [hshare b0 hb0 hc0] at hl0; rw [hshare b1 hb1 hc1] at hl1; exact hl1 hl0
  by_cases hcase : ∃ r ∈ rules, ∃ be ∈ msks.zip exs,
      be.1 ≠ 0 ∧ bEq (featOf be.2 (ruleJ r)) (ruleP r) ≠ 0
  · -- Case B: first rule firing on a remaining example
    obtain ⟨pre, r0, suf, hsplit, hPr0, hprefirst⟩ := exists_first_split _ rules hcase
    obtain ⟨be1, hbe1, hbe1act, hbe1fire⟩ := hPr0
    have hr0mem : r0 ∈ rules := by rw [hsplit]; exact List.mem_append_right _ (List.mem_cons_self ..)
    -- no earlier rule fires on any remaining example we test
    have hpre0 : ∀ be ∈ msks.zip exs, be.1 ≠ 0 →
        ∀ y ∈ pre, bEq (featOf be.2 (ruleJ y)) (ruleP y) = 0 := by
      intro be hbe hact y hy
      by_contra hz
      exact hprefirst y hy ⟨be, hbe, hact, hz⟩
    refine ⟨ruleJ r0, featOf be1.2 (ruleJ r0), hval r0 hr0mem,
      hfeat1 be1.2 (List.of_mem_zip hbe1).2 _, mk _ _ (ruleL r0) ?_ ?_⟩
    · exact ⟨be1, hbe1, hbe1act, by rw [bEq_self]; exact one_ne_zero⟩
    · intro be hbe hcov_be
      obtain ⟨hact, hcvb⟩ := hcov_be
      have hfeq : featOf be.2 (ruleJ r0) = featOf be1.2 (ruleJ r0) :=
        (bEq_ne_zero_bits _ _ (hfeat1 be.2 (List.of_mem_zip hbe).2 _)
          (hfeat1 be1.2 (List.of_mem_zip hbe1).2 _)).mp hcvb
      have hfire : bEq (featOf be.2 (ruleJ r0)) (ruleP r0) ≠ 0 := by rw [hfeq]; exact hbe1fire
      have hev := hcons be hbe hact
      rw [hsplit, evalDLn_append,
        evalDLn_not_fires pre _ be.2 (hpre0 be hbe hact),
        evalDLn, if_neg hfire] at hev
      exact hev.symm
  · -- Case A: no rule fires on any remaining example ⇒ monochromatic (= default)
    obtain ⟨be0, hbe0, hbe0act⟩ := hne
    refine ⟨0, featOf be0.2 0, hk, hfeat1 be0.2 (List.of_mem_zip hbe0).2 _, mk _ _ d ?_ ?_⟩
    · exact ⟨be0, hbe0, hbe0act, by rw [bEq_self]; exact one_ne_zero⟩
    · intro be hbe hcov_be
      obtain ⟨hact, _⟩ := hcov_be
      have hnf : ∀ r ∈ rules, bEq (featOf be.2 (ruleJ r)) (ruleP r) = 0 := by
        intro r hr
        by_contra hz
        exact hcase ⟨r, hr, be, hbe, hact, hz⟩
      have hev := hcons be hbe hact
      rw [evalDLn_not_fires rules d be.2 hnf] at hev
      exact hev.symm

/-! ### Engine Lemma 2 — OUTPUT CONSISTENCY

The round invariant, tracking the forward emitted DL `D` and the working mask `M`: every removed
example is classified by `D` to its own label (via a firing rule), every remaining example fires NO
rule of `D`. The firing-step is factored as `corrInvD_fire` with the literal `(j,p,l)` ABSTRACT — so no
tactic ever `whnf`-descends the symbolic `findLitVal` (see [[f20-whnf-opaque-verdict]]). -/

/-- The per-round correctness invariant on `(forward DL D, working mask M)`. -/
def CorrInvD (inst : ℕ) (D : List ℕ) (M : ℕ) : Prop :=
  ∀ i, i < readM inst →
    (headL (peel M i) = 0 →
      firesN D (headL (peel (readData inst) i)) ∧
      evalDLn D 0 (headL (peel (readData inst) i)) = lblOf (headL (peel (readData inst) i))) ∧
    (headL (peel M i) ≠ 0 → ¬ firesN D (headL (peel (readData inst) i)))

/-- **The firing-round step.** Appending the greedy round's covering-pure rule `⟨j,⟨p,l⟩⟩` and refining
the mask preserves `CorrInvD`. Abstract `j,p,l` (the caller supplies `flJ/flP/flL` of the literal). -/
theorem corrInvD_fire (inst : ℕ) (hw : WFBits inst) (M : ℕ) (hm : MaskValid M (readM inst))
    (j p l : ℕ) (hcov : coverLit inst M j p ≠ 0) (hl : l = litLabel inst M j p)
    (D : List ℕ) (hinv : CorrInvD inst D M) :
    CorrInvD inst (D ++ [Nat.pair j (Nat.pair p l)]) (maskUpdate inst M j p) := by
  have hw' := hw; have hm' := hm
  obtain ⟨_hwf, exs, hdeq, hdlen, hlbl1, hfeat1⟩ := hw'
  obtain ⟨msks, hmeq, hmlen, _hmbit⟩ := hm'
  set triple := Nat.pair j (Nat.pair p l) with htriple
  have hrj : ruleJ triple = j := by simp only [htriple, ruleJ, Nat.unpair_pair]
  have hrp : ruleP triple = p := by simp only [htriple, ruleP, Nat.unpair_pair]
  have hrl : ruleL triple = l := by simp only [htriple, ruleL, Nat.unpair_pair]
  intro i hi
  have ihrem := (hinv i hi).1
  have ihkeep := (hinv i hi).2
  -- the refined bit at `i`
  have hbit : headL (peel (maskUpdate inst M j p) i)
      = bAnd (headL (peel M i)) (bNot (bEq (featOf (headL (peel (readData inst) i)) j) p)) :=
    maskUpdate_getBit inst M j p i hw hm hi
  set exi := headL (peel (readData inst) i) with hexidef
  set b := headL (peel M i) with hbdef
  -- the new rule fires on `exi` iff `bEq (featOf exi j) p ≠ 0`
  have htrfire : bEq (featOf exi (ruleJ triple)) (ruleP triple) = bEq (featOf exi j) p := by
    rw [hrj, hrp]
  by_cases hb : b = 0
  · -- already removed before this round
    obtain ⟨hfir, hev⟩ := ihrem hb
    have hnew0 : headL (peel (maskUpdate inst M j p) i) = 0 := by
      rw [hbit, hb]; simp [bAnd]
    refine ⟨fun _ => ⟨?_, ?_⟩, fun h => absurd hnew0 h⟩
    · exact ⟨hfir.choose, List.mem_append_left _ hfir.choose_spec.1, hfir.choose_spec.2⟩
    · rw [evalDLn_append, evalDLn_fires_const D _ 0 exi hfir]; exact hev
  · by_cases hf : bEq (featOf exi j) p = 0
    · -- still remaining (rule does not fire)
      have hkeep := ihkeep hb
      have hnewne : headL (peel (maskUpdate inst M j p) i) ≠ 0 := by
        rw [hbit]; rw [bAnd_ne_zero]
        exact ⟨hb, by rw [bNot_ne_zero]; exact hf⟩
      refine ⟨fun h => absurd h hnewne, fun _ => ?_⟩
      rintro ⟨r, hr, hrfire⟩
      rcases List.mem_append.mp hr with hrin | hrin
      · exact hkeep ⟨r, hrin, hrfire⟩
      · rw [List.mem_singleton] at hrin; subst hrin
        rw [htrfire, hf] at hrfire; exact hrfire rfl
    · -- newly removed this round (rule fires; `exi` is covered)
      have hkeep := ihkeep hb
      have hnew0 : headL (peel (maskUpdate inst M j p) i) = 0 := by
        rw [hbit, bAnd_eq_zero]; exact Or.inr (bNot_pos_of_ne hf)
      -- covered ⇒ its label is `litLabel = l`
      have hcount : readM inst = exs.length := hdlen.symm
      have hzlen : msks.length = exs.length := hmlen.trans hdlen.symm
      have hie : i < exs.length := by rw [hdlen]; exact hi
      have him : i < msks.length := by rw [hmlen]; exact hi
      have hexi_ex : exi = exs[i] := by rw [hexidef, hdeq, getExample_encode exs i hie]
      have hb_ms : b = msks[i] := by rw [hbdef, hmeq, getExample_encode msks i him]
      have hzproof : i < (msks.zip exs).length := by
        rw [List.length_zip, hzlen, Nat.min_self]; exact hie
      have hzip : (msks[i], exs[i]) ∈ msks.zip exs := by
        have hz : (msks.zip exs)[i]'hzproof = (msks[i], exs[i]) := List.getElem_zip
        exact hz ▸ List.getElem_mem hzproof
      have hcovered : Covered j p (msks[i], exs[i]) := by
        refine ⟨?_, ?_⟩
        · change msks[i] ≠ 0; rw [← hb_ms]; exact hb
        · change bEq (featOf exs[i] j) p ≠ 0; rw [← hexi_ex]; exact hf
      have hlbleq : lblOf exs[i] = litLabel inst M j p :=
        covered_lbl_eq_litLabel inst M j p msks exs hmeq hdeq hcount hzlen hlbl1
          (msks[i], exs[i]) hzip hcovered hcov
      refine ⟨fun _ => ⟨?_, ?_⟩, fun h => absurd hnew0 h⟩
      · exact ⟨triple, List.mem_append_right _ (List.mem_singleton_self _),
          by rw [htrfire]; exact hf⟩
      · rw [evalDLn_append, evalDLn_not_fires D _ exi (fun r hr => by
          by_contra hz
          exact hkeep ⟨r, hr, hz⟩)]
        rw [evalDLn, htrfire, if_neg hf, hrl, hexi_ex, hlbleq, hl]

/-- **The round-invariant, assembled.** After `t` rounds the emitted forward DL `D` (valid indices) and
the working mask `svMask (svAcc n t)` satisfy `CorrInvD` — provided the loop STARTED from the all-ones
mask (every example initially remaining). Induction: no-op rounds carry it, firing rounds apply
`corrInvD_fire`. -/
theorem corrInv (n : ℕ) (hw : WFBits (svInst n))
    (hm0 : MaskValid (svMask0 n) (readM (svInst n)))
    (hone : svMask0 n = encodeList (List.replicate (readM (svInst n)) 1)) :
    ∀ t, ∃ D : List ℕ, svDL (svAcc n t) = encodeList D.reverse ∧
      (∀ r ∈ D, ruleJ r < readK (svInst n)) ∧ CorrInvD (svInst n) D (svMask (svAcc n t)) := by
  intro t
  induction t with
  | zero =>
    refine ⟨[], ?_, ?_, ?_⟩
    · rw [svAcc_zero]; simp only [svDL, Nat.unpair_pair, List.reverse_nil, encodeList]
    · intro r hr; simp at hr
    · intro i hi
      have hbit1 : headL (peel (svMask (svAcc n 0)) i) = 1 := by
        rw [svAcc_zero]; simp only [svMask, Nat.unpair_pair]
        rw [hone, getExample_encode _ i (by rw [List.length_replicate]; exact hi),
          List.getElem_replicate]
      refine ⟨fun h0 => ?_, fun _ => ?_⟩
      · rw [hbit1] at h0; exact absurd h0 one_ne_zero
      · rintro ⟨r, hr, -⟩; simp at hr
  | succ t ih =>
    obtain ⟨D, hDeq, hDval, hDinv⟩ := ih
    rw [svAcc_succ]
    unfold svStepFn
    split_ifs with hfound
    · exact ⟨D, hDeq, hDval, hDinv⟩
    · have hfound' : flFound (findLitVal (Nat.pair (svInst n) (svMask (svAcc n t)))) ≠ 0 := hfound
      obtain ⟨hj, _hp, hcov, hlbl⟩ :=
        findLit_sound (Nat.pair (svInst n) (svMask (svAcc n t))) hfound'
      -- rewrite `flInst N`/`flMask N` via SPECIFIC equalities (not `Nat.unpair_pair`), else kabstract
      -- checks `(findLitVal N).unpair` against the `Nat.pair` pattern and `whnf`-blows the literal scan.
      have hfiN : flInst (Nat.pair (svInst n) (svMask (svAcc n t))) = svInst n := by
        rw [flInst, Nat.unpair_pair]
      have hfmN : flMask (Nat.pair (svInst n) (svMask (svAcc n t))) = svMask (svAcc n t) := by
        rw [flMask, Nat.unpair_pair]
      rw [hfiN] at hj hcov hlbl
      rw [hfmN] at hcov hlbl
      -- Freeze the found literal as an OPAQUE `lit` (revert the facts, generalize, re-intro) so no
      -- downstream tactic can `whnf`-descend into the symbolic `findLitVal` iterate. `svUpdated` and
      -- its bridge lemmas take `lit` as an opaque argument, so the whole firing step stays symbolic.
      -- (See f20-whnf-opaque-verdict.)
      revert hj hcov hlbl
      generalize findLitVal (Nat.pair (svInst n) (svMask (svAcc n t))) = lit
      intro hj hcov hlbl
      refine ⟨D ++ [Nat.pair (flJ lit) (Nat.pair (flP lit) (flL lit))], ?_, ?_, ?_⟩
      · rw [svDL_svUpdated, hDeq]
        simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
          List.singleton_append, encodeList]
      · intro r hr
        rcases List.mem_append.mp hr with h | h
        · exact hDval r h
        · rw [List.mem_singleton] at h; subst h; rw [ruleJ_pair]; exact hj
      · rw [svMask_svUpdated]
        exact corrInvD_fire (svInst n) hw (svMask (svAcc n t)) (maskValid_svAcc n hw hm0 t).1
          _ _ _ hcov hlbl D hDinv

/-- **ENGINE LEMMA 2 — OUTPUT CONSISTENCY.** If `solve` (from the all-ones mask) empties its mask, its
emitted forward DL `D` is a consistent 1-DL (valid indices) for ALL examples: every example is removed
at the round whose covering rule first fires on it, and by purity that rule's label is the example's. -/
theorem output_consistent (n : ℕ) (hw : WFBits (svInst n))
    (hm0 : MaskValid (svMask0 n) (readM (svInst n)))
    (hone : svMask0 n = encodeList (List.replicate (readM (svInst n)) 1))
    (hfinal : ∀ i, i < readM (svInst n) →
      headL (peel (svMask (svAcc n (readM (svInst n)))) i) = 0)
    (exs : List ℕ) (hdeq : readData (svInst n) = encodeList exs)
    (hdlen : exs.length = readM (svInst n)) :
    ∃ (rules : List ℕ) (d : ℕ), (∀ r ∈ rules, ruleJ r < readK (svInst n)) ∧
      ∀ e ∈ exs, evalDLn rules d e = lblOf e := by
  obtain ⟨D, _hDeq, hDval, hDinv⟩ := corrInv n hw hm0 hone (readM (svInst n))
  refine ⟨D, 0, hDval, ?_⟩
  intro e he
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp he
  have hi' : i < readM (svInst n) := by rw [← hdlen]; exact hi
  obtain ⟨_hfir, hev⟩ := (hDinv i hi').1 (hfinal i hi')
  rw [hdeq, getExample_encode exs i hi] at hev
  exact hev

/-! ### C2c-ii — the monovariant and the decision theorem

The greedy loop runs a FIXED `readM` rounds, so turning "a consistent 1-DL exists" into "the final mask is
empty" needs a monovariant. Track `activeCount M = ∑_{i<m} bit_i` — the number of still-remaining
examples. Two facts drive it to zero within `m` rounds:
  * PROGRESS (`fire_of_active`): while the mask has an active bit, a consistent DL forces a covering-pure
    literal (`progress`), so `findLit` fires that round;
  * SHRINK (`activeCount_fire_lt`): a firing round zeroes ≥1 active bit (`coverLit_covers` +
    `maskUpdate_getBit`), so `activeCount` strictly drops.
From the all-ones mask (`activeCount = m`), after `m` rounds the count is `0`, i.e. the mask is empty. The
converse is Engine Lemma 2 (`output_consistent`). Packaged as `solve_decides`. -/

/-- `Nat.pair` is injective in both arguments (read off by `unpair`). -/
theorem pair_inj {a b c d : ℕ} (h : Nat.pair a b = Nat.pair c d) : a = c ∧ b = d := by
  have h' := congrArg Nat.unpair h
  rwa [Nat.unpair_pair, Nat.unpair_pair, Prod.mk.injEq] at h'

/-- `encodeList` is injective (flag-cons cells are `Nat.pair`-rigid), so the well-formed example list is
unique — lets us transport `WFBits`'s feature/label facts onto any `readData = encodeList exs`. -/
theorem encodeList_inj : ∀ a b : List ℕ, encodeList a = encodeList b → a = b := by
  intro a
  induction a with
  | nil =>
    intro b hb
    cases b with
    | nil => rfl
    | cons y ys =>
      rw [encodeList, encodeList] at hb
      have h' := congrArg Nat.unpair hb
      rw [Nat.unpair_zero, Nat.unpair_pair] at h'
      exact absurd (congrArg Prod.fst h') (by simp)
  | cons x xs ih =>
    intro b hb
    cases b with
    | nil =>
      rw [encodeList, encodeList] at hb
      have h' := congrArg Nat.unpair hb
      rw [Nat.unpair_zero, Nat.unpair_pair] at h'
      exact absurd (congrArg Prod.fst h') (by simp)
    | cons y ys =>
      rw [encodeList, encodeList] at hb
      obtain ⟨_, h2⟩ := pair_inj hb
      obtain ⟨hxy, htl⟩ := pair_inj h2
      rw [hxy, ih ys htl]

/-- The monovariant: number of still-active bits among the first `m` mask slots. -/
def activeCount (M m : ℕ) : ℕ := ∑ i ∈ Finset.range m, headL (peel M i)

/-- Zero active count ⇒ the mask is empty on every visited slot. -/
theorem allZero_of_activeCount_zero (M m : ℕ) (h : activeCount M m = 0) :
    ∀ i, i < m → headL (peel M i) = 0 := by
  intro i hi
  exact (Finset.sum_eq_zero_iff.mp h) i (Finset.mem_range.mpr hi)

/-- The initial (all-ones) mask has full active count `m`. -/
theorem activeCount_all_ones (n : ℕ)
    (hone : svMask0 n = encodeList (List.replicate (readM (svInst n)) 1)) :
    activeCount (svMask (svAcc n 0)) (readM (svInst n)) = readM (svInst n) := by
  unfold activeCount
  rw [svAcc_zero]
  simp only [svMask, Nat.unpair_pair]
  rw [show (∑ i ∈ Finset.range (readM (svInst n)), headL (peel (svMask0 n) i))
        = ∑ _i ∈ Finset.range (readM (svInst n)), 1 from
      Finset.sum_congr rfl (fun i hi => by
        rw [Finset.mem_range] at hi
        rw [hone, getExample_encode _ i (by rw [List.length_replicate]; exact hi),
          List.getElem_replicate])]
  simp

/-- **SHRINK.** A firing round zeroes ≥1 active bit, so `activeCount` strictly decreases. -/
theorem activeCount_fire_lt (n t : ℕ) (hw : WFBits (svInst n))
    (hm0 : MaskValid (svMask0 n) (readM (svInst n)))
    (hfire : flFound (findLitVal (Nat.pair (svInst n) (svMask (svAcc n t)))) ≠ 0) :
    activeCount (svMask (svAcc n (t + 1))) (readM (svInst n))
      < activeCount (svMask (svAcc n t)) (readM (svInst n)) := by
  have hmi : MaskValid (svMask (svAcc n t)) (readM (svInst n)) := (maskValid_svAcc n hw hm0 t).1
  obtain ⟨_hj, _hp, hcov, _hlbl⟩ :=
    findLit_sound (Nat.pair (svInst n) (svMask (svAcc n t))) hfire
  have hfi : flInst (Nat.pair (svInst n) (svMask (svAcc n t))) = svInst n := by
    rw [flInst, Nat.unpair_pair]
  have hfm : flMask (Nat.pair (svInst n) (svMask (svAcc n t))) = svMask (svAcc n t) := by
    rw [flMask, Nat.unpair_pair]
  rw [hfi] at hcov
  rw [hfm] at hcov
  -- the successor mask on a firing round is `maskUpdate` by the found literal
  have hsucc : svMask (svAcc n (t + 1))
      = maskUpdate (svInst n) (svMask (svAcc n t))
          (flJ (findLitVal (Nat.pair (svInst n) (svMask (svAcc n t)))))
          (flP (findLitVal (Nat.pair (svInst n) (svMask (svAcc n t))))) := by
    rw [svAcc_succ]; unfold svStepFn
    split_ifs with hf
    · exact absurd hf hfire
    · rw [svMask_svUpdated]
  rw [hsucc]
  -- freeze the literal as an OPAQUE `lit` (see f20-whnf-opaque-verdict)
  revert hcov
  generalize findLitVal (Nat.pair (svInst n) (svMask (svAcc n t))) = lit
  intro hcov
  unfold activeCount
  apply Finset.sum_lt_sum
  · -- termwise: the refined bit never exceeds the old bit
    intro i hi
    rw [Finset.mem_range] at hi
    rw [maskUpdate_getBit (svInst n) (svMask (svAcc n t)) (flJ lit) (flP lit) i hw hmi hi]
    exact bAnd_le_left _ _
  · -- strict: the covered example's bit drops from `≠0` to `0`
    obtain ⟨msks, exs, hmeq, hdeqc, hlen, hcount, be, hbe, hcovered⟩ :=
      coverLit_covers (svInst n) (svMask (svAcc n t)) (flJ lit) (flP lit) hw hmi hcov
    obtain ⟨i0, hi0z, hget⟩ := List.mem_iff_getElem.mp hbe
    rw [List.getElem_zip] at hget
    have hzlen : (msks.zip exs).length = readM (svInst n) := by
      rw [List.length_zip, hlen, Nat.min_self]; exact hcount.symm
    have hi0 : i0 < readM (svInst n) := by rw [hzlen] at hi0z; exact hi0z
    have hi0m : i0 < msks.length := by rw [hlen, ← hcount]; exact hi0
    have hi0e : i0 < exs.length := by rw [← hcount]; exact hi0
    have hbe1 : be.1 = msks[i0] := by rw [← hget]
    have hbe2 : be.2 = exs[i0] := by rw [← hget]
    have holdbit : headL (peel (svMask (svAcc n t)) i0) = msks[i0] := by
      rw [hmeq, getExample_encode msks i0 hi0m]
    have hdatabit : headL (peel (readData (svInst n)) i0) = exs[i0] := by
      rw [hdeqc, getExample_encode exs i0 hi0e]
    have hfire_i0 : bEq (featOf (headL (peel (readData (svInst n)) i0)) (flJ lit)) (flP lit) ≠ 0 := by
      rw [hdatabit, ← hbe2]; exact hcovered.2
    refine ⟨i0, Finset.mem_range.mpr hi0, ?_⟩
    rw [maskUpdate_getBit (svInst n) (svMask (svAcc n t)) (flJ lit) (flP lit) i0 hw hmi hi0,
      bNot_pos_of_ne hfire_i0, holdbit, (bAnd_eq_zero (msks[i0]) 0).mpr (Or.inr rfl)]
    have hne0 : msks[i0] ≠ 0 := by rw [← hbe1]; exact hcovered.1
    omega

/-- An empty mask cannot fire: no active example ⇒ no covering literal ⇒ `findLit` returns `found = 0`. -/
theorem not_fire_of_allZero (n t : ℕ) (hw : WFBits (svInst n))
    (hm0 : MaskValid (svMask0 n) (readM (svInst n)))
    (hz : ∀ i, i < readM (svInst n) → headL (peel (svMask (svAcc n t)) i) = 0) :
    flFound (findLitVal (Nat.pair (svInst n) (svMask (svAcc n t)))) = 0 := by
  by_contra hne
  obtain ⟨_hj, _hp, hcov, _hlbl⟩ :=
    findLit_sound (Nat.pair (svInst n) (svMask (svAcc n t))) hne
  have hfi : flInst (Nat.pair (svInst n) (svMask (svAcc n t))) = svInst n := by
    rw [flInst, Nat.unpair_pair]
  have hfm : flMask (Nat.pair (svInst n) (svMask (svAcc n t))) = svMask (svAcc n t) := by
    rw [flMask, Nat.unpair_pair]
  rw [hfi] at hcov
  rw [hfm] at hcov
  have hmi : MaskValid (svMask (svAcc n t)) (readM (svInst n)) := (maskValid_svAcc n hw hm0 t).1
  revert hcov
  generalize findLitVal (Nat.pair (svInst n) (svMask (svAcc n t))) = lit
  intro hcov
  obtain ⟨msks, exs, hmeq, _hdeqc, hlen, hcount, be, hbe, hcovered⟩ :=
    coverLit_covers (svInst n) (svMask (svAcc n t)) (flJ lit) (flP lit) hw hmi hcov
  obtain ⟨i0, hi0z, hget⟩ := List.mem_iff_getElem.mp hbe
  rw [List.getElem_zip] at hget
  have hzlen : (msks.zip exs).length = readM (svInst n) := by
    rw [List.length_zip, hlen, Nat.min_self]; exact hcount.symm
  have hi0 : i0 < readM (svInst n) := by rw [hzlen] at hi0z; exact hi0z
  have hi0m : i0 < msks.length := by rw [hlen, ← hcount]; exact hi0
  have hbe1 : be.1 = msks[i0] := by rw [← hget]
  have hcontra : headL (peel (svMask (svAcc n t)) i0) ≠ 0 := by
    rw [hmeq, getExample_encode msks i0 hi0m, ← hbe1]; exact hcovered.1
  exact hcontra (hz i0 hi0)

/-- **PROGRESS.** While some example is still active, a consistent 1-DL forces a covering-pure literal, so
the round fires. Bridges `progress` (which yields a bit `p ≤ 1`) to `findLit_found_iff`. -/
theorem fire_of_active (n t : ℕ) (hw : WFBits (svInst n)) (hk : 0 < readK (svInst n))
    (hm0 : MaskValid (svMask0 n) (readM (svInst n)))
    (exs : List ℕ) (hdeq : readData (svInst n) = encodeList exs)
    (hdlen : exs.length = readM (svInst n))
    (hcons : ExistsConsistentDL (svInst n) exs)
    (i0 : ℕ) (hi0 : i0 < readM (svInst n))
    (hact : headL (peel (svMask (svAcc n t)) i0) ≠ 0) :
    flFound (findLitVal (Nat.pair (svInst n) (svMask (svAcc n t)))) ≠ 0 := by
  obtain ⟨rules, d, hval, hcons'⟩ := hcons
  have hmi : MaskValid (svMask (svAcc n t)) (readM (svInst n)) := (maskValid_svAcc n hw hm0 t).1
  obtain ⟨msks, hmeq, hmlen, _hmbit⟩ := hmi
  -- transport `WFBits`'s feature facts onto the given `exs`
  obtain ⟨_hwf, exsW, hdeqW, _hdlenW, _hlblW, hfeatW⟩ := hw
  have hexeq : exsW = exs := encodeList_inj _ _ (by rw [← hdeqW, ← hdeq])
  subst hexeq
  -- the active slot gives a `zip` witness with a nonzero mask bit
  have hi0m : i0 < msks.length := by rw [hmlen]; exact hi0
  have hi0e : i0 < exsW.length := by rw [hdlen]; exact hi0
  have hmsi : msks[i0] ≠ 0 := by
    rw [hmeq, getExample_encode msks i0 hi0m] at hact; exact hact
  have hi0z : i0 < (msks.zip exsW).length := by
    rw [List.length_zip, hmlen, hdlen, Nat.min_self]; exact hi0
  have hbe : (msks[i0], exsW[i0]) ∈ msks.zip exsW := by
    have hmem := List.getElem_mem hi0z
    rwa [List.getElem_zip] at hmem
  have hcons'' : ∀ be ∈ msks.zip exsW, be.1 ≠ 0 → evalDLn rules d be.2 = lblOf be.2 :=
    fun be hbe' _ => hcons' be.2 (List.of_mem_zip hbe').2
  obtain ⟨j, p, hjk, hp1, hcov⟩ :=
    progress (svInst n) (svMask (svAcc n t)) hk msks exsW hmeq hdeqW hdlen.symm
      (by rw [hmlen, hdlen]) hfeatW ⟨(msks[i0], exsW[i0]), hbe, hmsi⟩ rules d hval hcons''
  rw [findLit_found_iff]
  have hfi : flInst (Nat.pair (svInst n) (svMask (svAcc n t))) = svInst n := by
    rw [flInst, Nat.unpair_pair]
  have hfm : flMask (Nat.pair (svInst n) (svMask (svAcc n t))) = svMask (svAcc n t) := by
    rw [flMask, Nat.unpair_pair]
  rw [hfi, hfm]
  refine ⟨j, hjk, ?_⟩
  interval_cases p
  · exact Or.inl hcov
  · exact Or.inr hcov

/-- **The monovariant bound.** For a consistent 1-DL, after `t` rounds either the count has fallen by `t`
(so `activeCount + t ≤ m`) or the mask is already empty. At `t = m` both force the mask empty. -/
theorem activeCount_bound (n : ℕ) (hw : WFBits (svInst n)) (hk : 0 < readK (svInst n))
    (hm0 : MaskValid (svMask0 n) (readM (svInst n)))
    (hone : svMask0 n = encodeList (List.replicate (readM (svInst n)) 1))
    (exs : List ℕ) (hdeq : readData (svInst n) = encodeList exs)
    (hdlen : exs.length = readM (svInst n))
    (hcons : ExistsConsistentDL (svInst n) exs) :
    ∀ t, activeCount (svMask (svAcc n t)) (readM (svInst n)) + t ≤ readM (svInst n)
      ∨ (∀ i, i < readM (svInst n) → headL (peel (svMask (svAcc n t)) i) = 0) := by
  intro t
  induction t with
  | zero => left; rw [activeCount_all_ones n hone]; omega
  | succ k ih =>
    -- an empty round stays empty (the loop freezes)
    have freeze : (∀ i, i < readM (svInst n) → headL (peel (svMask (svAcc n k)) i) = 0) →
        ∀ i, i < readM (svInst n) → headL (peel (svMask (svAcc n (k + 1))) i) = 0 := by
      intro hemp i hi
      have hnf := not_fire_of_allZero n k hw hm0 hemp
      have hfix : svMask (svAcc n (k + 1)) = svMask (svAcc n k) := by
        rw [svAcc_succ]; unfold svStepFn; rw [if_pos hnf]
      rw [hfix]; exact hemp i hi
    rcases ih with hL | hR
    · by_cases hemp : ∀ i, i < readM (svInst n) → headL (peel (svMask (svAcc n k)) i) = 0
      · exact Or.inr (freeze hemp)
      · obtain ⟨i0, hi0, hact⟩ :
            ∃ i, i < readM (svInst n) ∧ headL (peel (svMask (svAcc n k)) i) ≠ 0 := by
          by_contra hcon
          exact hemp (fun i hi => by by_contra hb; exact hcon ⟨i, hi, hb⟩)
        have hfire := fire_of_active n k hw hk hm0 exs hdeq hdlen hcons i0 hi0 hact
        have hlt := activeCount_fire_lt n k hw hm0 hfire
        left; omega
    · exact Or.inr (freeze hR)

/-- **C2c CAPSTONE — greedy correctness.** From the all-ones mask, `solve` empties its mask **iff** a
consistent 1-DL over valid feature literals exists. (⇒) is Engine Lemma 2 (`output_consistent`); (⇐) is
the monovariant (`activeCount_bound`), driving the count to `0` within `readM` rounds. -/
theorem solve_decides (n : ℕ) (hn : SolveWF n) (hk : 0 < readK (svInst n))
    (hone : svMask0 n = encodeList (List.replicate (readM (svInst n)) 1))
    (exs : List ℕ) (hdeq : readData (svInst n) = encodeList exs)
    (hdlen : exs.length = readM (svInst n)) :
    (∀ i, i < readM (svInst n) →
        headL (peel (svMask (svAcc n (readM (svInst n)))) i) = 0)
      ↔ ExistsConsistentDL (svInst n) exs := by
  obtain ⟨hw, hm0⟩ := hn
  constructor
  · intro hfinal
    exact output_consistent n hw hm0 hone hfinal exs hdeq hdlen
  · intro hcons
    rcases activeCount_bound n hw hk hm0 hone exs hdeq hdlen hcons (readM (svInst n)) with hL | hR
    · intro i hi
      have hz : activeCount (svMask (svAcc n (readM (svInst n)))) (readM (svInst n)) = 0 := by omega
      exact allZero_of_activeCount_zero _ _ hz i hi
    · exact hR

/-! ## Axiom-cleanliness guards (CI-enforced)

Each guard **fails `lake build`** if the theorem's axiom set ever drifts from the standard
`[propext, Classical.choice, Quot.sound]`. -/

/-- info: 'OneDL.val_cReverse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms val_cReverse

/-- info: 'OneDL.maskValid_maskUpdate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms maskValid_maskUpdate

/-- info: 'OneDL.maskUpdate_getBit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms maskUpdate_getBit

/-- info: 'OneDL.polyTime_maskUpdate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms polyTime_maskUpdate

/-- info: 'OneDL.findLit_found_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms findLit_found_iff

/-- info: 'OneDL.findLit_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms findLit_sound

/-- info: 'OneDL.polyTime_findLit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms polyTime_findLit

/-- info: 'OneDL.polyTime_solve' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms polyTime_solve

/-- info: 'OneDL.maskValid_solve' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms maskValid_solve

/-- info: 'OneDL.dlModel_svAcc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms dlModel_svAcc

/-- info: 'OneDL.progress' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms progress

/-- info: 'OneDL.output_consistent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms output_consistent

/-- info: 'OneDL.solve_decides' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms solve_decides

end OneDL
