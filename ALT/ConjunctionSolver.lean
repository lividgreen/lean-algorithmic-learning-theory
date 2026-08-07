/-
Copyright (c) 2026 Mykola Palamarchuk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mykola Palamarchuk
-/
import ALT.Code.BitGates
import ALT.DecisionListData

-- Formal-check file, not Mathlib-destined: opt out of the house-style linters.
set_option linter.style.header false
set_option linter.style.longLine false

/-!
# The conjunction consistency solver

Provenance: [SQ] §4's *General form* paragraph, which names conjunctions first among the classes
whose poly-time consistency problem discharges Theorem 4.1's maintainer hypothesis (Lemma 4.2(3))
by the same argument as the 1-decision-list class (`ALT/DecisionListSolver.lean`,
`ALT/DecisionListPredictor.lean`): poly-time consistency ⇒ poly-time maintenance
(Hirsh–Mishra–Pitt 2004). This module makes the conjunction case a second machine-checked instance.

Builds on `ALT/DecisionListData.lean` (the shared instance/example encoding: `readK`/`readM`,
`peel`/`cPeel`, `headL`/`tailL`, `WF`/`WFBits`, `encodeList`, `lblOf`/`fvOf`/`featOf`) and
`ALT/Code/BitGates.lean` (the bit-logic gates `cAnd`/`cOr`/`cNot`/`cEqBit`). Deliberately does NOT
import `ALT/DecisionListSolver.lean`: a conjunction is not a decision list, and the elimination
algorithm below needs none of the greedy solver's machinery.

## The class

A conjunction over `k` Boolean features is a `List` of literals, each a pair `⟨j, p⟩` read as
"feature `j` equals `p`"; it evaluates to `1` on an example when EVERY literal is satisfied, else
`0`. A literal set containing both polarities of one feature (`⟨j,0⟩` and `⟨j,1⟩` both present) is a
legitimate member, not an exclusion — a single feature cannot equal both bits, so such a set simply
never accepts.

## The decider (stages CJ-A/CJ-B/CJ-C)

**CJ-A** (`cAliveLoop`) computes, for a fixed feature `j`, whether literal `⟨j,0⟩` and `⟨j,1⟩` each
survive elimination: a literal survives iff no labelled-`1` example violates it (an `m`-round
AND-fold over the examples). **CJ-B** (`cRejectLoop`) checks, for a fixed example `e`, whether SOME
surviving literal is violated by `e` (a `k`-round OR-fold over the features, invoking CJ-A fresh at
each feature). **CJ-C** (`cConjSolve`) is the assembled decider: every example is labelled `1` or
rejected by the surviving set (an `m`-round AND-fold over the examples, invoking CJ-B fresh at each
example). No literal list is ever built or reversed — every stage folds to a NUMBER (a bit or a bit
pair), which is what keeps the construction to three nested numeric folds instead of the 1-DL
solver's greedy round/list-splice machinery.
-/

namespace Conj

open OneDL
open Nat.Partrec (Code)
open Nat.Partrec.Code
open TimeCost

/-! ## The literal type and conjunction evaluation -/

/-- Feature index of a literal `r = ⟨j, p⟩`: "feature `j` equals `p`". -/
def litJ (r : ℕ) : ℕ := r.unpair.1
/-- Polarity of a literal `r = ⟨j, p⟩`. -/
def litP (r : ℕ) : ℕ := r.unpair.2

private theorem litJ_pair (j p : ℕ) : litJ (Nat.pair j p) = j := by simp [litJ, Nat.unpair_pair]
private theorem litP_pair (j p : ℕ) : litP (Nat.pair j p) = p := by simp [litP, Nat.unpair_pair]

/-- **Conjunction evaluation.** A conjunction is a `List` of literals; it evaluates to `1` on `e`
when every literal is satisfied, else `0`. Satisfaction compares `featOf e (litJ r)` against
`litP r` by zero/nonzero-ness (mirroring `OneDL`'s own `bEq`), not raw equality: this is what makes
a "junk" polarity `litP r ∉ {0,1}` behave exactly like `1` rather than being unsatisfiable by
construction, matching `ExistsConsistentConj`'s literal space below (feature-index-valid, polarity
unconstrained) with no separate polarity hypothesis needed anywhere downstream. -/
def evalConj : List ℕ → ℕ → ℕ
  | [], _ => 1
  | r :: rs, e => if (featOf e (litJ r) = 0 ↔ litP r = 0) then evalConj rs e else 0

/-- The conjunction's output is always a bit. -/
theorem evalConj_le_one (lits : List ℕ) (e : ℕ) : evalConj lits e ≤ 1 := by
  induction lits with
  | nil => simp [evalConj]
  | cons r rs ih => unfold evalConj; split <;> simp [ih]

/-- **Membership characterisation.** `evalConj` accepts `e` iff every literal of `lits` is satisfied
by `e` — order- and duplicate-independent, unlike a decision list's first-match semantics. -/
theorem evalConj_eq_one_iff (lits : List ℕ) (e : ℕ) :
    evalConj lits e = 1 ↔ ∀ r ∈ lits, (featOf e (litJ r) = 0 ↔ litP r = 0) := by
  induction lits with
  | nil => simp [evalConj]
  | cons r rs ih =>
      unfold evalConj
      by_cases h : (featOf e (litJ r) = 0 ↔ litP r = 0)
      · rw [if_pos h]
        simp only [List.mem_cons, forall_eq_or_imp]
        exact ⟨fun he => ⟨h, ih.mp he⟩, fun hp => ih.mpr hp.2⟩
      · rw [if_neg h]
        simp only [List.mem_cons, forall_eq_or_imp]
        constructor
        · intro h0; exact absurd h0 (by decide)
        · intro hp; exact absurd hp.1 h

/-- The contrapositive form: `evalConj` REJECTS `e` iff some literal of `lits` is violated. -/
theorem evalConj_eq_zero_iff (lits : List ℕ) (e : ℕ) :
    evalConj lits e = 0 ↔ ∃ r ∈ lits, ¬ (featOf e (litJ r) = 0 ↔ litP r = 0) := by
  have h1 := evalConj_le_one lits e
  have h2 := evalConj_eq_one_iff lits e
  constructor
  · intro h0
    by_contra hcon
    have hall : ∀ r ∈ lits, (featOf e (litJ r) = 0 ↔ litP r = 0) := by
      intro r hr
      by_contra hne
      exact hcon ⟨r, hr, hne⟩
    have := h2.mpr hall
    omega
  · rintro ⟨r, hr, hne⟩
    by_contra h0
    have heq1 : evalConj lits e = 1 := by omega
    exact hne (h2.mp heq1 r hr)

/-- **Consistency.** Every example is classified to its own label by the conjunction. -/
def ConsistentConj (lits : List ℕ) (exs : List ℕ) : Prop := ∀ e ∈ exs, evalConj lits e = lblOf e

/-- **Existence of a consistent conjunction** over VALID feature literals (`litJ r < readK inst`) —
the literal space the solver searches. This is what the decider below decides. -/
def ExistsConsistentConj (inst : ℕ) (exs : List ℕ) : Prop :=
  ∃ lits : List ℕ, (∀ r ∈ lits, litJ r < readK inst) ∧ ConsistentConj lits exs

/-! ## Local semantic bit-ops (mirror the gate `val` laws, cf. `OneDL`'s own local mirrors) -/

/-- `¬` on a bit — mirrors `val_cNot`. -/
def bitNot (n : ℕ) : ℕ := if n = 0 then 1 else 0
/-- `∧` on bits — mirrors `val_cAnd`. -/
def bitAnd (a b : ℕ) : ℕ := if a = 0 then 0 else (if b = 0 then 0 else 1)
/-- `∨` on bits — mirrors `val_cOr`. -/
def bitOr (a b : ℕ) : ℕ := if a = 0 then (if b = 0 then 0 else 1) else 1

theorem val_cNot' (n : ℕ) : val cNot n = bitNot n := val_cNot n
theorem val_cAnd' (a b : ℕ) : val cAnd (Nat.pair a b) = bitAnd a b := val_cAnd a b
theorem val_cOr' (a b : ℕ) : val cOr (Nat.pair a b) = bitOr a b := val_cOr a b

theorem bitNot_le_one (n : ℕ) : bitNot n ≤ 1 := by unfold bitNot; split <;> simp
theorem bitAnd_le_one (a b : ℕ) : bitAnd a b ≤ 1 := by unfold bitAnd; split <;> [simp; split <;> simp]
theorem bitOr_le_one (a b : ℕ) : bitOr a b ≤ 1 := by unfold bitOr; split <;> [split <;> simp; simp]

/-! ## Stage CJ-A — per-feature literal survival, an `m`-round AND-fold over the examples

`aliveVal0 inst j` / `aliveVal1 inst j` are `1` iff no labelled-`1` example of `inst` violates
literal `⟨j,0⟩` / `⟨j,1⟩`. Packed input `N = ⟨inst, j⟩`; accumulator `⟨exSuf, ⟨a0, a1⟩⟩`. -/

/-- The instance, from the packed input `⟨inst, j⟩`. -/
private def instA (N : ℕ) : ℕ := N.unpair.1
/-- The feature index, from the packed input `⟨inst, j⟩`. -/
private def jA (N : ℕ) : ℕ := N.unpair.2

/-- The unscanned example suffix. -/
private def exSufA (acc : ℕ) : ℕ := acc.unpair.1
/-- The running survival bit for literal `⟨j,0⟩`. -/
private def a0A (acc : ℕ) : ℕ := acc.unpair.2.unpair.1
/-- The running survival bit for literal `⟨j,1⟩`. -/
private def a1A (acc : ℕ) : ℕ := acc.unpair.2.unpair.2

/-- The initial accumulator: the full example list, both literals vacuously alive. -/
private def aliveInitAcc (data : ℕ) : ℕ := Nat.pair data (Nat.pair 1 1)

/-- The semantic step: read the current example off the carried suffix, AND each survival bit with
"this example does not violate the literal" (vacuously true when the example is labelled `0`), and
peel the suffix one cell. -/
private def aliveStepFn (j acc : ℕ) : ℕ :=
  Nat.pair (tailL (exSufA acc))
    (Nat.pair
      (bitAnd (a0A acc)
        (bitOr (bitNot (lblOf (headL (exSufA acc)))) (bitNot (featOf (headL (exSufA acc)) j))))
      (bitAnd (a1A acc)
        (bitOr (bitNot (lblOf (headL (exSufA acc)))) (featOf (headL (exSufA acc)) j))))

/-! ### The `Code` realisation of stage CJ-A -/

/-- Flag-cons head, as a `Code` (mirrors `OneDL`'s own private copy). -/
def cHeadL : Code := comp left right
/-- Flag-cons tail, as a `Code`. -/
def cTailL : Code := comp right right

private theorem rfindFree_cHeadL : RfindFree cHeadL := ⟨trivial, trivial⟩
private theorem rfindFree_cTailL : RfindFree cTailL := ⟨trivial, trivial⟩
private theorem val_cHeadL (L : ℕ) : val cHeadL L = headL L := by
  simp only [cHeadL, val_comp, val_left, val_right, headL]
private theorem val_cTailL (L : ℕ) : val cTailL L = tailL L := by
  simp only [cTailL, val_comp, val_right, tailL]
private theorem tc_cHeadL (L : ℕ) : tc cHeadL L = 3 := by simp only [cHeadL, tc_comp, tc_left, tc_right]
private theorem tc_cTailL (L : ℕ) : tc cTailL L = 3 := by simp only [cTailL, tc_comp, tc_right]

/-- `instA` as a `Code`. -/
def cInstA : Code := left
/-- `jA` as a `Code`. -/
def cJA : Code := right
/-- `readData (instA N)` as a `Code` (`readData inst = tailL inst` on this instance encoding). -/
def cDataA : Code := comp cTailL cInstA

private theorem val_cInstA (N : ℕ) : val cInstA N = instA N := by simp only [cInstA, val_left, instA]
private theorem val_cJA (N : ℕ) : val cJA N = jA N := by simp only [cJA, val_right, jA]
private theorem val_cDataA (N : ℕ) : val cDataA N = readData (instA N) := by
  simp only [cDataA, val_comp, val_cTailL, val_cInstA, tailL, readData, instA]

/-- Base code: build `aliveInitAcc (readData (instA N))` from the packed input `N`. -/
def cAliveInit : Code := pair cDataA (pair (constCode 1) (constCode 1))

private theorem rfindFree_cAliveInit : RfindFree cAliveInit :=
  ⟨⟨rfindFree_cTailL, trivial⟩, rfindFree_constCode 1, rfindFree_constCode 1⟩

private theorem val_cAliveInit (N : ℕ) : val cAliveInit N = aliveInitAcc (readData (instA N)) := by
  simp only [cAliveInit, val_pair, val_cDataA, val_constCode, aliveInitAcc]

/-- Accumulator, out of the step input `⟨a, ⟨i, acc⟩⟩`. -/
def cAccA : Code := comp right right
/-- The literal's feature index, from the seed `a = ⟨inst,j⟩`. -/
def cJaA : Code := comp cJA left
/-- The example suffix, from the accumulator. -/
def cExSufA : Code := comp left cAccA
/-- The `a0` field, from the accumulator. -/
def cA0A : Code := comp left (comp right cAccA)
/-- The `a1` field, from the accumulator. -/
def cA1A : Code := comp right (comp right cAccA)
/-- The current example. -/
def cCurExA : Code := comp cHeadL cExSufA
/-- The current example's label. -/
def cCurLblA : Code := comp left cCurExA
/-- The current example's feature vector. -/
def cFvCurA : Code := comp right cCurExA
/-- The current example's feature `j`. -/
def cCurFeatA : Code := comp cHeadL (comp cPeel (pair cFvCurA cJaA))
/-- Is the current example irrelevant to literal `⟨j,0⟩`'s survival (label `0`, or feature `= 0`)? -/
def cSafe0A : Code := comp cOr (pair (comp cNot cCurLblA) (comp cNot cCurFeatA))
/-- Is the current example irrelevant to literal `⟨j,1⟩`'s survival (label `0`, or feature `= 1`)? -/
def cSafe1A : Code := comp cOr (pair (comp cNot cCurLblA) cCurFeatA)
/-- The updated `a0` field. -/
def cA0'A : Code := comp cAnd (pair cA0A cSafe0A)
/-- The updated `a1` field. -/
def cA1'A : Code := comp cAnd (pair cA1A cSafe1A)
/-- The step: peel the suffix, AND each survival bit with this round's safety bit. -/
def cAliveStep : Code := pair (comp cTailL cExSufA) (pair cA0'A cA1'A)

private theorem rfindFree_cAliveStep : RfindFree cAliveStep := by
  simp only [cAliveStep, cA0'A, cA1'A, cSafe0A, cSafe1A, cCurLblA, cCurFeatA, cFvCurA, cCurExA,
    cExSufA, cA0A, cA1A, cAccA, cJaA, cJA, cHeadL, cTailL, cAnd, cOr, cNot, cIsPos, cShape0, cSwap,
    isPosCore, notCore, orCore, cPeel, cTailStep, constCode, RfindFree, and_self]

private theorem val_cA0A (a i acc : ℕ) : val cA0A (Nat.pair a (Nat.pair i acc)) = a0A acc := by
  simp only [cA0A, cAccA, val_comp, val_left, val_right, Nat.unpair_pair, a0A]
private theorem val_cA1A (a i acc : ℕ) : val cA1A (Nat.pair a (Nat.pair i acc)) = a1A acc := by
  simp only [cA1A, cAccA, val_comp, val_right, Nat.unpair_pair, a1A]
private theorem val_cExSufA (a i acc : ℕ) : val cExSufA (Nat.pair a (Nat.pair i acc)) = exSufA acc := by
  simp only [cExSufA, cAccA, val_comp, val_left, val_right, Nat.unpair_pair, exSufA]
private theorem val_cJaA (a i acc : ℕ) : val cJaA (Nat.pair a (Nat.pair i acc)) = jA a := by
  simp only [cJaA, cJA, val_comp, val_left, val_right, Nat.unpair_pair, jA]
private theorem val_cCurExA (a i acc : ℕ) :
    val cCurExA (Nat.pair a (Nat.pair i acc)) = headL (exSufA acc) := by
  simp only [cCurExA, val_comp, val_cHeadL, val_cExSufA]
private theorem val_cCurLblA (a i acc : ℕ) :
    val cCurLblA (Nat.pair a (Nat.pair i acc)) = lblOf (headL (exSufA acc)) := by
  simp only [cCurLblA, val_comp, val_left, val_cCurExA, lblOf]
private theorem val_cFvCurA (a i acc : ℕ) :
    val cFvCurA (Nat.pair a (Nat.pair i acc)) = fvOf (headL (exSufA acc)) := by
  simp only [cFvCurA, val_comp, val_right, val_cCurExA, fvOf]
private theorem val_cCurFeatA (a i acc : ℕ) :
    val cCurFeatA (Nat.pair a (Nat.pair i acc)) = featOf (headL (exSufA acc)) (jA a) := by
  simp only [cCurFeatA, val_comp, val_pair, val_cHeadL, val_cPeel, val_cFvCurA, val_cJaA,
    featOf]

private theorem val_cAliveStep (a i acc : ℕ) :
    val cAliveStep (Nat.pair a (Nat.pair i acc)) = aliveStepFn (jA a) acc := by
  simp only [cAliveStep, cA0'A, cA1'A, cSafe0A, cSafe1A, val_pair, val_comp, val_cAnd', val_cOr',
    val_cNot', val_cTailL, val_cA0A, val_cA1A, val_cExSufA, val_cCurLblA, val_cCurFeatA,
    aliveStepFn]

private theorem val_cAliveLoop_raw (N t : ℕ) :
    val (prec cAliveInit cAliveStep) (Nat.pair N t)
      = (aliveStepFn (jA N))^[t] (aliveInitAcc (readData (instA N))) := by
  induction t with
  | zero => rw [val_prec_zero, val_cAliveInit, Function.iterate_zero_apply]
  | succ k ih => rw [val_prec_succ, val_cAliveStep, ih, Function.iterate_succ_apply']

/-- The accumulator after the full `m`-round scan. -/
private def aliveAcc (N : ℕ) : ℕ := (aliveStepFn (jA N))^[readM (instA N)] (aliveInitAcc (readData (instA N)))

/-- `aliveVal0 inst j`: `1` iff no labelled-`1` example of `inst` violates literal `⟨j,0⟩`. -/
def aliveVal0 (inst j : ℕ) : ℕ := a0A (aliveAcc (Nat.pair inst j))
/-- `aliveVal1 inst j`: `1` iff no labelled-`1` example of `inst` violates literal `⟨j,1⟩`. -/
def aliveVal1 (inst j : ℕ) : ℕ := a1A (aliveAcc (Nat.pair inst j))

/-- Round budget: `readM (instA N)`. -/
def cAliveCount : Code := comp cReadM cInstA
/-- Identity shaper (the loop seed is the whole packed input `⟨inst,j⟩`). -/
def cAliveId : Code := pair left right
/-- The assembled CJ-A scan. -/
def cAliveLoop : Code := comp (prec cAliveInit cAliveStep) (pair cAliveId cAliveCount)

private theorem rfindFree_cAliveId : RfindFree cAliveId := ⟨trivial, trivial⟩
private theorem rfindFree_cAliveCount : RfindFree cAliveCount := ⟨rfindFree_cReadM, trivial⟩
private theorem rfindFree_cAliveLoop : RfindFree cAliveLoop :=
  ⟨⟨rfindFree_cAliveInit, rfindFree_cAliveStep⟩, rfindFree_cAliveId, rfindFree_cAliveCount⟩

private theorem val_cAliveId (N : ℕ) : val cAliveId N = N := by
  simp only [cAliveId, val_pair, val_left, val_right, Nat.pair_unpair]
private theorem val_cAliveCount (N : ℕ) : val cAliveCount N = readM (instA N) := by
  simp only [cAliveCount, val_comp, val_cReadM, val_cInstA]

private theorem val_cAliveLoop (N : ℕ) : val cAliveLoop N = aliveAcc N := by
  rw [cAliveLoop, val_comp, val_pair, val_cAliveId, val_cAliveCount, val_cAliveLoop_raw, aliveAcc]

/-! ### Reading `aliveVal0`/`aliveVal1` off `cAliveLoop`'s bare output

Exposed so downstream stages read the two survival bits off `cAliveLoop` by composing with a plain
projection — the fix for the T41-style private bridge (a public equation lemma from the start,
rather than a Code-level `rfl` reconstructing a private composition after the fact). -/

/-- The `a0`-field of a BARE `cAliveLoop` output (not a step-input triple). -/
def cReadA0 : Code := comp left right
/-- The `a1`-field of a BARE `cAliveLoop` output. -/
def cReadA1 : Code := comp right right

private theorem val_cReadA0 (acc : ℕ) : val cReadA0 acc = a0A acc := by
  simp only [cReadA0, val_comp, val_left, val_right, a0A]
private theorem val_cReadA1 (acc : ℕ) : val cReadA1 acc = a1A acc := by
  simp only [cReadA1, val_comp, val_right, a1A]

/-- **CJ-A's public value laws.** `aliveVal0`/`aliveVal1` are exactly `cAliveLoop`'s output read
through the plain projections above — no private internals needed downstream. -/
private theorem val_aliveVal0 (inst j : ℕ) :
    val (comp cReadA0 cAliveLoop) (Nat.pair inst j) = aliveVal0 inst j := by
  rw [val_comp, val_cAliveLoop, val_cReadA0, aliveVal0]
private theorem val_aliveVal1 (inst j : ℕ) :
    val (comp cReadA1 cAliveLoop) (Nat.pair inst j) = aliveVal1 inst j := by
  rw [val_comp, val_cAliveLoop, val_cReadA1, aliveVal1]

/-! ### CJ-A correctness — the `List`-model fold characterisation -/

private theorem bitAnd_ne_zero (a b : ℕ) : bitAnd a b ≠ 0 ↔ a ≠ 0 ∧ b ≠ 0 := by
  unfold bitAnd; by_cases ha : a = 0 <;> by_cases hb : b = 0 <;> simp [ha, hb]
private theorem bitOr_ne_zero (a b : ℕ) : bitOr a b ≠ 0 ↔ a ≠ 0 ∨ b ≠ 0 := by
  unfold bitOr; by_cases ha : a = 0 <;> by_cases hb : b = 0 <;> simp [ha, hb]
private theorem bitNot_ne_zero (n : ℕ) : bitNot n ≠ 0 ↔ n = 0 := by
  unfold bitNot; by_cases h : n = 0 <;> simp [h]

/-- **The AND-fold realises the list.** Running the semantic step over the encoded example list for
`exs.length` iterations from seed `⟨a0,a1⟩` empties the suffix and AND-folds the per-example safety
bit into each of `a0`/`a1` independently. -/
private theorem aliveStepFn_iterate (j : ℕ) (exs : List ℕ) (a0 a1 : ℕ) :
    (aliveStepFn j)^[exs.length] (Nat.pair (encodeList exs) (Nat.pair a0 a1))
      = Nat.pair 0 (Nat.pair
          (exs.foldl (fun z e => bitAnd z (bitOr (bitNot (lblOf e)) (bitNot (featOf e j)))) a0)
          (exs.foldl (fun z e => bitAnd z (bitOr (bitNot (lblOf e)) (featOf e j))) a1)) := by
  induction exs generalizing a0 a1 with
  | nil => simp [encodeList]
  | cons e es ih =>
      rw [List.length_cons, Function.iterate_succ_apply]
      have hx : aliveStepFn j (Nat.pair (encodeList (e :: es)) (Nat.pair a0 a1))
          = Nat.pair (encodeList es)
              (Nat.pair (bitAnd a0 (bitOr (bitNot (lblOf e)) (bitNot (featOf e j))))
                        (bitAnd a1 (bitOr (bitNot (lblOf e)) (featOf e j)))) := by
        simp only [aliveStepFn, exSufA, a0A, a1A, Nat.unpair_pair, headL_encode_cons,
          tailL_encode_cons]
      rw [hx, ih]
      simp only [List.foldl_cons]

/-- A `bitAnd`-accumulating `foldl` is nonzero iff the seed is, and every element fires. -/
private theorem andFold_ne_zero_iff {α : Type*} (f : α → ℕ) (l : List α) (init : ℕ) :
    (l.foldl (fun z x => bitAnd z (f x)) init) ≠ 0 ↔ init ≠ 0 ∧ ∀ x ∈ l, f x ≠ 0 := by
  induction l generalizing init with
  | nil => simp
  | cons x xs ih =>
      rw [List.foldl_cons, ih, bitAnd_ne_zero]
      simp only [List.mem_cons, forall_eq_or_imp]
      tauto

/-- **`aliveVal0` characterisation.** Literal `⟨j,0⟩` survives iff no example of `exs` both carries
label `1` and violates it. -/
theorem aliveVal0_iff (inst j : ℕ) (exs : List ℕ)
    (hdeq : readData inst = encodeList exs) (hdlen : exs.length = readM inst) :
    aliveVal0 inst j ≠ 0 ↔ ∀ e ∈ exs, lblOf e = 0 ∨ featOf e j = 0 := by
  have hval : aliveVal0 inst j
      = exs.foldl (fun z e => bitAnd z (bitOr (bitNot (lblOf e)) (bitNot (featOf e j)))) 1 := by
    unfold aliveVal0 aliveAcc a0A
    simp only [instA, jA, Nat.unpair_pair, aliveInitAcc]
    rw [hdeq, ← hdlen, aliveStepFn_iterate]
    simp only [Nat.unpair_pair]
  rw [hval, andFold_ne_zero_iff]
  simp only [ne_eq, one_ne_zero, not_false_eq_true, true_and, bitOr_ne_zero, bitNot_ne_zero]

/-- **`aliveVal1` characterisation.** Literal `⟨j,1⟩` survives iff no example of `exs` both carries
label `1` and violates it (`featOf e j = 0`; stated as `≠ 0` rather than `= 1` to hold with no bit
hypothesis — the two coincide under `WFBits`, used where the distinction matters below). -/
theorem aliveVal1_iff (inst j : ℕ) (exs : List ℕ)
    (hdeq : readData inst = encodeList exs) (hdlen : exs.length = readM inst) :
    aliveVal1 inst j ≠ 0 ↔ ∀ e ∈ exs, lblOf e = 0 ∨ featOf e j ≠ 0 := by
  have hval : aliveVal1 inst j
      = exs.foldl (fun z e => bitAnd z (bitOr (bitNot (lblOf e)) (featOf e j))) 1 := by
    unfold aliveVal1 aliveAcc a1A
    simp only [instA, jA, Nat.unpair_pair, aliveInitAcc]
    rw [hdeq, ← hdlen, aliveStepFn_iterate]
    simp only [Nat.unpair_pair]
  rw [hval, andFold_ne_zero_iff]
  simp only [ne_eq, one_ne_zero, not_false_eq_true, true_and, bitOr_ne_zero, bitNot_ne_zero]

private theorem aliveVal0_le_one (inst j : ℕ) : aliveVal0 inst j ≤ 1 := by
  unfold aliveVal0 aliveAcc a0A
  generalize (readM (instA (Nat.pair inst j))) = t
  cases t with
  | zero => simp [aliveInitAcc, Nat.unpair_pair]
  | succ k =>
      rw [Function.iterate_succ_apply']
      simp only [aliveStepFn, a0A, Nat.unpair_pair]
      exact bitAnd_le_one _ _

private theorem aliveVal1_le_one (inst j : ℕ) : aliveVal1 inst j ≤ 1 := by
  unfold aliveVal1 aliveAcc a1A
  generalize (readM (instA (Nat.pair inst j))) = t
  cases t with
  | zero => simp [aliveInitAcc, Nat.unpair_pair]
  | succ k =>
      rw [Function.iterate_succ_apply']
      simp only [aliveStepFn, a1A, Nat.unpair_pair]
      exact bitAnd_le_one _ _

/-! ### CJ-A native cost

Mirrors `OneDL`'s own `tc_cPurity_raw` derivation: every gate is `O(1)` on bit operands, and the only
value-scaling cost is the feature peel to index `j`, `O(j)`. -/

/-- The peel loop's native cost — re-derived here since `OneDL`'s own copy is private. -/
private theorem tc_cPeel_le (L m : ℕ) : tc cPeel (Nat.pair L m) ≤ 8 * m + 4 := by
  unfold cPeel
  have h := tc_prec_le (cf := pair left right) (cg := cTailStep) (B := 7)
    (fun x => (tc_cTailStep x).le) L m
  simp only [tc_pair, tc_left, tc_right] at h
  omega

private theorem inv_exSufA_peel (j data : ℕ) :
    ∀ i, exSufA ((aliveStepFn j)^[i] (aliveInitAcc data)) = peel data i := by
  intro i
  induction i with
  | zero => simp [aliveInitAcc, exSufA, peel]
  | succ k ih =>
      rw [Function.iterate_succ_apply',
        show exSufA (aliveStepFn j ((aliveStepFn j)^[k] (aliveInitAcc data)))
          = tailL (exSufA ((aliveStepFn j)^[k] (aliveInitAcc data))) from by
            simp only [aliveStepFn, exSufA, Nat.unpair_pair],
        ih]
      simp only [peel, Function.iterate_succ_apply']

private theorem inv_a0A_le_one (j data : ℕ) : ∀ t, a0A ((aliveStepFn j)^[t] (aliveInitAcc data)) ≤ 1 := by
  intro t
  cases t with
  | zero => simp [aliveInitAcc, a0A]
  | succ k =>
      rw [Function.iterate_succ_apply']; simp only [aliveStepFn, a0A, Nat.unpair_pair]
      exact bitAnd_le_one _ _
private theorem inv_a1A_le_one (j data : ℕ) : ∀ t, a1A ((aliveStepFn j)^[t] (aliveInitAcc data)) ≤ 1 := by
  intro t
  cases t with
  | zero => simp [aliveInitAcc, a1A]
  | succ k =>
      rw [Function.iterate_succ_apply']; simp only [aliveStepFn, a1A, Nat.unpair_pair]
      exact bitAnd_le_one _ _

/-- **Visited-state bit-ness.** At every visited example `i < readM inst`, the label and feature `j`
are bits (`WFBits`). -/
private theorem visited_bits_A (inst j i : ℕ) (hw : WFBits inst) (hi : i < readM inst) :
    lblOf (headL (exSufA ((aliveStepFn j)^[i] (aliveInitAcc (readData inst))))) ≤ 1 ∧
    featOf (headL (exSufA ((aliveStepFn j)^[i] (aliveInitAcc (readData inst))))) j ≤ 1 := by
  rw [inv_exSufA_peel]
  obtain ⟨_hwf, exs, hdeq, hdlen, hlbl, hfeat⟩ := hw
  have hie : i < exs.length := by rw [hdlen]; exact hi
  rw [hdeq, getExample_encode exs i hie]
  exact ⟨hlbl _ (List.getElem_mem hie), hfeat _ (List.getElem_mem hie) j⟩

private theorem tc_cAccA_le (a i acc : ℕ) : tc cAccA (Nat.pair a (Nat.pair i acc)) ≤ 3 := by
  simp only [cAccA, tc_comp, tc_right]; omega
private theorem tc_cExSufA_le (a i acc : ℕ) : tc cExSufA (Nat.pair a (Nat.pair i acc)) ≤ 5 := by
  have := tc_cAccA_le a i acc; simp only [cExSufA, tc_comp, tc_left]; omega
private theorem tc_cA0A_le (a i acc : ℕ) : tc cA0A (Nat.pair a (Nat.pair i acc)) ≤ 7 := by
  have := tc_cAccA_le a i acc; simp only [cA0A, tc_comp, tc_left, tc_right]; omega
private theorem tc_cA1A_le (a i acc : ℕ) : tc cA1A (Nat.pair a (Nat.pair i acc)) ≤ 7 := by
  have := tc_cAccA_le a i acc; simp only [cA1A, tc_comp, tc_right]; omega
private theorem tc_cJaA_le (a i acc : ℕ) : tc cJaA (Nat.pair a (Nat.pair i acc)) ≤ 5 := by
  simp only [cJaA, cJA, tc_comp, tc_left, tc_right]; omega
private theorem tc_cCurExA_le (a i acc : ℕ) : tc cCurExA (Nat.pair a (Nat.pair i acc)) ≤ 10 := by
  have := tc_cExSufA_le a i acc; simp only [cCurExA, tc_comp, tc_cHeadL]; omega
private theorem tc_cCurLblA_le (a i acc : ℕ) : tc cCurLblA (Nat.pair a (Nat.pair i acc)) ≤ 15 := by
  have := tc_cCurExA_le a i acc; simp only [cCurLblA, tc_comp, tc_left]; omega

private theorem tc_cFvCurA_le (a i acc : ℕ) : tc cFvCurA (Nat.pair a (Nat.pair i acc)) ≤ 15 := by
  have := tc_cCurExA_le a i acc; simp only [cFvCurA, tc_comp, tc_right]; omega

/-- **The feature read: the one value-scaling cost, `O(jA a)`.** Left unreduced (`val cFvCurA`/
`val cJaA` stay as atoms) so the goal's own `simp`-normal form matches `hpeel` verbatim — the same
device `OneDL`'s own `tc_cFeat_le` uses. -/
private theorem tc_cCurFeatA_le (a i acc : ℕ) :
    tc cCurFeatA (Nat.pair a (Nat.pair i acc)) ≤ 8 * jA a + 40 := by
  have hfv := tc_cFvCurA_le a i acc
  have hja := tc_cJaA_le a i acc
  have hpeel := tc_cPeel_le (val cFvCurA (Nat.pair a (Nat.pair i acc)))
    (val cJaA (Nat.pair a (Nat.pair i acc)))
  have hjav := val_cJaA a i acc
  simp only [cCurFeatA, tc_comp, tc_pair, tc_cHeadL, val_pair]
  omega

private theorem tc_cSafe0A_le (a i acc : ℕ) (hlbl : lblOf (headL (exSufA acc)) ≤ 1)
    (hfeat : featOf (headL (exSufA acc)) (jA a) ≤ 1) :
    tc cSafe0A (Nat.pair a (Nat.pair i acc)) ≤ 8 * jA a + 300 := by
  have hl := tc_cCurLblA_le a i acc
  have hf := tc_cCurFeatA_le a i acc
  have hlv : val cCurLblA (Nat.pair a (Nat.pair i acc)) ≤ 1 := by rw [val_cCurLblA]; exact hlbl
  have hfv : val cCurFeatA (Nat.pair a (Nat.pair i acc)) ≤ 1 := by rw [val_cCurFeatA]; exact hfeat
  have hnl := tc_cNot_bit hlv
  have hnf := tc_cNot_le (val cCurFeatA (Nat.pair a (Nat.pair i acc)))
  have hnlv : val (comp cNot cCurLblA) (Nat.pair a (Nat.pair i acc)) ≤ 1 := by
    rw [val_comp, val_cNot']; exact bitNot_le_one _
  have hnfv : val (comp cNot cCurFeatA) (Nat.pair a (Nat.pair i acc)) ≤ 1 := by
    rw [val_comp, val_cNot']; exact bitNot_le_one _
  have hor := tc_cOr_bit hnlv hnfv
  simp only [cSafe0A, tc_comp, tc_pair, val_pair]
  omega

private theorem tc_cSafe1A_le (a i acc : ℕ) (hlbl : lblOf (headL (exSufA acc)) ≤ 1)
    (hfeat : featOf (headL (exSufA acc)) (jA a) ≤ 1) :
    tc cSafe1A (Nat.pair a (Nat.pair i acc)) ≤ 8 * jA a + 300 := by
  have hl := tc_cCurLblA_le a i acc
  have hf := tc_cCurFeatA_le a i acc
  have hlv : val cCurLblA (Nat.pair a (Nat.pair i acc)) ≤ 1 := by rw [val_cCurLblA]; exact hlbl
  have hfv : val cCurFeatA (Nat.pair a (Nat.pair i acc)) ≤ 1 := by rw [val_cCurFeatA]; exact hfeat
  have hnl := tc_cNot_bit hlv
  have hnlv : val (comp cNot cCurLblA) (Nat.pair a (Nat.pair i acc)) ≤ 1 := by
    rw [val_comp, val_cNot']; exact bitNot_le_one _
  have hor := tc_cOr_bit hnlv hfv
  simp only [cSafe1A, tc_comp, tc_pair, val_pair]
  omega

private theorem tc_cA0'A_le (a i acc : ℕ) (h0 : a0A acc ≤ 1) (hlbl : lblOf (headL (exSufA acc)) ≤ 1)
    (hfeat : featOf (headL (exSufA acc)) (jA a) ≤ 1) :
    tc cA0'A (Nat.pair a (Nat.pair i acc)) ≤ 8 * jA a + 700 := by
  have h0t := tc_cA0A_le a i acc
  have hst := tc_cSafe0A_le a i acc hlbl hfeat
  have h0v : val cA0A (Nat.pair a (Nat.pair i acc)) ≤ 1 := by rw [val_cA0A]; exact h0
  have hsv : val cSafe0A (Nat.pair a (Nat.pair i acc)) ≤ 1 := by
    unfold cSafe0A
    rw [val_comp, val_pair]
    exact val_cOr_le_one _ _
  have hand := tc_cAnd_bit h0v hsv
  simp only [cA0'A, tc_comp, tc_pair, val_pair]
  omega

private theorem tc_cA1'A_le (a i acc : ℕ) (h1 : a1A acc ≤ 1) (hlbl : lblOf (headL (exSufA acc)) ≤ 1)
    (hfeat : featOf (headL (exSufA acc)) (jA a) ≤ 1) :
    tc cA1'A (Nat.pair a (Nat.pair i acc)) ≤ 8 * jA a + 700 := by
  have h1t := tc_cA1A_le a i acc
  have hst := tc_cSafe1A_le a i acc hlbl hfeat
  have h1v : val cA1A (Nat.pair a (Nat.pair i acc)) ≤ 1 := by rw [val_cA1A]; exact h1
  have hsv : val cSafe1A (Nat.pair a (Nat.pair i acc)) ≤ 1 := by
    unfold cSafe1A
    rw [val_comp, val_pair]
    exact val_cOr_le_one _ _
  have hand := tc_cAnd_bit h1v hsv
  simp only [cA1'A, tc_comp, tc_pair, val_pair]
  omega

/-- **The per-step cost bound.** Under bit operands (accumulator flags, label, feature), the step
costs `≤ 16·jA a + 1500`: every gate is `O(1)` and only the feature peel scales. -/
private theorem tc_cAliveStep_le (a i acc : ℕ) (h0 : a0A acc ≤ 1) (h1 : a1A acc ≤ 1)
    (hlbl : lblOf (headL (exSufA acc)) ≤ 1) (hfeat : featOf (headL (exSufA acc)) (jA a) ≤ 1) :
    tc cAliveStep (Nat.pair a (Nat.pair i acc)) ≤ 16 * jA a + 1500 := by
  have h0' := tc_cA0'A_le a i acc h0 hlbl hfeat
  have h1' := tc_cA1'A_le a i acc h1 hlbl hfeat
  have hex := tc_cExSufA_le a i acc
  simp only [cAliveStep, tc_pair, tc_comp, tc_cTailL]
  omega

/-- **`cAliveLoop`'s native cost on a well-formed instance.** -/
private theorem tc_cAliveLoop_raw (inst j : ℕ) (hw : WFBits inst) :
    tc cAliveLoop (Nat.pair inst j) ≤ (16 * j + 1501) * readM inst + 500 := by
  have hpair : val (pair cAliveId cAliveCount) (Nat.pair inst j) = Nat.pair (Nat.pair inst j) (readM inst) := by
    rw [val_pair, val_cAliveId, val_cAliveCount]
    simp only [instA, Nat.unpair_pair]
  have hidcount : tc (pair cAliveId cAliveCount) (Nat.pair inst j) ≤ 20 := by
    simp only [cAliveId, cAliveCount, cReadM, cInstA, tc_pair, tc_comp, tc_left, tc_right]; omega
  have hjv : jA (Nat.pair inst j) = j := by simp [jA, Nat.unpair_pair]
  have hiv : instA (Nat.pair inst j) = inst := by simp [instA, Nat.unpair_pair]
  have hstep : ∀ i, i < readM inst →
      tc cAliveStep (Nat.pair (Nat.pair inst j)
          (Nat.pair i (val (prec cAliveInit cAliveStep) (Nat.pair (Nat.pair inst j) i))))
        ≤ 16 * j + 1500 := by
    intro i hi
    rw [show val (prec cAliveInit cAliveStep) (Nat.pair (Nat.pair inst j) i)
      = (aliveStepFn (jA (Nat.pair inst j)))^[i] (aliveInitAcc (readData (instA (Nat.pair inst j))))
      from val_cAliveLoop_raw (Nat.pair inst j) i]
    rw [hiv, hjv]
    obtain ⟨hlbl, hfeat⟩ := visited_bits_A inst j i hw hi
    have h0 := inv_a0A_le_one j (readData inst) i
    have h1 := inv_a1A_le_one j (readData inst) i
    have hfeat' : featOf (headL (exSufA ((aliveStepFn j)^[i] (aliveInitAcc (readData inst)))))
        (jA (Nat.pair inst j)) ≤ 1 := by rw [hjv]; exact hfeat
    have hres := tc_cAliveStep_le (Nat.pair inst j) i
      ((aliveStepFn j)^[i] (aliveInitAcc (readData inst))) h0 h1 hlbl hfeat'
    rwa [hjv] at hres
  have hprec := tc_prec_le' (cf := cAliveInit) (cg := cAliveStep) (a := Nat.pair inst j)
    (B := 16 * j + 1500) (readM inst) hstep
  have hinit : tc cAliveInit (Nat.pair inst j) ≤ 20 := by
    have h1 := tc_constCode_le 1 (Nat.pair inst j)
    have h2 := tc_cTailL (val left (Nat.pair inst j))
    simp only [cAliveInit, cDataA, tc_pair, tc_comp, cInstA, tc_left]
    omega
  have heq : (16 * j + 1500 + 1) * readM inst = (16 * j + 1501) * readM inst := by ring
  simp only [cAliveLoop, tc_comp, hpair]
  omega

/-! ## Stage CJ-B — per-example rejection, a `k`-round OR-fold over the features

`rejectsVal inst e` is `1` iff some surviving literal is violated by `e`. Packed input
`M = ⟨inst, e⟩`; accumulator a single bit. Unlike CJ-A, the step genuinely needs the round index
(the feature `i` it is currently examining), so it is characterised directly off `val (prec …)`
(mirroring `OneDL`'s own `svAcc`/`flAcc`) rather than via `Function.iterate`. -/

/-- The instance, from the packed input `⟨inst, e⟩`. -/
private def instB (M : ℕ) : ℕ := M.unpair.1
/-- The candidate example, from the packed input `⟨inst, e⟩`. -/
private def exB (M : ℕ) : ℕ := M.unpair.2

/-- Is literal `⟨i,0⟩` or `⟨i,1⟩` (whichever of the two survives) violated by `e`? -/
def violatedFn (inst e i : ℕ) : ℕ :=
  bitOr (bitAnd (aliveVal0 inst i) (featOf e i)) (bitAnd (aliveVal1 inst i) (bitNot (featOf e i)))

/-- The semantic step: OR this round's violation bit into the running accumulator. -/
private def rejStepFn (a i acc : ℕ) : ℕ := bitOr acc (violatedFn (instB a) (exB a) i)

/-! ### The `Code` realisation of stage CJ-B -/

/-- The accumulator, out of the step input `⟨a, ⟨i, acc⟩⟩`. -/
def cAccB : Code := comp right right
/-- The round index `i`, out of the step input. -/
def cIB : Code := comp left right
/-- The seed `a = ⟨inst,e⟩`, out of the step input. -/
def cSeedB : Code := left
/-- `instB a`, out of the step input. -/
def cInstStepB : Code := comp left cSeedB
/-- `exB a`, out of the step input. -/
def cExStepB : Code := comp right cSeedB
/-- `⟨instB a, i⟩`, the packed argument for a fresh CJ-A call. -/
def cAliveArgB : Code := pair cInstStepB cIB
/-- `aliveVal0 (instB a) i`, via a fresh CJ-A call. Left-associated so `val_comp` splits off exactly
the `comp cReadA0 cAliveLoop` sub-term `val_aliveVal0` is stated over. -/
def cAlive0B : Code := comp (comp cReadA0 cAliveLoop) cAliveArgB
/-- `aliveVal1 (instB a) i`, via a fresh CJ-A call. -/
def cAlive1B : Code := comp (comp cReadA1 cAliveLoop) cAliveArgB
/-- The feature vector of the candidate example. -/
def cFvB : Code := comp right cExStepB
/-- Feature `i` of the candidate example. -/
def cFeatB : Code := comp cHeadL (comp cPeel (pair cFvB cIB))
/-- Literal `⟨i,0⟩` violated: it survives, and the candidate's feature `i` is `1`. -/
def cViol0B : Code := comp cAnd (pair cAlive0B cFeatB)
/-- Literal `⟨i,1⟩` violated: it survives, and the candidate's feature `i` is `0`. -/
def cViol1B : Code := comp cAnd (pair cAlive1B (comp cNot cFeatB))
/-- Either literal violated this round. -/
def cViolB : Code := comp cOr (pair cViol0B cViol1B)
/-- The step: OR the accumulator with this round's violation bit. -/
def cRejStep : Code := comp cOr (pair cAccB cViolB)
/-- Base code: the accumulator starts at `0` (nothing violated yet). -/
def cRejBase : Code := zero

private theorem rfindFree_cRejStep : RfindFree cRejStep := by
  simp only [cRejStep, cViolB, cViol0B, cViol1B, cAlive0B, cAlive1B, cAliveArgB, cFeatB, cFvB,
    cExStepB, cInstStepB, cSeedB, cIB, cAccB, cHeadL, cAnd, cOr, cNot, cIsPos, cShape0, cSwap,
    isPosCore, notCore, orCore, cPeel, cTailStep, constCode, cReadA0, cReadA1,
    cAliveLoop, cAliveInit, cAliveStep, cA0'A, cA1'A, cSafe0A, cSafe1A, cCurLblA, cCurFeatA, cFvCurA,
    cCurExA, cExSufA, cA0A, cA1A, cAccA, cJaA, cJA, cTailL, cAliveId, cAliveCount, cReadM, cInstA,
    cDataA, RfindFree, and_self]

private theorem val_cAccB (a i acc : ℕ) : val cAccB (Nat.pair a (Nat.pair i acc)) = acc := by
  simp only [cAccB, val_comp, val_right, Nat.unpair_pair]
private theorem val_cIB (a i acc : ℕ) : val cIB (Nat.pair a (Nat.pair i acc)) = i := by
  simp only [cIB, val_comp, val_left, val_right, Nat.unpair_pair]
private theorem val_cSeedB (a i acc : ℕ) : val cSeedB (Nat.pair a (Nat.pair i acc)) = a := by
  simp only [cSeedB, val_left, Nat.unpair_pair]
private theorem val_cInstStepB (a i acc : ℕ) : val cInstStepB (Nat.pair a (Nat.pair i acc)) = instB a := by
  simp only [cInstStepB, val_comp, val_left, val_cSeedB, instB]
private theorem val_cExStepB (a i acc : ℕ) : val cExStepB (Nat.pair a (Nat.pair i acc)) = exB a := by
  simp only [cExStepB, val_comp, val_right, val_cSeedB, exB]
private theorem val_cAliveArgB (a i acc : ℕ) :
    val cAliveArgB (Nat.pair a (Nat.pair i acc)) = Nat.pair (instB a) i := by
  simp only [cAliveArgB, val_pair, val_cInstStepB, val_cIB]
private theorem val_cAlive0B (a i acc : ℕ) :
    val cAlive0B (Nat.pair a (Nat.pair i acc)) = aliveVal0 (instB a) i := by
  rw [cAlive0B, val_comp, val_cAliveArgB, val_aliveVal0]
private theorem val_cAlive1B (a i acc : ℕ) :
    val cAlive1B (Nat.pair a (Nat.pair i acc)) = aliveVal1 (instB a) i := by
  rw [cAlive1B, val_comp, val_cAliveArgB, val_aliveVal1]
private theorem val_cFvB (a i acc : ℕ) : val cFvB (Nat.pair a (Nat.pair i acc)) = fvOf (exB a) := by
  simp only [cFvB, val_comp, val_cExStepB, val_right, fvOf]
private theorem val_cFeatB (a i acc : ℕ) :
    val cFeatB (Nat.pair a (Nat.pair i acc)) = featOf (exB a) i := by
  simp only [cFeatB, val_comp, val_pair, val_cHeadL, val_cPeel, val_cFvB, val_cIB, featOf]
private theorem val_cRejStep (a i acc : ℕ) :
    val cRejStep (Nat.pair a (Nat.pair i acc)) = rejStepFn a i acc := by
  simp only [cRejStep, cViolB, cViol0B, cViol1B, val_pair, val_comp, val_cOr', val_cAnd', val_cNot',
    val_cAccB, val_cAlive0B, val_cAlive1B, val_cFeatB, rejStepFn, violatedFn]

/-- **CJ-B's accumulator**, characterised directly off `val (prec …)` — the round index is
genuinely needed by the step, so this mirrors `OneDL`'s own `svAcc`/`flAcc` rather than
`Function.iterate`. -/
def rejAcc (M t : ℕ) : ℕ := val (prec cRejBase cRejStep) (Nat.pair M t)

private theorem rejAcc_zero (M : ℕ) : rejAcc M 0 = 0 := by
  unfold rejAcc; rw [val_prec_zero, cRejBase, val_zero]
private theorem rejAcc_succ (M t : ℕ) : rejAcc M (t + 1) = rejStepFn M t (rejAcc M t) := by
  unfold rejAcc; rw [val_prec_succ, val_cRejStep]

/-- `instB`, from the OUTER packed input (not a step input). -/
def cInstOfB : Code := left
/-- Round budget: `readK (instB M)`. -/
def cRejCount : Code := comp cReadK cInstOfB
/-- Identity shaper: the loop seed is the whole packed input `⟨inst,e⟩`. -/
def cRejId : Code := pair left right
/-- The assembled CJ-B scan. -/
def cRejLoop : Code := comp (prec cRejBase cRejStep) (pair cRejId cRejCount)

private theorem rfindFree_cInstOfB : RfindFree cInstOfB := trivial
private theorem rfindFree_cRejCount : RfindFree cRejCount := ⟨rfindFree_cReadK, rfindFree_cInstOfB⟩
private theorem rfindFree_cRejId : RfindFree cRejId := ⟨trivial, trivial⟩
private theorem rfindFree_cRejBase : RfindFree cRejBase := trivial
private theorem rfindFree_cRejLoop : RfindFree cRejLoop :=
  ⟨⟨rfindFree_cRejBase, rfindFree_cRejStep⟩, rfindFree_cRejId, rfindFree_cRejCount⟩

private theorem val_cInstOfB (M : ℕ) : val cInstOfB M = instB M := by simp only [cInstOfB, val_left, instB]
private theorem val_cRejCount (M : ℕ) : val cRejCount M = readK (instB M) := by
  simp only [cRejCount, val_comp, val_cReadK, val_cInstOfB]
private theorem val_cRejId (M : ℕ) : val cRejId M = M := by
  simp only [cRejId, val_pair, val_left, val_right, Nat.pair_unpair]

private theorem val_cRejLoop (M : ℕ) : val cRejLoop M = rejAcc M (readK (instB M)) := by
  rw [cRejLoop, val_comp, val_pair, val_cRejId, val_cRejCount, rejAcc]

/-- `rejectsVal inst e`: `1` iff some surviving literal is violated by `e`. -/
def rejectsVal (inst e : ℕ) : ℕ := rejAcc (Nat.pair inst e) (readK inst)

/-- **CJ-B's public value law.** -/
private theorem val_cRejLoop_rejectsVal (inst e : ℕ) :
    val cRejLoop (Nat.pair inst e) = rejectsVal inst e := by
  rw [val_cRejLoop]
  simp only [instB, Nat.unpair_pair, rejectsVal]

/-! ### CJ-B correctness -/

private theorem rejAcc_ne_zero_iff (M : ℕ) :
    ∀ t, rejAcc M t ≠ 0 ↔ ∃ i < t, violatedFn (instB M) (exB M) i ≠ 0 := by
  intro t
  induction t with
  | zero => simp [rejAcc_zero]
  | succ k ih =>
      rw [rejAcc_succ, rejStepFn, bitOr_ne_zero, ih]
      constructor
      · rintro (⟨i, hi, hv⟩ | hv)
        · exact ⟨i, by omega, hv⟩
        · exact ⟨k, by omega, hv⟩
      · rintro ⟨i, hi, hv⟩
        rcases (by omega : i < k ∨ i = k) with h | h
        · exact Or.inl ⟨i, h, hv⟩
        · subst h; exact Or.inr hv

/-- **`rejectsVal` characterisation.** `rejectsVal inst e ≠ 0` iff some feature `i < readK inst` has
a surviving, violated literal. -/
theorem rejectsVal_ne_zero_iff (inst e : ℕ) :
    rejectsVal inst e ≠ 0 ↔ ∃ i < readK inst, violatedFn inst e i ≠ 0 := by
  unfold rejectsVal
  have := rejAcc_ne_zero_iff (Nat.pair inst e) (readK inst)
  simpa only [instB, exB, Nat.unpair_pair] using this

private theorem violatedFn_ne_zero_iff (inst e i : ℕ) :
    violatedFn inst e i ≠ 0 ↔
      (aliveVal0 inst i ≠ 0 ∧ featOf e i ≠ 0) ∨ (aliveVal1 inst i ≠ 0 ∧ featOf e i = 0) := by
  unfold violatedFn
  rw [bitOr_ne_zero, bitAnd_ne_zero, bitAnd_ne_zero, bitNot_ne_zero]

private theorem rejectsVal_le_one (inst e : ℕ) : rejectsVal inst e ≤ 1 := by
  unfold rejectsVal
  generalize readK inst = t
  induction t with
  | zero => rw [rejAcc_zero]; omega
  | succ k ih => rw [rejAcc_succ, rejStepFn]; exact bitOr_le_one _ _

/-! ### CJ-B native cost

Each round invokes CJ-A fresh, so the per-round cost is dominated by `tc cAliveLoop`'s own bound
(`tc_cAliveLoop_raw`), instantiated at the round's feature index. -/

private theorem tc_cReadA0_le (X : ℕ) : tc cReadA0 X ≤ 3 := by
  simp only [cReadA0, tc_comp, tc_left, tc_right]; omega
private theorem tc_cReadA1_le (X : ℕ) : tc cReadA1 X ≤ 3 := by
  simp only [cReadA1, tc_comp, tc_right]; omega

private theorem tc_cAccB_le (a i acc : ℕ) : tc cAccB (Nat.pair a (Nat.pair i acc)) ≤ 3 := by
  simp only [cAccB, tc_comp, tc_right]; omega
private theorem tc_cIB_le (a i acc : ℕ) : tc cIB (Nat.pair a (Nat.pair i acc)) ≤ 5 := by
  simp only [cIB, tc_comp, tc_left, tc_right]; omega
private theorem tc_cSeedB_le (a i acc : ℕ) : tc cSeedB (Nat.pair a (Nat.pair i acc)) ≤ 1 := by
  simp only [cSeedB, tc_left]; omega
private theorem tc_cInstStepB_le (a i acc : ℕ) : tc cInstStepB (Nat.pair a (Nat.pair i acc)) ≤ 5 := by
  have := tc_cSeedB_le a i acc; simp only [cInstStepB, tc_comp, tc_left]; omega
private theorem tc_cExStepB_le (a i acc : ℕ) : tc cExStepB (Nat.pair a (Nat.pair i acc)) ≤ 5 := by
  have := tc_cSeedB_le a i acc; simp only [cExStepB, tc_comp, tc_right]; omega

private theorem tc_cAliveArgB_le (a i acc : ℕ) : tc cAliveArgB (Nat.pair a (Nat.pair i acc)) ≤ 15 := by
  have h1 := tc_cInstStepB_le a i acc
  have h2 := tc_cIB_le a i acc
  simp only [cAliveArgB, tc_pair]
  omega

/-- **`cAlive0B`'s native cost**, dominated by a fresh CJ-A call at the round's feature index. -/
private theorem tc_cAlive0B_le (a i acc : ℕ) (hw : WFBits (instB a)) :
    tc cAlive0B (Nat.pair a (Nat.pair i acc)) ≤ (16 * i + 1501) * readM (instB a) + 600 := by
  have harg := tc_cAliveArgB_le a i acc
  have hloop := tc_cAliveLoop_raw (instB a) i hw
  have hr0 := tc_cReadA0_le (val cAliveLoop (Nat.pair (instB a) i))
  simp only [cAlive0B, tc_comp, val_cAliveArgB]
  omega

private theorem tc_cAlive1B_le (a i acc : ℕ) (hw : WFBits (instB a)) :
    tc cAlive1B (Nat.pair a (Nat.pair i acc)) ≤ (16 * i + 1501) * readM (instB a) + 600 := by
  have harg := tc_cAliveArgB_le a i acc
  have hloop := tc_cAliveLoop_raw (instB a) i hw
  have hr1 := tc_cReadA1_le (val cAliveLoop (Nat.pair (instB a) i))
  simp only [cAlive1B, tc_comp, val_cAliveArgB]
  omega

private theorem val_cAlive0B_le_one (a i acc : ℕ) : val cAlive0B (Nat.pair a (Nat.pair i acc)) ≤ 1 := by
  rw [val_cAlive0B]; exact aliveVal0_le_one _ _
private theorem val_cAlive1B_le_one (a i acc : ℕ) : val cAlive1B (Nat.pair a (Nat.pair i acc)) ≤ 1 := by
  rw [val_cAlive1B]; exact aliveVal1_le_one _ _

private theorem tc_cFvB_le (a i acc : ℕ) : tc cFvB (Nat.pair a (Nat.pair i acc)) ≤ 10 := by
  have := tc_cExStepB_le a i acc; simp only [cFvB, tc_comp, tc_right]; omega

/-- **The feature read: the one value-scaling cost, `O(i)`.** -/
private theorem tc_cFeatB_le (a i acc : ℕ) : tc cFeatB (Nat.pair a (Nat.pair i acc)) ≤ 8 * i + 40 := by
  have hfv := tc_cFvB_le a i acc
  have hia := tc_cIB_le a i acc
  have hpeel := tc_cPeel_le (val cFvB (Nat.pair a (Nat.pair i acc)))
    (val cIB (Nat.pair a (Nat.pair i acc)))
  have hiv := val_cIB a i acc
  simp only [cFeatB, tc_comp, tc_pair, tc_cHeadL, val_pair]
  omega

private theorem tc_cViol0B_le (a i acc : ℕ) (hw : WFBits (instB a)) (hqb : featOf (exB a) i ≤ 1) :
    tc cViol0B (Nat.pair a (Nat.pair i acc)) ≤ (16 * i + 1501) * readM (instB a) + 8 * i + 900 := by
  have h0 := tc_cAlive0B_le a i acc hw
  have hf := tc_cFeatB_le a i acc
  have h0v := val_cAlive0B_le_one a i acc
  have hfv : val cFeatB (Nat.pair a (Nat.pair i acc)) ≤ 1 := by rw [val_cFeatB]; exact hqb
  have hand := tc_cAnd_bit h0v hfv
  simp only [cViol0B, tc_comp, tc_pair, val_pair]
  omega

private theorem tc_cViol1B_le (a i acc : ℕ) (hw : WFBits (instB a)) (hqb : featOf (exB a) i ≤ 1) :
    tc cViol1B (Nat.pair a (Nat.pair i acc)) ≤ (16 * i + 1501) * readM (instB a) + 8 * i + 950 := by
  have h1 := tc_cAlive1B_le a i acc hw
  have hf := tc_cFeatB_le a i acc
  have h1v := val_cAlive1B_le_one a i acc
  have hfv : val cFeatB (Nat.pair a (Nat.pair i acc)) ≤ 1 := by rw [val_cFeatB]; exact hqb
  have hnf := tc_cNot_bit hfv
  have hnfv : val (comp cNot cFeatB) (Nat.pair a (Nat.pair i acc)) ≤ 1 := by
    rw [val_comp, val_cNot']; exact bitNot_le_one _
  have hand := tc_cAnd_bit h1v hnfv
  simp only [cViol1B, tc_comp, tc_pair, val_pair]
  omega

private theorem tc_cViolB_le (a i acc : ℕ) (hw : WFBits (instB a)) (hqb : featOf (exB a) i ≤ 1) :
    tc cViolB (Nat.pair a (Nat.pair i acc))
      ≤ 2 * ((16 * i + 1501) * readM (instB a)) + 16 * i + 1900 := by
  have hv0 := tc_cViol0B_le a i acc hw hqb
  have hv1 := tc_cViol1B_le a i acc hw hqb
  have hv0v : val cViol0B (Nat.pair a (Nat.pair i acc)) ≤ 1 := by
    unfold cViol0B; rw [val_comp, val_pair]; exact val_cAnd_le_one _ _
  have hv1v : val cViol1B (Nat.pair a (Nat.pair i acc)) ≤ 1 := by
    unfold cViol1B; rw [val_comp, val_pair]; exact val_cAnd_le_one _ _
  have hor := tc_cOr_bit hv0v hv1v
  simp only [cViolB, tc_comp, tc_pair, val_pair]
  omega

private theorem inv_rejAcc_le_one (M : ℕ) : ∀ t, rejAcc M t ≤ 1 := by
  intro t
  induction t with
  | zero => rw [rejAcc_zero]; omega
  | succ k ih => rw [rejAcc_succ, rejStepFn]; exact bitOr_le_one _ _

/-- **The per-step cost bound.** Dominated by two fresh CJ-A calls, `O(i)` rounds deep into each. -/
private theorem tc_cRejStep_le (a i acc : ℕ) (hacc : acc ≤ 1) (hw : WFBits (instB a))
    (hqb : featOf (exB a) i ≤ 1) :
    tc cRejStep (Nat.pair a (Nat.pair i acc))
      ≤ 2 * ((16 * i + 1501) * readM (instB a)) + 16 * i + 2000 := by
  have hviol := tc_cViolB_le a i acc hw hqb
  have haccT := tc_cAccB_le a i acc
  have haccv : val cAccB (Nat.pair a (Nat.pair i acc)) ≤ 1 := by rw [val_cAccB]; exact hacc
  have hviolv : val cViolB (Nat.pair a (Nat.pair i acc)) ≤ 1 := by
    unfold cViolB; rw [val_comp, val_pair]; exact val_cOr_le_one _ _
  have hor := tc_cOr_bit haccv hviolv
  simp only [cRejStep, tc_comp, tc_pair, val_pair]
  omega

/-- **`cRejLoop`'s native cost on a well-formed instance**, given the candidate example's feature
vector is bit-valued (`WFBits` covers the example list; the query point, when the caller uses one,
supplies its own bit hypothesis the same way). -/
private theorem tc_cRejLoop_raw (M : ℕ) (hw : WFBits (instB M)) (hqb : ∀ i, featOf (exB M) i ≤ 1) :
    tc cRejLoop M
      ≤ (2 * ((16 * readK (instB M) + 1501) * readM (instB M)) + 16 * readK (instB M) + 2001)
          * readK (instB M) + 500 := by
  have hpair : val (pair cRejId cRejCount) M = Nat.pair M (readK (instB M)) := by
    rw [val_pair, val_cRejId, val_cRejCount]
  have hidcount : tc (pair cRejId cRejCount) M ≤ 20 := by
    simp only [cRejId, cRejCount, cInstOfB, cReadK, tc_pair, tc_comp, tc_left, tc_right]
    omega
  have hstep : ∀ i, i < readK (instB M) →
      tc cRejStep (Nat.pair M (Nat.pair i (val (prec cRejBase cRejStep) (Nat.pair M i))))
        ≤ 2 * ((16 * readK (instB M) + 1501) * readM (instB M)) + 16 * readK (instB M) + 2000 := by
    intro i hi
    have hacc : rejAcc M i ≤ 1 := inv_rejAcc_le_one M i
    have hqbi : featOf (exB M) i ≤ 1 := hqb i
    have hraw := tc_cRejStep_le M i (rejAcc M i) hacc hw hqbi
    have hmono : (16 * i + 1501) * readM (instB M) ≤ (16 * readK (instB M) + 1501) * readM (instB M) :=
      Nat.mul_le_mul_right _ (by omega)
    unfold rejAcc at hraw
    omega
  have hprec := tc_prec_le' (cf := cRejBase) (cg := cRejStep) (a := M)
    (B := 2 * ((16 * readK (instB M) + 1501) * readM (instB M)) + 16 * readK (instB M) + 2000)
    (readK (instB M)) hstep
  have hbase : tc cRejBase M ≤ 1 := by simp [cRejBase]
  have heq : ((2 * ((16 * readK (instB M) + 1501) * readM (instB M)) + 16 * readK (instB M) + 2000)
        + 1) * readK (instB M)
      = (2 * ((16 * readK (instB M) + 1501) * readM (instB M)) + 16 * readK (instB M) + 2001)
          * readK (instB M) := by ring
  simp only [cRejLoop, tc_comp, hpair]
  omega

/-! ## Stage CJ-C — the assembled decider, an `m`-round AND-fold over the examples

`conjDecideVal inst` is `1` iff every example is labelled `1` or rejected by the surviving set —
[SQ] §4's *General form* elimination decider, made computable. The packed input IS `inst` itself
(no extra pairing): the step needs no round-dependent parameter beyond the fixed instance, so — like
CJ-A — it is realised via `Function.iterate` over a carried example suffix. -/

/-- The unscanned example suffix. -/
def exSufC (acc : ℕ) : ℕ := acc.unpair.1
/-- The running verdict bit (AND-accumulated so far). -/
def vC (acc : ℕ) : ℕ := acc.unpair.2

/-- The initial accumulator: the full example list, verdict vacuously `1`. -/
def cjInitAcc (data : ℕ) : ℕ := Nat.pair data 1

/-- The semantic step: the current example is labelled `1` or rejected by the surviving set; AND
that into the running verdict, and peel the suffix one cell. -/
def cjStepFn (inst acc : ℕ) : ℕ :=
  Nat.pair (tailL (exSufC acc))
    (bitAnd (vC acc) (bitOr (lblOf (headL (exSufC acc))) (rejectsVal inst (headL (exSufC acc)))))

/-! ### The `Code` realisation of stage CJ-C -/

/-- The instance `a`, out of the step input `⟨a, ⟨i, acc⟩⟩` (the packed input IS the instance). -/
def cInstC : Code := left
/-- The accumulator, out of the step input. -/
def cAccC : Code := comp right right
/-- The example suffix, from the accumulator. -/
def cExSufC : Code := comp left cAccC
/-- The verdict bit, from the accumulator. -/
def cVC : Code := comp right cAccC
/-- The current example. -/
def cCurExC : Code := comp cHeadL cExSufC
/-- The current example's label. -/
def cCurLblC : Code := comp left cCurExC
/-- `⟨inst, e⟩`, the packed argument for a fresh CJ-B call. -/
def cRejArgC : Code := pair cInstC cCurExC
/-- `rejectsVal inst e`, via a fresh CJ-B call. -/
def cRejC : Code := comp cRejLoop cRejArgC
/-- Is the current example safe (labelled `1`, or rejected by the surviving set)? -/
def cSafeC : Code := comp cOr (pair cCurLblC cRejC)
/-- The updated verdict bit. -/
def cV'C : Code := comp cAnd (pair cVC cSafeC)
/-- The step: peel the suffix, AND the verdict with this round's safety bit. -/
def cjStep : Code := pair (comp cTailL cExSufC) cV'C
/-- Base code: build `cjInitAcc (readData a)` from the seed `a` (`readData a = tailL a`). -/
def cjInit : Code := pair cTailL (constCode 1)

private theorem rfindFree_cjStep : RfindFree cjStep := by
  simp only [cjStep, cV'C, cSafeC, cRejC, cRejArgC, cCurLblC, cCurExC, cExSufC, cVC, cAccC, cInstC,
    cHeadL, cTailL, cAnd, cOr, cNot, cIsPos, cShape0, cSwap, isPosCore, notCore, orCore, cPeel,
    cTailStep, constCode,
    cRejLoop, cRejBase, cRejStep, cRejId, cRejCount, cInstOfB, cReadK, cViolB, cViol0B, cViol1B,
    cAlive0B, cAlive1B, cAliveArgB, cFeatB, cFvB, cExStepB, cInstStepB, cSeedB, cIB, cAccB,
    cReadA0, cReadA1, cAliveLoop, cAliveInit, cAliveStep, cA0'A, cA1'A, cSafe0A, cSafe1A, cCurLblA,
    cCurFeatA, cFvCurA, cCurExA, cExSufA, cA0A, cA1A, cAccA, cJaA, cJA, cAliveId, cAliveCount, cReadM,
    cInstA, cDataA, RfindFree, and_self]

private theorem val_cInstC (a i acc : ℕ) : val cInstC (Nat.pair a (Nat.pair i acc)) = a := by
  simp only [cInstC, val_left, Nat.unpair_pair]
private theorem val_cAccC (a i acc : ℕ) : val cAccC (Nat.pair a (Nat.pair i acc)) = acc := by
  simp only [cAccC, val_comp, val_right, Nat.unpair_pair]
private theorem val_cExSufC (a i acc : ℕ) : val cExSufC (Nat.pair a (Nat.pair i acc)) = exSufC acc := by
  simp only [cExSufC, val_comp, val_left, val_cAccC, exSufC]
private theorem val_cVC (a i acc : ℕ) : val cVC (Nat.pair a (Nat.pair i acc)) = vC acc := by
  simp only [cVC, val_comp, val_right, val_cAccC, vC]
private theorem val_cCurExC (a i acc : ℕ) :
    val cCurExC (Nat.pair a (Nat.pair i acc)) = headL (exSufC acc) := by
  simp only [cCurExC, val_comp, val_cHeadL, val_cExSufC]
private theorem val_cCurLblC (a i acc : ℕ) :
    val cCurLblC (Nat.pair a (Nat.pair i acc)) = lblOf (headL (exSufC acc)) := by
  simp only [cCurLblC, val_comp, val_left, val_cCurExC, lblOf]
private theorem val_cRejArgC (a i acc : ℕ) :
    val cRejArgC (Nat.pair a (Nat.pair i acc)) = Nat.pair a (headL (exSufC acc)) := by
  simp only [cRejArgC, val_pair, val_cInstC, val_cCurExC]
private theorem val_cRejC (a i acc : ℕ) :
    val cRejC (Nat.pair a (Nat.pair i acc)) = rejectsVal a (headL (exSufC acc)) := by
  rw [cRejC, val_comp, val_cRejArgC, val_cRejLoop_rejectsVal]
private theorem val_cjStep (a i acc : ℕ) :
    val cjStep (Nat.pair a (Nat.pair i acc)) = cjStepFn a acc := by
  simp only [cjStep, cV'C, cSafeC, val_pair, val_comp, val_cAnd', val_cOr', val_cTailL, val_cVC,
    val_cCurLblC, val_cRejC, val_cExSufC, cjStepFn]

private theorem val_cjLoop_raw (n t : ℕ) :
    val (prec cjInit cjStep) (Nat.pair n t) = (cjStepFn n)^[t] (cjInitAcc (readData n)) := by
  induction t with
  | zero =>
      rw [val_prec_zero]
      simp only [cjInit, val_pair, val_cTailL, val_constCode, cjInitAcc, tailL, readData,
        Function.iterate_zero_apply]
  | succ k ih => rw [val_prec_succ, val_cjStep, ih, Function.iterate_succ_apply']

/-- The accumulator after the full `m`-round scan. -/
def cjAcc (n : ℕ) : ℕ := (cjStepFn n)^[readM n] (cjInitAcc (readData n))

/-- **`conjDecideVal`**: `1` iff every example is labelled `1` or rejected by the surviving set. -/
def conjDecideVal (inst : ℕ) : ℕ := vC (cjAcc inst)

/-- Round budget: `readM n`. -/
def cjCount : Code := cReadM
/-- Identity shaper: the loop seed is the whole packed input (the instance itself). -/
def cjId : Code := pair left right
/-- The raw scan: outputs the FULL final accumulator `⟨exSuf,verdict⟩`, not yet the bare bit. -/
def cjLoop : Code := comp (prec cjInit cjStep) (pair cjId cjCount)
/-- The verdict field of a BARE accumulator (not a step-input triple). -/
def cReadVC : Code := right
/-- **`cConjSolve`**: the assembled CJ-C decider — `cjLoop`'s output read through `cReadVC`. -/
def cConjSolve : Code := comp cReadVC cjLoop

private theorem rfindFree_cjInit : RfindFree cjInit := ⟨rfindFree_cTailL, rfindFree_constCode 1⟩
private theorem rfindFree_cjId : RfindFree cjId := ⟨trivial, trivial⟩
private theorem rfindFree_cjCount : RfindFree cjCount := rfindFree_cReadM
private theorem rfindFree_cjLoop : RfindFree cjLoop :=
  ⟨⟨rfindFree_cjInit, rfindFree_cjStep⟩, rfindFree_cjId, rfindFree_cjCount⟩
private theorem rfindFree_cReadVC : RfindFree cReadVC := trivial
private theorem rfindFree_cConjSolve : RfindFree cConjSolve := ⟨rfindFree_cReadVC, rfindFree_cjLoop⟩

private theorem val_cjId (n : ℕ) : val cjId n = n := by
  simp only [cjId, val_pair, val_left, val_right, Nat.pair_unpair]
private theorem val_cjCount (n : ℕ) : val cjCount n = readM n := by
  simp only [cjCount, val_cReadM]
private theorem val_cReadVC (acc : ℕ) : val cReadVC acc = vC acc := by simp only [cReadVC, val_right, vC]

private theorem val_cjLoop (n : ℕ) : val cjLoop n = cjAcc n := by
  rw [cjLoop, val_comp, val_pair, val_cjId, val_cjCount, val_cjLoop_raw, cjAcc]

/-- **CJ-C's public value law.** Exposed as a plain equation from the whole `Code` composition down
to `conjDecideVal` — no private internals needed by any consumer (the fix this target exists to
apply from the start, rather than after the fact as in T41). -/
theorem val_cConjSolve (n : ℕ) : val cConjSolve n = conjDecideVal n := by
  rw [cConjSolve, val_comp, val_cjLoop, val_cReadVC, conjDecideVal]

/-! ### CJ-C native cost

Each round invokes CJ-B fresh, so the per-round cost is dominated by `tc cRejLoop`'s own bound
(`tc_cRejLoop_raw`). -/

private theorem inv_exSufC_peel (inst : ℕ) :
    ∀ t, exSufC ((cjStepFn inst)^[t] (cjInitAcc (readData inst))) = peel (readData inst) t := by
  intro t
  induction t with
  | zero => simp [cjInitAcc, exSufC, peel]
  | succ k ih =>
      rw [Function.iterate_succ_apply',
        show exSufC (cjStepFn inst ((cjStepFn inst)^[k] (cjInitAcc (readData inst))))
          = tailL (exSufC ((cjStepFn inst)^[k] (cjInitAcc (readData inst)))) from by
            simp only [cjStepFn, exSufC, Nat.unpair_pair],
        ih]
      simp only [peel, Function.iterate_succ_apply']

private theorem inv_vC_le_one (inst : ℕ) : ∀ t, vC ((cjStepFn inst)^[t] (cjInitAcc (readData inst))) ≤ 1 := by
  intro t
  cases t with
  | zero => simp [cjInitAcc, vC]
  | succ k =>
      rw [Function.iterate_succ_apply']
      simp only [cjStepFn, vC, Nat.unpair_pair]
      exact bitAnd_le_one _ _

/-- **Visited-state bit-ness.** At every visited example `i < readM inst`, the label and every
feature are bits (`WFBits`). -/
private theorem visited_bits_C (inst i : ℕ) (hw : WFBits inst) (hi : i < readM inst) :
    lblOf (headL (exSufC ((cjStepFn inst)^[i] (cjInitAcc (readData inst))))) ≤ 1 ∧
    (∀ j, featOf (headL (exSufC ((cjStepFn inst)^[i] (cjInitAcc (readData inst))))) j ≤ 1) := by
  rw [inv_exSufC_peel]
  obtain ⟨_hwf, exs, hdeq, hdlen, hlbl, hfeat⟩ := hw
  have hie : i < exs.length := by rw [hdlen]; exact hi
  rw [hdeq, getExample_encode exs i hie]
  exact ⟨hlbl _ (List.getElem_mem hie), fun j => hfeat _ (List.getElem_mem hie) j⟩

private theorem tc_cInstC_le (a i acc : ℕ) : tc cInstC (Nat.pair a (Nat.pair i acc)) ≤ 3 := by
  simp only [cInstC, tc_left]; omega
private theorem tc_cAccC_le (a i acc : ℕ) : tc cAccC (Nat.pair a (Nat.pair i acc)) ≤ 3 := by
  simp only [cAccC, tc_comp, tc_right]; omega
private theorem tc_cExSufC_le (a i acc : ℕ) : tc cExSufC (Nat.pair a (Nat.pair i acc)) ≤ 5 := by
  have := tc_cAccC_le a i acc; simp only [cExSufC, tc_comp, tc_left]; omega
private theorem tc_cVC_le (a i acc : ℕ) : tc cVC (Nat.pair a (Nat.pair i acc)) ≤ 5 := by
  have := tc_cAccC_le a i acc; simp only [cVC, tc_comp, tc_right]; omega
private theorem tc_cCurExC_le (a i acc : ℕ) : tc cCurExC (Nat.pair a (Nat.pair i acc)) ≤ 10 := by
  have := tc_cExSufC_le a i acc; simp only [cCurExC, tc_comp, tc_cHeadL]; omega
private theorem tc_cCurLblC_le (a i acc : ℕ) : tc cCurLblC (Nat.pair a (Nat.pair i acc)) ≤ 15 := by
  have := tc_cCurExC_le a i acc; simp only [cCurLblC, tc_comp, tc_left]; omega

private theorem tc_cRejArgC_le (a i acc : ℕ) : tc cRejArgC (Nat.pair a (Nat.pair i acc)) ≤ 15 := by
  have h1 := tc_cInstC_le a i acc
  have h2 := tc_cCurExC_le a i acc
  simp only [cRejArgC, tc_pair]
  omega

/-- **`cRejC`'s native cost**, dominated by a fresh CJ-B call over the whole instance `a`. -/
private theorem tc_cRejC_le (a i acc : ℕ) (hw : WFBits a)
    (hqb : ∀ j, featOf (headL (exSufC acc)) j ≤ 1) :
    tc cRejC (Nat.pair a (Nat.pair i acc))
      ≤ (2 * ((16 * readK a + 1501) * readM a) + 16 * readK a + 2001) * readK a + 700 := by
  have harg := tc_cRejArgC_le a i acc
  have hib : instB (Nat.pair a (headL (exSufC acc))) = a := by simp [instB, Nat.unpair_pair]
  have heb : exB (Nat.pair a (headL (exSufC acc))) = headL (exSufC acc) := by
    simp [exB, Nat.unpair_pair]
  have hw' : WFBits (instB (Nat.pair a (headL (exSufC acc)))) := by rw [hib]; exact hw
  have hqb' : ∀ j, featOf (exB (Nat.pair a (headL (exSufC acc)))) j ≤ 1 := by rw [heb]; exact hqb
  have hloop := tc_cRejLoop_raw (Nat.pair a (headL (exSufC acc))) hw' hqb'
  rw [hib] at hloop
  simp only [cRejC, tc_comp, val_cRejArgC]
  omega

private theorem tc_cSafeC_le (a i acc : ℕ) (hw : WFBits a) (hqbl : lblOf (headL (exSufC acc)) ≤ 1)
    (hqb : ∀ j, featOf (headL (exSufC acc)) j ≤ 1) :
    tc cSafeC (Nat.pair a (Nat.pair i acc))
      ≤ (2 * ((16 * readK a + 1501) * readM a) + 16 * readK a + 2001) * readK a + 800 := by
  have hl := tc_cCurLblC_le a i acc
  have hr := tc_cRejC_le a i acc hw hqb
  have hlv : val cCurLblC (Nat.pair a (Nat.pair i acc)) ≤ 1 := by rw [val_cCurLblC]; exact hqbl
  have hrv : val cRejC (Nat.pair a (Nat.pair i acc)) ≤ 1 := by
    rw [val_cRejC]; exact rejectsVal_le_one _ _
  have hor := tc_cOr_bit hlv hrv
  simp only [cSafeC, tc_comp, tc_pair, val_pair]
  omega

private theorem tc_cV'C_le (a i acc : ℕ) (hv : vC acc ≤ 1) (hw : WFBits a)
    (hqbl : lblOf (headL (exSufC acc)) ≤ 1) (hqb : ∀ j, featOf (headL (exSufC acc)) j ≤ 1) :
    tc cV'C (Nat.pair a (Nat.pair i acc))
      ≤ (2 * ((16 * readK a + 1501) * readM a) + 16 * readK a + 2001) * readK a + 1100 := by
  have hvt := tc_cVC_le a i acc
  have hst := tc_cSafeC_le a i acc hw hqbl hqb
  have hvv : val cVC (Nat.pair a (Nat.pair i acc)) ≤ 1 := by rw [val_cVC]; exact hv
  have hsv : val cSafeC (Nat.pair a (Nat.pair i acc)) ≤ 1 := by
    unfold cSafeC; rw [val_comp, val_pair]; exact val_cOr_le_one _ _
  have hand := tc_cAnd_bit hvv hsv
  simp only [cV'C, tc_comp, tc_pair, val_pair]
  omega

/-- **The per-step cost bound.** Dominated by a fresh CJ-B call. -/
private theorem tc_cjStep_le (a i acc : ℕ) (hv : vC acc ≤ 1) (hw : WFBits a)
    (hqbl : lblOf (headL (exSufC acc)) ≤ 1) (hqb : ∀ j, featOf (headL (exSufC acc)) j ≤ 1) :
    tc cjStep (Nat.pair a (Nat.pair i acc))
      ≤ (2 * ((16 * readK a + 1501) * readM a) + 16 * readK a + 2001) * readK a + 1200 := by
  have hv' := tc_cV'C_le a i acc hv hw hqbl hqb
  have hex := tc_cExSufC_le a i acc
  simp only [cjStep, tc_pair, tc_comp, tc_cTailL]
  omega

/-- **`cConjSolve`'s native cost on a well-formed instance** — an EXPLICIT polynomial in the example
count `m = readM inst` and the feature count `k = readK inst` (unsimplified: a fresh CJ-B call,
itself dominated by two fresh CJ-A calls, run once per example, giving the poly(m,k) analogue of
`OneDL.tc_cSolve_raw`). -/
theorem tc_cConjSolve_raw (inst : ℕ) (hw : WFBits inst) :
    tc cConjSolve inst
      ≤ (((2 * ((16 * readK inst + 1501) * readM inst) + 16 * readK inst + 2001) * readK inst
            + 1200) + 1) * readM inst + 520 := by
  have hpair : val (pair cjId cjCount) inst = Nat.pair inst (readM inst) := by
    rw [val_pair, val_cjId, val_cjCount]
  have hidcount : tc (pair cjId cjCount) inst ≤ 20 := by
    simp only [cjId, cjCount, cReadM, tc_pair, tc_comp, tc_left, tc_right]
    omega
  have hstep : ∀ i, i < readM inst →
      tc cjStep (Nat.pair inst (Nat.pair i (val (prec cjInit cjStep) (Nat.pair inst i))))
        ≤ (2 * ((16 * readK inst + 1501) * readM inst) + 16 * readK inst + 2001) * readK inst
            + 1200 := by
    intro i hi
    rw [show val (prec cjInit cjStep) (Nat.pair inst i)
      = (cjStepFn inst)^[i] (cjInitAcc (readData inst)) from val_cjLoop_raw inst i]
    have hv := inv_vC_le_one inst i
    obtain ⟨hqbl, hqb⟩ := visited_bits_C inst i hw hi
    exact tc_cjStep_le inst i _ hv hw hqbl hqb
  have hprec := tc_prec_le' (cf := cjInit) (cg := cjStep) (a := inst)
    (B := (2 * ((16 * readK inst + 1501) * readM inst) + 16 * readK inst + 2001) * readK inst
        + 1200)
    (readM inst) hstep
  have hinit : tc cjInit inst ≤ 20 := by
    have h1 := tc_cTailL inst
    have h2 := tc_constCode_le 1 inst
    simp only [cjInit, tc_pair]
    omega
  simp only [cConjSolve, cReadVC, tc_comp, tc_right, cjLoop, hpair]
  omega

/-- Poly-time on a domain — the honest "poly cost + output size on well-formed inputs" notion,
mirroring `OneDL.PolyBoundedOn`/`OneDL.PolyTimeOn` exactly. Kept as a local copy rather than
imported: importing it would mean importing the whole 1-DL greedy solver for two generic
definitions that are not themselves about decision lists (see the module docstring). -/
def PolyBoundedOn (D : ℕ → Prop) (t : ℕ → ℕ) : Prop :=
  ∃ C k : ℕ, ∀ n, D n → t n ≤ C * (Nat.size n + 1) ^ k + C

/-- `f` is computed on `D` by an `rfind`-free code whose step count AND output size are both
`PolyBoundedOn D`. -/
def PolyTimeOn (D : ℕ → Prop) (f : ℕ → ℕ) : Prop :=
  ∃ c : Code, RfindFree c ∧ (∀ n, D n → val c n = f n) ∧
    PolyBoundedOn D (tc c) ∧ PolyBoundedOn D (fun n => Nat.size (f n))

/-- The well-formed domain for `cConjSolve`: a bit-well-formed instance. -/
def ConjWF (inst : ℕ) : Prop := WFBits inst

private theorem polyBoundedOn_tc_cConjSolve : PolyBoundedOn ConjWF (tc cConjSolve) := by
  refine ⟨10000, 4, fun n hn => ?_⟩
  have hwf : WF n := hn.1
  have hk : readK n ≤ Nat.size n := readK_le_size n hwf
  have hm : readM n ≤ Nat.size n := readM_le_size n hwf
  have hraw := tc_cConjSolve_raw n hn
  set S := Nat.size n with hSdef
  have hA : 16 * readK n + 1501 ≤ 1517 * (S + 1) := by nlinarith
  have hB : (16 * readK n + 1501) * readM n ≤ 1517 * (S + 1) * (S + 1) := by
    have h1 : (16 * readK n + 1501) * readM n ≤ (1517 * (S + 1)) * readM n :=
      Nat.mul_le_mul_right _ hA
    have h2 : (1517 * (S + 1)) * readM n ≤ (1517 * (S + 1)) * (S + 1) :=
      Nat.mul_le_mul_left _ (by omega)
    omega
  have hC : 2 * ((16 * readK n + 1501) * readM n) + 16 * readK n + 2001 ≤ 5100 * (S + 1) ^ 2 := by
    nlinarith [hB]
  have hD : (2 * ((16 * readK n + 1501) * readM n) + 16 * readK n + 2001) * readK n
      ≤ 5100 * (S + 1) ^ 2 * (S + 1) := by
    have h1 : (2 * ((16 * readK n + 1501) * readM n) + 16 * readK n + 2001) * readK n
        ≤ (5100 * (S + 1) ^ 2) * readK n := Nat.mul_le_mul_right _ hC
    have h2 : (5100 * (S + 1) ^ 2) * readK n ≤ (5100 * (S + 1) ^ 2) * (S + 1) :=
      Nat.mul_le_mul_left _ (by omega)
    omega
  have hE : ((2 * ((16 * readK n + 1501) * readM n) + 16 * readK n + 2001) * readK n + 1200) + 1
      ≤ 6000 * (S + 1) ^ 3 := by nlinarith [hD]
  have hF : (((2 * ((16 * readK n + 1501) * readM n) + 16 * readK n + 2001) * readK n + 1200) + 1)
        * readM n
      ≤ 6000 * (S + 1) ^ 3 * (S + 1) := by
    have h1 : (((2 * ((16 * readK n + 1501) * readM n) + 16 * readK n + 2001) * readK n + 1200) + 1)
          * readM n
        ≤ (6000 * (S + 1) ^ 3) * readM n := Nat.mul_le_mul_right _ hE
    have h2 : (6000 * (S + 1) ^ 3) * readM n ≤ (6000 * (S + 1) ^ 3) * (S + 1) :=
      Nat.mul_le_mul_left _ (by omega)
    omega
  have hpow : (S + 1) ^ 3 * (S + 1) = (S + 1) ^ 4 := by ring
  nlinarith [hraw, hF, hpow]

/-! ### CJ-C correctness — the `List`-model fold characterisation -/

/-- **The AND-fold realises the list.** Running the semantic step over the encoded example list for
`exs.length` iterations from seed `v` empties the suffix and AND-folds "labelled `1`, or rejected"
into `v`. -/
private theorem cjStepFn_iterate (inst : ℕ) (exs : List ℕ) (v : ℕ) :
    (cjStepFn inst)^[exs.length] (Nat.pair (encodeList exs) v)
      = Nat.pair 0 (exs.foldl (fun z e => bitAnd z (bitOr (lblOf e) (rejectsVal inst e))) v) := by
  induction exs generalizing v with
  | nil => simp [encodeList]
  | cons e es ih =>
      rw [List.length_cons, Function.iterate_succ_apply]
      have hx : cjStepFn inst (Nat.pair (encodeList (e :: es)) v)
          = Nat.pair (encodeList es) (bitAnd v (bitOr (lblOf e) (rejectsVal inst e))) := by
        simp only [cjStepFn, exSufC, vC, Nat.unpair_pair, headL_encode_cons, tailL_encode_cons]
      rw [hx, ih]
      simp only [List.foldl_cons]

/-- **`conjDecideVal` characterisation.** The verdict is nonzero iff every example is labelled `1`
or rejected by the surviving set. -/
theorem conjDecideVal_ne_zero_iff (inst : ℕ) (exs : List ℕ)
    (hdeq : readData inst = encodeList exs) (hdlen : exs.length = readM inst) :
    conjDecideVal inst ≠ 0 ↔ ∀ e ∈ exs, lblOf e ≠ 0 ∨ rejectsVal inst e ≠ 0 := by
  have hval : conjDecideVal inst
      = exs.foldl (fun z e => bitAnd z (bitOr (lblOf e) (rejectsVal inst e))) 1 := by
    unfold conjDecideVal cjAcc
    simp only [cjInitAcc]
    rw [hdeq, ← hdlen, cjStepFn_iterate]
    simp only [vC, Nat.unpair_pair]
  rw [hval, andFold_ne_zero_iff]
  simp only [ne_eq, one_ne_zero, not_false_eq_true, true_and, bitOr_ne_zero]

theorem conjDecideVal_le_one (inst : ℕ) : conjDecideVal inst ≤ 1 := by
  unfold conjDecideVal cjAcc
  generalize readM inst = t
  generalize readData inst = data
  induction t generalizing data with
  | zero => simp [cjInitAcc, vC, Nat.unpair_pair]
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      simp only [cjStepFn, vC, Nat.unpair_pair]
      exact bitAnd_le_one _ _

/-- **`polyTime_conjSolve`.** The elimination decider is poly-time on the honest well-formed
domain: `cConjSolve` computes it (`val_cConjSolve`), its native cost is `PolyBoundedOn`
(`tc_cConjSolve_raw`, bundled into a single power of `Nat.size`), and its output is a bit, hence
trivially poly-bit. -/
theorem polyTime_conjSolve : PolyTimeOn ConjWF conjDecideVal := by
  refine ⟨cConjSolve, rfindFree_cConjSolve, fun n _ => val_cConjSolve n,
    polyBoundedOn_tc_cConjSolve, ?_⟩
  refine ⟨2, 0, fun n _ => ?_⟩
  change Nat.size (conjDecideVal n) ≤ 2 * (Nat.size n + 1) ^ 0 + 2
  have h1 : conjDecideVal n ≤ 1 := conjDecideVal_le_one n
  have hle : Nat.size (conjDecideVal n) ≤ 1 :=
    le_trans (Nat.size_le_size h1) (le_of_eq Nat.size_one)
  omega

/-! ## The main theorem — `conj_decides`

The witnessed literal set for the `⇐` direction: every surviving literal, over both polarities. A
`Prop`-level construction used only for the existence proof — the decider itself never builds it. -/

/-- The surviving literals over feature `j`: `⟨j,0⟩` if it survives, `⟨j,1⟩` if it survives, neither,
either, or both. -/
private def survivorsAt (inst j : ℕ) : List ℕ :=
  (if aliveVal0 inst j ≠ 0 then [Nat.pair j 0] else []) ++
    (if aliveVal1 inst j ≠ 0 then [Nat.pair j 1] else [])

/-- **All** surviving literals, over every feature `j < readK inst`. -/
private def survivors (inst : ℕ) : List ℕ := (List.range (readK inst)).flatMap (survivorsAt inst)

private theorem mem_survivorsAt_iff (inst j r : ℕ) :
    r ∈ survivorsAt inst j ↔
      (r = Nat.pair j 0 ∧ aliveVal0 inst j ≠ 0) ∨ (r = Nat.pair j 1 ∧ aliveVal1 inst j ≠ 0) := by
  unfold survivorsAt
  constructor
  · intro hr
    rw [List.mem_append] at hr
    rcases hr with hr | hr
    · by_cases h0 : aliveVal0 inst j ≠ 0
      · rw [if_pos h0, List.mem_singleton] at hr; exact Or.inl ⟨hr, h0⟩
      · rw [if_neg h0] at hr; simp at hr
    · by_cases h1 : aliveVal1 inst j ≠ 0
      · rw [if_pos h1, List.mem_singleton] at hr; exact Or.inr ⟨hr, h1⟩
      · rw [if_neg h1] at hr; simp at hr
  · rintro (⟨rfl, h0⟩ | ⟨rfl, h1⟩)
    · rw [List.mem_append, if_pos h0]; left; exact List.mem_singleton.mpr rfl
    · rw [List.mem_append, if_pos h1]; right; exact List.mem_singleton.mpr rfl

private theorem mem_survivors_iff (inst r : ℕ) :
    r ∈ survivors inst ↔
      (aliveVal0 inst (litJ r) ≠ 0 ∧ litP r = 0 ∧ litJ r < readK inst) ∨
        (aliveVal1 inst (litJ r) ≠ 0 ∧ litP r = 1 ∧ litJ r < readK inst) := by
  unfold survivors
  rw [List.mem_flatMap]
  constructor
  · rintro ⟨j, hj, hmem⟩
    rw [List.mem_range] at hj
    rw [mem_survivorsAt_iff] at hmem
    rcases hmem with ⟨rfl, ha⟩ | ⟨rfl, ha⟩
    · exact Or.inl ⟨by rwa [litJ_pair], by rw [litP_pair], by rwa [litJ_pair]⟩
    · exact Or.inr ⟨by rwa [litJ_pair], by rw [litP_pair], by rwa [litJ_pair]⟩
  · intro h
    refine ⟨litJ r, ?_, ?_⟩
    · rw [List.mem_range]
      rcases h with ⟨_, _, hj⟩ | ⟨_, _, hj⟩ <;> exact hj
    · rw [mem_survivorsAt_iff]
      rcases h with ⟨ha, hp, _⟩ | ⟨ha, hp, _⟩
      · left
        have heq : Nat.pair (litJ r) (litP r) = r := Nat.pair_unpair r
        rw [hp] at heq
        exact ⟨heq.symm, ha⟩
      · right
        have heq : Nat.pair (litJ r) (litP r) = r := Nat.pair_unpair r
        rw [hp] at heq
        exact ⟨heq.symm, ha⟩

private theorem survivors_litJ_lt (inst r : ℕ) (hr : r ∈ survivors inst) : litJ r < readK inst := by
  rcases (mem_survivors_iff inst r).mp hr with ⟨_, _, h⟩ | ⟨_, _, h⟩ <;> exact h

/-- **`conj_decides`.** The elimination decider's verdict holds iff a consistent conjunction over
valid feature literals exists — [SQ] §4's *General form* elimination algorithm, machine-checked.
The mathematical content: `survivors inst` is the most specific conjunction consistent with the
labelled-`1` examples (`aliveVal0_iff`/`aliveVal1_iff`), every consistent member's literals are a
subset of it (via the same characterisation, run in reverse), and it is therefore itself consistent
exactly when it rejects every labelled-`0` example — which `conjDecideVal` checks directly. -/
theorem conj_decides (inst : ℕ) (exs : List ℕ)
    (hdeq : readData inst = encodeList exs) (hdlen : exs.length = readM inst)
    (hlbl : ∀ e ∈ exs, lblOf e ≤ 1) :
    conjDecideVal inst ≠ 0 ↔ ExistsConsistentConj inst exs := by
  rw [conjDecideVal_ne_zero_iff inst exs hdeq hdlen]
  constructor
  · intro hall
    refine ⟨survivors inst, survivors_litJ_lt inst, fun e he => ?_⟩
    have hb := hlbl e he
    rcases (by omega : lblOf e = 0 ∨ lblOf e = 1) with hl | hl
    · -- negative example: some surviving literal is violated
      rw [hl, evalConj_eq_zero_iff]
      rcases hall e he with hc | hc
      · exact absurd hl hc
      · obtain ⟨i, hik, hviol⟩ := (rejectsVal_ne_zero_iff inst e).mp hc
        rcases (violatedFn_ne_zero_iff inst e i).mp hviol with ⟨ha0, hf⟩ | ⟨ha1, hf⟩
        · refine ⟨Nat.pair i 0, (mem_survivors_iff inst _).mpr (Or.inl ?_), ?_⟩
          · rw [litJ_pair, litP_pair]; exact ⟨ha0, rfl, hik⟩
          · rw [litJ_pair, litP_pair]
            intro hcontra
            exact hf (hcontra.mpr rfl)
        · refine ⟨Nat.pair i 1, (mem_survivors_iff inst _).mpr (Or.inr ?_), ?_⟩
          · rw [litJ_pair, litP_pair]; exact ⟨ha1, rfl, hik⟩
          · rw [litJ_pair, litP_pair]
            intro hcontra
            exact absurd (hcontra.mp hf) (by omega)
    · -- positive example: every surviving literal is satisfied
      rw [hl, evalConj_eq_one_iff]
      intro r hr
      rcases (mem_survivors_iff inst r).mp hr with ⟨ha0, hp, _⟩ | ⟨ha1, hp, _⟩
      · rw [hp]
        have hcond := (aliveVal0_iff inst (litJ r) exs hdeq hdlen).mp ha0 e he
        rcases hcond with hl0 | hf0
        · exact absurd hl0 (by omega)
        · exact ⟨fun _ => rfl, fun _ => hf0⟩
      · rw [hp]
        have hcond := (aliveVal1_iff inst (litJ r) exs hdeq hdlen).mp ha1 e he
        rcases hcond with hl0 | hf0
        · exact absurd hl0 (by omega)
        · exact ⟨fun hc => absurd hc hf0, fun hc => absurd hc (by omega)⟩
  · rintro ⟨lits, hval, hcons⟩ e he
    by_cases hl : lblOf e = 0
    · right
      have hev : evalConj lits e = 0 := by rw [hcons e he, hl]
      obtain ⟨r, hr, hne⟩ := (evalConj_eq_zero_iff lits e).mp hev
      have hj : litJ r < readK inst := hval r hr
      rw [rejectsVal_ne_zero_iff]
      refine ⟨litJ r, hj, ?_⟩
      rw [violatedFn_ne_zero_iff]
      by_cases hp : litP r = 0
      · have halive : aliveVal0 inst (litJ r) ≠ 0 := by
          rw [aliveVal0_iff inst (litJ r) exs hdeq hdlen]
          intro e' he'
          by_cases hl' : lblOf e' = 0
          · exact Or.inl hl'
          · right
            have hb' := hlbl e' he'
            have hl1 : lblOf e' = 1 := by omega
            have hev' : evalConj lits e' = 1 := by rw [hcons e' he', hl1]
            have hcondr := (evalConj_eq_one_iff lits e').mp hev' r hr
            rw [hp] at hcondr
            exact hcondr.mpr rfl
        left
        refine ⟨halive, ?_⟩
        rw [hp] at hne
        intro hcontra
        exact hne ⟨fun _ => rfl, fun _ => hcontra⟩
      · have halive : aliveVal1 inst (litJ r) ≠ 0 := by
          rw [aliveVal1_iff inst (litJ r) exs hdeq hdlen]
          intro e' he'
          by_cases hl' : lblOf e' = 0
          · exact Or.inl hl'
          · right
            have hb' := hlbl e' he'
            have hl1 : lblOf e' = 1 := by omega
            have hev' : evalConj lits e' = 1 := by rw [hcons e' he', hl1]
            have hcondr := (evalConj_eq_one_iff lits e').mp hev' r hr
            intro hcontra
            exact hp (hcondr.mp hcontra)
        right
        refine ⟨halive, ?_⟩
        by_contra hcontra
        exact hne ⟨fun hc => absurd hc hcontra, fun hc => absurd hc hp⟩
    · left; omega

/-! ## Axiom-cleanliness guards (CI-enforced)

Each guard **fails `lake build`** if the theorem's axiom set ever drifts from the standard
`[propext, Classical.choice, Quot.sound]`. -/

/-- info: 'Conj.conj_decides' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms conj_decides

/-- info: 'Conj.tc_cConjSolve_raw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms tc_cConjSolve_raw

/-- info: 'Conj.polyTime_conjSolve' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms polyTime_conjSolve

end Conj
