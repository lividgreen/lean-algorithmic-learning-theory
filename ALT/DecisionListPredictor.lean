/-
Copyright (c) 2026 Mykola Palamarchuk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mykola Palamarchuk
-/
import ALT.DecisionListSolver

-- Formal-check file, not Mathlib-destined: opt out of the house-style linters.
set_option linter.style.header false
set_option linter.style.longLine false

/-!
# The version-space (forced-symbol) predictor for 1-decision lists

Provenance: [SQ] §4, Corollary 4.3(b). The consistency decider `OneDL.cSolve`
(`ALT/DecisionListSolver.lean`) decides 1-DL consistency; this module reads its decision off as a
computed value (Stage A), extends an instance by one candidate example (Stage B), and composes two
such decisions into the two-consistency-call forced-symbol predictor the corollary's read-off
describes (Stage C): append each candidate next-symbol as a constraint, and the symbol whose
appended constraint leaves every consistent 1-DL in agreement is the prediction.

**Stage A** turns `OneDL.solve_decides`'s Prop-valued decision into a computed bit (`cDecide`,
`decideVal`, `decide_iff`). **Stage B** extends a solver instance by one candidate example
(`mkEx`, `extInst`, `extPacked`) and proves the one genuinely new combinatorial fact the
two-call read-off rests on: a decision list whose value at a point is not itself a bit can always
be relabeled, at that one point, to any bit, without disturbing its consistency with the existing
examples (`exists_relabel`). **Stage C** assembles the two extended decisions into the
forced-symbol verdict (`forcedVal`) and proves it classifies the version space exhaustively —
empty, forced at a bit, or split (`forced_iff`, `empty_iff`, `split_iff`) — with an explicit
native-cost bound (`tc_forced_raw`) and a `PolyTimeOn` closure (`polyTime_forced`).
-/

namespace OneDL

open Nat.Partrec (Code)
open Nat.Partrec.Code
open TimeCost

/-! ## Stage A — the consistency decider as a computed bit

`cAllZero` scans the first `m` cells of a mask and reports whether every one of them is zero — the
`Code` form of `OneDL.solve_decides`'s `∀ i, i < m → headL (peel M i) = 0` hypothesis. Composed with
`cSolve`'s mask output, it reads the greedy solver's Prop-valued verdict off as a bit (`cDecide`).
-/

/-! ### The emptiness scan `cAllZero`

Accumulator `⟨maskSuf, flag⟩`: `maskSuf` starts at the mask and is peeled one cell per round; `flag`
starts at `1` and is `AND`-folded with the negation of each visited head bit, so it survives as `1`
iff every visited cell was `0`. The scan needs no `WFBits`/`MaskValid` hypothesis for its cost bound —
`bAnd`/`bNot` normalize to a bit for ANY input, magnitude-independent. -/

/-- Mask suffix field of the emptiness-scan accumulator. -/
private def azMs (acc : ℕ) : ℕ := acc.unpair.1
/-- Flag field of the emptiness-scan accumulator. -/
private def azFlag (acc : ℕ) : ℕ := acc.unpair.2

/-- The semantic step: peel the mask suffix one cell, and `AND` the flag with the negation of the
visited head bit. -/
private def azStepFn (acc : ℕ) : ℕ :=
  Nat.pair (tailL (azMs acc)) (bAnd (azFlag acc) (bNot (headL (azMs acc))))

/-- The initial accumulator: the full mask suffix, flag `1` (vacuously "all zero so far"). -/
private def azInitAcc (mask : ℕ) : ℕ := Nat.pair mask 1

/-- `headL` as a `Code` (mirrors `OneDL.DecisionListSolver`'s private `cHead`). -/
private def cHd : Code := comp left right
/-- `tailL` as a `Code` (mirrors `OneDL.DecisionListSolver`'s private `cTail`). -/
private def cTl : Code := comp right right

private theorem val_cHd (L : ℕ) : val cHd L = headL L := by
  simp only [cHd, val_comp, val_left, val_right, headL]
private theorem val_cTl (L : ℕ) : val cTl L = tailL L := by
  simp only [cTl, val_comp, val_right, tailL]
private theorem tc_cHd (L : ℕ) : tc cHd L = 3 := by simp only [cHd, tc_comp, tc_left, tc_right]
private theorem tc_cTl (L : ℕ) : tc cTl L = 3 := by simp only [cTl, tc_comp, tc_right]

/-- The whole loop parameter, unchanged through every round (unused by the step itself). -/
private def cIdN : Code := pair left right
/-- The accumulator, out of the step input `⟨a, ⟨i, acc⟩⟩`. -/
private def cAzAcc : Code := comp right right
/-- The mask-suffix field of the accumulator. -/
private def cAzMs : Code := comp left cAzAcc
/-- The flag field of the accumulator. -/
private def cAzFlag : Code := comp right cAzAcc
/-- The visited head bit. -/
private def cAzHead : Code := comp cHd cAzMs
/-- The peeled mask suffix. -/
private def cAzTail : Code := comp cTl cAzMs
/-- The updated flag: `AND` with the negated head bit. -/
private def cAzFlag' : Code := comp cAnd (pair cAzFlag (comp cNot cAzHead))
/-- The scan's step code. -/
private def cAzStep : Code := pair cAzTail cAzFlag'
/-- The scan's base code: from `mask`, build `azInitAcc mask`. -/
private def cAzInit : Code := pair right (constCode 1)
/-- The round budget: the first component `m` of the packed input `⟨m, mask⟩`. -/
private def cCountM : Code := left
/-- The raw scan loop, over the packed input `N = ⟨m, mask⟩`. -/
private def cAzLoop : Code := comp (prec cAzInit cAzStep) (pair cIdN cCountM)
/-- **The emptiness-scan primitive.** Reads out the flag: `1` iff every one of the first `m` mask
cells is `0`. -/
def cAllZero : Code := comp right cAzLoop

private theorem rfindFree_cAzStep : RfindFree cAzStep := by
  simp only [cAzStep, cAzFlag', cAzHead, cAzTail, cAzMs, cAzFlag, cAzAcc, cHd, cTl, cAnd, cOr, cNot,
    cIsPos, cShape0, cSwap, isPosCore, notCore, orCore, constCode, RfindFree, and_self]
private theorem rfindFree_cAzInit : RfindFree cAzInit := ⟨trivial, rfindFree_constCode 1⟩
private theorem rfindFree_cIdN : RfindFree cIdN := ⟨trivial, trivial⟩
private theorem rfindFree_cCountM : RfindFree cCountM := trivial
private theorem rfindFree_cAzLoop : RfindFree cAzLoop :=
  ⟨⟨rfindFree_cAzInit, rfindFree_cAzStep⟩, rfindFree_cIdN, rfindFree_cCountM⟩

private theorem val_cAnd' (a b : ℕ) : val cAnd (Nat.pair a b) = bAnd a b := val_cAnd a b
private theorem val_cNot' (n : ℕ) : val cNot n = bNot n := val_cNot n

private theorem val_cAzStep (a i acc : ℕ) :
    val cAzStep (Nat.pair a (Nat.pair i acc)) = azStepFn acc := by
  simp only [cAzStep, cAzFlag', cAzHead, cAzTail, cAzMs, cAzFlag, cAzAcc, val_pair, val_comp,
    val_left, val_right, val_cHd, val_cTl, val_cAnd', val_cNot', Nat.unpair_pair, azStepFn, azMs,
    azFlag]

private theorem val_cAzInit (N : ℕ) : val cAzInit N = azInitAcc N.unpair.2 := by
  simp only [cAzInit, val_pair, val_right, val_constCode, azInitAcc]

private theorem val_cAzLoop_raw (N t : ℕ) :
    val (prec cAzInit cAzStep) (Nat.pair N t) = azStepFn^[t] (azInitAcc N.unpair.2) := by
  induction t with
  | zero => rw [val_prec_zero, val_cAzInit, Function.iterate_zero_apply]
  | succ k ih => rw [val_prec_succ, val_cAzStep, ih, Function.iterate_succ_apply']

private theorem val_cAzLoop (N : ℕ) :
    val cAzLoop N = azStepFn^[N.unpair.1] (azInitAcc N.unpair.2) := by
  have hpair : val (pair cIdN cCountM) N = Nat.pair N N.unpair.1 := by
    simp only [cIdN, cCountM, val_pair, val_left, val_right, Nat.pair_unpair]
  rw [cAzLoop, val_comp, hpair, val_cAzLoop_raw]

private theorem val_cAllZero (N : ℕ) : val cAllZero N = azFlag (azStepFn^[N.unpair.1] (azInitAcc N.unpair.2)) := by
  rw [cAllZero, val_comp, val_cAzLoop]; rfl

/-- `allZeroVal N` on the packed input `N = ⟨m, mask⟩`: `1` iff every one of the first `m` mask cells
is `0`, `0` otherwise. -/
def allZeroVal (N : ℕ) : ℕ := val cAllZero N

/-! ### `allZero_iff` — the scan's correctness against the `List` model -/

private theorem bAnd_le_one (a b : ℕ) : bAnd a b ≤ 1 := by unfold bAnd; split_ifs <;> simp
private theorem bNot_le_one (n : ℕ) : bNot n ≤ 1 := by unfold bNot; split <;> simp
private theorem bOr_le_one (a b : ℕ) : bOr a b ≤ 1 := by unfold bOr; split_ifs <;> simp
private theorem bAnd_ne_zero (a b : ℕ) : bAnd a b ≠ 0 ↔ a ≠ 0 ∧ b ≠ 0 := by
  unfold bAnd; by_cases ha : a = 0 <;> by_cases hb : b = 0 <;> simp [ha, hb]
private theorem bNot_ne_zero (n : ℕ) : bNot n ≠ 0 ↔ n = 0 := by
  unfold bNot; by_cases h : n = 0 <;> simp [h]

/-- **The scan realizes the fold.** Running the semantic step over an encoded list for `bs.length`
iterations from seed `z` empties the suffix and `AND`-negation-folds `bs` into `z`. -/
private theorem azStepFn_iterate (z : ℕ) : ∀ bs : List ℕ,
    azStepFn^[bs.length] (Nat.pair (encodeList bs) z)
      = Nat.pair 0 (bs.foldl (fun y b => bAnd y (bNot b)) z) := by
  intro bs
  induction bs generalizing z with
  | nil => simp [encodeList]
  | cons b bs ih =>
      rw [List.length_cons, Function.iterate_succ_apply]
      have hx : azStepFn (Nat.pair (encodeList (b :: bs)) z)
          = Nat.pair (encodeList bs) (bAnd z (bNot b)) := by
        simp only [azStepFn, azMs, azFlag, Nat.unpair_pair, headL_encode_cons, tailL_encode_cons]
      rw [hx, ih, List.foldl_cons]

/-- The `AND`-negation fold is nonzero iff the seed is, and every element of the list is `0`. -/
private theorem azFold_ne_zero_iff (z : ℕ) : ∀ bs : List ℕ,
    (bs.foldl (fun y b => bAnd y (bNot b)) z) ≠ 0 ↔ z ≠ 0 ∧ ∀ b ∈ bs, b = 0 := by
  intro bs
  induction bs generalizing z with
  | nil => simp
  | cons b bs ih =>
      rw [List.foldl_cons, ih, bAnd_ne_zero, bNot_ne_zero]
      constructor
      · rintro ⟨⟨hz, hb⟩, hbs⟩; exact ⟨hz, fun b' hb' => by
          rcases List.mem_cons.mp hb' with rfl | hin
          · exact hb
          · exact hbs b' hin⟩
      · rintro ⟨hz, hall⟩
        exact ⟨⟨hz, hall b (List.mem_cons_self ..)⟩,
          fun b' hb' => hall b' (List.mem_cons_of_mem _ hb')⟩

private theorem forall_getElem_iff_forall_mem (bs : List ℕ) (P : ℕ → Prop) :
    (∀ i, (h : i < bs.length) → P bs[i]) ↔ ∀ b ∈ bs, P b := by
  constructor
  · intro h b hb
    obtain ⟨i, hi, hget⟩ := List.mem_iff_getElem.mp hb
    exact hget ▸ h i hi
  · intro h i hi
    exact h bs[i] (List.getElem_mem hi)

/-- **The emptiness scan is correct.** Under `MaskValid`, `allZeroVal ⟨m, mask⟩ ≠ 0` iff every one of
the first `m` mask cells is `0` — the `Code` form of the hypothesis `OneDL.solve_decides` concludes. -/
theorem allZero_iff (m mask : ℕ) (h : MaskValid mask m) :
    allZeroVal (Nat.pair m mask) ≠ 0 ↔ ∀ i, i < m → headL (peel mask i) = 0 := by
  obtain ⟨msks, hmeq, hmlen, _hmbit⟩ := h
  have hval : allZeroVal (Nat.pair m mask) = msks.foldl (fun y b => bAnd y (bNot b)) 1 := by
    unfold allZeroVal
    rw [val_cAllZero, Nat.unpair_pair, azInitAcc, hmeq, ← hmlen, azStepFn_iterate]
    simp only [azFlag, Nat.unpair_pair]
  rw [hval, azFold_ne_zero_iff]
  simp only [ne_eq, one_ne_zero, not_false_eq_true, true_and]
  rw [← forall_getElem_iff_forall_mem]
  constructor
  · intro h i hi
    have him : i < msks.length := by rw [hmlen]; exact hi
    rw [hmeq, getExample_encode msks i him]
    exact h i him
  · intro h i him
    have hi : i < m := by rw [← hmlen]; exact him
    have := h i hi
    rwa [hmeq, getExample_encode msks i him] at this

/-! ### The scan's native cost — magnitude-independent given `MaskValid` -/

private theorem flag_le_one (acc : ℕ) : azFlag (azStepFn acc) ≤ 1 := by
  simp only [azStepFn, azFlag, Nat.unpair_pair]; exact bAnd_le_one _ _

private theorem azFlag_le_one (mask : ℕ) : ∀ i, azFlag (azStepFn^[i] (azInitAcc mask)) ≤ 1 := by
  intro i
  cases i with
  | zero =>
      have : azFlag (azStepFn^[0] (azInitAcc mask)) = 1 := by
        simp only [Function.iterate_zero_apply, azInitAcc, azFlag, Nat.unpair_pair]
      omega
  | succ k => rw [Function.iterate_succ_apply']; exact flag_le_one _

private theorem inv_azMs_peel (mask : ℕ) :
    ∀ i, azMs (azStepFn^[i] (azInitAcc mask)) = peel mask i := by
  intro i
  induction i with
  | zero => simp only [Function.iterate_zero_apply, azInitAcc, azMs, Nat.unpair_pair, peel,
      Function.iterate_zero_apply]
  | succ k ih =>
      rw [Function.iterate_succ_apply', show azMs (azStepFn (azStepFn^[k] (azInitAcc mask)))
        = tailL (azMs (azStepFn^[k] (azInitAcc mask))) from by
          simp only [azStepFn, azMs, Nat.unpair_pair], ih]
      simp only [peel, Function.iterate_succ_apply']

private theorem azHead_visited_le_one (mask m : ℕ) (h : MaskValid mask m) (i : ℕ) (hi : i < m) :
    headL (azMs (azStepFn^[i] (azInitAcc mask))) ≤ 1 := by
  rw [inv_azMs_peel]
  obtain ⟨msks, hmeq, hmlen, hmbit⟩ := h
  have him : i < msks.length := by rw [hmlen]; exact hi
  rw [hmeq, getExample_encode msks i him]
  exact hmbit _ (List.getElem_mem him)

private theorem tc_cAzStep_le (a i acc : ℕ) (hmask : headL (azMs acc) ≤ 1) (hflag : azFlag acc ≤ 1) :
    tc cAzStep (Nat.pair a (Nat.pair i acc)) ≤ 300 := by
  have hAccT : tc cAzAcc (Nat.pair a (Nat.pair i acc)) ≤ 3 := by
    simp only [cAzAcc, tc_comp, tc_right]; omega
  have hMsT : tc cAzMs (Nat.pair a (Nat.pair i acc)) ≤ 5 := by
    have := hAccT; simp only [cAzMs, tc_comp, tc_left]; omega
  have hFlagT : tc cAzFlag (Nat.pair a (Nat.pair i acc)) ≤ 5 := by
    have := hAccT; simp only [cAzFlag, tc_comp, tc_right]; omega
  have hMsV : val cAzMs (Nat.pair a (Nat.pair i acc)) = azMs acc := by
    simp only [cAzMs, cAzAcc, val_comp, val_left, val_right, Nat.unpair_pair, azMs]
  have hFlagV : val cAzFlag (Nat.pair a (Nat.pair i acc)) = azFlag acc := by
    simp only [cAzFlag, cAzAcc, val_comp, val_right, Nat.unpair_pair, azFlag]
  have hTailT : tc cAzTail (Nat.pair a (Nat.pair i acc)) ≤ 9 := by
    have := hMsT; simp only [cAzTail, tc_comp, tc_cTl]; omega
  have hHeadT : tc cAzHead (Nat.pair a (Nat.pair i acc)) ≤ 9 := by
    have := hMsT; simp only [cAzHead, tc_comp, tc_cHd]; omega
  have hHeadV : val cAzHead (Nat.pair a (Nat.pair i acc)) = headL (azMs acc) := by
    simp only [cAzHead, val_comp, val_cHd, hMsV]
  have hNotHeadT : tc (comp cNot cAzHead) (Nat.pair a (Nat.pair i acc)) ≤ 22 := by
    have hnot := tc_cNot_bit (x := val cAzHead (Nat.pair a (Nat.pair i acc))) (by rw [hHeadV]; exact hmask)
    simp only [tc_comp]; omega
  have hNotHeadV : val (comp cNot cAzHead) (Nat.pair a (Nat.pair i acc)) = bNot (headL (azMs acc)) := by
    simp only [val_comp, val_cNot', hHeadV]
  have hPairT : tc (pair cAzFlag (comp cNot cAzHead)) (Nat.pair a (Nat.pair i acc)) ≤ 28 := by
    have := hFlagT; have := hNotHeadT; simp only [tc_pair]; omega
  have hAndT : tc cAnd (val (pair cAzFlag (comp cNot cAzHead)) (Nat.pair a (Nat.pair i acc))) ≤ 204 := by
    rw [val_pair, hFlagV, hNotHeadV]
    exact tc_cAnd_bit hflag (bNot_le_one _)
  have hFlag'T : tc cAzFlag' (Nat.pair a (Nat.pair i acc)) ≤ 233 := by
    have := hPairT; have := hAndT; simp only [cAzFlag', tc_comp]; omega
  simp only [cAzStep, tc_pair]; omega

private theorem hAzStep_visited (N : ℕ) (h : MaskValid N.unpair.2 N.unpair.1) :
    ∀ i, i < N.unpair.1 →
      tc cAzStep (Nat.pair N (Nat.pair i (val (prec cAzInit cAzStep) (Nat.pair N i)))) ≤ 300 := by
  intro i hi
  rw [val_cAzLoop_raw]
  exact tc_cAzStep_le N i _ (azHead_visited_le_one N.unpair.2 N.unpair.1 h i hi) (azFlag_le_one N.unpair.2 i)

private theorem tc_cAzInit_le (N : ℕ) : tc cAzInit N ≤ 5 := by
  have := tc_constCode_le 1 N
  simp only [cAzInit, tc_pair, tc_right]; omega

/-- **The scan's native cost.** Given `MaskValid mask m`, `tc cAllZero ⟨m, mask⟩ ≤ 301·m + 20`. -/
private theorem tc_cAllZero_le (N : ℕ) (h : MaskValid N.unpair.2 N.unpair.1) :
    tc cAllZero N ≤ 301 * N.unpair.1 + 20 := by
  have hpair : val (pair cIdN cCountM) N = Nat.pair N N.unpair.1 := by
    simp only [cIdN, cCountM, val_pair, val_left, val_right, Nat.pair_unpair]
  have hprec : tc (prec cAzInit cAzStep) (Nat.pair N N.unpair.1)
      ≤ tc cAzInit N + (300 + 1) * N.unpair.1 + 1 :=
    tc_prec_le' N.unpair.1 (hAzStep_visited N h)
  have hinit := tc_cAzInit_le N
  have hidc : tc (pair cIdN cCountM) N ≤ 5 := by
    simp only [cIdN, cCountM, tc_pair, tc_left, tc_right]; omega
  have hloop : tc cAzLoop N ≤ tc cAzInit N + 301 * N.unpair.1 + 1 + 5 + 1 := by
    rw [cAzLoop, tc_comp, hpair]; omega
  have hright := tc_right (val cAzLoop N)
  simp only [cAllZero, tc_comp]; omega

/-! ## `cDecide` — `cSolve` composed with the emptiness scan -/

set_option maxHeartbeats 0 in
-- `Code` equality against a fully spelled-out term is deep, plain-delta defeq checking with no
-- propositional content, so it is slow rather than large — it terminates, just past the default cap.
/-- **`cSolve`'s structure, spelled out.** The only route from the public `cSolve`/`solveVal` to the
public `svMask`/`svAcc` layer `OneDL.solve_decides` is stated over: `cAssemble`, `cSvLoop`, `cId` and
`cSvCount` are private to `ALT/DecisionListSolver.lean`, so their wiring is re-derived here instead of
named. -/
private theorem hcode_cSolve : cSolve =
    comp (pair left (comp cReverse (pair (comp right right) (comp left right))))
      (comp (prec cSvInit cSvStep) (pair (pair left right) (comp cReadM left))) := rfl

set_option maxHeartbeats 0 in
-- same slow-not-stuck deep defeq as `hcode_cSolve` above (the closing `rfl` matches `svAcc`/`svMask`
-- against their own unfolding, propositionally trivial but syntactically deep).
/-- **The bridge.** `solve`'s output mask is `svMask (svAcc n (readM (svInst n)))` — the same quantity
`OneDL.solve_decides` and `OneDL.output_consistent` speak of. -/
private theorem solveVal_fst_eq (n : ℕ) :
    (solveVal n).unpair.1 = svMask (svAcc n (readM (svInst n))) := by
  unfold solveVal
  rw [hcode_cSolve, val_comp, val_pair, val_left, Nat.unpair_pair, val_comp, val_pair, val_pair,
    val_left, val_right, Nat.pair_unpair, val_comp, val_left, val_cReadM]
  rfl

/-- **`cDecide`**: `cSolve`'s output mask (the emptiness scan's mask input) fed to `cAllZero`, at the
scan length `readM (svInst n)`. -/
def cDecide : Code := comp cAllZero (pair (comp cReadM left) (comp left cSolve))

/-- `decideVal n`: nonzero iff `solve`'s output mask is empty on its first `readM (svInst n)` cells —
`solve_decides`'s decision, read off as a computed bit. -/
def decideVal (n : ℕ) : ℕ := val cDecide n

private theorem val_cDecide (n : ℕ) :
    decideVal n = allZeroVal (Nat.pair (readM (svInst n)) (solveVal n).unpair.1) := by
  unfold decideVal cDecide allZeroVal
  rw [val_comp, val_pair, val_comp, val_cReadM, val_left, val_comp, val_left]
  rfl

/-- **The decision matches `solve_decides`.** Under the same hypothesis block `OneDL.solve_decides`
carries, `decideVal n` is nonzero iff a consistent `1`-decision list over valid feature literals
exists — [SQ] §4's cited decider, made computable. -/
theorem decide_iff (n : ℕ) (hn : SolveWF n) (hk : 0 < readK (svInst n))
    (hone : svMask0 n = encodeList (List.replicate (readM (svInst n)) 1))
    (exs : List ℕ) (hdeq : readData (svInst n) = encodeList exs)
    (hdlen : exs.length = readM (svInst n)) :
    decideVal n ≠ 0 ↔ ExistsConsistentDL (svInst n) exs := by
  rw [val_cDecide, allZero_iff _ _ (maskValid_solve n hn), solveVal_fst_eq]
  exact solve_decides n hn hk hone exs hdeq hdlen

/-! ### `cDecide`'s native cost -/

private theorem tc_cReadM_le (n : ℕ) : tc cReadM n ≤ 3 := by
  simp only [cReadM, tc_comp, tc_left, tc_right]; omega

/-- **`cDecide`'s native cost.** `tc cDecide n ≤ tc cSolve n + 301·readM (svInst n) + 37`, given
`SolveWF n` (needed for the scan's `MaskValid` bound). -/
private theorem tc_cDecide_le (n : ℕ) (hn : SolveWF n) :
    tc cDecide n ≤ tc cSolve n + 301 * readM (svInst n) + 37 := by
  have hpairval : val (pair (comp cReadM left) (comp left cSolve)) n
      = Nat.pair (readM (svInst n)) (solveVal n).unpair.1 := by
    simp only [val_pair, val_comp, val_cReadM, val_left, svInst, solveVal]
  have hscan : tc cAllZero (val (pair (comp cReadM left) (comp left cSolve)) n)
      ≤ 301 * readM (svInst n) + 20 := by
    rw [hpairval]
    have := tc_cAllZero_le (Nat.pair (readM (svInst n)) (solveVal n).unpair.1)
      (by simpa using maskValid_solve n hn)
    simpa using this
  have hrm : tc (comp cReadM left) n ≤ 5 := by
    have := tc_cReadM_le n.unpair.1
    simp only [tc_comp, tc_left, val_left]; omega
  have hsv : tc (comp left cSolve) n ≤ tc cSolve n + 2 := by
    simp only [tc_comp, tc_left]; omega
  have hpair : tc (pair (comp cReadM left) (comp left cSolve)) n ≤ tc cSolve n + 8 := by
    simp only [tc_pair]; omega
  simp only [cDecide, tc_comp]; omega

/-! ## Stage B — extending an instance by one candidate example

`mkEx b fv` packs a candidate example at feature vector `fv` with label `b`; `extInst`/`extPacked`
prepend it onto a solver instance's example list and mask (a flag-cons cell, `O(1)` — prepend, not
append, since `Consistent` quantifies over membership and example order is immaterial). -/

/-- An example with label `b` and feature vector `fv`. -/
def mkEx (b fv : ℕ) : ℕ := Nat.pair b fv

/-- The instance extended by one candidate example `e`, prepended. -/
def extInst (inst e : ℕ) : ℕ :=
  Nat.pair (readK inst) (Nat.pair (readM inst + 1) (Nat.pair 1 (Nat.pair e (readData inst))))

/-- The packed solver input extended by one candidate example, mask bit prepended active. -/
def extPacked (n e : ℕ) : ℕ := Nat.pair (extInst (svInst n) e) (Nat.pair 1 (Nat.pair 1 (svMask0 n)))

private theorem lblOf_mkEx (b fv : ℕ) : lblOf (mkEx b fv) = b := by simp [mkEx, lblOf, Nat.unpair_pair]
private theorem fvOf_mkEx (b fv : ℕ) : fvOf (mkEx b fv) = fv := by simp [mkEx, fvOf, Nat.unpair_pair]

private theorem readK_extInst (inst e : ℕ) : readK (extInst inst e) = readK inst := by
  simp [extInst, readK, Nat.unpair_pair]
private theorem readM_extInst (inst e : ℕ) : readM (extInst inst e) = readM inst + 1 := by
  simp [extInst, readM, Nat.unpair_pair]
private theorem readData_extInst (inst e : ℕ) :
    readData (extInst inst e) = Nat.pair 1 (Nat.pair e (readData inst)) := by
  simp [extInst, readData, Nat.unpair_pair]
private theorem firstExample_extInst (inst e : ℕ) : firstExample (extInst inst e) = e := by
  simp [firstExample, readData_extInst, Nat.unpair_pair]
private theorem firstFV_extInst (inst e : ℕ) : firstFV (extInst inst e) = fvOf e := by
  simp [firstFV, firstExample_extInst, fvOf]

private theorem svInst_extPacked (n e : ℕ) : svInst (extPacked n e) = extInst (svInst n) e := by
  simp [extPacked, svInst, Nat.unpair_pair]
private theorem svMask0_extPacked (n e : ℕ) :
    svMask0 (extPacked n e) = Nat.pair 1 (Nat.pair 1 (svMask0 n)) := by
  simp [extPacked, svMask0, Nat.unpair_pair]

/-! ### Well-formedness is preserved by extension -/

private theorem pair_inj' {a b c d : ℕ} (h : Nat.pair a b = Nat.pair c d) : a = c ∧ b = d := by
  have h' := congrArg Nat.unpair h
  rwa [Nat.unpair_pair, Nat.unpair_pair, Prod.mk.injEq] at h'

private theorem pair_mono' {a a' b b' : ℕ} (ha : a ≤ a') (hb : b ≤ b') :
    Nat.pair a b ≤ Nat.pair a' b' := by
  rcases eq_or_lt_of_le ha with rfl | ha'
  · rcases eq_or_lt_of_le hb with rfl | hb'
    · exact le_refl _
    · exact (Nat.pair_lt_pair_right a hb').le
  · rcases eq_or_lt_of_le hb with rfl | hb'
    · exact (Nat.pair_lt_pair_left b ha').le
    · exact le_trans (Nat.pair_lt_pair_left b ha').le (Nat.pair_lt_pair_right a' hb').le

private theorem encodeList_inj : ∀ a b : List ℕ, encodeList a = encodeList b → a = b := by
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
      obtain ⟨_, h2⟩ := pair_inj' hb
      obtain ⟨hxy, htl⟩ := pair_inj' h2
      rw [hxy, ih ys htl]

/-- `WFBits`'s own binary-regime witness list agrees with any other `encodeList`-matching list. -/
private theorem wfbits_exs_bits (n : ℕ) (hw : WFBits (svInst n)) (exs : List ℕ)
    (hdeq : readData (svInst n) = encodeList exs) (hdlen : exs.length = readM (svInst n)) :
    (∀ e ∈ exs, lblOf e ≤ 1) ∧ ∀ e ∈ exs, ∀ j, featOf e j ≤ 1 := by
  obtain ⟨_, exsW, hdeqW, _, hlblW, hfeatW⟩ := hw
  have heq : exsW = exs := encodeList_inj _ _ (by rw [← hdeqW, ← hdeq])
  subst heq
  exact ⟨hlblW, hfeatW⟩

private theorem wfbits_extPacked (n x b : ℕ) (hn : SolveWF n) (hb : b ≤ 1)
    (hqx : IsList x (readK (svInst n))) (hqbits : ∀ j, headL (peel x j) ≤ 1)
    (exs : List ℕ) (hdeq : readData (svInst n) = encodeList exs)
    (hdlen : exs.length = readM (svInst n)) :
    WFBits (svInst (extPacked n (mkEx b x))) := by
  obtain ⟨hwB, _⟩ := hn
  have hMlist := hwB.1.2.1
  rw [svInst_extPacked]
  obtain ⟨hlbl, hfeat⟩ := wfbits_exs_bits n hwB exs hdeq hdlen
  refine ⟨⟨?_, ?_, ?_⟩, mkEx b x :: exs, ?_, ?_, ?_, ?_⟩
  · rw [readM_extInst]; omega
  · rw [readData_extInst, hdeq, readM_extInst]
    exact IsList.cons (mkEx b x) (encodeList exs) (readM (svInst n)) (hdeq ▸ hMlist)
  · rw [firstFV_extInst, fvOf_mkEx, readK_extInst]; exact hqx
  · rw [readData_extInst, hdeq]; rfl
  · rw [readM_extInst]; simp [hdlen]
  · intro e he
    rcases List.mem_cons.mp he with rfl | hin
    · rw [lblOf_mkEx]; exact hb
    · exact hlbl e hin
  · intro e he j
    rcases List.mem_cons.mp he with rfl | hin
    · show featOf (mkEx b x) j ≤ 1
      unfold featOf
      rw [fvOf_mkEx]
      exact hqbits j
    · exact hfeat e hin j

private theorem maskValid_extPacked (n x b : ℕ) (hn : SolveWF n) :
    MaskValid (svMask0 (extPacked n (mkEx b x))) (readM (svInst (extPacked n (mkEx b x)))) := by
  obtain ⟨msks0, hmeq, hmlen, hmbit⟩ := hn.2
  rw [svMask0_extPacked, svInst_extPacked, readM_extInst, hmeq]
  refine ⟨1 :: msks0, ?_, ?_, ?_⟩
  · rfl
  · simp [hmlen]
  · intro c hc
    rcases List.mem_cons.mp hc with rfl | hin
    · exact le_refl 1
    · exact hmbit c hin

private theorem allOnes_extPacked (n x b : ℕ)
    (hone : svMask0 n = encodeList (List.replicate (readM (svInst n)) 1)) :
    svMask0 (extPacked n (mkEx b x))
      = encodeList (List.replicate (readM (svInst (extPacked n (mkEx b x)))) 1) := by
  rw [svMask0_extPacked, svInst_extPacked, readM_extInst, List.replicate_succ, hone]
  rfl

private theorem readK_svInst_extPacked (n x b : ℕ) :
    readK (svInst (extPacked n (mkEx b x))) = readK (svInst n) := by
  rw [svInst_extPacked, readK_extInst]

private theorem readM_svInst_extPacked (n x b : ℕ) :
    readM (svInst (extPacked n (mkEx b x))) = readM (svInst n) + 1 := by
  rw [svInst_extPacked, readM_extInst]

private theorem readData_svInst_extPacked (n x b : ℕ) (exs : List ℕ)
    (hdeq : readData (svInst n) = encodeList exs) :
    readData (svInst (extPacked n (mkEx b x))) = encodeList (mkEx b x :: exs) := by
  rw [svInst_extPacked, readData_extInst, hdeq]; rfl

/-- **The full well-formedness bundle a candidate extension needs.** -/
private theorem solveWF_extPacked (n x b : ℕ) (hn : SolveWF n) (hb : b ≤ 1)
    (hqx : IsList x (readK (svInst n))) (hqbits : ∀ j, headL (peel x j) ≤ 1)
    (exs : List ℕ) (hdeq : readData (svInst n) = encodeList exs)
    (hdlen : exs.length = readM (svInst n)) :
    SolveWF (extPacked n (mkEx b x)) :=
  ⟨wfbits_extPacked n x b hn hb hqx hqbits exs hdeq hdlen, maskValid_extPacked n x b hn⟩

/-! ### `exists_relabel` — the round's one genuinely new lemma -/

private theorem evalDLn_append (D E : List ℕ) (d e : ℕ) :
    evalDLn (D ++ E) d e = evalDLn D (evalDLn E d e) e := by
  induction D with
  | nil => rfl
  | cons r rs ih => simp only [List.cons_append, evalDLn, ih]

private theorem evalDLn_not_fires (D : List ℕ) (d e : ℕ)
    (h : ∀ r ∈ D, bEq (featOf e (ruleJ r)) (ruleP r) = 0) : evalDLn D d e = d := by
  induction D with
  | nil => rfl
  | cons r rs ih =>
      rw [evalDLn, if_pos (h r (List.mem_cons_self ..))]
      exact ih (fun r' hr' => h r' (List.mem_cons_of_mem _ hr'))

private def firesN' (D : List ℕ) (e : ℕ) : Prop := ∃ r ∈ D, bEq (featOf e (ruleJ r)) (ruleP r) ≠ 0

private theorem evalDLn_fires_const (D : List ℕ) (d1 d2 e : ℕ) (h : firesN' D e) :
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

private theorem exists_first_split {α} (P : α → Prop) :
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

/-- **Relabeling.** A decision list valid on `exs` whose value at `x` is not itself a bit can be
relabeled — at the point of first divergence on `x` — to predict any target bit `b` there, without
disturbing its consistency with `exs`: the failing rule's own label is never what any example of
`exs` falls through to (its label would then be a non-bit), so only its label needs to change. -/
theorem exists_relabel (K x : ℕ) (exs : List ℕ) (hlbl : ∀ e ∈ exs, lblOf e ≤ 1)
    (rules : List ℕ) (d : ℕ) (hval : ∀ r ∈ rules, ruleJ r < K)
    (hcons : Consistent rules d exs)
    (hbad : evalDLn rules d x ≠ 0 ∧ evalDLn rules d x ≠ 1) (b : ℕ) :
    ∃ rules' d', (∀ r ∈ rules', ruleJ r < K) ∧ evalDLn rules' d' x = b ∧
      Consistent rules' d' exs := by
  by_cases hcase : ∃ r ∈ rules, bEq (featOf x (ruleJ r)) (ruleP r) ≠ 0
  · -- some rule fires on `x`: take the FIRST such rule `r0` and relabel only it
    obtain ⟨pre, r0, suf, hsplit, hPr0, hprefirst⟩ :=
      exists_first_split (fun r => bEq (featOf x (ruleJ r)) (ruleP r) ≠ 0) rules hcase
    have hprefirst' : ∀ r ∈ pre, bEq (featOf x (ruleJ r)) (ruleP r) = 0 :=
      fun r hr => not_not.mp (hprefirst r hr)
    have hr0mem : r0 ∈ rules := by
      rw [hsplit]; exact List.mem_append_right _ (List.mem_cons_self ..)
    have hval0 : ruleJ r0 < K := hval r0 hr0mem
    have hval_x : evalDLn rules d x = ruleL r0 := by
      rw [hsplit, evalDLn_append, evalDLn_not_fires pre _ x hprefirst', evalDLn, if_neg hPr0]
    have hL01 : ruleL r0 ≠ 0 ∧ ruleL r0 ≠ 1 := by rw [← hval_x]; exact hbad
    set r0' : ℕ := Nat.pair (ruleJ r0) (Nat.pair (ruleP r0) b) with hr0'def
    have hJr0' : ruleJ r0' = ruleJ r0 := by simp [hr0'def, ruleJ, Nat.unpair_pair]
    have hPr0' : ruleP r0' = ruleP r0 := by simp [hr0'def, ruleP, Nat.unpair_pair]
    have hLr0' : ruleL r0' = b := by simp [hr0'def, ruleL, Nat.unpair_pair]
    refine ⟨pre ++ r0' :: suf, d, ?_, ?_, ?_⟩
    · intro r hr
      rcases List.mem_append.mp hr with hrpre | hrsuf
      · exact hval r (by rw [hsplit]; exact List.mem_append_left _ hrpre)
      · rcases List.mem_cons.mp hrsuf with rfl | hrs
        · rw [hJr0']; exact hval0
        · exact hval r (by
            rw [hsplit]; exact List.mem_append_right _ (List.mem_cons_of_mem _ hrs))
    · rw [evalDLn_append, evalDLn_not_fires pre _ x hprefirst']
      rw [evalDLn, hJr0', hPr0', if_neg hPr0, hLr0']
    · intro e he
      rw [evalDLn_append]
      by_cases hpre_fire : firesN' pre e
      · have heq1 : evalDLn pre (evalDLn (r0 :: suf) d e) e = evalDLn pre d e :=
          evalDLn_fires_const pre _ d e hpre_fire
        have heq2 : evalDLn pre (evalDLn (r0' :: suf) d e) e = evalDLn pre d e :=
          evalDLn_fires_const pre _ d e hpre_fire
        rw [heq2]
        have horig : evalDLn rules d e = lblOf e := hcons e he
        rw [hsplit, evalDLn_append, heq1] at horig
        exact horig
      · unfold firesN' at hpre_fire
        push Not at hpre_fire
        rw [evalDLn_not_fires pre _ e hpre_fire]
        have horig : evalDLn rules d e = lblOf e := hcons e he
        rw [hsplit, evalDLn_append, evalDLn_not_fires pre _ e hpre_fire] at horig
        by_cases hr0fire : bEq (featOf e (ruleJ r0)) (ruleP r0) ≠ 0
        · exfalso
          rw [evalDLn, if_neg hr0fire] at horig
          have hle1 : ruleL r0 ≤ 1 := by rw [horig]; exact hlbl e he
          omega
        · push Not at hr0fire
          rw [evalDLn, if_pos hr0fire] at horig
          change evalDLn (r0' :: suf) d e = lblOf e
          rw [evalDLn, hJr0', hPr0', if_pos hr0fire]
          exact horig
  · -- no rule fires on `x`: every example of `exs` must already be decided by a firing rule
    push Not at hcase
    have hevx : evalDLn rules d x = d := evalDLn_not_fires rules d x hcase
    have hdbad : d ≠ 0 ∧ d ≠ 1 := hevx ▸ hbad
    have hallfire : ∀ e ∈ exs, firesN' rules e := by
      intro e he
      by_contra hnf
      unfold firesN' at hnf
      push Not at hnf
      have h1 : evalDLn rules d e = d := evalDLn_not_fires rules d e hnf
      have h2 : evalDLn rules d e = lblOf e := hcons e he
      have h3 : d ≤ 1 := by rw [← h1, h2]; exact hlbl e he
      omega
    refine ⟨rules, b, hval, evalDLn_not_fires rules b x hcase, ?_⟩
    intro e he
    rw [evalDLn_fires_const rules b d e (hallfire e he)]
    exact hcons e he

/-! ## Stage C — the forced-symbol verdict

Two `decideVal` calls at the query point wrapped with each candidate bit — [SQ] §4's read-off: "append
each candidate next-symbol as a constraint; the symbol whose appended constraint leaves every
consistent `1`-DL in agreement is the prediction." -/

/-! ### `cForced`'s wiring — the two extended-instance codes, computed once each -/

/-- The whole packed input `⟨n, x⟩`, first component. -/
private def cN : Code := left
/-- The whole packed input `⟨n, x⟩`, second component (the query point). -/
private def cX : Code := right
/-- `svInst n`, from `⟨n, x⟩`. -/
private def cSvInstP : Code := comp left cN
/-- `svMask0 n`, from `⟨n, x⟩`. -/
private def cSvMask0P : Code := comp right cN
/-- `readK (svInst n)`, from `⟨n, x⟩`. -/
private def cReadKP : Code := comp cReadK cSvInstP
/-- `readM (svInst n)`, from `⟨n, x⟩`. -/
private def cReadMP : Code := comp cReadM cSvInstP
/-- `readData` as a `Code` (mirrors `OneDL.DecisionListSolver`'s private `cData`-style reads). -/
private def cReadDataC : Code := comp right right
/-- `readData (svInst n)`, from `⟨n, x⟩`. -/
private def cReadDataP : Code := comp cReadDataC cSvInstP

/-- `mkEx b x`, from `⟨n, x⟩`, for a literal bit `b`. -/
private def cMkExB (b : ℕ) : Code := pair (constCode b) cX
/-- `extInst (svInst n) (mkEx b x)`, from `⟨n, x⟩`. -/
private def cExtInstB (b : ℕ) : Code :=
  pair cReadKP (pair (comp succ cReadMP) (pair (constCode 1) (pair (cMkExB b) cReadDataP)))
/-- `extPacked n (mkEx b x)`, from `⟨n, x⟩`. -/
private def cExtPackedB (b : ℕ) : Code :=
  pair (cExtInstB b) (pair (constCode 1) (pair (constCode 1) cSvMask0P))

private theorem val_cReadDataC (inst : ℕ) : val cReadDataC inst = readData inst := by
  simp [cReadDataC, val_comp, val_right, readData]

private theorem val_cExtPackedB (b n x : ℕ) :
    val (cExtPackedB b) (Nat.pair n x) = extPacked n (mkEx b x) := by
  simp only [cExtPackedB, cExtInstB, cMkExB, cReadKP, cReadMP, cReadDataP, cSvInstP, cSvMask0P,
    cN, cX, val_pair, val_comp, val_left, val_right, val_succ, val_constCode, val_cReadK,
    val_cReadM, val_cReadDataC, Nat.unpair_pair, extPacked, extInst, mkEx, svInst, svMask0]

/-- Both extended decisions, computed once each. -/
private def cD01 : Code := pair (comp cDecide (cExtPackedB 0)) (comp cDecide (cExtPackedB 1))

private theorem val_cD01 (n x : ℕ) :
    val cD01 (Nat.pair n x)
      = Nat.pair (decideVal (extPacked n (mkEx 0 x))) (decideVal (extPacked n (mkEx 1 x))) := by
  simp only [cD01, val_pair, val_comp, val_cExtPackedB]
  rfl

/-! ### The forced-symbol read-off — pure `O(1)` bit logic on the two decisions -/

private def cD0core : Code := left
private def cD1core : Code := right
/-- `d0 XOR d1`: exactly one of the two extended decisions succeeded. -/
private def cFlagCore : Code :=
  comp cOr (pair (comp cAnd (pair cD0core (comp cNot cD1core)))
                 (comp cAnd (pair cD1core (comp cNot cD0core))))
/-- The forced label, valid only when `cFlagCore ≠ 0`: `d1` itself (`d1 = 0` reads bit `0`, `d1 = 1`
reads bit `1`), masked to `0` when the calls are not forced. -/
private def cLabelCore : Code := comp cAnd (pair cFlagCore cD1core)
private def cForcedCore : Code := pair cFlagCore cLabelCore

/-- **`cForced`**: the two-consistency-call forced-symbol predictor, on the packed input `⟨n, x⟩`. -/
def cForced : Code := comp cForcedCore cD01

/-- `forcedVal n x`: `⟨1, b⟩` when exactly one of the two extended decisions succeeds (`b` its
label), `⟨0, 0⟩` otherwise (empty or split). -/
def forcedVal (n x : ℕ) : ℕ := val cForced (Nat.pair n x)

private theorem val_cAnd'' (a b : ℕ) : val cAnd (Nat.pair a b) = bAnd a b := val_cAnd a b
private theorem val_cOr'' (a b : ℕ) : val cOr (Nat.pair a b) = bOr a b := val_cOr a b
private theorem val_cNot'' (n : ℕ) : val cNot n = bNot n := val_cNot n

private theorem val_cForcedCore (d0 d1 : ℕ) :
    val cForcedCore (Nat.pair d0 d1)
      = Nat.pair (bOr (bAnd d0 (bNot d1)) (bAnd d1 (bNot d0)))
          (bAnd (bOr (bAnd d0 (bNot d1)) (bAnd d1 (bNot d0))) d1) := by
  simp only [cForcedCore, cFlagCore, cLabelCore, cD0core, cD1core, val_pair, val_comp,
    val_left, val_right, val_cAnd'', val_cOr'', val_cNot'', Nat.unpair_pair]

/-- The two extended decisions, named for readability. -/
private def d0V (n x : ℕ) : ℕ := decideVal (extPacked n (mkEx 0 x))
private def d1V (n x : ℕ) : ℕ := decideVal (extPacked n (mkEx 1 x))
private def forcedFlagV (n x : ℕ) : ℕ := bOr (bAnd (d0V n x) (bNot (d1V n x)))
  (bAnd (d1V n x) (bNot (d0V n x)))
private def forcedLabelV (n x : ℕ) : ℕ := bAnd (forcedFlagV n x) (d1V n x)

theorem val_cForced (n x : ℕ) :
    forcedVal n x = Nat.pair (forcedFlagV n x) (forcedLabelV n x) := by
  unfold forcedVal cForced
  rw [val_comp, val_cD01, val_cForcedCore]
  simp only [forcedFlagV, forcedLabelV, d0V, d1V]

private theorem allZeroVal_le_one (N : ℕ) : allZeroVal N ≤ 1 := by
  unfold allZeroVal
  rw [val_cAllZero]
  exact azFlag_le_one N.unpair.2 N.unpair.1

private theorem decideVal_le_one (n : ℕ) : decideVal n ≤ 1 := by
  rw [val_cDecide]
  exact allZeroVal_le_one _

/-! ### Bridging a single extended decision to `ExistsConsistentDL` -/

private theorem evalDLn_fvOf_congr (rules : List ℕ) (d e1 e2 : ℕ) (h : fvOf e1 = fvOf e2) :
    evalDLn rules d e1 = evalDLn rules d e2 := by
  induction rules with
  | nil => rfl
  | cons r rs ih =>
      have hf : featOf e1 (ruleJ r) = featOf e2 (ruleJ r) := by unfold featOf; rw [h]
      unfold evalDLn
      rw [hf]
      split_ifs with hc
      · exact ih
      · rfl

private theorem evalDLn_mkEx_congr (rules : List ℕ) (d b1 b2 x : ℕ) :
    evalDLn rules d (mkEx b1 x) = evalDLn rules d (mkEx b2 x) :=
  evalDLn_fvOf_congr rules d (mkEx b1 x) (mkEx b2 x) (by rw [fvOf_mkEx, fvOf_mkEx])

/-- **A single extended decision, unfolded.** `decideVal (extPacked n (mkEx b x)) ≠ 0` iff some
valid decision list, consistent with `exs`, evaluates the query point to `b`. -/
private theorem dV_iff (n x b : ℕ) (hn : SolveWF n) (hk : 0 < readK (svInst n)) (hb : b ≤ 1)
    (hone : svMask0 n = encodeList (List.replicate (readM (svInst n)) 1))
    (hqx : IsList x (readK (svInst n))) (hqbits : ∀ j, headL (peel x j) ≤ 1)
    (exs : List ℕ) (hdeq : readData (svInst n) = encodeList exs)
    (hdlen : exs.length = readM (svInst n)) :
    decideVal (extPacked n (mkEx b x)) ≠ 0 ↔
      ∃ rules d, (∀ r ∈ rules, ruleJ r < readK (svInst n)) ∧
        evalDLn rules d (mkEx b x) = b ∧ Consistent rules d exs := by
  have hSW := solveWF_extPacked n x b hn hb hqx hqbits exs hdeq hdlen
  have hk' : 0 < readK (svInst (extPacked n (mkEx b x))) := by
    rw [readK_svInst_extPacked]; exact hk
  have hone' := allOnes_extPacked n x b hone
  have hdeq' := readData_svInst_extPacked n x b exs hdeq
  have hdlen' : (mkEx b x :: exs).length = readM (svInst (extPacked n (mkEx b x))) := by
    rw [readM_svInst_extPacked]; simp [hdlen]
  rw [decide_iff (extPacked n (mkEx b x)) hSW hk' hone' (mkEx b x :: exs) hdeq' hdlen']
  unfold ExistsConsistentDL Consistent
  rw [readK_svInst_extPacked]
  constructor
  · rintro ⟨rules, d, hval, hcons⟩
    have hev : evalDLn rules d (mkEx b x) = b := by
      have := hcons (mkEx b x) (List.mem_cons_self ..)
      rwa [lblOf_mkEx] at this
    exact ⟨rules, d, hval, hev, fun e he => hcons e (List.mem_cons_of_mem _ he)⟩
  · rintro ⟨rules, d, hval, hev, hcons⟩
    refine ⟨rules, d, hval, fun e he => ?_⟩
    rcases List.mem_cons.mp he with rfl | hin
    · rw [lblOf_mkEx]; exact hev
    · exact hcons e hin

/-! ### The classification -/

/-- **The four reachable states of the two decisions**, both always bits: empty (neither
consistent), forced at `0`, forced at `1`, or split (both consistent). -/
private theorem forced_cases (n x : ℕ) :
    (d0V n x = 0 ∧ d1V n x = 0 ∧ forcedFlagV n x = 0 ∧ forcedLabelV n x = 0) ∨
    (d0V n x = 0 ∧ d1V n x = 1 ∧ forcedFlagV n x = 1 ∧ forcedLabelV n x = 1) ∨
    (d0V n x = 1 ∧ d1V n x = 0 ∧ forcedFlagV n x = 1 ∧ forcedLabelV n x = 0) ∨
    (d0V n x = 1 ∧ d1V n x = 1 ∧ forcedFlagV n x = 0 ∧ forcedLabelV n x = 0) := by
  have hd0 : d0V n x ≤ 1 := decideVal_le_one (extPacked n (mkEx 0 x))
  have hd1 : d1V n x ≤ 1 := decideVal_le_one (extPacked n (mkEx 1 x))
  rcases (by omega : d0V n x = 0 ∨ d0V n x = 1) with h0 | h0 <;>
    rcases (by omega : d1V n x = 0 ∨ d1V n x = 1) with h1 | h1
  · exact Or.inl ⟨h0, h1, by simp only [forcedFlagV, h0, h1]; decide,
      by simp only [forcedLabelV, forcedFlagV, h0, h1]; decide⟩
  · exact Or.inr (Or.inl ⟨h0, h1, by simp only [forcedFlagV, h0, h1]; decide,
      by simp only [forcedLabelV, forcedFlagV, h0, h1]; decide⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨h0, h1, by simp only [forcedFlagV, h0, h1]; decide,
      by simp only [forcedLabelV, forcedFlagV, h0, h1]; decide⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨h0, h1, by simp only [forcedFlagV, h0, h1]; decide,
      by simp only [forcedLabelV, forcedFlagV, h0, h1]; decide⟩))

/-- From "`b`'s extended call succeeds and the other fails", the classification's content: the truth
survives and every valid consistent decision list agrees with `b` at the query point. Uses
`exists_relabel` to rule out a non-bit prediction, and the failing other-bit call to rule out `1-b`. -/
private theorem forced_core (n x b : ℕ) (hn : SolveWF n) (hk : 0 < readK (svInst n)) (hb : b ≤ 1)
    (hone : svMask0 n = encodeList (List.replicate (readM (svInst n)) 1))
    (hqx : IsList x (readK (svInst n))) (hqbits : ∀ j, headL (peel x j) ≤ 1)
    (exs : List ℕ) (hdeq : readData (svInst n) = encodeList exs)
    (hdlen : exs.length = readM (svInst n))
    (hbforced : decideVal (extPacked n (mkEx b x)) ≠ 0)
    (hobforced : decideVal (extPacked n (mkEx (1 - b) x)) = 0) :
    ExistsConsistentDL (svInst n) exs ∧
      ∀ rules d, (∀ r ∈ rules, ruleJ r < readK (svInst n)) → Consistent rules d exs →
        evalDLn rules d (mkEx 0 x) = b := by
  have hlbl := (wfbits_exs_bits n hn.1 exs hdeq hdlen).1
  obtain ⟨rules, d, hval, hev, hcons⟩ :=
    (dV_iff n x b hn hk hb hone hqx hqbits exs hdeq hdlen).mp hbforced
  refine ⟨⟨rules, d, hval, hcons⟩, ?_⟩
  intro rules' d' hval' hcons'
  by_contra hne
  have hcase : evalDLn rules' d' (mkEx 0 x) = 1 - b ∨
      (evalDLn rules' d' (mkEx 0 x) ≠ 0 ∧ evalDLn rules' d' (mkEx 0 x) ≠ 1) := by omega
  have hother : decideVal (extPacked n (mkEx (1 - b) x)) ≠ 0 := by
    apply (dV_iff n x (1 - b) hn hk (by omega) hone hqx hqbits exs hdeq hdlen).mpr
    rcases hcase with hc | hc
    · refine ⟨rules', d', hval', ?_, hcons'⟩
      rw [evalDLn_mkEx_congr rules' d' (1 - b) 0 x]; exact hc
    · obtain ⟨rules'', d'', hval'', hev'', hcons''⟩ :=
        exists_relabel (readK (svInst n)) (mkEx 0 x) exs hlbl rules' d' hval' hcons' hc (1 - b)
      refine ⟨rules'', d'', hval'', ?_, hcons''⟩
      rw [evalDLn_mkEx_congr rules'' d'' (1 - b) 0 x]; exact hev''
  exact hother hobforced

/-- The converse direction's content: unanimity forces both extended calls to their expected
verdicts. -/
private theorem forced_of_unanimous (n x b : ℕ) (hn : SolveWF n) (hk : 0 < readK (svInst n))
    (hb : b ≤ 1) (hone : svMask0 n = encodeList (List.replicate (readM (svInst n)) 1))
    (hqx : IsList x (readK (svInst n))) (hqbits : ∀ j, headL (peel x j) ≤ 1)
    (exs : List ℕ) (hdeq : readData (svInst n) = encodeList exs)
    (hdlen : exs.length = readM (svInst n))
    (hcons : ExistsConsistentDL (svInst n) exs)
    (hunanim : ∀ rules d, (∀ r ∈ rules, ruleJ r < readK (svInst n)) → Consistent rules d exs →
      evalDLn rules d (mkEx 0 x) = b) :
    decideVal (extPacked n (mkEx b x)) ≠ 0 ∧ decideVal (extPacked n (mkEx (1 - b) x)) = 0 := by
  obtain ⟨rules, d, hval, hconsD⟩ := hcons
  have hev0 : evalDLn rules d (mkEx 0 x) = b := hunanim rules d hval hconsD
  have hevb : evalDLn rules d (mkEx b x) = b := by
    rw [evalDLn_mkEx_congr rules d b 0 x]; exact hev0
  have hbforced : decideVal (extPacked n (mkEx b x)) ≠ 0 :=
    (dV_iff n x b hn hk hb hone hqx hqbits exs hdeq hdlen).mpr ⟨rules, d, hval, hevb, hconsD⟩
  refine ⟨hbforced, ?_⟩
  by_contra hobforced
  obtain ⟨rules'', d'', hval'', hev'', hcons''⟩ :=
    (dV_iff n x (1 - b) hn hk (by omega) hone hqx hqbits exs hdeq hdlen).mp hobforced
  have hev0' : evalDLn rules'' d'' (mkEx 0 x) = 1 - b := by
    rw [evalDLn_mkEx_congr rules'' d'' 0 (1 - b) x]; exact hev''
  have := hunanim rules'' d'' hval'' hcons''
  omega

/-- **`forced_iff`.** `forcedVal n x` reads off `⟨1, b⟩` exactly when the version space is
nonempty and unanimous on `b` at the query point — [SQ] §4's read-off, made exact. The forward
direction is where `exists_relabel` is spent: the failing other call rules out `1 - b`, and
relabeling rules out every non-bit prediction. -/
theorem forced_iff (n x : ℕ) (hn : SolveWF n) (hk : 0 < readK (svInst n))
    (hone : svMask0 n = encodeList (List.replicate (readM (svInst n)) 1))
    (hqx : IsList x (readK (svInst n))) (hqbits : ∀ j, headL (peel x j) ≤ 1)
    (exs : List ℕ) (hdeq : readData (svInst n) = encodeList exs)
    (hdlen : exs.length = readM (svInst n)) (b : ℕ) (hb : b ≤ 1) :
    forcedVal n x = Nat.pair 1 b
      ↔ ExistsConsistentDL (svInst n) exs ∧
        ∀ rules d, (∀ r ∈ rules, ruleJ r < readK (svInst n)) → Consistent rules d exs →
          evalDLn rules d (mkEx 0 x) = b := by
  constructor
  · intro heq
    rw [val_cForced] at heq
    rcases forced_cases n x with ⟨h0, h1, hf, hl⟩ | ⟨h0, h1, hf, hl⟩ | ⟨h0, h1, hf, hl⟩ |
      ⟨h0, h1, hf, hl⟩ <;> rw [hf, hl] at heq
    · obtain ⟨hcontra, -⟩ := pair_inj' heq; omega
    · obtain ⟨-, hbeq⟩ := pair_inj' heq
      subst hbeq
      exact forced_core n x 1 hn hk (by omega) hone hqx hqbits exs hdeq hdlen
        (by unfold d1V at h1; omega) (by unfold d0V at h0; simpa using h0)
    · obtain ⟨-, hbeq⟩ := pair_inj' heq
      subst hbeq
      exact forced_core n x 0 hn hk (by omega) hone hqx hqbits exs hdeq hdlen
        (by unfold d0V at h0; omega) (by unfold d1V at h1; simpa using h1)
    · obtain ⟨hcontra, -⟩ := pair_inj' heq; omega
  · rintro ⟨hcons, hunanim⟩
    obtain ⟨hbforced, hobforced⟩ :=
      forced_of_unanimous n x b hn hk hb hone hqx hqbits exs hdeq hdlen hcons hunanim
    rw [val_cForced]
    have hd0 : d0V n x ≤ 1 := decideVal_le_one (extPacked n (mkEx 0 x))
    have hd1 : d1V n x ≤ 1 := decideVal_le_one (extPacked n (mkEx 1 x))
    rcases (by omega : b = 0 ∨ b = 1) with rfl | rfl
    · have hz0 : d0V n x = 1 := by unfold d0V at hd0 ⊢; omega
      have hz1 : d1V n x = 0 := by unfold d1V; simpa using hobforced
      simp only [forcedFlagV, forcedLabelV, hz0, hz1]; decide
    · have hz1 : d1V n x = 1 := by unfold d1V at hd1 ⊢; omega
      have hz0 : d0V n x = 0 := by unfold d0V; simpa using hobforced
      simp only [forcedFlagV, forcedLabelV, hz0, hz1]; decide

/-- **`empty_iff`.** Both extended decisions fail exactly when no consistent `1`-decision list
exists at all — the version space is empty. -/
theorem empty_iff (n x : ℕ) (hn : SolveWF n) (hk : 0 < readK (svInst n))
    (hone : svMask0 n = encodeList (List.replicate (readM (svInst n)) 1))
    (hqx : IsList x (readK (svInst n))) (hqbits : ∀ j, headL (peel x j) ≤ 1)
    (exs : List ℕ) (hdeq : readData (svInst n) = encodeList exs)
    (hdlen : exs.length = readM (svInst n)) :
    d0V n x = 0 ∧ d1V n x = 0 ↔ ¬ ExistsConsistentDL (svInst n) exs := by
  have hlbl := (wfbits_exs_bits n hn.1 exs hdeq hdlen).1
  unfold d0V d1V
  constructor
  · rintro ⟨h0, h1⟩ hcons
    obtain ⟨rules, d, hval, hconsD⟩ := hcons
    by_cases hv0 : evalDLn rules d (mkEx 0 x) = 0
    · exact ((dV_iff n x 0 hn hk (by omega) hone hqx hqbits exs hdeq hdlen).mpr
        ⟨rules, d, hval, hv0, hconsD⟩) h0
    · by_cases hv1 : evalDLn rules d (mkEx 0 x) = 1
      · have hev1 : evalDLn rules d (mkEx 1 x) = 1 := by
          rw [evalDLn_mkEx_congr rules d 1 0 x]; exact hv1
        exact ((dV_iff n x 1 hn hk (by omega) hone hqx hqbits exs hdeq hdlen).mpr
          ⟨rules, d, hval, hev1, hconsD⟩) h1
      · obtain ⟨rules', d', hval', hev', hcons'⟩ :=
          exists_relabel (readK (svInst n)) (mkEx 0 x) exs hlbl rules d hval hconsD
            ⟨hv0, hv1⟩ 0
        exact ((dV_iff n x 0 hn hk (by omega) hone hqx hqbits exs hdeq hdlen).mpr
          ⟨rules', d', hval', hev', hcons'⟩) h0
  · intro hncons
    refine ⟨?_, ?_⟩
    · by_contra h0
      obtain ⟨rules, d, hval, _, hcons⟩ :=
        (dV_iff n x 0 hn hk (by omega) hone hqx hqbits exs hdeq hdlen).mp h0
      exact hncons ⟨rules, d, hval, hcons⟩
    · by_contra h1
      obtain ⟨rules, d, hval, _, hcons⟩ :=
        (dV_iff n x 1 hn hk (by omega) hone hqx hqbits exs hdeq hdlen).mp h1
      exact hncons ⟨rules, d, hval, hcons⟩

/-- **`split_iff`.** Both extended decisions succeed exactly when the version space contains two
valid consistent members predicting the two different bits at the query point. -/
theorem split_iff (n x : ℕ) (hn : SolveWF n) (hk : 0 < readK (svInst n))
    (hone : svMask0 n = encodeList (List.replicate (readM (svInst n)) 1))
    (hqx : IsList x (readK (svInst n))) (hqbits : ∀ j, headL (peel x j) ≤ 1)
    (exs : List ℕ) (hdeq : readData (svInst n) = encodeList exs)
    (hdlen : exs.length = readM (svInst n)) :
    d0V n x ≠ 0 ∧ d1V n x ≠ 0 ↔
      ∃ rules0 d0 rules1 d1, (∀ r ∈ rules0, ruleJ r < readK (svInst n)) ∧
        Consistent rules0 d0 exs ∧ (∀ r ∈ rules1, ruleJ r < readK (svInst n)) ∧
        Consistent rules1 d1 exs ∧ evalDLn rules0 d0 (mkEx 0 x) = 0 ∧
        evalDLn rules1 d1 (mkEx 0 x) = 1 := by
  unfold d0V d1V
  rw [dV_iff n x 0 hn hk (by omega) hone hqx hqbits exs hdeq hdlen,
    dV_iff n x 1 hn hk (by omega) hone hqx hqbits exs hdeq hdlen]
  constructor
  · rintro ⟨⟨rules0, d0, hval0, hev0, hcons0⟩, ⟨rules1, d1, hval1, hev1, hcons1⟩⟩
    refine ⟨rules0, d0, rules1, d1, hval0, hcons0, hval1, hcons1, hev0, ?_⟩
    rw [← evalDLn_mkEx_congr rules1 d1 1 0 x]; exact hev1
  · rintro ⟨rules0, d0, rules1, d1, hval0, hcons0, hval1, hcons1, hev0, hev1⟩
    refine ⟨⟨rules0, d0, hval0, hev0, hcons0⟩, ⟨rules1, d1, hval1, ?_, hcons1⟩⟩
    rw [evalDLn_mkEx_congr rules1 d1 1 0 x]; exact hev1

/-! ### `cForced`'s native cost -/

/-- **The extension's `Bsv` step is exact**, since `BsvMask`/`BsvFind` are affine/multiplicative in
`readM` alone: bumping `readM` by one adds a fixed polynomial in `readK`. -/
private theorem Bsv_ext (n e : ℕ) :
    Bsv (extInst (svInst n) e)
      = Bsv (svInst n) + (8 * readK (svInst n) + 2442
          + (32 * readK (svInst n) + 11402) * readK (svInst n)) := by
  unfold Bsv BsvMask BsvFind
  rw [readK_extInst, readM_extInst]
  ring

private theorem tc_cExtPackedB_le (b n x : ℕ) (hb : b ≤ 1) :
    tc (cExtPackedB b) (Nat.pair n x) ≤ 60 := by
  have hN : tc cN (Nat.pair n x) ≤ 1 := by simp [cN]
  have hX : tc cX (Nat.pair n x) ≤ 1 := by simp [cX]
  have hvN : val cN (Nat.pair n x) = n := by simp [cN, val_left]
  have hSvInstP : tc cSvInstP (Nat.pair n x) ≤ 3 := by
    have := hN; simp only [cSvInstP, tc_comp, tc_left]; omega
  have hSvMask0P : tc cSvMask0P (Nat.pair n x) ≤ 3 := by
    have := hN; simp only [cSvMask0P, tc_comp, tc_right]; omega
  have hvSvInstP : val cSvInstP (Nat.pair n x) = svInst n := by
    simp [cSvInstP, val_comp, val_left, hvN, svInst]
  have hReadKP : tc cReadKP (Nat.pair n x) ≤ 5 := by
    have h1 := hSvInstP
    have h2 : tc cReadK (val cSvInstP (Nat.pair n x)) ≤ 1 := by rw [hvSvInstP]; simp [cReadK]
    simp only [cReadKP, tc_comp]; omega
  have hReadMP : tc cReadMP (Nat.pair n x) ≤ 7 := by
    have h1 := hSvInstP
    have h2 : tc cReadM (val cSvInstP (Nat.pair n x)) ≤ 3 := by
      rw [hvSvInstP]; exact tc_cReadM_le _
    simp only [cReadMP, tc_comp]; omega
  have hReadDataP : tc cReadDataP (Nat.pair n x) ≤ 7 := by
    have h1 := hSvInstP
    have h2 : tc cReadDataC (val cSvInstP (Nat.pair n x)) ≤ 3 := by
      simp [cReadDataC, tc_comp, tc_right]
    simp only [cReadDataP, tc_comp]; omega
  have hMkExB : tc (cMkExB b) (Nat.pair n x) ≤ 6 := by
    have h1 : tc (constCode b) (Nat.pair n x) ≤ 3 := by
      have := tc_constCode_le b (Nat.pair n x); omega
    have := hX
    simp only [cMkExB, tc_pair]; omega
  have hExtInstB : tc (cExtInstB b) (Nat.pair n x) ≤ 40 := by
    have h1 := hReadKP
    have h2 := hReadMP
    have h3 : tc succ (val cReadMP (Nat.pair n x)) ≤ 1 := by simp
    have h4 : tc (constCode 1) (Nat.pair n x) ≤ 3 := tc_constCode_le 1 _
    have h5 := hMkExB
    have h6 := hReadDataP
    simp only [cExtInstB, tc_pair, tc_comp]; omega
  have h7 : tc (constCode 1) (Nat.pair n x) ≤ 3 := tc_constCode_le 1 _
  simp only [cExtPackedB, tc_pair]; omega

/-- The forced-symbol read-off's `O(1)` bit logic, on any pair of already-bit-valued decisions. -/
private theorem tc_cForcedCore_le (d0 d1 : ℕ) (h0 : d0 ≤ 1) (h1 : d1 ≤ 1) :
    tc cForcedCore (Nat.pair d0 d1) ≤ 1200 := by
  have hD0 : tc cD0core (Nat.pair d0 d1) ≤ 1 := by simp [cD0core]
  have hD1 : tc cD1core (Nat.pair d0 d1) ≤ 1 := by simp [cD1core]
  have hvD0 : val cD0core (Nat.pair d0 d1) = d0 := by simp [cD0core, val_left]
  have hvD1 : val cD1core (Nat.pair d0 d1) = d1 := by simp [cD1core, val_right]
  have hNotD1 : tc (comp cNot cD1core) (Nat.pair d0 d1) ≤ 14 := by
    have := hD1
    have hb : val cD1core (Nat.pair d0 d1) ≤ 1 := by rw [hvD1]; exact h1
    have := tc_cNot_bit hb
    simp only [tc_comp]; omega
  have hvNotD1 : val (comp cNot cD1core) (Nat.pair d0 d1) = bNot d1 := by
    simp [val_comp, val_cNot'', hvD1]
  have hNotD0 : tc (comp cNot cD0core) (Nat.pair d0 d1) ≤ 14 := by
    have := hD0
    have hb : val cD0core (Nat.pair d0 d1) ≤ 1 := by rw [hvD0]; exact h0
    have := tc_cNot_bit hb
    simp only [tc_comp]; omega
  have hvNotD0 : val (comp cNot cD0core) (Nat.pair d0 d1) = bNot d0 := by
    simp [val_comp, val_cNot'', hvD0]
  have hAnd1 : tc cAnd (val (pair cD0core (comp cNot cD1core)) (Nat.pair d0 d1)) ≤ 204 := by
    rw [val_pair, hvD0, hvNotD1]
    exact tc_cAnd_bit h0 (bNot_le_one _)
  have hPair1 : tc (pair cD0core (comp cNot cD1core)) (Nat.pair d0 d1) ≤ 16 := by
    have := hD0; have := hNotD1; simp only [tc_pair]; omega
  have hBranch1 : tc (comp cAnd (pair cD0core (comp cNot cD1core))) (Nat.pair d0 d1) ≤ 221 := by
    have := hPair1; have := hAnd1; simp only [tc_comp]; omega
  have hvBranch1 : val (comp cAnd (pair cD0core (comp cNot cD1core))) (Nat.pair d0 d1)
      = bAnd d0 (bNot d1) := by
    simp [val_comp, val_pair, val_cAnd'', hvD0, hvNotD1]
  have hAnd2 : tc cAnd (val (pair cD1core (comp cNot cD0core)) (Nat.pair d0 d1)) ≤ 204 := by
    rw [val_pair, hvD1, hvNotD0]
    exact tc_cAnd_bit h1 (bNot_le_one _)
  have hPair2 : tc (pair cD1core (comp cNot cD0core)) (Nat.pair d0 d1) ≤ 16 := by
    have := hD1; have := hNotD0; simp only [tc_pair]; omega
  have hBranch2 : tc (comp cAnd (pair cD1core (comp cNot cD0core))) (Nat.pair d0 d1) ≤ 221 := by
    have := hPair2; have := hAnd2; simp only [tc_comp]; omega
  have hvBranch2 : val (comp cAnd (pair cD1core (comp cNot cD0core))) (Nat.pair d0 d1)
      = bAnd d1 (bNot d0) := by
    simp [val_comp, val_pair, val_cAnd'', hvD1, hvNotD0]
  have hPairBoth : tc (pair (comp cAnd (pair cD0core (comp cNot cD1core)))
      (comp cAnd (pair cD1core (comp cNot cD0core)))) (Nat.pair d0 d1) ≤ 443 := by
    have := hBranch1; have := hBranch2; simp only [tc_pair]; omega
  have hOr : tc cOr (val (pair (comp cAnd (pair cD0core (comp cNot cD1core)))
      (comp cAnd (pair cD1core (comp cNot cD0core)))) (Nat.pair d0 d1)) ≤ 21 := by
    rw [val_pair, hvBranch1, hvBranch2]
    exact tc_cOr_bit (bAnd_le_one _ _) (bAnd_le_one _ _)
  have hFlag : tc cFlagCore (Nat.pair d0 d1) ≤ 465 := by
    have := hPairBoth; have := hOr; simp only [cFlagCore, tc_comp]; omega
  have hvFlag : val cFlagCore (Nat.pair d0 d1) = bOr (bAnd d0 (bNot d1)) (bAnd d1 (bNot d0)) := by
    simp only [cFlagCore, val_comp, val_pair, val_cOr'', hvBranch1, hvBranch2]
  have hAnd3 : tc cAnd (val (pair cFlagCore cD1core) (Nat.pair d0 d1)) ≤ 204 := by
    rw [val_pair, hvFlag, hvD1]
    exact tc_cAnd_bit (bOr_le_one _ _) h1
  have hPair3 : tc (pair cFlagCore cD1core) (Nat.pair d0 d1) ≤ 467 := by
    have := hFlag; have := hD1; simp only [tc_pair]; omega
  have hLabel : tc cLabelCore (Nat.pair d0 d1) ≤ 672 := by
    have := hPair3; have := hAnd3; simp only [cLabelCore, tc_comp]; omega
  simp only [cForcedCore, tc_pair]; omega

set_option maxHeartbeats 0 in
-- same slow-not-stuck kernel unfolding as `hcode_cSolve` above: `cSolve`'s `rfind'`-freeness is
-- witnessed purely by the goal's own inductive shape, so `constructor` walks the whole private
-- structure by repeated weak-head reduction — no name from `DecisionListSolver` is ever written.

private theorem rfindFree_cForced : RfindFree cForced := by repeat constructor

/-- **`cForced`'s native cost.** Two extended solves at `readM (svInst n) + 1` examples with
`readK (svInst n)` unchanged (`OneDL.tc_cSolve_raw` instantiated at each, via the exact `Bsv`
step `Bsv_ext`), plus the Stage A scan overhead (`tc_cDecide_le`), plus `O(1)` wiring and
read-off. -/
theorem tc_forced_raw (n x : ℕ) (hn : SolveWF n)
    (hqx : IsList x (readK (svInst n))) (hqbits : ∀ j, headL (peel x j) ≤ 1) :
    tc cForced (Nat.pair n x) ≤
      2 * ((Bsv (svInst n) + (8 * readK (svInst n) + 2442
            + (32 * readK (svInst n) + 11402) * readK (svInst n)) + 42) * (readM (svInst n) + 1)
          + 67 + 301 * (readM (svInst n) + 1) + 37 + 60) + 1300 := by
  obtain ⟨exs, hdeq, hdlen, _⟩ := hn.1.2
  have hb0 : SolveWF (extPacked n (mkEx 0 x)) :=
    solveWF_extPacked n x 0 hn (by omega) hqx hqbits exs hdeq hdlen
  have hb1 : SolveWF (extPacked n (mkEx 1 x)) :=
    solveWF_extPacked n x 1 hn (by omega) hqx hqbits exs hdeq hdlen
  have hrm0 : readM (svInst (extPacked n (mkEx 0 x))) = readM (svInst n) + 1 :=
    readM_svInst_extPacked n x 0
  have hrm1 : readM (svInst (extPacked n (mkEx 1 x))) = readM (svInst n) + 1 :=
    readM_svInst_extPacked n x 1
  have hbsv0 : Bsv (svInst (extPacked n (mkEx 0 x)))
      = Bsv (svInst n) + (8 * readK (svInst n) + 2442
          + (32 * readK (svInst n) + 11402) * readK (svInst n)) := by
    rw [svInst_extPacked]; exact Bsv_ext n (mkEx 0 x)
  have hbsv1 : Bsv (svInst (extPacked n (mkEx 1 x)))
      = Bsv (svInst n) + (8 * readK (svInst n) + 2442
          + (32 * readK (svInst n) + 11402) * readK (svInst n)) := by
    rw [svInst_extPacked]; exact Bsv_ext n (mkEx 1 x)
  have hsolve0 : tc cSolve (extPacked n (mkEx 0 x))
      ≤ (Bsv (svInst n) + (8 * readK (svInst n) + 2442
          + (32 * readK (svInst n) + 11402) * readK (svInst n)) + 42) * (readM (svInst n) + 1)
        + 67 := by
    have h := tc_cSolve_raw (extPacked n (mkEx 0 x)) hb0.1 hb0.2
    rw [hbsv0, hrm0] at h; exact h
  have hsolve1 : tc cSolve (extPacked n (mkEx 1 x))
      ≤ (Bsv (svInst n) + (8 * readK (svInst n) + 2442
          + (32 * readK (svInst n) + 11402) * readK (svInst n)) + 42) * (readM (svInst n) + 1)
        + 67 := by
    have h := tc_cSolve_raw (extPacked n (mkEx 1 x)) hb1.1 hb1.2
    rw [hbsv1, hrm1] at h; exact h
  have hdec0 : tc cDecide (extPacked n (mkEx 0 x))
      ≤ tc cSolve (extPacked n (mkEx 0 x)) + 301 * (readM (svInst n) + 1) + 37 := by
    have h := tc_cDecide_le (extPacked n (mkEx 0 x)) hb0
    rw [hrm0] at h; exact h
  have hdec1 : tc cDecide (extPacked n (mkEx 1 x))
      ≤ tc cSolve (extPacked n (mkEx 1 x)) + 301 * (readM (svInst n) + 1) + 37 := by
    have h := tc_cDecide_le (extPacked n (mkEx 1 x)) hb1
    rw [hrm1] at h; exact h
  have hep0 : tc (cExtPackedB 0) (Nat.pair n x) ≤ 60 := tc_cExtPackedB_le 0 n x (by omega)
  have hep1 : tc (cExtPackedB 1) (Nat.pair n x) ≤ 60 := tc_cExtPackedB_le 1 n x (by omega)
  have hcall0 : tc (comp cDecide (cExtPackedB 0)) (Nat.pair n x)
      ≤ tc cDecide (extPacked n (mkEx 0 x)) + 61 := by
    have h := tc_comp cDecide (cExtPackedB 0) (Nat.pair n x)
    rw [val_cExtPackedB] at h
    omega
  have hcall1 : tc (comp cDecide (cExtPackedB 1)) (Nat.pair n x)
      ≤ tc cDecide (extPacked n (mkEx 1 x)) + 61 := by
    have h := tc_comp cDecide (cExtPackedB 1) (Nat.pair n x)
    rw [val_cExtPackedB] at h
    omega
  have hd01 : tc cD01 (Nat.pair n x)
      ≤ tc (comp cDecide (cExtPackedB 0)) (Nat.pair n x)
        + tc (comp cDecide (cExtPackedB 1)) (Nat.pair n x) + 1 := by
    simp only [cD01, tc_pair]; omega
  have hd0b : d0V n x ≤ 1 := decideVal_le_one (extPacked n (mkEx 0 x))
  have hd1b : d1V n x ≤ 1 := decideVal_le_one (extPacked n (mkEx 1 x))
  have hcorepre : val cD01 (Nat.pair n x)
      = Nat.pair (decideVal (extPacked n (mkEx 0 x))) (decideVal (extPacked n (mkEx 1 x))) :=
    val_cD01 n x
  have hcore : tc cForcedCore (val cD01 (Nat.pair n x)) ≤ 1200 := by
    rw [hcorepre]
    exact tc_cForcedCore_le _ _ (by unfold d0V at hd0b; exact hd0b) (by unfold d1V at hd1b; exact hd1b)
  simp only [cForced, tc_comp]
  omega

/-- **The forced-symbol predictor's well-formed domain.** -/
def ForcedWF (p : ℕ) : Prop :=
  SolveWF p.unpair.1 ∧ IsList p.unpair.2 (readK (svInst p.unpair.1)) ∧
    ∀ j, headL (peel p.unpair.2 j) ≤ 1

/-- **`polyTime_forced`.** The two-consistency-call forced-symbol predictor is poly-time on the
well-formed domain: `cForced` computes it, its native cost is `PolyBoundedOn` (via `tc_forced_raw`
and `OneDL.polyTime_solve`'s own poly-bit closure applied twice), and its output is a bit,
hence trivially poly-bit. -/
theorem polyTime_forced : PolyTimeOn ForcedWF (fun p => forcedVal p.unpair.1 p.unpair.2) := by
  refine ⟨cForced, rfindFree_cForced, fun p _ => ?_, ?_, ?_⟩
  · change val cForced p = forcedVal p.unpair.1 p.unpair.2
    unfold forcedVal
    rw [Nat.pair_unpair]
  · refine ⟨300000, 4, fun p hp => ?_⟩
    obtain ⟨n, x, rfl⟩ : ∃ n x, p = Nat.pair n x :=
      ⟨p.unpair.1, p.unpair.2, (Nat.pair_unpair p).symm⟩
    obtain ⟨hn, hqx, hqbits⟩ := hp
    simp only [Nat.unpair_pair] at hn hqx hqbits
    have hraw := tc_forced_raw n x hn hqx hqbits
    have hrk : readK (svInst n) ≤ Nat.size n :=
      le_trans (readK_le_size (svInst n) hn.1.1) (Nat.size_le_size (Nat.unpair_left_le n))
    have hrm : readM (svInst n) ≤ Nat.size n :=
      le_trans (readM_le_size (svInst n) hn.1.1) (Nat.size_le_size (Nat.unpair_left_le n))
    have hbsv : Bsv (svInst n) ≤ 19668 * (Nat.size n + 1) ^ 3 := by
      unfold Bsv BsvMask BsvFind
      nlinarith [hrk, hrm, Nat.mul_le_mul (Nat.mul_le_mul hrk hrk) hrm, Nat.mul_le_mul hrk hrk]
    have hsizeN : Nat.size n ≤ Nat.size (Nat.pair n x) := Nat.size_le_size (left_le_pair n x)
    set S := Nat.size (Nat.pair n x) with hSdef
    have hrk' : readK (svInst n) + 1 ≤ S + 1 := by omega
    have hrm' : readM (svInst n) + 1 ≤ S + 1 := by omega
    have hbsv' : Bsv (svInst n) ≤ 19668 * (S + 1) ^ 3 := by
      calc Bsv (svInst n) ≤ 19668 * (Nat.size n + 1) ^ 3 := hbsv
        _ ≤ 19668 * (S + 1) ^ 3 := by gcongr
    have hDelta : 8 * readK (svInst n) + 2442
        + (32 * readK (svInst n) + 11402) * readK (svInst n) ≤ 50000 * (S + 1) ^ 2 := by
      nlinarith [hrk', Nat.mul_le_mul hrk' hrk']
    have hSum : Bsv (svInst n) + (8 * readK (svInst n) + 2442
        + (32 * readK (svInst n) + 11402) * readK (svInst n)) + 42 ≤ 70000 * (S + 1) ^ 3 := by
      nlinarith [hbsv', hDelta]
    have hMul : (Bsv (svInst n) + (8 * readK (svInst n) + 2442
        + (32 * readK (svInst n) + 11402) * readK (svInst n)) + 42) * (readM (svInst n) + 1)
        ≤ 70000 * (S + 1) ^ 4 := by
      calc _ ≤ 70000 * (S + 1) ^ 3 * (S + 1) := Nat.mul_le_mul hSum hrm'
        _ = 70000 * (S + 1) ^ 4 := by ring
    have hpow : (S + 1) ^ 3 ≤ (S + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
    nlinarith [hraw, hMul, hrm', hpow]
  · refine ⟨1, 0, fun p _ => ?_⟩
    have h1 : forcedFlagV p.unpair.1 p.unpair.2 ≤ 1 := bOr_le_one _ _
    have h2 : forcedLabelV p.unpair.1 p.unpair.2 ≤ 1 := bAnd_le_one _ _
    have hval3 : forcedVal p.unpair.1 p.unpair.2 ≤ 3 := by
      rw [val_cForced]
      calc Nat.pair (forcedFlagV p.unpair.1 p.unpair.2) (forcedLabelV p.unpair.1 p.unpair.2)
          ≤ Nat.pair 1 1 := pair_mono' h1 h2
        _ = 3 := by decide
    have hsize : Nat.size (forcedVal p.unpair.1 p.unpair.2) ≤ 2 :=
      le_trans (Nat.size_le_size hval3) (by decide)
    simpa using hsize

/-! ## Axiom-cleanliness guards (CI-enforced)

Each guard **fails `lake build`** if the theorem's axiom set ever drifts from the standard
`[propext, Classical.choice, Quot.sound]`. -/

/-- info: 'OneDL.decide_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms decide_iff

/-- info: 'OneDL.exists_relabel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms exists_relabel

/-- info: 'OneDL.forced_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms forced_iff

/-- info: 'OneDL.empty_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms empty_iff

/-- info: 'OneDL.split_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms split_iff

/-- info: 'OneDL.tc_forced_raw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms tc_forced_raw

/-- info: 'OneDL.polyTime_forced' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms polyTime_forced

end OneDL
