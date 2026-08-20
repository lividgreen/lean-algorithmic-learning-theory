/-
Copyright (c) 2026 Mykola Palamarchuk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mykola Palamarchuk
-/
import ALT.ConjunctionSolver

-- Formal-check file, not Mathlib-destined: opt out of the house-style linters.
set_option linter.style.header false
set_option linter.style.longLine false

/-!
# The version-space (forced-symbol) predictor for conjunctions

Provenance: [SQ] §4's *General form* paragraph, read alongside Corollary 4.3(b)'s read-off for
1-decision lists (`ALT/DecisionListPredictor.lean`): the two-consistency-call forced-symbol
predictor is not special to decision lists — any class with a poly-time consistency solver
(Hirsh–Mishra–Pitt 2004) supports it the same way. This module runs that argument over the
conjunction decider (`ALT/ConjunctionSolver.lean`).

Extends a solver instance by one candidate example (`mkEx`, `extInst`) and composes two decisions
— `cConjSolve` run on the instance extended by the query point at each candidate label — into the
forced-symbol verdict, exactly as [SQ] §4's read-off describes: append each candidate next-symbol
as a constraint; the symbol whose appended constraint leaves every consistent conjunction in
agreement is the prediction.

**Cheaper than the 1-DL case, structurally.** `Conj.evalConj`'s output is a bit BY CONSTRUCTION
(`Conj.evalConj_le_one`), unlike a decision list's `evalDLn`, which can return an arbitrary label via
`ruleL` and therefore needs `exists_relabel` to rule out a non-bit prediction at the query before the
two-call classification is exact. No such gap exists here, so `conj_empty_iff` below is immediate
from `evalConj`'s bit-ness and its label-invariance (`evalConj_mkEx_congr`) — no relabelling argument
is ported. Likewise `cConjSolve`'s own output IS the consistency verdict (no separate "mask-emptiness
scan" the way `OneDL.cSolve`'s mask needed one): Stage A of the 1-DL predictor (`cDecide`/`decideVal`)
has no analogue here, since `Conj.conjDecideVal` already is the computed bit.

Placed in its OWN module — mirroring `DecisionListSolver.lean`/`DecisionListPredictor.lean` — rather
than as a section of `ConjunctionSolver.lean`, so the cross-module transfer is genuinely exercised:
the whole classification below is built ONLY from `Conj`'s public API
(`cConjSolve`/`val_cConjSolve`/`conj_decides`/`tc_cConjSolve_raw`/`PolyTimeOn`), with no Code-level
`rfl` bridge across the module boundary — the measurement this target exists to make (see the
`CLAUDE.md` T41 lesson: a private composition law forces an expensive re-derivation from the
consumer side; here the composition law was public from the start).
-/

namespace Conj

open OneDL
open Nat.Partrec (Code)
open Nat.Partrec.Code
open TimeCost

/-! ## Stage B (relative to the 1-DL predictor's lettering) — extending an instance by one example

`mkEx b fv` packs a candidate example at feature vector `fv` with label `b`; `extInst` prepends it
onto a solver instance's example list (a flag-cons cell, `O(1)` — prepend, not append, since
`ConsistentConj` quantifies over membership and example order is immaterial). No mask to extend
(unlike `OneDL`'s solver, `Conj`'s decider carries no working mask) and no separate "packed with
mask" step: the extended CJ-C input is `extInst inst (mkEx b x)` itself. -/

/-- An example with label `b` and feature vector `fv`. -/
def mkEx (b fv : ℕ) : ℕ := Nat.pair b fv

/-- The instance extended by one candidate example `e`, prepended. -/
def extInst (inst e : ℕ) : ℕ :=
  Nat.pair (readK inst) (Nat.pair (readM inst + 1) (Nat.pair 1 (Nat.pair e (readData inst))))

private theorem lblOf_mkEx (b fv : ℕ) : lblOf (mkEx b fv) = b := by simp [mkEx, lblOf, Nat.unpair_pair]
private theorem fvOf_mkEx (b fv : ℕ) : fvOf (mkEx b fv) = fv := by simp [mkEx, fvOf, Nat.unpair_pair]

private theorem readK_extInst (inst e : ℕ) : readK (extInst inst e) = readK inst := by
  simp [extInst, readK, Nat.unpair_pair]
private theorem readM_extInst (inst e : ℕ) : readM (extInst inst e) = readM inst + 1 := by
  simp [extInst, readM, Nat.unpair_pair]
private theorem readData_extInst (inst e : ℕ) :
    readData (extInst inst e) = Nat.pair 1 (Nat.pair e (readData inst)) := by
  simp [extInst, readData, Nat.unpair_pair]

/-! ### Well-formedness is preserved by extension -/

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
      have h1 := congrArg Nat.unpair hb
      rw [Nat.unpair_pair, Nat.unpair_pair] at h1
      have h2 : x = y ∧ encodeList xs = encodeList ys := by
        have := congrArg Prod.snd h1
        simp only at this
        have h3 := congrArg Nat.unpair this
        rw [Nat.unpair_pair, Nat.unpair_pair] at h3
        exact ⟨congrArg Prod.fst h3, congrArg Prod.snd h3⟩
      rw [h2.1, ih ys h2.2]

/-- `WFBits`'s own binary-regime witness list agrees with any other `encodeList`-matching list. -/
private theorem wfbits_exs_bits (inst : ℕ) (hw : WFBits inst) (exs : List ℕ)
    (hdeq : readData inst = encodeList exs) (hdlen : exs.length = readM inst) :
    (∀ e ∈ exs, lblOf e ≤ 1) ∧ ∀ e ∈ exs, ∀ j, featOf e j ≤ 1 := by
  obtain ⟨_, exsW, hdeqW, _, hlblW, hfeatW⟩ := hw
  have heq : exsW = exs := encodeList_inj _ _ (by rw [← hdeqW, ← hdeq])
  subst heq
  exact ⟨hlblW, hfeatW⟩

private theorem wfbits_extInst (inst x b : ℕ) (hw : WFBits inst) (hb : b ≤ 1)
    (hqx : IsList x (readK inst)) (hqbits : ∀ j, headL (peel x j) ≤ 1)
    (exs : List ℕ) (hdeq : readData inst = encodeList exs) (hdlen : exs.length = readM inst) :
    WFBits (extInst inst (mkEx b x)) := by
  obtain ⟨hwfB, exsW, hdeqW, hdlenW, hlblW, hfeatW⟩ := hw
  obtain ⟨hlbl, hfeat⟩ := wfbits_exs_bits inst ⟨hwfB, exsW, hdeqW, hdlenW, hlblW, hfeatW⟩ exs hdeq hdlen
  refine ⟨⟨?_, ?_, ?_⟩, mkEx b x :: exs, ?_, ?_, ?_, ?_⟩
  · rw [readM_extInst]; omega
  · rw [readData_extInst, hdeq, readM_extInst]
    exact IsList.cons (mkEx b x) (encodeList exs) (readM inst) (hdeq ▸ hwfB.2.1)
  · rw [show firstFV (extInst inst (mkEx b x)) = fvOf (mkEx b x) from by
        simp [firstFV, extInst, readData, firstExample, Nat.unpair_pair, fvOf],
      fvOf_mkEx, readK_extInst]
    exact hqx
  · rw [readData_extInst, hdeq]; rfl
  · rw [readM_extInst]; simp [hdlen]
  · intro e he
    rcases List.mem_cons.mp he with rfl | hin
    · rw [lblOf_mkEx]; exact hb
    · exact hlbl e hin
  · intro e he j
    rcases List.mem_cons.mp he with rfl | hin
    · show featOf (mkEx b x) j ≤ 1
      unfold featOf; rw [fvOf_mkEx]; exact hqbits j
    · exact hfeat e hin j

/-! ## `Code` realisation: the extended instance, and two fresh `cConjSolve` calls

`cX`/`cN` project the packed input `⟨inst, x⟩`; `cExtInstB b` builds `extInst inst (mkEx b x)` as a
`Code`; `cD01` is the pair of extended decisions, `⟨inst,x⟩ ↦ ⟨dV inst x 0, dV inst x 1⟩`. -/

private def cN : Code := left
private def cX : Code := right
private def cReadKP : Code := comp cReadK cN
private def cReadMP : Code := comp cReadM cN
private def cReadDataC : Code := comp right right
private def cReadDataP : Code := comp cReadDataC cN

private theorem val_cN (n x : ℕ) : val cN (Nat.pair n x) = n := by simp [cN, val_left]
private theorem val_cReadDataC (inst : ℕ) : val cReadDataC inst = readData inst := by
  simp [cReadDataC, val_comp, val_right, readData]

/-- `mkEx b x`, from `⟨n, x⟩`, for a literal bit `b`. -/
private def cMkExB (b : ℕ) : Code := pair (constCode b) cX
/-- `extInst inst (mkEx b x)`, from `⟨n, x⟩`. -/
private def cExtInstB (b : ℕ) : Code :=
  pair cReadKP (pair (comp succ cReadMP) (pair (constCode 1) (pair (cMkExB b) cReadDataP)))

private theorem val_cExtInstB (b n x : ℕ) :
    val (cExtInstB b) (Nat.pair n x) = extInst n (mkEx b x) := by
  simp only [cExtInstB, cMkExB, cReadKP, cReadMP, cReadDataP, cN, cX, val_pair, val_comp, val_left,
    val_right, val_succ, val_constCode, val_cReadK, val_cReadM, val_cReadDataC, Nat.unpair_pair,
    extInst, mkEx]

/-- Both extended decisions, computed once each — via `cConjSolve` directly, since CJ-C's own
output already IS the verdict bit (no `cDecide`-style scan needed on top of it). -/
private def cD01 : Code := pair (comp cConjSolve (cExtInstB 0)) (comp cConjSolve (cExtInstB 1))

private theorem val_cD01 (n x : ℕ) :
    val cD01 (Nat.pair n x)
      = Nat.pair (conjDecideVal (extInst n (mkEx 0 x))) (conjDecideVal (extInst n (mkEx 1 x))) := by
  simp only [cD01, val_pair, val_comp, val_cExtInstB, val_cConjSolve]

/-! ### The forced-symbol read-off — pure `O(1)` bit logic on the two decisions -/

private def cD0core : Code := left
private def cD1core : Code := right
/-- `d0 XOR d1`: exactly one of the two extended decisions succeeded. -/
private def cFlagCore : Code :=
  comp cOr (pair (comp cAnd (pair cD0core (comp cNot cD1core)))
                 (comp cAnd (pair cD1core (comp cNot cD0core))))
/-- The forced label, valid only when `cFlagCore ≠ 0`: `d1` itself. -/
private def cLabelCore : Code := comp cAnd (pair cFlagCore cD1core)
private def cForcedCore : Code := pair cFlagCore cLabelCore

/-- **`cForced`**: the two-consistency-call forced-symbol predictor, on the packed input `⟨inst,x⟩`. -/
def cForced : Code := comp cForcedCore cD01

/-- `forcedVal inst x`: `⟨1, b⟩` when exactly one of the two extended decisions succeeds (`b` its
label), `⟨0, 0⟩` otherwise (empty or split). -/
def forcedVal (inst x : ℕ) : ℕ := val cForced (Nat.pair inst x)

private def d0V (inst x : ℕ) : ℕ := conjDecideVal (extInst inst (mkEx 0 x))
private def d1V (inst x : ℕ) : ℕ := conjDecideVal (extInst inst (mkEx 1 x))
private def forcedFlagV (inst x : ℕ) : ℕ :=
  bitOr (bitAnd (d0V inst x) (bitNot (d1V inst x))) (bitAnd (d1V inst x) (bitNot (d0V inst x)))
private def forcedLabelV (inst x : ℕ) : ℕ := bitAnd (forcedFlagV inst x) (d1V inst x)

theorem val_cForced (inst x : ℕ) :
    forcedVal inst x = Nat.pair (forcedFlagV inst x) (forcedLabelV inst x) := by
  unfold forcedVal cForced
  rw [val_comp, val_cD01]
  simp only [cForcedCore, cFlagCore, cLabelCore, cD0core, cD1core, val_pair, val_comp, val_left,
    val_right, val_cAnd', val_cOr', val_cNot', Nat.unpair_pair, forcedFlagV, forcedLabelV, d0V, d1V]

/-! ### Bridging a single extended decision to `ExistsConsistentConj` -/

/-- **`evalConj` is label-invariant at the query**: it reads only the feature vector, never the
label, so relabelling the candidate never changes the verdict. -/
theorem evalConj_mkEx_congr (lits : List ℕ) (b1 b2 x : ℕ) :
    evalConj lits (mkEx b1 x) = evalConj lits (mkEx b2 x) := by
  induction lits with
  | nil => rfl
  | cons r rs ih =>
      have hf : featOf (mkEx b1 x) (litJ r) = featOf (mkEx b2 x) (litJ r) := by
        unfold featOf; rw [fvOf_mkEx, fvOf_mkEx]
      unfold evalConj
      rw [hf, ih]

/-- **A single extended decision, unfolded.** `conjDecideVal` at the instance extended by `⟨b,x⟩`
is nonzero iff some valid literal set, consistent with `exs`, has the query evaluate to `b`. -/
theorem dV_iff (inst x b : ℕ) (hw : WFBits inst) (hb : b ≤ 1)
    (hqx : IsList x (readK inst)) (hqbits : ∀ j, headL (peel x j) ≤ 1)
    (exs : List ℕ) (hdeq : readData inst = encodeList exs) (hdlen : exs.length = readM inst) :
    conjDecideVal (extInst inst (mkEx b x)) ≠ 0 ↔
      ∃ lits, (∀ r ∈ lits, litJ r < readK inst) ∧
        evalConj lits (mkEx b x) = b ∧ ConsistentConj lits exs := by
  have hWF := wfbits_extInst inst x b hw hb hqx hqbits exs hdeq hdlen
  have hdeq' : readData (extInst inst (mkEx b x)) = encodeList (mkEx b x :: exs) := by
    rw [readData_extInst, hdeq]; rfl
  have hdlen' : (mkEx b x :: exs).length = readM (extInst inst (mkEx b x)) := by
    rw [readM_extInst]; simp [hdlen]
  have hlbl' : ∀ e ∈ (mkEx b x :: exs), lblOf e ≤ 1 := by
    intro e he
    rcases List.mem_cons.mp he with rfl | hin
    · rw [lblOf_mkEx]; exact hb
    · exact (wfbits_exs_bits inst hw exs hdeq hdlen).1 e hin
  rw [conj_decides (extInst inst (mkEx b x)) (mkEx b x :: exs) hdeq' hdlen' hlbl']
  unfold ExistsConsistentConj ConsistentConj
  rw [readK_extInst]
  constructor
  · rintro ⟨lits, hval, hcons⟩
    refine ⟨lits, hval, ?_, fun e he => hcons e (List.mem_cons_of_mem _ he)⟩
    have := hcons (mkEx b x) (List.mem_cons_self ..)
    rwa [lblOf_mkEx] at this
  · rintro ⟨lits, hval, hev, hcons⟩
    refine ⟨lits, hval, fun e he => ?_⟩
    rcases List.mem_cons.mp he with rfl | hin
    · rw [lblOf_mkEx]; exact hev
    · exact hcons e hin

/-! ### The classification

Both `conj_empty_iff` and `forced_core` below skip `OneDL`'s `exists_relabel` step entirely:
`evalConj`'s value is a bit BY CONSTRUCTION (`evalConj_le_one`), so "the query's predicted value" is
always `0` or `1` — there is no non-bit prediction case to exclude before the two-call read-off is
exact. -/

/-- **`conj_empty_iff`.** Neither extended call succeeds iff no consistent literal set exists at
all — the version space is empty. Immediate from `evalConj`'s bit-ness and label-invariance: any
witness consistent with `exs` already decides the query at SOME bit, giving one of the two calls a
witness. -/
theorem conj_empty_iff (inst x : ℕ) (hw : WFBits inst)
    (hqx : IsList x (readK inst)) (hqbits : ∀ j, headL (peel x j) ≤ 1)
    (exs : List ℕ) (hdeq : readData inst = encodeList exs) (hdlen : exs.length = readM inst) :
    d0V inst x = 0 ∧ d1V inst x = 0 ↔ ¬ ExistsConsistentConj inst exs := by
  unfold d0V d1V
  constructor
  · rintro ⟨h0, h1⟩ ⟨lits, hval, hcons⟩
    have hωle : evalConj lits (mkEx 0 x) ≤ 1 := evalConj_le_one lits (mkEx 0 x)
    rcases (by omega : evalConj lits (mkEx 0 x) = 0 ∨ evalConj lits (mkEx 0 x) = 1) with hω0 | hω1
    · exact ((dV_iff inst x 0 hw (by omega) hqx hqbits exs hdeq hdlen).mpr
        ⟨lits, hval, hω0, hcons⟩) h0
    · have hev1 : evalConj lits (mkEx 1 x) = 1 := by
        rw [evalConj_mkEx_congr lits 1 0 x]; exact hω1
      exact ((dV_iff inst x 1 hw (by omega) hqx hqbits exs hdeq hdlen).mpr
        ⟨lits, hval, hev1, hcons⟩) h1
  · intro hncons
    refine ⟨?_, ?_⟩
    · by_contra h0
      obtain ⟨lits, hval, _, hcons⟩ := (dV_iff inst x 0 hw (by omega) hqx hqbits exs hdeq hdlen).mp h0
      exact hncons ⟨lits, hval, hcons⟩
    · by_contra h1
      obtain ⟨lits, hval, _, hcons⟩ := (dV_iff inst x 1 hw (by omega) hqx hqbits exs hdeq hdlen).mp h1
      exact hncons ⟨lits, hval, hcons⟩

/-- From "`b`'s extended call succeeds and the other fails", the classification's content: the truth
survives and every valid consistent literal set agrees with `b` at the query point. No relabelling
needed: any OTHER consistent witness `lits'` has `evalConj lits' (mkEx 0 x)` a bit, and if it were
`1-b` it would itself witness the OTHER (failing) call. -/
private theorem forced_core (inst x b : ℕ) (hw : WFBits inst) (hb : b ≤ 1)
    (hqx : IsList x (readK inst)) (hqbits : ∀ j, headL (peel x j) ≤ 1)
    (exs : List ℕ) (hdeq : readData inst = encodeList exs) (hdlen : exs.length = readM inst)
    (hbforced : conjDecideVal (extInst inst (mkEx b x)) ≠ 0)
    (hobforced : conjDecideVal (extInst inst (mkEx (1 - b) x)) = 0) :
    ExistsConsistentConj inst exs ∧
      ∀ lits, (∀ r ∈ lits, litJ r < readK inst) → ConsistentConj lits exs →
        evalConj lits (mkEx 0 x) = b := by
  obtain ⟨lits, hval, hev, hcons⟩ :=
    (dV_iff inst x b hw hb hqx hqbits exs hdeq hdlen).mp hbforced
  refine ⟨⟨lits, hval, hcons⟩, ?_⟩
  intro lits' hval' hcons'
  by_contra hne
  have hω := evalConj_le_one lits' (mkEx 0 x)
  have hcase : evalConj lits' (mkEx 0 x) = 1 - b := by omega
  have hev' : evalConj lits' (mkEx (1 - b) x) = 1 - b := by
    rw [evalConj_mkEx_congr lits' (1 - b) 0 x]; exact hcase
  have hother : conjDecideVal (extInst inst (mkEx (1 - b) x)) ≠ 0 :=
    (dV_iff inst x (1 - b) hw (by omega) hqx hqbits exs hdeq hdlen).mpr ⟨lits', hval', hev', hcons'⟩
  exact hother hobforced

/-- The converse direction's content: unanimity forces both extended calls to their expected
verdicts. -/
private theorem forced_of_unanimous (inst x b : ℕ) (hw : WFBits inst) (hb : b ≤ 1)
    (hqx : IsList x (readK inst)) (hqbits : ∀ j, headL (peel x j) ≤ 1)
    (exs : List ℕ) (hdeq : readData inst = encodeList exs) (hdlen : exs.length = readM inst)
    (hcons : ExistsConsistentConj inst exs)
    (hunanim : ∀ lits, (∀ r ∈ lits, litJ r < readK inst) → ConsistentConj lits exs →
      evalConj lits (mkEx 0 x) = b) :
    conjDecideVal (extInst inst (mkEx b x)) ≠ 0 ∧
      conjDecideVal (extInst inst (mkEx (1 - b) x)) = 0 := by
  obtain ⟨lits, hval, hconsD⟩ := hcons
  have hev0 : evalConj lits (mkEx 0 x) = b := hunanim lits hval hconsD
  have hevb : evalConj lits (mkEx b x) = b := by
    rw [evalConj_mkEx_congr lits b 0 x]; exact hev0
  have hbforced : conjDecideVal (extInst inst (mkEx b x)) ≠ 0 :=
    (dV_iff inst x b hw hb hqx hqbits exs hdeq hdlen).mpr ⟨lits, hval, hevb, hconsD⟩
  refine ⟨hbforced, ?_⟩
  by_contra hobforced
  obtain ⟨lits'', hval'', hev'', hcons''⟩ :=
    (dV_iff inst x (1 - b) hw (by omega) hqx hqbits exs hdeq hdlen).mp hobforced
  have hev0' : evalConj lits'' (mkEx 0 x) = 1 - b := by
    rw [evalConj_mkEx_congr lits'' 0 (1 - b) x]; exact hev''
  have := hunanim lits'' hval'' hcons''
  omega

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

/-- **The four reachable states of the two decisions**, both always bits. -/
private theorem forced_cases (inst x : ℕ) :
    (d0V inst x = 0 ∧ d1V inst x = 0 ∧ forcedFlagV inst x = 0 ∧ forcedLabelV inst x = 0) ∨
    (d0V inst x = 0 ∧ d1V inst x = 1 ∧ forcedFlagV inst x = 1 ∧ forcedLabelV inst x = 1) ∨
    (d0V inst x = 1 ∧ d1V inst x = 0 ∧ forcedFlagV inst x = 1 ∧ forcedLabelV inst x = 0) ∨
    (d0V inst x = 1 ∧ d1V inst x = 1 ∧ forcedFlagV inst x = 0 ∧ forcedLabelV inst x = 0) := by
  have hd0 : d0V inst x ≤ 1 := conjDecideVal_le_one _
  have hd1 : d1V inst x ≤ 1 := conjDecideVal_le_one _
  rcases (by omega : d0V inst x = 0 ∨ d0V inst x = 1) with h0 | h0 <;>
    rcases (by omega : d1V inst x = 0 ∨ d1V inst x = 1) with h1 | h1
  · exact Or.inl ⟨h0, h1, by simp only [forcedFlagV, h0, h1]; decide,
      by simp only [forcedLabelV, forcedFlagV, h0, h1]; decide⟩
  · exact Or.inr (Or.inl ⟨h0, h1, by simp only [forcedFlagV, h0, h1]; decide,
      by simp only [forcedLabelV, forcedFlagV, h0, h1]; decide⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨h0, h1, by simp only [forcedFlagV, h0, h1]; decide,
      by simp only [forcedLabelV, forcedFlagV, h0, h1]; decide⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨h0, h1, by simp only [forcedFlagV, h0, h1]; decide,
      by simp only [forcedLabelV, forcedFlagV, h0, h1]; decide⟩))

/-- **`conj_forced_iff`.** `forcedVal inst x` reads off `⟨1, b⟩` exactly when the version space is
nonempty and unanimous on `b` at the query point. -/
theorem conj_forced_iff (inst x : ℕ) (hw : WFBits inst)
    (hqx : IsList x (readK inst)) (hqbits : ∀ j, headL (peel x j) ≤ 1)
    (exs : List ℕ) (hdeq : readData inst = encodeList exs) (hdlen : exs.length = readM inst)
    (b : ℕ) (hb : b ≤ 1) :
    forcedVal inst x = Nat.pair 1 b
      ↔ ExistsConsistentConj inst exs ∧
        ∀ lits, (∀ r ∈ lits, litJ r < readK inst) → ConsistentConj lits exs →
          evalConj lits (mkEx 0 x) = b := by
  constructor
  · intro heq
    rw [val_cForced] at heq
    rcases forced_cases inst x with ⟨h0, h1, hf, hl⟩ | ⟨h0, h1, hf, hl⟩ | ⟨h0, h1, hf, hl⟩ |
      ⟨h0, h1, hf, hl⟩ <;> rw [hf, hl] at heq
    · obtain ⟨hcontra, -⟩ := pair_inj' heq; omega
    · obtain ⟨-, hbeq⟩ := pair_inj' heq
      subst hbeq
      exact forced_core inst x 1 hw (by omega) hqx hqbits exs hdeq hdlen
        (by unfold d1V at h1; omega) (by unfold d0V at h0; simpa using h0)
    · obtain ⟨-, hbeq⟩ := pair_inj' heq
      subst hbeq
      exact forced_core inst x 0 hw (by omega) hqx hqbits exs hdeq hdlen
        (by unfold d0V at h0; omega) (by unfold d1V at h1; simpa using h1)
    · obtain ⟨hcontra, -⟩ := pair_inj' heq; omega
  · rintro ⟨hcons, hunanim⟩
    obtain ⟨hbforced, hobforced⟩ :=
      forced_of_unanimous inst x b hw hb hqx hqbits exs hdeq hdlen hcons hunanim
    rw [val_cForced]
    have hd0 : d0V inst x ≤ 1 := conjDecideVal_le_one _
    have hd1 : d1V inst x ≤ 1 := conjDecideVal_le_one _
    rcases (by omega : b = 0 ∨ b = 1) with rfl | rfl
    · have hz0 : d0V inst x ≠ 0 := hbforced
      have hz1 : d1V inst x = 0 := hobforced
      have hz0' : d0V inst x = 1 := by omega
      simp only [forcedFlagV, forcedLabelV, hz0', hz1]; decide
    · have hz1 : d1V inst x ≠ 0 := hbforced
      have hz0 : d0V inst x = 0 := hobforced
      have hz1' : d1V inst x = 1 := by omega
      simp only [forcedFlagV, forcedLabelV, hz0, hz1']; decide

/-- **`conj_split_iff`.** Both extended decisions succeed exactly when two distinct valid consistent
literal sets predict the two different bits at the query point. -/
theorem conj_split_iff (inst x : ℕ) (hw : WFBits inst)
    (hqx : IsList x (readK inst)) (hqbits : ∀ j, headL (peel x j) ≤ 1)
    (exs : List ℕ) (hdeq : readData inst = encodeList exs) (hdlen : exs.length = readM inst) :
    d0V inst x ≠ 0 ∧ d1V inst x ≠ 0 ↔
      ∃ lits0 lits1, (∀ r ∈ lits0, litJ r < readK inst) ∧ ConsistentConj lits0 exs ∧
        (∀ r ∈ lits1, litJ r < readK inst) ∧ ConsistentConj lits1 exs ∧
        evalConj lits0 (mkEx 0 x) = 0 ∧ evalConj lits1 (mkEx 0 x) = 1 := by
  unfold d0V d1V
  rw [dV_iff inst x 0 hw (by omega) hqx hqbits exs hdeq hdlen,
    dV_iff inst x 1 hw (by omega) hqx hqbits exs hdeq hdlen]
  constructor
  · rintro ⟨⟨lits0, hval0, hev0, hcons0⟩, ⟨lits1, hval1, hev1, hcons1⟩⟩
    refine ⟨lits0, lits1, hval0, hcons0, hval1, hcons1, hev0, ?_⟩
    rw [← evalConj_mkEx_congr lits1 1 0 x]; exact hev1
  · rintro ⟨lits0, lits1, hval0, hcons0, hval1, hcons1, hev0, hev1⟩
    refine ⟨⟨lits0, hval0, hev0, hcons0⟩, ⟨lits1, hval1, ?_, hcons1⟩⟩
    rw [evalConj_mkEx_congr lits1 1 0 x]; exact hev1

/-! ### `cForced`'s native cost

Two extended `cConjSolve` calls at `readM inst + 1` examples with `readK inst` unchanged
(`tc_cConjSolve_raw` instantiated at each, via `readK_extInst`/`readM_extInst`), plus the `O(1)`
wiring and the forced-symbol read-off's own `O(1)` bit logic. -/

private theorem tc_cN_le (n x : ℕ) : tc cN (Nat.pair n x) ≤ 3 := by simp [cN, tc_left]
private theorem tc_cX_le (n x : ℕ) : tc cX (Nat.pair n x) ≤ 3 := by simp [cX, tc_right]
private theorem tc_cReadDataC_le (X : ℕ) : tc cReadDataC X ≤ 5 := by
  simp only [cReadDataC, tc_comp, tc_right]; omega
private theorem tc_cReadKP_le (n x : ℕ) : tc cReadKP (Nat.pair n x) ≤ 10 := by
  have := tc_cN_le n x; simp only [cReadKP, tc_comp, cReadK, tc_left]; omega
private theorem tc_cReadMP_le (n x : ℕ) : tc cReadMP (Nat.pair n x) ≤ 10 := by
  have := tc_cN_le n x; simp only [cReadMP, tc_comp, cReadM, tc_left, tc_right]; omega
private theorem tc_cReadDataP_le (n x : ℕ) : tc cReadDataP (Nat.pair n x) ≤ 15 := by
  have h1 := tc_cN_le n x
  have h2 := tc_cReadDataC_le (val cN (Nat.pair n x))
  simp only [cReadDataP, tc_comp]
  omega
private theorem tc_cMkExB_le (b n x : ℕ) (hb : b ≤ 1) : tc (cMkExB b) (Nat.pair n x) ≤ 10 := by
  have h1 := tc_constCode_le b (Nat.pair n x)
  have h2 := tc_cX_le n x
  simp only [cMkExB, tc_pair]
  omega
private theorem tc_cExtInstB_le (b n x : ℕ) (hb : b ≤ 1) : tc (cExtInstB b) (Nat.pair n x) ≤ 60 := by
  have h1 := tc_cReadKP_le n x
  have h2 := tc_cReadMP_le n x
  have h3 : tc succ (val cReadMP (Nat.pair n x)) ≤ 1 := by simp
  have h4 := tc_constCode_le 1 (Nat.pair n x)
  have h5 := tc_cMkExB_le b n x hb
  have h6 := tc_cReadDataP_le n x
  simp only [cExtInstB, tc_pair, tc_comp]
  omega

/-- **`cD01`'s native cost.** Two fresh `cConjSolve` calls, each at `readK inst` features and
`readM inst + 1` examples. -/
private theorem tc_cD01_le (n x : ℕ) (hw : WFBits n) (hqx : IsList x (readK n))
    (hqbits : ∀ j, headL (peel x j) ≤ 1) :
    tc cD01 (Nat.pair n x)
      ≤ 2 * ((((2 * ((16 * readK n + 1501) * (readM n + 1)) + 16 * readK n + 2001) * readK n
            + 1200) + 1) * (readM n + 1) + 520) + 200 := by
  obtain ⟨exs, hdeq, hdlen, _, _⟩ := hw.2
  have hWF0 : WFBits (extInst n (mkEx 0 x)) :=
    wfbits_extInst n x 0 hw (by omega) hqx hqbits exs hdeq hdlen
  have hWF1 : WFBits (extInst n (mkEx 1 x)) :=
    wfbits_extInst n x 1 hw (by omega) hqx hqbits exs hdeq hdlen
  have hk0 : readK (extInst n (mkEx 0 x)) = readK n := readK_extInst n (mkEx 0 x)
  have hm0 : readM (extInst n (mkEx 0 x)) = readM n + 1 := readM_extInst n (mkEx 0 x)
  have hk1 : readK (extInst n (mkEx 1 x)) = readK n := readK_extInst n (mkEx 1 x)
  have hm1 : readM (extInst n (mkEx 1 x)) = readM n + 1 := readM_extInst n (mkEx 1 x)
  have hraw0 := tc_cConjSolve_raw (extInst n (mkEx 0 x)) hWF0
  have hraw1 := tc_cConjSolve_raw (extInst n (mkEx 1 x)) hWF1
  rw [hk0, hm0] at hraw0
  rw [hk1, hm1] at hraw1
  have he0 := tc_cExtInstB_le 0 n x (by omega)
  have he1 := tc_cExtInstB_le 1 n x (by omega)
  simp only [cD01, tc_pair, tc_comp, val_cExtInstB]
  omega

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
  have hvNotD1 : val (comp cNot cD1core) (Nat.pair d0 d1) = bitNot d1 := by
    simp [val_comp, val_cNot', hvD1]
  have hNotD0 : tc (comp cNot cD0core) (Nat.pair d0 d1) ≤ 14 := by
    have := hD0
    have hb : val cD0core (Nat.pair d0 d1) ≤ 1 := by rw [hvD0]; exact h0
    have := tc_cNot_bit hb
    simp only [tc_comp]; omega
  have hvNotD0 : val (comp cNot cD0core) (Nat.pair d0 d1) = bitNot d0 := by
    simp [val_comp, val_cNot', hvD0]
  have hAnd1 : tc cAnd (val (pair cD0core (comp cNot cD1core)) (Nat.pair d0 d1)) ≤ 204 := by
    rw [val_pair, hvD0, hvNotD1]
    exact tc_cAnd_bit h0 (bitNot_le_one _)
  have hPair1 : tc (pair cD0core (comp cNot cD1core)) (Nat.pair d0 d1) ≤ 16 := by
    have := hD0; have := hNotD1; simp only [tc_pair]; omega
  have hBranch1 : tc (comp cAnd (pair cD0core (comp cNot cD1core))) (Nat.pair d0 d1) ≤ 221 := by
    have := hPair1; have := hAnd1; simp only [tc_comp]; omega
  have hvBranch1 : val (comp cAnd (pair cD0core (comp cNot cD1core))) (Nat.pair d0 d1)
      = bitAnd d0 (bitNot d1) := by
    simp [val_comp, val_pair, val_cAnd', hvD0, hvNotD1]
  have hAnd2 : tc cAnd (val (pair cD1core (comp cNot cD0core)) (Nat.pair d0 d1)) ≤ 204 := by
    rw [val_pair, hvD1, hvNotD0]
    exact tc_cAnd_bit h1 (bitNot_le_one _)
  have hPair2 : tc (pair cD1core (comp cNot cD0core)) (Nat.pair d0 d1) ≤ 16 := by
    have := hD1; have := hNotD0; simp only [tc_pair]; omega
  have hBranch2 : tc (comp cAnd (pair cD1core (comp cNot cD0core))) (Nat.pair d0 d1) ≤ 221 := by
    have := hPair2; have := hAnd2; simp only [tc_comp]; omega
  have hvBranch2 : val (comp cAnd (pair cD1core (comp cNot cD0core))) (Nat.pair d0 d1)
      = bitAnd d1 (bitNot d0) := by
    simp [val_comp, val_pair, val_cAnd', hvD1, hvNotD0]
  have hPairBoth : tc (pair (comp cAnd (pair cD0core (comp cNot cD1core)))
      (comp cAnd (pair cD1core (comp cNot cD0core)))) (Nat.pair d0 d1) ≤ 443 := by
    have := hBranch1; have := hBranch2; simp only [tc_pair]; omega
  have hOr : tc cOr (val (pair (comp cAnd (pair cD0core (comp cNot cD1core)))
      (comp cAnd (pair cD1core (comp cNot cD0core)))) (Nat.pair d0 d1)) ≤ 21 := by
    rw [val_pair, hvBranch1, hvBranch2]
    exact tc_cOr_bit (bitAnd_le_one _ _) (bitAnd_le_one _ _)
  have hFlag : tc cFlagCore (Nat.pair d0 d1) ≤ 465 := by
    have := hPairBoth; have := hOr; simp only [cFlagCore, tc_comp]; omega
  have hvFlag : val cFlagCore (Nat.pair d0 d1)
      = bitOr (bitAnd d0 (bitNot d1)) (bitAnd d1 (bitNot d0)) := by
    simp only [cFlagCore, val_comp, val_pair, val_cOr', hvBranch1, hvBranch2]
  have hAnd3 : tc cAnd (val (pair cFlagCore cD1core) (Nat.pair d0 d1)) ≤ 204 := by
    rw [val_pair, hvFlag, hvD1]
    exact tc_cAnd_bit (bitOr_le_one _ _) h1
  have hPair3 : tc (pair cFlagCore cD1core) (Nat.pair d0 d1) ≤ 467 := by
    have := hFlag; have := hD1; simp only [tc_pair]; omega
  have hLabel : tc cLabelCore (Nat.pair d0 d1) ≤ 672 := by
    have := hPair3; have := hAnd3; simp only [cLabelCore, tc_comp]; omega
  simp only [cForcedCore, tc_pair]
  omega

private theorem rfindFree_cForced : RfindFree cForced := by repeat constructor

/-- **`cForced`'s native cost** — an EXPLICIT polynomial in `readK inst` and `readM inst`. -/
theorem tc_forced_raw (inst x : ℕ) (hw : WFBits inst) (hqx : IsList x (readK inst))
    (hqbits : ∀ j, headL (peel x j) ≤ 1) :
    tc cForced (Nat.pair inst x)
      ≤ 2 * ((((2 * ((16 * readK inst + 1501) * (readM inst + 1)) + 16 * readK inst + 2001)
            * readK inst + 1200) + 1) * (readM inst + 1) + 520) + 200 + 1300 := by
  have hd01 := tc_cD01_le inst x hw hqx hqbits
  have hcorepre : val cD01 (Nat.pair inst x)
      = Nat.pair (conjDecideVal (extInst inst (mkEx 0 x)))
          (conjDecideVal (extInst inst (mkEx 1 x))) :=
    val_cD01 inst x
  have hd0b : conjDecideVal (extInst inst (mkEx 0 x)) ≤ 1 := conjDecideVal_le_one _
  have hd1b : conjDecideVal (extInst inst (mkEx 1 x)) ≤ 1 := conjDecideVal_le_one _
  have hcore : tc cForcedCore (val cD01 (Nat.pair inst x)) ≤ 1200 := by
    rw [hcorepre]; exact tc_cForcedCore_le _ _ hd0b hd1b
  simp only [cForced, tc_comp]
  omega

/-- **The forced-symbol predictor's well-formed domain.** -/
def ForcedWF (p : ℕ) : Prop :=
  WFBits p.unpair.1 ∧ IsList p.unpair.2 (readK p.unpair.1) ∧ ∀ j, headL (peel p.unpair.2 j) ≤ 1

set_option maxRecDepth 4000 in
/-- **`polyTime_forced`.** The two-consistency-call forced-symbol predictor is poly-time on the
well-formed domain: `cForced` computes it, its native cost is `PolyBoundedOn` (via `tc_forced_raw`
and `polyTime_conjSolve`'s own poly-bit closure applied twice), and its output is a bit pair,
hence trivially poly-bit. -/
theorem polyTime_forced : PolyTimeOn ForcedWF (fun p => forcedVal p.unpair.1 p.unpair.2) := by
  refine ⟨cForced, rfindFree_cForced, fun p _ => ?_, ?_, ?_⟩
  · change val cForced p = forcedVal p.unpair.1 p.unpair.2
    unfold forcedVal
    rw [Nat.pair_unpair]
  · refine ⟨20000, 4, fun p hp => ?_⟩
    obtain ⟨n, x, rfl⟩ : ∃ n x, p = Nat.pair n x :=
      ⟨p.unpair.1, p.unpair.2, (Nat.pair_unpair p).symm⟩
    obtain ⟨hw, hqx, hqbits⟩ := hp
    simp only [Nat.unpair_pair] at hw hqx hqbits
    have hraw := tc_forced_raw n x hw hqx hqbits
    have hwf : WF n := hw.1
    have hk : readK n ≤ Nat.size n := readK_le_size n hwf
    have hm : readM n ≤ Nat.size n := readM_le_size n hwf
    have hsizeN : Nat.size n ≤ Nat.size (Nat.pair n x) := Nat.size_le_size (left_le_pair n x)
    set S := Nat.size (Nat.pair n x) with hSdef
    have hk1 : readK n + 1 ≤ S + 1 := by omega
    have hm1 : readM n + 1 ≤ S + 1 := by omega
    have hA : 16 * readK n + 1501 ≤ 1517 * (S + 1) := by omega
    have hB : (16 * readK n + 1501) * (readM n + 1) ≤ 1517 * (S + 1) * (S + 1) := by
      have h1 : (16 * readK n + 1501) * (readM n + 1) ≤ (1517 * (S + 1)) * (readM n + 1) :=
        Nat.mul_le_mul_right _ hA
      have h2 : (1517 * (S + 1)) * (readM n + 1) ≤ (1517 * (S + 1)) * (S + 1) :=
        Nat.mul_le_mul_left _ (by omega)
      omega
    have hC : 2 * ((16 * readK n + 1501) * (readM n + 1)) + 16 * readK n + 2001
        ≤ 5100 * (S + 1) ^ 2 := by nlinarith [hB]
    have hD : (2 * ((16 * readK n + 1501) * (readM n + 1)) + 16 * readK n + 2001) * readK n
        ≤ 5100 * (S + 1) ^ 2 * (S + 1) := by
      have h1 : (2 * ((16 * readK n + 1501) * (readM n + 1)) + 16 * readK n + 2001) * readK n
          ≤ (5100 * (S + 1) ^ 2) * readK n := Nat.mul_le_mul_right _ hC
      have h2 : (5100 * (S + 1) ^ 2) * readK n ≤ (5100 * (S + 1) ^ 2) * (S + 1) :=
        Nat.mul_le_mul_left _ (by omega)
      omega
    have hE : ((2 * ((16 * readK n + 1501) * (readM n + 1)) + 16 * readK n + 2001) * readK n
          + 1200) + 1 ≤ 6000 * (S + 1) ^ 3 := by nlinarith [hD]
    have hF : (((2 * ((16 * readK n + 1501) * (readM n + 1)) + 16 * readK n + 2001) * readK n
          + 1200) + 1) * (readM n + 1)
        ≤ 6000 * (S + 1) ^ 3 * (S + 1) := by
      have h1 : (((2 * ((16 * readK n + 1501) * (readM n + 1)) + 16 * readK n + 2001) * readK n
            + 1200) + 1) * (readM n + 1)
          ≤ (6000 * (S + 1) ^ 3) * (readM n + 1) := Nat.mul_le_mul_right _ hE
      have h2 : (6000 * (S + 1) ^ 3) * (readM n + 1) ≤ (6000 * (S + 1) ^ 3) * (S + 1) :=
        Nat.mul_le_mul_left _ (by omega)
      omega
    have hpow : (S + 1) ^ 3 * (S + 1) = (S + 1) ^ 4 := by ring
    nlinarith [hraw, hF, hpow]
  · refine ⟨3, 0, fun p _ => ?_⟩
    change Nat.size (forcedVal p.unpair.1 p.unpair.2) ≤ 3 * (Nat.size p + 1) ^ 0 + 3
    have h1 : forcedFlagV p.unpair.1 p.unpair.2 ≤ 1 := bitOr_le_one _ _
    have h2 : forcedLabelV p.unpair.1 p.unpair.2 ≤ 1 := bitAnd_le_one _ _
    have hval3 : forcedVal p.unpair.1 p.unpair.2 ≤ 3 := by
      rw [val_cForced]
      exact le_trans (pair_mono' h1 h2) (by decide)
    have hsize : Nat.size (forcedVal p.unpair.1 p.unpair.2) ≤ 2 :=
      le_trans (Nat.size_le_size hval3) (by decide)
    omega

/-! ## Axiom-cleanliness guards (CI-enforced)

Each guard **fails `lake build`** if the theorem's axiom set ever drifts from the standard
`[propext, Classical.choice, Quot.sound]`. -/

/-- info: 'Conj.dV_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms dV_iff

/-- info: 'Conj.conj_empty_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms conj_empty_iff

/-- info: 'Conj.conj_forced_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms conj_forced_iff

/-- info: 'Conj.conj_split_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms conj_split_iff

/-- info: 'Conj.tc_forced_raw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms tc_forced_raw

/-- info: 'Conj.polyTime_forced' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms polyTime_forced

end Conj
