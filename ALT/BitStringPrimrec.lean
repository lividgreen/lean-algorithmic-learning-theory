/-
Copyright (c) 2026 Mykola Palamarchuk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mykola Palamarchuk
-/
module

public import ALT.PrefixMachine

-- Formal-check file, not Mathlib-destined: opt out of the house-style header linter.
set_option linter.style.header false

/-!
# The bit-string layer's computability, and `pfy`'s uniform partial recursiveness

Provenance: [Discovery] §1.1 and FV-20, over the universal prefix machine `PrefixMachine.pfy`.
Extends `ALT/PrefixMachine.lean` (`bitsToNat`, `natToBits`, `foldStep`, `newlyHalting`,
`acceptedList`, `pfy`).

## What this establishes

* `natToBits`, `bitsToNat` are `Primrec`: a fuel-bounded reformulation of `natToBits` fitting
  `Primrec.nat_iterate`, bridged to the well-founded definition by `natToBitsFuel_eq`.
* The prefix relation on bit-strings is a `PrimrecRel`.
* `foldStep`, `newlyHalting`, `acceptedList` are `Primrec₂`.
* **`pfy_partrec`**: `pfy` is partial recursive, uniformly in the machine — the open boundary
  `ALT/PrefixMachine.lean` flags at `pfy`'s own definition.

## What this does NOT establish (flagged)

* The algorithmic probability `QB`'s lower-semicomputability and the coding theorem itself are not
  attempted here.
-/


@[expose] public section

namespace PrefixMachine

open Nat.Partrec Nat.Partrec.Code AdditiveComplexity CodeEvalLaws KolmogorovComplexity

/-! ## `natToBits`, `bitsToNat` are primitive recursive -/

/-- One step of peeling `natToBits`'s low bit: idle once the state has bottomed out at `0`,
otherwise move to the smaller state and cons the peeled bit onto the accumulator. -/
def natToBitsStep (st : ℕ × List Bool) : ℕ × List Bool :=
  if st.1 + 1 < 2 then st else ((st.1 + 1) / 2 - 1, decide ((st.1 + 1) % 2 = 1) :: st.2)

/-- `natToBits` by fuel: peel the low bit of `m + 1` and cons it, `fuel` times, over the state
`(m, acc)` starting at `(n, [])`. -/
def natToBitsFuel (fuel n : ℕ) : List Bool :=
  (natToBitsStep^[fuel] (n, [])).2

/-- Once the state has bottomed out at `0`, every further step is idle. -/
private theorem natToBitsStep_idle_zero (acc : List Bool) :
    ∀ fuel : ℕ, natToBitsStep^[fuel] (0, acc) = (0, acc)
  | 0 => rfl
  | fuel + 1 => by
      rw [Function.iterate_succ_apply', natToBitsStep_idle_zero acc fuel]
      simp [natToBitsStep]

/-- With any starting accumulator, and fuel exceeding the state, peeling reaches `0` and the
accumulator gains exactly `natToBits` of the starting state, prepended. -/
private theorem natToBitsStep_iterate_acc (n fuel : ℕ) (acc : List Bool) (h : n < fuel) :
    natToBitsStep^[fuel] (n, acc) = (0, natToBits n ++ acc) := by
  induction n using natToBits.induct generalizing fuel acc with
  | case1 n hn =>
      have hn0 : n = 0 := by omega
      subst hn0
      rw [natToBits_zero, List.nil_append]
      exact natToBitsStep_idle_zero acc fuel
  | case2 n hn ih =>
      obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show fuel ≠ 0 by omega)
      rw [Function.iterate_succ_apply]
      have hstep : natToBitsStep (n, acc)
          = ((n + 1) / 2 - 1, decide ((n + 1) % 2 = 1) :: acc) := by
        simp [natToBitsStep, hn]
      rw [hstep]
      have hk : (n + 1) / 2 - 1 < k := by omega
      rw [ih k (decide ((n + 1) % 2 = 1) :: acc) hk]
      have hnb : natToBits n = natToBits ((n + 1) / 2 - 1) ++ [decide ((n + 1) % 2 = 1)] := by
        conv_lhs => rw [natToBits]
        simp [hn]
      rw [hnb, List.append_assoc]
      simp

theorem natToBitsFuel_eq (n : ℕ) : natToBitsFuel (n + 1) n = natToBits n := by
  unfold natToBitsFuel
  rw [natToBitsStep_iterate_acc n (n + 1) [] (by omega), List.append_nil]

private theorem primrec_natToBitsStep : Primrec natToBitsStep := by
  have hc : Primrec fun st : ℕ × List Bool => decide (st.1 + 1 < 2) :=
    Primrec.nat_lt.decide.comp (Primrec.succ.comp Primrec.fst) (Primrec.const 2)
  have hdiv : Primrec fun st : ℕ × List Bool => (st.1 + 1) / 2 - 1 :=
    Primrec.nat_sub.comp
      (Primrec.nat_div.comp (Primrec.succ.comp Primrec.fst) (Primrec.const 2))
      (Primrec.const 1)
  have hbit : Primrec fun st : ℕ × List Bool => decide ((st.1 + 1) % 2 = 1) :: st.2 :=
    Primrec.list_cons.comp
      (Primrec.eq.decide.comp
        (Primrec.nat_mod.comp (Primrec.succ.comp Primrec.fst) (Primrec.const 2))
        (Primrec.const 1))
      Primrec.snd
  have hfalse : Primrec fun st : ℕ × List Bool =>
      ((st.1 + 1) / 2 - 1, decide ((st.1 + 1) % 2 = 1) :: st.2) := hdiv.pair hbit
  have := Primrec.cond hc Primrec.id hfalse
  refine this.of_eq fun st => ?_
  unfold natToBitsStep
  simp only [id]
  rw [Bool.cond_decide]

private theorem primrec₂_natToBitsFuel : Primrec₂ natToBitsFuel := by
  have hh : Primrec₂ fun (_ : ℕ × ℕ) (x : ℕ × List Bool) => natToBitsStep x :=
    primrec_natToBitsStep.comp Primrec.snd
  have := Primrec.nat_iterate (α := ℕ × ℕ) Primrec.fst
    (Primrec.snd.pair (Primrec.const ([] : List Bool))) hh
  exact (Primrec.snd.comp this).of_eq fun p => rfl

theorem primrec_natToBits : Primrec natToBits := by
  have := primrec₂_natToBitsFuel.comp Primrec.succ Primrec.id
  exact this.of_eq natToBitsFuel_eq

theorem primrec_bitsToNat : Primrec bitsToNat := by
  have hstep : Primrec₂ fun (acc : ℕ) (b : Bool) => 2 * acc + b.toNat :=
    Primrec.nat_add.comp
      (Primrec.nat_mul.comp (Primrec.const 2) Primrec.fst)
      ((Primrec.dom_bool Bool.toNat).comp Primrec.snd)
  have hh : Primrec₂ fun (_ : List Bool) (sb : ℕ × Bool) => 2 * sb.1 + sb.2.toNat :=
    Primrec.comp₂ hstep Primrec₂.right
  have hfold : Primrec fun p : List Bool => p.foldl (fun acc b => 2 * acc + b.toNat) 1 :=
    Primrec.list_foldl Primrec.id (Primrec.const 1) hh
  exact (Primrec.nat_sub.comp hfold (Primrec.const 1)).of_eq fun p => by
    simp [bitsToNat]

/-! ## The prefix relation, `foldStep`, `newlyHalting`, `acceptedList` -/

/-- **Prefix of one bit-string by another**: `p <+: q ↔ List.take p.length q = p`. -/
theorem primrec_isPrefix : PrimrecRel fun p q : List Bool => p <+: q :=
  (Primrec.eq.comp₂ (Primrec₂.left)
      (Primrec₂.comp₂ Primrec.list_take (Primrec.list_length.comp₂ Primrec₂.left)
        Primrec₂.right)).of_eq
    fun _ _ => (List.prefix_iff_eq_take).symm

/-- The relation `foldStep` tests: some earlier-accepted input is comparable, as a bit-string, to
the candidate. -/
private theorem primrec_foldStepRel :
    PrimrecRel fun m n : ℕ => natToBits m <+: natToBits n ∨ natToBits n <+: natToBits m := by
  have hA : PrimrecRel fun m n : ℕ => natToBits m <+: natToBits n :=
    primrec_isPrefix.comp₂ (Primrec.comp₂ primrec_natToBits Primrec₂.left)
      (Primrec.comp₂ primrec_natToBits Primrec₂.right)
  have hB : PrimrecRel fun m n : ℕ => natToBits n <+: natToBits m :=
    primrec_isPrefix.comp₂ (Primrec.comp₂ primrec_natToBits Primrec₂.right)
      (Primrec.comp₂ primrec_natToBits Primrec₂.left)
  exact hA.or hB

private theorem primrec₂_foldStep : Primrec₂ foldStep := by
  have hExists : PrimrecRel fun (L : List ℕ) (n : ℕ) =>
      ∃ m ∈ L, natToBits m <+: natToBits n ∨ natToBits n <+: natToBits m :=
    primrec_foldStepRel.exists_mem_list
  exact (Primrec.ite hExists Primrec.fst Primrec.list_concat).of_eq fun p => by
    unfold foldStep
    rfl

private theorem primrec₂_newlyHalting : Primrec₂ newlyHalting := by
  have hf : Primrec fun a : Code × ℕ => List.range (a.2 + 1) :=
    Primrec.list_range.comp (Primrec.succ.comp Primrec.snd)
  have hq1 : Primrec fun p : (Code × ℕ) × ℕ => ((p.1.2 + 1, p.1.1), p.2) :=
    ((Primrec.succ.comp (Primrec.snd.comp Primrec.fst)).pair
      (Primrec.fst.comp Primrec.fst)).pair Primrec.snd
  have hEv1 : Primrec fun p : (Code × ℕ) × ℕ => evaln (p.1.2 + 1) p.1.1 p.2 := by
    have := Nat.Partrec.Code.primrec_evaln.comp hq1
    exact this.of_eq fun p => rfl
  have hq0 : Primrec fun p : (Code × ℕ) × ℕ => ((p.1.2, p.1.1), p.2) :=
    ((Primrec.snd.comp Primrec.fst).pair (Primrec.fst.comp Primrec.fst)).pair Primrec.snd
  have hEv0 : Primrec fun p : (Code × ℕ) × ℕ => evaln p.1.2 p.1.1 p.2 := by
    have := Nat.Partrec.Code.primrec_evaln.comp hq0
    exact this.of_eq fun p => rfl
  have hCond : Primrec fun p : (Code × ℕ) × ℕ =>
      (evaln (p.1.2 + 1) p.1.1 p.2).isSome && !(evaln p.1.2 p.1.1 p.2).isSome :=
    Primrec.and.comp (Primrec.option_isSome.comp hEv1)
      (Primrec.not.comp (Primrec.option_isSome.comp hEv0))
  have hg : Primrec₂ fun (a : Code × ℕ) (n : ℕ) =>
      cond ((evaln (a.2 + 1) a.1 n).isSome && !(evaln a.2 a.1 n).isSome) (some n) none :=
    Primrec.cond hCond (Primrec.option_some.comp Primrec.snd) (Primrec.const none)
  have hres := Primrec.listFilterMap hf hg
  refine hres.of_eq fun a => ?_
  simp only [newlyHalting, ← List.filterMap_eq_filter, Bool.cond_eq_ite, Option.guard]

theorem primrec₂_acceptedList : Primrec₂ acceptedList := by
  have hf' : Primrec fun a : Code × (ℕ × List ℕ) => newlyHalting a.1 a.2.1 :=
    Primrec.comp primrec₂_newlyHalting (Primrec.fst.pair (Primrec.fst.comp Primrec.snd))
  have hg' : Primrec fun a : Code × (ℕ × List ℕ) => a.2.2 :=
    Primrec.snd.comp Primrec.snd
  have hh' : Primrec₂ fun (_ : Code × (ℕ × List ℕ)) (sb : List ℕ × ℕ) => foldStep sb.1 sb.2 :=
    Primrec.comp₂ primrec₂_foldStep Primrec₂.right
  have hfold : Primrec fun a : Code × (ℕ × List ℕ) =>
      (newlyHalting a.1 a.2.1).foldl foldStep a.2.2 :=
    Primrec.list_foldl hf' hg' hh'
  have hfold₂ : Primrec₂ fun (c : Code) (sa : ℕ × List ℕ) =>
      (newlyHalting c sa.1).foldl foldStep sa.2 := hfold
  have := Primrec.nat_rec (f := fun _ : Code => ([] : List ℕ)) (Primrec.const []) hfold₂
  refine this.of_eq fun c s => ?_
  induction s with
  | zero => rfl
  | succ s ih =>
      change (newlyHalting c s).foldl foldStep (Nat.rec [] _ s) = acceptedList c (s + 1)
      rw [ih]
      rfl

/-! ## `pfy` is partial recursive, uniformly in the machine -/

/-- List membership is a `PrimrecRel`. -/
theorem primrec_mem_list : PrimrecRel fun (L : List ℕ) (n : ℕ) => n ∈ L :=
  (Primrec.eq.exists_mem_list).of_eq fun _ n =>
    ⟨fun ⟨_, hm, he⟩ => he ▸ hm, fun h => ⟨n, h, rfl⟩⟩

private theorem primrec₂_acceptedListMem :
    Primrec₂ fun (cn : Code × ℕ) (s : ℕ) => decide (cn.2 ∈ acceptedList cn.1 s) := by
  have hL : Primrec fun p : (Code × ℕ) × ℕ => acceptedList p.1.1 p.2 :=
    Primrec.comp primrec₂_acceptedList (Primrec.fst.comp Primrec.fst |>.pair Primrec.snd)
  have hn0 : Primrec fun p : (Code × ℕ) × ℕ => p.1.2 :=
    Primrec.snd.comp Primrec.fst
  exact (primrec_mem_list.comp hL hn0).decide

open scoped Classical in
/-- Once the state has bottomed out, `Nat.rfind` over acceptance-by-stage reproduces `pfy`'s own
`Nat.find`. -/
private theorem rfind_acceptedList_eq (c : Code) (n : ℕ) :
    Nat.rfind (fun s => Part.some (decide (n ∈ acceptedList c s))) =
      if h : ∃ s, n ∈ acceptedList c s then Part.some (Nat.find h) else Part.none := by
  split
  · rename_i h
    apply Part.eq_some_iff.mpr
    apply Nat.mem_rfind.mpr
    refine ⟨by simp [Nat.find_spec h], fun {m} hm => ?_⟩
    simp only [Part.mem_some_iff]
    exact (decide_eq_false (Nat.find_min h hm)).symm
  · rename_i h
    apply Part.eq_none_iff.mpr
    rintro v hv
    replace hv := Nat.mem_rfind.mp hv
    apply h
    refine ⟨v, ?_⟩
    have := hv.1
    simp only [Part.mem_some_iff] at this
    simpa using this.symm

/-- **`pfy` is `Nat.rfind`-then-`evaln`**, over the stage at which `n` first gets accepted. -/
theorem pfy_eq_bind (c : Code) (n : ℕ) :
    pfy c n = (Nat.rfind fun s => Part.some (decide (n ∈ acceptedList c s))) >>=
      fun s => (evaln s c n : Part ℕ) := by
  change pfy c n =
    (Nat.rfind fun s => Part.some (decide (n ∈ acceptedList c s))).bind
      fun s => (evaln s c n : Part ℕ)
  rw [rfind_acceptedList_eq]
  unfold pfy
  split
  · rename_i h
    rw [Part.bind_some]
    conv_rhs =>
      rw [← Option.some_get (evaln_isSome_of_mem_acceptedList c (Nat.find h) (Nat.find_spec h))]
    rfl
  · rename_i h
    exact (Part.bind_none _).symm

/-- **`pfy` is partial recursive, uniformly in the machine.** -/
theorem pfy_partrec : Partrec₂ fun (c : Code) (n : ℕ) => pfy c n := by
  have hcomp : Computable₂ fun (cn : Code × ℕ) (s : ℕ) => decide (cn.2 ∈ acceptedList cn.1 s) :=
    primrec₂_acceptedListMem.to_comp
  have hpart : Partrec₂ fun (cn : Code × ℕ) (s : ℕ) =>
      Part.some (decide (cn.2 ∈ acceptedList cn.1 s)) :=
    hcomp.partrec₂
  have hrfind : Partrec fun cn : Code × ℕ =>
      Nat.rfind fun s => Part.some (decide (cn.2 ∈ acceptedList cn.1 s)) :=
    Partrec.rfind hpart
  have hevalnc : Computable fun p : (Code × ℕ) × ℕ => evaln p.2 p.1.1 p.1.2 := by
    have hq : Primrec fun p : (Code × ℕ) × ℕ => ((p.2, p.1.1), p.1.2) :=
      (Primrec.snd.pair (Primrec.fst.comp Primrec.fst)).pair (Primrec.snd.comp Primrec.fst)
    have := Primrec.comp Nat.Partrec.Code.primrec_evaln hq
    exact this.to_comp.of_eq fun p => rfl
  have hg : Partrec₂ fun (cn : Code × ℕ) (s : ℕ) => (evaln s cn.1 cn.2 : Part ℕ) :=
    Computable.ofOption hevalnc
  have hbind : Partrec fun cn : Code × ℕ =>
      (Nat.rfind fun s => Part.some (decide (cn.2 ∈ acceptedList cn.1 s))) >>=
        fun s => (evaln s cn.1 cn.2 : Part ℕ) :=
    Partrec.bind hrfind hg
  exact hbind.of_eq fun cn => (pfy_eq_bind cn.1 cn.2).symm

end PrefixMachine
