/-
Copyright (c) 2026 Mykola Palamarchuk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mykola Palamarchuk
-/
import ALT.BitStringPrimrec
import ALT.CodingTheoremWeak

-- Formal-check file, not Mathlib-destined: opt out of the house-style header linter.
set_option linter.style.header false

/-!
# `QB`'s lower-semicomputability ([Discovery] §1.1, FV-21)

Provenance: [Discovery] §1.1 and FV-21, over the universal prefix machine `PrefixMachine.KB`, the
algorithmic probability `PrefixMachine.QB`, and the bit-string computability layer of
`ALT/BitStringPrimrec.lean`. Extends `ALT/CodingTheoremWeak.lean` and `ALT/BitStringPrimrec.lean`.

## What this establishes

* `primrec_elen`: the additive AST program length `AdditiveComplexity.elen` is `Primrec`.
* `QB_lsc`: the algorithmic probability `QB` is lower-semicomputable, via `QBApprox`, a computable
  dyadic approximation over the level-`t` accepted-by-stage bit-string layer.

## What this does NOT establish (flagged)

The coding theorem itself (`coding_theorem_weak`, `coding_theorem_weak_QB`) is established in
`ALT/CodingTheoremDecoder.lean`, over `QB_lsc` here. The `O(1)` coding theorem and the online
Kraft–Chaitin invariant it needs are not attempted in either module.
-/

namespace PrefixMachine

open Nat.Partrec Nat.Partrec.Code AdditiveComplexity CodeEvalLaws KolmogorovComplexity

/-! ## The additive AST program length is primitive recursive -/

theorem primrec_elen : Primrec elen := by
  have hpr : Primrec fun a : Code × Code × Code × ℕ × ℕ => 3 + a.2.2.2.1 + a.2.2.2.2 :=
    Primrec.nat_add.comp
      (Primrec.nat_add.comp (Primrec.const 3)
        (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))
      (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
  have hrf : Primrec fun a : Code × Code × ℕ => 3 + a.2.2 :=
    Primrec.nat_add.comp (Primrec.const 3) (Primrec.snd.comp Primrec.snd)
  have hF := Nat.Partrec.Code.primrec_recOn (α := Code) (σ := ℕ) (c := id) Primrec.id
    (z := fun _ : Code => (3 : ℕ)) (Primrec.const 3)
    (s := fun _ : Code => (3 : ℕ)) (Primrec.const 3)
    (l := fun _ : Code => (3 : ℕ)) (Primrec.const 3)
    (r := fun _ : Code => (3 : ℕ)) (Primrec.const 3)
    (pr := fun (_ : Code) (_ _ : Code) (hf hg : ℕ) => 3 + hf + hg) hpr
    (co := fun (_ : Code) (_ _ : Code) (hf hg : ℕ) => 3 + hf + hg) hpr
    (pc := fun (_ : Code) (_ _ : Code) (hf hg : ℕ) => 3 + hf + hg) hpr
    (rf := fun (_ : Code) (_ : Code) (hf : ℕ) => 3 + hf) hrf
  refine hF.of_eq fun a => ?_
  induction a with
  | zero => rfl
  | succ => rfl
  | left => rfl
  | right => rfl
  | pair cf cg ihf ihg =>
      simp only [id_eq] at ihf ihg ⊢
      rw [ihf, ihg, E_len_pair]
  | comp cf cg ihf ihg =>
      simp only [id_eq] at ihf ihg ⊢
      rw [ihf, ihg, E_len_comp]
  | prec cf cg ihf ihg =>
      simp only [id_eq] at ihf ihg ⊢
      rw [ihf, ihg]
      simp only [elen, E, List.length_append, List.length_cons, List.length_nil]
  | rfind' cf ihf =>
      simp only [id_eq] at ihf ⊢
      rw [ihf]
      simp only [elen, E, List.length_append, List.length_cons, List.length_nil]

/-! ## `QB_lsc`: the dyadic approximation -/

/-- Bridge a bounded `Finset.range` sum to the `List.range`-and-`sum` form Primrec combinators
build on. -/
private theorem finsetSum_range_eq_listSum (n : ℕ) (f : ℕ → ℕ) :
    ∑ i ∈ Finset.range n, f i = ((List.range n).map f).sum := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih, List.range_succ, List.map_append, List.sum_append]
      simp

/-- Sum a `Primrec`-shaped `List ℕ` — the pattern behind every bounded sum below. -/
private theorem primrec_list_sum {α : Type*} [Primcodable α] {f : α → List ℕ} (hf : Primrec f) :
    Primrec fun a => (f a).sum :=
  (Primrec.list_foldr hf (Primrec.const 0)
      (Primrec.nat_add.comp (Primrec.fst.comp Primrec.snd)
        (Primrec.snd.comp Primrec.snd)).to₂).of_eq
    fun a => by simp [List.sum_eq_foldr]

/-- Division distributes over a `Finset` sum. -/
private theorem sum_div_eq {ι : Type*} (s : Finset ι) (f : ι → ℝ) (a : ℝ) :
    (∑ i ∈ s, f i) / a = ∑ i ∈ s, f i / a := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert i s' hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, add_div, ih]

/-- The single term of `QBApprox`'s double sum: the Kraft weight, at stage `t`, of the description
`(Denumerable.ofNat Code k, natToBits n)` — nonzero exactly when it fits in `t` bits and decodes to
`x` by stage `t`. -/
def QBApproxTerm (t x k n : ℕ) : ℕ :=
  let c := Denumerable.ofNat Code k
  if elen c + (natToBits n).length ≤ t ∧ n ∈ acceptedList c t ∧ evaln t c n = some x
  then 2 ^ (t - (elen c + (natToBits n).length)) else 0

/-- **The dyadic approximation to `QB`**: at stage `t`, the total weight of every description of
total length at most `t` that decodes to `x` within `t` steps. -/
def QBApprox (t x : ℕ) : ℕ :=
  ∑ k ∈ Finset.range t, ∑ n ∈ Finset.range (2 ^ (t + 1) - 1), QBApproxTerm t x k n

private theorem primrec_pow : Primrec₂ ((· ^ ·) : ℕ → ℕ → ℕ) :=
  Primrec₂.unpaired'.1 Nat.Primrec.pow

private theorem primrec_QBApproxTerm :
    Primrec fun p : ℕ × ℕ × ℕ × ℕ => QBApproxTerm p.1 p.2.1 p.2.2.1 p.2.2.2 := by
  have hc : Primrec fun p : ℕ × ℕ × ℕ × ℕ => Denumerable.ofNat Code p.2.2.1 :=
    (Primrec.ofNat Code).comp (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
  have hn' : Primrec fun p : ℕ × ℕ × ℕ × ℕ => p.2.2.2 :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have hL : Primrec fun p : ℕ × ℕ × ℕ × ℕ =>
      elen (Denumerable.ofNat Code p.2.2.1) + (natToBits p.2.2.2).length :=
    Primrec.nat_add.comp (primrec_elen.comp hc)
      (Primrec.list_length.comp (primrec_natToBits.comp hn'))
  have hLe : Primrec fun p : ℕ × ℕ × ℕ × ℕ =>
      decide (elen (Denumerable.ofNat Code p.2.2.1) + (natToBits p.2.2.2).length ≤ p.1) :=
    Primrec.nat_le.decide.comp hL Primrec.fst
  have hmem : Primrec fun p : ℕ × ℕ × ℕ × ℕ =>
      decide (p.2.2.2 ∈ acceptedList (Denumerable.ofNat Code p.2.2.1) p.1) := by
    have hAccList : Primrec fun p : ℕ × ℕ × ℕ × ℕ =>
        acceptedList (Denumerable.ofNat Code p.2.2.1) p.1 :=
      Primrec.comp primrec₂_acceptedList (hc.pair Primrec.fst)
    exact (primrec_mem_list.comp hAccList hn').decide
  have hev : Primrec fun p : ℕ × ℕ × ℕ × ℕ =>
      decide (evaln p.1 (Denumerable.ofNat Code p.2.2.1) p.2.2.2 = some p.2.1) := by
    have hEv : Primrec fun p : ℕ × ℕ × ℕ × ℕ =>
        evaln p.1 (Denumerable.ofNat Code p.2.2.1) p.2.2.2 := by
      have hq : Primrec fun p : ℕ × ℕ × ℕ × ℕ =>
          ((p.1, Denumerable.ofNat Code p.2.2.1), p.2.2.2) :=
        (Primrec.fst.pair hc).pair hn'
      exact Primrec.comp Nat.Partrec.Code.primrec_evaln hq
    have hSomeX : Primrec fun p : ℕ × ℕ × ℕ × ℕ => (some p.2.1 : Option ℕ) :=
      Primrec.option_some.comp (Primrec.fst.comp Primrec.snd)
    exact (Primrec.eq.comp hEv hSomeX).decide
  have hcondBool : Primrec fun p : ℕ × ℕ × ℕ × ℕ =>
      decide (elen (Denumerable.ofNat Code p.2.2.1) + (natToBits p.2.2.2).length ≤ p.1) &&
        decide (p.2.2.2 ∈ acceptedList (Denumerable.ofNat Code p.2.2.1) p.1) &&
        decide (evaln p.1 (Denumerable.ofNat Code p.2.2.1) p.2.2.2 = some p.2.1) :=
    Primrec.and.comp (Primrec.and.comp hLe hmem) hev
  have hval : Primrec fun p : ℕ × ℕ × ℕ × ℕ =>
      (2 : ℕ) ^ (p.1 - (elen (Denumerable.ofNat Code p.2.2.1) + (natToBits p.2.2.2).length)) :=
    primrec_pow.comp (Primrec.const 2) (Primrec.nat_sub.comp Primrec.fst hL)
  have := Primrec.cond hcondBool hval (Primrec.const 0)
  refine this.of_eq fun p => ?_
  unfold QBApproxTerm
  simp [and_assoc]

private theorem primrec₂_QBApprox : Primrec₂ QBApprox := by
  have hr : Primrec fun q : (ℕ × ℕ × ℕ) × ℕ => (q.1.1, q.1.2.1, q.1.2.2, q.2) :=
    (Primrec.fst.comp Primrec.fst).pair
      ((Primrec.fst.comp (Primrec.snd.comp Primrec.fst)).pair
        ((Primrec.snd.comp (Primrec.snd.comp Primrec.fst)).pair Primrec.snd))
  have hg1 : Primrec fun q : (ℕ × ℕ × ℕ) × ℕ => QBApproxTerm q.1.1 q.1.2.1 q.1.2.2 q.2 := by
    have := Primrec.comp primrec_QBApproxTerm hr
    exact this.of_eq fun q => rfl
  have hinnerList : Primrec fun a : ℕ × ℕ × ℕ =>
      (List.range (2 ^ (a.1 + 1) - 1)).map fun n => QBApproxTerm a.1 a.2.1 a.2.2 n :=
    Primrec.list_map
      (Primrec.list_range.comp
        (Primrec.nat_sub.comp
          (primrec_pow.comp (Primrec.const 2) (Primrec.succ.comp Primrec.fst))
          (Primrec.const 1)))
      hg1
  have hg2 : Primrec fun a : ℕ × ℕ × ℕ =>
      ((List.range (2 ^ (a.1 + 1) - 1)).map fun n => QBApproxTerm a.1 a.2.1 a.2.2 n).sum :=
    primrec_list_sum hinnerList
  have hg2' : Primrec fun q : (ℕ × ℕ) × ℕ =>
      ((List.range (2 ^ (q.1.1 + 1) - 1)).map fun n => QBApproxTerm q.1.1 q.1.2 q.2 n).sum :=
    hg2.comp
      ((Primrec.fst.comp Primrec.fst).pair ((Primrec.snd.comp Primrec.fst).pair Primrec.snd))
  have houterList : Primrec fun a : ℕ × ℕ =>
      (List.range a.1).map fun k =>
        ((List.range (2 ^ (a.1 + 1) - 1)).map fun n => QBApproxTerm a.1 a.2 k n).sum :=
    Primrec.list_map (Primrec.list_range.comp Primrec.fst) hg2'
  have hres : Primrec fun a : ℕ × ℕ =>
      ((List.range a.1).map fun k =>
        ((List.range (2 ^ (a.1 + 1) - 1)).map fun n => QBApproxTerm a.1 a.2 k n).sum).sum :=
    primrec_list_sum houterList
  refine hres.of_eq fun a => ?_
  change QBApprox a.1 a.2 = _
  unfold QBApprox
  rw [finsetSum_range_eq_listSum]

/-! ## `QB_lsc`: monotonicity -/

/-- A term valid at stage `t` stays valid at stage `t + 1` with double the weight; an invalid one
stays at worst `0`. -/
private theorem QBApproxTerm_double_le (t x k n : ℕ) :
    2 * QBApproxTerm t x k n ≤ QBApproxTerm (t + 1) x k n := by
  unfold QBApproxTerm
  set c := Denumerable.ofNat Code k with hc
  by_cases h : elen c + (natToBits n).length ≤ t ∧ n ∈ acceptedList c t ∧ evaln t c n = some x
  · obtain ⟨hL, hacc, hev⟩ := h
    have hL' : elen c + (natToBits n).length ≤ t + 1 := by omega
    have hacc' : n ∈ acceptedList c (t + 1) := acceptedList_mono (Nat.le_succ t) hacc
    have hev' : evaln (t + 1) c n = some x := by
      have hmem : x ∈ evaln (t + 1) c n := evaln_mono (Nat.le_succ t) hev
      exact hmem
    rw [if_pos ⟨hL, hacc, hev⟩, if_pos ⟨hL', hacc', hev'⟩]
    rw [show t + 1 - (elen c + (natToBits n).length) = (t - (elen c + (natToBits n).length)) + 1
      from by omega, pow_succ]
    exact le_of_eq (by ring)
  · rw [if_neg h]
    simp

/-- **Monotonicity**: `QBApprox`'s dyadic value never decreases with the stage. -/
private theorem QBApprox_mono_nat (t x : ℕ) : 2 * QBApprox t x ≤ QBApprox (t + 1) x := by
  unfold QBApprox
  calc 2 * ∑ k ∈ Finset.range t, ∑ n ∈ Finset.range (2 ^ (t + 1) - 1), QBApproxTerm t x k n
      = ∑ k ∈ Finset.range t, ∑ n ∈ Finset.range (2 ^ (t + 1) - 1), 2 * QBApproxTerm t x k n := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.mul_sum]
    _ ≤ ∑ k ∈ Finset.range t, ∑ n ∈ Finset.range (2 ^ (t + 1) - 1), QBApproxTerm (t + 1) x k n := by
        refine Finset.sum_le_sum fun k _ => ?_
        exact Finset.sum_le_sum fun n _ => QBApproxTerm_double_le t x k n
    _ ≤ ∑ k ∈ Finset.range (t + 1), ∑ n ∈ Finset.range (2 ^ (t + 1 + 1) - 1),
          QBApproxTerm (t + 1) x k n := by
        have hsub2 : Finset.range (2 ^ (t + 1) - 1) ⊆ Finset.range (2 ^ (t + 1 + 1) - 1) := by
          have h2 : (2 : ℕ) ^ (t + 1) ≤ 2 ^ (t + 1 + 1) :=
            Nat.pow_le_pow_right (by norm_num) (by omega)
          exact Finset.range_subset.mpr fun i hi => Finset.mem_range.mpr (by omega)
        have step1 : ∑ k ∈ Finset.range t, ∑ n ∈ Finset.range (2 ^ (t + 1) - 1),
              QBApproxTerm (t + 1) x k n
            ≤ ∑ k ∈ Finset.range t, ∑ n ∈ Finset.range (2 ^ (t + 1 + 1) - 1),
              QBApproxTerm (t + 1) x k n :=
          Finset.sum_le_sum fun k _ =>
            Finset.sum_le_sum_of_subset_of_nonneg hsub2 fun n _ _ => Nat.zero_le _
        refine step1.trans ?_
        exact Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.range_subset.mpr fun i hi => Finset.mem_range.mpr (by omega))
          fun k _ _ => Nat.zero_le _

theorem QBApprox_mono (t x : ℕ) :
    (QBApprox t x : ℝ) / 2 ^ t ≤ (QBApprox (t + 1) x : ℝ) / 2 ^ (t + 1) := by
  have hcast : (2 * QBApprox t x : ℝ) ≤ (QBApprox (t + 1) x : ℝ) := by
    exact_mod_cast QBApprox_mono_nat t x
  have heq : (QBApprox t x : ℝ) / 2 ^ t = 2 * (QBApprox t x : ℝ) / 2 ^ (t + 1) := by
    rw [pow_succ]; ring
  rw [heq]
  gcongr

/-! ## `QB_lsc`: the lower bound -/

/-- If `n` is accepted, and evaluates to `x`, by stage `s`, then `x` is `pfy c n`'s value: `evaln`
is stable from the first accepting stage on, so this holds at ANY accepting stage, not only the
first. -/
private theorem pfy_eq_of_evaln_stage {c : Code} {n s x : ℕ} (hacc : n ∈ acceptedList c s)
    (hev : evaln s c n = some x) : x ∈ pfy c n := by
  have hdom : n ∈ (pfy c).Dom := (mem_pfy_dom_iff c n).mpr ⟨s, hacc⟩
  obtain ⟨x', hx'⟩ := Part.dom_iff_mem.mp hdom
  have hxeval : x ∈ c.eval n := evaln_sound hev
  have hx'eval : x' ∈ c.eval n := pfy_sub c n x' hx'
  rwa [Part.mem_unique hxeval hx'eval]

/-- The real-number identity behind a valid `QBApprox` term: divided by `2 ^ t`, a Kraft weight
truncated to `t` bits is exactly the untruncated weight. -/
private theorem pow_sub_div_eq (t L : ℕ) (hL : L ≤ t) :
    ((2 : ℕ) ^ (t - L) : ℝ) / 2 ^ t = (1 / 2 : ℝ) ^ L := by
  push_cast
  rw [show ((1 : ℝ) / 2) ^ L = 1 / 2 ^ L from by rw [div_pow, one_pow]]
  rw [div_eq_div_iff (by positivity) (by positivity), one_mul, ← pow_add, Nat.sub_add_cancel hL]

open scoped Classical in
/-- Divided by `2 ^ t`, a `QBApprox` term is bounded by the description's own contribution to
`QB`'s defining series — with equality exactly when the term is valid. -/
private theorem QBApproxTerm_le_term (t x k n : ℕ) :
    (QBApproxTerm t x k n : ℝ) / 2 ^ t ≤
      if x ∈ pfy (Denumerable.ofNat Code k) (bitsToNat (natToBits n))
      then kbWeight (Denumerable.ofNat Code k, natToBits n) else 0 := by
  rw [bitsToNat_natToBits]
  unfold QBApproxTerm
  set c := Denumerable.ofNat Code k
  by_cases h : elen c + (natToBits n).length ≤ t ∧ n ∈ acceptedList c t ∧ evaln t c n = some x
  · obtain ⟨hL, hacc, hev⟩ := h
    have hx : x ∈ pfy c n := pfy_eq_of_evaln_stage hacc hev
    rw [if_pos ⟨hL, hacc, hev⟩, if_pos hx]
    unfold kbWeight
    have hmemS : natToBits n ∈ natToBits '' (pfy c).Dom :=
      ⟨n, Part.dom_iff_mem.mpr ⟨x, hx⟩, rfl⟩
    rw [if_pos hmemS]
    refine le_of_eq ?_
    push_cast
    rw [show ((1 : ℝ) / 2) ^ (elen c + (natToBits n).length)
        = 1 / 2 ^ (elen c + (natToBits n).length)
      from by rw [div_pow, one_pow]]
    rw [div_eq_div_iff (by positivity) (by positivity), one_mul, ← pow_add,
      Nat.sub_add_cancel hL]
  · rw [if_neg h]
    split
    · simp only [Nat.cast_zero, zero_div]
      exact kbWeight_nonneg _
    · simp

/-- The description map is injective: distinct machine/argument-index pairs give distinct
descriptions. -/
private theorem phi_injective :
    Function.Injective fun kn : ℕ × ℕ => (Denumerable.ofNat Code kn.1, natToBits kn.2) := by
  rintro ⟨k, n⟩ ⟨k', n'⟩ heq
  simp only [Prod.mk.injEq] at heq
  obtain ⟨hk, hn⟩ := heq
  have hk' : k = k' := by
    have := congrArg Encodable.encode hk
    rwa [Denumerable.encode_ofNat, Denumerable.encode_ofNat] at this
  have hn' : n = n' := by
    have := congrArg bitsToNat hn
    rwa [bitsToNat_natToBits, bitsToNat_natToBits] at this
  simp [hk', hn']

open scoped Classical in
/-- **The lower bound**: `QBApprox`'s dyadic value never exceeds `QB`. -/
theorem QBApprox_le (t x : ℕ) : (QBApprox t x : ℝ) / 2 ^ t ≤ QB x := by
  have hstep : (QBApprox t x : ℝ) / 2 ^ t
      ≤ ∑ k ∈ Finset.range t, ∑ n ∈ Finset.range (2 ^ (t + 1) - 1),
          if x ∈ pfy (Denumerable.ofNat Code k) (bitsToNat (natToBits n))
          then kbWeight (Denumerable.ofNat Code k, natToBits n) else 0 := by
    unfold QBApprox
    push_cast
    rw [sum_div_eq]
    refine Finset.sum_le_sum fun k _ => ?_
    rw [sum_div_eq]
    exact Finset.sum_le_sum fun n _ => QBApproxTerm_le_term t x k n
  refine hstep.trans ?_
  classical
  set S : Finset (Code × List Bool) :=
    (Finset.range t ×ˢ Finset.range (2 ^ (t + 1) - 1)).image
      (fun kn : ℕ × ℕ => (Denumerable.ofNat Code kn.1, natToBits kn.2)) with hS
  have himg : ∑ q ∈ S, (if x ∈ pfy q.1 (bitsToNat q.2) then kbWeight q else 0)
      = ∑ kn ∈ Finset.range t ×ˢ Finset.range (2 ^ (t + 1) - 1),
          (if x ∈ pfy (Denumerable.ofNat Code kn.1) (bitsToNat (natToBits kn.2))
            then kbWeight (Denumerable.ofNat Code kn.1, natToBits kn.2) else 0) := by
    rw [hS, Finset.sum_image]
    intro a _ b _ hab
    exact phi_injective hab
  rw [← Finset.sum_product', ← himg]
  exact Summable.sum_le_tsum S (fun _ _ => by
    split <;> [exact kbWeight_nonneg _; exact le_refl 0]) (summable_QB_term x)

/-! ## `QB_lsc`: convergence -/

/-- A description's decoding stage: some stage at which its argument is accepted and evaluates to
the decoded value. -/
private theorem exists_stage_of_mem_pfy {c : Code} {n x : ℕ} (hx : x ∈ pfy c n) :
    ∃ s, n ∈ acceptedList c s ∧ evaln s c n = some x := by
  have hdom : n ∈ (pfy c).Dom := Part.dom_iff_mem.mpr ⟨x, hx⟩
  have hex : ∃ s, n ∈ acceptedList c s := (mem_pfy_dom_iff c n).mp hdom
  refine ⟨Nat.find hex, Nat.find_spec hex, ?_⟩
  unfold pfy at hx
  rw [dif_pos hex, Part.mem_some_iff] at hx
  rw [hx]
  exact (Option.some_get _).symm

theorem QBApprox_lt (x : ℕ) (q : ℝ) (hq : q < QB x) :
    ∃ t, q < (QBApprox t x : ℝ) / 2 ^ t := by
  classical
  have hsum : HasSum (fun cp : Code × List Bool =>
      if x ∈ pfy cp.1 (bitsToNat cp.2) then kbWeight cp else 0) (QB x) :=
    (summable_QB_term x).hasSum
  have hev : ∀ᶠ F : Finset (Code × List Bool) in Filter.atTop,
      q < ∑ cp ∈ F, if x ∈ pfy cp.1 (bitsToNat cp.2) then kbWeight cp else 0 :=
    (tendsto_order.mp hsum).1 q hq
  obtain ⟨F, hF⟩ := hev.exists
  set stage : Code × List Bool → ℕ := fun cp =>
    if h : x ∈ pfy cp.1 (bitsToNat cp.2) then (exists_stage_of_mem_pfy h).choose else 0
    with hstagedef
  set bnd : Code × List Bool → ℕ := fun cp =>
    max (Encodable.encode cp.1) (max (elen cp.1 + cp.2.length) (stage cp)) with hbnddef
  set t : ℕ := F.sup bnd + 1 with htdef
  refine ⟨t, hF.trans_le ?_⟩
  have hbnd_lt : ∀ cp ∈ F, bnd cp < t := fun cp hcp =>
    htdef ▸ Nat.lt_succ_of_le (Finset.le_sup hcp)
  have hk_lt : ∀ cp ∈ F, Encodable.encode cp.1 < t := fun cp hcp =>
    lt_of_le_of_lt (le_max_left _ _) (hbnd_lt cp hcp)
  have hL_lt : ∀ cp ∈ F, elen cp.1 + cp.2.length < t := fun cp hcp =>
    lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_right _ _)) (hbnd_lt cp hcp)
  have hstage_lt : ∀ cp ∈ F, stage cp < t := fun cp hcp =>
    lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_right _ _)) (hbnd_lt cp hcp)
  have hacc_ev : ∀ cp ∈ F, ∀ hx : x ∈ pfy cp.1 (bitsToNat cp.2),
      bitsToNat cp.2 ∈ acceptedList cp.1 t ∧ evaln t cp.1 (bitsToNat cp.2) = some x := by
    intro cp hcp hx
    have hspec := (exists_stage_of_mem_pfy hx).choose_spec
    have hstage_eq : stage cp = (exists_stage_of_mem_pfy hx).choose := by
      rw [hstagedef]; exact dif_pos hx
    have hle : stage cp ≤ t := le_of_lt (hstage_lt cp hcp)
    rw [hstage_eq] at hle
    exact ⟨acceptedList_mono hle hspec.1, evaln_mono hle hspec.2⟩
  have hterm_eq : ∀ cp ∈ F, (if x ∈ pfy cp.1 (bitsToNat cp.2) then kbWeight cp else 0)
      = (QBApproxTerm t x (Encodable.encode cp.1) (bitsToNat cp.2) : ℝ) / 2 ^ t := by
    intro cp hcp
    by_cases hx : x ∈ pfy cp.1 (bitsToNat cp.2)
    · rw [if_pos hx]
      obtain ⟨hacc, hev⟩ := hacc_ev cp hcp hx
      unfold QBApproxTerm
      simp only [Denumerable.ofNat_encode, natToBits_bitsToNat]
      rw [if_pos ⟨le_of_lt (hL_lt cp hcp), hacc, hev⟩]
      unfold kbWeight
      have hmemS : cp.2 ∈ natToBits '' (pfy cp.1).Dom :=
        ⟨bitsToNat cp.2, Part.dom_iff_mem.mpr ⟨x, hx⟩, natToBits_bitsToNat cp.2⟩
      rw [if_pos hmemS]
      refine Eq.symm ?_
      push_cast
      exact pow_sub_div_eq t (elen cp.1 + cp.2.length) (le_of_lt (hL_lt cp hcp))
    · rw [if_neg hx]
      unfold QBApproxTerm
      simp only [Denumerable.ofNat_encode, natToBits_bitsToNat]
      by_cases hcond : elen cp.1 + cp.2.length ≤ t ∧
          bitsToNat cp.2 ∈ acceptedList cp.1 t ∧ evaln t cp.1 (bitsToNat cp.2) = some x
      · exact absurd (pfy_eq_of_evaln_stage hcond.2.1 hcond.2.2) hx
      · rw [if_neg hcond]; simp
  have hpsi_inj : Function.Injective
      fun cp : Code × List Bool => (Encodable.encode cp.1, bitsToNat cp.2) := by
    rintro ⟨c, p⟩ ⟨c', p'⟩ heq
    simp only [Prod.mk.injEq] at heq
    obtain ⟨hc, hp⟩ := heq
    have hc' : c = c' := by
      have := congrArg (Encodable.decode (α := Code)) hc
      simpa using this
    have hp' : p = p' := by
      have := congrArg natToBits hp
      rwa [natToBits_bitsToNat, natToBits_bitsToNat] at this
    simp [hc', hp']
  have hpsi_mem : ∀ cp ∈ F, (Encodable.encode cp.1, bitsToNat cp.2)
      ∈ Finset.range t ×ˢ Finset.range (2 ^ (t + 1) - 1) := by
    intro cp hcp
    rw [Finset.mem_product, Finset.mem_range, Finset.mem_range]
    refine ⟨hk_lt cp hcp, ?_⟩
    have hlen : (natToBits (bitsToNat cp.2)).length ≤ t := by
      rw [natToBits_bitsToNat]
      exact le_of_lt (lt_of_le_of_lt (Nat.le_add_left _ _) (hL_lt cp hcp))
    have hsize : Nat.size (bitsToNat cp.2 + 1) ≤ t + 1 := by
      rw [← length_natToBits]; omega
    have hlt : bitsToNat cp.2 + 1 < 2 ^ (t + 1) := Nat.size_le.mp hsize
    omega
  calc ∑ cp ∈ F, (if x ∈ pfy cp.1 (bitsToNat cp.2) then kbWeight cp else 0)
      = ∑ cp ∈ F, (QBApproxTerm t x (Encodable.encode cp.1) (bitsToNat cp.2) : ℝ) / 2 ^ t :=
        Finset.sum_congr rfl hterm_eq
    _ = ∑ q ∈ F.image (fun cp => (Encodable.encode cp.1, bitsToNat cp.2)),
          (QBApproxTerm t x q.1 q.2 : ℝ) / 2 ^ t := by
        rw [Finset.sum_image fun a _ b _ hab => hpsi_inj hab]
    _ ≤ ∑ q ∈ Finset.range t ×ˢ Finset.range (2 ^ (t + 1) - 1),
          (QBApproxTerm t x q.1 q.2 : ℝ) / 2 ^ t := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun q _ _ => by positivity
        exact Finset.image_subset_iff.mpr hpsi_mem
    _ = ∑ k ∈ Finset.range t, ∑ n ∈ Finset.range (2 ^ (t + 1) - 1),
          (QBApproxTerm t x k n : ℝ) / 2 ^ t :=
        Finset.sum_product' (Finset.range t) (Finset.range (2 ^ (t + 1) - 1))
          fun k n => (QBApproxTerm t x k n : ℝ) / 2 ^ t
    _ = (QBApprox t x : ℝ) / 2 ^ t := by
        unfold QBApprox
        push_cast
        rw [sum_div_eq]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [sum_div_eq]

/-- **`QB` is lower-semicomputable**: `QBApprox` is its computable, monotone, dyadic
approximation. -/
theorem QB_lsc : LowerSemicomputable QB :=
  ⟨QBApprox, primrec₂_QBApprox.to_comp, QBApprox_mono, QBApprox_le, QBApprox_lt⟩

end PrefixMachine
