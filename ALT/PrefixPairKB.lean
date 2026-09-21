/-
Copyright (c) 2026 Mykola Palamarchuk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mykola Palamarchuk
-/
module

public import ALT.PrefixInvarianceKB

-- Formal-check file, not Mathlib-destined: opt out of the house-style header linter.
set_option linter.style.header false

/-!
# `KB`'s subadditivity on pairs

Provenance: the pairing half of [Discovery] §1.1's universal-machine description, over the prefix
complexity `KB` of `ALT/PrefixMachine.lean` and the universal prefix machine `univPrefix` of
`ALT/PrefixInvarianceKB.lean`.

## What this establishes

* `KB_pair_le` — **`KB`'s subadditivity on pairs**: `∃ c, ∀ x y, KB (Nat.pair x y) ≤ KB x + KB y +
  c`. A single new machine searches its own input for the ONE point at which it splits into a
  description for `x` followed by a description for `y`, each read through `univPrefix`: since
  `univPrefix`'s own halting domain is prefix-free (`prefixFree_univPrefix_dom`), an input has at
  most one such split, so no serialization parser and no per-machine dovetail are needed — the
  search runs on `Nat.Partrec.Code.evaln` directly, over `univPrefix` alone.

## What this does NOT establish (flagged)

* This is **not** the same fact as `AdditiveComplexity.KE_subadditive` in another currency:
  `KE_subadditive` composes `Code.pair`, running both programs on the SAME input, definitionally;
  here the two descriptions carry different arguments, no such combinator reaches across them, and
  the split-point search is the whole content.
* The constant is `elen` of a `Classical.choose`n machine: existential, uncomputed.
-/


@[expose] public section

namespace PrefixMachine

open Nat.Partrec Nat.Partrec.Code AdditiveComplexity CodeEvalLaws

/-! ## The split-point search, primitive-recursively -/

private theorem primrec_splitK : Primrec fun p : ℕ × ℕ => (Nat.unpair p.2).1 :=
  (Primrec.fst.comp Primrec.unpair).comp Primrec.snd

private theorem primrec_splitS : Primrec fun p : ℕ × ℕ => (Nat.unpair p.2).2 :=
  (Primrec.snd.comp Primrec.unpair).comp Primrec.snd

private theorem primrec_splitW : Primrec fun p : ℕ × ℕ => natToBits p.1 :=
  primrec_natToBits.comp Primrec.fst

private theorem primrec_splitTake : Primrec fun p : ℕ × ℕ =>
    (natToBits p.1).take (Nat.unpair p.2).1 :=
  Primrec.comp Primrec.list_take (primrec_splitK.pair primrec_splitW)

private theorem primrec_splitDrop : Primrec fun p : ℕ × ℕ =>
    (natToBits p.1).drop (Nat.unpair p.2).1 :=
  Primrec.comp Primrec.list_drop (primrec_splitK.pair primrec_splitW)

private theorem primrec_splitArgA : Primrec fun p : ℕ × ℕ =>
    bitsToNat ((natToBits p.1).take (Nat.unpair p.2).1) :=
  primrec_bitsToNat.comp primrec_splitTake

private theorem primrec_splitArgB : Primrec fun p : ℕ × ℕ =>
    bitsToNat ((natToBits p.1).drop (Nat.unpair p.2).1) :=
  primrec_bitsToNat.comp primrec_splitDrop

/-- **The split-point search predicate**, primitive-recursively: writing `n = Nat.pair k s`, does
`univPrefix` halt by stage `s` on the first `k` bits of `m`'s bit-string. -/
private theorem primrec₂_splitCond : Primrec₂ fun (m n : ℕ) =>
    (evaln (Nat.unpair n).2 univPrefix
      (bitsToNat ((natToBits m).take (Nat.unpair n).1))).isSome := by
  have hq : Primrec fun p : ℕ × ℕ => (((Nat.unpair p.2).2, univPrefix),
      bitsToNat ((natToBits p.1).take (Nat.unpair p.2).1)) :=
    (primrec_splitS.pair (Primrec.const univPrefix)).pair primrec_splitArgA
  have hev : Primrec fun p : ℕ × ℕ =>
      evaln (Nat.unpair p.2).2 univPrefix
        (bitsToNat ((natToBits p.1).take (Nat.unpair p.2).1)) :=
    (Nat.Partrec.Code.primrec_evaln.comp hq).of_eq fun p => rfl
  exact Primrec.option_isSome.comp hev

/-! ## The split-point search, as a value: `Nat.rfind` reduces to `Nat.find` -/

open scoped Classical in
/-- Once the state has bottomed out, `Nat.rfind` over the split predicate reproduces `Nat.find` —
the same reduction `BitStringPrimrec.rfind_acceptedList_eq` makes for `pfy`'s own search. -/
private theorem rfind_splitCond_eq (m : ℕ) :
    Nat.rfind (fun n : ℕ => Part.some
        ((evaln (Nat.unpair n).2 univPrefix
          (bitsToNat ((natToBits m).take (Nat.unpair n).1))).isSome)) =
      if h : ∃ n : ℕ, (evaln (Nat.unpair n).2 univPrefix
          (bitsToNat ((natToBits m).take (Nat.unpair n).1))).isSome = true then
        Part.some (Nat.find h) else Part.none := by
  split
  · rename_i h
    apply Part.eq_some_iff.mpr
    apply Nat.mem_rfind.mpr
    refine ⟨by simp [Nat.find_spec h], fun {j} hj => ?_⟩
    simp only [Part.mem_some_iff]
    exact (Bool.eq_false_iff.mpr (fun hc => Nat.find_min h hj hc)).symm
  · rename_i h
    apply Part.eq_none_iff.mpr
    rintro n hn
    replace hn := Nat.mem_rfind.mp hn
    exact h ⟨n, by simpa using hn.1⟩

/-! ## The machine, as a code -/

theorem partrec_pairMachineFn :
    Nat.Partrec (fun m : ℕ =>
      (Nat.rfind fun n : ℕ => Part.some
          ((evaln (Nat.unpair n).2 univPrefix
            (bitsToNat ((natToBits m).take (Nat.unpair n).1))).isSome)).bind
        fun n : ℕ =>
          (univPrefix.eval (bitsToNat ((natToBits m).take (Nat.unpair n).1))).bind
            fun x : ℕ =>
              (univPrefix.eval (bitsToNat ((natToBits m).drop (Nat.unpair n).1))).bind
                fun y : ℕ => Part.some (Nat.pair x y)) := by
  have hArfind : Partrec fun m : ℕ => Nat.rfind fun n : ℕ => Part.some
      ((evaln (Nat.unpair n).2 univPrefix
        (bitsToNat ((natToBits m).take (Nat.unpair n).1))).isSome) :=
    Partrec.rfind primrec₂_splitCond.to_comp.partrec₂
  have hEvalA_raw : Partrec fun mn : ℕ × ℕ =>
      univPrefix.eval (bitsToNat ((natToBits mn.1).take (Nat.unpair mn.2).1)) :=
    Nat.Partrec.Code.eval_part.comp (Computable.const univPrefix) primrec_splitArgA.to_comp
  have hEvalB_raw : Partrec fun mn : ℕ × ℕ =>
      univPrefix.eval (bitsToNat ((natToBits mn.1).drop (Nat.unpair mn.2).1)) :=
    Nat.Partrec.Code.eval_part.comp (Computable.const univPrefix) primrec_splitArgB.to_comp
  have hx2 : Primrec₂ fun (a : (ℕ × ℕ) × ℕ) (_ : ℕ) => a.2 :=
    Primrec.comp₂ Primrec.snd Primrec₂.left
  have hpairxy : Primrec₂ fun (a : (ℕ × ℕ) × ℕ) (y : ℕ) => Nat.pair a.2 y :=
    Primrec₂.natPair.comp₂ hx2 Primrec₂.right
  have hLevel2 : Partrec fun a : (ℕ × ℕ) × ℕ =>
      (univPrefix.eval (bitsToNat ((natToBits a.1.1).drop (Nat.unpair a.1.2).1))).bind
        fun y => Part.some (Nat.pair a.2 y) :=
    Partrec.bind (hEvalB_raw.comp Computable.fst) hpairxy.to_comp.partrec₂
  have hLevel1 : Partrec fun mn : ℕ × ℕ =>
      (univPrefix.eval (bitsToNat ((natToBits mn.1).take (Nat.unpair mn.2).1))).bind
        fun x => (univPrefix.eval (bitsToNat ((natToBits mn.1).drop (Nat.unpair mn.2).1))).bind
          fun y => Part.some (Nat.pair x y) :=
    Partrec.bind hEvalA_raw hLevel2
  exact Partrec.nat_iff.mp (Partrec.bind hArfind hLevel1)

/-- **The pairing machine, as a code.** Searches its input, read as bits, for the one point where
it splits into a description for one value followed by a description for another, each read
through `univPrefix`. -/
noncomputable def pairMachine : Code :=
  Classical.choose (exists_code.mp partrec_pairMachineFn)

theorem pairMachine_eval : pairMachine.eval =
    fun m : ℕ =>
      (Nat.rfind fun n : ℕ => Part.some
          ((evaln (Nat.unpair n).2 univPrefix
            (bitsToNat ((natToBits m).take (Nat.unpair n).1))).isSome)).bind
        fun n : ℕ =>
          (univPrefix.eval (bitsToNat ((natToBits m).take (Nat.unpair n).1))).bind
            fun x : ℕ =>
              (univPrefix.eval (bitsToNat ((natToBits m).drop (Nat.unpair n).1))).bind
                fun y : ℕ => Part.some (Nat.pair x y) :=
  Classical.choose_spec (exists_code.mp partrec_pairMachineFn)

/-! ## The machine's own halting domain, read as bit-strings, is prefix-free -/

/-- Two members of a prefix-free set that prefix a common list coincide, and so do the remainders
— the peeling step of the machine's decode, proved locally in two lines. -/
private theorem peel {S : Set (List Bool)} (h : PrefixFree S)
    {w w' r1 r2 : List Bool} (hw : w ∈ S) (hw' : w' ∈ S) (heq : w ++ r1 = w' ++ r2) :
    w = w' ∧ r1 = r2 := by
  have hww' : w = w' := by
    rcases le_total w.length w'.length with hle | hle
    · have hp : w <+: w' ++ r2 := ⟨r1, heq⟩
      exact h w hw w' hw' ((List.isPrefix_append_of_length hle).mp hp)
    · have hp : w' <+: w ++ r1 := ⟨r2, heq.symm⟩
      exact (h w' hw' w hw ((List.isPrefix_append_of_length hle).mp hp)).symm
  refine ⟨hww', ?_⟩
  rw [hww'] at heq
  exact List.append_cancel_left heq

/-- Any input `pairMachine` halts on decomposes, through the split-point search, into two halves
each genuinely in `univPrefix`'s own halting domain (read as bit-strings). -/
private theorem pairMachine_decomp {m : ℕ} (hm : m ∈ pairMachine.eval.Dom) :
    ∃ n : ℕ,
      natToBits m = (natToBits m).take (Nat.unpair n).1 ++ (natToBits m).drop (Nat.unpair n).1 ∧
      (natToBits m).take (Nat.unpair n).1 ∈ natToBits '' univPrefix.eval.Dom ∧
      (natToBits m).drop (Nat.unpair n).1 ∈ natToBits '' univPrefix.eval.Dom := by
  obtain ⟨v, hv⟩ := Part.dom_iff_mem.mp hm
  rw [congrFun pairMachine_eval m] at hv
  obtain ⟨n, hn, hbv⟩ := Part.mem_bind_iff.mp hv
  have hnfind : true = (evaln (Nat.unpair n).2 univPrefix
      (bitsToNat ((natToBits m).take (Nat.unpair n).1))).isSome :=
    Part.mem_some_iff.mp (Nat.rfind_spec hn)
  obtain ⟨u, hu⟩ := Option.isSome_iff_exists.mp hnfind.symm
  have huD : (natToBits m).take (Nat.unpair n).1 ∈ natToBits '' univPrefix.eval.Dom :=
    ⟨bitsToNat ((natToBits m).take (Nat.unpair n).1),
      Part.dom_iff_mem.mpr ⟨u, evaln_sound hu⟩, natToBits_bitsToNat _⟩
  obtain ⟨x, hx, hbv2⟩ := Part.mem_bind_iff.mp hbv
  obtain ⟨y, hy, -⟩ := Part.mem_bind_iff.mp hbv2
  have hvD : (natToBits m).drop (Nat.unpair n).1 ∈ natToBits '' univPrefix.eval.Dom :=
    ⟨bitsToNat ((natToBits m).drop (Nat.unpair n).1),
      Part.dom_iff_mem.mpr ⟨y, hy⟩, natToBits_bitsToNat _⟩
  exact ⟨n, (List.take_append_drop (Nat.unpair n).1 (natToBits m)).symm, huD, hvD⟩

/-- **`pairMachine`'s own halting domain, read as bit-strings, is prefix-free.** Two accepted
inputs decompose (`pairMachine_decomp`) into two halves each in `univPrefix`'s own domain; a
prefix relation between the whole inputs peels (`peel`, over `univPrefix`'s domain, prefix-free by
`prefixFree_univPrefix_dom`) to a matching first half and then — read again through
`prefixFree_univPrefix_dom` — a matching second half. -/
theorem prefixFree_pairMachine_dom : PrefixFree (natToBits '' pairMachine.eval.Dom) := by
  intro p₁ hp₁ p₂ hp₂ hpre
  obtain ⟨m₁, hm₁, rfl⟩ := hp₁
  obtain ⟨m₂, hm₂, rfl⟩ := hp₂
  obtain ⟨n₁, heq₁, hu₁, hv₁⟩ := pairMachine_decomp hm₁
  obtain ⟨n₂, heq₂, hu₂, hv₂⟩ := pairMachine_decomp hm₂
  rw [heq₁, heq₂] at hpre ⊢
  obtain ⟨r, hr⟩ := hpre
  rw [List.append_assoc] at hr
  obtain ⟨htake_eq, hdrop_eq⟩ := peel prefixFree_univPrefix_dom hu₁ hu₂ hr
  have hdrop_pre :
      (natToBits m₁).drop (Nat.unpair n₁).1 <+: (natToBits m₂).drop (Nat.unpair n₂).1 :=
    ⟨r, hdrop_eq⟩
  have hdrop_eq' :
      (natToBits m₁).drop (Nat.unpair n₁).1 = (natToBits m₂).drop (Nat.unpair n₂).1 :=
    prefixFree_univPrefix_dom _ hv₁ _ hv₂ hdrop_pre
  rw [htake_eq, hdrop_eq']

/-! ## `KB`'s subadditivity on pairs -/

/-- **`KB`'s subadditivity on pairs.** Take the `KB`-optimal descriptions `(d₁, q₁)` for `x` and
`(d₂, q₂)` for `y`; each converges through `univPrefix` (`univPrefix_spec`), and `E d₂` is never
empty (`E_ne_nil`), so the concatenation's own split point `(E d₁ ++ q₁).length` is strictly below
its length. The split-point search finds SOME point satisfying the predicate — `Nat.find`'s own
witness — and since `univPrefix`'s domain is prefix-free, that point coincides with the genuine
split (both are `.take`-prefixes of the same list, comparable, hence equal, hence equal-length by
`min`), so both `univPrefix.eval` calls resolve exactly as intended and `pairMachine` outputs
`Nat.pair x y` on the concatenated description. -/
theorem KB_pair_le : ∃ c, ∀ x y, KB (Nat.pair x y) ≤ KB x + KB y + c := by
  refine ⟨elen pairMachine, fun x y => ?_⟩
  obtain ⟨d₁, q₁, hxmem, hxlen⟩ := exists_min_KB x
  obtain ⟨d₂, q₂, hymem, hylen⟩ := exists_min_KB y
  have hux : univPrefix.eval (bitsToNat (E d₁ ++ q₁)) = Part.some x := by
    rw [univPrefix_spec]; exact Part.eq_some_iff.mpr hxmem
  have huy : univPrefix.eval (bitsToNat (E d₂ ++ q₂)) = Part.some y := by
    rw [univPrefix_spec]; exact Part.eq_some_iff.mpr hymem
  have hu1D : (E d₁ ++ q₁) ∈ natToBits '' univPrefix.eval.Dom :=
    ⟨bitsToNat (E d₁ ++ q₁), Part.dom_iff_mem.mpr ⟨x, Part.eq_some_iff.mp hux⟩,
      natToBits_bitsToNat _⟩
  set w : List Bool := (E d₁ ++ q₁) ++ (E d₂ ++ q₂) with hwdef
  have hklt : (E d₁ ++ q₁).length < w.length := by
    have hpos : 0 < (E d₂).length := List.length_pos_iff.mpr (E_ne_nil d₂)
    simp only [hwdef, List.length_append]
    omega
  have htakek : w.take (E d₁ ++ q₁).length = E d₁ ++ q₁ := List.take_left
  have hdropk : w.drop (E d₁ ++ q₁).length = E d₂ ++ q₂ := List.drop_left
  have hu1D' : w.take (E d₁ ++ q₁).length ∈ natToBits '' univPrefix.eval.Dom := by
    rw [htakek]; exact hu1D
  -- The search converges: `(E d₁ ++ q₁).length` paired with a runtime bound for `x` satisfies it.
  obtain ⟨s, hs⟩ := evaln_complete.mp (Part.eq_some_iff.mp hux)
  have hwitness : (evaln (Nat.unpair (Nat.pair (E d₁ ++ q₁).length s)).2 univPrefix
      (bitsToNat ((natToBits (bitsToNat w)).take
        (Nat.unpair (Nat.pair (E d₁ ++ q₁).length s)).1))).isSome = true := by
    rw [Nat.unpair_pair, natToBits_bitsToNat, htakek]
    exact Option.isSome_iff_exists.mpr ⟨x, hs⟩
  have hex : ∃ n : ℕ, (evaln (Nat.unpair n).2 univPrefix
      (bitsToNat ((natToBits (bitsToNat w)).take (Nat.unpair n).1))).isSome = true :=
    ⟨_, hwitness⟩
  set n : ℕ := Nat.find hex with hndef
  have hnspec := Nat.find_spec hex
  rw [← hndef] at hnspec
  -- The found split coincides with the genuine one, by `univPrefix`'s prefix-freeness.
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hnspec
  have hnD : (natToBits (bitsToNat w)).take (Nat.unpair n).1 ∈ natToBits '' univPrefix.eval.Dom :=
    ⟨bitsToNat ((natToBits (bitsToNat w)).take (Nat.unpair n).1),
      Part.dom_iff_mem.mpr ⟨v, evaln_sound hv⟩, natToBits_bitsToNat _⟩
  rw [natToBits_bitsToNat] at hnD
  have hcomp : w.take (Nat.unpair n).1 <+: w.take (E d₁ ++ q₁).length ∨
      w.take (E d₁ ++ q₁).length <+: w.take (Nat.unpair n).1 :=
    (le_total (Nat.unpair n).1 (E d₁ ++ q₁).length).imp
      (fun h => List.take_prefix_take_left h) (fun h => List.take_prefix_take_left h)
  have htakeeq : w.take (Nat.unpair n).1 = w.take (E d₁ ++ q₁).length := by
    rcases hcomp with h | h
    · exact prefixFree_univPrefix_dom _ hnD _ hu1D' h
    · exact (prefixFree_univPrefix_dom _ hu1D' _ hnD h).symm
  have hklen : (Nat.unpair n).1 = (E d₁ ++ q₁).length := by
    have := congrArg List.length htakeeq
    simp only [List.length_take] at this
    omega
  -- Both halves now resolve exactly as intended.
  have hfinal : pairMachine.eval (bitsToNat w) = Part.some (Nat.pair x y) := by
    rw [congrFun pairMachine_eval (bitsToNat w), rfind_splitCond_eq, dite_eq_left hex, ← hndef,
      Part.bind_some, natToBits_bitsToNat, hklen, htakek, hux, Part.bind_some, hdropk, huy,
      Part.bind_some]
  have hpf : PrefixFree (natToBits '' pairMachine.eval.Dom) := prefixFree_pairMachine_dom
  have hpfy_eq : pfy pairMachine = pairMachine.eval := pfy_eq_of_prefixFree _ hpf
  have hmem : Nat.pair x y ∈ pfy pairMachine (bitsToNat w) := by
    rw [hpfy_eq, hfinal]; exact Part.mem_some _
  have hKBle : KB (Nat.pair x y) ≤ elen pairMachine + w.length := KB_le hmem
  have hxlen' : (E d₁).length + q₁.length = KB x := hxlen
  have hylen' : (E d₂).length + q₂.length = KB y := hylen
  have hwlen : w.length = (E d₁).length + q₁.length + ((E d₂).length + q₂.length) := by
    simp only [hwdef, List.length_append]
  omega

end PrefixMachine
