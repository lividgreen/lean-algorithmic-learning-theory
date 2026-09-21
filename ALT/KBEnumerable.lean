/-
Copyright (c) 2026 Mykola Palamarchuk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mykola Palamarchuk
-/
module

public import ALT.ChaitinPrefix
public import ALT.SerializationParse
public import Foundation.FirstOrder.Incompleteness.Examples

-- Formal-check file, not Mathlib-destined: opt out of the house-style header linter.
set_option linter.style.header false

/-!
# `KB`'s coded-pair predicate is computably enumerable ([Decoupling] §6.6, [Discovery] §1.1)

Provenance: [Decoupling] §6.6 (the additive form of Theorem 6.6 this predicate serves) and
[Discovery] §1.1 (`KB`, FV-20). Discharges `KolmogorovComplexity.REPred kleB`, the second leaf
hypothesis of `ChaitinPrefix.lean`'s additive Chaitin bound — the twin of `rePred_kle` at `KB`
in place of `K_bitlen`. Both leaves (`EParserSpec` too) being present here also assembles the
unconditional theory-level statements they were blocking.

## What this establishes
* `kleB_iff_exists`: `kleB` restated as a description search — some serialized machine and binary
  argument, of total length at most the bound, decoding to the coded value via `pfy`.
* `mem_pfy_iff_exists_stage`: `pfy`'s output is reached at SOME finite stage of `acceptedList`,
  not only the least one — the search `rePred_kleB` dovetails over.
* `rePred_kleB`: `kleB` is computably enumerable, dovetailing over a witness code, a binary
  argument and a step budget.
* `chaitin_bound_KB`, `chaitin_bound_KB_min`, `chaitin_theoremB`, `chaitin_theoremB_RE`: the
  `ChaitinPrefix.lean` bounds, unconditional now that both leaves are proved.
* `exists_enumerator_chaitinB`: a theory's provability predicate at `chaitinSentenceB`, decidable
  by `T.Δ₁`, is exhibited BY a `Code`, not merely asserted enumerable.
* `chaitin_theoremB_nonvacuous`: a concrete theory (`𝗣𝗔⁻`) meeting every instance `chaitin_theoremB`
  asks for, together with its own enumerator.
* `setOf_KB_le_finite`, `chaitin_true_unprovableB`: the counting bound on `KB` and the
  true-and-unprovable family at the additive constant, `KB`'s twin of `chaitin_true_unprovable`.

## What this does NOT establish (flagged)
* Nothing beyond the two leaves and the assembly above; the abstract bounds' own boundaries
  (named in `ChaitinPrefix.lean`) are unchanged.
-/


@[expose] public section

namespace KolmogorovComplexity

open Nat.Partrec Nat.Partrec.Code AdditiveComplexity PrefixMachine
open FFL.FirstOrder FFL.FirstOrder.Arithmetic

/-! ## `kleB` as a description search -/

/-- **`kleB` restated as a description search**: some serialized machine `c` and binary argument
`p`, together no longer than the bound, whose `pfy`-decoding is the coded value. -/
theorem kleB_iff_exists (a : ℕ) : kleB a ↔
    ∃ (c : Code) (p : List Bool), elen c + p.length ≤ (Nat.unpair a).2 ∧
      (Nat.unpair a).1 ∈ pfy c (bitsToNat p) := by
  unfold kleB
  constructor
  · intro h
    obtain ⟨c, p, hmem, hlen⟩ := exists_min_KB (Nat.unpair a).1
    exact ⟨c, p, hlen ▸ h, hmem⟩
  · rintro ⟨c, p, hlen, hmem⟩
    exact (KB_le hmem).trans hlen

/-! ## `pfy`'s output is reached at some finite stage -/

/-- **`pfy`'s value is witnessed at any accepting stage, not only the least one**: `evaln` never
changes a value once defined (`evaln_mono`), so the value read off at the least accepting stage
(`pfy`'s own definition) agrees with the value read off at any later one. -/
theorem mem_pfy_iff_exists_stage (c : Code) (n x : ℕ) :
    x ∈ pfy c n ↔ ∃ k, n ∈ acceptedList c k ∧ evaln k c n = some x := by
  unfold pfy
  split
  · rename_i hex
    rw [Part.mem_some_iff]
    constructor
    · intro hx
      refine ⟨Nat.find hex, Nat.find_spec hex, ?_⟩
      rw [hx]
      exact (Option.some_get _).symm
    · rintro ⟨k, hk, hev⟩
      have hfindSome := evaln_isSome_of_mem_acceptedList c (Nat.find hex) (Nat.find_spec hex)
      obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp hfindSome
      have hyk : evaln k c n = some y := evaln_mono (Nat.find_le hk) hy
      rw [hev] at hyk
      have hxy : x = y := by injection hyk
      rw [hxy]
      exact (Option.get_of_mem hfindSome hy).symm
  · rename_i hnex
    constructor
    · intro hx
      exact absurd hx (Part.notMem_none x)
    · rintro ⟨k, hk, -⟩
      exact absurd ⟨k, hk⟩ hnex

/-! ## `kleB` is computably enumerable -/

/-- The dovetailed search: a witness code `c`, a binary argument `p` and a step budget `k`, all
of it decidable — the length bound, `p` accepted by stage `k`, and `k` steps of `c` on `p`
reaching the coded value. -/
private abbrev kleBSearch : ((ℕ × Code) × List Bool) × ℕ → Prop := fun x =>
  elen x.1.1.2 + x.1.2.length ≤ (Nat.unpair x.1.1.1).2 ∧
    bitsToNat x.1.2 ∈ acceptedList x.1.1.2 x.2 ∧
    evaln x.2 x.1.1.2 (bitsToNat x.1.2) = some (Nat.unpair x.1.1.1).1

private theorem primrec_kleBSearch : Primrec fun x => decide (kleBSearch x) := by
  have ha : Primrec fun x : ((ℕ × Code) × List Bool) × ℕ => x.1.1.1 :=
    Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
  have hc : Primrec fun x : ((ℕ × Code) × List Bool) × ℕ => x.1.1.2 :=
    Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
  have hp : Primrec fun x : ((ℕ × Code) × List Bool) × ℕ => x.1.2 :=
    Primrec.snd.comp Primrec.fst
  have hk : Primrec fun x : ((ℕ × Code) × List Bool) × ℕ => x.2 := Primrec.snd
  have hunpair2 : Primrec fun x : ((ℕ × Code) × List Bool) × ℕ => (Nat.unpair x.1.1.1).2 :=
    Primrec.snd.comp (Primrec.unpair.comp ha)
  have hunpair1 : Primrec fun x : ((ℕ × Code) × List Bool) × ℕ => (Nat.unpair x.1.1.1).1 :=
    Primrec.fst.comp (Primrec.unpair.comp ha)
  have hbn : Primrec fun x : ((ℕ × Code) × List Bool) × ℕ => bitsToNat x.1.2 :=
    primrec_bitsToNat.comp hp
  have hL : Primrec fun x : ((ℕ × Code) × List Bool) × ℕ => elen x.1.1.2 + x.1.2.length :=
    Primrec.nat_add.comp (primrec_elen.comp hc) (Primrec.list_length.comp hp)
  have hLe : Primrec fun x : ((ℕ × Code) × List Bool) × ℕ =>
      decide (elen x.1.1.2 + x.1.2.length ≤ (Nat.unpair x.1.1.1).2) :=
    Primrec.nat_le.decide.comp hL hunpair2
  have hAccList : Primrec fun x : ((ℕ × Code) × List Bool) × ℕ => acceptedList x.1.1.2 x.2 :=
    Primrec.comp primrec₂_acceptedList (hc.pair hk)
  have hmem : Primrec fun x : ((ℕ × Code) × List Bool) × ℕ =>
      decide (bitsToNat x.1.2 ∈ acceptedList x.1.1.2 x.2) :=
    (primrec_mem_list.comp hAccList hbn).decide
  have hEv : Primrec fun x : ((ℕ × Code) × List Bool) × ℕ => evaln x.2 x.1.1.2 (bitsToNat x.1.2) :=
    Primrec.comp Nat.Partrec.Code.primrec_evaln ((hk.pair hc).pair hbn)
  have hSome : Primrec fun x : ((ℕ × Code) × List Bool) × ℕ =>
      (some (Nat.unpair x.1.1.1).1 : Option ℕ) := Primrec.option_some.comp hunpair1
  have hev : Primrec fun x : ((ℕ × Code) × List Bool) × ℕ =>
      decide (evaln x.2 x.1.1.2 (bitsToNat x.1.2) = some (Nat.unpair x.1.1.1).1) :=
    (Primrec.eq.comp hEv hSome).decide
  exact (Primrec.and.comp (Primrec.and.comp hLe hmem) hev).of_eq fun x => by
    simp [kleBSearch, Bool.and_assoc]

private theorem rePred_kleBSearch : REPred kleBSearch :=
  (Primrec.primrecPred primrec_kleBSearch).computablePred.to_re

/-- **`kleB` is computably enumerable**: dovetail over a witness code, a binary argument and a
step budget, testing the length bound and `pfy`'s stage-bounded membership by `ComputablePred`.
The twin of `rePred_kle` at `KB` in place of `K_bitlen`. -/
theorem rePred_kleB : REPred kleB := by
  have hR1 : REPred fun x : (ℕ × Code) × List Bool => ∃ k : ℕ, kleBSearch (x, k) :=
    REPred.projection rePred_kleBSearch
  have hR2 : REPred fun y : ℕ × Code => ∃ (p : List Bool) (k : ℕ), kleBSearch ((y, p), k) :=
    REPred.projection hR1
  have hR3 : REPred fun a : ℕ => ∃ (c : Code) (p : List Bool) (k : ℕ),
      kleBSearch (((a, c), p), k) := REPred.projection hR2
  refine hR3.of_eq fun a => ?_
  rw [kleB_iff_exists]
  constructor
  · rintro ⟨c, p, k, hlen, hk, hev⟩
    exact ⟨c, p, hlen, (mem_pfy_iff_exists_stage c (bitsToNat p) (Nat.unpair a).1).mpr ⟨k, hk, hev⟩⟩
  · rintro ⟨c, p, hlen, hmem⟩
    obtain ⟨k, hk, hev⟩ := (mem_pfy_iff_exists_stage c (bitsToNat p) (Nat.unpair a).1).mp hmem
    exact ⟨c, p, k, hlen, hk, hev⟩

-- `rePred_kleB`'s own axiom guard: kept here, not in `ALT/AxiomAuditMathlib.lean`, because that
-- umbrella never imports `ChaitinPrefix.lean` (it is deliberately Mathlib-only, per its own
-- import list) and `kleB` lives there — mirrors `EParserSpec`'s guard, kept in
-- `ALT/SerializationParse.lean` itself for the same reason.
set_option linter.style.longLine false in
/-- info: 'KolmogorovComplexity.rePred_kleB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms rePred_kleB

/-! ## The assembly: both leaves are present -/

/-- **Chaitin's bound, unconditional, on `KB`.** `chaitin_bound_KB_of` at the now-proved
`eParserSpec`. -/
theorem chaitin_bound_KB : ∃ c₀ : Code, ∀ e : Code,
    (∀ s n, (e.eval (Nat.pair s n)).Dom → n < KB s) →
    ∀ s n, (e.eval (Nat.pair s n)).Dom →
      ∀ (d : Code) (q : List Bool), Encodable.encode e ∈ pfy d (bitsToNat q) →
        n < elen c₀ + (elen d + q.length) :=
  chaitin_bound_KB_of eParserSpec

/-- **Chaitin's bound, unconditional, minimized to `KB`'s own value.** -/
theorem chaitin_bound_KB_min : ∃ c₀ : Code, ∀ e : Code,
    (∀ s n, (e.eval (Nat.pair s n)).Dom → n < KB s) →
    ∀ s n, (e.eval (Nat.pair s n)).Dom → n < elen c₀ + KB (Encodable.encode e) :=
  chaitin_bound_KB_of_min eParserSpec

/-- **Chaitin's incompleteness theorem, additive form, unconditional.** `chaitin_theoremB_of` at
the now-proved `eParserSpec` and `rePred_kleB`. -/
theorem chaitin_theoremB : ∃ c₀ : Code, ∀ (T : ArithmeticTheory) [T.Δ₁] [𝗥₀ ⪯ T]
    [FFL.Entailment.Consistent T] (e : Code),
    (∀ a, (e.eval a).Dom ↔ T ⊢ chaitinSentenceB (Nat.unpair a).1 (Nat.unpair a).2) →
    ∀ s n, T ⊢ chaitinSentenceB s n → n < elen c₀ + KB (Encodable.encode e) :=
  chaitin_theoremB_of eParserSpec rePred_kleB

/-- Transported to any recursively enumerable, consistent extension of `𝗥₀`, unconditional. -/
theorem chaitin_theoremB_RE : ∃ c₀ : Code, ∀ (T : ArithmeticTheory) [T.RE] [𝗥₀ ⪯ T]
    [FFL.Entailment.Consistent T] (e : Code),
    (∀ a, (e.eval a).Dom ↔ T ⊢ chaitinSentenceB (Nat.unpair a).1 (Nat.unpair a).2) →
    ∀ s n, T ⊢ chaitinSentenceB s n → n < elen c₀ + KB (Encodable.encode e) :=
  chaitin_theoremB_of_RE eParserSpec rePred_kleB

/-- **A theory's `chaitinSentenceB`-provability predicate is exhibited by a `Code`**, not only
asserted enumerable: `rePred_provable_chaitinB`'s `REPred`, unpacked through `REPred.iff'` into a
partial `Unit`-valued function, then through `Nat.Partrec.Code.exists_code` into a `Code` whose
own halting domain agrees — the shape `chaitin_bound`'s proof opens with. -/
theorem exists_enumerator_chaitinB (T : ArithmeticTheory) [T.Δ₁] :
    ∃ e : Code, ∀ a, (e.eval a).Dom ↔ T ⊢ chaitinSentenceB (Nat.unpair a).1 (Nat.unpair a).2 := by
  obtain ⟨f, hf, hfQ⟩ := REPred.iff'.mp (rePred_provable_chaitinB T)
  have hf' : Partrec fun a => (f a).map fun _ : Unit => (0 : ℕ) :=
    Partrec.map hf (Computable.const 0).to₂
  obtain ⟨e, he⟩ := Nat.Partrec.Code.exists_code.1 (Partrec.nat_iff.mp hf')
  refine ⟨e, fun a => ?_⟩
  rw [congrFun he a]
  change (f a).Dom ↔ _
  exact (hfQ a).symm

/-- **`chaitin_theoremB`'s hypotheses are jointly satisfiable**: the concrete theory `𝗣𝗔⁻`
(finite, `Δ₁` via `Theory.Δ₁.ofFinite`, `𝗥₀ ⪯ 𝗣𝗔⁻` and consistent, all found by instance search —
the same witness `GodelComplete.lean` uses) meets every instance binder at once, together with
its own enumerator. -/
theorem chaitin_theoremB_nonvacuous :
    ∃ (T : ArithmeticTheory) (_ : T.Δ₁) (_ : (𝗥₀ : ArithmeticTheory) ⪯ T)
      (_ : FFL.Entailment.Consistent T) (e : Code),
      ∀ a, (e.eval a).Dom ↔ T ⊢ chaitinSentenceB (Nat.unpair a).1 (Nat.unpair a).2 := by
  obtain ⟨e, he⟩ := exists_enumerator_chaitinB 𝗣𝗔⁻
  exact ⟨𝗣𝗔⁻, inferInstance, inferInstance, inferInstance, e, he⟩

/-- **The counting bound on `KB`**: at most finitely many naturals are describable within a fixed
budget — `KB`'s twin of `AdditiveComplexity.finite_KE_le`, over `E c ++ q` (injective by
`E_append_inj`) in place of `E c` alone, since a `KB`-description carries an argument too. -/
theorem setOf_KB_le_finite (L : ℕ) : {x : ℕ | KB x ≤ L}.Finite := by
  have hinj : Function.Injective fun x : ℕ => (minDescCode x, minDescArg x) := by
    intro x y hxy
    have hx := (minDesc_spec x).1
    have hy := (minDesc_spec y).1
    rw [Prod.mk.injEq] at hxy
    rw [hxy.1, hxy.2] at hx
    exact Part.mem_unique hx hy
  have hinj' : Function.Injective fun x : ℕ => E (minDescCode x) ++ minDescArg x := by
    intro x y hxy
    have := (E_append_inj (minDescCode x) (minDescCode y) (minDescArg x) (minDescArg y) hxy).1
    exact hinj (Prod.ext this
      ((E_append_inj (minDescCode x) (minDescCode y) (minDescArg x) (minDescArg y) hxy).2))
  have hsub : {x : ℕ | KB x ≤ L} ⊆
      (fun x => E (minDescCode x) ++ minDescArg x) ⁻¹' ↑(bitLists L) := fun x hx =>
    mem_bitLists (by
      have h2 : (E (minDescCode x)).length + (minDescArg x).length = KB x := (minDesc_spec x).2
      simp only [List.length_append]
      rw [h2]
      exact hx)
  exact Set.Finite.subset (Set.Finite.preimage hinj'.injOn (bitLists L).finite_toSet) hsub

/-- **`KB`'s true-and-unprovable family, at the additive constant.** `KB`'s twin of
`chaitin_true_unprovable`: at every `s` past the constant `elen c₀ + KB (Encodable.encode e)`,
the sentence "the prefix complexity of `s` exceeds that constant" is true in `ℕ` yet unprovable
in `T`. -/
theorem chaitin_true_unprovableB : ∃ c₀ : Code, ∀ (T : ArithmeticTheory) [T.Δ₁] [𝗥₀ ⪯ T]
    [FFL.Entailment.Consistent T] (e : Code),
    (∀ a, (e.eval a).Dom ↔ T ⊢ chaitinSentenceB (Nat.unpair a).1 (Nat.unpair a).2) →
    ∀ s, elen c₀ + KB (Encodable.encode e) < KB s →
      (ℕ↓[ℒₒᵣ] ⊧ chaitinSentenceB s (elen c₀ + KB (Encodable.encode e))) ∧
        T ⊬ chaitinSentenceB s (elen c₀ + KB (Encodable.encode e)) := by
  obtain ⟨c₀, hc₀⟩ := chaitin_theoremB
  refine ⟨c₀, fun T _ _ _ e henum s hs => ⟨?_, fun h => ?_⟩⟩
  · exact (models_chaitinSentenceB_iff rePred_kleB s _).mpr hs
  · exact absurd (hc₀ T e henum s _ h) (_root_.lt_irrefl _)

end KolmogorovComplexity
