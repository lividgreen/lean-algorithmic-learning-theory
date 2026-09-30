/-
Copyright (c) 2026 Mykola Palamarchuk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mykola Palamarchuk
-/
module

public import ALT.ChaitinIncompleteness
public import ALT.BitStringPrimrec
public import ALT.CodingTheoremBitwise

-- Formal-check file, not Mathlib-destined: opt out of the house-style header linter.
set_option linter.style.header false

/-!
# Chaitin's incompleteness theorem, additive form on a prefix machine ([Decoupling] §6.6)

Provenance: [Decoupling] §6.6's closing paragraph, over the prefix complexity `KB` of
`ALT/PrefixMachine.lean` in place of the index bit-length `K_bitlen` of
`ALT/ChaitinIncompleteness.lean`. That module's closing paragraph reads: "The constant is
named, not numeric: the bit-length of a fixed point Kleene's recursion theorem supplies
existentially, and nothing here relates it to the description length of `T` itself." This
module closes that boundary: on `KB`, a theory's own enumerator is charged at its OWN prefix
complexity, so the bound is additive in the theory's description length, `elen c₀` fixed once
for every theory.

Status: conditional on two leaf propositions that enter as explicit hypotheses and are not
proved here: `EParserSpec` (a computable, self-delimiting parser recovering a serialized
machine and its trailing argument from a `KB`-description) and `REPred kleB` (the Chaitin
predicate on `KB`'s coded pairs is computably enumerable) — each proved in its own companion
module.

## What this establishes
* `EParserSpec`, `kleB`, `kleB_iff` — the leaf statement and the predicate, read at a coded
  pair as `KB s ≤ n`, exactly as `kle`/`kle_iff` in `ALT/ChaitinIncompleteness.lean` read
  `K_bitlen s ≤ n`.
* `chaitinSentenceB`, `models_chaitinSentenceB_iff` — the sentence "`KB(s) > n`", `kle`'s twin
  at `KB`, given `REPred kleB` as a hypothesis rather than proved in-file.
* `rePred_provable_chaitinB`, `chaitin_soundB` — the theory-relative steps, from `[T.Δ₁]`
  alone, respectively `[𝗥₀ ⪯ T]` and consistency alone, mirroring the `K_bitlen` layer line
  for line.
* `chaitin_bound_KB_of`, `chaitin_bound_KB_of_min` — the abstract Berry bound, given
  `EParserSpec`: a computably enumerable relation asserting only true `KB` bounds is bounded
  by `elen c₀ + (elen d + q.length)` at every description `(d, q)` of the enumerator's own
  code, hence by `elen c₀ + KB (Encodable.encode e)`.
* `chaitin_theoremB_of`, `chaitin_theoremB_of_RE` — the theory-relative form, at `[T.Δ₁]`
  respectively `[T.RE]` (transported through Foundation's `T.craig`): the constant is
  `elen c₀ + KB (Encodable.encode e)`, `elen c₀` fixed once for every theory and
  `KB (Encodable.encode e)` the theory's OWN prefix complexity through its enumerator —
  Chaitin's additive form, closing the boundary above.

## What this does NOT establish (flagged)
* `EParserSpec` and `REPred kleB` are hypotheses, each discharged in its own companion
  module.
* The joint-satisfiability witness of these two hypotheses is exactly their two proofs, and
  is stated once both are in the tree, not here.
* Chaitin's own clause (a) — a uniform additive constant over sound systems' AXIOM size — is
  not restated; the constant here is a program's own prefix complexity over `T`'s enumerator,
  not `T`'s syntax.
-/


@[expose] public section

namespace KolmogorovComplexity

open Nat.Partrec Nat.Partrec.Code AdditiveComplexity PrefixMachine
open FFL.FirstOrder FFL.FirstOrder.Arithmetic

/-! ## The two leaf propositions -/

/-- **The parser specification.** A computable parser recovering a serialized machine `e` and its
trailing argument `r` from any description `E e ++ r` — and ONLY from a description of that
shape. -/
def EParserSpec : Prop :=
  ∃ parse : List Bool → Option (Code × List Bool), Primrec parse ∧
    (∀ e r, parse (E e ++ r) = some (e, r)) ∧
    (∀ w e r, parse w = some (e, r) → w = E e ++ r)

/-- **The predicate.** "The prefix complexity of `(Nat.unpair a).1` is at most
`(Nat.unpair a).2`" — `kle`'s twin at `KB` in place of `K_bitlen`. `REPred kleB`, the second
leaf proposition, enters below as an explicit hypothesis rather than a proof in this file. -/
def kleB (a : ℕ) : Prop := KB (Nat.unpair a).1 ≤ (Nat.unpair a).2

theorem kleB_iff (s n : ℕ) : kleB (Nat.pair s n) ↔ KB s ≤ n := by
  unfold kleB
  rw [Nat.unpair_pair]

/-- The sentence "the prefix complexity of `s` exceeds `n`": the negation of Foundation's Σ₁
representation of `kleB`, at the numeral of the coded pair — `chaitinSentence`'s twin at
`KB`. -/
noncomputable def chaitinSentenceB (s n : ℕ) : ArithmeticSentence :=
  ∼(codeOfREPred kleB)/[Nat.pair s n]

theorem models_chaitinSentenceB_iff (hre : REPred kleB) (s n : ℕ) :
    (ℕ↓[ℒₒᵣ] ⊧ chaitinSentenceB s n) ↔ n < KB s := by
  have h1 : (ℕ↓[ℒₒᵣ] ⊧ (codeOfREPred kleB)/[Nat.pair s n]) ↔ kleB (Nat.pair s n) := by
    simpa [models_iff, Semiformula.eval_substs, Matrix.constant_eq_singleton] using
      codeOfREPred_spec hre (x := Nat.pair s n)
  unfold chaitinSentenceB
  simp only [FFL.Semantics.Not.models_not] at h1 ⊢
  rw [h1, kleB_iff, not_le]

variable (T : ArithmeticTheory) [T.Δ₁] [𝗥₀ ⪯ T] [FFL.Entailment.Consistent T]

omit [𝗥₀ ⪯ T] [FFL.Entailment.Consistent T] in
open FFL.Entailment Bootstrapping Bootstrapping.Arithmetic FFL.FirstOrder.Bounding in
/-- The provability predicate over `T` at the fixed formula `codeOfREPred kleB`, varied over
the substituted numeral, is recursively enumerable — needs only `[T.Δ₁]`, exactly as
`rePred_provable_chaitin`; no `REPred kleB` hypothesis is needed here either, since the
argument is purely about `T`'s own provability predicate being Σ₁-definable. -/
theorem rePred_provable_chaitinB :
    REPred fun a : ℕ => T ⊢ chaitinSentenceB (Nat.unpair a).1 (Nat.unpair a).2 := by
  have heq : (fun a : ℕ => T ⊢ chaitinSentenceB (Nat.unpair a).1 (Nat.unpair a).2) =
      fun a : ℕ => T ⊢ ∼(codeOfREPred kleB)/[a] := by
    funext a
    unfold chaitinSentenceB
    rw [Nat.pair_unpair a]
  rw [heq]
  have hS1 : 𝚺ᴬ₁-Predicate fun a : ℕ =>
      Provable T (neg ℒₒᵣ (subst ℒₒᵣ ?[numeral a]
        (⌜codeOfREPred kleB⌝ : ℕ))) := by
    definability
  refine (rePred_iff_sigma1.mpr hS1).of_eq (fun a => ?_)
  simp [←provable_iff_provable, Sentence.quote_def, Rewriting.emb_subst_eq_subst_coe₁,
    Semiformula.quote_def]

omit [T.Δ₁] in
/-- `T`'s consistency makes every provable Chaitin-on-`KB` sentence true, given `REPred
kleB` — the `KB` twin of `chaitin_sound`, needing only `[𝗥₀ ⪯ T]` and consistency (through
`sigma_one_completeness`), plus the leaf hypothesis to invoke
`models_chaitinSentenceB_iff`. -/
theorem chaitin_soundB (hre : REPred kleB) (s n : ℕ) (h : T ⊢ chaitinSentenceB s n) :
    n < KB s := by
  by_contra hcon
  push Not at hcon
  have hkleB : kleB (Nat.pair s n) := (kleB_iff s n).mpr hcon
  have hmod : ℕ↓[ℒₒᵣ] ⊧ (codeOfREPred kleB)/[Nat.pair s n] := by
    have h1 : (ℕ↓[ℒₒᵣ] ⊧ (codeOfREPred kleB)/[Nat.pair s n]) ↔ kleB (Nat.pair s n) := by
      simpa [models_iff, Semiformula.eval_substs,
        Matrix.constant_eq_singleton] using
        codeOfREPred_spec hre (x := Nat.pair s n)
    exact h1.mpr hkleB
  have hsig : ℬ[<, ℒₒᵣ].Hierarchy 𝚺 1
      (((codeOfREPred kleB)/[Nat.pair s n] : ArithmeticSentence)) := by
    simp [codeOfREPred, codeOfPartrec']
  have hpos : T ⊢ (codeOfREPred kleB)/[Nat.pair s n] :=
    sigma_one_completeness (σ := (codeOfREPred kleB)/[Nat.pair s n]) hsig hmod
  have hneg : T ⊢ ∼(codeOfREPred kleB)/[Nat.pair s n] := h
  exact FFL.Entailment.Consistent.not_bot (𝓢 := T) (by cl_prover [hpos, hneg])

/-! ## The abstract Berry bound on `KB`

The three `Nat.unpair` projections packing `(s, n, k)` into one natural, COPIED from
`ALT/ChaitinIncompleteness.lean`'s (file-private) `sOf`/`nOf`/`kOf` rather than exported
from there — `private` is file-scoped, so the two triples coexist without conflict. -/

private def sOf (m : ℕ) : ℕ := (Nat.unpair m).1

private def nOf (m : ℕ) : ℕ := (Nat.unpair (Nat.unpair m).2).1

private def kOf (m : ℕ) : ℕ := (Nat.unpair (Nat.unpair m).2).2

private theorem sOf_pack (s n k : ℕ) : sOf (Nat.pair s (Nat.pair n k)) = s := by
  simp [sOf, Nat.unpair_pair]

private theorem nOf_pack (s n k : ℕ) : nOf (Nat.pair s (Nat.pair n k)) = n := by
  simp [nOf, Nat.unpair_pair]

private theorem kOf_pack (s n k : ℕ) : kOf (Nat.pair s (Nat.pair n k)) = k := by
  simp [kOf, Nat.unpair_pair]

private theorem primrec_sOf : Primrec sOf := Primrec.fst.comp Primrec.unpair

private theorem primrec_nOf : Primrec nOf :=
  Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))

private theorem primrec_kOf : Primrec kOf :=
  Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))

set_option maxHeartbeats 4000000 in
-- The nested-bind `Partrec₂`/`fixed_point₂` elaboration over the `Code × List Bool` shape is
-- heavy in this imported environment, as in `chaitin_bound`; default 200k heartbeats is short.
/-- **Chaitin's bound, abstract form, on `KB`.** A computably enumerable relation that
asserts only TRUE `KB`-lower-bounds is bounded, at every `KB`-description `(d, q)` of its own
enumerator's code, by a FIXED `elen c₀` plus that description's own length —
`chaitin_bound`'s twin, with the search over `pfy` and the theory's enumerator entering
through the argument bits rather than as a fixed code. -/
theorem chaitin_bound_KB_of (hparse : EParserSpec) :
    ∃ c₀ : Code, ∀ e : Code,
      (∀ s n, (e.eval (Nat.pair s n)).Dom → n < KB s) →
      ∀ s n, (e.eval (Nat.pair s n)).Dom →
        ∀ (d : Code) (q : List Bool), Encodable.encode e ∈ pfy d (bitsToNat q) →
          n < elen c₀ + (elen d + q.length) := by
  obtain ⟨parse, hparsePrim, hparse2, hparse3⟩ := hparse
  -- Stage A: parse `natToBits m` as a candidate `KB`-description `(d, q)`.
  have hnatBits2 : Primrec fun a : Code × ℕ => natToBits a.2 :=
    primrec_natToBits.comp Primrec.snd
  have hparseNB : Primrec fun a : Code × ℕ => parse (natToBits a.2) :=
    hparsePrim.comp hnatBits2
  have hstage1' := Computable.ofOption hparseNB.to_comp
  have hstage1 :
      Partrec fun a : Code × ℕ => (parse (natToBits a.2) : Part (Code × List Bool)) :=
    hstage1'.of_eq fun _ => rfl
  -- Stage B: run `pfy d` on `q`'s bits, to get `x` (meant to be `Encodable.encode e`).
  have hg1 :
      Partrec₂ (fun (_ : Code × ℕ) (dq : Code × List Bool) => pfy dq.1 (bitsToNat dq.2)) := by
    have hmap : Primrec fun p : (Code × ℕ) × (Code × List Bool) => (p.2.1, bitsToNat p.2.2) :=
      (Primrec.fst.comp Primrec.snd).pair
        (primrec_bitsToNat.comp (Primrec.snd.comp Primrec.snd))
    exact (Partrec.comp pfy_partrec hmap.to_comp).of_eq fun _ => rfl
  have hbind1' := Partrec.bind hstage1 hg1
  have hbind1 : Partrec₂ (fun (c : Code) (m : ℕ) =>
      (parse (natToBits m) : Part (Code × List Bool)).bind fun dq =>
        pfy dq.1 (bitsToNat dq.2)) :=
    hbind1'.of_eq fun _ => rfl
  -- Stage C: decode `x` as a `Code` — the enumerator `e`.
  have hg2 : Partrec₂ (fun (_ : Code × ℕ) (x : ℕ) =>
      (Encodable.decode (α := Code) x : Part Code)) :=
    Computable.ofOption ((Computable.decode (α := Code)).comp Computable.snd)
  have hbind2' := Partrec.bind hbind1 hg2
  have hbind2 : Partrec₂ (fun (c : Code) (m : ℕ) =>
      ((parse (natToBits m) : Part (Code × List Bool)).bind fun dq =>
        pfy dq.1 (bitsToNat dq.2)).bind fun x => (Encodable.decode (α := Code) x : Part Code)) :=
    hbind2'.of_eq fun _ => rfl
  -- Stage D: run `chaitin_bound`'s own Berry search over the DECODED enumerator `e`, at the
  -- self-referential threshold `elen c + (natToBits m).length` — built in `Primrec` throughout.
  have hg3 : Partrec₂ (fun (a : Code × ℕ) (e : Code) => (Nat.rfind fun w =>
      Part.some (decide (elen a.1 + (natToBits a.2).length ≤ nOf w) &&
        (evaln (kOf w) e (Nat.pair (sOf w) (nOf w))).isSome)).map sOf) := by
    have c2 : Primrec fun t : ((Code × ℕ) × Code) × ℕ => nOf t.2 :=
      primrec_nOf.comp Primrec.snd
    have c3 : Primrec fun t : ((Code × ℕ) × Code) × ℕ => kOf t.2 :=
      primrec_kOf.comp Primrec.snd
    have c4 : Primrec fun t : ((Code × ℕ) × Code) × ℕ => sOf t.2 :=
      primrec_sOf.comp Primrec.snd
    have ce : Primrec fun t : ((Code × ℕ) × Code) × ℕ => t.1.2 :=
      Primrec.snd.comp Primrec.fst
    have hthresh : Primrec fun t : ((Code × ℕ) × Code) × ℕ =>
        elen t.1.1.1 + (natToBits t.1.1.2).length := by
      have hc1 : Primrec fun t : ((Code × ℕ) × Code) × ℕ => elen t.1.1.1 :=
        primrec_elen.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
      have hc2 : Primrec fun t : ((Code × ℕ) × Code) × ℕ => (natToBits t.1.1.2).length :=
        Primrec.list_length.comp
          (primrec_natToBits.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)))
      exact Primrec.nat_add.comp hc1 hc2
    have hle : Primrec fun t : ((Code × ℕ) × Code) × ℕ =>
        decide (elen t.1.1.1 + (natToBits t.1.1.2).length ≤ nOf t.2) :=
      Primrec.nat_le.decide.comp hthresh c2
    have hpairSN : Primrec fun t : ((Code × ℕ) × Code) × ℕ => Nat.pair (sOf t.2) (nOf t.2) :=
      Primrec₂.natPair.comp c4 c2
    have hev : Primrec fun t : ((Code × ℕ) × Code) × ℕ =>
        evaln (kOf t.2) t.1.2 (Nat.pair (sOf t.2) (nOf t.2)) :=
      Nat.Partrec.Code.primrec_evaln.comp ((c3.pair ce).pair hpairSN)
    have hisSome : Primrec fun t : ((Code × ℕ) × Code) × ℕ =>
        (evaln (kOf t.2) t.1.2 (Nat.pair (sOf t.2) (nOf t.2))).isSome :=
      Primrec.option_isSome.comp hev
    have hcond : Primrec₂ (fun (a : (Code × ℕ) × Code) (w : ℕ) =>
        decide (elen a.1.1 + (natToBits a.1.2).length ≤ nOf w) &&
          (evaln (kOf w) a.2 (Nat.pair (sOf w) (nOf w))).isSome) :=
      Primrec.and.comp hle hisSome
    have hrfindp : Partrec₂ (fun (a : (Code × ℕ) × Code) (w : ℕ) =>
        Part.some (decide (elen a.1.1 + (natToBits a.1.2).length ≤ nOf w) &&
          (evaln (kOf w) a.2 (Nat.pair (sOf w) (nOf w))).isSome)) := hcond.to_comp.partrec₂
    have hrfind' := Partrec.rfind hrfindp
    have hrfind : Partrec fun a : (Code × ℕ) × Code => Nat.rfind fun w =>
        Part.some (decide (elen a.1.1 + (natToBits a.1.2).length ≤ nOf w) &&
          (evaln (kOf w) a.2 (Nat.pair (sOf w) (nOf w))).isSome) := hrfind'.of_eq fun _ => rfl
    -- The `sOf ∘ snd` projection, ascribed `Primrec₂` DIRECTLY (rather than left for
    -- `Partrec.map` to bridge from a flat `Computable`): at this triple-nested domain,
    -- bridging inside `Partrec.map`'s own elaboration is the expensive `whnf` unification.
    have hsOfSnd : Primrec₂ (fun (_ : (Code × ℕ) × Code) (w : ℕ) => sOf w) :=
      primrec_sOf.comp Primrec.snd
    have hmapd' := Partrec.map hrfind hsOfSnd.to_comp
    exact hmapd'.of_eq fun _ => rfl
  have hbind3' := Partrec.bind hbind2 hg3
  have hbind3 : Partrec₂ (fun (c : Code) (m : ℕ) =>
      (((parse (natToBits m) : Part (Code × List Bool)).bind fun dq =>
        pfy dq.1 (bitsToNat dq.2)).bind fun x =>
          (Encodable.decode (α := Code) x : Part Code)).bind
        fun e => (Nat.rfind fun w =>
          Part.some (decide (elen c + (natToBits m).length ≤ nOf w) &&
            (evaln (kOf w) e (Nat.pair (sOf w) (nOf w))).isSome)).map sOf) :=
    hbind3'.of_eq fun _ => rfl
  obtain ⟨c₀, hc₀⟩ := fixed_point₂ hbind3
  -- `c₀`'s halting domain is prefix-free: any accepted `m` decodes, through `parse`, to a
  -- `(d, q)` with `q` itself a valid `pfy d`-argument; the parse spec plus `pfy_prefixFree`
  -- pin `d` and `q` uniquely from any prefix relation between two such descriptions.
  have hdecomp : ∀ m : ℕ, m ∈ c₀.eval.Dom →
      ∃ (d : Code) (q : List Bool), natToBits m = E d ++ q ∧ q ∈ natToBits '' (pfy d).Dom := by
    intro m hm
    obtain ⟨v, hv⟩ := Part.dom_iff_mem.mp hm
    rw [congrFun hc₀ m] at hv
    -- The bind chain is `((A.bind B).bind C).bind D`: peel outermost-first, so the FIRST
    -- obtain lands on `C`'s value (the decoded enumerator), the THIRD on `A`'s (the parse).
    obtain ⟨e', he', _⟩ := Part.mem_bind_iff.mp hv
    obtain ⟨x, hx, _⟩ := Part.mem_bind_iff.mp he'
    obtain ⟨dq, hdq, hBdq⟩ := Part.mem_bind_iff.mp hx
    have hparse_eq : parse (natToBits m) = some dq := Part.mem_ofOption.mp hdq
    have hspec : natToBits m = E dq.1 ++ dq.2 := hparse3 (natToBits m) dq.1 dq.2 hparse_eq
    refine ⟨dq.1, dq.2, hspec, ?_⟩
    have hbcdom : bitsToNat dq.2 ∈ (pfy dq.1).Dom := Part.dom_iff_mem.mpr ⟨x, hBdq⟩
    exact ⟨bitsToNat dq.2, hbcdom, natToBits_bitsToNat _⟩
  have hpf : PrefixFree (natToBits '' c₀.eval.Dom) := by
    intro p₁ hp₁ p₂ hp₂ hpre
    obtain ⟨m₁, hm₁, rfl⟩ := hp₁
    obtain ⟨m₂, hm₂, rfl⟩ := hp₂
    obtain ⟨d₁, q₁, heq₁, hq₁⟩ := hdecomp m₁ hm₁
    obtain ⟨d₂, q₂, heq₂, hq₂⟩ := hdecomp m₂ hm₂
    rw [heq₁, heq₂] at hpre ⊢
    obtain ⟨r, hr⟩ := hpre
    rw [List.append_assoc] at hr
    obtain ⟨hd, hqr⟩ := E_append_inj d₁ d₂ (q₁ ++ r) q₂ hr
    subst hd
    have hq12 : q₁ = q₂ := pfy_prefixFree d₁ q₁ hq₁ q₂ hq₂ ⟨r, hqr⟩
    rw [hq12]
  have hpfy_eq : pfy c₀ = c₀.eval := pfy_eq_of_prefixFree c₀ hpf
  refine ⟨c₀, fun e hsound s n hdom d q hqd => ?_⟩
  by_contra hcon
  push Not at hcon
  -- `m := bitsToNat (E d ++ q)` re-decodes, through `parse`, to exactly `(d, q)`.
  set m : ℕ := bitsToNat (E d ++ q) with hmdef
  have hnb : natToBits m = E d ++ q := natToBits_bitsToNat _
  have hparse_m : parse (natToBits m) = some (d, q) := by rw [hnb]; exact hparse2 d q
  have hdec : (Encodable.decode (α := Code) (Encodable.encode e) : Option Code) = some e :=
    Encodable.encodek e
  have hlenm : (natToBits m).length = elen d + q.length := by
    rw [hnb]; simp [elen]
  set p₀ : ℕ →. Bool := fun w =>
      Part.some (decide (elen c₀ + (natToBits m).length ≤ nOf w) &&
        (evaln (kOf w) e (Nat.pair (sOf w) (nOf w))).isSome) with hp₀def
  -- A witness for the search: `e`'s own halting at `(s, n)`, with a sufficient step budget.
  obtain ⟨v, hv⟩ := Part.dom_iff_mem.mp hdom
  obtain ⟨k, hk⟩ := evaln_complete.1 hv
  have hmem : true ∈ p₀ (Nat.pair s (Nat.pair n k)) := by
    simp only [hp₀def, Part.mem_some_iff]
    rw [sOf_pack, nOf_pack, kOf_pack, hlenm]
    simpa [hcon] using Option.isSome_iff_exists.mpr ⟨_, hk⟩
  have hdomrf : (Nat.rfind p₀).Dom := by
    rw [Nat.rfind_dom]
    exact ⟨Nat.pair s (Nat.pair n k), hmem, fun {_} _ => trivial⟩
  set w : ℕ := (Nat.rfind p₀).get hdomrf with hwdef
  have hwspec : true ∈ p₀ w := Nat.rfind_spec (Part.get_mem hdomrf)
  have hwspec' : elen c₀ + (natToBits m).length ≤ nOf w ∧
      (evaln (kOf w) e (Nat.pair (sOf w) (nOf w))).isSome := by
    simpa [hp₀def, Bool.and_eq_true] using hwspec
  have hQw : (e.eval (Nat.pair (sOf w) (nOf w))).Dom := by
    rw [Part.dom_iff_mem]
    obtain ⟨v', hv'⟩ := Option.isSome_iff_exists.mp hwspec'.2
    exact ⟨v', evaln_sound hv'⟩
  have hsoundw : nOf w < KB (sOf w) := hsound (sOf w) (nOf w) hQw
  -- `c₀.eval m` reproduces the SAME search, since `m` decodes to exactly `(d, q, e)`.
  have hval : c₀.eval m = Part.some (sOf w) := by
    rw [congrFun hc₀ m]
    have hpart1 : (parse (natToBits m) : Part (Code × List Bool)) = Part.some (d, q) := by
      rw [Part.eq_some_iff, Part.mem_ofOption]; exact hparse_m
    have hpart2 : pfy d (bitsToNat q) = Part.some (Encodable.encode e) :=
      Part.eq_some_iff.mpr hqd
    have hpart3 : (Encodable.decode (α := Code) (Encodable.encode e) : Part Code) =
        Part.some e := by
      rw [Part.eq_some_iff, Part.mem_ofOption]; exact hdec
    rw [hpart1, Part.bind_some, hpart2, Part.bind_some, hpart3, Part.bind_some]
    have hrfind_eq : Nat.rfind p₀ = Part.some w := Part.get_eq_iff_eq_some.mp hwdef.symm
    change (Nat.rfind p₀).map sOf = Part.some (sOf w)
    rw [hrfind_eq]
    simp
  have hmemphi : sOf w ∈ pfy c₀ (bitsToNat (natToBits m)) := by
    rw [bitsToNat_natToBits, hpfy_eq, hval]
    exact Part.mem_some _
  have hKBle : KB (sOf w) ≤ elen c₀ + (natToBits m).length := KB_le hmemphi
  have hchain : KB (sOf w) ≤ nOf w := hKBle.trans hwspec'.1
  omega

/-- **Chaitin's bound, minimized to `KB`'s own value**: replacing the arbitrary description
`(d, q)` of `e`'s code by an OPTIMAL one (`exists_min_KB`), the bound reads directly against
`KB (Encodable.encode e)`. -/
theorem chaitin_bound_KB_of_min (hparse : EParserSpec) :
    ∃ c₀ : Code, ∀ e : Code,
      (∀ s n, (e.eval (Nat.pair s n)).Dom → n < KB s) →
      ∀ s n, (e.eval (Nat.pair s n)).Dom → n < elen c₀ + KB (Encodable.encode e) := by
  obtain ⟨c₀, hc₀⟩ := chaitin_bound_KB_of hparse
  refine ⟨c₀, fun e hsound s n hdom => ?_⟩
  obtain ⟨d, q, hdq, hlen⟩ := exists_min_KB (Encodable.encode e)
  have hb := hc₀ e hsound s n hdom d q hdq
  rwa [hlen] at hb

/-! ## Transport to a theory's own provability, at the theory's OWN enumerator -/

/-- **Chaitin's incompleteness theorem, additive form, over a `Δ₁`-axiomatized theory.** The
constant `elen c₀ + KB (Encodable.encode e)` splits into a FIXED part (`elen c₀`, one Berry
program for every theory) and the theory's OWN prefix complexity, through any enumerator `e`
of its provable sentences of this form. -/
theorem chaitin_theoremB_of (hparse : EParserSpec) (hre : REPred kleB) :
    ∃ c₀ : Code, ∀ (T : ArithmeticTheory) [T.Δ₁] [𝗥₀ ⪯ T] [FFL.Entailment.Consistent T]
      (e : Code),
      (∀ a, (e.eval a).Dom ↔ T ⊢ chaitinSentenceB (Nat.unpair a).1 (Nat.unpair a).2) →
      ∀ s n, T ⊢ chaitinSentenceB s n → n < elen c₀ + KB (Encodable.encode e) := by
  obtain ⟨c₀, hc₀⟩ := chaitin_bound_KB_of_min hparse
  refine ⟨c₀, fun T => ?_⟩
  intro _ _ _ e henum s n hprov
  have hdomsn : (e.eval (Nat.pair s n)).Dom := by
    rw [henum, Nat.unpair_pair]; exact hprov
  have hsound : ∀ s' n', (e.eval (Nat.pair s' n')).Dom → n' < KB s' := by
    intro s' n' hdom'
    have hprov' := (henum (Nat.pair s' n')).mp hdom'
    rw [Nat.unpair_pair] at hprov'
    exact chaitin_soundB T hre s' n' hprov'
  exact hc₀ e hsound s n hdomsn

/-- **Transported to any recursively enumerable, consistent extension of `𝗥₀`**, via
Foundation's `T.craig`, exactly as `chaitin_theorem_of_RE` — the SAME constant,
`T.craig ≊ T`. -/
theorem chaitin_theoremB_of_RE (hparse : EParserSpec) (hre : REPred kleB) :
    ∃ c₀ : Code, ∀ (T : ArithmeticTheory) [T.RE] [𝗥₀ ⪯ T] [FFL.Entailment.Consistent T]
      (e : Code),
      (∀ a, (e.eval a).Dom ↔ T ⊢ chaitinSentenceB (Nat.unpair a).1 (Nat.unpair a).2) →
      ∀ s n, T ⊢ chaitinSentenceB s n → n < elen c₀ + KB (Encodable.encode e) := by
  obtain ⟨c₀, hc₀⟩ := chaitin_theoremB_of hparse hre
  refine ⟨c₀, fun T => ?_⟩
  intro _ _ _ e henum s n h
  have henum' : ∀ a, (e.eval a).Dom ↔
      T.craig ⊢ chaitinSentenceB (Nat.unpair a).1 (Nat.unpair a).2 := fun a =>
    (henum a).trans (FFL.Entailment.Equiv.iff.mp inferInstance _)
  exact hc₀ T.craig e henum' s n ((FFL.Entailment.Equiv.iff.mp inferInstance _).mp h)

end KolmogorovComplexity
