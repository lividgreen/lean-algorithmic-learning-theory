/-
Copyright (c) 2026 Mykola Palamarchuk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mykola Palamarchuk
-/
import ALT.KolmogorovBitlen
import Foundation.FirstOrder.Incompleteness.Halting

-- Formal-check file, not Mathlib-destined: opt out of the house-style header linter.
set_option linter.style.header false

/-!
# Chaitin's incompleteness theorem over bit-length complexity ([Decoupling] §6.6, [Discovery] §1.1)

Provenance: [Decoupling] §6.6 (Theorem 6.6, FV-28), over the bit-length complexity `K_bitlen` of
[Discovery] §1.1 (`ALT/KolmogorovBitlen.lean`) and the `FormalizedFormalLogic/Foundation`
arithmetic — its representation of computably enumerable predicates (`codeOfREPred`), its
Σ₁-completeness over `𝗥₀`, and the Σ₁ provability predicate of a `Δ₁`-axiomatized theory.

Status: PROVED, axiom-clean at the standard triple (guarded in `ALT/AxiomAuditFoundation.lean`).

## What this establishes
* `chaitin_bound` — the abstract Berry bound: a computably enumerable relation on pairs that
  asserts only true lower bounds `n < K_bitlen s` is bounded by the bit-length of one program, a
  Kleene fixed point (`fixed_point₂`) of the search that enumerates the relation.
* `kle`, `kle_iff`, `rePred_kle` — "some program of bit-length at most `n` outputs `s`", read at a
  coded pair as `K_bitlen s ≤ n`, and computably enumerable.
* `chaitinSentence`, `models_chaitinSentence_iff` — the sentence "`K(s) > n`" as the negation of
  Foundation's Σ₁ representation of `kle`; true in `ℕ` iff `n < K_bitlen s`.
* Over `T` with `[T.Δ₁] [𝗥₀ ⪯ T] [Consistent T]`: `rePred_provable_chaitin` (the provable set is
  computably enumerable, from `T.Δ₁` alone), `chaitin_sound` (a provable Chaitin sentence is true,
  from `𝗥₀ ⪯ T` and consistency alone, through Σ₁-completeness), and `chaitin_theorem`: `T`
  proves `chaitinSentence s n` for no `n` at or above the bit-length of one fixed-point program;
  `chaitin_true_unprovable` and `setOf_K_bitlen_le_finite` give the true, unprovable sentences at
  that constant, all but finitely many `s` carrying one.

## What this does NOT establish
* The constant is a fixed point's bit-length, given existentially — named, not computed — and no
  bound in `T`'s own description length is stated: Chaitin's additive form would need a
  size-controlled recursion theorem on an additive measure, which `fixed_point₂` does not give.
* Nothing is claimed of any arithmetization of "`K(s) > n`" other than `codeOfREPred kle`.
-/

namespace KolmogorovComplexity

open Nat.Partrec Nat.Partrec.Code

/-! ## Piece 1: the abstract Chaitin bound (Mathlib only) -/

/-- The three `Nat.unpair` projections packing `(s, n, k)` into one natural, used by the Berry
search below: `m = Nat.pair s (Nat.pair n k)`. -/
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

-- As in `ALT/KolmogorovBitlen.lean`: keep `codelen'` irreducible for the Berry proof below,
-- otherwise `whnf` unfolds it to `Nat.size (encode …)` and loops on `Nat.size`'s `binaryRec`
-- during `Computable` unification.
attribute [local irreducible] codelen'

set_option maxHeartbeats 1000000 in
-- The `Partrec.rfind`/`fixed_point₂` elaboration over the nested `Code × ℕ` shape is heavy in
-- this imported environment; the default 200k heartbeats is short (mirrors `computable_nat_size`
-- in `ALT/KolmogorovBitlen.lean`).
/-- Chaitin's bound, abstract form: a computably enumerable relation that asserts only TRUE lower
bounds on bit-length complexity is bounded by a constant, and the constant is the bit-length of one
program — a fixed point of the search that enumerates the relation. -/
theorem chaitin_bound {P : ℕ × ℕ → Prop} (hP : REPred P)
    (hsound : ∀ s n, P (s, n) → n < K_bitlen s) :
    ∃ c₀ : Code, ∀ s n, P (s, n) → n < codelen' c₀ := by
  -- Reduce `P`'s enumerability to a code `cQ` whose halting on `Nat.pair s n` decides `P (s, n)`.
  have hQ : REPred fun a : ℕ => P (Nat.unpair a) := REPred.comp Primrec.unpair.to_comp hP
  obtain ⟨f, hf, hfQ⟩ := REPred.iff'.mp hQ
  have hf' : Partrec fun a => (f a).map fun _ : Unit => (0 : ℕ) :=
    Partrec.map hf (Computable.const 0).to₂
  obtain ⟨cQ, hcQ⟩ := Nat.Partrec.Code.exists_code.1 (Partrec.nat_iff.mp hf')
  have hQdom : ∀ a, (cQ.eval a).Dom ↔ P (Nat.unpair a) := by
    intro a
    rw [congrFun hcQ a]
    change (f a).Dom ↔ P (Nat.unpair a)
    exact (hfQ a).symm
  -- `decide (· ≤ ·)` is computable.
  have hle : Computable fun p : ℕ × ℕ => decide (p.1 ≤ p.2) := by
    have hpr := Primrec.nat_le.choose_spec.to_comp
    have heq : (fun a : ℕ × ℕ => @decide _ (Primrec.nat_le.choose a)) =
        fun p : ℕ × ℕ => decide (p.1 ≤ p.2) := by funext a; congr 1
    rw [← heq]; exact hpr
  -- The Berry predicate at `(c, m)`: `codelen' c ≤ nOf m`, and `cQ` halts on
  -- `Nat.pair (sOf m) (nOf m)` within `kOf m` steps.
  have hg : Computable fun r : (Code × ℕ) × ℕ =>
      decide (codelen' r.1.1 ≤ nOf r.2) &&
        (evaln (kOf r.2) cQ (Nat.pair (sOf r.2) (nOf r.2))).isSome := by
    -- Built in `Primrec` throughout (converted to `Computable` only at the end): mixing
    -- `Computable`/`Primrec` `.comp` calls on this composite shape hits a `whnf` timeout.
    have c2 : Primrec fun r : (Code × ℕ) × ℕ => nOf r.2 := primrec_nOf.comp Primrec.snd
    have c3 : Primrec fun r : (Code × ℕ) × ℕ => kOf r.2 := primrec_kOf.comp Primrec.snd
    have c4 : Primrec fun r : (Code × ℕ) × ℕ => sOf r.2 := primrec_sOf.comp Primrec.snd
    have hpair : Primrec fun r : (Code × ℕ) × ℕ => Nat.pair (sOf r.2) (nOf r.2) :=
      Primrec₂.natPair.comp c4 c2
    have hev : Primrec fun r : (Code × ℕ) × ℕ =>
        evaln (kOf r.2) cQ (Nat.pair (sOf r.2) (nOf r.2)) :=
      Nat.Partrec.Code.primrec_evaln.comp ((c3.pair (Primrec.const cQ)).pair hpair)
    have hisSome : Primrec fun r : (Code × ℕ) × ℕ =>
        (evaln (kOf r.2) cQ (Nat.pair (sOf r.2) (nOf r.2))).isSome :=
      Primrec.option_isSome.comp hev
    have c1 : Computable fun r : (Code × ℕ) × ℕ => codelen' r.1.1 :=
      computable_codelen'.comp (Computable.fst.comp Computable.fst)
    exact Computable₂.comp Primrec.and.to_comp (hle.comp (c1.pair c2.to_comp)) hisSome.to_comp
  -- The Berry search (an `rfind`, ignoring the second argument) is `Partrec₂`.
  have hf2 : Partrec₂ (fun (c : Code) (_ : ℕ) => Nat.rfind fun m =>
      Part.some (decide (codelen' c ≤ nOf m) &&
        (evaln (kOf m) cQ (Nat.pair (sOf m) (nOf m))).isSome)) :=
    Partrec.rfind (p := fun (q : Code × ℕ) (m : ℕ) =>
      Part.some (decide (codelen' q.1 ≤ nOf m) &&
        (evaln (kOf m) cQ (Nat.pair (sOf m) (nOf m))).isSome)) hg.partrec
  -- Compose with `sOf`: the fixed point will output the FIRST coordinate of the least witness.
  have hf3 : Partrec₂ (fun (c : Code) (_ : ℕ) => (Nat.rfind fun m =>
      Part.some (decide (codelen' c ≤ nOf m) &&
        (evaln (kOf m) cQ (Nat.pair (sOf m) (nOf m))).isSome)).map sOf) :=
    Partrec.map hf2 (primrec_sOf.to_comp.comp Computable.snd)
  obtain ⟨c₀, hc₀⟩ := fixed_point₂ hf3
  refine ⟨c₀, fun s n hPsn => ?_⟩
  set p₀ : ℕ →. Bool := fun m => Part.some (decide (codelen' c₀ ≤ nOf m) &&
      (evaln (kOf m) cQ (Nat.pair (sOf m) (nOf m))).isSome) with hp₀
  by_contra hcon
  push Not at hcon
  -- `hcon : codelen' c₀ ≤ n`; find a witness `m` for the rfind at `(s, n)`.
  have hPn : P (Nat.unpair (Nat.pair s n)) := by rw [Nat.unpair_pair]; exact hPsn
  have hdomQ : (cQ.eval (Nat.pair s n)).Dom := (hQdom (Nat.pair s n)).mpr hPn
  obtain ⟨k, hk⟩ := evaln_complete.1 (Part.dom_iff_mem.mp hdomQ).choose_spec
  have hmem : true ∈ p₀ (Nat.pair s (Nat.pair n k)) := by
    simp only [hp₀, Part.mem_some_iff]
    rw [sOf_pack, nOf_pack, kOf_pack]
    simpa [hcon] using Option.isSome_iff_exists.mpr ⟨_, hk⟩
  have hdom : (Nat.rfind p₀).Dom := by
    rw [Nat.rfind_dom]
    exact ⟨Nat.pair s (Nat.pair n k), hmem, fun {m} _ => trivial⟩
  set w : ℕ := (Nat.rfind p₀).get hdom with hw
  have hwspec : true ∈ p₀ w := Nat.rfind_spec (Part.get_mem hdom)
  have hwspec' : codelen' c₀ ≤ nOf w ∧
      (evaln (kOf w) cQ (Nat.pair (sOf w) (nOf w))).isSome := by
    simpa [hp₀, Bool.and_eq_true] using hwspec
  have hQw : P (Nat.unpair (Nat.pair (sOf w) (nOf w))) := by
    apply (hQdom (Nat.pair (sOf w) (nOf w))).mp
    rw [Part.dom_iff_mem]
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hwspec'.2
    exact ⟨v, evaln_sound hv⟩
  rw [Nat.unpair_pair] at hQw
  have hsoundw : nOf w < K_bitlen (sOf w) := hsound (sOf w) (nOf w) hQw
  have heval : c₀.eval 0 = (Nat.rfind p₀).map sOf := by rw [hc₀]
  have hrfind_eq : Nat.rfind p₀ = Part.some w := Part.get_eq_iff_eq_some.mp hw.symm
  have hcomp : Computes c₀ (sOf w) := by
    rw [Computes, heval, hrfind_eq]; simp
  have hle' : K_bitlen (sOf w) ≤ codelen' c₀ := K_bitlen_le hcomp
  omega

/-! ## Piece 2: the arithmetic form (Foundation) -/

open FFL.FirstOrder FFL.FirstOrder.Arithmetic

/-- "The bit-length complexity of `(Nat.unpair a).1` is at most `(Nat.unpair a).2`" — a computably
enumerable predicate on coded pairs. -/
def kle (a : ℕ) : Prop :=
  ∃ c : Code, codelen' c ≤ (Nat.unpair a).2 ∧ Computes c (Nat.unpair a).1

theorem kle_iff (s n : ℕ) : kle (Nat.pair s n) ↔ K_bitlen s ≤ n := by
  unfold kle
  rw [Nat.unpair_pair]
  constructor
  · rintro ⟨c, hcl, hcomp⟩
    exact (K_bitlen_le hcomp).trans hcl
  · intro h
    obtain ⟨c, hcomp, hlen⟩ := exists_min_code s
    refine ⟨c, ?_, hcomp⟩
    have hcl : codelen' c = K_bitlen s := by
      unfold codelen'
      rw [hlen, ← K_bitlen_eq]
    omega

private theorem computable_decide_le : Computable fun p : ℕ × ℕ => decide (p.1 ≤ p.2) := by
  have hpr := Primrec.nat_le.choose_spec.to_comp
  have heq : (fun a : ℕ × ℕ => @decide _ (Primrec.nat_le.choose a)) =
      fun p : ℕ × ℕ => decide (p.1 ≤ p.2) := by funext a; congr 1
  rw [← heq]; exact hpr

private theorem computable_decide_eq_option :
    Computable fun p : Option ℕ × Option ℕ => decide (p.1 = p.2) := by
  have hpr := (Primrec.eq (α := Option ℕ)).choose_spec.to_comp
  have heq : (fun a : Option ℕ × Option ℕ => @decide _ ((Primrec.eq (α := Option ℕ)).choose a)) =
      fun p : Option ℕ × Option ℕ => decide (p.1 = p.2) := by funext a; congr 1
  rw [← heq]; exact hpr

/-- `kle` is recursively enumerable: dovetail over a witness code `c` and a step budget `k`,
testing `codelen' c ≤ n` and `evaln k c 0 = some x` by `ComputablePred`. -/
theorem rePred_kle : REPred kle := by
  set Q : (ℕ × Code) × ℕ → Prop := fun x =>
    codelen' x.1.2 ≤ (Nat.unpair x.1.1).2 ∧ evaln x.2 x.1.2 0 = some (Nat.unpair x.1.1).1
    with hQ
  have hp1 : ComputablePred fun x : (ℕ × Code) × ℕ =>
      codelen' x.1.2 ≤ (Nat.unpair x.1.1).2 := by
    have hc1 : Computable fun x : (ℕ × Code) × ℕ => codelen' x.1.2 :=
      computable_codelen'.comp (Computable.snd.comp Computable.fst)
    have hc2 : Computable fun x : (ℕ × Code) × ℕ => (Nat.unpair x.1.1).2 :=
      (Primrec.snd.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.fst))).to_comp
    exact Computable.computablePred (computable_decide_le.comp (hc1.pair hc2))
  have hp2 : ComputablePred fun x : (ℕ × Code) × ℕ =>
      evaln x.2 x.1.2 0 = some (Nat.unpair x.1.1).1 := by
    have hev : Computable fun x : (ℕ × Code) × ℕ => evaln x.2 x.1.2 0 := by
      have hprim : Computable fun a : (ℕ × Code) × ℕ => evaln a.1.1 a.1.2 a.2 :=
        Nat.Partrec.Code.primrec_evaln.to_comp
      exact hprim.comp
        ((Computable.snd.pair (Computable.snd.comp Computable.fst)).pair (Computable.const 0))
    have hsome : Computable fun x : (ℕ × Code) × ℕ => (some (Nat.unpair x.1.1).1 : Option ℕ) :=
      Computable.option_some.comp
        ((Primrec.fst.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.fst))).to_comp)
    exact Computable.computablePred (computable_decide_eq_option.comp (hev.pair hsome))
  have hQcomp : ComputablePred Q := hp1.and hp2
  have hpQ1 : REPred fun x : ℕ × Code => ∃ k : ℕ, Q (x, k) := REPred.projection hQcomp.to_re
  have hpQ2 : REPred fun a : ℕ => ∃ c : Code, ∃ k : ℕ, Q ((a, c), k) := REPred.projection hpQ1
  refine hpQ2.of_eq (fun a => ?_)
  unfold kle Q
  constructor
  · rintro ⟨c, k, hcl, hev⟩
    exact ⟨c, hcl, by rw [Computes]; exact Part.eq_some_iff.mpr (evaln_sound hev)⟩
  · rintro ⟨c, hcl, hcomp⟩
    rw [Computes] at hcomp
    obtain ⟨k, hk⟩ := evaln_complete.1 (Part.eq_some_iff.mp hcomp)
    exact ⟨c, k, hcl, hk⟩

/-- The Chaitin sentence "the bit-length complexity of `s` exceeds `n`": the negation of
Foundation's Σ₁ representation of `kle`, at the numeral of the coded pair. -/
noncomputable def chaitinSentence (s n : ℕ) : ArithmeticSentence :=
  ∼(codeOfREPred kle)/[Nat.pair s n]

theorem models_chaitinSentence_iff (s n : ℕ) :
    (ℕ↓[ℒₒᵣ] ⊧ chaitinSentence s n) ↔ n < K_bitlen s := by
  have h1 : (ℕ↓[ℒₒᵣ] ⊧ (codeOfREPred kle)/[Nat.pair s n]) ↔ kle (Nat.pair s n) := by
    simpa [models_iff, Semiformula.eval_substs, Matrix.constant_eq_singleton] using
      codeOfREPred_spec rePred_kle (x := Nat.pair s n)
  unfold chaitinSentence
  simp only [FFL.Semantics.Not.models_not] at h1 ⊢
  rw [h1, kle_iff, not_le]

variable (T : ArithmeticTheory) [T.Δ₁] [𝗥₀ ⪯ T] [FFL.Entailment.Consistent T]

omit [𝗥₀ ⪯ T] [FFL.Entailment.Consistent T] in
open FFL.Entailment Bootstrapping Bootstrapping.Arithmetic in
/-- The provability predicate over `T` at the fixed formula `codeOfREPred kle`, varied over the
substituted numeral, is recursively enumerable — needs only `[T.Δ₁]` (the theory's own provability
predicate is Σ₁-definable; no soundness or `𝗥₀ ⪯ T` is used). -/
theorem rePred_provable_chaitin :
    REPred fun a : ℕ => T ⊢ chaitinSentence (Nat.unpair a).1 (Nat.unpair a).2 := by
  have heq : (fun a : ℕ => T ⊢ chaitinSentence (Nat.unpair a).1 (Nat.unpair a).2) =
      fun a : ℕ => T ⊢ ∼(codeOfREPred kle)/[a] := by
    funext a
    unfold chaitinSentence
    rw [Nat.pair_unpair a]
  rw [heq]
  have hS1 : 𝚺₁-Predicate fun a : ℕ =>
      Provable T (neg ℒₒᵣ (subst ℒₒᵣ ?[numeral a] (⌜codeOfREPred kle⌝ : ℕ))) := by definability
  refine (rePred_iff_sigma1.mpr hS1).of_eq (fun a => ?_)
  simp [←provable_iff_provable, Sentence.quote_def, Rewriting.emb_subst_eq_subst_coe₁,
    Semiformula.quote_def]

omit [T.Δ₁] in
/-- `T`'s consistency makes every provable Chaitin sentence true (the ℕ side of `kle`'s
representation, via `sigma_one_completeness` under `𝗥₀ ⪯ T` alone). -/
theorem chaitin_sound (s n : ℕ) (h : T ⊢ chaitinSentence s n) : n < K_bitlen s := by
  by_contra hcon
  push Not at hcon
  have hkle : kle (Nat.pair s n) := (kle_iff s n).mpr hcon
  have hmod : ℕ↓[ℒₒᵣ] ⊧ (codeOfREPred kle)/[Nat.pair s n] := by
    have h1 : (ℕ↓[ℒₒᵣ] ⊧ (codeOfREPred kle)/[Nat.pair s n]) ↔ kle (Nat.pair s n) := by
      simpa [models_iff, Semiformula.eval_substs, Matrix.constant_eq_singleton] using
        codeOfREPred_spec rePred_kle (x := Nat.pair s n)
    exact h1.mpr hkle
  have hsig : Hierarchy 𝚺 1 (((codeOfREPred kle)/[Nat.pair s n] : ArithmeticSentence)) := by
    simp [codeOfREPred, codeOfPartrec']
  have hpos : T ⊢ (codeOfREPred kle)/[Nat.pair s n] :=
    sigma_one_completeness (σ := (codeOfREPred kle)/[Nat.pair s n]) hsig hmod
  have hneg : T ⊢ ∼(codeOfREPred kle)/[Nat.pair s n] := h
  exact FFL.Entailment.Consistent.not_bot (𝓢 := T) (by cl_prover [hpos, hneg])

/-- **Chaitin's incompleteness theorem** over Mathlib's universal machine and a `Δ₁`-axiomatized
consistent extension of `𝗥₀`: the theory proves "the bit-length complexity of `s` exceeds `n`" for
no `n` at or above the bit-length of one fixed-point program. -/
theorem chaitin_theorem : ∃ c₀ : Code, ∀ s n, T ⊢ chaitinSentence s n → n < codelen' c₀ := by
  have hpair : Computable fun p : ℕ × ℕ => Nat.pair p.1 p.2 := Primrec₂.natPair.to_comp
  have hPP : REPred fun p : ℕ × ℕ => T ⊢ chaitinSentence p.1 p.2 :=
    (REPred.comp hpair (rePred_provable_chaitin T)).of_eq (fun p => by rw [Nat.unpair_pair])
  exact chaitin_bound hPP (fun s n h => chaitin_sound T s n h)

theorem chaitin_true_unprovable :
    ∃ c₀ : Code, ∀ s, codelen' c₀ < K_bitlen s →
      (ℕ↓[ℒₒᵣ] ⊧ chaitinSentence s (codelen' c₀)) ∧ T ⊬ chaitinSentence s (codelen' c₀) := by
  obtain ⟨c₀, hc₀⟩ := chaitin_theorem T
  refine ⟨c₀, fun s hs => ⟨(models_chaitinSentence_iff s (codelen' c₀)).mpr hs, fun h => ?_⟩⟩
  exact absurd (hc₀ s (codelen' c₀) h) (_root_.lt_irrefl _)

theorem setOf_K_bitlen_le_finite (L : ℕ) : {s | K_bitlen s ≤ L}.Finite := by
  apply Set.Finite.subset (setOf_K_le_finite (2 ^ L))
  intro s hs
  simp only [Set.mem_ofPred_eq] at hs ⊢
  rw [K_bitlen_eq, Nat.size_le] at hs
  omega

/-! ## Piece 3: transport to recursively enumerable theories, via Craig's trick

`T.craig` (`FormalizedFormalLogic/Foundation`) is a `Δ₁`-axiomatized theory deductively
equivalent to any `RE`-axiomatized `T`, so the `Δ₁` forms above transport along that equivalence
to the whole `RE` class, at the same fixed-point constant. -/

omit [T.Δ₁] in
/-- **Chaitin's incompleteness theorem**, for any recursively enumerable, consistent extension of
`𝗥₀`: transported from `chaitin_theorem` along `T ≊ T.craig` (Craig's trick). -/
theorem chaitin_theorem_of_RE [T.RE] :
    ∃ c₀ : Code, ∀ s n, T ⊢ chaitinSentence s n → n < codelen' c₀ := by
  obtain ⟨c₀, hc₀⟩ := chaitin_theorem T.craig
  exact ⟨c₀, fun s n h => hc₀ s n ((FFL.Entailment.Equiv.iff.mp inferInstance _).mp h)⟩

omit [T.Δ₁] in
theorem chaitin_true_unprovable_of_RE [T.RE] :
    ∃ c₀ : Code, ∀ s, codelen' c₀ < K_bitlen s →
      (ℕ↓[ℒₒᵣ] ⊧ chaitinSentence s (codelen' c₀)) ∧ T ⊬ chaitinSentence s (codelen' c₀) := by
  obtain ⟨c₀, hc₀⟩ := chaitin_true_unprovable T.craig
  refine ⟨c₀, fun s hs => ⟨(hc₀ s hs).1, ?_⟩⟩
  exact (FFL.Entailment.Equiv.unprovable inferInstance).mpr (hc₀ s hs).2

end KolmogorovComplexity
