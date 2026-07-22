/-
Copyright (c) 2026 Mykola Palamarchuk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mykola Palamarchuk
-/
import Mathlib
import ALT.BinaryKraft
import ALT.KolmogorovComplexity

-- Formal-check file, not Mathlib-destined: opt out of the house-style header linter.
set_option linter.style.header false

/-!
# Additive AST program-length complexity `KE` (two-machine invariance, part one)

Provenance: [SQ] §2 (description/time-bounded complexity) and
[Discovery] §1.1 (`K(R) = r`, program length in bits). Extends
`ALT/KolmogorovComplexity.lean` (`Computes`, `const_computes`) with an **additive**
program-length measure that the index/bit-length measures (`codelen`, `codelen'`) cannot provide.

Status: PROVED.

## Why additive `E` (not the existing `encode`-based measures)
`ALT/KolmogorovComplexity.lean` and `ALT/KolmogorovBitlen.lean` measure a program by its Gödel
index `encode c` (resp. `Nat.size (encode c)`). Mathlib's `encodeCode` pairs children with the
quadratic `Nat.pair` at every binary node, so `encode (comp cf cg)` is *super-linear* in
`encode cf + encode cg`; there is no additive law `|comp cf cg| = |cf| + |cg| + O(1)`. Every corpus
docstring flags exactly this blowup as the obstruction to the two-machine additive-invariance bound
`K_U ≤ K_V + c_{U,V}` and to a clean `KE(x) ≤ K_d(x) + c_d`.

`E` fixes this by serializing the AST in prefix (Polish) form with a fixed 3-bit opcode per node, so
program length is additive **by construction**: `|E (comp cf cg)| = 3 + |E cf| + |E cg|`
(`E_len_comp`). This is the first half of the invariance target: the compositional length algebra.

## What this establishes
* `E`, `elen`, `KE`: self-delimiting AST encoding, its bit-length, and the induced complexity.
* `E_len_comp`, `E_len_pair`: exact additive length laws (the payoff `encode` cannot give).
* `KE_le`, `exists_min_E`: the minimization API (mirrors Slice-1 `K_le`/`exists_min_code`).
* `KE_comp_le`, `KE_subadditive`: compositional upper bounds — `KE (Nat.pair x y) ≤ KE x + KE y + 3`
  (the additive subadditivity the index measure cannot prove).
* `E_append_inj`, `E_injective`: **parse uniqueness** — the prefix encoding decodes: a serialized
  program is a prefix of no other program's serialization, so `E` is injective. This is what makes
  program length a *code* length rather than an arbitrary weight.
* `card_KE_le`, `finite_KE_le`: the **counting bound** — at most `2 ^ (L + 1)` naturals have
  `KE ≤ L`, because distinct values need distinct shortest programs, `E` is injective, and there
  are fewer than `2 ^ (L + 1)` bit-strings of length at most `L`. This is the incompressibility
  method's supply side, consumed by [Persistence] §7.
* `KE_t`, `KE_le_KE_t`, `KE_t_antitone`: time-bounded refinement (scaffold for [SQ] Prop 2.2),
  a one-symbol swap of the corpus `K_t` construction (`elen` for the index `codelen`).

## What this does NOT establish (flagged)
* Two-machine additive invariance itself (the second half): needs a length-efficient *binary*
  constant `bconst : ℕ → Code` with `|E (bconst n)| = O(Nat.size n)` — Mathlib's `Code.const` is
  a *unary* tower (`const (n+1) = comp succ (const n)`), so `|E (Code.const n)| = Θ(n)`,
  exponential in bit-length. Deferred to a separate sub-project (the `bconst` gate).
* Does NOT reconnect `KE` to the abstract `r`/`K` reals of the MDL corpus.

## Hypotheses: paper-stated vs added
* Paper-stated / faithful: additive program length; subadditivity `KE(⟨x,y⟩) ≤ KE x + KE y + O(1)`.
* Added / modeling: one fixed machine (`Code.eval`); 3-bit Polish opcode; input-`0` convention
  (`Computes`) inherited from Slice 1.
-/

namespace AdditiveComplexity

open Nat.Partrec Nat.Partrec.Code KolmogorovComplexity

/-- Self-delimiting AST encoding of a `Code` in prefix (Polish) form: a fixed 3-bit opcode per node,
followed by the children's encodings. Additive by construction (`E_len_comp`/`E_len_pair`). -/
def E : Code → List Bool
  | .zero => [false, false, false]
  | .succ => [false, false, true]
  | .left => [false, true, false]
  | .right => [false, true, true]
  | .pair cf cg => [true, false, false] ++ E cf ++ E cg
  | .comp cf cg => [true, false, true] ++ E cf ++ E cg
  | .prec cf cg => [true, true, false] ++ E cf ++ E cg
  | .rfind' cf => [true, true, true] ++ E cf

/-- Program length under the additive encoding: the bit-length of `E c`. -/
def elen (c : Code) : ℕ := (E c).length

/-- **Additive** Kolmogorov complexity: least `elen`-length over codes computing `x` from input `0`.
Well-defined — `Code.const x` computes `x` (Slice 1), so the minimand is nonempty. -/
noncomputable def KE (x : ℕ) : ℕ := sInf {l | ∃ c, Computes c x ∧ elen c = l}

/-- The additive length law for `comp` (the payoff the `encode` index measure cannot give): the
3-bit opcode plus the two children's lengths. `E (comp …)` unfolds by `rfl`, and `simp only`
computes the list lengths and normalizes the sum. -/
theorem E_len_comp (cf cg : Code) : elen (comp cf cg) = 3 + elen cf + elen cg := by
  simp only [elen, E, List.length_append, List.length_cons, List.length_nil]

/-- The additive length law for `pair` (identical shape to `E_len_comp`). -/
theorem E_len_pair (cf cg : Code) : elen (pair cf cg) = 3 + elen cf + elen cg := by
  simp only [elen, E, List.length_append, List.length_cons, List.length_nil]

/-- Any program computing `x` bounds `KE x` by its own additive length. (Mirrors
`KolmogorovComplexity.K_le`: `elen c` is a member of the minimand.) -/
theorem KE_le {c : Code} {x : ℕ} (h : Computes c x) : KE x ≤ elen c :=
  Nat.sInf_le ⟨c, h, rfl⟩

/-- `KE x` is achieved by some code. (Mirrors `KolmogorovComplexity.exists_min_code`: the minimand
is nonempty via `const_computes`, so `Nat.sInf_mem` applies.) -/
theorem exists_min_E (x : ℕ) : ∃ c, Computes c x ∧ elen c = KE x := by
  have hne : {l | ∃ c, Computes c x ∧ elen c = l}.Nonempty :=
    ⟨elen (Code.const x), Code.const x, const_computes x, rfl⟩
  obtain ⟨c, hc, hl⟩ := Nat.sInf_mem hne
  exact ⟨c, hc, hl⟩

/-- Composition upper bound: a `comp c d` computing `x` bounds `KE x` additively — `KE_le` on the
witness, then the additive `E_len_comp`. -/
theorem KE_comp_le {c d : Code} {x : ℕ} (h : Computes (comp c d) x) :
    KE x ≤ elen c + elen d + 3 := by
  have hle := KE_le h
  rw [E_len_comp] at hle
  omega

/-- **Subadditivity** (the headline additive bound): `KE (Nat.pair x y) ≤ KE x + KE y + 3`. Take the
`KE`-optimal codes `cx`, `cy` for `x`, `y`; `pair cx cy` computes `Nat.pair x y` (the `pair` eval
law is definitional), and its length is `3 + elen cx + elen cy` by `E_len_pair`. -/
theorem KE_subadditive (x y : ℕ) : KE (Nat.pair x y) ≤ KE x + KE y + 3 := by
  obtain ⟨cx, hcx, hlx⟩ := exists_min_E x
  obtain ⟨cy, hcy, hly⟩ := exists_min_E y
  -- `pair cx cy` computes `Nat.pair x y`: the `pair` eval law is definitional (STEP 0 probe d).
  have hpair : Computes (pair cx cy) (Nat.pair x y) := by
    simp only [Computes] at hcx hcy ⊢
    change Nat.pair <$> eval cx 0 <*> eval cy 0 = Part.some (Nat.pair x y)
    rw [hcx, hcy]
    simp [Seq.seq]
  have hle := KE_le hpair
  rw [E_len_pair] at hle
  omega

/-! ## Parse uniqueness: `E` is injective

The serialization is a prefix code by construction: the 3-bit opcode at the head of a node says how
many children follow, so a serialized program can be read off the front of any bit-stream that
begins with it, and nothing else can. The statement that carries the induction is the stronger
*parse-uniqueness* form (`E_append_inj`) — if two serializations agree after arbitrary trailing
bits, the programs and the trailing bits agree — from which injectivity is the empty-tail case. -/

/-- **Parse uniqueness.** A serialized program determines itself and its trailing bits: no `E c` is
a proper prefix of another `E d`. The induction is on `c`, with `d` and both tails universally
quantified — the binary nodes consume their two children by two applications of the induction
hypothesis. -/
theorem E_append_inj : ∀ (c d : Code) (L₁ L₂ : List Bool),
    E c ++ L₁ = E d ++ L₂ → c = d ∧ L₁ = L₂ := by
  intro c
  induction c with
  | zero => intro d L₁ L₂ h; cases d <;> simp_all [E]
  | succ => intro d L₁ L₂ h; cases d <;> simp_all [E]
  | left => intro d L₁ L₂ h; cases d <;> simp_all [E]
  | right => intro d L₁ L₂ h; cases d <;> simp_all [E]
  | pair cf cg ihf ihg =>
      intro d L₁ L₂ h
      cases d <;> simp only [E, List.cons_append, List.nil_append, List.append_assoc,
        List.cons.injEq, Bool.true_eq_false, Bool.false_eq_true, false_and, and_false,
        true_and] at h
      obtain ⟨rfl, h2⟩ := ihf _ _ _ h
      obtain ⟨rfl, rfl⟩ := ihg _ _ _ h2
      exact ⟨rfl, rfl⟩
  | comp cf cg ihf ihg =>
      intro d L₁ L₂ h
      cases d <;> simp only [E, List.cons_append, List.nil_append, List.append_assoc,
        List.cons.injEq, Bool.true_eq_false, Bool.false_eq_true, false_and, and_false,
        true_and] at h
      obtain ⟨rfl, h2⟩ := ihf _ _ _ h
      obtain ⟨rfl, rfl⟩ := ihg _ _ _ h2
      exact ⟨rfl, rfl⟩
  | prec cf cg ihf ihg =>
      intro d L₁ L₂ h
      cases d <;> simp only [E, List.cons_append, List.nil_append, List.append_assoc,
        List.cons.injEq, Bool.true_eq_false, Bool.false_eq_true, false_and, and_false,
        true_and] at h
      obtain ⟨rfl, h2⟩ := ihf _ _ _ h
      obtain ⟨rfl, rfl⟩ := ihg _ _ _ h2
      exact ⟨rfl, rfl⟩
  | rfind' cf ihf =>
      intro d L₁ L₂ h
      cases d <;> simp only [E, List.cons_append, List.nil_append, List.append_assoc,
        List.cons.injEq, Bool.true_eq_false, false_and, and_false, true_and] at h
      obtain ⟨rfl, rfl⟩ := ihf _ _ _ h
      exact ⟨rfl, rfl⟩

/-- **The serialization is injective**: distinct programs have distinct bit-strings (the empty-tail
case of `E_append_inj`). Distinct outputs therefore need distinct shortest programs — the
prerequisite of every counting bound on `KE` (`card_KE_le`). -/
theorem E_injective : Function.Injective E := fun c d h =>
  (E_append_inj c d [] [] (by simpa using h)).1

/-! ## Kraft's inequality: the code lengths are affordable

Parse uniqueness says `E` is a prefix code, and a prefix code is uniquely decodable: a
concatenation of serialized programs parses back to exactly one list of programs. Kraft's
inequality (McMillan's counting argument, `InformationTheory.kraft_mcmillan_inequality`) then
prices the lengths — `∑ 2 ^ (-elen c) ≤ 1` over ALL programs at once. The counting bounds below
are the finite shadow of this: a budget of `L` bits cannot be spent twice. -/

/-- `E` never emits the empty string: every node opens with its 3-bit opcode. -/
theorem E_ne_nil (c : Code) : E c ≠ [] := by
  cases c <;> simp [E]

open InformationTheory in
/-- **The serialization is uniquely decodable**: two lists of programs whose concatenations agree
are the same list. Parse uniqueness (`E_append_inj`) peels one program off each side at a time —
the head programs coincide and the tails still agree, so the induction closes. -/
theorem uniquelyDecodable_range_E : UniquelyDecodable (Set.range E) := by
  intro L₁
  induction L₁ with
  | nil =>
      rintro (_ | ⟨v, vs⟩) - h₂ hflat
      · rfl
      · obtain ⟨d, rfl⟩ := h₂ v (by simp)
        simp only [List.flatten_nil, List.flatten_cons] at hflat
        exact absurd (List.append_eq_nil_iff.mp hflat.symm).1 (E_ne_nil d)
  | cons w ws ih =>
      rintro (_ | ⟨v, vs⟩) h₁ h₂ hflat
      · obtain ⟨c, rfl⟩ := h₁ w (by simp)
        simp only [List.flatten_nil, List.flatten_cons] at hflat
        exact absurd (List.append_eq_nil_iff.mp hflat).1 (E_ne_nil c)
      · obtain ⟨c, rfl⟩ := h₁ w (by simp)
        obtain ⟨d, rfl⟩ := h₂ v (by simp)
        simp only [List.flatten_cons] at hflat
        obtain ⟨rfl, htail⟩ := E_append_inj c d _ _ hflat
        rw [ih vs (fun x hx => h₁ x (List.mem_cons_of_mem _ hx))
              (fun x hx => h₂ x (List.mem_cons_of_mem _ hx)) htail]

/-- **Kraft's inequality over any finite set of programs.** McMillan's argument applies to the
serialized codewords; injectivity of `E` (`E_injective`) transports the sum back to the programs
themselves. Both steps are generic in the code, so this is `BinaryKraft.indexed_finset_sum_le_one`
at `E`. -/
theorem kraft_sum_le_one (F : Finset Code) :
    ∑ c ∈ F, (1 / 2 : ℝ) ^ elen c ≤ 1 := by
  simpa [elen] using
    BinaryKraft.indexed_finset_sum_le_one E E_injective uniquelyDecodable_range_E F

/-- **Kraft's inequality for the additive encoding**: `∑ 2 ^ (-elen c) ≤ 1`, over all programs.
Every finite subtotal is at most one (`kraft_sum_le_one`), and the summands are nonnegative, so the
sum over the whole (countably infinite) space of programs is too. Short programs are therefore
scarce by arithmetic, not by convention: halving the length doubles the price. -/
theorem kraft_KP_E : ∑' c : Code, (1 / 2 : ℝ) ^ elen c ≤ 1 := by
  simpa [elen] using
    BinaryKraft.indexed_tsum_le_one E E_injective uniquelyDecodable_range_E

/-! ## Counting programs: how many naturals are `L`-compressible

Fewer than `2 ^ (L + 1)` bit-strings have length at most `L`; parse uniqueness turns that into a
bound on how many naturals admit a program of length at most `L`. This is the supply side of the
incompressibility method: a budget of `L` bits describes at most `2 ^ (L + 1)` objects, so any set
of more than that many objects contains an incompressible one. -/

/-- The bit-strings of length at most `L`, as a finite set: the empty string, and everything
obtained by prefixing a bit to a bit-string of length at most `L - 1`. -/
def bitLists : ℕ → Finset (List Bool)
  | 0 => {[]}
  | L + 1 =>
      insert [] (((bitLists L).image (List.cons true)) ∪ ((bitLists L).image (List.cons false)))

/-- `bitLists L` contains every bit-string of length at most `L`. -/
theorem mem_bitLists : ∀ {L : ℕ} {l : List Bool}, l.length ≤ L → l ∈ bitLists L
  | 0, l, h => by
      have hl : l = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.mp h)
      simp [bitLists, hl]
  | _ + 1, [], _ => by simp [bitLists]
  | L + 1, (b :: t), h => by
      have ht : t.length ≤ L := by simpa using h
      have hmem := mem_bitLists ht
      refine Finset.mem_insert_of_mem ?_
      cases b
      · exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ hmem)
      · exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ hmem)

/-- There are at most `2 ^ (L + 1) - 1` bit-strings of length at most `L` (in fact exactly that
many; the inequality is all the counting needs). One empty string, plus two copies of the previous
level. -/
theorem card_bitLists (L : ℕ) : (bitLists L).card ≤ 2 ^ (L + 1) - 1 := by
  induction L with
  | zero => simp [bitLists]
  | succ L ih =>
      have h1 : (bitLists (L + 1)).card
          ≤ (((bitLists L).image (List.cons true)) ∪ ((bitLists L).image (List.cons false))).card
            + 1 := Finset.card_insert_le _ _
      have h2 := Finset.card_union_le ((bitLists L).image (List.cons true))
        ((bitLists L).image (List.cons false))
      have h3 := Finset.card_image_le (s := bitLists L) (f := List.cons true)
      have h4 := Finset.card_image_le (s := bitLists L) (f := List.cons false)
      have hp : 2 ^ (L + 1 + 1) = 2 * 2 ^ (L + 1) := by ring
      have hpos : 1 ≤ 2 ^ (L + 1) := Nat.one_le_two_pow
      omega

/-- A shortest program for `x` (`exists_min_E` makes the choice possible). -/
noncomputable def minCode (x : ℕ) : Code := (exists_min_E x).choose

theorem minCode_computes (x : ℕ) : Computes (minCode x) x := (exists_min_E x).choose_spec.1

theorem elen_minCode (x : ℕ) : elen (minCode x) = KE x := (exists_min_E x).choose_spec.2

theorem length_E_minCode (x : ℕ) : (E (minCode x)).length = KE x := elen_minCode x

/-- **Distinct values have distinct shortest programs.** A program computes ONE value, and `E` is
injective, so `x ↦ E (minCode x)` is injective — the pigeonhole map behind `card_KE_le`. -/
theorem minCode_E_injective : Function.Injective fun x => E (minCode x) := by
  intro x y h
  have hc : minCode x = minCode y := E_injective h
  have hx := minCode_computes x
  have hy := minCode_computes y
  rw [Computes, hc] at hx
  rw [Computes] at hy
  exact Part.some_injective (hx.symm.trans hy)

/-- Only finitely many naturals are describable within a fixed budget. -/
theorem finite_KE_le (L : ℕ) : {x : ℕ | KE x ≤ L}.Finite := by
  have hsub : {x : ℕ | KE x ≤ L} ⊆ (fun x => E (minCode x)) ⁻¹' ↑(bitLists L) := fun x hx =>
    mem_bitLists (by rw [length_E_minCode]; exact hx)
  exact Set.Finite.subset (Set.Finite.preimage (minCode_E_injective.injOn)
    (bitLists L).finite_toSet) hsub

/-- **The counting bound**: at most `2 ^ (L + 1)` naturals have complexity at most `L`. Each such
value carries its own shortest program (`minCode_E_injective`), and those programs are bit-strings
of length at most `L`, of which there are fewer than `2 ^ (L + 1)` (`card_bitLists`).

A description budget of `L` bits buys at most `2 ^ (L + 1)` objects: this is the supply side of the
incompressibility method, and the counting half of the collapse of [Persistence] §7. -/
theorem card_KE_le (L : ℕ) : {x : ℕ | KE x ≤ L}.ncard ≤ 2 ^ (L + 1) := by
  have hmaps : ∀ x ∈ {x : ℕ | KE x ≤ L}, (fun x => E (minCode x)) x ∈ (↑(bitLists L) : Set _) :=
    fun x hx => mem_bitLists (by rw [length_E_minCode]; exact hx)
  have hle := Set.ncard_le_ncard_of_injOn (fun x => E (minCode x)) hmaps
    (minCode_E_injective.injOn) (bitLists L).finite_toSet
  rw [Set.ncard_coe_finset] at hle
  have := card_bitLists L
  have hpos : 1 ≤ 2 ^ (L + 1) := Nat.one_le_two_pow
  omega

/-! ## Time-bounded refinement (scaffold for [SQ] Prop 2.2)

A one-symbol swap of the corpus `KolmogorovTimeBounded.K_t` construction: `elen` in place of the
index `codelen`, over the same `evaln` step-budget set. -/

/-- Additive lengths of programs outputting `x` from input `0` within `t` `evaln`-steps. -/
def tElens (t x : ℕ) : Set ℕ := {l | ∃ c, x ∈ Code.evaln t c 0 ∧ elen c = l}

/-- Time-bounded additive complexity: least `elen`-length over codes outputting `x` from input `0`
within `t` `evaln`-steps; `⊤` if none halts in budget `t`. Mirrors `KolmogorovTimeBounded.K_t` with
the additive length `elen` in place of the index `codelen`. -/
noncomputable def KE_t (t x : ℕ) : ℕ∞ := sInf ((Nat.cast : ℕ → ℕ∞) '' tElens t x)

/-- More compute never hurts: `KE x ≤ KE_t t x` — the `t`-bounded programs are a sub-collection of
all programs (`evaln_sound`). Mirrors `KolmogorovTimeBounded.K_le_K_t`. -/
theorem KE_le_KE_t (t x : ℕ) : (KE x : ℕ∞) ≤ KE_t t x := by
  apply le_sInf
  rintro _ ⟨_, ⟨c, hev, rfl⟩, rfl⟩
  exact_mod_cast KE_le (Part.eq_some_iff.mpr (evaln_sound hev))

/-- Antitone in the budget: more steps ⇒ no larger `KE_t` (`evaln_mono`). Mirrors
`KolmogorovTimeBounded.K_t_antitone`. -/
theorem KE_t_antitone {t₁ t₂ : ℕ} (h : t₁ ≤ t₂) (x : ℕ) : KE_t t₂ x ≤ KE_t t₁ x := by
  apply sInf_le_sInf
  apply Set.image_mono
  rintro l ⟨c, hev, rfl⟩
  exact ⟨c, evaln_mono h hev, rfl⟩

/-- Time-bounded analogue of `KE_le`: any code halting on `x` within budget `t` bounds `KE_t t x` by
its own additive length (`elen c ∈ tElens t x`, then `sInf_le`). -/
theorem KE_t_le {t x : ℕ} {c : Code} (h : x ∈ Code.evaln t c 0) : KE_t t x ≤ (elen c : ℕ∞) := by
  apply sInf_le
  exact ⟨elen c, ⟨c, h, rfl⟩, rfl⟩

end AdditiveComplexity
