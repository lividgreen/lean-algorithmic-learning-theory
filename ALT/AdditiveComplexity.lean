/-
Copyright (c) 2026 Mykola Palamarchuk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mykola Palamarchuk
-/
import Mathlib
import ALT.KolmogorovComplexity

-- Formal-check file, not Mathlib-destined: opt out of the house-style header linter.
set_option linter.style.header false

/-!
# Additive AST program-length complexity `KE` (two-machine invariance, part one)

Provenance: Paper III §2 (description/time-bounded complexity) and
Paper II §1.1 (`K(R) = r`, program length in bits). Extends
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
* `KE_t`, `KE_le_KE_t`, `KE_t_antitone`: time-bounded refinement (scaffold for Paper III Prop 2.2),
  a one-symbol swap of the corpus `K_t` construction (`elen` for the index `codelen`).

## What this does NOT establish (flagged / later stages)
* Two-machine additive invariance itself (the second half): needs a length-efficient *binary* constant
  `bconst : ℕ → Code` with `|E (bconst n)| = O(Nat.size n)` — Mathlib's `Code.const` is a *unary*
  tower (`const (n+1) = comp succ (const n)`), so `|E (Code.const n)| = Θ(n)`, exponential in
  bit-length. Deferred to a separate sub-project (the `bconst` gate).
* Prefix-freeness of `E` as a `List Bool` code (a parse-uniqueness lemma) — not needed for the
  additive bounds here; deferred.
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

/-! ## Time-bounded refinement (scaffold for Paper III Prop 2.2)

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
