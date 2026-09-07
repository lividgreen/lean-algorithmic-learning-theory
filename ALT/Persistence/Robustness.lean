/-
Copyright (c) 2026 Mykola Palamarchuk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mykola Palamarchuk
-/
import Batteries.Tactic.OpenPrivate
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.InformationTheory.Hamming
import ALT.GodelInternalization
import ALT.Persistence.Counting

-- Formal-check file, not Mathlib-destined: opt out of the house-style header linter.
set_option linter.style.header false

/-!
# Persistence capacity IV: worlds, towers and the robustness margin ([Persistence] §2, §10)

Part four of the `PersistenceCapacity` development (umbrella and map: `ALT.PersistenceCapacity`).
The counting of `ALT.Persistence.Counting` lives over a fixed permutation world; this module
carries the capacity theory to general endofunction worlds and world constructions, stacks
sub-systems into towers, and prices what survives a perturbation.

## Main results

* World constructions: disjoint unions (`unionWorld` — the kind regime is closed under
  composition), basins as worlds of their own, Cartesian products (a habitat beside an
  environment), and time dilation at `O (log τ)` (`KE_iterate_le` — a slower reading is not a
  cheaper one).
* `CbHe` / `CbHue` / `CbHe_le_core_factorial` / `CbHe_perm` / `CbHue_perm` — **the budgeted
  entropic capacities over a general endofunction world** ([Persistence] §2, Definitions 2.1–2.2;
  §5): valued on the recurrent core, capped by the core's factorial, and equal to `CbH` / `CbHu`
  when the world is a permutation.
* `CbHev_eq_CbHeOn` — **eventual capacity from a basin IS exact capacity on its attractor**
  ([Persistence] §10.1 read at §5's budget): a transient is a shift of the clock and nothing
  else.
* `CbHue_le_CbHe` — **owning beats renting by at most the clock, over an arbitrary
  endofunction**, via a clamped reindexing that repeats by construction.
* `card_basinWorld_carries_le` — **the floor does not survive irreversibility**
  ([Persistence] §7, Proposition 7.9(ii)): fold a fixed-cycle core and one-step transient basins
  into a world and the entropic floor Corollary 7.5(i) gives every permutation world is gone — at
  most `2 ^ (b + 1) * (c - 1) ^ tr` of the `c ^ tr` worlds of that shape admit ANY non-constant
  affordable carried family, at any fixed label count.
* `Intertwines.comp` / `uniformBudget_comp` / `tower_no_free_lunch` / `entropy_comp_le` — **the
  tower** ([Persistence] §10.2 + §2): squares compose, dilations multiply, budgets add; stacking
  buys structure, never generic capacity, and entropy is antitone up the levels. Beside it, the
  guest ledgers ([Guests] §2, §4, §9.2): the reversible-host dichotomy, the lossy and law-blind
  ledgers, and the two-block and conjugation guests (every division of the bill is realized).
* `hasMargin_iff` / `repair_tax` / `majority_margin` — the **robustness margin** ([Persistence]
  §10.1 + §2): it factors into basin fatness and local constancy, it is paid for in carried
  content by sphere packing in the memory, and three-copy majority saturates the bound exactly
  (`repair_tax_tight_majWorld`).
* The packaged **Witness World** ([Persistence] §5, §7, §8, §10.1 + [Decoupling] §6): a lawful
  sub-system beside an arbitrary environment, priced end to end, its macro reading owned in the
  capacity vocabulary — and **Emergence**: the ceiling of the whole development, priced.
-/

namespace PersistenceCapacity

open Decoupling CodeEvalLaws

variable {X ι V M : Type*}

open AdditiveComplexity KolmogorovComplexity Nat.Partrec Nat.Partrec.Code

-- File-boundary bookkeeping for the split development: these helpers stay `private` (they are
-- proof plumbing, not interface), and the sibling modules reach them with `open private`.
open private exists_image_stable omegaLimit_eq_image omegaLimit_subset majWorld_apply from
  ALT.Persistence.Core
open private corePerm_pow_apply omegaPerm_pow_apply from ALT.Persistence.MovingLens
open private UniformBudget.mono bddAbove_uniformBudgetedEntropies candBijBool candBijBool_iff
  candPerm candPerm_apply candTable candTable_injOn candTable_packMarks descentEquivStab digitAt
  digitAt_worldNumeral eval_faithBuilder ledger_graded_paired_persists lensCode_injective
  natRec_iterate primrec_candBijBool primrec_candTable primrec_list_all primrec_list_sum
  primrec_rawTable primrec_unzipFst primrec_unzipSnd rawTable rawTable_lensCode smul_lens_apply
  sum_digits_div_mod unzipFst unzipFst_lensTable_pairLens unzipSnd unzipSnd_lensTable_pairLens
  worldNumeral worldNumeral_lt from ALT.Persistence.Counting

-- Reopened from `ALT.Persistence.Counting`'s `Collapse` section: the same relabelling action
-- and scoping (see the note there on `arrowAction` and why faithful frames are spelled
-- `⇑(U ^ t)⁻¹`).
section Collapse

open MulAction Equiv Nat AdditiveComplexity

attribute [local instance] arrowAction

variable {n m : ℕ}

/-! ## Disjoint-union worlds: the kind regime is closed under composition

A world can be built out of two smaller ones by letting them run side by side, sharing nothing: the
**disjoint union** `unionWorld U₁ U₂`, a permutation of `Fin (n₁ + n₂)` acting as `U₁` on the first
block and `U₂` on the second. It is worth being clear about what kind of object this is. A union
world is *structured by construction* — it preserves its blocks, so it is nothing like a generic
permutation, and the collapse's generic statements simply do not speak about it. That is the point
rather than a caveat: composed worlds live on the kind side of the phase boundary, and this
section is about what holds there.

Two things compose.

**Rules compose** (`KE_unionWorld_le`): `KE (U₁ ⊕ U₂) ≤ KE U₁ + KE U₂ + O (1)`, with the constant
one fixed builder. So the cheap-dynamics regime is **closed under disjoint union** — a union of
cheap worlds is cheap. The builder needs no size parameters: a world's table is a list as long as
its block, so the block sizes are read off the two tables' own lengths, and the second block's
entries are shifted by the first's length.

**Capacities are superadditive** (`CbHu_unionWorld_ge`): affordable readings of the two blocks
combine into one affordable reading of the union, and the union's carried entropy is at least the
product of the blocks'. The orbit arithmetic is where the inequality comes from — the block-pair
lens has exactly the two blocks' fibres, so the merged profile gives
`(n₁ + n₂)! / (∏ f¹! · ∏ f²!) ≥ [n₁! / ∏ f¹!] · [n₂! / ∏ f²!]`, which is `n₁! · n₂! ≤ (n₁ + n₂)!`
after clearing denominators.

The phase reading: **the emergence region is closed under composition**. A world with one kind part
hosts affordable sub-systems regardless of what its other parts do — the kind part's capacity is a
floor for the whole, and the two blocks' capacities multiply rather than merely add. Nothing here
contradicts the collapse; the collapse prices *generic* worlds, and a union world is not one.

Anchors: [Persistence] §5, Definition 5.5 and §8's kind-world regime. The composition laws are this
development's; no numbered result of [Persistence] is claimed machine-checked by their presence. -/

/-- **The disjoint-union world** `U₁ ⊕ U₂`: the two worlds run side by side on `Fin (n₁ + n₂)`,
neither block ever mapping into the other. Transported along `finSumFinEquiv` from the sum
permutation, so its block action needs the two evaluation lemmas below — it does *not* compute
definitionally, `finSumFinEquiv.symm` being an `addCases`. -/
def unionWorld {n₁ n₂ : ℕ} (U₁ : Perm (Fin n₁)) (U₂ : Perm (Fin n₂)) : Perm (Fin (n₁ + n₂)) :=
  Equiv.permCongr finSumFinEquiv (Equiv.sumCongr U₁ U₂)

/-- The union world acts as `U₁` on the first block. -/
@[simp] theorem unionWorld_left {n₁ n₂ : ℕ} (U₁ : Perm (Fin n₁)) (U₂ : Perm (Fin n₂)) (i : Fin n₁) :
    unionWorld U₁ U₂ (Fin.castAdd n₂ i) = Fin.castAdd n₂ (U₁ i) := by
  simp [unionWorld, Equiv.permCongr_def]

/-- The union world acts as `U₂` on the second block. -/
@[simp] theorem unionWorld_right {n₁ n₂ : ℕ} (U₁ : Perm (Fin n₁)) (U₂ : Perm (Fin n₂))
    (j : Fin n₂) : unionWorld U₁ U₂ (Fin.natAdd n₁ j) = Fin.natAdd n₁ (U₂ j) := by
  simp [unionWorld, Equiv.permCongr_def]

/-- Blocks are preserved by every power: the union world never mixes them. -/
private theorem unionWorld_pow_left {n₁ n₂ : ℕ} (U₁ : Perm (Fin n₁)) (U₂ : Perm (Fin n₂)) (t : ℕ)
    (i : Fin n₁) : ((unionWorld U₁ U₂) ^ t) (Fin.castAdd n₂ i) = Fin.castAdd n₂ ((U₁ ^ t) i) := by
  induction t generalizing i with
  | zero => simp
  | succ t ih => rw [pow_succ, pow_succ]; simp [Equiv.Perm.mul_apply, ih]

private theorem unionWorld_pow_right {n₁ n₂ : ℕ} (U₁ : Perm (Fin n₁)) (U₂ : Perm (Fin n₂)) (t : ℕ)
    (j : Fin n₂) : ((unionWorld U₁ U₂) ^ t) (Fin.natAdd n₁ j) = Fin.natAdd n₁ ((U₂ ^ t) j) := by
  induction t generalizing j with
  | zero => simp
  | succ t ih => rw [pow_succ, pow_succ]; simp [Equiv.Perm.mul_apply, ih]

/-- The inverse of a union world moving only the second block fixes the first, by injectivity of
the forward map (`unionWorld_left` reads block one as `1`, which is `id`). -/
private theorem unionWorld_inv_left {n₁ n₂ : ℕ} (U₂ : Perm (Fin n₂)) (i : Fin n₁) :
    (unionWorld (1 : Perm (Fin n₁)) U₂)⁻¹ (Fin.castAdd n₂ i) = Fin.castAdd n₂ i := by
  apply (unionWorld (1 : Perm (Fin n₁)) U₂).injective
  simp

/-- The inverse of a union world moving only the second block acts there as `U₂⁻¹`. -/
private theorem unionWorld_inv_right {n₁ n₂ : ℕ} (U₂ : Perm (Fin n₂)) (j : Fin n₂) :
    (unionWorld (1 : Perm (Fin n₁)) U₂)⁻¹ (Fin.natAdd n₁ j) = Fin.natAdd n₁ (U₂⁻¹ j) := by
  apply (unionWorld (1 : Perm (Fin n₁)) U₂).injective
  simp

/-- Every power of that inverse still fixes the first block, same induction as
`unionWorld_pow_left`. -/
private theorem unionWorld_invPow_left {n₁ n₂ : ℕ} (U₂ : Perm (Fin n₂)) (t : ℕ) (i : Fin n₁) :
    ((unionWorld (1 : Perm (Fin n₁)) U₂)⁻¹ ^ t) (Fin.castAdd n₂ i) = Fin.castAdd n₂ i := by
  induction t generalizing i with
  | zero => simp
  | succ t ih =>
      rw [pow_succ, Equiv.Perm.mul_apply, unionWorld_inv_left]
      exact ih i

/-- Every power of that inverse acts on the second block as the corresponding power of `U₂⁻¹`. -/
private theorem unionWorld_invPow_right {n₁ n₂ : ℕ} (U₂ : Perm (Fin n₂)) (t : ℕ) (j : Fin n₂) :
    ((unionWorld (1 : Perm (Fin n₁)) U₂)⁻¹ ^ t) (Fin.natAdd n₁ j)
      = Fin.natAdd n₁ ((U₂⁻¹ ^ t) j) := by
  induction t generalizing j with
  | zero => simp
  | succ t ih =>
      rw [pow_succ, pow_succ, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, unionWorld_inv_right]
      exact ih _

/-- **Two tables, concatenated with the second block's entries shifted.** The shared shape of both
builders below: for the world the shift is the first table's own length, for a lens it is the first
block's label count. -/
def shiftAppend (T₁ T₂ : List ℕ) (s : ℕ) : List ℕ := T₁ ++ T₂.map (fun v => s + v)

private theorem primrec_shiftAppend :
    Primrec fun q : (List ℕ × List ℕ) × ℕ => shiftAppend q.1.1 q.1.2 q.2 := by
  have hmap : Primrec fun q : (List ℕ × List ℕ) × ℕ => q.1.2.map (fun v => q.2 + v) :=
    Primrec.list_map (Primrec.snd.comp Primrec.fst)
      (Primrec.nat_add.comp (Primrec.snd.comp Primrec.fst) Primrec.snd).to₂
  exact Primrec.list_append.comp (Primrec.fst.comp Primrec.fst) hmap

/-- The union world's table is the two blocks' tables, the second shifted past the first. -/
theorem lensTable_unionWorld {n₁ n₂ : ℕ} (U₁ : Perm (Fin n₁)) (U₂ : Perm (Fin n₂)) :
    lensTable ⇑(unionWorld U₁ U₂) = shiftAppend (lensTable ⇑U₁) (lensTable ⇑U₂) n₁ := by
  have hfun : (fun x : Fin (n₁ + n₂) => ((unionWorld U₁ U₂ x : Fin (n₁ + n₂)) : ℕ))
      = Fin.append (fun i => ((U₁ i : Fin n₁) : ℕ)) (fun j => n₁ + ((U₂ j : Fin n₂) : ℕ)) := by
    funext x
    refine Fin.addCases (fun i => ?_) (fun j => ?_) x <;> simp
  rw [shiftAppend, lensTable, lensTable, lensTable, ← List.ofFn_eq_map, ← List.ofFn_eq_map,
    ← List.ofFn_eq_map, List.map_ofFn, hfun, List.ofFn_fin_append]
  rfl

/-- **The union-world builder**: on `⟨U₁'s table, U₂'s table⟩` it outputs the union world's table.
ONE fixed function — no block sizes are passed in, because a table is as long as its block. -/
def unionTableFn (p : ℕ) : ℕ :=
  Encodable.encode
    (shiftAppend ((Encodable.decode (α := List ℕ) p.unpair.1).getD [])
      ((Encodable.decode (α := List ℕ) p.unpair.2).getD [])
      ((Encodable.decode (α := List ℕ) p.unpair.1).getD []).length)

private theorem primrec_unionTableFn : Primrec unionTableFn := by
  have hdec1 : Primrec fun p : ℕ => (Encodable.decode (α := List ℕ) p.unpair.1).getD [] :=
    Primrec.option_getD.comp (Primrec.decode.comp (Primrec.fst.comp Primrec.unpair))
      (Primrec.const [])
  have hdec2 : Primrec fun p : ℕ => (Encodable.decode (α := List ℕ) p.unpair.2).getD [] :=
    Primrec.option_getD.comp (Primrec.decode.comp (Primrec.snd.comp Primrec.unpair))
      (Primrec.const [])
  exact Primrec.encode.comp
    (primrec_shiftAppend.comp (Primrec.pair (Primrec.pair hdec1 hdec2)
      (Primrec.list_length.comp hdec1)))

/-- **The builder is correct**: it outputs exactly the union world's encoded table. -/
theorem unionTableFn_eq {n₁ n₂ : ℕ} (U₁ : Perm (Fin n₁)) (U₂ : Perm (Fin n₂)) :
    unionTableFn (Nat.pair (lensCode ⇑U₁) (lensCode ⇑U₂)) = lensCode ⇑(unionWorld U₁ U₂) := by
  have hlen : (lensTable ⇑U₁).length = n₁ := by rw [lensTable]; simp
  rw [unionTableFn]
  simp only [Nat.unpair_pair, decode_lensCode]
  rw [hlen, ← lensTable_unionWorld]
  rfl

private theorem partrec_unionTableFn : Nat.Partrec (fun p : ℕ => (unionTableFn p : ℕ)) :=
  _root_.Partrec.nat_iff.mp (Primrec.to_comp primrec_unionTableFn).partrec

/-- **The fixed union-world builder code.** -/
noncomputable def unionBuilder : Nat.Partrec.Code :=
  Classical.choose (Nat.Partrec.Code.exists_code.mp partrec_unionTableFn)

private theorem eval_unionBuilder (p : ℕ) :
    Nat.Partrec.Code.eval unionBuilder p = Part.some (unionTableFn p) := by
  have h := congrFun (Classical.choose_spec
    (Nat.Partrec.Code.exists_code.mp partrec_unionTableFn)) p
  simpa [unionBuilder] using h

/-- **Rules compose: the cheap-dynamics regime is closed under disjoint union.** Given codes for the
two blocks' tables, the union world costs their lengths plus an absolute constant
`elen unionBuilder + 6` — one fixed builder and the assembly's opcodes, independent of the worlds
and of `n₁`, `n₂`.

No size parameter is loaded, and none is needed: a world's table is a list as long as its block, so
`unionTableFn` reads `n₁` off the first table and shifts the second block's entries by it.

The consequence is the composition law of the kind regime. If `U₁` and `U₂` are (CD) — rules of
order `log` of their sizes, as `KE_lcgWorld_le` exhibits — then so is `U₁ ⊕ U₂`. Cheapness of the
rule is not something a world can lose by being put beside another cheap world. -/
theorem KE_unionWorld_le {n₁ n₂ : ℕ} (U₁ : Perm (Fin n₁)) (U₂ : Perm (Fin n₂))
    (c₁ c₂ : Nat.Partrec.Code) (h₁ : c₁.eval 0 = Part.some (lensCode ⇑U₁))
    (h₂ : c₂.eval 0 = Part.some (lensCode ⇑U₂)) :
    KE (lensCode ⇑(unionWorld U₁ U₂)) ≤ elen c₁ + elen c₂ + (elen unionBuilder + 6) := by
  have hp : Nat.Partrec.Code.eval (Nat.Partrec.Code.pair c₁ c₂) 0
      = Part.some (Nat.pair (lensCode ⇑U₁) (lensCode ⇑U₂)) := by
    change Nat.pair <$> _ <*> _ = _
    rw [h₁, h₂]; simp [Seq.seq]
  have hcomp : Computes (Nat.Partrec.Code.comp unionBuilder (Nat.Partrec.Code.pair c₁ c₂))
      (lensCode ⇑(unionWorld U₁ U₂)) := by
    change Nat.Partrec.Code.eval _ 0 = _
    rw [eval_comp_some hp, eval_unionBuilder, unionTableFn_eq]
  have hle := KE_le hcomp
  rw [E_len_comp, E_len_pair] at hle
  omega

/-- **The block-pair lens**: read each block with its own reading, and keep the two label sets
apart — block one's labels land in `Fin (k₁ + k₂)`'s lower range, block two's in the upper. Keeping
them disjoint is what makes the union's fibres exactly the two blocks' fibres. -/
def unionLens {n₁ n₂ k₁ k₂ : ℕ} (ℓ₁ : ℕ → Fin n₁ → Fin k₁) (ℓ₂ : ℕ → Fin n₂ → Fin k₂) (t : ℕ) :
    Fin (n₁ + n₂) → Fin (k₁ + k₂) :=
  Fin.append (fun i => Fin.castAdd k₂ (ℓ₁ t i)) (fun j => Fin.natAdd k₁ (ℓ₂ t j))

/-- **A block-pair of carrying families carries the union.** Each block's reading persists along its
own block, and the union world never moves a state across the divide. -/
theorem permCarries_unionLens {n₁ n₂ k₁ k₂ : ℕ} {U₁ : Perm (Fin n₁)} {U₂ : Perm (Fin n₂)}
    {ℓ₁ : ℕ → Fin n₁ → Fin k₁} {ℓ₂ : ℕ → Fin n₂ → Fin k₂}
    (h₁ : PermCarries U₁ ℓ₁) (h₂ : PermCarries U₂ ℓ₂) :
    PermCarries (unionWorld U₁ U₂) (unionLens ℓ₁ ℓ₂) := by
  constructor
  · intro v
    refine Fin.addCases (fun a => ?_) (fun b => ?_) v
    · obtain ⟨i, hi⟩ := h₁.1 a
      exact ⟨Fin.castAdd n₂ i, by simp [unionLens, Fin.append_left, hi]⟩
    · obtain ⟨j, hj⟩ := h₂.1 b
      exact ⟨Fin.natAdd n₁ j, by simp [unionLens, Fin.append_right, hj]⟩
  · intro t x
    refine Fin.addCases (fun i => ?_) (fun j => ?_) x
    · rw [unionWorld_pow_left]
      simp only [unionLens, Fin.append_left]
      rw [h₁.2 t i]
    · rw [unionWorld_pow_right]
      simp only [unionLens, Fin.append_right]
      rw [h₂.2 t j]

/-- **The block-pair-lens builder**: on `⟨⟨block one's table, block two's table⟩, k₁⟩` it gives
the union lens's table. Unlike `unionTableFn`, the shift **must** be supplied — a lens's table has
one entry per state, so its length is the block size and the *label* count is nowhere in it. That is
the one place a size parameter is unavoidable here, and `uniformBudget_unionLens` pays `O (log k₁)`
for it. -/
private def unionLensTableFn (p : ℕ) : ℕ :=
  Encodable.encode
    (shiftAppend ((Encodable.decode (α := List ℕ) p.unpair.1.unpair.1).getD [])
      ((Encodable.decode (α := List ℕ) p.unpair.1.unpair.2).getD []) p.unpair.2)

private theorem primrec_unionLensTableFn : Primrec unionLensTableFn := by
  have hdec1 : Primrec fun p : ℕ => (Encodable.decode (α := List ℕ) p.unpair.1.unpair.1).getD [] :=
    Primrec.option_getD.comp
      (Primrec.decode.comp
        (Primrec.fst.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.unpair))))
      (Primrec.const [])
  have hdec2 : Primrec fun p : ℕ => (Encodable.decode (α := List ℕ) p.unpair.1.unpair.2).getD [] :=
    Primrec.option_getD.comp
      (Primrec.decode.comp
        (Primrec.snd.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.unpair))))
      (Primrec.const [])
  exact Primrec.encode.comp
    (primrec_shiftAppend.comp (Primrec.pair (Primrec.pair hdec1 hdec2)
      (Primrec.snd.comp Primrec.unpair)))

/-- The union lens's table is the two readings' tables, the second shifted past the first's
labels. -/
private theorem lensTable_unionLens {n₁ n₂ k₁ k₂ : ℕ} (ℓ₁ : ℕ → Fin n₁ → Fin k₁)
    (ℓ₂ : ℕ → Fin n₂ → Fin k₂) (t : ℕ) :
    lensTable (unionLens ℓ₁ ℓ₂ t) = shiftAppend (lensTable (ℓ₁ t)) (lensTable (ℓ₂ t)) k₁ := by
  have hfun : (fun x : Fin (n₁ + n₂) => ((unionLens ℓ₁ ℓ₂ t x : Fin (k₁ + k₂)) : ℕ))
      = Fin.append (fun i => ((ℓ₁ t i : Fin k₁) : ℕ)) (fun j => k₁ + ((ℓ₂ t j : Fin k₂) : ℕ)) := by
    funext x
    refine Fin.addCases (fun i => ?_) (fun j => ?_) x <;> simp [unionLens]
  rw [shiftAppend, lensTable, lensTable, lensTable, ← List.ofFn_eq_map, ← List.ofFn_eq_map,
    ← List.ofFn_eq_map, List.map_ofFn, hfun, List.ofFn_fin_append]
  rfl

private theorem unionLensTableFn_eq {n₁ n₂ k₁ k₂ : ℕ} (ℓ₁ : ℕ → Fin n₁ → Fin k₁)
    (ℓ₂ : ℕ → Fin n₂ → Fin k₂) (t : ℕ) :
    unionLensTableFn (Nat.pair (Nat.pair (lensCode (ℓ₁ t)) (lensCode (ℓ₂ t))) k₁)
      = lensCode (unionLens ℓ₁ ℓ₂ t) := by
  rw [unionLensTableFn]
  simp only [Nat.unpair_pair, decode_lensCode]
  rw [← lensTable_unionLens]
  rfl

private theorem partrec_unionLensTableFn : Nat.Partrec (fun p : ℕ => (unionLensTableFn p : ℕ)) :=
  _root_.Partrec.nat_iff.mp (Primrec.to_comp primrec_unionLensTableFn).partrec

/-- **The fixed block-pair-lens builder code.** -/
noncomputable def unionLensBuilder : Nat.Partrec.Code :=
  Classical.choose (Nat.Partrec.Code.exists_code.mp partrec_unionLensTableFn)

private theorem eval_unionLensBuilder (p : ℕ) :
    Nat.Partrec.Code.eval unionLensBuilder p = Part.some (unionLensTableFn p) := by
  have h := congrFun (Classical.choose_spec
    (Nat.Partrec.Code.exists_code.mp partrec_unionLensTableFn)) p
  simpa [unionLensBuilder] using h

/-- **Owned readings compose**: two owners, one owner of the pair. The union family is owned at
`b₁ + b₂ + O (log k₁)` — the two programs, run at the same clock value, plus the label shift.

The `O (log k₁)` is not removable on this route and is not a fixed constant: a lens's table records
one label per state, so it fixes the block size but says nothing about how many labels exist. It is
the one asymmetry with `KE_unionWorld_le`, where the shift *is* readable off the table. Since a
carried family's reference frame is surjective, `k₁ ≤ n₁` always, so the term is `O (log n₁)` — see
`CbHu_unionWorld_ge`, which is where it gets discharged into a world-size constant. -/
theorem uniformBudget_unionLens {n₁ n₂ k₁ k₂ : ℕ} {ℓ₁ : ℕ → Fin n₁ → Fin k₁}
    {ℓ₂ : ℕ → Fin n₂ → Fin k₂} {b₁ b₂ : ℕ} (h₁ : UniformBudget ℓ₁ b₁)
    (h₂ : UniformBudget ℓ₂ b₂) :
    UniformBudget (unionLens ℓ₁ ℓ₂) (b₁ + b₂ + (15 + elen dbl) * Nat.size k₁
      + (elen unionLensBuilder + (15 + elen dbl) + 9)) := by
  obtain ⟨c₁, hlen₁, heval₁⟩ := h₁
  obtain ⟨c₂, hlen₂, heval₂⟩ := h₂
  refine ⟨Nat.Partrec.Code.comp unionLensBuilder
    (Nat.Partrec.Code.pair (Nat.Partrec.Code.pair c₁ c₂) (bconst k₁)), ?_, ?_⟩
  · have hb := elen_bconst_le k₁
    simp only [E_len_comp, E_len_pair]
    omega
  · intro t
    have hp1 : Nat.Partrec.Code.eval (Nat.Partrec.Code.pair c₁ c₂) t
        = Part.some (Nat.pair (lensCode (ℓ₁ t)) (lensCode (ℓ₂ t))) := by
      change Nat.pair <$> _ <*> _ = _
      rw [heval₁ t, heval₂ t]; simp [Seq.seq]
    have hp2 : Nat.Partrec.Code.eval
        (Nat.Partrec.Code.pair (Nat.Partrec.Code.pair c₁ c₂) (bconst k₁)) t
        = Part.some (Nat.pair (Nat.pair (lensCode (ℓ₁ t)) (lensCode (ℓ₂ t))) k₁) := by
      change Nat.pair <$> _ <*> _ = _
      rw [hp1, eval_bconst k₁ t]; simp [Seq.seq]
    rw [eval_comp_some hp2, eval_unionLensBuilder, unionLensTableFn_eq]

/-- The union lens's fibre over a **first-block** label is that block's fibre: no state of the
second block carries a first-block label. -/
private theorem card_fiber_unionLens_left {n₁ n₂ k₁ k₂ : ℕ} (ℓ₁ : ℕ → Fin n₁ → Fin k₁)
    (ℓ₂ : ℕ → Fin n₂ → Fin k₂) (a : Fin k₁) :
    Nat.card {x : Fin (n₁ + n₂) // unionLens ℓ₁ ℓ₂ 0 x = Fin.castAdd k₂ a}
      = Nat.card {i : Fin n₁ // ℓ₁ 0 i = a} := by
  have e1 : {x : Fin (n₁ + n₂) // unionLens ℓ₁ ℓ₂ 0 x = Fin.castAdd k₂ a}
      ≃ {c : Fin n₁ ⊕ Fin n₂ // unionLens ℓ₁ ℓ₂ 0 (finSumFinEquiv c) = Fin.castAdd k₂ a} :=
    Equiv.subtypeEquiv finSumFinEquiv.symm (fun x => by simp)
  have e3 : {i : Fin n₁ // unionLens ℓ₁ ℓ₂ 0 (finSumFinEquiv (Sum.inl i)) = Fin.castAdd k₂ a}
      ≃ {i : Fin n₁ // ℓ₁ 0 i = a} :=
    Equiv.subtypeEquiv (Equiv.refl _) (fun i => by
      simp [unionLens, finSumFinEquiv_apply_left, Fin.append_left, Fin.castAdd_inj])
  have hemp :
      IsEmpty {j : Fin n₂ //
        unionLens ℓ₁ ℓ₂ 0 (finSumFinEquiv (Sum.inr j)) = Fin.castAdd k₂ a} := by
    constructor
    rintro ⟨j, hj⟩
    rw [finSumFinEquiv_apply_right] at hj
    simp only [unionLens, Fin.append_right] at hj
    have hv := congrArg Fin.val hj
    simp only [Fin.val_natAdd, Fin.val_castAdd] at hv
    have := a.isLt
    omega
  exact Nat.card_congr (e1.trans (Equiv.subtypeSum.trans ((Equiv.sumEmpty _ _).trans e3)))

/-- The union lens's fibre over a **second-block** label is that block's fibre. -/
private theorem card_fiber_unionLens_right {n₁ n₂ k₁ k₂ : ℕ} (ℓ₁ : ℕ → Fin n₁ → Fin k₁)
    (ℓ₂ : ℕ → Fin n₂ → Fin k₂) (b : Fin k₂) :
    Nat.card {x : Fin (n₁ + n₂) // unionLens ℓ₁ ℓ₂ 0 x = Fin.natAdd k₁ b}
      = Nat.card {j : Fin n₂ // ℓ₂ 0 j = b} := by
  have e1 : {x : Fin (n₁ + n₂) // unionLens ℓ₁ ℓ₂ 0 x = Fin.natAdd k₁ b}
      ≃ {c : Fin n₁ ⊕ Fin n₂ // unionLens ℓ₁ ℓ₂ 0 (finSumFinEquiv c) = Fin.natAdd k₁ b} :=
    Equiv.subtypeEquiv finSumFinEquiv.symm (fun x => by simp)
  have e3 : {j : Fin n₂ // unionLens ℓ₁ ℓ₂ 0 (finSumFinEquiv (Sum.inr j)) = Fin.natAdd k₁ b}
      ≃ {j : Fin n₂ // ℓ₂ 0 j = b} :=
    Equiv.subtypeEquiv (Equiv.refl _) (fun j => by
      simp [unionLens, finSumFinEquiv_apply_right, Fin.append_right, Fin.natAdd_inj])
  have hemp :
      IsEmpty {i : Fin n₁ // unionLens ℓ₁ ℓ₂ 0 (finSumFinEquiv (Sum.inl i)) = Fin.natAdd k₁ b} := by
    constructor
    rintro ⟨i, hi⟩
    rw [finSumFinEquiv_apply_left] at hi
    simp only [unionLens, Fin.append_left] at hi
    have hv := congrArg Fin.val hi
    simp only [Fin.val_natAdd, Fin.val_castAdd] at hv
    have := (ℓ₁ 0 i).isLt
    omega
  exact Nat.card_congr (e1.trans (Equiv.subtypeSum.trans ((Equiv.emptySum _ _).trans e3)))

/-- **The union's fibre profile is the two blocks' profiles, merged** — disjoint labels keep the
fibres from mixing, so the orbit–stabilizer product factors. -/
theorem prod_fiber_unionLens {n₁ n₂ k₁ k₂ : ℕ} (ℓ₁ : ℕ → Fin n₁ → Fin k₁)
    (ℓ₂ : ℕ → Fin n₂ → Fin k₂) :
    ∏ i : Fin (k₁ + k₂), (Nat.card {x : Fin (n₁ + n₂) // unionLens ℓ₁ ℓ₂ 0 x = i})!
      = (∏ a : Fin k₁, (Nat.card {i : Fin n₁ // ℓ₁ 0 i = a})!)
        * ∏ b : Fin k₂, (Nat.card {j : Fin n₂ // ℓ₂ 0 j = b})! := by
  rw [Fin.prod_univ_add]
  congr 1
  · exact Finset.prod_congr rfl fun a _ => by rw [card_fiber_unionLens_left]
  · exact Finset.prod_congr rfl fun b _ => by rw [card_fiber_unionLens_right]

/-- A carried family's reference frame is surjective, so it has no more labels than states. -/
theorem permCarries_label_le {n' k : ℕ} {U : Perm (Fin n')} {ℓ : ℕ → Fin n' → Fin k}
    (h : PermCarries U ℓ) : k ≤ n' := by
  have := Fintype.card_le_of_surjective _ h.1
  simpa using this

/-- **Capacities are superadditive: the emergence region is closed under composition.** The union
world's uniform entropic capacity is at least the **product** of the two blocks' — an owner of an
affordable reading of each block owns an affordable reading of the union, and the union's carried
entropy multiplies rather than merely adding.

The budget shift `O (log n₁) + O (1)` is the label-shift constant of `uniformBudget_unionLens`,
discharged here into a world-size term: a carried family's frame is surjective, so its label count
is at most its block size (`permCarries_label_le`).

The orbit arithmetic is the content. Disjoint labels keep the two blocks' fibres from mixing
(`prod_fiber_unionLens`), so orbit–stabilizer gives
`N_u · (P₁ · P₂) = (n₁ + n₂)!` against `N₁ · P₁ = n₁!` and `N₂ · P₂ = n₂!`; the inequality is then
exactly `n₁! · n₂! ≤ (n₁ + n₂)!` with the fibre products cancelled.

The phase reading, plainly. A union world is **structured by construction** — it preserves its
blocks, so the collapse's generic caps say nothing about it, and no contradiction arises from its
capacity being large. What the statement says is that kindness composes: a world with one kind part
carries everything that part carries, whatever its other parts do. Together with `KE_unionWorld_le`
— cheap rules compose — this is the composition law of the kind regime. -/
theorem CbHu_unionWorld_ge {n₁ n₂ : ℕ} (U₁ : Perm (Fin n₁)) (U₂ : Perm (Fin n₂)) (b₁ b₂ : ℕ) :
    CbHu U₁ b₁ * CbHu U₂ b₂
      ≤ CbHu (unionWorld U₁ U₂) (b₁ + b₂ + (15 + elen dbl) * Nat.size n₁
          + (elen unionLensBuilder + (15 + elen dbl) + 9)) := by
  rcases Set.eq_empty_or_nonempty (UniformBudgetedEntropies U₁ b₁) with h₁e | h₁n
  · simp [CbHu, h₁e]
  rcases Set.eq_empty_or_nonempty (UniformBudgetedEntropies U₂ b₂) with h₂e | h₂n
  · simp [CbHu, h₂e]
  obtain ⟨k₁, ℓ₁, hcar₁, hbud₁, hval₁⟩ : CbHu U₁ b₁ ∈ UniformBudgetedEntropies U₁ b₁ :=
    Nat.sSup_mem h₁n (bddAbove_uniformBudgetedEntropies U₁ b₁)
  obtain ⟨k₂, ℓ₂, hcar₂, hbud₂, hval₂⟩ : CbHu U₂ b₂ ∈ UniformBudgetedEntropies U₂ b₂ :=
    Nat.sSup_mem h₂n (bddAbove_uniformBudgetedEntropies U₂ b₂)
  -- the block-pair family is owned at the stated budget
  have hbudU : UniformBudget (unionLens ℓ₁ ℓ₂) (b₁ + b₂ + (15 + elen dbl) * Nat.size n₁
      + (elen unionLensBuilder + (15 + elen dbl) + 9)) := by
    refine UniformBudget.mono (uniformBudget_unionLens hbud₁ hbud₂) ?_
    have hk : Nat.size k₁ ≤ Nat.size n₁ := Nat.size_le_size (permCarries_label_le hcar₁)
    have := Nat.mul_le_mul_left (15 + elen dbl) hk
    omega
  have hge := CbHu_ge_of_uniform (permCarries_unionLens hcar₁ hcar₂) hbudU
  -- orbit–stabilizer on all three worlds
  have hu := card_orbit_mul_prod_fiber (unionLens ℓ₁ ℓ₂ 0)
  rw [prod_fiber_unionLens] at hu
  have h1 := card_orbit_mul_prod_fiber (ℓ₁ 0)
  have h2 := card_orbit_mul_prod_fiber (ℓ₂ 0)
  set N₁ := Nat.card ↥(orbit (Perm (Fin n₁)) (ℓ₁ 0)) with hN₁
  set N₂ := Nat.card ↥(orbit (Perm (Fin n₂)) (ℓ₂ 0)) with hN₂
  set Nu := Nat.card ↥(orbit (Perm (Fin (n₁ + n₂))) (unionLens ℓ₁ ℓ₂ 0)) with hNu
  set P₁ := ∏ a : Fin k₁, (Nat.card {i : Fin n₁ // ℓ₁ 0 i = a})! with hP₁
  set P₂ := ∏ b : Fin k₂, (Nat.card {j : Fin n₂ // ℓ₂ 0 j = b})! with hP₂
  have hP₁pos : 0 < P₁ := Finset.prod_pos fun a _ => Nat.factorial_pos _
  have hP₂pos : 0 < P₂ := Finset.prod_pos fun b _ => Nat.factorial_pos _
  -- `n₁! · n₂! ≤ (n₁ + n₂)!` is the whole inequality, once the fibre products cancel
  have hfact : n₁ ! * n₂ ! ≤ (n₁ + n₂)! :=
    Nat.le_of_dvd (Nat.factorial_pos _) (Nat.factorial_mul_factorial_dvd_factorial_add n₁ n₂)
  have hkey : N₁ * N₂ * (P₁ * P₂) ≤ Nu * (P₁ * P₂) := by
    calc N₁ * N₂ * (P₁ * P₂) = (N₁ * P₁) * (N₂ * P₂) := by ring
      _ = n₁ ! * n₂ ! := by rw [h1, h2]
      _ ≤ (n₁ + n₂)! := hfact
      _ = Nu * (P₁ * P₂) := hu.symm
  have hcancel : N₁ * N₂ ≤ Nu :=
    Nat.le_of_mul_le_mul_right hkey (Nat.mul_pos hP₁pos hP₂pos)
  calc CbHu U₁ b₁ * CbHu U₂ b₂ = N₁ * N₂ := by rw [hval₁, hval₂]
    _ ≤ Nu := hcancel
    _ ≤ _ := hge

/-! ## Basins: a closed region is a world of its own

Every capacity above quantifies over *all* states. An observer that only ever inhabits part of the
world should be priced against that part. For a permutation world the right notion of "part" is a
**closed** region — a `B` the world never leaves — and the content of this section is that such a
region is not a new setting at all: it is a smaller permutation world.

`image_perm_eq` is why. A permutation that maps `B` into `B` maps `B` *onto* `B` (injectivity plus
finiteness), so `B` is setwise invariant, `U` restricts to a permutation of `B` (`subPerm`), and
transporting along an enumeration gives an honest world `subWorld` over `Fin B.card`. Carrying
families correspond both ways — `permCarriesOn_restrict` and `permCarriesOn_extend` — and the
ledger's frame determination survives restriction (`permCarriesOn_frame_one`).

So the initial-conditions axis has, over permutation worlds, exactly the content of
**decomposition**: which closed regions carry what. That is a real reduction and it is also a real
limit — a genuinely new setting (emergence from a typical starting state, measures on initial
states) needs worlds that are not invertible, where a basin is not a sub-world. That boundary is
deliberate here, not a defect.

**What is not here, and why.** The capacity-level reduction — `CbH_on B U b` against
`CbH (subWorld hB e) b'` at a shifted budget — is *not* proved. The correspondence of families is
free, but the correspondence of *budgets* is not: a family on `B` is priced by `lensCode`, a table
listing one entry per state of the ambient `Fin n`, while the sub-world's family is priced by a
table over `Fin B.card`. Converting between them is an explicit-code obligation — re-indexing a
table along the enumeration, which the builder must be given, at a cost of order
`B.card · log n` bits, not `O (1)`. Neither direction escapes it: extending a family by a constant
off `B` is free as a *function* and not free as a *table*. The objects and the family
correspondence are stated here; the code transport is left open rather than assumed. -/

/-- **A closed region is invariant**: if a permutation maps `B` into `B`, it maps `B` onto `B`. The
one-line reason finiteness is doing work — injectivity makes the image as large as `B` itself, and
a subset of `B` with `B`'s cardinality is `B`. -/
theorem image_perm_eq {U : Perm (Fin n)} {B : Finset (Fin n)} (hB : ∀ i ∈ B, U i ∈ B) :
    B.image ⇑U = B := by
  refine Finset.eq_of_subset_of_card_le ?_ ?_
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    exact hB x hx
  · rw [Finset.card_image_of_injective _ (Equiv.injective U)]

/-- Membership in a closed region is `U`-invariant in both directions — the converse half is what
`image_perm_eq` buys, and it is what lets `U` restrict to a *permutation* of `B`. -/
theorem mem_iff_apply_mem {U : Perm (Fin n)} {B : Finset (Fin n)} (hB : ∀ i ∈ B, U i ∈ B)
    (x : Fin n) : U x ∈ B ↔ x ∈ B := by
  refine ⟨fun h => ?_, hB x⟩
  rw [← image_perm_eq hB] at h
  obtain ⟨y, hy, hxy⟩ := Finset.mem_image.mp h
  rwa [← (Equiv.injective U) hxy]

/-- **The world restricted to a closed region** — a permutation of `B` itself. -/
def subPerm {U : Perm (Fin n)} {B : Finset (Fin n)} (hB : ∀ i ∈ B, U i ∈ B) :
    Perm {x : Fin n // x ∈ B} :=
  U.subtypePerm (mem_iff_apply_mem hB)

/-- Closed regions are closed under every power. -/
theorem pow_mem_of_closed {U : Perm (Fin n)} {B : Finset (Fin n)} (hB : ∀ i ∈ B, U i ∈ B)
    (t : ℕ) {x : Fin n} (hx : x ∈ B) : (U ^ t) x ∈ B := by
  induction t generalizing x with
  | zero => simpa using hx
  | succ t ih =>
    rw [pow_succ, Equiv.Perm.mul_apply]
    exact ih (hB x hx)

/-- **The sub-world**: the restricted permutation, transported along an enumeration of `B` into an
honest permutation world over `Fin B.card`. -/
def subWorld {U : Perm (Fin n)} {B : Finset (Fin n)} (hB : ∀ i ∈ B, U i ∈ B)
    (e : {x : Fin n // x ∈ B} ≃ Fin B.card) : Perm (Fin B.card) :=
  Equiv.permCongr e (subPerm hB)

private theorem subPerm_pow_apply {U : Perm (Fin n)} {B : Finset (Fin n)} (hB : ∀ i ∈ B, U i ∈ B)
    (t : ℕ) (y : {x : Fin n // x ∈ B}) :
    (((subPerm hB) ^ t) y : Fin n) = (U ^ t) (y : Fin n) := by
  rw [subPerm, Equiv.Perm.subtypePerm_pow]
  rfl

theorem subWorld_pow_apply {U : Perm (Fin n)} {B : Finset (Fin n)} (hB : ∀ i ∈ B, U i ∈ B)
    (e : {x : Fin n // x ∈ B} ≃ Fin B.card) (t : ℕ) (y : {x : Fin n // x ∈ B}) :
    ((subWorld hB e) ^ t) (e y) = e (((subPerm hB) ^ t) y) := by
  induction t generalizing y with
  | zero => simp
  | succ t ih =>
    rw [pow_succ, pow_succ, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply]
    rw [show subWorld hB e (e y) = e (subPerm hB y) by simp [subWorld, Equiv.permCongr_def]]
    exact ih (subPerm hB y)

/-- **Carrying a model on a basin** ([Persistence] §7's `PermCarries`, relativized): the reference
frame resolves the region, and the persistence identity is demanded only at the region's states. -/
def PermCarriesOn {m : ℕ} (B : Finset (Fin n)) (U : Perm (Fin n)) (ℓ : ℕ → Fin n → Fin m) : Prop :=
  (∀ v : Fin m, ∃ x ∈ B, ℓ 0 x = v) ∧ ∀ t, ∀ x ∈ B, ℓ t ((U ^ t) x) = ℓ 0 x

/-- A family read only at the region's states, indexed by the enumeration. -/
def restrictLens {m : ℕ} (B : Finset (Fin n)) (e : {x : Fin n // x ∈ B} ≃ Fin B.card)
    (ℓ : ℕ → Fin n → Fin m) (t : ℕ) : Fin B.card → Fin m :=
  fun j => ℓ t ((e.symm j : Fin n))

/-- A family on the sub-world, read back onto the whole world by a constant off the region. -/
def extendLens {m : ℕ} (B : Finset (Fin n)) (e : {x : Fin n // x ∈ B} ≃ Fin B.card) (v₀ : Fin m)
    (ℓ' : ℕ → Fin B.card → Fin m) (t : ℕ) : Fin n → Fin m :=
  fun x => if h : x ∈ B then ℓ' t (e ⟨x, h⟩) else v₀

/-- **A basin family restricts to a sub-world family.** -/
theorem permCarriesOn_restrict {m : ℕ} {U : Perm (Fin n)} {B : Finset (Fin n)}
    (hB : ∀ i ∈ B, U i ∈ B) (e : {x : Fin n // x ∈ B} ≃ Fin B.card) {ℓ : ℕ → Fin n → Fin m}
    (h : PermCarriesOn B U ℓ) : PermCarries (subWorld hB e) (restrictLens B e ℓ) := by
  constructor
  · intro v
    obtain ⟨x, hx, hv⟩ := h.1 v
    exact ⟨e ⟨x, hx⟩, by simp [restrictLens, hv]⟩
  · intro t j
    have hkey := subWorld_pow_apply hB e t (e.symm j)
    rw [Equiv.apply_symm_apply] at hkey
    simp only [restrictLens, hkey, Equiv.symm_apply_apply]
    rw [subPerm_pow_apply hB t (e.symm j)]
    exact h.2 t _ (e.symm j).2

/-- **A sub-world family extends to a basin family** — the direction that needs nothing but a
constant off the region. Note what this does *not* say: the extension is free as a function, and its
*table* still has to be transported along the enumeration, which is why no budget appears. -/
theorem permCarriesOn_extend {m : ℕ} {U : Perm (Fin n)} {B : Finset (Fin n)}
    (hB : ∀ i ∈ B, U i ∈ B) (e : {x : Fin n // x ∈ B} ≃ Fin B.card) (v₀ : Fin m)
    {ℓ' : ℕ → Fin B.card → Fin m} (h : PermCarries (subWorld hB e) ℓ') :
    PermCarriesOn B U (extendLens B e v₀ ℓ') := by
  constructor
  · intro v
    obtain ⟨j, hj⟩ := h.1 v
    refine ⟨(e.symm j : Fin n), (e.symm j).2, ?_⟩
    simp only [extendLens, dif_pos (e.symm j).2]
    rw [show (⟨((e.symm j : {x : Fin n // x ∈ B}) : Fin n), (e.symm j).2⟩ :
      {x : Fin n // x ∈ B}) = e.symm j from rfl, Equiv.apply_symm_apply, hj]
  · intro t x hx
    have hxt : (U ^ t) x ∈ B := pow_mem_of_closed hB t hx
    simp only [extendLens, dif_pos hx, dif_pos hxt]
    have hkey := subWorld_pow_apply hB e t ⟨x, hx⟩
    have hsub : (((subPerm hB) ^ t) ⟨x, hx⟩ : {x : Fin n // x ∈ B}) = ⟨(U ^ t) x, hxt⟩ :=
      Subtype.ext (subPerm_pow_apply hB t ⟨x, hx⟩)
    rw [hsub] at hkey
    rw [← hkey]
    exact h.2 t (e ⟨x, hx⟩)

/-- **The ledger survives restriction to a basin**: on a closed region the second frame is still
determined by the first and the world. -/
theorem permCarriesOn_frame_one {m : ℕ} {U : Perm (Fin n)} {B : Finset (Fin n)}
    {ℓ : ℕ → Fin n → Fin m} (h : PermCarriesOn B U ℓ) {x : Fin n} (hx : x ∈ B) :
    ℓ 1 (U x) = ℓ 0 x := by
  have := h.2 1 x hx
  simpa using this

/-! ## General worlds: capacity over an endofunction ([Persistence] §2, Definitions 2.1–2.2; §3)

Everything above prices a reading over a **permutation** world — the setting §7's counting needs,
where the world is its own recurrent core. [Persistence] §2 assumes no such thing: a world is a
finite set with an update and nothing further, Definition 2.1 states carrying for an arbitrary
`U : Mem → Mem`, and §3's ceiling is precisely about the worlds where that update fails to be
injective. This section brings the budgeted objects to that generality.

The carrying predicate is **not a new one**. It is `Carries`, the §3 predicate, at the state type
`Fin n`: `Carries U ℓ` says `ℓ 0` is surjective and `ℓ t (U^[t] s) = ℓ 0 s` for every `t` and `s`,
which is Definition 2.1 verbatim. `permCarries_iff_carries` records that `PermCarries` is that same
predicate at an invertible update, so the two carrying notions in this file are one notion.

**What the entropy is valued in.** Definition 2.2 measures a lens's carried entropy on a finite
`S ⊆ Mem` as the log-size of its relabelling class *on `S`* — its orbit under `Sym (S)` — and prices
a persistent family by `E (ℓ₀)`, the entropy on the **recurrent core**. The persistence identity is
not silent off the core: it pins `ℓ 0` everywhere, forcing it through the retraction onto the core
(`carries_frame_zero_congr`), and only the LATER frames are free there, reading a state off the
image of `U^[t]` however they like. So `CbHe` values a family at
`Nat.card (orbit (Perm ↥(core U)) (coreLens U (ℓ 0)))`, which is Definition 2.2's `2 ^ (E (ℓ₀))` on
`S = core U`, and `carries_coreLens_eq` is what entitles it to price a whole family by frame zero:
on the core every frame is one relabelling of `ℓ 0`, so all frames share a profile. Over a
permutation world the core is everything and this agrees with `CbH` on the nose (`CbHe_perm`); over
a general world it does not, and the core-restricted reading is the definition's.

**What the budget is valued in.** The budget stays *ambient*: `lensCode` tabulates a frame over the
whole of `Fin n`, exactly as everywhere above, and `PermBudget` / `UniformBudget` are reused
unchanged (neither mentions the world). Value and price are thus measured on different sets, and
deliberately: carried entropy is what a reading *distinguishes*, and Definition 2.2 measures that on
the core; a budget is what a reading *costs to write down*, and a table is written over the states
it enumerates. Restricting the table to the core would price a reading below what it costs to say
where the core sits. -/

/-- **`PermCarries` is `Carries` at an invertible update** — the two carrying predicates of this
file are one predicate. `Carries` is [Persistence] §2, Definition 2.1 verbatim, at an arbitrary
endofunction; `PermCarries` is it over a permutation world, with the iterate `U^[t]` spelled as the
group power `U ^ t`. -/
theorem permCarries_iff_carries {U : Perm (Fin n)} {ℓ : ℕ → Fin n → Fin m} :
    PermCarries U ℓ ↔ Carries (⇑U) ℓ := by
  simp only [PermCarries, PermPersists, Carries, Equiv.Perm.coe_pow]

/-- **A permutation world is its own recurrent core** ([Persistence] §7's standing simplification,
proved rather than assumed): nothing is transient when nothing is irreversible. -/
private theorem core_perm (U : Perm (Fin n)) : core (⇑U) = Set.univ := by
  have h : ∀ t : ℕ, ((⇑U)^[t]) '' Set.univ = (Set.univ : Set (Fin n)) := by
    intro t
    have hs : Function.Surjective ((⇑U)^[t]) := by
      rw [← Equiv.Perm.coe_pow]; exact (U ^ t).surjective
    rw [Set.image_univ, Set.range_eq_univ]
    exact hs
  simp only [core, h, Set.iInter_const]

/-- The core of a permutation world, identified with the world itself. -/
private noncomputable def corePermEquiv (U : Perm (Fin n)) : ↥(core (⇑U)) ≃ Fin n :=
  (Equiv.setCongr (core_perm U)).trans (Equiv.Set.univ (Fin n))

/-- **Carried entropy transports along a relabelling of the domain** ([Persistence] §2, Definition
2.2). The entropy of a lens depends on its fibre profile and the size of the set it is read on,
nothing else — so an identification of domains carries it across. This is what lets the core-valued
capacity below be compared with the ambient one over a permutation world.

Proved by the exact count (`card_orbit_mul_prod_fiber_card`) on each side rather than by exhibiting
an equivalence of orbits: the two orbit cardinalities multiply the *same* fibre product to the
*same* factorial, and the fibre product is positive. -/
private theorem card_orbit_congr {α β : Type*} [Finite α] (e : α ≃ β) (f : α → Fin m) :
    Nat.card ↥(orbit (Perm α) f) = Nat.card ↥(orbit (Perm β) (f ∘ ⇑e.symm)) := by
  have : Finite β := Finite.of_equiv α e
  have hα := card_orbit_mul_prod_fiber_card f
  have hβ := card_orbit_mul_prod_fiber_card (f ∘ ⇑e.symm)
  have hfib : ∀ i : Fin m,
      Nat.card {y : β // (f ∘ ⇑e.symm) y = i} = Nat.card {x : α // f x = i} := fun i =>
    Nat.card_congr (e.symm.subtypeEquiv fun _ => Iff.rfl)
  rw [Nat.card_congr e.symm, Finset.prod_congr rfl fun i _ => by rw [hfib i]] at hβ
  have hpos : 0 < ∏ i : Fin m, (Nat.card {x : α // f x = i})! :=
    Finset.prod_pos fun i _ => Nat.factorial_pos _
  exact Nat.eq_of_mul_eq_mul_right hpos (hα.trans hβ.symm)

/-- **Over a permutation world the core-restricted entropy is the ambient one.** The core is the
whole world (`core_perm`), and carried entropy transports along that identification. -/
private theorem coreOrbit_perm (U : Perm (Fin n)) (f : Fin n → Fin m) :
    Nat.card ↥(orbit (Perm ↥(core (⇑U))) (coreLens (⇑U) f))
      = Nat.card ↥(orbit (Perm (Fin n)) f) := by
  have h := card_orbit_congr (corePermEquiv U) (coreLens (⇑U) f)
  have hcomp : coreLens (⇑U) f ∘ ⇑(corePermEquiv U).symm = f := rfl
  rwa [hcomp] at h

/-- The **carried entropies affordable at budget `b` over a general endofunction world**: the
core-restricted relabelling-class sizes `2 ^ (E (ℓ₀))` ([Persistence] §2, Definition 2.2) of the
reference frames of those families that carry a persistent model over `U` at a per-frame cost of `b`
bits. The `BudgetedEntropies` of §7 is the case of an invertible `U`. -/
def BudgetedEntropiesE (U : Fin n → Fin n) (b : ℕ) : Set ℕ :=
  {N : ℕ | ∃ k : ℕ, ∃ ℓ : ℕ → Fin n → Fin k, Carries U ℓ ∧ PermBudget ℓ b ∧
      N = Nat.card ↥(orbit (Perm ↥(core U)) (coreLens U (ℓ 0)))}

/-- **The entropic budgeted capacity over a general endofunction world** ([Persistence] §5,
Definition 5.4 read at §2's generality), in cardinality form: the largest carried entropy — on the
recurrent core, the only part persistence constrains — of a reference frame whose family costs at
most `b` bits per frame. `sSup ∅ = 0`: a budget that affords no family at all carries nothing. -/
noncomputable def CbHe (U : Fin n → Fin n) (b : ℕ) : ℕ := sSup (BudgetedEntropiesE U b)

/-- The **uniformly** affordable carried entropies over a general endofunction world: as
`BudgetedEntropiesE`, with one program computing every frame instead of a budget per frame. -/
def UniformBudgetedEntropiesE (U : Fin n → Fin n) (b : ℕ) : Set ℕ :=
  {N : ℕ | ∃ k : ℕ, ∃ ℓ : ℕ → Fin n → Fin k, Carries U ℓ ∧ UniformBudget ℓ b ∧
      N = Nat.card ↥(orbit (Perm ↥(core U)) (coreLens U (ℓ 0)))}

/-- **The uniform entropic capacity over a general endofunction world** ([Persistence] §5,
Definition 5.5 read at §2's generality): what an *owner* — one program for the whole family — keeps
at budget `b`. -/
noncomputable def CbHue (U : Fin n → Fin n) (b : ℕ) : ℕ := sSup (UniformBudgetedEntropiesE U b)

/-- No reading distinguishes more of the core than the core has to offer: a relabelling class on the
core is at most `|core U| !`. -/
private theorem budgetedEntropiesE_le {U : Fin n → Fin n} {b N : ℕ}
    (h : N ∈ BudgetedEntropiesE U b) : N ≤ (Nat.card ↥(core U))! := by
  obtain ⟨k, ℓ, -, -, rfl⟩ := h
  have hprod : 0 < ∏ i : Fin k, (Nat.card {x : ↥(core U) // coreLens U (ℓ 0) x = i})! :=
    Finset.prod_pos fun i _ => Nat.factorial_pos _
  exact card_orbit_mul_prod_fiber_card (coreLens U (ℓ 0)) ▸ Nat.le_mul_of_pos_right _ hprod

/-- The uniform variant is bounded for the same reason — the bound is the orbit count and consumes
no budget at all. -/
private theorem uniformBudgetedEntropiesE_le {U : Fin n → Fin n} {b N : ℕ}
    (h : N ∈ UniformBudgetedEntropiesE U b) : N ≤ (Nat.card ↥(core U))! := by
  obtain ⟨k, ℓ, -, -, rfl⟩ := h
  have hprod : 0 < ∏ i : Fin k, (Nat.card {x : ↥(core U) // coreLens U (ℓ 0) x = i})! :=
    Finset.prod_pos fun i _ => Nat.factorial_pos _
  exact card_orbit_mul_prod_fiber_card (coreLens U (ℓ 0)) ▸ Nat.le_mul_of_pos_right _ hprod

/-- The recurrent core is part of the world. -/
private theorem card_core_le (U : Fin n → Fin n) : Nat.card ↥(core U) ≤ n := by
  have h : Nat.card ↥(core U) ≤ Nat.card (Fin n) :=
    Nat.card_le_card_of_injective _ Subtype.val_injective
  simpa using h

private theorem bddAbove_budgetedEntropiesE (U : Fin n → Fin n) (b : ℕ) :
    BddAbove (BudgetedEntropiesE U b) :=
  ⟨(Nat.card ↥(core U))!, fun _ h => budgetedEntropiesE_le h⟩

private theorem bddAbove_uniformBudgetedEntropiesE (U : Fin n → Fin n) (b : ℕ) :
    BddAbove (UniformBudgetedEntropiesE U b) :=
  ⟨(Nat.card ↥(core U))!, fun _ h => uniformBudgetedEntropiesE_le h⟩

/-- **An owned family's carried entropy is affordable over a general endofunction world** — the
`le_csSup` step of the uniform entropic capacity `CbHue`, the general-world counterpart of
`CbHu_ge_of_uniform`. A uniform-budgeted family carrying a persistent model witnesses its
core-restricted reference-frame orbit as a member of what the budget affords. -/
theorem CbHue_ge_of_uniform {U : Fin n → Fin n} {k b : ℕ} {ℓ : ℕ → Fin n → Fin k}
    (hcar : Carries U ℓ) (hbud : UniformBudget ℓ b) :
    Nat.card ↥(orbit (Perm ↥(core U)) (coreLens U (ℓ 0))) ≤ CbHue U b :=
  le_csSup (bddAbove_uniformBudgetedEntropiesE U b) ⟨k, ℓ, hcar, hbud, rfl⟩

/-- **The entropic capacity of a general world is capped by its recurrent core** — the §3 ceiling in
the entropic currency. An observer keeps no more than the reversible part of the world can hold,
whatever it pays. -/
theorem CbHe_le_core_factorial (U : Fin n → Fin n) (b : ℕ) : CbHe U b ≤ (Nat.card ↥(core U))! := by
  rcases Set.eq_empty_or_nonempty (BudgetedEntropiesE U b) with hemp | hne
  · simp [CbHe, hemp]
  · exact csSup_le hne fun _ h => budgetedEntropiesE_le h

private theorem CbHue_le_core_factorial (U : Fin n → Fin n) (b : ℕ) :
    CbHue U b ≤ (Nat.card ↥(core U))! := by
  rcases Set.eq_empty_or_nonempty (UniformBudgetedEntropiesE U b) with hemp | hne
  · simp [CbHue, hemp]
  · exact csSup_le hne fun _ h => uniformBudgetedEntropiesE_le h

theorem CbHue_mono (U : Fin n → Fin n) {b₁ b₂ : ℕ} (h : b₁ ≤ b₂) : CbHue U b₁ ≤ CbHue U b₂ :=
  csSup_le_csSup' (bddAbove_uniformBudgetedEntropiesE U b₂) (by
    rintro N ⟨k, ℓ, hcar, hbud, rfl⟩
    exact ⟨k, ℓ, hcar, UniformBudget.mono hbud h, rfl⟩)

/-- **The general objects restrict to the §7 ones** — the sanity bridge. Over a permutation world
the carrying predicates agree (`permCarries_iff_carries`) and the core is everything
(`coreOrbit_perm`), so the affordable-entropy sets are literally the same set. -/
private theorem budgetedEntropiesE_perm (U : Perm (Fin n)) (b : ℕ) :
    BudgetedEntropiesE (⇑U) b = BudgetedEntropies U b := by
  ext N
  constructor
  · rintro ⟨k, ℓ, hcar, hbud, rfl⟩
    exact ⟨k, ℓ, permCarries_iff_carries.mpr hcar, hbud, coreOrbit_perm U (ℓ 0)⟩
  · rintro ⟨k, ℓ, hcar, hbud, rfl⟩
    exact ⟨k, ℓ, permCarries_iff_carries.mp hcar, hbud, (coreOrbit_perm U (ℓ 0)).symm⟩

private theorem uniformBudgetedEntropiesE_perm (U : Perm (Fin n)) (b : ℕ) :
    UniformBudgetedEntropiesE (⇑U) b = UniformBudgetedEntropies U b := by
  ext N
  constructor
  · rintro ⟨k, ℓ, hcar, hbud, rfl⟩
    exact ⟨k, ℓ, permCarries_iff_carries.mpr hcar, hbud, coreOrbit_perm U (ℓ 0)⟩
  · rintro ⟨k, ℓ, hcar, hbud, rfl⟩
    exact ⟨k, ℓ, permCarries_iff_carries.mp hcar, hbud, (coreOrbit_perm U (ℓ 0)).symm⟩

/-- **The general capacity agrees with the §7 capacity over a permutation world.** Nothing above is
disturbed by the generalization: `CbH` is `CbHe` at an invertible update. -/
theorem CbHe_perm (U : Perm (Fin n)) (b : ℕ) : CbHe (⇑U) b = CbH U b := by
  rw [CbHe, CbH, budgetedEntropiesE_perm]

/-- The uniform objects agree likewise: `CbHu` is `CbHue` at an invertible update. -/
theorem CbHue_perm (U : Perm (Fin n)) (b : ℕ) : CbHue (⇑U) b = CbHu U b := by
  rw [CbHue, CbHu, uniformBudgetedEntropiesE_perm]

/-! ## The floor does not survive irreversibility ([Persistence] §7, Proposition 7.9)

`CbHe_le_core_factorial` just above is the CAP over a general endofunction world, and it is
unaffected by what follows. This section is the FLOOR beneath it, and it does not survive:
Corollary 7.5(i) floors `CbH` at `(1/2 − o(1)) · b` over EVERY permutation world, but fold a core
of transient states into it and the floor is gone — generically the capacity is exactly zero,
however large the core. Reversibility is not a convenience in that corollary's hypothesis; it is
what makes the retraction onto the core the identity, and folding it forces the reading to pay for
the fold, a description of the WORLD rather than of the reading. -/

/-- **The world of a `c`-cycle core with one-step basins**: a fixed cycle `cyc` runs the first `c`
states, and each of `tr` further states is routed directly into the core by `β`. Every world of
this shape shares the same core (the first `c` states) and differs only in `β`, so the `c ^ tr`
choices of `β` enumerate the worlds of the shape outright. -/
def basinWorld {c tr : ℕ} (cyc : Perm (Fin c)) (β : Fin tr → Fin c) : Fin (c + tr) → Fin (c + tr) :=
  Fin.append (fun i => Fin.castAdd tr (cyc i)) (fun j => Fin.castAdd tr (β j))

/-- The world acts as the fixed cycle on the core. -/
@[simp] private theorem basinWorld_core {c tr : ℕ} (cyc : Perm (Fin c)) (β : Fin tr → Fin c)
    (i : Fin c) : basinWorld cyc β (Fin.castAdd tr i) = Fin.castAdd tr (cyc i) := by
  simp [basinWorld, Fin.append_left]

/-- The world routes a transient state into the core by `β`, in one step. -/
@[simp] private theorem basinWorld_transient {c tr : ℕ} (cyc : Perm (Fin c)) (β : Fin tr → Fin c)
    (j : Fin tr) : basinWorld cyc β (Fin.natAdd c j) = Fin.castAdd tr (β j) := by
  simp [basinWorld, Fin.append_right]

/-- **The reference frame at a transient state is pinned by the frame at the core state one cycle
step behind its landing point** — reading the persistence identity at `t = 1` twice, once through
the transient route and once through the core route it lands beside, and matching the two. This is
the mechanism behind Proposition 7.9(i): `carries_frame_zero_congr` gives the general merging
statement, and this is what merging costs a transient state specifically, in THIS shape of world. -/
private theorem basinWorld_confine {c tr k : ℕ} {cyc : Perm (Fin c)} {β : Fin tr → Fin c}
    {ℓ : Lens (Fin (c + tr)) (Fin k)} (h : Carries (basinWorld cyc β) ℓ) (j : Fin tr) :
    ℓ 0 (Fin.castAdd tr (cyc.symm (β j))) = ℓ 0 (Fin.natAdd c j) := by
  have e1 : ℓ 1 (Fin.castAdd tr (β j)) = ℓ 0 (Fin.natAdd c j) := by
    have := h.2 1 (Fin.natAdd c j)
    rwa [Function.iterate_one, basinWorld_transient] at this
  have e2 : ℓ 1 (Fin.castAdd tr (β j)) = ℓ 0 (Fin.castAdd tr (cyc.symm (β j))) := by
    have := h.2 1 (Fin.castAdd tr (cyc.symm (β j)))
    rwa [Function.iterate_one, basinWorld_core, Equiv.apply_symm_apply] at this
  rw [← e1, e2]

/-- A non-constant function's fibres are all proper: none of them is the whole domain, so each has
at most `c - 1` elements. -/
private theorem card_fiber_le_of_nonconst {c k : ℕ} {f : Fin c → Fin k} (hf : ∃ x y, f x ≠ f y)
    (v : Fin k) : Nat.card {x : Fin c // f x = v} ≤ c - 1 := by
  obtain ⟨x, y, hxy⟩ := hf
  have hne : {x : Fin c | f x = v} ≠ Set.univ := by
    intro heq
    exact hxy (by rw [show f x = v from Set.eq_univ_iff_forall.mp heq x,
      show f y = v from Set.eq_univ_iff_forall.mp heq y])
  have hssub : {x : Fin c | f x = v} ⊂ Set.univ := Set.ssubset_univ_iff.mpr hne
  have hlt := Set.ncard_lt_ncard hssub Set.finite_univ
  rw [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin] at hlt
  have hcast : Nat.card {x : Fin c // f x = v} = {x : Fin c | f x = v}.ncard :=
    Nat.card_coe_set_eq _
  omega

/-- The `β` compatible with a fixed core reading `g` and transient reading `hval` — landing, for
each transient state, in the core fibre its own table entry names — is a Pi type of fibres. -/
private noncomputable def compatEquiv {c tr k : ℕ} (cyc : Perm (Fin c)) (g : Fin c → Fin k)
    (hval : Fin tr → Fin k) : {β : Fin tr → Fin c // ∀ j, g (cyc.symm (β j)) = hval j}
      ≃ ∀ j : Fin tr, {x : Fin c // g (cyc.symm x) = hval j} :=
  Equiv.subtypePiEquivPi (p := fun (j : Fin tr) (x : Fin c) => g (cyc.symm x) = hval j)

/-- **The confined count** ([Persistence] §7, Proposition 7.9(ii)'s counting core): the `β`
compatible with a fixed NON-CONSTANT core reading `g` and a fixed transient reading `hval` number
at most `(c - 1) ^ tr` — each of the `tr` transient states is confined to one fibre of `g`, and a
non-constant `g`'s fibres are all of size at most `c - 1`. -/
private theorem card_compat_le {c tr k : ℕ} (cyc : Perm (Fin c)) {g : Fin c → Fin k}
    (hg : ∃ x y, g x ≠ g y) (hval : Fin tr → Fin k) :
    Nat.card {β : Fin tr → Fin c // ∀ j, g (cyc.symm (β j)) = hval j} ≤ (c - 1) ^ tr := by
  rw [Nat.card_congr (compatEquiv cyc g hval), Nat.card_pi]
  have hgc : ∃ x y, (fun x => g (cyc.symm x)) x ≠ (fun x => g (cyc.symm x)) y := by
    obtain ⟨x, y, hxy⟩ := hg
    exact ⟨cyc x, cyc y, by simpa using hxy⟩
  calc ∏ j : Fin tr, Nat.card {x : Fin c // g (cyc.symm x) = hval j}
      ≤ ∏ _j : Fin tr, (c - 1) :=
        Finset.prod_le_prod (fun _ _ => Nat.zero_le _)
          (fun j _ => card_fiber_le_of_nonconst hgc (hval j))
    _ = (c - 1) ^ tr := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- At most `2 ^ (b + 1)` reference frames on `Fin n → Fin k` are affordable at budget `b` —
`card_KE_le`'s counting bound, pulled back along `lensCode`'s injectivity. -/
private theorem card_affordable_le (n k b : ℕ) :
    Nat.card {f : Fin n → Fin k // KE (lensCode f) ≤ b} ≤ 2 ^ (b + 1) := by
  have : Finite {v : ℕ // KE v ≤ b} := (finite_KE_le b).to_subtype
  have hinj : Function.Injective
      (fun f : {f : Fin n → Fin k // KE (lensCode f) ≤ b} =>
        (⟨lensCode f.1, f.2⟩ : {v : ℕ // KE v ≤ b})) := by
    intro a a' hab
    exact Subtype.ext (lensCode_injective (congrArg Subtype.val hab))
  have hle := Nat.card_le_card_of_injective _ hinj
  have heq : Nat.card {v : ℕ // KE v ≤ b} = {v : ℕ | KE v ≤ b}.ncard := Nat.card_coe_set_eq _
  have hcard := card_KE_le b
  omega

/-- **Proposition 7.9(ii)** ([Persistence] §7): fix a `c`-cycle core and route each of `tr`
transient states directly into it by `β`. At budget `b`, over a fixed label count `k`, at most
`2 ^ (b + 1) * (c - 1) ^ tr` of the `c ^ tr` worlds of this shape admit ANY non-constant affordable
carried family — a vanishing fraction as `tr → ∞` at fixed `c`, `b`, `k`, however large the core:
folding the carrier into a core forces the reading to pay for the fold, which is a description of
the world and not of the reading.

The mechanism: a carried family's reference frame at a transient state is pinned, by
`basinWorld_confine`, to agree with the reference frame at one specific core state — so once the
frame is fixed and affordable (`card_affordable_le`), each transient state has at most `c - 1`
places left to be routed to (`card_compat_le`), and the two bounds multiply. -/
theorem card_basinWorld_carries_le (c tr k b : ℕ) (cyc : Perm (Fin c)) :
    Nat.card {β : Fin tr → Fin c //
        ∃ ℓ : ℕ → Fin (c + tr) → Fin k, Carries (basinWorld cyc β) ℓ ∧ PermBudget ℓ b ∧
          ∃ x y : Fin c, ℓ 0 (Fin.castAdd tr x) ≠ ℓ 0 (Fin.castAdd tr y)}
      ≤ 2 ^ (b + 1) * (c - 1) ^ tr := by
  classical
  set AffN := {f : Fin (c + tr) → Fin k //
      KE (lensCode f) ≤ b ∧ ∃ x y : Fin c, f (Fin.castAdd tr x) ≠ f (Fin.castAdd tr y)}
    with hAffdef
  have hAffCard : Nat.card AffN ≤ 2 ^ (b + 1) := by
    have : Finite {v : ℕ // KE v ≤ b} := (finite_KE_le b).to_subtype
    have hinj : Function.Injective
        (fun f : AffN => (⟨lensCode f.1, f.2.1⟩ : {v : ℕ // KE v ≤ b})) :=
      fun a a' hab => Subtype.ext (lensCode_injective (congrArg Subtype.val hab))
    have hle := Nat.card_le_card_of_injective _ hinj
    have heq : Nat.card {v : ℕ // KE v ≤ b} = {v : ℕ | KE v ≤ b}.ncard := Nat.card_coe_set_eq _
    have hcard := card_KE_le b
    omega
  have hAffFin : Finite AffN := by
    have : Finite {v : ℕ // KE v ≤ b} := (finite_KE_le b).to_subtype
    exact Finite.of_injective (fun f : AffN => (⟨lensCode f.1, f.2.1⟩ : {v : ℕ // KE v ≤ b}))
      (fun a a' hab => Subtype.ext (lensCode_injective (congrArg Subtype.val hab)))
  have : Fintype AffN := Fintype.ofFinite _
  set Compat : AffN → (Fin tr → Fin c) → Prop :=
      fun f β' => ∀ j, f.1 (Fin.castAdd tr (cyc.symm (β' j))) = f.1 (Fin.natAdd c j)
    with hCompatdef
  -- the sigma type: an affordable non-constant frame, and a `β'` compatible with it
  have hSigmaCard : Nat.card {p : AffN × (Fin tr → Fin c) // Compat p.1 p.2}
      ≤ 2 ^ (b + 1) * (c - 1) ^ tr := by
    rw [Nat.card_congr (Equiv.subtypeProdEquivSigmaSubtype Compat), Nat.card_sigma]
    calc ∑ f : AffN, Nat.card {β' // Compat f β'}
        ≤ ∑ _f : AffN, (c - 1) ^ tr := by
          refine Finset.sum_le_sum fun f _ => ?_
          exact card_compat_le cyc f.2.2 (fun j => f.1 (Fin.natAdd c j))
      _ = Nat.card AffN * (c - 1) ^ tr := by
          rw [Finset.sum_const, Finset.card_univ, Nat.card_eq_fintype_card, smul_eq_mul]
      _ ≤ 2 ^ (b + 1) * (c - 1) ^ tr := Nat.mul_le_mul_right _ hAffCard
  have hΦinj : Function.Injective (fun s : {β : Fin tr → Fin c //
        ∃ ℓ : ℕ → Fin (c + tr) → Fin k, Carries (basinWorld cyc β) ℓ ∧ PermBudget ℓ b ∧
          ∃ x y : Fin c, ℓ 0 (Fin.castAdd tr x) ≠ ℓ 0 (Fin.castAdd tr y)} =>
      (⟨(⟨s.2.choose 0, s.2.choose_spec.2.1 0, s.2.choose_spec.2.2⟩, s.1),
        fun j => basinWorld_confine s.2.choose_spec.1 j⟩ :
        {p : AffN × (Fin tr → Fin c) // Compat p.1 p.2})) := by
    intro s s' hss'
    exact Subtype.ext (congrArg Prod.snd (congrArg Subtype.val hss'))
  calc Nat.card {β : Fin tr → Fin c // ∃ ℓ : ℕ → Fin (c + tr) → Fin k,
        Carries (basinWorld cyc β) ℓ ∧ PermBudget ℓ b ∧
          ∃ x y : Fin c, ℓ 0 (Fin.castAdd tr x) ≠ ℓ 0 (Fin.castAdd tr y)}
      ≤ Nat.card {p : AffN × (Fin tr → Fin c) // Compat p.1 p.2} :=
        Nat.card_le_card_of_injective _ hΦinj
    _ ≤ 2 ^ (b + 1) * (c - 1) ^ tr := hSigmaCard

/-! ## Time dilation: the rule transports at `O (log τ)`

A reading need not keep step with the world. A family that carries a model *every `τ` steps* —
`ℓ_{t+1} (U^[τ] s) = ℓ t s` — is exactly a family carrying a model over the world `U^[τ]`, so the
dilated question reduces to the undilated one over a different world. What that reduction costs is
the price of the dilated *rule*, and the answer is that it costs almost nothing:
`K (U^[τ]) ≤ K (U) + O (log τ)`, the `O (log τ)` being the clock alone.

`iterBuilder` is the witness — one fixed program, independent of the world and of `n`, that composes
a table with itself. So a slow reading is not a cheaper reading: whatever a `τ`-dilated observer can
afford over `U`, an undilated one affords over `U^[τ]` at a rule cost greater by `O (log τ)` — and
`τ`'s only appearance is through its binary numeral. Dilation is nearly free on the rule side, and
the ceiling it faces is `core (U^[τ])`, which is `core U` itself when `U` is a permutation.

This is the rule-side half only. Nothing here says a dilated family carries the same entropy; it
says the world it carries over is no harder to describe. -/

/-- **Composing two tabulated endofunctions**: entry `i` of `stepComp T T'` is `T`'s entry at `T'`'s
entry `i` — the table of `U ∘ V` from the tables of `U` and `V`. Unlike `ownStep`, which inverts a
permutation's table, this needs nothing of `U` but that it be a function. -/
def stepComp (T T' : List ℕ) : List ℕ := T'.map fun v => T.getD v 0

/-- **The table of `U^[τ]`**, by self-composition. The identity's table is `List.range n`, read off
`T`'s own length — no size parameter is loaded, and none is needed. -/
private def iterTable (T : List ℕ) (τ : ℕ) : List ℕ := (stepComp T)^[τ] (List.range T.length)

/-- Composition of tables tabulates composition of functions. -/
private theorem stepComp_lensTable (U V : Fin n → Fin n) :
    stepComp (lensTable U) (lensTable V) = lensTable (U ∘ V) := by
  simp only [stepComp, lensTable, List.map_map]
  refine List.map_congr_left fun i _ => ?_
  exact getD_map_finRange (fun j : Fin n => ((U j : Fin n) : ℕ)) (V i)

/-- Iterated self-composition tabulates the iterate: `τ` steps of `stepComp` against `U`'s own table
turn the identity's table into `U^[τ]`'s. -/
private theorem iterTable_lensTable (U : Fin n → Fin n) (τ : ℕ) :
    iterTable (lensTable U) τ = lensTable (U^[τ]) := by
  induction τ with
  | zero => simp [iterTable, lensTable]
  | succ t ih =>
      have hstep : iterTable (lensTable U) (t + 1)
          = stepComp (lensTable U) (iterTable (lensTable U) t) :=
        Function.iterate_succ_apply' _ _ _
      rw [hstep, ih, stepComp_lensTable, ← Function.iterate_succ']

/-- **The dilation builder, from `⟨U's table, τ⟩`** — ONE fixed function of a single natural number,
carrying no dependence on `n` or the world: decode the table, compose it with itself `τ` times,
re-encode. -/
private def iterTableFn (p : ℕ) : ℕ :=
  Encodable.encode (iterTable ((Encodable.decode (α := List ℕ) p.unpair.1).getD []) p.unpair.2)

private theorem primrec_stepComp : Primrec₂ stepComp := by
  have hg : Primrec₂ fun (q : List ℕ × List ℕ) (v : ℕ) => q.1.getD v 0 :=
    ((Primrec.list_getD 0).comp (Primrec.fst.comp Primrec.fst) Primrec.snd).to₂
  exact (Primrec.list_map Primrec.snd hg).to₂

private theorem primrec_iterTable : Primrec₂ iterTable := by
  have hg : Primrec₂ fun (T : List ℕ) (p : ℕ × List ℕ) => stepComp T p.2 :=
    (primrec_stepComp.comp Primrec.fst (Primrec.snd.comp Primrec.snd)).to₂
  exact (Primrec.nat_rec (f := fun T : List ℕ => List.range T.length)
    (Primrec.list_range.comp Primrec.list_length) hg).of_eq
    fun T τ => natRec_iterate (stepComp T) (List.range T.length) τ

/-- **The dilation builder is primitive recursive.** Decoding is `Primrec.decode`, composition is a
`List.map`, and the iteration is `Nat.rec`. -/
private theorem primrec_iterTableFn : Primrec iterTableFn := by
  have hdecT : Primrec fun p : ℕ => (Encodable.decode (α := List ℕ) p.unpair.1).getD [] :=
    Primrec.option_getD.comp
      (Primrec.decode.comp (Primrec.fst.comp Primrec.unpair)) (Primrec.const [])
  have hτ : Primrec fun p : ℕ => p.unpair.2 := Primrec.snd.comp Primrec.unpair
  exact Primrec.encode.comp (primrec_iterTable.comp hdecT hτ)

private theorem partrec_iterTableFn : Nat.Partrec (fun p : ℕ => (iterTableFn p : ℕ)) :=
  _root_.Partrec.nat_iff.mp (Primrec.to_comp primrec_iterTableFn).partrec

/-- **The fixed self-composition builder code.** One program, independent of the world and of
`n`. -/
noncomputable def iterBuilder : Nat.Partrec.Code :=
  Classical.choose (Nat.Partrec.Code.exists_code.mp partrec_iterTableFn)

/-- The builder's evaluation law. -/
private theorem eval_iterBuilder (p : ℕ) :
    Nat.Partrec.Code.eval iterBuilder p = Part.some (iterTableFn p) := by
  have h := congrFun (Classical.choose_spec
    (Nat.Partrec.Code.exists_code.mp partrec_iterTableFn)) p
  simpa [iterBuilder] using h

/-- **The builder is correct**: on `⟨U's table, τ⟩` it outputs `U^[τ]`'s encoded tabulation. -/
private theorem iterTableFn_eq (U : Fin n → Fin n) (τ : ℕ) :
    iterTableFn (Nat.pair (lensCode U) τ) = lensCode (U^[τ]) := by
  rw [iterTableFn]
  simp only [Nat.unpair_pair, decode_lensCode]
  rw [iterTable_lensTable]
  rfl

/-- **The dilated rule costs the rule plus the clock** — time dilation is nearly free on the rule
side. Given any code for `U`'s table, `U^[τ]`'s table has a description longer by
`(15 + elen dbl) · Nat.size τ` — the binary numeral for `τ` — plus the absolute constant
`elen iterBuilder + (15 + elen dbl) + 6`, which depends on neither the world, nor `τ`, nor `n`.

The assembled program is `comp iterBuilder (pair cU (bconst τ))`: recover the table, hand it to the
builder with `τ`'s binary numeral, and the builder composes the table with itself `τ` times.

`τ` enters through `Nat.size τ` and nowhere else, so a `τ`-fold slower world is a `log₂ τ`-more
expensive world — an observer that reads every `τ` steps buys its dilation for the price of naming
`τ`. As with `ownership`, the bound is in terms of the *given* code's length rather than `KE`; the
two coincide when the code is `KE`-optimal. -/
theorem KE_iterate_le (U : Fin n → Fin n) (cU : Nat.Partrec.Code)
    (hU : cU.eval 0 = Part.some (lensCode U)) (τ : ℕ) :
    KE (lensCode (U^[τ])) ≤ elen cU + (15 + elen dbl) * Nat.size τ
      + (elen iterBuilder + (15 + elen dbl) + 6) := by
  have hp : Nat.Partrec.Code.eval (Nat.Partrec.Code.pair cU (bconst τ)) 0
      = Part.some (Nat.pair (lensCode U) τ) := by
    change Nat.pair <$> _ <*> _ = _
    rw [hU, eval_bconst]; simp [Seq.seq]
  have hcomp : Computes (Nat.Partrec.Code.comp iterBuilder (Nat.Partrec.Code.pair cU (bconst τ)))
      (lensCode (U^[τ])) := by
    change Nat.Partrec.Code.eval _ 0 = _
    rw [eval_comp_some hp, eval_iterBuilder, iterTableFn_eq]
  have hle := KE_le hcomp
  rw [E_len_comp, E_len_pair] at hle
  have hb := elen_bconst_le τ
  omega

/-! ## Settling from a basin: eventual capacity is exact capacity on the attractor
([Persistence] §10.1 (silent self-stabilization) + §2–§3)

§10.1 relaxes "correct at every step" to "correct after a transient" — the *silence* property of
self-stabilization — and Theorem 10.1 settles the question for a STATIC decoder
(`eventual_decoupling_iff`). This section asks the budgeted question for a lens *family*: how much
carried entropy can an observer keep if it is allowed to be wrong for a while?

The answer is that the relaxation buys nothing and costs nothing: **eventual capacity from a basin
`B` is exact capacity on its attractor `ω(B)`** (`CbHev_eq_CbHeOn`). Both directions are a shift of
the clock. A settling family, run past its transient, exactly carries on `ω(B)` — orbits from `B`
are inside `ω(B)` by then, and the frames are *reused*, so the per-frame budget transfers
untouched. Conversely an exact family on `ω(B)`, its clock delayed by the space transient, settles
from all of `B`.

Two things make this reduction pay. `ω(B)` is a permutation world (`omegaLimit_bijOn`,
`omegaPerm`), so everything §7 proves about permutation worlds applies to it verbatim — the
attractor is not a new setting. And the reduction is **budget-free in both directions**: frames are
priced by `lensCode` over the ambient world on both sides, and a shift reuses frames rather than
rebuilding them, so no table is ever re-indexed. Restricting the *frames* to `ω(B)` would not be
free — an ambient table cannot be traded for a sub-world table without paying to say where the
sub-world sits — which is why the frames stay ambient here and only the *value* is read on the
attractor's subtype, exactly as `CbHe` does on the core. -/

/-- **Exact carrying on a region**, with the frames priced ambiently ([Persistence] §2, Definition
2.1, read on a subset). The frames are functions of the whole world; only their behaviour on `S` is
constrained, and `lensCode` prices them over the whole world as everywhere else. -/
def CarriesOn {m : ℕ} (U : Fin n → Fin n) (ℓ : ℕ → Fin n → Fin m) (S : Set (Fin n)) : Prop :=
  Set.SurjOn (ℓ 0) S Set.univ ∧ ∀ t, ∀ x ∈ S, ℓ t (U^[t] x) = ℓ 0 x

/-- **Settling from a basin** — the lens-family form of [Persistence] §10.1's hypothesis, where
Theorem 10.1 (`eventual_decoupling_iff`) states it for a static decoder. Along every orbit from `B`
the reading is eventually constant, at the value `v` records; the transient `T` is *pointwise* and
depends on the family, so no bound on it is assumed here.

**Which map carries the surjectivity, and why it is `v`.** The demand is that the *settled value*
be surjective, not that frame zero be. This is the convention the reduction needs and it is the
honest one: the carried content of a settling family is what it settles to. A family whose frame
zero is surjective may settle to a single value — distinguishing nothing, forever — so with the
surjectivity on `ℓ 0` the reduction below is simply false in the `⇒` direction. -/
def EventuallyCarries {m : ℕ} (U : Fin n → Fin n) (ℓ : ℕ → Fin n → Fin m) (B : Finset (Fin n))
    (v : Fin n → Fin m) : Prop :=
  Set.SurjOn v ↑B Set.univ ∧ ∀ s ∈ B, ∃ T, ∀ t ≥ T, ℓ t (U^[t] s) = v s

/-- A `U`-closed `Finset` is a `U`-closed set. -/
private theorem coe_closed {U : Fin n → Fin n} {B : Finset (Fin n)} (hB : ∀ i ∈ B, U i ∈ B) :
    ∀ s ∈ (↑B : Set (Fin n)), U s ∈ (↑B : Set (Fin n)) := fun s hs => hB s hs

/-- **Reading the attractor through the world's own iterate does not change the carried entropy.**
Precomposing with `U^[t]` is, on the attractor, precomposing with a power of `omegaPerm` — a
relabelling — so it lands in the same orbit. This is what makes the value of a settling family
independent of *when* it is read, and it is the engine of both directions of the reduction. -/
theorem orbit_restrict_iterate {U : Fin n → Fin n} {B : Set (Fin n)} (hB : ∀ s ∈ B, U s ∈ B)
    (f : Fin n → Fin m) (t : ℕ) :
    orbit (Perm ↥(omegaLimit U B)) ((omegaLimit U B).domRestrict (f ∘ U^[t]))
      = orbit (Perm ↥(omegaLimit U B)) ((omegaLimit U B).domRestrict f) := by
  have h : (omegaLimit U B).domRestrict (f ∘ U^[t])
      = ((omegaPerm U hB ^ t)⁻¹) • ((omegaLimit U B).domRestrict f) := by
    funext x
    simp only [smul_lens_apply, inv_inv, Set.domRestrict_apply, Function.comp_apply,
      omegaPerm_pow_apply]
  rw [h, orbit_smul]

/-- **Every frame is the reference frame, transported** — `carries_coreLens_eq` for an attractor.
`ω(B)` is a permutation world, so an exactly-carrying family has no freedom there past frame
zero. -/
theorem carriesOn_restrict_eq {U : Fin n → Fin n} {B : Set (Fin n)} (hB : ∀ s ∈ B, U s ∈ B)
    {ℓ : ℕ → Fin n → Fin m} (h : CarriesOn U ℓ (omegaLimit U B)) (t : ℕ) :
    (omegaLimit U B).domRestrict (ℓ t)
      = (omegaLimit U B).domRestrict (ℓ 0) ∘ ⇑(omegaPerm U hB ^ t)⁻¹ := by
  funext x
  have hy := h.2 t (((omegaPerm U hB ^ t)⁻¹ x : ↥(omegaLimit U B)) : Fin n)
    ((omegaPerm U hB ^ t)⁻¹ x).2
  rw [← omegaPerm_pow_apply U hB t ((omegaPerm U hB ^ t)⁻¹ x)] at hy
  simpa using hy

/-- The **carried entropies affordable at budget `b` for a reading exact on `S`**: the
relabelling-class sizes of the reference frame *restricted to `S`* ([Persistence] §2, Definition
2.2, whose `E_S` is measured on exactly such an `S`). -/
def EntropiesOn (U : Fin n → Fin n) (S : Set (Fin n)) (b : ℕ) : Set ℕ :=
  {N : ℕ | ∃ k : ℕ, ∃ ℓ : ℕ → Fin n → Fin k, CarriesOn U ℓ S ∧ PermBudget ℓ b ∧
      N = Nat.card ↥(orbit (Perm ↥S) (S.domRestrict (ℓ 0)))}

/-- **The exact entropic capacity on a region**, in cardinality form. `CbHe` is the case
`S = core U` up to the reference frame's relabelling. -/
noncomputable def CbHeOn (U : Fin n → Fin n) (S : Set (Fin n)) (b : ℕ) : ℕ :=
  sSup (EntropiesOn U S b)

/-- The **carried entropies affordable at budget `b` to an observer allowed a transient**: the
relabelling class, on the attractor, of the value a settling family settles to. -/
def EventualEntropies (U : Fin n → Fin n) (B : Finset (Fin n)) (b : ℕ) : Set ℕ :=
  {N : ℕ | ∃ k : ℕ, ∃ ℓ : ℕ → Fin n → Fin k, ∃ v : Fin n → Fin k,
      EventuallyCarries U ℓ B v ∧ PermBudget ℓ b ∧
      N = Nat.card ↥(orbit (Perm ↥(omegaLimit U ↑B)) ((omegaLimit U ↑B).domRestrict v))}

/-- **The eventual entropic capacity from a basin** ([Persistence] §10.1 read at §5's budget): the
largest carried entropy an observer can settle to from `B`, at `b` bits per frame. -/
noncomputable def CbHev (U : Fin n → Fin n) (B : Finset (Fin n)) (b : ℕ) : ℕ :=
  sSup (EventualEntropies U B b)

/-- **The reduction, at the level of achievable values** — the probe's verdict. The entropies a
settling family can reach from `B` are *exactly* those an exactly-carrying family reaches on `ω(B)`,
at the same budget.

`⇒` runs the family past `T := max (its own pointwise transients over the finite basin) (the space
transient)`: orbits from `B` fill `ω(B)` by then, the shifted family carries there exactly, and its
frames are the original family's — so the budget is untouched. `⇐` delays an exact family's clock by
the space transient, which settles it from all of `B` within `≤` that transient.

Neither direction re-indexes a table: the frames are ambient on both sides and shifting reuses
them. -/
theorem eventualEntropies_eq (U : Fin n → Fin n) {B : Finset (Fin n)} (hB : ∀ i ∈ B, U i ∈ B)
    (b : ℕ) : EventualEntropies U B b = EntropiesOn U (omegaLimit U ↑B) b := by
  have hB' := coe_closed hB
  obtain ⟨Nst, hNst⟩ := exists_image_stable U hB'
  have homega : omegaLimit U ↑B = (U^[Nst]) '' ↑B := omegaLimit_eq_image U hB' hNst
  ext N
  constructor
  · rintro ⟨k, ℓ, v, hev, hbud, rfl⟩
    choose! Tf hTf using hev.2
    set T := max (B.sup Tf) Nst with hTdef
    have hTge : ∀ s ∈ B, Tf s ≤ T := fun s hs => le_trans (Finset.le_sup hs) (le_max_left _ _)
    have himg : (U^[T]) '' (↑B : Set (Fin n)) = omegaLimit U ↑B := by
      rw [homega]; exact hNst T (le_max_right _ _)
    -- the value is read at `T` through the world's own iterate, hence in `ℓ T`'s class
    have hveq : (omegaLimit U ↑B).domRestrict v = (omegaLimit U ↑B).domRestrict (ℓ T ∘ U^[T]) := by
      funext x
      have hxB : (x : Fin n) ∈ B := omegaLimit_subset U (↑B) x.2
      exact (hTf _ hxB T (hTge _ hxB)).symm
    refine ⟨k, fun u => ℓ (T + u), ⟨?_, ?_⟩, fun t => hbud (T + t), ?_⟩
    · intro y _
      obtain ⟨s, hs, hvs⟩ := hev.1 (Set.mem_univ y)
      refine ⟨U^[T] s, by rw [← himg]; exact ⟨s, hs, rfl⟩, ?_⟩
      simpa using (hTf s hs T (hTge s hs)).trans hvs
    · intro t x hx
      rw [← himg] at hx
      obtain ⟨s, hs, rfl⟩ := hx
      have hsB : s ∈ B := hs
      have hcomm : U^[t] (U^[T] s) = U^[T + t] s := by
        rw [← Function.iterate_add_apply, Nat.add_comm]
      simp only [Nat.add_zero, hcomm]
      rw [hTf s hsB (T + t) (le_trans (hTge s hsB) (Nat.le_add_right T t)),
        hTf s hsB T (hTge s hsB)]
    · simp only [Nat.add_zero]
      rw [hveq, orbit_restrict_iterate hB' (ℓ T) T]
  · rintro ⟨k, ℓ, hcar, hbud, rfl⟩
    refine ⟨k, fun t => ℓ (t - Nst), fun s => ℓ 0 (U^[Nst] s), ⟨?_, ?_⟩,
      fun t => hbud (t - Nst), ?_⟩
    · intro y _
      obtain ⟨x, hx, hxy⟩ := hcar.1 (Set.mem_univ y)
      rw [homega] at hx
      obtain ⟨s, hs, rfl⟩ := hx
      exact ⟨s, hs, hxy⟩
    · intro s hs
      refine ⟨Nst, fun t ht => ?_⟩
      have hmem : U^[Nst] s ∈ omegaLimit U ↑B := by rw [homega]; exact ⟨s, hs, rfl⟩
      have h := hcar.2 (t - Nst) _ hmem
      rwa [← Function.iterate_add_apply, Nat.sub_add_cancel ht] at h
    · exact (orbit_restrict_iterate hB' (ℓ 0) Nst).symm ▸ rfl

/-- **Eventual capacity from a basin IS exact capacity on its attractor** ([Persistence] §10.1 read
at §5's budget) — the settling probe's verdict.

An observer allowed to be wrong for a while, over a world it cannot leave, keeps exactly what an
observer required to be right from the first step keeps over the attractor — at the same price per
frame. Being wrong for a while is worth nothing, and it costs nothing; the transient is a shift of
the clock and nothing else.

Since `ω(B)` is a permutation world (`omegaPerm`), the whole of §7 applies to it: the eventual
question over an irreversible world is the exact question over a reversible one. -/
theorem CbHev_eq_CbHeOn (U : Fin n → Fin n) {B : Finset (Fin n)} (hB : ∀ i ∈ B, U i ∈ B) (b : ℕ) :
    CbHev U B b = CbHeOn U (omegaLimit U ↑B) b := by
  rw [CbHev, CbHeOn, eventualEntropies_eq U hB b]

/-- No reading distinguishes more of a region than the region has to offer. -/
private theorem entropiesOn_le {U : Fin n → Fin n} {S : Set (Fin n)} {b N : ℕ}
    (h : N ∈ EntropiesOn U S b) : N ≤ (Nat.card ↥S)! := by
  obtain ⟨k, ℓ, -, -, rfl⟩ := h
  have hprod : 0 < ∏ i : Fin k, (Nat.card {x : ↥S // S.domRestrict (ℓ 0) x = i})! :=
    Finset.prod_pos fun i _ => Nat.factorial_pos _
  exact card_orbit_mul_prod_fiber_card (S.domRestrict (ℓ 0)) ▸ Nat.le_mul_of_pos_right _ hprod

/-- **The attractor is the ceiling on eventual capacity** — the §3 ceiling, relativized to a basin
and read in the entropic currency. A transient buys no more than the attractor can hold. -/
private theorem CbHeOn_le_factorial (U : Fin n → Fin n) (S : Set (Fin n)) (b : ℕ) :
    CbHeOn U S b ≤ (Nat.card ↥S)! := by
  rcases Set.eq_empty_or_nonempty (EntropiesOn U S b) with hemp | hne
  · simp [CbHeOn, hemp]
  · exact csSup_le hne fun _ h => entropiesOn_le h

theorem CbHev_le_factorial (U : Fin n → Fin n) {B : Finset (Fin n)} (hB : ∀ i ∈ B, U i ∈ B)
    (b : ℕ) : CbHev U B b ≤ (Nat.card ↥(omegaLimit U ↑B))! := by
  rw [CbHev_eq_CbHeOn U hB b]; exact CbHeOn_le_factorial U _ b

/-! ## Owning beats renting by at most the clock, over ANY world

`CbHu_le_CbH` compares the two budgets over a permutation world, where a carried family's frames
repeat with the world's period and the owner's clock therefore never counts past `orderOf U`. Over a
general endofunction that argument is unavailable as stated: `lensCode` prices the AMBIENT table,
and it is the LATER frames — `ℓ t` for `t ≥ 1` — that are unconstrained wherever they read off the
image of `U^[t]`, so the frames of a carried family need not repeat at all.

They do not have to. The capacity is a supremum over families *achieving a value*, not a statement
about the family one is handed — so it is enough to exhibit, for each uniform family, SOME per-frame
family with the same value. `CbHue_le_CbHe` does that by **replacing the family with a clamped
reindexing of itself**: read frame `t` for `t < n`, and past that read frame
`n + ((t − n) % orderOf (corePerm U))`.

The replacement carries because of where the two regimes meet. Below `n` it is the original family.
At or past `n` every state is already in the recurrent core (`iterate_mem_core` — the space bounds
its own transient), and on the core congruent exponents give literally equal frames
(`carries_coreLens_eq` plus `pow_mod_orderOf`), so the clamped index reads what the true index would
have. Frame zero is untouched, so the carried entropy is untouched. And every frame the replacement
ever reads has index at most `n + orderOf (corePerm U) ≤ n + n !`, so one uniform program prices all
of them through a clock that never counts past that.

The cost is `O (log (n + n !))` — the clock, and nothing else. As with `CbHu_le_CbH` the constant
depends on `n` alone, not on the world, the reading, or the family; and as there, no route makes it
absolute. -/

/-- **The clamped clock**: identity below `n`, and past `n` a reindexing into
`[n, n + orderOf (corePerm U))` by the core permutation's period. -/
private noncomputable def clamp (U : Fin n → Fin n) (t : ℕ) : ℕ :=
  if t < n then t else n + ((t - n) % orderOf (corePerm U))

private theorem clamp_zero (U : Fin n → Fin n) : clamp U 0 = 0 := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · simp [clamp, hn]
  · simp [clamp, hn]

/-- The core permutation's period is at most `n !`. -/
private theorem orderOf_corePerm_le (U : Fin n → Fin n) : orderOf (corePerm U) ≤ n ! := by
  classical
  have : Fintype ↥(core U) := Fintype.ofFinite _
  have h := orderOf_le_card_univ (x := corePerm U)
  rw [Fintype.card_perm] at h
  refine h.trans (Nat.factorial_le ?_)
  have := card_core_le U
  rwa [Nat.card_eq_fintype_card] at this

/-- The clamped clock never counts past `n + n !`. -/
private theorem clamp_le (U : Fin n → Fin n) (t : ℕ) : clamp U t ≤ n + n ! := by
  have hpos : 0 < orderOf (corePerm U) := orderOf_pos _
  have hle := orderOf_corePerm_le U
  by_cases h : t < n
  · simp only [clamp, if_pos h]; omega
  · simp only [clamp, if_neg h]
    have := Nat.mod_lt (t - n) hpos
    omega

/-- **Past the transient, the clamped index reads the same frame.** At or past `n` the exponents
`clamp U t` and `t` are congruent modulo the core permutation's order, so they name the same power
of it — and on the core a carried family's frame is determined by that power
(`carries_coreLens_eq`). -/
private theorem corePerm_pow_clamp (U : Fin n → Fin n) {t : ℕ} (ht : n ≤ t) :
    corePerm U ^ (clamp U t) = corePerm U ^ t := by
  have hlt : ¬ t < n := by omega
  simp only [clamp, if_neg hlt]
  rw [pow_add, pow_mod_orderOf, ← pow_add]
  congr 1
  omega

/-- **Owning beats renting by at most the clock, over an arbitrary endofunction world** — the
general-world form of `CbHu_le_CbH`.

An owner at budget `b` carries no more entropy than a renter at `b + O (log (n + n !))`, with no
horizon anywhere. The renter is handed not the owner's family but its clamped reindexing
(`clamp`), which carries the same entropy (frame zero is shared) and whose every frame is the
owner's program run on a clock bounded by `n + n !` — the space transient plus the core's period.

That the frames of the ORIGINAL family may never repeat off the core is not an obstacle: capacity
asks what value is achievable, and the replacement achieves it. -/
theorem CbHue_le_CbHe (U : Fin n → Fin n) (b : ℕ) :
    CbHue U b ≤ CbHe U (b + (15 + elen dbl) * Nat.size (n + n !) + (3 + (15 + elen dbl))) := by
  refine csSup_le_csSup' (bddAbove_budgetedEntropiesE U _) ?_
  rintro N ⟨k, ℓ, hcar, hbud, rfl⟩
  refine ⟨k, fun t => ℓ (clamp U t), ⟨?_, ?_⟩, ?_, ?_⟩
  · simp only [clamp_zero]; exact hcar.1
  · intro t s
    simp only [clamp_zero]
    by_cases ht : t < n
    · simp only [clamp, if_pos ht]; exact hcar.2 t s
    · push Not at ht
      have hmem : U^[t] s ∈ core U := iterate_mem_core U (by simpa using ht) s
      have key : ℓ (clamp U t) (U^[t] s) = ℓ t (U^[t] s) := by
        have h1 := congrFun (carries_coreLens_eq hcar (clamp U t)) ⟨U^[t] s, hmem⟩
        have h2 := congrFun (carries_coreLens_eq hcar t) ⟨U^[t] s, hmem⟩
        simp only [coreLens, Function.comp_apply] at h1 h2
        rw [h1, h2, corePerm_pow_clamp U ht]
      rw [key]; exact hcar.2 t s
  · intro t
    have hc := uniformBudget_frame_cost hbud (clamp U t)
    have hs : Nat.size (clamp U t) ≤ Nat.size (n + n !) := Nat.size_le_size (clamp_le U t)
    have hmul := Nat.mul_le_mul_left (15 + elen dbl) hs
    exact le_trans hc (by omega)
  · simp only [clamp_zero]

/-! ## The tower: sub-systems of sub-systems ([Persistence] §10.2 + §2)

A sub-system is a world, so it hosts sub-systems of its own. This section builds the tower and
prices it.

The object is the **intertwining square** `Intertwines U F ℓ` — the world's step, read one frame
later, is the model's own law applied to the reading. It is the time-indexed form of the
substitution property (`Autonomous`/`descent_iff`, Hartmanis–Stearns 1966): where `Autonomous` asks
that a *single* decoder's fibres be `U`-invariant, the square asks the same of a moving family,
frame by frame. **Dilation needs no second definition**: a `τ`-dilated square is a square over
`U^[τ]`, and `KE_iterate_le` already prices the dilated world.

Three facts make the tower:

* **Squares compose, and dilations multiply** (`Intertwines.comp`): a `τ₁`-square from the base to
  level 1, stacked with a `τ₂`-square from level 1 to level 2, is a `τ₁ * τ₂`-square from the base
  to level 2. Level 2's clock ticks once per `τ₂` ticks of level 1's, which is why the composite's
  frame `k` reads level-1 frame `τ₂ * k`. This is the renormalization-flavoured part and it is
  purely equational.
* **Budgets add** (`uniformBudget_comp`): one fixed builder runs both levels' programs and composes
  their tabulations, so an owner of both levels owns the composite at `b₁ + b₂` plus the clock
  needed to say `τ₂` — `O (Nat.size τ₂)`, the `bconst` idiom, absolute in everything else.
* **The identity law anchors** (`Intertwines.anchored`): a square whose law is `id` is exactly a
  carrying family. So a tower that *carries a memory* at the top is a carrying family of the
  iterated base world.

Together these give **no free lunch** (`tower_no_free_lunch`, `tower_no_free_lunch_perm`): the whole
tower's carried entropy is bounded by the *iterated base world's* uniform capacity at the *summed*
budget. Since `U ^ (τ₁ * τ₂)` is a permutation in its own right when `U` is, `CbHu_collapse` applies
to it verbatim: generically there is no affordable reading of the iterated world either. **Stacking
buys structure, never generic capacity** — a tower is priced by its total budget against the
iterated world's generic ceiling, and no amount of hierarchy evades the count. -/

/-- **The intertwining square** ([Persistence] §10.2, the time-indexed substitution property): one
step of the world, read one frame later, is one step of the model's own law `F` applied to the
reading. `Autonomous` is the static form (`descent_iff`); this is the moving family's form.

A **`τ`-dilated** square needs no separate definition — it is `Intertwines (U^[τ]) F ℓ`, a square
over the iterated world, whose rule `KE_iterate_le` prices at `K (U) + O (log τ)`. -/
def Intertwines (U : X → X) (F : M → M) (ℓ : ℕ → X → M) : Prop :=
  ∀ t s, ℓ (t + 1) (U s) = F (ℓ t s)

/-- A square over `U^[1]` is a square over `U`: dilation by one is no dilation. -/
theorem intertwines_iterate_one {U : X → X} {F : M → M} {ℓ : ℕ → X → M} :
    Intertwines (U^[1]) F ℓ ↔ Intertwines U F ℓ := by
  rw [Function.iterate_one]

/-- **Telescoping**: `t` steps of the world, read through frame `t`, are `t` steps of the law
applied to frame zero's reading. The square is a *local* statement; this is its global content. -/
theorem Intertwines.iterate {U : X → X} {F : M → M} {ℓ : ℕ → X → M}
    (h : Intertwines U F ℓ) : ∀ t s, ℓ t (U^[t] s) = F^[t] (ℓ 0 s) := by
  intro t
  induction t with
  | zero => intro s; rfl
  | succ t ih =>
      intro s
      rw [Function.iterate_succ_apply', h t (U^[t] s), ih s, Function.iterate_succ_apply']

/-- **Telescoping a dilated square, from an arbitrary starting frame**: `j` blocks of `τ` steps of
the world advance the frame index by `j` and the reading by `j` steps of the law. This is the engine
of the composition lemma — it is what lets level 2 read level 1 at *its* own clock rate. -/
private theorem Intertwines.iterate_shift {U : X → X} {F : M → M} {ℓ : ℕ → X → M} {τ : ℕ}
    (h : Intertwines (U^[τ]) F ℓ) : ∀ j r x, ℓ (r + j) (U^[τ * j] x) = F^[j] (ℓ r x) := by
  intro j
  induction j with
  | zero => intro r x; simp
  | succ j ih =>
      intro r x
      rw [show τ * (j + 1) = τ + τ * j from by ring, Function.iterate_add_apply, ← Nat.add_assoc,
        h (r + j) (U^[τ * j] x), ih r x, Function.iterate_succ_apply']

/-- **The identity law anchors the family**: a square whose model law is `id` reads the same value
through every frame — exactly `Carries`'s persistence identity. Persistence is the `F = id` fibre of
the square, as `decoupling_is_identity_law` is the `F = id` fibre of descent.

The converse is deliberately NOT claimed: an anchored family constrains `ℓ (t + 1)` only on the
*image* `U '' univ`, so off the image the frames are free and no square need hold there. -/
theorem Intertwines.anchored {U : X → X} {ℓ : ℕ → X → M} (h : Intertwines U id ℓ) :
    ∀ t s, ℓ t (U^[t] s) = ℓ 0 s := by
  intro t s
  simpa using h.iterate t s

/-! ### The reversible-host dichotomy ([Guests] §2 Definition 2.2, Remark 2.4(a))

Over a reversible host `(X, e)` — `e : X ≃ X` a bijection — the intertwining square admits no
off-core region at all, so lossiness in the guest law has exactly one escape: the reading must
*move*. A time-independent reading forces the guest law bijective outright
(`Intertwines.fixed_bijective`), while a moving reading realizes every law whatever, uniquely from
its own initial frame (`intertwines_realize`, `Intertwines.closed_form`). A time-indexed factor map
is therefore not a generalization for its own sake: it is what makes a lossy guest of a reversible
host possible at all. -/

/-- **Realization** ([Guests] §2 Definition 2.2, Remark 2.4(a)): over a reversible host, running a
guest law `F` forward and the host's inverse backward in lockstep — `ℓₜ = F^[t] ∘ ℓ₀ ∘ (e.symm)^[t]`
— intertwines `e` with `F`, for ANY law `F` and any initial frame `ℓ₀`. Surjectivity of `ℓ₀` is
deliberately not assumed here — it is not a hypothesis of the square — but it transfers to make the
family a reading in the sense of Definition 2.2, since the family's own frame zero is `ℓ₀` by `rfl`.
-/
theorem intertwines_realize (e : X ≃ X) (F : M → M) (ℓ₀ : X → M) :
    Intertwines (⇑e) F (fun t => F^[t] ∘ ℓ₀ ∘ (⇑e.symm)^[t]) := by
  intro t s
  simp only [Function.comp_apply]
  rw [Function.iterate_succ_apply (⇑e.symm), e.symm_apply_apply, Function.iterate_succ_apply' F]

set_option linter.style.longLine false in
/-- info: 'PersistenceCapacity.intertwines_realize' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms intertwines_realize

/-- **The closed form** ([Guests] §2 Definition 2.2, Remark 2.4(a)), which subsumes uniqueness: over
a reversible host, EVERY intertwining family is the one `intertwines_realize` builds from its own
initial frame. Two families intertwining the same `e` with the same `F` and sharing `ℓ 0` therefore
agree at every frame — there is no second reading with that data. -/
theorem Intertwines.closed_form {e : X ≃ X} {F : M → M} {ℓ : ℕ → X → M}
    (h : Intertwines (⇑e) F ℓ) :
    ∀ t, ℓ t = fun x => F^[t] (ℓ 0 ((⇑e.symm)^[t] x)) := by
  intro t
  induction t with
  | zero => simp
  | succ t ih =>
      funext x
      have hx := h t (e.symm x)
      rw [e.apply_symm_apply] at hx
      rw [hx, congrFun ih (e.symm x), ← Function.iterate_succ_apply' F,
        ← Function.iterate_succ_apply (⇑e.symm)]

set_option linter.style.longLine false in
/-- info: 'PersistenceCapacity.Intertwines.closed_form' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Intertwines.closed_form

/-- **The fixed-lens converse** ([Guests] §2 Definition 2.2, Remark 2.4(a)): a time-independent
reading forces the guest law bijective, so no fixed lens sees a lossy guest of a reversible host —
`intertwines_realize`'s moving lens is not an artifact of the construction but the only way to own a
lossy law at all. The host need only be surjective, not reversible outright: surjectivity of `U` and
of the shared frame `ℓ₀` is all the argument uses. -/
theorem Intertwines.fixed_bijective [Finite M] {U : X → X} {F : M → M} {ℓ₀ : X → M}
    (hU : Function.Surjective U) (hℓ₀ : Function.Surjective ℓ₀)
    (h : Intertwines U F (fun _ => ℓ₀)) :
    Function.Bijective F := by
  have hFsurj : Function.Surjective F := by
    intro m
    obtain ⟨x, hx⟩ := hℓ₀ m
    obtain ⟨s, hs⟩ := hU x
    refine ⟨ℓ₀ s, ?_⟩
    have heq : ℓ₀ (U s) = F (ℓ₀ s) := h 0 s
    rw [hs, hx] at heq
    exact heq.symm
  exact ⟨Finite.injective_iff_surjective.mpr hFsurj, hFsurj⟩

set_option linter.style.longLine false in
/-- info: 'PersistenceCapacity.Intertwines.fixed_bijective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Intertwines.fixed_bijective

/-! ### The lossy ledger ([Guests] §2 Remark 2.4(a); [Guests] §9.2)

The coset argument behind `ledger_graded` only ever reads the world through a reference frame and
its own one-step image; it never uses that the family is itself persistent. So a lossy guest law
`F` running behind a persistent family `ℓ` — `Intertwines (⇑U) F ℓ` — is priced the same way, once
`F ∘ ℓ 0` stands in as the reference frame: `(F ∘ ℓ 0, ℓ 1)` is exactly the pair `ledger_graded`
wants, read off the square at `t = 0`. A second, purely combinatorial fact turns the guest's own
settling depth into a resolution bound on the same currency: an image chain that strictly
decreases for `d` steps starting at `Set.range F` forces `Set.range F` to carry at least `d`
elements, since each step drops the count by at least one and the chain's last term is
non-empty. -/

/-- **The lossy ledger** ([Guests] §2 Remark 2.4(a); [Guests] §9.2, the dynamical reading): a
lossy guest law `F` running behind a persistent family `ℓ` is priced exactly as `ledger_graded`
prices a persistent family's own two frames, with `F ∘ ℓ 0` as the reference frame — the coset term
runs over `F ∘ ℓ 0`'s fibres rather than `ℓ 0`'s.

A reduction, not a new count. Put `g := F ∘ ℓ 0` and `ℓ' t := g ∘ (⇑U⁻¹)^[t]`: `ℓ'` persists `U`
(unwinding the host's inverse against its own power recovers `g`), `ℓ' 0 = g` by definition, and
`ℓ' 1 = ℓ 1` by the square read at `t = 0`. `ledger_graded` applied to `ℓ'` then prices `U` from
exactly the pair `(g, ℓ 1)`. -/
theorem ledger_graded_lossy (hn : 0 < n) {U : Perm (Fin n)} {F : Fin m → Fin m}
    {ℓ : ℕ → Fin n → Fin m} (h : Intertwines (⇑U) F ℓ) :
    KE (lensCode U) ≤ KE (lensCode (F ∘ ℓ 0)) + KE (lensCode (ℓ 1))
      + (15 + elen dbl) * Nat.size (∏ i : Fin m, (Nat.card {x : Fin n // (F ∘ ℓ 0) x = i})!)
      + (15 + elen dbl) * Nat.size n
      + (elen gradedBuilder + 2 * (15 + elen dbl) + 39) := by
  set g : Fin n → Fin m := F ∘ ℓ 0 with hgdef
  set ℓ' : ℕ → Fin n → Fin m := fun t => g ∘ (⇑U⁻¹)^[t] with hℓ'def
  have hpers : PermPersists U ℓ' := by
    intro t x
    have hinv : (⇑U⁻¹)^[t] ((U ^ t) x) = x := by
      rw [← Equiv.Perm.coe_pow, inv_pow]
      exact (U ^ t).symm_apply_apply x
    simp only [hℓ'def, Function.comp_apply, hinv, Function.iterate_zero_apply]
  have h0 : ℓ' 0 = g := by simp [hℓ'def]
  have h1 : ℓ' 1 = ℓ 1 := by
    funext x
    have hux : (U : Fin n → Fin n) (U⁻¹ x) = x := U.apply_symm_apply x
    have hstep := h 0 (U⁻¹ x)
    rw [hux] at hstep
    simp only [hℓ'def, Function.comp_apply, Function.iterate_one, hgdef]
    exact hstep.symm
  have hbound := ledger_graded hn hpers
  rwa [h0, h1] at hbound

set_option linter.style.longLine false in
/-- info: 'PersistenceCapacity.ledger_graded_lossy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ledger_graded_lossy

/-- **The lossy ledger, at the paired frame** ([Guests] §4, Law 1's sketch; [Persistence] §6,
Remark 6.6): the guest's first two frames extend to a persistent family whose reference lens is
`F ∘ ℓ 0` and whose second frame is `ℓ 1`, and the paired ledger prices the host from those two
frames read as ONE paired table — `KE (lensCode (pairLens (F ∘ ℓ 0) (ℓ 1)))` rather than the two
separate frame prices `ledger_graded_lossy` charges. The same reduction `ledger_graded_lossy`
performs, landing on `ledger_graded_paired_persists` instead of `ledger_graded`: put
`g := F ∘ ℓ 0` and `ℓ' t := g ∘ (⇑U⁻¹)^[t]`, whose persistence identity and first two frames are
exactly `ledger_graded_lossy`'s own. -/
theorem ledger_graded_paired_lossy (hn : 0 < n) {U : Perm (Fin n)} {F : Fin m → Fin m}
    {ℓ : ℕ → Fin n → Fin m} (h : Intertwines (⇑U) F ℓ) :
    KE (lensCode U) ≤ KE (lensCode (pairLens (F ∘ ℓ 0) (ℓ 1)))
      + (15 + elen dbl) * Nat.size (∏ i : Fin m, (Nat.card {x : Fin n // (F ∘ ℓ 0) x = i})!)
      + (15 + elen dbl) * Nat.size n
      + pairedLedgerConst := by
  set g : Fin n → Fin m := F ∘ ℓ 0 with hgdef
  set ℓ' : ℕ → Fin n → Fin m := fun t => g ∘ (⇑U⁻¹)^[t] with hℓ'def
  have hpers : PermPersists U ℓ' := by
    intro t x
    have hinv : (⇑U⁻¹)^[t] ((U ^ t) x) = x := by
      rw [← Equiv.Perm.coe_pow, inv_pow]
      exact (U ^ t).symm_apply_apply x
    simp only [hℓ'def, Function.comp_apply, hinv, Function.iterate_zero_apply]
  have h0 : ℓ' 0 = g := by simp [hℓ'def]
  have h1 : ℓ' 1 = ℓ 1 := by
    funext x
    have hux : (U : Fin n → Fin n) (U⁻¹ x) = x := U.apply_symm_apply x
    have hstep := h 0 (U⁻¹ x)
    rw [hux] at hstep
    simp only [hℓ'def, Function.comp_apply, Function.iterate_one, hgdef]
    exact hstep.symm
  have hbound := ledger_graded_paired_persists hn hpers
  rwa [h0, h1] at hbound

set_option linter.style.longLine false in
/-- info: 'PersistenceCapacity.ledger_graded_paired_lossy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ledger_graded_paired_lossy

/-- **A strictly decreasing chain of naturals, counted**: `d` consecutive strict drops starting at
`c 0` force `c 0` to exceed `c d` by at least `d`. Pure arithmetic, no sets involved — the set-level
fact below is this applied to the cardinalities of an image chain. -/
private theorem chain_card_add_le {c : ℕ → ℕ} {d : ℕ} (h : ∀ j < d, c (j + 1) < c j) :
    c d + d ≤ c 0 := by
  induction d with
  | zero => simp
  | succ d ih =>
    have h1 : c (d + 1) < c d := h d (Nat.lt_succ_self d)
    have h2 : c d + d ≤ c 0 := ih (fun j hj => h j (hj.trans (Nat.lt_succ_self d)))
    omega

/-- **The image-chain bound** ([Guests] §9.2): if a law's iterated images strictly decrease for `d`
steps starting at its own image — `Set.range F ⊃ Set.range (F^[2]) ⊃ ⋯ ⊃ Set.range (F^[d])`, each
inclusion strict, with the chain's last term `Set.range (F^[d])` non-empty — then
`d ≤ Nat.card (Set.range F)`. Elementary: each strict step drops the image's cardinality by at
least one, and the last image contributes at least the one further element non-emptiness
guarantees. This is what turns a lossy guest's settling depth into a resolution bound on the same
frame `ledger_graded_lossy` prices ([Guests] §9.2). -/
theorem settlingDepth_le_card_range {F : Fin m → Fin m} {d : ℕ}
    (hchain : ∀ j, j + 1 < d → Set.range (F^[j + 2]) ⊂ Set.range (F^[j + 1]))
    (hlast : (Set.range (F^[d])).Nonempty) :
    d ≤ Nat.card (Set.range F) := by
  rcases d with _ | e
  · exact Nat.zero_le _
  · have hc : ∀ j < e, Nat.card (Set.range (F^[j + 2])) < Nat.card (Set.range (F^[j + 1])) :=
      fun j hj => Set.ncard_lt_ncard (hchain j (by omega)) (Set.toFinite _)
    have hbound := chain_card_add_le (c := fun j => Nat.card (Set.range (F^[j + 1]))) hc
    simp only [Nat.zero_add, Function.iterate_one] at hbound
    have hpos : 0 < Nat.card (Set.range (F^[e + 1])) := by
      have : Nonempty (Set.range (F^[e + 1])) := hlast.to_subtype
      exact Nat.card_pos
    omega

set_option linter.style.longLine false in
/-- info: 'PersistenceCapacity.settlingDepth_le_card_range' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms settlingDepth_le_card_range

/-- **The resolution clause, at the parity guest's own witness** ([Guests] §9.2): the parity-then-
die guest's law `fun _ => 0` has a SINGLETON range, so `settlingDepth_le_card_range`'s resolution
bound pins any settling depth this law admits to at most one step — depth one at resolution one
prices nothing. This is the guard `intertwines_parityLens`/`parityLens_intertwines_not_carries`
were missing: neither states what the depth floor forces at the family's own law. -/
theorem settlingDepth_parityLens_le_one {d : ℕ}
    (hchain : ∀ j, j + 1 < d →
      Set.range ((fun _ : Fin 2 => (0 : Fin 2))^[j + 2])
        ⊂ Set.range ((fun _ : Fin 2 => (0 : Fin 2))^[j + 1]))
    (hlast : (Set.range ((fun _ : Fin 2 => (0 : Fin 2))^[d])).Nonempty) :
    d ≤ 1 := by
  have hcard : Nat.card (Set.range (fun _ : Fin 2 => (0 : Fin 2))) = 1 := by
    have hone : (Set.range (fun _ : Fin 2 => (0 : Fin 2)) : Set (Fin 2)) = {0} := by
      ext y
      simp only [Set.mem_range, Set.mem_singleton_iff]
      exact ⟨fun ⟨_, h⟩ => h.symm, fun h => ⟨0, h.symm⟩⟩
    rw [hone, Nat.card_coe_set_eq, Set.ncard_singleton]
  have hbound := settlingDepth_le_card_range hchain hlast
  rwa [hcard] at hbound

set_option linter.style.longLine false in
/-- info: 'PersistenceCapacity.settlingDepth_parityLens_le_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms settlingDepth_parityLens_le_one

/-! ### The law-blind count and its ledger ([Guests] §9.2)

Persistence prices the world against ONE named law. The count behind it is coarser: among every
permutation SOME law could explain — quantifying the law away entirely — how many are there?
`card_lawBlind_le` answers this by the coset argument `collapse_count` already runs, read against
the CODOMAIN lens `ℓ'` rather than an affordable-frame set: a law-blind permutation determines its
own law only on the domain lens's actual image, so the count splits into a choice of that partial
map — at most `(card range ℓ') ^ (card range ℓ)` of them — times one `ℓ'`-fibre-stabilizer coset
per choice (`∏ᵢ (fibreᵢ)!`, `card_stabilizer_lens`). -/

/-- **The permutations some law explains** ([Guests] §9.2): the set a fixed pair of lenses
`(ℓ, ℓ')` cannot distinguish from carrying a law of its own — quantifying the law away, unlike
`PermCarries`/`Intertwines`, which each fix one. -/
def LawBlind (ℓ ℓ' : Fin n → Fin m) : Set (Perm (Fin n)) :=
  {V : Perm (Fin n) | ∃ f : Fin m → Fin m, ℓ' ∘ ⇑V = f ∘ ℓ}

/-- **The law-blind count** ([Guests] §9.2): at most `(card range ℓ') ^ (card range ℓ)` guesses at
the induced partial law, each pinning `V` down to one `ℓ'`-fibre-stabilizer coset — one map guess
per point `ℓ` actually reads, times `card_stabilizer_lens`'s own coset size. -/
theorem card_lawBlind_le (ℓ ℓ' : Fin n → Fin m) :
    Nat.card (LawBlind ℓ ℓ') ≤ Nat.card (Set.range ℓ') ^ Nat.card (Set.range ℓ)
      * ∏ i : Fin m, (Nat.card {x : Fin n // ℓ' x = i})! := by
  classical
  set S : Finset (Perm (Fin n)) := Finset.univ.filter (fun V => V ∈ LawBlind ℓ ℓ') with hSdef
  set Φ : Perm (Fin n) → (↥(Set.range ℓ) → ↥(Set.range ℓ')) :=
    fun V y => ⟨ℓ' (V y.2.choose), Set.mem_range_self _⟩ with hΦdef
  set T : Finset (↥(Set.range ℓ) → ↥(Set.range ℓ')) := Finset.univ with hTdef
  have hΦ_eq : ∀ {V : Perm (Fin n)} {f : Fin m → Fin m}, ℓ' ∘ ⇑V = f ∘ ℓ →
      ∀ y : ↥(Set.range ℓ), (Φ V y : Fin m) = f y.1 := by
    intro V f hf y
    have hchoose : ℓ y.2.choose = y.1 := y.2.choose_spec
    have hcongr := congrFun hf y.2.choose
    simp only [Function.comp_apply] at hcongr
    change ℓ' (V y.2.choose) = f y.1
    rw [hcongr, hchoose]
  have hfib : ∀ v ∈ T, (S.filter fun V => Φ V = v).card
      ≤ ∏ i : Fin m, (Nat.card {x : Fin n // ℓ' x = i})! := by
    intro v _
    rcases Finset.eq_empty_or_nonempty (S.filter fun V => Φ V = v) with hemp | ⟨W, hW⟩
    · simp [hemp]
    · have hWmem := Finset.mem_filter.mp hW
      have hWA : W ∈ LawBlind ℓ ℓ' := by
        have h := (Finset.mem_filter.mp hWmem.1).2
        simpa [hSdef] using h
      obtain ⟨fW, hfW⟩ := hWA
      have hWv : Φ W = v := hWmem.2
      have : Fintype ↥(stabilizer (Perm (Fin n)) ℓ') := Fintype.ofFinite _
      have hmaps : ∀ U ∈ S.filter fun V => Φ V = v,
          W * U⁻¹ ∈ (stabilizer (Perm (Fin n)) ℓ' : Set (Perm (Fin n))).toFinset := by
        intro U hU
        have hUmem := Finset.mem_filter.mp hU
        have hUA : U ∈ LawBlind ℓ ℓ' := by
          have h := (Finset.mem_filter.mp hUmem.1).2
          simpa [hSdef] using h
        obtain ⟨fU, hfU⟩ := hUA
        have hUv : Φ U = v := hUmem.2
        have heqfun : ℓ' ∘ ⇑U = ℓ' ∘ ⇑W := by
          funext x
          have hy : Φ U ⟨ℓ x, ⟨x, rfl⟩⟩ = Φ W ⟨ℓ x, ⟨x, rfl⟩⟩ := by rw [hUv, hWv]
          have h1 := hΦ_eq hfU (⟨ℓ x, ⟨x, rfl⟩⟩ : ↥(Set.range ℓ))
          have h2 := hΦ_eq hfW (⟨ℓ x, ⟨x, rfl⟩⟩ : ↥(Set.range ℓ))
          have hzz : fU (ℓ x) = fW (ℓ x) := by
            have hcast := congrArg (fun z : ↥(Set.range ℓ') => (z : Fin m)) hy
            rw [h1, h2] at hcast
            exact hcast
          calc (ℓ' ∘ ⇑U) x = fU (ℓ x) := congrFun hfU x
            _ = fW (ℓ x) := hzz
            _ = (ℓ' ∘ ⇑W) x := (congrFun hfW x).symm
        have hlens : U⁻¹ • ℓ' = W⁻¹ • ℓ' := by
          funext x
          rw [smul_lens_apply, smul_lens_apply, inv_inv, inv_inv]
          exact congrFun heqfun x
        simp only [Set.mem_toFinset, SetLike.mem_coe, mem_stabilizer_iff, mul_smul, hlens,
          smul_inv_smul]
      have hinj : Set.InjOn (fun U => W * U⁻¹) ↑(S.filter fun U => Φ U = v) :=
        fun a _ c _ hac => inv_injective (mul_left_cancel hac)
      have hcard := Finset.card_le_card_of_injOn (fun U => W * U⁻¹) hmaps hinj
      rw [Set.toFinset_card, ← Nat.card_eq_fintype_card] at hcard
      have hstab : Nat.card ↥((stabilizer (Perm (Fin n)) ℓ' : Set (Perm (Fin n))))
          = ∏ i : Fin m, (Nat.card {x : Fin n // ℓ' x = i})! := card_stabilizer_lens ℓ'
      exact hstab ▸ hcard
  have hmapsT : ∀ V ∈ S, Φ V ∈ T := fun V _ => Finset.mem_univ _
  have hmain := Finset.card_le_mul_card_image_of_maps_to hmapsT
    (∏ i : Fin m, (Nat.card {x : Fin n // ℓ' x = i})!) hfib
  have hTcard : T.card = Nat.card (Set.range ℓ') ^ Nat.card (Set.range ℓ) := by
    rw [hTdef, Finset.card_univ, ← Nat.card_eq_fintype_card, Nat.card_fun]
  have hSset : (LawBlind ℓ ℓ' : Set (Perm (Fin n))) = ↑S := by
    ext V; simp [hSdef]
  have hcardeq : Nat.card (LawBlind ℓ ℓ') = S.card := by
    rw [Nat.card_coe_set_eq, hSset, Set.ncard_coe_finset]
  rw [hcardeq]
  calc S.card ≤ (∏ i : Fin m, (Nat.card {x : Fin n // ℓ' x = i})!) * T.card := hmain
    _ = (∏ i : Fin m, (Nat.card {x : Fin n // ℓ' x = i})!)
        * (Nat.card (Set.range ℓ') ^ Nat.card (Set.range ℓ)) := by rw [hTcard]
    _ = Nat.card (Set.range ℓ') ^ Nat.card (Set.range ℓ)
        * ∏ i : Fin m, (Nat.card {x : Fin n // ℓ' x = i})! := by ring

set_option linter.style.longLine false in
/-- info: 'PersistenceCapacity.card_lawBlind_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms card_lawBlind_le

/-! ### The law-blind ledger, over the paired frame ([Guests] §9.2)

`card_lawBlind_le` counts; this enumerates. A fixed decoder recovers `U`'s own table from the
paired frame `pairLens ℓ ℓ'` plus an index into the SAME set the count bounds —
`ledger_graded_paired`'s own plumbing, with the transport check widened from "equals a fixed
reference table" to "equals it after SOME law", `isValid`'s single ∀ becoming a doubly-bounded ∀∀
implication (`lbOK`/`lbBool`, `pairOK`/`candBijBool`'s own shape). No term below ever reads `F`:
the address is `(ℓ, ℓ')` alone, which is what separates this from `ledger_graded_paired_lossy`. -/

/-- **One law-blind pairwise test**, `Bool`-valued: skip the pair when the `ℓ`-table disagrees at
`i` and `j`, else require the `ℓ'`-table to agree at the candidate's own images — `pairOK`'s
shape, reading two tables through the candidate rather than comparing digits directly. -/
private def lbOK (n t0 t1 w i j : ℕ) : Bool :=
  (!decide ((rawTable t0).getD i 0 = (rawTable t0).getD j 0)) ||
    decide ((rawTable t1).getD (digitAt n w i) 0 = (rawTable t1).getD (digitAt n w j) 0)

private theorem primrec_lbOK :
    Primrec₂ fun (a : ℕ × ℕ) (j : ℕ) =>
      lbOK a.1.unpair.1 a.1.unpair.2.unpair.1 a.1.unpair.2.unpair.2.unpair.1
        a.1.unpair.2.unpair.2.unpair.2 a.2 j := by
  have hpow : Primrec₂ ((· ^ ·) : ℕ → ℕ → ℕ) := Primrec₂.unpaired'.1 Nat.Primrec.pow
  have hN : Primrec fun q : (ℕ × ℕ) × ℕ => q.1.1.unpair.1 :=
    Primrec.fst.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.fst))
  have hT0 : Primrec fun q : (ℕ × ℕ) × ℕ => q.1.1.unpair.2.unpair.1 :=
    Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp (Primrec.unpair.comp
      (Primrec.fst.comp Primrec.fst))))
  have hT1 : Primrec fun q : (ℕ × ℕ) × ℕ => q.1.1.unpair.2.unpair.2.unpair.1 :=
    Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp (Primrec.unpair.comp
      (Primrec.snd.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.fst))))))
  have hW : Primrec fun q : (ℕ × ℕ) × ℕ => q.1.1.unpair.2.unpair.2.unpair.2 :=
    Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp (Primrec.unpair.comp
      (Primrec.snd.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.fst))))))
  have hI : Primrec fun q : (ℕ × ℕ) × ℕ => q.1.2 := Primrec.snd.comp Primrec.fst
  have hJ : Primrec fun q : (ℕ × ℕ) × ℕ => q.2 := Primrec.snd
  have hdigI : Primrec fun q : (ℕ × ℕ) × ℕ =>
      digitAt q.1.1.unpair.1 q.1.1.unpair.2.unpair.2.unpair.2 q.1.2 :=
    Primrec.nat_mod.comp (Primrec.nat_div.comp hW (hpow.comp hN hI)) hN
  have hdigJ : Primrec fun q : (ℕ × ℕ) × ℕ =>
      digitAt q.1.1.unpair.1 q.1.1.unpair.2.unpair.2.unpair.2 q.2 :=
    Primrec.nat_mod.comp (Primrec.nat_div.comp hW (hpow.comp hN hJ)) hN
  have hT0i : Primrec fun q : (ℕ × ℕ) × ℕ => (rawTable q.1.1.unpair.2.unpair.1).getD q.1.2 0 :=
    (Primrec.list_getD 0).comp (primrec_rawTable.comp hT0) hI
  have hT0j : Primrec fun q : (ℕ × ℕ) × ℕ => (rawTable q.1.1.unpair.2.unpair.1).getD q.2 0 :=
    (Primrec.list_getD 0).comp (primrec_rawTable.comp hT0) hJ
  have hT1i : Primrec fun q : (ℕ × ℕ) × ℕ =>
      (rawTable q.1.1.unpair.2.unpair.2.unpair.1).getD
        (digitAt q.1.1.unpair.1 q.1.1.unpair.2.unpair.2.unpair.2 q.1.2) 0 :=
    (Primrec.list_getD 0).comp (primrec_rawTable.comp hT1) hdigI
  have hT1j : Primrec fun q : (ℕ × ℕ) × ℕ =>
      (rawTable q.1.1.unpair.2.unpair.2.unpair.1).getD
        (digitAt q.1.1.unpair.1 q.1.1.unpair.2.unpair.2.unpair.2 q.2) 0 :=
    (Primrec.list_getD 0).comp (primrec_rawTable.comp hT1) hdigJ
  have h1 : Primrec fun q : (ℕ × ℕ) × ℕ =>
      decide ((rawTable q.1.1.unpair.2.unpair.1).getD q.1.2 0
        = (rawTable q.1.1.unpair.2.unpair.1).getD q.2 0) :=
    Primrec.eq.decide.comp hT0i hT0j
  have h2 : Primrec fun q : (ℕ × ℕ) × ℕ =>
      decide ((rawTable q.1.1.unpair.2.unpair.2.unpair.1).getD
          (digitAt q.1.1.unpair.1 q.1.1.unpair.2.unpair.2.unpair.2 q.1.2) 0
        = (rawTable q.1.1.unpair.2.unpair.2.unpair.1).getD
          (digitAt q.1.1.unpair.1 q.1.1.unpair.2.unpair.2.unpair.2 q.2) 0) :=
    Primrec.eq.decide.comp hT1i hT1j
  exact ((Primrec.dom_bool₂ (fun (b1 b2 : Bool) => (!b1) || b2)).comp h1 h2).of_eq
    fun q => by simp [lbOK]

private theorem lbOK_iff (n t0 t1 w i j : ℕ) :
    lbOK n t0 t1 w i j = true ↔
      (rawTable t0).getD i 0 = (rawTable t0).getD j 0 →
        (rawTable t1).getD (digitAt n w i) 0 = (rawTable t1).getD (digitAt n w j) 0 := by
  simp only [lbOK, Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq]
  constructor
  · intro h hcond
    rcases h with hne | heq
    · exact absurd hcond hne
    · exact heq
  · intro h
    by_cases hcond : (rawTable t0).getD i 0 = (rawTable t0).getD j 0
    · right; exact h hcond
    · left; exact hcond

/-- **The doubly-bounded law-blind search** ([Guests] §9.2): every pair of positions in `[0, n)`
respects `lbOK` — `candBijBool`'s own outer shape, folded over `lbOK` instead of `pairOK`. -/
private def lbBool (n t0 t1 w : ℕ) : Bool :=
  (List.range n).all fun i => (List.range n).all fun j => lbOK n t0 t1 w i j

set_option maxHeartbeats 1000000 in
-- multi-level packing meets the double fold, same reason as primrec_candBijBool.
private theorem primrec_lbBool :
    Primrec fun p : ℕ => lbBool p.unpair.1 p.unpair.2.unpair.1 p.unpair.2.unpair.2.unpair.1
      p.unpair.2.unpair.2.unpair.2 := by
  have hN : Primrec fun p : ℕ => p.unpair.1 := Primrec.fst.comp Primrec.unpair
  have hInner : Primrec₂ fun (packed4 i : ℕ) =>
      (List.range packed4.unpair.1).all
        (fun j => lbOK packed4.unpair.1 packed4.unpair.2.unpair.1
          packed4.unpair.2.unpair.2.unpair.1 packed4.unpair.2.unpair.2.unpair.2 i j) :=
    primrec_list_all (Primrec.list_range.comp (Primrec.fst.comp (Primrec.unpair.comp Primrec.fst)))
      primrec_lbOK
  have hOuter : Primrec fun packed4 : ℕ =>
      (List.range packed4.unpair.1).all (fun i =>
        (List.range packed4.unpair.1).all
          (fun j => lbOK packed4.unpair.1 packed4.unpair.2.unpair.1
            packed4.unpair.2.unpair.2.unpair.1 packed4.unpair.2.unpair.2.unpair.2 i j)) :=
    primrec_list_all (Primrec.list_range.comp (Primrec.fst.comp Primrec.unpair)) hInner
  exact hOuter.of_eq fun packed4 => rfl

private theorem lbBool_iff (n t0 t1 w : ℕ) :
    lbBool n t0 t1 w = true ↔
      ∀ i < n, ∀ j < n, (rawTable t0).getD i 0 = (rawTable t0).getD j 0 →
        (rawTable t1).getD (digitAt n w i) 0 = (rawTable t1).getD (digitAt n w j) 0 := by
  simp only [lbBool, List.all_eq_true, List.mem_range]
  constructor
  · intro h i hi j hj; exact (lbOK_iff n t0 t1 w i j).mp (h i hi j hj)
  · intro h i hi j hj; exact (lbOK_iff n t0 t1 w i j).mpr (h i hi j hj)

/-- **A candidate is law-blind valid** when its table is a genuine permutation AND its `ℓ'`-image
respects `ℓ`'s fibres — `isValid`'s shape, with the fixed reference table's equality widened to
`lbBool`'s existential-law agreement. -/
private def isValidLB (n t0 t1 w : ℕ) : Prop :=
  candBijBool n w = true ∧ lbBool n t0 t1 w = true

private instance decIsValidLB (n t0 t1 w : ℕ) : Decidable (isValidLB n t0 t1 w) := by
  unfold isValidLB; infer_instance

private theorem primrec_isValidLB :
    PrimrecPred fun p : ℕ => isValidLB p.unpair.1 p.unpair.2.unpair.1
      p.unpair.2.unpair.2.unpair.1 p.unpair.2.unpair.2.unpair.2 := by
  have hN : Primrec fun p : ℕ => p.unpair.1 := Primrec.fst.comp Primrec.unpair
  have hW : Primrec fun p : ℕ => p.unpair.2.unpair.2.unpair.2 :=
    Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp (Primrec.unpair.comp
      (Primrec.snd.comp Primrec.unpair))))
  have hBij : PrimrecPred fun p : ℕ => candBijBool p.unpair.1 p.unpair.2.unpair.2.unpair.2 = true :=
    Primrec.eq.comp (primrec_candBijBool.comp hN hW) (Primrec.const true)
  have hLB : PrimrecPred fun p : ℕ => lbBool p.unpair.1 p.unpair.2.unpair.1
      p.unpair.2.unpair.2.unpair.1 p.unpair.2.unpair.2.unpair.2 = true :=
    Primrec.eq.comp primrec_lbBool (Primrec.const true)
  exact hBij.and hLB

set_option maxHeartbeats 1000000 in
-- multi-level packing meets primrec_isValidLB, same reason as primrec_isValid_rel.
private theorem primrec_isValidLB_rel :
    PrimrecRel fun (w param : ℕ) =>
      isValidLB param.unpair.1 param.unpair.2.unpair.1 param.unpair.2.unpair.2 w := by
  have hn' : Primrec fun q : ℕ × ℕ => q.2.unpair.1 :=
    Primrec.fst.comp (Primrec.unpair.comp Primrec.snd)
  have ht0' : Primrec fun q : ℕ × ℕ => q.2.unpair.2.unpair.1 :=
    Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp (Primrec.unpair.comp Primrec.snd)))
  have ht1' : Primrec fun q : ℕ × ℕ => q.2.unpair.2.unpair.2 :=
    Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp (Primrec.unpair.comp Primrec.snd)))
  have hw' : Primrec fun q : ℕ × ℕ => q.1 := Primrec.fst
  have hinner1 : Primrec fun q : ℕ × ℕ => Nat.pair (q.2.unpair.2.unpair.2) (q.1) :=
    Primrec₂.natPair.comp ht1' hw'
  have hinner2 : Primrec fun q : ℕ × ℕ =>
      Nat.pair (q.2.unpair.2.unpair.1) (Nat.pair (q.2.unpair.2.unpair.2) (q.1)) :=
    Primrec₂.natPair.comp ht0' hinner1
  have hfull : Primrec fun q : ℕ × ℕ =>
      Nat.pair (q.2.unpair.1) (Nat.pair (q.2.unpair.2.unpair.1)
        (Nat.pair (q.2.unpair.2.unpair.2) (q.1))) :=
    Primrec₂.natPair.comp hn' hinner2
  have hkey := primrec_isValidLB.comp hfull
  refine hkey.of_eq fun q => ?_
  simp only [Nat.unpair_pair]

/-- **The law-blind candidate list**: every numeral below `n ^ n` whose table is law-blind valid,
in the numeral's own order — `candList`'s own shape, at the law-blind predicate. -/
private def candListLB (n t0 t1 : ℕ) : List ℕ :=
  (List.range (n ^ n)).filter (fun w => decide (isValidLB n t0 t1 w))

private theorem primrec_candListLB :
    Primrec fun p : ℕ => candListLB p.unpair.1 p.unpair.2.unpair.1 p.unpair.2.unpair.2 := by
  have hpow : Primrec₂ ((· ^ ·) : ℕ → ℕ → ℕ) := Primrec₂.unpaired'.1 Nat.Primrec.pow
  have hN : Primrec fun p : ℕ => p.unpair.1 := Primrec.fst.comp Primrec.unpair
  have hL : Primrec fun p : ℕ => List.range (p.unpair.1 ^ p.unpair.1) :=
    Primrec.list_range.comp (hpow.comp hN hN)
  have hfilt := (PrimrecRel.listFilter primrec_isValidLB_rel).comp hL Primrec.id
  exact hfilt.of_eq fun p => rfl

/-- **The law-blind tabulation, rebuilt from the packed program** `⟨n, t0, t1, idx⟩` —
`gradedTableFn`'s own shape, filtering `candListLB` instead of `candList`. -/
private def gradedTableFnLB (a : ℕ) : ℕ :=
  Encodable.encode (candTable a.unpair.1
    (List.getD (candListLB a.unpair.1 a.unpair.2.unpair.1 a.unpair.2.unpair.2.unpair.1)
      a.unpair.2.unpair.2.unpair.2 0))

set_option maxHeartbeats 1000000 in
-- same headroom reason as primrec_gradedTableFn: multi-level packing meets primrec_candListLB.
private theorem primrec_gradedTableFnLB : Primrec gradedTableFnLB := by
  have hN : Primrec fun a : ℕ => a.unpair.1 := Primrec.fst.comp Primrec.unpair
  have hT0 : Primrec fun a : ℕ => a.unpair.2.unpair.1 :=
    Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))
  have hT1 : Primrec fun a : ℕ => a.unpair.2.unpair.2.unpair.1 :=
    Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp
      (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))))
  have hIdx : Primrec fun a : ℕ => a.unpair.2.unpair.2.unpair.2 :=
    Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp
      (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))))
  have hParam : Primrec fun a : ℕ =>
      Nat.pair a.unpair.1 (Nat.pair a.unpair.2.unpair.1 a.unpair.2.unpair.2.unpair.1) :=
    Primrec₂.natPair.comp hN (Primrec₂.natPair.comp hT0 hT1)
  have hCL : Primrec fun a : ℕ =>
      candListLB a.unpair.1 a.unpair.2.unpair.1 a.unpair.2.unpair.2.unpair.1 := by
    have := primrec_candListLB.comp hParam
    refine this.of_eq fun a => ?_
    simp only [Nat.unpair_pair]
  have hSel : Primrec fun a : ℕ =>
      List.getD (candListLB a.unpair.1 a.unpair.2.unpair.1 a.unpair.2.unpair.2.unpair.1)
        a.unpair.2.unpair.2.unpair.2 0 :=
    (Primrec.list_getD 0).comp hCL hIdx
  exact Primrec.encode.comp (primrec_candTable.comp hN hSel)

private theorem partrec_gradedTableFnLB : Nat.Partrec (fun a : ℕ => (gradedTableFnLB a : ℕ)) :=
  _root_.Partrec.nat_iff.mp (Primrec.to_comp primrec_gradedTableFnLB).partrec

/-- **The fixed law-blind ledger builder code.** One program, independent of `n`, the lenses, and
the law. -/
private noncomputable def gradedBuilderLB : Nat.Partrec.Code :=
  Classical.choose (Nat.Partrec.Code.exists_code.mp partrec_gradedTableFnLB)

/-- **The world's own table is a law-blind valid candidate**: bijective (`U` is a permutation) and
its `ℓ'`-image factors through `ℓ` via `F` — read through the encode/decode round trip and the
base-`n` packing. No term below reads `F` itself; only its EXISTENCE is used. -/
private theorem isValidLB_worldNumeral (hn : 0 < n) {U : Perm (Fin n)} {ℓ ℓ' : Fin n → Fin m}
    {F : Fin m → Fin m} (hF : ℓ' ∘ ⇑U = F ∘ ℓ) :
    isValidLB n (lensCode ℓ) (lensCode ℓ') (worldNumeral U) := by
  constructor
  · rw [candBijBool_iff]
    intro i hi j hj hij hcontra
    have hdi : digitAt n (worldNumeral U) i = (U (⟨i, hi⟩ : Fin n) : ℕ) :=
      digitAt_worldNumeral hn U ⟨i, hi⟩
    have hdj : digitAt n (worldNumeral U) j = (U (⟨j, hj⟩ : Fin n) : ℕ) :=
      digitAt_worldNumeral hn U ⟨j, hj⟩
    rw [hdi, hdj] at hcontra
    exact hij (congrArg Fin.val (U.injective (Fin.val_injective hcontra)))
  · rw [lbBool_iff]
    intro i hi j hj hcond
    have hget0 : ∀ k (hk : k < n), (rawTable (lensCode ℓ)).getD k 0
        = (ℓ (⟨k, hk⟩ : Fin n) : ℕ) := fun k hk => by
      rw [rawTable_lensCode, lensTable]
      exact getD_map_finRange (fun y : Fin n => (ℓ y : ℕ)) ⟨k, hk⟩
    have hxy : ℓ (⟨i, hi⟩ : Fin n) = ℓ (⟨j, hj⟩ : Fin n) := by
      apply Fin.val_injective
      rw [← hget0 i hi, ← hget0 j hj]
      exact hcond
    have hUxy : ℓ' (U (⟨i, hi⟩ : Fin n)) = ℓ' (U (⟨j, hj⟩ : Fin n)) := by
      have hi' := congrFun hF (⟨i, hi⟩ : Fin n)
      have hj' := congrFun hF (⟨j, hj⟩ : Fin n)
      simp only [Function.comp_apply] at hi' hj'
      rw [hi', hj', hxy]
    have hget1 : ∀ k (hk : k < n), (rawTable (lensCode ℓ')).getD
        (digitAt n (worldNumeral U) k) 0 = (ℓ' (U (⟨k, hk⟩ : Fin n)) : ℕ) := fun k hk => by
      rw [digitAt_worldNumeral hn U ⟨k, hk⟩, rawTable_lensCode, lensTable]
      exact getD_map_finRange (fun y : Fin n => (ℓ' y : ℕ)) (U ⟨k, hk⟩)
    rw [hget1 i hi, hget1 j hj]
    exact congrArg (fun x : Fin m => (x : ℕ)) hUxy

/-- **A law-blind valid candidate's own permutation agrees, through `ℓ'`, wherever `ℓ` agrees**:
`lbBool`'s content, read at `candPerm`'s own digits via `candPerm_apply`. -/
private theorem candPerm_lb_agree {n w : ℕ} (hn : 0 < n) {ℓ ℓ' : Fin n → Fin m}
    (hb : candBijBool n w = true) (hlb : lbBool n (lensCode ℓ) (lensCode ℓ') w = true)
    {x y : Fin n} (hxy : ℓ x = ℓ y) :
    ℓ' (candPerm n w x) = ℓ' (candPerm n w y) := by
  have hcond : (rawTable (lensCode ℓ)).getD (x : ℕ) 0 = (rawTable (lensCode ℓ)).getD (y : ℕ) 0 := by
    rw [rawTable_lensCode, lensTable, getD_map_finRange, getD_map_finRange]
    exact congrArg (fun z : Fin m => (z : ℕ)) hxy
  have hres := (lbBool_iff n (lensCode ℓ) (lensCode ℓ') w).mp hlb (x : ℕ) x.2 (y : ℕ) y.2 hcond
  have hdigx : digitAt n w (x : ℕ) = (candPerm n w x : ℕ) := (candPerm_apply hn hb x).symm
  have hdigy : digitAt n w (y : ℕ) = (candPerm n w y : ℕ) := (candPerm_apply hn hb y).symm
  rw [hdigx, hdigy] at hres
  have hgx : (rawTable (lensCode ℓ')).getD (candPerm n w x : ℕ) 0 = (ℓ' (candPerm n w x) : ℕ) := by
    rw [rawTable_lensCode, lensTable]; exact getD_map_finRange _ _
  have hgy : (rawTable (lensCode ℓ')).getD (candPerm n w y : ℕ) 0 = (ℓ' (candPerm n w y) : ℕ) := by
    rw [rawTable_lensCode, lensTable]; exact getD_map_finRange _ _
  rw [hgx, hgy] at hres
  exact Fin.val_injective hres

/-- **A law-blind valid candidate's own permutation is law-blind**: it witnesses its own
membership in `LawBlind ℓ ℓ'`, the induced law read off any preimage under `ℓ`
(`candPerm_lb_agree` certifying the choice is immaterial). -/
private theorem isValidLB_mem_lawBlind {n w : ℕ} (hn : 0 < n) {ℓ ℓ' : Fin n → Fin m}
    (hv : isValidLB n (lensCode ℓ) (lensCode ℓ') w) :
    candPerm n w ∈ LawBlind ℓ ℓ' := by
  classical
  refine ⟨fun a => if h : ∃ x : Fin n, ℓ x = a then ℓ' (candPerm n w h.choose) else a, ?_⟩
  funext x
  simp only [Function.comp_apply]
  rw [dif_pos (⟨x, rfl⟩ : ∃ x' : Fin n, ℓ x' = ℓ x)]
  exact candPerm_lb_agree hn hv.1 hv.2
    (Exists.choose_spec (⟨x, rfl⟩ : ∃ x' : Fin n, ℓ x' = ℓ x)).symm

/-- **The law-blind candidate list's length is bounded by the law-blind count**: distinct valid
numerals give distinct permutations (`candTable_injOn`, `candBijBool`'s digits determining the
candidate), each a member of `LawBlind ℓ ℓ'` by `isValidLB_mem_lawBlind` — no coset detour needed,
since the target set IS the set being injected into. `V0 ∈ LawBlind ℓ ℓ'` supplies the junk value
an invalid numeral's branch needs (`LawBlind` is a plain set, not a subgroup, with no free `1`). -/
private theorem candListLB_length_le (hn : 0 < n) {ℓ ℓ' : Fin n → Fin m}
    {V0 : Perm (Fin n)} (hV0 : V0 ∈ LawBlind ℓ ℓ') :
    (candListLB n (lensCode ℓ) (lensCode ℓ')).length ≤ Nat.card (LawBlind ℓ ℓ') := by
  classical
  set t0 := lensCode ℓ with ht0
  set t1 := lensCode ℓ' with ht1
  have : Finite (LawBlind ℓ ℓ') := Set.toFinite _
  have : Fintype ↥(LawBlind ℓ ℓ') := Fintype.ofFinite _
  have hnodup : (candListLB n t0 t1).Nodup := List.nodup_range.filter _
  have hmem : ∀ w ∈ (candListLB n t0 t1).toFinset, w < n ^ n ∧ isValidLB n t0 t1 w := by
    intro w hw
    rw [List.mem_toFinset, candListLB, List.mem_filter, List.mem_range, decide_eq_true_eq] at hw
    exact hw
  have hinj0 : Set.InjOn (candPerm n) {w | w < n ^ n ∧ isValidLB n t0 t1 w} := by
    intro w1 hw1 w2 hw2 heq
    have hb1 : candBijBool n w1 = true := hw1.2.1
    have hb2 : candBijBool n w2 = true := hw2.2.1
    have hdig : ∀ i : Fin n, digitAt n w1 (i : ℕ) = digitAt n w2 (i : ℕ) := by
      intro i
      rw [← candPerm_apply hn hb1 i, ← candPerm_apply hn hb2 i, heq]
    apply candTable_injOn hw1.1 hw2.1
    change (List.range n).map (digitAt n w1) = (List.range n).map (digitAt n w2)
    refine List.map_congr_left fun j hj => ?_
    exact hdig ⟨j, List.mem_range.mp hj⟩
  set f : ℕ → ↥(LawBlind ℓ ℓ') := fun w =>
    if h : isValidLB n t0 t1 w then ⟨candPerm n w, isValidLB_mem_lawBlind hn h⟩ else ⟨V0, hV0⟩
    with hf
  have hcard := Finset.card_le_card_of_injOn f
    (s := (candListLB n t0 t1).toFinset) (t := Finset.univ)
    (fun w _ => Finset.mem_univ (f w))
    (by
      intro w1 hw1 w2 hw2 heq
      rw [Finset.mem_coe] at hw1 hw2
      have h1 := hmem w1 hw1
      have h2 := hmem w2 hw2
      have hfw1 : f w1 = ⟨candPerm n w1, isValidLB_mem_lawBlind hn h1.2⟩ := dif_pos h1.2
      have hfw2 : f w2 = ⟨candPerm n w2, isValidLB_mem_lawBlind hn h2.2⟩ := dif_pos h2.2
      rw [hfw1, hfw2, Subtype.mk_eq_mk] at heq
      exact hinj0 ⟨h1.1, h1.2⟩ ⟨h2.1, h2.2⟩ heq)
  rw [← List.toFinset_card_of_nodup hnodup, Nat.card_eq_fintype_card]
  simpa using hcard

/-- **The paired law-blind tabulation, rebuilt from the packed program** `⟨n, pairCode, idx⟩`:
unzip the paired table back into the two frame tables and hand them to `gradedTableFnLB`'s own
decoder — `pairedGradedTableFn`'s own shape, at the law-blind decoder rather than the persistence
one. -/
private def pairedGradedTableFnLB (a : ℕ) : ℕ :=
  gradedTableFnLB
    (Nat.pair a.unpair.1
      (Nat.pair
        (Encodable.encode
          (unzipFst ((Encodable.decode (α := List ℕ) a.unpair.2.unpair.1).getD [])))
        (Nat.pair
          (Encodable.encode
            (unzipSnd ((Encodable.decode (α := List ℕ) a.unpair.2.unpair.1).getD [])))
          a.unpair.2.unpair.2)))

set_option maxHeartbeats 1000000 in
-- multi-level packing meets primrec_gradedTableFnLB, same headroom as primrec_pairedGradedTableFn.
private theorem primrec_pairedGradedTableFnLB : Primrec pairedGradedTableFnLB := by
  have hN : Primrec fun a : ℕ => a.unpair.1 := Primrec.fst.comp Primrec.unpair
  have hPC : Primrec fun a : ℕ => a.unpair.2.unpair.1 :=
    Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))
  have hIdx : Primrec fun a : ℕ => a.unpair.2.unpair.2 :=
    Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))
  have hDec : Primrec fun a : ℕ => (Encodable.decode (α := List ℕ) a.unpair.2.unpair.1).getD [] :=
    Primrec.option_getD.comp (Primrec.decode.comp hPC) (Primrec.const [])
  have hT0 : Primrec fun a : ℕ => Encodable.encode (unzipFst
      ((Encodable.decode (α := List ℕ) a.unpair.2.unpair.1).getD [])) :=
    Primrec.encode.comp (primrec_unzipFst.comp hDec)
  have hT1 : Primrec fun a : ℕ => Encodable.encode (unzipSnd
      ((Encodable.decode (α := List ℕ) a.unpair.2.unpair.1).getD [])) :=
    Primrec.encode.comp (primrec_unzipSnd.comp hDec)
  have hPacked : Primrec fun a : ℕ =>
      Nat.pair a.unpair.1 (Nat.pair (Encodable.encode (unzipFst
        ((Encodable.decode (α := List ℕ) a.unpair.2.unpair.1).getD [])))
        (Nat.pair (Encodable.encode (unzipSnd
          ((Encodable.decode (α := List ℕ) a.unpair.2.unpair.1).getD [])))
          a.unpair.2.unpair.2)) :=
    Primrec₂.natPair.comp hN (Primrec₂.natPair.comp hT0 (Primrec₂.natPair.comp hT1 hIdx))
  exact primrec_gradedTableFnLB.comp hPacked

/-- **The builder is correct**: unzipping the paired code before running `gradedTableFnLB`'s
decoder is the same as running it on the two separate frame codes. -/
private theorem pairedGradedTableFnLB_eq (n idx : ℕ) {m : ℕ} (ℓ ℓ' : Fin n → Fin m) :
    pairedGradedTableFnLB (Nat.pair n (Nat.pair (lensCode (pairLens ℓ ℓ')) idx))
      = gradedTableFnLB (Nat.pair n (Nat.pair (lensCode ℓ) (Nat.pair (lensCode ℓ') idx))) := by
  have hpc : (Encodable.decode (α := List ℕ) (lensCode (pairLens ℓ ℓ'))).getD []
      = lensTable (pairLens ℓ ℓ') := by rw [lensCode, Encodable.encodek]; rfl
  rw [pairedGradedTableFnLB]
  simp only [Nat.unpair_pair]
  rw [hpc, unzipFst_lensTable_pairLens, unzipSnd_lensTable_pairLens]
  rfl

private theorem partrec_pairedGradedTableFnLB :
    Nat.Partrec (fun a : ℕ => (pairedGradedTableFnLB a : ℕ)) :=
  _root_.Partrec.nat_iff.mp (Primrec.to_comp primrec_pairedGradedTableFnLB).partrec

/-- **The fixed paired law-blind builder code.** One program, independent of `n`, the world, and
the two lenses. -/
noncomputable def pairedGradedBuilderLB : Nat.Partrec.Code :=
  Classical.choose (Nat.Partrec.Code.exists_code.mp partrec_pairedGradedTableFnLB)

private theorem eval_pairedGradedBuilderLB (a : ℕ) :
    Nat.Partrec.Code.eval pairedGradedBuilderLB a = Part.some (pairedGradedTableFnLB a) := by
  have h := congrFun (Classical.choose_spec
    (Nat.Partrec.Code.exists_code.mp partrec_pairedGradedTableFnLB)) a
  simpa [pairedGradedBuilderLB] using h

/-- **The law-blind ledger's constant**: one fixed builder plus the assembly's opcodes — `n`, the
paired frame code, and the coset index, `pairedLedgerConst`'s own shape at the law-blind builder. -/
noncomputable def pairedLedgerConstLB : ℕ := elen pairedGradedBuilderLB + 2 * (15 + elen dbl) + 15

/-- **The law-blind ledger** ([Guests] §9.2): one step of an intertwining square — `ℓ' ∘ U = F ∘ ℓ`
for SOME `F`, which `Intertwines` supplies at every `t` — prices `U` against the paired frame
`pairLens ℓ ℓ'` plus an index into `card_lawBlind_le`'s own count, no term reading `F` at all: the
address is `(ℓ, ℓ')` alone, quantifying the law away exactly as `LawBlind` does. Mirrors
`ledger_graded_paired`'s enumeration plumbing — an index into a computed finite set, the SAME
`Nat.size n` / `Nat.size (…)` split its own bookkeeping produces, read here against
`card_lawBlind_le`'s bound rather than a single fibre-stabilizer count. -/
theorem ledger_lawBlind (hn : 0 < n) {U : Perm (Fin n)} {ℓ ℓ' : Fin n → Fin m} {F : Fin m → Fin m}
    (hF : ℓ' ∘ ⇑U = F ∘ ℓ) :
    KE (lensCode U) ≤ KE (lensCode (pairLens ℓ ℓ'))
      + (15 + elen dbl) * Nat.size (Nat.card (Set.range ℓ') ^ Nat.card (Set.range ℓ)
        * ∏ i : Fin m, (Nat.card {x : Fin n // ℓ' x = i})!)
      + (15 + elen dbl) * Nat.size n
      + pairedLedgerConstLB := by
  set t0 := lensCode ℓ with ht0
  set t1 := lensCode ℓ' with ht1
  set N := Nat.card (Set.range ℓ') ^ Nat.card (Set.range ℓ)
    * ∏ i : Fin m, (Nat.card {x : Fin n // ℓ' x = i})! with hNdef
  have hUmem : U ∈ LawBlind ℓ ℓ' := ⟨F, hF⟩
  have hvalid : isValidLB n t0 t1 (worldNumeral U) := isValidLB_worldNumeral hn hF
  have hlt : worldNumeral U < n ^ n := worldNumeral_lt hn U
  have hmem : worldNumeral U ∈ candListLB n t0 t1 := by
    rw [candListLB, List.mem_filter, List.mem_range, decide_eq_true_eq]
    exact ⟨hlt, hvalid⟩
  obtain ⟨idx, hidxlt, hidxeq⟩ := List.getElem_of_mem hmem
  have hlenle : (candListLB n t0 t1).length ≤ N := by
    rw [hNdef]
    calc (candListLB n t0 t1).length ≤ Nat.card (LawBlind ℓ ℓ') :=
          candListLB_length_le hn hUmem
      _ ≤ Nat.card (Set.range ℓ') ^ Nat.card (Set.range ℓ)
          * ∏ i : Fin m, (Nat.card {x : Fin n // ℓ' x = i})! := card_lawBlind_le ℓ ℓ'
  have hidxN : idx < N := lt_of_lt_of_le hidxlt hlenle
  have hgetD : List.getD (candListLB n t0 t1) idx 0 = worldNumeral U := by
    rw [List.getD_eq_getElem _ _ hidxlt]; exact hidxeq
  have heval : gradedTableFnLB (Nat.pair n (Nat.pair t0 (Nat.pair t1 idx))) = lensCode U := by
    rw [gradedTableFnLB]
    simp only [Nat.unpair_pair]
    rw [hgetD]
    exact congrArg Encodable.encode (candTable_packMarks hn U)
  have hevalp : pairedGradedTableFnLB (Nat.pair n (Nat.pair (lensCode (pairLens ℓ ℓ')) idx))
      = lensCode U := by
    rw [pairedGradedTableFnLB_eq]
    exact heval
  obtain ⟨cp, hcp, hlcp⟩ := exists_min_E (lensCode (pairLens ℓ ℓ'))
  have hz : eval zero (0 : ℕ) = Part.some 0 := rfl
  have hn' : eval (bconst n) 0 = Part.some n := eval_bconst n 0
  have hp0 : eval (comp cp zero) 0 = Part.some (lensCode (pairLens ℓ ℓ')) :=
    (eval_comp_some hz).trans hcp
  have hb : eval (bconst idx) 0 = Part.some idx := eval_bconst idx 0
  have hpair3 : eval (pair (comp cp zero) (bconst idx)) 0
      = Part.some (Nat.pair (lensCode (pairLens ℓ ℓ')) idx) := by
    change Nat.pair <$> _ <*> _ = _
    rw [hp0, hb]; simp [Seq.seq]
  have hpair1 : eval (pair (bconst n) (pair (comp cp zero) (bconst idx))) 0
      = Part.some (Nat.pair n (Nat.pair (lensCode (pairLens ℓ ℓ')) idx)) := by
    change Nat.pair <$> _ <*> _ = _
    rw [hn', hpair3]; simp [Seq.seq]
  have hcomp : Computes
      (comp pairedGradedBuilderLB (pair (bconst n) (pair (comp cp zero) (bconst idx))))
      (lensCode U) := by
    change eval (comp pairedGradedBuilderLB
      (pair (bconst n) (pair (comp cp zero) (bconst idx)))) 0 = _
    rw [eval_comp_some hpair1, eval_pairedGradedBuilderLB, hevalp]
  have hle := KE_le hcomp
  rw [E_len_comp, E_len_pair, E_len_pair, E_len_comp] at hle
  have hzlen : elen (zero : Code) = 3 := rfl
  have hbc := elen_bconst_le idx
  have hbn := elen_bconst_le n
  have hidxsize : Nat.size idx ≤ Nat.size N := Nat.size_le_size (le_of_lt hidxN)
  have hidxsize' : (15 + elen dbl) * Nat.size idx ≤ (15 + elen dbl) * Nat.size N :=
    Nat.mul_le_mul_left _ hidxsize
  rw [hzlen, hlcp] at hle
  rw [pairedLedgerConstLB]
  omega

set_option linter.style.longLine false in
/-- info: 'PersistenceCapacity.ledger_lawBlind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ledger_lawBlind

/-! ### Off the fibre: the collapse has no analogue past `F = id` ([Guests] §4, the v0.4 correction
to Laws 1 and 2)

`PermCarries` is `PermPersists` plus surjectivity of the reference frame, and `PermPersists` is
exactly `Intertwines U id ℓ` read over `Perm (Fin n)` — the permutation specialization of
`Intertwines.anchored`'s `F = id` fibre. Off that fibre the collapse has no analogue at all: a lossy
law can intertwine a family for *every* host permutation while the family carries none of them
(`parityLens_intertwines_not_carries`), and a family that intertwines the host's own law can be
faithful at every frame while still carrying no permutation but the identity
(`discreteFactor_intertwines_not_carries`). Both are refuting instances behind [Guests] §4's Laws 1
and 2 as restated in v0.4: each law's proof, over an imported ledger, needs the family to persist,
and these show that hypothesis is load-bearing rather than a presentation choice. -/

/-- **The parity guest's reading**: frame zero reads a state's parity into `Fin 2`, every later
frame is the constant `0`. Paired with `parityLens_intertwines_not_carries`. -/
def parityLens (n : ℕ) : ℕ → Fin n → Fin 2
  | 0, x => ⟨(x : ℕ) % 2, Nat.mod_lt _ (by norm_num)⟩
  | _ + 1, _ => 0

/-- The parity guest intertwines the constant law for **every** permutation of `Fin n`: past frame
zero both sides of the square are the constant `0`, and at frame zero they agree because the law
itself is constant. No hypothesis on `U` at all. -/
theorem intertwines_parityLens (n : ℕ) (U : Perm (Fin n)) :
    Intertwines (⇑U) (fun _ : Fin 2 => 0) (parityLens n) := by
  intro t s
  cases t <;> rfl

/-- The parity guest's persistence identity fails at every permutation, once some state is odd: the
identity at `t = 1` reads frame zero as the constant `0` everywhere, which it is not at an odd
state. -/
theorem not_permPersists_parityLens {n : ℕ} (hn : 2 ≤ n) (U : Perm (Fin n)) :
    ¬ PermPersists U (parityLens n) := by
  intro h
  have heq := h 1 (⟨1, hn⟩ : Fin n)
  simp [parityLens] at heq

/-- **Witness 1 — the parity guest** ([Guests] §4): a lossy law intertwines this family for
*every* permutation of `Fin n`, yet the family carries none of them, so `Intertwines` is strictly
more general than `PermCarries` off the `F = id` fibre. `2 ≤ n` is needed so `Fin n` has an odd
state for frame zero to distinguish from the even one. -/
theorem parityLens_intertwines_not_carries {n : ℕ} (hn : 2 ≤ n) (U : Perm (Fin n)) :
    Intertwines (⇑U) (fun _ : Fin 2 => 0) (parityLens n) ∧ ¬ PermCarries U (parityLens n) :=
  ⟨intertwines_parityLens n U, fun hc => not_permPersists_parityLens hn U hc.2⟩

set_option linter.style.longLine false in
/-- info: 'PersistenceCapacity.parityLens_intertwines_not_carries' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms parityLens_intertwines_not_carries

/-- The discrete factor intertwines the host's own law by `rfl`: reading every state as itself, one
step of the world already *is* one step of the law applied to the reading. -/
theorem intertwines_discreteFactor (U : Perm (Fin n)) :
    Intertwines (⇑U) (⇑U) (fun _ : ℕ => (id : Fin n → Fin n)) :=
  fun _ _ => rfl

/-- The discrete factor's persistence identity fails at every permutation but the identity: at
`t = 1` it reads `U x = x` for every state `x`, which is exactly the identity `U` is not. -/
theorem not_permCarries_discreteFactor {U : Perm (Fin n)} (hU : U ≠ 1) :
    ¬ PermCarries U (fun _ : ℕ => (id : Fin n → Fin n)) := by
  rintro ⟨-, hpers⟩
  refine hU (Equiv.ext fun x => ?_)
  have heq := hpers 1 x
  simpa [pow_one] using heq

/-- **Witness 2 — the discrete factor** ([Guests] §4): the identity reading, run behind the host's
own law, is faithful at every frame and intertwines by `rfl` — yet it carries no permutation but the
identity, so faithfulness at every frame is no substitute for `PermCarries`'s persistence identity
off the `F = id` fibre. -/
theorem discreteFactor_intertwines_not_carries {U : Perm (Fin n)} (hU : U ≠ 1) :
    Intertwines (⇑U) (⇑U) (fun _ : ℕ => (id : Fin n → Fin n))
      ∧ Function.Bijective (id : Fin n → Fin n)
      ∧ ¬ PermCarries U (fun _ : ℕ => (id : Fin n → Fin n)) :=
  ⟨intertwines_discreteFactor U, Function.bijective_id, not_permCarries_discreteFactor hU⟩

set_option linter.style.longLine false in
/-- info: 'PersistenceCapacity.discreteFactor_intertwines_not_carries' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms discreteFactor_intertwines_not_carries

/-! ### The two-block guest ([Guests] §4, Remark 4.2: every division of the bill is realized)

Neither witness above is the only way to pay Law 1's `cost(S) + K(F)` debt: the **two-block
guest** splits the carrier into invariant blocks of sizes `n₁` and `n₂`, lets the host act as
`U₁ ⊕ U₂`, and gives the guest's law the first block while its reading moves with the second. At
`U₁ = 1` this is the persistent memory of `U₂`; at `U₂ = 1` it is the discrete factor of `U₁`
(Witness 2 above); in between it stays faithful throughout while intertwining, dividing the debt
between `K(F)` and `cost(S)` at every split of the two blocks. -/

/-- **The two-block guest's reading**: undo the second block by `t` steps, leave the first alone.
Paired with `intertwines_twoBlockGuest`, `bijective_twoBlockLens`, `not_permPersists_twoBlockGuest`
and `ne_twoBlockLens`, and bundled in `twoBlockGuest_intertwines_not_carries`. -/
def twoBlockLens (n₁ : ℕ) {n₂ : ℕ} (U₂ : Perm (Fin n₂)) (t : ℕ) :
    Fin (n₁ + n₂) → Fin (n₁ + n₂) :=
  ⇑((unionWorld (1 : Perm (Fin n₁)) U₂)⁻¹ ^ t)

private theorem exists_apply_ne {k : ℕ} {V : Perm (Fin k)} (hV : V ≠ 1) : ∃ x : Fin k, V x ≠ x := by
  by_contra h
  push Not at h
  exact hV (Equiv.ext h)

/-- A permutation's inverse cancels it — stated to keep `⁻¹`'s surface syntax intact for `simp`,
where the library's `Equiv.symm`-phrased form (`Equiv.Perm.inv_def` unfolds `⁻¹` to `.symm`) would
otherwise fight a neighbouring `pow_succ`/`unionWorld_invPow_*` rewrite over the same subterm. -/
private theorem invApplySelf {k : ℕ} (V : Perm (Fin k)) (x : Fin k) : V⁻¹ (V x) = x := by
  rw [Equiv.Perm.inv_def]; exact Equiv.symm_apply_apply V x

/-- **The square commutes blockwise** ([Guests] §4, Remark 4.2): `U = U₁ ⊕ U₂`, the law carries the
first block (`F = U₁ ⊕ id`), and the reading undoes the second (`ℓₜ = (id ⊕ U₂)^{-t}`) —
block-disjoint maps commute, so no hypothesis on `U₁` or `U₂` is needed at all. -/
theorem intertwines_twoBlockGuest {n₁ n₂ : ℕ} (U₁ : Perm (Fin n₁)) (U₂ : Perm (Fin n₂)) :
    Intertwines (⇑(unionWorld U₁ U₂)) (⇑(unionWorld U₁ (1 : Perm (Fin n₂))))
      (twoBlockLens n₁ U₂) := by
  intro t x
  refine Fin.addCases (fun i => ?_) (fun j => ?_) x
  · simp only [twoBlockLens, unionWorld_left, unionWorld_invPow_left]
  · simp only [twoBlockLens, unionWorld_right, unionWorld_invPow_right, Equiv.Perm.one_apply]
    congr 1
    rw [pow_succ, Equiv.Perm.mul_apply, invApplySelf]

/-- **Every frame is a bijection**: each is the coercion of a permutation, so faithfulness is
near-free — the honest content of the square is `intertwines_twoBlockGuest`. -/
theorem bijective_twoBlockLens {n₁ n₂ : ℕ} (U₂ : Perm (Fin n₂)) (t : ℕ) :
    Function.Bijective (twoBlockLens n₁ U₂ t) :=
  ((unionWorld (1 : Perm (Fin n₁)) U₂)⁻¹ ^ t).bijective

/-- **Not `PermPersists` when `U₁ ≠ 1`** ([Guests] §4, Remark 4.2): frame one undoes only the second
block, so any point the first block moves witnesses the persistence identity's failure — hence not
`PermCarries` either (`twoBlockGuest_intertwines_not_carries`). -/
theorem not_permPersists_twoBlockGuest {n₁ n₂ : ℕ} {U₁ : Perm (Fin n₁)} (U₂ : Perm (Fin n₂))
    (hU₁ : U₁ ≠ 1) :
    ¬ PermPersists (unionWorld U₁ U₂) (twoBlockLens n₁ U₂) := by
  intro hpers
  obtain ⟨i, hi⟩ := exists_apply_ne hU₁
  have heq := hpers 1 (Fin.castAdd n₂ i)
  simp only [pow_one, twoBlockLens, unionWorld_left, unionWorld_inv_left,
    unionWorld_invPow_left] at heq
  exact hi (Fin.castAdd_injective n₁ n₂ heq)

/-- **The frames are non-constant when `U₂ ≠ 1`** ([Guests] §4, Remark 4.2): the separation from the
discrete-factor shape, where every frame is the identity. -/
theorem ne_twoBlockLens (n₁ : ℕ) {n₂ : ℕ} {U₂ : Perm (Fin n₂)} (hU₂ : U₂ ≠ 1) :
    twoBlockLens n₁ U₂ 1 ≠ twoBlockLens n₁ U₂ 0 := by
  obtain ⟨k, hk⟩ := exists_apply_ne hU₂
  intro hEq
  have heq := congrFun hEq (Fin.natAdd n₁ (U₂ k))
  simp only [twoBlockLens, pow_one, pow_zero, Equiv.Perm.one_apply, unionWorld_inv_right,
    invApplySelf] at heq
  exact hk (Fin.natAdd_injective n₂ n₁ heq).symm

/-- **Witness 3 — the two-block guest** ([Guests] §4, Remark 4.2): bundles (a)–(d) beside
`discreteFactor_intertwines_not_carries`, whose shape it mirrors. When both blocks act nontrivially
the family intertwines, stays faithful at every frame, carries no permutation (`PermCarries` fails),
and is not frame-constant — the family that realizes every intermediate division of Law 1's debt
between `K(F)` and `cost(S)`, degenerating to the persistent memory at `U₁ = 1` and to Witness 2 at
`U₂ = 1`. -/
theorem twoBlockGuest_intertwines_not_carries {n₁ n₂ : ℕ} (U₁ : Perm (Fin n₁)) (U₂ : Perm (Fin n₂))
    (hU₁ : U₁ ≠ 1) (hU₂ : U₂ ≠ 1) :
    Intertwines (⇑(unionWorld U₁ U₂)) (⇑(unionWorld U₁ (1 : Perm (Fin n₂))))
        (twoBlockLens n₁ U₂)
      ∧ (∀ t, Function.Bijective (twoBlockLens n₁ U₂ t))
      ∧ ¬ PermCarries (unionWorld U₁ U₂) (twoBlockLens n₁ U₂)
      ∧ twoBlockLens n₁ U₂ 1 ≠ twoBlockLens n₁ U₂ 0 :=
  ⟨intertwines_twoBlockGuest U₁ U₂, bijective_twoBlockLens U₂,
    fun hcar => not_permPersists_twoBlockGuest U₂ hU₁ hcar.2, ne_twoBlockLens n₁ hU₂⟩

set_option linter.style.longLine false in
/-- info: 'PersistenceCapacity.twoBlockGuest_intertwines_not_carries' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms twoBlockGuest_intertwines_not_carries

/-! ### The conjugation guest ([Guests] §4, Remark 4.2: the split curve over single-cycle hosts)

A single-cycle host bars the two-block route above — its centralizer is its own powers, so no
non-trivial invariant block exists to split. The **conjugation guest** realizes the same curve by
relabeling instead: conjugate the standard cycle `σ₀` (`finRotate n`) by `h = h₁ ∘ h₂`, split across
disjoint initial segments, and read by `h₁⁻¹` alone. Three pieces make the witness go:

* **The recovery identity** (`orbitEnum_bijective`, `orbitEnum_conj`, `orbitEnum_unique`): a
  conjugator of `σ₀` fixing `0` is determined by the image of one point, so it IS the host's own
  orbit enumeration — total, no search.
* **The pair injection** (`conjugation_pair_injective`): the recovery identity pins the conjugating
  pair `(h₁, h₂)` from the conjugate alone.
* **The guest's clauses** (`conjugationGuest_intertwines_not_carries`): the square commutes by pure
  cancellation, every frame is a bijection, and the family carries nothing. -/

/-! #### The recovery identity -/

/-- **The orbit enumeration**: read the host `U`'s orbit of `0` off `U`'s own powers. Paired with
`orbitEnum_bijective`, `orbitEnum_conj` and `orbitEnum_unique`. -/
def orbitEnum {n : ℕ} [NeZero n] (U : Perm (Fin n)) : Fin n → Fin n := fun j => (U ^ (j : ℕ)) 0

private theorem orbitEnum_noSmallPeriod {n : ℕ} [NeZero n] {U : Perm (Fin n)}
    (hU : ∀ x, ∃ k : ℕ, (U ^ k) 0 = x) {d : ℕ} (hd0 : 0 < d) (hdn : d < n)
    (hUd : (U ^ d) 0 = 0) : False := by
  have hfix : ∀ x : Fin n, (U ^ d) x = x := by
    intro x
    obtain ⟨k, hk⟩ := hU x
    have hcomm : (U ^ d) ((U ^ k) 0) = (U ^ k) ((U ^ d) 0) := by
      rw [← Equiv.Perm.mul_apply, ← Equiv.Perm.mul_apply, ← pow_add, ← pow_add, Nat.add_comm]
    rw [hk, hUd] at hcomm
    exact hcomm.trans hk
  have hone : U ^ d = 1 := Equiv.ext hfix
  have hsurj : Function.Surjective (fun r : Fin d => (U ^ (r : ℕ)) 0) := by
    intro x
    obtain ⟨k, hk⟩ := hU x
    refine ⟨⟨k % d, Nat.mod_lt _ hd0⟩, ?_⟩
    change (U ^ (k % d)) 0 = x
    have hkd : d * (k / d) + k % d = k := Nat.div_add_mod k d
    have hstep : U ^ (d * (k / d) + k % d) = U ^ (k % d) := by
      rw [pow_add, pow_mul, hone, one_pow, one_mul]
    rw [hkd] at hstep
    rw [← hstep, hk]
  have hcard := Fintype.card_le_of_surjective _ hsurj
  simp only [Fintype.card_fin] at hcard
  omega

/-- **Bijective** ([Guests] §4, Remark 4.2): a period shorter than `n` would recur inside `Fin n`
before covering it, contradicting transitivity — the pigeonhole `orbitEnum_noSmallPeriod` runs. -/
theorem orbitEnum_bijective {n : ℕ} [NeZero n] {U : Perm (Fin n)}
    (hU : ∀ x, ∃ k : ℕ, (U ^ k) 0 = x) : Function.Bijective (orbitEnum U) := by
  rw [← Finite.injective_iff_bijective]
  have key : ∀ a b : Fin n, (a : ℕ) < (b : ℕ) → orbitEnum U a ≠ orbitEnum U b := by
    intro a b hlt heq
    have hbn : (b : ℕ) < n := b.isLt
    set d := (b : ℕ) - (a : ℕ) with hd
    have hd0 : 0 < d := by omega
    have hdn : d < n := by omega
    have hUd : (U ^ d) 0 = 0 := by
      have hab : (a : ℕ) + d = (b : ℕ) := by omega
      have hcanc : (U ^ (a : ℕ)) ((U ^ d) 0) = (U ^ (a : ℕ)) 0 := by
        rw [← Equiv.Perm.mul_apply, ← pow_add, hab]
        exact heq.symm
      exact (U ^ (a : ℕ)).injective hcanc
    exact orbitEnum_noSmallPeriod hU hd0 hdn hUd
  intro a b heq
  rcases lt_trichotomy (a : ℕ) (b : ℕ) with h | h | h
  · exact absurd heq (key a b h)
  · exact Fin.ext h
  · exact absurd heq.symm (key b a h)

private theorem orbitEnum_pow_n_zero {n : ℕ} [NeZero n] {U : Perm (Fin n)}
    (hU : ∀ x, ∃ k : ℕ, (U ^ k) 0 = x) : (U ^ n) 0 = 0 := by
  obtain ⟨m, hm⟩ := (orbitEnum_bijective hU).2 ((U ^ n) 0)
  simp only [orbitEnum] at hm
  have hm0 : m = 0 := by
    by_contra hne
    have hmpos : 0 < (m : ℕ) := Nat.pos_of_ne_zero (fun h0 => hne (Fin.ext h0))
    have hmn : (m : ℕ) < n := m.isLt
    set d := n - (m : ℕ) with hd
    have hd0 : 0 < d := by omega
    have hdn : d < n := by omega
    have hmd : (m : ℕ) + d = n := by omega
    have hcanc : (U ^ (m : ℕ)) ((U ^ d) 0) = (U ^ (m : ℕ)) 0 := by
      rw [← Equiv.Perm.mul_apply, ← pow_add, hmd, hm]
    have hUd : (U ^ d) 0 = 0 := (U ^ (m : ℕ)).injective hcanc
    exact orbitEnum_noSmallPeriod hU hd0 hdn hUd
  rw [hm0] at hm
  simpa using hm.symm

private theorem finRotate_val_succ_or_wrap {n : ℕ} [NeZero n] (j : Fin n) :
    ((finRotate n j : ℕ) = (j : ℕ) + 1 ∧ (j : ℕ) + 1 < n) ∨
      ((finRotate n j : ℕ) = 0 ∧ (j : ℕ) + 1 = n) := by
  obtain ⟨n', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne n)
  rcases eq_or_ne j (Fin.last n') with hj | hj
  · right
    subst hj
    refine ⟨by simp, by simp⟩
  · left
    have hlt : (j : ℕ) < n' := Fin.val_lt_last hj
    exact ⟨coe_finRotate_of_ne_last hj, by omega⟩

/-- **The conjugation identity** ([Guests] §4, Remark 4.2): the orbit enumeration conjugates `σ₀`
to `U`. The wrap step at the top index needs `(U ^ n) 0 = 0`, itself forced by bijectivity. -/
theorem orbitEnum_conj {n : ℕ} [NeZero n] {U : Perm (Fin n)}
    (hU : ∀ x, ∃ k : ℕ, (U ^ k) 0 = x) (j : Fin n) :
    orbitEnum U (finRotate n j) = U (orbitEnum U j) := by
  simp only [orbitEnum]
  rcases finRotate_val_succ_or_wrap j with ⟨hval, -⟩ | ⟨hval, hlast⟩
  · rw [hval, _root_.pow_succ', Equiv.Perm.mul_apply]
  · rw [hval, pow_zero, Equiv.Perm.one_apply]
    have hn0 : (U ^ ((j : ℕ) + 1)) 0 = 0 := by rw [hlast]; exact orbitEnum_pow_n_zero hU
    rw [_root_.pow_succ', Equiv.Perm.mul_apply] at hn0
    exact hn0.symm

private theorem orbitEnum_unique_aux {n : ℕ} [NeZero n] {U : Perm (Fin n)}
    (hU : ∀ x, ∃ k : ℕ, (U ^ k) 0 = x) {g : Perm (Fin n)}
    (hg : ∀ x, g (finRotate n x) = U (g x)) (hg0 : g 0 = 0) :
    ∀ v : ℕ, ∀ hv : v < n, g ⟨v, hv⟩ = orbitEnum U ⟨v, hv⟩ := by
  intro v
  induction v with
  | zero =>
    intro hv
    have h0 : (⟨0, hv⟩ : Fin n) = 0 := rfl
    rw [h0, hg0]
    simp [orbitEnum]
  | succ m ih =>
    intro hv
    have hmn : m < n := by omega
    have hp : (finRotate n (⟨m, hmn⟩ : Fin n) : ℕ) = m + 1 := by
      rcases finRotate_val_succ_or_wrap (⟨m, hmn⟩ : Fin n) with ⟨h1, -⟩ | ⟨h1, h2⟩
      · exact h1
      · have h2' : m + 1 = n := h2
        omega
    have hjeq : finRotate n (⟨m, hmn⟩ : Fin n) = (⟨m + 1, hv⟩ : Fin n) := Fin.ext hp
    calc g (⟨m + 1, hv⟩ : Fin n) = g (finRotate n (⟨m, hmn⟩ : Fin n)) := by rw [hjeq]
      _ = U (g ⟨m, hmn⟩) := hg _
      _ = U (orbitEnum U ⟨m, hmn⟩) := by rw [ih hmn]
      _ = orbitEnum U (finRotate n (⟨m, hmn⟩ : Fin n)) := (orbitEnum_conj hU _).symm
      _ = orbitEnum U (⟨m + 1, hv⟩ : Fin n) := by rw [hjeq]

/-- **Uniqueness** ([Guests] §4, Remark 4.2): the unique conjugator of `σ₀` to `U` fixing `0` is the
orbit enumeration — proved by induction along the cycle from `0`, using `orbitEnum_conj` at each
step. -/
theorem orbitEnum_unique {n : ℕ} [NeZero n] {U : Perm (Fin n)}
    (hU : ∀ x, ∃ k : ℕ, (U ^ k) 0 = x) {g : Perm (Fin n)}
    (hg : ∀ x, g (finRotate n x) = U (g x)) (hg0 : g 0 = 0) (j : Fin n) :
    g j = orbitEnum U j := by
  simpa using orbitEnum_unique_aux hU hg hg0 (j : ℕ) j.isLt

/-! #### The pair injection -/

private theorem finRotate_moves {n : ℕ} (hn : 2 ≤ n) : ∀ x : Fin n, finRotate n x ≠ x := by
  have hns : (finRotate n).support = Finset.univ := support_finRotate_of_le hn
  intro x hx
  exact Equiv.Perm.mem_support.mp (hns ▸ Finset.mem_univ x) hx

private theorem finRotate_transitive {n : ℕ} [NeZero n] (hn : 2 ≤ n) :
    ∀ y : Fin n, ∃ k : ℕ, ((finRotate n) ^ k) (0 : Fin n) = y := fun y =>
  (isCycle_finRotate_of_le hn).exists_pow_eq (finRotate_moves hn 0) (finRotate_moves hn y)

/-- **The pair injection** ([Guests] §4, Remark 4.2: the conjugation guest): a conjugating pair
`(h₁, h₂)` split across disjoint initial segments — `h₁` fixing every point outside `{1, …, m}`,
`h₂` every point outside `{m + 1, …, n − 1}`, both fixing `0` — is determined by the conjugate
`(h₁ * h₂) * σ₀ * (h₁ * h₂)⁻¹` alone. The conjugate pins `h₁ * h₂` via `orbitEnum_unique`; the
disjoint-support hypotheses then split the product into its two factors. -/
theorem conjugation_pair_injective {n : ℕ} [NeZero n] (hn : 2 ≤ n) (m : ℕ)
    {h₁ h₂ h₁' h₂' : Perm (Fin n)}
    (hh₁ : ∀ x : Fin n, (x : ℕ) = 0 ∨ m < (x : ℕ) → h₁ x = x)
    (hh₂ : ∀ x : Fin n, (x : ℕ) ≤ m → h₂ x = x)
    (hh₁' : ∀ x : Fin n, (x : ℕ) = 0 ∨ m < (x : ℕ) → h₁' x = x)
    (hh₂' : ∀ x : Fin n, (x : ℕ) ≤ m → h₂' x = x)
    (heq : (h₁ * h₂) * finRotate n * (h₁ * h₂)⁻¹ = (h₁' * h₂') * finRotate n * (h₁' * h₂')⁻¹) :
    h₁ = h₁' ∧ h₂ = h₂' := by
  set U := (h₁ * h₂) * finRotate n * (h₁ * h₂)⁻¹ with hUdef
  have hfix1 : h₁ 0 = 0 := hh₁ 0 (Or.inl (by simp))
  have hfix2 : h₂ 0 = 0 := hh₂ 0 (by simp)
  have hfix1' : h₁' 0 = 0 := hh₁' 0 (Or.inl (by simp))
  have hfix2' : h₂' 0 = 0 := hh₂' 0 (by simp)
  have key : ∀ a b : Perm (Fin n), a 0 = 0 → b 0 = 0 →
      (a * b) * finRotate n * (a * b)⁻¹ = U → ∀ j, (a * b) j = orbitEnum U j := by
    intro a b ha hb hab
    have h0 : (a * b) 0 = 0 := by rw [Equiv.Perm.mul_apply, hb, ha]
    have hmul : (a * b) * finRotate n = U * (a * b) := by
      have h := congrArg (· * (a * b)) hab
      simpa [mul_assoc] using h
    have hg : ∀ x, (a * b) (finRotate n x) = U ((a * b) x) := by
      intro x
      rw [← Equiv.Perm.mul_apply, ← Equiv.Perm.mul_apply, hmul]
    have hcomm : ∀ (j : ℕ) (x : Fin n), (a * b) (((finRotate n) ^ j) x) = (U ^ j) ((a * b) x) := by
      intro j
      induction j with
      | zero => intro x; simp
      | succ j ih =>
        intro x
        have step1 : ((finRotate n) ^ (j + 1)) x = finRotate n (((finRotate n) ^ j) x) := by
          rw [_root_.pow_succ', Equiv.Perm.mul_apply]
        have step2 : (U ^ (j + 1)) ((a * b) x) = U ((U ^ j) ((a * b) x)) := by
          rw [_root_.pow_succ', Equiv.Perm.mul_apply]
        rw [step1, hg, ih, step2]
    have htrans : ∀ y : Fin n, ∃ k : ℕ, (U ^ k) 0 = y := by
      intro y
      obtain ⟨k, hk⟩ := finRotate_transitive hn ((a * b)⁻¹ y)
      refine ⟨k, ?_⟩
      have hc := hcomm k 0
      rw [h0, hk] at hc
      simpa using hc.symm
    exact orbitEnum_unique htrans hg h0
  have e1 := key h₁ h₂ hfix1 hfix2 rfl
  have e2 := key h₁' h₂' hfix1' hfix2' heq.symm
  have hcomb : h₁ * h₂ = h₁' * h₂' := Equiv.ext (fun j => (e1 j).trans (e2 j).symm)
  have hcombx := Equiv.ext_iff.mp hcomb
  have heq1 : h₁ = h₁' := by
    apply Equiv.ext
    intro x
    by_cases hx : (x : ℕ) ≤ m
    · have h2x : h₂ x = x := hh₂ x hx
      have h2'x : h₂' x = x := hh₂' x hx
      have hcx := hcombx x
      simpa [Equiv.Perm.mul_apply, h2x, h2'x] using hcx
    · have hx' : m < (x : ℕ) := by omega
      rw [hh₁ x (Or.inr hx'), hh₁' x (Or.inr hx')]
  have heq2 : h₂ = h₂' := mul_left_cancel (by rw [hcomb, heq1])
  exact ⟨heq1, heq2⟩

/-! #### The conjugation guest's clauses -/

/-- **The conjugation guest's reading**: the constant `h₁⁻¹`, independent of the time index — a
relabeling, not a moving decoder. Paired with `intertwines_conjugationGuest`,
`bijective_conjugationLens` and `not_permCarries_conjugationGuest`, bundled in
`conjugationGuest_intertwines_not_carries`. -/
def conjugationLens {n : ℕ} (h₁ : Perm (Fin n)) : ℕ → Fin n → Fin n := fun _ => ⇑h₁⁻¹

/-- **The square commutes by cancellation** ([Guests] §4, Remark 4.2): with `h = h₁ * h₂`, the
constant reading `h₁⁻¹` intertwines the world `h * σ₀ * h⁻¹` with law `h₂ * σ₀ * h₂⁻¹` — pure group
cancellation, no hypothesis on `h₁` or `h₂` at all. -/
theorem intertwines_conjugationGuest {n : ℕ} (h₁ h₂ : Perm (Fin n)) :
    Intertwines (⇑((h₁ * h₂) * finRotate n * (h₁ * h₂)⁻¹)) (⇑(h₂ * finRotate n * h₂⁻¹))
      (conjugationLens h₁) := by
  intro t x
  change h₁⁻¹ (((h₁ * h₂) * finRotate n * (h₁ * h₂)⁻¹) x) = (h₂ * finRotate n * h₂⁻¹) (h₁⁻¹ x)
  have hcancel :
      h₁⁻¹ * ((h₁ * h₂) * finRotate n * (h₁ * h₂)⁻¹) = (h₂ * finRotate n * h₂⁻¹) * h₁⁻¹ := by
    group
  have hx := Equiv.ext_iff.mp hcancel x
  simp only [Equiv.Perm.mul_apply] at hx
  exact hx

/-- **Every frame is a bijection**: `conjugationLens h₁ t` is `h₁⁻¹`'s coercion, so faithfulness is
free — the honest content of the square is `intertwines_conjugationGuest`. -/
theorem bijective_conjugationLens {n : ℕ} (h₁ : Perm (Fin n)) (t : ℕ) :
    Function.Bijective (conjugationLens h₁ t) := by
  simp only [conjugationLens]
  exact h₁⁻¹.bijective

/-- **Not `PermCarries`** ([Guests] §4, Remark 4.2): over `2 ≤ n`, `σ₀` moves every point, hence so
does its conjugate `U` — at `U 0 ≠ 0` the persistence identity already fails, unconditionally on
`h₁`, `h₂`. -/
theorem not_permCarries_conjugationGuest {n : ℕ} [NeZero n] (hn : 2 ≤ n) (h₁ h₂ : Perm (Fin n)) :
    ¬ PermCarries ((h₁ * h₂) * finRotate n * (h₁ * h₂)⁻¹) (conjugationLens h₁) := by
  set h := h₁ * h₂ with hhdef
  have hmove : finRotate n (h⁻¹ 0) ≠ h⁻¹ 0 := finRotate_moves hn _
  have hU0 : (h * finRotate n * h⁻¹) 0 ≠ 0 := by
    simp only [Equiv.Perm.mul_apply]
    intro hc
    have h2 : h (h⁻¹ (0 : Fin n)) = 0 := by simp
    exact hmove (h.injective (hc.trans h2.symm))
  rintro ⟨-, hpers⟩
  have heq := hpers 1 0
  simp only [pow_one, conjugationLens] at heq
  exact hU0 ((h₁⁻¹).injective heq)

/-- **The discrete-factor degeneracy** ([Guests] §4, Remark 4.2): at `h₁ = 1` the reading collapses
to the identity — combined with `h₁ * h₂ = h₂` there, `intertwines_conjugationGuest` specializes to
exactly `intertwines_discreteFactor`'s shape, world and law both `h₂ * σ₀ * h₂⁻¹`. -/
theorem conjugationLens_one {n : ℕ} :
    conjugationLens (1 : Perm (Fin n)) = fun _ => (id : Fin n → Fin n) := by
  funext t x
  simp [conjugationLens]

/-- **Witness — the conjugation guest** ([Guests] §4, Remark 4.2): over `2 ≤ n`, the family
intertwines its host by pure cancellation, stays faithful at every frame, and carries no
permutation — realizing the split curve over single-cycle hosts by relabeling rather than block
motion, degenerating to the discrete factor at `h₁ = 1` (`conjugationLens_one`). -/
theorem conjugationGuest_intertwines_not_carries {n : ℕ} [NeZero n] (hn : 2 ≤ n)
    (h₁ h₂ : Perm (Fin n)) :
    Intertwines (⇑((h₁ * h₂) * finRotate n * (h₁ * h₂)⁻¹)) (⇑(h₂ * finRotate n * h₂⁻¹))
        (conjugationLens h₁)
      ∧ (∀ t, Function.Bijective (conjugationLens h₁ t))
      ∧ ¬ PermCarries ((h₁ * h₂) * finRotate n * (h₁ * h₂)⁻¹) (conjugationLens h₁) :=
  ⟨intertwines_conjugationGuest h₁ h₂, bijective_conjugationLens h₁,
    not_permCarries_conjugationGuest hn h₁ h₂⟩

set_option linter.style.longLine false in
/-- info: 'PersistenceCapacity.orbitEnum_bijective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms orbitEnum_bijective

set_option linter.style.longLine false in
/-- info: 'PersistenceCapacity.orbitEnum_conj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms orbitEnum_conj

set_option linter.style.longLine false in
/-- info: 'PersistenceCapacity.orbitEnum_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms orbitEnum_unique

set_option linter.style.longLine false in
/-- info: 'PersistenceCapacity.conjugation_pair_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms conjugation_pair_injective

set_option linter.style.longLine false in
/-- info: 'PersistenceCapacity.conjugationGuest_intertwines_not_carries' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms conjugationGuest_intertwines_not_carries

/-- **The composition lemma — the tower's core** ([Persistence] §10.2). Squares compose and
**dilations multiply**: a `τ₁`-square from the base to level 1, stacked with a `τ₂`-square from
level 1 to level 2, is a `τ₁ * τ₂`-square from the base to level 2, read through the composite
family `k ↦ ℓ₂ k ∘ ℓ₁ (τ₂ * k)`.

The frame bookkeeping is the whole content: level 2's clock ticks once per `τ₂` ticks of level 1's,
so the composite's frame `k` must read level 1 at frame `τ₂ * k`. Purely equational — no finiteness,
no budget, no structure on the state spaces. -/
theorem Intertwines.comp {P : Type*} {U : X → X} {F₁ : M → M} {F₂ : P → P}
    {ℓ₁ : ℕ → X → M} {ℓ₂ : ℕ → M → P} {τ₁ τ₂ : ℕ}
    (h₁ : Intertwines (U^[τ₁]) F₁ ℓ₁) (h₂ : Intertwines (F₁^[τ₂]) F₂ ℓ₂) :
    Intertwines (U^[τ₁ * τ₂]) F₂ (fun k => ℓ₂ k ∘ ℓ₁ (τ₂ * k)) := by
  intro k x
  simp only [Function.comp_apply]
  rw [show τ₂ * (k + 1) = τ₂ * k + τ₂ from by ring,
    h₁.iterate_shift τ₂ (τ₂ * k) x]
  exact h₂ k (ℓ₁ (τ₂ * k) x)

/-- Surjectivity composes frame by frame: the tower distinguishes what both levels distinguish. -/
private theorem surjective_tower_frame {P : Type*} {ℓ₁ : ℕ → X → M} {ℓ₂ : ℕ → M → P} {τ₂ : ℕ}
    (h₁ : Function.Surjective (ℓ₁ 0)) (h₂ : Function.Surjective (ℓ₂ 0)) :
    Function.Surjective ((fun k => ℓ₂ k ∘ ℓ₁ (τ₂ * k)) 0) := by
  simpa using h₂.comp h₁

/-- **A tower carrying a memory is a carrying family of the iterated base world.** Compose the two
squares (`Intertwines.comp`), observe the composite law is `id`, and anchor it
(`Intertwines.anchored`). This is what puts the whole tower inside the base world's capacity
accounting. -/
theorem tower_carries {P : Type*} {U : X → X} {F₁ : M → M} {ℓ₁ : ℕ → X → M} {ℓ₂ : ℕ → M → P}
    {τ₁ τ₂ : ℕ} (h₁ : Intertwines (U^[τ₁]) F₁ ℓ₁) (h₂ : Intertwines (F₁^[τ₂]) id ℓ₂)
    (hs₁ : Function.Surjective (ℓ₁ 0)) (hs₂ : Function.Surjective (ℓ₂ 0)) :
    Carries (U^[τ₁ * τ₂]) (fun k => ℓ₂ k ∘ ℓ₁ (τ₂ * k)) :=
  ⟨surjective_tower_frame hs₁ hs₂, (h₁.comp h₂).anchored⟩

/-! ### Budgets add: one builder runs both levels ([Persistence] §10.2 read at §5's budget)

The composite family is `k ↦ ℓ₂ k ∘ ℓ₁ (τ₂ * k)`, so an owner of the tower must, from `k`, produce
the *composed* tabulation. One fixed program does it: rescale the clock (`scaleCode`, the level-1
index `τ₂ * k` with `τ₂` loaded as a binary constant), run each level's own program, and compose the
two tabulations (`compBuilder`). The price is `elen c₁ + elen c₂` plus `O (Nat.size τ₂)` for saying
`τ₂` and an absolute constant for the plumbing — nothing depends on the worlds, the alphabets, or
the families. Budgets ADD; the dilation is paid for in its bit-length, not its magnitude. -/

/-- **The composer does not care that the alphabets agree.** `stepComp` composes tabulated maps by
looking each of the inner table's outputs up in the outer table, and that operation is blind to the
`Fin` bounds — so the same builder that iterates an endofunction composes a level-2 reading with a
level-1 reading across three different alphabets. -/
private theorem stepComp_lensTable_comp {n₁ n₂ n₃ : ℕ} (g : Fin n₂ → Fin n₃) (f : Fin n₁ → Fin n₂) :
    stepComp (lensTable g) (lensTable f) = lensTable (g ∘ f) := by
  simp only [stepComp, lensTable, List.map_map]
  refine List.map_congr_left fun i _ => ?_
  exact getD_map_finRange (fun j : Fin n₂ => ((g j : Fin n₃) : ℕ)) (f i)

/-- The composer as a numeral function: decode two tables, compose them, re-encode. Carries no
dependence on the alphabets — the tables know their own lengths. -/
def compTableFn (p : ℕ) : ℕ :=
  Encodable.encode (stepComp ((Encodable.decode (α := List ℕ) p.unpair.1).getD [])
    ((Encodable.decode (α := List ℕ) p.unpair.2).getD []))

/-- **The composer is primitive recursive**: decoding is `Primrec.decode` and composition is a
`List.map` lookup. -/
private theorem primrec_compTableFn : Primrec compTableFn := by
  have h1 : Primrec fun p : ℕ => (Encodable.decode (α := List ℕ) p.unpair.1).getD [] :=
    Primrec.option_getD.comp
      (Primrec.decode.comp (Primrec.fst.comp Primrec.unpair)) (Primrec.const [])
  have h2 : Primrec fun p : ℕ => (Encodable.decode (α := List ℕ) p.unpair.2).getD [] :=
    Primrec.option_getD.comp
      (Primrec.decode.comp (Primrec.snd.comp Primrec.unpair)) (Primrec.const [])
  exact Primrec.encode.comp (primrec_stepComp.comp h1 h2)

private theorem partrec_compTableFn : Nat.Partrec (fun p : ℕ => (compTableFn p : ℕ)) :=
  _root_.Partrec.nat_iff.mp (Primrec.to_comp primrec_compTableFn).partrec

/-- **The fixed composition builder.** One program, independent of the worlds and the alphabets. -/
noncomputable def compBuilder : Nat.Partrec.Code :=
  Classical.choose (Nat.Partrec.Code.exists_code.mp partrec_compTableFn)

private theorem eval_compBuilder (p : ℕ) :
    Nat.Partrec.Code.eval compBuilder p = Part.some (compTableFn p) := by
  have h := congrFun (Classical.choose_spec
    (Nat.Partrec.Code.exists_code.mp partrec_compTableFn)) p
  simpa [compBuilder] using h

/-- **The composer is correct**: on `⟨outer table, inner table⟩` it outputs the composite's
tabulation. -/
theorem compTableFn_eq {n₁ n₂ n₃ : ℕ} (g : Fin n₂ → Fin n₃) (f : Fin n₁ → Fin n₂) :
    compTableFn (Nat.pair (lensCode g) (lensCode f)) = lensCode (g ∘ f) := by
  rw [compTableFn]
  simp only [Nat.unpair_pair, decode_lensCode]
  rw [stepComp_lensTable_comp]
  rfl

/-- Multiplying the two halves of a pair. -/
private def mulFn (p : ℕ) : ℕ := p.unpair.1 * p.unpair.2

private theorem primrec_mulFn : Primrec mulFn :=
  Primrec.nat_mul.comp (Primrec.fst.comp Primrec.unpair) (Primrec.snd.comp Primrec.unpair)

private theorem partrec_mulFn : Nat.Partrec (fun p : ℕ => (mulFn p : ℕ)) :=
  _root_.Partrec.nat_iff.mp (Primrec.to_comp primrec_mulFn).partrec

/-- The fixed multiplication builder. -/
noncomputable def mulBuilder : Nat.Partrec.Code :=
  Classical.choose (Nat.Partrec.Code.exists_code.mp partrec_mulFn)

private theorem eval_mulBuilder (p : ℕ) :
    Nat.Partrec.Code.eval mulBuilder p = Part.some (mulFn p) := by
  have h := congrFun (Classical.choose_spec
    (Nat.Partrec.Code.exists_code.mp partrec_mulFn)) p
  simpa [mulBuilder] using h

/-- **The clock rescaler** `k ↦ τ * k`: level 2's frame `k` is level 1's frame `τ * k`. The dilation
`τ` rides in as a *binary* constant (`bconst`), so the tower pays for its dilation in bit-length —
`O (Nat.size τ)` — and not in magnitude. -/
private noncomputable def scaleCode (τ : ℕ) : Nat.Partrec.Code :=
  comp mulBuilder (pair (bconst τ) Code.id)

private theorem eval_scaleCode (τ k : ℕ) : (scaleCode τ).eval k = Part.some (τ * k) := by
  have hp : (pair (bconst τ) Code.id).eval k = Part.some (Nat.pair τ k) := by
    change Nat.pair <$> (bconst τ).eval k <*> Code.id.eval k = _
    rw [eval_bconst, eval_id]
    simp [Seq.seq]
  rw [scaleCode, eval_comp_some hp, eval_mulBuilder, mulFn, Nat.unpair_pair]

private theorem elen_scaleCode_le (τ : ℕ) :
    elen (scaleCode τ) ≤ (15 + elen dbl) * Nat.size τ + (elen mulBuilder + (30 + elen dbl)) := by
  have hb := elen_bconst_le τ
  have hid : elen Code.id = 9 := by decide
  rw [scaleCode, E_len_comp, E_len_pair]
  omega

/-- **The tower builder**: one program for the composite family. Rescale the clock, run each level's
program on its own index, compose the tabulations. -/
private noncomputable def towerCode (c₁ c₂ : Nat.Partrec.Code) (τ₂ : ℕ) : Nat.Partrec.Code :=
  comp compBuilder (pair c₂ (comp c₁ (scaleCode τ₂)))

/-- The plumbing constant: the two fixed builders plus the opcodes. Absolute — independent of the
worlds, the alphabets, the families, the dilations, and the budgets. -/
noncomputable def towerConst : ℕ := 39 + elen compBuilder + elen mulBuilder + elen dbl

private theorem eval_towerCode {n₁ n₂ n₃ : ℕ} {ℓ₁ : ℕ → Fin n₁ → Fin n₂} {ℓ₂ : ℕ → Fin n₂ → Fin n₃}
    {c₁ c₂ : Nat.Partrec.Code} (he₁ : ∀ t, c₁.eval t = Part.some (lensCode (ℓ₁ t)))
    (he₂ : ∀ t, c₂.eval t = Part.some (lensCode (ℓ₂ t))) (τ₂ k : ℕ) :
    (towerCode c₁ c₂ τ₂).eval k = Part.some (lensCode (ℓ₂ k ∘ ℓ₁ (τ₂ * k))) := by
  have hinner : (comp c₁ (scaleCode τ₂)).eval k = Part.some (lensCode (ℓ₁ (τ₂ * k))) := by
    rw [eval_comp_some (eval_scaleCode τ₂ k), he₁]
  have hp : (pair c₂ (comp c₁ (scaleCode τ₂))).eval k
      = Part.some (Nat.pair (lensCode (ℓ₂ k)) (lensCode (ℓ₁ (τ₂ * k)))) := by
    change Nat.pair <$> c₂.eval k <*> (comp c₁ (scaleCode τ₂)).eval k = _
    rw [he₂, hinner]
    simp [Seq.seq]
  rw [towerCode, eval_comp_some hp, eval_compBuilder, compTableFn_eq]

private theorem elen_towerCode_le (c₁ c₂ : Nat.Partrec.Code) (τ₂ : ℕ) :
    elen (towerCode c₁ c₂ τ₂)
      ≤ elen c₁ + elen c₂ + (15 + elen dbl) * Nat.size τ₂ + towerConst := by
  have hs := elen_scaleCode_le τ₂
  rw [towerCode, E_len_comp, E_len_pair, E_len_comp, towerConst]
  omega

/-- **Budgets add** ([Persistence] §10.2 read at §5, Definition 5.1's uniform variant): an owner of
both levels owns the tower, at the sum of the two budgets plus the clock needed to say the dilation
and an absolute constant. One fixed builder does the work, so nothing here scales with the worlds,
the alphabets, or the families — and the dilation is charged its bit-length, not its magnitude.

This is what makes the tower a *priced* object rather than a free construction, and it is what
`tower_no_free_lunch` spends. -/
theorem uniformBudget_comp {n₁ n₂ n₃ : ℕ} {ℓ₁ : ℕ → Fin n₁ → Fin n₂} {ℓ₂ : ℕ → Fin n₂ → Fin n₃}
    {τ₂ b₁ b₂ : ℕ} (h₁ : UniformBudget ℓ₁ b₁) (h₂ : UniformBudget ℓ₂ b₂) :
    UniformBudget (fun j => ℓ₂ j ∘ ℓ₁ (τ₂ * j))
      (b₁ + b₂ + (15 + elen dbl) * Nat.size τ₂ + towerConst) := by
  obtain ⟨c₁, hl₁, he₁⟩ := h₁
  obtain ⟨c₂, hl₂, he₂⟩ := h₂
  refine ⟨towerCode c₁ c₂ τ₂, ?_, fun k => eval_towerCode he₁ he₂ τ₂ k⟩
  have := elen_towerCode_le c₁ c₂ τ₂
  omega

/-! ### No free lunch: the collapse is tower-stable ([Persistence] §10.2 + §7)

A tower whose top law is the identity *carries a memory*: whatever level 2 reads survives every step
of the base world, forever. The two theorems below price that memory — and the price is charged
against the **base** world, not the comfortable coarse-grained one the tower's top level inhabits.

The argument is the three facts assembled. The tower is a carrying family of `U^[τ₁ * τ₂]`
(`tower_carries`); it is owned at the summed budget (`uniformBudget_comp`); so its carried entropy
is a member of the iterated world's uniform-capacity set, hence below the supremum. Nothing about
the tower's *height* or its internal structure enters: two levels are priced here, and the same
composition applied repeatedly prices any finite tower, because the composite of two squares is
again a square.

**What this buys, and what it does not.** `CbHu_collapse` is a statement about *every* permutation
world of `Fin n`, and `U ^ (τ₁ * τ₂)` is a permutation of `Fin n` in its own right — so the generic
ceiling applies to the iterated world exactly as it applies to any other: outside a `2 ^ (-d)`
fraction of `Perm (Fin n)`, no reading affordable at the summed budget carries more than
`2 ^ (2 · budget + O(1) + d)`. **Stacking buys structure, never generic capacity.**

What is NOT claimed, and is not proved anywhere here: that a generic `U` has a generic `U ^ k`. The
map `U ↦ U ^ k` does not preserve the counting measure on `Perm (Fin n)` (squaring is not even
injective on it), so transporting genericity from the base to the iterated world is a separate
question — an open obligation, not a corollary. The theorems below are unconditional; the generic
reading of them is conditional on where the iterated world happens to sit. -/

/-- **No free lunch, over a general base world** ([Persistence] §10.2 read at §5's budget). A
two-level tower whose top law is the identity carries no more than the *iterated base world's*
uniform capacity at the *summed* budget. The whole hierarchy is priced against `U^[τ₁ * τ₂]` — the
observer's levels bought structure, and the count does not care.

The dilation enters only as `O (Nat.size τ₂)`: a tower may slow itself down arbitrarily and pay only
the bit-length of its own clock ratio. -/
theorem tower_no_free_lunch {n₁ n₂ n₃ : ℕ} {U : Fin n₁ → Fin n₁} {F₁ : Fin n₂ → Fin n₂}
    {ℓ₁ : ℕ → Fin n₁ → Fin n₂} {ℓ₂ : ℕ → Fin n₂ → Fin n₃} {τ₁ τ₂ b₁ b₂ : ℕ}
    (h₁ : Intertwines (U^[τ₁]) F₁ ℓ₁) (h₂ : Intertwines (F₁^[τ₂]) id ℓ₂)
    (hs₁ : Function.Surjective (ℓ₁ 0)) (hs₂ : Function.Surjective (ℓ₂ 0))
    (hb₁ : UniformBudget ℓ₁ b₁) (hb₂ : UniformBudget ℓ₂ b₂) :
    Nat.card ↥(orbit (Perm ↥(core (U^[τ₁ * τ₂])))
        (coreLens (U^[τ₁ * τ₂]) ((fun j => ℓ₂ j ∘ ℓ₁ (τ₂ * j)) 0)))
      ≤ CbHue (U^[τ₁ * τ₂]) (b₁ + b₂ + (15 + elen dbl) * Nat.size τ₂ + towerConst) :=
  le_csSup (bddAbove_uniformBudgetedEntropiesE _ _)
    ⟨n₃, _, tower_carries h₁ h₂ hs₁ hs₂, uniformBudget_comp hb₁ hb₂, rfl⟩

/-- **No free lunch, over a permutation base**: the same bound against `CbHu (U ^ (τ₁ * τ₂))`, where
the iterated world is spelled as the group power it is. This is the form `CbHu_collapse` consumes —
the iterated world is a permutation of `Fin n₁` like any other, so the generic ceiling covers the
tower without a new argument (see the section note on what genericity transport would additionally
require). -/
theorem tower_no_free_lunch_perm {n₁ n₂ n₃ : ℕ} {U : Perm (Fin n₁)} {F₁ : Fin n₂ → Fin n₂}
    {ℓ₁ : ℕ → Fin n₁ → Fin n₂} {ℓ₂ : ℕ → Fin n₂ → Fin n₃} {τ₁ τ₂ b₁ b₂ : ℕ}
    (h₁ : Intertwines ((⇑U)^[τ₁]) F₁ ℓ₁) (h₂ : Intertwines (F₁^[τ₂]) id ℓ₂)
    (hs₁ : Function.Surjective (ℓ₁ 0)) (hs₂ : Function.Surjective (ℓ₂ 0))
    (hb₁ : UniformBudget ℓ₁ b₁) (hb₂ : UniformBudget ℓ₂ b₂) :
    Nat.card ↥(orbit (Perm (Fin n₁)) ((fun j => ℓ₂ j ∘ ℓ₁ (τ₂ * j)) 0))
      ≤ CbHu (U ^ (τ₁ * τ₂)) (b₁ + b₂ + (15 + elen dbl) * Nat.size τ₂ + towerConst) := by
  refine le_csSup (bddAbove_uniformBudgetedEntropies _ _)
    ⟨n₃, _, ?_, uniformBudget_comp hb₁ hb₂, rfl⟩
  rw [permCarries_iff_carries, Equiv.Perm.coe_pow]
  exact tower_carries h₁ h₂ hs₁ hs₂

/-! ### Coarsening never gains: entropy is antitone up the tower ([Persistence] §2, Definition 2.2)

Each level of a tower reads the level below through a further lens. That reading can only *lose*:
coarsening merges fibres, and merged fibres mean a smaller relabelling class. -/

/-- **Coarsening is equivariant**: composing a further reading on the left commutes with relabelling
the domain on the right — the two operations touch opposite ends of the arrow. -/
private theorem comp_smul_lens {α : Type*} {k : ℕ} (U : Perm α) (ℓ : α → Fin m)
    (g : Fin m → Fin k) : g ∘ (U • ℓ) = U • (g ∘ ℓ) := rfl

/-- The coarsened reading's relabelling class is the *image* of the original's, by equivariance. -/
private theorem orbit_comp_eq_image {α : Type*} {k : ℕ} (ℓ : α → Fin m) (g : Fin m → Fin k) :
    orbit (Perm α) (g ∘ ℓ) = (fun h : α → Fin m => g ∘ h) '' orbit (Perm α) ℓ := by
  ext h
  constructor
  · rintro ⟨U, rfl⟩
    exact ⟨U • ℓ, ⟨U, rfl⟩, comp_smul_lens U ℓ g⟩
  · rintro ⟨h', ⟨U, rfl⟩, rfl⟩
    exact ⟨U, (comp_smul_lens U ℓ g).symm⟩

/-- **Composing a further lens never gains carried entropy** ([Persistence] §2, Definition 2.2).
Coarsening merges fibres, so the coarse reading's relabelling class is a quotient of the fine one's
— a surjection, hence no larger. This is the dual reading of the factorial inequality
`a ! · b ! ≤ (a + b)!`, obtained without the factorials: equivariance alone carries it, because the
image of an orbit under an equivariant map IS the image orbit.

For a tower this says **entropy is antitone up the levels**: no level reads more than the level
below it, so a tower buys its structure out of content it already had. -/
theorem entropy_comp_le {α : Type*} [Finite α] {k : ℕ} (ℓ : α → Fin m) (g : Fin m → Fin k) :
    Nat.card ↥(orbit (Perm α) (g ∘ ℓ)) ≤ Nat.card ↥(orbit (Perm α) ℓ) := by
  rw [orbit_comp_eq_image, Nat.card_coe_set_eq, Nat.card_coe_set_eq]
  exact Set.ncard_image_le (Set.toFinite _)

/-! ## Cartesian product worlds: a habitat beside an environment

The union section put two worlds side by side as a *disjoint union*, where a state belongs to one
block or the other. The other way to compose two worlds is the **Cartesian product**: a state is a
*pair*, and both worlds turn at once, neither reading the other. `prodWorld U₁ U₂` is that world,
`Prod.map` by definition, and `prodWorldFin U₁ U₂` is its `Fin (n₁ * n₂)` instance, transported
along `finProdFinEquiv`. Like a union world, a product world is *structured by construction*, so the
generic statements of the collapse do not speak about it; that is again the point rather than a
caveat.

The reason to want this composite specifically: it is the shape of an observer's world when a
region it can read runs beside a region it cannot. Call the factors a habitat and an environment.
Four things then hold, and together they say that a product world can be cheap to *describe
coarsely* and expensive to *read faithfully* at the same time.

**Rules compose** (`KE_prodWorldFin_le`): `KE (U₁ × U₂) ≤ KE U₁ + KE U₂ + O (1)`, the constant one
fixed builder. As with the union, no size parameter is loaded, and here neither factor's size is
needed: a world's table is as long as its state space, so `prodTableFn` reads `n₂` off the second
table's own length and interleaves. So the cheap-dynamics regime is closed under Cartesian product
too.

**Readings lift through projections** (`carries_prodLensFst`, `intertwines_prodLensFst`). A lens
family on the habitat becomes a lens family on the product by ignoring the second coordinate, and
both of the properties that make it a sub-system survive verbatim: it still carries its model, and
if it satisfied an intertwining square with a law `F`, the lifted family satisfies the same square
with the same `F`. Neither proof does any work — the product's first coordinate evolves by `U₁` and
by nothing else — and that is the content: *what the habitat does is unaffected by what it is
standing next to*. The lift is owned at `O (log n₂)` above the factor's own budget
(`uniformBudget_prodLensFinFst`); the size must be supplied here, exactly as for the union's lens,
because a lens's table has one entry per state and so records the state count but not the label
count.

**A faithful reading hands back BOTH factors' rules** (`KE_factorFst_le_of_faithful`,
`KE_factorSnd_le_of_faithful`). This is the converse direction and the sharp one. An observer that
reads the *whole* product bijectively and owns that reading at budget `b` thereby stores a
description of each factor's rule at `2 · b + O (log n₂) + O (1)` — including the factor it may have
no interest in. The route is the ledger: a faithful owned family hands back the product world's own
table (`faithful_rule_cost`), and a fixed splitter recovers each factor's table from it, the first
by dividing out the second block's size and the second by taking the residue.

The consequence is a contrast rather than a single bound. Read the two directions against each
other: the habitat's coarse law is ownable at `O (K (G) + log κ)` by the lift, while any faithful
reading of the whole world is priced at half of what the *environment's* rule costs to describe. A
world can therefore be one whose sub-system is nearly free to run and whose full state is
unaffordable to read — and the gap is as wide as the environment's rule is incompressible, with no
appeal to the environment's dynamics being complicated in any other sense.

**Capacity projects** (`CbHu_prodWorldFin_ge_fst`): a factor's uniform entropic capacity is a floor
for the product's, at the budget shifted by the lift. The orbit arithmetic needs no multinomial
identity here — the lift is *equivariant* (`liftFst_smul`: relabelling the factor by `U` is
relabelling the product by `U × 1`) and injective, so it embeds the factor's orbit into the
product's, and cardinality follows.

Anchors: [Persistence] §2 + §8. The composition laws are this development's; no numbered result of
[Persistence] is claimed machine-checked by their presence. -/

/-- **The Cartesian product world** `U₁ × U₂`: both factors turn at once, neither reading the
other. Componentwise by definition, so its evaluation and iteration laws are `rfl`. -/
def prodWorld {X₁ X₂ : Type*} (U₁ : X₁ → X₁) (U₂ : X₂ → X₂) : X₁ × X₂ → X₁ × X₂ :=
  Prod.map U₁ U₂

@[simp] private theorem prodWorld_apply {X₁ X₂ : Type*} (U₁ : X₁ → X₁) (U₂ : X₂ → X₂)
    (x : X₁ × X₂) : prodWorld U₁ U₂ x = (U₁ x.1, U₂ x.2) := rfl

/-- **The factors never mix**: `t` steps of the product are `t` steps of each factor. -/
theorem prodWorld_iterate {X₁ X₂ : Type*} (U₁ : X₁ → X₁) (U₂ : X₂ → X₂) (t : ℕ) :
    (prodWorld U₁ U₂)^[t] = prodWorld (U₁^[t]) (U₂^[t]) := Prod.map_iterate U₁ U₂ t

@[simp] private theorem prodWorld_iterate_apply {X₁ X₂ : Type*} (U₁ : X₁ → X₁) (U₂ : X₂ → X₂)
    (t : ℕ) (x : X₁ × X₂) : (prodWorld U₁ U₂)^[t] x = (U₁^[t] x.1, U₂^[t] x.2) := by
  rw [prodWorld_iterate]; rfl

/-- The product of two **permutations** is a permutation of the product, acting as `prodWorld`. -/
private def prodPerm {X₁ X₂ : Type*} (U₁ : Perm X₁) (U₂ : Perm X₂) : Perm (X₁ × X₂) :=
  Equiv.prodCongr U₁ U₂

/-- **The product world on `Fin (n₁ * n₂)`**: `prodPerm` transported along `finProdFinEquiv`, which
pairs `(i, j)` with `j + n₂ * i`. Its action needs the evaluation lemma below — the transport does
*not* compute definitionally, `finProdFinEquiv.symm` being a `divNat`/`modNat` pair. -/
def prodWorldFin {n₁ n₂ : ℕ} (U₁ : Perm (Fin n₁)) (U₂ : Perm (Fin n₂)) : Perm (Fin (n₁ * n₂)) :=
  Equiv.permCongr finProdFinEquiv (Equiv.prodCongr U₁ U₂)

/-- The product world acts on each coordinate by its own factor. -/
@[simp] theorem prodWorldFin_apply {n₁ n₂ : ℕ} (U₁ : Perm (Fin n₁)) (U₂ : Perm (Fin n₂))
    (i : Fin n₁) (j : Fin n₂) :
    prodWorldFin U₁ U₂ (finProdFinEquiv (i, j)) = finProdFinEquiv (U₁ i, U₂ j) := by
  simp [prodWorldFin, Equiv.permCongr_def]

/-- Coordinates are preserved by every power: the product world never mixes its factors. -/
theorem prodWorldFin_pow {n₁ n₂ : ℕ} (U₁ : Perm (Fin n₁)) (U₂ : Perm (Fin n₂)) (t : ℕ)
    (i : Fin n₁) (j : Fin n₂) :
    ((prodWorldFin U₁ U₂) ^ t) (finProdFinEquiv (i, j))
      = finProdFinEquiv ((U₁ ^ t) i, (U₂ ^ t) j) := by
  induction t generalizing i j with
  | zero => simp
  | succ t ih => simp only [pow_succ]; simp [Equiv.Perm.mul_apply, ih]

/-- The product world's table entry at the pair `(i, j)`, in the index shape `List.ofFn_mul`
produces: state `i * n₂ + j` moves to `(U₂ j) + n₂ * (U₁ i)`. -/
private theorem prodWorldFin_val {n₁ n₂ : ℕ} (U₁ : Perm (Fin n₁)) (U₂ : Perm (Fin n₂)) (i : Fin n₁)
    (j : Fin n₂) (h : i.val * n₂ + j.val < n₁ * n₂) :
    ((prodWorldFin U₁ U₂ ⟨i.val * n₂ + j.val, h⟩ : Fin (n₁ * n₂)) : ℕ)
      = ((U₂ j : Fin n₂) : ℕ) + n₂ * ((U₁ i : Fin n₁) : ℕ) := by
  have hidx : (⟨i.val * n₂ + j.val, h⟩ : Fin (n₁ * n₂)) = finProdFinEquiv (i, j) := by
    apply Fin.ext
    simp [finProdFinEquiv_apply_val]
    ring
  rw [hidx, prodWorldFin_apply]
  simp [finProdFinEquiv_apply_val]

/-- **Two tables, interleaved**: one copy of the second table per entry of the first, each shifted
by the second block's size. The shift and the block count are both read off `T₂.length` — a table is
as long as its state space — so no size parameter appears. -/
def prodAppend (T₁ T₂ : List ℕ) : List ℕ :=
  T₁.flatMap (fun a => T₂.map (fun b => b + T₂.length * a))

private theorem primrec_prodAppend : Primrec fun q : List ℕ × List ℕ => prodAppend q.1 q.2 := by
  refine Primrec.list_flatMap Primrec.fst ?_
  refine Primrec₂.mk ?_
  refine Primrec.list_map (Primrec.snd.comp Primrec.fst) ?_
  refine Primrec₂.mk ?_
  exact Primrec.nat_add.comp Primrec.snd
    (Primrec.nat_mul.comp
      (Primrec.list_length.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)))
      (Primrec.snd.comp Primrec.fst))

/-- The product world's table is the two factors' tables, interleaved. -/
theorem lensTable_prodWorldFin {n₁ n₂ : ℕ} (U₁ : Perm (Fin n₁)) (U₂ : Perm (Fin n₂)) :
    lensTable ⇑(prodWorldFin U₁ U₂) = prodAppend (lensTable ⇑U₁) (lensTable ⇑U₂) := by
  have hlen : (lensTable ⇑U₂).length = n₂ := by rw [lensTable]; simp
  rw [prodAppend, hlen, lensTable, lensTable, lensTable, ← List.ofFn_eq_map, ← List.ofFn_eq_map,
    ← List.ofFn_eq_map, List.flatMap_def, List.map_ofFn]
  rw [List.ofFn_mul]
  congr 1
  refine congrArg List.ofFn (funext fun i => ?_)
  simp only [Function.comp_apply, List.map_ofFn]
  refine congrArg List.ofFn (funext fun j => ?_)
  simp only [Function.comp_apply]
  exact prodWorldFin_val U₁ U₂ i j _

/-- **The product-world builder**: on `⟨U₁'s table, U₂'s table⟩` it outputs the product world's
table. ONE fixed function, with no size parameters at all. -/
def prodTableFn (p : ℕ) : ℕ :=
  Encodable.encode
    (prodAppend ((Encodable.decode (α := List ℕ) p.unpair.1).getD [])
      ((Encodable.decode (α := List ℕ) p.unpair.2).getD []))

private theorem primrec_prodTableFn : Primrec prodTableFn := by
  have hdec1 : Primrec fun p : ℕ => (Encodable.decode (α := List ℕ) p.unpair.1).getD [] :=
    Primrec.option_getD.comp (Primrec.decode.comp (Primrec.fst.comp Primrec.unpair))
      (Primrec.const [])
  have hdec2 : Primrec fun p : ℕ => (Encodable.decode (α := List ℕ) p.unpair.2).getD [] :=
    Primrec.option_getD.comp (Primrec.decode.comp (Primrec.snd.comp Primrec.unpair))
      (Primrec.const [])
  exact Primrec.encode.comp (primrec_prodAppend.comp (Primrec.pair hdec1 hdec2))

/-- **The builder is correct**: it outputs exactly the product world's encoded table. -/
theorem prodTableFn_eq {n₁ n₂ : ℕ} (U₁ : Perm (Fin n₁)) (U₂ : Perm (Fin n₂)) :
    prodTableFn (Nat.pair (lensCode ⇑U₁) (lensCode ⇑U₂)) = lensCode ⇑(prodWorldFin U₁ U₂) := by
  rw [prodTableFn]
  simp only [Nat.unpair_pair, decode_lensCode]
  rw [← lensTable_prodWorldFin]
  rfl

private theorem partrec_prodTableFn : Nat.Partrec (fun p : ℕ => (prodTableFn p : ℕ)) :=
  _root_.Partrec.nat_iff.mp (Primrec.to_comp primrec_prodTableFn).partrec

/-- **The fixed product-world builder code.** -/
noncomputable def prodBuilder : Nat.Partrec.Code :=
  Classical.choose (Nat.Partrec.Code.exists_code.mp partrec_prodTableFn)

private theorem eval_prodBuilder (p : ℕ) :
    Nat.Partrec.Code.eval prodBuilder p = Part.some (prodTableFn p) := by
  have h := congrFun (Classical.choose_spec
    (Nat.Partrec.Code.exists_code.mp partrec_prodTableFn)) p
  simpa [prodBuilder] using h

/-- **Rules compose: the cheap-dynamics regime is closed under Cartesian product.** Given codes for
the two factors' tables, the product world costs their lengths plus an absolute constant
`elen prodBuilder + 6` — one fixed builder and the assembly's opcodes, independent of the worlds and
of `n₁`, `n₂`.

Not even one size parameter is loaded, and none is needed: each table is as long as its own state
space, so `prodTableFn` reads `n₂` off the second table and interleaves. This is the strongest form
the constant can take, and it matches `KE_unionWorld_le`'s.

If `U₁` and `U₂` have rules of order `log` of their sizes — as `KE_lcgWorld_le` exhibits — then so
does `U₁ × U₂`: putting a cheap world beside another cheap world cannot make the pair expensive to
describe. -/
theorem KE_prodWorldFin_le {n₁ n₂ : ℕ} (U₁ : Perm (Fin n₁)) (U₂ : Perm (Fin n₂))
    (c₁ c₂ : Nat.Partrec.Code) (h₁ : c₁.eval 0 = Part.some (lensCode ⇑U₁))
    (h₂ : c₂.eval 0 = Part.some (lensCode ⇑U₂)) :
    KE (lensCode ⇑(prodWorldFin U₁ U₂)) ≤ elen c₁ + elen c₂ + (elen prodBuilder + 6) := by
  have hp : Nat.Partrec.Code.eval (Nat.Partrec.Code.pair c₁ c₂) 0
      = Part.some (Nat.pair (lensCode ⇑U₁) (lensCode ⇑U₂)) := by
    change Nat.pair <$> _ <*> _ = _
    rw [h₁, h₂]; simp [Seq.seq]
  have hcomp : Computes (Nat.Partrec.Code.comp prodBuilder (Nat.Partrec.Code.pair c₁ c₂))
      (lensCode ⇑(prodWorldFin U₁ U₂)) := by
    change Nat.Partrec.Code.eval _ 0 = _
    rw [eval_comp_some hp, eval_prodBuilder, prodTableFn_eq]
  have hle := KE_le hcomp
  rw [E_len_comp, E_len_pair] at hle
  omega

/-- **A reading of the habitat, lifted to the product**: read the first coordinate and ignore the
second. -/
def prodLensFst {X₁ X₂ M : Type*} (ℓ₁ : ℕ → X₁ → M) : ℕ → X₁ × X₂ → M :=
  fun t x => ℓ₁ t x.1

/-- **The lift still carries its model.** The product's first coordinate evolves by `U₁` and by
nothing else, so persistence transports verbatim; surjectivity needs only that there is *some*
second coordinate to stand at. What the habitat does is unaffected by what it stands beside. -/
theorem carries_prodLensFst {X₁ X₂ M : Type*} [Nonempty X₂] {U₁ : X₁ → X₁} {U₂ : X₂ → X₂}
    {ℓ₁ : ℕ → X₁ → M} (h : Carries U₁ ℓ₁) :
    Carries (prodWorld U₁ U₂) (prodLensFst (X₂ := X₂) ℓ₁) := by
  constructor
  · intro v
    obtain ⟨x, hx⟩ := h.1 v
    exact ⟨(x, Classical.arbitrary X₂), hx⟩
  · intro t s
    simp only [prodLensFst, prodWorld_iterate_apply]
    exact h.2 t s.1

/-- **The lift satisfies the same square with the same law.** A sub-system of the habitat is a
sub-system of the product, running the identical `F`: one line, because the square is a statement
about the first coordinate only. -/
theorem intertwines_prodLensFst {X₁ X₂ M : Type*} {U₁ : X₁ → X₁} {U₂ : X₂ → X₂} {F : M → M}
    {ℓ₁ : ℕ → X₁ → M} (h : Intertwines U₁ F ℓ₁) :
    Intertwines (prodWorld U₁ U₂) F (prodLensFst (X₂ := X₂) ℓ₁) :=
  fun t s => h t s.1

/-- The lift on `Fin (n₁ * n₂)`: read the state's first coordinate through the factor's frame. -/
def prodLensFinFst {n₁ k₁ : ℕ} (ℓ₁ : ℕ → Fin n₁ → Fin k₁) (n₂ : ℕ) :
    ℕ → Fin (n₁ * n₂) → Fin k₁ :=
  fun t p => ℓ₁ t (finProdFinEquiv.symm p).1

@[simp] private theorem divNat_finProdFinEquiv {n₁ n₂ : ℕ} (i : Fin n₁) (j : Fin n₂) :
    (finProdFinEquiv (i, j)).divNat = i := by
  have h := finProdFinEquiv.symm_apply_apply (i, j)
  rw [finProdFinEquiv_symm_apply] at h
  exact congrArg Prod.fst h

@[simp] private theorem prodLensFinFst_apply {n₁ n₂ k₁ : ℕ} (ℓ₁ : ℕ → Fin n₁ → Fin k₁) (t : ℕ)
    (i : Fin n₁) (j : Fin n₂) :
    prodLensFinFst ℓ₁ n₂ t (finProdFinEquiv (i, j)) = ℓ₁ t i := by
  simp [prodLensFinFst]

/-- The lifted family carries the factor's model over the product world. A nonempty second factor
is what makes the lifted frame surjective. -/
theorem permCarries_prodLensFinFst {n₁ n₂ k₁ : ℕ} {U₁ : Perm (Fin n₁)} {U₂ : Perm (Fin n₂)}
    {ℓ₁ : ℕ → Fin n₁ → Fin k₁} (h : PermCarries U₁ ℓ₁) (hn₂ : 0 < n₂) :
    PermCarries (prodWorldFin U₁ U₂) (prodLensFinFst ℓ₁ n₂) := by
  constructor
  · intro v
    obtain ⟨i, hi⟩ := h.1 v
    exact ⟨finProdFinEquiv (i, ⟨0, hn₂⟩), by simpa using hi⟩
  · intro t p
    obtain ⟨⟨i, j⟩, rfl⟩ := finProdFinEquiv.surjective p
    rw [prodWorldFin_pow, prodLensFinFst_apply, prodLensFinFst_apply]
    exact h.2 t i

/-- **Each label, repeated once per state of the second factor.** The shape of the lifted frame's
table; the repetition count must be supplied — see `uniformBudget_prodLensFinFst`. -/
private def liftAppend (T₁ : List ℕ) (s : ℕ) : List ℕ := T₁.flatMap (fun a => List.replicate s a)

private theorem primrec_liftAppend : Primrec fun q : List ℕ × ℕ => liftAppend q.1 q.2 := by
  have hrw : (fun q : List ℕ × ℕ => liftAppend q.1 q.2)
      = fun q : List ℕ × ℕ => q.1.flatMap (fun a => (List.range q.2).map (fun _ => a)) := by
    funext q
    rw [liftAppend]
    simp only [List.map_const', List.length_range]
  rw [hrw]
  refine Primrec.list_flatMap Primrec.fst ?_
  refine Primrec₂.mk ?_
  refine Primrec.list_map (Primrec.list_range.comp (Primrec.snd.comp Primrec.fst)) ?_
  exact Primrec₂.mk (Primrec.snd.comp Primrec.fst)

private theorem lensTable_prodLensFinFst {n₁ n₂ k₁ : ℕ} (ℓ₁ : ℕ → Fin n₁ → Fin k₁) (t : ℕ) :
    lensTable (prodLensFinFst ℓ₁ n₂ t) = liftAppend (lensTable (ℓ₁ t)) n₂ := by
  rw [liftAppend, lensTable, lensTable, ← List.ofFn_eq_map, ← List.ofFn_eq_map,
    List.flatMap_def, List.map_ofFn]
  rw [List.ofFn_mul]
  congr 1
  refine congrArg List.ofFn (funext fun i => ?_)
  simp only [Function.comp_apply, ← List.ofFn_const]
  refine congrArg List.ofFn (funext fun j => ?_)
  have hidx : (⟨i.val * n₂ + j.val, by
      calc i.val * n₂ + j.val < (i.val + 1) * n₂ := by
            rw [Nat.add_mul, Nat.one_mul]; exact Nat.add_lt_add_left j.isLt _
        _ ≤ n₁ * n₂ := Nat.mul_le_mul_right _ i.isLt⟩ : Fin (n₁ * n₂))
      = finProdFinEquiv (i, j) := by
    apply Fin.ext
    simp [finProdFinEquiv_apply_val]
    ring
  simp only [prodLensFinFst, hidx]
  simp

/-- **The lift builder**: on `⟨the factor frame's table, n₂⟩` it gives the lifted frame's table. -/
private def liftLensTableFn (p : ℕ) : ℕ :=
  Encodable.encode
    (liftAppend ((Encodable.decode (α := List ℕ) p.unpair.1).getD []) p.unpair.2)

private theorem primrec_liftLensTableFn : Primrec liftLensTableFn := by
  have hdec1 : Primrec fun p : ℕ => (Encodable.decode (α := List ℕ) p.unpair.1).getD [] :=
    Primrec.option_getD.comp (Primrec.decode.comp (Primrec.fst.comp Primrec.unpair))
      (Primrec.const [])
  exact Primrec.encode.comp
    (primrec_liftAppend.comp (Primrec.pair hdec1 (Primrec.snd.comp Primrec.unpair)))

private theorem liftLensTableFn_eq {n₁ n₂ k₁ : ℕ} (ℓ₁ : ℕ → Fin n₁ → Fin k₁) (t : ℕ) :
    liftLensTableFn (Nat.pair (lensCode (ℓ₁ t)) n₂) = lensCode (prodLensFinFst ℓ₁ n₂ t) := by
  rw [liftLensTableFn]
  simp only [Nat.unpair_pair, decode_lensCode]
  rw [← lensTable_prodLensFinFst]
  rfl

private theorem partrec_liftLensTableFn : Nat.Partrec (fun p : ℕ => (liftLensTableFn p : ℕ)) :=
  _root_.Partrec.nat_iff.mp (Primrec.to_comp primrec_liftLensTableFn).partrec

/-- **The fixed lift-builder code.** -/
noncomputable def liftBuilder : Nat.Partrec.Code :=
  Classical.choose (Nat.Partrec.Code.exists_code.mp partrec_liftLensTableFn)

private theorem eval_liftBuilder (p : ℕ) :
    Nat.Partrec.Code.eval liftBuilder p = Part.some (liftLensTableFn p) := by
  have h := congrFun (Classical.choose_spec
    (Nat.Partrec.Code.exists_code.mp partrec_liftLensTableFn)) p
  simpa [liftBuilder] using h

/-- **The lifted reading is owned at the factor's budget plus the second factor's size.** The
`O (log n₂)` is not removable on this route and is not a fixed constant, for the same reason as in
`uniformBudget_unionLens`: a lens's table records one label per state, so it fixes the state count
but says nothing about how many states the *other* factor has. Standing beside a big environment
costs the observer the environment's size and nothing more. -/
theorem uniformBudget_prodLensFinFst {n₁ n₂ k₁ : ℕ} {ℓ₁ : ℕ → Fin n₁ → Fin k₁} {b₁ : ℕ}
    (h₁ : UniformBudget ℓ₁ b₁) :
    UniformBudget (prodLensFinFst ℓ₁ n₂) (b₁ + (15 + elen dbl) * Nat.size n₂
      + (elen liftBuilder + (15 + elen dbl) + 6)) := by
  obtain ⟨c₁, hlen₁, heval₁⟩ := h₁
  refine ⟨Nat.Partrec.Code.comp liftBuilder (Nat.Partrec.Code.pair c₁ (bconst n₂)), ?_, ?_⟩
  · have hb := elen_bconst_le n₂
    simp only [E_len_comp, E_len_pair]
    omega
  · intro t
    have hp : Nat.Partrec.Code.eval (Nat.Partrec.Code.pair c₁ (bconst n₂)) t
        = Part.some (Nat.pair (lensCode (ℓ₁ t)) n₂) := by
      change Nat.pair <$> _ <*> _ = _
      rw [heval₁ t, eval_bconst n₂ t]; simp [Seq.seq]
    rw [eval_comp_some hp, eval_liftBuilder, liftLensTableFn_eq]

/-- A lens table is as long as its state space. -/
theorem lensTable_length {n m : ℕ} (ℓ : Fin n → Fin m) : (lensTable ℓ).length = n := by
  rw [lensTable]; simp

/-- A lens table's entry at a state is that state's label. -/
private theorem lensTable_getD {n m : ℕ} (ℓ : Fin n → Fin m) (i : ℕ) (h : i < n) :
    (lensTable ℓ).getD i 0 = ((ℓ ⟨i, h⟩ : Fin m) : ℕ) := by
  rw [lensTable, ← List.ofFn_eq_map]
  rw [List.getD_eq_getElem _ _ (by simpa using h)]
  simp

/-- **Recovering the first factor's table** from the product's: the entry at `(i, 0)` is
`(U₂ 0) + n₂ · (U₁ i)`, so dividing by the second factor's size returns `U₁ i` exactly — the
residue is below `n₂` and vanishes. -/
def splitFst (T : List ℕ) (s : ℕ) : List ℕ :=
  (List.range (T.length / s)).map (fun i => T.getD (i * s) 0 / s)

/-- **Recovering the second factor's table** from the product's: the entry at `(0, j)` is
`(U₂ j) + n₂ · (U₁ 0)`, so its residue mod the second factor's size returns `U₂ j` exactly. -/
def splitSnd (T : List ℕ) (s : ℕ) : List ℕ :=
  (List.range s).map (fun j => T.getD j 0 % s)

private theorem primrec_splitFst : Primrec fun q : List ℕ × ℕ => splitFst q.1 q.2 := by
  refine Primrec.list_map
    (Primrec.list_range.comp (Primrec.nat_div.comp (Primrec.list_length.comp Primrec.fst)
      Primrec.snd)) ?_
  refine Primrec₂.mk ?_
  exact Primrec.nat_div.comp
    ((Primrec.list_getD 0).comp (Primrec.fst.comp Primrec.fst)
      (Primrec.nat_mul.comp Primrec.snd (Primrec.snd.comp Primrec.fst)))
    (Primrec.snd.comp Primrec.fst)

private theorem primrec_splitSnd : Primrec fun q : List ℕ × ℕ => splitSnd q.1 q.2 := by
  refine Primrec.list_map (Primrec.list_range.comp Primrec.snd) ?_
  refine Primrec₂.mk ?_
  exact Primrec.nat_mod.comp
    ((Primrec.list_getD 0).comp (Primrec.fst.comp Primrec.fst) Primrec.snd)
    (Primrec.snd.comp Primrec.fst)

private theorem splitFst_prodWorldFin {n₁ n₂ : ℕ} (U₁ : Perm (Fin n₁)) (U₂ : Perm (Fin n₂))
    (hn₂ : 0 < n₂) : splitFst (lensTable ⇑(prodWorldFin U₁ U₂)) n₂ = lensTable ⇑U₁ := by
  have hlenT : (lensTable ⇑(prodWorldFin U₁ U₂)).length = n₁ * n₂ := lensTable_length _
  rw [splitFst, hlenT, Nat.mul_div_cancel _ hn₂]
  apply List.ext_getElem
  · simp [lensTable_length]
  · intro i h1 h2
    have hi : i < n₁ := by simpa using h1
    rw [List.getElem_map, List.getElem_range, ← List.getD_eq_getElem _ 0 h2,
      lensTable_getD _ i hi]
    have hlt : i * n₂ + (0 : ℕ) < n₁ * n₂ := by
      calc i * n₂ + 0 = i * n₂ := by omega
        _ < (i + 1) * n₂ := by rw [Nat.add_mul, Nat.one_mul]; omega
        _ ≤ n₁ * n₂ := Nat.mul_le_mul_right _ hi
    have hidx : i * n₂ = i * n₂ + (0 : ℕ) := by omega
    rw [hidx, lensTable_getD _ _ hlt]
    rw [prodWorldFin_val U₁ U₂ ⟨i, hi⟩ ⟨0, hn₂⟩ hlt]
    rw [Nat.add_mul_div_left _ _ hn₂, Nat.div_eq_of_lt (U₂ ⟨0, hn₂⟩).isLt, Nat.zero_add]

private theorem splitSnd_prodWorldFin {n₁ n₂ : ℕ} (U₁ : Perm (Fin n₁)) (U₂ : Perm (Fin n₂))
    (hn₁ : 0 < n₁) : splitSnd (lensTable ⇑(prodWorldFin U₁ U₂)) n₂ = lensTable ⇑U₂ := by
  rw [splitSnd]
  apply List.ext_getElem
  · simp [lensTable_length]
  · intro j h1 h2
    have hj : j < n₂ := by simpa using h1
    rw [List.getElem_map, List.getElem_range, ← List.getD_eq_getElem _ 0 h2,
      lensTable_getD _ j hj]
    have hlt : 0 * n₂ + j < n₁ * n₂ := by
      calc 0 * n₂ + j = j := by omega
        _ < n₂ := hj
        _ = 1 * n₂ := by omega
        _ ≤ n₁ * n₂ := Nat.mul_le_mul_right _ hn₁
    have hidx : j = 0 * n₂ + j := by omega
    conv_lhs => rw [hidx]
    rw [lensTable_getD _ _ hlt, prodWorldFin_val U₁ U₂ ⟨0, hn₁⟩ ⟨j, hj⟩ hlt,
      Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (U₂ ⟨j, hj⟩).isLt]

/-- **The first-factor splitter**: on `⟨the product world's table, n₂⟩` it outputs the first
factor's table. -/
def splitFstFn (p : ℕ) : ℕ :=
  Encodable.encode
    (splitFst ((Encodable.decode (α := List ℕ) p.unpair.1).getD []) p.unpair.2)

/-- **The second-factor splitter**: on `⟨the product world's table, n₂⟩` it outputs the second
factor's table. -/
def splitSndFn (p : ℕ) : ℕ :=
  Encodable.encode
    (splitSnd ((Encodable.decode (α := List ℕ) p.unpair.1).getD []) p.unpair.2)

private theorem primrec_splitFstFn : Primrec splitFstFn := by
  have hdec : Primrec fun p : ℕ => (Encodable.decode (α := List ℕ) p.unpair.1).getD [] :=
    Primrec.option_getD.comp (Primrec.decode.comp (Primrec.fst.comp Primrec.unpair))
      (Primrec.const [])
  exact Primrec.encode.comp
    (primrec_splitFst.comp (Primrec.pair hdec (Primrec.snd.comp Primrec.unpair)))

private theorem primrec_splitSndFn : Primrec splitSndFn := by
  have hdec : Primrec fun p : ℕ => (Encodable.decode (α := List ℕ) p.unpair.1).getD [] :=
    Primrec.option_getD.comp (Primrec.decode.comp (Primrec.fst.comp Primrec.unpair))
      (Primrec.const [])
  exact Primrec.encode.comp
    (primrec_splitSnd.comp (Primrec.pair hdec (Primrec.snd.comp Primrec.unpair)))

theorem splitFstFn_eq {n₁ n₂ : ℕ} (U₁ : Perm (Fin n₁)) (U₂ : Perm (Fin n₂)) (hn₂ : 0 < n₂) :
    splitFstFn (Nat.pair (lensCode ⇑(prodWorldFin U₁ U₂)) n₂) = lensCode ⇑U₁ := by
  rw [splitFstFn]
  simp only [Nat.unpair_pair, decode_lensCode]
  rw [splitFst_prodWorldFin U₁ U₂ hn₂]
  rfl

theorem splitSndFn_eq {n₁ n₂ : ℕ} (U₁ : Perm (Fin n₁)) (U₂ : Perm (Fin n₂)) (hn₁ : 0 < n₁) :
    splitSndFn (Nat.pair (lensCode ⇑(prodWorldFin U₁ U₂)) n₂) = lensCode ⇑U₂ := by
  rw [splitSndFn]
  simp only [Nat.unpair_pair, decode_lensCode]
  rw [splitSnd_prodWorldFin U₁ U₂ hn₁]
  rfl

private theorem partrec_splitFstFn : Nat.Partrec (fun p : ℕ => (splitFstFn p : ℕ)) :=
  _root_.Partrec.nat_iff.mp (Primrec.to_comp primrec_splitFstFn).partrec

private theorem partrec_splitSndFn : Nat.Partrec (fun p : ℕ => (splitSndFn p : ℕ)) :=
  _root_.Partrec.nat_iff.mp (Primrec.to_comp primrec_splitSndFn).partrec

/-- **The fixed first-factor splitter code.** -/
noncomputable def splitFstBuilder : Nat.Partrec.Code :=
  Classical.choose (Nat.Partrec.Code.exists_code.mp partrec_splitFstFn)

/-- **The fixed second-factor splitter code.** -/
noncomputable def splitSndBuilder : Nat.Partrec.Code :=
  Classical.choose (Nat.Partrec.Code.exists_code.mp partrec_splitSndFn)

private theorem eval_splitFstBuilder (p : ℕ) :
    Nat.Partrec.Code.eval splitFstBuilder p = Part.some (splitFstFn p) := by
  have h := congrFun (Classical.choose_spec
    (Nat.Partrec.Code.exists_code.mp partrec_splitFstFn)) p
  simpa [splitFstBuilder] using h

private theorem eval_splitSndBuilder (p : ℕ) :
    Nat.Partrec.Code.eval splitSndBuilder p = Part.some (splitSndFn p) := by
  have h := congrFun (Classical.choose_spec
    (Nat.Partrec.Code.exists_code.mp partrec_splitSndFn)) p
  simpa [splitSndBuilder] using h

/-- **A faithful reading of the product hands back the FIRST factor's rule.** An observer reading
the whole product bijectively and owning that reading at budget `b` stores a description of `U₁` at
`2 · b + O (log n₂) + O (1)`.

The route is the ledger followed by a fixed splitter: `faithful_rule_cost` turns the owned faithful
family into a description of the product world's own table, and `splitFstBuilder` divides out the
second factor's size. The factor two is inherited — it is `faithful_rule_cost`'s own, the owner's
program written twice, at the two clock values the ledger reads. -/
theorem KE_factorFst_le_of_faithful {n₁ n₂ k : ℕ} {U₁ : Perm (Fin n₁)} {U₂ : Perm (Fin n₂)}
    {ℓ : ℕ → Fin (n₁ * n₂) → Fin k} {b : ℕ}
    (hcar : PermCarries (prodWorldFin U₁ U₂) ℓ) (hbij : Function.Bijective (ℓ 0))
    (hbud : UniformBudget ℓ b) (hn₂ : 0 < n₂) :
    KE (lensCode ⇑U₁) ≤ 2 * b + (15 + elen dbl) * Nat.size n₂
      + (elen splitFstBuilder + elen icode + 4 * (15 + elen dbl) + 18) := by
  have hprod := faithful_rule_cost hcar hbij hbud
  obtain ⟨c, hc, hlen⟩ := exists_min_E (lensCode ⇑(prodWorldFin U₁ U₂))
  have hb := elen_bconst_le n₂
  have hp : Nat.Partrec.Code.eval (Nat.Partrec.Code.pair c (bconst n₂)) 0
      = Part.some (Nat.pair (lensCode ⇑(prodWorldFin U₁ U₂)) n₂) := by
    change Nat.pair <$> _ <*> _ = _
    rw [hc, eval_bconst n₂ 0]; simp [Seq.seq]
  have hcomp : Computes (Nat.Partrec.Code.comp splitFstBuilder
      (Nat.Partrec.Code.pair c (bconst n₂))) (lensCode ⇑U₁) := by
    change Nat.Partrec.Code.eval _ 0 = _
    rw [eval_comp_some hp, eval_splitFstBuilder, splitFstFn_eq U₁ U₂ hn₂]
  have hle := KE_le hcomp
  rw [E_len_comp, E_len_pair] at hle
  omega

/-- **A faithful reading of the product hands back the SECOND factor's rule** — the factor the
observer may have no interest in. Same route, taking the residue instead of the quotient.

Read against `uniformBudget_prodLensFinFst` this is the contrast the product world exists to
exhibit. A reading confined to the first factor is owned at that factor's own budget plus
`O (log n₂)`, however wild the second factor is. A reading of the *whole* world is not: it prices
the observer at half of `KE` of the second factor's rule, so over any family of second factors whose
rules are incompressible — the overwhelming majority of permutations, by `collapse_generic`'s
counting — no faithful reading of the product is affordable at all. Cheap to run a sub-system in;
unaffordable to read entire. -/
theorem KE_factorSnd_le_of_faithful {n₁ n₂ k : ℕ} {U₁ : Perm (Fin n₁)} {U₂ : Perm (Fin n₂)}
    {ℓ : ℕ → Fin (n₁ * n₂) → Fin k} {b : ℕ}
    (hcar : PermCarries (prodWorldFin U₁ U₂) ℓ) (hbij : Function.Bijective (ℓ 0))
    (hbud : UniformBudget ℓ b) (hn₁ : 0 < n₁) :
    KE (lensCode ⇑U₂) ≤ 2 * b + (15 + elen dbl) * Nat.size n₂
      + (elen splitSndBuilder + elen icode + 4 * (15 + elen dbl) + 18) := by
  have hprod := faithful_rule_cost hcar hbij hbud
  obtain ⟨c, hc, hlen⟩ := exists_min_E (lensCode ⇑(prodWorldFin U₁ U₂))
  have hb := elen_bconst_le n₂
  have hp : Nat.Partrec.Code.eval (Nat.Partrec.Code.pair c (bconst n₂)) 0
      = Part.some (Nat.pair (lensCode ⇑(prodWorldFin U₁ U₂)) n₂) := by
    change Nat.pair <$> _ <*> _ = _
    rw [hc, eval_bconst n₂ 0]; simp [Seq.seq]
  have hcomp : Computes (Nat.Partrec.Code.comp splitSndBuilder
      (Nat.Partrec.Code.pair c (bconst n₂))) (lensCode ⇑U₂) := by
    change Nat.Partrec.Code.eval _ 0 = _
    rw [eval_comp_some hp, eval_splitSndBuilder, splitSndFn_eq U₁ U₂ hn₁]
  have hle := KE_le hcomp
  rw [E_len_comp, E_len_pair] at hle
  omega

/-- The lifted frame, as a static lens: the family lift read at one frame. -/
def liftFst {n₁ k₁ : ℕ} (ℓ₀ : Fin n₁ → Fin k₁) (n₂ : ℕ) : Fin (n₁ * n₂) → Fin k₁ :=
  fun p => ℓ₀ (finProdFinEquiv.symm p).1

@[simp] private theorem liftFst_apply {n₁ n₂ k₁ : ℕ} (ℓ₀ : Fin n₁ → Fin k₁) (i : Fin n₁)
    (j : Fin n₂) : liftFst ℓ₀ n₂ (finProdFinEquiv (i, j)) = ℓ₀ i := by simp [liftFst]

private theorem liftFst_injective {n₁ n₂ k₁ : ℕ} (hn₂ : 0 < n₂) :
    Function.Injective (fun ℓ₀ : Fin n₁ → Fin k₁ => liftFst ℓ₀ n₂) := by
  intro ℓ₀ ℓ₀' h
  funext i
  have := congrFun h (finProdFinEquiv (i, ⟨0, hn₂⟩))
  simpa using this

/-- **The lift is equivariant**: relabelling the factor by `U` is relabelling the product by
`U × 1`. This is what makes the capacity projection an orbit *embedding* rather than a multinomial
computation. -/
theorem liftFst_smul {n₁ n₂ k₁ : ℕ} (U : Perm (Fin n₁)) (ℓ₀ : Fin n₁ → Fin k₁) :
    liftFst (U • ℓ₀) n₂ = (prodWorldFin U (1 : Perm (Fin n₂))) • (liftFst ℓ₀ n₂) := by
  funext p
  obtain ⟨⟨i, j⟩, rfl⟩ := finProdFinEquiv.surjective p
  have hinv : (prodWorldFin U (1 : Perm (Fin n₂)))⁻¹ (finProdFinEquiv (i, j))
      = finProdFinEquiv (U⁻¹ i, j) := by
    rw [Equiv.Perm.inv_def, Equiv.symm_apply_eq, prodWorldFin_apply]
    simp
  rw [smul_lens_apply, hinv, liftFst_apply, liftFst_apply, smul_lens_apply]

/-- The factor's orbit embeds in the product's: equivariance sends `U • ℓ₀` to `(U × 1) • liftFst`,
and the lift is injective, so no two relabellings of the factor collide. -/
private theorem card_orbit_le_liftFst {n₁ n₂ k₁ : ℕ} (ℓ₀ : Fin n₁ → Fin k₁) (hn₂ : 0 < n₂) :
    Nat.card ↥(orbit (Perm (Fin n₁)) ℓ₀)
      ≤ Nat.card ↥(orbit (Perm (Fin (n₁ * n₂))) (liftFst ℓ₀ n₂)) := by
  have : Finite ↥(orbit (Perm (Fin (n₁ * n₂))) (liftFst ℓ₀ n₂)) := Set.toFinite _
  refine Nat.card_le_card_of_injective
    (fun x : ↥(orbit (Perm (Fin n₁)) ℓ₀) => (⟨liftFst x.1 n₂, ?_⟩ :
      ↥(orbit (Perm (Fin (n₁ * n₂))) (liftFst ℓ₀ n₂)))) ?_
  · obtain ⟨U, hU⟩ := x.2
    exact ⟨prodWorldFin U (1 : Perm (Fin n₂)), by
      change (prodWorldFin U (1 : Perm (Fin n₂))) • liftFst ℓ₀ n₂ = liftFst (x.1) n₂
      rw [← liftFst_smul]
      exact congrArg (fun z => liftFst z n₂) hU⟩
  · intro x y h
    exact Subtype.ext (liftFst_injective hn₂ (Subtype.ext_iff.mp h))

/-- **Capacity projects through the product**: whatever entropy an owner can carry in a factor, it
can carry in the product at the same budget plus the lift's `O (log n₂)`.

So a world with one kind factor hosts affordable sub-systems regardless of what its other factor
does — the kind factor's capacity is a floor for the whole. Nothing here contradicts the collapse:
the collapse prices *generic* worlds, and a product world is not one. -/
theorem CbHu_prodWorldFin_ge_fst {n₁ n₂ : ℕ} (U₁ : Perm (Fin n₁)) (U₂ : Perm (Fin n₂)) (b₁ : ℕ)
    (hn₂ : 0 < n₂) :
    CbHu U₁ b₁ ≤ CbHu (prodWorldFin U₁ U₂) (b₁ + (15 + elen dbl) * Nat.size n₂
      + (elen liftBuilder + (15 + elen dbl) + 6)) := by
  rcases Set.eq_empty_or_nonempty (UniformBudgetedEntropies U₁ b₁) with hemp | hne
  · simp [CbHu, hemp]
  · refine csSup_le hne ?_
    rintro N ⟨k, ℓ₁, hcar, hbud, rfl⟩
    calc Nat.card ↥(orbit (Perm (Fin n₁)) (ℓ₁ 0))
        ≤ Nat.card ↥(orbit (Perm (Fin (n₁ * n₂))) (liftFst (ℓ₁ 0) n₂)) :=
          card_orbit_le_liftFst _ hn₂
      _ ≤ _ := CbHu_ge_of_uniform (permCarries_prodLensFinFst hcar hn₂)
                (uniformBudget_prodLensFinFst hbud)

end Collapse

/-! ## The robustness margin: how far a settled reading survives a perturbation
([Persistence] §10.1 + §2)

Settling asks that the reading be right *eventually* along orbits from a basin `B`. It says nothing
about what happens if the world is *kicked* — if a state on the attractor `ω(B)` is perturbed in a
few cells. This section prices that.

The setting returns to the cell-structured memory `Mem ι V = ι → V` ([Persistence] §2.1), because a
perturbation is counted in cells: `hammingDist`. The **robustness margin** of a settling family is
the largest `e` such that every `e`-cell perturbation of an attractor state stays in the basin and
keeps the settled value. `HasMargin` bundles the two demands; `hasMargin_iff` separates them into
**basin fatness** (`Ball e s ⊆ B`) and **local constancy** (`v` is constant there), which is the
form the design calls for and which is here a one-line consequence — the two do not diverge.

**What the margin depends on.** Not on the observer's family: `HasMargin` mentions only `U`, `B`,
`v` and `e`. The family `ℓ` enters solely in certifying that `v` *is* the settled value
(`SettlesValue`), so the margin is an attribute of the sub-system, not of who is watching it.

**The price** (`repair_tax`, [Persistence] §10.1's sphere packing). Distinct settled values on the
attractor cannot be `e`-close, so the `e`-balls around one representative per value are pairwise
disjoint — and Hamming space is homogeneous, so they all have the ball's cardinality. Counting them
inside the memory gives `#values * #Ball e ≤ #Mem`, the multiplicative form of the paper's display
`log₂|Ω| ≤ |Mem|·log₂|V| − log₂|Ball_e|`: **every cell of margin is paid for out of carried
content**. Tightness for repetition codes is paper-level and not formalized here.

Recovery *time* (`RecoversWithin`) is defined and shown monotone, and no more: its theory is the
temporal frontier. -/

section Margin

/-- A **settling family with a named settled value** ([Persistence] §10.1, the lens-family form over
an arbitrary world): along every orbit from `B` the reading is eventually constant, at the value `v`
records. The transient is pointwise and unbounded — nothing here bounds when settling happens. -/
def SettlesValue (U : X → X) (ℓ : ℕ → X → M) (B : Set X) (v : X → M) : Prop :=
  ∀ s ∈ B, ∃ T, ∀ t ≥ T, ℓ t (U^[t] s) = v s

/-- The **Hamming ball** of radius `e` about `c`: the states reachable by corrupting at most `e`
cells. -/
def hball [Fintype ι] [DecidableEq V] (e : ℕ) (c : Mem ι V) : Set (Mem ι V) :=
  {x | hammingDist c x ≤ e}

private theorem mem_hball [Fintype ι] [DecidableEq V] {e : ℕ} {c x : Mem ι V} :
    x ∈ hball e c ↔ hammingDist c x ≤ e := Iff.rfl

private theorem hball_mono [Fintype ι] [DecidableEq V] {e e' : ℕ} (h : e ≤ e') (c : Mem ι V) :
    hball e c ⊆ hball e' c := fun _ hx => le_trans hx h

instance instDecidableMemHball [Fintype ι] [DecidableEq V] (e : ℕ) (c : Mem ι V) :
    DecidablePred (· ∈ hball e c) :=
  fun x => inferInstanceAs (Decidable (hammingDist c x ≤ e))

/-- **The robustness margin condition.** Every `e`-cell perturbation of a state on the attractor
`ω(B)` lands back in the basin and is read at the same settled value: the reading on the attractor
is an `e`-error-correcting code whose decoder is the world's own dynamics.

Note what is *absent*: the observer's family `ℓ`. The margin constrains `B` and `v` only. -/
def HasMargin [Fintype ι] [DecidableEq V] (U : Mem ι V → Mem ι V) (B : Set (Mem ι V))
    (v : Mem ι V → M) (e : ℕ) : Prop :=
  ∀ s ∈ omegaLimit U B, ∀ s' ∈ hball e s, s' ∈ B ∧ v s' = v s

/-- **The factorization** ([Persistence] §10.1, the design's coherence test): the margin condition
is exactly **basin fatness** (`Ball e s ⊆ B` around every attractor state) together with **local
constancy** (`v` constant on each such ball, intersected with the basin).

The two forms do not diverge: fatness makes the intersection in the second clause the whole ball,
which is why the one-clause and two-clause readings agree. Constancy is stated as "equal to `v s`"
rather than "constant on the set", and the two agree because `s` itself lies in the set. -/
theorem hasMargin_iff [Fintype ι] [DecidableEq V] (U : Mem ι V → Mem ι V) (B : Set (Mem ι V))
    (v : Mem ι V → M) (e : ℕ) :
    HasMargin U B v e ↔
      (∀ s ∈ omegaLimit U B, hball e s ⊆ B) ∧
      (∀ s ∈ omegaLimit U B, ∀ s' ∈ hball e s ∩ B, v s' = v s) := by
  constructor
  · intro h
    exact ⟨fun s hs s' hs' => (h s hs s' hs').1, fun s hs s' hs' => (h s hs s' hs'.1).2⟩
  · rintro ⟨hfat, hconst⟩ s hs s' hs'
    have hmem : s' ∈ B := hfat s hs hs'
    exact ⟨hmem, hconst s hs s' ⟨hs', hmem⟩⟩

/-- A margin is a margin at every smaller radius. -/
theorem HasMargin.mono [Fintype ι] [DecidableEq V] {U : Mem ι V → Mem ι V} {B : Set (Mem ι V)}
    {v : Mem ι V → M} {e e' : ℕ} (h : HasMargin U B v e) (hle : e' ≤ e) :
    HasMargin U B v e' := fun s hs s' hs' => h s hs s' (hball_mono hle s hs')

/-- **The degenerate sanity check**: every settling family has margin `0`. A zero-cell perturbation
is no perturbation (`hammingDist x y = 0 ↔ x = y`), and the attractor is inside its own basin. -/
private theorem hasMargin_zero [Fintype ι] [DecidableEq V] (U : Mem ι V → Mem ι V)
    (B : Set (Mem ι V)) (v : Mem ι V → M) : HasMargin U B v 0 := by
  intro s hs s' hs'
  have : s = s' := hammingDist_eq_zero.mp (Nat.le_zero.mp hs')
  subst this
  exact ⟨omegaLimit_subset U B hs, rfl⟩

/-- The radii at which the reading is robust, capped at the memory's width. The cap costs nothing:
`hammingDist` never exceeds `Fintype.card ι`, so beyond it the condition has already saturated —
and it is what makes the supremum below a supremum of a bounded set rather than the `ℕ`-`sSup`
convention's `0`. -/
def MarginSet [Fintype ι] [DecidableEq V] (U : Mem ι V → Mem ι V) (B : Set (Mem ι V))
    (v : Mem ι V → M) : Set ℕ :=
  {e | e ≤ Fintype.card ι ∧ HasMargin U B v e}

/-- **The robustness margin** `e(S)` of a settling family: the largest number of cells that may be
corrupted on the attractor without moving the settled reading. -/
noncomputable def margin [Fintype ι] [DecidableEq V] (U : Mem ι V → Mem ι V) (B : Set (Mem ι V))
    (v : Mem ι V → M) : ℕ :=
  sSup (MarginSet U B v)

private theorem zero_mem_marginSet [Fintype ι] [DecidableEq V] (U : Mem ι V → Mem ι V)
    (B : Set (Mem ι V)) (v : Mem ι V → M) : 0 ∈ MarginSet U B v :=
  ⟨Nat.zero_le _, hasMargin_zero U B v⟩

private theorem bddAbove_marginSet [Fintype ι] [DecidableEq V] (U : Mem ι V → Mem ι V)
    (B : Set (Mem ι V)) (v : Mem ι V → M) : BddAbove (MarginSet U B v) :=
  ⟨Fintype.card ι, fun _ he => he.1⟩

private theorem le_margin [Fintype ι] [DecidableEq V] {U : Mem ι V → Mem ι V} {B : Set (Mem ι V)}
    {v : Mem ι V → M} {e : ℕ} (he : e ∈ MarginSet U B v) : e ≤ margin U B v :=
  le_csSup (bddAbove_marginSet U B v) he

/-- **The margin is itself a margin**: the supremum is attained, so `margin` names a radius at which
the reading really is robust. -/
theorem hasMargin_margin [Fintype ι] [DecidableEq V] (U : Mem ι V → Mem ι V) (B : Set (Mem ι V))
    (v : Mem ι V → M) : HasMargin U B v (margin U B v) :=
  (Nat.sSup_mem ⟨0, zero_mem_marginSet U B v⟩ (bddAbove_marginSet U B v)).2

/-! ### The price of a margin: sphere packing in the memory ([Persistence] §10.1) -/

/-- The **transporter** carrying `c` to `s`: swap the two cells' values in every coordinate. Hamming
space is homogeneous, and this is the witness — a distance-preserving bijection of the whole memory
taking any state to any other. -/
def transport [DecidableEq V] (c s : Mem ι V) : Mem ι V ≃ Mem ι V :=
  Equiv.piCongrRight fun i => Equiv.swap (c i) (s i)

private theorem transport_apply [DecidableEq V] (c s x : Mem ι V) (i : ι) :
    transport c s x i = Equiv.swap (c i) (s i) (x i) := rfl

private theorem transport_left [DecidableEq V] (c s : Mem ι V) : transport c s c = s := by
  funext i
  simp [transport_apply]

/-- The transporter preserves Hamming distance: it acts injectively in each cell. -/
theorem hammingDist_transport [Fintype ι] [DecidableEq V] (c s x y : Mem ι V) :
    hammingDist (transport c s x) (transport c s y) = hammingDist x y :=
  hammingDist_comp (fun i => (Equiv.swap (c i) (s i) : V → V))
    (fun i => (Equiv.swap (c i) (s i)).injective)

/-- Balls are carried to balls: the transporter maps `Ball e c` into `Ball e s`. -/
private theorem transport_mem_hball [Fintype ι] [DecidableEq V] {e : ℕ} {c x : Mem ι V}
    (s : Mem ι V) (hx : x ∈ hball e c) : transport c s x ∈ hball e s := by
  have h : hammingDist (transport c s c) (transport c s x) = hammingDist c x :=
    hammingDist_transport c s c x
  rw [transport_left] at h
  rw [mem_hball, h]
  exact hx

/-- **The repair tax** ([Persistence] §10.1, the sphere-packing bound). A settling family with
margin `e` pays for it in carried content: the settled values attained on the attractor, times the
size of an `e`-ball, fit inside the memory.

Two facts do the work. Distinct settled values on the attractor are `e`-**separated**: a state
`e`-close to two attractor points of different value would have to be read at both values at once,
so the `e`-balls around one representative per value are pairwise **disjoint**. And Hamming space is
homogeneous (`transport`), so each of those balls has the cardinality of the ball about *any*
centre `c` — which is why the bound may be stated with a ball the caller chooses.

This is the multiplicative `ℕ` form of the paper's display
`log₂|Ω| ≤ |Mem|·log₂|V| − log₂|Ball_e(|Mem|)|`. Tightness for repetition codes is paper-level and
is not formalized here. -/
theorem repair_tax [Fintype ι] [DecidableEq V] [Finite V] {U : Mem ι V → Mem ι V}
    {B : Set (Mem ι V)} {v : Mem ι V → M} {e : ℕ} (h : HasMargin U B v e) (c : Mem ι V) :
    Nat.card ↥(v '' omegaLimit U B) * Nat.card ↥(hball e c) ≤ Nat.card (Mem ι V) := by
  classical
  -- one representative on the attractor per attained settled value
  have hrep : ∀ w : ↥(v '' omegaLimit U B), ∃ s, s ∈ omegaLimit U B ∧ v s = (w : M) :=
    fun w => w.2
  choose rep hrepA hrepv using hrep
  -- transporting the chosen ball onto a representative's ball keeps that representative's value
  have key : ∀ (w : ↥(v '' omegaLimit U B)) (x : ↥(hball e c)),
      v (transport c (rep w) (x : Mem ι V)) = (w : M) := by
    intro w x
    have hmem := transport_mem_hball (rep w) x.2
    rw [(h (rep w) (hrepA w) _ hmem).2, hrepv w]
  rw [← Nat.card_prod]
  refine Nat.card_le_card_of_injective
    (fun p : ↥(v '' omegaLimit U B) × ↥(hball e c) => transport c (rep p.1) (p.2 : Mem ι V)) ?_
  rintro ⟨w, x⟩ ⟨w', x'⟩ hpq
  simp only at hpq
  -- the shared image lies in both balls, so the two values coincide: the balls are disjoint
  have hw : w = w' := Subtype.ext (by rw [← key w x, ← key w' x', hpq])
  subst hw
  -- and the transporter is a bijection, so the ball points coincide too
  have hx : x = x' := Subtype.ext ((transport c (rep w)).injective hpq)
  subst hx
  rfl

/-- **The repair tax with every value attained**: if the settled value is surjective on the
attractor, the whole value alphabet is taxed — `#M * #Ball e ≤ #Mem`. -/
theorem repair_tax_surjOn [Fintype ι] [DecidableEq V] [Finite V] {U : Mem ι V → Mem ι V}
    {B : Set (Mem ι V)} {v : Mem ι V → M} {e : ℕ} (h : HasMargin U B v e)
    (hsurj : Set.SurjOn v (omegaLimit U B) Set.univ) (c : Mem ι V) :
    Nat.card M * Nat.card ↥(hball e c) ≤ Nat.card (Mem ι V) := by
  have himg : v '' omegaLimit U B = Set.univ := Set.eq_univ_of_univ_subset hsurj
  have := repair_tax h (v := v) c
  rwa [himg, Nat.card_coe_set_eq, Set.ncard_univ] at this

/-! ### Recovery time: the definition only ([Persistence] §10.1; the temporal frontier)

How *long* repair takes is the unpriced dimension. The predicate and its monotonicity are recorded
here so the quantity has a name; its theory is deliberately out of scope. -/

/-- The family has **recovered by `T`** at radius `e`: every `e`-cell perturbation of an attractor
state is read at its settled value from step `T` on. -/
def RecoversWithin [Fintype ι] [DecidableEq V] (U : Mem ι V → Mem ι V) (ℓ : ℕ → Mem ι V → M)
    (B : Set (Mem ι V)) (v : Mem ι V → M) (e T : ℕ) : Prop :=
  ∀ s ∈ omegaLimit U B, ∀ s' ∈ hball e s, ∀ t ≥ T, ℓ t (U^[t] s') = v s'

private theorem RecoversWithin.mono_time [Fintype ι] [DecidableEq V] {U : Mem ι V → Mem ι V}
    {ℓ : ℕ → Mem ι V → M} {B : Set (Mem ι V)} {v : Mem ι V → M} {e T T' : ℕ}
    (h : RecoversWithin U ℓ B v e T) (hle : T ≤ T') : RecoversWithin U ℓ B v e T' :=
  fun s hs s' hs' t ht => h s hs s' hs' t (le_trans hle ht)

private theorem RecoversWithin.mono_radius [Fintype ι] [DecidableEq V] {U : Mem ι V → Mem ι V}
    {ℓ : ℕ → Mem ι V → M} {B : Set (Mem ι V)} {v : Mem ι V → M} {e e' T : ℕ}
    (h : RecoversWithin U ℓ B v e T) (hle : e' ≤ e) : RecoversWithin U ℓ B v e' T :=
  fun s hs s' hs' => h s hs s' (hball_mono hle s hs')

/-- Under a margin, recovery restores the **attractor's** value, not merely the perturbed state's
own: the two agree exactly because the perturbation stayed inside the margin. -/
private theorem RecoversWithin.settled_value [Fintype ι] [DecidableEq V] {U : Mem ι V → Mem ι V}
    {ℓ : ℕ → Mem ι V → M} {B : Set (Mem ι V)} {v : Mem ι V → M} {e T : ℕ}
    (hm : HasMargin U B v e) (h : RecoversWithin U ℓ B v e T) :
    ∀ s ∈ omegaLimit U B, ∀ s' ∈ hball e s, ∀ t ≥ T, ℓ t (U^[t] s') = v s :=
  fun s hs s' hs' t ht => (h s hs s' hs' t ht).trans (hm s hs s' hs').2

/-- **The recovery time** at radius `e`: the least step by which every `e`-perturbation is read
correctly. -/
noncomputable def recoveryTime [Fintype ι] [DecidableEq V] (U : Mem ι V → Mem ι V)
    (ℓ : ℕ → Mem ι V → M) (B : Set (Mem ι V)) (v : Mem ι V → M) (e : ℕ) : ℕ :=
  sInf {T | RecoversWithin U ℓ B v e T}

private theorem recoveryTime_le [Fintype ι] [DecidableEq V] {U : Mem ι V → Mem ι V}
    {ℓ : ℕ → Mem ι V → M} {B : Set (Mem ι V)} {v : Mem ι V → M} {e T : ℕ}
    (h : RecoversWithin U ℓ B v e T) :
    recoveryTime U ℓ B v e ≤ T := Nat.sInf_le h

private theorem recoversWithin_recoveryTime [Fintype ι] [DecidableEq V] {U : Mem ι V → Mem ι V}
    {ℓ : ℕ → Mem ι V → M} {B : Set (Mem ι V)} {v : Mem ι V → M} {e : ℕ}
    (h : ∃ T, RecoversWithin U ℓ B v e T) :
    RecoversWithin U ℓ B v e (recoveryTime U ℓ B v e) := Nat.sInf_mem h

/-! ### The positive witness: the majority world is robust ([Decoupling] §3.5) -/

/-- The majority world writes back its own consensus bit: `majBit` is invariant under one step. -/
private theorem majBit_majWorld (s : Mem (Fin 3) Bool) : majBit (majWorld s) = majBit s := by
  rw [majWorld_apply]
  cases h : majBit s <;> simp [majBit]

/-- …hence under every number of steps: the consensus bit is what the majority world conserves. -/
private theorem majBit_iterate (t : ℕ) (s : Mem (Fin 3) Bool) :
    majBit (majWorld^[t] s) = majBit s := by
  induction t with
  | zero => rfl
  | succ t ih => rw [Function.iterate_succ_apply', majBit_majWorld]; exact ih

/-- The consensus bit settles instantly along every orbit: the majority world with the static
decoder `majBit` is a settling family, with transient zero. -/
private theorem settlesValue_majWorld :
    SettlesValue majWorld (fun _ => majBit) (Set.univ : Set (Mem (Fin 3) Bool)) majBit :=
  fun s _ => ⟨0, fun t _ => majBit_iterate t s⟩

/-- Both bits are attained: the settled reading carries one full bit. -/
private theorem surjOn_majBit :
    Set.SurjOn majBit (Set.univ : Set (Mem (Fin 3) Bool)) Set.univ := by
  intro b _
  exact ⟨fun _ => b, Set.mem_univ _, by cases b <;> rfl⟩

/-- **The majority world has margin at least one** — the probe's positive witness. On the attractor
(the consensus set, `core_majWorld`) all three copies agree, so flipping any single copy leaves two
in agreement and the majority — hence the settled bit — unchanged. The `1` is the whole content of
"three-copy redundancy corrects one error", read here as a property of the *world's dynamics*
rather than of a code: `majWorld` is its own decoder. -/
private theorem hasMargin_majWorld :
    HasMargin majWorld (Set.univ : Set (Mem (Fin 3) Bool)) majBit 1 := by
  intro s hs s' hs'
  refine ⟨Set.mem_univ _, ?_⟩
  rw [← core_eq_omegaLimit, core_majWorld] at hs
  obtain ⟨h01, h12⟩ := hs
  rw [mem_hball] at hs'
  revert h01 h12 hs'
  revert s s'
  decide

private theorem margin_majWorld : 1 ≤ margin majWorld (Set.univ : Set (Mem (Fin 3) Bool)) majBit :=
  le_margin ⟨by simp, hasMargin_majWorld⟩

/-- **The tax is tight on the worked witness.** Three cells over two values is a memory of eight
states; the majority world's attractor carries two settled values, and a radius-one ball holds four
— `2 * 4 = 8`, the memory exactly. Three-copy redundancy spends its *entire* capacity buying margin
one, which is what makes `repair_tax` a real constraint rather than slack. Tightness for repetition
codes in general is paper-level ([Persistence] §10.1) and is not formalized here. -/
theorem repair_tax_tight_majWorld :
    Nat.card ↥(majBit '' omegaLimit majWorld (Set.univ : Set (Mem (Fin 3) Bool))) *
        Nat.card ↥(hball 1 (fun _ => false : Mem (Fin 3) Bool))
      = Nat.card (Mem (Fin 3) Bool) := by
  rw [← core_eq_omegaLimit, core_majWorld]
  simp only [Nat.card_eq_fintype_card]
  decide

/-- **The worked robust sub-system**: the majority world carries a settling family whose settled
value is surjective — one full bit — and whose robustness margin is at least one cell. Total
overwrite globally, one-error-correcting on-shell. -/
theorem majority_margin :
    ∃ (ℓ : ℕ → Mem (Fin 3) Bool → Bool) (v : Mem (Fin 3) Bool → Bool),
      SettlesValue majWorld ℓ Set.univ v ∧ Set.SurjOn v Set.univ Set.univ ∧
      1 ≤ margin majWorld Set.univ v :=
  ⟨fun _ => majBit, majBit, settlesValue_majWorld, surjOn_majBit, margin_majWorld⟩

/-! ### The recursive-majority block: margin that compounds with depth

The majority world above is the depth-one case of a family. Replace each of its three cells by a
whole majority block, recursively, `k` times: the result is a world on `3 ^ k` cells whose margin is
not `1` but `2 ^ k − 1`. That is the point of the construction — **redundancy composed with itself
buys margin exponential in the depth**, while the cell count grows exponentially too, at the larger
base `3`. Depth is what makes a block robust; the price is recorded elsewhere in this section
(`repair_tax`), and it is paid.

The pieces. `maj3` is majority-of-three on `Bool`. `decRec k` decodes a `3 ^ k`-cell block by
majority of its three sub-block decodes, splitting the index along `tripleEquiv`. `encRec k b` is
the codeword for `b` — and it is simply the **constant function**: triplicating a constant
recursively still writes `b` in every cell, so the encoder needs no recursion even though the
decoder does. There are exactly two codewords whatever the depth, so the block carries one bit.

**The healing radius** (`decRec_healing`): fewer than `2 ^ k` corrupted cells cannot change the
decode. The induction is the whole content. At depth `k + 1` a budget below
`2 ^ (k + 1) = 2 · 2 ^ k` is split three ways (`hammingDist_split`), and *at most one* sub-block
can be handed `2 ^ k` or more
— two would already exhaust the budget. The other two sub-blocks decode correctly by the inductive
hypothesis, and majority-of-three needs only two. Radii are stated as strict bounds
(`hammingDist … < 2 ^ k`) throughout, which is the same content as `≤ 2 ^ k − 1` with no truncated
subtraction anywhere in the arithmetic.

**The world is its own decoder** (`healWorld`): one step decodes and re-encodes. Within the healing
radius one step lands *exactly* on the codeword (`healWorld_heals`), and in fact **every** state
lands on a codeword after one step (`healWorld_mem_codewords`) — the map is idempotent
(`healWorld_idem`), its fixed points are exactly the two codewords (`healWorld_fixed_iff`), and its
recurrent core is exactly the codeword pair (`core_healWorld`). So the basin is the whole memory and
the transient is one step from anywhere, which is the strongest form the settling clause can take.
The decoded bit itself settles at once (`settlesValue_healWorld`, transient zero): it is invariant
under a single step, so the reading is right *before* the state has finished moving.

**The margin is exactly `2 ^ k − 1`** (`recMaj_margin_eq`). The lower bound is the healing radius
(`recMaj_hasMargin`, at every radius strictly below `2 ^ k`). The upper bound is a witness
(`recMaj_not_hasMargin`): `advRec k b` corrupts two of the three sub-blocks recursively, spends
exactly `2 ^ k` cells (`hammingDist_advRec`), and flips the decode (`decRec_advRec`) — majority
turned against itself. Nothing is left on the table, and `majority_margin` is this statement at
`k = 1`.

What this section deliberately does **not** do: price the healer. `decRec` is a decoder, not a code;
no `KE` bound on `healWorld` is claimed here, and none is needed for the margin, which is an
attribute of the dynamics alone (`HasMargin` mentions no observer). The combinatorics stands on its
own.

Anchors: [Persistence] §10.1 + §2. The recursive block is this development's; no numbered result of
[Persistence] is claimed machine-checked by its presence. -/

/-- **Majority of three** on `Bool`. -/
def maj3 (a b c : Bool) : Bool := (a && b) || (b && c) || (a && c)

@[simp] private theorem maj3_self (b : Bool) : maj3 b b b = b := by cases b <;> rfl

/-- Two agreeing votes carry the majority, wherever the third sits. -/
private theorem maj3_left_left (b z : Bool) : maj3 b b z = b := by cases b <;> cases z <;> rfl

private theorem maj3_left_right (b z : Bool) : maj3 b z b = b := by cases b <;> cases z <;> rfl

private theorem maj3_right_right (b z : Bool) : maj3 z b b = b := by cases b <;> cases z <;> rfl

/-- The index split of a depth-`(k+1)` block into three depth-`k` sub-blocks. -/
def tripleEquiv (k : ℕ) : Fin 3 × Fin (3 ^ k) ≃ Fin (3 ^ (k + 1)) :=
  finProdFinEquiv.trans (finCongr (by ring))

/-- The `c`-th depth-`k` sub-block of a depth-`(k+1)` block. -/
def subBlock (k : ℕ) (c : Fin 3) (x : Mem (Fin (3 ^ (k + 1))) Bool) :
    Mem (Fin (3 ^ k)) Bool :=
  fun i => x (tripleEquiv k (c, i))

/-- **The recursive-majority decoder**: majority of the three sub-block decodes, all the way
down. -/
def decRec : (k : ℕ) → Mem (Fin (3 ^ k)) Bool → Bool
  | 0, x => x ⟨0, by norm_num⟩
  | k + 1, x =>
      maj3 (decRec k (subBlock k 0 x)) (decRec k (subBlock k 1 x)) (decRec k (subBlock k 2 x))

/-- **The codeword for `b`**: the constant function. Triplicating a constant recursively writes `b`
in every cell, so — unlike the decoder — the encoder needs no recursion at all. Exactly two
codewords exist at every depth: the block carries one bit. -/
def encRec (k : ℕ) (b : Bool) : Mem (Fin (3 ^ k)) Bool := fun _ => b

@[simp] private theorem subBlock_encRec (k : ℕ) (c : Fin 3) (b : Bool) :
    subBlock k c (encRec (k + 1) b) = encRec k b := rfl

/-- **The roundtrip**: the decoder reads back what the encoder wrote. -/
@[simp] theorem decRec_encRec (k : ℕ) (b : Bool) : decRec k (encRec k b) = b := by
  induction k with
  | zero => rfl
  | succ k ih => rw [decRec]; simp only [subBlock_encRec, ih]; exact maj3_self b

/-- `hammingDist` as a sum of indicators — the counting form the block split needs. -/
private theorem hammingDist_eq_sum {ι : Type*} [Fintype ι] (x y : ι → Bool) :
    hammingDist x y = ∑ i, if x i ≠ y i then 1 else 0 := by
  rw [hammingDist, Finset.card_filter]

/-- **The three-way split**: a depth-`(k+1)` distance is the sum of its three sub-block distances.
Proved by counting through the index equivalence rather than by transporting `hammingDist`, which
has no reindexing lemma to transport along. This is what makes the healing induction a budget
argument. -/
theorem hammingDist_split (k : ℕ) (x y : Mem (Fin (3 ^ (k + 1))) Bool) :
    hammingDist x y = hammingDist (subBlock k 0 x) (subBlock k 0 y)
      + hammingDist (subBlock k 1 x) (subBlock k 1 y)
      + hammingDist (subBlock k 2 x) (subBlock k 2 y) := by
  rw [hammingDist_eq_sum, hammingDist_eq_sum, hammingDist_eq_sum, hammingDist_eq_sum]
  rw [← Equiv.sum_comp (tripleEquiv k) (fun i => if x i ≠ y i then 1 else 0)]
  rw [Fintype.sum_prod_type]
  rw [Fin.sum_univ_three]
  rfl

/-- **The healing radius**: fewer than `2 ^ k` corrupted cells cannot change the decode.

The induction is a budget argument. At depth `k + 1` the corruption is split three ways, and since
`2 ^ (k + 1) = 2 · 2 ^ k`, at most ONE sub-block can be handed `2 ^ k` cells or more — two would
already exhaust the budget. The remaining two decode correctly by the inductive hypothesis, and
majority-of-three needs only two votes. Depth `k` therefore corrects `2 ^ k − 1` errors on `3 ^ k`
cells: margin exponential in the depth. -/
theorem decRec_healing : ∀ (k : ℕ) (x : Mem (Fin (3 ^ k)) Bool) (b : Bool),
    hammingDist x (encRec k b) < 2 ^ k → decRec k x = b := by
  intro k
  induction k with
  | zero =>
      intro x b h
      have h1 : hammingDist x (encRec 0 b) < 1 := h
      rw [hammingDist_lt_one.mp h1]
      exact decRec_encRec 0 b
  | succ k ih =>
      intro x b h
      rw [hammingDist_split] at h
      simp only [subBlock_encRec] at h
      have hp : (2 : ℕ) ^ (k + 1) = 2 * 2 ^ k := by ring
      rw [hp] at h
      rw [decRec]
      by_cases h0 : hammingDist (subBlock k 0 x) (encRec k b) < 2 ^ k
      · by_cases h1 : hammingDist (subBlock k 1 x) (encRec k b) < 2 ^ k
        · rw [ih _ _ h0, ih _ _ h1]; exact maj3_left_left b _
        · have h2 : hammingDist (subBlock k 2 x) (encRec k b) < 2 ^ k := by omega
          rw [ih _ _ h0, ih _ _ h2]; exact maj3_left_right b _
      · have h1 : hammingDist (subBlock k 1 x) (encRec k b) < 2 ^ k := by omega
        have h2 : hammingDist (subBlock k 2 x) (encRec k b) < 2 ^ k := by omega
        rw [ih _ _ h1, ih _ _ h2]; exact maj3_right_right b _

/-- **The healer world**: one step decodes the block and re-encodes it. Like the majority world it
generalizes, it is its own decoder — the error correction is the dynamics, not an observer's
apparatus. -/
def healWorld (k : ℕ) : Mem (Fin (3 ^ k)) Bool → Mem (Fin (3 ^ k)) Bool :=
  fun x => encRec k (decRec k x)

private theorem healWorld_apply (k : ℕ) (x : Mem (Fin (3 ^ k)) Bool) :
    healWorld k x = encRec k (decRec k x) := rfl

/-- **One step lands exactly on the codeword**, from anywhere inside the healing radius: the
perturbed state does not merely stay readable, it is erased back to the codeword itself. -/
theorem healWorld_heals (k : ℕ) (x : Mem (Fin (3 ^ k)) Bool) (b : Bool)
    (h : hammingDist x (encRec k b) < 2 ^ k) : healWorld k x = encRec k b := by
  rw [healWorld_apply, decRec_healing k x b h]

/-- **Every** state is a codeword after one step — not only those near one. The basin is the whole
memory and the transient is one, which is the strongest form the settling clause can take. -/
theorem healWorld_mem_codewords (k : ℕ) (x : Mem (Fin (3 ^ k)) Bool) :
    ∃ b, healWorld k x = encRec k b := ⟨decRec k x, rfl⟩

/-- The decoded bit is what the healer world conserves. -/
@[simp] private theorem decRec_healWorld (k : ℕ) (x : Mem (Fin (3 ^ k)) Bool) :
    decRec k (healWorld k x) = decRec k x := by
  rw [healWorld_apply, decRec_encRec]

theorem healWorld_idem (k : ℕ) (x : Mem (Fin (3 ^ k)) Bool) :
    healWorld k (healWorld k x) = healWorld k x := by
  rw [healWorld_apply k (healWorld k x), decRec_healWorld]
  exact (healWorld_apply k x).symm

/-- The fixed points are exactly the two codewords. -/
theorem healWorld_fixed_iff (k : ℕ) (x : Mem (Fin (3 ^ k)) Bool) :
    healWorld k x = x ↔ ∃ b, x = encRec k b := by
  constructor
  · intro h; exact ⟨decRec k x, h.symm⟩
  · rintro ⟨b, rfl⟩; rw [healWorld_apply, decRec_encRec]

/-- **The recurrent core is the codeword pair.** One step lands in it from anywhere, and the world
is the identity there — the depth-`k` analogue of the majority world's consensus set. -/
theorem core_healWorld (k : ℕ) :
    core (healWorld k) = {x : Mem (Fin (3 ^ k)) Bool | ∃ b, x = encRec k b} := by
  ext x
  constructor
  · intro hx
    obtain ⟨y, -, hy⟩ : x ∈ ((healWorld k)^[1]) '' Set.univ := Set.mem_iInter.mp hx 1
    rw [Function.iterate_one] at hy
    subst hy
    exact healWorld_mem_codewords k y
  · rintro ⟨b, rfl⟩
    have hfix : healWorld k (encRec k b) = encRec k b :=
      (healWorld_fixed_iff k _).mpr ⟨b, rfl⟩
    exact Set.mem_iInter.mpr fun t => ⟨_, Set.mem_univ _, Function.iterate_fixed hfix t⟩

private theorem decRec_iterate (k t : ℕ) (x : Mem (Fin (3 ^ k)) Bool) :
    decRec k ((healWorld k)^[t] x) = decRec k x := by
  induction t with
  | zero => rfl
  | succ t ih => rw [Function.iterate_succ_apply', decRec_healWorld]; exact ih

/-- The decoded bit settles instantly along every orbit — transient zero, because one step does not
move it. The *state* reaches the attractor at step one; the *reading* is already right at step
zero. -/
theorem settlesValue_healWorld (k : ℕ) :
    SettlesValue (healWorld k) (fun _ => decRec k)
      (Set.univ : Set (Mem (Fin (3 ^ k)) Bool)) (decRec k) :=
  fun s _ => ⟨0, fun t _ => decRec_iterate k t s⟩

/-- Both bits are attained: the settled reading carries one full bit at every depth. -/
theorem surjOn_decRec (k : ℕ) :
    Set.SurjOn (decRec k) (Set.univ : Set (Mem (Fin (3 ^ k)) Bool)) Set.univ := by
  intro b _
  exact ⟨encRec k b, Set.mem_univ _, decRec_encRec k b⟩

/-- **The margin of the depth-`k` block**, at every radius strictly below `2 ^ k`: on the attractor
the state is a codeword, so a sub-radius perturbation is exactly the healing lemma's hypothesis. -/
theorem recMaj_hasMargin (k e : ℕ) (he : e < 2 ^ k) :
    HasMargin (healWorld k) (Set.univ : Set (Mem (Fin (3 ^ k)) Bool)) (decRec k) e := by
  intro s hs s' hs'
  refine ⟨Set.mem_univ _, ?_⟩
  rw [← core_eq_omegaLimit, core_healWorld] at hs
  obtain ⟨b, rfl⟩ := hs
  rw [mem_hball] at hs'
  rw [decRec_encRec]
  refine decRec_healing k s' b ?_
  rw [hammingDist_comm]
  omega

private theorem two_pow_le_three_pow (k : ℕ) : (2 : ℕ) ^ k ≤ 3 ^ k :=
  Nat.pow_le_pow_left (by norm_num) k

private theorem recMaj_le_margin (k e : ℕ) (he : e < 2 ^ k) :
    e ≤ margin (healWorld k) (Set.univ : Set (Mem (Fin (3 ^ k)) Bool)) (decRec k) := by
  refine le_margin ⟨?_, recMaj_hasMargin k e he⟩
  have h3 := two_pow_le_three_pow k
  simp only [Fintype.card_fin]
  omega

/-- The headline lower bound: margin at least `2 ^ k − 1` on `3 ^ k` cells, from a depth-`k` local
construction. The subtraction is harmless here — `2 ^ k` is positive — and it is the only place one
appears; the arithmetic above runs on strict bounds. -/
theorem recMaj_margin_ge (k : ℕ) :
    2 ^ k - 1 ≤ margin (healWorld k) (Set.univ : Set (Mem (Fin (3 ^ k)) Bool)) (decRec k) := by
  refine recMaj_le_margin k _ ?_
  have : 0 < (2 : ℕ) ^ k := Nat.two_pow_pos k
  omega

/-- **The adversarial pattern**: corrupt two of the three sub-blocks recursively, leaving the third
clean. It spends exactly `2 ^ k` cells and turns majority against itself. -/
def advRec : (k : ℕ) → Bool → Mem (Fin (3 ^ k)) Bool
  | 0, b => fun _ => !b
  | k + 1, b => fun p =>
      if ((tripleEquiv k).symm p).1 = 2 then b else advRec k b ((tripleEquiv k).symm p).2

private theorem subBlock_advRec_zero (k : ℕ) (b : Bool) :
    subBlock k 0 (advRec (k + 1) b) = advRec k b := by
  funext i; simp [subBlock, advRec, Equiv.symm_apply_apply]

private theorem subBlock_advRec_one (k : ℕ) (b : Bool) :
    subBlock k 1 (advRec (k + 1) b) = advRec k b := by
  funext i; simp [subBlock, advRec, Equiv.symm_apply_apply]

private theorem subBlock_advRec_two (k : ℕ) (b : Bool) :
    subBlock k 2 (advRec (k + 1) b) = encRec k b := by
  funext i; simp [subBlock, advRec, Equiv.symm_apply_apply, encRec]

/-- The pattern spends **exactly** the healing radius: two corrupted sub-blocks at `2 ^ k` each. -/
theorem hammingDist_advRec (k : ℕ) (b : Bool) :
    hammingDist (advRec k b) (encRec k b) = 2 ^ k := by
  induction k with
  | zero => cases b <;> decide
  | succ k ih =>
      rw [hammingDist_split, subBlock_advRec_zero, subBlock_advRec_one, subBlock_advRec_two,
        subBlock_encRec, subBlock_encRec, subBlock_encRec, ih, hammingDist_self]
      ring

/-- …and it flips the decode: two of three sub-blocks now vote the wrong way. -/
theorem decRec_advRec (k : ℕ) (b : Bool) : decRec k (advRec k b) = !b := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [decRec, subBlock_advRec_zero, subBlock_advRec_one, subBlock_advRec_two, ih,
        decRec_encRec]
      exact maj3_left_left (!b) b

/-- **Sharpness**: the margin fails at radius exactly `2 ^ k`. The healing radius is not an artefact
of the proof — one more cell than `2 ^ k − 1` genuinely breaks the block. -/
theorem recMaj_not_hasMargin (k : ℕ) :
    ¬ HasMargin (healWorld k) (Set.univ : Set (Mem (Fin (3 ^ k)) Bool)) (decRec k) (2 ^ k) := by
  intro h
  have hs : encRec k false
      ∈ omegaLimit (healWorld k) (Set.univ : Set (Mem (Fin (3 ^ k)) Bool)) := by
    rw [← core_eq_omegaLimit, core_healWorld]; exact ⟨false, rfl⟩
  have hb : advRec k false ∈ hball (2 ^ k) (encRec k false) := by
    rw [mem_hball, hammingDist_comm, hammingDist_advRec]
  have hcontra := (h _ hs _ hb).2
  rw [decRec_advRec, decRec_encRec] at hcontra
  exact Bool.noConfusion hcontra

/-- **The margin of the depth-`k` block is exactly `2 ^ k − 1`.** The healing radius gives the lower
bound and the adversarial pattern the upper: nothing is left on the table.

Read against `repair_tax`, this is what the tower costs. Depth `k` buys margin `2 ^ k − 1` and
spends `3 ^ k` cells to carry the same one bit that three cells carried at depth one — the margin
grows exponentially, and so does the tax. `majority_margin` is this statement at `k = 1`. -/
theorem recMaj_margin_eq (k : ℕ) :
    margin (healWorld k) (Set.univ : Set (Mem (Fin (3 ^ k)) Bool)) (decRec k) = 2 ^ k - 1 := by
  refine le_antisymm ?_ (recMaj_margin_ge k)
  by_contra hcon
  have hlt := Nat.not_le.mp hcon
  have hge : 2 ^ k ≤ margin (healWorld k) (Set.univ : Set (Mem (Fin (3 ^ k)) Bool)) (decRec k) := by
    have : 0 < (2 : ℕ) ^ k := Nat.two_pow_pos k
    omega
  exact recMaj_not_hasMargin k
    ((hasMargin_margin (healWorld k) Set.univ (decRec k)).mono hge)

/-- **The worked robust sub-system at depth `k`**: a settling family whose settled value is
surjective — one full bit — and whose robustness margin is exactly `2 ^ k − 1` cells on `3 ^ k`.
The depth-one case is `majority_margin`; compounding the construction compounds the margin. -/
theorem recMaj_margin (k : ℕ) :
    ∃ (ℓ : ℕ → Mem (Fin (3 ^ k)) Bool → Bool) (v : Mem (Fin (3 ^ k)) Bool → Bool),
      SettlesValue (healWorld k) ℓ Set.univ v ∧ Set.SurjOn v Set.univ Set.univ ∧
      margin (healWorld k) Set.univ v = 2 ^ k - 1 :=
  ⟨fun _ => decRec k, decRec k, settlesValue_healWorld k, surjOn_decRec k, recMaj_margin_eq k⟩

/-! ### The witness world: a lawful sub-system beside an arbitrary environment

Everything above is now assembled into one world. Take `κ` recursive-majority blocks of depth `k` —
the **habitat** — and let them run a macro law `G` on the `κ` bits they decode to; set that
beside an **environment** carrying an arbitrary update `π`, sharing nothing. The result,
`witnessWorld κ k G π`, is a world whose readable sub-system is exactly `(Bool ^ κ, G)`.

The cell structure is the point. A product of two memories is a memory on the disjoint union of
their indices (`sumMem`), so the whole world is a `Mem` on `(Fin κ × Fin (3 ^ k)) ⊕ ι_J` and
perturbations of it are counted in cells like any other — `hammingDist` splits across the two parts
(`hammingDist_sum_index`) exactly as it splits across a block's three sub-blocks.
`witnessWorld_conj` records that this world *is* the Cartesian product world of the
disjoint-union section, read through
that bridge; nothing new is being defined, only re-indexed onto cells.

**The square is exact and unconditional** (`witness_square`). `macroLens` decodes each block; the
habitat's update decodes, applies `G`, and re-encodes; and `decRec ∘ encRec = id` collapses the
composite to `G` in three lines. No hypothesis on the state is needed — not validity, not
proximity to a codeword — because the update writes codewords whatever it was handed. So the
sub-system's law holds *everywhere*, and by telescoping (`witnessLens_iterate`) the reading follows
`G`'s own trajectory from step **zero**, from every initial state, whatever the environment does.
That is the emergence clause in its strongest form: the basin is not merely large, it is everything,
and there is no transient in the reading at all. The *state* takes one step to become a codeword
state (`witnessWorld_valid_after_one`); the *reading* never needed to.

**The margin is the block's, and the environment is free** (`witnessWorld_hasMargin`, at every
radius strictly below `2 ^ k`). The reading ignores the environment's cells entirely, so however
many of them there are and however wildly `π` moves them, they neither add to the margin nor
subtract from it. `witnessWorld_rejoins` is the same fact along the whole orbit: a perturbed state
inside the radius does not merely recover eventually — its reading agrees with the unperturbed one
at *every* step. The rejoining is immediate.

**A domain caution, checked rather than assumed.** The healing hypothesis is distance to a
**codeword** habitat state, not distance between arbitrary states. Over arbitrary states the
"perturbation cannot change the decode" reading is false, and cheaply so: at `k = 1` the block
`(0,0,1)` decodes `false` and `(0,1,1)` decodes `true`, one cell apart with `1 < 2 ^ 1`. What is
true is `habitat_heals` — and it is what the margin needs, because `HasMargin` quantifies its base
state
over the attractor, and the attractor consists of codeword states
(`omegaLimit_witnessWorld_subset`).

**What is deliberately absent: a price.** The reading here is *lawful*, not settled — it moves, by
`G` — so `SettlesValue` is the wrong predicate for it and `Intertwines` is the right one;
`HasMargin` and `margin` apply verbatim either way, mentioning no observer and no settling. And no
`KE` bound on
this world is claimed: pricing a `Mem`-carrier world means tabulating it along an enumeration of its
`2 ^ (κ · 3 ^ k + #ι_J)` states, which this section does not build. The existence of the sub-system
is combinatorial and stands alone; what it costs an observer to own is a separate question, and a
separate construction.

Anchors: [Persistence] §10.1–§10.2 + §2 + §8. The construction is this development's; no numbered
result of [Persistence] is claimed machine-checked by its presence. -/

/-- **A product of memories is a memory on the disjoint union of their indices.** This is what gives
a two-part world a cell structure, so that perturbations of it are counted in cells. -/
def sumMem {ι₁ ι₂ V : Type*} : Mem ι₁ V × Mem ι₂ V ≃ Mem (ι₁ ⊕ ι₂) V :=
  (Equiv.sumArrowEquivProdArrow ι₁ ι₂ V).symm

@[simp] private theorem sumMem_apply {ι₁ ι₂ V : Type*} (p : Mem ι₁ V × Mem ι₂ V) :
    (sumMem p : Mem (ι₁ ⊕ ι₂) V) = Sum.elim p.1 p.2 := rfl

@[simp] private theorem sumMem_symm_apply {ι₁ ι₂ V : Type*} (x : Mem (ι₁ ⊕ ι₂) V) :
    sumMem.symm x = (x ∘ Sum.inl, x ∘ Sum.inr) := rfl

/-- **Distance splits across the two parts** — the disjoint-union analogue of the block split. -/
theorem hammingDist_sum_index {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂]
    (x y : Mem (ι₁ ⊕ ι₂) Bool) :
    hammingDist x y
      = hammingDist (x ∘ Sum.inl) (y ∘ Sum.inl) + hammingDist (x ∘ Sum.inr) (y ∘ Sum.inr) := by
  rw [hammingDist_eq_sum, hammingDist_eq_sum, hammingDist_eq_sum, Fintype.sum_sum_type]
  rfl

/-- The `i`-th depth-`k` block of a habitat state. -/
def blockOf {κ k : ℕ} (h : Mem (Fin κ × Fin (3 ^ k)) Bool) (i : Fin κ) :
    Mem (Fin (3 ^ k)) Bool := fun p => h (i, p)

/-- **The macro reading**: decode each block to its bit. This is the sub-system's lens. -/
def macroLens (κ k : ℕ) (h : Mem (Fin κ × Fin (3 ^ k)) Bool) : Mem (Fin κ) Bool :=
  fun i => decRec k (blockOf h i)

/-- **The habitat codeword** for a macro state: write each block's bit into every one of its
cells. -/
def habitatEnc (κ k : ℕ) (b : Mem (Fin κ) Bool) : Mem (Fin κ × Fin (3 ^ k)) Bool :=
  fun q => b q.1

/-- **The habitat world**: decode the blocks, apply the macro law once, re-encode cleanly. -/
def habitatWorld (κ k : ℕ) (G : Mem (Fin κ) Bool → Mem (Fin κ) Bool)
    (h : Mem (Fin κ × Fin (3 ^ k)) Bool) : Mem (Fin κ × Fin (3 ^ k)) Bool :=
  habitatEnc κ k (G (macroLens κ k h))

@[simp] private theorem blockOf_habitatEnc (κ k : ℕ) (b : Mem (Fin κ) Bool) (i : Fin κ) :
    blockOf (habitatEnc κ k b) i = encRec k (b i) := rfl

@[simp] theorem macroLens_habitatEnc (κ k : ℕ) (b : Mem (Fin κ) Bool) :
    macroLens κ k (habitatEnc κ k b) = b := by
  funext i; rw [macroLens, blockOf_habitatEnc, decRec_encRec]

/-- The habitat distance is the sum of its blocks' distances. -/
theorem hammingDist_habitat_blocks (κ k : ℕ) (h h' : Mem (Fin κ × Fin (3 ^ k)) Bool) :
    hammingDist h h' = ∑ i : Fin κ, hammingDist (blockOf h i) (blockOf h' i) := by
  rw [hammingDist_eq_sum, Fintype.sum_prod_type]
  exact Finset.sum_congr rfl fun i _ => (hammingDist_eq_sum _ _).symm

/-- …so a total budget bounds every single block's share of it. -/
private theorem hammingDist_blockOf_le (κ k : ℕ) (h h' : Mem (Fin κ × Fin (3 ^ k)) Bool)
    (i : Fin κ) : hammingDist (blockOf h i) (blockOf h' i) ≤ hammingDist h h' := by
  rw [hammingDist_habitat_blocks]
  exact Finset.single_le_sum
    (f := fun j => hammingDist (blockOf h j) (blockOf h' j))
    (fun j _ => Nat.zero_le _) (Finset.mem_univ i)

/-- **The habitat heals**: fewer than `2 ^ k` corrupted cells of a **codeword** habitat state leave
the macro reading unchanged — a total budget below the block's healing radius leaves every block
below it, and each block then heals on its own.

The reference point must be a codeword, and the hypothesis says so. Between arbitrary states the
claim is false at every depth: at `k = 1` the blocks `(0,0,1)` and `(0,1,1)` are one cell apart —
well inside `2 ^ 1` — and decode to opposite bits. Majority forgets corruption of a codeword, not
disagreement between two arbitrary states. -/
theorem habitat_heals (κ k : ℕ) (b : Mem (Fin κ) Bool) (h' : Mem (Fin κ × Fin (3 ^ k)) Bool)
    (hd : hammingDist (habitatEnc κ k b) h' < 2 ^ k) : macroLens κ k h' = b := by
  funext i
  refine decRec_healing k (blockOf h' i) (b i) ?_
  have hle := hammingDist_blockOf_le κ k (habitatEnc κ k b) h' i
  rw [blockOf_habitatEnc] at hle
  rw [hammingDist_comm]
  omega

/-- One step from a perturbed codeword state is the step from the codeword itself: the habitat
forgets the perturbation entirely. -/
theorem habitatWorld_forgets (κ k : ℕ) (G : Mem (Fin κ) Bool → Mem (Fin κ) Bool)
    (b : Mem (Fin κ) Bool) (h' : Mem (Fin κ × Fin (3 ^ k)) Bool)
    (hd : hammingDist (habitatEnc κ k b) h' < 2 ^ k) :
    habitatWorld κ k G h' = habitatWorld κ k G (habitatEnc κ k b) := by
  rw [habitatWorld, habitatWorld, habitat_heals κ k b h' hd, macroLens_habitatEnc]

/-- The macro reading is onto: every macro state is written by its codeword. -/
theorem macroLens_surjective (κ k : ℕ) : Function.Surjective (macroLens κ k) :=
  fun b => ⟨habitatEnc κ k b, macroLens_habitatEnc κ k b⟩

/-- **The exact square on the habitat**, with no hypothesis on the state: the update writes
codewords whatever it was handed, and the decoder reads them back. -/
theorem macro_square (κ k : ℕ) (G : Mem (Fin κ) Bool → Mem (Fin κ) Bool)
    (h : Mem (Fin κ × Fin (3 ^ k)) Bool) :
    macroLens κ k (habitatWorld κ k G h) = G (macroLens κ k h) := by
  rw [habitatWorld, macroLens_habitatEnc]

theorem intertwines_macroLens (κ k : ℕ) (G : Mem (Fin κ) Bool → Mem (Fin κ) Bool) :
    Intertwines (habitatWorld κ k G) G (fun _ => macroLens κ k) :=
  fun _ h => macro_square κ k G h

section Witness

variable {ι_J : Type*}

/-- **The witness world**: `κ` depth-`k` blocks running the macro law `G`, beside an environment
running an arbitrary `π`, sharing nothing. A `Mem` on the disjoint union of the two indices, so its
perturbations are counted in cells. -/
def witnessWorld (κ k : ℕ) (G : Mem (Fin κ) Bool → Mem (Fin κ) Bool)
    (π : Mem ι_J Bool → Mem ι_J Bool) :
    Mem ((Fin κ × Fin (3 ^ k)) ⊕ ι_J) Bool → Mem ((Fin κ × Fin (3 ^ k)) ⊕ ι_J) Bool :=
  fun x => Sum.elim (habitatWorld κ k G (x ∘ Sum.inl)) (π (x ∘ Sum.inr))

/-- **The witness world's reading**: the macro state of its habitat. It does not look at the
environment at all — which is what makes the environment free. -/
def witnessLens (κ k : ℕ) (x : Mem ((Fin κ × Fin (3 ^ k)) ⊕ ι_J) Bool) : Mem (Fin κ) Bool :=
  macroLens κ k (x ∘ Sum.inl)

/-- The witness world **is** the Cartesian product world of the disjoint-union section, read through
the cell bridge: nothing new is defined here, only re-indexed onto cells. -/
theorem witnessWorld_conj (κ k : ℕ) (G : Mem (Fin κ) Bool → Mem (Fin κ) Bool)
    (π : Mem ι_J Bool → Mem ι_J Bool) :
    witnessWorld κ k G π = sumMem ∘ prodWorld (habitatWorld κ k G) π ∘ sumMem.symm := by
  funext x
  rfl

@[simp] private theorem witnessWorld_inl (κ k : ℕ) (G : Mem (Fin κ) Bool → Mem (Fin κ) Bool)
    (π : Mem ι_J Bool → Mem ι_J Bool) (x : Mem ((Fin κ × Fin (3 ^ k)) ⊕ ι_J) Bool) :
    (witnessWorld κ k G π x) ∘ Sum.inl = habitatWorld κ k G (x ∘ Sum.inl) := rfl

/-- **The exact square for the full world**: the reading obeys the macro law at every state,
whatever the environment is doing beside it. -/
theorem witness_square (κ k : ℕ) (G : Mem (Fin κ) Bool → Mem (Fin κ) Bool)
    (π : Mem ι_J Bool → Mem ι_J Bool) (x : Mem ((Fin κ × Fin (3 ^ k)) ⊕ ι_J) Bool) :
    witnessLens κ k (witnessWorld κ k G π x) = G (witnessLens κ k x) := by
  rw [witnessLens, witnessWorld_inl, witnessLens, macro_square]

theorem intertwines_witnessLens (κ k : ℕ) (G : Mem (Fin κ) Bool → Mem (Fin κ) Bool)
    (π : Mem ι_J Bool → Mem ι_J Bool) :
    Intertwines (witnessWorld κ k G π) G (fun _ => witnessLens κ k) :=
  fun _ x => witness_square κ k G π x

/-- The reading carries a full `κ`-bit macro state. -/
theorem witnessLens_surjective (κ k : ℕ) [Nonempty (Mem ι_J Bool)] :
    Function.Surjective (witnessLens (ι_J := ι_J) κ k) := by
  intro b
  exact ⟨Sum.elim (habitatEnc κ k b) (Classical.arbitrary (Mem ι_J Bool)),
    by rw [witnessLens]; exact macroLens_habitatEnc κ k b⟩

/-- The attractor consists of habitat-codeword states — which is why the margin's base state is
always one, and why `habitat_heals`'s codeword hypothesis is no restriction where it is used. -/
theorem omegaLimit_witnessWorld_subset (κ k : ℕ) (G : Mem (Fin κ) Bool → Mem (Fin κ) Bool)
    (π : Mem ι_J Bool → Mem ι_J Bool) :
    omegaLimit (witnessWorld κ k G π) Set.univ
      ⊆ {x : Mem ((Fin κ × Fin (3 ^ k)) ⊕ ι_J) Bool | ∃ b, x ∘ Sum.inl = habitatEnc κ k b} := by
  intro x hx
  obtain ⟨y, -, hy⟩ : x ∈ ((witnessWorld κ k G π)^[1]) '' Set.univ := Set.mem_iInter.mp hx 1
  rw [Function.iterate_one] at hy
  subst hy
  exact ⟨G (macroLens κ k (y ∘ Sum.inl)), rfl⟩

/-- **The margin of the full world is the block's**, at every radius strictly below `2 ^ k` —
however large the environment beside it, and whatever that environment does. The reading ignores
the
environment's cells, so they neither add to the margin nor subtract from it. -/
theorem witnessWorld_hasMargin [Fintype ι_J] (κ k : ℕ) (G : Mem (Fin κ) Bool → Mem (Fin κ) Bool)
    (π : Mem ι_J Bool → Mem ι_J Bool) (e : ℕ) (he : e < 2 ^ k) :
    HasMargin (witnessWorld κ k G π) (Set.univ : Set (Mem ((Fin κ × Fin (3 ^ k)) ⊕ ι_J) Bool))
      (witnessLens κ k) e := by
  intro s hs s' hs'
  refine ⟨Set.mem_univ _, ?_⟩
  obtain ⟨b, hb⟩ := omegaLimit_witnessWorld_subset κ k G π hs
  rw [mem_hball, hammingDist_sum_index] at hs'
  rw [witnessLens, witnessLens, hb]
  rw [macroLens_habitatEnc]
  refine habitat_heals κ k b (s' ∘ Sum.inl) ?_
  rw [← hb]
  omega

/-- **Emergence in its strongest form**: from EVERY initial state and every environment, the reading
follows the macro law's own trajectory — from step zero, with no hypothesis on the state whatever.
The basin is not merely large; it is everything, and the reading has no transient at all. -/
theorem witnessLens_iterate (κ k : ℕ) (G : Mem (Fin κ) Bool → Mem (Fin κ) Bool)
    (π : Mem ι_J Bool → Mem ι_J Bool) (t : ℕ)
    (x : Mem ((Fin κ × Fin (3 ^ k)) ⊕ ι_J) Bool) :
    witnessLens κ k ((witnessWorld κ k G π)^[t] x) = G^[t] (witnessLens κ k x) :=
  (intertwines_witnessLens κ k G π).iterate t x

/-- The *state* becomes a codeword state after one step, from anywhere — while the *reading* was
already lawful at step zero. -/
theorem witnessWorld_valid_after_one (κ k : ℕ) (G : Mem (Fin κ) Bool → Mem (Fin κ) Bool)
    (π : Mem ι_J Bool → Mem ι_J Bool) (x : Mem ((Fin κ × Fin (3 ^ k)) ⊕ ι_J) Bool) :
    ∃ b, (witnessWorld κ k G π x) ∘ Sum.inl = habitatEnc κ k b :=
  ⟨G (macroLens κ k (x ∘ Sum.inl)), rfl⟩

/-- **The perturbed orbit rejoins the macro-trajectory immediately**: a perturbation inside the
healing radius does not merely wash out eventually — the two readings agree at *every* step. -/
theorem witnessWorld_rejoins [Fintype ι_J] (κ k : ℕ) (G : Mem (Fin κ) Bool → Mem (Fin κ) Bool)
    (π : Mem ι_J Bool → Mem ι_J Bool) (b : Mem (Fin κ) Bool)
    (x x' : Mem ((Fin κ × Fin (3 ^ k)) ⊕ ι_J) Bool)
    (hx : x ∘ Sum.inl = habitatEnc κ k b) (hd : hammingDist x x' < 2 ^ k) (t : ℕ) :
    witnessLens κ k ((witnessWorld κ k G π)^[t] x')
      = witnessLens κ k ((witnessWorld κ k G π)^[t] x) := by
  rw [witnessLens_iterate, witnessLens_iterate]
  congr 1
  rw [witnessLens, witnessLens, hx, macroLens_habitatEnc]
  refine habitat_heals κ k b (x' ∘ Sum.inl) ?_
  rw [← hx]
  rw [hammingDist_sum_index] at hd
  omega

/-- The margin in numeric form: at least `2 ^ k − 1` cells, on a memory of `κ · 3 ^ k` habitat cells
beside however many environment cells. A nonempty habitat is what makes the radius fit inside the
memory. -/
theorem witnessWorld_margin_ge [Fintype ι_J] (κ k : ℕ)
    (G : Mem (Fin κ) Bool → Mem (Fin κ) Bool) (π : Mem ι_J Bool → Mem ι_J Bool) (hκ : 0 < κ) :
    2 ^ k - 1 ≤ margin (witnessWorld κ k G π)
      (Set.univ : Set (Mem ((Fin κ × Fin (3 ^ k)) ⊕ ι_J) Bool)) (witnessLens κ k) := by
  refine le_margin ⟨?_, witnessWorld_hasMargin κ k G π _ (by have := Nat.two_pow_pos k; omega)⟩
  have h23 := two_pow_le_three_pow k
  have hk : (3 : ℕ) ^ k ≤ κ * 3 ^ k := Nat.le_mul_of_pos_left _ hκ
  simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
  omega

/-- **The witness world hosts its sub-system.** A surjective reading — one full bit per block —
obeying the macro law `G` EXACTLY at every step from every initial state, and robust to any
perturbation of fewer than `2 ^ k` cells: however large the environment standing beside it, and
whatever that environment does.

This is the existence half of the construction, and it is unconditional in `κ`, `k`, `G` and `π`.
What such a sub-system costs an observer to own is not settled here. -/
theorem witness_world_hosts [Fintype ι_J] [Nonempty (Mem ι_J Bool)] (κ k : ℕ)
    (G : Mem (Fin κ) Bool → Mem (Fin κ) Bool) (π : Mem ι_J Bool → Mem ι_J Bool) :
    Function.Surjective (witnessLens (ι_J := ι_J) κ k) ∧
      Intertwines (witnessWorld κ k G π) G (fun _ => witnessLens κ k) ∧
      ∀ e < 2 ^ k, HasMargin (witnessWorld κ k G π) Set.univ (witnessLens κ k) e :=
  ⟨witnessLens_surjective κ k, intertwines_witnessLens κ k G π,
    fun e he => witnessWorld_hasMargin κ k G π e he⟩

end Witness

/-! ### The pricing bridge: memories as numerals

Everything above about the witness world is combinatorial, and lives where it should — on the
cell-structured memory `Mem ι V`, where a perturbation is a number of cells. The pricing
machinery of this development lives somewhere else: on `Fin n` carriers, where `n` counts *states*,
because that is what a table is indexed by. A memory of `N` cells has `2 ^ N` states, so the two
layers do not meet on their own.

This section is the bridge, and it is deliberately one bridge. `stateEquiv N` packs a memory state
into the numeral its cells spell, and `packWorld` transports any `Mem`-carrier world along it. The
whole existing pricing stack — `lensTable`, `lensCode`, `KE`, `UniformBudget`, the capacities — then
applies to the packed world verbatim, with nothing duplicated on the memory side.

**The endianness is fixed here, once.** Cell `i` carries weight `2 ^ i`: cell `0` is the low bit,
little-endian, so a packed state is `∑ᵢ (cell i) · 2 ^ i`. This is the same convention as
`packMarks`, the pricing layer's other numeral, and the same as Mathlib's `finFunctionFinEquiv`
through which it is built — so `stateEquiv_digit` is `sum_digits_div_mod` at base two, reusing the
digit lemma the marking price already runs on. Nothing below re-derives it, and nothing should
revisit the choice.

The transport laws are what make the bridge usable rather than merely definable: packing respects
composition (`packWorld_comp`), identity, and iteration (`packWorld_iterate`), so an orbit upstairs
is an orbit downstairs; an invertible world packs to a genuine permutation (`packPerm`), which is
what the `Perm`-carrier results require; and a lawful reading stays lawful (`packWorld_square`), so
an intertwining square survives the crossing intact.

What this section does **not** do is price anything yet. It makes the witness world *expressible* in
the pricing vocabulary; exhibiting a short program for its table is a separate construction, and it
needs a numeral-level decoder that this section does not build.

Anchors: [Persistence] §2 + §5. The bridge is this development's; no numbered result of
[Persistence] is claimed machine-checked by its presence. -/

/-- **The canonical packing**: a memory state is the numeral its cells spell, cell `i` carrying
weight `2 ^ i` — cell `0` is the low bit. Built from Mathlib's `finFunctionFinEquiv`, whose
convention this is, and shared with `packMarks`. -/
def stateEquiv (N : ℕ) : Mem (Fin N) Bool ≃ Fin (2 ^ N) :=
  (Equiv.arrowCongr (Equiv.refl (Fin N)) finTwoEquiv.symm).trans finFunctionFinEquiv

theorem stateEquiv_val {N : ℕ} (x : Mem (Fin N) Bool) :
    ((stateEquiv N x : Fin (2 ^ N)) : ℕ) = ∑ i : Fin N, (if x i then 1 else 0) * 2 ^ (i : ℕ) := by
  rw [stateEquiv]
  simp only [Equiv.trans_apply, Equiv.arrowCongr_apply, Equiv.refl_symm, Equiv.coe_refl,
    Function.comp_def, id_eq, finFunctionFinEquiv_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  cases h : x i <;> simp [finTwoEquiv]

/-- The `j`-th binary digit of a memory state, in the shape `sum_digits_div_mod` consumes. -/
private def bitDigit {N : ℕ} (x : Mem (Fin N) Bool) (j : ℕ) : ℕ :=
  if h : j < N then (if x ⟨j, h⟩ then 1 else 0) else 0

private theorem bitDigit_lt {N : ℕ} (x : Mem (Fin N) Bool) (j : ℕ) : bitDigit x j < 2 := by
  rw [bitDigit]; split
  · split <;> norm_num
  · norm_num

private theorem stateEquiv_val_range {N : ℕ} (x : Mem (Fin N) Bool) :
    ((stateEquiv N x : Fin (2 ^ N)) : ℕ) = ∑ j ∈ Finset.range N, bitDigit x j * 2 ^ j := by
  rw [stateEquiv_val, Finset.sum_range fun j => bitDigit x j * 2 ^ j]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [bitDigit]
  simp

/-- **Digit extraction**: bit `i` of a packed state is cell `i`. This is the marking price's own
digit lemma at base two — the two numerals of the pricing layer share a convention and a proof. -/
theorem stateEquiv_digit {N : ℕ} (x : Mem (Fin N) Bool) (i : Fin N) :
    ((stateEquiv N x : Fin (2 ^ N)) : ℕ) / 2 ^ (i : ℕ) % 2 = if x i then 1 else 0 := by
  rw [stateEquiv_val_range,
    sum_digits_div_mod (n := 2) (by norm_num) N (bitDigit x) (bitDigit_lt x) i i.2, bitDigit]
  simp

/-- **A memory world, priced**: transported along the packing onto the `Fin (2 ^ N)` carrier the
tables are indexed by. Every `KE`, `UniformBudget` and capacity statement of this development
applies to `packWorld U` verbatim. -/
def packWorld {N : ℕ} (U : Mem (Fin N) Bool → Mem (Fin N) Bool) : Fin (2 ^ N) → Fin (2 ^ N) :=
  fun s => stateEquiv N (U ((stateEquiv N).symm s))

@[simp] private theorem packWorld_apply {N : ℕ} (U : Mem (Fin N) Bool → Mem (Fin N) Bool)
    (x : Mem (Fin N) Bool) : packWorld U (stateEquiv N x) = stateEquiv N (U x) := by
  rw [packWorld, Equiv.symm_apply_apply]

theorem packWorld_comp {N : ℕ} (U₁ U₂ : Mem (Fin N) Bool → Mem (Fin N) Bool) :
    packWorld (U₁ ∘ U₂) = packWorld U₁ ∘ packWorld U₂ := by
  funext s
  obtain ⟨x, rfl⟩ := (stateEquiv N).surjective s
  simp [Function.comp_def]

theorem packWorld_id {N : ℕ} : packWorld (id : Mem (Fin N) Bool → Mem (Fin N) Bool) = id := by
  funext s
  obtain ⟨x, rfl⟩ := (stateEquiv N).surjective s
  simp

/-- **Orbits survive the crossing**: `t` steps upstairs are `t` steps downstairs. -/
theorem packWorld_iterate {N : ℕ} (U : Mem (Fin N) Bool → Mem (Fin N) Bool) (t : ℕ) :
    (packWorld U)^[t] = packWorld (U^[t]) := by
  induction t with
  | zero => rw [Function.iterate_zero, Function.iterate_zero, packWorld_id]
  | succ t ih =>
      funext s
      obtain ⟨x, rfl⟩ := (stateEquiv N).surjective s
      rw [Function.iterate_succ_apply, packWorld_apply, ih, packWorld_apply, packWorld_apply,
        Function.iterate_succ_apply]

/-- An invertible memory world packs to a genuine permutation — which is what the `Perm`-carrier
results ask for. -/
def packPerm {N : ℕ} (U : Equiv.Perm (Mem (Fin N) Bool)) : Equiv.Perm (Fin (2 ^ N)) :=
  Equiv.permCongr (stateEquiv N) U

theorem packPerm_coe {N : ℕ} (U : Equiv.Perm (Mem (Fin N) Bool)) :
    ⇑(packPerm U) = packWorld ⇑U := by
  funext s
  rw [packPerm, packWorld, Equiv.permCongr_apply]

/-- A reading between memories, transported to the carrier its table is indexed by. -/
def packLens {N M : ℕ} (ℓ : Mem (Fin N) Bool → Mem (Fin M) Bool) : Fin (2 ^ N) → Fin (2 ^ M) :=
  fun s => stateEquiv M (ℓ ((stateEquiv N).symm s))

@[simp] private theorem packLens_apply {N M : ℕ} (ℓ : Mem (Fin N) Bool → Mem (Fin M) Bool)
    (x : Mem (Fin N) Bool) : packLens ℓ (stateEquiv N x) = stateEquiv M (ℓ x) := by
  rw [packLens, Equiv.symm_apply_apply]

theorem packLens_surjective {N M : ℕ} {ℓ : Mem (Fin N) Bool → Mem (Fin M) Bool}
    (h : Function.Surjective ℓ) : Function.Surjective (packLens ℓ) := by
  intro v
  obtain ⟨y, hy⟩ := (stateEquiv M).surjective v
  obtain ⟨x, hx⟩ := h y
  exact ⟨stateEquiv N x, by rw [packLens_apply, hx, hy]⟩

/-- **A lawful reading stays lawful**: the intertwining square survives the crossing intact, so a
sub-system upstairs is a sub-system downstairs, with the same law. -/
theorem packWorld_square {N M : ℕ} {U : Mem (Fin N) Bool → Mem (Fin N) Bool}
    {F : Mem (Fin M) Bool → Mem (Fin M) Bool} {ℓ : Mem (Fin N) Bool → Mem (Fin M) Bool}
    (h : ∀ x, ℓ (U x) = F (ℓ x)) (s : Fin (2 ^ N)) :
    packLens ℓ (packWorld U s) = packWorld F (packLens ℓ s) := by
  obtain ⟨x, rfl⟩ := (stateEquiv N).surjective s
  rw [packWorld_apply, packLens_apply, packLens_apply, packWorld_apply, h]

/-! ### The bottom-up anchor: the majority tree read from the other end

`decRec` recurses **top-down**: it splits a depth-`(k+1)` block into three depth-`k` sub-blocks and
takes the majority of their decodes. Reading `tripleEquiv`, the sub-block index is the block's
**most-significant** base-3 digit — sub-block `c` occupies the positions `i + 3 ^ k · c`.

There is another order. Collapse the **least-significant** digit first: replace each adjacent triple
of cells `3j, 3j+1, 3j+2` by its majority, leaving a depth-`k` block, and decode that. That is
`reduceBot`, and `decRec_bottomUp` says the two orders agree — as they must, since both evaluate the
same ternary majority tree, one from the root and one from the leaves.

Why it is worth proving rather than observing. The two orders are not interchangeable *as
recursions*. Top-down makes **three** recursive calls, on three different sub-blocks; bottom-up
makes **one**, on a single reduced block. A recursion with one call and a shrinking argument is what
primitive recursion offers, so the bottom-up order is the one a numeral-level decoder can follow —
and `decRec_bottomUp` is what licenses reading the tree that way without changing what it computes.

The whole proof is one lemma. `subBlock_reduceBot` says **top blocks commute with the bottom
reduction**: collapsing the bottom digit and then taking sub-block `c` is taking sub-block `c` and
then collapsing. That is a statement about index arithmetic and nothing else —
`3 · (i + 3 ^ k · c) + r = (3 · i + r) + 3 ^ (k+1) · c` — and it is where all of the arithmetic
lives, deliberately isolated. Given it, the anchor is an induction whose base case is `maj3` itself
and whose step is the inductive hypothesis followed by the commutation.

Anchors: [Persistence] §2 + §5. The reformulation is this development's; no numbered result of
[Persistence] is claimed machine-checked by its presence. -/

/-- The value of `tripleEquiv`: sub-block index `c` is the **most-significant** base-3 digit, at
weight `3 ^ k`, and the position within the sub-block is the remainder. -/
theorem tripleEquiv_val (k : ℕ) (c : Fin 3) (i : Fin (3 ^ k)) :
    ((tripleEquiv k (c, i) : Fin (3 ^ (k + 1))) : ℕ) = (i : ℕ) + 3 ^ k * (c : ℕ) := by
  rw [tripleEquiv]
  simp [finProdFinEquiv_apply_val]

private theorem reduceBot_bound {k : ℕ} (j : Fin (3 ^ k)) (r : ℕ) (hr : r < 3) :
    3 * (j : ℕ) + r < 3 ^ (k + 1) := by
  have hj := j.2
  have h3 : (3 : ℕ) ^ (k + 1) = 3 * 3 ^ k := by ring
  omega

/-- **The bottom reduction**: collapse the **least-significant** base-3 digit — output cell `j` is
the majority of the input's adjacent triple `3j`, `3j+1`, `3j+2`. -/
def reduceBot (k : ℕ) (x : Mem (Fin (3 ^ (k + 1))) Bool) : Mem (Fin (3 ^ k)) Bool :=
  fun j => maj3 (x ⟨3 * (j : ℕ), reduceBot_bound j 0 (by norm_num)⟩)
                (x ⟨3 * (j : ℕ) + 1, reduceBot_bound j 1 (by norm_num)⟩)
                (x ⟨3 * (j : ℕ) + 2, reduceBot_bound j 2 (by norm_num)⟩)

/-- **Top blocks commute with the bottom reduction.** The key lemma, and the only place the index
arithmetic lives: taking sub-block `c` after collapsing the bottom digit is collapsing after taking
sub-block `c`, because `3 · (i + 3 ^ k · c) + r = (3 · i + r) + 3 ^ (k+1) · c`. -/
theorem subBlock_reduceBot (k : ℕ) (c : Fin 3) (x : Mem (Fin (3 ^ (k + 2))) Bool) :
    subBlock k c (reduceBot (k + 1) x) = reduceBot k (subBlock (k + 1) c x) := by
  funext i
  have key : ∀ (r : ℕ) (hr : r < 3),
      3 * ((tripleEquiv k (c, i) : Fin (3 ^ (k + 1))) : ℕ) + r
        = ((tripleEquiv (k + 1) (c, ⟨3 * (i : ℕ) + r, reduceBot_bound i r hr⟩)
              : Fin (3 ^ (k + 2))) : ℕ) := by
    intro r hr
    rw [tripleEquiv_val, tripleEquiv_val]
    change 3 * ((i : ℕ) + 3 ^ k * (c : ℕ)) + r = (3 * (i : ℕ) + r) + 3 ^ (k + 1) * (c : ℕ)
    rw [pow_succ]
    ring
  simp only [subBlock, reduceBot]
  congr 1
  · exact congrArg x (Fin.ext (key 0 (by norm_num)))
  · exact congrArg x (Fin.ext (key 1 (by norm_num)))
  · exact congrArg x (Fin.ext (key 2 (by norm_num)))

/-- **The anchor**: decoding a depth-`(k+1)` block top-down equals collapsing its bottom digit and
decoding the depth-`k` block that remains. Both orders evaluate the same ternary majority tree — one
from the root, one from the leaves.

This is what licenses a decoder that recurses **once** per level instead of three times: the
bottom-up order is the shape primitive recursion offers, and this says nothing is lost by taking
it. -/
theorem decRec_bottomUp : ∀ (k : ℕ) (x : Mem (Fin (3 ^ (k + 1))) Bool),
    decRec (k + 1) x = decRec k (reduceBot k x) := by
  intro k
  induction k with
  | zero => intro x; rfl
  | succ k ih =>
      intro x
      rw [decRec]
      rw [ih (subBlock (k + 1) 0 x), ih (subBlock (k + 1) 1 x), ih (subBlock (k + 1) 2 x)]
      rw [← subBlock_reduceBot k 0 x, ← subBlock_reduceBot k 1 x, ← subBlock_reduceBot k 2 x]
      rw [decRec]

/-! ### The numeral decoder: `decRec` computed on packed states

The anchor says a depth-`k` decode is `k` bottom collapses followed by reading one cell. This
section carries that loop across to numerals, where the pricing layer works.

**Majority is halving.** For bits, `maj3` is `(a + b + c) / 2`: the sum lands in `{0,1,2,3}` and
halving sends it to `{0,0,1,1}`, which is exactly the majority. `maj3_natBit` is that identity,
checked on all eight cases. It is what keeps everything below `ℕ`-valued, with no `Bool` in the
arithmetic.

**One level, one square.** `packReduce m` collapses a numeral's bit-triples by the `ℕ`-majority, and
`packReduce_stateEquiv` says it agrees with `reduceBot` through the packing. The proof is term-wise
and has no induction in it: both sides are `∑ j ∈ range (3 ^ k), d j · 2 ^ j`, the left by
definition and the right by `stateEquiv_val_range`, and `stateEquiv_digit` identifies each bit of
the packed state with the cell it came from. This is the *only* place the memory/numeral boundary is
crossed, and it is crossed at the simplest statement available — one level, no recursion.

**The loop.** `numDecRec` collapses `k` times and reads the low bit: **one** recursive call per
level, which is what `decRec_bottomUp` licenses and what primitive recursion can follow.
`numDecRec_stateEquiv` is the bridge, and each induction step is exactly two rewrites — the square
of this section, then the anchor of the last. Nothing else enters.

The decoder is a `ℕ → ℕ → ℕ` function here; a program computing it, and the habitat table built from
one, are the next construction.

Anchors: [Persistence] §2 + §5. The decoder is this development's; no numbered result of
[Persistence] is claimed machine-checked by its presence. -/

/-- **Majority of three bits is halving their sum**: the sum lands in `{0,1,2,3}` and `/ 2` sends it
to `{0,0,1,1}`. Checked on all eight cases, and it is what keeps the numeral arithmetic below free
of `Bool`. -/
theorem maj3_natBit (a b c : Bool) :
    (if maj3 a b c then 1 else 0 : ℕ)
      = ((if a then 1 else 0) + (if b then 1 else 0) + (if c then 1 else 0) : ℕ) / 2 := by
  revert a b c; decide

/-- Bit `j` of a numeral. -/
def numBitN (s j : ℕ) : ℕ := s / 2 ^ j % 2

/-- **The numeral form of `reduceBot`**: output digit `j` is the majority of the input's bit-triple
`3j, 3j+1, 3j+2`, taken as a halved sum. -/
def packReduce (m s : ℕ) : ℕ :=
  ∑ j ∈ Finset.range m,
    ((numBitN s (3 * j) + numBitN s (3 * j + 1) + numBitN s (3 * j + 2)) / 2) * 2 ^ j

private theorem numBitN_stateEquiv {N : ℕ} (x : Mem (Fin N) Bool) (j : ℕ) (hj : j < N) :
    numBitN ((stateEquiv N x : Fin (2 ^ N)) : ℕ) j = if x ⟨j, hj⟩ then 1 else 0 := by
  rw [numBitN]
  exact stateEquiv_digit x ⟨j, hj⟩

/-- **The one-level square**: reducing the numeral is packing the reduced memory.

Term-wise, with no induction: both sides are `∑ j ∈ range (3 ^ k), d j · 2 ^ j`, and
`stateEquiv_digit` identifies each bit of the packed state with the cell it came from. This is
the only crossing of the memory/numeral boundary, made at the simplest statement there is. -/
theorem packReduce_stateEquiv (k : ℕ) (x : Mem (Fin (3 ^ (k + 1))) Bool) :
    packReduce (3 ^ k) ((stateEquiv (3 ^ (k + 1)) x : Fin (2 ^ 3 ^ (k + 1))) : ℕ)
      = ((stateEquiv (3 ^ k) (reduceBot k x) : Fin (2 ^ 3 ^ k)) : ℕ) := by
  conv_rhs => rw [stateEquiv_val_range]
  rw [packReduce]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjk : j < 3 ^ k := Finset.mem_range.mp hj
  have h3 : (3 : ℕ) ^ (k + 1) = 3 * 3 ^ k := by ring
  have hb0 : 3 * j < 3 ^ (k + 1) := by omega
  have hb1 : 3 * j + 1 < 3 ^ (k + 1) := by omega
  have hb2 : 3 * j + 2 < 3 ^ (k + 1) := by omega
  rw [numBitN_stateEquiv x (3 * j) hb0, numBitN_stateEquiv x (3 * j + 1) hb1,
    numBitN_stateEquiv x (3 * j + 2) hb2]
  congr 1
  rw [bitDigit]
  simp only [hjk, dif_pos]
  rw [reduceBot]
  rw [← maj3_natBit]

/-- **The numeral decoder**: collapse the bottom digit `k` times, then read the bit that remains.
One recursive call per level — the shape `decRec_bottomUp` licenses. -/
def numDecRec : ℕ → ℕ → ℕ
  | 0, s => s % 2
  | k + 1, s => numDecRec k (packReduce (3 ^ k) s)

/-- **The bridge**: the numeral decoder computes `decRec` on packed states.

Each induction step is two rewrites and nothing else — the one-level square above, then the anchor.
The dependent boundary is never crossed again; it was crossed once, in `packReduce_stateEquiv`. -/
theorem numDecRec_stateEquiv : ∀ (k : ℕ) (x : Mem (Fin (3 ^ k)) Bool),
    numDecRec k ((stateEquiv (3 ^ k) x : Fin (2 ^ 3 ^ k)) : ℕ) = if decRec k x then 1 else 0 := by
  intro k
  induction k with
  | zero =>
      intro x
      rw [numDecRec, decRec]
      have h := stateEquiv_digit x ⟨0, by norm_num⟩
      simp only [pow_zero, Nat.div_one] at h
      exact h
  | succ k ih =>
      intro x
      rw [numDecRec, packReduce_stateEquiv k x, ih (reduceBot k x), decRec_bottomUp k x]

/-! ### The decoder as a program: `decRec` priced

The bridge of the last section is a theorem about a `ℕ → ℕ → ℕ` function. To price anything it must
become a *program*, and that is what this section builds: `decBuilder`, one fixed code that decodes
a packed block of any depth.

Two pieces of engineering, no new mathematics. First, `packReduce` is primitive recursive: its
`Finset.range` sum becomes a `List` fold (`packReduceList`, bridged by `packReduceList_eq` — the
idiom `markVal` already runs on), and its bit-triple extraction is `/`, `^`, `%`, which is
`digitAt` at base two.

Second, the decode's recursion has to be reshaped to fit. `numDecRec` recurses on the depth with a
*changing* argument, which `Primrec.nat_rec` does not offer — it offers one call on an accumulator.
So `numDecIter` carries the pair `(remaining depth, current numeral)` and steps it, which fits
`nat_rec` exactly; `numDecIter_read` says the pair iteration computes `numDecRec`, and that is the
whole reason it exists. The induction works by peeling the iteration from the **front**
(`natRec_eq_iterate` turns the `Nat.rec` into a `Function.iterate`, whose `succ_apply` peels the
first step) — peeling from the back leaves the initial depth mismatched with the recursion's own
counter, and the proof does not close.

`decBuilder` is then the `markBuilder` idiom verbatim: one program, taking `⟨depth, packed state⟩`
as a single paired natural, extracted from universality and hence uniform in both.
`eval_decBuilder_stateEquiv` is the payoff — run the code on a packed memory and it returns the bit
`decRec` reads off that memory.

Anchors: [Persistence] §2 + §5. The decoder is this development's; no numbered result of
[Persistence] is claimed machine-checked by its presence. -/

/-- the List form of `packReduce`, the shape `Primrec` consumes -/
private def packReduceList (m s : ℕ) : ℕ :=
  ((List.range m).map fun j =>
    ((numBitN s (3 * j) + numBitN s (3 * j + 1) + numBitN s (3 * j + 2)) / 2) * 2 ^ j).sum

private theorem packReduceList_eq (m s : ℕ) : packReduceList m s = packReduce m s := by
  rw [packReduceList, packReduce]; simp [Finset.sum, Multiset.range]

theorem primrec_packReduce : Primrec₂ packReduce := by
  have hpow : Primrec₂ ((· ^ ·) : ℕ → ℕ → ℕ) := Primrec₂.unpaired'.1 Nat.Primrec.pow
  -- the bit at a computed index, over `q : (ℕ × ℕ) × ℕ` — `q.1.2` the numeral, `q.2` the digit `j`
  have hbit : ∀ r : ℕ, Primrec fun q : (ℕ × ℕ) × ℕ => numBitN q.1.2 (3 * q.2 + r) := by
    intro r
    exact Primrec.nat_mod.comp
      (Primrec.nat_div.comp (Primrec.snd.comp Primrec.fst)
        (hpow.comp (Primrec.const 2)
          (Primrec.nat_add.comp
            (Primrec.nat_mul.comp (Primrec.const 3) Primrec.snd) (Primrec.const r))))
      (Primrec.const 2)
  have hinner : Primrec₂ fun (p : ℕ × ℕ) (j : ℕ) =>
      ((numBitN p.2 (3 * j) + numBitN p.2 (3 * j + 1) + numBitN p.2 (3 * j + 2)) / 2) * 2 ^ j := by
    have h0 : Primrec fun q : (ℕ × ℕ) × ℕ => numBitN q.1.2 (3 * q.2) := by
      have := hbit 0
      simpa using this
    exact Primrec₂.mk (Primrec.nat_mul.comp
      (Primrec.nat_div.comp
        (Primrec.nat_add.comp (Primrec.nat_add.comp h0 (hbit 1)) (hbit 2))
        (Primrec.const 2))
      (hpow.comp (Primrec.const 2) Primrec.snd))
  have hlist : Primrec fun p : ℕ × ℕ => packReduceList p.1 p.2 :=
    primrec_list_sum (Primrec.list_map (Primrec.list_range.comp Primrec.fst) hinner)
  exact (hlist.of_eq fun p => packReduceList_eq p.1 p.2).to₂

private theorem natRec_eq_iterate {α : Type*} (f : α → α) : ∀ (n : ℕ) (p : α),
    Nat.rec p (fun _ ih => f ih) n = f^[n] p := by
  intro n
  induction n with
  | zero => intro p; rfl
  | succ n ih => intro p; rw [Function.iterate_succ_apply']; exact congrArg f (ih p)

/-- one level of the decode, as a step on `(remaining depth, numeral)` -/
def redStep (p : ℕ × ℕ) : ℕ × ℕ := (p.1 - 1, packReduce (3 ^ (p.1 - 1)) p.2)

private theorem primrec_redStep : Primrec redStep := by
  have hpow : Primrec₂ ((· ^ ·) : ℕ → ℕ → ℕ) := Primrec₂.unpaired'.1 Nat.Primrec.pow
  have hd : Primrec fun p : ℕ × ℕ => p.1 - 1 :=
    Primrec.nat_sub.comp Primrec.fst (Primrec.const 1)
  exact Primrec.pair hd
    (primrec_packReduce.comp (hpow.comp (Primrec.const 3) hd) Primrec.snd)

/-- the decoder in the shape `Primrec.nat_rec` consumes: iterate `k` times from `(k, s)` -/
def numDecIter (k s : ℕ) : ℕ × ℕ :=
  Nat.rec (k, s) (fun _ ih => redStep ih) k

private theorem numDecIter_eq (k s : ℕ) : numDecIter k s = redStep^[k] (k, s) :=
  natRec_eq_iterate redStep k (k, s)

/-- the read-out: the iteration computes `numDecRec` -/
private theorem redStep_iterate_read : ∀ (n s : ℕ),
    ((redStep^[n]) (n, s)).2 % 2 = numDecRec n s := by
  intro n
  induction n with
  | zero => intro s; rfl
  | succ n ih =>
      intro s
      rw [Function.iterate_succ_apply]
      have hstep : redStep (n + 1, s) = (n, packReduce (3 ^ n) s) := by
        rw [redStep]; simp
      rw [hstep, ih (packReduce (3 ^ n) s), numDecRec]

theorem numDecIter_read (k s : ℕ) : (numDecIter k s).2 % 2 = numDecRec k s := by
  rw [numDecIter_eq]; exact redStep_iterate_read k s

theorem primrec_numDecIter : Primrec₂ numDecIter := by
  have h := Primrec.nat_rec (f := fun p : ℕ × ℕ => (p.1, p.2))
    (g := fun _ (q : ℕ × (ℕ × ℕ)) => redStep q.2)
    (Primrec.pair Primrec.fst Primrec.snd)
    (Primrec₂.mk (primrec_redStep.comp (Primrec.snd.comp Primrec.snd)))
  exact (h.comp Primrec.id Primrec.fst).of_eq fun p => rfl

theorem primrec_numDecRec : Primrec₂ numDecRec := by
  have h : Primrec fun p : ℕ × ℕ => (numDecIter p.1 p.2).2 % 2 :=
    Primrec.nat_mod.comp (Primrec.snd.comp primrec_numDecIter) (Primrec.const 2)
  exact h.of_eq fun p => numDecIter_read p.1 p.2

/-- the decode as ONE function of a single natural — `⟨depth, packed state⟩` -/
def decFn (a : ℕ) : ℕ := numDecRec a.unpair.1 a.unpair.2

private theorem primrec_decFn : Primrec decFn :=
  primrec_numDecRec.comp (Primrec.fst.comp Primrec.unpair) (Primrec.snd.comp Primrec.unpair)

private theorem partrec_decFn : Nat.Partrec (fun a : ℕ => (decFn a : ℕ)) :=
  _root_.Partrec.nat_iff.mp (Primrec.to_comp primrec_decFn).partrec

/-- **The fixed decoder code**: one program, uniform in the depth and the state. -/
noncomputable def decBuilder : Nat.Partrec.Code :=
  Classical.choose (Nat.Partrec.Code.exists_code.mp partrec_decFn)

theorem eval_decBuilder (a : ℕ) :
    Nat.Partrec.Code.eval decBuilder a = Part.some (decFn a) := by
  have h := congrFun (Classical.choose_spec
    (Nat.Partrec.Code.exists_code.mp partrec_decFn)) a
  simpa [decBuilder] using h

/-- **The decoder code is correct against `decRec`**: run on `⟨k, packed x⟩` it returns the bit
`decRec k x`. -/
theorem eval_decBuilder_stateEquiv (k : ℕ) (x : Mem (Fin (3 ^ k)) Bool) :
    Nat.Partrec.Code.eval decBuilder
        (Nat.pair k ((stateEquiv (3 ^ k) x : Fin (2 ^ 3 ^ k)) : ℕ))
      = Part.some (if decRec k x then 1 else 0) := by
  rw [eval_decBuilder, decFn]
  simp only [Nat.unpair_pair]
  rw [numDecRec_stateEquiv]
/-! ### The habitat on flat cells: blocks are digits

The habitat's cells are indexed by `Fin κ × Fin (3 ^ k)` — block, then position within it. The
packing wants a flat `Fin (κ * 3 ^ k)`, so this section relabels, and then says the one thing the
priced walk needs.

**The relabelling.** `flatHab` sends block `i`, position `p` to the flat cell `p + 3 ^ k * i`: block
`i` occupies the contiguous run `[3 ^ k * i, 3 ^ k * (i + 1))`. That is `finProdFinEquiv`'s own
convention, the same one `tripleEquiv` uses one level down, so the two levels of the construction
agree about which index is the significant one without anything being chosen twice.

**Blocks are digits.** Packed little-endian, a habitat state is therefore a base-`2 ^ 3 ^ k`
numeral whose digit `i` is the packed block `i` (`stateEquiv_flatHab_blocks`, regrouping the bit sum
through `finProdFinEquiv` exactly as the disjoint-union and block-split lemmas do). So extracting a
block is extracting a digit — and `stateEquiv_flatHab_block` is the marking price's digit lemma
again, now at base `2 ^ 3 ^ k`. That is the third base this one lemma has served: base `n` for the
marks, base two for a memory's cells, and base `2 ^ 3 ^ k` for a habitat's blocks.

**The one-cell lemma.** `numDecRec_block` is where the two levels meet: take the packed habitat,
extract digit `i`, run the decoder on it, and out comes exactly the bit `macroLens` reads off block
`i`. Every ingredient of a habitat walk's correctness is in that one statement — the block
extraction from this section, the decoder bridge from the last. The walk itself, and the price it
buys, are the next construction.

Anchors: [Persistence] §2 + §5 + §8. The relabelling is this development's; no numbered result of
[Persistence] is claimed machine-checked by its presence. -/

/-- **Re-indexing a memory**: relabelling the cells is an equivalence of memories. -/
def reindexMem {ι₁ ι₂ V : Type*} (e : ι₁ ≃ ι₂) : Mem ι₂ V ≃ Mem ι₁ V :=
  Equiv.arrowCongr e.symm (Equiv.refl V)

@[simp] private theorem reindexMem_apply {ι₁ ι₂ V : Type*} (e : ι₁ ≃ ι₂) (x : Mem ι₂ V) (i : ι₁) :
    reindexMem e x i = x (e i) := rfl

/-- The habitat's flat cell index: block `i`, position `p` sits at `p + 3 ^ k * i`, so block `i`
occupies the run `[3 ^ k * i, 3 ^ k * (i + 1))`. -/
def habEquiv (κ k : ℕ) : Fin (κ * 3 ^ k) ≃ Fin κ × Fin (3 ^ k) := finProdFinEquiv.symm

/-- The habitat state, relabelled onto flat cells so that the packing applies. -/
def flatHab (κ k : ℕ) : Mem (Fin κ × Fin (3 ^ k)) Bool ≃ Mem (Fin (κ * 3 ^ k)) Bool :=
  reindexMem (habEquiv κ k)

@[simp] private theorem flatHab_symm_cell (κ k : ℕ) (h : Mem (Fin κ × Fin (3 ^ k)) Bool)
    (i : Fin κ) (p : Fin (3 ^ k)) :
    flatHab κ k h (finProdFinEquiv (i, p)) = h (i, p) := by
  rw [flatHab, reindexMem_apply, habEquiv]
  simp

/-- **A packed habitat is a base-`2 ^ 3 ^ k` numeral whose digits are its packed blocks.** The bit
sum regroups through `finProdFinEquiv`, block by block. -/
theorem stateEquiv_flatHab_blocks (κ k : ℕ) (h : Mem (Fin κ × Fin (3 ^ k)) Bool) :
    ((stateEquiv (κ * 3 ^ k) (flatHab κ k h) : Fin (2 ^ (κ * 3 ^ k))) : ℕ)
      = ∑ i : Fin κ, ((stateEquiv (3 ^ k) (blockOf h i) : Fin (2 ^ 3 ^ k)) : ℕ)
          * (2 ^ 3 ^ k) ^ (i : ℕ) := by
  rw [stateEquiv_val]
  rw [← Equiv.sum_comp (finProdFinEquiv (m := κ) (n := 3 ^ k))
    (fun j => (if flatHab κ k h j then 1 else 0) * 2 ^ (j : ℕ))]
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [stateEquiv_val, Finset.sum_mul]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [flatHab_symm_cell, finProdFinEquiv_apply_val, ← pow_mul, pow_add, ← mul_assoc]
  rfl

/-- The packed habitat's base-`2 ^ 3 ^ k` digit `j`, in the shape `sum_digits_div_mod` consumes. -/
private def blockDigit (κ k : ℕ) (h : Mem (Fin κ × Fin (3 ^ k)) Bool) (j : ℕ) : ℕ :=
  if hj : j < κ then ((stateEquiv (3 ^ k) (blockOf h ⟨j, hj⟩) : Fin (2 ^ 3 ^ k)) : ℕ) else 0

private theorem blockDigit_lt (κ k : ℕ) (h : Mem (Fin κ × Fin (3 ^ k)) Bool) (j : ℕ) :
    blockDigit κ k h j < 2 ^ 3 ^ k := by
  rw [blockDigit]; split
  · exact Fin.isLt _
  · positivity

private theorem stateEquiv_flatHab_range (κ k : ℕ) (h : Mem (Fin κ × Fin (3 ^ k)) Bool) :
    ((stateEquiv (κ * 3 ^ k) (flatHab κ k h) : Fin (2 ^ (κ * 3 ^ k))) : ℕ)
      = ∑ j ∈ Finset.range κ, blockDigit κ k h j * (2 ^ 3 ^ k) ^ j := by
  rw [stateEquiv_flatHab_blocks,
    Finset.sum_range fun j => blockDigit κ k h j * (2 ^ 3 ^ k) ^ j]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [blockDigit]
  simp

/-- **Block extraction**: the packed block `i` is the packed habitat's base-`2 ^ 3 ^ k` digit `i` —
the marking price's digit lemma at a third base. -/
theorem stateEquiv_flatHab_block (κ k : ℕ) (h : Mem (Fin κ × Fin (3 ^ k)) Bool) (i : Fin κ) :
    ((stateEquiv (κ * 3 ^ k) (flatHab κ k h) : Fin (2 ^ (κ * 3 ^ k))) : ℕ)
        / (2 ^ 3 ^ k) ^ (i : ℕ) % (2 ^ 3 ^ k)
      = ((stateEquiv (3 ^ k) (blockOf h i) : Fin (2 ^ 3 ^ k)) : ℕ) := by
  rw [stateEquiv_flatHab_range,
    sum_digits_div_mod (n := 2 ^ 3 ^ k) (by positivity) κ (blockDigit κ k h)
      (blockDigit_lt κ k h) i i.2,
    blockDigit]
  simp

/-- **The macro bit of block `i`, read off the packed habitat by program**: extract digit `i`, run
the decoder, and out comes exactly the bit `macroLens` reads off that block.

The two levels meet here. Block extraction is this section's digit lemma; the decoder's correctness
is the numeral bridge. Every ingredient of a habitat walk's correctness is this one statement, and
the walk that consumes it — with the price it buys — is a separate construction. -/
theorem numDecRec_block (κ k : ℕ) (h : Mem (Fin κ × Fin (3 ^ k)) Bool) (i : Fin κ) :
    numDecRec k (((stateEquiv (κ * 3 ^ k) (flatHab κ k h) : Fin (2 ^ (κ * 3 ^ k))) : ℕ)
        / (2 ^ 3 ^ k) ^ (i : ℕ) % (2 ^ 3 ^ k))
      = if macroLens κ k h i then 1 else 0 := by
  rw [stateEquiv_flatHab_block, numDecRec_stateEquiv]
  rfl

/-! ### The blocks' two constants, and the macro word

Two facts remain between the habitat and its price, and both are about numerals.

**A codeword block is a constant numeral.** Encoding writes one bit into all `3 ^ k` cells of a
block, so packed it is either all-ones — `2 ^ 3 ^ k - 1`, the geometric sum — or zero
(`stateEquiv_encRec`). The subtraction is harmless: `2 ^ 3 ^ k` is positive, and this is the one
place a constant of that shape appears. These are the two values a habitat walk writes back.

**The macro word is the packed macro reading.** Run the decoder on each block digit and assemble the
results little-endian, and what comes out is exactly `stateEquiv` of `macroLens`
(`macroWord_eq`) — the regrouping lemma of the last section, read backwards one level up. Per block
it is the one-cell lemma; across blocks it is the same digit bookkeeping as everywhere else in this
layer.

With these, a habitat walk has no mathematics left in front of it: extract the digits, decode each,
assemble the word, look it up in the macro law's table, and write back the two constants.

Anchors: [Persistence] §2 + §5 + §8. Both facts are this development's; no numbered result of
[Persistence] is claimed machine-checked by their presence. -/

private theorem sum_two_pow_range (n : ℕ) : ∑ i ∈ Finset.range n, 2 ^ i = 2 ^ n - 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      have := Nat.one_le_two_pow (n := n)
      omega

/-- **The two constants**: a codeword block packs to all-ones or all-zeros. -/
theorem stateEquiv_encRec (k : ℕ) (b : Bool) :
    ((stateEquiv (3 ^ k) (encRec k b) : Fin (2 ^ 3 ^ k)) : ℕ)
      = if b then 2 ^ 3 ^ k - 1 else 0 := by
  rw [stateEquiv_val]
  cases b
  · simp [encRec]
  · have hb : ∀ i : Fin (3 ^ k),
        (if encRec k true i then 1 else 0) * 2 ^ (i : ℕ) = 2 ^ (i : ℕ) := by
      intro i; simp [encRec]
    rw [Finset.sum_congr rfl fun i _ => hb i, ← Finset.sum_range fun j => 2 ^ j,
      sum_two_pow_range]
    simp

/-- **The macro word, packed**: assembling the blocks' decoded bits little-endian gives exactly the
packed macro reading. The regrouping lemma of the last section, run backwards at the macro level. -/
theorem macroWord_eq (κ k : ℕ) (h : Mem (Fin κ × Fin (3 ^ k)) Bool) :
    ∑ j ∈ Finset.range κ,
        numDecRec k (((stateEquiv (κ * 3 ^ k) (flatHab κ k h) : Fin (2 ^ (κ * 3 ^ k))) : ℕ)
          / (2 ^ 3 ^ k) ^ j % (2 ^ 3 ^ k)) * 2 ^ j
      = ((stateEquiv κ (macroLens κ k h) : Fin (2 ^ κ)) : ℕ) := by
  conv_rhs => rw [stateEquiv_val_range]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjk : j < κ := Finset.mem_range.mp hj
  have hb := numDecRec_block κ k h ⟨j, hjk⟩
  rw [hb, bitDigit]
  simp only [hjk, dif_pos]
/-! ### The habitat walk: the update, computed on numerals

The habitat world decodes its blocks, applies the macro law once, and re-encodes. This section does
that arithmetic on the packed numeral, and proves it agrees.

The walk is three steps and each has its lemma already. `macroWordOf` extracts the block digits,
decodes each, and assembles the results little-endian — `macroWord_eq` says that is the packed macro
reading. A lookup in the macro law's own table then gives the packed next macro state, by
`packWorld_apply`. And `habWriteBack` writes the two constants back, block by block —
`stateEquiv_encRec` says a codeword block packs to all-ones or zero, and `stateEquiv_flatHab_range`
reassembles them into a habitat. `habStep_stateEquiv` chains the three, and nothing else enters:
every step of it was proved before the walk was written.

What the walk consumes is the macro law as a *table*, packed by `packWorld` — which is the point of
the bridge. `G` is a function on memories; the pricing layer only ever sees the `2 ^ κ`-entry table
of its packed form, and one entry of that table is all the walk reads per state.

Anchors: [Persistence] §2 + §5 + §8. The walk is this development's; no numbered result of
[Persistence] is claimed machine-checked by its presence. -/

/-- the macro word read off a packed habitat: decode each block digit, assemble little-endian -/
def macroWordOf (κ k s : ℕ) : ℕ :=
  ((List.range κ).map fun j => numDecRec k (s / (2 ^ 3 ^ k) ^ j % (2 ^ 3 ^ k)) * 2 ^ j).sum

private theorem macroWordOf_eq_sum (κ k s : ℕ) :
    macroWordOf κ k s
      = ∑ j ∈ Finset.range κ, numDecRec k (s / (2 ^ 3 ^ k) ^ j % (2 ^ 3 ^ k)) * 2 ^ j := by
  rw [macroWordOf]; simp [Finset.sum, Multiset.range]

theorem macroWordOf_stateEquiv (κ k : ℕ) (h : Mem (Fin κ × Fin (3 ^ k)) Bool) :
    macroWordOf κ k ((stateEquiv (κ * 3 ^ k) (flatHab κ k h) : Fin (2 ^ (κ * 3 ^ k))) : ℕ)
      = ((stateEquiv κ (macroLens κ k h) : Fin (2 ^ κ)) : ℕ) := by
  rw [macroWordOf_eq_sum, macroWord_eq]

/-- writing back the two constants: block `j` becomes all-ones or all-zeros by bit `j` of `Gw` -/
def habWriteBack (κ k Gw : ℕ) : ℕ :=
  ((List.range κ).map fun j => numBitN Gw j * (2 ^ 3 ^ k - 1) * (2 ^ 3 ^ k) ^ j).sum

private theorem habWriteBack_eq_sum (κ k Gw : ℕ) :
    habWriteBack κ k Gw
      = ∑ j ∈ Finset.range κ, numBitN Gw j * (2 ^ 3 ^ k - 1) * (2 ^ 3 ^ k) ^ j := by
  rw [habWriteBack]; simp [Finset.sum, Multiset.range]

theorem habWriteBack_stateEquiv (κ k : ℕ) (b : Mem (Fin κ) Bool) :
    habWriteBack κ k ((stateEquiv κ b : Fin (2 ^ κ)) : ℕ)
      = ((stateEquiv (κ * 3 ^ k) (flatHab κ k (habitatEnc κ k b))
            : Fin (2 ^ (κ * 3 ^ k))) : ℕ) := by
  rw [habWriteBack_eq_sum]
  conv_rhs => rw [stateEquiv_flatHab_range]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjk : j < κ := Finset.mem_range.mp hj
  rw [numBitN_stateEquiv b j hjk, blockDigit]
  simp only [hjk, dif_pos, blockOf_habitatEnc, stateEquiv_encRec]
  cases b ⟨j, hjk⟩ <;> simp

/-- **The habitat walk**: from `G`'s packed table and a packed habitat, the packed next habitat. -/
def habStep (κ k Gt s : ℕ) : ℕ :=
  habWriteBack κ k (((Encodable.decode (α := List ℕ) Gt).getD []).getD (macroWordOf κ k s) 0)

/-- **The walk is correct**: it computes the packed habitat world. -/
theorem habStep_stateEquiv (κ k : ℕ) (G : Mem (Fin κ) Bool → Mem (Fin κ) Bool)
    (h : Mem (Fin κ × Fin (3 ^ k)) Bool) :
    habStep κ k (lensCode (packWorld G))
        ((stateEquiv (κ * 3 ^ k) (flatHab κ k h) : Fin (2 ^ (κ * 3 ^ k))) : ℕ)
      = ((stateEquiv (κ * 3 ^ k) (flatHab κ k (habitatWorld κ k G h))
            : Fin (2 ^ (κ * 3 ^ k))) : ℕ) := by
  rw [habStep, decode_lensCode, macroWordOf_stateEquiv,
    lensTable_getD _ _ (Fin.isLt (stateEquiv κ (macroLens κ k h)))]
  simp only [Fin.eta]
  rw [packWorld_apply, habWriteBack_stateEquiv, habitatWorld]
/-! ### The walk, primitive recursive

The walk is arithmetic on numerals, so it is primitive recursive, and this section says so. There is
no mathematics here — the walk's meaning was settled by `habStep_stateEquiv`; what is established
now is only that a program can carry it out.

Each piece follows the shape the marking price already uses: a bounded sum over `List.range`, folded
by `primrec_list_sum`, with `/`, `%`, `^` doing the digit work. `macroWordOf` needs the decoder
(`primrec_numDecRec`, itself the pair-accumulator's payoff); `habWriteBack` needs only the two block
constants; `habStep` composes them either side of one table lookup.

Anchors: [Persistence] §2 + §5 + §8. No numbered result of [Persistence] is claimed machine-checked
by their presence. -/

private theorem hpow2 : Primrec₂ ((· ^ ·) : ℕ → ℕ → ℕ) := Primrec₂.unpaired'.1 Nat.Primrec.pow

theorem primrec_macroWordOf : Primrec fun q : (ℕ × ℕ) × ℕ => macroWordOf q.1.1 q.1.2 q.2 := by
  have hinner : Primrec₂ fun (q : (ℕ × ℕ) × ℕ) (j : ℕ) =>
      numDecRec q.1.2 (q.2 / (2 ^ 3 ^ q.1.2) ^ j % (2 ^ 3 ^ q.1.2)) * 2 ^ j := by
    refine Primrec₂.mk ?_
    have hk : Primrec fun p : ((ℕ × ℕ) × ℕ) × ℕ => p.1.1.2 :=
      Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
    have hs : Primrec fun p : ((ℕ × ℕ) × ℕ) × ℕ => p.1.2 := Primrec.snd.comp Primrec.fst
    have hbase : Primrec fun p : ((ℕ × ℕ) × ℕ) × ℕ => 2 ^ 3 ^ p.1.1.2 :=
      hpow2.comp (Primrec.const 2) (hpow2.comp (Primrec.const 3) hk)
    exact Primrec.nat_mul.comp
      (primrec_numDecRec.comp hk
        (Primrec.nat_mod.comp
          (Primrec.nat_div.comp hs (hpow2.comp hbase Primrec.snd)) hbase))
      (hpow2.comp (Primrec.const 2) Primrec.snd)
  exact (primrec_list_sum
    (Primrec.list_map (Primrec.list_range.comp (Primrec.fst.comp Primrec.fst)) hinner)).of_eq
      fun q => rfl

theorem primrec_habWriteBack : Primrec fun q : (ℕ × ℕ) × ℕ => habWriteBack q.1.1 q.1.2 q.2 := by
  have hinner : Primrec₂ fun (q : (ℕ × ℕ) × ℕ) (j : ℕ) =>
      numBitN q.2 j * (2 ^ 3 ^ q.1.2 - 1) * (2 ^ 3 ^ q.1.2) ^ j := by
    refine Primrec₂.mk ?_
    have hk : Primrec fun p : ((ℕ × ℕ) × ℕ) × ℕ => p.1.1.2 :=
      Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
    have hGw : Primrec fun p : ((ℕ × ℕ) × ℕ) × ℕ => p.1.2 := Primrec.snd.comp Primrec.fst
    have hbase : Primrec fun p : ((ℕ × ℕ) × ℕ) × ℕ => 2 ^ 3 ^ p.1.1.2 :=
      hpow2.comp (Primrec.const 2) (hpow2.comp (Primrec.const 3) hk)
    have hbit : Primrec fun p : ((ℕ × ℕ) × ℕ) × ℕ => numBitN p.1.2 p.2 :=
      Primrec.nat_mod.comp
        (Primrec.nat_div.comp hGw (hpow2.comp (Primrec.const 2) Primrec.snd))
        (Primrec.const 2)
    exact Primrec.nat_mul.comp
      (Primrec.nat_mul.comp hbit (Primrec.nat_sub.comp hbase (Primrec.const 1)))
      (hpow2.comp hbase Primrec.snd)
  exact (primrec_list_sum
    (Primrec.list_map (Primrec.list_range.comp (Primrec.fst.comp Primrec.fst)) hinner)).of_eq
      fun q => rfl

theorem primrec_habStep :
    Primrec fun q : (ℕ × ℕ) × (ℕ × ℕ) => habStep q.1.1 q.1.2 q.2.1 q.2.2 := by
  have hκ : Primrec fun q : (ℕ × ℕ) × (ℕ × ℕ) => q.1.1 := Primrec.fst.comp Primrec.fst
  have hk : Primrec fun q : (ℕ × ℕ) × (ℕ × ℕ) => q.1.2 := Primrec.snd.comp Primrec.fst
  have hGt : Primrec fun q : (ℕ × ℕ) × (ℕ × ℕ) => q.2.1 := Primrec.fst.comp Primrec.snd
  have hs : Primrec fun q : (ℕ × ℕ) × (ℕ × ℕ) => q.2.2 := Primrec.snd.comp Primrec.snd
  have hword : Primrec fun q : (ℕ × ℕ) × (ℕ × ℕ) => macroWordOf q.1.1 q.1.2 q.2.2 :=
    primrec_macroWordOf.comp (Primrec.pair (Primrec.pair hκ hk) hs)
  have hdec : Primrec fun q : (ℕ × ℕ) × (ℕ × ℕ) =>
      (Encodable.decode (α := List ℕ) q.2.1).getD [] :=
    Primrec.option_getD.comp (Primrec.decode.comp hGt) (Primrec.const [])
  have hlook : Primrec fun q : (ℕ × ℕ) × (ℕ × ℕ) =>
      ((Encodable.decode (α := List ℕ) q.2.1).getD []).getD (macroWordOf q.1.1 q.1.2 q.2.2) 0 :=
    (Primrec.list_getD 0).comp hdec hword
  exact primrec_habWriteBack.comp (Primrec.pair (Primrec.pair hκ hk) hlook)
/-! ### The habitat world on flat cells

The walk computes on numerals; this section gives the map it computes a name.

`habitatWorld` lives on `Mem (Fin κ × Fin (3 ^ k)) Bool` — block, then position. The pricing layer
indexes tables by states of a `Mem (Fin N) Bool`, so `flatWorld` is the same world seen through the
relabelling: conjugate `habitatWorld` by `flatHab`, and what results is a world on `κ * 3 ^ k` flat
cells whose packing is what a table would list.

Its one law is a restatement, not new content: `habStep_packWorld` says the walk, run on a packed
state, computes `packWorld (flatWorld κ k G)` — which is `habStep_stateEquiv` with both sides given
their names. Every state of the flat world is a packed habitat and every packed habitat is a state,
so the two statements carry the same information; this one is simply in the vocabulary a price is
written in.

Anchors: [Persistence] §2 + §5 + §8. No numbered result of [Persistence] is claimed machine-checked
by its presence. -/

/-- The habitat world rewritten on flat cells: conjugate `habitatWorld κ k G` by the packing
`flatHab κ k`, so the state space is a single `Fin (κ * 3 ^ k)`-indexed memory rather than a
product. Same dynamics, in the vocabulary a price is written in. -/
def flatWorld (κ k : ℕ) (G : Mem (Fin κ) Bool → Mem (Fin κ) Bool) :
    Mem (Fin (κ * 3 ^ k)) Bool → Mem (Fin (κ * 3 ^ k)) Bool :=
  fun x => flatHab κ k (habitatWorld κ k G ((flatHab κ k).symm x))

@[simp] theorem flatWorld_flatHab (κ k : ℕ) (G : Mem (Fin κ) Bool → Mem (Fin κ) Bool)
    (h : Mem (Fin κ × Fin (3 ^ k)) Bool) :
    flatWorld κ k G (flatHab κ k h) = flatHab κ k (habitatWorld κ k G h) := by
  rw [flatWorld, Equiv.symm_apply_apply]

theorem habStep_packWorld (κ k : ℕ) (G : Mem (Fin κ) Bool → Mem (Fin κ) Bool)
    (t : Fin (2 ^ (κ * 3 ^ k))) :
    habStep κ k (lensCode (packWorld G)) (t : ℕ)
      = ((packWorld (flatWorld κ k G) t : Fin (2 ^ (κ * 3 ^ k))) : ℕ) := by
  obtain ⟨x, rfl⟩ := (stateEquiv (κ * 3 ^ k)).surjective t
  obtain ⟨h, rfl⟩ := (flatHab κ k).surjective x
  rw [habStep_stateEquiv, packWorld_apply, flatWorld_flatHab]
/-! ### The habitat world, priced

Now the walk becomes a program with a price. Two obstacles stood in the way, both of elaboration
cost rather than mathematics, and both are dissolved here once.

**A normal form for tables.** `lensTable` lists its entries along `List.finRange n`; a builder that
produces a table lists them along `List.range n`. Bridging the two by `List.ext_getElem` forces the
elaborator to unify a `Fin.mk` at the table's length — harmless at a symbolic `n`, ruinous when the
length is `2 ^ (κ · 3 ^ k)`. `lensTable_range` rewrites the first form into the second, proved once
at symbolic `n`, so every downstream bridge is a `List.map` congruence over `List.range` with no
index unified. All three of this layer's numeral bases feed tables through `lensTable`, so the
normal form is the whole layer's asset, not this section's alone.

**An opaque step.** The walk's step `habStep` is a deep composition — nested folds, the decoder's
`Nat.rec`, `packReduce`. When a `Primrec` lemma unifies against it, `isDefEq` unfolds that body and
grinds. But the step's meaning is entirely captured by `habStep_packWorld`; its body is never needed
again. So it is made `irreducible` here, and the `Primrec` proof matches at the head in one step.

With those, the assembly is the marking price verbatim. `habTableFn` tabulates the walk over
`List.range (2 ^ (κ · 3 ^ k))`; `habTableFn_eq` identifies it with the packed flat world's table (by
`habStep_packWorld`, through the normal form); `exists_code` extracts `habBuilder`; and
`KE_flatWorld_le` prices it.

**The price is the point.** A world of `2 ^ (κ · 3 ^ k)` states is described in
`elen cG + O(size κ + size k)` bits — the macro law's own program plus the logarithms of the two
structural parameters, and *nothing that scales with the state count*. The route matters: the
builder is fed the macro law as a **code** `cG`, composed, so its length enters additively; feeding
it the
law's exponential-length table instead would price the table, not the law. This is the (U)-positive
statement in the world's own currency — the sub-system's coarse law is cheap even though the world
it runs in is astronomically large.

Anchors: [Persistence] §2 + §5 + §8. No numbered result of [Persistence] is claimed machine-checked
by their presence. -/

/-- **The table normal form**: `lensTable` re-listed along `List.range n` rather than
`List.finRange n`. Proved once at symbolic `n`, so a downstream bridge to a `List.range`-built table
is a `List.map` congruence with no `Fin` index ever unified — the fix for the huge-length wall, and
the reusable asset the whole numeral layer feeds through. -/
theorem lensTable_range {n m : ℕ} (ℓ : Fin n → Fin m) :
    lensTable ℓ = (List.range n).map (fun i => if h : i < n then (ℓ ⟨i, h⟩ : ℕ) else 0) := by
  rw [lensTable]
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    rw [List.getElem_map, List.getElem_map, List.getElem_finRange, List.getElem_range]
    have hi : i < n := by simpa using h1
    rw [dif_pos hi, Fin.cast_mk]

section Price

attribute [local irreducible] habStep

/-- **The habitat table**: the walk tabulated over every state, as one function of the paired input
`⟨κ, k, G's packed table⟩`. -/
def habTableFn (a : ℕ) : ℕ :=
  Encodable.encode ((List.range (2 ^ (a.unpair.1 * 3 ^ a.unpair.2.unpair.1))).map
    (fun s => habStep a.unpair.1 a.unpair.2.unpair.1 a.unpair.2.unpair.2 s))

theorem primrec_habTableFn : Primrec habTableFn := by
  have hpow : Primrec₂ ((· ^ ·) : ℕ → ℕ → ℕ) := Primrec₂.unpaired'.1 Nat.Primrec.pow
  have hκ : Primrec fun a : ℕ => a.unpair.1 := Primrec.fst.comp Primrec.unpair
  have hk : Primrec fun a : ℕ => a.unpair.2.unpair.1 :=
    Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))
  have hGt : Primrec fun a : ℕ => a.unpair.2.unpair.2 :=
    Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))
  have hN : Primrec fun a : ℕ => 2 ^ (a.unpair.1 * 3 ^ a.unpair.2.unpair.1) :=
    hpow.comp (Primrec.const 2)
      (Primrec.nat_mul.comp hκ (hpow.comp (Primrec.const 3) hk))
  have hinner : Primrec₂ fun (a : ℕ) (s : ℕ) =>
      habStep a.unpair.1 a.unpair.2.unpair.1 a.unpair.2.unpair.2 s :=
    Primrec₂.mk (primrec_habStep.comp
      (Primrec.pair
        (Primrec.pair (hκ.comp Primrec.fst) (hk.comp Primrec.fst))
        (Primrec.pair (hGt.comp Primrec.fst) Primrec.snd)))
  exact Primrec.encode.comp (Primrec.list_map (Primrec.list_range.comp hN) hinner)

/-- **The table is the packed flat world's**. The bridge that timed out until the normal form: both
sides list along `List.range (2 ^ (κ · 3 ^ k))`, so the equality is a `List.map` congruence closed
per-entry by `habStep_packWorld`, never unifying an index at the huge length. -/
theorem habTableFn_eq (κ k : ℕ) (G : Mem (Fin κ) Bool → Mem (Fin κ) Bool) :
    habTableFn (Nat.pair κ (Nat.pair k (lensCode (packWorld G))))
      = lensCode (packWorld (flatWorld κ k G)) := by
  rw [habTableFn]
  simp only [Nat.unpair_pair]
  conv_rhs => rw [lensCode, lensTable_range]
  congr 1
  refine List.map_congr_left fun s hs => ?_
  have hsN : s < 2 ^ (κ * 3 ^ k) := List.mem_range.mp hs
  rw [dif_pos hsN]
  exact habStep_packWorld κ k G ⟨s, hsN⟩

private theorem partrec_habTableFn : Nat.Partrec (fun a : ℕ => (habTableFn a : ℕ)) :=
  _root_.Partrec.nat_iff.mp (Primrec.to_comp primrec_habTableFn).partrec

/-- **The fixed habitat builder code**, extracted from universality: one program taking
`⟨κ, k, the macro law's table⟩`. -/
noncomputable def habBuilder : Nat.Partrec.Code :=
  Classical.choose (Nat.Partrec.Code.exists_code.mp partrec_habTableFn)

theorem eval_habBuilder (a : ℕ) :
    Nat.Partrec.Code.eval habBuilder a = Part.some (habTableFn a) := by
  have h := congrFun (Classical.choose_spec
    (Nat.Partrec.Code.exists_code.mp partrec_habTableFn)) a
  simpa [habBuilder] using h

/-- **The habitat world is owned at the macro law's own cost plus logarithms** ([Persistence] §8,
the (U)-positive clause in world-table form). Given a code `cG` for the macro law's packed table,
the flat habitat world — a world of `2 ^ (κ · 3 ^ k)` states — has a table describable in
`elen cG + O(size κ + size k)` bits: the law's program, composed into the fixed builder, plus the
logarithms of the two structural parameters. Nothing here scales with the number of states.

The macro law enters as a **code**, `comp cG zero`, so its length is additive; were it fed as its
`2 ^ κ`-entry table the bound would price the table, not the law. That distinction is the whole
content of "the sub-system owns its law cheaply". -/
theorem KE_flatWorld_le (κ k : ℕ) (G : Mem (Fin κ) Bool → Mem (Fin κ) Bool)
    (cG : Nat.Partrec.Code) (hG : cG.eval 0 = Part.some (lensCode (packWorld G))) :
    KE (lensCode (packWorld (flatWorld κ k G)))
      ≤ elen cG + (15 + elen dbl) * (Nat.size κ + Nat.size k)
        + (elen habBuilder + 2 * (15 + elen dbl) + 15) := by
  have hz : Nat.Partrec.Code.eval Nat.Partrec.Code.zero 0 = Part.some 0 := rfl
  have hcG : Nat.Partrec.Code.eval (Nat.Partrec.Code.comp cG Nat.Partrec.Code.zero) 0
      = Part.some (lensCode (packWorld G)) := (eval_comp_some hz).trans hG
  have hp2 : Nat.Partrec.Code.eval
      (Nat.Partrec.Code.pair (bconst k) (Nat.Partrec.Code.comp cG Nat.Partrec.Code.zero)) 0
      = Part.some (Nat.pair k (lensCode (packWorld G))) := by
    change Nat.pair <$> _ <*> _ = _
    rw [eval_bconst k 0, hcG]; simp [Seq.seq]
  have hp1 : Nat.Partrec.Code.eval
      (Nat.Partrec.Code.pair (bconst κ)
        (Nat.Partrec.Code.pair (bconst k) (Nat.Partrec.Code.comp cG Nat.Partrec.Code.zero))) 0
      = Part.some (Nat.pair κ (Nat.pair k (lensCode (packWorld G)))) := by
    change Nat.pair <$> _ <*> _ = _
    rw [eval_bconst κ 0, hp2]; simp [Seq.seq]
  have hcomp : Computes (Nat.Partrec.Code.comp habBuilder
      (Nat.Partrec.Code.pair (bconst κ)
        (Nat.Partrec.Code.pair (bconst k) (Nat.Partrec.Code.comp cG Nat.Partrec.Code.zero))))
      (lensCode (packWorld (flatWorld κ k G))) := by
    change Nat.Partrec.Code.eval _ 0 = _
    rw [eval_comp_some hp1, eval_habBuilder, habTableFn_eq]
  have hle := KE_le hcomp
  have hbκ := elen_bconst_le κ
  have hbk := elen_bconst_le k
  have hz3 : elen Nat.Partrec.Code.zero = 3 := rfl
  simp only [E_len_comp, E_len_pair, hz3] at hle
  rw [Nat.mul_add]
  omega

end Price

/-! ### The packaged Witness World ([Persistence] §5, §7, §8, §10.1 + [Decoupling] §6)

The construction so far — the habitat world running a macro law `G` beside an arbitrary environment
`π`, its exact reading, its healing margin, its price — is assembled here into one statement, and
its two remaining clauses are supplied: the internalization threshold it crosses, and the contrast
that makes it interesting — that its *typical* member is unreadable in full even though its coarse
law is free.

The threshold is arithmetic on an imported bound. The contrast is the core-anchored version of the
ownership ladder: the habitat world is not a permutation, so `faithful_rule_cost` cannot price it
directly — but its **recurrent core** is a genuine permutation (codewords running `G` beside the
environment running `π`), and a faithful reading of *that* still hands back the environment's rule,
whose table is incompressible for all but a vanishing fraction of environments.

Anchors: [Persistence] §5, §7, §8, §10.1 + [Decoupling] §6. No numbered result of [Persistence] is
claimed machine-checked by anything in this section; the packaged theorem is a synthesis the paper
does not yet state. -/

section WitnessWorldPackage

open Equiv MulAction

attribute [local instance] arrowAction

/-- **The internalization threshold** ([Decoupling] §6.3, consumed as a black box). The κ-bit
habitat **hosts** the bounded checker for the Gödel sentence of number `g`: its `2 ^ κ` macro states
have room for the recursor of the concrete `poly(g) = g²` proof-code budget of [Decoupling] §6.3, so
`g² + 1 ≤ 2 ^ κ` and every candidate proof code `p ≤ M_chk ≤ g²` is a macro state.

(Distinct from `CategoricalThreshold.hostsAt`, the [Decoupling] §6 work-budget predicate
`capacity n ≤ w`; this is its concrete downstream consequence in the habitat's own state count, and
`hostsThreshold_of_capacity` is the bridge between the two.) -/
def hostsThreshold (κ g : ℕ) : Prop := g ^ 2 + 1 ≤ 2 ^ κ

/-- **Above the capacity threshold the habitat hosts the checker.** Whenever the κ macro bits meet
[Decoupling] §6.3's linear capacity `capacity n = 2 n` for the Gödel sentence of number `g`
(`n := ⌈log₂ (g + 1)⌉` — precisely `CategoricalThreshold.hostsAt κ g`), the habitat's `2 ^ κ` macro
states host the depth-`g²` bounded recursor. Pure arithmetic on the imported [Decoupling] §6.3
bound — this section is its consumer, not its prover. -/
theorem hostsThreshold_of_capacity {κ g : ℕ}
    (h : GodelInternalization.capacity (Nat.clog 2 (g + 1)) ≤ κ) : hostsThreshold κ g := by
  refine (GodelInternalization.capacity_bound g (g ^ 2) le_rfl).trans ?_
  exact Nat.pow_le_pow_right (by norm_num) h

/-! #### The full world, packed and priced

The witness world is the habitat world beside the environment (`witnessWorld_conj`: it *is*
`prodWorld (habitatWorld κ k G) π` read through the disjoint-union bridge). Packed onto the numeral
carrier the tables index, the habitat factor is not a permutation, so its price needs the Cartesian
product world of two **endofunctions** — `prodWorldFinFn`, the non-invertible counterpart of
`prodWorldFin`. Its table is the same interleaving (`prodAppend`), so the same `prodBuilder` prices
it, and the whole world costs the macro law's code, the environment's code, and the logarithms of
the structural sizes — nothing that scales with the state count. -/

/-- **The Cartesian product world on `Fin (n₁ * n₂)`, for endofunctions**: both coordinates step by
their own factor, neither reading the other. `prodWorldFin` is the case of two permutations; the
witness world's habitat factor is not one, so this is the shape its price needs. -/
def prodWorldFinFn {n₁ n₂ : ℕ} (U₁ : Fin n₁ → Fin n₁) (U₂ : Fin n₂ → Fin n₂) :
    Fin (n₁ * n₂) → Fin (n₁ * n₂) :=
  fun p => finProdFinEquiv (U₁ (finProdFinEquiv.symm p).1, U₂ (finProdFinEquiv.symm p).2)

@[simp] private theorem prodWorldFinFn_apply {n₁ n₂ : ℕ} (U₁ : Fin n₁ → Fin n₁)
    (U₂ : Fin n₂ → Fin n₂) (i : Fin n₁) (j : Fin n₂) :
    prodWorldFinFn U₁ U₂ (finProdFinEquiv (i, j)) = finProdFinEquiv (U₁ i, U₂ j) := by
  simp [prodWorldFinFn]

/-- The product world's table entry at the pair `(i, j)`, in the index shape `List.ofFn_mul`
produces — the `prodWorldFin_val` arithmetic with the permutation coercion dropped. -/
private theorem prodWorldFinFn_val {n₁ n₂ : ℕ} (U₁ : Fin n₁ → Fin n₁) (U₂ : Fin n₂ → Fin n₂)
    (i : Fin n₁) (j : Fin n₂) (h : i.val * n₂ + j.val < n₁ * n₂) :
    ((prodWorldFinFn U₁ U₂ ⟨i.val * n₂ + j.val, h⟩ : Fin (n₁ * n₂)) : ℕ)
      = ((U₂ j : Fin n₂) : ℕ) + n₂ * ((U₁ i : Fin n₁) : ℕ) := by
  have hidx : (⟨i.val * n₂ + j.val, h⟩ : Fin (n₁ * n₂)) = finProdFinEquiv (i, j) := by
    apply Fin.ext
    simp [finProdFinEquiv_apply_val]
    ring
  rw [hidx, prodWorldFinFn_apply]
  simp [finProdFinEquiv_apply_val]

/-- The endofunction product world's table is the two factors' tables interleaved, exactly as for
`prodWorldFin`. -/
private theorem lensTable_prodWorldFinFn {n₁ n₂ : ℕ} (U₁ : Fin n₁ → Fin n₁) (U₂ : Fin n₂ → Fin n₂) :
    lensTable (prodWorldFinFn U₁ U₂) = prodAppend (lensTable U₁) (lensTable U₂) := by
  have hlen : (lensTable U₂).length = n₂ := by rw [lensTable]; simp
  rw [prodAppend, hlen, lensTable, lensTable, lensTable, ← List.ofFn_eq_map, ← List.ofFn_eq_map,
    ← List.ofFn_eq_map, List.flatMap_def, List.map_ofFn]
  rw [List.ofFn_mul]
  congr 1
  refine congrArg List.ofFn (funext fun i => ?_)
  simp only [Function.comp_apply, List.map_ofFn]
  refine congrArg List.ofFn (funext fun j => ?_)
  simp only [Function.comp_apply]
  exact prodWorldFinFn_val U₁ U₂ i j _

/-- **`prodBuilder` prices the endofunction product too**: on `⟨U₁'s table, U₂'s table⟩` the one
fixed product builder outputs the endofunction product world's table. -/
private theorem prodTableFn_eq_fn {n₁ n₂ : ℕ} (U₁ : Fin n₁ → Fin n₁) (U₂ : Fin n₂ → Fin n₂) :
    prodTableFn (Nat.pair (lensCode U₁) (lensCode U₂)) = lensCode (prodWorldFinFn U₁ U₂) := by
  rw [prodTableFn]
  simp only [Nat.unpair_pair, decode_lensCode]
  rw [← lensTable_prodWorldFinFn]
  rfl

/-- **Rules compose for endofunctions too.** Given codes for the two factors' tables, the
endofunction product world costs their lengths plus the same absolute constant
`elen prodBuilder + 6` as `KE_prodWorldFin_le` — one fixed builder, independent of the worlds. -/
private theorem KE_prodWorldFinFn_le {n₁ n₂ : ℕ} (U₁ : Fin n₁ → Fin n₁) (U₂ : Fin n₂ → Fin n₂)
    (c₁ c₂ : Code) (h₁ : c₁.eval 0 = Part.some (lensCode U₁))
    (h₂ : c₂.eval 0 = Part.some (lensCode U₂)) :
    KE (lensCode (prodWorldFinFn U₁ U₂)) ≤ elen c₁ + elen c₂ + (elen prodBuilder + 6) := by
  have hp : Nat.Partrec.Code.eval (Nat.Partrec.Code.pair c₁ c₂) 0
      = Part.some (Nat.pair (lensCode U₁) (lensCode U₂)) := by
    change Nat.pair <$> _ <*> _ = _
    rw [h₁, h₂]; simp [Seq.seq]
  have hcomp : Computes (Nat.Partrec.Code.comp prodBuilder (Nat.Partrec.Code.pair c₁ c₂))
      (lensCode (prodWorldFinFn U₁ U₂)) := by
    change Nat.Partrec.Code.eval _ 0 = _
    rw [eval_comp_some hp, eval_prodBuilder, prodTableFn_eq_fn]
  have hle := KE_le hcomp
  rw [E_len_comp, E_len_pair] at hle
  omega

/-- **The witness world, packed and priced** ([Persistence] §8, the (U)-positive clause in the
world's own table currency). The habitat world running the macro law `G`, packed onto its
`2 ^ (κ · 3 ^ k)`-numeral carrier, set beside an environment world `E` on its own `2 ^ J` states,
has a table describable in

  `elen cG + elen cπ + O(size κ + size k)`

bits: the macro law's program `cG`, the environment's program `cπ`, and the logarithms of the two
structural parameters — and *nothing that scales with the number of states*, of which there are
`2 ^ (κ · 3 ^ k) · 2 ^ J`. Both laws enter as **codes**, composed into the fixed builders (the
habitat's, then `prodBuilder`), so their lengths are additive; feeding either as its exponential
table would price the table, not the law. This is the whole world's version of the statement that a
cheaply-run world stays cheap to describe when a second cheap world is set beside it. -/
theorem KE_packWitnessWorld_le (κ k J : ℕ) (G : Mem (Fin κ) Bool → Mem (Fin κ) Bool)
    (E : Fin (2 ^ J) → Fin (2 ^ J)) (cG cπ : Code)
    (hG : cG.eval 0 = Part.some (lensCode (packWorld G)))
    (hπ : cπ.eval 0 = Part.some (lensCode E)) :
    KE (lensCode (prodWorldFinFn (packWorld (flatWorld κ k G)) E))
      ≤ elen cG + elen cπ + (15 + elen dbl) * (Nat.size κ + Nat.size k)
        + (elen prodBuilder + elen habBuilder + 2 * (15 + elen dbl) + 21) := by
  obtain ⟨cHab, hHabEval, hHabLen⟩ := exists_min_E (lensCode (packWorld (flatWorld κ k G)))
  have hcHabLe : elen cHab ≤ elen cG + (15 + elen dbl) * (Nat.size κ + Nat.size k)
      + (elen habBuilder + 2 * (15 + elen dbl) + 15) := by
    rw [hHabLen]; exact KE_flatWorld_le κ k G cG hG
  have hprod := KE_prodWorldFinFn_le (packWorld (flatWorld κ k G)) E cHab cπ hHabEval hπ
  omega

/-! #### The contrast: the typical member is unreadable in full

The habitat world is not a permutation, so `faithful_rule_cost` cannot price the witness world
directly. Its **recurrent core** is one, though: every state surviving forever is a codeword-habitat
state (`omegaLimit_witnessWorld_subset`), and on codewords the update is the macro law running
beside the environment — a Cartesian product of two permutations, `prodWorldFin` of the macro core
and the environment. A faithful reading of that core world therefore hands back the environment's
rule (`KE_factorSnd_le_of_faithful`), whose table is incompressible for all but a vanishing fraction
of environments.

`card_readable_core_le` makes "vanishing" precise, in the ncard idiom of the collapse. The
environment permutations admitting a faithful uniform reading of the core world at budget `b` number
at most `2 ^ (2 b + O(size n₂) + 1)` — a `2 ^ (−d)` fraction of the `n₂ !` permutations once
`2 b + O(size n₂)` falls a margin `d` below `log₂ (n₂ !)`. So below half the environment's entropy —
`b < (log₂ (n₂ !) − O(log n₂) − d) / 2` — all but a `2 ^ (−d)` fraction of environments admit **no**
faithful reading of the world at all: cheap to run a sub-system in, unaffordable to read entire. The
`O(log n₂)` slack and the halving are `KE_factorSnd_le_of_faithful`'s own; the statement is
asymptotic. -/

/-- **The typical environment is unreadable in full.** Fix the habitat's recurrent rule `U₁`. The
environment permutations `U₂` for which the core world `prodWorldFin U₁ U₂` admits *some* faithful
uniform reading at budget `b` number at most `2 ^ (2 b + O(size n₂) + 1)` — a description of the
environment's own rule falls out of any such reading (`KE_factorSnd_le_of_faithful`), and there are
too few short descriptions (`card_KE_le`) for many environments to have one. Once `2 b + O(size n₂)`
drops a margin `d` below `log₂ (n₂ !)`, this is a `2 ^ (−d)` fraction of the `n₂ !` environments:
the coarse law costs two lines, yet the world entire is unaffordable to all but a vanishing few. -/
theorem card_readable_core_le {n₁ n₂ : ℕ} (U₁ : Perm (Fin n₁)) (b : ℕ) (hn₁ : 0 < n₁) :
    {U₂ : Perm (Fin n₂) | ∃ (k : ℕ) (ℓ : ℕ → Fin (n₁ * n₂) → Fin k),
        PermCarries (prodWorldFin U₁ U₂) ℓ ∧ Function.Bijective (ℓ 0) ∧ UniformBudget ℓ b}.ncard
      ≤ 2 ^ (2 * b + (15 + elen dbl) * Nat.size n₂
          + (elen splitSndBuilder + elen icode + 4 * (15 + elen dbl) + 18) + 1) := by
  set s := 2 * b + (15 + elen dbl) * Nat.size n₂
      + (elen splitSndBuilder + elen icode + 4 * (15 + elen dbl) + 18) with hs
  refine le_trans (Set.ncard_le_ncard_of_injOn (fun U₂ : Perm (Fin n₂) => lensCode ⇑U₂) ?_ ?_
    (AdditiveComplexity.finite_KE_le s)) (AdditiveComplexity.card_KE_le s)
  · rintro U₂ ⟨k, ℓ, hcar, hbij, hbud⟩
    exact KE_factorSnd_le_of_faithful hcar hbij hbud hn₁
  · intro U V _ _ h
    exact DFunLike.coe_injective (lensCode_injective h)

/-! #### The macro reading, owned in the capacity vocabulary

The (U)-positive clause, priced in the world's own KE currency by `KE_flatWorld_le`, restated as a
lower bound on the world's uniform *entropic capacity* `CbHue` ([Persistence] §2, Definition 2.2 +
§5, Definition 5.5). When the macro law `G` is a permutation the reading is genuinely *owned*: one
program computes the whole time-indexed family that reads the macro state back, so its carried
entropy — the relabelling orbit of the reference frame on the recurrent core — is affordable at the
law's own budget. Reversibility is where it is needed: the reading's persistence transports the
macro state backwards along the `G`-orbit, which only a permutation supports. -/

/-- The flat habitat world's **macro reading**: relabel onto blocks, decode each. -/
def flatRead (κ k : ℕ) (x : Mem (Fin (κ * 3 ^ k)) Bool) : Mem (Fin κ) Bool :=
  macroLens κ k ((flatHab κ k).symm x)

/-- The macro reading, transported onto the numeral carrier the capacities are indexed by. -/
def packRead (κ k : ℕ) : Fin (2 ^ (κ * 3 ^ k)) → Fin (2 ^ κ) := packLens (flatRead κ k)

private theorem flatRead_surjective (κ k : ℕ) : Function.Surjective (flatRead κ k) := by
  intro b
  obtain ⟨h, hh⟩ := macroLens_surjective κ k b
  exact ⟨flatHab κ k h, by rw [flatRead, Equiv.symm_apply_apply, hh]⟩

private theorem packRead_surjective (κ k : ℕ) : Function.Surjective (packRead κ k) :=
  packLens_surjective (flatRead_surjective κ k)

/-- **The reading intertwines the flat world with the macro law**: reading after a step is a step of
`G` after reading, on the numeral carrier — `flatWorld` conjugates `habitatWorld`, `macroLens` reads
`G` off it, and the packing preserves the square. -/
private theorem packRead_square (κ k : ℕ) (G : Mem (Fin κ) Bool → Mem (Fin κ) Bool)
    (s : Fin (2 ^ (κ * 3 ^ k))) :
    packRead κ k (packWorld (flatWorld κ k G) s) = packWorld G (packRead κ k s) := by
  refine packWorld_square (fun x => ?_) s
  rw [flatRead, flatRead, flatWorld, Equiv.symm_apply_apply, macro_square]

/-- **The reading's table**, tabulated over every state as one function of the paired input
`⟨κ, k⟩` — the reading has no other parameter, so nothing about `G` or the environment enters. -/
private def readTableFn (a : ℕ) : ℕ :=
  Encodable.encode ((List.range (2 ^ (a.unpair.1 * 3 ^ a.unpair.2))).map
    (fun s => macroWordOf a.unpair.1 a.unpair.2 s))

private theorem primrec_readTableFn : Primrec readTableFn := by
  have hpow : Primrec₂ ((· ^ ·) : ℕ → ℕ → ℕ) := Primrec₂.unpaired'.1 Nat.Primrec.pow
  have hκ : Primrec fun a : ℕ => a.unpair.1 := Primrec.fst.comp Primrec.unpair
  have hk : Primrec fun a : ℕ => a.unpair.2 := Primrec.snd.comp Primrec.unpair
  have hN : Primrec fun a : ℕ => 2 ^ (a.unpair.1 * 3 ^ a.unpair.2) :=
    hpow.comp (Primrec.const 2) (Primrec.nat_mul.comp hκ (hpow.comp (Primrec.const 3) hk))
  have hinner : Primrec₂ fun (a : ℕ) (s : ℕ) => macroWordOf a.unpair.1 a.unpair.2 s :=
    Primrec₂.mk (primrec_macroWordOf.comp
      (Primrec.pair (Primrec.pair (hκ.comp Primrec.fst) (hk.comp Primrec.fst)) Primrec.snd))
  exact Primrec.encode.comp (Primrec.list_map (Primrec.list_range.comp hN) hinner)

/-- **The reading's table is the packed macro reading's**: both list along `List.range`, closed
per-entry by `macroWordOf_stateEquiv` through the `List.range` normal form — the huge length never
unifies an index. -/
private theorem readTableFn_eq (κ k : ℕ) :
    readTableFn (Nat.pair κ k) = lensCode (packRead κ k) := by
  rw [readTableFn]
  simp only [Nat.unpair_pair]
  conv_rhs => rw [packRead, lensCode, lensTable_range]
  congr 1
  refine List.map_congr_left fun s hs => ?_
  have hsN : s < 2 ^ (κ * 3 ^ k) := List.mem_range.mp hs
  rw [dif_pos hsN]
  obtain ⟨h, hh⟩ : ∃ h, (stateEquiv (κ * 3 ^ k) (flatHab κ k h) : Fin (2 ^ (κ * 3 ^ k)))
      = ⟨s, hsN⟩ := by
    refine ⟨(flatHab κ k).symm ((stateEquiv (κ * 3 ^ k)).symm ⟨s, hsN⟩), ?_⟩
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  have hlhs : macroWordOf κ k s = ((stateEquiv κ (macroLens κ k h) : Fin (2 ^ κ)) : ℕ) := by
    conv_lhs => rw [show s = ((stateEquiv (κ * 3 ^ k) (flatHab κ k h) : Fin (2 ^ (κ * 3 ^ k))) : ℕ)
      from by rw [hh]]
    exact macroWordOf_stateEquiv κ k h
  have hrhs : ((packLens (flatRead κ k) ⟨s, hsN⟩ : Fin (2 ^ κ)) : ℕ)
      = ((stateEquiv κ (macroLens κ k h) : Fin (2 ^ κ)) : ℕ) := by
    rw [← hh, packLens_apply, flatRead, Equiv.symm_apply_apply]
  rw [hlhs, hrhs]

private theorem partrec_readTableFn : Nat.Partrec (fun a : ℕ => (readTableFn a : ℕ)) :=
  _root_.Partrec.nat_iff.mp (Primrec.to_comp primrec_readTableFn).partrec

/-- **The fixed reading builder code**: one program taking `⟨κ, k⟩` and returning the reading's
table — the decoder, uniform in the structural sizes and free of `G`. -/
noncomputable def readBuilder : Nat.Partrec.Code :=
  Classical.choose (Nat.Partrec.Code.exists_code.mp partrec_readTableFn)

private theorem eval_readBuilder (a : ℕ) :
    Nat.Partrec.Code.eval readBuilder a = Part.some (readTableFn a) := by
  have h := congrFun (Classical.choose_spec
    (Nat.Partrec.Code.exists_code.mp partrec_readTableFn)) a
  simpa [readBuilder] using h

/-- **The owned reading family**: at frame `t`, read the macro state and transport it `t` steps back
along the macro law. Where `G` is a permutation this is `⇑((packPerm G)^t)⁻¹ ∘ packRead`, and it
carries the persistent macro model — the reference frame is the reading itself. -/
private def ownLens (κ k : ℕ) (G : Perm (Mem (Fin κ) Bool)) :
    ℕ → Fin (2 ^ (κ * 3 ^ k)) → Fin (2 ^ κ) :=
  fun t s => ⇑((packPerm G ^ t)⁻¹) (packRead κ k s)

private theorem ownLens_zero (κ k : ℕ) (G : Perm (Mem (Fin κ) Bool)) :
    ownLens κ k G 0 = packRead κ k := by
  funext s; simp [ownLens]

/-- **The family carries the macro model** over the flat habitat world. The reading intertwines the
world with the macro law (`packRead_square`), so `t` steps of the world advance the macro state by
`⇑((packPerm G)^t)`; transporting it back by the inverse recovers the reference reading.
Reversibility enters exactly here — the inverse iterate needs `G` a permutation. -/
private theorem carries_ownLens (κ k : ℕ) (G : Perm (Mem (Fin κ) Bool)) :
    Carries (packWorld (flatWorld κ k ⇑G)) (ownLens κ k G) := by
  have hsq : Intertwines (packWorld (flatWorld κ k ⇑G)) (packWorld ⇑G) (fun _ => packRead κ k) :=
    fun _ s => packRead_square κ k ⇑G s
  refine ⟨by rw [ownLens_zero]; exact packRead_surjective κ k, fun t s => ?_⟩
  have hit := hsq.iterate t s
  have hpow : (packWorld (⇑G))^[t] = ⇑((packPerm G) ^ t) := by
    rw [← packPerm_coe, ← Equiv.Perm.coe_pow]
  simp only [ownLens]
  rw [hit, hpow]
  simp

/-- **The family is owned at the macro law's own budget plus logarithms.** One fixed program
computes every frame: the macro law's code `cG` recovers the law's table (composed, so additive),
`faithBuilder` transports the identity frame `t` steps, `readBuilder` supplies the decoder from
`⟨κ, k⟩` alone, and `compBuilder` composes the two. The reading enters as a **code**, not its
exponential table — fed the two small structural numbers, `readBuilder` rebuilds it — so the whole
time-indexed family costs
`elen cG + O(size κ + size k)`, nothing scaling with the state count. -/
private theorem uniformBudget_ownLens (κ k : ℕ) (G : Perm (Mem (Fin κ) Bool))
    (cG : Nat.Partrec.Code) (hG : cG.eval 0 = Part.some (lensCode (packWorld ⇑G))) :
    UniformBudget (ownLens κ k G)
      (elen compBuilder + elen faithBuilder + elen readBuilder + elen cG
        + (15 + elen dbl) * Nat.size (Nat.pair κ k) + ((15 + elen dbl) + 30)) := by
  refine ⟨Nat.Partrec.Code.comp compBuilder
    (Nat.Partrec.Code.pair
      (Nat.Partrec.Code.comp faithBuilder
        (Nat.Partrec.Code.pair (Nat.Partrec.Code.comp cG Nat.Partrec.Code.zero)
          Nat.Partrec.Code.id))
      (Nat.Partrec.Code.comp readBuilder (bconst (Nat.pair κ k)))), ?_, ?_⟩
  · have hz : elen Nat.Partrec.Code.zero = 3 := rfl
    have hid : elen Nat.Partrec.Code.id = 9 := rfl
    have hb := elen_bconst_le (Nat.pair κ k)
    simp only [E_len_comp, E_len_pair, hz, hid]
    omega
  · intro t
    have hz : Nat.Partrec.Code.eval Nat.Partrec.Code.zero t = Part.some 0 := rfl
    have hcg : Nat.Partrec.Code.eval (Nat.Partrec.Code.comp cG Nat.Partrec.Code.zero) t
        = Part.some (lensCode ⇑(packPerm G)) := by rw [eval_comp_some hz, hG, packPerm_coe]
    have hpair1 : Nat.Partrec.Code.eval (Nat.Partrec.Code.pair
        (Nat.Partrec.Code.comp cG Nat.Partrec.Code.zero) Nat.Partrec.Code.id) t
        = Part.some (Nat.pair (lensCode ⇑(packPerm G)) t) := by
      change Nat.pair <$> _ <*> _ = _
      rw [hcg, Nat.Partrec.Code.eval_id]; simp [Seq.seq]
    have hfaith : Nat.Partrec.Code.eval (Nat.Partrec.Code.comp faithBuilder
        (Nat.Partrec.Code.pair (Nat.Partrec.Code.comp cG Nat.Partrec.Code.zero)
          Nat.Partrec.Code.id)) t = Part.some (lensCode ⇑((packPerm G ^ t)⁻¹)) := by
      rw [eval_comp_some hpair1, eval_faithBuilder, faithTableFn_eq]
    have hread : Nat.Partrec.Code.eval
        (Nat.Partrec.Code.comp readBuilder (bconst (Nat.pair κ k))) t
        = Part.some (lensCode (packRead κ k)) := by
      rw [eval_comp_some (eval_bconst (Nat.pair κ k) t), eval_readBuilder, readTableFn_eq]
    have hpair2 : Nat.Partrec.Code.eval (Nat.Partrec.Code.pair
        (Nat.Partrec.Code.comp faithBuilder (Nat.Partrec.Code.pair
          (Nat.Partrec.Code.comp cG Nat.Partrec.Code.zero) Nat.Partrec.Code.id))
        (Nat.Partrec.Code.comp readBuilder (bconst (Nat.pair κ k)))) t
        = Part.some (Nat.pair (lensCode ⇑((packPerm G ^ t)⁻¹)) (lensCode (packRead κ k))) := by
      change Nat.pair <$> _ <*> _ = _
      rw [hfaith, hread]; simp [Seq.seq]
    rw [eval_comp_some hpair2, eval_compBuilder, compTableFn_eq]
    rfl

/-- **The macro reading is owned, in the capacity vocabulary** ([Persistence] §2, Definition 2.2 +
§5, Definition 5.5 — the (U)-positive clause). When the macro law `G` is a permutation, the flat
habitat world's uniform *entropic capacity* at budget `elen cG + O(size κ + size k)` is at least the
carried entropy of the macro reading: the relabelling orbit of its reference frame on the recurrent
core. The world's rule is cheap (`KE_flatWorld_le`) and, at that same budget, it is genuinely
*owned* — one program reads the macro state back forever. -/
theorem CbHue_flatWorld_ge (κ k : ℕ) (G : Perm (Mem (Fin κ) Bool)) (cG : Nat.Partrec.Code)
    (hG : cG.eval 0 = Part.some (lensCode (packWorld ⇑G))) :
    Nat.card ↥(orbit (Perm ↥(core (packWorld (flatWorld κ k ⇑G))))
        (coreLens (packWorld (flatWorld κ k ⇑G)) (packRead κ k)))
      ≤ CbHue (packWorld (flatWorld κ k ⇑G))
          (elen compBuilder + elen faithBuilder + elen readBuilder + elen cG
            + (15 + elen dbl) * Nat.size (Nat.pair κ k) + ((15 + elen dbl) + 30)) := by
  have h := CbHue_ge_of_uniform (carries_ownLens κ k G) (uniformBudget_ownLens κ k G cG hG)
  rwa [ownLens_zero] at h

/-! #### The recurrent core, identified

`omegaLimit_witnessWorld_subset` places the recurrent core inside the codeword-habitat states. When
`G` and `π` are permutations the inclusion is an **equality**: every codeword-habitat state is
recurrent, because a permutation's iterate is onto — running the world `t` steps backwards (invert
`G^t` on the macro state, `π^t` on the environment) exhibits a preimage at every `t`. So the core is
exactly codewords beside the environment: the genuine permutation on which a faithful reading, and
hence the contrast of `card_readable_core_le`, lives. -/

/-- **The witness world's iterate factors**: `t` steps of the whole world are `t` steps of the
habitat beside `t` steps of the environment. -/
private theorem witnessWorld_iterate_apply {ι_J : Type*} (κ k : ℕ)
    (G : Mem (Fin κ) Bool → Mem (Fin κ) Bool) (π : Mem ι_J Bool → Mem ι_J Bool)
    (t : ℕ) (x : Mem ((Fin κ × Fin (3 ^ k)) ⊕ ι_J) Bool) :
    (witnessWorld κ k G π)^[t] x
      = Sum.elim ((habitatWorld κ k G)^[t] (x ∘ Sum.inl)) (π^[t] (x ∘ Sum.inr)) := by
  induction t generalizing x with
  | zero => simp only [Function.iterate_zero, id_eq]; funext c; cases c <;> rfl
  | succ t ih =>
      rw [Function.iterate_succ_apply', ih]
      simp only [witnessWorld, Sum.elim_comp_inl, Sum.elim_comp_inr, Function.iterate_succ_apply']

/-- **On codewords the habitat runs the macro law**: `t` steps of the habitat world from a codeword
state advance its macro word by `G^t`, re-encoded. -/
private theorem habitatWorld_iterate_codeword (κ k : ℕ) (G : Perm (Mem (Fin κ) Bool)) (t : ℕ)
    (c : Mem (Fin κ) Bool) :
    (habitatWorld κ k ⇑G)^[t] (habitatEnc κ k c) = habitatEnc κ k (⇑(G ^ t) c) := by
  induction t generalizing c with
  | zero => simp
  | succ t ih =>
      rw [Function.iterate_succ_apply]
      have hstep : habitatWorld κ k ⇑G (habitatEnc κ k c) = habitatEnc κ k (⇑G c) := by
        rw [habitatWorld, macroLens_habitatEnc]
      rw [hstep, ih, pow_succ, Equiv.Perm.mul_apply]

/-- **The recurrent core is codewords beside the environment.** For permutation `G, π` the inclusion
of `omegaLimit_witnessWorld_subset` is an equality: the states surviving forever are exactly those
whose habitat block-content is a codeword, the environment ranging freely. -/
theorem omegaLimit_witnessWorld_eq {ι_J : Type*} (κ k : ℕ)
    (G : Perm (Mem (Fin κ) Bool)) (π : Perm (Mem ι_J Bool)) :
    core (witnessWorld κ k ⇑G ⇑π)
      = {x : Mem ((Fin κ × Fin (3 ^ k)) ⊕ ι_J) Bool | ∃ b, x ∘ Sum.inl = habitatEnc κ k b} := by
  refine Set.Subset.antisymm (omegaLimit_witnessWorld_subset κ k ⇑G ⇑π) ?_
  rintro x ⟨b, hb⟩
  rw [core, Set.mem_iInter]
  intro t
  refine ⟨Sum.elim (habitatEnc κ k (⇑(G ^ t)⁻¹ b)) (⇑(π ^ t)⁻¹ (x ∘ Sum.inr)),
    Set.mem_univ _, ?_⟩
  rw [witnessWorld_iterate_apply, Sum.elim_comp_inl, Sum.elim_comp_inr,
    habitatWorld_iterate_codeword, ← Equiv.Perm.coe_pow]
  have hg : ⇑(G ^ t) (⇑(G ^ t)⁻¹ b) = b := by simp
  have hp : ⇑(π ^ t) (⇑(π ^ t)⁻¹ (x ∘ Sum.inr)) = x ∘ Sum.inr := by simp
  rw [hg, hp, ← hb]
  exact Sum.elim_comp_inl_inr x

/-- **On the core, the world is the product permutation.** A codeword-habitat state steps to the
codeword of `⇑G b` beside `⇑π` of the environment: on the recurrent core
(`omegaLimit_witnessWorld_eq`) the witness world is exactly `(enc ∘ G ∘ dec) × π`, the explicit
permutation the attractor carries — the identification that escapes the basin-address wall, made
concrete. -/
theorem witnessWorld_codeword {ι_J : Type*} (κ k : ℕ) (G : Perm (Mem (Fin κ) Bool))
    (π : Perm (Mem ι_J Bool)) (b : Mem (Fin κ) Bool) (env : Mem ι_J Bool) :
    witnessWorld κ k ⇑G ⇑π (Sum.elim (habitatEnc κ k b) env)
      = Sum.elim (habitatEnc κ k (⇑G b)) (⇑π env) := by
  simp only [witnessWorld, habitatWorld, Sum.elim_comp_inl, Sum.elim_comp_inr, macroLens_habitatEnc]

/-! #### The package

`witness_world` gathers the construction into one statement of record. For every `κ, k`, permutation
macro law `G` and environment `π`, the designed world `W(κ, k, G, π)` hosts a reading that

* is **surjective** — one full bit per block, a `κ`-bit macro state (`witnessLens_surjective`);
* obeys `G` **exactly, from every initial state**, whatever the environment is doing beside it
  (`intertwines_witnessLens` — the exact square, no transient);
* is **robust** to any perturbation of fewer than `2 ^ k` cells, with margin at least `2 ^ k − 1`
  on the `κ · 3 ^ k` habitat cells, however large the environment (`witnessWorld_margin_ge`);
* is **cheaply owned** — one fixed program reads the macro state back at every frame, so the flat
  world's uniform entropic capacity `CbHue` at budget `elen cG + O(size κ + size k)` is at least the
  reading's carried entropy, its reference-frame relabelling orbit on the recurrent core
  (`CbHue_flatWorld_ge`, the (U)-positive clause in the capacity vocabulary; `KE_flatWorld_le` is
  the same content in the world's own KE currency); and
* crosses the **internalization threshold** — the habitat's `κ` macro bits host the [Decoupling]
  §6.3 bounded checker for every Gödel number `g` within the capacity
  (`hostsThreshold_of_capacity`).

The surjectivity, lawfulness, robustness and threshold clauses hold for an arbitrary *endofunction*
`G` (a nonempty habitat `0 < κ` for the margin to fit the memory); the ownership clause takes `G` a
permutation, where the reading's persistence — transporting the macro state back along the
`G`-orbit — is available. The construction's sixth clause — the negative half, that the *typical*
member is
unreadable in full — is the companion `card_readable_core_le` above, stated over the recurrent core
(a genuine permutation whose environment factor is incompressible for all but a vanishing fraction
of environments) rather than folded in here, since it quantifies over the *family* of environments,
not a single one. Together they are the affordability ladder in one place: every member hosts a
robust, lawful, cheaply-owned reading crossing the internalization threshold, while its typical
member is unaffordable to read entire.

Anchors: [Persistence] §5, §7, §8, §10.1 + [Decoupling] §6. This conjunction is a synthesis of the
development; **no numbered proposition of [Persistence] is claimed machine-checked** by it — the
paper does not yet state this theorem, deliberately, pending how the Witness World enters its
prose. -/
theorem witness_world {ι_J : Type*} [Fintype ι_J] [Nonempty (Mem ι_J Bool)] (κ k : ℕ)
    (hκ : 0 < κ) (G : Perm (Mem (Fin κ) Bool)) (π : Mem ι_J Bool → Mem ι_J Bool)
    (cG : Nat.Partrec.Code) (hG : cG.eval 0 = Part.some (lensCode (packWorld ⇑G))) :
    Function.Surjective (witnessLens (ι_J := ι_J) κ k) ∧
    Intertwines (witnessWorld κ k ⇑G π) ⇑G (fun _ => witnessLens κ k) ∧
    2 ^ k - 1 ≤ margin (witnessWorld κ k ⇑G π)
      (Set.univ : Set (Mem ((Fin κ × Fin (3 ^ k)) ⊕ ι_J) Bool)) (witnessLens κ k) ∧
    Nat.card ↥(orbit (Perm ↥(core (packWorld (flatWorld κ k ⇑G))))
        (coreLens (packWorld (flatWorld κ k ⇑G)) (packRead κ k)))
      ≤ CbHue (packWorld (flatWorld κ k ⇑G))
          (elen compBuilder + elen faithBuilder + elen readBuilder + elen cG
            + (15 + elen dbl) * Nat.size (Nat.pair κ k) + ((15 + elen dbl) + 30)) ∧
    (∀ g, GodelInternalization.capacity (Nat.clog 2 (g + 1)) ≤ κ → hostsThreshold κ g) :=
  ⟨witnessLens_surjective κ k, intertwines_witnessLens κ k ⇑G π,
    witnessWorld_margin_ge κ k ⇑G π hκ, CbHue_flatWorld_ge κ k G cG hG,
    fun _ h => hostsThreshold_of_capacity h⟩

end WitnessWorldPackage

end Margin

/-! ## Emergence: pricing the ceiling ([Persistence] §2, §5 + [Decoupling] §3.5)

`capacity_core_ge` exhibits, for `2 ^ κ ≤ |core U|`, a family carrying a `κ`-bit model over any
world `U` — lawful from *every* initial state, because it flows into the recurrent core (`U^[N]`)
before co-moving with the recurrent rule. What that construction does not do is **own** the family.
This section prices it: the guest is computed by one fixed program from a code for the world's table
and a code for the reference frame, so its carried entropy is affordable — the first theorem of the
emergence programme, "a big-enough core and an affordable rule host an owned guest".

The reversible case is `ownership` composed with `CbHu_ge_of_uniform`. The irreversible case is the
same shape with one twist: on the recurrent core `U` acts as a permutation of order dividing `n !`,
so its inverse there is a *forward* power — `(U ↾ core)⁻¹ = corePerm ^ (n ! − 1)` — and the whole
co-moving-after-flow-in family collapses to a single forward iterate `θ ∘ U^[(n ! − 1) · t + n]`. No
core inverse, no stabilization search, no irreducible bounded minimization: the guest's table at
frame `t` is `U`'s table iterated a computable number of times, read through the frame.

Anchors: [Persistence] §2 + §5 + [Decoupling] §3.5. No numbered result is claimed machine-checked by
this section's presence; it prices a construction the papers state without a price. -/

section Emergence

open Equiv MulAction

attribute [local instance] arrowAction

/-- **The priced ceiling for reversible hosts.** Over a permutation world `U`, any surjective
reference frame `ℓ₀` given by a code is *owned*: the canonical family `ℓ_t = (U ^ t) • ℓ₀` is
computed by one program of length `elen cℓ + elen cU + O(1)` (`ownership`), so the world's uniform
entropic capacity at that budget is at least `ℓ₀`'s relabelling-class size. The reversible case of
the emergence bound, with the witness world's habitat structure dropped — an arbitrary owned frame
over an arbitrary permutation host. -/
theorem CbHu_ge_owned {n m : ℕ} (U : Perm (Fin n)) (ℓ₀ : Fin n → Fin m)
    (cℓ cU : Nat.Partrec.Code) (hsurj : Function.Surjective ℓ₀)
    (hℓ : cℓ.eval 0 = Part.some (lensCode ℓ₀)) (hU : cU.eval 0 = Part.some (lensCode ⇑U)) :
    Nat.card ↥(orbit (Perm (Fin n)) ℓ₀)
      ≤ CbHu U (elen cℓ + elen cU + (elen ownBuilder + 30)) := by
  have h := CbHu_ge_of_uniform (permCarries_smul hsurj) (ownership cℓ cU hℓ hU)
  simpa using h

/-- **The emergence guest**: read the model off the recurrent core after flowing into it, co-moving
with the recurrent rule by a single **forward** power. On the core `U` is a permutation of order
dividing `n !`, so its inverse there is `corePerm ^ (n ! − 1)` and the whole
co-move-after-flow-in family is `θ ∘ U^[(n ! − 1) · t + n]` — no core inverse, no bounded search. -/
def emergeLens {n m : ℕ} (U : Fin n → Fin n) (θ : Fin n → Fin m) : ℕ → Fin n → Fin m :=
  fun t s => θ (U^[(Nat.factorial n - 1) * t + n] s)

/-- **The emergence guest carries the model, from every initial state.** After `n` steps every state
is in the recurrent core (`iterate_mem_core`); there `U` has order dividing `n !`, so `n ! · t`
further steps return to where they started, and the forward-power co-moving frame reads back the
time-`0` value. The only hypothesis is that the frame reads a full model off the core. -/
theorem carries_emergeLens {n m : ℕ} (U : Fin n → Fin n) (θ : Fin n → Fin m)
    (hsurj : Function.Surjective (fun s => θ (U^[n] s))) :
    Carries U (emergeLens U θ) := by
  classical
  have : Fintype ↥(core U) := Fintype.ofFinite _
  have hord : orderOf (corePerm U) ∣ Nat.factorial n := by
    refine dvd_trans orderOf_dvd_card ?_
    rw [Fintype.card_perm]
    exact Nat.factorial_dvd_factorial (by rw [← Nat.card_eq_fintype_card]; exact card_core_le U)
  have hpow1 : corePerm U ^ (Nat.factorial n) = 1 := orderOf_dvd_iff_pow_eq_one.mp hord
  have hfix : ∀ y : Fin n, y ∈ core U → U^[Nat.factorial n] y = y := by
    intro y hy
    have h := corePerm_pow_apply U (Nat.factorial n) ⟨y, hy⟩
    rw [hpow1] at h
    simpa using h.symm
  refine ⟨?_, fun t s => ?_⟩
  · have h0 : emergeLens U θ 0 = fun s => θ (U^[n] s) := by
      funext s; simp only [emergeLens, Nat.mul_zero, Nat.zero_add]
    rw [h0]; exact hsurj
  · have hmem : U^[n] s ∈ core U :=
      iterate_mem_core U (Nat.card_eq_fintype_card.trans (Fintype.card_fin n)).le s
    simp only [emergeLens]
    rw [Nat.mul_zero, Nat.zero_add, ← Function.iterate_add_apply]
    congr 1
    have hexp : (Nat.factorial n - 1) * t + n + t = Nat.factorial n * t + n := by
      rw [Nat.sub_one_mul]
      have hle : t ≤ Nat.factorial n * t := Nat.le_mul_of_pos_left t (Nat.factorial_pos n)
      omega
    rw [hexp, Function.iterate_add_apply, Function.iterate_mul]
    exact Function.iterate_fixed (hfix _ hmem) t

/-- The factorial is primitive recursive — the exponent's one non-trivial ingredient. -/
private theorem primrec_factorial : Primrec Nat.factorial := by
  have hstep : Primrec₂ fun (m ih : ℕ) => (m + 1) * ih :=
    (Primrec.nat_mul.comp (Primrec.succ.comp Primrec.fst) Primrec.snd).to₂
  refine (Primrec.nat_rec₁ 1 hstep).of_eq fun n => ?_
  induction n with
  | zero => rfl
  | succ k ih => rw [Nat.factorial_succ, ← ih]

/-- **The emergence builder's table**: from `⟨U's table, θ's table, t⟩`, iterate `U`'s table
`(n ! − 1) · t + n` times (`iterTable`, `n` read off the table's own length) and read the result
through `θ` (`stepComp`) — the guest's frame-`t` table, all forward, no inverse. -/
private def emergeTableFn (a : ℕ) : ℕ :=
  Encodable.encode (stepComp ((Encodable.decode (α := List ℕ) a.unpair.2.unpair.1).getD [])
    (iterTable ((Encodable.decode (α := List ℕ) a.unpair.1).getD [])
      ((Nat.factorial ((Encodable.decode (α := List ℕ) a.unpair.1).getD []).length - 1)
        * a.unpair.2.unpair.2 + ((Encodable.decode (α := List ℕ) a.unpair.1).getD []).length)))

private theorem primrec_emergeTableFn : Primrec emergeTableFn := by
  have hP : Primrec fun a : ℕ => (Encodable.decode (α := List ℕ) a.unpair.1).getD [] :=
    Primrec.option_getD.comp (Primrec.decode.comp (Primrec.fst.comp Primrec.unpair))
      (Primrec.const [])
  have hQ : Primrec fun a : ℕ => (Encodable.decode (α := List ℕ) a.unpair.2.unpair.1).getD [] :=
    Primrec.option_getD.comp
      (Primrec.decode.comp (Primrec.fst.comp (Primrec.unpair.comp
        (Primrec.snd.comp Primrec.unpair)))) (Primrec.const [])
  have ht : Primrec fun a : ℕ => a.unpair.2.unpair.2 :=
    Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))
  have hn : Primrec fun a : ℕ => ((Encodable.decode (α := List ℕ) a.unpair.1).getD []).length :=
    Primrec.list_length.comp hP
  have hexpo : Primrec fun a : ℕ =>
      (Nat.factorial ((Encodable.decode (α := List ℕ) a.unpair.1).getD []).length - 1)
        * a.unpair.2.unpair.2 + ((Encodable.decode (α := List ℕ) a.unpair.1).getD []).length :=
    Primrec.nat_add.comp
      (Primrec.nat_mul.comp (Primrec.nat_sub.comp (primrec_factorial.comp hn) (Primrec.const 1)) ht)
      hn
  exact Primrec.encode.comp
    (primrec_stepComp.comp hQ (primrec_iterTable.comp hP hexpo))

/-- **The builder is correct**: on `⟨U's table, θ's table, t⟩` it outputs exactly the guest's
frame-`t` table. Both bridges are in-tree — `iterTable_lensTable` tabulates the iterate,
`stepComp_lensTable_comp` composes the frame — so the table lists over `Fin n`, never an exponential
alphabet. -/
private theorem emergeTableFn_eq {n m : ℕ} (U : Fin n → Fin n) (θ : Fin n → Fin m) (t : ℕ) :
    emergeTableFn (Nat.pair (lensCode U) (Nat.pair (lensCode θ) t))
      = lensCode (emergeLens U θ t) := by
  rw [emergeTableFn]
  simp only [Nat.unpair_pair, decode_lensCode, lensTable_length]
  rw [iterTable_lensTable, stepComp_lensTable_comp]
  rfl

private theorem partrec_emergeTableFn : Nat.Partrec (fun a : ℕ => (emergeTableFn a : ℕ)) :=
  _root_.Partrec.nat_iff.mp (Primrec.to_comp primrec_emergeTableFn).partrec

/-- **The fixed emergence builder code**: one program taking `⟨U's table, θ's table, t⟩`. -/
noncomputable def emergeBuilder : Nat.Partrec.Code :=
  Classical.choose (Nat.Partrec.Code.exists_code.mp partrec_emergeTableFn)

private theorem eval_emergeBuilder (a : ℕ) :
    Nat.Partrec.Code.eval emergeBuilder a = Part.some (emergeTableFn a) := by
  have h := congrFun (Classical.choose_spec
    (Nat.Partrec.Code.exists_code.mp partrec_emergeTableFn)) a
  simpa [emergeBuilder] using h

/-- **The emergence guest is owned at the world's rule plus the frame, and nothing else.** One fixed
program of length `elen cU + elen cθ + O(1)` computes every frame: the world's code and the frame's
code, composed into `emergeBuilder`, which reads `n` off the table and does the arithmetic itself.
The clock `t` is the only per-frame input; no size parameter is loaded, because the exponent is
computed inside from the table rather than fed in. -/
theorem uniformBudget_emergeLens {n m : ℕ} (U : Fin n → Fin n) (θ : Fin n → Fin m)
    (cU cθ : Nat.Partrec.Code) (hU : cU.eval 0 = Part.some (lensCode U))
    (hθ : cθ.eval 0 = Part.some (lensCode θ)) :
    UniformBudget (emergeLens U θ) (elen emergeBuilder + elen cU + elen cθ + 30) := by
  refine ⟨Nat.Partrec.Code.comp emergeBuilder (Nat.Partrec.Code.pair
    (Nat.Partrec.Code.comp cU Nat.Partrec.Code.zero)
    (Nat.Partrec.Code.pair (Nat.Partrec.Code.comp cθ Nat.Partrec.Code.zero)
      Nat.Partrec.Code.id)), ?_, ?_⟩
  · have hz : elen Nat.Partrec.Code.zero = 3 := rfl
    have hid : elen Nat.Partrec.Code.id = 9 := rfl
    simp only [E_len_comp, E_len_pair, hz, hid]
    omega
  · intro t
    have hz : Nat.Partrec.Code.eval Nat.Partrec.Code.zero t = Part.some 0 := rfl
    have hcU : Nat.Partrec.Code.eval (Nat.Partrec.Code.comp cU Nat.Partrec.Code.zero) t
        = Part.some (lensCode U) := (eval_comp_some hz).trans hU
    have hcθ : Nat.Partrec.Code.eval (Nat.Partrec.Code.comp cθ Nat.Partrec.Code.zero) t
        = Part.some (lensCode θ) := (eval_comp_some hz).trans hθ
    have hp1 : Nat.Partrec.Code.eval (Nat.Partrec.Code.pair
        (Nat.Partrec.Code.comp cθ Nat.Partrec.Code.zero) Nat.Partrec.Code.id) t
        = Part.some (Nat.pair (lensCode θ) t) := by
      change Nat.pair <$> _ <*> _ = _
      rw [hcθ, Nat.Partrec.Code.eval_id]; simp [Seq.seq]
    have hp2 : Nat.Partrec.Code.eval (Nat.Partrec.Code.pair
        (Nat.Partrec.Code.comp cU Nat.Partrec.Code.zero)
        (Nat.Partrec.Code.pair (Nat.Partrec.Code.comp cθ Nat.Partrec.Code.zero)
          Nat.Partrec.Code.id)) t
        = Part.some (Nat.pair (lensCode U) (Nat.pair (lensCode θ) t)) := by
      change Nat.pair <$> _ <*> _ = _
      rw [hcU, hp1]; simp [Seq.seq]
    rw [eval_comp_some hp2, eval_emergeBuilder, emergeTableFn_eq]

/-- **Emergence: a big-enough core and an affordable rule host an owned guest, lawful from every
initial state** ([Persistence] §2 + §5 + [Decoupling] §3.5). Given codes for the world's table and
for a frame `θ` that reads a full `m`-valued model off the recurrent core (so `m ≤ |core U|`), the
guest `emergeLens U θ`:

* **carries the model from every initial state** — it flows into the core in `n` steps and then
  co-moves with the recurrent rule (`carries_emergeLens`), with no basin restriction; and
* is **owned** — computed by one program of length `elen cU + elen cθ + O(1)`, so the world's
  uniform entropic capacity at that budget is at least the guest's carried entropy, the relabelling
  orbit of its reference frame on the core.

Taking `m = 2 ^ κ` gives an owned `κ`-guest wherever the core has room for it — the first theorem of
the emergence programme, the priced counterpart of `capacity_core_ge` (which exhibits the guest but
does not own it). The irreversible case matches the reversible `CbHu_ge_owned` in shape; the twist
is that on the core the inverse is a forward power, so the whole construction stays a single forward
iterate. No numbered result is claimed machine-checked by this theorem. -/
theorem emergence {n m : ℕ} (U : Fin n → Fin n) (θ : Fin n → Fin m)
    (cU cθ : Nat.Partrec.Code) (hsurj : Function.Surjective (fun s => θ (U^[n] s)))
    (hU : cU.eval 0 = Part.some (lensCode U)) (hθ : cθ.eval 0 = Part.some (lensCode θ)) :
    Carries U (emergeLens U θ) ∧
    Nat.card ↥(orbit (Perm ↥(core U)) (coreLens U (emergeLens U θ 0)))
      ≤ CbHue U (elen emergeBuilder + elen cU + elen cθ + 30) :=
  ⟨carries_emergeLens U θ hsurj,
    CbHue_ge_of_uniform (carries_emergeLens U θ hsurj)
      (uniformBudget_emergeLens U θ cU cθ hU hθ)⟩

end Emergence

end PersistenceCapacity
