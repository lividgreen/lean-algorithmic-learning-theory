/-
Copyright (c) 2026 Mykola Palamarchuk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mykola Palamarchuk
-/
import ALT.CategoricalThreshold
import ALT.PersistenceCapacity

-- Formal-check file, not Mathlib-destined: opt out of the house-style linters.
set_option linter.style.header false
set_option linter.style.longLine false
-- Definitional `show`/`simp only [def]` (unfolding a class carrier to a defeq goal) is idiomatic here.
set_option linter.style.show false

/-!
# The expressiveness excess order: a graded representational class and its strict threshold

This module assembles two independently machine-checked strands — the [Decoupling] §6 categorical
threshold and the [Persistence] §5/§7 priced Witness World — into one **expressiveness order**, the
formal content of the sentence "the guest crosses an internalization threshold: its state space
represents statements about the host-and-itself that the host's evolution never decides".

The order has two layers.

* **The representational grade.** `RepClass w` is the class of realizability objects (`Asm`) that
  fit in `w` work bits (`CapacityLayer.FitsIn`), a filtration monotone in the budget
  (`RepClass_mono`) whose inclusions are *strict* exactly as the budget grows (`RepClass_subset_iff`:
  `RepClass w ⊆ RepClass w' ↔ w ≤ w'`). This grades objects by how much memory they need — the
  ordinary "priced domain" layer, with no reference to reflection.

* **The strict internalization clause.** `Outgrows κ` says: at every Gödel size `g` the budget `κ`
  can host ([Decoupling] §6.4 `hostsAt`), and every working budget `g < M_chk ≤ g²`, there is a
  genuine reflective object of the realizability CCC `Asm`, of working depth `M_chk`, whose bounded
  recursor fits in `κ` bits and which — under imported incompleteness at `g` — represents a
  true-but-underivable sentence. This is the *excess*: not "a bigger set of states" (the grade), but
  a state space deciding statements the host's own evolution leaves open. Its content is [Decoupling]
  §6.4 (`CategoricalThreshold.hostsAt_threshold`) packaged as a named predicate on the budget.

The order is **non-degenerate**: `outgrows_excludes` records its excluded region — a budget under the
Gödel-sentence size `⌈log₂(g+1)⌉` cannot host the threshold at all, so the strict clause is quantified
within genuine capacity, never sold on the empty `g = 0` case.

The capstone `witness_outgrows` places the two layers on one carrier: the [Persistence] §5/§7 Witness
World's guest (surjective, exactly `G`-lawful from every initial state, robust, and owned at
`O(K(G) + log κ + log k)`) *also* `Outgrows κ`. So the same cheaply-owned macro reading that carries
the host's law crosses the internalization threshold for every Gödel size within its carried capacity.

Provenance: [Decoupling] §6.3/§6.4 (the threshold side) and [Persistence] §5/§7 (the capacity side).
This synthesis is stated in **no** paper; **no numbered result is claimed machine-checked** by this
module. Each constituent — `CategoricalThreshold.hostsAt_threshold`, `PersistenceCapacity.witness_world`,
`CapacityLayer.FitsIn.mono` — is already axiom-clean; this module is the assembly.
-/

namespace ExcessOrder

open RealizabilityCCC RealizabilityRecursor
open PersistenceCapacity Decoupling AdditiveComplexity
open Equiv MulAction

-- `•` on the recurrent-core reading is the relabelling action `U • ℓ = ℓ ∘ U⁻¹`; the same local
-- instance `PersistenceCapacity.witness_world` is stated under (see its note on the pointwise clash).
attribute [local instance] arrowAction

/-! ### The representational grade

`RepClass w` is Rep(S) "up to capacity `w`" seen as a *class of objects* rather than a subcategory:
the realizability objects encoding into `w` work bits. It is the ordinary priced-domain layer of the
order — objects graded by memory, with no reference to reflection. -/

/-- **The representational grade at budget `w`** ([Decoupling] §4.2/§6.4): the realizability objects
`A : Asm` whose carrier fits in `w` work bits (`CapacityLayer.FitsIn A w` — finite, `≤ 2^w` elements).
The `w`-th level of the capacity filtration, as a class of objects. -/
def RepClass (w : ℕ) : Set Asm := {A | CapacityLayer.FitsIn A w}

/-- **The grade is monotone in the budget**: more work memory can only add objects. Directly the
capacity monotonicity `CapacityLayer.FitsIn.mono`. -/
theorem RepClass_mono {w w' : ℕ} (h : w ≤ w') : RepClass w ⊆ RepClass w' := by
  intro A hA
  simp only [RepClass, Set.mem_setOf_eq] at hA ⊢
  exact hA.mono h

/-- **The grade is a faithful order**: the inclusion `RepClass w ⊆ RepClass w'` holds **iff**
`w ≤ w'`. Monotonicity is `RepClass_mono`; the converse is separated by the bounded-recursor object
`recursorAsm (2^w − 1)`, whose carrier `ZMod (2^w)` has exactly `2^w` elements — so it fits in `w`
bits but overflows any strictly smaller budget. The grade therefore distinguishes every budget: the
representational levels are genuinely ordered, not eventually constant. -/
theorem RepClass_subset_iff {w w' : ℕ} : RepClass w ⊆ RepClass w' ↔ w ≤ w' := by
  refine ⟨fun hsub => ?_, RepClass_mono⟩
  by_contra hlt
  rw [not_le] at hlt
  have hpow : 0 < 2 ^ w := by positivity
  -- the separating object: carrier `ZMod (2^w)`, exactly `2^w` elements
  have hin : recursorAsm (2 ^ w - 1) ∈ RepClass w := by
    simp only [RepClass, Set.mem_setOf_eq]
    exact CapacityLayer.recursorAsm_fitsIn (2 ^ w - 1) w (by omega)
  have hout : CapacityLayer.FitsIn (recursorAsm (2 ^ w - 1)) w' := hsub hin
  have hcard : Nat.card (recursorAsm (2 ^ w - 1)).carrier = 2 ^ w := by
    have hc : Nat.card (recursorAsm (2 ^ w - 1)).carrier = (2 ^ w - 1) + 1 := by
      simp [Nat.card_eq_fintype_card, ZMod.card]
    omega
  have hle : 2 ^ w ≤ 2 ^ w' := by rw [← hcard]; exact hout.2
  have : w ≤ w' := (Nat.pow_le_pow_iff_right (by norm_num)).mp hle
  omega

/-! ### The strict internalization clause

The excess proper: not that the state space is *bigger*, but that it **decides** statements the host's
evolution leaves open. `Outgrows κ` names [Decoupling] §6.4's delivered reflective object as a
predicate on the budget `κ` and the subsystem's internal logic. -/

/-- **The internalization threshold, as a predicate on the budget** ([Decoupling] §6.3/§6.4). At every
Gödel size `g` the budget `κ` can host (`CategoricalThreshold.hostsAt κ g`) and every proof-code
working budget `g < M_chk ≤ g²`, the budget `κ` **outgrows** the host: there is a genuine reflective
object `R` of the realizability CCC `Asm` (Definition 6.1: Cartesian closed *and* a bounded recursor),
of working depth `M_chk`, whose recursor object fits in `κ` work bits, and which — under imported
incompleteness at `g` — represents a sentence that is true and underivable in the internal logic.

Quantified *within capacity* (`hostsAt κ g` as a hypothesis), so the excess is claimed only where the
budget genuinely hosts the threshold; `outgrows_excludes` records where that fails. -/
def Outgrows {Sentence : Type*} (κ : ℕ) (gnum : Sentence → ℕ)
    (Derivable True_ : Sentence → Prop) : Prop :=
  ∀ g Mchk, CategoricalThreshold.hostsAt κ g → g < Mchk → Mchk ≤ g ^ 2 →
    ∃ R : ReflectiveAsm g, R.depth = Mchk ∧
      CapacityLayer.FitsIn (recursorAsm R.depth) κ ∧
      (GodelThreshold.Incompleteness gnum Derivable True_ g →
        ∃ M, GodelThreshold.RepresentsUnderivableTruth gnum Derivable True_ M)

/-- **The internalization threshold holds at every budget** ([Decoupling] §6.4). `Outgrows κ` is
exactly `CategoricalThreshold.hostsAt_threshold` re-read as a predicate on `κ`: wherever the budget
hosts and the proof-code budget is degree-2, the delivered reflective object is realized at `κ` bits
and represents an underivable truth under incompleteness. -/
theorem outgrows {Sentence : Type*} (κ : ℕ) (gnum : Sentence → ℕ)
    (Derivable True_ : Sentence → Prop) : Outgrows κ gnum Derivable True_ :=
  fun _ _ hhost h1 h2 =>
    CategoricalThreshold.hostsAt_threshold gnum Derivable True_ hhost h1 h2

/-- **The order's excluded region (non-degeneracy)** ([Decoupling] §6.4). A budget under the
Gödel-sentence size `⌈log₂(g+1)⌉` cannot host the threshold for a theory of Gödel size `g` — the
linear capacity is the strictly larger `2⌈log₂(g+1)⌉`. This is the order's non-degeneracy witness:
the strict clause `Outgrows` is quantified within genuine capacity, and below the sentence size there
is no reflective object to deliver. (Directly `CategoricalThreshold.hostsAt_excludes`.) -/
theorem outgrows_excludes {κ g : ℕ} (h : κ < Nat.clog 2 (g + 1)) :
    ¬ CategoricalThreshold.hostsAt κ g :=
  CategoricalThreshold.hostsAt_excludes h

/-! ### The packaged excess theorem

`witness_outgrows` places the priced-domain layer and the internalization layer on one carrier: the
[Persistence] §5/§7 Witness World's cheaply-owned guest is *also* an object that outgrows its host. -/

/-- **The Witness World's guest crosses the internalization threshold** ([Persistence] §5/§7 +
[Decoupling] §6.3/§6.4). For a nonempty habitat (`0 < κ`), a permutation macro law `G` given by a code
`cG` (`hG`), and any environment `π`, the designed world `W(κ, k, G, π)` hosts a macro reading that is

* **surjective** — a full `κ`-bit macro state;
* exactly **`G`-lawful from every initial state** — the intertwining square, no transient;
* **robust** — margin at least `2^k − 1` against any perturbation of fewer than `2^k` cells;
* **cheaply owned** — one fixed program reads the macro state back at every frame, so the flat world's
  uniform entropic capacity `CbHue` at budget `elen cG + O(size κ + size k)` (i.e. `O(K(G) + log κ +
  log k)`) is at least the reading's carried entropy; and hosts the [Decoupling] §6.3 checker for
  every Gödel size within its `2^κ` macro states,

and additionally `Outgrows κ`: at every Gödel size the budget `κ` hosts and every degree-2 proof-code
budget, it delivers the genuine reflective object of the realizability CCC `Asm` that — under imported
incompleteness — represents a true-but-underivable sentence.

So the same owned reading that carries the host's law crosses the internalization threshold: it
represents statements about the host-and-itself that the host's evolution never decides.

This synthesis is stated in **no** paper; **no numbered result is claimed machine-checked** by it. The
first conjunct is `PersistenceCapacity.witness_world` verbatim; the second is `outgrows`. -/
theorem witness_outgrows {ι_J : Type*} [Fintype ι_J] [Nonempty (Mem ι_J Bool)]
    {Sentence : Type*} (gnum : Sentence → ℕ) (Derivable True_ : Sentence → Prop)
    (κ k : ℕ) (hκ : 0 < κ) (G : Perm (Mem (Fin κ) Bool)) (π : Mem ι_J Bool → Mem ι_J Bool)
    (cG : Nat.Partrec.Code) (hG : cG.eval 0 = Part.some (lensCode (packWorld ⇑G))) :
    (Function.Surjective (witnessLens (ι_J := ι_J) κ k) ∧
      Intertwines (witnessWorld κ k ⇑G π) ⇑G (fun _ => witnessLens κ k) ∧
      2 ^ k - 1 ≤ margin (witnessWorld κ k ⇑G π)
        (Set.univ : Set (Mem ((Fin κ × Fin (3 ^ k)) ⊕ ι_J) Bool)) (witnessLens κ k) ∧
      Nat.card ↥(orbit (Perm ↥(core (packWorld (flatWorld κ k ⇑G))))
          (coreLens (packWorld (flatWorld κ k ⇑G)) (packRead κ k)))
        ≤ CbHue (packWorld (flatWorld κ k ⇑G))
            (elen compBuilder + elen faithBuilder + elen readBuilder + elen cG
              + (15 + elen dbl) * Nat.size (Nat.pair κ k) + ((15 + elen dbl) + 30)) ∧
      (∀ g, GodelInternalization.capacity (Nat.clog 2 (g + 1)) ≤ κ → hostsThreshold κ g)) ∧
    Outgrows κ gnum Derivable True_ :=
  ⟨witness_world (ι_J := ι_J) κ k hκ G π cG hG, outgrows κ gnum Derivable True_⟩

end ExcessOrder
