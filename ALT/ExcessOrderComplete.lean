/-
Copyright (c) 2026 Mykola Palamarchuk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mykola Palamarchuk
-/
import ALT.ExcessOrder
import ALT.GodelComplete

-- Formal-check file, not Mathlib-destined: opt out of the house-style linters.
set_option linter.style.header false
set_option linter.style.longLine false

/-!
# The excess order at a concrete theory: discharging incompleteness inside `Outgrows`

`ALT/ExcessOrder.lean` states the internalization threshold as a predicate on the budget, and its
excess clause is deliberately **conditional**: at each Gödel size `g` it delivers a reflective object
that represents a true-but-underivable sentence *under* `GodelThreshold.Incompleteness … g` — a
hypothesis imported at that size, not proved there. `ALT/GodelComplete.lean` proves exactly that
hypothesis for arithmetic theories, against upstream `FormalizedFormalLogic/Foundation`.

This module composes the two, so the excess becomes **unconditional**: at a concrete theory there is
a Gödel size at which the reflective object represents an underivable truth outright, with no
incompleteness antecedent left standing.

* `outgrows_arith` — the adapter, for any `T` with `[T.Δ₁] [𝗥₀ ⪯ T] [ℕ↓[ℒₒᵣ] ⊧* T]`: a Gödel size
  `gTS` at which every degree-2 proof-code budget yields the reflective object of the realizability
  CCC `Asm`, fitting in `κ` work bits, together with a represented underivable truth.
* `outgrows_paMinus` — the same at `T = 𝗣𝗔⁻`, Foundation's *finite* fragment of Peano arithmetic:
  the most faithful witness, whose `Δ₁`-definability comes from finiteness (`Theory.Δ₁.ofFinite`)
  rather than from a definability theorem, so nothing beyond the standard axioms is used.
* `witness_outgrows_paMinus` — the capstone: the [Persistence] §5/§7 Witness World's cheaply-owned
  guest carries the host's law **and** unconditionally outgrows it at `𝗣𝗔⁻`.

The unconditional form is genuinely stronger than `ExcessOrder.witness_outgrows`, whose second
conjunct discharges nothing: there, "represents an underivable truth" is an implication that a reader
must still supply an incompleteness proof to use. Here the sentence is delivered.

Note the quantifier shape. Incompleteness supplies **one** Gödel size, so the unconditional statement
is `∃ gTS, ∀ Mchk, …` — existential in the size, universal in the proof-code budget — where the
conditional `Outgrows` is universal in both. That is the honest strength of the composition: the
excess is realized at a Gödel size the theory actually provides, not at every size uniformly.

A consequence worth reading off, since it is what keeps the statement from being over-read: the
hosting hypothesis is now pinned at *that* size. `gTS` is the encoding of the theory's own Gödel
sentence, so `CategoricalThreshold.hostsAt κ gTS` demands a budget that reaches it, and
`ExcessOrder.outgrows_excludes` rules out every `κ < Nat.clog 2 (gTS + 1)`. The guest outgrows the
host only once its carried capacity covers the sentence at issue — the threshold is crossed at a
concrete price, not for free at small `κ`.

Provenance: [Decoupling] §6.3/§6.4 + [Persistence] §5/§7. This synthesis is stated in **no** paper;
**no numbered result is claimed machine-checked** by this module. Each constituent —
`ExcessOrder.outgrows`, `GodelComplete.incompleteness_of_arith`, `PersistenceCapacity.witness_world`
— is already axiom-clean; this module is the composition.
-/

namespace ExcessOrder

open RealizabilityCCC RealizabilityRecursor
open PersistenceCapacity Decoupling AdditiveComplexity
open Equiv MulAction
open LO.FirstOrder LO.FirstOrder.Arithmetic

-- `•` on the recurrent-core reading is the relabelling action `U • ℓ = ℓ ∘ U⁻¹`, as in `ExcessOrder`.
attribute [local instance] arrowAction

/-- **The excess order at an arithmetic theory, with incompleteness discharged** ([Decoupling]
§6.3/§6.4). For any arithmetic theory `T` that is `Δ₁`-definable, interprets `𝗥₀`, and is true in `ℕ`,
there is a Gödel size `gTS` such that for every proof-code budget `gTS < Mchk ≤ gTS²` at which the
budget `κ` hosts, the delivered reflective object `R : ReflectiveAsm gTS` has working depth `Mchk`,
its bounded recursor fits in `κ` work bits, and it represents a sentence true in `ℕ` but underivable
in `T`.

This is `ExcessOrder.Outgrows` instantiated at `T`'s sentences with its incompleteness antecedent
**discharged** rather than assumed: `GodelComplete.incompleteness_of_arith` supplies the hypothesis
that `Outgrows` consumes. The size `gTS` is existentially quantified because incompleteness supplies
one Gödel sentence, hence one size. -/
theorem outgrows_arith (κ : ℕ) (T : ArithmeticTheory) [T.Δ₁] [𝗥₀ ⪯ T] [ℕ↓[ℒₒᵣ] ⊧* T] :
    ∃ gTS, ∀ Mchk, CategoricalThreshold.hostsAt κ gTS → gTS < Mchk → Mchk ≤ gTS ^ 2 →
      ∃ R : ReflectiveAsm gTS, R.depth = Mchk ∧
        CapacityLayer.FitsIn (recursorAsm R.depth) κ ∧
        ∃ M, GodelThreshold.RepresentsUnderivableTruth (Encodable.encode : Sentence ℒₒᵣ → ℕ)
          (fun δ => T ⊢ δ) (fun δ => ℕ↓[ℒₒᵣ] ⊧ δ) M := by
  obtain ⟨gTS, hInc⟩ := GodelComplete.incompleteness_of_arith T
  refine ⟨gTS, fun Mchk hhost h1 h2 => ?_⟩
  obtain ⟨R, hdepth, hfits, himp⟩ :=
    outgrows κ (Encodable.encode : Sentence ℒₒᵣ → ℕ)
      (fun δ => T ⊢ δ) (fun δ => ℕ↓[ℒₒᵣ] ⊧ δ) gTS Mchk hhost h1 h2
  exact ⟨R, hdepth, hfits, himp hInc⟩

/-- **The excess order at `𝗣𝗔⁻`, unconditionally** ([Decoupling] §6.3/§6.4). `outgrows_arith` at
Foundation's finite fragment of Peano arithmetic. `𝗣𝗔⁻` is the most faithful witness available: it is
*finite*, so its `Δ₁`-definability is `Theory.Δ₁.ofFinite` rather than a definability theorem, and
`𝗣𝗔⁻ ⊊ 𝗜𝚺₁` makes underivability in `𝗣𝗔⁻` the weaker — hence more faithful — claim. Fully
axiom-clean: `#print axioms` shows only `propext, Classical.choice, Quot.sound`. -/
theorem outgrows_paMinus (κ : ℕ) :
    ∃ gTS, ∀ Mchk, CategoricalThreshold.hostsAt κ gTS → gTS < Mchk → Mchk ≤ gTS ^ 2 →
      ∃ R : ReflectiveAsm gTS, R.depth = Mchk ∧
        CapacityLayer.FitsIn (recursorAsm R.depth) κ ∧
        ∃ M, GodelThreshold.RepresentsUnderivableTruth (Encodable.encode : Sentence ℒₒᵣ → ℕ)
          (fun δ => (𝗣𝗔⁻ : ArithmeticTheory) ⊢ δ) (fun δ => ℕ↓[ℒₒᵣ] ⊧ δ) M := by
  haveI : (𝗣𝗔⁻ : ArithmeticTheory).Δ₁ := Theory.Δ₁.ofFinite 𝗣𝗔⁻ PeanoMinus.finite
  exact outgrows_arith κ 𝗣𝗔⁻

/-- **The Witness World's guest unconditionally outgrows its host at `𝗣𝗔⁻`** ([Persistence] §5/§7 +
[Decoupling] §6.3/§6.4). The unconditional counterpart of `ExcessOrder.witness_outgrows`: the same
designed world `W(κ, k, G, π)` hosts a macro reading that is surjective, exactly `G`-lawful from every
initial state, robust against any perturbation of fewer than `2^k` cells, and cheaply owned at
`O(K(G) + log κ + log k)` — **and** at a Gödel size of `𝗣𝗔⁻` delivers a reflective object of the
realizability CCC `Asm` that represents a true-but-underivable sentence, with no incompleteness
hypothesis remaining.

So the cheaply-owned reading that carries the host's law does not merely *conditionally* cross the
internalization threshold: at a concrete, finitely axiomatized arithmetic there is a statement about
the host-and-itself that the guest's state space decides and the host's evolution does not.

The first conjunct is `PersistenceCapacity.witness_world` verbatim; the second is
`outgrows_paMinus`. This synthesis is stated in **no** paper; **no numbered result is claimed
machine-checked** by it. -/
theorem witness_outgrows_paMinus {ι_J : Type*} [Fintype ι_J] [Nonempty (Mem ι_J Bool)]
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
    (∃ gTS, ∀ Mchk, CategoricalThreshold.hostsAt κ gTS → gTS < Mchk → Mchk ≤ gTS ^ 2 →
      ∃ R : ReflectiveAsm gTS, R.depth = Mchk ∧
        CapacityLayer.FitsIn (recursorAsm R.depth) κ ∧
        ∃ M, GodelThreshold.RepresentsUnderivableTruth (Encodable.encode : Sentence ℒₒᵣ → ℕ)
          (fun δ => (𝗣𝗔⁻ : ArithmeticTheory) ⊢ δ) (fun δ => ℕ↓[ℒₒᵣ] ⊧ δ) M) :=
  ⟨witness_world (ι_J := ι_J) κ k hκ G π cG hG, outgrows_paMinus κ⟩

end ExcessOrder
