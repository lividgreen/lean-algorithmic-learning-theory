/-
Copyright (c) 2026 Mykola Palamarchuk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mykola Palamarchuk
-/
import ALT.CodePacking

/-!
# Bounded universality, priced

A universal evaluator is usually produced as an existence statement: some code computes what any
other code computes. Such a witness has no constructor skeleton, so nothing about it can be
priced — and a capacity-graded semantics needs exactly that price.

This module states the priced form. `UniversalAt F` says a code exists that runs the reference
dynamics within workspace `F` of the run's own width. Three things about the statement are
deliberate.

**It prices against the reference, not the witness.** The cost is charged against
`BoundedInterp.stepUFn`, the mathematical layer that specifies what the machine does, and against
the widths *that* run passes through. Nothing in the definition mentions how a witness represents a
configuration, so two witnesses with different internals are compared on the same terms.

**Grade-relativity is the width hypothesis.** "Executes code within capacity" is the named
hypothesis `∀ σ ≤ τ, Nat.size (stepUFn^[σ] (initConfig p x)) ≤ W`: on runs whose configurations stay
within `W` bits, the workspace is affine in `W`. It has to be a hypothesis rather than a derived
quantity — a frame stores the values a simulated recursion has accumulated, which are outputs of the
computation being run, not functions of the code's shape, so nothing bounds them from the code
alone.

**The semantics is anchored elsewhere, on purpose.** That the reference dynamics computes `eval`
is `BoundedInterp.machine_sound` and `BoundedInterp.machine_complete`, both independent of any
witness. Folding them into this definition would make the predicate about a particular machine
rather than about the price of running one, so they are cited rather than absorbed.

The iteration count enters only through `Nat.size τ`: the recursor carries its own counter, and the
workspace measure charges the width of every value a node touches. No leading term depends on how
far the run has gone.
-/

namespace BoundedUniversal

open Nat.Partrec (Code)
open Nat.Partrec.Code
open TimeCost

/-- **Bounded universality at a price.** Some code runs the reference dynamics, and does so within
workspace `F` of the widest of: the run's own configurations, its argument, and its counter. -/
def UniversalAt (F : ℕ → ℕ) : Prop :=
  ∃ u : Code,
    (∀ p x τ : ℕ,
      val u (Nat.pair (Nat.pair p x) τ)
        = BoundedInterp.stepUFn^[τ] (BoundedInterp.initConfig p x)) ∧
    (∀ p x τ W : ℕ,
      (∀ σ, σ ≤ τ →
        Nat.size (BoundedInterp.stepUFn^[σ] (BoundedInterp.initConfig p x)) ≤ W) →
      spaceCost u (Nat.pair (Nat.pair p x) τ)
        ≤ F (max W (max (Nat.size (Nat.pair p x)) (Nat.size τ))))

/-- The price the constructed interpreter actually pays: affine, with both constants inherited from
the step's own workspace law. They are upper bounds and are not claimed to be tight. -/
def universalCost (m : ℕ) : ℕ := 524300 * m + 131120

/-- **Bounded universality holds, at an affine price, with a structural witness.** The witness is
`CodePacking.runU` — a `prec` code built from constructors, which is what makes it priceable at
all. -/
theorem universalAt_holds : UniversalAt universalCost := by
  refine ⟨CodePacking.runU, CodePacking.val_runU, ?_⟩
  intro p x τ W hW
  have h := CodePacking.spaceCost_runU_le p x W τ hW
  have h1 : W ≤ max W (max (Nat.size (Nat.pair p x)) (Nat.size τ)) := le_max_left _ _
  have h2 : Nat.size (Nat.pair p x) ≤ max W (max (Nat.size (Nat.pair p x)) (Nat.size τ)) :=
    le_trans (le_max_left _ _) (le_max_right _ _)
  have h3 : Nat.size τ ≤ max W (max (Nat.size (Nat.pair p x)) (Nat.size τ)) :=
    le_trans (le_max_right _ _) (le_max_right _ _)
  rw [universalCost]
  omega

end BoundedUniversal
