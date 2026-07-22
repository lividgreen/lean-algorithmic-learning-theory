/-
Copyright (c) 2026 Mykola Palamarchuk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mykola Palamarchuk
-/
import ALT.PersistenceCapacity

-- Formal-check file, not Mathlib-destined: opt out of the house-style header linter.
set_option linter.style.header false

/-!
# The structural category of decoupled simulations ([Decoupling] §4.5)

Provenance: [Decoupling] §4.5 — the *domain* of the functor Conjecture 4.4 asks for: decoupled
learners, with capacity-respecting simulations as morphisms. This file defines those morphisms and
proves they form a category.

## Scope: STRUCTURAL only
A capacity-respecting simulation is a triple: a hosting square, a code-locality condition, and a
**resource grade** on the reading family. Only the first two are here. The graded enrichment — the
uniform-budget field and the realizer-transport lemma that prices a realizer of grade `g` in the
guest by a grade computed from `(g, b, τ)` in the host — is **deliberately absent**: it waits on
the encoding conventions that fix the price, and nothing below should be read as establishing it.
What is established is that the *underlying* structure is a category: morphisms compose, identities
exist, and the two conditions are closed under both.

## The two conditions, and why only one of them is primitive
A decoupled subsystem splits its state as `C × W` — a code region and a work region — and its step
map leaves the code region fixed. That read-only property is not an extra axiom here; it is the
defining property of decoupling ([Decoupling] §3, Lemma 3.1), recorded as `ReadOnly`.

A simulation of `U` by `U'` is then:
* **the square** `Intertwines (U'^[τ]) U ℓ` — `τ` host steps, read one frame later, are one guest
  step of the reading ([Persistence] §10.2, where dilated squares and their composition law live);
* **code-locality** — the guest code the reading returns depends on the host state only through the
  host's *code* region. Stated relationally (`x'.1 = y'.1 → (ℓ t x').1 = (ℓ t y').1`) rather than as
  a factorization through an existential translation map, so no choice is used and no translation
  map has to be constructed.

The design question this settles is which conditions are primitive. One might expect to *require*
that the code region be carried across the square, and separately that the induced code translation
be time-independent. Neither is a hypothesis: both are theorems.
* `code_carrying` — the square's code component is automatically a *carrying* square: the reading's
  guest code is unchanged by a block of `τ` host steps. It follows from the **guest's** read-only
  property alone, which collapses the square's code component.
* `code_time_indep` — the reading's code component is automatically *time-independent*: it returns
  the same guest code through every frame. It follows from the **host's** read-only property
  together with code-locality, and needs nothing else — in particular no inhabitedness of the work
  region and no choice.

So code-locality is the one genuine condition, and it is trivially closed under composition (the
code translations simply chain).

## Non-discreteness
`counter_simulates` exhibits a nontrivial morphism: the mod-`k·n` counter hosts the mod-`n` counter,
read by reduction mod `n`, at dilation `1`. So the category is not discrete, and the definition is
not vacuously satisfied only by identities.
-/

namespace DecoupledSimulation

open PersistenceCapacity

variable {C W C' W' C'' W'' : Type*}

/-! ## Decoupled step maps -/

/-- **The decoupling property** ([Decoupling] §3, Lemma 3.1): on a state space split as `C × W`
into a code region and a work region, the step map leaves the code region fixed. This is the
defining property of a decoupled subsystem, not an extra assumption imposed here. -/
def ReadOnly (U : C × W → C × W) : Prop := ∀ s, (U s).1 = s.1

/-- Read-only survives iteration: no number of steps touches the code region. -/
theorem ReadOnly.iterate {U : C × W → C × W} (h : ReadOnly U) : ∀ n s, ((U^[n]) s).1 = s.1 := by
  intro n
  induction n with
  | zero => intro s; rfl
  | succ m ih =>
      intro s
      rw [Function.iterate_succ_apply, ih (U s)]
      exact h s

/-! ## The morphisms -/

/-- **A simulation of `U` by `U'` at dilation `τ`** — a morphism of the domain category
[Decoupling] §4.5 asks for, minus its resource grade (see the module docstring).

`square` is the hosting square: `τ` steps of the host, read one frame later, are one step of the
guest. `codeLocal` says the reading's guest code is determined by the host's code region alone —
stated as a relation between host states agreeing on their code, which avoids constructing (or
choosing) a translation map. -/
structure Simulates (U' : C' × W' → C' × W') (U : C × W → C × W)
    (ℓ : ℕ → C' × W' → C × W) (τ : ℕ) : Prop where
  /-- the hosting square at dilation `τ` -/
  square : Intertwines (U'^[τ]) U ℓ
  /-- the reading's guest code depends on the host state only through the host's code region -/
  codeLocal : ∀ t x' y', x'.1 = y'.1 → (ℓ t x').1 = (ℓ t y').1

/-! ## The two automaticity facts -/

/-- **The code region is carried automatically.** A block of `τ` host steps does not change the
guest code the reading returns. Nothing is assumed about the reading beyond the square: the guest's
own read-only property collapses the square's code component, so "the square carries the code
region" is a consequence of decoupling rather than a condition on the morphism. -/
theorem code_carrying {U' : C' × W' → C' × W'} {U : C × W → C × W} {ℓ : ℕ → C' × W' → C × W}
    {τ : ℕ} (hU : ReadOnly U) (h : Simulates U' U ℓ τ) :
    ∀ t x', (ℓ (t + 1) ((U'^[τ]) x')).1 = (ℓ t x').1 := by
  intro t x'
  rw [h.square t x']
  exact hU (ℓ t x')

/-- **The induced code translation is time-independent automatically.** The reading returns the same
guest code through every frame. The host's read-only property fixes the host code across a block of
`τ` steps, code-locality transports the previous lemma's equation from `(U'^[τ]) x'` back to `x'`,
and the two together leave no room for a frame dependence.

No inhabitedness of the work region and no choice enter: the argument is entirely a chain of
equations at the single state `x'`. -/
theorem code_time_indep {U' : C' × W' → C' × W'} {U : C × W → C × W} {ℓ : ℕ → C' × W' → C × W}
    {τ : ℕ} (hU : ReadOnly U) (hU' : ReadOnly U') (h : Simulates U' U ℓ τ) :
    ∀ t x', (ℓ (t + 1) x').1 = (ℓ t x').1 := by
  intro t x'
  rw [← h.codeLocal (t + 1) ((U'^[τ]) x') x' (hU'.iterate τ x')]
  exact code_carrying hU h t x'

/-! ## The category structure -/

/-- **Identity.** Every decoupled step map simulates itself, read by the identity at dilation
`1`. -/
theorem Simulates.id (U : C × W → C × W) : Simulates U U (fun _ => _root_.id) 1 where
  square := intertwines_iterate_one.mpr fun _ _ => rfl
  codeLocal := fun _ _ _ h => h

/-- **Composition — the capstone.** Simulations compose and dilations multiply: if `U'` simulates
`U` at dilation `τ₁` and `U''` simulates `U'` at dilation `τ₂`, then `U''` simulates `U` at dilation
`τ₂ * τ₁`, read through the composite family `k ↦ ℓ₁ k ∘ ℓ₂ (τ₁ * k)` — the outer reading is taken
at the inner clock rate, since the guest's clock ticks once per `τ₁` ticks of the middle system's.

The square half is the tower's composition law ([Persistence] §10.2); the code-locality half chains
the two localities and needs nothing else, which is what makes the condition a categorical one
rather than a constraint that has to be re-established at each level. -/
theorem Simulates.comp {U : C × W → C × W} {U' : C' × W' → C' × W'} {U'' : C'' × W'' → C'' × W''}
    {ℓ₁ : ℕ → C' × W' → C × W} {ℓ₂ : ℕ → C'' × W'' → C' × W'} {τ₁ τ₂ : ℕ}
    (h₁ : Simulates U' U ℓ₁ τ₁) (h₂ : Simulates U'' U' ℓ₂ τ₂) :
    Simulates U'' U (fun k => ℓ₁ k ∘ ℓ₂ (τ₁ * k)) (τ₂ * τ₁) where
  square := Intertwines.comp h₂.square h₁.square
  codeLocal := fun t x'' y'' hxy =>
    h₁.codeLocal t _ _ (h₂.codeLocal (τ₁ * t) x'' y'' hxy)

/-! ## A nontrivial morphism: the counter tower -/

section Counter

variable {n k : ℕ} [NeZero n] [NeZero k]

/-- The cyclic counter of modulus `m` as a decoupled step map: an empty code region and a work
register that advances by one. -/
def counterStep (m : ℕ) [NeZero m] : Unit × Fin m → Unit × Fin m := fun s => (s.1, s.2 + 1)

/-- The counter's code region is read-only — vacuously, its code region being a point. -/
theorem counterStep_readOnly (m : ℕ) [NeZero m] : ReadOnly (counterStep m) := fun _ => rfl

instance : NeZero (k * n) := ⟨Nat.mul_ne_zero (NeZero.ne k) (NeZero.ne n)⟩

/-- The reading that reduces the work register mod `n`, the same at every frame. -/
def modLens (n : ℕ) [NeZero n] (m : ℕ) : ℕ → Unit × Fin m → Unit × Fin n :=
  fun _ s => ((), ⟨s.2.val % n, Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne n))⟩)

/-- **The category is not discrete.** The mod-`k·n` counter hosts the mod-`n` counter, read by
reduction mod `n`, at dilation `1`: the square commutes because `n ∣ k·n`, so reducing the host's
wrap-around mod `n` is the guest's own wrap-around. Code-locality is immediate — the reading's guest
code is the point. -/
theorem counter_simulates :
    Simulates (counterStep (k * n)) (counterStep n) (modLens n (k * n)) 1 where
  square := by
    refine intertwines_iterate_one.mpr fun t s => ?_
    simp only [counterStep, modLens, Prod.mk.injEq, true_and]
    apply Fin.val_injective
    have hdvd : n ∣ k * n := dvd_mul_left n k
    simp only [Fin.val_add, Fin.val_one', Nat.mod_mod_of_dvd _ hdvd]
    rw [Nat.add_mod, Nat.mod_mod_of_dvd _ hdvd]
  codeLocal := fun _ _ _ _ => rfl

end Counter

end DecoupledSimulation
