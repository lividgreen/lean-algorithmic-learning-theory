/-
Copyright (c) 2026 Mykola Palamarchuk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mykola Palamarchuk
-/
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Set.Card.Arithmetic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.FinCases
import ALT.Decoupling

-- Formal-check file, not Mathlib-destined: opt out of the house-style header linter.
set_option linter.style.header false

/-!
# Persistence capacity I: the recurrent core and the absolute ceiling ([Decoupling] §3.5)

Part one of the `PersistenceCapacity` development. The umbrella module `ALT.PersistenceCapacity`
imports all four parts; its docstring carries the capacity-name key and the map of the whole
development, and every part shares the `PersistenceCapacity` namespace.

A finite world is a state space `X` with an update `U : X → X`. This module owns the dynamics
underneath every capacity statement — the **recurrent core** — and the ceiling it imposes on any
time-dependent decoder, however powerful.

## Main results

* `core_bijOn` — the update restricts to a bijection on the **recurrent core**
  `⋂ t, U^[t] '' univ` (the states surviving every number of steps).
* `iterate_mem_core` — **the space bounds its own transient**: after `Nat.card X` steps every
  state is in the recurrent core, since the image chain strictly decreases until it stabilizes.
* `Lens` / `Carries` — the **lens family**, a time-indexed decoder subject to no constraint
  whatever: not locality, not simplicity, not computability. That is what makes the capacity
  theorem an ABSOLUTE bound rather than a statement about some class of observers.
* `capacity_horizon_le` / `capacity_horizon_ge` — the maximal model persistable for `T` steps has
  exactly `|U^[T] '' univ|` elements ([Decoupling] §3.5, Proposition 3.5, the finite-horizon
  half).
* `capacity_core` / `capacity_core_ge` / `capacity_core_iff` — letting `T → ∞`, a persistent
  model of size `m` exists iff `m ≤ |core U|` ([Decoupling] §3.5, Proposition 3.5). What
  obstructs memory is not overwriting but irreversibility.
* `static_le_moving` / `rotate_gap` — the static capacity of [Decoupling] §3 (Corollary 3.3)
  never exceeds the moving one, and the gap can be total: rotate-left has static capacity `0` and
  moving capacity the whole memory.
* `eventual_decoupling_iff` — a model correct only EVENTUALLY (a self-repairing code region)
  settles along every orbit from a `U`-closed basin `B` iff `U` is read-only on `R` over the
  ω-limit set `⋂ t, U^[t] '' B`. [Decoupling] §3, Proposition 3.4 is the case `ω B = B`.
* `eventual_descent_iff` — a decoded model obeys the law `F` eventually along every orbit from
  `B` iff it obeys `F` on `ω(B)`; `eventual_decoupling_iff` is its identity-law case.
* `staticLens_factors` / `hierarchy` — the static stratum ([Persistence] §4): a lens with
  `ℓ ∘ U = ℓ` is exactly a function constant on the components of the transition graph, and
  read-only cells ≤ components ≤ recurrent core.
-/

namespace PersistenceCapacity

open Decoupling

variable {X ι V M : Type*}

/-! ### ω-limit sets and the recurrent core

For a `U`-closed set `B` the forward images `U^[t] '' B` form a decreasing chain; on a finite state
space it stabilizes, and its intersection — the ω-limit set — is where `U` is a bijection. Taking
`B = univ` gives the **recurrent core**: the states surviving every number of steps.

This section and the capacity section below are stated for an arbitrary finite state type `X` and an
arbitrary endofunction `U : X → X` — the generality of [Persistence] §2.1, where a world is a finite
set with an update and nothing further is assumed. The cell-structured world `Mem ι V = ι → V` is
the instance `X = ι → V`, and the sections that genuinely need cells (the read-only stratum, the
rotation gap, the eventual-persistence relaxation) take it. -/

/-- The **ω-limit set** of a set of states: the states reachable from `B` after every number of
steps. For a `U`-closed `B` this is the union of the limit cycles reachable from `B`. -/
def omegaLimit (U : X → X) (B : Set X) : Set X :=
  ⋂ t : ℕ, (U^[t]) '' B

/-- The **recurrent core**: the states that survive every number of steps. `U` restricts to a
bijection on it (`core_bijOn`), which is the entire reason it is the ceiling on persistence. -/
def core (U : X → X) : Set X := ⋂ t : ℕ, (U^[t]) '' Set.univ

/-- The core is the ω-limit set of the whole memory. -/
theorem core_eq_omegaLimit (U : X → X) : core U = omegaLimit U Set.univ := rfl

/-- The whole memory is `U`-closed — the hypothesis under which the core inherits every ω-limit
fact below. -/
private theorem univ_closed (U : X → X) : ∀ s ∈ (Set.univ : Set X), U s ∈ Set.univ :=
  fun _ _ => Set.mem_univ _

/-- One step of the image chain: `U^[t+1] '' B = U '' (U^[t] '' B)`. -/
private theorem image_iterate_succ (U : X → X) (B : Set X) (t : ℕ) :
    (U^[t + 1]) '' B = U '' ((U^[t]) '' B) := by
  rw [← Set.image_comp, ← Function.iterate_succ']

/-- The image chain of a `U`-closed set decreases. -/
private theorem image_iterate_subset (U : X → X) {B : Set X}
    (hB : ∀ s ∈ B, U s ∈ B) (t : ℕ) : (U^[t + 1]) '' B ⊆ (U^[t]) '' B := by
  rintro _ ⟨b, hb, rfl⟩
  exact ⟨U b, hB b hb, (Function.iterate_succ_apply U t b).symm⟩

/-- The image chain of a `U`-closed set is antitone. -/
private theorem image_iterate_antitone (U : X → X) {B : Set X}
    (hB : ∀ s ∈ B, U s ∈ B) {m n : ℕ} (h : m ≤ n) : (U^[n]) '' B ⊆ (U^[m]) '' B := by
  induction n, h using Nat.le_induction with
  | base => exact subset_rfl
  | succ n _ ih => exact (image_iterate_subset U hB n).trans ih

/-- On a finite memory the image chain of a `U`-closed set **stabilizes, and by step `|B|`**: past
some index `N ≤ B.ncard` every further step reproduces the same set. This is the finite-endofunction
fact behind the whole section, with the transient bounded by the space it happens in.

The bound is the whole reason to state it this way. The chain is antitone, so before it stabilizes
it *strictly* decreases, and a chain of naturals starting at `B.ncard` cannot strictly decrease more
than `B.ncard` times. Stabilization is therefore over by step `B.ncard` — no earlier index need be
exhibited, and none later is needed. -/
theorem exists_image_stable_le [Finite X] (U : X → X) {B : Set X}
    (hB : ∀ s ∈ B, U s ∈ B) : ∃ N ≤ B.ncard, ∀ t, N ≤ t → (U^[t]) '' B = (U^[N]) '' B := by
  have hfin : ∀ t : ℕ, ((U^[t]) '' B).Finite := fun _ => Set.toFinite _
  have hzero : ((U^[0]) '' B).ncard = B.ncard := by simp
  have hstep : ∃ N ≤ B.ncard, ((U^[N]) '' B).ncard ≤ ((U^[N + 1]) '' B).ncard := by
    by_contra hc
    push Not at hc
    -- otherwise the chain strictly drops `B.ncard + 1` times from `B.ncard`, which `ℕ` forbids
    have key : ∀ t, t ≤ B.ncard + 1 → ((U^[t]) '' B).ncard + t ≤ ((U^[0]) '' B).ncard := by
      intro t
      induction t with
      | zero => simp
      | succ t ih =>
          intro ht
          have h1 := ih (by omega)
          have h2 := hc t (by omega)
          omega
    have h := key (B.ncard + 1) le_rfl
    omega
  obtain ⟨N, hNle, hN⟩ := hstep
  have hEq : (U^[N + 1]) '' B = (U^[N]) '' B :=
    Set.eq_of_subset_of_ncard_le (image_iterate_subset U hB N) hN (hfin N)
  have hall : ∀ k : ℕ, (U^[N + k]) '' B = (U^[N]) '' B := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
        have hrw : N + (k + 1) = (N + k) + 1 := by omega
        rw [hrw, image_iterate_succ, ih, ← image_iterate_succ, hEq]
  refine ⟨N, hNle, fun t ht => ?_⟩
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le ht
  exact hall k

/-- The image chain of a `U`-closed set stabilizes — `exists_image_stable_le` forgetting the
bound. -/
private theorem exists_image_stable [Finite X] (U : X → X) {B : Set X}
    (hB : ∀ s ∈ B, U s ∈ B) : ∃ N : ℕ, ∀ t, N ≤ t → (U^[t]) '' B = (U^[N]) '' B :=
  let ⟨N, _, h⟩ := exists_image_stable_le U hB
  ⟨N, h⟩

/-- Past the stabilization index the ω-limit set **is** the image. -/
private theorem omegaLimit_eq_image [Finite X] (U : X → X) {B : Set X}
    (hB : ∀ s ∈ B, U s ∈ B) {N : ℕ} (hN : ∀ t, N ≤ t → (U^[t]) '' B = (U^[N]) '' B) :
    omegaLimit U B = (U^[N]) '' B := by
  refine Set.Subset.antisymm (Set.iInter_subset _ N) fun x hx => ?_
  refine Set.mem_iInter.mpr fun t => ?_
  rcases Nat.lt_or_ge t N with h | h
  · exact image_iterate_antitone U hB h.le hx
  · rw [hN t h]; exact hx

/-- The ω-limit set sits inside its basin (the `t = 0` component of the intersection). -/
private theorem omegaLimit_subset (U : X → X) (B : Set X) : omegaLimit U B ⊆ B := by
  intro x hx
  have := Set.mem_iInter.mp hx 0
  simpa using this

/-- Every state of a `U`-closed `B` lands in the ω-limit set after finitely many steps. -/
private theorem mem_omegaLimit_iterate [Finite X] (U : X → X) {B : Set X}
    (hB : ∀ s ∈ B, U s ∈ B) : ∃ N : ℕ, ∀ s ∈ B, (U^[N]) s ∈ omegaLimit U B := by
  obtain ⟨N, hN⟩ := exists_image_stable U hB
  exact ⟨N, fun s hs => by rw [omegaLimit_eq_image U hB hN]; exact ⟨s, hs, rfl⟩⟩

/-- The ω-limit set is invariant: `U` maps it ONTO itself. -/
private theorem image_omegaLimit [Finite X] (U : X → X) {B : Set X}
    (hB : ∀ s ∈ B, U s ∈ B) : U '' omegaLimit U B = omegaLimit U B := by
  obtain ⟨N, hN⟩ := exists_image_stable U hB
  rw [omegaLimit_eq_image U hB hN, ← image_iterate_succ, hN (N + 1) (by omega)]

/-- **`U` restricts to a bijection on the ω-limit set.** Surjectivity is invariance
(`image_omegaLimit`); injectivity is then forced by finiteness. -/
theorem omegaLimit_bijOn [Finite X] (U : X → X) {B : Set X}
    (hB : ∀ s ∈ B, U s ∈ B) : Set.BijOn U (omegaLimit U B) (omegaLimit U B) := by
  have himg := image_omegaLimit U hB
  refine ⟨fun x hx => ?_, ?_, fun x hx => ?_⟩
  · rw [← himg]; exact ⟨x, hx, rfl⟩
  · exact Set.injOn_of_ncard_image_eq (by rw [himg]) (Set.toFinite _)
  · rw [himg]; exact hx

/-- A bijection of a set iterates to a bijection of that set. -/
private theorem bijOn_iterate {U : X → X} {s : Set X} (h : Set.BijOn U s s) (n : ℕ) :
    Set.BijOn (U^[n]) s s := by
  induction n with
  | zero => simpa using Set.bijOn_id s
  | succ k ih => rw [Function.iterate_succ]; exact ih.comp h

/-- **`U` restricts to a bijection on the recurrent core** — the standard finite-endofunction fact
([Decoupling] §3.5): the eventual image is where the dynamics is reversible. -/
theorem core_bijOn [Finite X] (U : X → X) :
    Set.BijOn U (core U) (core U) := by
  rw [core_eq_omegaLimit]
  exact omegaLimit_bijOn U (univ_closed U)

/-- **The transient is over by step `|X|`**: after `Nat.card X` steps, every state whatever is in
the recurrent core. The image chain strictly decreases until it stabilizes and it starts at `|X|`
(`exists_image_stable_le`), so it has stabilized by then — the space bounds its own transient.

This is the bound that makes a settling clock finite: an observer that waits `|X|` steps is past
every world's transient, without knowing the world. -/
theorem iterate_mem_core [Finite X] (U : X → X) {t : ℕ} (ht : Nat.card X ≤ t) (s : X) :
    U^[t] s ∈ core U := by
  obtain ⟨N, hNle, hN⟩ := exists_image_stable_le U (univ_closed U)
  rw [Set.ncard_univ] at hNle
  have hcore : core U = (U^[N]) '' Set.univ := omegaLimit_eq_image U (univ_closed U) hN
  rw [hcore, ← hN t (le_trans hNle ht)]
  exact ⟨s, Set.mem_univ _, rfl⟩

/-- The core is the stabilized image of the whole memory. -/
private theorem core_eq_image [Finite X] (U : X → X) :
    ∃ N : ℕ, core U = (U^[N]) '' Set.univ ∧
      ∀ t, N ≤ t → (U^[t]) '' Set.univ = (U^[N]) '' Set.univ :=
  let ⟨N, hN⟩ := exists_image_stable U (univ_closed U)
  ⟨N, by rw [core_eq_omegaLimit]; exact omegaLimit_eq_image U (univ_closed U) hN, hN⟩

/-! ### The lens family and its capacity ([Decoupling] §3.5, Proposition 3.5) -/

/-- A **lens family**: a time-indexed decoder. Deliberately unconstrained — not required to be
local, simple, or computable. -/
abbrev Lens (X M : Type*) := ℕ → X → M

/-- The family **carries a persistent model up to horizon `T`**: reading through the time-`t` lens
recovers what the time-`0` lens read. Surjectivity of `ℓ 0` makes the model genuinely `M`-sized. -/
def CarriesUpTo (U : X → X) (ℓ : Lens X M) (T : ℕ) : Prop :=
  Function.Surjective (ℓ 0) ∧ ∀ t ≤ T, ∀ s, ℓ t (U^[t] s) = ℓ 0 s

/-- The family **carries a persistent model** for all time. -/
def Carries (U : X → X) (ℓ : Lens X M) : Prop :=
  Function.Surjective (ℓ 0) ∧ ∀ t s, ℓ t (U^[t] s) = ℓ 0 s

/-- Persistence for all time is persistence up to every horizon. -/
private theorem Carries.carriesUpTo {U : X → X} {ℓ : Lens X M} (h : Carries U ℓ) (T : ℕ) :
    CarriesUpTo U ℓ T := ⟨h.1, fun t _ s => h.2 t s⟩

/-- **Persistence capacity at horizon `T`, the ceiling** ([Decoupling] §3.5, Proposition 3.5). Any
lens family persisting `T` steps carries a model no larger than the `T`-step image of the world —
whatever the lens. Reading persistence at `t = T` makes `ℓ T` a surjection from that image onto the
model, and a surjection cannot leave the target bigger than the source. -/
private theorem capacity_horizon_le_ncard [Finite X] [Fintype M] {U : X → X}
    {ℓ : Lens X M} {T : ℕ} (h : CarriesUpTo U ℓ T) :
    Fintype.card M ≤ ((U^[T]) '' Set.univ).ncard := by
  have hsurj : Function.Surjective fun x : ↥((U^[T]) '' Set.univ) => ℓ T x.1 := by
    intro m
    obtain ⟨s, hs⟩ := h.1 m
    exact ⟨⟨U^[T] s, ⟨s, Set.mem_univ _, rfl⟩⟩, by simpa using (h.2 T le_rfl s).trans hs⟩
  have hle := Nat.card_le_card_of_surjective _ hsurj
  rwa [Nat.card_eq_fintype_card, Nat.card_coe_set_eq] at hle

/-- **Persistence capacity at horizon `T`, the ceiling** ([Decoupling] §3.5, Proposition 3.5), in
`Finset` form. -/
theorem capacity_horizon_le [Fintype X] [DecidableEq X] [Fintype M]
    {U : X → X} {ℓ : Lens X M} {T : ℕ} (h : CarriesUpTo U ℓ T) :
    Fintype.card M ≤ (Finset.univ.image (U^[T])).card := by
  have hle := capacity_horizon_le_ncard h
  rwa [← Finset.coe_univ, ← Finset.coe_image, Set.ncard_coe_finset] at hle

/-- **Persistence capacity at horizon `T`, attained** ([Decoupling] §3.5, Proposition 3.5). Every
model of that size is realized: read the world `T` steps ahead and stand still, i.e.
`ℓ t := θ ∘ U^[T - t]`. -/
theorem capacity_horizon_ge [Fintype X] [DecidableEq X] [Fintype M]
    [Nonempty M] {U : X → X} {T : ℕ}
    (h : Fintype.card M ≤ (Finset.univ.image (U^[T])).card) :
    ∃ ℓ : Lens X M, CarriesUpTo U ℓ T := by
  classical
  have hcard : Fintype.card M ≤ Fintype.card ↥(Finset.univ.image (U^[T])) := by
    rw [Fintype.card_coe]; exact h
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hcard
  set f : M → X := fun m => ((e m : ↥(Finset.univ.image (U^[T]))) : X) with hfdef
  have hf_inj : Function.Injective f := fun a b hab =>
    e.injective (Subtype.ext hab)
  have hf_mem : ∀ m, f m ∈ Finset.univ.image (U^[T]) := fun m => (e m).2
  set θ : X → M := Function.invFun f with hθdef
  have hθ : ∀ m, θ (f m) = m := Function.leftInverse_invFun hf_inj
  refine ⟨fun t s => θ (U^[T - t] s), ?_, ?_⟩
  · intro m
    obtain ⟨s, -, hs⟩ := Finset.mem_image.mp (hf_mem m)
    exact ⟨s, by simpa [hs] using hθ m⟩
  · intro t ht s
    have hadd : (T - t) + t = T := by omega
    simp only [← Function.iterate_add_apply, hadd, Nat.sub_zero]

/-- **The ceiling on persistence** ([Decoupling] §3.5, Proposition 3.5). No observer, however
powerful, carries more than the recurrent core: irreversibility is the only obstruction to
memory. -/
theorem capacity_core [Finite X] [Fintype M]
    {U : X → X} {ℓ : Lens X M} (h : Carries U ℓ) :
    Fintype.card M ≤ Nat.card (core U) := by
  obtain ⟨N, hcore, -⟩ := core_eq_image U
  rw [Nat.card_coe_set_eq, hcore]
  exact capacity_horizon_le_ncard (h.carriesUpTo N)

/-- Inverting the update along the core: `U^[t]` is undone by iterating `U`'s inverse on the
core. -/
private theorem invFunOn_iterate_left [Finite X] [Nonempty (X)]
    (U : X → X) {x : X} (hx : x ∈ core U) (t : ℕ) :
    (Function.invFunOn U (core U))^[t] (U^[t] x) = x := by
  have hbij := core_bijOn U
  have hleft := hbij.injOn.leftInvOn_invFunOn
  induction t with
  | zero => rfl
  | succ t ih =>
      have hxt : U^[t] x ∈ core U := hbij.mapsTo.iterate t hx
      rw [Function.iterate_succ_apply' U t x, Function.iterate_succ_apply, hleft hxt, ih]

/-- **The ceiling is attained** ([Decoupling] §3.5, Proposition 3.5, the `⇐` half). A model of any
size up to the core is carried by the canonical moving family `ℓ t := θ ∘ (U ↾ core)⁻¹^t ∘ U^[N]`:
flow into the core, then co-move with the recurrent rule. -/
theorem capacity_core_ge [Finite X] [Fintype M] [Nonempty M] {U : X → X}
    (h : Fintype.card M ≤ Nat.card (core U)) :
    ∃ ℓ : Lens X M, Carries U ℓ := by
  classical
  obtain ⟨N, hcore, -⟩ := core_eq_image U
  have hcorepos : 0 < Nat.card ↥(core U) := lt_of_lt_of_le Fintype.card_pos h
  have hne : (core U).Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    rintro hempty
    rw [hempty] at hcorepos
    simp at hcorepos
  have : Nonempty (X) := ⟨hne.some⟩
  have : Fintype ↥(core U) := Fintype.ofFinite _
  -- an injection of the model into the core, and a left inverse `θ` reading the model off it
  have hcard : Fintype.card M ≤ Fintype.card ↥(core U) := by
    rw [← Nat.card_eq_fintype_card (α := ↥(core U))]
    exact h
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hcard
  set f : M → X := fun m => ((e m : ↥(core U)) : X) with hfdef
  have hf_inj : Function.Injective f := fun a b hab => e.injective (Subtype.ext hab)
  have hf_mem : ∀ m, f m ∈ core U := fun m => (e m).2
  set θ : X → M := Function.invFun f with hθdef
  have hθ : ∀ m, θ (f m) = m := Function.leftInverse_invFun hf_inj
  refine ⟨fun t s => θ ((Function.invFunOn U (core U))^[t] (U^[N] s)), ?_, ?_⟩
  · intro m
    obtain ⟨s, -, hs⟩ : f m ∈ (U^[N]) '' Set.univ := by rw [← hcore]; exact hf_mem m
    exact ⟨s, by simpa [hs] using hθ m⟩
  · intro t s
    have hmem : U^[N] s ∈ core U := by rw [hcore]; exact ⟨s, Set.mem_univ _, rfl⟩
    have hcomm : U^[N] (U^[t] s) = U^[t] (U^[N] s) := by
      rw [← Function.iterate_add_apply, ← Function.iterate_add_apply, Nat.add_comm]
    simp only [hcomm, invFunOn_iterate_left U hmem t, Function.iterate_zero_apply]

/-- **Proposition 3.5** ([Decoupling] §3.5), packaged: a lens family carrying a persistent model of
size `|M|` exists **iff** `|M| ≤ |core U|`. No constraint on the lens — locality, simplicity and
computability are all irrelevant to the bound. -/
theorem capacity_core_iff [Finite X] [Fintype M] [Nonempty M] {U : X → X} :
    (∃ ℓ : Lens X M, Carries U ℓ) ↔ Fintype.card M ≤ Nat.card (core U) :=
  ⟨fun ⟨_, hℓ⟩ => capacity_core hℓ, capacity_core_ge⟩

/-! ### The static capacity is below the moving one, and the gap can be total -/

/-- The cells the update never rewrites — the maximal static code region of [Decoupling] §3
(Corollary 3.3). -/
def Fix (U : Mem ι V → Mem ι V) : Set ι := {a | ∀ s, U s a = s a}

/-- `U` is read-only on `Fix U` (`Decoupling.Fixes`), by definition. -/
private theorem fixes_fix (U : Mem ι V → Mem ι V) : Fixes U (Fix U) := fun _ _ ha => ha _

/-- **The static capacity never exceeds the moving one** ([Decoupling] §3.5(i)). The number of
models storable at fixed addresses, `|V| ^ |Fix U|`, is at most `|core U|`, because restriction from
the core onto the fixed cells is surjective: any assignment of the fixed cells is realized by a core
state (flow an arbitrary completion into the core — the fixed cells ride along unchanged). -/
theorem static_le_moving [Finite ι] [Fintype V] (U : Mem ι V → Mem ι V) :
    Fintype.card V ^ Nat.card (Fix U) ≤ Nat.card (core U) := by
  classical
  rcases isEmpty_or_nonempty (Mem ι V) with hE | hNE
  · -- the memory itself is empty: no values, at least one cell, so the static capacity is `0`
    have hVe : IsEmpty V := ⟨fun v => hE.false (fun _ => v)⟩
    have hιne : Nonempty ι := by
      by_contra hc
      rw [not_nonempty_iff] at hc
      exact hE.false (fun a => (hc.false a).elim)
    have hFix : Fix U = Set.univ := by
      ext a
      simp only [Fix, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
      exact fun s => (hE.false s).elim
    have hpos : 0 < Nat.card ↥(Fix U) := by
      rw [hFix, Nat.card_coe_set_eq, Set.ncard_univ]
      exact Nat.card_pos
    have hcardV : Fintype.card V = 0 := Fintype.card_eq_zero
    rw [hcardV, zero_pow (by omega)]
    exact Nat.zero_le _
  · obtain ⟨s₀⟩ := hNE
    obtain ⟨N, hcore, -⟩ := core_eq_image U
    have hsurj : Function.Surjective
        (fun (x : ↥(core U)) (a : ↥(Fix U)) => (x : Mem ι V) (a : ι)) := by
      intro v
      set t : Mem ι V := fun a => if h : a ∈ Fix U then v ⟨a, h⟩ else s₀ a with ht
      refine ⟨⟨U^[N] t, by rw [hcore]; exact ⟨t, Set.mem_univ _, rfl⟩⟩, ?_⟩
      funext a
      have h1 : (U^[N] t) (a : ι) = t (a : ι) := fixes_iterate (fixes_fix U) N t (a : ι) a.2
      have h2 : t (a : ι) = v a := by simp only [ht, dif_pos a.2, Subtype.coe_eta]
      change (U^[N] t) (a : ι) = v a
      rw [h1, h2]
    have hle : Nat.card (↥(Fix U) → V) ≤ Nat.card ↥(core U) :=
      Nat.card_le_card_of_surjective _ hsurj
    have : Fintype ↥(Fix U) := Fintype.ofFinite _
    have hcard : Nat.card (↥(Fix U) → V) = Fintype.card V ^ Nat.card ↥(Fix U) := by
      rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_fun]
    rwa [hcard] at hle

/-- **The gap is total** ([Decoupling] §3.5(i)). Rotate-left on a cyclic string rewrites EVERY cell
— `Fix U = ∅`, so [Decoupling] §3 Corollary 3.2 applies and the static capacity is zero — yet it is
a bijection, so the core is the whole memory and the moving capacity is `log₂ |Mem|` bits. Total
overwrite precludes persistent content at a fixed ADDRESS, not persistent content. -/
theorem rotate_gap (n : ℕ) (hn : 2 ≤ n) :
    ∃ U : Mem (ZMod n) Bool → Mem (ZMod n) Bool, Fix U = ∅ ∧ core U = Set.univ := by
  have : NeZero n := ⟨by omega⟩
  have : Fact (1 < n) := ⟨by omega⟩
  refine ⟨fun s i => s (i + 1), ?_, ?_⟩
  · ext a
    simp only [Fix, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_forall]
    have hne : a + 1 ≠ a := fun hcon => one_ne_zero (α := ZMod n) (add_eq_left.mp hcon)
    exact ⟨fun i => decide (i = a), by simp [hne]⟩
  · have hbij : Function.Bijective (fun (s : Mem (ZMod n) Bool) i => s (i + 1)) := by
      constructor
      · intro s t h
        funext i
        have h2 : s (i - 1 + 1) = t (i - 1 + 1) := congrFun h (i - 1)
        rwa [sub_add_cancel] at h2
      · intro s
        exact ⟨fun i => s (i - 1), by funext i; simp⟩
    refine Set.eq_univ_of_forall fun x => Set.mem_iInter.mpr fun t => ?_
    obtain ⟨y, hy⟩ := (hbij.iterate t).2 x
    exact ⟨y, Set.mem_univ _, hy⟩

/-! ### Eventual persistence: a self-repairing code region ([Decoupling] §3.5, the relaxations)

Relax "the model is correct at every step" to "the model is correct eventually". The conclusion
relaxes from "read-only everywhere" to "read-only on the ω-limit set" — and nothing weaker. -/

/-- The decoded model **settles** along the orbit of `s`: it is eventually constant. -/
def Settles (U : Mem ι V → Mem ι V) (decode : Mem ι V → M) (s : Mem ι V) : Prop :=
  ∃ T, ∀ k ≥ T, decode (U^[k] s) = decode (U^[T] s)

/-- Every state of the ω-limit set is periodic: it lies on a limit cycle. -/
private theorem exists_period [Finite X] (U : X → X) {B : Set X}
    (hB : ∀ s ∈ B, U s ∈ B) {s : X} (hs : s ∈ omegaLimit U B) :
    ∃ p, 1 ≤ p ∧ U^[p] s = s := by
  have hbij := omegaLimit_bijOn U hB
  have hmt := hbij.mapsTo
  have hinj := hbij.injOn
  have key : ∀ i j : ℕ, i < j → U^[i] s = U^[j] s → ∃ p, 1 ≤ p ∧ U^[p] s = s := by
    intro i j hij hEq
    refine ⟨j - i, by omega, ?_⟩
    have hji : j = i + (j - i) := by omega
    rw [hji, Function.iterate_add_apply] at hEq
    exact (hinj.iterate hmt i (hmt.iterate (j - i) hs) hs hEq.symm)
  obtain ⟨i, j, hij, hEq⟩ := Finite.exists_ne_map_eq_of_infinite
    (fun k : ℕ => (⟨U^[k] s, hmt.iterate k hs⟩ : ↥(omegaLimit U B)))
  have hEq' : U^[i] s = U^[j] s := congrArg Subtype.val hEq
  rcases lt_or_gt_of_ne hij with h | h
  · exact key i j h hEq'
  · exact key j i h hEq'.symm

/-- Iterating a `U`-closed set's ω-limit stays inside it. -/
private theorem iterate_mem_omegaLimit [Finite X] (U : X → X) {B : Set X} (hB : ∀ s ∈ B, U s ∈ B)
    {s : X} (hs : s ∈ omegaLimit U B) (k : ℕ) : U^[k] s ∈ omegaLimit U B :=
  (omegaLimit_bijOn U hB).mapsTo.iterate k hs

/-- **The Eventual Decoupling Lemma** ([Decoupling] §3.5). For a faithful decoder and a `U`-closed
basin `B`: the decoded model settles along every orbit from `B` **iff** `U` is read-only on `R` over
the ω-limit set. Relaxing persistence to eventual persistence does not escape the Total-Overwrite
Exclusion — it relocates it from the whole memory to `ω B`. [Decoupling] §3, Proposition 3.4
(`Decoupling.decoupling_iff_persists_on`) is the case `ω B = B`.

The `⇒` direction argues through the limit cycle: a state of `ω B` is periodic (`exists_period`),
and a settling sequence along a cycle is constant on it — so the model is preserved in ONE step
there, and faithfulness converts that into read-only. -/
theorem eventual_decoupling_iff [Finite ι] [Finite V] {U : Mem ι V → Mem ι V} {R : Set ι}
    {decode : Mem ι V → M} {B : Set (Mem ι V)} (hf : Faithful decode R)
    (hB : ∀ s ∈ B, U s ∈ B) :
    (∀ s ∈ B, Settles U decode s) ↔ (∀ s ∈ omegaLimit U B, ∀ a ∈ R, U s a = s a) := by
  constructor
  · intro hset s hs a ha
    obtain ⟨p, hp1, hp⟩ := exists_period U hB hs
    obtain ⟨T, hT⟩ := hset s (omegaLimit_subset U B hs)
    have hper : ∀ j : ℕ, U^[p * j] s = s := by
      intro j
      induction j with
      | zero => simp
      | succ j ih =>
          have hrw : p * (j + 1) = p * j + p := by ring
          rw [hrw, Function.iterate_add_apply, hp, ih]
    have hTle : T ≤ p * T := Nat.le_mul_of_pos_left T hp1
    have e1 : decode s = decode (U^[T] s) := by
      have := hT (p * T) hTle
      rwa [hper T] at this
    have e2 : decode (U s) = decode (U^[T] s) := by
      have := hT (p * T + 1) (by omega)
      rwa [Function.iterate_succ_apply', hper T] at this
    exact (hf (U s) s).mp (by rw [e2, ← e1]) a ha
  · intro hfix s hs
    obtain ⟨N, hN⟩ := exists_image_stable U hB
    have hmem : U^[N] s ∈ omegaLimit U B := by
      rw [omegaLimit_eq_image U hB hN]; exact ⟨s, hs, rfl⟩
    have hclosed : ∀ x ∈ omegaLimit U B, U x ∈ omegaLimit U B := fun _ hx =>
      (omegaLimit_bijOn U hB).mapsTo hx
    have hval : ∀ k, decode (U^[k] (U^[N] s)) = decode (U^[N] s) := fun k =>
      hf.dependsOn _ _ fun a ha => fixes_iterate_on hclosed hfix k (U^[N] s) hmem a ha
    refine ⟨N, fun k hk => ?_⟩
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
    have hrw : U^[N + j] s = U^[j] (U^[N] s) := by
      rw [Nat.add_comm, Function.iterate_add_apply]
    rw [hrw, hval j]

/-- Coherence: [Decoupling] §3, Proposition 3.4 (`Decoupling.decoupling_iff_persists_on`) is the
case `ω B = B` — a basin already equal to its own ω-limit set, where "settles eventually" and
"persists at every step" coincide. -/
example [Finite ι] [Finite V] {U : Mem ι V → Mem ι V} {R : Set ι} {decode : Mem ι V → M}
    {B : Set (Mem ι V)} (hf : Faithful decode R) (hB : ∀ s ∈ B, U s ∈ B)
    (hfix : omegaLimit U B = B) :
    (∀ s ∈ B, Settles U decode s) ↔ (∀ s ∈ B, ∀ k, decode (U^[k] s) = decode s) := by
  rw [eventual_decoupling_iff hf hB, hfix]
  exact decoupling_iff_persists_on hf hB

/-- **Majority-vote write-back on three copies**: every cell is overwritten, every step, with the
majority of the three. The worked self-repairing world of [Decoupling] §3.5. -/
def majWorld : Mem (Fin 3) Bool → Mem (Fin 3) Bool :=
  fun s _ => (s 0 && s 1) || (s 1 && s 2) || (s 0 && s 2)

/-- The **consensus bit** the majority world writes back: the value all three copies agree on once
the world has settled. -/
def majBit (s : Mem (Fin 3) Bool) : Bool := (s 0 && s 1) || (s 1 && s 2) || (s 0 && s 2)

private theorem majWorld_apply (s : Mem (Fin 3) Bool) : majWorld s = fun _ => majBit s := rfl

/-- **The recurrent core of the majority world is the consensus set**: the states whose three copies
agree. One step lands in it, and `majWorld` is the identity there. -/
theorem core_majWorld : core majWorld = {s | s 0 = s 1 ∧ s 1 = s 2} := by
  ext x
  constructor
  · intro hx
    obtain ⟨y, -, hy⟩ : x ∈ (majWorld^[1]) '' Set.univ := Set.mem_iInter.mp hx 1
    rw [Function.iterate_one] at hy
    subst hy
    exact ⟨rfl, rfl⟩
  · rintro ⟨h01, h12⟩
    have h02 : x 0 = x 2 := h01.trans h12
    have hUx : majWorld x = x := by
      funext i
      rw [majWorld]
      fin_cases i <;> simp [← h01, ← h02]
    exact Set.mem_iInter.mpr fun t => ⟨x, Set.mem_univ _, Function.iterate_fixed hUx t⟩

/-- **The worked instance: majority-vote write-back on three copies.** Each cell is overwritten,
every step, with the majority of the three — so `Fix U = ∅` and [Decoupling] §3 Corollary 3.2
correctly reports NO static model. Yet the recurrent core is exactly the **consensus set** (the
states whose three copies agree), `U` is the identity there, and one bit persists eventually: a
single corrupted copy is repaired in one step and the surviving bit is the consensus.

Total overwrite globally, read-only on-shell — the concrete witness for
`eventual_decoupling_iff`. -/
theorem majority_selfRepair :
    ∃ U : Mem (Fin 3) Bool → Mem (Fin 3) Bool,
      Fix U = ∅ ∧ core U = {s | s 0 = s 1 ∧ s 1 = s 2} ∧ Nat.card (core U) = 2 := by
  refine ⟨majWorld, ?_, core_majWorld, ?_⟩
  · -- no cell is read-only: the lone dissenter is always overwritten by the majority
    ext a
    simp only [Fix, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_forall, majWorld]
    exact ⟨fun i => decide (i = a), by fin_cases a <;> decide⟩
  · -- and the consensus set holds exactly one bit
    rw [core_majWorld, Nat.card_eq_fintype_card]
    decide

/-! ### After the lens: the effective law ([Decoupling] §3.5, the relaxations)

The last relaxation: a decoded model that obeys a law of its own rather than standing still. Such a
law exists exactly when the lens's fibres are `U`-invariant — the **substitution property** of
Hartmanis and Stearns (1966), cited in [Decoupling] §3.5. That property is not ours; what is
recorded here is the identification of [Decoupling] §3 Lemma 3.1 as its **identity-law case**
(`decoupling_is_identity_law`): persistence is not a special topic, it is the `F = id` fibre of the
descent hierarchy, and the read-only requirement is relocated rather than removed. -/

/-- The decoded model obeys a law of its own: states that look alike keep looking alike. (The
`U`-invariance of the lens's fibres — the substitution property of Hartmanis–Stearns 1966.) -/
def Autonomous (U : Mem ι V → Mem ι V) (decode : Mem ι V → M) : Prop :=
  ∀ s t, decode s = decode t → decode (U s) = decode (U t)

/-- **Descent** (the substitution property, Hartmanis–Stearns 1966; [Decoupling] §3.5). The world's
rule induces a law on the decoded model **iff** the lens's fibres are `U`-invariant. Forward is
immediate; backward reads the induced law off any preimage, which is well defined precisely by
autonomy. -/
theorem descent_iff {U : Mem ι V → Mem ι V} {decode : Mem ι V → M} :
    (∃ F : M → M, ∀ s, decode (U s) = F (decode s)) ↔ Autonomous U decode := by
  classical
  constructor
  · rintro ⟨F, hF⟩ s t hst
    rw [hF, hF, hst]
  · intro hA
    refine ⟨fun m => if h : ∃ s, decode s = m then decode (U h.choose) else m, fun s => ?_⟩
    have hex : ∃ t, decode t = decode s := ⟨s, rfl⟩
    simp only [dif_pos hex]
    exact (hA _ _ hex.choose_spec).symm

/-- The decoded model **eventually follows the law `F`** along the orbit of `s`: past a transient,
each step of the world moves the reading by `F`. `Settles` is the case `F = id`, stated as eventual
constancy rather than as an eventual one-step law — over an orbit the two say the same thing. -/
def SettlesTo (U : X → X) (decode : X → M) (F : M → M) (s : X) : Prop :=
  ∃ T, ∀ k ≥ T, decode (U^[k + 1] s) = F (decode (U^[k] s))

/-- **Eventual descent** ([Persistence] §10.1 read at §10.2's generality): the decoded model
eventually obeys the law `F` along every orbit from a `U`-closed `B` **iff** it obeys `F` at every
state of the ω-limit set. The eventual-decoupling statement (`eventual_decoupling_iff`, whose
conclusion is read-only-on-`R` through a faithful decoder) is the identity-law case of this, exactly
as `decoupling_is_identity_law` is the identity-law case of `descent_iff`.

The two directions are the two halves of the ω-limit picture. Backward, orbits from `B` are inside
`ω B` past the transient, where the law holds by hypothesis. Forward argues on the limit *cycle*: a
state of `ω B` returns to itself (`exists_period`), so a law obeyed eventually is obeyed at the
state itself — read the hypothesis at a multiple of the period, past the transient, and the orbit
has come back to where it started.

No cell structure and no faithfulness are needed: this is a statement about an endofunction, a
decoder, and a candidate law. What it does NOT say is that some `F` exists — only descent
(`descent_iff`, `Autonomous`) decides that, and here `F` is given. -/
theorem eventual_descent_iff [Finite X] {U : X → X} {decode : X → M} {F : M → M} {B : Set X}
    (hB : ∀ s ∈ B, U s ∈ B) :
    (∀ s ∈ B, SettlesTo U decode F s) ↔ (∀ s ∈ omegaLimit U B, decode (U s) = F (decode s)) := by
  constructor
  · intro hset s hs
    obtain ⟨p, hp1, hp⟩ := exists_period U hB hs
    obtain ⟨T, hT⟩ := hset s (omegaLimit_subset U B hs)
    have hper : ∀ j : ℕ, U^[p * j] s = s := by
      intro j
      induction j with
      | zero => simp
      | succ j ih =>
          have hrw : p * (j + 1) = p * j + p := by ring
          rw [hrw, Function.iterate_add_apply, hp, ih]
    have h := hT (p * T) (Nat.le_mul_of_pos_left T hp1)
    rwa [Function.iterate_succ_apply', hper T] at h
  · intro hlaw s hs
    obtain ⟨N, hN⟩ := mem_omegaLimit_iterate U hB
    refine ⟨N, fun k hk => ?_⟩
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
    have hmem : U^[N + j] s ∈ omegaLimit U B := by
      rw [Nat.add_comm, Function.iterate_add_apply]
      exact iterate_mem_omegaLimit U hB (hN s hs) j
    rw [Function.iterate_succ_apply']
    exact hlaw _ hmem

/-- **[Decoupling] §3 Lemma 3.1, relocated: the identity-law case of descent.** Under a faithful
decoder the induced law is the IDENTITY exactly when `U` is read-only on `R`. So persistence is not
a separate phenomenon — it is the `F = id` fibre of the descent hierarchy, and each relaxation moves
the read-only requirement rather than removing it. -/
theorem decoupling_is_identity_law {U : Mem ι V → Mem ι V} {R : Set ι} {decode : Mem ι V → M}
    (hf : Faithful decode R) : (∀ s, decode (U s) = decode s) ↔ Fixes U R :=
  ⟨fun h => fixes_of_persists hf h, fun h s => hf.dependsOn _ _ fun a ha => h s a ha⟩

/-! ### The static hierarchy: conserved quantities ([Persistence] §4)

Between the read-only region of [Decoupling] §3 and the moving observer's ceiling sits one more
class of decoder: the **static lens** — a single `ℓ : Mem → M` with `ℓ ∘ U = ℓ`, no faithfulness, no
region structure. Such an `ℓ` is a conserved quantity of the dynamics, and it is exactly a function
constant on the components of the transition graph, so the static-lens capacity is the number of
components. Three inequalities place it: read-only cells ≤ components ≤ recurrent core.

What a static lens buys is strictly less than what a code region buys. It carries a conserved
quantity, not a program: [Decoupling]'s `necessity_needs_faithful` is the observation that a lossy
persistent lens yields no runnable region at all. -/

/-- The equivalence generated by one step of the update: `s` and `t` are related when a chain of
forward steps, taken in either direction, joins them. Its classes are the weakly-connected
components of the transition graph. Stated at an arbitrary carrier `X`: the definition uses
nothing of `Mem ι V`, and `staticLens_factors` through `hierarchy` below instantiate it there with
no change to their own statements. -/
def orbitRel (U : X → X) : X → X → Prop :=
  Relation.EqvGen fun s t => t = U s

/-- The setoid of `orbitRel`. `Quotient (orbitSetoid U)` is the set of **components**, and its
cardinality is the static-lens capacity ([Persistence] §4, L2). -/
def orbitSetoid (U : X → X) : Setoid X :=
  Relation.EqvGen.setoid fun s t => t = U s

/-- One step relates a state to its successor. -/
theorem orbitRel_step (U : X → X) (s : X) : orbitRel U s (U s) :=
  Relation.EqvGen.rel _ _ rfl

/-- Every state is related to all of its iterates: the orbit lies in one component. -/
theorem orbitRel_iterate (U : X → X) (s : X) (k : ℕ) :
    orbitRel U s (U^[k] s) := by
  induction k with
  | zero => exact Relation.EqvGen.refl _
  | succ k ih =>
      have hstep : orbitRel U (U^[k] s) (U^[k + 1] s) := by
        have h := orbitRel_step U (U^[k] s)
        rwa [← Function.iterate_succ_apply' U k s] at h
      exact Relation.EqvGen.trans _ _ _ ih hstep

/-- **A static lens is exactly a function constant on the components** ([Persistence] §4, L2).
Forward is an induction over the generated equivalence; backward is the single step `s ∼ U s`. -/
theorem staticLens_factors {U : Mem ι V → Mem ι V} (ℓ : Mem ι V → M) :
    (∀ s, ℓ (U s) = ℓ s) ↔ ∀ s t, orbitRel U s t → ℓ s = ℓ t := by
  constructor
  · intro h s t hst
    induction hst with
    | rel x y hxy => subst hxy; exact (h x).symm
    | refl x => rfl
    | symm x y _ ih => exact ih.symm
    | trans x y z _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  · intro h s
    exact (h s (U s) (orbitRel_step U s)).symm

/-- **The static capacity is attained**: the quotient map is itself a static lens, and it is
surjective — so a model of size `#components` persists under a decoder that never moves. -/
theorem components_carries (U : Mem ι V → Mem ι V) :
    (∀ s, Quotient.mk (orbitSetoid U) (U s) = Quotient.mk (orbitSetoid U) s) ∧
      Function.Surjective (Quotient.mk (orbitSetoid U)) :=
  ⟨fun s => Quotient.sound (Relation.EqvGen.symm _ _ (orbitRel_step U s)),
    Quotient.mk_surjective⟩

/-- **The static capacity is the number of components** ([Persistence] §4, L2), the upper half: a
static lens is constant on the components (`staticLens_factors`), hence factors through the
quotient, and a surjection cannot leave its target bigger than its source. -/
theorem staticCapacity_le [Finite ι] [Finite V] {U : Mem ι V → Mem ι V} {ℓ : Mem ι V → M}
    (hst : ∀ s, ℓ (U s) = ℓ s) (hsurj : Function.Surjective ℓ) :
    Nat.card M ≤ Nat.card (Quotient (orbitSetoid U)) := by
  have hfac : ∀ s t, (orbitSetoid U).r s t → ℓ s = ℓ t := (staticLens_factors ℓ).mp hst
  refine Nat.card_le_card_of_surjective (Quotient.lift ℓ hfac) ?_
  intro y
  obtain ⟨s, rfl⟩ := hsurj y
  exact ⟨Quotient.mk (orbitSetoid U) s, rfl⟩

/-- **Read-only cells are below the components** ([Persistence] §4, Proposition 4.1, first
inequality). Restriction to the never-rewritten cells is itself a static lens — the update leaves
those cells alone, so the restriction is unchanged in one step — and it is onto every assignment of
them. So all `|V| ^ |Fix U|` static models fit inside the component count. -/
theorem fix_le_components [Finite ι] [Finite V] (U : Mem ι V → Mem ι V) :
    Nat.card V ^ Nat.card ↥(Fix U) ≤ Nat.card (Quotient (orbitSetoid U)) := by
  classical
  rcases isEmpty_or_nonempty (Mem ι V) with hE | hNE
  · -- the memory itself is empty: no values, at least one cell, so the static capacity is `0`
    have hVe : IsEmpty V := ⟨fun v => hE.false fun _ => v⟩
    have hιne : Nonempty ι := by
      by_contra hc
      rw [not_nonempty_iff] at hc
      exact hE.false fun a => (hc.false a).elim
    have hFix : Fix U = Set.univ := by
      ext a
      simp only [Fix, Set.mem_univ, iff_true]
      exact fun s => (hE.false s).elim
    have hpos : 0 < Nat.card ↥(Fix U) := by
      rw [hFix, Nat.card_coe_set_eq, Set.ncard_univ]
      exact Nat.card_pos
    rw [Nat.card_of_isEmpty (α := V), zero_pow (by omega)]
    exact Nat.zero_le _
  · obtain ⟨s₀⟩ := hNE
    have : Fintype V := Fintype.ofFinite V
    have : Fintype ↥(Fix U) := Fintype.ofFinite _
    set ρ : Mem ι V → (↥(Fix U) → V) := fun s a => s (a : ι) with hρ
    have hst : ∀ s, ρ (U s) = ρ s := fun s => funext fun a => a.2 s
    have hsurj : Function.Surjective ρ := by
      intro v
      refine ⟨fun a => if h : a ∈ Fix U then v ⟨a, h⟩ else s₀ a, funext fun a => ?_⟩
      simp [hρ, a.2]
    have hle := staticCapacity_le hst hsurj
    have hcard : Nat.card (↥(Fix U) → V) = Nat.card V ^ Nat.card ↥(Fix U) := by
      rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
        Fintype.card_fun]
    rwa [hcard] at hle

/-- **The components are below the recurrent core** ([Persistence] §4, Proposition 4.1, second
inequality). Every component contains a core state — iterate past stabilization and the orbit lands
in the core without leaving its class — so the quotient map is already surjective from the core. -/
theorem components_le_core [Finite ι] [Finite V] (U : Mem ι V → Mem ι V) :
    Nat.card (Quotient (orbitSetoid U)) ≤ Nat.card ↥(core U) := by
  obtain ⟨N, hN⟩ := mem_omegaLimit_iterate U (univ_closed U)
  refine Nat.card_le_card_of_surjective
    (fun x : ↥(core U) => Quotient.mk (orbitSetoid U) (x : Mem ι V)) ?_
  intro q
  obtain ⟨s, rfl⟩ := Quotient.exists_rep q
  refine ⟨⟨U^[N] s, ?_⟩, ?_⟩
  · rw [core_eq_omegaLimit]
    exact hN s (Set.mem_univ s)
  · exact Quotient.sound (Relation.EqvGen.symm _ _ (orbitRel_iterate U s N))

/-- **The hierarchy** ([Persistence] §4, Proposition 4.1): a fixed region carries no more than a
conserved quantity, which carries no more than the moving observer's ceiling. The gaps are real —
rotate-left has an empty fixed region (`rotate_gap`) and a full core. -/
theorem hierarchy [Finite ι] [Finite V] (U : Mem ι V → Mem ι V) :
    Nat.card V ^ Nat.card ↥(Fix U) ≤ Nat.card (Quotient (orbitSetoid U)) ∧
      Nat.card (Quotient (orbitSetoid U)) ≤ Nat.card ↥(core U) :=
  ⟨fix_le_components U, components_le_core U⟩

end PersistenceCapacity
