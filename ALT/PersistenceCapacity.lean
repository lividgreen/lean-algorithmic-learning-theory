/-
Copyright (c) 2026 Mykola Palamarchuk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mykola Palamarchuk
-/
import Mathlib
import ALT.AdditiveComplexity
import ALT.BinaryConstant
import ALT.Decoupling
import ALT.GodelInternalization

-- Formal-check file, not Mathlib-destined: opt out of the house-style header linter.
set_option linter.style.header false

/-!
# Persistence capacity: moving decoders and the price of a frame ([Decoupling] §3.5)

A finite world is a state space `X` with an update `U : X → X`, and the cell-structured case is the
memory `Mem ι V = ι → V` ([Persistence] §2.1). The Decoupling Lemma
([Decoupling] §3, `Decoupling.decoupling_iff_persists_all`) says a faithfully-encoded model read off
a FIXED region survives iteration exactly when the update is read-only there; total overwrite
therefore excludes a persistent model ([Decoupling] §3, Corollary 3.2). A *time-dependent* decoder
evades that exclusion — on a cyclic string under rotation every cell is rewritten at every step, yet
a decoder tracking the moving window recovers the same model forever. This file states exactly what
the evasion costs ([Decoupling] §3.5).

A **lens family** `ℓ : ℕ → X → M` is a time-indexed decoder subject to no constraint whatever:
not locality, not simplicity, not computability. That is what makes the capacity theorem an
ABSOLUTE bound rather than a statement about some class of observers.

## Main results

* `core_bijOn` — the update restricts to a bijection on the **recurrent core** `⋂ t, U^[t] '' univ`
  (the states surviving every number of steps).
* `carries_coreLens_eq` / `carries_frame_eqOn_core` — **the frames are determined on the core**:
  over ANY endofunction world, `U` restricted to the core is a permutation `corePerm`, and a carried
  family satisfies `ℓ t = ℓ 0 ∘ (corePerm U ^ t)⁻¹` there. Off the core the identity constrains
  nothing. This is what [Persistence] §2, Definition 2.2 appeals to in pricing a whole family by its
  reference frame: on the core all frames share one profile.
* `CbHe` / `CbHue` / `CbHe_le_core_factorial` / `CbHe_perm` / `CbHue_perm` — **the budgeted entropic
  capacities over a general endofunction world** ([Persistence] §2, Definitions 2.1–2.2; §5): the
  carried entropy of a reference frame *on the recurrent core*, per-frame-budgeted and uniformly
  budgeted. Capped by the core's factorial — the §3 ceiling in the entropic currency — and equal to
  `CbH` / `CbHu` when the world is a permutation, which `permCarries_iff_carries` explains: the two
  carrying predicates of this file are one predicate.
* `iterate_mem_core` — **the space bounds its own transient**: after `Nat.card X` steps every state
  is in the recurrent core, since the image chain strictly decreases until it stabilizes.
* `CbHev_eq_CbHeOn` — **eventual capacity from a basin IS exact capacity on its attractor**
  ([Persistence] §10.1 read at §5's budget). An observer allowed to be wrong for a while keeps
  exactly what an observer required to be right from the first step keeps over `ω(B)`, at the same
  price per frame: a transient is a shift of the clock and nothing else. Since `ω(B)` is a
  permutation world (`omegaPerm`), §7 applies to it verbatim.
* `hasMargin_iff` / `repair_tax` / `majority_margin` — the **robustness margin** ([Persistence]
  §10.1 + §2). Settling says the reading is right eventually; it says nothing about a *kick*. The
  margin is the largest number of cells that may be corrupted on the attractor with the settled
  value surviving — an attribute of the sub-system, not of the observer, since the condition never
  mentions the family. It **factors** into basin fatness and local constancy (`hasMargin_iff`), and
  it is **paid for in carried content** (`repair_tax`): distinct settled values are `e`-separated,
  so the `e`-balls around one representative per value pack disjointly into the memory,
  `#values * #Ball e ≤ #Mem`. Majority-vote write-back is the worked witness at margin one
  (`majority_margin`), and it saturates the bound exactly (`repair_tax_tight_majWorld`) — three-copy
  redundancy spends its whole capacity buying one cell of margin.
* `Intertwines.comp` / `uniformBudget_comp` / `tower_no_free_lunch` — **the tower** ([Persistence]
  §10.2 + §2). A sub-system is a world, so it hosts sub-systems. The **intertwining square** is the
  time-indexed substitution property, and dilation needs no second definition — a `τ`-dilated square
  is a square over `U^[τ]`. Squares **compose** and dilations **multiply** (`τ₁ * τ₂`); budgets
  **add**, one fixed builder running both levels' programs and composing their tabulations, the
  dilation charged its bit-length `O (Nat.size τ₂)` rather than its magnitude. A tower whose top law
  is `id` is therefore a carrying family of the *iterated base world* (`tower_carries`), so its
  entropy is capped by that world's uniform capacity at the *summed* budget: **stacking buys
  structure, never generic capacity**. `entropy_comp_le` adds that entropy is antitone up the
  levels — coarsening merges fibres, so each level reads no more than the level below.
* `CbHue_le_CbHe` — **owning beats renting by at most the clock, over an arbitrary endofunction**:
  the general-world form of `CbHu_le_CbH`, at `O (log (n + n !))`. The frames of a carried family
  need not repeat off the core, so the period argument is unavailable as stated; what carries the
  proof is that capacity asks which values are ACHIEVABLE, so the uniform family may be replaced by
  a clamped reindexing of itself (`clamp`) that repeats by construction and shares frame zero.
* `eventual_descent_iff` — **eventual descent**: a decoded model obeys the law `F` eventually along
  every orbit from `B` iff it obeys `F` on `ω(B)`. `eventual_decoupling_iff` is its identity-law
  case, as `decoupling_is_identity_law` is `descent_iff`'s.
* `KE_iterate_le` — **time dilation is nearly free on the rule side**: `K (U^[τ])` is `K (U)` plus
  `O (log τ)`, via one fixed self-composition builder, `τ` entering only through its numeral. A
  family
  reading every `τ` steps is a family over `U^[τ]`, so a slower reading is not a cheaper one.
* `capacity_horizon_le` / `capacity_horizon_ge` — the maximal model persistable for `T` steps has
  exactly `|U^[T] '' univ|` elements ([Decoupling] §3.5, Proposition 3.5, the finite-horizon half).
* `capacity_core` / `capacity_core_ge` / `capacity_core_iff` — letting `T → ∞`, a persistent model
  of size `m` exists iff `m ≤ |core U|` ([Decoupling] §3.5, Proposition 3.5). What obstructs memory
  is not overwriting but irreversibility.
* `static_le_moving` / `rotate_gap` — the static capacity of [Decoupling] §3 (Corollary 3.3) never
  exceeds the moving one, and the gap can be total: rotate-left has static capacity `0` (it rewrites
  every cell) and moving capacity the whole memory. Total overwrite precludes persistent content at
  a fixed ADDRESS, not persistent content.
* `lens_bijOn_core` / `ledger` / `ledger_determines` — the price of the escape. If the family
  carries a MAXIMAL model then every frame is a bijection on the core and `U` restricted to the core
  is `ℓ₁⁻¹ ∘ ℓ₀`: the world's recurrent rule is recoverable from the observer's first two frames.
* `ledger_K` — the same in complexity form: `KE (U ↾ core) ≤ KE ℓ₀ + KE ℓ₁ + O(1)`, the constant
  being the length of a single fixed invert-and-compose program (`icode`) that depends on neither
  the world, the lens, the enumerations, nor the size of the memory. The complexity has not
  vanished; it has been relocated, out of the world and into the decoder.
* `eventual_decoupling_iff` — a model correct only EVENTUALLY (a self-repairing code region) settles
  along every orbit from a `U`-closed basin `B` iff `U` is read-only on `R` over the ω-limit set
  `⋂ t, U^[t] '' B`. [Decoupling] §3, Proposition 3.4 is the case `ω B = B`.
* `staticLens_factors` / `hierarchy` — the static stratum between the two ([Persistence] §4): a
  lens with `ℓ ∘ U = ℓ` is exactly a function constant on the components of the transition graph,
  and read-only cells ≤ components ≤ recurrent core. A conserved quantity is what a moving observer
  can be undercut to, and it is strictly less than a runnable code region.
* `Cb` / `capacity_sandwich` — the **budgeted persistence capacity** ([Persistence] §5): the largest
  model carried by a family whose every frame's core table costs at most `b` bits. Monotone in the
  budget, capped by the core at every budget, and above the static levels past a finite one.
* `collapse` / `collapse_balanced` / `collapse_generic` — **the price is generically unpayable**
  ([Persistence] §7). Over a permutation world the second frame is forced to be `ℓ₀ ∘ U⁻¹`, a budget
  of `b` bits describes at most `2 ^ (b + 1)` frames, and each frame is hit by exactly one coset of
  the lens's stabilizer — so all but a `2 ^ (b + 1) / N_bal` fraction of worlds admit NO affordable
  moving decoder at all, with `N_bal = n ! / ((n / m) !) ^ m` the balanced-lens count.
* `collapse_union` — the same **uniformly over the reference frame** ([Persistence] §7,
  Corollary 7.4): summing the per-frame count by the Kraft inequality, all but a `2 ^ (-d)` fraction
  of worlds price *every* persistent reading at the entropy it carries. There are no discounts.
* `CbH` / `CbH_collapse` / `CbH_ge_marking'` — **the entropic capacity is pinned at `Θ(b)`**
  ([Persistence] §5, Definition 5.4; §7, Corollary 7.5(i)). The honest currency is not the label
  count but the carried entropy of the reference frame — its relabelling-class size. Generically
  `C_b^H (U) ≤ 2b + d + 2` (the cap, from the Kraft union), while over EVERY permutation world `r`
  marks riding along carry `log₂ (n ! / (n − r)!)` (the floor, exact). An observer keeps, to within
  a factor two, exactly the entropy it pays for.
* `KE_markingLens_le` — **the marks are provably cheap** ([Persistence] §5, Proposition 5.3): an
  explicit program of length `O ((r + 1) · log₂ n)`, uniform over where the marks sit, tabulates
  `r` marks on `n` states. It discharges the floor's price hypothesis.

## Scope

`KE` is the additive Kolmogorov complexity of `ALT.AdditiveComplexity` (program length under a
fixed self-delimiting encoding of `Nat.Partrec.Code`), and the finite objects enter it through an
explicit tabulation (`frameTable`, `worldTable`, `coreTable`, `lensTable`) along a chosen
enumeration of the core and of the model.

The capacity objects `Cb`, `CbH` and `CbHe` are stated in **cardinality form** — they are valued in
the reference frame's relabelling-class size, which is `2 ^ E` for the carried entropy `E`. The
`log₂` is applied paper-side; taking the supremum before the logarithm loses nothing, since `log₂`
is monotone and the families are finite.

**Which results need which world.** The ceiling of §3 (`core`, `Carries`, `capacity_core_iff`) and
the core determination (`carries_coreLens_eq`) hold over an arbitrary finite state type `X` with an
arbitrary `U : X → X`, which is the generality [Persistence] §2.1 states. The cell structure
`Mem ι V` is taken only where it carries the content: the read-only stratum and the static
hierarchy (`Fix`, `static_le_moving`, `rotate_gap`, `hierarchy`), the eventual-persistence
relaxation (`eventual_decoupling_iff`, `majority_selfRepair`), and the complexity-form ledger. The
counting of §7 (`collapse`, `CbH`) is stated over a permutation world, where the world is its own
recurrent core; `CbHe` / `CbHue` are the same budgeted objects over an arbitrary endofunction, and
`CbHe_perm` / `CbHue_perm` check that the two agree exactly where both apply.

Over a general world, value and price are measured on different sets, deliberately: the carried
entropy is valued on the recurrent core, per [Persistence] §2, Definition 2.2, while the budget
prices the ambient table `lensCode` as everywhere else. The reason is given at `CbHe`. The basin
objects (`CbHev`, `CbHeOn`) keep that split for the same reason, and it is what makes their
reduction budget-free: shifting a clock reuses frames, where restricting them to a sub-world would
have to re-index a table.

Two steps of [Persistence] §7 are deliberately left at paper level: the Stirling asymptotic
`log₂ N_bal = κ · n − ((2 ^ κ − 1) / 2) · log₂ n − O(2 ^ κ)`, which converts the exact count
`card_balancedLenses` into the paper's threshold and is presentation, not content; and the paper's
CONDITIONAL form `K (ℓ₁ | ℓ₀)`, of which the plain-`KE` bounds here are the unconditional
first cut. Neither is used by anything proved here.

Nothing here is assumed rather than proved. The per-frame price of the marking family
([Persistence] §5, Proposition 5.3 — `r` marks on `n` states cost `O (r · log₂ n)` bits to
tabulate) was the development's last named hypothesis; it is now discharged as an explicit code
(`KE_markingLens_le`), so the marking floor holds outright (`CbH_ge_marking'`). The hypothesis form
`CbH_ge_marking` is kept: it is the general statement, taking any price bound whatever.
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
theorem univ_closed (U : X → X) : ∀ s ∈ (Set.univ : Set X), U s ∈ Set.univ :=
  fun _ _ => Set.mem_univ _

/-- One step of the image chain: `U^[t+1] '' B = U '' (U^[t] '' B)`. -/
theorem image_iterate_succ (U : X → X) (B : Set X) (t : ℕ) :
    (U^[t + 1]) '' B = U '' ((U^[t]) '' B) := by
  rw [← Set.image_comp, ← Function.iterate_succ']

/-- The image chain of a `U`-closed set decreases. -/
theorem image_iterate_subset (U : X → X) {B : Set X}
    (hB : ∀ s ∈ B, U s ∈ B) (t : ℕ) : (U^[t + 1]) '' B ⊆ (U^[t]) '' B := by
  rintro _ ⟨b, hb, rfl⟩
  exact ⟨U b, hB b hb, (Function.iterate_succ_apply U t b).symm⟩

/-- The image chain of a `U`-closed set is antitone. -/
theorem image_iterate_antitone (U : X → X) {B : Set X}
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
theorem exists_image_stable [Finite X] (U : X → X) {B : Set X}
    (hB : ∀ s ∈ B, U s ∈ B) : ∃ N : ℕ, ∀ t, N ≤ t → (U^[t]) '' B = (U^[N]) '' B :=
  let ⟨N, _, h⟩ := exists_image_stable_le U hB
  ⟨N, h⟩

/-- Past the stabilization index the ω-limit set **is** the image. -/
theorem omegaLimit_eq_image [Finite X] (U : X → X) {B : Set X}
    (hB : ∀ s ∈ B, U s ∈ B) {N : ℕ} (hN : ∀ t, N ≤ t → (U^[t]) '' B = (U^[N]) '' B) :
    omegaLimit U B = (U^[N]) '' B := by
  refine Set.Subset.antisymm (Set.iInter_subset _ N) fun x hx => ?_
  refine Set.mem_iInter.mpr fun t => ?_
  rcases Nat.lt_or_ge t N with h | h
  · exact image_iterate_antitone U hB h.le hx
  · rw [hN t h]; exact hx

/-- The ω-limit set sits inside its basin (the `t = 0` component of the intersection). -/
theorem omegaLimit_subset (U : X → X) (B : Set X) : omegaLimit U B ⊆ B := by
  intro x hx
  have := Set.mem_iInter.mp hx 0
  simpa using this

/-- Every state of a `U`-closed `B` lands in the ω-limit set after finitely many steps. -/
theorem mem_omegaLimit_iterate [Finite X] (U : X → X) {B : Set X}
    (hB : ∀ s ∈ B, U s ∈ B) : ∃ N : ℕ, ∀ s ∈ B, (U^[N]) s ∈ omegaLimit U B := by
  obtain ⟨N, hN⟩ := exists_image_stable U hB
  exact ⟨N, fun s hs => by rw [omegaLimit_eq_image U hB hN]; exact ⟨s, hs, rfl⟩⟩

/-- The ω-limit set is invariant: `U` maps it ONTO itself. -/
theorem image_omegaLimit [Finite X] (U : X → X) {B : Set X}
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
theorem bijOn_iterate {U : X → X} {s : Set X} (h : Set.BijOn U s s) (n : ℕ) :
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
theorem core_eq_image [Finite X] (U : X → X) :
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
theorem Carries.carriesUpTo {U : X → X} {ℓ : Lens X M} (h : Carries U ℓ) (T : ℕ) :
    CarriesUpTo U ℓ T := ⟨h.1, fun t _ s => h.2 t s⟩

/-- The `⇒` half in one line: `ℓ 0` is constant on the fibres of `U^[T]`, so it factors through the
`T`-step image. -/
theorem const_on_fibres {U : X → X} {ℓ : Lens X M} {T : ℕ} (h : CarriesUpTo U ℓ T)
    {s t : X} (hst : U^[T] s = U^[T] t) : ℓ 0 s = ℓ 0 t := by
  rw [← h.2 T le_rfl s, ← h.2 T le_rfl t, hst]

/-- **Persistence capacity at horizon `T`, the ceiling** ([Decoupling] §3.5, Proposition 3.5). Any
lens family persisting `T` steps carries a model no larger than the `T`-step image of the world —
whatever the lens. Reading persistence at `t = T` makes `ℓ T` a surjection from that image onto the
model, and a surjection cannot leave the target bigger than the source. -/
theorem capacity_horizon_le_ncard [Finite X] [Fintype M] {U : X → X}
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
theorem invFunOn_iterate_left [Finite X] [Nonempty (X)]
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
  haveI : Nonempty (X) := ⟨hne.some⟩
  haveI : Fintype ↥(core U) := Fintype.ofFinite _
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

/-! ### Determination on the core: every frame is the reference frame, transported

[Persistence] §2, Definition 2.2 prices an entire persistent family by the carried entropy of its
reference frame *on the recurrent core*, on the ground that "on the core every frame is `ℓ₀`
composed with a power of the core permutation, so all frames share one profile". This section proves
that, for an arbitrary endofunction world.

Off the core there is nothing to prove and nothing to say. `U` need not be injective on the
transient states, distinct frames may read them however they like, and the persistence identity
constrains none of it. On the core `U` *is* a bijection (`core_bijOn`), hence a genuine permutation
`corePerm` of the core, and the identity solves for `ℓ t` exactly as it does over a permutation
world (`permCarries_frame_eq`) — the difference being that here the inverse exists only after
restricting. -/

/-- **The recurrent rule, as a permutation of the core.** `U` restricts to a bijection there
(`core_bijOn`), so the core carries a genuine `Equiv.Perm`: the world's reversible part, extracted
from an update that need not be reversible anywhere else. -/
noncomputable def corePerm [Finite X] (U : X → X) : Equiv.Perm ↥(core U) :=
  Set.BijOn.equiv U (core_bijOn U)

@[simp] theorem corePerm_apply [Finite X] (U : X → X) (x : ↥(core U)) :
    ((corePerm U x : X)) = U x := rfl

/-- The core permutation's powers are the world's iterates, read on the core. -/
theorem corePerm_pow_apply [Finite X] (U : X → X) (t : ℕ) (x : ↥(core U)) :
    (((corePerm U ^ t) x : X)) = U^[t] x := by
  induction t generalizing x with
  | zero => rfl
  | succ t ih =>
      rw [pow_succ, Equiv.Perm.mul_apply, ih, corePerm_apply, Function.iterate_succ_apply]

/-- **The rule on an attractor, as a permutation.** `U` restricts to a bijection on the ω-limit set
of any closed `B` (`omegaLimit_bijOn`), so an attractor carries a genuine `Equiv.Perm`: the
recurrent rule of the sub-world that orbits from `B` settle into. `corePerm` is the case
`B = univ`. -/
noncomputable def omegaPerm [Finite X] (U : X → X) {B : Set X} (hB : ∀ s ∈ B, U s ∈ B) :
    Equiv.Perm ↥(omegaLimit U B) :=
  Set.BijOn.equiv U (omegaLimit_bijOn U hB)

@[simp] theorem omegaPerm_apply [Finite X] (U : X → X) {B : Set X} (hB : ∀ s ∈ B, U s ∈ B)
    (x : ↥(omegaLimit U B)) : ((omegaPerm U hB x : X)) = U x := rfl

/-- The recurrent core is the attractor of the whole world, and its permutation is that
attractor's. -/
theorem corePerm_eq_omegaPerm [Finite X] (U : X → X) :
    corePerm U = omegaPerm U (univ_closed U) := rfl

/-- The attractor permutation's powers are the world's iterates, read on the attractor. -/
theorem omegaPerm_pow_apply [Finite X] (U : X → X) {B : Set X} (hB : ∀ s ∈ B, U s ∈ B) (t : ℕ)
    (x : ↥(omegaLimit U B)) : (((omegaPerm U hB ^ t) x : X)) = U^[t] x := by
  induction t generalizing x with
  | zero => rfl
  | succ t ih =>
      rw [pow_succ, Equiv.Perm.mul_apply, ih, omegaPerm_apply, Function.iterate_succ_apply]

/-- A lens **restricted to the recurrent core** — the only part of it the persistence identity
constrains, and the part [Persistence] §2, Definition 2.2 measures the carried entropy of. This is
`Set.restrict` at `core U`; the ω-limit sections below use `Set.restrict` directly. -/
def coreLens (U : X → X) (f : X → M) : ↥(core U) → M := fun x => f x

theorem coreLens_eq_restrict (U : X → X) (f : X → M) : coreLens U f = (core U).restrict f := rfl

/-- **Every frame is the reference frame, transported by the recurrent rule** — the endofunction
analogue of `permCarries_frame_eq`, and the fact [Persistence] §2, Definition 2.2 appeals to when it
prices a whole family by `E (ℓ₀)`.

`corePerm U ^ t` is invertible, so the persistence identity `ℓ t ∘ U^[t] = ℓ 0` solves on the core
for `ℓ t = ℓ 0 ∘ (corePerm U ^ t)⁻¹`: a carried family has no freedom on the core past its reference
frame, over ANY endofunction world. Whatever the frames do on the transient states — where they are
wholly unconstrained — the recurrent part of every reading is one relabelling of `ℓ 0`.

Spelled as an explicit composition rather than through the relabelling action, for the reason given
at `arrowAction` below: the two are definitionally equal, and only this one means what it says after
elaboration. -/
theorem carries_coreLens_eq [Finite X] {U : X → X} {ℓ : Lens X M} (h : Carries U ℓ) (t : ℕ) :
    coreLens U (ℓ t) = coreLens U (ℓ 0) ∘ ⇑(corePerm U ^ t)⁻¹ := by
  funext x
  have hy := h.2 t (((corePerm U ^ t)⁻¹ x : ↥(core U)) : X)
  rw [← corePerm_pow_apply U t ((corePerm U ^ t)⁻¹ x)] at hy
  simpa [coreLens] using hy

/-- **Determination on the core, ambiently**: the same statement read back in `X`, with the core
permutation's inverse spelled as `U`'s inverse along the core. `Set.EqOn` is the honest form — off
the core the identity says nothing. -/
theorem carries_frame_eqOn_core [Finite X] [Nonempty X] {U : X → X} {ℓ : Lens X M}
    (h : Carries U ℓ) (t : ℕ) :
    Set.EqOn (ℓ t) (ℓ 0 ∘ (Function.invFunOn U (core U))^[t]) (core U) := by
  intro x hx
  obtain ⟨z, hz, rfl⟩ := (bijOn_iterate (core_bijOn U) t).surjOn hx
  simp only [Function.comp_apply, invFunOn_iterate_left U hz t]
  exact h.2 t z

/-! ### The static capacity is below the moving one, and the gap can be total -/

/-- The cells the update never rewrites — the maximal static code region of [Decoupling] §3
(Corollary 3.3). -/
def Fix (U : Mem ι V → Mem ι V) : Set ι := {a | ∀ s, U s a = s a}

/-- `U` is read-only on `Fix U` (`Decoupling.Fixes`), by definition. -/
theorem fixes_fix (U : Mem ι V → Mem ι V) : Fixes U (Fix U) := fun _ _ ha => ha _

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
      simp only [Fix, Set.mem_setOf_eq, Set.mem_univ, iff_true]
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
    haveI : Fintype ↥(Fix U) := Fintype.ofFinite _
    have hcard : Nat.card (↥(Fix U) → V) = Fintype.card V ^ Nat.card ↥(Fix U) := by
      rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_fun]
    rwa [hcard] at hle

/-- **The gap is total** ([Decoupling] §3.5(i)). Rotate-left on a cyclic string rewrites EVERY cell
— `Fix U = ∅`, so [Decoupling] §3 Corollary 3.2 applies and the static capacity is zero — yet it is
a bijection, so the core is the whole memory and the moving capacity is `log₂ |Mem|` bits. Total
overwrite precludes persistent content at a fixed ADDRESS, not persistent content. -/
theorem rotate_gap (n : ℕ) (hn : 2 ≤ n) :
    ∃ U : Mem (ZMod n) Bool → Mem (ZMod n) Bool, Fix U = ∅ ∧ core U = Set.univ := by
  haveI : NeZero n := ⟨by omega⟩
  haveI : Fact (1 < n) := ⟨by omega⟩
  refine ⟨fun s i => s (i + 1), ?_, ?_⟩
  · ext a
    simp only [Fix, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_forall]
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

/-! ### The observer's ledger: the price of a moving lens ([Decoupling] §3.5(iii))

If the family carries the MAXIMAL model then every frame is a bijection on the core, and the world's
recurrent rule falls out of the observer's first two frames. The complexity does not vanish; it is
relocated, out of the world and into the decoder. -/

/-- Every frame of a maximal family is a bijection from the core onto the model. -/
theorem lens_bijOn_core [Finite ι] [Finite V] [Fintype M] {U : Mem ι V → Mem ι V}
    {ℓ : Lens (Mem ι V) M} (h : Carries U ℓ) (hmax : Fintype.card M = Nat.card (core U)) (t : ℕ) :
    Set.BijOn (ℓ t) (core U) Set.univ := by
  obtain ⟨N, hcore, hstab⟩ := core_eq_image U
  -- past the stabilization index, surjectivity onto the model plus a cardinality count
  have hbase : ∀ T, N ≤ T → Set.BijOn (ℓ T) (core U) Set.univ := by
    intro T hT
    have hsurj : Set.SurjOn (ℓ T) (core U) Set.univ := by
      intro m _
      obtain ⟨s, hs⟩ := h.1 m
      refine ⟨U^[T] s, ?_, by rw [h.2 T s, hs]⟩
      rw [hcore, ← hstab T hT]
      exact ⟨s, Set.mem_univ _, rfl⟩
    have himg : (ℓ T) '' (core U) = Set.univ :=
      Set.eq_univ_of_univ_subset (fun m hm => hsurj hm)
    have hncard : ((ℓ T) '' (core U)).ncard = (core U).ncard := by
      rw [himg, Set.ncard_univ, ← Nat.card_coe_set_eq, ← hmax, Nat.card_eq_fintype_card]
    exact ⟨fun x _ => Set.mem_univ _, Set.injOn_of_ncard_image_eq hncard (Set.toFinite _), hsurj⟩
  -- a general frame is the stabilized frame precomposed with `U^[N]`, a bijection of the core
  have hUN : Set.BijOn (U^[N]) (core U) (core U) := bijOn_iterate (core_bijOn U) N
  have heq : Set.EqOn (ℓ (t + N) ∘ U^[N]) (ℓ t) (core U) := by
    intro x hx
    have hxt : x ∈ (U^[t]) '' Set.univ := Set.mem_iInter.mp hx t
    obtain ⟨z, -, rfl⟩ := hxt
    have h1 : (U^[N]) (U^[t] z) = U^[t + N] z := by
      rw [← Function.iterate_add_apply, Nat.add_comm]
    simp only [Function.comp_apply, h1, h.2 (t + N) z, h.2 t z]
  exact ((hbase (t + N) (by omega)).comp hUN).congr heq

/-- **The ledger** ([Decoupling] §3.5(iii)). For a maximal model, `U` restricted to the core is
`ℓ₁⁻¹ ∘ ℓ₀`: the observer's first two frames DETERMINE the world's recurrent update rule. The
complexity has not vanished — it has moved out of the world and into the decoder. -/
theorem ledger [Finite ι] [Finite V] [Fintype M] [Nonempty (Mem ι V)] {U : Mem ι V → Mem ι V}
    {ℓ : Lens (Mem ι V) M} (h : Carries U ℓ) (hmax : Fintype.card M = Nat.card (core U))
    {s : Mem ι V} (hs : s ∈ core U) :
    U s = Function.invFunOn (ℓ 1) (core U) (ℓ 0 s) := by
  have hb := lens_bijOn_core h hmax 1
  have hUs : U s ∈ core U := (core_bijOn U).mapsTo hs
  have h1 : ℓ 1 (U s) = ℓ 0 s := by simpa using h.2 1 s
  have hinv := hb.injOn.leftInvOn_invFunOn hUs
  rw [← h1, hinv]

/-- **The ledger, choice-free form.** Two worlds with the same recurrent core, observed by families
whose first two frames agree, have the SAME recurrent rule. This is the determination content of
`ledger` — "the world's rule is recoverable from the observer's first two frames" — with no inverse
function, hence no choice. The Kolmogorov reading `K (U ↾ core) ≤ K ℓ₀ + K ℓ₁ + O(1)` rides the
standard encoding of these finite tables. -/
theorem ledger_determines [Finite ι] [Finite V] [Fintype M] {U U' : Mem ι V → Mem ι V}
    {ℓ ℓ' : Lens (Mem ι V) M} (h : Carries U ℓ) (hmax : Fintype.card M = Nat.card (core U))
    (h' : Carries U' ℓ') (hcore : core U = core U')
    (h0 : ℓ 0 = ℓ' 0) (h1 : ℓ 1 = ℓ' 1) : ∀ s ∈ core U, U s = U' s := by
  intro s hs
  have hinj := (lens_bijOn_core h hmax 1).injOn
  have hUs : U s ∈ core U := (core_bijOn U).mapsTo hs
  have hU's : U' s ∈ core U := by
    rw [hcore]
    exact (core_bijOn U').mapsTo (hcore ▸ hs)
  refine hinj hUs hU's ?_
  have e1 : ℓ 1 (U s) = ℓ 0 s := by simpa using h.2 1 s
  have e2 : ℓ' 1 (U' s) = ℓ' 0 s := by simpa using h'.2 1 s
  rw [e1, h1] at *
  rw [h0]
  rw [← e2, h1]

/-! ### The ledger in complexity form ([Decoupling] §3.5(iii))

The identity `U ↾ core = ℓ₁⁻¹ ∘ ℓ₀` becomes a Kolmogorov bound once the three finite objects are
tabulated. Fix an enumeration `eC` of the core and `eM` of the model; a frame tabulates as the list
of model indices it reads off the core states (`frameTable`), and the world's recurrent rule
tabulates as the list of core indices it steps to (`worldTable`). Then ONE program — invert the
second table and compose it with the first (`invcomp`, a single fixed `Code`, `icode`) — recovers
the world's table from the observer's first two frames, so

`KE (worldTable) ≤ KE (frameTable 0) + KE (frameTable 1) + O(1)`

with a constant that does not depend on the world, the lens, the enumerations, or the memory size.
The world's recurrent rule is no more complex than the observer's first two frames: the complexity
has not vanished, it has been relocated into the decoder. -/

open AdditiveComplexity KolmogorovComplexity Nat.Partrec Nat.Partrec.Code

/-- First-occurrence index of `v` in a list of naturals (`0` if absent) — table inversion. -/
def idx (v : ℕ) (L : List ℕ) : ℕ :=
  L.rec 0 fun b _ IH => if b = v then 0 else IH + 1

@[simp] theorem idx_nil (v : ℕ) : idx v [] = 0 := rfl

@[simp] theorem idx_cons (v b : ℕ) (L : List ℕ) :
    idx v (b :: L) = if b = v then 0 else idx v L + 1 := rfl

/-- Table inversion is correct on a duplicate-free table: the index of the `i`-th entry is `i`. -/
theorem idx_getElem : ∀ {L : List ℕ}, L.Nodup → ∀ {i : ℕ} (hi : i < L.length), idx L[i] L = i
  | [], _, i, hi => absurd hi (by simp)
  | b :: T, _, 0, _ => by simp
  | b :: T, hL, (k + 1), hk => by
      rw [List.nodup_cons] at hL
      have hlt : k < T.length := by simpa using hk
      have hne : b ≠ T[k] := fun hcon => hL.1 (hcon ▸ List.getElem_mem hlt)
      have hrec : idx T[k] T = k := idx_getElem hL.2 hlt
      simpa [hne] using hrec

/-- Table inversion on an injective tabulation over `Fin n`. -/
theorem idx_map_finRange {n : ℕ} (f : Fin n → ℕ) (hf : Function.Injective f) (j : Fin n) :
    idx (f j) ((List.finRange n).map f) = (j : ℕ) := by
  have hnodup : ((List.finRange n).map f).Nodup :=
    (List.nodup_finRange n).map hf
  have hlen : ((List.finRange n).map f).length = n := by simp
  have hj : (j : ℕ) < ((List.finRange n).map f).length := by rw [hlen]; exact j.2
  have hget : ((List.finRange n).map f)[(j : ℕ)] = f j := by simp
  have := idx_getElem hnodup hj
  rwa [hget] at this

/-- **The fixed invert-and-compose program.** On the pair of encoded tables `⟨t₀, t₁⟩` it maps each
entry of `t₀` to its position in `t₁` — that is, it computes `t₁⁻¹ ∘ t₀`. -/
def invcomp (p : ℕ) : ℕ :=
  Encodable.encode
    (((Encodable.decode (α := List ℕ) p.unpair.1).getD []).map fun v =>
      idx v ((Encodable.decode (α := List ℕ) p.unpair.2).getD []))

theorem primrec_idx : Primrec fun p : ℕ × List ℕ => idx p.1 p.2 := by
  have h : Primrec₂ fun (p : ℕ × List ℕ) (t : ℕ × List ℕ × ℕ) =>
      if t.1 = p.1 then 0 else t.2.2 + 1 :=
    Primrec.ite (Primrec.eq.comp (Primrec.fst.comp Primrec.snd) (Primrec.fst.comp Primrec.fst))
      (Primrec.const 0) (Primrec.succ.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
  exact Primrec.list_rec Primrec.snd (Primrec.const 0) h

theorem primrec_invcomp : Primrec invcomp := by
  have hdec1 : Primrec fun p : ℕ => (Encodable.decode (α := List ℕ) p.unpair.1).getD [] :=
    Primrec.option_getD.comp (Primrec.decode.comp (Primrec.fst.comp Primrec.unpair))
      (Primrec.const [])
  have hdec2 : Primrec fun p : ℕ => (Encodable.decode (α := List ℕ) p.unpair.2).getD [] :=
    Primrec.option_getD.comp (Primrec.decode.comp (Primrec.snd.comp Primrec.unpair))
      (Primrec.const [])
  have hg : Primrec₂ fun (p : ℕ) (v : ℕ) =>
      idx v ((Encodable.decode (α := List ℕ) p.unpair.2).getD []) :=
    primrec_idx.comp (Primrec.pair Primrec.snd (hdec2.comp Primrec.fst))
  exact Primrec.encode.comp (Primrec.list_map hdec1 hg)

theorem partrec_invcomp : Nat.Partrec invcomp :=
  Partrec.nat_iff.mp primrec_invcomp.to_comp.partrec

/-- The invert-and-compose program as a single fixed `Code`: its length `elen icode` is the whole
constant in `ledger_K`, and it depends on nothing else. -/
noncomputable def icode : Code := Classical.choose (exists_code.mp partrec_invcomp)

theorem eval_icode (p : ℕ) : icode.eval p = Part.some (invcomp p) := by
  have h := congrFun (Classical.choose_spec (exists_code.mp partrec_invcomp)) p
  simpa [icode] using h

/-- If `b` outputs `v` on input `j`, then `comp a b` runs `a` on `v` (the `comp` eval law is
definitional). -/
private theorem eval_comp_some {a b : Code} {j v : ℕ} (hv : eval b j = Part.some v) :
    eval (comp a b) j = eval a v := by
  change eval b j >>= eval a = eval a v
  rw [hv]
  exact Part.bind_some v (eval a)

/-- The observer's frame `t`, **tabulated**: the model index each core state is read as, listed
along an enumeration `eC` of the core. -/
def frameTable {n : ℕ} (U : Mem ι V → Mem ι V) (ℓ : Lens (Mem ι V) M) (t : ℕ)
    (eC : ↥(core U) ≃ Fin n) (eM : M ≃ Fin n) : List ℕ :=
  (List.finRange n).map fun i => ((eM (ℓ t ((eC.symm i : ↥(core U)) : Mem ι V)) : Fin n) : ℕ)

/-- The world's recurrent rule, **tabulated**: the core index each core state steps to. -/
noncomputable def worldTable [Finite ι] [Finite V] {n : ℕ} (U : Mem ι V → Mem ι V)
    (eC : ↥(core U) ≃ Fin n) : List ℕ :=
  (List.finRange n).map fun i =>
    ((eC ⟨U ((eC.symm i : ↥(core U)) : Mem ι V),
      (core_bijOn U).mapsTo (eC.symm i).2⟩ : Fin n) : ℕ)

/-- The fixed program recovers the world's table from the observer's first two frames. -/
theorem invcomp_frameTables [Finite ι] [Finite V] [Fintype M] {U : Mem ι V → Mem ι V}
    {ℓ : Lens (Mem ι V) M} (h : Carries U ℓ) (hmax : Fintype.card M = Nat.card (core U))
    {n : ℕ} (eC : ↥(core U) ≃ Fin n) (eM : M ≃ Fin n) :
    invcomp (Nat.pair (Encodable.encode (frameTable U ℓ 0 eC eM))
      (Encodable.encode (frameTable U ℓ 1 eC eM))) = Encodable.encode (worldTable U eC) := by
  -- the two tabulations, as functions on the index set
  set f₀ : Fin n → ℕ := fun i => ((eM (ℓ 0 ((eC.symm i : ↥(core U)) : Mem ι V)) : Fin n) : ℕ)
    with hf₀
  set f₁ : Fin n → ℕ := fun i => ((eM (ℓ 1 ((eC.symm i : ↥(core U)) : Mem ι V)) : Fin n) : ℕ)
    with hf₁
  -- `ℓ 1` is injective on the core (maximal model), so its tabulation is injective
  have hinj₁ : Function.Injective f₁ := by
    intro i j hij
    have h1 : ℓ 1 ((eC.symm i : ↥(core U)) : Mem ι V) = ℓ 1 ((eC.symm j : ↥(core U)) : Mem ι V) :=
      eM.injective (Fin.val_injective hij)
    have h2 := (lens_bijOn_core h hmax 1).injOn (eC.symm i).2 (eC.symm j).2 h1
    exact eC.symm.injective (Subtype.ext h2)
  simp only [invcomp, Nat.unpair_pair, Encodable.encodek, Option.getD_some, frameTable, worldTable,
    List.map_map, ← hf₀, ← hf₁]
  refine congrArg Encodable.encode (List.map_congr_left fun i _ => ?_)
  -- the ledger, in index form: the core state `U s` is the unique one `ℓ 1` reads as `ℓ 0 s`
  set j₀ : Fin n := eC ⟨U ((eC.symm i : ↥(core U)) : Mem ι V),
    (core_bijOn U).mapsTo (eC.symm i).2⟩ with hj₀
  have hstep : f₁ j₀ = f₀ i := by
    have hval : ((eC.symm j₀ : ↥(core U)) : Mem ι V) = U ((eC.symm i : ↥(core U)) : Mem ι V) := by
      rw [hj₀, Equiv.symm_apply_apply]
    have hcarry : ℓ 1 (U ((eC.symm i : ↥(core U)) : Mem ι V))
        = ℓ 0 ((eC.symm i : ↥(core U)) : Mem ι V) := by
      simpa using h.2 1 ((eC.symm i : ↥(core U)) : Mem ι V)
    simp only [hf₀, hf₁, hval, hcarry]
  change idx (f₀ i) ((List.finRange n).map f₁) = (j₀ : ℕ)
  rw [← hstep]
  exact idx_map_finRange f₁ hinj₁ j₀

/-- **The ledger, in complexity form** ([Decoupling] §3.5(iii)). The world's recurrent rule is no
more complex than the observer's first two frames: `KE (U ↾ core) ≤ KE ℓ₀ + KE ℓ₁ + O(1)`, where the
constant is the length of the single fixed invert-and-compose program and depends on nothing —
neither the world, nor the lens, nor the enumerations, nor the size of the memory.

The complexity has not vanished; it has been RELOCATED, out of the world and into the decoder. An
observer that evades the Total-Overwrite Exclusion with a moving lens must therefore store, in its
first two frames, a description of the world's recurrent rule. -/
theorem ledger_K [Finite ι] [Finite V] [Fintype M] {U : Mem ι V → Mem ι V} {ℓ : Lens (Mem ι V) M}
    (h : Carries U ℓ) (hmax : Fintype.card M = Nat.card (core U))
    {n : ℕ} (eC : ↥(core U) ≃ Fin n) (eM : M ≃ Fin n) :
    KE (Encodable.encode (worldTable U eC))
      ≤ KE (Encodable.encode (frameTable U ℓ 0 eC eM))
        + KE (Encodable.encode (frameTable U ℓ 1 eC eM)) + (elen icode + 6) := by
  set a := Encodable.encode (frameTable U ℓ 0 eC eM) with ha
  set b := Encodable.encode (frameTable U ℓ 1 eC eM) with hb
  -- a shortest program for the pair of frames, extended by the fixed inverter
  obtain ⟨d, hd, hdlen⟩ := exists_min_E (Nat.pair a b)
  have hcomp : Computes (comp icode d) (Encodable.encode (worldTable U eC)) := by
    change eval (comp icode d) 0 = _
    rw [eval_comp_some hd, eval_icode, invcomp_frameTables h hmax eC eM]
  have hle := KE_comp_le hcomp
  have hsub := KE_subadditive a b
  omega

/-! ### Eventual persistence: a self-repairing code region ([Decoupling] §3.5, the relaxations)

Relax "the model is correct at every step" to "the model is correct eventually". The conclusion
relaxes from "read-only everywhere" to "read-only on the ω-limit set" — and nothing weaker. -/

/-- The decoded model **settles** along the orbit of `s`: it is eventually constant. -/
def Settles (U : Mem ι V → Mem ι V) (decode : Mem ι V → M) (s : Mem ι V) : Prop :=
  ∃ T, ∀ k ≥ T, decode (U^[k] s) = decode (U^[T] s)

/-- Every state of the ω-limit set is periodic: it lies on a limit cycle. -/
theorem exists_period [Finite X] (U : X → X) {B : Set X}
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
theorem iterate_mem_omegaLimit [Finite X] (U : X → X) {B : Set X} (hB : ∀ s ∈ B, U s ∈ B)
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

theorem majWorld_apply (s : Mem (Fin 3) Bool) : majWorld s = fun _ => majBit s := rfl

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
    simp only [Fix, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_forall, majWorld]
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
components of the transition graph. -/
def orbitRel (U : Mem ι V → Mem ι V) : Mem ι V → Mem ι V → Prop :=
  Relation.EqvGen fun s t => t = U s

/-- The setoid of `orbitRel`. `Quotient (orbitSetoid U)` is the set of **components**, and its
cardinality is the static-lens capacity ([Persistence] §4, L2). -/
def orbitSetoid (U : Mem ι V → Mem ι V) : Setoid (Mem ι V) :=
  Relation.EqvGen.setoid fun s t => t = U s

/-- One step relates a state to its successor. -/
theorem orbitRel_step (U : Mem ι V → Mem ι V) (s : Mem ι V) : orbitRel U s (U s) :=
  Relation.EqvGen.rel _ _ rfl

/-- Every state is related to all of its iterates: the orbit lies in one component. -/
theorem orbitRel_iterate (U : Mem ι V → Mem ι V) (s : Mem ι V) (k : ℕ) :
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
    haveI : Fintype V := Fintype.ofFinite V
    haveI : Fintype ↥(Fix U) := Fintype.ofFinite _
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

/-! ### The budgeted capacity ([Persistence] §5)

The ceiling of Proposition 3.5 prices the decoder at zero. An observer, however, must STORE the
decoder it runs, and the complexity of a frame is the complexity of its table on the core — the part
of the frame the persistence identity constrains (`ledger_K` fixes exactly this reading of `K (ℓ)`).

`Cb U eC b` is the largest model carried by a family whose EVERY frame costs at most `b` bits: the
budgeted persistence capacity, in cardinality (not logarithmic) form. It is monotone in the budget,
capped by the recurrent core at every budget, and it reaches the static levels of §4 at some finite
budget — the sandwich `static ≤ C_b ≤ |core|`. That the top of the sandwich is generically
unreachable is the collapse of §7 below. -/

section Budget

variable {ι V : Type*} [Finite ι] [Finite V]

/-- The frame's **table on the core**, along a chosen enumeration `eC` of the core: the model index
each core state is read as. This is the finite object the budget prices, and it is the same
tabulation the ledger's complexity form uses (`frameTable`). -/
def coreTable {n m : ℕ} (U : Mem ι V → Mem ι V) (eC : ↥(core U) ≃ Fin n) (f : Mem ι V → Fin m) :
    List ℕ :=
  (List.finRange n).map fun i => ((f ((eC.symm i : ↥(core U)) : Mem ι V) : Fin m) : ℕ)

/-- The family is **affordable at budget `b`**: every frame's core table has complexity at most `b`.
The budget is per-frame (a uniform variant — one program computing `t ↦ ℓ t` — costs each frame an
extra `O (log t)`). -/
def Budgeted {n m : ℕ} (U : Mem ι V → Mem ι V) (eC : ↥(core U) ≃ Fin n) (ℓ : Lens (Mem ι V) (Fin m))
    (b : ℕ) : Prop :=
  ∀ t, KE (Encodable.encode (coreTable U eC (ℓ t))) ≤ b

/-- The model sizes carried by SOME budget-`b` family. -/
def BudgetedSizes {n : ℕ} (U : Mem ι V → Mem ι V) (eC : ↥(core U) ≃ Fin n) (b : ℕ) : Set ℕ :=
  {m : ℕ | ∃ ℓ : Lens (Mem ι V) (Fin m), Carries U ℓ ∧ Budgeted U eC ℓ b}

/-- **The budgeted persistence capacity** ([Persistence] §5, Definition 5.1), in cardinality form:
the largest model carried by a lens family every frame of which costs at most `b` bits. The
unbudgeted limit is the ceiling of Proposition 3.5; the content of the theory is what happens
strictly below it. -/
noncomputable def Cb {n : ℕ} (U : Mem ι V → Mem ι V) (eC : ↥(core U) ≃ Fin n) (b : ℕ) : ℕ :=
  sSup (BudgetedSizes U eC b)

/-- Nothing carried at any budget exceeds the core (Proposition 3.5 applied to the underlying
unbudgeted family). -/
theorem budgetedSizes_le {n : ℕ} {U : Mem ι V → Mem ι V} {eC : ↥(core U) ≃ Fin n} {b m : ℕ}
    (hm : m ∈ BudgetedSizes U eC b) : m ≤ Nat.card ↥(core U) := by
  obtain ⟨ℓ, hcar, -⟩ := hm
  simpa using capacity_core hcar

theorem bddAbove_budgetedSizes {n : ℕ} (U : Mem ι V → Mem ι V) (eC : ↥(core U) ≃ Fin n) (b : ℕ) :
    BddAbove (BudgetedSizes U eC b) :=
  ⟨Nat.card ↥(core U), fun _ hm => budgetedSizes_le hm⟩

/-- **The upper half of the sandwich** ([Persistence] §5, Proposition 5.2): no budget buys more than
the recurrent core. -/
theorem Cb_le_core {n : ℕ} (U : Mem ι V → Mem ι V) (eC : ↥(core U) ≃ Fin n) (b : ℕ) :
    Cb U eC b ≤ Nat.card ↥(core U) := by
  rcases Set.eq_empty_or_nonempty (BudgetedSizes U eC b) with hemp | hne
  · simp [Cb, hemp]
  · exact csSup_le hne fun _ hm => budgetedSizes_le hm

/-- More budget never hurts: `Cb` is monotone. -/
theorem Cb_mono {n : ℕ} (U : Mem ι V → Mem ι V) (eC : ↥(core U) ≃ Fin n) {b₁ b₂ : ℕ}
    (h : b₁ ≤ b₂) : Cb U eC b₁ ≤ Cb U eC b₂ :=
  csSup_le_csSup' (bddAbove_budgetedSizes U eC b₂) (by
    rintro m ⟨ℓ, hcar, hbud⟩
    exact ⟨ℓ, hcar, fun t => (hbud t).trans h⟩)

/-- **The lower half of the sandwich, in finite-budget form** ([Persistence] §5, Proposition 5.2). A
static lens is a CONSTANT family, so all its frames have the one complexity its table has — whatever
that is — and every budget from there up carries it. (The paper's explicit threshold `c₀ + log₂ n`
prices that one table; the finite-budget form is what the capacity object needs.) -/
theorem Cb_ge_of_static {n m : ℕ} (U : Mem ι V → Mem ι V) (eC : ↥(core U) ≃ Fin n)
    {f : Mem ι V → Fin m} (hst : ∀ s, f (U s) = f s) (hsurj : Function.Surjective f) :
    ∃ b, m ≤ Cb U eC b := by
  have hiter : ∀ t s, f (U^[t] s) = f s := by
    intro t
    induction t with
    | zero => intro s; rfl
    | succ t ih => intro s; rw [Function.iterate_succ_apply', hst, ih]
  exact ⟨KE (Encodable.encode (coreTable U eC f)),
    le_csSup (bddAbove_budgetedSizes U eC _) ⟨fun _ => f, ⟨hsurj, fun t s => hiter t s⟩,
      fun _ => le_refl _⟩⟩

/-- The whole static stratum of [Persistence] §4 is affordable at some finite budget: the quotient
map onto the components is a static lens (`components_carries`). -/
theorem Cb_ge_components {n : ℕ} (U : Mem ι V → Mem ι V) (eC : ↥(core U) ≃ Fin n) :
    ∃ b, Nat.card (Quotient (orbitSetoid U)) ≤ Cb U eC b := by
  have e := Finite.equivFin (Quotient (orbitSetoid U))
  refine Cb_ge_of_static U eC (f := fun s => e (Quotient.mk (orbitSetoid U) s)) ?_ ?_
  · intro s
    rw [(components_carries U).1 s]
  · exact e.surjective.comp Quotient.mk_surjective

/-- The read-only capacity of [Decoupling] §3 (Corollary 3.3) is affordable at some finite budget —
the L1 stratum through the L2 one (`fix_le_components`). -/
theorem Cb_ge_fix {n : ℕ} (U : Mem ι V → Mem ι V) (eC : ↥(core U) ≃ Fin n) :
    ∃ b, Nat.card V ^ Nat.card ↥(Fix U) ≤ Cb U eC b := by
  obtain ⟨b, hb⟩ := Cb_ge_components U eC
  exact ⟨b, le_trans (fix_le_components U) hb⟩

/-- **The sandwich** ([Persistence] §5, Proposition 5.2): past some finite budget the capacity is
pinned between the static levels of §4 and the recurrent core. Which end it sits at is the question
of §7 — and generically it is the bottom. -/
theorem capacity_sandwich {n : ℕ} (U : Mem ι V → Mem ι V) (eC : ↥(core U) ≃ Fin n) :
    ∃ b₀, ∀ b ≥ b₀, Nat.card (Quotient (orbitSetoid U)) ≤ Cb U eC b ∧
      Cb U eC b ≤ Nat.card ↥(core U) := by
  obtain ⟨b₀, hb₀⟩ := Cb_ge_components U eC
  exact ⟨b₀, fun b hb => ⟨hb₀.trans (Cb_mono U eC hb), Cb_le_core U eC b⟩⟩

end Budget

/-! ### The collapse: counting decoders over the symmetric group ([Persistence] §7)

The ledger says a maximal moving decoder CONTAINS the world's recurrent rule. This section shows the
price is generically unpayable, by counting.

The setting is the one the counting needs, and the one [Persistence] §7 states: the world IS its own
recurrent core — a permutation `U` of `Fin n` — and the model is `Fin m`. There the ledger is
immediate and needs no maximality: persistence at `t = 1` reads `ℓ 1 (U x) = ℓ 0 x`, and `U` is
invertible, so `ℓ 1 = ℓ 0 ∘ U⁻¹` (`permCarries_frame_one`) — the second frame is DETERMINED by the
first frame and the world. (In the cell-structured setting of the rest of this file that is
`lens_bijOn_core` and `ledger`, where invertibility must first be recovered on the core.)

Counting then does the rest. Permutations act on lenses by `U • ℓ = ℓ ∘ U⁻¹`; the stabilizer of `ℓ₀`
is the product of the symmetric groups of its fibers (`card_stabilizer_lens`), so the lenses
reachable from `ℓ₀` — exactly those with `ℓ₀`'s fiber sizes (`mem_orbit_lens_iff`) — number
`n ! / ∏ᵢ (fiberᵢ) !`, and the balanced case is `n ! / ((n / m) !) ^ m` (`card_balancedLenses`). A
budget of `b` bits describes at most `2 ^ (b + 1)` tables (`card_KE_le`), each pulled back to one
coset of the stabilizer, so at most `2 ^ (b + 1) · ∏ᵢ (fiberᵢ) !` permutations admit an affordable
second frame (`collapse_count`). Dividing: all but a `2 ^ (b + 1) / N_bal` fraction of worlds admit
NO budget-`b` family carrying the model at all (`collapse`, `collapse_generic`).

Carrying even one persistent bit by a moving decoder, in a generic world, costs more description
than the world itself holds. -/

section Collapse

open MulAction Equiv Nat AdditiveComplexity

-- Throughout, `•` on lenses is the relabelling action `U • ℓ = ℓ ∘ U⁻¹`. Every statement below is
-- written at a symbolic label count `m`, where that is the only reading: Mathlib's pointwise `Pi`
-- action needs the codomain to be acted on, and `Perm (Fin n)` does not act on `Fin m`. Beware the
-- degenerate case — at `m = n` the pointwise action `(U • ℓ) x = U (ℓ x)` also typechecks and,
-- being a direct instance, WINS over this one (reached through `MulAction.toSMul`). Raising this
-- attribute's priority does not change that. So faithful (`m = n`) frames are stated below as
-- `⇑(U ^ t)⁻¹` outright rather than as `(U ^ t) • id`: the two are definitionally equal, and only
-- the former means the same thing after elaboration.
attribute [local instance] arrowAction

variable {n m : ℕ}

/-- Permutations act on lenses by relabelling the domain: `U • ℓ` reads the cell `U⁻¹ x` where `ℓ`
read `x`. This is the action under which the canonical family of Proposition 3.5 moves its
frames. -/
theorem smul_lens_apply {α : Type*} (U : Perm α) (ℓ : α → Fin m) (x : α) :
    (U • ℓ) x = ℓ (U⁻¹ x) := rfl

/-- A permutation stabilizes a lens exactly when it preserves the lens's fibers. -/
theorem mem_stabilizer_lens {α : Type*} {U : Perm α} {ℓ : α → Fin m} :
    U ∈ stabilizer (Perm α) ℓ ↔ ∀ x, ℓ (U x) = ℓ x := by
  constructor
  · intro h x
    have := congrFun (mem_stabilizer_iff.mp h) (U x)
    rw [smul_lens_apply] at this
    simpa using this.symm
  · intro h
    refine mem_stabilizer_iff.mpr (funext fun x => ?_)
    rw [smul_lens_apply]
    have := h (U⁻¹ x)
    simpa using this.symm

/-- **The stabilizer of a lens is the product of the symmetric groups of its fibers**
([Persistence] §7, Lemma 7.1). A fiber-preserving permutation is exactly a choice of one permutation
per fiber: forward, restrict; backward, assemble along the fibration of `Fin n` by `ℓ`. -/
noncomputable def stabEquivPi {α : Type*} (ℓ : α → Fin m) :
    ↥(stabilizer (Perm α) ℓ) ≃ ∀ i : Fin m, Perm {x : α // ℓ x = i} where
  toFun U := fun i => Equiv.Perm.subtypePerm U.1 (fun x => by
    rw [mem_stabilizer_lens.mp U.2 x])
  invFun τ := ⟨(Equiv.permCongr (Equiv.sigmaFiberEquiv ℓ)) (Equiv.sigmaCongrRight τ),
    mem_stabilizer_lens.mpr fun x => (τ (ℓ x) ⟨x, rfl⟩).2⟩
  left_inv U := by
    ext x
    rfl
  right_inv τ := by
    funext i
    ext y
    obtain ⟨y, rfl⟩ := y
    rfl

/-- The fibers, as the paper writes them: `{x // ℓ x = i}` is the preimage `ℓ ⁻¹' {i}`. -/
theorem card_fiber_eq {α : Type*} (ℓ : α → Fin m) (i : Fin m) :
    Nat.card {x : α // ℓ x = i} = (ℓ ⁻¹' {i}).ncard :=
  Nat.card_coe_set_eq (ℓ ⁻¹' {i})

/-- **Fiber uniformity, in cardinality form** ([Persistence] §7, Lemma 7.1): the permutations fixing
a lens number `∏ᵢ (fiberᵢ) !`. -/
theorem card_stabilizer_lens {α : Type*} [Finite α] (ℓ : α → Fin m) :
    Nat.card ↥(stabilizer (Perm α) ℓ) = ∏ i : Fin m, (Nat.card {x : α // ℓ x = i})! := by
  rw [Nat.card_congr (stabEquivPi ℓ), Nat.card_pi]
  exact Finset.prod_congr rfl fun i _ => Nat.card_perm

/-- **The orbit of a lens is the set of lenses with its fiber sizes** ([Persistence] §7, Lemma 7.1,
the surjectivity half). Precomposing with a permutation cannot change how many states a value is
read from; conversely, any lens with the same fiber sizes is reached by matching the fibers up. -/
theorem mem_orbit_lens_iff {α : Type*} [Finite α] (ℓ₀ ℓ : α → Fin m) :
    ℓ ∈ orbit (Perm α) ℓ₀ ↔
      ∀ i, Nat.card {x : α // ℓ x = i} = Nat.card {x : α // ℓ₀ x = i} := by
  classical
  haveI : Fintype α := Fintype.ofFinite _
  constructor
  · rintro ⟨U, rfl⟩ i
    have hequiv : {x : α // ℓ₀ x = i} ≃ {x : α // (U • ℓ₀) x = i} :=
      Equiv.subtypeEquiv U fun x => by
        change ℓ₀ x = i ↔ ℓ₀ (U⁻¹ (U x)) = i
        simp
    exact (Nat.card_congr hequiv).symm
  · intro h
    have e : ∀ i, {x : α // ℓ x = i} ≃ {x : α // ℓ₀ x = i} := fun i =>
      (Fintype.card_eq.mp (by
        rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]; exact h i)).some
    set τ : Perm α :=
      (Equiv.sigmaFiberEquiv ℓ).symm.trans
        ((Equiv.sigmaCongrRight e).trans (Equiv.sigmaFiberEquiv ℓ₀)) with hτ
    have hτ_apply : ∀ x, ℓ₀ (τ x) = ℓ x := fun x => (e (ℓ x) ⟨x, rfl⟩).2
    refine MulAction.mem_orbit_iff.mpr ⟨τ⁻¹, funext fun x => ?_⟩
    rw [smul_lens_apply, inv_inv, hτ_apply]

/-- **Orbit–stabilizer for lenses, over any finite domain** ([Persistence] §2, Definition 2.2;
§7, Lemma 7.2): a lens's relabelling class on a finite set `S` numbers `|S| ! / ∏ᵢ (fiberᵢ) !` —
stated multiplicatively, which is what the counting consumes.

This is Definition 2.2's carried entropy `E_S (ℓ)` in cardinality form, at the generality the
definition is stated: an arbitrary finite `S`, not merely the whole world.
`card_orbit_mul_prod_fiber` below is the case `S = Fin n` that §7's counting uses; the recurrent
core — the `S` that Definition 2.2 actually prices a persistent family on — is `α = ↥(core U)`. -/
theorem card_orbit_mul_prod_fiber_card {α : Type*} [Finite α] (ℓ : α → Fin m) :
    Nat.card ↥(orbit (Perm α) ℓ) * ∏ i : Fin m, (Nat.card {x : α // ℓ x = i})!
      = (Nat.card α)! := by
  classical
  haveI : Fintype α := Fintype.ofFinite _
  haveI : Fintype ↥(orbit (Perm α) ℓ) := Fintype.ofFinite _
  haveI : Fintype ↥(stabilizer (Perm α) ℓ) := Fintype.ofFinite _
  have h := MulAction.card_orbit_mul_card_stabilizer_eq_card_group (Perm α) ℓ
  rw [← card_stabilizer_lens ℓ, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, h,
    Fintype.card_perm, Nat.card_eq_fintype_card]

/-- **Orbit–stabilizer for lenses** ([Persistence] §7, Lemma 7.2): the lenses with `ℓ`'s fiber sizes
number `n ! / ∏ᵢ (fiberᵢ) !` — stated multiplicatively, which is what the counting consumes. -/
theorem card_orbit_mul_prod_fiber (ℓ : Fin n → Fin m) :
    Nat.card ↥(orbit (Perm (Fin n)) ℓ) * ∏ i : Fin m, (Nat.card {x : Fin n // ℓ x = i})!
      = n ! := by
  simpa using card_orbit_mul_prod_fiber_card ℓ

/-- A lens is **balanced** when every value is read from the same number `n / m` of states — the
extremal case of [Persistence] §7, and the one maximality forces up to the core's cycle
structure. -/
def Balanced (ℓ : Fin n → Fin m) : Prop := ∀ i, Nat.card {x : Fin n // ℓ x = i} = n / m

/-- Balanced lenses exist whenever the model size divides the core size: read the state's index
modulo `m`, whose fibers are the `m` arithmetic progressions of step `m`. -/
theorem exists_balanced (hm : 0 < m) (hdvd : m ∣ n) : ∃ ℓ : Fin n → Fin m, Balanced ℓ := by
  have hmul : n / m * m = n := Nat.div_mul_cancel hdvd
  refine ⟨fun x => ⟨(x : ℕ) % m, Nat.mod_lt _ hm⟩, fun i => ?_⟩
  have hbound : ∀ j : Fin (n / m), (j : ℕ) * m + (i : ℕ) < n := by
    intro j
    have h1 : (j : ℕ) * m + m ≤ n / m * m := by
      calc (j : ℕ) * m + m = ((j : ℕ) + 1) * m := by ring
        _ ≤ n / m * m := Nat.mul_le_mul_right m j.2
    have h2 : (i : ℕ) < m := i.2
    omega
  have e : {x : Fin n // (⟨(x : ℕ) % m, Nat.mod_lt _ hm⟩ : Fin m) = i} ≃ Fin (n / m) :=
    { toFun := fun x => ⟨x.val.val / m, Nat.div_lt_div_of_lt_of_dvd hdvd x.val.isLt⟩
      invFun := fun j => ⟨⟨(j : ℕ) * m + (i : ℕ), hbound j⟩, by
        apply Fin.ext
        simp [Nat.mod_eq_of_lt i.2]⟩
      left_inv := fun x => by
        have hx : x.val.val % m = (i : ℕ) := congrArg Fin.val x.property
        apply Subtype.ext
        apply Fin.ext
        simpa [hx] using Nat.div_add_mod' x.val.val m
      right_inv := fun j => by
        apply Fin.ext
        change ((j : ℕ) * m + (i : ℕ)) / m = (j : ℕ)
        rw [Nat.add_comm, Nat.add_mul_div_right _ _ hm, Nat.div_eq_of_lt i.2, Nat.zero_add] }
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_fin]

theorem prod_fiber_balanced {ℓ : Fin n → Fin m} (h : Balanced ℓ) :
    ∏ i : Fin m, (Nat.card {x : Fin n // ℓ x = i})! = ((n / m)!) ^ m := by
  rw [Finset.prod_congr rfl fun i (_ : i ∈ Finset.univ) => by rw [h i]]
  simp

/-- **The count of balanced lenses** ([Persistence] §7, Lemma 7.2): `N_bal = n ! / ((n / m) !) ^ m`,
stated multiplicatively. Its logarithm is `κ · n − Θ(2 ^ κ · log n)` for `m = 2 ^ κ` — a Stirling
estimate, and the one presentation-level step this development leaves to the paper. -/
theorem card_balancedLenses {ℓ : Fin n → Fin m} (h : Balanced ℓ) :
    Nat.card ↥(orbit (Perm (Fin n)) ℓ) * ((n / m)!) ^ m = n ! := by
  rw [← prod_fiber_balanced h]
  exact card_orbit_mul_prod_fiber ℓ

/-- The lens, tabulated along `Fin n`: the finite object whose complexity prices the frame. -/
def lensTable (ℓ : Fin n → Fin m) : List ℕ := (List.finRange n).map fun i => (ℓ i : ℕ)

/-- The encoded tabulation. `KE (lensCode ℓ)` is the frame's price, in the sense of `ledger_K`. -/
def lensCode (ℓ : Fin n → Fin m) : ℕ := Encodable.encode (lensTable ℓ)

theorem lensCode_injective : Function.Injective (lensCode (n := n) (m := m)) := by
  intro ℓ ℓ' h
  have h2 : lensTable ℓ = lensTable ℓ' := Encodable.encode_injective h
  funext x
  have hx : ((ℓ x : Fin m) : ℕ) = ((ℓ' x : Fin m) : ℕ) :=
    (List.map_inj_left.mp h2) x (List.mem_finRange x)
  exact Fin.val_injective hx

/-- **The collapse count** ([Persistence] §7, Theorem 7.3, the counting core). At most
`2 ^ (b + 1) · ∏ᵢ (fiberᵢ) !` permutations have a `b`-affordable relabelled frame.

Two facts multiply. A budget of `b` bits describes at most `2 ^ (b + 1)` tables (`card_KE_le`), and
a lens determines its permutations up to the stabilizer — the permutations sending `ℓ₀` to a GIVEN
lens form one coset, of size `∏ᵢ (fiberᵢ) !` (`card_stabilizer_lens`). Affordable frames are
therefore few, and the permutations that admit one are few times the coset size. -/
theorem collapse_count (ℓ₀ : Fin n → Fin m) (b : ℕ) :
    {U : Perm (Fin n) | KE (lensCode (U • ℓ₀)) ≤ b}.ncard
      ≤ 2 ^ (b + 1) * ∏ i : Fin m, (Nat.card {x : Fin n // ℓ₀ x = i})! := by
  classical
  set f : Perm (Fin n) → ℕ := fun U => lensCode (U • ℓ₀) with hf
  set S : Finset (Perm (Fin n)) := Finset.univ.filter fun U => KE (f U) ≤ b with hSdef
  set T : Finset ℕ := (finite_KE_le b).toFinset with hTdef
  -- each fiber of `f` over `S` injects into the stabilizer: it is (part of) one coset
  have hfib : ∀ v ∈ T, (S.filter fun U => f U = v).card
      ≤ ∏ i : Fin m, (Nat.card {x : Fin n // ℓ₀ x = i})! := by
    intro v _
    rcases Finset.eq_empty_or_nonempty (S.filter fun U => f U = v) with hemp | ⟨W, hW⟩
    · simp [hemp]
    · have hWv : f W = v := (Finset.mem_filter.mp hW).2
      haveI : Fintype ↥(stabilizer (Perm (Fin n)) ℓ₀) := Fintype.ofFinite _
      have hmaps : ∀ U ∈ S.filter fun U => f U = v,
          W⁻¹ * U ∈ (stabilizer (Perm (Fin n)) ℓ₀ : Set (Perm (Fin n))).toFinset := by
        intro U hU
        have hUv : f U = v := (Finset.mem_filter.mp hU).2
        have hlens : U • ℓ₀ = W • ℓ₀ := lensCode_injective (hUv.trans hWv.symm)
        simp only [Set.mem_toFinset, SetLike.mem_coe, mem_stabilizer_iff, mul_smul, hlens,
          inv_smul_smul]
      have hinj : Set.InjOn (fun U => W⁻¹ * U) ↑(S.filter fun U => f U = v) :=
        fun a _ c _ hac => mul_left_cancel hac
      have hcard := Finset.card_le_card_of_injOn (fun U => W⁻¹ * U) hmaps hinj
      rw [Set.toFinset_card, ← Nat.card_eq_fintype_card] at hcard
      have hstab : Nat.card ↥((stabilizer (Perm (Fin n)) ℓ₀ : Set (Perm (Fin n))))
          = ∏ i : Fin m, (Nat.card {x : Fin n // ℓ₀ x = i})! := card_stabilizer_lens ℓ₀
      exact hstab ▸ hcard
  have hmapsT : ∀ U ∈ S, f U ∈ T := by
    intro U hU
    simpa [hTdef] using (Finset.mem_filter.mp hU).2
  have hmain := Finset.card_le_mul_card_image_of_maps_to hmapsT
    (∏ i : Fin m, (Nat.card {x : Fin n // ℓ₀ x = i})!) hfib
  have hT : T.card ≤ 2 ^ (b + 1) := by
    have := card_KE_le b
    rwa [Set.ncard_eq_toFinset_card _ (finite_KE_le b)] at this
  have hSset : {U : Perm (Fin n) | KE (lensCode (U • ℓ₀)) ≤ b} = ↑S := by
    ext U; simp [hSdef, hf]
  rw [hSset, Set.ncard_coe_finset]
  calc S.card ≤ (∏ i : Fin m, (Nat.card {x : Fin n // ℓ₀ x = i})!) * T.card := hmain
    _ ≤ (∏ i : Fin m, (Nat.card {x : Fin n // ℓ₀ x = i})!) * 2 ^ (b + 1) :=
        Nat.mul_le_mul_left _ hT
    _ = 2 ^ (b + 1) * ∏ i : Fin m, (Nat.card {x : Fin n // ℓ₀ x = i})! := Nat.mul_comm _ _

/-- The collapse count as a FRACTION of the symmetric group ([Persistence] §7, Theorem 7.3): the
permutations with an affordable relabelled frame are at most a `2 ^ (b + 1) / N_bal` fraction of all
`n !` of them, where `N_bal` is the orbit — division-free, by clearing the denominator. -/
theorem collapse_fraction (ℓ₀ : Fin n → Fin m) (b : ℕ) :
    {U : Perm (Fin n) | KE (lensCode (U • ℓ₀)) ≤ b}.ncard
        * Nat.card ↥(orbit (Perm (Fin n)) ℓ₀) ≤ 2 ^ (b + 1) * n ! := by
  have h1 := collapse_count ℓ₀ b
  have h2 := card_orbit_mul_prod_fiber ℓ₀
  calc {U : Perm (Fin n) | KE (lensCode (U • ℓ₀)) ≤ b}.ncard
        * Nat.card ↥(orbit (Perm (Fin n)) ℓ₀)
      ≤ (2 ^ (b + 1) * ∏ i : Fin m, (Nat.card {x : Fin n // ℓ₀ x = i})!)
        * Nat.card ↥(orbit (Perm (Fin n)) ℓ₀) := Nat.mul_le_mul_right _ h1
    _ = 2 ^ (b + 1) * (Nat.card ↥(orbit (Perm (Fin n)) ℓ₀)
        * ∏ i : Fin m, (Nat.card {x : Fin n // ℓ₀ x = i})!) := by ring
    _ = 2 ^ (b + 1) * n ! := by rw [h2]

/-- A lens family over a **permutation world** ([Persistence] §7): the world is its own recurrent
core, so `U^t` is a genuine power and the persistence identity is `ℓ t ∘ U ^ t = ℓ 0`. -/
def PermCarries (U : Perm (Fin n)) (ℓ : ℕ → Fin n → Fin m) : Prop :=
  Function.Surjective (ℓ 0) ∧ ∀ t x, ℓ t ((U ^ t) x) = ℓ 0 x

/-- Every frame of the family is affordable at budget `b` ([Persistence] §5, per-frame budget). -/
def PermBudget (ℓ : ℕ → Fin n → Fin m) (b : ℕ) : Prop := ∀ t, KE (lensCode (ℓ t)) ≤ b

/-- **The ledger over a permutation world** ([Persistence] §6, Theorem 6.1, in the §7 setting): the
second frame is DETERMINED by the first frame and the world, `ℓ 1 = ℓ 0 ∘ U⁻¹`. No maximality is
needed here — the world is already invertible — which is why the counting can price `ℓ 1` for every
family at once. (In the cell-structured setting this is `lens_bijOn_core` and `ledger`.) -/
theorem permCarries_frame_one {U : Perm (Fin n)} {ℓ : ℕ → Fin n → Fin m}
    (h : PermCarries U ℓ) : ℓ 1 = U • ℓ 0 := by
  funext x
  rw [smul_lens_apply]
  have := h.2 1 (U⁻¹ x)
  simpa using this

/-- **The Collapse Theorem** ([Persistence] §7, Theorem 7.3). For a fixed reference frame `ℓ₀`, the
worlds admitting ANY budget-`b` family that carries the model through `ℓ₀` number at most
`2 ^ (b + 1) · ∏ᵢ (fiberᵢ) !`.

The proof is the ledger plus the count: the family's second frame must be `ℓ₀ ∘ U⁻¹`
(`permCarries_frame_one`), so a world with an affordable family is a world with an affordable
relabelled frame — and those were counted (`collapse_count`). The budget hypothesis is used at
`t = 1` only, so the theorem is if anything stronger than the paper's per-frame form. -/
theorem collapse (ℓ₀ : Fin n → Fin m) (b : ℕ) :
    {U : Perm (Fin n) | ∃ ℓ : ℕ → Fin n → Fin m,
        PermCarries U ℓ ∧ ℓ 0 = ℓ₀ ∧ PermBudget ℓ b}.ncard
      ≤ 2 ^ (b + 1) * ∏ i : Fin m, (Nat.card {x : Fin n // ℓ₀ x = i})! := by
  refine le_trans (Set.ncard_le_ncard ?_ (Set.toFinite _)) (collapse_count ℓ₀ b)
  rintro U ⟨ℓ, hcar, h0, hbud⟩
  have h1 : ℓ 1 = U • ℓ₀ := by rw [permCarries_frame_one hcar, h0]
  have hb := hbud 1
  rwa [h1] at hb

/-- **The Collapse Theorem, balanced case** ([Persistence] §7, Theorem 7.3): with `m = 2 ^ κ` values
each read from `n / m` states, at most `2 ^ (b + 1) · ((n / m) !) ^ m` worlds are affordable. Since
`N_bal = n ! / ((n / m) !) ^ m` has `log₂ N_bal = κ · n − Θ(2 ^ κ log n)`, a budget below that
leaves all but a vanishing fraction of worlds with NO affordable moving decoder. -/
theorem collapse_balanced {ℓ₀ : Fin n → Fin m} (hbal : Balanced ℓ₀) (b : ℕ) :
    {U : Perm (Fin n) | ∃ ℓ : ℕ → Fin n → Fin m,
        PermCarries U ℓ ∧ ℓ 0 = ℓ₀ ∧ PermBudget ℓ b}.ncard
      ≤ 2 ^ (b + 1) * ((n / m)!) ^ m := by
  rw [← prod_fiber_balanced hbal]
  exact collapse ℓ₀ b

/-- **The collapse, as a fraction of all worlds** ([Persistence] §7, Theorem 7.3): the worlds
carrying the model under some budget-`b` family are at most a `2 ^ (b + 1) / N_bal` fraction of the
`n !` permutations of the core. For a budget below `log₂ N_bal − d` the fraction is below
`2 ^ (−d)`: **generic worlds admit no affordable moving decoder at all.** -/
theorem collapse_generic (ℓ₀ : Fin n → Fin m) (b : ℕ) :
    {U : Perm (Fin n) | ∃ ℓ : ℕ → Fin n → Fin m,
        PermCarries U ℓ ∧ ℓ 0 = ℓ₀ ∧ PermBudget ℓ b}.ncard
        * Nat.card ↥(orbit (Perm (Fin n)) ℓ₀) ≤ 2 ^ (b + 1) * n ! := by
  refine le_trans (Nat.mul_le_mul_right _ (Set.ncard_le_ncard ?_ (Set.toFinite _)))
    (collapse_fraction ℓ₀ b)
  rintro U ⟨ℓ, hcar, h0, hbud⟩
  have h1 : ℓ 1 = U • ℓ₀ := by rw [permCarries_frame_one hcar, h0]
  have hb := hbud 1
  rwa [h1] at hb

/-- The value list of a **surjective** lens recovers its codomain: the labels are exactly
`{0, …, m − 1}`, so `(lensTable ℓ).toFinset = Finset.range m`. This is the joint prefix-freeness
Corollary 7.4's union over lenses of *different* label counts needs: `lensCode` is injective across
codomains once restricted to surjective lenses, even though `lensTable` stores only the values, not
`m`. -/
theorem toFinset_lensTable_of_surjective {ℓ : Fin n → Fin m} (hs : Function.Surjective ℓ) :
    (lensTable ℓ).toFinset = Finset.range m := by
  ext v
  simp only [List.mem_toFinset, lensTable, List.mem_map, List.mem_finRange, true_and,
    Finset.mem_range]
  constructor
  · rintro ⟨i, rfl⟩; exact (ℓ i).isLt
  · intro hv; obtain ⟨i, hi⟩ := hs ⟨v, hv⟩; exact ⟨i, by rw [hi]⟩

/-- **`lensCode` is injective on surjective lenses, across codomains** ([Persistence] §7, the joint
prefix-freeness Corollary 7.4's Kraft union requires). Two surjective lenses with the same code have
the same label count: their value lists agree, so their value *sets* `Finset.range m` agree, forcing
`m = m'`. (For fixed `m`, `lensCode_injective` then recovers the lens itself.) No change to
`lensCode` is needed — surjectivity alone recovers the codomain size the encoding does not store. -/
theorem lensCode_codomain_of_surjective {m m' : ℕ} {ℓ : Fin n → Fin m} {ℓ' : Fin n → Fin m'}
    (hs : Function.Surjective ℓ) (hs' : Function.Surjective ℓ') (h : lensCode ℓ = lensCode ℓ') :
    m = m' := by
  have ht : lensTable ℓ = lensTable ℓ' := Encodable.encode_injective h
  have hrange : Finset.range m = Finset.range m' := by
    rw [← toFinset_lensTable_of_surjective hs, ← toFinset_lensTable_of_surjective hs', ht]
  have := congrArg Finset.card hrange
  rwa [Finset.card_range, Finset.card_range] at this

/-- **The per-frame collapse budget, division-free** ([Persistence] §7, Corollary 7.4, the per-lens
ingredient). Fix a reference frame `ℓ₀`; write `N := Nat.card (orbit ℓ₀)` for its relabelling-class
size, so the carried entropy is `log₂ N` (`card_orbit_mul_prod_fiber`). Worlds whose determined
second frame `U • ℓ₀` is so cheap that the two-frame description `KE ℓ₀ + KE (U • ℓ₀)` still falls
`d + 2` below the entropy number `N` are few: their count times `2 ^ (KE ℓ₀ + d + 1)` is at most
`n !`. Multiplicative, so the orbit cardinality cancels against `collapse_fraction` with no division
— the per-lens count Corollary 7.4's Kraft union sums. Threshold `Nat.log 2 N ∸ (KE ℓ₀ + d + 2)`;
below the entropy the bad set is empty (the degenerate branch). -/
theorem collapse_union_frame (ℓ₀ : Fin n → Fin m) (d : ℕ) :
    {U : Perm (Fin n) | 2 ^ (KE (lensCode ℓ₀) + KE (lensCode (U • ℓ₀)) + d + 2)
        < Nat.card ↥(orbit (Perm (Fin n)) ℓ₀)}.ncard * 2 ^ (KE (lensCode ℓ₀) + d + 1) ≤ n ! := by
  classical
  set A := KE (lensCode ℓ₀) with hA
  set N := Nat.card ↥(orbit (Perm (Fin n)) ℓ₀) with hN
  have hNpos : 0 < N := by
    haveI : Nonempty ↥(orbit (Perm (Fin n)) ℓ₀) := ⟨⟨ℓ₀, mem_orbit_self ℓ₀⟩⟩
    haveI : Finite ↥(orbit (Perm (Fin n)) ℓ₀) := Set.Finite.to_subtype (Set.toFinite _)
    exact hN ▸ Nat.card_pos
  set Bad := {U : Perm (Fin n) | 2 ^ (A + KE (lensCode (U • ℓ₀)) + d + 2) < N} with hBad
  rcases Set.eq_empty_or_nonempty Bad with hemp | ⟨U₀, hU₀⟩
  · simp only [hemp, Set.ncard_empty, Nat.zero_mul]; exact Nat.zero_le _
  · -- nonempty ⇒ the entropy number exceeds the base budget, so the log threshold is exact
    have hU₀' : 2 ^ (A + KE (lensCode (U₀ • ℓ₀)) + d + 2) < N := hU₀
    have hlow : 2 ^ (A + d + 2) ≤ N :=
      le_of_lt (lt_of_le_of_lt (Nat.pow_le_pow_right (by norm_num) (by omega)) hU₀')
    have hloglow : A + d + 2 ≤ Nat.log 2 N :=
      Nat.le_log_of_pow_le (by norm_num) hlow
    set b₀ := Nat.log 2 N - (A + d + 2) with hb₀
    -- every bad world's determined frame is ≤ b₀-affordable
    have hsub : Bad ⊆ {U : Perm (Fin n) | KE (lensCode (U • ℓ₀)) ≤ b₀} := by
      intro U hU
      have hUlt : 2 ^ (A + KE (lensCode (U • ℓ₀)) + d + 2) < N := hU
      have hup : 2 ^ (A + KE (lensCode (U • ℓ₀)) + d + 2) < 2 ^ (Nat.log 2 N + 1) :=
        lt_of_lt_of_le hUlt (le_of_lt (Nat.lt_pow_succ_log_self (by norm_num) N))
      have hexp : A + KE (lensCode (U • ℓ₀)) + d + 2 < Nat.log 2 N + 1 :=
        (Nat.pow_lt_pow_iff_right (by norm_num)).mp hup
      change KE (lensCode (U • ℓ₀)) ≤ b₀
      omega
    -- collapse_fraction at the threshold budget, then cancel the orbit cardinality
    have hcf := collapse_fraction ℓ₀ b₀
    have hbadN : Bad.ncard * N ≤ 2 ^ (b₀ + 1) * n ! :=
      le_trans (Nat.mul_le_mul_right _ (Set.ncard_le_ncard hsub (Set.toFinite _))) hcf
    have hkey : Bad.ncard * 2 ^ (A + d + 1) * N ≤ n ! * N := by
      calc Bad.ncard * 2 ^ (A + d + 1) * N
            = Bad.ncard * N * 2 ^ (A + d + 1) := by ring
        _ ≤ 2 ^ (b₀ + 1) * n ! * 2 ^ (A + d + 1) := Nat.mul_le_mul_right _ hbadN
        _ = 2 ^ (b₀ + 1 + (A + d + 1)) * n ! := by rw [pow_add]; ring
        _ = 2 ^ (Nat.log 2 N) * n ! := by rw [show b₀ + 1 + (A + d + 1) = Nat.log 2 N by omega]
        _ ≤ N * n ! := Nat.mul_le_mul_right _ (Nat.pow_log_le_self 2 hNpos.ne')
        _ = n ! * N := by ring
    exact Nat.le_of_mul_le_mul_right hkey hNpos

/-- **The Kraft union collapse** ([Persistence] §7, Corollary 7.4, logs cleared). Summing the
per-frame count `collapse_union_frame` over *all* reference frames at once: for every `d`, the
permutation worlds admitting a surjective reference frame `ℓ₀` whose two-frame description
`KE ℓ₀ + KE (ℓ₀ ∘ U⁻¹)` still falls `d + 2` below its carried entropy `log₂ (Nat.card (orbit ℓ₀))`
number at most `n ! / 2 ^ d` — a `2 ^ (-d)` fraction, uniformly over the reference frame.
Generically there are **no discounts**: an observer's two-frame budget must cover the entropy it
carries.

The union ranges over lenses of *different* label counts `Fin m`; it is sound because `lensCode` is
jointly injective on surjective lenses (`lensCode_codomain_of_surjective`), so the Kraft inequality
`kraft_sum_le_one` bounds `∑ 2 ^ (-KE ℓ₀) ≤ 1` over the whole family. Surjectivity forces `m ≤ n`,
so the family is finite. -/
theorem collapse_union (d : ℕ) :
    {U : Perm (Fin n) | ∃ m, ∃ ℓ₀ : Fin n → Fin m, Function.Surjective ℓ₀ ∧
        2 ^ (KE (lensCode ℓ₀) + KE (lensCode (ℓ₀ ∘ ⇑U⁻¹)) + d + 2)
          < Nat.card ↥(orbit (Perm (Fin n)) ℓ₀)}.ncard * 2 ^ d ≤ n ! := by
  classical
  -- surjective lenses with codomain ≤ n — a finite index for the union
  let SL := Σ k : Fin (n + 1), {ℓ : Fin n → Fin (k : ℕ) // Function.Surjective ℓ}
  let frameSet : SL → Set (Perm (Fin n)) := fun s =>
    {U | 2 ^ (KE (lensCode s.2.1) + KE (lensCode (U • s.2.1)) + d + 2)
        < Nat.card ↥(orbit (Perm (Fin n)) s.2.1)}
  set B := {U : Perm (Fin n) | ∃ m, ∃ ℓ₀ : Fin n → Fin m, Function.Surjective ℓ₀ ∧
      2 ^ (KE (lensCode ℓ₀) + KE (lensCode (ℓ₀ ∘ ⇑U⁻¹)) + d + 2)
        < Nat.card ↥(orbit (Perm (Fin n)) ℓ₀)} with hBdef
  -- (1) every bad world is caught by some per-frame bad set
  have hcover : B ⊆ ⋃ s : SL, frameSet s := by
    intro U hU
    obtain ⟨m, ℓ₀, hsurj, hlt⟩ := hU
    have hmn : m < n + 1 := by
      have h := Fintype.card_le_of_surjective ℓ₀ hsurj
      simp only [Fintype.card_fin] at h; omega
    refine Set.mem_iUnion.mpr ⟨⟨⟨m, hmn⟩, ⟨ℓ₀, hsurj⟩⟩, ?_⟩
    change 2 ^ (KE (lensCode ℓ₀) + KE (lensCode (U • ℓ₀)) + d + 2)
        < Nat.card ↥(orbit (Perm (Fin n)) ℓ₀)
    rwa [show U • ℓ₀ = ℓ₀ ∘ ⇑U⁻¹ from rfl]
  -- (2) union bound: the count is at most the sum of the per-frame counts
  have hUB : B.ncard ≤ ∑ s : SL, (frameSet s).ncard :=
    le_trans (Set.ncard_le_ncard hcover (Set.toFinite _)) (Set.ncard_iUnion_le_of_fintype _)
  -- (3) Kraft over the lens family: ∑ 2^(-KE) ≤ 1
  have minCode_inj : Function.Injective minCode :=
    fun a b h => minCode_E_injective (congrArg E h)
  have hφinj : Function.Injective (fun s : SL => minCode (lensCode s.2.1)) := by
    rintro ⟨k, ℓ, hℓ⟩ ⟨k', ℓ', hℓ'⟩ h
    have hcode : lensCode ℓ = lensCode ℓ' := minCode_inj h
    obtain rfl : k = k' := Fin.ext (lensCode_codomain_of_surjective hℓ hℓ' hcode)
    obtain rfl : ℓ = ℓ' := lensCode_injective hcode
    rfl
  have hkraft : ∑ s : SL, (1 / 2 : ℝ) ^ KE (lensCode s.2.1) ≤ 1 := by
    have hrw : ∀ s : SL, (1 / 2 : ℝ) ^ KE (lensCode s.2.1)
        = (1 / 2 : ℝ) ^ elen (minCode (lensCode s.2.1)) := fun s => by rw [elen_minCode]
    calc ∑ s : SL, (1 / 2 : ℝ) ^ KE (lensCode s.2.1)
          = ∑ s : SL, (1 / 2 : ℝ) ^ elen (minCode (lensCode s.2.1)) := by
            exact Finset.sum_congr rfl fun s _ => hrw s
      _ = ∑ c ∈ (Finset.univ.image fun s : SL => minCode (lensCode s.2.1)),
            (1 / 2 : ℝ) ^ elen c := by
            rw [Finset.sum_image fun x _ y _ h => hφinj h]
      _ ≤ 1 := kraft_sum_le_one _
  -- (4) assemble in ℝ: per-frame bound + Kraft, then clear to ℕ
  have hterm : ∀ s : SL, ((frameSet s).ncard : ℝ)
      ≤ (n ! : ℝ) * (1 / 2 : ℝ) ^ (d + 1) * (1 / 2 : ℝ) ^ KE (lensCode s.2.1) := by
    intro s
    have hnat := collapse_union_frame s.2.1 d
    have hcast : ((frameSet s).ncard : ℝ) * (2 : ℝ) ^ (KE (lensCode s.2.1) + d + 1)
        ≤ (n ! : ℝ) := by
      exact_mod_cast hnat
    rw [show (n ! : ℝ) * (1 / 2 : ℝ) ^ (d + 1) * (1 / 2 : ℝ) ^ KE (lensCode s.2.1)
          = (n ! : ℝ) / (2 : ℝ) ^ (KE (lensCode s.2.1) + d + 1) by
        rw [one_div, inv_pow, inv_pow, mul_assoc, ← mul_inv, ← pow_add, ← div_eq_mul_inv]
        congr 2
        omega]
    rw [le_div_iff₀ (by positivity)]
    exact hcast
  have hsum : ((B.ncard : ℝ)) ≤ (n ! : ℝ) * (1 / 2 : ℝ) ^ (d + 1) := by
    calc ((B.ncard : ℝ)) ≤ ∑ s : SL, ((frameSet s).ncard : ℝ) := by
            exact_mod_cast hUB
      _ ≤ ∑ s : SL, (n ! : ℝ) * (1 / 2 : ℝ) ^ (d + 1) * (1 / 2 : ℝ) ^ KE (lensCode s.2.1) :=
            Finset.sum_le_sum fun s _ => hterm s
      _ = (n ! : ℝ) * (1 / 2 : ℝ) ^ (d + 1)
            * ∑ s : SL, (1 / 2 : ℝ) ^ KE (lensCode s.2.1) := by rw [← Finset.mul_sum]
      _ ≤ (n ! : ℝ) * (1 / 2 : ℝ) ^ (d + 1) * 1 :=
            mul_le_mul_of_nonneg_left hkraft (by positivity)
      _ = (n ! : ℝ) * (1 / 2 : ℝ) ^ (d + 1) := by ring
  -- (5) multiply by 2^d and cast back to ℕ
  have hfinal : ((B.ncard : ℝ)) * (2 : ℝ) ^ d ≤ (n ! : ℝ) := by
    calc ((B.ncard : ℝ)) * (2 : ℝ) ^ d
          ≤ (n ! : ℝ) * (1 / 2 : ℝ) ^ (d + 1) * (2 : ℝ) ^ d :=
            mul_le_mul_of_nonneg_right hsum (by positivity)
      _ = (n ! : ℝ) * (1 / 2 : ℝ) := by
            have h1 : (1 / 2 : ℝ) ^ d * (2 : ℝ) ^ d = 1 := by rw [← mul_pow]; norm_num
            calc (n ! : ℝ) * (1 / 2 : ℝ) ^ (d + 1) * (2 : ℝ) ^ d
                  = (n ! : ℝ) * (1 / 2 : ℝ) * ((1 / 2 : ℝ) ^ d * (2 : ℝ) ^ d) := by
                    rw [pow_succ]; ring
              _ = (n ! : ℝ) * (1 / 2 : ℝ) := by rw [h1]; ring
      _ ≤ (n ! : ℝ) := by nlinarith [Nat.cast_nonneg (α := ℝ) (n !)]
  exact_mod_cast hfinal

/-! ### The entropic capacity ([Persistence] §5, Definition 5.4)

Definition 5.1's capacity counts *labels*, and §5 argues the label count is the wrong currency: a
handful of moving marks is affordable in every world, however complex, and distinguishes almost
nothing. The currency that survives the collapse is the **carried entropy** of the reference frame.
A frame `ℓ₀`'s relabelling class `orbit ℓ₀` has cardinality `N₀ = n ! / ∏ᵢ (fiberᵢ) !`
(`card_orbit_mul_prod_fiber`), and the entropy `E (ℓ₀)` of [Persistence] §2, Definition 2.2 is
`log₂ N₀`.

The object below is valued in `N₀` itself rather than its logarithm — as with `Cb`, the cardinality
form is the machine-checkable one and the `log₂` is applied paper-side. So `CbH U b` is the paper's
`2 ^ (C_b^H (U))`, and the cap `CbH_collapse` below — no world outside a `2 ^ (-d)` fraction has
`2 ^ (2 * b + d + 2) < CbH U b` — reads `C_b^H (U) ≤ 2 * b + d + 2`, which is Corollary 7.4's
`C_b^H (U) ≤ 2 * b + d + O (1)` with the `O (1)` pinned at `2`. Taking the supremum before the
logarithm loses nothing: `log₂` is monotone and the family of values is finite. -/

/-- The **carried entropies affordable at budget `b`**: the relabelling-class sizes
`N₀ = Nat.card (orbit ℓ₀)` of the reference frames `ℓ₀ = ℓ 0` of those families that carry a
persistent model over `U` at a per-frame cost of `b` bits. The label count is not fixed — the
maximum of [Persistence] §5, Definition 5.4 ranges over families carrying a model of any size. -/
def BudgetedEntropies (U : Perm (Fin n)) (b : ℕ) : Set ℕ :=
  {N : ℕ | ∃ k : ℕ, ∃ ℓ : ℕ → Fin n → Fin k, PermCarries U ℓ ∧ PermBudget ℓ b ∧
      N = Nat.card ↥(orbit (Perm (Fin n)) (ℓ 0))}

/-- **The entropic budgeted capacity** ([Persistence] §5, Definition 5.4) over a permutation world —
§7's setting, where the world is its own recurrent core — in cardinality form: the largest carried
entropy, as the relabelling-class size `2 ^ E` (see above), of a reference frame whose family costs
at most `b` bits per frame. `sSup ∅ = 0`: a budget that affords no family at all carries nothing. -/
noncomputable def CbH (U : Perm (Fin n)) (b : ℕ) : ℕ := sSup (BudgetedEntropies U b)

/-- No reading distinguishes more than the world has to offer: a relabelling class is a set of
lenses reachable from one another by permutations, so its size is at most `n !`
(`card_orbit_mul_prod_fiber`, the fiber product being at least one). This is what makes the
supremum well-defined. -/
theorem budgetedEntropies_le {U : Perm (Fin n)} {b N : ℕ} (h : N ∈ BudgetedEntropies U b) :
    N ≤ n ! := by
  obtain ⟨k, ℓ, -, -, rfl⟩ := h
  have hprod : 0 < ∏ i : Fin k, (Nat.card {x : Fin n // ℓ 0 x = i})! :=
    Finset.prod_pos fun i _ => Nat.factorial_pos _
  exact card_orbit_mul_prod_fiber (ℓ 0) ▸ Nat.le_mul_of_pos_right _ hprod

theorem bddAbove_budgetedEntropies (U : Perm (Fin n)) (b : ℕ) :
    BddAbove (BudgetedEntropies U b) :=
  ⟨n !, fun _ h => budgetedEntropies_le h⟩

/-- **The entropic capacity never exceeds a faithful reading** ([Persistence] §5): `log₂ n !` is the
entropy of a bijective frame, and no budget buys more. -/
theorem CbH_le_factorial (U : Perm (Fin n)) (b : ℕ) : CbH U b ≤ n ! := by
  rcases Set.eq_empty_or_nonempty (BudgetedEntropies U b) with hemp | hne
  · simp [CbH, hemp]
  · exact csSup_le hne fun _ h => budgetedEntropies_le h

/-- More budget never hurts: `CbH` is monotone (the `Cb_mono` of the entropic currency). -/
theorem CbH_mono (U : Perm (Fin n)) {b₁ b₂ : ℕ} (h : b₁ ≤ b₂) : CbH U b₁ ≤ CbH U b₂ :=
  csSup_le_csSup' (bddAbove_budgetedEntropies U b₂) (by
    rintro N ⟨k, ℓ, hcar, hbud, rfl⟩
    exact ⟨k, ℓ, hcar, fun t => (hbud t).trans h, rfl⟩)

/-- **The entropic capacity is generically pinned at `2b + d + O (1)`** ([Persistence] §7,
Corollary 7.5(i), the cap; the `O (1)` is `2`). For every `d`, the worlds whose entropic capacity at
budget `b` exceeds `2 * b + d + 2` — i.e. `2 ^ (2 * b + d + 2) < CbH U b`, the division-free reading
of `C_b^H (U) > 2 * b + d + 2` — number at most `n ! / 2 ^ d`, a `2 ^ (-d)` fraction of the worlds.

**An observer keeps, to within a factor two, exactly the entropy it pays for**: there are no
discounts, generically.

The proof is `collapse_union` plus the observation that the supremum is attained. A world with
`2 ^ (2 * b + d + 2) < CbH U b` has an actual budget-`b` family realizing that entropy
(`Nat.sSup_mem`); its reference frame is surjective, and the family's second frame is *determined*
as `ℓ₀ ∘ U⁻¹` (`permCarries_frame_one`), so the two frames cost at most `b` each — putting the world
in the Kraft union's exceptional set, which `collapse_union` has already counted. The budget
hypothesis is consumed at `t = 0` and `t = 1` only. -/
theorem CbH_collapse (b d : ℕ) :
    {U : Perm (Fin n) | 2 ^ (2 * b + d + 2) < CbH U b}.ncard * 2 ^ d ≤ n ! := by
  refine le_trans (Nat.mul_le_mul_right _ (Set.ncard_le_ncard ?_ (Set.toFinite _)))
    (collapse_union d)
  intro U hU
  have hlt : 2 ^ (2 * b + d + 2) < CbH U b := hU
  have hne : (BudgetedEntropies U b).Nonempty := by
    by_contra hcon
    rw [Set.not_nonempty_iff_eq_empty] at hcon
    rw [CbH, hcon, csSup_empty] at hlt
    exact absurd hlt (Nat.not_lt_zero _)
  obtain ⟨k, ℓ, hcar, hbud, hval⟩ : CbH U b ∈ BudgetedEntropies U b :=
    Nat.sSup_mem hne (bddAbove_budgetedEntropies U b)
  refine ⟨k, ℓ 0, hcar.1, ?_⟩
  have h1 : ℓ 1 = U • ℓ 0 := permCarries_frame_one hcar
  have hb0 := hbud 0
  have hb1 := hbud 1
  rw [h1, show U • ℓ 0 = ℓ 0 ∘ ⇑U⁻¹ from rfl] at hb1
  calc 2 ^ (KE (lensCode (ℓ 0)) + KE (lensCode (ℓ 0 ∘ ⇑U⁻¹)) + d + 2)
      ≤ 2 ^ (2 * b + d + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
    _ < Nat.card ↥(orbit (Perm (Fin n)) (ℓ 0)) := hval ▸ hlt

/-! ### The marking floor ([Persistence] §5, Proposition 5.3)

The cap above is one side of Corollary 7.5(i); this is the other. Mark `r` distinguished points of
the world, sending `x j` to the label `j + 1` and everything else to `0`, and let the marks *ride
the world*: `ℓ t := ℓ₀ ∘ (U ^ t)⁻¹`. Persistence is immediate, and the construction needs no
genericity — it runs over **every** permutation world, however complex the rule.

What the marks carry is exactly computed: the profile is `(n − r, 1, …, 1)`, so the reference
frame's relabelling class has `n ! / (n − r)!` elements (`prod_fiber_marking`) and the carried
entropy is `log₂ (n ! / (n − r)!) ≈ r · log₂ n` — a floor on `CbH` as soon as the budget affords the
family (`CbH_ge_marking`).

Proposition 5.3's own content is the *price* of that family: each frame's table is "the current
positions `U ^ t (x j)`, each with its label, else `0`", which an explicit program loads in
`O (r · log₂ n)` bits. That price is proved below (`KE_markingLens_le`), and `smul_markingLens` is
what makes one such bound suffice for the whole family: every frame of the family *is* a marking
lens, with the marks moved along, so the price is uniform in `t` by construction rather than by
estimate. The floor consuming it is `CbH_ge_marking'`. -/

/-- The **marking lens** ([Persistence] §5, Proposition 5.3): `r` distinguished points `x 0, …,
x (r−1)` are read as the labels `1, …, r`, and every other state is read as `0`. Definitionally the
cheapest nontrivial reading — it distinguishes a handful of points and nothing else. -/
noncomputable def markingLens {r : ℕ} (x : Fin r → Fin n) (i : Fin n) : Fin (r + 1) :=
  if h : ∃ j, x j = i then h.choose.succ else 0

/-- A marked point is read as its own label. -/
theorem markingLens_mark {r : ℕ} {x : Fin r → Fin n} (hx : Function.Injective x) (j : Fin r) :
    markingLens x (x j) = j.succ := by
  have h : ∃ j', x j' = x j := ⟨j, rfl⟩
  rw [markingLens, dif_pos h]
  exact congrArg Fin.succ (hx h.choose_spec)

/-- An unmarked point is read as `0`. -/
theorem markingLens_unmark {r : ℕ} {x : Fin r → Fin n} {i : Fin n} (h : ¬∃ j, x j = i) :
    markingLens x i = 0 := by
  rw [markingLens, dif_neg h]

/-- Only the marked points carry labels: reading `j + 1` identifies the state as `x j`. -/
theorem markingLens_eq_succ_iff {r : ℕ} {x : Fin r → Fin n} (hx : Function.Injective x)
    {i : Fin n} {j : Fin r} : markingLens x i = j.succ ↔ x j = i := by
  constructor
  · intro h
    by_cases hex : ∃ j', x j' = i
    · rw [markingLens, dif_pos hex] at h
      rw [← Fin.succ_injective _ h]
      exact hex.choose_spec
    · rw [markingLens_unmark hex] at h
      exact absurd h.symm (Fin.succ_ne_zero j)
  · rintro rfl
    exact markingLens_mark hx j

/-- The `0`-fiber of the marking lens is everything unmarked: `n − r` states. -/
theorem card_fiber_marking_zero {r : ℕ} {x : Fin r → Fin n} (hx : Function.Injective x) :
    Nat.card {i : Fin n // markingLens x i = 0} = n - r := by
  classical
  have hset : ∀ i : Fin n, markingLens x i = 0 ↔ i ∉ Set.range x := by
    intro i
    constructor
    · rintro h ⟨j, rfl⟩
      exact absurd ((markingLens_mark hx j).symm.trans h) (Fin.succ_ne_zero j)
    · intro h
      exact markingLens_unmark fun hex => h hex
  have hcong : {i : Fin n // markingLens x i = 0} = {i : Fin n // i ∉ Set.range x} := by
    congr 1
    ext i
    exact hset i
  rw [hcong, Nat.card_eq_fintype_card, Fintype.card_subtype_compl, ← Nat.card_eq_fintype_card,
    ← Nat.card_eq_fintype_card, Nat.card_range_of_injective hx]
  simp

/-- The marking lens is **surjective** as soon as one point is left unmarked: the marks supply the
labels `1, …, r`, and the `n − r` unmarked states supply `0`. -/
theorem markingLens_surjective {r : ℕ} {x : Fin r → Fin n} (hx : Function.Injective x)
    (hrn : r < n) : Function.Surjective (markingLens x) := by
  intro l
  induction l using Fin.cases with
  | zero =>
      have hpos : 0 < Nat.card {i : Fin n // markingLens x i = 0} := by
        rw [card_fiber_marking_zero hx]; omega
      obtain ⟨⟨i, hi⟩⟩ := (Nat.card_pos_iff.mp hpos).1
      exact ⟨i, hi⟩
  | succ j => exact ⟨x j, markingLens_mark hx j⟩

/-- Each label `j + 1` is carried by exactly one state — the mark `x j`. -/
theorem card_fiber_marking_succ {r : ℕ} {x : Fin r → Fin n} (hx : Function.Injective x)
    (j : Fin r) : Nat.card {i : Fin n // markingLens x i = j.succ} = 1 := by
  rw [Nat.card_eq_one_iff_unique]
  refine ⟨⟨fun a b => ?_⟩, ⟨⟨x j, markingLens_mark hx j⟩⟩⟩
  have ha : x j = (a : Fin n) := (markingLens_eq_succ_iff hx).mp a.2
  have hb : x j = (b : Fin n) := (markingLens_eq_succ_iff hx).mp b.2
  exact Subtype.ext (ha ▸ hb)

/-- **The marking lens's profile** ([Persistence] §5, Proposition 5.3): fiber sizes `(n − r, 1, …,
1)`, so the fiber product — the size of each relabelling coset — is `(n − r)!`. With
`card_orbit_mul_prod_fiber` this pins the carried entropy at `log₂ (n ! / (n − r)!)` exactly. -/
theorem prod_fiber_marking {r : ℕ} {x : Fin r → Fin n} (hx : Function.Injective x) :
    ∏ l : Fin (r + 1), (Nat.card {i : Fin n // markingLens x i = l})! = (n - r)! := by
  rw [Fin.prod_univ_succ, card_fiber_marking_zero hx]
  have hone : ∀ j : Fin r, (Nat.card {i : Fin n // markingLens x i = j.succ})! = 1 := by
    intro j
    rw [card_fiber_marking_succ hx j]
    rfl
  rw [Finset.prod_congr rfl fun j _ => hone j]
  simp

/-- **Every frame of the marking family is itself a marking lens** — with the marks moved along:
`U • markingLens x = markingLens (U ∘ x)`. This is what "the marks ride the world" means
tabulation-side, and it is why the family's price does not drift with `t`: each frame is the *same
kind of object*, `r` marks on `n` states, differing only in where the marks sit. Proposition 5.3's
per-frame bound is therefore one bound, uniform over the marks — not a bound per time step.

Injectivity is needed: it is what makes the label of a marked point unambiguous on both sides. -/
theorem smul_markingLens {r : ℕ} {x : Fin r → Fin n} (hx : Function.Injective x)
    (U : Perm (Fin n)) : U • markingLens x = markingLens (⇑U ∘ x) := by
  have hUx : Function.Injective (⇑U ∘ x) := U.injective.comp hx
  funext i
  rw [smul_lens_apply]
  by_cases hex : ∃ j, (⇑U ∘ x) j = i
  · obtain ⟨j, hj⟩ := hex
    have hxj : x j = U⁻¹ i := by
      rw [← hj]
      simp
    rw [← hxj, markingLens_mark hx j, ← hj, markingLens_mark hUx j]
  · rw [markingLens_unmark hex, markingLens_unmark]
    rintro ⟨j, hj⟩
    exact hex ⟨j, by simp [hj]⟩

/-- **The marks ride the world** ([Persistence] §5, Proposition 5.3, the persistence half): the
family `ℓ t := ℓ₀ ∘ (U ^ t)⁻¹` carries a persistent model over **every** permutation world. Reading
through the time-`t` frame after `t` steps returns the time-`0` reading, by construction — no
genericity, no maximality, no hypothesis on `U` at all. -/
theorem markCarries {r : ℕ} {U : Perm (Fin n)} {x : Fin r → Fin n} (hx : Function.Injective x)
    (hrn : r < n) : PermCarries U (fun t => (U ^ t) • markingLens x) := by
  constructor
  · simpa using markingLens_surjective hx hrn
  · intro t i
    change markingLens x ((U ^ t)⁻¹ ((U ^ t) i)) = markingLens x ((U ^ 0)⁻¹ i)
    simp

/-- **The marking floor** ([Persistence] §5, Proposition 5.3 + §7, Corollary 7.5(i), the floor).
Over **every** permutation world, a budget that affords the marking family carries entropy
`log₂ (n ! / (n − r)!)` — stated division-free as `n ! ≤ CbH U b * (n − r)!`.

The price enters as the hypothesis `hprice`: **`r` marks on `n` states cost at most `b` bits to
tabulate**, uniformly over where the marks sit. That is exactly Proposition 5.3's own claim
(`(2 ^ κ − 1) · (⌈log₂ n⌉ + κ) + O (1)` bits, "for every `t`"), and `smul_markingLens` is what makes
one such bound cover every frame: each frame *is* a marking lens, with the marks moved along.

This is the general form, taking any price bound whatever. `KE_markingLens_le` proves one, and
`CbH_ge_marking'` is the resulting unconditional floor.

Corollary 7.5(i)'s asymptotic `C_b^H (U) ≥ (1/2 − o(1)) · b` — choose the largest affordable `r` and
compare `log₂ (n ! / (n − r)!) ≥ r · (log₂ n − 1)` against the price — is the paper-level conversion
of this exact floor. -/
theorem CbH_ge_marking {r : ℕ} {U : Perm (Fin n)} {x : Fin r → Fin n} (hx : Function.Injective x)
    (hrn : r < n) {b : ℕ}
    (hprice : ∀ y : Fin r → Fin n, Function.Injective y → KE (lensCode (markingLens y)) ≤ b) :
    n ! ≤ CbH U b * (n - r)! := by
  have hb : ∀ t, KE (lensCode ((U ^ t) • markingLens x)) ≤ b := fun t => by
    rw [smul_markingLens hx (U ^ t)]
    exact hprice _ ((U ^ t).injective.comp hx)
  have hmem : Nat.card ↥(orbit (Perm (Fin n)) (markingLens x)) ∈ BudgetedEntropies U b :=
    ⟨r + 1, fun t => (U ^ t) • markingLens x, markCarries hx hrn, hb, by simp⟩
  have hle : Nat.card ↥(orbit (Perm (Fin n)) (markingLens x)) ≤ CbH U b :=
    le_csSup (bddAbove_budgetedEntropies U b) hmem
  calc n ! = Nat.card ↥(orbit (Perm (Fin n)) (markingLens x))
        * ∏ l : Fin (r + 1), (Nat.card {i : Fin n // markingLens x i = l})! :=
        (card_orbit_mul_prod_fiber (markingLens x)).symm
    _ = Nat.card ↥(orbit (Perm (Fin n)) (markingLens x)) * (n - r)! := by
        rw [prod_fiber_marking hx]
    _ ≤ CbH U b * (n - r)! := Nat.mul_le_mul_right _ hle

/-! ## The price of the marking family

Proposition 5.3's own content — "`r` marks on `n` states cost `O (r · log₂ n)` bits to tabulate,
uniformly over where the marks sit" — proved as an explicit code, discharging `CbH_ge_marking`'s
`hprice`.

The route is forced by the additive carrier. The marks are packed as the **base-`n` numeral**
`∑ⱼ (x j) · n ^ j` (`packMarks`), whose bit-length is `r · ⌈log₂ n⌉`; the `Encodable` list encoding
would pair at every cons and cost `2 ^ r`. That numeral, together with `n` and `r`, is loaded as a
single `Nat.pair`-packed program by the binary constant `bconst`, whose additive length is
`O (Nat.size p)` rather than `Θ (p)`, and fed to **one fixed table-builder** (`markBuilder`), which
is independent of `n`, `r`, and the marks — the uniform-constant discipline of `ledger_K`. The
builder's output value is astronomically large; that is irrelevant, since `KE` prices the program,
not the value.

The machine bound prices **positions only**, the labels being implicit in the digit order — slightly
*stronger* than the display of [Persistence] §5, Proposition 5.3, which pays
`(2 ^ κ − 1) · (⌈log₂ n⌉ + κ) + O (1)` for positions and labels together. -/

/-- The `j`-th digit of the packed marks: the `j`-th mark's position, or `0` past the last mark. -/
def markDigit {r : ℕ} (x : Fin r → Fin n) (j : ℕ) : ℕ := if h : j < r then (x ⟨j, h⟩ : ℕ) else 0

/-- **The marks packed as a base-`n` numeral** ([Persistence] §5, Proposition 5.3, the price). Its
bit-length is `r · ⌈log₂ n⌉`, against the `2 ^ r` of an `Encodable` list of positions. -/
def packMarks {r : ℕ} (x : Fin r → Fin n) : ℕ := ∑ j ∈ Finset.range r, markDigit x j * n ^ j

/-- Every digit is a position, hence `< n`. -/
theorem markDigit_lt {r : ℕ} (hn : 0 < n) (x : Fin r → Fin n) (j : ℕ) : markDigit x j < n := by
  unfold markDigit; split
  · exact (x _).2
  · exact hn

/-- An `r`-digit base-`n` numeral is `< n ^ r`. -/
private theorem sum_digits_lt (d : ℕ → ℕ) (hd : ∀ j, d j < n) :
    ∀ r : ℕ, (∑ j ∈ Finset.range r, d j * n ^ j) < n ^ r := by
  intro r
  induction r with
  | zero => simp
  | succ r ih =>
    rw [Finset.sum_range_succ, pow_succ]
    calc (∑ j ∈ Finset.range r, d j * n ^ j) + d r * n ^ r
        < n ^ r + d r * n ^ r := by omega
      _ = (d r + 1) * n ^ r := by ring
      _ ≤ n * n ^ r := Nat.mul_le_mul_right _ (by have := hd r; omega)
      _ = n ^ r * n := by ring

/-- Base-`n` digit extraction: dividing out the lower digits and reducing mod `n` returns `d k`.
Induction on the digit count, peeling the low digit via `S = d 0 + n · S'`. -/
private theorem sum_digits_div_mod (hn : 0 < n) :
    ∀ (r : ℕ) (d : ℕ → ℕ), (∀ j, d j < n) → ∀ k, k < r →
      (∑ j ∈ Finset.range r, d j * n ^ j) / n ^ k % n = d k := by
  intro r
  induction r with
  | zero => intro d hd k hk; omega
  | succ r ih =>
    intro d hd k hk
    have hpeel : (∑ j ∈ Finset.range (r + 1), d j * n ^ j)
        = d 0 + n * ∑ j ∈ Finset.range r, d (j + 1) * n ^ j := by
      rw [Finset.sum_range_succ']
      simp only [pow_zero, mul_one, pow_succ, Finset.mul_sum]
      ring_nf
      rw [Nat.add_comm]
      congr 1
      exact Finset.sum_congr rfl fun j _ => by ring
    match k with
    | 0 =>
      rw [hpeel, pow_zero, Nat.div_one, Nat.add_mul_mod_self_left]
      exact Nat.mod_eq_of_lt (hd 0)
    | (k + 1) =>
      have hrec : (∑ j ∈ Finset.range (r + 1), d j * n ^ j) / n
          = ∑ j ∈ Finset.range r, d (j + 1) * n ^ j := by
        rw [hpeel, Nat.add_mul_div_left _ _ hn, Nat.div_eq_of_lt (hd 0), Nat.zero_add]
      have hsplit : (∑ j ∈ Finset.range (r + 1), d j * n ^ j) / n ^ (k + 1)
          = ((∑ j ∈ Finset.range (r + 1), d j * n ^ j) / n) / n ^ k := by
        rw [Nat.div_div_eq_div_mul, ← pow_succ']
      rw [hsplit, hrec]
      exact ih (fun j => d (j + 1)) (fun j => hd (j + 1)) k (by omega)

/-- **The packing is faithful**: the numeral's `k`-th base-`n` digit is the `k`-th mark. -/
theorem digit_packMarks (hn : 0 < n) {r : ℕ} (x : Fin r → Fin n) (k : Fin r) :
    packMarks x / n ^ (k : ℕ) % n = (x k : ℕ) := by
  rw [packMarks, sum_digits_div_mod hn r (markDigit x) (markDigit_lt hn x) k k.2]
  unfold markDigit
  rw [dif_pos k.2]

/-- The packing fits in `r` base-`n` digits. -/
theorem packMarks_lt (hn : 0 < n) {r : ℕ} (x : Fin r → Fin n) : packMarks x < n ^ r :=
  sum_digits_lt _ (markDigit_lt hn x) r

/-- **The packing costs `r · Nat.size n` bits** — linear in `r`, against the `Encodable` list
encoding's `2 ^ r`. This is the whole reason for the numeral. -/
theorem size_packMarks_le (hn : 0 < n) {r : ℕ} (x : Fin r → Fin n) :
    Nat.size (packMarks x) ≤ r * Nat.size n := by
  rw [Nat.size_le]
  calc packMarks x < n ^ r := packMarks_lt hn x
    _ ≤ (2 ^ Nat.size n) ^ r := Nat.pow_le_pow_left (le_of_lt (Nat.lt_size_self n)) r
    _ = 2 ^ (r * Nat.size n) := by rw [← pow_mul, Nat.mul_comm]

private theorem pair_lt_sq (a b : ℕ) : Nat.pair a b < (a + b + 1) ^ 2 := by
  rw [Nat.pair]
  split
  · next h => nlinarith
  · next h => nlinarith [Nat.not_lt.mp h]

/-- **Pairing costs a constant factor in bits**: `Nat.pair` squares the value, hence doubles the
bit-length, up to an additive constant. The bookkeeping that keeps the packed program
logarithmic. -/
theorem size_pair_le (a b : ℕ) : Nat.size (Nat.pair a b) ≤ 2 * (Nat.size a + Nat.size b) + 2 := by
  have hs : Nat.size (a + b + 1) ≤ Nat.size a + Nat.size b + 1 := by
    rw [Nat.size_le]
    have ha := Nat.lt_size_self a
    have hb := Nat.lt_size_self b
    calc a + b + 1 < 2 ^ Nat.size a + 2 ^ Nat.size b := by omega
      _ ≤ 2 ^ (Nat.size a + Nat.size b) + 2 ^ (Nat.size a + Nat.size b) := by
          have h1 : (2 : ℕ) ^ Nat.size a ≤ 2 ^ (Nat.size a + Nat.size b) :=
            Nat.pow_le_pow_right (by norm_num) (by omega)
          have h2 : (2 : ℕ) ^ Nat.size b ≤ 2 ^ (Nat.size a + Nat.size b) :=
            Nat.pow_le_pow_right (by norm_num) (by omega)
          omega
      _ = 2 ^ (Nat.size a + Nat.size b + 1) := by ring
  rw [Nat.size_le]
  calc Nat.pair a b < (a + b + 1) ^ 2 := pair_lt_sq a b
    _ < (2 ^ Nat.size (a + b + 1)) ^ 2 := Nat.pow_lt_pow_left (Nat.lt_size_self _) (by norm_num)
    _ = 2 ^ (2 * Nat.size (a + b + 1)) := by rw [← pow_mul, Nat.mul_comm]
    _ ≤ 2 ^ (2 * (Nat.size a + Nat.size b) + 2) := by
        apply Nat.pow_le_pow_right (by norm_num); omega

/-- The `j`-th base-`n` digit of `v`, at the level the builder works: plain arithmetic on `ℕ`. -/
def digitAt (n v j : ℕ) : ℕ := v / n ^ j % n

/-- The label the marking lens assigns to state `i`, read off the packed marks: the index of the
mark sitting at `i`, plus one, or `0` if none does. The sum is a bounded search — under injectivity
at most one term survives. -/
def markVal (n r v i : ℕ) : ℕ :=
  ((List.range r).map fun j => if digitAt n v j = i then j + 1 else 0).sum

/-- **The tabulation, rebuilt from the packed program `⟨n, r, v⟩`** — ONE fixed function of a single
natural number, carrying no dependence on `n`, `r`, or the marks. -/
def markTableFn (a : ℕ) : ℕ :=
  Encodable.encode ((List.range a.unpair.1).map
    (markVal a.unpair.1 a.unpair.2.unpair.1 a.unpair.2.unpair.2))

theorem markVal_eq_sum (n r v i : ℕ) :
    markVal n r v i = ∑ j ∈ Finset.range r, (if digitAt n v j = i then j + 1 else 0) := by
  rw [markVal]; simp [Finset.sum, Multiset.range]

/-- **The builder reads the marking lens back off the numeral.** Injectivity is what collapses the
bounded search to a single term: at most one mark sits at any given state. -/
theorem markVal_eq (hn : 0 < n) {r : ℕ} {x : Fin r → Fin n} (hx : Function.Injective x)
    (i : Fin n) : markVal n r (packMarks x) (i : ℕ) = (markingLens x i : ℕ) := by
  rw [markVal_eq_sum]
  -- the test at index `j < r` fires exactly when the `j`-th mark sits at `i`
  have htest : ∀ (j : ℕ) (hj : j < r),
      (digitAt n (packMarks x) j = (i : ℕ)) ↔ x ⟨j, hj⟩ = i := by
    intro j hj
    rw [show digitAt n (packMarks x) j = (x ⟨j, hj⟩ : ℕ) from digit_packMarks hn x ⟨j, hj⟩]
    exact ⟨fun h => Fin.val_injective h, fun h => congrArg Fin.val h⟩
  by_cases hex : ∃ k : Fin r, x k = i
  · -- marked: injectivity leaves exactly one surviving term
    obtain ⟨k, hk⟩ := hex
    have hml : (markingLens x i : ℕ) = (k : ℕ) + 1 := by
      rw [← hk, markingLens_mark hx k]; simp
    have hc : digitAt n (packMarks x) (k : ℕ) = (i : ℕ) := by
      rw [htest (k : ℕ) k.2, Fin.eta]; exact hk
    have h0 : ∀ j ∈ Finset.range r, j ≠ (k : ℕ) →
        (if digitAt n (packMarks x) j = (i : ℕ) then j + 1 else 0) = 0 := by
      intro j hj hjk
      rw [Finset.mem_range] at hj
      have hnc : ¬(digitAt n (packMarks x) j = (i : ℕ)) := by
        rw [htest j hj]
        exact fun hcontra => hjk (congrArg Fin.val (hx (hcontra.trans hk.symm)))
      rw [if_neg hnc]
    have h1 : (k : ℕ) ∉ Finset.range r →
        (if digitAt n (packMarks x) (k : ℕ) = (i : ℕ) then (k : ℕ) + 1 else 0) = 0 :=
      fun hk' => absurd (Finset.mem_range.mpr k.2) hk'
    rw [Finset.sum_eq_single (k : ℕ) h0 h1, if_pos hc, hml]
  · -- unmarked: every term vanishes
    rw [markingLens_unmark hex, Fin.val_zero]
    refine Finset.sum_eq_zero fun j hj => ?_
    rw [Finset.mem_range] at hj
    have hnc : ¬(digitAt n (packMarks x) j = (i : ℕ)) := by
      rw [htest j hj]
      exact fun hcontra => hex ⟨⟨j, hj⟩, hcontra⟩
    rw [if_neg hnc]

/-- **The builder is correct**: on the packed program `⟨n, r, packMarks x⟩` it outputs exactly the
marking lens's encoded tabulation — the very number whose `KE` is the frame's price. -/
theorem markTableFn_eq (hn : 0 < n) {r : ℕ} {x : Fin r → Fin n} (hx : Function.Injective x) :
    markTableFn (Nat.pair n (Nat.pair r (packMarks x))) = lensCode (markingLens x) := by
  rw [markTableFn, lensCode, lensTable]
  simp only [Nat.unpair_pair]
  congr 1
  have hfr : (List.finRange n).map Fin.val = List.range n := by simp
  rw [← hfr, List.map_map]
  exact List.map_congr_left fun i _ => markVal_eq hn hx i

/-- Summing a primitive-recursive list of naturals is primitive recursive (`List.sum` as a
`foldr`). -/
theorem primrec_list_sum {α : Type*} [Primcodable α] {f : α → List ℕ} (hf : Primrec f) :
    Primrec fun a => (f a).sum :=
  (Primrec.list_foldr hf (Primrec.const 0)
      (Primrec.nat_add.comp (Primrec.fst.comp Primrec.snd)
        (Primrec.snd.comp Primrec.snd)).to₂).of_eq
    fun a => by simp [List.sum_eq_foldr]

/-- **The builder is primitive recursive.** Digit extraction is `/`, `^`, `%`; the mark's index is a
bounded search over `List.range r`; the tabulation is a `List.map` over `List.range n`. -/
theorem primrec_markTableFn : Primrec markTableFn := by
  have hN : Primrec fun a : ℕ => a.unpair.1 := Primrec.fst.comp Primrec.unpair
  have hRV : Primrec fun a : ℕ => a.unpair.2 := Primrec.snd.comp Primrec.unpair
  have hR : Primrec fun a : ℕ => a.unpair.2.unpair.1 := Primrec.fst.comp (Primrec.unpair.comp hRV)
  have hV : Primrec fun a : ℕ => a.unpair.2.unpair.2 := Primrec.snd.comp (Primrec.unpair.comp hRV)
  have hpow : Primrec₂ ((· ^ ·) : ℕ → ℕ → ℕ) := Primrec₂.unpaired'.1 Nat.Primrec.pow
  -- the digit test, over `q : (ℕ × ℕ) × ℕ` — `q.1.1` the program, `q.1.2` the state, `q.2` the mark
  have hinner : Primrec₂ fun (p : ℕ × ℕ) (j : ℕ) =>
      if digitAt p.1.unpair.1 p.1.unpair.2.unpair.2 j = p.2 then j + 1 else 0 := by
    have ha : Primrec fun q : (ℕ × ℕ) × ℕ => q.1.1 := Primrec.fst.comp Primrec.fst
    have hdig : Primrec fun q : (ℕ × ℕ) × ℕ =>
        digitAt q.1.1.unpair.1 q.1.1.unpair.2.unpair.2 q.2 :=
      Primrec.nat_mod.comp
        (Primrec.nat_div.comp (hV.comp ha) (hpow.comp (hN.comp ha) Primrec.snd))
        (hN.comp ha)
    exact (Primrec.ite (PrimrecRel.comp Primrec.eq hdig (Primrec.snd.comp Primrec.fst))
      (Primrec.succ.comp Primrec.snd) (Primrec.const 0)).to₂
  -- the label at one state
  have hmarkVal : Primrec₂ fun (a : ℕ) (i : ℕ) =>
      markVal a.unpair.1 a.unpair.2.unpair.1 a.unpair.2.unpair.2 i :=
    (primrec_list_sum (f := fun p : ℕ × ℕ =>
        (List.range p.1.unpair.2.unpair.1).map fun j =>
          if digitAt p.1.unpair.1 p.1.unpair.2.unpair.2 j = p.2 then j + 1 else 0)
      (Primrec.list_map (Primrec.list_range.comp (hR.comp Primrec.fst)) hinner)).to₂
  exact Primrec.encode.comp (Primrec.list_map (Primrec.list_range.comp hN) hmarkVal)

theorem partrec_markTableFn : Nat.Partrec (fun a : ℕ => (markTableFn a : ℕ)) :=
  _root_.Partrec.nat_iff.mp (Primrec.to_comp primrec_markTableFn).partrec

/-- **The fixed table-builder code.** Extracted from universality, it takes no parameters: one
program, independent of `n`, `r`, and where the marks sit — the uniform constant `ledger_K`'s
discipline demands, and what makes the price below a single bound covering every frame. -/
noncomputable def markBuilder : Nat.Partrec.Code :=
  Classical.choose (Nat.Partrec.Code.exists_code.mp partrec_markTableFn)

/-- The builder's evaluation law. -/
theorem eval_markBuilder (a : ℕ) :
    Nat.Partrec.Code.eval markBuilder a = Part.some (markTableFn a) := by
  have h := congrFun (Classical.choose_spec
    (Nat.Partrec.Code.exists_code.mp partrec_markTableFn)) a
  simpa [markBuilder] using h

/-- **The marking lens's explicit price** ([Persistence] §5, Proposition 5.3, the cost bound):
`r` marks on `n` states are tabulated by a program of length
`6 · κ · (r + 1) · Nat.size n + O (1)`, with `κ = 15 + elen dbl` and the additive constant
`elen markBuilder + 7 · κ + 3` — both absolute, fixed once and for all.

The bound is **uniform over the marks**: `x` occurs only on the left. That is exactly the quantifier
`CbH_ge_marking`'s `hprice` needs, and with `smul_markingLens` — every frame is itself a marking
lens, with the marks moved along — one such bound prices the whole family, at every `t`.

Assembly: `comp markBuilder (bconst ⟨n, r, packMarks x⟩)`. The marks ride in a base-`n` numeral of
`r · Nat.size n` bits (`size_packMarks_le`), `Nat.pair` costs a constant factor (`size_pair_le`),
`bconst` loads the packed program in `O (Nat.size p)` rather than `Θ (p)` (`elen_bconst_le`), and
`invariance_general` charges the fixed builder once.

Taking `r + 1 = 2 ^ κ ≤ n / 2` this is the proposition's `c₁ · 2 ^ κ · log₂ n`. It prices positions
only — the labels are implicit in the digit order — where the paper's display pays
`(2 ^ κ − 1) · (⌈log₂ n⌉ + κ) + O (1)` for both. -/
theorem KE_markingLens_le {r : ℕ} (hrn : r < n) {x : Fin r → Fin n}
    (hx : Function.Injective x) :
    KE (lensCode (markingLens x))
      ≤ 6 * (15 + elen dbl) * ((r + 1) * Nat.size n)
        + (elen markBuilder + 7 * (15 + elen dbl) + 3) := by
  have hn : 0 < n := by omega
  have heval : Nat.Partrec.Code.eval markBuilder (Nat.pair n (Nat.pair r (packMarks x)))
      = Part.some (lensCode (markingLens x)) := by
    rw [eval_markBuilder, markTableFn_eq hn hx]
  have hinv := invariance_general markBuilder (Nat.pair n (Nat.pair r (packMarks x))) _ heval
  -- the packed program is `O ((r + 1) · Nat.size n)` bits
  have hsr : Nat.size r ≤ Nat.size n := Nat.size_le_size (le_of_lt hrn)
  have hsv : Nat.size (packMarks x) ≤ r * Nat.size n := size_packMarks_le hn x
  have h1 : Nat.size (Nat.pair r (packMarks x)) ≤ 2 * ((r + 1) * Nat.size n) + 2 := by
    have := size_pair_le r (packMarks x)
    have hrw : (r + 1) * Nat.size n = r * Nat.size n + Nat.size n := by ring
    omega
  have hn1 : Nat.size n ≤ (r + 1) * Nat.size n := Nat.le_mul_of_pos_left _ (by omega)
  have h2 : Nat.size (Nat.pair n (Nat.pair r (packMarks x))) ≤ 6 * ((r + 1) * Nat.size n) + 6 := by
    have := size_pair_le n (Nat.pair r (packMarks x))
    omega
  have hkey : (15 + elen dbl) * Nat.size (Nat.pair n (Nat.pair r (packMarks x)))
      ≤ 6 * (15 + elen dbl) * ((r + 1) * Nat.size n) + 6 * (15 + elen dbl) := by
    calc (15 + elen dbl) * Nat.size (Nat.pair n (Nat.pair r (packMarks x)))
        ≤ (15 + elen dbl) * (6 * ((r + 1) * Nat.size n) + 6) := Nat.mul_le_mul_left _ h2
      _ = 6 * (15 + elen dbl) * ((r + 1) * Nat.size n) + 6 * (15 + elen dbl) := by ring
  calc KE (lensCode (markingLens x))
      ≤ elen markBuilder + (15 + elen dbl) * Nat.size (Nat.pair n (Nat.pair r (packMarks x)))
          + (3 + (15 + elen dbl)) := hinv
    _ ≤ elen markBuilder + (6 * (15 + elen dbl) * ((r + 1) * Nat.size n) + 6 * (15 + elen dbl))
          + (3 + (15 + elen dbl)) := Nat.add_le_add_right (Nat.add_le_add_left hkey _) _
    _ = 6 * (15 + elen dbl) * ((r + 1) * Nat.size n)
          + (elen markBuilder + 7 * (15 + elen dbl) + 3) := by ring

/-- **The marking floor, unconditional** ([Persistence] §5, Proposition 5.3 + §7, Corollary 7.5(i)).
`CbH_ge_marking` with its price hypothesis discharged by `KE_markingLens_le`: over **every**
permutation world, a budget that clears the explicit price of `r` marks carries entropy
`log₂ (n ! / (n − r)!)`, stated division-free.

No genericity, no maximality, no hypothesis on `U`, and — now — no named price. -/
theorem CbH_ge_marking' {r : ℕ} {U : Perm (Fin n)} {x : Fin r → Fin n}
    (hx : Function.Injective x) (hrn : r < n) {b : ℕ}
    (hb : 6 * (15 + elen dbl) * ((r + 1) * Nat.size n)
        + (elen markBuilder + 7 * (15 + elen dbl) + 3) ≤ b) :
    n ! ≤ CbH U b * (n - r)! :=
  CbH_ge_marking hx hrn fun _ hy => le_trans (KE_markingLens_le hrn hy) hb

/-! ## Renting versus owning a reading ([Persistence] §5, Definition 5.1, the uniform variant)

Definition 5.1's budget is **per-frame**: each frame's table must be describable in `b` bits, and
nothing relates the descriptions. An observer meeting it *rents* its reading — it pays the floor
again at every step, forever, and the collapse prices exactly that rent.

The uniform variant named after Definition 5.1 is the other way to hold a reading: one program of
length at most `b` computing `t ↦ ℓ t`. The observer *owns* the reading, paying once. The exchange
rate between the two is the paper's `K (ℓ t) ≤ b + O (log t)`, and `uniformBudget_frame_cost` is
that reduction with both constants explicit and absolute: the owner's program, run at `t`, is a
description of frame `t` — hand `t` to it as a binary constant and `invariance_general` charges the
program once and the clock `O (log t)`.

The reduction is what makes the uniform capacity's cap **horizon-free**. `CbHu_collapse` below is
`CbH_collapse` with the budget shifted by an absolute constant and *no* `log T` term anywhere,
because the collapse consumes frames `0` and `1` only (`permCarries_frame_one`) — and those two
clock inputs are constants, so their `O (log t)` is `O (1)`. Renting and owning collapse alike;
what differs is what the observer pays to get there. -/

/-- **The uniform budget** ([Persistence] §5, Definition 5.1, the uniform variant): a *single*
program of length at most `b` computes every frame's table, `t ↦ lensCode (ℓ t)`. Contrast
`PermBudget`, which asks only that each frame have *some* `b`-bit description of its own — a
uniform budget is strictly the stronger demand, and the observer meeting it pays once rather than
per frame. -/
def UniformBudget (ℓ : ℕ → Fin n → Fin m) (b : ℕ) : Prop :=
  ∃ c : Nat.Partrec.Code, elen c ≤ b ∧ ∀ t, c.eval t = Part.some (lensCode (ℓ t))

/-- A larger budget affords no less: the same program witnesses it. -/
theorem UniformBudget.mono {ℓ : ℕ → Fin n → Fin m} {b₁ b₂ : ℕ} (h : UniformBudget ℓ b₁)
    (hb : b₁ ≤ b₂) : UniformBudget ℓ b₂ :=
  let ⟨c, hlen, heval⟩ := h
  ⟨c, hlen.trans hb, heval⟩

/-- **The frame-cost reduction** — [Persistence] §5, the uniform variant's
`K (ℓ t) ≤ b + O (log t)`.
An owner's program is a description of every one of its frames, at the price of the clock: run the
program on the binary numeral for `t`. The `O (log t)` is `κ · Nat.size t` with `κ = 15 + elen dbl`
and the additive constant `3 + κ`, both absolute — fixed once and for all, independent of the
family, the world, and `n`.

This is what converts an owned reading into a rented one, and it is the only bridge between the two
budgets used below. -/
theorem uniformBudget_frame_cost {ℓ : ℕ → Fin n → Fin m} {b : ℕ} (h : UniformBudget ℓ b) (t : ℕ) :
    KE (lensCode (ℓ t)) ≤ b + (15 + elen dbl) * Nat.size t + (3 + (15 + elen dbl)) := by
  obtain ⟨c, hlen, heval⟩ := h
  have hinv := invariance_general c t (lensCode (ℓ t)) (heval t)
  omega

/-- **The first two frames cost the budget plus a constant.** The clock inputs `t = 0` and `t = 1`
are themselves constants — `Nat.size t ≤ 1` — so the reduction's `O (log t)` degenerates to `O (1)`
on exactly the frames the collapse reads. No horizon appears, and none can: the bound is uniform in
everything. -/
theorem uniformBudget_early_cost {ℓ : ℕ → Fin n → Fin m} {b : ℕ} (h : UniformBudget ℓ b) {t : ℕ}
    (ht : t ≤ 1) : KE (lensCode (ℓ t)) ≤ b + (33 + 2 * elen dbl) := by
  have hc := uniformBudget_frame_cost h t
  have hs : Nat.size t ≤ 1 := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp ht with rfl | rfl <;> simp
  have hm := Nat.mul_le_mul (le_refl (15 + elen dbl)) hs
  omega

/-- The **carried entropies affordable to an owner at budget `b`**: `BudgetedEntropies` with the
per-frame predicate replaced by `UniformBudget`. -/
def UniformBudgetedEntropies (U : Perm (Fin n)) (b : ℕ) : Set ℕ :=
  {N : ℕ | ∃ k : ℕ, ∃ ℓ : ℕ → Fin n → Fin k, PermCarries U ℓ ∧ UniformBudget ℓ b ∧
      N = Nat.card ↥(orbit (Perm (Fin n)) (ℓ 0))}

/-- **The uniform entropic capacity** — [Persistence] §5, Definition 5.4 read through Definition
5.1's uniform variant: the largest carried entropy, as the relabelling-class size `2 ^ E` (the
cardinality form of `CbH`, see above), of a reference frame whose family is computed *by one
program* of at most `b` bits. The capacity of an observer that owns its reading rather than renting
it. -/
noncomputable def CbHu (U : Perm (Fin n)) (b : ℕ) : ℕ := sSup (UniformBudgetedEntropies U b)

/-- No reading distinguishes more than the world has to offer (`budgetedEntropies_le`'s argument,
verbatim: the budget plays no part). -/
theorem uniformBudgetedEntropies_le {U : Perm (Fin n)} {b N : ℕ}
    (h : N ∈ UniformBudgetedEntropies U b) : N ≤ n ! := by
  obtain ⟨k, ℓ, -, -, rfl⟩ := h
  have hprod : 0 < ∏ i : Fin k, (Nat.card {x : Fin n // ℓ 0 x = i})! :=
    Finset.prod_pos fun i _ => Nat.factorial_pos _
  exact card_orbit_mul_prod_fiber (ℓ 0) ▸ Nat.le_mul_of_pos_right _ hprod

theorem bddAbove_uniformBudgetedEntropies (U : Perm (Fin n)) (b : ℕ) :
    BddAbove (UniformBudgetedEntropies U b) :=
  ⟨n !, fun _ h => uniformBudgetedEntropies_le h⟩

/-- **An owner's capacity never exceeds a faithful reading** either. -/
theorem CbHu_le_factorial (U : Perm (Fin n)) (b : ℕ) : CbHu U b ≤ n ! := by
  rcases Set.eq_empty_or_nonempty (UniformBudgetedEntropies U b) with hemp | hne
  · simp [CbHu, hemp]
  · exact csSup_le hne fun _ h => uniformBudgetedEntropies_le h

/-- More budget never hurts an owner either. -/
theorem CbHu_mono (U : Perm (Fin n)) {b₁ b₂ : ℕ} (h : b₁ ≤ b₂) : CbHu U b₁ ≤ CbHu U b₂ :=
  csSup_le_csSup' (bddAbove_uniformBudgetedEntropies U b₂) (by
    rintro N ⟨k, ℓ, hcar, hbud, rfl⟩
    exact ⟨k, ℓ, hcar, hbud.mono h, rfl⟩)

/-- **Owning does not beat the collapse** — the uniform capacity's cap, horizon-free. For every `d`,
the worlds whose *uniform* entropic capacity at budget `b` exceeds `2 · (b + c) + d + 2` — with the
absolute constant `c = 33 + 2 · elen dbl` — number at most `n ! / 2 ^ d`, a `2 ^ (-d)` fraction.

This is `CbH_collapse` with the budget shifted by `c` and **nothing else changed**: no horizon, no
`log T`, no growing term. The reason is structural rather than incidental. `collapse_union` prices a
world through frames `0` and `1` alone (`permCarries_frame_one` determines the second frame from the
first), the frame-cost reduction charges frame `t` a clock of `O (log t)`, and `log 0` and `log 1`
are `O (1)`. So the whole `O (log t)` slack of the uniform variant is spent before the clock ever
ticks, and an owner faces the same `Θ (b)` ceiling a renter does — at any horizon whatsoever.

Ownership is therefore not a way around the collapse; it is a way to *pay for a reading once*. What
it buys is the subject of the (CD) constructions below. -/
theorem CbHu_collapse (b d : ℕ) :
    {U : Perm (Fin n) | 2 ^ (2 * (b + (33 + 2 * elen dbl)) + d + 2) < CbHu U b}.ncard * 2 ^ d
      ≤ n ! := by
  refine le_trans (Nat.mul_le_mul_right _ (Set.ncard_le_ncard ?_ (Set.toFinite _)))
    (collapse_union d)
  intro U hU
  have hlt : 2 ^ (2 * (b + (33 + 2 * elen dbl)) + d + 2) < CbHu U b := hU
  have hne : (UniformBudgetedEntropies U b).Nonempty := by
    by_contra hcon
    rw [Set.not_nonempty_iff_eq_empty] at hcon
    rw [CbHu, hcon, csSup_empty] at hlt
    exact absurd hlt (Nat.not_lt_zero _)
  obtain ⟨k, ℓ, hcar, hbud, hval⟩ : CbHu U b ∈ UniformBudgetedEntropies U b :=
    Nat.sSup_mem hne (bddAbove_uniformBudgetedEntropies U b)
  refine ⟨k, ℓ 0, hcar.1, ?_⟩
  have h1 : ℓ 1 = U • ℓ 0 := permCarries_frame_one hcar
  have hb0 := uniformBudget_early_cost hbud (t := 0) (by norm_num)
  have hb1 := uniformBudget_early_cost hbud (t := 1) (le_refl 1)
  rw [h1, show U • ℓ 0 = ℓ 0 ∘ ⇑U⁻¹ from rfl] at hb1
  calc 2 ^ (KE (lensCode (ℓ 0)) + KE (lensCode (ℓ 0 ∘ ⇑U⁻¹)) + d + 2)
      ≤ 2 ^ (2 * (b + (33 + 2 * elen dbl)) + d + 2) :=
        Nat.pow_le_pow_right (by norm_num) (by omega)
    _ < Nat.card ↥(orbit (Perm (Fin n)) (ℓ 0)) := hval ▸ hlt

/-! ## The ownership construction ([Persistence] §8, Proposition 8.1)

Proposition 8.1 prices the canonical family `ℓ t = θ ∘ (U_∞⁻¹) ^ t ∘ U ^ N` at
`K (U|core) + K (θ) + O (log t)` per frame. `ownership` is the corresponding construction in the §7
permutation setting, where the world is its own recurrent core (no transient `U ^ N`, and
`U_∞ = U`) and the family is `ℓ t = ℓ₀ ∘ (U ^ t)⁻¹`: a code for `ℓ₀`'s table and a code for `U`'s
table assemble — by a *fixed* builder, absolute constant included — into a **uniform** budget for
the whole family.

Two things are worth reading off the statement. First, the world's own table needs no new encoding
apparatus: a permutation of `Fin n` coerces to a function `Fin n → Fin n`, which is a lens, so
`lensCode ⇑U` is the same object the collapse already prices. Second, Proposition 8.1's `O (log t)`
per frame does not appear here — it has been *absorbed* into the definition of `UniformBudget`, and
`uniformBudget_frame_cost` is where it reappears, with the constant made explicit. That is the whole
point of the uniform variant: the clock is not part of what the owner stores.

The construction itself is table transport. `U`'s table is inverted by `idx` — the ledger's own
primitive — and the reading is dragged along it once per step. -/

/-- The canonical family over a permutation world carries a persistent model, for **any** surjective
reference frame ([Persistence] §7). `markCarries`, with the marking lens generalized away: reading
through the time-`t` frame after `t` steps returns the time-`0` reading by construction, over every
permutation world, with no hypothesis on `U`. -/
theorem permCarries_smul {U : Perm (Fin n)} {ℓ₀ : Fin n → Fin m} (h : Function.Surjective ℓ₀) :
    PermCarries U (fun t => (U ^ t) • ℓ₀) := by
  constructor
  · simpa using h
  · intro t i
    change ℓ₀ ((U ^ t)⁻¹ ((U ^ t) i)) = ℓ₀ ((U ^ 0)⁻¹ i)
    simp

/-- One step of **table transport**: the reading `L`, dragged along the world whose own table is
`P`. Entry `i` of the new table is entry `idx i P` of the old — and `idx i P` is the unique `j` with
`U j = i`, that is, `U⁻¹ i`. So `ownStep P` computes `L ↦ L ∘ U⁻¹` on tables, using nothing but the
list operations, and `idx` is the same table inversion the ledger runs on. -/
def ownStep (P L : List ℕ) : List ℕ := (List.range L.length).map fun i => L.getD (idx i P) 0

/-- `t` steps of table transport — the owner's whole computation, once the tables are in hand. -/
def ownIter (P : List ℕ) (t : ℕ) (L : List ℕ) : List ℕ := (ownStep P)^[t] L

/-- Reading an entry out of a tabulation over `Fin n`. -/
theorem getD_map_finRange (g : Fin n → ℕ) (j : Fin n) :
    ((List.finRange n).map g).getD (j : ℕ) 0 = g j := by
  have hj : (j : ℕ) < ((List.finRange n).map g).length := by simp [j.2]
  rw [List.getD_eq_getElem _ _ hj]
  simp

/-- **Table transport is composition with `U⁻¹`**: one step of `ownStep` against the world's own
table is exactly one step of the canonical family. Injectivity of `U` is what makes `idx` invert the
table (`idx_map_finRange`). -/
theorem ownStep_lensTable (U : Perm (Fin n)) (ℓ : Fin n → Fin m) :
    ownStep (lensTable ⇑U) (lensTable ℓ) = lensTable (ℓ ∘ ⇑U⁻¹) := by
  have hfinj : Function.Injective (fun j : Fin n => ((U j : Fin n) : ℕ)) :=
    Fin.val_injective.comp U.injective
  have hlen : (lensTable ℓ).length = n := by simp [lensTable]
  have hfr : (List.finRange n).map Fin.val = List.range n := by simp
  rw [ownStep, hlen, ← hfr, List.map_map]
  refine List.map_congr_left fun i _ => ?_
  -- `idx i (lensTable ⇑U) = U⁻¹ i`: the table is an injective tabulation, so `idx` inverts it
  have hidx : idx (i : ℕ) (lensTable ⇑U) = ((U⁻¹ i : Fin n) : ℕ) := by
    have h := idx_map_finRange (fun j : Fin n => ((U j : Fin n) : ℕ)) hfinj (U⁻¹ i)
    simpa [lensTable] using h
  simp only [Function.comp_apply]
  rw [hidx, lensTable, getD_map_finRange]

/-- Iterated transport realizes the canonical family: `t` steps of `ownStep` against `U`'s table
turn `ℓ₀`'s table into frame `t`'s. -/
theorem ownIter_lensTable (U : Perm (Fin n)) (ℓ₀ : Fin n → Fin m) (t : ℕ) :
    ownIter (lensTable ⇑U) t (lensTable ℓ₀) = lensTable ((U ^ t) • ℓ₀) := by
  induction t with
  | zero => simp [ownIter]
  | succ t ih =>
    have hstep : ownIter (lensTable ⇑U) (t + 1) (lensTable ℓ₀)
        = ownStep (lensTable ⇑U) (ownIter (lensTable ⇑U) t (lensTable ℓ₀)) :=
      Function.iterate_succ_apply' _ _ _
    -- transport by `U⁻¹` IS the action of `U`, and `U * U ^ t = U ^ (t + 1)`
    have hcomp : ((U ^ t) • ℓ₀) ∘ ⇑U⁻¹ = (U ^ (t + 1)) • ℓ₀ := by
      rw [show ((U ^ t) • ℓ₀) ∘ ⇑U⁻¹ = U • ((U ^ t) • ℓ₀) from rfl, ← mul_smul,
        ← _root_.pow_succ']
    rw [hstep, ih, ownStep_lensTable, hcomp]

/-- **The owner's program, rebuilt from `⟨⟨ℓ₀'s table, U's table⟩, t⟩`** — ONE fixed function of a
single natural number, carrying no dependence on `n`, the world, or the reading: decode the two
tables, transport `t` times, re-encode. -/
def ownTableFn (a : ℕ) : ℕ :=
  Encodable.encode
    (ownIter ((Encodable.decode (α := List ℕ) a.unpair.1.unpair.2).getD [])
      a.unpair.2
      ((Encodable.decode (α := List ℕ) a.unpair.1.unpair.1).getD []))

theorem primrec_ownStep : Primrec₂ ownStep := by
  have hg : Primrec₂ fun (q : List ℕ × List ℕ) (i : ℕ) => q.2.getD (idx i q.1) 0 :=
    ((Primrec.list_getD 0).comp (Primrec.snd.comp Primrec.fst)
      (primrec_idx.comp (Primrec.pair Primrec.snd (Primrec.fst.comp Primrec.fst)))).to₂
  exact (Primrec.list_map
    (Primrec.list_range.comp (Primrec.list_length.comp Primrec.snd)) hg).to₂

/-- `Nat.rec` on a constant motive is iteration. -/
private theorem natRec_iterate {α : Type*} (f : α → α) (x : α) : ∀ t : ℕ,
    (Nat.rec (motive := fun _ => α) x (fun _ IH => f IH) t) = f^[t] x
  | 0 => rfl
  | t + 1 => by
    rw [Function.iterate_succ_apply']
    exact congrArg f (natRec_iterate f x t)

theorem primrec_ownIter : Primrec₂ fun (q : List ℕ × List ℕ) (t : ℕ) => ownIter q.1 t q.2 := by
  have hg : Primrec₂ fun (q : List ℕ × List ℕ) (p : ℕ × List ℕ) => ownStep q.1 p.2 :=
    (primrec_ownStep.comp (Primrec.fst.comp Primrec.fst)
      (Primrec.snd.comp Primrec.snd)).to₂
  exact (Primrec.nat_rec (f := fun q : List ℕ × List ℕ => q.2) Primrec.snd hg).of_eq
    fun q t => natRec_iterate (ownStep q.1) q.2 t

/-- **The owner's builder is primitive recursive.** Decoding is `Primrec.decode`, transport is a
`List.map` over `List.range` composed with the ledger's table inversion, and the iteration is
`Nat.rec`. -/
theorem primrec_ownTableFn : Primrec ownTableFn := by
  have hLP : Primrec fun a : ℕ => a.unpair.1 := Primrec.fst.comp Primrec.unpair
  have hdecL : Primrec fun a : ℕ =>
      (Encodable.decode (α := List ℕ) a.unpair.1.unpair.1).getD [] :=
    Primrec.option_getD.comp
      (Primrec.decode.comp (Primrec.fst.comp (Primrec.unpair.comp hLP))) (Primrec.const [])
  have hdecP : Primrec fun a : ℕ =>
      (Encodable.decode (α := List ℕ) a.unpair.1.unpair.2).getD [] :=
    Primrec.option_getD.comp
      (Primrec.decode.comp (Primrec.snd.comp (Primrec.unpair.comp hLP))) (Primrec.const [])
  have hT : Primrec fun a : ℕ => a.unpair.2 := Primrec.snd.comp Primrec.unpair
  exact Primrec.encode.comp
    (primrec_ownIter.comp (Primrec.pair hdecP hdecL) hT)

theorem partrec_ownTableFn : Nat.Partrec (fun a : ℕ => (ownTableFn a : ℕ)) :=
  _root_.Partrec.nat_iff.mp (Primrec.to_comp primrec_ownTableFn).partrec

/-- **The fixed iterate-compose builder code.** One program, independent of the world, the reading,
and `n` — the whole `c₀` of `ownership` below. -/
noncomputable def ownBuilder : Nat.Partrec.Code :=
  Classical.choose (Nat.Partrec.Code.exists_code.mp partrec_ownTableFn)

/-- The builder's evaluation law. -/
theorem eval_ownBuilder (a : ℕ) :
    Nat.Partrec.Code.eval ownBuilder a = Part.some (ownTableFn a) := by
  have h := congrFun (Classical.choose_spec
    (Nat.Partrec.Code.exists_code.mp partrec_ownTableFn)) a
  simpa [ownBuilder] using h

/-- A lens table decodes back to itself. -/
theorem decode_lensCode (ℓ : Fin n → Fin m) :
    (Encodable.decode (α := List ℕ) (lensCode ℓ)).getD [] = lensTable ℓ := by
  rw [lensCode, Encodable.encodek]; rfl

/-- **The builder is correct**: on `⟨⟨ℓ₀'s table, U's table⟩, t⟩` it outputs frame `t`'s encoded
tabulation. -/
theorem ownTableFn_eq (U : Perm (Fin n)) (ℓ₀ : Fin n → Fin m) (t : ℕ) :
    ownTableFn (Nat.pair (Nat.pair (lensCode ℓ₀) (lensCode ⇑U)) t)
      = lensCode ((U ^ t) • ℓ₀) := by
  rw [ownTableFn]
  simp only [Nat.unpair_pair, decode_lensCode]
  rw [ownIter_lensTable]
  rfl

/-- **The ownership construction**, after [Persistence] §8, Proposition 8.1. Given a code for the
reading's table and a code for the *world's* table, the canonical family `ℓ t = ℓ₀ ∘ (U ^ t)⁻¹` is
**owned** at `elen cℓ + elen cU + c₀`, with the absolute constant
`c₀ = elen ownBuilder + 30` — one fixed builder plus the assembly's opcodes, independent of the
world, the reading, and `n`.

The assembled program is `comp ownBuilder (pair (pair (comp cℓ zero) (comp cU zero)) id)`: on input
`t` it runs the two given codes to recover the tables, hands them to the builder together with `t`,
and the builder transports the reading `t` steps along the world.

The rent/own contrast is the reason to have this. A renter pays the collapse's floor at every frame,
forever. An owner pays `K (ℓ₀) + K (U)` **once** — and since `K (U) ≤ log₂ n ! + O (1)` for every
world whatsoever, owning is never the more expensive option. What makes it *cheap* is a cheap world:
`KE_lcgWorld_le` exhibits one where `elen cU` is `O (log n)`.

Note what is NOT claimed. This is the permutation-setting construction, not Proposition 8.1's own
statement, which is set in the cell-structured world over the recurrent core `Mem_∞` and carries the
transient `U ^ N`; that plumbing is deliberately not built here. And Proposition 8.1's per-frame
`O (log t)` does not appear above because `UniformBudget` does not charge for the clock —
`uniformBudget_frame_cost` is where that cost is recovered, and `CbHu_collapse` is where it is shown
not to help. The bound is in terms of the *given* codes' lengths, not `KE`; the two coincide when
the codes are `KE`-optimal, which is how `CbHu_ge_lcg` consumes it. -/
theorem ownership {U : Perm (Fin n)} {ℓ₀ : Fin n → Fin m} (cℓ cU : Nat.Partrec.Code)
    (hℓ : cℓ.eval 0 = Part.some (lensCode ℓ₀))
    (hU : cU.eval 0 = Part.some (lensCode ⇑U)) :
    UniformBudget (fun t => (U ^ t) • ℓ₀) (elen cℓ + elen cU + (elen ownBuilder + 30)) := by
  classical
  refine ⟨Nat.Partrec.Code.comp ownBuilder
    (Nat.Partrec.Code.pair
      (Nat.Partrec.Code.pair (Nat.Partrec.Code.comp cℓ Nat.Partrec.Code.zero)
        (Nat.Partrec.Code.comp cU Nat.Partrec.Code.zero))
      Nat.Partrec.Code.id), ?_, ?_⟩
  · have hz : elen Nat.Partrec.Code.zero = 3 := rfl
    have hid : elen Nat.Partrec.Code.id = 9 := rfl
    simp only [E_len_comp, E_len_pair, hz, hid]
    omega
  · intro t
    have hz : Nat.Partrec.Code.eval Nat.Partrec.Code.zero t = Part.some 0 := rfl
    have hcl : Nat.Partrec.Code.eval (Nat.Partrec.Code.comp cℓ Nat.Partrec.Code.zero) t
        = Part.some (lensCode ℓ₀) := (eval_comp_some hz).trans hℓ
    have hcu : Nat.Partrec.Code.eval (Nat.Partrec.Code.comp cU Nat.Partrec.Code.zero) t
        = Part.some (lensCode ⇑U) := (eval_comp_some hz).trans hU
    have hp1 : Nat.Partrec.Code.eval
        (Nat.Partrec.Code.pair (Nat.Partrec.Code.comp cℓ Nat.Partrec.Code.zero)
          (Nat.Partrec.Code.comp cU Nat.Partrec.Code.zero)) t
        = Part.some (Nat.pair (lensCode ℓ₀) (lensCode ⇑U)) := by
      change Nat.pair <$> _ <*> _ = _
      rw [hcl, hcu]; simp [Seq.seq]
    have hp2 : Nat.Partrec.Code.eval
        (Nat.Partrec.Code.pair
          (Nat.Partrec.Code.pair (Nat.Partrec.Code.comp cℓ Nat.Partrec.Code.zero)
            (Nat.Partrec.Code.comp cU Nat.Partrec.Code.zero))
          Nat.Partrec.Code.id) t
        = Part.some (Nat.pair (Nat.pair (lensCode ℓ₀) (lensCode ⇑U)) t) := by
      change Nat.pair <$> _ <*> _ = _
      rw [hp1, Nat.Partrec.Code.eval_id]; simp [Seq.seq]
    rw [eval_comp_some hp2, eval_ownBuilder, ownTableFn_eq]

/-! ## The multiplicative congruential world: cheap dynamics, exhibited

[Persistence] §8, Proposition 8.3 names the **(CD) cheap-dynamics** regime — `K (U|core)` of order
`b + log n` — and shows it is exactly where a world's readings admit cheap generation. §8's
discussion exhibits (CD) by *rotation*. Here is the other textbook example, and a more instructive
one: `x ↦ a · x mod m`, the division-remainder pseudo-random generator.

The point of the example is the gap between how a world *looks* and what it *costs*. The orbit of a
seed under `x ↦ a · x mod m` is the output of a pseudo-random generator: it passes for random at any
horizon short of the period, and an observer watching it sees no order at all. Yet the rule is two
numbers. `KE_lcgWorld_le` prices the whole world at `O (Nat.size a + Nat.size m)` bits — `O (log m)`
— with explicit absolute constants: however chaotic the *view*, the world is (CD), and every
[Persistence] §8 conclusion about kind worlds applies to it.

That is the honest form of "order appears from chaos" in this framework: nothing about the world
changes. What changes is whether an observer can afford the rule. -/

/-- **The multiplicative congruential world** `x ↦ a · x mod m` — the textbook division-remainder
pseudo-random generator — as a permutation of `Fin m`. Coprimality of `a` and `m` is what makes the
map injective, hence (on a finite type) bijective: `a · x ≡ a · y` cancels to `x ≡ y` exactly when
`a` is invertible mod `m`. -/
noncomputable def lcgWorld (a m : ℕ) (h : Nat.Coprime a m) : Perm (Fin m) :=
  Equiv.ofBijective
    (fun x : Fin m => ⟨a * (x : ℕ) % m, Nat.mod_lt _ ((Nat.zero_le _).trans_lt x.isLt)⟩)
    (Finite.injective_iff_bijective.mp (by
      intro x y hxy
      have h1 : a * (x : ℕ) % m = a * (y : ℕ) % m := congrArg Fin.val hxy
      have h3 : (x : ℕ) % m = (y : ℕ) % m := Nat.ModEq.cancel_left_of_coprime h.symm h1
      rw [Nat.mod_eq_of_lt x.isLt, Nat.mod_eq_of_lt y.isLt] at h3
      exact Fin.ext h3))

/-- The world's rule, read off: the state `x` steps to `a · x mod m`. -/
@[simp] theorem lcgWorld_apply (a m : ℕ) (h : Nat.Coprime a m) (x : Fin m) :
    ((lcgWorld a m h x : Fin m) : ℕ) = a * (x : ℕ) % m := rfl

/-- **The world's table, rebuilt from the packed rule `⟨a, m⟩`** — ONE fixed function of a single
natural number, carrying no dependence on `a` or `m`: tabulate `i ↦ a · i mod m` over `List.range m`
by plain digit arithmetic. This is the `markBuilder` idiom, and the source of the `O (1)` in the
price below. -/
def lcgTableFn (p : ℕ) : ℕ :=
  Encodable.encode ((List.range p.unpair.2).map fun i => p.unpair.1 * i % p.unpair.2)

/-- **The builder is primitive recursive.** The table is a `List.map` of one multiplication and one
remainder over `List.range m`. -/
theorem primrec_lcgTableFn : Primrec lcgTableFn := by
  have hA : Primrec fun p : ℕ => p.unpair.1 := Primrec.fst.comp Primrec.unpair
  have hM : Primrec fun p : ℕ => p.unpair.2 := Primrec.snd.comp Primrec.unpair
  have hinner : Primrec₂ fun (p : ℕ) (i : ℕ) => p.unpair.1 * i % p.unpair.2 :=
    (Primrec.nat_mod.comp
      (Primrec.nat_mul.comp (hA.comp Primrec.fst) Primrec.snd)
      (hM.comp Primrec.fst)).to₂
  exact Primrec.encode.comp (Primrec.list_map (Primrec.list_range.comp hM) hinner)

/-- **The builder is correct**: on the packed rule `⟨a, m⟩` it outputs exactly the world's encoded
tabulation — the very number whose `KE` is the world's price. -/
theorem lcgTableFn_eq (a m : ℕ) (h : Nat.Coprime a m) :
    lcgTableFn (Nat.pair a m) = lensCode ⇑(lcgWorld a m h) := by
  rw [lcgTableFn, lensCode, lensTable]
  simp only [Nat.unpair_pair]
  congr 1
  have hfr : (List.finRange m).map Fin.val = List.range m := by simp
  rw [← hfr, List.map_map]
  exact List.map_congr_left fun i _ => (lcgWorld_apply a m h i).symm

theorem partrec_lcgTableFn : Nat.Partrec (fun p : ℕ => (lcgTableFn p : ℕ)) :=
  _root_.Partrec.nat_iff.mp (Primrec.to_comp primrec_lcgTableFn).partrec

/-- **The fixed congruential-world builder code.** One program, independent of `a` and `m`. -/
noncomputable def lcgBuilder : Nat.Partrec.Code :=
  Classical.choose (Nat.Partrec.Code.exists_code.mp partrec_lcgTableFn)

/-- The builder's evaluation law. -/
theorem eval_lcgBuilder (p : ℕ) :
    Nat.Partrec.Code.eval lcgBuilder p = Part.some (lcgTableFn p) := by
  have h := congrFun (Classical.choose_spec
    (Nat.Partrec.Code.exists_code.mp partrec_lcgTableFn)) p
  simpa [lcgBuilder] using h

/-- **The congruential world is cheap** — an explicit `(CD)` witness ([Persistence] §8, Proposition
8.3's cheap-dynamics condition). The whole world `x ↦ a · x mod m` is described in
`2 · κ · (Nat.size a + Nat.size m) + O (1)` bits, with `κ = 15 + elen dbl` and the additive constant
`elen lcgBuilder + 3 · κ + 3` — both absolute, fixed once and for all, independent of `a` and `m`.
Since `Nat.size a` and `Nat.size m` are the bit-lengths, this is `O (log m)` for `a < m`.

Assembly: `comp lcgBuilder (bconst ⟨a, m⟩)`. The rule rides in a pair of numerals, `Nat.pair` costs
a constant factor (`size_pair_le`), `bconst` loads it in `O (Nat.size p)` rather than `Θ (p)`
(`elen_bconst_le`), and `invariance_general` charges the fixed builder once.

The contrast with [Persistence] §8's incompressible `n`-cycle is the whole content: *most* worlds
cost `Θ (n log n)` to describe (the counting argument of Proposition 8.3), and this one — whose
orbits are what a pseudo-random generator emits — costs `O (log m)`. Locally random, globally a
two-number rule. -/
theorem KE_lcgWorld_le (a m : ℕ) (h : Nat.Coprime a m) :
    KE (lensCode ⇑(lcgWorld a m h))
      ≤ 2 * (15 + elen dbl) * (Nat.size a + Nat.size m)
        + (elen lcgBuilder + 3 * (15 + elen dbl) + 3) := by
  have heval : Nat.Partrec.Code.eval lcgBuilder (Nat.pair a m)
      = Part.some (lensCode ⇑(lcgWorld a m h)) := by
    rw [eval_lcgBuilder, lcgTableFn_eq]
  have hinv := invariance_general lcgBuilder (Nat.pair a m) _ heval
  have hkey : (15 + elen dbl) * Nat.size (Nat.pair a m)
      ≤ 2 * (15 + elen dbl) * (Nat.size a + Nat.size m) + 2 * (15 + elen dbl) := by
    calc (15 + elen dbl) * Nat.size (Nat.pair a m)
        ≤ (15 + elen dbl) * (2 * (Nat.size a + Nat.size m) + 2) :=
          Nat.mul_le_mul_left _ (size_pair_le a m)
      _ = 2 * (15 + elen dbl) * (Nat.size a + Nat.size m) + 2 * (15 + elen dbl) := by ring
  calc KE (lensCode ⇑(lcgWorld a m h))
      ≤ elen lcgBuilder + (15 + elen dbl) * Nat.size (Nat.pair a m)
          + (3 + (15 + elen dbl)) := hinv
    _ ≤ elen lcgBuilder + (2 * (15 + elen dbl) * (Nat.size a + Nat.size m) + 2 * (15 + elen dbl))
          + (3 + (15 + elen dbl)) := Nat.add_le_add_right (Nat.add_le_add_left hkey _) _
    _ = 2 * (15 + elen dbl) * (Nat.size a + Nat.size m)
          + (elen lcgBuilder + 3 * (15 + elen dbl) + 3) := by ring

/-- **Ownership over a cheap world: every reading, affordable forever.** The showcase corollary —
`ownership` run over `lcgWorld`, with the world's price discharged by `KE_lcgWorld_le`.

Over the congruential world `x ↦ a · x mod m`, an owner holding `O (log m)` bits for the *rule* and
`KE (lensCode ℓ₀)` bits for its *reading* owns the whole family `ℓ t = ℓ₀ ∘ (U ^ t)⁻¹` — and its
uniform entropic capacity reaches `ℓ₀`'s full relabelling class, the entropy of the reference frame
in its entirety. The `O (1)` is `elen lcgBuilder + elen ownBuilder + 3 · κ + 33`, absolute.

Compare what a renter pays. `CbHu_collapse` says an owner is capped like everybody else at
`Θ (b)` — but here `b` is `KE (lensCode ℓ₀) + O (log m)`, so the *world* is nearly free and the
observer's whole budget goes on its reading. That is the (CD) regime's content, exhibited on the
textbook pseudo-random generator: the orbits look like noise at every horizon short of the period,
and the rule costs two numbers. -/
theorem CbHu_ge_lcg {a m : ℕ} (h : Nat.Coprime a m) {k : ℕ} {ℓ₀ : Fin m → Fin k}
    (hsurj : Function.Surjective ℓ₀) {b : ℕ}
    (hb : 2 * (15 + elen dbl) * (Nat.size a + Nat.size m) + KE (lensCode ℓ₀)
        + (elen lcgBuilder + elen ownBuilder + 3 * (15 + elen dbl) + 33) ≤ b) :
    Nat.card ↥(orbit (Perm (Fin m)) ℓ₀) ≤ CbHu (lcgWorld a m h) b := by
  -- the world's own code: the fixed builder loaded with the packed rule `⟨a, m⟩`
  have hcU : Nat.Partrec.Code.eval
      (Nat.Partrec.Code.comp lcgBuilder (bconst (Nat.pair a m))) 0
      = Part.some (lensCode ⇑(lcgWorld a m h)) := by
    rw [eval_comp_some (eval_bconst (Nat.pair a m) 0), eval_lcgBuilder, lcgTableFn_eq]
  have hown := ownership (U := lcgWorld a m h) (ℓ₀ := ℓ₀) (minCode (lensCode ℓ₀))
    (Nat.Partrec.Code.comp lcgBuilder (bconst (Nat.pair a m)))
    (minCode_computes (lensCode ℓ₀)) hcU
  -- the assembled owner fits the budget
  have hlen : elen (minCode (lensCode ℓ₀))
      + elen (Nat.Partrec.Code.comp lcgBuilder (bconst (Nat.pair a m)))
      + (elen ownBuilder + 30) ≤ b := by
    refine le_trans ?_ hb
    rw [E_len_comp, elen_minCode]
    have hbc : elen (bconst (Nat.pair a m))
        ≤ 2 * (15 + elen dbl) * (Nat.size a + Nat.size m) + 3 * (15 + elen dbl) := by
      refine le_trans (elen_bconst_le (Nat.pair a m)) ?_
      have hkey : (15 + elen dbl) * Nat.size (Nat.pair a m)
          ≤ 2 * (15 + elen dbl) * (Nat.size a + Nat.size m) + 2 * (15 + elen dbl) := by
        calc (15 + elen dbl) * Nat.size (Nat.pair a m)
            ≤ (15 + elen dbl) * (2 * (Nat.size a + Nat.size m) + 2) :=
              Nat.mul_le_mul_left _ (size_pair_le a m)
          _ = 2 * (15 + elen dbl) * (Nat.size a + Nat.size m) + 2 * (15 + elen dbl) := by ring
      omega
    omega
  have hmem : Nat.card ↥(orbit (Perm (Fin m)) ℓ₀)
      ∈ UniformBudgetedEntropies (lcgWorld a m h) b :=
    ⟨k, fun t => ((lcgWorld a m h) ^ t) • ℓ₀, permCarries_smul hsurj, hown.mono hlen, by simp⟩
  exact le_csSup (bddAbove_uniformBudgetedEntropies _ b) hmem

/-! ## Faithful self-reading is priced at the world's rule

A reading is **faithful** when its reference frame is bijective: the observer resolves every state
of the world, losing nothing. This section prices exactly that, in both directions, and finds the
world's own rule on both sides of the ledger.

**Owning** (`faithful_ownership`): a code for the world's table `⇑U` — and nothing else — buys the
faithful family `ℓ t = (U ^ t) • id` outright, at `elen cU + O (1)`. The identity frame needs no
description of its own: the world's table *is* a list of length `n`, so one fixed builder reads `n`
off it and tabulates `[0, …, n − 1]` for free. This is `ownership` at `ℓ₀ = id`, with the reading's
price collapsed to a constant.

**Extraction** (`faithful_rule_cost`): conversely, any faithful family owned at budget `b` *hands
back* the world's rule, `KE (lensCode ⇑U) ≤ 2 · b + O (1)`. The owner's own program, run at `0` and
at `1`, is a description of the two frames the ledger consumes; `ℓ 0` bijective makes `ℓ 1`
injective, so the ledger's table inversion (`invcomp`, `idx`) reads `U = ℓ₁⁻¹ ∘ ℓ₀` straight off
them. The factor two is the code appearing twice in the assembly, and it is inherent to this route:
no self-interpreter is chased to remove it.

Together the two bound the least faithful budget `b*` by
`(b* ≥) (KE (lensCode ⇑U) − O (1)) / 2` and `b* ≤ KE (lensCode ⇑U) + O (1)`, with **absolute**
constants — no `n`, no world, no reading. What a subsystem can faithfully read of its own world is
priced at the world's rule, to within a factor two.

`CbHu_attains_ceiling` is the capstone: where the rule is affordable, the uniform entropic capacity
is not merely large but *exactly* `n !` — the absolute ceiling of `CbHu_le_factorial`, attained. A
bijective frame has all-singleton fibres, so its relabelling class is the whole symmetric group.

Read against the collapse this is the entire rent/own story in one line. `CbHu_collapse` says an
owner is generically capped at `Θ (b)`, and `log₂ n !` is `Θ (n log n)` — so the worlds meeting the
ceiling here are exactly the exceptional ones, those whose rule is cheap enough to buy. The
congruential world above is one: `KE_lcgWorld_le` prices it at `O (log m)`, so it reads itself
faithfully, forever, out of a logarithmic budget.

Anchors: [Persistence] §5, Definition 5.5 (the uniform budget) and §6 (the ledger, read as the rent
side), over the ownership construction of §8, Proposition 8.1. Both directions are statements of
this development, not of any numbered result there; nothing in [Persistence] is claimed
machine-checked by their presence. -/

/-- The identity frame's table is `[0, …, n − 1]`: reading every state as itself tabulates the
range. -/
theorem lensCode_id : lensCode (id : Fin n → Fin n) = Encodable.encode (List.range n) := by
  rw [lensCode, lensTable]
  congr 1
  simp

/-- **The identity frame, rebuilt from the world's own table** — ONE fixed function of a single
natural number. A table for a world over `Fin n` is a list of length `n`, so its length is the only
input the identity frame's tabulation needs: decode, measure, and tabulate the range. This is why a
faithful reading costs nothing beyond the rule. -/
def idFromTableFn (a : ℕ) : ℕ :=
  Encodable.encode (List.range ((Encodable.decode (α := List ℕ) a).getD []).length)

/-- The rebuild is correct: from *any* frame's table over `Fin n` — the world's own included — it
recovers the identity frame's table. -/
theorem idFromTableFn_eq (ℓ : Fin n → Fin m) :
    idFromTableFn (lensCode ℓ) = lensCode (id : Fin n → Fin n) := by
  rw [idFromTableFn, decode_lensCode, lensCode_id, lensTable]
  simp

theorem primrec_idFromTableFn : Primrec idFromTableFn := by
  have hdec : Primrec fun a : ℕ => (Encodable.decode (α := List ℕ) a).getD [] :=
    Primrec.option_getD.comp Primrec.decode (Primrec.const [])
  exact Primrec.encode.comp (Primrec.list_range.comp (Primrec.list_length.comp hdec))

/-- **The faithful-family builder**: on `⟨the world's table, t⟩` it rebuilds the identity frame from
the world's table and transports it `t` steps along the world. One program, independent of the world
and of `n` — `ownTableFn`'s table transport with the reading supplied for free. -/
def faithTableFn (p : ℕ) : ℕ :=
  ownTableFn (Nat.pair (Nat.pair (idFromTableFn p.unpair.1) p.unpair.1) p.unpair.2)

theorem primrec_faithTableFn : Primrec faithTableFn := by
  have hA : Primrec fun p : ℕ => p.unpair.1 := Primrec.fst.comp Primrec.unpair
  have hT : Primrec fun p : ℕ => p.unpair.2 := Primrec.snd.comp Primrec.unpair
  exact primrec_ownTableFn.comp
    (Primrec₂.natPair.comp
      (Primrec₂.natPair.comp (primrec_idFromTableFn.comp hA) hA) hT)

/-- **The builder is correct**: on `⟨U's table, t⟩` it outputs frame `t` of the faithful family —
the world's own inverse iterate `(U ^ t)⁻¹`, which is what transporting the identity frame `t` steps
*is*. -/
theorem faithTableFn_eq (U : Perm (Fin n)) (t : ℕ) :
    faithTableFn (Nat.pair (lensCode ⇑U) t) = lensCode ⇑((U ^ t)⁻¹) := by
  rw [faithTableFn]
  simp only [Nat.unpair_pair, idFromTableFn_eq]
  rw [ownTableFn_eq U (id : Fin n → Fin n) t]
  rfl

/-- **The faithful family carries a persistent model**, over every permutation world: read the state
`x` at time `t` as the state it came from, `(U ^ t)⁻¹ x`. The persistence identity is then immediate
— `(U ^ t)⁻¹ ((U ^ t) x) = x` — and the reference frame is the identity, which resolves every state.
This is `permCarries_smul` at `ℓ₀ = id`, spelled without the action (see the note on `arrowAction`
above). -/
theorem permCarries_inv (U : Perm (Fin n)) : PermCarries U (fun t => ⇑((U ^ t)⁻¹)) := by
  refine ⟨?_, fun t x => ?_⟩ <;> simp [Function.surjective_id]

/-- The faithful family's reference frame is **bijective**: it is the identity. -/
theorem bijective_faithful_frame (U : Perm (Fin n)) :
    Function.Bijective (⇑((U ^ 0)⁻¹) : Fin n → Fin n) := by
  simp

/-- **An owned family's carried entropy is affordable**: the `le_csSup` step of the uniform
capacity, isolated. Stated at a symbolic label count `k`, which is what keeps its `orbit` the
relabelling one. -/
theorem CbHu_ge_of_uniform {U : Perm (Fin n)} {k b : ℕ} {ℓ : ℕ → Fin n → Fin k}
    (hcar : PermCarries U ℓ) (hbud : UniformBudget ℓ b) :
    Nat.card ↥(orbit (Perm (Fin n)) (ℓ 0)) ≤ CbHu U b :=
  le_csSup (bddAbove_uniformBudgetedEntropies U b) ⟨k, ℓ, hcar, hbud, rfl⟩

theorem partrec_faithTableFn : Nat.Partrec (fun p : ℕ => (faithTableFn p : ℕ)) :=
  _root_.Partrec.nat_iff.mp (Primrec.to_comp primrec_faithTableFn).partrec

/-- **The fixed faithful-family builder code.** One program, independent of everything. -/
noncomputable def faithBuilder : Nat.Partrec.Code :=
  Classical.choose (Nat.Partrec.Code.exists_code.mp partrec_faithTableFn)

/-- The builder's evaluation law. -/
theorem eval_faithBuilder (p : ℕ) :
    Nat.Partrec.Code.eval faithBuilder p = Part.some (faithTableFn p) := by
  have h := congrFun (Classical.choose_spec
    (Nat.Partrec.Code.exists_code.mp partrec_faithTableFn)) p
  simpa [faithBuilder] using h

/-- **Owning a faithful reading costs the rule, and nothing else** (⇐). A code for the world's table
buys a family that carries a persistent model, reads the world *bijectively* — losing no state at
all — and is **owned**: one program of length `elen cU + O (1)` computes every frame. The additive
constant `elen faithBuilder + 21` is absolute — one fixed builder plus the assembly's opcodes,
independent of the world and of `n`.

The assembled program is `comp faithBuilder (pair (comp cU zero) id)`: on input `t` it runs `cU` to
recover the world's table, and hands the builder that table together with `t`. No description of the
*reading* appears anywhere, because none is needed — the identity frame is read off the world's
table's length (`idFromTableFn`).

This is the ownership construction at `ℓ₀ = id` ([Persistence] §8, Proposition 8.1's family in the
§7 permutation setting), and `faithful_rule_cost` is its converse. -/
theorem faithful_ownership {U : Perm (Fin n)} (cU : Nat.Partrec.Code)
    (hU : cU.eval 0 = Part.some (lensCode ⇑U)) :
    ∃ ℓ : ℕ → Fin n → Fin n, PermCarries U ℓ ∧ Function.Bijective (ℓ 0) ∧
      UniformBudget ℓ (elen cU + (elen faithBuilder + 21)) := by
  refine ⟨fun t => ⇑((U ^ t)⁻¹), permCarries_inv U, bijective_faithful_frame U, ?_⟩
  · refine ⟨Nat.Partrec.Code.comp faithBuilder
      (Nat.Partrec.Code.pair (Nat.Partrec.Code.comp cU Nat.Partrec.Code.zero)
        Nat.Partrec.Code.id), ?_, ?_⟩
    · have hz : elen Nat.Partrec.Code.zero = 3 := rfl
      have hid : elen Nat.Partrec.Code.id = 9 := rfl
      simp only [E_len_comp, E_len_pair, hz, hid]
      omega
    · intro t
      have hz : Nat.Partrec.Code.eval Nat.Partrec.Code.zero t = Part.some 0 := rfl
      have hcu : Nat.Partrec.Code.eval (Nat.Partrec.Code.comp cU Nat.Partrec.Code.zero) t
          = Part.some (lensCode ⇑U) := (eval_comp_some hz).trans hU
      have hp : Nat.Partrec.Code.eval
          (Nat.Partrec.Code.pair (Nat.Partrec.Code.comp cU Nat.Partrec.Code.zero)
            Nat.Partrec.Code.id) t
          = Part.some (Nat.pair (lensCode ⇑U) t) := by
        change Nat.pair <$> _ <*> _ = _
        rw [hcu, Nat.Partrec.Code.eval_id]; simp [Seq.seq]
      rw [eval_comp_some hp, eval_faithBuilder, faithTableFn_eq]

/-- **The ledger over a faithful frame**: the world's table is recovered from the family's first two
frames by the fixed invert-and-compose program — the same `invcomp` the general ledger runs on.

`ℓ 1 = ℓ 0 ∘ U⁻¹` (`permCarries_frame_one`) and `ℓ 0` bijective make `ℓ 1` injective, so `U i` is
the *unique* state `ℓ 1` reads as `ℓ 0` reads `i` — and `idx`, table inversion, finds it. -/
theorem invcomp_permFrames {U : Perm (Fin n)} {ℓ : ℕ → Fin n → Fin m}
    (hcar : PermCarries U ℓ) (hbij : Function.Bijective (ℓ 0)) :
    invcomp (Nat.pair (lensCode (ℓ 0)) (lensCode (ℓ 1))) = lensCode ⇑U := by
  set f₀ : Fin n → ℕ := fun i => ((ℓ 0 i : Fin m) : ℕ) with hf₀
  set f₁ : Fin n → ℕ := fun i => ((ℓ 1 i : Fin m) : ℕ) with hf₁
  have h1 : ℓ 1 = ℓ 0 ∘ ⇑U⁻¹ := permCarries_frame_one hcar
  have hinj₁ : Function.Injective f₁ := by
    rw [hf₁]
    intro i j hij
    have hv := Fin.val_injective hij
    rw [h1] at hv
    exact (Equiv.injective U⁻¹) (hbij.1 hv)
  simp only [invcomp, Nat.unpair_pair, lensCode, lensTable, Encodable.encodek, Option.getD_some,
    List.map_map, ← hf₀, ← hf₁]
  refine congrArg Encodable.encode (List.map_congr_left fun i _ => ?_)
  have hstep : f₁ (U i) = f₀ i := by
    have := hcar.2 1 i
    simp only [pow_one] at this
    simp only [hf₀, hf₁, this]
  change idx (f₀ i) ((List.finRange n).map f₁) = ((U i : Fin n) : ℕ)
  rw [← hstep]
  exact idx_map_finRange f₁ hinj₁ (U i)

/-- **A faithful reading hands back the rule** (⇒), the converse of `faithful_ownership`. Any
family that carries a persistent model, reads the world bijectively, and is owned at budget `b`
contains a description of the world itself: `KE (lensCode ⇑U) ≤ 2 · b + O (1)`, with the constant
`elen icode + 3 · κ + 12` absolute (`κ = 15 + elen dbl`).

The assembly is `comp icode (pair (comp c (bconst 0)) (comp c (bconst 1)))`: the owner's single
program `c`, run at the two clock values the ledger needs, feeds the fixed inverter. The **factor
two is the code written twice** — `c` appears at both `t = 0` and `t = 1` — and it is what makes the
characterization exact only to within a factor two. Nothing weaker is available on this route: the
two frames are separate inputs to the inverter, and only a self-interpreter could share the text.

This is the ledger of [Persistence] §6 read against the uniform budget of Definition 5.5: an owner
of a faithful reading does not merely pay the rule's price — it *stores* the rule. -/
theorem faithful_rule_cost {U : Perm (Fin n)} {ℓ : ℕ → Fin n → Fin m} {b : ℕ}
    (hcar : PermCarries U ℓ) (hbij : Function.Bijective (ℓ 0)) (hbud : UniformBudget ℓ b) :
    KE (lensCode ⇑U) ≤ 2 * b + (elen icode + 3 * (15 + elen dbl) + 12) := by
  obtain ⟨c, hlen, heval⟩ := hbud
  have h0 : Nat.Partrec.Code.eval (Nat.Partrec.Code.comp c (bconst 0)) 0
      = Part.some (lensCode (ℓ 0)) := (eval_comp_some (eval_bconst 0 0)).trans (heval 0)
  have h1 : Nat.Partrec.Code.eval (Nat.Partrec.Code.comp c (bconst 1)) 0
      = Part.some (lensCode (ℓ 1)) := (eval_comp_some (eval_bconst 1 0)).trans (heval 1)
  have hp : Nat.Partrec.Code.eval
      (Nat.Partrec.Code.pair (Nat.Partrec.Code.comp c (bconst 0))
        (Nat.Partrec.Code.comp c (bconst 1))) 0
      = Part.some (Nat.pair (lensCode (ℓ 0)) (lensCode (ℓ 1))) := by
    change Nat.pair <$> _ <*> _ = _
    rw [h0, h1]; simp [Seq.seq]
  have hcomp : Computes (Nat.Partrec.Code.comp icode
      (Nat.Partrec.Code.pair (Nat.Partrec.Code.comp c (bconst 0))
        (Nat.Partrec.Code.comp c (bconst 1)))) (lensCode ⇑U) := by
    change Nat.Partrec.Code.eval _ 0 = _
    rw [eval_comp_some hp, eval_icode, invcomp_permFrames hcar hbij]
  have hle := KE_le hcomp
  rw [E_len_comp, E_len_pair, E_len_comp, E_len_comp] at hle
  have hb0 : elen (bconst 0) ≤ 15 + elen dbl := by
    have := elen_bconst_le 0
    simpa using this
  have hb1 : elen (bconst 1) ≤ 2 * (15 + elen dbl) := by
    have := elen_bconst_le 1
    have hs : Nat.size 1 = 1 := rfl
    rw [hs] at this
    omega
  omega

/-- A **faithful** frame's fibres are singletons, so the fibre product of the orbit–stabilizer count
is `1`: a bijective reading has a trivial stabilizer. -/
theorem prod_fiber_bijective {ℓ : Fin n → Fin m} (h : Function.Bijective ℓ) :
    ∏ i : Fin m, (Nat.card {x : Fin n // ℓ x = i})! = 1 := by
  refine Finset.prod_eq_one fun i _ => ?_
  have hone : Nat.card {x : Fin n // ℓ x = i} = 1 := by
    obtain ⟨x, hx, huniq⟩ := h.existsUnique i
    exact Nat.card_eq_one_iff_exists.mpr ⟨⟨x, hx⟩, fun y => Subtype.ext (huniq y y.2)⟩
  rw [hone]
  rfl

/-- **Self-ownership attains the absolute ceiling** — a machine-checked *equality*. If the world's
own table is affordable at all — some code `cU` for `lensCode ⇑U` fitting inside `b` with the
faithful family's absolute constant to spare — then the uniform entropic capacity is **exactly**
`n !`, the ceiling of `CbHu_le_factorial`.

Both directions are needed and both are here: `CbHu_le_factorial` caps every reading at `n !`, and
`faithful_ownership` exhibits a family attaining it — bijective, so its fibres are singletons
(`prod_fiber_bijective`) and its relabelling class is all of `n !` by orbit–stabilizer
(`card_orbit_mul_prod_fiber`).

The reading of the equality is the point. `CbHu_collapse` prices a generic world's owner at
`Θ (b)`, and `log₂ n !` is `Θ (n log n)`: so a world at this ceiling is *exceptional*, and what
makes it exceptional is precisely that its rule is cheap. Everything a subsystem can faithfully read
of its own world is bought, in full, at the price of the world's rule and an absolute constant —
`faithful_rule_cost` is the converse showing nothing cheaper does it. The congruential world
`x ↦ a · x mod m` is the worked instance (`KE_lcgWorld_le`): `O (log m)` bits, every state resolved,
forever. -/
theorem CbHu_attains_ceiling {U : Perm (Fin n)} {b : ℕ} (cU : Nat.Partrec.Code)
    (hU : cU.eval 0 = Part.some (lensCode ⇑U))
    (hb : elen cU + (elen faithBuilder + 21) ≤ b) :
    CbHu U b = n ! := by
  refine le_antisymm (CbHu_le_factorial U b) ?_
  obtain ⟨ℓ, hcar, hbij, hbud⟩ := faithful_ownership (U := U) cU hU
  have hge := CbHu_ge_of_uniform hcar (hbud.mono hb)
  have hcard := card_orbit_mul_prod_fiber (ℓ 0)
  rw [prod_fiber_bijective hbij, Nat.mul_one] at hcard
  exact hcard ▸ hge

/-! ## Capacity out to a horizon

Every capacity above is unbounded-horizon: the persistence identity is demanded at every `t`, and
the budget prices every frame, forever. An observer with a finite life demands less. The objects
below index by a horizon `T` — carry the model, and pay for it, out to time `T` only — and they are
where the uniform (owned) and per-frame (rented) budgets can finally be compared *honestly*.

Why the horizon is the natural setting for that comparison. The exchange rate between the budgets is
`uniformBudget_frame_cost`: an owner's program run at `t` describes frame `t` at `b + O (log t)`.
Truncate at `T` and the clock is bounded — `O (log T)` — and the comparison is immediate
(`CbHu_upTo_le_CbH_upTo`). The horizon is not a technicality here; it is what the `log` is a
function of.

It is *not*, however, the only setting: `CbHu_le_CbH` at the end of this section gives the same
comparison with no horizon at all, at cost `O (log n !)`, because a carried family over a
permutation world repeats with the world's period. The two differ in what the constant depends on —
`T` there, `n` here — and neither is absolute.

What does *not* need a horizon is the collapse. `CbH_upTo_collapse` is `CbH_collapse` with the cap
unchanged, at every `T ≥ 1`, because the counting consumes frames `0` and `1` and nothing else
(`permCarries_frame_one`): the collapse is a horizon-1 statement already, and truncating the object
it speaks about cannot weaken it. A short-lived observer gets no discount for being short-lived.

Anchors: [Persistence] §5, Definition 5.4 and Definition 5.5, read out to a horizon; §7, Theorem 7.3
and Corollary 7.5(i) for the cap. The horizon-indexed objects are this development's; no numbered
result of [Persistence] is claimed machine-checked by their presence. -/

/-- **Carrying a model out to horizon `T`** ([Persistence] §7's `PermCarries`, truncated): the
reference frame still resolves the world (`ℓ 0` surjective), but the persistence identity is
demanded only for `t ≤ T`. Frames past the horizon are unconstrained — the observer is not asked to
outlive its own reading. -/
def PermCarriesUpTo (U : Perm (Fin n)) (ℓ : ℕ → Fin n → Fin m) (T : ℕ) : Prop :=
  Function.Surjective (ℓ 0) ∧ ∀ t ≤ T, ∀ x, ℓ t ((U ^ t) x) = ℓ 0 x

/-- An unbounded-horizon family satisfies every truncation of itself. -/
theorem PermCarries.upTo {U : Perm (Fin n)} {ℓ : ℕ → Fin n → Fin m} (h : PermCarries U ℓ) (T : ℕ) :
    PermCarriesUpTo U ℓ T :=
  ⟨h.1, fun t _ x => h.2 t x⟩

/-- **The per-frame budget out to horizon `T`**: every frame up to `T` is affordable at `b`. -/
def PermBudgetUpTo (ℓ : ℕ → Fin n → Fin m) (b T : ℕ) : Prop := ∀ t ≤ T, KE (lensCode (ℓ t)) ≤ b

/-- **The uniform budget out to horizon `T`**: one program of length at most `b` computes every
frame's table up to `T`. What the program does past the horizon is not asked. -/
def UniformBudgetUpTo (ℓ : ℕ → Fin n → Fin m) (b T : ℕ) : Prop :=
  ∃ c : Nat.Partrec.Code, elen c ≤ b ∧ ∀ t ≤ T, c.eval t = Part.some (lensCode (ℓ t))

theorem UniformBudget.upTo {ℓ : ℕ → Fin n → Fin m} {b : ℕ} (h : UniformBudget ℓ b) (T : ℕ) :
    UniformBudgetUpTo ℓ b T :=
  let ⟨c, hlen, heval⟩ := h
  ⟨c, hlen, fun t _ => heval t⟩

/-- **The ledger survives truncation**: at any horizon `T ≥ 1` the second frame is still determined
by the first and the world (`permCarries_frame_one`'s argument, which reads `t = 1` only). -/
theorem permCarriesUpTo_frame_one {U : Perm (Fin n)} {ℓ : ℕ → Fin n → Fin m} {T : ℕ}
    (h : PermCarriesUpTo U ℓ T) (hT : 1 ≤ T) : ℓ 1 = U • ℓ 0 := by
  funext x
  rw [smul_lens_apply]
  have := h.2 1 hT (U⁻¹ x)
  simpa using this

/-- The **carried entropies affordable at budget `b` out to horizon `T`** — `BudgetedEntropies`
with both conditions truncated. -/
def BudgetedEntropiesUpTo (U : Perm (Fin n)) (b T : ℕ) : Set ℕ :=
  {N : ℕ | ∃ k : ℕ, ∃ ℓ : ℕ → Fin n → Fin k, PermCarriesUpTo U ℓ T ∧ PermBudgetUpTo ℓ b T ∧
      N = Nat.card ↥(orbit (Perm (Fin n)) (ℓ 0))}

/-- **The entropic capacity out to horizon `T`** ([Persistence] §5, Definition 5.4 truncated): the
largest carried entropy of a reference frame whose family carries the model, and pays `b` per frame,
out to time `T`. -/
noncomputable def CbH_upTo (U : Perm (Fin n)) (b T : ℕ) : ℕ := sSup (BudgetedEntropiesUpTo U b T)

/-- The **owner's** carried entropies out to horizon `T`. -/
def UniformBudgetedEntropiesUpTo (U : Perm (Fin n)) (b T : ℕ) : Set ℕ :=
  {N : ℕ | ∃ k : ℕ, ∃ ℓ : ℕ → Fin n → Fin k, PermCarriesUpTo U ℓ T ∧ UniformBudgetUpTo ℓ b T ∧
      N = Nat.card ↥(orbit (Perm (Fin n)) (ℓ 0))}

/-- **The uniform entropic capacity out to horizon `T`** ([Persistence] §5, Definition 5.5
truncated): the capacity of an observer that owns its reading and needs it only until `T`. -/
noncomputable def CbHu_upTo (U : Perm (Fin n)) (b T : ℕ) : ℕ :=
  sSup (UniformBudgetedEntropiesUpTo U b T)

theorem budgetedEntropiesUpTo_le {U : Perm (Fin n)} {b T N : ℕ}
    (h : N ∈ BudgetedEntropiesUpTo U b T) : N ≤ n ! := by
  obtain ⟨k, ℓ, -, -, rfl⟩ := h
  have hprod : 0 < ∏ i : Fin k, (Nat.card {x : Fin n // ℓ 0 x = i})! :=
    Finset.prod_pos fun i _ => Nat.factorial_pos _
  exact card_orbit_mul_prod_fiber (ℓ 0) ▸ Nat.le_mul_of_pos_right _ hprod

theorem bddAbove_budgetedEntropiesUpTo (U : Perm (Fin n)) (b T : ℕ) :
    BddAbove (BudgetedEntropiesUpTo U b T) :=
  ⟨n !, fun _ h => budgetedEntropiesUpTo_le h⟩

theorem uniformBudgetedEntropiesUpTo_le {U : Perm (Fin n)} {b T N : ℕ}
    (h : N ∈ UniformBudgetedEntropiesUpTo U b T) : N ≤ n ! := by
  obtain ⟨k, ℓ, -, -, rfl⟩ := h
  have hprod : 0 < ∏ i : Fin k, (Nat.card {x : Fin n // ℓ 0 x = i})! :=
    Finset.prod_pos fun i _ => Nat.factorial_pos _
  exact card_orbit_mul_prod_fiber (ℓ 0) ▸ Nat.le_mul_of_pos_right _ hprod

theorem bddAbove_uniformBudgetedEntropiesUpTo (U : Perm (Fin n)) (b T : ℕ) :
    BddAbove (UniformBudgetedEntropiesUpTo U b T) :=
  ⟨n !, fun _ h => uniformBudgetedEntropiesUpTo_le h⟩

/-- **No reading distinguishes more than the world has to offer**, at any horizon. -/
theorem CbH_upTo_le_factorial (U : Perm (Fin n)) (b T : ℕ) : CbH_upTo U b T ≤ n ! := by
  rcases Set.eq_empty_or_nonempty (BudgetedEntropiesUpTo U b T) with hemp | hne
  · simp [CbH_upTo, hemp]
  · exact csSup_le hne fun _ h => budgetedEntropiesUpTo_le h

theorem CbHu_upTo_le_factorial (U : Perm (Fin n)) (b T : ℕ) : CbHu_upTo U b T ≤ n ! := by
  rcases Set.eq_empty_or_nonempty (UniformBudgetedEntropiesUpTo U b T) with hemp | hne
  · simp [CbHu_upTo, hemp]
  · exact csSup_le hne fun _ h => uniformBudgetedEntropiesUpTo_le h

/-- **More budget never hurts**, at any horizon. -/
theorem CbH_upTo_mono (U : Perm (Fin n)) (T : ℕ) {b₁ b₂ : ℕ} (h : b₁ ≤ b₂) :
    CbH_upTo U b₁ T ≤ CbH_upTo U b₂ T :=
  csSup_le_csSup' (bddAbove_budgetedEntropiesUpTo U b₂ T) (by
    rintro N ⟨k, ℓ, hcar, hbud, rfl⟩
    exact ⟨k, ℓ, hcar, fun t ht => (hbud t ht).trans h, rfl⟩)

/-- **A longer horizon never helps**: `CbH_upTo` is antitone in `T`. A family carrying the model out
to `T₂` carries it out to every `T₁ ≤ T₂`, and pays for fewer frames doing so — more horizon is
strictly more constraint, never more capacity. -/
theorem CbH_upTo_antitone (U : Perm (Fin n)) (b : ℕ) {T₁ T₂ : ℕ} (h : T₁ ≤ T₂) :
    CbH_upTo U b T₂ ≤ CbH_upTo U b T₁ :=
  csSup_le_csSup' (bddAbove_budgetedEntropiesUpTo U b T₁) (by
    rintro N ⟨k, ℓ, hcar, hbud, rfl⟩
    exact ⟨k, ℓ, ⟨hcar.1, fun t ht => hcar.2 t (ht.trans h)⟩,
      fun t ht => hbud t (ht.trans h), rfl⟩)

/-- The owner's capacity is antitone in the horizon too. -/
theorem CbHu_upTo_antitone (U : Perm (Fin n)) (b : ℕ) {T₁ T₂ : ℕ} (h : T₁ ≤ T₂) :
    CbHu_upTo U b T₂ ≤ CbHu_upTo U b T₁ :=
  csSup_le_csSup' (bddAbove_uniformBudgetedEntropiesUpTo U b T₁) (by
    rintro N ⟨k, ℓ, hcar, hbud, rfl⟩
    obtain ⟨c, hlen, heval⟩ := hbud
    exact ⟨k, ℓ, ⟨hcar.1, fun t ht => hcar.2 t (ht.trans h)⟩,
      ⟨c, hlen, fun t ht => heval t (ht.trans h)⟩, rfl⟩)

/-- **The unbounded-horizon capacity is below every truncation** — the full object satisfies every
truncation of itself, so nothing is lost by asking less. -/
theorem CbH_le_CbH_upTo (U : Perm (Fin n)) (b T : ℕ) : CbH U b ≤ CbH_upTo U b T :=
  csSup_le_csSup' (bddAbove_budgetedEntropiesUpTo U b T) (by
    rintro N ⟨k, ℓ, hcar, hbud, rfl⟩
    exact ⟨k, ℓ, hcar.upTo T, fun t _ => hbud t, rfl⟩)

/-- The same for an owner. -/
theorem CbHu_le_CbHu_upTo (U : Perm (Fin n)) (b T : ℕ) : CbHu U b ≤ CbHu_upTo U b T :=
  csSup_le_csSup' (bddAbove_uniformBudgetedEntropiesUpTo U b T) (by
    rintro N ⟨k, ℓ, hcar, hbud, rfl⟩
    exact ⟨k, ℓ, hcar.upTo T, hbud.upTo T, rfl⟩)

/-- **The collapse does not care about the horizon** ([Persistence] §7, Corollary 7.5(i)'s cap, out
to `T`). For every `d` and every horizon `T ≥ 1`, the worlds whose entropic capacity *out to `T`* at
budget `b` exceeds `2 * b + d + 2` number at most `n ! / 2 ^ d` — the **same** cap as
`CbH_collapse`, with nothing given away for the shorter life.

The reason is structural. The counting consumes frames `0` and `1` and no others: `ℓ 1` is
determined by `ℓ 0` and the world (`permCarriesUpTo_frame_one`), and the budget is read at those two
frames alone. So `CbH_collapse` was *already* a horizon-1 statement, and truncating the capacity
object it bounds cannot weaken it. An observer that only needs its reading until tomorrow pays the
same generic price as one that needs it forever. -/
theorem CbH_upTo_collapse (b d : ℕ) {T : ℕ} (hT : 1 ≤ T) :
    {U : Perm (Fin n) | 2 ^ (2 * b + d + 2) < CbH_upTo U b T}.ncard * 2 ^ d ≤ n ! := by
  refine le_trans (Nat.mul_le_mul_right _ (Set.ncard_le_ncard ?_ (Set.toFinite _)))
    (collapse_union d)
  intro U hU
  have hlt : 2 ^ (2 * b + d + 2) < CbH_upTo U b T := hU
  have hne : (BudgetedEntropiesUpTo U b T).Nonempty := by
    by_contra hcon
    rw [Set.not_nonempty_iff_eq_empty] at hcon
    rw [CbH_upTo, hcon, csSup_empty] at hlt
    exact absurd hlt (Nat.not_lt_zero _)
  obtain ⟨k, ℓ, hcar, hbud, hval⟩ : CbH_upTo U b T ∈ BudgetedEntropiesUpTo U b T :=
    Nat.sSup_mem hne (bddAbove_budgetedEntropiesUpTo U b T)
  refine ⟨k, ℓ 0, hcar.1, ?_⟩
  have h1 : ℓ 1 = U • ℓ 0 := permCarriesUpTo_frame_one hcar hT
  have hb0 := hbud 0 (Nat.zero_le _)
  have hb1 := hbud 1 hT
  rw [h1, show U • ℓ 0 = ℓ 0 ∘ ⇑U⁻¹ from rfl] at hb1
  calc 2 ^ (KE (lensCode (ℓ 0)) + KE (lensCode (ℓ 0 ∘ ⇑U⁻¹)) + d + 2)
      ≤ 2 ^ (2 * b + d + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
    _ < Nat.card ↥(orbit (Perm (Fin n)) (ℓ 0)) := hval ▸ hlt

/-- **The frame-cost reduction, out to a horizon**: an owner's program prices every frame it is
asked about at `b + O (log T)` — the clock is read at `t ≤ T`, so `Nat.size t ≤ Nat.size T` bounds
it uniformly over the frames in question. -/
theorem uniformBudgetUpTo_frame_cost {ℓ : ℕ → Fin n → Fin m} {b T : ℕ}
    (h : UniformBudgetUpTo ℓ b T) {t : ℕ} (ht : t ≤ T) :
    KE (lensCode (ℓ t)) ≤ b + (15 + elen dbl) * Nat.size T + (3 + (15 + elen dbl)) := by
  obtain ⟨c, hlen, heval⟩ := h
  have hinv := invariance_general c t (lensCode (ℓ t)) (heval t ht)
  have hsize : Nat.size t ≤ Nat.size T := Nat.size_le_size ht
  have hmul := Nat.mul_le_mul_left (15 + elen dbl) hsize
  omega

/-- **Owning buys at most the clock** — the true uniform-versus-per-frame comparison, and the reason
it must be horizon-indexed.

Out to horizon `T`, an owner at budget `b` carries no more entropy than a renter at
`b + O (log T)`: the owner's program, run at each `t ≤ T`, *is* a per-frame description, costing the
program plus the clock (`uniformBudgetUpTo_frame_cost`), and `t ≤ T` bounds the clock at
`κ · Nat.size T` with `κ = 15 + elen dbl` absolute.

What the horizon buys is a constant that does not grow with `n`. Dropping it entirely still leaves a
comparison — `CbHu_le_CbH`, at `O (log n !)`, over the frames' period — but no route gives an
**absolute** constant here. The statement that *is* absolute is the collapse (`CbHu_collapse`),
which needs only frames `0` and `1`, whose clocks are constants.

So the ledger of renting versus owning reads: owning is amortization worth exactly the clock, and
the clock is worth `O (log T)`. It buys no entropy the renter cannot have for `O (log T)` more
bits — and, generically, `CbH_upTo_collapse` caps them both at `Θ (b)` anyway. -/
theorem CbHu_upTo_le_CbH_upTo (U : Perm (Fin n)) (b T : ℕ) :
    CbHu_upTo U b T ≤ CbH_upTo U (b + (15 + elen dbl) * Nat.size T + (3 + (15 + elen dbl))) T :=
  csSup_le_csSup' (bddAbove_budgetedEntropiesUpTo U _ T) (by
    rintro N ⟨k, ℓ, hcar, hbud, rfl⟩
    exact ⟨k, ℓ, hcar, fun t ht => uniformBudgetUpTo_frame_cost hbud ht, rfl⟩)

/-! ### The horizon runs out: a family over a permutation world repeats

The clock is unbounded in `t`, but the *frames are not*. Over a permutation world the persistence
identity determines every frame from the reference one — `ℓ t = ℓ 0 ∘ (U ^ t)⁻¹` — so the family
inherits the world's own period, and only `orderOf U ≤ n !` distinct frames ever exist. The clock
therefore never has to count past the period: an owner's `O (log t)` is really `O (log orderOf U)`,
which is `O (log n !) = O (n log n)` at worst.

So the uniform-to-per-frame comparison *does* hold with no horizon at all
(`CbHu_le_CbH`) — the cost is a constant in `n`, not an absolute one. This is worth stating
precisely, because "unbounded in `t`" invites the stronger reading that no horizon-free comparison
exists; over these worlds one does. What is genuinely unavailable horizon-free is an **absolute**
constant, independent of `n`: `CbHu_upTo_le_CbH_upTo` pays `O (log T)` and `CbHu_le_CbH` pays
`O (log n !)`, and neither degenerates to `O (1)`. -/

/-- **Every frame is the reference frame, relabelled** — the persistence identity solved for `ℓ t`.
`U ^ t` is invertible, so `ℓ t ∘ U ^ t = ℓ 0` reads as `ℓ t = ℓ 0 ∘ (U ^ t)⁻¹`: over a permutation
world a family carrying a model has no freedom past its reference frame. -/
theorem permCarries_frame_eq {U : Perm (Fin n)} {ℓ : ℕ → Fin n → Fin m} (h : PermCarries U ℓ)
    (t : ℕ) : ℓ t = ℓ 0 ∘ ⇑((U ^ t)⁻¹) := by
  funext y
  have := h.2 t ((U ^ t)⁻¹ y)
  simpa using this

/-- **The family repeats with the world's period**: frame `t` is frame `t % orderOf U`. A carried
family over a permutation world takes only `orderOf U` distinct values, however long it runs. -/
theorem permCarries_frame_mod {U : Perm (Fin n)} {ℓ : ℕ → Fin n → Fin m} (h : PermCarries U ℓ)
    (t : ℕ) : ℓ (t % orderOf U) = ℓ t := by
  rw [permCarries_frame_eq h, permCarries_frame_eq h (t := t), pow_mod_orderOf]

/-- **Owning beats renting by at most the world's period** — the uniform-to-per-frame comparison,
horizon-free after all.

An owner at budget `b` carries no more entropy than a renter at `b + O (log n !)`, with **no horizon
anywhere**: the frames of a carried family repeat with the world's period (`permCarries_frame_mod`),
so the owner's program never needs its clock past `orderOf U ≤ n !`, and the `O (log t)` of
`uniformBudget_frame_cost` is really `O (log orderOf U)`.

The constant `κ · Nat.size (n !) + (3 + κ)` depends on `n` and on nothing else — not the world, not
the reading, not the family. That dependence is the whole difference between this and
`CbHu_upTo_le_CbH_upTo`, which pays `O (log T)` for a horizon `T` that may be far below the period.
What no route gives is an **absolute** constant: over an unbounded horizon the clock genuinely must
count to the period, and `log n !` is `Θ (n log n)`.

Set against `CbHu_collapse`, whose cap *is* absolute in exactly this sense, the shape of the
rent/own ledger is complete: owning never escapes the generic ceiling, and it never buys more than
the
clock. -/
theorem CbHu_le_CbH (U : Perm (Fin n)) (b : ℕ) :
    CbHu U b ≤ CbH U (b + (15 + elen dbl) * Nat.size (n !) + (3 + (15 + elen dbl))) := by
  refine csSup_le_csSup' (bddAbove_budgetedEntropies U _) ?_
  rintro N ⟨k, ℓ, hcar, hbud, rfl⟩
  refine ⟨k, ℓ, hcar, fun t => ?_, rfl⟩
  rw [← permCarries_frame_mod hcar t]
  have hc := uniformBudget_frame_cost hbud (t % orderOf U)
  have hpos : 0 < orderOf U := orderOf_pos U
  have hcard : orderOf U ≤ n ! := by
    have h := orderOf_le_card_univ (x := U)
    rwa [Fintype.card_perm, Fintype.card_fin] at h
  have hsize : Nat.size (t % orderOf U) ≤ Nat.size (n !) :=
    Nat.size_le_size (le_trans (Nat.le_of_lt (Nat.mod_lt _ hpos)) hcard)
  have hmul := Nat.mul_le_mul_left (15 + elen dbl) hsize
  omega

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
theorem unionWorld_pow_left {n₁ n₂ : ℕ} (U₁ : Perm (Fin n₁)) (U₂ : Perm (Fin n₂)) (t : ℕ)
    (i : Fin n₁) : ((unionWorld U₁ U₂) ^ t) (Fin.castAdd n₂ i) = Fin.castAdd n₂ ((U₁ ^ t) i) := by
  induction t generalizing i with
  | zero => simp
  | succ t ih => rw [pow_succ, pow_succ]; simp [Equiv.Perm.mul_apply, ih]

theorem unionWorld_pow_right {n₁ n₂ : ℕ} (U₁ : Perm (Fin n₁)) (U₂ : Perm (Fin n₂)) (t : ℕ)
    (j : Fin n₂) : ((unionWorld U₁ U₂) ^ t) (Fin.natAdd n₁ j) = Fin.natAdd n₁ ((U₂ ^ t) j) := by
  induction t generalizing j with
  | zero => simp
  | succ t ih => rw [pow_succ, pow_succ]; simp [Equiv.Perm.mul_apply, ih]

/-- **Two tables, concatenated with the second block's entries shifted.** The shared shape of both
builders below: for the world the shift is the first table's own length, for a lens it is the first
block's label count. -/
def shiftAppend (T₁ T₂ : List ℕ) (s : ℕ) : List ℕ := T₁ ++ T₂.map (fun v => s + v)

theorem primrec_shiftAppend :
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

theorem primrec_unionTableFn : Primrec unionTableFn := by
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

theorem partrec_unionTableFn : Nat.Partrec (fun p : ℕ => (unionTableFn p : ℕ)) :=
  _root_.Partrec.nat_iff.mp (Primrec.to_comp primrec_unionTableFn).partrec

/-- **The fixed union-world builder code.** -/
noncomputable def unionBuilder : Nat.Partrec.Code :=
  Classical.choose (Nat.Partrec.Code.exists_code.mp partrec_unionTableFn)

theorem eval_unionBuilder (p : ℕ) :
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
def unionLensTableFn (p : ℕ) : ℕ :=
  Encodable.encode
    (shiftAppend ((Encodable.decode (α := List ℕ) p.unpair.1.unpair.1).getD [])
      ((Encodable.decode (α := List ℕ) p.unpair.1.unpair.2).getD []) p.unpair.2)

theorem primrec_unionLensTableFn : Primrec unionLensTableFn := by
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
theorem lensTable_unionLens {n₁ n₂ k₁ k₂ : ℕ} (ℓ₁ : ℕ → Fin n₁ → Fin k₁)
    (ℓ₂ : ℕ → Fin n₂ → Fin k₂) (t : ℕ) :
    lensTable (unionLens ℓ₁ ℓ₂ t) = shiftAppend (lensTable (ℓ₁ t)) (lensTable (ℓ₂ t)) k₁ := by
  have hfun : (fun x : Fin (n₁ + n₂) => ((unionLens ℓ₁ ℓ₂ t x : Fin (k₁ + k₂)) : ℕ))
      = Fin.append (fun i => ((ℓ₁ t i : Fin k₁) : ℕ)) (fun j => k₁ + ((ℓ₂ t j : Fin k₂) : ℕ)) := by
    funext x
    refine Fin.addCases (fun i => ?_) (fun j => ?_) x <;> simp [unionLens]
  rw [shiftAppend, lensTable, lensTable, lensTable, ← List.ofFn_eq_map, ← List.ofFn_eq_map,
    ← List.ofFn_eq_map, List.map_ofFn, hfun, List.ofFn_fin_append]
  rfl

theorem unionLensTableFn_eq {n₁ n₂ k₁ k₂ : ℕ} (ℓ₁ : ℕ → Fin n₁ → Fin k₁)
    (ℓ₂ : ℕ → Fin n₂ → Fin k₂) (t : ℕ) :
    unionLensTableFn (Nat.pair (Nat.pair (lensCode (ℓ₁ t)) (lensCode (ℓ₂ t))) k₁)
      = lensCode (unionLens ℓ₁ ℓ₂ t) := by
  rw [unionLensTableFn]
  simp only [Nat.unpair_pair, decode_lensCode]
  rw [← lensTable_unionLens]
  rfl

theorem partrec_unionLensTableFn : Nat.Partrec (fun p : ℕ => (unionLensTableFn p : ℕ)) :=
  _root_.Partrec.nat_iff.mp (Primrec.to_comp primrec_unionLensTableFn).partrec

/-- **The fixed block-pair-lens builder code.** -/
noncomputable def unionLensBuilder : Nat.Partrec.Code :=
  Classical.choose (Nat.Partrec.Code.exists_code.mp partrec_unionLensTableFn)

theorem eval_unionLensBuilder (p : ℕ) :
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
theorem card_fiber_unionLens_left {n₁ n₂ k₁ k₂ : ℕ} (ℓ₁ : ℕ → Fin n₁ → Fin k₁)
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
  haveI hemp :
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
theorem card_fiber_unionLens_right {n₁ n₂ k₁ k₂ : ℕ} (ℓ₁ : ℕ → Fin n₁ → Fin k₁)
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
  haveI hemp :
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
    refine (uniformBudget_unionLens hbud₁ hbud₂).mono ?_
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

theorem subPerm_pow_apply {U : Perm (Fin n)} {B : Finset (Fin n)} (hB : ∀ i ∈ B, U i ∈ B)
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
a persistent family by `E (ℓ₀)`, the entropy on the **recurrent core**, "the only part of a lens the
persistence identity constrains". So `CbHe` values a family at
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
  simp only [PermCarries, Carries, Equiv.Perm.coe_pow]

/-- **A permutation world is its own recurrent core** ([Persistence] §7's standing simplification,
proved rather than assumed): nothing is transient when nothing is irreversible. -/
theorem core_perm (U : Perm (Fin n)) : core (⇑U) = Set.univ := by
  have h : ∀ t : ℕ, ((⇑U)^[t]) '' Set.univ = (Set.univ : Set (Fin n)) := by
    intro t
    have hs : Function.Surjective ((⇑U)^[t]) := by
      rw [← Equiv.Perm.coe_pow]; exact (U ^ t).surjective
    rw [Set.image_univ, Set.range_eq_univ]
    exact hs
  simp only [core, h, Set.iInter_const]

/-- The core of a permutation world, identified with the world itself. -/
noncomputable def corePermEquiv (U : Perm (Fin n)) : ↥(core (⇑U)) ≃ Fin n :=
  (Equiv.setCongr (core_perm U)).trans (Equiv.Set.univ (Fin n))

/-- **Carried entropy transports along a relabelling of the domain** ([Persistence] §2, Definition
2.2). The entropy of a lens depends on its fibre profile and the size of the set it is read on,
nothing else — so an identification of domains carries it across. This is what lets the core-valued
capacity below be compared with the ambient one over a permutation world.

Proved by the exact count (`card_orbit_mul_prod_fiber_card`) on each side rather than by exhibiting
an equivalence of orbits: the two orbit cardinalities multiply the *same* fibre product to the
*same* factorial, and the fibre product is positive. -/
theorem card_orbit_congr {α β : Type*} [Finite α] (e : α ≃ β) (f : α → Fin m) :
    Nat.card ↥(orbit (Perm α) f) = Nat.card ↥(orbit (Perm β) (f ∘ ⇑e.symm)) := by
  haveI : Finite β := Finite.of_equiv α e
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
theorem coreOrbit_perm (U : Perm (Fin n)) (f : Fin n → Fin m) :
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
theorem budgetedEntropiesE_le {U : Fin n → Fin n} {b N : ℕ} (h : N ∈ BudgetedEntropiesE U b) :
    N ≤ (Nat.card ↥(core U))! := by
  obtain ⟨k, ℓ, -, -, rfl⟩ := h
  have hprod : 0 < ∏ i : Fin k, (Nat.card {x : ↥(core U) // coreLens U (ℓ 0) x = i})! :=
    Finset.prod_pos fun i _ => Nat.factorial_pos _
  exact card_orbit_mul_prod_fiber_card (coreLens U (ℓ 0)) ▸ Nat.le_mul_of_pos_right _ hprod

/-- The uniform variant is bounded for the same reason — the bound is the orbit count and consumes
no budget at all. -/
theorem uniformBudgetedEntropiesE_le {U : Fin n → Fin n} {b N : ℕ}
    (h : N ∈ UniformBudgetedEntropiesE U b) : N ≤ (Nat.card ↥(core U))! := by
  obtain ⟨k, ℓ, -, -, rfl⟩ := h
  have hprod : 0 < ∏ i : Fin k, (Nat.card {x : ↥(core U) // coreLens U (ℓ 0) x = i})! :=
    Finset.prod_pos fun i _ => Nat.factorial_pos _
  exact card_orbit_mul_prod_fiber_card (coreLens U (ℓ 0)) ▸ Nat.le_mul_of_pos_right _ hprod

/-- The recurrent core is part of the world. -/
theorem card_core_le (U : Fin n → Fin n) : Nat.card ↥(core U) ≤ n := by
  have h : Nat.card ↥(core U) ≤ Nat.card (Fin n) :=
    Nat.card_le_card_of_injective _ Subtype.val_injective
  simpa using h

theorem bddAbove_budgetedEntropiesE (U : Fin n → Fin n) (b : ℕ) :
    BddAbove (BudgetedEntropiesE U b) :=
  ⟨(Nat.card ↥(core U))!, fun _ h => budgetedEntropiesE_le h⟩

theorem bddAbove_uniformBudgetedEntropiesE (U : Fin n → Fin n) (b : ℕ) :
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

theorem CbHue_le_core_factorial (U : Fin n → Fin n) (b : ℕ) :
    CbHue U b ≤ (Nat.card ↥(core U))! := by
  rcases Set.eq_empty_or_nonempty (UniformBudgetedEntropiesE U b) with hemp | hne
  · simp [CbHue, hemp]
  · exact csSup_le hne fun _ h => uniformBudgetedEntropiesE_le h

/-- The core cap is below the world cap: `CbHe U b ≤ n !`, the general-world form of
`CbH_le_factorial`. Over a permutation world the two coincide; over an irreversible one the core
factorial is the sharper statement, and it is the one [Persistence] §3 predicts. -/
theorem CbHe_le_factorial (U : Fin n → Fin n) (b : ℕ) : CbHe U b ≤ n ! :=
  (CbHe_le_core_factorial U b).trans (Nat.factorial_le (card_core_le U))

theorem CbHue_le_factorial (U : Fin n → Fin n) (b : ℕ) : CbHue U b ≤ n ! :=
  (CbHue_le_core_factorial U b).trans (Nat.factorial_le (card_core_le U))

/-- More budget never hurts. -/
theorem CbHe_mono (U : Fin n → Fin n) {b₁ b₂ : ℕ} (h : b₁ ≤ b₂) : CbHe U b₁ ≤ CbHe U b₂ :=
  csSup_le_csSup' (bddAbove_budgetedEntropiesE U b₂) (by
    rintro N ⟨k, ℓ, hcar, hbud, rfl⟩
    exact ⟨k, ℓ, hcar, fun t => (hbud t).trans h, rfl⟩)

theorem CbHue_mono (U : Fin n → Fin n) {b₁ b₂ : ℕ} (h : b₁ ≤ b₂) : CbHue U b₁ ≤ CbHue U b₂ :=
  csSup_le_csSup' (bddAbove_uniformBudgetedEntropiesE U b₂) (by
    rintro N ⟨k, ℓ, hcar, hbud, rfl⟩
    exact ⟨k, ℓ, hcar, hbud.mono h, rfl⟩)

/-- **The general objects restrict to the §7 ones** — the sanity bridge. Over a permutation world
the carrying predicates agree (`permCarries_iff_carries`) and the core is everything
(`coreOrbit_perm`), so the affordable-entropy sets are literally the same set. -/
theorem budgetedEntropiesE_perm (U : Perm (Fin n)) (b : ℕ) :
    BudgetedEntropiesE (⇑U) b = BudgetedEntropies U b := by
  ext N
  constructor
  · rintro ⟨k, ℓ, hcar, hbud, rfl⟩
    exact ⟨k, ℓ, permCarries_iff_carries.mpr hcar, hbud, coreOrbit_perm U (ℓ 0)⟩
  · rintro ⟨k, ℓ, hcar, hbud, rfl⟩
    exact ⟨k, ℓ, permCarries_iff_carries.mp hcar, hbud, (coreOrbit_perm U (ℓ 0)).symm⟩

theorem uniformBudgetedEntropiesE_perm (U : Perm (Fin n)) (b : ℕ) :
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
def iterTable (T : List ℕ) (τ : ℕ) : List ℕ := (stepComp T)^[τ] (List.range T.length)

/-- Composition of tables tabulates composition of functions. -/
theorem stepComp_lensTable (U V : Fin n → Fin n) :
    stepComp (lensTable U) (lensTable V) = lensTable (U ∘ V) := by
  simp only [stepComp, lensTable, List.map_map]
  refine List.map_congr_left fun i _ => ?_
  exact getD_map_finRange (fun j : Fin n => ((U j : Fin n) : ℕ)) (V i)

/-- Iterated self-composition tabulates the iterate: `τ` steps of `stepComp` against `U`'s own table
turn the identity's table into `U^[τ]`'s. -/
theorem iterTable_lensTable (U : Fin n → Fin n) (τ : ℕ) :
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
def iterTableFn (p : ℕ) : ℕ :=
  Encodable.encode (iterTable ((Encodable.decode (α := List ℕ) p.unpair.1).getD []) p.unpair.2)

theorem primrec_stepComp : Primrec₂ stepComp := by
  have hg : Primrec₂ fun (q : List ℕ × List ℕ) (v : ℕ) => q.1.getD v 0 :=
    ((Primrec.list_getD 0).comp (Primrec.fst.comp Primrec.fst) Primrec.snd).to₂
  exact (Primrec.list_map Primrec.snd hg).to₂

theorem primrec_iterTable : Primrec₂ iterTable := by
  have hg : Primrec₂ fun (T : List ℕ) (p : ℕ × List ℕ) => stepComp T p.2 :=
    (primrec_stepComp.comp Primrec.fst (Primrec.snd.comp Primrec.snd)).to₂
  exact (Primrec.nat_rec (f := fun T : List ℕ => List.range T.length)
    (Primrec.list_range.comp Primrec.list_length) hg).of_eq
    fun T τ => natRec_iterate (stepComp T) (List.range T.length) τ

/-- **The dilation builder is primitive recursive.** Decoding is `Primrec.decode`, composition is a
`List.map`, and the iteration is `Nat.rec`. -/
theorem primrec_iterTableFn : Primrec iterTableFn := by
  have hdecT : Primrec fun p : ℕ => (Encodable.decode (α := List ℕ) p.unpair.1).getD [] :=
    Primrec.option_getD.comp
      (Primrec.decode.comp (Primrec.fst.comp Primrec.unpair)) (Primrec.const [])
  have hτ : Primrec fun p : ℕ => p.unpair.2 := Primrec.snd.comp Primrec.unpair
  exact Primrec.encode.comp (primrec_iterTable.comp hdecT hτ)

theorem partrec_iterTableFn : Nat.Partrec (fun p : ℕ => (iterTableFn p : ℕ)) :=
  _root_.Partrec.nat_iff.mp (Primrec.to_comp primrec_iterTableFn).partrec

/-- **The fixed self-composition builder code.** One program, independent of the world and of
`n`. -/
noncomputable def iterBuilder : Nat.Partrec.Code :=
  Classical.choose (Nat.Partrec.Code.exists_code.mp partrec_iterTableFn)

/-- The builder's evaluation law. -/
theorem eval_iterBuilder (p : ℕ) :
    Nat.Partrec.Code.eval iterBuilder p = Part.some (iterTableFn p) := by
  have h := congrFun (Classical.choose_spec
    (Nat.Partrec.Code.exists_code.mp partrec_iterTableFn)) p
  simpa [iterBuilder] using h

/-- **The builder is correct**: on `⟨U's table, τ⟩` it outputs `U^[τ]`'s encoded tabulation. -/
theorem iterTableFn_eq (U : Fin n → Fin n) (τ : ℕ) :
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
theorem coe_closed {U : Fin n → Fin n} {B : Finset (Fin n)} (hB : ∀ i ∈ B, U i ∈ B) :
    ∀ s ∈ (↑B : Set (Fin n)), U s ∈ (↑B : Set (Fin n)) := fun s hs => hB s hs

/-- **Reading the attractor through the world's own iterate does not change the carried entropy.**
Precomposing with `U^[t]` is, on the attractor, precomposing with a power of `omegaPerm` — a
relabelling — so it lands in the same orbit. This is what makes the value of a settling family
independent of *when* it is read, and it is the engine of both directions of the reduction. -/
theorem orbit_restrict_iterate {U : Fin n → Fin n} {B : Set (Fin n)} (hB : ∀ s ∈ B, U s ∈ B)
    (f : Fin n → Fin m) (t : ℕ) :
    orbit (Perm ↥(omegaLimit U B)) ((omegaLimit U B).restrict (f ∘ U^[t]))
      = orbit (Perm ↥(omegaLimit U B)) ((omegaLimit U B).restrict f) := by
  have h : (omegaLimit U B).restrict (f ∘ U^[t])
      = ((omegaPerm U hB ^ t)⁻¹) • ((omegaLimit U B).restrict f) := by
    funext x
    simp only [smul_lens_apply, inv_inv, Set.restrict_apply, Function.comp_apply,
      omegaPerm_pow_apply]
  rw [h, orbit_smul]

/-- **Every frame is the reference frame, transported** — `carries_coreLens_eq` for an attractor.
`ω(B)` is a permutation world, so an exactly-carrying family has no freedom there past frame
zero. -/
theorem carriesOn_restrict_eq {U : Fin n → Fin n} {B : Set (Fin n)} (hB : ∀ s ∈ B, U s ∈ B)
    {ℓ : ℕ → Fin n → Fin m} (h : CarriesOn U ℓ (omegaLimit U B)) (t : ℕ) :
    (omegaLimit U B).restrict (ℓ t)
      = (omegaLimit U B).restrict (ℓ 0) ∘ ⇑(omegaPerm U hB ^ t)⁻¹ := by
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
      N = Nat.card ↥(orbit (Perm ↥S) (S.restrict (ℓ 0)))}

/-- **The exact entropic capacity on a region**, in cardinality form. `CbHe` is the case
`S = core U` up to the reference frame's relabelling. -/
noncomputable def CbHeOn (U : Fin n → Fin n) (S : Set (Fin n)) (b : ℕ) : ℕ :=
  sSup (EntropiesOn U S b)

/-- The **carried entropies affordable at budget `b` to an observer allowed a transient**: the
relabelling class, on the attractor, of the value a settling family settles to. -/
def EventualEntropies (U : Fin n → Fin n) (B : Finset (Fin n)) (b : ℕ) : Set ℕ :=
  {N : ℕ | ∃ k : ℕ, ∃ ℓ : ℕ → Fin n → Fin k, ∃ v : Fin n → Fin k,
      EventuallyCarries U ℓ B v ∧ PermBudget ℓ b ∧
      N = Nat.card ↥(orbit (Perm ↥(omegaLimit U ↑B)) ((omegaLimit U ↑B).restrict v))}

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
    have hveq : (omegaLimit U ↑B).restrict v = (omegaLimit U ↑B).restrict (ℓ T ∘ U^[T]) := by
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
theorem entropiesOn_le {U : Fin n → Fin n} {S : Set (Fin n)} {b N : ℕ}
    (h : N ∈ EntropiesOn U S b) : N ≤ (Nat.card ↥S)! := by
  obtain ⟨k, ℓ, -, -, rfl⟩ := h
  have hprod : 0 < ∏ i : Fin k, (Nat.card {x : ↥S // S.restrict (ℓ 0) x = i})! :=
    Finset.prod_pos fun i _ => Nat.factorial_pos _
  exact card_orbit_mul_prod_fiber_card (S.restrict (ℓ 0)) ▸ Nat.le_mul_of_pos_right _ hprod

theorem bddAbove_entropiesOn (U : Fin n → Fin n) (S : Set (Fin n)) (b : ℕ) :
    BddAbove (EntropiesOn U S b) := ⟨(Nat.card ↥S)!, fun _ h => entropiesOn_le h⟩

/-- **The attractor is the ceiling on eventual capacity** — the §3 ceiling, relativized to a basin
and read in the entropic currency. A transient buys no more than the attractor can hold. -/
theorem CbHeOn_le_factorial (U : Fin n → Fin n) (S : Set (Fin n)) (b : ℕ) :
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
frames off the recurrent core are unconstrained by the persistence identity, and so the frames of a
carried family need not repeat at all.

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
noncomputable def clamp (U : Fin n → Fin n) (t : ℕ) : ℕ :=
  if t < n then t else n + ((t - n) % orderOf (corePerm U))

theorem clamp_zero (U : Fin n → Fin n) : clamp U 0 = 0 := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · simp [clamp, hn]
  · simp [clamp, hn]

/-- The core permutation's period is at most `n !`. -/
theorem orderOf_corePerm_le (U : Fin n → Fin n) : orderOf (corePerm U) ≤ n ! := by
  classical
  haveI : Fintype ↥(core U) := Fintype.ofFinite _
  have h := orderOf_le_card_univ (x := corePerm U)
  rw [Fintype.card_perm] at h
  refine h.trans (Nat.factorial_le ?_)
  have := card_core_le U
  rwa [Nat.card_eq_fintype_card] at this

/-- The clamped clock never counts past `n + n !`. -/
theorem clamp_le (U : Fin n → Fin n) (t : ℕ) : clamp U t ≤ n + n ! := by
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
theorem corePerm_pow_clamp (U : Fin n → Fin n) {t : ℕ} (ht : n ≤ t) :
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
theorem Intertwines.iterate {U : X → X} {F : M → M} {ℓ : ℕ → X → M} (h : Intertwines U F ℓ) :
    ∀ t s, ℓ t (U^[t] s) = F^[t] (ℓ 0 s) := by
  intro t
  induction t with
  | zero => intro s; rfl
  | succ t ih =>
      intro s
      rw [Function.iterate_succ_apply', h t (U^[t] s), ih s, Function.iterate_succ_apply']

/-- **Telescoping a dilated square, from an arbitrary starting frame**: `j` blocks of `τ` steps of
the world advance the frame index by `j` and the reading by `j` steps of the law. This is the engine
of the composition lemma — it is what lets level 2 read level 1 at *its* own clock rate. -/
theorem Intertwines.iterate_shift {U : X → X} {F : M → M} {ℓ : ℕ → X → M} {τ : ℕ}
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
theorem surjective_tower_frame {P : Type*} {ℓ₁ : ℕ → X → M} {ℓ₂ : ℕ → M → P} {τ₂ : ℕ}
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
theorem stepComp_lensTable_comp {n₁ n₂ n₃ : ℕ} (g : Fin n₂ → Fin n₃) (f : Fin n₁ → Fin n₂) :
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
theorem primrec_compTableFn : Primrec compTableFn := by
  have h1 : Primrec fun p : ℕ => (Encodable.decode (α := List ℕ) p.unpair.1).getD [] :=
    Primrec.option_getD.comp
      (Primrec.decode.comp (Primrec.fst.comp Primrec.unpair)) (Primrec.const [])
  have h2 : Primrec fun p : ℕ => (Encodable.decode (α := List ℕ) p.unpair.2).getD [] :=
    Primrec.option_getD.comp
      (Primrec.decode.comp (Primrec.snd.comp Primrec.unpair)) (Primrec.const [])
  exact Primrec.encode.comp (primrec_stepComp.comp h1 h2)

theorem partrec_compTableFn : Nat.Partrec (fun p : ℕ => (compTableFn p : ℕ)) :=
  _root_.Partrec.nat_iff.mp (Primrec.to_comp primrec_compTableFn).partrec

/-- **The fixed composition builder.** One program, independent of the worlds and the alphabets. -/
noncomputable def compBuilder : Nat.Partrec.Code :=
  Classical.choose (Nat.Partrec.Code.exists_code.mp partrec_compTableFn)

theorem eval_compBuilder (p : ℕ) :
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
def mulFn (p : ℕ) : ℕ := p.unpair.1 * p.unpair.2

theorem primrec_mulFn : Primrec mulFn :=
  Primrec.nat_mul.comp (Primrec.fst.comp Primrec.unpair) (Primrec.snd.comp Primrec.unpair)

theorem partrec_mulFn : Nat.Partrec (fun p : ℕ => (mulFn p : ℕ)) :=
  _root_.Partrec.nat_iff.mp (Primrec.to_comp primrec_mulFn).partrec

/-- The fixed multiplication builder. -/
noncomputable def mulBuilder : Nat.Partrec.Code :=
  Classical.choose (Nat.Partrec.Code.exists_code.mp partrec_mulFn)

theorem eval_mulBuilder (p : ℕ) :
    Nat.Partrec.Code.eval mulBuilder p = Part.some (mulFn p) := by
  have h := congrFun (Classical.choose_spec
    (Nat.Partrec.Code.exists_code.mp partrec_mulFn)) p
  simpa [mulBuilder] using h

/-- **The clock rescaler** `k ↦ τ * k`: level 2's frame `k` is level 1's frame `τ * k`. The dilation
`τ` rides in as a *binary* constant (`bconst`), so the tower pays for its dilation in bit-length —
`O (Nat.size τ)` — and not in magnitude. -/
noncomputable def scaleCode (τ : ℕ) : Nat.Partrec.Code :=
  comp mulBuilder (pair (bconst τ) Code.id)

theorem eval_scaleCode (τ k : ℕ) : (scaleCode τ).eval k = Part.some (τ * k) := by
  have hp : (pair (bconst τ) Code.id).eval k = Part.some (Nat.pair τ k) := by
    change Nat.pair <$> (bconst τ).eval k <*> Code.id.eval k = _
    rw [eval_bconst, eval_id]
    simp [Seq.seq]
  rw [scaleCode, eval_comp_some hp, eval_mulBuilder, mulFn, Nat.unpair_pair]

theorem elen_scaleCode_le (τ : ℕ) :
    elen (scaleCode τ) ≤ (15 + elen dbl) * Nat.size τ + (elen mulBuilder + (30 + elen dbl)) := by
  have hb := elen_bconst_le τ
  have hid : elen Code.id = 9 := by decide
  rw [scaleCode, E_len_comp, E_len_pair]
  omega

/-- **The tower builder**: one program for the composite family. Rescale the clock, run each level's
program on its own index, compose the tabulations. -/
noncomputable def towerCode (c₁ c₂ : Nat.Partrec.Code) (τ₂ : ℕ) : Nat.Partrec.Code :=
  comp compBuilder (pair c₂ (comp c₁ (scaleCode τ₂)))

/-- The plumbing constant: the two fixed builders plus the opcodes. Absolute — independent of the
worlds, the alphabets, the families, the dilations, and the budgets. -/
noncomputable def towerConst : ℕ := 39 + elen compBuilder + elen mulBuilder + elen dbl

theorem eval_towerCode {n₁ n₂ n₃ : ℕ} {ℓ₁ : ℕ → Fin n₁ → Fin n₂} {ℓ₂ : ℕ → Fin n₂ → Fin n₃}
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

theorem elen_towerCode_le (c₁ c₂ : Nat.Partrec.Code) (τ₂ : ℕ) :
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
theorem comp_smul_lens {α : Type*} {k : ℕ} (U : Perm α) (ℓ : α → Fin m) (g : Fin m → Fin k) :
    g ∘ (U • ℓ) = U • (g ∘ ℓ) := rfl

/-- The coarsened reading's relabelling class is the *image* of the original's, by equivariance. -/
theorem orbit_comp_eq_image {α : Type*} {k : ℕ} (ℓ : α → Fin m) (g : Fin m → Fin k) :
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

@[simp] theorem prodWorld_apply {X₁ X₂ : Type*} (U₁ : X₁ → X₁) (U₂ : X₂ → X₂) (x : X₁ × X₂) :
    prodWorld U₁ U₂ x = (U₁ x.1, U₂ x.2) := rfl

/-- **The factors never mix**: `t` steps of the product are `t` steps of each factor. -/
theorem prodWorld_iterate {X₁ X₂ : Type*} (U₁ : X₁ → X₁) (U₂ : X₂ → X₂) (t : ℕ) :
    (prodWorld U₁ U₂)^[t] = prodWorld (U₁^[t]) (U₂^[t]) := Prod.map_iterate U₁ U₂ t

@[simp] theorem prodWorld_iterate_apply {X₁ X₂ : Type*} (U₁ : X₁ → X₁) (U₂ : X₂ → X₂) (t : ℕ)
    (x : X₁ × X₂) : (prodWorld U₁ U₂)^[t] x = (U₁^[t] x.1, U₂^[t] x.2) := by
  rw [prodWorld_iterate]; rfl

/-- The product of two **permutations** is a permutation of the product, acting as `prodWorld`. -/
def prodPerm {X₁ X₂ : Type*} (U₁ : Perm X₁) (U₂ : Perm X₂) : Perm (X₁ × X₂) :=
  Equiv.prodCongr U₁ U₂

theorem prodPerm_coe {X₁ X₂ : Type*} (U₁ : Perm X₁) (U₂ : Perm X₂) :
    ⇑(prodPerm U₁ U₂) = prodWorld ⇑U₁ ⇑U₂ := rfl

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
theorem prodWorldFin_val {n₁ n₂ : ℕ} (U₁ : Perm (Fin n₁)) (U₂ : Perm (Fin n₂)) (i : Fin n₁)
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

theorem primrec_prodAppend : Primrec fun q : List ℕ × List ℕ => prodAppend q.1 q.2 := by
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

theorem primrec_prodTableFn : Primrec prodTableFn := by
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

theorem partrec_prodTableFn : Nat.Partrec (fun p : ℕ => (prodTableFn p : ℕ)) :=
  _root_.Partrec.nat_iff.mp (Primrec.to_comp primrec_prodTableFn).partrec

/-- **The fixed product-world builder code.** -/
noncomputable def prodBuilder : Nat.Partrec.Code :=
  Classical.choose (Nat.Partrec.Code.exists_code.mp partrec_prodTableFn)

theorem eval_prodBuilder (p : ℕ) :
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

@[simp] theorem divNat_finProdFinEquiv {n₁ n₂ : ℕ} (i : Fin n₁) (j : Fin n₂) :
    (finProdFinEquiv (i, j)).divNat = i := by
  have h := finProdFinEquiv.symm_apply_apply (i, j)
  rw [finProdFinEquiv_symm_apply] at h
  exact congrArg Prod.fst h

@[simp] theorem prodLensFinFst_apply {n₁ n₂ k₁ : ℕ} (ℓ₁ : ℕ → Fin n₁ → Fin k₁) (t : ℕ)
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
def liftAppend (T₁ : List ℕ) (s : ℕ) : List ℕ := T₁.flatMap (fun a => List.replicate s a)

theorem primrec_liftAppend : Primrec fun q : List ℕ × ℕ => liftAppend q.1 q.2 := by
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

theorem lensTable_prodLensFinFst {n₁ n₂ k₁ : ℕ} (ℓ₁ : ℕ → Fin n₁ → Fin k₁) (t : ℕ) :
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
def liftLensTableFn (p : ℕ) : ℕ :=
  Encodable.encode
    (liftAppend ((Encodable.decode (α := List ℕ) p.unpair.1).getD []) p.unpair.2)

theorem primrec_liftLensTableFn : Primrec liftLensTableFn := by
  have hdec1 : Primrec fun p : ℕ => (Encodable.decode (α := List ℕ) p.unpair.1).getD [] :=
    Primrec.option_getD.comp (Primrec.decode.comp (Primrec.fst.comp Primrec.unpair))
      (Primrec.const [])
  exact Primrec.encode.comp
    (primrec_liftAppend.comp (Primrec.pair hdec1 (Primrec.snd.comp Primrec.unpair)))

theorem liftLensTableFn_eq {n₁ n₂ k₁ : ℕ} (ℓ₁ : ℕ → Fin n₁ → Fin k₁) (t : ℕ) :
    liftLensTableFn (Nat.pair (lensCode (ℓ₁ t)) n₂) = lensCode (prodLensFinFst ℓ₁ n₂ t) := by
  rw [liftLensTableFn]
  simp only [Nat.unpair_pair, decode_lensCode]
  rw [← lensTable_prodLensFinFst]
  rfl

theorem partrec_liftLensTableFn : Nat.Partrec (fun p : ℕ => (liftLensTableFn p : ℕ)) :=
  _root_.Partrec.nat_iff.mp (Primrec.to_comp primrec_liftLensTableFn).partrec

/-- **The fixed lift-builder code.** -/
noncomputable def liftBuilder : Nat.Partrec.Code :=
  Classical.choose (Nat.Partrec.Code.exists_code.mp partrec_liftLensTableFn)

theorem eval_liftBuilder (p : ℕ) :
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
theorem lensTable_getD {n m : ℕ} (ℓ : Fin n → Fin m) (i : ℕ) (h : i < n) :
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

theorem primrec_splitFst : Primrec fun q : List ℕ × ℕ => splitFst q.1 q.2 := by
  refine Primrec.list_map
    (Primrec.list_range.comp (Primrec.nat_div.comp (Primrec.list_length.comp Primrec.fst)
      Primrec.snd)) ?_
  refine Primrec₂.mk ?_
  exact Primrec.nat_div.comp
    ((Primrec.list_getD 0).comp (Primrec.fst.comp Primrec.fst)
      (Primrec.nat_mul.comp Primrec.snd (Primrec.snd.comp Primrec.fst)))
    (Primrec.snd.comp Primrec.fst)

theorem primrec_splitSnd : Primrec fun q : List ℕ × ℕ => splitSnd q.1 q.2 := by
  refine Primrec.list_map (Primrec.list_range.comp Primrec.snd) ?_
  refine Primrec₂.mk ?_
  exact Primrec.nat_mod.comp
    ((Primrec.list_getD 0).comp (Primrec.fst.comp Primrec.fst) Primrec.snd)
    (Primrec.snd.comp Primrec.fst)

theorem splitFst_prodWorldFin {n₁ n₂ : ℕ} (U₁ : Perm (Fin n₁)) (U₂ : Perm (Fin n₂))
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

theorem splitSnd_prodWorldFin {n₁ n₂ : ℕ} (U₁ : Perm (Fin n₁)) (U₂ : Perm (Fin n₂))
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

theorem primrec_splitFstFn : Primrec splitFstFn := by
  have hdec : Primrec fun p : ℕ => (Encodable.decode (α := List ℕ) p.unpair.1).getD [] :=
    Primrec.option_getD.comp (Primrec.decode.comp (Primrec.fst.comp Primrec.unpair))
      (Primrec.const [])
  exact Primrec.encode.comp
    (primrec_splitFst.comp (Primrec.pair hdec (Primrec.snd.comp Primrec.unpair)))

theorem primrec_splitSndFn : Primrec splitSndFn := by
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

theorem partrec_splitFstFn : Nat.Partrec (fun p : ℕ => (splitFstFn p : ℕ)) :=
  _root_.Partrec.nat_iff.mp (Primrec.to_comp primrec_splitFstFn).partrec

theorem partrec_splitSndFn : Nat.Partrec (fun p : ℕ => (splitSndFn p : ℕ)) :=
  _root_.Partrec.nat_iff.mp (Primrec.to_comp primrec_splitSndFn).partrec

/-- **The fixed first-factor splitter code.** -/
noncomputable def splitFstBuilder : Nat.Partrec.Code :=
  Classical.choose (Nat.Partrec.Code.exists_code.mp partrec_splitFstFn)

/-- **The fixed second-factor splitter code.** -/
noncomputable def splitSndBuilder : Nat.Partrec.Code :=
  Classical.choose (Nat.Partrec.Code.exists_code.mp partrec_splitSndFn)

theorem eval_splitFstBuilder (p : ℕ) :
    Nat.Partrec.Code.eval splitFstBuilder p = Part.some (splitFstFn p) := by
  have h := congrFun (Classical.choose_spec
    (Nat.Partrec.Code.exists_code.mp partrec_splitFstFn)) p
  simpa [splitFstBuilder] using h

theorem eval_splitSndBuilder (p : ℕ) :
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

theorem prodLensFinFst_eq_liftFst {n₁ n₂ k₁ : ℕ} (ℓ₁ : ℕ → Fin n₁ → Fin k₁) (t : ℕ) :
    prodLensFinFst ℓ₁ n₂ t = liftFst (ℓ₁ t) n₂ := rfl

@[simp] theorem liftFst_apply {n₁ n₂ k₁ : ℕ} (ℓ₀ : Fin n₁ → Fin k₁) (i : Fin n₁) (j : Fin n₂) :
    liftFst ℓ₀ n₂ (finProdFinEquiv (i, j)) = ℓ₀ i := by simp [liftFst]

theorem liftFst_injective {n₁ n₂ k₁ : ℕ} (hn₂ : 0 < n₂) :
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
theorem card_orbit_le_liftFst {n₁ n₂ k₁ : ℕ} (ℓ₀ : Fin n₁ → Fin k₁) (hn₂ : 0 < n₂) :
    Nat.card ↥(orbit (Perm (Fin n₁)) ℓ₀)
      ≤ Nat.card ↥(orbit (Perm (Fin (n₁ * n₂))) (liftFst ℓ₀ n₂)) := by
  haveI : Finite ↥(orbit (Perm (Fin (n₁ * n₂))) (liftFst ℓ₀ n₂)) := Set.toFinite _
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

/-- Coherence with the budgeted form: `EventuallyCarries` is settling plus the demand that the
settled value be surjective. The two predicates are one predicate. -/
theorem eventuallyCarries_iff_settlesValue {n m : ℕ} (U : Fin n → Fin n) (ℓ : ℕ → Fin n → Fin m)
    (B : Finset (Fin n)) (v : Fin n → Fin m) :
    EventuallyCarries U ℓ B v ↔ Set.SurjOn v ↑B Set.univ ∧ SettlesValue U ℓ (↑B) v :=
  Iff.rfl

/-- The **Hamming ball** of radius `e` about `c`: the states reachable by corrupting at most `e`
cells. -/
def hball [Fintype ι] [DecidableEq V] (e : ℕ) (c : Mem ι V) : Set (Mem ι V) :=
  {x | hammingDist c x ≤ e}

theorem mem_hball [Fintype ι] [DecidableEq V] {e : ℕ} {c x : Mem ι V} :
    x ∈ hball e c ↔ hammingDist c x ≤ e := Iff.rfl

theorem self_mem_hball [Fintype ι] [DecidableEq V] (e : ℕ) (c : Mem ι V) : c ∈ hball e c := by
  simp [hball]

theorem hball_mono [Fintype ι] [DecidableEq V] {e e' : ℕ} (h : e ≤ e') (c : Mem ι V) :
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
theorem hasMargin_zero [Fintype ι] [DecidableEq V] (U : Mem ι V → Mem ι V) (B : Set (Mem ι V))
    (v : Mem ι V → M) : HasMargin U B v 0 := by
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

theorem zero_mem_marginSet [Fintype ι] [DecidableEq V] (U : Mem ι V → Mem ι V) (B : Set (Mem ι V))
    (v : Mem ι V → M) : 0 ∈ MarginSet U B v :=
  ⟨Nat.zero_le _, hasMargin_zero U B v⟩

theorem bddAbove_marginSet [Fintype ι] [DecidableEq V] (U : Mem ι V → Mem ι V) (B : Set (Mem ι V))
    (v : Mem ι V → M) : BddAbove (MarginSet U B v) :=
  ⟨Fintype.card ι, fun _ he => he.1⟩

theorem le_margin [Fintype ι] [DecidableEq V] {U : Mem ι V → Mem ι V} {B : Set (Mem ι V)}
    {v : Mem ι V → M} {e : ℕ} (he : e ∈ MarginSet U B v) : e ≤ margin U B v :=
  le_csSup (bddAbove_marginSet U B v) he

theorem margin_le_card [Fintype ι] [DecidableEq V] (U : Mem ι V → Mem ι V) (B : Set (Mem ι V))
    (v : Mem ι V → M) : margin U B v ≤ Fintype.card ι :=
  csSup_le ⟨0, zero_mem_marginSet U B v⟩ fun _ he => he.1

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

theorem transport_apply [DecidableEq V] (c s x : Mem ι V) (i : ι) :
    transport c s x i = Equiv.swap (c i) (s i) (x i) := rfl

theorem transport_left [DecidableEq V] (c s : Mem ι V) : transport c s c = s := by
  funext i
  simp [transport_apply]

/-- The transporter preserves Hamming distance: it acts injectively in each cell. -/
theorem hammingDist_transport [Fintype ι] [DecidableEq V] (c s x y : Mem ι V) :
    hammingDist (transport c s x) (transport c s y) = hammingDist x y :=
  hammingDist_comp (fun i => (Equiv.swap (c i) (s i) : V → V))
    (fun i => (Equiv.swap (c i) (s i)).injective)

/-- Balls are carried to balls: the transporter maps `Ball e c` into `Ball e s`. -/
theorem transport_mem_hball [Fintype ι] [DecidableEq V] {e : ℕ} {c x : Mem ι V} (s : Mem ι V)
    (hx : x ∈ hball e c) : transport c s x ∈ hball e s := by
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

theorem RecoversWithin.mono_time [Fintype ι] [DecidableEq V] {U : Mem ι V → Mem ι V}
    {ℓ : ℕ → Mem ι V → M} {B : Set (Mem ι V)} {v : Mem ι V → M} {e T T' : ℕ}
    (h : RecoversWithin U ℓ B v e T) (hle : T ≤ T') : RecoversWithin U ℓ B v e T' :=
  fun s hs s' hs' t ht => h s hs s' hs' t (le_trans hle ht)

theorem RecoversWithin.mono_radius [Fintype ι] [DecidableEq V] {U : Mem ι V → Mem ι V}
    {ℓ : ℕ → Mem ι V → M} {B : Set (Mem ι V)} {v : Mem ι V → M} {e e' T : ℕ}
    (h : RecoversWithin U ℓ B v e T) (hle : e' ≤ e) : RecoversWithin U ℓ B v e' T :=
  fun s hs s' hs' => h s hs s' (hball_mono hle s hs')

/-- Under a margin, recovery restores the **attractor's** value, not merely the perturbed state's
own: the two agree exactly because the perturbation stayed inside the margin. -/
theorem RecoversWithin.settled_value [Fintype ι] [DecidableEq V] {U : Mem ι V → Mem ι V}
    {ℓ : ℕ → Mem ι V → M} {B : Set (Mem ι V)} {v : Mem ι V → M} {e T : ℕ}
    (hm : HasMargin U B v e) (h : RecoversWithin U ℓ B v e T) :
    ∀ s ∈ omegaLimit U B, ∀ s' ∈ hball e s, ∀ t ≥ T, ℓ t (U^[t] s') = v s :=
  fun s hs s' hs' t ht => (h s hs s' hs' t ht).trans (hm s hs s' hs').2

/-- **The recovery time** at radius `e`: the least step by which every `e`-perturbation is read
correctly. -/
noncomputable def recoveryTime [Fintype ι] [DecidableEq V] (U : Mem ι V → Mem ι V)
    (ℓ : ℕ → Mem ι V → M) (B : Set (Mem ι V)) (v : Mem ι V → M) (e : ℕ) : ℕ :=
  sInf {T | RecoversWithin U ℓ B v e T}

theorem recoveryTime_le [Fintype ι] [DecidableEq V] {U : Mem ι V → Mem ι V} {ℓ : ℕ → Mem ι V → M}
    {B : Set (Mem ι V)} {v : Mem ι V → M} {e T : ℕ} (h : RecoversWithin U ℓ B v e T) :
    recoveryTime U ℓ B v e ≤ T := Nat.sInf_le h

theorem recoversWithin_recoveryTime [Fintype ι] [DecidableEq V] {U : Mem ι V → Mem ι V}
    {ℓ : ℕ → Mem ι V → M} {B : Set (Mem ι V)} {v : Mem ι V → M} {e : ℕ}
    (h : ∃ T, RecoversWithin U ℓ B v e T) :
    RecoversWithin U ℓ B v e (recoveryTime U ℓ B v e) := Nat.sInf_mem h

/-! ### The positive witness: the majority world is robust ([Decoupling] §3.5) -/

/-- The majority world writes back its own consensus bit: `majBit` is invariant under one step. -/
theorem majBit_majWorld (s : Mem (Fin 3) Bool) : majBit (majWorld s) = majBit s := by
  rw [majWorld_apply]
  cases h : majBit s <;> simp [majBit]

/-- …hence under every number of steps: the consensus bit is what the majority world conserves. -/
theorem majBit_iterate (t : ℕ) (s : Mem (Fin 3) Bool) : majBit (majWorld^[t] s) = majBit s := by
  induction t with
  | zero => rfl
  | succ t ih => rw [Function.iterate_succ_apply', majBit_majWorld]; exact ih

/-- The consensus bit settles instantly along every orbit: the majority world with the static
decoder `majBit` is a settling family, with transient zero. -/
theorem settlesValue_majWorld :
    SettlesValue majWorld (fun _ => majBit) (Set.univ : Set (Mem (Fin 3) Bool)) majBit :=
  fun s _ => ⟨0, fun t _ => majBit_iterate t s⟩

/-- Both bits are attained: the settled reading carries one full bit. -/
theorem surjOn_majBit :
    Set.SurjOn majBit (Set.univ : Set (Mem (Fin 3) Bool)) Set.univ := by
  intro b _
  exact ⟨fun _ => b, Set.mem_univ _, by cases b <;> rfl⟩

/-- **The majority world has margin at least one** — the probe's positive witness. On the attractor
(the consensus set, `core_majWorld`) all three copies agree, so flipping any single copy leaves two
in agreement and the majority — hence the settled bit — unchanged. The `1` is the whole content of
"three-copy redundancy corrects one error", read here as a property of the *world's dynamics*
rather than of a code: `majWorld` is its own decoder. -/
theorem hasMargin_majWorld :
    HasMargin majWorld (Set.univ : Set (Mem (Fin 3) Bool)) majBit 1 := by
  intro s hs s' hs'
  refine ⟨Set.mem_univ _, ?_⟩
  rw [← core_eq_omegaLimit, core_majWorld] at hs
  obtain ⟨h01, h12⟩ := hs
  rw [mem_hball] at hs'
  revert h01 h12 hs'
  revert s s'
  decide

theorem margin_majWorld : 1 ≤ margin majWorld (Set.univ : Set (Mem (Fin 3) Bool)) majBit :=
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

@[simp] theorem maj3_self (b : Bool) : maj3 b b b = b := by cases b <;> rfl

/-- Two agreeing votes carry the majority, wherever the third sits. -/
theorem maj3_left_left (b z : Bool) : maj3 b b z = b := by cases b <;> cases z <;> rfl

theorem maj3_left_right (b z : Bool) : maj3 b z b = b := by cases b <;> cases z <;> rfl

theorem maj3_right_right (b z : Bool) : maj3 z b b = b := by cases b <;> cases z <;> rfl

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

@[simp] theorem subBlock_encRec (k : ℕ) (c : Fin 3) (b : Bool) :
    subBlock k c (encRec (k + 1) b) = encRec k b := rfl

/-- **The roundtrip**: the decoder reads back what the encoder wrote. -/
@[simp] theorem decRec_encRec (k : ℕ) (b : Bool) : decRec k (encRec k b) = b := by
  induction k with
  | zero => rfl
  | succ k ih => rw [decRec]; simp only [subBlock_encRec, ih]; exact maj3_self b

/-- `hammingDist` as a sum of indicators — the counting form the block split needs. -/
theorem hammingDist_eq_sum {ι : Type*} [Fintype ι] (x y : ι → Bool) :
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

theorem healWorld_apply (k : ℕ) (x : Mem (Fin (3 ^ k)) Bool) :
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
@[simp] theorem decRec_healWorld (k : ℕ) (x : Mem (Fin (3 ^ k)) Bool) :
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

theorem decRec_iterate (k t : ℕ) (x : Mem (Fin (3 ^ k)) Bool) :
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

theorem two_pow_le_three_pow (k : ℕ) : (2 : ℕ) ^ k ≤ 3 ^ k :=
  Nat.pow_le_pow_left (by norm_num) k

theorem recMaj_le_margin (k e : ℕ) (he : e < 2 ^ k) :
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

theorem subBlock_advRec_zero (k : ℕ) (b : Bool) :
    subBlock k 0 (advRec (k + 1) b) = advRec k b := by
  funext i; simp [subBlock, advRec, Equiv.symm_apply_apply]

theorem subBlock_advRec_one (k : ℕ) (b : Bool) :
    subBlock k 1 (advRec (k + 1) b) = advRec k b := by
  funext i; simp [subBlock, advRec, Equiv.symm_apply_apply]

theorem subBlock_advRec_two (k : ℕ) (b : Bool) :
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

@[simp] theorem sumMem_apply {ι₁ ι₂ V : Type*} (p : Mem ι₁ V × Mem ι₂ V) :
    (sumMem p : Mem (ι₁ ⊕ ι₂) V) = Sum.elim p.1 p.2 := rfl

@[simp] theorem sumMem_symm_apply {ι₁ ι₂ V : Type*} (x : Mem (ι₁ ⊕ ι₂) V) :
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

@[simp] theorem blockOf_habitatEnc (κ k : ℕ) (b : Mem (Fin κ) Bool) (i : Fin κ) :
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
theorem hammingDist_blockOf_le (κ k : ℕ) (h h' : Mem (Fin κ × Fin (3 ^ k)) Bool) (i : Fin κ) :
    hammingDist (blockOf h i) (blockOf h' i) ≤ hammingDist h h' := by
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

theorem habitatWorld_valid (κ k : ℕ) (G : Mem (Fin κ) Bool → Mem (Fin κ) Bool)
    (h : Mem (Fin κ × Fin (3 ^ k)) Bool) :
    ∃ b, habitatWorld κ k G h = habitatEnc κ k b := ⟨G (macroLens κ k h), rfl⟩

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

@[simp] theorem witnessWorld_inl (κ k : ℕ) (G : Mem (Fin κ) Bool → Mem (Fin κ) Bool)
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
def bitDigit {N : ℕ} (x : Mem (Fin N) Bool) (j : ℕ) : ℕ :=
  if h : j < N then (if x ⟨j, h⟩ then 1 else 0) else 0

theorem bitDigit_lt {N : ℕ} (x : Mem (Fin N) Bool) (j : ℕ) : bitDigit x j < 2 := by
  rw [bitDigit]; split
  · split <;> norm_num
  · norm_num

theorem stateEquiv_val_range {N : ℕ} (x : Mem (Fin N) Bool) :
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

@[simp] theorem packWorld_apply {N : ℕ} (U : Mem (Fin N) Bool → Mem (Fin N) Bool)
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

@[simp] theorem packLens_apply {N M : ℕ} (ℓ : Mem (Fin N) Bool → Mem (Fin M) Bool)
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

theorem numBitN_stateEquiv {N : ℕ} (x : Mem (Fin N) Bool) (j : ℕ) (hj : j < N) :
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
def packReduceList (m s : ℕ) : ℕ :=
  ((List.range m).map fun j =>
    ((numBitN s (3 * j) + numBitN s (3 * j + 1) + numBitN s (3 * j + 2)) / 2) * 2 ^ j).sum

theorem packReduceList_eq (m s : ℕ) : packReduceList m s = packReduce m s := by
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
private def redStep (p : ℕ × ℕ) : ℕ × ℕ := (p.1 - 1, packReduce (3 ^ (p.1 - 1)) p.2)

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

theorem primrec_decFn : Primrec decFn :=
  primrec_numDecRec.comp (Primrec.fst.comp Primrec.unpair) (Primrec.snd.comp Primrec.unpair)

theorem partrec_decFn : Nat.Partrec (fun a : ℕ => (decFn a : ℕ)) :=
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

@[simp] theorem reindexMem_apply {ι₁ ι₂ V : Type*} (e : ι₁ ≃ ι₂) (x : Mem ι₂ V) (i : ι₁) :
    reindexMem e x i = x (e i) := rfl

/-- The habitat's flat cell index: block `i`, position `p` sits at `p + 3 ^ k * i`, so block `i`
occupies the run `[3 ^ k * i, 3 ^ k * (i + 1))`. -/
def habEquiv (κ k : ℕ) : Fin (κ * 3 ^ k) ≃ Fin κ × Fin (3 ^ k) := finProdFinEquiv.symm

/-- The habitat state, relabelled onto flat cells so that the packing applies. -/
def flatHab (κ k : ℕ) : Mem (Fin κ × Fin (3 ^ k)) Bool ≃ Mem (Fin (κ * 3 ^ k)) Bool :=
  reindexMem (habEquiv κ k)

@[simp] theorem flatHab_symm_cell (κ k : ℕ) (h : Mem (Fin κ × Fin (3 ^ k)) Bool)
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
def blockDigit (κ k : ℕ) (h : Mem (Fin κ × Fin (3 ^ k)) Bool) (j : ℕ) : ℕ :=
  if hj : j < κ then ((stateEquiv (3 ^ k) (blockOf h ⟨j, hj⟩) : Fin (2 ^ 3 ^ k)) : ℕ) else 0

theorem blockDigit_lt (κ k : ℕ) (h : Mem (Fin κ × Fin (3 ^ k)) Bool) (j : ℕ) :
    blockDigit κ k h j < 2 ^ 3 ^ k := by
  rw [blockDigit]; split
  · exact Fin.isLt _
  · positivity

theorem stateEquiv_flatHab_range (κ k : ℕ) (h : Mem (Fin κ × Fin (3 ^ k)) Bool) :
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

theorem macroWordOf_eq_sum (κ k s : ℕ) :
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

theorem habWriteBack_eq_sum (κ k Gw : ℕ) :
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

private theorem eval_comp_some' {a b : Nat.Partrec.Code} {j v : ℕ}
    (hv : Nat.Partrec.Code.eval b j = Part.some v) :
    Nat.Partrec.Code.eval (Nat.Partrec.Code.comp a b) j = Nat.Partrec.Code.eval a v := by
  simp [Nat.Partrec.Code.eval, hv]

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

theorem partrec_habTableFn : Nat.Partrec (fun a : ℕ => (habTableFn a : ℕ)) :=
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
      = Part.some (lensCode (packWorld G)) := (eval_comp_some' hz).trans hG
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
    rw [eval_comp_some' hp1, eval_habBuilder, habTableFn_eq]
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

@[simp] theorem prodWorldFinFn_apply {n₁ n₂ : ℕ} (U₁ : Fin n₁ → Fin n₁) (U₂ : Fin n₂ → Fin n₂)
    (i : Fin n₁) (j : Fin n₂) :
    prodWorldFinFn U₁ U₂ (finProdFinEquiv (i, j)) = finProdFinEquiv (U₁ i, U₂ j) := by
  simp [prodWorldFinFn]

/-- The product world's table entry at the pair `(i, j)`, in the index shape `List.ofFn_mul`
produces — the `prodWorldFin_val` arithmetic with the permutation coercion dropped. -/
theorem prodWorldFinFn_val {n₁ n₂ : ℕ} (U₁ : Fin n₁ → Fin n₁) (U₂ : Fin n₂ → Fin n₂) (i : Fin n₁)
    (j : Fin n₂) (h : i.val * n₂ + j.val < n₁ * n₂) :
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
theorem lensTable_prodWorldFinFn {n₁ n₂ : ℕ} (U₁ : Fin n₁ → Fin n₁) (U₂ : Fin n₂ → Fin n₂) :
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
theorem prodTableFn_eq_fn {n₁ n₂ : ℕ} (U₁ : Fin n₁ → Fin n₁) (U₂ : Fin n₂ → Fin n₂) :
    prodTableFn (Nat.pair (lensCode U₁) (lensCode U₂)) = lensCode (prodWorldFinFn U₁ U₂) := by
  rw [prodTableFn]
  simp only [Nat.unpair_pair, decode_lensCode]
  rw [← lensTable_prodWorldFinFn]
  rfl

/-- **Rules compose for endofunctions too.** Given codes for the two factors' tables, the
endofunction product world costs their lengths plus the same absolute constant
`elen prodBuilder + 6` as `KE_prodWorldFin_le` — one fixed builder, independent of the worlds. -/
theorem KE_prodWorldFinFn_le {n₁ n₂ : ℕ} (U₁ : Fin n₁ → Fin n₁) (U₂ : Fin n₂ → Fin n₂)
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

theorem flatRead_surjective (κ k : ℕ) : Function.Surjective (flatRead κ k) := by
  intro b
  obtain ⟨h, hh⟩ := macroLens_surjective κ k b
  exact ⟨flatHab κ k h, by rw [flatRead, Equiv.symm_apply_apply, hh]⟩

theorem packRead_surjective (κ k : ℕ) : Function.Surjective (packRead κ k) :=
  packLens_surjective (flatRead_surjective κ k)

/-- **The reading intertwines the flat world with the macro law**: reading after a step is a step of
`G` after reading, on the numeral carrier — `flatWorld` conjugates `habitatWorld`, `macroLens` reads
`G` off it, and the packing preserves the square. -/
theorem packRead_square (κ k : ℕ) (G : Mem (Fin κ) Bool → Mem (Fin κ) Bool)
    (s : Fin (2 ^ (κ * 3 ^ k))) :
    packRead κ k (packWorld (flatWorld κ k G) s) = packWorld G (packRead κ k s) := by
  refine packWorld_square (fun x => ?_) s
  rw [flatRead, flatRead, flatWorld, Equiv.symm_apply_apply, macro_square]

/-- **The reading's table**, tabulated over every state as one function of the paired input
`⟨κ, k⟩` — the reading has no other parameter, so nothing about `G` or the environment enters. -/
def readTableFn (a : ℕ) : ℕ :=
  Encodable.encode ((List.range (2 ^ (a.unpair.1 * 3 ^ a.unpair.2))).map
    (fun s => macroWordOf a.unpair.1 a.unpair.2 s))

theorem primrec_readTableFn : Primrec readTableFn := by
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
theorem readTableFn_eq (κ k : ℕ) : readTableFn (Nat.pair κ k) = lensCode (packRead κ k) := by
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

theorem partrec_readTableFn : Nat.Partrec (fun a : ℕ => (readTableFn a : ℕ)) :=
  _root_.Partrec.nat_iff.mp (Primrec.to_comp primrec_readTableFn).partrec

/-- **The fixed reading builder code**: one program taking `⟨κ, k⟩` and returning the reading's
table — the decoder, uniform in the structural sizes and free of `G`. -/
noncomputable def readBuilder : Nat.Partrec.Code :=
  Classical.choose (Nat.Partrec.Code.exists_code.mp partrec_readTableFn)

theorem eval_readBuilder (a : ℕ) :
    Nat.Partrec.Code.eval readBuilder a = Part.some (readTableFn a) := by
  have h := congrFun (Classical.choose_spec
    (Nat.Partrec.Code.exists_code.mp partrec_readTableFn)) a
  simpa [readBuilder] using h

/-- **The owned reading family**: at frame `t`, read the macro state and transport it `t` steps back
along the macro law. Where `G` is a permutation this is `⇑((packPerm G)^t)⁻¹ ∘ packRead`, and it
carries the persistent macro model — the reference frame is the reading itself. -/
def ownLens (κ k : ℕ) (G : Perm (Mem (Fin κ) Bool)) : ℕ → Fin (2 ^ (κ * 3 ^ k)) → Fin (2 ^ κ) :=
  fun t s => ⇑((packPerm G ^ t)⁻¹) (packRead κ k s)

theorem ownLens_zero (κ k : ℕ) (G : Perm (Mem (Fin κ) Bool)) : ownLens κ k G 0 = packRead κ k := by
  funext s; simp [ownLens]

/-- **The family carries the macro model** over the flat habitat world. The reading intertwines the
world with the macro law (`packRead_square`), so `t` steps of the world advance the macro state by
`⇑((packPerm G)^t)`; transporting it back by the inverse recovers the reference reading.
Reversibility enters exactly here — the inverse iterate needs `G` a permutation. -/
theorem carries_ownLens (κ k : ℕ) (G : Perm (Mem (Fin κ) Bool)) :
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
theorem uniformBudget_ownLens (κ k : ℕ) (G : Perm (Mem (Fin κ) Bool)) (cG : Nat.Partrec.Code)
    (hG : cG.eval 0 = Part.some (lensCode (packWorld ⇑G))) :
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
theorem witnessWorld_iterate_apply {ι_J : Type*} (κ k : ℕ)
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
theorem habitatWorld_iterate_codeword (κ k : ℕ) (G : Perm (Mem (Fin κ) Bool)) (t : ℕ)
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
  haveI : Fintype ↥(core U) := Fintype.ofFinite _
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
theorem primrec_factorial : Primrec Nat.factorial := by
  have hstep : Primrec₂ fun (m ih : ℕ) => (m + 1) * ih :=
    (Primrec.nat_mul.comp (Primrec.succ.comp Primrec.fst) Primrec.snd).to₂
  refine (Primrec.nat_rec₁ 1 hstep).of_eq fun n => ?_
  induction n with
  | zero => rfl
  | succ k ih => rw [Nat.factorial_succ, ← ih]

/-- **The emergence builder's table**: from `⟨U's table, θ's table, t⟩`, iterate `U`'s table
`(n ! − 1) · t + n` times (`iterTable`, `n` read off the table's own length) and read the result
through `θ` (`stepComp`) — the guest's frame-`t` table, all forward, no inverse. -/
def emergeTableFn (a : ℕ) : ℕ :=
  Encodable.encode (stepComp ((Encodable.decode (α := List ℕ) a.unpair.2.unpair.1).getD [])
    (iterTable ((Encodable.decode (α := List ℕ) a.unpair.1).getD [])
      ((Nat.factorial ((Encodable.decode (α := List ℕ) a.unpair.1).getD []).length - 1)
        * a.unpair.2.unpair.2 + ((Encodable.decode (α := List ℕ) a.unpair.1).getD []).length)))

theorem primrec_emergeTableFn : Primrec emergeTableFn := by
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
theorem emergeTableFn_eq {n m : ℕ} (U : Fin n → Fin n) (θ : Fin n → Fin m) (t : ℕ) :
    emergeTableFn (Nat.pair (lensCode U) (Nat.pair (lensCode θ) t))
      = lensCode (emergeLens U θ t) := by
  rw [emergeTableFn]
  simp only [Nat.unpair_pair, decode_lensCode, lensTable_length]
  rw [iterTable_lensTable, stepComp_lensTable_comp]
  rfl

theorem partrec_emergeTableFn : Nat.Partrec (fun a : ℕ => (emergeTableFn a : ℕ)) :=
  _root_.Partrec.nat_iff.mp (Primrec.to_comp primrec_emergeTableFn).partrec

/-- **The fixed emergence builder code**: one program taking `⟨U's table, θ's table, t⟩`. -/
noncomputable def emergeBuilder : Nat.Partrec.Code :=
  Classical.choose (Nat.Partrec.Code.exists_code.mp partrec_emergeTableFn)

theorem eval_emergeBuilder (a : ℕ) :
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



