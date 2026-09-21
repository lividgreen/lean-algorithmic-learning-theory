/-
Copyright (c) 2026 Mykola Palamarchuk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mykola Palamarchuk
-/
module

public import ALT.MemoryWidth

-- Formal-check file, not Mathlib-destined: opt out of the house-style header linter.
set_option linter.style.header false

/-!
# The growing width: the memory width at a world's (G2)-part
([Guests] §7 Definition 7.22, Definition 7.2's (G2) read against Definition 7.8's memory width)

Definition 7.2's growth grades are a property of a TRAJECTORY, and Definition 7.8's memory width is
a property of the PRESENTED WORLD `(X, U, Ω)` — Theorem 7.9's third scope note says so in as many
words, and nothing in the paper links the two. This file builds the object in which both are
visible, and it is a restriction rather than a new invention: the memory width taken at the states
whose `U`-orbit has unbounded `size` — Definition 7.2's `(G2)` — rather than at every admitted
state.

## Main results

* `GrowingPart` — the `(G2)`-part at an arbitrary `size : X → ℕ`: the states whose orbit under `U`
  has unbounded `size`.
* `mem_growingPart_iff_apply` / `mem_growingPart_iff_iterate` — the part is invariant under `U` and
  under any of its iterates, the second by induction on the first.
* `growingPart_of_merge` — the part is MERGE-SATURATED: two states some common iterate identifies
  are on the same side of it, which is what licenses reading the restriction on the merge quotient.
* `advances_growingPart` — a growing world's `(G2)`-part restriction is itself advancing, so
  `MemoryWidth.memWidth` is defined on it exactly as on the unrestricted stages.
* `growingWidth` — the memory width read at the `(G2)`-part: `MemoryWidth.memWidth` applied to the
  stage family intersected with `GrowingPart`, so every fact `MemoryWidth.lean` proves about
  `memWidth`'s SHAPE is inherited rather than reproved.
* `growingWidth_mono` — monotone, with no hypothesis beyond `Advances`: `MemoryWidth.memWidth_mono`
  applied to `advances_growingPart`, nothing further.
* `growingWidth_le_memWidth` — never exceeds the unrestricted width, via
  `MemoryWidth.memWidth_mono_of_subset` applied to the restriction's own inclusion.
* The guard family, both at `Ω t = {n | n ≤ t}` on `ℕ`:
  `growingWidth_id_slowClock_eq_zero_memWidth_eq_succ` — **the separating witness**, pinning that
  `growingWidth` is a genuine restriction of `memWidth` and not the same quantity under a different
  name — and `growingWidth_nat_succ_eq_one` — **the non-vacuity twin**, pinning that the restriction
  is not vacuously zero.

## Scope

**Registered as [Guests] §7 Definition 7.22** (FV row GV-30): the `(G2)`-part, the growing width,
its monotonicity and its bound by the plain width, and the two worlds at which the restriction is
genuine. The definitions also cite Definitions 7.2 and 7.8, the two objects being reconciled.

`growingWidth` inherits `memWidth`'s own dependence on the presented stage family, not only on
`(X, U)`: Theorem 7.9's third scope note observes that `memWidth` is a property of `(X, U, Ω)`, and
restricting further by `GrowingPart U size` adds a second axis of dependence, on `size`, without
removing the first. The guard family's own witnesses instantiate both: the identity update kills the
part outright regardless of `Ω` (`growingPart_id_eq_empty`), while the successor update's part is
everything regardless of `Ω` (`growingPart_nat_succ_eq_univ`) — in neither instance does the
restriction interact with which stage family is chosen, but nothing here claims that holds in
general.

`size` is left an arbitrary `X → ℕ`, on purpose: Definition 7.2 says "encoded size," and this file
owes no encoding — a consumer supplying one specializes `size` at the call site.

`GrowingPart`'s defining condition ranges over an entire orbit (`∀ N, ∃ k, …`), so it is not
decidable, and every proof below is classical; no `Decidable` instance is attempted or needed.
-/


@[expose] public section

namespace GrowingWidth

open GrowingCore GrowingWorld MemoryWidth

variable {X : Type*}

/-! ## The `(G2)`-part -/

/-- **The `(G2)`-part** ([Guests] Definition 7.22, Definition 7.2's `(G2)`): the states whose
orbit under `U` has `size` unbounded along it. -/
def GrowingPart (U : X → X) (size : X → ℕ) : Set X :=
  {x | ∀ N, ∃ k, N < size (U^[k] x)}

/-- **The part is `U`-invariant**: a state is in the part exactly when its `U`-image is. Forward:
given `N`, unboundedness at `max N (size x)` supplies a `k` that cannot be `0` (that would force
`max N (size x) < size x`, false since `size x ≤ max N (size x)`), so `k = j + 1` and `U^[j] (U x)`
is the witness for `N`. Backward: `U^[k] (U x) = U^[k + 1] x` supplies the witness directly, one
step later. -/
theorem mem_growingPart_iff_apply (U : X → X) (size : X → ℕ) (x : X) :
    x ∈ GrowingPart U size ↔ U x ∈ GrowingPart U size := by
  constructor
  · intro hx N
    obtain ⟨k, hk⟩ := hx (max N (size x))
    have hk0 : k ≠ 0 := by
      rintro rfl
      simp only [Function.iterate_zero_apply] at hk
      exact absurd hk (not_lt.mpr (le_max_right N (size x)))
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk0
    refine ⟨j, ?_⟩
    rw [Function.iterate_succ_apply] at hk
    exact lt_of_le_of_lt (le_max_left N (size x)) hk
  · intro hUx N
    obtain ⟨k, hk⟩ := hUx N
    exact ⟨k + 1, by rw [Function.iterate_succ_apply]; exact hk⟩

/-- **The part is invariant under every iterate of `U`**, by induction over
`mem_growingPart_iff_apply`. -/
theorem mem_growingPart_iff_iterate (U : X → X) (size : X → ℕ) (x : X) (k : ℕ) :
    x ∈ GrowingPart U size ↔ U^[k] x ∈ GrowingPart U size := by
  induction k with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', ← mem_growingPart_iff_apply]
    exact ih

/-- **The part is merge-saturated**: two states some common iterate of `U` identifies are on the
same side of it — the fact that licenses reading the restriction on the merge quotient rather than
only on individual states. -/
theorem growingPart_of_merge {U : X → X} {size : X → ℕ} {x y : X} {k : ℕ}
    (h : U^[k] x = U^[k] y) : x ∈ GrowingPart U size ↔ y ∈ GrowingPart U size := by
  rw [mem_growingPart_iff_iterate U size x k, h, ← mem_growingPart_iff_iterate U size y k]

/-- **The `(G2)`-part restriction of a growing world is itself advancing**: immediate from
`Advances`'s own unfolding and `mem_growingPart_iff_apply`. -/
theorem advances_growingPart {U : X → X} {Ω : ℕ → Set X} {size : X → ℕ}
    (hadv : Advances U Ω) : Advances U (fun t => Ω t ∩ GrowingPart U size) := by
  rintro t s ⟨hsΩ, hsG⟩
  exact ⟨hadv t s hsΩ, (mem_growingPart_iff_apply U size s).mp hsG⟩

/-! ## The growing width -/

/-- **The growing width** ([Guests] Definition 7.22, Definition 7.8's memory width read at
Definition 7.2's `(G2)`-part): `MemoryWidth.memWidth` applied to the stage family restricted to the
states whose orbit has unbounded `size`. -/
noncomputable def growingWidth (U : X → X) (size : X → ℕ) (Ω : ℕ → Set X) (t : ℕ) : ℕ∞ :=
  MemoryWidth.memWidth U (fun t => Ω t ∩ GrowingPart U size) t

/-- **Monotone, with no hypothesis beyond `Advances`**: `MemoryWidth.memWidth_mono` applied to
`advances_growingPart`, nothing further — the point of defining `growingWidth` as a restricted
`memWidth` rather than as a fresh supremum. -/
theorem growingWidth_mono {U : X → X} {size : X → ℕ} {Ω : ℕ → Set X}
    (hadv : Advances U Ω) : Monotone (growingWidth U size Ω) :=
  MemoryWidth.memWidth_mono (advances_growingPart hadv)

/-- **Never exceeds the unrestricted width**: `MemoryWidth.memWidth_mono_of_subset` applied to the
restriction's own inclusion, `Ω t ∩ GrowingPart U size ⊆ Ω t`. -/
theorem growingWidth_le_memWidth {U : X → X} {size : X → ℕ} {Ω : ℕ → Set X} {t : ℕ} :
    growingWidth U size Ω t ≤ MemoryWidth.memWidth U Ω t :=
  MemoryWidth.memWidth_mono_of_subset Set.inter_subset_left

/-! ## The guard family, at `Ω t = {n | n ≤ t}` on `ℕ` -/

/-- **The `(G2)`-part is EMPTY at the identity update**, whatever `size`: the orbit of any point is
constant, so no `size` is unbounded along it — `N := size x` refutes unboundedness outright. The
first half of guard (a): the separating witness. -/
theorem growingPart_id_eq_empty (size : X → ℕ) : GrowingPart (id : X → X) size = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  intro x hx
  obtain ⟨k, hk⟩ := hx (size x)
  simp only [Function.iterate_id, id_eq] at hk
  exact absurd hk (lt_irrefl _)

/-- **The `(G2)`-part is EVERYTHING at the successor update read by `id`**: `Nat.succ^[k] x = x + k`
is unbounded in `k` for every `x`, so every point already qualifies. The first half of guard (b):
the non-vacuity twin. -/
theorem growingPart_nat_succ_eq_univ : GrowingPart Nat.succ (id : ℕ → ℕ) = Set.univ := by
  rw [Set.eq_univ_iff_forall]
  intro x N
  refine ⟨N + 1, ?_⟩
  simp only [id_eq, Nat.succ_iterate]
  omega

/-- `mergeLaw (id : X → X)` fixes every class hit by `mergeMk`: `mergeLaw_mergeMk` at `U = id`
reduces the target back to the source, and `id`'s iterates change nothing further. What makes
`Reaches (id : X → X)` trivial (`isAntichain_reaches_id`). -/
private theorem mergeLaw_id_iterate_mergeMk (j : ℕ) (s : X) :
    (mergeLaw (id : X → X))^[j] (mergeMk (id : X → X) s) = mergeMk (id : X → X) s := by
  induction j with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ih, mergeLaw_mergeMk]; rfl

/-- **`Reaches` is trivial at the identity update**: the retained profile of `id`, at ANY stage
family, is an antichain — `id`'s induced law fixes every class outright, so no class ever reaches a
distinct one. -/
private theorem isAntichain_reaches_id (Ω : ℕ → Set X) (t : ℕ) :
    IsAntichain (MemoryWidth.Reaches (id : X → X)) (mergeStage (id : X → X) Ω t) := by
  rintro _ ⟨s, -, rfl⟩ _ ⟨s', -, rfl⟩ hne ⟨j, hj⟩
  rw [mergeLaw_id_iterate_mergeMk] at hj
  exact hne hj

/-- The retained profile of the identity update is the state stage itself, `mergeMk id` never
merging distinct states. -/
private theorem mergeStage_id_encard (Ω : ℕ → Set X) (t : ℕ) :
    (mergeStage (id : X → X) Ω t).encard = (Ω t).encard :=
  Function.Injective.encard_image (mergeMk_injective_of_injective Function.injective_id) (Ω t)

/-- The identity update's retained profile, at the initial-segment stage family, has exactly
`t + 1` classes — `Set.Iic t` counted, transported through `mergeStage_id_encard`. -/
private theorem mergeStage_id_slowClock_encard (t : ℕ) :
    (mergeStage (id : ℕ → ℕ) (fun t => Set.Iic t) t).encard = t + 1 := by
  rw [mergeStage_id_encard]
  simp [Set.Finite.encard_eq_coe_toFinset_card (Set.finite_Iic t), Nat.card_Iic]

/-- **Guard (a), the separating witness**: at the identity update on `ℕ` (any `size`, since the part
is empty regardless), the growing width is `0` at every stage of the initial-segment family, while
the unrestricted memory width there grows without bound — `mergeMk id` never merges, so the retained
profile is trivially an antichain (`isAntichain_reaches_id`) of the stage's own count
(`mergeStage_id_slowClock_encard`), `t + 1`. So `growingWidth` is a genuine restriction of
`memWidth`, not the same quantity under a different name. -/
theorem growingWidth_id_slowClock_eq_zero_memWidth_eq_succ (size : ℕ → ℕ) (t : ℕ) :
    growingWidth (id : ℕ → ℕ) size (fun t => Set.Iic t) t = 0 ∧
      MemoryWidth.memWidth (id : ℕ → ℕ) (fun t => Set.Iic t) t = t + 1 := by
  refine ⟨?_, ?_⟩
  · change MemoryWidth.memWidth (id : ℕ → ℕ)
        (fun t' => Set.Iic t' ∩ GrowingPart (id : ℕ → ℕ) size) t = 0
    rw [MemoryWidth.memWidth_eq_encard_of_isAntichain
        (isAntichain_reaches_id (fun t' => Set.Iic t' ∩ GrowingPart (id : ℕ → ℕ) size) t)]
    change (mergeMk (id : ℕ → ℕ) '' (Set.Iic t ∩ GrowingPart (id : ℕ → ℕ) size)).encard = 0
    rw [growingPart_id_eq_empty, Set.inter_empty, Set.image_empty, Set.encard_empty]
  · rw [MemoryWidth.memWidth_eq_encard_of_isAntichain
        (isAntichain_reaches_id (fun t => Set.Iic t) t), mergeStage_id_slowClock_encard]

/-- `memWidth` depends on the stage family only through the single value `mergeStage U Ω t`, so
equal retained profiles at `t` give equal widths there — the transport
`growingWidth_nat_succ_eq_one` needs to fold its restricted family back into the plain one. -/
private theorem memWidth_eq_of_mergeStage_eq {U : X → X} {Ω Ω' : ℕ → Set X} {t : ℕ}
    (h : mergeStage U Ω t = mergeStage U Ω' t) :
    MemoryWidth.memWidth U Ω t = MemoryWidth.memWidth U Ω' t := by
  unfold MemoryWidth.memWidth
  rw [h]

/-- Intersecting with the successor update's `(G2)`-part (`Set.univ`, by
`growingPart_nat_succ_eq_univ`) changes nothing. -/
private theorem inter_growingPart_nat_succ (Ω : ℕ → Set ℕ) (t : ℕ) :
    Ω t ∩ GrowingPart Nat.succ (id : ℕ → ℕ) = Ω t := by
  rw [growingPart_nat_succ_eq_univ, Set.inter_univ]

/-- **Guard (b), the non-vacuity twin**: at the successor update read by `id`, the `(G2)`-part is
everything (`growingPart_nat_succ_eq_univ`), so the restriction removes nothing and the growing
width agrees with `MemoryWidth.memWidth_nat_succ_eq_one`'s clock value, `1`, at any admitted stage
family. So the restriction is not vacuously zero. -/
theorem growingWidth_nat_succ_eq_one {Ω : ℕ → Set ℕ} {t : ℕ} (hne : (Ω t).Nonempty) :
    growingWidth Nat.succ (id : ℕ → ℕ) Ω t = 1 := by
  have hstage : mergeStage Nat.succ (fun t' => Ω t' ∩ GrowingPart Nat.succ (id : ℕ → ℕ)) t
      = mergeStage Nat.succ Ω t := by
    change mergeMk Nat.succ '' (Ω t ∩ GrowingPart Nat.succ (id : ℕ → ℕ)) = mergeMk Nat.succ '' Ω t
    rw [inter_growingPart_nat_succ]
  change MemoryWidth.memWidth Nat.succ (fun t' => Ω t' ∩ GrowingPart Nat.succ (id : ℕ → ℕ)) t = 1
  rw [memWidth_eq_of_mergeStage_eq hstage]
  exact MemoryWidth.memWidth_nat_succ_eq_one hne

end GrowingWidth

/-! ## Axiom audit

Both guard theorems are `#print axioms`-clean on the standard triple, and the guards below make
that build-enforced. -/

set_option linter.style.longLine false

/-- info: 'GrowingWidth.growingWidth_id_slowClock_eq_zero_memWidth_eq_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GrowingWidth.growingWidth_id_slowClock_eq_zero_memWidth_eq_succ

/-- info: 'GrowingWidth.growingWidth_nat_succ_eq_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GrowingWidth.growingWidth_nat_succ_eq_one
