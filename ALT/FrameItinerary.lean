/-
Copyright (c) 2026 Mykola Palamarchuk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mykola Palamarchuk
-/
module

public import ALT.PersistenceCapacity

-- Formal-check file, not Mathlib-destined: opt out of the house-style header linter.
set_option linter.style.header false

/-!
# The ledger's frame count and the truncated itinerary ([Persistence] §6, Theorem 6.5)

`ALT/PersistenceCapacity.lean` prices a two-frame family (`ledger_graded`, Theorem 6.4). This module
prices a family read at any finite set of times: a permutation `V` is **consistent** with the frames
held at `S` when it carries each frame at a time `t ∈ S` back to the frame one step earlier, and the
consistent permutations number one bijection per block of the *joint* partition the frames at `S`
induce (`itinerary`, `Consistent`, `consistent_card`). Theorem 6.5(ii)'s `∏_z c^B_z!` is this count
at `S = Bminus B`, the members of `B` whose predecessor is also in `B` (`consistent_card_bminus`);
clause (i) is the same count read at the *truncated itinerary* `R_{k−1}` rather than at its
`U`-shift (`consistent_card_consecutive`); and at `S = {1}` the count collapses to Theorem 6.4's own
coset, `card_stabilizer_lens (ℓ 0)` (`consistent_card_one`), so the general statement still says
Theorem 6.4 at its bottom end.

Theorem 6.5's `K (U) ≤ …` display itself — the decoder that loads a variable-length list of frame
codes and pays `elen` per element — is machine-checked too, in `PersistenceCapacity.lean`
(`ledger_itinerary`, `ledger_itinerary_consecutive`): a new `Primrec` construction rather than a
generalization of `gradedBuilder`, over an explicit `List ℕ` of held times. This module's own
`consistentWith_sort_eq_consistent_bminus`/`consistentWith_range_eq_consistent_ico` identify that
list-indexed set with `Consistent` at `Bminus B`/`Finset.Ico 1 k` exactly, so
`ledger_itinerary_bminus`/`ledger_itinerary_range` below restate the two displays at `B`/`k`
directly, with `N` supplied by `consistent_card_bminus`/`consistent_card_consecutive`.

A sharper fact holds at an injective itinerary ([Persistence] §8, Proposition 8.38(i)): when
`itinerary ℓ S` is injective, `U` is the ONLY permutation consistent with the frames held at `S`,
not merely the count's own witness — `consistent_unique_of_injective`, with
`consistent_unique_of_injective_bminus` its instance at `S = Bminus B`, the set Proposition 8.38's
own argument reads.
-/


@[expose] public section

namespace FrameItinerary

open PersistenceCapacity AdditiveComplexity Equiv Equiv.Perm MulAction Nat

-- `•` on lenses is the relabelling action `U • ℓ = ℓ ∘ U⁻¹` ([Persistence] §7, Lemma 7.1's
-- convention); `PersistenceCapacity`'s own local instance of it does not export past that file's
-- `section Collapse`, so it is re-opened here for the same codomain-generic reason.
attribute [local instance] arrowAction

variable {n m : ℕ}

/-- `(U • ℓ) x = ℓ (U⁻¹ x)`, restated because `PersistenceCapacity.smul_lens_apply` is file-private.
-/
private theorem smul_lens_apply' {α β : Type*} (U : Perm α) (ℓ : α → β) (x : α) :
    (U • ℓ) x = ℓ (U⁻¹ x) := rfl

/-- A permutation stabilizes a lens exactly when it preserves the lens's fibers, restated because
`PersistenceCapacity.mem_stabilizer_lens` is file-private. -/
private theorem mem_stabilizer_lens' {α β : Type*} {U : Perm α} {ℓ : α → β} :
    U ∈ stabilizer (Perm α) ℓ ↔ ∀ x, ℓ (U x) = ℓ x := by
  constructor
  · intro h x
    have := congrFun (mem_stabilizer_iff.mp h) (U x)
    rw [smul_lens_apply'] at this
    simpa using this.symm
  · intro h
    refine mem_stabilizer_iff.mpr (funext fun x => ?_)
    rw [smul_lens_apply']
    have := h (U⁻¹ x)
    simpa using this.symm

/-! ### The one-step identity -/

/-- **Persistence, one step at a time** ([Persistence] §6, the identity Theorem 6.5's proof reads at
each `t ∈ B^-`): `PermCarries` gives `ℓ t ∘ U ^ t = ℓ 0`; solving two consecutive instances of that
against each other gives the step form `ℓ t (U x) = ℓ (t − 1) x`, holding at every `x` rather than
merely along `U`'s own orbit through a fixed point. -/
theorem permCarries_step {U : Perm (Fin n)} {ℓ : ℕ → Fin n → Fin m} (h : PermCarries U ℓ)
    {t : ℕ} (ht : 1 ≤ t) (x : Fin n) : ℓ t (U x) = ℓ (t - 1) x := by
  set s := t - 1 with hs
  have hts : t = s + 1 := by omega
  set z : Fin n := (U ^ s)⁻¹ x with hz
  have hxz : (U ^ s) z = x := by rw [hz]; simp
  have h0 : ℓ s x = ℓ 0 z := by rw [← hxz]; exact h.2 s z
  have hUx : (U ^ (s + 1)) z = U x := by rw [_root_.pow_succ', Equiv.Perm.mul_apply, hxz]
  have h1 : ℓ t (U x) = ℓ 0 z := by rw [hts, ← hUx]; exact h.2 (s + 1) z
  rw [h1, h0]

/-! ### The consistent-permutation count -/

/-- **The itinerary read at a set of times**: the frames held at `S`, packaged as one lens with
codomain `↥S → Fin m`. Its stabilizer's fibers are the blocks of the joint partition
`⋀_{t ∈ S} P_t`. -/
def itinerary (ℓ : ℕ → Fin n → Fin m) (S : Finset ℕ) : Fin n → (↥S → Fin m) :=
  fun x t => ℓ (t : ℕ) x

/-- **Consistency with the frames held at `S`** ([Persistence] §6, Theorem 6.5's proof): a
permutation `V` is consistent when it carries every `t ∈ S`'s frame back to the frame one step
earlier, `ℓ t (V x) = ℓ (t − 1) x`. -/
def Consistent (ℓ : ℕ → Fin n → Fin m) (S : Finset ℕ) : Set (Perm (Fin n)) :=
  {V | ∀ t ∈ S, ∀ x, ℓ t (V x) = ℓ (t - 1) x}

private theorem mem_consistent_of_permCarries {U : Perm (Fin n)} {ℓ : ℕ → Fin n → Fin m}
    (hcar : PermCarries U ℓ) {S : Finset ℕ} (hS : 0 ∉ S) : U ∈ Consistent ℓ S := by
  intro t ht x
  have ht1 : 1 ≤ t := by
    rcases Nat.eq_zero_or_pos t with h0 | hpos
    · exact absurd (h0 ▸ ht) hS
    · exact hpos
  exact permCarries_step hcar ht1 x

private theorem mem_stabilizer_itinerary_of_mem_consistent
    {U : Perm (Fin n)} {ℓ : ℕ → Fin n → Fin m} (hcar : PermCarries U ℓ) {S : Finset ℕ}
    (hS : 0 ∉ S) {V : Perm (Fin n)} (hV : V ∈ Consistent ℓ S) :
    V * U⁻¹ ∈ stabilizer (Perm (Fin n)) (itinerary ℓ S) := by
  have hU : U ∈ Consistent ℓ S := mem_consistent_of_permCarries hcar hS
  rw [mem_stabilizer_lens']
  intro x
  funext t
  have hty : (t : ℕ) ∈ S := t.2
  change ℓ (t : ℕ) ((V * U⁻¹) x) = ℓ (t : ℕ) x
  have h1 : ℓ (t : ℕ) (V (U⁻¹ x)) = ℓ ((t : ℕ) - 1) (U⁻¹ x) := hV (t : ℕ) hty (U⁻¹ x)
  have hinv : U (U⁻¹ x) = x := Equiv.apply_symm_apply U x
  have h2 : ℓ (t : ℕ) x = ℓ ((t : ℕ) - 1) (U⁻¹ x) := by
    have hh := hU (t : ℕ) hty (U⁻¹ x)
    rwa [hinv] at hh
  rw [Equiv.Perm.mul_apply, h1, ← h2]

private theorem mem_consistent_of_mem_stabilizer_itinerary
    {U : Perm (Fin n)} {ℓ : ℕ → Fin n → Fin m} (hcar : PermCarries U ℓ) {S : Finset ℕ}
    (hS : 0 ∉ S) {W : Perm (Fin n)} (hW : W ∈ stabilizer (Perm (Fin n)) (itinerary ℓ S)) :
    W * U ∈ Consistent ℓ S := by
  have hU : U ∈ Consistent ℓ S := mem_consistent_of_permCarries hcar hS
  rw [mem_stabilizer_lens'] at hW
  intro t ht x
  rw [Equiv.Perm.mul_apply]
  have hWt : ℓ t (W (U x)) = ℓ t (U x) := congrFun (hW (U x)) ⟨t, ht⟩
  rw [hWt]
  exact hU t ht x

/-- **The consistent permutations are one coset of the joint stabilizer** ([Persistence] §6, the
route Theorem 6.5's proof takes): `V ↦ V * U⁻¹` bijects `Consistent ℓ S` onto
`stabilizer (itinerary ℓ S)`, using `permCarries_step` at each `t ∈ S` to place `U` itself in
`Consistent ℓ S` first. -/
private noncomputable def consistentEquivStab {U : Perm (Fin n)} {ℓ : ℕ → Fin n → Fin m}
    (hcar : PermCarries U ℓ) {S : Finset ℕ} (hS : 0 ∉ S) :
    ↥(Consistent ℓ S) ≃ ↥(stabilizer (Perm (Fin n)) (itinerary ℓ S)) where
  toFun V := ⟨V.1 * U⁻¹, mem_stabilizer_itinerary_of_mem_consistent hcar hS V.2⟩
  invFun W := ⟨W.1 * U, mem_consistent_of_mem_stabilizer_itinerary hcar hS W.2⟩
  left_inv V := Subtype.ext (by group)
  right_inv W := Subtype.ext (by group)

/-- **The ledger at any frames, counting core** ([Persistence] §6, Theorem 6.5's `∏_z c_z!`, at
general `S`): the permutations consistent with the frames held at `S` number one bijection per
block of the joint partition `⋀_{t ∈ S} P_t` — `0 ∉ S` is required so every constraint has a
genuine predecessor frame in hand. The product runs over the WHOLE codomain `↥S → Fin m`; an
unoccupied block contributes `0! = 1`, which is why this matches the occupied-block form Theorem
6.5 states. -/
theorem consistent_card {U : Perm (Fin n)} {ℓ : ℕ → Fin n → Fin m} (hcar : PermCarries U ℓ)
    {S : Finset ℕ} (hS : 0 ∉ S) :
    Nat.card ↥(Consistent ℓ S)
      = ∏ z : (↥S → Fin m), (Nat.card {x : Fin n // itinerary ℓ S x = z})! := by
  rw [Nat.card_congr (consistentEquivStab hcar hS)]
  exact card_stabilizer_lens_dom (itinerary ℓ S)

/-! ### Proposition 8.38(i): uniqueness at a separating set -/

/-- **At a separating set the world is the unique consistent permutation** ([Persistence] §8,
Proposition 8.38(i)): when `itinerary ℓ S` is injective, `x` and `U x` share exactly the pattern
`itinerary ℓ S` assigns to `x`'s predecessor under any `V ∈ Consistent ℓ S` — since both `U` and `V`
carry the frames at `S` back to the frames one step earlier — so injectivity forces `V x = U x` at
every `x` directly, with no appeal to `consistent_card`'s counting route. -/
theorem consistent_unique_of_injective {U : Perm (Fin n)} {ℓ : ℕ → Fin n → Fin m}
    (hcar : PermCarries U ℓ) {S : Finset ℕ} (hS : 0 ∉ S)
    (hinj : Function.Injective (itinerary ℓ S)) :
    Consistent ℓ S = {U} := by
  have hU : U ∈ Consistent ℓ S := mem_consistent_of_permCarries hcar hS
  refine Set.eq_singleton_iff_unique_mem.mpr ⟨hU, fun V hV => Equiv.ext fun x => hinj ?_⟩
  funext t
  change ℓ (t : ℕ) (V x) = ℓ (t : ℕ) (U x)
  rw [hV (t : ℕ) t.2 x, hU (t : ℕ) t.2 x]

/-! ### Theorem 6.5(ii): any frames at all -/

/-- **`B^-`** ([Persistence] §6, Theorem 6.5(ii)): the members of `B` whose predecessor is also in
`B` — the only times at which a `V` consistent with the frames held at `B` is genuinely constrained,
since those are the times at which both `ℓ t` and `ℓ (t − 1)` are in hand. -/
def Bminus (B : Finset ℕ) : Finset ℕ := B.filter (fun t => 1 ≤ t ∧ t - 1 ∈ B)

private theorem zero_not_mem_Bminus (B : Finset ℕ) : (0 : ℕ) ∉ Bminus B := by
  intro h
  have := (Finset.mem_filter.mp h).2.1
  omega

/-- **The ledger at any frames** ([Persistence] §6, Theorem 6.5(ii)'s counting core): for an
arbitrary finite set of times `B`, the permutations consistent with the frames held at `B` — read at
exactly the times `Bminus B` the proof isolates — number one bijection per block of
`⋀_{t ∈ Bminus B} P_t`. -/
theorem consistent_card_bminus {U : Perm (Fin n)} {ℓ : ℕ → Fin n → Fin m} (hcar : PermCarries U ℓ)
    (B : Finset ℕ) :
    Nat.card ↥(Consistent ℓ (Bminus B))
      = ∏ z : (↥(Bminus B) → Fin m), (Nat.card {x : Fin n // itinerary ℓ (Bminus B) x = z})! :=
  consistent_card hcar (zero_not_mem_Bminus B)

/-- **The decoder at `Bminus B`** ([Persistence] §8, Proposition 8.38(i), read at the times
Theorem 6.5(ii) and Proposition 8.20's proof draw from): `consistent_unique_of_injective` at
`S := Bminus B`, which already excludes `0` (`zero_not_mem_Bminus`). -/
theorem consistent_unique_of_injective_bminus {U : Perm (Fin n)} {ℓ : ℕ → Fin n → Fin m}
    (hcar : PermCarries U ℓ) (B : Finset ℕ)
    (hinj : Function.Injective (itinerary ℓ (Bminus B))) :
    Consistent ℓ (Bminus B) = {U} :=
  consistent_unique_of_injective hcar (zero_not_mem_Bminus B) hinj

/-! ### Theorem 6.5(i): consecutive frames, at the truncated itinerary -/

private def icoShiftEquiv (k : ℕ) : ↥(Finset.Ico 1 k) ≃ Fin (k - 1) where
  toFun t := ⟨t.1 - 1, by
    have h := t.2
    simp only [Finset.mem_Ico] at h
    omega⟩
  invFun j := ⟨j.1 + 1, by
    have h := j.2
    simp only [Finset.mem_Ico]
    omega⟩
  left_inv t := by
    have h := t.2
    simp only [Finset.mem_Ico] at h
    ext
    simp only
    omega
  right_inv j := by
    ext
    simp only
    omega

/-- **The ledger at `k` consecutive frames, read at the truncated itinerary**
([Persistence] §6, Theorem 6.5(i)): for `k ≥ 2`, the permutations consistent with frames
`ℓ 0, …, ℓ (k − 1)` number one bijection per block of `R_{k−1} := ⋀_{t < k−1} P_t` — the
truncated itinerary itself, not its `U`-shift `⋀_{1 ≤ t < k} P_t` that `consistent_card` reads
directly. `U` is the transport between the two: `permCarries_step` shows
`itinerary ℓ (Ico 1 k) (U x)` reindexes to `R_{k−1} x` along `Finset.Ico 1 k ≃ Fin (k − 1)`,
`t ↦ t − 1`, and `x ↦ U⁻¹ x` carries a fiber of one partition onto the corresponding fiber of the
other. -/
theorem consistent_card_consecutive {U : Perm (Fin n)} {ℓ : ℕ → Fin n → Fin m}
    (hcar : PermCarries U ℓ) {k : ℕ} (_hk : 2 ≤ k) :
    Nat.card ↥(Consistent ℓ (Finset.Ico 1 k))
      = ∏ z : (Fin (k - 1) → Fin m),
          (Nat.card {x : Fin n // (fun j : Fin (k - 1) => ℓ (j : ℕ) x) = z})! := by
  have h0 : (0 : ℕ) ∉ Finset.Ico 1 k := by simp
  rw [consistent_card hcar h0]
  set e := icoShiftEquiv k with he
  set R : Fin n → Fin (k - 1) → Fin m := fun x j => ℓ (j : ℕ) x with hR
  have hUinv : ∀ y : Fin n, U (U⁻¹ y) = y := fun y => Equiv.apply_symm_apply U y
  have heinv : ∀ j : Fin (k - 1), e (e.symm j) = j := fun j => Equiv.apply_symm_apply e j
  have hstep : ∀ (x : Fin n) (t : ↥(Finset.Ico 1 k)),
      itinerary ℓ (Finset.Ico 1 k) (U x) t = R x (e t) := by
    intro x t
    have ht1 : 1 ≤ (t : ℕ) := (Finset.mem_Ico.mp t.2).1
    change ℓ (t : ℕ) (U x) = ℓ ((e t : ℕ)) x
    rw [permCarries_step hcar ht1 x]
    rfl
  have hfiber : ∀ z : (↥(Finset.Ico 1 k) → Fin m),
      Nat.card {y : Fin n // itinerary ℓ (Finset.Ico 1 k) y = z}
        = Nat.card {x : Fin n // R x = z ∘ e.symm} := by
    intro z
    refine Nat.card_congr (Equiv.subtypeEquiv U⁻¹ fun y => ?_)
    constructor
    · intro hy
      funext j
      have hxj : R ((U⁻¹ : Perm (Fin n)) y) j
          = itinerary ℓ (Finset.Ico 1 k) (U ((U⁻¹ : Perm (Fin n)) y)) (e.symm j) := by
        have hs := hstep ((U⁻¹ : Perm (Fin n)) y) (e.symm j)
        rw [heinv j] at hs
        exact hs.symm
      rw [hxj, hUinv, hy]
      rfl
    · intro hx
      funext t
      have hcf := congrFun hx (e t)
      have hxj : R ((U⁻¹ : Perm (Fin n)) y) (e t) = itinerary ℓ (Finset.Ico 1 k) y t := by
        have hs := hstep ((U⁻¹ : Perm (Fin n)) y) t
        rw [hUinv] at hs
        exact hs.symm
      rw [hxj] at hcf
      rw [hcf]
      simp
  refine Fintype.prod_equiv (e.arrowCongr (Equiv.refl (Fin m)))
    (fun z => (Nat.card {y : Fin n // itinerary ℓ (Finset.Ico 1 k) y = z})!)
    (fun z' => (Nat.card {x : Fin n // R x = z'})!) fun z => ?_
  have hzeq : (e.arrowCongr (Equiv.refl (Fin m))) z = z ∘ ⇑e.symm := by
    funext a
    simp [Equiv.arrowCongr_apply]
  rw [hzeq, hfiber z]

/-! ### Non-vacuity: `k = 2` is Theorem 6.4 -/

/-- **The general theorem still says Theorem 6.4 at `k = 2`** ([Persistence] §6, Theorem 6.5's
bottom end): consistency at the single time `S = {1}` is exactly Theorem 6.4's own coset condition
`ℓ 1 (V x) = ℓ 0 x`, so the count is `card_stabilizer_lens (ℓ 0)`'s value — `permCarries_frame_one`
gives `ℓ 1 = U • ℓ 0`, matching the fibers. -/
theorem consistent_card_one {U : Perm (Fin n)} {ℓ : ℕ → Fin n → Fin m} (hcar : PermCarries U ℓ) :
    Nat.card ↥(Consistent ℓ ({1} : Finset ℕ))
      = ∏ i : Fin m, (Nat.card {x : Fin n // ℓ 0 x = i})! := by
  have h1 : ℓ 1 = U • ℓ 0 := permCarries_frame_one hcar.2
  have key : ∀ V : Perm (Fin n), V ∈ Consistent ℓ ({1} : Finset ℕ) ↔
      U⁻¹ * V ∈ stabilizer (Perm (Fin n)) (ℓ 0) := by
    intro V
    rw [mem_stabilizer_lens']
    constructor
    · intro hV x
      have hVx := hV 1 (Finset.mem_singleton_self 1) x
      rw [h1, smul_lens_apply'] at hVx
      rw [Equiv.Perm.mul_apply]
      exact hVx
    · intro hV t ht x
      have hteq : t = 1 := Finset.mem_singleton.mp ht
      subst hteq
      have hVx := hV x
      rw [Equiv.Perm.mul_apply] at hVx
      change ℓ 1 (V x) = ℓ (1 - 1) x
      rw [h1, smul_lens_apply']
      exact hVx
  have hcard : Nat.card ↥(Consistent ℓ ({1} : Finset ℕ))
      = Nat.card ↥(stabilizer (Perm (Fin n)) (ℓ 0)) := by
    apply Nat.card_congr
    exact
      { toFun := fun V => ⟨U⁻¹ * V.1, (key V.1).mp V.2⟩
        invFun := fun W => ⟨U * W.1, (key (U * W.1)).mpr (by
          rw [show U⁻¹ * (U * W.1) = W.1 by group]; exact W.2)⟩
        left_inv := fun V => Subtype.ext (by group)
        right_inv := fun W => Subtype.ext (by group) }
  rw [hcard]
  exact card_stabilizer_lens (ℓ 0)

/-! ### Theorem 6.5's `K (U) ≤ …` display

`PersistenceCapacity.ConsistentWith` reads the same consistency condition as `Consistent` here, but
over an explicit `List ℕ` of held times rather than a `Finset ℕ` — the currency the decoder's
`Primrec` construction needs. The two bridge lemmas below identify the sets exactly, so
`PersistenceCapacity.ledger_itinerary`/`ledger_itinerary_consecutive` — the machine-checked decoder,
built there — apply here with `N` supplied from
`consistent_card_bminus`/`consistent_card_consecutive`. -/

/-- **`ConsistentWith` at a sorted `B`, `Consistent` at `Bminus B`, are the same set**: both name
exactly the pairs `t = t' + 1` with `t, t' ∈ B`, `ConsistentWith` over the pair directly and
`Consistent` over `t ∈ Bminus B` with `t' := t - 1` read off the definition. Sortedness is not
load-bearing for the identity — only for which `List ℕ` the decoder below is handed. -/
theorem consistentWith_sort_eq_consistent_bminus (ℓ : ℕ → Fin n → Fin m) (B : Finset ℕ) :
    ConsistentWith ℓ (B.sort (· ≤ ·)) = Consistent ℓ (Bminus B) := by
  ext V
  simp only [ConsistentWith, Consistent, Set.mem_ofPred_eq, Finset.mem_sort, Bminus,
    Finset.mem_filter]
  constructor
  · intro h t ⟨htB, ht1, ht1B⟩ x
    exact h t htB (t - 1) ht1B (by omega) x
  · intro h t htB t' ht'B hstep x
    have ht1B' : t - 1 ∈ B := by rwa [show t - 1 = t' from by omega]
    have hstep' := h t ⟨htB, by omega, ht1B'⟩ x
    rwa [show t - 1 = t' from by omega] at hstep'

/-- **`ConsistentWith` at `List.range k`, `Consistent` at `Finset.Ico 1 k`, are the same set**: the
pairs `t = t' + 1` inside `[0, k)` are exactly the times `t ∈ [1, k)`, `t' := t - 1`. -/
theorem consistentWith_range_eq_consistent_ico (ℓ : ℕ → Fin n → Fin m) (k : ℕ) :
    ConsistentWith ℓ (List.range k) = Consistent ℓ (Finset.Ico 1 k) := by
  ext V
  simp only [ConsistentWith, Consistent, Set.mem_ofPred_eq, List.mem_range, Finset.mem_Ico]
  constructor
  · intro h t ⟨ht1, htk⟩ x
    exact h t htk (t - 1) (by omega) (by omega) x
  · intro h t htk t' ht'k hstep x
    have hstep' := h t ⟨by omega, htk⟩ x
    rwa [show t - 1 = t' from by omega] at hstep'

/-- A `List.map`/`List.sum` over a `Finset`'s sort is that `Finset`'s own sum — the bridge from
`ledger_itinerary`'s list-indexed frame/size sums to the `Finset`-indexed sums Theorem 6.5(ii)'s
own `∑_{t∈B}` notation writes. -/
private theorem sum_map_sort_eq_finset_sum (B : Finset ℕ) (f : ℕ → ℕ) :
    ((B.sort (· ≤ ·)).map f).sum = ∑ t ∈ B, f t := by
  rw [Finset.sum_eq_multiset_sum, ← Finset.sort_eq (r := (· ≤ ·)) B]
  rfl

/-- **The ledger at any frames** ([Persistence] §6, Theorem 6.5(ii)'s display), read at `B`
directly: `ledger_itinerary` at `bs := B.sort (· ≤ ·)`, with the frame/size sums restated as
`Finset` sums over `B`, the length as `B.card`, and `N` supplied exactly by
`consistent_card_bminus`. -/
theorem ledger_itinerary_bminus (hn : 0 < n) {U : Perm (Fin n)} {ℓ : ℕ → Fin n → Fin m}
    (hcar : PermCarries U ℓ) (B : Finset ℕ)
    (c : ℕ → Nat.Partrec.Code)
    (hc : ∀ t ∈ B, (c t).eval 0 = Part.some (lensCode (ℓ t))) :
    KE (lensCode U)
      ≤ (∑ t ∈ B, elen (c t))
        + (15 + elen dbl) * (∑ t ∈ B, Nat.size t)
        + (39 + elen dbl) * B.card
        + (15 + elen dbl) * Nat.size (∏ z : (↥(Bminus B) → Fin m),
            (Nat.card {x : Fin n // itinerary ℓ (Bminus B) x = z})!)
        + (15 + elen dbl) * Nat.size n
        + (elen itinBuilder + 2 * (15 + elen dbl) + 18) := by
  have hUmem : U ∈ ConsistentWith ℓ (B.sort (· ≤ ·)) := by
    rw [consistentWith_sort_eq_consistent_bminus]
    exact mem_consistent_of_permCarries hcar (zero_not_mem_Bminus B)
  have hc' : ∀ t ∈ B.sort (· ≤ ·), (c t).eval 0 = Part.some (lensCode (ℓ t)) := by
    intro t ht
    exact hc t (Finset.mem_sort (· ≤ ·) |>.mp ht)
  have hN : Nat.card ↥(ConsistentWith ℓ (B.sort (· ≤ ·)))
      ≤ ∏ z : (↥(Bminus B) → Fin m), (Nat.card {x : Fin n // itinerary ℓ (Bminus B) x = z})! := by
    rw [consistentWith_sort_eq_consistent_bminus, consistent_card_bminus hcar]
  have hbound := ledger_itinerary hn (B.sort (· ≤ ·)) hUmem c hc' _ hN
  rwa [sum_map_sort_eq_finset_sum B (fun t => elen (c t)), sum_map_sort_eq_finset_sum B Nat.size,
    Finset.length_sort] at hbound

/-- **The ledger at `k` consecutive frames** ([Persistence] §6, Theorem 6.5(i)'s display):
`ledger_itinerary_consecutive` at `bs := List.range k`, with `N` supplied exactly by
`consistent_card_consecutive`, so the index is read at the truncated itinerary `R_{k−1}` itself. -/
theorem ledger_itinerary_range (hn : 0 < n) {U : Perm (Fin n)} {ℓ : ℕ → Fin n → Fin m}
    (hcar : PermCarries U ℓ) {k : ℕ} (hk : 2 ≤ k)
    (c : ℕ → Nat.Partrec.Code)
    (hc : ∀ t < k, (c t).eval 0 = Part.some (lensCode (ℓ t))) :
    KE (lensCode U)
      ≤ ((List.range k).map fun t => elen (c t)).sum
        + 15 * k
        + (15 + elen dbl) * Nat.size k
        + (15 + elen dbl) * Nat.size (∏ z : (Fin (k - 1) → Fin m),
            (Nat.card {x : Fin n // (fun j : Fin (k - 1) => ℓ (j : ℕ) x) = z})!)
        + (15 + elen dbl) * Nat.size n
        + (elen itinBuilder + elen rangeCode + 3 * (15 + elen dbl) + 18) := by
  have hUmem : U ∈ ConsistentWith ℓ (List.range k) := by
    rw [consistentWith_range_eq_consistent_ico]
    exact mem_consistent_of_permCarries hcar (by simp)
  have hN : Nat.card ↥(ConsistentWith ℓ (List.range k))
      ≤ ∏ z : (Fin (k - 1) → Fin m),
          (Nat.card {x : Fin n // (fun j : Fin (k - 1) => ℓ (j : ℕ) x) = z})! := by
    rw [consistentWith_range_eq_consistent_ico, consistent_card_consecutive hcar hk]
  exact ledger_itinerary_consecutive hn k hUmem c hc _ hN

/-! ### Proposition 8.30: a reading constant off an invariant region -/

/-- **A region left unread carries no constraint** ([Persistence] §8, Proposition 8.30's own
reading, generalized off its specific construction): when the reference frame is constant off a
`U`-invariant block `B`, EVERY frame is constant off `B`, and at the SAME value — `B`'s complement
is closed under `U` and hence under every `(U ^ t)⁻¹` (`image_perm_eq`/`mem_iff_apply_mem`,
[PersistenceCapacity]), so `permCarries_step`'s identity `ℓ t z = ℓ 0 ((U ^ t)⁻¹ z)` reads the same
off-`B` value at every `t`. `Bᶜ` therefore sits inside a single block of the joint partition
`itinerary ℓ S` induces, and the whole symmetric group of `Bᶜ` stays consistent with the frames held
at `S`: the frames pin down nothing at all on the complement. -/
theorem consistent_card_ge_factorial_compl {U : Perm (Fin n)} {ℓ : ℕ → Fin n → Fin m}
    (hcar : PermCarries U ℓ) {S : Finset ℕ} (hS : 0 ∉ S)
    {B : Finset (Fin n)} (hB : ∀ i ∈ B, U i ∈ B)
    (hconst : ∀ x ∉ B, ∀ y ∉ B, ℓ 0 x = ℓ 0 y) :
    (Bᶜ.card)! ≤ Nat.card ↥(Consistent ℓ S) := by
  rw [consistent_card hcar hS]
  rcases Finset.eq_empty_or_nonempty (Bᶜ : Finset (Fin n)) with hEmpty | ⟨x0, hx0⟩
  · simp only [hEmpty, Finset.card_empty, Nat.factorial_zero]
    exact Finset.one_le_prod fun z _ => Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero _)
  · have hx0' : x0 ∉ B := Finset.mem_compl.mp hx0
    have hBcInv : ∀ i ∈ (Bᶜ : Finset (Fin n)), U⁻¹ i ∈ (Bᶜ : Finset (Fin n)) := by
      intro i hi
      simp only [Finset.mem_compl] at hi ⊢
      intro hmem
      exact hi (by simpa using (mem_iff_apply_mem hB (U⁻¹ i)).mpr hmem)
    have hpowBc : ∀ (t : ℕ) (x : Fin n), x ∈ (Bᶜ : Finset (Fin n)) →
        (U⁻¹ ^ t) x ∈ (Bᶜ : Finset (Fin n)) := fun t x hx => pow_mem_of_closed hBcInv t hx
    have hconstall : ∀ (t : ℕ) (y : Fin n), y ∈ (Bᶜ : Finset (Fin n)) → ℓ t y = ℓ 0 x0 := by
      intro t y hy
      have hyB : (U ^ t)⁻¹ y ∈ (Bᶜ : Finset (Fin n)) := by
        rw [← inv_pow]; exact hpowBc t y hy
      have hstep : ℓ t y = ℓ 0 ((U ^ t)⁻¹ y) := by
        have h := hcar.2 t ((U ^ t)⁻¹ y)
        have happly : (U ^ t) ((U ^ t)⁻¹ y) = y := Equiv.apply_symm_apply (U ^ t) y
        rwa [happly] at h
      rw [hstep]
      exact hconst _ (Finset.mem_compl.mp hyB) x0 hx0'
    have hitfib : ∀ y ∈ (Bᶜ : Finset (Fin n)), itinerary ℓ S y = itinerary ℓ S x0 := by
      intro y hy
      funext t
      change ℓ (t : ℕ) y = ℓ (t : ℕ) x0
      rw [hconstall (t : ℕ) y hy, hconstall (t : ℕ) x0 hx0]
    have hinj : Function.Injective (fun x : ↥(Bᶜ : Finset (Fin n)) =>
        (⟨x.1, hitfib x.1 x.2⟩ : {z : Fin n // itinerary ℓ S z = itinerary ℓ S x0})) := by
      intro a b hab
      exact Subtype.ext (by simpa using hab)
    have hcard_le : Nat.card ↥(Bᶜ : Finset (Fin n))
        ≤ Nat.card {z : Fin n // itinerary ℓ S z = itinerary ℓ S x0} :=
      Nat.card_le_card_of_injective _ hinj
    have hBcNatCard : Nat.card ↥(Bᶜ : Finset (Fin n)) = Bᶜ.card := by
      rw [Nat.card_eq_fintype_card, Fintype.card_coe]
    have hle : Bᶜ.card ≤ Nat.card {z : Fin n // itinerary ℓ S z = itinerary ℓ S x0} :=
      hBcNatCard ▸ hcard_le
    calc (Bᶜ.card)! ≤ (Nat.card {z : Fin n // itinerary ℓ S z = itinerary ℓ S x0})! :=
          Nat.factorial_le hle
      _ ≤ ∏ z : (↥S → Fin m), (Nat.card {x : Fin n // itinerary ℓ S x = z})! :=
          Finset.single_le_prod (f := fun z => (Nat.card {x : Fin n // itinerary ℓ S x = z})!)
            (fun z _ => Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero _))
            (Finset.mem_univ (itinerary ℓ S x0))

/-! ### Two load-bearing hypotheses

Both witnesses are checked exhaustively over the concrete family below (`n = 3`, `m = 2`): each
shows `Consistent` collapses to the empty set while the itinerary's block-count product stays
positive, so the two sides of `consistent_card`'s conclusion cannot agree — the count formula
genuinely needs the hypothesis it is dropped from. -/

private def guardSkewU : Perm (Fin 3) := Equiv.swap 0 1
private def guardSkewFrame : Fin 3 → Fin 2 := ![0, 1, 0]
private def guardSkewLens : ℕ → Fin 3 → Fin 2 := fun t => guardSkewFrame ∘ ⇑(guardSkewU ^ t)⁻¹

private theorem guardSkewLens_carries : PermCarries guardSkewU guardSkewLens := by
  refine ⟨by decide, fun t x => ?_⟩
  change guardSkewFrame ((guardSkewU ^ t)⁻¹ ((guardSkewU ^ t) x)) = guardSkewFrame x
  simp

/-- **`0 ∉ S` is load-bearing** ([Persistence] §6, Theorem 6.5(ii)'s hypothesis): at `n = 3`,
`m = 2`, `U = swap 0 1`, `ℓ 0 = ![0, 1, 0]`, `ℓ t := ℓ 0 ∘ (U ^ t)⁻¹` — a genuine `PermCarries`
family (`guardSkewLens_carries`) — `Consistent ℓ {0, 1}` is empty (`{0, 1}` names `S`, not
`Bminus S`, so the `t = 0` constraint fires against the nonexistent frame `ℓ (0 - 1) = ℓ 0`) while
the block-count product is positive, so `consistent_card`'s conclusion fails without the
hypothesis. -/
private theorem guard_zeroS_load_bearing :
    Nat.card ↥(Consistent guardSkewLens ({0, 1} : Finset ℕ))
      ≠ ∏ z : (↥({0, 1} : Finset ℕ) → Fin 2),
          (Nat.card {x : Fin 3 // itinerary guardSkewLens ({0, 1} : Finset ℕ) x = z})! := by
  have hempty : Consistent guardSkewLens ({0, 1} : Finset ℕ) = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    intro V
    simp only [Consistent, Set.mem_ofPred_eq]
    revert V
    decide
  have hpos : (∏ z : (↥({0, 1} : Finset ℕ) → Fin 2),
      (Nat.card {x : Fin 3 // itinerary guardSkewLens ({0, 1} : Finset ℕ) x = z})!) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun z _ => Nat.factorial_ne_zero _
  rw [hempty, Nat.card_of_isEmpty]
  exact hpos.symm

private def guardArbitraryLens : ℕ → Fin 3 → Fin 2
  | 0 => ![0, 0, 0]
  | 1 => ![1, 0, 0]
  | _ => ![0, 0, 1]

/-- **`PermCarries` is load-bearing** ([Persistence] §6, Theorem 6.5's carried-family hypothesis):
at `n = 3`, `m = 2`, frames `ℓ 0 = ![0, 0, 0]`, `ℓ 1 = ![1, 0, 0]`, `ℓ 2 = ![0, 0, 1]` — no
permutation world carries this family, since `ℓ 0` is not even surjective — `Consistent ℓ {1}` is
empty while the block-count product is positive, so `consistent_card`'s conclusion fails for an
arbitrary lens family not known to arise from any `PermCarries U ℓ`. -/
private theorem guard_permCarries_load_bearing :
    Nat.card ↥(Consistent guardArbitraryLens ({1} : Finset ℕ))
      ≠ ∏ z : (↥({1} : Finset ℕ) → Fin 2),
          (Nat.card {x : Fin 3 // itinerary guardArbitraryLens ({1} : Finset ℕ) x = z})! := by
  have hempty : Consistent guardArbitraryLens ({1} : Finset ℕ) = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    intro V
    simp only [Consistent, Set.mem_ofPred_eq]
    revert V
    decide
  have hpos : (∏ z : (↥({1} : Finset ℕ) → Fin 2),
      (Nat.card {x : Fin 3 // itinerary guardArbitraryLens ({1} : Finset ℕ) x = z})!) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun z _ => Nat.factorial_ne_zero _
  rw [hempty, Nat.card_of_isEmpty]
  exact hpos.symm

private def guardOtherV : Perm (Fin 3) := Equiv.swap 1 2 * Equiv.swap 0 1

/-- **Injectivity of `itinerary ℓ S` is load-bearing** ([Persistence] §8, Proposition 8.38(i)'s
hypothesis): at the family above, `S = {1}` has a non-injective `itinerary guardSkewLens S` — both
`1` and `2` read the pattern `0` — and `Consistent guardSkewLens S` holds the two DISTINCT
permutations `guardSkewU` and `guardOtherV`, the 3-cycle sending `0 ↦ 2 ↦ 1 ↦ 0`, so
`consistent_unique_of_injective`'s conclusion fails without the hypothesis. -/
private theorem guard_hinj_load_bearing :
    ¬ Function.Injective (itinerary guardSkewLens ({1} : Finset ℕ)) ∧
      guardSkewU ≠ guardOtherV ∧
      guardOtherV ∈ Consistent guardSkewLens ({1} : Finset ℕ) := by
  refine ⟨?_, by decide, ?_⟩
  · intro hinj
    have h12 : itinerary guardSkewLens ({1} : Finset ℕ) 1
        = itinerary guardSkewLens ({1} : Finset ℕ) 2 := by decide
    exact absurd (hinj h12) (by decide)
  · simp only [Consistent, Set.mem_ofPred_eq]
    decide

private def guardRegionU : Perm (Fin 4) := Equiv.swap 0 1 * Equiv.swap 2 3
private def guardRegionFrame : Fin 4 → Fin 3 := ![0, 1, 2, 2]
private def guardRegionLens : ℕ → Fin 4 → Fin 3 := fun t => guardRegionFrame ∘ ⇑(guardRegionU ^ t)⁻¹
private def guardRegionB : Finset (Fin 4) := {0, 1}
private def guardRegionV : Perm (Fin 4) := Equiv.swap 0 1

private theorem guardRegionLens_carries : PermCarries guardRegionU guardRegionLens := by
  refine ⟨by decide, fun t x => ?_⟩
  change guardRegionFrame ((guardRegionU ^ t)⁻¹ ((guardRegionU ^ t) x)) = guardRegionFrame x
  simp

/-- **`consistent_card_ge_factorial_compl` is non-vacuous, and contrasts with Proposition 8.38(i)**
([Persistence] §8, Proposition 8.30's own reading — Remark 8.19's degenerate case made concrete): at
`n = 4`, `U = swap 0 1 * swap 2 3`, `ℓ 0 = ![0, 1, 2, 2]`, `ℓ t := ℓ 0 ∘ (U ^ t)⁻¹` — a genuine
`PermCarries` family (`guardRegionLens_carries`) — the block `B = {0, 1}` is `U`-closed and `ℓ 0` is
constant off it (both checked exhaustively below), so `consistent_card_ge_factorial_compl` applies
here with a genuinely nontrivial floor: `Bᶜ = {2, 3}` forces at least `2! = 2`, not merely `1`.
Read at `S = {1, 2}`, the itinerary sends both `2` and `3` to the pattern `(2, 2)` — non-injective —
so `consistent_unique_of_injective` does not apply; and unlike there, `Consistent ℓ S` is genuinely
NOT a singleton: `guardRegionV := swap 0 1`, distinct from `U` (it leaves `2` and `3` alone), is a
second permutation consistent with the frames held at `S`. The freedom is exactly the region left
unread, not injectivity failing in the abstract. -/
private theorem guard_region_nonvacuous :
    ¬ Function.Injective (itinerary guardRegionLens ({1, 2} : Finset ℕ)) ∧
      (∀ i ∈ guardRegionB, guardRegionU i ∈ guardRegionB) ∧
      (∀ x ∉ guardRegionB, ∀ y ∉ guardRegionB, guardRegionLens 0 x = guardRegionLens 0 y) ∧
      guardRegionV ≠ guardRegionU ∧
      guardRegionV ∈ Consistent guardRegionLens ({1, 2} : Finset ℕ) := by
  refine ⟨?_, by decide, by decide, by decide, ?_⟩
  · intro hinj
    have h23 : itinerary guardRegionLens ({1, 2} : Finset ℕ) 2
        = itinerary guardRegionLens ({1, 2} : Finset ℕ) 3 := by decide
    exact absurd (hinj h23) (by decide)
  · simp only [Consistent, Set.mem_ofPred_eq]
    decide

end FrameItinerary

/-! ## Axiom audit

The ten capstones above are `#print axioms`-clean on the standard triple, and the guards below
make that build-enforced. -/

set_option linter.style.longLine false

/-- info: 'FrameItinerary.permCarries_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FrameItinerary.permCarries_step

/-- info: 'FrameItinerary.consistent_card' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FrameItinerary.consistent_card

/-- info: 'FrameItinerary.consistent_unique_of_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FrameItinerary.consistent_unique_of_injective

/-- info: 'FrameItinerary.consistent_card_bminus' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FrameItinerary.consistent_card_bminus

/-- info: 'FrameItinerary.consistent_unique_of_injective_bminus' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FrameItinerary.consistent_unique_of_injective_bminus

/-- info: 'FrameItinerary.consistent_card_consecutive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FrameItinerary.consistent_card_consecutive

/-- info: 'FrameItinerary.consistent_card_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FrameItinerary.consistent_card_one

/-- info: 'FrameItinerary.consistent_card_ge_factorial_compl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FrameItinerary.consistent_card_ge_factorial_compl

/-- info: 'FrameItinerary.ledger_itinerary_bminus' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FrameItinerary.ledger_itinerary_bminus

/-- info: 'FrameItinerary.ledger_itinerary_range' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FrameItinerary.ledger_itinerary_range
