/-
Copyright (c) 2026 Mykola Palamarchuk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mykola Palamarchuk
-/
module

public import Batteries.Tactic.OpenPrivate
public import ALT.GrowingWidth
public import ALT.ExtremeTapWidth
import all ALT.ExtremeTapWidth

-- Formal-check file, not Mathlib-destined: opt out of the house-style header linter.
set_option linter.style.header false

/-!
# The growing width at the light cone: unbounded at the six exact-move tables
([Guests] §7 Proposition 7.23, Definition 7.2's (G2) read at the support diameter, Definition
7.8's memory width at the light-cone presentation, Propositions 7.19 and 7.20's exact endpoint
moves)

`GrowingWidth.lean` defines the growing width — the memory width read at a world's `(G2)`-part —
and leaves its `size` an arbitrary `X → ℕ`. This file instantiates `size` at the support
DIAMETER on the finitely-supported configurations of the line, and computes with it at the class
[Guests] Proposition 7.19 names: the updates with exact endpoint moves `(1, 1)` — trivial kernel,
injective, the leftmost support cell moving left by exactly one cell at each step and the
rightmost right by exactly one. Three facts, each one transport from `ExtremeTapWidth.lean`'s
statements:

* the `(G2)`-part is EXACTLY the nonzero states (`growingPart_eq_ne_zero`), because one step
  moves a nonzero state's diameter by exactly two (`diam_iterate`) — the first instantiation of
  the `size` axis at which the part is a theorem rather than a numerical proxy;
* the light-cone family from an `n`-cell window advances (`advances_lightCone`), from the two
  spread identities alone;
* the nonzero states of the region `t` cells wider sit inside the cone's stage-`t` part, so
  `MemoryWidth.memWidth_mono_of_subset` carries that region's root count, less its zero root,
  into the growing width (`rootSet_encard_le_growingWidth_lightCone_add_one`), and Proposition
  7.20's count makes it at least `2 ^ (n + t - 1)` (`two_pow_le_growingWidth_lightCone`), hence
  unbounded in `t` (`growingWidth_lightCone_unbounded`).

The six tables of Proposition 7.19 — `30`, `86`, `90`, `150`, `154`, `210` — instantiate the
class statement one line each; the identity update and the two shifts (tables `170` and `240`,
Proposition 7.20(iv)) are the guard family, at which the diameter never moves and the growing
width is `0`.

## Main results

* `diam` — the support diameter, `max' - min' + 1`, and `0` at the zero state.
* `lightCone` — the light-cone family from the `n`-cell window `[0, n)`: stage `t` is the states
  supported in `[-t, n + t)`, the window widened by `t` cells at each end.
* `diam_apply_of_moves` / `diam_iterate_of_moves` — at exact endpoint moves `(a, b)` one step
  moves a nonzero state's diameter by exactly `a + b` ([Guests] Proposition 7.20(iii)'s own
  sentence), hence `k` steps by `k · (a + b)`; `diam_iterate` is the `(1, 1)` instance, `+ 2 k`.
* `growingPart_eq_ne_zero` — at exact moves `(1, 1)` the `(G2)`-part under `diam` is exactly
  `{s | s ≠ 0}`.
* `advances_lightCone` / `growingWidth_lightCone_mono` — the light-cone family advances, so the
  growing width along it is monotone (`GrowingWidth.growingWidth_mono`, nothing further).
* `memWidth_regionStates_sdiff_zero_add_one` — the nonzero region's width, plus one, is the root
  count: `rootSet U n \ {0}` is a root set of `regionStates n \ {0}` in Proposition 7.16's sense.
* `rootSet_encard_le_growingWidth_lightCone_add_one` — the transport: the root count of the
  region `n + t` is at most the cone's stage-`t` growing width plus one.
* `two_pow_le_growingWidth_lightCone` — `2 ^ (n + t - 1)` is a lower bound at `2 ≤ n + t`.
* `growingWidth_lightCone_unbounded` — the growing width along the cone is unbounded in `t`, with
  `growingWidth_lightCone_unbounded_nonvacuous` exhibiting `rule90` meeting every hypothesis at
  once, and `growingWidth_lightCone_unbounded_rule90` … `_rule210` the six instantiations.
* The guard family — `growingWidth_lightCone_id_eq_zero`, `growingWidth_lightCone_rule170_eq_zero`,
  `growingWidth_lightCone_rule240_eq_zero`: where the update leaves the diameter alone the part is
  empty (`GrowingWidth.growingPart_id_eq_empty`, `growingPart_eq_empty_of_moves_sum_zero`) and
  the growing width is `0`. The statement is false where the rule does nothing.

## Scope

**Registered as [Guests] §7 Proposition 7.23** (FV row GV-31), clauses (i) to (v). The other
citations here are to the objects instantiated — Definitions 7.2, 7.8 and 7.22, and Propositions
7.19 and 7.20's exact-move class, tables and shifts.

`diam` is ONE reading of Definition 7.2's "encoded size", chosen because at exact endpoint moves
it makes the `(G2)`-part a theorem; the support count, another reading, is not used here and
nothing is claimed about the part under it.

**The bound is a LOWER bound, not the value.** The cone's stage-`t` growing width is observed to
be the root count of the region `2 t` cells wider, less one — which is what it must be if the
width is invariant under translating the region, the cone at stage `t` being the `(n + 2 t)`-cell
region shifted by `-t` and each of these rules commuting with the shift. That invariance is a
shift-equivariance fact per rule and a transport of `rootSet` along a translation, and neither is
stated here: the lower bound already delivers unboundedness.

`U 0 = 0` is a consequence of the trivial-kernel hypothesis (`hUeqZero.mpr rfl`), so no theorem
taking `hUeqZero` takes it separately; `advances_lightCone`, which needs only that the zero state
is fixed, takes `U 0 = 0` alone. Injectivity enters only through the root-set machinery — the
antichain and `mergeMk`'s injectivity — and none of the diameter or advancing facts consume it.

The carrier is load-bearing exactly as Proposition 7.19's boundary says: every statement is about
the finitely-supported configurations of the line and nothing beyond them.
-/

open private rootSet_cover rootSet_antichain iterate_ne_zero zero_mem_rootSet encard_pow_ne_top
  rule90_zero
  rule30_eq_zero_iff rule30_injective rule30_support_min'_spread rule30_support_max'_spread
  rule86_eq_zero_iff rule86_injective rule86_support_min'_spread rule86_support_max'_spread
  rule154_eq_zero_iff rule154_injective rule154_support_min'_spread rule154_support_max'_spread
  rule210_eq_zero_iff rule210_injective rule210_support_min'_spread rule210_support_max'_spread
  rule170_eq_zero_iff rule240_eq_zero_iff from ALT.ExtremeTapWidth

@[expose] public section

namespace LightConeWidth

open GrowingWidth MemoryWidth GrowingCore GrowingWorld ExtremeTapWidth

/-! ## The support diameter and the light-cone family -/

/-- **The support diameter**, `max' - min' + 1`, and `0` at the zero state: the `size` at which
`GrowingWidth.GrowingPart` is a theorem rather than a numerical proxy at exact endpoint moves
([Guests] §7 Definition 7.2's "encoded size", one reading of it). -/
def diam (s : ℤ →₀ ZMod 2) : ℕ :=
  if h : s.support.Nonempty then (s.support.max' h - s.support.min' h).toNat + 1 else 0

/-- **The light-cone family** from the `n`-cell window `[0, n)` ([Guests] §7 Definition 7.1's
given presentation): stage `t` is the states supported in the window widened by `t` cells at
each end, `[-t, n + t)`. -/
def lightCone (n t : ℕ) : Set (ℤ →₀ ZMod 2) :=
  {s | ∀ i ∈ s.support, -(t : ℤ) ≤ i ∧ i < (n : ℤ) + t}

/-- The zero state has diameter `0`: its support is empty. -/
private theorem diam_zero : diam (0 : ℤ →₀ ZMod 2) = 0 := by
  simp [diam]

/-- At a nonempty support the diameter is `max' - min' + 1`, the `if` resolved. -/
private theorem diam_eq {s : ℤ →₀ ZMod 2} (hne : s.support.Nonempty) :
    diam s = (s.support.max' hne - s.support.min' hne).toNat + 1 := by
  rw [diam, dite_eq_left hne]

/-! ## The diameter along an orbit at exact endpoint moves -/

/-- **One step moves a nonzero state's diameter by exactly `a + b`** ([Guests] Proposition
7.20(iii)'s own sentence, at the trivial kernel and the two exact-spread identities): the image
is nonzero, its leftmost cell sits at `min' - a` and its rightmost at `max' + b`, and
`ExtremeTapWidth.hUspread_sign_nonneg` supplies `0 ≤ a + b`, which is what lets the move be
stated in `ℕ` as `+ (a + b).toNat`. -/
theorem diam_apply_of_moves
    {U : (ℤ →₀ ZMod 2) → (ℤ →₀ ZMod 2)} {a b : ℤ}
    (hUeqZero : ∀ {s : ℤ →₀ ZMod 2}, U s = 0 ↔ s = 0)
    (hUmin' : ∀ {s : ℤ →₀ ZMod 2} (hne : s.support.Nonempty) (hne' : (U s).support.Nonempty),
      (U s).support.min' hne' = s.support.min' hne - a)
    (hUmax' : ∀ {s : ℤ →₀ ZMod 2} (hne : s.support.Nonempty) (hne' : (U s).support.Nonempty),
      (U s).support.max' hne' = s.support.max' hne + b)
    {s : ℤ →₀ ZMod 2} (hs : s ≠ 0) :
    diam (U s) = diam s + (a + b).toNat := by
  have hab : 0 ≤ a + b := hUspread_sign_nonneg hUeqZero hUmin' hUmax'
  have hne : s.support.Nonempty := Finsupp.support_nonempty_iff.mpr hs
  have hUs : U s ≠ 0 := fun h => hs (hUeqZero.mp h)
  have hne' : (U s).support.Nonempty := Finsupp.support_nonempty_iff.mpr hUs
  have hle : s.support.min' hne ≤ s.support.max' hne := Finset.min'_le_max' _ hne
  rw [diam_eq hne, diam_eq hne', hUmin' hne hne', hUmax' hne hne']
  omega

/-- **`k` steps move a nonzero state's diameter by exactly `k · (a + b)`** ([Guests]
Proposition 7.23(i)): `diam_apply_of_moves` iterated, the trivial kernel keeping every iterate
nonzero. -/
theorem diam_iterate_of_moves
    {U : (ℤ →₀ ZMod 2) → (ℤ →₀ ZMod 2)} {a b : ℤ}
    (hUeqZero : ∀ {s : ℤ →₀ ZMod 2}, U s = 0 ↔ s = 0)
    (hUmin' : ∀ {s : ℤ →₀ ZMod 2} (hne : s.support.Nonempty) (hne' : (U s).support.Nonempty),
      (U s).support.min' hne' = s.support.min' hne - a)
    (hUmax' : ∀ {s : ℤ →₀ ZMod 2} (hne : s.support.Nonempty) (hne' : (U s).support.Nonempty),
      (U s).support.max' hne' = s.support.max' hne + b)
    {s : ℤ →₀ ZMod 2} (hs : s ≠ 0) (k : ℕ) :
    diam (U^[k] s) = diam s + k * (a + b).toNat := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply',
      diam_apply_of_moves hUeqZero hUmin' hUmax' (iterate_ne_zero hUeqZero hs k), ih]
    ring

/-- **At exact moves `(1, 1)` the diameter grows by exactly two a step**: `diam_iterate_of_moves`
at `(a, b) = (1, 1)`. -/
theorem diam_iterate
    {U : (ℤ →₀ ZMod 2) → (ℤ →₀ ZMod 2)}
    (hUeqZero : ∀ {s : ℤ →₀ ZMod 2}, U s = 0 ↔ s = 0)
    (hUmin' : ∀ {s : ℤ →₀ ZMod 2} (hne : s.support.Nonempty) (hne' : (U s).support.Nonempty),
      (U s).support.min' hne' = s.support.min' hne - 1)
    (hUmax' : ∀ {s : ℤ →₀ ZMod 2} (hne : s.support.Nonempty) (hne' : (U s).support.Nonempty),
      (U s).support.max' hne' = s.support.max' hne + 1)
    {s : ℤ →₀ ZMod 2} (hs : s ≠ 0) (k : ℕ) :
    diam (U^[k] s) = diam s + 2 * k := by
  rw [diam_iterate_of_moves (a := 1) (b := 1) hUeqZero hUmin' hUmax' hs k,
    show ((1 : ℤ) + 1).toNat = 2 by decide]
  ring

/-! ## The `(G2)`-part is exactly the nonzero states -/

/-- **The `(G2)`-part under the diameter is EXACTLY the nonzero states** at exact moves `(1, 1)`
([Guests] Proposition 7.23(i); Definition 7.2's `(G2)`, at Proposition 7.19's class): a nonzero
state's orbit has diameter `diam s + 2 k` at step `k`, unbounded, while the zero state is a fixed
point of diameter `0`. -/
theorem growingPart_eq_ne_zero
    {U : (ℤ →₀ ZMod 2) → (ℤ →₀ ZMod 2)}
    (hUeqZero : ∀ {s : ℤ →₀ ZMod 2}, U s = 0 ↔ s = 0)
    (hUmin' : ∀ {s : ℤ →₀ ZMod 2} (hne : s.support.Nonempty) (hne' : (U s).support.Nonempty),
      (U s).support.min' hne' = s.support.min' hne - 1)
    (hUmax' : ∀ {s : ℤ →₀ ZMod 2} (hne : s.support.Nonempty) (hne' : (U s).support.Nonempty),
      (U s).support.max' hne' = s.support.max' hne + 1) :
    GrowingPart U diam = {s | s ≠ 0} := by
  ext s
  constructor
  · intro hs h
    subst h
    obtain ⟨k, hk⟩ := hs 0
    rw [Function.iterate_fixed (hUeqZero.mpr rfl) k, diam_zero] at hk
    exact lt_irrefl 0 hk
  · intro hs N
    refine ⟨N + 1, ?_⟩
    rw [diam_iterate hUeqZero hUmin' hUmax' hs]
    omega

/-- **The `(G2)`-part under the diameter is EMPTY where the two moves cancel** — `a + b = 0`, the
two shifts' case ([Guests] Proposition 7.23(i); Proposition 7.20(iv)): the diameter is then
constant along every orbit, the zero state's included, so no orbit has it unbounded. -/
theorem growingPart_eq_empty_of_moves_sum_zero
    {U : (ℤ →₀ ZMod 2) → (ℤ →₀ ZMod 2)} {a b : ℤ}
    (hUeqZero : ∀ {s : ℤ →₀ ZMod 2}, U s = 0 ↔ s = 0)
    (hUmin' : ∀ {s : ℤ →₀ ZMod 2} (hne : s.support.Nonempty) (hne' : (U s).support.Nonempty),
      (U s).support.min' hne' = s.support.min' hne - a)
    (hUmax' : ∀ {s : ℤ →₀ ZMod 2} (hne : s.support.Nonempty) (hne' : (U s).support.Nonempty),
      (U s).support.max' hne' = s.support.max' hne + b)
    (hab : a + b = 0) :
    GrowingPart U diam = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  intro s hs
  obtain ⟨k, hk⟩ := hs (diam s)
  by_cases h0 : s = 0
  · subst h0
    rw [Function.iterate_fixed (hUeqZero.mpr rfl) k] at hk
    exact lt_irrefl _ hk
  · rw [diam_iterate_of_moves hUeqZero hUmin' hUmax' h0 k, hab] at hk
    simp at hk

/-! ## The light-cone family advances -/

/-- **The light-cone family advances** ([Guests] Proposition 7.23(ii); Definition 7.1's
condition, verbatim), from the two exact-spread identities and the fixed zero state alone: a state
supported in `[-t, n + t)` has its image supported in `[-t - 1, n + t + 1)` — the zero image
trivially, a nonzero one because its leftmost cell is `min' - 1` and its rightmost `max' + 1`. No
"spreads by at most one cell" fact is needed; the exact identities are stronger. -/
theorem advances_lightCone
    {U : (ℤ →₀ ZMod 2) → (ℤ →₀ ZMod 2)}
    (hUzero : U 0 = 0)
    (hUmin' : ∀ {s : ℤ →₀ ZMod 2} (hne : s.support.Nonempty) (hne' : (U s).support.Nonempty),
      (U s).support.min' hne' = s.support.min' hne - 1)
    (hUmax' : ∀ {s : ℤ →₀ ZMod 2} (hne : s.support.Nonempty) (hne' : (U s).support.Nonempty),
      (U s).support.max' hne' = s.support.max' hne + 1)
    (n : ℕ) : Advances U (lightCone n) := by
  intro t s hs
  by_cases hUs : U s = 0
  · rw [hUs]
    intro i hi
    simp at hi
  · have hs0 : s ≠ 0 := fun h => hUs (h ▸ hUzero)
    have hne : s.support.Nonempty := Finsupp.support_nonempty_iff.mpr hs0
    have hne' : (U s).support.Nonempty := Finsupp.support_nonempty_iff.mpr hUs
    intro i hi
    have h1 := Finset.min'_le _ i hi
    have h2 := Finset.le_max' _ i hi
    rw [hUmin' hne hne'] at h1
    rw [hUmax' hne hne'] at h2
    have h3 := hs _ (Finset.min'_mem s.support hne)
    have h4 := hs _ (Finset.max'_mem s.support hne)
    push_cast
    omega

/-- **The growing width along the light cone is monotone** ([Guests] Proposition 7.23(ii)):
`GrowingWidth.growingWidth_mono` at `advances_lightCone`, nothing further (Theorem 7.9(i)'s
mechanism, at the restricted family). -/
theorem growingWidth_lightCone_mono
    {U : (ℤ →₀ ZMod 2) → (ℤ →₀ ZMod 2)}
    (hUzero : U 0 = 0)
    (hUmin' : ∀ {s : ℤ →₀ ZMod 2} (hne : s.support.Nonempty) (hne' : (U s).support.Nonempty),
      (U s).support.min' hne' = s.support.min' hne - 1)
    (hUmax' : ∀ {s : ℤ →₀ ZMod 2} (hne : s.support.Nonempty) (hne' : (U s).support.Nonempty),
      (U s).support.max' hne' = s.support.max' hne + 1)
    (n : ℕ) : Monotone (growingWidth U diam (lightCone n)) :=
  growingWidth_mono (advances_lightCone hUzero hUmin' hUmax' n)

/-! ## The nonzero region's width is the root count less one -/

/-- **The nonzero region's width, plus one, is the root count** ([Guests] §7 Proposition 7.16 at
the root set `rootSet U n \ {0}` of the stage `regionStates n \ {0}`): the roots less the zero
root are still an antichain, being a subset of `rootSet`'s, and still a cover, because a root
reaching a NONZERO state is itself nonzero, the zero state being a fixed point. The width is then
that root set's own count by `mergeMk`'s injectivity, and Mathlib's
`Set.encard_sdiff_singleton_add_one` at the zero root — which `rootSet` contains by construction —
restores the full root count. Stated at an arbitrary index `t` of the CONSTANT family, so the
transport below can use it at the cone's own index with no family-change step. -/
theorem memWidth_regionStates_sdiff_zero_add_one
    {U : (ℤ →₀ ZMod 2) → (ℤ →₀ ZMod 2)}
    (hUeqZero : ∀ {s : ℤ →₀ ZMod 2}, U s = 0 ↔ s = 0)
    (hUinj : Function.Injective U)
    (hUmin' : ∀ {s : ℤ →₀ ZMod 2} (hne : s.support.Nonempty) (hne' : (U s).support.Nonempty),
      (U s).support.min' hne' = s.support.min' hne - 1)
    (hUmax' : ∀ {s : ℤ →₀ ZMod 2} (hne : s.support.Nonempty) (hne' : (U s).support.Nonempty),
      (U s).support.max' hne' = s.support.max' hne + 1)
    (n t : ℕ) :
    memWidth U (fun _ => regionStates n \ {0}) t + 1 = (rootSet U n).encard := by
  have hUzero : U 0 = 0 := hUeqZero.mpr rfl
  have hsub : rootSet U n \ {0} ⊆ (fun _ => regionStates n \ {0}) t :=
    Set.sdiff_subset_sdiff_left Set.sdiff_subset
  have hanti : IsAntichain (Reaches U) (mergeMk U '' (rootSet U n \ {0})) :=
    (rootSet_antichain (a := 1) (b := 1) hUzero hUeqZero hUinj hUmin' hUmax' n).subset
      (Set.image_mono Set.sdiff_subset)
  have hcover : ∀ s ∈ (fun _ => regionStates n \ {0}) t, ∃ r ∈ rootSet U n \ {0},
      Reaches U (mergeMk U r) (mergeMk U s) := by
    rintro s ⟨hs, hs0⟩
    obtain ⟨r, hr, j, hj⟩ :=
      rootSet_cover (a := 1) (b := 1) hUeqZero hUmin' hUmax' (by norm_num) n s hs
    refine ⟨r, ⟨hr, ?_⟩, j, by rw [mergeLaw_iterate_mergeMk, hj]⟩
    intro hr0
    rw [Set.mem_singleton_iff] at hr0
    subst hr0
    exact hs0 (by rw [Set.mem_singleton_iff, ← hj, Function.iterate_fixed hUzero j])
  rw [memWidth_eq_encard_of_rootSet hsub hanti hcover,
    Function.Injective.encard_image (mergeMk_injective_of_injective hUinj),
    Set.encard_sdiff_singleton_add_one (zero_mem_rootSet hUeqZero n)]

/-! ## The transport, the power bound, and the headline -/

/-- **The transport** ([Guests] Proposition 7.23(iii)): the root count of the region `n + t`
cells wide is at most the cone's stage-`t` growing width plus one. The nonzero states of that
region sit inside `lightCone n t ∩ GrowingPart U diam` — support in `[0, n + t)` is support in
`[-t, n + t)`, and a nonzero state is in the part by `growingPart_eq_ne_zero` — so
`MemoryWidth.memWidth_mono_of_subset`, at the single index `t` and with no hypothesis, carries
`memWidth_regionStates_sdiff_zero_add_one`'s width into the growing width. A LOWER bound: see the
module's Scope note. -/
theorem rootSet_encard_le_growingWidth_lightCone_add_one
    {U : (ℤ →₀ ZMod 2) → (ℤ →₀ ZMod 2)}
    (hUeqZero : ∀ {s : ℤ →₀ ZMod 2}, U s = 0 ↔ s = 0)
    (hUinj : Function.Injective U)
    (hUmin' : ∀ {s : ℤ →₀ ZMod 2} (hne : s.support.Nonempty) (hne' : (U s).support.Nonempty),
      (U s).support.min' hne' = s.support.min' hne - 1)
    (hUmax' : ∀ {s : ℤ →₀ ZMod 2} (hne : s.support.Nonempty) (hne' : (U s).support.Nonempty),
      (U s).support.max' hne' = s.support.max' hne + 1)
    (n t : ℕ) :
    (rootSet U (n + t)).encard ≤ growingWidth U diam (lightCone n) t + 1 := by
  rw [← memWidth_regionStates_sdiff_zero_add_one hUeqZero hUinj hUmin' hUmax' (n + t) t]
  refine add_le_add ?_ le_rfl
  unfold growingWidth
  apply memWidth_mono_of_subset
  rintro s ⟨hs, hs0⟩
  refine ⟨?_, ?_⟩
  · intro i hi
    have := hs i hi
    push_cast at this ⊢
    omega
  · rw [growingPart_eq_ne_zero hUeqZero hUmin' hUmax']
    exact fun h => hs0 (Set.mem_singleton_iff.mpr h)

/-- The arithmetic behind the power bound, in `ℕ∞` with every step additive: a count satisfying
`c + 2 ^ (m - 2) = 2 ^ m + 1` at `2 ≤ m` is at least `2 ^ (m - 1) + 1`. The count is finite
(the right side is), so it lifts to `ℕ`, where `2 ^ m = 4 · 2 ^ (m - 2)` and
`2 ^ (m - 1) = 2 · 2 ^ (m - 2)` settle it. -/
private theorem two_pow_pred_add_one_le {c : ℕ∞} {m : ℕ} (hm : 2 ≤ m)
    (h : c + 2 ^ (m - 2) = 2 ^ m + 1) : 2 ^ (m - 1) + 1 ≤ c := by
  have hc : c ≠ ⊤ := by
    rintro rfl
    rw [top_add] at h
    exact WithTop.add_ne_top.mpr ⟨encard_pow_ne_top m, WithTop.one_ne_top⟩ h.symm
  lift c to ℕ using hc
  norm_cast at h ⊢
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hm
  rw [show k + 2 - 2 = k by omega] at h
  rw [show k + 2 - 1 = k + 1 by omega]
  rw [pow_succ, pow_succ] at h
  rw [pow_succ]
  omega

/-- **The power bound** ([Guests] Proposition 7.23(iii)): at `2 ≤ n + t` the cone's stage-`t`
growing width is at least `2 ^ (n + t - 1)` — the transport composed with [Guests] Proposition
7.20's count at `(a, b) = (1, 1)`, `m = 2` (`ExtremeTapWidth.rootSet_encard_add_of_hyps`: the
region's root count plus `2 ^ (n + t - 2)` is `2 ^ (n + t) + 1`), the `+ 1` cancelled in `ℕ∞` at a
finite summand. -/
theorem two_pow_le_growingWidth_lightCone
    {U : (ℤ →₀ ZMod 2) → (ℤ →₀ ZMod 2)}
    (hUeqZero : ∀ {s : ℤ →₀ ZMod 2}, U s = 0 ↔ s = 0)
    (hUinj : Function.Injective U)
    (hUmin' : ∀ {s : ℤ →₀ ZMod 2} (hne : s.support.Nonempty) (hne' : (U s).support.Nonempty),
      (U s).support.min' hne' = s.support.min' hne - 1)
    (hUmax' : ∀ {s : ℤ →₀ ZMod 2} (hne : s.support.Nonempty) (hne' : (U s).support.Nonempty),
      (U s).support.max' hne' = s.support.max' hne + 1)
    {n t : ℕ} (h : 2 ≤ n + t) :
    (2 : ℕ∞) ^ (n + t - 1) ≤ growingWidth U diam (lightCone n) t := by
  have hcount := rootSet_encard_add_of_hyps (a := 1) (b := 1) hUeqZero hUinj hUmin' hUmax'
    (n := n + t) (m := 2) (by norm_num) h
  have hroot := two_pow_pred_add_one_le h hcount
  have hbound := rootSet_encard_le_growingWidth_lightCone_add_one hUeqZero hUinj hUmin' hUmax' n t
  exact (ENat.add_le_add_iff_right WithTop.one_ne_top).mp (hroot.trans hbound)

/-- **The headline: the growing width along the light cone is unbounded** at every update with exact
endpoint moves `(1, 1)` — [Guests] Proposition 7.23(iii); Definition 7.2's `(G2)`-part, read by
Definition 7.8's width at the light-cone presentation, at Proposition 7.19's class. Stage
`t := N + 2` and the power bound: `N < 2 ^ (N + 1) ≤ 2 ^ (n + N + 1)`. -/
theorem growingWidth_lightCone_unbounded
    {U : (ℤ →₀ ZMod 2) → (ℤ →₀ ZMod 2)}
    (hUeqZero : ∀ {s : ℤ →₀ ZMod 2}, U s = 0 ↔ s = 0)
    (hUinj : Function.Injective U)
    (hUmin' : ∀ {s : ℤ →₀ ZMod 2} (hne : s.support.Nonempty) (hne' : (U s).support.Nonempty),
      (U s).support.min' hne' = s.support.min' hne - 1)
    (hUmax' : ∀ {s : ℤ →₀ ZMod 2} (hne : s.support.Nonempty) (hne' : (U s).support.Nonempty),
      (U s).support.max' hne' = s.support.max' hne + 1)
    (n : ℕ) : ∀ N : ℕ, ∃ t : ℕ, (N : ℕ∞) < growingWidth U diam (lightCone n) t := by
  intro N
  refine ⟨N + 2, lt_of_lt_of_le ?_
    (two_pow_le_growingWidth_lightCone hUeqZero hUinj hUmin' hUmax' (by omega))⟩
  have h1 : N < 2 ^ (n + (N + 2) - 1) :=
    lt_of_lt_of_le Nat.lt_two_pow_self (Nat.pow_le_pow_right (by norm_num) (by omega))
  exact_mod_cast h1

/-- **The hypotheses are jointly satisfiable** ([Guests] Proposition 7.23(iv)): `rule90` meets
all five facts at once — the fixed zero state, the trivial kernel, injectivity, and both exact
spreads — so `growingWidth_lightCone_unbounded` is not vacuous. The fixed zero state is listed
although the headline derives it from the trivial kernel, so that the witness covers every form of
the hypothesis set this file states. -/
theorem growingWidth_lightCone_unbounded_nonvacuous :
    ∃ U : (ℤ →₀ ZMod 2) → (ℤ →₀ ZMod 2), U 0 = 0 ∧
      (∀ {s : ℤ →₀ ZMod 2}, U s = 0 ↔ s = 0) ∧ Function.Injective U ∧
      (∀ {s : ℤ →₀ ZMod 2} (hne : s.support.Nonempty) (hne' : (U s).support.Nonempty),
        (U s).support.min' hne' = s.support.min' hne - 1) ∧
      (∀ {s : ℤ →₀ ZMod 2} (hne : s.support.Nonempty) (hne' : (U s).support.Nonempty),
        (U s).support.max' hne' = s.support.max' hne + 1) :=
  ⟨rule90, rule90_zero, rule90_eq_zero_iff, rule90_injective,
    fun hne hne' => rule90_support_min'_spread hne hne',
    fun hne hne' => rule90_support_max'_spread hne hne'⟩

/-! ## The six tables ([Guests] §7 Proposition 7.23(iv); Proposition 7.19(ii)) -/

/-- **Table `90`** ([Guests] Proposition 7.23(iv)): the headline at `rule90`'s own
facts. -/
theorem growingWidth_lightCone_unbounded_rule90 (n : ℕ) :
    ∀ N : ℕ, ∃ t : ℕ, (N : ℕ∞) < growingWidth rule90 diam (lightCone n) t :=
  growingWidth_lightCone_unbounded rule90_eq_zero_iff rule90_injective
    rule90_support_min'_spread rule90_support_max'_spread n

/-- **Table `150`** ([Guests] Proposition 7.23(iv)): the headline at `rule150`'s own
facts. -/
theorem growingWidth_lightCone_unbounded_rule150 (n : ℕ) :
    ∀ N : ℕ, ∃ t : ℕ, (N : ℕ∞) < growingWidth rule150 diam (lightCone n) t :=
  growingWidth_lightCone_unbounded rule150_eq_zero_iff rule150_injective
    rule150_support_min'_spread rule150_support_max'_spread n

/-- **Table `30`**, non-additive ([Guests] Proposition 7.23(iv)): the headline at `rule30`'s own
facts. -/
theorem growingWidth_lightCone_unbounded_rule30 (n : ℕ) :
    ∀ N : ℕ, ∃ t : ℕ, (N : ℕ∞) < growingWidth rule30 diam (lightCone n) t :=
  growingWidth_lightCone_unbounded rule30_eq_zero_iff rule30_injective
    rule30_support_min'_spread rule30_support_max'_spread n

/-- **Table `86`**, non-additive ([Guests] Proposition 7.23(iv)): the headline at `rule86`'s own
facts. -/
theorem growingWidth_lightCone_unbounded_rule86 (n : ℕ) :
    ∀ N : ℕ, ∃ t : ℕ, (N : ℕ∞) < growingWidth rule86 diam (lightCone n) t :=
  growingWidth_lightCone_unbounded rule86_eq_zero_iff rule86_injective
    rule86_support_min'_spread rule86_support_max'_spread n

/-- **Table `154`**, non-additive ([Guests] Proposition 7.23(iv)): the headline at `rule154`'s
own facts. -/
theorem growingWidth_lightCone_unbounded_rule154 (n : ℕ) :
    ∀ N : ℕ, ∃ t : ℕ, (N : ℕ∞) < growingWidth rule154 diam (lightCone n) t :=
  growingWidth_lightCone_unbounded rule154_eq_zero_iff rule154_injective
    rule154_support_min'_spread rule154_support_max'_spread n

/-- **Table `210`**, non-additive ([Guests] Proposition 7.23(iv)): the headline at `rule210`'s
own facts. -/
theorem growingWidth_lightCone_unbounded_rule210 (n : ℕ) :
    ∀ N : ℕ, ∃ t : ℕ, (N : ℕ∞) < growingWidth rule210 diam (lightCone n) t :=
  growingWidth_lightCone_unbounded rule210_eq_zero_iff rule210_injective
    rule210_support_min'_spread rule210_support_max'_spread n

/-! ## The guard family: the statement is false where the rule does nothing

Stated at the GROWING width, never at the plain one: `memWidth id (lightCone n) t` is the region's
whole count ([Guests] Proposition 7.20(ii)'s identity witness) and is exactly what the growing
width is there to exclude. -/

/-- The width of an empty stage is `0`: the retained profile is empty, so
`MemoryWidth.memWidth_le_encard_mergeStage` bounds the width by `0`. -/
private theorem memWidth_eq_zero_of_empty {X : Type*} {U : X → X} {Ω : ℕ → Set X} {t : ℕ}
    (h : Ω t = ∅) : memWidth U Ω t = 0 := by
  apply nonpos_iff_eq_zero.mp
  refine (memWidth_le_encard_mergeStage U Ω t).trans ?_
  have hst : mergeStage U Ω t = ∅ := by
    change mergeMk U '' Ω t = ∅
    rw [h, Set.image_empty]
  rw [hst, Set.encard_empty]

/-- **The identity update has growing width `0` along the light cone** ([Guests] §7 Proposition
7.23(v)): its `(G2)`-part is empty whatever the `size` (`GrowingWidth.growingPart_id_eq_empty`), so
every restricted stage is empty. Against Proposition 7.20(ii): the PLAIN width there is the
region's whole count. -/
theorem growingWidth_lightCone_id_eq_zero (n t : ℕ) :
    growingWidth (id : (ℤ →₀ ZMod 2) → (ℤ →₀ ZMod 2)) diam (lightCone n) t = 0 := by
  unfold growingWidth
  exact memWidth_eq_zero_of_empty (by rw [growingPart_id_eq_empty, Set.inter_empty])

/-- **The shift `170` has growing width `0` along the light cone** ([Guests] Proposition 7.23(v);
Proposition 7.20(iv), endpoint moves `(1, -1)`): the diameter is constant along every orbit, so the
part is empty (`growingPart_eq_empty_of_moves_sum_zero`). -/
theorem growingWidth_lightCone_rule170_eq_zero (n t : ℕ) :
    growingWidth rule170 diam (lightCone n) t = 0 := by
  unfold growingWidth
  exact memWidth_eq_zero_of_empty (by
    rw [growingPart_eq_empty_of_moves_sum_zero (a := 1) (b := -1) rule170_eq_zero_iff
      rule170_support_min'_spread rule170_support_max'_spread (by norm_num), Set.inter_empty])

/-- **The shift `240` has growing width `0` along the light cone** ([Guests] Proposition 7.23(v);
Proposition 7.20(iv), endpoint moves `(-1, 1)`): the twin of
`growingWidth_lightCone_rule170_eq_zero`. -/
theorem growingWidth_lightCone_rule240_eq_zero (n t : ℕ) :
    growingWidth rule240 diam (lightCone n) t = 0 := by
  unfold growingWidth
  exact memWidth_eq_zero_of_empty (by
    rw [growingPart_eq_empty_of_moves_sum_zero (a := -1) (b := 1) rule240_eq_zero_iff
      rule240_support_min'_spread rule240_support_max'_spread (by norm_num), Set.inter_empty])

end LightConeWidth

/-! ## Axiom audit

Every capstone above is `#print axioms`-clean on the standard triple, and the guards below make
that build-enforced. -/

set_option linter.style.longLine false

/-- info: 'LightConeWidth.growingWidth_lightCone_unbounded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LightConeWidth.growingWidth_lightCone_unbounded

/-- info: 'LightConeWidth.growingWidth_lightCone_unbounded_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LightConeWidth.growingWidth_lightCone_unbounded_nonvacuous

/-- info: 'LightConeWidth.growingWidth_lightCone_unbounded_rule90' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LightConeWidth.growingWidth_lightCone_unbounded_rule90

/-- info: 'LightConeWidth.growingWidth_lightCone_unbounded_rule150' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LightConeWidth.growingWidth_lightCone_unbounded_rule150

/-- info: 'LightConeWidth.growingWidth_lightCone_unbounded_rule30' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LightConeWidth.growingWidth_lightCone_unbounded_rule30

/-- info: 'LightConeWidth.growingWidth_lightCone_unbounded_rule86' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LightConeWidth.growingWidth_lightCone_unbounded_rule86

/-- info: 'LightConeWidth.growingWidth_lightCone_unbounded_rule154' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LightConeWidth.growingWidth_lightCone_unbounded_rule154

/-- info: 'LightConeWidth.growingWidth_lightCone_unbounded_rule210' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LightConeWidth.growingWidth_lightCone_unbounded_rule210

/-- info: 'LightConeWidth.growingWidth_lightCone_id_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LightConeWidth.growingWidth_lightCone_id_eq_zero

/-- info: 'LightConeWidth.growingWidth_lightCone_rule170_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LightConeWidth.growingWidth_lightCone_rule170_eq_zero

/-- info: 'LightConeWidth.growingWidth_lightCone_rule240_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LightConeWidth.growingWidth_lightCone_rule240_eq_zero
