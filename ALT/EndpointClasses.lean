/-
Copyright (c) 2026 Mykola Palamarchuk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mykola Palamarchuk
-/
module

public import ALT.LightConeWidth
public import ALT.ExtremeTapWidth

-- Formal-check file, not Mathlib-destined: opt out of the house-style header linter.
set_option linter.style.header false

/-!
# The growing width at the light cone, over the whole radius-one rule space
([Guests] §7 Definition 7.22, Proposition 7.23, §9.2's growing-branch bullet)

`LightConeWidth.lean` proves the growing width along the light cone unbounded at the six tables of
[Guests] Proposition 7.19 — those with an EXACT endpoint move `(1, 1)` at every nonzero state,
via `mergeMk`'s global injectivity. This file extends that to the whole `128`-table quiescent
radius-one rule space, with an engine that needs no injectivity: an antichain of the retained
profile is a set of states with pairwise DISJOINT forward orbits — `Reaches` unfolds through
`MemoryWidth.mergeLaw_iterate_mergeMk` to an equation between iterates, and two iterates of
distinct translates of one state coincide only when the exponents and the offsets coincide, at any
update whose two endpoints move by exact constants `a b` with `a + b ≥ 1` on an invariant set.

The engine is `linear_le_growingWidth_lightCone_of_invariant`: at a set `S` the update preserves,
containing every translate of a fixed nonzero state `s₀`, on which the two endpoints move by exact
constants summing to at least `1`, the light cone's growing width is at least linear in the stage.
Two instances of it cover every table the table bits classify as accreting: `S` the nonzero states,
where the moves are exact by the table bits alone (Class A, `48` tables); and `S` the states whose
two rightmost (or leftmost) cells are set, where a tap on one side and a held two-cell "end-word"
on the other keep the endpoint fixed cell by cell (Class E, `4` tables). The zero class (`48`
tables) is the mirror: no tap on either side, or one tap with the other endpoint always dying, and
the diameter is non-increasing on every orbit, so the `(G2)`-part is empty and the growing width is
identically zero. The middle band (`28` tables) is not decided here.

## Main results

* `translate` — shift by `i` cells, `Finsupp.mapDomain (· + i)`.
* `linear_le_growingWidth_lightCone_of_invariant` — **the engine**: at an invariant translation-
  closed set with exact endpoint moves summing to at least `1`, the light cone's growing width at
  stage `t` is at least `n + 2 t + 1 - diam s₀`.
* `growingWidth_lightCone_unbounded_of_invariant` — the engine's unbounded corollary, at the same
  hypotheses.
* `tableRule_min'_of_leftTap` / `tableRule_max'_of_rightTap` and the mirrors, `tableRule_min'_of_
  leftHold` / `tableRule_max'_of_rightHold` and the mirrors — the table-bit leaves the two Class-A
  instances of the engine consume.
* `EndsOneOne` / `StartsOneOne` and their leaves (`endsOneOne_tableRule`, `tableRule_max'_of_
  endsOneOne`, `endsOneOne_translate`, and the mirrors) — the Class-E instance's own invariant set.
* `advances_lightCone_tableRule` — the light cone advances under EVERY quiescent table, from
  `tableRule`'s own support bound alone.
* `growingPart_eq_empty_of_diam_le` / `growingWidth_lightCone_eq_zero_of_diam_le` — the zero side's
  parent: a non-increasing diameter empties the `(G2)`-part.
* `diam_tableRule_le_of_noTap` / `diam_tableRule_le_of_leftTap_rightDies` and the mirror — the
  zero class's table-bit leaves.
* `AccretesByEndpoints` / `ZeroByEndpoints` — the two classes, as explicit bit disjunctions.
* `growingWidth_lightCone_unbounded_of_accretesByEndpoints` / `growingWidth_lightCone_eq_zero_of_
  zeroByEndpoints` — **the class theorems**, over every quiescent table meeting the class.
* `accretesByEndpoints_zeroByEndpoints_disjoint` — the two classes never overlap.
* `card_quiescent` / `card_accretesByEndpoints` / `card_zeroByEndpoints` — **the counts**: `128`
  quiescent tables, `52` accreting by the class theorem, `48` zero by the class theorem.
* `f202` / `growingWidth_lightCone_unbounded_of_invariant_nonvacuous` / `growingWidth_lightCone_
  unbounded_f202` — the engine's hypotheses are jointly satisfiable, at the Class-E instance.

## Scope

**Registered as [Guests] §7 Definition 7.22, Proposition 7.23's boundary paragraph, and §9.2's
growing-branch bullet.** The class theorems bracket the fraction of the `128` quiescent radius-one
tables at which the growing width along the light cone is unbounded: at least `52 / 128` unbounded
and at least `48 / 128` identically zero, so the open fraction lies in `[52 / 128, 80 / 128]`. The
remaining `28` tables (the middle band) are NOT decided here — no theorem in this file classifies
them, and neither does any other declaration in the tree.

The engine's bound is LINEAR, not the exponential bound `LightConeWidth.two_pow_le_growingWidth_
lightCone` proves at the six exact-move tables under injectivity: at those six tables the landed
exponential statement is the sharper one, and this file's bound is the wider engine, reaching tables
the exponential route cannot.

`AccretesByEndpoints`/`ZeroByEndpoints` classify tables by their BITS alone; neither predicate
claims anything about a table outside the `128` quiescent ones (`f 0 0 0 = 0`), and `card_quiescent`
states the ambient count precisely so the two class counts read as fractions of it.
-/


@[expose] public section

namespace EndpointClasses

open GrowingWidth MemoryWidth GrowingCore GrowingWorld ExtremeTapWidth LightConeWidth

/-! ## Translation, and its support facts -/

/-- **Translation by `i` cells**: `Finsupp.mapDomain (· + i)`, shifting every support cell right by
`i`. -/
noncomputable def translate (i : ℤ) (s : ℤ →₀ ZMod 2) : ℤ →₀ ZMod 2 :=
  Finsupp.mapDomain (· + i) s

private theorem translate_zero (s : ℤ →₀ ZMod 2) : translate 0 s = s := by
  ext x
  have h := Finsupp.mapDomain_apply_of_injective (add_left_injective (0 : ℤ)) s x
  rwa [add_zero] at h

private theorem translate_apply (i x : ℤ) (s : ℤ →₀ ZMod 2) : translate i s (x + i) = s x :=
  Finsupp.mapDomain_apply_of_injective (add_left_injective i) s x

private theorem translate_support (i : ℤ) (s : ℤ →₀ ZMod 2) :
    (translate i s).support = s.support.image (· + i) :=
  Finsupp.mapDomain_support_of_injective (add_left_injective i) s

private theorem translate_ne_zero_iff (i : ℤ) {s : ℤ →₀ ZMod 2} : translate i s = 0 ↔ s = 0 := by
  constructor
  · intro h
    have hs : (translate i s).support = ∅ := by rw [h]; simp
    rw [translate_support] at hs
    exact Finsupp.support_eq_empty.mp (Finset.image_eq_empty.mp hs)
  · intro h; rw [h]; simp [translate]

private theorem minCongr {s t : Finset ℤ} (h : s = t) (hs : s.Nonempty) (ht : t.Nonempty) :
    s.min' hs = t.min' ht := by subst h; rfl

private theorem maxCongr {s t : Finset ℤ} (h : s = t) (hs : s.Nonempty) (ht : t.Nonempty) :
    s.max' hs = t.max' ht := by subst h; rfl

private theorem translate_monotone (i : ℤ) : Monotone (· + i : ℤ → ℤ) :=
  fun x y h => by change x + i ≤ y + i; omega

private theorem translate_support_min' (i : ℤ) {s : ℤ →₀ ZMod 2} (hne : s.support.Nonempty)
    (hne' : (translate i s).support.Nonempty) :
    (translate i s).support.min' hne' = s.support.min' hne + i := by
  rw [minCongr (translate_support i s) hne' (hne.image _)]
  exact (Monotone.map_finset_min' (translate_monotone i) hne).symm

private theorem translate_support_max' (i : ℤ) {s : ℤ →₀ ZMod 2} (hne : s.support.Nonempty)
    (hne' : (translate i s).support.Nonempty) :
    (translate i s).support.max' hne' = s.support.max' hne + i := by
  rw [maxCongr (translate_support i s) hne' (hne.image _)]
  exact (Monotone.map_finset_max' (translate_monotone i) hne).symm

/-- **The support bound**: `translate i s` sits inside `[s.support.min' + i, s.support.max' +
i]`. -/
private theorem translate_support_bound (i : ℤ) {s : ℤ →₀ ZMod 2} (hne : s.support.Nonempty)
    {x : ℤ} (hx : x ∈ (translate i s).support) :
    s.support.min' hne + i ≤ x ∧ x ≤ s.support.max' hne + i := by
  have hne' : (translate i s).support.Nonempty := ⟨x, hx⟩
  rw [← translate_support_min' i hne hne', ← translate_support_max' i hne hne']
  exact ⟨Finset.min'_le _ x hx, Finset.le_max' _ x hx⟩

/-! ## Small generic helpers reused across the table-bit leaves -/

private theorem below_min'_eq_zero {s : ℤ →₀ ZMod 2} (hne : s.support.Nonempty) {x : ℤ}
    (hx : x < s.support.min' hne) : s x = 0 := by
  by_contra hc
  have hmem : x ∈ s.support := Finsupp.mem_support_iff.mpr hc
  have := Finset.min'_le s.support x hmem
  omega

private theorem above_max'_eq_zero {s : ℤ →₀ ZMod 2} (hne : s.support.Nonempty) {x : ℤ}
    (hx : s.support.max' hne < x) : s x = 0 := by
  by_contra hc
  have hmem : x ∈ s.support := Finsupp.mem_support_iff.mpr hc
  have := Finset.le_max' s.support x hmem
  omega

private theorem zmod2_eq_one_of_ne_zero' : ∀ a : ZMod 2, a ≠ 0 → a = 1 := by decide

private theorem memWidth_eq_zero_of_empty {X : Type*} {V : X → X} {Ω : ℕ → Set X} {t : ℕ}
    (h : Ω t = ∅) : MemoryWidth.memWidth V Ω t = 0 := by
  apply nonpos_iff_eq_zero.mp
  refine (MemoryWidth.memWidth_le_encard_mergeStage V Ω t).trans ?_
  have hst : GrowingCore.mergeStage V Ω t = ∅ := by
    change GrowingCore.mergeMk V '' Ω t = ∅
    rw [h, Set.image_empty]
  rw [hst, Set.encard_empty]

private theorem diam_zero' : diam (0 : ℤ →₀ ZMod 2) = 0 := by simp [LightConeWidth.diam]

private theorem diam_eq' {s : ℤ →₀ ZMod 2} (hne : s.support.Nonempty) :
    diam s = (s.support.max' hne - s.support.min' hne).toNat + 1 := by
  simp [LightConeWidth.diam, hne]

private theorem diam_le_of_support_subset {t' : ℤ →₀ ZMod 2} {m M : ℤ}
    (h : ∀ x ∈ t'.support, m ≤ x ∧ x ≤ M) (hle : m ≤ M) :
    diam t' ≤ (M - m).toNat + 1 := by
  by_cases ht : t'.support.Nonempty
  · rw [diam_eq' ht]
    have h1 := (h _ (Finset.min'_mem t'.support ht)).1
    have h2 := (h _ (Finset.max'_mem t'.support ht)).2
    have h3 := Finset.min'_le_max' t'.support ht
    omega
  · have hz : t' = 0 := Finsupp.support_eq_empty.mp (Finset.not_nonempty_iff_eq_empty.mp ht)
    rw [hz, diam_zero']
    omega

/-! ## Piece 1: the engine — exact endpoint moves on an invariant translation-closed set -/

section Engine

variable {U : (ℤ →₀ ZMod 2) → (ℤ →₀ ZMod 2)} {S : Set (ℤ →₀ ZMod 2)} {a b : ℤ}

private theorem mem_S_iterate (hS : ∀ s ∈ S, U s ∈ S) {s : ℤ →₀ ZMod 2} (hs : s ∈ S) :
    ∀ k : ℕ, U^[k] s ∈ S
  | 0 => hs
  | k + 1 => by rw [Function.iterate_succ_apply']; exact hS _ (mem_S_iterate hS hs k)

private theorem iterate_min'_spread_S
    (hS : ∀ s ∈ S, U s ∈ S) (hSne : ∀ s ∈ S, s ≠ 0)
    (hSmin' : ∀ s ∈ S, ∀ (hne : s.support.Nonempty) (hne' : (U s).support.Nonempty),
      (U s).support.min' hne' = s.support.min' hne - a)
    {s : ℤ →₀ ZMod 2} (hs : s ∈ S) (hne : s.support.Nonempty) :
    ∀ (k : ℕ) (hne' : (U^[k] s).support.Nonempty),
      (U^[k] s).support.min' hne' = s.support.min' hne - k * a := by
  intro k
  induction k with
  | zero =>
    intro hne'
    rw [minCongr (congrArg Finsupp.support (rfl : U^[0] s = s)) hne' hne]; simp
  | succ j ih =>
    intro hne'
    have hjS : U^[j] s ∈ S := mem_S_iterate hS hs j
    have hjne : U^[j] s ≠ 0 := hSne _ hjS
    have hjne' : (U^[j] s).support.Nonempty := Finsupp.support_nonempty_iff.mpr hjne
    have e : U^[j + 1] s = U (U^[j] s) := Function.iterate_succ_apply' U j s
    have hUjne' : (U (U^[j] s)).support.Nonempty := by rw [← e]; exact hne'
    rw [minCongr (congrArg Finsupp.support e) hne' hUjne', hSmin' _ hjS hjne' hUjne', ih hjne']
    push_cast; ring

private theorem iterate_max'_spread_S
    (hS : ∀ s ∈ S, U s ∈ S) (hSne : ∀ s ∈ S, s ≠ 0)
    (hSmax' : ∀ s ∈ S, ∀ (hne : s.support.Nonempty) (hne' : (U s).support.Nonempty),
      (U s).support.max' hne' = s.support.max' hne + b)
    {s : ℤ →₀ ZMod 2} (hs : s ∈ S) (hne : s.support.Nonempty) :
    ∀ (k : ℕ) (hne' : (U^[k] s).support.Nonempty),
      (U^[k] s).support.max' hne' = s.support.max' hne + k * b := by
  intro k
  induction k with
  | zero =>
    intro hne'
    rw [maxCongr (congrArg Finsupp.support (rfl : U^[0] s = s)) hne' hne]; simp
  | succ j ih =>
    intro hne'
    have hjS : U^[j] s ∈ S := mem_S_iterate hS hs j
    have hjne : U^[j] s ≠ 0 := hSne _ hjS
    have hjne' : (U^[j] s).support.Nonempty := Finsupp.support_nonempty_iff.mpr hjne
    have e : U^[j + 1] s = U (U^[j] s) := Function.iterate_succ_apply' U j s
    have hUjne' : (U (U^[j] s)).support.Nonempty := by rw [← e]; exact hne'
    rw [maxCongr (congrArg Finsupp.support e) hne' hUjne', hSmax' _ hjS hjne' hUjne', ih hjne']
    push_cast; ring

/-- **Every translate is `(G2)`**: the diameter of `translate i s₀`'s orbit under `U` is unbounded,
since `S`'s exact endpoint moves sum to at least `1`. -/
private theorem translate_mem_growingPart
    (hS : ∀ s ∈ S, U s ∈ S) (hSne : ∀ s ∈ S, s ≠ 0)
    (hSmin' : ∀ s ∈ S, ∀ (hne : s.support.Nonempty) (hne' : (U s).support.Nonempty),
      (U s).support.min' hne' = s.support.min' hne - a)
    (hSmax' : ∀ s ∈ S, ∀ (hne : s.support.Nonempty) (hne' : (U s).support.Nonempty),
      (U s).support.max' hne' = s.support.max' hne + b)
    (hab : 1 ≤ a + b) {s₀ : ℤ →₀ ZMod 2} (hs₀ : ∀ i : ℤ, translate i s₀ ∈ S) (i : ℤ) :
    translate i s₀ ∈ GrowingPart U diam := by
  intro N
  refine ⟨N + 1, ?_⟩
  have hiS : translate i s₀ ∈ S := hs₀ i
  have hine : (translate i s₀).support.Nonempty := Finsupp.support_nonempty_iff.mpr (hSne _ hiS)
  have hne' : (U^[N + 1] (translate i s₀)).support.Nonempty :=
    Finsupp.support_nonempty_iff.mpr (hSne _ (mem_S_iterate hS hiS (N + 1)))
  have hmin := iterate_min'_spread_S hS hSne hSmin' hiS hine (N + 1) hne'
  have hmax := iterate_max'_spread_S hS hSne hSmax' hiS hine (N + 1) hne'
  have hle : (translate i s₀).support.min' hine ≤ (translate i s₀).support.max' hine :=
    Finset.min'_le_max' _ hine
  have hstep : ((N + 1 : ℕ) : ℤ) ≤ ((N + 1 : ℕ) : ℤ) * (a + b) := by
    calc ((N + 1 : ℕ) : ℤ) = ((N + 1 : ℕ) : ℤ) * 1 := (mul_one _).symm
      _ ≤ ((N + 1 : ℕ) : ℤ) * (a + b) := mul_le_mul_of_nonneg_left hab (by positivity)
  have hexpand : ((N + 1 : ℕ) : ℤ) * (a + b) =
      ((N + 1 : ℕ) : ℤ) * a + ((N + 1 : ℕ) : ℤ) * b := by ring
  have hbig : (N : ℤ) + 1 ≤
      ((translate i s₀).support.max' hine + ((N + 1 : ℕ) : ℤ) * b) -
        ((translate i s₀).support.min' hine - ((N + 1 : ℕ) : ℤ) * a) := by
    push_cast at hstep hexpand ⊢
    linarith [hle, hstep, hexpand]
  rw [diam_eq' hne', hmin, hmax]
  omega

/-- **The disjoint-orbit crux**: two iterates of two translates of `s₀` coincide only when the
exponents and the offsets coincide — Finding 1's arithmetic, `(a + b)(j - k) = 0`. -/
private theorem translate_orbit_eq
    (hS : ∀ s ∈ S, U s ∈ S) (hSne : ∀ s ∈ S, s ≠ 0)
    (hSmin' : ∀ s ∈ S, ∀ (hne : s.support.Nonempty) (hne' : (U s).support.Nonempty),
      (U s).support.min' hne' = s.support.min' hne - a)
    (hSmax' : ∀ s ∈ S, ∀ (hne : s.support.Nonempty) (hne' : (U s).support.Nonempty),
      (U s).support.max' hne' = s.support.max' hne + b)
    (hab : 1 ≤ a + b) {s₀ : ℤ →₀ ZMod 2} (hs₀ : ∀ i : ℤ, translate i s₀ ∈ S)
    {i i' : ℤ} {j k : ℕ} (heq : U^[j] (translate i s₀) = U^[k] (translate i' s₀)) :
    j = k ∧ i = i' := by
  have hs0S : s₀ ∈ S := by have h := hs₀ 0; rwa [translate_zero] at h
  have hne0 : s₀.support.Nonempty := Finsupp.support_nonempty_iff.mpr (hSne _ hs0S)
  have hiS : translate i s₀ ∈ S := hs₀ i
  have hi'S : translate i' s₀ ∈ S := hs₀ i'
  have hine : (translate i s₀).support.Nonempty := Finsupp.support_nonempty_iff.mpr (hSne _ hiS)
  have hi'ne : (translate i' s₀).support.Nonempty := Finsupp.support_nonempty_iff.mpr (hSne _ hi'S)
  have hjne' : (U^[j] (translate i s₀)).support.Nonempty :=
    Finsupp.support_nonempty_iff.mpr (hSne _ (mem_S_iterate hS hiS j))
  have hkne' : (U^[k] (translate i' s₀)).support.Nonempty :=
    Finsupp.support_nonempty_iff.mpr (hSne _ (mem_S_iterate hS hi'S k))
  have hminL := iterate_min'_spread_S hS hSne hSmin' hiS hine j hjne'
  have hmaxL := iterate_max'_spread_S hS hSne hSmax' hiS hine j hjne'
  have hminR := iterate_min'_spread_S hS hSne hSmin' hi'S hi'ne k hkne'
  have hmaxR := iterate_max'_spread_S hS hSne hSmax' hi'S hi'ne k hkne'
  have hti := translate_support_min' i hne0 hine
  have hti2 := translate_support_max' i hne0 hine
  have hti' := translate_support_min' i' hne0 hi'ne
  have hti'2 := translate_support_max' i' hne0 hi'ne
  have hsupp_eq : (U^[j] (translate i s₀)).support = (U^[k] (translate i' s₀)).support :=
    congrArg Finsupp.support heq
  have hminEq := minCongr hsupp_eq hjne' hkne'
  have hmaxEq := maxCongr hsupp_eq hjne' hkne'
  rw [hminL, hti, hminR, hti'] at hminEq
  rw [hmaxL, hti2, hmaxR, hti'2] at hmaxEq
  -- hminEq : s₀.min' + i - ↑j * a = s₀.min' + i' - ↑k * a
  -- hmaxEq : s₀.max' + i + ↑j * b = s₀.max' + i' + ↑k * b
  have h1 : i - i' = ((j : ℤ) - k) * a := by nlinarith [hminEq]
  have h2 : i - i' = -(((j : ℤ) - k) * b) := by nlinarith [hmaxEq]
  have h3 : ((j : ℤ) - k) * (a + b) = 0 := by nlinarith [h1, h2]
  have hjk : (j : ℤ) = (k : ℤ) := by
    rcases mul_eq_zero.mp h3 with h | h
    · omega
    · omega
  have hjk' : j = k := by omega
  refine ⟨hjk', ?_⟩
  rw [hjk] at h1
  linarith [h1]

/-- **The engine: `n + 2 t + 1 - diam s₀` is a lower bound**, at exact endpoint moves `(a, b)` with
`a + b ≥ 1` on a set `S` the update preserves and which holds every translate of a fixed nonzero
`s₀`. Route: the translates `translate i s₀` for `i` in a window based at `-t - s₀.support.min'`,
read through `Fin c` at `c := n + 2 t + 1 - diam s₀`, form an antichain of `Reaches U` inside
`lightCone n t ∩ GrowingPart U diam`, each translate being `(G2)` (`translate_mem_growingPart`) and
pairwise `Reaches`-incomparable and pairwise distinct under `mergeMk` (`translate_orbit_eq`, at `j =
k` for the antichain half and at `j = k` again — a single exponent, since `Merges` supplies one —
for the injectivity half). -/
theorem linear_le_growingWidth_lightCone_of_invariant
    (hS : ∀ s ∈ S, U s ∈ S) (hSne : ∀ s ∈ S, s ≠ 0)
    (hSmin' : ∀ s ∈ S, ∀ (hne : s.support.Nonempty) (hne' : (U s).support.Nonempty),
      (U s).support.min' hne' = s.support.min' hne - a)
    (hSmax' : ∀ s ∈ S, ∀ (hne : s.support.Nonempty) (hne' : (U s).support.Nonempty),
      (U s).support.max' hne' = s.support.max' hne + b)
    (hab : 1 ≤ a + b) {s₀ : ℤ →₀ ZMod 2} (hs₀ : ∀ i : ℤ, translate i s₀ ∈ S) (n t : ℕ) :
    ((n + 2 * t + 1 - diam s₀ : ℕ) : ℕ∞) ≤ growingWidth U diam (lightCone n) t := by
  have hs0S : s₀ ∈ S := by have h := hs₀ 0; rwa [translate_zero] at h
  have hne0 : s₀.support.Nonempty := Finsupp.support_nonempty_iff.mpr (hSne _ hs0S)
  set m₀ := s₀.support.min' hne0 with hm₀_def
  set M₀ := s₀.support.max' hne0 with hM₀_def
  set c : ℕ := n + 2 * t + 1 - diam s₀ with hc_def
  set i₀ : ℤ := -(t : ℤ) - m₀ with hi₀_def
  set F : Fin c → (ℤ →₀ ZMod 2) := fun k => translate (i₀ + (k : ℤ)) s₀ with hF_def
  have hFS : ∀ k : Fin c, F k ∈ S := fun k => hs₀ _
  have hFne : ∀ k : Fin c, (F k).support.Nonempty :=
    fun k => Finsupp.support_nonempty_iff.mpr (hSne _ (hFS k))
  have hFbound : ∀ k : Fin c, ∀ x ∈ (F k).support,
      m₀ + (i₀ + (k : ℤ)) ≤ x ∧ x ≤ M₀ + (i₀ + (k : ℤ)) :=
    fun k _ hx => translate_support_bound (i₀ + (k : ℤ)) hne0 hx
  have hdiam_eq : diam s₀ = (M₀ - m₀).toNat + 1 := diam_eq' hne0
  have hFcone : ∀ k : Fin c, F k ∈ lightCone n t := by
    intro k x hx
    have hb := hFbound k x hx
    have hkc : (k : ℕ) < c := k.isLt
    have hkpos : (0 : ℤ) ≤ (k : ℤ) := Int.natCast_nonneg _
    constructor <;> omega
  have hFgrow : ∀ k : Fin c, F k ∈ GrowingPart U diam :=
    fun k => translate_mem_growingPart hS hSne hSmin' hSmax' hab hs₀ _
  have hmergeInj : Function.Injective (fun k : Fin c => mergeMk U (F k)) := by
    intro k1 k2 heq
    have hM : Merges U (F k1) (F k2) := Quotient.exact heq
    obtain ⟨k', hk'⟩ := hM
    have hres := translate_orbit_eq hS hSne hSmin' hSmax' hab hs₀ (i := i₀ + (k1 : ℤ))
      (i' := i₀ + (k2 : ℤ)) (j := k') (k := k') hk'
    have h2 := hres.2
    exact Fin.ext (by omega)
  set A : Set (MergeQuot U) := Set.range (fun k : Fin c => mergeMk U (F k)) with hA_def
  have hAcard : A.encard = (c : ℕ∞) := by
    rw [hA_def, hmergeInj.encard_range, ENat.card_eq_coe_fintype_card, Fintype.card_fin]
  have hAsub : A ⊆ mergeStage U (fun t' => lightCone n t' ∩ GrowingPart U diam) t := by
    rintro _ ⟨k, rfl⟩
    exact ⟨F k, ⟨hFcone k, hFgrow k⟩, rfl⟩
  have hAanti : IsAntichain (Reaches U) A := by
    rintro _ ⟨k1, rfl⟩ _ ⟨k2, rfl⟩ hne ⟨j, hj⟩
    rw [mergeLaw_iterate_mergeMk] at hj
    have hM : Merges U (U^[j] (F k1)) (F k2) := Quotient.exact hj
    obtain ⟨k', hk'⟩ := hM
    have heq2 : U^[k' + j] (F k1) = U^[k'] (F k2) := by
      rw [Function.iterate_add_apply]; exact hk'
    have hres := translate_orbit_eq hS hSne hSmin' hSmax' hab hs₀ (i := i₀ + (k1 : ℤ))
      (i' := i₀ + (k2 : ℤ)) (j := k' + j) (k := k') heq2
    have h2 := hres.2
    exact hne (congrArg (fun k => mergeMk U (F k)) (Fin.ext (show (k1 : ℕ) = (k2 : ℕ) by omega)))
  have hle : (c : ℕ∞) ≤ growingWidth U diam (lightCone n) t := by
    unfold growingWidth
    rw [← hAcard]
    exact le_sSup ⟨A, ⟨hAsub, hAanti⟩, rfl⟩
  rwa [hc_def]

/-- **The engine's unbounded corollary**, at the same hypotheses. -/
theorem growingWidth_lightCone_unbounded_of_invariant
    (hS : ∀ s ∈ S, U s ∈ S) (hSne : ∀ s ∈ S, s ≠ 0)
    (hSmin' : ∀ s ∈ S, ∀ (hne : s.support.Nonempty) (hne' : (U s).support.Nonempty),
      (U s).support.min' hne' = s.support.min' hne - a)
    (hSmax' : ∀ s ∈ S, ∀ (hne : s.support.Nonempty) (hne' : (U s).support.Nonempty),
      (U s).support.max' hne' = s.support.max' hne + b)
    (hab : 1 ≤ a + b) {s₀ : ℤ →₀ ZMod 2} (hs₀ : ∀ i : ℤ, translate i s₀ ∈ S) (n : ℕ) :
    ∀ N : ℕ, ∃ t : ℕ, (N : ℕ∞) < growingWidth U diam (lightCone n) t := by
  intro N
  refine ⟨N + diam s₀, ?_⟩
  have hbound := linear_le_growingWidth_lightCone_of_invariant hS hSne hSmin' hSmax' hab hs₀ n
    (N + diam s₀)
  have hlt : N < n + 2 * (N + diam s₀) + 1 - diam s₀ := by omega
  exact lt_of_lt_of_le (by exact_mod_cast hlt) hbound

end Engine

/-! ## Piece 2: the table-bit leaves -/

section TableLeaves

variable {f : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2} {hq : f 0 0 0 = 0}

/-- **Left tap** (`f 0 0 1 = 1`): the leftmost support cell fires, so nothing longer holds it. -/
theorem tableRule_ne_zero_of_leftTap (h : f 0 0 1 = 1) {s : ℤ →₀ ZMod 2} (hs : s ≠ 0) :
    tableRule f hq s ≠ 0 := by
  have hne : s.support.Nonempty := Finsupp.support_nonempty_iff.mpr hs
  set m := s.support.min' hne with hm_def
  intro hcontra
  have hval : tableRule f hq s (m - 1) = 0 := by rw [hcontra]; simp
  rw [tableRule_apply] at hval
  have h1 : s (m - 1 - 1) = 0 := below_min'_eq_zero hne (by omega)
  have h2 : s (m - 1) = 0 := below_min'_eq_zero hne (by omega)
  have h3 : s (m - 1 + 1) = 1 := by
    rw [show m - 1 + 1 = m by omega]
    exact zmod2_eq_one_of_ne_zero' _ (Finsupp.mem_support_iff.mp (Finset.min'_mem s.support hne))
  rw [h1, h2, h3, h] at hval
  exact absurd hval (by decide)

/-- **Left tap, the exact spread**: the leftmost support cell moves left by exactly one. -/
theorem tableRule_min'_of_leftTap (h : f 0 0 1 = 1) {s : ℤ →₀ ZMod 2} (hne : s.support.Nonempty)
    (hne' : (tableRule f hq s).support.Nonempty) :
    (tableRule f hq s).support.min' hne' = s.support.min' hne - 1 := by
  set m := s.support.min' hne with hm_def
  rw [Finset.min'_eq_iff]
  refine ⟨?_, ?_⟩
  · rw [Finsupp.mem_support_iff, tableRule_apply]
    have h1 : s (m - 1 - 1) = 0 := below_min'_eq_zero hne (by omega)
    have h2 : s (m - 1) = 0 := below_min'_eq_zero hne (by omega)
    have h3 : s (m - 1 + 1) = 1 := by
      rw [show m - 1 + 1 = m by omega]
      exact zmod2_eq_one_of_ne_zero' _ (Finsupp.mem_support_iff.mp (Finset.min'_mem s.support hne))
    rw [h1, h2, h3, h]; decide
  · intro y hy
    rw [Finsupp.mem_support_iff, tableRule_apply] at hy
    by_contra hlt
    push Not at hlt
    apply hy
    have h1 : s (y - 1) = 0 := below_min'_eq_zero hne (by omega)
    have h2 : s y = 0 := below_min'_eq_zero hne (by omega)
    have h3 : s (y + 1) = 0 := below_min'_eq_zero hne (by omega)
    rw [h1, h2, h3]
    exact hq

/-- **Right tap** (`f 1 0 0 = 1`), the mirror of `tableRule_ne_zero_of_leftTap`. -/
private theorem tableRule_ne_zero_of_rightTap (h : f 1 0 0 = 1) {s : ℤ →₀ ZMod 2} (hs : s ≠ 0) :
    tableRule f hq s ≠ 0 := by
  have hne : s.support.Nonempty := Finsupp.support_nonempty_iff.mpr hs
  set M := s.support.max' hne with hM_def
  intro hcontra
  have hval : tableRule f hq s (M + 1) = 0 := by rw [hcontra]; simp
  rw [tableRule_apply] at hval
  have h1 : s (M + 1 - 1) = 1 := by
    rw [show M + 1 - 1 = M by omega]
    exact zmod2_eq_one_of_ne_zero' _ (Finsupp.mem_support_iff.mp (Finset.max'_mem s.support hne))
  have h2 : s (M + 1) = 0 := above_max'_eq_zero hne (by omega)
  have h3 : s (M + 1 + 1) = 0 := above_max'_eq_zero hne (by omega)
  rw [h1, h2, h3, h] at hval
  exact absurd hval (by decide)

/-- **Right tap, the exact spread**, the mirror of `tableRule_min'_of_leftTap`. -/
theorem tableRule_max'_of_rightTap (h : f 1 0 0 = 1) {s : ℤ →₀ ZMod 2} (hne : s.support.Nonempty)
    (hne' : (tableRule f hq s).support.Nonempty) :
    (tableRule f hq s).support.max' hne' = s.support.max' hne + 1 := by
  set M := s.support.max' hne with hM_def
  rw [Finset.max'_eq_iff]
  refine ⟨?_, ?_⟩
  · rw [Finsupp.mem_support_iff, tableRule_apply]
    have h1 : s (M + 1 - 1) = 1 := by
      rw [show M + 1 - 1 = M by omega]
      exact zmod2_eq_one_of_ne_zero' _ (Finsupp.mem_support_iff.mp (Finset.max'_mem s.support hne))
    have h2 : s (M + 1) = 0 := above_max'_eq_zero hne (by omega)
    have h3 : s (M + 1 + 1) = 0 := above_max'_eq_zero hne (by omega)
    rw [h1, h2, h3, h]; decide
  · intro y hy
    rw [Finsupp.mem_support_iff, tableRule_apply] at hy
    by_contra hlt
    push Not at hlt
    apply hy
    have h1 : s (y - 1) = 0 := above_max'_eq_zero hne (by omega)
    have h2 : s y = 0 := above_max'_eq_zero hne (by omega)
    have h3 : s (y + 1) = 0 := above_max'_eq_zero hne (by omega)
    rw [h1, h2, h3]
    exact hq

/-- **Left hold** (`f 0 0 1 = 0`, `f 0 1 0 = 1`, `f 0 1 1 = 1`): the leftmost cell holds whatever
its right neighbour, no tap. -/
private theorem tableRule_ne_zero_of_leftHold (_h1 : f 0 0 1 = 0) (h2 : f 0 1 0 = 1)
    (h3 : f 0 1 1 = 1) {s : ℤ →₀ ZMod 2} (hs : s ≠ 0) : tableRule f hq s ≠ 0 := by
  have hne : s.support.Nonempty := Finsupp.support_nonempty_iff.mpr hs
  set m := s.support.min' hne with hm_def
  intro hcontra
  have hval : tableRule f hq s m = 0 := by rw [hcontra]; simp
  rw [tableRule_apply] at hval
  have hleft : s (m - 1) = 0 := below_min'_eq_zero hne (by omega)
  have hmid : s m = 1 :=
    zmod2_eq_one_of_ne_zero' _ (Finsupp.mem_support_iff.mp (Finset.min'_mem s.support hne))
  by_cases hc : s (m + 1) = 0
  · rw [hleft, hmid, hc, h2] at hval; exact absurd hval (by decide)
  · have h1' : s (m + 1) = 1 := zmod2_eq_one_of_ne_zero' _ hc
    rw [hleft, hmid, h1', h3] at hval; exact absurd hval (by decide)

/-- **Left hold, the exact spread — the leftmost cell UNCHANGED**. -/
theorem tableRule_min'_of_leftHold (h1 : f 0 0 1 = 0) (h2 : f 0 1 0 = 1) (h3 : f 0 1 1 = 1)
    {s : ℤ →₀ ZMod 2} (hne : s.support.Nonempty) (hne' : (tableRule f hq s).support.Nonempty) :
    (tableRule f hq s).support.min' hne' = s.support.min' hne := by
  set m := s.support.min' hne with hm_def
  rw [Finset.min'_eq_iff]
  refine ⟨?_, ?_⟩
  · rw [Finsupp.mem_support_iff, tableRule_apply]
    have hleft : s (m - 1) = 0 := below_min'_eq_zero hne (by omega)
    have hmid : s m = 1 :=
      zmod2_eq_one_of_ne_zero' _ (Finsupp.mem_support_iff.mp (Finset.min'_mem s.support hne))
    by_cases hc : s (m + 1) = 0
    · rw [hleft, hmid, hc, h2]; decide
    · have h1' : s (m + 1) = 1 := zmod2_eq_one_of_ne_zero' _ hc
      rw [hleft, hmid, h1', h3]; decide
  · intro y hy
    rw [Finsupp.mem_support_iff, tableRule_apply] at hy
    by_contra hlt
    push Not at hlt
    apply hy
    have h1' : s (y - 1) = 0 := below_min'_eq_zero hne (by omega)
    have h2' : s y = 0 := below_min'_eq_zero hne (by omega)
    by_cases hbc : y + 1 = m
    · have h3' : s (y + 1) = 1 := by
        rw [hbc]
        exact zmod2_eq_one_of_ne_zero' _
          (Finsupp.mem_support_iff.mp (Finset.min'_mem s.support hne))
      rw [h1', h2', h3', h1]
    · have h3' : s (y + 1) = 0 := below_min'_eq_zero hne (by omega)
      rw [h1', h2', h3']
      exact hq

/-- **Right hold** (`f 1 0 0 = 0`, `f 0 1 0 = 1`, `f 1 1 0 = 1`), the mirror. -/
private theorem tableRule_ne_zero_of_rightHold (_h1 : f 1 0 0 = 0) (h2 : f 0 1 0 = 1)
    (h3 : f 1 1 0 = 1) {s : ℤ →₀ ZMod 2} (hs : s ≠ 0) : tableRule f hq s ≠ 0 := by
  have hne : s.support.Nonempty := Finsupp.support_nonempty_iff.mpr hs
  set M := s.support.max' hne with hM_def
  intro hcontra
  have hval : tableRule f hq s M = 0 := by rw [hcontra]; simp
  rw [tableRule_apply] at hval
  have hright : s (M + 1) = 0 := above_max'_eq_zero hne (by omega)
  have hmid : s M = 1 :=
    zmod2_eq_one_of_ne_zero' _ (Finsupp.mem_support_iff.mp (Finset.max'_mem s.support hne))
  by_cases hc : s (M - 1) = 0
  · rw [hc, hmid, hright, h2] at hval; exact absurd hval (by decide)
  · have h1' : s (M - 1) = 1 := zmod2_eq_one_of_ne_zero' _ hc
    rw [h1', hmid, hright, h3] at hval; exact absurd hval (by decide)

/-- **Right hold, the exact spread — the rightmost cell UNCHANGED**, the mirror. -/
theorem tableRule_max'_of_rightHold (h1 : f 1 0 0 = 0) (h2 : f 0 1 0 = 1) (h3 : f 1 1 0 = 1)
    {s : ℤ →₀ ZMod 2} (hne : s.support.Nonempty) (hne' : (tableRule f hq s).support.Nonempty) :
    (tableRule f hq s).support.max' hne' = s.support.max' hne := by
  set M := s.support.max' hne with hM_def
  rw [Finset.max'_eq_iff]
  refine ⟨?_, ?_⟩
  · rw [Finsupp.mem_support_iff, tableRule_apply]
    have hright : s (M + 1) = 0 := above_max'_eq_zero hne (by omega)
    have hmid : s M = 1 :=
      zmod2_eq_one_of_ne_zero' _ (Finsupp.mem_support_iff.mp (Finset.max'_mem s.support hne))
    by_cases hc : s (M - 1) = 0
    · rw [hc, hmid, hright, h2]; decide
    · have h1' : s (M - 1) = 1 := zmod2_eq_one_of_ne_zero' _ hc
      rw [h1', hmid, hright, h3]; decide
  · intro y hy
    rw [Finsupp.mem_support_iff, tableRule_apply] at hy
    by_contra hlt
    push Not at hlt
    apply hy
    have h2' : s y = 0 := above_max'_eq_zero hne (by omega)
    have h3' : s (y + 1) = 0 := above_max'_eq_zero hne (by omega)
    by_cases hbc : y - 1 = M
    · have h1' : s (y - 1) = 1 := by
        rw [hbc]
        exact zmod2_eq_one_of_ne_zero' _
          (Finsupp.mem_support_iff.mp (Finset.max'_mem s.support hne))
      rw [h1', h2', h3', h1]
    · have h1' : s (y - 1) = 0 := above_max'_eq_zero hne (by omega)
      rw [h1', h2', h3']
      exact hq

/-! ### The end-word: two rightmost (or leftmost) cells held together -/

/-- **The right end-word `11`**: nonempty support with its two rightmost cells both set. -/
def EndsOneOne (s : ℤ →₀ ZMod 2) : Prop :=
  ∃ hne : s.support.Nonempty, s (s.support.max' hne - 1) = 1

/-- **The left end-word `11`**, the mirror. -/
def StartsOneOne (s : ℤ →₀ ZMod 2) : Prop :=
  ∃ hne : s.support.Nonempty, s (s.support.min' hne + 1) = 1

private theorem endsOneOne_ne_zero {s : ℤ →₀ ZMod 2} (h : EndsOneOne s) : s ≠ 0 :=
  Finsupp.support_nonempty_iff.mp h.1

private theorem startsOneOne_ne_zero {s : ℤ →₀ ZMod 2} (h : StartsOneOne s) : s ≠ 0 :=
  Finsupp.support_nonempty_iff.mp h.1

/-- **The right end-word held, the rightmost cell UNCHANGED** (`f 1 0 0 = 0`, `f 1 1 0 = 1`,
`f 0 1 1 = 1`, `f 1 1 1 = 1`): the cell `max'` sees `(1, 1, 0)` and the cell `max' - 1` sees
`(x, 1, 1)`, both firing regardless of `x`; `max' + 1` sees `(1, 0, 0)` and does not. -/
theorem tableRule_max'_of_endsOneOne (h1 : f 1 0 0 = 0) (h2 : f 1 1 0 = 1) (_h3 : f 0 1 1 = 1)
    (_h4 : f 1 1 1 = 1) {s : ℤ →₀ ZMod 2} (hs : EndsOneOne s) (hne : s.support.Nonempty)
    (hne' : (tableRule f hq s).support.Nonempty) :
    (tableRule f hq s).support.max' hne' = s.support.max' hne := by
  obtain ⟨_, hval⟩ := hs
  set M := s.support.max' hne with hM_def
  rw [Finset.max'_eq_iff]
  refine ⟨?_, ?_⟩
  · rw [Finsupp.mem_support_iff, tableRule_apply]
    have hM1 : s (M + 1) = 0 := above_max'_eq_zero hne (by omega)
    have hMval : s M = 1 :=
      zmod2_eq_one_of_ne_zero' _ (Finsupp.mem_support_iff.mp (Finset.max'_mem s.support hne))
    have hMm1 : s (M - 1) = 1 := hval
    rw [hMm1, hMval, hM1, h2]; decide
  · intro y hy
    rw [Finsupp.mem_support_iff, tableRule_apply] at hy
    by_contra hlt
    push Not at hlt
    apply hy
    have h2' : s y = 0 := above_max'_eq_zero hne (by omega)
    have h3' : s (y + 1) = 0 := above_max'_eq_zero hne (by omega)
    by_cases hbc : y - 1 = M
    · have h1' : s (y - 1) = 1 := by
        rw [hbc]
        exact zmod2_eq_one_of_ne_zero' _
          (Finsupp.mem_support_iff.mp (Finset.max'_mem s.support hne))
      rw [h1', h2', h3', h1]
    · have h1' : s (y - 1) = 0 := above_max'_eq_zero hne (by omega)
      rw [h1', h2', h3']
      exact hq

/-- **The right end-word is `U`-invariant**. -/
theorem endsOneOne_tableRule (h1 : f 1 0 0 = 0) (h2 : f 1 1 0 = 1) (h3 : f 0 1 1 = 1)
    (h4 : f 1 1 1 = 1) {s : ℤ →₀ ZMod 2} (hs : EndsOneOne s) : EndsOneOne (tableRule f hq s) := by
  have hne : s.support.Nonempty := endsOneOne_ne_zero hs |> Finsupp.support_nonempty_iff.mpr
  obtain ⟨_, hval⟩ := hs
  have hval' : tableRule f hq s (s.support.max' hne) ≠ 0 := by
    rw [tableRule_apply]
    have hM1 : s (s.support.max' hne + 1) = 0 := above_max'_eq_zero hne (by omega)
    have hMval : s (s.support.max' hne) = 1 :=
      zmod2_eq_one_of_ne_zero' _ (Finsupp.mem_support_iff.mp (Finset.max'_mem s.support hne))
    have hMm1 : s (s.support.max' hne - 1) = 1 := hval
    rw [hMm1, hMval, hM1, h2]; decide
  have hne' : (tableRule f hq s).support.Nonempty := ⟨_, Finsupp.mem_support_iff.mpr hval'⟩
  have hmax_eq := tableRule_max'_of_endsOneOne h1 h2 h3 h4 ⟨hne, hval⟩ hne hne'
  refine ⟨hne', ?_⟩
  rw [hmax_eq, tableRule_apply]
  set M := s.support.max' hne with hM_def
  have hmid : s (M - 1) = 1 := hval
  have hright : s (M - 1 + 1) = 1 := by
    rw [show M - 1 + 1 = M by omega]
    exact zmod2_eq_one_of_ne_zero' _ (Finsupp.mem_support_iff.mp (Finset.max'_mem s.support hne))
  by_cases hc : s (M - 1 - 1) = 0
  · rw [hc, hmid, hright, h3]
  · have hleft : s (M - 1 - 1) = 1 := zmod2_eq_one_of_ne_zero' _ hc
    rw [hleft, hmid, hright, h4]

/-- **The right end-word is translation-invariant**. -/
theorem endsOneOne_translate {i : ℤ} {s : ℤ →₀ ZMod 2} (h : EndsOneOne s) :
    EndsOneOne (translate i s) := by
  obtain ⟨hne, hval⟩ := h
  have hne' : (translate i s).support.Nonempty := by rw [translate_support]; exact hne.image _
  have hmax : (translate i s).support.max' hne' = s.support.max' hne + i :=
    translate_support_max' i hne hne'
  refine ⟨hne', ?_⟩
  rw [hmax, show s.support.max' hne + i - 1 = (s.support.max' hne - 1) + i by ring, translate_apply]
  exact hval

/-- **The left end-word held, the leftmost cell UNCHANGED**, the mirror of `tableRule_max'_of_
endsOneOne`. -/
theorem tableRule_min'_of_startsOneOne (h1 : f 0 0 1 = 0) (h2 : f 0 1 1 = 1) (_h3 : f 1 1 0 = 1)
    (_h4 : f 1 1 1 = 1) {s : ℤ →₀ ZMod 2} (hs : StartsOneOne s) (hne : s.support.Nonempty)
    (hne' : (tableRule f hq s).support.Nonempty) :
    (tableRule f hq s).support.min' hne' = s.support.min' hne := by
  obtain ⟨_, hval⟩ := hs
  set m := s.support.min' hne with hm_def
  rw [Finset.min'_eq_iff]
  refine ⟨?_, ?_⟩
  · rw [Finsupp.mem_support_iff, tableRule_apply]
    have hm1 : s (m - 1) = 0 := below_min'_eq_zero hne (by omega)
    have hmval : s m = 1 :=
      zmod2_eq_one_of_ne_zero' _ (Finsupp.mem_support_iff.mp (Finset.min'_mem s.support hne))
    have hmp1 : s (m + 1) = 1 := hval
    rw [hm1, hmval, hmp1, h2]; decide
  · intro y hy
    rw [Finsupp.mem_support_iff, tableRule_apply] at hy
    by_contra hlt
    push Not at hlt
    apply hy
    have h1' : s (y - 1) = 0 := below_min'_eq_zero hne (by omega)
    have h2' : s y = 0 := below_min'_eq_zero hne (by omega)
    by_cases hbc : y + 1 = m
    · have h3' : s (y + 1) = 1 := by
        rw [hbc]
        exact zmod2_eq_one_of_ne_zero' _
          (Finsupp.mem_support_iff.mp (Finset.min'_mem s.support hne))
      rw [h1', h2', h3', h1]
    · have h3' : s (y + 1) = 0 := below_min'_eq_zero hne (by omega)
      rw [h1', h2', h3']
      exact hq

/-- **The left end-word is `U`-invariant**, the mirror of `endsOneOne_tableRule`. -/
theorem startsOneOne_tableRule (h1 : f 0 0 1 = 0) (h2 : f 0 1 1 = 1) (h3 : f 1 1 0 = 1)
    (h4 : f 1 1 1 = 1) {s : ℤ →₀ ZMod 2} (hs : StartsOneOne s) :
    StartsOneOne (tableRule f hq s) := by
  have hne : s.support.Nonempty := startsOneOne_ne_zero hs |> Finsupp.support_nonempty_iff.mpr
  obtain ⟨_, hval⟩ := hs
  have hval' : tableRule f hq s (s.support.min' hne) ≠ 0 := by
    rw [tableRule_apply]
    have hm1 : s (s.support.min' hne - 1) = 0 := below_min'_eq_zero hne (by omega)
    have hmval : s (s.support.min' hne) = 1 :=
      zmod2_eq_one_of_ne_zero' _ (Finsupp.mem_support_iff.mp (Finset.min'_mem s.support hne))
    have hmp1 : s (s.support.min' hne + 1) = 1 := hval
    rw [hm1, hmval, hmp1, h2]; decide
  have hne' : (tableRule f hq s).support.Nonempty := ⟨_, Finsupp.mem_support_iff.mpr hval'⟩
  have hmin_eq := tableRule_min'_of_startsOneOne h1 h2 h3 h4 ⟨hne, hval⟩ hne hne'
  refine ⟨hne', ?_⟩
  rw [hmin_eq, tableRule_apply]
  set m := s.support.min' hne with hm_def
  have hmid : s (m + 1) = 1 := hval
  have hleft : s (m + 1 - 1) = 1 := by
    rw [show m + 1 - 1 = m by omega]
    exact zmod2_eq_one_of_ne_zero' _ (Finsupp.mem_support_iff.mp (Finset.min'_mem s.support hne))
  by_cases hc : s (m + 1 + 1) = 0
  · rw [hleft, hmid, hc, h3]
  · have hright : s (m + 1 + 1) = 1 := zmod2_eq_one_of_ne_zero' _ hc
    rw [hleft, hmid, hright, h4]

/-- **The left end-word is translation-invariant**, the mirror of `endsOneOne_translate`. -/
theorem startsOneOne_translate {i : ℤ} {s : ℤ →₀ ZMod 2} (h : StartsOneOne s) :
    StartsOneOne (translate i s) := by
  obtain ⟨hne, hval⟩ := h
  have hne' : (translate i s).support.Nonempty := by rw [translate_support]; exact hne.image _
  have hmin : (translate i s).support.min' hne' = s.support.min' hne + i :=
    translate_support_min' i hne hne'
  refine ⟨hne', ?_⟩
  rw [hmin, show s.support.min' hne + i + 1 = (s.support.min' hne + 1) + i by ring, translate_apply]
  exact hval

/-- **The light cone advances under EVERY quiescent table**: `tableRule`'s own support bound
widens by at most one cell at each end. -/
theorem advances_lightCone_tableRule (f : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2) (hq : f 0 0 0 = 0)
    (n : ℕ) : Advances (tableRule f hq) (lightCone n) := by
  intro t s hs x hx
  have hb := Finsupp.support_onFinset_subset hx
  simp only [Finset.mem_union, Finset.mem_image] at hb
  rcases hb with (⟨y, hy, rfl⟩ | ⟨y, hy, rfl⟩) | hb
  · have := hs y hy; omega
  · have := hs y hy; omega
  · have := hs x hb; omega

end TableLeaves

/-! ## Piece 3: the zero side — a non-increasing diameter empties the `(G2)`-part -/

theorem growingPart_eq_empty_of_diam_le {U : (ℤ →₀ ZMod 2) → (ℤ →₀ ZMod 2)}
    (hU : ∀ s, diam (U s) ≤ diam s) : GrowingPart U diam = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  intro s hs
  have hmono : ∀ k : ℕ, diam (U^[k] s) ≤ diam s := by
    intro k
    induction k with
    | zero => simp
    | succ j ih => rw [Function.iterate_succ_apply']; exact (hU _).trans ih
  obtain ⟨k, hk⟩ := hs (diam s)
  have := hmono k
  omega

theorem growingWidth_lightCone_eq_zero_of_diam_le {U : (ℤ →₀ ZMod 2) → (ℤ →₀ ZMod 2)}
    (hU : ∀ s, diam (U s) ≤ diam s) (n t : ℕ) :
    growingWidth U diam (lightCone n) t = 0 := by
  unfold growingWidth
  exact memWidth_eq_zero_of_empty (by rw [growingPart_eq_empty_of_diam_le hU, Set.inter_empty])

section ZeroLeaves

variable {f : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2} {hq : f 0 0 0 = 0}

private theorem tableRule_zero' (f : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2) (hq : f 0 0 0 = 0) :
    tableRule f hq 0 = 0 := by
  ext i
  rw [tableRule_apply]
  simpa using hq

/-- **No tap on either side** (`f 0 0 1 = 0`, `f 1 0 0 = 0`): the image's support sits inside
`[min', max']`. -/
theorem diam_tableRule_le_of_noTap (h1 : f 0 0 1 = 0) (h2 : f 1 0 0 = 0) (s : ℤ →₀ ZMod 2) :
    diam (tableRule f hq s) ≤ diam s := by
  by_cases hs : s = 0
  · subst hs; rw [tableRule_zero']
  · have hne : s.support.Nonempty := Finsupp.support_nonempty_iff.mpr hs
    have hbound : ∀ x ∈ (tableRule f hq s).support,
        s.support.min' hne ≤ x ∧ x ≤ s.support.max' hne := by
      intro x hx
      rw [Finsupp.mem_support_iff, tableRule_apply] at hx
      by_contra hc
      rw [not_and_or, not_le, not_le] at hc
      apply hx
      rcases hc with hc | hc
      · by_cases hbc : x + 1 = s.support.min' hne
        · have hr : s (x + 1) = 1 := by
            rw [hbc]
            exact zmod2_eq_one_of_ne_zero' _
              (Finsupp.mem_support_iff.mp (Finset.min'_mem s.support hne))
          have hl : s (x - 1) = 0 := below_min'_eq_zero hne (by omega)
          have hc0 : s x = 0 := below_min'_eq_zero hne (by omega)
          rw [hl, hc0, hr, h1]
        · have hr : s (x + 1) = 0 := below_min'_eq_zero hne (by omega)
          have hl : s (x - 1) = 0 := below_min'_eq_zero hne (by omega)
          have hc0 : s x = 0 := below_min'_eq_zero hne (by omega)
          rw [hl, hc0, hr]; exact hq
      · by_cases hbc : x - 1 = s.support.max' hne
        · have hl : s (x - 1) = 1 := by
            rw [hbc]
            exact zmod2_eq_one_of_ne_zero' _
              (Finsupp.mem_support_iff.mp (Finset.max'_mem s.support hne))
          have hr : s (x + 1) = 0 := above_max'_eq_zero hne (by omega)
          have hc0 : s x = 0 := above_max'_eq_zero hne (by omega)
          rw [hl, hc0, hr, h2]
        · have hl : s (x - 1) = 0 := above_max'_eq_zero hne (by omega)
          have hr : s (x + 1) = 0 := above_max'_eq_zero hne (by omega)
          have hc0 : s x = 0 := above_max'_eq_zero hne (by omega)
          rw [hl, hc0, hr]; exact hq
    rw [diam_eq' hne]
    exact diam_le_of_support_subset hbound (Finset.min'_le_max' s.support hne)

/-- **Left tap, right dies** (`f 0 0 1 = 1`, `f 1 0 0 = 0`, `f 0 1 0 = 0`, `f 1 1 0 = 0`): the
image's support sits inside `[min' - 1, max' - 1]`, the cell `max'` seeing `(x, 1, 0)` and dying
regardless of `x`. -/
theorem diam_tableRule_le_of_leftTap_rightDies (_h1 : f 0 0 1 = 1) (h2 : f 1 0 0 = 0)
    (h3 : f 0 1 0 = 0) (h4 : f 1 1 0 = 0) (s : ℤ →₀ ZMod 2) :
    diam (tableRule f hq s) ≤ diam s := by
  by_cases hs : s = 0
  · subst hs; rw [tableRule_zero']
  · have hne : s.support.Nonempty := Finsupp.support_nonempty_iff.mpr hs
    have hbound : ∀ x ∈ (tableRule f hq s).support,
        s.support.min' hne - 1 ≤ x ∧ x ≤ s.support.max' hne - 1 := by
      intro x hx
      rw [Finsupp.mem_support_iff, tableRule_apply] at hx
      by_contra hc
      rw [not_and_or, not_le, not_le] at hc
      apply hx
      rcases hc with hc | hc
      · have hl : s (x - 1) = 0 := below_min'_eq_zero hne (by omega)
        have hc0 : s x = 0 := below_min'_eq_zero hne (by omega)
        have hr : s (x + 1) = 0 := below_min'_eq_zero hne (by omega)
        rw [hl, hc0, hr]; exact hq
      · by_cases hbc0 : x = s.support.max' hne
        · have hc0 : s x = 1 := by
            rw [hbc0]
            exact zmod2_eq_one_of_ne_zero' _
              (Finsupp.mem_support_iff.mp (Finset.max'_mem s.support hne))
          have hr : s (x + 1) = 0 := above_max'_eq_zero hne (by omega)
          by_cases hlc : s (x - 1) = 0
          · rw [hlc, hc0, hr, h3]
          · have hl : s (x - 1) = 1 := zmod2_eq_one_of_ne_zero' _ hlc
            rw [hl, hc0, hr, h4]
        · by_cases hbc1 : x - 1 = s.support.max' hne
          · -- x = max' + 1: value f(1, 0, 0), the cell that dies via h2.
            have hl : s (x - 1) = 1 := by
              rw [hbc1]
              exact zmod2_eq_one_of_ne_zero' _
                (Finsupp.mem_support_iff.mp (Finset.max'_mem s.support hne))
            have hc0 : s x = 0 := above_max'_eq_zero hne (by omega)
            have hr : s (x + 1) = 0 := above_max'_eq_zero hne (by omega)
            rw [hl, hc0, hr, h2]
          · have hl : s (x - 1) = 0 := above_max'_eq_zero hne (by omega)
            have hc0 : s x = 0 := above_max'_eq_zero hne (by omega)
            have hr : s (x + 1) = 0 := above_max'_eq_zero hne (by omega)
            rw [hl, hc0, hr]; exact hq
    have hstep := diam_le_of_support_subset hbound
      (by have := Finset.min'_le_max' s.support hne; omega)
    have hd : diam s = (s.support.max' hne - s.support.min' hne).toNat + 1 := diam_eq' hne
    have heq : s.support.max' hne - 1 - (s.support.min' hne - 1) =
        s.support.max' hne - s.support.min' hne := by ring
    rw [heq] at hstep
    omega

/-- **Right tap, left dies**, the mirror of `diam_tableRule_le_of_leftTap_rightDies`. -/
theorem diam_tableRule_le_of_rightTap_leftDies (_h1 : f 1 0 0 = 1) (h2 : f 0 0 1 = 0)
    (h3 : f 0 1 0 = 0) (h4 : f 0 1 1 = 0) (s : ℤ →₀ ZMod 2) :
    diam (tableRule f hq s) ≤ diam s := by
  by_cases hs : s = 0
  · subst hs; rw [tableRule_zero']
  · have hne : s.support.Nonempty := Finsupp.support_nonempty_iff.mpr hs
    have hbound : ∀ x ∈ (tableRule f hq s).support,
        s.support.min' hne + 1 ≤ x ∧ x ≤ s.support.max' hne + 1 := by
      intro x hx
      rw [Finsupp.mem_support_iff, tableRule_apply] at hx
      by_contra hc
      rw [not_and_or, not_le, not_le] at hc
      apply hx
      rcases hc with hc | hc
      · by_cases hbc0 : x = s.support.min' hne
        · have hc0 : s x = 1 := by
            rw [hbc0]
            exact zmod2_eq_one_of_ne_zero' _
              (Finsupp.mem_support_iff.mp (Finset.min'_mem s.support hne))
          have hl : s (x - 1) = 0 := below_min'_eq_zero hne (by omega)
          by_cases hrc : s (x + 1) = 0
          · rw [hl, hc0, hrc, h3]
          · have hr : s (x + 1) = 1 := zmod2_eq_one_of_ne_zero' _ hrc
            rw [hl, hc0, hr, h4]
        · by_cases hbc1 : x + 1 = s.support.min' hne
          · -- x = min' - 1: value f(0, 0, 1), the cell that dies via h2.
            have hr : s (x + 1) = 1 := by
              rw [hbc1]
              exact zmod2_eq_one_of_ne_zero' _
                (Finsupp.mem_support_iff.mp (Finset.min'_mem s.support hne))
            have hc0 : s x = 0 := below_min'_eq_zero hne (by omega)
            have hl : s (x - 1) = 0 := below_min'_eq_zero hne (by omega)
            rw [hl, hc0, hr, h2]
          · have hc0 : s x = 0 := below_min'_eq_zero hne (by omega)
            have hl : s (x - 1) = 0 := below_min'_eq_zero hne (by omega)
            have hr : s (x + 1) = 0 := below_min'_eq_zero hne (by omega)
            rw [hl, hc0, hr]; exact hq
      · have hr : s (x + 1) = 0 := above_max'_eq_zero hne (by omega)
        have hc0 : s x = 0 := above_max'_eq_zero hne (by omega)
        have hl : s (x - 1) = 0 := above_max'_eq_zero hne (by omega)
        rw [hl, hc0, hr]; exact hq
    have hstep := diam_le_of_support_subset hbound
      (by have := Finset.min'_le_max' s.support hne; omega)
    have hd : diam s = (s.support.max' hne - s.support.min' hne).toNat + 1 := diam_eq' hne
    have heq : s.support.max' hne + 1 - (s.support.min' hne + 1) =
        s.support.max' hne - s.support.min' hne := by ring
    rw [heq] at hstep
    omega

end ZeroLeaves

/-! ## Piece 4: the two classes, the counts, and the witness -/

/-- **Class A ∪ Class E**: exact endpoint moves summing to at least `1` — either both endpoints
tap or hold with the other tapping (Class A), or one endpoint is held by a two-cell end-word while
the other taps (Class E, the last two disjuncts). -/
def AccretesByEndpoints (f : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2) : Prop :=
  (f 0 0 1 = 1 ∧ f 1 0 0 = 1) ∨
  (f 0 0 1 = 1 ∧ f 1 0 0 = 0 ∧ f 0 1 0 = 1 ∧ f 1 1 0 = 1) ∨
  (f 1 0 0 = 1 ∧ f 0 0 1 = 0 ∧ f 0 1 0 = 1 ∧ f 0 1 1 = 1) ∨
  (f 0 0 1 = 1 ∧ f 1 0 0 = 0 ∧ f 1 1 0 = 1 ∧ f 0 1 1 = 1 ∧ f 1 1 1 = 1) ∨
  (f 1 0 0 = 1 ∧ f 0 0 1 = 0 ∧ f 0 1 1 = 1 ∧ f 1 1 0 = 1 ∧ f 1 1 1 = 1)

/-- **Class Z**: the diameter is non-increasing at every nonzero state — no tap on either side, or
one tap with the other endpoint always dying. -/
def ZeroByEndpoints (f : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2) : Prop :=
  (f 0 0 1 = 0 ∧ f 1 0 0 = 0) ∨
  (f 0 0 1 = 1 ∧ f 1 0 0 = 0 ∧ f 0 1 0 = 0 ∧ f 1 1 0 = 0) ∨
  (f 1 0 0 = 1 ∧ f 0 0 1 = 0 ∧ f 0 1 0 = 0 ∧ f 0 1 1 = 0)

-- Public (not private): a private instance inside this file's `@[expose] public section` fails
-- as a stuck `Decidable` synthesis in the public theorems below, rather than by name.
instance decidablePred_accretesByEndpoints : DecidablePred AccretesByEndpoints :=
  fun f => by unfold AccretesByEndpoints; infer_instance

instance decidablePred_zeroByEndpoints : DecidablePred ZeroByEndpoints :=
  fun f => by unfold ZeroByEndpoints; infer_instance

private theorem single01_ne_zero : (Finsupp.single (0 : ℤ) (1 : ZMod 2)) ≠ 0 := by
  rw [Ne, Finsupp.single_eq_zero]; decide

/-- **The end-word seed**: the two-cell state `{0, 1}`, both cells set. -/
private noncomputable def endWordSeed : ℤ →₀ ZMod 2 :=
  Finsupp.single (0 : ℤ) (1 : ZMod 2) + Finsupp.single (1 : ℤ) (1 : ZMod 2)

private theorem endWordSeed_apply0 : endWordSeed 0 = 1 := by
  rw [endWordSeed, Finsupp.add_apply, Finsupp.single_apply, Finsupp.single_apply]
  simp

private theorem endWordSeed_apply1 : endWordSeed 1 = 1 := by
  rw [endWordSeed, Finsupp.add_apply, Finsupp.single_apply, Finsupp.single_apply]
  simp

private theorem endWordSeed_apply_other {x : ℤ} (h0 : x ≠ 0) (h1 : x ≠ 1) : endWordSeed x = 0 := by
  rw [endWordSeed, Finsupp.add_apply, Finsupp.single_apply, Finsupp.single_apply]
  simp [Ne.symm h0, Ne.symm h1]

private theorem endWordSeed_hne : endWordSeed.support.Nonempty :=
  ⟨0, Finsupp.mem_support_iff.mpr (by rw [endWordSeed_apply0]; decide)⟩

private theorem endWordSeed_max : endWordSeed.support.max' endWordSeed_hne = 1 := by
  apply le_antisymm
  · apply Finset.max'_le
    intro y hy
    by_contra hc
    push Not at hc
    exact (Finsupp.mem_support_iff.mp hy)
      (endWordSeed_apply_other (by omega) (by omega))
  · exact Finset.le_max' _ 1 (Finsupp.mem_support_iff.mpr (by rw [endWordSeed_apply1]; decide))

private theorem endWordSeed_min : endWordSeed.support.min' endWordSeed_hne = 0 := by
  apply le_antisymm
  · exact Finset.min'_le _ 0 (Finsupp.mem_support_iff.mpr (by rw [endWordSeed_apply0]; decide))
  · apply Finset.le_min'
    intro y hy
    by_contra hc
    push Not at hc
    exact (Finsupp.mem_support_iff.mp hy)
      (endWordSeed_apply_other (by omega) (by omega))

private theorem endWord_seed_endsOneOne : EndsOneOne endWordSeed := by
  refine ⟨endWordSeed_hne, ?_⟩
  rw [endWordSeed_max, show (1 : ℤ) - 1 = 0 by ring, endWordSeed_apply0]

private theorem endWord_seed_startsOneOne : StartsOneOne endWordSeed := by
  refine ⟨endWordSeed_hne, ?_⟩
  rw [endWordSeed_min, show (0 : ℤ) + 1 = 1 by ring, endWordSeed_apply1]

/-- **The class theorem for `AccretesByEndpoints`**: the light cone's growing width is unbounded at
every quiescent table meeting the class — `52` of the `128` quiescent radius-one tables
(`card_accretesByEndpoints`); the `28`-table middle band between this class and `ZeroByEndpoints`
is not decided here. -/
theorem growingWidth_lightCone_unbounded_of_accretesByEndpoints
    (f : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2) (hq : f 0 0 0 = 0) (hf : AccretesByEndpoints f)
    (n : ℕ) : ∀ N : ℕ, ∃ t, (N : ℕ∞) < growingWidth (tableRule f hq) diam (lightCone n) t := by
  rcases hf with h | h | h | h | h
  · exact growingWidth_lightCone_unbounded_of_invariant (S := {s | s ≠ 0}) (a := 1) (b := 1)
      (fun s hs => tableRule_ne_zero_of_leftTap h.1 hs)
      (fun s hs => hs)
      (fun s _ hne hne' => tableRule_min'_of_leftTap h.1 hne hne')
      (fun s _ hne hne' => tableRule_max'_of_rightTap h.2 hne hne')
      (by norm_num) (s₀ := Finsupp.single (0 : ℤ) (1 : ZMod 2))
      (fun i heq => single01_ne_zero ((translate_ne_zero_iff i).mp heq)) n
  · exact growingWidth_lightCone_unbounded_of_invariant (S := {s | s ≠ 0}) (a := 1) (b := 0)
      (fun s hs => tableRule_ne_zero_of_leftTap h.1 hs)
      (fun s hs => hs)
      (fun s _ hne hne' => tableRule_min'_of_leftTap h.1 hne hne')
      (fun s _ hne hne' =>
        (tableRule_max'_of_rightHold h.2.1 h.2.2.1 h.2.2.2 hne hne').trans (add_zero _).symm)
      (by norm_num) (s₀ := Finsupp.single (0 : ℤ) (1 : ZMod 2))
      (fun i heq => single01_ne_zero ((translate_ne_zero_iff i).mp heq)) n
  · exact growingWidth_lightCone_unbounded_of_invariant (S := {s | s ≠ 0}) (a := 0) (b := 1)
      (fun s hs => tableRule_ne_zero_of_rightTap h.1 hs)
      (fun s hs => hs)
      (fun s _ hne hne' =>
        (tableRule_min'_of_leftHold h.2.1 h.2.2.1 h.2.2.2 hne hne').trans (sub_zero _).symm)
      (fun s _ hne hne' => tableRule_max'_of_rightTap h.1 hne hne')
      (by norm_num) (s₀ := Finsupp.single (0 : ℤ) (1 : ZMod 2))
      (fun i heq => single01_ne_zero ((translate_ne_zero_iff i).mp heq)) n
  · exact growingWidth_lightCone_unbounded_of_invariant (S := {s | EndsOneOne s}) (a := 1) (b := 0)
      (fun s hs => endsOneOne_tableRule h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2 hs)
      (fun s hs => endsOneOne_ne_zero hs)
      (fun s _ hne hne' => tableRule_min'_of_leftTap h.1 hne hne')
      (fun s hs hne hne' =>
        (tableRule_max'_of_endsOneOne h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2 hs hne hne').trans
          (add_zero _).symm)
      (by norm_num) (s₀ := endWordSeed)
      (fun i => endsOneOne_translate endWord_seed_endsOneOne) n
  · exact growingWidth_lightCone_unbounded_of_invariant
      (S := {s | StartsOneOne s}) (a := 0) (b := 1)
      (fun s hs => startsOneOne_tableRule h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2 hs)
      (fun s hs => startsOneOne_ne_zero hs)
      (fun s hs hne hne' =>
        (tableRule_min'_of_startsOneOne h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2 hs hne hne').trans
          (sub_zero _).symm)
      (fun s _ hne hne' => tableRule_max'_of_rightTap h.1 hne hne')
      (by norm_num) (s₀ := endWordSeed)
      (fun i => startsOneOne_translate endWord_seed_startsOneOne) n

/-- **The class theorem for `ZeroByEndpoints`**: the light cone's growing width is identically zero
at every quiescent table meeting the class — `48` of the `128` quiescent radius-one tables
(`card_zeroByEndpoints`); the `28`-table middle band between this class and `AccretesByEndpoints`
is not decided here. -/
theorem growingWidth_lightCone_eq_zero_of_zeroByEndpoints
    (f : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2) (hq : f 0 0 0 = 0) (hf : ZeroByEndpoints f)
    (n t : ℕ) : growingWidth (tableRule f hq) diam (lightCone n) t = 0 := by
  rcases hf with h | h | h
  · exact growingWidth_lightCone_eq_zero_of_diam_le (diam_tableRule_le_of_noTap h.1 h.2) n t
  · exact growingWidth_lightCone_eq_zero_of_diam_le
      (diam_tableRule_le_of_leftTap_rightDies h.1 h.2.1 h.2.2.1 h.2.2.2) n t
  · exact growingWidth_lightCone_eq_zero_of_diam_le
      (diam_tableRule_le_of_rightTap_leftDies h.1 h.2.1 h.2.2.1 h.2.2.2) n t

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
-- see card_quiescent.
/-- **The two classes never overlap**. -/
theorem accretesByEndpoints_zeroByEndpoints_disjoint :
    ∀ f : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2, ¬ (AccretesByEndpoints f ∧ ZeroByEndpoints f) := by
  decide

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
-- the ambient type has 256 members; kernel reduction of the nested Pi-Fintype instance needs more
-- than the defaults of both limits.
theorem card_quiescent :
    Fintype.card {f : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2 // f 0 0 0 = 0} = 128 := by decide

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
-- see card_quiescent.
theorem card_accretesByEndpoints :
    Fintype.card {f : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2 // f 0 0 0 = 0 ∧ AccretesByEndpoints f}
      = 52 := by decide

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
-- see card_quiescent.
theorem card_zeroByEndpoints :
    Fintype.card {f : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2 // f 0 0 0 = 0 ∧ ZeroByEndpoints f}
      = 48 := by decide

/-! ### The witness: `f202`, the end-word instance, jointly satisfiable -/

/-- **Table `202`**: `f 0 0 1 = f 0 1 1 = f 1 1 0 = f 1 1 1 = 1`, the other four values `0`. The
Class-E witness — the instance where `S ≠ {s | s ≠ 0}` is genuinely used. -/
def f202 (a b c : ZMod 2) : ZMod 2 := c + a * (b + c)

theorem hq202 : f202 0 0 0 = 0 := by decide

private theorem f202_001 : f202 0 0 1 = 1 := by decide
private theorem f202_100 : f202 1 0 0 = 0 := by decide
private theorem f202_110 : f202 1 1 0 = 1 := by decide
private theorem f202_011 : f202 0 1 1 = 1 := by decide
private theorem f202_111 : f202 1 1 1 = 1 := by decide

/-- **The engine's hypotheses are jointly satisfiable**: `f202` at `S := {s | EndsOneOne s}`,
`(a, b) = (1, 0)`, `s₀ := Finsupp.single 0 1 + Finsupp.single 1 1` meets all six at once, the
instance that shows `S ≠ {s | s ≠ 0}` is used. -/
theorem growingWidth_lightCone_unbounded_of_invariant_nonvacuous :
    ∃ (U : (ℤ →₀ ZMod 2) → (ℤ →₀ ZMod 2)) (S : Set (ℤ →₀ ZMod 2)) (a b : ℤ),
      (∀ s ∈ S, U s ∈ S) ∧ (∀ s ∈ S, s ≠ 0) ∧
      (∀ s ∈ S, ∀ (hne : s.support.Nonempty) (hne' : (U s).support.Nonempty),
        (U s).support.min' hne' = s.support.min' hne - a) ∧
      (∀ s ∈ S, ∀ (hne : s.support.Nonempty) (hne' : (U s).support.Nonempty),
        (U s).support.max' hne' = s.support.max' hne + b) ∧
      1 ≤ a + b ∧
      ∃ s₀ : ℤ →₀ ZMod 2, ∀ i : ℤ, translate i s₀ ∈ S :=
  ⟨tableRule f202 hq202, {s | EndsOneOne s}, 1, 0,
    fun s hs => endsOneOne_tableRule f202_100 f202_110 f202_011 f202_111 hs,
    fun s hs => endsOneOne_ne_zero hs,
    fun s _ hne hne' => tableRule_min'_of_leftTap f202_001 hne hne',
    fun s hs hne hne' =>
      (tableRule_max'_of_endsOneOne f202_100 f202_110 f202_011 f202_111 hs hne hne').trans
        (add_zero _).symm,
    by norm_num,
    endWordSeed,
    fun i => endsOneOne_translate endWord_seed_endsOneOne⟩

/-- **The instantiation at `f202`**. -/
theorem growingWidth_lightCone_unbounded_f202 (n : ℕ) :
    ∀ N : ℕ, ∃ t, (N : ℕ∞) < growingWidth (tableRule f202 hq202) diam (lightCone n) t :=
  growingWidth_lightCone_unbounded_of_invariant (S := {s | EndsOneOne s}) (a := 1) (b := 0)
    (fun s hs => endsOneOne_tableRule f202_100 f202_110 f202_011 f202_111 hs)
    (fun s hs => endsOneOne_ne_zero hs)
    (fun s _ hne hne' => tableRule_min'_of_leftTap f202_001 hne hne')
    (fun s hs hne hne' =>
      (tableRule_max'_of_endsOneOne f202_100 f202_110 f202_011 f202_111 hs hne hne').trans
        (add_zero _).symm)
    (by norm_num) (s₀ := endWordSeed)
    (fun i => endsOneOne_translate endWord_seed_endsOneOne) n

/-! ### The six landed instantiations and the three landed zero statements are instances -/

/-- `rule90`'s own table, `f a b c = a + c`. -/
def f90 (a _b c : ZMod 2) : ZMod 2 := a + c

/-- `rule150`'s own table, `f a b c = a + b + c`. -/
def f150 (a b c : ZMod 2) : ZMod 2 := a + b + c

theorem accretesByEndpoints_f90 : AccretesByEndpoints f90 := by decide
theorem accretesByEndpoints_f150 : AccretesByEndpoints f150 := by decide
theorem accretesByEndpoints_f30 : AccretesByEndpoints f30 := by decide
theorem accretesByEndpoints_f210 : AccretesByEndpoints f210 := by decide
theorem accretesByEndpoints_f86 : AccretesByEndpoints f86 := by decide
theorem accretesByEndpoints_f154 : AccretesByEndpoints f154 := by decide

theorem zeroByEndpoints_f170 : ZeroByEndpoints f170 := by decide
theorem zeroByEndpoints_f240 : ZeroByEndpoints f240 := by decide

end EndpointClasses

/-! ## Axiom audit

Every capstone above is `#print axioms`-clean on the standard triple, and the guards below make
that build-enforced. -/

set_option linter.style.longLine false

/-- info: 'EndpointClasses.linear_le_growingWidth_lightCone_of_invariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EndpointClasses.linear_le_growingWidth_lightCone_of_invariant

/-- info: 'EndpointClasses.growingWidth_lightCone_unbounded_of_invariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EndpointClasses.growingWidth_lightCone_unbounded_of_invariant

/-- info: 'EndpointClasses.growingPart_eq_empty_of_diam_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EndpointClasses.growingPart_eq_empty_of_diam_le

/-- info: 'EndpointClasses.growingWidth_lightCone_eq_zero_of_diam_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EndpointClasses.growingWidth_lightCone_eq_zero_of_diam_le

/-- info: 'EndpointClasses.growingWidth_lightCone_unbounded_of_accretesByEndpoints' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EndpointClasses.growingWidth_lightCone_unbounded_of_accretesByEndpoints

/-- info: 'EndpointClasses.growingWidth_lightCone_eq_zero_of_zeroByEndpoints' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EndpointClasses.growingWidth_lightCone_eq_zero_of_zeroByEndpoints

/-- info: 'EndpointClasses.accretesByEndpoints_zeroByEndpoints_disjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EndpointClasses.accretesByEndpoints_zeroByEndpoints_disjoint

/-- info: 'EndpointClasses.card_quiescent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EndpointClasses.card_quiescent

/-- info: 'EndpointClasses.card_accretesByEndpoints' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EndpointClasses.card_accretesByEndpoints

/-- info: 'EndpointClasses.card_zeroByEndpoints' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EndpointClasses.card_zeroByEndpoints

/-- info: 'EndpointClasses.growingWidth_lightCone_unbounded_of_invariant_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EndpointClasses.growingWidth_lightCone_unbounded_of_invariant_nonvacuous

/-- info: 'EndpointClasses.growingWidth_lightCone_unbounded_f202' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EndpointClasses.growingWidth_lightCone_unbounded_f202
