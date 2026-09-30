/-
Copyright (c) 2026 Mykola Palamarchuk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mykola Palamarchuk
-/
module

public import ALT.ExtremeTapWidth
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Fin
public import Mathlib.Data.Fintype.Pi

-- Formal-check file, not Mathlib-destined: opt out of the house-style header linter.
set_option linter.style.header false

/-!
# The margin a cell's reading allows

Extends [Guests] §3, the paragraph "Robustness margin — survival", where one-step erasure is set
apart from the margin, and [Guests] §4, Law 4, whose packing inequality this localizes. Nothing
here is registered against any paper.

Four conditions are minted here and named for use in every docstring. A function of a state
**reads only** a finite set of cells (`ReadsOnly`). A function **holds within** `e` at a state
when every state differing from it at no more than `e` cells has the same value (`HoldsWithin`).
An update **erases at** `e` a state when every state differing from it at no more than `e` cells
has the same successor (`ErasesAt`, on the finitely-supported line configurations). An update
**erases within** `e` a state under the same reading, over ALL functions of a general index type
(`ErasesWithin`) — the form the full (not finitely-supported) line needs.

None of these four is the margin of `ALT/Persistence/Robustness.lean`, which is stated through
`hammingDist` on a finite carrier; the conditions here are unrelated and apply to an infinite index
type (`ℤ`, or a general `ι`).

## Main results

* `margins_add_lt_card_of_readsOnly` — the localized packing bound: if `g` reads only `N` and holds
  within `e₀`/`e₁` at two states `g` tells apart, the two states differ, inside `N`, at more cells
  than `e₀ + e₁`.
* `margins_add_lt_card_of_readsOnly_nonvacuous` — a fixed instance at which the bound is an
  equality: the majority of three cells, both constant states, margins `1` and `1`, a difference of
  `3`.
* `margins_add_lt_card_guard` — the guard: what `g` reads is load-bearing, at the same majority read
  against a single cell it does not read only, at margins `1, 1`.
* `tableRule_iterate_apply_congr` — the radius-one locality of `ExtremeTapWidth.tableRule`'s
  iterate: two finitely-supported states agreeing on a `2τ + 1`-cell window around a cell give the
  same value there after `τ` steps.
* `ErasesAt` and `tableRule_margins_add_le_two_mul` — `margins_add_lt_card_of_readsOnly` applied
  through `tableRule_iterate_apply_congr`'s locality: the two margins of a radius-one rule's
  `τ`-step iterate, at two states it tells apart, add to at most `2τ`.
* `tableRule_margins_add_le_two_mul_nonvacuous` — a fixed instance: the majority table at one step,
  the zero state against three adjacent set cells, margins `1` and `0`.
* `lineRule` — the same radius-one local rule as `tableRule`, over ALL functions of the line rather
  than the finitely-supported ones.
* `not_erasesWithin_two_const` — a margin of `2` cannot hold at both constant states of a radius-one
  table's iterate at once.
* `majTable` and `erasesWithin_one_const_iff` — a margin of `1` holds at both constant states, at
  every positive scale, exactly when the table is the majority of its three cells.
* `erasesWithin_one_const_majTable` — the right side's own witness: the majority table meets both
  quiescence conditions and its one-step margin is `1` at both constant states.
* `erasesWithin_two_const_zero_guard` — the guard: the second constant state is load-bearing in the
  first result — the conjunction of the three cells erases within `2` at the zero state alone.
* `lineRule_eq_of_erasesWithin_two` — at scale one, two states each erasing within `2` in one step
  have the same successor, at every table, on all functions of the line.
* `lineRule_eq_of_erasesWithin_two_nonvacuous` — a fixed instance: the constant-zero table erases
  within `2` at two different states.
* `lineRule_ne_of_erasesWithin_one_guard` — the guard: at the majority table both constant states
  erase within `1` and their successors differ, so the margin `2` is load-bearing.

## Scope

`ReadsOnly`, `HoldsWithin` and `ErasesWithin` quantify over a general index type `ι` and are stated
with no reference to any particular rule; `ErasesAt` is specialized to the finitely-supported
configurations of the line, matching `tableRule`'s own shape. `HoldsWithin` and `ErasesWithin`
quantify over a finite set of cells that CONTAINS the differing cells and need not equal it, which
is what makes them monotone in the margin without any decidability assumption; `ErasesAt` counts
the support of the difference itself. The witnesses and the guard pair are existential
statements: each names its margins and its count, and the function, the table or the state that
meets them is in the proof and not in the statement. Whether two finitely-supported states told
apart by a radius-one table can both have a positive margin is not stated here.
-/


@[expose] public section

namespace LocalMargin

open ExtremeTapWidth

/-! ## The localized packing bound -/

/-- **Reads only `N`**: `g`'s value is determined by the coordinates in `N` alone. -/
def ReadsOnly {ι V W : Type*} (g : (ι → V) → W) (N : Finset ι) : Prop :=
  ∀ x y : ι → V, (∀ j ∈ N, x j = y j) → g x = g y

/-- **Holds within `e` at `c`**: every state agreeing with `c` outside some set of at most `e`
cells gives `g` the same value as `c` does. -/
def HoldsWithin {ι V W : Type*} (g : (ι → V) → W) (c : ι → V) (e : ℕ) : Prop :=
  ∀ x : ι → V, (∃ D : Finset ι, D.card ≤ e ∧ ∀ j, j ∉ D → x j = c j) → g x = g c

/-- **The localized packing bound.** Route: split a smallest-`e₀ + e₁` witness to the two states'
disagreement (restricted to `N`) into a piece of size at most `e₀` and the rest, of size at most
`e₁`; rewrite each state to the other on its own piece, and the two rewrites agree on all of `N`
(since `N`'s disagreement set is exactly split between the pieces) while each individually holds
within its margin of the state it started from — so `g` reads the same value off both rewrites
through `N`, chaining `g c₀` to `g c₁`. -/
theorem margins_add_lt_card_of_readsOnly {ι V W : Type*} [DecidableEq V]
    (g : (ι → V) → W) (N : Finset ι) (hN : ReadsOnly g N) (c₀ c₁ : ι → V)
    (hne : g c₀ ≠ g c₁) (e₀ e₁ : ℕ)
    (h₀ : HoldsWithin g c₀ e₀) (h₁ : HoldsWithin g c₁ e₁) :
    e₀ + e₁ + 1 ≤ (N.filter fun j => c₀ j ≠ c₁ j).card := by
  classical
  by_contra hcon
  push Not at hcon
  set S : Finset ι := N.filter fun j => c₀ j ≠ c₁ j with hS_def
  have hScard : S.card ≤ e₀ + e₁ := by omega
  obtain ⟨A, hAS, hAcard⟩ := Finset.exists_subset_card_eq (s := S) (n := min e₀ S.card)
    (min_le_right _ _)
  set B : Finset ι := S \ A with hB_def
  have hAcard_le : A.card ≤ e₀ := hAcard ▸ min_le_left _ _
  have hBcard_le : B.card ≤ e₁ := by
    have hcard_eq : B.card = S.card - A.card := by
      rw [hB_def, Finset.card_sdiff, Finset.inter_eq_left.mpr hAS]
    by_cases hle : S.card ≤ e₀
    · rw [min_eq_right hle] at hAcard; omega
    · rw [min_eq_left (not_le.mp hle).le] at hAcard; omega
  set x : ι → V := fun j => if j ∈ A then c₁ j else c₀ j with hx_def
  set y : ι → V := fun j => if j ∈ B then c₀ j else c₁ j with hy_def
  have hgx : g x = g c₀ := h₀ x ⟨A, hAcard_le, fun j hj => by simp [hx_def, hj]⟩
  have hgy : g y = g c₁ := h₁ y ⟨B, hBcard_le, fun j hj => by simp [hy_def, hj]⟩
  have hdisj : Disjoint A B := by rw [hB_def]; exact disjoint_sdiff_self_right
  have hAB : A ∪ B = S := by rw [hB_def]; exact Finset.union_sdiff_of_subset hAS
  have hxy : ∀ j ∈ N, x j = y j := by
    intro j hj
    by_cases hjS : j ∈ S
    · have hjAB : j ∈ A ∪ B := hAB ▸ hjS
      rcases Finset.mem_union.mp hjAB with hjA | hjB
      · have hjB' : j ∉ B := fun h => (Finset.disjoint_left.mp hdisj) hjA h
        simp [hx_def, hy_def, hjA, hjB']
      · have hjA' : j ∉ A := fun h => (Finset.disjoint_left.mp hdisj) h hjB
        simp [hx_def, hy_def, hjA', hjB]
    · have hjA' : j ∉ A := fun h => hjS (hAS h)
      have hjB' : j ∉ B := fun h => hjS (Finset.mem_sdiff.mp h).1
      have heq : c₀ j = c₁ j := by
        by_contra hne'
        exact hjS (Finset.mem_filter.mpr ⟨hj, hne'⟩)
      simp [hx_def, hy_def, hjA', hjB', heq]
  exact hne (hgx ▸ hgy ▸ hN x y hxy)

private def majFin3 : (Fin 3 → Bool) → Bool := fun x => (x 0 && x 1) || (x 1 && x 2) || (x 0 && x 2)

private theorem majFin3_false_of_card_le_one :
    ∀ x : Fin 3 → Bool, (Finset.univ.filter fun j => x j = true).card ≤ 1 → majFin3 x = false := by
  decide

private theorem majFin3_true_of_card_le_one :
    ∀ x : Fin 3 → Bool, (Finset.univ.filter fun j => x j = false).card ≤ 1 → majFin3 x = true := by
  decide

private theorem holdsWithin_majFin3_false_one : HoldsWithin majFin3 (fun _ : Fin 3 => false) 1 := by
  rintro x ⟨D, hD, hx⟩
  have hsub : (Finset.univ.filter fun j => x j = true) ⊆ D := by
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    by_contra hjD
    have h1 : x j = false := hx j hjD
    rw [h1] at hj
    exact absurd hj (by decide)
  exact majFin3_false_of_card_le_one x ((Finset.card_le_card hsub).trans hD)

private theorem holdsWithin_majFin3_true_one : HoldsWithin majFin3 (fun _ : Fin 3 => true) 1 := by
  rintro x ⟨D, hD, hx⟩
  have hsub : (Finset.univ.filter fun j => x j = false) ⊆ D := by
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    by_contra hjD
    have h1 : x j = true := hx j hjD
    rw [h1] at hj
    exact absurd hj (by decide)
  exact majFin3_true_of_card_le_one x ((Finset.card_le_card hsub).trans hD)

/-- The smallest instance meeting `margins_add_lt_card_of_readsOnly`'s four hypotheses at once, at
which the bound is an equality: the majority of three cells, `N` the whole index, both constant
states, margins `1` and `1` — the two states differ at all three cells. -/
theorem margins_add_lt_card_of_readsOnly_nonvacuous :
    ∃ (g : (Fin 3 → Bool) → Bool) (N : Finset (Fin 3)) (c₀ c₁ : Fin 3 → Bool) (e₀ e₁ : ℕ),
      ReadsOnly g N ∧ g c₀ ≠ g c₁ ∧ HoldsWithin g c₀ e₀ ∧ HoldsWithin g c₁ e₁ ∧ e₀ = 1 ∧ e₁ = 1 ∧
        (N.filter fun j => c₀ j ≠ c₁ j).card = 3 := by
  refine ⟨majFin3, Finset.univ, fun _ => false, fun _ => true, 1, 1,
    fun x y h => congrArg majFin3 (funext fun j => h j (Finset.mem_univ j)), by decide,
    holdsWithin_majFin3_false_one, holdsWithin_majFin3_true_one, rfl, rfl, by decide⟩

/-- **Guard**: what the function reads is load-bearing — the same majority, read against a single
cell it does not read only, meets `margins_add_lt_card_of_readsOnly`'s other three hypotheses at
margins `1, 1`, the same margins `margins_add_lt_card_of_readsOnly_nonvacuous` proves, while its
own conclusion fails: the two constant states differ, inside that one cell, at fewer cells than the
margins force. -/
theorem margins_add_lt_card_guard :
    ∃ (g : (Fin 3 → Bool) → Bool) (N : Finset (Fin 3)) (c₀ c₁ : Fin 3 → Bool) (e₀ e₁ : ℕ),
      g c₀ ≠ g c₁ ∧ HoldsWithin g c₀ e₀ ∧ HoldsWithin g c₁ e₁ ∧ e₀ = 1 ∧ e₁ = 1 ∧
        N.card = 1 ∧ ¬ (e₀ + e₁ + 1 ≤ (N.filter fun j => c₀ j ≠ c₁ j).card) := by
  refine ⟨majFin3, {0}, fun _ => false, fun _ => true, 1, 1, by decide,
    holdsWithin_majFin3_false_one, holdsWithin_majFin3_true_one, rfl, rfl, by decide, by decide⟩

/-! ## The radius-one form at a scale -/

theorem tableRule_iterate_apply_congr (f : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2) (hq : f 0 0 0 = 0)
    (τ : ℕ) (i : ℤ) (s s' : ℤ →₀ ZMod 2)
    (h : ∀ j : ℤ, i - (τ : ℤ) ≤ j → j ≤ i + (τ : ℤ) → s j = s' j) :
    ((tableRule f hq)^[τ] s) i = ((tableRule f hq)^[τ] s') i := by
  induction τ generalizing i with
  | zero => simpa using h i (by simp) (by simp)
  | succ k ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    rw [tableRule_apply, tableRule_apply]
    have e1 : ((tableRule f hq)^[k] s) (i - 1) = ((tableRule f hq)^[k] s') (i - 1) :=
      ih (i - 1) (fun j hj1 hj2 => h j (by omega) (by omega))
    have e2 : ((tableRule f hq)^[k] s) i = ((tableRule f hq)^[k] s') i :=
      ih i (fun j hj1 hj2 => h j (by omega) (by omega))
    have e3 : ((tableRule f hq)^[k] s) (i + 1) = ((tableRule f hq)^[k] s') (i + 1) :=
      ih (i + 1) (fun j hj1 hj2 => h j (by omega) (by omega))
    rw [e1, e2, e3]

/-- **Erases at `e` from `c`**: every finitely-supported state within Hamming reach `e` of `c` gives
`U` the same output as `c` does. -/
def ErasesAt (U : (ℤ →₀ ZMod 2) → (ℤ →₀ ZMod 2)) (c : ℤ →₀ ZMod 2) (e : ℕ) : Prop :=
  ∀ d : ℤ →₀ ZMod 2, d.support.card ≤ e → U (c + d) = U c

/-- The radius-one local rule over ALL functions of the line, not only the finitely-supported ones
— the same formula as `ExtremeTapWidth.tableRule`, used here to bridge into
`margins_add_lt_card_of_readsOnly`'s abstract `ReadsOnly`/`HoldsWithin` (stated for a general
Pi-type domain) and, later in this file, to state the margin conditions at the two constant
states, which are not finitely supported. -/
def lineRule (f : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2) : (ℤ → ZMod 2) → (ℤ → ZMod 2) :=
  fun x i => f (x (i - 1)) (x i) (x (i + 1))

private theorem lineRule_iterate_apply_congr (f : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2)
    (τ : ℕ) (i : ℤ) (x x' : ℤ → ZMod 2)
    (h : ∀ j : ℤ, i - (τ : ℤ) ≤ j → j ≤ i + (τ : ℤ) → x j = x' j) :
    (lineRule f)^[τ] x i = (lineRule f)^[τ] x' i := by
  induction τ generalizing i with
  | zero => simpa using h i (by simp) (by simp)
  | succ k ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    change f (_) (_) (_) = f (_) (_) (_)
    have e1 : (lineRule f)^[k] x (i - 1) = (lineRule f)^[k] x' (i - 1) :=
      ih (i - 1) (fun j hj1 hj2 => h j (by omega) (by omega))
    have e2 : (lineRule f)^[k] x i = (lineRule f)^[k] x' i :=
      ih i (fun j hj1 hj2 => h j (by omega) (by omega))
    have e3 : (lineRule f)^[k] x (i + 1) = (lineRule f)^[k] x' (i + 1) :=
      ih (i + 1) (fun j hj1 hj2 => h j (by omega) (by omega))
    rw [e1, e2, e3]

private theorem coe_tableRule_iterate (f : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2) (hq : f 0 0 0 = 0)
    (τ : ℕ) (s : ℤ →₀ ZMod 2) :
    (⇑((tableRule f hq)^[τ] s) : ℤ → ZMod 2) = (lineRule f)^[τ] (⇑s) := by
  induction τ with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    funext i
    rw [tableRule_apply]
    rw [show (((tableRule f hq)^[k] s) (i-1)) = (lineRule f)^[k] (⇑s) (i-1) from congrFun ih (i-1),
      show (((tableRule f hq)^[k] s) i) = (lineRule f)^[k] (⇑s) i from congrFun ih i,
      show (((tableRule f hq)^[k] s) (i+1)) = (lineRule f)^[k] (⇑s) (i+1) from congrFun ih (i+1)]
    rfl

/-- **The two margins add to at most twice the scale.** `margins_add_lt_card_of_readsOnly` applied
at a cell the two `τ`-step iterates disagree on, its `2τ + 1`-cell window as `N`, and `g` the
window's own `τ`-step value, bridged from the finitely-supported states through
`lineRule`/`coe_tableRule_iterate` (any window-agreeing GENERAL function of the line is exhibited as
a finitely-supported rewrite of one of the two states, via `Finsupp.onFinset`, to invoke
`ErasesAt`). -/
theorem tableRule_margins_add_le_two_mul (f : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2)
    (hq : f 0 0 0 = 0) (τ : ℕ) (c₀ c₁ : ℤ →₀ ZMod 2)
    (hne : (tableRule f hq)^[τ] c₀ ≠ (tableRule f hq)^[τ] c₁) (e₀ e₁ : ℕ)
    (h₀ : ErasesAt ((tableRule f hq)^[τ]) c₀ e₀) (h₁ : ErasesAt ((tableRule f hq)^[τ]) c₁ e₁) :
    e₀ + e₁ ≤ 2 * τ := by
  classical
  obtain ⟨i, hi⟩ : ∃ i : ℤ, (tableRule f hq)^[τ] c₀ i ≠ (tableRule f hq)^[τ] c₁ i := by
    by_contra hall
    push Not at hall
    exact hne (DFunLike.ext _ _ hall)
  set N : Finset ℤ := Finset.Icc (i - (τ : ℤ)) (i + (τ : ℤ)) with hN_def
  have hNcard : N.card = 2 * τ + 1 := by
    rw [hN_def, Int.card_Icc]
    have heq : (i + (τ : ℤ) + 1 - (i - (τ : ℤ))) = 2 * (τ : ℤ) + 1 := by ring
    rw [heq]; omega
  set g : (ℤ → ZMod 2) → ZMod 2 := fun x => (lineRule f)^[τ] x i with hg_def
  have hReads : ReadsOnly g N := fun x y hxy =>
    lineRule_iterate_apply_congr f τ i x y
      (fun j hj1 hj2 => hxy j (by rw [hN_def, Finset.mem_Icc]; exact ⟨hj1, hj2⟩))
  have hgc : ∀ s : ℤ →₀ ZMod 2, g (⇑s) = (tableRule f hq)^[τ] s i := fun s => by
    rw [hg_def]; change (lineRule f)^[τ] (⇑s) i = _
    rw [← coe_tableRule_iterate f hq τ s]
  have hne' : g (⇑c₀) ≠ g (⇑c₁) := by rw [hgc, hgc]; exact hi
  have hHolds : ∀ (c : ℤ →₀ ZMod 2) (e : ℕ), ErasesAt ((tableRule f hq)^[τ]) c e →
      HoldsWithin g (⇑c) e := by
    intro c e hE x ⟨D, hD, hx⟩
    have hsupp : ∀ j, x j ≠ 0 → j ∈ D ∪ c.support := by
      intro j hj
      by_cases hjD : j ∈ D
      · exact Finset.mem_union_left _ hjD
      · refine Finset.mem_union_right _ (Finsupp.mem_support_iff.mpr ?_)
        rw [← hx j hjD]; exact hj
    set x' : ℤ →₀ ZMod 2 := Finsupp.onFinset (D ∪ c.support) x hsupp with hx'_def
    have hx'_apply : ∀ j, x' j = x j := fun j => Finsupp.onFinset_apply
    set d : ℤ →₀ ZMod 2 := x' - c with hd_def
    have hd_supp : d.support ⊆ D := by
      intro j hj
      by_contra hjD
      have hz : d j = 0 := by
        rw [hd_def, Finsupp.sub_apply, hx'_apply, hx j hjD, sub_self]
      exact (Finsupp.mem_support_iff.mp hj) hz
    have hd_card : d.support.card ≤ e := (Finset.card_le_card hd_supp).trans hD
    have hx'_eq : x' = c + d := by rw [hd_def]; abel
    have hUx' : (tableRule f hq)^[τ] x' = (tableRule f hq)^[τ] c := by
      rw [hx'_eq]; exact hE d hd_card
    have hxeq : x = (⇑x' : ℤ → ZMod 2) := funext fun j => (hx'_apply j).symm
    change g x = g (⇑c)
    rw [hxeq, hgc, hgc, hUx']
  have h₀' : HoldsWithin g (⇑c₀) e₀ := hHolds c₀ e₀ h₀
  have h₁' : HoldsWithin g (⇑c₁) e₁ := hHolds c₁ e₁ h₁
  have hfinal := margins_add_lt_card_of_readsOnly g N hReads (⇑c₀) (⇑c₁) hne' e₀ e₁ h₀' h₁'
  have hfilter_le : (N.filter fun j => (⇑c₀ : ℤ → ZMod 2) j ≠ (⇑c₁ : ℤ → ZMod 2) j).card ≤ N.card :=
    Finset.card_filter_le _ _
  omega

/-- The majority of three cells, the shared table for the rest of this file (`[Guests] §4`'s Law
4's rule family includes it; the elementary-table number is `232`). -/
def majTable (a b c : ZMod 2) : ZMod 2 := a * b + b * c + a * c

private theorem erasesAt_zero (U : (ℤ →₀ ZMod 2) → (ℤ →₀ ZMod 2)) (c : ℤ →₀ ZMod 2) :
    ErasesAt U c 0 := by
  intro d hd
  have hd0 : d = 0 := Finsupp.support_eq_empty.mp (Finset.card_eq_zero.mp (Nat.le_zero.mp hd))
  rw [hd0, add_zero]

private theorem tableRule_majTable_single (p : ℤ) :
    tableRule majTable (by decide : majTable 0 0 0 = 0) (Finsupp.single p (1 : ZMod 2)) = 0 := by
  ext i
  rw [tableRule_apply]
  simp only [Finsupp.coe_zero, Pi.zero_apply]
  by_cases h1 : i - 1 = p <;> by_cases h2 : i = p <;> by_cases h3 : i + 1 = p <;>
    simp_all [majTable]
  all_goals omega

private theorem zmod2_eq_one_of_ne_zero : ∀ a : ZMod 2, a ≠ 0 → a = 1 := by decide

private theorem tableRule_majTable_zero_eq :
    tableRule majTable (by decide : majTable 0 0 0 = 0) (0 : ℤ →₀ ZMod 2) = 0 := by
  ext i
  rw [tableRule_apply]
  simpa using (by decide : majTable 0 0 0 = 0)

private theorem erasesAt_zero_one :
    ErasesAt (tableRule majTable (by decide : majTable 0 0 0 = 0)) (0 : ℤ →₀ ZMod 2) 1 := by
  intro d hd
  rw [zero_add]
  by_cases hd0 : d = 0
  · rw [hd0]
  · have hne : d.support.Nonempty := Finsupp.support_nonempty_iff.mpr hd0
    have hcard1 : d.support.card = 1 := le_antisymm hd (Finset.card_pos.mpr hne)
    obtain ⟨p, hp⟩ := Finset.card_eq_one.mp hcard1
    obtain ⟨hdp, hd_eq⟩ := Finsupp.support_eq_singleton.mp hp
    rw [hd_eq, zmod2_eq_one_of_ne_zero _ hdp]
    exact (tableRule_majTable_single p).trans tableRule_majTable_zero_eq.symm

private noncomputable def threeAdjacent : ℤ →₀ ZMod 2 :=
  Finsupp.single (-1 : ℤ) 1 + Finsupp.single (0 : ℤ) 1 + Finsupp.single (1 : ℤ) 1

/-- The smallest instance meeting `tableRule_margins_add_le_two_mul`'s three hypotheses at once:
the majority table at scale `1`, the zero state against a state with three adjacent cells set,
margins `1` and `0`. The statement names the table, the zero state and the two margins, and
leaves the second state existential. -/
theorem tableRule_margins_add_le_two_mul_nonvacuous :
    ∃ (hq : majTable 0 0 0 = 0) (c₁ : ℤ →₀ ZMod 2),
      (tableRule majTable hq)^[1] (0 : ℤ →₀ ZMod 2) ≠ (tableRule majTable hq)^[1] c₁ ∧
        ErasesAt ((tableRule majTable hq)^[1]) (0 : ℤ →₀ ZMod 2) 1 ∧
        ErasesAt ((tableRule majTable hq)^[1]) c₁ 0 := by
  refine ⟨by decide, threeAdjacent, ?_, ?_, erasesAt_zero _ _⟩
  · have hqz : majTable 0 0 0 = 0 := by decide
    have hL : (tableRule majTable hqz)^[1] (0 : ℤ →₀ ZMod 2) 0 = 0 := by
      rw [Function.iterate_one, tableRule_apply]
      simp [majTable]
    have hR : (tableRule majTable hqz)^[1] threeAdjacent 0 = 1 := by
      have e1 : threeAdjacent ((0 : ℤ) - 1) = 1 := by simp [threeAdjacent]
      have e2 : threeAdjacent (0 : ℤ) = 1 := by simp [threeAdjacent]
      have e3 : threeAdjacent ((0 : ℤ) + 1) = 1 := by simp [threeAdjacent]
      rw [Function.iterate_one, tableRule_apply, e1, e2, e3]
      decide
    intro hcon
    have hcontra := DFunLike.congr_fun hcon (0 : ℤ)
    rw [hL, hR] at hcontra
    exact absurd hcontra (by decide)
  · simpa only [Function.iterate_one] using erasesAt_zero_one

/-! ## The two constant states of a radius-one table -/

private theorem lineRule_apply (f : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2) (x : ℤ → ZMod 2) (i : ℤ) :
    lineRule f x i = f (x (i - 1)) (x i) (x (i + 1)) := rfl

/-- **Erases within `e` at `c`**: the same condition as `ErasesAt`, over ALL functions of a general
index type — the form the two constant states need, since they are not finitely supported. -/
def ErasesWithin {ι V : Type*} (U : (ι → V) → (ι → V)) (c : ι → V) (e : ℕ) : Prop :=
  ∀ x : ι → V, (∃ D : Finset ι, D.card ≤ e ∧ ∀ j, j ∉ D → x j = c j) → U x = U c

private theorem movingRight_persists (f : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2) (bg defect : ZMod 2)
    (hbg_fixed : f bg bg bg = bg) (hstep : f defect bg bg = defect) :
    ∀ (p : ℤ) (x : ℤ → ZMod 2), x p = defect → (∀ j, p < j → x j = bg) →
      ∀ k : ℕ, (lineRule f)^[k] x (p + k) = defect ∧
        ∀ j, p + (k : ℤ) < j → (lineRule f)^[k] x j = bg := by
  intro p x hp hright k
  induction k with
  | zero => simpa using ⟨hp, hright⟩
  | succ n ih =>
    obtain ⟨ihp, ihright⟩ := ih
    rw [Function.iterate_succ_apply']
    set y := (lineRule f)^[n] x with hy_def
    constructor
    · rw [lineRule_apply]
      have e1 : p + ((n + 1 : ℕ) : ℤ) - 1 = p + (n : ℤ) := by omega
      have e2 : p + (n : ℤ) < p + ((n + 1 : ℕ) : ℤ) := by omega
      have e3 : p + (n : ℤ) < p + ((n + 1 : ℕ) : ℤ) + 1 := by omega
      rw [e1, ihp, ihright _ e2, ihright _ e3]
      exact hstep
    · intro j hj
      rw [lineRule_apply]
      have hj' : p + (n : ℤ) < j := by omega
      rw [ihright (j - 1) (by omega), ihright j (by omega), ihright (j + 1) (by omega)]
      exact hbg_fixed

private theorem movingLeft_persists (f : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2) (bg defect : ZMod 2)
    (hbg_fixed : f bg bg bg = bg) (hstep : f bg bg defect = defect) :
    ∀ (p : ℤ) (x : ℤ → ZMod 2), x p = defect → (∀ j, j < p → x j = bg) →
      ∀ k : ℕ, (lineRule f)^[k] x (p - k) = defect ∧
        ∀ j, j < p - (k : ℤ) → (lineRule f)^[k] x j = bg := by
  intro p x hp hleft k
  induction k with
  | zero => simpa using ⟨hp, hleft⟩
  | succ n ih =>
    obtain ⟨ihp, ihleft⟩ := ih
    rw [Function.iterate_succ_apply']
    set y := (lineRule f)^[n] x with hy_def
    constructor
    · rw [lineRule_apply]
      have e1 : p - ((n + 1 : ℕ) : ℤ) + 1 = p - (n : ℤ) := by omega
      have e2 : p - ((n + 1 : ℕ) : ℤ) - 1 < p - (n : ℤ) := by omega
      have e3 : p - ((n + 1 : ℕ) : ℤ) < p - (n : ℤ) := by omega
      rw [e1, ihp, ihleft _ e2, ihleft _ e3]
      exact hstep
    · intro j hj
      rw [lineRule_apply]
      have hj' : j < p - (n : ℤ) := by omega
      rw [ihleft (j - 1) (by omega), ihleft j (by omega), ihleft (j + 1) (by omega)]
      exact hbg_fixed

private theorem stationary_persists (f : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2) (bg defect : ZMod 2)
    (hbg_fixed : f bg bg bg = bg) (hmoveR : f defect bg bg = bg) (hmoveL : f bg bg defect = bg)
    (hstep : f bg defect bg = defect) :
    ∀ (p : ℤ) (x : ℤ → ZMod 2), x p = defect → (∀ j, j ≠ p → x j = bg) →
      ∀ k : ℕ, (lineRule f)^[k] x p = defect ∧ ∀ j, j ≠ p → (lineRule f)^[k] x j = bg := by
  intro p x hp hout k
  induction k with
  | zero => simpa using ⟨hp, hout⟩
  | succ n ih =>
    obtain ⟨ihp, ihout⟩ := ih
    rw [Function.iterate_succ_apply']
    set y := (lineRule f)^[n] x with hy_def
    constructor
    · rw [lineRule_apply]
      rw [ihout (p - 1) (by omega), ihp, ihout (p + 1) (by omega)]
      exact hstep
    · intro j hj
      rw [lineRule_apply]
      rcases eq_or_ne (j - 1) p with h1 | h1
      · have hj2 : j ≠ p := hj
        have hj2' : j + 1 ≠ p := by omega
        rw [h1, ihp, ihout j hj2, ihout (j + 1) hj2']
        exact hmoveR
      · rcases eq_or_ne j p with h2 | h2
        · exact absurd h2 hj
        · rcases eq_or_ne (j + 1) p with h3 | h3
          · have hj1 : j - 1 ≠ p := by omega
            rw [ihout (j - 1) hj1, ihout j h2, h3, ihp]
            exact hmoveL
          · rw [ihout (j - 1) h1, ihout j h2, ihout (j + 1) h3]
            exact hbg_fixed

private theorem majTable_eq_bg_of_two_agree :
    ∀ a b c bg : ZMod 2,
      ((a = bg ∧ b = bg) ∨ (b = bg ∧ c = bg) ∨ (a = bg ∧ c = bg)) → majTable a b c = bg := by
  decide

private theorem erasesWithin_lineRule_majTable_one (bg : ZMod 2) (hbg : majTable bg bg bg = bg) :
    ErasesWithin (lineRule majTable) (fun _ : ℤ => bg) 1 := by
  rintro x ⟨D, hD, hx⟩
  funext i
  change majTable (x (i - 1)) (x i) (x (i + 1)) = majTable bg bg bg
  rw [hbg]
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hD with hD0 | hD1
  · have hDe : D = ∅ := Finset.card_eq_zero.mp hD0
    have hall : ∀ j, x j = bg := fun j => hx j (by simp [hDe])
    rw [hall, hall, hall]
    exact hbg
  · obtain ⟨q, hDq⟩ := Finset.card_eq_one.mp hD1
    have hxq : ∀ j, j ≠ q → x j = bg := fun j hj => hx j (by simp [hDq, hj])
    by_cases h1 : i - 1 = q
    · have h2 : x i = bg := hxq i (by omega)
      have h3 : x (i + 1) = bg := hxq (i + 1) (by omega)
      exact majTable_eq_bg_of_two_agree _ _ _ _ (Or.inr (Or.inl ⟨h2, h3⟩))
    · by_cases h2 : i = q
      · have h1' : x (i - 1) = bg := hxq (i - 1) (by omega)
        have h3' : x (i + 1) = bg := hxq (i + 1) (by omega)
        exact majTable_eq_bg_of_two_agree _ _ _ _ (Or.inr (Or.inr ⟨h1', h3'⟩))
      · by_cases h3 : i + 1 = q
        · have h1' : x (i - 1) = bg := hxq (i - 1) (by omega)
          have h2' : x i = bg := hxq i (by omega)
          exact majTable_eq_bg_of_two_agree _ _ _ _ (Or.inl ⟨h1', h2'⟩)
        · have h1' : x (i - 1) = bg := hxq (i - 1) h1
          have h2' : x i = bg := hxq i h2
          exact majTable_eq_bg_of_two_agree _ _ _ _ (Or.inl ⟨h1', h2'⟩)

private theorem lineRule_const_fixed (f : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2) (bg : ZMod 2)
    (hbg : f bg bg bg = bg) : lineRule f (fun _ : ℤ => bg) = fun _ => bg := by
  funext i
  rw [lineRule_apply]
  exact hbg

private theorem lineRule_iterate_const_fixed (f : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2) (bg : ZMod 2)
    (hbg : f bg bg bg = bg) (τ : ℕ) : (lineRule f)^[τ] (fun _ : ℤ => bg) = fun _ => bg :=
  (Function.IsFixedPt.iterate (lineRule_const_fixed f bg hbg) τ : _)

private theorem erasesWithin_iterate_of_erasesWithin_one (f : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2)
    (bg : ZMod 2) (hbg : f bg bg bg = bg) (e : ℕ)
    (hone : ErasesWithin (lineRule f) (fun _ : ℤ => bg) e) {τ : ℕ} (hτ : 0 < τ) :
    ErasesWithin ((lineRule f)^[τ]) (fun _ : ℤ => bg) e := by
  obtain ⟨τ', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hτ.ne'
  intro x hx
  have h1 : (lineRule f)^[τ' + 1] x = (lineRule f)^[τ'] (lineRule f x) :=
    Function.iterate_succ_apply _ _ _
  have h2 : lineRule f x = fun _ : ℤ => bg := (hone x hx).trans (lineRule_const_fixed f bg hbg)
  have h3 : (lineRule f)^[τ'] (fun _ : ℤ => bg) = fun _ => bg :=
    lineRule_iterate_const_fixed f bg hbg τ'
  have h4 : (lineRule f)^[τ' + 1] (fun _ : ℤ => bg) = fun _ => bg :=
    lineRule_iterate_const_fixed f bg hbg (τ' + 1)
  rw [h1, h2, h3, h4]

private theorem false_of_erasesWithin_movingRight (f : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2)
    (bg defect : ZMod 2) (hbg_fixed : f bg bg bg = bg) (hstep : f defect bg bg = defect)
    (hdiff : defect ≠ bg) {τ : ℕ}
    (hEW : ErasesWithin ((lineRule f)^[τ]) (fun _ : ℤ => bg) 1) : False := by
  set x : ℤ → ZMod 2 := fun j => if j = 0 then defect else bg with hx_def
  have hxp : x 0 = defect := by simp [hx_def]
  have hxright : ∀ j : ℤ, 0 < j → x j = bg := fun j hj => by
    simp only [hx_def]; rw [ite_eq_right (by omega)]
  obtain ⟨hpos, -⟩ := movingRight_persists f bg defect hbg_fixed hstep 0 x hxp hxright τ
  have hD : ∃ D : Finset ℤ, D.card ≤ 1 ∧ ∀ j, j ∉ D → x j = bg :=
    ⟨{0}, by simp, fun j hj => by
      simp only [hx_def]; rw [ite_eq_right]; simpa using hj⟩
  have heq := hEW x hD
  rw [lineRule_iterate_const_fixed f bg hbg_fixed τ] at heq
  have hev := congrFun heq ((0 : ℤ) + τ)
  rw [hpos] at hev
  exact hdiff hev

private theorem false_of_erasesWithin_movingLeft (f : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2)
    (bg defect : ZMod 2) (hbg_fixed : f bg bg bg = bg) (hstep : f bg bg defect = defect)
    (hdiff : defect ≠ bg) {τ : ℕ}
    (hEW : ErasesWithin ((lineRule f)^[τ]) (fun _ : ℤ => bg) 1) : False := by
  set x : ℤ → ZMod 2 := fun j => if j = 0 then defect else bg with hx_def
  have hxp : x 0 = defect := by simp [hx_def]
  have hxleft : ∀ j : ℤ, j < 0 → x j = bg := fun j hj => by
    simp only [hx_def]; rw [ite_eq_right (by omega)]
  obtain ⟨hpos, -⟩ := movingLeft_persists f bg defect hbg_fixed hstep 0 x hxp hxleft τ
  have hD : ∃ D : Finset ℤ, D.card ≤ 1 ∧ ∀ j, j ∉ D → x j = bg :=
    ⟨{0}, by simp, fun j hj => by
      simp only [hx_def]; rw [ite_eq_right]; simpa using hj⟩
  have heq := hEW x hD
  rw [lineRule_iterate_const_fixed f bg hbg_fixed τ] at heq
  have hev := congrFun heq ((0 : ℤ) - τ)
  rw [hpos] at hev
  exact hdiff hev

private theorem false_of_erasesWithin_stationary (f : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2)
    (bg defect : ZMod 2) (hbg_fixed : f bg bg bg = bg) (hmoveR : f defect bg bg = bg)
    (hmoveL : f bg bg defect = bg) (hstep : f bg defect bg = defect) (hdiff : defect ≠ bg)
    {τ : ℕ} (hEW : ErasesWithin ((lineRule f)^[τ]) (fun _ : ℤ => bg) 1) : False := by
  set x : ℤ → ZMod 2 := fun j => if j = 0 then defect else bg with hx_def
  have hxp : x 0 = defect := by simp [hx_def]
  have hxout : ∀ j : ℤ, j ≠ 0 → x j = bg := fun j hj => by simp [hx_def, hj]
  obtain ⟨hpos, -⟩ := stationary_persists f bg defect hbg_fixed hmoveR hmoveL hstep 0 x hxp hxout τ
  have hD : ∃ D : Finset ℤ, D.card ≤ 1 ∧ ∀ j, j ∉ D → x j = bg :=
    ⟨{0}, by simp, fun j hj => hxout j (by simpa using hj)⟩
  have heq := hEW x hD
  rw [lineRule_iterate_const_fixed f bg hbg_fixed τ] at heq
  have hev := congrFun heq (0 : ℤ)
  rw [hpos] at hev
  exact hdiff hev

private theorem zmod2_ne_one_iff_eq_zero : ∀ a : ZMod 2, a ≠ 1 → a = 0 := by decide
private theorem zmod2_ne_zero_iff_eq_one : ∀ a : ZMod 2, a ≠ 0 → a = 1 := by decide
private theorem zmod2_eq_zero_or_one : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide

/-- **The forward direction, in full.** Six boundary bits are pinned by contrapositive: a "bad"
value at any one of them would make a single- or two-cell perturbation of a constant state persist
forever under the table's own iterate (moving in one direction, or fixed in place), contradicting
the margin-`1` hypothesis at whichever constant state the perturbation sits in — `f 0 1 1`/`f 1 1 0`
(a lone zero among ones, moving right/left), `f 0 0 1`/`f 1 0 0` (a lone one among zeros, moving
left/right), and, once those four are pinned, `f 0 1 0`/`f 1 0 1` (a lone one/zero held fixed in
place). All six forced values, together with the two quiescence hypotheses, match `majTable`'s own
table at all eight triples. -/
private theorem eq_majTable_of_erasesWithin_one (f : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2)
    (h0 : f 0 0 0 = 0) (h1 : f 1 1 1 = 1) {τ : ℕ}
    (hE0 : ErasesWithin ((lineRule f)^[τ]) (fun _ : ℤ => 0) 1)
    (hE1 : ErasesWithin ((lineRule f)^[τ]) (fun _ : ℤ => 1) 1) :
    f = majTable := by
  have h011 : f 0 1 1 = 1 := by
    by_contra hc
    exact false_of_erasesWithin_movingRight f 1 0 h1 (zmod2_ne_one_iff_eq_zero _ hc) (by decide) hE1
  have h110 : f 1 1 0 = 1 := by
    by_contra hc
    exact false_of_erasesWithin_movingLeft f 1 0 h1 (zmod2_ne_one_iff_eq_zero _ hc) (by decide) hE1
  have h001 : f 0 0 1 = 0 := by
    by_contra hc
    exact false_of_erasesWithin_movingLeft f 0 1 h0 (zmod2_ne_zero_iff_eq_one _ hc) (by decide) hE0
  have h100 : f 1 0 0 = 0 := by
    by_contra hc
    exact false_of_erasesWithin_movingRight f 0 1 h0 (zmod2_ne_zero_iff_eq_one _ hc) (by decide) hE0
  have h010 : f 0 1 0 = 0 := by
    by_contra hc
    exact false_of_erasesWithin_stationary f 0 1 h0 h100 h001
      (zmod2_ne_zero_iff_eq_one _ hc) (by decide) hE0
  have h101 : f 1 0 1 = 1 := by
    by_contra hc
    exact false_of_erasesWithin_stationary f 1 0 h1 h011 h110
      (zmod2_ne_one_iff_eq_zero _ hc) (by decide) hE1
  funext a b c
  rcases zmod2_eq_zero_or_one a with rfl | rfl <;>
    rcases zmod2_eq_zero_or_one b with rfl | rfl <;>
    rcases zmod2_eq_zero_or_one c with rfl | rfl
  · exact h0.trans (by decide)
  · exact h001.trans (by decide)
  · exact h010.trans (by decide)
  · exact h011.trans (by decide)
  · exact h100.trans (by decide)
  · exact h101.trans (by decide)
  · exact h110.trans (by decide)
  · exact h1.trans (by decide)

private def twoBlock : ℤ → ZMod 2 := fun j => if j = 0 ∨ j = 1 then 1 else 0

private theorem majTable_twoBlock_fixed : lineRule majTable twoBlock = twoBlock := by
  funext i
  rw [lineRule_apply]
  by_cases h1 : i = 0
  · subst h1; decide
  by_cases h2 : i = 1
  · subst h2; decide
  by_cases h3 : i = -1
  · subst h3; decide
  by_cases h4 : i = 2
  · subst h4; decide
  · have e1 : ¬(i - 1 = 0 ∨ i - 1 = 1) := by omega
    have e2 : ¬(i = 0 ∨ i = 1) := by omega
    have e3 : ¬(i + 1 = 0 ∨ i + 1 = 1) := by omega
    simp only [twoBlock, ite_eq_right e1, ite_eq_right e2, ite_eq_right e3, majTable]
    decide

/-- **A margin of `2` cannot hold at both constant states.** Downward closure reduces margin `2` to
margin `1` at both, pinning `f = majTable` by `eq_majTable_of_erasesWithin_one`; two adjacent set
cells among zeros are then a genuine FIXED POINT of `majTable`'s rule (`majTable_twoBlock_fixed`),
never returning to the all-zero state, which a margin of `2` at the zero state would require. -/
theorem not_erasesWithin_two_const (f : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2)
    (h0 : f 0 0 0 = 0) (h1 : f 1 1 1 = 1) (τ : ℕ) :
    ¬ (ErasesWithin ((lineRule f)^[τ]) (fun _ : ℤ => 0) 2 ∧
       ErasesWithin ((lineRule f)^[τ]) (fun _ : ℤ => 1) 2) := by
  rintro ⟨hE0, hE1⟩
  have hE0' : ErasesWithin ((lineRule f)^[τ]) (fun _ : ℤ => 0) 1 :=
    fun x hx => hE0 x (hx.imp fun D hD => ⟨by omega, hD.2⟩)
  have hE1' : ErasesWithin ((lineRule f)^[τ]) (fun _ : ℤ => 1) 1 :=
    fun x hx => hE1 x (hx.imp fun D hD => ⟨by omega, hD.2⟩)
  have hf : f = majTable := eq_majTable_of_erasesWithin_one f h0 h1 hE0' hE1'
  subst hf
  have hfix : (lineRule majTable)^[τ] twoBlock = twoBlock :=
    Function.IsFixedPt.iterate majTable_twoBlock_fixed τ
  have hD : ∃ D : Finset ℤ, D.card ≤ 2 ∧ ∀ j, j ∉ D → twoBlock j = 0 := by
    refine ⟨{0, 1}, by decide, fun j hj => ?_⟩
    simp only [twoBlock]
    rw [ite_eq_right (by simpa using hj)]
  have heq := hE0 twoBlock hD
  rw [hfix, lineRule_iterate_const_fixed majTable 0 (by decide) τ] at heq
  have hcontra := congrFun heq (0 : ℤ)
  simp only [twoBlock] at hcontra
  exact absurd hcontra (by decide)

/-- **A margin of `1` at both constant states, at a positive scale, holds exactly for the
majority.** The forward direction is `eq_majTable_of_erasesWithin_one`; the converse is one step of
the majority (`erasesWithin_lineRule_majTable_one`, since a single mismatch among three cells never
overturns a majority vote), promoted to every positive scale by
`erasesWithin_iterate_of_erasesWithin_one` since both constant states are themselves fixed under the
majority rule. -/
theorem erasesWithin_one_const_iff (f : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2)
    (h0 : f 0 0 0 = 0) (h1 : f 1 1 1 = 1) {τ : ℕ} (hτ : 0 < τ) :
    (ErasesWithin ((lineRule f)^[τ]) (fun _ : ℤ => 0) 1 ∧
       ErasesWithin ((lineRule f)^[τ]) (fun _ : ℤ => 1) 1) ↔ f = majTable := by
  constructor
  · rintro ⟨hE0, hE1⟩
    exact eq_majTable_of_erasesWithin_one f h0 h1 hE0 hE1
  · rintro rfl
    refine ⟨?_, ?_⟩
    · exact erasesWithin_iterate_of_erasesWithin_one majTable 0 (by decide) 1
        (erasesWithin_lineRule_majTable_one 0 (by decide)) hτ
    · exact erasesWithin_iterate_of_erasesWithin_one majTable 1 (by decide) 1
        (erasesWithin_lineRule_majTable_one 1 (by decide)) hτ

private def f128 : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2 := fun a b c => a * b * c

private theorem f128_eq_zero_or_all_one :
    ∀ a b c : ZMod 2, f128 a b c ≠ 0 → a = 1 ∧ b = 1 ∧ c = 1 := by decide

/-- **Guard**: the second constant state is load-bearing in `not_erasesWithin_two_const` — the
conjunction of the three cells fixes both constant states and erases within `2` at the zero state
ALONE (three cells set among zeros are needed to output a `1` anywhere, and a perturbation within
`2` can set at most two). The statement is existential in the table and the scale. -/
theorem erasesWithin_two_const_zero_guard :
    ∃ (f : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2) (τ : ℕ), f 0 0 0 = 0 ∧ f 1 1 1 = 1 ∧
      ErasesWithin ((lineRule f)^[τ]) (fun _ : ℤ => 0) 2 := by
  refine ⟨f128, 1, by decide, by decide, ?_⟩
  rw [Function.iterate_one]
  rintro x ⟨D, hD, hx⟩
  funext i
  rw [lineRule_apply]
  by_contra hc
  obtain ⟨ha, hb, hc'⟩ := f128_eq_zero_or_all_one _ _ _ hc
  have hmem1 : i - 1 ∈ D := by
    by_contra h
    have h0' : x (i - 1) = 0 := hx (i - 1) h
    exact absurd (ha ▸ h0') (by decide)
  have hmem2 : i ∈ D := by
    by_contra h
    have h0' : x i = 0 := hx i h
    exact absurd (hb ▸ h0') (by decide)
  have hmem3 : i + 1 ∈ D := by
    by_contra h
    have h0' : x (i + 1) = 0 := hx (i + 1) h
    exact absurd (hc' ▸ h0') (by decide)
  have hsub : ({i - 1, i, i + 1} : Finset ℤ) ⊆ D := by
    intro j hj
    simp only [Finset.mem_insert, Finset.mem_singleton] at hj
    rcases hj with rfl | rfl | rfl
    · exact hmem1
    · exact hmem2
    · exact hmem3
  have h3 : ({i - 1, i, i + 1} : Finset ℤ).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp; omega),
      Finset.card_insert_of_notMem (by simp), Finset.card_singleton]
  have hle := Finset.card_le_card hsub
  omega

/-- The right side's own witness for `erasesWithin_one_const_iff`: the majority table meets both
quiescence conditions, and its one-step margin is `1` at both constant states. -/
theorem erasesWithin_one_const_majTable :
    majTable 0 0 0 = 0 ∧ majTable 1 1 1 = 1 ∧
      ErasesWithin ((lineRule majTable)^[1]) (fun _ : ℤ => 0) 1 ∧
      ErasesWithin ((lineRule majTable)^[1]) (fun _ : ℤ => 1) 1 := by
  refine ⟨by decide, by decide, ?_, ?_⟩
  · simpa only [Function.iterate_one] using erasesWithin_lineRule_majTable_one 0 (by decide)
  · simpa only [Function.iterate_one] using erasesWithin_lineRule_majTable_one 1 (by decide)

/-! ## Two states erasing within `2` at scale one -/

private theorem agree_of_erasesWithin_two (f : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2)
    (x : ℤ → ZMod 2) (hx : ErasesWithin (lineRule f) x 2) (i : ℤ) (a b c : ZMod 2)
    (h : a = x (i - 1) ∨ b = x i ∨ c = x (i + 1)) :
    f a b c = f (x (i - 1)) (x i) (x (i + 1)) := by
  rcases h with rfl | rfl | rfl
  · have := congrFun (hx (fun j => if j = i then b else if j = i + 1 then c else x j)
      ⟨{i, i + 1}, Finset.card_le_two, fun j hj => by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hj
        simp [hj.1, hj.2]⟩) i
    simpa [lineRule_apply, show i - 1 ≠ i by omega, show i - 1 ≠ i + 1 by omega,
      show i ≠ i + 1 by omega] using this
  · have := congrFun (hx (fun j => if j = i - 1 then a else if j = i + 1 then c else x j)
      ⟨{i - 1, i + 1}, Finset.card_le_two, fun j hj => by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hj
        simp [hj.1, hj.2]⟩) i
    simpa [lineRule_apply, show i ≠ i - 1 by omega, show i ≠ i + 1 by omega,
      show i + 1 ≠ i - 1 by omega] using this
  · have := congrFun (hx (fun j => if j = i - 1 then a else if j = i then b else x j)
      ⟨{i - 1, i}, Finset.card_le_two, fun j hj => by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hj
        simp [hj.1, hj.2]⟩) i
    simpa [lineRule_apply, show i + 1 ≠ i - 1 by omega, show i + 1 ≠ i by omega,
      show i ≠ i - 1 by omega] using this

/-- The finite core: two distinct triples, each with `f` constant on every triple sharing a
coordinate with it, make `f` constant. -/
private theorem const_of_two_triples :
    ∀ (f : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2) (a b c d e g : ZMod 2),
      (∀ u v w, (u = a ∨ v = b ∨ w = c) → f u v w = f a b c) →
      (∀ u v w, (u = d ∨ v = e ∨ w = g) → f u v w = f d e g) →
      (a, b, c) ≠ (d, e, g) → ∀ u v w, f u v w = f a b c := by
  intro f a b c d e g h1 h2 hne u v w
  have hw : f a e c = f a b c := h1 a e c (Or.inl rfl)
  have hw' : f a e c = f d e g := h2 a e c (Or.inr (Or.inl rfl))
  by_cases h : u = a ∨ v = b ∨ w = c
  · exact h1 u v w h
  · have hc : ∀ a b c d e g u v w : ZMod 2, ¬(u = a ∨ v = b ∨ w = c) → (a, b, c) ≠ (d, e, g) →
        (u = d ∨ v = e ∨ w = g) := by decide
    exact (h2 u v w (hc a b c d e g u v w h hne)).trans (hw'.symm.trans hw)

private theorem const_of_ne (f : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2)
    (x : ℤ → ZMod 2) (hx : ErasesWithin (lineRule f) x 2) (i : ℤ) (hne : x i ≠ x (i + 1)) :
    ∀ u v w, f u v w = f 0 0 0 := by
  have hne' : (x (i - 1), x i, x (i + 1)) ≠ (x (i + 1 - 1), x (i + 1), x (i + 1 + 1)) := by
    intro h
    exact hne (congrArg (fun t => t.2.1) h)
  have key := const_of_two_triples f _ _ _ _ _ _
    (fun u v w h => agree_of_erasesWithin_two f x hx i u v w h)
    (fun u v w h => agree_of_erasesWithin_two f x hx (i + 1) u v w h) hne'
  intro u v w
  rw [key u v w, key 0 0 0]

private theorem const_of_forall_eq (x : ℤ → ZMod 2) (h : ∀ i, x i = x (i + 1)) :
    ∀ i, x i = x 0 := by
  intro i
  induction i using Int.induction_on with
  | zero => rfl
  | succ k ih => rw [← ih, h k]
  | pred k ih => rw [← ih, h (-(k : ℤ) - 1)]; simp

/-- **Two states each erasing within `2` in one step have the same successor.** At scale one a
window is a triple, and a state erasing within `2` has `f` constant on every triple within two
flips of each of its own triples, which is every triple but that triple's complement. Two distinct
triples of one state then force `f` constant on all eight; a state with one triple is constant; and
the two constant states erasing within `2` together force `f`'s values at `(0,0,0)` and `(1,1,1)`
equal. In each case both successors are one constant function. No quiescence is used. -/
theorem lineRule_eq_of_erasesWithin_two (f : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2)
    (x y : ℤ → ZMod 2) (hx : ErasesWithin (lineRule f) x 2) (hy : ErasesWithin (lineRule f) y 2) :
    lineRule f x = lineRule f y := by
  by_cases hcx : ∃ i, x i ≠ x (i + 1)
  · obtain ⟨i, hi⟩ := hcx
    have hf := const_of_ne f x hx i hi
    funext j
    rw [lineRule_apply, lineRule_apply]
    exact (hf _ _ _).trans (hf _ _ _).symm
  by_cases hcy : ∃ i, y i ≠ y (i + 1)
  · obtain ⟨i, hi⟩ := hcy
    have hf := const_of_ne f y hy i hi
    funext j
    rw [lineRule_apply, lineRule_apply]
    exact (hf _ _ _).trans (hf _ _ _).symm
  push Not at hcx hcy
  have ex := const_of_forall_eq x hcx
  have ey := const_of_forall_eq y hcy
  have hxc : ∀ i, (x (i - 1), x i, x (i + 1)) = (x 0, x 0, x 0) := by
    intro i; rw [ex i, ex (i - 1), ex (i + 1)]
  have hyc : ∀ i, (y (i - 1), y i, y (i + 1)) = (y 0, y 0, y 0) := by
    intro i; rw [ey i, ey (i - 1), ey (i + 1)]
  have px := fun u v w (h : u = x 0 ∨ v = x 0 ∨ w = x 0) =>
    by simpa [ex] using agree_of_erasesWithin_two f x hx 0 u v w (by simpa [ex] using h)
  have py := fun u v w (h : u = y 0 ∨ v = y 0 ∨ w = y 0) =>
    by simpa [ey] using agree_of_erasesWithin_two f y hy 0 u v w (by simpa [ey] using h)
  have hx' : lineRule f x = fun _ => f (x 0) (x 0) (x 0) := by
    funext j; rw [lineRule_apply, ex (j - 1), ex j, ex (j + 1)]
  have hy' : lineRule f y = fun _ => f (y 0) (y 0) (y 0) := by
    funext j; rw [lineRule_apply, ey (j - 1), ey j, ey (j + 1)]
  rw [hx', hy']
  have h01 : (∀ u v w : ZMod 2, (u = 0 ∨ v = 0 ∨ w = 0) → f u v w = f 0 0 0) →
      (∀ u v w : ZMod 2, (u = 1 ∨ v = 1 ∨ w = 1) → f u v w = f 1 1 1) → f 0 0 0 = f 1 1 1 := by
    intro h0 h1
    rw [← h0 0 0 1 (by decide), h1 0 0 1 (by decide)]
  have hb : ∀ p : ZMod 2, p = 0 ∨ p = 1 := by decide
  rcases hb (x 0) with hp | hp <;> rcases hb (y 0) with hq | hq <;>
    rw [hp] at px ⊢ <;> rw [hq] at py ⊢
  all_goals first
    | rfl
    | exact congrArg (fun v => fun _ : ℤ => v) (h01 px py)
    | exact congrArg (fun v => fun _ : ℤ => v) (h01 py px).symm

/-- The two hypotheses of `lineRule_eq_of_erasesWithin_two` hold at once at two DIFFERENT states:
the constant-zero table erases within `2` everywhere, at the zero state and at the state with cell
`0` set. -/
theorem lineRule_eq_of_erasesWithin_two_nonvacuous :
    ErasesWithin (lineRule fun _ _ _ => (0 : ZMod 2)) (fun _ : ℤ => 0) 2 ∧
      ErasesWithin (lineRule fun _ _ _ => (0 : ZMod 2)) (fun i : ℤ => if i = 0 then 1 else 0) 2 ∧
      (fun _ : ℤ => (0 : ZMod 2)) ≠ (fun i : ℤ => if i = 0 then 1 else 0) := by
  refine ⟨fun _ _ => rfl, fun _ _ => rfl, fun h => ?_⟩
  have := congrFun h 0
  simp at this

/-- **Guard: the margin `2` is load-bearing.** At the majority table both constant states erase
within `1` in one step (`erasesWithin_one_const_majTable`), and their successors differ. -/
theorem lineRule_ne_of_erasesWithin_one_guard :
    ErasesWithin (lineRule majTable) (fun _ : ℤ => 0) 1 ∧
      ErasesWithin (lineRule majTable) (fun _ : ℤ => 1) 1 ∧
      lineRule majTable (fun _ : ℤ => 0) ≠ lineRule majTable (fun _ : ℤ => 1) := by
  obtain ⟨-, -, h0, h1⟩ := erasesWithin_one_const_majTable
  refine ⟨by simpa only [Function.iterate_one] using h0,
    by simpa only [Function.iterate_one] using h1, fun h => ?_⟩
  have := congrFun h 0
  revert this
  decide

end LocalMargin

/-! ## Axiom audit

Every public theorem above is `#print axioms`-clean on the standard triple, and the guards below
make that build-enforced. -/

set_option linter.style.longLine false

/-- info: 'LocalMargin.margins_add_lt_card_of_readsOnly' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LocalMargin.margins_add_lt_card_of_readsOnly

/-- info: 'LocalMargin.margins_add_lt_card_of_readsOnly_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LocalMargin.margins_add_lt_card_of_readsOnly_nonvacuous

/-- info: 'LocalMargin.margins_add_lt_card_guard' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LocalMargin.margins_add_lt_card_guard

/-- info: 'LocalMargin.tableRule_iterate_apply_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LocalMargin.tableRule_iterate_apply_congr

/-- info: 'LocalMargin.tableRule_margins_add_le_two_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LocalMargin.tableRule_margins_add_le_two_mul

/-- info: 'LocalMargin.tableRule_margins_add_le_two_mul_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LocalMargin.tableRule_margins_add_le_two_mul_nonvacuous

/-- info: 'LocalMargin.not_erasesWithin_two_const' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LocalMargin.not_erasesWithin_two_const

/-- info: 'LocalMargin.erasesWithin_one_const_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LocalMargin.erasesWithin_one_const_iff

/-- info: 'LocalMargin.erasesWithin_two_const_zero_guard' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LocalMargin.erasesWithin_two_const_zero_guard

/-- info: 'LocalMargin.erasesWithin_one_const_majTable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LocalMargin.erasesWithin_one_const_majTable

/-- info: 'LocalMargin.lineRule_eq_of_erasesWithin_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LocalMargin.lineRule_eq_of_erasesWithin_two

/-- info: 'LocalMargin.lineRule_eq_of_erasesWithin_two_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LocalMargin.lineRule_eq_of_erasesWithin_two_nonvacuous

/-- info: 'LocalMargin.lineRule_ne_of_erasesWithin_one_guard' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LocalMargin.lineRule_ne_of_erasesWithin_one_guard
