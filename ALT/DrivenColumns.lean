/-
Copyright (c) 2026 Mykola Palamarchuk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mykola Palamarchuk
-/
module

public import ALT.ObservedColumn

-- Formal-check file, not Mathlib-destined: opt out of the house-style header linter.
set_option linter.style.header false

/-!
# Driven columns: finite systems fed by an eventually periodic input
([Guests] §7 Proposition 7.26, [Guests] §7 Remark 7.25)

`ObservedColumn.lean` proves a table's own column eventually periodic when the diameter along its
orbit never grows, and exhibits an accreting table (`f90`) whose single-seed CENTER column is
nonetheless eventually periodic — the converse fails. This file extends that machinery two ways.

First, a finite-valued sequence driven by an eventually periodic input is itself eventually
periodic (`eventuallyPeriodic_of_driven`), by a pigeonhole-and-propagate argument independent of
table rules entirely. Applied to a table's own recursion, this gives: the columns strictly between
two settled columns are eventually periodic too (`eventuallyPeriodic_observedColumn_between`, via
the window form `eventuallyPeriodic_observedWindow_iff`), and the diagonal RAYS moving at the
rule's own light-cone speed are always eventually periodic, at every quiescent table and every
finitely-supported seed (`eventuallyPeriodic_observedRay_one`/`_neg_one`), with speed zero
recovering the column (`observedRay_zero`) and every other integer speed beyond `±1` running
outside the light cone entirely (not treated here).

Second, `f90`'s single-seed column at cell `1` — one cell over from the center column
`ObservedColumn.lean` already settles — is NOT eventually periodic
(`not_eventuallyPeriodic_observedColumn_f90_single_one`): it reads `1` at every stage `2 ^ j - 1`
(`j ≥ 1`) and `0` strictly between consecutive such stages, a gap that grows without bound. The
identity behind this (`iterate_two_pow_f90`) is pure `ZMod 2` cancellation over `2 ^ j` steps, no
binomial coefficient and no Lucas' theorem.

## Main results

* `eventuallyPeriodic_of_driven` — **the engine**: `[Finite α]`, a driving input eventually
  periodic in `ι`, and a step relation `a (t + 1) = g (a t) (u t)` give `a` eventually periodic.
  `eventuallyPeriodic_comp`/`eventuallyPeriodic_pair` — post-composition and pairing, its two
  standing closure facts. `eventuallyPeriodic_of_driven_nonvacuous` — a period-two `Bool` input and
  its running `xor`, meeting both hypotheses at once with the driven sequence itself not constant.
* `observedWindow`, `eventuallyPeriodic_observedWindow_iff` — a width-`(m + 1)` window is
  eventually periodic iff its two boundary columns are.
* `eventuallyPeriodic_observedColumn_between` — **the driven interior**: at `a ≤ i ≤ b`, columns
  eventually periodic at both `a` and `b` force the column at `i` eventually periodic too — a
  corollary of the window form. `eventuallyPeriodic_observedColumn_between_nonvacuous` meets its
  four hypotheses at once, at the shift `f170` from the single seed.
* `observedRay`, `observedRay_zero` — the ray at integer speed `v` from cell `e`, agreeing with the
  observed column at `v = 0`.
* `eventuallyPeriodic_observedRay_one` / `eventuallyPeriodic_observedRay_neg_one` — **the rays at
  the rule's own speed** are eventually periodic, at every quiescent table (`f 0 0 0 = 0`) and
  every finitely-supported seed, with no further hypothesis on either.
* `iterate_two_pow_f90` — `2 ^ j` steps of rule `90`, folded into one identity by repeated
  `ZMod 2` doubling-cancellation.
* `observedColumn_f90_single_one_live` / `observedColumn_f90_single_one_dead_between` — the
  single-seed column at cell `1`, under `f90`, reads `1` at every stage `2 ^ (j + 1) - 1` and `0`
  at every stage strictly between two such stages. `observedColumn_f90_single_one` assembles the
  two halves into one equality, the dyadic block a step falls in named by `Nat.log 2`.
* `not_eventuallyPeriodic_observedColumn_f90_single_one` — **the first column proved not
  eventually periodic**: the gap between consecutive live stages grows without bound, past any
  claimed period.
* `eventuallyPeriodic_observedColumn_between_guard` — the guard: one settled end does not settle
  the cells beside it, at `f90`, cells `0` and `1`.
* `not_eventuallyPeriodic_observedRay_zero_f90` — the guard: the ray theorems' speed is
  load-bearing, since speed `0` on this same witness is exactly the column just proved not
  eventually periodic.

## Scope

Registered as [Guests] §7 Proposition 7.26, rows GV-36 and GV-37: the engine is its clause (i),
the window form and the driven interior its clause (ii), the rays its clause (iii), and the
doubling identity with the column at cell `1` its clause (iv). [Guests] §7 Remark 7.25 is the
statement it extends.

The column at cell `1` is stated first as its two halves, `observedColumn_f90_single_one_live` and
`observedColumn_f90_single_one_dead_between`, and
`not_eventuallyPeriodic_observedColumn_f90_single_one` consumes the two halves alone rather than
the assembled equality. `observedColumn_f90_single_one` assembles them, over `Classical`
decidability of the existential condition, into the one equality covering every step.

Every theorem is stated at `tableRule f hq`, never at an arbitrary radius-one `U`, and the ray
theorems are stated for every table meeting quiescence alone and every finitely-supported seed —
no result here is specialized to `f90` beyond the column-`1` witness (which is precisely about
`f90`) and the guard pair built on it.
-/


@[expose] public section

namespace DrivenColumns

open ExtremeTapWidth EndpointClasses
open ObservedColumn (observedColumn hq90)

/-! ## Piece 1: the engine -/

/-- **Iterating an eventual period**: `k` copies of a period `P` still return `f` to its own value,
past the same threshold. -/
private theorem eventuallyPeriodic_apply_add_mul {α : Type*} {f : ℕ → α} {P N : ℕ}
    (hper : ∀ t, N ≤ t → f (t + P) = f t) (t : ℕ) (ht : N ≤ t) (k : ℕ) :
    f (t + k * P) = f t := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [show t + (k + 1) * P = (t + k * P) + P from by ring, hper (t + k * P) (by omega), ih]

/-- **The engine** ([Guests] §7 Proposition 7.26(i), row GV-36): a finite-valued sequence driven
by an eventually periodic input is itself eventually periodic. The values `a (N₁ + j * P)`, `N₁`
past both `hstep`'s own threshold and the input's, range over the finite type `α`, so two of them
coincide at some `j < j'`; propagating that coincidence forward one step at a time through `hstep`
and the input's own periodicity extends it to every later stage, at period `(j' - j) * P`. -/
theorem eventuallyPeriodic_of_driven {α ι : Type*} [Finite α] (g : α → ι → α)
    {u : ℕ → ι} {a : ℕ → α} (hu : GrowingComposite.EventuallyPeriodic u)
    (hstep : ∃ N, ∀ t, N ≤ t → a (t + 1) = g (a t) (u t)) :
    GrowingComposite.EventuallyPeriodic a := by
  classical
  obtain ⟨P, N₀, hP, hperu⟩ := hu
  obtain ⟨N, hstepN⟩ := hstep
  set N₁ : ℕ := max N N₀ with hN₁_def
  obtain ⟨j, j', hjj', heq⟩ := Set.Finite.exists_lt_map_eq_of_forall_mem
    (f := fun j : ℕ => a (N₁ + j * P)) (fun j => Set.mem_univ _) Set.finite_univ
  set Δ : ℕ := j' - j with hΔ_def
  have hΔpos : 0 < Δ := by omega
  have hjΔ : j' = j + Δ := by omega
  set M : ℕ := N₁ + j * P with hM_def
  have hMN : N ≤ M := by rw [hM_def, hN₁_def]; omega
  have hMN₀ : N₀ ≤ M := by rw [hM_def, hN₁_def]; omega
  have hbase : a (M + Δ * P) = a M := by
    have hidx : M + Δ * P = N₁ + j' * P := by rw [hM_def, hjΔ]; ring
    rw [hidx]; exact heq.symm
  have hind : ∀ r : ℕ, a (M + r + Δ * P) = a (M + r) := by
    intro r
    induction r with
    | zero => simpa using hbase
    | succ r ih =>
        have hrM : N ≤ M + r := le_trans hMN (Nat.le_add_right _ _)
        have hrM' : N ≤ M + r + Δ * P := le_trans hrM (Nat.le_add_right _ _)
        have hrM0 : N₀ ≤ M + r := le_trans hMN₀ (Nat.le_add_right _ _)
        have h1 : a (M + r + 1) = g (a (M + r)) (u (M + r)) := hstepN (M + r) hrM
        have h2 : a (M + r + Δ * P + 1) = g (a (M + r + Δ * P)) (u (M + r + Δ * P)) :=
          hstepN (M + r + Δ * P) hrM'
        have hu_eq : u (M + r + Δ * P) = u (M + r) :=
          eventuallyPeriodic_apply_add_mul hperu (M + r) hrM0 Δ
        calc a (M + (r + 1) + Δ * P)
            = a (M + r + Δ * P + 1) := by congr 1; ring
          _ = g (a (M + r + Δ * P)) (u (M + r + Δ * P)) := h2
          _ = g (a (M + r)) (u (M + r + Δ * P)) := by rw [ih]
          _ = g (a (M + r)) (u (M + r)) := by rw [hu_eq]
          _ = a (M + r + 1) := h1.symm
          _ = a (M + (r + 1)) := rfl
  refine ⟨Δ * P, M, Nat.mul_pos hΔpos hP, fun t ht => ?_⟩
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le ht
  exact hind r

/-- **Post-composition** ([Guests] §7 Proposition 7.26(i), row GV-36): an eventually periodic
sequence stays eventually periodic under any further map. -/
theorem eventuallyPeriodic_comp {α β : Type*} {f : ℕ → α}
    (hf : GrowingComposite.EventuallyPeriodic f) (φ : α → β) :
    GrowingComposite.EventuallyPeriodic (φ ∘ f) := by
  obtain ⟨P, N, hP, hper⟩ := hf
  exact ⟨P, N, hP, fun t ht => by simp only [Function.comp_apply, hper t ht]⟩

/-- **Pairing** ([Guests] §7 Proposition 7.26(i), row GV-36): two eventually periodic sequences
pair into one, at the product of their periods and the later of their thresholds. -/
theorem eventuallyPeriodic_pair {α β : Type*} {f : ℕ → α} {g : ℕ → β}
    (hf : GrowingComposite.EventuallyPeriodic f) (hg : GrowingComposite.EventuallyPeriodic g) :
    GrowingComposite.EventuallyPeriodic (fun t => (f t, g t)) := by
  obtain ⟨P₁, N₁, hP₁, hper₁⟩ := hf
  obtain ⟨P₂, N₂, hP₂, hper₂⟩ := hg
  refine ⟨P₁ * P₂, max N₁ N₂, Nat.mul_pos hP₁ hP₂, fun t ht => ?_⟩
  change (f (t + P₁ * P₂), g (t + P₁ * P₂)) = (f t, g t)
  have h1 : f (t + P₁ * P₂) = f t := by
    have h := eventuallyPeriodic_apply_add_mul hper₁ t (le_trans (le_max_left N₁ N₂) ht) P₂
    rwa [show P₂ * P₁ = P₁ * P₂ from by ring] at h
  have h2 : g (t + P₁ * P₂) = g t :=
    eventuallyPeriodic_apply_add_mul hper₂ t (le_trans (le_max_right N₁ N₂) ht) P₁
  rw [h1, h2]

/-- **A shift of an eventually periodic sequence stays eventually periodic**, at the same period and
threshold: internal plumbing for reading a driven state's value one step ahead. -/
private theorem eventuallyPeriodic_shift {α : Type*} {f : ℕ → α}
    (hf : GrowingComposite.EventuallyPeriodic f) (k : ℕ) :
    GrowingComposite.EventuallyPeriodic (fun t => f (t + k)) := by
  obtain ⟨P, N, hP, hper⟩ := hf
  refine ⟨P, N, hP, fun t ht => ?_⟩
  change f (t + P + k) = f (t + k)
  rw [show t + P + k = t + k + P from by ring]
  exact hper (t + k) (by omega)

/-- The smallest instance meeting `eventuallyPeriodic_of_driven`'s two hypotheses, with the driven
sequence itself not constant: a period-two input and its running XOR. -/
def nonvacDriven_u : ℕ → Bool := fun t => decide (t % 2 = 0)

def nonvacDriven_a : ℕ → Bool
  | 0 => false
  | t + 1 => xor (nonvacDriven_a t) (nonvacDriven_u t)

theorem eventuallyPeriodic_of_driven_nonvacuous :
    GrowingComposite.EventuallyPeriodic nonvacDriven_u ∧
      (∃ N, ∀ t, N ≤ t →
        nonvacDriven_a (t + 1) = xor (nonvacDriven_a t) (nonvacDriven_u t)) ∧
      nonvacDriven_a 0 ≠ nonvacDriven_a 1 := by
  refine ⟨⟨2, 0, by norm_num, fun t _ => ?_⟩, ⟨0, fun _ _ => rfl⟩, by decide⟩
  show nonvacDriven_u (t + 2) = nonvacDriven_u t
  have ht2 : (t + 2) % 2 = t % 2 := by omega
  simp only [nonvacDriven_u, ht2]

/-! ## Piece 2: the driven interior -/

/-- **The width-`(m + 1)` observed window**: cells `a, a + 1, …, a + m`, read all at once. -/
def observedWindow (U : (ℤ →₀ ZMod 2) → (ℤ →₀ ZMod 2)) (s₀ : ℤ →₀ ZMod 2) (a : ℤ) (n : ℕ) :
    ℕ → (Fin n → ZMod 2) := fun t j => (U^[t] s₀) (a + ((j : ℕ) : ℤ))

/-- **The window's own driven step**: the two boundary cells (`j = 0`, `j = m`) are read off
directly from the pair of external inputs, and every interior cell follows the table's own rule
from its two window-internal neighbours. -/
private def windowStep (f : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2) (m : ℕ) :
    (Fin (m + 1) → ZMod 2) → (ZMod 2 × ZMod 2) → (Fin (m + 1) → ZMod 2) :=
  fun w p j =>
    if hj0 : (j : ℕ) = 0 then p.1
    else if hjm : (j : ℕ) = m then p.2
    else f (w ⟨(j : ℕ) - 1, by have := j.isLt; omega⟩) (w j)
           (w ⟨(j : ℕ) + 1, by have := j.isLt; omega⟩)

/-- **The window form** ([Guests] §7 Proposition 7.26(ii), row GV-36): the whole width-`(m + 1)`
window is eventually periodic iff its two boundary columns are. Forward, two projections
(post-composition at `j = 0` and `j = m`).
Backward, `eventuallyPeriodic_of_driven` on the window itself: the pair of boundary columns,
shifted one step ahead, is the driving input (eventually periodic by `eventuallyPeriodic_pair`),
`windowStep` reads
the boundary cells off that input directly and drives the interior by `tableRule_apply`, and the
whole window's own recursion matches `windowStep`'s shape exactly. -/
theorem eventuallyPeriodic_observedWindow_iff
    (f : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2) (hq : f 0 0 0 = 0) (s₀ : ℤ →₀ ZMod 2)
    (a : ℤ) (m : ℕ) :
    GrowingComposite.EventuallyPeriodic (observedWindow (tableRule f hq) s₀ a (m + 1)) ↔
      GrowingComposite.EventuallyPeriodic (observedColumn (tableRule f hq) s₀ a) ∧
      GrowingComposite.EventuallyPeriodic (observedColumn (tableRule f hq) s₀ (a + (m : ℤ))) := by
  constructor
  · intro hW
    refine ⟨?_, ?_⟩
    · have h := eventuallyPeriodic_comp hW (fun w : Fin (m + 1) → ZMod 2 => w 0)
      have heq : (fun w : Fin (m + 1) → ZMod 2 => w 0)
          ∘ observedWindow (tableRule f hq) s₀ a (m + 1)
          = observedColumn (tableRule f hq) s₀ a := by
        funext t
        simp [observedWindow, observedColumn]
      rwa [heq] at h
    · have h := eventuallyPeriodic_comp hW (fun w : Fin (m + 1) → ZMod 2 => w (Fin.last m))
      have heq : (fun w : Fin (m + 1) → ZMod 2 => w (Fin.last m))
          ∘ observedWindow (tableRule f hq) s₀ a (m + 1)
          = observedColumn (tableRule f hq) s₀ (a + (m : ℤ)) := by
        funext t
        simp [observedWindow, observedColumn, Fin.last]
      rwa [heq] at h
  · rintro ⟨ha, hb⟩
    have hu : GrowingComposite.EventuallyPeriodic
        (fun t => (observedColumn (tableRule f hq) s₀ a (t + 1),
                   observedColumn (tableRule f hq) s₀ (a + (m : ℤ)) (t + 1))) :=
      eventuallyPeriodic_pair (eventuallyPeriodic_shift ha 1) (eventuallyPeriodic_shift hb 1)
    have hstep : ∃ N, ∀ t, N ≤ t →
        observedWindow (tableRule f hq) s₀ a (m + 1) (t + 1)
          = windowStep f m (observedWindow (tableRule f hq) s₀ a (m + 1) t)
              (observedColumn (tableRule f hq) s₀ a (t + 1),
               observedColumn (tableRule f hq) s₀ (a + (m : ℤ)) (t + 1)) := by
      refine ⟨0, fun t _ => ?_⟩
      funext j
      simp only [observedWindow, windowStep]
      split_ifs with hj0 hjm
      · rw [hj0]
        simp [observedColumn]
      · rw [hjm]
        simp [observedColumn]
      · have hjge : 1 ≤ (j : ℕ) := Nat.one_le_iff_ne_zero.mpr hj0
        have e1 : a + ((j : ℕ) : ℤ) - 1 = a + (((j : ℕ) - 1 : ℕ) : ℤ) := by
          push_cast [hjge]; ring
        have e2 : a + ((j : ℕ) : ℤ) + 1 = a + (((j : ℕ) + 1 : ℕ) : ℤ) := by push_cast; ring
        rw [← e1, ← e2, Function.iterate_succ_apply', tableRule_apply]
    exact eventuallyPeriodic_of_driven (windowStep f m) hu hstep

/-- **The driven interior, between two settled columns** ([Guests] §7 Proposition 7.26(ii), row
GV-36): at `a ≤ i ≤ b`, if the columns at `a` and `b` are each eventually periodic, so is the
column at `i`. A corollary of the window form: `i` sits
inside the width-`(b - a + 1)` window based at `a`, whose two boundary columns are exactly the
hypotheses, and `i`'s own column is one coordinate projection of that window. -/
theorem eventuallyPeriodic_observedColumn_between
    (f : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2) (hq : f 0 0 0 = 0) (s₀ : ℤ →₀ ZMod 2) {a b i : ℤ}
    (ha : GrowingComposite.EventuallyPeriodic (observedColumn (tableRule f hq) s₀ a))
    (hb : GrowingComposite.EventuallyPeriodic (observedColumn (tableRule f hq) s₀ b))
    (hai : a ≤ i) (hib : i ≤ b) :
    GrowingComposite.EventuallyPeriodic (observedColumn (tableRule f hq) s₀ i) := by
  set m : ℕ := (b - a).toNat with hm_def
  have hab : a + (m : ℤ) = b := by omega
  have hb' : GrowingComposite.EventuallyPeriodic
      (observedColumn (tableRule f hq) s₀ (a + (m : ℤ))) := by rw [hab]; exact hb
  have hW : GrowingComposite.EventuallyPeriodic (observedWindow (tableRule f hq) s₀ a (m + 1)) :=
    (eventuallyPeriodic_observedWindow_iff f hq s₀ a m).mpr ⟨ha, hb'⟩
  set k : ℕ := (i - a).toNat with hk_def
  have hklt : k < m + 1 := by omega
  have hik : a + (k : ℤ) = i := by omega
  have h := eventuallyPeriodic_comp hW (fun w : Fin (m + 1) → ZMod 2 => w ⟨k, hklt⟩)
  have heq : (fun w : Fin (m + 1) → ZMod 2 => w ⟨k, hklt⟩)
      ∘ observedWindow (tableRule f hq) s₀ a (m + 1) = observedColumn (tableRule f hq) s₀ i := by
    funext t
    change observedWindow (tableRule f hq) s₀ a (m + 1) t ⟨k, hklt⟩
      = observedColumn (tableRule f hq) s₀ i t
    simp only [observedWindow, observedColumn]
    congr 1
  rwa [heq] at h

/-- The joint-satisfiability witness for `eventuallyPeriodic_observedColumn_between`'s four
hypotheses: the shift `f170` from the single seed, at `a = -1`, `i = 0`, `b = 1`, with both end
columns eventually periodic by
`ObservedColumn.eventuallyPeriodic_observedColumn_of_zeroByEndpoints`. -/
theorem eventuallyPeriodic_observedColumn_between_nonvacuous :
    GrowingComposite.EventuallyPeriodic
        (observedColumn (tableRule f170 hq170) (Finsupp.single (0 : ℤ) (1 : ZMod 2)) (-1)) ∧
      GrowingComposite.EventuallyPeriodic
        (observedColumn (tableRule f170 hq170) (Finsupp.single (0 : ℤ) (1 : ZMod 2)) 1) ∧
      (-1 : ℤ) ≤ 0 ∧ (0 : ℤ) ≤ 1 := by
  refine ⟨?_, ?_, by norm_num, by norm_num⟩ <;>
    exact ObservedColumn.eventuallyPeriodic_observedColumn_of_zeroByEndpoints
      f170 hq170 EndpointClasses.zeroByEndpoints_f170 _ _

/-! ## Piece 3: the rays at the rule's own speed -/

/-- **The observed ray**: the value read at cell `e + v · t` at stage `t`, moving at integer speed
`v` cells per step. -/
def observedRay (U : (ℤ →₀ ZMod 2) → (ℤ →₀ ZMod 2)) (s₀ : ℤ →₀ ZMod 2) (v e : ℤ) :
    ℕ → ZMod 2 := fun t => (U^[t] s₀) (e + v * (t : ℤ))

/-- **Speed zero is the observed column** ([Guests] §7 Proposition 7.26(iii), row GV-37). -/
theorem observedRay_zero (U : (ℤ →₀ ZMod 2) → (ℤ →₀ ZMod 2)) (s₀ : ℤ →₀ ZMod 2) (e : ℤ) :
    observedRay U s₀ 0 e = observedColumn U s₀ e := by
  funext t
  simp [observedRay, observedColumn]

/-- **A bound above the support**: since `s` is finitely supported, some `M` bounds every nonzero
cell from above. -/
private theorem exists_bound_above_support (s : ℤ →₀ ZMod 2) :
    ∃ M : ℤ, ∀ k : ℤ, M < k → s k = 0 := by
  by_cases h : s.support.Nonempty
  · refine ⟨s.support.max' h, fun k hk => ?_⟩
    by_contra hc
    have := Finset.le_max' s.support k (Finsupp.mem_support_iff.mpr hc)
    omega
  · refine ⟨0, fun k _ => ?_⟩
    have hz : s = 0 := Finsupp.support_eq_empty.mp (Finset.not_nonempty_iff_eq_empty.mp h)
    rw [hz]; simp

/-- **A bound below the support**, the mirror. -/
private theorem exists_bound_below_support (s : ℤ →₀ ZMod 2) :
    ∃ M : ℤ, ∀ k : ℤ, k < M → s k = 0 := by
  by_cases h : s.support.Nonempty
  · refine ⟨s.support.min' h, fun k hk => ?_⟩
    by_contra hc
    have := Finset.min'_le s.support k (Finsupp.mem_support_iff.mpr hc)
    omega
  · refine ⟨0, fun k _ => ?_⟩
    have hz : s = 0 := Finsupp.support_eq_empty.mp (Finset.not_nonempty_iff_eq_empty.mp h)
    rw [hz]; simp

/-- **The support bound propagates forward, above**: if `s₀` vanishes past `M`, so does every
iterate, past `M` shifted by the elapsed time. -/
private theorem tableRule_iterate_eq_zero_of_gt (f : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2)
    (hq : f 0 0 0 = 0) (s₀ : ℤ →₀ ZMod 2) {M : ℤ} (hM : ∀ k : ℤ, M < k → s₀ k = 0) :
    ∀ (t : ℕ) (j : ℤ), M + (t : ℤ) < j → ((tableRule f hq)^[t] s₀) j = 0 := by
  intro t
  induction t with
  | zero => intro j hj; exact hM j (by omega)
  | succ t ih =>
      intro j hj
      rw [Function.iterate_succ_apply', tableRule_apply,
        ih (j - 1) (by omega), ih j (by omega), ih (j + 1) (by omega)]
      exact hq

/-- **The support bound propagates forward, below**, the mirror. -/
private theorem tableRule_iterate_eq_zero_of_lt (f : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2)
    (hq : f 0 0 0 = 0) (s₀ : ℤ →₀ ZMod 2) {M : ℤ} (hM : ∀ k : ℤ, k < M → s₀ k = 0) :
    ∀ (t : ℕ) (j : ℤ), j < M - (t : ℤ) → ((tableRule f hq)^[t] s₀) j = 0 := by
  intro t
  induction t with
  | zero => intro j hj; exact hM j (by omega)
  | succ t ih =>
      intro j hj
      rw [Function.iterate_succ_apply', tableRule_apply,
        ih (j - 1) (by omega), ih j (by omega), ih (j + 1) (by omega)]
      exact hq

/-- **A ray starting beyond the support's upper bound is constantly `0`**. -/
private theorem observedRay_one_eq_zero_of_gt (f : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2)
    (hq : f 0 0 0 = 0) (s₀ : ℤ →₀ ZMod 2) {M e : ℤ} (hM : ∀ k : ℤ, M < k → s₀ k = 0)
    (he : M < e) (t : ℕ) : observedRay (tableRule f hq) s₀ 1 e t = 0 :=
  tableRule_iterate_eq_zero_of_gt f hq s₀ hM t (e + 1 * (t : ℤ)) (by omega)

/-- **A ray starting beyond the support's lower bound is constantly `0`**, the mirror. -/
private theorem observedRay_neg_one_eq_zero_of_lt (f : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2)
    (hq : f 0 0 0 = 0) (s₀ : ℤ →₀ ZMod 2) {M e : ℤ} (hM : ∀ k : ℤ, k < M → s₀ k = 0)
    (he : e < M) (t : ℕ) : observedRay (tableRule f hq) s₀ (-1) e t = 0 :=
  tableRule_iterate_eq_zero_of_lt f hq s₀ hM t (e + (-1) * (t : ℤ)) (by omega)

private theorem eventuallyPeriodic_observedRay_one_of_gt (f : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2)
    (hq : f 0 0 0 = 0) (s₀ : ℤ →₀ ZMod 2) {M e : ℤ} (hM : ∀ k : ℤ, M < k → s₀ k = 0)
    (he : M < e) : GrowingComposite.EventuallyPeriodic (observedRay (tableRule f hq) s₀ 1 e) :=
  ⟨1, 0, one_pos, fun t _ => by
    rw [observedRay_one_eq_zero_of_gt f hq s₀ hM he, observedRay_one_eq_zero_of_gt f hq s₀ hM he]⟩

private theorem eventuallyPeriodic_observedRay_neg_one_of_lt (f : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2)
    (hq : f 0 0 0 = 0) (s₀ : ℤ →₀ ZMod 2) {M e : ℤ} (hM : ∀ k : ℤ, k < M → s₀ k = 0)
    (he : e < M) :
    GrowingComposite.EventuallyPeriodic (observedRay (tableRule f hq) s₀ (-1) e) :=
  ⟨1, 0, one_pos, fun t _ => by
    rw [observedRay_neg_one_eq_zero_of_lt f hq s₀ hM he,
      observedRay_neg_one_eq_zero_of_lt f hq s₀ hM he]⟩

/-- **The ray at speed `1`, by strong induction on the distance to the support's upper bound**:
`ray_e (t + 1) = f (ray_e t) (ray_{e+1} t) (ray_{e+2} t)` drives `ray_e` by the pair `(ray_{e+1},
ray_{e+2})`, each closer to (or past) the bound, so `eventuallyPeriodic_of_driven` closes the
induction once the pair is eventually periodic by the induction hypothesis and pairing. -/
private theorem eventuallyPeriodic_observedRay_one_of_le (f : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2)
    (hq : f 0 0 0 = 0) (s₀ : ℤ →₀ ZMod 2) {M : ℤ} (hM : ∀ k : ℤ, M < k → s₀ k = 0) :
    ∀ n : ℕ, ∀ e : ℤ, (M + 1 - e).toNat ≤ n →
      GrowingComposite.EventuallyPeriodic (observedRay (tableRule f hq) s₀ 1 e) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro e he
    by_cases hcase : M < e
    · exact eventuallyPeriodic_observedRay_one_of_gt f hq s₀ hM hcase
    · push Not at hcase
      have hu := eventuallyPeriodic_pair (ih (M + 1 - (e + 1)).toNat (by omega) (e + 1) le_rfl)
        (ih (M + 1 - (e + 2)).toNat (by omega) (e + 2) le_rfl)
      have hstep : ∃ N, ∀ t, N ≤ t →
          observedRay (tableRule f hq) s₀ 1 e (t + 1)
            = (fun (x : ZMod 2) (p : ZMod 2 × ZMod 2) => f x p.1 p.2)
                (observedRay (tableRule f hq) s₀ 1 e t)
                ((fun t => (observedRay (tableRule f hq) s₀ 1 (e + 1) t,
                            observedRay (tableRule f hq) s₀ 1 (e + 2) t)) t) := by
        refine ⟨0, fun t _ => ?_⟩
        change ((tableRule f hq)^[t + 1] s₀) (e + 1 * ((t + 1 : ℕ) : ℤ))
          = f (((tableRule f hq)^[t] s₀) (e + 1 * (t : ℤ)))
              (((tableRule f hq)^[t] s₀) ((e + 1) + 1 * (t : ℤ)))
              (((tableRule f hq)^[t] s₀) ((e + 2) + 1 * (t : ℤ)))
        have e1 : e + 1 * ((t + 1 : ℕ) : ℤ) - 1 = e + 1 * (t : ℤ) := by push_cast; ring
        have e2 : e + 1 * ((t + 1 : ℕ) : ℤ) = (e + 1) + 1 * (t : ℤ) := by push_cast; ring
        have e3 : e + 1 * ((t + 1 : ℕ) : ℤ) + 1 = (e + 2) + 1 * (t : ℤ) := by push_cast; ring
        rw [Function.iterate_succ_apply', tableRule_apply, e1, e3, e2]
      exact eventuallyPeriodic_of_driven (fun (x : ZMod 2) (p : ZMod 2 × ZMod 2) => f x p.1 p.2)
        hu hstep

/-- **The ray at speed `-1`**, the mirror: `ray_e (t + 1) = f (ray_{e-2} t) (ray_{e-1} t) (ray_e
t)` drives `ray_e` by the pair `(ray_{e-2}, ray_{e-1})`, by strong induction on the distance to the
support's lower bound. -/
private theorem eventuallyPeriodic_observedRay_neg_one_of_le (f : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2)
    (hq : f 0 0 0 = 0) (s₀ : ℤ →₀ ZMod 2) {M : ℤ} (hM : ∀ k : ℤ, k < M → s₀ k = 0) :
    ∀ n : ℕ, ∀ e : ℤ, (e - M + 1).toNat ≤ n →
      GrowingComposite.EventuallyPeriodic (observedRay (tableRule f hq) s₀ (-1) e) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro e he
    by_cases hcase : e < M
    · exact eventuallyPeriodic_observedRay_neg_one_of_lt f hq s₀ hM hcase
    · push Not at hcase
      have hu := eventuallyPeriodic_pair (ih (e - 2 - M + 1).toNat (by omega) (e - 2) le_rfl)
        (ih (e - 1 - M + 1).toNat (by omega) (e - 1) le_rfl)
      have hstep : ∃ N, ∀ t, N ≤ t →
          observedRay (tableRule f hq) s₀ (-1) e (t + 1)
            = (fun (x : ZMod 2) (p : ZMod 2 × ZMod 2) => f p.1 p.2 x)
                (observedRay (tableRule f hq) s₀ (-1) e t)
                ((fun t => (observedRay (tableRule f hq) s₀ (-1) (e - 2) t,
                            observedRay (tableRule f hq) s₀ (-1) (e - 1) t)) t) := by
        refine ⟨0, fun t _ => ?_⟩
        change ((tableRule f hq)^[t + 1] s₀) (e + (-1) * ((t + 1 : ℕ) : ℤ))
          = f (((tableRule f hq)^[t] s₀) ((e - 2) + (-1) * (t : ℤ)))
              (((tableRule f hq)^[t] s₀) ((e - 1) + (-1) * (t : ℤ)))
              (((tableRule f hq)^[t] s₀) (e + (-1) * (t : ℤ)))
        have e1 : e + (-1) * ((t + 1 : ℕ) : ℤ) - 1 = (e - 2) + (-1) * (t : ℤ) := by push_cast; ring
        have e2 : e + (-1) * ((t + 1 : ℕ) : ℤ) = (e - 1) + (-1) * (t : ℤ) := by push_cast; ring
        have e3 : e + (-1) * ((t + 1 : ℕ) : ℤ) + 1 = e + (-1) * (t : ℤ) := by push_cast; ring
        rw [Function.iterate_succ_apply', tableRule_apply, e1, e3, e2]
      exact eventuallyPeriodic_of_driven (fun (x : ZMod 2) (p : ZMod 2 × ZMod 2) => f p.1 p.2 x)
        hu hstep

/-- **The ray at speed `1` is eventually periodic** ([Guests] §7 Proposition 7.26(iii), row GV-37),
at every table meeting quiescence alone and every finitely-supported seed. -/
theorem eventuallyPeriodic_observedRay_one
    (f : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2) (hq : f 0 0 0 = 0) (s₀ : ℤ →₀ ZMod 2) (e : ℤ) :
    GrowingComposite.EventuallyPeriodic (observedRay (tableRule f hq) s₀ 1 e) := by
  obtain ⟨M, hM⟩ := exists_bound_above_support s₀
  exact eventuallyPeriodic_observedRay_one_of_le f hq s₀ hM (M + 1 - e).toNat e le_rfl

/-- **The ray at speed `-1` is eventually periodic** ([Guests] §7 Proposition 7.26(iii), row
GV-37), the mirror. -/
theorem eventuallyPeriodic_observedRay_neg_one
    (f : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2) (hq : f 0 0 0 = 0) (s₀ : ℤ →₀ ZMod 2) (e : ℤ) :
    GrowingComposite.EventuallyPeriodic (observedRay (tableRule f hq) s₀ (-1) e) := by
  obtain ⟨M, hM⟩ := exists_bound_below_support s₀
  exact eventuallyPeriodic_observedRay_neg_one_of_le f hq s₀ hM (e - M + 1).toNat e le_rfl

/-! ## Piece 4: a column that is not eventually periodic -/

/-- **`2 ^ j` steps of rule `90`, in one identity** ([Guests] §7 Proposition 7.26(iv), row GV-37):
pure `ZMod 2` cancellation of the doubled middle term, no binomial coefficient and no Lucas'
theorem. -/
theorem iterate_two_pow_f90 :
    ∀ (j : ℕ) (s : ℤ →₀ ZMod 2) (i : ℤ),
      ((tableRule f90 hq90) ^[2 ^ j] s) i = s (i - 2 ^ j) + s (i + 2 ^ j) := by
  intro j
  induction j with
  | zero =>
      intro s i
      change (tableRule f90 hq90 s) i = s (i - (2 : ℤ) ^ (0 : ℕ)) + s (i + (2 : ℤ) ^ (0 : ℕ))
      rw [tableRule_apply]
      norm_num [EndpointClasses.f90]
  | succ j ih =>
      intro s i
      have hiter : (2 : ℕ) ^ (j + 1) = 2 ^ j + 2 ^ j := by rw [pow_succ]; ring
      rw [hiter, Function.iterate_add_apply, ih ((tableRule f90 hq90) ^[2 ^ j] s) i,
        ih s (i - (2 : ℤ) ^ j), ih s (i + (2 : ℤ) ^ j)]
      have hpow : (2 : ℤ) ^ (j + 1) = (2 : ℤ) ^ j + (2 : ℤ) ^ j := by rw [pow_succ]; ring
      have e1 : i - (2 : ℤ) ^ j - (2 : ℤ) ^ j = i - (2 : ℤ) ^ (j + 1) := by rw [hpow]; ring
      have e2 : i - (2 : ℤ) ^ j + (2 : ℤ) ^ j = i := by ring
      have e3 : i + (2 : ℤ) ^ j - (2 : ℤ) ^ j = i := by ring
      have e4 : i + (2 : ℤ) ^ j + (2 : ℤ) ^ j = i + (2 : ℤ) ^ (j + 1) := by rw [hpow]; ring
      rw [e1, e2, e3, e4]
      have hcollapse : ∀ a b c : ZMod 2, a + b + (b + c) = a + c := by decide
      exact hcollapse (s (i - (2 : ℤ) ^ (j + 1))) (s i) (s (i + (2 : ℤ) ^ (j + 1)))

/-- **The light cone's edge is live**: the leftmost reachable cell at stage `r`, from the single
seed, always carries a `1` — by induction on `r`, using the lower support bound
(`tableRule_iterate_eq_zero_of_lt`) to kill the two cells feeding the edge from further left. -/
private theorem observedColumn_f90_single_edge :
    ∀ r : ℕ, ((tableRule f90 hq90) ^[r] (Finsupp.single (0 : ℤ) (1 : ZMod 2))) (-(r : ℤ)) = 1 := by
  intro r
  induction r with
  | zero => simp
  | succ r ih =>
      have hM : ∀ k : ℤ, k < 0 → (Finsupp.single (0 : ℤ) (1 : ZMod 2)) k = 0 := by
        intro k hk
        exact Finsupp.single_eq_of_ne (by omega)
      have hleft2 := tableRule_iterate_eq_zero_of_lt f90 hq90
        (Finsupp.single (0 : ℤ) (1 : ZMod 2)) hM r (-(r : ℤ) - 2) (by omega)
      have hleft1 := tableRule_iterate_eq_zero_of_lt f90 hq90
        (Finsupp.single (0 : ℤ) (1 : ZMod 2)) hM r (-(r : ℤ) - 1) (by omega)
      change ((tableRule f90 hq90) ^[r + 1] (Finsupp.single (0 : ℤ) (1 : ZMod 2)))
        (-((r : ℤ) + 1)) = 1
      have e1 : -((r : ℤ) + 1) - 1 = -(r : ℤ) - 2 := by ring
      have e2 : -((r : ℤ) + 1) + 1 = -(r : ℤ) := by ring
      have e0 : -((r : ℤ) + 1) = -(r : ℤ) - 1 := by ring
      rw [Function.iterate_succ_apply', tableRule_apply, e1, e2, e0, hleft2, hleft1, ih]
      decide

/-- **The step identity read at cell `1`**, combining `iterate_two_pow_f90` with
`Function.iterate_add_apply`. -/
private theorem observedColumn_f90_single_step (j r : ℕ) :
    ((tableRule f90 hq90) ^[2 ^ j + r] (Finsupp.single (0 : ℤ) (1 : ZMod 2))) 1
      = ((tableRule f90 hq90) ^[r] (Finsupp.single (0 : ℤ) (1 : ZMod 2))) (1 - 2 ^ j)
        + ((tableRule f90 hq90) ^[r] (Finsupp.single (0 : ℤ) (1 : ZMod 2))) (1 + 2 ^ j) := by
  rw [Function.iterate_add_apply, iterate_two_pow_f90]

/-- **Live at `2 ^ (j + 1) - 1`** ([Guests] §7 Proposition 7.26(iv), row GV-37): the column at
cell `1` reads `1` at every stage `2 ^ j' - 1` with `j' ≥ 1`, one cell over from the center column
of [Guests] §7 Remark 7.25. Route: `2 ^ (j + 1) - 1 = 2 ^ j + (2 ^ j - 1)`, and the step identity at
`r = 2 ^ j - 1` gives the edge-live value (`observedColumn_f90_single_edge`, since `1 - 2 ^ j = -(2
^ j - 1)`) plus a cell beyond the `r`-step support (`0`, `tableRule_iterate_eq_zero_of_gt`). -/
theorem observedColumn_f90_single_one_live (j : ℕ) :
    ((tableRule f90 hq90) ^[2 ^ (j + 1) - 1] (Finsupp.single (0 : ℤ) (1 : ZMod 2))) 1 = 1 := by
  have h1 : (1 : ℕ) ≤ 2 ^ j := Nat.one_le_two_pow
  have hcastp : ((2 ^ j : ℕ) : ℤ) = (2 : ℤ) ^ j := by push_cast; ring
  have hidx : 2 ^ j + (2 ^ j - 1) = 2 ^ (j + 1) - 1 := by rw [pow_succ]; omega
  have hstep := observedColumn_f90_single_step j (2 ^ j - 1)
  rw [hidx] at hstep
  have hcast : ((2 ^ j - 1 : ℕ) : ℤ) = (2 : ℤ) ^ j - 1 := by
    rw [Nat.cast_sub h1]; push_cast; ring
  have hEdge := observedColumn_f90_single_edge (2 ^ j - 1)
  have heq : -((2 ^ j - 1 : ℕ) : ℤ) = 1 - (2 : ℤ) ^ j := by rw [hcast]; ring
  rw [heq] at hEdge
  have hM0 : ∀ k : ℤ, 0 < k → (Finsupp.single (0 : ℤ) (1 : ZMod 2)) k = 0 := by
    intro k hk; exact Finsupp.single_eq_of_ne (by omega)
  have hZero := tableRule_iterate_eq_zero_of_gt f90 hq90
    (Finsupp.single (0 : ℤ) (1 : ZMod 2)) hM0 (2 ^ j - 1) (1 + (2 : ℤ) ^ j) (by omega)
  rw [hstep, hEdge, hZero]
  decide

/-- **Dead strictly between two live stages** ([Guests] §7 Proposition 7.26(iv), row GV-37): at
`2 ^ j + r` with `r < 2 ^ j - 1`, the column at cell `1` reads `0` — the other half of the witness.
Route: the step identity's two summands both
land beyond the `r`-step support, above (`1 + 2 ^ j`) and below (`1 - 2 ^ j`, exactly where
`r < 2 ^ j - 1` bites). -/
theorem observedColumn_f90_single_one_dead_between (j r : ℕ) (hr : r < 2 ^ j - 1) :
    ((tableRule f90 hq90) ^[2 ^ j + r] (Finsupp.single (0 : ℤ) (1 : ZMod 2))) 1 = 0 := by
  have hcastp : ((2 ^ j : ℕ) : ℤ) = (2 : ℤ) ^ j := by push_cast; ring
  have hstep := observedColumn_f90_single_step j r
  have hM0 : ∀ k : ℤ, 0 < k → (Finsupp.single (0 : ℤ) (1 : ZMod 2)) k = 0 := by
    intro k hk; exact Finsupp.single_eq_of_ne (by omega)
  have hMlt : ∀ k : ℤ, k < 0 → (Finsupp.single (0 : ℤ) (1 : ZMod 2)) k = 0 := by
    intro k hk; exact Finsupp.single_eq_of_ne (by omega)
  have hZ1 := tableRule_iterate_eq_zero_of_lt f90 hq90
    (Finsupp.single (0 : ℤ) (1 : ZMod 2)) hMlt r (1 - (2 : ℤ) ^ j) (by omega)
  have hZ2 := tableRule_iterate_eq_zero_of_gt f90 hq90
    (Finsupp.single (0 : ℤ) (1 : ZMod 2)) hM0 r (1 + (2 : ℤ) ^ j) (by omega)
  rw [hstep, hZ1, hZ2]
  decide

open Classical in
/-- **The column at cell `1`, assembled into one equality**: `observedColumn_f90_single_one_live`
and `observedColumn_f90_single_one_dead_between` cover disjoint, contiguous dyadic blocks
`[2 ^ j, 2 ^ (j + 1) - 1]` (`j ≥ 1`) tiling every step from `1` on, with step `0` separate (the
seed itself misses cell `1`); `Nat.log 2` names the unique block a step `≥ 1` falls in. -/
theorem observedColumn_f90_single_one :
    observedColumn (tableRule f90 hq90) (Finsupp.single (0 : ℤ) (1 : ZMod 2)) 1
      = fun t => if ∃ j, 0 < j ∧ t + 1 = 2 ^ j then 1 else 0 := by
  funext t
  simp only [observedColumn]
  split_ifs with hcase
  · obtain ⟨j, hjpos, hjeq⟩ := hcase
    obtain ⟨j', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hjpos.ne'
    have hlive := observedColumn_f90_single_one_live j'
    rwa [show t = 2 ^ (j' + 1) - 1 from by omega]
  · rcases Nat.eq_zero_or_pos t with ht0 | htpos
    · subst ht0
      simp
    · set j := Nat.log 2 t with hj_def
      have h1 : 2 ^ j ≤ t := Nat.pow_log_le_self 2 (by omega)
      have h2 : t < 2 ^ (j + 1) := Nat.lt_pow_succ_log_self (by norm_num) t
      have hpow : 2 ^ (j + 1) = 2 * 2 ^ j := by rw [pow_succ]; ring
      have hjpos : 0 < j := by
        rcases Nat.eq_zero_or_pos j with hj0 | hj0
        · exfalso
          have h2c := h2
          rw [hj0] at h2c
          norm_num at h2c
          apply hcase
          refine ⟨1, one_pos, ?_⟩
          change t + 1 = 2
          omega
        · exact hj0
      have hne : t ≠ 2 ^ (j + 1) - 1 := by
        intro heqt
        apply hcase
        exact ⟨j + 1, by omega, by omega⟩
      have hjge1 : 1 ≤ 2 ^ j := Nat.one_le_two_pow
      have hr : t - 2 ^ j < 2 ^ j - 1 := by omega
      have hidx : 2 ^ j + (t - 2 ^ j) = t := by omega
      have hdead := observedColumn_f90_single_one_dead_between j (t - 2 ^ j) hr
      rwa [hidx] at hdead

/-- **The column at `f90`'s center-adjacent cell is not eventually periodic** ([Guests] §7
Proposition 7.26(iv), row GV-37), from the single seed: half of [Guests] §7 Remark 7.25's own
witness (`observedColumn_f90_single`, at cell `0`) does not extend to cell `1`. Route: given a
period `P` from `N`, pick `j` past `N + P + 1`; stage `2 ^ j - 1` is live and stage `2 ^ j - 1 + P`
is dead, contradicting the period. -/
theorem not_eventuallyPeriodic_observedColumn_f90_single_one :
    ¬ GrowingComposite.EventuallyPeriodic
      (observedColumn (tableRule f90 hq90) (Finsupp.single (0 : ℤ) (1 : ZMod 2)) 1) := by
  rintro ⟨P, N, hP, hper⟩
  set j : ℕ := N + P + 2 with hj_def
  have hjbig : N + P + 1 < 2 ^ j := by
    have hlt := Nat.lt_two_pow_self (n := j)
    omega
  have hj1 : 1 ≤ j := by omega
  have hlive := observedColumn_f90_single_one_live (j - 1)
  rw [show j - 1 + 1 = j from by omega] at hlive
  have ht1N : N ≤ 2 ^ j - 1 := by omega
  have hr : P - 1 < 2 ^ j - 1 := by omega
  have hdb := observedColumn_f90_single_one_dead_between j (P - 1) hr
  have hidx : 2 ^ j + (P - 1) = 2 ^ j - 1 + P := by omega
  rw [hidx] at hdb
  have hthis := hper (2 ^ j - 1) ht1N
  simp only [observedColumn] at hthis
  rw [hdb, hlive] at hthis
  exact absurd hthis (by decide)

/-! ## Piece 5: the guards -/

/-- **`eventuallyPeriodic_observedColumn_between`'s second end is load-bearing** ([Guests] §7
Proposition 7.26(ii), row GV-36). At `f90`, the single seed, `a = 0`, `i = 1 = b`: the column at
`0` is eventually periodic
(`ObservedColumn.observedColumn_f90_single`), but the column at `1` is not
(`not_eventuallyPeriodic_observedColumn_f90_single_one`) — one settled end does not settle the
cells beside it. -/
theorem eventuallyPeriodic_observedColumn_between_guard :
    ∃ (f : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2) (hq : f 0 0 0 = 0) (s₀ : ℤ →₀ ZMod 2)
      (a i b : ℤ), a ≤ i ∧ i ≤ b ∧
      GrowingComposite.EventuallyPeriodic (observedColumn (tableRule f hq) s₀ a) ∧
      ¬ GrowingComposite.EventuallyPeriodic (observedColumn (tableRule f hq) s₀ i) := by
  refine ⟨f90, hq90, Finsupp.single 0 1, 0, 1, 1, by norm_num, le_rfl, ?_, ?_⟩
  · rw [ObservedColumn.observedColumn_f90_single]
    exact ⟨1, 1, one_pos, fun u _ => by
      have h2 : u ≠ 0 := by omega
      simp [h2]⟩
  · exact not_eventuallyPeriodic_observedColumn_f90_single_one

/-- **The speed is load-bearing in `eventuallyPeriodic_observedRay_one`/`_neg_one`** ([Guests] §7
Proposition 7.26(iii), row GV-37). At speed `0` a ray is exactly a column (`observedRay_zero`), and
this column
(`not_eventuallyPeriodic_observedColumn_f90_single_one`'s own witness) is not eventually
periodic. -/
theorem not_eventuallyPeriodic_observedRay_zero_f90 :
    ¬ GrowingComposite.EventuallyPeriodic
      (observedRay (tableRule f90 hq90) (Finsupp.single (0 : ℤ) (1 : ZMod 2)) 0 1) := by
  rw [observedRay_zero]
  exact not_eventuallyPeriodic_observedColumn_f90_single_one

end DrivenColumns

/-! ## Axiom audit

Every public theorem above is `#print axioms`-clean on the standard triple, and the guards below
make that build-enforced. -/

set_option linter.style.longLine false

/-- info: 'DrivenColumns.eventuallyPeriodic_of_driven' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DrivenColumns.eventuallyPeriodic_of_driven

/-- info: 'DrivenColumns.eventuallyPeriodic_comp' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms DrivenColumns.eventuallyPeriodic_comp

/-- info: 'DrivenColumns.eventuallyPeriodic_pair' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DrivenColumns.eventuallyPeriodic_pair

/-- info: 'DrivenColumns.eventuallyPeriodic_of_driven_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DrivenColumns.eventuallyPeriodic_of_driven_nonvacuous

/-- info: 'DrivenColumns.eventuallyPeriodic_observedWindow_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DrivenColumns.eventuallyPeriodic_observedWindow_iff

/-- info: 'DrivenColumns.eventuallyPeriodic_observedColumn_between' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DrivenColumns.eventuallyPeriodic_observedColumn_between

/-- info: 'DrivenColumns.eventuallyPeriodic_observedColumn_between_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DrivenColumns.eventuallyPeriodic_observedColumn_between_nonvacuous

/-- info: 'DrivenColumns.observedRay_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DrivenColumns.observedRay_zero

/-- info: 'DrivenColumns.eventuallyPeriodic_observedRay_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DrivenColumns.eventuallyPeriodic_observedRay_one

/-- info: 'DrivenColumns.eventuallyPeriodic_observedRay_neg_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DrivenColumns.eventuallyPeriodic_observedRay_neg_one

/-- info: 'DrivenColumns.iterate_two_pow_f90' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DrivenColumns.iterate_two_pow_f90

/-- info: 'DrivenColumns.observedColumn_f90_single_one_live' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DrivenColumns.observedColumn_f90_single_one_live

/-- info: 'DrivenColumns.observedColumn_f90_single_one_dead_between' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DrivenColumns.observedColumn_f90_single_one_dead_between

/-- info: 'DrivenColumns.observedColumn_f90_single_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DrivenColumns.observedColumn_f90_single_one

/-- info: 'DrivenColumns.not_eventuallyPeriodic_observedColumn_f90_single_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DrivenColumns.not_eventuallyPeriodic_observedColumn_f90_single_one

/-- info: 'DrivenColumns.eventuallyPeriodic_observedColumn_between_guard' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DrivenColumns.eventuallyPeriodic_observedColumn_between_guard

/-- info: 'DrivenColumns.not_eventuallyPeriodic_observedRay_zero_f90' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DrivenColumns.not_eventuallyPeriodic_observedRay_zero_f90
