/-
Copyright (c) 2026 Mykola Palamarchuk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mykola Palamarchuk
-/
module

public import Batteries.Tactic.OpenPrivate
public import ALT.EndpointClasses
public import ALT.GrowingComposite
import all ALT.EndpointClasses
import all ALT.ExtremeTapWidth

-- Formal-check file, not Mathlib-destined: opt out of the house-style header linter.
set_option linter.style.header false

/-!
# The observed column: a non-periodic cell observation forces unbounded diameter
([Guests] §7 Definition 7.2 and Propositions 7.24 and 7.28, [Growth] §3)

A radius-one table rule acts on the finitely-supported configurations of the line. An observer who
reads one cell `i` along the orbit of a seed `s₀` sees the column `t ↦ (U^t s₀) i`
(`observedColumn`). [Growth] §3 makes eventual periodicity the hinge between a finite recurrent
core and a growing orbit; this file proves the corresponding fact for the table rules, with the
support DIAMETER as the size ([Guests] §7 Definition 7.2's "encoded size", one reading of it):

**at a table rule whose diameter never grows, every observed column is eventually periodic.**

The argument is a recurrence with drift. A rule commutes with translation, and along an orbit whose
diameter never exceeds `D` the state read up to translation lives in the finite set of
configurations supported on `D` cells, so two stages of the orbit have the same pattern: the later
one is the earlier one translated by some `d`. Translation commutes with the rule, so the orbit
from the earlier stage on repeats with period `P` (the stage gap) up to a drift of `d` cells per
period. At `d = 0` the column is periodic with period `P`; at `d ≠ 0` the finitely many pattern
phases drift off the observed cell for good, and the column is eventually constant `0`.

The zero class of [Guests] §7 Proposition 7.24 (`EndpointClasses.ZeroByEndpoints`) is a family of
tables at which the diameter never grows, so its observed columns are all eventually periodic. The
contrapositive is the form to cite: a cell observation that is not eventually periodic forces the
diameter to grow along the orbit, so the observer's unending repairs are paid for by the host's
accretion.

## Main results

* `observedColumn` — the column read at cell `i` along the orbit of `s₀` under `U`.
* `eventuallyPeriodic_observedColumn_of_diam_le` — at a quiescent table rule whose diameter never
  grows, every observed column is eventually periodic.
* `eventuallyPeriodic_observedColumn_of_zeroByEndpoints` — the corollary at every table of the zero
  class.
* `exists_diam_lt_iterate_of_not_eventuallyPeriodic` — the contrapositive along the orbit of the
  seed: a non-periodic observed column forces a growth step of the diameter at some stage of the
  orbit; `exists_diam_lt_of_not_eventuallyPeriodic` is its form over all states.
* `eventuallyPeriodic_observedColumn_of_zeroByEndpoints_nonvacuous` — both hypotheses of the
  corollary are met at once, at the shift `f170` (each cell reads its right neighbour), with
  `observedColumn_f170_single` its column from the single seed.
* `observedColumn_f90_single` / `observedColumn_f90_eventually_periodic_witness` — **the converse
  fails** ([Guests] §7 Remark 7.25): at `f90` (`EndpointClasses.AccretesByEndpoints`, whose diameter
  is unbounded rather than never growing), the single seed's column at the center is nonetheless
  `1` then `0` forever, by a symmetry the seed keeps under `i ↦ -i` through every step
  (`tableRule_f90_single_neg`) — eventual periodicity does not force the diameter back down.
* `diam_lt_tableRule_f30_single` — the diameter hypothesis is load-bearing: at rule 30 the single
  seed's diameter goes from `1` to `3`, so the hypothesis of the first theorem fails there.
* `observedRationalRay` — the ray of rational speed `p / q` from cell `e`: the value at
  `e + ⌊p t / q⌋` at step `t`; `observedRationalRay_zero` is the observed column at speed `0`.
  The rational ray is [Guests] §7 Proposition 7.28, the column staying Remark 7.25's.
* `eventuallyPeriodic_observedRationalRay_of_diam_le` — at a quiescent table rule whose diameter
  never grows, every rational ray from every seed is eventually periodic: sampled every `q P`
  steps of the drift's period `P`, the ray either reads one cell of the repeating pattern for ever
  or leaves it for good. `eventuallyPeriodic_observedRationalRay_of_zeroByEndpoints` is the
  corollary at the zero class, and `eventuallyPeriodic_observedRationalRay_of_diam_le_nonvacuous`
  meets the three hypotheses at the shift `f170`.

## Scope

The theorems are about the observed column, and the rational ray, of the RULE `tableRule f hq` on
configurations of finite support, at one seed and one cell or one ray. Nothing here classifies the
tables whose diameter grows, and nothing is claimed about the column or any ray at any such
table, rule 30's included: the guard
`diam_lt_tableRule_f30_single` shows only that the hypothesis fails there. The diameter is one
reading of "size"; the support count, another, is not used.
-/

open private translate_zero translate_apply translate_support diam_eq' from ALT.EndpointClasses
open private card_regionStates from ALT.ExtremeTapWidth

@[expose] public section

namespace ObservedColumn

open ExtremeTapWidth LightConeWidth
open EndpointClasses (ZeroByEndpoints zeroByEndpoints_f170 diam_tableRule_le_of_noTap
  diam_tableRule_le_of_leftTap_rightDies diam_tableRule_le_of_rightTap_leftDies
  AccretesByEndpoints f90 accretesByEndpoints_f90)

-- Shorthand for `EndpointClasses.translate`, which Mathlib's root-level `translate` makes
-- ambiguous once `EndpointClasses` is opened.
local notation "τ" => EndpointClasses.translate

/-! ## The observed column -/

/-- **The observed column**: the value an observer reads at cell `i` at stage `t` along the orbit
of `s₀` under `U`. -/
def observedColumn (U : (ℤ →₀ ZMod 2) → (ℤ →₀ ZMod 2)) (s₀ : ℤ →₀ ZMod 2) (i : ℤ) : ℕ → ZMod 2 :=
  fun t => (U^[t] s₀) i

/-! ## Translation: the cell rule, composition, and the rule's equivariance -/

private theorem translate_apply_sub (i x : ℤ) (s : ℤ →₀ ZMod 2) : τ i s x = s (x - i) := by
  have h := translate_apply i (x - i) s
  rwa [sub_add_cancel] at h

private theorem translate_translate (a b : ℤ) (s : ℤ →₀ ZMod 2) :
    τ a (τ b s) = τ (a + b) s := by
  ext x
  rw [translate_apply_sub, translate_apply_sub, translate_apply_sub, sub_sub]

private theorem tableRule_translate (f : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2) (hq : f 0 0 0 = 0)
    (k : ℤ) (s : ℤ →₀ ZMod 2) :
    tableRule f hq (τ k s) = τ k (tableRule f hq s) := by
  ext x
  simp only [tableRule_apply, translate_apply_sub]
  rw [show x - 1 - k = x - k - 1 by ring, show x + 1 - k = x - k + 1 by ring]

private theorem iterate_translate {U : (ℤ →₀ ZMod 2) → (ℤ →₀ ZMod 2)}
    (hE : ∀ (d : ℤ) (s : ℤ →₀ ZMod 2), U (τ d s) = τ d (U s))
    (d : ℤ) (s : ℤ →₀ ZMod 2) :
    ∀ k : ℕ, U^[k] (τ d s) = τ d (U^[k] s)
  | 0 => rfl
  | k + 1 => by
    rw [Function.iterate_succ_apply', iterate_translate hE d s k, hE,
      Function.iterate_succ_apply']

/-! ## The normal form up to translation, and its finiteness -/

/-- The state translated so that its leftmost support cell sits at `0`; `0` at the zero state. -/
private noncomputable def normalForm (s : ℤ →₀ ZMod 2) : ℤ →₀ ZMod 2 :=
  if h : s.support.Nonempty then τ (-(s.support.min' h)) s else 0

private theorem exists_translate_normalForm (s : ℤ →₀ ZMod 2) :
    ∃ m : ℤ, s = τ m (normalForm s) := by
  by_cases h : s.support.Nonempty
  · refine ⟨s.support.min' h, ?_⟩
    rw [normalForm, dite_eq_left h, translate_translate, add_neg_cancel, translate_zero]
  · have hs : s = 0 := Finsupp.support_eq_empty.mp (Finset.not_nonempty_iff_eq_empty.mp h)
    refine ⟨0, ?_⟩
    rw [normalForm, dite_eq_right h, translate_zero, hs]

private theorem normalForm_mem_regionStates {s : ℤ →₀ ZMod 2} {D : ℕ} (hD : diam s ≤ D) :
    normalForm s ∈ regionStates D := by
  by_cases h : s.support.Nonempty
  · rw [normalForm, dite_eq_left h]
    intro x hx
    simp only [translate_support, Finset.mem_image] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    have h1 := Finset.min'_le s.support y hy
    have h2 := Finset.le_max' s.support y hy
    have h3 := diam_eq' h
    omega
  · rw [normalForm, dite_eq_right h]
    intro x hx
    simp at hx

/-- The configurations supported on `n` cells form a finite set. -/
private theorem finite_regionStates (n : ℕ) : (regionStates n).Finite := by
  have h : (regionStates n).encard = ((2 ^ n : ℕ) : ℕ∞) := by
    rw [card_regionStates]; push_cast; rfl
  exact Set.finite_of_encard_eq_coe h

/-! ## Recurrence with drift -/

/-- **The recurrence**: along an orbit of bounded diameter two stages have the same pattern up to
translation, so a later stage is an earlier one translated by some `d` (the pigeonhole on the
normal form, which lives in the finite set of configurations on `D` cells). -/
private theorem exists_drift {U : (ℤ →₀ ZMod 2) → (ℤ →₀ ZMod 2)} (s₀ : ℤ →₀ ZMod 2) {D : ℕ}
    (hD : ∀ t, diam (U^[t] s₀) ≤ D) :
    ∃ (t₁ P : ℕ) (d : ℤ), 0 < P ∧ U^[t₁ + P] s₀ = τ d (U^[t₁] s₀) := by
  obtain ⟨a, b, hab, heq⟩ := Set.Finite.exists_lt_map_eq_of_forall_mem
    (f := fun t : ℕ => normalForm (U^[t] s₀)) (fun t => normalForm_mem_regionStates (hD t))
    (finite_regionStates D)
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hab
  obtain ⟨m₁, h₁⟩ := exists_translate_normalForm (U^[a] s₀)
  obtain ⟨m₂, h₂⟩ := exists_translate_normalForm (U^[a + k + 1] s₀)
  refine ⟨a, k + 1, m₂ - m₁, Nat.succ_pos k, ?_⟩
  have heq' : normalForm (U^[a + k + 1] s₀) = normalForm (U^[a] s₀) := heq.symm
  calc U^[a + (k + 1)] s₀
      = τ m₂ (normalForm (U^[a + k + 1] s₀)) := h₂
    _ = τ m₂ (normalForm (U^[a] s₀)) := by rw [heq']
    _ = τ ((m₂ - m₁) + m₁) (normalForm (U^[a] s₀)) := by rw [sub_add_cancel]
    _ = τ (m₂ - m₁) (τ m₁ (normalForm (U^[a] s₀))) :=
        (translate_translate _ _ _).symm
    _ = τ (m₂ - m₁) (U^[a] s₀) := by rw [← h₁]

/-- **The drift accumulates**: at a rule commuting with translation, a drift of `d` over `P` steps
from stage `t₁` is a drift of `n d` over `n P` steps from every stage `u ≥ t₁`. -/
private theorem iterate_drift {U : (ℤ →₀ ZMod 2) → (ℤ →₀ ZMod 2)}
    (hE : ∀ (d : ℤ) (s : ℤ →₀ ZMod 2), U (τ d s) = τ d (U s))
    (s₀ : ℤ →₀ ZMod 2) {t₁ P : ℕ} {d : ℤ}
    (hdrift : U^[t₁ + P] s₀ = τ d (U^[t₁] s₀)) :
    ∀ u : ℕ, t₁ ≤ u → ∀ n : ℕ, U^[u + n * P] s₀ = τ ((n : ℤ) * d) (U^[u] s₀) := by
  -- the drift holds at every stage from `t₁` on
  have hstep : ∀ u : ℕ, t₁ ≤ u → U^[u + P] s₀ = τ d (U^[u] s₀) := by
    intro u hu
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hu
    rw [show t₁ + k + P = k + (t₁ + P) by omega, Function.iterate_add_apply, hdrift,
      iterate_translate hE, show t₁ + k = k + t₁ by omega, Function.iterate_add_apply]
  -- and accumulates over `n` periods
  intro u hu n
  induction n with
  | zero => simp [translate_zero]
  | succ n ih =>
    have hu' : t₁ ≤ u + n * P := le_trans hu (Nat.le_add_right _ _)
    rw [show u + (n + 1) * P = (u + n * P) + P by ring, hstep _ hu', ih, translate_translate]
    congr 1
    push_cast
    ring

/-- **Drift makes the column eventually periodic**: at a rule commuting with translation, if a
later stage of the orbit is an earlier one translated by `d`, the column at every cell is
periodic with the stage gap as period when `d = 0` and eventually constant `0` otherwise. -/
private theorem eventuallyPeriodic_of_drift {U : (ℤ →₀ ZMod 2) → (ℤ →₀ ZMod 2)}
    (hE : ∀ (d : ℤ) (s : ℤ →₀ ZMod 2), U (τ d s) = τ d (U s))
    (s₀ : ℤ →₀ ZMod 2) (i : ℤ) {t₁ P : ℕ} {d : ℤ} (hP : 0 < P)
    (hdrift : U^[t₁ + P] s₀ = τ d (U^[t₁] s₀)) :
    GrowingComposite.EventuallyPeriodic (observedColumn U s₀ i) := by
  have hiter := iterate_drift hE s₀ hdrift
  have hstep : ∀ u : ℕ, t₁ ≤ u → U^[u + P] s₀ = τ d (U^[u] s₀) := by
    intro u hu
    simpa using hiter u hu 1
  by_cases hd : d = 0
  · subst hd
    refine ⟨P, t₁, hP, fun u hu => ?_⟩
    change (U^[u + P] s₀) i = (U^[u] s₀) i
    rw [hstep u hu, translate_zero]
  · -- the finitely many phases `t₁ + k`, `k < P`, are supported in one window
    obtain ⟨B, hB⟩ : ∃ B : ℕ, ∀ k, k < P → ∀ x : ℤ, (U^[t₁ + k] s₀) x ≠ 0 → x.natAbs ≤ B := by
      refine ⟨(Finset.range P).sup (fun k => (U^[t₁ + k] s₀).support.sup Int.natAbs), ?_⟩
      intro k hk x hx
      have hx' : x ∈ (U^[t₁ + k] s₀).support := Finsupp.mem_support_iff.mpr hx
      exact (Finset.le_sup (f := Int.natAbs) hx').trans
        (Finset.le_sup (f := fun k => (U^[t₁ + k] s₀).support.sup Int.natAbs)
          (Finset.mem_range.mpr hk))
    obtain ⟨n₀, hn₀⟩ : ∃ n₀ : ℕ, n₀ = B + i.natAbs + 1 := ⟨_, rfl⟩
    have hd' : 1 ≤ d.natAbs := Int.natAbs_pos.mpr hd
    have hzero : ∀ u : ℕ, t₁ + n₀ * P ≤ u → (U^[u] s₀) i = 0 := by
      intro u hu
      obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hu
      have hdm := Nat.div_add_mod' r P
      have hk : r % P < P := Nat.mod_lt r hP
      have hu_eq : t₁ + n₀ * P + r = (t₁ + r % P) + (n₀ + r / P) * P := by
        rw [Nat.add_mul]
        omega
      rw [hu_eq, hiter (t₁ + r % P) (Nat.le_add_right _ _) (n₀ + r / P), translate_apply_sub]
      by_contra hne
      have hb := hB (r % P) hk _ hne
      obtain ⟨N', hN'⟩ : ∃ N' : ℕ, N' = n₀ + r / P := ⟨_, rfl⟩
      rw [← hN'] at hb
      have h1 : ((N' : ℤ) * d).natAbs = N' * d.natAbs := by
        rw [Int.natAbs_mul, Int.natAbs_natCast]
      have h2 : N' ≤ ((N' : ℤ) * d).natAbs := by
        rw [h1]
        exact Nat.le_mul_of_pos_right _ hd'
      have h3 : ((N' : ℤ) * d).natAbs ≤ i.natAbs + (i - (N' : ℤ) * d).natAbs := by
        have := Int.natAbs_sub_le i (i - (N' : ℤ) * d)
        rwa [sub_sub_cancel] at this
      have h4 : N' ≤ i.natAbs + B := h2.trans (h3.trans (Nat.add_le_add_left hb _))
      have h5 : n₀ ≤ N' := by rw [hN']; exact Nat.le_add_right _ _
      omega
    refine ⟨1, t₁ + n₀ * P, one_pos, fun u hu => ?_⟩
    change (U^[u + 1] s₀) i = (U^[u] s₀) i
    rw [hzero u hu, hzero (u + 1) (by omega)]

/-! ## The theorems -/

/-- At a quiescent table rule the diameter along an orbit that never grows is bounded, hence the
column is eventually periodic. -/
private theorem eventuallyPeriodic_of_orbit_diam_le (f : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2)
    (hq : f 0 0 0 = 0) (s₀ : ℤ →₀ ZMod 2) (i : ℤ)
    (hO : ∀ t : ℕ, diam ((tableRule f hq)^[t + 1] s₀) ≤ diam ((tableRule f hq)^[t] s₀)) :
    GrowingComposite.EventuallyPeriodic (observedColumn (tableRule f hq) s₀ i) := by
  have hmono : ∀ t : ℕ, diam ((tableRule f hq)^[t] s₀) ≤ diam s₀ := by
    intro t
    induction t with
    | zero => exact le_rfl
    | succ j ih => exact (hO j).trans ih
  obtain ⟨t₁, P, d, hP, hdrift⟩ := exists_drift s₀ hmono
  exact eventuallyPeriodic_of_drift (fun d s => tableRule_translate f hq d s) s₀ i hP hdrift

/-- At a table rule whose diameter never grows, every observed column is eventually periodic:
the pattern up to translation ranges over a finite set, so it recurs, and a recurrence with drift
`d` per period `P` makes the column periodic with period `P` when `d = 0` and eventually
constant `0` otherwise. -/
theorem eventuallyPeriodic_observedColumn_of_diam_le (f : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2)
    (hq : f 0 0 0 = 0) (hU : ∀ s, diam (tableRule f hq s) ≤ diam s)
    (s₀ : ℤ →₀ ZMod 2) (i : ℤ) :
    GrowingComposite.EventuallyPeriodic (observedColumn (tableRule f hq) s₀ i) :=
  eventuallyPeriodic_of_orbit_diam_le f hq s₀ i
    (fun t => by rw [Function.iterate_succ_apply']; exact hU _)

/-- At every table of the zero class the diameter never grows: the three diameter lemmas of
`EndpointClasses`, one per clause. -/
private theorem diam_tableRule_le_of_zeroByEndpoints (f : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2)
    (hq : f 0 0 0 = 0) (hf : ZeroByEndpoints f) : ∀ s, diam (tableRule f hq s) ≤ diam s := by
  rcases hf with h | h | h
  · exact diam_tableRule_le_of_noTap h.1 h.2
  · exact diam_tableRule_le_of_leftTap_rightDies h.1 h.2.1 h.2.2.1 h.2.2.2
  · exact diam_tableRule_le_of_rightTap_leftDies h.1 h.2.1 h.2.2.1 h.2.2.2

/-- **The corollary at the zero class**: at every quiescent table meeting `ZeroByEndpoints` — no tap
on either side, or one tap with the other endpoint always dying — every observed column is
eventually periodic ([Guests] §7 Proposition 7.24). -/
theorem eventuallyPeriodic_observedColumn_of_zeroByEndpoints
    (f : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2) (hq : f 0 0 0 = 0) (hf : ZeroByEndpoints f)
    (s₀ : ℤ →₀ ZMod 2) (i : ℤ) :
    GrowingComposite.EventuallyPeriodic (observedColumn (tableRule f hq) s₀ i) :=
  eventuallyPeriodic_observedColumn_of_diam_le f hq
    (diam_tableRule_le_of_zeroByEndpoints f hq hf) s₀ i

/-- **The contrapositive along the orbit of the seed**: an observed column that is not eventually
periodic forces the diameter to grow at some stage of the orbit of `s₀` itself — the observer's
unending repairs are paid for by the host's accretion. -/
theorem exists_diam_lt_iterate_of_not_eventuallyPeriodic
    (f : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2) (hq : f 0 0 0 = 0) (s₀ : ℤ →₀ ZMod 2) (i : ℤ)
    (h : ¬ GrowingComposite.EventuallyPeriodic (observedColumn (tableRule f hq) s₀ i)) :
    ∃ t : ℕ, diam ((tableRule f hq)^[t] s₀) < diam ((tableRule f hq)^[t + 1] s₀) := by
  by_contra hcon
  push Not at hcon
  exact h (eventuallyPeriodic_of_orbit_diam_le f hq s₀ i hcon)

/-- A cell observation that is not eventually periodic forces the diameter to grow along the
orbit somewhere: the observer's unending repairs are paid for by the host's accretion. -/
theorem exists_diam_lt_of_not_eventuallyPeriodic
    (f : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2) (hq : f 0 0 0 = 0) (s₀ : ℤ →₀ ZMod 2) (i : ℤ)
    (h : ¬ GrowingComposite.EventuallyPeriodic (observedColumn (tableRule f hq) s₀ i)) :
    ∃ s, diam s < diam (tableRule f hq s) := by
  obtain ⟨t, ht⟩ := exists_diam_lt_iterate_of_not_eventuallyPeriodic f hq s₀ i h
  exact ⟨_, by rwa [← Function.iterate_succ_apply' (tableRule f hq) t s₀]⟩

/-! ## The rational ray -/

/-- **The rational ray**: the value at `e + ⌊p t / q⌋` at step `t`; at `p = 0` it is the observed
column, and `DrivenColumns.observedRay` at velocity `1` is its case `p = q = 1`. -/
def observedRationalRay (U : (ℤ →₀ ZMod 2) → (ℤ →₀ ZMod 2)) (s₀ : ℤ →₀ ZMod 2) (p q : ℕ)
    (e : ℤ) : ℕ → ZMod 2 :=
  fun t => (U^[t] s₀) (e + ((p * t / q : ℕ) : ℤ))

/-- **Speed zero is the observed column** ([Guests] §7 Proposition 7.28, row GV-40). -/
theorem observedRationalRay_zero (U : (ℤ →₀ ZMod 2) → (ℤ →₀ ZMod 2)) (s₀ : ℤ →₀ ZMod 2)
    (q : ℕ) (e : ℤ) : observedRationalRay U s₀ 0 q e = observedColumn U s₀ e := by
  funext t
  simp [observedRationalRay, observedColumn]

/-- **The ray sampled every `q P` steps**: under a drift of `d` per `P` steps from stage `t₁`, the
ray's value at `u + n q P` is the stage-`u` state read `n (p P − q d)` cells past the ray's
stage-`u` position. -/
private theorem observedRationalRay_sample {U : (ℤ →₀ ZMod 2) → (ℤ →₀ ZMod 2)}
    (hE : ∀ (d : ℤ) (s : ℤ →₀ ZMod 2), U (τ d s) = τ d (U s))
    (s₀ : ℤ →₀ ZMod 2) {t₁ P : ℕ} {d : ℤ}
    (hdrift : U^[t₁ + P] s₀ = τ d (U^[t₁] s₀)) (p q : ℕ) (hq0 : 0 < q) (e : ℤ)
    (u : ℕ) (hu : t₁ ≤ u) (n : ℕ) :
    observedRationalRay U s₀ p q e (u + n * (q * P)) =
      (U^[u] s₀) (e + ((p * u / q : ℕ) : ℤ) + (n : ℤ) * ((p : ℤ) * P - (q : ℤ) * d)) := by
  have hdiv : p * (u + n * (q * P)) / q = p * u / q + n * p * P := by
    rw [show p * (u + n * (q * P)) = p * u + (n * p * P) * q by ring,
      Nat.add_mul_div_right _ _ hq0]
  unfold observedRationalRay
  rw [hdiv, show u + n * (q * P) = u + (n * q) * P by ring,
    iterate_drift hE s₀ hdrift u hu (n * q), translate_apply_sub]
  congr 1
  push_cast
  ring

/-- **A drift makes every rational ray eventually periodic**: sampled every `q P` steps the ray's
position relative to the pattern changes by `p P − q d` cells, so the ray is periodic with period
`q P` from stage `t₁` when that is zero, and otherwise leaves the finitely many phases' supports
for good and is eventually constant `0`. -/
private theorem eventuallyPeriodic_ray_of_drift {U : (ℤ →₀ ZMod 2) → (ℤ →₀ ZMod 2)}
    (hE : ∀ (d : ℤ) (s : ℤ →₀ ZMod 2), U (τ d s) = τ d (U s))
    (s₀ : ℤ →₀ ZMod 2) (p q : ℕ) (hq0 : 0 < q) (e : ℤ) {t₁ P : ℕ} {d : ℤ} (hP : 0 < P)
    (hdrift : U^[t₁ + P] s₀ = τ d (U^[t₁] s₀)) :
    GrowingComposite.EventuallyPeriodic (observedRationalRay U s₀ p q e) := by
  have hsample := observedRationalRay_sample hE s₀ hdrift p q hq0 e
  have hQ : 0 < q * P := Nat.mul_pos hq0 hP
  by_cases hδ : (p : ℤ) * P - (q : ℤ) * d = 0
  · refine ⟨q * P, t₁, hQ, fun u hu => ?_⟩
    have h := hsample u hu 1
    rw [one_mul, hδ, mul_zero, add_zero] at h
    exact h
  · -- the finitely many phases `t₁ + r`, `r < q P`, are supported in one window
    obtain ⟨B, hB⟩ : ∃ B : ℕ, ∀ r, r < q * P → ∀ x : ℤ, (U^[t₁ + r] s₀) x ≠ 0 → x.natAbs ≤ B := by
      refine ⟨(Finset.range (q * P)).sup (fun r => (U^[t₁ + r] s₀).support.sup Int.natAbs), ?_⟩
      intro r hr x hx
      have hx' : x ∈ (U^[t₁ + r] s₀).support := Finsupp.mem_support_iff.mpr hx
      exact (Finset.le_sup (f := Int.natAbs) hx').trans
        (Finset.le_sup (f := fun r => (U^[t₁ + r] s₀).support.sup Int.natAbs)
          (Finset.mem_range.mpr hr))
    -- and the ray's position at those phases is bounded as well
    obtain ⟨C, hC⟩ : ∃ C : ℕ, C = p * (t₁ + q * P) := ⟨_, rfl⟩
    have hX : ∀ r, r < q * P →
        (e + ((p * (t₁ + r) / q : ℕ) : ℤ)).natAbs ≤ e.natAbs + C := by
      intro r hr
      calc (e + ((p * (t₁ + r) / q : ℕ) : ℤ)).natAbs
          ≤ e.natAbs + ((p * (t₁ + r) / q : ℕ) : ℤ).natAbs := Int.natAbs_add_le _ _
        _ = e.natAbs + p * (t₁ + r) / q := by rw [Int.natAbs_natCast]
        _ ≤ e.natAbs + C := by
          have h1 : p * (t₁ + r) / q ≤ p * (t₁ + r) := Nat.div_le_self _ _
          have h2 : p * (t₁ + r) ≤ p * (t₁ + q * P) := Nat.mul_le_mul_left _ (by omega)
          omega
    obtain ⟨n₀, hn₀⟩ : ∃ n₀ : ℕ, n₀ = B + e.natAbs + C + 1 := ⟨_, rfl⟩
    have hδ' : 1 ≤ ((p : ℤ) * P - (q : ℤ) * d).natAbs := Int.natAbs_pos.mpr hδ
    have hzero : ∀ u : ℕ, t₁ + n₀ * (q * P) ≤ u → observedRationalRay U s₀ p q e u = 0 := by
      intro u hu
      obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hu
      have hdm := Nat.div_add_mod' r (q * P)
      have hr : r % (q * P) < q * P := Nat.mod_lt r hQ
      have hu_eq : t₁ + n₀ * (q * P) + r =
          (t₁ + r % (q * P)) + (n₀ + r / (q * P)) * (q * P) := by
        rw [Nat.add_mul]
        omega
      rw [hu_eq, hsample (t₁ + r % (q * P)) (Nat.le_add_right _ _) (n₀ + r / (q * P))]
      by_contra hne
      have hb := hB (r % (q * P)) hr _ hne
      have hx := hX (r % (q * P)) hr
      obtain ⟨N', hN'⟩ : ∃ N' : ℕ, N' = n₀ + r / (q * P) := ⟨_, rfl⟩
      obtain ⟨X, hXd⟩ : ∃ X : ℤ, X = e + ((p * (t₁ + r % (q * P)) / q : ℕ) : ℤ) := ⟨_, rfl⟩
      obtain ⟨δ, hδd⟩ : ∃ δ : ℤ, δ = (p : ℤ) * P - (q : ℤ) * d := ⟨_, rfl⟩
      rw [← hN', ← hXd, ← hδd] at hb
      rw [← hXd] at hx
      rw [← hδd] at hδ'
      have h1 : ((N' : ℤ) * δ).natAbs = N' * δ.natAbs := by
        rw [Int.natAbs_mul, Int.natAbs_natCast]
      have h2 : N' ≤ ((N' : ℤ) * δ).natAbs := by
        rw [h1]
        exact Nat.le_mul_of_pos_right _ hδ'
      have h3 : ((N' : ℤ) * δ).natAbs ≤ (X + (N' : ℤ) * δ).natAbs + X.natAbs := by
        have := Int.natAbs_sub_le (X + (N' : ℤ) * δ) X
        rwa [add_sub_cancel_left] at this
      have h5 : n₀ ≤ N' := by rw [hN']; exact Nat.le_add_right _ _
      omega
    refine ⟨1, t₁ + n₀ * (q * P), one_pos, fun u hu => ?_⟩
    rw [hzero u hu, hzero (u + 1) (by omega)]

/-- **Every rational ray at an orbit whose diameter never rises is eventually periodic.** The orbit
repeats up to a translation `d` every `P` steps from some step on; sampled every `q P` steps the
ray's position relative to the pattern changes by `p P − q d` cells, so the ray reads one relative
cell for ever when that is zero and leaves the pattern for good otherwise ([Guests] §7 Proposition
7.28, row GV-40, at the ray of speed `p / q` in place of the column). -/
theorem eventuallyPeriodic_observedRationalRay_of_diam_le (f : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2)
    (hq : f 0 0 0 = 0) (hU : ∀ s, diam (tableRule f hq s) ≤ diam s) (s₀ : ℤ →₀ ZMod 2)
    (p q : ℕ) (hq0 : 0 < q) (e : ℤ) :
    GrowingComposite.EventuallyPeriodic (observedRationalRay (tableRule f hq) s₀ p q e) := by
  have hmono : ∀ t : ℕ, diam ((tableRule f hq)^[t] s₀) ≤ diam s₀ := by
    intro t
    induction t with
    | zero => exact le_rfl
    | succ j ih => rw [Function.iterate_succ_apply']; exact (hU _).trans ih
  obtain ⟨t₁, P, d, hP, hdrift⟩ := exists_drift s₀ hmono
  exact eventuallyPeriodic_ray_of_drift (fun d s => tableRule_translate f hq d s) s₀ p q hq0 e
    hP hdrift

/-- **The rational ray's corollary at the zero class**: at every quiescent table meeting
`ZeroByEndpoints`, every rational ray from every seed is eventually periodic
([Guests] §7 Proposition 7.28, row GV-40). -/
theorem eventuallyPeriodic_observedRationalRay_of_zeroByEndpoints
    (f : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2) (hq : f 0 0 0 = 0) (hf : ZeroByEndpoints f)
    (s₀ : ℤ →₀ ZMod 2) (p q : ℕ) (hq0 : 0 < q) (e : ℤ) :
    GrowingComposite.EventuallyPeriodic (observedRationalRay (tableRule f hq) s₀ p q e) :=
  eventuallyPeriodic_observedRationalRay_of_diam_le f hq
    (diam_tableRule_le_of_zeroByEndpoints f hq hf) s₀ p q hq0 e

/-- **All three hypotheses of the rational ray's theorem are met at once, and the conclusion holds
there**: the shift `f170`, quiescent, with its diameter never rising by `zeroByEndpoints_f170`,
the single seed, speed `1/2` and start `0`. -/
theorem eventuallyPeriodic_observedRationalRay_of_diam_le_nonvacuous :
    f170 0 0 0 = 0 ∧ (∀ s, diam (tableRule f170 hq170 s) ≤ diam s) ∧ 0 < 2 ∧
      GrowingComposite.EventuallyPeriodic
        (observedRationalRay (tableRule f170 hq170) (Finsupp.single 0 1) 1 2 0) :=
  ⟨hq170, diam_tableRule_le_of_zeroByEndpoints f170 hq170 zeroByEndpoints_f170, by norm_num,
    eventuallyPeriodic_observedRationalRay_of_diam_le f170 hq170
      (diam_tableRule_le_of_zeroByEndpoints f170 hq170 zeroByEndpoints_f170) _ 1 2
      (by norm_num) 0⟩

/-! ## The witness and the guard -/

/-- The column of the shift `f170` (each cell reads its right neighbour) from the single seed,
read at the center: `1` at stage `0` and `0` at every later stage. -/
theorem observedColumn_f170_single :
    observedColumn (tableRule f170 hq170) (Finsupp.single (0 : ℤ) (1 : ZMod 2)) 0 =
      fun t => if t = 0 then 1 else 0 := by
  have hit : ∀ (t : ℕ) (s : ℤ →₀ ZMod 2) (j : ℤ),
      ((tableRule f170 hq170)^[t] s) j = s (j + t) := by
    intro t
    induction t with
    | zero => intro s j; simp
    | succ t ih =>
      intro s j
      rw [Function.iterate_succ_apply, ih, tableRule_apply]
      change s (j + (t : ℤ) + 1) = s (j + ((t + 1 : ℕ) : ℤ))
      rw [Nat.cast_succ, add_assoc]
  funext t
  change ((tableRule f170 hq170)^[t] (Finsupp.single (0 : ℤ) (1 : ZMod 2))) 0 = _
  rw [hit, Finsupp.single_apply]
  by_cases ht : t = 0
  · simp [ht]
  · have h0 : ¬ ((0 : ℤ) = (t : ℤ)) := by omega
    simp [ht, h0]

theorem hq90 : f90 0 0 0 = 0 := by decide

/-- Every iterate from the single seed is symmetric under `i ↦ -i`: `f90`'s table sums the two
neighbours and drops the center, and a seed that is itself symmetric keeps that symmetry through
every step. -/
private theorem tableRule_f90_single_neg (t : ℕ) (i : ℤ) :
    ((tableRule f90 hq90)^[t] (Finsupp.single (0 : ℤ) (1 : ZMod 2))) (-i)
      = ((tableRule f90 hq90)^[t] (Finsupp.single (0 : ℤ) (1 : ZMod 2))) i := by
  induction t generalizing i with
  | zero =>
      simp only [Function.iterate_zero, id_eq, Finsupp.single_apply]
      split_ifs with h1 h2 h2 <;> first | rfl | (exfalso; omega)
  | succ t ih =>
      rw [Function.iterate_succ_apply', tableRule_apply, tableRule_apply, f90, f90,
        show -i - 1 = -(i + 1) by ring, show -i + 1 = -(i - 1) by ring, ih (i + 1), ih (i - 1)]
      ring

/-- **The column at an accreting table, from the single seed** ([Guests] §7 Remark 7.25, row
GV-35). `f90`'s table sums the two neighbours and drops the center, so past stage `0` the reading
at the seeded cell is the sum of
two neighbours the seed's own symmetry keeps equal (`tableRule_f90_single_neg`), and that sum
vanishes in `ZMod 2`: the center reads `1` at stage `0` and `0` at every stage after, exactly as at
the zero-class shift `f170` (`observedColumn_f170_single`) despite `f90` accreting rather than
staying quiescent. -/
theorem observedColumn_f90_single :
    observedColumn (tableRule f90 hq90) (Finsupp.single (0 : ℤ) (1 : ZMod 2)) 0 =
      fun t => if t = 0 then 1 else 0 := by
  have hzero : ∀ x : ZMod 2, x + x = 0 := by decide
  funext t
  cases t with
  | zero =>
      change ((tableRule f90 hq90)^[0] (Finsupp.single (0 : ℤ) (1 : ZMod 2))) 0 = _
      simp
  | succ t =>
      change ((tableRule f90 hq90)^[t + 1] (Finsupp.single (0 : ℤ) (1 : ZMod 2))) 0 = _
      rw [Function.iterate_succ_apply', tableRule_apply, f90,
        show (0 : ℤ) - 1 = -1 by ring, show (0 : ℤ) + 1 = 1 by ring,
        ← tableRule_f90_single_neg t 1]
      simp only [Nat.succ_ne_zero, reduceIte]
      exact hzero _

/-- **The witness for [Guests] §7 Remark 7.25's "the converse fails"** (row GV-35): an accreting
table whose single-seed center column is nonetheless eventually periodic — the general implication
runs only from a bounded diameter to eventual periodicity, and `f90` shows periodicity does not
force the diameter back down. Packaged in the same existential shape as
`eventuallyPeriodic_observedColumn_of_zeroByEndpoints_nonvacuous`, with `AccretesByEndpoints` in
place of `ZeroByEndpoints`. -/
theorem observedColumn_f90_eventually_periodic_witness :
    ∃ (f : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2) (hq : f 0 0 0 = 0), AccretesByEndpoints f ∧
      GrowingComposite.EventuallyPeriodic
        (observedColumn (tableRule f hq) (Finsupp.single 0 1) 0) := by
  refine ⟨f90, hq90, accretesByEndpoints_f90, 1, 1, one_pos, fun u hu => ?_⟩
  rw [observedColumn_f90_single]
  have h1 : u ≠ 0 := by omega
  simp [h1]

/-- **Both hypotheses of the zero-class corollary are met at once**: the shift `f170`, quiescent and
zero-class, whose single-seed column at the center is `1` then `0` forever
(`observedColumn_f170_single`). -/
theorem eventuallyPeriodic_observedColumn_of_zeroByEndpoints_nonvacuous :
    ∃ (f : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2) (hq : f 0 0 0 = 0), ZeroByEndpoints f ∧
      GrowingComposite.EventuallyPeriodic
        (observedColumn (tableRule f hq) (Finsupp.single 0 1) 0) :=
  ⟨f170, hq170, zeroByEndpoints_f170,
    eventuallyPeriodic_observedColumn_of_zeroByEndpoints f170 hq170 zeroByEndpoints_f170 _ _⟩

/-- **Guard: the diameter hypothesis is load-bearing.** At rule 30 the single seed has diameter `1`
and its image has diameter `3`, so `∀ s, diam (tableRule f30 hq30 s) ≤ diam s` fails there and
`eventuallyPeriodic_observedColumn_of_diam_le` does not apply. Nothing is claimed about the
column itself. -/
theorem diam_lt_tableRule_f30_single :
    diam (Finsupp.single (0 : ℤ) (1 : ZMod 2)) <
      diam (tableRule f30 hq30 (Finsupp.single (0 : ℤ) (1 : ZMod 2))) := by
  have hd1 : diam (Finsupp.single (0 : ℤ) (1 : ZMod 2)) = 1 := by simp [diam]
  have hm1 : (-1 : ℤ) ∈ (tableRule f30 hq30 (Finsupp.single (0 : ℤ) (1 : ZMod 2))).support := by
    rw [Finsupp.mem_support_iff, tableRule_apply]
    simp [f30]
  have hp1 : (1 : ℤ) ∈ (tableRule f30 hq30 (Finsupp.single (0 : ℤ) (1 : ZMod 2))).support := by
    rw [Finsupp.mem_support_iff, tableRule_apply]
    simp [f30]
  have hne : (tableRule f30 hq30 (Finsupp.single (0 : ℤ) (1 : ZMod 2))).support.Nonempty :=
    ⟨1, hp1⟩
  have hmax := Finset.le_max' _ 1 hp1
  have hmin := Finset.min'_le _ (-1) hm1
  rw [hd1, diam_eq' hne]
  omega

end ObservedColumn

/-! ## Axiom audit

Every public theorem above is `#print axioms`-clean on the standard triple, and the guards below
make that build-enforced. -/

set_option linter.style.longLine false

/-- info: 'ObservedColumn.eventuallyPeriodic_observedColumn_of_diam_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ObservedColumn.eventuallyPeriodic_observedColumn_of_diam_le

/-- info: 'ObservedColumn.eventuallyPeriodic_observedColumn_of_zeroByEndpoints' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ObservedColumn.eventuallyPeriodic_observedColumn_of_zeroByEndpoints

/-- info: 'ObservedColumn.exists_diam_lt_iterate_of_not_eventuallyPeriodic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ObservedColumn.exists_diam_lt_iterate_of_not_eventuallyPeriodic

/-- info: 'ObservedColumn.exists_diam_lt_of_not_eventuallyPeriodic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ObservedColumn.exists_diam_lt_of_not_eventuallyPeriodic

/-- info: 'ObservedColumn.observedColumn_f170_single' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ObservedColumn.observedColumn_f170_single

/-- info: 'ObservedColumn.hq90' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ObservedColumn.hq90

/-- info: 'ObservedColumn.observedColumn_f90_single' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ObservedColumn.observedColumn_f90_single

/-- info: 'ObservedColumn.observedColumn_f90_eventually_periodic_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ObservedColumn.observedColumn_f90_eventually_periodic_witness

/-- info: 'ObservedColumn.eventuallyPeriodic_observedColumn_of_zeroByEndpoints_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ObservedColumn.eventuallyPeriodic_observedColumn_of_zeroByEndpoints_nonvacuous

/-- info: 'ObservedColumn.diam_lt_tableRule_f30_single' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ObservedColumn.diam_lt_tableRule_f30_single

/-- info: 'ObservedColumn.observedRationalRay_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ObservedColumn.observedRationalRay_zero

/-- info: 'ObservedColumn.eventuallyPeriodic_observedRationalRay_of_diam_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ObservedColumn.eventuallyPeriodic_observedRationalRay_of_diam_le

/-- info: 'ObservedColumn.eventuallyPeriodic_observedRationalRay_of_zeroByEndpoints' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ObservedColumn.eventuallyPeriodic_observedRationalRay_of_zeroByEndpoints

/-- info: 'ObservedColumn.eventuallyPeriodic_observedRationalRay_of_diam_le_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ObservedColumn.eventuallyPeriodic_observedRationalRay_of_diam_le_nonvacuous
