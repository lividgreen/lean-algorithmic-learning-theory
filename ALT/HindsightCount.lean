/-
Copyright (c) 2026 Mykola Palamarchuk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mykola Palamarchuk
-/
module

public import ALT.DrivenColumns
public import ALT.FlooredMixture

-- Formal-check file, not Mathlib-destined: opt out of the house-style header linter.
set_option linter.style.header false

/-!
# The hindsight count: a law on the last `k` readings, and its bound

`DrivenColumns.lean` proves a finite-valued sequence driven by an eventually periodic input
eventually periodic, and exhibits a column that is not. `FlooredMixture.lean` bounds the surprise
count of a floored mixture against one reference candidate's own miss count. This file connects the
two currencies: a sequence is eventually periodic exactly when SOME fixed law on its last `k`
readings answers correctly from some point on, and exactly when the fewest misses any such law
makes stays bounded as the horizon grows — and a bound on one reference law's misses, via that
connection, bounds the surprise count of a floored mixture run over a whole FAMILY of such laws.

Two conditions are minted here and named for use in every docstring. A sequence is **eventually
exact at memory `k`** when some law on its last `k` readings answers the next reading from some
step on (`EventuallyExact`). The **miss matrix of a law family** is the Boolean matrix recording
which law of a finite family misses at which step (`lawMissMatrix`).

## Main results

* `EventuallyExact` — the memory-`k` law condition. `eventuallyExact_of_eventuallyPeriodic` reads
  it off eventual periodicity directly, at the period as memory;
  `eventuallyPeriodic_of_eventuallyExact` is the converse, over a finite alphabet, by casting the
  law's own driven register (`shiftAppendStep`) as an instance of
  `DrivenColumns.eventuallyPeriodic_of_driven`; `exists_eventuallyExact_iff_eventuallyPeriodic`
  folds the two directions into one equivalence, and
  `eventuallyExact_nat_id_not_eventuallyPeriodic` guards the finite-alphabet hypothesis: the
  naturals' own identity is exact at memory `1` yet never eventually periodic.
* `lawMisses`, `hindsightCount` — how often a fixed law misses before a horizon, and the fewest
  misses any law on the given memory makes. `hindsightCount_bounded_iff_eventuallyExact` and
  `exists_hindsightCount_bounded_iff_eventuallyPeriodic` are the two count-currency counterparts of
  the law-currency facts above, the second existentially over the memory.
* `exists_eventuallyExact_observedWindow_iff` / `exists_hindsightCount_bounded_observedWindow_iff`
  — both currencies of `DrivenColumns.eventuallyPeriodic_observedWindow_iff`'s window form, read at
  a table rule's observed window: the width-`(m + 1)` window meets the condition iff its two
  boundary columns each do, at their own (separate) memories.
* `lawMissMatrix` — the miss matrix of a finite law family.
  `floorSurprise_card_mul_le_of_lawMisses_le` instantiates
  `WeightedFiber.floorSurprise_card_mul_le_missCount` at that matrix: a bound on one reference
  law's own misses bounds the floored mixture's surprise count over the whole family, free of the
  family's size beyond the constant already in the imported bound.
  `floorSurprise_card_mul_le_of_lawMisses_le_nonvacuous` meets both of that instantiation's
  hypotheses at once, at a threshold below `1` so the surprise set is not empty by vacuity.
* `eventuallyExact_observedColumn_f90_single`,
  `not_exists_eventuallyExact_observedColumn_f90_single_one`,
  `hindsightCount_observedColumn_f90_single_one_unbounded` — the guard pair, both currencies, at the
  column `DrivenColumns.not_eventuallyPeriodic_observedColumn_f90_single_one` already settles: the
  center column is eventually exact at memory `0`, and the cell beside it is eventually exact at NO
  memory, with an unbounded hindsight count at every memory.
* `exists_hindsightCount_bounded_observedColumn_of_zeroByEndpoints`,
  `exists_hindsightCount_bounded_observedWindow_of_zeroByEndpoints` — the observer's bill against
  the world's growth read at the class level: at every table of the zero class some memory gives
  every cell's count, and every window's, a bound.
  `exists_hindsightCount_bounded_observedColumn_of_zeroByEndpoints_nonvacuous` meets both named
  hypotheses at once at table `170`, and
  `exists_hindsightCount_bounded_observedColumn_zero_class_guard` shows the class hypothesis
  load-bearing: table `90` is in the other class and one cell's count there is unbounded at every
  memory.

## Scope

The two window theorems are registered as `[Guests] §7 Proposition 7.27`, clause (i), row GV-38;
nothing else here is registered against any paper: the class-level corollary is registered against
none, `[Guests] §7 Proposition 7.24` being the class it ranges over and Proposition 7.27 the
count's registration, cited for that reason alone, and it claims nothing at the twenty-eight
tables in neither class; `[Guests] §7 Proposition 7.26` and
`[Inevitability] §6` with row IN-13 are what the rest extends, cited for that reason alone. The two
window theorems are stated at a general table rule `tableRule f hq`, never specialized beyond the
guard pair's own column. `floorSurprise_card_mul_le_of_lawMisses_le` claims nothing about the
family beyond what `WeightedFiber.floorSurprise_card_mul_le_missCount` already claims of its
`missCount` argument; the family structure buys only that the reference law `Ls i₀` may be read off
a FIXED memory shared by every law of the family, not a sharper bound.
-/


@[expose] public section

namespace HindsightCount

open ExtremeTapWidth EndpointClasses
open ObservedColumn (observedColumn hq90)
open DrivenColumns

/-! ## Piece 1: a law on the last `k` readings, and eventual periodicity -/

/-- **A law on the last `k` readings**: some function of the window `x t, …, x (t + k - 1)`
answers `x (t + k)`, from some point on. -/
def EventuallyExact {α : Type*} (k : ℕ) (x : ℕ → α) : Prop :=
  ∃ (L : (Fin k → α) → α) (N : ℕ), ∀ t, N ≤ t → L (fun i => x (t + (i : ℕ))) = x (t + k)

/-- **Eventual periodicity gives a law**: the law that answers the oldest reading its own period
holds, at the period as memory. -/
theorem eventuallyExact_of_eventuallyPeriodic {α : Type*} {x : ℕ → α}
    (hx : GrowingComposite.EventuallyPeriodic x) : ∃ k, EventuallyExact k x := by
  obtain ⟨P, N, hP, hper⟩ := hx
  exact ⟨P, fun w => w ⟨0, hP⟩, N, fun t ht => (hper t ht).symm⟩

/-- **The shift-and-append step**: read one cell further along the window when there is one, and
answer with the law otherwise. -/
private def shiftAppendStep {α : Type*} (k : ℕ) (L : (Fin k → α) → α) :
    (Fin k → α) → (Fin k → α) :=
  fun w j => if hj : (j : ℕ) + 1 < k then w ⟨(j : ℕ) + 1, hj⟩ else L w

/-- **A law gives eventual periodicity**, over a finite alphabet. At `k = 0` the law directly gives
`x` eventually constant. At `k > 0` the block of the last `k` readings is itself driven — over a
one-point input, by `shiftAppendStep` — hence eventually periodic by `eventuallyPeriodic_of_driven`,
and `x` is its `0`-th coordinate. -/
theorem eventuallyPeriodic_of_eventuallyExact {α : Type*} [Finite α] {k : ℕ} {x : ℕ → α}
    (hx : EventuallyExact k x) : GrowingComposite.EventuallyPeriodic x := by
  classical
  obtain ⟨L, N, hL⟩ := hx
  rcases Nat.eq_zero_or_pos k with hk0 | hkpos
  · subst hk0
    refine ⟨1, N, one_pos, fun t ht => ?_⟩
    have hw : (fun i : Fin 0 => x (t + (i : ℕ))) = fun i : Fin 0 => x (t + 1 + (i : ℕ)) :=
      Subsingleton.elim _ _
    have h0 := hL t ht
    have h1 := hL (t + 1) (Nat.le_succ_of_le ht)
    rw [Nat.add_zero] at h0
    rw [Nat.add_zero, ← hw] at h1
    rw [h1] at h0
    exact h0
  · have hstep : ∃ N', ∀ t, N' ≤ t →
        (fun i : Fin k => x (t + 1 + (i : ℕ))) =
          shiftAppendStep k L (fun i : Fin k => x (t + (i : ℕ))) := by
      refine ⟨N, fun t ht => ?_⟩
      funext j
      show x (t + 1 + (j : ℕ)) = shiftAppendStep k L (fun i : Fin k => x (t + (i : ℕ))) j
      unfold shiftAppendStep
      rcases lt_or_ge ((j : ℕ) + 1) k with hj | hj
      · rw [dite_eq_left hj]
        change x (t + 1 + (j : ℕ)) = x (t + ((j : ℕ) + 1))
        congr 1
        omega
      · rw [dite_eq_right (by omega)]
        have hLt := hL t ht
        rw [hLt]
        have hjlt := j.isLt
        congr 1
        omega
    have hu : GrowingComposite.EventuallyPeriodic (fun _ : ℕ => ()) :=
      ⟨1, 0, one_pos, fun _ _ => rfl⟩
    have hblock : GrowingComposite.EventuallyPeriodic
        (fun t : ℕ => (fun i : Fin k => x (t + (i : ℕ)))) := by
      obtain ⟨N', hN'⟩ := hstep
      exact eventuallyPeriodic_of_driven (fun (w : Fin k → α) (_ : Unit) => shiftAppendStep k L w)
        hu ⟨N', fun t ht => hN' t ht⟩
    have h0 : (0 : ℕ) < k := hkpos
    have heq : (fun w : Fin k → α => w ⟨0, h0⟩) ∘
        (fun t : ℕ => (fun i : Fin k => x (t + (i : ℕ)))) = x := by
      funext t
      change x (t + (0 : ℕ)) = x t
      rw [Nat.add_zero]
    have hcomp := eventuallyPeriodic_comp hblock (fun w : Fin k → α => w ⟨0, h0⟩)
    rwa [heq] at hcomp

/-- **The two directions above, as one equivalence.** -/
theorem exists_eventuallyExact_iff_eventuallyPeriodic {α : Type*} [Finite α] (x : ℕ → α) :
    (∃ k, EventuallyExact k x) ↔ GrowingComposite.EventuallyPeriodic x := by
  constructor
  · rintro ⟨k, hk⟩
    exact eventuallyPeriodic_of_eventuallyExact hk
  · intro hx
    exact eventuallyExact_of_eventuallyPeriodic hx

/-- **The finite alphabet is load-bearing** in `eventuallyPeriodic_of_eventuallyExact`: the law
that adds one to its one reading is exact from the start, and the identity on the naturals repeats
nowhere. -/
theorem eventuallyExact_nat_id_not_eventuallyPeriodic :
    EventuallyExact 1 (fun t : ℕ => t) ∧
      ¬ GrowingComposite.EventuallyPeriodic (fun t : ℕ => t) := by
  refine ⟨⟨fun w => w 0 + 1, 0, fun t _ => by simp⟩, ?_⟩
  rintro ⟨P, N, hP, hper⟩
  have h : N + P = N := hper N le_rfl
  omega

/-! ## Piece 2: the hindsight count -/

/-- **How often a fixed law on the last `k` readings misses**, before horizon `T`. -/
noncomputable def lawMisses {α : Type*} [DecidableEq α] (k : ℕ) (L : (Fin k → α) → α)
    (x : ℕ → α) (T : ℕ) : ℕ :=
  ((Finset.range T).filter fun t => L (fun i => x (t + (i : ℕ))) ≠ x (t + k)).card

/-- **The hindsight count**: the fewest misses any law on the last `k` readings makes before `T`. -/
noncomputable def hindsightCount {α : Type*} [DecidableEq α] (k : ℕ) (x : ℕ → α) (T : ℕ) : ℕ :=
  ⨅ L : (Fin k → α) → α, lawMisses k L x T

private theorem lawMisses_succ {α : Type*} [DecidableEq α] (k : ℕ) (L : (Fin k → α) → α)
    (x : ℕ → α) (T : ℕ) :
    lawMisses k L x (T + 1) =
      lawMisses k L x T + (if L (fun i => x (T + (i : ℕ))) ≠ x (T + k) then 1 else 0) := by
  rw [lawMisses, lawMisses, Finset.range_add_one, Finset.filter_insert]
  by_cases h : L (fun i => x (T + (i : ℕ))) ≠ x (T + k)
  · rw [ite_eq_left h, ite_eq_left h, Finset.card_insert_of_notMem (by simp)]
  · rw [ite_eq_right h, ite_eq_right h, Nat.add_zero]

private theorem lawMisses_mono {α : Type*} [DecidableEq α] (k : ℕ) (L : (Fin k → α) → α)
    (x : ℕ → α) : Monotone (lawMisses k L x) :=
  monotone_nat_of_le_succ (fun T => by rw [lawMisses_succ]; omega)

/-- **A monotone `ℕ`-sequence bounded above is eventually constant.** Self-contained, by strong
induction on the bound: if the bound is hit, the sequence is pinned at it from there on; if not,
the tighter bound applies. -/
private theorem exists_eventually_eq_succ_of_monotone_bddAbove :
    ∀ (B : ℕ) (g : ℕ → ℕ), Monotone g → (∀ t, g t ≤ B) → ∃ N, ∀ t, N ≤ t → g (t + 1) = g t := by
  intro B
  induction B with
  | zero =>
      intro g _ hbdd
      refine ⟨0, fun t _ => ?_⟩
      have h1 := hbdd (t + 1)
      have h2 := hbdd t
      omega
  | succ B ih =>
      intro g hmono hbdd
      by_cases hcase : ∃ t0, g t0 = B + 1
      · obtain ⟨t0, ht0⟩ := hcase
        refine ⟨t0, fun t ht => ?_⟩
        have hle1 := hmono ht
        have hle2 := hbdd t
        have hle3 := hbdd (t + 1)
        have hle4 := hmono (show t ≤ t + 1 by omega)
        omega
      · push Not at hcase
        have hbdd' : ∀ t, g t ≤ B := fun t => by
          have h1 := hbdd t
          have h2 := hcase t
          omega
        exact ih g hmono hbdd'

/-- **A bounded hindsight count is a law**: the laws are finitely many, the infimum over a
nonempty finite family in `ℕ` is attained at each `T` (`ciInf_mem`), so one law attains the
infimum at infinitely many `T` (`Finite.exists_infinite_fiber`, the pigeonhole), hence — by
monotonicity — at every `T`; a monotone count bounded above stops rising, and from the last rise on
that law never misses. -/
theorem hindsightCount_bounded_iff_eventuallyExact {α : Type*} [Finite α] [DecidableEq α]
    (k : ℕ) (x : ℕ → α) :
    (∃ B, ∀ T, hindsightCount k x T ≤ B) ↔ EventuallyExact k x := by
  constructor
  · rintro ⟨B, hB⟩
    have : Nonempty α := ⟨x 0⟩
    have hattain : ∀ T, ∃ L, lawMisses k L x T = hindsightCount k x T :=
      fun T => ciInf_mem (fun L => lawMisses k L x T)
    choose choiceL hchoiceL using hattain
    obtain ⟨L, hLfiberTC⟩ := Finite.exists_infinite_fiber choiceL
    have hLfiber : (choiceL ⁻¹' {L}).Infinite := Set.infinite_coe_iff.mp hLfiberTC
    have hbddT : ∀ T, lawMisses k L x T ≤ B := by
      intro T
      obtain ⟨T', hT'mem, hT'gt⟩ := hLfiber.exists_notMem_finset (Finset.range (T + 1))
      have heq : choiceL T' = L := by simpa using hT'mem
      have hTT' : T ≤ T' := by
        simp only [Finset.mem_range, not_lt] at hT'gt
        omega
      calc lawMisses k L x T ≤ lawMisses k L x T' := lawMisses_mono k L x hTT'
        _ = lawMisses k (choiceL T') x T' := by rw [heq]
        _ = hindsightCount k x T' := hchoiceL T'
        _ ≤ B := hB T'
    obtain ⟨N, hN⟩ :=
      exists_eventually_eq_succ_of_monotone_bddAbove B (lawMisses k L x) (lawMisses_mono k L x)
        hbddT
    refine ⟨L, N, fun t ht => ?_⟩
    have heq := hN t ht
    rw [lawMisses_succ] at heq
    by_contra hne
    rw [ite_eq_left hne] at heq
    omega
  · rintro ⟨L, N, hL⟩
    refine ⟨N, fun T => ?_⟩
    have hle : hindsightCount k x T ≤ lawMisses k L x T := ciInf_le' _ L
    have hsub : (Finset.range T).filter (fun t => L (fun i => x (t + (i : ℕ))) ≠ x (t + k))
        ⊆ Finset.range N := by
      intro t ht
      simp only [Finset.mem_filter, Finset.mem_range] at ht
      rw [Finset.mem_range]
      by_contra hc
      push Not at hc
      exact ht.2 (hL t hc)
    have : lawMisses k L x T ≤ N := by
      calc lawMisses k L x T ≤ (Finset.range N).card := Finset.card_le_card hsub
        _ = N := Finset.card_range N
    omega

/-- **The existential count-currency form**: bounded hindsight count at SOME memory, exactly when
eventually periodic. -/
theorem exists_hindsightCount_bounded_iff_eventuallyPeriodic {α : Type*} [Finite α]
    [DecidableEq α] (x : ℕ → α) :
    (∃ k B, ∀ T, hindsightCount k x T ≤ B) ↔ GrowingComposite.EventuallyPeriodic x := by
  constructor
  · rintro ⟨k, B, hB⟩
    exact eventuallyPeriodic_of_eventuallyExact
      ((hindsightCount_bounded_iff_eventuallyExact k x).mp ⟨B, hB⟩)
  · intro hx
    obtain ⟨k, hk⟩ := eventuallyExact_of_eventuallyPeriodic hx
    obtain ⟨B, hB⟩ := (hindsightCount_bounded_iff_eventuallyExact k x).mpr hk
    exact ⟨k, B, hB⟩

/-! ## Piece 3: the window of a table rule -/

/-- **The window's law-currency form**: the width-`(m + 1)` window is eventually exact at SOME
memory iff its two boundary columns each are, at their own (separate) memories — three applications
of the pieces above around `eventuallyPeriodic_observedWindow_iff`. -/
theorem exists_eventuallyExact_observedWindow_iff
    (f : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2) (hq : f 0 0 0 = 0) (s₀ : ℤ →₀ ZMod 2)
    (a : ℤ) (m : ℕ) :
    (∃ k, EventuallyExact k (observedWindow (tableRule f hq) s₀ a (m + 1))) ↔
      (∃ k, EventuallyExact k (observedColumn (tableRule f hq) s₀ a)) ∧
      (∃ k, EventuallyExact k (observedColumn (tableRule f hq) s₀ (a + (m : ℤ)))) := by
  constructor
  · rintro ⟨k, hk⟩
    have hep := eventuallyPeriodic_of_eventuallyExact hk
    rw [eventuallyPeriodic_observedWindow_iff] at hep
    exact ⟨eventuallyExact_of_eventuallyPeriodic hep.1, eventuallyExact_of_eventuallyPeriodic hep.2⟩
  · rintro ⟨⟨k1, hk1⟩, ⟨k2, hk2⟩⟩
    have hep : GrowingComposite.EventuallyPeriodic
        (observedWindow (tableRule f hq) s₀ a (m + 1)) := by
      rw [eventuallyPeriodic_observedWindow_iff]
      exact ⟨eventuallyPeriodic_of_eventuallyExact hk1, eventuallyPeriodic_of_eventuallyExact hk2⟩
    exact eventuallyExact_of_eventuallyPeriodic hep

/-- **The window's count-currency form**, the same fact read through `hindsightCount`: both sides
reduce to `exists_hindsightCount_bounded_iff_eventuallyPeriodic`, and what remains is exactly
`eventuallyPeriodic_observedWindow_iff`. -/
theorem exists_hindsightCount_bounded_observedWindow_iff
    (f : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2) (hq : f 0 0 0 = 0) (s₀ : ℤ →₀ ZMod 2)
    (a : ℤ) (m : ℕ) :
    (∃ k B, ∀ T,
        hindsightCount k (observedWindow (tableRule f hq) s₀ a (m + 1)) T ≤ B) ↔
      (∃ k B, ∀ T, hindsightCount k (observedColumn (tableRule f hq) s₀ a) T ≤ B) ∧
      (∃ k B, ∀ T, hindsightCount k (observedColumn (tableRule f hq) s₀ (a + (m : ℤ))) T ≤ B) := by
  simp only [exists_hindsightCount_bounded_iff_eventuallyPeriodic]
  exact eventuallyPeriodic_observedWindow_iff f hq s₀ a m

/-! ## Piece 4: the bounded-register learner over a law family -/

/-- **The miss matrix of a law family**: which law of a finite family misses at which step. -/
def lawMissMatrix {α : Type*} [DecidableEq α] {C : ℕ} (k : ℕ)
    (Ls : Fin C → (Fin k → α) → α) (x : ℕ → α) : ℕ → Fin C → Bool :=
  fun t i => decide (Ls i (fun j => x (t + (j : ℕ))) ≠ x (t + k))

/-- **The instantiation**: a bound on one reference law's own misses bounds the floored mixture's
surprise count over the whole family — `WeightedFiber.floorSurprise_card_mul_le_missCount` at the
family's miss matrix, with `WeightedFiber.missCount` there identified with `lawMisses` here. The
right side is free of the horizon and of the family beyond the one reference law: that is the
content carried over from the imported bound. -/
theorem floorSurprise_card_mul_le_of_lawMisses_le {α : Type*} [DecidableEq α] {C : ℕ}
    (k : ℕ) (Ls : Fin C → (Fin k → α) → α) (x : ℕ → α) (b : ℕ) (θ : ℚ)
    (hbudget : 2 * ((C : ℚ) - 1) ≤ θ * 2 ^ b) (i₀ : Fin C) {B : ℕ}
    (hB : ∀ T, lawMisses k (Ls i₀) x T ≤ B) (n : ℕ) :
    ((WeightedFiber.floorSurpriseSet (lawMissMatrix k Ls x) b θ n).card : ℚ) * θ
      ≤ 4 * ((C : ℚ) - 1) + 2 * (C : ℚ) * (B : ℚ) := by
  have hmc : WeightedFiber.missCount (lawMissMatrix k Ls x) i₀ n = lawMisses k (Ls i₀) x n := by
    unfold WeightedFiber.missCount lawMisses lawMissMatrix
    simp
  have hbound := WeightedFiber.floorSurprise_card_mul_le_missCount (lawMissMatrix k Ls x) b θ
    hbudget i₀ n
  rw [hmc] at hbound
  refine hbound.trans ?_
  gcongr
  exact_mod_cast hB n

/-- The witness sequence, `true` only at `t = 0`. -/
def nvX : ℕ → Bool := fun t => t == 0

/-- The witness family: two candidates, each the constant "always false" law over an empty
memory. -/
def nvLs : Fin 2 → (Fin 0 → Bool) → Bool := fun _ _ => false

private theorem nvLawMissMatrix_eq (t : ℕ) (i : Fin 2) : lawMissMatrix 0 nvLs nvX t i = nvX t := by
  unfold lawMissMatrix nvLs
  cases nvX t <;> decide

private theorem nv_raw0 (i : Fin 2) :
    WeightedFiber.raw (WeightedFiber.wRun (2 ^ 2) (WeightedFiber.missFit (lawMissMatrix 0 nvLs nvX))
      0) i = 1 := by
  rw [WeightedFiber.wRun_eq_pow_expRun]
  simp [WeightedFiber.expRun]

private theorem nv_wrongMass0 : WeightedFiber.wrongMass (lawMissMatrix 0 nvLs nvX) 2 0 = 1 := by
  unfold WeightedFiber.wrongMass
  simp only [nvLawMissMatrix_eq, nvX, beq_self_eq_true, ite_true, WeightedFiber.toDist, nv_raw0]
  rw [Fin.sum_univ_two]
  norm_num

/-- The smallest instance meeting `floorSurprise_card_mul_le_of_lawMisses_le`'s two hypotheses at
once: two candidates (`nvLs`), memory `0`, the constant "always false" law for each, against the
sequence `true` only at `t = 0` (`nvX`). Both candidates miss at the uniform start, clearing the
threshold `θ = 1/2` there (`floorSurprise_vacuous_at_badW_budget` marks `θ ≥ 1` at this budget as
the zone to stay out of), and the reference law misses at most once, ever. -/
theorem floorSurprise_card_mul_le_of_lawMisses_le_nonvacuous :
    2 * (((2 : ℕ) : ℚ) - 1) ≤ (1 / 2 : ℚ) * 2 ^ (2 : ℕ) ∧
      (∀ T, lawMisses 0 (nvLs 0) nvX T ≤ 1) ∧
      (WeightedFiber.floorSurpriseSet (lawMissMatrix 0 nvLs nvX) 2 (1 / 2 : ℚ) 1).Nonempty := by
  refine ⟨by norm_num, fun T => ?_, 0, ?_⟩
  · have hsub : (Finset.range T).filter (fun t => nvLs 0 (fun j => nvX (t + (j : ℕ))) ≠ nvX (t + 0))
        ⊆ {0} := by
      intro t ht
      simp only [Finset.mem_filter, Finset.mem_range] at ht
      simp only [Finset.mem_singleton]
      by_contra hc
      apply ht.2
      unfold nvLs nvX
      simp [hc]
    calc lawMisses 0 (nvLs 0) nvX T ≤ ({0} : Finset ℕ).card := Finset.card_le_card hsub
      _ = 1 := Finset.card_singleton 0
  · simp only [WeightedFiber.floorSurpriseSet, Finset.mem_filter, Finset.mem_range]
    exact ⟨Nat.one_pos, by rw [nv_wrongMass0]; norm_num⟩

/-! ## Piece 5: the guards at table `90` -/

/-- **The center column is eventually exact at memory `0`**: it settles to `0` from stage `1` on. -/
theorem eventuallyExact_observedColumn_f90_single :
    EventuallyExact 0
      (observedColumn (tableRule f90 hq90) (Finsupp.single (0 : ℤ) (1 : ZMod 2)) 0) := by
  refine ⟨fun _ => 0, 1, fun t ht => ?_⟩
  change (0 : ZMod 2) = observedColumn (tableRule f90 hq90)
    (Finsupp.single (0 : ℤ) (1 : ZMod 2)) 0 (t + 0)
  rw [Nat.add_zero, ObservedColumn.observedColumn_f90_single]
  have ht0 : t ≠ 0 := by omega
  simp [ht0]

/-- **The cell beside it is eventually exact at NO memory.** -/
theorem not_exists_eventuallyExact_observedColumn_f90_single_one :
    ¬ ∃ k, EventuallyExact k
      (observedColumn (tableRule f90 hq90) (Finsupp.single (0 : ℤ) (1 : ZMod 2)) 1) := by
  rintro ⟨k, hk⟩
  exact not_eventuallyPeriodic_observedColumn_f90_single_one
    (eventuallyPeriodic_of_eventuallyExact hk)

/-- **Its hindsight count is unbounded, at every memory.** -/
theorem hindsightCount_observedColumn_f90_single_one_unbounded (k B : ℕ) :
    ∃ T, B < hindsightCount k
      (observedColumn (tableRule f90 hq90) (Finsupp.single (0 : ℤ) (1 : ZMod 2)) 1) T := by
  by_contra hcon
  push Not at hcon
  have hee : EventuallyExact k
      (observedColumn (tableRule f90 hq90) (Finsupp.single (0 : ℤ) (1 : ZMod 2)) 1) :=
    (hindsightCount_bounded_iff_eventuallyExact k _).mp ⟨B, hcon⟩
  exact not_exists_eventuallyExact_observedColumn_f90_single_one ⟨k, hee⟩

/-! ## Piece 6: the count at the two classes of tables -/

/-- **The observer's bill at the zero class**: at every table of the zero class, every cell's
hindsight count is bounded at some memory. It is
`exists_hindsightCount_bounded_iff_eventuallyPeriodic` read through
`ObservedColumn.eventuallyPeriodic_observedColumn_of_zeroByEndpoints`; the class is
`[Guests] §7 Proposition 7.24`'s and the count's registration `[Guests] §7 Proposition 7.27`,
cited for that reason alone. -/
theorem exists_hindsightCount_bounded_observedColumn_of_zeroByEndpoints
    (f : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2) (hq : f 0 0 0 = 0) (hf : ZeroByEndpoints f)
    (s₀ : ℤ →₀ ZMod 2) (i : ℤ) :
    ∃ k B, ∀ T, hindsightCount k (observedColumn (tableRule f hq) s₀ i) T ≤ B :=
  (exists_hindsightCount_bounded_iff_eventuallyPeriodic _).mpr
    (ObservedColumn.eventuallyPeriodic_observedColumn_of_zeroByEndpoints f hq hf s₀ i)

/-- **The same bill at every window** of the zero class: the width-`(m + 1)` window at cell `a`
has a bounded count at some memory, by the window form through the column form at its two end
cells. -/
theorem exists_hindsightCount_bounded_observedWindow_of_zeroByEndpoints
    (f : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2) (hq : f 0 0 0 = 0) (hf : ZeroByEndpoints f)
    (s₀ : ℤ →₀ ZMod 2) (a : ℤ) (m : ℕ) :
    ∃ k B, ∀ T,
      hindsightCount k (observedWindow (tableRule f hq) s₀ a (m + 1)) T ≤ B :=
  (exists_hindsightCount_bounded_observedWindow_iff f hq s₀ a m).mpr
    ⟨exists_hindsightCount_bounded_observedColumn_of_zeroByEndpoints f hq hf s₀ a,
      exists_hindsightCount_bounded_observedColumn_of_zeroByEndpoints f hq hf s₀ (a + (m : ℤ))⟩

/-- **Both hypotheses of the corollary hold at once**, at table `170` (the shift) from the single
seed `1` at cell `0`, and its conclusion is asserted there. -/
theorem exists_hindsightCount_bounded_observedColumn_of_zeroByEndpoints_nonvacuous :
    f170 0 0 0 = 0 ∧ ZeroByEndpoints f170 ∧
      ∃ k B, ∀ T, hindsightCount k
        (observedColumn (tableRule f170 hq170) (Finsupp.single (0 : ℤ) (1 : ZMod 2)) 0) T ≤ B :=
  ⟨hq170, zeroByEndpoints_f170,
    exists_hindsightCount_bounded_observedColumn_of_zeroByEndpoints f170 hq170
      zeroByEndpoints_f170 _ _⟩

/-- **The class hypothesis is load-bearing**: table `90` lies in the other class, and at it the
cell-one column's hindsight count exceeds every bound, at every memory. -/
theorem exists_hindsightCount_bounded_observedColumn_zero_class_guard :
    AccretesByEndpoints f90 ∧ ∀ k B, ∃ T, B < hindsightCount k
      (observedColumn (tableRule f90 hq90) (Finsupp.single (0 : ℤ) (1 : ZMod 2)) 1) T :=
  ⟨accretesByEndpoints_f90, hindsightCount_observedColumn_f90_single_one_unbounded⟩

end HindsightCount

/-! ## Axiom audit

Every public theorem above is `#print axioms`-clean on the standard triple, and the guards below
make that build-enforced. -/

set_option linter.style.longLine false

/-- info: 'HindsightCount.eventuallyExact_of_eventuallyPeriodic' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms HindsightCount.eventuallyExact_of_eventuallyPeriodic

/-- info: 'HindsightCount.eventuallyPeriodic_of_eventuallyExact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms HindsightCount.eventuallyPeriodic_of_eventuallyExact

/-- info: 'HindsightCount.hindsightCount_bounded_iff_eventuallyExact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms HindsightCount.hindsightCount_bounded_iff_eventuallyExact

/-- info: 'HindsightCount.exists_hindsightCount_bounded_iff_eventuallyPeriodic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms HindsightCount.exists_hindsightCount_bounded_iff_eventuallyPeriodic

/-- info: 'HindsightCount.exists_eventuallyExact_observedWindow_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms HindsightCount.exists_eventuallyExact_observedWindow_iff

/-- info: 'HindsightCount.exists_hindsightCount_bounded_observedWindow_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms HindsightCount.exists_hindsightCount_bounded_observedWindow_iff

/-- info: 'HindsightCount.floorSurprise_card_mul_le_of_lawMisses_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms HindsightCount.floorSurprise_card_mul_le_of_lawMisses_le

/-- info: 'HindsightCount.floorSurprise_card_mul_le_of_lawMisses_le_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms HindsightCount.floorSurprise_card_mul_le_of_lawMisses_le_nonvacuous

/-- info: 'HindsightCount.eventuallyExact_observedColumn_f90_single' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms HindsightCount.eventuallyExact_observedColumn_f90_single

/-- info: 'HindsightCount.not_exists_eventuallyExact_observedColumn_f90_single_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms HindsightCount.not_exists_eventuallyExact_observedColumn_f90_single_one

/-- info: 'HindsightCount.hindsightCount_observedColumn_f90_single_one_unbounded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms HindsightCount.hindsightCount_observedColumn_f90_single_one_unbounded

/-- info: 'HindsightCount.exists_eventuallyExact_iff_eventuallyPeriodic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms HindsightCount.exists_eventuallyExact_iff_eventuallyPeriodic

/-- info: 'HindsightCount.eventuallyExact_nat_id_not_eventuallyPeriodic' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms HindsightCount.eventuallyExact_nat_id_not_eventuallyPeriodic

/-- info: 'HindsightCount.exists_hindsightCount_bounded_observedColumn_of_zeroByEndpoints' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms HindsightCount.exists_hindsightCount_bounded_observedColumn_of_zeroByEndpoints

/-- info: 'HindsightCount.exists_hindsightCount_bounded_observedWindow_of_zeroByEndpoints' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms HindsightCount.exists_hindsightCount_bounded_observedWindow_of_zeroByEndpoints

/-- info: 'HindsightCount.exists_hindsightCount_bounded_observedColumn_of_zeroByEndpoints_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms HindsightCount.exists_hindsightCount_bounded_observedColumn_of_zeroByEndpoints_nonvacuous

/-- info: 'HindsightCount.exists_hindsightCount_bounded_observedColumn_zero_class_guard' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms HindsightCount.exists_hindsightCount_bounded_observedColumn_zero_class_guard
