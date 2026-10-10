/-
Copyright (c) 2026 Mykola Palamarchuk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mykola Palamarchuk
-/
module

public import CellularAutomata.HindsightCount
public import ALT.FlooredMixture

-- Formal-check file, not Mathlib-destined: opt out of the house-style header linter.
set_option linter.style.header false

/-!
# The hindsight count against a floored mixture
([RuleSpace] §4 Proposition 4.3)

`HindsightCount.lean` connects eventual periodicity to the fewest misses a law on the last `k`
readings makes. `FlooredMixture.lean` bounds the surprise count of a floored mixture against one
reference candidate's own miss count. This file instantiates the second at the miss matrix of a
finite law family, so that a bound on one reference law's misses bounds the floored mixture's
surprise count over the whole family.

## Main results

* `lawMissMatrix` — the miss matrix of a finite law family: which law of the family misses at
  which step.
* `floorSurprise_card_mul_le_of_lawMisses_le` — instantiates
  `WeightedFiber.floorSurprise_card_mul_le_missCount` at that matrix: a bound on one reference
  law's own misses bounds the floored mixture's surprise count over the whole family, free of the
  family's size beyond the constant already in the imported bound.
* `floorSurprise_card_mul_le_of_lawMisses_le_nonvacuous` — meets both of that instantiation's
  hypotheses at once, at a threshold below `1` so the surprise set is not empty by vacuity.

## Scope

`floorSurprise_card_mul_le_of_lawMisses_le` claims nothing about the family beyond what
`WeightedFiber.floorSurprise_card_mul_le_missCount` already claims of its `missCount` argument; the
family structure buys only that the reference law `Ls i₀` may be read off a FIXED memory shared by
every law of the family, not a sharper bound.
-/


@[expose] public section

namespace HindsightCount

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

end HindsightCount

/-! ## Axiom audit

Every capstone above is `#print axioms`-clean on the standard triple, and the guards below make
that build-enforced. -/

set_option linter.style.longLine false

/-- info: 'HindsightCount.floorSurprise_card_mul_le_of_lawMisses_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms HindsightCount.floorSurprise_card_mul_le_of_lawMisses_le

/-- info: 'HindsightCount.floorSurprise_card_mul_le_of_lawMisses_le_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms HindsightCount.floorSurprise_card_mul_le_of_lawMisses_le_nonvacuous
