/-
Copyright (c) 2026 Mykola Palamarchuk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mykola Palamarchuk
-/
module

public import ALT.SubstitutionSource
public import ALT.TapeHostSchedule

/-!
# The substitution source's identification, over ℕ directly
([Growth] §4 Theorems 4.3–4.4)

`SubstitutionSource.subObs` is not eventually periodic, so it has no finite-host presentation as
some `o : ZMod N → Bool` and cannot instantiate `TapeHostObservability.Profile` or
`TapeHostSchedule.schedSurvivors_eq_singleton_sharp`, both stated over such a host. This module
supplies the same window-deviation-to-identification pipeline directly over `ℕ`: `ProfileNat` is
`Profile`'s twin with the phase `c : ℕ` in place of `c : ZMod N`, `deviation_bound_nat` and
`schedSurvivors_eq_singleton_sharp_nat` are twins of the corresponding `TapeHostObservability` /
`TapeHostSchedule` theorems (the algebra is unchanged; only the reindexing that produces the
deviation bound is simpler, being plain `ℕ` addition rather than a `ZMod N` cast), and
`sharpHorizon`, `schedSurvivors` themselves are reused verbatim — neither one is ZMod-specific.

## Main results

* `ProfileNat` — the window-deviation profile, over `o : ℕ → Bool` directly.
* `deviation_bound_nat` — the two-offset query's deviation from the profile's displaced answer.
* `schedSurvivors_eq_singleton_sharp_nat` — the sharp identification window, at
  `fun t => o (c + t)`.
* `subObs_profile` — `SubstitutionSource.subObs` inhabits `ProfileNat`, at `S = 14` and `subW`.
* `subObs_identifies` — the schedule identifies the true literal on `subObs`, at every phase, from
  `TapeHostSchedule.sharpHorizon 14 77 (1/8) (5/16) (1/4)` on — `η = 1/8`, `τ = 5/16`, `μ = 1/4`
  meet `identifies_of_lt_quarter`'s own window (margins `3/8, 3/8, 1/8`), and `ρ 0 = 2η - 1` holds
  exactly at `subRho 0 = -3/4`.

## Scope

`identifies_of_lt_quarter` itself is not reproduced here: its role was to CHOOSE a `τ` inside the
window from `η, μ` alone, and `subObs`'s `τ = 5/16` is already pinned by the design (the same value
`identifies_of_lt_quarter`'s own proof would pick at `η = 1/8, μ = 1/4`), so `subObs_identifies`
calls `schedSurvivors_eq_singleton_sharp_nat` at that `τ` directly.
-/


@[expose] public section

namespace SubstitutionSchedule

open NoisyWindowChain BirkhoffTool Finset SubstitutionSource

/-! ## The ℕ-native profile and deviation bound -/

/-- **The window-deviation profile, over `o : ℕ → Bool` directly.**
`TapeHostObservability.Profile`'s twin, with the phase `c : ℕ` in place of `c : ZMod N` — the
shape a non-eventually-periodic source needs, since it has no finite-host presentation to wrap in
`Profile` itself. -/
structure ProfileNat (o : ℕ → Bool) (S : ℝ) (ρ W : Fin 8 → ℝ) : Prop where
  /-- The single-site character sum, at every phase and horizon, is bounded by `S`. -/
  single : ∀ (c n : ℕ), |∑ t ∈ range n, ParityWalk.chi (o (c + t))| ≤ S
  /-- The pair character sum at offsets `(a, 8)`, at every phase and horizon, deviates from the
  linear trend `n * ρ a` by at most `W a`. -/
  pair : ∀ (c : ℕ) (a : Fin 8) (n : ℕ),
    |∑ t ∈ range n, ParityWalk.chi (o (c + t + (a : ℕ))) *
        ParityWalk.chi (o (c + t + 8)) - (n : ℝ) * ρ a| ≤ W a

/-- **The query's deviation from the profile's own displaced answer, over `ℕ`.**
`TapeHostObservability.deviation_bound`'s twin: the reindexing is plain `ℕ` addition, so no cast
bureaucracy is needed. -/
theorem deviation_bound_nat {o : ℕ → Bool} {S : ℝ} {ρ W : Fin 8 → ℝ} (h : ProfileNat o S ρ W)
    (c : ℕ) (ψ : Bool → Bool → ℝ) (hψ : ∀ u v, |ψ u v| ≤ 1) (a : Fin 8) {n : ℕ} (hn : 1 ≤ n) :
    (n : ℝ) * |SQOracle.empiricalMean (pairEnsemble ψ (a : ℕ) 8) n (fun t => o (c + t)) -
        (pairMean ψ + pairCoefAB ψ * ρ a)| ≤ 2 * S + W a := by
  have hSa : |∑ t ∈ range n, ParityWalk.chi ((fun t => o (c + t)) (t + (a : ℕ)))| ≤ S := by
    have heq : (∑ t ∈ range n, ParityWalk.chi ((fun t => o (c + t)) (t + (a : ℕ))))
        = ∑ t ∈ range n, ParityWalk.chi (o (c + (a : ℕ) + t)) := by
      refine Finset.sum_congr rfl (fun t _ => ?_)
      simp only []
      congr 1; congr 1; omega
    rw [heq]
    exact h.single (c + (a : ℕ)) n
  have hSb : |∑ t ∈ range n, ParityWalk.chi ((fun t => o (c + t)) (t + 8))| ≤ S := by
    have heq : (∑ t ∈ range n, ParityWalk.chi ((fun t => o (c + t)) (t + 8)))
        = ∑ t ∈ range n, ParityWalk.chi (o (c + 8 + t)) := by
      refine Finset.sum_congr rfl (fun t _ => ?_)
      simp only []
      congr 1; congr 1; omega
    rw [heq]
    exact h.single (c + 8) n
  have hW : |∑ t ∈ range n, ParityWalk.chi ((fun t => o (c + t)) (t + (a : ℕ))) *
      ParityWalk.chi ((fun t => o (c + t)) (t + 8)) - (n : ℝ) * ρ a| ≤ W a := by
    have heq : (∑ t ∈ range n, ParityWalk.chi ((fun t => o (c + t)) (t + (a : ℕ))) *
        ParityWalk.chi ((fun t => o (c + t)) (t + 8)))
        = ∑ t ∈ range n, ParityWalk.chi (o (c + t + (a : ℕ))) * ParityWalk.chi (o (c + t + 8)) := by
      refine Finset.sum_congr rfl (fun t _ => ?_)
      simp only []
      congr 1; (congr 1; congr 1; omega)
    rw [heq]
    exact h.pair c a n
  exact empiricalMean_deviation_le_of_window_bounds ψ hψ (a : ℕ) 8 hn (fun t => o (c + t)) (ρ a) S
    (W a) hSa hSb hW

/-! ## The sharp identification window -/

/-- **The sharp identification window, over `ℕ`.**
`TapeHostSchedule.schedSurvivors_eq_singleton_sharp`'s twin: the same algebra, over
`deviation_bound_nat` and `fun t => o (c + t)` in place of `deviation_bound` and `hostTraj o c`.
`TapeHostSchedule.schedSurvivors`, `TapeHostSchedule.sharpHorizon` and
`LearningWitness.singleLiteralAns` are all already `ℕ`-native, so they are reused verbatim. -/
theorem schedSurvivors_eq_singleton_sharp_nat {o : ℕ → Bool} {S : ℝ} {ρ W : Fin 8 → ℝ}
    (h : ProfileNat o S ρ W) (Wm : ℝ) (hW : ∀ a, W a ≤ Wm)
    {η τ μ : ℝ} (hτ : 0 < τ) (hη : 0 ≤ η) (hρ0 : ρ 0 = 2 * η - 1)
    (hρ : ∀ a : Fin 8, (a : ℕ) ≠ 0 → |ρ a| ≤ μ) (_hμ0 : 0 ≤ μ)
    (hbudget : 2 * η ≤ τ) (hμτ : μ < 2 * τ) (hsep : 2 * τ + μ < 1)
    (c : ℕ) {n : ℕ} (hn1 : 1 ≤ n)
    (hn : (2 * S + Wm) / min (2 * τ - 2 * η) (min (2 * τ - μ) (1 - μ - 2 * τ)) < n) :
    TapeHostSchedule.schedSurvivors τ n (fun t => o (c + t)) = {0} := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
  have hm1 : (0 : ℝ) < 2 * τ - 2 * η := by linarith
  have hm2 : (0 : ℝ) < 2 * τ - μ := by linarith
  have hm3 : (0 : ℝ) < 1 - μ - 2 * τ := by linarith
  have hmm : (0 : ℝ) < min (2 * τ - 2 * η) (min (2 * τ - μ) (1 - μ - 2 * τ)) :=
    lt_min hm1 (lt_min hm2 hm3)
  have h1 : (2 * S + Wm) < (n : ℝ) * min (2 * τ - 2 * η) (min (2 * τ - μ) (1 - μ - 2 * τ)) :=
    (div_lt_iff₀ hmm).mp hn
  have heps : (2 * S + Wm) / (n : ℝ) <
      min (2 * τ - 2 * η) (min (2 * τ - μ) (1 - μ - 2 * τ)) := by
    rw [div_lt_iff₀ hn0]
    nlinarith [h1]
  have hlt1 : (2 * S + Wm) / (n : ℝ) < 2 * τ - 2 * η :=
    lt_of_lt_of_le heps (min_le_left _ _)
  have hlt2 : (2 * S + Wm) / (n : ℝ) < 2 * τ - μ :=
    lt_of_lt_of_le heps (le_trans (min_le_right _ _) (min_le_left _ _))
  have hlt3 : (2 * S + Wm) / (n : ℝ) < 1 - μ - 2 * τ :=
    lt_of_lt_of_le heps (le_trans (min_le_right _ _) (min_le_right _ _))
  have hε : ∀ a : Fin 8, |SQOracle.empiricalMean (pairEnsemble pairChar (a : ℕ) 8) n
      (fun t => o (c + t)) - ρ a| ≤ (2 * S + Wm) / (n : ℝ) := by
    intro a
    have hdb := deviation_bound_nat h c pairChar abs_pairChar_le_one a hn1
    rw [pairMean_pairChar, pairCoefAB_pairChar, one_mul, zero_add] at hdb
    have hWa : W a ≤ Wm := hW a
    rw [le_div_iff₀ hn0]
    nlinarith [hdb, hWa]
  rw [Finset.eq_singleton_iff_unique_mem]
  constructor
  · simp only [TapeHostSchedule.schedSurvivors, Finset.mem_filter, Finset.mem_univ, true_and]
    intro a
    by_cases ha0 : a = (0 : Fin 8)
    · subst ha0
      have hlit : LearningWitness.singleLiteralAns (0 : Fin 8) (0 : Fin 8) = -1 := by
        simp [LearningWitness.singleLiteralAns]
      rw [hlit, abs_le]
      obtain ⟨hεl, hεu⟩ := abs_le.mp (hε (0 : Fin 8))
      constructor <;> nlinarith [hεl, hεu, hρ0, hη, hlt1]
    · have hane : (a : ℕ) ≠ 0 := by
        intro hcontra
        exact ha0 (by ext; simpa using hcontra)
      have hlit : LearningWitness.singleLiteralAns a (0 : Fin 8) = 0 := by
        unfold LearningWitness.singleLiteralAns
        rw [ite_eq_right ha0]
      rw [hlit, abs_le]
      obtain ⟨hεl, hεu⟩ := abs_le.mp (hε a)
      obtain ⟨hρl, hρu⟩ := abs_le.mp (hρ a hane)
      constructor <;> nlinarith [hεl, hεu, hρl, hρu, hlt2]
  · intro i hi
    by_contra hne
    simp only [TapeHostSchedule.schedSurvivors, Finset.mem_filter, Finset.mem_univ,
      true_and] at hi
    have hane : (i : ℕ) ≠ 0 := by
        intro hcontra
        exact hne (by ext; simpa using hcontra)
    have hlit : LearningWitness.singleLiteralAns i i = -1 := by
      simp [LearningWitness.singleLiteralAns]
    have hb := hi i
    rw [hlit] at hb
    obtain ⟨hεl, hεu⟩ := abs_le.mp (hε i)
    obtain ⟨hρl, hρu⟩ := abs_le.mp (hρ i hane)
    have hx : (-1 : ℝ) - SQOracle.empiricalMean (pairEnsemble pairChar (i : ℕ) 8) n
        (fun t => o (c + t)) < -(2 * τ) := by nlinarith [hεl, hεu, hρl, hρu, hlt3]
    have habs2 : |(-1 : ℝ) - SQOracle.empiricalMean (pairEnsemble pairChar (i : ℕ) 8) n
        (fun t => o (c + t))| > 2 * τ := by
      rw [abs_of_neg (by linarith [hx] : (-1 : ℝ) - SQOracle.empiricalMean
          (pairEnsemble pairChar (i : ℕ) 8) n (fun t => o (c + t)) < 0)]
      linarith [hx]
    linarith [hb, habs2]

/-! ## Instantiation at `subObs` -/

/-- **`subObs` inhabits `ProfileNat`**, at its own window constants. -/
theorem subObs_profile : ProfileNat subObs 14 subRho subW :=
  ⟨subObs_single, subObs_pair⟩

/-- **The schedule identifies the true literal on `subObs`, at every phase.** `η = 1/8`,
`τ = 5/16`, `μ = 1/4` meet `TapeHostSchedule.identifies_of_lt_quarter`'s own window
(`η < (1 - μ)/4`, the margins `3/8, 3/8, 1/8`), and `subRho 0 = -3/4 = 2η - 1` exactly. -/
theorem subObs_identifies (c n : ℕ)
    (hn : TapeHostSchedule.sharpHorizon 14 77 (1 / 8) (5 / 16) (1 / 4) ≤ n) :
    TapeHostSchedule.schedSurvivors (5 / 16) n (fun t => subObs (c + t)) = {0} := by
  have hn1 : 1 ≤ n := le_trans (Nat.le_add_left 1 _) hn
  refine schedSurvivors_eq_singleton_sharp_nat (η := 1 / 8) (τ := 5 / 16) (μ := 1 / 4)
    subObs_profile 77 (fun _ => le_refl 77)
    (by norm_num) (by norm_num) (by simp [subRho]; norm_num)
    (fun a ha => by fin_cases a <;> simp_all [subRho] <;> norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) c hn1 ?_
  have h1 : (2 * (14 : ℝ) + 77) /
      min (2 * (5 / 16 : ℝ) - 2 * (1 / 8)) (min (2 * (5 / 16 : ℝ) - 1 / 4)
        (1 - 1 / 4 - 2 * (5 / 16)))
      < (⌊(2 * (14 : ℝ) + 77) /
          min (2 * (5 / 16 : ℝ) - 2 * (1 / 8)) (min (2 * (5 / 16 : ℝ) - 1 / 4)
            (1 - 1 / 4 - 2 * (5 / 16)))⌋₊ : ℝ) + 1 :=
    Nat.lt_floor_add_one _
  have h2 : (⌊(2 * (14 : ℝ) + 77) /
          min (2 * (5 / 16 : ℝ) - 2 * (1 / 8)) (min (2 * (5 / 16 : ℝ) - 1 / 4)
            (1 - 1 / 4 - 2 * (5 / 16)))⌋₊ + 1 : ℝ) ≤ (n : ℝ) := by
    have hn' : ⌊(2 * (14 : ℝ) + 77) /
        min (2 * (5 / 16 : ℝ) - 2 * (1 / 8)) (min (2 * (5 / 16 : ℝ) - 1 / 4)
          (1 - 1 / 4 - 2 * (5 / 16)))⌋₊ + 1 ≤ n := hn
    exact_mod_cast hn'
  linarith

end SubstitutionSchedule

/-! ## Axiom audit

Every capstone above is `#print axioms`-clean on the standard triple, and the guards below make
that build-enforced. -/

set_option linter.style.longLine false

/-- info: 'SubstitutionSchedule.deviation_bound_nat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SubstitutionSchedule.deviation_bound_nat

/-- info: 'SubstitutionSchedule.schedSurvivors_eq_singleton_sharp_nat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SubstitutionSchedule.schedSurvivors_eq_singleton_sharp_nat

/-- info: 'SubstitutionSchedule.subObs_profile' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SubstitutionSchedule.subObs_profile

/-- info: 'SubstitutionSchedule.subObs_identifies' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SubstitutionSchedule.subObs_identifies
