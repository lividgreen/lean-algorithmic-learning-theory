/-
Copyright (c) 2026 Mykola Palamarchuk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mykola Palamarchuk
-/
import ALT.TapeHost
import ALT.BirkhoffTool
import ALT.NoisyWindowChain

/-!
# The finite autonomous host's E1, over an arbitrary window-deviation profile

`TapeHost.lean` wraps an arbitrary observation sequence `o : ZMod N → Bool` into a finite
autonomous host. This module reads that host's own emitted process at every starting phase and
assembles the schedule's E1 (`BirkhoffTool.MixingHoeffding`) from a `Profile`: a named
window-deviation bound on `o`'s own single-site and pair-correlation character sums. This is
`BlockPairObservability.lean`'s pipeline with the design's own certified window bounds made a
hypothesis, so any sequence whose deviation is bounded this way inherits the same schedule theorem.

## Main results

* `hostTraj` — the host's own emitted observation process, from phase `c` onward.
* `Profile` — the named window-deviation profile: a single-site bound `S` and, at every offset
  `a : Fin 8`, a pair-correlation bound `W a` against a declared correlation `ρ a`.
* `deviation_bound` — the query's deviation from the profile's own displaced answer, bounded by
  `2 * S + W a`, at every offset `a` and starting phase `c`.
* `phaseLaw`, `phaseLaw_isProbabilityMeasure` — the finite average of the host's own per-phase
  Dirac laws.
* `mixingHoeffding_schedule` — **the assembled statement**: at any `Profile`, every offset
  `a : Fin 8`, and every bounded `ψ`, `MixingHoeffding` holds on `phaseLaw` at the profile's own
  displaced answer.

## Scope

Deliberately out of scope: the `𝒮_L` substrate and its membership statement, and anything about
the `𝒮_E` route-class — those are `TapeHostWitness.lean`'s and `TapeHostOverlap.lean`'s. The
paper home is [Inevitability] §5 Theorem 5.8, row IN-37.
-/

namespace TapeHostObservability

open TapeHost NoisyWindowChain MeasureTheory BirkhoffTool

variable {N : ℕ} [NeZero N] (o : ZMod N → Bool)

/-! ## The host's own observation process -/

/-- The host's own emitted observation process, from ℕ-phase `c` onward. -/
def hostTraj (c : ZMod N) : ℕ → Bool := fun t => o (c + t)

/-! ## The window-deviation profile -/

/-- **The window-deviation profile.** A named single-site bound `S` on `o`'s own character sums,
and, at every offset `a : Fin 8`, a pair-correlation bound `W a` against a declared correlation
`ρ a` between the sites `a` and `8` apart — the exact shape `BlockPairObservability.lean`'s
`hSa`/`hSb`/`hW` window bounds instantiate for the certified design. -/
structure Profile (S : ℝ) (ρ W : Fin 8 → ℝ) : Prop where
  /-- The single-site character sum, at every phase and horizon, is bounded by `S`. -/
  single : ∀ (c : ZMod N) (n : ℕ), |∑ t ∈ Finset.range n, ParityWalk.chi (o (c + (t : ℕ)))| ≤ S
  /-- The pair character sum at offsets `(a, 8)`, at every phase and horizon, deviates from the
  linear trend `n * ρ a` by at most `W a`. -/
  pair : ∀ (c : ZMod N) (a : Fin 8) (n : ℕ),
    |∑ t ∈ Finset.range n, ParityWalk.chi (o (c + (t : ℕ) + ((a : ℕ) : ZMod N))) *
        ParityWalk.chi (o (c + (t : ℕ) + ((8 : ℕ) : ZMod N))) - (n : ℝ) * ρ a| ≤ W a

variable {S : ℝ} {ρ W : Fin 8 → ℝ}

omit [NeZero N] in
/-- Reindexing a host-trajectory shift into the base point: `hostTraj o c (t + b) = o (c + b + t)`,
for any ℕ offset `b`. The one identity every reindexing below reduces to. -/
private lemma hostTraj_shift (c : ZMod N) (t b : ℕ) :
    hostTraj o c (t + b) = o (c + ((b : ℕ) : ZMod N) + (t : ℕ)) := by
  change o (c + ((t + b : ℕ) : ZMod N)) = o (c + ((b : ℕ) : ZMod N) + (t : ℕ))
  congr 1
  push_cast
  ring

omit [NeZero N] in
/-- **The query's deviation from the profile's own displaced answer.** The public interface to
`Profile`: given the single-site bound `S` and the pair bound `W a` against the declared
correlation `ρ a`, the two-offset query's `n`-scaled deviation from `pairMean ψ + pairCoefAB ψ · ρ
a`, along the host's own process from phase `c`, is at most `2 * S + W a` —
`empiricalMean_deviation_le_of_window_bounds`, fed the profile's own two window bounds after
reindexing them onto `hostTraj`. -/
theorem deviation_bound (h : Profile o S ρ W) (c : ZMod N) (ψ : Bool → Bool → ℝ)
    (hψ : ∀ u v, |ψ u v| ≤ 1) (a : Fin 8) {n : ℕ} (hn : 1 ≤ n) :
    (n : ℝ) * |SQOracle.empiricalMean (pairEnsemble ψ (a : ℕ) 8) n (hostTraj o c) -
        (pairMean ψ + pairCoefAB ψ * ρ a)| ≤ 2 * S + W a := by
  have hSa : |∑ t ∈ Finset.range n, ParityWalk.chi (hostTraj o c (t + (a : ℕ)))| ≤ S := by
    simp_rw [hostTraj_shift]
    exact h.single (c + ((a : ℕ) : ZMod N)) n
  have hSb : |∑ t ∈ Finset.range n, ParityWalk.chi (hostTraj o c (t + 8))| ≤ S := by
    simp_rw [hostTraj_shift]
    exact h.single (c + ((8 : ℕ) : ZMod N)) n
  have hW : |∑ t ∈ Finset.range n, ParityWalk.chi (hostTraj o c (t + (a : ℕ))) *
      ParityWalk.chi (hostTraj o c (t + 8)) - (n : ℝ) * ρ a| ≤ W a := by
    have heq : (∑ t ∈ Finset.range n, ParityWalk.chi (hostTraj o c (t + (a : ℕ))) *
        ParityWalk.chi (hostTraj o c (t + 8)))
        = ∑ t ∈ Finset.range n, ParityWalk.chi (o (c + (t : ℕ) + ((a : ℕ) : ZMod N))) *
            ParityWalk.chi (o (c + (t : ℕ) + ((8 : ℕ) : ZMod N))) := by
      apply Finset.sum_congr rfl
      intro t _
      have ea : hostTraj o c (t + (a : ℕ)) = o (c + (t : ℕ) + ((a : ℕ) : ZMod N)) := by
        change o (c + ((t + (a : ℕ) : ℕ) : ZMod N)) = o (c + (t : ℕ) + ((a : ℕ) : ZMod N))
        congr 1; push_cast; ring
      have e8 : hostTraj o c (t + 8) = o (c + (t : ℕ) + ((8 : ℕ) : ZMod N)) := by
        change o (c + ((t + 8 : ℕ) : ZMod N)) = o (c + (t : ℕ) + ((8 : ℕ) : ZMod N))
        congr 1; push_cast; ring
      rw [ea, e8]
    rw [heq]
    exact h.pair c a n
  exact empiricalMean_deviation_le_of_window_bounds ψ hψ (a : ℕ) 8 hn (hostTraj o c) (ρ a) S (W a)
    hSa hSb hW

/-! ## The phase law -/

/-- **The phase law.** The finite average of the host's own per-phase Dirac laws. -/
noncomputable def phaseLaw : Measure (ℕ → Bool) :=
  ((Fintype.card (ZMod N) : ENNReal))⁻¹ • ∑ c : ZMod N, Measure.dirac (hostTraj o c)

instance phaseLaw_isProbabilityMeasure : IsProbabilityMeasure (phaseLaw o) := by
  constructor
  unfold phaseLaw
  rw [Measure.smul_apply, Measure.finsetSum_apply, smul_eq_mul]
  have hcard_pos : 0 < Fintype.card (ZMod N) := Fintype.card_pos
  have hcardE : (Fintype.card (ZMod N) : ENNReal) ≠ 0 := by exact_mod_cast hcard_pos.ne'
  have hcardEtop : (Fintype.card (ZMod N) : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top _
  have hsum : (∑ c : ZMod N, (Measure.dirac (hostTraj o c)) Set.univ)
      = (Fintype.card (ZMod N) : ENNReal) := by
    simp [measure_univ]
  rw [hsum]
  exact ENNReal.inv_mul_cancel hcardE hcardEtop

/-! ## The assembled schedule theorem -/

/-- Averaging the per-phase Dirac `MixingHoeffding` bound over every phase — with the same
constant at every phase — gives `MixingHoeffding` under the phase law. -/
private lemma mixingHoeffding_phaseLaw_of_forall_dirac
    (Z : ℕ → (ℕ → Bool) → ℝ) (predZ constC : ℝ)
    (h : ∀ c : ZMod N, MixingHoeffding (Measure.dirac (hostTraj o c)) Z predZ constC) :
    MixingHoeffding (phaseLaw o) Z predZ constC := by
  intro n τ hn hτ
  set A : Set (ℕ → Bool) := {ω | τ ≤ |SQOracle.empiricalMean Z n ω - predZ|} with hAdef
  have hcard_pos : 0 < Fintype.card (ZMod N) := Fintype.card_pos
  have hcardE : (Fintype.card (ZMod N) : ENNReal) ≠ 0 := by exact_mod_cast hcard_pos.ne'
  have hphaseLaw_apply : (phaseLaw o) A =
      (Fintype.card (ZMod N) : ENNReal)⁻¹ * ∑ c : ZMod N, (Measure.dirac (hostTraj o c)) A := by
    unfold phaseLaw
    rw [Measure.smul_apply, Measure.finsetSum_apply, smul_eq_mul]
  have hreal_eq : (phaseLaw o).real A =
      (Fintype.card (ZMod N) : ℝ)⁻¹ * ∑ c : ZMod N, (Measure.dirac (hostTraj o c)).real A := by
    unfold Measure.real
    rw [hphaseLaw_apply, ENNReal.toReal_mul, ENNReal.toReal_inv,
      ENNReal.toReal_sum (fun c _ => measure_ne_top _ A)]
    norm_cast
  rw [hreal_eq]
  have hbound : ∀ c : ZMod N, (Measure.dirac (hostTraj o c)).real A ≤
      2 * Real.exp (-(n : ℝ) * τ ^ 2 / (2 * constC)) := fun c => h c n τ hn hτ
  have hsum_bound : (∑ c : ZMod N, (Measure.dirac (hostTraj o c)).real A) ≤
      (Fintype.card (ZMod N) : ℝ) * (2 * Real.exp (-(n : ℝ) * τ ^ 2 / (2 * constC))) := by
    calc (∑ c : ZMod N, (Measure.dirac (hostTraj o c)).real A)
        ≤ ∑ _c : ZMod N, 2 * Real.exp (-(n : ℝ) * τ ^ 2 / (2 * constC)) :=
          Finset.sum_le_sum (fun c _ => hbound c)
      _ = (Fintype.card (ZMod N) : ℝ) * (2 * Real.exp (-(n : ℝ) * τ ^ 2 / (2 * constC))) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hcardR : (0 : ℝ) < (Fintype.card (ZMod N) : ℝ) := by exact_mod_cast hcard_pos
  calc (Fintype.card (ZMod N) : ℝ)⁻¹ * ∑ c : ZMod N, (Measure.dirac (hostTraj o c)).real A
      ≤ (Fintype.card (ZMod N) : ℝ)⁻¹ *
          ((Fintype.card (ZMod N) : ℝ) * (2 * Real.exp (-(n : ℝ) * τ ^ 2 / (2 * constC)))) :=
        mul_le_mul_of_nonneg_left hsum_bound (by positivity)
    _ = 2 * Real.exp (-(n : ℝ) * τ ^ 2 / (2 * constC)) := by
        field_simp

/-- **The assembled schedule theorem.** At any `Profile`, every offset `a : Fin 8`, and every
bounded query `ψ`, the schedule's two-offset query satisfies `MixingHoeffding` on the finite
average of the host's own per-phase Dirac laws (`phaseLaw`), at the profile's own displaced
answer — `deviation_bound`, lifted through `mixingHoeffding_dirac_of_deviation_bound` at every
phase and combined via `mixingHoeffding_phaseLaw_of_forall_dirac`. -/
theorem mixingHoeffding_schedule (h : Profile o S ρ W) (a : Fin 8) (ψ : Bool → Bool → ℝ)
    (hψ : ∀ u v, |ψ u v| ≤ 1) :
    MixingHoeffding (phaseLaw o) (pairEnsemble ψ (a : ℕ) 8) (pairMean ψ + pairCoefAB ψ * ρ a)
      ((2 * S + W a) ^ 2 / (2 * Real.log 2)) := by
  have hS0 : 0 ≤ S := by simpa using h.single 0 0
  have hWa0 : 0 ≤ W a := by simpa using h.pair 0 a 0
  apply mixingHoeffding_phaseLaw_of_forall_dirac o
  intro c
  exact mixingHoeffding_dirac_of_deviation_bound (hostTraj o c) (pairEnsemble ψ (a : ℕ) 8) _ _
    (by linarith) (fun i => measurable_pairEnsemble ψ (a : ℕ) 8 i)
    (fun n hn => deviation_bound o h c ψ hψ a hn)

end TapeHostObservability
