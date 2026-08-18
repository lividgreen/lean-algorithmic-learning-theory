/-
Copyright (c) 2026 Mykola Palamarchuk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mykola Palamarchuk
-/
import ALT.BlockPairHost

/-!
# The certified block-pair host's own scheduled E1

`BlockPairHost.lean` assembles a finite autonomous host carrying the certified block-pair design
(`BlockPairProfile.lean`) as its own observation process. This module reads that process at every
starting phase, ties it to the noisy-window-chain vocabulary (`NoisyWindowChain.lean`) three ways,
and assembles the schedule's E1: `BirkhoffTool.MixingHoeffding` at every offset `a : Fin 8` and
every bounded query `ψ`, on the finite average of the host's own per-phase Dirac laws.

## Main results

* `hostTraj` — the host's own emitted observation process, from phase `c` onward.
* `chi_designObs` — **tie (i)**: the design is `±1`-valued, so its character is its own cast.
* `designTape`, `hostTraj_eq_obs` — **tie (ii)**: the host's process from phase `c` *is* the noisy
  window chain's own `obs 8` on the designed initial window, closing the tape loop.
* `chiSum_eq_singleWindow`, `chiProd_eq_cyclicCorrWindow` — **tie (iii)**: the schedule's own
  character sums are the design's single-site and pair-correlation windows.
* `phaseLaw`, `phaseLaw_isProbabilityMeasure` — the finite average of the host's own per-phase
  Dirac laws.
* `mixingHoeffding_schedule` — **the assembled statement**: for every `M ≥ 1`, every offset
  `a : Fin 8`, and every bounded `ψ`, `MixingHoeffding` holds on `phaseLaw M` at the schedule's own
  displaced answer.

## Scope

Deliberately out of scope: the `𝒮_L` substrate and its membership statement, and anything about
the `𝒮_E` route-class — those are `BlockPairWitness.lean`'s and `BlockPairOverlap.lean`'s. The
paper home is [Inevitability] §5 Theorem 5.8, row IN-37.
-/

namespace BlockPairObservability

open BlockPairProfile BlockPairHost NoisyWindowChain MeasureTheory BirkhoffTool

variable (M : ℕ) [NeZero (2 * (2 * M))]

/-! ## The host's own observation process -/

/-- The host's own emitted observation process, from ℕ-phase `c` onward: the design read
`hostUpdate_iterate_last`'s own right-hand side, as a function of the elapsed time. -/
def hostTraj (c : ZMod (2 * (2 * M) * 24)) : ℕ → Bool := fun t => designObs M (c + t)

/-! ## Tie (i): the design is exactly `±1`-valued -/

private lemma blockSeq_wordU_wordV_eq_one_or_neg_one (u : ZMod (2 * (2 * M) * 24)) :
    blockSeq wordU wordV (blockSign (2 * (2 * M))) u = 1 ∨
      blockSeq wordU wordV (blockSign (2 * (2 * M))) u = -1 := by
  have hsq := blockSeq_wordU_wordV_sq M u
  have hz : (blockSeq wordU wordV (blockSign (2 * (2 * M))) u - 1) *
      (blockSeq wordU wordV (blockSign (2 * (2 * M))) u + 1) = 0 := by nlinarith [hsq]
  rcases mul_eq_zero.mp hz with h1 | h1
  · left; omega
  · right; omega

/-- **Tie (i).** The design's value at every point equals `−1` exactly where `designObs` reads
`true`, and `+1` where it reads `false` — so its character is its own cast, since the design is
exactly `±1`-valued (`blockSeq_wordU_wordV_sq`). -/
theorem chi_designObs (c : ZMod (2 * (2 * M) * 24)) :
    ParityWalk.chi (designObs M c) =
      (blockSeq wordU wordV (blockSign (2 * (2 * M))) c : ℝ) := by
  rcases blockSeq_wordU_wordV_eq_one_or_neg_one M c with h1 | h1
  · have hobs : designObs M c = false := by unfold designObs; rw [h1]; decide
    rw [hobs, h1]; simp
  · have hobs : designObs M c = true := by unfold designObs; rw [h1]; decide
    rw [hobs, h1]; simp

/-! ## Tie (ii): the host's process is the chain's own `obs 8` -/

/-- The window fed to the noisy window chain's `obs`: the design itself below the horizon `8`, and
the tape bit `hostTape` supplies above it. -/
private def designTape (c : ZMod (2 * (2 * M) * 24)) : ℕ → Bool :=
  fun t => if t < 8 then designObs M (c + t) else hostTape M (c + t)

/-- **Tie (ii).** The host's own emitted process from phase `c` *is* the noisy window chain's own
`obs 8` on the designed initial window, extended by the tape bit `hostTape` supplies — closing the
tape loop `hostTape`'s own docstring describes. -/
theorem hostTraj_eq_obs (c : ZMod (2 * (2 * M) * 24)) :
    hostTraj M c = NoisyWindowChain.obs 8 (designTape M c) := by
  funext t
  change designObs M (c + (t : ZMod _)) = NoisyWindowChain.obs 8 (designTape M c) t
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    by_cases ht : t < 8
    · rw [NoisyWindowChain.obs_of_lt (designTape M c) ht]
      unfold designTape
      rw [if_pos ht]
    · obtain ⟨s, hs⟩ : ∃ s, t = s + 8 := ⟨t - 8, by omega⟩
      have hih := ih s (by omega)
      have hdt : designTape M c (s + 8) = hostTape M (c + ((s + 8 : ℕ) : ZMod _)) := by
        unfold designTape
        rw [if_neg (by omega : ¬ s + 8 < 8)]
      rw [hs, NoisyWindowChain.obs_add (by norm_num : (0 : ℕ) < 8) (designTape M c) s, hdt, ← hih]
      have hcast2 : hostTape M (c + ((s + 8 : ℕ) : ZMod _))
          = (designObs M (c + ((s + 8 : ℕ) : ZMod _)) == designObs M (c + (s : ZMod _))) := by
        unfold hostTape
        congr 2
        push_cast
        ring
      rw [hcast2]
      cases designObs M (c + ((s + 8 : ℕ) : ZMod (2 * (2 * M) * 24))) <;>
        cases designObs M (c + (s : ZMod (2 * (2 * M) * 24))) <;> decide

/-! ## Tie (iii): the schedule's character sums are the design's own windows -/

private lemma cast_add_val (c : ZMod (2 * (2 * M) * 24)) (a i : ℕ) :
    c + ((a + i : ℕ) : ZMod (2 * (2 * M) * 24)) =
      ((c.val + a + i : ℕ) : ZMod (2 * (2 * M) * 24)) := by
  conv_lhs => rw [← ZMod.natCast_zmod_val c]
  push_cast
  ring

/-- **Tie (iii), single-site.** The schedule's own single-site character sum, at offset `a` and
along the host's process from phase `c`, is the design's own single-site window at ℕ-phase
`c.val + a`. -/
theorem chiSum_eq_singleWindow (c : ZMod (2 * (2 * M) * 24)) (a n : ℕ) :
    (∑ t ∈ Finset.range n, ParityWalk.chi (hostTraj M c (t + a))) =
      ((singleWindow (blockSeq wordU wordV (blockSign (2 * (2 * M)))) (c.val + a) n : ℤ) : ℝ) := by
  unfold singleWindow
  push_cast
  apply Finset.sum_congr rfl
  intro t _
  change ParityWalk.chi (designObs M (c + ((t + a : ℕ) : ZMod _))) = _
  rw [show (t + a : ℕ) = (a + t : ℕ) from by ring, cast_add_val M c a t, chi_designObs]
  congr 2
  push_cast
  ring

/-- **Tie (iii), pair.** The schedule's own pair character sum, at offsets `(a, 8)` with `a ≤ 8`
and along the host's process from phase `c`, is the design's own cyclic correlation window at lag
`8 − a` and ℕ-phase `c.val + a`. -/
theorem chiProd_eq_cyclicCorrWindow (c : ZMod (2 * (2 * M) * 24)) {a : ℕ} (ha8 : a ≤ 8) (n : ℕ) :
    (∑ t ∈ Finset.range n,
        ParityWalk.chi (hostTraj M c (t + a)) * ParityWalk.chi (hostTraj M c (t + 8))) =
      ((cyclicCorrWindow (blockSeq wordU wordV (blockSign (2 * (2 * M)))) (8 - a) (c.val + a) n :
        ℤ) : ℝ) := by
  unfold cyclicCorrWindow
  push_cast
  apply Finset.sum_congr rfl
  intro t _
  change ParityWalk.chi (designObs M (c + ((t + a : ℕ) : ZMod _))) *
      ParityWalk.chi (designObs M (c + ((t + 8 : ℕ) : ZMod _))) = _
  have hidx1 : c + ((t + a : ℕ) : ZMod (2 * (2 * M) * 24))
      = ((c.val + a + t : ℕ) : ZMod (2 * (2 * M) * 24)) := by
    rw [show (t + a : ℕ) = (a + t : ℕ) from by ring]
    exact cast_add_val M c a t
  have hidx2 : c + ((t + 8 : ℕ) : ZMod (2 * (2 * M) * 24))
      = ((c.val + a + t : ℕ) : ZMod (2 * (2 * M) * 24)) +
        ((8 - a : ℕ) : ZMod (2 * (2 * M) * 24)) := by
    rw [show (t + 8 : ℕ) = (a + t) + (8 - a) from by omega, cast_add_val M c (a + t) (8 - a)]
    push_cast
    ring
  rw [hidx1, hidx2, chi_designObs, chi_designObs]
  push_cast
  ring

/-! ## The per-phase deviation bound -/

/-- **The cross-class deviation bound.** At any offset `1 ≤ a ≤ 7`, the two-offset query's
`n`-scaled deviation from the flat answer `pairMean ψ`, along the host's process from any phase
`c`, is bounded by `2 * 56 + 192` — twice the single-site window constant plus T71's zone window
constant, uniformly in `c` and `n`. -/
private theorem deviation_bound_cross (c : ZMod (2 * (2 * M) * 24)) (ψ : Bool → Bool → ℝ)
    (hψ : ∀ u v, |ψ u v| ≤ 1) {a : ℕ} (ha1 : 1 ≤ a) (ha7 : a ≤ 7) {n : ℕ} (hn : 1 ≤ n) :
    (n : ℝ) * |SQOracle.empiricalMean (pairEnsemble ψ a 8) n (hostTraj M c) - pairMean ψ| ≤
      2 * 56 + 192 := by
  have hSa : |∑ t ∈ Finset.range n, ParityWalk.chi (hostTraj M c (t + a))| ≤ (56 : ℝ) := by
    rw [chiSum_eq_singleWindow M c a n, ← Int.cast_abs]
    exact_mod_cast singleWindow_blockSeq_wordU_wordV_bound M (c.val + a) n
  have hSb : |∑ t ∈ Finset.range n, ParityWalk.chi (hostTraj M c (t + 8))| ≤ (56 : ℝ) := by
    rw [chiSum_eq_singleWindow M c 8 n, ← Int.cast_abs]
    exact_mod_cast singleWindow_blockSeq_wordU_wordV_bound M (c.val + 8) n
  have hW : |∑ t ∈ Finset.range n, ParityWalk.chi (hostTraj M c (t + a)) *
      ParityWalk.chi (hostTraj M c (t + 8)) - (n : ℝ) * 0| ≤ (192 : ℝ) := by
    rw [mul_zero, sub_zero, chiProd_eq_cyclicCorrWindow M c (by omega : a ≤ 8) n, ← Int.cast_abs]
    exact_mod_cast cyclicCorrWindow_blockSeq_wordU_wordV_zone M (by omega : 1 ≤ 8 - a)
      (by omega : 8 - a ≤ 7) (c.val + a) n
  have h := empiricalMean_deviation_le_of_window_bounds ψ hψ a 8 hn (hostTraj M c) 0 56 192
    hSa hSb hW
  simpa using h

/-- **The same-class deviation bound.** At offset `0` (self-correlation at lag `8`, the rule's own
literal against the label), the two-offset query's `n`-scaled deviation from the displaced answer
`pairMean ψ + pairCoefAB ψ * (-2/3)`, along the host's process from any phase `c`, is bounded by
`2 * 56 + 46` — the spike window bound divided by the trend scale `2 * 24`. -/
private theorem deviation_bound_same (c : ZMod (2 * (2 * M) * 24)) (ψ : Bool → Bool → ℝ)
    (hψ : ∀ u v, |ψ u v| ≤ 1) {n : ℕ} (hn : 1 ≤ n) :
    (n : ℝ) * |SQOracle.empiricalMean (pairEnsemble ψ 0 8) n (hostTraj M c) -
        (pairMean ψ + pairCoefAB ψ * (-2 / 3))| ≤ 2 * 56 + 46 := by
  have hSa : |∑ t ∈ Finset.range n, ParityWalk.chi (hostTraj M c (t + 0))| ≤ (56 : ℝ) := by
    rw [chiSum_eq_singleWindow M c 0 n, ← Int.cast_abs]
    exact_mod_cast singleWindow_blockSeq_wordU_wordV_bound M (c.val + 0) n
  have hSb : |∑ t ∈ Finset.range n, ParityWalk.chi (hostTraj M c (t + 8))| ≤ (56 : ℝ) := by
    rw [chiSum_eq_singleWindow M c 8 n, ← Int.cast_abs]
    exact_mod_cast singleWindow_blockSeq_wordU_wordV_bound M (c.val + 8) n
  have hW : |∑ t ∈ Finset.range n, ParityWalk.chi (hostTraj M c (t + 0)) *
      ParityWalk.chi (hostTraj M c (t + 8)) - (n : ℝ) * (-2 / 3)| ≤ (46 : ℝ) := by
    rw [chiProd_eq_cyclicCorrWindow M c (by omega : (0 : ℕ) ≤ 8) n]
    have haperiodic : aperiodicCorr wordU 8 + aperiodicCorr wordV 8 = -32 := by decide
    have hb := cyclicCorrWindow_blockSeq_wordU_wordV_spike M (c.val + 0) n
    rw [haperiodic] at hb
    set X : ℤ := cyclicCorrWindow (blockSeq wordU wordV (blockSign (2 * (2 * M)))) 8
      (c.val + 0) n with hXdef
    have hbR : |48 * (X : ℝ) + 32 * (n : ℝ)| ≤ 2208 := by
      have heq : (48 : ℝ) * (X : ℝ) + 32 * (n : ℝ) = ((2 * 24 * X - n * (-32) : ℤ) : ℝ) := by
        push_cast; ring
      rw [heq]
      exact_mod_cast hb
    have heq2 : (X : ℝ) - (n : ℝ) * (-2 / 3) = (48 * (X : ℝ) + 32 * (n : ℝ)) / 48 := by ring
    rw [heq2, abs_div]
    rw [show |(48 : ℝ)| = 48 from by norm_num, div_le_iff₀ (by norm_num : (0 : ℝ) < 48)]
    linarith [hbR]
  have h := empiricalMean_deviation_le_of_window_bounds ψ hψ 0 8 hn (hostTraj M c) (-2 / 3) 56 46
    hSa hSb hW
  exact h

/-! ## The phase law -/

/-- **The phase law.** The finite average of the host's own per-phase Dirac laws — the honest
reading of the single-orbit E1 randomness a deterministic finite host has: one law per starting
phase, weighted uniformly. -/
noncomputable def phaseLaw : Measure (ℕ → Bool) :=
  ((Fintype.card (ZMod (2 * (2 * M) * 24)) : ENNReal))⁻¹ •
    ∑ c : ZMod (2 * (2 * M) * 24), Measure.dirac (hostTraj M c)

instance phaseLaw_isProbabilityMeasure : IsProbabilityMeasure (phaseLaw M) := by
  constructor
  unfold phaseLaw
  rw [Measure.smul_apply, Measure.finsetSum_apply, smul_eq_mul]
  have hcard_pos : 0 < Fintype.card (ZMod (2 * (2 * M) * 24)) := Fintype.card_pos
  have hcardE : (Fintype.card (ZMod (2 * (2 * M) * 24)) : ENNReal) ≠ 0 := by
    exact_mod_cast hcard_pos.ne'
  have hcardEtop : (Fintype.card (ZMod (2 * (2 * M) * 24)) : ENNReal) ≠ ⊤ :=
    ENNReal.natCast_ne_top _
  have hsum : (∑ c : ZMod (2 * (2 * M) * 24), (Measure.dirac (hostTraj M c)) Set.univ)
      = (Fintype.card (ZMod (2 * (2 * M) * 24)) : ENNReal) := by
    simp [measure_univ]
  rw [hsum]
  exact ENNReal.inv_mul_cancel hcardE hcardEtop

/-! ## The assembled schedule theorem -/

/-- Averaging the per-phase Dirac `MixingHoeffding` bound over every phase — with the same
constant at every phase — gives `MixingHoeffding` under the phase law. -/
private lemma mixingHoeffding_phaseLaw_of_forall_dirac
    (Z : ℕ → (ℕ → Bool) → ℝ) (predZ constC : ℝ)
    (h : ∀ c : ZMod (2 * (2 * M) * 24),
      MixingHoeffding (Measure.dirac (hostTraj M c)) Z predZ constC) :
    MixingHoeffding (phaseLaw M) Z predZ constC := by
  intro n τ hn hτ
  set S : Set (ℕ → Bool) := {ω | τ ≤ |SQOracle.empiricalMean Z n ω - predZ|} with hSdef
  have hcard_pos : 0 < Fintype.card (ZMod (2 * (2 * M) * 24)) := Fintype.card_pos
  have hcardE : (Fintype.card (ZMod (2 * (2 * M) * 24)) : ENNReal) ≠ 0 := by
    exact_mod_cast hcard_pos.ne'
  have hphaseLaw_apply : (phaseLaw M) S =
      (Fintype.card (ZMod (2 * (2 * M) * 24)) : ENNReal)⁻¹ *
        ∑ c : ZMod (2 * (2 * M) * 24), (Measure.dirac (hostTraj M c)) S := by
    unfold phaseLaw
    rw [Measure.smul_apply, Measure.finsetSum_apply, smul_eq_mul]
  have hreal_eq : (phaseLaw M).real S =
      (Fintype.card (ZMod (2 * (2 * M) * 24)) : ℝ)⁻¹ *
        ∑ c : ZMod (2 * (2 * M) * 24), (Measure.dirac (hostTraj M c)).real S := by
    unfold Measure.real
    rw [hphaseLaw_apply, ENNReal.toReal_mul, ENNReal.toReal_inv,
      ENNReal.toReal_sum (fun c _ => measure_ne_top _ S)]
    norm_cast
  rw [hreal_eq]
  have hbound : ∀ c : ZMod (2 * (2 * M) * 24), (Measure.dirac (hostTraj M c)).real S ≤
      2 * Real.exp (-(n : ℝ) * τ ^ 2 / (2 * constC)) := fun c => h c n τ hn hτ
  have hsum_bound : (∑ c : ZMod (2 * (2 * M) * 24), (Measure.dirac (hostTraj M c)).real S) ≤
      (Fintype.card (ZMod (2 * (2 * M) * 24)) : ℝ) *
        (2 * Real.exp (-(n : ℝ) * τ ^ 2 / (2 * constC))) := by
    calc (∑ c : ZMod (2 * (2 * M) * 24), (Measure.dirac (hostTraj M c)).real S)
        ≤ ∑ _c : ZMod (2 * (2 * M) * 24), 2 * Real.exp (-(n : ℝ) * τ ^ 2 / (2 * constC)) :=
          Finset.sum_le_sum (fun c _ => hbound c)
      _ = (Fintype.card (ZMod (2 * (2 * M) * 24)) : ℝ) *
          (2 * Real.exp (-(n : ℝ) * τ ^ 2 / (2 * constC))) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hcardR : (0 : ℝ) < (Fintype.card (ZMod (2 * (2 * M) * 24)) : ℝ) := by
    exact_mod_cast hcard_pos
  calc (Fintype.card (ZMod (2 * (2 * M) * 24)) : ℝ)⁻¹ *
      ∑ c : ZMod (2 * (2 * M) * 24), (Measure.dirac (hostTraj M c)).real S
      ≤ (Fintype.card (ZMod (2 * (2 * M) * 24)) : ℝ)⁻¹ *
          ((Fintype.card (ZMod (2 * (2 * M) * 24)) : ℝ) *
            (2 * Real.exp (-(n : ℝ) * τ ^ 2 / (2 * constC)))) :=
        mul_le_mul_of_nonneg_left hsum_bound (by positivity)
    _ = 2 * Real.exp (-(n : ℝ) * τ ^ 2 / (2 * constC)) := by
        field_simp

/-- **The assembled schedule theorem.** For every `M` with `NeZero (2 * (2 * M))` (i.e. `M ≥ 1`),
every offset `a : Fin 8`, and every bounded query `ψ`, the schedule's two-offset query satisfies
`MixingHoeffding` on the finite average of the host's own per-phase Dirac laws (`phaseLaw M`), at
the schedule's own displaced answer — the deterministic prefix bounds of `deviation_bound_cross`/
`deviation_bound_same`, lifted through `mixingHoeffding_dirac_of_deviation_bound` at every phase
and combined via `mixingHoeffding_phaseLaw_of_forall_dirac`. -/
theorem mixingHoeffding_schedule (a : Fin 8) (ψ : Bool → Bool → ℝ) (hψ : ∀ u v, |ψ u v| ≤ 1) :
    MixingHoeffding (phaseLaw M) (pairEnsemble ψ (a : ℕ) 8)
      (if (a : ℕ) = 0 then pairMean ψ + pairCoefAB ψ * (-2 / 3) else pairMean ψ)
      ((if (a : ℕ) = 0 then (2 * 56 + 46 : ℝ) else (2 * 56 + 192 : ℝ)) ^ 2 / (2 * Real.log 2)) := by
  have haLt := a.isLt
  apply mixingHoeffding_phaseLaw_of_forall_dirac M
  intro c
  by_cases ha0 : (a : ℕ) = 0
  · rw [if_pos ha0, if_pos ha0]
    refine mixingHoeffding_dirac_of_deviation_bound (hostTraj M c) (pairEnsemble ψ (a : ℕ) 8) _
      _ (by norm_num) (fun i => measurable_pairEnsemble ψ (a : ℕ) 8 i) (fun n hn => ?_)
    rw [ha0]
    exact deviation_bound_same M c ψ hψ hn
  · rw [if_neg ha0, if_neg ha0]
    refine mixingHoeffding_dirac_of_deviation_bound (hostTraj M c) (pairEnsemble ψ (a : ℕ) 8) _
      _ (by norm_num) (fun i => measurable_pairEnsemble ψ (a : ℕ) 8 i) (fun n hn => ?_)
    exact deviation_bound_cross M c ψ hψ (by omega) (by omega) hn

end BlockPairObservability
