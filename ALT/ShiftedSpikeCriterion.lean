module

public import ALT.BlockPairProfile
public import ALT.TapeHostSchedule
public import ALT.ParityWalk

/-!
# A second certified design: literal `2`, spike lag `6`, identified from `817`

`BlockPairProfile.lean`'s second certified word pair (`wordU2`, `wordV2`, length `22`, spike lag
`6`) is read here as a Boolean observation (`designObs2`), shown to meet
`Profile` at the window bounds that pair's own correlation profile
establishes (`designObs2_profile`), and shown to identify literal `2` under
`schedSurvivors`'s `2τ`-pruning rule (`shiftedSpike_identifies`).

Unlike the certified block-pair design, this identification needs no tape/window host mechanics:
`Profile` and `schedSurvivors` act on the observation
sequence alone, through `TapeHost.traj o c := fun t => o (c + t)`, so `designObs2`
is fed to them directly. A tape/window host carrying this design — needed only for the rung/tower
capstone — is `ShiftedSpikeHost.lean`'s business.

## Main results

* `designObs2` — the second certified design, read as a Boolean observation.
* `chi_designObs2` — the design is exactly `±1`-valued, so its character is its own cast.
* `designObs2_profile` — the design meets `Profile` at `S = 48`, correlation
  `-8/11` at offset `2` (zero elsewhere), and window bounds `34`/`176`.
* `shiftedSpike_identifies` — **the affordable regime's second worked example**:
  `schedSurvivors`'s `2τ`-pruning rule isolates literal `2` from this design's own
  profile, at `τ = 1/3` and every horizon `n > 816`.

## Scope

Deliberately out of scope, as `BlockPairObservability.lean`'s own tie (ii) and everything past it:
any tape/window host, the `𝒮_L`/`𝒮_E` substrate questions, and the tower rung — those are
`ShiftedSpikeHost.lean`'s and `ShiftedSpikeTower.lean`'s. The paper home is [Inevitability] §6
Remark 6.14's finite degeneracy clause.
-/


@[expose] public section

namespace ALT

variable (M : ℕ) [NeZero (2 * (2 * M))]

/-! ## The design, read as a Boolean observation -/

/-- The second certified design, read as a Boolean observation: `true` exactly where the design's
value is `-1`, mirroring `BlockPairHost.designObs`. -/
def designObs2 (u : ZMod (2 * (2 * M) * 22)) : Bool :=
  decide (blockSeq wordU2 wordV2 (blockSign (2 * (2 * M))) u = -1)

/-! ## The design is exactly `±1`-valued -/

private lemma blockSeq_wordU2_wordV2_eq_one_or_neg_one (u : ZMod (2 * (2 * M) * 22)) :
    blockSeq wordU2 wordV2 (blockSign (2 * (2 * M))) u = 1 ∨
      blockSeq wordU2 wordV2 (blockSign (2 * (2 * M))) u = -1 := by
  have hsq := blockSeq_wordU2_wordV2_sq M u
  have hz : (blockSeq wordU2 wordV2 (blockSign (2 * (2 * M))) u - 1) *
      (blockSeq wordU2 wordV2 (blockSign (2 * (2 * M))) u + 1) = 0 := by nlinarith [hsq]
  rcases mul_eq_zero.mp hz with h1 | h1
  · left; omega
  · right; omega

/-- **The design's character is its own cast**, mirroring `BlockPairHost.chi_designObs`. -/
theorem chi_designObs2 (c : ZMod (2 * (2 * M) * 22)) :
    ALT.chi (designObs2 M c) =
      (blockSeq wordU2 wordV2 (blockSign (2 * (2 * M))) c : ℝ) := by
  rcases blockSeq_wordU2_wordV2_eq_one_or_neg_one M c with h1 | h1
  · have hobs : designObs2 M c = false := by unfold designObs2; rw [h1]; decide
    rw [hobs, h1]; simp
  · have hobs : designObs2 M c = true := by unfold designObs2; rw [h1]; decide
    rw [hobs, h1]; simp

/-! ## The schedule's character sums are the design's own windows -/

private lemma cast_add_val2 (c : ZMod (2 * (2 * M) * 22)) (a i : ℕ) :
    c + ((a + i : ℕ) : ZMod (2 * (2 * M) * 22)) =
      ((c.val + a + i : ℕ) : ZMod (2 * (2 * M) * 22)) := by
  conv_lhs => rw [← ZMod.natCast_zmod_val c]
  push_cast
  ring

private theorem chiSum_eq_singleWindow2 (c : ZMod (2 * (2 * M) * 22)) (a n : ℕ) :
    (∑ t ∈ Finset.range n,
        ALT.chi (TapeHost.traj (designObs2 M) c (t + a))) =
      ((singleWindow (blockSeq wordU2 wordV2 (blockSign (2 * (2 * M)))) (c.val + a) n :
        ℤ) : ℝ) := by
  unfold singleWindow
  push_cast
  apply Finset.sum_congr rfl
  intro t _
  change ALT.chi (designObs2 M (c + ((t + a : ℕ) : ZMod _))) = _
  rw [show (t + a : ℕ) = (a + t : ℕ) from by ring, cast_add_val2 M c a t, chi_designObs2]
  congr 2
  push_cast
  ring

private theorem chiProd_eq_cyclicCorrWindow2 (c : ZMod (2 * (2 * M) * 22)) {a : ℕ} (ha8 : a ≤ 8)
    (n : ℕ) :
    (∑ t ∈ Finset.range n,
        ALT.chi (TapeHost.traj (designObs2 M) c (t + a)) *
          ALT.chi (TapeHost.traj (designObs2 M) c (t + 8))) =
      ((cyclicCorrWindow (blockSeq wordU2 wordV2 (blockSign (2 * (2 * M)))) (8 - a) (c.val + a)
        n : ℤ) : ℝ) := by
  unfold cyclicCorrWindow
  push_cast
  apply Finset.sum_congr rfl
  intro t _
  change ALT.chi (designObs2 M (c + ((t + a : ℕ) : ZMod _))) *
      ALT.chi (designObs2 M (c + ((t + 8 : ℕ) : ZMod _))) = _
  have hidx1 : c + ((t + a : ℕ) : ZMod (2 * (2 * M) * 22))
      = ((c.val + a + t : ℕ) : ZMod (2 * (2 * M) * 22)) := by
    rw [show (t + a : ℕ) = (a + t : ℕ) from by ring]
    exact cast_add_val2 M c a t
  have hidx2 : c + ((t + 8 : ℕ) : ZMod (2 * (2 * M) * 22))
      = ((c.val + a + t : ℕ) : ZMod (2 * (2 * M) * 22)) +
        ((8 - a : ℕ) : ZMod (2 * (2 * M) * 22)) := by
    rw [show (t + 8 : ℕ) = (a + t) + (8 - a) from by omega, cast_add_val2 M c (a + t) (8 - a)]
    push_cast
    ring
  rw [hidx1, hidx2, chi_designObs2, chi_designObs2]
  push_cast
  ring

/-! ## The design meets `Profile` -/

/-- **The second certified design meets `Profile`.** At every phase `c` and
offset `a : Fin 8`, the single-site window bound is `48` and the pair-correlation bound against the
declared correlation is `176` off the rule's own literal `2` and `34` on it — the window bounds
`BlockPairProfile`'s own `cyclicCorrWindow_blockSeq_wordU2_wordV2_zone`/`_spike`,
`singleWindow_blockSeq_wordU2_wordV2_bound` establish, mirroring `BlockPairCriterion.
designObs_profile`. The correlation `-8/11` is `2 * (3/22) - 1`, the density `η = 3/22` this
design's tape carries — see `ShiftedSpikeHost.lean`. -/
theorem designObs2_profile :
    Profile (designObs2 M) 48
      (fun a => if (a : ℕ) = 2 then -8 / 11 else 0)
      (fun a => if (a : ℕ) = 2 then 34 else 176) where
  single := fun c n => by
    change |∑ t ∈ Finset.range n,
        ALT.chi (TapeHost.traj (designObs2 M) c (t + 0))| ≤ (48 : ℝ)
    rw [chiSum_eq_singleWindow2 M c 0 n, ← Int.cast_abs]
    exact_mod_cast singleWindow_blockSeq_wordU2_wordV2_bound M (c.val + 0) n
  pair := fun c a n => by
    have ea : ∀ t : ℕ,
        designObs2 M (c + (t : ℕ) + ((a : ℕ) : ZMod (2 * (2 * M) * 22)))
          = TapeHost.traj (designObs2 M) c (t + (a : ℕ)) := by
      intro t
      change designObs2 M (c + (t : ℕ) + ((a : ℕ) : ZMod (2 * (2 * M) * 22)))
          = designObs2 M (c + ((t + (a : ℕ) : ℕ) : ZMod (2 * (2 * M) * 22)))
      congr 1
      push_cast
      ring
    have e8 : ∀ t : ℕ,
        designObs2 M (c + (t : ℕ) + ((8 : ℕ) : ZMod (2 * (2 * M) * 22)))
          = TapeHost.traj (designObs2 M) c (t + 8) := by
      intro t
      change designObs2 M (c + (t : ℕ) + ((8 : ℕ) : ZMod (2 * (2 * M) * 22)))
          = designObs2 M (c + ((t + 8 : ℕ) : ZMod (2 * (2 * M) * 22)))
      congr 1
      push_cast
      ring
    simp_rw [ea, e8]
    by_cases ha2 : (a : ℕ) = 2
    · rw [ite_eq_left ha2, ite_eq_left ha2, ha2]
      rw [chiProd_eq_cyclicCorrWindow2 M c (by omega : (2 : ℕ) ≤ 8) n]
      have haperiodic : aperiodicCorr wordU2 6 + aperiodicCorr wordV2 6 = -32 := by decide
      have hb := cyclicCorrWindow_blockSeq_wordU2_wordV2_spike M (c.val + 2) n
      rw [haperiodic] at hb
      set X : ℤ := cyclicCorrWindow (blockSeq wordU2 wordV2 (blockSign (2 * (2 * M)))) 6
        (c.val + 2) n with hXdef
      have hbR : |44 * (X : ℝ) + 32 * (n : ℝ)| ≤ 1496 := by
        have heq : (44 : ℝ) * (X : ℝ) + 32 * (n : ℝ) = ((2 * 22 * X - n * (-32) : ℤ) : ℝ) := by
          push_cast; ring
        rw [heq]
        exact_mod_cast hb
      have heq2 : (X : ℝ) - (n : ℝ) * (-8 / 11) = (44 * (X : ℝ) + 32 * (n : ℝ)) / 44 := by ring
      rw [heq2, abs_div]
      rw [show |(44 : ℝ)| = 44 from by norm_num, div_le_iff₀ (by norm_num : (0 : ℝ) < 44)]
      linarith [hbR]
    · rw [ite_eq_right ha2, ite_eq_right ha2, mul_zero, sub_zero]
      have ha8 : (a : ℕ) ≤ 8 := by omega
      rw [chiProd_eq_cyclicCorrWindow2 M c ha8 n, ← Int.cast_abs]
      have haLt := a.isLt
      have hd1 : 1 ≤ 8 - (a : ℕ) := by omega
      have hd8 : 8 - (a : ℕ) ≤ 8 := by omega
      have hd6 : 8 - (a : ℕ) ≠ 6 := by omega
      exact_mod_cast
        cyclicCorrWindow_blockSeq_wordU2_wordV2_zone M hd1 hd8 hd6 (c.val + (a : ℕ)) n

/-! ## The affordable regime's second worked example -/

/-- **The affordable regime's second worked example.** On the second certified design,
`schedSurvivors`'s `2τ`-pruning rule isolates literal `2` at `τ = 1/3` and every
horizon `n > 816` — `designObs2_profile`'s own window bounds (`S = 48`, `Wm = 176`) meet
`schedSurvivors_eq_singleton_at`'s three conditions with room to spare
(`2 * (3/22) = 3/11 ≤ 1/3`, `0 ≤ 1/3`, `3 * (1/3) + 0 ≤ 1`), the design's own density `η = 3/22`
sitting inside the schedule's tolerance rather than exactly at its boundary, unlike the certified
design's `η = 1/6` at `τ = 1/3`. -/
theorem shiftedSpike_identifies (c : ZMod (2 * (2 * M) * 22)) {n : ℕ} (hn : 816 < n) :
    schedSurvivors (1 / 3) n
      (TapeHost.traj (designObs2 M) c) = {(2 : Fin 8)} := by
  have hW : ∀ a : Fin 8, (if (a : ℕ) = 2 then (34 : ℝ) else 176) ≤ 176 := by
    intro a
    by_cases ha : (a : ℕ) = 2
    · rw [ite_eq_left ha]; norm_num
    · rw [ite_eq_right ha]
  have hρj : (if (2 : ℕ) = 2 then (-8 / 11 : ℝ) else 0) = 2 * ((3 : ℝ) / 22) - 1 := by norm_num
  have hρ : ∀ a : Fin 8, a ≠ (2 : Fin 8) →
      |(if (a : ℕ) = 2 then (-8 / 11 : ℝ) else 0)| ≤ (0 : ℝ) := by
    intro a ha
    have ha' : (a : ℕ) ≠ 2 := by
      intro hcontra
      exact ha (by ext; simpa using hcontra)
    simp [ha']
  have hn' : (2 * 48 + 176 : ℝ) / (1 / 3) < (n : ℝ) := by
    have hnR : (816 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    norm_num
    linarith [hnR]
  exact schedSurvivors_eq_singleton_at (o := designObs2 M) (j := (2 : Fin 8))
    (h := designObs2_profile M) (Wm := 176) (hW := hW) (hτ := by norm_num) (hη := by norm_num)
    (hρj := hρj) (hρ := hρ) (_hμ0 := by norm_num) (hbudget := by norm_num)
    (hμτ := by norm_num) (hsep := by norm_num) (c := c) (hn1 := by omega) (hn := hn')

end ALT

/-! ## Axiom audit -/

/-- info: 'ALT.designObs2_profile' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.designObs2_profile

set_option linter.style.longLine false in
/-- info: 'ALT.shiftedSpike_identifies' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.shiftedSpike_identifies
