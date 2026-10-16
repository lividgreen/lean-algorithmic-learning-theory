module

public import ALT.BlockPairProfile
public import ALT.NoisyWindowChain
public import ALT.TapeHostObservability
public import ALT.TapeHostOverlap
public import ALT.TapeHostSchedule
public import ALT.BlockPairHost
public import ALT.BlockPairCriterion
public import ALT.ParityWalk

/-!
# The profile-class family instantiates the profile-class criterion, at every length

`BlockPairProfile.lean` extends the certified block-pair sequence (`wordU`/`wordV`, [Inevitability]
§5 Theorem 5.8) to a family, one member per length `8 * r`: `antiExt seedU r`/`antiExt seedV r`,
`r = 3` being the certified pair (`antiExt_seedU_three`/`antiExt_seedV_three`). This module reads
that family as an observation sequence (`designObsF`), ties it to the noisy-window-chain vocabulary
at general `r` (mirroring `BlockPairObservability.lean`'s three ties), certifies it meets
`Profile` (`designObsF_profile`, mirroring `BlockPairCriterion.designObs_
profile`), and instantiates [Inevitability] §5 Proposition 5.9's class-level criterion
(`TapeHost.overlap`) and §6 Proposition 6.10's identification window
(`identifies_of_lt_quarter`) at every member with `r ≥ 3`: every member of the
family is in both route-classes and identifies at its own horizon, with slack growing in `r`.

## Main results

* `designObsF` — the family's design at extension count `r`, read as a Boolean observation.
* `chi_designObsF`, `chiSum_eq_singleWindowF`, `chiProd_eq_cyclicCorrWindowF` — the three ties, at
  general `r`, mirroring `BlockPairObservability.lean`'s certified-pair ties.
* `designObsF_profile` — the family meets `Profile` at every `r ≥ 2`, at the
  window bounds `cyclicCorrWindow_blockSeq_family_zone/_spike`/
  `singleWindow_blockSeq_family_bound` establish.
* `designObsF_three_eq` — the certified design IS the family's `r = 3` member.
* `blockPairFamily_overlap` — every member with `r ≥ 2` is simultaneously in `𝒮_E` and `𝒮_L`, at
  `TapeHost.overlap`'s coupled numeral standard.
* `blockPairFamily_identifies` — every member with `r ≥ 3` identifies the true literal, at
  `identifies_of_lt_quarter`'s sharp window, density `η = 1 / (2 * r)`.
* `designObsF_three_overlap_eq` — the `r = 3` instance of `blockPairFamily_overlap` IS
  `blockPair_overlap_coupled`, up to `designObsF_three_eq`: the family
  generalizes the certified case rather than replacing it.

## Scope

One architecture, one seed pair, a family along length: the window bounds this module reads off
`BlockPairProfile.lean` are the same shape as the certified pair's, with the spike remainder
constant `32` in place of the certified pair's tight `14` (a crude but `r`-uniform bound; see
`blockRemainder_antiExt_bound`'s own docstring) — so `designObsF_profile`'s window
bound at offset `0` is a constant `64`, not the certified pair's `46`, while the single-site and
cross-class bounds keep the certified pair's own shape. Nothing about approximate zones (`μ > 0`)
or about survival; not the class-level bridge [Inevitability] §7 names. The paper home is
[Inevitability] §5 Proposition 5.9, §6 Proposition 6.10, rows IN-41, IN-42, IN-43.
-/


@[expose] public section

namespace ALT

/-! ## The family's design, read as a Boolean observation -/

/-- **The family's design**, at extension count `r`: `true` exactly where the assembled sequence's
value is `-1`, mirroring `BlockPairHost.designObs`'s own reading of the certified pair. -/
noncomputable def designObsF (r M : ℕ) [NeZero (2 * (2 * M))] [NeZero r] :
    ZMod (2 * (2 * M) * (8 * r)) → Bool :=
  fun u => decide (blockSeq (antiExt seedU r) (antiExt seedV r) (blockSign (2 * (2 * M))) u = -1)

/-! ## Tie (i): the design is exactly `±1`-valued -/

private lemma blockSeq_antiExt_sq (M r : ℕ) [NeZero (2 * (2 * M))] [NeZero r]
    (x : ZMod (2 * (2 * M) * (8 * r))) :
    blockSeq (antiExt seedU r) (antiExt seedV r) (blockSign (2 * (2 * M))) x *
      blockSeq (antiExt seedU r) (antiExt seedV r) (blockSign (2 * (2 * M))) x = 1 := by
  rw [blockSeq_val]
  have hr1 : 1 ≤ r := NeZero.pos r
  have hxlt : x.val < 2 * (2 * M) * (8 * r) := ZMod.val_lt x
  have hxlt2 : x.val < 8 * r * (2 * (2 * M)) := by
    rw [Nat.mul_comm (8 * r) (2 * (2 * M))]
    exact hxlt
  have hdivlt : x.val / (8 * r) < 2 * (2 * M) := Nat.div_lt_of_lt_mul hxlt2
  have hε := blockSign_sq (2 * (2 * M)) ⟨x.val / (8 * r), hdivlt⟩
  split_ifs
  · have hu := antiExt_sq seedU seedU_sq r ⟨x.val % (8 * r), Nat.mod_lt _ (by omega)⟩
    calc blockSign (2 * (2 * M)) ⟨x.val / (8 * r), hdivlt⟩ *
          antiExt seedU r ⟨x.val % (8 * r), _⟩ *
          (blockSign (2 * (2 * M)) ⟨x.val / (8 * r), hdivlt⟩ *
            antiExt seedU r ⟨x.val % (8 * r), _⟩)
        = (blockSign (2 * (2 * M)) ⟨x.val / (8 * r), hdivlt⟩ *
            blockSign (2 * (2 * M)) ⟨x.val / (8 * r), hdivlt⟩) *
            (antiExt seedU r ⟨x.val % (8 * r), _⟩ * antiExt seedU r ⟨x.val % (8 * r), _⟩) := by
          ring
      _ = 1 * 1 := by rw [hε, hu]
      _ = 1 := by ring
  · have hv := antiExt_sq seedV seedV_sq r ⟨x.val % (8 * r), Nat.mod_lt _ (by omega)⟩
    calc blockSign (2 * (2 * M)) ⟨x.val / (8 * r), hdivlt⟩ *
          antiExt seedV r ⟨x.val % (8 * r), _⟩ *
          (blockSign (2 * (2 * M)) ⟨x.val / (8 * r), hdivlt⟩ *
            antiExt seedV r ⟨x.val % (8 * r), _⟩)
        = (blockSign (2 * (2 * M)) ⟨x.val / (8 * r), hdivlt⟩ *
            blockSign (2 * (2 * M)) ⟨x.val / (8 * r), hdivlt⟩) *
            (antiExt seedV r ⟨x.val % (8 * r), _⟩ * antiExt seedV r ⟨x.val % (8 * r), _⟩) := by
          ring
      _ = 1 * 1 := by rw [hε, hv]
      _ = 1 := by ring

private lemma blockSeq_antiExt_eq_one_or_neg_one (M r : ℕ) [NeZero (2 * (2 * M))] [NeZero r]
    (x : ZMod (2 * (2 * M) * (8 * r))) :
    blockSeq (antiExt seedU r) (antiExt seedV r) (blockSign (2 * (2 * M))) x = 1 ∨
      blockSeq (antiExt seedU r) (antiExt seedV r) (blockSign (2 * (2 * M))) x = -1 := by
  have hsq := blockSeq_antiExt_sq M r x
  have hz : (blockSeq (antiExt seedU r) (antiExt seedV r) (blockSign (2 * (2 * M))) x - 1) *
      (blockSeq (antiExt seedU r) (antiExt seedV r) (blockSign (2 * (2 * M))) x + 1) = 0 := by
    nlinarith [hsq]
  rcases mul_eq_zero.mp hz with h1 | h1
  · left; omega
  · right; omega

/-- **Tie (i).** The family's design's value at every point equals `−1` exactly where `designObsF`
reads `true`, and `+1` where it reads `false`, mirroring `BlockPairHost.chi_designObs`. -/
theorem chi_designObsF (M r : ℕ) [NeZero (2 * (2 * M))] [NeZero r]
    (c : ZMod (2 * (2 * M) * (8 * r))) :
    ALT.chi (designObsF r M c) =
      (blockSeq (antiExt seedU r) (antiExt seedV r) (blockSign (2 * (2 * M))) c : ℝ) := by
  rcases blockSeq_antiExt_eq_one_or_neg_one M r c with h1 | h1
  · have hobs : designObsF r M c = false := by unfold designObsF; rw [h1]; decide
    rw [hobs, h1]; simp
  · have hobs : designObsF r M c = true := by unfold designObsF; rw [h1]; decide
    rw [hobs, h1]; simp

/-! ## Tie (iii): the schedule's own character sums are the design's own windows -/

private lemma cast_add_valF (M r : ℕ) [NeZero (2 * (2 * M))] [NeZero r]
    (c : ZMod (2 * (2 * M) * (8 * r))) (a i : ℕ) :
    c + ((a + i : ℕ) : ZMod (2 * (2 * M) * (8 * r))) =
      ((c.val + a + i : ℕ) : ZMod (2 * (2 * M) * (8 * r))) := by
  conv_lhs => rw [← ZMod.natCast_zmod_val c]
  push_cast
  ring

/-- **Tie (iii), single-site**, mirroring `BlockPairHost.chiSum_eq_singleWindow`. -/
theorem chiSum_eq_singleWindowF (M r : ℕ) [NeZero (2 * (2 * M))] [NeZero r]
    (c : ZMod (2 * (2 * M) * (8 * r))) (a n : ℕ) :
    (∑ t ∈ Finset.range n, ALT.chi (TapeHost.traj (designObsF r M) c
      (t + a))) =
      ((singleWindow (blockSeq (antiExt seedU r) (antiExt seedV r) (blockSign (2 * (2 * M))))
        (c.val + a) n : ℤ) : ℝ) := by
  unfold singleWindow
  push_cast
  apply Finset.sum_congr rfl
  intro t _
  change ALT.chi (designObsF r M (c + ((t + a : ℕ) : ZMod _))) = _
  rw [show (t + a : ℕ) = (a + t : ℕ) from by ring, cast_add_valF M r c a t, chi_designObsF]
  congr 2
  push_cast
  ring

/-- **Tie (iii), pair**, mirroring `BlockPairHost.chiProd_eq_cyclicCorrWindow`. -/
theorem chiProd_eq_cyclicCorrWindowF (M r : ℕ) [NeZero (2 * (2 * M))] [NeZero r]
    (c : ZMod (2 * (2 * M) * (8 * r))) {a : ℕ} (ha8 : a ≤ 8) (n : ℕ) :
    (∑ t ∈ Finset.range n,
        ALT.chi (TapeHost.traj (designObsF r M) c (t + a)) *
        ALT.chi (TapeHost.traj (designObsF r M) c (t + 8))) =
      ((cyclicCorrWindow (blockSeq (antiExt seedU r) (antiExt seedV r) (blockSign (2 * (2 * M))))
        (8 - a) (c.val + a) n : ℤ) : ℝ) := by
  unfold cyclicCorrWindow
  push_cast
  apply Finset.sum_congr rfl
  intro t _
  change ALT.chi (designObsF r M (c + ((t + a : ℕ) : ZMod _))) *
      ALT.chi (designObsF r M (c + ((t + 8 : ℕ) : ZMod _))) = _
  have hidx1 : c + ((t + a : ℕ) : ZMod (2 * (2 * M) * (8 * r)))
      = ((c.val + a + t : ℕ) : ZMod (2 * (2 * M) * (8 * r))) := by
    rw [show (t + a : ℕ) = (a + t : ℕ) from by ring]
    exact cast_add_valF M r c a t
  have hidx2 : c + ((t + 8 : ℕ) : ZMod (2 * (2 * M) * (8 * r)))
      = ((c.val + a + t : ℕ) : ZMod (2 * (2 * M) * (8 * r))) +
        ((8 - a : ℕ) : ZMod (2 * (2 * M) * (8 * r))) := by
    rw [show (t + 8 : ℕ) = (a + t) + (8 - a) from by omega, cast_add_valF M r c (a + t) (8 - a)]
    push_cast
    ring
  rw [hidx1, hidx2, chi_designObsF, chi_designObsF]
  push_cast
  ring

/-! ## The family meets the profile-class criterion -/

/-- **The family meets `Profile`**, at every `r ≥ 2`. The single-site bound
`2 * (4 + 8 * r)` and the cross-class window bound `2 * ((2 + 2 * 1) * (8 * r))` keep the certified
pair's own shape (`singleWindow_blockSeq_family_bound`, `cyclicCorrWindow_blockSeq_family_zone`);
the same-class window bound is the constant `64` — `4 * 1 * 8 + 32` off
`cyclicCorrWindow_blockSeq_family_spike`'s own crude remainder constant `32`, in place of the
certified pair's `46` (`4 * 1 * 8 + 14`). -/
theorem designObsF_profile (M r : ℕ) [NeZero (2 * (2 * M))] [NeZero r] (hr2 : 2 ≤ r) :
    Profile (designObsF r M) (2 * ((4 : ℝ) + 8 * r))
      (fun a => if (a : ℕ) = 0 then -((8 * r - 8 : ℝ) / (8 * r)) else 0)
      (fun a => if (a : ℕ) = 0 then (64 : ℝ) else 2 * ((2 + 2 * 1) * (8 * r : ℝ))) where
  single := fun c n => by
    change |∑ t ∈ Finset.range n,
        ALT.chi (TapeHost.traj (designObsF r M) c (t + 0))| ≤
        2 * ((4 : ℝ) + 8 * r)
    rw [chiSum_eq_singleWindowF M r c 0 n, ← Int.cast_abs]
    have h := singleWindow_blockSeq_family_bound M r (c.val + 0) n
    exact_mod_cast h
  pair := fun c a n => by
    have ea : ∀ t : ℕ,
        designObsF r M (c + (t : ℕ) + ((a : ℕ) : ZMod (2 * (2 * M) * (8 * r))))
          = TapeHost.traj (designObsF r M) c (t + (a : ℕ)) := by
      intro t
      change designObsF r M (c + (t : ℕ) + ((a : ℕ) : ZMod (2 * (2 * M) * (8 * r))))
          = designObsF r M (c + ((t + (a : ℕ) : ℕ) : ZMod (2 * (2 * M) * (8 * r))))
      congr 1
      push_cast
      ring
    have e8 : ∀ t : ℕ,
        designObsF r M (c + (t : ℕ) + ((8 : ℕ) : ZMod (2 * (2 * M) * (8 * r))))
          = TapeHost.traj (designObsF r M) c (t + 8) := by
      intro t
      change designObsF r M (c + (t : ℕ) + ((8 : ℕ) : ZMod (2 * (2 * M) * (8 * r))))
          = designObsF r M (c + ((t + 8 : ℕ) : ZMod (2 * (2 * M) * (8 * r))))
      congr 1
      push_cast
      ring
    simp_rw [ea, e8]
    by_cases ha0 : (a : ℕ) = 0
    · rw [ite_eq_left ha0, ite_eq_left ha0, ha0]
      rw [chiProd_eq_cyclicCorrWindowF M r c (by omega : (0 : ℕ) ≤ 8) n]
      have hb := cyclicCorrWindow_blockSeq_family_spike M r hr2 (c.val + 0) n
      set X : ℤ := cyclicCorrWindow
        (blockSeq (antiExt seedU r) (antiExt seedV r) (blockSign (2 * (2 * M)))) 8
        (c.val + 0) n with hXdef
      have hspU := aperiodicCorr_antiExt_spike seedU seedU_sq r (by omega)
      have hspV := aperiodicCorr_antiExt_spike seedV seedV_sq r (by omega)
      rw [hspU, hspV] at hb
      have hbR : |2 * (8 * r : ℝ) * (X : ℝ) -
          (n : ℝ) * (-(8 * (r : ℝ) - 8) + -(8 * (r : ℝ) - 8))|
          ≤ 2 * ((4 * 1 * (8 : ℝ) + 32) * (8 * r : ℝ)) := by
        have heq : (2 * (8 * r : ℝ) * (X : ℝ) -
            (n : ℝ) * (-(8 * (r : ℝ) - 8) + -(8 * (r : ℝ) - 8))) =
            ((2 * (8 * r : ℤ) * X - (n : ℤ) * (-(8 * (r : ℤ) - 8) + -(8 * (r : ℤ) - 8)) : ℤ) :
              ℝ) := by
          push_cast; ring
        rw [heq]
        exact_mod_cast hb
      have heq2 : (X : ℝ) - (n : ℝ) * (-((8 * r - 8 : ℝ) / (8 * r))) =
          (2 * (8 * r : ℝ) * (X : ℝ) - (n : ℝ) *
            (-(8 * (r : ℝ) - 8) + -(8 * (r : ℝ) - 8))) / (2 * (8 * r : ℝ)) := by
        have hr0 : (8 * (r : ℝ)) ≠ 0 := by
          have hrpos : (0 : ℝ) < (r : ℝ) := by exact_mod_cast NeZero.pos r
          positivity
        field_simp
        ring
      rw [heq2, abs_div]
      have habs2r : |(2 * (8 * r : ℝ))| = 2 * (8 * r : ℝ) := by
        rw [abs_of_nonneg]; positivity
      rw [habs2r, div_le_iff₀ (by positivity : (0 : ℝ) < 2 * (8 * r : ℝ))]
      nlinarith [hbR]
    · rw [ite_eq_right ha0, ite_eq_right ha0, mul_zero, sub_zero]
      have ha7 : (a : ℕ) ≤ 8 := by omega
      rw [chiProd_eq_cyclicCorrWindowF M r c ha7 n, ← Int.cast_abs]
      have hz := cyclicCorrWindow_blockSeq_family_zone M r (by omega : 1 ≤ 8 - (a : ℕ))
        (by omega : 8 - (a : ℕ) ≤ 7) (c.val + (a : ℕ)) n
      exact_mod_cast hz

/-! ## The certified pair is the `r = 3` member -/

/-- **The certified design IS the family's `r = 3` member.** -/
theorem designObsF_three_eq (M : ℕ) [NeZero (2 * (2 * M))] :
    designObsF 3 M = BlockPairHost.designObs M := by
  funext u
  unfold designObsF BlockPairHost.designObs
  rw [antiExt_seedU_three, antiExt_seedV_three]

/-! ## Every member is in both route-classes, at `r ≥ 2` -/

/-- **Every member of the family is in both route-classes.** At `r ≥ 2`, the family's design is
simultaneously a member of `𝒮_E` and of `𝒮_L`, at `TapeHost.overlap`'s own coupled
numeral standard — the certified pair's own `blockPair_overlap_coupled` (`BlockPairCriterion.lean`)
is the `r = 3` instance (`designObsF_three_overlap_eq`). -/
theorem blockPairFamily_overlap (r M : ℕ) (hr2 : 2 ≤ r) [NeZero (2 * (2 * M))] [NeZero r] :
    ∃ gTS, ∀ (τ : ℝ), 2 * (1 / (2 * r) : ℝ) ≤ τ → ∀ (K : ℝ),
      (8 : ℝ) + ALT.capacity (Nat.clog 2 (gTS + 1)) ≤ K →
      ALT.hostsAt (TapeHost.frameBits (2 * (2 * M) * (8 * r))) gTS →
      ALT.SubstrateE
        (TapeHost.subUpdate (2 * (2 * M) * (8 * r)) (designObsF r M))
        (TapeHost.codeRegion (2 * (2 * M) * (8 * r))) 3 K (2 * K) 1 2 3 (1 / 2) 8 gTS
        True True True True
        (ALT.GrowsLawfulGuestOf
          (TapeHost.packed (2 * (2 * M) * (8 * r)) (designObsF r M))
          (TapeHost.frame (2 * (2 * M) * (8 * r)) (designObsF r M)))
        (ALT.GrownGuestReachesThresholdAt
          (TapeHost.frameBits (2 * (2 * M) * (8 * r))) gTS) ∧
      ALT.SubstrateL
        (TapeHost.subUpdate (2 * (2 * M) * (8 * r)) (designObsF r M))
        (TapeHost.codeRegion (2 * (2 * M) * (8 * r))) 3 K (2 * K) 1 2 3 (1 / 2) 8 gTS
        True True True True
        (TapeHost.Realizable (2 * (2 * M) * (8 * r)) (designObsF r M))
        (ALT.ChainWindowBudget 8 (1 / (2 * r)) τ) := by
  obtain ⟨gTS, hgTS⟩ := TapeHost.overlap
  refine ⟨gTS, fun τ hτ K hK hhost => ?_⟩
  exact hgTS (2 * (2 * M) * (8 * r)) (designObsF r M) _ _ _ (designObsF_profile M r hr2)
    (1 / (2 * r)) τ (by positivity) hτ K hK hhost

/-- **The `r = 3` instance ties back to the certified overlap.** Up to `designObsF_three_eq`,
`blockPairFamily_overlap` at `r = 3` IS `blockPair_overlap_coupled` — the
family generalizes the certified case rather than replacing it. -/
theorem designObsF_three_overlap_eq (M : ℕ) [NeZero (2 * (2 * M))] :
    ∃ gTS, ∀ (τ : ℝ), 2 * (1 / 6 : ℝ) ≤ τ → ∀ (K : ℝ),
      (8 : ℝ) + ALT.capacity (Nat.clog 2 (gTS + 1)) ≤ K →
      ALT.hostsAt (TapeHost.frameBits (2 * (2 * M) * (8 * 3))) gTS →
      ALT.SubstrateE
        (TapeHost.subUpdate (2 * (2 * M) * (8 * 3)) (designObsF 3 M))
        (TapeHost.codeRegion (2 * (2 * M) * (8 * 3))) 3 K (2 * K) 1 2 3 (1 / 2) 8 gTS
        True True True True
        (ALT.GrowsLawfulGuestOf
          (TapeHost.packed (2 * (2 * M) * (8 * 3)) (designObsF 3 M))
          (TapeHost.frame (2 * (2 * M) * (8 * 3)) (designObsF 3 M)))
        (ALT.GrownGuestReachesThresholdAt
          (TapeHost.frameBits (2 * (2 * M) * (8 * 3))) gTS) ∧
      ALT.SubstrateL
        (TapeHost.subUpdate (2 * (2 * M) * (8 * 3)) (designObsF 3 M))
        (TapeHost.codeRegion (2 * (2 * M) * (8 * 3))) 3 K (2 * K) 1 2 3 (1 / 2) 8 gTS
        True True True True
        (TapeHost.Realizable (2 * (2 * M) * (8 * 3)) (designObsF 3 M))
        (ALT.ChainWindowBudget 8 (1 / 6) τ) := by
  rw [designObsF_three_eq]
  obtain ⟨gTS, h⟩ := blockPair_overlap_coupled
  exact ⟨gTS, h M⟩

/-! ## Every member identifies the true literal, at `r ≥ 3` -/

/-- **Every member of the family, from `r = 3` on, identifies the true literal.** Density
`η = 1 / (2 * r)` sits inside `identifies_of_lt_quarter`'s window `η < 1 / 4`
exactly for `r ≥ 3` — the certified pair's own `r = 3` at density `1 / 6`; slack grows with `r`. -/
theorem blockPairFamily_identifies (r M : ℕ) (hr3 : 3 ≤ r) [NeZero (2 * (2 * M))] [NeZero r]
    (c : ZMod (2 * (2 * M) * (8 * r))) :
    ∃ τ : ℝ, 0 < τ ∧ 2 * (1 / (2 * r) : ℝ) ≤ τ ∧
      ∀ n : ℕ, sharpHorizon (2 * ((4 : ℝ) + 8 * r))
          (2 * ((2 + 2 * 1) * (8 * r : ℝ))) (1 / (2 * r)) τ 0 ≤ n →
        schedSurvivors τ n
          (TapeHost.traj (designObsF r M) c) = {0} := by
  have hr2 : 2 ≤ r := by omega
  have hrpos : (0 : ℝ) < (r : ℝ) := by exact_mod_cast (by omega : 0 < r)
  have hr2R : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr2
  have hρ0 : (fun a : Fin 8 => if (a : ℕ) = 0 then -((8 * (r : ℝ) - 8) / (8 * r)) else (0 : ℝ))
      (0 : Fin 8) = 2 * (1 / (2 * r) : ℝ) - 1 := by
    simp only [Fin.val_zero, ite_true]
    have hr0 : (8 * (r : ℝ)) ≠ 0 := by positivity
    field_simp
    ring
  have hW : ∀ a : Fin 8, (fun a : Fin 8 => if (a : ℕ) = 0 then (64 : ℝ)
      else 2 * ((2 + 2 * 1) * (8 * r : ℝ))) a ≤ 2 * ((2 + 2 * 1) * (8 * r : ℝ)) := by
    intro a
    by_cases ha : (a : ℕ) = 0
    · simp only [ha, ite_true]
      have heq : 2 * ((2 + 2 * (1 : ℝ)) * (8 * (r : ℝ))) = 64 * r := by ring
      rw [heq]
      nlinarith [hr2R]
    · simp only [ha, ite_false, le_refl]
  have hwin : (1 / (2 * (r : ℝ)) : ℝ) < (1 - 0) / 4 := by
    rw [show (1 : ℝ) - 0 = 1 by ring, div_lt_div_iff₀ (by positivity) (by norm_num)]
    have hr3' : (3 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr3
    nlinarith [hr3']
  exact identifies_of_lt_quarter (designObsF r M) (designObsF_profile M r hr2)
    (2 * ((2 + 2 * 1) * (8 * r : ℝ))) hW (by positivity) hρ0
    (fun a ha => by simp only [ha, ite_false]; norm_num) (le_refl 0) (by norm_num) hwin c

end ALT
