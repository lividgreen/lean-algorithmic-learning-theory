module

public import ALT.BlockPairOverlap
public import ALT.TapeHostFiber
public import ALT.TapeHostOverlap
public import ALT.TapeHostSchedule

/-!
# The certified block-pair sequence instantiates the profile-class criterion

`TapeHostWitness.lean`/`TapeHostOverlap.lean` state the block-pair pipeline over an arbitrary
observation sequence and window-deviation profile. This module certifies that the certified
block-pair design (`BlockPairProfile.designObs`, via `BlockPairHost`) meets that profile at the
SAME window constants `BlockPairHost.deviation_bound_same`/`BlockPairHost.deviation_bound_cross`
already establish (`BlockPairHost.designObs_profile`), ties the general host to the certified one at
that instance (`BlockPairHost.tape_eq_tapeHost_tape`, `BlockPairHost.update_eq`,
`BlockPairHost.subUpdate_eq`), records the tape's own derived density (`blockPair_density`), and
instantiates the class-level overlap (`TapeHost.overlap`) at the certified design to get the
certified host into BOTH route-classes at the coupled numeral standard (`blockPair_overlap_coupled`)
— alongside, not in place of, `BlockPairHost.witness_overlap`'s own registered [Inevitability] §5
Theorem 5.8 boundary at the decoupled numerals.

## Main results

* `BlockPairHost.designObs_profile` — the certified design meets `Profile` at `S = 56`,
  the zero/`-2/3` correlations and `192`/`46` window bounds `BlockPairObservability`'s own
  `BlockPairHost.deviation_bound_cross`/`BlockPairHost.deviation_bound_same` already establish.
* `BlockPairHost.tape_eq_tapeHost_tape`, `BlockPairHost.update_eq`, `BlockPairHost.subUpdate_eq` —
  the certified host IS the general host at `o := BlockPairHost.designObs M`,
  `N := 2 * (2 * M) * 24`.
* `blockPair_density` — the certified design's own tape density: `2 · #{tape = true} = 32 · M`,
  from `TapeHost.tape_density` and `blockSeq_wordU_wordV_correlation`'s lag-`8` value
  `-64 · M`.
* `blockPair_noiseCount` — `TapeHost.noiseCount_tapeStream_bounds` at the certified design's
  own profile and density `η = 1/6`: the fiber-facing noise count tracks `n/6` within `23`.
* `blockPair_overlap_coupled` — **the certified instance of the class-level overlap**: the
  certified host is simultaneously a member of `𝒮_E` and of `𝒮_L`, at `TapeHost.overlap`'s
  own coupled numeral standard, from the certified design's profile at
  `η = 1/6`.
* `BlockPairHost.traj_eq` — the certified host's own trajectory IS `TapeHost.traj` at
  `o := BlockPairHost.designObs M` (definitional, as
  `BlockPairHost.tape_eq_tapeHost_tape`/`BlockPairHost.update_eq` are).
* `blockPair_identifies` — **the affordable regime's worked example, at the certified design**:
  `schedSurvivors`'s `2τ`-pruning rule isolates the true literal from the
  certified design's own profile, at `τ = 1/3` and every horizon past `912`.

## Scope

`blockPair_overlap_coupled` is NOT `BlockPairHost.witness_overlap` restated: that theorem
stays untouched, byte-identical, registering [Inevitability] §5 Theorem 5.8's own boundary at the
DECOUPLED numerals (class `g(T_S) = 2` at `K = 108`, crossing at the excess Gödel size). This
module's own capstone is the coupled standard `TapeHostOverlap`'s class-level constructor forces —
a second, independent witness that the certified host clears IN-24's coupling standard too, not a
replacement for the registered result.

Anchors: [Inevitability] §5 Theorem 5.8, rows IN-14, IN-37, IN-38.
-/


@[expose] public section

namespace ALT

/-! ## The certified design meets the profile -/

/-- **The certified design meets `Profile`.** At every phase `c` and offset
`a : Fin 8`, the single-site window bound is `56` and the pair-correlation bound against the
declared correlation is `192` off the rule's own literal and `46` on it — exactly
`BlockPairHost.deviation_bound_cross`/`BlockPairHost.deviation_bound_same`'s own `hSa`/`hSb`/`hW`
derivations, restated as the profile's two fields. -/
theorem BlockPairHost.designObs_profile (M : ℕ) [NeZero (2 * (2 * M))] :
    Profile (BlockPairHost.designObs M) 56
      (fun a => if (a : ℕ) = 0 then -2 / 3 else 0)
      (fun a => if (a : ℕ) = 0 then 46 else 192) where
  single := fun c n => by
    change |∑ t ∈ Finset.range n,
        ALT.chi (BlockPairHost.traj M c (t + 0))| ≤ (56 : ℝ)
    rw [BlockPairHost.chiSum_eq_singleWindow M c 0 n, ← Int.cast_abs]
    exact_mod_cast singleWindow_blockSeq_wordU_wordV_bound M (c.val + 0) n
  pair := fun c a n => by
    have ea : ∀ t : ℕ,
        BlockPairHost.designObs M (c + (t : ℕ) + ((a : ℕ) : ZMod (2 * (2 * M) * 24)))
          = BlockPairHost.traj M c (t + (a : ℕ)) := by
      intro t
      change BlockPairHost.designObs M (c + (t : ℕ) + ((a : ℕ) : ZMod (2 * (2 * M) * 24)))
          = BlockPairHost.designObs M (c + ((t + (a : ℕ) : ℕ) : ZMod (2 * (2 * M) * 24)))
      congr 1
      push_cast
      ring
    have e8 : ∀ t : ℕ,
        BlockPairHost.designObs M (c + (t : ℕ) + ((8 : ℕ) : ZMod (2 * (2 * M) * 24)))
          = BlockPairHost.traj M c (t + 8) := by
      intro t
      change BlockPairHost.designObs M (c + (t : ℕ) + ((8 : ℕ) : ZMod (2 * (2 * M) * 24)))
          = BlockPairHost.designObs M (c + ((t + 8 : ℕ) : ZMod (2 * (2 * M) * 24)))
      congr 1
      push_cast
      ring
    simp_rw [ea, e8]
    by_cases ha0 : (a : ℕ) = 0
    · rw [ite_eq_left ha0, ite_eq_left ha0, ha0]
      rw [BlockPairHost.chiProd_eq_cyclicCorrWindow M c (by omega : (0 : ℕ) ≤ 8) n]
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
    · rw [ite_eq_right ha0, ite_eq_right ha0, mul_zero, sub_zero]
      have ha7 : (a : ℕ) ≤ 8 := by omega
      rw [BlockPairHost.chiProd_eq_cyclicCorrWindow M c ha7 n, ← Int.cast_abs]
      exact_mod_cast cyclicCorrWindow_blockSeq_wordU_wordV_zone M
        (by omega : 1 ≤ 8 - (a : ℕ)) (by omega : 8 - (a : ℕ) ≤ 7) (c.val + (a : ℕ)) n

/-! ## The ties between the general and certified hosts -/

/-- The certified host's tape IS the general host's tape at `o := BlockPairHost.designObs M`. -/
theorem BlockPairHost.tape_eq_tapeHost_tape (M : ℕ) [NeZero (2 * (2 * M))] :
    BlockPairHost.tape M = TapeHost.tape (BlockPairHost.designObs M) := rfl

/-- The certified host's update IS the general host's update at `o := BlockPairHost.designObs M`. -/
theorem BlockPairHost.update_eq (M : ℕ) [NeZero (2 * (2 * M))] :
    BlockPairHost.update M = TapeHost.tapeUpdate (BlockPairHost.designObs M) := rfl

/-- The certified witness's substrate update IS the general witness's substrate update at
`N := 2 * (2 * M) * 24`, `o := BlockPairHost.designObs M`. -/
theorem BlockPairHost.subUpdate_eq (M : ℕ) [NeZero (2 * (2 * M))] :
    BlockPairHost.subUpdate M
      = TapeHost.subUpdate (2 * (2 * M) * 24) (BlockPairHost.designObs M) := by
  funext s x
  cases x with
  | inl i => rfl
  | inr y => cases y with
    | inl i => rfl
    | inr j => rfl

/-! ## The tape's own derived density -/

private lemma sum_mul_sub_eq_cyclicCorr {N : ℕ} [NeZero N] (x : ZMod N → ℤ) :
    (∑ u : ZMod N, x u * x (u - 8)) = cyclicCorr x 8 := by
  have hcancel : ∀ i : ZMod N, i - 8 + 8 = i := fun i => by ring
  have hcomp := Equiv.sum_comp (Equiv.subRight (8 : ZMod N)) (fun y => x (y + 8) * x y)
  simp only [Equiv.subRight_apply, hcancel] at hcomp
  unfold cyclicCorr
  rw [hcomp]
  exact Finset.sum_congr rfl (fun i _ => mul_comm (x (i + 8)) (x i))

/-- **The tape's own derived density.** From `TapeHost.tape_density` and the certified
pair's own exact lag-`8` correlation `-64 · M` (`blockSeq_wordU_wordV_correlation`): `N = 96 · M`,
so `2 · #{tape = true} = 96 · M - 64 · M = 32 · M` — a density of `1/6`, IN-14's/IN-37's `η`. -/
theorem blockPair_density (M : ℕ) [NeZero (2 * (2 * M))] :
    (2 * (Finset.univ.filter (fun u : ZMod (2 * (2 * M) * 24) =>
      TapeHost.tape (BlockPairHost.designObs M) u = true)).card : ℝ) = 32 * (M : ℝ) := by
  have hden := TapeHost.tape_density (2 * (2 * M) * 24) (BlockPairHost.designObs M)
  have hchi : ∀ u : ZMod (2 * (2 * M) * 24), ALT.chi (BlockPairHost.designObs M u)
      = (blockSeq wordU wordV (blockSign (2 * (2 * M))) u : ℝ) :=
    BlockPairHost.chi_designObs M
  have hzeq := sum_mul_sub_eq_cyclicCorr (blockSeq wordU wordV (blockSign (2 * (2 * M))))
  have hcast : ((∑ u : ZMod (2 * (2 * M) * 24), blockSeq wordU wordV (blockSign (2 * (2 * M))) u
      * blockSeq wordU wordV (blockSign (2 * (2 * M))) (u - 8) : ℤ) : ℝ)
      = ((cyclicCorr (blockSeq wordU wordV (blockSign (2 * (2 * M)))) 8 : ℤ) : ℝ) := by
    exact_mod_cast hzeq
  have hsum_eq : (∑ u : ZMod (2 * (2 * M) * 24), ALT.chi (BlockPairHost.designObs M u) *
      ALT.chi (BlockPairHost.designObs M (u - 8)))
      = ((cyclicCorr (blockSeq wordU wordV (blockSign (2 * (2 * M)))) 8 : ℤ) : ℝ) := by
    rw [← hcast]
    push_cast
    exact Finset.sum_congr rfl (fun u _ => by rw [hchi u, hchi (u - 8)])
  rw [hsum_eq, (blockSeq_wordU_wordV_correlation M).2] at hden
  push_cast at hden
  linarith [hden]

/-! ## The fiber-facing noise count, at the certified density -/

/-- **The certified instance of `TapeHost.noiseCount_tapeStream_bounds`.**
`BlockPairHost.designObs_profile`'s own window bounds at `a = 0` (`ρ 0 = -2/3`, `W 0 = 46`) meet
`ρ 0 = 2η - 1` at `η = 1/6` exactly, so the fiber-facing noise count on the certified design
tracks `n/6` within half of `46`. -/
theorem blockPair_noiseCount (M : ℕ) [NeZero (2 * (2 * M))] (c : ZMod (2 * (2 * M) * 24))
    (n : ℕ) :
    |(ALT.noiseCount
        (TapeHost.tapeStream (BlockPairHost.designObs M) c) 8 n : ℝ) -
      (n : ℝ) * (1 / 6)| ≤ 23 := by
  have hρ0 : (if (0 : ℕ) = 0 then (-2 / 3 : ℝ) else 0) = 2 * (1 / 6 : ℝ) - 1 := by norm_num
  have hb := TapeHost.noiseCount_tapeStream_bounds (BlockPairHost.designObs M)
    (BlockPairHost.designObs_profile M) hρ0 c n
  norm_num at hb
  exact hb

/-! ## The certified instance of the class-level overlap -/

/-- **The certified instance of the class-level overlap.** At `η = 1/6` (`blockPair_density`'s own
tape density), the certified block-pair host is simultaneously a member of `𝒮_E` and of `𝒮_L`, at
`TapeHost.overlap`'s own coupled numeral standard — an independent witness of the
coupling standard alongside, not in place of, `BlockPairHost.witness_overlap`'s registered
decoupled boundary. -/
theorem blockPair_overlap_coupled :
    ∃ gTS, ∀ (M : ℕ) [NeZero (2 * (2 * M))] (τ : ℝ), 2 * (1 / 6 : ℝ) ≤ τ → ∀ (K : ℝ),
      (8 : ℝ) + ALT.capacity (Nat.clog 2 (gTS + 1)) ≤ K →
      ALT.hostsAt (TapeHost.frameBits (2 * (2 * M) * 24)) gTS →
      ALT.SubstrateE
        (TapeHost.subUpdate (2 * (2 * M) * 24) (BlockPairHost.designObs M))
        (TapeHost.codeRegion (2 * (2 * M) * 24)) 3 K (2 * K) 1 2 3 (1 / 2) 8 gTS
        True True True True
        (ALT.GrowsLawfulGuestOf
          (TapeHost.packed (2 * (2 * M) * 24) (BlockPairHost.designObs M))
          (TapeHost.frame (2 * (2 * M) * 24) (BlockPairHost.designObs M)))
        (ALT.GrownGuestReachesThresholdAt
          (TapeHost.frameBits (2 * (2 * M) * 24)) gTS) ∧
      ALT.SubstrateL
        (TapeHost.subUpdate (2 * (2 * M) * 24) (BlockPairHost.designObs M))
        (TapeHost.codeRegion (2 * (2 * M) * 24)) 3 K (2 * K) 1 2 3 (1 / 2) 8 gTS
        True True True True
        (TapeHost.Realizable (2 * (2 * M) * 24) (BlockPairHost.designObs M))
        (ALT.ChainWindowBudget 8 (1 / 6) τ) := by
  obtain ⟨gTS, hgTS⟩ := TapeHost.overlap
  refine ⟨gTS, fun M _ τ hτ K hK hhost => ?_⟩
  exact hgTS (2 * (2 * M) * 24) (BlockPairHost.designObs M) _ _ _
    (BlockPairHost.designObs_profile M)
    (1 / 6) τ (by norm_num) hτ K hK hhost

/-! ## The affordable regime's worked example, at the certified design -/

/-- The certified host's own trajectory IS the general host's `BlockPairHost.traj` at
`o := BlockPairHost.designObs M` —
definitional, as `BlockPairHost.tape_eq_tapeHost_tape`/`BlockPairHost.update_eq` are. -/
theorem BlockPairHost.traj_eq (M : ℕ) [NeZero (2 * (2 * M))] (c : ZMod (2 * (2 * M) * 24)) :
    BlockPairHost.traj M c
      = TapeHost.traj (BlockPairHost.designObs M) c := rfl

/-- **The affordable regime's worked example, at the certified design.** [Inevitability] §6's
"a possible affordable regime" paragraph, at a witness: on the certified block-pair host,
`schedSurvivors`'s `2τ`-pruning rule isolates the true literal `0` at `τ = 1/3`
and every horizon `n > 912` — `BlockPairHost.designObs_profile`'s own window bounds (`S = 56`,
`Wm = 192`) meet `schedSurvivors_eq_singleton`'s three conditions with equality
(`2 * (1/6) ≤ 1/3`, `0 ≤ 1/3`, `3 * (1/3) + 0 ≤ 1`), the certified tape density `η = 1/6`
(`blockPair_density`) sitting exactly at the schedule's own tolerance boundary. -/
theorem blockPair_identifies (M : ℕ) [NeZero (2 * (2 * M))] (c : ZMod (2 * (2 * M) * 24))
    {n : ℕ} (hn : 912 < n) :
    schedSurvivors (1 / 3) n (BlockPairHost.traj M c) = {0} := by
  rw [BlockPairHost.traj_eq]
  have hW : ∀ a : Fin 8, (if (a : ℕ) = 0 then (46 : ℝ) else 192) ≤ 192 := by
    intro a
    by_cases ha : (a : ℕ) = 0
    · rw [ite_eq_left ha]; norm_num
    · rw [ite_eq_right ha]
  have hρ0 : (if (0 : ℕ) = 0 then (-2 / 3 : ℝ) else 0) = 2 * (1 / 6 : ℝ) - 1 := by norm_num
  have hρ : ∀ a : Fin 8, (a : ℕ) ≠ 0 →
      |(if (a : ℕ) = 0 then (-2 / 3 : ℝ) else 0)| ≤ (0 : ℝ) := by
    intro a ha
    simp [ha]
  have hn' : (2 * 56 + 192 : ℝ) / (1 / 3) < (n : ℝ) := by
    have hnR : (912 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    norm_num
    linarith [hnR]
  exact schedSurvivors_eq_singleton (BlockPairHost.designObs M)
    (BlockPairHost.designObs_profile M) 192 hW (by norm_num) (by norm_num) hρ0 hρ (by norm_num)
      (by norm_num)
    (by norm_num) (by norm_num) c (by omega) hn'

/-- **`blockPair_identifies`, re-derived at the sharp identification window.** The certified
design's own three margins — `2 * (1/3) - 2 * (1/6) = 1/3`, `2 * (1/3) - 0 = 2/3`,
`1 - 0 - 2 * (1/3) = 1/3` — have minimum `1/3`, the same threshold the landed theorem's single
`τ`-wide budget already used, so the horizon is unchanged: `912` stands under
`schedSurvivors_eq_singleton_sharp` exactly as under the landed
`schedSurvivors_eq_singleton`. -/
theorem blockPair_identifies_sharp (M : ℕ) [NeZero (2 * (2 * M))] (c : ZMod (2 * (2 * M) * 24))
    {n : ℕ} (hn : 912 < n) :
    schedSurvivors (1 / 3) n (BlockPairHost.traj M c) = {0} := by
  rw [BlockPairHost.traj_eq]
  have hW : ∀ a : Fin 8, (if (a : ℕ) = 0 then (46 : ℝ) else 192) ≤ 192 := by
    intro a
    by_cases ha : (a : ℕ) = 0
    · rw [ite_eq_left ha]; norm_num
    · rw [ite_eq_right ha]
  have hρ0 : (if (0 : ℕ) = 0 then (-2 / 3 : ℝ) else 0) = 2 * (1 / 6 : ℝ) - 1 := by norm_num
  have hρ : ∀ a : Fin 8, (a : ℕ) ≠ 0 →
      |(if (a : ℕ) = 0 then (-2 / 3 : ℝ) else 0)| ≤ (0 : ℝ) := by
    intro a ha
    simp [ha]
  have hmineq : min ((2 : ℝ) * (1 / 3) - 2 * (1 / 6)) (min (2 * (1 / 3) - 0) (1 - 0 - 2 * (1 / 3)))
      = 1 / 3 := by norm_num
  have hn' : (2 * 56 + 192 : ℝ) /
      min ((2 : ℝ) * (1 / 3) - 2 * (1 / 6)) (min (2 * (1 / 3) - 0) (1 - 0 - 2 * (1 / 3))) <
      (n : ℝ) := by
    rw [hmineq]
    have hnR : (912 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    norm_num
    linarith [hnR]
  exact schedSurvivors_eq_singleton_sharp (BlockPairHost.designObs M)
    (BlockPairHost.designObs_profile M) 192 hW (by norm_num) (by norm_num) hρ0 hρ (by norm_num)
      (by norm_num)
    (by norm_num) (by norm_num) c (by omega) hn'

end ALT
