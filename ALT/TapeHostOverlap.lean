module

public import ALT.TapeHostWitness
public import ALT.SubstrateEmergence

/-!
# The finite autonomous host's class-level overlap, over an arbitrary window-deviation profile

`BlockPairOverlap.lean` exhibits the certified block-pair host as a member of BOTH route-classes
`𝒮_E` and `𝒮_L` ([Inevitability] §2 Definition 2.3), at the certified instance's own fixed numerals
(`K = 108`, `gTS = 2`, decoupled from the crossing's Gödel size). This module packs the general
host of `TapeHostWitness.lean` onto its numeral carrier via `SubstrateEmergence`'s class-level
`𝒮_E` constructor and assembles the CLASS-LEVEL overlap, at IN-24's coupling standard: one Gödel
size `gTS` shared by BOTH the class's own capacity clause and the crossing clause, rather than the
certified instance's two independent numeral sets.

The tie between the packed update and the host's own update is by `ALT.packedUpdate`
itself — `packed` is DEFINED from `subUpdate` and the packing equivalence, mirroring
`BlockPairHost.packed`'s own shape. The frame's surjectivity is the loaded orbit's own
closed form (`readCounter_iterate_load`), exactly as `BlockPairOverlap`'s own
`frame_surj_iterate` — no permutation-transport argument, and no appeal to periodicity.

## Main results

* `idxEquiv`, `stateEquiv`, `packed` — the host, packed onto its numeral carrier via
  `ALT.packedUpdate`.
* `frameBits`, `frame`, `frame_surj_iterate` — the counter-register frame, and its
  surjectivity after one full pass, from the loaded orbit's own closed form.
* `substrateE` — the host is a member of `𝒮_E`, at any `(K, gTS)` clearing `8 +
  capacity(⌈log₂(gTS+1)⌉)`, via `ALT.substrateE_of_emergence`.
* `overlap` — **the class-level overlap**: at any `Profile`, any `(K, gTS)` clearing that
  same bound, and `hostsAt (frameBits N) gTS`, the SAME update and SAME code region are
  simultaneously a member of `𝒮_E` and of `𝒮_L`, at the SAME coupled numeral set — IN-24's
  coupling standard, `gTS` identified between the class's own capacity clause and the crossing.

## Scope

This is not [Inevitability] §5 Theorem 5.8's registered overlap (`BlockPairHost.witness_overlap`,
kept untouched, byte-identical, at the certified instance's own decoupled numerals: class
`g(T_S) = 2` at `K = 108`, crossing at the excess Gödel size). It is the profile-class criterion's
own overlap, at the coupled standard `SubstrateEmergence`'s class-level constructor forces: the SAME
`gTS` for both `ReflectiveCapacity K sCodeSize gTS` and `GrownGuestReachesThresholdAt κ gTS`. As
`frame_surj_iterate` needs no periodicity, `overlap` says nothing about survival ([Inevitability]
§6) either.

Anchors: [Inevitability] §2 Definition 2.3, §5 Theorem 5.1(a), §5 Theorem 5.8, [Guests] §6
Theorem 6.1, rows IN-5, IN-14, IN-38.
-/


@[expose] public section

namespace ALT

namespace TapeHost

/-! ## The packed host, and the one transport law its orbit needs -/

/-- **The re-indexing equivalence** identifying the host's own three-part cell index with a flat
`Fin`, in the shape the pricing carrier `ALT.stateEquiv` is built over. -/
def idxEquiv (N : ℕ) : Idx N ≃ Fin (8 + (8 + Nat.size N)) :=
  (Equiv.sumCongr (Equiv.refl (Fin 8)) finSumFinEquiv).trans finSumFinEquiv

/-- **The host, packed onto its numeral carrier.** Composes `idxEquiv` with
`ALT.stateEquiv`'s own cell-`i`-carries-weight-`2^i` convention. -/
def stateEquiv (N : ℕ) : Mem N ≃ Fin (2 ^ (8 + (8 + Nat.size N))) :=
  (Equiv.arrowCongr (idxEquiv N) (Equiv.refl Bool)).trans
    (ALT.stateEquiv (8 + (8 + Nat.size N)))

/-- **The host's own update, packed.** `ALT.packedUpdate` applied to
`subUpdate` and `stateEquiv` — the endofunction the class-level `𝒮_E`
constructor is applied to below. -/
def packed (N : ℕ) [NeZero N] (o : ZMod N → Bool) :
    Fin (2 ^ (8 + (8 + Nat.size N))) → Fin (2 ^ (8 + (8 + Nat.size N))) :=
  ALT.packedUpdate (stateEquiv N) (subUpdate N o)

/-! ## The counter-register frame, and its surjectivity from the loaded orbit alone -/

/-- **The host's own bit count.** `2 ^ frameBits N ≤ N` (`Nat.pow_log_le_self`), so the
counter register's low bits give a frame of exactly this width. -/
def frameBits (N : ℕ) : ℕ := Nat.log 2 N

/-- **The frame**: the packed state's counter register, read back and reduced to its low
`frameBits N` bits. -/
def frame (N : ℕ) [NeZero N] (_o : ZMod N → Bool) :
    Fin (2 ^ (8 + (8 + Nat.size N))) → Fin (2 ^ frameBits N) :=
  fun s => ⟨(readCounter N ((stateEquiv N).symm s)).val % 2 ^ frameBits N,
    Nat.mod_lt _ (by positivity)⟩

/-- **The frame surjects after one full pass.** For any target `y`, the state loaded at phase
`y - 7 - n` (`n` the packed carrier's own size) reads the counter back at `y` after `n` steps
(`readCounter_iterate_load`), and `y`'s own value is already below `N`
(`y.isLt` against `Nat.pow_log_le_self`), so the reduction mod `2 ^ frameBits N` is inert. No
permutation-transport argument, and no appeal to periodicity — the loaded orbit's closed form is
enough. -/
theorem frame_surj_iterate (N : ℕ) [NeZero N] (o : ZMod N → Bool) :
    Function.Surjective (fun s : Fin (2 ^ (8 + (8 + Nat.size N))) =>
      frame N o ((packed N o)^[2 ^ (8 + (8 + Nat.size N))] s)) := by
  intro y
  have hNne : (N : ℕ) ≠ 0 := NeZero.ne _
  set c : ZMod N :=
    ((y : ℕ) : ZMod N) - 7 - ((2 ^ (8 + (8 + Nat.size N)) : ℕ) : ZMod N) with hc
  refine ⟨stateEquiv N (load N o c), ?_⟩
  have hiter : (packed N o)^[2 ^ (8 + (8 + Nat.size N))]
      (stateEquiv N (load N o c))
      = stateEquiv N ((subUpdate N o)^[2 ^ (8 + (8 + Nat.size N))]
          (load N o c)) :=
    ALT.packedUpdate_iterate (stateEquiv N) (subUpdate N o)
      _ _
  simp only [hiter, frame, Equiv.symm_apply_apply, readCounter_iterate_load]
  apply Fin.ext
  have hval : c + 7 + (2 ^ (8 + (8 + Nat.size N)) : ℕ) = ((y : ℕ) : ZMod N) := by
    rw [hc]; ring
  change (c + 7 + (2 ^ (8 + (8 + Nat.size N)) : ℕ) : ZMod N).val
      % 2 ^ frameBits N = (y : ℕ)
  rw [hval]
  have hylt : (y : ℕ) < N := lt_of_lt_of_le y.isLt (Nat.pow_log_le_self 2 hNne)
  rw [ZMod.val_cast_of_lt hylt]
  exact Nat.mod_eq_of_lt y.isLt

/-! ## The host is a member of `𝒮_E`, at any coupled `(K, gTS)` -/

/-- The tight numeric bound `3 · log 6 ≤ 6` behind `substrateE`'s and `overlap`'s
own regime clause: `Real.exp_one_gt_d9` squared gives `6 < exp 2`, hence `log 6 < 2` via
`Real.log_le_iff_le_exp`. -/
private theorem log_three_div_half_le_two : Real.log ((3 : ℝ) / (1 / 2)) ≤ 2 := by
  have h1 := Real.exp_one_gt_d9
  have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
  have hexp2 : (6 : ℝ) ≤ Real.exp 2 := by rw [h2]; nlinarith [h1]
  have hlog6 : Real.log 6 ≤ 2 := (Real.log_le_iff_le_exp (by norm_num)).mpr hexp2
  have heq : (3 / (1 / 2) : ℝ) = 6 := by norm_num
  rw [heq]; exact hlog6

/-- **The host is a member of `𝒮_E`.** At any `(K, gTS)` clearing `8 +
capacity(⌈log₂(gTS+1)⌉)` — IN-24's coupling standard — via `ALT.substrateE_of_emergence`:
`frame_surj_iterate` is the surjectivity hypothesis, `hK` is BOTH the regime clause (`3 · log 6
≤ 6 ≤ 8 ≤ K`) and (S3) itself. -/
theorem substrateE (N : ℕ) [NeZero N] (o : ZMod N → Bool) (K : ℝ) (gTS : ℕ)
    (hK : (8 : ℝ) + ALT.capacity (Nat.clog 2 (gTS + 1)) ≤ K)
    (hE : ALT.GrownGuestReachesThresholdAt (frameBits N) gTS) :
    ALT.SubstrateE (subUpdate N o)
      (codeRegion N) 3 K (2 * K) 1 2 3 (1 / 2) 8 gTS True True True True
      (ALT.GrowsLawfulGuestOf (packed N o) (frame N o))
      (ALT.GrownGuestReachesThresholdAt (frameBits N) gTS) := by
  have hK8 : (8 : ℝ) ≤ K := by
    have hcap_nonneg : (0 : ℝ) ≤ (ALT.capacity (Nat.clog 2 (gTS + 1)) : ℝ) :=
      Nat.cast_nonneg _
    linarith
  have hlog := log_three_div_half_le_two
  exact ALT.substrateE_of_emergence (subUpdate N o)
    (codeRegion N) (subUpdate_fixes N o)
    (stateEquiv N) (frame N o) (frame_surj_iterate N o)
    3 K (2 * K) 1 2 3 (1 / 2) 8 gTS True True True True
    ⟨by linarith, le_refl _, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num,
      by norm_num⟩
    ⟨hK, trivial, trivial, trivial, trivial⟩ hE

/-! ## The class-level overlap -/

/-- **The class-level overlap.** At any window-deviation `Profile`, any `(K, gTS)` clearing `8 +
capacity(⌈log₂(gTS+1)⌉)`, and `hostsAt (frameBits N) gTS`, the SAME update and SAME code
region are simultaneously a member of `𝒮_E` (`substrateE`) and of `𝒮_L`
(`substrateL`), at the SAME numeral set — IN-24's coupling standard, `gTS`
shared by the class's own capacity clause and the crossing clause (unlike [Inevitability] §5
Theorem 5.8's registered `BlockPairHost.witness_overlap`, whose class and crossing sizes are
decoupled). `gTS` is fixed once, outside `N` and `o`, from
`ALT.grownGuestReachesThresholdAt_uniform`. -/
theorem overlap :
    ∃ gTS, ∀ (N : ℕ) [NeZero N] (o : ZMod N → Bool) (S : ℝ) (ρ W : Fin 8 → ℝ),
      Profile o S ρ W → ∀ (η τ : ℝ), 0 ≤ η → 2 * η ≤ τ → ∀ (K : ℝ),
      (8 : ℝ) + ALT.capacity (Nat.clog 2 (gTS + 1)) ≤ K →
      ALT.hostsAt (frameBits N) gTS →
      ALT.SubstrateE (subUpdate N o)
        (codeRegion N) 3 K (2 * K) 1 2 3 (1 / 2) 8 gTS True True True True
        (ALT.GrowsLawfulGuestOf (packed N o) (frame N o))
        (ALT.GrownGuestReachesThresholdAt (frameBits N) gTS) ∧
      ALT.SubstrateL (subUpdate N o)
        (codeRegion N) 3 K (2 * K) 1 2 3 (1 / 2) 8 gTS True True True True
        (Realizable N o) (ALT.ChainWindowBudget 8 η τ) := by
  obtain ⟨gTS, hgTS⟩ := ALT.grownGuestReachesThresholdAt_uniform
  refine ⟨gTS, fun N _ o S ρ W h η τ hη hτ K hK _hhost => ?_⟩
  exact ⟨substrateE N o K gTS hK (hgTS (frameBits N)),
    substrateL N o h K gTS hK hη hτ⟩

end TapeHost

end ALT
