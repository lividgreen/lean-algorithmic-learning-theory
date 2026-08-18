/-
Copyright (c) 2026 Mykola Palamarchuk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mykola Palamarchuk
-/
import ALT.TapeHostWitness
import ALT.SubstrateEmergence

/-!
# The finite autonomous host's class-level overlap, over an arbitrary window-deviation profile

`BlockPairOverlap.lean` exhibits the certified block-pair host as a member of BOTH route-classes
`𝒮_E` and `𝒮_L` ([Inevitability] §2 Definition 2.3), at the certified instance's own fixed numerals
(`K = 108`, `gTS = 2`, decoupled from the crossing's Gödel size). This module packs the general
host of `TapeHostWitness.lean` onto its numeral carrier via `SubstrateEmergence`'s class-level
`𝒮_E` constructor and assembles the CLASS-LEVEL overlap, at IN-24's coupling standard: one Gödel
size `gTS` shared by BOTH the class's own capacity clause and the crossing clause, rather than the
certified instance's two independent numeral sets.

The tie between the packed update and the host's own update is by `SubstrateEmergence.packedUpdate`
itself — `hostPacked` is DEFINED from `hostSubUpdate` and the packing equivalence, mirroring
`BlockPairOverlap.hostPacked`'s own shape. The frame's surjectivity is the loaded orbit's own
closed form (`TapeHostWitness.readCounter_iterate_loadHost`), exactly as `BlockPairOverlap`'s own
`hostFrame_surj_iterate` — no permutation-transport argument, and no appeal to periodicity.

## Main results

* `hostIdxEquiv`, `hostStateEquiv`, `hostPacked` — the host, packed onto its numeral carrier via
  `SubstrateEmergence.packedUpdate`.
* `hostFrameBits`, `hostFrame`, `hostFrame_surj_iterate` — the counter-register frame, and its
  surjectivity after one full pass, from the loaded orbit's own closed form.
* `tapeHost_substrateE` — the host is a member of `𝒮_E`, at any `(K, gTS)` clearing `8 +
  capacity(⌈log₂(gTS+1)⌉)`, via `SubstrateEmergence.substrateE_of_emergence`.
* `tapeHost_overlap` — **the class-level overlap**: at any `Profile`, any `(K, gTS)` clearing that
  same bound, and `hostsAt (hostFrameBits N) gTS`, the SAME update and SAME code region are
  simultaneously a member of `𝒮_E` and of `𝒮_L`, at the SAME coupled numeral set — IN-24's
  coupling standard, `gTS` identified between the class's own capacity clause and the crossing.

## Scope

This is not [Inevitability] §5 Theorem 5.8's registered overlap (`BlockPairOverlap.hostWitness_
overlap`, kept untouched, byte-identical, at the certified instance's own decoupled numerals: class
`g(T_S) = 2` at `K = 108`, crossing at the excess Gödel size). It is the profile-class criterion's
own overlap, at the coupled standard `SubstrateEmergence`'s class-level constructor forces: the SAME
`gTS` for both `ReflectiveCapacity K sCodeSize gTS` and `GrownGuestReachesThresholdAt κ gTS`. As
`TapeHostOverlap.hostFrame_surj_iterate` needs no periodicity, `tapeHost_overlap` says nothing about
survival ([Inevitability] §6) either.

Anchors: [Inevitability] §2 Definition 2.3, §5 Theorem 5.1(a), §5 Theorem 5.8, [Guests] §6
Theorem 6.1, rows IN-5, IN-14, IN-38.
-/

namespace TapeHostOverlap

/-! ## The packed host, and the one transport law its orbit needs -/

/-- **The re-indexing equivalence** identifying the host's own three-part cell index with a flat
`Fin`, in the shape the pricing carrier `PersistenceCapacity.stateEquiv` is built over. -/
def hostIdxEquiv (N : ℕ) : TapeHostWitness.HostIdx N ≃ Fin (8 + (8 + Nat.size N)) :=
  (Equiv.sumCongr (Equiv.refl (Fin 8)) finSumFinEquiv).trans finSumFinEquiv

/-- **The host, packed onto its numeral carrier.** Composes `hostIdxEquiv` with
`PersistenceCapacity.stateEquiv`'s own cell-`i`-carries-weight-`2^i` convention. -/
def hostStateEquiv (N : ℕ) : TapeHostWitness.HostMem N ≃ Fin (2 ^ (8 + (8 + Nat.size N))) :=
  (Equiv.arrowCongr (hostIdxEquiv N) (Equiv.refl Bool)).trans
    (PersistenceCapacity.stateEquiv (8 + (8 + Nat.size N)))

/-- **The host's own update, packed.** `SubstrateEmergence.packedUpdate` applied to
`TapeHostWitness.hostSubUpdate` and `hostStateEquiv` — the endofunction the class-level `𝒮_E`
constructor is applied to below. -/
def hostPacked (N : ℕ) [NeZero N] (o : ZMod N → Bool) :
    Fin (2 ^ (8 + (8 + Nat.size N))) → Fin (2 ^ (8 + (8 + Nat.size N))) :=
  SubstrateEmergence.packedUpdate (hostStateEquiv N) (TapeHostWitness.hostSubUpdate N o)

/-! ## The counter-register frame, and its surjectivity from the loaded orbit alone -/

/-- **The host's own bit count.** `2 ^ hostFrameBits N ≤ N` (`Nat.pow_log_le_self`), so the
counter register's low bits give a frame of exactly this width. -/
def hostFrameBits (N : ℕ) : ℕ := Nat.log 2 N

/-- **The frame**: the packed state's counter register, read back and reduced to its low
`hostFrameBits N` bits. -/
def hostFrame (N : ℕ) [NeZero N] (_o : ZMod N → Bool) :
    Fin (2 ^ (8 + (8 + Nat.size N))) → Fin (2 ^ hostFrameBits N) :=
  fun s => ⟨(TapeHostWitness.readCounter N ((hostStateEquiv N).symm s)).val % 2 ^ hostFrameBits N,
    Nat.mod_lt _ (by positivity)⟩

/-- **The frame surjects after one full pass.** For any target `y`, the state loaded at phase
`y - 7 - n` (`n` the packed carrier's own size) reads the counter back at `y` after `n` steps
(`TapeHostWitness.readCounter_iterate_loadHost`), and `y`'s own value is already below `N`
(`y.isLt` against `Nat.pow_log_le_self`), so the reduction mod `2 ^ hostFrameBits N` is inert. No
permutation-transport argument, and no appeal to periodicity — the loaded orbit's closed form is
enough. -/
theorem hostFrame_surj_iterate (N : ℕ) [NeZero N] (o : ZMod N → Bool) :
    Function.Surjective (fun s : Fin (2 ^ (8 + (8 + Nat.size N))) =>
      hostFrame N o ((hostPacked N o)^[2 ^ (8 + (8 + Nat.size N))] s)) := by
  intro y
  have hNne : (N : ℕ) ≠ 0 := NeZero.ne _
  set c : ZMod N :=
    ((y : ℕ) : ZMod N) - 7 - ((2 ^ (8 + (8 + Nat.size N)) : ℕ) : ZMod N) with hc
  refine ⟨hostStateEquiv N (TapeHostWitness.loadHost N o c), ?_⟩
  have hiter : (hostPacked N o)^[2 ^ (8 + (8 + Nat.size N))]
      (hostStateEquiv N (TapeHostWitness.loadHost N o c))
      = hostStateEquiv N ((TapeHostWitness.hostSubUpdate N o)^[2 ^ (8 + (8 + Nat.size N))]
          (TapeHostWitness.loadHost N o c)) :=
    SubstrateEmergence.packedUpdate_iterate (hostStateEquiv N) (TapeHostWitness.hostSubUpdate N o)
      _ _
  simp only [hiter, hostFrame, Equiv.symm_apply_apply, TapeHostWitness.readCounter_iterate_loadHost]
  apply Fin.ext
  have hval : c + 7 + (2 ^ (8 + (8 + Nat.size N)) : ℕ) = ((y : ℕ) : ZMod N) := by
    rw [hc]; ring
  change (c + 7 + (2 ^ (8 + (8 + Nat.size N)) : ℕ) : ZMod N).val
      % 2 ^ hostFrameBits N = (y : ℕ)
  rw [hval]
  have hylt : (y : ℕ) < N := lt_of_lt_of_le y.isLt (Nat.pow_log_le_self 2 hNne)
  rw [ZMod.val_cast_of_lt hylt]
  exact Nat.mod_eq_of_lt y.isLt

/-! ## The host is a member of `𝒮_E`, at any coupled `(K, gTS)` -/

/-- The tight numeric bound `3 · log 6 ≤ 6` behind `tapeHost_substrateE`'s and `tapeHost_overlap`'s
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
capacity(⌈log₂(gTS+1)⌉)` — IN-24's coupling standard — via `SubstrateEmergence.
substrateE_of_emergence`: `hostFrame_surj_iterate` is the surjectivity hypothesis, `hK` is BOTH the
regime clause (`3 · log 6 ≤ 6 ≤ 8 ≤ K`) and (S3) itself. -/
theorem tapeHost_substrateE (N : ℕ) [NeZero N] (o : ZMod N → Bool) (K : ℝ) (gTS : ℕ)
    (hK : (8 : ℝ) + GodelInternalization.capacity (Nat.clog 2 (gTS + 1)) ≤ K)
    (hE : SubstrateEmergence.GrownGuestReachesThresholdAt (hostFrameBits N) gTS) :
    SubstrateClass.SubstrateE (TapeHostWitness.hostSubUpdate N o)
      (TapeHostWitness.hostCodeRegion N) 3 K (2 * K) 1 2 3 (1 / 2) 8 gTS True True True True
      (SubstrateEmergence.GrowsLawfulGuestOf (hostPacked N o) (hostFrame N o))
      (SubstrateEmergence.GrownGuestReachesThresholdAt (hostFrameBits N) gTS) := by
  have hK8 : (8 : ℝ) ≤ K := by
    have hcap_nonneg : (0 : ℝ) ≤ (GodelInternalization.capacity (Nat.clog 2 (gTS + 1)) : ℝ) :=
      Nat.cast_nonneg _
    linarith
  have hlog := log_three_div_half_le_two
  exact SubstrateEmergence.substrateE_of_emergence (TapeHostWitness.hostSubUpdate N o)
    (TapeHostWitness.hostCodeRegion N) (TapeHostWitness.hostSubUpdate_fixes N o)
    (hostStateEquiv N) (hostFrame N o) (hostFrame_surj_iterate N o)
    3 K (2 * K) 1 2 3 (1 / 2) 8 gTS True True True True
    ⟨by linarith, le_refl _, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num,
      by norm_num⟩
    ⟨hK, trivial, trivial, trivial, trivial⟩ hE

/-! ## The class-level overlap -/

/-- **The class-level overlap.** At any window-deviation `Profile`, any `(K, gTS)` clearing `8 +
capacity(⌈log₂(gTS+1)⌉)`, and `hostsAt (hostFrameBits N) gTS`, the SAME update and SAME code
region are simultaneously a member of `𝒮_E` (`tapeHost_substrateE`) and of `𝒮_L`
(`TapeHostWitness.tapeHost_substrateL`), at the SAME numeral set — IN-24's coupling standard, `gTS`
shared by the class's own capacity clause and the crossing clause (unlike [Inevitability] §5
Theorem 5.8's registered `BlockPairOverlap.hostWitness_overlap`, whose class and crossing sizes are
decoupled). `gTS` is fixed once, outside `N` and `o`, from `SubstrateEmergence.
grownGuestReachesThresholdAt_uniform`. -/
theorem tapeHost_overlap :
    ∃ gTS, ∀ (N : ℕ) [NeZero N] (o : ZMod N → Bool) (S : ℝ) (ρ W : Fin 8 → ℝ),
      TapeHostObservability.Profile o S ρ W → ∀ (η τ : ℝ), 0 ≤ η → 2 * η ≤ τ → ∀ (K : ℝ),
      (8 : ℝ) + GodelInternalization.capacity (Nat.clog 2 (gTS + 1)) ≤ K →
      CategoricalThreshold.hostsAt (hostFrameBits N) gTS →
      SubstrateClass.SubstrateE (TapeHostWitness.hostSubUpdate N o)
        (TapeHostWitness.hostCodeRegion N) 3 K (2 * K) 1 2 3 (1 / 2) 8 gTS True True True True
        (SubstrateEmergence.GrowsLawfulGuestOf (hostPacked N o) (hostFrame N o))
        (SubstrateEmergence.GrownGuestReachesThresholdAt (hostFrameBits N) gTS) ∧
      SubstrateClass.SubstrateL (TapeHostWitness.hostSubUpdate N o)
        (TapeHostWitness.hostCodeRegion N) 3 K (2 * K) 1 2 3 (1 / 2) 8 gTS True True True True
        (TapeHostWitness.HostRealizable N o) (LearningWitness.ChainWindowBudget 8 η τ) := by
  obtain ⟨gTS, hgTS⟩ := SubstrateEmergence.grownGuestReachesThresholdAt_uniform
  refine ⟨gTS, fun N _ o S ρ W h η τ hη hτ K hK _hhost => ?_⟩
  exact ⟨tapeHost_substrateE N o K gTS hK (hgTS (hostFrameBits N)),
    TapeHostWitness.tapeHost_substrateL N o h K gTS hK hη hτ⟩

end TapeHostOverlap
