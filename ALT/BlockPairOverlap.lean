/-
Copyright (c) 2026 Mykola Palamarchuk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mykola Palamarchuk
-/
import ALT.BlockPairWitness
import ALT.ExcessOrderComplete
import ALT.AccretingExcess

-- Formal-check file, not Mathlib-destined: opt out of the house-style linters.
set_option linter.style.header false
set_option linter.style.longLine false

/-!
# The certified block-pair host is ALSO a member of `𝒮_E`

`BlockPairWitness.lean` exhibits the certified block-pair host as a member of the learning
route-class `𝒮_L` ([Inevitability] §2 Definition 2.3), with E1 drawn from the host's own dynamics.
This module exhibits the SAME host, at the SAME update and the SAME code region, as a member of the
OTHER route-class, `𝒮_E`: the update grows a lawful, affordably-owned guest from every initial state
([Guests] §6 Theorem 6.1's own construction), and that grown guest reaches Definition 2.1's
threshold, in the sense [Inevitability] §5 Theorem 5.1(a) discharges for its own emergence witness
(the Witness World's crossing at `𝗣𝗔⁻`).

The guest is built by re-packing the host's memory onto the numeral carrier the emergence and
capacity machinery of `PersistenceCapacity.lean` is indexed by (`hostPacked`), reading a frame off
the packed host's own counter register (`hostFrame`), and showing that frame surjects onto its
target after one full pass through every packed state — the loaded orbit alone, with no
permutation-transport argument. From there the growth clause is `PersistenceCapacity.emergence`
applied to the packed host and the counter frame, and the crossing clause is
`AccretingWitness.outgrows_paMinus_uniform`'s uniform Gödel size, read at the packed host's own bit
count.

## Main results

* `hostFrameBits`, `hostIdxEquiv`, `hostStateEquiv`, `hostPacked`, `hostPacked_iterate` — the packed
  host and the one transport law its orbit needs.
* `hostFrame`, `hostFrame_surj_iterate` — the counter-register frame, and its surjectivity after one
  full pass, from the loaded orbit's own closed form.
* `HostGrowsLawfulGuest`, `hostCarries`, `hostOwned` — the growth clause, at
  `PersistenceCapacity.emergence`'s own shape: the guest carries the model from every initial state
  and is owned at the packed host's rule plus the frame, parametric in the codes for both (matching
  `PersistenceCapacity.witness_world`'s own standard, whose macro-law code `cG` is a hypothesis
  rather than a built object).
* `HostGrownGuestReachesThreshold`, `hostGrownGuestReachesThreshold`,
  `hostFrameBits_eventually_hostsAt` — the crossing clause, at `witness_outgrows_paMinus`'s own
  standard: a Gödel size fixed once, that every sufficiently large host's bit count hosts.
* `hostWitness_substrateE` — the certified host is a member of `𝒮_E`, at the same `(S1)`/`(S2)`/`(S3)`
  numerals `BlockPairWitness.hostWitness_substrateL` carries for `𝒮_L`.
* `hostWitness_overlap` — **the overlap capstone**: the SAME update, the SAME code region and the
  SAME numerals are simultaneously a member of `𝒮_E` and of `𝒮_L`
  (`BlockPairWitness.hostWitness_substrateL`), from a common threshold on the host's size.

## Scope

This does NOT say anything about survival ([Inevitability] §6): the host's `(window, counter)`
dynamics is a permutation outright (`BlockPairHost.hostUpdate_iterate_period_all`) and its
recurrent core is permuted as every finite host's is, so [Guests] Law 4 leaves no positive margin
to price, and nothing here revisits that. It does NOT state a class-level fact
relating the two route-classes in general — only that this ONE finite, deterministic, autonomous
host inhabits both, at one update, one code region and one numeral set. The paper home is
[Inevitability] §5 Theorem 5.8(c), row IN-38, which registers the overlap at exactly this
boundary.

Anchors: [Inevitability] §2 Definition 2.3, [Inevitability] §5 Theorem 5.1(a), [Guests] §6 Theorem
6.1, rows GV-5, GV-7, IN-5, IN-14.
-/

namespace BlockPairOverlap

open Equiv MulAction
open RealizabilityCCC RealizabilityRecursor
open PersistenceCapacity Decoupling AdditiveComplexity
open LO.FirstOrder LO.FirstOrder.Arithmetic

attribute [local instance] arrowAction

/-! ## The packed host, and the one transport law its orbit needs -/

/-- **The host's own bit count.** `2 ^ hostFrameBits M ≤ Π` (`Nat.pow_log_le_self`), so the counter
register's low bits give a frame of exactly this width. -/
def hostFrameBits (M : ℕ) : ℕ := Nat.log 2 (2 * (2 * M) * 24)

/-- **The re-indexing equivalence** identifying the host's own three-part cell index with a flat
`Fin`, in the shape the pricing carrier `PersistenceCapacity.stateEquiv` is built over. -/
def hostIdxEquiv (M : ℕ) [NeZero (2 * (2 * M))] :
    BlockPairWitness.HostIdx M ≃ Fin (8 + (8 + Nat.size (2 * (2 * M) * 24))) :=
  (Equiv.sumCongr (Equiv.refl (Fin 8)) finSumFinEquiv).trans finSumFinEquiv

/-- **The host, packed onto its numeral carrier.** Composes `hostIdxEquiv` with
`PersistenceCapacity.stateEquiv`'s own cell-`i`-carries-weight-`2^i` convention. -/
def hostStateEquiv (M : ℕ) [NeZero (2 * (2 * M))] :
    BlockPairWitness.HostMem M ≃ Fin (2 ^ (8 + (8 + Nat.size (2 * (2 * M) * 24)))) :=
  (Equiv.arrowCongr (hostIdxEquiv M) (Equiv.refl Bool)).trans
    (PersistenceCapacity.stateEquiv (8 + (8 + Nat.size (2 * (2 * M) * 24))))

/-- **The host's own update, packed.** The conjugate of `BlockPairWitness.hostSubUpdate` along
`hostStateEquiv` — the endofunction the emergence and capacity machinery is applied to below. -/
def hostPacked (M : ℕ) [NeZero (2 * (2 * M))] :
    Fin (2 ^ (8 + (8 + Nat.size (2 * (2 * M) * 24)))) →
      Fin (2 ^ (8 + (8 + Nat.size (2 * (2 * M) * 24)))) :=
  fun s => hostStateEquiv M (BlockPairWitness.hostSubUpdate M ((hostStateEquiv M).symm s))

private lemma hostPacked_apply (M : ℕ) [NeZero (2 * (2 * M))] (x : BlockPairWitness.HostMem M) :
    hostPacked M (hostStateEquiv M x) = hostStateEquiv M (BlockPairWitness.hostSubUpdate M x) := by
  rw [hostPacked, Equiv.symm_apply_apply]

/-- **Orbits survive the packing**: `t` steps of the packed update from a packed state are the
packing of `t` steps of the host's own update. -/
theorem hostPacked_iterate (M : ℕ) [NeZero (2 * (2 * M))] (t : ℕ)
    (s : BlockPairWitness.HostMem M) :
    (hostPacked M)^[t] (hostStateEquiv M s) =
      hostStateEquiv M ((BlockPairWitness.hostSubUpdate M)^[t] s) := by
  induction t with
  | zero => simp
  | succ t ih =>
      rw [Function.iterate_succ_apply', ih, hostPacked_apply, Function.iterate_succ_apply']

/-! ## The counter-register frame, and its surjectivity from the loaded orbit alone -/

/-- **The frame**: the packed state's counter register, read back and reduced to its low
`hostFrameBits M` bits. -/
def hostFrame (M : ℕ) [NeZero (2 * (2 * M))] :
    Fin (2 ^ (8 + (8 + Nat.size (2 * (2 * M) * 24)))) → Fin (2 ^ hostFrameBits M) :=
  fun s => ⟨(BlockPairWitness.readCounter M ((hostStateEquiv M).symm s)).val % 2 ^ hostFrameBits M,
    Nat.mod_lt _ (by positivity)⟩

/-- **The frame surjects after one full pass.** For any target `y`, the state loaded at phase
`y - 7 - n` (`n` the packed carrier's own size) reads the counter back at `y` after `n` steps
(`BlockPairWitness.readCounter_iterate_loadHost`), and `y`'s own value is already below `Π`
(`y.isLt` against `Nat.pow_log_le_self`), so the reduction mod `2 ^ hostFrameBits M` is inert. No
permutation-transport argument, and no appeal to the host's own periodicity — the loaded orbit's
closed form is enough. -/
theorem hostFrame_surj_iterate (M : ℕ) [NeZero (2 * (2 * M))] :
    Function.Surjective (fun s : Fin (2 ^ (8 + (8 + Nat.size (2 * (2 * M) * 24)))) =>
      hostFrame M ((hostPacked M)^[2 ^ (8 + (8 + Nat.size (2 * (2 * M) * 24)))] s)) := by
  intro y
  have hPiNe : (2 * (2 * M) * 24 : ℕ) ≠ 0 := NeZero.ne _
  set c : ZMod (2 * (2 * M) * 24) :=
    ((y : ℕ) : ZMod (2 * (2 * M) * 24)) - 7
      - ((2 ^ (8 + (8 + Nat.size (2 * (2 * M) * 24))) : ℕ) : ZMod (2 * (2 * M) * 24)) with hc
  refine ⟨hostStateEquiv M (BlockPairWitness.loadHost M c), ?_⟩
  simp only [hostPacked_iterate, hostFrame, Equiv.symm_apply_apply,
    BlockPairWitness.readCounter_iterate_loadHost]
  apply Fin.ext
  have hval : c + 7 + (2 ^ (8 + (8 + Nat.size (2 * (2 * M) * 24))) : ℕ)
      = ((y : ℕ) : ZMod (2 * (2 * M) * 24)) := by
    rw [hc]; ring
  change (c + 7 + (2 ^ (8 + (8 + Nat.size (2 * (2 * M) * 24))) : ℕ) : ZMod (2 * (2 * M) * 24)).val
      % 2 ^ hostFrameBits M = (y : ℕ)
  rw [hval]
  have hylt : (y : ℕ) < 2 * (2 * M) * 24 :=
    lt_of_lt_of_le y.isLt (Nat.pow_log_le_self 2 hPiNe)
  rw [ZMod.val_cast_of_lt hylt]
  exact Nat.mod_eq_of_lt y.isLt

/-! ## The growth clause: the packed host emerges an owned guest from every initial state -/

/-- **The guest carries the model from every initial state**, at `PersistenceCapacity.emergence`'s
own shape: the packed host flows into its recurrent core in `n` steps (`n` its own state count) and
then co-moves with the recurrent rule, reading `hostFrame` off the core. -/
theorem hostCarries (M : ℕ) [NeZero (2 * (2 * M))] :
    PersistenceCapacity.Carries (hostPacked M)
      (PersistenceCapacity.emergeLens (hostPacked M) (hostFrame M)) :=
  PersistenceCapacity.carries_emergeLens (hostPacked M) (hostFrame M) (hostFrame_surj_iterate M)

/-- **The guest is owned, parametric in codes for the packed rule and the frame.** One program of
length `elen emergeBuilder + elen cU + elen cθ + O(1)` computes every frame, so the packed host's
uniform entropic capacity at that budget bounds the guest's carried entropy — the relabelling orbit
of the frame's reference reading on the recurrent core. The codes `cU`, `cθ` are carried as
hypotheses, `witness_world`'s own standard: no builder for the host's own table is attempted here. -/
theorem hostOwned (M : ℕ) [NeZero (2 * (2 * M))] (cU cθ : Nat.Partrec.Code)
    (hU : cU.eval 0 = Part.some (PersistenceCapacity.lensCode (hostPacked M)))
    (hθ : cθ.eval 0 = Part.some (PersistenceCapacity.lensCode (hostFrame M))) :
    Nat.card ↥(orbit (Perm ↥(PersistenceCapacity.core (hostPacked M)))
        (PersistenceCapacity.coreLens (hostPacked M)
          (PersistenceCapacity.emergeLens (hostPacked M) (hostFrame M) 0)))
      ≤ PersistenceCapacity.CbHue (hostPacked M)
          (AdditiveComplexity.elen PersistenceCapacity.emergeBuilder + AdditiveComplexity.elen cU
            + AdditiveComplexity.elen cθ + 30) :=
  (PersistenceCapacity.emergence (hostPacked M) (hostFrame M) cU cθ (hostFrame_surj_iterate M)
    hU hθ).2

/-- **The growth clause, bundled** ([Guests] §6 Theorem 6.1's own shape, [Inevitability] §2
Definition 2.3's first clause). Parametric in the codes `cU`, `cθ` — owned at the host's own
description cost, no absolute cheapness claimed. -/
def HostGrowsLawfulGuest (M : ℕ) [NeZero (2 * (2 * M))] : Prop :=
  PersistenceCapacity.Carries (hostPacked M)
      (PersistenceCapacity.emergeLens (hostPacked M) (hostFrame M)) ∧
    ∀ cU cθ : Nat.Partrec.Code,
      cU.eval 0 = Part.some (PersistenceCapacity.lensCode (hostPacked M)) →
      cθ.eval 0 = Part.some (PersistenceCapacity.lensCode (hostFrame M)) →
      Nat.card ↥(orbit (Perm ↥(PersistenceCapacity.core (hostPacked M)))
          (PersistenceCapacity.coreLens (hostPacked M)
            (PersistenceCapacity.emergeLens (hostPacked M) (hostFrame M) 0)))
        ≤ PersistenceCapacity.CbHue (hostPacked M)
            (AdditiveComplexity.elen PersistenceCapacity.emergeBuilder + AdditiveComplexity.elen cU
              + AdditiveComplexity.elen cθ + 30)

/-! ## The crossing clause: a Gödel size every sufficiently large host hosts -/

/-- **The crossing clause** ([Inevitability] §5 Theorem 5.1(a)'s own standard, `witness_world`'s
last conjunct beside `witness_outgrows_paMinus`'s unconditional excess): every Gödel size within the
host's own bit count is hosted in `PersistenceCapacity.hostsThreshold`'s sense, and at `gTS` itself,
whenever the bit count hosts it, the delivered reflective object represents a sentence true and
underivable in `𝗣𝗔⁻`. -/
def HostGrownGuestReachesThreshold (M gTS : ℕ) : Prop :=
  (∀ g, CategoricalThreshold.hostsAt (hostFrameBits M) g →
      PersistenceCapacity.hostsThreshold (hostFrameBits M) g) ∧
    (∀ Mchk, CategoricalThreshold.hostsAt (hostFrameBits M) gTS → gTS < Mchk → Mchk ≤ gTS ^ 2 →
      ∃ R : ReflectiveAsm gTS, R.depth = Mchk ∧
        CapacityLayer.FitsIn (recursorAsm R.depth) (hostFrameBits M) ∧
        ∃ N, GodelThreshold.RepresentsUnderivableTruth (Encodable.encode : Sentence ℒₒᵣ → ℕ)
          (fun δ => (𝗣𝗔⁻ : ArithmeticTheory) ⊢ δ) (fun δ => ℕ↓[ℒₒᵣ] ⊧ δ) N)

/-- **A Gödel size fixed once, that every sufficiently hosting bit count represents.** From
`AccretingWitness.outgrows_paMinus_uniform`'s own `gTS`, obtained outside any particular `M`. -/
theorem hostGrownGuestReachesThreshold :
    ∃ gTS, ∀ (M : ℕ) [NeZero (2 * (2 * M))], HostGrownGuestReachesThreshold M gTS := by
  obtain ⟨gTS, hgTS⟩ := AccretingWitness.outgrows_paMinus_uniform
  refine ⟨gTS, fun M => ?_⟩
  intro _
  exact ⟨fun g h => PersistenceCapacity.hostsThreshold_of_capacity h,
    fun Mchk h1 h2 h3 => hgTS (hostFrameBits M) Mchk h1 h2 h3⟩

/-- **Every sufficiently large host's bit count hosts a fixed Gödel size** ([Decoupling] §6.3/§6.4,
`CategoricalThreshold.hostsAt_mono`/`hostsAt_enters`'s own pattern). `Nat.log` grows without bound in
its argument, and `24 * (2 * M)` dominates `M`, so past `M₀ := 2 ^ capacity(⌈log₂(gTS+1)⌉)` the
host's own bit count already meets the capacity `gTS`'s Gödel sentence needs. -/
theorem hostFrameBits_eventually_hostsAt (gTS : ℕ) :
    ∃ M₀, ∀ M, M₀ ≤ M → CategoricalThreshold.hostsAt (hostFrameBits M) gTS := by
  refine ⟨2 ^ GodelInternalization.capacity (Nat.clog 2 (gTS + 1)), fun M hM => ?_⟩
  refine CategoricalThreshold.hostsAt_mono ?_ (CategoricalThreshold.hostsAt_enters gTS)
  have h1 : Nat.log 2 (2 ^ GodelInternalization.capacity (Nat.clog 2 (gTS + 1))) ≤ Nat.log 2 M :=
    Nat.log_mono_right hM
  rw [Nat.log_pow (by norm_num)] at h1
  have h2 : Nat.log 2 M ≤ Nat.log 2 (2 * (2 * M) * 24) := Nat.log_mono_right (by omega)
  exact h1.trans h2

/-! ## The host is a member of `𝒮_E` -/

/-- **The certified host is a member of `𝒮_E`** ([Inevitability] §2 Definition 2.3), at the SAME
`(S1)`/`(S2)`/`(S3)` numerals `BlockPairWitness.hostWitness_substrateL` carries for `𝒮_L`: `r = 3`,
`K = 8 + 100`, `L = 2K`, `c₀ = 1`, `c₁ = 2`, `c₂ = 3`, `δ = 1/2`, `sCodeSize = 8`
(`BlockPairWitness.hostCodeRegion_ncard`), the structure's own Gödel size `2`. The growth clause is
`HostGrowsLawfulGuest`; the crossing clause is carried as a hypothesis, since it is fixed once across
every host by `hostGrownGuestReachesThreshold` rather than rebuilt per host. -/
theorem hostWitness_substrateE (M gTS : ℕ) [NeZero (2 * (2 * M))]
    (hE : HostGrownGuestReachesThreshold M gTS) :
    SubstrateClass.SubstrateE (BlockPairWitness.hostSubUpdate M) (BlockPairWitness.hostCodeRegion M)
      3 ((8 : ℝ) + 100) (2 * ((8 : ℝ) + 100)) 1 2 3 (1 / 2) 8 2
      True True True True (HostGrowsLawfulGuest M) (HostGrownGuestReachesThreshold M gTS) := by
  have hlog : Real.log (3 / (1 / 2)) ≤ 3 / (1 / 2) - 1 := Real.log_le_sub_one_of_pos (by norm_num)
  have hcap : GodelInternalization.capacity (Nat.clog 2 (2 + 1)) = 4 := by decide
  refine
    { s1 := BlockPairWitness.hostSubUpdate_fixes M
      s2 := ⟨by nlinarith, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num,
        by norm_num, by norm_num⟩
      s3 := ⟨by rw [hcap]; norm_num, trivial, trivial, trivial, trivial⟩
      growsLawfulGuest := ⟨hostCarries M, hostOwned M⟩
      grownGuestReachesThreshold := hE }

/-! ## The overlap capstone -/

/-- **The overlap capstone.** The SAME update, the SAME code region and the SAME numerals are
simultaneously a member of `𝒮_E` (the emergence route-class, above) and of `𝒮_L`
(`BlockPairWitness.hostWitness_substrateL`, [Inevitability] §5 Theorem 5.1(b)'s own route), from a
common threshold on the host's size: past `M₀`, the host's bit count hosts the crossing's Gödel size
`gTS`, `𝒮_E` membership holds at that `gTS`, and `𝒮_L` membership holds unconditionally (its own
threshold needs no `M`-dependent side condition). This answers, for one finite, deterministic,
autonomous host, [Inevitability] §5 Remark 5.7's closing question — whether a host can be its own
source of representativeness — in the sense that the SAME host answers it BOTH ways at once. -/
theorem hostWitness_overlap {τ : ℝ} (hτ : 2 * (1 / 6 : ℝ) ≤ τ) :
    ∃ gTS M₀, ∀ M, M₀ ≤ M → ∀ [NeZero (2 * (2 * M))],
      CategoricalThreshold.hostsAt (hostFrameBits M) gTS ∧
      SubstrateClass.SubstrateE (BlockPairWitness.hostSubUpdate M)
        (BlockPairWitness.hostCodeRegion M)
        3 ((8 : ℝ) + 100) (2 * ((8 : ℝ) + 100)) 1 2 3 (1 / 2) 8 2
        True True True True (HostGrowsLawfulGuest M) (HostGrownGuestReachesThreshold M gTS) ∧
      SubstrateClass.SubstrateL (BlockPairWitness.hostSubUpdate M)
        (BlockPairWitness.hostCodeRegion M)
        3 ((8 : ℝ) + 100) (2 * ((8 : ℝ) + 100)) 1 2 3 (1 / 2) 8 2
        True True True True (BlockPairWitness.HostRealizable M)
        (LearningWitness.ChainWindowBudget 8 (1 / 6) τ) := by
  obtain ⟨gTS, hgTS⟩ := hostGrownGuestReachesThreshold
  obtain ⟨M₀, hM₀⟩ := hostFrameBits_eventually_hostsAt gTS
  refine ⟨gTS, max 1 M₀, fun M hM => ?_⟩
  intro _
  have hhost : CategoricalThreshold.hostsAt (hostFrameBits M) gTS :=
    hM₀ M (le_trans (le_max_right 1 M₀) hM)
  exact ⟨hhost, hostWitness_substrateE M gTS (hgTS M), BlockPairWitness.hostWitness_substrateL M hτ⟩

end BlockPairOverlap
