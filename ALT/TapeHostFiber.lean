/-
Copyright (c) 2026 Mykola Palamarchuk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mykola Palamarchuk
-/
import ALT.TapeHostWitness
import ALT.WitnessMixture
import ALT.DamageGate

/-!
# Theorem 6.6's noisy-branch machinery, read on the profile-class base ([Inevitability] §6)

`TapeHost.lean`/`TapeHostObservability.lean` wrap an arbitrary observation sequence into a finite
autonomous host, and `WitnessMixture.lean`/`DamageGate.lean` state the single witness's noisy-branch
machinery — the surprise budget's rate and the noise-gated absorption bound — on an arbitrary noise
stream. This module supplies the missing interface: a stream and one identity tying the host's own
emitted process to that stream, so the stream-arbitrary machinery reads at an autonomous host whose
observability is its own, over the whole window-deviation `Profile` class ([Inevitability] §5
Proposition 5.9).

## The interface

`tapeStream o c` extends the host's own observation sequence `o` by the derived tape it reads past
the first eight positions — the first eight bits the sequence itself, then the tape bit
`TapeHost.tape o` supplies — mirroring `BlockPairObservability.designTape`'s construction at a
general sequence rather than the certified design. `hostTraj_eq_obs` closes the loop:
`TapeHostObservability.hostTraj o c` is exactly the noisy window chain's own `obs 8` on this stream.

Candidate `0`'s miss at `t`, read on `tapeStream o c`, is the tape's own bit `t` steps past the
window — a function of the host's counter, not of an external noise source
(`witMiss_zero_tapeStream`). Summed over a window, that miss count is exactly the profile's own
same-class pair sum at offset `0` (`noiseCount_tapeStream_eq`), so `Profile.pair` at `a = 0` bounds
it against the profile's declared density `η` (`noiseCount_tapeStream_bounds`) — the tie the rest of
the module reads through.

## Main results

* `tapeStream` — the fiber-facing stream: the sequence itself below `8`, the derived tape above it.
* `hostTraj_eq_obs` — the host's own process **is** the noisy window chain's `obs 8` on
  `tapeStream`.
* `witMiss_zero_tapeStream` — the true candidate's miss **is** the tape's own bit.
* `noiseCount_tapeStream_eq` — the noise count's doubled value is the horizon plus the profile's own
  same-class pair sum.
* `noiseCount_tapeStream_bounds` — **the tie**: the noise count tracks `n · η` within half the
  profile's own window bound `W 0`.
* `floorSurprise_rate_tapeHost` — Theorem 6.6(iii)'s rate, `28 + 16 · (nη + W 0/2)`, read on the
  profile-class base.
* `noiseGated_tapeStream_iff` — the noise gate, read on `tapeStream`, is confinement to the tape's
  own firings — a function of the host's state, not an external condition.
* `exists_untouched_copy_tapeHost` — Theorem 6.6(v′)'s absorption at a horizon, from the profile's
  own bound on the noise count.
* `tapeStream_fires_forever` — the positive fact behind (v)/(v″)'s absence at a positive-density
  profile: the derived tape fires past every horizon.

## Scope

This module states nothing lifetime-free: `tapeStream_fires_forever` is the reason (v)/(v″)'s
quiet-stream gates are not on offer at a positive-density profile, not a route around that absence.
Nothing here derives the damage model — (D1)/(D2) stay named exactly as Theorem 6.6 states them,
and the noise gate's being a function of the host's own state is a fact about where the firing set
lives, not a coupling of damage to misprediction. Nothing here settles the fiber: the composite's
convergence is `FlooredMixture.lean`/`BasinSettling.lean`'s own business, untouched. And this is one
architecture — the length-eight window chain on a derived tape — read at the profile class
[Inevitability] §5 Proposition 5.9 already names; it is not a general damage-model or fiber-settling
result.

[Inevitability] §6 Theorem 6.6 (clauses (iii), (v′)); §5 Proposition 5.9; rows IN-16, IN-28, IN-41.
-/

namespace TapeHostFiber

variable {N : ℕ} [NeZero N] (o : ZMod N → Bool)

/-! ## The fiber-facing interface: one stream, one identity -/

/-- **The fiber-facing stream.** The sequence's own value below the window length `8`, and the
derived tape's bit past it — `BlockPairObservability.designTape`'s construction at a general
sequence `o` rather than the certified design. -/
def tapeStream (c : ZMod N) : ℕ → Bool :=
  fun t => if t < 8 then o (c + t) else TapeHost.tape o (c + t)

omit [NeZero N] in
private theorem tapeStream_add8 (c : ZMod N) (t : ℕ) :
    tapeStream o c (t + 8) = TapeHost.tape o (c + ((t + 8 : ℕ) : ZMod N)) := by
  unfold tapeStream
  rw [if_neg (by omega : ¬ t + 8 < 8)]

omit [NeZero N] in
/-- **The host's own process is the noisy window chain's `obs 8` on `tapeStream`.**
`BlockPairObservability.hostTraj_eq_obs`'s proof at a general sequence `o`: strong induction on the
elapsed time, `NoisyWindowChain.obs_of_lt` below the window length, and `NoisyWindowChain.obs_add`
together with the tape's own defining identity above it. -/
theorem hostTraj_eq_obs (c : ZMod N) :
    TapeHostObservability.hostTraj o c = NoisyWindowChain.obs 8 (tapeStream o c) := by
  funext t
  change o (c + (t : ZMod N)) = NoisyWindowChain.obs 8 (tapeStream o c) t
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    by_cases ht : t < 8
    · rw [NoisyWindowChain.obs_of_lt (tapeStream o c) ht]
      unfold tapeStream
      rw [if_pos ht]
    · obtain ⟨s, hs⟩ : ∃ s, t = s + 8 := ⟨t - 8, by omega⟩
      have hih := ih s (by omega)
      rw [hs, NoisyWindowChain.obs_add (by norm_num : (0 : ℕ) < 8) (tapeStream o c) s,
        tapeStream_add8, ← hih]
      have hcast2 : TapeHost.tape o (c + ((s + 8 : ℕ) : ZMod N))
          = (o (c + ((s + 8 : ℕ) : ZMod N)) == o (c + (s : ZMod N))) := by
        unfold TapeHost.tape
        congr 2
        push_cast
        ring
      rw [hcast2]
      cases o (c + ((s + 8 : ℕ) : ZMod N)) <;> cases o (c + (s : ZMod N)) <;> decide

omit [NeZero N] in
/-- **The true candidate's miss is the tape's own bit.** `WitnessMixture.witMiss_zero` read at
`tapeStream o c`: candidate `0`'s miss at `t` is the stream's bit `t + 8` steps past the phase,
which — past the window — is exactly the derived tape's own bit there, a function of the host's
counter rather than an external noise source. -/
theorem witMiss_zero_tapeStream (c : ZMod N) (t : ℕ) :
    WitnessMixture.witMiss 8 (tapeStream o c) t 0 = TapeHost.tape o (c + (t + 8 : ℕ)) := by
  rw [WitnessMixture.witMiss_zero]
  exact tapeStream_add8 o c t

/-! ## The tie: the noise count is the profile's own same-class pair sum -/

omit [NeZero N] in
private lemma pairChar_tapeStream_eq (c : ZMod N) (t : ℕ) :
    ParityWalk.chi (o (c + (t : ℕ))) * ParityWalk.chi (o (c + (t : ℕ) + 8))
      = (2 : ℝ) * (if tapeStream o c (t + 8) = true then (1 : ℝ) else 0) - 1 := by
  rw [tapeStream_add8]
  have hidx : c + ((t + 8 : ℕ) : ZMod N) = c + (t : ℕ) + 8 := by push_cast; ring
  have hcast2 : TapeHost.tape o (c + ((t + 8 : ℕ) : ZMod N))
      = (o (c + ((t + 8 : ℕ) : ZMod N)) == o (c + (t : ℕ))) := by
    unfold TapeHost.tape
    congr 2
    push_cast
    ring
  rw [hcast2, hidx]
  cases o (c + (t : ℕ) + 8) <;> cases o (c + (t : ℕ)) <;> norm_num [ParityWalk.chi]

omit [NeZero N] in
private lemma noiseCount_tapeStream_eq_sum (c : ZMod N) (n : ℕ) :
    (WitnessMixture.noiseCount (tapeStream o c) 8 n : ℝ) =
      ∑ t ∈ Finset.range n, (if tapeStream o c (t + 8) = true then (1 : ℝ) else 0) := by
  rw [WitnessMixture.noiseCount]
  exact Finset.natCast_card_filter (fun t => tapeStream o c (t + 8) = true) (Finset.range n)

omit [NeZero N] in
/-- **The noise count's doubled value is the horizon plus the profile's own same-class pair sum.**
The window form of `TapeHostWitness.tape_density`'s per-point identity
(`χ(o u) · χ(o (u − 8)) = 2 · [tape o u = true] − 1`), summed over the window and read at
`u = c + t + 8`, so that the indicator sum *is* `WitnessMixture.noiseCount`. -/
theorem noiseCount_tapeStream_eq (c : ZMod N) (n : ℕ) :
    (2 : ℝ) * (WitnessMixture.noiseCount (tapeStream o c) 8 n : ℝ) = (n : ℝ) +
      ∑ t ∈ Finset.range n,
        ParityWalk.chi (o (c + (t : ℕ))) * ParityWalk.chi (o (c + (t : ℕ) + 8)) := by
  rw [Finset.sum_congr rfl (fun t (_ : t ∈ Finset.range n) => pairChar_tapeStream_eq o c t),
    Finset.sum_sub_distrib, ← Finset.mul_sum, ← noiseCount_tapeStream_eq_sum, Finset.sum_const,
    Finset.card_range, nsmul_eq_mul, mul_one]
  ring

omit [NeZero N] in
/-- **The tie between the noise count and the profile's own declared density.** `Profile.pair` at
`a = 0` and phase `c` bounds the same-class pair sum `noiseCount_tapeStream_eq` produces within
`W 0` of the trend `n · ρ 0`; at `ρ 0 = 2η − 1` this reads as the noise count tracking `n · η`
within half that bound — the pair `(o (c + t), o (c + t + 8))` being exactly `noiseCount`'s own
window. -/
theorem noiseCount_tapeStream_bounds {S : ℝ} {ρ W : Fin 8 → ℝ}
    (h : TapeHostObservability.Profile o S ρ W) {η : ℝ} (hρ0 : ρ 0 = 2 * η - 1)
    (c : ZMod N) (n : ℕ) :
    |(WitnessMixture.noiseCount (tapeStream o c) 8 n : ℝ) - (n : ℝ) * η| ≤ W 0 / 2 := by
  have hpair := h.pair c 0 n
  have hsum : (∑ t ∈ Finset.range n,
      ParityWalk.chi (o (c + (t : ℕ) + (((0 : Fin 8) : ℕ) : ZMod N))) *
        ParityWalk.chi (o (c + (t : ℕ) + ((8 : ℕ) : ZMod N))))
      = ∑ t ∈ Finset.range n,
          ParityWalk.chi (o (c + (t : ℕ))) * ParityWalk.chi (o (c + (t : ℕ) + 8)) := by
    refine Finset.sum_congr rfl fun t _ => ?_
    have e1 : c + (t : ℕ) + (((0 : Fin 8) : ℕ) : ZMod N) = c + (t : ℕ) := by
      have h0 : ((0 : Fin 8) : ℕ) = 0 := rfl
      rw [h0]; push_cast; ring
    have e2 : c + (t : ℕ) + ((8 : ℕ) : ZMod N) = c + (t : ℕ) + 8 := by push_cast; ring
    rw [e1, e2]
  rw [hsum, hρ0] at hpair
  have heq := noiseCount_tapeStream_eq o c n
  have hexpand : (n : ℝ) * (2 * η - 1) = 2 * ((n : ℝ) * η) - n := by ring
  rw [hexpand] at hpair
  rw [abs_le] at hpair ⊢
  exact ⟨by linarith [heq], by linarith [heq]⟩

/-! ## Theorem 6.6(iii)'s rate, read on the profile-class base -/

omit [NeZero N] in
/-- **The surprise budget's rate, at the profile's own constants** ([Inevitability] §6 Theorem
6.6(iii)). `WitnessMixture.witness_floorSurprise_card_mul_le` at `k = 8`, `ξ := tapeStream o c`,
with `noiseCount_tapeStream_bounds`'s upper half pricing the noise count in the profile's `η` and
`W 0`. -/
theorem floorSurprise_rate_tapeHost {S : ℝ} {ρ W : Fin 8 → ℝ}
    (h : TapeHostObservability.Profile o S ρ W) {η : ℝ} (hρ0 : ρ 0 = 2 * η - 1)
    (c : ZMod N) (b : ℕ) (θ : ℚ) (hbudget : 2 * ((8 : ℚ) - 1) ≤ θ * 2 ^ b) (n : ℕ) :
    ((WeightedFiber.floorSurpriseSet (WitnessMixture.witMiss 8 (tapeStream o c)) b θ n).card : ℝ)
        * (θ : ℝ)
      ≤ 28 + 16 * ((n : ℝ) * η + W 0 / 2) := by
  have hqR : ((WeightedFiber.floorSurpriseSet
        (WitnessMixture.witMiss 8 (tapeStream o c)) b θ n).card : ℝ) * (θ : ℝ)
      ≤ 4 * ((8 : ℝ) - 1) + 2 * (8 : ℝ) *
          (WitnessMixture.noiseCount (tapeStream o c) 8 n : ℝ) := by
    exact_mod_cast WitnessMixture.witness_floorSurprise_card_mul_le (tapeStream o c) b θ hbudget n
  have hbound := noiseCount_tapeStream_bounds o h hρ0 c n
  rw [abs_le] at hbound
  linarith [hqR, hbound.2]

/-! ## Theorem 6.6(v′)'s absorption, at an endogenous gate -/

omit [NeZero N] in
/-- **The noise gate, read on `tapeStream`, is confinement to the derived tape's own firings** —
a function of the host's own state rather than an external condition
([Inevitability] §6 Theorem 6.6(v′)). -/
theorem noiseGated_tapeStream_iff (c : ZMod N) (H : Finset ℕ) :
    DamageGate.NoiseGated 8 (tapeStream o c) H ↔
      ∀ s ∈ H, TapeHost.tape o (c + (s + 8 : ℕ)) = true := by
  unfold DamageGate.NoiseGated
  simp only [tapeStream_add8]

omit [NeZero N] in
/-- **Absorption at a horizon, from the profile's own bound on the noise count**
([Inevitability] §6 Theorem 6.6(v′)). `DamageGate.exists_untouched_copy_of_noiseGated` at
`ξ := tapeStream o c`, with the redundancy hypothesis discharged through
`noiseCount_tapeStream_bounds`'s upper half rather than the raw noise count. -/
theorem exists_untouched_copy_tapeHost {P : ℕ} [NeZero P] {S : ℝ} {ρ W : Fin 8 → ℝ}
    (h : TapeHostObservability.Profile o S ρ W) {η : ℝ} (hρ0 : ρ 0 = 2 * η - 1)
    (c : ZMod N) {n cnt : ℕ} {H : Finset ℕ} (hH : H ⊆ Finset.range n)
    (hgate : DamageGate.NoiseGated 8 (tapeStream o c) H)
    (col : ℕ → Finset (Fin P)) (hcol : ∀ t, (col t).card ≤ cnt)
    (hP : (cnt : ℝ) * ((n : ℝ) * η + W 0 / 2) < (P : ℝ)) :
    ∃ i₀ : Fin P, ∀ t ∈ H, i₀ ∉ col t := by
  have hbound := noiseCount_tapeStream_bounds o h hρ0 c n
  rw [abs_le] at hbound
  have h1 : (WitnessMixture.noiseCount (tapeStream o c) 8 n : ℝ) ≤ (n : ℝ) * η + W 0 / 2 := by
    linarith [hbound.2]
  have hcnt0 : (0 : ℝ) ≤ (cnt : ℝ) := Nat.cast_nonneg cnt
  have hnc : (cnt : ℝ) * (WitnessMixture.noiseCount (tapeStream o c) 8 n : ℝ) < (P : ℝ) :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_left h1 hcnt0) hP
  have hnc' : cnt * WitnessMixture.noiseCount (tapeStream o c) 8 n < P := by exact_mod_cast hnc
  exact DamageGate.exists_untouched_copy_of_noiseGated (tapeStream o c) hH hgate col hcol hnc'

/-! ## The positive fact behind (v)/(v″)'s absence -/

omit [NeZero N] in
/-- **The derived tape fires past every horizon, at a positive-density profile.** From
`noiseCount_tapeStream_bounds`'s lower half, the noise count grows without bound in `n`, so no
horizon is quiet from some point on — the fact behind (v)/(v″)'s quiet-stream gates and the
settling theorems' never-missing/eventually-realizable hypotheses being unavailable here
([Inevitability] §6, the proof paragraph's route-absence reading; Remark 5.7's designed-source
paragraph). Stated as a positive fact about the stream, never as an impossibility of survival. -/
theorem tapeStream_fires_forever {S : ℝ} {ρ W : Fin 8 → ℝ}
    (h : TapeHostObservability.Profile o S ρ W) {η : ℝ} (hρ0 : ρ 0 = 2 * η - 1) (hη : 0 < η)
    (c : ZMod N) : ∀ T : ℕ, ∃ t, T ≤ t ∧ tapeStream o c t = true := by
  intro T
  obtain ⟨n, hn⟩ := exists_nat_gt (((T : ℝ) + W 0 / 2) / η)
  have hbound := noiseCount_tapeStream_bounds o h hρ0 c n
  rw [abs_le] at hbound
  have hlt : (T : ℝ) < (n : ℝ) * η - W 0 / 2 := by
    rw [div_lt_iff₀ hη] at hn
    linarith
  have hcardT : T < WitnessMixture.noiseCount (tapeStream o c) 8 n := by
    have hR : (T : ℝ) < (WitnessMixture.noiseCount (tapeStream o c) 8 n : ℝ) := by
      linarith [hbound.1]
    exact_mod_cast hR
  have hnotsub : ¬ (((Finset.range n).filter fun t => tapeStream o c (t + 8)) ⊆
      Finset.range T) := by
    intro hsub
    have hle := Finset.card_le_card hsub
    rw [Finset.card_range] at hle
    have hle' : WitnessMixture.noiseCount (tapeStream o c) 8 n ≤ T := hle
    omega
  obtain ⟨t, htmem, htT⟩ := Finset.not_subset.mp hnotsub
  rw [Finset.mem_filter] at htmem
  rw [Finset.mem_range] at htT
  exact ⟨t + 8, by omega, htmem.2⟩

end TapeHostFiber
