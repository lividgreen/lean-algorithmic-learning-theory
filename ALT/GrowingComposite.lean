/-
Copyright (c) 2026 Mykola Palamarchuk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mykola Palamarchuk
-/
module

public import ALT.GrowingWorld
public import ALT.NoisyWindowChain
public import ALT.DamageGate
public import ErgodicTheory.DrivenColumns

-- Formal-check file, not Mathlib-destined: opt out of the house-style header linter.
set_option linter.style.header false

/-!
# The growing composite: a noisy window chain over a growing autonomous source ([Growth] §3)

`GrowingWorld.lean` states the staged square at an arbitrary carrier and stress-tests it against a
single accretive tape; this file composes that tape's own growing-source variant with
`NoisyWindowChain.lean`'s chain, so the chain's noise is no longer supplied from outside the world
but emitted by the world's own growing state.

The composite carrier pairs a length-`k` window with an append-only tape (`Decoupling.Mem ℕ ℕ`):
`seqWrite` is `Decoupling.tapeWrite` with the fresh cell carrying the emitted noise bit instead of a
constant, and `compUpdate` steps the window by `NoisyWindowChain.noisyStep` on exactly the bit
`seqWrite` records that step — so the tape *is* the consumed-noise history, and the composite's
window coordinate, read off the tape's own orbit, is the chain's `windowAt` at the word the tape
writes (`windowFst_iterate_compUpdate`).

Against that composite, the counter-free reading transports `GrowingWorld.lean`'s guard verbatim —
no autonomous law reads the window alone once the source is non-constant — while the
counter-including reading closes a staged square exactly as `tapeRead` does.

The second half addresses the escape `not_mixingHoeffding_of_periodic_ne`'s trap needs: **eventual
periodicity of the observation process**, not periodicity of the noise stream and not
unsatisfiability of the trap's hypothesis (`hper` is empirical-mean constancy, which a non-periodic
stream can satisfy). `EventuallyPeriodic` transports between a stream and its chain observation in
both directions (`eventuallyPeriodic_of_eventuallyPeriodic_obs`,
`eventuallyPeriodic_obs_of_eventuallyPeriodic`), so a composite whose source is not eventually
periodic provably never takes the route the trap needs (`not_eventuallyPeriodic_obs_of_not`) — while
`DamageGate.quietStream`, [Inevitability] §6 Theorem 6.6(v″)'s designed source, sits on the forced
side (`eventuallyPeriodic_obs_quietStream`).

The Dirac reading of `BirkhoffTool.MixingHoeffding` turns the hypothesis, at a single fixed
trajectory, into an elementary arithmetic bound (`mixingHoeffding_dirac_iff`,
`mixingHoeffdingTo_dirac_iff`) — consumed verbatim by the oracle corollaries, which quantify over
the measure.

Finally `mephisto`/`mephDecim` name a concrete non-constant source — the Mephisto Waltz's parity of
ternary digit-`2` count, pattern-decimated against disjoint width-`4` blocks matched to the word
`0111` — witnessing the window-only guard's hypothesis at a decidable instance.

## Main results

* `seqWrite`, `advances_seqWrite` — the parametric growing source, and its advance of the landed
  binary tape stages.
* `compUpdate`, `compStage`, `advances_compUpdate` — the composite carrier and its own staged
  advance.
* `windowFst_iterate_compUpdate` — **the orbit bridge**: the composite's window coordinate, from an
  initial window and an empty tape, is the chain's own `windowAt` at the concatenated word.
* `not_exists_stagedSquare_windowOnly` — **the guard**, transported: the window-only reading admits
  no autonomous guest law once the source is non-constant at the two stages compared.
* `counterLaw`, `stagedSquare_compUpdate_counter`, `advances_counterLaw_guestStage` — **the
  square**: the counter-including reading closes against an explicit autonomous law, whose own
  growth `advances_guestStage` then supplies at no further cost.
* `EventuallyPeriodic` — eventual periodicity of a `ℕ`-indexed sequence, absent from Mathlib and
  minted here.
* `eventuallyPeriodic_of_eventuallyPeriodic_obs` — **the load-bearing transport**: eventual
  periodicity of the chain's observation forces eventual periodicity of the source.
* `eventuallyPeriodic_obs_of_eventuallyPeriodic`, `not_eventuallyPeriodic_obs_of_not` — the converse
  transport, completing the iff, and its contrapositive: a non-eventually-periodic source's
  observation is never eventually periodic — the route `not_mixingHoeffding_of_periodic_ne`'s trap
  needs is then absent, for that composite.
* `eventuallyPeriodic_obs_quietStream` — **the contrast**: the designed quiet source of
  [Inevitability] §6 Theorem 6.6(v″) sits on the forced side.
* `mixingHoeffding_dirac_iff`, `mixingHoeffdingTo_dirac_iff` — **the Dirac reading**: at a single
  fixed trajectory, `MixingHoeffding`/`MixingHoeffdingTo` reduce to an explicit per-`n` bound on the
  empirical deviation.
* `mephisto`, `mephDecim` — the named source instance, and `mephDecim_zero`/`mephDecim_one`/
  `mephDecim_two` its small-numeral values, instantiating the window-only guard
  (`not_exists_stagedSquare_windowOnly_mephDecim`).

## Scope

The emit index (`s 0 + 1`) is `seqWrite`'s own local convention, matching `windowAt_succ`'s own
noise offset exactly, and nothing here claims a different one is unavailable.
Deliberately not proved here, and stated as the honest boundary: `mephDecim`'s own
non-eventual-periodicity (an open question — the conditional transport above carries the structure
without it) and any Dirac convergence rate for it (the Dirac iff above is exactly the
named-hypothesis form `MixingHoeffding`/`MixingHoeffdingTo` already are; nothing here proves an
instance of either at `mephDecim`).
No empirical figures — densities or fitted constants — appear in this file.
-/


@[expose] public section

namespace GrowingComposite

/-! ## The parametric growing source, and the composite world -/

/-- **The parametric growing source**: `Decoupling.tapeWrite` with the fresh cell carrying the
emitted bit `ξ` instead of a constant. -/
def seqWrite (ξ : ℕ → Bool) : Decoupling.Mem ℕ ℕ → Decoupling.Mem ℕ ℕ :=
  fun s a => if a = 0 then s 0 + 1 else if a = s 0 + 1 then (ξ (s 0 + 1)).toNat else s a

/-- **`seqWrite` advances the landed binary tape stages.** `advances_tapeStageB`'s own proof shape,
with the constant fresh bit replaced by `ξ`'s: a `Bool.toNat` is at most one. -/
theorem advances_seqWrite (ξ : ℕ → Bool) :
    GrowingWorld.Advances (seqWrite ξ) GrowingWorld.tapeStageB := by
  rintro t s ⟨h0, hbin, hzero⟩
  refine ⟨?_, ?_, ?_⟩
  · simp [seqWrite, h0]
  · intro a ha1 ha2
    simp only [seqWrite]
    rw [ite_eq_right (by omega : a ≠ 0)]
    by_cases hb : a = s 0 + 1
    · simp only [hb]
      cases ξ (s 0 + 1) <;> simp
    · rw [ite_eq_right hb]
      exact hbin a ha1 (by omega)
  · intro a ha
    simp only [seqWrite]
    rw [ite_eq_right (by omega : a ≠ 0), ite_eq_right (by rw [h0]; omega : a ≠ s 0 + 1)]
    exact hzero a (by omega)

/-- **The composite carrier's update**: the window steps by `NoisyWindowChain.noisyStep` on exactly
the bit `seqWrite` records this step, so the tape *is* the consumed-noise history. -/
def compUpdate (k : ℕ) [NeZero k] (ξ : ℕ → Bool) :
    (Fin k → Bool) × Decoupling.Mem ℕ ℕ → (Fin k → Bool) × Decoupling.Mem ℕ ℕ :=
  fun p => (NoisyWindowChain.noisyStep k p.1 (ξ (p.2 0 + 1)), seqWrite ξ p.2)

/-- **The composite's stages**: an arbitrary window, over the landed binary tape stages. -/
def compStage (k : ℕ) (t : ℕ) : Set ((Fin k → Bool) × Decoupling.Mem ℕ ℕ) :=
  Set.univ ×ˢ GrowingWorld.tapeStageB t

/-- **The composite advances its own stages.** -/
theorem advances_compUpdate (k : ℕ) [NeZero k] (ξ : ℕ → Bool) :
    GrowingWorld.Advances (compUpdate k ξ) (compStage k) := by
  rintro t ⟨w, s⟩ ⟨-, hs⟩
  exact ⟨Set.mem_univ _, advances_seqWrite ξ t s hs⟩

/-! ## The orbit bridge -/

/-- The composite's second coordinate, iterated from an empty tape, is `seqWrite`'s own orbit — the
window's own noise argument never reads the first coordinate. -/
private theorem snd_iterate_compUpdate (k : ℕ) [NeZero k] (ξ : ℕ → Bool) (w₀ : Fin k → Bool)
    (t : ℕ) : ((compUpdate k ξ)^[t] (w₀, fun _ => 0)).2 = (seqWrite ξ)^[t] (fun _ => 0) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    simp only [compUpdate, ih]

/-- The orbit's own counter, from an empty tape: after `t` steps the tape's stage counter reads
`t` — the same fact `Decoupling.tapeStage`'s membership names, transported to `seqWrite`. -/
private theorem snd_iterate_compUpdate_zero (k : ℕ) [NeZero k] (ξ : ℕ → Bool) (w₀ : Fin k → Bool)
    (t : ℕ) : ((compUpdate k ξ)^[t] (w₀, fun _ => 0)).2 0 = t := by
  have hmem : (fun _ : ℕ => (0 : ℕ)) ∈ GrowingWorld.tapeStageB 0 := by
    refine ⟨rfl, fun a ha1 ha2 => ?_, fun a _ => ?_⟩
    · omega
    · rfl
  have : (seqWrite ξ)^[t] (fun _ => 0) ∈ GrowingWorld.tapeStageB t := by
    induction t with
    | zero => exact hmem
    | succ t ih => rw [Function.iterate_succ_apply']; exact advances_seqWrite ξ t _ ih
  rw [snd_iterate_compUpdate k ξ w₀ t]
  exact this.1

/-- **The orbit bridge.** Started at an initial window `w₀` and an empty tape, the composite's
window coordinate at time `t` is the chain's own `windowAt` at the concatenated word: `w₀`'s bits,
then the emitted stream `ξ`. -/
theorem windowFst_iterate_compUpdate (k : ℕ) [NeZero k] (ξ : ℕ → Bool) (w₀ : Fin k → Bool)
    (t : ℕ) : ((compUpdate k ξ)^[t] (w₀, fun _ => 0)).1
      = NoisyWindowChain.windowAt k
          (fun u => if h : u < k then w₀ ⟨u, h⟩ else ξ (u - k + 1)) t := by
  set ξ' : ℕ → Bool := fun u => if h : u < k then w₀ ⟨u, h⟩ else ξ (u - k + 1) with hξ'
  induction t with
  | zero =>
    funext i
    have hi : (i : ℕ) < k := i.isLt
    rw [show (compUpdate k ξ)^[0] (w₀, fun _ => 0) = (w₀, fun _ => 0) from rfl]
    change w₀ i = NoisyWindowChain.windowAt k ξ' 0 i
    rw [NoisyWindowChain.windowAt, NoisyWindowChain.obs_of_lt ξ' (by omega)]
    simp only [hξ', Nat.zero_add, dite_eq_left hi]
  | succ t ih =>
    rw [Function.iterate_succ_apply']
    change (compUpdate k ξ ((compUpdate k ξ)^[t] (w₀, fun _ => 0))).1
      = NoisyWindowChain.windowAt k ξ' (t + 1)
    rw [NoisyWindowChain.windowAt_succ ξ' t, ← ih]
    change NoisyWindowChain.noisyStep k ((compUpdate k ξ)^[t] (w₀, fun _ => 0)).1
        (ξ (((compUpdate k ξ)^[t] (w₀, fun _ => 0)).2 0 + 1))
      = NoisyWindowChain.noisyStep k ((compUpdate k ξ)^[t] (w₀, fun _ => 0)).1 (ξ' (t + k))
    rw [snd_iterate_compUpdate_zero k ξ w₀ t]
    congr 1
    have hnk : ¬ (t + k < k) := by omega
    simp only [hξ', dite_eq_right hnk]
    congr 1
    omega

/-! ## The guard and the square -/

/-- `noisyStep` at a fixed window differs whenever its noise argument does: the last window
coordinate is exactly where the noise bit is written. -/
private theorem noisyStep_ne_of_ne (k : ℕ) [NeZero k] (w : Fin k → Bool) {b1 b2 : Bool}
    (hb : b1 ≠ b2) : NoisyWindowChain.noisyStep k w b1 ≠ NoisyWindowChain.noisyStep k w b2 := by
  intro heq
  have hkpos : 0 < k := NeZero.pos k
  have hlast : k - 1 < k := by omega
  have hne : ¬ ((⟨k - 1, hlast⟩ : Fin k) : ℕ) + 1 < k := by
    have : ((⟨k - 1, hlast⟩ : Fin k) : ℕ) = k - 1 := rfl
    omega
  have hcong := congrFun heq ⟨k - 1, hlast⟩
  simp only [NoisyWindowChain.noisyStep, ite_eq_right hne] at hcong
  apply hb
  cases hw : NoisyWindowChain.windowMap k w ⟨k - 1, hlast⟩ <;>
    cases b1 <;> cases b2 <;> simp_all

/-- **The guard, transported.** The window-only reading admits no autonomous guest law over the
composite's product stages once the source's emitted bits differ at the two stages compared: two
states sharing a window force the guest law to send that reading to `noisyStep`'s value at both
noise bits, and `noisyStep_ne_of_ne` says those differ —
`GrowingWorld.not_exists_stagedSquare_tapeDecode`'s pattern, transported from the tape's counter to
the window's own noise argument. -/
theorem not_exists_stagedSquare_windowOnly (k : ℕ) [NeZero k] (ξ : ℕ → Bool) {u v : ℕ}
    (hne : ξ (u + 1) ≠ ξ (v + 1)) :
    ¬ ∃ F : (Fin k → Bool) → (Fin k → Bool),
      GrowingWorld.StagedSquare (compUpdate k ξ) F (fun _ p => p.1) (compStage k) := by
  rintro ⟨F, hF⟩
  set w : Fin k → Bool := fun _ => false with hw
  have hu := hF u (w, GrowingWorld.encode u (fun _ => false))
    ⟨Set.mem_univ _, GrowingWorld.encode_mem u (fun _ => false)⟩
  have hv := hF v (w, GrowingWorld.encode v (fun _ => false))
    ⟨Set.mem_univ _, GrowingWorld.encode_mem v (fun _ => false)⟩
  simp only [compUpdate, GrowingWorld.encode] at hu hv
  exact noisyStep_ne_of_ne k w hne (hu.trans hv.symm)

/-- **The counter-including autonomous law**, driving the composite's noise from a bare stage
counter instead of the tape. -/
def counterLaw (k : ℕ) [NeZero k] (ξ : ℕ → Bool) : (Fin k → Bool) × ℕ → (Fin k → Bool) × ℕ :=
  fun p => (NoisyWindowChain.noisyStep k p.1 (ξ (p.2 + 1)), p.2 + 1)

/-- **The square.** With the counter included in the reading, `counterLaw` closes the staged square
against the composite's own update — `GrowingWorld.stagedSquare_tapeRead`'s pattern, transported. -/
theorem stagedSquare_compUpdate_counter (k : ℕ) [NeZero k] (ξ : ℕ → Bool) :
    GrowingWorld.StagedSquare (compUpdate k ξ) (counterLaw k ξ) (fun _ p => (p.1, p.2 0))
      (compStage k) := by
  rintro t ⟨w, s⟩ ⟨-, hs⟩
  have hs0 : s 0 = t := hs.1
  simp [compUpdate, counterLaw, seqWrite, hs0]

/-- **The guest's own growth**, at no further cost: `advances_guestStage` applied to the square
above. -/
theorem advances_counterLaw_guestStage (k : ℕ) [NeZero k] (ξ : ℕ → Bool) :
    GrowingWorld.Advances (counterLaw k ξ)
      (GrowingWorld.guestStage (fun _ p => (p.1, p.2 0)) (compStage k)) :=
  GrowingWorld.advances_guestStage (advances_compUpdate k ξ) (stagedSquare_compUpdate_counter k ξ)

/-! ## Eventual periodicity: the transport, and the contrast guard -/

/-- `xor` cancels on the left: pure Boolean algebra, proved once at genuine local variables so
`cases` substitutes correctly. -/
private theorem xor_left_cancel {a b c : Bool} (h : xor a b = xor a c) : b = c := by
  cases a <;> cases b <;> cases c <;> simp_all

/-- `xor a b = false` iff `a = b`: the other Boolean fact this file's transport needs. -/
private theorem xor_eq_false_iff {a b : Bool} : xor a b = false ↔ a = b := by
  cases a <;> cases b <;> simp

/-- **The load-bearing direction.** Eventual periodicity of the chain's observation forces eventual
periodicity of the source: `obs_add` solves for the noise bit at every step, so a period of the
observation transports to the source verbatim, past a threshold shifted by the window length. -/
theorem eventuallyPeriodic_of_eventuallyPeriodic_obs {k : ℕ} (hk : 0 < k) {ξ : ℕ → Bool}
    (h : EventuallyPeriodic (NoisyWindowChain.obs k ξ)) : EventuallyPeriodic ξ := by
  obtain ⟨P, N, hP, hper⟩ := h
  refine ⟨P, N + k, hP, ?_⟩
  intro m hm
  obtain ⟨u, rfl⟩ : ∃ u, m = u + k := ⟨m - k, by omega⟩
  have hA := NoisyWindowChain.obs_add hk ξ u
  have hB := NoisyWindowChain.obs_add hk ξ (u + P)
  rw [show u + P + k = u + k + P from by ring, hper (u + k) (by omega),
    hper u (by omega)] at hB
  have hnot := hA.symm.trans hB
  have hxor := congrArg not hnot
  simp only [Bool.not_not] at hxor
  exact (xor_left_cancel hxor).symm

/-- **Completing the iff.** Eventual periodicity of the source transports to the chain's
observation, at period `k * (2 * P)`: `obs_xor_obs_add_mul` at `d = 2 * P` splits, via
`ParityWalk.par_add`, into two `P`-blocks whose terms agree past the threshold — each term of the
second block is a source value `k * P` past the matching term of the first, and the source is
`P`-periodic there — so the two parities cancel and the xor is `false`. -/
theorem eventuallyPeriodic_obs_of_eventuallyPeriodic {k : ℕ} (hk : 0 < k) {ξ : ℕ → Bool}
    (h : EventuallyPeriodic ξ) : EventuallyPeriodic (NoisyWindowChain.obs k ξ) := by
  obtain ⟨P, N, hP, hper⟩ := h
  refine ⟨k * (2 * P), N, by positivity, ?_⟩
  intro u hu
  rw [show 2 * P = P + P from by ring]
  have hiter : ∀ m x, N ≤ x → ξ (x + m * P) = ξ x := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      intro x hx
      rw [show x + (m + 1) * P = (x + P) + m * P from by ring, ih (x + P) (by omega), hper x hx]
  have hfun : (fun i => ξ (u + k * (P + i + 1))) = (fun i => ξ (u + k * (i + 1))) := by
    funext i
    rw [show u + k * (P + i + 1) = (u + k * (i + 1)) + k * P from by ring]
    exact hiter k (u + k * (i + 1)) (by omega)
  have hzero : ParityWalk.par (fun i => ξ (u + k * (i + 1))) (P + P) = false := by
    rw [ParityWalk.par_add (fun i => ξ (u + k * (i + 1))) P P, hfun]
    cases ParityWalk.par (fun i => ξ (u + k * (i + 1))) P <;> rfl
  have hbridge := NoisyWindowChain.obs_xor_obs_add_mul hk ξ u (P + P)
  rw [hzero] at hbridge
  exact (xor_eq_false_iff.mp hbridge).symm

/-- **The escape, as a contrapositive of the load-bearing direction.** A source that is not
eventually periodic gives an observation process that is not eventually periodic either — so the
route `BirkhoffTool.not_mixingHoeffding_of_periodic_ne`'s trap needs, over such a composite, does
not exist. -/
theorem not_eventuallyPeriodic_obs_of_not {k : ℕ} (hk : 0 < k) {ξ : ℕ → Bool}
    (h : ¬ EventuallyPeriodic ξ) : ¬ EventuallyPeriodic (NoisyWindowChain.obs k ξ) :=
  fun hobs => h (eventuallyPeriodic_of_eventuallyPeriodic_obs hk hobs)

/-- **The contrast** ([Growth] §3). `DamageGate.quietStream`, the designed source of
[Inevitability] §6 Theorem 6.6(v″), sits on the forced side: past its last firing the noise reads
identically `false`, so
`obs_add` gives a plain alternation and the observation is eventually periodic at period `2 * k`. -/
theorem eventuallyPeriodic_obs_quietStream (k : ℕ) (hk : 0 < k) (j m : ℕ) :
    EventuallyPeriodic (NoisyWindowChain.obs k (DamageGate.quietStream j m)) := by
  refine ⟨2 * k, j + m, by omega, ?_⟩
  intro u hu
  have hq1 : DamageGate.quietStream j m (u + k) = false := by
    simp only [DamageGate.quietStream, decide_eq_false_iff_not]
    omega
  have hq2 : DamageGate.quietStream j m (u + k + k) = false := by
    simp only [DamageGate.quietStream, decide_eq_false_iff_not]
    omega
  have h1 : NoisyWindowChain.obs k (DamageGate.quietStream j m) (u + k)
      = !(NoisyWindowChain.obs k (DamageGate.quietStream j m) u) := by
    have hraw := NoisyWindowChain.obs_add hk (DamageGate.quietStream j m) u
    rw [hq1] at hraw
    simpa using hraw
  have h2 : NoisyWindowChain.obs k (DamageGate.quietStream j m) (u + k + k)
      = !(NoisyWindowChain.obs k (DamageGate.quietStream j m) (u + k)) := by
    have hraw := NoisyWindowChain.obs_add hk (DamageGate.quietStream j m) (u + k)
    rw [hq2] at hraw
    simpa using hraw
  rw [show u + 2 * k = u + k + k from by ring, h2, h1]
  simp

/-! ## The Dirac reading of `MixingHoeffding` -/

/-- The workhorse: at a single fixed trajectory `ω₀` and a single sample size `n`, the tail bound
over every `τ ≥ 0` is equivalent to the explicit deviation bound at `ω₀` itself — forward by
instantiating at the deviation `τ := |empiricalMean Z n ω₀ - predZ|` (the Dirac mass is one there);
backward by splitting on whether `τ` clears the envelope (the event then misses `ω₀`, measure zero)
or not (the bound's own right side is then at least one). -/
private theorem dirac_tail_iff {X : Type*} [MeasurableSpace X] (ω₀ : ℕ → X)
    (Z : ℕ → (ℕ → X) → ℝ) (predZ c : ℝ) (hc : 0 < c) (hmeas : ∀ i, Measurable (Z i))
    (n : ℕ) (hn : 1 ≤ n) :
    (∀ τ : ℝ, 0 ≤ τ →
      (MeasureTheory.Measure.dirac ω₀).real
          {ω | τ ≤ |SQOracle.empiricalMean Z n ω - predZ|}
        ≤ 2 * Real.exp (-(n : ℝ) * τ ^ 2 / (2 * c)))
      ↔ |SQOracle.empiricalMean Z n ω₀ - predZ| ≤ Real.sqrt (2 * c * Real.log 2 / n) := by
  have hempmeas : Measurable (SQOracle.empiricalMean Z n) := by
    refine Measurable.const_mul ?_ _
    exact Finset.measurable_fun_sum (Finset.range n) fun i _ => hmeas i
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hexp2 : Real.exp (-Real.log 2) = 1 / 2 := by
    rw [Real.exp_neg, Real.exp_log (by norm_num)]; norm_num
  constructor
  · intro hb
    set τ : ℝ := |SQOracle.empiricalMean Z n ω₀ - predZ| with hτdef
    have hτnn : 0 ≤ τ := abs_nonneg _
    have hAmeas : MeasurableSet {ω | τ ≤ |SQOracle.empiricalMean Z n ω - predZ|} :=
      measurableSet_le measurable_const ((hempmeas.sub_const predZ).abs)
    have hmem : ω₀ ∈ {ω | τ ≤ |SQOracle.empiricalMean Z n ω - predZ|} := le_refl τ
    have hval : (MeasureTheory.Measure.dirac ω₀).real
        {ω | τ ≤ |SQOracle.empiricalMean Z n ω - predZ|} = 1 := by
      rw [MeasureTheory.Measure.real, MeasureTheory.Measure.dirac_apply' ω₀ hAmeas]
      simp [Set.indicator, hmem]
    have hbound := hb τ hτnn
    rw [hval] at hbound
    have hge : Real.exp (-Real.log 2) ≤ Real.exp (-(n : ℝ) * τ ^ 2 / (2 * c)) := by
      rw [hexp2]; linarith
    have hle : -Real.log 2 ≤ -(n : ℝ) * τ ^ 2 / (2 * c) := Real.exp_le_exp.mp hge
    have heq : -(n : ℝ) * τ ^ 2 / (2 * c) = -((n : ℝ) * τ ^ 2 / (2 * c)) := by ring
    rw [heq] at hle
    have hstep : (n : ℝ) * τ ^ 2 / (2 * c) ≤ Real.log 2 := by linarith
    have hbound2 : (n : ℝ) * τ ^ 2 ≤ 2 * c * Real.log 2 := by
      rw [div_le_iff₀ (by positivity)] at hstep; nlinarith [hstep]
    rw [Real.le_sqrt hτnn (by positivity), le_div_iff₀ hnR]
    nlinarith [hbound2]
  · intro hle τ hτ
    by_cases hτcase : Real.sqrt (2 * c * Real.log 2 / n) < τ
    · have hAmeas : MeasurableSet {ω | τ ≤ |SQOracle.empiricalMean Z n ω - predZ|} :=
        measurableSet_le measurable_const ((hempmeas.sub_const predZ).abs)
      have hnotmem : ω₀ ∉ {ω | τ ≤ |SQOracle.empiricalMean Z n ω - predZ|} := by
        simp only [Set.mem_ofPred_eq, not_le]
        exact lt_of_le_of_lt hle hτcase
      have hval : (MeasureTheory.Measure.dirac ω₀).real
          {ω | τ ≤ |SQOracle.empiricalMean Z n ω - predZ|} = 0 := by
        rw [MeasureTheory.Measure.real, MeasureTheory.Measure.dirac_apply' ω₀ hAmeas]
        simp [Set.indicator, hnotmem]
      rw [hval]
      positivity
    · push Not at hτcase
      have hτsq : τ ^ 2 ≤ 2 * c * Real.log 2 / n := (Real.le_sqrt hτ (by positivity)).mp hτcase
      have hbound : (n : ℝ) * τ ^ 2 ≤ 2 * c * Real.log 2 := by
        rw [le_div_iff₀ hnR] at hτsq; nlinarith [hτsq]
      have hstep : (n : ℝ) * τ ^ 2 / (2 * c) ≤ Real.log 2 := by
        rw [div_le_iff₀ (by positivity)]; nlinarith [hbound]
      have hle2 : -Real.log 2 ≤ -(n : ℝ) * τ ^ 2 / (2 * c) := by
        have heq : -(n : ℝ) * τ ^ 2 / (2 * c) = -((n : ℝ) * τ ^ 2 / (2 * c)) := by ring
        rw [heq]; linarith
      have hexp := Real.exp_le_exp.mpr hle2
      rw [hexp2] at hexp
      have hrhs : (1 : ℝ) ≤ 2 * Real.exp (-(n : ℝ) * τ ^ 2 / (2 * c)) := by linarith
      exact le_trans MeasureTheory.measureReal_le_one hrhs

/-- **The Dirac reading of `MixingHoeffding`.** At a single fixed trajectory `ω₀`, the FJS-shaped
hypothesis reduces to an explicit per-`n` bound on the empirical deviation: the tail bound clears
one exactly when `τ ≤ √(2c·ln 2 / n)`. The oracle corollaries quantify over the measure, so this
instance is consumed by them verbatim. -/
theorem mixingHoeffding_dirac_iff {X : Type*} [MeasurableSpace X] (ω₀ : ℕ → X)
    (Z : ℕ → (ℕ → X) → ℝ) (predZ c : ℝ) (hc : 0 < c) (hmeas : ∀ i, Measurable (Z i)) :
    BirkhoffTool.MixingHoeffding (MeasureTheory.Measure.dirac ω₀) Z predZ c ↔
      ∀ n : ℕ, 1 ≤ n →
        |SQOracle.empiricalMean Z n ω₀ - predZ| ≤ Real.sqrt (2 * c * Real.log 2 / n) := by
  constructor
  · intro h n hn
    exact (dirac_tail_iff ω₀ Z predZ c hc hmeas n hn).mp (fun τ hτ => h n τ hn hτ)
  · intro h n τ hn hτ
    exact (dirac_tail_iff ω₀ Z predZ c hc hmeas n hn).mpr (h n hn) τ hτ

/-- **The finite-horizon Dirac reading.** The same equivalence for `MixingHoeffdingTo`, with
`n ≤ N` added on both sides — the form current truth takes for a candidate whose Dirac rate is
established only in bounded form. -/
theorem mixingHoeffdingTo_dirac_iff {X : Type*} [MeasurableSpace X] (ω₀ : ℕ → X)
    (Z : ℕ → (ℕ → X) → ℝ) (predZ c : ℝ) (N : ℕ) (hc : 0 < c) (hmeas : ∀ i, Measurable (Z i)) :
    BirkhoffTool.MixingHoeffdingTo N (MeasureTheory.Measure.dirac ω₀) Z predZ c ↔
      ∀ n : ℕ, 1 ≤ n → n ≤ N →
        |SQOracle.empiricalMean Z n ω₀ - predZ| ≤ Real.sqrt (2 * c * Real.log 2 / n) := by
  constructor
  · intro h n hn hnN
    exact (dirac_tail_iff ω₀ Z predZ c hc hmeas n hn).mp (fun τ hτ => h n τ hn hnN hτ)
  · intro h n τ hn hnN hτ
    exact (dirac_tail_iff ω₀ Z predZ c hc hmeas n hn).mpr (h n hn hnN) τ hτ

/-! ## The named source instance -/

/-- **The Mephisto Waltz**: the parity of the count of the ternary digit `2` — a classical
3-automatic sequence. -/
def mephisto (n : ℕ) : Bool := decide ((Nat.digits 3 n).count 2 % 2 = 1)

/-- **The pattern-decimated source**: disjoint width-`4` blocks of the Mephisto Waltz matched
against the word `0111`. -/
def mephDecim (t : ℕ) : Bool :=
  decide (mephisto (4 * t) = false ∧ mephisto (4 * t + 1) = true ∧
    mephisto (4 * t + 2) = true ∧ mephisto (4 * t + 3) = true)

theorem mephDecim_zero : mephDecim 0 = false := by decide

theorem mephDecim_one : mephDecim 1 = true := by decide

theorem mephDecim_two : mephDecim 2 = false := by decide

/-- **The instantiation.** `mephDecim` witnesses the window-only guard's hypothesis: its values at
`1` and `2` differ. -/
theorem not_exists_stagedSquare_windowOnly_mephDecim (k : ℕ) [NeZero k] :
    ¬ ∃ F : (Fin k → Bool) → (Fin k → Bool),
      GrowingWorld.StagedSquare (compUpdate k mephDecim) F (fun _ p => p.1) (compStage k) :=
  not_exists_stagedSquare_windowOnly k mephDecim (u := 0) (v := 1) (by
    change mephDecim 1 ≠ mephDecim 2
    rw [mephDecim_one, mephDecim_two]
    decide)

end GrowingComposite

/-! ## Axiom audit

Every capstone above is `#print axioms`-clean on the standard triple or a subset of it, and the
guards below make that build-enforced. -/

set_option linter.style.longLine false

/-- info: 'GrowingComposite.advances_seqWrite' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GrowingComposite.advances_seqWrite

/-- info: 'GrowingComposite.advances_compUpdate' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GrowingComposite.advances_compUpdate

/-- info: 'GrowingComposite.windowFst_iterate_compUpdate' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GrowingComposite.windowFst_iterate_compUpdate

/-- info: 'GrowingComposite.not_exists_stagedSquare_windowOnly' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GrowingComposite.not_exists_stagedSquare_windowOnly

/-- info: 'GrowingComposite.stagedSquare_compUpdate_counter' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms GrowingComposite.stagedSquare_compUpdate_counter

/-- info: 'GrowingComposite.advances_counterLaw_guestStage' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GrowingComposite.advances_counterLaw_guestStage

/-- info: 'GrowingComposite.eventuallyPeriodic_of_eventuallyPeriodic_obs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GrowingComposite.eventuallyPeriodic_of_eventuallyPeriodic_obs

/-- info: 'GrowingComposite.eventuallyPeriodic_obs_of_eventuallyPeriodic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GrowingComposite.eventuallyPeriodic_obs_of_eventuallyPeriodic

/-- info: 'GrowingComposite.not_eventuallyPeriodic_obs_of_not' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GrowingComposite.not_eventuallyPeriodic_obs_of_not

/-- info: 'GrowingComposite.eventuallyPeriodic_obs_quietStream' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GrowingComposite.eventuallyPeriodic_obs_quietStream

/-- info: 'GrowingComposite.mixingHoeffding_dirac_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GrowingComposite.mixingHoeffding_dirac_iff

/-- info: 'GrowingComposite.mixingHoeffdingTo_dirac_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GrowingComposite.mixingHoeffdingTo_dirac_iff

/-- info: 'GrowingComposite.mephDecim_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GrowingComposite.mephDecim_zero

/-- info: 'GrowingComposite.mephDecim_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GrowingComposite.mephDecim_one

/-- info: 'GrowingComposite.mephDecim_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GrowingComposite.mephDecim_two

/-- info: 'GrowingComposite.not_exists_stagedSquare_windowOnly_mephDecim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GrowingComposite.not_exists_stagedSquare_windowOnly_mephDecim
