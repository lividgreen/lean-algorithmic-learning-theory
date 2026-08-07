/-
Copyright (c) 2026 Mykola Palamarchuk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mykola Palamarchuk
-/
import ALT.FlooredMixture
import ALT.LearningWitness

-- Formal-check file, not Mathlib-destined: opt out of the house-style header linter.
set_option linter.style.header false

/-!
# The floored mixture on the witness's own trajectory ([Inevitability] §6)

This module claims **the assembly only**. Both halves already exist and neither is re-proved here:
the agnostic event bound for the floored mixture is `ALT/FlooredMixture.lean`'s
(`floorSurprise_card_mul_le_missCount`, where the Littlestone–Warmuth attribution lives), and the
noisy window chain with its recursion is `ALT/NoisyWindowChain.lean`'s, embedded as a substrate in
`ALT/LearningWitness.lean`. What is new is that the two meet **at the miss indicator**.

## The meeting point

The learning witness runs the `k` single-literal predictors over a length-`k` window: candidate `i`
reads window coordinate `i` — `windowAt k ξ t i = obs k ξ (t + i)` — and predicts the complement of
what it reads, `singleLiteral i w = !(w i)`; the symbol it is predicting is the one just past the
window, `obs k ξ (t + k)`. Candidate `0` is the chain's own rule. The chain's recursion
`obs_add` says `o_{t+k} = ¬o_t ⊕ ξ_{t+k}`, so candidate `0`'s prediction `¬o_t` differs from the
realized symbol **exactly when the noise bit fires**: `witMiss_zero` is that identity, and
`missCount_witMiss_zero` promotes it to an equality of counts — the true rule's miss count *is* the
noise count, not merely bounded by it.

The floored mixture riding that trajectory therefore inherits its surprise budget with the noise
priced in. `witness_floorSurprise_card_mul_le` is the pathwise capstone: for **every** noise stream,
under the budget gate alone, `card · θ ≤ 4(k−1) + 2k · noiseCount`. No probability enters it.
`witness_integral_floorSurprise_le` then averages it under the witness's own Bernoulli(`η`) noise
law, giving `4(k−1) + 2kηn`.

The reading [Inevitability] §6 takes from this is that on the learning branch the damage budget is a
**rate** — slope `2kη/θ` in the run length — where the emergence branch's, holding a candidate that
never misses, stays lifetime-free. The rate is not slack: the miss-count term's coefficient is
bracketed from below by the sharpness families of `FlooredMixture`, and the true rule really does
miss at the noise rate.

## Main results

* `witMiss` — the witness's miss indicator, pathwise in the noise stream; `witMiss_eq_not_xor` is
  its normal form and `measurable_witMiss` its measurability.
* `noiseCount` — how often the noise bit has fired in the window's own offset.
* `witMiss_zero`, `missCount_witMiss_zero` — the identity and its count form.
* `witness_floorSurprise_card_mul_le` — **the pathwise capstone**.
* `witness_floorSurprise_card_lt` — the non-vacuity guard: a strict gap forces the surprise count
  below the horizon, beating the trivial `card ≤ n` bound.
* `witness_floorSurprise_bound_ge_n_of_le` — the complementary vacuity: below the gate the bound's
  own right-hand side is no better than the horizon.
* `witness_floorSurprise_card_lt_of_rate` — the guard in [Inevitability] §6's rate form.
* `witness_toDist_wRun_sub_bayesFrom_le` — **the composed drift bound** ([Inevitability] §7), at a
  restart point the noise stream supplies as noise-freedom but not as co-leadership.
* `witness_toDist_wRun_sub_bayesRun_le` — the start-of-run corollary: co-leadership holds for free
  at `s = 0`, leaving the noise-free prefix as the only hypothesis.
* `singleNoiseBit`, `witness_singleNoiseBit_not_coleader` — the guard: a fixed instance where the
  witness does not supply co-leadership at a later restart point.
* `integral_noiseCount` — the noise count's mean, `ηn`, under `LearningWitness.noiseLaw`.
* `witness_integral_floorSurprise_le` — **the expectation corollary**.

## Scope

This is a **process-level** composition: the mixture reads the observation stream, and the noise is
law-level external randomness. No skew-product embedding of the noisy base is attempted, and the
mixing base with its invariant measure stays unformalized — [Inevitability] §8's recorded boundary.
The bound's miss-count coefficient is the `2C` that `FlooredMixture` proves, not the `[θ, 2θ]` its
sharpness pair brackets; that gap is inherited, not opened here.

The drift-bound composition carries its own boundary. Its co-leadership hypothesis is not something
the noise stream supplies at a general restart point — `witness_singleNoiseBit_not_coleader` fixes
an instance where it fails — and it is discharged for free only at the run's own start.
-/

namespace WitnessMixture

open MeasureTheory ProbabilityTheory NoisyWindowChain WeightedFiber

/-! ## The miss indicator and the noise count -/

/-- How often the noise bit driving the step into time `t + k` has fired, over the first `n`
steps. This is the witness's noise stream read at the chain's own offset. -/
def noiseCount (ξ : ℕ → Bool) (k n : ℕ) : ℕ := ((Finset.range n).filter fun t => ξ (t + k)).card

/-- **The witness's miss indicator**, pathwise in the noise stream: candidate `i` predicts the
complement of window coordinate `i` — the window at time `t` being `obs k ξ (t + ·)` — and the
symbol it is predicting is `obs k ξ (t + k)`, the one just past the window. -/
def witMiss (k : ℕ) (ξ : ℕ → Bool) : ℕ → Fin k → Bool :=
  fun t i => decide ((!(obs k ξ (t + (i : ℕ)))) ≠ obs k ξ (t + k))

/-- The miss indicator's normal form: a candidate misses exactly when its window coordinate and the
realized symbol **agree** — its prediction being that coordinate's complement. -/
theorem witMiss_eq_not_xor (k : ℕ) (ξ : ℕ → Bool) (t : ℕ) (i : Fin k) :
    witMiss k ξ t i = !(xor (obs k ξ (t + (i : ℕ))) (obs k ξ (t + k))) := by
  rw [witMiss]
  cases obs k ξ (t + (i : ℕ)) <;> cases obs k ξ (t + k) <;> rfl

/-- **The identity the assembly turns on.** Candidate `0` is the chain's own rule, and its miss at
time `t` *is* the noise bit written into the step it is predicting.

One unfolding of the chain's recursion `obs_add`: the realized symbol is `¬o_t ⊕ ξ_{t+k}` and the
prediction is `¬o_t`, so the two differ precisely when `ξ_{t+k}` fires. -/
theorem witMiss_zero {k : ℕ} [NeZero k] (ξ : ℕ → Bool) (t : ℕ) :
    witMiss k ξ t 0 = ξ (t + k) := by
  have hk : 0 < k := Nat.pos_of_ne_zero (NeZero.ne k)
  have hz : ((0 : Fin k) : ℕ) = 0 := by simp
  rw [witMiss_eq_not_xor, hz, Nat.add_zero, obs_add hk]
  cases obs k ξ t <;> cases ξ (t + k) <;> rfl

/-- **The count form.** The true rule's miss count over the first `n` steps *is* the noise count —
an equality, not a bound, which is what lets the tracking bound be read as a noise rate. -/
theorem missCount_witMiss_zero {k : ℕ} [NeZero k] (ξ : ℕ → Bool) (n : ℕ) :
    missCount (witMiss k ξ) 0 n = noiseCount ξ k n := by
  rw [missCount, noiseCount]
  exact congrArg Finset.card (Finset.filter_congr fun t _ => by rw [witMiss_zero])

/-! ## The pathwise capstone -/

/-- **The floored mixture on the witness's own trajectory, pathwise.**

`FlooredMixture.floorSurprise_card_mul_le_missCount` read at `C = k`, `i₀ = 0`, with
`missCount_witMiss_zero` rewriting the reference candidate's miss count into the noise count. For
**every** noise stream, under the budget gate alone, the mixture's surprises are bounded by a
lifetime-free anchor `4(k−1)` plus `2k` per noise bit.

No probability enters: this is a statement about each trajectory separately, and the noise stream is
an arbitrary function. What the composition buys [Inevitability] §6 is that the hypothesis the
unbounded-run guarantee needs is one the noisy witness *supplies* — its true rule's misses are
counted rather than forbidden — where realizability was one it refuted. -/
theorem witness_floorSurprise_card_mul_le {k : ℕ} [NeZero k] (ξ : ℕ → Bool) (b : ℕ) (θ : ℚ)
    (hbudget : 2 * ((k : ℚ) - 1) ≤ θ * 2 ^ b) (n : ℕ) :
    ((floorSurpriseSet (witMiss k ξ) b θ n).card : ℚ) * θ
      ≤ 4 * ((k : ℚ) - 1) + 2 * (k : ℚ) * (noiseCount ξ k n : ℚ) := by
  have h := floorSurprise_card_mul_le_missCount (witMiss k ξ) b θ hbudget 0 n
  rwa [missCount_witMiss_zero] at h

/-! ## Non-vacuity: when the tracking bound beats the trivial one

The pathwise capstone bounds the surprise count by `(4(k−1) + 2k·noiseCount)/θ`, but every count
over a horizon `n` is already at most `n`; the bound says something only where its own right-hand
side, divided by `θ`, falls strictly below `n`. [Inevitability] §6 reads that boundary as
`η < θ/(2k)`: the guard below states the strict side, the statement after it the failing side, so
the hypothesis is shown load-bearing rather than decorative. -/

/-- **The guard**: a strict gap between the pathwise bound and `θ·n` forces the surprise count
strictly below the horizon — the tracking bound beats the trivial `card ≤ n` bound outright. -/
theorem witness_floorSurprise_card_lt {k : ℕ} [NeZero k] (ξ : ℕ → Bool) (b : ℕ) (θ : ℚ)
    (hθ : 0 < θ) (hbudget : 2 * ((k : ℚ) - 1) ≤ θ * 2 ^ b) (n : ℕ)
    (hgap : 4 * ((k : ℚ) - 1) + 2 * (k : ℚ) * (noiseCount ξ k n : ℚ) < θ * n) :
    (floorSurpriseSet (witMiss k ξ) b θ n).card < n := by
  have hle := witness_floorSurprise_card_mul_le ξ b θ hbudget n
  have hlt : ((floorSurpriseSet (witMiss k ξ) b θ n).card : ℚ) * θ < (n : ℚ) * θ := by
    calc ((floorSurpriseSet (witMiss k ξ) b θ n).card : ℚ) * θ
        ≤ 4 * ((k : ℚ) - 1) + 2 * (k : ℚ) * (noiseCount ξ k n : ℚ) := hle
      _ < θ * n := hgap
      _ = (n : ℚ) * θ := mul_comm θ n
  exact_mod_cast lt_of_mul_lt_mul_right hlt hθ.le

/-- **The complementary vacuity.** Below the gate — `θ·n ≤ 4(k−1) + 2k·noiseCount` — the bound's own
right-hand side, divided by `θ`, is at least the horizon `n`: it permits every step to be a
surprise, exactly what the trivial `card ≤ n` bound already says, so
`witness_floorSurprise_card_lt`'s hypothesis is reachable and its failure is not vacuous either.
Arithmetic only, on the numbers `θ`, `n` and `noiseCount`, no system involved. -/
theorem witness_floorSurprise_bound_ge_n_of_le {k : ℕ} (ξ : ℕ → Bool) (θ : ℚ) (hθ : 0 < θ)
    (n : ℕ) (hgap : θ * n ≤ 4 * ((k : ℚ) - 1) + 2 * (k : ℚ) * (noiseCount ξ k n : ℚ)) :
    (n : ℚ) ≤ (4 * ((k : ℚ) - 1) + 2 * (k : ℚ) * (noiseCount ξ k n : ℚ)) / θ := by
  rw [le_div_iff₀' hθ]
  exact hgap

/-- **The rate form.** Since the noise count never exceeds the horizon, the guard already fires
once `noiseCount`'s own coefficient clears the gap — the "slope `2kη/θ` below one" reading
[Inevitability] §6 states the bound in. -/
theorem witness_floorSurprise_card_lt_of_rate {k : ℕ} [NeZero k] (ξ : ℕ → Bool) (b : ℕ)
    (θ : ℚ) (hθ : 0 < θ) (hbudget : 2 * ((k : ℚ) - 1) ≤ θ * 2 ^ b) (n : ℕ)
    (hgap : 2 * (k : ℚ) * (noiseCount ξ k n : ℚ) < θ * n - 4 * ((k : ℚ) - 1)) :
    (floorSurpriseSet (witMiss k ξ) b θ n).card < n :=
  witness_floorSurprise_card_lt ξ b θ hθ hbudget n (by linarith)

/-! ## The drift bound on the witness's own trajectory ([Inevitability] §7)

`FlooredMixture.toDist_wRun_sub_bayesFrom_le` compares the floored run not with exact Bayes from
the beginning but with exact Bayes **restarted** at a running co-leader that misses at no step of
the window, and it asks nothing about the run before the restart point. Composed with `witMiss_zero`
the miss-freedom hypothesis becomes a statement about the noise stream: the reference candidate
misses at no step of `[s, t)` exactly when the noise bit has not fired there.

Co-leadership is a different matter. It is **not** supplied by the witness in general: the exponent
ceiling caps how far ahead the true rule's own running total can get, so one noise bit can hand a
competitor the whole budget outright, at a restart point well inside the run.
`witness_singleNoiseBit_not_coleader` proves this for a fixed instance — the construction fails the
hypothesis, not merely the general theorem's proof.

At the run's own start, `s = 0`, co-leadership holds for free: every candidate starts at exponent
`0`, leaving the noise-free prefix as the composition's only remaining hypothesis. That is
`witness_toDist_wRun_sub_bayesRun_le`, the one form of the composition that carries nothing beyond
the noise stream itself. -/

/-- **The drift bound on the witness's own trajectory, composed at a restart point.**

`FlooredMixture.toDist_wRun_sub_bayesFrom_le` read at `iL = 0`, with `witMiss_zero` rewriting the
reference candidate's miss-freedom hypothesis into a statement about the noise stream alone: no
noise bit fires in `[s, t)`. The running-co-leader hypothesis is carried unchanged — the witness
does not discharge it, and `witness_singleNoiseBit_not_coleader` shows a fixed instance where it
fails. Under both, the floored run's reading at `t` stays within `2(k−1)/2^b` of exact Bayes
restarted at `s` from the floored run's own state there. -/
theorem witness_toDist_wRun_sub_bayesFrom_le {k : ℕ} [NeZero k] (ξ : ℕ → Bool) (b : ℕ) {s t : ℕ}
    (hst : s ≤ t) (hlead : ∀ j, expRun (witMiss k ξ) b s j ≤ expRun (witMiss k ξ) b s 0)
    (hnoise : ∀ u, s ≤ u → u < t → ξ (u + k) = false) :
    ∑ i, |toDist (raw (wRun (2 ^ b) (missFit (witMiss k ξ)) t)) i
        - toDist (bayesFrom (witMiss k ξ) b s t) i| ≤ 2 * ((k : ℚ) - 1) / 2 ^ b :=
  toDist_wRun_sub_bayesFrom_le (witMiss k ξ) b (iL := 0) hst hlead
    (fun u hu1 hu2 => by rw [witMiss_zero]; exact hnoise u hu1 hu2)

/-- **The start-of-run corollary: the one form that carries nothing beyond the noise stream.**

`expRun (witMiss k ξ) b 0` is identically zero, so at `s = 0` every candidate starts as a running
co-leader and the composition above's other hypothesis discharges outright. The floored run's
reading at `t` then stays within `2(k−1)/2^b` of exact Bayes run from the start, provided only that
the noise stream has not fired anywhere in `[0, t)`. -/
theorem witness_toDist_wRun_sub_bayesRun_le {k : ℕ} [NeZero k] (ξ : ℕ → Bool) (b t : ℕ)
    (hnoise : ∀ u, u < t → ξ (u + k) = false) :
    ∑ i, |toDist (raw (wRun (2 ^ b) (missFit (witMiss k ξ)) t)) i
        - toDist (bayesRun (missFit (witMiss k ξ)) t) i| ≤ 2 * ((k : ℚ) - 1) / 2 ^ b := by
  have hbf : bayesRun (missFit (witMiss k ξ)) t = bayesFrom (witMiss k ξ) b 0 t := by
    funext i
    exact (bayesFrom_zero (witMiss k ξ) b t i).symm
  rw [hbf]
  exact witness_toDist_wRun_sub_bayesFrom_le ξ b (Nat.zero_le t) (fun j => by simp [expRun])
    (fun u _ hu => hnoise u hu)

/-! ### The guard: co-leadership is not free at a general restart point

The pathwise capstone above needs no hypothesis on the other candidates, but the drift bound's
co-leader hypothesis is a real constraint on the witness, not a bookkeeping formality. The instance
below fixes `k = 2`, `b = 1` and a noise stream firing at one position, and shows the running
co-leader condition failing at the step right after the reference candidate's own miss: one noise
bit is enough to hand the whole exponent budget to the other candidate. -/

/-- **A noise stream firing once, at position `3`.** Read against the length-`2` window: both
candidates hit at time `0` and at time `1`, but the reference candidate's own miss at time `1` (its
window reads the fired bit) leaves it at exponent `0` a step later, while the other candidate — who
read past the noise bit and kept hitting — holds the ceiling. -/
def singleNoiseBit : ℕ → Bool := fun u => decide (u = 3)

/-- **Co-leadership fails at the step after the reference candidate's own miss.** At `s = 2` the
exponent vector is `(0, 1)`: the reference candidate the composition above always reads as `iL` is
no longer a co-leader, so its hypothesis is not something the witness supplies — it is refuted by
this fixed instance, not merely absent from what is proved. -/
theorem witness_singleNoiseBit_not_coleader :
    ¬ (∀ j : Fin 2, expRun (witMiss 2 singleNoiseBit) 1 2 j
        ≤ expRun (witMiss 2 singleNoiseBit) 1 2 0) := by
  intro h
  have hj := h 1
  have h0 : expRun (witMiss 2 singleNoiseBit) 1 2 0 = 0 := by decide
  have h1 : expRun (witMiss 2 singleNoiseBit) 1 2 1 = 1 := by decide
  omega

/-! ## Measurability: the surprise count is a cylinder function

Everything below is plumbing for the expectation corollary. The floored run's whole state at time
`t` is `expRun` at `t`, which reads the miss indicator strictly before `t`; so the surprise count
over the first `n` steps depends on the noise stream only through the finitely many Bools
`witMiss k ω s i` with `s < n`. Factoring through that finite tuple makes measurability immediate,
the tuple space being discrete. -/

section Measurability

variable {C : ℕ}

/-- The exponent automaton at time `t` reads the miss indicator strictly before `t`. -/
private lemma expRun_congr {M M' : ℕ → Fin C → Bool} (b : ℕ) :
    ∀ t : ℕ, (∀ s, s < t → M s = M' s) → expRun M b t = expRun M' b t := by
  intro t
  induction t with
  | zero => intro _; rfl
  | succ t ih =>
      intro h
      change expStep b (M t) (expRun M b t) = expStep b (M' t) (expRun M' b t)
      rw [ih fun s hs => h s (by omega), h t (by omega)]

/-- The wrong mass at time `t` reads the miss indicator up to and including `t`. -/
private lemma wrongMass_congr {M M' : ℕ → Fin C → Bool} (b t : ℕ)
    (h : ∀ s, s ≤ t → M s = M' s) : wrongMass M b t = wrongMass M' b t := by
  have hv : raw (wRun (2 ^ b) (missFit M) t) = raw (wRun (2 ^ b) (missFit M') t) := by
    funext i
    rw [wRun_eq_pow_expRun, wRun_eq_pow_expRun,
      congrFun (expRun_congr b t fun s hs => h s hs.le) i]
  rw [wrongMass, wrongMass, hv, h t le_rfl]

/-- The surprise set over the first `n` steps reads the miss indicator strictly before `n`. -/
private lemma floorSurpriseSet_congr {M M' : ℕ → Fin C → Bool} (b : ℕ) (θ : ℚ) (n : ℕ)
    (h : ∀ s, s < n → M s = M' s) :
    floorSurpriseSet M b θ n = floorSurpriseSet M' b θ n := by
  rw [floorSurpriseSet, floorSurpriseSet]
  exact Finset.filter_congr fun t ht => by
    rw [wrongMass_congr b t fun s hs => h s (lt_of_le_of_lt hs (Finset.mem_range.mp ht))]

variable {k : ℕ}

/-- The chain's observation at a fixed time, as a function of the noise stream. -/
private lemma measurable_obs_coord [NeZero k] (u : ℕ) :
    Measurable fun ω : ℕ → Bool => obs k ω u :=
  (measurable_pi_apply u).comp
    (measurable_traj (ξ := fun i (ω : ℕ → Bool) => ω i)
      (Nat.one_le_iff_ne_zero.mpr (NeZero.ne k)) fun i => measurable_pi_apply i)

/-- Each miss bit is measurable in the noise stream: it reads two observations, each a parity walk
over finitely many noise coordinates. -/
theorem measurable_witMiss [NeZero k] (t : ℕ) (i : Fin k) :
    Measurable fun ω : ℕ → Bool => witMiss k ω t i := by
  have h : (fun ω : ℕ → Bool => witMiss k ω t i)
      = fun ω => !(xor (obs k ω (t + (i : ℕ))) (obs k ω (t + k))) := by
    funext ω; rw [witMiss_eq_not_xor]
  rw [h]
  exact (Measurable.of_discrete (f := fun c : Bool => !c)).comp
    (ParityWalk.measurable_xor (measurable_obs_coord _) (measurable_obs_coord _))

/-- The finite tuple the surprise count factors through. -/
private def witTuple (k n : ℕ) (ω : ℕ → Bool) : Fin n → Fin k → Bool :=
  fun s i => witMiss k ω (s : ℕ) i

/-- The tuple read back as a miss indicator, junk past the horizon. -/
private def witExtend (k n : ℕ) (v : Fin n → Fin k → Bool) : ℕ → Fin k → Bool :=
  fun s i => if h : s < n then v ⟨s, h⟩ i else false

private lemma witExtend_witTuple (k n : ℕ) (ω : ℕ → Bool) {s : ℕ} (hs : s < n) :
    witExtend k n (witTuple k n ω) s = witMiss k ω s := by
  funext i
  rw [witExtend, dif_pos hs, witTuple]

private lemma measurable_witTuple [NeZero k] (n : ℕ) : Measurable (witTuple k n) :=
  measurable_pi_lambda _ fun _ => measurable_pi_lambda _ fun _ => measurable_witMiss _ _

/-- **The surprise count is measurable in the noise stream** — it is a cylinder function of the
first `n` miss vectors, and the tuple space carrying them is discrete. -/
theorem measurable_floorSurpriseCard [NeZero k] (b : ℕ) (θ : ℚ) (n : ℕ) :
    Measurable fun ω : ℕ → Bool => ((floorSurpriseSet (witMiss k ω) b θ n).card : ℝ) := by
  have h : (fun ω : ℕ → Bool => ((floorSurpriseSet (witMiss k ω) b θ n).card : ℝ))
      = (fun v : Fin n → Fin k → Bool =>
          ((floorSurpriseSet (witExtend k n v) b θ n).card : ℝ)) ∘ witTuple k n := by
    funext ω
    exact congrArg (fun m : ℕ => (m : ℝ)) (congrArg Finset.card
      (floorSurpriseSet_congr b θ n fun s hs => witExtend_witTuple k n ω hs)).symm
  rw [h]
  exact Measurable.of_discrete.comp (measurable_witTuple n)

/-- The surprise count never exceeds the horizon: it counts steps below `n`. -/
private lemma floorSurpriseCard_le (M : ℕ → Fin C → Bool) (b : ℕ) (θ : ℚ) (n : ℕ) :
    (floorSurpriseSet M b θ n).card ≤ n := by
  rw [floorSurpriseSet]
  exact le_trans (Finset.card_filter_le _ _) (le_of_eq (Finset.card_range n))

end Measurability

/-! ## The expectation corollary -/

section Expectation

variable {k : ℕ}

private lemma integrable_of_bounded {μ : Measure (ℕ → Bool)} [IsFiniteMeasure μ]
    {f : (ℕ → Bool) → ℝ} (hf : Measurable f) {c : ℝ} (hb : ∀ ω, ‖f ω‖ ≤ c) :
    Integrable f μ :=
  (integrable_const c).mono' hf.aestronglyMeasurable (Filter.Eventually.of_forall hb)

private lemma measurable_noiseIndicator (j : ℕ) :
    Measurable fun ω : ℕ → Bool => if ω j then (1 : ℝ) else 0 :=
  (Measurable.of_discrete (f := fun c : Bool => if c then (1 : ℝ) else 0)).comp
    (measurable_pi_apply j)

/-- One noise coordinate's mean under the Bernoulli(`p`) shift: the fire probability itself. -/
private lemma integral_noiseIndicator (p : unitInterval) (j : ℕ) :
    ∫ ω : ℕ → Bool, (if ω j then (1 : ℝ) else 0) ∂(LearningWitness.noiseLaw p) = (p : ℝ) := by
  have hmap : (LearningWitness.noiseLaw p).map (fun ω : ℕ → Bool => ω j)
      = ProbabilityTheory.bernoulliMeasure true false p :=
    Measure.infinitePi_map_eval _ j
  have hfm : Measurable fun c : Bool => if c then (1 : ℝ) else 0 := Measurable.of_discrete
  have hsm : AEStronglyMeasurable (fun c : Bool => if c then (1 : ℝ) else 0)
      ((LearningWitness.noiseLaw p).map fun ω : ℕ → Bool => ω j) := hfm.aestronglyMeasurable
  have h : ∫ ω : ℕ → Bool, (if ω j then (1 : ℝ) else 0) ∂(LearningWitness.noiseLaw p)
      = ∫ c : Bool, (if c then (1 : ℝ) else 0)
          ∂(ProbabilityTheory.bernoulliMeasure true false p) := by
    rw [← hmap, integral_map (measurable_pi_apply j).aemeasurable hsm]
  rw [h, ProbabilityTheory.integral_bernoulliMeasure]
  simp

private lemma noiseCount_eq_sum (ξ : ℕ → Bool) (k n : ℕ) :
    (noiseCount ξ k n : ℝ) = ∑ t ∈ Finset.range n, (if ξ (t + k) then (1 : ℝ) else 0) := by
  rw [noiseCount, Finset.card_filter]
  push_cast
  exact Finset.sum_congr rfl fun t _ => by split <;> simp

private lemma measurable_noiseCount (k n : ℕ) :
    Measurable fun ω : ℕ → Bool => (noiseCount ω k n : ℝ) := by
  have h : (fun ω : ℕ → Bool => (noiseCount ω k n : ℝ))
      = fun ω => ∑ t ∈ Finset.range n, (if ω (t + k) then (1 : ℝ) else 0) := by
    funext ω; rw [noiseCount_eq_sum]
  rw [h]
  exact Finset.measurable_sum _ fun t _ => measurable_noiseIndicator (t + k)

/-- **The noise count's mean is `ηn`** under the witness's own Bernoulli(`η`) shift: `n` coordinate
indicators, each of mean `η`, by linearity. -/
theorem integral_noiseCount (p : unitInterval) (k n : ℕ) :
    ∫ ω, (noiseCount ω k n : ℝ) ∂(LearningWitness.noiseLaw p) = (p : ℝ) * n := by
  have h : ∫ ω, (noiseCount ω k n : ℝ) ∂(LearningWitness.noiseLaw p)
      = ∫ ω, ∑ t ∈ Finset.range n, (if ω (t + k) then (1 : ℝ) else 0)
          ∂(LearningWitness.noiseLaw p) :=
    integral_congr_ae (Filter.Eventually.of_forall fun ω => noiseCount_eq_sum ω k n)
  rw [h, integral_finsetSum _ fun t _ =>
    integrable_of_bounded (measurable_noiseIndicator (t + k)) (c := 1) fun ω => by
      split <;> simp]
  rw [Finset.sum_congr rfl fun t _ => integral_noiseIndicator p (t + k)]
  simp [mul_comm]

/-- **The floored mixture on the witness's own trajectory, in expectation.**

The pathwise capstone averaged under `LearningWitness.noiseLaw`, the Bernoulli(`η`) shift that makes
the witness's whole hypothesis block inhabited. The integrand is a cylinder function of finitely
many noise coordinates, hence measurable and bounded; the right-hand side is
`integral_noiseCount`'s `ηn` carried through by linearity.

This is the damage budget as a **rate**: `4(k−1)` is the lifetime-free anchor the emergence branch
also gets, and `2kηn` is what the learning branch pays for a true rule that misses at the noise rate
— slope `2kη/θ` in the run length once divided through by the threshold. -/
theorem witness_integral_floorSurprise_le [NeZero k] (p : unitInterval) (b : ℕ) (θ : ℚ)
    (hbudget : 2 * ((k : ℚ) - 1) ≤ θ * 2 ^ b) (n : ℕ) :
    ∫ ω, ((floorSurpriseSet (witMiss k ω) b θ n).card : ℝ) * (θ : ℝ)
        ∂(LearningWitness.noiseLaw p)
      ≤ 4 * ((k : ℝ) - 1) + 2 * (k : ℝ) * (p : ℝ) * n := by
  have hpath : ∀ ω : ℕ → Bool,
      ((floorSurpriseSet (witMiss k ω) b θ n).card : ℝ) * (θ : ℝ)
        ≤ 4 * ((k : ℝ) - 1) + 2 * (k : ℝ) * (noiseCount ω k n : ℝ) := by
    intro ω
    exact_mod_cast witness_floorSurprise_card_mul_le ω b θ hbudget n
  have hleft : Integrable
      (fun ω : ℕ → Bool => ((floorSurpriseSet (witMiss k ω) b θ n).card : ℝ) * (θ : ℝ))
      (LearningWitness.noiseLaw p) := by
    refine integrable_of_bounded ((measurable_floorSurpriseCard b θ n).mul_const _)
      (c := (n : ℝ) * |(θ : ℝ)|) fun ω => ?_
    rw [norm_mul, Real.norm_natCast, Real.norm_eq_abs]
    have hcard : (((floorSurpriseSet (witMiss k ω) b θ n).card : ℕ) : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast floorSurpriseCard_le (witMiss k ω) b θ n
    exact mul_le_mul_of_nonneg_right hcard (abs_nonneg _)
  have hright : Integrable
      (fun ω : ℕ → Bool => 4 * ((k : ℝ) - 1) + 2 * (k : ℝ) * (noiseCount ω k n : ℝ))
      (LearningWitness.noiseLaw p) :=
    (integrable_const _).add
      ((integrable_of_bounded (measurable_noiseCount k n) (c := (n : ℝ)) fun ω => by
        rw [Real.norm_natCast]
        exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _) |>.trans
          (le_of_eq (Finset.card_range n))).const_mul _)
  refine le_trans (integral_mono hleft hright hpath) (le_of_eq ?_)
  rw [integral_add (integrable_const _)
    ((integrable_of_bounded (measurable_noiseCount k n) (c := (n : ℝ)) fun ω => by
      rw [Real.norm_natCast]
      exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _) |>.trans
        (le_of_eq (Finset.card_range n))).const_mul _),
    integral_const, integral_const_mul, integral_noiseCount]
  simp
  ring

end Expectation

end WitnessMixture

/-- info: 'WitnessMixture.witness_floorSurprise_card_mul_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms WitnessMixture.witness_floorSurprise_card_mul_le

/-- info: 'WitnessMixture.witness_floorSurprise_card_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms WitnessMixture.witness_floorSurprise_card_lt

/-- info: 'WitnessMixture.witness_floorSurprise_bound_ge_n_of_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms WitnessMixture.witness_floorSurprise_bound_ge_n_of_le

/-- info: 'WitnessMixture.witness_floorSurprise_card_lt_of_rate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms WitnessMixture.witness_floorSurprise_card_lt_of_rate

/-- info: 'WitnessMixture.witness_toDist_wRun_sub_bayesFrom_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms WitnessMixture.witness_toDist_wRun_sub_bayesFrom_le

/-- info: 'WitnessMixture.witness_toDist_wRun_sub_bayesRun_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms WitnessMixture.witness_toDist_wRun_sub_bayesRun_le

/-- info: 'WitnessMixture.witness_singleNoiseBit_not_coleader' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms WitnessMixture.witness_singleNoiseBit_not_coleader

/-- info: 'WitnessMixture.witness_integral_floorSurprise_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms WitnessMixture.witness_integral_floorSurprise_le
