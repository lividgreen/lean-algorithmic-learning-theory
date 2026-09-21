/-
Copyright (c) 2026 Mykola Palamarchuk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mykola Palamarchuk
-/
module

public import Mathlib.Algebra.Order.Ring.Pow
public import ALT.BasinSettling

-- Formal-check file, not Mathlib-destined: opt out of the house-style header linter.
set_option linter.style.header false

/-!
# The log-mass event bound over seeded starts ([Discovery] §3.3)

`FlooredMixture` prices the floored mixture's surprises against the *pool*: the realizable event
bound is `card · θ ≤ 4(C−1)`, linear in the candidate count, and that constant is the price of the
uniform prior the run starts from. This file changes the currency. The run is started from an
arbitrary power-of-two weight vector and the count is paid in the **start's own mass ratio** —
logarithmic in the pool and linear in how far below the pool's ceiling the truth was seeded.

Two readings come out of one theorem. At the uniform start the seed's deficit vanishes and the
bound is logarithmic in the candidate count alone. At a prior-shaped start — the truth seeded `r`
doublings down, every competitor at the ceiling — it is linear in `r`, which is the currency
[Discovery] §3.3 states its own surprise budget in: the count is paid in the truth's description
length rather than in the size of the pool it is found in.

The carrier is the restriction that makes this elementary. A power-of-two weight vector stays one
under the generation, so the seeded run has a normal form through `FlooredMixture`'s existing
`expStep` and every logarithm reads as an integer exponent. General rational starts are
`BasinSettling`'s territory — settling, not counting — and nothing here is claimed of them.

## Main results

* `expRunFrom` / `expRunFrom_zero` / `expRunFrom_le` / `raw_wRunFrom_eq_pow_expRunFrom` — **the
  seeded normal form**. The exponent automaton is closed under `expStep` from *any* start inside
  the budget, and from a power-of-two start the floored run is again exactly `2 ^ expRunFrom`. The
  transition is the landed one, unchanged: the start never enters the step, so only the base case
  of `wRun_eq_pow_expRun`'s induction is new. `expRunFrom_zero` identifies the zero seed with
  `expRun`, which is what lets the uniform-start reading be stated over the landed
  `floorSurpriseSet` rather than a parallel object.
* `wrongMassFrom` / `floorSurpriseSetFrom` — **the seeded surprise objects**, mirroring `wrongMass`
  and `floorSurpriseSet` with the same strict `θ <` membership, and agreeing with them at the zero
  seed (`wrongMassFrom_zero`, `floorSurpriseSetFrom_zero`).
* `floorSurpriseFrom_card_mul_le` — **the log-mass event bound**. Under the landed budget gate
  `2(C−1) ≤ θ·2^b`, with a candidate that never misses and a seed inside the budget,
  `card · θ ≤ 5·(D + ⌊log₂ C⌋) + 4` over every horizon, where `D` is the seed's deficit: how many
  doublings the truth starts behind the seed's largest exponent. The horizon does not occur on the
  right at all. The mechanism is a potential — the total mass in units of the truth's own — which
  a surprise multiplies by at most `1 − θ/4` and no step ever raises, starting at most at `C·2^D`
  and never falling below `1`.
* `floorSurprise_card_mul_le_log` — **the uniform start**, `card · θ ≤ 5⌊log₂ C⌋ + 4`, stated over
  the landed `floorSurpriseSet` so that it reads directly against `floorSurprise_card_mul_le`'s
  `4(C−1)`.
* `floorSurpriseFrom_card_mul_le_prior` — **the prior-shaped start**, `card · θ ≤ 5(r + ⌊log₂ C⌋)
  + 4` with the truth seeded `r` doublings below a pool at the ceiling.
* `floorSurpriseFrom_unbounded_below_gate` and `floorSurpriseFrom_unbounded_below_gate_witness` —
  **the gate is load-bearing, and under realizability**. Below the gate the bound is not merely
  unproved but false: on the all-miss family every step of every horizon is a surprise, with a
  candidate that never misses present the whole time (`allMiss_realizable`). The witness pins it at
  nine candidates, budget `2^3` and threshold `1/4`, where the gate reads `16 ≤ 2`.
* `floorSurpriseFrom_deficit_card_ge` and `floorSurpriseFrom_deficit_refutes_seed_free` — **the
  seed's deficit is necessary**. Two candidates, the truth seeded `r` doublings below a competitor
  that starts at the ceiling and misses at every step: while the truth climbs, no ceiling candidate
  hits, the divisor stays at `1`, and the competitor holds a strict majority of the mass at every
  one of those `r` steps. So the count is at least `r` at a fixed candidate count and threshold,
  with the gate satisfied and `deficitMiss_realizable` supplying the never-missing candidate — no
  bound free of the start exists, and the log term is not an artefact of the potential.

## Scope

**The constants are not the sharpest the mechanism admits, and the two event bounds are
independent.** Against `floorSurprise_card_mul_le`'s `4(C−1)`, the uniform-start reading here is
sharper from `C = 5` on and weaker at `C = 2, 3, 4`; neither statement subsumes the other, and the
agnostic tracking bound `floorSurprise_card_mul_le_missCount` is untouched — its additive
accounting is what composes with a miss count, and this currency does not.

Two factors are being given away, both identified. The per-surprise factor `1 − θ/4` cannot be
improved to `1 − θ/2` under *this* gate: at a rescale step the floor may hold `C − 1` candidates at
one quantum, and the gate permits exactly `θ/2` of the total to sit there, so half the surprise's
missing mass can be floor junk that does not decay. A strictly stronger gate would recover the
factor continuously, and is not assumed. The second factor is spent converting a multiplicative
decay into a count without leaving `ℚ`: halving the potential takes `⌈4/θ⌉` surprises by the
elementary route, where the real logarithm would charge `⌈(4 ln 2)/θ⌉`. The sharpness guards below
bracket the deficit's necessary coefficient from below at `θ`, against the `5` proved.

What is not here: the seeded **agnostic** combination — this bound plus a miss-count term from an
arbitrary start — is not attempted; the exact closed form of the deficit family's count is not
computed, only the growth in `r` that refutes a seed-free bound; and general (non power-of-two)
starts are outside the carrier, since without them the normal form is unavailable and the
logarithm stops being an integer exponent.

## Attribution

The logarithmic term is the `log n` of Littlestone and Warmuth, *The weighted majority algorithm*,
Information and Computation **108** (1994), Corollary 2.1, in the mixture's wrong-mass currency.
This is an instance of that bound and an adaptation of its potential argument, not a new result:
what is proved here rather than imported is the behaviour on the quantized power-of-two carrier —
where the floor is the budget projection's own clip rather than a weight threshold applied by hand,
and where the floor's feedback has to be confined by a budget gate that has no counterpart in the
unquantized setting — together with the exact constants above and the reading of the start's mass
ratio as an integer deficit.
-/


@[expose] public section

namespace WeightedFiber

/-! ## The seeded exponent automaton -/

section SeededAutomaton

variable {C : ℕ}

/-- **The exponent automaton from a seeded start.** `expRun`'s start — every candidate at one
quantum — is baked into its definition; here the start is a parameter and the transition is the
landed `expStep`, unchanged. The automaton is closed under that step from *any* start, which is
what a power-of-two seed buys: a power-of-two weight vector stays one. -/
def expRunFrom (e₀ : Fin C → ℕ) (M : ℕ → Fin C → Bool) (b : ℕ) : ℕ → (Fin C → ℕ)
  | 0 => e₀
  | t + 1 => expStep b (M t) (expRunFrom e₀ M b t)

/-- **The zero seed recovers `expRun`.** The seeded automaton is a generalization and not a
parallel development: at the all-ones weight vector — every exponent `0` — it is the automaton
every result upstream is stated of. -/
theorem expRunFrom_zero (M : ℕ → Fin C → Bool) (b t : ℕ) :
    expRunFrom (fun _ => 0) M b t = expRun M b t := by
  induction t with
  | zero => rfl
  | succ t ih => rw [expRunFrom, ih]; rfl

/-- **The exponents never leave the budget**, from any start inside it. The invariant of
`expRun_le`, with the seed bound doing at time `0` what the all-ones start did for free. -/
theorem expRunFrom_le {e₀ : Fin C → ℕ} {b : ℕ} (he₀ : ∀ i, e₀ i ≤ b) (M : ℕ → Fin C → Bool)
    (t : ℕ) (i : Fin C) : expRunFrom e₀ M b t i ≤ b := by
  induction t generalizing i with
  | zero => exact he₀ i
  | succ t ih =>
      change expStep b (M t) (expRunFrom e₀ M b t) i ≤ b
      rw [expStep]
      have hi := ih i
      by_cases hδ : ∃ j, expRunFrom e₀ M b t j = b ∧ M t j = false
      · rw [ite_eq_left hδ]
        split <;> omega
      · rw [ite_eq_right hδ]
        by_cases hm : M t i
        · rw [ite_eq_left hm]; omega
        · rw [ite_eq_right hm]
          have : expRunFrom e₀ M b t i ≠ b := fun hb => hδ ⟨i, hb, by simpa using hm⟩
          omega

/-- **The seeded normal form.** From a power-of-two start the floored run is again *exactly* the
exponent automaton: the weight of candidate `i` at time `t` is `2 ^ expRunFrom e₀ M b t i`. The
proof is `wRun_eq_pow_expRun`'s, with the seed bound replacing the all-ones base case — the two
divisor computations in the step are untouched, because the step never sees the start. -/
theorem raw_wRunFrom_eq_pow_expRunFrom {e₀ : Fin C → ℕ} {b : ℕ} (he₀ : ∀ i, e₀ i ≤ b)
    (M : ℕ → Fin C → Bool) (t : ℕ) (i : Fin C) :
    raw (wRunFrom (2 ^ b) (missFit M) (pack (2 ^ b) fun j => 2 ^ e₀ j) t) i
      = 2 ^ expRunFrom e₀ M b t i := by
  have hW : 1 ≤ 2 ^ b := Nat.one_le_two_pow
  induction t generalizing i with
  | zero =>
      change raw (pack (2 ^ b) fun j => 2 ^ e₀ j) i = _
      rw [raw, pack]
      exact min_eq_left (Nat.pow_le_pow_right (by norm_num) (he₀ i))
  | succ t ih =>
      set w := wRunFrom (2 ^ b) (missFit M) (pack (2 ^ b) fun j => 2 ^ e₀ j) with hw
      have hstep : raw (w (t + 1))
          = project (2 ^ b) (bayesStep (missFit M t) (raw (w t))) := by
        change raw (wGen (2 ^ b) (missFit M t) (w t)) = _
        exact raw_wGen hW _ _
      set u : Fin C → ℕ := bayesStep (missFit M t) (raw (w t)) with hu
      have hui : ∀ j, u j = 2 ^ (expRunFrom e₀ M b t j + (if M t j then 0 else 1)) := by
        intro j
        rw [hu, bayesStep, ih j, missFit]
        by_cases h : M t j
        · rw [ite_eq_left h, ite_eq_left h, Nat.mul_one, Nat.add_zero]
        · rw [ite_eq_right h, ite_eq_right h, pow_succ]
      rw [hstep]
      change project (2 ^ b) u i = 2 ^ expStep b (M t) (expRunFrom e₀ M b t) i
      rw [expStep, project]
      by_cases hδ : ∃ j, expRunFrom e₀ M b t j = b ∧ M t j = false
      · -- a candidate at the ceiling hits: the post-step maximum is `2 ^ (b+1)`, the divisor is `2`
        rw [ite_eq_left hδ]
        obtain ⟨j₀, hj₀e, hj₀m⟩ := hδ
        have hmax : wMax u = 2 ^ (b + 1) := by
          refine le_antisymm (Finset.sup_le fun j _ => ?_) ?_
          · rw [hui j]
            refine Nat.pow_le_pow_right (by norm_num) ?_
            have := expRunFrom_le he₀ M t j
            split <;> omega
          · have hj : u j₀ = 2 ^ (b + 1) := by
              rw [hui j₀, hj₀e, ite_eq_right (by simp [hj₀m])]
            exact hj ▸ le_wMax u j₀
        have hd2 : scaleDiv (2 ^ b) u = 2 := by
          rw [scaleDiv, hmax, pow_succ]
          have : (2 ^ b * 2 + 2 ^ b - 1) / 2 ^ b = 2 :=
            Nat.div_eq_of_lt_le (by omega) (by omega)
          omega
        rw [hd2, hui i]
        rcases Nat.eq_zero_or_pos (expRunFrom e₀ M b t i + (if M t i then 0 else 1)) with h0 | hpos
        · rw [h0]
          norm_num
        · obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hpos.ne'
          rw [hk, pow_succ, Nat.mul_div_cancel _ (by norm_num), Nat.succ_sub_one]
          exact max_eq_right Nat.one_le_two_pow
      · -- no ceiling candidate hits: the maximum stays inside the budget and the divisor is `1`
        rw [ite_eq_right hδ]
        have hle : wMax u ≤ 2 ^ b := by
          refine Finset.sup_le fun j _ => ?_
          rw [hui j]
          refine Nat.pow_le_pow_right (by norm_num) ?_
          have h1 := expRunFrom_le he₀ M t j
          by_cases hm : M t j
          · rw [ite_eq_left hm]; omega
          · rw [ite_eq_right hm]
            have : expRunFrom e₀ M b t j ≠ b := fun hb => hδ ⟨j, hb, by simpa using hm⟩
            omega
        have hd1 : scaleDiv (2 ^ b) u = 1 := by
          have hlt : (wMax u + 2 ^ b - 1) / 2 ^ b < 2 :=
            (Nat.div_lt_iff_lt_mul (by omega)).mpr (by omega)
          rw [scaleDiv]
          omega
        rw [hd1, Nat.div_one, hui i, Nat.sub_zero]
        exact max_eq_right Nat.one_le_two_pow

end SeededAutomaton

/-! ## The seeded surprise objects -/

section SeededSurprise

variable {C : ℕ}

/-- The seeded run's wrong mass, mirroring `wrongMass` over `wRunFrom`. -/
def wrongMassFrom (e₀ : Fin C → ℕ) (M : ℕ → Fin C → Bool) (b t : ℕ) : ℚ :=
  ∑ i, if M t i then
    toDist (raw (wRunFrom (2 ^ b) (missFit M) (pack (2 ^ b) fun j => 2 ^ e₀ j) t)) i else 0

/-- The seeded surprise set, mirroring `floorSurpriseSet`: the membership condition is strict, as
in `BayesRedundancy.surpriseSet`. -/
def floorSurpriseSetFrom (e₀ : Fin C → ℕ) (M : ℕ → Fin C → Bool) (b : ℕ) (θ : ℚ) (n : ℕ) :
    Finset ℕ :=
  (Finset.range n).filter fun t => θ < wrongMassFrom e₀ M b t

/-- **At the zero seed the seeded objects are the landed ones**, so every uniform-start statement
below reads directly against `floorSurpriseSet`. -/
theorem wrongMassFrom_zero (M : ℕ → Fin C → Bool) (b t : ℕ) :
    wrongMassFrom (fun _ => 0) M b t = wrongMass M b t := by
  have h : (pack (2 ^ b) fun _ : Fin C => 2 ^ (0 : ℕ)) = pack (2 ^ b) fun _ => 1 := by
    simp
  rw [wrongMassFrom, wrongMass, h]
  exact Finset.sum_congr rfl fun i _ => by rw [wRunFrom_pack_one]

theorem floorSurpriseSetFrom_zero (M : ℕ → Fin C → Bool) (b : ℕ) (θ : ℚ) (n : ℕ) :
    floorSurpriseSetFrom (fun _ => 0) M b θ n = floorSurpriseSet M b θ n := by
  rw [floorSurpriseSetFrom, floorSurpriseSet]
  exact Finset.filter_congr fun t _ => by rw [wrongMassFrom_zero]

end SeededSurprise

/-! ## The mass potential -/

section Potential

variable {C : ℕ}

/-- The total mass carried by an exponent vector. -/
private def expTotal (e : Fin C → ℕ) : ℚ := ∑ j, (2 : ℚ) ^ e j

/-- The mass on the candidates that miss. -/
private def expMiss (e : Fin C → ℕ) (m : Fin C → Bool) : ℚ :=
  ∑ j, if m j = true then (2 : ℚ) ^ e j else 0

/-- The floor's own feedback: one half-quantum for each candidate the rescale would push below the
reserve — a missing candidate already sitting at exponent `0`. -/
private def expClip (e : Fin C → ℕ) (m : Fin C → Bool) : ℚ :=
  ∑ j, if m j = true ∧ e j = 0 then (1 : ℚ) else 0

/-- **The potential**: the total mass measured in units of candidate `i`'s own. -/
private def expPot (e : Fin C → ℕ) (i : Fin C) : ℚ := expTotal e / (2 : ℚ) ^ e i

private theorem expTotal_pos (e : Fin C → ℕ) (i : Fin C) : 0 < expTotal e :=
  Finset.sum_pos (fun j _ => by positivity) ⟨i, Finset.mem_univ i⟩

private theorem pow_le_expTotal (e : Fin C → ℕ) (i : Fin C) : (2 : ℚ) ^ e i ≤ expTotal e :=
  Finset.single_le_sum (f := fun j => (2 : ℚ) ^ e j) (fun j _ => by positivity)
    (Finset.mem_univ i)

private theorem one_le_expPot (e : Fin C → ℕ) (i : Fin C) : 1 ≤ expPot e i := by
  rw [expPot, le_div_iff₀ (by positivity), one_mul]
  exact pow_le_expTotal e i

private theorem expClip_le_expMiss (e : Fin C → ℕ) (m : Fin C → Bool) :
    expClip e m ≤ expMiss e m := by
  refine Finset.sum_le_sum fun j _ => ?_
  by_cases hm : m j = true
  · rw [ite_eq_left hm]
    by_cases h0 : e j = 0
    · rw [ite_eq_left ⟨hm, h0⟩, h0, pow_zero]
    · rw [ite_eq_right (fun hc => h0 hc.2)]
      positivity
  · rw [ite_eq_right hm, ite_eq_right (fun hc => hm hc.1)]

/-- The floor can hold at most one candidate per competitor: the reference hits, so it is never
among them. -/
private theorem expClip_le_sub_one (e : Fin C → ℕ) {m : Fin C → Bool} {iR : Fin C}
    (h : m iR = false) : expClip e m ≤ (C : ℚ) - 1 := by
  have hC1 : 1 ≤ C := iR.pos
  have h0 : (if m iR = true ∧ e iR = 0 then (1 : ℚ) else 0) = 0 := by
    rw [ite_eq_right]
    rintro ⟨h1, -⟩
    rw [h] at h1
    exact Bool.noConfusion h1
  rw [expClip, ← Finset.sum_erase_add _ _ (Finset.mem_univ iR), h0, add_zero]
  calc ∑ j ∈ Finset.univ.erase iR, (if m j = true ∧ e j = 0 then (1 : ℚ) else 0)
      ≤ ∑ _j ∈ Finset.univ.erase iR, (1 : ℚ) :=
        Finset.sum_le_sum fun j _ => by split <;> norm_num
    _ = (C : ℚ) - 1 := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_one,
          Finset.card_erase_of_mem (Finset.mem_univ iR), Finset.card_univ, Fintype.card_fin,
          Nat.cast_sub hC1, Nat.cast_one]

/-- **One step, no rescale**: every hitter doubles and every misser stands still. -/
private theorem expTotal_expStep_of_not_rescale {b : ℕ} {m : Fin C → Bool} {e : Fin C → ℕ}
    (h : ¬ ∃ j, e j = b ∧ m j = false) :
    expTotal (expStep b m e) = 2 * expTotal e - expMiss e m := by
  rw [expTotal, expTotal, expMiss, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hj : expStep b m e j = e j + (if m j = true then 0 else 1) := by
    simp only [expStep, ite_eq_right h, Nat.sub_zero]
  rw [hj]
  by_cases hm : m j = true
  · rw [ite_eq_left hm, ite_eq_left hm, Nat.add_zero]; ring
  · rw [ite_eq_right hm, ite_eq_right hm, pow_succ]; ring

/-- **One step, with the rescale**: the same, halved — except at the floor, where the reserve
holds a candidate at one quantum instead of the half it would otherwise carry. That excess is
exactly `expClip`. -/
private theorem expTotal_expStep_of_rescale {b : ℕ} {m : Fin C → Bool} {e : Fin C → ℕ}
    (h : ∃ j, e j = b ∧ m j = false) :
    2 * expTotal (expStep b m e) = 2 * expTotal e - expMiss e m + expClip e m := by
  rw [expTotal, expTotal, expMiss, expClip, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hj : expStep b m e j = (e j + (if m j = true then 0 else 1)) - 1 := by
    simp only [expStep, ite_eq_left h]
  rw [hj]
  by_cases hm : m j = true
  · rw [ite_eq_left hm, ite_eq_left hm, Nat.add_zero]
    rcases Nat.eq_zero_or_pos (e j) with h0 | hpos
    · rw [ite_eq_left ⟨hm, h0⟩, h0]
      norm_num
    · obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hpos.ne'
      rw [ite_eq_right (fun hc => by omega), hk, Nat.succ_sub_one, pow_succ]
      ring
  · rw [ite_eq_right hm, ite_eq_right hm, ite_eq_right (fun hc => hm hc.1), Nat.add_sub_cancel]
    ring

/-- **The potential's step law**, in the one form both readings need. Whatever the divisor does,
the potential after a step is bounded by the pre-step total less half the missing mass, plus
whatever the floor feeds back — and the floor feeds back nothing at all unless the rescale fires,
which is why the junk allowance `J` is only charged there. -/
private theorem expPot_expStep_le {b : ℕ} {m : Fin C → Bool} {e : Fin C → ℕ} {iR : Fin C}
    (hiR : m iR = false) (J : ℚ) (hJ0 : 0 ≤ J)
    (hJ : (∃ j, e j = b ∧ m j = false) → expClip e m ≤ J) :
    expPot (expStep b m e) iR ≤ (2 * expTotal e - expMiss e m + J) / (2 * (2 : ℚ) ^ e iR) := by
  have hpow : (0 : ℚ) < (2 : ℚ) ^ e iR := by positivity
  have hmiR : ¬ (m iR = true) := by rw [hiR]; exact Bool.noConfusion
  by_cases hδ : ∃ j, e j = b ∧ m j = false
  · have hstep : expStep b m e iR = e iR := by
      simp only [expStep, ite_eq_left hδ, ite_eq_right hmiR]
      omega
    have htot := expTotal_expStep_of_rescale hδ
    have hc := hJ hδ
    rw [expPot, hstep, div_le_div_iff₀ hpow (by positivity)]
    nlinarith [htot, hc, hpow]
  · have hstep : expStep b m e iR = e iR + 1 := by
      simp only [expStep, ite_eq_right hδ, ite_eq_right hmiR, Nat.sub_zero]
    have htot := expTotal_expStep_of_not_rescale hδ
    rw [expPot, hstep, htot, pow_succ, mul_comm ((2 : ℚ) ^ e iR) 2]
    exact div_le_div_of_nonneg_right (by linarith) (by positivity)

private theorem expMiss_nonneg (e : Fin C → ℕ) (m : Fin C → Bool) : 0 ≤ expMiss e m :=
  Finset.sum_nonneg fun j _ => by split <;> positivity

/-- The seeded run's total mass, read off the normal form. -/
private theorem sum_raw_cast {e₀ : Fin C → ℕ} {b : ℕ} (he₀ : ∀ i, e₀ i ≤ b)
    (M : ℕ → Fin C → Bool) (t : ℕ) :
    ∑ j, ((raw (wRunFrom (2 ^ b) (missFit M) (pack (2 ^ b) fun k => 2 ^ e₀ k) t) j : ℕ) : ℚ)
      = expTotal (expRunFrom e₀ M b t) := by
  rw [expTotal]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [raw_wRunFrom_eq_pow_expRunFrom he₀]
  push_cast
  ring

/-- **The wrong mass is the exponent automaton's own missing fraction.** This is the bridge the
whole argument runs on: the reading's probability of being wrong at a step is a ratio of sums of
powers of two, so the potential below can be manipulated in `ℚ` with no reference to the carrier. -/
private theorem wrongMassFrom_eq_div {e₀ : Fin C → ℕ} {b : ℕ} (he₀ : ∀ i, e₀ i ≤ b)
    (M : ℕ → Fin C → Bool) (t : ℕ) :
    wrongMassFrom e₀ M b t
      = expMiss (expRunFrom e₀ M b t) (M t) / expTotal (expRunFrom e₀ M b t) := by
  rw [wrongMassFrom, expMiss, div_eq_mul_inv, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hm : M t i = true
  · rw [ite_eq_left hm, ite_eq_left hm, ← div_eq_mul_inv]
    change ((raw (wRunFrom (2 ^ b) (missFit M) (pack (2 ^ b) fun k => 2 ^ e₀ k) t) i : ℕ) : ℚ)
        / ∑ j, ((raw (wRunFrom (2 ^ b) (missFit M) (pack (2 ^ b) fun k => 2 ^ e₀ k) t) j : ℕ) : ℚ)
      = _
    rw [sum_raw_cast he₀, raw_wRunFrom_eq_pow_expRunFrom he₀]
    push_cast
    ring
  · rw [ite_eq_right hm, ite_eq_right hm, zero_mul]

/-- **The potential never rises.** Whatever the divisor does and whoever misses, the floor feeds
back no more than the missing mass it was charged on — so the reference candidate's share of the
total is non-decreasing along the whole run. -/
private theorem expPot_run_step_le {e₀ : Fin C → ℕ} {b : ℕ} (M : ℕ → Fin C → Bool) {iR : Fin C}
    (hR : ∀ t, M t iR = false) (t : ℕ) :
    expPot (expRunFrom e₀ M b (t + 1)) iR ≤ expPot (expRunFrom e₀ M b t) iR := by
  set e := expRunFrom e₀ M b t with he
  have hpow : (0 : ℚ) < (2 : ℚ) ^ e iR := by positivity
  have hstep := expPot_expStep_le (b := b) (hR t) (expMiss e (M t)) (expMiss_nonneg e (M t))
    (fun _ => expClip_le_expMiss e (M t))
  refine le_trans hstep ?_
  rw [expPot, div_le_div_iff₀ (by positivity) hpow]
  ring_nf
  nlinarith [hpow]

/-- **A surprise costs a fixed fraction of the potential.** The missing mass exceeds `θ` of the
total; the floor's feedback is confined to half of that by the budget gate — the rescale only fires
with a candidate at the ceiling, so the total is at least `2 ^ b` there — and what is left over is
the drop. -/
private theorem expPot_run_step_le_of_surprise {e₀ : Fin C → ℕ} {b : ℕ} (he₀ : ∀ i, e₀ i ≤ b)
    (M : ℕ → Fin C → Bool) {iR : Fin C} (hR : ∀ t, M t iR = false) {θ : ℚ} (hθ0 : 0 ≤ θ)
    (hbudget : 2 * ((C : ℚ) - 1) ≤ θ * 2 ^ b) {t : ℕ} (hs : θ < wrongMassFrom e₀ M b t) :
    expPot (expRunFrom e₀ M b (t + 1)) iR ≤ (1 - θ / 4) * expPot (expRunFrom e₀ M b t) iR := by
  set e := expRunFrom e₀ M b t with he
  have hT : 0 < expTotal e := expTotal_pos e iR
  have hpow : (0 : ℚ) < (2 : ℚ) ^ e iR := by positivity
  have hmiss : θ * expTotal e < expMiss e (M t) := by
    have h := hs
    rw [wrongMassFrom_eq_div he₀, lt_div_iff₀ hT] at h
    exact h
  have hJ : (∃ j, e j = b ∧ M t j = false) → expClip e (M t) ≤ θ * expTotal e / 2 := by
    rintro ⟨j, hj, -⟩
    have h1 : expClip e (M t) ≤ (C : ℚ) - 1 := expClip_le_sub_one e (hR t)
    have h2 : (2 : ℚ) ^ b ≤ expTotal e := by
      rw [← hj]
      exact pow_le_expTotal e j
    nlinarith [hbudget, h1, h2, hθ0]
  have hstep := expPot_expStep_le (b := b) (hR t) (θ * expTotal e / 2) (by positivity) hJ
  refine le_trans hstep ?_
  rw [expPot, ← mul_div_assoc, div_le_div_iff₀ (by positivity) hpow]
  nlinarith [hmiss, hpow]

private theorem expMiss_le_expTotal (e : Fin C → ℕ) (m : Fin C → Bool) :
    expMiss e m ≤ expTotal e := by
  refine Finset.sum_le_sum fun j _ => ?_
  split
  · exact le_rfl
  · positivity

private theorem wrongMassFrom_le_one {e₀ : Fin C → ℕ} {b : ℕ} (he₀ : ∀ i, e₀ i ≤ b)
    (M : ℕ → Fin C → Bool) (i : Fin C) (t : ℕ) : wrongMassFrom e₀ M b t ≤ 1 := by
  rw [wrongMassFrom_eq_div he₀, div_le_one (expTotal_pos _ i)]
  exact expMiss_le_expTotal _ _

/-- The start's own potential, bounded by the seed's spread: everyone is at most the seed's
largest exponent, so the total is at most `C` copies of it. -/
private theorem expPot_seed_le (e₀ : Fin C → ℕ) (iR : Fin C) :
    expPot e₀ iR ≤ (C : ℚ) * 2 ^ (Finset.univ.sup e₀ - e₀ iR) := by
  have hiR : e₀ iR ≤ Finset.univ.sup e₀ := Finset.le_sup (Finset.mem_univ iR)
  have hsplit : (2 : ℚ) ^ Finset.univ.sup e₀
      = (2 : ℚ) ^ (Finset.univ.sup e₀ - e₀ iR) * (2 : ℚ) ^ e₀ iR := by
    rw [← pow_add]
    congr 1
    omega
  rw [expPot, div_le_iff₀ (by positivity)]
  calc expTotal e₀ ≤ ∑ _j : Fin C, (2 : ℚ) ^ Finset.univ.sup e₀ :=
        Finset.sum_le_sum fun j _ =>
          pow_le_pow_right₀ (by norm_num) (Finset.le_sup (Finset.mem_univ j))
    _ = (C : ℚ) * 2 ^ Finset.univ.sup e₀ := by
        rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_fin]
    _ = (C : ℚ) * 2 ^ (Finset.univ.sup e₀ - e₀ iR) * 2 ^ e₀ iR := by rw [hsplit]; ring

end Potential

/-! ## The log-mass event bound -/

section EventBound

variable {C : ℕ}

private theorem floorSurpriseSetFrom_card_succ (e₀ : Fin C → ℕ) (M : ℕ → Fin C → Bool)
    (b : ℕ) (θ : ℚ) (n : ℕ) :
    (floorSurpriseSetFrom e₀ M b θ (n + 1)).card
      = (floorSurpriseSetFrom e₀ M b θ n).card
        + (if θ < wrongMassFrom e₀ M b n then 1 else 0) := by
  rw [floorSurpriseSetFrom, floorSurpriseSetFrom, Finset.range_add_one, Finset.filter_insert]
  by_cases h : θ < wrongMassFrom e₀ M b n
  · rw [ite_eq_left h, Finset.card_insert_of_notMem (by simp), ite_eq_left h]
  · rw [ite_eq_right h, ite_eq_right h, Nat.add_zero]

/-- **Every surprise is paid out of the potential.** The count of surprises before the horizon
appears as an exponent: each one multiplies the reference candidate's share by at most
`1 − θ/4`, and no step ever raises it. -/
private theorem expPot_run_le_pow {e₀ : Fin C → ℕ} {b : ℕ} (he₀ : ∀ i, e₀ i ≤ b)
    (M : ℕ → Fin C → Bool) {iR : Fin C} (hR : ∀ t, M t iR = false) {θ : ℚ} (hθ0 : 0 ≤ θ)
    (hθ1 : θ ≤ 1) (hbudget : 2 * ((C : ℚ) - 1) ≤ θ * 2 ^ b) (n : ℕ) :
    expPot (expRunFrom e₀ M b n) iR
      ≤ (1 - θ / 4) ^ (floorSurpriseSetFrom e₀ M b θ n).card * expPot e₀ iR := by
  have hc : (0 : ℚ) ≤ 1 - θ / 4 := by linarith
  induction n with
  | zero => simp [floorSurpriseSetFrom, expRunFrom]
  | succ n ih =>
      rw [floorSurpriseSetFrom_card_succ]
      by_cases h : θ < wrongMassFrom e₀ M b n
      · rw [ite_eq_left h, pow_succ]
        calc expPot (expRunFrom e₀ M b (n + 1)) iR
            ≤ (1 - θ / 4) * expPot (expRunFrom e₀ M b n) iR :=
              expPot_run_step_le_of_surprise he₀ M hR hθ0 hbudget h
          _ ≤ (1 - θ / 4)
              * ((1 - θ / 4) ^ (floorSurpriseSetFrom e₀ M b θ n).card * expPot e₀ iR) :=
              mul_le_mul_of_nonneg_left ih hc
          _ = _ := by ring
      · rw [ite_eq_right h, Nat.add_zero]
        exact le_trans (expPot_run_step_le M hR n) ih

/-- **The log-mass event bound over seeded starts** ([Discovery] §3.3, Proposition 3.4).

Call a step a surprise when the mass the floored mixture puts on the candidates that miss there
exceeds a threshold `θ`. From a power-of-two seeded start, under the budget gate
`2(C−1) ≤ θ·2^b` and with a candidate `iR` that never misses, the surprise count over any horizon
satisfies `card · θ ≤ 5·(D + ⌊log₂ C⌋) + 4`, where `D` is the seed's deficit — how many doublings
the truth starts behind the seed's largest exponent. The horizon does not occur on the right at
all: this is a lifetime-free event budget, in the currency of the start's own mass ratio.

The mechanism is a potential: the total mass measured in units of the truth's own. A surprise
multiplies it by at most `1 − θ/4` — the missing mass exceeds `θ` of the total, and the mass the
floor feeds back is confined to half of that by the gate, since the rescale only fires with a
candidate at the ceiling — and no step ever raises it. The potential starts at most at `C·2^D` and
never falls below `1`, so the count is logarithmic in the start's spread rather than linear in the
candidate count.

This is the mixture-currency instance of the `log n` term of Littlestone and Warmuth, *The weighted
majority algorithm*, Information and Computation **108** (1994), Corollary 2.1. What is proved here
rather than imported is the exact constant on the quantized power-of-two carrier — where the floor
is the budget projection's own clip rather than a weight threshold applied by hand — and the
reading of the start's mass ratio as an integer deficit, which is what a power-of-two seed buys.

The constant is not the sharpest the mechanism admits. The factor `1 − θ/4` cannot be improved to
`1 − θ/2` under *this* gate at a rescale step: the floor may hold `C − 1` candidates at one quantum
and the gate allows exactly `θ/2` of the total to sit there. A further factor is spent converting
the multiplicative decay to a count without leaving `ℚ` — halving the potential takes `⌈4/θ⌉`
surprises by the elementary route. Against the landed `floorSurprise_card_mul_le`, whose right side
is `4(C−1)`, this bound is therefore sharper from `C = 5` on and weaker at `C = 2, 3, 4`; the
two are independent statements and neither subsumes the other. -/
theorem floorSurpriseFrom_card_mul_le {e₀ : Fin C → ℕ} {b : ℕ} (he₀ : ∀ i, e₀ i ≤ b)
    (M : ℕ → Fin C → Bool) {iR : Fin C} (hR : ∀ t, M t iR = false) (θ : ℚ)
    (hbudget : 2 * ((C : ℚ) - 1) ≤ θ * 2 ^ b) (n : ℕ) :
    ((floorSurpriseSetFrom e₀ M b θ n).card : ℚ) * θ
      ≤ 5 * ((Finset.univ.sup e₀ - e₀ iR + Nat.log 2 C : ℕ) : ℚ) + 4 := by
  set K : ℕ := Finset.univ.sup e₀ - e₀ iR + Nat.log 2 C with hK
  have hKQ : (0 : ℚ) ≤ (K : ℚ) := by positivity
  by_cases hθ0 : 0 < θ
  case neg =>
    have hle : θ ≤ 0 := not_lt.mp hθ0
    have : ((floorSurpriseSetFrom e₀ M b θ n).card : ℚ) * θ ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) hle
    linarith
  by_cases hθ1 : θ < 1
  case neg =>
    have hone : (1 : ℚ) ≤ θ := not_lt.mp hθ1
    have hempty : floorSurpriseSetFrom e₀ M b θ n = ∅ := by
      rw [floorSurpriseSetFrom, Finset.filter_eq_empty_iff]
      intro t _
      exact not_lt.mpr (le_trans (wrongMassFrom_le_one he₀ M iR t) hone)
    rw [hempty, Finset.card_empty, Nat.cast_zero, zero_mul]
    linarith
  -- the working range: `0 < θ < 1`
  set N : ℕ := (floorSurpriseSetFrom e₀ M b θ n).card with hN
  have hΦ0 : (0 : ℚ) ≤ expPot e₀ iR := le_trans zero_le_one (one_le_expPot e₀ iR)
  have hdecay := expPot_run_le_pow he₀ M hR hθ0.le hθ1.le hbudget n
  have hone : (1 : ℚ) ≤ (1 - θ / 4) ^ N * expPot e₀ iR :=
    le_trans (one_le_expPot (expRunFrom e₀ M b n) iR) hdecay
  -- the multiplicative budget, read in the other direction
  have hprod : (1 + θ / 4) ^ N ≤ expPot e₀ iR := by
    have hmul : (1 + θ / 4) ^ N * ((1 - θ / 4) ^ N * expPot e₀ iR)
        = (1 - θ ^ 2 / 16) ^ N * expPot e₀ iR := by
      rw [← mul_assoc, ← mul_pow]
      ring_nf
    have h1 : (1 + θ / 4) ^ N * 1 ≤ (1 + θ / 4) ^ N * ((1 - θ / 4) ^ N * expPot e₀ iR) :=
      mul_le_mul_of_nonneg_left hone (by positivity)
    rw [hmul] at h1
    have h2 : (1 - θ ^ 2 / 16) ^ N ≤ 1 := pow_le_one₀ (by nlinarith) (by nlinarith)
    nlinarith [h1, hΦ0]
  -- the block: `⌈4/θ⌉` surprises halve the potential
  set m : ℕ := ⌈(4 : ℚ) / θ⌉₊ with hm
  have hm4 : (4 : ℚ) / θ ≤ (m : ℚ) := Nat.le_ceil _
  have hmθ : (4 : ℚ) ≤ (m : ℚ) * θ := by
    rw [div_le_iff₀ hθ0] at hm4
    linarith
  have hmlt : (m : ℚ) < 4 / θ + 1 := Nat.ceil_lt_add_one (by positivity)
  have hmθlt : (m : ℚ) * θ < 4 + θ := by
    have := mul_lt_mul_of_pos_right hmlt hθ0
    rw [add_mul, div_mul_cancel₀ _ hθ0.ne', one_mul] at this
    exact this
  have hm0 : 0 < m := by
    by_contra hc
    rw [Nat.eq_zero_of_not_pos hc] at hmθ
    norm_num at hmθ
  have hbase : (1 : ℚ) ≤ 1 + θ / 4 := by linarith
  have h2m : (2 : ℚ) ≤ (1 + θ / 4) ^ m := by
    have hb := one_add_mul_le_pow (a := θ / 4) (by linarith) m
    have : (1 : ℚ) ≤ (m : ℚ) * (θ / 4) := by linarith
    linarith
  have hq : (2 : ℚ) ^ (N / m) ≤ (1 + θ / 4) ^ N := by
    calc (2 : ℚ) ^ (N / m) ≤ ((1 + θ / 4) ^ m) ^ (N / m) :=
          pow_le_pow_left₀ (by norm_num) h2m _
      _ = (1 + θ / 4) ^ (m * (N / m)) := by rw [← pow_mul]
      _ ≤ (1 + θ / 4) ^ N := by
          refine pow_le_pow_right₀ hbase ?_
          rw [Nat.mul_comm]
          exact Nat.div_mul_le_self N m
  -- the potential's own ceiling turns the block count into the seed's deficit
  have hceil : (2 : ℚ) ^ (N / m) ≤ (C : ℚ) * 2 ^ (Finset.univ.sup e₀ - e₀ iR) :=
    le_trans hq (le_trans hprod (expPot_seed_le e₀ iR))
  have hblocks : N / m ≤ K := by
    by_contra hcon
    have hle : K + 1 ≤ N / m := not_le.mp hcon
    have hCq : (C : ℚ) < 2 ^ (Nat.log 2 C + 1) := by
      have := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) C
      exact_mod_cast this
    have hgrow : (2 : ℚ) ^ (K + 1) ≤ (2 : ℚ) ^ (N / m) :=
      pow_le_pow_right₀ (by norm_num) hle
    have hsplit : (2 : ℚ) ^ (K + 1)
        = 2 ^ (Finset.univ.sup e₀ - e₀ iR) * 2 ^ (Nat.log 2 C + 1) := by
      have hsum : K + 1 = (Finset.univ.sup e₀ - e₀ iR) + (Nat.log 2 C + 1) := by omega
      rw [hsum, pow_add]
    rw [hsplit] at hgrow
    have hpos : (0 : ℚ) < 2 ^ (Finset.univ.sup e₀ - e₀ iR) := by positivity
    nlinarith [hceil, hgrow, hCq, hpos]
  -- and the count follows, one block at a time
  have hNlt : N < (K + 1) * m := (Nat.div_lt_iff_lt_mul hm0).mp (by omega)
  have hNQ : (N : ℚ) + 1 ≤ ((K : ℚ) + 1) * (m : ℚ) := by
    have : (N : ℚ) + 1 ≤ (((K + 1) * m : ℕ) : ℚ) := by exact_mod_cast hNlt
    push_cast at this
    linarith
  have hstep : (N : ℚ) * θ ≤ (((K : ℚ) + 1) * (m : ℚ) - 1) * θ := by
    refine mul_le_mul_of_nonneg_right (by linarith) hθ0.le
  nlinarith [hstep, hmθlt, hKQ, hθ1, hθ0]

/-- **The uniform start**: the fiber's own all-ones prior, where the seed's deficit vanishes and
the bound is logarithmic in the candidate count alone. Stated over the landed `floorSurpriseSet`,
so it reads directly against `floorSurprise_card_mul_le`'s `4(C−1)` — sharper from `C = 5` on,
weaker at `C = 2, 3, 4`, and neither statement subsumes the other. -/
theorem floorSurprise_card_mul_le_log (M : ℕ → Fin C → Bool) {iR : Fin C}
    (hR : ∀ t, M t iR = false) (b : ℕ) (θ : ℚ) (hbudget : 2 * ((C : ℚ) - 1) ≤ θ * 2 ^ b)
    (n : ℕ) :
    ((floorSurpriseSet M b θ n).card : ℚ) * θ ≤ 5 * (Nat.log 2 C : ℚ) + 4 := by
  have hsup : Finset.univ.sup (fun _ : Fin C => 0) = 0 :=
    le_antisymm (Finset.sup_le fun _ _ => le_rfl) (Nat.zero_le _)
  have h := floorSurpriseFrom_card_mul_le (e₀ := fun _ => 0) (b := b)
    (fun _ => Nat.zero_le b) M hR θ hbudget n
  rw [floorSurpriseSetFrom_zero, hsup] at h
  simpa using h

/-- **The prior-shaped start** ([Discovery] §3.3's own currency). The truth is seeded `r` doublings
below the ceiling every other candidate starts at — the quantized reading of a prior `2 ^ (−r)` on
a description of length `r`, against a pool at the top — and the surprise budget is then linear in
that description length and logarithmic in the pool. This is the shape the constant decision was
for: the count is paid in the truth's own description length, not in the size of the pool it is
found in. -/
theorem floorSurpriseFrom_card_mul_le_prior (M : ℕ → Fin C → Bool) {iR : Fin C}
    (hR : ∀ t, M t iR = false) {b r : ℕ} (hr : r ≤ b) (hC : 2 ≤ C) (θ : ℚ)
    (hbudget : 2 * ((C : ℚ) - 1) ≤ θ * 2 ^ b) (n : ℕ) :
    ((floorSurpriseSetFrom (fun i => if i = iR then b - r else b) M b θ n).card : ℚ) * θ
      ≤ 5 * ((r + Nat.log 2 C : ℕ) : ℚ) + 4 := by
  set e₀ : Fin C → ℕ := fun i => if i = iR then b - r else b with he₀def
  have he₀ : ∀ i, e₀ i ≤ b := by
    intro i
    rw [he₀def]
    dsimp only
    split <;> omega
  obtain ⟨j, hj⟩ : ∃ j : Fin C, j ≠ iR :=
    Fintype.exists_ne_of_one_lt_card (by simp only [Fintype.card_fin]; omega) iR
  have hjval : e₀ j = b := by rw [he₀def]; dsimp only; rw [ite_eq_right hj]
  have hsup : Finset.univ.sup e₀ = b :=
    le_antisymm (Finset.sup_le fun i _ => he₀ i)
      (hjval ▸ Finset.le_sup (Finset.mem_univ j))
  have hiR : e₀ iR = b - r := by rw [he₀def]; dsimp only; rw [ite_eq_left rfl]
  have h := floorSurpriseFrom_card_mul_le he₀ M hR θ hbudget n
  rw [hsup, hiR, show b - (b - r) = r by omega] at h
  exact h

end EventBound

/-! ## The guards -/

section Guards

/-! ### The budget gate is load-bearing, with a never-missing candidate present

The bound above buys its logarithm with the gate, and below the gate it is *false* rather than
unproved — even under realizability, which is what separates this guard from the landed
realizability families. The all-miss family already refutes it: the floor alone keeps the reading
wrong at every step, so the count grows with the horizon while the right side does not. -/

/-- The all-miss family's own never-missing candidate: the guard below drops the gate and keeps
every other hypothesis of the bound, realizability included. -/
theorem allMiss_realizable {C : ℕ} (iR : Fin C) (t : ℕ) : allMiss iR t iR = false := by
  simp [allMiss]

/-- **Below the gate there is no bound at all**, seeded or not. Read at the uniform start, where
the seed's deficit vanishes and the log-mass bound reads `5⌊log₂ C⌋ + 4`, the count is the whole
horizon. -/
theorem floorSurpriseFrom_unbounded_below_gate {C : ℕ} {iR : Fin C} (b : ℕ) (θ : ℚ)
    (hθ : θ * ((2 : ℚ) ^ b + ((C : ℚ) - 1)) < (C : ℚ) - 1) (n : ℕ) :
    (floorSurpriseSetFrom (fun _ => 0) (allMiss iR) b θ n).card = n := by
  rw [floorSurpriseSetFrom_zero]
  exact floorSurprises_unbounded_below_budget b θ hθ n

/-- **The refutation at named parameters.** Nine candidates, budget `2 ^ 3`, threshold `1/4`: the
gate reads `16 ≤ 2` and fails, a candidate never misses, and every step of every horizon is a
surprise — so the count is unbounded where the bound would have it at `5⌊log₂ 9⌋ + 4`. -/
theorem floorSurpriseFrom_unbounded_below_gate_witness (n : ℕ) :
    ¬ (2 * ((9 : ℚ) - 1) ≤ (1 / 4 : ℚ) * 2 ^ 3) ∧
      (floorSurpriseSetFrom (fun _ => 0) (allMiss (0 : Fin 9)) 3 (1 / 4) n).card = n :=
  ⟨by norm_num, floorSurpriseFrom_unbounded_below_gate 3 (1 / 4) (by norm_num) n⟩

/-! ### The seed's deficit is necessary: the count grows with it

The log term is not an artefact of the potential. Two candidates, the truth seeded `r` doublings
below a competitor that starts at the ceiling and misses at every step: while the truth climbs, no
candidate at the ceiling hits, the divisor stays at `1`, and the competitor holds a strict majority
of the mass at every one of those `r` steps. So the count is at least `r`, at a fixed candidate
count and a fixed threshold — and no bound free of the start can exist. -/

/-- Two candidates: the truth never misses, the competitor always does. -/
def deficitMiss : ℕ → Fin 2 → Bool := fun _ i => decide ((i : ℕ) = 1)

/-- The family's own never-missing witness. -/
theorem deficitMiss_realizable (t : ℕ) : deficitMiss t 0 = false := by simp [deficitMiss]

/-- The seeded start: the truth `r` doublings below the ceiling the competitor starts at. -/
def deficitSeed (b r : ℕ) : Fin 2 → ℕ := ![b - r, b]

private theorem deficitSeed_le (b r : ℕ) (i : Fin 2) : deficitSeed b r i ≤ b := by
  fin_cases i <;> simp [deficitSeed]

/-- **The climbing phase in closed form.** The competitor sits at the ceiling but misses, so it
never triggers the rescale; the truth hits at every step and climbs one doubling at a time. -/
private theorem expRunFrom_deficit {b r : ℕ} (hr : r ≤ b) :
    ∀ t, t ≤ r → expRunFrom (deficitSeed b r) deficitMiss b t = ![b - r + t, b] := by
  intro t
  induction t with
  | zero =>
      intro _
      funext i
      fin_cases i <;> simp [expRunFrom, deficitSeed]
  | succ t ih =>
      intro ht
      have ihe := ih (by omega)
      change expStep b (deficitMiss t) (expRunFrom (deficitSeed b r) deficitMiss b t) = _
      rw [ihe]
      have hδ : ¬ ∃ j, (![b - r + t, b] : Fin 2 → ℕ) j = b ∧ deficitMiss t j = false := by
        rintro ⟨j, hj1, hj2⟩
        fin_cases j
        · simp at hj1
          omega
        · simp [deficitMiss] at hj2
      funext i
      rw [expStep, ite_eq_right hδ]
      fin_cases i <;> simp [deficitMiss]
      all_goals omega

/-- The wrong mass through the climbing phase: the competitor's ceiling against the truth's own
partial climb. -/
private theorem wrongMassFrom_deficit {b r : ℕ} (hr : r ≤ b) {t : ℕ} (ht : t ≤ r) :
    wrongMassFrom (deficitSeed b r) deficitMiss b t
      = (2 : ℚ) ^ b / ((2 : ℚ) ^ (b - r + t) + (2 : ℚ) ^ b) := by
  rw [wrongMassFrom_eq_div (deficitSeed_le b r), expRunFrom_deficit hr t ht, expMiss, expTotal,
    Fin.sum_univ_two, Fin.sum_univ_two]
  simp [deficitMiss]

/-- Every step of the climbing phase is a surprise, at any threshold the gate can hold. -/
private theorem deficit_surprise {b r : ℕ} (hr : r ≤ b) {θ : ℚ} (hθ : θ ≤ 1 / 2) {t : ℕ}
    (ht : t < r) : θ < wrongMassFrom (deficitSeed b r) deficitMiss b t := by
  rw [wrongMassFrom_deficit hr (by omega)]
  have h1 : (2 : ℚ) ^ (b - r + t) < (2 : ℚ) ^ b :=
    pow_lt_pow_right₀ (by norm_num) (by omega)
  have h2 : (0 : ℚ) < (2 : ℚ) ^ (b - r + t) := by positivity
  rw [lt_div_iff₀ (by positivity)]
  nlinarith

/-- **The count is at least the seed's deficit.** -/
theorem floorSurpriseFrom_deficit_card_ge {b r : ℕ} (hr : r ≤ b) {θ : ℚ} (hθ : θ ≤ 1 / 2)
    {n : ℕ} (hn : r ≤ n) :
    r ≤ (floorSurpriseSetFrom (deficitSeed b r) deficitMiss b θ n).card := by
  have hsub : Finset.range r ⊆ floorSurpriseSetFrom (deficitSeed b r) deficitMiss b θ n := by
    intro t htmem
    have ht : t < r := Finset.mem_range.mp htmem
    rw [floorSurpriseSetFrom, Finset.mem_filter]
    exact ⟨Finset.mem_range.mpr (by omega), deficit_surprise hr hθ ht⟩
  calc r = (Finset.range r).card := (Finset.card_range r).symm
    _ ≤ _ := Finset.card_le_card hsub

/-- **No bound free of the start exists**, so the seed's deficit in `floorSurpriseFrom_card_mul_le`
is necessary and not an artefact of the potential. At two candidates and a fixed threshold, with
the budget gate satisfied and a candidate that never misses, any proposed constant is already
exceeded once the seed's deficit exceeds it — and the deficit is free, bounded only by the budget
exponent. Read against the bound's own right side, this brackets the deficit's coefficient from
below at `θ`, where the bound proves `5`. -/
theorem floorSurpriseFrom_deficit_refutes_seed_free {b r : ℕ} (hr : r ≤ b) {θ : ℚ}
    (hθ0 : 0 < θ) (hθ : θ ≤ 1 / 2) (hgate : 2 * (((2 : ℕ) : ℚ) - 1) ≤ θ * 2 ^ b) {K : ℚ}
    (hK : K < (r : ℚ) * θ) {n : ℕ} (hn : r ≤ n) :
    (2 * (((2 : ℕ) : ℚ) - 1) ≤ θ * 2 ^ b) ∧ (∀ t, deficitMiss t 0 = false) ∧
      K < ((floorSurpriseSetFrom (deficitSeed b r) deficitMiss b θ n).card : ℚ) * θ := by
  refine ⟨hgate, deficitMiss_realizable, ?_⟩
  have hcard : (r : ℚ)
      ≤ ((floorSurpriseSetFrom (deficitSeed b r) deficitMiss b θ n).card : ℚ) := by
    exact_mod_cast floorSurpriseFrom_deficit_card_ge hr hθ hn
  nlinarith [hcard, hθ0, hK]

end Guards

end WeightedFiber

/-- info: 'WeightedFiber.raw_wRunFrom_eq_pow_expRunFrom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms WeightedFiber.raw_wRunFrom_eq_pow_expRunFrom

/-- info: 'WeightedFiber.floorSurpriseFrom_card_mul_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms WeightedFiber.floorSurpriseFrom_card_mul_le

/-- info: 'WeightedFiber.floorSurprise_card_mul_le_log' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms WeightedFiber.floorSurprise_card_mul_le_log

/-- info: 'WeightedFiber.floorSurpriseFrom_card_mul_le_prior' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms WeightedFiber.floorSurpriseFrom_card_mul_le_prior

/-- info: 'WeightedFiber.floorSurpriseFrom_unbounded_below_gate_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms WeightedFiber.floorSurpriseFrom_unbounded_below_gate_witness

/-- info: 'WeightedFiber.floorSurpriseFrom_deficit_refutes_seed_free' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms WeightedFiber.floorSurpriseFrom_deficit_refutes_seed_free
