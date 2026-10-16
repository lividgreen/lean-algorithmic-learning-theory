module

public import Mathlib.Algebra.Order.Ring.Pow
public import ALT.BasinSettling


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
* `floorSurpriseFrom_card_add_le_capacity` — **the floored mixture's exact capacity threshold**,
  a genuinely different (additive) reading from the log-mass bound above:
  `card + C·e₀ iR ≤ C·b + ∑ (erase iR) e₀`, the seed's own capacity, under the floor condition
  `C − 1 ≤ θ·(2^b + C − 1)` — weaker than the budget gate — and a realizable candidate.
  `floorSurprise_card_le_capacity` is its uniform-start corollary (`card ≤ C·b`), and
  `floorSurprise_bounded_iff` closes the window: at the uniform start a lifetime-free bound over
  every stream with a never-missing candidate exists exactly when the floor condition holds —
  when it fails, `floorSurprises_unbounded_below_budget`'s own family already refutes one.
  `floorSurpriseFrom_allMiss_mem` / `floorSurpriseFrom_allMiss_card_ge` price the all-miss family's
  own surprise steps from *any* seeded start, and `floorSurpriseFrom_deficit_card_ge` below is one
  instance of them rather than a parallel development.
* `floorSurpriseFrom_unbounded_below_gate` and `floorSurpriseFrom_unbounded_below_gate_witness` —
  **the gate is load-bearing, and under realizability**. The count is unbounded at its own
  condition `θ·(2^b + C − 1) < C − 1` — strictly stronger than the landed gate's failure — where
  the all-miss family makes every step of every horizon a surprise, with a candidate that never
  misses present the whole time (`allMiss_realizable`). The witness pins it at nine candidates,
  budget `2^3` and threshold `1/4`, where the gate reads `16 ≤ 2`. Read against
  `floorSurpriseFrom_card_add_le_capacity` below, whose own condition is exactly this one negated,
  the gate is a sufficient condition for the landed constants and not the boundary.
* `floorSurpriseFrom_allMiss_card_eq`, `floorSurpriseFrom_allMiss_card_eq_nonvacuous` and
  `floorSurpriseFrom_bounded_iff` — **the window closes from every start**. Below the floor
  condition the all-miss family makes every step a surprise from *every* power-of-two start inside
  the register, not only the zero seed: the truth's exponent never exceeds `b` and each competitor
  holds at least one quantum, so the wrong mass is at least `(C − 1)/(2^b + C − 1)` at every step.
  With the capacity bound this is the seeded form of the threshold — from every such start a
  horizon-free bound over every stream with a never-missing candidate exists exactly when the
  floor condition holds — of which `floorSurprise_bounded_iff` is the zero seed's case. The
  witness pins the leaf at two candidates, budget `2`, the start `(1, 2)` and threshold `1/8`.
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

namespace ALT

open WVec

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
in `BayesRedundancy.errorTimes`. -/
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

/-! ## The floored mixture's exact capacity threshold -/

section CapacityBound

variable {C : ℕ}

/-- **The capacity potential**: `C` copies of the reference's own remaining headroom to the
ceiling, plus the competitors' exponents outright. Additive by design, so it composes with the
surprise count with no subtraction. -/
private def capPot (b : ℕ) (iR : Fin C) (e : Fin C → ℕ) : ℕ :=
  C * (b - e iR) + ∑ i ∈ Finset.univ.erase iR, e i

/-- **Off a rescale the potential drops by exactly one.** The reference candidate hits and is not
at the ceiling, so its headroom falls by one doubling — costing `capPot` a full `C` — while the
`C − 1` competitors rise by at most one doubling each. -/
private theorem capPot_expStep_add_one_le_of_not_rescale {b : ℕ} {m : Fin C → Bool} {e : Fin C → ℕ}
    {iR : Fin C} (he : ∀ i, e i ≤ b) (hiR : m iR = false)
    (hδ : ¬ ∃ j, e j = b ∧ m j = false) :
    capPot b iR (expStep b m e) + 1 ≤ capPot b iR e := by
  have heiRb : e iR < b := by
    rcases lt_or_eq_of_le (he iR) with h | h
    · exact h
    · exact absurd ⟨iR, h, hiR⟩ hδ
  have heiR' : expStep b m e iR = e iR + 1 := by
    simp only [expStep, ite_eq_right hδ, ite_eq_right (by simp [hiR] : ¬ (m iR = true)),
      Nat.sub_zero]
  have hrest : ∀ j ∈ Finset.univ.erase iR, expStep b m e j ≤ e j + 1 := by
    intro j _
    simp only [expStep, ite_eq_right hδ, Nat.sub_zero]
    split <;> omega
  have hcard : (Finset.univ.erase iR).card = C - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ iR), Finset.card_univ, Fintype.card_fin]
  have hsum : ∑ j ∈ Finset.univ.erase iR, expStep b m e j
      ≤ ∑ j ∈ Finset.univ.erase iR, e j + (C - 1) := by
    calc ∑ j ∈ Finset.univ.erase iR, expStep b m e j
        ≤ ∑ j ∈ Finset.univ.erase iR, (e j + 1) := Finset.sum_le_sum hrest
      _ = ∑ j ∈ Finset.univ.erase iR, e j + (Finset.univ.erase iR).card := by
          rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one]
      _ = ∑ j ∈ Finset.univ.erase iR, e j + (C - 1) := by rw [hcard]
  have hbC : C * (b - (e iR + 1)) + C = C * (b - e iR) := by
    have hd : b - e iR = (b - (e iR + 1)) + 1 := by omega
    rw [hd]; ring
  have hCpos : 0 < C := iR.pos
  rw [capPot, capPot, heiR']
  clear heiR' hrest hcard he hδ heiRb
  revert hbC hsum hCpos
  generalize C * (b - (e iR + 1)) = A1
  generalize C * (b - e iR) = A2
  generalize ∑ i ∈ Finset.univ.erase iR, expStep b m e i = S1
  generalize ∑ i ∈ Finset.univ.erase iR, e i = S2
  intro hbC hsum hCpos
  omega

/-- **At a rescale the potential never rises.** The reference is frozen at the ceiling and no
competitor's exponent can increase. -/
private theorem capPot_expStep_le_of_rescale {b : ℕ} {m : Fin C → Bool} {e : Fin C → ℕ}
    {iR : Fin C} (hiR : m iR = false) (hδ : ∃ j, e j = b ∧ m j = false) :
    capPot b iR (expStep b m e) ≤ capPot b iR e := by
  have heiR' : expStep b m e iR = e iR := by
    simp only [expStep, ite_eq_left hδ, ite_eq_right (by simp [hiR] : ¬ (m iR = true))]
    omega
  have hrest : ∀ j ∈ Finset.univ.erase iR, expStep b m e j ≤ e j := by
    intro j _
    simp only [expStep, ite_eq_left hδ]
    split <;> omega
  rw [capPot, capPot, heiR']
  exact Nat.add_le_add_left (Finset.sum_le_sum hrest) _

/-- **The potential never rises**, combining the two branches of `expStep`. -/
private theorem capPot_expStep_le {b : ℕ} {m : Fin C → Bool} {e : Fin C → ℕ} {iR : Fin C}
    (he : ∀ i, e i ≤ b) (hiR : m iR = false) :
    capPot b iR (expStep b m e) ≤ capPot b iR e := by
  by_cases hδ : ∃ j, e j = b ∧ m j = false
  · exact capPot_expStep_le_of_rescale hiR hδ
  · have h := capPot_expStep_add_one_le_of_not_rescale he hiR hδ
    omega

/-- **A surprise costs the potential at least one.** At a rescale, the budget floor `hfloor` forces
some missing candidate off the floor — otherwise the missing mass could not exceed `θ` of a total
that already carries a ceiling term — and that candidate alone drops the competitors' sum by one;
off a rescale the potential falls by one regardless (`capPot_expStep_le`'s own case). -/
private theorem capPot_expStep_add_one_le_of_surprise {b : ℕ} {m : Fin C → Bool} {e : Fin C → ℕ}
    {iR : Fin C} (he : ∀ i, e i ≤ b) (hiR : m iR = false) {θ : ℚ}
    (hfloor : (C : ℚ) - 1 ≤ θ * ((2 : ℚ) ^ b + ((C : ℚ) - 1)))
    (hs : θ < expMiss e m / expTotal e) :
    capPot b iR (expStep b m e) + 1 ≤ capPot b iR e := by
  by_cases hδ : ∃ j, e j = b ∧ m j = false
  · obtain ⟨j₀, hj₀e, hj₀m⟩ := hδ
    have hδ' : ∃ j, e j = b ∧ m j = false := ⟨j₀, hj₀e, hj₀m⟩
    have heiR' : expStep b m e iR = e iR := by
      simp only [expStep, ite_eq_left hδ', ite_eq_right (by simp [hiR] : ¬ (m iR = true))]
      omega
    have hT : (0 : ℚ) < expTotal e := expTotal_pos e iR
    have hcardj0 : ((Finset.univ.erase j₀).card : ℚ) = (C : ℚ) - 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ j₀), Finset.card_univ, Fintype.card_fin,
        Nat.cast_sub j₀.pos, Nat.cast_one]
    have hTge : (2 : ℚ) ^ b + ((C : ℚ) - 1) ≤ expTotal e := by
      have hone : ∀ j ∈ Finset.univ.erase j₀, (1 : ℚ) ≤ (2 : ℚ) ^ e j := fun j _ =>
        one_le_pow₀ (by norm_num)
      calc (2 : ℚ) ^ b + ((C : ℚ) - 1)
          = (2 : ℚ) ^ e j₀ + ∑ _j ∈ Finset.univ.erase j₀, (1 : ℚ) := by
            rw [hj₀e, Finset.sum_const, nsmul_eq_mul, mul_one, hcardj0]
        _ ≤ (2 : ℚ) ^ e j₀ + ∑ j ∈ Finset.univ.erase j₀, (2 : ℚ) ^ e j := by
            gcongr with j hj
            exact hone j hj
        _ = expTotal e := by
            rw [expTotal, ← Finset.sum_erase_add _ _ (Finset.mem_univ j₀)]; ring
    have hCQ : (0 : ℚ) ≤ (C : ℚ) - 1 := by
      have : (1 : ℚ) ≤ (C : ℚ) := by exact_mod_cast iR.pos
      linarith
    have hpos2 : (0 : ℚ) < (2 : ℚ) ^ b + ((C : ℚ) - 1) := by
      have h2 : (0 : ℚ) < (2 : ℚ) ^ b := by positivity
      linarith
    have hθ0 : 0 ≤ θ := by
      by_contra hneg
      push Not at hneg
      have : θ * ((2 : ℚ) ^ b + ((C : ℚ) - 1)) < 0 := mul_neg_of_neg_of_pos hneg hpos2
      linarith [hfloor, hCQ]
    have hnotall0 : ∃ j, m j = true ∧ 0 < e j := by
      by_contra hcon
      push Not at hcon
      have hcardIR : ((Finset.univ.erase iR).card : ℚ) = (C : ℚ) - 1 := by
        rw [Finset.card_erase_of_mem (Finset.mem_univ iR), Finset.card_univ, Fintype.card_fin,
          Nat.cast_sub iR.pos, Nat.cast_one]
      have hM0 : expMiss e m ≤ (C : ℚ) - 1 := by
        rw [expMiss]
        calc ∑ j, (if m j = true then (2 : ℚ) ^ e j else 0)
            ≤ ∑ j ∈ Finset.univ.erase iR, (if m j = true then (2 : ℚ) ^ e j else 0) := by
              rw [← Finset.sum_erase_add _ _ (Finset.mem_univ iR),
                ite_eq_right (by simp [hiR] : ¬ (m iR = true))]
              linarith [Finset.sum_nonneg (fun j (_ : j ∈ Finset.univ.erase iR) =>
                show (0:ℚ) ≤ if m j = true then (2:ℚ)^e j else 0 by split <;> positivity)]
          _ ≤ ∑ _j ∈ Finset.univ.erase iR, (1 : ℚ) := by
              refine Finset.sum_le_sum fun j _ => ?_
              by_cases hm : m j = true
              · rw [ite_eq_left hm, Nat.le_zero.mp (hcon j hm), pow_zero]
              · rw [ite_eq_right hm]; norm_num
          _ = (C : ℚ) - 1 := by rw [Finset.sum_const, nsmul_eq_mul, mul_one, hcardIR]
      have : expMiss e m / expTotal e ≤ θ := by
        rw [div_le_iff₀ hT]
        calc expMiss e m ≤ (C : ℚ) - 1 := hM0
          _ ≤ θ * ((2 : ℚ) ^ b + ((C : ℚ) - 1)) := hfloor
          _ ≤ θ * expTotal e := mul_le_mul_of_nonneg_left hTge hθ0
      linarith [hs]
    obtain ⟨j₁, hj₁m, hj₁pos⟩ := hnotall0
    have hj₁ne : j₁ ≠ iR := by
      rintro rfl
      rw [hiR] at hj₁m
      exact Bool.noConfusion hj₁m
    have hj₁mem : j₁ ∈ Finset.univ.erase iR := Finset.mem_erase.mpr ⟨hj₁ne, Finset.mem_univ j₁⟩
    have hj₁step : expStep b m e j₁ < e j₁ := by
      simp only [expStep, ite_eq_left hδ', ite_eq_left hj₁m]
      omega
    have hrest : ∀ j ∈ Finset.univ.erase iR, expStep b m e j ≤ e j := by
      intro j _
      simp only [expStep, ite_eq_left hδ']
      split <;> omega
    have hlt : ∑ j ∈ Finset.univ.erase iR, expStep b m e j
        < ∑ j ∈ Finset.univ.erase iR, e j :=
      Finset.sum_lt_sum hrest ⟨j₁, hj₁mem, hj₁step⟩
    rw [capPot, capPot, heiR']
    clear hrest hj₁step hj₁mem hj₁ne hj₁m hj₁pos hTge hcardj0 hT heiR' hδ' hj₀e hj₀m
      hfloor hs he
    revert hlt
    generalize ∑ i ∈ Finset.univ.erase iR, expStep b m e i = S1
    generalize ∑ i ∈ Finset.univ.erase iR, e i = S2
    omega
  · exact capPot_expStep_add_one_le_of_not_rescale he hiR hδ

/-- **The count accumulates against the seed's own potential.** Every surprise costs `capPot` at
least one and it never rises otherwise, so after any horizon the count plus what remains of the
potential is still bounded by where it started. -/
private theorem capPot_run_le {e₀ : Fin C → ℕ} {b : ℕ} (he₀ : ∀ i, e₀ i ≤ b)
    (M : ℕ → Fin C → Bool) {iR : Fin C} (hR : ∀ t, M t iR = false) {θ : ℚ}
    (hfloor : (C : ℚ) - 1 ≤ θ * ((2 : ℚ) ^ b + ((C : ℚ) - 1))) (n : ℕ) :
    (floorSurpriseSetFrom e₀ M b θ n).card + capPot b iR (expRunFrom e₀ M b n)
      ≤ capPot b iR e₀ := by
  induction n with
  | zero => simp [floorSurpriseSetFrom, expRunFrom]
  | succ n ih =>
      rw [floorSurpriseSetFrom_card_succ]
      have hen : ∀ i, expRunFrom e₀ M b n i ≤ b := fun i => expRunFrom_le he₀ M n i
      have heq : expRunFrom e₀ M b (n + 1) = expStep b (M n) (expRunFrom e₀ M b n) := rfl
      rw [heq]
      by_cases h : θ < wrongMassFrom e₀ M b n
      · rw [ite_eq_left h]
        have hs : θ < expMiss (expRunFrom e₀ M b n) (M n) / expTotal (expRunFrom e₀ M b n) := by
          rwa [wrongMassFrom_eq_div he₀] at h
        have hstep := capPot_expStep_add_one_le_of_surprise hen (hR n) hfloor hs
        omega
      · rw [ite_eq_right h, Nat.add_zero]
        have hstep := capPot_expStep_le hen (hR n)
        omega

/-- **The floored mixture's exact capacity threshold** ([Discovery] Proposition 3.5(i), row FV-37;
[Inevitability] §6, [Inevitability] §7).

Under the floor condition `C − 1 ≤ θ·(2^b + C − 1)`, which is weaker than
`floorSurpriseFrom_card_mul_le`'s budget gate, and with a candidate `iR` that never
misses, the surprise count over any horizon is bounded by the seed's own capacity: `C` copies of
how far below the ceiling the truth started, plus the competitors' starting exponents outright.
The mechanism is the additive potential `capPot` — `C` times the reference's remaining headroom to
the ceiling, plus the competitors' exponents — which a surprise costs at least one and which never
rises otherwise: the reference is frozen at a rescale and no competitor's exponent can increase
there, while off a rescale the reference's headroom drops by one doubling (costing `C`) against the
competitors rising by at most `C − 1` doublings between them, and at a rescale that is a surprise
the floor condition forces some missing candidate off the floor, costing the competitors' sum at
least one on its own.

This is a genuinely different reading from `floorSurpriseFrom_card_mul_le`'s multiplicative one: it
is exact where that one is not (`floorSurpriseFrom_card_add_le_capacity_nonvacuous` exhibits an
instance below that bound's own gate where this one still has content), and it is the threshold the
window of [Inevitability] §7 stands on — the repair total is bounded at every realizable task once
the floor condition holds, by the seed's own capacity, and unbounded at a task when it fails
(`floorSurprise_bounded_iff`, at the uniform start). -/
theorem floorSurpriseFrom_card_add_le_capacity {e₀ : Fin C → ℕ} {b : ℕ} (he₀ : ∀ i, e₀ i ≤ b)
    (M : ℕ → Fin C → Bool) {iR : Fin C} (hR : ∀ t, M t iR = false) (θ : ℚ)
    (hfloor : (C : ℚ) - 1 ≤ θ * ((2 : ℚ) ^ b + ((C : ℚ) - 1))) (n : ℕ) :
    (floorSurpriseSetFrom e₀ M b θ n).card + C * e₀ iR
      ≤ C * b + ∑ i ∈ Finset.univ.erase iR, e₀ i := by
  have h := capPot_run_le he₀ M hR hfloor n
  have hiRb := he₀ iR
  have hCeq : C * (b - e₀ iR) + C * e₀ iR = C * b := by
    rw [← Nat.mul_add]
    congr 1
    omega
  rw [capPot, capPot] at h
  omega

/-- **The uniform start** ([Discovery] Proposition 3.5(i), row FV-37). At the fiber's own all-ones
prior the seed's headroom is `C` copies of the whole budget and the competitors start at nothing,
so the capacity bound reads `card ≤ C·b`. -/
theorem floorSurprise_card_le_capacity (M : ℕ → Fin C → Bool) {iR : Fin C}
    (hR : ∀ t, M t iR = false) (b : ℕ) (θ : ℚ)
    (hfloor : (C : ℚ) - 1 ≤ θ * ((2 : ℚ) ^ b + ((C : ℚ) - 1))) (n : ℕ) :
    (floorSurpriseSet M b θ n).card ≤ C * b := by
  have h := floorSurpriseFrom_card_add_le_capacity (e₀ := fun _ => 0) (fun _ => Nat.zero_le b)
    M hR θ hfloor n
  rw [floorSurpriseSetFrom_zero] at h
  simpa using h

/-- **The window closes** ([Discovery] Proposition 3.5(ii), row FV-37). At the uniform start, a
lifetime-free bound on the surprise count over every stream with a never-missing candidate exists
exactly when the floor condition
`C − 1 ≤ θ·(2^b + C − 1)` holds: sufficiency is `floorSurprise_card_le_capacity`'s bound at
`N = C·b`, and necessity is the all-miss family's own unbounded growth
(`floorSurprises_unbounded_below_budget`), realizable by `allMiss_realizable`. Between the two
[Inevitability] §7's window vanishes: when the condition fails there is no bound at all, and when
it holds the capacity bound already supplies one. -/
theorem floorSurprise_bounded_iff {iR : Fin C} (b : ℕ) (θ : ℚ) :
    (∃ N, ∀ M : ℕ → Fin C → Bool, (∀ t, M t iR = false) →
        ∀ n, (floorSurpriseSet M b θ n).card ≤ N)
      ↔ (C : ℚ) - 1 ≤ θ * ((2 : ℚ) ^ b + ((C : ℚ) - 1)) := by
  constructor
  · rintro ⟨N, hN⟩
    by_contra hcon
    have hunb := floorSurprises_unbounded_below_budget (iR := iR) b θ (not_le.mp hcon) (N + 1)
    have hbound := hN (allMiss iR) (fun t => by simp [allMiss]) (N + 1)
    omega
  · intro hfloor
    exact ⟨C * b, fun M hR n => floorSurprise_card_le_capacity M hR b θ hfloor n⟩

end CapacityBound

/-! ## The guards -/

section Guards

/-! ### The budget gate is load-bearing, with a never-missing candidate present

The bound above buys its logarithm with the gate, and at its OWN condition —
`θ·(2^b + C − 1) < C − 1`, strictly stronger than the gate's failure — it is *false* rather than
unproved, even under realizability, which is what separates this guard from the landed
realizability families. The all-miss family already refutes it: the floor alone keeps the reading
wrong at every step, so the count grows with the horizon while the right side does not.
`floorSurpriseFrom_card_add_le_capacity` reads the SAME condition negated as its own hypothesis, so
the gate above is a sufficient condition for both landed bounds' constants and not the boundary of
either. -/

/-- The all-miss family's own never-missing candidate: the guard below drops the gate and keeps
every other hypothesis of the bound, realizability included. -/
theorem allMiss_realizable {C : ℕ} (iR : Fin C) (t : ℕ) : allMiss iR t iR = false := by
  simp [allMiss]

/-- **Below its own condition there is no bound at all**, seeded or not — a condition strictly
stronger than the gate's mere failure (`floorSurpriseFrom_card_add_le_capacity`'s own hypothesis is
this one negated). Read at the uniform start, where the seed's deficit vanishes and the log-mass
bound reads `5⌊log₂ C⌋ + 4`, the count is the whole horizon. -/
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

/-! ### The window closes from every start

The gate guard above refutes a lifetime-free bound at the zero seed. Below the floor condition the
all-miss family refutes one from *every* power-of-two start inside the register — the truth's
exponent never exceeds `b` and each competitor holds at least one quantum, so the wrong mass sits
above `θ` at every step no matter where the run began — and with the capacity bound this closes
the seeded window: from every such start a horizon-free bound exists exactly when the floor
condition holds. -/

/-- **Below the floor condition every step of the all-miss stream is a surprise, from every
power-of-two start inside the register.** The truth's exponent never exceeds `b` and every
competitor's is at least `0`, so the wrong mass at every step is at least
`(C − 1)/(2^b + C − 1)`, which the condition's failure puts above `θ`. The landed
`floorSurpriseFrom_unbounded_below_gate` is this at the zero seed. -/
theorem floorSurpriseFrom_allMiss_card_eq {C : ℕ} {e₀ : Fin C → ℕ} {b : ℕ} (he₀ : ∀ i, e₀ i ≤ b)
    {iR : Fin C} (θ : ℚ) (hθ : θ * ((2 : ℚ) ^ b + ((C : ℚ) - 1)) < (C : ℚ) - 1) (n : ℕ) :
    (floorSurpriseSetFrom e₀ (allMiss iR) b θ n).card = n := by
  have hC1 : 1 ≤ C := iR.pos
  have hCq : (0 : ℚ) ≤ (C : ℚ) - 1 := by
    have : (1 : ℚ) ≤ (C : ℚ) := by exact_mod_cast hC1
    linarith
  have hsurp : ∀ t, θ < wrongMassFrom e₀ (allMiss iR) b t := by
    intro t
    set e_t := expRunFrom e₀ (allMiss iR) b t with he_t_def
    set St := ∑ i ∈ Finset.univ.erase iR, (2 : ℚ) ^ e_t i with hSt_def
    have hMissEq : expMiss e_t (allMiss iR t) = St := by
      rw [expMiss, ← Finset.sum_erase_add _ _ (Finset.mem_univ iR),
        show (if allMiss iR t iR = true then ((2 : ℚ)) ^ e_t iR else 0) = 0 by simp [allMiss],
        add_zero, hSt_def]
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [ite_eq_left (show allMiss iR t j = true by simp [allMiss, (Finset.mem_erase.mp hj).1])]
    have hTotEq : expTotal e_t = (2 : ℚ) ^ e_t iR + St := by
      rw [expTotal, ← Finset.sum_erase_add _ _ (Finset.mem_univ iR), hSt_def, add_comm]
    have hP : (2 : ℚ) ^ e_t iR ≤ (2 : ℚ) ^ b :=
      pow_le_pow_right₀ (by norm_num) (expRunFrom_le he₀ (allMiss iR) t iR)
    have hPpos : (0 : ℚ) < (2 : ℚ) ^ e_t iR := by positivity
    have hcard : ((Finset.univ.erase iR).card : ℚ) = (C : ℚ) - 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ iR), Finset.card_univ, Fintype.card_fin,
        Nat.cast_sub hC1, Nat.cast_one]
    have hSt : (C : ℚ) - 1 ≤ St := by
      rw [← hcard, Finset.card_eq_sum_ones, Nat.cast_sum, hSt_def]
      push_cast
      exact Finset.sum_le_sum fun i _ => one_le_pow₀ (by norm_num)
    have hθ1 : θ ≤ 1 := by
      by_contra h
      push Not at h
      have h2b : (0 : ℚ) < (2 : ℚ) ^ b + ((C : ℚ) - 1) := by positivity
      nlinarith
    rw [wrongMassFrom_eq_div he₀, hMissEq, hTotEq, lt_div_iff₀ (by linarith)]
    rcases lt_or_ge θ 0 with hneg | hθ0
    · nlinarith
    · nlinarith [mul_le_mul_of_nonneg_left hP hθ0,
        mul_le_mul_of_nonneg_right hSt (sub_nonneg.mpr hθ1)]
  rw [floorSurpriseSetFrom, Finset.filter_true_of_mem fun t _ => hsurp t, Finset.card_range]

/-- The hypotheses of `floorSurpriseFrom_allMiss_card_eq` hold at once at named parameters: two
candidates, budget `2`, the start `(1, 2)` with the truth first, threshold `1/8`; every step is a
surprise there. -/
theorem floorSurpriseFrom_allMiss_card_eq_nonvacuous (n : ℕ) :
    (∀ i, (![1, 2] : Fin 2 → ℕ) i ≤ 2) ∧
      (1 / 8 : ℚ) * ((2 : ℚ) ^ 2 + ((2 : ℚ) - 1)) < (2 : ℚ) - 1 ∧
      (floorSurpriseSetFrom ![1, 2] (allMiss (0 : Fin 2)) 2 (1 / 8) n).card = n :=
  ⟨by decide, by norm_num, floorSurpriseFrom_allMiss_card_eq (by decide) (1 / 8) (by norm_num) n⟩

/-- **The window closes from every start** ([Discovery] Proposition 3.5(ii), past the uniform
start). From every power-of-two start inside the register, a horizon-free bound on the surprise
count over every stream with a never-missing candidate exists exactly when the floor condition
holds: sufficiency is `floorSurpriseFrom_card_add_le_capacity` at `N = C·b + Σ_{i ≠ iR} e₀ i`,
necessity is `floorSurpriseFrom_allMiss_card_eq` at horizon `N + 1`;
`floorSurprise_bounded_iff` is the zero seed's case. -/
theorem floorSurpriseFrom_bounded_iff {C : ℕ} {e₀ : Fin C → ℕ} {b : ℕ} (he₀ : ∀ i, e₀ i ≤ b)
    {iR : Fin C} (θ : ℚ) :
    (∃ N, ∀ M : ℕ → Fin C → Bool, (∀ t, M t iR = false) →
        ∀ n, (floorSurpriseSetFrom e₀ M b θ n).card ≤ N)
      ↔ (C : ℚ) - 1 ≤ θ * ((2 : ℚ) ^ b + ((C : ℚ) - 1)) := by
  constructor
  · rintro ⟨N, hN⟩
    by_contra hcon
    have hunb := floorSurpriseFrom_allMiss_card_eq he₀ (iR := iR) θ (not_le.mp hcon) (N + 1)
    have hbound := hN (allMiss iR) (allMiss_realizable iR) (N + 1)
    omega
  · intro hfloor
    refine ⟨C * b + ∑ i ∈ Finset.univ.erase iR, e₀ i, fun M hR n => ?_⟩
    have h := floorSurpriseFrom_card_add_le_capacity he₀ M hR θ hfloor n
    omega

/-! ### The all-miss family's surprise steps, from any start

The guard above shows the all-miss family refutes a lifetime-free bound at its own condition, at
the zero seed. This prices its surprise steps precisely from *any* seeded start, in the currency the
capacity bound above uses — and it is what lets the deficit family below be read as one instance
of this family rather than a parallel development. -/

/-- **The headroom invariant.** Along the all-miss family the truth's exponent plus every
competitor's own exponent can only trade in the truth's favour: at any step, a competitor's seed
exponent is bounded by its own current exponent plus how far the truth has pulled ahead of its
seed. Off a rescale the truth gains one and no competitor moves; at a rescale the truth is frozen
and a competitor's exponent falls by at most one — either way the inequality is preserved. -/
private theorem allMiss_headroom_invariant {C : ℕ} {e₀ : Fin C → ℕ} {b : ℕ} {iR : Fin C} (t : ℕ)
    (j : Fin C) (hj : j ≠ iR) :
    e₀ j + expRunFrom e₀ (allMiss iR) b t iR
      ≤ e₀ iR + t + expRunFrom e₀ (allMiss iR) b t j := by
  induction t with
  | zero => simp only [expRunFrom]; omega
  | succ t ih =>
      have heq : expRunFrom e₀ (allMiss iR) b (t + 1)
          = expStep b (allMiss iR t) (expRunFrom e₀ (allMiss iR) b t) := rfl
      rw [heq]
      set e := expRunFrom e₀ (allMiss iR) b t with he_def
      have hcompM : allMiss iR t j = true := by simp [allMiss, hj]
      have hIRnotM : ¬ (allMiss iR t iR = true) := by simp [allMiss]
      by_cases hδ : ∃ k, e k = b ∧ allMiss iR t k = false
      · have heiR' : expStep b (allMiss iR t) e iR = e iR := by
          simp only [expStep, ite_eq_left hδ, ite_eq_right hIRnotM]
          omega
        have hej' : expStep b (allMiss iR t) e j = e j - 1 := by
          simp only [expStep, ite_eq_left hδ, ite_eq_left hcompM, Nat.add_zero]
        rw [heiR', hej']
        omega
      · have heiR' : expStep b (allMiss iR t) e iR = e iR + 1 := by
          simp only [expStep, ite_eq_right hδ, ite_eq_right hIRnotM, Nat.sub_zero]
        have hej' : expStep b (allMiss iR t) e j = e j := by
          simp only [expStep, ite_eq_right hδ, ite_eq_left hcompM, Nat.add_zero, Nat.sub_zero]
        rw [heiR', hej']
        omega

/-- **A surprise step of the all-miss family, from any start** ([Discovery] Proposition 3.5(iii),
row FV-37). Once the seed's own headroom is spent — the competitors' initial mass exceeds `2`
raised to the sum of the truth's own seed exponent and the elapsed time — the step is a surprise,
at any threshold up to `1/2`. The mechanism
is `allMiss_headroom_invariant` read as a mass inequality: the competitors' current mass, scaled by
the truth's own current share, dominates the seed's competitor mass scaled by the truth's *seed*
share, so the competitors cannot have decayed faster than the hypothesis rules out. -/
theorem floorSurpriseFrom_allMiss_mem {C : ℕ} {e₀ : Fin C → ℕ} {b : ℕ} (he₀ : ∀ i, e₀ i ≤ b)
    {iR : Fin C} {θ : ℚ} (hθ : θ ≤ 1 / 2) {t n : ℕ} (ht : t < n)
    (hlt : 2 ^ (e₀ iR + t) < ∑ i ∈ Finset.univ.erase iR, 2 ^ e₀ i) :
    t ∈ floorSurpriseSetFrom e₀ (allMiss iR) b θ n := by
  set e_t := expRunFrom e₀ (allMiss iR) b t with he_t_def
  set S0 := ∑ i ∈ Finset.univ.erase iR, 2 ^ e₀ i with hS0_def
  set St := ∑ i ∈ Finset.univ.erase iR, 2 ^ e_t i with hSt_def
  have hkey : 2 ^ e_t iR * S0 ≤ 2 ^ (e₀ iR + t) * St := by
    rw [hS0_def, hSt_def, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_le_sum fun j hj => ?_
    have hjne : j ≠ iR := (Finset.mem_erase.mp hj).1
    have hinv := allMiss_headroom_invariant (e₀ := e₀) (b := b) (iR := iR) t j hjne
    calc 2 ^ e_t iR * 2 ^ e₀ j = 2 ^ (e₀ j + e_t iR) := by rw [← pow_add]; ring_nf
      _ ≤ 2 ^ (e₀ iR + t + e_t j) := Nat.pow_le_pow_right (by norm_num) hinv
      _ = 2 ^ (e₀ iR + t) * 2 ^ e_t j := by rw [pow_add]
  have hStgt : 2 ^ e_t iR < St := by
    by_contra hcon
    push Not at hcon
    have h2 : 2 ^ (e₀ iR + t) * St ≤ 2 ^ (e₀ iR + t) * 2 ^ e_t iR := Nat.mul_le_mul_left _ hcon
    have h3 : 2 ^ e_t iR * S0 ≤ 2 ^ e_t iR * 2 ^ (e₀ iR + t) := by
      rw [mul_comm (2 ^ e_t iR) (2 ^ (e₀ iR + t))]
      exact le_trans hkey h2
    have h4 : S0 ≤ 2 ^ (e₀ iR + t) :=
      Nat.le_of_mul_le_mul_left h3 (pow_pos (by norm_num) _)
    omega
  have hStgt' : (2 : ℚ) ^ e_t iR < (St : ℚ) := by exact_mod_cast hStgt
  have hStpos : (0 : ℚ) ≤ (2 : ℚ) ^ e_t iR := by positivity
  have hMissEq : expMiss e_t (allMiss iR t) = (St : ℚ) := by
    rw [expMiss, ← Finset.sum_erase_add _ _ (Finset.mem_univ iR),
      show (if allMiss iR t iR = true then ((2 : ℚ)) ^ e_t iR else 0) = 0 by simp [allMiss],
      add_zero, hSt_def]
    push_cast
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [ite_eq_left (show allMiss iR t j = true by simp [allMiss, (Finset.mem_erase.mp hj).1])]
  have hTotEq : expTotal e_t = (2 : ℚ) ^ e_t iR + (St : ℚ) := by
    rw [expTotal, ← Finset.sum_erase_add _ _ (Finset.mem_univ iR), hSt_def]
    push_cast
    ring
  rw [floorSurpriseSetFrom, Finset.mem_filter]
  refine ⟨Finset.mem_range.mpr ht, ?_⟩
  rw [wrongMassFrom_eq_div he₀, hMissEq, hTotEq, lt_div_iff₀ (by linarith)]
  nlinarith [mul_le_mul_of_nonneg_right hθ (by linarith : (0 : ℚ) ≤ (2 : ℚ) ^ e_t iR + St)]

/-- **The count is at least `k` once the seed's headroom is spent by `k`** ([Discovery] Proposition
3.5(iii), row FV-37). The mem lemma applies at every step below `k`, since the power on the left
only shrinks as `t` does. -/
theorem floorSurpriseFrom_allMiss_card_ge {C : ℕ} {e₀ : Fin C → ℕ} {b : ℕ} (he₀ : ∀ i, e₀ i ≤ b)
    {iR : Fin C} {θ : ℚ} (hθ : θ ≤ 1 / 2) {k n : ℕ} (hk : k ≤ n)
    (hle : 2 ^ (e₀ iR + k) ≤ ∑ i ∈ Finset.univ.erase iR, 2 ^ e₀ i) :
    k ≤ (floorSurpriseSetFrom e₀ (allMiss iR) b θ n).card := by
  have hsub : Finset.range k ⊆ floorSurpriseSetFrom e₀ (allMiss iR) b θ n := by
    intro t htmem
    have ht : t < k := Finset.mem_range.mp htmem
    have hlt : 2 ^ (e₀ iR + t) < ∑ i ∈ Finset.univ.erase iR, 2 ^ e₀ i :=
      lt_of_lt_of_le (Nat.pow_lt_pow_right (by norm_num) (by omega)) hle
    exact floorSurpriseFrom_allMiss_mem he₀ hθ (by omega) hlt
  calc k = (Finset.range k).card := (Finset.card_range k).symm
    _ ≤ _ := Finset.card_le_card hsub

/-- **Non-vacuity.** Three candidates, the zero seed, threshold `1/2`: the seed's headroom is spent
immediately (`1 < 2`), so stage `0` is already a surprise. -/
theorem floorSurpriseFrom_allMiss_mem_nonvacuous :
    (0 : ℕ) ∈ floorSurpriseSetFrom (fun _ : Fin 3 => 0) (allMiss (0 : Fin 3)) 0 (1 / 2 : ℚ) 1 :=
  floorSurpriseFrom_allMiss_mem (fun _ => le_refl 0) (le_refl _) (by norm_num) (by decide)

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

/-- **The count is at least the seed's deficit** ([Discovery] Proposition 3.5(iii), row FV-37) —
one instance of `floorSurpriseFrom_allMiss_card_ge` at two candidates: `deficitMiss` is `allMiss 0`
and `deficitSeed b r`'s competitor sum is exactly `2 ^ b`, so the seed's headroom is spent by
exactly `r`. -/
theorem floorSurpriseFrom_deficit_card_ge {b r : ℕ} (hr : r ≤ b) {θ : ℚ} (hθ : θ ≤ 1 / 2)
    {n : ℕ} (hn : r ≤ n) :
    r ≤ (floorSurpriseSetFrom (deficitSeed b r) deficitMiss b θ n).card := by
  have hMiss : deficitMiss = allMiss (0 : Fin 2) := by
    funext t i
    fin_cases i <;> simp [deficitMiss, allMiss]
  have herase : (Finset.univ.erase (0 : Fin 2)) = {1} := by decide
  have hle : 2 ^ (deficitSeed b r 0 + r)
      ≤ ∑ i ∈ Finset.univ.erase (0 : Fin 2), 2 ^ deficitSeed b r i := by
    rw [herase, Finset.sum_singleton, show deficitSeed b r 0 = b - r by simp [deficitSeed],
      show deficitSeed b r 1 = b by simp [deficitSeed], show b - r + r = b from by omega]
  rw [hMiss]
  exact floorSurpriseFrom_allMiss_card_ge (deficitSeed_le b r) hθ hn hle

/-- **Non-vacuity, against the landed gate** — for `floorSurpriseFrom_card_add_le_capacity`. Two
candidates, budget `2 ^ 2`, threshold `1/4`, the truth seeded two doublings below a competitor at
the ceiling: `hfloor` holds while the landed multiplicative bound's own gate `2(C−1) ≤ θ·2^b` fails
(`4 ≤ 1` is false), and the count is nonetheless positive — `floorSurpriseFrom_deficit_card_ge`
already forces it to at least `2`, comfortably inside this piece's own bound of `2·2 + 2 = 6` — so
the capacity bound has content exactly where the landed one has none. -/
theorem floorSurpriseFrom_card_add_le_capacity_nonvacuous :
    (∀ i, deficitSeed 2 2 i ≤ 2) ∧ (∀ t, deficitMiss t (0 : Fin 2) = false) ∧
      ((2 : ℚ) - 1 ≤ (1 / 4 : ℚ) * ((2 : ℚ) ^ 2 + ((2 : ℚ) - 1))) ∧
      ¬ (2 * ((2 : ℚ) - 1) ≤ (1 / 4 : ℚ) * 2 ^ 2) ∧
      0 < (floorSurpriseSetFrom (deficitSeed 2 2) deficitMiss 2 (1 / 4) 2).card :=
  ⟨deficitSeed_le 2 2, deficitMiss_realizable, by norm_num, by norm_num,
    lt_of_lt_of_le (by norm_num)
      (floorSurpriseFrom_deficit_card_ge (b := 2) (r := 2) (θ := 1 / 4) (n := 2)
        (by norm_num) (by norm_num) (le_refl 2))⟩

/-- **No bound free of the start exists** ([Discovery] Proposition 3.5(iii), row FV-37), so the
seed's deficit in `floorSurpriseFrom_card_mul_le` is necessary and not an artefact of the
potential. At two candidates and a fixed threshold, with
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

end ALT

set_option linter.style.longLine false in
/-- info: 'ALT.raw_wRunFrom_eq_pow_expRunFrom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.raw_wRunFrom_eq_pow_expRunFrom

set_option linter.style.longLine false in
/-- info: 'ALT.floorSurpriseFrom_card_mul_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.floorSurpriseFrom_card_mul_le

set_option linter.style.longLine false in
/-- info: 'ALT.floorSurprise_card_mul_le_log' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.floorSurprise_card_mul_le_log

set_option linter.style.longLine false in
/-- info: 'ALT.floorSurpriseFrom_card_mul_le_prior' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.floorSurpriseFrom_card_mul_le_prior

set_option linter.style.longLine false in
/-- info: 'ALT.floorSurpriseFrom_unbounded_below_gate_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.floorSurpriseFrom_unbounded_below_gate_witness

set_option linter.style.longLine false in
/-- info: 'ALT.floorSurpriseFrom_deficit_refutes_seed_free' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.floorSurpriseFrom_deficit_refutes_seed_free

set_option linter.style.longLine false in
/-- info: 'ALT.floorSurpriseFrom_card_add_le_capacity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.floorSurpriseFrom_card_add_le_capacity

set_option linter.style.longLine false in
/-- info: 'ALT.floorSurprise_card_le_capacity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.floorSurprise_card_le_capacity

set_option linter.style.longLine false in
/-- info: 'ALT.floorSurprise_bounded_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.floorSurprise_bounded_iff

set_option linter.style.longLine false in
/-- info: 'ALT.floorSurpriseFrom_allMiss_mem_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.floorSurpriseFrom_allMiss_mem_nonvacuous

set_option linter.style.longLine false in
/-- info: 'ALT.floorSurpriseFrom_card_add_le_capacity_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.floorSurpriseFrom_card_add_le_capacity_nonvacuous

set_option linter.style.longLine false in
/-- info: 'ALT.floorSurpriseFrom_allMiss_card_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.floorSurpriseFrom_allMiss_card_eq

set_option linter.style.longLine false in
/-- info: 'ALT.floorSurpriseFrom_allMiss_card_eq_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.floorSurpriseFrom_allMiss_card_eq_nonvacuous

set_option linter.style.longLine false in
/-- info: 'ALT.floorSurpriseFrom_bounded_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.floorSurpriseFrom_bounded_iff
