/-
Copyright (c) 2026 Mykola Palamarchuk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mykola Palamarchuk
-/
import ALT.QuantizationRate

-- Formal-check file, not Mathlib-destined: opt out of the house-style header linter.
set_option linter.style.header false

/-!
# The floored mixture: normal form, event bound, no accumulation, convergence ([Inevitability] §6)

`QuantizationRate` prices *one* projected generation against the exact Bayes step it approximates,
and leaves two questions open: what the surprise budget of [Discovery] §3.3 becomes for a process
that reserves a quantum per candidate, and what the residual does over a whole run. The
fixed-mixture redundancy argument does not transfer verbatim to either — the floor leaks mass off
the truth at every step, and the rescale projection can drop an update entirely. Both questions are
answered here, in one named regime, off a single exact description of the dynamics.

A third question is answered off that same description, and it is about the fiber's **reading**
rather than its distribution: whether selection under predictive fitness reaches a settled state at
all. Under realizability it does — and by the fitness alone, the weighted fiber carrying no
variation rule to impose one.

## The regime

Budget `W = 2 ^ b`; the `2`-vs-`1` fitness shape of `predFitPos`, driven by an abstract miss
indicator `M : ℕ → Fin C → Bool`; and `wRun`'s own all-ones start. The **normal form** assumes
nothing beyond that, and neither does the **event bound** in the tracking form that counts the
surprises against an arbitrary reference candidate's own errors. Two results add **realizability** —
a candidate `iR` that never misses — and there the hypothesis is load-bearing rather than
convenient: the *lifetime-free* event count and the no-accumulation bound are both *refuted* without
it, by families satisfying every other condition. The base dynamics, the decoder and the candidates'
predictions are all abstracted into `M`, so the results hold of any instantiation.

## Main results

* `wRun_eq_pow_expRun` — **the general normal form**, the hub everything else reads off, and it
  carries no hypothesis at all. The floored run is *exactly* an exponent automaton: the weight of
  candidate `i` at time `t` is `2 ^ expRun M b t i`, where a hit adds one exponent and the common
  rescale subtracts one from *every* exponent exactly when some candidate already at the ceiling
  hits. This is an identity, not an estimate: every weight is a power of two throughout, and the
  projection's floor at one quantum is the ℕ-subtraction's clip at exponent `0`. `expRun_le` makes
  the ceiling an invariant, and `expMax_mono`/`expMax_absorbing` make the running leader a proved
  object rather than an assumption — non-decreasing, and absorbing once it reaches the ceiling.
* `wRun_eq_pow_deficit` — **the saturation normal form**: the hub read at a frozen leader. A
  candidate that never misses holds the ceiling from time `b` on, so from then on every step
  triggers the rescale and the automaton collapses (`expRun_eq_deficit`) to a clipped deficit,
  `2 ^ (min t b - missCount M i t)` with ℕ-subtraction carrying the clip. A hit then pays nothing, a
  miss costs one exponent, and the rounding residual — the whole subject of `QuantizationRate`'s
  per-step rate — vanishes identically. `raw_wRun_eq_bayesRun_missFit` recovers the known
  below-horizon regime from it, and `raw_wRun_allMiss_eq_badW` identifies
  `weighted_fiber_not_exactly_bayes`'s annihilated update as the clip in action — a saturated
  competitor's miss absorbed at the floor.
* `floorSurprise_card_mul_le_missCount` — **the event bound**, and it asks for no realizable
  candidate. Call a step a surprise when the mass on the candidates that miss there exceeds a
  threshold `θ`. Once the budget clears that threshold (`2(C−1) ≤ θ·2^b`), the surprise count over
  any horizon satisfies `card · θ ≤ 4(C−1) + 2C · missCount i₀ n` for **every** candidate `i₀` in
  the pool — quantified over the whole pool, not chosen as an argmin, which is the presentation the
  bound is imported in. The horizon never reaches the right side by itself, only through one
  candidate's own errors, the same product form as `BayesRedundancy.surprise_card_mul_le`; the leak
  is priced against the *threshold* and against the reference's errors, never against elapsed time.
  This is the mixture-currency instance of the agnostic weighted-majority bound of Littlestone and
  Warmuth (1994); the theorem's own docstring carries the citation and says exactly what is proved
  here rather than imported.
* `floorSurprise_card_mul_le` — **the lifetime-free specialization**: read at a candidate that never
  misses, whose miss count is `0` at every horizon, the bound above becomes `card · θ ≤ 4(C−1)` over
  the whole run, `n` occurring only inside the surprise set. This is the form [Inevitability] §6
  consumes.
* `floorSurprises_unbounded_below_budget` — **the budget guard, proved first**. Below the budget
  threshold the bound above is not merely unproved but *false*: on the all-miss family every step is
  a surprise, so the count grows with the horizon without limit.
  `floorSurprises_unbounded_witness` is a concrete instance. The budget hypothesis is therefore
  load-bearing, and `floorSurprise_vacuous_at_badW_budget` marks the other edge — at the
  annihilating instance's own `C = W = 2` the hypothesis already forces `θ ≥ 1`, where
  `wrongMass_lt_one` leaves the surprise set empty.
* `floorSurprises_unbounded_everyMiss` and `floorSurprises_unbounded_altMiss` — **the realizability
  guard**, and it refutes rather than defers. With the budget gate *satisfied*, two families make
  every step a surprise: the degenerate one where nobody ever hits, and the non-degenerate one where
  two candidates miss alternately and each hits half the time.
  `floorSurprise_card_mul_gt_everyMiss_witness` and `floorSurprise_card_mul_gt_altMiss_witness`
  exhibit the gate holding and the conclusion failing at named parameters. So a lifetime-free right
  side is unavailable in general, and what replaces it is the reference candidate's own miss count —
  `floorSurprise_card_mul_le_missCount`, which holds of these families rather than excluding them.
  Read the other way they become sharpness witnesses: `le_of_card_mul_le_missCount_everyMiss` and
  `two_mul_le_of_card_mul_le_missCount_altMiss` force any admissible miss-count coefficient to be at
  least `θ`, and at least `2θ` on the alternating family. `wrongMass_everyMiss` refutes
  `wrongMass_lt_one` on the same family; `wrongMass_lt_one_of_hit` is its repair (the honest
  hypothesis there is *per-step*), and `wrongMass_le_one` is the unconditional non-strict form.
* `toDist_wRun_sub_bayesRun_le` — **the drift does not accumulate**. The floored run's reading stays
  within `2(C−1)/2^b` of the exact Bayes run's in total variation, *uniformly in the elapsed time*:
  the bound mentions no horizon at all. The per-step rate provably does not telescope, so what
  replaces the telescope is the normal form — rescaled by the common factor the clip cost it, the
  floored run agrees with the exact run coordinate for coordinate except on the saturated
  candidates. The residual measures the spread of the candidates' miss counts beyond `log₂ W`, and
  nothing about elapsed time. `toDist_mul_left` — normalization forgets a common scalar — is the
  one general-purpose lemma the argument needed.
* `toDist_wRun_sub_bayesRun_not_le_mirrorMiss` — **the same guard for accumulation**. On a mirror
  family whose two candidates end with equal miss counts, the exact run is symmetric while the
  floored one reads `1 : 8`, and the discrepancy is exactly `7/9` at *every* budget — against a
  bound that vanishes in the budget. What the floor buys is `tracking` the recent leader, and
  tracking is not approximating exact Bayes; the exact-Bayes comparison exists only in the one
  regime where the leader never changes.
* `toDist_wRun_sub_bayesFrom_le` — **the tracking form of that bound**, and it is the answer to the
  guard above rather than a retreat from it. Change the comparator: `bayesFrom` is exact Bayes
  **restarted at a time `s`** from the floored run's own state there. Against it the same
  `2(C−1)/2^b` holds, uniformly in the elapsed time, with no realizable candidate anywhere — the
  hypotheses are carried by one candidate over the window `[s, t)` alone, that it is a running
  co-leader at `s` and misses at no step inside. `coleader_persists` makes the first hypothesis
  propagate, and `expRun_eq_hitCount_sub` is the window's own normal form: the state at `s` plus the
  restarted hit count, less the rescales the window paid. The bound above is the `s = 0` instance
  (`bayesFrom_zero`), proved as such and not separately.
* `toDist_wRun_sub_bayesFrom_not_le_preAbsorption` and
  `toDist_wRun_sub_bayesFrom_not_le_sinkRecover` — **the two hypotheses are independent, and both
  load-bearing**. Each family drops exactly one and holds the discrepancy at a constant while the
  bound vanishes: `preAbsorption` (`C = 3`) offers the window a never-missing candidate
  (`preAbsorption_never_misses_one`) that is a whole budget short of co-leadership at `s`
  (`preAbsorption_not_coleader`), and reaches `850/963`; `sinkRecover` (`C = 2`) offers a genuine
  co-leader at `s` (`sinkRecover_coleader`) that later quits, and reaches `63/65`.
  `preAbsorption_misses_of_ne_one` and `sinkRecover_no_survivor` close the escape in each case: no
  other candidate could have been taken instead.
* `raw_wRun_eq_wMax_iff` / `argmax_wRun_eq_least_consistent` — **the ceiling set is the version
  space**. Under realizability a candidate carries the maximum weight exactly when its miss count is
  zero, so the reading — `argmax`, whose fold keeps the incumbent on ties — is the least-indexed
  candidate that has never missed. An identity, holding at every time past the first rescale rather
  than asymptotically, and read straight off the saturation normal form.
* `argmax_wRun_eventually_const` — **selection settles**. The version space is antitone and never
  empty, so the reading's index is a non-decreasing natural number below the candidate count:
  `argmax_wRun_mono` (which needs no guard — before the first rescale the pool ties and the reading
  sits at `0`) and then `argmax_wRun_card_changes_le`, the `C − 1` bound on how often it moves. What
  drives it is the **fitness alone**; the fiber has no variation rule to impose a settled shape.
* `rotMiss` / `argmax_wRun_rotMiss` / `wrongMass_rotMiss` — **the least-recently-wrong rotation**:
  `C` candidates, candidate `i` missing exactly at `t ≡ i (mod C)`. The reading is exactly the
  candidate about to miss (`argmax_wRun_rotMiss`), so it is dethroned at *every* step once `C ≥ 2`
  (`argmax_wRun_rotMiss_ne_succ`); yet the wrong mass never exceeds `2/(C+1)` (`wrongMass_rotMiss`),
  so the surprise set stays empty at any threshold at or above that floor
  (`floorSurpriseSet_rotMiss_eq_empty`). `rotMiss_prediction_identification_separation` assembles
  both halves, and `rotMiss_prediction_identification_separation_witness` is the concrete,
  non-vacuous instance. The reading is the classical follow-the-leader rule, already cited
  in-corpus via Lattimore–Hutter–Sunehag ([Discovery] §3.3); what is exhibited is the separation of
  two repair counters this file already carries, not a new reading.
* `argmaxFrame_wWorld_eventually_const` — **the fiber's own reading settles**, along a base
  trajectory and through the frame the pricing assembly uses. `predMiss` instantiates the abstract
  indicator at `predFitPos` scored against the base's next state, `missFit_predMiss` is the bridge,
  and `iterate_wWorld_wStartAt` identifies the skew product's fiber coordinate with `wRun`.
  Pathwise, from the all-ones start, with no hypothesis on the initial state;
  `argmaxFrame_wWorld_eventually_const_of_faithful` is the same statement from a codeword that
  decodes to the base rule itself.

## Scope

The regime above is the whole of what is claimed. General `W` is **not** covered *here*: the
exactness of the normal form is what a power-of-two budget buys, and outside it the rounding
residual returns and the per-step rate of `QuantizationRate` remains the only tool. (The one thing
that does hold at a general budget is the *settling* of the reading, which needs no closed form —
`BasinSettling`.) Neither is a general fitness ceiling, nor stochastic candidates. The event
bound's constant is linear in the candidate count where [Discovery] §3.3's is the description
length of the truth; that is the price of the uniform prior `wRun` starts from, and no sharpening
of it is attempted. The miss-count
coefficient is likewise linear in `C` where the logarithmic potential argument gives one free of it:
that is the price of an additive accounting in ℚ, and the sharpness readings above bound how much is
being given away. The tracking form of the *accumulation* bound reaches only the comparator
restarted at a co-leader point: what is false against exact Bayes from the beginning of time stays
false, and the restarted form's own guards say what is false without each of its hypotheses.
No bound against a comparator restarted at an *arbitrary* time is claimed, and the two families
show why one is not available. The floored process is treated abstractly through `M`, and
[Discovery] §3.3's own fixed-mixture bound is untouched, exported exactly as before.

The convergence at the end is the **discovery** half only, and it is pathwise: the reading settles
on a candidate consistent with the observed trajectory, at every trajectory that carries one. It is
stated from the fiber's own all-ones start, and everything it says *about which candidate* the
reading settles on is a privilege of that start — `BasinSettling` carries settling to every initial
weight vector and every budget, and refutes the version-space characterization, the reading's
monotonicity and the `C − 1` change count there. What neither gives is the **race**: which initial
conditions let discovery outrun damage turns on the survival half, priced elsewhere; nothing here
covers the winner-take-all fiber, whose fixed pool is not this dynamics, nor a noisy base, where
even the best candidate misses and realizability fails. Nor is any of it a **coverage** statement:
the pricing assembly's hypothesis quantifies over initial states of the base coordinate, and neither
condition implies the other.

Both statements are in ℚ wrong-mass form rather than squared-Hellinger form. For deterministic
point-predicting candidates the translation is arithmetic — the mixture's probability of the
realized symbol is `1 −` the wrong mass — and keeping it out of the Lean statement avoids a real
square root for no added content, at the same abstraction level at which [Inevitability] §6 consumes
the fixed-mixture surprise set.

The rotation family sits inside the same below-the-horizon regime as the general normal form: its
closed forms hold for `t ≤ b`, and no claim is made past it. What it claims is exactly the
separation of two repair counters this file already carries — nothing about observer
synchronization, stored structure, or program-running-time depth, none of which any result here
characterizes, contrasts with, or bears on.
-/

namespace WeightedFiber

section Normal

variable {C : ℕ}

/-- The `2`-vs-`1` fitness of `predFitPos`, driven by an abstract miss indicator. -/
def missFit (M : ℕ → Fin C → Bool) : ℕ → Fin C → ℕ := fun t i => if M t i then 1 else 2

/-- How often candidate `i` has missed strictly before time `t`. -/
def missCount (M : ℕ → Fin C → Bool) (i : Fin C) (t : ℕ) : ℕ :=
  ((Finset.range t).filter fun s => M s i).card

private theorem missCount_zero (M : ℕ → Fin C → Bool) (i : Fin C) : missCount M i 0 = 0 := by
  simp [missCount]

private theorem missCount_succ (M : ℕ → Fin C → Bool) (i : Fin C) (t : ℕ) :
    missCount M i (t + 1) = missCount M i t + (if M t i then 1 else 0) := by
  rw [missCount, missCount, Finset.range_add_one, Finset.filter_insert]
  by_cases h : M t i
  · rw [if_pos h, Finset.card_insert_of_notMem (by simp), if_pos h]
  · rw [if_neg h, if_neg h, Nat.add_zero]

private theorem missCount_le (M : ℕ → Fin C → Bool) (i : Fin C) (t : ℕ) : missCount M i t ≤ t := by
  rw [missCount]
  exact le_trans (Finset.card_filter_le _ _) (by simp)

theorem missCount_eq_zero (M : ℕ → Fin C → Bool) {i : Fin C} (h : ∀ t, M t i = false) (t : ℕ) :
    missCount M i t = 0 := by
  induction t with
  | zero => exact missCount_zero M i
  | succ t ih => rw [missCount_succ, ih, if_neg (by simp [h t])]

/-- The converse, read at one step: a zero miss count over a horizon means no miss inside it. -/
theorem eq_false_of_missCount_eq_zero {M : ℕ → Fin C → Bool} {i : Fin C} {t s : ℕ}
    (h : missCount M i t = 0) (hs : s < t) : M s i = false := by
  by_contra hc
  rw [missCount, Finset.card_eq_zero] at h
  have : s ∈ (Finset.range t).filter fun u => M u i :=
    Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hs, by simpa using hc⟩
  rw [h] at this
  exact absurd this (Finset.notMem_empty s)

/-! ### The exponent automaton

The floored run's whole state is one exponent per candidate. `expStep` is the transition, and it
carries **no hypothesis**: a hit adds one to the candidate's exponent, and the common rescale
subtracts one from *every* exponent exactly when some candidate already at the ceiling hits. That
last clause is the entire content of the budget projection — the rescale tracks the weight vector's
maximum, so a step costs the whole population one doubling precisely when the leader would otherwise
overflow. -/

/-- One step of the exponent automaton: a hit adds one, and the common rescale subtracts one exactly
when some candidate at the ceiling hits. ℕ-subtraction carries the floor. -/
def expStep (b : ℕ) (m : Fin C → Bool) (e : Fin C → ℕ) : Fin C → ℕ :=
  fun i => (e i + (if m i then 0 else 1)) - (if ∃ j, e j = b ∧ m j = false then 1 else 0)

/-- The floored run's exponent vector, from the all-ones start. -/
def expRun (M : ℕ → Fin C → Bool) (b : ℕ) : ℕ → (Fin C → ℕ)
  | 0 => fun _ => 0
  | t + 1 => expStep b (M t) (expRun M b t)

/-- **The exponents never leave the budget.** The ceiling `b` is an invariant of the automaton, and
proving it needs nothing about the miss sequence: the only way to reach `b + 1` is from `b` on a
hit, and a candidate hitting at the ceiling is exactly what triggers the rescale. -/
theorem expRun_le (M : ℕ → Fin C → Bool) (b t : ℕ) (i : Fin C) : expRun M b t i ≤ b := by
  induction t generalizing i with
  | zero => exact Nat.zero_le b
  | succ t ih =>
      change expStep b (M t) (expRun M b t) i ≤ b
      rw [expStep]
      have hi := ih i
      by_cases hδ : ∃ j, expRun M b t j = b ∧ M t j = false
      · rw [if_pos hδ]
        split <;> omega
      · rw [if_neg hδ]
        by_cases hm : M t i
        · rw [if_pos hm]; omega
        · rw [if_neg hm]
          have : expRun M b t i ≠ b := fun hb => hδ ⟨i, hb, by simpa using hm⟩
          omega

/-- **The general normal form** — the floored run, in closed form, with no hypothesis at all.

At a power-of-two budget and the `2`-vs-`1` fitness shape, `raw (wRun (2^b) (missFit M) t)` is
*exactly* `2 ^ expRun M b t`: every weight is a power of two at every step, and the whole run is the
exponent automaton above. Realizability plays no part — it enters the *closed form* below only
through the divisor, and the divisor is leader-relative to begin with.

The proof is the two divisor computations. A candidate at the ceiling that hits pushes the post-step
maximum to `2 ^ (b+1)`, where the rescale divisor is exactly `2`; otherwise the maximum stays inside
the budget and the divisor is exactly `1`. Because every weight is a power of two, dividing by `2`
subtracts one exponent — and the projection's floor at one quantum is precisely the ℕ-subtraction's
clip at exponent `0`. -/
theorem wRun_eq_pow_expRun (M : ℕ → Fin C → Bool) (b t : ℕ) (i : Fin C) :
    raw (wRun (2 ^ b) (missFit M) t) i = 2 ^ expRun M b t i := by
  have hW : 1 ≤ 2 ^ b := Nat.one_le_two_pow
  induction t generalizing i with
  | zero =>
      change raw (pack (2 ^ b) (fun _ => (1 : ℕ))) i = _
      rw [raw, pack]
      simp [expRun, min_eq_left hW]
  | succ t ih =>
      have hstep : raw (wRun (2 ^ b) (missFit M) (t + 1))
          = project (2 ^ b) (bayesStep (missFit M t) (raw (wRun (2 ^ b) (missFit M) t))) := by
        change raw (wGen (2 ^ b) (missFit M t) (wRun (2 ^ b) (missFit M) t)) = _
        exact raw_wGen hW _ _
      set u : Fin C → ℕ := bayesStep (missFit M t) (raw (wRun (2 ^ b) (missFit M) t)) with hu
      have hui : ∀ j, u j = 2 ^ (expRun M b t j + (if M t j then 0 else 1)) := by
        intro j
        rw [hu, bayesStep, ih j, missFit]
        by_cases h : M t j
        · rw [if_pos h, if_pos h, Nat.mul_one, Nat.add_zero]
        · rw [if_neg h, if_neg h, pow_succ]
      rw [hstep]
      change project (2 ^ b) u i = 2 ^ expStep b (M t) (expRun M b t) i
      rw [expStep, project]
      by_cases hδ : ∃ j, expRun M b t j = b ∧ M t j = false
      · -- a candidate at the ceiling hits: the post-step maximum is `2 ^ (b+1)`, the divisor is `2`
        rw [if_pos hδ]
        obtain ⟨j₀, hj₀e, hj₀m⟩ := hδ
        have hmax : wMax u = 2 ^ (b + 1) := by
          refine le_antisymm (Finset.sup_le fun j _ => ?_) ?_
          · rw [hui j]
            refine Nat.pow_le_pow_right (by norm_num) ?_
            have := expRun_le M b t j
            split <;> omega
          · have hj : u j₀ = 2 ^ (b + 1) := by
              rw [hui j₀, hj₀e, if_neg (by simp [hj₀m])]
            exact hj ▸ le_wMax u j₀
        have hd2 : scaleDiv (2 ^ b) u = 2 := by
          rw [scaleDiv, hmax, pow_succ]
          have : (2 ^ b * 2 + 2 ^ b - 1) / 2 ^ b = 2 :=
            Nat.div_eq_of_lt_le (by omega) (by omega)
          omega
        rw [hd2, hui i]
        rcases Nat.eq_zero_or_pos (expRun M b t i + (if M t i then 0 else 1)) with h0 | hpos
        · rw [h0]
          norm_num
        · obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hpos.ne'
          rw [hk, pow_succ, Nat.mul_div_cancel _ (by norm_num), Nat.succ_sub_one]
          exact max_eq_right Nat.one_le_two_pow
      · -- no ceiling candidate hits: the maximum stays inside the budget and the divisor is `1`
        rw [if_neg hδ]
        have hle : wMax u ≤ 2 ^ b := by
          refine Finset.sup_le fun j _ => ?_
          rw [hui j]
          refine Nat.pow_le_pow_right (by norm_num) ?_
          have h1 := expRun_le M b t j
          by_cases hm : M t j
          · rw [if_pos hm]; omega
          · rw [if_neg hm]
            have : expRun M b t j ≠ b := fun hb => hδ ⟨j, hb, by simpa using hm⟩
            omega
        have hd1 : scaleDiv (2 ^ b) u = 1 := by
          have hlt : (wMax u + 2 ^ b - 1) / 2 ^ b < 2 :=
            (Nat.div_lt_iff_lt_mul (by omega)).mpr (by omega)
          rw [scaleDiv]
          omega
        rw [hd1, Nat.div_one, hui i, Nat.sub_zero]
        exact max_eq_right Nat.one_le_two_pow

/-! ### The running leader

The rescale is driven by the largest exponent in play. Under realizability that leader is frozen at
the truth; in general it is still a well-behaved object, and the two facts the automaton needs are
theorems rather than hypotheses. -/

/-- The **running leader's exponent**: the largest exponent any candidate holds at time `t`. -/
def expMax (M : ℕ → Fin C → Bool) (b t : ℕ) : ℕ := Finset.univ.sup (expRun M b t)

theorem expMax_le (M : ℕ → Fin C → Bool) (b t : ℕ) : expMax M b t ≤ b :=
  Finset.sup_le fun i _ => expRun_le M b t i

/-- The one-step fact behind both leader theorems. When no ceiling candidate hits, every coordinate
is non-decreasing; when one does, that candidate itself lands back on the ceiling, which already
dominates the pre-step maximum. -/
theorem sup_le_sup_expStep (b : ℕ) (m : Fin C → Bool) (e : Fin C → ℕ) (he : ∀ i, e i ≤ b) :
    Finset.univ.sup e ≤ Finset.univ.sup (expStep b m e) := by
  by_cases hδ : ∃ j, e j = b ∧ m j = false
  · obtain ⟨j, hje, hjm⟩ := hδ
    have hδ' : ∃ j, e j = b ∧ m j = false := ⟨j, hje, hjm⟩
    have hj : expStep b m e j = b := by
      change (e j + (if m j then 0 else 1)) - (if ∃ j, e j = b ∧ m j = false then 1 else 0) = b
      rw [if_neg (by simp [hjm] : ¬ (m j = true)), if_pos hδ', hje]
      omega
    calc Finset.univ.sup e ≤ b := Finset.sup_le fun i _ => he i
      _ = expStep b m e j := hj.symm
      _ ≤ Finset.univ.sup (expStep b m e) := Finset.le_sup (Finset.mem_univ j)
  · refine Finset.sup_mono_fun fun i _ => ?_
    change e i ≤ (e i + (if m i then 0 else 1)) - (if ∃ j, e j = b ∧ m j = false then 1 else 0)
    rw [if_neg hδ]
    omega

/-- **The leader never falls back.** The largest exponent in play is non-decreasing in time — no
hypothesis, no realizability. -/
theorem expMax_mono (M : ℕ → Fin C → Bool) (b : ℕ) {t t' : ℕ} (h : t ≤ t') :
    expMax M b t ≤ expMax M b t' := by
  obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le h
  clear h
  induction s with
  | zero => simp
  | succ s ih =>
      refine le_trans ih ?_
      change Finset.univ.sup (expRun M b (t + s)) ≤ Finset.univ.sup (expStep b (M (t + s))
        (expRun M b (t + s)))
      exact sup_le_sup_expStep b (M (t + s)) (expRun M b (t + s)) (expRun_le M b (t + s))

/-- **The ceiling absorbs.** Once any candidate reaches the budget exponent, some candidate holds it
forever after: the leader is non-decreasing and can never exceed `b`. -/
theorem expMax_absorbing (M : ℕ → Fin C → Bool) (b t : ℕ) (h : expMax M b t = b) (s : ℕ) :
    expMax M b (t + s) = b := by
  refine le_antisymm (expMax_le M b (t + s)) ?_
  calc b = expMax M b t := h.symm
    _ ≤ expMax M b (t + s) := expMax_mono M b (Nat.le_add_right t s)

/-- A candidate's **deficit against the running leader**: how many doublings behind the largest
exponent in play it sits. This is the general form of the geometric charge: under realizability the
leader is the truth and the deficit is the miss count clipped at the budget exponent, but the
reading is controlled by the deficit whether or not the leader is frozen. -/
def expDef (M : ℕ → Fin C → Bool) (b t : ℕ) (i : Fin C) : ℕ := expMax M b t - expRun M b t i

theorem expDef_le (M : ℕ → Fin C → Bool) (b t : ℕ) (i : Fin C) : expDef M b t i ≤ b :=
  le_trans (Nat.sub_le _ _) (expMax_le M b t)

/-! ### The realizable closed form -/

/-- **Realizability collapses the automaton to a clipped deficit.** A candidate that never misses
sits at the ceiling from time `b` onwards, so from then on *every* step triggers the rescale and the
leader is frozen: a hit pays nothing, a miss costs one exponent, and the exponent is the clipped
deficit `min t b − missCount M i t`. -/
theorem expRun_eq_deficit (M : ℕ → Fin C → Bool) {iR : Fin C} (hR : ∀ t, M t iR = false)
    (b t : ℕ) (i : Fin C) : expRun M b t i = min t b - missCount M i t := by
  induction t generalizing i with
  | zero => rw [missCount_zero]; simp [expRun]
  | succ t ih =>
      change expStep b (M t) (expRun M b t) i = _
      have hiR : expRun M b t iR = min t b := by
        rw [ih iR, missCount_eq_zero M hR t, Nat.sub_zero]
      have hδ : (∃ j, expRun M b t j = b ∧ M t j = false) ↔ b ≤ t := by
        constructor
        · rintro ⟨j, hj, -⟩
          rw [ih j] at hj
          have := missCount_le M j t
          omega
        · exact fun hbt => ⟨iR, by rw [hiR]; omega, hR t⟩
      rw [expStep, ih i, missCount_succ]
      have hm := missCount_le M i t
      by_cases hbt : b ≤ t
      · rw [if_pos (hδ.mpr hbt), min_eq_right hbt, min_eq_right (by omega : b ≤ t + 1)]
        clear hδ hiR ih
        by_cases h : M t i
        · rw [if_pos h, if_pos h]; omega
        · rw [if_neg h, if_neg h]; omega
      · rw [if_neg fun hh => hbt (hδ.mp hh), min_eq_left (by omega : t ≤ b),
          min_eq_left (by omega : t + 1 ≤ b)]
        clear hδ hiR ih
        by_cases h : M t i
        · rw [if_pos h, if_pos h]; omega
        · rw [if_neg h, if_neg h]; omega

/-- **The saturation normal form** — the floored run, in closed form.

At a power-of-two budget, with the `2`-vs-`1` fitness shape and a candidate that never misses, the
projected run is *exactly* a clipped-deficit automaton: candidate `i` carries
`2 ^ (min t b - missCount M i t)`, the ℕ-subtraction carrying the clip. This is an identity, not an
approximation, and that is what the regime buys. Realizability holds the truth at the ceiling, so
past the horizon the post-step maximum is exactly twice the budget and the common divisor is
exactly `2`; a hit then pays `·2/2` and costs nothing, a miss pays `·1/2` and costs one exponent,
floored at one quantum. Every weight stays a power of two and the rounding residual — the whole
subject of `QuantizationRate`'s per-step rate — vanishes identically here.

Both sides of the horizon are covered by the one formula: below it `min t b` is `t` and the
exponent is the hit count, which is `raw_wRun_eq_bayesRun`'s regime.

This is `wRun_eq_pow_expRun` read at a frozen leader: the hub is hypothesis-free, and realizability
buys exactly the collapse of the exponent automaton to a clipped deficit. -/
theorem wRun_eq_pow_deficit (M : ℕ → Fin C → Bool) {iR : Fin C}
    (hR : ∀ t, M t iR = false) (b t : ℕ) (i : Fin C) :
    raw (wRun (2 ^ b) (missFit M) t) i = 2 ^ (min t b - missCount M i t) := by
  rw [wRun_eq_pow_expRun M b t i, expRun_eq_deficit M hR b t i]

/-- The exact-run analogue of the normal form: with no carrier there is no clip, so the exponent is
the plain hit count and grows without bound. The difference between this and `wRun_eq_pow_deficit`
is the whole of what the finite carrier costs. -/
theorem bayesRun_missFit (M : ℕ → Fin C → Bool) (t : ℕ) (i : Fin C) :
    bayesRun (missFit M) t i = 2 ^ (t - missCount M i t) := by
  induction t with
  | zero => simp [bayesRun, missCount_zero]
  | succ t ih =>
      have hm := missCount_le M i t
      change bayesStep (missFit M t) (bayesRun (missFit M) t) i = _
      rw [bayesStep, ih, missFit, missCount_succ]
      by_cases h : M t i
      · rw [if_pos h, if_pos h, Nat.mul_one]
        congr 1
        omega
      · rw [if_neg h, if_neg h, Nat.add_zero, ← pow_succ]
        congr 1
        omega

/-- **Below the horizon the normal form is the known regime.** One formula covers both sides of the
horizon: while `t ≤ b` the clip has not bitten, the two exponents coincide, and the floored run is
the exact run — `raw_wRun_eq_bayesRun`'s conclusion, recovered here from the normal form alone for
the `{1,2}`-fitness family. -/
theorem raw_wRun_eq_bayesRun_missFit (M : ℕ → Fin C → Bool) {iR : Fin C} (hR : ∀ t, M t iR = false)
    {b t : ℕ} (ht : t ≤ b) (i : Fin C) :
    raw (wRun (2 ^ b) (missFit M) t) i = bayesRun (missFit M) t i := by
  rw [wRun_eq_pow_deficit M hR b t i, bayesRun_missFit, min_eq_left ht]

/-- **Below the horizon, realizability was never needed.** The clip has not bitten while `t ≤ b`, so
no candidate — realizable or not — can yet sit at the ceiling and trigger a rescale: the exponent is
the plain hit count for *any* miss indicator. `raw_wRun_eq_bayesRun_missFit` is this fact composed
with `bayesRun_missFit`'s own closed form; realizability only starts to matter once some candidate
could be at the ceiling, i.e. past the horizon. -/
theorem expRun_eq_sub_missCount_of_le (M : ℕ → Fin C → Bool) (b : ℕ) :
    ∀ t, t ≤ b → ∀ i, expRun M b t i = t - missCount M i t := by
  intro t
  induction t with
  | zero => intro _ i; rw [missCount_zero]; simp [expRun]
  | succ t ih =>
      intro ht i
      have ht' : t ≤ b := by omega
      have hall : ∀ j, expRun M b t j ≤ t := by
        intro j
        rw [ih ht' j]
        omega
      have hnodelta : ¬ ∃ j, expRun M b t j = b ∧ M t j = false := by
        rintro ⟨j, hj, -⟩
        have := hall j
        omega
      change expStep b (M t) (expRun M b t) i = _
      rw [expStep, if_neg hnodelta, ih ht' i, missCount_succ]
      have hmc := missCount_le M i t
      by_cases h : M t i
      · rw [if_pos h, if_pos h]; omega
      · rw [if_neg h, if_neg h]; omega

private theorem missCount_mono (M : ℕ → Fin C → Bool) (i : Fin C) {t t' : ℕ} (h : t ≤ t') :
    missCount M i t ≤ missCount M i t' := by
  rw [missCount, missCount]
  exact Finset.card_le_card (Finset.filter_subset_filter _ (Finset.range_mono h))

/-! ### The restarted normal form

Everything above reads the run from its own start. The *tracking* question reads it from an
arbitrary time `s`: how does the floored run at `t` compare with exact Bayes continued from the
state the floored run itself held at `s`? Two facts answer it, and neither needs a realizable
candidate. The first is that **co-leadership persists** while its holder keeps hitting. The second
is that under that hypothesis the window `[s, t)` is again one exponent automaton, run from the
state at `s`: each candidate's exponent is its restarted hit count less the rescales the window
paid, and the rescale count is determined by the co-leader's own distance from the ceiling. -/

/-- Over a window the miss count grows by at most the window's own length. -/
private theorem missCount_le_add (M : ℕ → Fin C → Bool) (i : Fin C) (s d : ℕ) :
    missCount M i (s + d) ≤ missCount M i s + d := by
  induction d with
  | zero => simp
  | succ d ih =>
      rw [show s + (d + 1) = (s + d) + 1 from rfl, missCount_succ]
      split <;> omega

/-- A window with no miss in it leaves the miss count where it found it. -/
private theorem missCount_eq_of_no_miss (M : ℕ → Fin C → Bool) (i : Fin C) (s d : ℕ) :
    (∀ u, s ≤ u → u < s + d → M u i = false) → missCount M i (s + d) = missCount M i s := by
  induction d with
  | zero => intro _; rfl
  | succ d ih =>
      intro h
      rw [show s + (d + 1) = (s + d) + 1 from rfl, missCount_succ,
        ih (fun u hu hlt => h u hu (by omega)),
        if_neg (by simp [h (s + d) (by omega) (by omega)])]
      omega

/-- How often candidate `i` has **hit** over the window `[s, t)`: the window's length, less the
misses inside it. At `s = 0` it is the whole run's hit count `t − missCount M i t`. -/
def hitCount (M : ℕ → Fin C → Bool) (i : Fin C) (s t : ℕ) : ℕ :=
  (t - s) - (missCount M i t - missCount M i s)

private theorem hitCount_self (M : ℕ → Fin C → Bool) (i : Fin C) (s : ℕ) :
    hitCount M i s s = 0 := by
  rw [hitCount]; omega

private theorem hitCount_zero (M : ℕ → Fin C → Bool) (i : Fin C) (t : ℕ) :
    hitCount M i 0 t = t - missCount M i t := by
  rw [hitCount, missCount_zero]; omega

private theorem hitCount_succ (M : ℕ → Fin C → Bool) (i : Fin C) {s t : ℕ} (h : s ≤ t) :
    hitCount M i s (t + 1) = hitCount M i s t + (if M t i then 0 else 1) := by
  have h1 : missCount M i s ≤ missCount M i t := missCount_mono M i h
  have h2 : missCount M i t ≤ missCount M i s + (t - s) := by
    have := missCount_le_add M i s (t - s)
    rwa [show s + (t - s) = t from by omega] at this
  rw [hitCount, hitCount, missCount_succ]
  by_cases hM : M t i
  · rw [if_pos hM, if_pos hM]; omega
  · rw [if_neg hM, if_neg hM]; omega

/-- A candidate that never misses inside the window hits at every one of its steps. -/
private theorem hitCount_of_no_miss (M : ℕ → Fin C → Bool) (i : Fin C) {s t : ℕ} (hst : s ≤ t)
    (h : ∀ u, s ≤ u → u < t → M u i = false) : hitCount M i s t = t - s := by
  have := missCount_eq_of_no_miss M i s (t - s) (fun u hu hlt => h u hu (by omega))
  rw [show s + (t - s) = t from by omega] at this
  rw [hitCount, this]
  omega

/-- **Co-leadership persists while its holder keeps hitting.** If `iL` carries a maximal exponent
at time `s` and misses at no step of `[s, t)`, then it carries a maximal exponent throughout
`[s, t]`. One induction does it, and it needs nothing else about the run: the rescale is charged to
everyone alike, a hit adds at most one exponent to anyone, and `iL` collects that one at every
step. -/
theorem coleader_persists (M : ℕ → Fin C → Bool) (b : ℕ) {iL : Fin C} {s t : ℕ}
    (hlead : ∀ j, expRun M b s j ≤ expRun M b s iL)
    (hiL : ∀ u, s ≤ u → u < t → M u iL = false) :
    ∀ u, s ≤ u → u ≤ t → ∀ j, expRun M b u j ≤ expRun M b u iL := by
  suffices h : ∀ d, s + d ≤ t → ∀ j, expRun M b (s + d) j ≤ expRun M b (s + d) iL by
    intro u hsu hut
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hsu
    exact h d hut
  intro d
  induction d with
  | zero => intro _ j; simpa using hlead j
  | succ d ih =>
      intro hd j
      have hj := ih (by omega) j
      have hms : M (s + d) iL = false := hiL (s + d) (by omega) (by omega)
      change expStep b (M (s + d)) (expRun M b (s + d)) j
        ≤ expStep b (M (s + d)) (expRun M b (s + d)) iL
      simp only [expStep]
      rw [if_neg (by simp [hms] : ¬ (M (s + d) iL = true))]
      by_cases hδ : ∃ k, expRun M b (s + d) k = b ∧ M (s + d) k = false
      · rw [if_pos hδ]
        by_cases hjm : M (s + d) j
        · rw [if_pos hjm]; omega
        · rw [if_neg hjm]; omega
      · rw [if_neg hδ]
        by_cases hjm : M (s + d) j
        · rw [if_pos hjm]; omega
        · rw [if_neg hjm]; omega

/-- **The window is again one automaton.** Under a co-leader that never misses, the exponent at
`s + d` is the state at `s` plus the window's hit count, less the window's rescale count — and that
rescale count is `d` beyond the co-leader's own distance `b − expRun M b s iL` from the ceiling,
because until the co-leader reaches the ceiling nobody is at it and no step rescales, and from then
on the co-leader is at it and hits, so every step does. -/
private theorem expRun_restart (M : ℕ → Fin C → Bool) (b : ℕ) {iL : Fin C} {s t : ℕ}
    (hlead : ∀ j, expRun M b s j ≤ expRun M b s iL)
    (hiL : ∀ u, s ≤ u → u < t → M u iL = false) :
    ∀ d, s + d ≤ t →
      expRun M b (s + d) iL = min (expRun M b s iL + d) b ∧
      ∀ i, expRun M b (s + d) i
        = (expRun M b s i + hitCount M i s (s + d)) - (d - (b - expRun M b s iL)) := by
  have hcb : expRun M b s iL ≤ b := expRun_le M b s iL
  intro d
  induction d with
  | zero =>
      intro _
      refine ⟨by rw [Nat.add_zero, Nat.add_zero]; omega, ?_⟩
      intro i
      rw [Nat.add_zero, hitCount_self]
      omega
  | succ d ih =>
      intro hd
      obtain ⟨ihL, ihi⟩ := ih (by omega)
      have hms : M (s + d) iL = false := hiL (s + d) (by omega) (by omega)
      have hcol : ∀ j, expRun M b (s + d) j ≤ expRun M b (s + d) iL :=
        coleader_persists M b hlead hiL (s + d) (by omega) (by omega)
      have hδ : (∃ k, expRun M b (s + d) k = b ∧ M (s + d) k = false)
          ↔ b ≤ expRun M b s iL + d := by
        constructor
        · rintro ⟨k, hk, -⟩
          have hkl := hcol k
          rw [hk, ihL] at hkl
          omega
        · intro hb
          exact ⟨iL, by rw [ihL]; omega, hms⟩
      have hstep : ∀ i, expRun M b (s + (d + 1)) i
          = (expRun M b (s + d) i + (if M (s + d) i then 0 else 1))
            - (if b ≤ expRun M b s iL + d then 1 else 0) := by
        intro i
        change expStep b (M (s + d)) (expRun M b (s + d)) i = _
        rw [expStep]
        congr 1
        by_cases h : b ≤ expRun M b s iL + d
        · rw [if_pos h, if_pos (hδ.mpr h)]
        · rw [if_neg h, if_neg (fun hh => h (hδ.mp hh))]
      have hhc : ∀ i, hitCount M i s (s + (d + 1))
          = hitCount M i s (s + d) + (if M (s + d) i then 0 else 1) :=
        fun i => hitCount_succ M i (by omega : s ≤ s + d)
      clear hδ hcol ih hiL hlead
      refine ⟨?_, ?_⟩
      · rw [hstep iL, if_neg (by simp [hms] : ¬ (M (s + d) iL = true)), ihL]
        clear hstep ihi ihL hms
        split <;> omega
      · intro i
        rw [hstep i, ihi i, hhc i]
        clear hstep ihi ihL hms hhc
        have hh : (if M (s + d) i then (0 : ℕ) else 1) ≤ 1 := by split <;> omega
        by_cases hbc : b ≤ expRun M b s iL + d
        · rw [if_pos hbc]; omega
        · rw [if_neg hbc]; omega

/-- The restarted normal form, read at the window's far end. -/
theorem expRun_eq_hitCount_sub (M : ℕ → Fin C → Bool) (b : ℕ) {iL : Fin C} {s t : ℕ}
    (hst : s ≤ t) (hlead : ∀ j, expRun M b s j ≤ expRun M b s iL)
    (hiL : ∀ u, s ≤ u → u < t → M u iL = false) (i : Fin C) :
    expRun M b t i
      = (expRun M b s i + hitCount M i s t) - ((t - s) - (b - expRun M b s iL)) := by
  have h := (expRun_restart M b hlead hiL (t - s) (by omega)).2 i
  rwa [show s + (t - s) = t from by omega] at h

end Normal

/-! ## The event bound -/

section Event

variable {C : ℕ}

/-- The mixture's mass on the candidates that miss at time `t` — the reading's own probability of
being wrong at that step. For deterministic point-predicting candidates this is `1 −` the
probability the mixture assigns the realized symbol, which is why the bounds below can stay in ℚ
rather than reaching for a square root. -/
def wrongMass (M : ℕ → Fin C → Bool) (b t : ℕ) : ℚ :=
  ∑ i, if M t i then toDist (raw (wRun (2 ^ b) (missFit M) t)) i else 0

/-- The steps, before `n`, at which the wrong mass strictly exceeds the threshold `θ`. The
membership condition is strict, as in `BayesRedundancy.surpriseSet`. -/
def floorSurpriseSet (M : ℕ → Fin C → Bool) (b : ℕ) (θ : ℚ) (n : ℕ) : Finset ℕ :=
  (Finset.range n).filter fun t => θ < wrongMass M b t

/-! ### The leader-relative charge

The realizable argument charged each candidate against the *truth*, which holds the ceiling from
time `b` onwards. With no realizable candidate there is no fixed reference — but there is still a
running leader, and `expMax` makes it a proved object rather than an assumption. What controls the
reading is `expDef`, the deficit against that leader, the general form of the realizable charge. -/

/-- **The share, against the running leader.** A candidate's posterior mass is at most
`(1/2) ^ expDef`, because the leader alone accounts for `2 ^ expMax` of the total weight. No
hypothesis, in particular no realizable candidate — under realizability the leader *is* the truth
and this is the realizable geometric charge, the deficit being the clipped miss count. -/
theorem toDist_wRun_le_expDef (M : ℕ → Fin C → Bool) (b t : ℕ) (i : Fin C) :
    toDist (raw (wRun (2 ^ b) (missFit M) t)) i ≤ (1 / 2 : ℚ) ^ expDef M b t i := by
  have hw : ∀ j, ((raw (wRun (2 ^ b) (missFit M) t) j : ℕ) : ℚ) = (2 : ℚ) ^ expRun M b t j := by
    intro j
    rw [wRun_eq_pow_expRun]
    push_cast
    ring
  have hile : expRun M b t i ≤ expMax M b t := Finset.le_sup (Finset.mem_univ i)
  have hkey : ((raw (wRun (2 ^ b) (missFit M) t) i : ℕ) : ℚ) / (2 : ℚ) ^ expMax M b t
      = (1 / 2 : ℚ) ^ expDef M b t i := by
    have hsplit : (2 : ℚ) ^ expMax M b t
        = (2 : ℚ) ^ expDef M b t i * (2 : ℚ) ^ expRun M b t i := by
      rw [← pow_add, expDef]
      congr 1
      omega
    rw [hw i, hsplit, div_pow, one_pow]
    field_simp
  rw [← hkey]
  obtain ⟨j₀, -, hj₀⟩ :=
    Finset.exists_mem_eq_sup (Finset.univ : Finset (Fin C)) ⟨i, Finset.mem_univ i⟩ (expRun M b t)
  have hpos : (0 : ℚ) < (2 : ℚ) ^ expMax M b t := by positivity
  have hZ : (2 : ℚ) ^ expMax M b t ≤ ∑ j, ((raw (wRun (2 ^ b) (missFit M) t) j : ℕ) : ℚ) := by
    rw [expMax, hj₀, ← hw j₀]
    exact Finset.single_le_sum (f := fun j => ((raw (wRun (2 ^ b) (missFit M) t) j : ℕ) : ℚ))
      (fun j _ => by positivity) (Finset.mem_univ j₀)
  change ((raw (wRun (2 ^ b) (missFit M) t) i : ℕ) : ℚ)
      / ∑ j, ((raw (wRun (2 ^ b) (missFit M) t) j : ℕ) : ℚ) ≤ _
  gcongr

/-- **The wrong mass is a probability.** The reading is a distribution, so the mass on candidates
that miss never exceeds `1` — no hypothesis, and `wrongMass_everyMiss` attains the value.
`wrongMass_lt_one_of_hit` is the strict form, and it needs some candidate to hit. -/
theorem wrongMass_le_one (M : ℕ → Fin C → Bool) (b t : ℕ) : wrongMass M b t ≤ 1 := by
  rcases Nat.eq_zero_or_pos C with hC | hC
  · subst hC
    rw [wrongMass]
    simp
  · have hw : ∀ j, ((raw (wRun (2 ^ b) (missFit M) t) j : ℕ) : ℚ) = (2 : ℚ) ^ expRun M b t j := by
      intro j
      rw [wRun_eq_pow_expRun]
      push_cast
      ring
    have hZ : (0 : ℚ) < ∑ j, ((raw (wRun (2 ^ b) (missFit M) t) j : ℕ) : ℚ) :=
      Finset.sum_pos (fun j _ => by rw [hw j]; positivity)
        ⟨⟨0, hC⟩, Finset.mem_univ (⟨0, hC⟩ : Fin C)⟩
    calc wrongMass M b t ≤ ∑ i, toDist (raw (wRun (2 ^ b) (missFit M) t)) i := by
          refine Finset.sum_le_sum fun i _ => ?_
          split
          · exact le_refl _
          · exact div_nonneg (by positivity) hZ.le
      _ = 1 := by
          change (∑ i, ((raw (wRun (2 ^ b) (missFit M) t) i : ℕ) : ℚ)
            / ∑ j, ((raw (wRun (2 ^ b) (missFit M) t) j : ℕ) : ℚ)) = 1
          simp_rw [div_eq_mul_inv]
          rw [← Finset.sum_mul, ← div_eq_mul_inv, div_self hZ.ne']

/-- The saturated half of the charge: candidates the floor has pushed a full budget behind the
leader. -/
private def satCharge (M : ℕ → Fin C → Bool) (b t : ℕ) (i : Fin C) : ℚ :=
  if M t i ∧ b ≤ expDef M b t i then (1 / 2 : ℚ) ^ b else 0

/-- The unsaturated half: candidates still inside the budget, charged by their own deficit. -/
private def unsatCharge (M : ℕ → Fin C → Bool) (b t : ℕ) (i : Fin C) : ℚ :=
  if M t i ∧ expDef M b t i < b then (1 / 2 : ℚ) ^ expDef M b t i else 0

private theorem wrongMass_le_charges (M : ℕ → Fin C → Bool) (b t : ℕ) :
    wrongMass M b t ≤ (∑ i, satCharge M b t i) + ∑ i, unsatCharge M b t i := by
  rw [← Finset.sum_add_distrib, wrongMass]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [satCharge, unsatCharge]
  by_cases hM : M t i
  · rw [if_pos hM]
    rcases Nat.lt_or_ge (expDef M b t i) b with hlt | hge
    · rw [if_neg (by omega : ¬(M t i ∧ b ≤ expDef M b t i)), if_pos ⟨hM, hlt⟩, zero_add]
      exact toDist_wRun_le_expDef M b t i
    · rw [if_pos ⟨hM, hge⟩, if_neg (by omega : ¬(M t i ∧ expDef M b t i < b)), add_zero]
      have h := toDist_wRun_le_expDef M b t i
      rwa [le_antisymm (expDef_le M b t i) hge] at h
  · rw [if_neg hM, if_neg (by tauto), if_neg (by tauto), add_zero]

/-- The floor's own noise: at a step where the reference candidate hits, the saturated candidates
together carry at most `(C−1)/2^b`. The reference is what the erasure needs — a candidate that hits
is charged nothing, so realizability is not what makes this count work, only *some* hitter is. -/
private theorem sum_satCharge_le (M : ℕ → Fin C → Bool) (b t : ℕ) {i₀ : Fin C}
    (h₀ : M t i₀ = false) : (∑ i, satCharge M b t i) ≤ ((C : ℚ) - 1) * (1 / 2 : ℚ) ^ b := by
  have hC1 : 1 ≤ C := i₀.pos
  have h0 : satCharge M b t i₀ = 0 := by rw [satCharge, if_neg (by simp [h₀])]
  rw [← Finset.sum_erase Finset.univ h0]
  calc ∑ i ∈ Finset.univ.erase i₀, satCharge M b t i
      ≤ ∑ _i ∈ Finset.univ.erase i₀, (1 / 2 : ℚ) ^ b := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [satCharge]
        split
        · exact le_refl _
        · positivity
    _ = ((Finset.univ.erase i₀).card : ℚ) * (1 / 2 : ℚ) ^ b := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ = ((C : ℚ) - 1) * (1 / 2 : ℚ) ^ b := by
        rw [Finset.card_erase_of_mem (Finset.mem_univ i₀), Finset.card_univ, Fintype.card_fin,
          Nat.cast_sub hC1, Nat.cast_one]

/-! ### The tracking potential

The realizable argument's lifetime total was a geometric series: a candidate's miss count is
strictly monotone at every charged step, so it pays each charge at most once and the total is below
`2`. That argument is exactly what the reflection breaks — the clip discards debt beyond the
ceiling, so a candidate returns to a deficit it has already paid and the charge falls due again.

What survives is that a *re-payment* has to be paid for: each one needs the reference candidate's
exponent to have fallen back relative to the candidate's, and that happens only at a step where the
reference itself misses. The bookkeeping is a potential in the two exponents. `leadGap x y` is
`2 · 2 ^ −(x−y)` above the diagonal and `2 + (y−x)` below it — decreasing in `x − y`, `2` on the
diagonal, never negative. A step at which the reference hits and the candidate misses shifts `x − y`
up by one and so releases exactly the charge; a step at which the reference misses can push it back
down, at a cost of at most `1`. -/

private def leadGap (x y : ℕ) : ℚ := 2 * (1 / 2 : ℚ) ^ (x - y) + ((y - x : ℕ) : ℚ)

private theorem leadGap_nonneg (x y : ℕ) : 0 ≤ leadGap x y := by
  rw [leadGap]; positivity

private theorem leadGap_zero : leadGap 0 0 = 2 := by norm_num [leadGap]

private theorem leadGap_of_le_left {x y : ℕ} (h : y ≤ x) :
    leadGap x y = 2 * (1 / 2 : ℚ) ^ (x - y) := by
  rw [leadGap, Nat.sub_eq_zero_of_le h, Nat.cast_zero, add_zero]

private theorem leadGap_of_le_right {x y : ℕ} (h : x ≤ y) :
    leadGap x y = 2 + ((y - x : ℕ) : ℚ) := by
  rw [leadGap, Nat.sub_eq_zero_of_le h, pow_zero, mul_one]

/-- **The charge released by one step of the reference's advance.** Uniformly in the sign of the
difference: above the diagonal the potential halves its geometric part, below it the linear part
drops by one, and both are exactly `(1/2) ^ (x − y)` with the truncated subtraction. -/
private theorem leadGap_succ_left (x y : ℕ) :
    leadGap (x + 1) y + (1 / 2 : ℚ) ^ (x - y) = leadGap x y := by
  rcases Nat.lt_or_ge x y with h | h
  · rw [leadGap_of_le_right (by omega : x + 1 ≤ y), leadGap_of_le_right h.le,
      Nat.sub_eq_zero_of_le h.le, pow_zero]
    have hc : ((y - x : ℕ) : ℚ) = ((y - (x + 1) : ℕ) : ℚ) + 1 := by
      have h1 : y - x = (y - (x + 1)) + 1 := by omega
      rw [h1]; push_cast; ring
    rw [hc]; ring
  · rw [leadGap_of_le_left (by omega : y ≤ x + 1), leadGap_of_le_left h,
      show x + 1 - y = (x - y) + 1 from by omega, pow_succ]
    ring

private theorem leadGap_le_succ_left (x y : ℕ) : leadGap (x + 1) y ≤ leadGap x y := by
  have h := leadGap_succ_left x y
  have : (0 : ℚ) < (1 / 2 : ℚ) ^ (x - y) := by positivity
  linarith

private theorem leadGap_le_succ_left_add_one (x y : ℕ) :
    leadGap x y ≤ leadGap (x + 1) y + 1 := by
  have h := leadGap_succ_left x y
  have h1 : (1 / 2 : ℚ) ^ (x - y) ≤ 1 := by
    apply pow_le_one₀ <;> norm_num
  linarith

private theorem leadGap_shift (x y : ℕ) : leadGap (x + 1) (y + 1) = leadGap x y := by
  rw [leadGap, leadGap, Nat.succ_sub_succ, Nat.succ_sub_succ]

private theorem leadGap_mono_right (x y : ℕ) : leadGap x y ≤ leadGap x (y + 1) := by
  rcases Nat.lt_or_ge x (y + 1) with h | h
  · rw [leadGap_of_le_right (by omega : x ≤ y + 1)]
    rcases Nat.lt_or_ge x y with h2 | h2
    · rw [leadGap_of_le_right h2.le]
      have : ((y - x : ℕ) : ℚ) ≤ ((y + 1 - x : ℕ) : ℚ) := by
        exact_mod_cast Nat.sub_le_sub_right (Nat.le_succ y) x
      linarith
    · have hxy : x = y := by omega
      subst hxy
      rw [leadGap_of_le_left (le_refl x)]
      have : ((x + 1 - x : ℕ) : ℚ) = 1 := by
        rw [show x + 1 - x = 1 from by omega]; norm_num
      rw [this]
      norm_num
  · rw [leadGap_of_le_left (by omega : y ≤ x), leadGap_of_le_left h,
      show x - (y + 1) = x - y - 1 from by omega]
    have := pow_le_pow_of_le_one (a := (1 / 2 : ℚ)) (by norm_num) (by norm_num)
      (by omega : x - y - 1 ≤ x - y)
    linarith

private theorem leadGap_succ_right_le (x y : ℕ) : leadGap x (y + 1) ≤ leadGap x y + 1 := by
  rcases Nat.lt_or_ge y x with h | h
  · rw [leadGap_of_le_left (by omega : y + 1 ≤ x), leadGap_of_le_left h.le,
      show x - y = (x - (y + 1)) + 1 from by omega, pow_succ]
    have h1 : (1 / 2 : ℚ) ^ (x - (y + 1)) ≤ 1 := by
      apply pow_le_one₀ <;> norm_num
    linarith
  · rw [leadGap_of_le_right (by omega : x ≤ y + 1), leadGap_of_le_right h]
    have : ((y + 1 - x : ℕ) : ℚ) = ((y - x : ℕ) : ℚ) + 1 := by
      rw [show y + 1 - x = (y - x) + 1 from by omega]; push_cast; ring
    rw [this]; ring_nf; linarith

/-- The step at which the charge is released: the reference gains one exponent, the candidate gains
none, and the common rescale `d` cancels — provided it does not clip the candidate, which is what
`d ≤ y` asks. -/
private theorem leadGap_step_drop {x y q d : ℕ} (hq : q = 0) (hd1 : d ≤ 1) (hdy : d ≤ y) :
    leadGap ((x + 1) - d) ((y + q) - d) + (1 / 2 : ℚ) ^ (x - y) = leadGap x y := by
  subst hq
  simp only [Nat.add_zero]
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd
    simpa using leadGap_succ_left x y
  · have hd' : d = 1 := by omega
    subst hd'
    rw [show x + 1 - 1 = x from by omega]
    have hsh := leadGap_shift x (y - 1)
    rw [show y - 1 + 1 = y from by omega] at hsh
    rw [← hsh]
    exact leadGap_succ_left x y

/-- At a step where the reference hits, the potential cannot rise — whatever the candidate does, and
whether or not the rescale fires or the clip bites. -/
private theorem leadGap_step_le_of_hit {x y q d : ℕ} (hq : q ≤ 1) (hd1 : d ≤ 1) :
    leadGap ((x + 1) - d) ((y + q) - d) ≤ leadGap x y := by
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd
    simp only [Nat.sub_zero]
    rcases Nat.eq_zero_or_pos q with hq0 | hq1
    · subst hq0; simpa using leadGap_le_succ_left x y
    · rw [show q = 1 from by omega]
      exact le_of_eq (leadGap_shift x y)
  · have hd' : d = 1 := by omega
    subst hd'
    rw [show x + 1 - 1 = x from by omega]
    rcases Nat.eq_zero_or_pos q with hq0 | hq1
    · subst hq0
      rw [Nat.add_zero]
      rcases Nat.eq_zero_or_pos y with hy | hy
      · subst hy; simp
      · have h := leadGap_mono_right x (y - 1)
        rwa [show y - 1 + 1 = y from by omega] at h
    · rw [show q = 1 from by omega, show y + 1 - 1 = y from by omega]

/-- At any step the potential rises by at most `1`, and by `leadGap_step_le_of_hit` a rise needs the
reference to miss. -/
private theorem leadGap_step_le {x y p q d : ℕ} (hp : p ≤ 1) (hq : q ≤ 1) (hd1 : d ≤ 1) :
    leadGap ((x + p) - d) ((y + q) - d) ≤ leadGap x y + 1 := by
  rcases Nat.eq_zero_or_pos p with hp0 | hp1
  · subst hp0
    rw [Nat.add_zero]
    rcases Nat.eq_zero_or_pos d with hd | hd
    · subst hd
      simp only [Nat.sub_zero]
      rcases Nat.eq_zero_or_pos q with hq0 | hq1
      · subst hq0; simp
      · rw [show q = 1 from by omega]
        exact leadGap_succ_right_le x y
    · have hd' : d = 1 := by omega
      subst hd'
      rcases Nat.eq_zero_or_pos x with hx | hx
      · subst hx
        simp only [Nat.zero_sub]
        rcases Nat.eq_zero_or_pos (y + q) with h0 | hpos
        · rw [h0, show y = 0 from by omega]
          simp
        · refine le_trans (?_ : leadGap 0 (y + q - 1) ≤ leadGap 0 (y + q)) ?_
          · have h := leadGap_mono_right 0 (y + q - 1)
            rwa [show y + q - 1 + 1 = y + q from by omega] at h
          · rcases Nat.eq_zero_or_pos q with hq0 | hq1
            · subst hq0; simp
            · rw [show q = 1 from by omega]
              exact leadGap_succ_right_le 0 y
      · rcases Nat.eq_zero_or_pos q with hq0 | hq1
        · subst hq0
          rw [Nat.add_zero]
          rcases Nat.eq_zero_or_pos y with hy | hy
          · subst hy
            simp only [Nat.zero_sub]
            have h := leadGap_le_succ_left_add_one (x - 1) 0
            rwa [show x - 1 + 1 = x from by omega] at h
          · have hsh := leadGap_shift (x - 1) (y - 1)
            rw [show x - 1 + 1 = x from by omega, show y - 1 + 1 = y from by omega] at hsh
            rw [hsh]
            linarith
        · rw [show q = 1 from by omega, show y + 1 - 1 = y from by omega]
          have h := leadGap_le_succ_left_add_one (x - 1) y
          rwa [show x - 1 + 1 = x from by omega] at h
  · rw [show p = 1 from by omega]
    exact le_trans (leadGap_step_le_of_hit hq hd1) (by linarith)

/-- The potential of candidate `i` against the reference candidate `i₀`, along the run. -/
private def leadPot (M : ℕ → Fin C → Bool) (b : ℕ) (i₀ i : Fin C) (t : ℕ) : ℚ :=
  leadGap (expRun M b t i₀) (expRun M b t i)

private theorem leadPot_zero (M : ℕ → Fin C → Bool) (b : ℕ) (i₀ i : Fin C) :
    leadPot M b i₀ i 0 = 2 := by
  rw [leadPot]
  exact leadGap_zero

private theorem leadPot_nonneg (M : ℕ → Fin C → Bool) (b : ℕ) (i₀ i : Fin C) (t : ℕ) :
    0 ≤ leadPot M b i₀ i t := leadGap_nonneg _ _

private theorem leadPot_step_le_of_hit (M : ℕ → Fin C → Bool) (b : ℕ) (i₀ i : Fin C) (t : ℕ)
    (h₀ : M t i₀ = false) : leadPot M b i₀ i (t + 1) ≤ leadPot M b i₀ i t := by
  have hp1 : (if M t i₀ then (0 : ℕ) else 1) = 1 := if_neg (by simp [h₀])
  simp only [leadPot]
  change leadGap (expStep b (M t) (expRun M b t) i₀) (expStep b (M t) (expRun M b t) i) ≤ _
  rw [expStep, hp1]
  exact leadGap_step_le_of_hit (by split <;> omega) (by split <;> omega)

private theorem leadPot_step_le (M : ℕ → Fin C → Bool) (b : ℕ) (i₀ i : Fin C) (t : ℕ) :
    leadPot M b i₀ i (t + 1) ≤ leadPot M b i₀ i t + 1 := by
  simp only [leadPot]
  change leadGap (expStep b (M t) (expRun M b t) i₀) (expStep b (M t) (expRun M b t) i) ≤ _
  rw [expStep]
  exact leadGap_step_le (by split <;> omega) (by split <;> omega) (by split <;> omega)

/-- **Each charge is paid out of the potential.** At a step where the reference hits, the drop in
the potential covers the candidate's unsaturated charge: the deficit against the leader is at least
the deficit against the reference, so the charge is at most the released `(1/2) ^ (x − y)`, and the
clip cannot bite, an unsaturated candidate not being at the floor when the rescale fires. -/
private theorem unsatCharge_le_leadPot_sub (M : ℕ → Fin C → Bool) (b t : ℕ) (i₀ i : Fin C)
    (h₀ : M t i₀ = false) :
    unsatCharge M b t i ≤ leadPot M b i₀ i t - leadPot M b i₀ i (t + 1) := by
  rw [unsatCharge]
  by_cases hc : M t i ∧ expDef M b t i < b
  · rw [if_pos hc]
    obtain ⟨hi, hlt⟩ := hc
    have hdle : (if ∃ j, expRun M b t j = b ∧ M t j = false then 1 else 0)
        ≤ expRun M b t i := by
      split
      · rename_i hex
        obtain ⟨j, hj, -⟩ := hex
        have hjle : expRun M b t j ≤ expMax M b t := Finset.le_sup (Finset.mem_univ j)
        have hmax : expMax M b t = b := le_antisymm (expMax_le M b t) (by omega)
        rw [expDef, hmax] at hlt
        omega
      · omega
    have hp1 : (if M t i₀ then (0 : ℕ) else 1) = 1 := if_neg (by simp [h₀])
    have hq0 : (if M t i then (0 : ℕ) else 1) = 0 := if_pos hi
    have hstep : leadPot M b i₀ i (t + 1)
        + (1 / 2 : ℚ) ^ (expRun M b t i₀ - expRun M b t i) = leadPot M b i₀ i t := by
      simp only [leadPot]
      change leadGap (expStep b (M t) (expRun M b t) i₀) (expStep b (M t) (expRun M b t) i)
        + _ = _
      rw [expStep, hp1]
      exact leadGap_step_drop hq0 (by split <;> omega) hdle
    have hmono : (1 / 2 : ℚ) ^ expDef M b t i
        ≤ (1 / 2 : ℚ) ^ (expRun M b t i₀ - expRun M b t i) := by
      refine pow_le_pow_of_le_one (by norm_num) (by norm_num) ?_
      rw [expDef]
      exact Nat.sub_le_sub_right (Finset.le_sup (Finset.mem_univ i₀)) _
    linarith
  · rw [if_neg hc]
    have := leadPot_step_le_of_hit M b i₀ i t h₀
    linarith

/-- **The geometric total, against an arbitrary reference.** A candidate's unsaturated charges over
the steps at which the reference hits total at most `2` plus the reference's own miss count: the
potential starts at `2`, never goes negative, releases each charge, and rises only at a step where
the reference misses, by at most `1`. At a reference that never misses the second term vanishes and
this is the realizable geometric total. -/
private theorem sum_unsatCharge_le (M : ℕ → Fin C → Bool) (b : ℕ) (i₀ i : Fin C) (n : ℕ)
    {s : Finset ℕ} (hs : s ⊆ Finset.range n) (h₀ : ∀ t ∈ s, M t i₀ = false) :
    ∑ t ∈ s, unsatCharge M b t i ≤ 2 + (missCount M i₀ n : ℚ) := by
  have hgnn : ∀ t : ℕ, 0 ≤ leadPot M b i₀ i t - leadPot M b i₀ i (t + 1)
      + (if M t i₀ then (1 : ℚ) else 0) := by
    intro t
    by_cases h : M t i₀
    · rw [if_pos h]
      have := leadPot_step_le M b i₀ i t
      linarith
    · rw [if_neg h]
      have := leadPot_step_le_of_hit M b i₀ i t (by simpa using h)
      linarith
  have hle : ∀ t ∈ s, unsatCharge M b t i ≤ leadPot M b i₀ i t - leadPot M b i₀ i (t + 1)
      + (if M t i₀ then (1 : ℚ) else 0) := by
    intro t ht
    have hh := h₀ t ht
    rw [if_neg (by simp [hh]), add_zero]
    exact unsatCharge_le_leadPot_sub M b t i₀ i hh
  have hsplit : ∑ t ∈ Finset.range n, (leadPot M b i₀ i t - leadPot M b i₀ i (t + 1)
      + (if M t i₀ then (1 : ℚ) else 0))
      = (leadPot M b i₀ i 0 - leadPot M b i₀ i n) + (missCount M i₀ n : ℚ) := by
    rw [Finset.sum_add_distrib, Finset.sum_range_sub' (leadPot M b i₀ i) n, Finset.sum_boole,
      missCount]
  calc ∑ t ∈ s, unsatCharge M b t i
      ≤ ∑ t ∈ s, (leadPot M b i₀ i t - leadPot M b i₀ i (t + 1)
          + (if M t i₀ then (1 : ℚ) else 0)) := Finset.sum_le_sum hle
    _ ≤ ∑ t ∈ Finset.range n, (leadPot M b i₀ i t - leadPot M b i₀ i (t + 1)
          + (if M t i₀ then (1 : ℚ) else 0)) :=
        Finset.sum_le_sum_of_subset_of_nonneg hs fun t _ _ => hgnn t
    _ = (leadPot M b i₀ i 0 - leadPot M b i₀ i n) + (missCount M i₀ n : ℚ) := hsplit
    _ ≤ 2 + (missCount M i₀ n : ℚ) := by
        have h0 := leadPot_zero M b i₀ i
        have hn := leadPot_nonneg M b i₀ i n
        linarith

/-! ### The guard: below the budget threshold there is no `n`-free bound -/

/-- **The all-miss family**: every candidate but `iR` misses at every step. -/
def allMiss (iR : Fin C) : ℕ → Fin C → Bool := fun _ i => decide (i ≠ iR)

private theorem allMiss_truth (iR : Fin C) (t : ℕ) : allMiss iR t iR = false := by simp [allMiss]

private theorem missCount_allMiss {iR i : Fin C} (h : i ≠ iR) (t : ℕ) :
    missCount (allMiss iR) i t = t := by
  induction t with
  | zero => exact missCount_zero _ _
  | succ t ih => rw [missCount_succ, ih, if_pos (by simp [allMiss, h] : allMiss iR t i = true)]

/-- Under the all-miss family every competitor sits at the floor and the truth at the ceiling. -/
private theorem raw_wRun_allMiss (iR : Fin C) (b t : ℕ) (i : Fin C) :
    raw (wRun (2 ^ b) (missFit (allMiss iR)) t) i = if i = iR then 2 ^ min t b else 1 := by
  rw [wRun_eq_pow_deficit (allMiss iR) (allMiss_truth iR) b t i]
  by_cases h : i = iR
  · rw [if_pos h, h, missCount_eq_zero _ (allMiss_truth iR), Nat.sub_zero]
  · rw [if_neg h, missCount_allMiss h t,
      show min t b - t = 0 from Nat.sub_eq_zero_of_le (min_le_left t b), pow_zero]

/-- The wrong mass under the all-miss family, exactly: the competitors hold one quantum each
against the truth's `2 ^ min t b`. -/
private theorem wrongMass_allMiss (iR : Fin C) (b t : ℕ) :
    wrongMass (allMiss iR) b t = ((C : ℚ) - 1) / ((2 : ℚ) ^ min t b + ((C : ℚ) - 1)) := by
  have hC1 : 1 ≤ C := iR.pos
  have hcard : ((Finset.univ.erase iR).card : ℚ) = (C : ℚ) - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ iR), Finset.card_univ, Fintype.card_fin,
      Nat.cast_sub hC1, Nat.cast_one]
  have hwj : ∀ j, ((raw (wRun (2 ^ b) (missFit (allMiss iR)) t) j : ℕ) : ℚ)
      = if j = iR then (2 : ℚ) ^ min t b else 1 := by
    intro j
    rw [raw_wRun_allMiss iR b t j]
    split <;> push_cast <;> ring
  have hZ : ∑ j, ((raw (wRun (2 ^ b) (missFit (allMiss iR)) t) j : ℕ) : ℚ)
      = (2 : ℚ) ^ min t b + ((C : ℚ) - 1) := by
    simp only [hwj]
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ iR), if_pos rfl,
      Finset.sum_congr rfl (fun j hj => if_neg (Finset.ne_of_mem_erase hj)),
      Finset.sum_const, nsmul_eq_mul, mul_one, hcard]
    ring
  have hterm : ∀ j, (if allMiss iR t j then
      toDist (raw (wRun (2 ^ b) (missFit (allMiss iR)) t)) j else 0)
      = if j = iR then 0 else 1 / ((2 : ℚ) ^ min t b + ((C : ℚ) - 1)) := by
    intro j
    by_cases h : j = iR
    · rw [h, if_pos rfl]
      simp [allMiss_truth iR]
    · rw [if_neg h, if_pos (by simp [allMiss, h] : allMiss iR t j = true),
        show toDist (raw (wRun (2 ^ b) (missFit (allMiss iR)) t)) j
          = ((raw (wRun (2 ^ b) (missFit (allMiss iR)) t) j : ℕ) : ℚ)
            / ∑ k, ((raw (wRun (2 ^ b) (missFit (allMiss iR)) t) k : ℕ) : ℚ) from rfl,
        hZ, hwj j, if_neg h]
  rw [wrongMass]
  simp only [hterm]
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ iR), if_pos rfl, add_zero,
    Finset.sum_congr rfl (fun j hj => if_neg (Finset.ne_of_mem_erase hj)),
    Finset.sum_const, nsmul_eq_mul, hcard, mul_one_div]

/-- **The guard.** Below the budget threshold the `n`-free bound is *false*: on the all-miss family
every single step is a surprise, so the surprise count grows without bound. This is what makes
`floorSurprise_card_mul_le`'s budget hypothesis load-bearing rather than decorative — delete it and
this family refutes what remains. -/
theorem floorSurprises_unbounded_below_budget {iR : Fin C} (b : ℕ) (θ : ℚ)
    (hθ : θ * ((2 : ℚ) ^ b + ((C : ℚ) - 1)) < (C : ℚ) - 1) (n : ℕ) :
    (floorSurpriseSet (allMiss iR) b θ n).card = n := by
  have hC1 : 1 ≤ C := iR.pos
  have hCQ : (0 : ℚ) ≤ (C : ℚ) - 1 := by
    have : (1 : ℚ) ≤ (C : ℚ) := by exact_mod_cast hC1
    linarith
  rw [floorSurpriseSet, Finset.filter_true_of_mem, Finset.card_range]
  intro t _
  rw [wrongMass_allMiss iR b t]
  have hden : (0 : ℚ) < (2 : ℚ) ^ min t b + ((C : ℚ) - 1) := by positivity
  have hbig : (0 : ℚ) < (2 : ℚ) ^ b + ((C : ℚ) - 1) := by positivity
  have hle : (2 : ℚ) ^ min t b ≤ (2 : ℚ) ^ b :=
    pow_le_pow_right₀ (by norm_num) (min_le_right t b)
  rw [lt_div_iff₀ hden]
  nlinarith [hθ, hle, hCQ]

/-- **The refutation, concretely.** Three candidates, budget `2`, threshold `1/4`: every step is a
surprise, so no `n`-free bound on the surprise count exists — while the budget hypothesis of
`floorSurprise_card_mul_le` reads `4 ≤ 1/2` and fails. -/
theorem floorSurprises_unbounded_witness (n : ℕ) :
    (floorSurpriseSet (allMiss (0 : Fin 3)) 1 (1 / 4) n).card = n :=
  floorSurprises_unbounded_below_budget 1 (1 / 4) (by norm_num) n

/-! ### The guard on realizability: the event bound is *false* without it

The budget gate above is not the only load-bearing hypothesis. Realizability is too, and in the
stronger sense: the two families below satisfy the budget gate and still make **every** step a
surprise, so a lifetime-free right-hand side is unavailable in general — `floorSurprise_card_mul_le`
is not a theorem waiting for a weaker hypothesis.

The mechanism is the one `sum_unsatCharge_le_two` depends on. Its argument is that a candidate pays
each geometric charge at most once, its miss count being strictly monotone at every charged step.
Without a frozen leader the clip discards debt beyond the ceiling, a candidate returns to a deficit
it has already paid, and the same charge falls due again and again. Positively: the floor buys
*tracking* — the floored mixture follows the recent leader where the exact mixture aggregates all
history, which is why the exact-Bayes comparison is available only under realizability. -/

/-- The reading at two candidates, in terms of the exponents alone. -/
private theorem wrongMass_two (M : ℕ → Fin 2 → Bool) (b t : ℕ) :
    wrongMass M b t
      = ((if M t 0 then (2 : ℚ) ^ expRun M b t 0 else 0)
          + (if M t 1 then (2 : ℚ) ^ expRun M b t 1 else 0))
        / ((2 : ℚ) ^ expRun M b t 0 + (2 : ℚ) ^ expRun M b t 1) := by
  have hw : ∀ i : Fin 2, ((raw (wRun (2 ^ b) (missFit M) t) i : ℕ) : ℚ)
      = (2 : ℚ) ^ expRun M b t i := by
    intro i
    rw [wRun_eq_pow_expRun]
    push_cast
    ring
  have hsum : ∑ j, ((raw (wRun (2 ^ b) (missFit M) t) j : ℕ) : ℚ)
      = (2 : ℚ) ^ expRun M b t 0 + (2 : ℚ) ^ expRun M b t 1 := by
    rw [Fin.sum_univ_two, hw 0, hw 1]
  have hd : ∀ i : Fin 2, toDist (raw (wRun (2 ^ b) (missFit M) t)) i
      = (2 : ℚ) ^ expRun M b t i / ((2 : ℚ) ^ expRun M b t 0 + (2 : ℚ) ^ expRun M b t 1) := by
    intro i
    change ((raw (wRun (2 ^ b) (missFit M) t) i : ℕ) : ℚ)
      / ∑ j, ((raw (wRun (2 ^ b) (missFit M) t) j : ℕ) : ℚ) = _
    rw [hw i, hsum]
  rw [wrongMass, Fin.sum_univ_two, hd 0, hd 1]
  split <;> split <;> ring

/-- **The degenerate refuting family**: *every* candidate misses at *every* step. -/
def everyMiss (C : ℕ) : ℕ → Fin C → Bool := fun _ _ => true

/-- No candidate is realizable here — which is what puts the family outside
`floorSurprise_card_mul_le`'s hypothesis rather than in contradiction with it. -/
theorem everyMiss_not_realizable (C : ℕ) (i : Fin C) : ¬ (∀ t, everyMiss C t i = false) :=
  fun h => by simpa [everyMiss] using h 0

/-- Nobody ever hits, so the rescale never fires and the exponents never move: the weights stay at
the all-ones start forever. -/
theorem expRun_everyMiss (C b t : ℕ) (i : Fin C) : expRun (everyMiss C) b t i = 0 := by
  induction t with
  | zero => rfl
  | succ t ih =>
      change expStep b (everyMiss C t) (expRun (everyMiss C) b t) i = 0
      rw [expStep, if_pos (show everyMiss C t i = true from rfl), ih]
      simp

theorem raw_wRun_everyMiss (C b t : ℕ) (i : Fin C) :
    raw (wRun (2 ^ b) (missFit (everyMiss C)) t) i = 1 := by
  rw [wRun_eq_pow_expRun, expRun_everyMiss, pow_zero]

/-- **The wrong mass is exactly `1` at every step**, whatever the budget. Every candidate misses, so
the whole uniform reading sits on candidates that are wrong. -/
theorem wrongMass_everyMiss {C : ℕ} [NeZero C] (b t : ℕ) : wrongMass (everyMiss C) b t = 1 := by
  have hCpos : (0 : ℚ) < (C : ℚ) := by
    have : 0 < C := Nat.pos_of_ne_zero (NeZero.ne C)
    exact_mod_cast this
  have hw : ∀ j : Fin C, ((raw (wRun (2 ^ b) (missFit (everyMiss C)) t) j : ℕ) : ℚ) = 1 := by
    intro j
    rw [raw_wRun_everyMiss]
    norm_num
  have hZ : ∑ j, ((raw (wRun (2 ^ b) (missFit (everyMiss C)) t) j : ℕ) : ℚ) = (C : ℚ) := by
    rw [Finset.sum_congr rfl (fun j _ => hw j), Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_one]
  have hterm : ∀ j : Fin C,
      (if everyMiss C t j then toDist (raw (wRun (2 ^ b) (missFit (everyMiss C)) t)) j else 0)
        = 1 / (C : ℚ) := by
    intro j
    rw [if_pos (show everyMiss C t j = true from rfl)]
    change ((raw (wRun (2 ^ b) (missFit (everyMiss C)) t) j : ℕ) : ℚ)
      / ∑ k, ((raw (wRun (2 ^ b) (missFit (everyMiss C)) t) k : ℕ) : ℚ) = _
    rw [hw j, hZ]
  rw [wrongMass, Finset.sum_congr rfl (fun j _ => hterm j), Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one_div, div_self hCpos.ne']

/-- **`wrongMass_lt_one`'s hypothesis is not decorative either**, and its honest general form is
*per-step*: the wrong mass reaches `1` exactly when the observation lies outside the candidates'
span at that step. See `wrongMass_lt_one_of_hit` for the repair. -/
theorem wrongMass_everyMiss_not_lt_one {C : ℕ} [NeZero C] (b t : ℕ) :
    ¬ wrongMass (everyMiss C) b t < 1 := by
  rw [wrongMass_everyMiss]
  exact lt_irrefl 1

/-- **The event bound is refutable without realizability.** On the every-candidate-misses family the
wrong mass is `1` at every step, so for any threshold below `1` the surprise count equals the
horizon — and the budget gate is untouched, being a condition on `θ`, `C` and `b` alone. -/
theorem floorSurprises_unbounded_everyMiss {C : ℕ} [NeZero C] (b : ℕ) {θ : ℚ} (hθ : θ < 1)
    (n : ℕ) : (floorSurpriseSet (everyMiss C) b θ n).card = n := by
  rw [floorSurpriseSet, Finset.filter_true_of_mem, Finset.card_range]
  intro t _
  rw [wrongMass_everyMiss]
  exact hθ

/-- **The refutation, concretely and hand-checkably.** Two candidates, `θ = 1/2`, budget `2^3`: the
gate `2(C−1) ≤ θ·2^b` reads `2 ≤ 4` and **holds**, yet over a horizon of `16` steps the surprise
count times the threshold is `8`, twice `floorSurprise_card_mul_le`'s `4(C−1) = 4`. So realizability
is load-bearing in that theorem, not slack. -/
theorem floorSurprise_card_mul_gt_everyMiss_witness :
    2 * (((2 : ℕ) : ℚ) - 1) ≤ (1 / 2 : ℚ) * 2 ^ 3 ∧
      4 * (((2 : ℕ) : ℚ) - 1)
        < ((floorSurpriseSet (everyMiss 2) 3 (1 / 2) 16).card : ℚ) * (1 / 2 : ℚ) := by
  refine ⟨by norm_num, ?_⟩
  rw [floorSurprises_unbounded_everyMiss 3 (by norm_num) 16]
  norm_num

/-- **The non-degenerate refuting family**: two candidates missing alternately, so each hits exactly
half the time. Candidate `i` misses at the steps `t` with `t % 2 = i`. -/
def altMiss : ℕ → Fin 2 → Bool := fun t i => decide ((i : ℕ) = t % 2)

/-- Neither candidate is realizable: each misses at every other step. -/
theorem altMiss_not_realizable (i : Fin 2) : ¬ (∀ t, altMiss t i = false) := by
  intro h
  have := h (i : ℕ)
  simp only [altMiss, decide_eq_false_iff_not] at this
  omega

/-- The alternating family's exponents in closed form. They climb in step to the ceiling and then
cycle: at even times both candidates sit at `min (t/2) b`, at odd times the hitter is one doubling
ahead. The `b − t % 2` on the first coordinate is the reflection — the candidate the rescale charges
drops back below the ceiling and climbs again on its next hit. -/
theorem expRun_altMiss (b t : ℕ) :
    expRun altMiss b t 0 = min (t / 2) (b - t % 2)
      ∧ expRun altMiss b t 1 = min ((t + 1) / 2) b := by
  induction t with
  | zero => exact ⟨by simp [expRun], by simp [expRun]⟩
  | succ t ih =>
      obtain ⟨ih0, ih1⟩ := ih
      rcases (by omega : t % 2 = 0 ∨ t % 2 = 1) with hr | hr
      · -- an even step: candidate `0` misses, candidate `1` hits, so the hitter drives the rescale
        have hm0 : altMiss t 0 = true := by simp [altMiss, hr]
        have hm1 : altMiss t 1 = false := by simp [altMiss, hr]
        have hδ : (∃ j : Fin 2, expRun altMiss b t j = b ∧ altMiss t j = false)
            ↔ b ≤ t / 2 := by
          rw [Fin.exists_fin_two]
          simp [hm0, hm1, ih1]
          omega
        have hstep : ∀ i : Fin 2, expStep b (altMiss t) (expRun altMiss b t) i
            = (expRun altMiss b t i + (if altMiss t i then 0 else 1))
              - (if b ≤ t / 2 then 1 else 0) := by
          intro i
          rw [expStep]
          congr 1
          by_cases h : b ≤ t / 2
          · rw [if_pos h, if_pos (hδ.mpr h)]
          · rw [if_neg h, if_neg (fun hh => h (hδ.mp hh))]
        clear hδ
        refine ⟨?_, ?_⟩
        · change expStep b (altMiss t) (expRun altMiss b t) 0 = _
          rw [hstep 0, if_pos hm0, ih0]
          split <;> omega
        · change expStep b (altMiss t) (expRun altMiss b t) 1 = _
          rw [hstep 1, if_neg (by simp [hm1]), ih1]
          split <;> omega
      · -- an odd step: candidate `1` misses, candidate `0` hits, and it is below the ceiling
        have hm0 : altMiss t 0 = false := by simp [altMiss, hr]
        have hm1 : altMiss t 1 = true := by simp [altMiss, hr]
        have hδ : (∃ j : Fin 2, expRun altMiss b t j = b ∧ altMiss t j = false)
            ↔ b = 0 := by
          rw [Fin.exists_fin_two]
          simp [hm0, hm1, ih0, hr]
          omega
        have hstep : ∀ i : Fin 2, expStep b (altMiss t) (expRun altMiss b t) i
            = (expRun altMiss b t i + (if altMiss t i then 0 else 1))
              - (if b = 0 then 1 else 0) := by
          intro i
          rw [expStep]
          congr 1
          by_cases h : b = 0
          · rw [if_pos h, if_pos (hδ.mpr h)]
          · rw [if_neg h, if_neg (fun hh => h (hδ.mp hh))]
        clear hδ
        refine ⟨?_, ?_⟩
        · change expStep b (altMiss t) (expRun altMiss b t) 0 = _
          rw [hstep 0, if_neg (by simp [hm0]), ih0]
          split <;> omega
        · change expStep b (altMiss t) (expRun altMiss b t) 1 = _
          rw [hstep 1, if_pos hm1, ih1]
          split <;> omega

/-- **The wrong mass never drops below `1/2`**, at any budget and any time. At even steps the two
candidates are level and the misser holds exactly half the mass; at odd steps the misser is the one
that just hit, so it holds at least half. -/
theorem wrongMass_altMiss_ge (b t : ℕ) : (1 / 2 : ℚ) ≤ wrongMass altMiss b t := by
  obtain ⟨h0, h1⟩ := expRun_altMiss b t
  rw [wrongMass_two]
  rcases (by omega : t % 2 = 0 ∨ t % 2 = 1) with hr | hr
  · have hm0 : altMiss t 0 = true := by simp [altMiss, hr]
    have hm1 : altMiss t 1 = false := by simp [altMiss, hr]
    have heq : expRun altMiss b t 0 = expRun altMiss b t 1 := by rw [h0, h1]; omega
    rw [if_pos hm0, if_neg (by simp [hm1]), heq, le_div_iff₀ (by positivity)]
    have : (0 : ℚ) < (2 : ℚ) ^ expRun altMiss b t 1 := by positivity
    linarith
  · have hm0 : altMiss t 0 = false := by simp [altMiss, hr]
    have hm1 : altMiss t 1 = true := by simp [altMiss, hr]
    have hle : expRun altMiss b t 0 ≤ expRun altMiss b t 1 := by rw [h0, h1]; omega
    have hpow : (2 : ℚ) ^ expRun altMiss b t 0 ≤ (2 : ℚ) ^ expRun altMiss b t 1 :=
      pow_le_pow_right₀ (by norm_num) hle
    rw [if_neg (by simp [hm0]), if_pos hm1, le_div_iff₀ (by positivity)]
    linarith

/-- **The refutation without the degeneracy.** Each candidate hits half the time, so the family is
not open to the objection that nobody ever learns anything — and still every step is a surprise for
any threshold below `1/2`. -/
theorem floorSurprises_unbounded_altMiss (b : ℕ) {θ : ℚ} (hθ : θ < 1 / 2) (n : ℕ) :
    (floorSurpriseSet altMiss b θ n).card = n := by
  rw [floorSurpriseSet, Finset.filter_true_of_mem, Finset.card_range]
  intro t _
  exact lt_of_lt_of_le hθ (wrongMass_altMiss_ge b t)

/-- **The non-degenerate refutation, concretely.** Two candidates, budget `2^6`, threshold
`θ = 4/2^6`: the gate reads `2 ≤ 4` and holds, and over `128` steps the surprise count times the
threshold is `8`, twice `floorSurprise_card_mul_le`'s `4(C−1) = 4`. -/
theorem floorSurprise_card_mul_gt_altMiss_witness :
    2 * (((2 : ℕ) : ℚ) - 1) ≤ (4 / 2 ^ 6 : ℚ) * 2 ^ 6 ∧
      4 * (((2 : ℕ) : ℚ) - 1)
        < ((floorSurpriseSet altMiss 6 (4 / 2 ^ 6) 128).card : ℚ) * (4 / 2 ^ 6 : ℚ) := by
  refine ⟨by norm_num, ?_⟩
  rw [floorSurprises_unbounded_altMiss 6 (by norm_num) 128]
  norm_num

/-! ### The event bound, gated by the budget -/

/-- The core of the count, over an arbitrary set of steps at which the reference candidate hits and
the wrong mass exceeds the threshold. Splitting it out keeps the two accountings apart: the steps at
which the reference itself misses are counted directly against its miss count, and everything else
is this. -/
private theorem card_mul_le_of_hitting_surprises (M : ℕ → Fin C → Bool) (b : ℕ) (θ : ℚ)
    (hbudget : 2 * ((C : ℚ) - 1) ≤ θ * 2 ^ b) (i₀ : Fin C) (n : ℕ) {s : Finset ℕ}
    (hs : s ⊆ Finset.range n) (hhit : ∀ t ∈ s, M t i₀ = false)
    (hsurp : ∀ t ∈ s, θ < wrongMass M b t) :
    (s.card : ℚ) * θ ≤ 2 * (((C : ℚ) - 1) * (2 + (missCount M i₀ n : ℚ))) := by
  have hC1 : 1 ≤ C := i₀.pos
  have hCQ : (0 : ℚ) ≤ (C : ℚ) - 1 := by
    have : (1 : ℚ) ≤ (C : ℚ) := by exact_mod_cast hC1
    linarith
  have hpow : (0 : ℚ) < (2 : ℚ) ^ b := by positivity
  have hsat : ∀ t ∈ s, (∑ i, satCharge M b t i) ≤ θ / 2 := by
    intro t ht
    refine le_trans (sum_satCharge_le M b t (hhit t ht)) ?_
    rw [div_pow, one_pow, mul_one_div, div_le_div_iff₀ hpow (by norm_num : (0:ℚ) < 2)]
    linarith
  have hstep : ∀ t ∈ s, θ / 2 ≤ ∑ i, unsatCharge M b t i := by
    intro t ht
    have h1 := wrongMass_le_charges M b t
    have h2 := hsat t ht
    have h3 := hsurp t ht
    linarith
  have h0 : ∑ t ∈ s, unsatCharge M b t i₀ = 0 :=
    Finset.sum_eq_zero fun t ht => by rw [unsatCharge, if_neg (by simp [hhit t ht])]
  have hunsat : ∑ i, ∑ t ∈ s, unsatCharge M b t i
      ≤ ((C : ℚ) - 1) * (2 + (missCount M i₀ n : ℚ)) := by
    rw [← Finset.sum_erase (f := fun i => ∑ t ∈ s, unsatCharge M b t i) Finset.univ h0]
    calc ∑ i ∈ Finset.univ.erase i₀, ∑ t ∈ s, unsatCharge M b t i
        ≤ ∑ _i ∈ Finset.univ.erase i₀, (2 + (missCount M i₀ n : ℚ)) :=
          Finset.sum_le_sum fun i _ => sum_unsatCharge_le M b i₀ i n hs hhit
      _ = ((C : ℚ) - 1) * (2 + (missCount M i₀ n : ℚ)) := by
          rw [Finset.sum_const, nsmul_eq_mul, Finset.card_erase_of_mem (Finset.mem_univ i₀),
            Finset.card_univ, Fintype.card_fin, Nat.cast_sub hC1, Nat.cast_one]
  have hmain : (s.card : ℚ) * (θ / 2) ≤ ((C : ℚ) - 1) * (2 + (missCount M i₀ n : ℚ)) := by
    calc (s.card : ℚ) * (θ / 2)
        = ∑ _t ∈ s, θ / 2 := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ t ∈ s, ∑ i, unsatCharge M b t i := Finset.sum_le_sum hstep
      _ = ∑ i, ∑ t ∈ s, unsatCharge M b t i := Finset.sum_comm
      _ ≤ _ := hunsat
  linarith

/-- **The floored event bound, agnostic.** Once the budget clears the surprise threshold
(`2(C−1) ≤ θ·2^b`), the steps at which the floored mixture's wrong mass exceeds `θ` are bounded over
the whole run by a right-hand side that mentions the horizon only through **one** candidate's miss
count — and that candidate is arbitrary, quantified over the whole pool rather than chosen as an
argmin. The horizon never occurs on the right by itself, the same product-form presentation as
`BayesRedundancy.surprise_card_mul_le`; a consumer instantiates at whichever candidate misses least.

This is the mixture-currency instance of the agnostic weighted-majority bound: Littlestone &
Warmuth, *The weighted majority algorithm*, Information and Computation **108** (1994), Corollary
2.1 and §3 (WML), whose floored variant already carries a tracking bound of this shape. What is
proved here rather than imported is the exact constant on the quantized power-of-two carrier — where
the floor is the budget projection's own clip rather than a weight threshold applied by hand —
together with the specialization to the realizable regime, `floorSurprise_card_mul_le` being this
bound read at a never-missing reference.

Three accountings meet. The floor's own noise is uniformly sub-threshold at a step where the
reference hits: the saturated candidates together carry at most `(C−1)/2^b ≤ θ/2`, so they can never
complete a surprise on their own, which is exactly what the budget hypothesis buys — and
`floorSurprises_unbounded_below_budget` shows that without it the conclusion is false rather than
unproved. The surplus therefore comes from candidates still inside the budget, and their charges
are paid out of `leadPot`, which only the reference's own misses refill. The steps at which the
reference itself misses carry no charge at all: they are counted directly, one per miss.

The miss-count coefficient is `2C`, where a share-potential argument in the logarithm gives one
free of `C`. That `C` is the price of an additive accounting in ℚ: each of the `C−1` competitors
keeps its own potential, and a single miss of the reference can refill all of them at once. The
families below read in the other direction and force the coefficient to be at least `θ`, and at
least `2θ` on the alternating family, so what separates the proved constant from a necessary one is
a factor in `C` rather than the shape. -/
theorem floorSurprise_card_mul_le_missCount (M : ℕ → Fin C → Bool) (b : ℕ) (θ : ℚ)
    (hbudget : 2 * ((C : ℚ) - 1) ≤ θ * 2 ^ b) (i₀ : Fin C) (n : ℕ) :
    ((floorSurpriseSet M b θ n).card : ℚ) * θ
      ≤ 4 * ((C : ℚ) - 1) + 2 * (C : ℚ) * (missCount M i₀ n : ℚ) := by
  have hC1 : 1 ≤ C := i₀.pos
  have hCQ : (0 : ℚ) ≤ (C : ℚ) - 1 := by
    have : (1 : ℚ) ≤ (C : ℚ) := by exact_mod_cast hC1
    linarith
  have hpow : (0 : ℚ) < (2 : ℚ) ^ b := by positivity
  have hmQ : (0 : ℚ) ≤ (missCount M i₀ n : ℚ) := by positivity
  by_cases hθ1 : (1 : ℚ) ≤ θ
  · have hempty : floorSurpriseSet M b θ n = ∅ := by
      rw [floorSurpriseSet, Finset.filter_eq_empty_iff]
      intro t _
      exact not_lt.mpr (le_trans (wrongMass_le_one M b t) hθ1)
    rw [hempty, Finset.card_empty, Nat.cast_zero, zero_mul]
    have hnn : (0 : ℚ) ≤ 2 * (C : ℚ) * (missCount M i₀ n : ℚ) := by positivity
    linarith
  · replace hθ1 : θ < 1 := not_le.mp hθ1
    have hθ0 : (0 : ℚ) ≤ θ := by
      by_contra hneg
      have := mul_neg_of_neg_of_pos (not_le.mp hneg) hpow
      linarith
    have hsub : floorSurpriseSet M b θ n ⊆ Finset.range n := by
      rw [floorSurpriseSet]
      exact Finset.filter_subset _ _
    have hmem : ∀ t ∈ floorSurpriseSet M b θ n, θ < wrongMass M b t := by
      intro t ht
      rw [floorSurpriseSet, Finset.mem_filter] at ht
      exact ht.2
    have hcore := card_mul_le_of_hitting_surprises M b θ hbudget i₀ n
      (fun t ht => hsub (Finset.mem_filter.mp ht).1)
      (fun t ht => (Finset.mem_filter.mp ht).2)
      (fun t ht => hmem t (Finset.mem_filter.mp ht).1)
    have hmiss : ((floorSurpriseSet M b θ n).filter fun t => ¬ (M t i₀ = false)).card
        ≤ missCount M i₀ n := by
      rw [missCount]
      refine Finset.card_le_card fun t ht => ?_
      rw [Finset.mem_filter] at ht ⊢
      exact ⟨hsub ht.1, by simpa using ht.2⟩
    have hmissQ : (((floorSurpriseSet M b θ n).filter fun t => ¬ (M t i₀ = false)).card : ℚ)
        ≤ (missCount M i₀ n : ℚ) := by exact_mod_cast hmiss
    have hmissθ : (((floorSurpriseSet M b θ n).filter fun t => ¬ (M t i₀ = false)).card : ℚ) * θ
        ≤ (missCount M i₀ n : ℚ) := by
      calc (((floorSurpriseSet M b θ n).filter fun t => ¬ (M t i₀ = false)).card : ℚ) * θ
          ≤ (missCount M i₀ n : ℚ) * θ := mul_le_mul_of_nonneg_right hmissQ hθ0
        _ ≤ (missCount M i₀ n : ℚ) * 1 := mul_le_mul_of_nonneg_left hθ1.le hmQ
        _ = _ := mul_one _
    have hcard : ((floorSurpriseSet M b θ n).filter fun t => M t i₀ = false).card
        + ((floorSurpriseSet M b θ n).filter fun t => ¬ (M t i₀ = false)).card
        = (floorSurpriseSet M b θ n).card :=
      Finset.card_filter_add_card_filter_not _
    have hcardQ : ((floorSurpriseSet M b θ n).card : ℚ)
        = (((floorSurpriseSet M b θ n).filter fun t => M t i₀ = false).card : ℚ)
          + (((floorSurpriseSet M b θ n).filter fun t => ¬ (M t i₀ = false)).card : ℚ) := by
      rw [← hcard]
      push_cast
      ring
    rw [hcardQ, add_mul]
    nlinarith [hcore, hmissθ, hmQ, hCQ]

/-- **The floored event bound in the realizable regime** — the agnostic bound above read at a
candidate that never misses, whose miss count is `0` at every horizon, so the right-hand side is
free of the horizon altogether: at most `4(C−1)/θ` surprises over the whole run, `n` occurring only
inside the surprise set. This is the form [Inevitability] §6 consumes. The families below show that
realizability cannot simply be dropped *from this statement*: what replaces it is the tracking form
above, not a weaker hypothesis. -/
theorem floorSurprise_card_mul_le (M : ℕ → Fin C → Bool) {iR : Fin C} (hR : ∀ t, M t iR = false)
    (b : ℕ) (θ : ℚ) (hbudget : 2 * ((C : ℚ) - 1) ≤ θ * 2 ^ b) (n : ℕ) :
    ((floorSurpriseSet M b θ n).card : ℚ) * θ ≤ 4 * ((C : ℚ) - 1) := by
  have h := floorSurprise_card_mul_le_missCount M b θ hbudget iR n
  rw [missCount_eq_zero M hR n] at h
  simpa using h

/-! ### Sharpness: the refutation families read against the tracking bound

The families that refute the lifetime-free count are *inside* the tracking bound's hypotheses — it
asks nothing of them — so they read there as sharpness witnesses rather than refutations. Both of
the two below pin the miss-count term from the other side: it cannot be dropped, its coefficient
cannot fall below `θ` in general, and on the alternating family not below `2θ`. `mirrorMiss` is
covered by the tracking bound too, unconditionally; what that family says is
`toDist_wRun_sub_bayesRun_not_le_mirrorMiss`, about accumulation against exact Bayes, and no
tracking form of *that* is attempted here. -/

/-- Every candidate misses at every step, so each one's miss count is the horizon. -/
theorem missCount_everyMiss (C : ℕ) (i : Fin C) (n : ℕ) : missCount (everyMiss C) i n = n := by
  induction n with
  | zero => exact missCount_zero _ _
  | succ n ih => rw [missCount_succ, ih, if_pos (show everyMiss C n i = true from rfl)]

/-- **Sharpness on `everyMiss`: the miss-count term is necessary, and its coefficient cannot go
below `θ`.** Every candidate misses at every step, so the surprise count *is* the horizon and *is*
every candidate's miss count. Any `κ` for which `card · θ ≤ 4(C−1) + κ · missCount i₀ n` holds at
every horizon therefore satisfies `θ ≤ κ`: at `κ = 0` this is
`floorSurprise_card_mul_gt_everyMiss_witness`'s refutation of the lifetime-free form, and
`floorSurprise_card_mul_le_missCount` supplies `κ = 2C`. -/
theorem le_of_card_mul_le_missCount_everyMiss {C : ℕ} [NeZero C] (b : ℕ) {θ κ : ℚ} (hθ : θ < 1)
    (_hbudget : 2 * ((C : ℚ) - 1) ≤ θ * 2 ^ b) (i₀ : Fin C)
    (h : ∀ n, ((floorSurpriseSet (everyMiss C) b θ n).card : ℚ) * θ
      ≤ 4 * ((C : ℚ) - 1) + κ * (missCount (everyMiss C) i₀ n : ℚ)) : θ ≤ κ := by
  by_contra hlt
  have hd : (0 : ℚ) < θ - κ := by
    have := not_le.mp hlt
    linarith
  obtain ⟨N, hN⟩ := exists_nat_gt (4 * ((C : ℚ) - 1) / (θ - κ))
  have hk := h N
  rw [floorSurprises_unbounded_everyMiss b hθ N, missCount_everyMiss] at hk
  rw [div_lt_iff₀ hd] at hN
  linarith

/-- Candidate `0` of the alternating family misses at the even steps: its miss count is `⌈n/2⌉`. -/
theorem missCount_altMiss_zero (n : ℕ) : missCount altMiss 0 n = (n + 1) / 2 := by
  induction n with
  | zero => rw [missCount_zero]
  | succ n ih =>
      rw [missCount_succ, ih]
      by_cases h : n % 2 = 0
      · rw [if_pos (show altMiss n 0 = true by simp [altMiss, h])]
        omega
      · rw [if_neg (show ¬ (altMiss n 0 = true) by simp [altMiss]; omega)]
        omega

/-- **Sharpness on `altMiss`: the coefficient cannot fall below `2θ`.** Two candidates missing
alternately: every step is a surprise for any threshold below `1/2`, while each candidate misses
only half the time, so the horizon enters the left side at full rate and the right at half. Any `κ`
for which the tracking bound holds at every horizon therefore satisfies `2θ ≤ κ`, and as `θ`
approaches `1/2` that forces `κ ≥ 1`. So the coefficient `2C` of
`floorSurprise_card_mul_le_missCount` is within a factor of `C` of necessary, not of a different
shape. -/
theorem two_mul_le_of_card_mul_le_missCount_altMiss (b : ℕ) {θ κ : ℚ} (hθ : θ < 1 / 2)
    (_hbudget : 2 * (((2 : ℕ) : ℚ) - 1) ≤ θ * 2 ^ b)
    (h : ∀ n, ((floorSurpriseSet altMiss b θ n).card : ℚ) * θ
      ≤ 4 * (((2 : ℕ) : ℚ) - 1) + κ * (missCount altMiss 0 n : ℚ)) : 2 * θ ≤ κ := by
  by_contra hlt
  have hd : (0 : ℚ) < 2 * θ - κ := by
    have := not_le.mp hlt
    linarith
  obtain ⟨K, hK⟩ := exists_nat_gt (4 / (2 * θ - κ))
  have hk := h (2 * K)
  rw [floorSurprises_unbounded_altMiss b hθ (2 * K), missCount_altMiss_zero,
    show (2 * K + 1) / 2 = K from by omega] at hk
  rw [div_lt_iff₀ hd] at hK
  push_cast at hk
  linarith

/-! ### Reconciliation: where the budget hypothesis leaves the bound silent -/

/-- **The wrong mass stays below `1`, and the honest hypothesis is per-step.** Some candidate
hitting *at that step* — the observation lying inside the candidates' span there — is enough, and it
is also necessary: `wrongMass_everyMiss` puts the mass at exactly `1` when nobody hits. Every
weight is a power of two by `wRun_eq_pow_expRun`, so the hitter's own mass is positive and
unaccounted for. -/
theorem wrongMass_lt_one_of_hit (M : ℕ → Fin C → Bool) (b t : ℕ) {i₀ : Fin C}
    (h₀ : M t i₀ = false) : wrongMass M b t < 1 := by
  have hwpos : ∀ i, (0 : ℚ) < ((raw (wRun (2 ^ b) (missFit M) t) i : ℕ) : ℚ) := by
    intro i
    rw [wRun_eq_pow_expRun M b t i]
    positivity
  have hZ : (0 : ℚ) < ∑ j, ((raw (wRun (2 ^ b) (missFit M) t) j : ℕ) : ℚ) :=
    Finset.sum_pos (fun j _ => hwpos j) ⟨i₀, Finset.mem_univ i₀⟩
  have h0 : (if M t i₀ then toDist (raw (wRun (2 ^ b) (missFit M) t)) i₀ else 0) = 0 :=
    if_neg (by simp [h₀])
  have hsplit := Finset.sum_erase_add Finset.univ
    (fun i => ((raw (wRun (2 ^ b) (missFit M) t) i : ℕ) : ℚ)) (Finset.mem_univ i₀)
  calc wrongMass M b t
      = ∑ i ∈ Finset.univ.erase i₀,
          (if M t i then toDist (raw (wRun (2 ^ b) (missFit M) t)) i else 0) := by
        rw [wrongMass, ← Finset.sum_erase
          (f := fun i => if M t i then toDist (raw (wRun (2 ^ b) (missFit M) t)) i else 0)
          Finset.univ h0]
    _ ≤ ∑ i ∈ Finset.univ.erase i₀, ((raw (wRun (2 ^ b) (missFit M) t) i : ℕ) : ℚ)
          / ∑ j, ((raw (wRun (2 ^ b) (missFit M) t) j : ℕ) : ℚ) := by
        refine Finset.sum_le_sum fun i _ => ?_
        split
        · exact le_of_eq rfl
        · positivity
    _ = (∑ i ∈ Finset.univ.erase i₀, ((raw (wRun (2 ^ b) (missFit M) t) i : ℕ) : ℚ))
          / ∑ j, ((raw (wRun (2 ^ b) (missFit M) t) j : ℕ) : ℚ) := by
        simp_rw [div_eq_mul_inv]
        rw [← Finset.sum_mul]
    _ < 1 := by
        rw [div_lt_one hZ]
        linarith [hwpos i₀]

/-- The truth always retains mass, so the wrong mass never reaches `1`. Realizability is more than
this needs — `wrongMass_lt_one_of_hit` asks only that *someone* hits at the step in question. -/
theorem wrongMass_lt_one (M : ℕ → Fin C → Bool) {iR : Fin C} (hR : ∀ t, M t iR = false)
    (b t : ℕ) : wrongMass M b t < 1 :=
  wrongMass_lt_one_of_hit M b t (hR t)

/-- Above threshold `1` there are no surprises at all: the wrong mass cannot get there. -/
theorem floorSurpriseSet_eq_empty_of_one_le (M : ℕ → Fin C → Bool) {iR : Fin C}
    (hR : ∀ t, M t iR = false) (b : ℕ) {θ : ℚ} (hθ : 1 ≤ θ) (n : ℕ) :
    floorSurpriseSet M b θ n = ∅ := by
  rw [floorSurpriseSet, Finset.filter_eq_empty_iff]
  intro t _
  exact not_lt.mpr (le_trans (le_of_lt (wrongMass_lt_one M hR b t)) hθ)

/-- **The event bound's own vacuity zone.** At `C = W = 2` — `weighted_fiber_not_exactly_bayes`'s
instance — the budget hypothesis already forces `θ ≥ 1`, where no wrong mass can reach the
threshold and the surprise set is empty for every horizon. So the annihilating instance and the
event bound occupy disjoint budgets rather than contradicting each other, exactly as
`toDist_sub_le_two` reconciled that instance with the per-step rate. -/
theorem floorSurprise_vacuous_at_badW_budget {M : ℕ → Fin 2 → Bool} {iR : Fin 2}
    (hR : ∀ t, M t iR = false) {θ : ℚ} (hbudget : 2 * (((2 : ℕ) : ℚ) - 1) ≤ θ * 2 ^ 1) (n : ℕ) :
    floorSurpriseSet M 1 θ n = ∅ :=
  floorSurpriseSet_eq_empty_of_one_le M hR 1 (by push_cast at hbudget; linarith) n

/-- **The annihilated update is the clip in action.** `weighted_fiber_not_exactly_bayes`'s
two-candidate, budget-`2` instance is the all-miss family at `b = 1`: from step `1` onwards the
floored run sits at `badW = (2,1)` forever, the competitor's every miss absorbed by the floor.
`badProject` is that fixed point exhibited one step at a time; the normal form gives it for all
`t ≥ 1` at once. -/
theorem raw_wRun_allMiss_eq_badW {t : ℕ} (ht : 1 ≤ t) :
    raw (wRun (2 ^ 1) (missFit (allMiss (0 : Fin 2))) t) = badW := by
  funext i
  rw [raw_wRun_allMiss (0 : Fin 2) 1 t i, min_eq_right ht]
  fin_cases i <;> simp [badW]

end Event

/-! ## The accumulated residual -/

section Accumulation

variable {C : ℕ}

/-- **Normalization forgets a common scalar.** The reading depends on the weight vector only
through its ray, so scaling every coordinate by the same positive natural leaves it fixed. -/
theorem toDist_mul_left {a : ℕ} (ha : 0 < a) (v : Fin C → ℕ) :
    toDist (fun i => a * v i) = toDist v := by
  funext i
  change ((a * v i : ℕ) : ℚ) / ∑ j, ((a * v j : ℕ) : ℚ)
    = ((v i : ℕ) : ℚ) / ∑ j, ((v j : ℕ) : ℚ)
  push_cast
  rw [← Finset.mul_sum]
  exact mul_div_mul_left _ _ (Nat.cast_ne_zero.mpr ha.ne')

/-! ### The restarted comparator -/

/-- **Exact Bayes restarted at time `s`**, from the floored run's own state there: the weights the
floored run holds at `s`, updated by the exact rule — no carrier, no projection — over `[s, t)`.
At `s = 0` this is `bayesRun` itself, the all-ones start being the floored run's own. -/
def bayesFrom (M : ℕ → Fin C → Bool) (b s t : ℕ) (i : Fin C) : ℕ :=
  raw (wRun (2 ^ b) (missFit M) s) i * 2 ^ hitCount M i s t

/-- The restarted comparator in exponent form, off the general normal form. -/
theorem bayesFrom_eq_pow (M : ℕ → Fin C → Bool) (b s t : ℕ) (i : Fin C) :
    bayesFrom M b s t i = 2 ^ (expRun M b s i + hitCount M i s t) := by
  rw [bayesFrom, wRun_eq_pow_expRun, ← pow_add]

/-- **At `s = 0` the restarted comparator is the exact run.** The floored run's state at time `0`
is the uniform start the exact run also begins from, so nothing has been restarted yet. -/
theorem bayesFrom_zero (M : ℕ → Fin C → Bool) (b t : ℕ) (i : Fin C) :
    bayesFrom M b 0 t i = bayesRun (missFit M) t i := by
  rw [bayesFrom_eq_pow, bayesRun_missFit, hitCount_zero]
  congr 1
  simp [expRun]

/-- **The tracking form of the accumulation bound**, and it asks for no realizable candidate.

Compare the floored run at `t` not with exact Bayes from the beginning of time — which
`toDist_wRun_sub_bayesRun_not_le_mirrorMiss` refutes outright without realizability — but with
exact Bayes **restarted at `s` from the floored run's own state there**. Then the same
`2(C−1)/2^b` holds, uniformly in the elapsed time, under two hypotheses carried by one candidate
over the window alone: `iL` is a running co-leader at `s`, and it misses at no step of `[s, t)`.
Nothing is assumed about the run before `s`, nothing about the other candidates, and nothing about
whether any candidate is consistent with the whole history.

The proof splits at the first time the co-leader reaches the ceiling. Before it no candidate is at
the ceiling, so no step rescales and the floored run *is* the restarted exact run, coordinate for
coordinate. From it the co-leader sits at the ceiling and hits at every step, so every step
rescales, and the argument is `toDist_wRun_sub_bayesRun_le`'s: scaled up by the common factor the
clip cost it, the two runs agree except on the candidates the clip has floored, of which there are
at most `C−1`, and each is off by at most the scale factor itself.

This is the mixture-currency instance of the tracking bounds of the weighted-majority and
fixed-share family — Littlestone and Warmuth (1994) §3 for the floored variant's weight floor,
recovery invariant and per-segment accounting, and Herbster and Warmuth (1998) for bounds against a
shifting comparator. That a weight floor buys recovery, that the weight ratios stay bounded, and
that a shifting comparator is trackable at all are theirs and are not claimed here. What is
machine-checked here is the comparator: exact Bayes restarted at a co-leader point, in total
variation on the quantized carrier, at the exact constant `2(C−1)/2^b`. -/
theorem toDist_wRun_sub_bayesFrom_le (M : ℕ → Fin C → Bool) (b : ℕ) {iL : Fin C} {s t : ℕ}
    (hst : s ≤ t) (hlead : ∀ j, expRun M b s j ≤ expRun M b s iL)
    (hiL : ∀ u, s ≤ u → u < t → M u iL = false) :
    ∑ i, |toDist (raw (wRun (2 ^ b) (missFit M) t)) i - toDist (bayesFrom M b s t) i|
      ≤ 2 * ((C : ℚ) - 1) / 2 ^ b := by
  have hC1 : 1 ≤ C := iL.pos
  have hCQ : (0 : ℚ) ≤ (C : ℚ) - 1 := by
    have : (1 : ℚ) ≤ (C : ℚ) := by exact_mod_cast hC1
    linarith
  have hpow : (0 : ℚ) < (2 : ℚ) ^ b := by positivity
  have hcb : expRun M b s iL ≤ b := expRun_le M b s iL
  have hhL : hitCount M iL s t = t - s := hitCount_of_no_miss M iL hst hiL
  have hexp : ∀ i, expRun M b t i
      = (expRun M b s i + hitCount M i s t) - ((t - s) - (b - expRun M b s iL)) :=
    expRun_eq_hitCount_sub M b hst hlead hiL
  by_cases hcase : b - expRun M b s iL ≤ t - s
  · -- past the ceiling: the co-leader is saturated, and the clip's cost is the whole residual
    set R := (t - s) - (b - expRun M b s iL) with hRdef
    have hFL : expRun M b s iL + hitCount M iL s t = R + b := by rw [hhL, hRdef]; omega
    set u : Fin C → ℕ := fun i => 2 ^ R * raw (wRun (2 ^ b) (missFit M) t) i with hu
    have hui : ∀ i, u i = 2 ^ (R + ((expRun M b s i + hitCount M i s t) - R)) := by
      intro i
      rw [hu]
      change 2 ^ R * raw (wRun (2 ^ b) (missFit M) t) i = _
      rw [wRun_eq_pow_expRun, hexp i, ← pow_add]
    have hconv : toDist (raw (wRun (2 ^ b) (missFit M) t)) = toDist u := by
      rw [hu]
      exact (toDist_mul_left (a := 2 ^ R) (by positivity) _).symm
    have hdiff : ∀ i, |((u i : ℕ) : ℚ) - ((bayesFrom M b s t i : ℕ) : ℚ)|
        ≤ if i = iL then 0 else (2 : ℚ) ^ R := by
      intro i
      by_cases hsat : R ≤ expRun M b s i + hitCount M i s t
      · have heq : u i = bayesFrom M b s t i := by
          rw [hui i, bayesFrom_eq_pow]
          congr 1
          omega
        rw [heq, sub_self, abs_zero]
        split
        · exact le_refl 0
        · positivity
      · have hne : i ≠ iL := by
          intro h
          rw [h] at hsat
          omega
        have huQ : ((u i : ℕ) : ℚ) = (2 : ℚ) ^ R := by
          rw [hui i, show R + ((expRun M b s i + hitCount M i s t) - R) = R from by omega]
          push_cast
          ring
        have hbQ : ((bayesFrom M b s t i : ℕ) : ℚ) ≤ (2 : ℚ) ^ R := by
          have hble : bayesFrom M b s t i ≤ 2 ^ R := by
            rw [bayesFrom_eq_pow]
            exact Nat.pow_le_pow_right (by norm_num) (by omega)
          calc ((bayesFrom M b s t i : ℕ) : ℚ) ≤ ((2 ^ R : ℕ) : ℚ) := by exact_mod_cast hble
            _ = (2 : ℚ) ^ R := by push_cast; ring
        have hbnn : (0 : ℚ) ≤ ((bayesFrom M b s t i : ℕ) : ℚ) := by positivity
        rw [if_neg hne, huQ, abs_of_nonneg (by linarith)]
        linarith
    have hsum : ∑ i, |((u i : ℕ) : ℚ) - ((bayesFrom M b s t i : ℕ) : ℚ)|
        ≤ ((C : ℚ) - 1) * (2 : ℚ) ^ R := by
      calc ∑ i, |((u i : ℕ) : ℚ) - ((bayesFrom M b s t i : ℕ) : ℚ)|
          ≤ ∑ i, if i = iL then 0 else (2 : ℚ) ^ R := Finset.sum_le_sum fun i _ => hdiff i
        _ = ((C : ℚ) - 1) * (2 : ℚ) ^ R := by
            rw [← Finset.sum_erase (f := fun i => if i = iL then (0 : ℚ) else (2 : ℚ) ^ R)
                Finset.univ (if_pos rfl),
              Finset.sum_congr rfl (fun j hj => if_neg (Finset.ne_of_mem_erase hj)),
              Finset.sum_const, nsmul_eq_mul, Finset.card_erase_of_mem (Finset.mem_univ iL),
              Finset.card_univ, Fintype.card_fin, Nat.cast_sub hC1, Nat.cast_one]
    have hbL : ((bayesFrom M b s t iL : ℕ) : ℚ) = (2 : ℚ) ^ R * 2 ^ b := by
      rw [bayesFrom_eq_pow, hFL]
      push_cast
      rw [pow_add]
    have hRB : (0 : ℚ) < (2 : ℚ) ^ R * 2 ^ b := by positivity
    have hBge : (2 : ℚ) ^ R * 2 ^ b ≤ ∑ j, ((bayesFrom M b s t j : ℕ) : ℚ) := by
      rw [← hbL]
      exact Finset.single_le_sum (f := fun j => ((bayesFrom M b s t j : ℕ) : ℚ))
        (fun j _ => by positivity) (Finset.mem_univ iL)
    have hBpos : (0 : ℚ) < ∑ j, ((bayesFrom M b s t j : ℕ) : ℚ) := lt_of_lt_of_le hRB hBge
    have hAge : (2 : ℚ) ^ R * 2 ^ b ≤ ∑ j, ((u j : ℕ) : ℚ) := by
      have huL : ((u iL : ℕ) : ℚ) = (2 : ℚ) ^ R * 2 ^ b := by
        rw [hui iL, show R + ((expRun M b s iL + hitCount M iL s t) - R) = R + b from by omega]
        push_cast
        rw [pow_add]
      rw [← huL]
      exact Finset.single_le_sum (f := fun j => ((u j : ℕ) : ℚ))
        (fun j _ => by positivity) (Finset.mem_univ iL)
    have hApos : (0 : ℚ) < ∑ j, ((u j : ℕ) : ℚ) := lt_of_lt_of_le hRB hAge
    rw [hconv]
    calc ∑ i, |toDist u i - toDist (bayesFrom M b s t) i|
        ≤ 2 * (∑ i, |((u i : ℕ) : ℚ) - ((bayesFrom M b s t i : ℕ) : ℚ)|)
            / ∑ j, ((bayesFrom M b s t j : ℕ) : ℚ) :=
          l1_normalize_le (fun i => ((u i : ℕ) : ℚ)) (fun i => ((bayesFrom M b s t i : ℕ) : ℚ))
            (fun i => by positivity) (fun i => by positivity) hApos hBpos
      _ ≤ 2 * ((C : ℚ) - 1) / 2 ^ b := by
          have hSle : (∑ i, |((u i : ℕ) : ℚ) - ((bayesFrom M b s t i : ℕ) : ℚ)|) * 2 ^ b
              ≤ ((C : ℚ) - 1) * ((2 : ℚ) ^ R * 2 ^ b) := by
            calc (∑ i, |((u i : ℕ) : ℚ) - ((bayesFrom M b s t i : ℕ) : ℚ)|) * 2 ^ b
                ≤ ((C : ℚ) - 1) * (2 : ℚ) ^ R * 2 ^ b :=
                  mul_le_mul_of_nonneg_right hsum hpow.le
              _ = ((C : ℚ) - 1) * ((2 : ℚ) ^ R * 2 ^ b) := by ring
          have hmul : ((C : ℚ) - 1) * ((2 : ℚ) ^ R * 2 ^ b)
              ≤ ((C : ℚ) - 1) * ∑ j, ((bayesFrom M b s t j : ℕ) : ℚ) :=
            mul_le_mul_of_nonneg_left hBge hCQ
          rw [div_le_div_iff₀ hBpos hpow]
          linarith
  · -- short of the ceiling: no step rescales, and the two runs are equal on the nose
    have hzero : (t - s) - (b - expRun M b s iL) = 0 := by omega
    have heq : raw (wRun (2 ^ b) (missFit M) t) = bayesFrom M b s t := by
      funext i
      rw [wRun_eq_pow_expRun, bayesFrom_eq_pow, hexp i, hzero, Nat.sub_zero]
    rw [heq]
    simp only [sub_self, abs_zero, Finset.sum_const_zero]
    exact div_nonneg (by linarith) hpow.le

/-- **The drift does not accumulate.** In the saturating regime the floored run's reading stays
within `2(C−1)/2^b` of the exact Bayes run's, *uniformly in `t`*: the right-hand side mentions no
horizon at all.

The per-step rate of `toDist_project_rate` provably does not telescope — Bayesian update is not
non-expansive in total variation — so this is a different argument, not a tighter constant. What
replaces the telescope is the normal form: scaled up by the common factor the clip cost it, the
floored run agrees with the exact run *exactly* on every candidate whose miss count is still inside
the budget exponent, and differs only on the saturated ones, of which there are at most `C−1`. So
the residual measures the spread of the candidates' miss counts beyond `log₂ W`, and nothing about
elapsed time. -/
theorem toDist_wRun_sub_bayesRun_le (M : ℕ → Fin C → Bool) {iR : Fin C}
    (hR : ∀ t, M t iR = false) (b t : ℕ) :
    ∑ i, |toDist (raw (wRun (2 ^ b) (missFit M) t)) i - toDist (bayesRun (missFit M) t) i|
      ≤ 2 * ((C : ℚ) - 1) / 2 ^ b := by
  have hbf : bayesRun (missFit M) t = bayesFrom M b 0 t := by
    funext i
    exact (bayesFrom_zero M b t i).symm
  rw [hbf]
  exact toDist_wRun_sub_bayesFrom_le (iL := iR) M b (Nat.zero_le t)
    (fun j => by simp [expRun]) (fun u _ _ => hR u)

/-! ### The guard on realizability: no accumulation is *false* without it

The bound above vanishes in the budget. The family below holds the discrepancy at `7/9` for
**every** budget, so realizability is not slack there either — and the mechanism is the same clip.
The exact run aggregates all history and ends symmetric; the floored run has discarded every debt
beyond the ceiling and ends `1 : 8`. -/

/-- **The mirror family**: candidate `0` hits for `b + 3` steps while candidate `1` misses, then the
two swap. By time `2b + 6` their miss counts are equal, so the exact run is symmetric — while the
floored run remembers only the last `b` steps of it. -/
def mirrorMiss (b : ℕ) : ℕ → Fin 2 → Bool :=
  fun t i => decide (if (i : ℕ) = 0 then b + 3 ≤ t else t < b + 3)

/-- Neither candidate is realizable: each misses throughout one of the two phases. -/
theorem mirrorMiss_not_realizable (b : ℕ) (i : Fin 2) : ¬ (∀ t, mirrorMiss b t i = false) := by
  intro h
  rcases Fin.exists_fin_two.mp ⟨i, rfl⟩ with hi | hi
  · have := h (b + 3)
    rw [hi] at this
    simp [mirrorMiss] at this
  · have := h 0
    rw [hi] at this
    simp [mirrorMiss] at this

/-- The first phase: candidate `0` climbs to the ceiling and holds it, candidate `1` is pinned at
the floor — its every miss absorbed by the clip. -/
private theorem expRun_mirrorMiss_phase1 (b : ℕ) : ∀ t, t ≤ b + 3 →
    expRun (mirrorMiss b) b t 0 = min t b ∧ expRun (mirrorMiss b) b t 1 = 0 := by
  intro t
  induction t with
  | zero => exact fun _ => ⟨by simp [expRun], by simp [expRun]⟩
  | succ t ih =>
      intro ht
      obtain ⟨h0, h1⟩ := ih (by omega)
      have hm0 : mirrorMiss b t 0 = false := by simp [mirrorMiss]; omega
      have hm1 : mirrorMiss b t 1 = true := by simp [mirrorMiss]; omega
      have hδ : (∃ j : Fin 2, expRun (mirrorMiss b) b t j = b ∧ mirrorMiss b t j = false)
          ↔ b ≤ t := by
        rw [Fin.exists_fin_two]
        simp [hm0, hm1, h0]
      have hstep : ∀ i : Fin 2, expStep b (mirrorMiss b t) (expRun (mirrorMiss b) b t) i
          = (expRun (mirrorMiss b) b t i + (if mirrorMiss b t i then 0 else 1))
            - (if b ≤ t then 1 else 0) := by
        intro i
        rw [expStep]
        congr 1
        by_cases h : b ≤ t
        · rw [if_pos h, if_pos (hδ.mpr h)]
        · rw [if_neg h, if_neg (fun hh => h (hδ.mp hh))]
      clear hδ
      refine ⟨?_, ?_⟩
      · change expStep b (mirrorMiss b t) (expRun (mirrorMiss b) b t) 0 = _
        rw [hstep 0, if_neg (by simp [hm0]), h0]
        split <;> omega
      · change expStep b (mirrorMiss b t) (expRun (mirrorMiss b) b t) 1 = _
        rw [hstep 1, if_pos hm1, h1]
        split <;> omega

/-- The second phase: candidate `1` climbs while candidate `0`, already at the ceiling, is charged
one exponent per rescale. Its exponent `b − (s − b)` is the reflection — debt it can never repay. -/
private theorem expRun_mirrorMiss_phase2 (b : ℕ) : ∀ s, s ≤ b + 3 →
    expRun (mirrorMiss b) b (b + 3 + s) 0 = b - (s - b)
      ∧ expRun (mirrorMiss b) b (b + 3 + s) 1 = min s b := by
  intro s
  induction s with
  | zero =>
      intro _
      obtain ⟨h0, h1⟩ := expRun_mirrorMiss_phase1 b (b + 3) (le_refl _)
      exact ⟨by rw [Nat.add_zero, h0]; omega, by rw [Nat.add_zero, h1]; omega⟩
  | succ s ih =>
      intro hs
      obtain ⟨h0, h1⟩ := ih (by omega)
      have hm0 : mirrorMiss b (b + 3 + s) 0 = true := by simp [mirrorMiss]
      have hm1 : mirrorMiss b (b + 3 + s) 1 = false := by simp [mirrorMiss]
      have hδ : (∃ j : Fin 2, expRun (mirrorMiss b) b (b + 3 + s) j = b
          ∧ mirrorMiss b (b + 3 + s) j = false) ↔ b ≤ s := by
        rw [Fin.exists_fin_two]
        simp [hm0, hm1, h1]
      have hstep : ∀ i : Fin 2,
          expStep b (mirrorMiss b (b + 3 + s)) (expRun (mirrorMiss b) b (b + 3 + s)) i
            = (expRun (mirrorMiss b) b (b + 3 + s) i
                + (if mirrorMiss b (b + 3 + s) i then 0 else 1)) - (if b ≤ s then 1 else 0) := by
        intro i
        rw [expStep]
        congr 1
        by_cases h : b ≤ s
        · rw [if_pos h, if_pos (hδ.mpr h)]
        · rw [if_neg h, if_neg (fun hh => h (hδ.mp hh))]
      clear hδ
      have hidx : b + 3 + (s + 1) = (b + 3 + s) + 1 := by omega
      rw [hidx]
      refine ⟨?_, ?_⟩
      · change expStep b (mirrorMiss b (b + 3 + s)) (expRun (mirrorMiss b) b (b + 3 + s)) 0 = _
        rw [hstep 0, if_pos hm0, h0]
        split <;> omega
      · change expStep b (mirrorMiss b (b + 3 + s)) (expRun (mirrorMiss b) b (b + 3 + s)) 1 = _
        rw [hstep 1, if_neg (by simp [hm1]), h1]
        split <;> omega

private theorem missCount_mirrorMiss_zero (b n : ℕ) :
    missCount (mirrorMiss b) 0 n = n - (b + 3) := by
  induction n with
  | zero => rw [missCount_zero]; omega
  | succ n ih =>
      rw [missCount_succ, ih]
      by_cases h : b + 3 ≤ n
      · rw [if_pos (show mirrorMiss b n 0 = true by simp [mirrorMiss]; omega)]
        omega
      · rw [if_neg (show ¬ (mirrorMiss b n 0 = true) by simp [mirrorMiss]; omega)]
        omega

private theorem missCount_mirrorMiss_one (b n : ℕ) :
    missCount (mirrorMiss b) 1 n = min n (b + 3) := by
  induction n with
  | zero => rw [missCount_zero]; omega
  | succ n ih =>
      rw [missCount_succ, ih]
      by_cases h : n < b + 3
      · rw [if_pos (show mirrorMiss b n 1 = true by simp [mirrorMiss]; omega)]
        omega
      · rw [if_neg (show ¬ (mirrorMiss b n 1 = true) by simp [mirrorMiss]; omega)]
        omega

/-- **The discrepancy on the mirror family, exactly: `7/9`, at every budget `b ≥ 3`.** The exact run
reads `(1/2, 1/2)` — equal miss counts, so no history distinguishes the two candidates — while the
floored run reads `(1/9, 8/9)`: the clip has thrown away everything beyond the last `b` steps, and
what survives is a ratio of `2 ^ 3` fixed by the phase length, not by the budget. -/
theorem toDist_wRun_sub_bayesRun_mirrorMiss (k : ℕ) :
    ∑ i, |toDist (raw (wRun (2 ^ (k + 3)) (missFit (mirrorMiss (k + 3))) (2 * k + 12))) i
        - toDist (bayesRun (missFit (mirrorMiss (k + 3))) (2 * k + 12)) i| = 7 / 9 := by
  obtain ⟨he0, he1⟩ := expRun_mirrorMiss_phase2 (k + 3) (k + 6) (by omega)
  rw [show (k + 3) + 3 + (k + 6) = 2 * k + 12 by omega] at he0 he1
  have he0' : expRun (mirrorMiss (k + 3)) (k + 3) (2 * k + 12) 0 = k := by rw [he0]; omega
  have he1' : expRun (mirrorMiss (k + 3)) (k + 3) (2 * k + 12) 1 = k + 3 := by rw [he1]; omega
  have hpk : (0 : ℚ) < (2 : ℚ) ^ k := by positivity
  -- the floored run: `2 ^ k` against `2 ^ (k+3)`
  have hw : ∀ i : Fin 2,
      ((raw (wRun (2 ^ (k + 3)) (missFit (mirrorMiss (k + 3))) (2 * k + 12)) i : ℕ) : ℚ)
        = (2 : ℚ) ^ expRun (mirrorMiss (k + 3)) (k + 3) (2 * k + 12) i := by
    intro i
    rw [wRun_eq_pow_expRun]
    push_cast
    ring
  have hwsum : ∑ j, ((raw (wRun (2 ^ (k + 3)) (missFit (mirrorMiss (k + 3))) (2 * k + 12))
      j : ℕ) : ℚ) = 9 * 2 ^ k := by
    rw [Fin.sum_univ_two, hw 0, hw 1, he0', he1', pow_add]
    ring
  have hd : ∀ i : Fin 2,
      toDist (raw (wRun (2 ^ (k + 3)) (missFit (mirrorMiss (k + 3))) (2 * k + 12))) i
        = (2 : ℚ) ^ expRun (mirrorMiss (k + 3)) (k + 3) (2 * k + 12) i / (9 * 2 ^ k) := by
    intro i
    change ((raw (wRun (2 ^ (k + 3)) (missFit (mirrorMiss (k + 3))) (2 * k + 12)) i : ℕ) : ℚ)
      / ∑ j, ((raw (wRun (2 ^ (k + 3)) (missFit (mirrorMiss (k + 3))) (2 * k + 12)) j : ℕ) : ℚ) = _
    rw [hw i, hwsum]
  -- the exact run: equal miss counts, hence symmetric
  have hb : ∀ i : Fin 2, ((bayesRun (missFit (mirrorMiss (k + 3))) (2 * k + 12) i : ℕ) : ℚ)
      = (2 : ℚ) ^ (k + 6) := by
    rw [Fin.forall_fin_two]
    refine ⟨?_, ?_⟩
    · rw [bayesRun_missFit, missCount_mirrorMiss_zero,
        show 2 * k + 12 - ((k + 3) + 3) = k + 6 by omega,
        show 2 * k + 12 - (k + 6) = k + 6 by omega]
      push_cast
      ring
    · rw [bayesRun_missFit, missCount_mirrorMiss_one,
        show min (2 * k + 12) ((k + 3) + 3) = k + 6 by omega,
        show 2 * k + 12 - (k + 6) = k + 6 by omega]
      push_cast
      ring
  have hbd : ∀ i : Fin 2, toDist (bayesRun (missFit (mirrorMiss (k + 3))) (2 * k + 12)) i
      = 1 / 2 := by
    intro i
    change ((bayesRun (missFit (mirrorMiss (k + 3))) (2 * k + 12) i : ℕ) : ℚ)
      / ∑ j, ((bayesRun (missFit (mirrorMiss (k + 3))) (2 * k + 12) j : ℕ) : ℚ) = _
    rw [Fin.sum_univ_two, hb 0, hb 1, hb i]
    have : (0 : ℚ) < (2 : ℚ) ^ (k + 6) := by positivity
    field_simp
    ring
  rw [Fin.sum_univ_two, hd 0, hd 1, hbd 0, hbd 1, he0', he1']
  have h1 : (2 : ℚ) ^ k / (9 * 2 ^ k) - 1 / 2 = -(7 / 18) := by field_simp; ring
  have h2 : (2 : ℚ) ^ (k + 3) / (9 * 2 ^ k) - 1 / 2 = 7 / 18 := by
    rw [pow_add]
    field_simp
    ring
  rw [h1, h2, abs_neg]
  norm_num

/-- **No accumulation is refutable without realizability.** The floored run's reading stays `7/9`
away from the exact run's on the mirror family, at every budget `b = k + 3` — while
`toDist_wRun_sub_bayesRun_le` bounds that distance by `2(C−1)/2^b`, which falls below `1/4` already
at `b = 3` and vanishes thereafter. The bound is not a theorem awaiting a weaker hypothesis: what
the floor buys is *tracking* the recent leader, and tracking is not approximating exact Bayes. -/
theorem toDist_wRun_sub_bayesRun_not_le_mirrorMiss (k : ℕ) :
    ¬ (∑ i, |toDist (raw (wRun (2 ^ (k + 3)) (missFit (mirrorMiss (k + 3))) (2 * k + 12))) i
          - toDist (bayesRun (missFit (mirrorMiss (k + 3))) (2 * k + 12)) i|
        ≤ 2 * (((2 : ℕ) : ℚ) - 1) / 2 ^ (k + 3)) := by
  rw [toDist_wRun_sub_bayesRun_mirrorMiss k]
  have h8 : (8 : ℚ) ≤ (2 : ℚ) ^ (k + 3) := by
    calc (8 : ℚ) = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ (k + 3) := pow_le_pow_right₀ (by norm_num) (by omega)
  intro hle
  rw [le_div_iff₀ (by positivity : (0 : ℚ) < (2 : ℚ) ^ (k + 3))] at hle
  push_cast at hle
  linarith

/-- **The refutation at the smallest budget where it bites.** At `b = 2` the clip has less history
to discard, so the surviving ratio is `1 : 4` rather than `1 : 8` — and the discrepancy `3/5` still
exceeds the bound's `2(C−1)/2^b = 1/2`. Below this the bound is large enough to absorb the gap,
which is the only reason `b = 2` needs its own arithmetic. -/
theorem toDist_wRun_sub_bayesRun_not_le_mirrorMiss_two :
    ¬ (∑ i, |toDist (raw (wRun (2 ^ 2) (missFit (mirrorMiss 2)) 10)) i
          - toDist (bayesRun (missFit (mirrorMiss 2)) 10) i|
        ≤ 2 * (((2 : ℕ) : ℚ) - 1) / 2 ^ 2) := by
  obtain ⟨he0, he1⟩ := expRun_mirrorMiss_phase2 2 5 (by omega)
  rw [show 2 + 3 + 5 = 10 from by norm_num] at he0 he1
  rw [show 2 - (5 - 2) = 0 from by norm_num] at he0
  rw [show min 5 2 = 2 from by norm_num] at he1
  have hw : ∀ i : Fin 2, ((raw (wRun (2 ^ 2) (missFit (mirrorMiss 2)) 10) i : ℕ) : ℚ)
      = (2 : ℚ) ^ expRun (mirrorMiss 2) 2 10 i := by
    intro i
    rw [wRun_eq_pow_expRun]
    push_cast
    ring
  have hd : ∀ i : Fin 2, toDist (raw (wRun (2 ^ 2) (missFit (mirrorMiss 2)) 10)) i
      = (2 : ℚ) ^ expRun (mirrorMiss 2) 2 10 i / 5 := by
    intro i
    change ((raw (wRun (2 ^ 2) (missFit (mirrorMiss 2)) 10) i : ℕ) : ℚ)
      / ∑ j, ((raw (wRun (2 ^ 2) (missFit (mirrorMiss 2)) 10) j : ℕ) : ℚ) = _
    rw [hw i, Fin.sum_univ_two, hw 0, hw 1, he0, he1]
    norm_num
  have hb : ∀ i : Fin 2, ((bayesRun (missFit (mirrorMiss 2)) 10 i : ℕ) : ℚ) = 32 := by
    rw [Fin.forall_fin_two]
    refine ⟨?_, ?_⟩
    · rw [bayesRun_missFit, missCount_mirrorMiss_zero]
      norm_num
    · rw [bayesRun_missFit, missCount_mirrorMiss_one]
      norm_num
  have hbd : ∀ i : Fin 2, toDist (bayesRun (missFit (mirrorMiss 2)) 10) i = 1 / 2 := by
    intro i
    change ((bayesRun (missFit (mirrorMiss 2)) 10 i : ℕ) : ℚ)
      / ∑ j, ((bayesRun (missFit (mirrorMiss 2)) 10 j : ℕ) : ℚ) = _
    rw [Fin.sum_univ_two, hb 0, hb 1, hb i]
    norm_num
  rw [Fin.sum_univ_two, hd 0, hd 1, hbd 0, hbd 1, he0, he1]
  norm_num

/-! ### The guards on the tracking hypotheses: both are load-bearing

`toDist_wRun_sub_bayesFrom_le` asks two things of one candidate over the window `[s, t)`: that it
is a running co-leader at `s`, and that it misses at no step inside. Neither is slack. The two
families below satisfy every other condition of the theorem — a power-of-two budget, the `2`-vs-`1`
fitness, the all-ones start — and each drops exactly one hypothesis; each then holds the
discrepancy above a fixed positive constant while the bound vanishes in the budget.

The mechanism is the same clip in both, read at the restart point. `preAbsorption` gives the window
a candidate that never misses, but one whose earlier debt the ceiling has already erased: the
restarted comparator credits it from a floor it did not earn, while the run credits the incumbent.
`sinkRecover` gives the window a co-leader, but one that later quits; the candidate that recovers
does so from a floor that has swallowed its own misses, and the restarted comparator, starting from
that floor, cannot see them either. -/

/-- **The pre-absorption family** (`C = 3`): candidate `0` climbs alone to the ceiling over `b`
steps; then for `8` steps candidate `1` hits alongside it and candidate `2` misses, both pinned at
the floor, so that everything those `8` steps decide is erased; then for `b + 2` steps candidate
`0` quits and `1` and `2` climb together. Read from `s = b`, candidate `1` is the window's only
never-missing candidate — and it is exactly `b` exponents short of being a co-leader there. -/
def preAbsorption (b : ℕ) : ℕ → Fin 3 → Bool := fun t i =>
  if t < b then decide (i ≠ 0) else if t < b + 8 then decide (i = 2) else decide (i = 0)

/-- Candidate `1` misses at no step from `b` on: it hits through the middle phase and the last. -/
theorem preAbsorption_never_misses_one (b : ℕ) {u : ℕ} (hu : b ≤ u) :
    preAbsorption b u 1 = false := by
  simp [preAbsorption]
  omega

/-- And it is the window's *only* never-missing candidate: `0` quits at `b + 8`, `2` misses from
the start. So no other choice of co-leader is available to rescue the theorem here. -/
theorem preAbsorption_misses_of_ne_one (b : ℕ) (i : Fin 3) (hi : i ≠ 1) :
    ∃ u, b ≤ u ∧ u < 2 * b + 10 ∧ preAbsorption b u i = true := by
  fin_cases i
  · exact ⟨b + 8, by omega, by omega, by simp [preAbsorption]⟩
  · exact absurd rfl hi
  · exact ⟨b, by omega, by omega, by simp [preAbsorption]⟩

/-- The first two phases: candidate `0` climbs to the ceiling and holds it, `1` and `2` are pinned
at the floor — `1`'s eight hits absorbed by the rescale exactly as `2`'s eight misses are. -/
private theorem expRun_preAbsorption_early (b : ℕ) : ∀ n, n ≤ b + 8 →
    expRun (preAbsorption b) b n 0 = min n b ∧ expRun (preAbsorption b) b n 1 = 0
      ∧ expRun (preAbsorption b) b n 2 = 0 := by
  intro n
  induction n with
  | zero => exact fun _ => ⟨by simp [expRun], by simp [expRun], by simp [expRun]⟩
  | succ n ih =>
      intro hn
      obtain ⟨h0, h1, h2⟩ := ih (by omega)
      have hm0 : preAbsorption b n 0 = false := by simp [preAbsorption]; omega
      have hδ : (∃ j : Fin 3, expRun (preAbsorption b) b n j = b
          ∧ preAbsorption b n j = false) ↔ b ≤ n := by
        constructor
        · rintro ⟨j, hj, -⟩
          fin_cases j
          · have hj' : expRun (preAbsorption b) b n 0 = b := hj
            rw [h0] at hj'; omega
          · have hj' : expRun (preAbsorption b) b n 1 = b := hj
            rw [h1] at hj'; omega
          · have hj' : expRun (preAbsorption b) b n 2 = b := hj
            rw [h2] at hj'; omega
        · exact fun hbn => ⟨0, by rw [h0]; omega, hm0⟩
      have hstep : ∀ i : Fin 3, expRun (preAbsorption b) b (n + 1) i
          = (expRun (preAbsorption b) b n i + (if preAbsorption b n i then 0 else 1))
            - (if b ≤ n then 1 else 0) := by
        intro i
        change expStep b (preAbsorption b n) (expRun (preAbsorption b) b n) i = _
        rw [expStep]
        congr 1
        by_cases h : b ≤ n
        · rw [if_pos h, if_pos (hδ.mpr h)]
        · rw [if_neg h, if_neg (fun hh => h (hδ.mp hh))]
      clear hδ
      refine ⟨?_, ?_, ?_⟩
      · rw [hstep 0, if_neg (by simp [hm0]), h0]
        split <;> omega
      · rw [hstep 1, h1]
        by_cases hnb : n < b
        · rw [if_pos (show preAbsorption b n 1 = true by simp [preAbsorption]; omega),
            if_neg (by omega : ¬ b ≤ n)]
        · rw [if_neg (show ¬ (preAbsorption b n 1 = true) by simp [preAbsorption]; omega),
            if_pos (by omega : b ≤ n)]
      · rw [hstep 2, h2,
          if_pos (show preAbsorption b n 2 = true by simp [preAbsorption]; omega)]
        split <;> omega

/-- The last phase: candidate `0` quits and is charged one exponent per rescale, while `1` and `2`
climb together — `2` carrying misses the floor has already erased. -/
private theorem expRun_preAbsorption_late (b : ℕ) : ∀ k, k ≤ b + 2 →
    expRun (preAbsorption b) b (b + 8 + k) 0 = b - (k - b)
      ∧ expRun (preAbsorption b) b (b + 8 + k) 1 = min k b
      ∧ expRun (preAbsorption b) b (b + 8 + k) 2 = min k b := by
  intro k
  induction k with
  | zero =>
      intro _
      obtain ⟨h0, h1, h2⟩ := expRun_preAbsorption_early b (b + 8) (le_refl _)
      exact ⟨by rw [Nat.add_zero, h0]; omega, by rw [Nat.add_zero, h1]; omega,
        by rw [Nat.add_zero, h2]; omega⟩
  | succ k ih =>
      intro hk
      obtain ⟨h0, h1, h2⟩ := ih (by omega)
      have hm0 : preAbsorption b (b + 8 + k) 0 = true := by simp [preAbsorption]; omega
      have hm1 : preAbsorption b (b + 8 + k) 1 = false := by simp [preAbsorption]; omega
      have hδ : (∃ j : Fin 3, expRun (preAbsorption b) b (b + 8 + k) j = b
          ∧ preAbsorption b (b + 8 + k) j = false) ↔ b ≤ k := by
        constructor
        · rintro ⟨j, hj, hjm⟩
          fin_cases j
          · have hjm' : preAbsorption b (b + 8 + k) 0 = false := hjm
            rw [hm0] at hjm'; exact absurd hjm' (by simp)
          · have hj' : expRun (preAbsorption b) b (b + 8 + k) 1 = b := hj
            rw [h1] at hj'; omega
          · have hj' : expRun (preAbsorption b) b (b + 8 + k) 2 = b := hj
            rw [h2] at hj'; omega
        · exact fun hbk => ⟨1, by rw [h1]; omega, hm1⟩
      have hstep : ∀ i : Fin 3, expRun (preAbsorption b) b (b + 8 + (k + 1)) i
          = (expRun (preAbsorption b) b (b + 8 + k) i
              + (if preAbsorption b (b + 8 + k) i then 0 else 1))
            - (if b ≤ k then 1 else 0) := by
        intro i
        change expStep b (preAbsorption b (b + 8 + k))
          (expRun (preAbsorption b) b (b + 8 + k)) i = _
        rw [expStep]
        congr 1
        by_cases h : b ≤ k
        · rw [if_pos h, if_pos (hδ.mpr h)]
        · rw [if_neg h, if_neg (fun hh => h (hδ.mp hh))]
      clear hδ
      refine ⟨?_, ?_, ?_⟩
      · rw [hstep 0, if_pos hm0, h0]
        split <;> omega
      · rw [hstep 1, if_neg (by simp [hm1]), h1]
        split <;> omega
      · rw [hstep 2, h2,
          if_neg (show ¬ (preAbsorption b (b + 8 + k) 2 = true) by simp [preAbsorption]; omega)]
        split <;> omega

private theorem missCount_preAbsorption_zero (b n : ℕ) :
    missCount (preAbsorption b) 0 n = n - (b + 8) := by
  induction n with
  | zero => rw [missCount_zero]; omega
  | succ n ih =>
      rw [missCount_succ, ih]
      by_cases h : b + 8 ≤ n
      · rw [if_pos (show preAbsorption b n 0 = true by simp [preAbsorption]; omega)]
        omega
      · rw [if_neg (show ¬ (preAbsorption b n 0 = true) by simp [preAbsorption]; omega)]
        omega

private theorem missCount_preAbsorption_one (b n : ℕ) :
    missCount (preAbsorption b) 1 n = min n b := by
  induction n with
  | zero => rw [missCount_zero]; omega
  | succ n ih =>
      rw [missCount_succ, ih]
      by_cases h : n < b
      · rw [if_pos (show preAbsorption b n 1 = true by simp [preAbsorption]; omega)]
        omega
      · rw [if_neg (show ¬ (preAbsorption b n 1 = true) by simp [preAbsorption]; omega)]
        omega

private theorem missCount_preAbsorption_two (b n : ℕ) :
    missCount (preAbsorption b) 2 n = min n (b + 8) := by
  induction n with
  | zero => rw [missCount_zero]; omega
  | succ n ih =>
      rw [missCount_succ, ih]
      by_cases h : n < b + 8
      · rw [if_pos (show preAbsorption b n 2 = true by simp [preAbsorption]; omega)]
        omega
      · rw [if_neg (show ¬ (preAbsorption b n 2 = true) by simp [preAbsorption]; omega)]
        omega

/-- **Co-leadership fails at the restart point**, and it fails by the whole budget: at `s = b` the
window's only never-missing candidate sits at exponent `0` against the incumbent's `b`. -/
theorem preAbsorption_not_coleader (b : ℕ) (hb : 1 ≤ b) :
    ¬ (∀ j : Fin 3, expRun (preAbsorption b) b b j ≤ expRun (preAbsorption b) b b 1) := by
  intro h
  obtain ⟨h0, h1, -⟩ := expRun_preAbsorption_early b b (by omega)
  have hj := h 0
  rw [h0, h1] at hj
  omega

/-- **The discrepancy without co-leadership: `850/963`, at every budget `b = k + 3`.** The floored
run reads `(1/9, 4/9, 4/9)` — the incumbent has been charged for quitting, and the two climbers are
level. The comparator restarted at `s = b` reads `(64/321, 256/321, 1/321)`: it starts from the
same floored state, but it then credits every one of the window's hits, including the eight the
ceiling erased for candidate `1` and the eight misses it erased for candidate `2`. The gap does not
move with the budget, and the ratios are fixed by the phase lengths alone. -/
theorem toDist_wRun_sub_bayesFrom_preAbsorption (k : ℕ) :
    ∑ i, |toDist (raw (wRun (2 ^ (k + 3)) (missFit (preAbsorption (k + 3))) (2 * k + 16))) i
        - toDist (bayesFrom (preAbsorption (k + 3)) (k + 3) (k + 3) (2 * k + 16)) i|
      = 850 / 963 := by
  obtain ⟨he0, he1, he2⟩ := expRun_preAbsorption_late (k + 3) ((k + 3) + 2) (le_refl _)
  rw [show (k + 3) + 8 + ((k + 3) + 2) = 2 * k + 16 by omega] at he0 he1 he2
  have he0' : expRun (preAbsorption (k + 3)) (k + 3) (2 * k + 16) 0 = k + 1 := by rw [he0]; omega
  have he1' : expRun (preAbsorption (k + 3)) (k + 3) (2 * k + 16) 1 = k + 3 := by rw [he1]; omega
  have he2' : expRun (preAbsorption (k + 3)) (k + 3) (2 * k + 16) 2 = k + 3 := by rw [he2]; omega
  obtain ⟨hs0, hs1, hs2⟩ := expRun_preAbsorption_early (k + 3) (k + 3) (by omega)
  have hs0' : expRun (preAbsorption (k + 3)) (k + 3) (k + 3) 0 = k + 3 := by rw [hs0]; omega
  have hh0 : hitCount (preAbsorption (k + 3)) 0 (k + 3) (2 * k + 16) = 8 := by
    rw [hitCount, missCount_preAbsorption_zero, missCount_preAbsorption_zero]; omega
  have hh1 : hitCount (preAbsorption (k + 3)) 1 (k + 3) (2 * k + 16) = k + 13 := by
    rw [hitCount, missCount_preAbsorption_one, missCount_preAbsorption_one]; omega
  have hh2 : hitCount (preAbsorption (k + 3)) 2 (k + 3) (2 * k + 16) = k + 5 := by
    rw [hitCount, missCount_preAbsorption_two, missCount_preAbsorption_two]; omega
  have hpk : (0 : ℚ) < (2 : ℚ) ^ (k + 1) := by positivity
  have hpk5 : (0 : ℚ) < (2 : ℚ) ^ (k + 5) := by positivity
  -- the floored run
  have hw : ∀ i : Fin 3,
      ((raw (wRun (2 ^ (k + 3)) (missFit (preAbsorption (k + 3))) (2 * k + 16)) i : ℕ) : ℚ)
        = (2 : ℚ) ^ expRun (preAbsorption (k + 3)) (k + 3) (2 * k + 16) i := by
    intro i
    rw [wRun_eq_pow_expRun]
    push_cast
    ring
  have hwsum : ∑ j, ((raw (wRun (2 ^ (k + 3)) (missFit (preAbsorption (k + 3)))
      (2 * k + 16)) j : ℕ) : ℚ) = 9 * 2 ^ (k + 1) := by
    rw [Fin.sum_univ_three, hw 0, hw 1, hw 2, he0', he1', he2',
      show k + 3 = (k + 1) + 2 by omega, pow_add]
    ring
  have hd : ∀ i : Fin 3,
      toDist (raw (wRun (2 ^ (k + 3)) (missFit (preAbsorption (k + 3))) (2 * k + 16))) i
        = (2 : ℚ) ^ expRun (preAbsorption (k + 3)) (k + 3) (2 * k + 16) i / (9 * 2 ^ (k + 1)) := by
    intro i
    change ((raw (wRun (2 ^ (k + 3)) (missFit (preAbsorption (k + 3))) (2 * k + 16)) i : ℕ) : ℚ)
      / ∑ j, ((raw (wRun (2 ^ (k + 3)) (missFit (preAbsorption (k + 3)))
        (2 * k + 16)) j : ℕ) : ℚ) = _
    rw [hw i, hwsum]
  -- the comparator restarted at `s = b`
  have hb : ∀ i : Fin 3,
      ((bayesFrom (preAbsorption (k + 3)) (k + 3) (k + 3) (2 * k + 16) i : ℕ) : ℚ)
        = (2 : ℚ) ^ (expRun (preAbsorption (k + 3)) (k + 3) (k + 3) i
            + hitCount (preAbsorption (k + 3)) i (k + 3) (2 * k + 16)) := by
    intro i
    rw [bayesFrom_eq_pow]
    push_cast
    ring
  have hbsum : ∑ j, ((bayesFrom (preAbsorption (k + 3)) (k + 3) (k + 3)
      (2 * k + 16) j : ℕ) : ℚ) = 321 * 2 ^ (k + 5) := by
    rw [Fin.sum_univ_three, hb 0, hb 1, hb 2, hs0', hs1, hs2, hh0, hh1, hh2,
      show k + 3 + 8 = (k + 5) + 6 by omega,
      show (0 : ℕ) + (k + 13) = (k + 5) + 8 by omega,
      show (0 : ℕ) + (k + 5) = k + 5 by omega, pow_add, pow_add]
    ring
  have hbd : ∀ i : Fin 3, toDist (bayesFrom (preAbsorption (k + 3)) (k + 3) (k + 3)
      (2 * k + 16)) i
        = (2 : ℚ) ^ (expRun (preAbsorption (k + 3)) (k + 3) (k + 3) i
            + hitCount (preAbsorption (k + 3)) i (k + 3) (2 * k + 16)) / (321 * 2 ^ (k + 5)) := by
    intro i
    change ((bayesFrom (preAbsorption (k + 3)) (k + 3) (k + 3) (2 * k + 16) i : ℕ) : ℚ)
      / ∑ j, ((bayesFrom (preAbsorption (k + 3)) (k + 3) (k + 3) (2 * k + 16) j : ℕ) : ℚ) = _
    rw [hb i, hbsum]
  rw [Fin.sum_univ_three, hd 0, hd 1, hd 2, hbd 0, hbd 1, hbd 2, he0', he1', he2',
    hs0', hs1, hs2, hh0, hh1, hh2]
  rw [show (2 : ℚ) ^ (k + 1) / (9 * 2 ^ (k + 1)) = 1 / 9 by field_simp,
    show (2 : ℚ) ^ (k + 3) / (9 * 2 ^ (k + 1)) = 4 / 9 by
      rw [show k + 3 = (k + 1) + 2 by omega, pow_add]; field_simp; ring,
    show (2 : ℚ) ^ (k + 3 + 8) / (321 * 2 ^ (k + 5)) = 64 / 321 by
      rw [show k + 3 + 8 = (k + 5) + 6 by omega, pow_add]; field_simp; ring,
    show (2 : ℚ) ^ ((0 : ℕ) + (k + 13)) / (321 * 2 ^ (k + 5)) = 256 / 321 by
      rw [show (0 : ℕ) + (k + 13) = (k + 5) + 8 by omega, pow_add]; field_simp; ring,
    show (2 : ℚ) ^ ((0 : ℕ) + (k + 5)) / (321 * 2 ^ (k + 5)) = 1 / 321 by
      rw [show (0 : ℕ) + (k + 5) = k + 5 by omega]; field_simp]
  norm_num

/-- **The tracking bound is refutable without co-leadership.** With `iL = 1` — the window's only
never-missing candidate — every other hypothesis of `toDist_wRun_sub_bayesFrom_le` holds and the
conclusion fails at every budget `b = k + 3`, the discrepancy staying at `850/963` against a bound
that is already `1/2` at `b = 3`. `preAbsorption_misses_of_ne_one` closes the escape: no other
candidate could have been taken as `iL`. -/
theorem toDist_wRun_sub_bayesFrom_not_le_preAbsorption (k : ℕ) :
    ¬ (∑ i, |toDist (raw (wRun (2 ^ (k + 3)) (missFit (preAbsorption (k + 3))) (2 * k + 16))) i
          - toDist (bayesFrom (preAbsorption (k + 3)) (k + 3) (k + 3) (2 * k + 16)) i|
        ≤ 2 * (((3 : ℕ) : ℚ) - 1) / 2 ^ (k + 3)) := by
  rw [toDist_wRun_sub_bayesFrom_preAbsorption k]
  have h8 : (8 : ℚ) ≤ (2 : ℚ) ^ (k + 3) := by
    calc (8 : ℚ) = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ (k + 3) := pow_le_pow_right₀ (by norm_num) (by omega)
  intro hle
  rw [le_div_iff₀ (by positivity : (0 : ℚ) < (2 : ℚ) ^ (k + 3))] at hle
  push_cast at hle
  linarith

/-- **The sink-and-recover family** (`C = 2`): candidate `0` climbs to the ceiling and holds it for
`b + 6` steps while candidate `1` is pinned at the floor, its every miss absorbed there; then `0`
quits for `b` steps and `1` climbs back to the ceiling. Read from `s = b`, candidate `0` *is* a
co-leader — and it is the six steps of debt the floor swallowed for `1`, invisible from the
restart state, that the comparator then cannot price. -/
def sinkRecover (b : ℕ) : ℕ → Fin 2 → Bool :=
  fun t i => if t < b + 6 then decide (i = 1) else decide (i = 0)

/-- **No candidate survives the window**: `1` misses through the middle phase, `0` through the
last. So the never-missing hypothesis fails for *every* choice of `iL`, and it is the only
hypothesis that does. -/
theorem sinkRecover_no_survivor (b : ℕ) (hb : 1 ≤ b) (i : Fin 2) :
    ∃ u, b ≤ u ∧ u < 2 * b + 6 ∧ sinkRecover b u i = true := by
  fin_cases i
  · exact ⟨b + 6, by omega, by omega, by simp [sinkRecover]⟩
  · exact ⟨b, by omega, by omega, by simp [sinkRecover]⟩

/-- The first phase: candidate `0` climbs to the ceiling and holds it; `1` is pinned at the
floor. -/
private theorem expRun_sinkRecover_early (b : ℕ) : ∀ n, n ≤ b + 6 →
    expRun (sinkRecover b) b n 0 = min n b ∧ expRun (sinkRecover b) b n 1 = 0 := by
  intro n
  induction n with
  | zero => exact fun _ => ⟨by simp [expRun], by simp [expRun]⟩
  | succ n ih =>
      intro hn
      obtain ⟨h0, h1⟩ := ih (by omega)
      have hm0 : sinkRecover b n 0 = false := by simp [sinkRecover]; omega
      have hm1 : sinkRecover b n 1 = true := by simp [sinkRecover]; omega
      have hδ : (∃ j : Fin 2, expRun (sinkRecover b) b n j = b
          ∧ sinkRecover b n j = false) ↔ b ≤ n := by
        rw [Fin.exists_fin_two]
        simp [hm0, hm1, h0]
      have hstep : ∀ i : Fin 2, expRun (sinkRecover b) b (n + 1) i
          = (expRun (sinkRecover b) b n i + (if sinkRecover b n i then 0 else 1))
            - (if b ≤ n then 1 else 0) := by
        intro i
        change expStep b (sinkRecover b n) (expRun (sinkRecover b) b n) i = _
        rw [expStep]
        congr 1
        by_cases h : b ≤ n
        · rw [if_pos h, if_pos (hδ.mpr h)]
        · rw [if_neg h, if_neg (fun hh => h (hδ.mp hh))]
      clear hδ
      refine ⟨?_, ?_⟩
      · rw [hstep 0, if_neg (by simp [hm0]), h0]
        split <;> omega
      · rw [hstep 1, if_pos hm1, h1]
        split <;> omega

/-- The second phase: candidate `1` climbs back to the ceiling out of the floor, while `0` holds
it — no rescale fires until `1` arrives, so `0` is never charged for quitting. -/
private theorem expRun_sinkRecover_late (b : ℕ) : ∀ j, j ≤ b →
    expRun (sinkRecover b) b (b + 6 + j) 0 = b
      ∧ expRun (sinkRecover b) b (b + 6 + j) 1 = min j b := by
  intro j
  induction j with
  | zero =>
      intro _
      obtain ⟨h0, h1⟩ := expRun_sinkRecover_early b (b + 6) (le_refl _)
      exact ⟨by rw [Nat.add_zero, h0]; omega, by rw [Nat.add_zero, h1]; omega⟩
  | succ j ih =>
      intro hj
      obtain ⟨h0, h1⟩ := ih (by omega)
      have hm0 : sinkRecover b (b + 6 + j) 0 = true := by simp [sinkRecover]
      have hm1 : sinkRecover b (b + 6 + j) 1 = false := by simp [sinkRecover]
      have hδ : (∃ i : Fin 2, expRun (sinkRecover b) b (b + 6 + j) i = b
          ∧ sinkRecover b (b + 6 + j) i = false) ↔ b ≤ j := by
        rw [Fin.exists_fin_two]
        simp [hm0, hm1, h1]
      have hstep : ∀ i : Fin 2, expRun (sinkRecover b) b (b + 6 + (j + 1)) i
          = (expRun (sinkRecover b) b (b + 6 + j) i
              + (if sinkRecover b (b + 6 + j) i then 0 else 1))
            - (if b ≤ j then 1 else 0) := by
        intro i
        change expStep b (sinkRecover b (b + 6 + j)) (expRun (sinkRecover b) b (b + 6 + j)) i = _
        rw [expStep]
        congr 1
        by_cases h : b ≤ j
        · rw [if_pos h, if_pos (hδ.mpr h)]
        · rw [if_neg h, if_neg (fun hh => h (hδ.mp hh))]
      clear hδ
      refine ⟨?_, ?_⟩
      · rw [hstep 0, if_pos hm0, h0]
        split <;> omega
      · rw [hstep 1, if_neg (by simp [hm1]), h1]
        split <;> omega

private theorem missCount_sinkRecover_zero (b n : ℕ) :
    missCount (sinkRecover b) 0 n = n - (b + 6) := by
  induction n with
  | zero => rw [missCount_zero]; omega
  | succ n ih =>
      rw [missCount_succ, ih]
      by_cases h : b + 6 ≤ n
      · rw [if_pos (show sinkRecover b n 0 = true by simp [sinkRecover]; omega)]
        omega
      · rw [if_neg (show ¬ (sinkRecover b n 0 = true) by simp [sinkRecover]; omega)]
        omega

private theorem missCount_sinkRecover_one (b n : ℕ) :
    missCount (sinkRecover b) 1 n = min n (b + 6) := by
  induction n with
  | zero => rw [missCount_zero]; omega
  | succ n ih =>
      rw [missCount_succ, ih]
      by_cases h : n < b + 6
      · rw [if_pos (show sinkRecover b n 1 = true by simp [sinkRecover]; omega)]
        omega
      · rw [if_neg (show ¬ (sinkRecover b n 1 = true) by simp [sinkRecover]; omega)]
        omega

/-- **Co-leadership does hold at the restart point** here: candidate `0` is at the ceiling at
`s = b`, so it is the never-missing hypothesis alone that the family drops. -/
theorem sinkRecover_coleader (b : ℕ) :
    ∀ j : Fin 2, expRun (sinkRecover b) b b j ≤ expRun (sinkRecover b) b b 0 := by
  obtain ⟨h0, h1⟩ := expRun_sinkRecover_early b b (by omega)
  rw [Fin.forall_fin_two]
  exact ⟨le_refl _, by rw [h0, h1]; omega⟩

/-- **The discrepancy without a surviving candidate: `63/65`, at every budget `b = k + 2`.** The
floored run ends symmetric — `1` has climbed all the way back, and `0` was never charged for
quitting, because no rescale fires until `1` arrives. The comparator restarted at `s = b` reads
`(64/65, 1/65)`: it inherits `0`'s ceiling and `1`'s floor as the *prior*, then credits `0` the six
hits it takes before quitting and holds `1`'s six misses against it — misses the floor had already
absorbed, so the run itself has forgotten them. -/
theorem toDist_wRun_sub_bayesFrom_sinkRecover (k : ℕ) :
    ∑ i, |toDist (raw (wRun (2 ^ (k + 2)) (missFit (sinkRecover (k + 2))) (2 * k + 10))) i
        - toDist (bayesFrom (sinkRecover (k + 2)) (k + 2) (k + 2) (2 * k + 10)) i|
      = 63 / 65 := by
  obtain ⟨he0, he1⟩ := expRun_sinkRecover_late (k + 2) (k + 2) (le_refl _)
  rw [show (k + 2) + 6 + (k + 2) = 2 * k + 10 by omega] at he0 he1
  have he1' : expRun (sinkRecover (k + 2)) (k + 2) (2 * k + 10) 1 = k + 2 := by rw [he1]; omega
  obtain ⟨hs0, hs1⟩ := expRun_sinkRecover_early (k + 2) (k + 2) (by omega)
  have hs0' : expRun (sinkRecover (k + 2)) (k + 2) (k + 2) 0 = k + 2 := by rw [hs0]; omega
  have hh0 : hitCount (sinkRecover (k + 2)) 0 (k + 2) (2 * k + 10) = 6 := by
    rw [hitCount, missCount_sinkRecover_zero, missCount_sinkRecover_zero]; omega
  have hh1 : hitCount (sinkRecover (k + 2)) 1 (k + 2) (2 * k + 10) = k + 2 := by
    rw [hitCount, missCount_sinkRecover_one, missCount_sinkRecover_one]; omega
  have hpk : (0 : ℚ) < (2 : ℚ) ^ (k + 2) := by positivity
  have hw : ∀ i : Fin 2,
      ((raw (wRun (2 ^ (k + 2)) (missFit (sinkRecover (k + 2))) (2 * k + 10)) i : ℕ) : ℚ)
        = (2 : ℚ) ^ expRun (sinkRecover (k + 2)) (k + 2) (2 * k + 10) i := by
    intro i
    rw [wRun_eq_pow_expRun]
    push_cast
    ring
  have hwsum : ∑ j, ((raw (wRun (2 ^ (k + 2)) (missFit (sinkRecover (k + 2)))
      (2 * k + 10)) j : ℕ) : ℚ) = 2 * 2 ^ (k + 2) := by
    rw [Fin.sum_univ_two, hw 0, hw 1, he0, he1']
    ring
  have hd : ∀ i : Fin 2,
      toDist (raw (wRun (2 ^ (k + 2)) (missFit (sinkRecover (k + 2))) (2 * k + 10))) i
        = (2 : ℚ) ^ expRun (sinkRecover (k + 2)) (k + 2) (2 * k + 10) i / (2 * 2 ^ (k + 2)) := by
    intro i
    change ((raw (wRun (2 ^ (k + 2)) (missFit (sinkRecover (k + 2))) (2 * k + 10)) i : ℕ) : ℚ)
      / ∑ j, ((raw (wRun (2 ^ (k + 2)) (missFit (sinkRecover (k + 2)))
        (2 * k + 10)) j : ℕ) : ℚ) = _
    rw [hw i, hwsum]
  have hb : ∀ i : Fin 2,
      ((bayesFrom (sinkRecover (k + 2)) (k + 2) (k + 2) (2 * k + 10) i : ℕ) : ℚ)
        = (2 : ℚ) ^ (expRun (sinkRecover (k + 2)) (k + 2) (k + 2) i
            + hitCount (sinkRecover (k + 2)) i (k + 2) (2 * k + 10)) := by
    intro i
    rw [bayesFrom_eq_pow]
    push_cast
    ring
  have hbsum : ∑ j, ((bayesFrom (sinkRecover (k + 2)) (k + 2) (k + 2)
      (2 * k + 10) j : ℕ) : ℚ) = 65 * 2 ^ (k + 2) := by
    rw [Fin.sum_univ_two, hb 0, hb 1, hs0', hs1, hh0, hh1,
      show k + 2 + 6 = (k + 2) + 6 by omega, show (0 : ℕ) + (k + 2) = k + 2 by omega, pow_add]
    ring
  have hbd : ∀ i : Fin 2, toDist (bayesFrom (sinkRecover (k + 2)) (k + 2) (k + 2)
      (2 * k + 10)) i
        = (2 : ℚ) ^ (expRun (sinkRecover (k + 2)) (k + 2) (k + 2) i
            + hitCount (sinkRecover (k + 2)) i (k + 2) (2 * k + 10)) / (65 * 2 ^ (k + 2)) := by
    intro i
    change ((bayesFrom (sinkRecover (k + 2)) (k + 2) (k + 2) (2 * k + 10) i : ℕ) : ℚ)
      / ∑ j, ((bayesFrom (sinkRecover (k + 2)) (k + 2) (k + 2) (2 * k + 10) j : ℕ) : ℚ) = _
    rw [hb i, hbsum]
  rw [Fin.sum_univ_two, hd 0, hd 1, hbd 0, hbd 1, he0, he1', hs0', hs1, hh0, hh1]
  rw [show (2 : ℚ) ^ (k + 2) / (2 * 2 ^ (k + 2)) = 1 / 2 by field_simp,
    show (2 : ℚ) ^ (k + 2 + 6) / (65 * 2 ^ (k + 2)) = 64 / 65 by
      rw [pow_add]; field_simp; ring,
    show (2 : ℚ) ^ ((0 : ℕ) + (k + 2)) / (65 * 2 ^ (k + 2)) = 1 / 65 by
      rw [show (0 : ℕ) + (k + 2) = k + 2 by omega]; field_simp]
  norm_num

/-- **The tracking bound is refutable without a never-missing candidate.** Co-leadership at `s`
holds — `sinkRecover_coleader` — and the conclusion still fails at every budget `b = k + 2`, the
discrepancy staying at `63/65` against a bound already `1/2` at `b = 2`. So the two hypotheses of
`toDist_wRun_sub_bayesFrom_le` are independent, and neither can be dropped. -/
theorem toDist_wRun_sub_bayesFrom_not_le_sinkRecover (k : ℕ) :
    ¬ (∑ i, |toDist (raw (wRun (2 ^ (k + 2)) (missFit (sinkRecover (k + 2))) (2 * k + 10))) i
          - toDist (bayesFrom (sinkRecover (k + 2)) (k + 2) (k + 2) (2 * k + 10)) i|
        ≤ 2 * (((2 : ℕ) : ℚ) - 1) / 2 ^ (k + 2)) := by
  rw [toDist_wRun_sub_bayesFrom_sinkRecover k]
  have h4 : (4 : ℚ) ≤ (2 : ℚ) ^ (k + 2) := by
    calc (4 : ℚ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (k + 2) := pow_le_pow_right₀ (by norm_num) (by omega)
  intro hle
  rw [le_div_iff₀ (by positivity : (0 : ℚ) < (2 : ℚ) ^ (k + 2))] at hle
  push_cast at hle
  linarith

end Accumulation

/-! ## The reading settles

Everything above prices the *distribution* the floored run carries. This section is about its
**reading** — `argmax` of the weight vector, which is what the frame of [Inevitability] §6 hands the
guest — and it needs no new estimate: it is the saturation normal form, read through `argmax`'s own
tie-breaking.

In one line: under realizability the closed form's maximum `2 ^ min t b` is attained **exactly** at
the candidates whose miss count is zero, so the ceiling set *is* the version space, and the reading
is the least-indexed candidate that has never missed. The version space is antitone in `t` and never
empty, so that index is non-decreasing and bounded by the candidate count — the reading changes at
most `C − 1` times and is eventually constant, on a candidate consistent with the whole trajectory.

What drives it is **fitness alone**. The weighted fiber's generation is
`pack ∘ project ∘ bayesStep`: selection, with the floor as its mutation kernel and no variation
rule whatever. The settled
populations elsewhere in the development are *imposed* — a rule overwrites every slot and the
fitness is never consulted — where here the misses eliminate competitors from the ceiling and
nothing else does.

The scope is the same realizability the drift bound needs and the agnostic event bound does not: a
candidate that never misses **along the observed trajectory**. Where even the best candidate misses
— a noisy base — none of this applies, and `floorSurprise_card_mul_le_missCount` is the instrument
there instead. -/

section Settling

variable {C : ℕ}

/-- **The ceiling of a realizable run.** The heaviest weight at time `t` is `2 ^ min t b`: no
candidate can be above the clipped horizon, and the never-missing one sits exactly on it. -/
theorem wMax_wRun_realizable (M : ℕ → Fin C → Bool) {iR : Fin C} (hR : ∀ t, M t iR = false)
    (b t : ℕ) : wMax (raw (wRun (2 ^ b) (missFit M) t)) = 2 ^ min t b := by
  refine le_antisymm (Finset.sup_le fun i _ => ?_) ?_
  · rw [wRun_eq_pow_deficit M hR b t i]
    exact Nat.pow_le_pow_right (by norm_num) (Nat.sub_le _ _)
  · have h := le_wMax (raw (wRun (2 ^ b) (missFit M) t)) iR
    rwa [wRun_eq_pow_deficit M hR b t iR, missCount_eq_zero M hR t, Nat.sub_zero] at h

/-- **The ceiling set is the version space.** A candidate carries the maximum weight exactly when it
has never missed — an identity holding at every time, not an asymptotic statement, and on both sides
of the horizon.

The guard `1 ≤ min t b` is where the content sits: at `min t b = 0` every weight is `2 ^ 0`, the
whole pool ties at the ceiling, and the equivalence degenerates. -/
theorem raw_wRun_eq_wMax_iff (M : ℕ → Fin C → Bool) {iR : Fin C} (hR : ∀ t, M t iR = false)
    {b t : ℕ} (ht : 1 ≤ min t b) (i : Fin C) :
    raw (wRun (2 ^ b) (missFit M) t) i = wMax (raw (wRun (2 ^ b) (missFit M) t))
      ↔ missCount M i t = 0 := by
  rw [wRun_eq_pow_deficit M hR b t i, wMax_wRun_realizable M hR b t]
  refine ⟨fun h => ?_, fun h => by rw [h, Nat.sub_zero]⟩
  have := Nat.pow_right_injective (le_refl 2) h
  omega

/-- **The reading is the least never-missing candidate**, in the characterization pair a consumer
wants: the reading has itself never missed, and it is at or below every candidate that has not. -/
theorem argmax_wRun_eq_least_consistent [NeZero C] (M : ℕ → Fin C → Bool) {iR : Fin C}
    (hR : ∀ t, M t iR = false) {b t : ℕ} (ht : 1 ≤ min t b) :
    missCount M (argmax (raw (wRun (2 ^ b) (missFit M) t))) t = 0 ∧
      ∀ j, missCount M j t = 0 → argmax (raw (wRun (2 ^ b) (missFit M) t)) ≤ j :=
  ⟨(raw_wRun_eq_wMax_iff M hR ht _).mp (argmax_eq_wMax _),
    fun j hj => argmax_le_of_eq_wMax ((raw_wRun_eq_wMax_iff M hR ht j).mpr hj)⟩

/-- Before the first rescale — at `t = 0`, or on a budget of one quantum — every weight is `2 ^ 0`
and the pool ties, so the tie-keeping fold returns the first candidate. No realizability is
involved, and this is what lets the two convergence statements below carry no guard on `b` or
`t`. -/
theorem argmax_wRun_of_min_eq_zero [NeZero C] (M : ℕ → Fin C → Bool) {b t : ℕ}
    (h : min t b = 0) : argmax (raw (wRun (2 ^ b) (missFit M) t)) = 0 := by
  have hone : ∀ i, raw (wRun (2 ^ b) (missFit M) t) i = 1 := by
    intro i
    rw [wRun_eq_pow_expRun]
    have he : expRun M b t i = 0 := by
      rcases Nat.eq_zero_or_pos t with rfl | htp
      · rfl
      · have := expRun_le M b t i
        omega
    rw [he, pow_zero]
  have hmax : wMax (raw (wRun (2 ^ b) (missFit M) t)) = 1 :=
    le_antisymm (Finset.sup_le fun i _ => le_of_eq (hone i))
      ((le_of_eq (hone 0).symm).trans (le_wMax _ 0))
  exact le_antisymm (argmax_le_of_eq_wMax (by rw [hone 0, hmax])) (Fin.zero_le _)

/-- **The reading never moves back.** The version space is antitone in the horizon, so its least
element is non-decreasing — and with no guard: before the first rescale the reading sits at `0`. -/
theorem argmax_wRun_mono [NeZero C] (M : ℕ → Fin C → Bool) {iR : Fin C} (hR : ∀ t, M t iR = false)
    (b : ℕ) {t t' : ℕ} (h : t ≤ t') :
    (argmax (raw (wRun (2 ^ b) (missFit M) t)) : ℕ)
      ≤ (argmax (raw (wRun (2 ^ b) (missFit M) t')) : ℕ) := by
  rcases Nat.eq_zero_or_pos (min t b) with h0 | ht
  · rw [argmax_wRun_of_min_eq_zero M h0]
    simp
  · have ht' : 1 ≤ min t' b := by omega
    have hz := (argmax_wRun_eq_least_consistent M hR ht').1
    exact (argmax_wRun_eq_least_consistent M hR ht).2 _
      (Nat.le_zero.mp ((missCount_mono M _ h).trans hz.le))

/-- A non-decreasing `ℕ`-valued sequence below a fixed bound is eventually constant. The bound is
what makes the supremum attained; without it `ℕ`'s `sSup` would answer `0`.

Stated of a bare sequence and used twice: here for the reading's index, bounded by the candidate
count, and in `BasinSettling` for a never-missing candidate's weight, bounded by the budget. -/
theorem exists_eventually_const_of_monotone {K : ℕ} (g : ℕ → ℕ)
    (hmono : ∀ {t t' : ℕ}, t ≤ t' → g t ≤ g t') (hlt : ∀ t, g t < K) :
    ∃ T, ∀ t, T ≤ t → g t = g T := by
  have hbdd : BddAbove (Set.range g) := ⟨K, by rintro _ ⟨t, rfl⟩; exact (hlt t).le⟩
  obtain ⟨T, hT⟩ := Nat.sSup_mem (Set.range_nonempty g) hbdd
  refine ⟨T, fun t htT => le_antisymm ?_ (hmono htT)⟩
  rw [hT]
  exact le_csSup hbdd (Set.mem_range_self t)

/-- **Selection settles.** The reading is eventually constant — pathwise, from the run's own
all-ones start, with realizability along the observed trajectory the only hypothesis.

The proof is the two facts above and nothing else: the reading is the least element of the version
space, which is antitone, so the reading's index is a non-decreasing natural number below `C`. -/
theorem argmax_wRun_eventually_const [NeZero C] (M : ℕ → Fin C → Bool) {iR : Fin C}
    (hR : ∀ t, M t iR = false) (b : ℕ) :
    ∃ T : ℕ, ∀ t, T ≤ t →
      argmax (raw (wRun (2 ^ b) (missFit M) t)) = argmax (raw (wRun (2 ^ b) (missFit M) T)) := by
  obtain ⟨T, hT⟩ :=
    exists_eventually_const_of_monotone (K := C)
      (fun t => ((argmax (raw (wRun (2 ^ b) (missFit M) t)) : Fin C) : ℕ))
      (fun h => argmax_wRun_mono M hR b h) (fun t => Fin.is_lt _)
  exact ⟨T, fun t htT => Fin.val_injective (hT t htT)⟩

/-- **At most `C − 1` changes.** The reading is a non-decreasing index in `Fin C`, so over any
horizon the steps at which it moves are at most one short of the candidate count — the version
space can shed its least element only that often. -/
theorem argmax_wRun_card_changes_le [NeZero C] (M : ℕ → Fin C → Bool) {iR : Fin C}
    (hR : ∀ t, M t iR = false) (b n : ℕ) :
    ((Finset.range n).filter fun t =>
        argmax (raw (wRun (2 ^ b) (missFit M) (t + 1)))
          ≠ argmax (raw (wRun (2 ^ b) (missFit M) t))).card ≤ C - 1 := by
  have hmono : Monotone fun t => ((argmax (raw (wRun (2 ^ b) (missFit M) t)) : Fin C) : ℕ) :=
    fun _ _ h => argmax_wRun_mono M hR b h
  calc ((Finset.range n).filter fun t =>
          argmax (raw (wRun (2 ^ b) (missFit M) (t + 1)))
            ≠ argmax (raw (wRun (2 ^ b) (missFit M) t))).card
      = ∑ t ∈ Finset.range n, if argmax (raw (wRun (2 ^ b) (missFit M) (t + 1)))
            ≠ argmax (raw (wRun (2 ^ b) (missFit M) t)) then 1 else 0 := Finset.card_filter _ _
    _ ≤ ∑ t ∈ Finset.range n,
          (((argmax (raw (wRun (2 ^ b) (missFit M) (t + 1))) : Fin C) : ℕ)
            - ((argmax (raw (wRun (2 ^ b) (missFit M) t)) : Fin C) : ℕ)) := by
        refine Finset.sum_le_sum fun t _ => ?_
        have hst : ((argmax (raw (wRun (2 ^ b) (missFit M) t)) : Fin C) : ℕ)
            ≤ ((argmax (raw (wRun (2 ^ b) (missFit M) (t + 1))) : Fin C) : ℕ) :=
          hmono (Nat.le_succ t)
        by_cases hne : argmax (raw (wRun (2 ^ b) (missFit M) (t + 1)))
            = argmax (raw (wRun (2 ^ b) (missFit M) t))
        · simp [hne]
        · rw [if_pos hne]
          have : ((argmax (raw (wRun (2 ^ b) (missFit M) (t + 1))) : Fin C) : ℕ)
              ≠ ((argmax (raw (wRun (2 ^ b) (missFit M) t)) : Fin C) : ℕ) :=
            fun hv => hne (Fin.val_injective hv)
          omega
    _ = ((argmax (raw (wRun (2 ^ b) (missFit M) n)) : Fin C) : ℕ)
          - ((argmax (raw (wRun (2 ^ b) (missFit M) 0)) : Fin C) : ℕ) :=
        Finset.sum_range_tsub hmono n
    _ ≤ C - 1 := by
        have := Fin.is_lt (argmax (raw (wRun (2 ^ b) (missFit M) n)))
        omega

end Settling

/-! ## The (P)/(I) separation: the least-recently-wrong rotation

Two repair counters have read the same trajectory throughout this file without ever being compared:
`argmax_wRun_card_changes_le`'s count of reading changes, and `floorSurpriseSet`'s count of
wrong-mass surprises. Nothing proved above ties them together, and the family below is the witness
that they are not tied — a run whose reading is dethroned at **every** step while the surprise set
stays **empty**, so no bound in one counter transfers to the other.

The construction: `C` candidates on a round-robin, candidate `i` missing exactly at the times
`t ≡ i (mod C)`. At every step the heaviest candidate is the one that missed longest ago — which is
exactly the one about to miss next — so the reading changes every step; and because the wrong mass
is spread over one candidate among `C` near-uniform weights, it never climbs past a fixed floor. The
two counters read the same run and disagree completely: `C − 1` reading changes forced into `T`, and
a wrong-mass surprise count forced to `0`.

The reading is the classical follow-the-leader rule, and its oscillation under an adversarial,
round-robin schedule is textbook — the reason online prediction is done with the *mixture* rather
than the leader — already cited in-corpus via Lattimore–Hutter–Sunehag ([Discovery] §3.3). What is
new here is not the reading but the pairing: one family exhibiting both counters at their opposite
extremes simultaneously, where the families already in this file (`everyMiss`, `allMiss`) each move
only one counter. -/

section Rotation

variable {C : ℕ} [NeZero C]

/-- **The least-recently-wrong rotation.** Candidate `i` misses exactly at the times `t` with
`t ≡ i (mod C)`, so no candidate is realizable (`rotMiss_not_realizable`) and every candidate misses
on a period of exactly `C`. -/
def rotMiss (C : ℕ) : ℕ → Fin C → Bool := fun t i => decide ((i : ℕ) = t % C)

omit [NeZero C] in
theorem rotMiss_not_realizable (i : Fin C) : ¬ ∀ t, rotMiss C t i = false := by
  intro h
  have := h (i : ℕ)
  simp only [rotMiss, decide_eq_false_iff_not] at this
  exact this (Nat.mod_eq_of_lt i.2).symm

omit [NeZero C] in
private theorem rotMiss_periodic (i : Fin C) (t : ℕ) : rotMiss C (C + t) i = rotMiss C t i := by
  simp [rotMiss, Nat.add_mod_left]

omit [NeZero C] in
private theorem missCount_rotMiss_base (i : Fin C) {t : ℕ} (ht : t ≤ C) :
    missCount (rotMiss C) i t = if (i : ℕ) < t then 1 else 0 := by
  induction t with
  | zero => simp [missCount_zero]
  | succ t ih =>
      have ht' : t ≤ C := by omega
      rw [missCount_succ, ih ht']
      have hmod : t % C = t := Nat.mod_eq_of_lt (by omega)
      change _ + (if (decide ((i : ℕ) = t % C) = true) then 1 else 0) = _
      rw [hmod]
      by_cases h : (i : ℕ) = t
      · simp [h]
      · by_cases h2 : (i : ℕ) < t
        · simp [h, h2]; omega
        · simp [h, h2]; omega

omit [NeZero C] in
private theorem missCount_rotMiss_peel (i : Fin C) (t : ℕ) :
    missCount (rotMiss C) i (C + t) = missCount (rotMiss C) i t + 1 := by
  induction t with
  | zero =>
      have hb := missCount_rotMiss_base (C := C) i (le_refl C)
      simp only [Nat.add_zero]
      rw [hb]
      have : (i : ℕ) < C := i.2
      simp [this, missCount_zero]
  | succ t ih =>
      have step1 : C + (t + 1) = (C + t) + 1 := by omega
      rw [step1, missCount_succ, ih, missCount_succ, rotMiss_periodic]
      omega

/-- **The rotation's miss count, in closed form.** Candidate `i` has missed `⌊t/C⌋` times by time
`t`, plus one more exactly when its own residue has already come up in the current partial
period — the general-`C` analogue of `expRun_altMiss`'s exponents, one level down. -/
theorem missCount_rotMiss (i : Fin C) (t : ℕ) :
    missCount (rotMiss C) i t = t / C + (if (i : ℕ) < t % C then 1 else 0) := by
  have hCpos : 0 < C := Nat.pos_of_ne_zero (NeZero.ne C)
  induction t using Nat.strong_induction_on with
  | _ t ih =>
      rcases lt_or_ge t C with hlt | hge
      · rw [missCount_rotMiss_base i hlt.le, Nat.div_eq_of_lt hlt, Nat.mod_eq_of_lt hlt]
        simp
      · obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le hge
        have hlts : s < C + s := by omega
        rw [missCount_rotMiss_peel, ih s hlts, Nat.add_comm C s, Nat.add_div_right s hCpos,
          Nat.add_mod_right]
        omega

/-- **The rotation's exponents below the horizon.** Composes the hypothesis-free hub
(`expRun_eq_sub_missCount_of_le`) with the miss count above: candidate `i` sits one doubling behind
the leader exactly while its own residue has already come up this period. -/
theorem expRun_rotMiss_of_le (b : ℕ) {t : ℕ} (ht : t ≤ b) (i : Fin C) :
    expRun (rotMiss C) b t i = t - (t / C + (if (i : ℕ) < t % C then 1 else 0)) := by
  rw [expRun_eq_sub_missCount_of_le (rotMiss C) b t ht i, missCount_rotMiss i t]

/-- **The running ceiling, below the horizon.** Every candidate whose residue has not yet come up
this period ties for the maximum, at `t − ⌊t/C⌋` — in particular the candidate about to miss, whose
own residue is exactly `t % C` and so is never `< t % C`. -/
theorem wMax_wRun_rotMiss (b : ℕ) {t : ℕ} (ht : t ≤ b) :
    wMax (raw (wRun (2 ^ b) (missFit (rotMiss C)) t)) = 2 ^ (t - t / C) := by
  have hCpos : 0 < C := Nat.pos_of_ne_zero (NeZero.ne C)
  refine le_antisymm (Finset.sup_le fun i _ => ?_) ?_
  · rw [wRun_eq_pow_expRun, expRun_rotMiss_of_le b ht i]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  · have h := le_wMax (raw (wRun (2 ^ b) (missFit (rotMiss C)) t))
      (⟨t % C, Nat.mod_lt t hCpos⟩ : Fin C)
    rwa [wRun_eq_pow_expRun, expRun_rotMiss_of_le b ht, if_neg (lt_irrefl _)] at h

private theorem raw_wRun_rotMiss_eq_wMax_iff (b : ℕ) {t : ℕ} (ht : t ≤ b) (i : Fin C) :
    raw (wRun (2 ^ b) (missFit (rotMiss C)) t) i
      = wMax (raw (wRun (2 ^ b) (missFit (rotMiss C)) t)) ↔ ¬ (i : ℕ) < t % C := by
  have hmc := missCount_le (rotMiss C) i t
  rw [missCount_rotMiss] at hmc
  rw [wRun_eq_pow_expRun, expRun_rotMiss_of_le b ht i, wMax_wRun_rotMiss b ht]
  constructor
  · intro h
    have := Nat.pow_right_injective (le_refl 2) h
    by_contra hlt
    rw [if_pos hlt] at this hmc
    omega
  · intro h
    rw [if_neg h, Nat.add_zero]

/-- **The reading is the candidate about to miss.** Among the tied ceiling-holders `argmax`'s own
tie-break keeps the least index, and that index is exactly `t % C` — the maximum weight sits on
whoever missed longest ago, which is precisely who misses next. -/
theorem argmax_wRun_rotMiss (b : ℕ) {t : ℕ} (ht : t ≤ b) :
    argmax (raw (wRun (2 ^ b) (missFit (rotMiss C)) t))
      = (⟨t % C, Nat.mod_lt t (Nat.pos_of_ne_zero (NeZero.ne C))⟩ : Fin C) := by
  set rIdx : Fin C := ⟨t % C, Nat.mod_lt t (Nat.pos_of_ne_zero (NeZero.ne C))⟩ with hrIdx
  have hR : raw (wRun (2 ^ b) (missFit (rotMiss C)) t) rIdx
      = wMax (raw (wRun (2 ^ b) (missFit (rotMiss C)) t)) :=
    (raw_wRun_rotMiss_eq_wMax_iff b ht rIdx).mpr (lt_irrefl _)
  have hle1 : argmax (raw (wRun (2 ^ b) (missFit (rotMiss C)) t)) ≤ rIdx :=
    argmax_le_of_eq_wMax hR
  have hA : raw (wRun (2 ^ b) (missFit (rotMiss C)) t)
      (argmax (raw (wRun (2 ^ b) (missFit (rotMiss C)) t)))
      = wMax (raw (wRun (2 ^ b) (missFit (rotMiss C)) t)) :=
    argmax_eq_wMax _
  have hle2 : rIdx ≤ argmax (raw (wRun (2 ^ b) (missFit (rotMiss C)) t)) :=
    Fin.not_lt.mp ((raw_wRun_rotMiss_eq_wMax_iff b ht _).mp hA)
  exact le_antisymm hle1 hle2

/-- **The (I) side: the reading is dethroned at every single step.** Consecutive residues mod `C`
never coincide once `C ≥ 2`, so the least-recently-wrong index moves at every step — the change
count `argmax_wRun_card_changes_le` bounds by `C − 1` is realized maximally on any horizon inside
the budget, one change per step rather than merely a nonzero rate. -/
theorem argmax_wRun_rotMiss_ne_succ (hC2 : 2 ≤ C) (b : ℕ) {t : ℕ} (ht : t + 1 ≤ b) :
    argmax (raw (wRun (2 ^ b) (missFit (rotMiss C)) (t + 1)))
      ≠ argmax (raw (wRun (2 ^ b) (missFit (rotMiss C)) t)) := by
  rw [argmax_wRun_rotMiss b ht, argmax_wRun_rotMiss b (by omega : t ≤ b)]
  intro hcontra
  have hval : (t + 1) % C = t % C := congrArg Fin.val hcontra
  have hCpos : 0 < C := Nat.pos_of_ne_zero (NeZero.ne C)
  have hr : t % C < C := Nat.mod_lt t hCpos
  have hstep : (t + 1) % C = (t % C + 1) % C := by
    conv_lhs => rw [← Nat.mod_add_div t C]
    rw [Nat.add_right_comm, Nat.add_mul_mod_self_left]
  rw [hstep] at hval
  rcases Nat.lt_or_ge (t % C + 1) C with h | h
  · rw [Nat.mod_eq_of_lt h] at hval
    omega
  · have heqC : t % C + 1 = C := by omega
    rw [heqC, Nat.mod_self] at hval
    omega

/-- **The sum of weights, below the horizon.** The `t % C` candidates whose residue has already come
up this period hold one doubling less than the rest. -/
theorem sum_raw_wRun_rotMiss (b : ℕ) {t : ℕ} (ht : t ≤ b) :
    ∑ i, raw (wRun (2 ^ b) (missFit (rotMiss C)) t) i
      = (t % C) * 2 ^ (t - t / C - 1) + (C - t % C) * 2 ^ (t - t / C) := by
  have hCpos : 0 < C := Nat.pos_of_ne_zero (NeZero.ne C)
  have hrC : t % C ≤ C := (Nat.mod_lt t hCpos).le
  have hcongr : ∀ i : Fin C, raw (wRun (2 ^ b) (missFit (rotMiss C)) t) i
      = 2 ^ (t - t / C - (if (i : ℕ) < t % C then 1 else 0)) := by
    intro i
    rw [wRun_eq_pow_expRun, expRun_rotMiss_of_le b ht i]
    congr 1
    omega
  rw [Finset.sum_congr rfl (fun i _ => hcongr i), Fin.sum_univ_eq_sum_range
    (fun j => 2 ^ (t - t / C - (if j < t % C then 1 else 0)))]
  rw [show Finset.range C = Finset.range (t % C) ∪ Finset.Ico (t % C) C by
    rw [Finset.range_eq_Ico, Finset.range_eq_Ico]; exact (Finset.Ico_union_Ico_eq_Ico
      (Nat.zero_le _) hrC).symm]
  rw [Finset.sum_union (by
    rw [Finset.range_eq_Ico]
    exact Finset.Ico_disjoint_Ico_consecutive 0 (t % C) C)]
  have hleft : ∑ j ∈ Finset.range (t % C), (2 : ℕ) ^ (t - t / C - (if j < t % C then 1 else 0))
      = (t % C) * 2 ^ (t - t / C - 1) := by
    rw [Finset.sum_congr rfl (fun j hj => by
      rw [if_pos (Finset.mem_range.mp hj)]), Finset.sum_const, Finset.card_range, smul_eq_mul]
  have hright : ∑ j ∈ Finset.Ico (t % C) C, (2 : ℕ) ^ (t - t / C - (if j < t % C then 1 else 0))
      = (C - t % C) * 2 ^ (t - t / C) := by
    rw [Finset.sum_congr rfl (fun j hj => by
      rw [if_neg (not_lt.mpr (Finset.mem_Ico.mp hj).1), Nat.sub_zero]), Finset.sum_const,
      Nat.card_Ico, smul_eq_mul]
  rw [hleft, hright]

/-- **The (P) side, in closed form.** The candidate about to miss carries the whole ceiling weight,
so the wrong mass at time `t` is exactly `2 / (2C − t % C)` — bounded, uniformly in `t`, well below
`1`. -/
theorem wrongMass_rotMiss (b : ℕ) {t : ℕ} (ht : t ≤ b) :
    wrongMass (rotMiss C) b t = 2 / (2 * (C : ℚ) - ((t % C : ℕ) : ℚ)) := by
  have hCpos : 0 < C := Nat.pos_of_ne_zero (NeZero.ne C)
  have hrC : t % C < C := Nat.mod_lt t hCpos
  have hcond : rotMiss C t (⟨t % C, hrC⟩ : Fin C) = true := by simp [rotMiss]
  have hsingle : wrongMass (rotMiss C) b t
      = toDist (raw (wRun (2 ^ b) (missFit (rotMiss C)) t)) (⟨t % C, hrC⟩ : Fin C) := by
    rw [wrongMass, Finset.sum_eq_single (⟨t % C, hrC⟩ : Fin C)]
    · rw [if_pos hcond]
    · intro i _ hi
      rw [if_neg]
      simp only [rotMiss, decide_eq_true_eq]
      intro hcontra
      exact hi (Fin.ext hcontra)
    · intro h
      exact absurd (Finset.mem_univ _) h
  rw [hsingle]
  have hnum : raw (wRun (2 ^ b) (missFit (rotMiss C)) t) (⟨t % C, hrC⟩ : Fin C)
      = 2 ^ (t - t / C) := by
    rw [wRun_eq_pow_expRun, expRun_rotMiss_of_le b ht, if_neg (lt_irrefl (t % C)), Nat.add_zero]
  have hden : ∑ i, raw (wRun (2 ^ b) (missFit (rotMiss C)) t) i
      = (t % C) * 2 ^ (t - t / C - 1) + (C - t % C) * 2 ^ (t - t / C) := sum_raw_wRun_rotMiss b ht
  rcases Nat.eq_zero_or_pos (t % C) with hr0 | hrpos
  · rw [show toDist (raw (wRun (2 ^ b) (missFit (rotMiss C)) t)) (⟨t % C, hrC⟩ : Fin C)
      = (raw (wRun (2 ^ b) (missFit (rotMiss C)) t) (⟨t % C, hrC⟩ : Fin C) : ℚ)
        / ∑ j, (raw (wRun (2 ^ b) (missFit (rotMiss C)) t) j : ℚ) from rfl]
    rw [hnum, ← Nat.cast_sum, hden, hr0]
    have hCQ : (C : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hCpos.ne'
    push_cast [Nat.sub_zero]
    field_simp
    ring
  · have hmiss0 : missCount (rotMiss C) 0 t = t / C + 1 := by
      rw [missCount_rotMiss]
      simp only [Fin.val_zero]
      simp [hrpos]
    have hK1 : 1 ≤ t - t / C := by
      have := missCount_le (rotMiss C) 0 t
      rw [hmiss0] at this
      omega
    rw [show toDist (raw (wRun (2 ^ b) (missFit (rotMiss C)) t)) (⟨t % C, hrC⟩ : Fin C)
      = (raw (wRun (2 ^ b) (missFit (rotMiss C)) t) (⟨t % C, hrC⟩ : Fin C) : ℚ)
        / ∑ j, (raw (wRun (2 ^ b) (missFit (rotMiss C)) t) j : ℚ) from rfl]
    rw [hnum, ← Nat.cast_sum, hden]
    have hpow : (2 : ℕ) ^ (t - t / C) = 2 * 2 ^ (t - t / C - 1) := by
      obtain ⟨K', hK'⟩ := Nat.exists_eq_add_of_le hK1
      rw [hK']
      simp [pow_add, pow_succ]
    have hCQ : (C : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hCpos.ne'
    have hCQpos : (0 : ℚ) < C := Nat.cast_pos.mpr hCpos
    have hpowQ : (0 : ℚ) < 2 ^ (t - t / C - 1) := by positivity
    have hrCQ : ((t % C : ℕ) : ℚ) ≤ C := by exact_mod_cast hrC.le
    have hrposQ : (0 : ℚ) < ((t % C : ℕ) : ℚ) := by exact_mod_cast hrpos
    push_cast [hpow, Nat.cast_sub hrC.le]
    rw [div_eq_div_iff (by nlinarith) (by nlinarith)]
    ring

/-- **The (P) side: the surprise set stays empty.** The wrong mass peaks at `2/(C+1)` — attained
when the candidate about to miss is the highest-indexed one, `t % C = C − 1` — so any threshold at
or above that floor never sees a surprise, on any horizon inside the budget. -/
theorem floorSurpriseSet_rotMiss_eq_empty (b : ℕ) {θ : ℚ} (hθ : 2 / ((C : ℚ) + 1) ≤ θ) {n : ℕ}
    (hn : n ≤ b) : floorSurpriseSet (rotMiss C) b θ n = ∅ := by
  rw [floorSurpriseSet, Finset.filter_eq_empty_iff]
  intro t ht
  rw [Finset.mem_range] at ht
  rw [wrongMass_rotMiss b (by omega : t ≤ b)]
  have hCpos : 0 < C := Nat.pos_of_ne_zero (NeZero.ne C)
  have hrC : t % C < C := Nat.mod_lt t hCpos
  have hCQpos : (0 : ℚ) < C := Nat.cast_pos.mpr hCpos
  have hrCQ : ((t % C : ℕ) : ℚ) + 1 ≤ C := by exact_mod_cast hrC
  have hbound : (2 : ℚ) / (2 * (C : ℚ) - ((t % C : ℕ) : ℚ)) ≤ 2 / ((C : ℚ) + 1) := by
    apply div_le_div_of_nonneg_left (by norm_num) (by linarith) (by linarith)
  intro hlt
  linarith

/-- **The separation, as one theorem.** At any horizon inside the budget, the identification counter
increments at every step while the prediction-repair set stays empty — so no functional bound in
either currency of [Discovery] §3.3's product form transfers to the other, agnostically. Compare
`everyMiss`/`allMiss` above, each of which moves only one of the two counters. -/
theorem rotMiss_prediction_identification_separation (hC2 : 2 ≤ C) (b n : ℕ) (hn : n ≤ b)
    {θ : ℚ} (hθ : 2 / ((C : ℚ) + 1) ≤ θ) :
    (∀ t < n, argmax (raw (wRun (2 ^ b) (missFit (rotMiss C)) (t + 1)))
        ≠ argmax (raw (wRun (2 ^ b) (missFit (rotMiss C)) t)))
      ∧ floorSurpriseSet (rotMiss C) b θ n = ∅ :=
  ⟨fun t htn => argmax_wRun_rotMiss_ne_succ hC2 b (by omega),
    floorSurpriseSet_rotMiss_eq_empty b hθ hn⟩

/-- **The witness, non-vacuous, at the gate-satisfying parameters `C = 8`, `b = 6`, `θ = 1/4`.** The
reading changes at both ends of the six-step window shown, and — by
`rotMiss_prediction_identification_separation` — at every step in between, so the rotation genuinely
rotates over this range; the surprise set is empty for the reason the theorem above gives, the wrong
mass bounded away from `1/4` by the pricing, not because the range itself is empty. -/
theorem rotMiss_prediction_identification_separation_witness :
    (argmax (raw (wRun (2 ^ 6) (missFit (rotMiss 8)) 1))
        ≠ argmax (raw (wRun (2 ^ 6) (missFit (rotMiss 8)) 0))
      ∧ argmax (raw (wRun (2 ^ 6) (missFit (rotMiss 8)) 6))
        ≠ argmax (raw (wRun (2 ^ 6) (missFit (rotMiss 8)) 5)))
      ∧ floorSurpriseSet (rotMiss 8) 6 (1 / 4) 6 = ∅ := by
  have h := rotMiss_prediction_identification_separation (C := 8) (by norm_num) 6 6 le_rfl
    (θ := 1 / 4) (by norm_num)
  exact ⟨⟨h.1 0 (by norm_num), h.1 5 (by norm_num)⟩, h.2⟩

end Rotation

/-! ## The fiber's reading along a base trajectory

The settling above is stated of the abstract miss indicator. Here it is instantiated at the
construction's own fitness — `predFitPos`, scored against the base's next state — and read through
the frame the pricing assembly uses, so what converges is the guest's reading rather than an
auxiliary sequence. -/

section PredictiveFiber

open SkewFiber

/-- **The skew product's start over a base point**: the base at `x₀`, the fiber at its own all-ones
vector. Nothing is written into the fiber — one reserved quantum per candidate is the uniform
prior — which is what makes the convergence below need no hypothesis on the initial state. -/
def wStartAt (C W : ℕ) {n₁ : ℕ} (x₀ : Fin n₁) : Fin (n₁ * (W + 1) ^ C) :=
  finProdFinEquiv (x₀, finFunctionFinEquiv (pack W (fun _ => 1) : WVec C W))

variable {n₁ C W : ℕ}

/-- **The predictive fiber's miss indicator**: candidate `c` misses at step `t` when the rule it
decodes to mispredicts where the base actually goes, along the trajectory from `x₀`. -/
def predMiss (S : Fin n₁ → Fin n₁) (dec : Fin C → Fin n₁ → Fin n₁) (x₀ : Fin n₁) :
    ℕ → Fin C → Bool :=
  fun t c => decide (dec c (S^[t] x₀) ≠ S (S^[t] x₀))

/-- **The bridge**: the abstract `2`-vs-`1` fitness driven by `predMiss` *is* predictive fitness
read along the base trajectory. Every result above therefore applies to the fiber at the cost of
this one rewrite — the base dynamics, the decoder and the candidates' predictions having been
abstracted into the indicator in the first place. -/
theorem missFit_predMiss (S : Fin n₁ → Fin n₁) (dec : Fin C → Fin n₁ → Fin n₁) (x₀ : Fin n₁)
    (t : ℕ) : missFit (predMiss S dec x₀) t = predFitPos S dec (S^[t] x₀) := by
  funext c
  rw [missFit, predMiss, predFitPos]
  by_cases h : dec c (S^[t] x₀) = S (S^[t] x₀) <;> simp [h]

/-- **The fiber coordinate of the skew run is the abstract run.** The base drives the fiber and
never reads it, so `t` steps of `wWorld` from the all-ones start leave the base at `S^[t] x₀` and
the fiber at `wRun`'s own `t`-th vector under the fitness sampled along that trajectory. -/
theorem iterate_wWorld_wStartAt (S : Fin n₁ → Fin n₁) (fit : Fin n₁ → Fin C → ℕ) (x₀ : Fin n₁)
    (t : ℕ) :
    (wWorld W S fit)^[t] (wStartAt C W x₀)
      = finProdFinEquiv (S^[t] x₀,
          finFunctionFinEquiv (wRun W (fun s => fit (S^[s] x₀)) t)) := by
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [Function.iterate_succ_apply', ih, wWorld, skewWorldFin_apply, wFiber,
        Equiv.symm_apply_apply, ← Function.iterate_succ_apply' S t x₀]
      rfl

/-- The frame's reading of the skew run, in the abstract run's own terms. -/
theorem argmaxFrame_iterate_wWorld [NeZero C] (S : Fin n₁ → Fin n₁) (fit : Fin n₁ → Fin C → ℕ)
    (x₀ : Fin n₁) (t : ℕ) :
    argmaxFrame n₁ W ((wWorld W S fit)^[t] (wStartAt C W x₀))
      = argmax (raw (wRun W (fun s => fit (S^[s] x₀)) t)) := by
  rw [iterate_wWorld_wStartAt]
  simp only [argmaxFrame, Equiv.symm_apply_apply]

/-- **The fittest reading settles, along the base trajectory** ([Inevitability] §6).

Score the candidates by `predFitPos` against the base's own next state and start the fiber from its
all-ones vector over any base point `x₀`. If *some* candidate decodes to a rule that predicts the
base correctly at every step of that trajectory, then the frame's reading is eventually constant, at
a candidate that agrees with the base at every step of the trajectory.

Three readings the statement supports. It is **pathwise**: hypothesis and conclusion both live on
one trajectory and there is no hypothesis on `x₀` at all, so this half of the question asks for no
basin and no measure. It is driven by **fitness alone**: the fiber's generation is the projected
replicator step and carries no variation rule, so nothing imposes the settled shape that the misses
do not. And it says nothing about **coverage** — the pricing assembly's hypothesis is a condition
over initial states of the base coordinate, discharged separately by the base-reading frame, and
neither condition implies the other.

The budget must hold at least two quanta, and `1 ≤ b` is not slack: at `b = 0` every weight is one
quantum forever and the reading is pinned at candidate `0` whether or not it predicts anything. -/
theorem argmaxFrame_wWorld_eventually_const [NeZero C] {b : ℕ} (hb : 1 ≤ b)
    (S : Fin n₁ → Fin n₁) (dec : Fin C → Fin n₁ → Fin n₁) (x₀ : Fin n₁) {c₀ : Fin C}
    (hc₀ : ∀ s, dec c₀ (S^[s] x₀) = S (S^[s] x₀)) :
    ∃ (T : ℕ) (c : Fin C), (∀ s, dec c (S^[s] x₀) = S (S^[s] x₀)) ∧
      ∀ t, T ≤ t →
        argmaxFrame n₁ (2 ^ b) ((wWorld (2 ^ b) S (predFitPos S dec))^[t] (wStartAt C (2 ^ b) x₀))
          = c := by
  have hfit : (fun s => predFitPos S dec (S^[s] x₀)) = missFit (predMiss S dec x₀) := by
    funext s
    exact (missFit_predMiss S dec x₀ s).symm
  have hR : ∀ s, predMiss S dec x₀ s c₀ = false := by
    intro s
    simp [predMiss, hc₀ s]
  obtain ⟨T₀, hT₀⟩ := argmax_wRun_eventually_const (predMiss S dec x₀) hR b
  refine ⟨max T₀ 1, argmax (raw (wRun (2 ^ b) (missFit (predMiss S dec x₀)) T₀)), ?_, ?_⟩
  · intro s
    set t := max (max T₀ 1) (s + 1) with hts
    have h1 : 1 ≤ min t b := by
      have : 1 ≤ t := le_trans (le_trans (le_max_right T₀ 1) (le_max_left _ _)) (le_refl t)
      omega
    have hz := (argmax_wRun_eq_least_consistent (predMiss S dec x₀) hR h1).1
    rw [hT₀ t (le_trans (le_max_left T₀ 1) (le_max_left _ _))] at hz
    have hs : s < t := lt_of_lt_of_le (Nat.lt_succ_self s) (le_max_right _ _)
    have hf := eq_false_of_missCount_eq_zero hz hs
    simpa [predMiss] using hf
  · intro t ht
    rw [argmaxFrame_iterate_wWorld, hfit]
    exact hT₀ t (le_trans (le_max_left T₀ 1) ht)

/-- The same conclusion from the clean sufficient condition — some codeword decodes to the base rule
itself — which is the premise `surjective_predFrame_of_faithful` discharges the pricing assembly's
coverage from. The two halves of [Inevitability] §6's frame question are then stated against one
hypothesis, on one dynamics, with neither derived from the other. -/
theorem argmaxFrame_wWorld_eventually_const_of_faithful [NeZero C] {b : ℕ} (hb : 1 ≤ b)
    (S : Fin n₁ → Fin n₁) (dec : Fin C → Fin n₁ → Fin n₁) (x₀ : Fin n₁) {c₀ : Fin C}
    (hc₀ : ∀ y, dec c₀ y = S y) :
    ∃ (T : ℕ) (c : Fin C), (∀ s, dec c (S^[s] x₀) = S (S^[s] x₀)) ∧
      ∀ t, T ≤ t →
        argmaxFrame n₁ (2 ^ b) ((wWorld (2 ^ b) S (predFitPos S dec))^[t] (wStartAt C (2 ^ b) x₀))
          = c :=
  argmaxFrame_wWorld_eventually_const hb S dec x₀ (fun _ => hc₀ _)

end PredictiveFiber

end WeightedFiber
