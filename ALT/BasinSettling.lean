module

public import ALT.FlooredMixture


/-!
# Settling from every initial weight vector ([Inevitability] §6)

`FlooredMixture`'s settling suite proves the weighted fiber's reading eventually constant **from the
fiber's own uniform start**, on a power-of-two budget, by way of the realizable closed form: the
ceiling set is the version space and the reading is its least element. Neither restriction is
essential to *settling*, and neither survives a seeded start. This file removes both.

The run is restarted from an arbitrary carrier vector (`wRunFrom`), the budget is an arbitrary
`1 ≤ W`, and the closed form is replaced by three monotonicity facts about the generation itself,
none of which mentions a power of two: a never-missing candidate's weight is non-decreasing, its
constancy locks the rescale divisor at `2`, and under that lock no weight rises.

## Main results

* `wRunFrom` / `wRunFrom_pack_one` / `wRunFrom_add` — the run from a given initial weight vector,
  the identification of the uniform start with `wRun`, and **restart invariance**: the run at
  `s + t` is the run restarted at its own state at `s`, under the fitness stream shifted by `s`.
  That identity is not statable over `wRun`, whose start is baked into its definition.
* `raw_wRunFrom_leader_le_succ` — **a never-missing candidate's weight never falls**, exactly: the
  exact step doubles it, and the rescale — a division by `1` or `2` and nothing else, because the
  two-valued fitness cannot more than double the maximum — halves it back at worst.
* `raw_wRunFrom_eventually_const` / `argmax_wRunFrom_eventually_const` — **the whole weight vector
  settles, and with it the reading**, at every budget of at least one quantum and from every vector
  the carrier holds, zeros included. Realizability along the observed trajectory is the only
  hypothesis: no positivity of the start is owed, because the floor absorbs a zero in one step.
* `argmax_wRunFrom_eventually_const_consistent` — **the identity clause**, at `2 ≤ W`: the settled
  reading misses at most finitely often. This is what survives of the version-space
  characterization, and it comes off the divisor lock rather than off a closed form.
* `argmax_wRunFrom_eventually_const_of_eventually_realizable` — the hypothesis a settling story
  actually wants, that *some* candidate misses only finitely often, obtained free from restart
  invariance; `…_consistent_of_eventually_realizable` carries the identity clause the same way.
* `argmaxFrame_wWorld_eventually_const_wStartFrom` — **the same at the fiber's own reading**, over
  the skew product and through the frame the pricing assembly uses, with the fiber coordinate
  started anywhere on the carrier (`wStartFrom`, whose uniform case is `wStartFrom_pack_one`).
  `iterate_wWorld_wStartFrom` and `argmaxFrame_iterate_wWorld_wStartFrom` are the identification of
  the skew run's fiber coordinate with the seeded run. The settled candidate is consistent along
  the **tail** of the trajectory, which is all a seeded start can give — see the version-space
  family below.

## What does not transport, each with its refuting family

* `argmax_wRunFrom_seededAlt_not_mono` and `argmax_wRunFrom_seededAlt_card_changes_eq` — the
  reading's **monotonicity** and its **`C − 1` change count** are privileges of the uniform start.
  Three candidates, the never-missing one seeded at a single quantum and an alternating pair at the
  budget: the reading moves back on its second step, and changes exactly `2b` times before settling
  — unbounded in the budget at a fixed candidate count, so no bound of that shape survives the
  change of initial condition at all. `raw_wRunFrom_seededAlt` is the family's closed form and
  `argmax_wRunFrom_seededAlt` the reading read off it; `argmax_wRunFrom_seededAlt_card_changes_gt`
  is the count in refuting form, and `argmax_wRunFrom_seededAlt_witness` reads the first five steps
  off the kernel independently of the closed form.
* `argmax_wRunFrom_lateHit_missCount_ne_zero` — **version-space membership** does not transport.
  Two candidates, the competitor missing once and seeded at the budget: `raw_wRunFrom_lateHit` has
  the run frozen after a single step, `argmax_wRunFrom_lateHit` reads it on the candidate that
  missed, and a never-missing candidate sits in the pool throughout.
  `argmax_wRunFrom_lateHit_at_two` is the family's own boundary — at two quanta the frozen state
  ties and the tie-keeping fold reads the never-missing candidate after all.
* `argmax_wRunFrom_zeroMiss_misses` — **`2 ≤ W` is necessary** for the identity clause. At one
  quantum every weight is pinned from the first step, the fold sits on candidate `0`, and that
  candidate misses at every step while another never does.
* `argmax_wRun_altMiss_not_eventually_const` — **realizability is load-bearing**, and it refutes
  rather than defers: on the alternating family both candidates miss infinitely often and the
  reading swings between them forever. `argmax_wRunFrom_altMiss_not_eventually_const` reads the same
  refutation at the seeded run, through the start bridge.

Each family carries its own non-vacuity: `seededAlt_realizable`, `lateHit_realizable` and
`zeroMiss_realizable` exhibit the never-missing candidate the settling theorem asks for, so every
refutation above drops exactly the one condition it is about and keeps the rest.

## Scope

Settling is what transports, and it transports strengthened — off the power-of-two carrier, off the
uniform start, and with realizability weakened to a condition on the tail of the miss record.
Everything the uniform-start development proves *about which candidate* the reading settles on is a
privilege of that start, and each failure is exhibited above rather than left open.

What is not here. No **rate**: the argument is monotone convergence of bounded `ℕ`-sequences and
bounds no settling time. No **coverage** statement — that hypothesis quantifies over initial states
of the base coordinate, and neither condition implies the other. And nothing about the race between
discovery and damage, whose survival half is priced elsewhere from a damage model that is a
hypothesis. The event and drift bounds are stated from the uniform start on a power-of-two budget
and are not re-derived here. -/


@[expose] public section

namespace ALT

open WVec

/-! ## The run from an arbitrary initial weight vector -/

section Seeded

variable {C : ℕ}

/-- **The weighted fiber's run from a given initial weight vector.** `wRun`'s start — one reserved
quantum per candidate — is baked into its definition, so a question about *other* initial conditions
cannot even be posed over it. Here the start is a parameter and the dynamics is unchanged. -/
def wRunFrom (W : ℕ) (F : ℕ → Fin C → ℕ) (w₀ : WVec C W) : ℕ → WVec C W
  | 0 => w₀
  | t + 1 => wGen W (F t) (wRunFrom W F w₀ t)

/-- **The uniform start recovers `wRun`.** The seeded run is a genuine generalization and not a
parallel development: at the all-ones vector it is the run every result upstream is stated of. -/
theorem wRunFrom_pack_one (W : ℕ) (F : ℕ → Fin C → ℕ) (t : ℕ) :
    wRunFrom W F (pack W fun _ => 1) t = wRun W F t := by
  induction t with
  | zero => rfl
  | succ t ih => exact congrArg (wGen W (F t)) ih

/-- **Restart invariance, exactly.** Running `s + t` steps is running `t` steps from the state
reached at `s`, under the fitness stream shifted by `s`. An identity with no hypothesis, and the
statement `wRun` cannot make: it is what turns a hypothesis about the *tail* of the miss record into
one about the whole of a restarted run. -/
theorem wRunFrom_add (W : ℕ) (F : ℕ → Fin C → ℕ) (w₀ : WVec C W) (s t : ℕ) :
    wRunFrom W F w₀ (s + t) = wRunFrom W (fun n => F (s + n)) (wRunFrom W F w₀ s) t := by
  induction t with
  | zero => rfl
  | succ t ih => exact congrArg (wGen W (F (s + t))) ih

end Seeded

/-! ## Settling, at every budget and from every start

The three facts the argument runs on, in order.

**One.** A candidate that never misses scores `2` at every step, so its weight is multiplied by `2`
and then divided by the common rescale divisor, which is `1` or `2` and nothing else — the
post-step maximum cannot exceed twice the budget. So its weight either doubles or stands still, and
the floor at one quantum can only raise it. It is non-decreasing, and bounded by the budget, hence
eventually constant at some `V ≥ 1`.

**Two.** That constancy *locks the divisor at* `2`. Were it `1` at some later step the leader's
entry would become `2V`, and `2V = V` forces `V = 0`, which the floor has already excluded.

**Three.** Under the lock every weight is non-increasing: a hit is `2w/2 = w` and a miss is
`max 1 ⌊w/2⌋ ≤ w`. Each coordinate is therefore eventually constant, and — the finitely many
coordinates being handled by their sum, which is itself a non-increasing natural number — the whole
vector is. The reading of an eventually constant vector is eventually constant.

None of the three mentions the budget's shape, the start, or a closed form. -/

section Basin

variable {C W : ℕ}

private theorem raw_le_budget (w : WVec C W) (i : Fin C) : raw w i ≤ W :=
  Nat.lt_succ_iff.mp (w i).isLt

private theorem missFit_le_two (M : ℕ → Fin C → Bool) (t : ℕ) (i : Fin C) :
    missFit M t i ≤ 2 := by rw [missFit]; split <;> omega

private theorem one_le_missFit (M : ℕ → Fin C → Bool) (t : ℕ) (i : Fin C) :
    1 ≤ missFit M t i := by rw [missFit]; split <;> omega

private theorem missFit_eq_two {M : ℕ → Fin C → Bool} {t : ℕ} {i : Fin C} (h : M t i = false) :
    missFit M t i = 2 := by simp [missFit, h]

private theorem missFit_eq_one {M : ℕ → Fin C → Bool} {t : ℕ} {i : Fin C} (h : M t i = true) :
    missFit M t i = 1 := by simp [missFit, h]

/-- The exact step's maximum is at most twice the budget: every weight is inside the budget and
every fitness value is at most `2`. -/
private theorem wMax_bayesStep_le (M : ℕ → Fin C → Bool) (t : ℕ) (w : WVec C W) :
    wMax (bayesStep (missFit M t) (raw w)) ≤ 2 * W :=
  Finset.sup_le fun i _ => by
    rw [bayesStep]
    calc raw w i * missFit M t i ≤ W * 2 :=
          Nat.mul_le_mul (raw_le_budget w i) (missFit_le_two M t i)
      _ = 2 * W := Nat.mul_comm W 2

/-- **The rescale divisor is `1` or `2`, always.** This is the whole of what the two-valued fitness
buys, and it is what replaces the power-of-two carrier: the exact step at most doubles the maximum,
so one halving always suffices to fit the budget again. -/
private theorem scaleDiv_bayesStep_le_two (hW : 1 ≤ W) (M : ℕ → Fin C → Bool) (t : ℕ)
    (w : WVec C W) : scaleDiv W (bayesStep (missFit M t) (raw w)) ≤ 2 := by
  have h := wMax_bayesStep_le M t w
  have hq : (wMax (bayesStep (missFit M t) (raw w)) + W - 1) / W < 3 :=
    Nat.div_lt_of_lt_mul (by omega)
  rw [scaleDiv]
  omega

private theorem raw_wRunFrom_succ (hW : 1 ≤ W) (F : ℕ → Fin C → ℕ) (w₀ : WVec C W) (t : ℕ) :
    raw (wRunFrom W F w₀ (t + 1)) = project W (bayesStep (F t) (raw (wRunFrom W F w₀ t))) :=
  raw_wGen hW _ _

/-- Past the first step no weight is below the reserve, whatever the start was — the floor absorbs a
zero in one generation. This is why no positivity hypothesis on the initial vector is owed. -/
private theorem one_le_raw_wRunFrom_succ (hW : 1 ≤ W) (F : ℕ → Fin C → ℕ) (w₀ : WVec C W)
    (t : ℕ) (i : Fin C) : 1 ≤ raw (wRunFrom W F w₀ (t + 1)) i := by
  rw [raw_wRunFrom_succ hW]
  exact one_le_project W _ i

private theorem one_le_raw_wRunFrom (hW : 1 ≤ W) (F : ℕ → Fin C → ℕ) (w₀ : WVec C W)
    {t : ℕ} (ht : 1 ≤ t) (i : Fin C) : 1 ≤ raw (wRunFrom W F w₀ t) i := by
  obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
  exact one_le_raw_wRunFrom_succ hW F w₀ s i

/-- **A never-missing candidate's weight never falls.** It scores `2` at every step, so the exact
step doubles it and the rescale halves it back at worst; the floor can only raise it further. Exact,
not asymptotic, and with no hypothesis on the start. -/
theorem raw_wRunFrom_leader_le_succ (hW : 1 ≤ W) {M : ℕ → Fin C → Bool} {iR : Fin C}
    (hR : ∀ t, M t iR = false) (w₀ : WVec C W) (t : ℕ) :
    raw (wRunFrom W (missFit M) w₀ t) iR ≤ raw (wRunFrom W (missFit M) w₀ (t + 1)) iR := by
  have hd2 := scaleDiv_bayesStep_le_two hW M t (wRunFrom W (missFit M) w₀ t)
  have hd1 := scaleDiv_pos W (bayesStep (missFit M t) (raw (wRunFrom W (missFit M) w₀ t)))
  have hu : bayesStep (missFit M t) (raw (wRunFrom W (missFit M) w₀ t)) iR
      = 2 * raw (wRunFrom W (missFit M) w₀ t) iR := by
    rw [bayesStep, missFit_eq_two (hR t)]; ring
  rw [raw_wRunFrom_succ hW, project, hu]
  rcases (show scaleDiv W (bayesStep (missFit M t) (raw (wRunFrom W (missFit M) w₀ t))) = 1
      ∨ scaleDiv W (bayesStep (missFit M t) (raw (wRunFrom W (missFit M) w₀ t))) = 2 by
        omega) with h | h
  · rw [h, Nat.div_one]; omega
  · rw [h, Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)]; omega

private theorem raw_wRunFrom_leader_mono (hW : 1 ≤ W) {M : ℕ → Fin C → Bool} {iR : Fin C}
    (hR : ∀ t, M t iR = false) (w₀ : WVec C W) :
    Monotone fun t => raw (wRunFrom W (missFit M) w₀ t) iR :=
  monotone_nat_of_le_succ fun t => raw_wRunFrom_leader_le_succ hW hR w₀ t

/-- **The leader's constancy locks the rescale divisor at `2`.** The divisor is `1` or `2`; at `1`
the never-missing candidate's entry would double, and a weight already at the reserve cannot double
and stay put. -/
private theorem scaleDiv_eq_two_of_leader_const (hW : 1 ≤ W) {M : ℕ → Fin C → Bool} {iR : Fin C}
    (hR : ∀ t, M t iR = false) (w₀ : WVec C W) {t : ℕ} (ht : 1 ≤ t)
    (hconst : raw (wRunFrom W (missFit M) w₀ (t + 1)) iR
      = raw (wRunFrom W (missFit M) w₀ t) iR) :
    scaleDiv W (bayesStep (missFit M t) (raw (wRunFrom W (missFit M) w₀ t))) = 2 := by
  have hV : 1 ≤ raw (wRunFrom W (missFit M) w₀ t) iR := one_le_raw_wRunFrom hW _ w₀ ht iR
  have hd2 := scaleDiv_bayesStep_le_two hW M t (wRunFrom W (missFit M) w₀ t)
  have hd1 := scaleDiv_pos W (bayesStep (missFit M t) (raw (wRunFrom W (missFit M) w₀ t)))
  have hu : bayesStep (missFit M t) (raw (wRunFrom W (missFit M) w₀ t)) iR
      = 2 * raw (wRunFrom W (missFit M) w₀ t) iR := by
    rw [bayesStep, missFit_eq_two (hR t)]; ring
  rw [raw_wRunFrom_succ hW, project, hu] at hconst
  rcases (show scaleDiv W (bayesStep (missFit M t) (raw (wRunFrom W (missFit M) w₀ t))) = 1
      ∨ scaleDiv W (bayesStep (missFit M t) (raw (wRunFrom W (missFit M) w₀ t))) = 2 by
        omega) with h | h
  · rw [h, Nat.div_one] at hconst; omega
  · exact h

/-- **Under the lock no weight rises.** A hit is `2w/2 = w` exactly and a miss is `max 1 ⌊w/2⌋`,
which is at most `w` once `w` is at the reserve. -/
private theorem raw_wRunFrom_succ_le_of_lock (hW : 1 ≤ W) (M : ℕ → Fin C → Bool)
    (w₀ : WVec C W) {t : ℕ} (ht : 1 ≤ t)
    (hd : scaleDiv W (bayesStep (missFit M t) (raw (wRunFrom W (missFit M) w₀ t))) = 2)
    (i : Fin C) :
    raw (wRunFrom W (missFit M) w₀ (t + 1)) i ≤ raw (wRunFrom W (missFit M) w₀ t) i := by
  have hp : 1 ≤ raw (wRunFrom W (missFit M) w₀ t) i := one_le_raw_wRunFrom hW _ w₀ ht i
  have hf := missFit_le_two M t i
  have hf1 := one_le_missFit M t i
  rw [raw_wRunFrom_succ hW, project, hd, bayesStep]
  rcases (show missFit M t i = 1 ∨ missFit M t i = 2 by omega) with h | h <;> rw [h] <;> omega

/-- A non-increasing `ℕ`-valued sequence is eventually constant. No bound is needed in this
direction — the range's infimum is attained, where a monotone sequence needs a ceiling to make its
supremum attained. -/
private theorem exists_eventually_const_of_antitone (g : ℕ → ℕ)
    (hanti : ∀ {t t' : ℕ}, t ≤ t' → g t' ≤ g t) :
    ∃ T, ∀ t, T ≤ t → g t = g T := by
  obtain ⟨T, hT⟩ := Nat.sInf_mem (Set.range_nonempty g)
  refine ⟨T, fun t htT => le_antisymm (hanti htT) ?_⟩
  rw [hT]
  exact Nat.sInf_le (Set.mem_range_self t)

/-- **The whole weight vector settles**, from every initial vector on the carrier and at every
budget — realizability along the observed trajectory is the only hypothesis, and the settling time
can be taken past the first step, where the floor has already filled in any zeros the start
carried. -/
theorem raw_wRunFrom_eventually_const (hW : 1 ≤ W) (M : ℕ → Fin C → Bool) {iR : Fin C}
    (hR : ∀ t, M t iR = false) (w₀ : WVec C W) :
    ∃ T : ℕ, 1 ≤ T ∧ ∀ t, T ≤ t →
      raw (wRunFrom W (missFit M) w₀ t) = raw (wRunFrom W (missFit M) w₀ T) := by
  obtain ⟨T₀, hT₀⟩ := exists_eventually_const_of_monotone (K := W + 1)
    (fun t => raw (wRunFrom W (missFit M) w₀ t) iR)
    (fun h => raw_wRunFrom_leader_mono hW hR w₀ h)
    (fun t => Nat.lt_succ_of_le (raw_le_budget _ iR))
  set T₁ := max T₀ 1 with hT₁def
  have hT₁one : 1 ≤ T₁ := le_max_right _ _
  have hT₀le : T₀ ≤ T₁ := le_max_left _ _
  have hlead : ∀ t, T₁ ≤ t → raw (wRunFrom W (missFit M) w₀ t) iR
      = raw (wRunFrom W (missFit M) w₀ T₁) iR := fun t ht => by
    rw [hT₀ t (le_trans hT₀le ht), hT₀ T₁ hT₀le]
  have hlock : ∀ t, T₁ ≤ t →
      scaleDiv W (bayesStep (missFit M t) (raw (wRunFrom W (missFit M) w₀ t))) = 2 := by
    intro t ht
    refine scaleDiv_eq_two_of_leader_const hW hR w₀ (le_trans hT₁one ht) ?_
    rw [hlead (t + 1) (by omega), hlead t ht]
  have hdrop : ∀ t, T₁ ≤ t → ∀ i, raw (wRunFrom W (missFit M) w₀ (t + 1)) i
      ≤ raw (wRunFrom W (missFit M) w₀ t) i := fun t ht i =>
    raw_wRunFrom_succ_le_of_lock hW M w₀ (le_trans hT₁one ht) (hlock t ht) i
  have hanti : ∀ i : Fin C, Antitone fun s => raw (wRunFrom W (missFit M) w₀ (T₁ + s)) i :=
    fun i => antitone_nat_of_succ_le fun s => hdrop (T₁ + s) (Nat.le_add_right _ _) i
  obtain ⟨S, hS⟩ := exists_eventually_const_of_antitone
    (fun s => ∑ i, raw (wRunFrom W (missFit M) w₀ (T₁ + s)) i)
    (fun {_ _} h => Finset.sum_le_sum fun i _ => hanti i h)
  refine ⟨T₁ + S, by omega, fun t ht => ?_⟩
  obtain ⟨s, rfl⟩ : ∃ s, t = T₁ + s := ⟨t - T₁, by omega⟩
  have hsS : S ≤ s := by omega
  funext i
  exact (Finset.sum_eq_sum_iff_of_le fun i _ => hanti i hsS).mp (hS s hsS) i (Finset.mem_univ i)

/-- **Selection settles from every initial weight vector** ([Inevitability] §6). The reading is
eventually constant at any budget of at least one quantum, from any vector the carrier holds —
zeros included — with realizability along the observed trajectory the only hypothesis.

What it costs relative to the uniform-start statement is precisely the version-space
characterization: the settled reading here need not be a candidate that has never missed, and
`argmax_wRunFrom_lateHit_missCount_ne_zero` exhibits one that has. What it buys is the initial
condition: the uniform-start theorem describes one trajectory of the fiber, this one describes all
of them. -/
theorem argmax_wRunFrom_eventually_const [NeZero C] (hW : 1 ≤ W) (M : ℕ → Fin C → Bool)
    {iR : Fin C} (hR : ∀ t, M t iR = false) (w₀ : WVec C W) :
    ∃ T : ℕ, ∀ t, T ≤ t →
      argmax (raw (wRunFrom W (missFit M) w₀ t))
        = argmax (raw (wRunFrom W (missFit M) w₀ T)) := by
  obtain ⟨T, -, hT⟩ := raw_wRunFrom_eventually_const hW M hR w₀
  exact ⟨T, fun t ht => by rw [hT t ht]⟩

/-- **The settled reading is eventually consistent**, at a budget of two quanta or more.

The version-space characterization does not transport to a seeded start, but this much of it does,
and by a different route: on the settled tail the divisor is locked at `2`, so the pre-rescale
maximum exceeds the budget and the settled maximum is therefore at least two quanta; the reading
attains that maximum; and a miss under the lock would halve it, which constancy forbids.

`2 ≤ W` is where it lives and is not slack — `argmax_wRunFrom_zeroMiss_misses` refutes the clause at
one quantum, the weight-level form of the uniform-start suite's own `b = 0` degeneracy. -/
theorem argmax_wRunFrom_eventually_const_consistent [NeZero C] (hW : 2 ≤ W)
    (M : ℕ → Fin C → Bool) {iR : Fin C} (hR : ∀ t, M t iR = false) (w₀ : WVec C W) :
    ∃ T : ℕ,
      (∀ t, T ≤ t → argmax (raw (wRunFrom W (missFit M) w₀ t))
        = argmax (raw (wRunFrom W (missFit M) w₀ T)))
      ∧ ∀ t, T ≤ t → M t (argmax (raw (wRunFrom W (missFit M) w₀ T))) = false := by
  have hW1 : 1 ≤ W := by omega
  obtain ⟨T, hT1, hT⟩ := raw_wRunFrom_eventually_const hW1 M hR w₀
  have hlock : ∀ s, T ≤ s →
      scaleDiv W (bayesStep (missFit M s) (raw (wRunFrom W (missFit M) w₀ s))) = 2 := by
    intro s hs
    refine scaleDiv_eq_two_of_leader_const hW1 hR w₀ (le_trans hT1 hs) ?_
    rw [congrFun (hT (s + 1) (by omega)) iR, congrFun (hT s hs) iR]
  refine ⟨T, fun t ht => by rw [hT t ht], fun t ht => ?_⟩
  set c := argmax (raw (wRunFrom W (missFit M) w₀ T)) with hc
  -- the settled maximum is at least two quanta, because the lock says the exact step overflows
  have hbound : wMax (bayesStep (missFit M T) (raw (wRunFrom W (missFit M) w₀ T)))
      ≤ 2 * wMax (raw (wRunFrom W (missFit M) w₀ T)) :=
    Finset.sup_le fun i _ => by
      rw [bayesStep]
      calc raw (wRunFrom W (missFit M) w₀ T) i * missFit M T i
          ≤ wMax (raw (wRunFrom W (missFit M) w₀ T)) * 2 :=
            Nat.mul_le_mul (le_wMax _ i) (missFit_le_two M T i)
        _ = 2 * wMax (raw (wRunFrom W (missFit M) w₀ T)) :=
            Nat.mul_comm _ 2
  have hd := hlock T le_rfl
  rw [scaleDiv] at hd
  have hq' := (Nat.le_div_iff_mul_le (by omega : 0 < W)).mp
    (show 2 ≤ (wMax (bayesStep (missFit M T) (raw (wRunFrom W (missFit M) w₀ T))) + W - 1) / W by
      omega)
  have hvc : raw (wRunFrom W (missFit M) w₀ T) c = wMax (raw (wRunFrom W (missFit M) w₀ T)) :=
    argmax_eq_wMax _
  -- a miss on the settled reading would strictly halve a weight the lock holds fixed
  by_contra hcon
  have hmiss : M t c = true := by revert hcon; cases M t c <;> simp
  have hstep : raw (wRunFrom W (missFit M) w₀ (t + 1)) c
      = max 1 (raw (wRunFrom W (missFit M) w₀ T) c / 2) := by
    rw [raw_wRunFrom_succ hW1, project, hlock t ht, bayesStep, missFit_eq_one hmiss,
      congrFun (hT t ht) c, Nat.mul_one]
  rw [congrFun (hT (t + 1) (by omega)) c] at hstep
  omega

private theorem missFit_shift (M : ℕ → Fin C → Bool) (s : ℕ) :
    (fun n => missFit M (s + n)) = missFit fun n => M (s + n) := rfl

/-- **Eventual realizability suffices**, and it is free: restart the run past the last miss.

The hypothesis a settling story actually wants is that *some* candidate misses only finitely often,
not that one never misses at all; over `wRun`, whose start is baked in, that hypothesis cannot even
be reduced to the other, because there is no run to restart. `wRunFrom_add` supplies the reduction,
and the settling time translates back by the same shift. -/
theorem argmax_wRunFrom_eventually_const_of_eventually_realizable [NeZero C] (hW : 1 ≤ W)
    (M : ℕ → Fin C → Bool) {iR : Fin C} {T₀ : ℕ} (hR : ∀ t, T₀ ≤ t → M t iR = false)
    (w₀ : WVec C W) :
    ∃ T : ℕ, ∀ t, T ≤ t →
      argmax (raw (wRunFrom W (missFit M) w₀ t))
        = argmax (raw (wRunFrom W (missFit M) w₀ T)) := by
  have hshift : ∀ t, wRunFrom W (missFit M) w₀ (T₀ + t)
      = wRunFrom W (missFit fun n => M (T₀ + n)) (wRunFrom W (missFit M) w₀ T₀) t := fun t => by
    rw [wRunFrom_add, missFit_shift]
  obtain ⟨T', hT'⟩ := argmax_wRunFrom_eventually_const hW (fun n => M (T₀ + n))
    (fun n => hR (T₀ + n) (Nat.le_add_right _ _)) (wRunFrom W (missFit M) w₀ T₀)
  refine ⟨T₀ + T', fun t ht => ?_⟩
  obtain ⟨s, rfl⟩ : ∃ s, t = T₀ + s := ⟨t - T₀, by omega⟩
  rw [hshift s, hshift T', hT' s (by omega)]

/-- The identity clause under eventual realizability, by the same restart. -/
theorem argmax_wRunFrom_eventually_const_consistent_of_eventually_realizable [NeZero C]
    (hW : 2 ≤ W) (M : ℕ → Fin C → Bool) {iR : Fin C} {T₀ : ℕ}
    (hR : ∀ t, T₀ ≤ t → M t iR = false) (w₀ : WVec C W) :
    ∃ T : ℕ,
      (∀ t, T ≤ t → argmax (raw (wRunFrom W (missFit M) w₀ t))
        = argmax (raw (wRunFrom W (missFit M) w₀ T)))
      ∧ ∀ t, T ≤ t → M t (argmax (raw (wRunFrom W (missFit M) w₀ T))) = false := by
  have hshift : ∀ t, wRunFrom W (missFit M) w₀ (T₀ + t)
      = wRunFrom W (missFit fun n => M (T₀ + n)) (wRunFrom W (missFit M) w₀ T₀) t := fun t => by
    rw [wRunFrom_add, missFit_shift]
  obtain ⟨T', h1, h2⟩ := argmax_wRunFrom_eventually_const_consistent hW (fun n => M (T₀ + n))
    (fun n => hR (T₀ + n) (Nat.le_add_right _ _)) (wRunFrom W (missFit M) w₀ T₀)
  refine ⟨T₀ + T', fun t ht => ?_, fun t ht => ?_⟩
  · obtain ⟨s, rfl⟩ : ∃ s, t = T₀ + s := ⟨t - T₀, by omega⟩
    rw [hshift s, hshift T', h1 s (by omega)]
  · obtain ⟨s, rfl⟩ : ∃ s, t = T₀ + s := ⟨t - T₀, by omega⟩
    rw [hshift T']
    exact h2 s (by omega)

/-! ## The lock shape: which vector the run actually reaches

The theorems above settle the *reading*; none of them says which weight vector the run itself
converges to. From the uniform start, under one persistent candidate, the vector is pinned down
exactly by two more facts about the generation: the persistent candidate dominates every other
coordinate pointwise, so the rescale divisor is a function of its own value alone, and that value
climbs by doubling until the budget stops it — landing on the largest power of two the budget holds,
not on the budget itself. `settled` is not this shape in general — the guard family below exhibits
budgets where the run's own fixed point is a different vector, at every candidate — but on a
power-of-two budget the two coincide, which is the corollary that follows. -/

/-- **The persistent candidate dominates the whole vector, pointwise, from the uniform start.** Both
start at the reserve; the exact step multiplies the persistent candidate by exactly `2` and every
other candidate by at most `2`, and the common rescale — one divisor, one floor, applied alike to
every coordinate — cannot disturb an inequality that already held before it. -/
private theorem raw_wRunFrom_le_leader (hW : 1 ≤ W) {M : ℕ → Fin C → Bool} {iR : Fin C}
    (hR : ∀ t, M t iR = false) (i : Fin C) (t : ℕ) :
    raw (wRunFrom W (missFit M) (pack W fun _ => 1) t) i
      ≤ raw (wRunFrom W (missFit M) (pack W fun _ => 1) t) iR := by
  induction t with
  | zero => exact le_of_eq rfl
  | succ t ih =>
      rw [raw_wRunFrom_succ hW, project, project]
      have hstepR : bayesStep (missFit M t)
          (raw (wRunFrom W (missFit M) (pack W fun _ => 1) t)) iR
          = 2 * raw (wRunFrom W (missFit M) (pack W fun _ => 1) t) iR := by
        rw [bayesStep, missFit_eq_two (hR t)]; ring
      have hstepI : bayesStep (missFit M t)
          (raw (wRunFrom W (missFit M) (pack W fun _ => 1) t)) i
          ≤ 2 * raw (wRunFrom W (missFit M) (pack W fun _ => 1) t) iR := by
        rw [bayesStep]
        calc raw (wRunFrom W (missFit M) (pack W fun _ => 1) t) i * missFit M t i
            ≤ raw (wRunFrom W (missFit M) (pack W fun _ => 1) t) iR * 2 :=
              Nat.mul_le_mul ih (missFit_le_two M t i)
          _ = 2 * raw (wRunFrom W (missFit M) (pack W fun _ => 1) t) iR := Nat.mul_comm _ _
      rw [hstepR]
      exact max_le_max le_rfl (Nat.div_le_div_right hstepI)

/-- The persistent candidate's raw weight, isolated for the recursion below. -/
private abbrev leaderVal (W : ℕ) (M : ℕ → Fin C → Bool) (iR : Fin C) (t : ℕ) : ℕ :=
  raw (wRunFrom W (missFit M) (pack W fun _ => 1) t) iR

private theorem leaderVal_zero (hW : 1 ≤ W) (M : ℕ → Fin C → Bool) (iR : Fin C) :
    leaderVal W M iR 0 = 1 := by
  change raw (pack W (fun _ => (1 : ℕ)) : WVec C W) iR = 1
  rw [raw, pack]
  exact min_eq_left hW

private theorem leaderVal_le (W : ℕ) (M : ℕ → Fin C → Bool) (iR : Fin C) (t : ℕ) :
    leaderVal W M iR t ≤ W := raw_le_budget _ iR

/-- The pre-rescale maximum is exactly twice the persistent candidate's own weight: dominance makes
it both the upper bound and, at its own coordinate, the value attained. -/
private theorem wMax_bayesStep_wRunFrom_eq_leader (hW : 1 ≤ W) {M : ℕ → Fin C → Bool} {iR : Fin C}
    (hR : ∀ t, M t iR = false) (t : ℕ) :
    wMax (bayesStep (missFit M t) (raw (wRunFrom W (missFit M) (pack W fun _ => 1) t)))
      = 2 * leaderVal W M iR t := by
  refine le_antisymm (Finset.sup_le fun i _ => ?_) ?_
  · rw [bayesStep]
    calc raw (wRunFrom W (missFit M) (pack W fun _ => 1) t) i * missFit M t i
        ≤ leaderVal W M iR t * 2 :=
          Nat.mul_le_mul (raw_wRunFrom_le_leader hW hR i t) (missFit_le_two M t i)
      _ = 2 * leaderVal W M iR t := Nat.mul_comm _ _
  · change 2 * raw (wRunFrom W (missFit M) (pack W fun _ => 1) t) iR ≤ _
    have h := le_wMax (bayesStep (missFit M t)
      (raw (wRunFrom W (missFit M) (pack W fun _ => 1) t))) iR
    rw [bayesStep, missFit_eq_two (hR t)] at h
    omega

private theorem scaleDiv_wRunFrom_eq (hW : 1 ≤ W) {M : ℕ → Fin C → Bool} {iR : Fin C}
    (hR : ∀ t, M t iR = false) (t : ℕ) :
    scaleDiv W (bayesStep (missFit M t) (raw (wRunFrom W (missFit M) (pack W fun _ => 1) t)))
      = max 1 ((2 * leaderVal W M iR t + W - 1) / W) := by
  rw [scaleDiv, wMax_bayesStep_wRunFrom_eq_leader hW hR t]

private theorem scaleDiv_wRunFrom_eq_one (hW : 1 ≤ W) {M : ℕ → Fin C → Bool} {iR : Fin C}
    (hR : ∀ t, M t iR = false) {t : ℕ} (h1 : 1 ≤ leaderVal W M iR t)
    (h2 : 2 * leaderVal W M iR t ≤ W) :
    scaleDiv W (bayesStep (missFit M t)
        (raw (wRunFrom W (missFit M) (pack W fun _ => 1) t))) = 1 := by
  rw [scaleDiv_wRunFrom_eq hW hR t]
  have hq : (2 * leaderVal W M iR t + W - 1) / W = 1 := Nat.div_eq_of_lt_le (by omega) (by omega)
  omega

private theorem scaleDiv_wRunFrom_eq_two (hW : 1 ≤ W) {M : ℕ → Fin C → Bool} {iR : Fin C}
    (hR : ∀ t, M t iR = false) {t : ℕ} (_h1 : 1 ≤ leaderVal W M iR t)
    (h2 : W < 2 * leaderVal W M iR t) (h3 : leaderVal W M iR t ≤ W) :
    scaleDiv W (bayesStep (missFit M t)
        (raw (wRunFrom W (missFit M) (pack W fun _ => 1) t))) = 2 := by
  rw [scaleDiv_wRunFrom_eq hW hR t]
  have hq : (2 * leaderVal W M iR t + W - 1) / W = 2 := Nat.div_eq_of_lt_le (by omega) (by omega)
  omega

/-- **The persistent candidate's own recursion**: it doubles while doubling still fits the budget,
and stands still the moment it does not. The rescale is the whole mechanism — no other coordinate's
behavior enters, because dominance already priced the divisor in terms of this value alone. -/
private theorem leaderVal_succ (hW : 1 ≤ W) {M : ℕ → Fin C → Bool} {iR : Fin C}
    (hR : ∀ t, M t iR = false) (t : ℕ) :
    leaderVal W M iR (t + 1)
      = if 2 * leaderVal W M iR t ≤ W then 2 * leaderVal W M iR t else leaderVal W M iR t := by
  have hL1 : 1 ≤ leaderVal W M iR t := by
    rcases Nat.eq_zero_or_pos t with ht0 | ht0
    · subst ht0; rw [leaderVal_zero hW]
    · exact one_le_raw_wRunFrom hW _ _ ht0 iR
  have hLW : leaderVal W M iR t ≤ W := leaderVal_le W M iR t
  have hbase : leaderVal W M iR (t + 1)
      = max 1 (2 * leaderVal W M iR t
          / scaleDiv W (bayesStep (missFit M t)
              (raw (wRunFrom W (missFit M) (pack W fun _ => 1) t)))) := by
    change raw (wRunFrom W (missFit M) (pack W fun _ => 1) (t + 1)) iR = _
    rw [raw_wRunFrom_succ hW, project, bayesStep, missFit_eq_two (hR t), Nat.mul_comm]
  split
  · rename_i h
    rw [hbase, scaleDiv_wRunFrom_eq_one hW hR hL1 h, Nat.div_one]
    omega
  · rename_i h
    rw [not_le] at h
    rw [hbase, scaleDiv_wRunFrom_eq_two hW hR hL1 h hLW,
      Nat.mul_div_cancel_left _ (by norm_num : (0 : ℕ) < 2)]
    omega

/-- **The closed form**: the persistent candidate's weight is a power of two at every step, the
smaller of the step count and the budget's own binary exponent. -/
private theorem leaderVal_eq_pow_min (hW : 1 ≤ W) {M : ℕ → Fin C → Bool} {iR : Fin C}
    (hR : ∀ t, M t iR = false) (t : ℕ) :
    leaderVal W M iR t = 2 ^ min t (Nat.log 2 W) := by
  induction t with
  | zero => rw [leaderVal_zero hW]; simp
  | succ t ih =>
      rw [leaderVal_succ hW hR, ih]
      rcases Nat.lt_or_ge t (Nat.log 2 W) with hlt | hge
      · have hmin1 : min t (Nat.log 2 W) = t := min_eq_left hlt.le
        have hmin2 : min (t + 1) (Nat.log 2 W) = t + 1 := min_eq_left (by omega)
        have h2 : 2 * 2 ^ min t (Nat.log 2 W) ≤ W := by
          rw [hmin1]
          calc 2 * 2 ^ t = 2 ^ (t + 1) := by rw [pow_succ]; ring
            _ ≤ 2 ^ Nat.log 2 W := Nat.pow_le_pow_right (by norm_num) (by omega)
            _ ≤ W := Nat.pow_log_le_self 2 (by omega)
        rw [ite_eq_left h2, hmin1, hmin2, pow_succ]; ring
      · have hmin1 : min t (Nat.log 2 W) = Nat.log 2 W := min_eq_right hge
        have hmin2 : min (t + 1) (Nat.log 2 W) = Nat.log 2 W := min_eq_right (by omega)
        have hlog : W < 2 ^ Nat.log 2 W * 2 := by
          have h := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) W
          simpa [pow_succ] using h
        have h2 : ¬ 2 * 2 ^ min t (Nat.log 2 W) ≤ W := by rw [hmin1]; omega
        rw [ite_eq_right h2, hmin1, hmin2]

private theorem leaderVal_eq_pow_of_ge (hW : 1 ≤ W) {M : ℕ → Fin C → Bool} {iR : Fin C}
    (hR : ∀ t, M t iR = false) {t : ℕ} (ht : Nat.log 2 W ≤ t) :
    leaderVal W M iR t = 2 ^ Nat.log 2 W := by
  rw [leaderVal_eq_pow_min hW hR, min_eq_right ht]

private theorem scaleDiv_wRunFrom_eq_two_of_ge_log (hW : 1 ≤ W) {M : ℕ → Fin C → Bool} {iR : Fin C}
    (hR : ∀ t, M t iR = false) {t : ℕ} (ht : Nat.log 2 W ≤ t) :
    scaleDiv W (bayesStep (missFit M t)
        (raw (wRunFrom W (missFit M) (pack W fun _ => 1) t))) = 2 := by
  have hLeq := leaderVal_eq_pow_of_ge hW hR ht
  have hL1 : 1 ≤ leaderVal W M iR t := by rw [hLeq]; exact Nat.one_le_two_pow
  have hLW : leaderVal W M iR t ≤ W := leaderVal_le W M iR t
  refine scaleDiv_wRunFrom_eq_two hW hR hL1 ?_ hLW
  rw [hLeq]
  have h := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) W
  have h' : W < 2 ^ Nat.log 2 W * 2 := by simpa [pow_succ] using h
  omega

/-- **The run reaches the lock shape, not merely a settled candidate.** Under a persistent candidate
and every other candidate missing infinitely often, the run's own weight vector — from the uniform
start — is eventually exactly the persistent candidate raised to the largest power of two the budget
holds, and every other coordinate at the one-quantum floor. Neither conclusion needs the budget to
be a power of two: `raw_wRunFrom_eventually_settled` below is what that extra hypothesis buys. -/
theorem raw_wRunFrom_eventually_lock (hW : 1 ≤ W) {M : ℕ → Fin C → Bool} {iR : Fin C}
    (hR : ∀ t, M t iR = false) (hOther : ∀ i, i ≠ iR → ∀ s, ∃ t, s ≤ t ∧ M t i = true) :
    ∃ T, ∀ t, T ≤ t →
      raw (wRunFrom W (missFit M) (pack W fun _ => 1) t)
        = fun i => if i = iR then 2 ^ Nat.log 2 W else 1 := by
  obtain ⟨T, hT1, hT⟩ := raw_wRunFrom_eventually_const hW M hR (pack W fun _ => 1)
  have hTge : Nat.log 2 W ≤ T := by
    by_contra hcon
    rw [not_le] at hcon
    have hEq : leaderVal W M iR (T + 1) = leaderVal W M iR T :=
      congrFun (hT (T + 1) (by omega)) iR
    have hLT := leaderVal_eq_pow_min hW hR T
    have hLT1 := leaderVal_eq_pow_min hW hR (T + 1)
    rw [min_eq_left hcon.le] at hLT
    rw [min_eq_left (by omega : T + 1 ≤ Nat.log 2 W)] at hLT1
    rw [hLT, hLT1] at hEq
    rw [pow_succ] at hEq
    have hpos : 0 < (2 : ℕ) ^ T := pow_pos (by norm_num) T
    omega
  refine ⟨T, fun t ht => ?_⟩
  have hRawEq : raw (wRunFrom W (missFit M) (pack W fun _ => 1) t)
      = raw (wRunFrom W (missFit M) (pack W fun _ => 1) T) := hT t ht
  rw [hRawEq]
  funext i
  by_cases hi : i = iR
  · subst hi
    rw [ite_eq_left rfl]
    exact leaderVal_eq_pow_of_ge hW hR hTge
  · rw [ite_eq_right hi]
    obtain ⟨t', ht', hmiss⟩ := hOther i hi T
    have heq1 : raw (wRunFrom W (missFit M) (pack W fun _ => 1) t') i
        = raw (wRunFrom W (missFit M) (pack W fun _ => 1) T) i := congrFun (hT t' ht') i
    have heq2 : raw (wRunFrom W (missFit M) (pack W fun _ => 1) (t' + 1)) i
        = raw (wRunFrom W (missFit M) (pack W fun _ => 1) T) i :=
      congrFun (hT (t' + 1) (by omega)) i
    have hlockAt : scaleDiv W (bayesStep (missFit M t')
        (raw (wRunFrom W (missFit M) (pack W fun _ => 1) t'))) = 2 :=
      scaleDiv_wRunFrom_eq_two_of_ge_log hW hR (le_trans hTge ht')
    have hstep : raw (wRunFrom W (missFit M) (pack W fun _ => 1) (t' + 1)) i
        = max 1 (raw (wRunFrom W (missFit M) (pack W fun _ => 1) t') i / 2) := by
      rw [raw_wRunFrom_succ hW, project, hlockAt, bayesStep, missFit_eq_one hmiss, Nat.mul_one]
    rw [heq1] at hstep
    rw [heq2] at hstep
    have hpos : 1 ≤ raw (wRunFrom W (missFit M) (pack W fun _ => 1) T) i :=
      one_le_raw_wRunFrom hW _ _ hT1 i
    omega

/-- **At a power-of-two budget the lock shape is `settled`.** The identification the paper's
formalization asks for, with the exact hypotheses under which it holds: a persistent candidate,
every other candidate missing infinitely often, and a budget that is a power of two. -/
theorem raw_wRunFrom_eventually_settled {k : ℕ} {M : ℕ → Fin C → Bool} {iR : Fin C}
    (hR : ∀ t, M t iR = false) (hOther : ∀ i, i ≠ iR → ∀ s, ∃ t, s ≤ t ∧ M t i = true)
    (hWk : W = 2 ^ k) :
    ∃ T, ∀ t, T ≤ t →
      raw (wRunFrom W (missFit M) (pack W fun _ => 1) t) = settled W iR := by
  have hW : 1 ≤ W := by rw [hWk]; exact Nat.one_le_two_pow
  obtain ⟨T, hT⟩ := raw_wRunFrom_eventually_lock hW hR hOther
  refine ⟨T, fun t ht => ?_⟩
  rw [hT t ht]
  funext i
  rw [settled]
  by_cases hi : i = iR
  · rw [ite_eq_left hi, ite_eq_left hi, hWk, Nat.log_pow (by norm_num : 1 < 2)]
  · rw [ite_eq_right hi, ite_eq_right hi]

end Basin

/-! ## The fiber's own reading, from an arbitrary fiber state

The settling above is stated of the abstract miss indicator. Here it is read through the frame the
pricing assembly uses, over the skew product and at the construction's own predictive fitness —
with the fiber coordinate started anywhere on the carrier rather than at the uniform prior. -/

section PredictiveFiber


variable {n₁ C W : ℕ}

/-- **The skew product's start at a given fiber state**: the base at `x₀`, the fiber at `w₀`. The
uniform-prior start is the special case `wStartFrom_pack_one` records. -/
def wStartFrom (W : ℕ) {n₁ C : ℕ} (x₀ : Fin n₁) (w₀ : WVec C W) : Fin (n₁ * (W + 1) ^ C) :=
  finProdFinEquiv (x₀, finFunctionFinEquiv w₀)

theorem wStartFrom_pack_one (C W : ℕ) (x₀ : Fin n₁) :
    wStartFrom W x₀ (pack W fun _ => 1 : WVec C W) = wStartAt C W x₀ := rfl

/-- **The fiber coordinate of the skew run is the seeded run.** The base drives the fiber and never
reads it, so `t` steps of `wWorld` leave the base at `S^[t] x₀` and the fiber at the seeded run's
`t`-th vector under the fitness sampled along that trajectory. -/
theorem iterate_wWorld_wStartFrom (S : Fin n₁ → Fin n₁) (fit : Fin n₁ → Fin C → ℕ) (x₀ : Fin n₁)
    (w₀ : WVec C W) (t : ℕ) :
    (wWorld W S fit)^[t] (wStartFrom W x₀ w₀)
      = finProdFinEquiv (S^[t] x₀,
          finFunctionFinEquiv (wRunFrom W (fun s => fit (S^[s] x₀)) w₀ t)) := by
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [Function.iterate_succ_apply', ih, wWorld, skewWorldFin_apply, wFiber,
        Equiv.symm_apply_apply, ← Function.iterate_succ_apply' S t x₀]
      rfl

theorem argmaxFrame_iterate_wWorld_wStartFrom [NeZero C] (S : Fin n₁ → Fin n₁)
    (fit : Fin n₁ → Fin C → ℕ) (x₀ : Fin n₁) (w₀ : WVec C W) (t : ℕ) :
    argmaxFrame n₁ W ((wWorld W S fit)^[t] (wStartFrom W x₀ w₀))
      = argmax (raw (wRunFrom W (fun s => fit (S^[s] x₀)) w₀ t)) := by
  rw [iterate_wWorld_wStartFrom]
  simp only [argmaxFrame, Equiv.symm_apply_apply]

/-- **The fiber's reading settles from every initial weight vector** ([Inevitability] §6).

Score the candidates by `predFitPos` against the base's own next state and start the fiber anywhere
on the carrier, over any base point. If some candidate decodes to a rule predicting the base
correctly at every step of that trajectory, the frame's reading is eventually constant — and, at a
budget of two quanta or more, on a candidate that agrees with the base from the settling time on.

Two differences from the uniform-start statement, and both are forced rather than conceded. The
budget is an arbitrary `2 ≤ W` where that one needs a power of two, because the argument no longer
runs through the exponent automaton. And the settled candidate is consistent along the **tail** of
the trajectory rather than all of it: `argmax_wRunFrom_lateHit_missCount_ne_zero` exhibits a seeded
run settling on a candidate that has already missed, so the global clause is unavailable here and
is not a weakness of the proof. -/
theorem argmaxFrame_wWorld_eventually_const_wStartFrom [NeZero C] (hW : 2 ≤ W)
    (S : Fin n₁ → Fin n₁) (dec : Fin C → Fin n₁ → Fin n₁) (x₀ : Fin n₁) {c₀ : Fin C}
    (hc₀ : ∀ s, dec c₀ (S^[s] x₀) = S (S^[s] x₀)) (w₀ : WVec C W) :
    ∃ (T : ℕ) (c : Fin C), (∀ s, T ≤ s → dec c (S^[s] x₀) = S (S^[s] x₀)) ∧
      ∀ t, T ≤ t →
        argmaxFrame n₁ W ((wWorld W S (predFitPos S dec))^[t] (wStartFrom W x₀ w₀)) = c := by
  have hfit : (fun s => predFitPos S dec (S^[s] x₀)) = missFit (predMiss S dec x₀) := by
    funext s
    exact (missFit_predMiss S dec x₀ s).symm
  have hR : ∀ s, predMiss S dec x₀ s c₀ = false := by
    intro s
    simp [predMiss, hc₀ s]
  obtain ⟨T, hconst, hcons⟩ :=
    argmax_wRunFrom_eventually_const_consistent hW (predMiss S dec x₀) hR w₀
  refine ⟨T, argmax (raw (wRunFrom W (missFit (predMiss S dec x₀)) w₀ T)), fun s hs => ?_,
    fun t ht => ?_⟩
  · simpa [predMiss] using hcons s hs
  · rw [argmaxFrame_iterate_wWorld_wStartFrom, hfit]
    exact hconst t ht

end PredictiveFiber

/-! ## What does not transport, and what the hypotheses are worth -/

section Guards

private theorem wMax_two (v : Fin 2 → ℕ) : wMax v = max (v 0) (v 1) := by
  refine le_antisymm (Finset.sup_le fun i _ => ?_) (max_le (le_wMax v 0) (le_wMax v 1))
  fin_cases i
  · exact le_max_left _ _
  · exact le_max_right _ _

/-! ### The reading's monotonicity and its change count are uniform-start privileges

From the uniform start the reading is the least never-missing candidate, so it never moves back and
moves at most `C − 1` times. Both statements are about that characterization rather than about
settling, and a seeded start refutes both: below, the reading moves back on its second step and
changes as often as the budget's exponent allows. -/

/-- Three candidates: candidate `0` never misses, candidate `1` misses at the even steps and
candidate `2` at the odd ones. -/
def seededAlt : ℕ → Fin 3 → Bool := fun t i => decide ((i : ℕ) = t % 2 + 1)

/-- The seeded start: one reserved quantum on the never-missing candidate, the whole budget on each
of the alternating pair. -/
def seededStart (W : ℕ) : WVec 3 W := pack W ![1, W, W]

theorem seededAlt_realizable (t : ℕ) : seededAlt t 0 = false := by
  simp only [seededAlt, decide_eq_false_iff_not, Fin.val_zero]
  omega

private theorem wMax_three (v : Fin 3 → ℕ) : wMax v = max (v 0) (max (v 1) (v 2)) := by
  refine le_antisymm (Finset.sup_le fun i _ => ?_)
    (max_le (le_wMax v 0) (max_le (le_wMax v 1) (le_wMax v 2)))
  fin_cases i
  · exact le_max_left _ _
  · exact le_trans (le_max_left _ _) (le_max_right _ _)
  · exact le_trans (le_max_right _ _) (le_max_right _ _)

private theorem eq_of_fin_three {v w : Fin 3 → ℕ} (h0 : v 0 = w 0) (h1 : v 1 = w 1)
    (h2 : v 2 = w 2) : v = w := by
  funext i
  fin_cases i
  exacts [h0, h1, h2]

/-- **The seeded run in closed form, through its alternating phase.** The never-missing candidate
climbs one doubling every two steps from its single quantum; the pair holding the budget trade the
rescale between them, whichever of the two just missed sitting one doubling down. -/
theorem raw_wRunFrom_seededAlt (b : ℕ) : ∀ t, t ≤ 2 * b →
    raw (wRunFrom (2 ^ b) (missFit seededAlt) (seededStart (2 ^ b)) t)
      = ![2 ^ (t / 2), 2 ^ (b - t % 2), 2 ^ b] := by
  have hW1 : 1 ≤ 2 ^ b := Nat.one_le_two_pow
  intro t
  induction t with
  | zero =>
      intro _
      change raw (seededStart (2 ^ b) : WVec 3 (2 ^ b)) = _
      refine eq_of_fin_three ?_ ?_ ?_
      · change min 1 (2 ^ b) = 2 ^ (0 / 2)
        simp only [Nat.zero_div, pow_zero, inf_eq_left]
        exact hW1
      · change min (2 ^ b) (2 ^ b) = 2 ^ (b - 0 % 2)
        simp
      · change min (2 ^ b) (2 ^ b) = 2 ^ b
        simp
  | succ t ih =>
      intro ht
      have hb : 1 ≤ b := by omega
      have hpow : (2 : ℕ) ^ b = 2 * 2 ^ (b - 1) := by
        rw [← pow_succ']
        congr 1
        omega
      have hq : 1 ≤ (2 : ℕ) ^ (t / 2) := Nat.one_le_two_pow
      have hq1 : 1 ≤ (2 : ℕ) ^ (b - 1) := Nat.one_le_two_pow
      have hf0 : missFit seededAlt t 0 = 2 := missFit_eq_two (seededAlt_realizable t)
      rw [raw_wRunFrom_succ hW1, ih (by omega)]
      rcases (show t % 2 = 0 ∨ t % 2 = 1 by omega) with hr | hr
      · -- an even step: the middle candidate misses, and the third is at the ceiling on a hit
        have hf1 : missFit seededAlt t 1 = 1 := missFit_eq_one (by simp [seededAlt, hr])
        have hf2 : missFit seededAlt t 2 = 2 := missFit_eq_two (by simp [seededAlt, hr])
        have hu : bayesStep (missFit seededAlt t) ![2 ^ (t / 2), 2 ^ (b - t % 2), 2 ^ b]
            = ![2 ^ (t / 2) * 2, 2 ^ b, 2 ^ b * 2] := by
          refine eq_of_fin_three ?_ ?_ ?_
          · change 2 ^ (t / 2) * missFit seededAlt t 0 = 2 ^ (t / 2) * 2
            rw [hf0]
          · change 2 ^ (b - t % 2) * missFit seededAlt t 1 = 2 ^ b
            rw [hf1, hr]
            simp
          · change 2 ^ b * missFit seededAlt t 2 = 2 ^ b * 2
            rw [hf2]
        have hm : wMax (![2 ^ (t / 2) * 2, 2 ^ b, 2 ^ b * 2] : Fin 3 → ℕ) = 2 ^ b * 2 := by
          rw [wMax_three]
          change max (2 ^ (t / 2) * 2) (max (2 ^ b) (2 ^ b * 2)) = 2 ^ b * 2
          have h1 : (2 : ℕ) ^ (t / 2) ≤ 2 ^ b := Nat.pow_le_pow_right (by norm_num) (by omega)
          omega
        have hd : scaleDiv (2 ^ b) (![2 ^ (t / 2) * 2, 2 ^ b, 2 ^ b * 2] : Fin 3 → ℕ) = 2 := by
          rw [scaleDiv, hm]
          have h : ((2 : ℕ) ^ b * 2 + 2 ^ b - 1) / 2 ^ b = 2 :=
            Nat.div_eq_of_lt_le (by omega) (by omega)
          omega
        rw [hu]
        refine eq_of_fin_three ?_ ?_ ?_
        · rw [project, hd]
          change max 1 (2 ^ (t / 2) * 2 / 2) = 2 ^ ((t + 1) / 2)
          rw [show (t + 1) / 2 = t / 2 by omega]
          omega
        · rw [project, hd]
          change max 1 ((2 : ℕ) ^ b / 2) = 2 ^ (b - (t + 1) % 2)
          rw [show (t + 1) % 2 = 1 by omega]
          omega
        · rw [project, hd]
          change max 1 ((2 : ℕ) ^ b * 2 / 2) = 2 ^ b
          omega
      · -- an odd step: the third candidate misses, so nothing at the ceiling hits and no rescale
        have hf1 : missFit seededAlt t 1 = 2 := missFit_eq_two (by simp [seededAlt, hr])
        have hf2 : missFit seededAlt t 2 = 1 := missFit_eq_one (by simp [seededAlt, hr])
        have hu : bayesStep (missFit seededAlt t) ![2 ^ (t / 2), 2 ^ (b - t % 2), 2 ^ b]
            = ![2 ^ (t / 2) * 2, 2 ^ b, 2 ^ b] := by
          refine eq_of_fin_three ?_ ?_ ?_
          · change 2 ^ (t / 2) * missFit seededAlt t 0 = 2 ^ (t / 2) * 2
            rw [hf0]
          · change 2 ^ (b - t % 2) * missFit seededAlt t 1 = 2 ^ b
            rw [hf1, hr]
            omega
          · change 2 ^ b * missFit seededAlt t 2 = 2 ^ b
            rw [hf2, Nat.mul_one]
        have hm : wMax (![2 ^ (t / 2) * 2, 2 ^ b, 2 ^ b] : Fin 3 → ℕ) = 2 ^ b := by
          rw [wMax_three]
          change max (2 ^ (t / 2) * 2) (max (2 ^ b) (2 ^ b)) = 2 ^ b
          have h1 : (2 : ℕ) ^ (t / 2) * 2 ≤ 2 ^ b := by
            rw [← pow_succ]
            exact Nat.pow_le_pow_right (by norm_num) (by omega)
          omega
        have hd : scaleDiv (2 ^ b) (![2 ^ (t / 2) * 2, 2 ^ b, 2 ^ b] : Fin 3 → ℕ) = 1 := by
          rw [scaleDiv, hm]
          have h : ((2 : ℕ) ^ b + 2 ^ b - 1) / 2 ^ b = 1 :=
            Nat.div_eq_of_lt_le (by omega) (by omega)
          omega
        rw [hu]
        refine eq_of_fin_three ?_ ?_ ?_
        · rw [project, hd]
          change max 1 (2 ^ (t / 2) * 2 / 1) = 2 ^ ((t + 1) / 2)
          rw [show (t + 1) / 2 = t / 2 + 1 by omega, pow_succ]
          omega
        · rw [project, hd]
          change max 1 ((2 : ℕ) ^ b / 1) = 2 ^ (b - (t + 1) % 2)
          rw [show (t + 1) % 2 = 0 by omega, Nat.sub_zero]
          omega
        · rw [project, hd]
          change max 1 ((2 : ℕ) ^ b / 1) = 2 ^ b
          omega

/-- The reading through the alternating phase: it swings between the two budget-holders at every
step, and reaches the never-missing candidate only when that one has caught up. -/
theorem argmax_wRunFrom_seededAlt {b t : ℕ} (hb : 1 ≤ b) (ht : t < 2 * b) :
    argmax (raw (wRunFrom (2 ^ b) (missFit seededAlt) (seededStart (2 ^ b)) t))
      = if t % 2 = 0 then 1 else 2 := by
  have hclosed := raw_wRunFrom_seededAlt b t (by omega)
  have hlt : (2 : ℕ) ^ (t / 2) < 2 ^ b := Nat.pow_lt_pow_right (by norm_num) (by omega)
  rcases (show t % 2 = 0 ∨ t % 2 = 1 by omega) with hr | hr
  · rw [ite_eq_left hr, hclosed, hr, Nat.sub_zero]
    have hmax : wMax (![2 ^ (t / 2), 2 ^ b, 2 ^ b] : Fin 3 → ℕ) = 2 ^ b := by
      rw [wMax_three]
      change max (2 ^ (t / 2)) (max (2 ^ b) (2 ^ b)) = 2 ^ b
      omega
    have hle1 : argmax (![2 ^ (t / 2), 2 ^ b, 2 ^ b] : Fin 3 → ℕ) ≤ 1 :=
      argmax_le_of_eq_wMax (by rw [hmax]; rfl)
    rcases (show argmax (![2 ^ (t / 2), 2 ^ b, 2 ^ b] : Fin 3 → ℕ) = 0
        ∨ argmax (![2 ^ (t / 2), 2 ^ b, 2 ^ b] : Fin 3 → ℕ) = 1 by
      revert hle1
      generalize argmax (![2 ^ (t / 2), 2 ^ b, 2 ^ b] : Fin 3 → ℕ) = j
      revert j
      decide) with h | h
    · exfalso
      have hattain := argmax_eq_wMax (![2 ^ (t / 2), 2 ^ b, 2 ^ b] : Fin 3 → ℕ)
      rw [h, hmax] at hattain
      change (2 : ℕ) ^ (t / 2) = 2 ^ b at hattain
      omega
    · exact h
  · rw [ite_eq_right (by omega), hclosed, hr]
    have hlt1 : (2 : ℕ) ^ (b - 1) < 2 ^ b := Nat.pow_lt_pow_right (by norm_num) (by omega)
    refine argmax_eq_of_strict fun i hi => ?_
    fin_cases i
    · exact hlt
    · exact hlt1
    · exact absurd rfl hi

/-- At the end of the alternating phase the never-missing candidate has caught up, the pool ties,
and the tie-keeping fold reads it. -/
private theorem argmax_wRunFrom_seededAlt_end (b : ℕ) :
    argmax (raw (wRunFrom (2 ^ b) (missFit seededAlt) (seededStart (2 ^ b)) (2 * b))) = 0 := by
  rw [raw_wRunFrom_seededAlt b (2 * b) le_rfl, show 2 * b / 2 = b by omega,
    show 2 * b % 2 = 0 by omega, Nat.sub_zero]
  have hmax : wMax (![2 ^ b, 2 ^ b, 2 ^ b] : Fin 3 → ℕ) = 2 ^ b := by
    rw [wMax_three]
    change max ((2 : ℕ) ^ b) (max (2 ^ b) (2 ^ b)) = 2 ^ b
    omega
  exact le_antisymm (argmax_le_of_eq_wMax (by rw [hmax]; rfl)) (Fin.zero_le _)

/-- **The change count is exactly `2b` — unbounded in the budget at three candidates.** So the
uniform start's `C − 1` bound is not merely exceeded from a seeded start; no bound in the candidate
count alone survives the change of initial condition. -/
theorem argmax_wRunFrom_seededAlt_card_changes_eq {b : ℕ} (hb : 1 ≤ b) :
    ((Finset.range (2 * b)).filter fun t =>
        argmax (raw (wRunFrom (2 ^ b) (missFit seededAlt) (seededStart (2 ^ b)) (t + 1)))
          ≠ argmax (raw (wRunFrom (2 ^ b) (missFit seededAlt) (seededStart (2 ^ b)) t))).card
      = 2 * b := by
  rw [Finset.filter_true_of_mem, Finset.card_range]
  intro t htmem
  have ht : t < 2 * b := Finset.mem_range.mp htmem
  rw [argmax_wRunFrom_seededAlt hb ht]
  rcases (show t + 1 < 2 * b ∨ t + 1 = 2 * b by omega) with ht1 | ht1
  · rw [argmax_wRunFrom_seededAlt hb ht1]
    rcases (show t % 2 = 0 ∨ t % 2 = 1 by omega) with hr | hr
    · rw [ite_eq_left hr, ite_eq_right (show ¬((t + 1) % 2 = 0) by omega)]
      decide
    · rw [ite_eq_right (show ¬(t % 2 = 0) by omega), ite_eq_left (show (t + 1) % 2 = 0 by omega)]
      decide
  · rw [ht1, argmax_wRunFrom_seededAlt_end, ite_eq_right (show ¬(t % 2 = 0) by omega)]
    decide

/-- **The reading moves back.** It reads candidate `1`, then `2`, then `1` again — so the uniform
start's `argmax_wRun_mono` is a statement about the least element of an antitone version space, not
about the dynamics. -/
theorem argmax_wRunFrom_seededAlt_not_mono {b : ℕ} (hb : 2 ≤ b) :
    ¬ ((argmax (raw (wRunFrom (2 ^ b) (missFit seededAlt) (seededStart (2 ^ b)) 1)) : ℕ)
        ≤ (argmax (raw (wRunFrom (2 ^ b) (missFit seededAlt) (seededStart (2 ^ b)) 2)) : ℕ)) := by
  rw [argmax_wRunFrom_seededAlt (by omega) (show 1 < 2 * b by omega),
    argmax_wRunFrom_seededAlt (by omega) (show 2 < 2 * b by omega)]
  decide

/-- **The `C − 1` change count fails at every budget past the first.** -/
theorem argmax_wRunFrom_seededAlt_card_changes_gt {b : ℕ} (hb : 2 ≤ b) :
    3 - 1 < ((Finset.range (2 * b)).filter fun t =>
        argmax (raw (wRunFrom (2 ^ b) (missFit seededAlt) (seededStart (2 ^ b)) (t + 1)))
          ≠ argmax (raw (wRunFrom (2 ^ b) (missFit seededAlt) (seededStart (2 ^ b)) t))).card := by
  rw [argmax_wRunFrom_seededAlt_card_changes_eq (by omega)]
  omega

/-- The family read off the kernel at budget `4`, independently of the closed form above: the
reading walks `1, 2, 1, 2` and then settles on the never-missing candidate. -/
theorem argmax_wRunFrom_seededAlt_witness :
    (List.range 5).map (fun t => argmax (raw (wRunFrom 4 (missFit seededAlt) (seededStart 4) t)))
      = [1, 2, 1, 2, 0] := by decide +kernel

/-! ### The settled reading need not be in the version space -/

/-- Two candidates: the competitor misses once, at the very first step, and never again. -/
def lateHit : ℕ → Fin 2 → Bool := fun t i => decide (t = 0 ∧ (i : ℕ) = 1)

/-- The seeded start: one reserved quantum on the never-missing candidate, the whole budget on the
competitor. -/
def lateStart (W : ℕ) : WVec 2 W := pack W ![1, W]

theorem lateHit_realizable (t : ℕ) : lateHit t 0 = false := by simp [lateHit]

/-- **The run freezes after one step**, at two quanta on the never-missing candidate and the whole
budget on the competitor that missed once. -/
theorem raw_wRunFrom_lateHit {W : ℕ} (hW : 3 ≤ W) (t : ℕ) :
    raw (wRunFrom W (missFit lateHit) (lateStart W) (t + 1)) = ![2, W] := by
  have hW1 : 1 ≤ W := by omega
  induction t with
  | zero =>
      rw [raw_wRunFrom_succ hW1]
      have hstart : raw (wRunFrom W (missFit lateHit) (lateStart W) 0) = ![1, W] := by
        change raw (lateStart W : WVec 2 W) = _
        funext i
        change min (![(1 : ℕ), W] i) W = _
        fin_cases i
        all_goals simp
        all_goals omega
      have hu : bayesStep (missFit lateHit 0) ![1, W] = ![2, W] := by
        have h0 : missFit lateHit 0 0 = 2 := missFit_eq_two (by simp [lateHit])
        have h1 : missFit lateHit 0 1 = 1 := missFit_eq_one (by simp [lateHit])
        funext i
        rw [bayesStep]
        fin_cases i <;> simp [h0, h1]
      have hm : wMax (![(2 : ℕ), W]) = W := by rw [wMax_two]; simp; omega
      have hd : scaleDiv W ![(2 : ℕ), W] = 1 := by
        rw [scaleDiv, hm]
        have : (W + W - 1) / W = 1 := Nat.div_eq_of_lt_le (by omega) (by omega)
        omega
      rw [hstart, hu]
      funext i
      rw [project, hd, Nat.div_one]
      fin_cases i
      all_goals simp
      all_goals omega
  | succ t ih =>
      rw [raw_wRunFrom_succ hW1, ih]
      have hf : ∀ i, missFit lateHit (t + 1) i = 2 := fun i =>
        missFit_eq_two (by simp [lateHit])
      have hu : bayesStep (missFit lateHit (t + 1)) ![2, W] = ![4, 2 * W] := by
        funext i
        rw [bayesStep, hf]
        fin_cases i
        all_goals simp
        all_goals ring
      have hm : wMax (![(4 : ℕ), 2 * W]) = 2 * W := by rw [wMax_two]; simp; omega
      have hd : scaleDiv W ![(4 : ℕ), 2 * W] = 2 := by
        rw [scaleDiv, hm]
        have : (2 * W + W - 1) / W = 2 := Nat.div_eq_of_lt_le (by omega) (by omega)
        omega
      rw [hu]
      funext i
      rw [project, hd]
      fin_cases i
      all_goals simp
      all_goals omega

/-- The frozen run reads its competitor: at three quanta or more the whole budget outweighs the
two the never-missing candidate has collected. -/
theorem argmax_wRunFrom_lateHit {W : ℕ} (hW : 3 ≤ W) (t : ℕ) :
    argmax (raw (wRunFrom W (missFit lateHit) (lateStart W) (t + 1))) = 1 := by
  rw [raw_wRunFrom_lateHit hW]
  refine argmax_eq_of_strict fun i hi => ?_
  have hi0 : i = 0 := by revert hi; fin_cases i <;> simp
  subst hi0
  simp
  omega

private theorem missCount_lateHit (t : ℕ) : missCount lateHit 1 (t + 1) = 1 := by
  have hset : ((Finset.range (t + 1)).filter fun s => lateHit s 1) = {0} := by
    ext s
    simp [lateHit]
  rw [missCount, hset]
  simp

/-- **The settled reading lies outside the version space.** From the uniform start the reading is a
candidate that has never missed; from this seeded start it is a candidate that has, while a
never-missing candidate sits in the pool the whole time.

The boundary is exact and is why the family is stated at three quanta: at `W = 2` the frozen state
ties at `(2, 2)` and the tie-keeping fold reads the never-missing candidate after all. -/
theorem argmax_wRunFrom_lateHit_missCount_ne_zero {W : ℕ} (hW : 3 ≤ W) (t : ℕ) :
    missCount lateHit (argmax (raw (wRunFrom W (missFit lateHit) (lateStart W) (t + 1)))) (t + 1)
      ≠ 0 := by
  rw [argmax_wRunFrom_lateHit hW, missCount_lateHit]
  omega

/-- The family's own boundary: at two quanta the frozen state ties and the reading is the
never-missing candidate, so three is where the refutation starts. -/
theorem argmax_wRunFrom_lateHit_at_two :
    argmax (raw (wRunFrom 2 (missFit lateHit) (lateStart 2) 1)) = 0 := by decide

/-! ### The identity clause needs two quanta -/

/-- Two candidates: candidate `0` misses at every step, candidate `1` never does. -/
def zeroMiss : ℕ → Fin 2 → Bool := fun _ i => decide ((i : ℕ) = 0)

theorem zeroMiss_realizable (t : ℕ) : zeroMiss t 1 = false := by simp [zeroMiss]

private theorem raw_wRunFrom_zeroMiss_eq_one (w₀ : WVec 2 1) (t : ℕ) (i : Fin 2) :
    raw (wRunFrom 1 (missFit zeroMiss) w₀ (t + 1)) i = 1 :=
  le_antisymm (raw_le_budget _ i) (one_le_raw_wRunFrom_succ le_rfl _ _ t i)

/-- At one quantum every weight is pinned from the first step on, so the tie-keeping fold sits on
candidate `0` whatever the start and whatever the fitness says. -/
private theorem argmax_wRunFrom_zeroMiss (w₀ : WVec 2 1) (t : ℕ) :
    argmax (raw (wRunFrom 1 (missFit zeroMiss) w₀ (t + 1))) = 0 := by
  have hone := raw_wRunFrom_zeroMiss_eq_one w₀ t
  have hmax : wMax (raw (wRunFrom 1 (missFit zeroMiss) w₀ (t + 1))) = 1 :=
    le_antisymm (Finset.sup_le fun i _ => le_of_eq (hone i))
      ((le_of_eq (hone 0).symm).trans (le_wMax _ 0))
  exact le_antisymm (argmax_le_of_eq_wMax (by rw [hone 0, hmax])) (Fin.zero_le _)

/-- **`2 ≤ W` is necessary for the identity clause.** At one quantum the reading settles — it is
constant from the first step — on a candidate that misses at *every* step, while the pool holds a
candidate that never misses. This is the weight-level form of the uniform-start suite's own `b = 0`
degeneracy, and it holds from every start. -/
theorem argmax_wRunFrom_zeroMiss_misses (w₀ : WVec 2 1) (T t : ℕ) :
    zeroMiss t (argmax (raw (wRunFrom 1 (missFit zeroMiss) w₀ (T + 1)))) = true := by
  rw [argmax_wRunFrom_zeroMiss]
  simp [zeroMiss]

/-! ### Realizability is load-bearing: without it the reading need not settle -/

private theorem argmax_wRun_altMiss_even {b t : ℕ} (ht : 2 * b ≤ t) (h2 : t % 2 = 0) :
    argmax (raw (wRun (2 ^ b) (missFit altMiss) t)) = 0 := by
  obtain ⟨h0, h1⟩ := expRun_altMiss b t
  have e0 : raw (wRun (2 ^ b) (missFit altMiss) t) 0 = 2 ^ b := by
    rw [wRun_eq_pow_expRun, h0, show min (t / 2) (b - t % 2) = b by omega]
  have e1 : raw (wRun (2 ^ b) (missFit altMiss) t) 1 = 2 ^ b := by
    rw [wRun_eq_pow_expRun, h1, show min ((t + 1) / 2) b = b by omega]
  have hmax : wMax (raw (wRun (2 ^ b) (missFit altMiss) t)) = 2 ^ b := by
    rw [wMax_two, e0, e1, max_self]
  exact le_antisymm (argmax_le_of_eq_wMax (by rw [e0, hmax])) (Fin.zero_le _)

private theorem argmax_wRun_altMiss_odd {b t : ℕ} (hb : 1 ≤ b) (ht : 2 * b ≤ t) (h2 : t % 2 = 1) :
    argmax (raw (wRun (2 ^ b) (missFit altMiss) t)) = 1 := by
  obtain ⟨h0, h1⟩ := expRun_altMiss b t
  have e0 : raw (wRun (2 ^ b) (missFit altMiss) t) 0 = 2 ^ (b - 1) := by
    rw [wRun_eq_pow_expRun, h0, show min (t / 2) (b - t % 2) = b - 1 by omega]
  have e1 : raw (wRun (2 ^ b) (missFit altMiss) t) 1 = 2 ^ b := by
    rw [wRun_eq_pow_expRun, h1, show min ((t + 1) / 2) b = b by omega]
  refine argmax_eq_of_strict fun i hi => ?_
  have hi0 : i = 0 := by revert hi; fin_cases i <;> simp
  subst hi0
  rw [e0, e1]
  exact Nat.pow_lt_pow_right (by norm_num) (by omega)

/-- **Without a realizable candidate the reading need not settle.** On the alternating family both
candidates miss infinitely often; past the horizon the pair of weights cycles between level and one
doubling apart, so the reading alternates between the two candidates forever. Every other hypothesis
of the settling theorem holds, so realizability is what is doing the work there. -/
theorem argmax_wRun_altMiss_not_eventually_const {b : ℕ} (hb : 1 ≤ b) (T : ℕ) :
    ∃ t, T ≤ t ∧ argmax (raw (wRun (2 ^ b) (missFit altMiss) t))
      ≠ argmax (raw (wRun (2 ^ b) (missFit altMiss) T)) := by
  by_cases h : argmax (raw (wRun (2 ^ b) (missFit altMiss) T)) = 0
  · refine ⟨2 * (T + b) + 1, by omega, ?_⟩
    rw [argmax_wRun_altMiss_odd hb (by omega) (by omega), h]
    decide
  · refine ⟨2 * (T + b), by omega, fun hh => h ?_⟩
    rw [← hh]
    exact argmax_wRun_altMiss_even (by omega) (by omega)

/-- The same refutation read at the seeded run, through the start bridge: the settling theorem's
realizability hypothesis cannot be dropped there either. -/
theorem argmax_wRunFrom_altMiss_not_eventually_const {b : ℕ} (hb : 1 ≤ b) (T : ℕ) :
    ∃ t, T ≤ t ∧
      argmax (raw (wRunFrom (2 ^ b) (missFit altMiss) (pack (2 ^ b) fun _ => 1) t))
        ≠ argmax (raw (wRunFrom (2 ^ b) (missFit altMiss) (pack (2 ^ b) fun _ => 1) T)) := by
  simpa only [wRunFrom_pack_one] using argmax_wRun_altMiss_not_eventually_const hb T

/-! ### `settled` is not the only shape the run reaches

Two mechanisms, each at a fixed instance, exhibit a vector the run reaches from the uniform start
that is not `settled W c` for *any* `c` — so the lock shape is what transports off a power-of-two
budget or off a single persistent candidate, and `settled` itself does not. -/

/-- **The persistent candidate stalls below a non-power-of-two budget.** `zeroMiss`'s candidate `1`
never misses; at `W = 3` the run is already a fixed point one step in, and the persistent candidate
has climbed to `2`, the last doubling the budget holds — not to `3`, the whole budget. -/
theorem raw_wRunFrom_zeroMiss_eq (t : ℕ) :
    raw (wRunFrom 3 (missFit zeroMiss) (pack 3 fun _ => 1) (t + 1)) = ![1, 2] := by
  induction t with
  | zero => decide
  | succ t ih =>
      rw [raw_wRunFrom_succ (by norm_num : (1 : ℕ) ≤ 3), ih]
      have hF : missFit zeroMiss (t + 1) = missFit zeroMiss 0 := rfl
      rw [hF]
      decide

/-- **The fixed point is not `settled`, at either candidate.** `settled 3 c` puts the whole budget
`3` on `c`; the run above never reaches coordinate `3` at all. -/
theorem raw_wRunFrom_zeroMiss_ne_settled (t : ℕ) (c : Fin 2) :
    raw (wRunFrom 3 (missFit zeroMiss) (pack 3 fun _ => 1) (t + 1)) ≠ settled 3 c := by
  rw [raw_wRunFrom_zeroMiss_eq t]
  fin_cases c <;> decide

/-- **Both candidates never miss** — the weakest realizable instance, and the second mechanism: a
candidate that stops missing keeps whatever weight it already holds. -/
def bothLead : ℕ → Fin 2 → Bool := fun _ _ => false

theorem bothLead_realizable (t : ℕ) : bothLead t 0 = false := rfl

/-- **A second candidate that stops missing keeps whatever weight it had.** At `W = 4`, with neither
candidate ever missing, the run from the uniform start settles at `![4, 4]` — outside the settled
family at every budget, since `settled` never puts the whole budget on more than one coordinate. -/
theorem raw_wRunFrom_bothLead_eq (t : ℕ) :
    raw (wRunFrom 4 (missFit bothLead) (pack 4 fun _ => 1) (t + 2)) = ![4, 4] := by
  induction t with
  | zero => decide
  | succ t ih =>
      have he : t + 1 + 2 = t + 2 + 1 := by omega
      rw [he, raw_wRunFrom_succ (by norm_num : (1 : ℕ) ≤ 4), ih]
      have hF : missFit bothLead (t + 2) = missFit bothLead 0 := rfl
      rw [hF]
      decide

theorem raw_wRunFrom_bothLead_ne_settled (t : ℕ) (c : Fin 2) :
    raw (wRunFrom 4 (missFit bothLead) (pack 4 fun _ => 1) (t + 2)) ≠ settled 4 c := by
  rw [raw_wRunFrom_bothLead_eq t]
  fin_cases c <;> decide

end Guards

end ALT

/-- info: 'ALT.wRunFrom_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.wRunFrom_add

set_option linter.style.longLine false in
/-- info: 'ALT.argmax_wRunFrom_eventually_const' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.argmax_wRunFrom_eventually_const

set_option linter.style.longLine false in
/-- info: 'ALT.argmax_wRunFrom_eventually_const_consistent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.argmax_wRunFrom_eventually_const_consistent

set_option linter.style.longLine false in
/-- info: 'ALT.argmax_wRunFrom_eventually_const_of_eventually_realizable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.argmax_wRunFrom_eventually_const_of_eventually_realizable

set_option linter.style.longLine false in
/-- info: 'ALT.argmax_wRunFrom_seededAlt_card_changes_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.argmax_wRunFrom_seededAlt_card_changes_eq

set_option linter.style.longLine false in
/-- info: 'ALT.argmax_wRunFrom_lateHit_missCount_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.argmax_wRunFrom_lateHit_missCount_ne_zero

set_option linter.style.longLine false in
/-- info: 'ALT.argmax_wRunFrom_zeroMiss_misses' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.argmax_wRunFrom_zeroMiss_misses

set_option linter.style.longLine false in
/-- info: 'ALT.argmax_wRun_altMiss_not_eventually_const' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.argmax_wRun_altMiss_not_eventually_const

set_option linter.style.longLine false in
/-- info: 'ALT.argmaxFrame_wWorld_eventually_const_wStartFrom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.argmaxFrame_wWorld_eventually_const_wStartFrom

set_option linter.style.longLine false in
/-- info: 'ALT.raw_wRunFrom_eventually_lock' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.raw_wRunFrom_eventually_lock

set_option linter.style.longLine false in
/-- info: 'ALT.raw_wRunFrom_eventually_settled' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.raw_wRunFrom_eventually_settled

set_option linter.style.longLine false in
/-- info: 'ALT.raw_wRunFrom_zeroMiss_ne_settled' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.raw_wRunFrom_zeroMiss_ne_settled

set_option linter.style.longLine false in
/-- info: 'ALT.raw_wRunFrom_bothLead_ne_settled' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.raw_wRunFrom_bothLead_ne_settled
