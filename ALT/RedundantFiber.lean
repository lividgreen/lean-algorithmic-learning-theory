/-
Copyright (c) 2026 Mykola Palamarchuk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mykola Palamarchuk
-/
module

public import ALT.LogMassEvent

-- Formal-check file, not Mathlib-destined: opt out of the house-style header linter.
set_option linter.style.header false

/-!
# The redundant fiber: recovery plus repetition ([Inevitability] §6, the survival core)

Proposition 6.1's structural clause (iii) asks a repair of the host: one-step erasure, a
non-expansive host, or a reading the damage cannot move. The weighted fiber's own carrier — a
population of `P` copies of the floored mixture, all reading the same base stream — supplies that
repair by construction, and this file proves it in three stages, in the sense of survival: the
composite's reading recovers from damage without any of the three structural conditions being
assumed of the host.

**Stage A — recovery.** A single floored fiber, damaged by a finite hit schedule on its own normal
form (the exponent vectors, so a hit keeps the carrier a power of two), settles after its last hit
exactly as an undamaged run restarted there (`dRun_eq_wRunFrom_of_hitFree`), hence settles at every
budget and for every finite schedule
(`argmax_dRun_eventually_const_of_eventually_realizable`). The recovery has a price, proved
directly over the schedule's own `Finset` index (`dSurpriseSet_card_mul_le`): past a hit landing on
a power-of-two vector, the seeded-start count (`LogMassEvent.floorSurpriseFrom_card_mul_le`) bounds
each segment's own surprises, and a schedule of several hits pays that bound once per hit, plus the
undamaged segment before the first one; the same bound restated over an explicit list of segments
is `segSurpriseCard_le`.

**Stage B — the P-fold carrier and the verifying decode.** `P` copies of the fiber step under the
*same* observation stream; the reading decodes the least-indexed copy whose current prediction
matches what the base actually does next (`compPredFrame`). Any two verifying copies decode the
same value — the observed transition itself — so a copy corrupt in its weights but correct in
its prediction still reads right (`compPredFrame_eq_of_mem_verifiers`). Priced on the flat carrier
over an arbitrary per-copy reading (`compFrameFlat`), the decode costs the three ingredient codes
plus one addressing term logarithmic in `P` (`KE_compFrameFlat_le`) — [Inevitability] Theorem
6.6(vi)'s decode half.

**Stage C — the intact copy, and per-step survival.** A damage schedule touching fewer than `P`
distinct copies in total always leaves one copy untouched (`exists_untouched_copy`), and an
untouched copy's trajectory is definitionally the single undamaged run
(`compRun_eq_wRunFrom_of_untouched`). Once that copy settles on a candidate consistent with the
base, it verifies at every later step, so the composite's reading equals the base's next state —
hence the undamaged composite's own reading — at any arrival pattern within the touch bound
(`compPredFrame_eq_next_of_touch_bound`, `compPredFrame_damaged_eq_undamaged_of_touch_bound`). The
touch bound is met whenever `P` exceeds the realizable event count times the per-event copy cost
(`compPredFrame_eq_next_of_realizable_budget`), assembling Proposition 6.1's structural clause
(iii) — the invariant-reading regime — from pieces this development has already proved. The touch
bound's other side is a guard (`compRun_synchronized_guard`): a schedule that touches every copy
defeats the reading however small its rate, since the copies recover only to be synchronized.

## Scope

The damage model itself — Proposition 6.1's (D1)/(D2), coupling corruption to misprediction and
bounding a hit's reach — is a **named hypothesis of the paper, not a theorem of this file**: every
theorem below quantifies over an arbitrary finite hit schedule of the stated shape, rather than
deriving that damage takes that shape from anything. This file's survival synthesis (Stages A–C)
is not yet a numbered proposition in any paper. The composite's own price — [Inevitability]
Theorem 6.6(vi), "P copies and the decode" — is formalized in its two halves across two files: the
`P`-fold carrier's cost is `SkewFiber.KE_skewWorldFin_powFiber_le`, and the decode's own cost,
priced here (`compFrameFlat`, `KE_compFrameFlat_le`), closes the clause.

Stage A's recovery price is proved directly over `dRun`'s own `Finset`-indexed schedule
(`dSurpriseSet_card_mul_le`), by induction on the schedule's size: `dRun_shift`/`dWrongMass_shift`
peel the earliest hit, and `dSurpriseSet_card_shift` turns that into a card split between the
undamaged segment before it and a damaged schedule in its own right, one hit smaller, after it. The
seeded, damaged exponent automaton (`dExpRun`, `raw_dRun_eq_pow_dExpRun`) is a companion normal-form
fact about the same packed `dRun` — the two share the landed automaton on every hit-free window
(`expStep`, via `raw_wRunFrom_eq_pow_expRunFrom`) — but the set-indexed price does not route through
it. `segSurpriseCard_le` restates the same bound over an explicit list of `(gap, landing)` segments
(`segRun`): Stage A's own decomposition where a schedule is naturally given as a list, not a bridge
the set-indexed price depends on. Stage C's survival theorems do not appeal to
`SurpriseBudget.survives_of_invariant`: the composite's own damage model — an override at named
copies, not a Hamming-bounded perturbation of one shared memory — is more direct to induct on than
to repackage as an instance of that structure.
-/


@[expose] public section

namespace WeightedFiber

open PersistenceCapacity AdditiveComplexity SkewFiber CodeEvalLaws

/-! ## Stage A — recovery: a damaged run settles, and its price is the seeded-start count -/

section Recovery

variable {C : ℕ}

/-- **A damaged run** ([Inevitability] §6, Proposition 6.1's damage model, restricted to an
arbitrary finite hit schedule). The ordinary generation, except at a hit time `t ∈ H`, where the
state that would ordinarily follow is discarded and replaced by `hit t`. `H`'s finiteness is what
gives the run a last hit, and hence a tail that is again an ordinary run. -/
def dRun (W : ℕ) (M : ℕ → Fin C → Bool) (w₀ : WVec C W) (H : Finset ℕ)
    (hit : ℕ → WVec C W) : ℕ → WVec C W
  | 0 => w₀
  | t + 1 => if t ∈ H then hit t else wGen W (missFit M t) (dRun W M w₀ H hit t)

/-- **Every finite subset of `ℕ` has a hit-free tail.** The schedule's own finiteness, made
explicit as a time after which no hit occurs. -/
theorem exists_hit_free_tail (H : Finset ℕ) : ∃ t₀, ∀ t, t₀ ≤ t → t ∉ H := by
  refine ⟨H.sup id + 1, fun t ht hmem => ?_⟩
  have hle : t ≤ H.sup id := Finset.le_sup (f := id) hmem
  omega

/-- **The damaged run's tail from any hit-free window is an undamaged run restarted there**
([Inevitability] §6, Finding 2 — the load-bearing identity, stated explicitly rather than left
to inference). Over any window `[t₀, t₀ + s)` that the schedule never hits, `s` further steps
of the damaged run are exactly `s` steps of `wRunFrom`, restarted at the damaged state at `t₀`
under the fitness stream shifted by `t₀`. Applied at a schedule's own hit-free tail this is
Finding 2's tail identity; applied between two consecutive hits it is what the recovery-price
corollary below sums over. -/
theorem dRun_eq_wRunFrom_of_hitFree (W : ℕ) (M : ℕ → Fin C → Bool) (w₀ : WVec C W)
    (H : Finset ℕ) (hit : ℕ → WVec C W) (t₀ : ℕ) {s : ℕ}
    (hfree : ∀ u, t₀ ≤ u → u < t₀ + s → u ∉ H) :
    dRun W M w₀ H hit (t₀ + s)
      = wRunFrom W (missFit fun n => M (t₀ + n)) (dRun W M w₀ H hit t₀) s := by
  induction s with
  | zero => rfl
  | succ s ih =>
      have hprev : ∀ u, t₀ ≤ u → u < t₀ + s → u ∉ H :=
        fun u hu hus => hfree u hu (by omega)
      have hthis : t₀ + s ∉ H := hfree (t₀ + s) (Nat.le_add_right _ _) (by omega)
      change dRun W M w₀ H hit (t₀ + s + 1) = _
      rw [dRun, ite_eq_right hthis, ih hprev]
      rfl

/-- **A damaged run agrees with the undamaged one below its own first hit** — the `t₀ = 0` instance
of the identity above, stated without the `t₀ + s` framing so it composes directly with a schedule
cut at its own minimum (`dRun_shift`). -/
theorem dRun_eq_wRunFrom_of_lt (W : ℕ) (M : ℕ → Fin C → Bool) (w₀ : WVec C W) (H : Finset ℕ)
    (hit : ℕ → WVec C W) {t : ℕ} (hfree : ∀ u, u < t → u ∉ H) :
    dRun W M w₀ H hit t = wRunFrom W (missFit M) w₀ t := by
  induction t with
  | zero => rfl
  | succ t ih =>
      have ht : t ∉ H := hfree t (Nat.lt_succ_self t)
      rw [dRun, ite_eq_right ht, ih (fun u hu => hfree u (by omega))]
      rfl

/-- **The reading settles for every finite hit schedule** ([Inevitability] §6, Finding 2 —
recovery). Eventual realizability of the same candidate that the undamaged fiber would need is
enough: the run settles past its last hit exactly as an ordinary one does
(`BasinSettling.argmax_wRunFrom_eventually_const_of_eventually_realizable`), composed with the tail
identity above. No structural condition on the host is assumed anywhere — a single floored fiber,
with no redundancy at all, already recovers from any finite-debt damage in this sense. -/
theorem argmax_dRun_eventually_const_of_eventually_realizable [NeZero C] {W : ℕ} (hW : 1 ≤ W)
    (M : ℕ → Fin C → Bool) (w₀ : WVec C W) (H : Finset ℕ) (hit : ℕ → WVec C W)
    {iR : Fin C} {T₀ : ℕ} (hR : ∀ t, T₀ ≤ t → M t iR = false) :
    ∃ T : ℕ, ∀ t, T ≤ t →
      argmax (raw (dRun W M w₀ H hit t)) = argmax (raw (dRun W M w₀ H hit T)) := by
  obtain ⟨t₀, ht₀⟩ := exists_hit_free_tail H
  obtain ⟨T', hT'⟩ := argmax_wRunFrom_eventually_const_of_eventually_realizable hW
    (fun n => M (t₀ + n)) (T₀ := T₀) (fun n hn => hR (t₀ + n) (by omega))
    (dRun W M w₀ H hit t₀)
  refine ⟨t₀ + T', fun t ht => ?_⟩
  obtain ⟨s, rfl⟩ : ∃ s, t = t₀ + s := ⟨t - t₀, by omega⟩
  have hs : T' ≤ s := by omega
  rw [dRun_eq_wRunFrom_of_hitFree W M w₀ H hit t₀ (fun u hu _ => ht₀ u hu),
    dRun_eq_wRunFrom_of_hitFree W M w₀ H hit t₀ (fun u hu _ => ht₀ u hu)]
  exact hT' s hs

/-! ### The damaged exponent run and its normal form

`dRun`'s hit-free windows already run `expStep` on a power-of-two carrier
(`raw_wRunFrom_eq_pow_expRunFrom`); `dExpRun` is the same automaton with hits included, so a
damaged run started and landed on power-of-two vectors again has an exact exponent normal form. -/

/-- **The damaged exponent run** ([Inevitability] §6, Finding 2's normal form, with damage).
Mirrors `dRun`'s own hit convention exactly on the exponent automaton: at a hit time `t ∈ H` the
exponent vector is overridden by `hit t`, and otherwise it steps by `expStep`. -/
def dExpRun (b : ℕ) (M : ℕ → Fin C → Bool) (e₀ : Fin C → ℕ) (H : Finset ℕ)
    (hit : ℕ → Fin C → ℕ) : ℕ → Fin C → ℕ
  | 0 => e₀
  | t + 1 => if t ∈ H then hit t else expStep b (M t) (dExpRun b M e₀ H hit t)

/-- **The exponents never leave the budget**, from a start and every landing inside it —
`dExpRun`'s own instance of `expRunFrom_le`, with the hit branch discharged by the landing bound
directly. -/
theorem dExpRun_le {b : ℕ} {e₀ : Fin C → ℕ} (he₀ : ∀ i, e₀ i ≤ b) (M : ℕ → Fin C → Bool)
    {H : Finset ℕ} {hit : ℕ → Fin C → ℕ} (hhit : ∀ s ∈ H, ∀ i, hit s i ≤ b) (t : ℕ) (i : Fin C) :
    dExpRun b M e₀ H hit t i ≤ b := by
  induction t generalizing i with
  | zero => exact he₀ i
  | succ t ih =>
      by_cases ht : t ∈ H
      · rw [dExpRun, ite_eq_left ht]
        exact hhit t ht i
      · rw [dExpRun, ite_eq_right ht]
        rw [expStep]
        have hi := ih i
        by_cases hδ : ∃ j, dExpRun b M e₀ H hit t j = b ∧ M t j = false
        · rw [ite_eq_left hδ]
          split <;> omega
        · rw [ite_eq_right hδ]
          by_cases hm : M t i
          · rw [ite_eq_left hm]; omega
          · rw [ite_eq_right hm]
            have : dExpRun b M e₀ H hit t i ≠ b := fun hb => hδ ⟨i, hb, by simpa using hm⟩
            omega

/-- **The seeded, damaged normal form.** From a power-of-two start with every landing a power of
two inside the budget, `dRun` on the packed carrier is again exactly `2 ^ dExpRun`: the hit case is
immediate from the landing's own bound (`pack` does not clamp inside the budget), and the non-hit
case is `raw_wRunFrom_eq_pow_expRunFrom`'s own step, unchanged. -/
theorem raw_dRun_eq_pow_dExpRun {b : ℕ} {e₀ : Fin C → ℕ} (he₀ : ∀ i, e₀ i ≤ b)
    (M : ℕ → Fin C → Bool) {H : Finset ℕ} {hit : ℕ → Fin C → ℕ}
    (hhit : ∀ s ∈ H, ∀ i, hit s i ≤ b) (t : ℕ) (i : Fin C) :
    raw (dRun (2 ^ b) M (pack (2 ^ b) fun j => 2 ^ e₀ j) H
        (fun s => pack (2 ^ b) fun j => 2 ^ hit s j) t) i
      = 2 ^ dExpRun b M e₀ H hit t i := by
  have hW : 1 ≤ 2 ^ b := Nat.one_le_two_pow
  induction t generalizing i with
  | zero =>
      change raw (pack (2 ^ b) fun j => 2 ^ e₀ j) i = _
      rw [raw, pack]
      exact min_eq_left (Nat.pow_le_pow_right (by norm_num) (he₀ i))
  | succ t ih =>
      by_cases ht : t ∈ H
      · rw [dRun, ite_eq_left ht, dExpRun, ite_eq_left ht]
        rw [raw, pack]
        exact min_eq_left (Nat.pow_le_pow_right (by norm_num) (hhit t ht i))
      · set w := dRun (2 ^ b) M (pack (2 ^ b) fun j => 2 ^ e₀ j) H
          (fun s => pack (2 ^ b) fun j => 2 ^ hit s j) with hw
        have hstep : raw (w (t + 1))
            = project (2 ^ b) (bayesStep (missFit M t) (raw (w t))) := by
          rw [hw, dRun, ite_eq_right ht]
          exact raw_wGen hW _ _
        set u : Fin C → ℕ := bayesStep (missFit M t) (raw (w t)) with hu
        have hui : ∀ j, u j = 2 ^ (dExpRun b M e₀ H hit t j + (if M t j then 0 else 1)) := by
          intro j
          rw [hu, bayesStep, ih j, missFit]
          by_cases h : M t j
          · rw [ite_eq_left h, ite_eq_left h, Nat.mul_one, Nat.add_zero]
          · rw [ite_eq_right h, ite_eq_right h, pow_succ]
        rw [hstep, dExpRun, ite_eq_right ht]
        change project (2 ^ b) u i = 2 ^ expStep b (M t) (dExpRun b M e₀ H hit t) i
        rw [expStep, project]
        by_cases hδ : ∃ j, dExpRun b M e₀ H hit t j = b ∧ M t j = false
        · rw [ite_eq_left hδ]
          obtain ⟨j₀, hj₀e, hj₀m⟩ := hδ
          have hmax : wMax u = 2 ^ (b + 1) := by
            refine le_antisymm (Finset.sup_le fun j _ => ?_) ?_
            · rw [hui j]
              refine Nat.pow_le_pow_right (by norm_num) ?_
              have := dExpRun_le he₀ M hhit t j
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
          rcases Nat.eq_zero_or_pos (dExpRun b M e₀ H hit t i + (if M t i then 0 else 1))
            with h0 | hpos
          · rw [h0]
            norm_num
          · obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hpos.ne'
            rw [hk, pow_succ, Nat.mul_div_cancel _ (by norm_num), Nat.succ_sub_one]
            exact max_eq_right Nat.one_le_two_pow
        · rw [ite_eq_right hδ]
          have hle : wMax u ≤ 2 ^ b := by
            refine Finset.sup_le fun j _ => ?_
            rw [hui j]
            refine Nat.pow_le_pow_right (by norm_num) ?_
            have h1 := dExpRun_le he₀ M hhit t j
            by_cases hm : M t j
            · rw [ite_eq_left hm]; omega
            · rw [ite_eq_right hm]
              have : dExpRun b M e₀ H hit t j ≠ b := fun hb => hδ ⟨j, hb, by simpa using hm⟩
              omega
          have hd1 : scaleDiv (2 ^ b) u = 1 := by
            have hlt : (wMax u + 2 ^ b - 1) / 2 ^ b < 2 :=
              (Nat.div_lt_iff_lt_mul (by omega)).mpr (by omega)
            rw [scaleDiv]
            omega
          rw [hd1, Nat.div_one, hui i, Nat.sub_zero]
          exact max_eq_right Nat.one_le_two_pow

/-! ### The recovery price: a schedule of landings on the exponent automaton

Damage stated on the normal form's own state space, as Proposition 6.1(i) needs it: a landing is
an exponent vector bounded by `b`, so the carrier stays a power of two at every one, and
`LogMassEvent.floorSurpriseFrom_card_mul_le` prices the segment that follows. `segRun`/
`segSurpriseCard` take the schedule as an explicit list of `(gap, landing)` pairs rather than as
`dRun`'s own `Finset`: the list form's counting recursion is definitional (`rfl`), where the
set-indexed price below needs the separate splitting lemma `dSurpriseSet_card_shift`. -/

/-- **The damaged exponent run, given as an explicit schedule of landings.** `segs` lists, in
order, how many undamaged steps follow before the next landing and what that landing is; after the
last entry the run continues undamaged forever. This is the same automaton `dRun`'s hit-free
windows run (`expStep`, via `raw_wRunFrom_eq_pow_expRunFrom`), packaged for the counting argument
below. -/
def segRun (b : ℕ) :
    (Fin C → ℕ) → (ℕ → Fin C → Bool) → List (ℕ × (Fin C → ℕ)) → ℕ →
      Fin C → ℕ
  | e, M, [], t => expRunFrom e M b t
  | e, M, (Δ, e') :: rest, t =>
      if t < Δ then expRunFrom e M b t else segRun b e' (fun k => M (Δ + k)) rest (t - Δ)

/-- **The schedule's own surprise count**, mirroring `segRun`'s own (`t < Δ`) recursion exactly:
the count over any horizon is the current segment's own count up to the landing, plus the rest of
the schedule's count over what remains — the decomposition Finding 2's price sums over. -/
def segSurpriseCard (b : ℕ) (θ : ℚ) :
    (Fin C → ℕ) → (ℕ → Fin C → Bool) → List (ℕ × (Fin C → ℕ)) → ℕ → ℕ
  | e, M, [], n => (floorSurpriseSetFrom e M b θ n).card
  | e, M, (Δ, e') :: rest, n =>
      (floorSurpriseSetFrom e M b θ (min n Δ)).card
        + segSurpriseCard b θ e' (fun k => M (Δ + k)) rest (n - Δ)

/-- **The recovery price over a whole schedule** ([Inevitability] §6, Finding 2's arithmetic
corollary). A candidate `iR` realizable throughout, every landing (and the start) bounded by `b`
and by a common deficit `D` against `iR`: the schedule's surprise count over any horizon is at most
one seeded-start bound (`LogMassEvent.floorSurpriseFrom_card_mul_le`) per segment — the undamaged
budget for the first, and the same recovery price again for each of the schedule's hits. `θ`'s own
positivity is not needed; the bound is `LogMassEvent`'s own, applied once per segment and summed by
the recursion itself. -/
theorem segSurpriseCard_le {b D : ℕ} {iR : Fin C} {θ : ℚ}
    (hbudget : 2 * ((C : ℚ) - 1) ≤ θ * 2 ^ b) :
    ∀ (segs : List (ℕ × (Fin C → ℕ))) (e : Fin C → ℕ) (M : ℕ → Fin C → Bool)
      (n : ℕ),
      (∀ t, M t iR = false) → (∀ i, e i ≤ b) → Finset.univ.sup e - e iR ≤ D →
      (∀ p ∈ segs, (∀ i, p.2 i ≤ b) ∧ Finset.univ.sup p.2 - p.2 iR ≤ D) →
      (segSurpriseCard b θ e M segs n : ℚ) * θ
        ≤ (segs.length + 1) * (5 * ((D + Nat.log 2 C : ℕ) : ℚ) + 4) := by
  intro segs
  induction segs with
  | nil =>
      intro e M n hR he hDbound _
      have hbase := floorSurpriseFrom_card_mul_le he M hR θ hbudget n
      have hmono : ((Finset.univ.sup e - e iR + Nat.log 2 C : ℕ) : ℚ)
          ≤ ((D + Nat.log 2 C : ℕ) : ℚ) := by exact_mod_cast Nat.add_le_add_right hDbound _
      simp only [segSurpriseCard, List.length_nil, Nat.cast_zero, zero_add, one_mul]
      linarith [hbase, hmono]
  | cons p rest ih =>
      obtain ⟨Δ, e'⟩ := p
      intro e M n hR he hDbound hall
      obtain ⟨he', hDbound'⟩ := hall (Δ, e') List.mem_cons_self
      have hRshift : ∀ t, (fun k => M (Δ + k)) t iR = false := fun t => hR (Δ + t)
      have hrest := ih e' (fun k => M (Δ + k)) (n - Δ) hRshift he' hDbound'
        (fun q hq => hall q (List.mem_cons_of_mem _ hq))
      have hthis := floorSurpriseFrom_card_mul_le he M hR θ hbudget (min n Δ)
      have hmono : ((Finset.univ.sup e - e iR + Nat.log 2 C : ℕ) : ℚ)
          ≤ ((D + Nat.log 2 C : ℕ) : ℚ) := by exact_mod_cast Nat.add_le_add_right hDbound _
      have hthis' : ((floorSurpriseSetFrom e M b θ (min n Δ)).card : ℚ) * θ
          ≤ 5 * ((D + Nat.log 2 C : ℕ) : ℚ) + 4 := by linarith [hthis, hmono]
      have hcard : segSurpriseCard b θ e M ((Δ, e') :: rest) n
          = (floorSurpriseSetFrom e M b θ (min n Δ)).card
            + segSurpriseCard b θ e' (fun k => M (Δ + k)) rest (n - Δ) := rfl
      rw [hcard, List.length_cons]
      push_cast
      push_cast at hthis' hrest
      nlinarith [hthis', hrest]

/-! ### The recovery price over `dRun`'s own set-indexed schedule

The list form above is the corollary's own decomposition — a schedule handed over as a sequence of
`(gap, landing)` pairs, priced by structural recursion. The set-indexed price below is proved
directly: no bridge from `dRun` to `segRun` is needed, since `dWrongMass`/`dSurpriseSet` mirror
`wrongMassFrom`/`floorSurpriseSetFrom` over `dRun` itself. -/

/-- **The damaged run's own wrong mass**, mirroring `wrongMassFrom` over `dRun` on the packed
carrier rather than over `wRunFrom`. -/
def dWrongMass (b : ℕ) (M : ℕ → Fin C → Bool) (e₀ : Fin C → ℕ) (H : Finset ℕ)
    (hit : ℕ → Fin C → ℕ) (t : ℕ) : ℚ :=
  ∑ i, if M t i then
    toDist (raw (dRun (2 ^ b) M (pack (2 ^ b) fun j => 2 ^ e₀ j) H
      (fun s => pack (2 ^ b) fun j => 2 ^ hit s j) t)) i
    else 0

/-- **The damaged run's own surprise set**, mirroring `floorSurpriseSetFrom`: the strict-`θ<`
membership condition, over `dWrongMass` in place of `wrongMassFrom`. -/
def dSurpriseSet (b : ℕ) (M : ℕ → Fin C → Bool) (e₀ : Fin C → ℕ) (H : Finset ℕ)
    (hit : ℕ → Fin C → ℕ) (θ : ℚ) (n : ℕ) : Finset ℕ :=
  (Finset.range n).filter fun t => θ < dWrongMass b M e₀ H hit t

/-- **Below a schedule's first hit the damaged wrong mass is the undamaged one** —
`dRun_eq_wRunFrom_of_lt`, read through `wrongMassFrom`. -/
private theorem dWrongMass_eq_of_lt (b : ℕ) (M : ℕ → Fin C → Bool) (e₀ : Fin C → ℕ) (H : Finset ℕ)
    (hit : ℕ → Fin C → ℕ) {t : ℕ} (hfree : ∀ u, u < t → u ∉ H) :
    dWrongMass b M e₀ H hit t = wrongMassFrom e₀ M b t := by
  rw [dWrongMass, wrongMassFrom,
    dRun_eq_wRunFrom_of_lt (2 ^ b) M (pack (2 ^ b) fun j => 2 ^ e₀ j) H
      (fun s => pack (2 ^ b) fun j => 2 ^ hit s j) hfree]

/-- **At the empty schedule the damaged wrong mass is the undamaged one**, the vacuous instance of
the bound above. -/
private theorem dWrongMass_eq_of_empty (b : ℕ) (M : ℕ → Fin C → Bool) (e₀ : Fin C → ℕ)
    (hit : ℕ → Fin C → ℕ) (t : ℕ) :
    dWrongMass b M e₀ ∅ hit t = wrongMassFrom e₀ M b t :=
  dWrongMass_eq_of_lt b M e₀ ∅ hit (fun u _ => Finset.notMem_empty u)

/-- **At the empty schedule the damaged surprise objects are the landed ones**, so every
undamaged-tail argument below reads directly against `floorSurpriseSetFrom`. -/
theorem dSurpriseSet_eq_of_empty (b : ℕ) (M : ℕ → Fin C → Bool) (e₀ : Fin C → ℕ)
    (hit : ℕ → Fin C → ℕ) (θ : ℚ) (n : ℕ) :
    dSurpriseSet b M e₀ ∅ hit θ n = floorSurpriseSetFrom e₀ M b θ n := by
  rw [dSurpriseSet, floorSurpriseSetFrom]
  exact Finset.filter_congr fun t _ => by rw [dWrongMass_eq_of_empty]

/-- **The damaged run restarts at its own minimum hit** ([Inevitability] §6, Finding 2's
recovery-price corollary — the bookkeeping step the capstone below inducts on). Past the earliest
hit `τ`, the run is again a damaged run in its own right: started from the landing `hit τ`, over
the remaining schedule reindexed by subtracting `τ + 1`, under the fitness stream shifted the same
way. Sound because `τ` is the minimum of `H`: every other element of `H` is at least `τ + 1`, where
the subtraction is injective. -/
theorem dRun_shift (W : ℕ) (M : ℕ → Fin C → Bool) (w₀ : WVec C W) (H : Finset ℕ)
    (hit : ℕ → WVec C W) {τ : ℕ} (hτmem : τ ∈ H) (hτmin : ∀ s ∈ H, τ ≤ s) (u : ℕ) :
    dRun W M w₀ H hit (τ + 1 + u)
      = dRun W (fun k => M (τ + 1 + k)) (hit τ) ((H.erase τ).image (· - (τ + 1)))
          (fun k => hit (τ + 1 + k)) u := by
  induction u with
  | zero => simp only [dRun, ite_eq_left hτmem]
  | succ u ih =>
      by_cases hmem : (τ + 1 + u) ∈ H
      · have hsub : (τ + 1 + u) - (τ + 1) = u := by omega
        have hne : τ + 1 + u ≠ τ := by omega
        have himg : u ∈ (H.erase τ).image (· - (τ + 1)) :=
          Finset.mem_image.mpr ⟨τ + 1 + u, Finset.mem_erase.mpr ⟨hne, hmem⟩, hsub⟩
        rw [show τ + 1 + (u + 1) = τ + 1 + u + 1 from by omega, dRun, ite_eq_left hmem,
          dRun, ite_eq_left himg]
      · have hnimg : u ∉ (H.erase τ).image (· - (τ + 1)) := by
          intro hc
          obtain ⟨s, hsmem, hsu⟩ := Finset.mem_image.mp hc
          have hne : s ≠ τ := (Finset.mem_erase.mp hsmem).1
          have hle := hτmin s (Finset.mem_of_mem_erase hsmem)
          have hseq : s = τ + 1 + u := by omega
          exact hmem (hseq ▸ Finset.mem_of_mem_erase hsmem)
        rw [show τ + 1 + (u + 1) = τ + 1 + u + 1 from by omega, dRun, ite_eq_right hmem, ih,
          dRun, ite_eq_right hnimg]
        rfl

/-- **The recursion `dRun_shift` gives for the seeded, exponent-landed schedule's own wrong mass**:
past the earliest hit `τ`, the run's wrong mass is again a damaged wrong mass in its own right,
started from the landing's own exponent vector `hit τ` over the reindexed rest of the schedule. -/
theorem dWrongMass_shift (b : ℕ) (M : ℕ → Fin C → Bool) (e₀ : Fin C → ℕ) (H : Finset ℕ)
    (hit : ℕ → Fin C → ℕ) {τ : ℕ} (hτmem : τ ∈ H) (hτmin : ∀ s ∈ H, τ ≤ s) (u : ℕ) :
    dWrongMass b M e₀ H hit (τ + 1 + u)
      = dWrongMass b (fun k => M (τ + 1 + k)) (hit τ) ((H.erase τ).image (· - (τ + 1)))
          (fun k => hit (τ + 1 + k)) u := by
  rw [dWrongMass, dWrongMass,
    dRun_shift (2 ^ b) M (pack (2 ^ b) fun j => 2 ^ e₀ j) H
      (fun s => pack (2 ^ b) fun j => 2 ^ hit s j) hτmem hτmin u]

/-- **The surprise count splits at a schedule's earliest hit** — `dRun_shift`'s consequence for
`dSurpriseSet`'s own cardinality. Below the hit the count is the undamaged one
(`dWrongMass_eq_of_lt`); from it on, `dWrongMass_shift` reindexes the rest of the schedule to a
damaged surprise set in its own right, started from the landing. -/
theorem dSurpriseSet_card_shift (b : ℕ) (M : ℕ → Fin C → Bool) (e₀ : Fin C → ℕ) (H : Finset ℕ)
    (hit : ℕ → Fin C → ℕ) (θ : ℚ) {τ : ℕ} (hτmem : τ ∈ H) (hτmin : ∀ s ∈ H, τ ≤ s) (n : ℕ) :
    (dSurpriseSet b M e₀ H hit θ n).card
      = (floorSurpriseSetFrom e₀ M b θ (min n (τ + 1))).card
        + (dSurpriseSet b (fun k => M (τ + 1 + k)) (hit τ) ((H.erase τ).image (· - (τ + 1)))
            (fun k => hit (τ + 1 + k)) θ (n - (τ + 1))).card := by
  have hfreeLt : ∀ t, t < τ + 1 → ∀ u, u < t → u ∉ H := by
    intro t ht u hu hmem
    exact absurd (hτmin u hmem) (by omega)
  by_cases hn : τ + 1 ≤ n
  · -- `τ + 1 ≤ n`: the split at `τ + 1` is genuine
    have hmin : min n (τ + 1) = τ + 1 := by omega
    set emb : ℕ ↪ ℕ := ⟨fun x => τ + 1 + x, fun a b hab => by
      change τ + 1 + a = τ + 1 + b at hab; omega⟩ with hemb
    have hembApply : ∀ x, emb x = τ + 1 + x := fun _ => rfl
    have hrange : Finset.range n = Finset.range (τ + 1) ∪ (Finset.range (n - (τ + 1))).map emb := by
      ext x
      simp only [Finset.mem_range, Finset.mem_union, Finset.mem_map, hembApply]
      constructor
      · intro hx
        by_cases hxlt : x < τ + 1
        · exact Or.inl hxlt
        · exact Or.inr ⟨x - (τ + 1), by omega, by omega⟩
      · rintro (hx | ⟨u, hu, rfl⟩) <;> omega
    have hdisj : Disjoint (Finset.range (τ + 1)) ((Finset.range (n - (τ + 1))).map emb) := by
      rw [Finset.disjoint_left]
      rintro x hx1 hx2
      simp only [Finset.mem_range] at hx1
      simp only [Finset.mem_map, hembApply] at hx2
      obtain ⟨u, -, hu⟩ := hx2
      omega
    have e1 : (Finset.range (τ + 1)).filter (fun t => θ < dWrongMass b M e₀ H hit t)
        = floorSurpriseSetFrom e₀ M b θ (τ + 1) := by
      rw [floorSurpriseSetFrom]
      exact Finset.filter_congr fun t ht => by
        rw [dWrongMass_eq_of_lt b M e₀ H hit (hfreeLt t (Finset.mem_range.mp ht))]
    have e2 : (((Finset.range (n - (τ + 1))).map emb).filter
          (fun t => θ < dWrongMass b M e₀ H hit t)).card
        = (dSurpriseSet b (fun k => M (τ + 1 + k)) (hit τ) ((H.erase τ).image (· - (τ + 1)))
            (fun k => hit (τ + 1 + k)) θ (n - (τ + 1))).card := by
      rw [Finset.filter_map, Finset.card_map, dSurpriseSet]
      congr 1
      refine Finset.filter_congr fun u _ => ?_
      simp only [Function.comp_apply, hembApply]
      rw [dWrongMass_shift b M e₀ H hit hτmem hτmin u]
    rw [hmin, dSurpriseSet, hrange, Finset.filter_union,
      Finset.card_union_of_disjoint
        (hdisj.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)),
      e1, e2]
  · -- `n < τ + 1`: the whole horizon is hit-free, and the tail is vacuous
    have hmin : min n (τ + 1) = n := by omega
    have hsub : n - (τ + 1) = 0 := by omega
    have hEq : dSurpriseSet b M e₀ H hit θ n = floorSurpriseSetFrom e₀ M b θ n := by
      rw [dSurpriseSet, floorSurpriseSetFrom]
      refine Finset.filter_congr fun t ht => ?_
      rw [dWrongMass_eq_of_lt b M e₀ H hit
        (hfreeLt t (by simp only [Finset.mem_range] at ht; omega))]
    rw [hmin, hsub, hEq, dSurpriseSet, Finset.range_zero, Finset.filter_empty,
      Finset.card_empty, Nat.add_zero]

/-- **The recovery price over the damaged run's own set-indexed schedule** ([Inevitability] §6,
Theorem 6.6(iv) — the first paper-level step, closed). The list-schedule corollary
(`segSurpriseCard_le`) transposed to `dRun`'s own `Finset`-indexed hits: a candidate `iR`
realizable throughout, the start and every landing bounded by `b` and by a common deficit `D`
against `iR`, the schedule's surprise count over any horizon is at most one seeded-start bound
(`LogMassEvent.floorSurpriseFrom_card_mul_le`) per hit, plus the undamaged segment's own. Induction
on `H.card`, peeling the earliest hit with `dSurpriseSet_card_shift`: the segment before it is
priced directly, the segment after it is a damaged schedule in its own right
(`dRun_shift`/`dWrongMass_shift`), one hit smaller. -/
theorem dSurpriseSet_card_mul_le {b D : ℕ} {iR : Fin C} {θ : ℚ}
    (hbudget : 2 * ((C : ℚ) - 1) ≤ θ * 2 ^ b) (M : ℕ → Fin C → Bool) (e₀ : Fin C → ℕ)
    (H : Finset ℕ) (hit : ℕ → Fin C → ℕ) (n : ℕ)
    (hR : ∀ t, M t iR = false) (he₀ : ∀ i, e₀ i ≤ b) (hDe₀ : Finset.univ.sup e₀ - e₀ iR ≤ D)
    (hhit : ∀ s ∈ H, (∀ i, hit s i ≤ b) ∧ Finset.univ.sup (hit s) - hit s iR ≤ D) :
    ((dSurpriseSet b M e₀ H hit θ n).card : ℚ) * θ
      ≤ (H.card + 1) * (5 * ((D + Nat.log 2 C : ℕ) : ℚ) + 4) := by
  have hmonoD : ∀ e' : Fin C → ℕ, Finset.univ.sup e' - e' iR ≤ D →
      ((Finset.univ.sup e' - e' iR + Nat.log 2 C : ℕ) : ℚ) ≤ ((D + Nat.log 2 C : ℕ) : ℚ) :=
    fun e' hDe' => by exact_mod_cast Nat.add_le_add_right hDe' _
  have baseEmpty : ∀ (M : ℕ → Fin C → Bool) (e₀ : Fin C → ℕ) (hit : ℕ → Fin C → ℕ) (n : ℕ),
      (∀ t, M t iR = false) → (∀ i, e₀ i ≤ b) → Finset.univ.sup e₀ - e₀ iR ≤ D →
      ((dSurpriseSet b M e₀ ∅ hit θ n).card : ℚ) * θ
        ≤ ((∅ : Finset ℕ).card + 1) * (5 * ((D + Nat.log 2 C : ℕ) : ℚ) + 4) := by
    intro M e₀ hit n hR he₀ hDe₀
    rw [dSurpriseSet_eq_of_empty]
    have hbase := floorSurpriseFrom_card_mul_le he₀ M hR θ hbudget n
    simp only [Finset.card_empty, Nat.cast_zero, zero_add, one_mul]
    linarith [hbase, hmonoD e₀ hDe₀]
  have main : ∀ k : ℕ, ∀ H : Finset ℕ, H.card ≤ k →
      ∀ (M : ℕ → Fin C → Bool) (e₀ : Fin C → ℕ) (hit : ℕ → Fin C → ℕ) (n : ℕ),
        (∀ t, M t iR = false) → (∀ i, e₀ i ≤ b) → Finset.univ.sup e₀ - e₀ iR ≤ D →
        (∀ s ∈ H, (∀ i, hit s i ≤ b) ∧ Finset.univ.sup (hit s) - hit s iR ≤ D) →
        ((dSurpriseSet b M e₀ H hit θ n).card : ℚ) * θ
          ≤ (H.card + 1) * (5 * ((D + Nat.log 2 C : ℕ) : ℚ) + 4) := by
    intro k
    induction k with
    | zero =>
        intro H hHk M e₀ hit n hR he₀ hDe₀ _
        have hHempty : H = ∅ := Finset.card_eq_zero.mp (by omega)
        subst hHempty
        exact baseEmpty M e₀ hit n hR he₀ hDe₀
    | succ k ih =>
        intro H hHk M e₀ hit n hR he₀ hDe₀ hhit
        rcases Finset.eq_empty_or_nonempty H with hempty | hne
        · subst hempty
          exact baseEmpty M e₀ hit n hR he₀ hDe₀
        · set τ := H.min' hne with hτ
          have hτmem : τ ∈ H := H.min'_mem hne
          have hτmin : ∀ s ∈ H, τ ≤ s := fun s hs => H.min'_le s hs
          obtain ⟨he', hD'⟩ := hhit τ hτmem
          have hcardEq : ((H.erase τ).image (· - (τ + 1))).card = H.card - 1 := by
            rw [Finset.card_image_of_injOn, Finset.card_erase_of_mem hτmem]
            intro a ha c hc hac
            have haH : a ∈ H := Finset.mem_of_mem_erase ha
            have hcH : c ∈ H := Finset.mem_of_mem_erase hc
            have hage : τ + 1 ≤ a := by
              have := hτmin a haH; have := Finset.ne_of_mem_erase ha; omega
            have hcge : τ + 1 ≤ c := by
              have := hτmin c hcH; have := Finset.ne_of_mem_erase hc; omega
            simp only at hac
            omega
          have hcardpos : 1 ≤ H.card := Finset.card_pos.mpr hne
          have hHcard : ((H.erase τ).image (· - (τ + 1))).card ≤ k := by omega
          have hrec := ih ((H.erase τ).image (· - (τ + 1))) hHcard
            (fun k => M (τ + 1 + k)) (hit τ) (fun k => hit (τ + 1 + k)) (n - (τ + 1))
            (fun t => hR (τ + 1 + t)) he' hD'
            (by
              intro s hs
              obtain ⟨s', hs'mem, hs'eq⟩ := Finset.mem_image.mp hs
              have hs'H : s' ∈ H := Finset.mem_of_mem_erase hs'mem
              have hs'ge : τ + 1 ≤ s' := by
                have := hτmin s' hs'H
                have := Finset.ne_of_mem_erase hs'mem
                omega
              have heq : τ + 1 + s = s' := by omega
              rw [heq]
              exact hhit s' hs'H)
          rw [hcardEq] at hrec
          have hcardsucc' : ((H.card - 1 : ℕ) : ℚ) + 1 = (H.card : ℚ) := by
            have h : (H.card - 1 : ℕ) + 1 = H.card := by omega
            exact_mod_cast h
          rw [hcardsucc'] at hrec
          have hrec' : ((dSurpriseSet b (fun k => M (τ + 1 + k)) (hit τ)
                ((H.erase τ).image (· - (τ + 1))) (fun k => hit (τ + 1 + k)) θ
                (n - (τ + 1))).card : ℚ) * θ
              ≤ (H.card : ℚ) * (5 * ((D + Nat.log 2 C : ℕ) : ℚ) + 4) := by exact_mod_cast hrec
          have hbaseSeg := floorSurpriseFrom_card_mul_le he₀ M hR θ hbudget (min n (τ + 1))
          have hbaseSeg' : ((floorSurpriseSetFrom e₀ M b θ (min n (τ + 1))).card : ℚ) * θ
              ≤ 5 * ((D + Nat.log 2 C : ℕ) : ℚ) + 4 := by linarith [hbaseSeg, hmonoD e₀ hDe₀]
          have hsplit := dSurpriseSet_card_shift b M e₀ H hit θ hτmem hτmin n
          have hsplitQ : ((dSurpriseSet b M e₀ H hit θ n).card : ℚ)
              = ((floorSurpriseSetFrom e₀ M b θ (min n (τ + 1))).card : ℚ)
                + ((dSurpriseSet b (fun k => M (τ + 1 + k)) (hit τ)
                    ((H.erase τ).image (· - (τ + 1))) (fun k => hit (τ + 1 + k)) θ
                    (n - (τ + 1))).card : ℚ) := by exact_mod_cast hsplit
          rw [hsplitQ, add_mul]
          nlinarith [hbaseSeg', hrec']
  exact main H.card H (le_refl H.card) M e₀ hit n hR he₀ hDe₀ hhit

/-! ### Which surprise set (D1) names: a refuting family

Proposition 6.1's damage model (D1) perturbs the guest only where its predictor is `ε`-surprised.
On this construction that sentence names two different sets — the damaged run's own surprises
(`dSurpriseSet`) and the undamaged run's (`floorSurpriseSetFrom`) — and neither contains the other
in general. `dSurpriseSet_card_mul_le` above already commits to the undamaged reading: its
hypothesis is stated over the schedule's own landings, not over the damaged run's own surprises.
Read on the run it damages instead, (D1) is not a budget at all — the family below exhibits a
schedule of every length whose every hit lands inside `dSurpriseSet`, while the same start and
stream cap the undamaged count at `2`. -/

private lemma reseed_dRun_eq {N t : ℕ} (ht : t < N) :
    dRun (2 ^ 2) (fun _ : ℕ => (![false, true] : Fin 2 → Bool))
      (pack (2 ^ 2) (fun j => 2 ^ (![0, 2] : Fin 2 → ℕ) j)) (Finset.range N)
      (fun _ => pack (2 ^ 2) (fun j => 2 ^ (![0, 2] : Fin 2 → ℕ) j)) t
      = pack (2 ^ 2) (fun j => 2 ^ (![0, 2] : Fin 2 → ℕ) j) := by
  cases t with
  | zero => rfl
  | succ t' =>
      have hmem : t' ∈ Finset.range N := Finset.mem_range.mpr (by omega)
      change dRun (2 ^ 2) (fun _ : ℕ => (![false, true] : Fin 2 → Bool))
        (pack (2 ^ 2) (fun j => 2 ^ (![0, 2] : Fin 2 → ℕ) j)) (Finset.range N)
        (fun _ => pack (2 ^ 2) (fun j => 2 ^ (![0, 2] : Fin 2 → ℕ) j)) (t' + 1) = _
      rw [dRun, ite_eq_left hmem]

private lemma reseed_dWrongMass_eq {N t : ℕ} (ht : t < N) :
    dWrongMass 2 (fun _ : ℕ => (![false, true] : Fin 2 → Bool)) (![0, 2] : Fin 2 → ℕ)
      (Finset.range N) (fun _ => (![0, 2] : Fin 2 → ℕ)) t = 4 / 5 := by
  rw [dWrongMass, Fin.sum_univ_two, reseed_dRun_eq ht]
  norm_num [raw, pack, toDist, Fin.sum_univ_two]

/-- **The damaged reading is not a budget** ([Inevitability] §6, Proposition 6.1's damage model,
read on the run it damages — IN-25). At `C = 2`, `b = 2`, `θ = 1/2`, candidate `1` missing at every
step and every hit re-seeding the run at its own start `![0, 2]`: every hit of a schedule of length
`N` lands inside the damaged run's own surprise set, for every `N`. The budget gate holds here with
equality (`2·(C−1) = θ·2^b = 2`), so this is not the sub-gate blow-up
`floorSurpriseFrom_unbounded_below_gate` already records — the family sits inside the gate, not
below it. -/
theorem dSurpriseSet_reseed_eq_range (N : ℕ) :
    dSurpriseSet 2 (fun _ : ℕ => (![false, true] : Fin 2 → Bool)) (![0, 2] : Fin 2 → ℕ)
      (Finset.range N) (fun _ => (![0, 2] : Fin 2 → ℕ)) (1 / 2 : ℚ) N = Finset.range N := by
  rw [dSurpriseSet]
  refine Finset.filter_true_of_mem fun t ht => ?_
  rw [reseed_dWrongMass_eq (Finset.mem_range.mp ht)]
  norm_num

-- The budget gate at these parameters, with equality: `2·(C−1) = θ·2^b` exactly.
example : 2 * ((2 : ℚ) - 1) ≤ (1 / 2 : ℚ) * 2 ^ (2 : ℕ) := by norm_num

private lemma reseed_wrongMassFrom_eq (t : ℕ) :
    wrongMassFrom (![0, 2] : Fin 2 → ℕ) (fun _ : ℕ => (![false, true] : Fin 2 → Bool)) 2 t
      = toDist (fun i => 2 ^ (expRunFrom (![0, 2] : Fin 2 → ℕ)
          (fun _ : ℕ => (![false, true] : Fin 2 → Bool)) 2 t i)) 1 := by
  have he₀ : ∀ i : Fin 2, (![0, 2] : Fin 2 → ℕ) i ≤ 2 := by decide
  rw [wrongMassFrom, Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Bool.false_eq_true, ite_false, ite_true,
    zero_add]
  congr 1
  funext i
  rw [raw_wRunFrom_eq_pow_expRunFrom he₀]

private lemma reseed_fixed (s : ℕ) :
    expRunFrom (![0, 2] : Fin 2 → ℕ) (fun _ : ℕ => (![false, true] : Fin 2 → Bool)) 2 (4 + s)
      = ![2, 0] := by
  induction s with
  | zero => decide
  | succ s ih =>
      rw [show 4 + (s + 1) = (4 + s) + 1 from by omega, expRunFrom, ih]
      decide

/-- **The undamaged reading, on the same start and stream, is a genuine budget.** The orbit
`![0,2] → ![1,2] → ![2,2] → ![2,1] → ![2,0]` (a fixed point from there on) has wrong mass `4/5,
2/3, 1/2, 1/3, 1/5`, so only the first two steps exceed `θ = 1/2` and every horizon's surprise
count is at most `2`. So the two readings of (D1) disagree sharply on this construction: unbounded
on the damaged run (`dSurpriseSet_reseed_eq_range`), capped at `2` on the undamaged one. -/
theorem floorSurpriseSetFrom_reseed_card_le (n : ℕ) :
    (floorSurpriseSetFrom (![0, 2] : Fin 2 → ℕ) (fun _ : ℕ => (![false, true] : Fin 2 → Bool))
        2 (1 / 2 : ℚ) n).card ≤ 2 := by
  have hsub : floorSurpriseSetFrom (![0, 2] : Fin 2 → ℕ)
      (fun _ : ℕ => (![false, true] : Fin 2 → Bool)) 2 (1 / 2 : ℚ) n ⊆ Finset.range 2 := by
    intro t ht
    rw [floorSurpriseSetFrom, Finset.mem_filter] at ht
    obtain ⟨-, hgt⟩ := ht
    rw [Finset.mem_range]
    by_contra hc
    rw [not_lt] at hc
    rw [reseed_wrongMassFrom_eq] at hgt
    rcases lt_or_ge t 3 with ht3 | ht3
    · have heq : t = 2 := by omega
      subst heq
      rw [show expRunFrom (![0, 2] : Fin 2 → ℕ) (fun _ : ℕ => (![false, true] : Fin 2 → Bool)) 2 2
          = ![2, 2] from by decide] at hgt
      norm_num [toDist, Fin.sum_univ_two] at hgt
    · rcases lt_or_ge t 4 with ht4 | ht4
      · have heq : t = 3 := by omega
        subst heq
        rw [show
            expRunFrom (![0, 2] : Fin 2 → ℕ) (fun _ : ℕ => (![false, true] : Fin 2 → Bool)) 2 3
              = ![2, 1] from by decide] at hgt
        norm_num [toDist, Fin.sum_univ_two] at hgt
      · obtain ⟨s, rfl⟩ : ∃ s, t = 4 + s := ⟨t - 4, by omega⟩
        rw [reseed_fixed] at hgt
        norm_num [toDist, Fin.sum_univ_two] at hgt
  calc (floorSurpriseSetFrom (![0, 2] : Fin 2 → ℕ)
      (fun _ : ℕ => (![false, true] : Fin 2 → Bool)) 2 (1 / 2 : ℚ) n).card
      ≤ (Finset.range 2).card := Finset.card_le_card hsub
    _ = 2 := Finset.card_range 2

end Recovery

/-! ## Stage B — the P-fold carrier and the verifying decode -/

section Composite

variable {n₁ C P : ℕ} {W : ℕ}

/-- **The verifying copies** ([Inevitability] §6, Finding 3): the members of the population whose
current prediction of the base matches what the base actually does next. Verification is
checkable against the observed transition, which is what a corrupted copy cannot spoof. -/
def verifiers [NeZero C] (S : Fin n₁ → Fin n₁) (dec : Fin C → Fin n₁ → Fin n₁)
    (x : Fin n₁) (v : Fin P → WVec C W) : Finset (Fin P) :=
  Finset.univ.filter fun i => dec (argmax (raw (v i))) x = S x

/-- **The composite reading**: the least-indexed verifying copy's prediction, falling back to
copy `0` when none verifies. Every theorem below arranges a verifying copy to exist, so the
fallback never fires in anything this file proves; it is here only to make the frame total. -/
def compPredFrame [NeZero C] [NeZero P] (S : Fin n₁ → Fin n₁)
    (dec : Fin C → Fin n₁ → Fin n₁) (x : Fin n₁) (v : Fin P → WVec C W) : Fin n₁ :=
  if h : (verifiers S dec x v).Nonempty then
    dec (argmax (raw (v ((verifiers S dec x v).min' h)))) x
  else dec (argmax (raw (v 0))) x

/-- **Value agreement** ([Inevitability] §6, Finding 3): any verifying copy decodes the observed
transition — trivially, since verification means exactly that — so the composite reading is
many-to-one in the copies exactly as the base-reading frame is many-to-one in codewords: a copy
corrupt in its weights but correct in its prediction still reads right. -/
theorem compPredFrame_eq_of_mem_verifiers [NeZero C] [NeZero P] {S : Fin n₁ → Fin n₁}
    {dec : Fin C → Fin n₁ → Fin n₁} {x : Fin n₁} {v : Fin P → WVec C W} {i : Fin P}
    (hi : i ∈ verifiers S dec x v) : compPredFrame S dec x v = S x := by
  have hne : (verifiers S dec x v).Nonempty := ⟨i, hi⟩
  have hmem : (verifiers S dec x v).min' hne ∈ verifiers S dec x v := Finset.min'_mem _ _
  rw [compPredFrame, dite_eq_left hne]
  simpa only [verifiers, Finset.mem_filter, Finset.mem_univ, true_and] using hmem

/-! ### The decode, generalized and priced ([Inevitability] Theorem 6.6(vi), the decode half)

`compPredFrame`'s reading, `argmax ∘ raw`, is a function of a copy's own state and of nothing
else — so the search this section prices is stated over an arbitrary per-copy state space `Fin n₂`
and an arbitrary reading `θ : Fin n₂ → Fin C`, folded onto the flat carrier `Fin (n₁ * n₂ ^ P)` the
pricing layer needs a `lensCode` for. `frameVerifiers`/`compFrame` mirror
`verifiers`/`compPredFrame` exactly, `List`-valued rather than `Finset`-valued: `List.finRange P`
lists the copies in increasing order, so its filter's own head (`List.getD · 0 default`) is
already the least verifying index, without a separate minimality argument, and the same shape is
what the Primrec builder below needs. -/

/-- **The verifying copies, on an arbitrary per-copy reading** ([Inevitability] §6, Finding 3,
generalized): `verifiers`, generalized from a raw weight vector's `argmax ∘ raw` reading to an
arbitrary per-copy state space `Fin n₂` and reading `θ`. -/
def frameVerifiers {n₂ : ℕ} (S : Fin n₁ → Fin n₁) (dec : Fin C → Fin n₁ → Fin n₁)
    (θ : Fin n₂ → Fin C) (x : Fin n₁) (v : Fin P → Fin n₂) : List (Fin P) :=
  (List.finRange P).filter fun i => decide (dec (θ (v i)) x = S x)

/-- **The composite reading, on an arbitrary per-copy reading** ([Inevitability] §6, Finding 3,
generalized): the least-indexed verifying copy's decoded prediction, falling back to copy `0` when
none verifies — `compPredFrame`'s own shape, generalized. -/
def compFrame {n₂ : ℕ} [NeZero P] (S : Fin n₁ → Fin n₁) (dec : Fin C → Fin n₁ → Fin n₁)
    (θ : Fin n₂ → Fin C) (x : Fin n₁) (v : Fin P → Fin n₂) : Fin n₁ :=
  dec (θ (v ((frameVerifiers S dec θ x v).getD 0 0))) x

/-- **Value agreement, generalized** — `compPredFrame_eq_of_mem_verifiers`'s own argument, over
`compFrame`. -/
theorem compFrame_eq_of_mem_verifiers {n₂ : ℕ} [NeZero P] {S : Fin n₁ → Fin n₁}
    {dec : Fin C → Fin n₁ → Fin n₁} {θ : Fin n₂ → Fin C} {x : Fin n₁} {v : Fin P → Fin n₂}
    {i : Fin P} (hi : i ∈ frameVerifiers S dec θ x v) :
    compFrame S dec θ x v = S x := by
  have hne : frameVerifiers S dec θ x v ≠ [] := List.ne_nil_of_mem hi
  have hmem : (frameVerifiers S dec θ x v).getD 0 0 ∈ frameVerifiers S dec θ x v := by
    have hlen : 0 < (frameVerifiers S dec θ x v).length := List.length_pos_of_ne_nil hne
    rw [List.getD_eq_getElem _ 0 hlen]
    exact List.getElem_mem hlen
  rw [frameVerifiers, List.mem_filter, decide_eq_true_eq] at hmem
  rw [compFrame]
  exact hmem.2

/-- **The composite decode, on the flat carrier** ([Inevitability] §6, Theorem 6.6(vi), the decode
half — priced by `KE_compFrameFlat_le`). `compFrame`, folded onto `Fin (n₁ * n₂ ^ P)`: `x` is the
base coordinate and `v` the `P` copies, read out of the composite fiber coordinate by
`finFunctionFinEquiv`. -/
def compFrameFlat {n₂ : ℕ} [NeZero P] (S : Fin n₁ → Fin n₁) (dec : Fin C → Fin n₁ → Fin n₁)
    (θ : Fin n₂ → Fin C) (p : Fin (n₁ * n₂ ^ P)) : Fin n₁ :=
  compFrame S dec θ (finProdFinEquiv.symm p).1 (finFunctionFinEquiv.symm (finProdFinEquiv.symm p).2)

/-- **Non-vacuity**: a flat state whose `i`-th copy verifies decodes to the base's own next state —
the flat analogue of `compPredFrame_eq_of_mem_verifiers`, over an arbitrary copy's raw reading
rather than membership in `frameVerifiers`. -/
theorem compFrameFlat_eq_of_exists {n₂ : ℕ} [NeZero P] {S : Fin n₁ → Fin n₁}
    {dec : Fin C → Fin n₁ → Fin n₁} {θ : Fin n₂ → Fin C} {p : Fin (n₁ * n₂ ^ P)} {i : Fin P}
    (hi : dec (θ (finFunctionFinEquiv.symm (finProdFinEquiv.symm p).2 i))
            (finProdFinEquiv.symm p).1 = S (finProdFinEquiv.symm p).1) :
    compFrameFlat S dec θ p = S (finProdFinEquiv.symm p).1 := by
  refine compFrame_eq_of_mem_verifiers (i := i) ?_
  rw [frameVerifiers, List.mem_filter, decide_eq_true_eq]
  exact ⟨List.mem_finRange i, hi⟩

/-- **The priced flat carrier is the composite guest's own state space** ([Inevitability] Theorem
6.6(vi)'s identification, the last residue of clause (vi)): `compFrameFlat`'s generalized decode,
instantiated at the per-copy space `n₂ := (W + 1) ^ C` with `θ` the fiber-only half of
`WeightedFiber.argmaxFrame`, agrees with `compPredFrame` on the composite's own carrier — the flat
`Fin (n₁ * ((W + 1) ^ C) ^ P)` is the population's own `Fin P → WVec C W`, read digitwise by
`finFunctionFinEquiv` at both levels (per copy, and over the population), exactly as `compPredFrame`
reads it directly. Neither side's tie-breaking order is observable here: every verifying copy
decodes to the same value `S x` (`compFrame_eq_of_mem_verifiers`,
`compPredFrame_eq_of_mem_verifiers`), so the two frames agree without needing `frameVerifiers`'s
least index and `verifiers`'s `Finset.min'` to be the same copy. -/
theorem compFrameFlat_eq_compPredFrame [NeZero C] [NeZero P] (S : Fin n₁ → Fin n₁)
    (dec : Fin C → Fin n₁ → Fin n₁) (x : Fin n₁) (v : Fin P → WVec C W) :
    compFrameFlat (n₂ := (W + 1) ^ C) S dec
        (fun q => argmax (raw (finFunctionFinEquiv.symm q)))
        (finProdFinEquiv (x, finFunctionFinEquiv fun j => finFunctionFinEquiv (v j)))
      = compPredFrame S dec x v := by
  set θ : Fin ((W + 1) ^ C) → Fin C := fun q => argmax (raw (finFunctionFinEquiv.symm q)) with hθ
  have hθv : ∀ j, θ (finFunctionFinEquiv (v j)) = argmax (raw (v j)) := by
    intro j
    simp only [hθ, Equiv.symm_apply_apply]
  have hflat : compFrameFlat (n₂ := (W + 1) ^ C) S dec θ
      (finProdFinEquiv (x, finFunctionFinEquiv fun j => finFunctionFinEquiv (v j)))
      = compFrame S dec θ x (fun j => finFunctionFinEquiv (v j)) := by
    rw [compFrameFlat]
    simp only [Equiv.symm_apply_apply]
  rw [hflat, compFrame]
  by_cases hne : (verifiers S dec x v).Nonempty
  · obtain ⟨i, hiv⟩ := hne
    have hif : i ∈ frameVerifiers S dec θ x (fun j => finFunctionFinEquiv (v j)) := by
      rw [frameVerifiers, List.mem_filter, decide_eq_true_eq]
      refine ⟨List.mem_finRange i, ?_⟩
      rw [hθv]
      simpa only [verifiers, Finset.mem_filter, Finset.mem_univ, true_and] using hiv
    have hleft : dec (θ ((fun j => finFunctionFinEquiv (v j))
        ((frameVerifiers S dec θ x (fun j => finFunctionFinEquiv (v j))).getD 0 0))) x = S x := by
      have := compFrame_eq_of_mem_verifiers (S := S) (dec := dec) hif
      rwa [compFrame] at this
    rw [hleft, compPredFrame_eq_of_mem_verifiers hiv]
  · have heq : verifiers S dec x v = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    have hempty : frameVerifiers S dec θ x (fun j => finFunctionFinEquiv (v j)) = [] := by
      rw [List.eq_nil_iff_forall_not_mem]
      intro i hmem
      rw [frameVerifiers, List.mem_filter, decide_eq_true_eq] at hmem
      have hiv : i ∈ verifiers S dec x v := by
        rw [verifiers, Finset.mem_filter]
        exact ⟨Finset.mem_univ i, hθv i ▸ hmem.2⟩
      rw [heq] at hiv
      exact absurd hiv (Finset.notMem_empty i)
    rw [hempty, List.getD_nil, hθv, compPredFrame, dite_eq_right hne]

end Composite

/-! ### The decode's price: a bounded search over the population

`compFrameFlat`'s search is priced by the same recipe as `SkewFiber.skewTableFn` (weave two
tables with one fixed builder) composed with `PersistenceCapacity`'s bounded-search recipe (filter
`List.range P`, select by `List.getD`, precedented by `candList`/`gradedTableFn`): the three
ingredient tables and `P` are packed into one natural number, and one fixed builder — independent
of `n₁`, `n₂`, `C`, and `P` — reads the tables' own lengths to recover the structural sizes, exactly
as `skewTableFn` does. `dec`'s table is `fiberFlat dec`'s, at width `n₁` (`dec`'s own shape,
`Fin C → Fin n₁ → Fin n₁`, is `fiberFlat`'s at `(C, n₁)`), so `C` is recovered as
`(lensTable (fiberFlat dec)).length / n₁`; `n₁`, `n₂` are the other two tables' own lengths. -/

/-- **The composite decode's raw arithmetic, at one flat index** — the per-copy decode
`Tdec.getD (Tθ.getD (digit c) 0 * n1 + x) 0`, `digit c := w / n2 ^ c % n2` reading copy `c`'s state
off `w`'s own base-`n2` expansion (`finFunctionFinEquiv`'s convention), evaluated at the least `c`
whose decode matches `TS`'s own entry at `x`. `n1 := TS.length` is read off `TS`, not carried
separately: `decAtRaw'` never needs `n2`'s own witness beyond `Tθ.length`, so only `TS` is loaded as
a table for this purpose. -/
private def decAtRaw' (TS Tdec Tθ : List ℕ) (x w c : ℕ) : ℕ :=
  Tdec.getD (Tθ.getD (w / Tθ.length ^ c % Tθ.length) 0 * TS.length + x) 0

private theorem primrec_decAtRaw' :
    Primrec₂ fun (param : List ℕ × List ℕ × List ℕ × ℕ × ℕ) (c : ℕ) =>
      decAtRaw' param.1 param.2.1 param.2.2.1 param.2.2.2.1 param.2.2.2.2 c := by
  have hpow : Primrec₂ ((· ^ ·) : ℕ → ℕ → ℕ) := Primrec₂.unpaired'.1 Nat.Primrec.pow
  have hTS : Primrec fun p : (List ℕ × List ℕ × List ℕ × ℕ × ℕ) × ℕ => p.1.1 :=
    Primrec.fst.comp Primrec.fst
  have hTdec : Primrec fun p : (List ℕ × List ℕ × List ℕ × ℕ × ℕ) × ℕ => p.1.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have hTθ : Primrec fun p : (List ℕ × List ℕ × List ℕ × ℕ × ℕ) × ℕ => p.1.2.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
  have hx : Primrec fun p : (List ℕ × List ℕ × List ℕ × ℕ × ℕ) × ℕ => p.1.2.2.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))
  have hw : Primrec fun p : (List ℕ × List ℕ × List ℕ × ℕ × ℕ) × ℕ => p.1.2.2.2.2 :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))
  have hc : Primrec fun p : (List ℕ × List ℕ × List ℕ × ℕ × ℕ) × ℕ => p.2 := Primrec.snd
  have hn1 : Primrec fun p : (List ℕ × List ℕ × List ℕ × ℕ × ℕ) × ℕ => p.1.1.length :=
    Primrec.list_length.comp hTS
  have hn2 : Primrec fun p : (List ℕ × List ℕ × List ℕ × ℕ × ℕ) × ℕ => p.1.2.2.1.length :=
    Primrec.list_length.comp hTθ
  have hn2c : Primrec fun p : (List ℕ × List ℕ × List ℕ × ℕ × ℕ) × ℕ => p.1.2.2.1.length ^ p.2 :=
    hpow.comp hn2 hc
  have hdigit : Primrec fun p : (List ℕ × List ℕ × List ℕ × ℕ × ℕ) × ℕ =>
      p.1.2.2.2.2 / p.1.2.2.1.length ^ p.2 % p.1.2.2.1.length :=
    Primrec.nat_mod.comp (Primrec.nat_div.comp hw hn2c) hn2
  have hθlook : Primrec fun p : (List ℕ × List ℕ × List ℕ × ℕ × ℕ) × ℕ =>
      p.1.2.2.1.getD (p.1.2.2.2.2 / p.1.2.2.1.length ^ p.2 % p.1.2.2.1.length) 0 :=
    (Primrec.list_getD 0).comp hTθ hdigit
  have hidx : Primrec fun p : (List ℕ × List ℕ × List ℕ × ℕ × ℕ) × ℕ =>
      p.1.2.2.1.getD (p.1.2.2.2.2 / p.1.2.2.1.length ^ p.2 % p.1.2.2.1.length) 0 * p.1.1.length
        + p.1.2.2.2.1 :=
    Primrec.nat_add.comp (Primrec.nat_mul.comp hθlook hn1) hx
  exact Primrec₂.mk ((Primrec.list_getD 0).comp hTdec hidx)

/-- **The composite decode's raw arithmetic, tabulated over one flat state** `q`: `x`/`w` split `q`
at `n2 ^ P` (`finProdFinEquiv`'s own convention), and the decode searches `List.range P` for the
least verifying copy, falling back to copy `0` — `List.getD · 0 0` on a filtered `List.range`, the
`candList`/`gradedTableFn` recipe. -/
def compFrameEntry (TS Tdec Tθ : List ℕ) (P q : ℕ) : ℕ :=
  let n2 := Tθ.length
  let x := q / n2 ^ P
  let w := q % n2 ^ P
  let decAt := fun c => Tdec.getD (Tθ.getD (w / n2 ^ c % n2) 0 * TS.length + x) 0
  decAt (((List.range P).filter fun c => decide (decAt c = TS.getD x 0)).getD 0 0)

private theorem primrec_compFrameEntry :
    Primrec fun p : ((List ℕ × List ℕ × List ℕ) × ℕ) × ℕ =>
      compFrameEntry p.1.1.1 p.1.1.2.1 p.1.1.2.2 p.1.2 p.2 := by
  have hpow : Primrec₂ ((· ^ ·) : ℕ → ℕ → ℕ) := Primrec₂.unpaired'.1 Nat.Primrec.pow
  have hTS : Primrec fun p : ((List ℕ × List ℕ × List ℕ) × ℕ) × ℕ => p.1.1.1 :=
    Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
  have hTdec : Primrec fun p : ((List ℕ × List ℕ × List ℕ) × ℕ) × ℕ => p.1.1.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
  have hTθ : Primrec fun p : ((List ℕ × List ℕ × List ℕ) × ℕ) × ℕ => p.1.1.2.2 :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
  have hP : Primrec fun p : ((List ℕ × List ℕ × List ℕ) × ℕ) × ℕ => p.1.2 :=
    Primrec.snd.comp Primrec.fst
  have hq : Primrec fun p : ((List ℕ × List ℕ × List ℕ) × ℕ) × ℕ => p.2 := Primrec.snd
  have hn2 : Primrec fun p : ((List ℕ × List ℕ × List ℕ) × ℕ) × ℕ => p.1.1.2.2.length :=
    Primrec.list_length.comp hTθ
  have hn2P : Primrec fun p : ((List ℕ × List ℕ × List ℕ) × ℕ) × ℕ => p.1.1.2.2.length ^ p.1.2 :=
    hpow.comp hn2 hP
  have hx : Primrec fun p : ((List ℕ × List ℕ × List ℕ) × ℕ) × ℕ =>
      p.2 / p.1.1.2.2.length ^ p.1.2 :=
    Primrec.nat_div.comp hq hn2P
  have hw : Primrec fun p : ((List ℕ × List ℕ × List ℕ) × ℕ) × ℕ =>
      p.2 % p.1.1.2.2.length ^ p.1.2 :=
    Primrec.nat_mod.comp hq hn2P
  have hparam : Primrec fun p : ((List ℕ × List ℕ × List ℕ) × ℕ) × ℕ =>
      (p.1.1.1, p.1.1.2.1, p.1.1.2.2, p.2 / p.1.1.2.2.length ^ p.1.2,
        p.2 % p.1.1.2.2.length ^ p.1.2) :=
    hTS.pair (hTdec.pair (hTθ.pair (hx.pair hw)))
  have s1 : Primrec fun a : ℕ × (List ℕ × List ℕ × List ℕ × ℕ × ℕ) => a.2 := Primrec.snd
  have s2 : Primrec fun a : ℕ × (List ℕ × List ℕ × List ℕ × ℕ × ℕ) => a.2.2 := Primrec.snd.comp s1
  have s3 : Primrec fun a : ℕ × (List ℕ × List ℕ × List ℕ × ℕ × ℕ) => a.2.2.2 :=
    Primrec.snd.comp s2
  have s4 : Primrec fun a : ℕ × (List ℕ × List ℕ × List ℕ × ℕ × ℕ) => a.2.2.2.2 :=
    Primrec.snd.comp s3
  have hgc : Primrec fun a : ℕ × (List ℕ × List ℕ × List ℕ × ℕ × ℕ) => a.1 := Primrec.fst
  have hgparam : Primrec fun a : ℕ × (List ℕ × List ℕ × List ℕ × ℕ × ℕ) => a.2 := s1
  have hgTS : Primrec fun a : ℕ × (List ℕ × List ℕ × List ℕ × ℕ × ℕ) => a.2.1 :=
    Primrec.fst.comp s1
  have hgx : Primrec fun a : ℕ × (List ℕ × List ℕ × List ℕ × ℕ × ℕ) => a.2.2.2.2.1 :=
    Primrec.fst.comp s4
  have hR : PrimrecRel fun (c : ℕ) (param : List ℕ × List ℕ × List ℕ × ℕ × ℕ) =>
      decAtRaw' param.1 param.2.1 param.2.2.1 param.2.2.2.1 param.2.2.2.2 c
        = param.1.getD param.2.2.2.1 0 :=
    Primrec.eq.comp (primrec_decAtRaw'.comp hgparam hgc) ((Primrec.list_getD 0).comp hgTS hgx)
  have hfilt : Primrec fun p : ((List ℕ × List ℕ × List ℕ) × ℕ) × ℕ =>
      (List.range p.1.2).filter fun c => decide
        (decAtRaw' p.1.1.1 p.1.1.2.1 p.1.1.2.2 (p.2 / p.1.1.2.2.length ^ p.1.2)
            (p.2 % p.1.1.2.2.length ^ p.1.2) c
          = p.1.1.1.getD (p.2 / p.1.1.2.2.length ^ p.1.2) 0) :=
    (PrimrecRel.listFilter hR).comp (Primrec.list_range.comp hP) hparam
  have hselIdx : Primrec fun p : ((List ℕ × List ℕ × List ℕ) × ℕ) × ℕ =>
      (((List.range p.1.2).filter fun c => decide
        (decAtRaw' p.1.1.1 p.1.1.2.1 p.1.1.2.2 (p.2 / p.1.1.2.2.length ^ p.1.2)
            (p.2 % p.1.1.2.2.length ^ p.1.2) c
          = p.1.1.1.getD (p.2 / p.1.1.2.2.length ^ p.1.2) 0)).getD 0 0) :=
    (Primrec.list_getD 0).comp hfilt (Primrec.const 0)
  have hfinal := primrec_decAtRaw'.comp hparam hselIdx
  exact hfinal.of_eq fun p => rfl

/-- **The composite decode's table.** `n1 := TS.length`, `n2 := Tθ.length` are read off the tables,
so no size parameter is loaded — only `P`, which cannot be recovered from any table's length. -/
def compFrameTable (TS Tdec Tθ : List ℕ) (P : ℕ) : List ℕ :=
  (List.range (TS.length * Tθ.length ^ P)).map (compFrameEntry TS Tdec Tθ P)

private theorem primrec_compFrameTable :
    Primrec fun p : (List ℕ × List ℕ × List ℕ) × ℕ =>
      compFrameTable p.1.1 p.1.2.1 p.1.2.2 p.2 := by
  have hpow : Primrec₂ ((· ^ ·) : ℕ → ℕ → ℕ) := Primrec₂.unpaired'.1 Nat.Primrec.pow
  have hTS : Primrec fun p : (List ℕ × List ℕ × List ℕ) × ℕ => p.1.1 :=
    Primrec.fst.comp Primrec.fst
  have hTθ : Primrec fun p : (List ℕ × List ℕ × List ℕ) × ℕ => p.1.2.2 :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.fst)
  have hP : Primrec fun p : (List ℕ × List ℕ × List ℕ) × ℕ => p.2 := Primrec.snd
  have hbound : Primrec fun p : (List ℕ × List ℕ × List ℕ) × ℕ =>
      p.1.1.length * p.1.2.2.length ^ p.2 :=
    Primrec.nat_mul.comp (Primrec.list_length.comp hTS)
      (hpow.comp (Primrec.list_length.comp hTθ) hP)
  exact Primrec.list_map (Primrec.list_range.comp hbound) (Primrec₂.mk primrec_compFrameEntry)

/-- A `fiberFlat`-shaped table's entry at a flat index, restated for `dec`'s own shape
(`SkewFiber.lensTable_getD_fiberFlat`'s content, unavailable here as it is file-local there). -/
private theorem lensTable_getD_fiberFlat' {a b : ℕ} (G : Fin a → Fin b → Fin b)
    (i : Fin a) (w : Fin b) :
    (lensTable (fiberFlat G)).getD ((i : ℕ) * b + w) 0 = (G i w : ℕ) := by
  have hval : (i : ℕ) * b + w = (finProdFinEquiv (i, w) : ℕ) := by
    rw [finProdFinEquiv_apply_val]; ring
  rw [hval, lensTable_getD _ (finProdFinEquiv (i, w)).isLt, fiberFlat_apply]

/-- **The least verifying `Fin P` and the least verifying raw `ℕ` agree**: `frameVerifiers`'
`List.finRange`-filtered search, read through `Fin.val`, is `List.range`'s own filtered search on
the corresponding raw predicate — the bridge the builder's correctness proof needs, since the
builder can only search over `List.range`. -/
private theorem finRange_filter_getD_val_eq {P : ℕ} [NeZero P] (pred : Fin P → Prop)
    [DecidablePred pred] (predN : ℕ → Prop) [DecidablePred predN]
    (hcompat : ∀ i : Fin P, pred i ↔ predN i.val) :
    (((List.finRange P).filter fun i => decide (pred i)).getD 0 (0 : Fin P) : ℕ)
      = ((List.range P).filter fun c => decide (predN c)).getD 0 0 := by
  have hmap : List.map (fun i : Fin P => (i : ℕ)) (List.finRange P) = List.range P :=
    List.map_coe_finRange_eq_range
  have hinj : Function.Injective (fun i : Fin P => (i : ℕ)) := Fin.val_injective
  have hfm : List.map (fun i : Fin P => (i : ℕ))
        ((List.finRange P).filter fun i => decide (pred i))
      = List.filter (fun b => decide (∃ a, (decide (pred a) = true) ∧ (a : ℕ) = b))
          (List.map (fun i : Fin P => (i : ℕ)) (List.finRange P)) :=
    List.map_filter (fun i => decide (pred i)) hinj (List.finRange P)
  rw [hmap] at hfm
  have hcongr : List.filter (fun b => decide (∃ a : Fin P, (decide (pred a) = true) ∧ (a : ℕ) = b))
      (List.range P) = List.filter (fun c => decide (predN c)) (List.range P) := by
    apply List.filter_congr
    intro b hb
    simp only [List.mem_range] at hb
    simp only [decide_eq_decide]
    constructor
    · rintro ⟨a, ha, hab⟩
      rw [decide_eq_true_eq] at ha
      subst hab
      exact (hcompat a).mp ha
    · intro h
      exact ⟨⟨b, hb⟩, by rw [decide_eq_true_eq]; exact (hcompat ⟨b, hb⟩).mpr h, rfl⟩
  rw [hcongr] at hfm
  have hval0 : ((0 : Fin P) : ℕ) = 0 := by simp
  rw [← hval0, ← hfm, List.getD_map]

/-- **The builder is correct**: the table it computes is `compFrameFlat`'s own `lensTable`. Case
split on `n1 = 0`/`n2 = 0` (the degenerate empty-carrier cases, as in `lensTable_skewWorldFin`);
otherwise the flat index splits at `n2 ^ P` (`finProdFinEquiv`'s convention), each copy's state is
a base-`n2` digit of the fiber coordinate (`finFunctionFinEquiv_symm_apply_val`), and the least
verifying raw index is the least verifying `Fin P` by `finRange_filter_getD_val_eq`. -/
private theorem compFrameTable_eq {n₁ n₂ C P : ℕ} [NeZero P] (S : Fin n₁ → Fin n₁)
    (dec : Fin C → Fin n₁ → Fin n₁) (θ : Fin n₂ → Fin C) :
    lensTable (compFrameFlat (P := P) S dec θ)
      = compFrameTable (lensTable S) (lensTable (fiberFlat dec)) (lensTable θ) P := by
  rcases Nat.eq_zero_or_pos n₁ with hn₁ | hn₁
  · subst hn₁
    simp [compFrameTable, lensTable]
  rcases Nat.eq_zero_or_pos n₂ with hn₂ | hn₂
  · subst hn₂
    have hP0 : P ≠ 0 := NeZero.ne P
    have h0P : (0 : ℕ) ^ P = 0 := zero_pow hP0
    simp [compFrameTable, h0P, lensTable]
  have hTSlen : (lensTable S).length = n₁ := lensTable_length S
  have hTθlen : (lensTable θ).length = n₂ := lensTable_length θ
  rw [lensTable_range]
  simp only [compFrameTable, hTSlen, hTθlen]
  refine List.map_congr_left fun q hq => ?_
  have hqlt : q < n₁ * n₂ ^ P := List.mem_range.mp hq
  rw [dite_eq_left hqlt]
  simp only [compFrameEntry, hTSlen, hTθlen]
  have hn2P : 0 < n₂ ^ P := pow_pos hn₂ P
  set x := q / n₂ ^ P with hxdef
  set w := q % n₂ ^ P with hwdef
  have hxlt : x < n₁ := Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm] at hqlt)
  have hwlt : w < n₂ ^ P := Nat.mod_lt _ hn2P
  have hidx : (⟨q, hqlt⟩ : Fin (n₁ * n₂ ^ P))
      = finProdFinEquiv (⟨x, hxlt⟩, (⟨w, hwlt⟩ : Fin (n₂ ^ P))) := by
    apply Fin.ext
    simp only [finProdFinEquiv_apply_val]
    rw [hxdef, hwdef]
    exact (Nat.mod_add_div q (n₂ ^ P)).symm
  change (compFrameFlat S dec θ ⟨q, hqlt⟩ : ℕ) = _
  rw [hidx, compFrameFlat]
  simp only [Equiv.symm_apply_apply]
  set v : Fin P → Fin n₂ := finFunctionFinEquiv.symm ⟨w, hwlt⟩ with hvdef
  have hv : ∀ c : Fin P, (v c : ℕ) = w / n₂ ^ (c : ℕ) % n₂ := by
    intro c
    rw [hvdef]
    exact finFunctionFinEquiv_symm_apply_val ⟨w, hwlt⟩ c
  set decAt : ℕ → ℕ := fun c => (lensTable (fiberFlat dec)).getD
      ((lensTable θ).getD (w / n₂ ^ c % n₂) 0 * n₁ + x) 0 with hdecAtdef
  have hdecAt : ∀ c : Fin P, decAt (c : ℕ) = (dec (θ (v c)) ⟨x, hxlt⟩ : ℕ) := by
    intro c
    rw [hdecAtdef]
    simp only
    rw [← hv c]
    have hvlt : (v c : ℕ) < n₂ := (v c).isLt
    rw [lensTable_getD θ hvlt]
    have hveq : (⟨(v c : ℕ), hvlt⟩ : Fin n₂) = v c := Fin.eta _ _
    rw [hveq, lensTable_getD_fiberFlat' dec (θ (v c)) ⟨x, hxlt⟩]
  have hTSx : (lensTable S).getD x 0 = (S ⟨x, hxlt⟩ : ℕ) := lensTable_getD S hxlt
  have hpredcompat : ∀ c : Fin P,
      (dec (θ (v c)) ⟨x, hxlt⟩ = S ⟨x, hxlt⟩) ↔ (decAt (c : ℕ) = (lensTable S).getD x 0) := by
    intro c
    rw [hdecAt c, hTSx]
    exact ⟨fun h => congrArg Fin.val h, fun h => Fin.ext h⟩
  have hbridge := finRange_filter_getD_val_eq (P := P)
    (fun i : Fin P => dec (θ (v i)) ⟨x, hxlt⟩ = S ⟨x, hxlt⟩)
    (fun c : ℕ => decAt c = (lensTable S).getD x 0) hpredcompat
  change (compFrame S dec θ ⟨x, hxlt⟩ v : ℕ) = _
  rw [compFrame, ← hdecAt ((frameVerifiers S dec θ ⟨x, hxlt⟩ v).getD 0 0)]
  exact congrArg decAt hbridge

/-- **The composite decode builder, from `⟨T_S, T_dec, T_θ, P⟩`** — ONE fixed function, with `P`
the only loaded numeral. -/
def compFrameTableFn (p : ℕ) : ℕ :=
  Encodable.encode (compFrameTable
    ((Encodable.decode (α := List ℕ) p.unpair.1).getD [])
    ((Encodable.decode (α := List ℕ) p.unpair.2.unpair.1).getD [])
    ((Encodable.decode (α := List ℕ) p.unpair.2.unpair.2.unpair.1).getD [])
    p.unpair.2.unpair.2.unpair.2)

private theorem primrec_compFrameTableFn : Primrec compFrameTableFn := by
  have hdec1 : Primrec fun p : ℕ => (Encodable.decode (α := List ℕ) p.unpair.1).getD [] :=
    Primrec.option_getD.comp
      (Primrec.decode.comp (Primrec.fst.comp Primrec.unpair)) (Primrec.const [])
  have hdec2 : Primrec fun p : ℕ =>
      (Encodable.decode (α := List ℕ) p.unpair.2.unpair.1).getD [] :=
    Primrec.option_getD.comp
      (Primrec.decode.comp
        (Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))))
      (Primrec.const [])
  have hdec3 : Primrec fun p : ℕ =>
      (Encodable.decode (α := List ℕ) p.unpair.2.unpair.2.unpair.1).getD [] :=
    Primrec.option_getD.comp
      (Primrec.decode.comp (Primrec.fst.comp (Primrec.unpair.comp
        (Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))))))
      (Primrec.const [])
  have hP : Primrec fun p : ℕ => p.unpair.2.unpair.2.unpair.2 :=
    Primrec.snd.comp (Primrec.unpair.comp
      (Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))))
  exact Primrec.encode.comp
    (primrec_compFrameTable.comp ((hdec1.pair (hdec2.pair hdec3)).pair hP))

/-- `compFrameTableFn` is partial recursive. -/
theorem partrec_compFrameTableFn : Nat.Partrec (fun p : ℕ => (compFrameTableFn p : ℕ)) :=
  _root_.Partrec.nat_iff.mp (Primrec.to_comp primrec_compFrameTableFn).partrec

/-- **The builder's packed correctness law.** -/
theorem compFrameTableFn_eq {n₁ n₂ C P : ℕ} [NeZero P] (S : Fin n₁ → Fin n₁)
    (dec : Fin C → Fin n₁ → Fin n₁) (θ : Fin n₂ → Fin C) :
    compFrameTableFn (Nat.pair (lensCode S) (Nat.pair (lensCode (fiberFlat dec))
        (Nat.pair (lensCode θ) P)))
      = lensCode (compFrameFlat (P := P) S dec θ) := by
  rw [compFrameTableFn]
  simp only [Nat.unpair_pair, decode_lensCode]
  rw [← compFrameTable_eq]
  rfl

/-- **The fixed composite-decode builder code.** One program, independent of the fiber, of `n₁`,
of `n₂`, of `C`, and of `P`. -/
noncomputable def compFrameBuilder : Nat.Partrec.Code :=
  Classical.choose (Nat.Partrec.Code.exists_code.mp partrec_compFrameTableFn)

private theorem eval_compFrameBuilder (p : ℕ) :
    Nat.Partrec.Code.eval compFrameBuilder p = Part.some (compFrameTableFn p) := by
  have h := congrFun (Classical.choose_spec
    (Nat.Partrec.Code.exists_code.mp partrec_compFrameTableFn)) p
  simpa [compFrameBuilder] using h

/-- **The composite decode's cheap code**: run the three ingredient codes, load `P` as a binary
numeral, hand all four to the fixed builder. -/
noncomputable def compFrameCode (cS cDec cθ : Nat.Partrec.Code) (P : ℕ) : Nat.Partrec.Code :=
  Nat.Partrec.Code.comp compFrameBuilder
    (Nat.Partrec.Code.pair cS (Nat.Partrec.Code.pair cDec
      (Nat.Partrec.Code.pair cθ (bconst P))))

theorem elen_compFrameCode_le (cS cDec cθ : Nat.Partrec.Code) (P : ℕ) :
    elen (compFrameCode cS cDec cθ P)
      ≤ elen cS + elen cDec + elen cθ + (15 + elen dbl) * Nat.size P
        + (elen compFrameBuilder + (15 + elen dbl) + 12) := by
  rw [compFrameCode, E_len_comp, E_len_pair, E_len_pair, E_len_pair]
  have hb := elen_bconst_le P
  omega

theorem eval_compFrameCode {n₁ n₂ C P : ℕ} [NeZero P] (S : Fin n₁ → Fin n₁)
    (dec : Fin C → Fin n₁ → Fin n₁) (θ : Fin n₂ → Fin C)
    (cS cDec cθ : Nat.Partrec.Code) (hS : cS.eval 0 = Part.some (lensCode S))
    (hDec : cDec.eval 0 = Part.some (lensCode (fiberFlat dec)))
    (hθ : cθ.eval 0 = Part.some (lensCode θ)) :
    (compFrameCode cS cDec cθ P).eval 0
      = Part.some (lensCode (compFrameFlat (P := P) S dec θ)) := by
  have hpn : Nat.Partrec.Code.eval (Nat.Partrec.Code.pair cθ (bconst P)) 0
      = Part.some (Nat.pair (lensCode θ) P) := by
    change Nat.pair <$> _ <*> _ = _
    rw [hθ, eval_bconst]; simp [Seq.seq]
  have hp2 : Nat.Partrec.Code.eval (Nat.Partrec.Code.pair cDec
      (Nat.Partrec.Code.pair cθ (bconst P))) 0
      = Part.some (Nat.pair (lensCode (fiberFlat dec)) (Nat.pair (lensCode θ) P)) := by
    change Nat.pair <$> _ <*> _ = _
    rw [hDec, hpn]; simp [Seq.seq]
  have hp1 : Nat.Partrec.Code.eval (Nat.Partrec.Code.pair cS (Nat.Partrec.Code.pair cDec
      (Nat.Partrec.Code.pair cθ (bconst P)))) 0
      = Part.some (Nat.pair (lensCode S)
          (Nat.pair (lensCode (fiberFlat dec)) (Nat.pair (lensCode θ) P))) := by
    change Nat.pair <$> _ <*> _ = _
    rw [hS, hp2]; simp [Seq.seq]
  rw [compFrameCode, eval_comp_some hp1, eval_compFrameBuilder, compFrameTableFn_eq]

/-- **The decode's price** ([Inevitability] Theorem 6.6(vi), the decode half — the theorem's one
remaining paper-level step, now closed). The three ingredient codes' lengths plus one addressing
term logarithmic in `P` (`Nat.size P`), plus an absolute constant independent of the world, of
`n₁`, `n₂`, `C`, and `P`. Assembled exactly as `SkewFiber.KE_skewWorldFin_powFiber_le` prices "P
copies": the composed code *runs* a bounded search over the population rather than carrying a
`P`-fold table, so `P` enters through `Nat.size P` alone. Together with
`SkewFiber.KE_skewWorldFin_powFiber_le`, this closes clause (vi) at the same level of identification
the rest of §6's pricing already runs at: the composite guest is `P` copies (there) and the
verifying decode (here), and both cost `O (log n₁ + log P)` over their own ingredients. -/
theorem KE_compFrameFlat_le {n₁ n₂ C P : ℕ} [NeZero P] (S : Fin n₁ → Fin n₁)
    (dec : Fin C → Fin n₁ → Fin n₁) (θ : Fin n₂ → Fin C)
    (cS cDec cθ : Nat.Partrec.Code) (hS : cS.eval 0 = Part.some (lensCode S))
    (hDec : cDec.eval 0 = Part.some (lensCode (fiberFlat dec)))
    (hθ : cθ.eval 0 = Part.some (lensCode θ)) :
    KE (lensCode (compFrameFlat (P := P) S dec θ))
      ≤ elen cS + elen cDec + elen cθ + (15 + elen dbl) * Nat.size P
        + (elen compFrameBuilder + (15 + elen dbl) + 12) := by
  have hle := KE_le (c := compFrameCode cS cDec cθ P)
    (eval_compFrameCode S dec θ cS cDec cθ hS hDec hθ)
  have hb := elen_compFrameCode_le cS cDec cθ P
  omega

/-! ## Stage C — the intact copy, and per-step survival -/

section Survival

variable {n₁ C P W : ℕ}

/-- **The `P`-fold carrier's damaged run** ([Inevitability] §6, Finding 3): every copy runs the
ordinary weighted-fiber generation under the *same* fitness stream; at a hit time `t ∈ H`, the
copies named by `col t` are overridden by `land t` instead, and every other copy still steps
ordinarily. `col`/`land` are consulted only at times in `H`. -/
def compRun (W : ℕ) (M : ℕ → Fin C → Bool) (v₀ : Fin P → WVec C W) (H : Finset ℕ)
    (col : ℕ → Finset (Fin P)) (land : ℕ → Fin P → WVec C W) : ℕ → Fin P → WVec C W
  | 0 => v₀
  | t + 1 => fun i =>
      if t ∈ H ∧ i ∈ col t then land t i
      else wGen W (missFit M t) (compRun W M v₀ H col land t i)

/-- **An untouched copy's trajectory is the single undamaged run** ([Inevitability] §6, Finding 3,
Stage C(i) — the definitional identity, stated explicitly). If copy `i₀` is never named at any
hit time, damage never reaches it, and its own coordinate of the composite run is exactly
`wRunFrom` from its own start. -/
theorem compRun_eq_wRunFrom_of_untouched (W : ℕ) (M : ℕ → Fin C → Bool)
    (v₀ : Fin P → WVec C W) (H : Finset ℕ) (col : ℕ → Finset (Fin P))
    (land : ℕ → Fin P → WVec C W) {i₀ : Fin P} (hi₀ : ∀ t ∈ H, i₀ ∉ col t)
    (t : ℕ) : compRun W M v₀ H col land t i₀ = wRunFrom W (missFit M) (v₀ i₀) t := by
  induction t with
  | zero => rfl
  | succ t ih =>
      have hnot : ¬ (t ∈ H ∧ i₀ ∈ col t) := fun ⟨htH, hti₀⟩ => hi₀ t htH hti₀
      change (if t ∈ H ∧ i₀ ∈ col t then land t i₀
        else wGen W (missFit M t) (compRun W M v₀ H col land t i₀)) = _
      rw [ite_eq_right hnot, ih]
      rfl

/-- **Every schedule touching fewer than `P` distinct copies leaves one untouched** — the
pigeonhole step behind Stage C(i). -/
theorem exists_untouched_copy (H : Finset ℕ) (col : ℕ → Finset (Fin P))
    (htouch : (H.biUnion col).card < P) : ∃ i₀ : Fin P, ∀ t ∈ H, i₀ ∉ col t := by
  have hpos : 0 < (Finset.univ \ H.biUnion col).card := by
    rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin]
    omega
  obtain ⟨i₀, hi₀⟩ := Finset.card_pos.mp hpos
  refine ⟨i₀, fun t ht hmem => ?_⟩
  exact (Finset.mem_sdiff.mp hi₀).2 (Finset.mem_biUnion.mpr ⟨t, ht, hmem⟩)

/-- **Per-step survival** ([Inevitability] §6, Proposition 6.1(iii)'s invariant-reading regime,
assembled from Stages A–C). From a base point whose generating rule is realizable in the guest's
class, at any budget of at least two quanta: for *any* damage schedule touching fewer than `P`
distinct copies in total, the composite's reading agrees with the base's own next state at every
step past the intact copy's settling time — for *any* arrival pattern within the touch bound,
since nothing above used one. -/
theorem compPredFrame_eq_next_of_touch_bound [NeZero C] [NeZero P] {hW : 2 ≤ W}
    (S : Fin n₁ → Fin n₁) (dec : Fin C → Fin n₁ → Fin n₁) (x₀ : Fin n₁)
    {c₀ : Fin C} (hc₀ : ∀ s, dec c₀ (S^[s] x₀) = S (S^[s] x₀))
    (v₀ : Fin P → WVec C W) (H : Finset ℕ)
    (col : ℕ → Finset (Fin P)) (land : ℕ → Fin P → WVec C W)
    (htouch : (H.biUnion col).card < P) :
    ∃ T : ℕ, ∀ t, T ≤ t →
      compPredFrame S dec (S^[t] x₀) (compRun W (predMiss S dec x₀) v₀ H col land t)
        = S (S^[t] x₀) := by
  obtain ⟨i₀, hi₀⟩ := exists_untouched_copy H col htouch
  have hR : ∀ s, predMiss S dec x₀ s c₀ = false := fun s => by simp [predMiss, hc₀ s]
  obtain ⟨T, hconst, hcons⟩ :=
    argmax_wRunFrom_eventually_const_consistent hW (predMiss S dec x₀) hR (v₀ i₀)
  refine ⟨T, fun t ht => ?_⟩
  have hcopy : compRun W (predMiss S dec x₀) v₀ H col land t i₀
      = wRunFrom W (missFit (predMiss S dec x₀)) (v₀ i₀) t :=
    compRun_eq_wRunFrom_of_untouched W (predMiss S dec x₀) v₀ H col land hi₀ t
  have hverify : dec (argmax (raw (compRun W (predMiss S dec x₀) v₀ H col land t i₀)))
      (S^[t] x₀) = S (S^[t] x₀) := by
    rw [hcopy, hconst t ht]
    simpa [predMiss] using hcons t ht
  exact compPredFrame_eq_of_mem_verifiers
    (Finset.mem_filter.mpr ⟨Finset.mem_univ i₀, hverify⟩)

/-- **The damaged and undamaged composites read the same** ([Inevitability] §6, assembling
survival against the plain construction): both equal the base's own next state, by the theorem
above applied once to the schedule and once to no schedule at all. -/
theorem compPredFrame_damaged_eq_undamaged_of_touch_bound [NeZero C] [NeZero P] {hW : 2 ≤ W}
    (S : Fin n₁ → Fin n₁) (dec : Fin C → Fin n₁ → Fin n₁) (x₀ : Fin n₁)
    {c₀ : Fin C} (hc₀ : ∀ s, dec c₀ (S^[s] x₀) = S (S^[s] x₀))
    (v₀ : Fin P → WVec C W) (H : Finset ℕ)
    (col : ℕ → Finset (Fin P)) (land : ℕ → Fin P → WVec C W)
    (htouch : (H.biUnion col).card < P) :
    ∃ T : ℕ, ∀ t, T ≤ t →
      compPredFrame S dec (S^[t] x₀) (compRun W (predMiss S dec x₀) v₀ H col land t)
        = compPredFrame S dec (S^[t] x₀)
            (compRun W (predMiss S dec x₀) v₀ ∅ (fun _ => ∅) (fun _ => v₀) t) := by
  have hP0 : 0 < P := by
    obtain ⟨i₀, -⟩ := exists_untouched_copy H col htouch
    exact i₀.pos
  obtain ⟨T, hT⟩ :=
    compPredFrame_eq_next_of_touch_bound (hW := hW) S dec x₀ hc₀ v₀ H col land htouch
  obtain ⟨T', hT'⟩ := compPredFrame_eq_next_of_touch_bound (hW := hW) S dec x₀ hc₀ v₀ ∅
    (fun _ => ∅) (fun _ => v₀) (by simpa using hP0)
  refine ⟨max T T', fun t ht => ?_⟩
  rw [hT t (le_trans (le_max_left _ _) ht), hT' t (le_trans (le_max_right _ _) ht)]

/-- **The budget instantiation** ([Inevitability] §6, Finding 4's closing move): on the realizable
branch the lifetime-free event count (`FlooredMixture.floorSurprise_card_mul_le`, `4(C-1)/θ`) is
the touch bound's own source. At `P` strictly above `c` times that count, any damage schedule
confined to the run's own surprise steps — at most `c` copies touched per surprise — meets the
touch hypothesis at every horizon, since the event count does not grow with it. The witness rate's
own currency (the noisy branch's `η`) is not instantiated here; it is the assembly row's remark,
not a further theorem, and nothing above needed it. -/
theorem compPredFrame_eq_next_of_realizable_budget [NeZero C] [NeZero P] {hW : 2 ≤ W} {b : ℕ}
    (S : Fin n₁ → Fin n₁) (dec : Fin C → Fin n₁ → Fin n₁) (x₀ : Fin n₁)
    {c₀ : Fin C} (hc₀ : ∀ s, dec c₀ (S^[s] x₀) = S (S^[s] x₀))
    (v₀ : Fin P → WVec C W) {θ : ℚ}
    (hbudget : 2 * ((C : ℚ) - 1) ≤ θ * 2 ^ b) (n : ℕ) {c : ℕ}
    (hP : (c : ℚ) * (4 * ((C : ℚ) - 1)) < (P : ℚ) * θ) (hθ0 : 0 < θ)
    (col : ℕ → Finset (Fin P))
    (hcol : ∀ t, (col t).card ≤ c) (land : ℕ → Fin P → WVec C W) :
    ∃ T : ℕ, ∀ t, T ≤ t →
      compPredFrame S dec (S^[t] x₀)
          (compRun W (predMiss S dec x₀) v₀
            (floorSurpriseSet (predMiss S dec x₀) b θ n) col land t)
        = S (S^[t] x₀) := by
  refine compPredFrame_eq_next_of_touch_bound (hW := hW) S dec x₀ hc₀ v₀
    (floorSurpriseSet (predMiss S dec x₀) b θ n) col land ?_
  have hR : ∀ s, predMiss S dec x₀ s c₀ = false := fun s => by simp [predMiss, hc₀ s]
  have hcardH : ((floorSurpriseSet (predMiss S dec x₀) b θ n).card : ℚ) * θ
      ≤ 4 * ((C : ℚ) - 1) := floorSurprise_card_mul_le (predMiss S dec x₀) hR b θ hbudget n
  have hunion : ((floorSurpriseSet (predMiss S dec x₀) b θ n).biUnion col).card
      ≤ (floorSurpriseSet (predMiss S dec x₀) b θ n).card * c :=
    le_trans Finset.card_biUnion_le
      (le_trans (Finset.sum_le_sum fun t _ => hcol t) (by rw [Finset.sum_const, smul_eq_mul]))
  have hQ : (((floorSurpriseSet (predMiss S dec x₀) b θ n).card * c : ℕ) : ℚ)
      < (P : ℚ) := by
    push_cast
    nlinarith [hcardH, hP, hθ0]
  exact lt_of_le_of_lt hunion (by exact_mod_cast hQ)

/-! ### The touch bound's other side: a schedule that touches every copy -/

/-- **The synchronizing miss matrix**: candidate `0` misses at steps `3`, `4` and `5` and nowhere
else; candidate `1` never misses. -/
def syncMiss : ℕ → Fin 2 → Bool := fun t i => decide (i = 0 ∧ (t = 3 ∨ t = 4 ∨ t = 5))

/-- **The synchronizing schedule**: copy `0` is hit at step `0` and copy `1` at step `1`. -/
def syncCol : ℕ → Finset (Fin 2) := fun t => if t = 0 then {0} else {1}

/-- **The installed vector**: candidate `0` at the cap `4`, candidate `1` at the floor. -/
def syncLand : ℕ → Fin 2 → WVec 2 4 := fun _ _ => ![4, 1]

/-- **Guard: a copy's recovery does not rescue a fixed population against a rate**
([Inevitability] Theorem 6.6(v), the touch bound's other side — IN-25). Two copies from the
uniform start, hit one per step with the same wrong leader installed, on a stream where that
leader then misses three steps running: at each of those steps every copy's heaviest candidate is
the one that misses, so no copy verifies and the composite reads wrong; at the step after, every
copy's heaviest candidate is the truth again — the recovery is real and buys nothing against
synchronization, since the copies were made to fail together. The burst is three steps, one more
than the budget's two doublings, because `argmax` keeps the incumbent at a tie. -/
theorem compRun_synchronized_guard :
    (∀ t, (t = 3 ∨ t = 4 ∨ t = 5) → ∀ i : Fin 2,
        syncMiss t
          (argmax (raw (compRun 4 syncMiss (fun _ _ => 1) {0, 1} syncCol syncLand t i))) = true) ∧
      ∀ i : Fin 2,
        argmax (raw (compRun 4 syncMiss (fun _ _ => 1) {0, 1} syncCol syncLand 6 i)) = 1 := by
  refine ⟨fun t ht i => ?_, fun i => ?_⟩
  · rcases ht with rfl | rfl | rfl <;> fin_cases i <;> decide
  · fin_cases i <;> decide

end Survival

end WeightedFiber

/-- info: 'WeightedFiber.dSurpriseSet_card_mul_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms WeightedFiber.dSurpriseSet_card_mul_le

/-- info: 'WeightedFiber.compPredFrame_eq_next_of_realizable_budget' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms WeightedFiber.compPredFrame_eq_next_of_realizable_budget

/-- info: 'WeightedFiber.dSurpriseSet_reseed_eq_range' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms WeightedFiber.dSurpriseSet_reseed_eq_range

/-- info: 'WeightedFiber.floorSurpriseSetFrom_reseed_card_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms WeightedFiber.floorSurpriseSetFrom_reseed_card_le

/-- info: 'WeightedFiber.KE_compFrameFlat_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms WeightedFiber.KE_compFrameFlat_le

/-- info: 'WeightedFiber.compRun_synchronized_guard' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms WeightedFiber.compRun_synchronized_guard
