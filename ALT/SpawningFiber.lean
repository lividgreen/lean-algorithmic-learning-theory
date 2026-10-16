module

public import ALT.RedundantFiber
public import ALT.GrowingWorld


/-!
# The spawning fiber: a growing population outlasts every rate below one
  ([Inevitability] §6, [Guests] §7)

`RedundantFiber.lean` proves survival by absorption for a *fixed* population of `P` copies: a hit
schedule touching fewer than `P` copies in total leaves one untouched, and that copy carries the
composite's reading. Against a constant rate of hits a fixed population is eventually exhausted
(`compRun_synchronized_guard` is the touch bound's other side). This file states the growing
answer: a population that **spawns one copy of the weighted fiber every step**, every copy starting
at the same vector and reading the base's own stream from its own spawn step on.

## Main results

* `spawnRun` — the damaged spawning population: copies indexed by `ℕ`, copy `j` active from step
  `j`, hits overriding named copies exactly as `compRun` does.
* `spawnRun_eq_wRunFrom_of_untouched` — an untouched copy is the undamaged run from its start on
  the stream from its own spawn step.
* `spawnPredFrame_eq_next_of_rate` — **the headline**: at a budget of at least two quanta, from a
  base point whose rule is realizable, if the number of copies touched before step `t` is at most
  `(a t + c) / b` with `a < b`, the composite's reading over the `t + 1` active copies equals the
  base's next state from some step on — with no settling hypothesis, since one settling time
  serves every spawned copy (the base is finite).
* `spawnPredFrame_eq_next_of_rate_nonvacuous` — the hypotheses hold together, with hits, at a
  pinned instance.
* `spawnPredFrame_rate_one_guard` — `a < b` is load-bearing: at rate one (every active copy hit at
  every step) the composite reads wrong at every step.
* `spawnUpdate`, `advances_spawnUpdate`, `spawnUpdate_iterate` — the undamaged population as a
  growing world in [Guests] §7 Definition 7.1's sense: the state is the base point together with
  the list of copies, and the update appends a fresh copy while every old copy takes one weighted
  step.
-/

@[expose] public section

namespace ALT

open WVec

section Spawn

variable {n₁ C : ℕ} {W : ℕ}

/-- **The damaged spawning population** ([Inevitability] §6, [Guests] §7): copies are indexed by
`ℕ`, copy `j` becomes active at step `j` (before that it sits at the start vector `u`), and from
then on takes the ordinary weighted-fiber generation under the fitness stream `missFit M`, except
that at step `t` the copies named by `col t` are overridden by `land t`. -/
def spawnRun (W : ℕ) (M : ℕ → Fin C → Bool) (u : WVec C W) (col : ℕ → Finset ℕ)
    (land : ℕ → ℕ → WVec C W) : ℕ → ℕ → WVec C W
  | 0 => fun _ => u
  | t + 1 => fun j =>
      if j ≤ t then
        (if j ∈ col t then land t j else wGen W (missFit M t) (spawnRun W M u col land t j))
      else u

/-- **The composite reading of the spawning population** ([Inevitability] §6): the verifying-copy
decode (`compPredFrame`) over the `t + 1` copies active at step `t`, against the base's state
`S^[t] x₀`, with the fitness stream the base's own trajectory drives (`predMiss`). -/
def spawnPredFrame [NeZero C] (S : Fin n₁ → Fin n₁) (dec : Fin C → Fin n₁ → Fin n₁)
    (x₀ : Fin n₁) (W : ℕ) (u : WVec C W) (col : ℕ → Finset ℕ) (land : ℕ → ℕ → WVec C W)
    (t : ℕ) : Fin n₁ :=
  compPredFrame S dec (S^[t] x₀)
    (fun i : Fin (t + 1) => spawnRun W (predMiss S dec x₀) u col land t i)

/-- **An untouched copy is the undamaged run from its own spawn step** ([Inevitability] §6): if
copy `j` is active at step `t` and named by no hit before `t`, its coordinate is `wRunFrom` from
the start vector on the stream shifted to begin at step `j`. -/
theorem spawnRun_eq_wRunFrom_of_untouched (W : ℕ) (M : ℕ → Fin C → Bool) (u : WVec C W)
    (col : ℕ → Finset ℕ) (land : ℕ → ℕ → WVec C W) {j t : ℕ} (hjt : j ≤ t)
    (hun : ∀ s, j ≤ s → s < t → j ∉ col s) :
    spawnRun W M u col land t j = wRunFrom W (fun k => missFit M (j + k)) u (t - j) := by
  obtain ⟨d, rfl⟩ : ∃ d, t = j + d := ⟨t - j, by omega⟩
  rw [Nat.add_sub_cancel_left]
  clear hjt
  induction d with
  | zero =>
      cases j with
      | zero => rfl
      | succ j => simp [spawnRun, wRunFrom]
  | succ d ih =>
      have hnot : j ∉ col (j + d) := hun (j + d) (by omega) (by omega)
      have ih' := ih (fun s hs hs' => hun s hs (by omega))
      rw [show j + (d + 1) = (j + d) + 1 from rfl]
      change (if j ≤ j + d then (if j ∈ col (j + d) then land (j + d) j
        else wGen W (missFit M (j + d)) (spawnRun W M u col land (j + d) j)) else u) = _
      have hle : j ≤ j + d := Nat.le_add_right j d
      simp only [hle, hnot, ↓reduceIte, ih']
      rfl

/-- The stream a copy spawned at step `j` sees is the stream of the base restarted at `S^[j] x₀`. -/
private theorem missFit_predMiss_shift (S : Fin n₁ → Fin n₁) (dec : Fin C → Fin n₁ → Fin n₁)
    (x₀ : Fin n₁) (j : ℕ) :
    (fun k => missFit (predMiss S dec x₀) (j + k)) = missFit (predMiss S dec (S^[j] x₀)) := by
  funext k c
  have h : S^[j + k] x₀ = S^[k] (S^[j] x₀) := by
    rw [add_comm j k, Function.iterate_add_apply]
  simp only [missFit, predMiss, h]
  congr

/-- **One settling time serves every spawned copy**: at every base point of the finite carrier,
either the rule is not realizable (nothing owed) or the settled leader of the run from `u` is
consistent with the base from some step on. -/
private theorem exists_settle_all [NeZero C] (hW : 2 ≤ W) (S : Fin n₁ → Fin n₁)
    (dec : Fin C → Fin n₁ → Fin n₁) {c₀ : Fin C} (u : WVec C W) :
    ∃ T₀ : ℕ, ∀ y : Fin n₁, (∀ s, dec c₀ (S^[s] y) = S (S^[s] y)) →
      ∀ k, T₀ ≤ k → dec (argmax (raw (wRunFrom W (missFit (predMiss S dec y)) u k))) (S^[k] y)
        = S (S^[k] y) := by
  have hone : ∀ y : Fin n₁, ∃ T : ℕ, (∀ s, dec c₀ (S^[s] y) = S (S^[s] y)) →
      ∀ k, T ≤ k → dec (argmax (raw (wRunFrom W (missFit (predMiss S dec y)) u k))) (S^[k] y)
        = S (S^[k] y) := by
    intro y
    by_cases hy : ∀ s, dec c₀ (S^[s] y) = S (S^[s] y)
    · have hR : ∀ s, predMiss S dec y s c₀ = false := fun s => by simp [predMiss, hy s]
      obtain ⟨T, hconst, hcons⟩ :=
        argmax_wRunFrom_eventually_const_consistent hW (predMiss S dec y) hR u
      refine ⟨T, fun _ k hk => ?_⟩
      rw [hconst k hk]
      simpa [predMiss] using hcons k hk
    · exact ⟨0, fun h => absurd h hy⟩
  choose T hT using hone
  refine ⟨Finset.univ.sup T, fun y hy k hk => hT y hy k ?_⟩
  exact le_trans (Finset.le_sup (Finset.mem_univ y)) hk

/-- **The spawning fiber outlasts every rate below one** ([Inevitability] §6, Theorem 6.6(v) with
a growing population; [Guests] §7): at a budget of at least two quanta, from a base point whose
rule is realizable by a candidate `c₀`, if the number of distinct copies touched before step `t`
is at most `(a t + c) / b` for some `a < b` — any arrival pattern within that rate, hits landing
arbitrary vectors — then from some step on the composite's reading over the `t + 1` active copies
equals the base's next state. No settling hypothesis is assumed: the base carrier is finite, so a
single settling time serves every copy spawned. The rate bound is not slack (`a < b` fails at rate
one: `spawnPredFrame_rate_one_guard`). -/
theorem spawnPredFrame_eq_next_of_rate [NeZero C] (hW : 2 ≤ W)
    (S : Fin n₁ → Fin n₁) (dec : Fin C → Fin n₁ → Fin n₁) (x₀ : Fin n₁)
    {c₀ : Fin C} (hc₀ : ∀ s, dec c₀ (S^[s] x₀) = S (S^[s] x₀))
    (u : WVec C W) (col : ℕ → Finset ℕ) (land : ℕ → ℕ → WVec C W)
    {a b c : ℕ} (hab : a < b)
    (hrate : ∀ t, b * ((Finset.range t).biUnion col).card ≤ a * t + c) :
    ∃ T, ∀ t, T ≤ t → spawnPredFrame S dec x₀ W u col land t = S (S^[t] x₀) := by
  obtain ⟨T₀, hT₀⟩ := exists_settle_all (c₀ := c₀) hW S dec u
  have hb : 0 < b := by omega
  refine ⟨c + b * T₀, fun t ht => ?_⟩
  have hT₀t : T₀ ≤ t := le_trans (Nat.le_mul_of_pos_left T₀ hb) (le_trans (Nat.le_add_left _ _) ht)
  -- a never-touched copy among the first `t - T₀ + 1`
  have hcard : ((Finset.range t).biUnion col).card < t - T₀ + 1 := by
    have h1 := hrate t
    have h2 : b * ((Finset.range t).biUnion col).card < b * (t - T₀ + 1) := by
      have h3 : (b - a) * t ≥ t := Nat.le_mul_of_pos_left t (by omega)
      have h4 : b * t = a * t + (b - a) * t := by
        rw [← Nat.add_mul]; congr 1; omega
      have h5 : b * (t - T₀ + 1) = b * t - b * T₀ + b := by
        have : b * (t - T₀) = b * t - b * T₀ := Nat.mul_sub b t T₀
        rw [Nat.mul_add, this, Nat.mul_one]
      have h6 : b * T₀ ≤ b * t := Nat.mul_le_mul_left b hT₀t
      omega
    exact lt_of_mul_lt_mul_left h2 (Nat.zero_le b)
  obtain ⟨j, hjr, hjH⟩ : ∃ j ∈ Finset.range (t - T₀ + 1), j ∉ (Finset.range t).biUnion col := by
    by_contra hcon
    push Not at hcon
    have := Finset.card_le_card (fun j hj => hcon j hj)
    simp at this
    omega
  have hjle : j ≤ t - T₀ := by simpa [Nat.lt_succ_iff] using hjr
  have hun : ∀ s, j ≤ s → s < t → j ∉ col s := fun s _ hs hmem =>
    hjH (Finset.mem_biUnion.mpr ⟨s, Finset.mem_range.mpr hs, hmem⟩)
  have hjt : j ≤ t := by omega
  have hcopy := spawnRun_eq_wRunFrom_of_untouched W (predMiss S dec x₀) u col land hjt hun
  rw [missFit_predMiss_shift] at hcopy
  have hreal : ∀ s, dec c₀ (S^[s] (S^[j] x₀)) = S (S^[s] (S^[j] x₀)) := fun s => by
    have := hc₀ (s + j)
    rwa [Function.iterate_add_apply] at this
  have hv := hT₀ (S^[j] x₀) hreal (t - j) (by omega)
  have hiter : S^[t - j] (S^[j] x₀) = S^[t] x₀ := by
    rw [← Function.iterate_add_apply, Nat.sub_add_cancel hjt]
  rw [hiter] at hv
  unfold spawnPredFrame
  refine compPredFrame_eq_of_mem_verifiers (i := ⟨j, by omega⟩) ?_
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
  change dec (argmax (raw (spawnRun W (predMiss S dec x₀) u col land t j))) (S^[t] x₀) = _
  rw [hcopy]
  exact hv

/-! ### The joint-satisfiability witness and the rate-one guard -/

/-- The base's step on two states, `x ↦ x + 1` (a two-cycle): the pinned instance's base. -/
def spawnS : Fin 2 → Fin 2 := fun x => x + 1

/-- The pinned instance's decoder: candidate `0` reads the current state back (always wrong about
the next one), candidate `1` is the base's own step (always right). -/
def spawnDec : Fin 2 → Fin 2 → Fin 2 := fun c => if c = 0 then id else spawnS

/-- The pinned instance's start vector: both candidates at one quantum, at the budget `W = 2`. -/
def spawnStart : WVec 2 2 := pack 2 (fun _ => 1)

/-- The pinned instance's installed vector: candidate `0` (the wrong one) at the cap. -/
def spawnLand : ℕ → ℕ → WVec 2 2 := fun _ _ => ![2, 1]

/-- **A rate-one-half schedule**: at every even step `t`, copy `t / 2` is hit; at odd steps
nothing is. At most `(t + 1) / 2` copies are touched before step `t`. -/
def spawnColHalf : ℕ → Finset ℕ := fun t => if t % 2 = 0 then {t / 2} else ∅

/-- **The rate-one schedule**: at step `t` every active copy (`0, …, t`) is hit. -/
def spawnColAll : ℕ → Finset ℕ := fun t => Finset.range (t + 1)

private theorem spawnS_ne (x : Fin 2) : spawnS x ≠ x := by
  revert x; decide

/-- The pinned instance's candidate `1` is always right. -/
private theorem spawnDec_one (x : Fin 2) : spawnDec 1 x = spawnS x := rfl

private theorem card_biUnion_spawnColHalf_le (t : ℕ) :
    2 * ((Finset.range t).biUnion spawnColHalf).card ≤ 1 * t + 1 := by
  have hsub : (Finset.range t).biUnion spawnColHalf ⊆ Finset.range ((t + 1) / 2) := by
    intro x hx
    obtain ⟨s, hs, hxs⟩ := Finset.mem_biUnion.mp hx
    rw [Finset.mem_range] at hs ⊢
    by_cases h : s % 2 = 0
    · simp only [spawnColHalf, h, ↓reduceIte, Finset.mem_singleton] at hxs
      omega
    · simp [spawnColHalf, h] at hxs
  have := Finset.card_le_card hsub
  rw [Finset.card_range] at this
  omega

/-- **The hypotheses of `spawnPredFrame_eq_next_of_rate` hold together, with hits**: at the pinned
instance — the two-cycle `spawnS` on `Fin 2`, two candidates decoded by `spawnDec` with `1` always
right, budget `2`, start `spawnStart`, the schedule `spawnColHalf` landing `spawnLand` — the budget,
the realizing candidate, `a = 1 < b = 2` and the rate bound with `c = 1` all hold, hits do occur,
and the theorem's conclusion follows. -/
theorem spawnPredFrame_eq_next_of_rate_nonvacuous :
    2 ≤ (2 : ℕ) ∧ (∀ s, spawnDec 1 (spawnS^[s] 0) = spawnS (spawnS^[s] 0)) ∧ (1 : ℕ) < 2 ∧
      (∀ t, 2 * ((Finset.range t).biUnion spawnColHalf).card ≤ 1 * t + 1) ∧
      (∃ t, spawnColHalf t ≠ ∅) ∧
      ∃ T, ∀ t, T ≤ t →
        spawnPredFrame spawnS spawnDec 0 2 spawnStart spawnColHalf spawnLand t
          = spawnS (spawnS^[t] 0) := by
  have hc₀ : ∀ s, spawnDec 1 (spawnS^[s] 0) = spawnS (spawnS^[s] 0) := fun s => spawnDec_one _
  refine ⟨le_rfl, hc₀, by norm_num, card_biUnion_spawnColHalf_le, ⟨0, ?_⟩,
    spawnPredFrame_eq_next_of_rate (le_refl 2) spawnS spawnDec 0 hc₀ spawnStart spawnColHalf
      spawnLand (a := 1) (b := 2) (c := 1) (by norm_num) card_biUnion_spawnColHalf_le⟩
  simp [spawnColHalf]

private theorem argmax_spawnStart : argmax (raw spawnStart) = 0 := by decide

private theorem argmax_spawnLandVec : argmax (raw (![2, 1] : WVec 2 2)) = 0 := by decide

private theorem argmax_spawnLand (t j : ℕ) : argmax (raw (spawnLand t j)) = 0 :=
  argmax_spawnLandVec

private theorem argmax_spawnRun_all (t j : ℕ) :
    argmax (raw (spawnRun 2 (predMiss spawnS spawnDec 0) spawnStart spawnColAll spawnLand t j))
      = 0 := by
  cases t with
  | zero => exact argmax_spawnStart
  | succ t =>
      change argmax (raw (if j ≤ t then (if j ∈ spawnColAll t then spawnLand t j
        else wGen 2 (missFit (predMiss spawnS spawnDec 0) t)
          (spawnRun 2 (predMiss spawnS spawnDec 0) spawnStart spawnColAll spawnLand t j))
        else spawnStart)) = 0
      by_cases hj : j ≤ t
      · have hmem : j ∈ spawnColAll t := Finset.mem_range.mpr (by omega)
        simp only [hj, hmem, ↓reduceIte]
        exact argmax_spawnLand t j
      · simp only [hj, ↓reduceIte]
        exact argmax_spawnStart

/-- **Guard: `a < b` is load-bearing** ([Inevitability] §6, Theorem 6.6(v) with a growing
population). At the pinned instance of `spawnPredFrame_eq_next_of_rate_nonvacuous` but for the
schedule `spawnColAll`, which hits every active copy at every step: the touched set before step `t`
has exactly `t` elements, so the rate bound holds at `a = b = 1`, `c = 0` and fails only the
strictness `a < b`; the budget and realizing candidate hold as before, and the composite reads
wrong at every step. The old copies are all landed on the wrong candidate, the newborn copy's tied
start reads candidate `0`, so no copy verifies and the fallback reads wrong. -/
theorem spawnPredFrame_rate_one_guard :
    2 ≤ (2 : ℕ) ∧ (∀ s, spawnDec 1 (spawnS^[s] 0) = spawnS (spawnS^[s] 0)) ∧
      (∀ t, ((Finset.range t).biUnion spawnColAll).card = t) ∧
      (∀ t, 1 * ((Finset.range t).biUnion spawnColAll).card ≤ 1 * t + 0) ∧
      ∀ t, spawnPredFrame spawnS spawnDec 0 2 spawnStart spawnColAll spawnLand t
        ≠ spawnS (spawnS^[t] 0) := by
  have hU : ∀ t, (Finset.range t).biUnion spawnColAll = Finset.range t := by
    intro t
    ext x
    simp only [Finset.mem_biUnion, Finset.mem_range, spawnColAll]
    constructor
    · rintro ⟨s, hs, hx⟩
      omega
    · intro hx
      exact ⟨x, hx, by omega⟩
  have hcard : ∀ t, ((Finset.range t).biUnion spawnColAll).card = t := fun t => by
    rw [hU t, Finset.card_range]
  refine ⟨le_rfl, fun s => spawnDec_one _, hcard, fun t => by rw [hcard t]; omega, fun t => ?_⟩
  have hread : spawnPredFrame spawnS spawnDec 0 2 spawnStart spawnColAll spawnLand t
      = spawnS^[t] 0 := by
    unfold spawnPredFrame compPredFrame
    split_ifs with h
    · simp [spawnDec, argmax_spawnRun_all]
    · simp [spawnDec, argmax_spawnRun_all]
  rw [hread]
  exact (spawnS_ne _).symm

end Spawn

/-! ## The growing world -/

section World

variable {n₁ C : ℕ}

private theorem fit_eq_missFit (S : Fin n₁ → Fin n₁) (dec : Fin C → Fin n₁ → Fin n₁)
    (x₀ : Fin n₁) (t : ℕ) :
    (fun c => if dec c (S^[t] x₀) ≠ S (S^[t] x₀) then 1 else 2)
      = missFit (predMiss S dec x₀) t := by
  funext c
  simp [missFit, predMiss]

private theorem spawnRun_succ_undamaged (W : ℕ) (M : ℕ → Fin C → Bool) (u : WVec C W) {t j : ℕ}
    (hj : j ≤ t) :
    spawnRun W M u (fun _ => ∅) (fun _ _ => u) (t + 1) j
      = wGen W (missFit M t) (spawnRun W M u (fun _ => ∅) (fun _ _ => u) t j) := by
  simp [spawnRun, hj]

/-- **The spawning population as a growing world** ([Guests] §7, Definition 7.1): the state is
the base point together with the list of copies; one update steps the base, gives every old copy
one weighted-fiber generation under the fitness the base's current step dictates (`1` for a
candidate whose decoded rule mispredicts, `2` otherwise), and appends a fresh copy at `u`. -/
def spawnUpdate (S : Fin n₁ → Fin n₁) (dec : Fin C → Fin n₁ → Fin n₁) (W : ℕ) (u : WVec C W) :
    Fin n₁ × List (WVec C W) → Fin n₁ × List (WVec C W) :=
  fun p => (S p.1, p.2.map (wGen W (fun c => if dec c p.1 ≠ S p.1 then 1 else 2)) ++ [u])

/-- **The spawning update advances the stage** ([Guests] §7, Definition 7.1): the states whose
population has `t + 1` copies are carried into those with `t + 2`. -/
theorem advances_spawnUpdate (S : Fin n₁ → Fin n₁) (dec : Fin C → Fin n₁ → Fin n₁) (W : ℕ)
    (u : WVec C W) :
    Nonautonomous.PositivelyInvariant (spawnUpdate S dec W u)
      (fun t => {p | p.2.length = t + 1}) := by
  intro t p hp
  simp only [Set.mem_ofPred_eq] at hp ⊢
  simp [spawnUpdate, hp]

/-- **The undamaged population is the growing world's orbit** ([Guests] §7, Definition 7.1):
iterating `spawnUpdate` `t` times from the base point `x₀` with one copy at `u` gives the base's
`t`-th state and the undamaged `spawnRun` population, listed by copy index. -/
theorem spawnUpdate_iterate (S : Fin n₁ → Fin n₁) (dec : Fin C → Fin n₁ → Fin n₁) (W : ℕ)
    (u : WVec C W) (x₀ : Fin n₁) (t : ℕ) :
    (spawnUpdate S dec W u)^[t] (x₀, [u])
      = (S^[t] x₀, List.ofFn (fun i : Fin (t + 1) =>
          spawnRun W (predMiss S dec x₀) u (fun _ => ∅) (fun _ _ => u) t i)) := by
  induction t with
  | zero => simp [spawnRun]
  | succ t ih =>
      rw [Function.iterate_succ_apply', ih]
      simp only [spawnUpdate, Prod.mk.injEq]
      refine ⟨(Function.iterate_succ_apply' S t x₀).symm, ?_⟩
      conv_rhs => rw [List.ofFn_succ']
      simp only [List.concat_eq_append, List.map_ofFn]
      congr 1
      · congr 1
        funext i
        have hi : (i.castSucc : ℕ) ≤ t := Nat.lt_succ_iff.mp i.isLt
        rw [spawnRun_succ_undamaged _ _ _ hi, ← fit_eq_missFit]
        rfl
      · simp [spawnRun]

end World

end ALT

set_option linter.style.longLine false in
/-- info: 'ALT.spawnPredFrame_eq_next_of_rate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.spawnPredFrame_eq_next_of_rate

set_option linter.style.longLine false in
/-- info: 'ALT.spawnPredFrame_eq_next_of_rate_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.spawnPredFrame_eq_next_of_rate_nonvacuous

set_option linter.style.longLine false in
/-- info: 'ALT.spawnPredFrame_rate_one_guard' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.spawnPredFrame_rate_one_guard
