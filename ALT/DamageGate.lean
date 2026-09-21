/-
Copyright (c) 2026 Mykola Palamarchuk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mykola Palamarchuk
-/
module

public import ALT.RedundantFiber
public import ALT.WitnessMixture

-- Formal-check file, not Mathlib-destined: opt out of the house-style header linter.
set_option linter.style.header false

/-!
# A noise-gated damage schedule, and the absorption it buys ([Inevitability] §6, IN-25)

Proposition 6.1's damage model (D1) says the guest's code is perturbed only where its predictor is
`ε`-surprised. Read literally on this construction, that condition names the *damaged* run's own
surprise set, and `RedundantFiber.lean` records why that reading fails to be a budget at all — a
schedule can land on every one of its own surprises, at every length. This file states a different,
weaker gate: one on the substrate's own noise stream directly, with no run, no weight vector and no
schedule anywhere in its statement, so it names the same set of times before and after any damage.
That is `NoiseGated`, and `noiseGated_iff_witMiss` is the reason it is worth a name at all — it is
exactly the noisy witness's own miss condition (`WitnessMixture.witMiss_zero`), read as a schedule
constraint rather than a run property.

A schedule confined to a noise-gated set inherits `WitnessMixture.noiseCount`'s own bound
(`noiseGated_card_le`), and confining a `P`-fold carrier's damage that way is enough to guarantee an
untouched copy, by the same pigeonhole step `RedundantFiber.lean` already proves
(`exists_untouched_copy_of_noiseGated`). The same route closes Theorem 6.6(v)'s own conclusion
directly (`compPredFrame_eq_next_of_noiseGated`), reusing `RedundantFiber.lean`'s touch-bound
argument rather than duplicating it.

Between the noise-free branch and one merely bounded per horizon sits a third class: a stream that
fires at most `m` times in total (`QuietFrom`). Its noise count is capped by the same `m` at *every*
horizon at once (`noiseCount_le_of_quietFrom`), so a single redundancy condition — not one per
horizon — already buys the composite's survival there (`exists_untouched_copy_of_quietFrom`,
`compPredFrame_eq_next_of_quietFrom`): a lifetime statement on a branch strictly between the two
Theorem 6.6(iii) names ([Inevitability] §6, Theorem 6.6(v″)). `quietStream` packages a designed
instance of this class, and `sourceStep`/`sourceOut` package a counter automaton emitting it, so
the class is witnessed rather than merely named.

## Main results

* `NoiseGated` — a hit schedule is gated when every one of its times sits on a fired noise bit.
* `noiseGated_iff_witMiss` — the gate **is** the noisy witness's own true-candidate miss condition.
* `noiseGated_card_le` — a gated schedule inside a horizon is no larger than the noise count there.
* `exists_untouched_copy_of_noiseGated` — a `P`-fold carrier survives a gated schedule whenever the
  redundancy exceeds the per-event copy cost times the noise count.
* `compPredFrame_eq_next_of_noiseGated` — the composite reads the base's own next state under a
  gated schedule of that redundancy, the same conclusion the realizable branch reaches, reached
  from the gate instead.
* `noiseGated_eq_empty_of_quiet` — **the boundary.** On a noise-free stream the only gated schedule
  is the empty one: a noise-gated host does no damage at all there, and a noise-free stream is
  exactly the branch whose surprise count is the lifetime-free anchor `4(C−1)/θ`.
* `QuietFrom` — a stream that has fired at most `m` times in total, at the same offset `NoiseGated`
  reads at.
* `noiseCount_le_of_quietFrom` — under `QuietFrom`, the noise count is capped by `m` at every
  horizon at once.
* `exists_untouched_copy_of_quietFrom`, `compPredFrame_eq_next_of_quietFrom` — the uniformization:
  one redundancy condition, `c · m < P`, serves every horizon's conclusion, a lifetime statement
  rather than the honestly per-horizon one `compPredFrame_eq_next_of_noiseGated` supplies on its
  own.
* `quietStream` — the designed eventually-quiet stream at parameters `k, m`, firing on exactly
  `[k, k + m)`.
* `quietFrom_quietStream`, `witMiss_quietStream_zero_iff`, `noiseGated_quietStream_iff` — its basic
  identities: it is eventually-quiet at its own `m`, its designated candidate's misses are exactly
  its designed window, and its gate is exactly confinement to that window.
* `witMiss_quietStream_zero_of_pos`, `finite_setOf_witMiss_quietStream` — the two boundary facts
  placing `quietStream` strictly between Theorem 6.6(iii)'s two branches: it misses immediately at
  `0 < m` (not the noise-free branch), yet its total miss set is finite (not the branch that never
  settles).
* `sourceStep`, `sourceOut` — a saturating counter automaton on `Fin (k + m + 1)` and its output.
* `val_iterate_sourceStep`, `sourceOut_iterate_sourceStep_zero` — the counter's closed form, and the
  fact that reading it from `0` emits `quietStream` exactly.
* `sourceStep_iterate_eq_last`, `sourceStep_last` — the counter saturates within `k + m` steps from
  any start, and its top is a fixed point.
* `sourceStep_not_injective` — at `1 ≤ m` the step map is not injective: the host's own
  non-invertibility, confined to the source and claimed of nothing downstream.

## Scope

None of this moves Theorem 6.6's own hypothesis. The theorem still names (D1)/(D2) as stated, and
whether a host's damage in fact takes the noise-gated shape is not a question this file answers —
it is a further, and strictly narrower, reading than the paper's own. What this file supplies is a
gate stated on the noise stream itself, its count, and the precise sense in which it is weaker than
what (D1) buys: `noiseGated_eq_empty_of_quiet` shows the gate has no content on the very branch the
lifetime-free bound covers, so this is a variant repair, not a strengthening, of Theorem 6.6(v).
`compPredFrame_eq_next_of_noiseGated` inherits that same boundary: it is a parallel route to the
theorem's own conclusion, honestly per-horizon rather than lifetime-free, not a replacement for the
realizable branch's.

The eventually-quiet material carries the identical boundary, one level up: `QuietFrom` is stated
on the stream alone, still names nothing about a run or a schedule, and its uniformization is a
reading of `exists_untouched_copy_of_noiseGated`/`compPredFrame_eq_next_of_noiseGated`, not a new
argument. What it does not supply is the composition this file's own uniform bound and a designed
instance's own realizability are stitched together into a single per-horizon-free survival
statement over an *arbitrary* eventually-quiet stream and an *arbitrary* gated schedule on it —
that composition, and the instantiation of `quietStream`/`sourceStep` at this construction's own
substrate, stay paper-level, exactly the sense in which (v″) names its own remaining seam.
-/


@[expose] public section

namespace DamageGate

open WitnessMixture WeightedFiber

/-! ## The gate -/

/-- **A noise-gated hit schedule.** Every time in `H` sits on a fired noise bit, `k` steps ahead of
itself — the same offset the noisy window witness's own miss condition reads at. Nothing here
mentions a run, a weight vector or a schedule's landings, so the same set `H` is gated or not before
and after any damage a host applies. -/
def NoiseGated (k : ℕ) (ξ : ℕ → Bool) (H : Finset ℕ) : Prop := ∀ s ∈ H, ξ (s + k) = true

/-- **The gate is the witness's own miss condition** ([Inevitability] §6, IN-25). `witMiss_zero`
says the true candidate's miss at `s` *is* the noise bit at `s + k`, so `NoiseGated` is exactly the
schedule confined to that candidate's own misses — the point of naming it: a set defined this way
is the same set whether read before or after damage, where the damaged run's own surprise set is
not. -/
theorem noiseGated_iff_witMiss {k : ℕ} [NeZero k] (ξ : ℕ → Bool) (H : Finset ℕ) :
    NoiseGated k ξ H ↔ ∀ s ∈ H, witMiss k ξ s 0 = true := by
  unfold NoiseGated
  simp only [witMiss_zero]

/-- **A gated schedule is no larger than the noise count.** Every element of `H` inside the horizon
`n` is a fired noise bit there, so `H` embeds into the noise-count set directly. -/
theorem noiseGated_card_le {k : ℕ} (ξ : ℕ → Bool) {H : Finset ℕ} {n : ℕ}
    (hH : H ⊆ Finset.range n) (hgate : NoiseGated k ξ H) : H.card ≤ noiseCount ξ k n := by
  rw [noiseCount]
  refine Finset.card_le_card fun s hs => ?_
  rw [Finset.mem_filter]
  exact ⟨hH hs, hgate s hs⟩

/-! ## The absorption bound, and its boundary -/

/-- **A `P`-fold carrier survives a noise-gated schedule of bounded per-event reach**
([Inevitability] §6, IN-25 — the gate's own absorption bound). At most `c` copies touched per hit,
confined to a noise-gated schedule inside the horizon `n`: once `P` exceeds `c` times the noise
count there, the union of touched copies is too small to cover every slot, and some copy is never
touched. Routed through `RedundantFiber.exists_untouched_copy` via `noiseGated_card_le`, the same
pigeonhole step Stage C already proves. -/
theorem exists_untouched_copy_of_noiseGated {P : ℕ} [NeZero P] {k n c : ℕ} (ξ : ℕ → Bool)
    {H : Finset ℕ} (hH : H ⊆ Finset.range n) (hgate : NoiseGated k ξ H)
    (col : ℕ → Finset (Fin P)) (hcol : ∀ t, (col t).card ≤ c)
    (hP : c * noiseCount ξ k n < P) :
    ∃ i₀ : Fin P, ∀ t ∈ H, i₀ ∉ col t := by
  refine WeightedFiber.exists_untouched_copy H col ?_
  have hunion : (H.biUnion col).card ≤ H.card * c :=
    le_trans Finset.card_biUnion_le
      (le_trans (Finset.sum_le_sum fun t _ => hcol t) (by rw [Finset.sum_const, smul_eq_mul]))
  have hHc : H.card ≤ noiseCount ξ k n := noiseGated_card_le ξ hH hgate
  calc (H.biUnion col).card ≤ H.card * c := hunion
    _ ≤ noiseCount ξ k n * c := Nat.mul_le_mul_right c hHc
    _ = c * noiseCount ξ k n := Nat.mul_comm _ _
    _ < P := hP

/-- **The same absorption conclusion, reached from the noise gate** ([Inevitability] §6,
Theorem 6.6(v), IN-28). `RedundantFiber.compPredFrame_eq_next_of_realizable_budget` reaches
`RedundantFiber.compPredFrame_eq_next_of_touch_bound`'s touch bound from the realizable branch's
surprise count; this reaches the identical touch bound from `NoiseGated` instead, via
`noiseGated_card_le`, and calls the same touch-bound theorem to close — the argument neither route
duplicates. The bound is over `noiseCount ξ k n`, a quantity of the horizon `n` itself rather than a
schedule-independent constant, so what this route delivers is honestly per-horizon — the shape the
noisy branch's own rate takes (clause (iii)), not the realizable branch's lifetime-free anchor.
**Not a strengthening of the damage model:** `noiseGated_eq_empty_of_quiet` already shows the gate
is empty on a noise-free stream, so this capstone has no content there — a parallel route to
Theorem 6.6(v), not a better one. -/
theorem compPredFrame_eq_next_of_noiseGated {n₁ C P W : ℕ} [NeZero C] [NeZero P] {hW : 2 ≤ W}
    (S : Fin n₁ → Fin n₁) (dec : Fin C → Fin n₁ → Fin n₁) (x₀ : Fin n₁)
    {c₀ : Fin C} (hc₀ : ∀ s, dec c₀ (S^[s] x₀) = S (S^[s] x₀))
    (v₀ : Fin P → WVec C W) {k n c : ℕ} (ξ : ℕ → Bool)
    {H : Finset ℕ} (hH : H ⊆ Finset.range n) (hgate : NoiseGated k ξ H)
    (col : ℕ → Finset (Fin P)) (hcol : ∀ t, (col t).card ≤ c)
    (hP : c * noiseCount ξ k n < P) (land : ℕ → Fin P → WVec C W) :
    ∃ T : ℕ, ∀ t, T ≤ t →
      compPredFrame S dec (S^[t] x₀) (compRun W (predMiss S dec x₀) v₀ H col land t)
        = S (S^[t] x₀) := by
  refine compPredFrame_eq_next_of_touch_bound (hW := hW) S dec x₀ hc₀ v₀ H col land ?_
  have hunion : (H.biUnion col).card ≤ H.card * c :=
    le_trans Finset.card_biUnion_le
      (le_trans (Finset.sum_le_sum fun t _ => hcol t) (by rw [Finset.sum_const, smul_eq_mul]))
  have hHc : H.card ≤ noiseCount ξ k n := noiseGated_card_le ξ hH hgate
  calc (H.biUnion col).card ≤ H.card * c := hunion
    _ ≤ noiseCount ξ k n * c := Nat.mul_le_mul_right c hHc
    _ = c * noiseCount ξ k n := Nat.mul_comm _ _
    _ < P := hP

/-- **The gate's own boundary — a noise-free stream gates nothing** ([Inevitability] §6, IN-25).
On a stream quiet throughout the horizon, the only schedule confined to it that is also noise-gated
is the empty one: a noise-gated host does no damage at all there. That noise-free stream is exactly
the branch whose surprise count is the lifetime-free anchor `4(C−1)/θ`
(`WitnessMixture.witness_floorSurprise_card_mul_le` at `noiseCount = 0`), so the gate and that bound
have content on disjoint branches — this is a variant repair of Theorem 6.6(v), not a strengthening
of it. -/
theorem noiseGated_eq_empty_of_quiet {k n : ℕ} {ξ : ℕ → Bool} {H : Finset ℕ}
    (hquiet : ∀ t < n, ξ (t + k) = false) (hH : H ⊆ Finset.range n)
    (hgate : NoiseGated k ξ H) : H = ∅ := by
  refine Finset.eq_empty_iff_forall_notMem.mpr fun s hs => ?_
  have hslt : s < n := Finset.mem_range.mp (hH hs)
  have h1 := hgate s hs
  have h2 := hquiet s hslt
  rw [h1] at h2
  exact Bool.noConfusion h2

/-! ## The eventually-quiet class, and its lifetime-free redundancy

Between the noise-free branch `noiseGated_eq_empty_of_quiet` covers and the honestly per-horizon
`compPredFrame_eq_next_of_noiseGated` sits a third class: streams that fire finitely often overall
rather than not at all. `QuietFrom` names it directly on the stream, with no run and no schedule,
exactly as `NoiseGated` does — `noiseCount_le_of_quietFrom` is the uniform-in-horizon bound that
makes a single redundancy condition serve every horizon at once ([Inevitability] §6, Theorem
6.6(v″)). -/

/-- **A stream that has fired at most `m` times in total, at offset `k`.** Every firing sits below
`m`, so the same bound `m` caps how often the stream has fired by *any* horizon — the class between
a noise-free stream (`m = 0`) and one merely bounded within each horizon separately
([Inevitability] §6, Theorem 6.6(v″)). -/
def QuietFrom (k m : ℕ) (ξ : ℕ → Bool) : Prop := ∀ s, ξ (s + k) = true → s < m

/-- **The uniform count.** Under `QuietFrom`, the noise count at *every* horizon `n` is capped by
the same `m` — the fired times all sit below `m`, so extending the horizon past `m` never grows the
count further ([Inevitability] §6, Theorem 6.6(v″), IN-13). -/
theorem noiseCount_le_of_quietFrom {k m : ℕ} {ξ : ℕ → Bool} (hq : QuietFrom k m ξ) (n : ℕ) :
    noiseCount ξ k n ≤ m := by
  rw [noiseCount]
  calc ((Finset.range n).filter fun t => ξ (t + k)).card
      ≤ (Finset.range m).card :=
        Finset.card_le_card fun t ht =>
          Finset.mem_range.mpr (hq t (Finset.mem_filter.mp ht).2)
    _ = m := Finset.card_range m

/-- **The composite survives a gated schedule under `QuietFrom`, at one redundancy for every
horizon at once.** `c * m < P` already covers `c * noiseCount ξ k n < P` at every `n`
(`noiseCount_le_of_quietFrom`), so `exists_untouched_copy_of_noiseGated`'s conclusion holds
uniformly — the fixed redundancy is a lifetime statement, not a per-horizon one
([Inevitability] §6, Theorem 6.6(v″)). -/
theorem exists_untouched_copy_of_quietFrom {P : ℕ} [NeZero P] {k m c : ℕ} {ξ : ℕ → Bool}
    (hq : QuietFrom k m ξ) (hP : c * m < P) {n : ℕ} {H : Finset ℕ} (hH : H ⊆ Finset.range n)
    (hgate : NoiseGated k ξ H) (col : ℕ → Finset (Fin P)) (hcol : ∀ t, (col t).card ≤ c) :
    ∃ i₀ : Fin P, ∀ t ∈ H, i₀ ∉ col t :=
  exists_untouched_copy_of_noiseGated ξ hH hgate col hcol
    (lt_of_le_of_lt (Nat.mul_le_mul_left c (noiseCount_le_of_quietFrom hq n)) hP)

/-- **The same uniformization of `compPredFrame_eq_next_of_noiseGated`** — one redundancy
condition, `c * m < P`, serving every horizon's conclusion at once, exactly (v)'s form reached from
the eventually-quiet class rather than from a per-horizon noise count ([Inevitability] §6,
Theorem 6.6(v″)). -/
theorem compPredFrame_eq_next_of_quietFrom {n₁ C P W : ℕ} [NeZero C] [NeZero P] {hW : 2 ≤ W}
    (S : Fin n₁ → Fin n₁) (dec : Fin C → Fin n₁ → Fin n₁) (x₀ : Fin n₁)
    {c₀ : Fin C} (hc₀ : ∀ s, dec c₀ (S^[s] x₀) = S (S^[s] x₀))
    (v₀ : Fin P → WVec C W) {k m c : ℕ} {ξ : ℕ → Bool} (hq : QuietFrom k m ξ) (hP : c * m < P)
    {n : ℕ} {H : Finset ℕ} (hH : H ⊆ Finset.range n) (hgate : NoiseGated k ξ H)
    (col : ℕ → Finset (Fin P)) (hcol : ∀ t, (col t).card ≤ c) (land : ℕ → Fin P → WVec C W) :
    ∃ T : ℕ, ∀ t, T ≤ t →
      compPredFrame S dec (S^[t] x₀) (compRun W (predMiss S dec x₀) v₀ H col land t)
        = S (S^[t] x₀) :=
  compPredFrame_eq_next_of_noiseGated (hW := hW) S dec x₀ hc₀ v₀ ξ hH hgate col hcol
    (lt_of_le_of_lt (Nat.mul_le_mul_left c (noiseCount_le_of_quietFrom hq n)) hP) land

/-! ## A designed instance, strictly between the two named branches

`quietStream` is a concrete eventually-quiet stream: it fires on exactly the window `[k, k + m)`.
At `0 < m` it is not the noise-free branch (`witMiss_quietStream_zero_of_pos` — it misses
immediately, at `s = 0`), yet its total miss set is finite (`finite_setOf_witMiss_quietStream`) —
the two boundary facts placing it in the class `QuietFrom` names and neither of Theorem 6.6(iii)'s
two branches covers on its own. -/

/-- **The designed eventually-quiet stream at parameters `k, m`.** Fires on exactly the window
`[k, k + m)` and is silent everywhere else ([Inevitability] §6, Theorem 6.6(v″)). -/
def quietStream (k m : ℕ) : ℕ → Bool := fun u => decide (k ≤ u ∧ u < k + m)

/-- **`quietStream` is eventually-quiet at its own parameter `m`.** Every one of its firings, read
at offset `k`, sits below `m` by construction ([Inevitability] §6, Theorem 6.6(v″)). -/
theorem quietFrom_quietStream (k m : ℕ) : QuietFrom k m (quietStream k m) := by
  intro s hs
  simp only [quietStream, decide_eq_true_eq] at hs
  omega

/-- **The designed candidate's misses are exactly the designed prefix.** `witMiss_zero` reads the
noise bit directly, and `quietStream` fires there exactly below `m` ([Inevitability] §6,
Theorem 6.6(v″)). -/
theorem witMiss_quietStream_zero_iff {k : ℕ} [NeZero k] (m s : ℕ) :
    witMiss k (quietStream k m) s 0 = true ↔ s < m := by
  rw [witMiss_zero, quietStream]
  simp only [decide_eq_true_eq]
  omega

/-- **The gate on `quietStream` is exactly confinement to the designed prefix.** Composing
`noiseGated_iff_witMiss` with `witMiss_quietStream_zero_iff` reads `NoiseGated` on this stream as a
plain range containment ([Inevitability] §6, Theorem 6.6(v″), IN-28). -/
theorem noiseGated_quietStream_iff {k : ℕ} [NeZero k] (m : ℕ) (H : Finset ℕ) :
    NoiseGated k (quietStream k m) H ↔ H ⊆ Finset.range m := by
  rw [noiseGated_iff_witMiss]
  simp only [witMiss_quietStream_zero_iff, ← Finset.mem_range]
  exact Iff.rfl

/-- **Not immediately realizable, at `0 < m`.** The designed candidate misses at `s = 0` — the
first boundary fact placing `quietStream` off the noise-free branch. -/
theorem witMiss_quietStream_zero_of_pos {k : ℕ} [NeZero k] {m : ℕ} (hm : 0 < m) :
    witMiss k (quietStream k m) 0 0 = true :=
  (witMiss_quietStream_zero_iff m 0).mpr hm

/-- **Eventually realizable.** The designed candidate's total miss set is finite — the second
boundary fact, placing `quietStream` off the noisy branch that never settles. -/
theorem finite_setOf_witMiss_quietStream {k : ℕ} [NeZero k] (m : ℕ) :
    {s : ℕ | witMiss k (quietStream k m) s 0 = true}.Finite :=
  Set.Finite.subset (Set.finite_Iio m) fun s hs => (witMiss_quietStream_zero_iff m s).mp hs

/-! ## A source automaton emitting the designed instance

`sourceStep` is a saturating counter on `Fin (k + m + 1)`: it increments until it reaches the top
and then holds there. Read through `sourceOut`, the state it reaches after `u` steps from `0`
emits exactly `quietStream k m u` — a host packaging for the designed instance, confining its own
non-invertibility to the source (`sourceStep_not_injective`) rather than to anything downstream. -/

/-- **The saturating counter.** Increments by one short of the top, `k + m`, and holds there —
the source `sourceOut` reads against. -/
def sourceStep (k m : ℕ) : Fin (k + m + 1) → Fin (k + m + 1) :=
  fun i => ⟨min ((i : ℕ) + 1) (k + m), by omega⟩

/-- **The source's output.** Fires exactly while the counter sits in `[k, k + m)`, mirroring
`quietStream`'s own window. -/
def sourceOut (k m : ℕ) (i : Fin (k + m + 1)) : Bool := decide (k ≤ (i : ℕ) ∧ (i : ℕ) < k + m)

/-- **The counter's value after `t` steps from any start**, in closed form: it advances by `t` and
saturates at `k + m`. Every fact about `sourceStep`'s orbit below reduces to this one arithmetic
identity. -/
theorem val_iterate_sourceStep (k m t : ℕ) (i : Fin (k + m + 1)) :
    ((sourceStep k m)^[t] i : ℕ) = min ((i : ℕ) + t) (k + m) := by
  induction t with
  | zero =>
      have h : (i : ℕ) ≤ k + m := Nat.le_of_lt_succ i.isLt
      simp only [Function.iterate_zero, id_eq, Nat.add_zero]
      omega
  | succ t ih =>
      rw [Function.iterate_succ_apply']
      change min (((sourceStep k m)^[t] i : ℕ) + 1) (k + m) = min ((i : ℕ) + (t + 1)) (k + m)
      omega

/-- **The source emits `quietStream` from state `0`** ([Inevitability] §6, Theorem 6.6(v″)): the
output read off the counter after `u` steps from `0` is the designed stream's own value at `u`. -/
theorem sourceOut_iterate_sourceStep_zero (k m u : ℕ) :
    sourceOut k m ((sourceStep k m)^[u] (0 : Fin (k + m + 1))) = quietStream k m u := by
  have hval := val_iterate_sourceStep k m u (0 : Fin (k + m + 1))
  simp only [Fin.val_zero, Nat.zero_add] at hval
  rw [sourceOut, hval, quietStream, decide_eq_decide]
  omega

/-- **The counter saturates by `k + m` steps, from every start.** Not just from `0` — the top is
reached from anywhere in the type within `k + m` steps, since no start sits further than `k + m`
below it. -/
theorem sourceStep_iterate_eq_last (k m : ℕ) (i : Fin (k + m + 1)) :
    (sourceStep k m)^[k + m] i = Fin.last (k + m) := by
  apply Fin.ext
  rw [val_iterate_sourceStep, Fin.val_last]
  omega

/-- **The saturated state is a fixed point.** Once at the top, the counter stays there. -/
theorem sourceStep_last (k m : ℕ) : sourceStep k m (Fin.last (k + m)) = Fin.last (k + m) := by
  apply Fin.ext
  rw [show ((sourceStep k m (Fin.last (k + m)) : ℕ)) = ((sourceStep k m)^[1] (Fin.last (k + m)) : ℕ)
      from rfl, val_iterate_sourceStep, Fin.val_last]
  omega

/-- **The step map is not injective, at `1 ≤ m`.** The saturated top and its immediate
predecessor both land on the top — the host's own non-invertibility, confined to the source and
nowhere claimed of the guest it drives. -/
theorem sourceStep_not_injective {k m : ℕ} (hm : 1 ≤ m) :
    ¬ Function.Injective (sourceStep k m) := by
  intro hinj
  have h1 : sourceStep k m (⟨k + m - 1, by omega⟩ : Fin (k + m + 1)) = Fin.last (k + m) := by
    apply Fin.ext
    simp only [sourceStep, Fin.val_last]
    omega
  have heq := hinj (h1.trans (sourceStep_last k m).symm)
  have hval : (k + m - 1 : ℕ) = k + m := by
    have := congrArg Fin.val heq
    simpa [Fin.val_last] using this
  omega

end DamageGate

/-- info: 'DamageGate.noiseGated_iff_witMiss' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DamageGate.noiseGated_iff_witMiss

/-- info: 'DamageGate.noiseGated_card_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DamageGate.noiseGated_card_le

/-- info: 'DamageGate.exists_untouched_copy_of_noiseGated' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DamageGate.exists_untouched_copy_of_noiseGated

/-- info: 'DamageGate.noiseGated_eq_empty_of_quiet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DamageGate.noiseGated_eq_empty_of_quiet

/-- info: 'DamageGate.compPredFrame_eq_next_of_noiseGated' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DamageGate.compPredFrame_eq_next_of_noiseGated

/-- info: 'DamageGate.noiseCount_le_of_quietFrom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DamageGate.noiseCount_le_of_quietFrom

/-- info: 'DamageGate.exists_untouched_copy_of_quietFrom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DamageGate.exists_untouched_copy_of_quietFrom

/-- info: 'DamageGate.compPredFrame_eq_next_of_quietFrom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DamageGate.compPredFrame_eq_next_of_quietFrom

/-- info: 'DamageGate.quietFrom_quietStream' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DamageGate.quietFrom_quietStream

/-- info: 'DamageGate.witMiss_quietStream_zero_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DamageGate.witMiss_quietStream_zero_iff

/-- info: 'DamageGate.noiseGated_quietStream_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DamageGate.noiseGated_quietStream_iff

/-- info: 'DamageGate.witMiss_quietStream_zero_of_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DamageGate.witMiss_quietStream_zero_of_pos

/-- info: 'DamageGate.finite_setOf_witMiss_quietStream' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DamageGate.finite_setOf_witMiss_quietStream

/-- info: 'DamageGate.val_iterate_sourceStep' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DamageGate.val_iterate_sourceStep

/-- info: 'DamageGate.sourceOut_iterate_sourceStep_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DamageGate.sourceOut_iterate_sourceStep_zero

/-- info: 'DamageGate.sourceStep_iterate_eq_last' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DamageGate.sourceStep_iterate_eq_last

/-- info: 'DamageGate.sourceStep_last' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DamageGate.sourceStep_last

/-- info: 'DamageGate.sourceStep_not_injective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DamageGate.sourceStep_not_injective
