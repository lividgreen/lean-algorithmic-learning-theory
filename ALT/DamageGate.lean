/-
Copyright (c) 2026 Mykola Palamarchuk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mykola Palamarchuk
-/
import ALT.RedundantFiber
import ALT.WitnessMixture

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
-/

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

end DamageGate

/-- info: 'DamageGate.noiseGated_iff_witMiss' depends on axioms: [propext, Quot.sound] -/
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
