/-
Copyright (c) 2026 Mykola Palamarchuk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mykola Palamarchuk
-/
module

public import ALT.SkewFiber
public import ALT.SurpriseBudget

-- Formal-check file, not Mathlib-destined: opt out of the house-style header linter.
set_option linter.style.header false

/-!
# Which hosts absorb a debt: the single-witness evolutionary fiber ([Inevitability] §6)

`SurpriseBudget` prices a debt against a margin over an arbitrary host in the Hamming metric on
`Mem ι V`; `SkewFiber` builds one deterministic generation of variation and selection over a
population `Pop P C = Fin P → Fin C`, driven by a base coordinate through a skew product. This file
asks `SurpriseBudget`'s question of `SkewFiber`'s own construction: does the evolutionary fiber's
step absorb a damage debt, and by which of `SurpriseBudget`'s repairs?

`Pop P C = Fin P → Fin C` is `Mem (Fin P) (Fin C)` definitionally, so every statement below is about
the fiber at a fixed base state, with the single self-map `gaGen (fit x) (vary x)` as the host and
the base coordinate treated as an external driver. Nothing here gives the base coordinate cells of
its own; that is outside what a skew product's fiber can be asked to absorb.

## Two negatives, and why a margin is the wrong question for this host

The evolutionary step is **expansive** whenever selection actually does anything
(`not_nonexpansive_of_gaGen_ne`): once two populations produce different winners, one single-slot
change along a path between them must flip the winner, and a flip changes every one of the `P`
slots at once. So `SurpriseBudget.survives_of_margin`'s hypothesis is unavailable except in the
degenerate case where selection is inoperative.

One-step erasure fails too, and not as a technicality: it fails **inside the construction's own
coverage regime** (`not_corrects_of_faithful`). With variation switched off —
`SkewFiber.surjective_fittestFrame_of_fixed`'s own setting — the fitness-minimizing codeword's
population is a fixed point, one cell off it is inside
radius `1`, and the fold reads that one changed cell straight back, changing the fitness winner
outright. So `SurpriseBudget.survives_of_corrects`'s hypothesis is unavailable there too, in the
exact regime where the codeword frame's own coverage witness lives.

## The headline: coverage and a margin collide

`margin_yields_max` shows a margin at a settled point forces that point's codeword to be
the strict fitness maximum — from the same single-slot construction. A settled point that is *also*
covered by every candidate codeword is therefore impossible once `2 ≤ C`
(`not_surjective_of_margin`): the ω-limit collapses to whichever populations reach the maximizer,
and the codeword-valued reading can be constant on it at best.

This does **not** refute `SkewFiber.fiber_emergence_pricing`'s hypothesis outright — that hypothesis
is surjectivity over the *whole* skew-product carrier, not over one fiber at a fixed base state.
What it refutes is the only way the population coordinate alone could carry that coverage:
freezing the base and ranging over initial populations, exactly
`SkewFiber.surjective_fittestFrame_of_fixed`'s route. Under a margin, coverage has to be charged to
the base coordinate instead — which is what
`SkewFiber.predFrame` does.

## The positive half: the base-reading frame absorbs a debt at radius `P - 1`

`predFrame_margin` prices what the fiber *can* do: at a fixed base state, the basin of populations
containing a correctly-predicting member is closed under one generation, the reading — the base's
own next state, decoded from the fittest member — is constant on it, and the margin is `P - 1`, the
widest radius under which a perturbation is guaranteed to leave at least one untouched slot.
`predFrame_survives` composes this with `SurpriseBudget.survives_of_invariant`: the damaged and
undamaged readings agree at every step, for any arrival pattern and any total debt, at that radius.

No accumulation argument reaches this: after one step both trajectories are constant populations, so
their Hamming distance is `0` or `P`, and `P > P - 1`. The margin survives only because
`survives_of_invariant` needs no accumulation bound at all.

## Scope

Everything here is at a **fixed base state** `x`, with `vary i = id` (variation switched off) in
every result that names a margin or a fixed point. Whether selection converges under real variation,
and from which initial states, is untouched — as in `SkewFiber` itself. No numbered result is
claimed machine-checked by this file; the port from [Inevitability] §6, Proposition 6.1(iii) to this
setting is stated in each theorem's own docstring.
-/


@[expose] public section

namespace EvoAbsorption

open SkewFiber SurpriseBudget PersistenceCapacity Decoupling

variable {n₁ P C : ℕ}

/-! ## A path between two populations, one slot at a time -/

section Path

/-- **The interpolation from `p` to `q`**: at step `k`, the first `k` slots already agree with `q`,
the rest still agree with `p`. `pathPop p q 0 = p` and, past `P`, `pathPop p q _ = q`. -/
private def pathPop (p q : Pop P C) (k : ℕ) : Pop P C := fun i => if (i : ℕ) < k then q i else p i

private theorem pathPop_zero (p q : Pop P C) : pathPop p q 0 = p := by
  funext i; simp [pathPop]

private theorem pathPop_eq_of_ge (p q : Pop P C) {k : ℕ} (hk : P ≤ k) : pathPop p q k = q := by
  funext i
  have hi : (i : ℕ) < k := lt_of_lt_of_le i.isLt hk
  simp [pathPop, hi]

/-- **Consecutive steps of the path are one slot apart, at most.** -/
private theorem hammingDist_pathPop_succ_le (p q : Pop P C) (k : ℕ) :
    hammingDist (pathPop p q k) (pathPop p q (k + 1)) ≤ 1 := by
  unfold hammingDist
  have hsub : (Finset.univ.filter fun i : Fin P => pathPop p q k i ≠ pathPop p q (k + 1) i)
      ⊆ Finset.univ.filter fun i : Fin P => (i : ℕ) = k := by
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    by_contra hne
    apply hi
    change (if (i : ℕ) < k then q i else p i) = (if (i : ℕ) < k + 1 then q i else p i)
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · rw [ite_eq_left hlt, ite_eq_left (by omega)]
    · rw [ite_eq_right (by omega), ite_eq_right (by omega)]
  have hone : (Finset.univ.filter fun i : Fin P => (i : ℕ) = k).card ≤ 1 :=
    Finset.card_le_one.mpr (by
      intro a ha b hb
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
      exact Fin.ext (ha.trans hb.symm))
  exact le_trans (Finset.card_le_card hsub) hone

/-- **A single flipped slot is one apart.** -/
private theorem hammingDist_update_eq_one {x : Pop P C} (i : Fin P) {v : Fin C} (hv : v ≠ x i) :
    hammingDist x (Function.update x i v) = 1 := by
  unfold hammingDist
  have heq : (Finset.univ.filter fun j : Fin P => x j ≠ Function.update x i v j) = {i} := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro hj
      by_contra hne
      exact hj (Function.update_of_ne hne v x).symm
    · rintro rfl
      simpa using hv.symm
  rw [heq, Finset.card_singleton]

/-- **A telescoping walk that never changes must have equal endpoints.** Its contrapositive is the
route into both negatives below: if the two ends of a walk differ, some single step along it
already differs. -/
private theorem exists_step_ne_of_ne {g : Pop P C → Pop P C} {r : ℕ → Pop P C}
    (hne : g (r 0) ≠ g (r P)) : ∃ k < P, g (r k) ≠ g (r (k + 1)) := by
  by_contra hc
  push Not at hc
  apply hne
  have hstable : ∀ m, m ≤ P → g (r 0) = g (r m) := by
    intro m
    induction m with
    | zero => intro _; rfl
    | succ m ih =>
        intro hm
        rw [ih (Nat.le_of_succ_le hm), hc m (Nat.lt_of_succ_le hm)]
  exact hstable P le_rfl

end Path

/-! ## (a) Non-expansiveness holds only when selection is inoperative -/

section Selection

variable [NeZero P]

/-- **A selection step is expansive whenever it does anything at all.** If two populations produce
different winners, some single-slot change along a path between them already flips the winner — and
since a generation copies the winner out to every slot, that one flip changes all `P` of them at
once. So `SurpriseBudget.HammingNonexpansive` is unavailable to `gaGen fit vary` except when
selection is constant on every input. -/
theorem not_nonexpansive_of_gaGen_ne (fit : Fin C → ℕ) (vary : Fin P → Fin C → Fin C) (hP : 2 ≤ P)
    (h : ∃ p q, gaGen fit vary p ≠ gaGen fit vary q) :
    ¬ HammingNonexpansive (gaGen fit vary) := by
  obtain ⟨p, q, hpq⟩ := h
  intro hne
  obtain ⟨k, -, hstep⟩ := exists_step_ne_of_ne (r := pathPop p q) (g := gaGen fit vary)
    (by rwa [pathPop_zero, pathPop_eq_of_ge p q le_rfl])
  have hdiff : ∀ i, gaGen fit vary (pathPop p q k) i ≠ gaGen fit vary (pathPop p q (k + 1)) i :=
    fun i hcontra => hstep (funext fun _ => hcontra)
  have hdist : hammingDist (gaGen fit vary (pathPop p q k))
      (gaGen fit vary (pathPop p q (k + 1))) = P := by
    unfold hammingDist
    rw [Finset.filter_true_of_mem (fun i _ => hdiff i), Finset.card_univ, Fintype.card_fin]
  have hle := hne (pathPop p q k) (pathPop p q (k + 1))
  rw [hdist] at hle
  have hstep_le := hammingDist_pathPop_succ_le p q k
  omega

/-- **The converse: with selection switched off, the step is trivially non-expansive.** A `gaGen`
that returns the same population from every input separates nothing, so it costs no damage to be
non-expansive over. Together with `not_nonexpansive_of_gaGen_ne` this reads as an equivalence:
`HammingNonexpansive (gaGen fit vary)` for `2 ≤ P` exactly when `gaGen fit vary` is constant. -/
theorem nonexpansive_of_gaGen_const (fit : Fin C → ℕ) (vary : Fin P → Fin C → Fin C)
    (hconst : ∀ p q, gaGen fit vary p = gaGen fit vary q) :
    HammingNonexpansive (gaGen fit vary) := fun p q => by
  rw [hconst p q, hammingDist_self]; exact Nat.zero_le _

end Selection

/-! ## (b) One-step erasure fails outright in the construction's own coverage regime -/

section Erasure

/-- The fold underlying `fittest` never leaves its starting value once every later slot's fitness
is no better: ties keep the incumbent, so a start that already dominates everything it visits is
a fixed point of the fold. -/
private theorem foldl_fittest_eq_of_ge (fit : Fin C → ℕ) (p : Pop P C) (l : List (Fin P))
    (c : Fin C) (hc : ∀ i ∈ l, fit (p i) ≤ fit c) :
    l.foldl (fun c i => if fit c < fit (p i) then p i else c) c = c := by
  induction l with
  | nil => rfl
  | cons i l ih =>
      simp only [List.mem_cons] at hc
      rw [List.foldl_cons, ite_eq_right (not_lt.mpr (hc i (Or.inl rfl)))]
      exact ih fun j hj => hc j (Or.inr hj)

/-- **A population dominated by its own first slot returns that slot.** -/
private theorem fittest_eq_of_ge [NeZero P] (fit : Fin C → ℕ) (p : Pop P C)
    (hle : ∀ i, fit (p i) ≤ fit (p 0)) : fittest fit p = p 0 :=
  foldl_fittest_eq_of_ge fit p (List.finRange P) (p 0) (fun i _ => hle i)

/-- **A uniform population with one slot swapped for a no-worse codeword keeps the swap as its
winner.** The single-slot pair both negatives below turn on: starting a uniform population at
`p₀` and overwriting slot `0` with `b`, the fold begins at `b` and nothing it meets afterwards
(all still `p₀`) beats it, so it never leaves. -/
private theorem fittest_update_const_eq [NeZero P] (fit : Fin C → ℕ) (p₀ b : Fin C)
    (hle : fit p₀ ≤ fit b) :
    fittest fit (Function.update (fun _ : Fin P => p₀) 0 b) = b := by
  have hupd0 : Function.update (fun _ : Fin P => p₀) 0 b 0 = b :=
    Function.update_self 0 b (fun _ : Fin P => p₀)
  have hge : ∀ i, fit (Function.update (fun _ : Fin P => p₀) 0 b i) ≤
      fit (Function.update (fun _ : Fin P => p₀) 0 b 0) := by
    rw [hupd0]
    intro i
    by_cases hi : i = 0
    · rw [hi, hupd0]
    · rw [Function.update_of_ne hi]; exact hle
  rw [fittest_eq_of_ge fit _ hge, hupd0]

/-- **One-step erasure fails at radius `1`, for every fitness, once variation is switched off** —
[Inevitability] §6's own coverage regime, `SkewFiber.surjective_fittestFrame_of_fixed`'s setting.
The fitness-minimizing codeword's uniform population is a fixed point, so it sits in the ω-limit of
the whole space; one cell of it flipped to any other codeword is inside radius `1`; and the fold
reads that flipped cell straight back as the new winner, since nothing else in the population beats
it in fitness. So a single-cell perturbation of an attractor state already changes the next state —
`SurpriseBudget.Corrects` is unavailable here, in exactly the regime the codeword frame's own
coverage witness (`SkewFiber.surjective_fittestFrame_of_fixed`) lives in. -/
theorem not_corrects_of_faithful [NeZero P] (fit : Fin C → ℕ) (hC : 2 ≤ C) :
    ¬ Corrects (gaGen fit fun _ : Fin P => id) Set.univ 1 := by
  intro hcorr
  have : Nontrivial (Fin C) := Fin.nontrivial_iff_two_le.mpr hC
  obtain ⟨c₀, hc₀⟩ := Finite.exists_min fit
  obtain ⟨b, hb⟩ := exists_ne c₀
  set s : Pop P C := fun _ => c₀ with hs_def
  have hfix : gaGen fit (fun _ : Fin P => id) s = s := by
    funext i
    change fittest fit (fun j => id (s j)) = c₀
    simpa [hs_def] using fittest_const P fit c₀
  have hsmem : s ∈ omegaLimit (gaGen fit fun _ : Fin P => id) Set.univ :=
    Set.mem_iInter.mpr fun t => ⟨s, Set.mem_univ s, Function.iterate_fixed hfix t⟩
  have hupdmem : Function.update s 0 b ∈ hball 1 s := by
    change hammingDist s (Function.update s 0 b) ≤ 1
    exact (hammingDist_update_eq_one 0 hb).le
  have heq := hcorr s hsmem (Function.update s 0 b) hupdmem
  have hval : gaGen fit (fun _ : Fin P => id) (Function.update s 0 b) 0 = b := by
    change fittest fit (fun j => id (Function.update s 0 b j)) = b
    have hidfun : (fun j => id (Function.update s 0 b j)) = Function.update s 0 b := rfl
    rw [hidfun]
    exact fittest_update_const_eq fit c₀ b (hc₀ b)
  have hval0 : gaGen fit (fun _ : Fin P => id) s 0 = c₀ := by
    change fittest fit (fun j => id (s j)) = c₀
    simpa [hs_def] using fittest_const P fit c₀
  exact hb (hval0 ▸ hval ▸ congrFun heq 0)

end Erasure

/-! ## (c) The headline: coverage and a margin collide -/

section Collision

/-- **`gaGen`'s output is always a constant population**, so every element of its ω-limit already
is one: the ω-limit is `⋂ t, U^[t] '' univ`, and the `t = 1` term alone already lands inside the
constant populations. -/
private theorem exists_const_of_mem_omegaLimit_gaGen [NeZero P] (fit : Fin C → ℕ)
    (vary : Fin P → Fin C → Fin C) {s : Pop P C}
    (hs : s ∈ omegaLimit (gaGen fit vary) Set.univ) : ∃ a, s = fun _ : Fin P => a := by
  obtain ⟨p, -, hp⟩ := Set.mem_iInter.mp hs 1
  refine ⟨fittest fit (fun i => vary i (p i)), ?_⟩
  rw [← hp, Function.iterate_one]
  rfl

/-- **A margin at a constant attractor point forces its codeword to be the strict fitness
maximum.** Perturbing that one attractor at a single slot to any other codeword `b` keeps the
margin's promise that the reading does not move — but `fittest_update_const_eq` shows the fold
only keeps that promise when `b` does not beat the attractor's own codeword. Since the perturbed
population puts `b` in the winner's seat unless something beats it, margin plus non-improvement
forces the win back to `a`, and ruling out a non-strict tie is exactly what keeps the codeword
unique. -/
theorem margin_yields_max [NeZero P] (fit : Fin C → ℕ) (vary : Fin P → Fin C → Fin C)
    (hmargin : HasMargin (gaGen fit vary) Set.univ (fittest fit) 1) (a : Fin C)
    (ha : (fun _ : Fin P => a) ∈ omegaLimit (gaGen fit vary) Set.univ) :
    ∀ b ≠ a, fit b < fit a := by
  intro b hb
  by_contra hnot
  rw [not_lt] at hnot
  have hupdmem : Function.update (fun _ : Fin P => a) 0 b ∈ hball 1 (fun _ : Fin P => a) := by
    change hammingDist (fun _ : Fin P => a) (Function.update (fun _ : Fin P => a) 0 b) ≤ 1
    exact (hammingDist_update_eq_one 0 hb).le
  have hval := (hmargin _ ha _ hupdmem).2
  rw [fittest_update_const_eq fit a b hnot, fittest_const] at hval
  exact hb hval

/-- **A margin and a codeword frame that reaches every candidate cannot coexist**, once
`2 ≤ C`: the coverage witnesses for two distinct codewords `a ≠ a'` are, by
`exists_const_of_mem_omegaLimit_gaGen` and `fittest_const`, exactly the constant populations at
`a` and `a'` themselves — and `margin_yields_max` applied to both orders forces `fit a' < fit a`
and `fit a < fit a'` at once.

This is stated over the *whole* ω-limit's coverage, not the initial-population coverage
`SkewFiber.surjective_fittestFrame_of_fixed` supplies — see the module docstring for why it does
**not** refute `SkewFiber.fiber_emergence_pricing`'s hypothesis outright. -/
theorem not_surjective_of_margin [NeZero P] (fit : Fin C → ℕ) (vary : Fin P → Fin C → Fin C)
    (hC : 2 ≤ C) (hmargin : HasMargin (gaGen fit vary) Set.univ (fittest fit) 1) :
    ¬ Function.Surjective
        (Set.domRestrict (omegaLimit (gaGen fit vary) Set.univ) (fittest fit)) := by
  intro hsurj
  have : Nontrivial (Fin C) := Fin.nontrivial_iff_two_le.mpr hC
  have hconst : ∀ a : Fin C, (fun _ : Fin P => a) ∈ omegaLimit (gaGen fit vary) Set.univ := by
    intro a
    obtain ⟨⟨s, hs⟩, hval⟩ := hsurj a
    change fittest fit s = a at hval
    obtain ⟨c, hc⟩ := exists_const_of_mem_omegaLimit_gaGen fit vary hs
    rw [hc, fittest_const] at hval
    have hsa : s = fun _ : Fin P => a := by rw [hc, hval]
    rwa [hsa] at hs
  obtain ⟨a, a', haa'⟩ := exists_pair_ne (Fin C)
  have h1 := margin_yields_max fit vary hmargin a (hconst a) a' haa'.symm
  have h2 := margin_yields_max fit vary hmargin a' (hconst a') a haa'
  omega

/-- **With variation switched off, the margin fails outright, with no coverage hypothesis at
all.** Every constant population is a fixed point of `gaGen fit fun _ => id`
(`SkewFiber.fittest_const`), so `margin_yields_max` applies to *every* codeword — forcing every
`a` to be the strict fitness maximum over every `a' ≠ a` simultaneously, which two distinct
codewords already contradict. -/
theorem not_hasMargin_of_faithful [NeZero P] (fit : Fin C → ℕ) (hC : 2 ≤ C) :
    ¬ HasMargin (gaGen fit fun _ : Fin P => id) Set.univ (fittest fit) 1 := by
  intro hmargin
  have : Nontrivial (Fin C) := Fin.nontrivial_iff_two_le.mpr hC
  have hfixed : ∀ c : Fin C, (fun _ : Fin P => c) ∈
      omegaLimit (gaGen fit fun _ : Fin P => id) Set.univ := by
    intro c
    have hfix : gaGen fit (fun _ : Fin P => id) (fun _ : Fin P => c) = fun _ : Fin P => c := by
      funext i
      change fittest fit (fun j => id ((fun _ : Fin P => c) j)) = c
      simpa using fittest_const P fit c
    exact Set.mem_iInter.mpr fun t => ⟨_, Set.mem_univ _, Function.iterate_fixed hfix t⟩
  obtain ⟨a, a', haa'⟩ := exists_pair_ne (Fin C)
  have h1 := margin_yields_max fit _ hmargin a (hfixed a) a' haa'.symm
  have h2 := margin_yields_max fit _ hmargin a' (hfixed a') a haa'
  omega

end Collision

/-! ## The positive half: the base-reading frame absorbs a debt at radius `P - 1` -/

section Absorption

variable [NeZero P] (S : Fin n₁ → Fin n₁) (dec : Fin C → Fin n₁ → Fin n₁) (x : Fin n₁)

private theorem predFit_le_one (c : Fin C) : predFit S dec x c ≤ 1 := by
  unfold predFit
  split <;> omega

/-- **The basin**: populations holding at least one member that correctly predicts the base's
next step from `x`. -/
def predBasin : Set (Pop P C) := {p | ∃ i, dec (p i) x = S x}

/-- **The reading**: the fittest member's own prediction of the base's next state — the fiber
half of `SkewFiber.predFrame`, at the base coordinate frozen to `x`. -/
def predReading : Pop P C → Fin n₁ := fun p => dec (fittest (predFit S dec x) p) x

/-- **One correct member already makes the winner correct.** `SkewFiber.fittest_ge` carries the
one member's fitness `1` up to the fold's winner, and `predFit` never exceeds `1`, so the winner's
fitness is pinned at exactly `1` too. This is the single fact `predBasin`'s closure, `predReading`'s
constancy on the basin, and the margin all reduce to. -/
private theorem fittest_correct_of_mem {p : Pop P C} {i : Fin P} (hi : dec (p i) x = S x) :
    dec (fittest (predFit S dec x) p) x = S x := by
  by_contra hne
  have h1 : predFit S dec x (p i) ≤ predFit S dec x (fittest (predFit S dec x) p) :=
    fittest_ge (predFit S dec x) p i
  have h2 : predFit S dec x (fittest (predFit S dec x) p) ≤ 1 := predFit_le_one S dec x _
  have hi1 : predFit S dec x (p i) = 1 := by
    change (if dec (p i) x = S x then 1 else 0) = 1
    rw [ite_eq_left hi]
  have hval0 : predFit S dec x (fittest (predFit S dec x) p) = 0 := by
    change (if dec (fittest (predFit S dec x) p) x = S x then 1 else 0) = 0
    rw [ite_eq_right hne]
  omega

/-- **The basin is closed under one generation**, and the image lands in the fully-correct
constant populations: whatever member of `p` was correct, `fittest_correct_of_mem` carries that
correctness to the winner, which selection then copies out to every slot. -/
theorem mapsTo_predBasin : ∀ p ∈ predBasin S dec x,
    gaGen (predFit S dec x) (fun _ : Fin P => id) p ∈ predBasin S dec x := by
  rintro p ⟨i, hi⟩
  refine ⟨0, ?_⟩
  change dec (fittest (predFit S dec x) p) x = S x
  exact fittest_correct_of_mem S dec x hi

omit [NeZero P] in
/-- A population dominated at every slot by another differs from it in fewer than `P` cells; below
`P`, some slot must already agree. -/
private theorem exists_eq_of_hammingDist_lt_card {y z : Pop P C} (h : hammingDist y z < P) :
    ∃ i, y i = z i := by
  by_contra hc
  push Not at hc
  have heq : hammingDist y z = P := by
    unfold hammingDist
    rw [Finset.filter_true_of_mem (fun i _ => hc i), Finset.card_univ, Fintype.card_fin]
  omega

/-- **Every point the ω-limit of the basin can reach is a fully-correct constant population.**
The `t = 1` term of the ω-limit's intersection already lands inside `gaGen`'s (always-constant)
image, and `fittest_correct_of_mem` reads off its correctness from whichever slot of the
pre-image was correct. -/
private theorem exists_correct_const_of_mem_omegaLimit {p₀ : Pop P C}
    (hs : p₀ ∈ omegaLimit (gaGen (predFit S dec x) fun _ : Fin P => id) (predBasin S dec x)) :
    ∃ c, dec c x = S x ∧ p₀ = fun _ : Fin P => c := by
  obtain ⟨p, hp, hUp⟩ := Set.mem_iInter.mp hs 1
  have hUp' : gaGen (predFit S dec x) (fun _ : Fin P => id) p = p₀ := by
    rw [← hUp, Function.iterate_one]
  obtain ⟨i₀, hi₀⟩ := hp
  refine ⟨fittest (predFit S dec x) p, fittest_correct_of_mem S dec x hi₀, ?_⟩
  funext j
  rw [← hUp']
  rfl

/-- **A perturbation of a correct constant population, at radius below `P`, leaves an untouched
slot — and that slot is still correct.** This is the fatness step, and the reason the margin's
radius is `P - 1` and not larger: at radius `P` a perturbation could touch every slot at once. -/
private theorem exists_correct_of_hball {c : Fin C} (hc : dec c x = S x) {s' : Pop P C}
    (hs' : hammingDist (fun _ : Fin P => c) s' ≤ P - 1) : ∃ j, dec (s' j) x = S x := by
  have hP0 : P ≠ 0 := NeZero.ne P
  have hltP : hammingDist (fun _ : Fin P => c) s' < P := lt_of_le_of_lt hs' (by omega)
  obtain ⟨j, hj⟩ := exists_eq_of_hammingDist_lt_card hltP
  exact ⟨j, by rw [← hj]; exact hc⟩

/-- **The margin, at radius `P - 1`** ([Inevitability] §6, Proposition 6.1(iii), the base-reading
repair): at a correct constant attractor, any perturbation of at most `P - 1` slots leaves an
untouched, still-correct slot — fatness — and by `fittest_correct_of_mem` the reading is `S x`
both before and after — constancy. The radius is exactly `P - 1`: `P` slots could all move at
once (`not_nonexpansive_of_gaGen_ne`), so the fatness argument is unavailable past it. -/
theorem predFrame_margin :
    HasMargin (gaGen (predFit S dec x) fun _ : Fin P => id) (predBasin S dec x)
      (predReading S dec x) (P - 1) := by
  rw [hasMargin_iff]
  refine ⟨?_, ?_⟩
  · intro s hs s' hs'
    change hammingDist s s' ≤ P - 1 at hs'
    obtain ⟨c, hc, hs_eq⟩ := exists_correct_const_of_mem_omegaLimit S dec x hs
    rw [hs_eq] at hs'
    exact exists_correct_of_hball S dec x hc hs'
  · intro s hs s' hs'
    obtain ⟨hs'ball, hs'mem⟩ := hs'
    have hsmem : s ∈ predBasin S dec x := by
      obtain ⟨p₀, hp₀, hp₀eq⟩ := Set.mem_iInter.mp hs 0
      rw [Function.iterate_zero] at hp₀eq
      exact hp₀eq ▸ hp₀
    obtain ⟨i, hi⟩ := hsmem
    obtain ⟨i', hi'⟩ := hs'mem
    change dec (fittest (predFit S dec x) s') x = dec (fittest (predFit S dec x) s) x
    rw [fittest_correct_of_mem S dec x hi', fittest_correct_of_mem S dec x hi]

/-- **Non-vacuity**: the basin is inhabited exactly when some codeword already predicts the base
correctly at `x` — required, since the whole construction is about the empty set otherwise. -/
theorem mem_predBasin_of_correct {c : Fin C} (hc : dec c x = S x) :
    (fun _ : Fin P => c) ∈ predBasin S dec x := ⟨0, hc⟩

/-- **The debt survives, at radius `P - 1`, for any arrival pattern and any total debt**
([Inevitability] §6, Proposition 6.1(iii) composed with the third repair,
`SurpriseBudget.survives_of_invariant`). Starting from the uniform population at a codeword `c`
that already predicts the base correctly at `x`, the damaged and undamaged trajectories read the
same base state at every step, for any damage schedule whose per-event radius stays at most
`P - 1` — no accumulation bound is needed, because `predReading` is constant on the whole basin
(`fittest_correct_of_mem`), not merely on a Hamming ball around the attractor.

No accumulation argument reaches this radius: after one step both trajectories are constant
populations, so their Hamming distance is `0` or `P`, and `P > P - 1`
(`not_nonexpansive_of_gaGen_ne`). `survives_of_invariant` needs no accumulation bound at all,
which is exactly why it is the repair that applies here. -/
theorem predFrame_survives {c : Fin C} (hc : dec c x = S x) (D : Damage (Fin P) (Fin C))
    (hrad : D.radius ≤ P - 1) (t : ℕ) :
    traj (gaGen (predFit S dec x) fun _ : Fin P => id) D t (fun _ : Fin P => c) ∈
        predBasin S dec x ∧
      predReading S dec x
          (traj (gaGen (predFit S dec x) fun _ : Fin P => id) D t (fun _ : Fin P => c)) =
        predReading S dec x
          ((gaGen (predFit S dec x) fun _ : Fin P => id)^[t] (fun _ : Fin P => c)) := by
  have hD : ∀ t', ∀ s ∈ predBasin S dec x,
      D.perturb t' (gaGen (predFit S dec x) (fun _ : Fin P => id) s) ∈ predBasin S dec x := by
    intro t' s hs
    obtain ⟨i, hi⟩ := hs
    have hcorrect : dec (fittest (predFit S dec x) s) x = S x := fittest_correct_of_mem S dec x hi
    have hUs_eq : gaGen (predFit S dec x) (fun _ : Fin P => id) s
        = fun _ : Fin P => fittest (predFit S dec x) s := rfl
    have hdist : hammingDist (gaGen (predFit S dec x) (fun _ : Fin P => id) s)
        (D.perturb t' (gaGen (predFit S dec x) (fun _ : Fin P => id) s)) ≤ P - 1 :=
      le_trans (D.bounded t' _) hrad
    rw [hUs_eq] at hdist
    exact exists_correct_of_hball S dec x hcorrect hdist
  have hv : ∀ s : Pop P C, s ∈ predBasin S dec x → ∀ s' : Pop P C, s' ∈ predBasin S dec x →
      predReading S dec x s = predReading S dec x s' := by
    intro s hs s' hs'
    obtain ⟨i, hi⟩ := hs
    obtain ⟨i', hi'⟩ := hs'
    change dec (fittest (predFit S dec x) s) x = dec (fittest (predFit S dec x) s') x
    rw [fittest_correct_of_mem S dec x hi, fittest_correct_of_mem S dec x hi']
  exact survives_of_invariant (mapsTo_predBasin S dec x) D hD hv
    (mem_predBasin_of_correct S dec x hc) t

end Absorption

/-!
The ten capstones above are `#print axioms`-clean on the standard triple, and the guards below
make that build-enforced.
-/

set_option linter.style.longLine false

/-- info: 'EvoAbsorption.not_nonexpansive_of_gaGen_ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EvoAbsorption.not_nonexpansive_of_gaGen_ne

/-- info: 'EvoAbsorption.nonexpansive_of_gaGen_const' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EvoAbsorption.nonexpansive_of_gaGen_const

/-- info: 'EvoAbsorption.not_corrects_of_faithful' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EvoAbsorption.not_corrects_of_faithful

/-- info: 'EvoAbsorption.margin_yields_max' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EvoAbsorption.margin_yields_max

/-- info: 'EvoAbsorption.not_surjective_of_margin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EvoAbsorption.not_surjective_of_margin

/-- info: 'EvoAbsorption.not_hasMargin_of_faithful' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EvoAbsorption.not_hasMargin_of_faithful

/-- info: 'EvoAbsorption.mapsTo_predBasin' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EvoAbsorption.mapsTo_predBasin

/-- info: 'EvoAbsorption.predFrame_margin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EvoAbsorption.predFrame_margin

/-- info: 'EvoAbsorption.mem_predBasin_of_correct' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms EvoAbsorption.mem_predBasin_of_correct

/-- info: 'EvoAbsorption.predFrame_survives' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EvoAbsorption.predFrame_survives

end EvoAbsorption
