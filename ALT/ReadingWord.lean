/-
Copyright (c) 2026 Mykola Palamarchuk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mykola Palamarchuk
-/
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Group.Finset

-- Formal-check file, not Mathlib-destined: opt out of the house-style header linter.
set_option linter.style.header false

/-!
# Cyclic words along an orbit: the decimation identity and the separating-set floor
([Persistence] §8, Propositions 8.20 and 8.25)

Combinatorics on cyclic words over `ZMod n`, standing alone: no dependence on the persistence
capacity machinery of `ALT/PersistenceCapacity.lean` or `ALT/FrameItinerary.lean`. The bridge from a
world-and-lens pair `(U, ℓ₀)` to a cyclic word `w` along an orbit is NOT built here.

Two counting cores, over a reading's word `w : ZMod n → α`:

* **The decimation identity** ([Persistence] §8, Proposition 8.25(i)): the mismatch set `M_d`, the
  positions where `w` disagrees with its own `d`-shift, is exactly the run boundaries of `w`'s
  `d`-decimation — sampling `w` every `d` steps — at ANY alphabet (`decimation_runs_eq_mismatch`,
  and its prime-cycle corollary `decimation_runs_eq_mismatch_of_prime`). For a binary reading, whose
  runs alternate between the two labels, this gives `m_min = 2 · r(w)` in one further step
  (`runs_eq_two_mul_arcs`, `mMin_eq_two_mul_rMin`) — the identity Proposition 8.25 states, by a
  cleaner route than the case analysis its "runs alternate" phrase suggests (§7).
* **The separating-set floor** ([Persistence] §8, Proposition 8.20's proof, the ceiling half only):
  a set `A` separating every pair `(j, j + d)` embeds `ZMod n` into `A × M_d` by the double count
  `j ↦ (t, j − t)`, giving `n ≤ |A| · |M_d|` for every `d ≠ 0` (`separating_card_le`), hence at the
  minimizing `d` over a prime cycle, `n ≤ |A| · m_min` (`separating_card_le_mMin`). Proposition
  8.20's own decoder — the fixed program recovering `U` from `A`'s frame codes plus an index, and
  the ceiling half of `κ*(w)`'s two-sided bound — is NOT built here: both need `A`'s members read
  as `Fin n`-valued codes and priced against `KE`, machinery this standalone module has no access
  to.
-/

namespace ReadingWord

open Finset

variable {n : ℕ} [NeZero n] {α : Type*} [DecidableEq α]

/-- **The mismatch set at shift `d`** ([Persistence] §8, Proposition 8.20): the positions where the
word disagrees with its own `d`-shift, `M_d := {s : w s ≠ w (s + d)}`. -/
def mismatch (w : ZMod n → α) (d : ZMod n) : Finset (ZMod n) :=
  univ.filter (fun s => w s ≠ w (s + d))

/-- **The `d`-decimation of a word** ([Persistence] §8, Proposition 8.25): the word sampled every
`d` steps, `i ↦ w (i · d)`. -/
def decimate (w : ZMod n → α) (d : ZMod n) : ZMod n → α := fun i => w (i * d)

/-- **The number of runs of a cyclic word**: the positions where a word disagrees with its
successor, at any alphabet. -/
def runs (v : ZMod n → α) : ℕ := (univ.filter (fun i => v i ≠ v (i + 1))).card

/-- **The number of arcs a binary word occupies**: the positions where the word reads `true` and
its predecessor read `false` — the START of a maximal run of `true`s. -/
def arcs (v : ZMod n → Bool) : ℕ := (univ.filter (fun i => v i && !v (i - 1))).card

/-! ### Proposition 8.25(i): the decimation identity -/

/-- **The decimation identity** ([Persistence] §8, Proposition 8.25(i)): at any alphabet, the
mismatch set at shift `d` has the same size as the run count of the `d`-decimation, whenever `d` is
a unit. `i ↦ i * d` is then a bijection of `ZMod n`, and it carries the run boundaries of the
decimation onto `M_d`: `decimate w d i ≠ decimate w d (i + 1)` reads `w (i * d) ≠ w (i * d + d)`,
which is `M_d` read at `i * d`. -/
theorem decimation_runs_eq_mismatch (w : ZMod n → α) {d : ZMod n} (hd : IsUnit d) :
    (mismatch w d).card = runs (decimate w d) := by
  obtain ⟨u, rfl⟩ := hd
  change (mismatch w (u : ZMod n)).card
      = (univ.filter (fun i => decimate w (u : ZMod n) i ≠ decimate w (u : ZMod n) (i + 1))).card
  apply Finset.card_bij' (fun s (_ : s ∈ mismatch w (u : ZMod n)) => s * (↑u⁻¹ : ZMod n))
    (fun i _ => i * (u : ZMod n))
  · intro s hs
    simp only [mismatch, decimate, Finset.mem_filter, Finset.mem_univ, true_and] at hs ⊢
    have h1 : s * (↑u⁻¹ : ZMod n) * ↑u = s := by rw [mul_assoc]; simp
    have h2 : (s * (↑u⁻¹ : ZMod n) + 1) * ↑u = s + ↑u := by rw [add_mul, one_mul, h1]
    rw [h1, h2]
    exact hs
  · intro i hi
    simp only [mismatch, decimate, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    rwa [add_mul, one_mul] at hi
  · intro s _
    rw [mul_assoc]; simp
  · intro i _
    rw [mul_assoc]; simp

private theorem isUnit_of_ne_zero_of_prime [Fact (Nat.Prime n)] {d : ZMod n} (hd : d ≠ 0) :
    IsUnit d := by
  have hp : Nat.Prime n := Fact.out
  have hval_lt : d.val < n := ZMod.val_lt d
  have hval_ne : d.val ≠ 0 := by
    intro h
    apply hd
    rw [← ZMod.natCast_rightInverse d, h]
    simp
  have hndvd : ¬ n ∣ d.val := by
    intro hdvd
    have := Nat.le_of_dvd (Nat.pos_of_ne_zero hval_ne) hdvd
    omega
  have hcop : d.val.Coprime n := (hp.coprime_iff_not_dvd.mpr hndvd).symm
  have hu : IsUnit ((d.val : ℕ) : ZMod n) := (ZMod.isUnit_iff_coprime d.val n).mpr hcop
  rwa [ZMod.natCast_rightInverse d] at hu

/-- **The decimation identity, prime case** ([Persistence] §8, Proposition 8.25(i), the form the
paper states): over a prime cycle every `d ≠ 0` is a unit. -/
theorem decimation_runs_eq_mismatch_of_prime [Fact (Nat.Prime n)] (w : ZMod n → α) {d : ZMod n}
    (hd : d ≠ 0) : (mismatch w d).card = runs (decimate w d) :=
  decimation_runs_eq_mismatch w (isUnit_of_ne_zero_of_prime hd)

private def guardWord : ZMod 4 → Bool := fun i => if i = 0 then true else false

/-- **The unit hypothesis is load-bearing** ([Persistence] §8, Proposition 8.25(i)'s hypothesis):
at `n = 4`, `d = 2` — not a unit, since `2 * 2 = 0` in `ZMod 4` — `w = ![true, false, false, false]`
has `(mismatch w 2).card = 2` while `runs (decimate w 2) = 4`. -/
theorem guard_unit_load_bearing :
    (mismatch guardWord (2 : ZMod 4)).card ≠ runs (decimate guardWord (2 : ZMod 4)) := by
  decide

/-! ### Proposition 8.25(i)'s binary half -/

private def descents (v : ZMod n → Bool) : Finset (ZMod n) :=
  univ.filter (fun i => v i = true ∧ v (i + 1) = false)

private def ascents (v : ZMod n → Bool) : Finset (ZMod n) :=
  univ.filter (fun i => v i = false ∧ v (i + 1) = true)

private theorem runs_eq_descents_add_ascents (v : ZMod n → Bool) :
    runs v = (descents v).card + (ascents v).card := by
  rw [runs, descents, ascents, Finset.card_filter, Finset.card_filter, Finset.card_filter,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  cases v i <;> cases v (i + 1) <;> simp

private theorem descents_card_eq_ascents_card (v : ZMod n → Bool) :
    (descents v).card = (ascents v).card := by
  set T : Finset (ZMod n) := univ.filter (fun i => v i = true) with hT
  set T' : Finset (ZMod n) := univ.filter (fun i => v (i + 1) = true) with hT'
  have h1 : (T.filter (fun i => v (i + 1) = true)).card
      + (T.filter (fun i => ¬ v (i + 1) = true)).card = T.card :=
    Finset.card_filter_add_card_filter_not _
  have h2 : (T'.filter (fun i => v i = true)).card
      + (T'.filter (fun i => ¬ v i = true)).card = T'.card :=
    Finset.card_filter_add_card_filter_not _
  have hTT_eq : T.filter (fun i => v (i + 1) = true) = T'.filter (fun i => v i = true) := by
    ext i
    simp only [hT, hT', Finset.mem_filter, Finset.mem_univ, true_and]
    tauto
  have hD : descents v = T.filter (fun i => ¬ v (i + 1) = true) := by
    ext i
    simp only [descents, hT, Finset.mem_filter, Finset.mem_univ, true_and, Bool.not_eq_true]
  have hA : ascents v = T'.filter (fun i => ¬ v i = true) := by
    ext i
    simp only [ascents, hT', Finset.mem_filter, Finset.mem_univ, true_and, Bool.not_eq_true]
    tauto
  have hinj : Function.Injective (fun j : ZMod n => j - 1) := by
    intro a b hab
    simp only at hab
    have hab' : a - 1 + 1 = b - 1 + 1 := by rw [hab]
    simpa using hab'
  have hTcard : T.card = T'.card := by
    have hTT' : T' = T.image (fun j => j - 1) := by
      ext i
      simp only [hT', hT, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro h
        exact ⟨i + 1, h, by simp⟩
      · rintro ⟨j, hj, rfl⟩
        simpa using hj
    rw [hTT', Finset.card_image_of_injective T hinj]
  rw [← hD] at h1
  rw [← hA] at h2
  rw [hTT_eq, hTcard] at h1
  omega

private theorem ascents_card_eq_arcs (v : ZMod n → Bool) : (ascents v).card = arcs v := by
  rw [arcs]
  apply Finset.card_bij' (fun i (_ : i ∈ ascents v) => i + 1) (fun j _ => j - 1)
  · intro i hi
    simp only [ascents, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, add_sub_cancel_right]
    obtain ⟨h1, h2⟩ := hi
    rw [h2, h1]
    rfl
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    simp only [ascents, Finset.mem_filter, Finset.mem_univ, true_and]
    have hj1 : v j = true := by
      rcases hb : v j with _ | _
      · simp [hb] at hj
      · rfl
    have hj2 : v (j - 1) = false := by
      rcases hb : v (j - 1) with _ | _
      · rfl
      · simp [hb] at hj
    exact ⟨by simpa using hj2, by simpa using hj1⟩
  · intro i _
    simp
  · intro j _
    simp

/-- **Proposition 8.25(i)'s binary half** ([Persistence] §8): a binary word's run count is twice its
arc count — needing no non-constancy hypothesis, since both sides vanish on a constant word. Route:
split the mismatch set into descents and ascents, biject ascents with arcs by `i ↦ i + 1`, and match
descents to ascents by counting each against the shared set of `true` positions from both sides. -/
theorem runs_eq_two_mul_arcs (v : ZMod n → Bool) : runs v = 2 * arcs v := by
  rw [runs_eq_descents_add_ascents, descents_card_eq_ascents_card, ascents_card_eq_arcs]
  omega

/-! ### The statistic identity `m_min = 2 · r(w)` -/

private def univNeZero (n : ℕ) [NeZero n] : Finset (ZMod n) := univ.filter (fun d => d ≠ 0)

omit [NeZero n] in
private theorem exists_ne_zero [Fact (Nat.Prime n)] : ∃ d : ZMod n, d ≠ 0 := by
  refine ⟨1, ?_⟩
  have hp := Fact.out (p := Nat.Prime n)
  haveI : Fact (1 < n) := ⟨hp.one_lt⟩
  exact one_ne_zero

private theorem univNeZero_nonempty [Fact (Nat.Prime n)] : (univNeZero n).Nonempty := by
  obtain ⟨d, hd⟩ := exists_ne_zero (n := n)
  exact ⟨d, by simp [univNeZero, hd]⟩

/-- **`m_min`** ([Persistence] §8, Proposition 8.20): the least Hamming self-distance of the word,
`min_{d ≠ 0} |M_d|`, taken with `Finset.inf'` over an explicit nonemptiness proof rather than
`sInf`, whose value on a degenerate set would not be the intended minimum. -/
def mMin [Fact (Nat.Prime n)] (w : ZMod n → α) : ℕ :=
  (univNeZero n).inf' univNeZero_nonempty (fun d => (mismatch w d).card)

/-- **`r(w)`** ([Persistence] §8, Proposition 8.25): the least number of arcs occupied by any
decimation of the word, `min_{d ≠ 0} arcs (decimate w d)`. -/
def rMin [Fact (Nat.Prime n)] (w : ZMod n → Bool) : ℕ :=
  (univNeZero n).inf' univNeZero_nonempty (fun d => arcs (decimate w d))

/-- **The statistic identity** ([Persistence] §8, Proposition 8.25(i) at the minimizing `d`):
`m_min = 2 · r(w)`. Primality is what makes every `d ≠ 0` a unit, so `decimation_runs_eq_mismatch`
applies pointwise at each `d`; the minima then agree because `n • ·` (here `2 • ·`) commutes with a
finite `inf'` (`Finset.nsmul_inf'`). -/
theorem mMin_eq_two_mul_rMin [Fact (Nat.Prime n)] (w : ZMod n → Bool) : mMin w = 2 * rMin w := by
  rw [mMin, rMin, ← smul_eq_mul, Finset.nsmul_inf']
  apply Finset.inf'_congr univNeZero_nonempty rfl
  intro d hd
  simp only [univNeZero, Finset.mem_filter, Finset.mem_univ, true_and] at hd
  rw [decimation_runs_eq_mismatch_of_prime w hd, runs_eq_two_mul_arcs, smul_eq_mul]

/-! ### Proposition 8.20's floor: separating sets -/

/-- **A separating set** ([Persistence] §8, Proposition 8.20): `A` separates every pair `j`,
`j + t` for `t ∈ A` when the pattern map `j ↦ (w (j − t))_{t ∈ A}` is injective. -/
def Separating (w : ZMod n → α) (A : Finset (ZMod n)) : Prop :=
  Function.Injective (fun j : ZMod n => fun t : ↥A => w (j - t))

/-- **The separating-set floor** ([Persistence] §8, Proposition 8.20's proof, the double count):
for any `d ≠ 0`, a separating set embeds `ZMod n` into `A × M_d`. `A` separates `j` from `j + d`
exactly when some `t ∈ A` has `j − t ∈ M_d`, so `j ↦ (t, j − t)` is well defined onto `A × M_d` and
surjective, giving `n ≤ |A| · |M_d|`. -/
theorem separating_card_le {w : ZMod n → α} {A : Finset (ZMod n)} (hA : Separating w A)
    {d : ZMod n} (hd : d ≠ 0) : n ≤ A.card * (mismatch w d).card := by
  have hsurj : Function.Surjective
      (fun p : ↥A × ↥(mismatch w d) => (p.1 : ZMod n) + (p.2 : ZMod n)) := by
    intro j
    have hne : j ≠ j + d := by
      intro h
      apply hd
      have h' : j + 0 = j + d := by rw [add_zero]; exact h
      exact (add_left_cancel h').symm
    have hdiff : (fun t : ↥A => w (j - (t : ZMod n)))
        ≠ (fun t : ↥A => w ((j + d) - (t : ZMod n))) := fun heq => hne (hA heq)
    obtain ⟨t, ht⟩ := Function.ne_iff.mp hdiff
    have hjd : (j + d) - (t : ZMod n) = (j - (t : ZMod n)) + d := by
      simp [sub_eq_add_neg, add_comm, add_assoc]
    rw [hjd] at ht
    have hmem : (j - (t : ZMod n)) ∈ mismatch w d := by
      simp only [mismatch, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ht
    exact ⟨(t, ⟨j - (t : ZMod n), hmem⟩), by simp⟩
  calc n = Fintype.card (ZMod n) := (ZMod.card n).symm
    _ ≤ Fintype.card (↥A × ↥(mismatch w d)) := Fintype.card_le_of_surjective _ hsurj
    _ = A.card * (mismatch w d).card := by
        rw [Fintype.card_prod, Fintype.card_coe, Fintype.card_coe]

/-- **The floor at the minimizing `d`** ([Persistence] §8, Proposition 8.20, the `m_min` form):
over a prime cycle, `separating_card_le` holds at every `d ≠ 0`, so it holds in particular at the
`d` achieving `mMin w`. -/
theorem separating_card_le_mMin [Fact (Nat.Prime n)] {w : ZMod n → α} {A : Finset (ZMod n)}
    (hA : Separating w A) : n ≤ A.card * mMin w := by
  obtain ⟨d, hdmem, hdeq⟩ :=
    Finset.exists_mem_eq_inf' univNeZero_nonempty (fun d => (mismatch w d).card)
  have hdne : d ≠ 0 := by simpa [univNeZero] using hdmem
  rw [mMin, hdeq]
  exact separating_card_le hA hdne

end ReadingWord

/-! ## Axiom audit

The six capstones above are `#print axioms`-clean on the standard triple, and the guards below
make that build-enforced. -/

set_option linter.style.longLine false

/-- info: 'ReadingWord.decimation_runs_eq_mismatch' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReadingWord.decimation_runs_eq_mismatch

/-- info: 'ReadingWord.decimation_runs_eq_mismatch_of_prime' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReadingWord.decimation_runs_eq_mismatch_of_prime

/-- info: 'ReadingWord.runs_eq_two_mul_arcs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReadingWord.runs_eq_two_mul_arcs

/-- info: 'ReadingWord.mMin_eq_two_mul_rMin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReadingWord.mMin_eq_two_mul_rMin

/-- info: 'ReadingWord.separating_card_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReadingWord.separating_card_le

/-- info: 'ReadingWord.separating_card_le_mMin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReadingWord.separating_card_le_mMin
