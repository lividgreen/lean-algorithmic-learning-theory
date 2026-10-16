module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.Group.Finset
public import Mathlib.Tactic.Ring


/-!
# Cyclic words along an orbit: the decimation identity and the separating-set floor
([Persistence] §8, Propositions 8.20 and 8.25)

Combinatorics on cyclic words over `ZMod n`, standing alone: no dependence on the persistence
capacity machinery of `ALT/PersistenceCapacity.lean` or `ALT/FrameItinerary.lean`. The bridge from a
world-and-lens pair `(U, ℓ₀)` to a cyclic word `w` along an orbit is NOT built here.

Two counting cores, over a reading's word `w : ZMod n → α`:

* **The decimation identity** ([Persistence] §8, Proposition 8.25(i), and at every shift
  Proposition 8.32): the mismatch set `M_d`, the positions where `w` disagrees with its own
  `d`-shift, is exactly the run boundaries of `w`'s `d`-decimation — sampling `w` every `d` steps —
  at ANY alphabet (`decimation_runs_eq_mismatch`, and its prime-cycle corollary
  `decimation_runs_eq_mismatch_of_prime`), whenever `d` is a unit. At an arbitrary shift, averaging
  over every starting point of the decimation clears the hypothesis entirely:
  `sum_runs_decimateFrom` gives `∑ a, runs (decimateFrom w d a) = n * |M_d|` with no condition on
  `d` at all — not `IsUnit`, not `d ≠ 0` — and `decimation_runs_eq_mismatch` is recovered from it by
  `n`-cancellation once every term in that sum is shown equal (which a unit `d` forces). For a
  binary reading, whose runs
  alternate between the two labels, this gives `m_min = 2 · r(w)` in one further step
  (`runs_eq_two_mul_arcs`, `mMin_eq_two_mul_rMin`) — the identity Proposition 8.25 states, by a
  cleaner route than the case analysis its "runs alternate" phrase suggests (§7) — and the averaged
  binary form and general-`n` statistic identity (`sum_arcs_decimateFrom`,
  `mMin_eq_two_mul_rMinGen`) likewise need no unit hypothesis.
* **The separating-set floor** ([Persistence] §8, Proposition 8.20's proof, the ceiling half only):
  a set `A` separating every pair `(j, j + d)` embeds `ZMod n` into `A × M_d` by the double count
  `j ↦ (t, j − t)`, giving `n ≤ |A| · |M_d|` for every `d ≠ 0` (`Separating.card_le`), hence at the
  minimizing `d` over a prime cycle, `n ≤ |A| · m_min` (`Separating.card_le_mMin`). The pattern map
  itself gives a second, cruder floor by a straight pigeonhole into `↥A → α`, `n ≤ |α| ^ |A|`
  ([Persistence] §8, Proposition 8.40(ii)'s second bound — `Separating.card_pow_le`). Proposition
  8.20's own decoder — the fixed program recovering `U` from `A`'s frame codes plus an index, and
  the ceiling half of `κ*(w)`'s two-sided bound — is NOT built here: both need `A`'s members read
  as `Fin n`-valued codes and priced against `KE`, machinery this standalone module has no access
  to.

Decimation composes ([Persistence] §8, Proposition 8.42(ii)'s route): `decimate (decimate w d) e =
decimate w (d * e)` (`decimate_decimate`) and `decimate w 1 = w` (`decimate_one`). Consequently,
over a prime cycle, `rMin` of a `d`-decimation is at most the original word's own arc count
(`rMin_decimate_le`) — undo the sampling at `d⁻¹` — which is the mechanism behind Proposition
8.42(ii)'s negative half: the arc count a pattern DISPLAYS is not the statistic `r(w)` a reading is
priced against, since a further decimation can collapse it back down
(`guard_arc_pattern_not_rMin`, a concrete decimated interval at `n = 11`).
-/


@[expose] public section

namespace ALT

open Finset

variable {n : ℕ} [NeZero n] {α : Type*} [DecidableEq α]

/-- **The mismatch set at shift `d`** ([Persistence] §8, Proposition 8.20): the positions where the
word disagrees with its own `d`-shift, `M_d := {s : w s ≠ w (s + d)}`. -/
def mismatch (w : ZMod n → α) (d : ZMod n) : Finset (ZMod n) :=
  univ.filter (fun s => w s ≠ w (s + d))

/-- **The `d`-decimation of a word** ([Persistence] §8, Proposition 8.25): the word sampled every
`d` steps, `i ↦ w (i · d)`. -/
def decimate (w : ZMod n → α) (d : ZMod n) : ZMod n → α := fun i => w (i * d)

/-- **The `d`-decimation started at `a`** ([Persistence] §8, Proposition 8.32): the walk
`i ↦ w (a + i · d)` — `decimate` is the case `a = 0` (`decimate_eq_decimateFrom_zero`). Averaging
the run count of `decimateFrom w d a` over every starting point `a` is what lets the decimation
identity drop its unit hypothesis on `d` (`sum_runs_decimateFrom`). -/
def decimateFrom (w : ZMod n → α) (d a : ZMod n) : ZMod n → α := fun i => w (a + i * d)

omit [NeZero n] [DecidableEq α] in
/-- **`decimate` is `decimateFrom` started at `0`.** -/
theorem decimate_eq_decimateFrom_zero (w : ZMod n → α) (d : ZMod n) :
    decimate w d = decimateFrom w d 0 := by
  funext i
  simp [decimate, decimateFrom]

omit [NeZero n] [DecidableEq α] in
/-- **Decimation composes by multiplying shifts** ([Persistence] §8, Proposition 8.42(ii)'s route):
sampling every `e` steps of a word already sampled every `d` steps is sampling every `d · e` steps
of the original, `decimate (decimate w d) e = decimate w (d * e)`. -/
theorem decimate_decimate (w : ZMod n → α) (d e : ZMod n) :
    decimate (decimate w d) e = decimate w (d * e) := by
  funext i
  simp only [decimate]
  congr 1
  ring

omit [NeZero n] [DecidableEq α] in
/-- **Decimating at shift `1` changes nothing.** -/
theorem decimate_one (w : ZMod n → α) : decimate w 1 = w := by
  funext i
  simp [decimate]

/-- **The number of runs of a cyclic word**: the positions where a word disagrees with its
successor, at any alphabet. -/
def runs (v : ZMod n → α) : ℕ := (univ.filter (fun i => v i ≠ v (i + 1))).card

/-- **The number of arcs a binary word occupies**: the positions where the word reads `true` and
its predecessor read `false` — the START of a maximal run of `true`s. -/
def arcs (v : ZMod n → Bool) : ℕ := (univ.filter (fun i => v i && !v (i - 1))).card

/-! ### Proposition 8.32: the decimation identity at every shift, and Proposition 8.25(i) as its
unit-shift corollary -/

/-- **Run count is invariant under an additive reindexing of the domain** — a basic fact about
`runs` with no connection to decimation, used to show `decimateFrom w d a` has the same run count
for every starting point `a`, at a unit shift. -/
private theorem runs_comp_add_const (v : ZMod n → α) (c : ZMod n) :
    runs (fun i => v (i + c)) = runs v := by
  apply Finset.card_bij' (fun i (_ : i ∈ univ.filter (fun i => v (i + c) ≠ v (i + 1 + c))) => i + c)
    (fun j _ => j - c)
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    have h : i + c + 1 = i + 1 + c := by ring
    rwa [h]
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
    have h1 : j - c + c = j := by ring
    have h2 : j - c + 1 + c = j + 1 := by ring
    rwa [h1, h2]
  · intro i _; ring
  · intro j _; ring

/-- **The averaged decimation identity, at every shift** ([Persistence] §8, Proposition 8.32): no
hypothesis on `d` at all — not `IsUnit`, not `d ≠ 0`. Route: expand both `runs` and `mismatch` as
`Finset.card` of filters, i.e. sums of `0`/`1` indicators; swap the order of summation over `a` and
`i`; and for each fixed `i`, the map `a ↦ a + i * d` is a bijection of `ZMod n` (`Equiv.addRight`),
so the inner sum over `a` collapses to `|M_d|` independent of `i`, leaving `n` copies. -/
theorem sum_runs_decimateFrom (w : ZMod n → α) (d : ZMod n) :
    ∑ a : ZMod n, runs (decimateFrom w d a) = n * (mismatch w d).card := by
  have key : ∀ a : ZMod n, runs (decimateFrom w d a)
      = ∑ i : ZMod n, if w (a + i * d) ≠ w (a + i * d + d) then 1 else 0 := by
    intro a
    rw [runs, Finset.card_filter]
    apply Finset.sum_congr rfl
    intro i _
    have heq : a + (i + 1) * d = a + i * d + d := by ring
    simp only [decimateFrom, heq]
  rw [Finset.sum_congr rfl (fun a _ => key a), Finset.sum_comm]
  have hcol : ∀ i : ZMod n, ∑ a : ZMod n, (if w (a + i * d) ≠ w (a + i * d + d) then 1 else 0)
      = (mismatch w d).card := by
    intro i
    rw [mismatch, Finset.card_filter]
    exact Fintype.sum_equiv (Equiv.addRight (i * d)) _ _ (fun a => rfl)
  rw [Finset.sum_congr rfl (fun i _ => hcol i), Finset.sum_const, Finset.card_univ, ZMod.card,
    smul_eq_mul]

omit [NeZero n] [DecidableEq α] in
/-- At a unit shift, the walk `i ↦ a + i * d` started at any `a` is a reindexing of the walk
started at `b`, by the constant `(a - b) * d⁻¹`: `a + i * d = b + (i + (a - b) * d⁻¹) * d`. -/
private theorem decimateFrom_reindex (w : ZMod n → α) {d : ZMod n} (hd : IsUnit d) (a b : ZMod n) :
    ∃ c : ZMod n, ∀ i, decimateFrom w d a i = decimateFrom w d b (i + c) := by
  obtain ⟨u, rfl⟩ := hd
  refine ⟨(a - b) * (↑u⁻¹ : ZMod n), fun i => ?_⟩
  simp only [decimateFrom]
  congr 1
  have hcancel : (a - b) * (↑u⁻¹ : ZMod n) * ↑u = a - b := by
    rw [mul_assoc]; simp
  have hexpand : (i + (a - b) * (↑u⁻¹ : ZMod n)) * ↑u
      = i * ↑u + (a - b) * (↑u⁻¹ : ZMod n) * ↑u := by ring
  rw [hexpand, hcancel]
  ring

/-- **At a unit shift, `runs (decimateFrom w d a)` does not depend on `a`.** Combined with
`sum_runs_decimateFrom`, this is what recovers `decimation_runs_eq_mismatch` by `n`-cancellation. -/
private theorem runs_decimateFrom_const_of_isUnit (w : ZMod n → α) {d : ZMod n} (hd : IsUnit d)
    (a b : ZMod n) : runs (decimateFrom w d a) = runs (decimateFrom w d b) := by
  obtain ⟨c, hc⟩ := decimateFrom_reindex w hd a b
  have heq : decimateFrom w d a = fun i => decimateFrom w d b (i + c) := funext hc
  rw [heq]
  exact runs_comp_add_const (decimateFrom w d b) c

/-- **The decimation identity** ([Persistence] §8, Proposition 8.25(i)): at any alphabet, the
mismatch set at shift `d` has the same size as the run count of the `d`-decimation, whenever `d` is
a unit — the `gcd (d, n) = 1` instance of Proposition 8.32's general form. At a unit shift,
`runs (decimateFrom w d a)` is the same for every `a` (`runs_decimateFrom_const_of_isUnit`), so
`sum_runs_decimateFrom`'s sum is `n` copies of `runs (decimate w d)` (`decimateFrom` at `a = 0`),
and `n ≠ 0` cancels against the `n * |M_d|` on the other side. -/
theorem decimation_runs_eq_mismatch (w : ZMod n → α) {d : ZMod n} (hd : IsUnit d) :
    (mismatch w d).card = runs (decimate w d) := by
  have hconst : ∀ a : ZMod n, runs (decimateFrom w d a) = runs (decimateFrom w d 0) :=
    fun a => runs_decimateFrom_const_of_isUnit w hd a 0
  have hsum := sum_runs_decimateFrom w d
  rw [Finset.sum_congr rfl (fun a _ => hconst a), Finset.sum_const, Finset.card_univ, ZMod.card,
    smul_eq_mul] at hsum
  have heq : runs (decimateFrom w d 0) = (mismatch w d).card :=
    Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero (NeZero.ne n)) hsum
  rw [decimate_eq_decimateFrom_zero]
  exact heq.symm

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

/-- The `n = 4` guard word: `true` at `0`, `false` elsewhere. -/
def guardWord : ZMod 4 → Bool := fun i => if i = 0 then true else false

/-- **The unit hypothesis is load-bearing** ([Persistence] §8, Proposition 8.25(i)'s hypothesis):
at `n = 4`, `d = 2` — not a unit, since `2 * 2 = 0` in `ZMod 4` — `w = ![true, false, false, false]`
has `(mismatch w 2).card = 2` while `runs (decimate w 2) = 4`. -/
theorem guard_unit_load_bearing :
    (mismatch guardWord (2 : ZMod 4)).card ≠ runs (decimate guardWord (2 : ZMod 4)) := by
  decide

/-- **The naive single-decimation binary reading is what a composite length breaks, not the
identity itself** ([Persistence] §8, Proposition 8.32's point): at the same `n = 4`, `d = 2`
witness, `(mismatch guardWord 2).card = 2` while `2 * arcs (decimate guardWord 2) = 4` — the
`m_min = 2 · r(w)` display fails when `r(w)` is read off a single decimation, exactly as
`guard_unit_load_bearing` shows the run-count identity itself fails there; `sum_arcs_decimateFrom`'s
averaged form is what survives at this shift. -/
theorem guard_composite_binary_load_bearing :
    (mismatch guardWord (2 : ZMod 4)).card ≠ 2 * arcs (decimate guardWord (2 : ZMod 4)) := by
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

/-- **The averaged binary form, at every shift** ([Persistence] §8, Proposition 8.32's binary
half): off `sum_runs_decimateFrom` and `runs_eq_two_mul_arcs` applied pointwise at each starting
point `a`, with no hypothesis on `d`. Stated multiplicatively — `n * |M_d| = 2 * ∑ …` rather than
dividing by `n` — so the one display the paper quotes carries no `ℕ`-division wart. -/
theorem sum_arcs_decimateFrom (w : ZMod n → Bool) (d : ZMod n) :
    n * (mismatch w d).card = 2 * ∑ a : ZMod n, arcs (decimateFrom w d a) := by
  rw [← sum_runs_decimateFrom w d, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  exact runs_eq_two_mul_arcs (decimateFrom w d a)

/-! ### The statistic identity `m_min = 2 · r(w)`, at every `n > 1`, and `mMin_eq_two_mul_rMin` as
its prime corollary -/

/-- The nonzero elements of `ZMod n`, as a `Finset`. -/
def univNeZero (n : ℕ) [NeZero n] : Finset (ZMod n) := univ.filter (fun d => d ≠ 0)

omit [NeZero n] in
private theorem exists_ne_zero [Fact (1 < n)] : ∃ d : ZMod n, d ≠ 0 :=
  ⟨1, one_ne_zero⟩

/-- `univNeZero n` is nonempty when `1 < n`. -/
theorem univNeZero_nonempty [Fact (1 < n)] : (univNeZero n).Nonempty := by
  obtain ⟨d, hd⟩ := exists_ne_zero (n := n)
  exact ⟨d, by simp [univNeZero, hd]⟩

/-- **`m_min`**, at any `n > 1` ([Persistence] §8, Proposition 8.20): the least Hamming
self-distance of the word, `min_{d ≠ 0} |M_d|`, taken with `Finset.inf'` over an explicit
nonemptiness proof rather than `sInf`, whose value on a degenerate set would not be the intended
minimum. Needs only `n > 1`, not primality: nonemptiness of the `d ≠ 0` index set is all
`Finset.inf'` asks for. -/
def mMin [Fact (1 < n)] (w : ZMod n → α) : ℕ :=
  (univNeZero n).inf' univNeZero_nonempty (fun d => (mismatch w d).card)

/-- **`r(w)`, averaged over every decimation's starting point** ([Persistence] §8, Proposition 8.32
at the minimizing `d`): `min_{d ≠ 0} ∑ a, arcs (decimateFrom w d a)`, at any `n > 1`. -/
def rMinGen [Fact (1 < n)] (w : ZMod n → Bool) : ℕ :=
  (univNeZero n).inf' univNeZero_nonempty (fun d => ∑ a : ZMod n, arcs (decimateFrom w d a))

/-- **`r(w)`, over a prime cycle** ([Persistence] §8, Proposition 8.25): the least number of arcs
occupied by any SINGLE decimation of the word, `min_{d ≠ 0} arcs (decimate w d)` — meaningful as the
paper's `r(w)` only where every `d ≠ 0` is a unit, since `guard_composite_binary_load_bearing` shows
a single decimation is not faithful at a composite length; `rMinGen` is the statistic that survives
there. `[Fact (Nat.Prime n)]` supplies `[Fact (1 < n)]` for `univNeZero_nonempty` automatically, via
Mathlib's `Nat.Prime.one_lt'`. -/
def rMin [Fact (Nat.Prime n)] (w : ZMod n → Bool) : ℕ :=
  (univNeZero n).inf' univNeZero_nonempty (fun d => arcs (decimate w d))

/-- **The general statistic identity** ([Persistence] §8, Proposition 8.32 at the minimizing `d`):
`n · m_min = 2 · r(w)`, averaged over decimations' starting points, at any `n > 1` — no unit
hypothesis on the minimizing `d`, unlike `mMin_eq_two_mul_rMin`. Route: `sum_arcs_decimateFrom`
supplies the pointwise identity `n * |M_d| = 2 * ∑ a, arcs (decimateFrom w d a)` at every `d`;
`n • ·` and `2 • ·` each commute with a finite `inf'` (`Finset.nsmul_inf'`), so the two minima
agree. -/
theorem mMin_eq_two_mul_rMinGen [Fact (1 < n)] (w : ZMod n → Bool) :
    n * mMin w = 2 * rMinGen w := by
  rw [mMin, rMinGen, ← smul_eq_mul, ← smul_eq_mul, Finset.nsmul_inf', Finset.nsmul_inf']
  apply Finset.inf'_congr univNeZero_nonempty rfl
  intro d hd
  simp only [univNeZero, Finset.mem_filter, Finset.mem_univ, true_and] at hd
  rw [smul_eq_mul, smul_eq_mul]
  exact sum_arcs_decimateFrom w d

/-- **The statistic identity, over a prime cycle** ([Persistence] §8, Proposition 8.25(i) at the
minimizing `d`): `m_min = 2 · r(w)`. Primality is what makes every `d ≠ 0` a unit, so
`decimation_runs_eq_mismatch` applies pointwise at each `d`; the minima then agree because `n • ·`
(here `2 • ·`) commutes with a finite `inf'` (`Finset.nsmul_inf'`). -/
theorem mMin_eq_two_mul_rMin [Fact (Nat.Prime n)] (w : ZMod n → Bool) : mMin w = 2 * rMin w := by
  rw [mMin, rMin, ← smul_eq_mul, Finset.nsmul_inf']
  apply Finset.inf'_congr univNeZero_nonempty rfl
  intro d hd
  simp only [univNeZero, Finset.mem_filter, Finset.mem_univ, true_and] at hd
  rw [decimation_runs_eq_mismatch_of_prime w hd, runs_eq_two_mul_arcs, smul_eq_mul]

/-! ### Proposition 8.42(ii): a decimated pattern's own minimizing decimation can undo it -/

/-- **A cheap-looking decimation can hide a cheaper one** ([Persistence] §8, Proposition 8.42(ii)):
`rMin` of a `d`-decimation is at most the word's own arc count. Route: write `d` as a unit `u`
(`isUnit_of_ne_zero_of_prime`), instantiate `rMin`'s `inf'` at `↑u⁻¹`, and undo the sampling via
`decimate_decimate` and `decimate_one`, using `u * ↑u⁻¹ = 1`. This is the mechanism behind
Proposition 8.42(ii)'s negative half: the arc count of a *pattern* is not `r(w)`, since decimating
it again can collapse it back to fewer arcs. -/
theorem rMin_decimate_le [Fact (Nat.Prime n)] (w : ZMod n → Bool) {d : ZMod n} (hd : d ≠ 0) :
    rMin (decimate w d) ≤ arcs w := by
  obtain ⟨u, rfl⟩ := isUnit_of_ne_zero_of_prime hd
  have hune : (↑u⁻¹ : ZMod n) ≠ 0 := Units.ne_zero _
  have hmem : (↑u⁻¹ : ZMod n) ∈ univNeZero n := by simp [univNeZero, hune]
  have hle : rMin (decimate w (u : ZMod n))
      ≤ arcs (decimate (decimate w (u : ZMod n)) (↑u⁻¹ : ZMod n)) :=
    Finset.inf'_le _ hmem
  have hcancel : (u : ZMod n) * (↑u⁻¹ : ZMod n) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have heq : decimate (decimate w (u : ZMod n)) (↑u⁻¹ : ZMod n) = w := by
    rw [decimate_decimate, hcancel, decimate_one]
  rwa [heq] at hle

/-- **A concrete decimated interval, at the arc count the pattern displays versus the arc count
its own decimation reveals** ([Persistence] §8, Proposition 8.42(ii)): at `n = 11` (prime), the
interval indicator `v := 1_{[0, 5)}` has `arcs v = 1`, while its `3`-decimation `u := decimate v 3`
reads `arcs u = 3` — three arcs by direct count — yet `rMin u = 1`, since `u`'s own `3⁻¹`-decimation
undoes the sampling and recovers `v`. So the arc count a pattern DISPLAYS is not the statistic
`r(w)` a reading is priced against; `rMin_decimate_le` is exactly why `rMin u ≤ arcs v = 1`. -/
theorem guard_arc_pattern_not_rMin :
    haveI : Fact (Nat.Prime 11) := ⟨by decide⟩
    arcs (decimate (fun i : ZMod 11 => decide (i.val < 5)) (3 : ZMod 11)) = 3 ∧
      rMin (decimate (fun i : ZMod 11 => decide (i.val < 5)) (3 : ZMod 11)) = 1 := by
  have : Fact (Nat.Prime 11) := ⟨by decide⟩
  exact ⟨by decide, by decide⟩

/-! ### Proposition 8.20's floor: separating sets -/

/-- **A separating set** ([Persistence] §8, Proposition 8.20): `A` separates every pair `j`,
`j + t` for `t ∈ A` when the pattern map `j ↦ (w (j − t))_{t ∈ A}` is injective. -/
def Separating (w : ZMod n → α) (A : Finset (ZMod n)) : Prop :=
  Function.Injective (fun j : ZMod n => fun t : ↥A => w (j - t))

/-- **The separating-set floor** ([Persistence] §8, Proposition 8.20's proof, the double count):
for any `d ≠ 0`, a separating set embeds `ZMod n` into `A × M_d`. `A` separates `j` from `j + d`
exactly when some `t ∈ A` has `j − t ∈ M_d`, so `j ↦ (t, j − t)` is well defined onto `A × M_d` and
surjective, giving `n ≤ |A| · |M_d|`. -/
theorem Separating.card_le {w : ZMod n → α} {A : Finset (ZMod n)} (hA : Separating w A)
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

omit [DecidableEq α] in
/-- **The counting floor: a separating set is a pigeonhole on the pattern map** ([Persistence] §8,
Proposition 8.40(ii)'s second bound): `Separating` is injectivity of the pattern map
`j ↦ (w (j − t))_{t ∈ A}` into `↥A → α`, so `n ≤ |α| ^ |A|` by a straight cardinality comparison —
no double count needed, unlike `Separating.card_le`. -/
theorem Separating.card_pow_le [Fintype α] {w : ZMod n → α} {A : Finset (ZMod n)}
    (hA : Separating w A) : n ≤ Fintype.card α ^ A.card := by
  have hcard := Fintype.card_le_of_injective _ hA
  rwa [Fintype.card_fun, Fintype.card_coe, ZMod.card] at hcard

/-- **The floor at the minimizing `d`** ([Persistence] §8, Proposition 8.20, the `m_min` form):
over a prime cycle, `Separating.card_le` holds at every `d ≠ 0`, so it holds in particular at the
`d` achieving `mMin w`. -/
theorem Separating.card_le_mMin [Fact (Nat.Prime n)] {w : ZMod n → α} {A : Finset (ZMod n)}
    (hA : Separating w A) : n ≤ A.card * mMin w := by
  obtain ⟨d, hdmem, hdeq⟩ :=
    Finset.exists_mem_eq_inf' univNeZero_nonempty (fun d => (mismatch w d).card)
  have hdne : d ≠ 0 := by simpa [univNeZero] using hdmem
  rw [mMin, hdeq]
  exact Separating.card_le hA hdne

end ALT

/-! ## Axiom audit

The guarded capstones above are `#print axioms`-clean on the standard triple, and the guards
below make that build-enforced. -/


/-- info: 'ALT.decimate_decimate' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.decimate_decimate

/-- info: 'ALT.decimate_one' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.decimate_one

/-- info: 'ALT.sum_runs_decimateFrom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.sum_runs_decimateFrom

set_option linter.style.longLine false in
/-- info: 'ALT.decimation_runs_eq_mismatch' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.decimation_runs_eq_mismatch

set_option linter.style.longLine false in
/-- info: 'ALT.decimation_runs_eq_mismatch_of_prime' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.decimation_runs_eq_mismatch_of_prime

/-- info: 'ALT.runs_eq_two_mul_arcs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.runs_eq_two_mul_arcs

/-- info: 'ALT.sum_arcs_decimateFrom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.sum_arcs_decimateFrom

set_option linter.style.longLine false in
/-- info: 'ALT.mMin_eq_two_mul_rMinGen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.mMin_eq_two_mul_rMinGen

/-- info: 'ALT.mMin_eq_two_mul_rMin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.mMin_eq_two_mul_rMin

/-- info: 'ALT.rMin_decimate_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.rMin_decimate_le

/-- info: 'ALT.Separating.card_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.Separating.card_le

/-- info: 'ALT.Separating.card_pow_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.Separating.card_pow_le

set_option linter.style.longLine false in
/-- info: 'ALT.Separating.card_le_mMin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.Separating.card_le_mMin
