/-
Copyright (c) 2026 Mykola Palamarchuk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mykola Palamarchuk
-/
module

public import ALT.WeightedFiber

-- Formal-check file, not Mathlib-destined: opt out of the house-style header linter.
set_option linter.style.header false

/-!
# The quantization rate ([Inevitability] §6)

`WeightedFiber.weighted_fiber_not_exactly_bayes` shows the carrier projection is not the identity:
on a two-candidate, budget-`2` instance the projected step discards an entire update the exact
replicator step would have made. This file answers the question that boundary opened — in what
sense, and how fast, does the finite fiber *approach* the exact Bayes run?

## Main results

* `bayesRun` / `wRun` — the exact and finite replicator **runs**, `n` generations under a varying
  fitness `F : ℕ → Fin C → ℕ` (one likelihood per step, as the real fiber receives).
* `raw_wRun_eq_bayesRun` / `toDist_wRun_eq_bayes` — **the exactness horizon**: while the fitness
  ceiling's `n`-th power stays inside the budget, the finite run does not approximate the exact
  run, it *is* it, because the projection has nothing to do. `wRun_ne_bayesRun_witness` shows the
  horizon is sharp: at `W = 2` the runs have already diverged by step `2`.
* `l1_normalize_le` — a general fact about ℚ-valued normalization, reusable outside this file: the
  L¹ distance between two normalized nonnegative vectors is controlled by the L¹ distance of the
  vectors themselves, over the second one's mass.
* `toDist_project_close` / `toDist_project_rate` / `wGen_bayes_rate` — **the per-step residual
  rate**: past the horizon, one projected generation stays within `O(C/W)` of the exact Bayes
  posterior in total variation.

## Scope

The rate bounds one generation against the exact posterior it approximates; it does **not**
telescope into a bound on `n` generations run against `n` generations of Bayes, because Bayesian
update is not non-expansive in total variation. A multi-step accumulation and a sharper
miss-count-based rate (the rescale is free when candidates agree; the floor only bites on
candidates already below one quantum) are both left open.
-/


@[expose] public section

namespace WeightedFiber

/-! ## The exactness horizon -/

section ExactnessHorizon

variable {C : ℕ}

/-- The **exact** replicator run: no carrier, no projection, weights free to grow. Step `n`
receives the fitness `F n`, so the run tracks a base trajectory feeding a different likelihood
into each generation, as the real fiber does. -/
def bayesRun (F : ℕ → Fin C → ℕ) : ℕ → (Fin C → ℕ)
  | 0 => fun _ => 1
  | n + 1 => bayesStep (F n) (bayesRun F n)

/-- The **finite** run: one projected `wGen` generation per step, under the same varying
fitness. -/
def wRun (W : ℕ) (F : ℕ → Fin C → ℕ) : ℕ → WVec C W
  | 0 => pack W (fun _ => 1)
  | n + 1 => wGen W (F n) (wRun W F n)

private theorem bayesRun_bounds {κ : ℕ} (F : ℕ → Fin C → ℕ) (hF1 : ∀ n i, 1 ≤ F n i)
    (hFκ : ∀ n i, F n i ≤ κ) (n : ℕ) (i : Fin C) :
    1 ≤ bayesRun F n i ∧ bayesRun F n i ≤ κ ^ n := by
  induction n with
  | zero => exact ⟨le_refl 1, by simp [bayesRun]⟩
  | succ n ih =>
      obtain ⟨ih1, ih2⟩ := ih
      have h1 := hF1 n i
      refine ⟨?_, ?_⟩
      · change 1 ≤ bayesStep (F n) (bayesRun F n) i
        rw [bayesStep]
        exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
      · change bayesStep (F n) (bayesRun F n) i ≤ κ ^ (n + 1)
        rw [bayesStep, pow_succ]
        exact Nat.mul_le_mul ih2 (hFκ n i)

/-- **The exactness horizon**: while the fitness ceiling's `n`-th power stays inside the budget,
the finite run is not merely *close to* the exact one, it is *equal* to it — the carrier
projection has nothing to do, because the exact vector already fits. `κ` bounds the per-step
fitness; `predFitPos` uses `κ = 2`. -/
theorem raw_wRun_eq_bayesRun {W κ : ℕ} (hW : 1 ≤ W) (F : ℕ → Fin C → ℕ)
    (hF1 : ∀ n i, 1 ≤ F n i) (hFκ : ∀ n i, F n i ≤ κ) :
    ∀ n : ℕ, κ ^ n ≤ W → raw (wRun W F n) = bayesRun F n := by
  rcases Nat.eq_zero_or_pos C with hC0 | hCpos
  · intro n _
    funext i
    exact absurd i.2 (by omega)
  · obtain ⟨i₀⟩ : Nonempty (Fin C) := ⟨⟨0, hCpos⟩⟩
    have hκ : 0 < κ := lt_of_lt_of_le (hF1 0 i₀) (hFκ 0 i₀)
    intro n
    induction n with
    | zero =>
        intro _
        funext i
        change raw (pack W (fun _ => (1 : ℕ))) i = 1
        rw [raw, pack]
        exact min_eq_left hW
    | succ n ih =>
        intro hn
        have hn' : κ ^ n ≤ W := le_trans (Nat.pow_le_pow_right hκ (Nat.le_succ n)) hn
        have IH := ih hn'
        change raw (wGen W (F n) (wRun W F n)) = bayesStep (F n) (bayesRun F n)
        set v : Fin C → ℕ := bayesStep (F n) (bayesRun F n) with hv
        have hv1 : ∀ i, 1 ≤ v i := by
          intro i
          rw [hv, bayesStep]
          have h1 := (bayesRun_bounds F hF1 hFκ n i).1
          have h2 := hF1 n i
          exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
        have hvκ : ∀ i, v i ≤ κ ^ (n + 1) := by
          intro i
          rw [hv, bayesStep, pow_succ]
          exact Nat.mul_le_mul (bayesRun_bounds F hF1 hFκ n i).2 (hFκ n i)
        have hvW : wMax v ≤ W := Finset.sup_le fun i _ => le_trans (hvκ i) hn
        have hmax1 : 1 ≤ wMax v := le_trans (hv1 i₀) (le_wMax v i₀)
        have hd1 : scaleDiv W v = 1 := by
          rw [scaleDiv]
          have : (wMax v + W - 1) / W = 1 := Nat.div_eq_of_lt_le (by omega) (by omega)
          omega
        have hproj : project W v = v := by
          funext i
          rw [project, hd1, Nat.div_one]
          exact max_eq_right (hv1 i)
        rw [raw_wGen hW, IH, hproj]

/-- The distribution form, composed from `raw_wRun_eq_bayesRun`: the finite run's reading is
exactly the `n`-step Bayes posterior, below the horizon. Unfolding `bayesRun` one step at a time
via `toDist_bayesStep` recovers the iterated form `bayesPost (⋯ bayesPost (toDist (fun _ => 1))
(F 0) ⋯) (F (n-1))` explicitly; the identity is carried once, at the level of the run, rather than
re-derived at every step. -/
theorem toDist_wRun_eq_bayes {W κ : ℕ} (hW : 1 ≤ W) (F : ℕ → Fin C → ℕ)
    (hF1 : ∀ n i, 1 ≤ F n i) (hFκ : ∀ n i, F n i ≤ κ) (n : ℕ) (hn : κ ^ n ≤ W) :
    toDist (raw (wRun W F n)) = toDist (bayesRun F n) := by
  rw [raw_wRun_eq_bayesRun hW F hF1 hFκ n hn]

/-- **The horizon is sharp.** At budget `2` the raw finite run has already diverged from the exact
run by step `2` — one step past where `raw_wRun_eq_bayesRun` guarantees equality (`2 ^ 1 ≤ 2` but
`2 ^ 2 > 2`), confirming the exponent in the horizon condition is not an artifact of the proof. -/
theorem wRun_ne_bayesRun_witness :
    raw (wRun 2 (fun (_ : ℕ) (_ : Fin 4) => 2) 2)
      ≠ bayesRun (fun (_ : ℕ) (_ : Fin 4) => 2) 2 := by
  decide

end ExactnessHorizon

/-! ## The per-step residual rate -/

section ResidualRate

variable {C : ℕ}

/-- **A general ℚ fact about normalization**, mentioning nothing about fibers: the L¹ distance
between two normalized nonnegative vectors is controlled by the L¹ distance of the vectors
themselves, over the second one's mass. The reusable core of every projection-residual bound
below. -/
theorem l1_normalize_le (a b : Fin C → ℚ) (ha : ∀ i, 0 ≤ a i) (_hb : ∀ i, 0 ≤ b i)
    (hA : 0 < ∑ i, a i) (hB : 0 < ∑ i, b i) :
    ∑ i, |a i / (∑ j, a j) - b i / (∑ j, b j)| ≤ 2 * (∑ i, |a i - b i|) / (∑ j, b j) := by
  set A := ∑ j, a j with hAdef
  set B := ∑ j, b j with hBdef
  have hAne : A ≠ 0 := hA.ne'
  have hterm : ∀ i, a i / A - b i / B = (a i * (B - A) - (b i - a i) * A) / (A * B) := by
    intro i; field_simp; ring
  have hbound : ∀ i, |a i / A - b i / B| ≤ (a i * |B - A| + |b i - a i| * A) / (A * B) := by
    intro i
    rw [hterm i, abs_div, abs_of_pos (mul_pos hA hB)]
    have htri : |a i * (B - A) - (b i - a i) * A| ≤ |a i * (B - A)| + |(b i - a i) * A| := by
      have h := abs_add_le (a i * (B - A)) (-((b i - a i) * A))
      simpa [sub_eq_add_neg, abs_neg] using h
    have heq : |a i * (B - A)| + |(b i - a i) * A| = a i * |B - A| + |b i - a i| * A := by
      rw [abs_mul, abs_mul, abs_of_nonneg (ha i), abs_of_nonneg hA.le]
    calc |a i * (B - A) - (b i - a i) * A| / (A * B)
        ≤ (|a i * (B - A)| + |(b i - a i) * A|) / (A * B) :=
          div_le_div_of_nonneg_right htri (mul_pos hA hB).le
      _ = (a i * |B - A| + |b i - a i| * A) / (A * B) := by rw [heq]
  calc ∑ i, |a i / A - b i / B|
      ≤ ∑ i, (a i * |B - A| + |b i - a i| * A) / (A * B) := Finset.sum_le_sum (fun i _ => hbound i)
    _ = (∑ i, (a i * |B - A| + |b i - a i| * A)) / (A * B) := by
        simp_rw [div_eq_mul_inv]
        rw [← Finset.sum_mul]
    _ = (A * |B - A| + (∑ i, |b i - a i|) * A) / (A * B) := by
        rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul]
    _ = A * (|B - A| + ∑ i, |b i - a i|) / (A * B) := by ring_nf
    _ = (|B - A| + ∑ i, |b i - a i|) / B := mul_div_mul_left _ _ hAne
    _ ≤ (∑ i, |b i - a i| + ∑ i, |b i - a i|) / B := by
        apply div_le_div_of_nonneg_right ?_ hB.le
        have hsub : B - A = ∑ i, (b i - a i) := by rw [Finset.sum_sub_distrib]
        have habs : |B - A| ≤ ∑ i, |b i - a i| := by
          rw [hsub]; exact Finset.abs_sum_le_sum_abs _ _
        linarith
    _ = 2 * (∑ i, |b i - a i|) / B := by ring
    _ = 2 * (∑ i, |a i - b i|) / B := by
        rw [show (∑ i, |b i - a i|) = ∑ i, |a i - b i| from
          Finset.sum_congr rfl (fun i _ => abs_sub_comm (b i) (a i))]

/-- **The coordinatewise residual is at most one quantum.** Above the floor it is integer-division
truncation: the exact ray-value and its floored coordinate differ by the fractional remainder,
which is `< 1`. At the floor the real quotient itself is `< 1`, so the discrepancy against the
forced `1` is again `≤ 1`. -/
private theorem abs_sub_project_le (W : ℕ) (v : Fin C → ℕ) (i : Fin C) :
    |(v i : ℚ) / (scaleDiv W v : ℚ) - (project W v i : ℚ)| ≤ 1 := by
  have hdpos : 0 < scaleDiv W v := scaleDiv_pos W v
  have hdQ : (0 : ℚ) < (scaleDiv W v : ℚ) := by exact_mod_cast hdpos
  have hsplit : (v i : ℚ) = (scaleDiv W v : ℚ) * ((v i / scaleDiv W v : ℕ) : ℚ)
      + ((v i % scaleDiv W v : ℕ) : ℚ) := by
    exact_mod_cast (Nat.div_add_mod (v i) (scaleDiv W v)).symm
  have hdiv : (v i : ℚ) / (scaleDiv W v : ℚ)
      = ((v i / scaleDiv W v : ℕ) : ℚ) + ((v i % scaleDiv W v : ℕ) : ℚ) / (scaleDiv W v : ℚ) := by
    rw [hsplit]; field_simp
  have hr0 : (0 : ℚ) ≤ ((v i % scaleDiv W v : ℕ) : ℚ) / (scaleDiv W v : ℚ) := by positivity
  have hr1 : ((v i % scaleDiv W v : ℕ) : ℚ) / (scaleDiv W v : ℚ) < 1 := by
    rw [div_lt_one hdQ]
    exact_mod_cast Nat.mod_lt (v i) hdpos
  rw [project, hdiv]
  rcases Nat.eq_zero_or_pos (v i / scaleDiv W v) with hq0 | hqpos
  · have hmax : max 1 (v i / scaleDiv W v) = 1 := by omega
    rw [hmax, hq0, Nat.cast_zero, zero_add, Nat.cast_one]
    rw [abs_of_nonpos (by linarith)]
    linarith
  · rw [max_eq_right hqpos]
    have heq : ((v i / scaleDiv W v : ℕ) : ℚ) + ((v i % scaleDiv W v : ℕ) : ℚ) / (scaleDiv W v : ℚ)
        - ((v i / scaleDiv W v : ℕ) : ℚ) = ((v i % scaleDiv W v : ℕ) : ℚ) / (scaleDiv W v : ℚ) := by
      ring
    rw [heq, abs_of_nonneg hr0]
    linarith

/-- **The projection stays close to the exact ray, in total variation.** No side hypothesis on the
budget: the bound is honest even when the projection has to do real work, and it degrades
gracefully as `∑ project W v` shrinks. `l1_normalize_le` applied to the un-normalized ray
`v / scaleDiv W v` (whose normalization is `toDist v`, by ray-invariance) against the projected
vector itself. -/
theorem toDist_project_close {W : ℕ} (_hW : 1 ≤ W) (v : Fin C → ℕ) (hv : 0 < ∑ j, v j) :
    ∑ i, |toDist (project W v) i - toDist v i| ≤ 2 * C / (∑ i, (project W v i : ℚ)) := by
  rcases Nat.eq_zero_or_pos C with hC0 | hCpos
  · subst hC0; simp
  have hdpos : 0 < scaleDiv W v := scaleDiv_pos W v
  have hdQ : (0 : ℚ) < (scaleDiv W v : ℚ) := by exact_mod_cast hdpos
  set a : Fin C → ℚ := fun i => (v i : ℚ) / (scaleDiv W v : ℚ) with ha_def
  set b : Fin C → ℚ := fun i => (project W v i : ℚ) with hb_def
  have ha : ∀ i, 0 ≤ a i := fun i => by rw [ha_def]; positivity
  have hb : ∀ i, 0 ≤ b i := fun i => by rw [hb_def]; positivity
  have hvQ : (0 : ℚ) < ∑ j, (v j : ℚ) := by exact_mod_cast hv
  have hasum : (∑ i, a i) = (∑ i, (v i : ℚ)) / (scaleDiv W v : ℚ) := by
    rw [ha_def]; simp_rw [div_eq_mul_inv]; rw [← Finset.sum_mul]
  have hA : 0 < ∑ i, a i := by rw [hasum]; positivity
  have hBpos : ∀ i, (1 : ℚ) ≤ b i := fun i => by
    change (1 : ℚ) ≤ (project W v i : ℚ); exact_mod_cast one_le_project W v i
  have hB : 0 < ∑ i, b i := by
    calc (0 : ℚ) < (C : ℚ) := by exact_mod_cast hCpos
      _ = ∑ _i : Fin C, (1 : ℚ) := by simp
      _ ≤ ∑ i, b i := Finset.sum_le_sum (fun i _ => hBpos i)
  have hray : ∀ i, a i / (∑ j, a j) = toDist v i := by
    intro i
    rw [ha_def, hasum]
    change ((v i : ℚ) / (scaleDiv W v : ℚ)) / ((∑ j, (v j : ℚ)) / (scaleDiv W v : ℚ)) = toDist v i
    rw [div_div_div_cancel_right₀ hdQ.ne']
    rfl
  have hbeq : ∀ i, toDist (project W v) i = b i / ∑ j, b j := fun i => rfl
  have hkey := l1_normalize_le a b ha hb hA hB
  have hres : ∀ i, |a i - b i| ≤ 1 := fun i => by
    rw [ha_def, hb_def]; exact abs_sub_project_le W v i
  have hsumres : ∑ i, |a i - b i| ≤ (C : ℚ) := by
    calc ∑ i, |a i - b i| ≤ ∑ _i : Fin C, (1 : ℚ) := Finset.sum_le_sum (fun i _ => hres i)
      _ = C := by simp
  calc ∑ i, |toDist (project W v) i - toDist v i|
      = ∑ i, |a i / (∑ j, a j) - b i / (∑ j, b j)| := by
        apply Finset.sum_congr rfl
        intro i _
        rw [hbeq i, hray i, abs_sub_comm]
    _ ≤ 2 * (∑ i, |a i - b i|) / (∑ j, b j) := hkey
    _ ≤ 2 * C / (∑ j, b j) := by
        apply div_le_div_of_nonneg_right _ hB.le
        linarith [hsumres]

private theorem ceilDiv_ge {a W : ℕ} (hW : 0 < W) : a ≤ W * ((a + W - 1) / W) := by
  have h := Nat.div_add_mod (a + W - 1) W
  have hr : (a + W - 1) % W < W := Nat.mod_lt _ hW
  omega

/-- **The budget binds through the leader alone.** Past the horizon (`W < wMax v`) the projection
does real work, and the heaviest candidate's projected weight is already at least half the budget
— stated multiplicatively to keep `ℕ` division out of the bound entirely. -/
theorem sum_project_ge {W : ℕ} (hW : 1 ≤ W) (v : Fin C → ℕ) (hmax : W < wMax v) :
    W ≤ 2 * ∑ i, project W v i := by
  have hwpos : 0 < wMax v := lt_of_le_of_lt (Nat.zero_le W) hmax
  have hne : (Finset.univ : Finset (Fin C)).Nonempty := by
    by_contra hne
    rw [Finset.not_nonempty_iff_eq_empty] at hne
    simp [wMax, hne] at hwpos
  obtain ⟨i₀, -, hi₀⟩ : ∃ i ∈ Finset.univ, wMax v = v i :=
    Finset.exists_mem_eq_sup Finset.univ hne v
  have hquot2 : 2 ≤ (wMax v + W - 1) / W := by
    rw [Nat.le_div_iff_mul_le hW]; omega
  have hd_eq : scaleDiv W v = (wMax v + W - 1) / W := by
    rw [scaleDiv]; omega
  have hdpos : 0 < scaleDiv W v := scaleDiv_pos W v
  have hd2 : 2 ≤ scaleDiv W v := by rw [hd_eq]; exact hquot2
  have hA : wMax v ≤ scaleDiv W v * W := by
    rw [hd_eq, mul_comm]; exact ceilDiv_ge hW
  have hA2 : scaleDiv W v * W ≤ wMax v + W - 1 := by
    rw [hd_eq]; exact Nat.div_mul_le_self _ _
  have hA2' : scaleDiv W v * W + 1 ≤ wMax v + W := by omega
  have hqr := Nat.div_add_mod (wMax v) (scaleDiv W v)
  have hrlt : wMax v % scaleDiv W v < scaleDiv W v := Nat.mod_lt _ hdpos
  have hq : W ≤ 2 * (wMax v / scaleDiv W v) := by
    rcases Nat.lt_or_ge (wMax v / scaleDiv W v) W with hcase | hcase
    · have hcaseZ : (wMax v / scaleDiv W v : ℤ) + 1 ≤ (W : ℤ) := by exact_mod_cast hcase
      zify at hA hA2' hqr hrlt hd2 hW ⊢
      nlinarith [hA, hA2', hqr, hrlt, hd2, hcaseZ,
        mul_nonneg (by linarith : (0:ℤ) ≤ (scaleDiv W v : ℤ) - 2)
                   (by linarith : (0:ℤ) ≤ (W : ℤ) - (wMax v / scaleDiv W v : ℤ) - 1)]
    · omega
  have hproj : wMax v / scaleDiv W v ≤ project W v i₀ := by
    rw [project, hi₀]; exact le_max_right _ _
  calc W ≤ 2 * (wMax v / scaleDiv W v) := hq
    _ ≤ 2 * project W v i₀ := by omega
    _ ≤ 2 * ∑ i, project W v i := by
        have := Finset.single_le_sum (f := fun i => project W v i)
          (fun i _ => Nat.zero_le _) (Finset.mem_univ i₀)
        omega

/-- **The rate, binding once the budget is spent past the horizon.** Composes
`toDist_project_close` (the general closeness bound) with `sum_project_ge` (the projected mass is
at least half the budget) to eliminate the projected mass from the denominator in favour of `W`
itself — the form `IN-8` cites. -/
theorem toDist_project_rate {W : ℕ} (hW : 1 ≤ W) (v : Fin C → ℕ) (hv : 0 < ∑ j, v j)
    (hmax : W < wMax v) :
    ∑ i, |toDist (project W v) i - toDist v i| ≤ 4 * C / W := by
  have h1 := toDist_project_close hW v hv
  have h2 := sum_project_ge hW v hmax
  have hSpos : 0 < ∑ i, project W v i := by omega
  have hSpos' : (0 : ℚ) < ∑ i, (project W v i : ℚ) := by exact_mod_cast hSpos
  have hWQ : (0 : ℚ) < (W : ℚ) := by exact_mod_cast hW
  have h2Q : (W : ℚ) ≤ 2 * ∑ i, (project W v i : ℚ) := by exact_mod_cast h2
  have hCQ : (0 : ℚ) ≤ (C : ℚ) := by positivity
  calc ∑ i, |toDist (project W v) i - toDist v i|
      ≤ 2 * C / (∑ i, (project W v i : ℚ)) := h1
    _ ≤ 4 * C / W := by
        rw [div_le_div_iff₀ hSpos' hWQ]
        nlinarith [h2Q, hCQ]

/-- **The composed statement against exact Bayes** — `IN-8`'s citation form: one projected
generation stays within `4C/W` of the exact posterior it approximates, past the horizon. -/
theorem wGen_bayes_rate {W : ℕ} (hW : 1 ≤ W) (f w : Fin C → ℕ) (hw : 0 < ∑ j, w j)
    (hf : ∀ i, 0 < f i) (hmax : W < wMax (bayesStep f w)) :
    ∑ i, |toDist (project W (bayesStep f w)) i - bayesPost (toDist w) f i| ≤ 4 * C / W := by
  have hle : ∀ j, w j ≤ bayesStep f w j := fun j => by
    rw [bayesStep]; exact Nat.le_mul_of_pos_right _ (hf j)
  have hbs : 0 < ∑ j, bayesStep f w j :=
    lt_of_lt_of_le hw (Finset.sum_le_sum (fun j _ => hle j))
  have hrate := toDist_project_rate hW (bayesStep f w) hbs hmax
  rwa [toDist_bayesStep f w hw hf] at hrate

end ResidualRate

/-! ## Reconciling the rate with the exhibited annihilation

`weighted_fiber_not_exactly_bayes` is not a counterexample to `wGen_bayes_rate` — it sits in the
regime the rate has nothing to say about. Total variation between any two readings is capped at
`2` (`toDist_sub_le_two`, universally, no fiber structure involved), while `wGen_bayes_rate`'s
bound `4 * C / W` at the witness's own `C = 2`, `W = 2` reads `4`, already above that universal
cap. The rate only binds once it undercuts `2`, i.e. once `W > 2 * C`: the annihilation regime is
`W ≲ C` and the rate bites only once `W ≫ C`, so the two facts occupy disjoint budgets rather than
contradicting each other. -/

section Reconciliation

variable {C : ℕ}

/-- **A universal cap, no fiber structure involved**: two readings never disagree by more than `2`
in total variation, because each coordinate's disagreement is at most the sum of the two masses
there, and each reading's own mass sums to exactly `1`. -/
theorem toDist_sub_le_two (w1 w2 : Fin C → ℕ) (h1 : 0 < ∑ j, w1 j) (h2 : 0 < ∑ j, w2 j) :
    ∑ i, |toDist w1 i - toDist w2 i| ≤ 2 := by
  have hd1 : (0 : ℚ) < ∑ j, (w1 j : ℚ) := by exact_mod_cast h1
  have hd2 : (0 : ℚ) < ∑ j, (w2 j : ℚ) := by exact_mod_cast h2
  have hp : ∀ i, 0 ≤ toDist w1 i := fun i => by unfold toDist; positivity
  have hq : ∀ i, 0 ≤ toDist w2 i := fun i => by unfold toDist; positivity
  have hpsum : ∑ i, toDist w1 i = 1 := by
    have heq : ∑ i, toDist w1 i = (∑ i, (w1 i : ℚ)) / ∑ j, (w1 j : ℚ) := by
      unfold toDist; simp_rw [div_eq_mul_inv]; rw [← Finset.sum_mul]
    rw [heq, div_self hd1.ne']
  have hqsum : ∑ i, toDist w2 i = 1 := by
    have heq : ∑ i, toDist w2 i = (∑ i, (w2 i : ℚ)) / ∑ j, (w2 j : ℚ) := by
      unfold toDist; simp_rw [div_eq_mul_inv]; rw [← Finset.sum_mul]
    rw [heq, div_self hd2.ne']
  have habs : ∀ i, |toDist w1 i - toDist w2 i| ≤ toDist w1 i + toDist w2 i := by
    intro i
    rw [abs_sub_le_iff]
    constructor <;> linarith [hp i, hq i]
  calc ∑ i, |toDist w1 i - toDist w2 i|
      ≤ ∑ i, (toDist w1 i + toDist w2 i) := Finset.sum_le_sum (fun i _ => habs i)
    _ = ∑ i, toDist w1 i + ∑ i, toDist w2 i := Finset.sum_add_distrib
    _ = 2 := by rw [hpsum, hqsum]; norm_num

/-- **The witness lies in the rate's own vacuity zone.** At `C = 2`, `W = 2` — exactly
`weighted_fiber_not_exactly_bayes`'s instance — `wGen_bayes_rate`'s bound is `4`, already above
the universal cap `toDist_sub_le_two` puts on any total-variation discrepancy. The total discarding
of a step there is consistent with the rate precisely because the rate is silent at that budget. -/
theorem rate_vacuous_at_badW_instance : (4 * (2 : ℚ) / (2 : ℚ)) ≥ 2 := by norm_num

end Reconciliation

end WeightedFiber
