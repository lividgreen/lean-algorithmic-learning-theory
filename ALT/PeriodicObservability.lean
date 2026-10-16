module

public import ALT.GrowingComposite

/-!
# The periodic dichotomy at a Dirac: E1 against the cycle average, and nowhere else

[Growth] §3 Proposition 3.1's positive half is stated at paper level: a finite deterministic
autonomous host, eventually periodic by construction, carries the sampling-rate hypothesis
`MixingHoeffding` only against its own period averages, at a constant the elementary
estimate puts at the order of the period squared. This module machine-checks that estimate, both
directions, at the Dirac reading `mixingHoeffding_dirac_iff` already gives a
deterministic trajectory: **(E1 at the cycle average)** the hypothesis holds against the query's own
cycle average, at a constant of order `(N + P)²`; **(at no other answer)** it fails at every other
declared answer, at every positive mixing constant — the Dirac-level refinement of
`ALT.not_mixingHoeffding_of_periodic_ne`, which needs its mean-constancy hypothesis over
*every* sample path rather than the single trajectory a Dirac law actually carries. Packaged at the
scheduled query class (`ALT.pairChar`, offsets `(a, 8)`), the two halves are one
dichotomy: `MixingHoeffding` holds at some positive constant iff the declared answer is the cycle
average — the estimate [Inevitability] §5 states at Remark 5.3, Proposition 5.4's cost paragraph
and Remark 5.7, cited there rather than reproved.

## Main results

* `cycleAvg` — the average of a sequence over one cycle, read from a threshold `N` at period `P`.
* `abs_sum_sub_mul_cycleAvg_le` — **the sequence lemma**: for any `[-1, 1]`-bounded, eventually
  `P`-periodic-from-`N` sequence, its partial sums track `n` times the cycle average to within
  `2(N + P)` at every horizon `n` — proved by strong induction, peeling one full period at a time
  (each peeled block contributes exactly the cycle average, by the periodic sequence's own
  shift-invariance over one period, `periodSum_eq_cycleAvg_mul`), so the whole bound is paid once,
  at the pre-period horizons `n < N + P`.
* `pairCycleAvg` — the cycle average of a two-offset query ensemble read along an eventually
  periodic observation.
* `mixingHoeffding_dirac_of_eventuallyPeriodic` — **E1 at the cycle average**: at the point mass on
  an eventually `P`-periodic-from-`N` observation, `MixingHoeffding` holds against the query's own
  cycle average, at constant `(2(N + P))² / (2 ln 2)` — the sequence lemma fed
  `ALT.mixingHoeffding_dirac_of_deviation_bound`.
* `not_mixingHoeffding_dirac_of_eventuallyPeriodic_ne` — **at no other answer**: at that same Dirac
  law, `MixingHoeffding` fails at every declared answer other than the cycle average and every
  positive mixing constant — through `mixingHoeffding_dirac_iff` and the sequence
  lemma, both per-`n` bounds forcing the gap to the cycle average below any positive threshold,
  false at one explicit large `n`. Needs no re-ensembling and no on-cycle start: it is stated at
  the Dirac on the genuine trajectory, with the genuine query ensemble, at an arbitrary pre-period.
* `mixingHoeffding_dirac_pairChar_iff` — **the dichotomy, packaged** at the scheduled offsets
  `(a, 8)` against `ALT.pairChar`: `MixingHoeffding` holds at some positive constant
  iff the declared answer is the cycle average.

## Scope

The constant `2(N + P)` in the sequence lemma is the honest one from the proof (peeling loses
nothing; the whole bound is paid at the pre-period), not the tightest available — a sharper `2N +
2r` at the exact remainder `r` is not worth stating. Nothing here bounds the BEST constant an
eventually periodic observation can carry against its cycle average; only the estimate's own order.
-/



@[expose] public section

namespace ALT

/-! ## The cycle average, and the sequence lemma -/

/-- **The cycle average**: the mean of `z` over one period, read from the threshold `N`. -/
noncomputable def cycleAvg (z : ℕ → ℝ) (N P : ℕ) : ℝ :=
  (P : ℝ)⁻¹ * ∑ j ∈ Finset.range P, z (N + j)

/-- A period-`P`-from-`N` sequence's period-length window sum is independent of where, past `N`,
that window starts — shifting the window by one replaces its first term with a new last term equal
to it by periodicity, so the sum is unchanged; iterating gives an arbitrary shift. -/
private theorem periodSum_shift_one (z : ℕ → ℝ) {P N : ℕ}
    (hper : ∀ t, N ≤ t → z (t + P) = z t) {u : ℕ} (hu : N ≤ u) :
    ∑ j ∈ Finset.range P, z (u + 1 + j) = ∑ j ∈ Finset.range P, z (u + j) := by
  have h1 : ∑ j ∈ Finset.range (P + 1), z (u + j)
      = ∑ j ∈ Finset.range P, z (u + (j + 1)) + z (u + 0) :=
    Finset.sum_range_succ' (fun j => z (u + j)) P
  have h2 : ∑ j ∈ Finset.range (P + 1), z (u + j)
      = ∑ j ∈ Finset.range P, z (u + j) + z (u + P) :=
    Finset.sum_range_succ (fun j => z (u + j)) P
  have hz : z (u + P) = z u := hper u hu
  have heq : ∑ j ∈ Finset.range P, z (u + (j + 1)) = ∑ j ∈ Finset.range P, z (u + j) := by
    have hcomb := h1.symm.trans h2
    simp only [Nat.add_zero] at hcomb
    rw [hz] at hcomb
    linarith [hcomb]
  have hshift : (fun j => z (u + (j + 1))) = (fun j => z (u + 1 + j)) := by
    funext j; congr 1; omega
  rwa [hshift] at heq

private theorem periodSum_shift (z : ℕ → ℝ) {P N : ℕ}
    (hper : ∀ t, N ≤ t → z (t + P) = z t) {u : ℕ} (hu : N ≤ u) (d : ℕ) :
    ∑ j ∈ Finset.range P, z (u + d + j) = ∑ j ∈ Finset.range P, z (u + j) := by
  induction d with
  | zero => simp
  | succ d ih =>
    have hud : N ≤ u + d := by omega
    have hstep := periodSum_shift_one z hper hud
    have hre : u + (d + 1) = (u + d) + 1 := by omega
    rw [hre, hstep]
    exact ih

/-- **Any full period from any point at or past `N` sums to the same total.** -/
private theorem periodSum_eq_cycleAvg_mul (z : ℕ → ℝ) {P N : ℕ}
    (hper : ∀ t, N ≤ t → z (t + P) = z t) {u : ℕ} (hu : N ≤ u) :
    ∑ j ∈ Finset.range P, z (u + j) = ∑ j ∈ Finset.range P, z (N + j) := by
  have hshift := periodSum_shift z hper (u := N) (le_refl N) (u - N)
  rwa [show N + (u - N) = u from by omega] at hshift

/-- **The sequence lemma.** Strong induction on `n`: below `N + P` the crude bound `|∑| ≤ n` and
`|n · cycleAvg| ≤ n` already give `2n ≤ 2(N + P)`; at or past `N + P`, peeling the last `P` terms
subtracts exactly `P · cycleAvg z N P` (by `periodSum_eq_cycleAvg_mul`), so the peeled block
contributes nothing to the bound and the induction hypothesis at `n - P` carries the whole estimate
forward unchanged. -/
theorem abs_sum_sub_mul_cycleAvg_le (z : ℕ → ℝ) (hz : ∀ t, |z t| ≤ 1) {P N : ℕ} (hP : 0 < P)
    (hper : ∀ t, N ≤ t → z (t + P) = z t) (n : ℕ) :
    |∑ t ∈ Finset.range n, z t - (n : ℝ) * cycleAvg z N P| ≤ 2 * (N + P) := by
  have havg_abs : |cycleAvg z N P| ≤ 1 := by
    have hPR : (0 : ℝ) < P := by exact_mod_cast hP
    rw [cycleAvg, abs_mul, abs_of_pos (by positivity : (0:ℝ) < (P:ℝ)⁻¹)]
    have hsum_abs : |∑ j ∈ Finset.range P, z (N + j)| ≤ (P : ℝ) := by
      calc |∑ j ∈ Finset.range P, z (N + j)| ≤ ∑ j ∈ Finset.range P, |z (N + j)| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _j ∈ Finset.range P, (1 : ℝ) := Finset.sum_le_sum (fun j _ => hz _)
        _ = (P : ℝ) := by simp
    calc (P:ℝ)⁻¹ * |∑ j ∈ Finset.range P, z (N + j)| ≤ (P:ℝ)⁻¹ * P :=
          mul_le_mul_of_nonneg_left hsum_abs (by positivity)
      _ = 1 := by field_simp
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases hcase : n < N + P
    · have h1 : |∑ t ∈ Finset.range n, z t| ≤ (n : ℝ) := by
        calc |∑ t ∈ Finset.range n, z t| ≤ ∑ t ∈ Finset.range n, |z t| :=
              Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ _t ∈ Finset.range n, (1 : ℝ) := Finset.sum_le_sum (fun t _ => hz t)
          _ = (n : ℝ) := by simp
      have h2 : |(n : ℝ) * cycleAvg z N P| ≤ (n : ℝ) := by
        rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg n)]
        calc (n : ℝ) * |cycleAvg z N P| ≤ (n : ℝ) * 1 :=
              mul_le_mul_of_nonneg_left havg_abs (Nat.cast_nonneg n)
          _ = (n : ℝ) := mul_one _
      have h3 := abs_sub (∑ t ∈ Finset.range n, z t) ((n : ℝ) * cycleAvg z N P)
      have hnR : (n : ℝ) < (N : ℝ) + P := by exact_mod_cast hcase
      linarith [h3, h1, h2]
    · push Not at hcase
      set n' := n - P with hn'def
      have hnn' : n = n' + P := by omega
      have hn'ge : N ≤ n' := by omega
      have hn'lt : n' < n := by omega
      have hIH := ih n' hn'lt
      have hsplit : ∑ t ∈ Finset.range n, z t
          = ∑ t ∈ Finset.range n', z t + ∑ j ∈ Finset.range P, z (n' + j) := by
        rw [hnn']; exact Finset.sum_range_add z n' P
      have hblock : ∑ j ∈ Finset.range P, z (n' + j) = ∑ j ∈ Finset.range P, z (N + j) :=
        periodSum_eq_cycleAvg_mul z hper hn'ge
      have hPavg : ∑ j ∈ Finset.range P, z (N + j) = (P : ℝ) * cycleAvg z N P := by
        rw [cycleAvg]
        have hPR : (P : ℝ) ≠ 0 := by exact_mod_cast hP.ne'
        field_simp
      have hrewrite : ∑ t ∈ Finset.range n, z t - (n : ℝ) * cycleAvg z N P
          = (∑ t ∈ Finset.range n', z t - (n' : ℝ) * cycleAvg z N P)
            + (∑ j ∈ Finset.range P, z (n' + j) - (P : ℝ) * cycleAvg z N P) := by
        rw [hsplit]
        have : ((n : ℕ) : ℝ) = (n' : ℝ) + (P : ℝ) := by rw [hnn']; push_cast; ring
        rw [this]; ring
      rw [hrewrite, hblock, hPavg, sub_self, add_zero]
      calc |∑ t ∈ Finset.range n', z t - (n' : ℝ) * cycleAvg z N P| ≤ 2 * (N + P) := hIH

/-! ## The two consumers, at the pair ensembles -/

/-- **The cycle average of a two-offset query ensemble**, read along an eventually periodic
observation. -/
noncomputable def pairCycleAvg (ψ : Bool → Bool → ℝ) (a b : ℕ) (o : ℕ → Bool) (N P : ℕ) : ℝ :=
  cycleAvg (fun t => ALT.pairEnsemble ψ a b t o) N P

/-- A two-offset query ensemble read along a `P`-periodic-from-`N` observation is itself
`P`-periodic from `N`: a shift of the observation's own periodicity by the two offsets, which only
helps, since `t + a ≥ N` and `t + b ≥ N` whenever `t ≥ N`. -/
private theorem eventuallyPeriodic_pairEnsemble (ψ : Bool → Bool → ℝ) (a b : ℕ) (o : ℕ → Bool)
    {P N : ℕ} (hper : ∀ u, N ≤ u → o (u + P) = o u) :
    ∀ t, N ≤ t → ALT.pairEnsemble ψ a b (t + P) o
      = ALT.pairEnsemble ψ a b t o := by
  intro t ht
  simp only [ALT.pairEnsemble]
  have hta : t + P + a = (t + a) + P := by omega
  have htb : t + P + b = (t + b) + P := by omega
  rw [hta, htb, hper (t + a) (by omega), hper (t + b) (by omega)]

/-! ## E1 at the cycle average -/

/-- **E1 at the cycle average.** At the point mass on an eventually `P`-periodic-from-`N`
observation, `MixingHoeffding` holds against the two-offset query's own cycle average, at constant
`(2(N + P))² / (2 ln 2)` — the sequence lemma's deviation bound fed
`ALT.mixingHoeffding_dirac_of_deviation_bound`. Cited: [Growth] §3 Proposition 3.1;
[Inevitability] §5 Remark 5.3, Proposition 5.4's cost paragraph, Remark 5.7. -/
theorem mixingHoeffding_dirac_of_eventuallyPeriodic (ψ : Bool → Bool → ℝ)
    (hψ : ∀ u v, |ψ u v| ≤ 1) (a b : ℕ) (o : ℕ → Bool) {P N : ℕ} (hP : 0 < P)
    (hper : ∀ u, N ≤ u → o (u + P) = o u) :
    MixingHoeffding (MeasureTheory.Measure.dirac o)
      (ALT.pairEnsemble ψ a b) (pairCycleAvg ψ a b o N P)
      ((2 * ((N : ℝ) + P)) ^ 2 / (2 * Real.log 2)) := by
  have hz : ∀ t, |ALT.pairEnsemble ψ a b t o| ≤ 1 := fun t => by
    simp only [ALT.pairEnsemble]; exact hψ _ _
  have hbound : ∀ n : ℕ, 1 ≤ n →
      (n : ℝ) * |SQOracle.empiricalMean (ALT.pairEnsemble ψ a b) n o
        - pairCycleAvg ψ a b o N P| ≤ 2 * ((N : ℝ) + P) := by
    intro n hn1
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
    have heq : (n : ℝ) * (SQOracle.empiricalMean (ALT.pairEnsemble ψ a b) n o
        - pairCycleAvg ψ a b o N P)
        = ∑ t ∈ Finset.range n, ALT.pairEnsemble ψ a b t o
          - (n : ℝ) * cycleAvg (fun t => ALT.pairEnsemble ψ a b t o) N P := by
      rw [SQOracle.empiricalMean, pairCycleAvg]
      field_simp
    have hb := abs_sum_sub_mul_cycleAvg_le (fun t => ALT.pairEnsemble ψ a b t o)
      hz hP (eventuallyPeriodic_pairEnsemble ψ a b o hper) n
    have hlhs : |(n : ℝ) * (SQOracle.empiricalMean (ALT.pairEnsemble ψ a b) n o
        - pairCycleAvg ψ a b o N P)|
        = (n : ℝ) * |SQOracle.empiricalMean (ALT.pairEnsemble ψ a b) n o
          - pairCycleAvg ψ a b o N P| := by
      rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg n)]
    rw [← hlhs, heq]
    exact hb
  exact ALT.mixingHoeffding_dirac_of_deviation_bound o
    (ALT.pairEnsemble ψ a b) (pairCycleAvg ψ a b o N P) (2 * ((N : ℝ) + P))
    (by positivity) (fun i => ALT.measurable_pairEnsemble ψ a b i) hbound

/-! ## At no other answer -/

/-- **At no other answer.** At that same Dirac law, `MixingHoeffding` fails at every declared
answer other than the cycle average, at every positive mixing constant. Through
`mixingHoeffding_dirac_iff`, the hypothesis gives `|mean_n − predZ| ≤
√(2c ln 2 / n)` at every `n ≥ 1`; the sequence lemma gives `|mean_n − avg| ≤ 2(N + P) / n`; the two
force the gap `|avg − predZ|` below any positive threshold, false at one explicit large `n`. Needs
no re-ensembling and no on-cycle start: `hper` is an arbitrary pre-period on the genuine trajectory
`o`, and the genuine query ensemble is what the bound is stated against. -/
theorem not_mixingHoeffding_dirac_of_eventuallyPeriodic_ne (ψ : Bool → Bool → ℝ)
    (hψ : ∀ u v, |ψ u v| ≤ 1) (a b : ℕ) (o : ℕ → Bool) {P N : ℕ} (hP : 0 < P)
    (hper : ∀ u, N ≤ u → o (u + P) = o u) {predZ c : ℝ} (hc : 0 < c)
    (hne : predZ ≠ pairCycleAvg ψ a b o N P) :
    ¬ MixingHoeffding (MeasureTheory.Measure.dirac o)
      (ALT.pairEnsemble ψ a b) predZ c := by
  intro hmix
  set gap := |pairCycleAvg ψ a b o N P - predZ| with hgapdef
  have hgap_pos : 0 < gap := by
    rw [hgapdef]; exact abs_pos.mpr (sub_ne_zero.mpr hne.symm)
  have hmeas : ∀ i, Measurable (ALT.pairEnsemble ψ a b i) :=
    fun i => ALT.measurable_pairEnsemble ψ a b i
  have hiff := (mixingHoeffding_dirac_iff o (ALT.pairEnsemble ψ a b)
    predZ c hc hmeas).mp hmix
  have hz : ∀ t, |ALT.pairEnsemble ψ a b t o| ≤ 1 := fun t => by
    simp only [ALT.pairEnsemble]; exact hψ _ _
  have hdev := abs_sum_sub_mul_cycleAvg_le (fun t => ALT.pairEnsemble ψ a b t o)
    hz hP (eventuallyPeriodic_pairEnsemble ψ a b o hper)
  set n₀ : ℕ := ⌈4 * ((N : ℝ) + P) / gap⌉₊ + ⌈8 * c * Real.log 2 / gap ^ 2⌉₊ + 1 with hn0def
  have hn0_pos : 1 ≤ n₀ := by omega
  have hn0Rpos : (0 : ℝ) < (n₀ : ℝ) := by exact_mod_cast hn0_pos
  have hn0R1 : 4 * ((N : ℝ) + P) / gap < (n₀ : ℝ) := by
    have h1 : 4 * ((N : ℝ) + P) / gap ≤ (⌈4 * ((N : ℝ) + P) / gap⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : (0 : ℝ) ≤ (⌈8 * c * Real.log 2 / gap ^ 2⌉₊ : ℝ) := Nat.cast_nonneg _
    rw [hn0def]; push_cast; linarith
  have hn0R2 : 8 * c * Real.log 2 / gap ^ 2 < (n₀ : ℝ) := by
    have h1 : 8 * c * Real.log 2 / gap ^ 2 ≤ (⌈8 * c * Real.log 2 / gap ^ 2⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : (0 : ℝ) ≤ (⌈4 * ((N : ℝ) + P) / gap⌉₊ : ℝ) := Nat.cast_nonneg _
    rw [hn0def]; push_cast; linarith
  have hbound1 : |SQOracle.empiricalMean (ALT.pairEnsemble ψ a b) n₀ o - predZ|
      ≤ Real.sqrt (2 * c * Real.log 2 / n₀) := hiff n₀ hn0_pos
  have hbound2 : |SQOracle.empiricalMean (ALT.pairEnsemble ψ a b) n₀ o
      - pairCycleAvg ψ a b o N P| ≤ 2 * ((N : ℝ) + P) / n₀ := by
    have heq : (n₀ : ℝ) * (SQOracle.empiricalMean (ALT.pairEnsemble ψ a b) n₀ o
        - pairCycleAvg ψ a b o N P)
        = ∑ t ∈ Finset.range n₀, ALT.pairEnsemble ψ a b t o
          - (n₀ : ℝ) * cycleAvg (fun t => ALT.pairEnsemble ψ a b t o) N P := by
      rw [SQOracle.empiricalMean, pairCycleAvg]
      field_simp
    have habs : (n₀ : ℝ) * |SQOracle.empiricalMean (ALT.pairEnsemble ψ a b) n₀ o
        - pairCycleAvg ψ a b o N P| ≤ 2 * ((N : ℝ) + P) := by
      rw [← abs_of_pos hn0Rpos, ← abs_mul, heq]
      exact hdev n₀
    rw [le_div_iff₀ hn0Rpos]
    linarith [habs]
  have htri : gap ≤
      |pairCycleAvg ψ a b o N P - SQOracle.empiricalMean (ALT.pairEnsemble ψ a b) n₀ o|
      + |SQOracle.empiricalMean (ALT.pairEnsemble ψ a b) n₀ o - predZ| := by
    rw [hgapdef]
    exact abs_sub_le (pairCycleAvg ψ a b o N P)
      (SQOracle.empiricalMean (ALT.pairEnsemble ψ a b) n₀ o) predZ
  have hcomm :
      |pairCycleAvg ψ a b o N P - SQOracle.empiricalMean (ALT.pairEnsemble ψ a b) n₀ o|
      = |SQOracle.empiricalMean (ALT.pairEnsemble ψ a b) n₀ o
          - pairCycleAvg ψ a b o N P| :=
    abs_sub_comm _ _
  have hh1 : 2 * ((N : ℝ) + P) / n₀ < gap / 2 := by
    rw [div_lt_iff₀ hgap_pos] at hn0R1
    rw [div_lt_div_iff₀ hn0Rpos (by norm_num : (0 : ℝ) < 2)]
    nlinarith [hn0R1]
  have hh2 : Real.sqrt (2 * c * Real.log 2 / n₀) < gap / 2 := by
    rw [Real.sqrt_lt' (by linarith : (0 : ℝ) < gap / 2)]
    rw [div_lt_iff₀ (by positivity : (0 : ℝ) < gap ^ 2)] at hn0R2
    rw [div_lt_iff₀ hn0Rpos]
    nlinarith [hn0R2]
  linarith [htri, hcomm, hbound2, hbound1, hh1, hh2]

/-! ## The dichotomy, packaged -/

/-- **The dichotomy, packaged** at the scheduled offsets `(a, 8)` against
`ALT.pairChar`. `0 < c` sits inside the existential because every nonpositive constant
makes `MixingHoeffding` hold trivially (`ALT.mixingHoeffding_of_nonpos`), so the genuine
content is at positive constants. -/
theorem mixingHoeffding_dirac_pairChar_iff (a : Fin 8) (o : ℕ → Bool) {P N : ℕ} (hP : 0 < P)
    (hper : ∀ u, N ≤ u → o (u + P) = o u) (predZ : ℝ) :
    (∃ c : ℝ, 0 < c ∧ MixingHoeffding (MeasureTheory.Measure.dirac o)
      (ALT.pairEnsemble ALT.pairChar (a : ℕ) 8) predZ c)
      ↔ predZ = pairCycleAvg ALT.pairChar (a : ℕ) 8 o N P := by
  constructor
  · rintro ⟨c, hc, hmix⟩
    by_contra hne
    exact not_mixingHoeffding_dirac_of_eventuallyPeriodic_ne ALT.pairChar
      ALT.abs_pairChar_le_one (a : ℕ) 8 o hP hper hc hne hmix
  · intro heq
    have hNPpos : (0 : ℝ) < 2 * ((N : ℝ) + P) := by
      have hPR : (0 : ℝ) < (P : ℝ) := by exact_mod_cast hP
      linarith [Nat.cast_nonneg (α := ℝ) N]
    have hlog2pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    refine ⟨(2 * ((N : ℝ) + P)) ^ 2 / (2 * Real.log 2),
      div_pos (pow_pos hNPpos 2) (by linarith), ?_⟩
    rw [heq]
    exact mixingHoeffding_dirac_of_eventuallyPeriodic ALT.pairChar
      ALT.abs_pairChar_le_one (a : ℕ) 8 o hP hper

end ALT

/-! ## Axiom audit

Every capstone above is `#print axioms`-clean on the standard triple or a subset of it, and the
guards below make that build-enforced. -/


set_option linter.style.longLine false in
/-- info: 'ALT.abs_sum_sub_mul_cycleAvg_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.abs_sum_sub_mul_cycleAvg_le

set_option linter.style.longLine false in
/-- info: 'ALT.mixingHoeffding_dirac_of_eventuallyPeriodic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.mixingHoeffding_dirac_of_eventuallyPeriodic

set_option linter.style.longLine false in
/-- info: 'ALT.not_mixingHoeffding_dirac_of_eventuallyPeriodic_ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.not_mixingHoeffding_dirac_of_eventuallyPeriodic_ne

set_option linter.style.longLine false in
/-- info: 'ALT.mixingHoeffding_dirac_pairChar_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.mixingHoeffding_dirac_pairChar_iff
