/-
Copyright (c) 2026 Mykola Palamarchuk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mykola Palamarchuk
-/
import ALT.TapeHostObservability
import ALT.LearningWitness

/-!
# The affordable regime's worked example: a deterministic schedule oracle and identification

[Inevitability] §6's "A possible affordable regime" paragraph names, as an open item, a worked
example: a class on which the discovery leg of the race is won at a bounded, explicit pace. This
module supplies it on every host of [Inevitability] §5 Proposition 5.9's class.

Two theorems. `scheduleOracle_deterministic` reads `TapeHostObservability.deviation_bound` at the
pair character (`NoisyWindowChain.pairChar`) and divides by the horizon `n`: on any `Profile`,
the schedule's own statistic at every offset is a `SQObjects.IsSQOracle` for the profile's trend
`ρ`, at tolerance `τ`, deterministically from an explicit horizon on, uniform in the period — no
`δ`, no measure. `schedSurvivors_eq_singleton` reads [SQ] §3.3's `2τ`-pruning rule as an object
(`schedSurvivors`) and shows it isolates the true literal (index `0`) from the same horizon on,
under three named conditions relating the window-noise density `η`, the cross-class trend bound
`μ`, and `τ`.

## Main results

* `scheduleOracle_deterministic` — the deterministic oracle: `SQObjects.IsSQOracle` at every phase
  and every horizon past `(2 * S + Wm) / τ ≤ n`.
* `schedSurvivors` — [SQ] §3.3's `2τ`-pruning rule at the single-literal class, as an object.
  `LearningWitness.witness_truth_survives`'s event is `0 ∈ schedSurvivors τ n o'` here.
* `schedSurvivors_eq_singleton` — the schedule's survivor set is the singleton `{0}` from the
  horizon on, under `2 * η ≤ τ`, `μ ≤ τ`, `3 * τ + μ ≤ 1`.
* `identificationHorizon`, `schedSurvivors_eq_singleton_of_horizon` — the horizon as an explicit
  natural number.
* `sharpHorizon`, `schedSurvivors_eq_singleton_sharp` — the sharp identification window: the same
  conclusion under the honest per-margin hypotheses (`2η ≤ τ`, `μ < 2τ`, `2τ + μ < 1`), at the
  explicit horizon `sharpHorizon`.
* `identifies_of_lt_quarter` — at every density `η < (1 - μ) / 4` with `μ < 1 / 2`, some admissible
  `τ` identifies from `sharpHorizon`'s horizon on.
* `not_identifies_of_gt_quarter` — the converse: past that density, every admissible `τ` leaves a
  wrong literal surviving.

## Scope

Deterministic throughout: `deviation_bound` already delivers the oracle at every phase and every
horizon past the threshold, with no `δ` and no tail. What is proved here is identification — that
the schedule's own `2τ`-pruning rule leaves the true literal alone — and nothing about compute
time, survival, or the bridge between the learning world's count and the guest world's bits. See
[Inevitability] §6 (the affordable-regime paragraph), §5 Proposition 5.9; [SQ] §3.1, §3.3; rows
FV-M, IN-41.
-/

namespace TapeHostSchedule

open TapeHostObservability NoisyWindowChain

variable {N : ℕ} [NeZero N] (o : ZMod N → Bool) {S : ℝ} {ρ W : Fin 8 → ℝ}

/-! ## The deterministic oracle -/

omit [NeZero N] in
/-- **The deterministic oracle.** On any `Profile`, the schedule's own statistic at every offset
`a` is a `SQObjects.IsSQOracle` for the profile's own trend `ρ`, at tolerance `τ`, from the
horizon `(2 * S + Wm) / τ ≤ n` on — one line off `deviation_bound` at `pairChar`
(`pairMean_pairChar`, `pairCoefAB_pairChar`), dividing by `n`. No `δ`: the bound holds at every
phase and every horizon past the threshold, deterministically. -/
theorem scheduleOracle_deterministic (h : Profile o S ρ W) (Wm : ℝ) (hW : ∀ a, W a ≤ Wm)
    (c : ZMod N) {τ : ℝ} (hτ : 0 < τ) {n : ℕ} (hn1 : 1 ≤ n) (hn : (2 * S + Wm) / τ ≤ n) :
    SQObjects.IsSQOracle
      (fun a : Fin 8 => SQOracle.empiricalMean (pairEnsemble pairChar (a : ℕ) 8) n (hostTraj o c))
      (fun a => ρ a) τ := by
  intro a
  have hdb := deviation_bound o h c pairChar abs_pairChar_le_one a hn1
  rw [pairMean_pairChar, pairCoefAB_pairChar, one_mul, zero_add] at hdb
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
  have hle : (2 * S + Wm) ≤ (n : ℝ) * τ := (div_le_iff₀ hτ).mp hn
  have hbound : (n : ℝ) * |SQOracle.empiricalMean (pairEnsemble pairChar (a : ℕ) 8) n
      (hostTraj o c) - ρ a| ≤ (n : ℝ) * τ := by
    have hWa : W a ≤ Wm := hW a
    linarith [hdb, hWa, hle]
  exact le_of_mul_le_mul_left hbound hn0

/-! ## The schedule's pruning rule, and identification -/

open scoped Classical in
/-- **The schedule's `2τ`-pruning rule, as an object.** [SQ] §3.3's rule at the single-literal
class: keep candidate literal `i` exactly when its noise-free answer
`LearningWitness.singleLiteralAns a i` is within `2τ` of the empirical statistic at every
scheduled offset `a`. `LearningWitness.witness_truth_survives`'s event is
`0 ∈ schedSurvivors τ n o'` here — the truth-side half of this rule, at the chain witness rather
than the tape host. -/
noncomputable def schedSurvivors (τ : ℝ) (n : ℕ) (o' : ℕ → Bool) : Finset (Fin 8) :=
  Finset.univ.filter (fun i => ∀ a : Fin 8,
    |LearningWitness.singleLiteralAns a i -
        SQOracle.empiricalMean (pairEnsemble pairChar (a : ℕ) 8) n o'| ≤ 2 * τ)

omit [NeZero N] in
/-- **Identification.** Under the deterministic oracle's own hypotheses, together with the
displacement `ρ 0 = 2 * η - 1` of the true literal's trend by the window-noise density `η`, a
bound `μ` on every other literal's trend, and three named conditions —
`2 * η ≤ τ` (the truth's own noise budget), `μ ≤ τ` (the cross-class budget), and
`3 * τ + μ ≤ 1` (separation from every wrong literal) — the schedule's `2τ`-pruning rule leaves
the true literal `0` alone, from the horizon `(2 * S + Wm) / τ < n` on. The strict horizon is what
makes the wrong-literal exclusion strict at the certified boundary `τ = 1/3`. -/
theorem schedSurvivors_eq_singleton (h : Profile o S ρ W) (Wm : ℝ) (hW : ∀ a, W a ≤ Wm)
    {η τ μ : ℝ} (hτ : 0 < τ) (hη : 0 ≤ η) (hρ0 : ρ 0 = 2 * η - 1)
    (hρ : ∀ a : Fin 8, (a : ℕ) ≠ 0 → |ρ a| ≤ μ) (_hμ0 : 0 ≤ μ)
    (hbudget : 2 * η ≤ τ) (hμτ : μ ≤ τ) (hsep : 3 * τ + μ ≤ 1)
    (c : ZMod N) {n : ℕ} (hn1 : 1 ≤ n) (hn : (2 * S + Wm) / τ < n) :
    schedSurvivors τ n (hostTraj o c) = {0} := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
  have h1 : (2 * S + Wm) < (n : ℝ) * τ := (div_lt_iff₀ hτ).mp hn
  -- the deterministic error at horizon `n`, strictly below `τ`
  have hεlt : (2 * S + Wm) / (n : ℝ) < τ := by
    rw [div_lt_iff₀ hn0]
    nlinarith [h1]
  have hε : ∀ a : Fin 8, |SQOracle.empiricalMean (pairEnsemble pairChar (a : ℕ) 8) n
      (hostTraj o c) - ρ a| ≤ (2 * S + Wm) / (n : ℝ) := by
    intro a
    have hdb := deviation_bound o h c pairChar abs_pairChar_le_one a hn1
    rw [pairMean_pairChar, pairCoefAB_pairChar, one_mul, zero_add] at hdb
    have hWa : W a ≤ Wm := hW a
    rw [le_div_iff₀ hn0]
    nlinarith [hdb, hWa]
  rw [Finset.eq_singleton_iff_unique_mem]
  constructor
  · -- the truth survives
    simp only [schedSurvivors, Finset.mem_filter, Finset.mem_univ, true_and]
    intro a
    by_cases ha0 : a = (0 : Fin 8)
    · subst ha0
      have hlit : LearningWitness.singleLiteralAns (0 : Fin 8) (0 : Fin 8) = -1 := by
        simp [LearningWitness.singleLiteralAns]
      rw [hlit, abs_le]
      obtain ⟨hεl, hεu⟩ := abs_le.mp (hε (0 : Fin 8))
      constructor <;> nlinarith [hεl, hεu, hρ0, hη, hbudget, hεlt]
    · have hane : (a : ℕ) ≠ 0 := by
        intro hcontra
        exact ha0 (by ext; simpa using hcontra)
      have hlit : LearningWitness.singleLiteralAns a (0 : Fin 8) = 0 := by
        unfold LearningWitness.singleLiteralAns
        rw [if_neg ha0]
      rw [hlit, abs_le]
      obtain ⟨hεl, hεu⟩ := abs_le.mp (hε a)
      obtain ⟨hρl, hρu⟩ := abs_le.mp (hρ a hane)
      constructor <;> nlinarith [hεl, hεu, hρl, hρu, hμτ, hεlt]
  · -- every wrong literal is excluded, at its own query
    intro i hi
    by_contra hne
    simp only [schedSurvivors, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    have hane : (i : ℕ) ≠ 0 := by
        intro hcontra
        exact hne (by ext; simpa using hcontra)
    have hlit : LearningWitness.singleLiteralAns i i = -1 := by
      simp [LearningWitness.singleLiteralAns]
    have hb := hi i
    rw [hlit] at hb
    obtain ⟨hεl, hεu⟩ := abs_le.mp (hε i)
    obtain ⟨hρl, hρu⟩ := abs_le.mp (hρ i hane)
    have hx : (-1 : ℝ) - SQOracle.empiricalMean (pairEnsemble pairChar (i : ℕ) 8) n
        (hostTraj o c) < -(2 * τ) := by nlinarith [hεl, hεu, hρl, hρu, hsep, hεlt]
    have : |(-1 : ℝ) - SQOracle.empiricalMean (pairEnsemble pairChar (i : ℕ) 8) n
        (hostTraj o c)| > 2 * τ := by
      rw [abs_of_neg (by linarith [hx] : (-1 : ℝ) - SQOracle.empiricalMean
          (pairEnsemble pairChar (i : ℕ) 8) n (hostTraj o c) < 0)]
      linarith [hx]
    linarith [hb, this]

omit [NeZero N] in
/-- **The identification horizon**, as an explicit natural number: `⌊(2S + Wm)/τ⌋ + 1`, the least
natural strictly above `(2 * S + Wm) / τ`. -/
noncomputable def identificationHorizon (S Wm τ : ℝ) : ℕ := ⌊(2 * S + Wm) / τ⌋₊ + 1

omit [NeZero N] in
/-- `schedSurvivors_eq_singleton`, restated at the explicit horizon: identification holds at
every `n` at least `identificationHorizon S Wm τ`. -/
theorem schedSurvivors_eq_singleton_of_horizon (h : Profile o S ρ W) (Wm : ℝ)
    (hW : ∀ a, W a ≤ Wm) {η τ μ : ℝ} (hτ : 0 < τ) (hη : 0 ≤ η) (hρ0 : ρ 0 = 2 * η - 1)
    (hρ : ∀ a : Fin 8, (a : ℕ) ≠ 0 → |ρ a| ≤ μ) (hμ0 : 0 ≤ μ)
    (hbudget : 2 * η ≤ τ) (hμτ : μ ≤ τ) (hsep : 3 * τ + μ ≤ 1)
    (c : ZMod N) {n : ℕ} (hn1 : 1 ≤ n) (hn : identificationHorizon S Wm τ ≤ n) :
    schedSurvivors τ n (hostTraj o c) = {0} := by
  have hlt : (2 * S + Wm) / τ < (n : ℝ) := by
    have h1 : (2 * S + Wm) / τ < (⌊(2 * S + Wm) / τ⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
    have h2 : ((⌊(2 * S + Wm) / τ⌋₊ : ℝ) + 1) ≤ (n : ℝ) := by
      have hn' : ⌊(2 * S + Wm) / τ⌋₊ + 1 ≤ n := hn
      exact_mod_cast hn'
    linarith
  exact schedSurvivors_eq_singleton o h Wm hW hτ hη hρ0 hρ hμ0 hbudget hμτ hsep c hn1 hlt

/-! ## The sharp identification window -/

omit [NeZero N] in
/-- **The sharp form of identification.** `schedSurvivors_eq_singleton`'s proof closes three
inequalities against the threshold `2τ` — the truth's same-class distance `2η + ε ≤ 2τ`, its
cross-class distances `μ + ε ≤ 2τ`, a wrong literal's own-query distance `1 - μ - ε > 2τ` — and its
landed hypotheses (`2 * η ≤ τ`, `μ ≤ τ`, `3 * τ + μ ≤ 1`, `ε < τ`) meet all three at once by
bounding the deterministic error `ε` against `τ`. Here `ε` is bounded against each margin
separately — the truth's own margin `2τ - 2η`, the cross-class margin `2τ - μ`, a wrong literal's
own-query margin `1 - μ - 2τ` — under the honest hypothesis list `2 * η ≤ τ`, `μ < 2 * τ`,
`2 * τ + μ < 1`; every margin is then positive (the first from `hτ`/`hbudget` alone, since
`2τ - 2η ≥ τ > 0`, needing no separate edge case at `2η = τ`). This gives identification at every
`η < (1 - μ) / 4` with `μ < 1 / 2` (`identifies_of_lt_quarter` below). The landed theorem and its
horizon form stay untouched, byte-identical (cited by row IN-43); this is an addition beside them.
-/
theorem schedSurvivors_eq_singleton_sharp (h : Profile o S ρ W) (Wm : ℝ) (hW : ∀ a, W a ≤ Wm)
    {η τ μ : ℝ} (hτ : 0 < τ) (hη : 0 ≤ η) (hρ0 : ρ 0 = 2 * η - 1)
    (hρ : ∀ a : Fin 8, (a : ℕ) ≠ 0 → |ρ a| ≤ μ) (_hμ0 : 0 ≤ μ)
    (hbudget : 2 * η ≤ τ) (hμτ : μ < 2 * τ) (hsep : 2 * τ + μ < 1)
    (c : ZMod N) {n : ℕ} (hn1 : 1 ≤ n)
    (hn : (2 * S + Wm) / min (2 * τ - 2 * η) (min (2 * τ - μ) (1 - μ - 2 * τ)) < n) :
    schedSurvivors τ n (hostTraj o c) = {0} := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
  have hm1 : (0 : ℝ) < 2 * τ - 2 * η := by linarith
  have hm2 : (0 : ℝ) < 2 * τ - μ := by linarith
  have hm3 : (0 : ℝ) < 1 - μ - 2 * τ := by linarith
  have hmm : (0 : ℝ) < min (2 * τ - 2 * η) (min (2 * τ - μ) (1 - μ - 2 * τ)) :=
    lt_min hm1 (lt_min hm2 hm3)
  have h1 : (2 * S + Wm) < (n : ℝ) * min (2 * τ - 2 * η) (min (2 * τ - μ) (1 - μ - 2 * τ)) :=
    (div_lt_iff₀ hmm).mp hn
  have heps : (2 * S + Wm) / (n : ℝ) <
      min (2 * τ - 2 * η) (min (2 * τ - μ) (1 - μ - 2 * τ)) := by
    rw [div_lt_iff₀ hn0]
    nlinarith [h1]
  have hlt1 : (2 * S + Wm) / (n : ℝ) < 2 * τ - 2 * η :=
    lt_of_lt_of_le heps (min_le_left _ _)
  have hlt2 : (2 * S + Wm) / (n : ℝ) < 2 * τ - μ :=
    lt_of_lt_of_le heps (le_trans (min_le_right _ _) (min_le_left _ _))
  have hlt3 : (2 * S + Wm) / (n : ℝ) < 1 - μ - 2 * τ :=
    lt_of_lt_of_le heps (le_trans (min_le_right _ _) (min_le_right _ _))
  have hε : ∀ a : Fin 8, |SQOracle.empiricalMean (pairEnsemble pairChar (a : ℕ) 8) n
      (hostTraj o c) - ρ a| ≤ (2 * S + Wm) / (n : ℝ) := by
    intro a
    have hdb := deviation_bound o h c pairChar abs_pairChar_le_one a hn1
    rw [pairMean_pairChar, pairCoefAB_pairChar, one_mul, zero_add] at hdb
    have hWa : W a ≤ Wm := hW a
    rw [le_div_iff₀ hn0]
    nlinarith [hdb, hWa]
  rw [Finset.eq_singleton_iff_unique_mem]
  constructor
  · -- the truth survives
    simp only [schedSurvivors, Finset.mem_filter, Finset.mem_univ, true_and]
    intro a
    by_cases ha0 : a = (0 : Fin 8)
    · subst ha0
      have hlit : LearningWitness.singleLiteralAns (0 : Fin 8) (0 : Fin 8) = -1 := by
        simp [LearningWitness.singleLiteralAns]
      rw [hlit, abs_le]
      obtain ⟨hεl, hεu⟩ := abs_le.mp (hε (0 : Fin 8))
      constructor <;> nlinarith [hεl, hεu, hρ0, hη, hlt1]
    · have hane : (a : ℕ) ≠ 0 := by
        intro hcontra
        exact ha0 (by ext; simpa using hcontra)
      have hlit : LearningWitness.singleLiteralAns a (0 : Fin 8) = 0 := by
        unfold LearningWitness.singleLiteralAns
        rw [if_neg ha0]
      rw [hlit, abs_le]
      obtain ⟨hεl, hεu⟩ := abs_le.mp (hε a)
      obtain ⟨hρl, hρu⟩ := abs_le.mp (hρ a hane)
      constructor <;> nlinarith [hεl, hεu, hρl, hρu, hlt2]
  · -- every wrong literal is excluded, at its own query
    intro i hi
    by_contra hne
    simp only [schedSurvivors, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    have hane : (i : ℕ) ≠ 0 := by
        intro hcontra
        exact hne (by ext; simpa using hcontra)
    have hlit : LearningWitness.singleLiteralAns i i = -1 := by
      simp [LearningWitness.singleLiteralAns]
    have hb := hi i
    rw [hlit] at hb
    obtain ⟨hεl, hεu⟩ := abs_le.mp (hε i)
    obtain ⟨hρl, hρu⟩ := abs_le.mp (hρ i hane)
    have hx : (-1 : ℝ) - SQOracle.empiricalMean (pairEnsemble pairChar (i : ℕ) 8) n
        (hostTraj o c) < -(2 * τ) := by nlinarith [hεl, hεu, hρl, hρu, hlt3]
    have : |(-1 : ℝ) - SQOracle.empiricalMean (pairEnsemble pairChar (i : ℕ) 8) n
        (hostTraj o c)| > 2 * τ := by
      rw [abs_of_neg (by linarith [hx] : (-1 : ℝ) - SQOracle.empiricalMean
          (pairEnsemble pairChar (i : ℕ) 8) n (hostTraj o c) < 0)]
      linarith [hx]
    linarith [hb, this]

/-- **The sharp identification horizon**, as an explicit natural number: the least natural
strictly above `(2S + Wm)` divided by the smallest of the three margins
(`2τ − 2η`, `2τ − μ`, `1 − μ − 2τ`). -/
noncomputable def sharpHorizon (S Wm η τ μ : ℝ) : ℕ :=
  ⌊(2 * S + Wm) / min (2 * τ - 2 * η) (min (2 * τ - μ) (1 - μ - 2 * τ))⌋₊ + 1

/-- `sharpHorizon` is always at least `1`. -/
private theorem one_le_sharpHorizon (S Wm η τ μ : ℝ) : 1 ≤ sharpHorizon S Wm η τ μ :=
  Nat.le_add_left 1 _

omit [NeZero N] in
/-- `schedSurvivors_eq_singleton_sharp`, restated at the explicit horizon: the sharp
identification holds at every `n` at least `sharpHorizon S Wm η τ μ`. -/
private theorem schedSurvivors_eq_singleton_sharp_of_horizon (h : Profile o S ρ W) (Wm : ℝ)
    (hW : ∀ a, W a ≤ Wm) {η τ μ : ℝ} (hτ : 0 < τ) (hη : 0 ≤ η) (hρ0 : ρ 0 = 2 * η - 1)
    (hρ : ∀ a : Fin 8, (a : ℕ) ≠ 0 → |ρ a| ≤ μ) (hμ0 : 0 ≤ μ)
    (hbudget : 2 * η ≤ τ) (hμτ : μ < 2 * τ) (hsep : 2 * τ + μ < 1)
    (c : ZMod N) {n : ℕ} (hn1 : 1 ≤ n) (hn : sharpHorizon S Wm η τ μ ≤ n) :
    schedSurvivors τ n (hostTraj o c) = {0} := by
  have hlt : (2 * S + Wm) / min (2 * τ - 2 * η) (min (2 * τ - μ) (1 - μ - 2 * τ)) < (n : ℝ) := by
    have h1 : (2 * S + Wm) / min (2 * τ - 2 * η) (min (2 * τ - μ) (1 - μ - 2 * τ)) <
        (⌊(2 * S + Wm) / min (2 * τ - 2 * η) (min (2 * τ - μ) (1 - μ - 2 * τ))⌋₊ : ℝ) + 1 :=
      Nat.lt_floor_add_one _
    have h2 : ((⌊(2 * S + Wm) / min (2 * τ - 2 * η) (min (2 * τ - μ) (1 - μ - 2 * τ))⌋₊ : ℝ) + 1)
        ≤ (n : ℝ) := by
      have hn' : ⌊(2 * S + Wm) / min (2 * τ - 2 * η) (min (2 * τ - μ) (1 - μ - 2 * τ))⌋₊ + 1
          ≤ n := hn
      exact_mod_cast hn'
    linarith
  exact schedSurvivors_eq_singleton_sharp o h Wm hW hτ hη hρ0 hρ hμ0 hbudget hμτ hsep c hn1 hlt

omit [NeZero N] in
/-- **The sharp identification window.** At every density `η < (1 - μ) / 4` with `μ < 1 / 2`,
some admissible tolerance `τ` (with `2 * η ≤ τ`) identifies the true literal from
`sharpHorizon`'s horizon on — the schedule's own limit under [SQ] §3.1's budget and §3.3's `2τ`
rule. The certified block-pair design (`τ = 1/3`, `η = 1/6`, `μ = 0`) sits inside this window; see
`BlockPairCriterion.blockPair_identifies`. -/
theorem identifies_of_lt_quarter (h : Profile o S ρ W) (Wm : ℝ) (hW : ∀ a, W a ≤ Wm)
    {η μ : ℝ} (hη : 0 ≤ η) (hρ0 : ρ 0 = 2 * η - 1) (hρ : ∀ a : Fin 8, (a : ℕ) ≠ 0 → |ρ a| ≤ μ)
    (hμ0 : 0 ≤ μ) (hμ : μ < 1 / 2) (hwin : η < (1 - μ) / 4) (c : ZMod N) :
    ∃ τ : ℝ, 0 < τ ∧ 2 * η ≤ τ ∧
      ∀ n : ℕ, sharpHorizon S Wm η τ μ ≤ n → schedSurvivors τ n (hostTraj o c) = {0} := by
  have hA1 : 2 * η ≤ max (2 * η) (μ / 2) := le_max_left _ _
  have hA2 : μ / 2 ≤ max (2 * η) (μ / 2) := le_max_right _ _
  have hAB : max (2 * η) (μ / 2) < (1 - μ) / 2 :=
    max_lt (by linarith [hwin]) (by linarith [hμ])
  refine ⟨(max (2 * η) (μ / 2) + (1 - μ) / 2) / 2, by linarith, by linarith, fun n hn => ?_⟩
  have hn1 : 1 ≤ n :=
    le_trans (one_le_sharpHorizon S Wm η ((max (2 * η) (μ / 2) + (1 - μ) / 2) / 2) μ) hn
  exact schedSurvivors_eq_singleton_sharp_of_horizon o h Wm hW (by linarith) hη hρ0 hρ hμ0
    (by linarith) (by linarith) (by linarith) c hn1 hn

omit [NeZero N] in
/-- **The converse: at every density above the window, no admissible tolerance identifies.**
Under [SQ] §3.1's budget `2 * η ≤ τ`, once the density exceeds the schedule's own limit
(`1 / 4 < η`, at the cross-class trends all `0`) every admissible tolerance forces `2 * τ > 1`,
and every wrong literal's own-query distance is then at most `1 + ε ≤ 2τ`: the wrong literal
survives, so the pruning rule fails to identify. Stated over wrong literals (`(j : ℕ) ≠ 0`) alone
— one surviving wrong literal already witnesses `schedSurvivors τ n (hostTraj o c) ≠ {0}`, which
is the refutation's content; the truth's own membership is not claimed at every `η` (an adversarial
deviation within the profile's own bound can push the true literal's own query past `2τ` once `η`
runs unboundedly above `1`, which the profile's hypotheses alone do not exclude), so `hη1 : η ≤ 1`
is carried as a named hypothesis — `η` is a density and this is its natural range, and it is what
keeps the wrong-literal statement below true and general rather than an artifact of one instance.
-/
theorem not_identifies_of_gt_quarter (h : Profile o S ρ W) (Wm : ℝ) (hW : ∀ a, W a ≤ Wm)
    {η τ : ℝ} (hη4 : 1 / 4 < η) (hη1 : η ≤ 1) (hρ0 : ρ 0 = 2 * η - 1)
    (hρ0' : ∀ a : Fin 8, (a : ℕ) ≠ 0 → ρ a = 0) (hbudget : 2 * η ≤ τ) (c : ZMod N) {n : ℕ}
    (hn1 : 1 ≤ n) (hn : (2 * S + Wm) / (2 * τ - 1) < n) :
    ∀ j : Fin 8, (j : ℕ) ≠ 0 → j ∈ schedSurvivors τ n (hostTraj o c) := by
  have h2τ1 : (0 : ℝ) < 2 * τ - 1 := by linarith
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
  have h1 : (2 * S + Wm) < (n : ℝ) * (2 * τ - 1) := (div_lt_iff₀ h2τ1).mp hn
  have hεlt : (2 * S + Wm) / (n : ℝ) < 2 * τ - 1 := by
    rw [div_lt_iff₀ hn0]
    nlinarith [h1]
  have hε : ∀ a : Fin 8, |SQOracle.empiricalMean (pairEnsemble pairChar (a : ℕ) 8) n
      (hostTraj o c) - ρ a| ≤ (2 * S + Wm) / (n : ℝ) := by
    intro a
    have hdb := deviation_bound o h c pairChar abs_pairChar_le_one a hn1
    rw [pairMean_pairChar, pairCoefAB_pairChar, one_mul, zero_add] at hdb
    have hWa : W a ≤ Wm := hW a
    rw [le_div_iff₀ hn0]
    nlinarith [hdb, hWa]
  intro j hjne
  simp only [schedSurvivors, Finset.mem_filter, Finset.mem_univ, true_and]
  intro a
  by_cases haj : a = j
  · subst haj
    have hlit : LearningWitness.singleLiteralAns a a = -1 := by
      simp [LearningWitness.singleLiteralAns]
    rw [hlit, abs_le]
    obtain ⟨hεl, hεu⟩ := abs_le.mp (hε a)
    have hρa : ρ a = 0 := hρ0' a hjne
    constructor <;> nlinarith [hεl, hεu, hρa, hεlt]
  · have hlit : LearningWitness.singleLiteralAns a j = 0 := by
      unfold LearningWitness.singleLiteralAns
      rw [if_neg haj]
    rw [hlit, abs_le]
    by_cases ha0 : a = (0 : Fin 8)
    · subst ha0
      obtain ⟨hεl, hεu⟩ := abs_le.mp (hε (0 : Fin 8))
      constructor <;> nlinarith [hεl, hεu, hρ0, hη4, hη1, hεlt]
    · have hane : (a : ℕ) ≠ 0 := by
        intro hcontra
        exact ha0 (by ext; simpa using hcontra)
      have hρa : ρ a = 0 := hρ0' a hane
      obtain ⟨hεl, hεu⟩ := abs_le.mp (hε a)
      constructor <;> nlinarith [hεl, hεu, hρa, hεlt]

end TapeHostSchedule
