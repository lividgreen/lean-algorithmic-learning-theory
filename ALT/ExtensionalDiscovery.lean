/-
Copyright (c) 2026 Mykola Palamarchuk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mykola Palamarchuk
-/
import Mathlib.Analysis.Normed.Group.Indicator
import Mathlib.Analysis.Normed.Group.Tannery

-- Formal-check file, not Mathlib-destined: opt out of the house-style linters.
set_option linter.style.header false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

/-!
# Extensional `[R]`-concentration — [Discovery] Proposition 3.2 over the near-twin-rich countable class

Provenance: [Discovery] §3.3, **Proposition 3.2**. This is the honest,
non-vacuous countable-class discovery statement that *drops per-step separation entirely* (so it is
non-empty on exactly the all-programs class where the per-step-separated `CountableDiscovery.countable_discovery`
is vacuous). It is a **fresh development** — indicator likelihoods, no separation — not an extension
of `ALT/CountableDiscovery.lean`; it reuses only that file's Kraft-summable-prior *pattern*
(`Summable w`, `∑' w ≤ 1` is not even needed — the tail is dominated by `w` directly).

## The statement
In the realizable deterministic case the likelihood of a hypothesis `i` after `n` observations is the
`0/1` indicator `L_i(n) = 1[i consistent with o_{1:n}]`. The on-trajectory equivalence class is
`[R] = {i : ∀ n, consistent i n}` (`inR`). The prequential-MDL posterior on `[R]`,
`postR n = P_{[R]} / Z_n` with `Z_n = P_{[R]} + tail_n`, rises monotonically to `1`:
* `Zmass_eq_PR_add_tail` — `Z_n = P_{[R]} + tail_n` (the consistent set splits as `[R] ⊔ (consistent ∖ [R])`);
* `tail_tendsto_zero` — the crux: every off-`[R]` competitor is falsified at a finite branching time,
  so `tail_n → 0` (dominated convergence against the summable prior `w`);
* `postR_monotone` — `postR` is monotone (`tail` is antitone in `n`);
* `postR_tendsto_one` / `extensional_R_concentration` — the capstone `postR n ↗ 1`.

## What is PROVED (no `sorry`, no deep import)
The whole of Proposition 3.2, from **only** the model hypotheses: `0 ≤ w`, `Summable w`, antitone
consistency (`m ≤ n → consistent i n → consistent i m` — "once falsified, always falsified"), and a
true rule `R ∈ [R]` with `0 < w R`. No separation hypothesis of any kind. `ι` stays a general
`Type*` (a genuinely countable class); there is **no** `[Fintype ι]`. Classical indicators
(`Set.indicator`) make `Classical.choice` an expected member of the axiom set.
-/

namespace ExtensionalDiscovery

open scoped BigOperators Topology
open Filter

variable {ι : Type*}

/-- Membership in the on-trajectory equivalence class `[R]`: `i` reproduces the trajectory forever. -/
def inR (consistent : ι → ℕ → Prop) (i : ι) : Prop := ∀ n, consistent i n

/-- Surviving mixture mass `Z_n = ∑'_i 1[i consistent with o_{1:n}]·w_i`: total prior of hypotheses
still consistent with the first `n` observations (the normalizer of the indicator likelihood). -/
noncomputable def Zmass (w : ι → ℝ) (consistent : ι → ℕ → Prop) (n : ℕ) : ℝ :=
  ∑' i, {i | consistent i n}.indicator w i

/-- Prior mass `P_{[R]} = ∑'_{i ∈ [R]} w_i` of the equivalence class `[R]`. -/
noncomputable def PR (w : ι → ℝ) (consistent : ι → ℕ → Prop) : ℝ :=
  ∑' i, {i | inR consistent i}.indicator w i

/-- Surviving off-`[R]` mass `tail_n = ∑'_{i ∉ [R], consistent at n} w_i`. -/
noncomputable def tail (w : ι → ℝ) (consistent : ι → ℕ → Prop) (n : ℕ) : ℝ :=
  ∑' i, {i | consistent i n ∧ ¬ inR consistent i}.indicator w i

/-- Posterior mass on `[R]` at step `n`: `postR n = P_{[R]} / Z_n`. (Numerator is `P_{[R]}` because
every member of `[R]` has indicator likelihood `1` at every `n`.) -/
noncomputable def postR (w : ι → ℝ) (consistent : ι → ℕ → Prop) (n : ℕ) : ℝ :=
  PR w consistent / Zmass w consistent n

variable {w : ι → ℝ} {consistent : ι → ℕ → Prop}

/-! ## Summability of the three indicator families (all dominated by the Kraft-summable prior `w`) -/

lemma summable_consistent (hsumw : Summable w) (n : ℕ) :
    Summable ({i | consistent i n}.indicator w) :=
  hsumw.indicator _

lemma summable_inR (hsumw : Summable w) :
    Summable ({i | inR consistent i}.indicator w) :=
  hsumw.indicator _

lemma summable_tail (hsumw : Summable w) (n : ℕ) :
    Summable ({i | consistent i n ∧ ¬ inR consistent i}.indicator w) :=
  hsumw.indicator _

/-! ## Step 1 — the normalizer splits: `Z_n = P_{[R]} + tail_n` -/

/-- **`Z_n = P_{[R]} + tail_n`.** The consistent set splits as the disjoint union
`[R] ⊔ (consistent-at-`n` ∖ [R])` (using `[R] ⊆ consistent-at-`n``, since a member of `[R]` is
consistent at every step), so the indicator likelihood mass splits into the class mass and the
surviving off-`[R]` mass. -/
theorem Zmass_eq_PR_add_tail (hsumw : Summable w) (n : ℕ) :
    Zmass w consistent n = PR w consistent + tail w consistent n := by
  unfold Zmass PR tail
  rw [← Summable.tsum_add (summable_inR hsumw) (summable_tail hsumw n)]
  refine tsum_congr (fun i => ?_)
  by_cases hinr : inR consistent i
  · rw [Set.indicator_of_mem (show i ∈ {i | consistent i n} from hinr n),
        Set.indicator_of_mem (show i ∈ {i | inR consistent i} from hinr),
        Set.indicator_of_notMem (show i ∉ {i | consistent i n ∧ ¬ inR consistent i} from
          fun h => h.2 hinr), add_zero]
  · by_cases hcon : consistent i n
    · rw [Set.indicator_of_mem (show i ∈ {i | consistent i n} from hcon),
          Set.indicator_of_notMem (show i ∉ {i | inR consistent i} from hinr),
          Set.indicator_of_mem (show i ∈ {i | consistent i n ∧ ¬ inR consistent i} from
            ⟨hcon, hinr⟩), zero_add]
    · rw [Set.indicator_of_notMem (show i ∉ {i | consistent i n} from hcon),
          Set.indicator_of_notMem (show i ∉ {i | inR consistent i} from hinr),
          Set.indicator_of_notMem (show i ∉ {i | consistent i n ∧ ¬ inR consistent i} from
            fun h => hcon h.1), add_zero]

/-- Rewriting of `postR` via the split normalizer: `postR n = P_{[R]} / (P_{[R]} + tail_n)`. -/
theorem postR_eq (hsumw : Summable w) (n : ℕ) :
    postR w consistent n = PR w consistent / (PR w consistent + tail w consistent n) := by
  rw [postR, Zmass_eq_PR_add_tail hsumw]

/-! ## Step 3 — the class mass is a positive constant: `0 < P_{[R]}` -/

/-- **`0 < P_{[R]}`.** Single-term lower bound: the true rule `R ∈ [R]` contributes `w R > 0`, and
every term of the nonneg summable family is `≥ 0`, so `P_{[R]} ≥ w R > 0`. -/
theorem PR_pos (hw : ∀ i, 0 ≤ w i) (hsumw : Summable w) {R : ι}
    (hR : inR consistent R) (hwR : 0 < w R) : 0 < PR w consistent := by
  have hle : {i | inR consistent i}.indicator w R ≤ PR w consistent :=
    Summable.le_tsum (summable_inR hsumw) R (fun b _ => Set.indicator_nonneg (fun a _ => hw a) b)
  rw [Set.indicator_of_mem (show R ∈ {i | inR consistent i} from hR)] at hle
  exact lt_of_lt_of_le hwR hle

/-! ## Step 4 — the crux: `tail_n → 0` (finite branching times + dominated convergence) -/

/-- **`tail_n → 0`.** For each fixed competitor `i`: if `i ∈ [R]` its tail term is identically `0`
(the `¬ inR` conjunct fails); if `i ∉ [R]` it is falsified at a finite branching time `N` and, by
antitone consistency, stays falsified, so its tail term is *eventually* `0`. Either way the term
tends to `0` and is dominated by the summable prior `w`; dominated convergence for `tsum`
(`tendsto_tsum_of_dominated_convergence`) gives `tail_n → ∑'_i 0 = 0`. No separation hypothesis. -/
theorem tail_tendsto_zero (hw : ∀ i, 0 ≤ w i) (hsumw : Summable w)
    (hanti : ∀ i m n, m ≤ n → consistent i n → consistent i m) :
    Tendsto (tail w consistent) atTop (𝓝 0) := by
  have hlim : ∀ i, Tendsto (fun n => {i | consistent i n ∧ ¬ inR consistent i}.indicator w i)
      atTop (𝓝 (0 : ℝ)) := by
    intro i
    by_cases hinr : inR consistent i
    · -- `i ∈ [R]`: the tail term is identically `0`.
      have h0 : (fun n => {i | consistent i n ∧ ¬ inR consistent i}.indicator w i)
          = fun _ => (0 : ℝ) :=
        funext fun n => Set.indicator_of_notMem (fun h => h.2 hinr) w
      rw [h0]; exact tendsto_const_nhds
    · -- `i ∉ [R]`: falsified at a finite `N`, hence eventually `0`.
      obtain ⟨N, hN⟩ : ∃ N, ¬ consistent i N := by
        simp only [inR, not_forall] at hinr; exact hinr
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [Filter.eventually_ge_atTop N] with n hn
      exact (Set.indicator_of_notMem (fun h => hN (hanti i N n hn h.1)) w).symm
  have hdom : ∀ n i, ‖{i | consistent i n ∧ ¬ inR consistent i}.indicator w i‖ ≤ w i := by
    intro n i
    calc ‖{i | consistent i n ∧ ¬ inR consistent i}.indicator w i‖
        ≤ ‖w i‖ := norm_indicator_le_norm_self _ _
      _ = w i := Real.norm_of_nonneg (hw i)
  have key := tendsto_tsum_of_dominated_convergence hsumw hlim (Filter.Eventually.of_forall hdom)
  simp only [tsum_zero] at key
  unfold tail
  exact key

/-! ## Step 6 — `tail` is antitone (monotone posterior) -/

/-- **`tail` antitone in `n`.** The consistent-at-`n` set shrinks with `n` (antitone consistency),
so the surviving off-`[R]` set shrinks and its nonneg-weighted mass is non-increasing. -/
theorem tail_antitone (hw : ∀ i, 0 ≤ w i) (hsumw : Summable w)
    (hanti : ∀ i m n, m ≤ n → consistent i n → consistent i m) :
    Antitone (tail w consistent) := by
  intro m n hmn
  have hsub : {i | consistent i n ∧ ¬ inR consistent i}
      ⊆ {i | consistent i m ∧ ¬ inR consistent i} :=
    fun j hj => ⟨hanti j m n hmn hj.1, hj.2⟩
  unfold tail
  refine Summable.tsum_le_tsum (fun i => ?_) (summable_tail hsumw n) (summable_tail hsumw m)
  exact Set.indicator_le_indicator_of_subset hsub (fun a => hw a) i

lemma tail_nonneg (hw : ∀ i, 0 ≤ w i) (n : ℕ) : 0 ≤ tail w consistent n := by
  unfold tail
  exact tsum_nonneg (fun i => Set.indicator_nonneg (fun a _ => hw a) i)

/-- **`postR` is monotone.** `postR n = P_{[R]}/(P_{[R]} + tail_n)` with `P_{[R]} > 0` fixed and
`tail` antitone and `≥ 0`, so the denominator is antitone and positive and the ratio is monotone. -/
theorem postR_monotone (hw : ∀ i, 0 ≤ w i) (hsumw : Summable w)
    (hanti : ∀ i m n, m ≤ n → consistent i n → consistent i m)
    {R : ι} (hR : inR consistent R) (hwR : 0 < w R) :
    Monotone (postR w consistent) := by
  have hPR : 0 < PR w consistent := PR_pos hw hsumw hR hwR
  have hta : Antitone (tail w consistent) := tail_antitone hw hsumw hanti
  intro m n hmn
  rw [postR_eq hsumw, postR_eq hsumw]
  have hdn : 0 < PR w consistent + tail w consistent n :=
    add_pos_of_pos_of_nonneg hPR (tail_nonneg hw n)
  exact div_le_div_of_nonneg_left hPR.le hdn (by linarith [hta hmn])

/-! ## Capstone — Proposition 3.2 -/

/-- **The posterior on `[R]` rises to `1`: `postR n → 1`.** The denominator `P_{[R]} + tail_n →
P_{[R]} ≠ 0` (step 4), and the constant numerator `P_{[R]}` gives `postR n → P_{[R]}/P_{[R]} = 1`. -/
theorem postR_tendsto_one (hw : ∀ i, 0 ≤ w i) (hsumw : Summable w)
    (hanti : ∀ i m n, m ≤ n → consistent i n → consistent i m)
    {R : ι} (hR : inR consistent R) (hwR : 0 < w R) :
    Tendsto (postR w consistent) atTop (𝓝 1) := by
  have hPR : 0 < PR w consistent := PR_pos hw hsumw hR hwR
  have htail : Tendsto (tail w consistent) atTop (𝓝 0) := tail_tendsto_zero hw hsumw hanti
  have hden : Tendsto (fun n => PR w consistent + tail w consistent n) atTop
      (𝓝 (PR w consistent)) := by simpa using htail.const_add (PR w consistent)
  have hdiv : Tendsto (fun n => PR w consistent / (PR w consistent + tail w consistent n))
      atTop (𝓝 (PR w consistent / PR w consistent)) :=
    tendsto_const_nhds.div hden (ne_of_gt hPR)
  rw [div_self (ne_of_gt hPR)] at hdiv
  have heq : postR w consistent
      = fun n => PR w consistent / (PR w consistent + tail w consistent n) :=
    funext (fun n => postR_eq hsumw n)
  rw [heq]; exact hdiv

/-- **Proposition 3.2 (Extensional `[R]`-concentration).** For the countable class in the realizable
deterministic setting with the Kraft-summable prior `w`, dropping per-step separation entirely: the
prequential-MDL posterior mass on the on-trajectory equivalence class `[R]` **rises monotonically to
`1`** — unconditionally, from only `0 ≤ w`, `Summable w`, antitone consistency, and a true rule
`R ∈ [R]` with `0 < w R`. No separation hypothesis; `ι` a general countable `Type*`. -/
theorem extensional_R_concentration (hw : ∀ i, 0 ≤ w i) (hsumw : Summable w)
    (hanti : ∀ i m n, m ≤ n → consistent i n → consistent i m)
    {R : ι} (hR : inR consistent R) (hwR : 0 < w R) :
    Monotone (postR w consistent) ∧ Tendsto (postR w consistent) atTop (𝓝 1) :=
  ⟨postR_monotone hw hsumw hanti hR hwR, postR_tendsto_one hw hsumw hanti hR hwR⟩

end ExtensionalDiscovery
