/-
Copyright (c) 2026 Mykola Palamarchuk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mykola Palamarchuk
-/
import Mathlib
import ALT.SQSearchPhaseMass

-- Formal-check file, not Mathlib-destined: opt out of the house-style linters (long doc lines).
set_option linter.style.header false
set_option linter.style.longLine false

/-!
# The mixture mass `Z_t` as a genuine supermartingale ([SQ] Appendix A, FV-I)

Provenance: [SQ], Appendix A: "Ville's inequality: the likelihood
ratio is a non-negative supermartingale under realizability", with `Z_t = ∑ w(R')·L_t(R')` and
`𝔼[Z_0] ≤ 1` by Kraft. This is exactly the premise FV-G's chained theorem
(`SQSearchPhaseMass.search_phase_mass_ville_chain`, `ALT/SQSearchPhaseMass.lean`) still carries
as `hsuper : Supermartingale Z ℱ μ`. FV-I **constructs** that `Z` on a trajectory space, discharging
the premise for the paper's realizable-deterministic regime ([Discovery] §3): candidates are
deterministic rules, the truth predicts the realized symbol with probability 1, so each per-step
likelihood factor of a candidate lies in `[0,1]` and `L_t(R') = ∏_{s<t} (factor s)`.

## Key design fact (why this needs no Ionescu–Tulcea construction)
With factors in `[0,1]`, `L_t` — hence `Z_t` — is pointwise NON-INCREASING in `t`. A
pointwise-antitone, adapted, bounded non-negative process is a supermartingale for ANY probability
measure: `μ[Z_j | ℱ_i] ≤ μ[Z_i | ℱ_i] = Z_i` by `condExp_mono` plus `condExp_of_stronglyMeasurable`.
So the truth's law stays an ARBITRARY probability measure on `ℕ → X`; no product-measure /
`Kernel.traj` machinery is needed. The stochastic-truth case (a genuine martingale argument) is
explicitly out of scope (Grünwald–Mehta stochastic case).

Filtration: Mathlib's `MeasureTheory.Filtration.piLE` on `ℕ → X` — `piLE i` is the σ-algebra of
events depending only on coordinates `≤ i`. FOUND in Mathlib (not hand-rolled).

## What this DOES establish
* `coordFil` — the coordinate filtration on the trajectory space `ℕ → X` (a thin wrapper over
  `Filtration.piLE`).
* `Z_nonneg`, `Z_le_one`, `Z_antitone` — `Z_t ∈ [0, ∑ w] ⊆ [0,1]` (Kraft) and pointwise antitone.
* `Z_stronglyAdapted` — `Z` is adapted to `coordFil` (each factor is `ℱ_{s+1}`-measurable).
* `Z_supermartingale` — `Z` is a genuine `MeasureTheory.Supermartingale` for ANY probability truth
  law `μ`, via the antitone + bounded + adapted route.
* `integral_Z_zero_le_one` — `𝔼[Z_0] ≤ 1` from Kraft (`Z_0 = ∑ w` is constant).
* `search_phase_mass_bound` — the FV-G chain instantiated at this constructed `Z`: the
  supermartingale / nonnegativity / `𝔼[Z_0]≤1` premises are DISCHARGED, leaving only the FV-G
  search-side data (`pruned`, `m`, `Φ`, `hcharge`).
* `detFactor`, `detFactor_mem_Icc`, `detFactor_stronglyMeasurable`, `L_det_eq_indicator`,
  `Z_det_supermartingale` — the abstract factor `g` made CONCRETE for the
  paper's DETERMINISTIC rule class: `detFactor pred i s ω = 𝟙[pred i s (ω|_{<s}) = ω s]` is the
  `0/1` likelihood of a deterministic rule, its `ℱ_{s+1}`-strong measurability is PROVED from
  `Filtration.piLE`'s coordinate structure over a discrete alphabet (no longer a named hypothesis),
  `L_det` is literally the alive-consistent indicator, and `Z_det_supermartingale` is a genuine
  supermartingale with NO abstract-`g` hypotheses — only the deterministic `pred`, weights, Kraft.

## What this does NOT establish (out of scope; no overclaiming)
* Not the stochastic-truth martingale (Grünwald–Mehta stochastic case): the
  antitone shortcut is specific to the deterministic regime's `[0,1]` factors.
* Not the countable candidate class: `cands` is a `Finset` (matching the FV-F/G/H pruning
  apparatus); the countable extension mirrors `CountableDiscovery`, recorded as residue.
* Not identifying the deterministic rule `pred` with the actual prequential-MDL algorithm's rule
  dynamics: `detFactor` genuinely instantiates the `[0,1]`-valued,
  `ℱ_{s+1}`-measurable factor for deterministic rules (closing the FV-I measurability residue), but
  which `pred` the algorithm emits is the algorithm-layer identification, still ahead.
* Not the Kraft bound's origin ([Discovery] `PriorNormalization`/`PrefixComplexity`): imported here as
  the hypothesis `hkraft : ∑ w ≤ 1`.
-/

namespace SQMixtureSupermartingale

open MeasureTheory
open scoped ProbabilityTheory

/-- The coordinate filtration on the trajectory space `ℕ → X` (Mathlib's `Filtration.piLE`):
`coordFil X n` is the σ-algebra of events depending only on coordinates `≤ n`. -/
abbrev coordFil (X : Type*) [MeasurableSpace X] :
    Filtration ℕ (inferInstance : MeasurableSpace (ℕ → X)) :=
  Filtration.piLE (X := fun _ : ℕ => X)

section Construction

variable {X : Type*} [MeasurableSpace X] {ι : Type*}
  (cands : Finset ι) (w : ι → ℝ) (g : ι → ℕ → (ℕ → X) → ℝ)

/-- Candidate `i`'s likelihood up to time `t`: the product of its per-step factors. -/
def L (i : ι) (t : ℕ) (ω : ℕ → X) : ℝ := ∏ s ∈ Finset.range t, g i s ω

/-- The prequential mixture mass `Z_t = ∑_{i ∈ cands} w(i)·L_i(t)`. -/
def Z (t : ℕ) (ω : ℕ → X) : ℝ := ∑ i ∈ cands, w i * L g i t ω

variable {μ : Measure (ℕ → X)}
  (hw : ∀ i ∈ cands, 0 ≤ w i) (hkraft : ∑ i ∈ cands, w i ≤ 1)
  (hg01 : ∀ i s ω, g i s ω ∈ Set.Icc (0 : ℝ) 1)
  (hgmeas : ∀ i s, StronglyMeasurable[coordFil X (s + 1)] (g i s))

omit [MeasurableSpace X] in
include hw hg01 in
/-- `Z_t ≥ 0`: a nonnegative-weighted sum of products of nonnegative factors. -/
theorem Z_nonneg (t : ℕ) (ω : ℕ → X) : 0 ≤ Z cands w g t ω :=
  Finset.sum_nonneg fun i hi =>
    mul_nonneg (hw i hi) (Finset.prod_nonneg fun s _ => (hg01 i s ω).1)

omit [MeasurableSpace X] in
include hw hkraft hg01 in
/-- `Z_t ≤ ∑ w ≤ 1`: each likelihood is `≤ 1` (product of `[0,1]` factors), then Kraft. -/
theorem Z_le_one (t : ℕ) (ω : ℕ → X) : Z cands w g t ω ≤ 1 := by
  have hterm : ∀ i ∈ cands, w i * L g i t ω ≤ w i := by
    intro i hi
    have hL1 : L g i t ω ≤ 1 :=
      Finset.prod_le_one (fun s _ => (hg01 i s ω).1) (fun s _ => (hg01 i s ω).2)
    calc w i * L g i t ω ≤ w i * 1 := mul_le_mul_of_nonneg_left hL1 (hw i hi)
      _ = w i := mul_one _
  calc Z cands w g t ω = ∑ i ∈ cands, w i * L g i t ω := rfl
    _ ≤ ∑ i ∈ cands, w i := Finset.sum_le_sum hterm
    _ ≤ 1 := hkraft

omit [MeasurableSpace X] in
include hw hg01 in
/-- `Z` is pointwise non-increasing: appending a `[0,1]` factor cannot increase any likelihood. -/
theorem Z_antitone (ω : ℕ → X) : Antitone fun t => Z cands w g t ω := by
  refine antitone_nat_of_succ_le fun t => ?_
  refine Finset.sum_le_sum fun i hi => ?_
  have hLnn : 0 ≤ L g i t ω := Finset.prod_nonneg fun s _ => (hg01 i s ω).1
  have hstep : L g i (t + 1) ω = L g i t ω * g i t ω := by
    simp only [L, Finset.prod_range_succ]
  rw [hstep]
  exact mul_le_mul_of_nonneg_left (mul_le_of_le_one_right hLnn (hg01 i t ω).2) (hw i hi)

include hgmeas in
/-- `Z` is strongly adapted to the coordinate filtration: the factor `g i s` looks only at
coordinates `≤ s + 1`, and for `s < t` that σ-algebra sits inside `coordFil X t`. -/
theorem Z_stronglyAdapted : StronglyAdapted (coordFil X) (Z cands w g) := by
  intro t
  refine Finset.stronglyMeasurable_fun_sum cands fun i _ => ?_
  refine stronglyMeasurable_const.mul ?_
  refine Finset.stronglyMeasurable_fun_prod (Finset.range t) fun s hs => ?_
  have hst : s + 1 ≤ t := Finset.mem_range.mp hs
  exact (hgmeas i s).mono ((coordFil X).mono hst)

include hw hkraft hg01 hgmeas in
/-- Each `Z_t` is integrable (bounded in `[0,1]`, strongly measurable, finite measure). -/
theorem Z_integrable [IsProbabilityMeasure μ] (t : ℕ) : Integrable (Z cands w g t) μ := by
  refine Integrable.of_bound ?_ 1 (Filter.Eventually.of_forall fun ω => ?_)
  · exact ((Z_stronglyAdapted cands w g hgmeas t).mono ((coordFil X).le t)).aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_of_nonneg (Z_nonneg cands w g hw hg01 t ω)]
    exact Z_le_one cands w g hw hkraft hg01 t ω

include hw hkraft hg01 hgmeas in
/-- `Z` is a genuine `MeasureTheory.Supermartingale` for ANY probability truth law `μ`: adapted +
integrable + `μ[Z_{i+1} | ℱ_i] ≤ μ[Z_i | ℱ_i] = Z_i` (`condExp_mono` on the antitone step, then
`condExp_of_stronglyMeasurable`). No martingale / product-measure construction. -/
theorem Z_supermartingale [IsProbabilityMeasure μ] :
    Supermartingale (Z cands w g) (coordFil X) μ := by
  refine supermartingale_nat (Z_stronglyAdapted cands w g hgmeas)
    (fun i => Z_integrable cands w g hw hkraft hg01 hgmeas i) fun i => ?_
  have hle : Z cands w g (i + 1) ≤ᵐ[μ] Z cands w g i :=
    Filter.Eventually.of_forall fun ω => Z_antitone cands w g hw hg01 ω (Nat.le_succ i)
  have hmono : μ[Z cands w g (i + 1) | coordFil X i] ≤ᵐ[μ] μ[Z cands w g i | coordFil X i] :=
    condExp_mono (Z_integrable cands w g hw hkraft hg01 hgmeas (i + 1))
      (Z_integrable cands w g hw hkraft hg01 hgmeas i) hle
  have heq : μ[Z cands w g i | coordFil X i] = Z cands w g i :=
    condExp_of_stronglyMeasurable ((coordFil X).le i) (Z_stronglyAdapted cands w g hgmeas i)
      (Z_integrable cands w g hw hkraft hg01 hgmeas i)
  rwa [heq] at hmono

include hkraft in
/-- `𝔼[Z_0] ≤ 1`: `Z_0 = ∑ w` is constant (empty product `= 1`), and Kraft gives `∑ w ≤ 1`. -/
theorem integral_Z_zero_le_one [IsProbabilityMeasure μ] : μ[Z cands w g 0] ≤ 1 := by
  have h0 : Z cands w g 0 = fun _ : ℕ → X => ∑ i ∈ cands, w i := by
    funext ω; simp only [Z, L, Finset.prod_range_zero, mul_one]
  rw [h0]
  simp only [integral_const, probReal_univ, one_smul]
  exact hkraft

include hw hkraft hg01 hgmeas in
/-- FV-I capstone: the FV-G search-phase mass bound, with its supermartingale /
nonnegativity / `𝔼[Z_0] ≤ 1` premises DISCHARGED by the constructed mixture `Z`. Only the FV-G
search-side data survives as hypotheses (`pruned`, `m`, `Φ`, `hcharge` — now conditioned on the
concrete `∀ t, Z t ω < 1/δ`). -/
theorem search_phase_mass_bound [IsProbabilityMeasure μ]
    (δ : ℝ) (hδ0 : 0 < δ)
    {κ : Type*} (pruned : (ℕ → X) → Finset κ) (mfun : (ℕ → X) → κ → ℝ)
    (Φ : (ℕ → X) → ℕ → ℝ) (N : ℕ) (Cc : ℝ)
    (hm1 : ∀ ω, ∀ i ∈ pruned ω, mfun ω i < 1)
    (hΦ0 : ∀ ω, Φ ω 0 ≤ Cc) (hΦn : ∀ ω, 0 ≤ Φ ω N)
    (hcharge : ∀ ω, (∀ t, Z cands w g t ω < 1 / δ) →
        ∑ i ∈ pruned ω, (-Real.log (1 - mfun ω i))
          ≤ (∑ k ∈ Finset.range N, (Φ ω k - Φ ω (k + 1))) + Real.log (1 / δ)) :
    μ {ω | Cc + Real.log (1 / δ) < ∑ i ∈ pruned ω, mfun ω i} ≤ ENNReal.ofReal δ :=
  SQSearchPhaseMass.search_phase_mass_ville_chain (Z cands w g)
    (Z_supermartingale cands w g hw hkraft hg01 hgmeas) (Z_nonneg cands w g hw hg01)
    (integral_Z_zero_le_one cands w g hkraft) δ hδ0 pruned mfun Φ N Cc hm1 hΦ0 hΦn hcharge

end Construction

section DeterministicFactor

/-! ### The deterministic-rule factor (completing FV-I for the paper's rule class)

[Discovery] / [SQ] rules are DETERMINISTIC: a candidate `R'` predicts a single next symbol
`pred R' s h ∈ X` from the length-`s` history `h`, so its per-step likelihood of the realized symbol
is `0/1`. This section instantiates the abstract factor `g` at that concrete `detFactor`, discharging
FV-I's last named hypothesis (`hgmeas`) for the deterministic regime: the strong measurability is
PROVED from `Filtration.piLE`'s coordinate structure (both the predicted symbol and the realized
symbol `ω s` depend only on coordinates `≤ s + 1`), the alphabet `X` being discrete
(`Countable` + `MeasurableSingletonClass`) so equality-events are measurable. -/

variable {X : Type*} [MeasurableSpace X] [Countable X] [MeasurableSingletonClass X] [DecidableEq X]
  {ι : Type*}

/-- The per-step likelihood of a DETERMINISTIC candidate: `1` if the rule `pred i` predicts the
realized symbol `ω s` from the history `ω|_{<s}`, else `0` ([Discovery] / [SQ] rules are
deterministic: `p_{R'}(x ∣ h) ∈ {0,1}`). -/
def detFactor (pred : ι → (s : ℕ) → (Fin s → X) → X) (i : ι) (s : ℕ) (ω : ℕ → X) : ℝ :=
  if pred i s (fun k => ω k) = ω s then 1 else 0

omit [MeasurableSpace X] [Countable X] [MeasurableSingletonClass X] in
/-- A deterministic factor is `{0,1}`-valued, hence in `[0,1]` — the `hg01` input to `Z`. -/
theorem detFactor_mem_Icc (pred : ι → (s : ℕ) → (Fin s → X) → X) (i : ι) (s : ℕ) (ω : ℕ → X) :
    detFactor pred i s ω ∈ Set.Icc (0 : ℝ) 1 := by
  rw [Set.mem_Icc]; unfold detFactor; split_ifs <;> norm_num

/-- The equality event `{ω | pred i s (ω|_{<s}) = ω s}` is `coordFil X (s+1)`-measurable — both the
predicted symbol and the realized symbol `ω s` factor through coordinates `≤ s + 1` (`piLE` is the
comap of the `Set.Iic (s+1)`-restriction), and the discrete alphabet makes equality measurable — so
the `{0,1}`-valued `detFactor` is `ℱ_{s+1}`-strongly measurable (the `hgmeas` input to `Z`). -/
theorem detFactor_stronglyMeasurable (pred : ι → (s : ℕ) → (Fin s → X) → X) (i : ι) (s : ℕ) :
    StronglyMeasurable[coordFil X (s + 1)] (detFactor pred i s) := by
  have hcoord : ∀ j : ℕ, j ≤ s + 1 → Measurable[coordFil X (s + 1)] (fun ω : ℕ → X => ω j) := by
    intro j hj
    exact (measurable_pi_apply (⟨j, Set.mem_Iic.mpr hj⟩ : ↥(Set.Iic (s + 1)))).comp
      (comap_measurable (Preorder.restrictLe (π := fun _ : ℕ => X) (s + 1)))
  have hf : Measurable[coordFil X (s + 1)] (fun ω : ℕ → X => pred i s (fun k => ω k)) := by
    have hrestr : Measurable[coordFil X (s + 1)] (fun ω : ℕ → X => (fun k : Fin s => ω k)) :=
      @measurable_pi_lambda (ℕ → X) (Fin s) (fun _ => X) (coordFil X (s + 1)) _
        (fun ω k => ω k) fun k => hcoord k (le_trans (le_of_lt k.2) (Nat.le_succ s))
    exact (measurable_of_countable (pred i s)).comp hrestr
  have hg : Measurable[coordFil X (s + 1)] (fun ω : ℕ → X => ω s) := hcoord s (Nat.le_succ s)
  have hSet : MeasurableSet[coordFil X (s + 1)] {ω : ℕ → X | pred i s (fun k => ω k) = ω s} :=
    _root_.measurableSet_eq_fun hf hg
  have hEq : detFactor pred i s
      = Set.indicator {ω : ℕ → X | pred i s (fun k => ω k) = ω s} (fun _ => (1 : ℝ)) := by
    funext ω
    simp only [detFactor, Set.indicator_apply, Set.mem_setOf_eq]
  rw [hEq]
  exact (@stronglyMeasurable_const (ℕ → X) ℝ (coordFil X (s + 1)) _ (1 : ℝ)).indicator hSet

omit [MeasurableSpace X] [Countable X] [MeasurableSingletonClass X] in
/-- The deterministic likelihood is the indicator of FULL consistency: `L_t = 1` iff the rule
predicts every realized symbol up to time `t`, else `0` (a product of `0/1` indicators). This makes
`Z` for deterministic rules literally the alive-consistent posterior mass — the paper's picture. -/
theorem L_det_eq_indicator (pred : ι → (s : ℕ) → (Fin s → X) → X) (i : ι) (t : ℕ) (ω : ℕ → X) :
    L (detFactor pred) i t ω
      = if ∀ s ∈ Finset.range t, pred i s (fun k => ω k) = ω s then 1 else 0 := by
  simp only [L, detFactor]
  rw [Finset.prod_boole]

variable {μ : Measure (ℕ → X)}

/-- FV-I hardening: `Z` for the paper's DETERMINISTIC rule class is a genuine
supermartingale for ANY probability truth law, with NO abstract-`g` hypotheses left — only the
deterministic rule `pred`, the weights, and Kraft. -/
theorem Z_det_supermartingale [IsProbabilityMeasure μ]
    (cands : Finset ι) (w : ι → ℝ) (pred : ι → (s : ℕ) → (Fin s → X) → X)
    (hw : ∀ i ∈ cands, 0 ≤ w i) (hkraft : ∑ i ∈ cands, w i ≤ 1) :
    Supermartingale (Z cands w (detFactor pred)) (coordFil X) μ :=
  Z_supermartingale cands w (detFactor pred) hw hkraft
    (fun i s ω => detFactor_mem_Icc pred i s ω)
    (fun i s => detFactor_stronglyMeasurable pred i s)

end DeterministicFactor

end SQMixtureSupermartingale
