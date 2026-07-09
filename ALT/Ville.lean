import Mathlib

-- Ville's inequality for non-negative supermartingales (FV-G hardening; a genuine Mathlib gap).
-- Complete proofs, no `sorry`; wired into ALT.lean and axiom-guarded in AxiomAuditMathlib.lean.
set_option linter.style.header false

open MeasureTheory Filter Topology
open scoped ProbabilityTheory

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} {ℱ : Filtration ℕ m0}

namespace Ville

/-- Ville's inequality for a non-negative supermartingale. -/
theorem ville_inequality [IsFiniteMeasure μ]
    (Z : ℕ → Ω → ℝ) (hsuper : Supermartingale Z ℱ μ) (hnn : ∀ n ω, 0 ≤ Z n ω)
    (lam : ℝ) (hlam : 0 < lam) :
    μ {ω | ∃ n, lam ≤ Z n ω} ≤ ENNReal.ofReal (μ[Z 0] / lam) := by
  set A : ℕ → Set Ω := fun N => {ω | ∃ n, n ≤ N ∧ lam ≤ Z n ω} with hA
  -- Finite-horizon bound, then N → ∞.
  have hfin : ∀ N, μ (A N) ≤ ENNReal.ofReal (μ[Z 0] / lam) := by
    intro N
    -- the coerced (ℕ∞-valued) capped hitting time
    set τN : Ω → ℕ∞ := fun ω => (hittingBtwn Z (Set.Ici lam) 0 N ω : ℕ) with hτN
    have hπN : IsStoppingTime ℱ τN :=
      hsuper.1.adapted.isStoppingTime_hittingBtwn measurableSet_Ici
    -- STEP 1 (optional stopping): 𝔼[stoppedValue Z τ_N] ≤ 𝔼[Z 0].
    have h1 : μ[stoppedValue Z τN] ≤ μ[Z 0] := by
      have key := (hsuper.neg).expected_stoppedValue_mono (isStoppingTime_const ℱ 0) hπN
        (fun _ => zero_le) (fun ω => by simp only [hτN]; exact_mod_cast hittingBtwn_le (u := Z) ω)
      have e2 : stoppedValue (-Z) τN = -stoppedValue Z τN := by
        funext ω; simp [stoppedValue, Pi.neg_apply]
      simp only [stoppedValue_const, e2, Pi.neg_apply, integral_neg] at key
      linarith [key]
    -- STEP 2 (crux): λ · μ(A_N) ≤ 𝔼[stoppedValue Z τ_N], via the hitting lower bound.
    have h2 : lam * (μ (A N)).toReal ≤ μ[stoppedValue Z τN] := by
      have hZmeas : ∀ n, Measurable (Z n) := fun n =>
        (hsuper.stronglyMeasurable n).measurable.le (ℱ.le n)
      -- A_N is a finite union of measurable level sets, hence measurable.
      have hmeasA : MeasurableSet (A N) := by
        have hrw : A N = ⋃ n ∈ Finset.range (N + 1), {ω | lam ≤ Z n ω} := by
          rw [hA]; ext ω
          simp only [Set.mem_setOf_eq, Set.mem_iUnion, Finset.mem_range, Nat.lt_succ_iff,
            exists_prop]
        rw [hrw]
        exact Finset.measurableSet_biUnion _ fun n _ =>
          measurableSet_le measurable_const (hZmeas n)
      -- Pointwise: `λ · 1_{A_N} ≤ stoppedValue Z τ_N` (≥ λ on the hit event, ≥ 0 off it).
      have hpt : (A N).indicator (fun _ => lam) ≤ stoppedValue Z τN := by
        intro ω
        by_cases hω : ω ∈ A N
        · rw [Set.indicator_of_mem hω]
          rw [hA, Set.mem_setOf_eq] at hω
          obtain ⟨n, hnN, hZn⟩ := hω
          exact Set.mem_Ici.mp (stoppedValue_hittingBtwn_mem (u := Z) (n := 0) (m := N)
            ⟨n, ⟨Nat.zero_le _, hnN⟩, hZn⟩)
        · rw [Set.indicator_of_notMem hω]; exact hnn _ _
      -- Integrate the pointwise bound.
      have hbdd : ∀ ω, τN ω ≤ (N : ℕ∞) :=
        fun ω => by simp only [hτN]; exact_mod_cast hittingBtwn_le (u := Z) ω
      have hint_sv : Integrable (stoppedValue Z τN) μ := by
        have e2 : stoppedValue (-Z) τN = -stoppedValue Z τN := by
          funext ω; simp [stoppedValue, Pi.neg_apply]
        have hi := (hsuper.neg).integrable_stoppedValue hπN hbdd
        rw [e2] at hi; simpa using hi.neg
      have hint_ind : Integrable ((A N).indicator (fun _ => lam)) μ :=
        (integrable_const lam).indicator hmeasA
      have hmono := integral_mono hint_ind hint_sv hpt
      rw [integral_indicator_const lam hmeasA, smul_eq_mul, mul_comm] at hmono
      exact hmono
    -- STEP 3 (arithmetic): combine 1 & 2, divide by λ, push through ENNReal.ofReal.
    have h3 : (μ (A N)).toReal ≤ μ[Z 0] / lam := by
      rw [le_div_iff₀ hlam]
      nlinarith [h1, h2]
    calc μ (A N) = ENNReal.ofReal ((μ (A N)).toReal) :=
          (ENNReal.ofReal_toReal (measure_ne_top μ _)).symm
      _ ≤ ENNReal.ofReal (μ[Z 0] / lam) := ENNReal.ofReal_le_ofReal h3
  -- STEP 4 (N → ∞): monotone union + continuity from below.
  have hmono : Monotone A := by
    intro N M hNM ω hω
    simp only [hA, Set.mem_setOf_eq] at hω ⊢
    obtain ⟨n, hn, hZ⟩ := hω
    exact ⟨n, hn.trans hNM, hZ⟩
  have hunion : (⋃ N, A N) = {ω | ∃ n, lam ≤ Z n ω} := by
    ext ω
    simp only [hA, Set.mem_iUnion, Set.mem_setOf_eq]
    constructor
    · rintro ⟨N, n, _, hZ⟩; exact ⟨n, hZ⟩
    · rintro ⟨n, hZ⟩; exact ⟨n, n, le_refl n, hZ⟩
  rw [← hunion]
  exact le_of_tendsto (tendsto_measure_iUnion_atTop hmono) (Eventually.of_forall hfin)

/-- FV-G potential budget: Ville's inequality at `λ = 1/δ` for a non-negative supermartingale with
`𝔼[Z 0] ≤ 1` gives `μ{∃ n, 1/δ ≤ Z n} ≤ δ`. This is the excursion budget of Appendix A Claim 2's
search phase: the total measure of paths whose log-Bayes potential ever exceeds the `1/δ` threshold
is at most `δ`. -/
theorem ville_potential_budget [IsFiniteMeasure μ]
    (Z : ℕ → Ω → ℝ) (hsuper : Supermartingale Z ℱ μ) (hnn : ∀ n ω, 0 ≤ Z n ω)
    (hZ0 : μ[Z 0] ≤ 1) (δ : ℝ) (hδ0 : 0 < δ) :
    μ {ω | ∃ n, 1 / δ ≤ Z n ω} ≤ ENNReal.ofReal δ := by
  refine (ville_inequality Z hsuper hnn (1 / δ) (by positivity)).trans (ENNReal.ofReal_le_ofReal ?_)
  rw [div_le_iff₀ (by positivity : (0:ℝ) < 1 / δ), mul_one_div, div_self hδ0.ne']
  exact hZ0

end Ville
