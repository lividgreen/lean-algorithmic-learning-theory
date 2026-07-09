import Mathlib

-- Tier-1 formal check, not Mathlib-destined: opt out of the house-style header linter.
set_option linter.style.header false

/-!
# Predictive transfer: the Bayes-mixture perturbation bound (Paper III Appendix A)

Provenance: `03_polynomial_convergence_under_SQ.md`, Appendix A "Soundness of SQ pruning":
* "Removing this mass perturbs the one-step predictive distribution by `≤ δ/2` in total." (≈l.294)
* "the predictive guarantee is preserved up to the `o(δ)` pruned mass." (≈l.296)
* the still-prose item "the predictive-transfer step that turns an `O(r)` pruned mass into the
  preserved one-step guarantee. It is the Bayes-mixture argument of Paper II, prose." (≈l.298)
* `ALT/SQPrunedMass.lean` records the same non-goal: the union "into a single soundness statement
  … stays in prose (it is the Bayes-mixture argument of Paper II)."

This file (FV-H) discharges that predictive-transfer step. It is the companion to FV-F
(`ALT/SQPrunedMass.lean`, post-discovery `∑ ε ≤ δ/2`) and FV-G (`ALT/SQSearchPhaseMass.lean`,
search-phase `∑ ε ≤ ln2·K(R) + ln(1/δ)` w.h.p., Ville-chained) — those mass budgets are exactly the
`∑ ε_t` that `accumulated_perturbation_le` consumes: FV-F ⇒ total predictive damage `≤ δ`,
FV-G ⇒ damage absorbed into the `O(r + log(1/δ))` discovery regret.

## The mathematical core, made exact (a SHARPENING of the prose)
A prequential mixture over candidates predicts `P(x) = (∑_i u_i · p_i x)/U` with unnormalized
posterior weights `u` and `U = ∑_i u_i`. Pruning the set `pruned` (posterior mass
`W = ∑_{pruned} u`, fraction `ε = W/U`) and renormalizing over the survivors `alive`
(`V = ∑_{alive} u`, `U = V + W`) yields `Q(x) = (∑_{alive} u_i · p_i x)/V`. Then, pointwise,
`Q x − P x = (S x · W − T x · V)/(V·U)` with `S x = ∑_{alive} u_i p_i x`,
`T x = ∑_{pruned} u_i p_i x`, and summing `|·|` over the outcomes gives `∑_x |Q x − P x| ≤ 2ε`
**exactly** — i.e. total variation
`≤ ε` with *no hidden constant*, so the paper's "`≤ δ/2` in total" is recovered at `ε ≤ δ/2` and
sharpened. Any `α`-guarantee on `P` (L1 vs. the truth `q`) transfers to `α + 2ε` on `Q`.

## What this DOES establish
* `mixture_prune_perturbation` (T1): the exact one-step perturbation bound
  `∑_x |Q x − P x| ≤ 2·(W/U)`, the mixture-prune identity summed with the elementary
  `|S·W − T·V| ≤ S·W + T·V` and the column sums `∑_x S x = V`, `∑_x T x = W`.
* `predictive_transfer` (T2): an `α`-guarantee on the full mixture `P` transfers to `α + 2·(W/U)`
  on the renormalized survivor mixture `Q`, by the pointwise triangle inequality + T1.
* `accumulated_perturbation_le` (T3): the "absorbed into the budget" accounting — across a
  step-indexed family of prunings each satisfying T1's hypotheses, the total L1 predictive damage
  is `≤ 2·∑_t ε_t`. This is `Finset.sum_le_sum` over T1 instances.

## What this does NOT establish (stays modeled / later assembly; no overclaiming)
* Not the identification of `ε_t` with the algorithm's actual pruned posterior fractions: wiring the
  weights `u`, survivors `alive t`, and pruned sets `pruned t` to the running SQ learner is the
  algorithm layer.
* Not the union with FV-E's `1−δ` truth-survival into one soundness statement: that final assembly
  (predictive damage `≤ δ` on the `≥ 1−δ` good event) stays for a later stage.
* Not WHY the pruned mass is small: that is FV-F (post-discovery decay+Kraft) and FV-G (search-phase
  log-Bayes potential + Ville) — this file only transfers a *given* small `∑ ε_t` to the predictor.
-/

namespace SQPredictiveTransfer

/-- The scalar heart of the perturbation bound: with survivor mass `V > 0`, pruned mass `W ≥ 0`,
and nonnegative outcome weights `a` (survivors) and `b` (pruned), the one-step predictive gap of a
single outcome, `|a/V − (a+b)/(V+W)| = |a·W − b·V|/(V·(V+W))`, is bounded by
`a·(W/(V·(V+W))) + b·(1/(V+W))`. Summing over the outcomes yields the `2·(W/U)` bound (T1). -/
private lemma perturb_pointwise {V W a b : ℝ} (hV : 0 < V) (hW : 0 ≤ W)
    (ha : 0 ≤ a) (hb : 0 ≤ b) :
    |a / V - (a + b) / (V + W)| ≤ a * (W / (V * (V + W))) + b * (1 / (V + W)) := by
  have hU : 0 < V + W := by linarith
  have hVU : 0 < V * (V + W) := mul_pos hV hU
  have hVne : V ≠ 0 := hV.ne'
  have hUne : (V + W) ≠ 0 := hU.ne'
  have heq : a / V - (a + b) / (V + W) = (a * W - b * V) / (V * (V + W)) := by
    field_simp
    ring
  have habs : |a * W - b * V| ≤ a * W + b * V := by
    rw [abs_le]
    constructor <;> nlinarith [mul_nonneg ha hW, mul_nonneg hb hV.le]
  rw [heq, abs_div, abs_of_pos hVU, div_le_iff₀ hVU]
  have hRHS : (a * (W / (V * (V + W))) + b * (1 / (V + W))) * (V * (V + W)) = a * W + b * V := by
    field_simp
  rw [hRHS]
  exact habs

/-- T1 (Appendix A, one-step perturbation): pruning the set `pruned` from a prequential mixture and
renormalizing over the survivors `alive` perturbs the one-step predictive distribution by
`∑_x |Q x − P x| ≤ 2·(W/U)` in L1, where `Q x = (∑_{alive} u_i p_i x)/V`,
`P x = (∑_{alive∪pruned} u_i p_i x)/U`, `V = ∑_{alive} u`, `U = ∑_{alive∪pruned} u`,
`W = ∑_{pruned} u`. The bound is **exact** (total variation `≤ W/U`, no hidden constant). -/
theorem mixture_prune_perturbation
    {ι X : Type*} [DecidableEq ι] (alive pruned : Finset ι) (hdisj : Disjoint alive pruned)
    (outs : Finset X) (u : ι → ℝ) (p : ι → X → ℝ)
    (hu : ∀ i ∈ alive ∪ pruned, 0 ≤ u i)
    (hp0 : ∀ i ∈ alive ∪ pruned, ∀ x ∈ outs, 0 ≤ p i x)
    (hp1 : ∀ i ∈ alive ∪ pruned, ∑ x ∈ outs, p i x = 1)
    (hV : 0 < ∑ i ∈ alive, u i) :
    ∑ x ∈ outs, |(∑ i ∈ alive, u i * p i x) / (∑ i ∈ alive, u i)
               - (∑ i ∈ alive ∪ pruned, u i * p i x) / (∑ i ∈ alive ∪ pruned, u i)|
      ≤ 2 * ((∑ i ∈ pruned, u i) / (∑ i ∈ alive ∪ pruned, u i)) := by
  set V := ∑ i ∈ alive, u i with hVdef
  set W := ∑ i ∈ pruned, u i with hWdef
  have hUsplit : ∑ i ∈ alive ∪ pruned, u i = V + W := by
    rw [hVdef, hWdef]; exact Finset.sum_union hdisj
  have hW0 : 0 ≤ W := by
    rw [hWdef]; exact Finset.sum_nonneg fun i hi => hu i (Finset.mem_union_right _ hi)
  have hUne : (V + W) ≠ 0 := by
    have : 0 < V + W := by linarith
    exact this.ne'
  have hVne : V ≠ 0 := hV.ne'
  -- column sums: ∑_x ∑_{alive} u_i p_i x = ∑_{alive} u_i = V, likewise for pruned/W
  have hSsum : ∑ x ∈ outs, (∑ i ∈ alive, u i * p i x) = V := by
    rw [Finset.sum_comm, hVdef]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    rw [← Finset.mul_sum, hp1 i (Finset.mem_union_left _ hi), mul_one]
  have hTsum : ∑ x ∈ outs, (∑ i ∈ pruned, u i * p i x) = W := by
    rw [Finset.sum_comm, hWdef]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    rw [← Finset.mul_sum, hp1 i (Finset.mem_union_right _ hi), mul_one]
  rw [hUsplit]
  -- pointwise perturbation bound, then sum
  have hbound : ∀ x ∈ outs,
      |(∑ i ∈ alive, u i * p i x) / V - (∑ i ∈ alive ∪ pruned, u i * p i x) / (V + W)|
        ≤ (∑ i ∈ alive, u i * p i x) * (W / (V * (V + W)))
          + (∑ i ∈ pruned, u i * p i x) * (1 / (V + W)) := by
    intro x hx
    have hsu : (∑ i ∈ alive ∪ pruned, u i * p i x)
        = (∑ i ∈ alive, u i * p i x) + (∑ i ∈ pruned, u i * p i x) :=
      Finset.sum_union hdisj
    rw [hsu]
    have ha : 0 ≤ ∑ i ∈ alive, u i * p i x :=
      Finset.sum_nonneg fun i hi => mul_nonneg (hu i (Finset.mem_union_left _ hi))
        (hp0 i (Finset.mem_union_left _ hi) x hx)
    have hb : 0 ≤ ∑ i ∈ pruned, u i * p i x :=
      Finset.sum_nonneg fun i hi => mul_nonneg (hu i (Finset.mem_union_right _ hi))
        (hp0 i (Finset.mem_union_right _ hi) x hx)
    exact perturb_pointwise hV hW0 ha hb
  calc ∑ x ∈ outs, |(∑ i ∈ alive, u i * p i x) / V
                   - (∑ i ∈ alive ∪ pruned, u i * p i x) / (V + W)|
      ≤ ∑ x ∈ outs, ((∑ i ∈ alive, u i * p i x) * (W / (V * (V + W)))
          + (∑ i ∈ pruned, u i * p i x) * (1 / (V + W))) := Finset.sum_le_sum hbound
    _ = 2 * (W / (V + W)) := by
        rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul, hSsum, hTsum]
        field_simp
        ring

/-- T2 (Appendix A, guarantee transfer): if the full prequential mixture `P` is within `α` in L1 of
the truth `q`, then after pruning and renormalizing, the survivor mixture `Q` is within
`α + 2·(W/U)` of `q`. The predictive guarantee is preserved up to twice the pruned posterior
mass. -/
theorem predictive_transfer
    {ι X : Type*} [DecidableEq ι] (alive pruned : Finset ι) (hdisj : Disjoint alive pruned)
    (outs : Finset X) (u : ι → ℝ) (p : ι → X → ℝ)
    (hu : ∀ i ∈ alive ∪ pruned, 0 ≤ u i)
    (hp0 : ∀ i ∈ alive ∪ pruned, ∀ x ∈ outs, 0 ≤ p i x)
    (hp1 : ∀ i ∈ alive ∪ pruned, ∑ x ∈ outs, p i x = 1)
    (hV : 0 < ∑ i ∈ alive, u i) (q : X → ℝ) (α : ℝ)
    (htruth : ∑ x ∈ outs, |(∑ i ∈ alive ∪ pruned, u i * p i x) / (∑ i ∈ alive ∪ pruned, u i)
                          - q x| ≤ α) :
    ∑ x ∈ outs, |(∑ i ∈ alive, u i * p i x) / (∑ i ∈ alive, u i) - q x|
      ≤ α + 2 * ((∑ i ∈ pruned, u i) / (∑ i ∈ alive ∪ pruned, u i)) := by
  have hpert := mixture_prune_perturbation alive pruned hdisj outs u p hu hp0 hp1 hV
  have htri : ∑ x ∈ outs, |(∑ i ∈ alive, u i * p i x) / (∑ i ∈ alive, u i) - q x|
      ≤ ∑ x ∈ outs, (|(∑ i ∈ alive, u i * p i x) / (∑ i ∈ alive, u i)
            - (∑ i ∈ alive ∪ pruned, u i * p i x) / (∑ i ∈ alive ∪ pruned, u i)|
          + |(∑ i ∈ alive ∪ pruned, u i * p i x) / (∑ i ∈ alive ∪ pruned, u i) - q x|) :=
    Finset.sum_le_sum fun x _ => abs_sub_le _ _ _
  rw [Finset.sum_add_distrib] at htri
  linarith [hpert, htruth, htri]

/-- T3 (Appendix A, accumulated accounting): across a step-indexed family of prunings — at each step
`t < n`, prune `pruned t` from the mixture with weights `u t` and predictors `p t`, satisfying T1's
hypotheses — the total one-step L1 predictive damage is `≤ 2·∑_t ε_t` with `ε_t = (∑ pruned t)/(∑
alive t ∪ pruned t)`. Consuming FV-F/FV-G's mass budgets `∑ ε_t` here bounds the total damage. -/
theorem accumulated_perturbation_le
    {ι X : Type*} [DecidableEq ι] (n : ℕ)
    (alive pruned : ℕ → Finset ι) (outs : Finset X) (u : ℕ → ι → ℝ) (p : ℕ → ι → X → ℝ)
    (hdisj : ∀ t ∈ Finset.range n, Disjoint (alive t) (pruned t))
    (hu : ∀ t ∈ Finset.range n, ∀ i ∈ alive t ∪ pruned t, 0 ≤ u t i)
    (hp0 : ∀ t ∈ Finset.range n, ∀ i ∈ alive t ∪ pruned t, ∀ x ∈ outs, 0 ≤ p t i x)
    (hp1 : ∀ t ∈ Finset.range n, ∀ i ∈ alive t ∪ pruned t, ∑ x ∈ outs, p t i x = 1)
    (hV : ∀ t ∈ Finset.range n, 0 < ∑ i ∈ alive t, u t i) :
    ∑ t ∈ Finset.range n,
        ∑ x ∈ outs, |(∑ i ∈ alive t, u t i * p t i x) / (∑ i ∈ alive t, u t i)
               - (∑ i ∈ alive t ∪ pruned t, u t i * p t i x)
                   / (∑ i ∈ alive t ∪ pruned t, u t i)|
      ≤ 2 * ∑ t ∈ Finset.range n,
              (∑ i ∈ pruned t, u t i) / (∑ i ∈ alive t ∪ pruned t, u t i) := by
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun t ht => ?_
  exact mixture_prune_perturbation (alive t) (pruned t) (hdisj t ht) outs (u t) (p t)
    (hu t ht) (hp0 t ht) (hp1 t ht) (hV t ht)

end SQPredictiveTransfer
