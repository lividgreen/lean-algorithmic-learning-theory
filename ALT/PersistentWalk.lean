/-
Copyright (c) 2026 Mykola Palamarchuk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mykola Palamarchuk
-/
module

public import Mathlib.Analysis.MeanInequalities
public import ALT.ParityWalk

/-!
# The persistent walk: a single-orbit tail whose constant is an inverse spectral gap

`ALT/ParityWalk.lean` supplies the tail of a two-state chain whose per-step multiplier has a
*negative* mean — the parity walk `x ↦ ¬x ⊕ ξ`, where consecutive states are anti-correlated and
the Birkhoff sums cancel in pairs.  That cancellation is why its constant carries no dependence on
the noise rate.

This module treats the opposite sign: a **persistent** walk, whose multiplier has mean
`ρ ∈ [0, 1)`.  Here nothing cancels, the telescope divides by the gap `1 − ρ`, and a
gap-dependent constant is unavoidable.  It is the minimal genuinely spectral case, and it is what a
*pair* of coordinates of a two-state chain looks like: two anti-correlated walks multiplied
together have their sign flips cancel, leaving persistence `ρ = λ²` at gap `1 − λ²`.

Two devices do the work.

* **Blocking.**  The tail is taken at a lag `K` chosen large enough that the accumulated
  persistence `ρ` is at most `1/2`, so the telescope's divisor `1 − ρ` is an absolute constant
  rather than the gap.  The gap then appears once, in `K` — linearly, not squared, which is the
  whole point of blocking rather than telescoping at lag one.
* **Interleaving without independence.**  The `K` residue classes of the time axis are *not*
  independent of each other — their noise blocks overlap across classes — so their sub-Gaussian
  bounds are combined by the arithmetic–geometric mean inequality rather than by a product formula
  or a union bound.  The price is a factor `K` in the variance proxy; a union bound would instead
  charge a factor `K` in front of the exponential, which the Hoeffding shape `2·exp(…)` that the
  SQ-oracle interface consumes ([SQ] §3.2) has no room for.

## Main results

* `hasSubgaussianMGF_sum_range` — **the combination step**: `K` summands, each sub-Gaussian with
  parameter `J` and *not assumed independent*, sum to a variable sub-Gaussian with parameter
  `K²·J`.
* `sum_range_mul_eq` — the time axis `[0, K·M)` decomposed into its `K` residue classes.
* `persistentSum_tail` — **the tail**: for a `Bool` process whose character obeys a lag-`K`
  multiplicative recursion against block multipliers of common mean `ρ ≤ 1/2`, the Birkhoff sum of
  the character through time `K·M + K` obeys an exponential tail with boundary allowance `4K` and
  variance proxy `K²·M`.
-/


@[expose] public section

namespace PersistentWalk

open MeasureTheory ProbabilityTheory ParityWalk Real

/-! ## Combining dependent summands: the arithmetic–geometric mean step -/

section Combine

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

omit [IsProbabilityMeasure P] in
/-- **The combination step.**  `K` summands, each sub-Gaussian with parameter `J` and with *no
independence assumed between them*, add up to a variable sub-Gaussian with parameter `K²·J`.

The tool is the arithmetic–geometric mean inequality applied pointwise to the exponentials:
`exp(t·∑ S_c) = ∏ (exp(K·t·S_c))^{1/K} ≤ K⁻¹·∑ exp(K·t·S_c)`.  Integrating and using each
summand's own bound at the inflated argument `K·t` gives the claim.

At the independent extreme the true parameter would be `K·J`; the extra factor `K` is exactly what
arbitrary dependence costs, and it is paid inside the exponent where the SQ interface can absorb
it into the mixing constant. -/
theorem hasSubgaussianMGF_sum_range {K : ℕ} (hK : 0 < K) (S : ℕ → Ω → ℝ) (J : NNReal)
    (hS : ∀ c, HasSubgaussianMGF (S c) J P) :
    HasSubgaussianMGF (fun ω => ∑ c ∈ Finset.range K, S c ω) ((K : NNReal) ^ 2 * J) P := by
  have hKR : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK
  have hKne : (K : ℝ) ≠ 0 := ne_of_gt hKR
  -- the pointwise arithmetic–geometric mean bound
  have hkey : ∀ (t : ℝ) (ω : Ω), Real.exp (t * ∑ c ∈ Finset.range K, S c ω)
      ≤ (K : ℝ)⁻¹ * ∑ c ∈ Finset.range K, Real.exp ((K : ℝ) * t * S c ω) := by
    intro t ω
    rw [Finset.mul_sum, Real.exp_sum]
    have hw : ∑ _c ∈ Finset.range K, (K : ℝ)⁻¹ = 1 := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      field_simp
    have hamgm := Real.geom_mean_le_arith_mean_weighted (Finset.range K)
      (fun _ => (K : ℝ)⁻¹) (fun c => Real.exp ((K : ℝ) * t * S c ω))
      (fun _ _ => by positivity) hw (fun _ _ => (Real.exp_pos _).le)
    have hpow : ∀ c : ℕ, Real.exp ((K : ℝ) * t * S c ω) ^ ((K : ℝ)⁻¹) = Real.exp (t * S c ω) := by
      intro c
      rw [← Real.exp_mul]
      congr 1
      field_simp
    calc ∏ c ∈ Finset.range K, Real.exp (t * S c ω)
        = ∏ c ∈ Finset.range K, Real.exp ((K : ℝ) * t * S c ω) ^ ((K : ℝ)⁻¹) :=
          Finset.prod_congr rfl fun c _ => (hpow c).symm
      _ ≤ ∑ c ∈ Finset.range K, (K : ℝ)⁻¹ * Real.exp ((K : ℝ) * t * S c ω) := hamgm
      _ = (K : ℝ)⁻¹ * ∑ c ∈ Finset.range K, Real.exp ((K : ℝ) * t * S c ω) := by
          rw [Finset.mul_sum]
  -- the dominating function is integrable, summand by summand
  have hdom : ∀ t : ℝ, Integrable
      (fun ω => (K : ℝ)⁻¹ * ∑ c ∈ Finset.range K, Real.exp ((K : ℝ) * t * S c ω)) P := by
    intro t
    refine Integrable.const_mul ?_ _
    exact integrable_finsetSum _ fun c _ => (hS c).integrable_exp_mul ((K : ℝ) * t)
  have hmeasS : AEStronglyMeasurable (fun ω => ∑ c ∈ Finset.range K, S c ω) P :=
    Finset.aestronglyMeasurable_fun_sum _ fun c _ => (hS c).aestronglyMeasurable
  have hint : ∀ t : ℝ, Integrable (fun ω => Real.exp (t * ∑ c ∈ Finset.range K, S c ω)) P := by
    intro t
    refine Integrable.mono' (hdom t)
      (Real.continuous_exp.comp_aestronglyMeasurable (hmeasS.const_mul t))
      (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _)]
    exact hkey t ω
  refine ⟨hint, fun t => ?_⟩
  have hJK : ∀ c : ℕ, mgf (S c) P ((K : ℝ) * t) ≤ Real.exp ((J : ℝ) * ((K : ℝ) * t) ^ 2 / 2) :=
    fun c => (hS c).mgf_le _
  calc mgf (fun ω => ∑ c ∈ Finset.range K, S c ω) P t
      = ∫ ω, Real.exp (t * ∑ c ∈ Finset.range K, S c ω) ∂P := rfl
    _ ≤ ∫ ω, (K : ℝ)⁻¹ * ∑ c ∈ Finset.range K, Real.exp ((K : ℝ) * t * S c ω) ∂P :=
        integral_mono (hint t) (hdom t) fun ω => hkey t ω
    _ = (K : ℝ)⁻¹ * ∑ c ∈ Finset.range K, mgf (S c) P ((K : ℝ) * t) := by
        rw [integral_const_mul,
          integral_finsetSum _ fun c _ => (hS c).integrable_exp_mul ((K : ℝ) * t)]
        rfl
    _ ≤ (K : ℝ)⁻¹ * ∑ _c ∈ Finset.range K, Real.exp ((J : ℝ) * ((K : ℝ) * t) ^ 2 / 2) := by
        gcongr with c hc
        exact hJK c
    _ = Real.exp ((((K : NNReal) ^ 2 * J : NNReal) : ℝ) * t ^ 2 / 2) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        push_cast
        rw [← mul_assoc, inv_mul_cancel₀ hKne, one_mul]
        congr 1
        ring

end Combine

/-! ## The time axis, decomposed into residue classes -/

/-- The time axis `[0, K·M)` is the disjoint union of its `K` residue classes mod `K`, each of
length `M`.  This is the interleaving the tail below runs on: the blocks a single class reads are
pairwise disjoint even when blocks of *different* classes overlap. -/
lemma sum_range_mul_eq {α : Type*} [AddCommMonoid α] {K : ℕ} (hK : 0 < K) (M : ℕ) (f : ℕ → α) :
    ∑ t ∈ Finset.range (K * M), f t
      = ∑ c ∈ Finset.range K, ∑ u ∈ Finset.range M, f (c + K * u) := by
  rw [← Finset.sum_product']
  refine Finset.sum_nbij' (fun t => (t % K, t / K)) (fun p => p.1 + K * p.2) ?_ ?_ ?_ ?_ ?_
  · intro t ht
    simp only [Finset.mem_range] at ht
    simp only [Finset.mem_product, Finset.mem_range]
    exact ⟨Nat.mod_lt _ hK, Nat.div_lt_of_lt_mul (by omega)⟩
  · intro p hp
    simp only [Finset.mem_product, Finset.mem_range] at hp
    simp only [Finset.mem_range]
    calc p.1 + K * p.2 < K + K * p.2 := by omega
      _ ≤ K * M := by
          have : K * p.2 + K ≤ K * M := by
            have : p.2 + 1 ≤ M := hp.2
            calc K * p.2 + K = K * (p.2 + 1) := by ring
              _ ≤ K * M := Nat.mul_le_mul_left K this
          omega
  · intro t _
    exact Nat.mod_add_div t K
  · intro p hp
    simp only [Finset.mem_product, Finset.mem_range] at hp
    have h1 : (p.1 + K * p.2) % K = p.1 := by
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hp.1]
    have h2 : (p.1 + K * p.2) / K = p.2 := by
      rw [Nat.add_mul_div_left _ _ hK, Nat.div_eq_of_lt hp.1, Nat.zero_add]
    rw [h1, h2]
  · intro t _
    rw [Nat.mod_add_div t K]

/-! ## The tail -/

section Tail

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {ξ : ℕ → Ω → Bool} {ρ : ℝ} {K : ℕ}

/-- **The persistent-walk tail.**  Let `o` be a `Bool` process whose character obeys the lag-`K`
multiplicative recursion `χ(o t)·Y t = χ(o (t+K))`, where each multiplier `Y t` is a
`[−1, 1]`-valued reading of a noise block `A t`, all multipliers have the same mean `ρ`, and —
within each residue class mod `K` — the blocks are pairwise disjoint and the process is readable
off everything the class's later blocks do not touch.  If the accumulated persistence satisfies
`ρ ≤ 1/2`, then the Birkhoff sum of `χ ∘ o` through time `K·M + K` obeys an exponential tail with
boundary allowance `4K` and variance proxy `K²·M`.

Read at a horizon `n = K·M + K` and a tolerance `τ`, this is the Hoeffding shape at a mixing
constant proportional to `K` — so choosing `K` as the blocking length that brings the persistence
below `1/2` prices the constant *linearly* in the inverse gap.  Telescoping at lag one instead
would divide by the gap itself and square it. -/
theorem persistentSum_tail (hmeas : ∀ i, Measurable (ξ i)) (hindep : iIndepFun ξ P)
    (hK : 0 < K) (hρ0 : 0 ≤ ρ) (hρ : ρ ≤ 1 / 2)
    (o : ℕ → Ω → Bool) (Y : ℕ → Ω → ℝ) (A : ℕ → Set ℕ)
    (hdisj : ∀ c u v, u ≠ v → Disjoint (A (c + K * u)) (A (c + K * v)))
    (hYmeas : ∀ t, Measurable[noiseAlg ξ (A t)] (Y t))
    (hYbdd : ∀ t ω, Y t ω ∈ Set.Icc (-1 : ℝ) 1) (hYmean : ∀ t, ∫ ω, Y t ω ∂P = ρ)
    (hom : ∀ c u, Measurable[noiseAlg ξ (pastSet (fun v => A (c + K * v)) u)] (o (c + K * u)))
    (hrec : ∀ t ω, chi (o t ω) * Y t ω = chi (o (t + K) ω))
    (M : ℕ) {ε : ℝ} (hε : 0 ≤ ε) :
    P.real {ω | 2 * ε + 4 * K ≤ |∑ t ∈ Finset.range (K * M + K), chi (o t ω)|}
      ≤ 2 * Real.exp (-ε ^ 2 / (2 * ((K : ℝ) ^ 2 * M))) := by
  -- each residue class is a block-signed sum, hence sub-Gaussian with parameter `M`
  set S : ℕ → Ω → ℝ := fun c =>
    blockSignedSum (fun u => o (c + K * u)) (fun u => Y (c + K * u)) ρ M with hSdef
  have hSsub : ∀ c, HasSubgaussianMGF (S c) M P := fun c =>
    hasSubgaussianMGF_blockSignedSum hmeas hindep (fun u v h => hdisj c u v h)
      (fun u => hYmeas _) (fun u ω => hYbdd _ ω) (fun u => hYmean _) (fun u => hom c u) M
  have htot : HasSubgaussianMGF (fun ω => ∑ c ∈ Finset.range K, S c ω) ((K : NNReal) ^ 2 * M) P :=
    hasSubgaussianMGF_sum_range hK S M hSsub
  -- the class sums reassemble the global signed sum
  have hsplit : ∀ ω, ∑ c ∈ Finset.range K, S c ω
      = ∑ t ∈ Finset.range (K * M), chi (o t ω) * (Y t ω - ρ) := fun ω =>
    (sum_range_mul_eq hK M fun t => chi (o t ω) * (Y t ω - ρ)).symm
  -- the deviation event sits inside the signed sum's own
  have hsub : {ω | 2 * ε + 4 * K ≤ |∑ t ∈ Finset.range (K * M + K), chi (o t ω)|}
      ⊆ {ω | ε ≤ |∑ c ∈ Finset.range K, S c ω|} := by
    intro ω hω
    simp only [Set.mem_ofPred_eq] at hω ⊢
    have hgen := abs_chiSum_le_gen (fun t => o t ω) (fun t => Y t ω) K ρ
      (abs_le.mpr ⟨by linarith, by linarith⟩) (fun t => hrec t ω) (K * M)
    rw [hsplit ω]
    nlinarith [abs_nonneg (∑ t ∈ Finset.range (K * M + K), chi (o t ω))]
  refine le_trans (measureReal_mono hsub (measure_ne_top _ _)) ?_
  have hchernoff := measureReal_abs_ge_le htot hε
  refine hchernoff.trans_eq ?_
  norm_num

end Tail

end PersistentWalk

/-! ## Axiom audit

The combination step and the persistent tail are `#print axioms`-clean on the standard triple, and
the guards below make that build-enforced. -/

set_option linter.style.longLine false

/-- info: 'PersistentWalk.hasSubgaussianMGF_sum_range' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PersistentWalk.hasSubgaussianMGF_sum_range

/-- info: 'PersistentWalk.persistentSum_tail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PersistentWalk.persistentSum_tail
