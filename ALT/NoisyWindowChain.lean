/-
Copyright (c) 2026 Mykola Palamarchuk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mykola Palamarchuk
-/
import ALT.BirkhoffTool
import ALT.ParityWalk

/-!
# The noisy window chain: an explicit source whose mixing constant is derived

Fix a window length `k ≥ 1` over the alphabet `Bool`.  The **noisy window chain** is the process

`o_{t+k} = ¬ o_t ⊕ ξ_{t+k}`,

with the initial window `o_0, …, o_{k−1}` and the noise bits `ξ_k, ξ_{k+1}, …` supplied by one
mutually independent family.  Noiselessly (`ξ ≡ false`) the length-`k` window evolves by the
permutation `w ↦ (w_2, …, w_k, ¬w_1)`, whose `k`-th power is bitwise complement, so its order
divides `2k` and the uniform law on windows is stationary; the noise preserves that stationarity and
supplies exactly the window-noise rate `η` that [SQ] §3.1's budget `2η ≤ τ` tolerates.

This module gives that chain a **derived** single-orbit Hoeffding constant.  Until now the corpus
discharged `BirkhoffTool.MixingHoeffding` only at the independent end (`mixingHoeffding_of_iid`,
`c = 1`); `mixingHoeffding_noisyWindowChain` below discharges it for a genuinely *dependent* source,
at the named constant

`c = 4k`,

for coordinate query ensembles `Z i o = φ (o i)` with `φ` valued in `[−1, 1]`.

## The constant, and what it does not contain

The constant carries **no dependence on the noise rate**.  That is not an artefact of a crude bound
but the shape of this chain: the `k`-step transition operator sends the character `χ_S` to
`(−λ)^{|S|} χ_S` with `λ = 1 − 2η`, so on the single-coordinate characters the eigenvalue is
*negative*.  The Birkhoff sums therefore cancel in consecutive pairs instead of accumulating, and
what governs them is `1 + λ ≥ 1`, not the spectral gap `1 − λ = 2η`.  A generic spectral-gap bound
of Fan–Jiang–Sun shape would read `c = (1+λ')/(1−λ') ≈ k/η` at the per-step norm
`λ' = λ^{1/k}`; that estimate is correct as a bound and pessimistic here by exactly the factor the
sign saves.  Only the *window length* survives, as the boundary allowance of the interleaving.

The trade-off `η ↔ c` that [SQ] §3.1's budget appears to price therefore does not exist for this
chain at coordinate observables: the noise rate may be taken as small as the budget `2η ≤ τ` allows
without inflating the sample complexity `n ≥ (2c/τ²)·log(2/δ)` at all.

## Main results

* `obs` — the observation process, *defined* by its interleaving: `o_u` is the residue class
  `u % k`'s parity walk after `u / k` steps.  `obs_interleave` is then definitional and
  `obs_add` recovers the chain's own recursion `o_{u+k} = ¬o_u ⊕ ξ_{u+k}`.
* `indepFun_residueClass` / `indepFun_residueClass_pair` — **the interleaving is a genuine
  independence decomposition**: each residue class's process is independent of the joint reading of
  every other class, and any two distinct classes are independent.  (Mutual independence packaged
  as a single `iIndepFun` over `Fin k` is *not* stated: it would need a σ-algebra grouping lemma
  Mathlib does not carry, and nothing below consumes it.)
* `windowMap`, `windowMap_iterate_len`, `windowMap_iterate_two_len`, `windowMap_bijective` — the
  noiseless window map is a permutation whose `k`-th power is complement, hence of order dividing
  `2k`.
* `windowAt_succ` — the chain's window at time `t+1` is the noisy step applied to its window at
  time `t`, so `windowMap` really is this chain's window map.
* `noisyStep_bijective`, `uniform_stationary` — each noise value acts as a permutation of the window
  space, hence the uniform law on windows is stationary for the noisy step, at every noise law.
* `mixingHoeffding_noisyWindowChain` — **the constant**: `MixingHoeffding μ Z (coordMean φ) (4k)`
  for the chain's own trajectory law `μ`, at every window length `k ≥ 1` and every noise rate.
* `not_mixingHoeffding_noisyWindowChain_pinned` — the standing vacuity guard: at this same law and
  this same constant the predicate is refutable, so the theorem above is a statement about the
  ensemble and not an artefact of the constant.

## Scope

The constant is derived for **coordinate** observables — queries that read one observation.  A
query reading two or more window coordinates at once sees characters `χ_S` with `|S| ≥ 2`, whose
`k`-step eigenvalue `(−λ)^{|S|}` is *positive* for even `|S|`; there the cancellation is absent and
a noise-rate-dependent constant is genuinely needed.  Nothing here claims otherwise, and nothing
here bounds that case.

No `SubstrateL` inhabitation is claimed: this module supplies one clause (E1, at a named base,
ensemble and constant) and says nothing about window sufficiency or Assumption A.
-/

namespace NoisyWindowChain

open MeasureTheory ProbabilityTheory ParityWalk

/-! ## The observation process, defined by its interleaving -/

/-- The observation process of the noisy window chain.

It is *defined* by the interleaving: the observation at time `u` is the residue class `u % k`'s
two-state parity walk, started at the initial bit `ξ (u % k)` and advanced `u / k` steps by the
noise bits `ξ (u % k + k·(j+1))`.  The chain's own recursion `o_{u+k} = ¬o_u ⊕ ξ_{u+k}` is then a
lemma (`obs_add`), not the definition — which is what makes the residue-class decomposition
transparent rather than something to be recovered. -/
def obs (k : ℕ) (ξ : ℕ → Bool) (u : ℕ) : Bool :=
  ParityWalk.walk (ξ (u % k)) (fun j => ξ (u % k + k * (j + 1))) (u / k)

/-- **The interleaving reduction**, deterministic half: along the residue class `r` the chain *is*
a two-state parity walk driven by that class's own noise bits. -/
theorem obs_interleave {k : ℕ} (hk : 0 < k) (ξ : ℕ → Bool) {r : ℕ} (hr : r < k) (j : ℕ) :
    obs k ξ (r + k * j) = ParityWalk.walk (ξ r) (fun i => ξ (r + k * (i + 1))) j := by
  have hmod : (r + k * j) % k = r := by
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hr]
  have hdiv : (r + k * j) / k = j := by
    rw [Nat.add_mul_div_left _ _ hk, Nat.div_eq_of_lt hr, Nat.zero_add]
  rw [obs, hmod, hdiv]

/-- Before the first step the observations are the initial window. -/
private theorem obs_of_lt {k : ℕ} (ξ : ℕ → Bool) {u : ℕ} (hu : u < k) : obs k ξ u = ξ u := by
  rw [obs, Nat.mod_eq_of_lt hu, Nat.div_eq_of_lt hu]
  rfl

/-- **The chain's recursion.**  The observation `k` steps on is the complement of the present one,
xored with the noise bit written at that time. -/
theorem obs_add {k : ℕ} (hk : 0 < k) (ξ : ℕ → Bool) (u : ℕ) :
    obs k ξ (u + k) = !(xor (obs k ξ u) (ξ (u + k))) := by
  have hmod : (u + k) % k = u % k := Nat.add_mod_right u k
  have hdiv : (u + k) / k = u / k + 1 := Nat.add_div_right u hk
  have hnoise : u % k + k * (u / k + 1) = u + k := by
    have h := Nat.mod_add_div u k
    rw [Nat.mul_succ]
    omega
  rw [obs, hmod, hdiv, ParityWalk.walk_succ, hnoise]
  rfl

/-- **The chain's character recursion**, in the multiplicative form `ParityWalk.chiSum_tail`
consumes. -/
theorem chi_obs_add {k : ℕ} (hk : 0 < k) (ξ : ℕ → Bool) (u : ℕ) :
    ParityWalk.chi (obs k ξ u) * ParityWalk.zeta (ξ (u + k))
      = ParityWalk.chi (obs k ξ (u + k)) := by
  rw [obs_add hk, ParityWalk.chi_not, ParityWalk.chi_xor, ParityWalk.zeta_eq_neg_chi]
  ring

/-! ## The noiseless window map -/

section Window

variable (k : ℕ) [NeZero k]

private lemma kpos : 0 < k := Nat.pos_of_ne_zero (NeZero.ne k)

/-- The noiseless window map `w ↦ (w_2, …, w_k, ¬w_1)` on length-`k` windows over `Bool`. -/
def windowMap (w : Fin k → Bool) : Fin k → Bool :=
  fun i => if h : (i : ℕ) + 1 < k then w ⟨(i : ℕ) + 1, h⟩ else !(w 0)

/-- The noiseless extension of a window to a whole observation word: the window itself, then all
noise bits off. -/
private def wext (w : Fin k → Bool) : ℕ → Bool :=
  fun t => if h : t < k then w ⟨t, h⟩ else false

omit [NeZero k] in
private lemma wext_of_lt (w : Fin k → Bool) {t : ℕ} (h : t < k) : wext k w t = w ⟨t, h⟩ := by
  simp [wext, h]

omit [NeZero k] in
private lemma wext_of_ge (w : Fin k → Bool) {t : ℕ} (h : k ≤ t) : wext k w t = false := by
  simp [wext, Nat.not_lt.mpr h]

/-- **The window map iterated is the noiseless chain read through a moving window.** -/
private theorem windowMap_iterate (w : Fin k → Bool) (s : ℕ) (i : Fin k) :
    (windowMap k)^[s] w i = obs k (wext k w) (s + (i : ℕ)) := by
  induction s generalizing i with
  | zero =>
    rw [Function.iterate_zero_apply, Nat.zero_add, obs_of_lt _ i.isLt, wext_of_lt _ _ i.isLt]
  | succ s ih =>
    rw [Function.iterate_succ_apply', windowMap]
    by_cases h : (i : ℕ) + 1 < k
    · rw [dif_pos h, ih ⟨(i : ℕ) + 1, h⟩]
      congr 1
      change s + ((i : ℕ) + 1) = s + 1 + (i : ℕ)
      omega
    · have hik : (i : ℕ) + 1 = k := by have := i.isLt; omega
      rw [dif_neg h, ih 0]
      have hz : ((0 : Fin k) : ℕ) = 0 := by
        simp
      rw [hz, Nat.add_zero]
      have hstep : obs k (wext k w) (s + k) = !(xor (obs k (wext k w) s) (wext k w (s + k))) :=
        obs_add (kpos k) _ s
      rw [show s + 1 + (i : ℕ) = s + k by omega, hstep, wext_of_ge _ _ (by omega)]
      cases obs k (wext k w) s <;> rfl

/-- **The `k`-th power of the window map is bitwise complement.** -/
theorem windowMap_iterate_len (w : Fin k → Bool) : (windowMap k)^[k] w = fun i => !(w i) := by
  funext i
  rw [windowMap_iterate k w k i]
  have h : obs k (wext k w) ((i : ℕ) + k)
      = !(xor (obs k (wext k w) (i : ℕ)) (wext k w ((i : ℕ) + k))) := obs_add (kpos k) _ _
  rw [show k + (i : ℕ) = (i : ℕ) + k by omega, h, wext_of_ge _ _ (by omega),
    obs_of_lt _ i.isLt, wext_of_lt _ _ i.isLt]
  cases w i <;> rfl

/-- **The window map has order dividing `2k`.** -/
theorem windowMap_iterate_two_len (w : Fin k → Bool) : (windowMap k)^[2 * k] w = w := by
  have h2 : 2 * k = k + k := by omega
  rw [h2, Function.iterate_add_apply, windowMap_iterate_len, windowMap_iterate_len]
  funext i
  simp

/-- The window map is a permutation of the window space — an immediate consequence of having a
finite order. -/
theorem windowMap_bijective : Function.Bijective (windowMap k) := by
  have hk1 : 1 ≤ 2 * k := by have := kpos k; omega
  refine Function.bijective_iff_has_inverse.mpr ⟨(windowMap k)^[2 * k - 1], ?_, ?_⟩
  · intro w
    rw [← Function.iterate_succ_apply (windowMap k) (2 * k - 1) w, Nat.succ_eq_add_one,
      Nat.sub_add_cancel hk1, windowMap_iterate_two_len]
  · intro w
    rw [← Function.iterate_succ_apply' (windowMap k) (2 * k - 1) w, Nat.succ_eq_add_one,
      Nat.sub_add_cancel hk1, windowMap_iterate_two_len]

/-! ## The noisy step and the stationarity of the uniform law -/

/-- One step of the *noisy* window chain on windows: the noiseless window map, with the freshly
written observation xored by the noise bit `b`. -/
def noisyStep (w : Fin k → Bool) (b : Bool) : Fin k → Bool :=
  fun i => if (i : ℕ) + 1 < k then windowMap k w i else xor (windowMap k w i) b

/-- Flipping the last window coordinate by a fixed bit is an involution. -/
private def lastFlip (b : Bool) (v : Fin k → Bool) : Fin k → Bool :=
  fun i => if (i : ℕ) + 1 < k then v i else xor (v i) b

omit [NeZero k] in
private lemma lastFlip_involutive (b : Bool) : Function.Involutive (lastFlip k b) := by
  intro v
  funext i
  by_cases h : (i : ℕ) + 1 < k <;> simp [lastFlip, h]

private lemma noisyStep_eq (w : Fin k → Bool) (b : Bool) :
    noisyStep k w b = lastFlip k b (windowMap k w) := rfl

/-- **Each noise value acts as a permutation of the window space.**  This is why the uniform law is
stationary at every noise law: the noise selects among bijections, and a bijection of a finite set
preserves the uniform measure. -/
theorem noisyStep_bijective (b : Bool) : Function.Bijective (fun w => noisyStep k w b) := by
  have : (fun w => noisyStep k w b) = (lastFlip k b) ∘ (windowMap k) := by
    funext w; rw [noisyStep_eq]; rfl
  rw [this]
  exact ((lastFlip_involutive k b).bijective).comp (windowMap_bijective k)

/-- The permutation of the window space induced by a noise value. -/
private noncomputable def noisyStepEquiv (b : Bool) : (Fin k → Bool) ≃ (Fin k → Bool) :=
  Equiv.ofBijective _ (noisyStep_bijective k b)

/-- **The uniform law on windows is stationary for the noisy step**, at every noise law
`p : Bool → ℝ` summing to `1`: the one-step mass landing on a window `v` is again `2^{-k}`.

This is the stationarity equation itself, not a corollary of one: the inner sum over `w` is the
kernel's mass, the outer factor `2^{-k}` the uniform weight. -/
theorem uniform_stationary (p : Bool → ℝ) (hp : p false + p true = 1) (v : Fin k → Bool) :
    (∑ w : Fin k → Bool, ∑ b : Bool, (if noisyStep k w b = v then p b else 0)) * (2 ^ k : ℝ)⁻¹
      = (2 ^ k : ℝ)⁻¹ := by
  have hinner : ∀ b : Bool,
      (∑ w : Fin k → Bool, (if noisyStep k w b = v then p b else 0)) = p b := by
    intro b
    have : (∑ w : Fin k → Bool, (if noisyStep k w b = v then p b else 0))
        = ∑ w : Fin k → Bool, (if noisyStepEquiv k b w = v then p b else 0) := rfl
    rw [this, ← Equiv.sum_comp (noisyStepEquiv k b).symm
      (fun w => if noisyStepEquiv k b w = v then p b else 0)]
    simp
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl fun b _ => hinner b]
  rw [Fintype.sum_bool, add_comm (p true) (p false), hp, one_mul]

end Window

/-! ## The chain's window is the window map's orbit -/

/-- The chain's window at time `t`. -/
def windowAt (k : ℕ) (ξ : ℕ → Bool) (t : ℕ) : Fin k → Bool := fun i => obs k ξ (t + (i : ℕ))

/-- **`windowMap` really is this chain's window map.**  The window one step on is the noisy step
applied to the present window, with the noise bit the chain writes at that time. -/
theorem windowAt_succ {k : ℕ} [NeZero k] (ξ : ℕ → Bool) (t : ℕ) :
    windowAt k ξ (t + 1) = noisyStep k (windowAt k ξ t) (ξ (t + k)) := by
  funext i
  rw [noisyStep, windowMap, windowAt, windowAt]
  by_cases h : (i : ℕ) + 1 < k
  · rw [if_pos h, dif_pos h]
    congr 1
    change t + 1 + (i : ℕ) = t + ((i : ℕ) + 1)
    omega
  · have hik : (i : ℕ) + 1 = k := by have := i.isLt; omega
    rw [if_neg h, dif_neg h]
    have hz : ((0 : Fin k) : ℕ) = 0 := by simp
    rw [hz, Nat.add_zero, show t + 1 + (i : ℕ) = t + k by omega,
      obs_add (Nat.pos_of_ne_zero (NeZero.ne k))]
    cases obs k ξ t <;> cases ξ (t + k) <;> rfl

/-! ## The derived mixing constant -/

section Concentration

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {ξ : ℕ → Ω → Bool} {m : ℝ} {k : ℕ}

/-- The chain's trajectory, as a point of the SQ trajectory space `ℕ → Bool`. -/
def traj (k : ℕ) (ξ : ℕ → Ω → Bool) (ω : Ω) : ℕ → Bool := fun u => obs k (fun i => ξ i ω) u

/-- A **coordinate query ensemble**: read a bounded observable of the observation at each time. -/
def coordEnsemble (φ : Bool → ℝ) : ℕ → (ℕ → Bool) → ℝ := fun i o => φ (o i)

/-- The stationary answer to a coordinate query under the uniform window law. -/
noncomputable def coordMean (φ : Bool → ℝ) : ℝ := (φ false + φ true) / 2

/-- The character coefficient of a `Bool` observable: the amplitude of its non-constant part. -/
private noncomputable def coordCoef (φ : Bool → ℝ) : ℝ := (φ false - φ true) / 2

/-- Every `Bool` observable is its uniform mean plus a multiple of the character. -/
private lemma coord_decomp (φ : Bool → ℝ) (b : Bool) :
    φ b = coordMean φ + coordCoef φ * ParityWalk.chi b := by
  cases b <;> simp [coordMean, coordCoef, ParityWalk.chi] <;> ring

private lemma abs_coordCoef_le_one {φ : Bool → ℝ} (hφ : ∀ b, |φ b| ≤ 1) : |coordCoef φ| ≤ 1 := by
  have h1 := hφ false
  have h2 := hφ true
  rw [abs_le] at h1 h2 ⊢
  constructor <;> rw [coordCoef] <;> linarith [h1.1, h1.2, h2.1, h2.2]

/-- The empirical answer to a coordinate query deviates from the stationary answer by exactly the
character's Birkhoff average, scaled by the observable's character coefficient. -/
private lemma empiricalMean_sub_coordMean (φ : Bool → ℝ) {n : ℕ} (hn : 1 ≤ n) (o : ℕ → Bool) :
    SQOracle.empiricalMean (coordEnsemble φ) n o - coordMean φ
      = coordCoef φ * ((n : ℝ)⁻¹ * ∑ u ∈ Finset.range n, ParityWalk.chi (o u)) := by
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  rw [SQOracle.empiricalMean]
  have hterm : ∀ i, coordEnsemble φ i o = coordMean φ + coordCoef φ * ParityWalk.chi (o i) :=
    fun i => coord_decomp φ (o i)
  have hsum : ∑ i ∈ Finset.range n, coordEnsemble φ i o
      = (n : ℝ) * coordMean φ + coordCoef φ * ∑ u ∈ Finset.range n, ParityWalk.chi (o u) := by
    rw [Finset.sum_congr rfl fun i _ => hterm i, Finset.sum_add_distrib, Finset.sum_const,
      Finset.card_range, nsmul_eq_mul, ← Finset.mul_sum]
  rw [hsum]
  field_simp
  ring

omit [MeasurableSpace Ω] in
/-- The observation at time `u` reads only the noise bits `ξ 0, …, ξ u`. -/
private lemma measurable_obs (hk : 1 ≤ k) (u : ℕ) :
    Measurable[ParityWalk.pastAlg ξ (u + k)] (fun ω => obs k (fun i => ξ i ω) u) := by
  refine ParityWalk.measurable_walk
    (ParityWalk.measurable_pastAlg_xi (lt_of_le_of_lt (Nat.mod_le u k) (by omega))) _ ?_
  intro j hj
  refine ParityWalk.measurable_pastAlg_xi ?_
  have h2 : k * (j + 1) ≤ k * (u / k) := Nat.mul_le_mul_left k hj
  have h3 : u % k + k * (u / k) = u := Nat.mod_add_div u k
  omega

private lemma measurable_traj (hk : 1 ≤ k) (hmeas : ∀ i, Measurable (ξ i)) :
    Measurable (traj k ξ) := by
  refine measurable_pi_lambda _ fun u => ?_
  exact (measurable_obs hk u).mono (ParityWalk.pastAlg_le hmeas (u + k)) le_rfl

omit [MeasurableSpace Ω] in
/-! ### The interleaving as an independence decomposition -/

/-- The residue class `r`'s own process: the chain read along `r, r+k, r+2k, …`. -/
def classProc (k r : ℕ) (ξ : ℕ → Ω → Bool) (ω : Ω) : ℕ → Bool :=
  fun j => obs k (fun i => ξ i ω) (r + k * j)

/-- The joint reading of every residue class *other* than `r`: the noise word with class `r`'s own
coordinates blanked out. -/
def restClasses (k r : ℕ) (ξ : ℕ → Ω → Bool) (ω : Ω) : ℕ → Bool :=
  fun i => if i % k = r then false else ξ i ω

omit [MeasurableSpace Ω] in
private lemma classProc_eq_walk (hk : 1 ≤ k) {r : ℕ} (hr : r < k) (ω : Ω) :
    classProc k r ξ ω
      = fun j => ParityWalk.walk (ξ r ω) (fun i => ξ (r + k * (i + 1)) ω) j := by
  funext j
  exact obs_interleave (by omega) (fun i => ξ i ω) hr j

private lemma mem_class {r : ℕ} (hr : r < k) (s : ℕ) : (r + k * s) % k = r := by
  rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hr]

omit [IsProbabilityMeasure P] in
/-- **The interleaving is an independence decomposition.**  The residue class `r`'s process is
independent of the joint reading of all the other classes: the two are driven by disjoint index sets
of the noise family, and `ParityWalk.indepFun_noiseAlg_compl` turns that into independence.

Together with `obs_interleave` this is the full content of the interleaving: `k` two-state parity
walks, each independent of everything the others see. -/
theorem indepFun_residueClass (hk : 1 ≤ k) (hmeas : ∀ i, Measurable (ξ i))
    (hindep : iIndepFun ξ P) {r : ℕ} (hr : r < k) :
    IndepFun (classProc k r ξ) (restClasses k r ξ) P := by
  classical
  set t : Set ℕ := {i : ℕ | i % k = r} with ht
  have hclass : Measurable[ParityWalk.noiseAlg ξ t] (classProc k r ξ) := by
    refine @measurable_pi_lambda _ _ _ (ParityWalk.noiseAlg ξ t) _ _ fun j => ?_
    have hre : (fun ω => classProc k r ξ ω j)
        = fun ω => ParityWalk.walk (ξ r ω) (fun i => ξ (r + k * (i + 1)) ω) j := by
      funext ω; rw [classProc_eq_walk hk hr ω]
    rw [hre]
    refine ParityWalk.measurable_walk (ParityWalk.measurable_noiseAlg_xi ?_) _ fun i _ => ?_
    · simpa [ht] using mem_class hr 0
    · exact ParityWalk.measurable_noiseAlg_xi (mem_class hr (i + 1))
  have hrest : Measurable[ParityWalk.noiseAlg ξ tᶜ] (restClasses k r ξ) := by
    refine @measurable_pi_lambda _ _ _ (ParityWalk.noiseAlg ξ tᶜ) _ _ fun i => ?_
    by_cases h : i % k = r
    · simp [restClasses, h]
    · simpa [restClasses, h] using
        ParityWalk.measurable_noiseAlg_xi (t := tᶜ) (by simp [ht, h])
  exact ParityWalk.indepFun_noiseAlg_compl hmeas hindep t hclass hrest

omit [IsProbabilityMeasure P] in
/-- **Two distinct residue classes are independent.**  Immediate from `indepFun_residueClass`: the
other class is a measurable reading of the blanked noise word. -/
theorem indepFun_residueClass_pair (hk : 1 ≤ k) (hmeas : ∀ i, Measurable (ξ i))
    (hindep : iIndepFun ξ P) {r r' : ℕ} (hr : r < k) (hr' : r' < k) (hne : r' ≠ r) :
    IndepFun (classProc k r ξ) (classProc k r' ξ) P := by
  classical
  have hgm : Measurable (fun (v : ℕ → Bool) (j : ℕ) =>
      ParityWalk.walk (v r') (fun i => v (r' + k * (i + 1))) j) := by
    refine measurable_pi_lambda _ fun j => ?_
    exact ParityWalk.measurable_walk (measurable_pi_apply r') _
      fun i _ => measurable_pi_apply (r' + k * (i + 1))
  have hcomp : (fun (v : ℕ → Bool) (j : ℕ) =>
      ParityWalk.walk (v r') (fun i => v (r' + k * (i + 1))) j) ∘ (restClasses k r ξ)
      = classProc k r' ξ := by
    funext ω
    have hval : ∀ s : ℕ, restClasses k r ξ ω (r' + k * s) = ξ (r' + k * s) ω := by
      intro s
      have hne2 : (r' + k * s) % k ≠ r := by rw [mem_class hr' s]; exact hne
      simp only [restClasses, if_neg hne2]
    have h0 : restClasses k r ξ ω r' = ξ r' ω := by
      have h := hval 0
      rwa [Nat.mul_zero, Nat.add_zero] at h
    have hrest : (fun i => restClasses k r ξ ω (r' + k * (i + 1)))
        = fun i => ξ (r' + k * (i + 1)) ω := by
      funext i; exact hval (i + 1)
    simp only [Function.comp_apply]
    rw [classProc_eq_walk hk hr' ω, h0, hrest]
  have hind := (indepFun_residueClass hk hmeas hindep hr).comp measurable_id hgm
  rwa [Function.id_comp, hcomp] at hind

omit [MeasurableSpace Ω] in
/-- The character's Birkhoff sum along one orbit never exceeds the horizon. -/
private lemma abs_chiSum_traj_le (ω : Ω) (n : ℕ) :
    |∑ u ∈ Finset.range n, ParityWalk.chi (traj k ξ ω u)| ≤ (n : ℝ) :=
  ParityWalk.abs_chiSum_le_card (fun u => traj k ξ ω u) n

/-- **The derived mixing constant.**  The noisy window chain of window length `k ≥ 1`, at any noise
rate, satisfies the FJS-shaped single-orbit Hoeffding hypothesis at the explicit constant `c = 4k`
for every coordinate query ensemble with a `[−1, 1]`-valued observable.

Two things are absent from the constant and are meant to be.  The **noise rate** is absent: the
hypothesis `-1 ≤ m ≤ 0` on the noise character's mean allows every rate from deterministic
alternation (`m = -1`) to unbiased (`m = 0`), and the bound is uniform over it.  And the **horizon**
enters only through `n`, exactly as in the i.i.d. case; the window length appears alone, as the
boundary allowance the interleaving costs.

Until this theorem `MixingHoeffding` was discharged only at `c = 1` for i.i.d. ensembles
(`BirkhoffTool.mixingHoeffding_of_iid`); this is the first dependent source whose constant the
corpus derives. -/
theorem mixingHoeffding_noisyWindowChain
    (hk : 1 ≤ k) (hmeas : ∀ i, Measurable (ξ i)) (hindep : iIndepFun ξ P)
    (hmean : ∀ u, ∫ ω, ParityWalk.zeta (ξ (u + k) ω) ∂P = m) (hm0 : -1 ≤ m) (hm : m ≤ 0)
    (φ : Bool → ℝ) (hφ : ∀ b, |φ b| ≤ 1) :
    BirkhoffTool.MixingHoeffding (Measure.map (traj k ξ) P) (coordEnsemble φ) (coordMean φ)
      (4 * k : ℝ) := by
  classical
  have hφm : Measurable φ := measurable_from_top
  have htraj : Measurable (traj k ξ) := measurable_traj hk hmeas
  have hkR : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  intro n τ hn hτ
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  -- the deviation event on trajectory space, and its measurability
  set A : Set (ℕ → Bool) :=
    {o | τ ≤ |SQOracle.empiricalMean (coordEnsemble φ) n o - coordMean φ|} with hA
  have hempm : Measurable (SQOracle.empiricalMean (coordEnsemble φ) n) := by
    refine Measurable.const_mul ?_ _
    exact Finset.measurable_fun_sum (Finset.range n) fun i _ => hφm.comp (measurable_pi_apply i)
  have hAmeas : MeasurableSet A :=
    measurableSet_le measurable_const ((hempm.sub_const _).abs)
  -- transfer to the source space
  have hmap : (Measure.map (traj k ξ) P).real A = P.real (traj k ξ ⁻¹' A) := by
    simp only [Measure.real, Measure.map_apply htraj hAmeas]
  -- the pullback sits inside the Birkhoff-sum deviation event
  set B : Set Ω := {ω | (n : ℝ) * τ ≤ |∑ u ∈ Finset.range n, ParityWalk.chi (traj k ξ ω u)|}
    with hB
  have hsub : traj k ξ ⁻¹' A ⊆ B := by
    intro ω hω
    simp only [hA, Set.mem_preimage, Set.mem_setOf_eq] at hω
    simp only [hB, Set.mem_setOf_eq]
    rw [empiricalMean_sub_coordMean φ hn] at hω
    set S : ℝ := ∑ u ∈ Finset.range n, ParityWalk.chi (traj k ξ ω u) with hS
    have hval : |coordCoef φ * ((n : ℝ)⁻¹ * S)| = |coordCoef φ| * ((n : ℝ)⁻¹ * |S|) := by
      rw [abs_mul, abs_mul, abs_inv, abs_of_nonneg hn0.le]
    rw [hval] at hω
    have hc := abs_coordCoef_le_one hφ
    have habs : (0 : ℝ) ≤ |S| := abs_nonneg _
    have hinv : (0 : ℝ) < (n : ℝ)⁻¹ := by positivity
    have hX : (0 : ℝ) ≤ (n : ℝ)⁻¹ * |S| := mul_nonneg hinv.le habs
    have h1 : τ ≤ (n : ℝ)⁻¹ * |S| := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hc) hX]
    calc (n : ℝ) * τ ≤ (n : ℝ) * ((n : ℝ)⁻¹ * |S|) :=
          mul_le_mul_of_nonneg_left h1 hn0.le
      _ = |S| := by field_simp
  rw [hmap]
  have hmono : P.real (traj k ξ ⁻¹' A) ≤ P.real B :=
    measureReal_mono hsub (measure_ne_top _ _)
  refine hmono.trans ?_
  -- three regimes
  by_cases hτ1 : 1 < τ
  · -- beyond the observable's own range the event is empty
    have hempty : B = ∅ := by
      ext ω
      simp only [hB, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_le]
      calc |∑ u ∈ Finset.range n, ParityWalk.chi (traj k ξ ω u)| ≤ (n : ℝ) :=
            abs_chiSum_traj_le ω n
        _ < (n : ℝ) * τ := by nlinarith
    rw [hempty]
    simp only [measureReal_empty]
    positivity
  replace hτ1 : τ ≤ 1 := not_lt.mp hτ1
  by_cases hbig : 4 * (k : ℝ) < (n : ℝ) * τ
  case neg =>
    replace hsmall : (n : ℝ) * τ ≤ 4 * k := not_lt.mp hbig
    -- the bound is not yet binding
    have hbound : (n : ℝ) * τ ^ 2 ≤ 4 * k := by nlinarith
    have hexp : (1 : ℝ) ≤ 2 * Real.exp (-(n : ℝ) * τ ^ 2 / (2 * (4 * k : ℝ))) := by
      have hx : -(1 : ℝ) / 2 ≤ -(n : ℝ) * τ ^ 2 / (2 * (4 * k : ℝ)) := by
        rw [div_le_div_iff₀ (by norm_num) (by positivity)]
        nlinarith
      have hlin := Real.add_one_le_exp (-(n : ℝ) * τ ^ 2 / (2 * (4 * k : ℝ)))
      linarith
    exact le_trans MeasureTheory.measureReal_le_one hexp
  case pos =>
    -- the sub-Gaussian regime
    have hnk : k ≤ n := by
      have : (4 : ℝ) * k < (n : ℝ) := by nlinarith
      have : (k : ℝ) < (n : ℝ) := by nlinarith
      exact_mod_cast le_of_lt this
    set N : ℕ := n - k with hN
    have hNk : N + k = n := by omega
    have hε : (0 : ℝ) ≤ (n : ℝ) * τ - 2 * k := by nlinarith
    have htail := ParityWalk.chiSum_tail hmeas hindep hmean hm0 hm
      (fun u ω => obs k (fun i => ξ i ω) u) (fun u => measurable_obs hk u)
      (fun u ω => chi_obs_add (by omega) (fun i => ξ i ω) u) N hε
    rw [hNk] at htail
    have hsetB : B = {ω | ((n : ℝ) * τ - 2 * k) + 2 * k
        ≤ |∑ u ∈ Finset.range n, ParityWalk.chi (obs k (fun i => ξ i ω) u)|} := by
      ext ω; simp only [hB, Set.mem_setOf_eq, traj]; constructor <;> intro h <;> linarith
    rw [hsetB]
    refine htail.trans ?_
    -- compare the two exponents
    have hNpos : (0 : ℝ) < (N : ℝ) := by
      have : 0 < N := by
        have h4 : (4 : ℝ) * k < (n : ℝ) := by nlinarith
        have : (2 : ℝ) * k < (n : ℝ) := by nlinarith
        have hkn : 2 * k < n := by exact_mod_cast this
        omega
      exact_mod_cast this
    have hNle : (N : ℝ) ≤ (n : ℝ) := by
      have : N ≤ n := by omega
      exact_mod_cast this
    have hhalf : (n : ℝ) * τ / 2 ≤ (n : ℝ) * τ - 2 * k := by nlinarith
    have hnt2 : (0 : ℝ) ≤ (n : ℝ) * τ ^ 2 := mul_nonneg hn0.le (sq_nonneg τ)
    have hkey : (n : ℝ) * τ ^ 2 / (2 * (4 * k : ℝ))
        ≤ ((n : ℝ) * τ - 2 * k) ^ 2 / (2 * (N : ℝ)) := by
      have hstep : (n : ℝ) * τ ^ 2 / 8 ≤ ((n : ℝ) * τ - 2 * k) ^ 2 / (2 * (N : ℝ)) := by
        rw [div_le_div_iff₀ (by norm_num) (by positivity)]
        have hnt : (0 : ℝ) ≤ (n : ℝ) * τ / 2 := by positivity
        have h1 := mul_self_le_mul_self hnt hhalf
        have h2 : (N : ℝ) * ((n : ℝ) * τ ^ 2) ≤ (n : ℝ) * ((n : ℝ) * τ ^ 2) :=
          mul_le_mul_of_nonneg_right hNle hnt2
        nlinarith [h1, h2]
      have hshrink : (n : ℝ) * τ ^ 2 / (2 * (4 * k : ℝ)) ≤ (n : ℝ) * τ ^ 2 / 8 := by
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]
        nlinarith [mul_nonneg hnt2 (by linarith : (0 : ℝ) ≤ 8 * (k : ℝ) - 8)]
      linarith
    have hneg : -((n : ℝ) * τ - 2 * k) ^ 2 / (2 * (N : ℝ))
        ≤ -(n : ℝ) * τ ^ 2 / (2 * (4 * k : ℝ)) := by
      have e1 : -((n : ℝ) * τ - 2 * k) ^ 2 / (2 * (N : ℝ))
          = -(((n : ℝ) * τ - 2 * k) ^ 2 / (2 * (N : ℝ))) := by ring
      have e2 : -(n : ℝ) * τ ^ 2 / (2 * (4 * k : ℝ))
          = -((n : ℝ) * τ ^ 2 / (2 * (4 * k : ℝ))) := by ring
      rw [e1, e2]
      linarith [hkey]
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hneg) (by norm_num)

/-- **The standing vacuity guard.**  At this same trajectory law and this same constant, the
predicate is refutable: the pinned ensemble of `BirkhoffTool.not_mixingHoeffding_pinned` fails it.
So `mixingHoeffding_noisyWindowChain` is a statement about the chain and its query ensemble, not an
artefact of a constant that carries no content (contrast
`BirkhoffTool.mixingHoeffding_of_nonpos`, which holds for everything at `c ≤ 0`). -/
theorem not_mixingHoeffding_noisyWindowChain_pinned
    (hk : 1 ≤ k) (hmeas : ∀ i, Measurable (ξ i)) :
    ¬ BirkhoffTool.MixingHoeffding (Measure.map (traj k ξ) P)
        (fun (_ : ℕ) (_ : ℕ → Bool) => (1 : ℝ)) 0 (4 * k : ℝ) := by
  have htraj : Measurable (traj k ξ) := measurable_traj hk hmeas
  have : IsProbabilityMeasure (Measure.map (traj k ξ) P) :=
    Measure.isProbabilityMeasure_map htraj.aemeasurable
  refine BirkhoffTool.not_mixingHoeffding_pinned _ ?_
  have : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  linarith

end Concentration

end NoisyWindowChain

/-! ## Axiom audit

The window-map order fact, the stationarity equation, the independence decomposition, the derived
mixing constant and its vacuity guard are all `#print axioms`-clean on the standard triple, and the
guards below make that build-enforced. -/

set_option linter.style.longLine false

/-- info: 'NoisyWindowChain.windowMap_iterate_two_len' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NoisyWindowChain.windowMap_iterate_two_len

/-- info: 'NoisyWindowChain.uniform_stationary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NoisyWindowChain.uniform_stationary

/-- info: 'NoisyWindowChain.indepFun_residueClass' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NoisyWindowChain.indepFun_residueClass

/-- info: 'NoisyWindowChain.mixingHoeffding_noisyWindowChain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NoisyWindowChain.mixingHoeffding_noisyWindowChain

/-- info: 'NoisyWindowChain.not_mixingHoeffding_noisyWindowChain_pinned' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NoisyWindowChain.not_mixingHoeffding_noisyWindowChain_pinned
