/-
Copyright (c) 2026 Mykola Palamarchuk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mykola Palamarchuk
-/
import ALT.BirkhoffTool
import ALT.ParityWalk
import ALT.PersistentWalk

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

for coordinate query ensembles `Z i o = φ (o i)` with `φ` valued in `[−1, 1]`.  A second theorem,
`mixingHoeffding_noisyWindowChain_pair`, discharges it for the **two-offset** ensembles
`Z t o = ψ (o_{t+a}, o_{t+b})` that a learner of single-literal decision lists schedules
([SQ] §3.1), at the named constant

`c = pairConst k η = O(k/η)`,

whenever the two offsets read distinct residue classes mod `k`.

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

At two-offset observables it does exist, and is priced.  A cross-class *pair* character is the
product of two coordinate characters, and under one chain step the two complements cancel
(`chi_pairObs_add`): the eigenvalue is `λ² ≥ 0`, the walk is *persistent* rather than alternating,
and the telescope divides by the gap `1 − λ² = 4η(1−η)` instead of being helped by `1 + λ`.  Hence
`pairConst k η = O(k/η)` (`pairConst_le`), and the `0 < η` hypothesis is load-bearing.

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
* `pairEnsemble`, `pairMean`, `pairObs` — the two-offset query class, its stationary answer, and
  the pair process, whose character is the product of the two observations' characters.
* `chi_pairObs_add` — **the sign cancellation**: under one chain step both observations complement
  and the two complements cancel, so a cross-class pair character is a *persistent* walk with
  eigenvalue `λ² ≥ 0`.
* `mixingHoeffding_noisyWindowChain_pair` — **the second constant**: `pairConst k η`, bounded by
  `108·k/η + 432·k` (`pairConst_le`), for every two-offset query with offsets in distinct residue
  classes and every noise rate `η > 0`.
* `not_mixingHoeffding_pinned_pair` — the module's single two-offset refutation device: a pinned
  two-offset answer at distance `≥ 1` from the declared one refutes the predicate at every positive
  constant.  Every two-offset refutation in the development is an instance of it.
* `not_mixingHoeffding_noisyWindowChain_pair_frozen` — at `η = 0` that predicate is refutable at
  **every** positive constant, so the noise-rate dependence is forced rather than proof slack.
* `chi_pairObs_lagK`, `samePairMean`, `samePairConst` — the **same-class** pair at the chain's own
  lag: its character is a single noise character, so the answer is displaced to
  `pairMean ψ + pairCoefAB ψ · m` and the constant is `48k`.
* `mixingHoeffding_noisyWindowChain_pair_lagK` — **the third constant**: `samePairConst k = 48k`,
  free of the noise rate, for every query at offsets `(a, a + k)` and every `m ∈ [−1, 0]`.
* `not_mixingHoeffding_noisyWindowChain_samePair_flatMean` /
  `mixingHoeffding_frozen_samePair_correctMean` — the matched pair that locates the same-class noise
  dependence in the ANSWER: one configuration, refuted at the flat answer at every positive
  constant, satisfied at the displaced answer at every constant.

## Scope

Three query classes are covered, and they behave differently.  A **coordinate** query reads one
observation and sees a character `χ_S` with `|S| = 1`, whose `k`-step eigenvalue `−λ` is negative:
the cancellation described above is available and the constant `4k` carries no noise rate.  A
**cross-class two-offset** query — offsets in distinct residue classes — sees a character with
`|S| = 2` whose eigenvalue `λ²` is *positive*: nothing cancels, and `pairConst k η` is genuinely
noise-rate-dependent — provably so, since `not_mixingHoeffding_noisyWindowChain_pair_frozen`
refutes the predicate at `η = 0` at every positive constant, on a trajectory law that satisfies
every hypothesis of the coordinate theorem.  A **same-class two-offset** query at the chain's own
lag — offsets `(a, a + k)` — is a third case again: its pair character is a single noise character,
so the constant `48k` is free of the noise rate, but the stationary answer is displaced by
`pairCoefAB ψ · m`.  There the noise rate is provably load-bearing in the ANSWER
(`not_mixingHoeffding_noisyWindowChain_samePair_flatMean`) and provably absent from the constant.

Not covered: queries reading three or more observations at once, and same-class offsets at the
lags `2k, 3k, …` (whose multiplier is a product over a block of noise bits, and which the
single-literal schedule does not use).

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

/-- Before the first step the observations are the initial window: the noise word's first `k` bits
*are* the chain's initial window, which is what makes a loaded initial state and a noise word the
same datum. -/
theorem obs_of_lt {k : ℕ} (ξ : ℕ → Bool) {u : ℕ} (hu : u < k) : obs k ξ u = ξ u := by
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
private theorem chi_obs_add {k : ℕ} (hk : 0 < k) (ξ : ℕ → Bool) (u : ℕ) :
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

/-- The chain's trajectory map is measurable: each observation reads finitely many noise bits. -/
lemma measurable_traj (hk : 1 ≤ k) (hmeas : ∀ i, Measurable (ξ i)) :
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

/-! ### The two-offset query class

The scope note above records that a query reading *two* observations is not covered by the
coordinate constant.  The rest of this module covers exactly that case, for the class a learner of
single-literal decision lists actually schedules: each of its queries correlates one window literal
with the label, so it reads two observations at fixed offsets ([SQ] §3.1). -/

/-- A **two-offset query ensemble**: at each query time, read a bounded observable of the
observations at two fixed offsets ahead. -/
def pairEnsemble (ψ : Bool → Bool → ℝ) (a b : ℕ) : ℕ → (ℕ → Bool) → ℝ :=
  fun t o => ψ (o (t + a)) (o (t + b))

/-- The stationary answer to a two-offset query whose offsets read *distinct* residue classes: the
two observations are then independent and uniform under the stationary window law, so the answer is
the flat average of `ψ` over its four argument pairs. -/
noncomputable def pairMean (ψ : Bool → Bool → ℝ) : ℝ :=
  (ψ false false + ψ false true + ψ true false + ψ true true) / 4

/-- The **pair character** `χ(u)·χ(v)`: the two-offset observable that isolates the genuinely
two-coordinate part of a query, and the one the guard below is pinned at. -/
noncomputable def pairChar (u v : Bool) : ℝ := ParityWalk.chi u * ParityWalk.chi v

@[simp] lemma pairMean_pairChar : pairMean pairChar = 0 := by
  norm_num [pairMean, pairChar, ParityWalk.chi]

lemma abs_pairChar_le_one (u v : Bool) : |pairChar u v| ≤ 1 := by
  cases u <;> cases v <;> norm_num [pairChar, ParityWalk.chi]

/-! ### The guard: at zero noise no constant covers the two-offset class

At noise rate `η = 0` each residue class's walk alternates deterministically, so a cross-class pair
character is *frozen* at its initial value: the empirical answer never moves, and the tail bound
`2·exp(−nτ²/(2c))` — which tends to `0` in `n` at every positive `c` — cannot dominate it.  The
witness below pins one such configuration completely.

Two things make this a genuine perturbation test of `mixingHoeffding_noisyWindowChain` rather than a
degenerate instance.  The pinned noise word satisfies *every* hypothesis of that theorem, at
`m = -1`; and dropping only the distinct-class requirement recovers the coordinate case, where the
landed constant `c = 4k` does cover the same trajectory law.  So the noise-rate dependence of the
pair constant is a fact about the query class, not slack in a proof. -/

/-- The guard's noise word: the initial window `(false, true, false)` at window length `3`, and
**no noise at all** — `frozenWord i = false` for every `i ≥ 3`. -/
def frozenWord (i : ℕ) : Bool := decide (i = 1)

private lemma frozenWord_of_three_le {i : ℕ} (h : 3 ≤ i) : frozenWord i = false := by
  simp only [frozenWord, decide_eq_false_iff_not]
  omega

/-- At zero noise the observation complements every `k` steps: the chain's recursion with the noise
bit switched off. -/
lemma frozen_obs_add (t : ℕ) : obs 3 frozenWord (t + 3) = !(obs 3 frozenWord t) := by
  rw [obs_add (by norm_num) frozenWord t, frozenWord_of_three_le (by omega)]
  cases obs 3 frozenWord t <;> rfl

/-- **The frozen pair identity.**  Offsets `0` and `2` read distinct residue classes mod `3`, yet
with this initial window the two observations agree at *every* time — so their pair character is
pinned at `+1` forever.  (Both sides complement together every three steps, and the three base
values agree.) -/
lemma frozen_obs_shift (t : ℕ) : obs 3 frozenWord (t + 2) = obs 3 frozenWord t := by
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    match t with
    | 0 => rfl
    | 1 => rfl
    | 2 => rfl
    | (n + 3) =>
      rw [show n + 3 + 2 = (n + 2) + 3 by omega, frozen_obs_add (n + 2), frozen_obs_add n,
        ih n (by omega)]

/-- The pinning behind the guard: at offsets `0` and `2` the two observations agree at every time,
so their pair character never leaves `+1`. -/
private lemma frozen_pin_zero_two (t : ℕ) :
    pairChar (obs 3 frozenWord (t + 0)) (obs 3 frozenWord (t + 2)) = 1 := by
  rw [Nat.add_zero, frozen_obs_shift t, pairChar]
  cases obs 3 frozenWord t <;> norm_num [ParityWalk.chi]

/-- A two-offset query reads two coordinates of the trajectory, hence is measurable. -/
lemma measurable_pairEnsemble (ψ : Bool → Bool → ℝ) (a b : ℕ) (t : ℕ) :
    Measurable (pairEnsemble ψ a b t) := by
  have h : pairEnsemble ψ a b t
      = (fun p : Bool × Bool => ψ p.1 p.2) ∘ fun o : ℕ → Bool => (o (t + a), o (t + b)) := rfl
  rw [h]
  exact Measurable.of_discrete.comp
    ((measurable_pi_apply (t + a)).prodMk (measurable_pi_apply (t + b)))

private lemma measurable_empiricalMean_pair (ψ : Bool → Bool → ℝ) (a b : ℕ) (n : ℕ) :
    Measurable (SQOracle.empiricalMean (pairEnsemble ψ a b) n) := by
  refine Measurable.const_mul ?_ _
  exact Finset.measurable_fun_sum (Finset.range n) fun t _ => measurable_pairEnsemble ψ a b t

/-- **A pinned two-offset answer refutes E1 at every positive constant.**  Read along one
*deterministic* noise word `w`, if a two-offset query's value never moves off `v`, then its
empirical answer is `v` at every horizon; a declared answer at distance `1` or more from `v` then
sits outside a deviation event of probability `1`, and the tail `2·exp(−nτ²/(2c))` — which tends to
`0` in `n` at every positive `c` — cannot dominate it.

This is the shape every two-offset refutation in this module takes; what changes between them is
which pinned value sits how far from which declared answer.  It is the *only* refutation device
here, so a new guard is a new pinning computation and nothing else. -/
theorem not_mixingHoeffding_pinned_pair {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {k a b : ℕ} (hk : 1 ≤ k) (w : ℕ → Bool) (ψ : Bool → Bool → ℝ)
    {v ans c : ℝ} (hc : 0 < c) (hpin : ∀ t, ψ (obs k w (t + a)) (obs k w (t + b)) = v)
    (hd : 1 ≤ |v - ans|) :
    ¬ BirkhoffTool.MixingHoeffding (Measure.map (traj k (fun i (_ : Ω) => w i)) P)
        (pairEnsemble ψ a b) ans c := by
  intro hmix
  have hFmeas : Measurable (traj k (fun i (_ : Ω) => w i)) :=
    measurable_traj hk fun _ => measurable_const
  have : IsProbabilityMeasure (Measure.map (traj k (fun i (_ : Ω) => w i)) P) :=
    Measure.isProbabilityMeasure_map hFmeas.aemeasurable
  refine BirkhoffTool.not_mixingHoeffding_pinned
    (Measure.map (traj k (fun i (_ : Ω) => w i)) P) hc ?_
  intro n τ hn hτ
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hemp : ∀ ω : Ω,
      SQOracle.empiricalMean (pairEnsemble ψ a b) n (traj k (fun i (_ : Ω) => w i) ω) = v := by
    intro ω
    have hterm : ∀ t : ℕ,
        pairEnsemble ψ a b t (traj k (fun i (_ : Ω) => w i) ω) = v := fun t => hpin t
    rw [SQOracle.empiricalMean, Finset.sum_congr rfl fun t _ => hterm t, Finset.sum_const,
      Finset.card_range, nsmul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hn0, one_mul]
  have hconst : ∀ o : ℕ → Bool,
      SQOracle.empiricalMean (fun (_ : ℕ) (_ : ℕ → Bool) => (1 : ℝ)) n o = 1 := by
    intro o
    rw [SQOracle.empiricalMean, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one,
      inv_mul_cancel₀ hn0]
  by_cases hτ1 : τ ≤ 1
  · -- the pinned answer sits at distance `≥ 1` from the target, so the tail bound must exceed `1`
    set A : Set (ℕ → Bool) :=
      {o | τ ≤ |SQOracle.empiricalMean (pairEnsemble ψ a b) n o - ans|} with hA
    have hAmeas : MeasurableSet A :=
      measurableSet_le measurable_const
        (((measurable_empiricalMean_pair ψ a b n).sub_const _).abs)
    have hpre : traj k (fun i (_ : Ω) => w i) ⁻¹' A = Set.univ := by
      ext ω
      simp only [hA, Set.mem_preimage, Set.mem_setOf_eq, Set.mem_univ, iff_true, hemp ω]
      linarith
    have hone : (Measure.map (traj k (fun i (_ : Ω) => w i)) P).real A = 1 := by
      simp [Measure.real, Measure.map_apply hFmeas hAmeas, hpre]
    have hb := hmix n τ hn hτ
    rw [hone] at hb
    exact le_trans MeasureTheory.measureReal_le_one hb
  · -- beyond the observable's own range the constant ensemble's event is empty
    replace hτ1 : 1 < τ := not_le.mp hτ1
    have hempty : {o : ℕ → Bool | τ ≤ |SQOracle.empiricalMean
        (fun (_ : ℕ) (_ : ℕ → Bool) => (1 : ℝ)) n o - 0|} = ∅ := by
      ext o
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_le, hconst o]
      simpa using hτ1
    rw [hempty, measureReal_empty]
    positivity

/-- **The guard.**  At window length `3`, offsets `0` and `2` (distinct residue classes) and the
noise rate `η = 0`, the two-offset predicate is refutable at **every** positive constant.  So no
noise-free constant covers the two-offset class, and in particular the coordinate constant `4k` of
`mixingHoeffding_noisyWindowChain` does not extend to it: the `η`-dependence of
`mixingHoeffding_noisyWindowChain_pair` below is forced, not an artefact of its proof. -/
theorem not_mixingHoeffding_noisyWindowChain_pair_frozen
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] {c : ℝ} (hc : 0 < c) :
    ¬ BirkhoffTool.MixingHoeffding (Measure.map (traj 3 (fun i (_ : Ω) => frozenWord i)) P)
        (pairEnsemble pairChar 0 2) (pairMean pairChar) c := by
  refine not_mixingHoeffding_pinned_pair P (by norm_num) frozenWord pairChar hc
    frozen_pin_zero_two ?_
  rw [pairMean_pairChar]; norm_num

/-! ### The pair process and its persistent multiplier

`pairObs` combines the two observations a two-offset query reads by `xor`, so that its character is
their product.  Under the chain's own recursion both observations complement, **and the two
complements cancel**: the pair character is multiplied by a *product* of two noise characters,
whose mean is `m² ≥ 0`.  So where each coordinate alone alternates — the negative eigenvalue that
makes `mixingHoeffding_noisyWindowChain`'s constant noise-rate-free — a cross-class pair is a
*persistent* walk, and its constant must pay for the gap.  The frozen refutation above is the
proof that it must. -/

/-- The **pair process**: the two observations a two-offset query reads, combined by `xor`. -/
def pairObs (k a b : ℕ) (ξ : ℕ → Bool) (t : ℕ) : Bool :=
  xor (obs k ξ (t + a)) (obs k ξ (t + b))

private lemma chi_pairObs (k a b : ℕ) (ξ : ℕ → Bool) (t : ℕ) :
    ParityWalk.chi (pairObs k a b ξ t)
      = ParityWalk.chi (obs k ξ (t + a)) * ParityWalk.chi (obs k ξ (t + b)) :=
  ParityWalk.chi_xor _ _

/-- **The pair recursion at one chain step, and the sign cancellation.**  Both observations
complement and pick up their own noise character; the two complements cancel, leaving the pair
character multiplied by a product of two *distinct* noise characters. -/
theorem chi_pairObs_add {k : ℕ} (hk : 0 < k) (a b : ℕ) (ξ : ℕ → Bool) (t : ℕ) :
    ParityWalk.chi (pairObs k a b ξ t)
        * (ParityWalk.zeta (ξ (t + a + k)) * ParityWalk.zeta (ξ (t + b + k)))
      = ParityWalk.chi (pairObs k a b ξ (t + k)) := by
  rw [chi_pairObs, chi_pairObs, show t + k + a = t + a + k by omega,
    show t + k + b = t + b + k by omega, ← chi_obs_add hk ξ (t + a), ← chi_obs_add hk ξ (t + b)]
  ring

/-- The pair multiplier over `L` chain steps: the product of the `2L` noise characters the two
residue classes consume between time `t` and time `t + k·L`. -/
private noncomputable def pairMult (k a b L : ℕ) (ξ : ℕ → Bool) (t : ℕ) : ℝ :=
  ∏ j ∈ Finset.range L,
    ParityWalk.zeta (ξ (t + a + k * (j + 1))) * ParityWalk.zeta (ξ (t + b + k * (j + 1)))

/-- **The pair recursion at the blocking lag `k·L`.** -/
private theorem chi_pairObs_add_mul {k : ℕ} (hk : 0 < k) (a b L : ℕ) (ξ : ℕ → Bool) (t : ℕ) :
    ParityWalk.chi (pairObs k a b ξ t) * pairMult k a b L ξ t
      = ParityWalk.chi (pairObs k a b ξ (t + k * L)) := by
  induction L with
  | zero => simp [pairMult]
  | succ L ih =>
    rw [pairMult, Finset.prod_range_succ, ← mul_assoc, ← pairMult, ih,
      show t + a + k * (L + 1) = t + k * L + a + k by ring,
      show t + b + k * (L + 1) = t + k * L + b + k by ring,
      show t + k * (L + 1) = t + k * L + k by ring]
    exact chi_pairObs_add hk a b ξ (t + k * L)

private lemma abs_pairMult (k a b L : ℕ) (ξ : ℕ → Bool) (t : ℕ) :
    |pairMult k a b L ξ t| = 1 := by
  rw [pairMult, Finset.abs_prod]
  refine Finset.prod_eq_one fun j _ => ?_
  rw [abs_mul]
  cases ξ (t + a + k * (j + 1)) <;> cases ξ (t + b + k * (j + 1)) <;>
    norm_num [ParityWalk.zeta]

private lemma pairMult_mem_Icc (k a b L : ℕ) (ξ : ℕ → Bool) (t : ℕ) :
    pairMult k a b L ξ t ∈ Set.Icc (-1 : ℝ) 1 := by
  have h := abs_pairMult k a b L ξ t
  rw [Set.mem_Icc]
  constructor <;> [exact (abs_le.mp h.le).1; exact (abs_le.mp h.le).2]

/-- The noise indices the pair multiplier at time `t` consumes. -/
private def pairBlock (k a b L : ℕ) (t : ℕ) : Set ℕ :=
  {i | ∃ j < L, i = t + a + k * (j + 1) ∨ i = t + b + k * (j + 1)}

/-! ### Arithmetic of the two residue classes -/

/-- Offsets in distinct residue classes never collide, from bases in one class and at any pair of
step counts.  This is the one place `¬ a ≡ b [MOD k]` is used, and it is used everywhere. -/
private lemma pairIdx_ne {a b : ℕ} (hab : ¬ a ≡ b [MOD k]) {s t : ℕ} (hst : s ≡ t [MOD k])
    (i j : ℕ) : s + a + k * i ≠ t + b + k * j := by
  intro h
  refine hab (Nat.ModEq.add_left_cancel hst ?_)
  have hmod : (s + a + k * i) % k = (t + b + k * j) % k := by rw [h]
  rwa [Nat.add_mul_mod_self_left, Nat.add_mul_mod_self_left] at hmod

/-- Every step of a residue class starts from the same class as the class's own base point. -/
private lemma classBase_modEq (c L w : ℕ) : c + k * L * w ≡ c [MOD k] := by
  change (c + k * L * w) % k = c % k
  rw [mul_assoc, Nat.add_mul_mod_self_left]

private lemma eq_of_block_index {L u v j j' : ℕ} (hL : 0 < L) (hj : j < L) (hj' : j' < L)
    (h : L * u + j = L * v + j') : u = v := by
  have h1 : (L * u + j) / L = u := by
    rw [Nat.mul_add_div hL, Nat.div_eq_of_lt hj, Nat.add_zero]
  have h2 : (L * v + j') / L = v := by
    rw [Nat.mul_add_div hL, Nat.div_eq_of_lt hj', Nat.add_zero]
  rw [← h1, ← h2, h]

/-- **The blocks of one residue class are pairwise disjoint.**  Within a class the a-side indices
advance by `k·L` per step and the b-side likewise, while an a-side index never equals a b-side one
because the offsets sit in distinct classes mod `k`.  (Across *different* classes the blocks do
overlap — which is exactly why the class sums are combined without independence.) -/
private lemma pairBlock_disjoint {a b L : ℕ} (hk : 0 < k) (hL : 0 < L) (hab : ¬ a ≡ b [MOD k])
    (c u v : ℕ) (huv : u ≠ v) :
    Disjoint (pairBlock k a b L (c + k * L * u)) (pairBlock k a b L (c + k * L * v)) := by
  have hbase : c + k * L * u ≡ c + k * L * v [MOD k] :=
    (classBase_modEq c L u).trans (classBase_modEq c L v).symm
  -- two steps of the same side, in different classes, are different indices
  have hstep : ∀ w j j' : ℕ, j < L → j' < L →
      c + k * L * u + w + k * (j + 1) = c + k * L * v + w + k * (j' + 1) → u = v := by
    intro w j j' hj hj' heq
    have h1 : k * (L * u) + k * (j + 1) = k * (L * v) + k * (j' + 1) := by
      simp only [mul_assoc] at heq; omega
    rw [← Nat.mul_add, ← Nat.mul_add] at h1
    exact eq_of_block_index hL hj hj' (by have := Nat.eq_of_mul_eq_mul_left hk h1; omega)
  rw [Set.disjoint_left]
  rintro i ⟨j, hj, hi⟩ ⟨j', hj', hi'⟩
  rcases hi with hi | hi <;> rcases hi' with hi' | hi'
  · exact huv (hstep a j j' hj hj' (by rw [← hi, ← hi']))
  · exact pairIdx_ne hab hbase (j + 1) (j' + 1) (by rw [← hi, ← hi'])
  · exact pairIdx_ne hab hbase.symm (j' + 1) (j + 1) (by rw [← hi, ← hi'])
  · exact huv (hstep b j j' hj hj' (by rw [← hi, ← hi']))

/-! ### Measurability of the pair data -/

omit [MeasurableSpace Ω] in
/-- The observation at time `w` reads only noise bits of its own residue class, up to time `w`. -/
private lemma measurable_obs_noiseAlg {S : Set ℕ} (hk : 1 ≤ k) (w : ℕ)
    (hS : ∀ i, i % k = w % k → i ≤ w → i ∈ S) :
    Measurable[ParityWalk.noiseAlg ξ S] (fun ω => obs k (fun i => ξ i ω) w) := by
  have hmodmod : w % k % k = w % k := Nat.mod_eq_of_lt (Nat.mod_lt _ (by omega))
  refine ParityWalk.measurable_walk
    (ParityWalk.measurable_noiseAlg_xi (hS _ hmodmod (Nat.mod_le w k))) _ fun j hj => ?_
  refine ParityWalk.measurable_noiseAlg_xi (hS _ ?_ ?_)
  · rw [Nat.add_mul_mod_self_left, hmodmod]
  · have h2 : k * (j + 1) ≤ k * (w / k) := Nat.mul_le_mul_left k hj
    have h3 : w % k + k * (w / k) = w := Nat.mod_add_div w k
    omega

omit [MeasurableSpace Ω] in
private lemma measurable_pairObs_noiseAlg {S : Set ℕ} {a b : ℕ} (hk : 1 ≤ k) (t : ℕ)
    (hSa : ∀ i, i % k = (t + a) % k → i ≤ t + a → i ∈ S)
    (hSb : ∀ i, i % k = (t + b) % k → i ≤ t + b → i ∈ S) :
    Measurable[ParityWalk.noiseAlg ξ S] (fun ω => pairObs k a b (fun i => ξ i ω) t) :=
  ParityWalk.measurable_xor (measurable_obs_noiseAlg hk _ hSa) (measurable_obs_noiseAlg hk _ hSb)

omit [MeasurableSpace Ω] in
private lemma measurable_pairMult {a b L : ℕ} (t : ℕ) :
    Measurable[ParityWalk.noiseAlg ξ (pairBlock k a b L t)]
      (fun ω => pairMult k a b L (fun i => ξ i ω) t) := by
  refine Finset.measurable_fun_prod _ fun j hj => ?_
  simp only [Finset.mem_range] at hj
  have h1 : t + a + k * (j + 1) ∈ pairBlock k a b L t := ⟨j, hj, Or.inl rfl⟩
  have h2 : t + b + k * (j + 1) ∈ pairBlock k a b L t := ⟨j, hj, Or.inr rfl⟩
  exact (ParityWalk.measurable_zeta.comp (ParityWalk.measurable_noiseAlg_xi h1)).mul
    (ParityWalk.measurable_zeta.comp (ParityWalk.measurable_noiseAlg_xi h2))

/-- A block index of one residue class lies in the class of its own offset. -/
private lemma modEq_blockIdx (L c w j x : ℕ) : c + k * L * w + x + k * j ≡ c + x [MOD k] := by
  change _ % k = _ % k
  rw [show c + k * L * w + x + k * j = c + x + k * (L * w + j) by ring, Nat.add_mul_mod_self_left]

private lemma modEq_class (L c w x : ℕ) : c + k * L * w + x ≡ c + x [MOD k] := by
  have h := modEq_blockIdx (k := k) L c w 0 x
  rwa [Nat.mul_zero, Nat.add_zero] at h

omit [MeasurableSpace Ω] in
/-- **The pair process is readable off the class's own past.**  Everything the pair character at
step `u` of residue class `c` reads is outside every block that class consumes from step `u` on:
an a-side index of a later block is strictly larger, and a b-side index lies in the wrong residue
class altogether. -/
private lemma measurable_pairObs_pastSet {a b L : ℕ} (hk : 1 ≤ k) (hab : ¬ a ≡ b [MOD k])
    (c u : ℕ) :
    Measurable[ParityWalk.noiseAlg ξ
        (ParityWalk.pastSet (fun v => pairBlock k a b L (c + k * L * v)) u)]
      (fun ω => pairObs k a b (fun i => ξ i ω) (c + k * L * u)) := by
  have hside : ∀ x : ℕ, x = a ∨ x = b →
      ∀ i, i % k = (c + k * L * u + x) % k → i ≤ c + k * L * u + x →
        i ∈ ParityWalk.pastSet (fun v => pairBlock k a b L (c + k * L * v)) u := by
    intro x hx i hmod hle v hv hmem
    obtain ⟨j, -, hi⟩ := hmem
    have hmono : k * L * u ≤ k * L * v := Nat.mul_le_mul_left _ hv
    have hkj : k ≤ k * (j + 1) := Nat.le_mul_of_pos_right k (by omega)
    have hx' : (c + k * L * u + x) % k = (c + x) % k := modEq_class L c u x
    have hclass : ∀ y : ℕ, i = c + k * L * v + y + k * (j + 1) → (c + x) % k = (c + y) % k := by
      intro y hiy
      have h1 : i % k = (c + y) % k := by rw [hiy]; exact modEq_blockIdx L c v (j + 1) y
      rw [hmod, hx'] at h1
      exact h1
    rcases hi with hi | hi
    · rcases hx with rfl | rfl
      · omega
      · exact hab (Nat.ModEq.add_left_cancel' c (hclass a hi).symm)
    · rcases hx with rfl | rfl
      · exact hab (Nat.ModEq.add_left_cancel' c (hclass b hi))
      · omega
  exact measurable_pairObs_noiseAlg hk _ (hside a (Or.inl rfl)) (hside b (Or.inr rfl))

/-! ### The multiplier's mean: the two sign flips cancel -/

/-- **The persistence.**  The pair multiplier over `L` chain steps has mean `m^{2L}` — an *even*
power of the noise character's mean, hence nonnegative.  This is the cancellation in the form the
tail consumes: a single coordinate's multiplier has mean `m ≤ 0` and its Birkhoff sums cancel; a
cross-class pair's has mean `m² ≥ 0` and they accumulate. -/
private lemma integral_pairMult {a b : ℕ} (hk : 1 ≤ k) (hmeas : ∀ i, Measurable (ξ i))
    (hindep : iIndepFun ξ P) (hab : ¬ a ≡ b [MOD k])
    (hmean : ∀ i, k ≤ i → ∫ ω, ParityWalk.zeta (ξ i ω) ∂P = m) (t L : ℕ) :
    ∫ ω, pairMult k a b L (fun i => ξ i ω) t ∂P = m ^ (2 * L) := by
  induction L with
  | zero => simp [pairMult]
  | succ L ih =>
    set p := t + a + k * (L + 1) with hp
    set q := t + b + k * (L + 1) with hq
    have hpq : p ≠ q := pairIdx_ne hab (Nat.ModEq.refl t) (L + 1) (L + 1)
    have hpk : k ≤ p := by
      have : k ≤ k * (L + 1) := Nat.le_mul_of_pos_right k (by omega)
      omega
    have hqk : k ≤ q := by
      have : k ≤ k * (L + 1) := Nat.le_mul_of_pos_right k (by omega)
      omega
    have hsplit : ∀ ω, pairMult k a b (L + 1) (fun i => ξ i ω) t
        = pairMult k a b L (fun i => ξ i ω) t
          * (ParityWalk.zeta (ξ p ω) * ParityWalk.zeta (ξ q ω)) := by
      intro ω; rw [hp, hq, pairMult, Finset.prod_range_succ]; rfl
    -- the earlier blocks avoid the two fresh indices
    have hF : Measurable[ParityWalk.noiseAlg ξ (({p, q} : Set ℕ)ᶜ)]
        (fun ω => pairMult k a b L (fun i => ξ i ω) t) := by
      refine (measurable_pairMult t).mono (ParityWalk.noiseAlg_mono ξ ?_) le_rfl
      rintro i ⟨j, hj, hi⟩
      have hjL : k * (j + 1) ≠ k * (L + 1) := fun h => by
        have := Nat.eq_of_mul_eq_mul_left (by omega : 0 < k) h; omega
      simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      rcases hi with hi | hi <;> subst hi <;> refine ⟨fun h => ?_, fun h => ?_⟩
      · exact hjL (by omega)
      · exact pairIdx_ne hab (Nat.ModEq.refl t) (j + 1) (L + 1) h
      · exact pairIdx_ne hab (Nat.ModEq.refl t) (L + 1) (j + 1) h.symm
      · exact hjL (by omega)
    have hG : Measurable[ParityWalk.noiseAlg ξ ((({p, q} : Set ℕ)ᶜ)ᶜ)]
        (fun ω => ParityWalk.zeta (ξ p ω) * ParityWalk.zeta (ξ q ω)) := by
      rw [compl_compl]
      exact (ParityWalk.measurable_zeta.comp
          (ParityWalk.measurable_noiseAlg_xi (by simp))).mul
        (ParityWalk.measurable_zeta.comp (ParityWalk.measurable_noiseAlg_xi (by simp)))
    have hind := ParityWalk.indepFun_noiseAlg_compl hmeas hindep _ hF hG
    have hFm : AEStronglyMeasurable (fun ω => pairMult k a b L (fun i => ξ i ω) t) P :=
      ((measurable_pairMult t).mono (ParityWalk.noiseAlg_le hmeas _) le_rfl).aestronglyMeasurable
    have hGm : AEStronglyMeasurable
        (fun ω => ParityWalk.zeta (ξ p ω) * ParityWalk.zeta (ξ q ω)) P :=
      ((ParityWalk.measurable_zeta.comp (hmeas p)).mul
        (ParityWalk.measurable_zeta.comp (hmeas q))).aestronglyMeasurable
    have hfresh : ∫ ω, ParityWalk.zeta (ξ p ω) * ParityWalk.zeta (ξ q ω) ∂P = m * m := by
      have hipq : IndepFun (fun ω => ParityWalk.zeta (ξ p ω))
          (fun ω => ParityWalk.zeta (ξ q ω)) P :=
        (hindep.indepFun hpq).comp ParityWalk.measurable_zeta ParityWalk.measurable_zeta
      rw [hipq.integral_fun_mul_eq_mul_integral
          (ParityWalk.measurable_zeta.comp (hmeas p)).aestronglyMeasurable
          (ParityWalk.measurable_zeta.comp (hmeas q)).aestronglyMeasurable,
        hmean p hpk, hmean q hqk]
    rw [integral_congr_ae (Filter.Eventually.of_forall hsplit),
      hind.integral_fun_mul_eq_mul_integral hFm hGm, ih, hfresh,
      show 2 * (L + 1) = 2 * L + 1 + 1 by ring, pow_succ, pow_succ]
    ring

/-! ### The Walsh split of a two-offset observable

A `[−1, 1]`-valued function of two bits is its flat mean plus three characters: the two coordinate
characters, and the *pair* character.  The first two are covered by the coordinate machinery at the
noise-rate-free constant; only the third needs the persistent tail. -/

private noncomputable def pairCoefA (ψ : Bool → Bool → ℝ) : ℝ :=
  (ψ false false + ψ false true - ψ true false - ψ true true) / 4

private noncomputable def pairCoefB (ψ : Bool → Bool → ℝ) : ℝ :=
  (ψ false false - ψ false true + ψ true false - ψ true true) / 4

/-- The **pair Walsh coefficient** of a two-offset observable: the amplitude of its genuinely
two-coordinate part, i.e. the coefficient of `χ(u)·χ(v)` in the Walsh expansion of `ψ`.

It is the one of the three coefficients that is public, because `samePairMean` — the stationary
answer to a *same-class* query — is stated in terms of it.  Its two single-coordinate siblings are
consumed only inside this file and stay private. -/
noncomputable def pairCoefAB (ψ : Bool → Bool → ℝ) : ℝ :=
  (ψ false false - ψ false true - ψ true false + ψ true true) / 4

private lemma pair_decomp (ψ : Bool → Bool → ℝ) (u v : Bool) :
    ψ u v = pairMean ψ + pairCoefA ψ * ParityWalk.chi u + pairCoefB ψ * ParityWalk.chi v
      + pairCoefAB ψ * ParityWalk.chi (xor u v) := by
  cases u <;> cases v <;>
    norm_num [pairMean, pairCoefA, pairCoefB, pairCoefAB, ParityWalk.chi] <;> ring

private lemma abs_pairCoef_le_one {ψ : Bool → Bool → ℝ} (hψ : ∀ u v, |ψ u v| ≤ 1) :
    |pairMean ψ| ≤ 1 ∧ |pairCoefA ψ| ≤ 1 ∧ |pairCoefB ψ| ≤ 1 ∧ |pairCoefAB ψ| ≤ 1 := by
  obtain ⟨h1, h1'⟩ := abs_le.mp (hψ false false)
  obtain ⟨h2, h2'⟩ := abs_le.mp (hψ false true)
  obtain ⟨h3, h3'⟩ := abs_le.mp (hψ true false)
  obtain ⟨h4, h4'⟩ := abs_le.mp (hψ true true)
  refine ⟨abs_le.mpr ⟨?_, ?_⟩, abs_le.mpr ⟨?_, ?_⟩, abs_le.mpr ⟨?_, ?_⟩, abs_le.mpr ⟨?_, ?_⟩⟩ <;>
    simp only [pairMean, pairCoefA, pairCoefB, pairCoefAB] <;> linarith

/-- **The query's deviation, split into three character sums.** -/
private lemma empiricalMean_sub_pairMean (ψ : Bool → Bool → ℝ) (a b : ℕ) {n : ℕ} (hn : 1 ≤ n)
    (o : ℕ → Bool) :
    (n : ℝ) * (SQOracle.empiricalMean (pairEnsemble ψ a b) n o - pairMean ψ)
      = pairCoefA ψ * (∑ t ∈ Finset.range n, ParityWalk.chi (o (t + a)))
        + pairCoefB ψ * (∑ t ∈ Finset.range n, ParityWalk.chi (o (t + b)))
        + pairCoefAB ψ
            * (∑ t ∈ Finset.range n, ParityWalk.chi (xor (o (t + a)) (o (t + b)))) := by
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hterm : ∀ t, pairEnsemble ψ a b t o
      = pairMean ψ + pairCoefA ψ * ParityWalk.chi (o (t + a))
        + pairCoefB ψ * ParityWalk.chi (o (t + b))
        + pairCoefAB ψ * ParityWalk.chi (xor (o (t + a)) (o (t + b))) :=
    fun t => pair_decomp ψ _ _
  rw [SQOracle.empiricalMean, Finset.sum_congr rfl fun t _ => hterm t]
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
    ← Finset.mul_sum]
  field_simp
  ring

/-- Extending a Birkhoff block of characters past its end costs at most the number of extra
terms. -/
private lemma abs_chiSum_extend (g : ℕ → Bool) (n₀ r : ℕ) :
    |∑ t ∈ Finset.range (n₀ + r), ParityWalk.chi (g t)|
      ≤ |∑ t ∈ Finset.range n₀, ParityWalk.chi (g t)| + r := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [show n₀ + (r + 1) = n₀ + r + 1 by omega, Finset.sum_range_succ]
    have htri := abs_add_le (∑ t ∈ Finset.range (n₀ + r), ParityWalk.chi (g t))
      (ParityWalk.chi (g (n₀ + r)))
    have habs : |ParityWalk.chi (g (n₀ + r))| = 1 := by
      cases g (n₀ + r) <;> norm_num [ParityWalk.chi]
    push_cast
    linarith

/-- Absorbing a union bound's factor into the exponent: a probability dominated by `6·exp(−x)` is
dominated by `2·exp(−x/3)`, which is the shape `MixingHoeffding` demands. -/
private lemma bound_absorb {p x : ℝ} (hp1 : p ≤ 1) (h : p ≤ 6 * Real.exp (-x)) :
    p ≤ 2 * Real.exp (-x / 3) := by
  have hlog2 : (0.69 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  by_cases hcase : x ≤ 3 * Real.log 2
  · have h1 : Real.exp (-Real.log 2) ≤ Real.exp (-x / 3) :=
      Real.exp_le_exp.mpr (by linarith)
    have h2 : Real.exp (-Real.log 2) = 1 / 2 := by
      rw [Real.exp_neg, Real.exp_log (by norm_num)]; norm_num
    rw [h2] at h1
    linarith
  · replace hcase : 3 * Real.log 2 < x := not_le.mp hcase
    have hsplit : Real.exp (-x) = Real.exp (-x / 3) * Real.exp (-(2 * x) / 3) := by
      rw [← Real.exp_add]; congr 1; ring
    have hbig : (3 : ℝ) ≤ Real.exp (2 * x / 3) := by
      have h4 : Real.exp (Real.log 4) ≤ Real.exp (2 * x / 3) := by
        refine Real.exp_le_exp.mpr ?_
        have : Real.log 4 = 2 * Real.log 2 := by
          rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
        rw [this]; linarith
      rw [Real.exp_log (by norm_num)] at h4
      linarith
    have hpos : (0 : ℝ) < Real.exp (2 * x / 3) := Real.exp_pos _
    have hinv : Real.exp (-(2 * x) / 3) ≤ 1 / 3 := by
      rw [show -(2 * x) / 3 = -(2 * x / 3) by ring, Real.exp_neg, inv_eq_one_div,
        div_le_div_iff₀ hpos (by norm_num)]
      linarith
    have hexp3 : (0 : ℝ) ≤ Real.exp (-x / 3) := (Real.exp_nonneg _)
    calc p ≤ 6 * Real.exp (-x) := h
      _ = 6 * (Real.exp (-x / 3) * Real.exp (-(2 * x) / 3)) := by rw [hsplit]
      _ ≤ 6 * (Real.exp (-x / 3) * (1 / 3)) := by
          have := mul_le_mul_of_nonneg_left hinv hexp3
          linarith
      _ = 2 * Real.exp (-x / 3) := by ring

/-! ### The blocking length, and the constant -/

/-- The **blocking length**: the number of chain steps over which a cross-class pair character's
persistence `(1−2η)²` decays below `1/2`.  It is `Θ(1/η)`, and it is the only place the noise rate
enters the constant. -/
noncomputable def pairBlockLen (η : ℝ) : ℕ := ⌈(4 * η)⁻¹⌉₊

/-- **The two-offset mixing constant**: linear in the window length and in the blocking length,
hence in the inverse noise rate (`pairConst_le`). -/
noncomputable def pairConst (k : ℕ) (η : ℝ) : ℝ := 432 * (k * pairBlockLen η)

private lemma pairBlockLen_pos {η : ℝ} (hη : 0 < η) : 0 < pairBlockLen η :=
  Nat.one_le_ceil_iff.mpr (by positivity)

/-- **The constant is `O(k/η)`.**  This is the `η ↔ c` trade-off [SQ] §3.1's budget `2η ≤ τ` prices,
made explicit: it is real for the two-offset class, where the coordinate case has none. -/
lemma pairConst_le (k : ℕ) {η : ℝ} (hη : 0 < η) : pairConst k η ≤ 108 * k / η + 432 * k := by
  have hceil : (pairBlockLen η : ℝ) ≤ (4 * η)⁻¹ + 1 :=
    le_of_lt (Nat.ceil_lt_add_one (by positivity))
  have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  have hstep : (432 : ℝ) * ((k : ℝ) * pairBlockLen η) ≤ 432 * ((k : ℝ) * ((4 * η)⁻¹ + 1)) := by
    have := mul_le_mul_of_nonneg_left hceil hk
    linarith
  refine hstep.trans (le_of_eq ?_)
  field_simp
  ring

/-- **The persistence decays below `1/2` over one block.** -/
private lemma pairPersistence_le_half {η : ℝ} (hη0 : 0 < η) (hη1 : η ≤ 1 / 2) :
    (2 * η - 1) ^ (2 * pairBlockLen η) ≤ 1 / 2 := by
  set L := pairBlockLen η with hL
  have hLge : (4 * η)⁻¹ ≤ (L : ℝ) := Nat.le_ceil _
  have hηL : (1 : ℝ) ≤ 4 * η * L := by
    have h4 : (0 : ℝ) < 4 * η := by linarith
    have hmul := mul_le_mul_of_nonneg_left hLge h4.le
    rwa [mul_inv_cancel₀ (ne_of_gt h4)] at hmul
  have hsq : (2 * η - 1) ^ 2 = (1 - 2 * η) ^ 2 := by ring
  have hbase : (0 : ℝ) ≤ 1 - 2 * η := by linarith
  have hexp : 1 - 2 * η ≤ Real.exp (-(2 * η)) := by
    have := Real.add_one_le_exp (-(2 * η))
    linarith
  have hstep : (2 * η - 1) ^ 2 ≤ Real.exp (-(2 * η)) ^ 2 := by
    rw [hsq]; exact pow_le_pow_left₀ hbase hexp 2
  have hpow : ((2 * η - 1) ^ 2) ^ L ≤ (Real.exp (-(2 * η)) ^ 2) ^ L :=
    pow_le_pow_left₀ (by positivity) hstep L
  have hcollapse : (Real.exp (-(2 * η)) ^ 2) ^ L = Real.exp (-(4 * η * L)) := by
    rw [← pow_mul, ← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hone : Real.exp (-(4 * η * L)) ≤ Real.exp (-1) := Real.exp_le_exp.mpr (by linarith)
  have hhalf : Real.exp (-1 : ℝ) ≤ 1 / 2 := by
    rw [Real.exp_neg, inv_eq_one_div, div_le_div_iff₀ (Real.exp_pos 1) (by norm_num)]
    linarith [Real.exp_one_gt_d9]
  calc (2 * η - 1) ^ (2 * L) = ((2 * η - 1) ^ 2) ^ L := by rw [pow_mul]
    _ ≤ (Real.exp (-(2 * η)) ^ 2) ^ L := hpow
    _ = Real.exp (-(4 * η * L)) := hcollapse
    _ ≤ Real.exp (-1) := hone
    _ ≤ 1 / 2 := hhalf

/-! ### The two character tails, at a common horizon -/

/-- A three-way union bound, in the real-valued form the tails come in. -/
private lemma measureReal_union3_le {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (E₁ E₂ E₃ : Set Ω) (d : ℝ) (h1 : P.real E₁ ≤ d) (h2 : P.real E₂ ≤ d) (h3 : P.real E₃ ≤ d) :
    P.real (E₁ ∪ E₂ ∪ E₃) ≤ 3 * d := by
  refine le_trans (measureReal_union_le _ _) ?_
  have h12 := measureReal_union_le (μ := P) E₁ E₂
  linarith


/-- A **coordinate** character's Birkhoff sum over the window `[off, off + n)`.  The boundary
allowance is `2k`, *not* `2(off + k)`: the telescope runs inside the window, so a query's own
offset never enters its constant. -/
private lemma coordChar_tail (hk : 1 ≤ k) (hmeas : ∀ i, Measurable (ξ i))
    (hindep : iIndepFun ξ P)
    (hmean : ∀ i, k ≤ i → ∫ ω, ParityWalk.zeta (ξ i ω) ∂P = m) (hm0 : -1 ≤ m) (hm : m ≤ 0)
    (off : ℕ) {n : ℕ} (hkn : k ≤ n) {x : ℝ} (hx : 0 ≤ x) :
    P.real {ω | x + 2 * (k : ℝ) ≤
        |∑ t ∈ Finset.range n, ParityWalk.chi (obs k (fun i => ξ i ω) (t + off))|}
      ≤ 2 * Real.exp (-x ^ 2 / (2 * ((n - k : ℕ) : ℝ))) := by
  have hNk : n - k + k = n := Nat.sub_add_cancel hkn
  have h := ParityWalk.chiSum_tail_gen (P := P) (ξ := ξ) (m := m) (d := off + k) (K := k)
    hmeas hindep (fun u => hmean _ (by omega)) hm0 hm
    (fun u ω => obs k (fun i => ξ i ω) (u + off))
    (fun u => by
      have hm := measurable_obs (ξ := ξ) hk (u + off)
      rwa [show u + (off + k) = u + off + k by omega])
    (fun u ω => by
      have hr := chi_obs_add (k := k) (by omega) (fun i => ξ i ω) (u + off)
      rw [show u + (off + k) = u + off + k by omega, show u + k + off = u + off + k by omega]
      exact hr)
    (n - k) hx
  rwa [hNk] at h

/-- The **pair** character's Birkhoff sum over `[0, n)`, at the blocking lag `k·L`.  The horizon is
rounded down to a whole number of blocks, at a cost of at most one more block. -/
private lemma pairChar_tail (hk : 1 ≤ k) (hmeas : ∀ i, Measurable (ξ i)) (hindep : iIndepFun ξ P)
    {a b L : ℕ} (hLpos : 0 < L) (hab : ¬ a ≡ b [MOD k]) {η : ℝ}
    (hmean : ∀ i, k ≤ i → ∫ ω, ParityWalk.zeta (ξ i ω) ∂P = 2 * η - 1)
    (hρ0 : (0 : ℝ) ≤ (2 * η - 1) ^ (2 * L)) (hρhalf : (2 * η - 1) ^ (2 * L) ≤ 1 / 2)
    {n : ℕ} (hnK : 2 * (k * L) ≤ n) {x : ℝ} (hx : 0 ≤ x) :
    P.real {ω | x + 5 * ((k * L : ℕ) : ℝ) ≤
        |∑ t ∈ Finset.range n, ParityWalk.chi (pairObs k a b (fun i => ξ i ω) t)|}
      ≤ 2 * Real.exp (-x ^ 2 / (2 * (4 * ((k * L : ℕ) : ℝ) * n))) := by
  have hKpos : 0 < k * L := Nat.mul_pos hk hLpos
  -- round the horizon down to a whole number of blocks
  have hdiv2 : 2 ≤ n / (k * L) := (Nat.le_div_iff_mul_le hKpos).mpr (by linarith [hnK])
  obtain ⟨M, hM⟩ : ∃ M, n / (k * L) = M + 1 := ⟨n / (k * L) - 1, by omega⟩
  have hMpos : 1 ≤ M := by omega
  have hMK : k * L * M + k * L = k * L * (n / (k * L)) := by rw [hM]; ring
  have hKMn : k * L * M + k * L ≤ n := by
    rw [hMK, Nat.mul_comm]; exact Nat.div_mul_le_self n (k * L)
  have hrem : n - (k * L * M + k * L) ≤ k * L := by
    have hmod := Nat.mod_add_div n (k * L)
    have hlt : n % (k * L) < k * L := Nat.mod_lt _ hKpos
    rw [hMK]
    omega
  obtain ⟨r, hr⟩ := Nat.exists_eq_add_of_le hKMn
  have hrK : (r : ℝ) ≤ ((k * L : ℕ) : ℝ) := by
    have : r ≤ k * L := by omega
    exact_mod_cast this
  -- the tail at the whole-block horizon
  have htail := PersistentWalk.persistentSum_tail (P := P) hmeas hindep hKpos hρ0 hρhalf
    (fun t ω => pairObs k a b (fun i => ξ i ω) t)
    (fun t ω => pairMult k a b L (fun i => ξ i ω) t) (pairBlock k a b L)
    (fun c u v huv => pairBlock_disjoint (by omega) hLpos hab c u v huv)
    (fun t => measurable_pairMult t) (fun t ω => pairMult_mem_Icc k a b L _ t)
    (fun t => integral_pairMult hk hmeas hindep hab hmean t L)
    (fun c u => measurable_pairObs_pastSet hk hab c u)
    (fun t ω => chi_pairObs_add_mul (by omega) a b L (fun i => ξ i ω) t) M
    (by positivity : (0 : ℝ) ≤ x / 2)
  refine le_trans (measureReal_mono ?_ (measure_ne_top _ _)) (le_trans htail ?_)
  · -- the extra terms past the last whole block cost at most one block
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω ⊢
    have hext := abs_chiSum_extend (fun t => pairObs k a b (fun i => ξ i ω) t)
      (k * L * M + k * L) r
    rw [← hr] at hext
    linarith
  · -- compare the exponents
    have hKR : (1 : ℝ) ≤ ((k * L : ℕ) : ℝ) := by exact_mod_cast hKpos
    have hnR : (0 : ℝ) < (n : ℝ) := by
      have : 0 < n := by omega
      exact_mod_cast this
    have hKMR : ((k * L : ℕ) : ℝ) * M ≤ (n : ℝ) := by
      have : k * L * M ≤ n := by omega
      exact_mod_cast this
    have hMR : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hMpos
    have hden : (0 : ℝ) < 2 * (((k * L : ℕ) : ℝ) ^ 2 * M) := by positivity
    have hden' : (0 : ℝ) < 2 * (4 * ((k * L : ℕ) : ℝ) * n) := by positivity
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by norm_num)
    rw [neg_div, neg_div, neg_le_neg_iff, div_le_div_iff₀ hden' hden]
    nlinarith [mul_nonneg (mul_nonneg (sq_nonneg x) (by linarith : (0:ℝ) ≤ ((k * L : ℕ) : ℝ)))
      (by linarith : (0:ℝ) ≤ (n : ℝ) - ((k * L : ℕ) : ℝ) * M)]

/-! ### The capstone -/

/-- **E1 for the two-offset query class.**  The noisy window chain of window length `k ≥ 1` at noise
rate `η > 0` satisfies the FJS-shaped single-orbit Hoeffding hypothesis at the explicit constant
`pairConst k η = O(k/η)`, for **every** query that reads two observations at fixed offsets in
*distinct* residue classes, with a `[−1, 1]`-valued observable.

This is the query class a learner of single-literal decision lists schedules ([SQ] §3.1): each of
its queries correlates one window literal with the label.  Where
`mixingHoeffding_noisyWindowChain` covers a query reading one observation at a constant free of the
noise rate, this covers a query reading two — and its constant must carry the noise rate, because
`not_mixingHoeffding_noisyWindowChain_pair_frozen` refutes the predicate at `η = 0` for every
positive constant.  So the `η ↔ c` trade-off that [SQ] §3.1's budget `2η ≤ τ` prices is real here,
and `pairConst_le` prices it: `c ≤ 108·k/η + 432·k`.

The hypothesis `0 < η` is therefore load-bearing and is kept honest rather than absorbed into a
junk value of the constant.

Three ingredients meet.  The observable splits into its flat mean and three characters, of which
the two coordinate characters are handled at the noise-rate-free constant and only the pair
character needs the gap.  The pair character is a *persistent* two-state walk — the two
coordinates' sign flips cancel, `integral_pairMult` — read at the blocking lag `k·L` that brings
its persistence below `1/2`.  And the `k·L` residue classes of the time axis, whose noise blocks
overlap across classes, are combined without any independence between them
(`PersistentWalk.hasSubgaussianMGF_sum_range`). -/
theorem mixingHoeffding_noisyWindowChain_pair
    (hk : 1 ≤ k) (hmeas : ∀ i, Measurable (ξ i)) (hindep : iIndepFun ξ P)
    {η : ℝ} (hη0 : 0 < η) (hη1 : η ≤ 1 / 2)
    (hmean : ∀ u, ∫ ω, ParityWalk.zeta (ξ (u + k) ω) ∂P = 2 * η - 1)
    {a b : ℕ} (hab : ¬ a ≡ b [MOD k])
    (ψ : Bool → Bool → ℝ) (hψ : ∀ u v, |ψ u v| ≤ 1) :
    BirkhoffTool.MixingHoeffding (Measure.map (traj k ξ) P) (pairEnsemble ψ a b) (pairMean ψ)
      (pairConst k η) := by
  classical
  obtain ⟨L, hLdef⟩ : ∃ L, pairBlockLen η = L := ⟨_, rfl⟩
  have hLpos : 0 < L := hLdef ▸ pairBlockLen_pos hη0
  have hKpos : 0 < k * L := Nat.mul_pos hk hLpos
  have hKR : (1 : ℝ) ≤ ((k * L : ℕ) : ℝ) := by exact_mod_cast hKpos
  have hkKR : (k : ℝ) ≤ ((k * L : ℕ) : ℝ) := by
    have : k ≤ k * L := Nat.le_mul_of_pos_right k hLpos
    exact_mod_cast this
  have hconst : pairConst k η = 432 * ((k * L : ℕ) : ℝ) := by
    rw [pairConst, hLdef]; push_cast; ring
  have htraj : Measurable (traj k ξ) := measurable_traj hk hmeas
  have hmean' : ∀ i, k ≤ i → ∫ ω, ParityWalk.zeta (ξ i ω) ∂P = 2 * η - 1 := by
    intro i hi
    have h := hmean (i - k)
    rwa [Nat.sub_add_cancel hi] at h
  have hρ0 : (0 : ℝ) ≤ (2 * η - 1) ^ (2 * L) := by rw [pow_mul]; positivity
  have hρhalf : (2 * η - 1) ^ (2 * L) ≤ 1 / 2 := hLdef ▸ pairPersistence_le_half hη0 hη1
  obtain ⟨hmeanabs, hcA, hcB, hcAB⟩ := abs_pairCoef_le_one hψ
  intro n τ hn hτ
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  set A : Set (ℕ → Bool) :=
    {o | τ ≤ |SQOracle.empiricalMean (pairEnsemble ψ a b) n o - pairMean ψ|} with hA
  have hAmeas : MeasurableSet A :=
    measurableSet_le measurable_const
      (((measurable_empiricalMean_pair ψ a b n).sub_const _).abs)
  have hmap : (Measure.map (traj k ξ) P).real A = P.real (traj k ξ ⁻¹' A) := by
    simp only [Measure.real, Measure.map_apply htraj hAmeas]
  rw [hmap]
  -- the empirical answer never leaves `[−1, 1]`
  have hempabs : ∀ o : ℕ → Bool, |SQOracle.empiricalMean (pairEnsemble ψ a b) n o| ≤ 1 := by
    intro o
    have hsum : |∑ t ∈ Finset.range n, pairEnsemble ψ a b t o| ≤ (n : ℝ) := by
      calc |∑ t ∈ Finset.range n, pairEnsemble ψ a b t o|
          ≤ ∑ t ∈ Finset.range n, |pairEnsemble ψ a b t o| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _t ∈ Finset.range n, (1 : ℝ) := Finset.sum_le_sum fun t _ => hψ _ _
        _ = (n : ℝ) := by simp
    rw [SQOracle.empiricalMean, abs_mul, abs_inv, abs_of_nonneg hn0.le]
    calc (n : ℝ)⁻¹ * |∑ t ∈ Finset.range n, pairEnsemble ψ a b t o|
        ≤ (n : ℝ)⁻¹ * (n : ℝ) := mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = 1 := inv_mul_cancel₀ (ne_of_gt hn0)
  by_cases hτ2 : 2 < τ
  · -- beyond the observable's own range the event is empty
    have hempty : traj k ξ ⁻¹' A = ∅ := by
      ext ω
      simp only [hA, Set.mem_preimage, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false,
        not_le]
      obtain ⟨h1, h2⟩ := abs_le.mp (hempabs (traj k ξ ω))
      obtain ⟨h3, h4⟩ := abs_le.mp hmeanabs
      exact abs_lt.mpr ⟨by linarith, by linarith⟩
    rw [hempty, measureReal_empty]
    positivity
  replace hτ2 : τ ≤ 2 := not_lt.mp hτ2
  by_cases hsmall : (n : ℝ) * τ < 30 * ((k * L : ℕ) : ℝ)
  · -- the bound is not yet binding
    have hb2 : (n : ℝ) * τ ^ 2 ≤ 60 * ((k * L : ℕ) : ℝ) := by nlinarith
    have hlog : (0.69 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
    have hkey : (n : ℝ) * τ ^ 2 / (2 * pairConst k η) ≤ Real.log 2 := by
      rw [hconst, div_le_iff₀ (by linarith)]
      nlinarith
    have h1 : Real.exp (-Real.log 2) ≤ Real.exp (-((n : ℝ) * τ ^ 2 / (2 * pairConst k η))) :=
      Real.exp_le_exp.mpr (by linarith)
    have h2 : Real.exp (-Real.log 2) = 1 / 2 := by
      rw [Real.exp_neg, Real.exp_log (by norm_num)]; norm_num
    rw [h2] at h1
    rw [show -(n : ℝ) * τ ^ 2 / (2 * pairConst k η)
        = -((n : ℝ) * τ ^ 2 / (2 * pairConst k η)) by ring]
    exact le_trans MeasureTheory.measureReal_le_one (by linarith)
  · -- the three character tails
    replace hsmall : 30 * ((k * L : ℕ) : ℝ) ≤ (n : ℝ) * τ := not_lt.mp hsmall
    have hτ0 : 0 < τ := by nlinarith
    have hnbig : 15 * ((k * L : ℕ) : ℝ) ≤ (n : ℝ) := by nlinarith
    have hnK : 2 * (k * L) ≤ n := by
      have : (2 : ℝ) * ((k * L : ℕ) : ℝ) ≤ (n : ℝ) := by linarith
      exact_mod_cast this
    have hkL : k ≤ k * L := Nat.le_mul_of_pos_right k hLpos
    have hkn : k ≤ n := by omega
    have hnkpos : (0 : ℝ) < ((n - k : ℕ) : ℝ) := by
      have : 0 < n - k := by omega
      exact_mod_cast this
    have hnkle : ((n - k : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.sub_le n k
    -- the two thresholds, and their slack
    have hx1nn : (0 : ℝ) ≤ (n : ℝ) * τ / 3 - 2 * (k : ℝ) := by nlinarith
    have hx3nn : (0 : ℝ) ≤ (n : ℝ) * τ / 3 - 5 * ((k * L : ℕ) : ℝ) := by nlinarith
    have hx1big : (n : ℝ) * τ / 4 ≤ (n : ℝ) * τ / 3 - 2 * (k : ℝ) := by nlinarith
    have hx3big : (n : ℝ) * τ / 6 ≤ (n : ℝ) * τ / 3 - 5 * ((k * L : ℕ) : ℝ) := by nlinarith
    -- a coordinate character's tail, at either offset
    have hcoordE : ∀ off : ℕ, P.real {ω | (n : ℝ) * τ / 3 ≤
        |∑ t ∈ Finset.range n, ParityWalk.chi (obs k (fun i => ξ i ω) (t + off))|}
        ≤ 2 * Real.exp (-((n : ℝ) * τ ^ 2 / (288 * ((k * L : ℕ) : ℝ)))) := by
      intro off
      have h := coordChar_tail hk hmeas hindep hmean' (by linarith) (by linarith) off hkn hx1nn
      have hset : {ω | (n : ℝ) * τ / 3 ≤
          |∑ t ∈ Finset.range n, ParityWalk.chi (obs k (fun i => ξ i ω) (t + off))|}
          = {ω | ((n : ℝ) * τ / 3 - 2 * (k : ℝ)) + 2 * (k : ℝ) ≤
            |∑ t ∈ Finset.range n, ParityWalk.chi (obs k (fun i => ξ i ω) (t + off))|} := by
        ext ω; simp only [Set.mem_setOf_eq]; constructor <;> intro hh <;> linarith
      rw [hset]
      refine h.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by norm_num))
      rw [neg_div, neg_le_neg_iff, div_le_div_iff₀ (by positivity) (by positivity)]
      have hsq : ((n : ℝ) * τ / 4) ^ 2 ≤ ((n : ℝ) * τ / 3 - 2 * (k : ℝ)) ^ 2 :=
        pow_le_pow_left₀ (by positivity) hx1big 2
      have hnn : (0 : ℝ) ≤ (n : ℝ) * τ ^ 2 := by positivity
      have hsq2 : (0 : ℝ) ≤ ((n : ℝ) * τ / 3 - 2 * (k : ℝ)) ^ 2 := sq_nonneg _
      calc (n : ℝ) * τ ^ 2 * (2 * ((n - k : ℕ) : ℝ))
          ≤ (n : ℝ) * τ ^ 2 * (2 * (n : ℝ)) :=
            mul_le_mul_of_nonneg_left (by linarith) hnn
        _ = 2 * ((n : ℝ) ^ 2 * τ ^ 2) := by ring
        _ ≤ 18 * ((n : ℝ) ^ 2 * τ ^ 2) := by
            have : (0 : ℝ) ≤ (n : ℝ) ^ 2 * τ ^ 2 := by positivity
            linarith
        _ = 288 * ((n : ℝ) * τ / 4) ^ 2 := by ring
        _ ≤ 288 * ((n : ℝ) * τ / 3 - 2 * (k : ℝ)) ^ 2 := by linarith
        _ ≤ ((n : ℝ) * τ / 3 - 2 * (k : ℝ)) ^ 2 * (288 * ((k * L : ℕ) : ℝ)) := by
            have hstep := mul_le_mul_of_nonneg_left
              (show (288 : ℝ) ≤ 288 * ((k * L : ℕ) : ℝ) by linarith) hsq2
            linarith
    -- the pair character's tail
    have hpairE : P.real {ω | (n : ℝ) * τ / 3 ≤
        |∑ t ∈ Finset.range n, ParityWalk.chi (pairObs k a b (fun i => ξ i ω) t)|}
        ≤ 2 * Real.exp (-((n : ℝ) * τ ^ 2 / (288 * ((k * L : ℕ) : ℝ)))) := by
      have h := pairChar_tail hk hmeas hindep hLpos hab hmean' hρ0 hρhalf hnK hx3nn
      have hset : {ω | (n : ℝ) * τ / 3 ≤
          |∑ t ∈ Finset.range n, ParityWalk.chi (pairObs k a b (fun i => ξ i ω) t)|}
          = {ω | ((n : ℝ) * τ / 3 - 5 * ((k * L : ℕ) : ℝ)) + 5 * ((k * L : ℕ) : ℝ) ≤
            |∑ t ∈ Finset.range n, ParityWalk.chi (pairObs k a b (fun i => ξ i ω) t)|} := by
        ext ω; simp only [Set.mem_setOf_eq]; constructor <;> intro hh <;> linarith
      rw [hset]
      refine h.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by norm_num))
      rw [neg_div, neg_le_neg_iff, div_le_div_iff₀ (by positivity) (by positivity)]
      have hsq : ((n : ℝ) * τ / 6) ^ 2
          ≤ ((n : ℝ) * τ / 3 - 5 * ((k * L : ℕ) : ℝ)) ^ 2 :=
        pow_le_pow_left₀ (by positivity) hx3big 2
      calc (n : ℝ) * τ ^ 2 * (2 * (4 * ((k * L : ℕ) : ℝ) * (n : ℝ)))
          = 288 * ((n : ℝ) * τ / 6) ^ 2 * ((k * L : ℕ) : ℝ) := by ring
        _ ≤ 288 * ((n : ℝ) * τ / 3 - 5 * ((k * L : ℕ) : ℝ)) ^ 2 * ((k * L : ℕ) : ℝ) := by
            have hstep := mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hsq (by norm_num : (0 : ℝ) ≤ 288))
              (show (0 : ℝ) ≤ ((k * L : ℕ) : ℝ) by linarith)
            linarith
        _ = ((n : ℝ) * τ / 3 - 5 * ((k * L : ℕ) : ℝ)) ^ 2 * (288 * ((k * L : ℕ) : ℝ)) := by ring
    -- the deviation forces one of the three characters to be large
    have hincl : traj k ξ ⁻¹' A ⊆
        ({ω | (n : ℝ) * τ / 3 ≤
            |∑ t ∈ Finset.range n, ParityWalk.chi (obs k (fun i => ξ i ω) (t + a))|}
          ∪ {ω | (n : ℝ) * τ / 3 ≤
            |∑ t ∈ Finset.range n, ParityWalk.chi (obs k (fun i => ξ i ω) (t + b))|})
          ∪ {ω | (n : ℝ) * τ / 3 ≤
            |∑ t ∈ Finset.range n, ParityWalk.chi (pairObs k a b (fun i => ξ i ω) t)|} := by
      intro ω hω
      simp only [hA, Set.mem_preimage, Set.mem_setOf_eq] at hω
      by_contra hcon
      simp only [Set.mem_union, not_or, Set.mem_setOf_eq, not_le] at hcon
      obtain ⟨⟨h1, h2⟩, h3⟩ := hcon
      have hid := empiricalMean_sub_pairMean ψ a b hn (traj k ξ ω)
      have htr : ∀ u, traj k ξ ω u = obs k (fun i => ξ i ω) u := fun _ => rfl
      have hxor : ∀ t, xor (obs k (fun i => ξ i ω) (t + a)) (obs k (fun i => ξ i ω) (t + b))
          = pairObs k a b (fun i => ξ i ω) t := fun _ => rfl
      simp only [htr, hxor] at hid
      have hbig : (n : ℝ) * τ ≤ |(n : ℝ)
          * (SQOracle.empiricalMean (pairEnsemble ψ a b) n (traj k ξ ω) - pairMean ψ)| := by
        rw [abs_mul, abs_of_nonneg hn0.le]
        exact mul_le_mul_of_nonneg_left hω hn0.le
      rw [hid] at hbig
      set Sa : ℝ := ∑ t ∈ Finset.range n, ParityWalk.chi (obs k (fun i => ξ i ω) (t + a))
      set Sb : ℝ := ∑ t ∈ Finset.range n, ParityWalk.chi (obs k (fun i => ξ i ω) (t + b))
      set Sq : ℝ := ∑ t ∈ Finset.range n, ParityWalk.chi (pairObs k a b (fun i => ξ i ω) t)
      have ea : |pairCoefA ψ * Sa| ≤ |Sa| := by
        rw [abs_mul]; exact mul_le_of_le_one_left (abs_nonneg Sa) hcA
      have eb : |pairCoefB ψ * Sb| ≤ |Sb| := by
        rw [abs_mul]; exact mul_le_of_le_one_left (abs_nonneg Sb) hcB
      have ec : |pairCoefAB ψ * Sq| ≤ |Sq| := by
        rw [abs_mul]; exact mul_le_of_le_one_left (abs_nonneg Sq) hcAB
      have htri1 := abs_add_le (pairCoefA ψ * Sa + pairCoefB ψ * Sb) (pairCoefAB ψ * Sq)
      have htri2 := abs_add_le (pairCoefA ψ * Sa) (pairCoefB ψ * Sb)
      linarith
    -- assemble
    have hsix : P.real (traj k ξ ⁻¹' A)
        ≤ 6 * Real.exp (-((n : ℝ) * τ ^ 2 / (288 * ((k * L : ℕ) : ℝ)))) := by
      refine le_trans (measureReal_mono hincl (measure_ne_top _ _)) ?_
      refine le_trans (measureReal_union3_le P _ _ _ _ (hcoordE a) (hcoordE b) hpairE)
        (le_of_eq (by ring))
    have harg : -((n : ℝ) * τ ^ 2 / (288 * ((k * L : ℕ) : ℝ))) / 3
        = -(n : ℝ) * τ ^ 2 / (2 * pairConst k η) := by
      rw [hconst]
      have hne : ((k * L : ℕ) : ℝ) ≠ 0 := by linarith
      field_simp
      ring
    have hfin := bound_absorb MeasureTheory.measureReal_le_one hsix
    rwa [harg] at hfin

/-! ### The same-class pair: the pair character IS the noise character

The scope note above records two-offset queries *inside one residue class* as not covered.  This
section covers the one same-class lag a learner of single-literal decision lists actually schedules
([SQ] §3.1): offsets `(a, a + k)` — the rule's own literal read against the label it predicts.

The mechanism is different from the cross-class one, and simpler.  At lag exactly `k` the chain's
own recursion makes the two observations xor to the complement of a single noise bit, so their pair
character *is* that bit's character (`chi_pairObs_lagK`): an i.i.d. sequence, with none of the walk
structure a cross-class pair has.  Nothing needs blocking and no gap is divided by, so the constant
stays free of the noise rate — as at coordinate observables, and for the same reason.

What moves instead is the **answer**.  An i.i.d. pair character has mean `m`, not `0`, so the
stationary answer is `samePairMean ψ m = pairMean ψ + pairCoefAB ψ · m` and not the flat
`pairMean ψ`.  The noise rate that left the constant reappears there, and
`not_mixingHoeffding_noisyWindowChain_samePair_flatMean` makes that displacement a theorem: at the
flat answer the predicate is refutable at every positive constant, on a trajectory law that
`mixingHoeffding_noisyWindowChain_pair_lagK` covers at the *correct* answer
(`mixingHoeffding_frozen_samePair_correctMean` — the perturbation test, sharp: the same
configuration satisfies the predicate at every constant once the answer is right). -/

/-- **The same-class pair character is the noise character.**  At lag exactly `k` the chain's
recursion `o_{u+k} = ¬o_u ⊕ ξ_{u+k}` makes the two observations xor to the complement of one noise
bit, so the pair character is that bit's character outright — the character of a single independent
coordinate, not of a walk. -/
theorem chi_pairObs_lagK {k : ℕ} (hk : 0 < k) (a : ℕ) (ξ : ℕ → Bool) (t : ℕ) :
    ParityWalk.chi (pairObs k a (a + k) ξ t) = ParityWalk.zeta (ξ (t + a + k)) := by
  have hrec := chi_obs_add hk ξ (t + a)
  have hsq : ParityWalk.chi (obs k ξ (t + a)) * ParityWalk.chi (obs k ξ (t + a)) = 1 := by
    cases obs k ξ (t + a) <;> norm_num [ParityWalk.chi]
  rw [chi_pairObs, show t + (a + k) = t + a + k by omega, ← hrec, ← mul_assoc, hsq, one_mul]

/-- The stationary answer to a **same-class** two-offset query at lag `k`.

For offsets in distinct residue classes the two observations are independent and uniform under the
stationary window law, and the answer is the flat `pairMean ψ`.  Inside one class at lag `k` they
are not: their pair character is the noise character itself, of mean `m`, so the answer is displaced
by `pairCoefAB ψ · m`.  This is where the noise rate lives for the same-class class — in the answer,
not in the constant. -/
noncomputable def samePairMean (ψ : Bool → Bool → ℝ) (m : ℝ) : ℝ :=
  pairMean ψ + pairCoefAB ψ * m

/-- **The same-class two-offset mixing constant**: `48·k`, carrying no dependence on the noise
rate — the same shape as the coordinate constant `4k` of `mixingHoeffding_noisyWindowChain`, and
for the same reason (there is nothing persistent whose gap must be divided by). -/
noncomputable def samePairConst (k : ℕ) : ℝ := 48 * k

@[simp] lemma samePairMean_pairChar (m : ℝ) : samePairMean pairChar m = m := by
  norm_num [samePairMean, pairMean, pairCoefAB, pairChar, ParityWalk.chi]

/-- **The answer displacement is at most the mean's own displacement.**  This is the inequality
[SQ] §3.1's window-noise budget consumes: moving the noise character's mean by `2η` moves the
same-class answer by at most `2η`, met with equality at `ψ = pairChar`. -/
lemma abs_samePairMean_sub {ψ : Bool → Bool → ℝ} (hψ : ∀ u v, |ψ u v| ≤ 1) (m m' : ℝ) :
    |samePairMean ψ m - samePairMean ψ m'| ≤ |m - m'| := by
  obtain ⟨-, -, -, hcAB⟩ := abs_pairCoef_le_one hψ
  have he : samePairMean ψ m - samePairMean ψ m' = pairCoefAB ψ * (m - m') := by
    simp only [samePairMean]; ring
  rw [he, abs_mul]
  exact mul_le_of_le_one_left (abs_nonneg _) hcAB

/-- The same-class answer stays inside the observable's own range, at every noise rate. -/
private lemma abs_samePairMean_le_one {ψ : Bool → Bool → ℝ} (hψ : ∀ u v, |ψ u v| ≤ 1)
    {m : ℝ} (hm0 : -1 ≤ m) (hm : m ≤ 0) : |samePairMean ψ m| ≤ 1 := by
  obtain ⟨h1, h1'⟩ := abs_le.mp (hψ false false)
  obtain ⟨h2, h2'⟩ := abs_le.mp (hψ false true)
  obtain ⟨h3, h3'⟩ := abs_le.mp (hψ true false)
  obtain ⟨h4, h4'⟩ := abs_le.mp (hψ true true)
  have hp : (0 : ℝ) ≤ 1 + m := by linarith
  have hq : (0 : ℝ) ≤ 1 - m := by linarith
  rw [abs_le]
  constructor <;> simp only [samePairMean, pairMean, pairCoefAB] <;>
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - ψ false false) hp,
      mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - ψ false true) hq,
      mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - ψ true false) hq,
      mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - ψ true true) hp,
      mul_nonneg (by linarith : (0 : ℝ) ≤ 1 + ψ false false) hp,
      mul_nonneg (by linarith : (0 : ℝ) ≤ 1 + ψ false true) hq,
      mul_nonneg (by linarith : (0 : ℝ) ≤ 1 + ψ true false) hq,
      mul_nonneg (by linarith : (0 : ℝ) ≤ 1 + ψ true true) hp]

/-! #### The guard, written first: at the flat answer the predicate fails

The cross-class guard refutes the predicate at zero noise, where the pair freezes.  The same-class
pair does *not* freeze at zero noise — it is deterministic and correct there — so the guard that
bites here is a different one: the **wrong answer**.  At the pinned configuration below the noise
character's mean is `m = -1` and the same-class pair character sits at `-1` forever, while the flat
answer `pairMean pairChar` is `0`.  So the predicate at the flat answer is refutable at every
positive constant, and the design claim it tests — that the noise rate moved out of the constant and
into the answer — is a theorem rather than a reading of the proof. -/

/-- The pinning behind the wrong-mean guard: at offsets `0` and `3` (the same residue class at lag
`k = 3`) the two observations are complementary at every time, so their pair character never leaves
`-1`. -/
private lemma frozen_pin_zero_three (t : ℕ) :
    pairChar (obs 3 frozenWord (t + 0)) (obs 3 frozenWord (t + 3)) = -1 := by
  rw [Nat.add_zero, frozen_obs_add t, pairChar, ParityWalk.chi_not]
  cases obs 3 frozenWord t <;> norm_num [ParityWalk.chi]

/-- **The wrong-mean refutation.**  At window length `3`, the same-class offsets `(0, 3)` and the
pinned noise word — a Dirac trajectory law whose noise character has mean `m = -1` — the two-offset
predicate at the FLAT answer `pairMean ψ` is refutable at every positive constant.

Contrast `not_mixingHoeffding_noisyWindowChain_pair_frozen`, whose content is that no constant
covers the cross-class pair at zero noise.  Here the constant is not at fault at all: the same
configuration satisfies the predicate at every constant once the answer is the displaced
`samePairMean` (`mixingHoeffding_frozen_samePair_correctMean`).  What fails is the flat answer, so
this theorem says exactly that the same-class noise dependence lives in the answer. -/
theorem not_mixingHoeffding_noisyWindowChain_samePair_flatMean
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] {c : ℝ} (hc : 0 < c) :
    ¬ BirkhoffTool.MixingHoeffding (Measure.map (traj 3 (fun i (_ : Ω) => frozenWord i)) P)
        (pairEnsemble pairChar 0 3) (pairMean pairChar) c := by
  refine not_mixingHoeffding_pinned_pair P (by norm_num) frozenWord pairChar hc
    frozen_pin_zero_three ?_
  rw [pairMean_pairChar]; norm_num

/-- **The perturbation test, sharp.**  The very configuration the wrong-mean guard refutes satisfies
the predicate at the *correct* answer `samePairMean pairChar (-1) = -1` — at **every** constant, the
deviation being identically zero.  So the guard above is about the answer and nothing else. -/
theorem mixingHoeffding_frozen_samePair_correctMean
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (c : ℝ) :
    BirkhoffTool.MixingHoeffding (Measure.map (traj 3 (fun i (_ : Ω) => frozenWord i)) P)
      (pairEnsemble pairChar 0 3) (samePairMean pairChar (-1)) c := by
  have hFmeas : Measurable (traj 3 (fun i (_ : Ω) => frozenWord i)) :=
    measurable_traj (by norm_num) fun _ => measurable_const
  simp only [samePairMean_pairChar]
  intro n τ hn hτ
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hemp : ∀ ω : Ω,
      SQOracle.empiricalMean (pairEnsemble pairChar 0 3) n
        (traj 3 (fun i (_ : Ω) => frozenWord i) ω) = -1 := by
    intro ω
    have hterm : ∀ t : ℕ,
        pairEnsemble pairChar 0 3 t (traj 3 (fun i (_ : Ω) => frozenWord i) ω) = -1 :=
      fun t => frozen_pin_zero_three t
    rw [SQOracle.empiricalMean, Finset.sum_congr rfl fun t _ => hterm t, Finset.sum_const,
      Finset.card_range, nsmul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hn0, one_mul]
  rcases eq_or_lt_of_le hτ with hτ0 | hτ0
  · -- at zero tolerance the tail bound is `2`, which dominates any probability
    rw [← hτ0]
    refine le_trans MeasureTheory.measureReal_le_one ?_
    norm_num
  · -- at positive tolerance the deviation event is empty
    have hAmeas : MeasurableSet
        {o : ℕ → Bool | τ ≤ |SQOracle.empiricalMean (pairEnsemble pairChar 0 3) n o - (-1)|} :=
      measurableSet_le measurable_const
        (((measurable_empiricalMean_pair pairChar 0 3 n).sub_const _).abs)
    have hpre : traj 3 (fun i (_ : Ω) => frozenWord i) ⁻¹'
        {o : ℕ → Bool | τ ≤ |SQOracle.empiricalMean (pairEnsemble pairChar 0 3) n o - (-1)|}
          = ∅ := by
      ext ω
      simp only [Set.mem_preimage, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_le,
        hemp ω]
      simpa using hτ0
    have hzero : (Measure.map (traj 3 (fun i (_ : Ω) => frozenWord i)) P).real
        {o : ℕ → Bool | τ ≤ |SQOracle.empiricalMean (pairEnsemble pairChar 0 3) n o - (-1)|}
          = 0 := by
      simp only [Measure.real, Measure.map_apply hFmeas hAmeas, hpre, measure_empty,
        ENNReal.toReal_zero]
    rw [hzero]
    positivity

/-! #### The two tails, and the capstone -/

/-- **The pair character's tail: a plain i.i.d. Hoeffding bound.**  The same-class pair character
being the noise character itself, its centred Birkhoff sum is a sum of independent, bounded, centred
variables; `ParityWalk.hasSubgaussianMGF_signedSum` at the constant sign `+1` gives it the
sub-Gaussian parameter `n`, the parameter an i.i.d. sum gets. -/
private lemma noiseChar_tail (hmeas : ∀ i, Measurable (ξ i)) (hindep : iIndepFun ξ P) {d : ℕ}
    (hmean : ∀ u, ∫ ω, ParityWalk.zeta (ξ (u + d) ω) ∂P = m) (n : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    P.real {ω | x ≤ |∑ t ∈ Finset.range n, (ParityWalk.zeta (ξ (t + d) ω) - m)|}
      ≤ 2 * Real.exp (-x ^ 2 / (2 * (n : ℝ))) := by
  have hsg : HasSubgaussianMGF
      (ParityWalk.signedSum ξ (fun (_ : ℕ) (_ : Ω) => false) m d n) n P :=
    ParityWalk.hasSubgaussianMGF_signedSum hmeas hindep (fun _ => measurable_const) hmean n
  have hre : ParityWalk.signedSum ξ (fun (_ : ℕ) (_ : Ω) => false) m d n
      = fun ω => ∑ t ∈ Finset.range n, (ParityWalk.zeta (ξ (t + d) ω) - m) := by
    funext ω
    simp [ParityWalk.signedSum, ParityWalk.chi]
  rw [hre] at hsg
  simpa using ParityWalk.measureReal_abs_ge_le hsg hx

/-- **The same-class query's deviation, split into three character sums** — the two coordinate
characters and the *centred* pair character.  The centring is the whole difference from
`empiricalMean_sub_pairMean`: it is where the displaced answer enters. -/
private lemma empiricalMean_sub_samePairMean (ψ : Bool → Bool → ℝ) (a b : ℕ) {n : ℕ} (hn : 1 ≤ n)
    (mm : ℝ) (o : ℕ → Bool) :
    (n : ℝ) * (SQOracle.empiricalMean (pairEnsemble ψ a b) n o - samePairMean ψ mm)
      = pairCoefA ψ * (∑ t ∈ Finset.range n, ParityWalk.chi (o (t + a)))
        + pairCoefB ψ * (∑ t ∈ Finset.range n, ParityWalk.chi (o (t + b)))
        + pairCoefAB ψ
            * (∑ t ∈ Finset.range n, (ParityWalk.chi (xor (o (t + a)) (o (t + b))) - mm)) := by
  have h := empiricalMean_sub_pairMean ψ a b hn o
  have hs : ∑ t ∈ Finset.range n, (ParityWalk.chi (xor (o (t + a)) (o (t + b))) - mm)
      = (∑ t ∈ Finset.range n, ParityWalk.chi (xor (o (t + a)) (o (t + b)))) - (n : ℝ) * mm := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have key : (n : ℝ) * (SQOracle.empiricalMean (pairEnsemble ψ a b) n o - samePairMean ψ mm)
      = (n : ℝ) * (SQOracle.empiricalMean (pairEnsemble ψ a b) n o - pairMean ψ)
        - (n : ℝ) * (pairCoefAB ψ * mm) := by
    simp only [samePairMean]; ring
  rw [key, h, hs]; ring

/-- **E1 for the same-class two-offset query class.**  The noisy window chain of window length
`k ≥ 1`, at EVERY noise rate, satisfies the FJS-shaped single-orbit Hoeffding hypothesis at the
explicit constant `samePairConst k = 48k` for every query reading two observations at offsets
`(a, a + k)` — the same residue class, at the chain's own lag — with a `[−1, 1]`-valued observable.

This is the query the witness's learner schedules against the *true* literal: the rule's own
coordinate read against the label it predicts ([SQ] §3.1).  Two things distinguish it from
`mixingHoeffding_noisyWindowChain_pair`, and they are the same thing seen twice.

The **constant carries no noise rate**, and the hypothesis `0 < η` is gone with it: `-1 ≤ m ≤ 0` is
all that is asked, exactly as in the coordinate theorem.  The reason is `chi_pairObs_lagK` — at this
lag the pair character is a single noise character, an i.i.d. sequence, so the persistent walk that
forced `pairConst k η = O(k/η)` is simply not present.

The **answer carries it instead**.  An i.i.d. pair character has mean `m`, so the stationary answer
is `samePairMean ψ m`, displaced from the flat `pairMean ψ` by `pairCoefAB ψ · m`.  That is not
slack: `not_mixingHoeffding_noisyWindowChain_samePair_flatMean` refutes the predicate at the flat
answer at every positive constant, on a law this theorem covers at the displaced one.  And
`abs_samePairMean_sub` prices the displacement at exactly [SQ] §3.1's own budget — writing
`m = 2η − 1`, the noisy answer sits within `2η` of the noiseless rule's answer. -/
theorem mixingHoeffding_noisyWindowChain_pair_lagK
    (hk : 1 ≤ k) (hmeas : ∀ i, Measurable (ξ i)) (hindep : iIndepFun ξ P)
    (hmean : ∀ u, ∫ ω, ParityWalk.zeta (ξ (u + k) ω) ∂P = m) (hm0 : -1 ≤ m) (hm : m ≤ 0)
    (a : ℕ) (ψ : Bool → Bool → ℝ) (hψ : ∀ u v, |ψ u v| ≤ 1) :
    BirkhoffTool.MixingHoeffding (Measure.map (traj k ξ) P) (pairEnsemble ψ a (a + k))
      (samePairMean ψ m) (samePairConst k) := by
  classical
  have hkR : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hconst : samePairConst k = 48 * (k : ℝ) := rfl
  have htraj : Measurable (traj k ξ) := measurable_traj hk hmeas
  have hmean' : ∀ i, k ≤ i → ∫ ω, ParityWalk.zeta (ξ i ω) ∂P = m := by
    intro i hi
    have h := hmean (i - k)
    rwa [Nat.sub_add_cancel hi] at h
  obtain ⟨-, hcA, hcB, hcAB⟩ := abs_pairCoef_le_one hψ
  have hansabs : |samePairMean ψ m| ≤ 1 := abs_samePairMean_le_one hψ hm0 hm
  intro n τ hn hτ
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  set A : Set (ℕ → Bool) :=
    {o | τ ≤ |SQOracle.empiricalMean (pairEnsemble ψ a (a + k)) n o - samePairMean ψ m|} with hA
  have hAmeas : MeasurableSet A :=
    measurableSet_le measurable_const
      (((measurable_empiricalMean_pair ψ a (a + k) n).sub_const _).abs)
  have hmap : (Measure.map (traj k ξ) P).real A = P.real (traj k ξ ⁻¹' A) := by
    simp only [Measure.real, Measure.map_apply htraj hAmeas]
  rw [hmap]
  have hempabs : ∀ o : ℕ → Bool, |SQOracle.empiricalMean (pairEnsemble ψ a (a + k)) n o| ≤ 1 := by
    intro o
    have hsum : |∑ t ∈ Finset.range n, pairEnsemble ψ a (a + k) t o| ≤ (n : ℝ) := by
      calc |∑ t ∈ Finset.range n, pairEnsemble ψ a (a + k) t o|
          ≤ ∑ t ∈ Finset.range n, |pairEnsemble ψ a (a + k) t o| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _t ∈ Finset.range n, (1 : ℝ) := Finset.sum_le_sum fun t _ => hψ _ _
        _ = (n : ℝ) := by simp
    rw [SQOracle.empiricalMean, abs_mul, abs_inv, abs_of_nonneg hn0.le]
    calc (n : ℝ)⁻¹ * |∑ t ∈ Finset.range n, pairEnsemble ψ a (a + k) t o|
        ≤ (n : ℝ)⁻¹ * (n : ℝ) := mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = 1 := inv_mul_cancel₀ (ne_of_gt hn0)
  by_cases hτ2 : 2 < τ
  · -- beyond the observable's own range the event is empty
    have hempty : traj k ξ ⁻¹' A = ∅ := by
      ext ω
      simp only [hA, Set.mem_preimage, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false,
        not_le]
      obtain ⟨h1, h2⟩ := abs_le.mp (hempabs (traj k ξ ω))
      obtain ⟨h3, h4⟩ := abs_le.mp hansabs
      exact abs_lt.mpr ⟨by linarith, by linarith⟩
    rw [hempty, measureReal_empty]
    positivity
  replace hτ2 : τ ≤ 2 := not_lt.mp hτ2
  by_cases hsmall : (n : ℝ) * τ < 30 * (k : ℝ)
  · -- the bound is not yet binding
    have hb2 : (n : ℝ) * τ ^ 2 ≤ 60 * (k : ℝ) := by
      nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 30 * (k : ℝ) - (n : ℝ) * τ) hτ]
    have hlog : (0.69 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
    have hkey : (n : ℝ) * τ ^ 2 / (2 * samePairConst k) ≤ Real.log 2 := by
      rw [hconst, div_le_iff₀ (by linarith)]
      nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ Real.log 2 - 0.625)
        (by linarith : (0 : ℝ) ≤ (k : ℝ))]
    have h1 : Real.exp (-Real.log 2) ≤ Real.exp (-((n : ℝ) * τ ^ 2 / (2 * samePairConst k))) :=
      Real.exp_le_exp.mpr (by linarith)
    have h2 : Real.exp (-Real.log 2) = 1 / 2 := by
      rw [Real.exp_neg, Real.exp_log (by norm_num)]; norm_num
    rw [h2] at h1
    rw [show -(n : ℝ) * τ ^ 2 / (2 * samePairConst k)
        = -((n : ℝ) * τ ^ 2 / (2 * samePairConst k)) by ring]
    exact le_trans MeasureTheory.measureReal_le_one (by linarith)
  · -- the three character tails
    replace hsmall : 30 * (k : ℝ) ≤ (n : ℝ) * τ := not_lt.mp hsmall
    have hτ0 : 0 < τ := by nlinarith
    have hnbig : 15 * (k : ℝ) ≤ (n : ℝ) := by nlinarith
    have hkn : k ≤ n := by
      have : (k : ℝ) ≤ (n : ℝ) := by linarith
      exact_mod_cast this
    have hnkpos : (0 : ℝ) < ((n - k : ℕ) : ℝ) := by
      have h2k : (2 : ℝ) * (k : ℝ) ≤ (n : ℝ) := by linarith
      have h2k' : 2 * k ≤ n := by exact_mod_cast h2k
      have : 0 < n - k := by omega
      exact_mod_cast this
    have hnkle : ((n - k : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.sub_le n k
    have hx1nn : (0 : ℝ) ≤ (n : ℝ) * τ / 3 - 2 * (k : ℝ) := by linarith
    have hx1big : (n : ℝ) * τ / 4 ≤ (n : ℝ) * τ / 3 - 2 * (k : ℝ) := by linarith
    -- a coordinate character's tail, at either offset
    have hcoordE : ∀ off : ℕ, P.real {ω | (n : ℝ) * τ / 3 ≤
        |∑ t ∈ Finset.range n, ParityWalk.chi (obs k (fun i => ξ i ω) (t + off))|}
        ≤ 2 * Real.exp (-((n : ℝ) * τ ^ 2 / 32)) := by
      intro off
      have h := coordChar_tail hk hmeas hindep hmean' hm0 hm off hkn hx1nn
      have hset : {ω | (n : ℝ) * τ / 3 ≤
          |∑ t ∈ Finset.range n, ParityWalk.chi (obs k (fun i => ξ i ω) (t + off))|}
          = {ω | ((n : ℝ) * τ / 3 - 2 * (k : ℝ)) + 2 * (k : ℝ) ≤
            |∑ t ∈ Finset.range n, ParityWalk.chi (obs k (fun i => ξ i ω) (t + off))|} := by
        ext ω; simp only [Set.mem_setOf_eq]; constructor <;> intro hh <;> linarith
      rw [hset]
      refine h.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by norm_num))
      rw [neg_div, neg_le_neg_iff, div_le_div_iff₀ (by norm_num) (by positivity)]
      have hnn : (0 : ℝ) ≤ (n : ℝ) * τ ^ 2 := by positivity
      have hsq : ((n : ℝ) * τ / 4) ^ 2 ≤ ((n : ℝ) * τ / 3 - 2 * (k : ℝ)) ^ 2 :=
        pow_le_pow_left₀ (by positivity) hx1big 2
      calc (n : ℝ) * τ ^ 2 * (2 * ((n - k : ℕ) : ℝ))
          ≤ (n : ℝ) * τ ^ 2 * (2 * (n : ℝ)) := mul_le_mul_of_nonneg_left (by linarith) hnn
        _ = 32 * ((n : ℝ) * τ / 4) ^ 2 := by ring
        _ ≤ 32 * ((n : ℝ) * τ / 3 - 2 * (k : ℝ)) ^ 2 := by linarith
        _ = ((n : ℝ) * τ / 3 - 2 * (k : ℝ)) ^ 2 * 32 := by ring
    -- the pair character's tail
    have hpairE : P.real {ω | (n : ℝ) * τ / 3 ≤
        |∑ t ∈ Finset.range n, (ParityWalk.zeta (ξ (t + (a + k)) ω) - m)|}
        ≤ 2 * Real.exp (-((n : ℝ) * τ ^ 2 / 32)) := by
      have h := noiseChar_tail (d := a + k) hmeas hindep
        (fun u => hmean' (u + (a + k)) (by omega)) n (by positivity : (0 : ℝ) ≤ (n : ℝ) * τ / 3)
      refine h.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by norm_num))
      rw [neg_div, neg_le_neg_iff, div_le_div_iff₀ (by norm_num) (by positivity)]
      nlinarith [sq_nonneg ((n : ℝ) * τ)]
    -- the deviation forces one of the three characters to be large
    have hincl : traj k ξ ⁻¹' A ⊆
        ({ω | (n : ℝ) * τ / 3 ≤
            |∑ t ∈ Finset.range n, ParityWalk.chi (obs k (fun i => ξ i ω) (t + a))|}
          ∪ {ω | (n : ℝ) * τ / 3 ≤
            |∑ t ∈ Finset.range n, ParityWalk.chi (obs k (fun i => ξ i ω) (t + (a + k)))|})
          ∪ {ω | (n : ℝ) * τ / 3 ≤
            |∑ t ∈ Finset.range n, (ParityWalk.zeta (ξ (t + (a + k)) ω) - m)|} := by
      intro ω hω
      simp only [hA, Set.mem_preimage, Set.mem_setOf_eq] at hω
      by_contra hcon
      simp only [Set.mem_union, not_or, Set.mem_setOf_eq, not_le] at hcon
      obtain ⟨⟨h1, h2⟩, h3⟩ := hcon
      have hid := empiricalMean_sub_samePairMean ψ a (a + k) hn m (traj k ξ ω)
      have htr : ∀ u, traj k ξ ω u = obs k (fun i => ξ i ω) u := fun _ => rfl
      have hxor : ∀ t, ParityWalk.chi (xor (obs k (fun i => ξ i ω) (t + a))
            (obs k (fun i => ξ i ω) (t + (a + k)))) = ParityWalk.zeta (ξ (t + (a + k)) ω) := by
        intro t
        have h := chi_pairObs_lagK (k := k) (by omega) a (fun i => ξ i ω) t
        rw [show t + a + k = t + (a + k) by omega] at h
        exact h
      simp only [htr, hxor] at hid
      have hbig : (n : ℝ) * τ ≤ |(n : ℝ)
          * (SQOracle.empiricalMean (pairEnsemble ψ a (a + k)) n (traj k ξ ω)
            - samePairMean ψ m)| := by
        rw [abs_mul, abs_of_nonneg hn0.le]
        exact mul_le_mul_of_nonneg_left hω hn0.le
      rw [hid] at hbig
      set Sa : ℝ := ∑ t ∈ Finset.range n, ParityWalk.chi (obs k (fun i => ξ i ω) (t + a))
      set Sb : ℝ := ∑ t ∈ Finset.range n, ParityWalk.chi (obs k (fun i => ξ i ω) (t + (a + k)))
      set Sq : ℝ := ∑ t ∈ Finset.range n, (ParityWalk.zeta (ξ (t + (a + k)) ω) - m)
      have ea : |pairCoefA ψ * Sa| ≤ |Sa| := by
        rw [abs_mul]; exact mul_le_of_le_one_left (abs_nonneg Sa) hcA
      have eb : |pairCoefB ψ * Sb| ≤ |Sb| := by
        rw [abs_mul]; exact mul_le_of_le_one_left (abs_nonneg Sb) hcB
      have ec : |pairCoefAB ψ * Sq| ≤ |Sq| := by
        rw [abs_mul]; exact mul_le_of_le_one_left (abs_nonneg Sq) hcAB
      have htri1 := abs_add_le (pairCoefA ψ * Sa + pairCoefB ψ * Sb) (pairCoefAB ψ * Sq)
      have htri2 := abs_add_le (pairCoefA ψ * Sa) (pairCoefB ψ * Sb)
      linarith
    -- assemble
    have hsix : P.real (traj k ξ ⁻¹' A) ≤ 6 * Real.exp (-((n : ℝ) * τ ^ 2 / 32)) := by
      refine le_trans (measureReal_mono hincl (measure_ne_top _ _)) ?_
      exact le_trans (measureReal_union3_le P _ _ _ _ (hcoordE a) (hcoordE (a + k)) hpairE)
        (le_of_eq (by ring))
    have hfin := bound_absorb MeasureTheory.measureReal_le_one hsix
    refine hfin.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by norm_num))
    rw [hconst, show -((n : ℝ) * τ ^ 2 / 32) / 3 = -((n : ℝ) * τ ^ 2 / 96) by ring,
      show -(n : ℝ) * τ ^ 2 / (2 * (48 * (k : ℝ))) = -((n : ℝ) * τ ^ 2 / (96 * (k : ℝ))) by ring,
      neg_le_neg_iff, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [mul_nonneg (mul_nonneg hn0.le (sq_nonneg τ)) (by linarith : (0 : ℝ) ≤ (k : ℝ) - 1)]

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

/-- info: 'NoisyWindowChain.mixingHoeffding_noisyWindowChain_pair' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NoisyWindowChain.mixingHoeffding_noisyWindowChain_pair

/-- info: 'NoisyWindowChain.not_mixingHoeffding_noisyWindowChain_pair_frozen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NoisyWindowChain.not_mixingHoeffding_noisyWindowChain_pair_frozen

/-- info: 'NoisyWindowChain.chi_pairObs_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NoisyWindowChain.chi_pairObs_add

/-- info: 'NoisyWindowChain.chi_pairObs_lagK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NoisyWindowChain.chi_pairObs_lagK

/-- info: 'NoisyWindowChain.mixingHoeffding_noisyWindowChain_pair_lagK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NoisyWindowChain.mixingHoeffding_noisyWindowChain_pair_lagK

/-- info: 'NoisyWindowChain.not_mixingHoeffding_noisyWindowChain_samePair_flatMean' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NoisyWindowChain.not_mixingHoeffding_noisyWindowChain_samePair_flatMean

/-- info: 'NoisyWindowChain.mixingHoeffding_frozen_samePair_correctMean' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NoisyWindowChain.mixingHoeffding_frozen_samePair_correctMean
