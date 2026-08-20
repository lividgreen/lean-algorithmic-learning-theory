/-
Copyright (c) 2026 Mykola Palamarchuk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mykola Palamarchuk
-/
import ALT.SubstitutionSchedule

/-!
# The strict-spectral substitution class: a `√n` envelope hypothesis and its consumers
([Growth] §5)

`SubstitutionSchedule.ProfileNat` bounds every window character sum by a CONSTANT `S` (or `W a`),
uniform in the horizon `n`. That is exactly what one non-eventually-periodic instance
(`SubstitutionSource.subObs`) delivers, but it is not what the wider class of primitive
constant-length substitutions with a strict spectral gap on their order-2 substitution matrix
delivers: for such a member the discrepancy dichotomy gives an order-`√n` bound, not a constant
one. `EnvelopeProfileNat` is `ProfileNat`'s twin with both right-hand sides scaled by `Real.sqrt n`,
the hypothesis shape that dichotomy actually hands over (any power below the boundary exponent
`1/2`, with any log factor, is absorbed into a clean `C · √n` bound at every `n ≥ 1`).

Both of `ProfileNat`'s consumers generalize cleanly to the envelope: `deviation_bound_envelope` is
`SubstitutionSchedule.deviation_bound_nat`'s proof with the `√n` factor carried through, and
`envelope_mixingHoeffding` / `schedSurvivors_eq_singleton_envelope` are the `√n`-twins of
`BirkhoffTool.mixingHoeffding_dirac_of_deviation_bound` and
`SubstitutionSchedule.schedSurvivors_eq_singleton_sharp_nat`, both routed through
`GrowingComposite.mixingHoeffding_dirac_iff`'s per-`n` reading instead of the constant-envelope
lemma, since the deviation bound itself now shrinks as `1/√n` rather than `1/n`.

`profileNat_toEnvelope` shows a constant bound is a special case (`S ≤ S · √n` at `n ≥ 1`), so the
landed instance (`SubstitutionSchedule.subObs_profile`) inhabits the class hypothesis
unconditionally — see `SubstitutionComposite.subObs_envelopeProfile`. `envelope_trend_unique`
shows the declared
trend data `ρ` is canonical given any envelope: two envelopes on the same observation with the same
phase force the same `ρ`, since a bounded difference that shrinks as `1/√n` at every horizon must be
zero.

## Main results

* `EnvelopeProfileNat` — the `√n`-scaled window-deviation profile.
* `profileNat_toEnvelope` — `ProfileNat` is the constant-bound special case of the envelope.
* `envelope_trend_unique` — the declared trend `ρ` is canonical given any envelope.
* `deviation_bound_envelope` — the two-offset query's deviation from the envelope's displaced
  answer, at the `√n`-scaled constant.
* `envelope_mixingHoeffding` — Dirac E1 at every envelope member, at the constant
  `(2S + W a)² / (2 ln 2)`.
* `schedSurvivors_eq_singleton_envelope`, `envelopeHorizon`, `identifies_of_lt_quarter_envelope` —
  the sharp identification window, at the squared horizon `((2S + Wm) / margin)² < n`.

## Scope

The class enters through the envelope hypothesis alone: nothing here defines an induced
substitution, a Perron vector, or decides membership from a spectral condition. A member's own
`ρ`, `S`, `W` are declared data, constrained by the envelope and pinned canonical by
`envelope_trend_unique`; the dichotomy that DELIVERS the envelope for a strict-spectral member is a
citation (Adamczewski, *Symbolic discrepancy and self-similar dynamics*, Ann. Inst. Fourier 54
(2004) 2201–2234), not machine-checked content.
-/

namespace SubstitutionClass

open NoisyWindowChain BirkhoffTool Finset SubstitutionSchedule TapeHostSchedule

/-! ## The envelope profile -/

/-- **The `√n`-scaled window-deviation profile**, over `o : ℕ → Bool` directly.
`SubstitutionSchedule.ProfileNat`'s twin, with both right-hand sides scaled by `Real.sqrt n`: the
hypothesis shape a primitive constant-length substitution member with second eigenvalue of its
order-2 substitution strictly below `√(length)` delivers, by Adamczewski, *Symbolic discrepancy and
self-similar dynamics*, Ann. Inst. Fourier 54 (2004) 2201–2234, Theorem 3 with Propositions 27/28
(any exponent strictly below `1/2`, with any log factor, is absorbed into a clean `C · √n` bound at
every `n ≥ 1`). Carried here as a hypothesis at declared trend data, not derived: defining the
induced substitution and proving unique ergodicity would import machinery no consumer below
needs. -/
structure EnvelopeProfileNat (o : ℕ → Bool) (S : ℝ) (ρ W : Fin 8 → ℝ) : Prop where
  /-- The single-site character sum, at every phase and horizon, is bounded by `S · √n`. -/
  single : ∀ (c n : ℕ), |∑ t ∈ range n, ParityWalk.chi (o (c + t))| ≤ S * Real.sqrt n
  /-- The pair character sum at offsets `(a, 8)`, at every phase and horizon, deviates from the
  linear trend `n * ρ a` by at most `W a · √n`. -/
  pair : ∀ (c : ℕ) (a : Fin 8) (n : ℕ),
    |∑ t ∈ range n, ParityWalk.chi (o (c + t + (a : ℕ))) *
        ParityWalk.chi (o (c + t + 8)) - (n : ℝ) * ρ a| ≤ W a * Real.sqrt n

private theorem nonneg_of_single {o : ℕ → Bool} {S : ℝ} {ρ W : Fin 8 → ℝ}
    (h : EnvelopeProfileNat o S ρ W) : 0 ≤ S := by
  have h0 : (0 : ℝ) ≤ S * Real.sqrt (1 : ℕ) := le_trans (abs_nonneg _) (h.single 0 1)
  simpa using h0

private theorem nonneg_of_pair {o : ℕ → Bool} {S : ℝ} {ρ W : Fin 8 → ℝ}
    (h : EnvelopeProfileNat o S ρ W) (a : Fin 8) : 0 ≤ W a := by
  have h0 : (0 : ℝ) ≤ W a * Real.sqrt (1 : ℕ) := le_trans (abs_nonneg _) (h.pair 0 a 1)
  simpa using h0

/-- **`ProfileNat` is the constant-bound special case of the envelope.** A constant bound is
`≤ C · √n` at every `n ≥ 1` (`Real.one_le_sqrt`); at `n = 0` both sides of each field vanish. So
every constant-profile source — in particular `SubstitutionSchedule.subObs_profile` — inhabits the
class hypothesis unconditionally. -/
theorem profileNat_toEnvelope {o : ℕ → Bool} {S : ℝ} {ρ W : Fin 8 → ℝ}
    (h : SubstitutionSchedule.ProfileNat o S ρ W) : EnvelopeProfileNat o S ρ W where
  single c n := by
    rcases Nat.eq_zero_or_pos n with rfl | hn1
    · simp
    · have hb := h.single c n
      have hS : (0 : ℝ) ≤ S := le_trans (abs_nonneg _) hb
      have h1 : (1 : ℝ) ≤ Real.sqrt n := Real.one_le_sqrt.mpr (by exact_mod_cast hn1)
      exact le_trans hb (le_mul_of_one_le_right hS h1)
  pair c a n := by
    rcases Nat.eq_zero_or_pos n with rfl | hn1
    · simp
    · have hb := h.pair c a n
      have hW : (0 : ℝ) ≤ W a := le_trans (abs_nonneg _) hb
      have h1 : (1 : ℝ) ≤ Real.sqrt n := Real.one_le_sqrt.mpr (by exact_mod_cast hn1)
      exact le_trans hb (le_mul_of_one_le_right hW h1)

/-- **The declared trend `ρ` is canonical given any envelope.** Two envelopes on the same
observation, at the same phase, force the same `ρ`: their pair fields combine to
`n * |ρ a - ρ' a| ≤ (W a + W' a) * √n` at every `n ≥ 1`, and a difference bounded that way at every
horizon is forced to `0` (a witness `n` past `(C / |ρ a - ρ' a|)²` refutes any nonzero gap). -/
theorem envelope_trend_unique {o : ℕ → Bool} {S S' : ℝ} {ρ ρ' W W' : Fin 8 → ℝ}
    (h : EnvelopeProfileNat o S ρ W) (h' : EnvelopeProfileNat o S' ρ' W') : ρ = ρ' := by
  funext a
  by_contra hne
  have hdpos : 0 < |ρ a - ρ' a| := abs_pos.mpr (sub_ne_zero.mpr hne)
  have hWa : 0 ≤ W a := nonneg_of_pair h a
  have hWa' : 0 ≤ W' a := nonneg_of_pair h' a
  set C : ℝ := W a + W' a with hCdef
  have hCnn : 0 ≤ C := add_nonneg hWa hWa'
  have hbound : ∀ n : ℕ, 1 ≤ n → (n : ℝ) * |ρ a - ρ' a| ≤ C * Real.sqrt n := by
    intro n hn1
    have h1 := h.pair 0 a n
    have h2 := h'.pair 0 a n
    rw [abs_le] at h1 h2
    have hmul : (n : ℝ) * |ρ a - ρ' a| = |(n : ℝ) * (ρ a - ρ' a)| := by
      rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) n)]
    rw [hmul, abs_le]
    constructor <;> nlinarith [h1.1, h1.2, h2.1, h2.2]
  set n0 : ℕ := ⌊(C / |ρ a - ρ' a|) ^ 2⌋₊ + 1 with hn0def
  have hn0gt : (C / |ρ a - ρ' a|) ^ 2 < (n0 : ℝ) := by
    rw [hn0def]; push_cast; exact Nat.lt_floor_add_one _
  have hn0ge1 : 1 ≤ n0 := Nat.le_add_left 1 _
  have hsq : C / |ρ a - ρ' a| < Real.sqrt n0 :=
    (Real.lt_sqrt (div_nonneg hCnn hdpos.le)).mpr hn0gt
  have hmullt : C < Real.sqrt n0 * |ρ a - ρ' a| := by
    rw [div_lt_iff₀ hdpos] at hsq; exact hsq
  have hn0pos : 0 < Real.sqrt (n0 : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hn0ge1)
  have hstep : C * Real.sqrt n0 < (Real.sqrt n0 * |ρ a - ρ' a|) * Real.sqrt n0 :=
    mul_lt_mul_of_pos_right hmullt hn0pos
  have hsqeq : Real.sqrt (n0 : ℝ) * Real.sqrt (n0 : ℝ) = (n0 : ℝ) :=
    Real.mul_self_sqrt (Nat.cast_nonneg n0)
  have hrw : (Real.sqrt n0 * |ρ a - ρ' a|) * Real.sqrt n0
      = (n0 : ℝ) * |ρ a - ρ' a| := by rw [mul_right_comm, hsqeq]
  rw [hrw] at hstep
  exact absurd (hbound n0 hn0ge1) (not_le.mpr hstep)

/-- Dividing a `deviation ≤ D · √n` bound by `n` gives `deviation ≤ D / √n`: the elementary step
`envelope_mixingHoeffding` and `schedSurvivors_eq_singleton_envelope` both reduce to. -/
private theorem sqrt_mul_abs_le_of_nat_mul_abs_le {n : ℕ} (hn1 : 1 ≤ n) {x D : ℝ}
    (hb : (n : ℝ) * |x| ≤ D * Real.sqrt n) : |x| ≤ D / Real.sqrt n := by
  have hsqrtpos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hn1)
  have heqn : Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) = (n : ℝ) :=
    Real.mul_self_sqrt (Nat.cast_nonneg n)
  rw [le_div_iff₀ hsqrtpos]
  have hstep : (Real.sqrt (n : ℝ) * |x|) * Real.sqrt (n : ℝ) ≤ D * Real.sqrt (n : ℝ) := by
    calc (Real.sqrt (n : ℝ) * |x|) * Real.sqrt (n : ℝ)
        = (Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ)) * |x| := by ring
      _ = (n : ℝ) * |x| := by rw [heqn]
      _ ≤ D * Real.sqrt (n : ℝ) := hb
  have hcancel := le_of_mul_le_mul_right hstep hsqrtpos
  linarith [hcancel]

/-- A squared-horizon witness past `(D / m)²` puts `D / √n` below the margin `m`: the elementary
step `schedSurvivors_eq_singleton_envelope`'s three margins and `envelopeHorizon` both reduce to. -/
private theorem div_sqrt_lt_of_sq_lt {D m : ℝ} (hm : 0 < m) (hD : 0 ≤ D) {n : ℕ} (hn1 : 1 ≤ n)
    (hsq : (D / m) ^ 2 < (n : ℝ)) : D / Real.sqrt n < m := by
  have hsqrtpos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hn1)
  have h2 : D / m < Real.sqrt n := (Real.lt_sqrt (div_nonneg hD hm.le)).mpr hsq
  rw [div_lt_iff₀ hm] at h2
  rw [div_lt_iff₀ hsqrtpos]
  nlinarith [h2]

/-! ## The deviation bound, and E1 -/

/-- **The query's deviation from the envelope's own displaced answer, over `ℕ`, at the `√n`-scaled
constant.** `SubstitutionSchedule.deviation_bound_nat`'s proof with the `√n` factor carried through:
the underlying combinator `NoisyWindowChain.empiricalMean_deviation_le_of_window_bounds` is generic
in its `S`/`W` arguments, so it accepts `S · √n` and `W a · √n` exactly as it accepts a constant. -/
theorem deviation_bound_envelope {o : ℕ → Bool} {S : ℝ} {ρ W : Fin 8 → ℝ}
    (h : EnvelopeProfileNat o S ρ W) (c : ℕ) (ψ : Bool → Bool → ℝ) (hψ : ∀ u v, |ψ u v| ≤ 1)
    (a : Fin 8) {n : ℕ} (hn : 1 ≤ n) :
    (n : ℝ) * |SQOracle.empiricalMean (pairEnsemble ψ (a : ℕ) 8) n (fun t => o (c + t)) -
        (pairMean ψ + pairCoefAB ψ * ρ a)| ≤ (2 * S + W a) * Real.sqrt n := by
  have hSa : |∑ t ∈ range n, ParityWalk.chi ((fun t => o (c + t)) (t + (a : ℕ)))|
      ≤ S * Real.sqrt n := by
    have heq : (∑ t ∈ range n, ParityWalk.chi ((fun t => o (c + t)) (t + (a : ℕ))))
        = ∑ t ∈ range n, ParityWalk.chi (o (c + (a : ℕ) + t)) := by
      refine Finset.sum_congr rfl (fun t _ => ?_)
      simp only []
      congr 1; congr 1; omega
    rw [heq]
    exact h.single (c + (a : ℕ)) n
  have hSb : |∑ t ∈ range n, ParityWalk.chi ((fun t => o (c + t)) (t + 8))|
      ≤ S * Real.sqrt n := by
    have heq : (∑ t ∈ range n, ParityWalk.chi ((fun t => o (c + t)) (t + 8)))
        = ∑ t ∈ range n, ParityWalk.chi (o (c + 8 + t)) := by
      refine Finset.sum_congr rfl (fun t _ => ?_)
      simp only []
      congr 1; congr 1; omega
    rw [heq]
    exact h.single (c + 8) n
  have hW : |∑ t ∈ range n, ParityWalk.chi ((fun t => o (c + t)) (t + (a : ℕ))) *
      ParityWalk.chi ((fun t => o (c + t)) (t + 8)) - (n : ℝ) * ρ a| ≤ W a * Real.sqrt n := by
    have heq : (∑ t ∈ range n, ParityWalk.chi ((fun t => o (c + t)) (t + (a : ℕ))) *
        ParityWalk.chi ((fun t => o (c + t)) (t + 8)))
        = ∑ t ∈ range n, ParityWalk.chi (o (c + t + (a : ℕ))) * ParityWalk.chi (o (c + t + 8)) := by
      refine Finset.sum_congr rfl (fun t _ => ?_)
      simp only []
      congr 1; (congr 1; congr 1; omega)
    rw [heq]
    exact h.pair c a n
  have hbase := empiricalMean_deviation_le_of_window_bounds ψ hψ (a : ℕ) 8 hn (fun t => o (c + t))
    (ρ a) (S * Real.sqrt n) (W a * Real.sqrt n) hSa hSb hW
  have heqrhs : (2 * S + W a) * Real.sqrt n = 2 * (S * Real.sqrt n) + W a * Real.sqrt n := by ring
  rw [heqrhs]
  exact hbase

/-- **Dirac E1 at every envelope member**, at the constant `(2S + W a)² / (2 ln 2)` — the `√n`-twin
of `BirkhoffTool.mixingHoeffding_dirac_of_deviation_bound`, routed through
`GrowingComposite.mixingHoeffding_dirac_iff` since the deviation bound here shrinks as `1/√n`
rather than being flat. At the degenerate constant `2S + W a = 0` the target constant is `0` and
`BirkhoffTool.mixingHoeffding_of_nonpos` discharges it directly, so no positivity hypothesis on
`2S + W a` is carried. -/
theorem envelope_mixingHoeffding {o : ℕ → Bool} {S : ℝ} {ρ W : Fin 8 → ℝ}
    (h : EnvelopeProfileNat o S ρ W) (a : Fin 8) :
    BirkhoffTool.MixingHoeffding (MeasureTheory.Measure.dirac o) (pairEnsemble pairChar (a : ℕ) 8)
      (ρ a) ((2 * S + W a) ^ 2 / (2 * Real.log 2)) := by
  have hSnn : 0 ≤ S := nonneg_of_single h
  have hWnn : 0 ≤ W a := nonneg_of_pair h a
  have hDnn : 0 ≤ 2 * S + W a := by linarith
  rcases eq_or_lt_of_le hDnn with hD0 | hDpos
  · exact BirkhoffTool.mixingHoeffding_of_nonpos _ _ _ _ (by rw [← hD0]; norm_num)
  · have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hc : 0 < (2 * S + W a) ^ 2 / (2 * Real.log 2) := by positivity
    rw [GrowingComposite.mixingHoeffding_dirac_iff o (pairEnsemble pairChar (a : ℕ) 8) (ρ a) _ hc
      (fun i => measurable_pairEnsemble pairChar (a : ℕ) 8 i)]
    intro n hn1
    have hdb := deviation_bound_envelope h 0 pairChar abs_pairChar_le_one a hn1
    simp only [Nat.zero_add] at hdb
    rw [pairMean_pairChar, pairCoefAB_pairChar, one_mul, zero_add] at hdb
    have hε := sqrt_mul_abs_le_of_nat_mul_abs_le hn1 hdb
    have heq : Real.sqrt (2 * ((2 * S + W a) ^ 2 / (2 * Real.log 2)) * Real.log 2 / (n : ℝ))
        = (2 * S + W a) / Real.sqrt n := by
      rw [show 2 * ((2 * S + W a) ^ 2 / (2 * Real.log 2)) * Real.log 2 / (n : ℝ)
          = (2 * S + W a) ^ 2 / (n : ℝ) from by field_simp]
      rw [Real.sqrt_div (sq_nonneg _), Real.sqrt_sq hDnn]
    rw [heq]
    exact hε

/-! ## The sharp identification window, `√n` form -/

/-- **The sharp identification window, over `ℕ`, at the `√n`-envelope.**
`SubstitutionSchedule.schedSurvivors_eq_singleton_sharp_nat`'s twin: the deterministic error is
`ε_n = (2S + Wm) / √n` in place of `(2S + Wm) / n`, and the same three-margin argument closes. -/
theorem schedSurvivors_eq_singleton_envelope {o : ℕ → Bool} {S : ℝ} {ρ W : Fin 8 → ℝ}
    (h : EnvelopeProfileNat o S ρ W) (Wm : ℝ) (hW : ∀ a, W a ≤ Wm)
    {η τ μ : ℝ} (hτ : 0 < τ) (hη : 0 ≤ η) (hρ0 : ρ 0 = 2 * η - 1)
    (hρ : ∀ a : Fin 8, (a : ℕ) ≠ 0 → |ρ a| ≤ μ) (_hμ0 : 0 ≤ μ)
    (hbudget : 2 * η ≤ τ) (hμτ : μ < 2 * τ) (hsep : 2 * τ + μ < 1)
    (c : ℕ) {n : ℕ} (hn1 : 1 ≤ n)
    (hn : ((2 * S + Wm) / min (2 * τ - 2 * η) (min (2 * τ - μ) (1 - μ - 2 * τ))) ^ 2 < n) :
    TapeHostSchedule.schedSurvivors τ n (fun t => o (c + t)) = {0} := by
  have hm1 : (0 : ℝ) < 2 * τ - 2 * η := by linarith
  have hm2 : (0 : ℝ) < 2 * τ - μ := by linarith
  have hm3 : (0 : ℝ) < 1 - μ - 2 * τ := by linarith
  have hmm : (0 : ℝ) < min (2 * τ - 2 * η) (min (2 * τ - μ) (1 - μ - 2 * τ)) :=
    lt_min hm1 (lt_min hm2 hm3)
  have hSnn : 0 ≤ S := nonneg_of_single h
  have hWmnn : 0 ≤ Wm := le_trans (nonneg_of_pair h 0) (hW 0)
  have hDnn : 0 ≤ 2 * S + Wm := by linarith
  have heps : (2 * S + Wm) / Real.sqrt n <
      min (2 * τ - 2 * η) (min (2 * τ - μ) (1 - μ - 2 * τ)) :=
    div_sqrt_lt_of_sq_lt hmm hDnn hn1 hn
  have hlt1 : (2 * S + Wm) / Real.sqrt n < 2 * τ - 2 * η :=
    lt_of_lt_of_le heps (min_le_left _ _)
  have hlt2 : (2 * S + Wm) / Real.sqrt n < 2 * τ - μ :=
    lt_of_lt_of_le heps (le_trans (min_le_right _ _) (min_le_left _ _))
  have hlt3 : (2 * S + Wm) / Real.sqrt n < 1 - μ - 2 * τ :=
    lt_of_lt_of_le heps (le_trans (min_le_right _ _) (min_le_right _ _))
  have hε : ∀ a : Fin 8, |SQOracle.empiricalMean (pairEnsemble pairChar (a : ℕ) 8) n
      (fun t => o (c + t)) - ρ a| ≤ (2 * S + Wm) / Real.sqrt n := by
    intro a
    have hdb := deviation_bound_envelope h c pairChar abs_pairChar_le_one a hn1
    rw [pairMean_pairChar, pairCoefAB_pairChar, one_mul, zero_add] at hdb
    have hWa : W a ≤ Wm := hW a
    have hsqrtnn : 0 ≤ Real.sqrt (n : ℝ) := Real.sqrt_nonneg _
    have hbound : (n : ℝ) * |SQOracle.empiricalMean (pairEnsemble pairChar (a : ℕ) 8) n
        (fun t => o (c + t)) - ρ a| ≤ (2 * S + Wm) * Real.sqrt n := by
      nlinarith [hdb, hWa, hsqrtnn]
    exact sqrt_mul_abs_le_of_nat_mul_abs_le hn1 hbound
  rw [Finset.eq_singleton_iff_unique_mem]
  constructor
  · simp only [TapeHostSchedule.schedSurvivors, Finset.mem_filter, Finset.mem_univ, true_and]
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
  · intro i hi
    by_contra hne
    simp only [TapeHostSchedule.schedSurvivors, Finset.mem_filter, Finset.mem_univ,
      true_and] at hi
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
        (fun t => o (c + t)) < -(2 * τ) := by nlinarith [hεl, hεu, hρl, hρu, hlt3]
    have habs2 : |(-1 : ℝ) - SQOracle.empiricalMean (pairEnsemble pairChar (i : ℕ) 8) n
        (fun t => o (c + t))| > 2 * τ := by
      rw [abs_of_neg (by linarith [hx] : (-1 : ℝ) - SQOracle.empiricalMean
          (pairEnsemble pairChar (i : ℕ) 8) n (fun t => o (c + t)) < 0)]
      linarith [hx]
    linarith [hb, habs2]

/-- **The envelope identification horizon**, as an explicit natural number: the least natural
strictly above `((2S + Wm) / margin)²`, the squared form `SubstitutionSchedule.sharpHorizon`'s own
horizon takes since the deterministic error here shrinks as `1/√n`. -/
noncomputable def envelopeHorizon (S Wm η τ μ : ℝ) : ℕ :=
  ⌊((2 * S + Wm) / min (2 * τ - 2 * η) (min (2 * τ - μ) (1 - μ - 2 * τ))) ^ 2⌋₊ + 1

private theorem one_le_envelopeHorizon (S Wm η τ μ : ℝ) : 1 ≤ envelopeHorizon S Wm η τ μ :=
  Nat.le_add_left 1 _

private theorem schedSurvivors_eq_singleton_envelope_of_horizon {o : ℕ → Bool} {S : ℝ}
    {ρ W : Fin 8 → ℝ} (h : EnvelopeProfileNat o S ρ W) (Wm : ℝ) (hW : ∀ a, W a ≤ Wm)
    {η τ μ : ℝ} (hτ : 0 < τ) (hη : 0 ≤ η) (hρ0 : ρ 0 = 2 * η - 1)
    (hρ : ∀ a : Fin 8, (a : ℕ) ≠ 0 → |ρ a| ≤ μ) (hμ0 : 0 ≤ μ)
    (hbudget : 2 * η ≤ τ) (hμτ : μ < 2 * τ) (hsep : 2 * τ + μ < 1)
    (c : ℕ) {n : ℕ} (hn1 : 1 ≤ n) (hn : envelopeHorizon S Wm η τ μ ≤ n) :
    TapeHostSchedule.schedSurvivors τ n (fun t => o (c + t)) = {0} := by
  have hlt : ((2 * S + Wm) / min (2 * τ - 2 * η) (min (2 * τ - μ) (1 - μ - 2 * τ))) ^ 2
      < (n : ℝ) := by
    have h1 := Nat.lt_floor_add_one
      (((2 * S + Wm) / min (2 * τ - 2 * η) (min (2 * τ - μ) (1 - μ - 2 * τ))) ^ 2)
    have h2 : (⌊((2 * S + Wm) / min (2 * τ - 2 * η) (min (2 * τ - μ) (1 - μ - 2 * τ))) ^ 2⌋₊ + 1
        : ℝ) ≤ (n : ℝ) := by
      have hn' : envelopeHorizon S Wm η τ μ ≤ n := hn
      exact_mod_cast hn'
    linarith
  exact schedSurvivors_eq_singleton_envelope h Wm hW hτ hη hρ0 hρ hμ0 hbudget hμτ hsep c hn1 hlt

/-- **The sharp identification window, at the envelope.** At every density `η < (1 - μ) / 4` with
`μ < 1 / 2`, some admissible tolerance `τ` identifies the true literal from `envelopeHorizon`'s
horizon on — `TapeHostSchedule.identifies_of_lt_quarter`'s twin, at the envelope hypothesis and its
squared horizon. -/
theorem identifies_of_lt_quarter_envelope {o : ℕ → Bool} {S : ℝ} {ρ W : Fin 8 → ℝ}
    (h : EnvelopeProfileNat o S ρ W) (Wm : ℝ) (hW : ∀ a, W a ≤ Wm)
    {η μ : ℝ} (hη : 0 ≤ η) (hρ0 : ρ 0 = 2 * η - 1) (hρ : ∀ a : Fin 8, (a : ℕ) ≠ 0 → |ρ a| ≤ μ)
    (hμ0 : 0 ≤ μ) (hμ : μ < 1 / 2) (hwin : η < (1 - μ) / 4) (c : ℕ) :
    ∃ τ : ℝ, 0 < τ ∧ 2 * η ≤ τ ∧
      ∀ n : ℕ, envelopeHorizon S Wm η τ μ ≤ n →
        TapeHostSchedule.schedSurvivors τ n (fun t => o (c + t)) = {0} := by
  have hA1 : 2 * η ≤ max (2 * η) (μ / 2) := le_max_left _ _
  have hA2 : μ / 2 ≤ max (2 * η) (μ / 2) := le_max_right _ _
  have hAB : max (2 * η) (μ / 2) < (1 - μ) / 2 :=
    max_lt (by linarith [hwin]) (by linarith [hμ])
  refine ⟨(max (2 * η) (μ / 2) + (1 - μ) / 2) / 2, by linarith, by linarith, fun n hn => ?_⟩
  have hn1 : 1 ≤ n :=
    le_trans (one_le_envelopeHorizon S Wm η ((max (2 * η) (μ / 2) + (1 - μ) / 2) / 2) μ) hn
  exact schedSurvivors_eq_singleton_envelope_of_horizon h Wm hW (by linarith) hη hρ0 hρ hμ0
    (by linarith) (by linarith) (by linarith) c hn1 hn

end SubstitutionClass

/-! ## Axiom audit

Every capstone above is `#print axioms`-clean on the standard triple, and the guards below make
that build-enforced. -/

set_option linter.style.longLine false

/-- info: 'SubstitutionClass.profileNat_toEnvelope' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SubstitutionClass.profileNat_toEnvelope

/-- info: 'SubstitutionClass.envelope_trend_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SubstitutionClass.envelope_trend_unique

/-- info: 'SubstitutionClass.deviation_bound_envelope' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SubstitutionClass.deviation_bound_envelope

/-- info: 'SubstitutionClass.envelope_mixingHoeffding' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SubstitutionClass.envelope_mixingHoeffding

/-- info: 'SubstitutionClass.schedSurvivors_eq_singleton_envelope' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SubstitutionClass.schedSurvivors_eq_singleton_envelope

/-- info: 'SubstitutionClass.identifies_of_lt_quarter_envelope' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SubstitutionClass.identifies_of_lt_quarter_envelope
