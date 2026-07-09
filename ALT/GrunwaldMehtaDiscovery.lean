import Mathlib
import ALT.EpsilonZeroBound

-- Tier-1 formal check, not Mathlib-destined: opt out of the house-style linters.
set_option linter.style.header false
set_option linter.style.longLine false

/-!
# Finite-time discovery — Paper II §3, Theorem 3.1 (prequential MDL)

Provenance: `02_mdl_dominance_and_discovery.md` §3.2 (central/Bernstein condition) and §3.3
(concentration + separation ⇒ discovery). The deep engine — **Grünwald–Mehta (2020) Theorem 7.4**
(the central condition implies an `O(1/n)` fast rate) — is a published black box: Mathlib has no
PAC-Bayes / fast-rate machinery, so for the **general stochastic** case we **import it as a
hypothesis** (`hrate`) and do NOT reprove it.

**No import remains for the paper's actual claim.** For the **realizable-deterministic** case — the
setting of Paper II's Sub-problem B — Theorem 3.1 is proved **fully unconditionally** in
`ALT/DeterministicDiscovery.lean` (`deterministic_discovery`): a direct
competitor-likelihood-decay argument over the prequential Bayes mixture of
`ALT/BayesRedundancy.lean`, with **no** GM Thm 7.4, **no** Markov step, and **no**
posterior-of-close hypothesis. The GM-conditional development below is the general-stochastic
generalization; `hrate` is its one genuine import, eliminated in the deterministic case.
(N.B. the two are different quantities: `hrate` here bounds `E[D_H²(P̄ₙ, P_R)]` — the Hellinger of the
*mixture* against the truth, in expectation over random data — whereas `DeterministicDiscovery`
bounds the cumulative per-step Hellinger `∑_t D_H²(δ_{oₜ}, condₜ)` for a fixed realised sequence; the
GM rate is precisely the bridge between them, so the deterministic proof does not route through it.)

This file machine-checks the paper's own two contributions feeding Theorem 3.1:

* **Piece 1 — `bernstein_central`** (§3.2): the central/`v`-GRIP condition `E[X²] ≤ ℓmax·E[X]` for a
  bounded non-negative excess loss, fully proved (elementary).
* **Piece 2 — `discovery_posterior_bound`** (§3.3): given the imported GM rate `Z n ≤ B/n`, a Markov
  step, and the separation/posterior modelling implication (all named hypotheses), the elementary
  threshold/Markov arithmetic delivering posterior concentration `w(R) ≥ 1 − δ/2`.

## What is PROVED vs. ASSUMED
* PROVED (no `sorry`): the central condition (Piece 1); and the §3.3 concentration *arithmetic* —
  rate `Z n ≤ B/n` past the threshold `n ≥ 2B/(δ ε₀)` gives `Z n ≤ (δ/2)·ε₀`, Markov then gives the
  tail `≤ δ/2`, and the posterior implication gives `w(R) ≥ 1 − δ/2`.
* ASSUMED (named hypotheses, **general stochastic case only** — all eliminated in the
  realizable-deterministic `DeterministicDiscovery.deterministic_discovery`): `hrate` = **GM Thm 7.4**
  (the one deep import here); `hpost` = `posterior_of_close`, the modelling implication that a mixture
  within `ε₀` of `P_R` (which, under the separation `hsep`, only `R` can achieve) carries posterior
  weight `w(R) ≥ 1 − tail`.
* The Markov step is now **proved** (Piece 2′): `markov_tail_real` discharges it with Mathlib's real
  Markov inequality `MeasureTheory.mul_meas_ge_le_integral_of_nonneg`, and
  `discovery_posterior_bound_markov` re-derives the discovery bound using it — so the abstract
  `hmarkov` of the original `discovery_posterior_bound` (kept for the elementary arithmetic form) is
  replaced by a genuine theorem. `W` remains the abstract squared-Hellinger r.v. (the Hellinger
  functional / Bayes mixture stay the modelling interface, like GM Thm 7.4).

`Z : ℕ → ℝ` models `E[D_H²(P̄ₙ, P_R)]`; `ε₀` is the squared-Hellinger separation of
`EpsilonZeroBound.eps0`; `B = c·(r·log 2 + log(1/δ))` is the `EpsilonZeroBound.Tdiscover` numerator.
-/

namespace GrunwaldMehtaDiscovery

open scoped BigOperators
open MeasureTheory

/-! ## Piece 1 — the central / Bernstein condition (§3.2)

Over a finite probability space `(Ω, μ)` (a pmf, `μ ≥ 0`), for a bounded non-negative random variable
`0 ≤ X ≤ ℓmax`, the `v`-GRIP / central condition holds with `v(x) = ℓmax·x`:
`E[X²] ≤ ℓmax·E[X]`. Realizable reading (§3.2): the excess loss `X_{R'} = −log P_{R'} ≥ 0` is bounded
by `ℓmax = O(log|O|)`, so the variance is controlled by the mean — exactly the central condition that
feeds Grünwald–Mehta. Only `μ ≥ 0` is needed (not `∑ μ = 1`); the pmf reading is the intended model. -/

/-- **Central / Bernstein condition.** `E[X²] ≤ ℓmax · E[X]` for `0 ≤ X ≤ ℓmax` under non-negative
weights `μ`. Pointwise `X² ≤ ℓmax·X`, then sum with the `μ ≥ 0` weights. -/
theorem bernstein_central {Ω : Type*} [Fintype Ω] (μ X : Ω → ℝ) (ℓmax : ℝ)
    (hμ : ∀ ω, 0 ≤ μ ω) (hX0 : ∀ ω, 0 ≤ X ω) (hXm : ∀ ω, X ω ≤ ℓmax) :
    (∑ ω, μ ω * (X ω) ^ 2) ≤ ℓmax * (∑ ω, μ ω * X ω) := by
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum (fun ω _ => ?_)
  have hpt : (X ω) ^ 2 ≤ ℓmax * X ω := by nlinarith [hX0 ω, hXm ω]
  nlinarith [hμ ω, hpt]

/-! ## Piece 2 — concentration + separation ⇒ discovery (§3.3)

The imported GM rate (Thm 7.4) is modelled as `hrate : Z n ≤ B/n` on the non-negative distance
`Z n = E[D_H²(P̄ₙ, P_R)]`, with `B = c·(r·log 2 + log(1/δ))`. Past the discovery threshold the rate
is below `(δ/2)·ε₀`; Markov turns that into a tail bound `≤ δ/2`; and the posterior implication
turns *that* into posterior concentration `w(R) ≥ 1 − δ/2`. Every step except the elementary
arithmetic is a named hypothesis (GM rate, Markov, posterior-of-close). -/

/-- The GM-rate numerator `B = c·(r·log 2 + log(1/δ))` is exactly the numerator of
`EpsilonZeroBound.Tdiscover` (`Tdiscover c r δ ε₀ · ε₀² = B`). The threshold used below,
`2B/(δ ε₀)`, is the elementary-Markov discovery time; the paper's `Tdiscover ∝ 1/ε₀²` is the tighter
GM form. Both are `O(B / poly(ε₀, δ))`. -/
lemma Tdiscover_numerator (c r δ ε₀ : ℝ) (hε : ε₀ ≠ 0) :
    EpsilonZeroBound.Tdiscover c r δ ε₀ * ε₀ ^ 2 = c * (r * Real.log 2 + Real.log (1 / δ)) := by
  unfold EpsilonZeroBound.Tdiscover
  field_simp

/-- **Threshold step.** Past `n ≥ 2B/(δ ε₀)`, the GM rate `Z n ≤ B/n` gives `Z n ≤ (δ/2)·ε₀`. -/
theorem rate_threshold {Z : ℕ → ℝ} {B δ ε₀ : ℝ} {n : ℕ}
    (hδ : 0 < δ) (hε : 0 < ε₀) (hn1 : 1 ≤ n)
    (hrate : Z n ≤ B / n) (hthresh : 2 * B / (δ * ε₀) ≤ (n : ℝ)) :
    Z n ≤ δ / 2 * ε₀ := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  rw [div_le_iff₀ (mul_pos hδ hε)] at hthresh   -- 2 * B ≤ ↑n * (δ * ε₀)
  have hBn : B / n ≤ δ / 2 * ε₀ := by
    rw [div_le_iff₀ hn0]                        -- B ≤ δ / 2 * ε₀ * ↑n
    nlinarith [hthresh]
  linarith [hrate, hBn]

/-- **Markov step.** Threshold + Markov's inequality `tail ≤ Z n / ε₀` give the squared-Hellinger
tail `P(D_H² ≥ ε₀) ≤ δ/2`. (`hmarkov` is the standard Markov inequality, kept abstract.) -/
theorem markov_tail {Z : ℕ → ℝ} {B δ ε₀ tail : ℝ} {n : ℕ}
    (hδ : 0 < δ) (hε : 0 < ε₀) (hn1 : 1 ≤ n)
    (hrate : Z n ≤ B / n) (hthresh : 2 * B / (δ * ε₀) ≤ (n : ℝ))
    (hmarkov : tail ≤ Z n / ε₀) :
    tail ≤ δ / 2 := by
  have hZn := rate_threshold hδ hε hn1 hrate hthresh
  have htail : Z n / ε₀ ≤ δ / 2 := by
    rw [div_le_iff₀ hε]                          -- Z n ≤ δ / 2 * ε₀
    linarith [hZn]
  linarith [hmarkov, htail]

/-- **§3.3 discovery (assembly).** Under the imported GM fast rate (`hrate` = Grünwald–Mehta Thm 7.4),
Markov (`hmarkov`), and the separation/posterior modelling implication (`hpost` =
`posterior_of_close`: since by separation only `R` lies within `ε₀` of `P_R`, the event "mixture
within `ε₀`" — which holds with probability `≥ 1 − tail` — forces posterior weight `w ≥ 1 − tail`),
past the discovery threshold `n ≥ 2B/(δ ε₀)` the prequential posterior concentrates on the true rule:
`w(R | o_{1:n}) ≥ 1 − δ/2`. Only the threshold/Markov arithmetic is proved here; the three named
hypotheses carry the GM import and the standard probabilistic steps. -/
theorem discovery_posterior_bound {Z : ℕ → ℝ} {B δ ε₀ tail w : ℝ} {n : ℕ}
    (hδ : 0 < δ) (hε : 0 < ε₀) (hn1 : 1 ≤ n)
    (hrate : Z n ≤ B / n) (hthresh : 2 * B / (δ * ε₀) ≤ (n : ℝ))
    (hmarkov : tail ≤ Z n / ε₀) (hpost : 1 - tail ≤ w) :
    1 - δ / 2 ≤ w := by
  have htail := markov_tail hδ hε hn1 hrate hthresh hmarkov
  linarith [hpost, htail]

/-! ## Piece 2′ — discharging the Markov step with Mathlib's real Markov inequality

`discovery_posterior_bound` above takes the Markov tail bound as the abstract hypothesis
`hmarkov : tail ≤ Z n / ε₀`. Here we **discharge it with a genuine theorem**: model the randomness
measure-theoretically — a measure space `(Ω, μ)` and a non-negative integrable random variable
`W : Ω → ℝ` standing for the squared-Hellinger distance `D_H²(P̄ₙ, P_R)` of the random observation
sequence — and apply Mathlib's **`MeasureTheory.mul_meas_ge_le_integral_of_nonneg`** (the real-valued
Bochner-integral Markov inequality). Given the GM expectation bound `E[W] = ∫ W ∂μ ≤ B/n`, this yields
the tail bound `μ.real {ω | ε₀ ≤ W ω} ≤ B/(n·ε₀)` as a *proved* fact, not an assumption.

### Now proved vs. still the interface
* PROVED: the Markov tail (`markov_tail_real`) — a real application of Mathlib's Markov inequality,
  replacing the abstract `hmarkov`.
* STILL the modelling interface (unchanged): `W` is *the* squared-Hellinger r.v. (we do not build the
  Hellinger functional or the Bayes mixture `P̄ₙ` — that stays the interface, like GM Thm 7.4);
  `hrate : ∫ W ∂μ ≤ B/n` is **GM Thm 7.4** (the imported black box); and `hpost` =
  `posterior_of_close`, the separation ⇒ posterior modelling implication. -/

/-- **Markov tail (real Markov inequality).** For a non-negative integrable `W` with expectation
`∫ W ∂μ ≤ B/n`, the tail mass past `ε₀` obeys `μ{ω | ε₀ ≤ W ω} ≤ B/(n·ε₀)`. A direct application of
`MeasureTheory.mul_meas_ge_le_integral_of_nonneg` (`ε₀·μ.real{ε₀ ≤ W} ≤ ∫ W`) then dividing by `ε₀`.
This is the genuine Markov step, replacing the abstract `hmarkov` of `discovery_posterior_bound`. -/
theorem markov_tail_real {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (W : Ω → ℝ)
    {B ε₀ : ℝ} {n : ℕ}
    (hnn : 0 ≤ᵐ[μ] W) (hint : Integrable W μ) (hε : 0 < ε₀)
    (hrate : (∫ ω, W ω ∂μ) ≤ B / n) :
    (μ {ω | ε₀ ≤ W ω}).toReal ≤ B / ((n : ℝ) * ε₀) := by
  have hmk := mul_meas_ge_le_integral_of_nonneg hnn hint ε₀
  have h1 : ε₀ * (μ {ω | ε₀ ≤ W ω}).toReal ≤ B / n := le_trans hmk hrate
  have h2 : (μ {ω | ε₀ ≤ W ω}).toReal ≤ (B / n) / ε₀ :=
    (le_div_iff₀ hε).mpr (by rw [mul_comm]; exact h1)
  rwa [div_div] at h2

/-- **§3.3 discovery with the Markov step discharged.** Same conclusion as `discovery_posterior_bound`
— posterior concentration `w(R) ≥ 1 − δ/2` past the threshold `n ≥ 2B/(δ ε₀)` — but the Markov tail
is now a *proved* application of Mathlib's Markov inequality (`markov_tail_real`) instead of the
abstract `hmarkov`. The only remaining named hypotheses are `hrate` (GM Thm 7.4, the imported rate on
`∫ W ∂μ`) and `hpost` (`posterior_of_close`, the separation ⇒ posterior implication); `W` abstractly
denotes the squared-Hellinger r.v. -/
theorem discovery_posterior_bound_markov {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (W : Ω → ℝ)
    {B δ ε₀ w : ℝ} {n : ℕ}
    (hδ : 0 < δ) (hε : 0 < ε₀) (hn1 : 1 ≤ n)
    (hnn : 0 ≤ᵐ[μ] W) (hint : Integrable W μ)
    (hrate : (∫ ω, W ω ∂μ) ≤ B / n)
    (hthresh : 2 * B / (δ * ε₀) ≤ (n : ℝ))
    (hpost : 1 - (μ {ω | ε₀ ≤ W ω}).toReal ≤ w) :
    1 - δ / 2 ≤ w := by
  have htail := markov_tail_real μ W hnn hint hε hrate
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  rw [div_le_iff₀ (mul_pos hδ hε)] at hthresh
  have hBn : B / ((n : ℝ) * ε₀) ≤ δ / 2 := by
    rw [div_le_iff₀ (mul_pos hn0 hε)]; nlinarith [hthresh]
  linarith [hpost, htail, hBn]

end GrunwaldMehtaDiscovery
