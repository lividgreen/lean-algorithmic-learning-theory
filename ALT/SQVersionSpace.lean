import ALT.ParityCounterexample
import Mathlib

-- Tier-1 formal check, not Mathlib-destined: opt out of the house-style header linter.
set_option linter.style.header false

/-!
# Positive arithmetic core of SQ version-space pruning (Paper III §3.4 / §4(b) / Appendix A)

Provenance: `03_polynomial_convergence_under_SQ.md`, §3.4 (statistical dimension `d_SQ` +
Assumption A), §4 step (b) (SQ-based enumeration of `M_T`), and Appendix A (the BFJKMR →
prequential adaptation: "the version-space bound", "the SQ handle", "the truth survives").

This is the POSITIVE complement to `ALT/ParityCounterexample.lean` (FV-A3): there the modeled
`d_SQ` is exponential and `PolyBounded` *fails*; here, under Assumption A (`d_SQ = poly(r)`) plus
the modeled BFJKMR envelope, the SAME `PolyBounded` notion *succeeds* and delivers the `poly(r)`
candidate set that Theorem 4.1 (ii,iii) consumes, together with the two-sided soundness of the
`2τ` pruning rule.

Status: PROVED as pure real-arithmetic / asymptotic statements. This is the *arithmetic core* of
§4(b) and Appendix A only.

## What this DOES establish
* `candidates_polyBounded` (Appendix A "version-space bound", §4 step (b)): if `d_SQ` is
  `PolyBounded` (Assumption A) and the version space is bounded by the modeled BFJKMR envelope
  `candidates r ≤ A · (d_SQ r)^m`, then the candidate set is itself `PolyBounded` — `poly(r)`. This
  is exactly the same `PolyBounded` predicate parity fails in FV-A3, here closing positively.
* `truth_survives_pruning` (Appendix A claim 1, "the truth survives"): the rule prunes any `R'`
  whose predicted statistic deviates from the empirical answer by `> 2τ`. If the empirical answer
  is within `τ` of the truth's mean (Birkhoff + concentration, modeled as the hypothesis `hemp`),
  the truth's own deviation is `≤ 2τ` — so the truth is NEVER pruned.
* `separated_impostor_pruned` (Appendix A, "the SQ handle" / pruning is effective): a candidate
  `R'` whose mean is `> 3τ`-separated from the truth IS pruned — its deviation from the empirical
  answer exceeds the `2τ` threshold. Together with `truth_survives_pruning` this is the soundness
  of SQ-pruning: it keeps the truth and removes every well-separated impostor.

## What this does NOT establish (stays in prose; no overclaiming)
* Not the SQ statistical dimension `d_SQ`, the SQ oracle, the concept class `M`, or the BFJKMR
  characterization itself: `candidates`, `dSQ`, and the envelope `A · d_SQ^m` are bare real
  functions standing in for the version-space machinery. The `2^{poly(log d_SQ)}·poly(k)` bound of
  Appendix A is MODELED as the premise `candidates r ≤ A · (d_SQ r)^m`.
* Not the §3 single-trajectory → SQ-oracle reduction, ergodicity (E1), Birkhoff, or the
  `O(1/√n)` query estimate. The "empirical answer is within `τ` of the truth's mean" fact is taken
  as the hypothesis `hemp`, not derived.
* Not the negligible-pruned-mass / competitor-decay half of Appendix A's soundness (claim 2): that
  is the Paper II Bayes-mixture redundancy argument and stays in prose. We prove only the
  *geometric* half — truth retained, separated impostors removed.
* Not Theorem 4.1's poly-time accounting (that is FV-B1, `PolyTimeAccounting.lean`); here we supply
  only the `poly(r)` size of the retained support that accounting consumes.

## Hypotheses: paper-stated vs added/strengthened
* Paper-stated / faithful: Assumption A as `PolyBounded d_SQ` (`∃ C, k`, §3.4); the version space
  `≤ 2^{poly(log d_SQ)}·poly(k) = poly(r)` modeled as a polynomial-in-`d_SQ` envelope
  (`A · d_SQ^m`); the `2τ` separation threshold of the SQ handle (Appendix A, `|E_{R'} − E_R| > 2τ`
  separates); the asymptotic regime `r → ∞` (`Filter.atTop`).
* Added/strengthened (flagged): a CONCRETE polynomial envelope with explicit constant `A ≥ 0` and
  natural-number exponent `m` in place of `2^{poly(log d_SQ)}·poly(k)`; eventual nonnegativity of
  `d_SQ` (`hdpos`, automatic for a genuine dimension); the impostor separation taken at `3τ`
  (strictly inside the `2τ` prune threshold by a `τ` margin, matching "well-separated").
-/

namespace SQVersionSpace

open ParityCounterexample Filter

/-- **T1 — version-space bound** (§3.4 / §4 step (b) / Appendix A "the version-space bound"):
if the statistical dimension `dSQ` is polynomially bounded in `r` (Assumption A) and the candidate
set / version space is bounded by a polynomial in `dSQ` (the modeled BFJKMR envelope
`candidates ≤ A · dSQ^m`), then the candidate set is itself `poly(r)`.

This is the POSITIVE complement to `ParityCounterexample.dSQ_not_polyBounded`: the very same
`PolyBounded` notion that parity fails, here delivering the `poly(r)` candidate set that
Theorem 4.1 (ii,iii) needs. -/
theorem candidates_polyBounded
    (dSQ candidates : ℝ → ℝ)
    (hd : PolyBounded dSQ)
    (A : ℝ) (m : ℕ) (hA : 0 ≤ A)
    (hcand : ∀ᶠ r in atTop, candidates r ≤ A * (dSQ r) ^ m)
    (hdpos : ∀ᶠ r in atTop, 0 ≤ dSQ r) :
    PolyBounded candidates := by
  obtain ⟨C, k, hCk⟩ := hd
  refine ⟨A * C ^ m, k * m, ?_⟩
  filter_upwards [hcand, hdpos, hCk] with r hcr hdr hCkr
  have hstep : (dSQ r) ^ m ≤ (C * r ^ k) ^ m := pow_le_pow_left₀ hdr hCkr m
  have hmain : candidates r ≤ A * (C * r ^ k) ^ m :=
    hcr.trans (mul_le_mul_of_nonneg_left hstep hA)
  have heq : A * C ^ m * r ^ (k * m) = A * (C * r ^ k) ^ m := by
    rw [mul_pow, ← pow_mul]; ring
  rw [heq]; exact hmain

/-- **T2a — the truth survives** (Appendix A claim 1): the pruning rule drops any candidate whose
predicted statistic deviates from the empirical answer by `> 2τ`. If the empirical answer `emp` is
within `τ` of the truth's mean `predR` (Birkhoff + concentration, modeled as `hemp`), then the
truth's own deviation `|predR − emp|` is `≤ 2τ` — so the truth is NEVER pruned. -/
theorem truth_survives_pruning
    (predR emp τ : ℝ) (hτ : 0 ≤ τ)
    (hemp : |emp - predR| ≤ τ) :
    |predR - emp| ≤ 2 * τ := by
  rw [abs_sub_comm]; linarith

/-- **T2b — separated impostors are pruned** (Appendix A "the SQ handle"; pruning is effective): a
candidate `R'` whose predicted mean `predR'` is `> 3τ`-separated from the truth `predR` IS pruned —
its deviation `|predR' − emp|` from the empirical answer exceeds the `2τ` threshold. Together with
`truth_survives_pruning` this is the soundness of SQ-pruning: keep the truth, remove every
well-separated impostor. -/
theorem separated_impostor_pruned
    (predR predR' emp τ : ℝ)
    (hemp : |emp - predR| ≤ τ)
    (hsep : 3 * τ < |predR' - predR|) :
    2 * τ < |predR' - emp| := by
  have h1 : |predR' - predR| ≤ |predR' - emp| + |emp - predR| := abs_sub_le predR' emp predR
  linarith

end SQVersionSpace
