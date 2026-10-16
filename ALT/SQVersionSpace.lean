module

public import Learning.SQBounds


/-!
# Positive arithmetic core of SQ version-space pruning ([SQ] §3.4 / §4(b) / Appendix A)

Provenance: [SQ], §3.4 (statistical dimension `d_SQ` +
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
The arithmetic the SQ model shares — `PolyBounded`, `candidates_polyBounded` and the two
`truth_survives_pruning` lemmas — lives in `Learning/SQBounds.lean`; the impostor lemmas
stay here.

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
  is the [Discovery] Bayes-mixture redundancy argument and stays in prose. We prove only the
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


@[expose] public section

namespace ALT

open SQBounds Filter

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

/-! ### Window-noise refinement of the `2τ` geometry ([SQ] §3.1)

The window-sufficiency assumption (W) of [SQ] §3.1 — "the window determines the next observation
under R" — is the *determinism* of the one-step predictor `f_R`.  It weakens gracefully to a
**window-noise rate** `η := μ(o_{t+1} ≠ f_R(w_t))`, the Bayes error of the predictor under the
invariant measure (`W` is `η = 0`). The realized answer is then the *joint* mean `a = 𝔼_μ φ(w,
o_next)`, which the empirical time-average concentrates on; the *deterministic* truth is
`predR = 𝔼_μ φ(w, f_R(w))`, and the two differ by the noise gap `|a − predR| ≤ 2η` (the query is
`[−1,1]`-valued; `SQOracle.noise_gap_integral`).  The two lemmas below are the noisy siblings of
`truth_survives_pruning` / `separated_impostor_pruned`: the deterministic truth survives the
*unchanged* `2τ`-pruning rule exactly when the window-noise budget `2η ≤ τ` holds, and a separated
impostor picks up the matching `+2η` slack.  Both specialize to the noiseless lemmas at `η = 0`. -/

/-- **T2b-noisy — separated impostors are pruned, with noise slack** ([SQ] §3.1, the window-noise
refinement of `separated_impostor_pruned`).  A candidate `predR'` whose predicted mean is
`> 3τ + 2η`-separated from the deterministic truth `predR` still deviates from the empirical answer
by `|predR' − emp| > 2τ`, so it is pruned.  The separation threshold picks up exactly the `+2η`
window-noise slack over the noiseless `3τ`.  At `η = 0` this is `separated_impostor_pruned`. -/
theorem separated_impostor_pruned_noisy
    (predR predR' a emp τ η : ℝ)
    (hconc : |emp - a| ≤ τ) (hnoise : |a - predR| ≤ 2 * η)
    (hsep : 3 * τ + 2 * η < |predR' - predR|) :
    2 * τ < |predR' - emp| := by
  have h1 : |predR' - predR| ≤ |predR' - emp| + |emp - predR| := abs_sub_le predR' emp predR
  have h2 : |emp - predR| ≤ |emp - a| + |a - predR| := abs_sub_le emp a predR
  linarith

end ALT
