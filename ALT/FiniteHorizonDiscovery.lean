/-
Copyright (c) 2026 Mykola Palamarchuk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mykola Palamarchuk
-/
module

public import ALT.BirkhoffTool
public import ALT.SQAlgorithm

-- Formal-check file, not Mathlib-destined: opt out of the house-style header linter.
set_option linter.style.header false
set_option linter.style.longLine false
-- `algorithm_discovery_of_mixingTo` calls `SQAlgorithm.algorithm_discovery`, whose own
-- `[DecidableEq ι]` is consumed by machinery internal to that theorem's proof (`Finset.erase`,
-- via `DeterministicDiscovery.deterministic_discovery`) without appearing in either theorem's own
-- conclusion type — the identical false positive `SQAlgorithm.lean` already disables this for.
set_option linter.unusedDecidableInType false

/-!
# The end-to-end finite-horizon guarantee ([SQ] §3.3, §4 Theorem 4.1(i))

Provenance: [SQ] §3.3 "When does the reduction work?" (the finite-horizon paragraph: a schedule
oracle proved from `MixingHoeffdingTo` at a horizon `N`, without covering every sample size) and
§4 Theorem 4.1(i) (the pruned posterior's sample complexity). Composes two independently-landed
theorems that neither cite nor import each other: `BirkhoffTool.empirical_isSQOracle_of_mixingTo`
(the finite-horizon mixing oracle over a schedule, off an event of measure `≤ δ`) and
`SQAlgorithm.algorithm_discovery` (Theorem 4.1(i) for the pruned algorithm, assembled from
[Discovery]'s discovery theorem by posterior monotonicity under the schedule's own oracle-closeness
hypothesis `hclose`). `ALT/BirkhoffTool.lean` imports `ALT.SQOracle`; `ALT/SQAlgorithm.lean` imports
the discovery/supermartingale stack; neither is upstream of the other, so the composition is a new,
third module rather than an addition to either parent.

## What is proved here (machine-checked, axioms = the standard triple)

* `algorithm_discovery_of_mixingTo` — on trajectories where the truth `iR` is realizable and
  `ε₀`-separated from every competitor at every step below the discovery horizon `m`, the event that
  the pruned posterior on `iR` still fails to reach `1 − δd/2` after `m` steps has measure `≤ δ`,
  `δ` being the oracle's own confidence budget for a schedule `Qs` answered from `n ≤ N` steps of a
  single orbit segment under `MixingHoeffdingTo N` at one shared mixing constant `c`.

  **The trajectory-wise hypotheses are conditioned inside the event, not quantified over every
  trajectory.** The natural-looking alternative — realizability and separation as `∀ ω` premises,
  concluding a bare `μ {ω | ¬ concentration} ≤ ENNReal.ofReal δ` — is unsatisfiable: at `s = 0`,
  realizability would demand `pred iR 0 (empty window) = ω 0` for *every* `ω`, which fails as soon as
  `X` has two elements, making that theorem true, empty, and empty invisibly. Conditioning the event
  on the hypotheses avoids this, needs no `∀ᵐ` machinery or measurability, and is the primitive a
  `μ`-a.e. consumer form (hypotheses a.e., conclusion a bare failure bound) would follow from in one
  line — not given here, since nothing yet consumes it.

  **The bridge is a pure inclusion, with one named identification and no containment side
  condition.** `SQObjects.IsSQOracle` quantifies over the *whole* query type, so instantiating
  `SQAlgorithm.algorithm_discovery` at the query type `↥Qs` — the schedule's own subtype — makes its
  `hclose` hypothesis an immediate specialization of the oracle predicate: every `sched t : Finset
  ↥Qs` already sits inside that universal. What the bridge does need, and states as the hypothesis
  `hstat`, is the modelling identification that each scheduled query's declared answer is the truth's
  own statistic (`stat iR φ = tru ↑φ`) — the step [SQ] §3.2 makes in prose. The proof is then: the
  event in the conclusion is a subset of the oracle's own failure event (a trajectory in the smaller
  event but outside the oracle's failure event would satisfy `algorithm_discovery`'s hypotheses via
  the bridge above, and hence its conclusion, contradicting the smaller event's own third conjunct);
  `measure_mono` closes the bound from `empirical_isSQOracle_of_mixingTo`.

  **Two sample counts appear, and nothing relates them.** `n`, the size at which the whole schedule
  is answered from a single orbit segment, carries `n ≤ N`; `m`, the step count the pruned posterior
  is bounded at, carries only [Discovery]'s own discovery threshold `hT`. So the horizon bounds the
  *schedule's answering*, never the *run*: a run may be arbitrarily longer than the horizon its
  environment is representative below, because the discovery half of Theorem 4.1 consumes no mixing
  at all.

## What is deliberately NOT in the statement or in scope

* **`n ≤ m`** — that the oracle's sample sits inside the prefix the learner has actually observed —
  is a modelling reading of this composition, not a mathematical hypothesis either parent needs: the
  theorem is true without it, and it would be an unused binder here. Read it as intended alongside
  the statement: the schedule is answered from a prefix of the same trajectory the discovery half
  runs over.
* **Theorem 4.1 parts (ii)–(iv)** are not composed: read at [SQ]'s own proof sketch, part (i) is the
  only part whose argument touches the mixing hypothesis at all — (ii)/(iii) are per-step cost, (iv)
  is `L`-independence, and neither consumes the oracle's accuracy.
* **The `μ`-a.e. consumer form** — see above; it is a one-line corollary of the conditioned form, not
  given because nothing here consumes it.
-/


@[expose] public section

namespace FiniteHorizonDiscovery

open MeasureTheory SQMixtureSupermartingale SQOracle

/-- **The end-to-end finite-horizon guarantee** ([SQ] §3.3, §4 Theorem 4.1(i)): composing the
finite-horizon mixing oracle (`BirkhoffTool.empirical_isSQOracle_of_mixingTo`) with Theorem 4.1(i)
for the pruned algorithm (`SQAlgorithm.algorithm_discovery`). See the module docstring for the
inclusion argument, the conditioned-event reading, and what stays out of scope. -/
theorem algorithm_discovery_of_mixingTo
    {X : Type*} [DecidableEq X] [Fintype X] [MeasurableSpace X]
    {ι : Type*} [Fintype ι] [DecidableEq ι] {Q : Type*}
    (μ : Measure (ℕ → X)) [IsProbabilityMeasure μ]
    (Qs : Finset Q) (hQs : Qs.Nonempty)
    (Z : Q → ℕ → (ℕ → X) → ℝ) (tru : Q → ℝ) (c : ℝ) (N n : ℕ) (τ δ : ℝ)
    (pred : ι → (s : ℕ) → (Fin s → X) → X) (stat : ι → ↥Qs → ℝ)
    (sched : ℕ → Finset ↥Qs) (w : ι → ℝ) (iR : ι) (k m : ℕ) (δd ε₀ : ℝ)
    (hmix : ∀ φ ∈ Qs, BirkhoffTool.MixingHoeffdingTo N μ (Z φ) (tru φ) c) (hc : 0 < c)
    (hn1 : 1 ≤ n) (hnN : n ≤ N) (hτ : 0 < τ) (hδ0 : 0 < δ)
    (hn : (2 * c / τ ^ 2) * Real.log (2 * (Qs.card : ℝ) / δ) ≤ (n : ℝ))
    (hstat : ∀ φ : ↥Qs, stat iR φ = tru ↑φ)
    (hw : ∀ i, 0 ≤ w i) (hwR : w iR = (2 : ℝ) ^ (-(k : ℝ))) (hsumw : ∑ i, w i ≤ 1)
    (hδd : 0 < δd) (hε : 0 < ε₀)
    (hT : ((k : ℝ) * Real.log 2 + Real.log (2 / δd)) / (2 * ε₀) ≤ (m : ℝ)) :
    μ {ω | (∀ s, pred iR s (fun j => ω j) = ω s)
            ∧ (∀ i, i ≠ iR → ∀ t ∈ Finset.range m,
                 ε₀ ≤ BayesRedundancy.sqHellinger (fun x => if x = ω t then 1 else 0)
                        (fun x => if pred i t (fun j => ω j) = x then (1 : ℝ) else 0))
            ∧ ¬ (1 - δd / 2 ≤ w iR * L (detFactor pred) iR m ω
                  / ∑ i ∈ SQAlgorithm.alive pred stat (fun φ => empiricalMean (Z ↑φ) n ω) τ sched
                        Finset.univ m ω, w i * L (detFactor pred) i m ω)}
      ≤ ENNReal.ofReal δ := by
  have hcov := BirkhoffTool.empirical_isSQOracle_of_mixingTo μ Qs hQs Z tru c N n τ δ
    hmix hc hn1 hnN hτ hδ0 hn
  refine le_trans (measure_mono ?_) hcov
  intro ω hω
  simp only [Set.mem_ofPred_eq] at hω
  obtain ⟨hreal, hsep, hnconc⟩ := hω
  simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, SQObjects.IsSQOracle]
  intro hosc
  apply hnconc
  have hclose : ∀ t, ∀ φ ∈ sched t, |empiricalMean (Z ↑φ) n ω - stat iR φ| ≤ τ := by
    intro t φ _
    rw [hstat φ]
    exact hosc φ
  exact SQAlgorithm.algorithm_discovery pred stat (fun φ : ↥Qs => empiricalMean (Z ↑φ) n ω) τ hτ.le
    sched w ω iR hw k hwR hsumw hreal hclose δd ε₀ hδd hε m hsep hT

/-- info: 'FiniteHorizonDiscovery.algorithm_discovery_of_mixingTo' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms algorithm_discovery_of_mixingTo

end FiniteHorizonDiscovery
