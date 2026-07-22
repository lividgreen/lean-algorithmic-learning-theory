/-
Copyright (c) 2026 Mykola Palamarchuk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mykola Palamarchuk
-/
import ALT.DeterministicDiscovery
import ALT.SQMixtureSupermartingale
import ALT.SQPredictiveTransfer
import ALT.SQVersionSpace

-- Formal-check file, not Mathlib-destined: opt out of the house-style linters (long defs/lines).
set_option linter.style.header false
set_option linter.style.longLine false
-- `posterior_concentration_transfer` carries `[DecidableEq ι]` for the `deterministic_discovery`
-- proof (Finset.erase over `ι`), though it is absent from the Dirac-pmf conclusion type; the
-- upstream `DeterministicDiscovery.lean` disables this same linter for the same reason.
set_option linter.unusedDecidableInType false

/-!
# The prequential-MDL-with-SQ-pruning algorithm as a Lean object ([SQ] §4 / App A, FV-K)

Provenance: [SQ], §4 Theorem 4.1 + proof sketch (a)–(c) and
Appendix A "The adaptation". The algorithm carries a posterior over deterministic candidate rules;
at each step it (Bayes-)filters candidates inconsistent with the observed symbol, and on scheduled
queries it prunes every candidate whose predicted statistic deviates from the oracle answer by more
than `2τ`. FV-K makes THIS algorithm a genuine Lean object and proves the identification theorems
that tie the standing FV artifacts to it — closing the ledger's outstanding identifications:
* which `pred`/`g` the algorithm emits (FV-I) — `alive_mass_eq_Z_det`;
* App-A Claim 1 ("the truth survives") for the algorithm itself — `truth_survives`, with the
  FV-A4 converse `separated_impostor_pruned_alg`;
* which `ε_t` FV-H's `accumulated_perturbation_le` consumes — `algorithm_damage_le`.

This file is **Finset-level**: the object is a family of `Finset ι` operations (Bayes consistency
filter + SQ pruning), with NO filtration/measurability content. The measure-theoretic inputs enter
only as the (already-proved) FV-E/FV-I/FV-H artifacts it cites.

## Constants (matched to FV-A4 `SQVersionSpace.lean` exactly)
* prune threshold `2τ` (`sqPrune` keeps `|stat i φ − oracleAns φ| ≤ 2τ`) — FV-A4's `2τ` rule;
* truth-survival closeness `|oracleAns φ − stat iR φ| ≤ τ` (the `emp − predR` order of FV-A4's
  `hemp`, which is exactly `SQOracle.empirical_isSQOracle`'s `|emp − tru| ≤ τ` at `answer = oracleAns`,
  `truth = stat iR`);
* impostor separation `3τ < |stat j φ − stat iR φ|` — FV-A4's `separated_impostor_pruned` `hsep`.

## Schedule encoding
`sched : ℕ → Finset Q`, with `sched t` the query set active by step `t`; the per-step alive set is
`alive … t ω = sqPrune stat oracleAns τ (sched t) (consistent pred cands t ω)` — sq-prune (over the
queries scheduled by `t`) of the time-`t` Bayes-consistent set.

## What this DOES establish
* `consistent`, `sqPrune`, `alive`, `prunedAt` — the algorithm as a compositional `Finset` object.
* `alive_mass_eq_Z_det` (FV-I identification): the UNpruned Bayes-consistent mass is FV-I's mixture,
  `∑_{consistent} w = Z cands w (detFactor pred)` — this is the "identify `g` with the algorithm" item.
* `truth_survives` (App A Claim 1 for the object): a realizable, `τ`-close truth index stays in
  `alive … t ω` for every `t` (reusing FV-A4's `truth_survives_pruning` at the `2τ` rule).
* `separated_impostor_pruned_alg` (FV-A4 converse for the object): a candidate `3τ`-separated from
  the truth on a scheduled query is pruned (reusing FV-A4's `separated_impostor_pruned`).
* `algorithm_damage_le` (FV-H `ε_t` identification): FV-H's accumulated predictive damage
  instantiated at the algorithm's OWN step families — survivors `alive … (t+1)` vs the step-`t`
  pruned-away set `prunedAt … t` — so `ε_t` is the algorithm's literal normalized pruned fraction.
* `posterior_concentration_transfer`: the algorithm's Dirac pmf instantiates [Discovery]'s
  `deterministic_discovery`, giving Theorem-3.1 concentration for the UNpruned Bayes posterior.
* `algorithm_discovery` (**Theorem 4.1(i) for the PRUNED algorithm**): the pruned posterior on the
  truth `iR` is `≥ 1 − δ/2`. The composition is MONOTONICITY, not "concentration ∘ damage": the
  pruned posterior is the Bayes posterior with the summation restricted to `alive n ⊆ cands`; since
  `iR ∈ alive n` (`truth_survives`), shrinking the summation set only shrinks the denominator, so the
  pruned quotient DOMINATES the unpruned one, which is `≥ 1 − δ/2` by
  `posterior_concentration_transfer`. The damage bound (`algorithm_damage_le`) keeps its SEPARATE
  role — bounding the predictive distribution's perturbation — and does NOT enter part (i).
  ([SQ] §4(i) writes `w(R ∣ o_{1:T}) ≥ 1 − δ`; the machinery delivers the stronger `1 − δ/2`,
  matching [Discovery] Theorem 3.1's form — kept as `1 − δ/2`.)

## What this does NOT establish (out of scope here; no overclaiming)
* Not the query-schedule CONSTRUCTION for a concrete class (BFJKMR enumeration): `sched`
  and `stat`/`oracleAns` are abstract data.
* Not the collector / `evaln` / `H_T` epiplexity layer (Prop 2.2 — see `Collector.lean`).
* Not the per-step COST accounting beyond FV-B1's arithmetic (Lemma 4.2 stays prose).
* Not the countable candidate class (`cands` is a `Finset`; `algorithm_discovery` instantiates
  `cands = Finset.univ`, matching `deterministic_discovery`'s full-`Fintype ι` normalizer).
-/

namespace SQAlgorithm

open SQMixtureSupermartingale

variable {X : Type*} [DecidableEq X] {ι : Type*} {Q : Type*}

/-- **Bayes consistency filter** (§4 sketch (a)): the candidates whose deterministic rule predicts
every observed symbol up to time `t`. -/
def consistent (pred : ι → (s : ℕ) → (Fin s → X) → X) (cands : Finset ι) (t : ℕ) (ω : ℕ → X) :
    Finset ι :=
  cands.filter (fun i => ∀ s ∈ Finset.range t, pred i s (fun k => ω k) = ω s)

/-- **SQ pruning step** (§4 sketch (b) / App A "the SQ handle"): from `S`, keep only the candidates
whose statistic is within `2τ` of the oracle answer on every scheduled query `φ ∈ Qs`. -/
noncomputable def sqPrune (stat : ι → Q → ℝ) (oracleAns : Q → ℝ) (τ : ℝ) (Qs : Finset Q)
    (S : Finset ι) : Finset ι :=
  S.filter (fun i => ∀ φ ∈ Qs, |stat i φ - oracleAns φ| ≤ 2 * τ)

/-- **The per-step alive set**: sq-prune (over the queries scheduled by time `t`, `sched t`) of the
time-`t` Bayes-consistent set. -/
noncomputable def alive (pred : ι → (s : ℕ) → (Fin s → X) → X) (stat : ι → Q → ℝ)
    (oracleAns : Q → ℝ) (τ : ℝ) (sched : ℕ → Finset Q) (cands : Finset ι) (t : ℕ) (ω : ℕ → X) :
    Finset ι :=
  sqPrune stat oracleAns τ (sched t) (consistent pred cands t ω)

/-- **The step-`t` pruned-away set**: candidates alive at `t` but removed by step `t+1`. -/
noncomputable def prunedAt [DecidableEq ι] (pred : ι → (s : ℕ) → (Fin s → X) → X)
    (stat : ι → Q → ℝ) (oracleAns : Q → ℝ) (τ : ℝ) (sched : ℕ → Finset Q) (cands : Finset ι)
    (t : ℕ) (ω : ℕ → X) : Finset ι :=
  alive pred stat oracleAns τ sched cands t ω \ alive pred stat oracleAns τ sched cands (t + 1) ω

/-- **FV-I identification** ("identify `g` with the algorithm"): the UNpruned Bayes-consistent
posterior mass is exactly FV-I's mixture `Z cands w (detFactor pred)` at time `t`. From
`L_det_eq_indicator` (each deterministic likelihood is the consistency indicator) and
`Finset.sum_filter`. -/
theorem alive_mass_eq_Z_det (pred : ι → (s : ℕ) → (Fin s → X) → X) (cands : Finset ι)
    (w : ι → ℝ) (t : ℕ) (ω : ℕ → X) :
    ∑ i ∈ consistent pred cands t ω, w i = Z cands w (detFactor pred) t ω := by
  simp only [Z, consistent]
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [L_det_eq_indicator]
  split_ifs <;> simp

/-- **App A Claim 1 for the object — the truth survives.** A truth index `iR ∈ cands` that is (a)
realizable (`pred iR` predicts every symbol) and (b) `τ`-close to every scheduled oracle answer
(`|oracleAns φ − stat iR φ| ≤ τ`, the FV-A4 `hemp` order, supplied w.h.p. by
`SQOracle.empirical_isSQOracle`) is in `alive … t ω` for every `t`. Reuses FV-A4's
`truth_survives_pruning` for the `τ ⇒ 2τ` step. -/
theorem truth_survives (pred : ι → (s : ℕ) → (Fin s → X) → X) (stat : ι → Q → ℝ)
    (oracleAns : Q → ℝ) (τ : ℝ) (hτ : 0 ≤ τ) (sched : ℕ → Finset Q) (cands : Finset ι)
    (ω : ℕ → X) (iR : ι) (hmem : iR ∈ cands)
    (hreal : ∀ s, pred iR s (fun k => ω k) = ω s)
    (hclose : ∀ t, ∀ φ ∈ sched t, |oracleAns φ - stat iR φ| ≤ τ) :
    ∀ t, iR ∈ alive pred stat oracleAns τ sched cands t ω := by
  intro t
  simp only [alive, sqPrune, consistent, Finset.mem_filter]
  refine ⟨⟨hmem, fun s _ => hreal s⟩, fun φ hφ => ?_⟩
  exact SQVersionSpace.truth_survives_pruning (stat iR φ) (oracleAns φ) τ hτ (hclose t φ hφ)

/-- **FV-A4 converse for the object — separated impostors are pruned.** A candidate `j` whose
statistic is `3τ`-separated from the truth `iR` on some scheduled query `φ ∈ sched t`, while the
oracle is `τ`-close to the truth there, is NOT in `alive … t ω` — its deviation exceeds the `2τ`
threshold (FV-A4's `separated_impostor_pruned`). -/
theorem separated_impostor_pruned_alg (pred : ι → (s : ℕ) → (Fin s → X) → X) (stat : ι → Q → ℝ)
    (oracleAns : Q → ℝ) (τ : ℝ) (sched : ℕ → Finset Q) (cands : Finset ι) (t : ℕ) (ω : ℕ → X)
    (iR j : ι) (φ : Q) (hφ : φ ∈ sched t)
    (hemp : |oracleAns φ - stat iR φ| ≤ τ)
    (hsep : 3 * τ < |stat j φ - stat iR φ|) :
    j ∉ alive pred stat oracleAns τ sched cands t ω := by
  intro hin
  simp only [alive, sqPrune, Finset.mem_filter] at hin
  have hle := hin.2 φ hφ
  have hgt := SQVersionSpace.separated_impostor_pruned (stat iR φ) (stat j φ) (oracleAns φ) τ hemp hsep
  linarith

/-- **FV-H `ε_t` identification.** FV-H's accumulated one-step predictive damage
(`SQPredictiveTransfer.accumulated_perturbation_le`) instantiated at the algorithm's OWN step
families: survivors `alive … (t+1) ω` and the step-`t` pruned-away set `prunedAt … t ω`. The bound's
`ε_t = (∑ prunedAt … t) / (∑ alive … (t+1) ∪ prunedAt … t)` is the algorithm's literal normalized
pruned fraction — turning FV-H's abstract accounting into a statement about THE algorithm. -/
theorem algorithm_damage_le [DecidableEq ι] (pred : ι → (s : ℕ) → (Fin s → X) → X)
    (stat : ι → Q → ℝ) (oracleAns : Q → ℝ) (τ : ℝ) (sched : ℕ → Finset Q) (cands : Finset ι)
    (ω : ℕ → X) (n : ℕ) (outs : Finset X) (u : ℕ → ι → ℝ) (p : ℕ → ι → X → ℝ)
    (hu : ∀ t ∈ Finset.range n, ∀ i ∈ alive pred stat oracleAns τ sched cands (t + 1) ω
        ∪ prunedAt pred stat oracleAns τ sched cands t ω, 0 ≤ u t i)
    (hp0 : ∀ t ∈ Finset.range n, ∀ i ∈ alive pred stat oracleAns τ sched cands (t + 1) ω
        ∪ prunedAt pred stat oracleAns τ sched cands t ω, ∀ x ∈ outs, 0 ≤ p t i x)
    (hp1 : ∀ t ∈ Finset.range n, ∀ i ∈ alive pred stat oracleAns τ sched cands (t + 1) ω
        ∪ prunedAt pred stat oracleAns τ sched cands t ω, ∑ x ∈ outs, p t i x = 1)
    (hV : ∀ t ∈ Finset.range n, 0 < ∑ i ∈ alive pred stat oracleAns τ sched cands (t + 1) ω, u t i) :
    ∑ t ∈ Finset.range n,
        ∑ x ∈ outs,
          |(∑ i ∈ alive pred stat oracleAns τ sched cands (t + 1) ω, u t i * p t i x)
                / (∑ i ∈ alive pred stat oracleAns τ sched cands (t + 1) ω, u t i)
            - (∑ i ∈ alive pred stat oracleAns τ sched cands (t + 1) ω
                  ∪ prunedAt pred stat oracleAns τ sched cands t ω, u t i * p t i x)
                / (∑ i ∈ alive pred stat oracleAns τ sched cands (t + 1) ω
                    ∪ prunedAt pred stat oracleAns τ sched cands t ω, u t i)|
      ≤ 2 * ∑ t ∈ Finset.range n,
              (∑ i ∈ prunedAt pred stat oracleAns τ sched cands t ω, u t i)
                / (∑ i ∈ alive pred stat oracleAns τ sched cands (t + 1) ω
                    ∪ prunedAt pred stat oracleAns τ sched cands t ω, u t i) :=
  SQPredictiveTransfer.accumulated_perturbation_le n
    (fun t => alive pred stat oracleAns τ sched cands (t + 1) ω)
    (fun t => prunedAt pred stat oracleAns τ sched cands t ω)
    outs u p
    (fun t _ => by
      simp only [prunedAt]
      exact Finset.disjoint_left.mpr fun i hi hp => (Finset.mem_sdiff.mp hp).2 hi)
    hu hp0 hp1 hV

/-- **(stretch) Unpruned posterior concentration via the algorithm's Dirac pmf.** Instantiating Paper
II's `DeterministicDiscovery.deterministic_discovery` at the algorithm's own deterministic predictor
— the Dirac pmf `q i s x = 𝟙[pred i s (ω|_{<s}) = x]` — gives Theorem-3.1 concentration for the
algorithm's UNpruned Bayes posterior: for `n ≥ (K(iR)·ln2 + ln(2/δ))/(2ε₀)` under per-step
separation `hsep`, the posterior on the true rule `iR` is `≥ 1 − δ/2`. This is the pmf-indexing
identification ([Discovery] ↔ the algorithm); composing it with `algorithm_damage_le` into a full
Theorem-4.1(i) statement for the PRUNED algorithm is the assembly residue (see module docstring). -/
theorem posterior_concentration_transfer [Fintype X] [Fintype ι] [DecidableEq ι]
    (pred : ι → (s : ℕ) → (Fin s → X) → X) (w : ι → ℝ) (ω : ℕ → X) (iR : ι)
    (hw : ∀ i, 0 ≤ w i) (k : ℕ) (hwR : w iR = (2 : ℝ) ^ (-(k : ℝ))) (hsumw : ∑ i, w i ≤ 1)
    (hreal : ∀ s, pred iR s (fun k => ω k) = ω s)
    (δ ε₀ : ℝ) (hδ : 0 < δ) (hε : 0 < ε₀) (n : ℕ)
    (hsep : ∀ i, i ≠ iR → ∀ t ∈ Finset.range n,
      ε₀ ≤ BayesRedundancy.sqHellinger (fun x => if x = ω t then 1 else 0)
             (fun x => if pred i t (fun j => ω j) = x then (1 : ℝ) else 0))
    (hT : ((k : ℝ) * Real.log 2 + Real.log (2 / δ)) / (2 * ε₀) ≤ (n : ℝ)) :
    1 - δ / 2 ≤ w iR
        * BayesRedundancy.Lik (fun i s x => if pred i s (fun j => ω j) = x then (1 : ℝ) else 0) ω iR n
        / BayesRedundancy.Pbarₚ (fun i s x => if pred i s (fun j => ω j) = x then (1 : ℝ) else 0)
            w ω n :=
  DeterministicDiscovery.deterministic_discovery
    (q := fun i s x => if pred i s (fun j => ω j) = x then (1 : ℝ) else 0) (R := iR)
    (fun i s x => by split_ifs <;> norm_num)
    (fun i s => by simp [Finset.sum_ite_eq])
    hw k hwR hsumw
    (fun s => if_pos (hreal s))
    δ ε₀ hδ hε n hsep hT

/-- **Posterior monotonicity under restriction** (the part-(i) composition principle): for weights
`v ≥ 0` on `S` with the truth `iR ∈ S' ⊆ S` carrying positive weight, restricting the normalizer to
`S'` can only shrink the denominator, so the restricted quotient dominates: `v iR / ∑_S v ≤ v iR /
∑_{S'} v`. Elementary; the denominator positivity on `S'` comes from `iR ∈ S'`, `v iR > 0`. -/
theorem posterior_mono_of_subset (v : ι → ℝ) (S S' : Finset ι) (hsub : S' ⊆ S)
    (iR : ι) (hiR : iR ∈ S') (hnn : ∀ i ∈ S, 0 ≤ v i) (hpos : 0 < v iR) :
    v iR / (∑ i ∈ S, v i) ≤ v iR / (∑ i ∈ S', v i) := by
  have hS'pos : 0 < ∑ i ∈ S', v i :=
    Finset.sum_pos' (fun i hi => hnn i (hsub hi)) ⟨iR, hiR, hpos⟩
  have hSge : ∑ i ∈ S', v i ≤ ∑ i ∈ S, v i :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i hiS _ => hnn i hiS)
  exact div_le_div_of_nonneg_left hpos.le hS'pos hSge

/-- **Bridge (FV-I ↔ [Discovery]):** the algorithm's Dirac pmf `Lik` in `posterior_concentration_transfer`
IS FV-I's likelihood `L (detFactor pred)` — both are `∏_{s<n} 𝟙[pred i s (ω|_{<s}) = ω s]`, so the
identification is definitional (`rfl`). -/
theorem Lik_qDirac_eq_L_det (pred : ι → (s : ℕ) → (Fin s → X) → X) (i : ι) (n : ℕ) (ω : ℕ → X) :
    BayesRedundancy.Lik (fun i s x => if pred i s (fun j => ω j) = x then (1 : ℝ) else 0) ω i n
      = L (detFactor pred) i n ω := rfl

/-- **Theorem 4.1(i) for the PRUNED algorithm.** Under realizability, the `2^{−k}` prior, per-step
separation `hsep`, the discovery horizon `hT`, and the truth's oracle-closeness `hclose`, the pruned
posterior on the true rule `iR` — the Bayes posterior with the normalizer restricted to the survivor
set `alive … n` — is `≥ 1 − δ/2`. Proof: `truth_survives` puts `iR ∈ alive n ⊆ univ`; the truth's
weight `w iR · L iR = w iR > 0` (realizability ⇒ `L iR = 1`); `posterior_mono_of_subset` then makes
the pruned quotient dominate the unpruned one, which is `≥ 1 − δ/2` by
`posterior_concentration_transfer` (Dirac bridge). The damage bound does NOT enter (see docstring).
`cands = Finset.univ` matches `deterministic_discovery`'s full-`Fintype ι` normalizer. -/
theorem algorithm_discovery [Fintype X] [Fintype ι] [DecidableEq ι]
    (pred : ι → (s : ℕ) → (Fin s → X) → X) (stat : ι → Q → ℝ) (oracleAns : Q → ℝ)
    (τ : ℝ) (hτ : 0 ≤ τ) (sched : ℕ → Finset Q) (w : ι → ℝ) (ω : ℕ → X) (iR : ι)
    (hw : ∀ i, 0 ≤ w i) (k : ℕ) (hwR : w iR = (2 : ℝ) ^ (-(k : ℝ))) (hsumw : ∑ i, w i ≤ 1)
    (hreal : ∀ s, pred iR s (fun k => ω k) = ω s)
    (hclose : ∀ t, ∀ φ ∈ sched t, |oracleAns φ - stat iR φ| ≤ τ)
    (δ ε₀ : ℝ) (hδ : 0 < δ) (hε : 0 < ε₀) (n : ℕ)
    (hsep : ∀ i, i ≠ iR → ∀ t ∈ Finset.range n,
      ε₀ ≤ BayesRedundancy.sqHellinger (fun x => if x = ω t then 1 else 0)
             (fun x => if pred i t (fun j => ω j) = x then (1 : ℝ) else 0))
    (hT : ((k : ℝ) * Real.log 2 + Real.log (2 / δ)) / (2 * ε₀) ≤ (n : ℝ)) :
    1 - δ / 2 ≤ w iR * L (detFactor pred) iR n ω
        / ∑ i ∈ alive pred stat oracleAns τ sched Finset.univ n ω,
            w i * L (detFactor pred) i n ω := by
  -- the truth's likelihood is 1 (realizability), so its weight is positive
  have hLnn : ∀ i, 0 ≤ L (detFactor pred) i n ω := by
    intro i
    simp only [L]
    exact Finset.prod_nonneg fun s _ => (detFactor_mem_Icc pred i s ω).1
  have hLiR : L (detFactor pred) iR n ω = 1 := by
    rw [L_det_eq_indicator, if_pos fun s _ => hreal s]
  have hwiR : 0 < w iR := by rw [hwR]; positivity
  have hviR : 0 < w iR * L (detFactor pred) iR n ω := by rw [hLiR, mul_one]; exact hwiR
  -- truth survives ⇒ `iR ∈ alive n ⊆ univ`
  have htruth : iR ∈ alive pred stat oracleAns τ sched Finset.univ n ω :=
    truth_survives pred stat oracleAns τ hτ sched Finset.univ ω iR (Finset.mem_univ iR) hreal hclose n
  -- posterior concentration over the full class (normalizer `= ∑ univ`), via the Dirac bridge
  have hbridgeP : BayesRedundancy.Pbarₚ
      (fun i s x => if pred i s (fun j => ω j) = x then (1 : ℝ) else 0) w ω n
      = ∑ i ∈ Finset.univ, w i * L (detFactor pred) i n ω := by
    simp only [BayesRedundancy.Pbarₚ, Lik_qDirac_eq_L_det]
  have hpct : 1 - δ / 2 ≤ w iR * L (detFactor pred) iR n ω
      / ∑ i ∈ Finset.univ, w i * L (detFactor pred) i n ω := by
    have h := posterior_concentration_transfer pred w ω iR hw k hwR hsumw hreal δ ε₀ hδ hε n hsep hT
    rw [← Lik_qDirac_eq_L_det pred iR n ω, ← hbridgeP]
    exact h
  -- monotonicity: restricting the normalizer to `alive n ⊆ univ` dominates
  have hmono := posterior_mono_of_subset (fun i => w i * L (detFactor pred) i n ω)
    Finset.univ (alive pred stat oracleAns τ sched Finset.univ n ω) (Finset.subset_univ _)
    iR htruth (fun i _ => mul_nonneg (hw i) (hLnn i)) hviR
  exact le_trans hpct hmono

end SQAlgorithm
