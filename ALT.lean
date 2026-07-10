/-
Copyright (c) 2026 Mykola Palamarchuk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mykola Palamarchuk
-/
import ALT.AdditiveComplexity
import ALT.AxiomAuditMathlib
import ALT.BayesRedundancy
import ALT.BinaryConstant
import ALT.Birkhoff.AxiomAudit
import ALT.Birkhoff.PointwiseBirkhoff
import ALT.BirkhoffTool
import ALT.CapacityLayer
import ALT.CapacityThreshold
import ALT.CartesianClosed
import ALT.CategoricalThreshold
import ALT.ChengCCC
import ALT.Collector
import ALT.CountableDiscovery
import ALT.CounterLearner
import ALT.DecisionListData
import ALT.DecisionListSolver
import ALT.Decoupling
import ALT.DeterministicDiscovery
import ALT.EpsilonZeroBound
import ALT.ExactBreakeven
import ALT.ExtensionalDiscovery
import ALT.FiniteInfoTheory
import ALT.GodelCore
import ALT.GodelInternalization
import ALT.GodelThreshold
import ALT.GrunwaldMehtaDiscovery
import ALT.HellingerBridge
import ALT.KReconnection
import ALT.KolmogorovBitlen
import ALT.KolmogorovComplexity
import ALT.KolmogorovTimeBounded
import ALT.MDLCoding
import ALT.MDLDominance
import ALT.ParameterizedNNO
import ALT.ParityCounterexample
import ALT.PolyTime
import ALT.PolyTimeAccounting
import ALT.PrefixComplexity
import ALT.PrefixInvariance
import ALT.PressureWindow
import ALT.PriorNormalization
import ALT.ProofChainSkeleton
import ALT.Realizability
import ALT.RealizabilityCCC
import ALT.RealizabilityCoproduct
import ALT.RealizabilityRecursor
import ALT.RealizerLength
import ALT.RecursorAlgebra
import ALT.Reflective
import ALT.RegimeConsistency
import ALT.RepFintype
import ALT.RetentionOverhead
import ALT.RetentionUpperBound
import ALT.SQAlgorithm
import ALT.SQEnvelope
import ALT.SQMixtureSupermartingale
import ALT.SQObjects
import ALT.SQOracle
import ALT.SQPredictiveTransfer
import ALT.SQPrunedMass
import ALT.SQSearchPhaseMass
import ALT.SQVersionSpace
import ALT.SampleComplexity
import ALT.SmokeTest
import ALT.StructureFunction
import ALT.TimeCost
import ALT.Ville

/-!
# ALT — Algorithmic Learning Theory in Lean 4

Machine-checked algorithmic learning theory over Mathlib: Ville's inequality,
statistical-query learning (statistical dimension, version-space envelopes, parity's
exponential lower bound), a prequential-MDL discovery chain, a step-counting cost
model for `Nat.Partrec.Code` carrying a greedy learner verified both correct and
polynomial-step, a realizability (assembly) category over Kleene's first algebra
with a bounded recursor, and a bounded Gödel decision.

The development machine-checks the load-bearing results of a companion paper
series, cited in docstrings as:

* **Paper I** — decoupling and the categorical threshold for representational
  reflection (the realizability category, the bounded recursor, the Gödel threshold);
* **Paper II** — MDL dominance and finite-time rule discovery;
* **Paper III** — polynomial-time convergence under statistical queries;
* **Paper IV** — the capstone (structural proof-chain check only).

The papers are in preparation; the repository README links preprints as they
appear. References of the form "Paper N §X" point into that series, and `FV-*`
tags name rows of the papers' formal-verification tables, mirrored by the
build-enforced axiom guards in `ALT.AxiomAuditMathlib` and
`ALT.AxiomAuditFoundation`.

## Verification standard

No `sorry`, `admit`, or `native_decide`; standard axioms only (`propext`,
`Classical.choice`, `Quot.sound`), with every capstone's exact axiom set
build-enforced by `#guard_msgs in #print axioms` guards.

This root module imports every Mathlib-side module. The four Foundation-side
modules (`ALT.AxiomAuditFoundation`, `ALT.GodelChecker`,
`ALT.GodelCheckerComplete`, `ALT.GodelComplete`) cannot be co-imported with the
Mathlib umbrella in one file (a `Matrix.map` root-name clash) and are listed as
separate library roots in `lakefile.toml`, so the build and the API docs cover
them as well.
-/
