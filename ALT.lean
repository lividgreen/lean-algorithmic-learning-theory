/-
Copyright (c) 2026 Mykola Palamarchuk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mykola Palamarchuk
-/
import ALT.AccretiveDecoupling
import ALT.AdditiveComplexity
import ALT.AxiomAuditFoundation
import ALT.AxiomAuditMathlib
import ALT.BasinSettling
import ALT.BayesRedundancy
import ALT.BinaryConstant
import ALT.BinaryKraft
import ALT.Birkhoff.AxiomAudit
import ALT.Birkhoff.PointwiseBirkhoff
import ALT.BirkhoffTool
import ALT.BoundedInterp
import ALT.CapacityBoundedEval
import ALT.CapacityLayer
import ALT.CapacityThreshold
import ALT.CartesianClosed
import ALT.CategoricalThreshold
import ALT.ChainDependencyAudit
import ALT.CheckerWorkspace
import ALT.ChengCCC
import ALT.Code.BitGates
import ALT.Code.EvalLaws
import ALT.Code.SizeArith
import ALT.CodeArith
import ALT.CodePacking
import ALT.Collector
import ALT.CommitmentSeam
import ALT.CountableDiscovery
import ALT.CounterLearner
import ALT.DecisionListData
import ALT.DecisionListSolver
import ALT.DecoupledSimulation
import ALT.Decoupling
import ALT.DeterministicDiscovery
import ALT.EpsilonZeroBound
import ALT.ExactBreakeven
import ALT.ExcessOrder
import ALT.ExcessOrderComplete
import ALT.ExtensionalDiscovery
import ALT.FiniteInfoTheory
import ALT.FlooredMixture
import ALT.FrameItinerary
import ALT.GodelChecker
import ALT.GodelCheckerAutomaton
import ALT.GodelCheckerComplete
import ALT.GodelComplete
import ALT.GodelCore
import ALT.GodelInternalization
import ALT.GodelThreshold
import ALT.GradeTransport
import ALT.GradedApplication
import ALT.GradedConjugation
import ALT.GradedSimulation
import ALT.GrunwaldMehtaDiscovery
import ALT.HellingerBridge
import ALT.KReconnection
import ALT.KolmogorovBitlen
import ALT.KolmogorovComplexity
import ALT.KolmogorovTimeBounded
import ALT.LearningWitness
import ALT.LogMassEvent
import ALT.MDLCoding
import ALT.MDLDominance
import ALT.MinimalityWitness
import ALT.NoisyWindowChain
import ALT.ParameterizedNNO
import ALT.ParityCounterexample
import ALT.ParityWalk
import ALT.PersistenceCapacity
import ALT.PersistentWalk
import ALT.PolyTime
import ALT.PolyTimeAccounting
import ALT.PrefixComplexity
import ALT.PrefixInvariance
import ALT.PressureWindow
import ALT.PriorNormalization
import ALT.QuantizationRate
import ALT.ReadingWord
import ALT.Realizability
import ALT.RealizabilityCCC
import ALT.RealizabilityCoproduct
import ALT.RealizabilityRecursor
import ALT.RealizabilitySubobject
import ALT.RealizerLength
import ALT.RecursorAlgebra
import ALT.Reflective
import ALT.ReflectiveAutomaton
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
import ALT.SearchCost
import ALT.SearchSpace
import ALT.SkewFiber
import ALT.StructureFunction
import ALT.SubstrateClass
import ALT.SurpriseBudget
import ALT.TimeCost
import ALT.UniversalAt
import ALT.Ville
import ALT.WeightedFiber
import ALT.WindowDeterminism
import ALT.WitnessMixture

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

* **[Decoupling]** — decoupling and the categorical threshold for representational
  reflection (the realizability category, the bounded recursor, the Gödel threshold);
* **[Discovery]** — MDL dominance and finite-time rule discovery;
* **[SQ]** — polynomial-time convergence under statistical queries;
* **[Persistence]** — resource-bounded persistence capacity: the priced decoder;
* **[Inevitability]** — the realization-synthesis capstone: two independent routes to
  a reflective subsystem, and the open problem of realizing both on one witness.

The papers are in preparation; the repository README links preprints as they
appear. References of the form "[Decoupling] §X" (a bracketed short-title key,
then the section anchor) point into that series, and `FV-*` tags name rows of
the papers' formal-verification tables, mirrored by the build-enforced axiom
guards in `ALT.AxiomAuditMathlib` and `ALT.AxiomAuditFoundation`.

## Verification standard

No `sorry`, `admit`, or `native_decide`; standard axioms only (`propext`,
`Classical.choice`, `Quot.sound`), with every capstone's exact axiom set
build-enforced by `#guard_msgs in #print axioms` guards.

This root module imports every module of the development — including the
Foundation-based ones (`ALT.AxiomAuditFoundation`, `ALT.GodelChecker`,
`ALT.GodelCheckerAutomaton`, `ALT.GodelCheckerComplete`, `ALT.GodelComplete`),
which discharge the Gödel incompleteness hypothesis against upstream
`FormalizedFormalLogic/Foundation`. So `ALT` is the single library root, and
the build and the API docs cover the development through it alone.

Several modules state a dependency boundary in their docstring ("deliberately a
leaf", "stays deliberately light", "cross-referenced but NOT imported") and hold
themselves to it with `assert_not_exists` on a characteristic declaration of the
excluded territory. An assertion whose witness name does not exist anywhere is
vacuous, so the root re-checks them all below: since this module's import closure
is the whole development, every such witness must resolve here.
-/

-- Silent when every `assert_not_exists` witness in the closure exists; warns, naming the module,
-- for any witness that does not — i.e. for a boundary assertion that is silently vacuous.
set_option linter.hashCommand false in
#check_assertions!
