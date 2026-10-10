/-
Copyright (c) 2026 Mykola Palamarchuk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mykola Palamarchuk
-/
module

public import ALT.AccretingExcess
public import ALT.AccretingWitness
public import ALT.AccretiveDecoupling
public import ALT.AxiomAuditFoundation
public import ALT.AxiomAuditMathlib
public import ALT.BasinSettling
public import ALT.BirkhoffTool
public import ALT.BlockPairCriterion
public import ALT.BlockPairFamilyCriterion
public import ALT.BlockPairHost
public import ALT.BlockPairObservability
public import ALT.BlockPairOverlap
public import ALT.BlockPairPrice
public import ALT.BlockPairProfile
public import ALT.BlockPairTower
public import ALT.BlockPairWitness
public import ALT.BoundedInterp
public import ALT.CanonicalFormLens
public import ALT.CapacityBoundedEval
public import ALT.CapacityLayer
public import ALT.CapacityThreshold
public import ALT.CartesianClosed
public import ALT.CategoricalThreshold
public import ALT.ChainDependencyAudit
public import ALT.ChaitinLadder
public import ALT.ChaitinPrefixLadder
public import ALT.CheckerWorkspace
public import ALT.CodeArith
public import ALT.CodeDataRate
public import ALT.CodePacking
public import ALT.Collector
public import ALT.CommitmentSeam
public import ALT.CountableDiscovery
public import ALT.CounterLearner
public import ALT.DamageGate
public import ALT.DecoupledSimulation
public import ALT.Decoupling
public import ALT.DeepLadder
public import ALT.DeterministicDiscovery
public import ALT.EpsilonZeroBound
public import ALT.EvoAbsorption
public import ALT.ExcessOrder
public import ALT.ExcessOrderComplete
public import ALT.ExpensiveLens
public import ALT.ExtensionalDiscovery
public import ALT.FiniteHorizonDiscovery
public import ALT.FiniteWorldWidth
public import ALT.FixedLensCriterion
public import ALT.FlooredMixture
public import ALT.FrameItinerary
public import ALT.GodelChecker
public import ALT.GodelCheckerAutomaton
public import ALT.GodelCheckerComplete
public import ALT.GodelComplete
public import ALT.GodelCore
public import ALT.GodelInternalization
public import ALT.GodelThreshold
public import ALT.GradeTransport
public import ALT.GradedApplication
public import ALT.GradedConjugation
public import ALT.GradedSimulation
public import ALT.GrowingComposite
public import ALT.GrowingCore
public import ALT.GrowingCoreCrossing
public import ALT.GrowingHostWitness
public import ALT.GrowingPrice
public import ALT.GrowingSeamWitness
public import ALT.GrowingWorld
public import ALT.GrunwaldMehtaDiscovery
public import ALT.HellingerBridge
public import ALT.HindsightMixture
public import ALT.IndexCost
public import ALT.KReconnection
public import ALT.LearningWitness
public import ALT.LearningWitnessComplete
public import ALT.LogMassEvent
public import ALT.MDLCoding
public import ALT.MDLDominance
public import ALT.MemoryWidthWitness
public import ALT.MinimalityWitness
public import ALT.NoisyWindowChain
public import ALT.ParameterizedNNO
public import ALT.ParityCounterexample
public import ALT.ParityWalk
public import ALT.PeriodicObservability
public import ALT.Persistence.Core
public import ALT.Persistence.Counting
public import ALT.Persistence.MovingLens
public import ALT.Persistence.Robustness
public import ALT.PersistenceCapacity
public import ALT.PersistentWalk
public import ALT.PolyTimeAccounting
public import ALT.PrefixEliasKB
public import ALT.QuantizationRate
public import ALT.ReadingWord
public import ALT.RealizabilityRecursor
public import ALT.RealizerLength
public import ALT.RecursorAlgebra
public import ALT.RecursorCoproductAlgebra
public import ALT.RedundantFiber
public import ALT.Reflective
public import ALT.ReflectiveAutomaton
public import ALT.RegimeConsistency
public import ALT.RegisterClass
public import ALT.RepFintype
public import ALT.RetentionOverhead
public import ALT.RetentionUpperBound
public import ALT.SQAlgorithm
public import ALT.SQMixtureSupermartingale
public import ALT.SQPredictiveTransfer
public import ALT.SQPrunedMass
public import ALT.SQSearchPhaseMass
public import ALT.SQVersionSpace
public import ALT.SampleComplexity
public import ALT.SearchCost
public import ALT.SearchSpace
public import ALT.ShiftedSpikeCriterion
public import ALT.ShiftedSpikeHost
public import ALT.ShiftedSpikeTower
public import ALT.SkewFiber
public import ALT.SpawningFiber
public import ALT.SubstitutionClass
public import ALT.SubstitutionComposite
public import ALT.SubstitutionSchedule
public import ALT.SubstitutionSource
public import ALT.SubstrateClass
public import ALT.SubstrateEmergence
public import ALT.SurpriseBudget
public import ALT.TapeHost
public import ALT.TapeHostFiber
public import ALT.TapeHostObservability
public import ALT.TapeHostOverlap
public import ALT.TapeHostSchedule
public import ALT.TapeHostSurvival
public import ALT.TapeHostWitness
public import ALT.UniversalAt
public import ALT.WeightedFiber
public import ALT.WindowDeterminism
public import ALT.WitnessMixture

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
* **[Guests]** — a description-length theory of systems running inside finite and growing
  dynamical systems: priced factors, the Witness World, emergence, and growing worlds with
  their growing core, memory width and staged collapse;
* **[RuleSpace]** — accretion, rays and robustness over the radius-one rule space:
  the growing width decided at every quiescent elementary cellular automaton, the
  rays of table 90 from the single seed, and robustness to two cells at every scale;
* **[Growth]** — endogenous observability on growing hosts: statistical-query
  learning from substitution sources at explicit horizons;
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

@[expose] public section

set_option linter.hashCommand false in
#check_assertions!
