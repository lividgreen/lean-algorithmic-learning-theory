module

public import ALT.BirkhoffTool
public import ALT.Decoupling
public import ALT.PersistenceCapacity
public import ALT.DecoupledSimulation
public import ALT.ParameterizedNNO
public import ALT.GodelInternalization
public import ALT.RepFintype
public import ALT.RecursorAlgebra
public import Realizability.Realizability
public import Realizability.RealizabilityCCC
public import ALT.RealizabilityRecursor
public import Realizability.RealizabilityCoproduct
public import ALT.RecursorCoproductAlgebra
public import Realizability.RealizabilitySubobject
public import ALT.CapacityLayer
public import ALT.RealizerLength
public import ALT.CategoricalThreshold
public import ALT.ReflectiveAutomaton
public import ShannonInfo.ChengCCC
public import ShannonInfo.FiniteInfoTheory
public import ALT.Reflective
public import ALT.CounterLearner
public import ALT.MDLCoding
public import ALT.GrunwaldMehtaDiscovery
public import ALT.RetentionUpperBound
public import Learning.BayesRedundancy
public import ALT.DeterministicDiscovery
public import ALT.CountableDiscovery
public import ALT.ExtensionalDiscovery
public import ALT.HellingerBridge
public import AIT.KolmogorovTimeBounded
public import ALT.PolyTimeAccounting
public import ALT.ParityCounterexample
public import ALT.SQVersionSpace
public import ALT.SampleComplexity
public import ALT.SQAlgorithm
public import ALT.CommitmentSeam
public import Learning.SQEnvelope
public import Learning.SQOracle
public import ALT.SQPredictiveTransfer
public import ALT.SQPrunedMass
public import ALT.SQMixtureSupermartingale
public import Learning.SQObjects
public import ALT.SQSearchPhaseMass
public import AnytimeValid.Ville
public import AIT.PrefixComplexity
public import CodeLayer.AdditiveComplexity
public import CodeLayer.BinaryConstant
public import CodeLayer.PrefixInvariance
public import ALT.CodeDataRate
public import AIT.PrefixMachine
public import CodeLayer.BitStringPrimrec
public import AIT.AlgorithmicProbability
public import AIT.CodingTheoremDecoder
public import AIT.KraftChaitin
public import AIT.CodingTheorem
public import AIT.KraftMinimality
public import AIT.StructureFunction
public import ALT.SearchCost
public import ALT.SearchSpace
public import CodeLayer.TimeCost
public import CodeLayer.PolyTime
public import ALT.CheckerWorkspace
public import ALT.CapacityBoundedEval
public import ALT.BoundedInterp
public import ALT.CodePacking
public import ALT.UniversalAt
public import ALT.GradeTransport
public import ALT.GradedApplication
public import ALT.GradedConjugation
public import ALT.GradedSimulation
public import ALT.Collector
public import Learning.DecisionListData
public import Learning.DecisionListSolver
-- Guard-gap closure: pre-`#guard_msgs` modules (capstones guarded in the appended section below).
public import ALT.CartesianClosed
public import ALT.GodelThreshold
public import ALT.RegimeConsistency
public import ALT.CapacityThreshold
public import ALT.MDLDominance
public import ALT.RetentionOverhead
public import CodeLayer.PriorNormalization
public import ALT.EpsilonZeroBound
public import ALT.KReconnection
public import AIT.KolmogorovComplexity
public import AIT.KolmogorovBitlen
public import ALT.ChainDependencyAudit
public import ALT.ExcessOrder
public import ALT.SkewFiber
public import ALT.AccretingWitness
public import ALT.AccretiveDecoupling
public import ALT.GrowingWorld
public import Nonautonomous.MergeQuotient
public import ALT.GrowingCore
public import ALT.SurpriseBudget
public import ALT.WeightedFiber
public import ALT.QuantizationRate
public import ALT.FlooredMixture
public import ALT.SubstrateClass
public import ALT.SubstrateEmergence
public import ALT.BlockPairProfile
public import ALT.BlockPairHost
public import ALT.BlockPairPrice
public import ALT.TapeHost
public import ALT.TapeHostFiber
public import ALT.TapeHostObservability
public import ALT.TapeHostWitness
public import ALT.BlockPairCriterion
public import ALT.BlockPairFamilyCriterion
public import ALT.TapeHostSurvival


/-!
# Axiom audit (Mathlib side) — machine-ENFORCED axiom-cleanliness ([Decoupling], [Discovery], [SQ])

Companion to `ALT/AxiomAuditFoundation.lean` for the umbrella-Mathlib–side theorems (the
Foundation/Mathlib import divide forbids one file importing both). Each `#guard_msgs in
#print axioms …` **fails `lake build`** if the theorem's axiom set drifts. The Decoupling core is
even `Classical.choice`-free (`[propext, Quot.sound]`), and the necessity counterexample is fully
constructive (`[propext]`).

Coverage spans all three Mathlib-side papers: **[Decoupling]** (decoupling, bounded recursor,
realizability CCC, categorical threshold), **[Discovery]** (MDL coding/dominance, Cheng-CCC
necessity, finite info-theory, Grünwald–Mehta / deterministic / countable discovery, retention), and
**[SQ]** (time-bounded Kolmogorov complexity, poly-time accounting, the parity SQ counterexample, SQ
version-space pruning, and the sample-complexity ε₀-absorption).
-/

-- §3 Decoupling Lemma (FV-7) — constructive core

@[expose] public section

/-- info: 'ALT.decoupling_iff_persists_all' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.decoupling_iff_persists_all

/-- info: 'ALT.necessity_needs_faithful' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.necessity_needs_faithful

/-- info: 'ALT.total_overwrite_exclusion' depends on axioms: [Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.total_overwrite_exclusion

-- §3 Corollary 3.3 (the decoupling dichotomy) and §3 Proposition 3.4 (the relativized equivalence
-- on an update-closed state set Ω) — both derived from the choice-free Decoupling core.
/-- info: 'ALT.decoupling_dichotomy' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.decoupling_dichotomy

/-- info: 'ALT.decoupling_iff_persists_on' depends on axioms: [Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.decoupling_iff_persists_on

-- The accretive extension: the same equivalence for a monotonically growing code region, plus the
-- coherence statement that the fixed-partition Proposition 3.4 is its constant-family case, and the
-- append-only instance on which the region grows strictly and the limit region is NOT read-only.
/-- info: 'ALT.accretive_decoupling_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.accretive_decoupling_iff

/-- info: 'ALT.accretive_iff_persists_on_const' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.accretive_iff_persists_on_const

set_option linter.style.longLine false in
/-- info: 'ALT.exists_strictly_accretive_decoupling' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.exists_strictly_accretive_decoupling

-- The committing substrate: an arbitrary stream committed one entry per stage, generalizing the
-- fixed-symbol tape above — Proposition 6.2's first theorem consumer, `accretive_persists` applied
-- to a stream instance rather than reproved.
/-- info: 'ALT.seqDecode_hereditary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.seqDecode_hereditary

-- The growing-world skeleton ([Guests] §2 over [Inevitability] §6): factor closure at an arbitrary
-- carrier, coherence with the fixed-carrier `Intertwines`, the guard showing the tape's
-- counter-free reading admits no guest law at all, and the counter-including reading's strictly
-- growing extent over the binary sub-stages.
/-- info: 'Nonautonomous.positivelyInvariant_imageFiber' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms Nonautonomous.positivelyInvariant_imageFiber

/-- info: 'ALT.stagedSquare_const_iff' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.stagedSquare_const_iff

set_option linter.style.longLine false in
/-- info: 'ALT.not_exists_stagedSquare_tapeDecode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.not_exists_stagedSquare_tapeDecode

set_option linter.style.longLine false in
/-- info: 'ALT.ncard_guestStage_tapeStageB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.ncard_guestStage_tapeStageB

-- The accreting healer world ([Guests] §3/§5 over the growing-world skeleton): the stages advance
-- under append-heal-turn, the majority reading obeys the growing-memory law from every state,
-- total flips under the healing radius are erased in one step with the accretion in the loop, and
-- the guest's extent doubles at every stage.
/-- info: 'ALT.advances_accUpdate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.advances_accUpdate

/-- info: 'ALT.stagedSquare_accRead' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.stagedSquare_accRead

/-- info: 'ALT.accUpdate_eq_of_sum_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.accUpdate_eq_of_sum_lt

/-- info: 'ALT.guestStage_accRead_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.guestStage_accRead_eq

set_option linter.style.longLine false in
/-- info: 'ALT.ncard_guestStage_accRead' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.ncard_guestStage_accRead

-- The growing core (`ALT/GrowingCore.lean`): the merge quotient's universality is guarded in
-- `ECA/AxiomAudit.lean`; at a finite carrier it is in bijection with the recurrent
-- core; and the accreting healer world's decode reading is one concrete consumer.
set_option linter.style.longLine false in
/-- info: 'ALT.nat_card_mergeQuot_eq_core' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.nat_card_mergeQuot_eq_core

/-- info: 'ALT.mergeRead_eq_of_merges' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.mergeRead_eq_of_merges

set_option linter.style.longLine false in
/-- info: 'ALT.accMerges_of_accUpdate_eq_of_sum_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.accMerges_of_accUpdate_eq_of_sum_lt

/-- info: 'ALT.accLaw_injective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.accLaw_injective

set_option linter.style.longLine false in
/-- info: 'ALT.accRead_merges_invariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.accRead_merges_invariant

-- The surprise-budget assembly: [Discovery]'s event count priced in cells, against [Persistence]'s
-- robustness margin and repair tax. Two survival theorems under two different (independent)
-- hypotheses on the host, and the counterexample showing that without either one a debt that fits
-- inside the margin still destroys the reading.
/-- info: 'ALT.debt_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.debt_le

/-- info: 'ALT.survives_of_margin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.survives_of_margin

/-- info: 'ALT.Corrects.survives' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.Corrects.survives

set_option linter.style.longLine false in
/-- info: 'ALT.CorrectsWithin.traj_eq_of_spaced' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.CorrectsWithin.traj_eq_of_spaced

set_option linter.style.longLine false in
/-- info: 'ALT.CorrectsWithin.survives' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.CorrectsWithin.survives

/-- info: 'ALT.survives_of_invariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.survives_of_invariant

/-- info: 'ALT.badWorld_not_survives' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.badWorld_not_survives

set_option linter.style.longLine false in
/-- info: 'ALT.correctsWithin_needs_spaced' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.correctsWithin_needs_spaced

/-- info: 'ALT.capacity_price' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.capacity_price

-- The settling companion: the damaged trajectory settles whenever the undamaged reading does, in
-- both the abstract and the purely dynamical form, plus guard families showing this is a
-- companion question to Proposition 6.1(iii) rather than a fourth sufficient condition.
set_option linter.style.longLine false in
/-- info: 'ALT.settles_traj_of_settles' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.settles_traj_of_settles

set_option linter.style.longLine false in
/-- info: 'ALT.settles_traj_of_readOnly' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.settles_traj_of_readOnly

set_option linter.style.longLine false in
/-- info: 'ALT.settles_traj_not_agreement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.settles_traj_not_agreement

/-- info: 'ALT.corrects_not_settles' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.corrects_not_settles

-- The joint-dependence mechanism: `Corrects` and `HammingNonexpansive` together force the ω-limit
-- set to a lone fixed point, whose ball is then exactly the third repair's invariant set, plus the
-- guard family witnessing where this collapses to nothing.
set_option linter.style.longLine false in
/-- info: 'ALT.Corrects.hammingDist_image_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.Corrects.hammingDist_image_lt

set_option linter.style.longLine false in
/-- info: 'ALT.Corrects.omegaLimit_subsingleton' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.Corrects.omegaLimit_subsingleton

set_option linter.style.longLine false in
/-- info: 'ALT.Corrects.exists_fixedPoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.Corrects.exists_fixedPoint

set_option linter.style.longLine false in
/-- info: 'ALT.Corrects.survives_of_invariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.Corrects.survives_of_invariant

set_option linter.style.longLine false in
/-- info: 'ALT.joint_dependence_boundary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.joint_dependence_boundary

-- The weighted fiber: fitness-proportional selection on a frequency-independent likelihood, whose
-- exact step IS Bayesian update; the carrier projection that a finite host forces; the transported
-- pricing assembly; and the instance showing the projection is not the identity.
/-- info: 'ALT.toDist_bayesStep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.toDist_bayesStep

/-- info: 'ALT.raw_wGen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.raw_wGen

set_option linter.style.longLine false in
/-- info: 'ALT.wFiber_emergence_pricing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.wFiber_emergence_pricing

set_option linter.style.longLine false in
/-- info: 'ALT.surjective_argmaxFrame_of_settled' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.surjective_argmaxFrame_of_settled

set_option linter.style.longLine false in
/-- info: 'ALT.weighted_fiber_not_exactly_bayes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.weighted_fiber_not_exactly_bayes

-- The quantization rate: the exactness horizon below which the finite run IS the exact run
-- (and its sharpness witness), the general L¹-normalization fact, the per-step residual bounds on
-- the carrier projection, the composed rate against exact Bayes, and the universal total-variation
-- cap that reconciles the rate with the annihilation instance above.
/-- info: 'ALT.raw_wRun_eq_bayesRun' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.raw_wRun_eq_bayesRun

/-- info: 'ALT.toDist_wRun_eq_bayes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.toDist_wRun_eq_bayes

set_option linter.style.longLine false in
/-- info: 'ALT.wRun_ne_bayesRun_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.wRun_ne_bayesRun_witness

/-- info: 'ALT.l1_normalize_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.l1_normalize_le

/-- info: 'ALT.toDist_project_close' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.toDist_project_close

/-- info: 'ALT.toDist_project_rate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.toDist_project_rate

/-- info: 'ALT.wGen_bayes_rate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.wGen_bayes_rate

/-- info: 'ALT.toDist_sub_le_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.toDist_sub_le_two

-- The floored mixture: the hypothesis-free exponent automaton with its running-leader theorems, the
-- saturation normal form recovered from it at a frozen leader (with the below-horizon regime and
-- the annihilating instance read off that), the threshold-gated event bound with the guard family
-- that refutes it below the budget, the uniform-in-time accumulation bound, and the three families
-- that refute the two quantitative results once realizability is dropped.
/-- info: 'ALT.wRun_eq_pow_expRun' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.wRun_eq_pow_expRun

/-- info: 'ALT.expRun_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.expRun_le

/-- info: 'ALT.expMax_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.expMax_mono

/-- info: 'ALT.expMax_absorbing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.expMax_absorbing

/-- info: 'ALT.wRun_eq_pow_deficit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.wRun_eq_pow_deficit

/-- info: 'ALT.bayesRun_missFit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.bayesRun_missFit

set_option linter.style.longLine false in
/-- info: 'ALT.raw_wRun_eq_bayesRun_missFit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.raw_wRun_eq_bayesRun_missFit

set_option linter.style.longLine false in
/-- info: 'ALT.floorSurprises_unbounded_below_budget' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.floorSurprises_unbounded_below_budget

set_option linter.style.longLine false in
/-- info: 'ALT.floorSurprises_unbounded_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.floorSurprises_unbounded_witness

set_option linter.style.longLine false in
/-- info: 'ALT.floorSurprise_card_mul_le_missCount' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.floorSurprise_card_mul_le_missCount

set_option linter.style.longLine false in
/-- info: 'ALT.floorSurprise_card_mul_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.floorSurprise_card_mul_le

/-- info: 'ALT.wrongMass_le_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.wrongMass_le_one

/-- info: 'ALT.wrongMass_lt_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.wrongMass_lt_one

set_option linter.style.longLine false in
/-- info: 'ALT.floorSurprise_vacuous_at_badW_budget' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.floorSurprise_vacuous_at_badW_budget

set_option linter.style.longLine false in
/-- info: 'ALT.raw_wRun_allMiss_eq_badW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.raw_wRun_allMiss_eq_badW

set_option linter.style.longLine false in
/-- info: 'ALT.wrongMass_lt_one_of_hit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.wrongMass_lt_one_of_hit

/-- info: 'ALT.wrongMass_everyMiss' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.wrongMass_everyMiss

set_option linter.style.longLine false in
/-- info: 'ALT.floorSurprises_unbounded_everyMiss' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.floorSurprises_unbounded_everyMiss

set_option linter.style.longLine false in
/-- info: 'ALT.floorSurprise_card_mul_gt_everyMiss_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.floorSurprise_card_mul_gt_everyMiss_witness

/-- info: 'ALT.expRun_altMiss' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.expRun_altMiss

set_option linter.style.longLine false in
/-- info: 'ALT.floorSurprises_unbounded_altMiss' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.floorSurprises_unbounded_altMiss

set_option linter.style.longLine false in
/-- info: 'ALT.floorSurprise_card_mul_gt_altMiss_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.floorSurprise_card_mul_gt_altMiss_witness

set_option linter.style.longLine false in
/-- info: 'ALT.le_of_card_mul_le_missCount_everyMiss' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.le_of_card_mul_le_missCount_everyMiss

set_option linter.style.longLine false in
/-- info: 'ALT.two_mul_le_of_card_mul_le_missCount_altMiss' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.two_mul_le_of_card_mul_le_missCount_altMiss

set_option linter.style.longLine false in
/-- info: 'ALT.toDist_wRun_sub_bayesRun_mirrorMiss' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.toDist_wRun_sub_bayesRun_mirrorMiss

set_option linter.style.longLine false in
/-- info: 'ALT.toDist_wRun_sub_bayesRun_not_le_mirrorMiss' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.toDist_wRun_sub_bayesRun_not_le_mirrorMiss

set_option linter.style.longLine false in
/-- info: 'ALT.toDist_wRun_sub_bayesRun_not_le_mirrorMiss_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.toDist_wRun_sub_bayesRun_not_le_mirrorMiss_two

/-- info: 'ALT.toDist_mul_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.toDist_mul_left

set_option linter.style.longLine false in
/-- info: 'ALT.toDist_wRun_sub_bayesRun_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.toDist_wRun_sub_bayesRun_le

-- The tracking form: the same bound against exact Bayes restarted at `s` from the floored run's
-- own state there, under a co-leader at `s` that never misses inside the window — no realizable
-- candidate anywhere. The bound above is its `s = 0` instance. Two families guard the two
-- hypotheses: dropping co-leadership holds the discrepancy at `850/963`, dropping the
-- never-missing candidate at `63/65`, both against a bound that vanishes in the budget.
/-- info: 'ALT.coleader_persists' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.coleader_persists

/-- info: 'ALT.expRun_eq_hitCount_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.expRun_eq_hitCount_sub

/-- info: 'ALT.bayesFrom_eq_pow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.bayesFrom_eq_pow

/-- info: 'ALT.bayesFrom_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.bayesFrom_zero

set_option linter.style.longLine false in
/-- info: 'ALT.toDist_wRun_sub_bayesFrom_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.toDist_wRun_sub_bayesFrom_le

set_option linter.style.longLine false in
/-- info: 'ALT.toDist_wRun_sub_bayesFrom_preAbsorption' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.toDist_wRun_sub_bayesFrom_preAbsorption

set_option linter.style.longLine false in
/-- info: 'ALT.toDist_wRun_sub_bayesFrom_not_le_preAbsorption' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.toDist_wRun_sub_bayesFrom_not_le_preAbsorption

set_option linter.style.longLine false in
/-- info: 'ALT.toDist_wRun_sub_bayesFrom_sinkRecover' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.toDist_wRun_sub_bayesFrom_sinkRecover

set_option linter.style.longLine false in
/-- info: 'ALT.toDist_wRun_sub_bayesFrom_not_le_sinkRecover' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.toDist_wRun_sub_bayesFrom_not_le_sinkRecover

-- The reading settles: under realizability the ceiling set is the version space, so the reading is
-- the least never-missing candidate — a non-decreasing index below the candidate count, hence
-- eventually constant and moving at most `C − 1` times. The last of the three is the same statement
-- at the construction's own predictive fitness, read through the frame the pricing assembly uses.
set_option linter.style.longLine false in
/-- info: 'ALT.argmax_wRun_eventually_const' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.argmax_wRun_eventually_const

set_option linter.style.longLine false in
/-- info: 'ALT.argmax_wRun_card_changes_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.argmax_wRun_card_changes_le

-- The (P)/(I) separation: the least-recently-wrong rotation. The hypothesis-free hub below the
-- horizon, the rotation's closed forms for its miss count and exponents, the running ceiling and
-- the reading identity it forces (the candidate about to miss holds the maximum weight), the
-- change-every-step and surprise-set-empty halves, and their assembly into one theorem plus a
-- concrete non-vacuous witness at the gate-satisfying parameters `C = 8`, `b = 6`, `θ = 1/4`.
set_option linter.style.longLine false in
/-- info: 'ALT.expRun_eq_sub_missCount_of_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.expRun_eq_sub_missCount_of_le

/-- info: 'ALT.missCount_rotMiss' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.missCount_rotMiss

/-- info: 'ALT.expRun_rotMiss_of_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.expRun_rotMiss_of_le

/-- info: 'ALT.wMax_wRun_rotMiss' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.wMax_wRun_rotMiss

/-- info: 'ALT.argmax_wRun_rotMiss' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.argmax_wRun_rotMiss

set_option linter.style.longLine false in
/-- info: 'ALT.argmax_wRun_rotMiss_ne_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.argmax_wRun_rotMiss_ne_succ

/-- info: 'ALT.sum_raw_wRun_rotMiss' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.sum_raw_wRun_rotMiss

/-- info: 'ALT.wrongMass_rotMiss' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.wrongMass_rotMiss

set_option linter.style.longLine false in
/-- info: 'ALT.floorSurpriseSet_rotMiss_eq_empty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.floorSurpriseSet_rotMiss_eq_empty

set_option linter.style.longLine false in
/-- info: 'ALT.rotMiss_prediction_identification_separation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.rotMiss_prediction_identification_separation

set_option linter.style.longLine false in
/-- info: 'ALT.rotMiss_prediction_identification_separation_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.rotMiss_prediction_identification_separation_witness

set_option linter.style.longLine false in
/-- info: 'ALT.argmaxFrame_wWorld_eventually_const' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.argmaxFrame_wWorld_eventually_const

-- The base-reading frame over the weighted fiber. `wFiber_emergence_pricing` imports coverage
-- through the candidate-valued `argmaxFrame`; `wPredFrame` reads the heaviest candidate's
-- prediction
-- of the base instead, so the coverage comes off the base coordinate and
-- `surjective_wPredFrame_of_faithful` discharges it from a candidate decoding to a surjective base
-- rule. Its settled antecedent is a fixed point of the construction's own predictive fitness
-- (`wGen_settled_of_faithful`) rather than a configuration a variation rule imposes, and over that
-- family of initial states the two frames separate: the candidate reading is constant, the
-- base reading surjective (`wFrames_separate_of_settled`). The family is not a convenience — under
-- the same hypotheses the candidate frame's coverage over ALL initial states can hold
-- (`surjective_argmaxFrame_of_all_faithful`). Coverage and convergence stay independent: neither
-- discharges the other, and nothing here shows selection reaches the settled configuration from an
-- arbitrary weight vector. No numbered result.

set_option linter.style.longLine false in
/-- info: 'ALT.wGen_settled_of_faithful' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.wGen_settled_of_faithful

set_option linter.style.longLine false in
/-- info: 'ALT.surjective_argmaxFrame_of_all_faithful' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.surjective_argmaxFrame_of_all_faithful

set_option linter.style.longLine false in
/-- info: 'ALT.surjective_wPredFrame_of_faithful' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.surjective_wPredFrame_of_faithful

set_option linter.style.longLine false in
/-- info: 'ALT.wFrames_separate_of_settled' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.wFrames_separate_of_settled

set_option linter.style.longLine false in
/-- info: 'ALT.wPredFrame_emergence_pricing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.wPredFrame_emergence_pricing

set_option linter.style.longLine false in
/-- info: 'ALT.wPredFrame_emergence_pricing_of_faithful' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.wPredFrame_emergence_pricing_of_faithful

-- §3.5 robustness of the exclusion (FV-22): moving decoders and the price of a frame. The update
-- restricts to a bijection on the recurrent core; the core is the exact ceiling on what ANY
-- time-dependent lens family can carry (Proposition 3.5, both halves); the static capacity of
-- Corollary 3.3 sits below it, with rotate-left the total-gap witness; a maximal family's first two
-- frames determine the world's recurrent rule; and eventual persistence relocates the read-only
-- requirement to the ω-limit set rather than removing it. The finite-image machinery (`Set.ncard`,
-- `Nat.card`, `Function.invFunOn`) is classical, so these carry the full standard axiom set.
/-- info: 'ALT.core_bijOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.core_bijOn

/-- info: 'ALT.capacity_horizon_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.capacity_horizon_le

/-- info: 'ALT.capacity_horizon_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.capacity_horizon_ge

/-- info: 'ALT.capacity_core' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.capacity_core

/-- info: 'ALT.capacity_core_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.capacity_core_iff

/-- info: 'ALT.static_le_moving' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.static_le_moving

/-- info: 'ALT.rotate_gap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.rotate_gap

/-- info: 'ALT.lens_bijOn_core' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.lens_bijOn_core

/-- info: 'ALT.ledger' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.ledger

/-- info: 'ALT.ledger_determines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.ledger_determines

-- The ledger in complexity form: the world's recurrent rule, tabulated on the core, is recovered
-- from the observer's first two frames by ONE fixed program, so its additive Kolmogorov complexity
-- is bounded by theirs plus a constant independent of the world, the lens, the enumerations and the
-- memory size.
/-- info: 'ALT.ledger_K' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.ledger_K

-- §3.5, the two relaxations. Eventual persistence: majority-vote write-back on three copies
-- overwrites every cell (no static model) yet repairs itself — the recurrent core is exactly the
-- consensus set and one bit persists. Descent: a decoded model obeys a law of its own iff the
-- lens's fibres are update-invariant (the substitution property of Hartmanis–Stearns 1966), of
-- which the Decoupling Lemma is the identity-law case — and that identification, being pure
-- shared-memory algebra, needs no axioms at all.
/-- info: 'ALT.majority_selfRepair' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.majority_selfRepair

/-- info: 'ALT.descent_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.descent_iff

/-- info: 'ALT.decoupling_is_identity_law' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.decoupling_is_identity_law

set_option linter.style.longLine false in
/-- info: 'ALT.eventual_decoupling_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.eventual_decoupling_iff

-- The serialization's codes grow at `1 + 4√3 ≈ 7.928` per node, below the `8` its three bits
-- could carry: a node-counted refinement of `card_KE_le`, via a truncated-Cauchy-square bound on
-- the counting generating function's singularity.
/-- info: 'ALT.card_codesOfNodes_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.card_codesOfNodes_le

-- The data rate of `KE` is bounded away from one bit per bit: no constant makes
-- `KE x ≤ (1 + 1/500) · Nat.size x + c` for every `x`, hence no constant makes `KE` an ideal code
-- even for its own computable measures.
/-- info: 'ALT.KE_data_rate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.KE_data_rate

-- [Persistence] §4, the static stratum. A lens with `ℓ ∘ U = ℓ` is exactly a function constant on
-- the components of the transition graph — an equivalence between a dynamical condition and a
-- combinatorial one, proved by induction over the generated equivalence, hence axiom-free. The
-- hierarchy then places the components: read-only cells ≤ components ≤ recurrent core.
/-- info: 'ALT.staticLens_factors' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.staticLens_factors

/-- info: 'ALT.hierarchy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.hierarchy

-- [Persistence] §5, the budgeted capacity `C_b`: the largest model carried by a family whose every
-- frame's core table costs at most `b` bits. It is capped by the recurrent core at every budget and
-- reaches the static levels of §4 at a finite one — the sandwich.
/-- info: 'ALT.Cb_le_core' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.Cb_le_core

/-- info: 'ALT.capacity_sandwich' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.capacity_sandwich

-- [Persistence] §7, the fiber-uniform counting over the symmetric group. Permutations act on lenses
-- by relabelling; the stabilizer of a lens is the product of the symmetric groups of its fibers, so
-- its orbit — exactly the lenses with its fiber sizes — has `n ! / ∏ᵢ (fiberᵢ) !` elements, and the
-- balanced count is `N_bal = n ! / ((n / m) !) ^ m`.
/-- info: 'ALT.card_stabilizer_lens' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.card_stabilizer_lens

-- [Persistence] §8, Corollary 8.11(i)'s own count: the permutations descending through a lens with
-- a given law are one coset of that lens's fiber-stabilizer, at a different translate — corrected
-- against §8's verification note, which had listed this as machine-checked already.
/-- info: 'ALT.card_descentCoset' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.card_descentCoset

/-- info: 'ALT.card_descentCoset_id' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.card_descentCoset_id

/-- info: 'ALT.mem_orbit_lens_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.mem_orbit_lens_iff

/-- info: 'ALT.card_balancedLenses' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.card_balancedLenses

-- [Persistence] §7, the collapse. A budget of `b` bits describes at most `2 ^ (b + 1)` frames, each
-- pulled back to one coset of the stabilizer, so at most `2 ^ (b + 1) · ∏ᵢ (fiberᵢ) !` worlds have
-- an affordable relabelled frame; and the ledger forces the second frame of ANY family carrying the
-- model to be exactly that relabelling. Hence all but a `2 ^ (b + 1) / N_bal` fraction of worlds
-- admit no affordable moving decoder at all.
/-- info: 'ALT.collapse_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.collapse_count

/-- info: 'ALT.collapse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.collapse

/-- info: 'ALT.Balanced.collapse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.Balanced.collapse

/-- info: 'ALT.collapse_generic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.collapse_generic

-- [Persistence] §7, Corollary 7.4 (the Kraft union, logs cleared): summing the per-frame count
-- (`collapse_union_frame`, division-free via `collapse_fraction` + `Nat.log`) over ALL reference
-- frames at once. Sound across lenses of different label counts because `lensCode` is jointly
-- injective on surjective lenses (`lensCode_codomain_of_surjective`), so the Kraft inequality
-- bounds
-- the whole sum — generically an observer's two-frame budget must cover its carried entropy.
set_option linter.style.longLine false in
/-- info: 'ALT.lensCode_codomain_of_surjective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.lensCode_codomain_of_surjective

/-- info: 'ALT.collapse_union_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.collapse_union_frame

/-- info: 'ALT.collapse_union' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.collapse_union

-- [Persistence] §5, Definition 5.4 + §7, Corollary 7.5(i) (the cap): the entropic capacity `CbH`,
-- valued in the reference frame's relabelling-class size `2 ^ E` (the `log₂` is paper-side, as with
-- `Cb`), is generically pinned at `2b + d + 2` bits — the Kraft union `collapse_union` applied to a
-- family realizing the attained supremum. An observer keeps, to within a factor two, exactly the
-- entropy it pays for.
/-- info: 'ALT.CbH_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.CbH_mono

/-- info: 'ALT.CbH_le_factorial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.CbH_le_factorial

/-- info: 'ALT.CbH_collapse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.CbH_collapse

/-- info: 'ALT.exists_perm_CbH_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.exists_perm_CbH_le

-- [Persistence] §5, Proposition 5.3 (the combinatorial half) + §7, Corollary 7.5(i) (the floor):
-- `r` marks riding the world carry entropy `log₂ (n ! / (n − r)!)` over EVERY permutation world.
-- `smul_markingLens` is the structural step — each frame is itself a marking lens, so Proposition
-- 5.3's per-frame price is one bound uniform over the marks, which `CbH_ge_marking` consumes as a
-- named hypothesis (the explicit-code discharge is not part of this bundle).
/-- info: 'ALT.smul_markingLens' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.smul_markingLens

set_option linter.style.longLine false in
/-- info: 'ALT.permCarries_pow_smul_markingLens' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.permCarries_pow_smul_markingLens

/-- info: 'ALT.prod_fiber_marking' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.prod_fiber_marking

/-- info: 'ALT.CbH_ge_marking' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.CbH_ge_marking

-- Proposition 5.3's price, discharged as an explicit code: the marking lens's tabulation is loaded
-- by ONE fixed builder from a base-`n` numeral of the marks, at `O ((r + 1) · log₂ n)` bits,
-- uniformly over where the marks sit (`KE_markingLens_le`) — and the floor that consumes it, with
-- no named price left (`CbH_ge_marking'`).

/-- info: 'ALT.KE_markingLens_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.KE_markingLens_le

/-- info: 'ALT.CbH_ge_marking'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.CbH_ge_marking'

-- T27, the graded ledger ([Persistence] Open problem 8.4's design). Theorem 6.3's ledger
-- generalized to EVERY carried family, maximal or not: the two frames pin `U` down only to a coset
-- of `ℓ₀`'s fiber-stabilizer, and the coset's counting halves (`orbitCard_ge_choose`,
-- `card_le_marks_succ`), the general-label marking price (`KE_labelledMarkingLens_le`), the graded
-- ledger itself (`ledger_graded`, with its non-vacuity check `ledger_graded_faithful`), and the
-- capstone (`CbH_le_pointwise`) assemble the marking-anatomy pole of the open problem.
/-- info: 'ALT.orbitCard_ge_choose' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.orbitCard_ge_choose

set_option linter.style.longLine false in
/-- info: 'ALT.orbitCard_eq_choose_of_two_fiber' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.orbitCard_eq_choose_of_two_fiber

/-- info: 'ALT.card_le_marks_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.card_le_marks_succ

set_option linter.style.longLine false in
/-- info: 'ALT.KE_labelledMarkingLens_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.KE_labelledMarkingLens_le

/-- info: 'ALT.ledger_graded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.ledger_graded

/-- info: 'ALT.ledger_graded_faithful' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.ledger_graded_faithful

-- [Persistence] §8, Corollary 8.11(i): the factor ledger's display, `ledger_graded`'s own decoder
-- at a different coset — `κ`'s table, `W`'s table, and an index into the descent set in place of
-- the two carried frames.
/-- info: 'ALT.ledger_descent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.ledger_descent

-- Remark 6.6: the paired frame — an address is paid once. The paired frame as a lens
-- (`pairLens`), its projections and descent-transport clause, the zip bound
-- (`KE_lensCode_pairLens_le`), and the graded ledger read at the paired frame instead of the two
-- separate frames (`ledger_graded_paired`, with `ledger_graded_paired_faithful` its non-vacuity
-- check at singleton fibres).

/-- info: 'ALT.pairLens_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.pairLens_left

/-- info: 'ALT.pairLens_right' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.pairLens_right

/-- info: 'ALT.pairLens_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.pairLens_comp

/-- info: 'ALT.pairLens_descends_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.pairLens_descends_iff

/-- info: 'ALT.zipLists_eq_lensTable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.zipLists_eq_lensTable

/-- info: 'ALT.zipTableFn_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.zipTableFn_eq

set_option linter.style.longLine false in
/-- info: 'ALT.KE_lensCode_pairLens_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.KE_lensCode_pairLens_le

set_option linter.style.longLine false in
/-- info: 'ALT.UniformBudget.pairLens_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.UniformBudget.pairLens_le

/-- info: 'ALT.ledger_graded_paired' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.ledger_graded_paired

set_option linter.style.longLine false in
/-- info: 'ALT.ledger_graded_paired_faithful' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.ledger_graded_paired_faithful

set_option linter.style.longLine false in
/-- info: 'ALT.UniformBudget.ledger_paired_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.UniformBudget.ledger_paired_le

/-- info: 'ALT.CbH_le_pointwise' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.CbH_le_pointwise

-- Renting versus owning a reading. The uniform budget of Definition 5.1's uniform variant — one
-- program computing every frame — with the frame-cost reduction that prices frame `t` at
-- `b + O (log t)` (`UniformBudget.frame_cost`), the uniform entropic capacity `CbHu`, and its
-- collapse cap. The cap is horizon-free: the collapse reads frames 0 and 1 only, whose clock inputs
-- are constants, so the reduction's `O (log t)` never grows (`CbHu_collapse`).

set_option linter.style.longLine false in
/-- info: 'ALT.UniformBudget.frame_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.UniformBudget.frame_cost

/-- info: 'ALT.CbHu_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.CbHu_mono

/-- info: 'ALT.CbHu_le_factorial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.CbHu_le_factorial

/-- info: 'ALT.CbHu_collapse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.CbHu_collapse

-- The ownership construction (Proposition 8.1's form in the permutation setting): table transport
-- along the world's own table, iterated by a fixed builder, turning codes for the reading's and the
-- world's tables into a uniform budget for the canonical family.

/-- info: 'ALT.permCarries_smul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.permCarries_smul

/-- info: 'ALT.ownIter_lensTable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.ownIter_lensTable

/-- info: 'ALT.ownership' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.ownership

-- The multiplicative congruential world `x ↦ a · x mod m` — the division-remainder pseudo-random
-- generator — as an explicit cheap-dynamics instance: priced at `O (log m)` bits by the builder
-- idiom (`KE_lcgWorld_le`), and the reading owned over it forever (`CbHu_ge_lcg`).

/-- info: 'ALT.KE_lcgWorld_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.KE_lcgWorld_le

/-- info: 'ALT.CbHu_ge_lcg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.CbHu_ge_lcg

-- Faithful self-reading, priced in both directions. Owning a bijective reading costs a code for the
-- world's table and an absolute constant (`faithful_ownership`, the identity frame rebuilt free
-- from
-- the world's table by `faithTableFn`); conversely any owned faithful family hands the world's rule
-- back at twice its budget (`faithful_rule_cost`, over the ledger's inverter `invcomp_permFrames`).
-- The capstone is the equality: where the rule is affordable, the uniform capacity is exactly
-- `n !`.

/-- info: 'ALT.faithTableFn_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.faithTableFn_eq

/-- info: 'ALT.faithful_ownership' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.faithful_ownership

/-- info: 'ALT.invcomp_permFrames' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.invcomp_permFrames

/-- info: 'ALT.faithful_rule_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.faithful_rule_cost

set_option linter.style.longLine false in
/-- info: 'ALT.UniformBudget.faithful_rule_cost_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.UniformBudget.faithful_rule_cost_le

/-- info: 'ALT.prod_fiber_bijective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.prod_fiber_bijective

/-- info: 'ALT.CbHu_attains_ceiling' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.CbHu_attains_ceiling

-- Capacity out to a horizon: the capacities of Definitions 5.4 and 5.5 with the persistence
-- identity
-- and the budget demanded only up to `T`. The collapse's cap is unchanged at every `T ≥ 1` (it
-- reads
-- frames 0 and 1 only), and the horizon is what makes the uniform→per-frame comparison true at all
-- —
-- the clock costs `O (log T)`, so the horizon-free form of that comparison does not hold.

set_option linter.style.longLine false in
/-- info: 'ALT.PermCarriesUpTo.frame_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.PermCarriesUpTo.frame_one

/-- info: 'ALT.CbHUpTo_antitone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.CbHUpTo_antitone

/-- info: 'ALT.CbH_le_CbHUpTo' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.CbH_le_CbHUpTo

/-- info: 'ALT.CbHUpTo_collapse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.CbHUpTo_collapse

set_option linter.style.longLine false in
/-- info: 'ALT.UniformBudgetUpTo.frame_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.UniformBudgetUpTo.frame_cost

/-- info: 'ALT.CbHuUpTo_le_CbHUpTo' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.CbHuUpTo_le_CbHUpTo

-- A carried family over a permutation world is determined by its reference frame and repeats with
-- the world's period, so an owner's clock never counts past `orderOf U ≤ n !` — and the uniform to
-- per-frame comparison holds with no horizon at all, at cost `O (log n !)` (`CbHu_le_CbH`).

-- Choice-free: solving the persistence identity for `ℓ t` is pure rewriting.
/-- info: 'ALT.PermCarries.frame_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.PermCarries.frame_eq

/-- info: 'ALT.PermCarries.frame_mod' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.PermCarries.frame_mod

/-- info: 'ALT.CbHu_le_CbH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.CbHu_le_CbH

-- Product worlds: the disjoint union of two worlds, whose block action needs the two evaluation
-- lemmas (the transport along `finSumFinEquiv` does not compute). Rules compose, so the cheap
-- dynamics regime is closed under disjoint union (`KE_unionWorld_le`); and capacities are
-- superadditive (`CbHu_unionWorld_ge`), the merged fibre profile of the block-pair lens carrying
-- the orbit arithmetic. A union world is structured by construction — the generic caps do not
-- speak about it.

/-- info: 'ALT.unionWorld_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.unionWorld_left

/-- info: 'ALT.unionWorld_right' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.unionWorld_right

/-- info: 'ALT.lensTable_unionWorld' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.lensTable_unionWorld

/-- info: 'ALT.unionTableFn_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.unionTableFn_eq

/-- info: 'ALT.KE_unionWorld_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.KE_unionWorld_le

/-- info: 'ALT.PermCarries.unionLens' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.PermCarries.unionLens

set_option linter.style.longLine false in
/-- info: 'ALT.UniformBudget.unionLens' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.UniformBudget.unionLens

/-- info: 'ALT.prod_fiber_unionLens' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.prod_fiber_unionLens

/-- info: 'ALT.CbHu_unionWorld_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.CbHu_unionWorld_ge

-- Cartesian product worlds: two worlds turning at once on pairs of states, the `Fin (n₁ * n₂)`
-- instance transported along `finProdFinEquiv` (so its coordinate action, like the union's, needs
-- an evaluation lemma). Rules compose with NO size parameter at all — each table is as long as its
-- own state space (`KE_prodWorldFin_le`). A reading of one factor lifts through the projection,
-- keeping both its persistence and its intertwining square — the square lift is axiom-free, the
-- product's first coordinate evolving by `U₁` and by nothing else. Conversely a FAITHFUL reading of
-- the whole product hands back each factor's rule at twice the budget
-- (`KE_factorFst_le_of_faithful`
-- / `KE_factorSnd_le_of_faithful`): the contrast between a cheap sub-system and an unaffordable
-- whole. Capacity projects through the lift by equivariance (`CbHu_prodWorldFin_ge_fst`).

/-- info: 'ALT.prodWorld_iterate' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.prodWorld_iterate

/-- info: 'ALT.prodWorldFin_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.prodWorldFin_apply

/-- info: 'ALT.prodWorldFin_pow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.prodWorldFin_pow

/-- info: 'ALT.lensTable_prodWorldFin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.lensTable_prodWorldFin

/-- info: 'ALT.prodTableFn_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.prodTableFn_eq

/-- info: 'ALT.KE_prodWorldFin_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.KE_prodWorldFin_le

/-- info: 'ALT.Carries.prodLensFst' depends on axioms: [propext, Classical.choice] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.Carries.prodLensFst

/-- info: 'ALT.Intertwines.prodLensFst' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.Intertwines.prodLensFst

set_option linter.style.longLine false in
/-- info: 'ALT.PermCarries.prodLensFinFst' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.PermCarries.prodLensFinFst

set_option linter.style.longLine false in
/-- info: 'ALT.UniformBudget.prodLensFinFst' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.UniformBudget.prodLensFinFst

/-- info: 'ALT.splitFstFn_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.splitFstFn_eq

/-- info: 'ALT.splitSndFn_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.splitSndFn_eq

set_option linter.style.longLine false in
/-- info: 'ALT.KE_factorFst_le_of_faithful' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.KE_factorFst_le_of_faithful

set_option linter.style.longLine false in
/-- info: 'ALT.KE_factorSnd_le_of_faithful' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.KE_factorSnd_le_of_faithful

/-- info: 'ALT.liftFst_smul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.liftFst_smul

set_option linter.style.longLine false in
/-- info: 'ALT.CbHu_prodWorldFin_ge_fst' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.CbHu_prodWorldFin_ge_fst

-- The recursive-majority block: the majority world compounded with itself `k` times, on `3 ^ k`
-- cells. The decoder recurses (majority of the three sub-block decodes, split along `tripleEquiv`);
-- the encoder does not — a recursively triplicated constant IS the constant function, so there are
-- exactly two codewords at every depth and the block carries one bit. The heart is
-- `decRec_healing`: fewer than `2 ^ k` corrupted cells cannot change the decode, because a budget
-- below `2 · 2 ^ k` splits three ways (`hammingDist_split`, proved by counting through the index
-- equivalence) and at most ONE sub-block can be handed `2 ^ k`. The world is its own decoder
-- (`healWorld`): every state lands on a codeword in one step, so the basin is everything and the
-- transient is one. The margin is EXACTLY `2 ^ k - 1` (`recMaj_margin_eq`) — the healing radius
-- from below, the recursive adversarial pattern `advRec` from above.

/-- info: 'ALT.decRec_encRec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.decRec_encRec

/-- info: 'ALT.hammingDist_split' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.hammingDist_split

/-- info: 'ALT.decRec_healing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.decRec_healing

/-- info: 'ALT.healWorld_heals' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.healWorld_heals

set_option linter.style.longLine false in
/-- info: 'ALT.healWorld_mem_codewords' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.healWorld_mem_codewords

/-- info: 'ALT.healWorld_idem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.healWorld_idem

/-- info: 'ALT.healWorld_fixed_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.healWorld_fixed_iff

/-- info: 'ALT.core_healWorld' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.core_healWorld

/-- info: 'ALT.settlesValue_healWorld' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.settlesValue_healWorld

/-- info: 'ALT.surjOn_decRec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.surjOn_decRec

/-- info: 'ALT.recMaj_hasMargin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.recMaj_hasMargin

/-- info: 'ALT.recMaj_margin_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.recMaj_margin_ge

/-- info: 'ALT.hammingDist_advRec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.hammingDist_advRec

/-- info: 'ALT.decRec_advRec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.decRec_advRec

/-- info: 'ALT.recMaj_not_hasMargin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.recMaj_not_hasMargin

/-- info: 'ALT.recMaj_margin_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.recMaj_margin_eq

/-- info: 'ALT.recMaj_margin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.recMaj_margin

-- The witness world: `κ` recursive-majority blocks running a macro law `G`, beside an environment
-- running an arbitrary `π`, sharing nothing. A product of memories is a memory on the disjoint
-- union
-- of their indices (`sumMem`), so the whole world has a cell structure and `hammingDist` splits
-- across the two parts (`hammingDist_sum_index`). The square is EXACT and needs no hypothesis on
-- the
-- state (`witness_square`) — the update writes codewords whatever it was handed — so the reading
-- follows `G`'s own trajectory from step zero, from EVERY initial state (`witnessLens_iterate`);
-- the
-- state takes one step to become a codeword state, the reading never needed to. The margin is the
-- block's, at every radius below `2 ^ k`, however large the environment (`witnessWorld_hasMargin`):
-- the reading ignores the environment's cells. `habitat_heals`'s hypothesis is distance to a
-- CODEWORD state and must be — between arbitrary states the claim is false at `k = 1`, where
-- `(0,0,1)` and `(0,1,1)` are one cell apart and decode oppositely; the attractor consists of
-- codeword states (`omegaLimit_witnessWorld_subset`), which is where the margin reads it.

/-- info: 'ALT.hammingDist_sum_index' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.hammingDist_sum_index

/-- info: 'ALT.macroLens_habitatEnc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.macroLens_habitatEnc

set_option linter.style.longLine false in
/-- info: 'ALT.hammingDist_habitat_blocks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.hammingDist_habitat_blocks

/-- info: 'ALT.habitat_heals' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.habitat_heals

/-- info: 'ALT.habitatWorld_forgets' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.habitatWorld_forgets

/-- info: 'ALT.macroLens_surjective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.macroLens_surjective

/-- info: 'ALT.macro_square' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.macro_square

/-- info: 'ALT.intertwines_macroLens' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.intertwines_macroLens

/-- info: 'ALT.witnessWorld_conj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.witnessWorld_conj

/-- info: 'ALT.witness_square' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.witness_square

set_option linter.style.longLine false in
/-- info: 'ALT.intertwines_witnessLens' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.intertwines_witnessLens

/-- info: 'ALT.witnessLens_surjective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.witnessLens_surjective

set_option linter.style.longLine false in
/-- info: 'ALT.omegaLimit_witnessWorld_subset' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.omegaLimit_witnessWorld_subset

/-- info: 'ALT.witnessWorld_hasMargin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.witnessWorld_hasMargin

/-- info: 'ALT.witnessLens_iterate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.witnessLens_iterate

set_option linter.style.longLine false in
/-- info: 'ALT.witnessWorld_valid_after_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.witnessWorld_valid_after_one

/-- info: 'ALT.witnessWorld_rejoins' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.witnessWorld_rejoins

/-- info: 'ALT.witnessWorld_margin_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.witnessWorld_margin_ge

/-- info: 'ALT.witness_world_hosts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.witness_world_hosts

-- The pricing bridge: the combinatorics above lives on `Mem ι V`, where a perturbation is a number
-- of cells; the pricing stack lives on `Fin n`, where `n` counts STATES, because that is what a
-- table is indexed by. `stateEquiv` packs a memory state into the numeral its cells spell — cell
-- `i`
-- at weight `2 ^ i`, cell `0` the low bit, the convention of `packMarks` and of Mathlib's
-- `finFunctionFinEquiv`, so `stateEquiv_digit` is the marking price's own digit lemma at base two.
-- `packWorld` transports any memory world onto the priced carrier and respects composition,
-- identity and iteration, so orbits survive; `packPerm` supplies the permutation the `Perm`-carrier
-- results ask for, and `packWorld_square` carries an intertwining square across intact. The bridge
-- makes the witness world EXPRESSIBLE in the pricing vocabulary; exhibiting a short program for its
-- table needs a numeral-level decoder, which is not built here.

/-- info: 'ALT.stateEquiv_val' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.stateEquiv_val

/-- info: 'ALT.stateEquiv_digit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.stateEquiv_digit

/-- info: 'ALT.packWorld_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.packWorld_comp

/-- info: 'ALT.packWorld_id' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.packWorld_id

/-- info: 'ALT.packWorld_iterate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.packWorld_iterate

/-- info: 'ALT.packPerm_coe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.packPerm_coe

/-- info: 'ALT.packLens_surjective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.packLens_surjective

/-- info: 'ALT.packWorld_square' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.packWorld_square

-- The bottom-up anchor. `decRec` recurses top-down, splitting the MOST-significant base-3 digit
-- (`tripleEquiv_val`: sub-block `c` sits at `i + 3 ^ k · c`) and making THREE recursive calls.
-- `reduceBot` collapses the LEAST-significant digit instead — each adjacent triple to its majority
-- —
-- and `decRec_bottomUp` says the two orders agree: both evaluate the same ternary majority tree,
-- one
-- from the root, one from the leaves. That matters because a bottom-up decode makes ONE recursive
-- call on a shrinking argument, which is the shape primitive recursion offers; the anchor licenses
-- reading the tree that way without changing what it computes. The whole proof is
-- `subBlock_reduceBot` — top blocks commute with the bottom reduction — which isolates the index
-- arithmetic `3 · (i + 3 ^ k · c) + r = (3 · i + r) + 3 ^ (k+1) · c` and nothing else.

/-- info: 'ALT.tripleEquiv_val' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.tripleEquiv_val

/-- info: 'ALT.subBlock_reduceBot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.subBlock_reduceBot

/-- info: 'ALT.decRec_bottomUp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.decRec_bottomUp

-- The numeral decoder. Majority of three BITS is halving their sum (`maj3_natBit`, all eight cases,
-- axiom-free) — which keeps the numeral arithmetic free of `Bool`. `packReduce` is `reduceBot` on
-- numerals, and `packReduce_stateEquiv` is the ONLY crossing of the memory/numeral boundary: term-
-- wise, no induction, both sides `∑ j ∈ range (3 ^ k), d j · 2 ^ j` with `stateEquiv_digit`
-- identifying each bit with its cell. `numDecRec` then collapses `k` times and reads the low bit —
-- one recursive call per level, the shape `decRec_bottomUp` licenses — and `numDecRec_stateEquiv`
-- bridges it to `decRec`, each induction step being the square then the anchor and nothing else.

/-- info: 'ALT.maj3_natBit' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.maj3_natBit

/-- info: 'ALT.packReduce_stateEquiv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.packReduce_stateEquiv

/-- info: 'ALT.numDecRec_stateEquiv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.numDecRec_stateEquiv

-- The decoder as a PROGRAM. `packReduce` is primitive recursive once its `Finset.range` sum becomes
-- a `List` fold (the `markVal` idiom) — its bit extraction is `digitAt` at base two, literally.
-- `numDecRec` recurses on the depth with a CHANGING argument, which `Primrec.nat_rec` does not
-- offer; `numDecIter` carries `(remaining depth, numeral)` as the accumulator, which fits, and
-- `numDecIter_read` says the two agree. The induction closes only by peeling the iteration from the
-- FRONT (`Function.iterate_succ_apply`): peeling from the back leaves the initial depth mismatched
-- against the recursion's own counter. `decBuilder` is then the `markBuilder` idiom verbatim — one
-- program on `⟨depth, packed state⟩` — and `eval_decBuilder_stateEquiv` runs it on a packed memory
-- to return the bit `decRec` reads there.

/-- info: 'ALT.primrec_packReduce' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.primrec_packReduce

/-- info: 'ALT.numDecIter_read' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.numDecIter_read

/-- info: 'ALT.primrec_numDecIter' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.primrec_numDecIter

/-- info: 'ALT.primrec_numDecRec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.primrec_numDecRec

/-- info: 'ALT.eval_decBuilder' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.eval_decBuilder

set_option linter.style.longLine false in
/-- info: 'ALT.eval_decBuilder_stateEquiv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.eval_decBuilder_stateEquiv

-- The habitat on flat cells. `flatHab` relabels block `i`, position `p` to the flat cell
-- `p + 3 ^ k * i` — `finProdFinEquiv`'s convention, the same `tripleEquiv` uses one level down, so
-- both levels agree about which index is significant without anything being chosen twice. Packed
-- little-endian, a habitat state is then a base-`2 ^ 3 ^ k` numeral whose digit `i` IS the packed
-- block `i` (`stateEquiv_flatHab_blocks`), so extracting a block is extracting a digit and
-- `stateEquiv_flatHab_block` is the marking price's digit lemma at a third base (base `n` for the
-- marks, base two for a memory's cells, base `2 ^ 3 ^ k` for a habitat's blocks).
-- `numDecRec_block` is where the two levels meet: extract digit `i`, run the decoder, out comes the
-- bit `macroLens` reads off block `i`.

set_option linter.style.longLine false in
/-- info: 'ALT.stateEquiv_flatHab_blocks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.stateEquiv_flatHab_blocks

set_option linter.style.longLine false in
/-- info: 'ALT.stateEquiv_flatHab_block' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.stateEquiv_flatHab_block

/-- info: 'ALT.numDecRec_block' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.numDecRec_block

-- The blocks' two constants and the macro word. A codeword block packs to all-ones
-- (`2 ^ 3 ^ k - 1`, the geometric sum) or zero (`stateEquiv_encRec`) — the two values a habitat
-- walk writes back. And decoding each block digit and assembling the results little-endian gives
-- exactly the packed macro reading (`macroWord_eq`): the regrouping lemma read backwards one level
-- up, per block the one-cell lemma, across blocks the same digit bookkeeping as everywhere in this
-- layer.

/-- info: 'ALT.stateEquiv_encRec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.stateEquiv_encRec

/-- info: 'ALT.macroWord_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.macroWord_eq

-- The habitat walk, computed on numerals. Three steps, each with its lemma already proved:
-- `macroWordOf` extracts the block digits, decodes each and assembles little-endian (`macroWord_eq`
-- says that is the packed macro reading); a lookup in the macro law's own packed table gives the
-- next macro state (`packWorld_apply`); `habWriteBack` writes the two constants back block by block
-- (`stateEquiv_encRec`), reassembled by `stateEquiv_flatHab_range`. `habStep_stateEquiv` chains the
-- three and nothing else enters — every step was proved before the walk was written. The walk reads
-- the macro law only as the `2 ^ κ`-entry table of its packed form, one entry per state.

/-- info: 'ALT.macroWordOf_stateEquiv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.macroWordOf_stateEquiv

set_option linter.style.longLine false in
/-- info: 'ALT.habWriteBack_stateEquiv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.habWriteBack_stateEquiv

/-- info: 'ALT.habStep_stateEquiv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.habStep_stateEquiv

-- The walk is primitive recursive. No mathematics — the walk's meaning was settled by
-- `habStep_stateEquiv`; these say only that a program can carry it out, each following the shape
-- the marking price already uses (a bounded sum over `List.range` folded by `primrec_list_sum`,
-- with `/`, `%`, `^` doing the digit work). `macroWordOf` needs the decoder (`primrec_numDecRec`,
-- the pair-accumulator's payoff); `habWriteBack` needs only the two block constants; `habStep`
-- composes them either side of one table lookup.

/-- info: 'ALT.primrec_macroWordOf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.primrec_macroWordOf

/-- info: 'ALT.primrec_habWriteBack' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.primrec_habWriteBack

/-- info: 'ALT.primrec_habStep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.primrec_habStep

-- The habitat world on flat cells. `habitatWorld` lives on `Mem (Fin κ × Fin (3 ^ k)) Bool`; the
-- pricing layer indexes tables by states of a `Mem (Fin N) Bool`, so `flatWorld` is the same world
-- conjugated by the relabelling. `habStep_packWorld` is `habStep_stateEquiv` with both sides named:
-- the walk, run on a packed state, computes `packWorld (flatWorld κ k G)`. Every state of the flat
-- world is a packed habitat and conversely, so the two carry the same information — this one is in
-- the vocabulary a price is written in.

/-- info: 'ALT.flatWorld_flatHab' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.flatWorld_flatHab

/-- info: 'ALT.habStep_packWorld' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.habStep_packWorld

-- The habitat world, priced. Two elaboration walls dissolved once: `lensTable_range` re-lists a
-- table along `List.range` (proved at symbolic `n`) so a bridge to a `2 ^ (κ · 3 ^ k)`-length table
-- never unifies an index; and `habStep` is made irreducible so the `Primrec` proof matches at the
-- head instead of grinding its body. Then the marking-price assembly verbatim: `habTableFn`
-- tabulates the walk, `habTableFn_eq` identifies it with the packed flat world's table,
-- `eval_habBuilder` extracts the code, and `KE_flatWorld_le` prices the world of `2 ^ (κ · 3 ^ k)`
-- states at `elen cG + O(size κ + size k)` — the macro law fed as a CODE and composed, so its
-- length
-- is additive and nothing scales with the state count. The (U)-positive clause in world-table form.

/-- info: 'ALT.lensTable_range' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.lensTable_range

/-- info: 'ALT.primrec_habTableFn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.primrec_habTableFn

/-- info: 'ALT.habTableFn_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.habTableFn_eq

/-- info: 'ALT.eval_habBuilder' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.eval_habBuilder

/-- info: 'ALT.KE_flatWorld_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.KE_flatWorld_le

-- The packaged Witness World. `hostsThreshold_of_capacity` crosses the internalization threshold,
-- consuming
-- [Decoupling] §6.3's capacity polynomial as a black box. `KE_packWitnessWorld_le` prices the full
-- world — the flat habitat world beside an environment, via the endofunction product
-- `prodWorldFinFn`
-- and `prodBuilder` — at `elen cG + elen cπ + O(size κ + size k)`. `card_readable_core_le` is the
-- contrast: the environment permutations admitting a faithful reading of the core world are
-- exponentially few (`KE_factorSnd_le_of_faithful` extracts the environment's rule, `card_KE_le`
-- counts short descriptions). `witness_world` conjoins the five positive clauses into the statement
-- of
-- record — surjective, `G`-lawful from every state, margin `2 ^ k − 1`, cheaply owned, above the
-- threshold — for every member of the class.

set_option linter.style.longLine false in
/-- info: 'ALT.hostsThreshold_of_capacity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.hostsThreshold_of_capacity

/-- info: 'ALT.KE_packWitnessWorld_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.KE_packWitnessWorld_le

/-- info: 'ALT.card_readable_core_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.card_readable_core_le

/-- info: 'ALT.witness_world' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.witness_world

-- The (U)-positive clause in the capacity vocabulary and the core identification.
-- `CbHue_flatWorld_ge`: when the macro law is a permutation, the flat world's uniform entropic
-- capacity at `elen cG + O(size κ + size k)` is at least the reading's carried entropy — one
-- program
-- reads the macro state back forever (`ownLens` carries the model, `readBuilder` supplies the
-- decoder
-- from `⟨κ, k⟩` alone). `omegaLimit_witnessWorld_eq`: for permutation `G, π` the recurrent core is
-- exactly the codeword-habitat states; `witnessWorld_codeword` is the recurrent dynamics on them —
-- the explicit product permutation `(enc ∘ G ∘ dec) × π`.

/-- info: 'ALT.CbHue_flatWorld_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.CbHue_flatWorld_ge

set_option linter.style.longLine false in
/-- info: 'ALT.omegaLimit_witnessWorld_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.omegaLimit_witnessWorld_eq

/-- info: 'ALT.witnessWorld_codeword' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.witnessWorld_codeword

-- Emergence: pricing the ceiling of [Decoupling] §3.5. `CbHu_ge_owned` is the reversible case — a
-- surjective owned frame over a permutation host is affordable via `ownership` +
-- `CbHu_ge_of_uniform`.
-- `emergence` is the endofunction case: on the recurrent core `U` has order dividing `n !`, so its
-- inverse there is a forward power and the co-move-after-flow-in guest collapses to `θ ∘ U^[k]`,
-- computed by `emergeBuilder` (`iterTable` + `stepComp`, no core inverse) — an owned guest, lawful
-- from every initial state, at `elen cU + elen cθ + O(1)`.

/-- info: 'ALT.CbHu_ge_owned' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.CbHu_ge_owned

/-- info: 'ALT.emergence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.emergence

-- The skew-product fiber: `emergence` applied to a host whose fiber evolves. `skewWorldFin` runs a
-- base rule and a base-driven fiber rule on one carrier; `skewBuilder` weaves the two tables, so
-- the
-- world's code is the two rules' codes composed (`KE_skewWorldFin_le`) rather than its own
-- exponential table. `fiber_emergence_pricing` instantiates the fiber with one generation of
-- variation and selection over a population of candidate codewords and prices the fittest reading
-- at
-- `elen cS + elen cF + elen cθ + O(1)`, taking the fiber's convergence as a named hypothesis;
-- `surjective_fittestFrame_of_fixed` exhibits a configuration meeting that hypothesis, so the
-- pricing is not vacuous. No numbered result.

/-- info: 'ALT.KE_skewWorldFin_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.KE_skewWorldFin_le

set_option linter.style.longLine false in
/-- info: 'ALT.fiber_emergence_pricing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.fiber_emergence_pricing

set_option linter.style.longLine false in
/-- info: 'ALT.surjective_fittestFrame_of_fixed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.surjective_fittestFrame_of_fixed

-- The base-reading frame, and why the frame is not a presentational choice.
-- `fiber_emergence_pricing`'s
-- imported hypothesis is a COVERAGE condition — the reading must take every value in its codomain
-- as
-- the initial state varies — and for a frame returning the fittest CODEWORD that competes with
-- settling: one fixed codeword from every initial state is a constant reading, refuting
-- surjectivity
-- once `2 ≤ C` (`not_surjective_fittestFrame_of_converged`). `predFrame` reads the fittest
-- candidate's
-- prediction of the base instead, so the coverage comes off the base coordinate, which the fiber
-- reads
-- but never writes (`base_iterate_skewWorldFin`); the same settling then leaves it standing
-- (`surjective_predFrame_of_converged`), and both halves hold of one overwriting dynamics
-- (`frames_separate_of_settled`), so neither implication is idle. `predFrame_emergence_pricing`
-- transports the assembly to the new frame at the same constant. Nothing here proves the fiber
-- settles under selection. No numbered result.

set_option linter.style.longLine false in
/-- info: 'ALT.not_surjective_fittestFrame_of_converged' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.not_surjective_fittestFrame_of_converged

set_option linter.style.longLine false in
/-- info: 'ALT.surjective_predFrame_of_faithful' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.surjective_predFrame_of_faithful

set_option linter.style.longLine false in
/-- info: 'ALT.surjective_predFrame_of_converged' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.surjective_predFrame_of_converged

set_option linter.style.longLine false in
/-- info: 'ALT.frames_separate_of_settled' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.frames_separate_of_settled

set_option linter.style.longLine false in
/-- info: 'ALT.predFrame_emergence_pricing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.predFrame_emergence_pricing

-- Basins: a region a permutation world never leaves is setwise invariant (`image_perm_eq`), so the
-- world restricts to a permutation of it and, transported along an enumeration, is a world of its
-- own. Carrying families correspond both ways, and the ledger's frame determination survives. The
-- capacity-level reduction is deliberately absent: transporting a table along the enumeration is an
-- explicit-code obligation, not a free one.

/-- info: 'ALT.image_perm_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.image_perm_eq

/-- info: 'ALT.mem_iff_apply_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.mem_iff_apply_mem

/-- info: 'ALT.pow_mem_of_closed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.pow_mem_of_closed

/-- info: 'ALT.subWorld_pow_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.subWorld_pow_apply

/-- info: 'ALT.PermCarriesOn.restrict' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.PermCarriesOn.restrict

/-- info: 'ALT.permCarriesOn_extend' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.permCarriesOn_extend

set_option linter.style.longLine false in
/-- info: 'ALT.PermCarriesOn.frame_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.PermCarriesOn.frame_one

-- the endofunction substrate: carrying, capacity and the dilated rule over a general world
-- ([Persistence] §2, Definitions 2.1-2.2; §3). `permCarries_iff_carries` is the alignment check --
-- the permutation predicate IS the general one at an invertible update -- and `CbHe_perm` /
-- `CbHue_perm` are the sanity bridge: the general capacities restrict to the permutation ones.
/-- info: 'ALT.Carries.coreLens_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.Carries.coreLens_eq

set_option linter.style.longLine false in
/-- info: 'ALT.Carries.frame_eqOn_core' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.Carries.frame_eqOn_core

/-- info: 'ALT.Carries.frame_zero_congr' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.Carries.frame_zero_congr

-- choice-free: the two predicates are one predicate, and `Equiv.Perm.coe_pow` is the only step.
/-- info: 'ALT.permCarries_iff_carries' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.permCarries_iff_carries

set_option linter.style.longLine false in
/-- info: 'ALT.card_orbit_mul_prod_fiber_card' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.card_orbit_mul_prod_fiber_card

/-- info: 'ALT.CbHe_le_core_factorial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.CbHe_le_core_factorial

/-- info: 'ALT.CbHe_perm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.CbHe_perm

/-- info: 'ALT.CbHue_perm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.CbHue_perm

-- the floor does not survive irreversibility ([Persistence] §7, Proposition 7.9(ii)): fold a
-- transient basin into a fixed cycle core and the generic entropic floor is gone, at every fixed
-- label count -- `basinWorld_confine` is the mechanism (a transient state's reference-frame
-- reading is pinned to one core fibre), `card_basinWorld_carries_le` the count it forces.
set_option linter.style.longLine false in
/-- info: 'ALT.card_basinWorld_carries_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.card_basinWorld_carries_le

/-- info: 'ALT.KE_iterate_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.KE_iterate_le

-- settling from a basin ([Persistence] §10.1, silent self-stabilization, read at §5's budget):
-- `iterate_mem_core` is the space transient (the state space bounds its own settling time);
-- `CbHev_eq_CbHeOn` is the reduction -- eventual capacity from a basin IS exact capacity on its
-- attractor; `CbHue_le_CbHe` compares the two budgets over an arbitrary endofunction, by replacing
-- the family with a clamped reindexing of itself rather than by arguing about the family given;
-- `eventual_descent_iff` is the general-law sibling of `eventual_decoupling_iff`.
/-- info: 'ALT.exists_image_stable_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.exists_image_stable_le

/-- info: 'ALT.iterate_mem_core' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.iterate_mem_core

/-- info: 'ALT.CarriesOn.restrict_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.CarriesOn.restrict_eq

/-- info: 'ALT.orbit_restrict_iterate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.orbit_restrict_iterate

/-- info: 'ALT.eventualEntropies_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.eventualEntropies_eq

/-- info: 'ALT.CbHev_eq_CbHeOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.CbHev_eq_CbHeOn

/-- info: 'ALT.CbHev_le_factorial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.CbHev_le_factorial

/-- info: 'ALT.CbHue_le_CbHe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.CbHue_le_CbHe

/-- info: 'ALT.eventual_descent_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.eventual_descent_iff

-- the tower ([Persistence] §10.2 + §2): `Intertwines.comp` composes squares and multiplies
-- dilations; `Intertwines.anchored` is the identity-law case (a square that carries a memory);
-- `UniformBudget.comp` adds the budgets through one fixed builder, the dilation charged its
-- bit-length; `tower_no_free_lunch`/`_perm` cap the whole tower by the ITERATED base world's
-- uniform capacity at the summed budget; `entropy_comp_le` makes entropy antitone up the levels.
/-- info: 'ALT.Intertwines.comp' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.Intertwines.comp

/-- info: 'ALT.Intertwines.anchored' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.Intertwines.anchored

/-- info: 'ALT.tower_carries' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.tower_carries

/-- info: 'ALT.compTableFn_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.compTableFn_eq

/-- info: 'ALT.UniformBudget.comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.UniformBudget.comp

/-- info: 'ALT.tower_no_free_lunch' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.tower_no_free_lunch

set_option linter.style.longLine false in
/-- info: 'ALT.tower_no_free_lunch_perm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.tower_no_free_lunch_perm

/-- info: 'ALT.entropy_comp_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.entropy_comp_le

-- The structural category of decoupled simulations (`ALT/DecoupledSimulation.lean`) — the domain
-- [Decoupling] §4.5 asks Conjecture 4.4's functor to start from. A morphism is a hosting square
-- (`Intertwines (U'^[τ]) U ℓ`) plus code-locality: the guest code the reading returns depends on
-- the host state only through the host's code region. STRUCTURAL ONLY — the resource grade on the
-- reading family, and the realizer transport it prices, are NOT here.
-- `code_time_indep`: the reading's code component is time-independent AUTOMATICALLY, from the
-- host's read-only property plus code-locality — no inhabitedness of the work region, no choice.
-- `Simulates.comp`: morphisms compose and dilations multiply, code-locality chaining with them —
-- with `Simulates.id` and the nontrivial `counter_simulates`, the category structure.
/-- info: 'ALT.code_time_indep' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.code_time_indep

/-- info: 'ALT.Simulates.comp' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.Simulates.comp

-- the robustness margin ([Persistence] §10.1 + §2): `hasMargin_iff` factors the margin condition
-- into basin fatness and local constancy; `hasMargin_margin` attains the supremum, so the margin
-- names a radius at which the reading really is robust; `repair_tax` prices a margin by sphere
-- packing in the memory; `majority_margin` is the worked robust sub-system, margin at least one.
/-- info: 'ALT.hasMargin_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.hasMargin_iff

/-- info: 'ALT.hasMargin_margin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.hasMargin_margin

/-- info: 'ALT.hammingDist_transport' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.hammingDist_transport

/-- info: 'ALT.repair_tax' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.repair_tax

/-- info: 'ALT.repair_tax_surjOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.repair_tax_surjOn

/-- info: 'ALT.majority_margin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.majority_margin

set_option linter.style.longLine false in
/-- info: 'ALT.repair_tax_tight_majWorld' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.repair_tax_tight_majWorld

-- §5 bounded recursor (FV-2)
/-- info: 'ALT.no_true_nno' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.no_true_nno

-- §6.3 internalization (FV-8) + §5.4 Prop 5.4
set_option linter.style.longLine false in
/-- info: 'ALT.BoundedChecker.decide_godel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.BoundedChecker.decide_godel

/-- info: 'ALT.capacity_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.capacity_bound

set_option linter.style.longLine false in
/-- info: 'ALT.proofcode_workspace_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.proofcode_workspace_bound

/-- info: 'ALT.prop_5_4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.prop_5_4

set_option linter.style.longLine false in
/-- info: 'ALT.BoundedChecker.internalization' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.BoundedChecker.internalization

-- §4 / §6.1 finite-set CCC (FV-10)
/-- info: 'ALT.reflective_satisfiable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.reflective_satisfiable

/-- info: 'ALT.exp_finite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.exp_finite

-- §5: the bounded recursor upgraded to a categorical UNIVERSAL PROPERTY, reusing
-- Mathlib's `CategoryTheory.Limits.IsInitial`. `recursorConeIsInitial` — the paper recursor is the
-- INITIAL object of the (thin) category of depth-≤M recursion cones (relativized, since
-- `no_true_nno`
-- forbids a true NNO on finite `W`); `recursorCone_canonical` — any other initial cone agrees with
-- it
-- on the orbit `N_M` (canonical, "not merely an orbit"). `Classical.choice` is genuine
-- (recursorCone
-- extracts the recursor via `Exists.choose`).
set_option linter.style.longLine false in
/-- info: 'ALT.ParamNNO.recursorConeIsInitial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.ParamNNO.recursorConeIsInitial

set_option linter.style.longLine false in
/-- info: 'ALT.ParamNNO.recursorCone_canonical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.ParamNNO.recursorCone_canonical

-- §5 sharpened: a GENUINE, discriminating initial algebra reusing Mathlib's
-- `CategoryTheory.Endofunctor.Algebra`. Unlike the thin/chaotic FV-17 cone category (where every
-- cone
-- is initial by `Subsingleton`), `boundedInitialAlgebraIsInitial` is initial with honest
-- algebra-hom
-- morphisms — uniqueness is a real orbit induction. It is initial only in the SATURATING
-- subcategory
-- (`no_true_nno`: the unrestricted initial `𝟙 ⊕ (·)`-algebra is `ℕ`);
-- `boundedAlg_str_not_injective`
-- records that the structure map is not iso, so Lambek does not force a fixed point here.
set_option linter.style.longLine false in
/-- info: 'ALT.TypeRecursorAlgebra.boundedInitialAlgebraIsInitial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.TypeRecursorAlgebra.boundedInitialAlgebraIsInitial

set_option linter.style.longLine false in
/-- info: 'ALT.TypeRecursorAlgebra.boundedAlg_str_not_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.TypeRecursorAlgebra.boundedAlg_str_not_injective

-- §4 / §6.1 unified CCC ∧ recursor on ONE carrier (FV-13)
set_option linter.style.longLine false in
/-- info: 'ALT.reflectiveAsmSatisfiable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.reflectiveAsmSatisfiable

-- §6 Consequence on the GENUINE single carrier (FV-13): the unified `ReflectiveAsm` ⟹
-- represents-an-underivable-truth, not the trivially-true `Type`-CCC stand-in of FV-5.
set_option linter.style.longLine false in
/-- info: 'ALT.ReflectiveAsm.representsUnderivableTruth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.ReflectiveAsm.representsUnderivableTruth

-- §6.1/§6.3 Theorem 6.2 as ONE machine-checked theorem on the genuine carrier (FV-15):
-- reflective object (Def 6.1) ∧ explicit capacity `2n` (FitsIn) ∧ §6.3 consequence, bundled.
/-- info: 'ALT.categorical_threshold' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.categorical_threshold

-- §6.4 Corollary 6.4: capacity stratification — the FV-15 object delivered at a work budget `w`
-- that hosts the threshold (monotone in `w`, entered at capacity `2n`, excluded below `n`).
/-- info: 'ALT.hostsAt_threshold' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.hostsAt_threshold

-- §6.1/§6.4 + [Inevitability] §2 Definition 2.1 — the threshold as a capacity-indexed MEMBERSHIP
-- condition (`ReflectiveWithin`): the vacuity guard first (it fails below the Gödel sentence's own
-- size, which the un-capacitated `ReflectiveAsm` cannot), then the entry point at capacity `2n`.
set_option linter.style.longLine false in
/-- info: 'ALT.not_reflectiveWithin_below_sentence_size' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.not_reflectiveWithin_below_sentence_size

set_option linter.style.longLine false in
/-- info: 'ALT.reflectiveWithin_at_capacity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.reflectiveWithin_at_capacity

-- [Inevitability] §6 Remark 6.4: the reflection ladder's capacity bound — a pigeonhole over
-- `not_reflectiveWithin_below_sentence_size`, then a non-vacuity witness at Gödel size 2.
/-- info: 'ALT.ladder_card_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.ladder_card_le

set_option linter.style.longLine false in
/-- info: 'ALT.ladder_card_le_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.ladder_card_le_nonvacuous

-- §6.5 Proposition 6.5 (FV-19): the reflective decision automaton — a shared-memory update whose
-- code cell is read-only (§3 Decoupling) and whose work cell runs the §6.3 bounded proof search,
-- halting on the §6 true-but-underivable Gödel sentence.
/-- info: 'ALT.BoundedChecker.step_fixes_code' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.BoundedChecker.step_fixes_code

/-- info: 'ALT.BoundedChecker.decodeCode_faithful' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.BoundedChecker.decodeCode_faithful

/-- info: 'ALT.BoundedChecker.decodeCode_nonconstant' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.BoundedChecker.decodeCode_nonconstant

/-- info: 'ALT.BoundedChecker.automaton_persists' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.BoundedChecker.automaton_persists

set_option linter.style.longLine false in
/-- info: 'ALT.BoundedChecker.automaton_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.BoundedChecker.automaton_run

set_option linter.style.longLine false in
/-- info: 'ALT.BoundedChecker.automaton_decides_godel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.BoundedChecker.automaton_decides_godel

-- §5 FV-18 ON THE GENUINE CARRIER ([Decoupling] §5.5): the endofunctor `X ↦ 𝟙 ⊕ X` on `Asm` (which
-- exists precisely because coproducts now do), and the discriminating initial `𝟙 ⊕ (·)`-algebra of
-- the saturating subcategory — the FV-18 headline restated on the SAME carrier `Asm` as the CCC and
-- the §6.3 checkers (no longer the `Type` stand-in). Honest algebra-hom morphisms (uniqueness a
-- real
-- orbit induction), initial only in the saturating subcategory (`no_true_nno`); the structure map
-- is
-- not injective (`boundedAlgAsm_str_not_injective`), so Lambek does not force a finite fixed point.
set_option linter.style.longLine false in
/-- info: 'ALT.AssemblyRecursorAlgebra.succEndoAsm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.AssemblyRecursorAlgebra.succEndoAsm

set_option linter.style.longLine false in
/-- info: 'ALT.AssemblyRecursorAlgebra.boundedInitialAlgebraAsmIsInitial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.AssemblyRecursorAlgebra.boundedInitialAlgebraAsmIsInitial

set_option linter.style.longLine false in
/-- info: 'ALT.AssemblyRecursorAlgebra.boundedAlgAsm_str_not_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.AssemblyRecursorAlgebra.boundedAlgAsm_str_not_injective

-- §4.2/§4.3 capacity layer: finite full subcategory, product closure, exponential overflow (FV-14)
/-- info: 'ALT.recursorAsm_fitsIn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.recursorAsm_fitsIn

/-- info: 'ALT.prodAsm_fitsIn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.prodAsm_fitsIn

/-- info: 'ALT.exp_card_overflow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.exp_card_overflow

-- §4.2 coproduct closure of the capacity filtration: `|A ⊕ B| = |A| + |B|` fits in
-- `max sₐ s_b + 1`.
/-- info: 'ALT.coprodAsm_fitsIn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.coprodAsm_fitsIn

-- §4.2 capacity accounting of the classifier inventory: comprehension subobjects cost no capacity
-- (`subAsm_fitsIn`), the classifier is one bit (`boolAsm_fitsIn`), and the power object
-- `[T ⇒ Bool]`
-- fits in `s` work bits IFF `|T| ≤ s` (`powAsm_fitsIn_iff`, exact `2^{|T|}` cardinality) — the
-- higher-order capacity threshold of §4.2.
/-- info: 'ALT.subAsm_fitsIn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.subAsm_fitsIn

/-- info: 'ALT.boolAsm_fitsIn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.boolAsm_fitsIn

/-- info: 'ALT.powAsm_fitsIn_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.powAsm_fitsIn_iff

-- §4.3 realizer-length non-closure (Shannon counting bound) — the realizer-length sibling of
-- FV-14: the SAME `2^s` capacity threshold that overflows the exponential in cardinality forces a
-- genuine morphism to need a realizer of bit-length `> s`. `Classical.choice` is genuine (via
-- `choose` on the short-realizer selector and `realizes_of_finite`).
set_option linter.style.longLine false in
/-- info: 'ALT.realizer_length_overflow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.realizer_length_overflow

/-- info: 'ALT.exp_realizer_overflow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.exp_realizer_overflow

-- §4.3 explicit exponential magnitude: the literal `≈ 2^{|s_work|}`-bit figure ([Decoupling] §4.3)
-- — the SAME fitting object needs a realizer of bit-length `≥ s·2^s`, sharpening the
-- linear `> s` figure of `exp_realizer_overflow` (Shannon counting bound at `b = s·2^s − 1`).
set_option linter.style.longLine false in
/-- info: 'ALT.exp_realizer_overflow_exponential' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.exp_realizer_overflow_exponential

-- §4.3/§7.2 almost-all counting form (FV-16): all but `≤ 2^b` of the functions have every
-- realizer longer than `b`; the complement of the `≤ 2^b` short-realizable functions.
set_option linter.style.longLine false in
/-- info: 'ALT.shortRealizable_card_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.shortRealizable_card_le

set_option linter.style.longLine false in
/-- info: 'ALT.almost_all_realizer_overflow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.almost_all_realizer_overflow

set_option linter.style.longLine false in
/-- info: 'ALT.almost_all_fatAsm_overflow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.almost_all_fatAsm_overflow

-- §6 reflective assembly (FV-5)
set_option linter.style.longLine false in
/-- info: 'ALT.ReflectiveType.representsUnderivableTruth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.ReflectiveType.representsUnderivableTruth

-- §4.4 / Conj 4.4 second learner instance (FV-6)
set_option linter.style.longLine false in
/-- info: 'ALT.ModularCounter.rules_card' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.ModularCounter.rules_card

set_option linter.style.longLine false in
/-- info: 'ALT.ModularCounter.step_eq_nno_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.ModularCounter.step_eq_nno_succ

set_option linter.style.longLine false in
/-- info: 'ALT.ModularCounter.nno_orbit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.ModularCounter.nno_orbit

-- [Discovery] Theorem 2.1 eq. (2): the lookup-table coding lower bound, content-checking
-- `ALT.Ltable = L`. Pigeonhole bound on ANY lossless code (`exists_long_codeword`), the
-- off-by-one-free fixed-width code (`tableEnc_length_ge`), and the `Ltable`-connection.
/-- info: 'ALT.exists_long_codeword' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.exists_long_codeword

/-- info: 'ALT.tableEnc_length_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.tableEnc_length_ge

/-- info: 'ALT.ltable_lower_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.ltable_lower_bound

-- [Discovery] Theorem 2.1 eq. (1): the rule-based two-part code upper bound, content-checking
-- `ALT.Lrule`. The self-delimiting `2·log₂ r` program-framing cost
-- (`selfDelim_length_le`),
-- its losslessness (`selfDelim_injective`), and the assembled two-part code length
-- (`lrule_upper_bound`).
/-- info: 'ALT.selfDelim_length_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.selfDelim_length_le

-- Cor 2.2 content-check: the self-delimiting code realizes the bits-form capacity threshold
-- `ALT.KminBits r 1`, grounding the asserted `2 log r` overhead in a real code
-- length.
set_option linter.style.longLine false in
/-- info: 'ALT.selfDelim_realizes_KminBits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.selfDelim_realizes_KminBits

/-- info: 'ALT.selfDelim_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.selfDelim_injective

/-- info: 'ALT.lrule_upper_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.lrule_upper_bound

-- [Discovery] Theorem 2.1 CAPSTONE: dominance between actual code lengths — the rule-based two-part
-- code is strictly shorter than the lookup-table code, combining eq. (1) + eq. (2) + the bit-unit
-- regime margin. (`ALT.mdl_dominance` is the natural-log arithmetic; this is the codes.)
/-- info: 'ALT.mdl_dominance_codes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.mdl_dominance_codes

-- eq.(1) residuals closed: the two-part code is genuinely lossless (`twoPart_injective`, the
-- Elias-γ
-- prefix decoder) and decode-correctness links the program to the generated output via
-- Code/Computes
-- (`ruleEncode_lossless`), giving the sequence-linked capstone (`mdl_dominance_codes_generated`).
/-- info: 'ALT.twoPart_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.twoPart_injective

/-- info: 'ALT.ruleEncode_lossless' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.ruleEncode_lossless

set_option linter.style.longLine false in
/-- info: 'ALT.mdl_dominance_codes_generated' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.mdl_dominance_codes_generated

-- [Discovery] §3 Theorem 3.1: the central/Bernstein condition (§3.2, proved) and the §3.3 discovery
-- assembly (threshold + Markov arithmetic, proved; GM Thm 22 / Markov / posterior-of-close imported
-- as named hypotheses — so only [propext, Classical.choice, Quot.sound], no extra deep axioms).
/-- info: 'ALT.bernstein_central' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.bernstein_central

set_option linter.style.longLine false in
/-- info: 'ALT.discovery_posterior_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.discovery_posterior_bound

-- §3.3 Markov step DISCHARGED: `markov_tail_real` is a real application of Mathlib's Markov
-- inequality (`mul_meas_ge_le_integral_of_nonneg`), and `discovery_posterior_bound_markov`
-- re-derives
-- the discovery bound using it instead of the abstract `hmarkov` hypothesis.
/-- info: 'ALT.markov_tail_real' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.markov_tail_real

set_option linter.style.longLine false in
/-- info: 'ALT.discovery_posterior_bound_markov' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.discovery_posterior_bound_markov

-- [Discovery] §4 Prop 4.2 (retention upper bound): the discovered rule persists under the
-- conditional-regeneration architecture, reusing [Decoupling]'s Decoupling Lemma.
-- `retention_persists`
-- and `retention_upper_bound` are CHOICE-FREE ([propext, Quot.sound]) — inherited from Decoupling's
-- choice-free core; only the quantitative `Fgt̄ = 0` (Finset/ℝ machinery) pulls in
-- `Classical.choice`.
/-- info: 'ALT.retention_persists' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.retention_persists

/-- info: 'ALT.retention_upper_bound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.retention_upper_bound

set_option linter.style.longLine false in
/-- info: 'ALT.expected_forgetting_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.expected_forgetting_zero

-- §3 Theorem 3.1 UNCONDITIONAL (realizable-deterministic): competitor-likelihood decay gives
-- posterior concentration with NO Grünwald–Mehta / Markov / posterior-of-close hypothesis — only
-- the
-- model (pmf q, prior w R = 2^{−K R}, ∑ w ≤ 1), realizability, and per-step separation.
set_option linter.style.longLine false in
/-- info: 'ALT.competitor_likelihood_decay' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.competitor_likelihood_decay

set_option linter.style.longLine false in
/-- info: 'ALT.deterministic_discovery' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.deterministic_discovery

-- §3 Theorem 3.1 over a COUNTABLE hypothesis class (the paper's `2^{−K(R')}` prior over all
-- programs,
-- §1.1): the same unconditional realizable-deterministic discovery with `∑'` over `ι`,
-- `Summable w`,
-- `∑' w ≤ 1`. Still NO Grünwald–Mehta / Markov / posterior-of-close.
set_option linter.style.longLine false in
/-- info: 'ALT.countable_posterior_lower_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.countable_posterior_lower_bound

/-- info: 'ALT.countable_discovery' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.countable_discovery

-- [Discovery] §3.3 Proposition 3.2 (FV-16): extensional `[R]`-concentration for the near-twin-rich
-- countable class — the honest, non-vacuous discovery statement that DROPS per-step separation
-- entirely. Indicator (`0/1`) likelihoods: the on-trajectory equivalence class `[R]` has positive
-- constant mass `P_{[R]}` (`PR_pos`), the surviving off-`[R]` mass is a Kraft tail vanishing by
-- dominated convergence (`tail_tendsto_zero` — the crux, every competitor falsified at a finite
-- branching time), the normalizer splits `Z_n = P_{[R]} + tail_n` (`Zmass_eq_PR_add_tail`), so the
-- posterior on `[R]` rises MONOTONICALLY to `1` (`extensional_R_concentration` — `postR_monotone` ∧
-- `postR_tendsto_one`). NO separation hypothesis; `ι` a general countable type (no `[Fintype ι]`);
-- only `0 ≤ w`, `Summable w`, antitone consistency, and a true rule `R ∈ [R]` with `0 < w R`.
/-- info: 'ALT.Zmass_eq_PR_add_tail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.Zmass_eq_PR_add_tail

/-- info: 'ALT.tail_tendsto_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.tail_tendsto_zero

/-- info: 'ALT.postR_tendsto_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.postR_tendsto_one

set_option linter.style.longLine false in
/-- info: 'ALT.extensional_R_concentration' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.extensional_R_concentration

-- [Discovery] §3.3 FV-15: genuine ε₀-Hellinger + the ε₀→query-separation bridge
-- (`HellingerBridge.lean`).
-- Target A makes ε₀ a real squared-Hellinger quantity: `sqHellinger_pos_of_ne` is the
-- positive-definiteness `ALT.eps0_pos` had to assume (`0 < sep i`); `eps0H_pos` is
-- ε₀'s
-- strict positivity from pairwise-distinctness alone; `hsep_of_eps0H`/`discovery_of_eps0H`
-- reconnect a
-- per-step eps0H-floor to `ALT.deterministic_discovery`'s `hsep`, so eps0H
-- drives
-- Theorem 3.1. Target B is the bridge: `sqHellinger_le_tv` (`D_H² ≤ TV`), `exists_separating_query`
-- (the sign query's `2·TV` mean gap), `identifiable_of_sqHellinger` (gap `≥ 2ε₀`), and
-- `separates_of_sqHellinger` (2τ-identifiability for `τ < ε₀`, in FV-J's `Separates` shape). The
-- certified scale is the honest `2ε₀`/`τ < ε₀`, NOT the `√ε₀` a mean-level reading assumes (module
-- boundary note; the papers' `√ε₀` wording carries a mean-level qualifier).
/-- info: 'ALT.sqHellinger_pos_of_ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.sqHellinger_pos_of_ne

/-- info: 'ALT.eps0H_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.eps0H_pos

/-- info: 'ALT.eps0H_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.eps0H_le

/-- info: 'ALT.hsep_of_eps0H' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.hsep_of_eps0H

/-- info: 'ALT.discovery_of_eps0H' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.discovery_of_eps0H

/-- info: 'ALT.sqHellinger_le_tv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.sqHellinger_le_tv

set_option linter.style.longLine false in
/-- info: 'ALT.exists_separating_query' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.exists_separating_query

set_option linter.style.longLine false in
/-- info: 'ALT.identifiable_of_sqHellinger' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.identifiable_of_sqHellinger

set_option linter.style.longLine false in
/-- info: 'ALT.separates_of_sqHellinger' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.separates_of_sqHellinger

-- [SQ] §4 Theorem 4.1 step-(c) total-work accounting (FV-B1): an `O(r·log(1/δ))` search window
-- times an `O(r)` per-step cost gives total work `O(r²·log(1/δ))` — thin product bookkeeping.
/-- info: 'ALT.polytime_accounting' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.polytime_accounting

-- [SQ] §5 parity SQ counterexample (FV-A3): every real power of `r` is little-o of the modeled
-- parity statistical dimension `d_SQ` (`poly_isLittleO_dSQ`), so `d_SQ` is not polynomially bounded
-- (`dSQ_not_polyBounded`) — Assumption A fails for parity, hence Theorem 4.1 does not apply to it.
/-- info: 'ALT.poly_isLittleO_dSQ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.poly_isLittleO_dSQ

/-- info: 'ALT.dSQ_not_polyBounded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.dSQ_not_polyBounded

set_option linter.style.longLine false in
/-- info: 'ALT.separated_impostor_pruned' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.separated_impostor_pruned

set_option linter.style.longLine false in
/-- info: 'ALT.separated_impostor_pruned_noisy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.separated_impostor_pruned_noisy

-- [SQ] §4 Theorem 4.1(i) sample complexity (FV-B2): the "Remark on ε₀" absorption collapsing the
-- imported [Discovery] Thm 3.1 discovery bound `O((r+log(1/δ))/ε₀)` to the stated `O(r²·log(1/δ))`
-- under
-- the benign-class `ε₀ = Ω(1/r)`. (Complements FV-B1: B1 = step-(c) total work, this = part-(i)
-- count.)
/-- info: 'ALT.sample_complexity_r2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.sample_complexity_r2

-- [SQ] App. A Claim 2, post-discovery half (FV-F): geometric decay kills the `2^K` prefactor
-- past `T_discover` (`prefactor_le`), so the accumulated post-discovery pruned mass is `≤ δ/2` by
-- competitor-decay + Kraft alone — no maximal inequality (`accumulated_pruned_mass_le`).
/-- info: 'ALT.prefactor_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.prefactor_le

set_option linter.style.longLine false in
/-- info: 'ALT.accumulated_pruned_mass_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.accumulated_pruned_mass_le

-- [SQ] App. A predictive transfer (FV-H): the Bayes-mixture step that turns a bounded pruned
-- mass into a preserved one-step predictive guarantee, made EXACT. `mixture_prune_perturbation` —
-- the one-step L1 perturbation `∑ₓ|Q x − P x| ≤ 2·(W/U)` (TV ≤ W/U, no hidden constant), sharpening
-- the prose "≤ δ/2 in total". `predictive_transfer` — an α-guarantee on the full mixture transfers
-- to `α + 2·(W/U)` on the renormalized survivor mixture. `accumulated_perturbation_le` — the total
-- L1 damage across a step family is `≤ 2·∑ₜ εₜ`, consuming the FV-F/FV-G mass budgets.
set_option linter.style.longLine false in
/-- info: 'ALT.mixture_prune_perturbation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.mixture_prune_perturbation

/-- info: 'ALT.predictive_transfer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.predictive_transfer

set_option linter.style.longLine false in
/-- info: 'ALT.accumulated_perturbation_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.accumulated_perturbation_le

-- [SQ] App. A Claim 2, search-phase half (FV-G): the log-Bayes potential companion to FV-F.
-- The truth-potential telescopes into `[0,K]` (`potential_range`), and the pointwise mass bound
-- `m ≤ −ln(1−m)` summed over the pruned set and charged to that potential (`hcharge`) gives the
-- accumulated search-phase pruned mass `≤ K = ln2·K(R) = O(r)` (`search_phase_pruned_mass_le`) —
-- the discovery-regret order, not `δ/2`. No maximal inequality; the regret/martingale control
-- enters
-- only as the imported `hcharge`, exactly as FV-F imports decay+normalizer as `hdecay`.
/-- info: 'ALT.potential_range' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.potential_range

set_option linter.style.longLine false in
/-- info: 'ALT.search_phase_pruned_mass_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.search_phase_pruned_mass_le

-- `pruned_mass_le_budget`: the slack form — the charge may exceed the telescoped potential drop by
-- an additive budget `B`, degrading the mass bound to `C + B`. The deterministic core the Ville
-- chain (below) rests on, with `B = ln(1/δ)` supplying the between-pruning net rise.
/-- info: 'ALT.pruned_mass_le_budget' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.pruned_mass_le_budget

-- FV-G CHAINED: `search_phase_mass_ville_chain` wires the two cores together — the
-- accumulated pruned mass exceeds `C + ln(1/δ)` only on the Ville excursion event, so
-- `μ{mass > C + ln(1/δ)} ≤ δ` (the paper's `O(r + log(1/δ))` w.h.p.). The `ln(1/δ)` term is DERIVED
-- from `ville_potential_budget` via `pruned_mass_le_budget`, not assumed. Its remaining hypotheses
-- are discharged below: the supermartingale premise by FV-I, and the Kraft `hΦ0` and the
-- no-excursion-conditional charge `hcharge` by the posterior model.
set_option linter.style.longLine false in
/-- info: 'ALT.search_phase_mass_ville_chain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.search_phase_mass_ville_chain

-- FV-G, the Kraft initialization DISCHARGED: the truth's normalized prior weight is `2^{−K(R)}/S`
-- with total mass `S ≤ 1` by Kraft–McMillan (`BinaryKraft`), so `Φ₀ = −ln w₀(R) ≤ ln2·K(R)` — the
-- `hΦ0` the chain used to assume, now derived from the code itself (no assumed normalizer).
set_option linter.style.longLine false in
/-- info: 'ALT.kraft_potential_init_of_code' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.kraft_potential_init_of_code

-- FV-G, the per-path charge DISCHARGED: under the posterior step model (prune a normalized mass,
-- renormalize, then Bayes-update), `−ln(1−m)` per prune is EXACTLY the potential drop plus the net
-- Bayes rise (`charge_identity`), and the rise telescopes to `ln (Z n)`, which is `< ln(1/δ)` on
-- the
-- no-excursion event — so `hcharge` is a theorem, not a hypothesis.
set_option linter.style.longLine false in
/-- info: 'ALT.charge_of_posterior_model' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.charge_of_posterior_model

-- FV-G CAPSTONE: the search-phase mass bound with BOTH modeled inputs closed. With probability
-- `≥ 1−δ` the accumulated pruned mass is `≤ ln2·K(R) + ln(1/δ)` (the paper's `O(r + log(1/δ))`),
-- and the only remaining premises are the posterior's dynamics — no inequality is assumed.
set_option linter.style.longLine false in
/-- info: 'ALT.search_phase_mass_charged' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.search_phase_mass_charged

-- FV-I: the FV-G supermartingale premise DISCHARGED. On the trajectory space
-- `ℕ → X` with Mathlib's coordinate filtration `Filtration.piLE`, `Z_t = ∑ w(R')·L_t(R')` (abstract
-- `[0,1]`-valued, `ℱ_{s+1}`-measurable per-step factors) is pointwise antitone + bounded + adapted,
-- hence a genuine `Supermartingale` for ANY probability truth law (`Z_supermartingale`, via
-- `supermartingale_nat` + `condExp_mono` + `condExp_of_stronglyMeasurable` — no Ionescu–Tulcea).
-- `𝔼[Z_0] ≤ 1` from Kraft (`integral_Z_zero_le_one`), and `search_phase_mass_bound` instantiates
-- the
-- FV-G chain at this `Z` — the `hsuper`/`hnn`/`hZ0` premises are gone, only the FV-G search-side
-- data
-- (`pruned`, `m`, `Φ`, `hcharge`) survives.
/-- info: 'ALT.Z_supermartingale' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.Z_supermartingale

/-- info: 'ALT.integral_Z_zero_le_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.integral_Z_zero_le_one

set_option linter.style.longLine false in
/-- info: 'ALT.search_phase_mass_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.search_phase_mass_bound

-- FV-I hardening: the abstract factor `g` made CONCRETE for the paper's DETERMINISTIC
-- rule class. `detFactor pred i s ω = 𝟙[pred i s (ω|_{<s}) = ω s]` is the `0/1` likelihood of a
-- deterministic rule; `detFactor_stronglyMeasurable` PROVES its `ℱ_{s+1}`-strong measurability from
-- `Filtration.piLE`'s coordinate structure over a discrete alphabet (the `hgmeas` premise, no
-- longer
-- a hypothesis); `L_det_eq_indicator` shows `L_det` is the alive-consistent indicator; and
-- `Z_det_supermartingale` is the FV-I supermartingale with NO abstract-`g` hypotheses left.
set_option linter.style.longLine false in
/-- info: 'ALT.detFactor_stronglyMeasurable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.detFactor_stronglyMeasurable

/-- info: 'ALT.L_det_eq_indicator' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.L_det_eq_indicator

/-- info: 'ALT.Z_det_supermartingale' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.Z_det_supermartingale

-- FV-K: the prequential-MDL-with-SQ-pruning ALGORITHM as a Finset object
-- (`ALT/SQAlgorithm.lean`), with the identification theorems tying the standing FV artifacts to it.
-- `alive_mass_eq_Z_det` — the unpruned Bayes-consistent mass IS FV-I's mixture
-- `Z cands w (detFactor
-- pred)` (the "identify g with the algorithm" item). `truth_survives` — App-A Claim 1 for the
-- object
-- (realizable + τ-close truth stays alive, reusing FV-A4's `truth_survives_pruning` at the 2τ
-- rule).
-- `separated_impostor_pruned_alg` — the FV-A4 converse (a 3τ-separated candidate is pruned).
-- `algorithm_damage_le` — FV-H's `accumulated_perturbation_le` at the algorithm's OWN step families
-- (survivors `alive (t+1)` vs pruned-away `prunedAt t`), so `ε_t` is its literal pruned fraction.
-- `posterior_concentration_transfer` — the algorithm's Dirac pmf instantiates [Discovery]'s
-- `deterministic_discovery`, giving unpruned posterior concentration (`≥ 1 − δ/2`).
/-- info: 'ALT.alive_mass_eq_Z_det' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.alive_mass_eq_Z_det

/-- info: 'ALT.truth_survives' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.truth_survives

set_option linter.style.longLine false in
/-- info: 'ALT.separated_impostor_pruned_alg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.separated_impostor_pruned_alg

/-- info: 'ALT.algorithm_damage_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.algorithm_damage_le

set_option linter.style.longLine false in
/-- info: 'ALT.posterior_concentration_transfer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.posterior_concentration_transfer

-- FV-K hardening: Theorem 4.1(i) assembled for the PRUNED algorithm via posterior
-- MONOTONICITY (not concentration∘damage). `posterior_mono_of_subset` — restricting a
-- nonneg-weighted
-- posterior's normalizer to a subset containing the (positive-weight) truth dominates the full
-- quotient. `Lik_qDirac_eq_L_det` — the Dirac-pmf `Lik` IS FV-I's `L (detFactor pred)`
-- (definitional).
-- `algorithm_discovery` — the pruned posterior on `iR` is `≥ 1 − δ/2`: `truth_survives` ⇒ `iR ∈
-- alive n ⊆ univ`, then monotonicity over `posterior_concentration_transfer`'s unpruned bound.
set_option linter.style.longLine false in
/-- info: 'ALT.posterior_mono_of_subset' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.posterior_mono_of_subset

/-- info: 'ALT.Lik_qDirac_eq_L_det' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.Lik_qDirac_eq_L_det

/-- info: 'ALT.algorithm_discovery' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.algorithm_discovery

-- The commitment step's selector (`ALT/CommitmentSeam.lean`) — the [Discovery] §5 Theorem 5.1(iv)
-- bridge from the §3 posterior to the §4 read-only code, hardened on the [SQ] §4 algorithm object.
-- `Commits.unique`: at most one candidate reaches the threshold `1 − δ/2`, by normalization — the
-- hypothesis `δ < 1` is load-bearing (at `δ = 1` two candidates can tie at half the mass and the
-- committed rule is genuinely undefined). `commitment_seam`: past the discovery horizon the
-- candidates satisfying the commitment predicate are EXACTLY the true rule, at every such time —
-- existence, uniqueness and time-stability of the selection in one equivalence.
-- What stays an architectural assumption, exactly as the paper states it: the WRITE of the selected
-- rule into the persistent code, and the `δ/2` corruption budget for keeping it there. Neither is
-- established; no code region appears in the module.
/-- info: 'ALT.Commits.unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.Commits.unique

/-- info: 'ALT.commitment_seam' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.commitment_seam

-- FV-AC hardening: the collector CONSTRUCTED (`ALT/Collector.lean`), so Prop
-- 2.2's "modeled premise" (an arbitrary `coll` assumed to halt) is DISCHARGED at the eval level.
-- `collector cR := prec zero (stepWrap cR)` is a fixed iterator template with the rule plugged in
-- (a rule-independent first-order collector cannot re-run `cR`); `orbitAcc_fst` certifies the
-- collected stream is the rule's orbit `rs^[t] 0`; `eval_collector`/`eval_assembly` prove the
-- assembly
-- `collector cR ∘ (pair zero (bconst n))` computes the orbit prefix `orbitAcc rs n`;
-- `elen_collector`
-- (`= elen cR + 60`, `Classical.choice`-free) shows the collector adds only a fixed constant, so
-- `prop_2_2_eval` gives `KE (orbitAcc rs n) ≤ elen cR + κ·Nat.size n + (84 + elen dbl)` =
-- `r + O(log n)`
-- with the collector DISCHARGED. Target B (explicit `evaln` budget) is walled — `evaln`'s `k` caps
-- intermediate values, so `prop_2_2_t_exists` ships the honest ∃-budget form (via
-- `evaln_complete`).
/-- info: 'ALT.orbitAcc_fst' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.orbitAcc_fst

/-- info: 'ALT.eval_collector' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.eval_collector

/-- info: 'ALT.eval_assembly' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.eval_assembly

/-- info: 'ALT.elen_collector' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.elen_collector

/-- info: 'ALT.elen_assembly' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.elen_assembly

/-- info: 'ALT.prop_2_2_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.prop_2_2_eval

/-- info: 'ALT.prop_2_2_t_exists' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.prop_2_2_t_exists

-- The search cost (`ALT/SearchCost.lean`) — the cost model extended from the rfind'-free fragment
-- to
-- ALL of `Nat.Partrec.Code`. `eval_eq_valP`: value-agreement UNRESTRICTED — the extended
-- evaluator's
-- value component is `eval` on every code, `rfind'` included, which is what `eval_eq_val` could
-- state
-- only on the fragment. `evalP_eq_evalT`: coherence — on the fragment the extended evaluator
-- returns
-- exactly the total one's `(val, tc)`, so every result proved against `tc` transfers and there is
-- ONE
-- cost model, not two. `evalP_dom`: the extended cost is defined exactly where `eval` halts — the
-- search neither restricts the domain (as a fuel bound would) nor extends it (as a placeholder
-- would).
-- `tcP_rfind'_le`: the `rfind'` analogue of `tc_prec_le` — a uniform per-probe bound `B` gives a
-- search with witness `n` a cost `≤ (n+1)·(B+1)`, linear in the probes actually made. The witness
-- is a
-- hypothesis, not a constant: an unbounded search admits no bound uniform in the input.
/-- info: 'ALT.eval_eq_valP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.eval_eq_valP

/-- info: 'ALT.evalP_eq_evalT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.evalP_eq_evalT

/-- info: 'ALT.evalP_dom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.evalP_dom

/-- info: 'ALT.tcP_rfind'_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.tcP_rfind'_le

-- The search WORKSPACE (`ALT/SearchSpace.lean`) — the space sibling of the search cost, making BOTH
-- native cost measures total over `Nat.Partrec.Code`. `eval_eq_valW`: value-agreement unrestricted
-- —
-- the workspace evaluator's value component is `eval` on every code, `rfind'` included, so the
-- workspace is charged along the genuine computation. `evalW_coherent`: on the rfind'-free fragment
-- it returns exactly `(val, spaceCost)`, so `spaceCost_prec_le` is a statement about this one
-- model.
-- `spaceCostP_rfind'`/`spaceCostP_rfind'_le`: the search's space laws — the exact probe-MAXIMUM
-- identity, and the bound `max S (Nat.size (n+m))` in which THE PROBE COUNT IS ABSENT. Where the
-- step account pays `(n+1)·(B+1)` for `n+1` probes, rerunning a probe reuses the same workspace;
-- only holding the answer adds bits.
/-- info: 'ALT.eval_eq_valW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.eval_eq_valW

/-- info: 'ALT.evalW_coherent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.evalW_coherent

/-- info: 'ALT.spaceCostP_rfind'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.spaceCostP_rfind'

/-- info: 'ALT.spaceCostP_rfind'_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.spaceCostP_rfind'_le

-- The bounded checker's scratch account (`ALT/CheckerWorkspace.lean`) — the [Decoupling] §6.3
-- workspace bound assembled from the per-constituent capacity bounds and the native space cost.
-- `checker_scratch_closure`: the enumeration over the `M_chk + 1` candidate proof codes runs in
-- `max (spaceCost cf a) S` workspace, with the budget `M_chk` ABSENT from the bound, stated in
-- §6.3's own bit-length vocabulary (`size_eq_clog` is the whole dictionary). The per-candidate
-- `Δ₀`/poly-time check of a held candidate (Buss 1986) is not constructed: it is the paper-level
-- input, entering as the hypothesis `hstep`. `checker_space_time_contrast`: the same loop priced
-- twice — the budget hypothesis `M_chk ≤ g^2` is consumed by the TIME half alone (exhaustive
-- search, polynomial in the value `g`), never by the space half. `checkerLoop_val_decides`: the
-- native bounded recursion computes the same verdict as the finite fold `Decide`.
set_option linter.style.longLine false in
/-- info: 'ALT.checker_scratch_closure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.checker_scratch_closure

set_option linter.style.longLine false in
/-- info: 'ALT.checker_space_time_contrast' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.checker_space_time_contrast

set_option linter.style.longLine false in
/-- info: 'ALT.checkerLoop_val_decides' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.checkerLoop_val_decides

-- Capacity-bounded evaluation (`ALT/CapacityBoundedEval.lean`) — the evaluator-side half of the
-- [Decoupling] §4.5 crux of Conjecture 4.4. `size_val_le_spaceCost`: the keystone, an output is
-- never wider than the workspace charged for producing it (the `RfindFree` hypothesis is essential,
-- `spaceCost` pricing `rfind'` as the placeholder `0`); `size_valW_le`: the same over the workspace
-- evaluator, unconditional on all of `Nat.Partrec.Code`. `spaceCost_comp_within`: grade closure —
-- a realizer within an `S`-bit workspace, fed a value produced within an `S`-bit workspace, runs
-- within the `S`-bit workspace. The transport clause of the crux (a capacity-respecting simulation
-- carries realizers across without overflowing the budget) is a statement about simulation
-- morphisms, which this development does not define; it is NOT established here.
/-- info: 'ALT.size_val_le_spaceCost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.size_val_le_spaceCost

/-- info: 'ALT.size_valW_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.size_valW_le

/-- info: 'ALT.spaceCost_comp_within' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.spaceCost_comp_within

-- Transporting a realizer across a change of encoding (`ALT/GradeTransport.lean`) — the action on
-- morphisms that [Decoupling] §4.5's Conjecture 4.4 needs, priced in both currencies. The transport
-- is the coded conjugation `comp c_emb (comp r c_proj)`, at FIXED algebra: this is re-encoding
-- within one assembly category, NOT the per-subsystem functor with its state-level layout, which
-- stays paper-level. `realizes_transport`: the conjugate realizes the same function against the
-- re-encoded conventions, given the retraction identity on the input side (the output side needs
-- only a coded map). `spaceCost_transport_le`: workspace grades MAX — `≤ max g b`, with no
-- constant,
-- a conjugation forming no pairs. `elen_transport`: description lengths ADD, exactly, `+ 6` for the
-- two serialized `comp` nodes. The dilation of a hosting square enters NEITHER bound: it prices
-- time at the level of the dynamics, not the workspace of one application.
/-- info: 'ALT.realizes_transport' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.realizes_transport

/-- info: 'ALT.spaceCost_transport_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.spaceCost_transport_le

/-- info: 'ALT.elen_transport' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.elen_transport

-- A small-step interpreter for `Nat.Partrec.Code` on configuration numerals
-- (`ALT/BoundedInterp.lean`) — the structurally presented evaluator [Decoupling] §4.5/§6.3 want,
-- at its MATHEMATICAL layer only: `stepUFn` is a function on numerals, not a code, and nothing here
-- prices anything. The stack spine is packed by CONCATENATION with a unary length header, not by
-- nested pairing: `size_stack_le` is the payoff — a well-formed stack of depth `d` with frames of
-- at most `F` bits costs `d * (2F + 2)` bits, linear in the depth where a nested pairing squares
-- per cell. `isStack_run`: every configuration reachable from `initConfig` has a well-formed stack,
-- so that bound applies along a whole run. `stkDepth_prec_descend`: bounded recursion is evaluated
-- as an UPWARD loop under one cell, so it costs one stack cell whatever its counter — the machine
-- computes the way `TimeCost.spaceCost` already prices it, with the counter in a `max` not a sum.
-- `runMeasure_not_antitone`: the obvious run measure (pending code depth plus stack depth) is NOT
-- non-increasing — returning into a frame makes the code that frame stored pending — so the depth
-- bound needs a per-frame invariant instead. `stkDepth_run_le`: that invariant (`StackOK`, charging
-- each cell for the code it stores plus the cells beneath it) carried out — along any run the stack
-- holds at most `codeDepth (ofNat p)` cells, which with `size_stack_le` bounds the workspace.
-- `eval_rfind'_unfold`: unbounded search as a one-probe recurrence — Mathlib
-- states the `rfind'` clause through `Nat.rfind` over an offset, and this is the recurrence the
-- machine implements; of independent use. `machine_sound`: if the machine halts after any number of
-- steps, its answer is a genuine value of the code it was given — exact, no fragment restriction
-- (unbounded search is an ordinary frame) and no fuel. Proved by giving each configuration a
-- denotation and showing a step never changes it. `machine_complete`: the converse, via the fuelled
-- evaluator used as an induction principle only — every value the code produces is reached by the
-- machine. Together the two pin the semantics to `Code.eval` on all of `Nat.Partrec.Code`. What is
-- NOT established is a step-count BOUND; the run is given existentially.
-- `PrecFree.tc_const`: a code built without bounded recursion charges a step count independent of
-- its input — the exact premise a fixed-skeleton constant-cost step would need. `Nat.Partrec.Code`
-- has no arithmetic primitive beyond `succ`, so realizing this step function needs `prec` for all
-- of its packing and every branch test, and `tc_prec_le` then charges by the VALUE of a counter
-- rather than its bit-length. The workspace side is unaffected (`spaceCost_prec_le` is a `max`).
/-- info: 'ALT.eval_rfind'_unfold' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.eval_rfind'_unfold

/-- info: 'ALT.machine_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.machine_sound

/-- info: 'ALT.size_stack_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.size_stack_le

/-- info: 'ALT.isStack_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.isStack_run

/-- info: 'ALT.stkDepth_prec_descend' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.stkDepth_prec_descend

set_option linter.style.longLine false in
/-- info: 'ALT.runMeasure_not_antitone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.runMeasure_not_antitone

/-- info: 'ALT.stkDepth_run_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.stkDepth_run_le

/-- info: 'ALT.machine_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.machine_complete

/-- info: 'ALT.PrecFree.tc_const' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.PrecFree.tc_const

-- The step function REALIZED as a `Nat.Partrec.Code` (`ALT/CodeArith.lean`, `ALT/CodePacking.lean`)
-- — the interpreter of `ALT/BoundedInterp.lean` built from the eight constructors.
-- `Nat.Partrec.Code`
-- has no arithmetic primitive beyond `succ`, so addition, multiplication, subtraction, division,
-- remainder, powers, bit-length and every comparison are built from bounded recursion first; the
-- packing and accessors follow; then the two group codes and the assembly. `val_stepU`: the code
-- computes the mathematical layer's step function on EVERY numeral, halted and stuck configurations
-- included. `rfindFree_stepU`: nothing in it searches, so the workspace account is total on it.
-- Priced for SPACE only — the native step count charges by the VALUE of a bounded recursion's
-- counter, which is why no time law is claimed (`PrecFree.tc_const` above records the premise that
-- fails). `not_spaceIO_cDbl`: the WORKSPACE shape "input-or-output width plus a constant" fails
-- already at doubling — a `pair` node is charged the width of the pair it forms, and pairing a
-- value with itself doubles it, so no constant closes the gap. The honest workspace bound for the
-- realized step is a MULTIPLE of the wider of its input and output, not that width plus a constant.
/-- info: 'ALT.val_stepU' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.val_stepU

/-- info: 'ALT.rfindFree_stepU' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.rfindFree_stepU

/-- info: 'ALT.not_spaceIO_cDbl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.not_spaceIO_cDbl

/-- info: 'ALT.spaceCost_stepU_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.spaceCost_stepU_le

/-- info: 'ALT.val_runU' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.val_runU

/-- info: 'ALT.spaceCost_runU_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.spaceCost_runU_le

/-- info: 'ALT.universalAt_holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.universalAt_holds

-- The graded exponential and the price of applying it (`ALT/GradedApplication.lean`).
-- `gradedExp` grades the exponential by realizer description length — the currency bounded
-- universality already charges in, and the same measure the realizer-length counting bound uses
-- (`grade_encode`). `appValue_mem_ap` / `exists_appRun_of_mem_ap`: application, repackaged as a run
-- of the reference dynamics rather than the algebra's skeleton-less decode, computes exactly the
-- algebra's application — the machine's own soundness and completeness at the application
-- interface. `appConfig_size_le`: the whole of what a grade buys on the workspace side, the INITIAL
-- configuration's width; later configurations hold values the computation produced, so the account
-- stays relative to a named width hypothesis, whose satisfiability on a finishing run is
-- `exists_width_bound`. `gradedApp_workspace_affine`: the account at the discharged affine price,
-- with no hypothesis on the cost function left. `gradedExp_app_realizes_within`: semantics and
-- price together — the applied value is genuinely realized, within the grade-derived budget.
-- `gradedExp_fitsIn`: over a modest codomain the graded exponential is a capacity object again,
-- fitting in exactly its grade, where the ungraded one overflows every capacity.
/-- info: 'ALT.grade_encode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.grade_encode

/-- info: 'ALT.appValue_mem_ap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.appValue_mem_ap

set_option linter.style.longLine false in
/-- info: 'ALT.exists_appRun_of_mem_ap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.exists_appRun_of_mem_ap

/-- info: 'ALT.appConfig_size_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.appConfig_size_le

/-- info: 'ALT.exists_width_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.exists_width_bound

set_option linter.style.longLine false in
/-- info: 'ALT.gradedApp_workspace_affine' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.gradedApp_workspace_affine

set_option linter.style.longLine false in
/-- info: 'ALT.gradedExp_app_realizes_within' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.gradedExp_app_realizes_within

/-- info: 'ALT.gradedExp_fitsIn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.gradedExp_fitsIn

-- Transport at grade (`ALT/GradedConjugation.lean`): the conjugation of a graded realizer one level
-- up from the single-encoding `GradeTransport`, on the many-realizers assemblies the graded
-- exponential is built over. `gradedTransport` carries an element of `[A ⇒ B]_g` to an element of
-- the
-- re-encoded exponential at grade `4·max g b + 9` — its underlying function unchanged, its realizer
-- the
-- transported index (`transportIdx`), whose grade the one-hop max-affine law bounds and whose
-- tracking
-- `tracks_transportIdx` supplies. The capstone guard certifies the whole chain — the index-currency
-- law, the Asm-level transport, and the packaging — is axiom-clean.
/-- info: 'ALT.gradedTransport' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.gradedTransport

-- The pullback direction of the same transport (`ALT/GradedConjugation.lean`): `gradedPullback`
-- carries a graded morphism to one between the pullbacks of its assemblies along a reading pair, at
-- grade `4·max g b + 9` — the mirror of `gradedTransport`, the retraction on the output side.
/-- info: 'ALT.gradedPullback' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.gradedPullback

-- The hosting-induced assembly map (`ALT/GradedSimulation.lean`): `GradedSimulates.inducedMap` is
-- the
-- map a capacity-respecting decoupled simulation induces on graded exponentials, per frame — the
-- guest-coded hypotheses discharge the pullback's retraction, and the grade grows by one hop to
-- `4·max g b + 9` (the price is `(g, b)`, not `(g, b, τ)`).
set_option linter.style.longLine false in
/-- info: 'ALT.GradedSimulates.inducedMap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.GradedSimulates.inducedMap

/-- info: 'ALT.prop_2_2_t_poly' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.prop_2_2_t_poly

/-! ## Guard-gap closure — modules predating the `#guard_msgs` discipline

The capstones below (each module docstring's "What this DOES establish" list) were built before the
audit-umbrella discipline and carried no guard; added here for uniform coverage at the same bar.
Grouped by paper. `ChainDependencyAudit`'s pure-propositional chain depends on NO axioms — a
strict subset the guard pins verbatim. -/

-- [Decoupling] §4 CCC stand-in for Rep(S) (`ALT/CartesianClosed.lean`, namespace `RepSCCC`): Prop
-- 4.3
-- Cartesian-closedness (`repS_cartesianClosed`), the §4.3 evaluation/currying universal property
-- (`expCurrying`), §4.5 functions-as-data (`functionsAsData`), and the §4.4 finite-exponential
-- miniature (`exp_finite`).
/-- info: 'ALT.repS_cartesianClosed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.repS_cartesianClosed

/-- info: 'ALT.expCurrying' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.expCurrying

/-- info: 'ALT.functionsAsDataType' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.functionsAsDataType

/-- info: 'ALT.exp_finite_type' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.exp_finite_type

-- [Decoupling] §5.3/§6 Gödel threshold (`ALT/GodelThreshold.lean`), tied to `ParamNNO`: the
-- Theorem 6.2 form — depth `> g(T_S)` under incompleteness ⟹ represents-an-underivable-truth. Pure
-- threshold logic, so it is `Classical.choice`-free (`[propext, Quot.sound]`, a strict subset).
/-- info: 'ALT.reflective_of_depth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.reflective_of_depth

-- [Discovery] §1.2 regime consistency (`ALT/RegimeConsistency.lean`): the strict ordering `r<K<L`
-- under C1–C3 (`regime_strict_ordering`) and its non-vacuity witness (`regime_satisfiable`).
/-- info: 'ALT.regime_strict_ordering' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.regime_strict_ordering

/-- info: 'ALT.regime_satisfiable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.regime_satisfiable

-- [Discovery] Cor 2.2 capacity threshold (`ALT/CapacityThreshold.lean`): in the regime, C1 entails
-- representability of the rule-based encoding (`representable_of_C1`).
/-- info: 'ALT.representable_of_C1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.representable_of_C1

-- [Discovery] Thm 2.1 static MDL dominance (`ALT/MDLDominance.lean`): the exact §2.2 Step-3 gap
-- identity (`dominance_gap_eq`) and strict dominance in the regime (`mdl_dominance`).
/-- info: 'ALT.dominance_gap_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.dominance_gap_eq

/-- info: 'ALT.mdl_dominance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.mdl_dominance

-- [Discovery] §4.4 retention overhead (`ALT/RetentionOverhead.lean`): the eq.(4) decomposition
-- (`overhead_eq`) and the `O(r·log(r/δ))` explicit-constant bound (`overhead_bigO`).
/-- info: 'ALT.overhead_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.overhead_eq

/-- info: 'ALT.overhead_bigO' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.overhead_bigO

-- [Discovery] §1.1 universal-prior sub-normalization (`CodeLayer/PriorNormalization.lean`): the
-- countable
-- extension read at the hypothesis class — the `∝ 2^{−K}` prior is a semimeasure
-- (`prior_tsum_le_one`).

-- [Discovery] §3.3 explicit ε₀ lower bound (`ALT/EpsilonZeroBound.lean`): positivity (`eps0_pos`),
-- the `γ`-separated demotion `ε₀ ≥ γ` (`eps0_ge_of_separated`), and the conditional polynomial
-- discovery-time bound (`Tdiscover_le_of_separated`).
/-- info: 'ALT.eps0_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.eps0_pos

/-- info: 'ALT.eps0_ge_of_separated' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.eps0_ge_of_separated

set_option linter.style.longLine false in
/-- info: 'ALT.Tdiscover_le_of_separated' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.Tdiscover_le_of_separated

-- [Discovery] K-reconnection (`ALT/KReconnection.lean`): the five load-bearing MDL-corpus theorems
-- re-stated at the genuine `r = K(R)` (bit-length Kolmogorov complexity of the rule `R`).
/-- info: 'ALT.representable_of_C1_K' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.representable_of_C1_K

/-- info: 'ALT.mdl_dominance_K' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.mdl_dominance_K

set_option linter.style.longLine false in
/-- info: 'ALT.regime_strict_ordering_K' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.regime_strict_ordering_K

/-- info: 'ALT.overhead_bigO_K' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.overhead_bigO_K

/-- info: 'ALT.polytime_accounting_K' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.polytime_accounting_K

-- Reflection-chain dependency audit (`ALT/ChainDependencyAudit.lean`): all five named edges
-- compose into the three terminal claims with no missing link (`chain_complete`) and bare
-- reflection sits off the tractability/retention path (`reflection_off_sq_and_retention`). Pure
-- propositional logic — NO axioms.
/-- info: 'ALT.chain_complete' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.chain_complete

/-- info: 'ALT.reflection_off_sq_and_retention' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.reflection_off_sq_and_retention

-- …and the steady-state per-step resource bound ([SQ] Cor 4.4) is likewise off the SQ path
-- (`steady_state_on_retention_off_sq`): reached without the tractability edge and without
-- SQ-learnability.
/-- info: 'ALT.steady_state_on_retention_off_sq' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.steady_state_on_retention_off_sq

-- [Decoupling] §6.3/§6.4 + [Persistence] §5/§7 — the expressiveness excess order. The graded
-- representational class is a faithful order (`RepClass_subset_iff`: inclusion iff budget ≤); the
-- strict internalization clause (`outgrows`) delivers the [Decoupling] §6.4 reflective object as a
-- predicate on the budget, non-degenerate below the Gödel-sentence size (`outgrows_excludes`); and
-- `witness_outgrows` places the [Persistence] §5/§7 Witness-World guest and the internalization
-- threshold on one carrier. Assembly over already-axiom-clean constituents; no numbered result.
/-- info: 'ALT.RepClass_subset_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.RepClass_subset_iff

/-- info: 'ALT.outgrows' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.outgrows

/-- info: 'ALT.outgrows_excludes' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.outgrows_excludes

/-- info: 'ALT.witness_outgrows' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.witness_outgrows

-- [Inevitability] §2 Definitions 2.1–2.3 — the reflective threshold and the substrate class.
-- The paper's own headline theorem (5.1(b)) gets its first Lean object here:
-- `SubstrateL.reachesThreshold`.
set_option linter.style.longLine false in
/-- info: 'ALT.SubstrateL.reachesThreshold' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.SubstrateL.reachesThreshold

set_option linter.style.longLine false in
/-- info: 'ALT.ReflectiveCapacity.fitsIn_headroom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.ReflectiveCapacity.fitsIn_headroom

/-- info: 'ALT.incompleteness_not_unconditionally_satisfiable' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.incompleteness_not_unconditionally_satisfiable

/-- info: 'ALT.s3_not_implied_by_s2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.s3_not_implied_by_s2

/-- info: 'ALT.substrate_satisfiable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.substrate_satisfiable

-- [Inevitability] §2 Definition 2.1 stated WITHIN a work budget (`ReachesThresholdWithin`):
-- the membership condition that can fail, and the boundary it fails at.
-- Exact on the tight family `g(T_S) = 2^n - 1`: membership iff the budget meets `capacity n = 2n`.
set_option linter.style.longLine false in
/-- info: 'ALT.tightFamily_reflectiveWithin_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.tightFamily_reflectiveWithin_iff

-- `𝒮_L` reaches it at the host's leftover capacity, consuming (S3).
set_option linter.style.longLine false in
/-- info: 'ALT.SubstrateL.reachesThresholdWithin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.SubstrateL.reachesThresholdWithin

-- And on that family (S3)-shaped capacity is NECESSARY for membership itself, not only for
-- what a member then delivers.
set_option linter.style.longLine false in
/-- info: 'ALT.reachesThresholdWithin_not_reachable_below_paperCapacity_on_family' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.reachesThresholdWithin_not_reachable_below_paperCapacity_on_family

-- The coupled chain discharges the new clause from its own capacity-bounded witness.
set_option linter.style.longLine false in
/-- info: 'ALT.coupledAtRequiredDepth_reachesThresholdWithin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.coupledAtRequiredDepth_reachesThresholdWithin

-- [Inevitability] §5 Remark 5.5, the learning branch: the budgeted threshold indexed by time, and
-- the persistence (S1) buys it. `Substrate.reachesThresholdWithinAt_persists` is the first
-- consumer of `Substrate`'s (S1) field anywhere in this development, and
-- `reachesThresholdWithinAt_lost_on_overwrite` is the guard that makes that hypothesis
-- load-bearing: an update that overwrites the code region holds the crossing at `t = 0` and has
-- lost it at `t = 1`.
set_option linter.style.longLine false in
/-- info: 'ALT.Substrate.reachesThresholdWithinAt_persists' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.Substrate.reachesThresholdWithinAt_persists

set_option linter.style.longLine false in
/-- info: 'ALT.reachesThresholdWithinAt_lost_on_overwrite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.reachesThresholdWithinAt_lost_on_overwrite

-- [Inevitability] §2 Definition 2.3, the class-level `𝒮_E` constructor: for any decoupled
-- `(U, R)`, any packing onto a numeral carrier, and any frame surjective off the packed update's
-- own iterate, `SubstrateE` follows from the numeral conditions and one crossing hypothesis at the
-- packed capacity — and the reversible corollary, Definition 2.3's own ruled sentence.
set_option linter.style.longLine false in
/-- info: 'ALT.substrateE_of_emergence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.substrateE_of_emergence

/-- info: 'ALT.substrateE_of_perm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.substrateE_of_perm

-- The block-pair correlation profile: the cyclic-correlation decomposition at symbolic block
-- count and its zone/spike corollaries, the Thue–Morse-sourced block-sign supply discharging both
-- transition-sum balances, and the certified length-24 word pair's assembled correlation profile.
/-- info: 'ALT.cyclicCorr_blockSeq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.cyclicCorr_blockSeq

set_option linter.style.longLine false in
/-- info: 'ALT.cyclicCorr_blockSeq_zone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.cyclicCorr_blockSeq_zone

set_option linter.style.longLine false in
/-- info: 'ALT.cyclicCorr_blockSeq_spike' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.cyclicCorr_blockSeq_spike

/-- info: 'ALT.tmSign_balance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.tmSign_balance

/-- info: 'ALT.blockSign_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.blockSign_sq

/-- info: 'ALT.blockSign_mul_noWrap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.blockSign_mul_noWrap

/-- info: 'ALT.blockSign_mul_wrap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.blockSign_mul_wrap

set_option linter.style.longLine false in
/-- info: 'ALT.blockSign_transition_even' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.blockSign_transition_even

set_option linter.style.longLine false in
/-- info: 'ALT.blockSign_transition_odd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.blockSign_transition_odd

set_option linter.style.longLine false in
/-- info: 'ALT.blockSeq_wordU_wordV_correlation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.blockSeq_wordU_wordV_correlation

-- The profile-class family (`ALT/BlockPairProfile.lean`): the certified pair's exact zone
-- generalizes to every extension count `r ≥ 1`, the same seeds extended with alternating block
-- sign to every length `8 * r`.
set_option linter.style.longLine false in
/-- info: 'ALT.aperiodicCorr_antiExt_zone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.aperiodicCorr_antiExt_zone

/-- info: 'ALT.tmPrefix_two_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.tmPrefix_two_mul

set_option linter.style.longLine false in
/-- info: 'ALT.tmPrefix_two_mul_add_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.tmPrefix_two_mul_add_one

/-- info: 'ALT.blockSign_eq_tmPrefix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.blockSign_eq_tmPrefix

-- The deviation envelope: Thue–Morse partial-sum bounds, the ℕ-indexed prefix/window machinery
-- with its exact block decomposition and period reduction, the zone/spike prefix and window
-- bounds at symbolic block count, and their instantiation at the certified word pair.
/-- info: 'ALT.tmSign_partial_odd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.tmSign_partial_odd

set_option linter.style.longLine false in
/-- info: 'ALT.tmSign_partial_abs_le_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.tmSign_partial_abs_le_one

set_option linter.style.longLine false in
/-- info: 'ALT.tau_partial_even_abs_le_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.tau_partial_even_abs_le_one

set_option linter.style.longLine false in
/-- info: 'ALT.tau_partial_odd_abs_le_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.tau_partial_odd_abs_le_one

set_option linter.style.longLine false in
/-- info: 'ALT.cyclicCorrPrefix_add_period' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.cyclicCorrPrefix_add_period

set_option linter.style.longLine false in
/-- info: 'ALT.cyclicCorrWindow_eq_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.cyclicCorrWindow_eq_sub

set_option linter.style.longLine false in
/-- info: 'ALT.cyclicCorrPrefix_mod_period' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.cyclicCorrPrefix_mod_period

set_option linter.style.longLine false in
/-- info: 'ALT.cyclicCorrPrefix_blockSeq_zone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.cyclicCorrPrefix_blockSeq_zone

set_option linter.style.longLine false in
/-- info: 'ALT.cyclicCorrPrefix_blockSeq_spike' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.cyclicCorrPrefix_blockSeq_spike

set_option linter.style.longLine false in
/-- info: 'ALT.cyclicCorrWindow_blockSeq_zone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.cyclicCorrWindow_blockSeq_zone

set_option linter.style.longLine false in
/-- info: 'ALT.cyclicCorrWindow_blockSeq_spike' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.cyclicCorrWindow_blockSeq_spike

set_option linter.style.longLine false in
/-- info: 'ALT.cyclicCorrPrefix_blockSeq_wordU_wordV_zone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.cyclicCorrPrefix_blockSeq_wordU_wordV_zone

set_option linter.style.longLine false in
/-- info: 'ALT.cyclicCorrPrefix_blockSeq_wordU_wordV_spike' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.cyclicCorrPrefix_blockSeq_wordU_wordV_spike

set_option linter.style.longLine false in
/-- info: 'ALT.cyclicCorrWindow_blockSeq_wordU_wordV_zone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.cyclicCorrWindow_blockSeq_wordU_wordV_zone

set_option linter.style.longLine false in
/-- info: 'ALT.cyclicCorrWindow_blockSeq_wordU_wordV_spike' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.cyclicCorrWindow_blockSeq_wordU_wordV_spike

set_option linter.style.longLine false in
/-- info: 'ALT.BlockPairHost.rot8_iterate_eight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.BlockPairHost.rot8_iterate_eight

set_option linter.style.longLine false in
/-- info: 'ALT.BlockPairHost.rot8_iterate_dvd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.BlockPairHost.rot8_iterate_dvd

set_option linter.style.longLine false in
/-- info: 'ALT.BlockPairHost.windowXor_noisyStep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.BlockPairHost.windowXor_noisyStep

set_option linter.style.longLine false in
/-- info: 'ALT.BlockPairHost.update_iterate_designWindow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.BlockPairHost.update_iterate_designWindow

set_option linter.style.longLine false in
/-- info: 'ALT.BlockPairHost.update_iterate_last' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.BlockPairHost.update_iterate_last

set_option linter.style.longLine false in
/-- info: 'ALT.BlockPairHost.update_iterate_period' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.BlockPairHost.update_iterate_period

set_option linter.style.longLine false in
/-- info: 'ALT.BlockPairHost.windowXor_update_iterate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.BlockPairHost.windowXor_update_iterate

set_option linter.style.longLine false in
/-- info: 'ALT.BlockPairHost.update_iterate_period_all' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.BlockPairHost.update_iterate_period_all

-- The profile-class 𝒮_L criterion (`ALT/TapeHost.lean`, `ALT/TapeHostObservability.lean`,
-- `ALT/TapeHostWitness.lean`): the block-pair pipeline's host and observability layers with the
-- observation sequence made a parameter, and the profile-class membership theorem over an
-- arbitrary window-deviation profile. The certified sequence's own instance of that profile
-- (`ALT/BlockPairCriterion.lean`) is guarded alongside it, below.
set_option linter.style.longLine false in
/-- info: 'ALT.TapeHost.mixingHoeffding_schedule' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.TapeHost.mixingHoeffding_schedule

/-- info: 'ALT.TapeHost.tape_density' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.TapeHost.tape_density

/-- info: 'ALT.TapeHost.substrateL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.TapeHost.substrateL

set_option linter.style.longLine false in
/-- info: 'ALT.BlockPairHost.designObs_profile' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.BlockPairHost.designObs_profile

-- The affordable regime's worked example (`ALT/TapeHostSchedule.lean`): the schedule's own
-- oracle is deterministic (`scheduleOracle_deterministic`) and its `2τ`-pruning rule
-- (`schedSurvivors`) isolates the true literal from an explicit horizon on, uniform in the
-- period. The certified block-pair design's own instance (`ALT/BlockPairCriterion.lean`) is
-- guarded alongside it, below.
set_option linter.style.longLine false in
/-- info: 'ALT.schedSurvivors_eq_singleton' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.schedSurvivors_eq_singleton

/-- info: 'ALT.blockPair_identifies' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.blockPair_identifies

-- The sharp identification window (`ALT/TapeHostSchedule.lean`): `schedSurvivors_eq_singleton`'s
-- three inequalities met against each of their own margins rather than a single `τ`-wide budget,
-- giving identification at every density below a quarter of the cross-class slack
-- (`identifies_of_lt_quarter`) and, at `μ = 0`, a refuting family above it
-- (`not_identifies_of_gt_quarter`).
set_option linter.style.longLine false in
/-- info: 'ALT.schedSurvivors_eq_singleton_sharp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.schedSurvivors_eq_singleton_sharp

set_option linter.style.longLine false in
/-- info: 'ALT.not_identifies_of_gt_quarter' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.not_identifies_of_gt_quarter

-- The profile-class family's own criterion instance (`ALT/BlockPairFamilyCriterion.lean`): the
-- family meets `ALT.Profile` at every `r ≥ 2` and identifies the true literal
-- from `r = 3` on, at density `η = 1 / (2 * r)` inside `identifies_of_lt_quarter`'s window. The
-- class-level overlap instance (`blockPairFamily_overlap`) routes through `𝗣𝗔⁻`
-- (`ALT.grownGuestReachesThresholdAt_uniform`), so it is guarded in
-- `AxiomAuditFoundation.lean` alongside `ALT.TapeHost.overlap`, not here.
/-- info: 'ALT.designObsF_profile' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.designObsF_profile

set_option linter.style.longLine false in
/-- info: 'ALT.blockPairFamily_identifies' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.blockPairFamily_identifies

-- The block-pair host's rule as an exhibited program. The numeral step `hostStepNum`/
-- `frameStepNum` bridges to `BlockPairHost.packed`/`BlockPairHost.frame` digit-by-digit through
-- `BlockPairHost.stateEquiv_digit`
-- (`hostStepNum_stateEquiv`/`frameStepNum_stateEquiv`); each is primitive recursive by direct
-- composition, tabulated (`hostTableFn`/`frameTableFn`), and identified with the packed tables
-- (`hostTableFn_eq`/`frameTableFn_eq`), giving fixed builders with no imported macro-law code.
-- `KE_hostPacked_le`/`KE_hostFrame_le` price the two tables at `elen <builder> + O(log Π [+ log
-- κ])`; `BlockPairHost.card_orbit_le_cbHue_cheap` is `BlockPairHost.card_orbit_le_cbHue` read at
-- those codes — the guest owned within an absolute constant plus `O(log Π)`, no imported code
-- parameter at all.

/-- info: 'ALT.tmSign_eq_tmBit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.tmSign_eq_tmBit

set_option linter.style.longLine false in
/-- info: 'ALT.tmPrefix_eq_tmPrefixBit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.tmPrefix_eq_tmPrefixBit

set_option linter.style.longLine false in
/-- info: 'ALT.blockSign_eq_blockSignBit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.blockSign_eq_blockSignBit

set_option linter.style.longLine false in
/-- info: 'ALT.BlockPairHost.designObs_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.BlockPairHost.designObs_eq

set_option linter.style.longLine false in
/-- info: 'ALT.BlockPairHost.tape_eq_decide_hostTapeBit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.BlockPairHost.tape_eq_decide_hostTapeBit

set_option linter.style.longLine false in
/-- info: 'ALT.BlockPairHost.stateEquiv_digit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.BlockPairHost.stateEquiv_digit

/-- info: 'ALT.hostStepNum_stateEquiv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.hostStepNum_stateEquiv

set_option linter.style.longLine false in
/-- info: 'ALT.frameStepNum_stateEquiv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.frameStepNum_stateEquiv

/-- info: 'ALT.primrec_hostTableFn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.primrec_hostTableFn

/-- info: 'ALT.hostTableFn_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.hostTableFn_eq

/-- info: 'ALT.eval_hostBuilder' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.eval_hostBuilder

/-- info: 'ALT.primrec_frameTableFn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.primrec_frameTableFn

/-- info: 'ALT.frameTableFn_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.frameTableFn_eq

/-- info: 'ALT.eval_frameBuilder' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.eval_frameBuilder

/-- info: 'ALT.KE_hostPacked_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.KE_hostPacked_le

/-- info: 'ALT.KE_hostFrame_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.KE_hostFrame_le

set_option linter.style.longLine false in
/-- info: 'ALT.BlockPairHost.card_orbit_le_cbHue_cheap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.BlockPairHost.card_orbit_le_cbHue_cheap

-- Theorem 6.6's noisy-branch machinery, read on the profile-class base: the surprise budget's rate
-- and the noise-gated absorption bound instantiated at the tape host's own fiber-facing stream
-- (`ALT.TapeHost.tapeStream`), and the positive fact that the derived tape fires past every
-- horizon at a positive-density profile.

set_option linter.style.longLine false in
/-- info: 'ALT.TapeHost.floorSurprise_rate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.TapeHost.floorSurprise_rate

set_option linter.style.longLine false in
/-- info: 'ALT.TapeHost.exists_untouched_copy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.TapeHost.exists_untouched_copy

set_option linter.style.longLine false in
/-- info: 'ALT.TapeHost.tapeStream_fires_forever' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.TapeHost.tapeStream_fires_forever

-- The base-plus-fiber composite (the tape host's own substrate with a `P`-copy redundant floored
-- fiber added as extra memory) is a member of `𝒮_L`: every field but the read-only-code witness is
-- the base's own (`ALT.TapeHost.substrateL`), transported through the composite's own
-- base-independence lemmas.
set_option linter.style.longLine false in
/-- info: 'ALT.TapeHost.comp_substrateL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.TapeHost.comp_substrateL

-- Survival by redundancy on the composite's own fiber ([Inevitability] §6 Theorem 6.6(iv)/(v′)):
-- an untouched copy exists and its reading is the single undamaged floored fiber's. No margin
-- enters, and no `𝗣𝗔⁻` machinery does either — this is `RedundantFiber`/`TapeHostFiber`'s own
-- combinatorics, not the crossing.
set_option linter.style.longLine false in
/-- info: 'ALT.TapeHost.comp_carries_survival' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.TapeHost.comp_carries_survival

/-! ## The Birkhoff port's trajectory-space tool: the single-orbit oracle guards -/

/-! ## Trajectory-space Tool (i) and the FJS-shaped oracle corollaries (`ALT/BirkhoffTool.lean`) -/

set_option linter.style.longLine false in
/-- info: 'ALT.timeAverage_tendsto_expectation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.timeAverage_tendsto_expectation

set_option linter.style.longLine false in
/-- info: 'ALT.mixing_oracle_sample_complexity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.mixing_oracle_sample_complexity

/-- info: 'ALT.mixing_oracle_tail_to' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.mixing_oracle_tail_to

/-- info: 'ALT.mixing_oracle_tail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.mixing_oracle_tail

/-- info: 'ALT.mixingHoeffding_of_iid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.mixingHoeffding_of_iid

set_option linter.style.longLine false in
/-- info: 'ALT.mixingHoeffding_of_nonpos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.mixingHoeffding_of_nonpos

set_option linter.style.longLine false in
/-- info: 'ALT.not_mixingHoeffding_pinned' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.not_mixingHoeffding_pinned

set_option linter.style.longLine false in
/-- info: 'ALT.mixing_oracle_truth_survives_noisy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.mixing_oracle_truth_survives_noisy

/-! ## Finite-horizon `MixingHoeffdingTo` (`ErgodicTheory/MixingHoeffding.lean`,
`ALT/BirkhoffTool.lean`) -/

set_option linter.style.longLine false in
/-- info: 'ALT.mixingHoeffdingTo_of_le_floor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.mixingHoeffdingTo_of_le_floor

set_option linter.style.longLine false in
/-- info: 'ALT.not_mixingHoeffdingTo_pinned' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.not_mixingHoeffdingTo_pinned

set_option linter.style.longLine false in
/-- info: 'ALT.mixingHoeffdingTo_mono_const' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.mixingHoeffdingTo_mono_const

set_option linter.style.longLine false in
/-- info: 'ALT.mixing_oracle_sample_complexity_to' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.mixing_oracle_sample_complexity_to

set_option linter.style.longLine false in
/-- info: 'ALT.mixing_oracle_truth_survives_noisy_to' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.mixing_oracle_truth_survives_noisy_to

/-! ## Finite-horizon SQ oracle over a schedule (`ALT/BirkhoffTool.lean`) -/

set_option linter.style.longLine false in
/-- info: 'ALT.empirical_isSQOracle_of_mixingTo' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.empirical_isSQOracle_of_mixingTo
