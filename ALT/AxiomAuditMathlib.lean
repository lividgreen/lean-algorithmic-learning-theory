import ALT.Decoupling
import ALT.ParameterizedNNO
import ALT.GodelInternalization
import ALT.RepFintype
import ALT.RecursorAlgebra
import ALT.Realizability
import ALT.RealizabilityCCC
import ALT.RealizabilityRecursor
import ALT.RealizabilityCoproduct
import ALT.CapacityLayer
import ALT.RealizerLength
import ALT.CategoricalThreshold
import ALT.ChengCCC
import ALT.FiniteInfoTheory
import ALT.Reflective
import ALT.CounterLearner
import ALT.MDLCoding
import ALT.GrunwaldMehtaDiscovery
import ALT.RetentionUpperBound
import ALT.BayesRedundancy
import ALT.DeterministicDiscovery
import ALT.CountableDiscovery
import ALT.ExtensionalDiscovery
import ALT.HellingerBridge
import ALT.KolmogorovTimeBounded
import ALT.PolyTimeAccounting
import ALT.ParityCounterexample
import ALT.SQVersionSpace
import ALT.SampleComplexity
import ALT.SQAlgorithm
import ALT.SQEnvelope
import ALT.SQOracle
import ALT.SQPredictiveTransfer
import ALT.SQPrunedMass
import ALT.SQMixtureSupermartingale
import ALT.SQObjects
import ALT.SQSearchPhaseMass
import ALT.Ville
import ALT.PrefixComplexity
import ALT.AdditiveComplexity
import ALT.BinaryConstant
import ALT.PrefixInvariance
import ALT.StructureFunction
import ALT.TimeCost
import ALT.PolyTime
import ALT.Collector
import ALT.DecisionListData
import ALT.DecisionListSolver
-- Guard-gap closure: pre-`#guard_msgs` modules (capstones guarded in the appended section below).
import ALT.CartesianClosed
import ALT.GodelThreshold
import ALT.RegimeConsistency
import ALT.CapacityThreshold
import ALT.MDLDominance
import ALT.RetentionOverhead
import ALT.PriorNormalization
import ALT.EpsilonZeroBound
import ALT.PressureWindow
import ALT.ExactBreakeven
import ALT.KReconnection
import ALT.KolmogorovComplexity
import ALT.KolmogorovBitlen
import ALT.ProofChainSkeleton

-- Tier-1 formal check, not Mathlib-destined: opt out of the house-style linters.
set_option linter.style.header false
set_option linter.style.longLine false

/-!
# Axiom audit (Mathlib side) — machine-ENFORCED axiom-cleanliness (Papers I, II, III)

Companion to `ALT/AxiomAuditFoundation.lean` for the umbrella-Mathlib–side theorems (the
Foundation/Mathlib import divide forbids one file importing both). Each `#guard_msgs in
#print axioms …` **fails `lake build`** if the theorem's axiom set drifts. The Decoupling core is
even `Classical.choice`-free (`[propext, Quot.sound]`), and the necessity counterexample is fully
constructive (`[propext]`).

Coverage spans all three Mathlib-side papers: **Paper I** (decoupling, bounded recursor, realizability
CCC, categorical threshold), **Paper II** (MDL coding/dominance, Cheng-CCC necessity, finite
info-theory, Grünwald–Mehta / deterministic / countable discovery, retention), and **Paper III**
(time-bounded Kolmogorov complexity, poly-time accounting, the parity SQ counterexample, SQ
version-space pruning, and the sample-complexity ε₀-absorption).
-/

-- §3 Decoupling Lemma (FV-7) — constructive core
/-- info: 'Decoupling.decoupling_iff_persists_all' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Decoupling.decoupling_iff_persists_all

/-- info: 'Decoupling.necessity_needs_faithful' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Decoupling.necessity_needs_faithful

-- §5 bounded recursor (FV-2)
/-- info: 'ParameterizedNNO.no_true_nno' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ParameterizedNNO.no_true_nno

-- §6.3 internalization Tier-1 (FV-8) + §5.4 Prop 5.4
/-- info: 'GodelInternalization.decide_godel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GodelInternalization.decide_godel

/-- info: 'GodelInternalization.capacity_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GodelInternalization.capacity_bound

/-- info: 'GodelInternalization.proofcode_workspace_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GodelInternalization.proofcode_workspace_bound

/-- info: 'GodelInternalization.prop_5_4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GodelInternalization.prop_5_4

/-- info: 'GodelInternalization.internalization' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GodelInternalization.internalization

-- §4 / §6.1 finite-set CCC (FV-10)
/-- info: 'RepFintype.reflective_satisfiable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RepFintype.reflective_satisfiable

/-- info: 'RepFintype.exp_finite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RepFintype.exp_finite

-- §5 F19: the bounded recursor upgraded to a categorical UNIVERSAL PROPERTY, reusing
-- Mathlib's `CategoryTheory.Limits.IsInitial`. `recursorCone_isInitial` — the paper recursor is the
-- INITIAL object of the (thin) category of depth-≤M recursion cones (relativized, since `no_true_nno`
-- forbids a true NNO on finite `W`); `recursorCone_canonical` — any other initial cone agrees with it
-- on the orbit `N_M` (canonical, "not merely an orbit"). `Classical.choice` is genuine (recursorCone
-- extracts the recursor via `Exists.choose`).
/-- info: 'ParameterizedNNO.ParamNNO.recursorCone_isInitial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ParameterizedNNO.ParamNNO.recursorCone_isInitial

/-- info: 'ParameterizedNNO.ParamNNO.recursorCone_canonical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ParameterizedNNO.ParamNNO.recursorCone_canonical

-- §5 F19 sharpened: a GENUINE, discriminating initial algebra reusing Mathlib's
-- `CategoryTheory.Endofunctor.Algebra`. Unlike the thin/chaotic FV-17 cone category (where every cone
-- is initial by `Subsingleton`), `boundedInitialAlgebra_isInitial` is initial with honest algebra-hom
-- morphisms — uniqueness is a real orbit induction. It is initial only in the SATURATING subcategory
-- (`no_true_nno`: the unrestricted initial `𝟙 ⊕ (·)`-algebra is `ℕ`); `boundedAlg_str_not_injective`
-- records that the structure map is not iso, so Lambek does not force a fixed point here.
/-- info: 'RecursorAlgebra.boundedInitialAlgebra_isInitial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RecursorAlgebra.boundedInitialAlgebra_isInitial

/-- info: 'RecursorAlgebra.boundedAlg_str_not_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RecursorAlgebra.boundedAlg_str_not_injective

-- §4.1 realizability category (FV-11)
/-- info: 'Realizability.universal_evaluator' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Realizability.universal_evaluator

/-- info: 'Realizability.counter_step_realizes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Realizability.counter_step_realizes

-- §4.1 / §4.5: every function between FINITE assemblies is a morphism (so `Prf`/`Decide` are
-- morphisms of Rep(S), not merely total Boolean functions).
/-- info: 'Realizability.realizes_of_finite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Realizability.realizes_of_finite

-- §4.3 realizability CCC (FV-12)
/-- info: 'RealizabilityCCC.exp_universal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RealizabilityCCC.exp_universal

-- §4 / §6.1 unified CCC ∧ recursor on ONE carrier (FV-13)
/-- info: 'RealizabilityRecursor.reflectiveAsm_satisfiable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RealizabilityRecursor.reflectiveAsm_satisfiable

-- §6 Consequence on the GENUINE single carrier (FV-13): the unified `ReflectiveAsm` ⟹
-- represents-an-underivable-truth, not the trivially-true `Type`-CCC stand-in of FV-5.
/-- info: 'RealizabilityRecursor.reflectiveAsm_representsUnderivableTruth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RealizabilityRecursor.reflectiveAsm_representsUnderivableTruth

-- §6.1/§6.3 Theorem 6.2 as ONE machine-checked theorem on the genuine carrier (FV-15):
-- reflective object (Def 6.1) ∧ explicit capacity `2n` (FitsIn) ∧ §6.3 consequence, bundled.
/-- info: 'CategoricalThreshold.categorical_threshold' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CategoricalThreshold.categorical_threshold

-- §4 FINITE COPRODUCTS in the realizability category `Asm` (Paper I item 3; upstreamable):
-- the initial object (`initialAsm_isInitial`) and the binary coproduct's copairing universal property
-- (`coprod_universal` — existence AND uniqueness of the mediating realized morphism), plus the
-- finite-domain trackability lemma (`trackable_of_finDom`) that makes maps out of a finite assembly
-- genuine morphisms. New realizability infrastructure, absent from Mathlib.
/-- info: 'RealizabilityCoproduct.initialAsm_isInitial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RealizabilityCoproduct.initialAsm_isInitial

/-- info: 'RealizabilityCoproduct.coprod_universal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RealizabilityCoproduct.coprod_universal

/-- info: 'RealizabilityCoproduct.trackable_of_finDom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RealizabilityCoproduct.trackable_of_finDom

-- §5 FV-18 ON THE GENUINE CARRIER (Paper I item 3): the endofunctor `X ↦ 𝟙 ⊕ X` on `Asm` (which
-- exists precisely because coproducts now do), and the discriminating initial `𝟙 ⊕ (·)`-algebra of
-- the saturating subcategory — the FV-18 headline restated on the SAME carrier `Asm` as the CCC and
-- the §6.3 checkers (no longer the `Type` stand-in). Honest algebra-hom morphisms (uniqueness a real
-- orbit induction), initial only in the saturating subcategory (`no_true_nno`); the structure map is
-- not injective (`boundedAlgAsm_str_not_injective`), so Lambek does not force a finite fixed point.
/-- info: 'RealizabilityCoproduct.succEndoAsm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RealizabilityCoproduct.succEndoAsm

/-- info: 'RealizabilityCoproduct.boundedInitialAlgebraAsm_isInitial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RealizabilityCoproduct.boundedInitialAlgebraAsm_isInitial

/-- info: 'RealizabilityCoproduct.boundedAlgAsm_str_not_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RealizabilityCoproduct.boundedAlgAsm_str_not_injective

-- §4.2/§4.3 capacity layer: finite full subcategory, product closure, exponential overflow (FV-14)
/-- info: 'CapacityLayer.recursorAsm_fitsIn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CapacityLayer.recursorAsm_fitsIn

/-- info: 'CapacityLayer.prodAsm_fitsIn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CapacityLayer.prodAsm_fitsIn

/-- info: 'CapacityLayer.exp_card_overflow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CapacityLayer.exp_card_overflow

-- §4.3 F4 realizer-length non-closure (Shannon counting bound) — the realizer-length sibling of
-- FV-14: the SAME `2^s` capacity threshold that overflows the exponential in cardinality forces a
-- genuine morphism to need a realizer of bit-length `> s`. `Classical.choice` is genuine (via
-- `choose` on the short-realizer selector and `realizes_of_finite`).
/-- info: 'Realizability.realizer_length_overflow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Realizability.realizer_length_overflow

/-- info: 'Realizability.exp_realizer_overflow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Realizability.exp_realizer_overflow

-- §4.3 F4 explicit exponential magnitude: the literal `≈ 2^{|s_work|}`-bit figure (Paper I §4.3)
-- — the SAME fitting object needs a realizer of bit-length `≥ s·2^s`, sharpening the
-- linear `> s` figure of `exp_realizer_overflow` (Shannon counting bound at `b = s·2^s − 1`).
/-- info: 'Realizability.exp_realizer_overflow_exponential' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Realizability.exp_realizer_overflow_exponential

-- §6 reflective assembly (FV-5)
/-- info: 'ReflectiveAssembly.reflective_representsUnderivableTruth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReflectiveAssembly.reflective_representsUnderivableTruth

-- §4.4 / Conj 4.4 second learner instance (FV-6)
/-- info: 'CounterLearner.rules_card' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CounterLearner.rules_card

/-- info: 'CounterLearner.step_eq_nno_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CounterLearner.step_eq_nno_succ

/-- info: 'CounterLearner.nno_orbit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CounterLearner.nno_orbit

-- Paper II §4 — Cheng (2026) Theorem 4 re-checked: necessity core + the necessary-not-sufficient
-- point (refuting Prop 4.2's earlier misuse), and the finite info-theory foundation (FV-9).
/-- info: 'ChengCCC.cccLower_vacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChengCCC.cccLower_vacuous

/-- info: 'ChengCCC.misid_lower_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChengCCC.misid_lower_bound

/-- info: 'ChengCCC.forgetting_lower_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChengCCC.forgetting_lower_bound

/-- info: 'FiniteInfoTheory.entropy_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FiniteInfoTheory.entropy_nonneg

-- FV-9 (cont.): mutual information of a joint pmf and its nonnegativity (finite Gibbs) — the first
-- discharged brick of the DPI/Fano interface that `ChengCCC` still carries as named hypotheses.
/-- info: 'FiniteInfoTheory.mutualInfo_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FiniteInfoTheory.mutualInfo_nonneg

-- FV-9 (cont.): entropy form of MI `I(X;Y) = H(X) − H(X|Y)` — discharges the `hCond` identity.
/-- info: 'FiniteInfoTheory.mutualInfo_eq_sub_condEntropy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FiniteInfoTheory.mutualInfo_eq_sub_condEntropy

-- FV-9 (cont.): conditional mutual information nonnegativity `I(X;Z|Y) ≥ 0` (per-slice finite Gibbs).
/-- info: 'FiniteInfoTheory.condMutualInfo_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FiniteInfoTheory.condMutualInfo_nonneg

-- FV-9 (cont.): the data-processing inequality `I(X;Z) ≤ I(X;Y)` for a Markov chain `X → Y → Z` —
-- the rigorous content discharging `hDPI` at the chain `T → c → θ`.
/-- info: 'FiniteInfoTheory.dataProcessing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FiniteInfoTheory.dataProcessing

-- FV-9 (cont.): Fano's inequality `(condEntropy μ − 1)/log(K−1) ≤ Pe` — discharges `hFano`.
/-- info: 'FiniteInfoTheory.fano'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FiniteInfoTheory.fano'

-- FV-9 (cont.): the other DPI direction `I(X;Z) ≤ I(Y;Z)` — gives `I(T;θ) ≤ I(c;θ) ≤ C_ctx`.
/-- info: 'FiniteInfoTheory.dataProcessing'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FiniteInfoTheory.dataProcessing'

-- FV-9 capstone: Cheng's misidentification bound with DPI / identity / Fano all DISCHARGED —
-- only the modelling setup (joint ν + MarkovCI, decoder g, capacity bound, K ≥ 3) remains.
/-- info: 'ChengCCC.cheng_misid_bound_discharged' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChengCCC.cheng_misid_bound_discharged

-- FV-9 capstone (cont.): the forgetting lower bound with DPI / identity / Fano all DISCHARGED —
-- only the modelling setup plus Cheng's informal Step-4 link `hConn` remain.
/-- info: 'ChengCCC.cheng_forgetting_bound_discharged' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChengCCC.cheng_forgetting_bound_discharged

-- Paper II Theorem 2.1 eq. (2): the lookup-table coding lower bound, content-checking
-- `MDLDominance.Ltable = L`. Pigeonhole bound on ANY lossless code (`exists_long_codeword`), the
-- off-by-one-free fixed-width code (`tableEnc_length_ge`), and the `Ltable`-connection.
/-- info: 'MDLCoding.exists_long_codeword' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MDLCoding.exists_long_codeword

/-- info: 'MDLCoding.tableEnc_length_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MDLCoding.tableEnc_length_ge

/-- info: 'MDLCoding.ltable_lower_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MDLCoding.ltable_lower_bound

-- Paper II Theorem 2.1 eq. (1): the rule-based two-part code upper bound, content-checking
-- `MDLDominance.Lrule`. The self-delimiting `2·log₂ r` program-framing cost (`selfDelim_length_le`),
-- its losslessness (`selfDelim_injective`), and the assembled two-part code length (`lrule_upper_bound`).
/-- info: 'MDLCoding.selfDelim_length_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MDLCoding.selfDelim_length_le

-- Cor 2.2 content-check: the self-delimiting code realizes the bits-form capacity threshold
-- `CapacityThreshold.KminBits r 1`, grounding the asserted `2 log r` overhead in a real code length.
/-- info: 'MDLCoding.selfDelim_realizes_KminBits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MDLCoding.selfDelim_realizes_KminBits

/-- info: 'MDLCoding.selfDelim_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MDLCoding.selfDelim_injective

/-- info: 'MDLCoding.lrule_upper_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MDLCoding.lrule_upper_bound

-- Paper II Theorem 2.1 CAPSTONE: dominance between actual code lengths — the rule-based two-part
-- code is strictly shorter than the lookup-table code, combining eq. (1) + eq. (2) + the bit-unit
-- regime margin. (`MDLDominance.mdl_dominance` is the natural-log arithmetic; this is the codes.)
/-- info: 'MDLCoding.mdl_dominance_codes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MDLCoding.mdl_dominance_codes

-- eq.(1) residuals closed: the two-part code is genuinely lossless (`twoPart_injective`, the Elias-γ
-- prefix decoder) and decode-correctness links the program to the generated output via Code/Computes
-- (`ruleEncode_lossless`), giving the sequence-linked capstone (`mdl_dominance_codes_generated`).
/-- info: 'MDLCoding.twoPart_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MDLCoding.twoPart_injective

/-- info: 'MDLCoding.ruleEncode_lossless' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MDLCoding.ruleEncode_lossless

/-- info: 'MDLCoding.mdl_dominance_codes_generated' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MDLCoding.mdl_dominance_codes_generated

-- Paper II §3 Theorem 3.1: the central/Bernstein condition (§3.2, proved) and the §3.3 discovery
-- assembly (threshold + Markov arithmetic, proved; GM Thm 7.4 / Markov / posterior-of-close imported
-- as named hypotheses — so only [propext, Classical.choice, Quot.sound], no extra deep axioms).
/-- info: 'GrunwaldMehtaDiscovery.bernstein_central' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GrunwaldMehtaDiscovery.bernstein_central

/-- info: 'GrunwaldMehtaDiscovery.discovery_posterior_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GrunwaldMehtaDiscovery.discovery_posterior_bound

-- §3.3 Markov step DISCHARGED: `markov_tail_real` is a real application of Mathlib's Markov
-- inequality (`mul_meas_ge_le_integral_of_nonneg`), and `discovery_posterior_bound_markov` re-derives
-- the discovery bound using it instead of the abstract `hmarkov` hypothesis.
/-- info: 'GrunwaldMehtaDiscovery.markov_tail_real' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GrunwaldMehtaDiscovery.markov_tail_real

/-- info: 'GrunwaldMehtaDiscovery.discovery_posterior_bound_markov' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GrunwaldMehtaDiscovery.discovery_posterior_bound_markov

-- Paper II §4 Prop 4.2 (retention upper bound): the discovered rule persists under the
-- conditional-regeneration architecture, reusing Paper I's Decoupling Lemma. `retention_persists`
-- and `retention_upper_bound` are CHOICE-FREE ([propext, Quot.sound]) — inherited from Decoupling's
-- choice-free core; only the quantitative `Fgt̄ = 0` (Finset/ℝ machinery) pulls in `Classical.choice`.
/-- info: 'RetentionUpperBound.retention_persists' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RetentionUpperBound.retention_persists

/-- info: 'RetentionUpperBound.retention_upper_bound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RetentionUpperBound.retention_upper_bound

/-- info: 'RetentionUpperBound.expected_forgetting_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RetentionUpperBound.expected_forgetting_zero

-- Paper II §3 Sub-problem B (Bayes-mixture redundancy, realizable-deterministic route toward dropping
-- `hrate`): the step-(3) calculus inequality (`log_le_hellinger`) + point-mass identity
-- (`hellinger_point_mass`), and the step-(1) mixture regret (`mixture_regret_log`). All elementary.
/-- info: 'BayesRedundancy.log_le_hellinger' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms BayesRedundancy.log_le_hellinger

/-- info: 'BayesRedundancy.hellinger_point_mass' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms BayesRedundancy.hellinger_point_mass

/-- info: 'BayesRedundancy.mixture_regret_log' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms BayesRedundancy.mixture_regret_log

-- §3 Sub-problem B (cont.): the prequential telescope (step 2) and the assembled rate (step 4) —
-- `−log P̄(n) = ∑ₜ −log condₜ`, then `∑ₜ D_H²ₜ ≤ K(R)·ln2/2` and the per-step average ≤ K(R)·ln2/(2n).
-- This is the Bayes-mixture redundancy rate (eq. 3) PROVED (realizable-deterministic), not assumed via `hrate`.
/-- info: 'BayesRedundancy.telescope' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms BayesRedundancy.telescope

/-- info: 'BayesRedundancy.cumulative_hellinger' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms BayesRedundancy.cumulative_hellinger

/-- info: 'BayesRedundancy.average_hellinger_rate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms BayesRedundancy.average_hellinger_rate

-- §3 Theorem 3.1 UNCONDITIONAL (realizable-deterministic): competitor-likelihood decay gives
-- posterior concentration with NO Grünwald–Mehta / Markov / posterior-of-close hypothesis — only the
-- model (pmf q, prior w R = 2^{−K R}, ∑ w ≤ 1), realizability, and per-step separation.
/-- info: 'DeterministicDiscovery.competitor_likelihood_decay' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeterministicDiscovery.competitor_likelihood_decay

/-- info: 'DeterministicDiscovery.deterministic_discovery' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeterministicDiscovery.deterministic_discovery

-- §3 Theorem 3.1 over a COUNTABLE hypothesis class (the paper's `2^{−K(R')}` prior over all programs,
-- §1.1): the same unconditional realizable-deterministic discovery with `∑'` over `ι`, `Summable w`,
-- `∑' w ≤ 1`. Still NO Grünwald–Mehta / Markov / posterior-of-close.
/-- info: 'CountableDiscovery.countable_posterior_lower_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CountableDiscovery.countable_posterior_lower_bound

/-- info: 'CountableDiscovery.countable_discovery' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CountableDiscovery.countable_discovery

-- Paper II §3.3 Proposition 3.2 (FV-16): extensional `[R]`-concentration for the near-twin-rich
-- countable class — the honest, non-vacuous discovery statement that DROPS per-step separation
-- entirely. Indicator (`0/1`) likelihoods: the on-trajectory equivalence class `[R]` has positive
-- constant mass `P_{[R]}` (`PR_pos`), the surviving off-`[R]` mass is a Kraft tail vanishing by
-- dominated convergence (`tail_tendsto_zero` — the crux, every competitor falsified at a finite
-- branching time), the normalizer splits `Z_n = P_{[R]} + tail_n` (`Zmass_eq_PR_add_tail`), so the
-- posterior on `[R]` rises MONOTONICALLY to `1` (`extensional_R_concentration` — `postR_monotone` ∧
-- `postR_tendsto_one`). NO separation hypothesis; `ι` a general countable type (no `[Fintype ι]`);
-- only `0 ≤ w`, `Summable w`, antitone consistency, and a true rule `R ∈ [R]` with `0 < w R`.
/-- info: 'ExtensionalDiscovery.Zmass_eq_PR_add_tail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ExtensionalDiscovery.Zmass_eq_PR_add_tail

/-- info: 'ExtensionalDiscovery.tail_tendsto_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ExtensionalDiscovery.tail_tendsto_zero

/-- info: 'ExtensionalDiscovery.postR_tendsto_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ExtensionalDiscovery.postR_tendsto_one

/-- info: 'ExtensionalDiscovery.extensional_R_concentration' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ExtensionalDiscovery.extensional_R_concentration

-- Paper II §3.3 FV-15: genuine ε₀-Hellinger + the ε₀→query-separation bridge (`HellingerBridge.lean`).
-- Target A makes ε₀ a real squared-Hellinger quantity: `sqHellinger_pos_of_ne` is the
-- positive-definiteness `EpsilonZeroBound.eps0_pos` had to assume (`0 < sep i`); `eps0H_pos` is ε₀'s
-- strict positivity from pairwise-distinctness alone; `hsep_of_eps0H`/`discovery_of_eps0H` reconnect a
-- per-step eps0H-floor to `DeterministicDiscovery.deterministic_discovery`'s `hsep`, so eps0H drives
-- Theorem 3.1. Target B is the bridge: `sqHellinger_le_tv` (`D_H² ≤ TV`), `exists_separating_query`
-- (the sign query's `2·TV` mean gap), `identifiable_of_sqHellinger` (gap `≥ 2ε₀`), and
-- `separates_of_sqHellinger` (2τ-identifiability for `τ < ε₀`, in FV-J's `Separates` shape). The
-- certified scale is the honest `2ε₀`/`τ < ε₀`, NOT the `√ε₀` a mean-level reading assumes (module
-- boundary note; the papers' `√ε₀` wording carries a mean-level qualifier).
/-- info: 'HellingerBridge.sqHellinger_pos_of_ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms HellingerBridge.sqHellinger_pos_of_ne

/-- info: 'HellingerBridge.eps0H_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms HellingerBridge.eps0H_pos

/-- info: 'HellingerBridge.eps0H_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms HellingerBridge.eps0H_le

/-- info: 'HellingerBridge.hsep_of_eps0H' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms HellingerBridge.hsep_of_eps0H

/-- info: 'HellingerBridge.discovery_of_eps0H' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms HellingerBridge.discovery_of_eps0H

/-- info: 'HellingerBridge.sqHellinger_le_tv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms HellingerBridge.sqHellinger_le_tv

/-- info: 'HellingerBridge.exists_separating_query' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms HellingerBridge.exists_separating_query

/-- info: 'HellingerBridge.identifiable_of_sqHellinger' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms HellingerBridge.identifiable_of_sqHellinger

/-- info: 'HellingerBridge.separates_of_sqHellinger' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms HellingerBridge.separates_of_sqHellinger

-- Paper III §2 time-bounded Kolmogorov complexity (FV-Kt): on Mathlib's `Code`, the resource
-- hierarchy `K ≤ K_t` (`K_le_K_t`), `K_t` antitone in the time budget (`K_t_antitone`), and
-- `K_t = K` for all sufficiently large budgets (`K_t_eventually`). These live in `namespace
-- KolmogorovComplexity` (the file is `KolmogorovTimeBounded.lean`).
/-- info: 'KolmogorovComplexity.K_le_K_t' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KolmogorovComplexity.K_le_K_t

/-- info: 'KolmogorovComplexity.K_t_antitone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KolmogorovComplexity.K_t_antitone

/-- info: 'KolmogorovComplexity.K_t_eventually' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KolmogorovComplexity.K_t_eventually

-- Paper III §4 Theorem 4.1 step-(c) total-work accounting (FV-B1): an `O(r·log(1/δ))` search window
-- times an `O(r)` per-step cost gives total work `O(r²·log(1/δ))` — thin product bookkeeping.
/-- info: 'PolyTimeAccounting.polytime_accounting' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PolyTimeAccounting.polytime_accounting

-- Paper III §5 parity SQ counterexample (FV-A3): every real power of `r` is little-o of the modeled
-- parity statistical dimension `d_SQ` (`poly_isLittleO_dSQ`), so `d_SQ` is not polynomially bounded
-- (`dSQ_not_polyBounded`) — Assumption A fails for parity, hence Theorem 4.1 does not apply to it.
/-- info: 'ParityCounterexample.poly_isLittleO_dSQ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ParityCounterexample.poly_isLittleO_dSQ

/-- info: 'ParityCounterexample.dSQ_not_polyBounded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ParityCounterexample.dSQ_not_polyBounded

-- Paper III §4 / App. A SQ version-space pruning (FV-A4): the candidate set stays poly-bounded under a
-- poly-bounded `d_SQ` (`candidates_polyBounded`), the truth is never pruned (`truth_survives_pruning`),
-- and a `> 3τ`-separated impostor IS pruned (`separated_impostor_pruned`) — soundness of SQ pruning.
/-- info: 'SQVersionSpace.candidates_polyBounded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SQVersionSpace.candidates_polyBounded

/-- info: 'SQVersionSpace.truth_survives_pruning' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SQVersionSpace.truth_survives_pruning

/-- info: 'SQVersionSpace.separated_impostor_pruned' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SQVersionSpace.separated_impostor_pruned

-- Paper III §4 Theorem 4.1(i) sample complexity (FV-B2): the "Remark on ε₀" absorption collapsing the
-- imported Paper II Thm 3.1 discovery bound `O((r+log(1/δ))/ε₀)` to the stated `O(r²·log(1/δ))` under
-- the benign-class `ε₀ = Ω(1/r)`. (Complements FV-B1: B1 = step-(c) total work, this = part-(i) count.)
/-- info: 'SampleComplexity.sample_complexity_r2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SampleComplexity.sample_complexity_r2

-- Paper III §3 ensemble SQ oracle, Tool (ii) (FV-E): Hoeffding concentration of the empirical SQ
-- answer (`sq_oracle_concentration`), the `n ≥ (2/τ²)·log(2/δ)` sample complexity
-- (`sq_oracle_sample_complexity`), and the §3→FV-A4 wiring that discharges the truth-survives
-- hypothesis with probability `≥ 1−δ` (`sq_oracle_truth_survives`).
/-- info: 'SQOracle.sq_oracle_concentration' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SQOracle.sq_oracle_concentration

/-- info: 'SQOracle.sq_oracle_sample_complexity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SQOracle.sq_oracle_sample_complexity

/-- info: 'SQOracle.sq_oracle_truth_survives' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SQOracle.sq_oracle_truth_survives

-- Stage-5a FV-E → FV-J glue: the finite-query union bound carrying per-query concentration to FV-J's
-- oracle object. `sq_oracle_uniform_tail` — if each of `Qs` fails tolerance `τ` w.p. `≤ δ`, then SOME
-- query fails w.p. `≤ |Qs|·δ` (`measure_biUnion_finset_le`). `empirical_isSQOracle` — off that event
-- (w.p. `≥ 1 − |Qs|·δ`) the `Qs`-restricted empirical answers satisfy `SQObjects.IsSQOracle`.
/-- info: 'SQOracle.sq_oracle_uniform_tail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SQOracle.sq_oracle_uniform_tail

/-- info: 'SQOracle.empirical_isSQOracle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SQOracle.empirical_isSQOracle

-- Stage-5b (closes the 5a residue): the per-query i.i.d. instantiation discharging the union bound's
-- `htail` from `sq_oracle_concentration` — `n ≥ (2/τ²)·log(2|Qs|/δ)` samples per query ⇒ the
-- empirical answers fail `IsSQOracle` on `↥Qs` w.p. `≤ δ`.
/-- info: 'SQOracle.empirical_isSQOracle_of_iid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SQOracle.empirical_isSQOracle_of_iid

-- Paper III App. A Claim 2, post-discovery half (FV-F): geometric decay kills the `2^K` prefactor
-- past `T_discover` (`prefactor_le`), so the accumulated post-discovery pruned mass is `≤ δ/2` by
-- competitor-decay + Kraft alone — no maximal inequality (`accumulated_pruned_mass_le`).
/-- info: 'SQPrunedMass.prefactor_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SQPrunedMass.prefactor_le

/-- info: 'SQPrunedMass.accumulated_pruned_mass_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SQPrunedMass.accumulated_pruned_mass_le

-- Paper III App. A predictive transfer (FV-H): the Bayes-mixture step that turns a bounded pruned
-- mass into a preserved one-step predictive guarantee, made EXACT. `mixture_prune_perturbation` —
-- the one-step L1 perturbation `∑ₓ|Q x − P x| ≤ 2·(W/U)` (TV ≤ W/U, no hidden constant), sharpening
-- the prose "≤ δ/2 in total". `predictive_transfer` — an α-guarantee on the full mixture transfers
-- to `α + 2·(W/U)` on the renormalized survivor mixture. `accumulated_perturbation_le` — the total
-- L1 damage across a step family is `≤ 2·∑ₜ εₜ`, consuming the FV-F/FV-G mass budgets.
/-- info: 'SQPredictiveTransfer.mixture_prune_perturbation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SQPredictiveTransfer.mixture_prune_perturbation

/-- info: 'SQPredictiveTransfer.predictive_transfer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SQPredictiveTransfer.predictive_transfer

/-- info: 'SQPredictiveTransfer.accumulated_perturbation_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SQPredictiveTransfer.accumulated_perturbation_le

-- Paper III App. A Claim 2, search-phase half (FV-G): the log-Bayes potential companion to FV-F.
-- The truth-potential telescopes into `[0,K]` (`potential_range`), and the pointwise mass bound
-- `m ≤ −ln(1−m)` summed over the pruned set and charged to that potential (`hcharge`) gives the
-- accumulated search-phase pruned mass `≤ K = ln2·K(R) = O(r)` (`search_phase_pruned_mass_le`) —
-- the discovery-regret order, not `δ/2`. No maximal inequality; the regret/martingale control enters
-- only as the imported `hcharge`, exactly as FV-F imports decay+normalizer as `hdecay`.
/-- info: 'SQSearchPhaseMass.potential_range' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SQSearchPhaseMass.potential_range

/-- info: 'SQSearchPhaseMass.search_phase_pruned_mass_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SQSearchPhaseMass.search_phase_pruned_mass_le

-- `pruned_mass_le_budget`: the slack form — the charge may exceed the telescoped potential drop by
-- an additive budget `B`, degrading the mass bound to `C + B`. The deterministic core the Ville
-- chain (below) rests on, with `B = ln(1/δ)` supplying the between-pruning net rise.
/-- info: 'SQSearchPhaseMass.pruned_mass_le_budget' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SQSearchPhaseMass.pruned_mass_le_budget

-- FV-G hardening (`ALT/Ville.lean`): the excursion control `hcharge` used to import is now a
-- PROVED theorem. `ville_inequality` — Ville's inequality for a non-negative supermartingale `Z`
-- (`𝔼[Z 0] < ∞`): `μ{∃ n, λ ≤ Z_n} ≤ 𝔼[Z 0]/λ`, proved via optional stopping on `-Z`
-- (`Submartingale.expected_stoppedValue_mono`) + the hitting lower bound + continuity from below —
-- NOT via `maximal_ineq` (submartingale-locked). `ville_potential_budget` — the `λ = 1/δ` corollary
-- `μ{∃ n, 1/δ ≤ Z_n} ≤ δ` under `𝔼[Z 0] ≤ 1`, the search-phase excursion budget of Appendix A Claim 2.
/-- info: 'Ville.ville_inequality' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ville.ville_inequality

/-- info: 'Ville.ville_potential_budget' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ville.ville_potential_budget

-- FV-G CHAINED (P-III stage 1): `search_phase_mass_ville_chain` wires the two cores together — the
-- accumulated pruned mass exceeds `C + ln(1/δ)` only on the Ville excursion event, so
-- `μ{mass > C + ln(1/δ)} ≤ δ` (the paper's `O(r + log(1/δ))` w.h.p.). The `ln(1/δ)` term is DERIVED
-- from `ville_potential_budget` via `pruned_mass_le_budget`, not assumed; what stays modeled is the
-- supermartingale premise on `Z`, the Kraft `hΦ0`, and the no-excursion-conditional charge `hcharge`.
/-- info: 'SQSearchPhaseMass.search_phase_mass_ville_chain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SQSearchPhaseMass.search_phase_mass_ville_chain

-- FV-I (P-III stage 3): the FV-G supermartingale premise DISCHARGED. On the trajectory space
-- `ℕ → X` with Mathlib's coordinate filtration `Filtration.piLE`, `Z_t = ∑ w(R')·L_t(R')` (abstract
-- `[0,1]`-valued, `ℱ_{s+1}`-measurable per-step factors) is pointwise antitone + bounded + adapted,
-- hence a genuine `Supermartingale` for ANY probability truth law (`Z_supermartingale`, via
-- `supermartingale_nat` + `condExp_mono` + `condExp_of_stronglyMeasurable` — no Ionescu–Tulcea).
-- `𝔼[Z_0] ≤ 1` from Kraft (`integral_Z_zero_le_one`), and `search_phase_mass_bound` instantiates the
-- FV-G chain at this `Z` — the `hsuper`/`hnn`/`hZ0` premises are gone, only the FV-G search-side data
-- (`pruned`, `m`, `Φ`, `hcharge`) survives.
/-- info: 'SQMixtureSupermartingale.Z_supermartingale' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SQMixtureSupermartingale.Z_supermartingale

/-- info: 'SQMixtureSupermartingale.integral_Z_zero_le_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SQMixtureSupermartingale.integral_Z_zero_le_one

/-- info: 'SQMixtureSupermartingale.search_phase_mass_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SQMixtureSupermartingale.search_phase_mass_bound

-- FV-I hardening (stage-5a): the abstract factor `g` made CONCRETE for the paper's DETERMINISTIC
-- rule class. `detFactor pred i s ω = 𝟙[pred i s (ω|_{<s}) = ω s]` is the `0/1` likelihood of a
-- deterministic rule; `detFactor_stronglyMeasurable` PROVES its `ℱ_{s+1}`-strong measurability from
-- `Filtration.piLE`'s coordinate structure over a discrete alphabet (the `hgmeas` premise, no longer
-- a hypothesis); `L_det_eq_indicator` shows `L_det` is the alive-consistent indicator; and
-- `Z_det_supermartingale` is the FV-I supermartingale with NO abstract-`g` hypotheses left.
/-- info: 'SQMixtureSupermartingale.detFactor_stronglyMeasurable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SQMixtureSupermartingale.detFactor_stronglyMeasurable

/-- info: 'SQMixtureSupermartingale.L_det_eq_indicator' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SQMixtureSupermartingale.L_det_eq_indicator

/-- info: 'SQMixtureSupermartingale.Z_det_supermartingale' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SQMixtureSupermartingale.Z_det_supermartingale

-- FV-J (P-III stage 4): the SQ objects made GENUINE (`ALT/SQObjects.lean`). The statistical
-- dimension `sqDim = (M.powerset.filter (SepFam …)).sup card` (§3.4) with its DEFINITIONAL
-- characterization `sepFam_card_le_sqDim` (every τ-separated subfamily has card ≤ sqDim) and survivor
-- pigeonhole `survivors_card_le_sqDim`; BQ1 distribution-specificity `sqDim_mono_queries` (fewer
-- separating queries ⇒ smaller-or-equal dimension); the poly-bound reuse of FV-A4's envelope
-- `survivors_polyBounded_of_separated`. The parity headline: exact character orthogonality
-- `ansPar_eq` (`= 1` iff `S = φ`, else `0`), the dimension theorem `sqDim_parity_ge : 2^n ≤ sqDim`
-- for `τ < 1`, and the FV-A3 bridge `parity_dSQ_ge_exp` promoting the previously-MODELED
-- `d_SQ = 2^Ω(n)` premise to a proof (`dSQ (log 2) n = 2^n ≤ sqDim`).
/-- info: 'SQObjects.sepFam_card_le_sqDim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SQObjects.sepFam_card_le_sqDim

/-- info: 'SQObjects.survivors_card_le_sqDim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SQObjects.survivors_card_le_sqDim

/-- info: 'SQObjects.sqDim_mono_queries' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SQObjects.sqDim_mono_queries

/-- info: 'SQObjects.survivors_polyBounded_of_separated' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SQObjects.survivors_polyBounded_of_separated

/-- info: 'SQObjects.ansPar_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SQObjects.ansPar_eq

/-- info: 'SQObjects.sqDim_parity_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SQObjects.sqDim_parity_ge

/-- info: 'SQObjects.parity_dSQ_ge_exp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SQObjects.parity_dSQ_ge_exp

-- FV-K (P-III stage 5b): the prequential-MDL-with-SQ-pruning ALGORITHM as a Finset object
-- (`ALT/SQAlgorithm.lean`), with the identification theorems tying the standing FV artifacts to it.
-- `alive_mass_eq_Z_det` — the unpruned Bayes-consistent mass IS FV-I's mixture `Z cands w (detFactor
-- pred)` (the "identify g with the algorithm" item). `truth_survives` — App-A Claim 1 for the object
-- (realizable + τ-close truth stays alive, reusing FV-A4's `truth_survives_pruning` at the 2τ rule).
-- `separated_impostor_pruned_alg` — the FV-A4 converse (a 3τ-separated candidate is pruned).
-- `algorithm_damage_le` — FV-H's `accumulated_perturbation_le` at the algorithm's OWN step families
-- (survivors `alive (t+1)` vs pruned-away `prunedAt t`), so `ε_t` is its literal pruned fraction.
-- `posterior_concentration_transfer` — the algorithm's Dirac pmf instantiates Paper II's
-- `deterministic_discovery`, giving unpruned posterior concentration (`≥ 1 − δ/2`).
/-- info: 'SQAlgorithm.alive_mass_eq_Z_det' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SQAlgorithm.alive_mass_eq_Z_det

/-- info: 'SQAlgorithm.truth_survives' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SQAlgorithm.truth_survives

/-- info: 'SQAlgorithm.separated_impostor_pruned_alg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SQAlgorithm.separated_impostor_pruned_alg

/-- info: 'SQAlgorithm.algorithm_damage_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SQAlgorithm.algorithm_damage_le

/-- info: 'SQAlgorithm.posterior_concentration_transfer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SQAlgorithm.posterior_concentration_transfer

-- FV-K hardening (P-III stage 5c-i): Theorem 4.1(i) assembled for the PRUNED algorithm via posterior
-- MONOTONICITY (not concentration∘damage). `posterior_mono_of_subset` — restricting a nonneg-weighted
-- posterior's normalizer to a subset containing the (positive-weight) truth dominates the full
-- quotient. `Lik_qDirac_eq_L_det` — the Dirac-pmf `Lik` IS FV-I's `L (detFactor pred)` (definitional).
-- `algorithm_discovery` — the pruned posterior on `iR` is `≥ 1 − δ/2`: `truth_survives` ⇒ `iR ∈
-- alive n ⊆ univ`, then monotonicity over `posterior_concentration_transfer`'s unpruned bound.
/-- info: 'SQAlgorithm.posterior_mono_of_subset' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SQAlgorithm.posterior_mono_of_subset

/-- info: 'SQAlgorithm.Lik_qDirac_eq_L_det' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SQAlgorithm.Lik_qDirac_eq_L_det

/-- info: 'SQAlgorithm.algorithm_discovery' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SQAlgorithm.algorithm_discovery

-- FV-L (P-III stage 6, final substantive target): the BFJKMR version-space envelope over FV-J's
-- GENUINE `sqDim`, via Szörényi's elementary maximality + packing (`ALT/SQEnvelope.lean`).
-- `close_on_of_prune` (App-A Prop-1 analogue) — survivors of the `2τ`-pruning rule are pairwise
-- `4τ`-close on the schedule (triangle inequality; the version space need NOT be pairwise separated).
-- `exists_sqNet` (Szörényi maximality) — every finite class has a MAXIMAL `τ`-separated subfamily
-- with `card = sqDim` that COVERS `M` (the "query schedule exists" residue FV-J/FV-K left open).
-- `subset_card_le_sqDim_of_ident` (the envelope) — under class-level identifiability at scale `2τ`,
-- the covering map is injective, so ANY subfamily (the version space) has `card ≤ sqDim M τ ans`.
-- `version_space_card_le` — the assembled App-A bound. `fvA4_envelope_discharged` — discharges FV-A4's
-- modeled premise `candidates ≤ A·d_SQ^m` with `A = m = 1`, the literal `PolyBounded` chain, closing
-- the residue with class-level identifiability replacing FV-J's survivor-set separation hypothesis.
/-- info: 'SQEnvelope.pairwise_close_on_of_oracle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SQEnvelope.pairwise_close_on_of_oracle

/-- info: 'SQEnvelope.close_on_of_prune' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SQEnvelope.close_on_of_prune

/-- info: 'SQEnvelope.exists_sqNet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SQEnvelope.exists_sqNet

/-- info: 'SQEnvelope.subset_card_le_sqDim_of_ident' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SQEnvelope.subset_card_le_sqDim_of_ident

/-- info: 'SQEnvelope.version_space_card_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SQEnvelope.version_space_card_le

/-- info: 'SQEnvelope.fvA4_envelope_discharged' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SQEnvelope.fvA4_envelope_discharged

-- Paper III §2 prefix-free Kolmogorov complexity `KP` is a SEMIMEASURE (FV-KP): the universal
-- a-priori / Solomonoff–Levin bound `∑ₓ 2⁻ᴷᴾ⁽ˣ⁾ ≤ 1` (`kraft_KP`, via Mathlib's Kraft route +
-- the injective least-index `K`), and the Paper II prior `w(R') = 2⁻ᴷᴾ⁽ᵉⁿᶜᵒᵈᵉ ᴿ'⁾` as a
-- semimeasure over any encodable rule class (`kraft_prior`).
/-- info: 'PrefixComplexity.kraft_KP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PrefixComplexity.kraft_KP

/-- info: 'PrefixComplexity.kraft_prior' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PrefixComplexity.kraft_prior

-- FV-KP (cont.): uncomputability of `KP` — the Kleene-`fixed_point₂` Berry argument (mirrors
-- `K_bitlen_not_computable`); a sanity follow-on to the semimeasure headline.
/-- info: 'PrefixComplexity.KP_not_computable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PrefixComplexity.KP_not_computable

-- Paper III Stage ① additive AST complexity `KE` (two-machine-invariance core, FV-KE): the additive
-- program-length laws the `encodeCode` index measure cannot give — subadditivity
-- `KE (Nat.pair x y) ≤ KE x + KE y + 3` (`KE_subadditive`), the composition bound (`KE_comp_le`),
-- and the time-bounded resource step `KE ≤ KE_t` (`KE_le_KE_t`, the Prop 2.2 scaffold).
/-- info: 'AdditiveComplexity.KE_subadditive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdditiveComplexity.KE_subadditive

/-- info: 'AdditiveComplexity.KE_comp_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdditiveComplexity.KE_comp_le

/-- info: 'AdditiveComplexity.KE_le_KE_t' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdditiveComplexity.KE_le_KE_t

-- Stage ② gate for Prop 2.2 / A2b (FV-KE cont.): the length-efficient binary constant `bconst`
-- correct (`eval_bconst`) with additive length `O(Nat.size n)` (`elen_bconst_le`) — the
-- `Θ(n)`-vs-`O(log)` fix over `Code.const`. `Classical.choice` is genuinely used (the doubling code
-- `dbl` is extracted from universality via `Classical.choose`).
/-- info: 'AdditiveComplexity.eval_bconst' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdditiveComplexity.eval_bconst

/-- info: 'AdditiveComplexity.elen_bconst_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdditiveComplexity.elen_bconst_le

-- FV-KE payoffs: Paper III Prop 2.2 `|P|`-component (`S_T ≤ r + O(log n)` via the binary `bconst`,
-- `prop_2_2_core`) and the multiplicative optimality / A2b model-bridge (`KE x ≤ elen d +
-- O(log p) + c`, `invariance_general`).
/-- info: 'AdditiveComplexity.prop_2_2_core' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdditiveComplexity.prop_2_2_core

/-- info: 'AdditiveComplexity.invariance_general' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdditiveComplexity.invariance_general

-- P-II item 2 (FV-AC ported to Paper II §1.1): two-machine invariance of the additive prior measure.
-- `KE_interp_le` — the ADDITIVE compose-method bound `KE (I⟦x⟧) ≤ KE x + elen I + 3` (the index
-- measure `KP` is walled by `encodeCode`'s quadratic pairing; the general-method case is the
-- κ-multiplicative `invariance_general` above). `prior_weight_machine_indep_compose` — §1.1's
-- machine-independence of the `2^{−KE}` prior weight up to a fixed `2^{−O(1)}` factor.
/-- info: 'PrefixInvariance.KE_interp_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PrefixInvariance.KE_interp_le

/-- info: 'PrefixInvariance.prior_weight_machine_indep_compose' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PrefixInvariance.prior_weight_machine_indep_compose

-- FV-AC hardening (P-III stage 5c-ii): the collector CONSTRUCTED (`ALT/Collector.lean`), so Prop
-- 2.2's "modeled premise" (an arbitrary `coll` assumed to halt) is DISCHARGED at the eval level.
-- `collector cR := prec zero (stepWrap cR)` is a fixed iterator template with the rule plugged in
-- (a rule-independent first-order collector cannot re-run `cR`); `orbitAcc_fst` certifies the
-- collected stream is the rule's orbit `rs^[t] 0`; `eval_collector`/`eval_assembly` prove the assembly
-- `collector cR ∘ (pair zero (bconst n))` computes the orbit prefix `orbitAcc rs n`; `elen_collector`
-- (`= elen cR + 60`, `Classical.choice`-free) shows the collector adds only a fixed constant, so
-- `prop_2_2_eval` gives `KE (orbitAcc rs n) ≤ elen cR + κ·Nat.size n + (84 + elen dbl)` = `r + O(log n)`
-- with the collector DISCHARGED. Target B (explicit `evaln` budget) is walled — `evaln`'s `k` caps
-- intermediate values, so `prop_2_2_t_exists` ships the honest ∃-budget form (via `evaln_complete`).
/-- info: 'AdditiveComplexity.orbitAcc_fst' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdditiveComplexity.orbitAcc_fst

/-- info: 'AdditiveComplexity.eval_collector' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdditiveComplexity.eval_collector

/-- info: 'AdditiveComplexity.eval_assembly' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdditiveComplexity.eval_assembly

/-- info: 'AdditiveComplexity.elen_collector' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdditiveComplexity.elen_collector

/-- info: 'AdditiveComplexity.elen_assembly' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdditiveComplexity.elen_assembly

/-- info: 'AdditiveComplexity.prop_2_2_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdditiveComplexity.prop_2_2_eval

/-- info: 'AdditiveComplexity.prop_2_2_t_exists' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdditiveComplexity.prop_2_2_t_exists

-- F20 Stage A — the native sequential-time cost (`ALT/TimeCost.lean`) and its collector payoff.
-- `eval_eq_val`: value-agreement — on the rfind'-free fragment the cost's value component IS `eval`,
-- so the cost carries NO value cap (the contrast with `evaln`). `tc_prec_le`: the generic engine — a
-- uniform per-step bound `B` gives `prec` a LINEAR, magnitude-independent step count. `prop_2_2_t_poly`
-- (in `Collector.lean`): the payoff — the collector's native cost on `Nat.pair a n` is `≤ (K+19)·n+19`,
-- with the explicit constant `C = 19`, NEVER referencing the super-exponential accumulator values.
-- This is the value-cap wall behind `prop_2_2_t_exists`'s ∃-budget discharged for the collector.
/-- info: 'TimeCost.eval_eq_val' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeCost.eval_eq_val

/-- info: 'TimeCost.tc_prec_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeCost.tc_prec_le

/-- info: 'AdditiveComplexity.prop_2_2_t_poly' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdditiveComplexity.prop_2_2_t_poly

-- F20 Stage C1 — the `PolyTime` predicate and its closure toolkit (`ALT/PolyTime.lean`), downstream
-- infra for bounding a concrete algorithm's native `tc`. `PolyTime` bundles an rfind'-free witness,
-- a poly-in-input-bit-length step count, and a poly output bit-length (the last clause is required for
-- composition to close). `polyTime_comp` — closure under composition (its proof genuinely consumes the
-- inner map's output-size clause, since the outer code's cost is measured against the inner OUTPUT
-- bit-length). `polyTime_prec` — the bounded-recursion / loop-cost closure via `tc_prec_le'`, with the
-- accumulator-poly and iteration-count premises explicit. `PolyTime` (a def) is even choice-free.
/-- info: 'TimeCost.PolyTime' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeCost.PolyTime

/-- info: 'TimeCost.polyTime_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeCost.polyTime_comp

/-- info: 'TimeCost.polyTime_prec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeCost.polyTime_prec

-- F20 Stage C1-validation — the `polyTime_prec` `hiter` blocker, the repaired loop closure, and a
-- fully-discharged worked example (`ALT/PolyTime.lean`). `unpair_snd_not_polyBounded` — a raw
-- second-projection slot is NOT poly-bounded in the input bit-length (exponential family
-- `⟨0, 2^j⟩`), so `polyTime_prec`'s `hiter` cannot be discharged for a genuine loop. `polyTime_loop`
-- — the usable bounded-recursion closure where the iteration COUNT is a poly-bit VALUE function of the
-- ACTUAL input (`hCval : PolyBounded count`), not a raw slot; realized as `comp (prec cf cg) shaper`
-- and bounded via `tc_prec_le'`. `polyTime_loop_worked_example` — a 3-iteration loop with a
-- genuinely non-constant per-step cost (nested inner loop over the index, so only `tc_prec_le'`
-- applies) and a scaling poly-bit accumulator, PolyTime with every premise discharged concretely.
/-- info: 'TimeCost.unpair_snd_not_polyBounded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeCost.unpair_snd_not_polyBounded

/-- info: 'TimeCost.polyTime_loop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeCost.polyTime_loop

/-- info: 'TimeCost.polyTime_loop_worked_example' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeCost.polyTime_loop_worked_example

-- F20 Stage C2a — the data layer for the 1-DL consistency solver (`ALT/DecisionListData.lean`).
-- `polyTime_readK`/`polyTime_readM` — the flat `#features`/`#examples` accessors (`left`,
-- `comp left right`) are `PolyTime` with `tc = O(1)`. `readM_le_size`/`readK_le_size` — THE
-- load-bearing size bound (I2): on a well-formed instance (`WF`: the stored counts are backed by
-- genuine length-`m`/length-`k` flag-cons lists) the counts are poly-bit VALUES,
-- `readM/readK inst ≤ Nat.size inst`, discharging `polyTime_loop`'s `hCval` for the solver's
-- scan/peel loops. Proof route: each flag-cons cell strictly grows `Nat.size` (`size_cons_gt`), so
-- a length-`m` list has `Nat.size ≥ m` (`isList_len_le_size`), and the list is a sub-term of `inst`.
/-- info: 'OneDL.polyTime_readK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OneDL.polyTime_readK

/-- info: 'OneDL.polyTime_readM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OneDL.polyTime_readM

/-- info: 'OneDL.readM_le_size' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OneDL.readM_le_size

/-- info: 'OneDL.readK_le_size' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OneDL.readK_le_size

-- F20 Stage C2a-part-2 — the decode-cost verdict, the flag-cons pivot, and the indexed accessors.
-- `cPred_tc_not_polyBounded` — the smallest rfind'-free predecessor is value-linear (`n ≤ tc cPred n`),
-- NOT poly-bounded, so an offset-cons (predecessor-based) decode fails; hence the flag-cons pivot
-- (`cons e r = Nat.pair 1 (Nat.pair e r)`, decoded by pure `unpair`, `tc = O(1)`). `polyTime_peel` —
-- the peel loop `n ↦ peel (A n) (C n)` is `PolyTime` given a poly-bit index `C` (a `polyTime_loop`
-- instance: `hCval` from `C`, `hacc` from the suffix `≤ A n`, constant step cost via `tc_prec_le'`).
-- `polyTime_getExample` — the `i`-th example accessor, `headL ∘ peel`. `getExample_encode` — List-model
-- correctness: `headL (peel (encodeList xs) i) = xs[i]` (via `peel`-is-`drop`).
/-- info: 'OneDL.cPred_tc_not_polyBounded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OneDL.cPred_tc_not_polyBounded

/-- info: 'OneDL.polyTime_peel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OneDL.polyTime_peel

/-- info: 'OneDL.polyTime_getExample' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OneDL.polyTime_getExample

/-- info: 'OneDL.getExample_encode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OneDL.getExample_encode

-- F20 Stage C2b — the inner scan primitives of the greedy 1-DL consistency solver
-- (`ALT/DecisionListSolver.lean`). THE FINDING: the native `tc` makes value-arithmetic (general `=`,
-- `isZero`, `add`) value-linear, so the scan must use a BIT-LOGIC gate library (binary features/labels)
-- and avoid label equality (track `sawZero`/`sawOne` bits instead). `val_cAnd`/`val_cEqBit` — the gate
-- semantics; each gate is bit-closed and `O(1)`-`tc` on bits. `val_cPurity` — the purity primitive `val`
-- law (loop = iterated carried-suffix step). `purity_correct` — the scan realises the covered-label
-- fold over `zip msks exs`. `purity_isPure_iff`/`purity_commonLabel`/`purity_sawAny` — the 3-field
-- verdict `⟨isPure, ⟨commonLabel, sawAny⟩⟩` reads out as "isPure iff not both a covered 0-label and
-- covered 1-label", "commonLabel = sawOne", and "sawAny ≠ 0 iff the literal covers ≥1 remaining
-- example" (the covering bit that stops a vacuous pure literal stalling greedy — the C2b-outer fix).
-- `polyTime_cScan` — the scan loop is `PolyTime` via `polyTime_loop`: `rfind'`-freeness, the shaper
-- `PolyTime`s, the base cost, and the accumulator-size bound (`polyBounded_acc`) are all discharged;
-- the WF/bit residuals (count poly-bit `hCval` from `readM_le_size`; the per-visited-step cost bound)
-- are threaded as premises exactly as `polyTime_peel` threads its index bound.
/-- info: 'OneDL.val_cAnd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OneDL.val_cAnd

/-- info: 'OneDL.val_cEqBit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OneDL.val_cEqBit

/-- info: 'OneDL.val_cPurity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OneDL.val_cPurity

/-- info: 'OneDL.purity_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OneDL.purity_correct

/-- info: 'OneDL.purity_isPure_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OneDL.purity_isPure_iff

/-- info: 'OneDL.polyTime_cScan' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OneDL.polyTime_cScan

-- F20 Stage C2b-part-1b — the per-step cost bound is discharged, so purity is a self-contained
-- `PolyTime` on an honest well-formed domain. `WFBits inst` — the binary well-formedness (WF plus every
-- feature bit and label `≤ 1`); `MaskValid mask m` — the working set is a length-`m` flag-cons list of
-- bits. `visited_bits` — over the visited states `i < readM inst`, the three operands the step reads
-- (mask head, feature at `j`, label) are all `≤ 1` (features/labels from `WFBits`, mask bit from
-- `MaskValid`, the `sawZero`/`sawOne` accumulators from the flag invariants), so `tc cStep ≤ 16·jOf n +
-- 5700`. `polyTime_purity` — packaged as `PolyTimeOn PurityWF purityVal`: the raw `(Bstep+1)·m` cost is
-- poly-bit via `jOf n ≤ readK ≤ size n` and `readM ≤ size n`, and the verdict is three bits. The ONLY
-- residual hypotheses are the WF-conditional ones (the `PurityWF` domain); no `PolyBounded` premises.
/-- info: 'OneDL.polyTime_purity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OneDL.polyTime_purity

-- F20 Stage C2b-outer — the greedy outer loop `solve` (`readM inst` rounds of covering-pure-literal
-- selection + mask refinement, output built by prepend then one final `cReverse`). `polyTime_solve` —
-- packaged as `PolyTimeOn SolveWF solveVal`: `O(m²·k²)` native cost (`k` rounds × one `findLit` `O(m·k²)`
-- + one `maskUpdate` `O(m·k)`), and — the crux — the exponential flag-cons OUTPUT stays poly-bit because
-- the instance already pays (exponentially) for its `m` examples: `two_pow_readM_le` gives
-- `2^(readM) ≤ size n + 1`, so `svCnt ≤ readM` rules cost `≤ (size n+1)²·O(size n)` bits (cubic).
-- `maskValid_solve` — the working mask stays a valid length-`m` bit-list every round (`maskValid_svAcc`
-- invariant); `dlModel_svAcc` — the output `svDL` is the flag-`cons` encoding of a genuine `List` of
-- `svCnt` rule-triples (the `List` model that lets `cReverse`/`size_encodeList_le` bound the output).
-- C2c owns greedy CORRECTNESS (finalMask all-zero iff a consistent 1-DL exists).
/-- info: 'OneDL.polyTime_solve' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OneDL.polyTime_solve

/-- info: 'OneDL.maskValid_solve' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OneDL.maskValid_solve

/-- info: 'OneDL.findLit_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OneDL.findLit_sound

-- C2c — greedy CORRECTNESS. `progress` (Engine Lemma 1: a consistent 1-DL forces a covering-pure literal
-- while any example is active — default-monochromatic vs first-firing-rule cases); `output_consistent`
-- (Engine Lemma 2: an emptied mask means the emitted forward DL is consistent for ALL examples); and the
-- capstone `solve_decides` — finalMask all-zero **iff** a consistent 1-DL over valid literals exists (⇐ by
-- the `activeCount` monovariant, ⇒ by Engine Lemma 2).
/-- info: 'OneDL.progress' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OneDL.progress

/-- info: 'OneDL.output_consistent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OneDL.output_consistent

/-- info: 'OneDL.solve_decides' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OneDL.solve_decides

/-! ## Guard-gap closure — modules predating the `#guard_msgs` discipline

The capstones below (each module docstring's "What this DOES establish" list) were built before the
audit-umbrella discipline and carried no guard; added here for uniform coverage at the same bar.
Grouped by paper. `ProofChainSkeleton`'s pure-propositional chain depends on NO axioms — a strict
subset the guard pins verbatim. -/

-- Paper I §4 CCC stand-in for Rep(S) (`ALT/CartesianClosed.lean`, namespace `RepSCCC`): Prop 4.3
-- Cartesian-closedness (`repS_cartesianClosed`), the §4.3 evaluation/currying universal property
-- (`expCurrying`), §4.5 functions-as-data (`functionsAsData`), and the §4.4 finite-exponential
-- miniature (`exp_finite`).
/-- info: 'RepSCCC.repS_cartesianClosed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RepSCCC.repS_cartesianClosed

/-- info: 'RepSCCC.expCurrying' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RepSCCC.expCurrying

/-- info: 'RepSCCC.functionsAsData' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RepSCCC.functionsAsData

/-- info: 'RepSCCC.exp_finite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RepSCCC.exp_finite

-- Paper I §5.3/§6 Gödel threshold (`ALT/GodelThreshold.lean`), tied to D1's `ParamNNO`: the
-- Theorem 6.2 form — depth `> g(T_S)` under incompleteness ⟹ represents-an-underivable-truth. Pure
-- threshold logic, so it is `Classical.choice`-free (`[propext, Quot.sound]`, a strict subset).
/-- info: 'GodelThreshold.reflective_of_depth' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GodelThreshold.reflective_of_depth

-- Paper II §1.2 regime consistency (`ALT/RegimeConsistency.lean`): the strict ordering `r<K<L`
-- under C1–C3 (`regime_strict_ordering`) and its non-vacuity witness (`regime_satisfiable`).
/-- info: 'RegimeConsistency.regime_strict_ordering' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RegimeConsistency.regime_strict_ordering

/-- info: 'RegimeConsistency.regime_satisfiable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RegimeConsistency.regime_satisfiable

-- Paper II Cor 2.2 capacity threshold (`ALT/CapacityThreshold.lean`): in the regime, C1 entails
-- representability of the rule-based encoding (`representable_of_C1`).
/-- info: 'CapacityThreshold.representable_of_C1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CapacityThreshold.representable_of_C1

-- Paper II Thm 2.1 static MDL dominance (`ALT/MDLDominance.lean`): the exact §2.2 Step-3 gap
-- identity (`dominance_gap_eq`) and strict dominance in the regime (`mdl_dominance`).
/-- info: 'MDLDominance.dominance_gap_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MDLDominance.dominance_gap_eq

/-- info: 'MDLDominance.mdl_dominance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MDLDominance.mdl_dominance

-- Paper II §4.4 retention overhead (`ALT/RetentionOverhead.lean`): the eq.(4) decomposition
-- (`overhead_eq`) and the `O(r·log(r/δ))` explicit-constant bound (`overhead_bigO`).
/-- info: 'RetentionOverhead.overhead_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RetentionOverhead.overhead_eq

/-- info: 'RetentionOverhead.overhead_bigO' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RetentionOverhead.overhead_bigO

-- Paper II §1.1 universal-prior sub-normalization (`ALT/PriorNormalization.lean`): binary
-- Kraft–McMillan (`prior_finset_sum_le_one`) and its countable extension — the `∝ 2^{−K}` prior is a
-- semimeasure (`prior_tsum_le_one`).
/-- info: 'PriorNormalization.prior_finset_sum_le_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PriorNormalization.prior_finset_sum_le_one

/-- info: 'PriorNormalization.prior_tsum_le_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PriorNormalization.prior_tsum_le_one

-- Paper II §3.3 explicit ε₀ lower bound (`ALT/EpsilonZeroBound.lean`): positivity (`eps0_pos`),
-- the `γ`-separated demotion `ε₀ ≥ γ` (`eps0_ge_of_separated`), and the conditional polynomial
-- discovery-time bound (`Tdiscover_le_of_separated`).
/-- info: 'EpsilonZeroBound.eps0_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EpsilonZeroBound.eps0_pos

/-- info: 'EpsilonZeroBound.eps0_ge_of_separated' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EpsilonZeroBound.eps0_ge_of_separated

/-- info: 'EpsilonZeroBound.Tdiscover_le_of_separated' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EpsilonZeroBound.Tdiscover_le_of_separated

-- B1a/B1b pressure window (conjectural framing) (`ALT/PressureWindow.lean`): the retention break-even
-- (`breakeven`), the window-as-interval-in-Π reparametrization (`regimeBand_iff_pi_mem`), and the S2
-- dynamical-window capstone (`dynamical_window`).
/-- info: 'PressureWindow.breakeven' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PressureWindow.breakeven

/-- info: 'PressureWindow.regimeBand_iff_pi_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PressureWindow.regimeBand_iff_pi_mem

/-- info: 'PressureWindow.dynamical_window' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PressureWindow.dynamical_window

-- Paper II exact-gap retention break-even (`ALT/ExactBreakeven.lean`): the exact dominance gap is
-- strictly positive in the regime (`domGap_pos`) and B1a's break-even at the exact endpoints
-- (`breakeven_exact`).
/-- info: 'ExactBreakeven.domGap_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ExactBreakeven.domGap_pos

/-- info: 'ExactBreakeven.breakeven_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ExactBreakeven.breakeven_exact

-- Paper II K-reconnection (`ALT/KReconnection.lean`): the five load-bearing MDL-corpus theorems
-- re-stated at the genuine `r = K(R)` (bit-length Kolmogorov complexity of the rule `R`).
/-- info: 'KReconnection.representable_of_C1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KReconnection.representable_of_C1

/-- info: 'KReconnection.mdl_dominance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KReconnection.mdl_dominance

/-- info: 'KReconnection.regime_strict_ordering' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KReconnection.regime_strict_ordering

/-- info: 'KReconnection.overhead_bigO' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KReconnection.overhead_bigO

/-- info: 'KReconnection.polytime_accounting' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KReconnection.polytime_accounting

-- Paper II/III base Kolmogorov complexity (`ALT/KolmogorovComplexity.lean`): unboundedness of `K`
-- (`K_unbounded`) and the headline uncomputability of `K` (`K_not_computable`).
/-- info: 'KolmogorovComplexity.K_unbounded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KolmogorovComplexity.K_unbounded

/-- info: 'KolmogorovComplexity.K_not_computable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KolmogorovComplexity.K_not_computable

-- Paper III bit-length Kolmogorov complexity (`ALT/KolmogorovBitlen.lean`, namespace
-- `KolmogorovComplexity`): uncomputability of the paper's `r`-in-bits (`K_bitlen_not_computable`).
/-- info: 'KolmogorovComplexity.K_bitlen_not_computable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KolmogorovComplexity.K_bitlen_not_computable

-- Paper IV proof-chain skeleton (`ALT/ProofChainSkeleton.lean`): the §6 assembly is logically
-- connected with no missing link (`inevitability_full`) and bare representational reflection sits off
-- the tractability/retention path (`reflective_core`). Pure propositional logic — NO axioms.
/-- info: 'ProofChainSkeleton.inevitability_full' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms ProofChainSkeleton.inevitability_full

/-- info: 'ProofChainSkeleton.reflective_core' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms ProofChainSkeleton.reflective_core

-- Paper II §2.3 — Kolmogorov structure function, the 45° / geometric lower bound (FV-14, P-II item 3
-- slice one) on the additive carrier. Two-part description (per model) `KE_le_of_model`; the four
-- targets: antitone `structFn_antitone`, singleton collapse `structFn_singleton`, the 45° slice
-- `KE_le_structFn` (`KE x ≤ α + c₁·h_x(α) + c₂`, `c₁ = 15 + elen dbl`), and the lower-bound form
-- `structFn_ge`. `Classical.choice` is genuinely used (`extractor`/`mkSingleton` from universality).
/-- info: 'StructureFunction.KE_le_of_model' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StructureFunction.KE_le_of_model

/-- info: 'StructureFunction.structFn_antitone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StructureFunction.structFn_antitone

/-- info: 'StructureFunction.structFn_singleton' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StructureFunction.structFn_singleton

/-- info: 'StructureFunction.KE_le_structFn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StructureFunction.KE_le_structFn

/-- info: 'StructureFunction.structFn_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StructureFunction.structFn_ge
