/-
Copyright (c) 2026 Mykola Palamarchuk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mykola Palamarchuk
-/
import ALT.Decoupling
import ALT.PersistenceCapacity
import ALT.DecoupledSimulation
import ALT.ParameterizedNNO
import ALT.GodelInternalization
import ALT.RepFintype
import ALT.RecursorAlgebra
import ALT.Realizability
import ALT.RealizabilityCCC
import ALT.RealizabilityRecursor
import ALT.RealizabilityCoproduct
import ALT.RealizabilitySubobject
import ALT.CapacityLayer
import ALT.RealizerLength
import ALT.CategoricalThreshold
import ALT.ReflectiveAutomaton
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
import ALT.CommitmentSeam
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
import ALT.SearchCost
import ALT.SearchSpace
import ALT.TimeCost
import ALT.PolyTime
import ALT.CheckerScratch
import ALT.CapacityBoundedEval
import ALT.BoundedInterp
import ALT.CodePacking
import ALT.UniversalAt
import ALT.GradeTransport
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
import ALT.ExcessOrder

-- Formal-check file, not Mathlib-destined: opt out of the house-style linters.
set_option linter.style.header false
set_option linter.style.longLine false

/-!
# Axiom audit (Mathlib side) — machine-ENFORCED axiom-cleanliness ([Decoupling], [Discovery], [SQ])

Companion to `ALT/AxiomAuditFoundation.lean` for the umbrella-Mathlib–side theorems (the
Foundation/Mathlib import divide forbids one file importing both). Each `#guard_msgs in
#print axioms …` **fails `lake build`** if the theorem's axiom set drifts. The Decoupling core is
even `Classical.choice`-free (`[propext, Quot.sound]`), and the necessity counterexample is fully
constructive (`[propext]`).

Coverage spans all three Mathlib-side papers: **[Decoupling]** (decoupling, bounded recursor, realizability
CCC, categorical threshold), **[Discovery]** (MDL coding/dominance, Cheng-CCC necessity, finite
info-theory, Grünwald–Mehta / deterministic / countable discovery, retention), and **[SQ]**
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

/-- info: 'Decoupling.total_overwrite_exclusion' depends on axioms: [Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Decoupling.total_overwrite_exclusion

-- §3 Corollary 3.3 (the decoupling dichotomy) and §3 Proposition 3.4 (the relativized equivalence
-- on an update-closed state set Ω) — both derived from the choice-free Decoupling core.
/-- info: 'Decoupling.decoupling_dichotomy' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Decoupling.decoupling_dichotomy

/-- info: 'Decoupling.decoupling_iff_persists_on' depends on axioms: [Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Decoupling.decoupling_iff_persists_on

-- §3.5 robustness of the exclusion (FV-22): moving decoders and the price of a frame. The update
-- restricts to a bijection on the recurrent core; the core is the exact ceiling on what ANY
-- time-dependent lens family can carry (Proposition 3.5, both halves); the static capacity of
-- Corollary 3.3 sits below it, with rotate-left the total-gap witness; a maximal family's first two
-- frames determine the world's recurrent rule; and eventual persistence relocates the read-only
-- requirement to the ω-limit set rather than removing it. The finite-image machinery (`Set.ncard`,
-- `Nat.card`, `Function.invFunOn`) is classical, so these carry the full standard axiom set.
/-- info: 'PersistenceCapacity.core_bijOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PersistenceCapacity.core_bijOn

/-- info: 'PersistenceCapacity.capacity_horizon_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PersistenceCapacity.capacity_horizon_le

/-- info: 'PersistenceCapacity.capacity_horizon_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PersistenceCapacity.capacity_horizon_ge

/-- info: 'PersistenceCapacity.capacity_core' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PersistenceCapacity.capacity_core

/-- info: 'PersistenceCapacity.capacity_core_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PersistenceCapacity.capacity_core_iff

/-- info: 'PersistenceCapacity.static_le_moving' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PersistenceCapacity.static_le_moving

/-- info: 'PersistenceCapacity.rotate_gap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PersistenceCapacity.rotate_gap

/-- info: 'PersistenceCapacity.lens_bijOn_core' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PersistenceCapacity.lens_bijOn_core

/-- info: 'PersistenceCapacity.ledger' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PersistenceCapacity.ledger

/-- info: 'PersistenceCapacity.ledger_determines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PersistenceCapacity.ledger_determines

-- The ledger in complexity form: the world's recurrent rule, tabulated on the core, is recovered
-- from the observer's first two frames by ONE fixed program, so its additive Kolmogorov complexity
-- is bounded by theirs plus a constant independent of the world, the lens, the enumerations and the
-- memory size.
/-- info: 'PersistenceCapacity.ledger_K' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PersistenceCapacity.ledger_K

-- §3.5, the two relaxations. Eventual persistence: majority-vote write-back on three copies
-- overwrites every cell (no static model) yet repairs itself — the recurrent core is exactly the
-- consensus set and one bit persists. Descent: a decoded model obeys a law of its own iff the
-- lens's fibres are update-invariant (the substitution property of Hartmanis–Stearns 1966), of
-- which the Decoupling Lemma is the identity-law case — and that identification, being pure
-- shared-memory algebra, needs no axioms at all.
/-- info: 'PersistenceCapacity.majority_selfRepair' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PersistenceCapacity.majority_selfRepair

/-- info: 'PersistenceCapacity.descent_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PersistenceCapacity.descent_iff

/-- info: 'PersistenceCapacity.decoupling_is_identity_law' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms PersistenceCapacity.decoupling_is_identity_law

/-- info: 'PersistenceCapacity.eventual_decoupling_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PersistenceCapacity.eventual_decoupling_iff

-- The serialization of a program is a prefix code: it parses uniquely, so distinct programs have
-- distinct bit-strings. Pure structural induction on the AST — no choice, and no `Quot.sound`.
/-- info: 'AdditiveComplexity.E_injective' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms AdditiveComplexity.E_injective

-- Prefix codes are uniquely decodable, so McMillan's counting argument prices the program
-- lengths: the weights `2 ^ (-elen c)` sum to at most one over ALL programs at once.
/-- info: 'AdditiveComplexity.kraft_KP_E' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdditiveComplexity.kraft_KP_E

-- The supply side of the incompressibility method: a budget of `L` bits describes at most
-- `2 ^ (L + 1)` naturals, because distinct values need distinct shortest programs and there are
-- fewer than `2 ^ (L + 1)` bit-strings of length at most `L`. Choosing a shortest program per value
-- is the classical step.
/-- info: 'AdditiveComplexity.card_KE_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdditiveComplexity.card_KE_le

-- [Persistence] §4, the static stratum. A lens with `ℓ ∘ U = ℓ` is exactly a function constant on
-- the components of the transition graph — an equivalence between a dynamical condition and a
-- combinatorial one, proved by induction over the generated equivalence, hence axiom-free. The
-- hierarchy then places the components: read-only cells ≤ components ≤ recurrent core.
/-- info: 'PersistenceCapacity.staticLens_factors' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms PersistenceCapacity.staticLens_factors

/-- info: 'PersistenceCapacity.hierarchy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PersistenceCapacity.hierarchy

-- [Persistence] §5, the budgeted capacity `C_b`: the largest model carried by a family whose every
-- frame's core table costs at most `b` bits. It is capped by the recurrent core at every budget and
-- reaches the static levels of §4 at a finite one — the sandwich.
/-- info: 'PersistenceCapacity.Cb_le_core' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PersistenceCapacity.Cb_le_core

/-- info: 'PersistenceCapacity.capacity_sandwich' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PersistenceCapacity.capacity_sandwich

-- [Persistence] §7, the fiber-uniform counting over the symmetric group. Permutations act on lenses
-- by relabelling; the stabilizer of a lens is the product of the symmetric groups of its fibers, so
-- its orbit — exactly the lenses with its fiber sizes — has `n ! / ∏ᵢ (fiberᵢ) !` elements, and the
-- balanced count is `N_bal = n ! / ((n / m) !) ^ m`.
/-- info: 'PersistenceCapacity.card_stabilizer_lens' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PersistenceCapacity.card_stabilizer_lens

/-- info: 'PersistenceCapacity.mem_orbit_lens_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PersistenceCapacity.mem_orbit_lens_iff

/-- info: 'PersistenceCapacity.card_balancedLenses' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PersistenceCapacity.card_balancedLenses

-- [Persistence] §7, the collapse. A budget of `b` bits describes at most `2 ^ (b + 1)` frames, each
-- pulled back to one coset of the stabilizer, so at most `2 ^ (b + 1) · ∏ᵢ (fiberᵢ) !` worlds have
-- an affordable relabelled frame; and the ledger forces the second frame of ANY family carrying the
-- model to be exactly that relabelling. Hence all but a `2 ^ (b + 1) / N_bal` fraction of worlds
-- admit no affordable moving decoder at all.
/-- info: 'PersistenceCapacity.collapse_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PersistenceCapacity.collapse_count

/-- info: 'PersistenceCapacity.collapse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PersistenceCapacity.collapse

/-- info: 'PersistenceCapacity.collapse_balanced' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PersistenceCapacity.collapse_balanced

/-- info: 'PersistenceCapacity.collapse_generic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PersistenceCapacity.collapse_generic

-- [Persistence] §7, Corollary 7.4 (the Kraft union, logs cleared): summing the per-frame count
-- (`collapse_union_frame`, division-free via `collapse_fraction` + `Nat.log`) over ALL reference
-- frames at once. Sound across lenses of different label counts because `lensCode` is jointly
-- injective on surjective lenses (`lensCode_codomain_of_surjective`), so the Kraft inequality bounds
-- the whole sum — generically an observer's two-frame budget must cover its carried entropy.
/-- info: 'PersistenceCapacity.lensCode_codomain_of_surjective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PersistenceCapacity.lensCode_codomain_of_surjective

/-- info: 'PersistenceCapacity.collapse_union_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PersistenceCapacity.collapse_union_frame

/-- info: 'PersistenceCapacity.collapse_union' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PersistenceCapacity.collapse_union

-- [Persistence] §5, Definition 5.4 + §7, Corollary 7.5(i) (the cap): the entropic capacity `CbH`,
-- valued in the reference frame's relabelling-class size `2 ^ E` (the `log₂` is paper-side, as with
-- `Cb`), is generically pinned at `2b + d + 2` bits — the Kraft union `collapse_union` applied to a
-- family realizing the attained supremum. An observer keeps, to within a factor two, exactly the
-- entropy it pays for.
/-- info: 'PersistenceCapacity.CbH_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PersistenceCapacity.CbH_mono

/-- info: 'PersistenceCapacity.CbH_le_factorial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PersistenceCapacity.CbH_le_factorial

/-- info: 'PersistenceCapacity.CbH_collapse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PersistenceCapacity.CbH_collapse

-- [Persistence] §5, Proposition 5.3 (the combinatorial half) + §7, Corollary 7.5(i) (the floor):
-- `r` marks riding the world carry entropy `log₂ (n ! / (n − r)!)` over EVERY permutation world.
-- `smul_markingLens` is the structural step — each frame is itself a marking lens, so Proposition
-- 5.3's per-frame price is one bound uniform over the marks, which `CbH_ge_marking` consumes as a
-- named hypothesis (the explicit-code discharge is not part of this bundle).
/-- info: 'PersistenceCapacity.smul_markingLens' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PersistenceCapacity.smul_markingLens

/-- info: 'PersistenceCapacity.markCarries' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PersistenceCapacity.markCarries

/-- info: 'PersistenceCapacity.prod_fiber_marking' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PersistenceCapacity.prod_fiber_marking

/-- info: 'PersistenceCapacity.CbH_ge_marking' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PersistenceCapacity.CbH_ge_marking

-- Proposition 5.3's price, discharged as an explicit code: the marking lens's tabulation is loaded
-- by ONE fixed builder from a base-`n` numeral of the marks, at `O ((r + 1) · log₂ n)` bits,
-- uniformly over where the marks sit (`KE_markingLens_le`) — and the floor that consumes it, with
-- no named price left (`CbH_ge_marking'`).

/-- info: 'PersistenceCapacity.KE_markingLens_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PersistenceCapacity.KE_markingLens_le

/-- info: 'PersistenceCapacity.CbH_ge_marking'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PersistenceCapacity.CbH_ge_marking'

-- Renting versus owning a reading. The uniform budget of Definition 5.1's uniform variant — one
-- program computing every frame — with the frame-cost reduction that prices frame `t` at
-- `b + O (log t)` (`uniformBudget_frame_cost`), the uniform entropic capacity `CbHu`, and its
-- collapse cap. The cap is horizon-free: the collapse reads frames 0 and 1 only, whose clock inputs
-- are constants, so the reduction's `O (log t)` never grows (`CbHu_collapse`).

/-- info: 'PersistenceCapacity.uniformBudget_frame_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PersistenceCapacity.uniformBudget_frame_cost

/-- info: 'PersistenceCapacity.CbHu_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PersistenceCapacity.CbHu_mono

/-- info: 'PersistenceCapacity.CbHu_le_factorial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PersistenceCapacity.CbHu_le_factorial

/-- info: 'PersistenceCapacity.CbHu_collapse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PersistenceCapacity.CbHu_collapse

-- The ownership construction (Proposition 8.1's form in the permutation setting): table transport
-- along the world's own table, iterated by a fixed builder, turning codes for the reading's and the
-- world's tables into a uniform budget for the canonical family.

/-- info: 'PersistenceCapacity.permCarries_smul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PersistenceCapacity.permCarries_smul

/-- info: 'PersistenceCapacity.ownIter_lensTable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PersistenceCapacity.ownIter_lensTable

/-- info: 'PersistenceCapacity.ownership' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PersistenceCapacity.ownership

-- The multiplicative congruential world `x ↦ a · x mod m` — the division-remainder pseudo-random
-- generator — as an explicit cheap-dynamics instance: priced at `O (log m)` bits by the builder
-- idiom (`KE_lcgWorld_le`), and the reading owned over it forever (`CbHu_ge_lcg`).

/-- info: 'PersistenceCapacity.KE_lcgWorld_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PersistenceCapacity.KE_lcgWorld_le

/-- info: 'PersistenceCapacity.CbHu_ge_lcg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PersistenceCapacity.CbHu_ge_lcg

-- Faithful self-reading, priced in both directions. Owning a bijective reading costs a code for the
-- world's table and an absolute constant (`faithful_ownership`, the identity frame rebuilt free from
-- the world's table by `faithTableFn`); conversely any owned faithful family hands the world's rule
-- back at twice its budget (`faithful_rule_cost`, over the ledger's inverter `invcomp_permFrames`).
-- The capstone is the equality: where the rule is affordable, the uniform capacity is exactly `n !`.

/-- info: 'PersistenceCapacity.faithTableFn_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PersistenceCapacity.faithTableFn_eq

/-- info: 'PersistenceCapacity.faithful_ownership' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PersistenceCapacity.faithful_ownership

/-- info: 'PersistenceCapacity.invcomp_permFrames' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PersistenceCapacity.invcomp_permFrames

/-- info: 'PersistenceCapacity.faithful_rule_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PersistenceCapacity.faithful_rule_cost

/-- info: 'PersistenceCapacity.prod_fiber_bijective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PersistenceCapacity.prod_fiber_bijective

/-- info: 'PersistenceCapacity.CbHu_attains_ceiling' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PersistenceCapacity.CbHu_attains_ceiling

-- Capacity out to a horizon: the capacities of Definitions 5.4 and 5.5 with the persistence identity
-- and the budget demanded only up to `T`. The collapse's cap is unchanged at every `T ≥ 1` (it reads
-- frames 0 and 1 only), and the horizon is what makes the uniform→per-frame comparison true at all —
-- the clock costs `O (log T)`, so the horizon-free form of that comparison does not hold.

/-- info: 'PersistenceCapacity.permCarriesUpTo_frame_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PersistenceCapacity.permCarriesUpTo_frame_one

/-- info: 'PersistenceCapacity.CbH_upTo_antitone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PersistenceCapacity.CbH_upTo_antitone

/-- info: 'PersistenceCapacity.CbH_le_CbH_upTo' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PersistenceCapacity.CbH_le_CbH_upTo

/-- info: 'PersistenceCapacity.CbH_upTo_collapse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PersistenceCapacity.CbH_upTo_collapse

/-- info: 'PersistenceCapacity.uniformBudgetUpTo_frame_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PersistenceCapacity.uniformBudgetUpTo_frame_cost

/-- info: 'PersistenceCapacity.CbHu_upTo_le_CbH_upTo' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PersistenceCapacity.CbHu_upTo_le_CbH_upTo

-- A carried family over a permutation world is determined by its reference frame and repeats with
-- the world's period, so an owner's clock never counts past `orderOf U ≤ n !` — and the uniform to
-- per-frame comparison holds with no horizon at all, at cost `O (log n !)` (`CbHu_le_CbH`).

-- Choice-free: solving the persistence identity for `ℓ t` is pure rewriting.
/-- info: 'PersistenceCapacity.permCarries_frame_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PersistenceCapacity.permCarries_frame_eq

/-- info: 'PersistenceCapacity.permCarries_frame_mod' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PersistenceCapacity.permCarries_frame_mod

/-- info: 'PersistenceCapacity.CbHu_le_CbH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PersistenceCapacity.CbHu_le_CbH

-- Product worlds: the disjoint union of two worlds, whose block action needs the two evaluation
-- lemmas (the transport along `finSumFinEquiv` does not compute). Rules compose, so the cheap
-- dynamics regime is closed under disjoint union (`KE_unionWorld_le`); and capacities are
-- superadditive (`CbHu_unionWorld_ge`), the merged fibre profile of the block-pair lens carrying
-- the orbit arithmetic. A union world is structured by construction — the generic caps do not
-- speak about it.

/-- info: 'PersistenceCapacity.unionWorld_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PersistenceCapacity.unionWorld_left

/-- info: 'PersistenceCapacity.unionWorld_right' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PersistenceCapacity.unionWorld_right

/-- info: 'PersistenceCapacity.lensTable_unionWorld' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PersistenceCapacity.lensTable_unionWorld

/-- info: 'PersistenceCapacity.unionTableFn_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PersistenceCapacity.unionTableFn_eq

/-- info: 'PersistenceCapacity.KE_unionWorld_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PersistenceCapacity.KE_unionWorld_le

/-- info: 'PersistenceCapacity.permCarries_unionLens' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PersistenceCapacity.permCarries_unionLens

/-- info: 'PersistenceCapacity.uniformBudget_unionLens' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PersistenceCapacity.uniformBudget_unionLens

/-- info: 'PersistenceCapacity.prod_fiber_unionLens' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PersistenceCapacity.prod_fiber_unionLens

/-- info: 'PersistenceCapacity.CbHu_unionWorld_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PersistenceCapacity.CbHu_unionWorld_ge

-- Cartesian product worlds: two worlds turning at once on pairs of states, the `Fin (n₁ * n₂)`
-- instance transported along `finProdFinEquiv` (so its coordinate action, like the union's, needs
-- an evaluation lemma). Rules compose with NO size parameter at all — each table is as long as its
-- own state space (`KE_prodWorldFin_le`). A reading of one factor lifts through the projection,
-- keeping both its persistence and its intertwining square — the square lift is axiom-free, the
-- product's first coordinate evolving by `U₁` and by nothing else. Conversely a FAITHFUL reading of
-- the whole product hands back each factor's rule at twice the budget (`KE_factorFst_le_of_faithful`
-- / `KE_factorSnd_le_of_faithful`): the contrast between a cheap sub-system and an unaffordable
-- whole. Capacity projects through the lift by equivariance (`CbHu_prodWorldFin_ge_fst`).

/-- info: 'PersistenceCapacity.prodWorld_iterate' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms PersistenceCapacity.prodWorld_iterate

/-- info: 'PersistenceCapacity.prodWorldFin_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PersistenceCapacity.prodWorldFin_apply

/-- info: 'PersistenceCapacity.prodWorldFin_pow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PersistenceCapacity.prodWorldFin_pow

/-- info: 'PersistenceCapacity.lensTable_prodWorldFin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PersistenceCapacity.lensTable_prodWorldFin

/-- info: 'PersistenceCapacity.prodTableFn_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PersistenceCapacity.prodTableFn_eq

/-- info: 'PersistenceCapacity.KE_prodWorldFin_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PersistenceCapacity.KE_prodWorldFin_le

/-- info: 'PersistenceCapacity.carries_prodLensFst' depends on axioms: [propext, Classical.choice] -/
#guard_msgs (whitespace := lax) in
#print axioms PersistenceCapacity.carries_prodLensFst

/-- info: 'PersistenceCapacity.intertwines_prodLensFst' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms PersistenceCapacity.intertwines_prodLensFst

/-- info: 'PersistenceCapacity.permCarries_prodLensFinFst' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PersistenceCapacity.permCarries_prodLensFinFst

/-- info: 'PersistenceCapacity.uniformBudget_prodLensFinFst' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PersistenceCapacity.uniformBudget_prodLensFinFst

/-- info: 'PersistenceCapacity.splitFstFn_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PersistenceCapacity.splitFstFn_eq

/-- info: 'PersistenceCapacity.splitSndFn_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PersistenceCapacity.splitSndFn_eq

/-- info: 'PersistenceCapacity.KE_factorFst_le_of_faithful' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PersistenceCapacity.KE_factorFst_le_of_faithful

/-- info: 'PersistenceCapacity.KE_factorSnd_le_of_faithful' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PersistenceCapacity.KE_factorSnd_le_of_faithful

/-- info: 'PersistenceCapacity.liftFst_smul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PersistenceCapacity.liftFst_smul

/-- info: 'PersistenceCapacity.CbHu_prodWorldFin_ge_fst' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PersistenceCapacity.CbHu_prodWorldFin_ge_fst

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

/-- info: 'PersistenceCapacity.decRec_encRec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PersistenceCapacity.decRec_encRec

/-- info: 'PersistenceCapacity.hammingDist_split' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PersistenceCapacity.hammingDist_split

/-- info: 'PersistenceCapacity.decRec_healing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PersistenceCapacity.decRec_healing

/-- info: 'PersistenceCapacity.healWorld_heals' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PersistenceCapacity.healWorld_heals

/-- info: 'PersistenceCapacity.healWorld_mem_codewords' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PersistenceCapacity.healWorld_mem_codewords

/-- info: 'PersistenceCapacity.healWorld_idem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PersistenceCapacity.healWorld_idem

/-- info: 'PersistenceCapacity.healWorld_fixed_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PersistenceCapacity.healWorld_fixed_iff

/-- info: 'PersistenceCapacity.core_healWorld' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PersistenceCapacity.core_healWorld

/-- info: 'PersistenceCapacity.settlesValue_healWorld' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PersistenceCapacity.settlesValue_healWorld

/-- info: 'PersistenceCapacity.surjOn_decRec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PersistenceCapacity.surjOn_decRec

/-- info: 'PersistenceCapacity.recMaj_hasMargin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PersistenceCapacity.recMaj_hasMargin

/-- info: 'PersistenceCapacity.recMaj_margin_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PersistenceCapacity.recMaj_margin_ge

/-- info: 'PersistenceCapacity.hammingDist_advRec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PersistenceCapacity.hammingDist_advRec

/-- info: 'PersistenceCapacity.decRec_advRec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PersistenceCapacity.decRec_advRec

/-- info: 'PersistenceCapacity.recMaj_not_hasMargin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PersistenceCapacity.recMaj_not_hasMargin

/-- info: 'PersistenceCapacity.recMaj_margin_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PersistenceCapacity.recMaj_margin_eq

/-- info: 'PersistenceCapacity.recMaj_margin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PersistenceCapacity.recMaj_margin

-- The witness world: `κ` recursive-majority blocks running a macro law `G`, beside an environment
-- running an arbitrary `π`, sharing nothing. A product of memories is a memory on the disjoint union
-- of their indices (`sumMem`), so the whole world has a cell structure and `hammingDist` splits
-- across the two parts (`hammingDist_sum_index`). The square is EXACT and needs no hypothesis on the
-- state (`witness_square`) — the update writes codewords whatever it was handed — so the reading
-- follows `G`'s own trajectory from step zero, from EVERY initial state (`witnessLens_iterate`); the
-- state takes one step to become a codeword state, the reading never needed to. The margin is the
-- block's, at every radius below `2 ^ k`, however large the environment (`witnessWorld_hasMargin`):
-- the reading ignores the environment's cells. `habitat_heals`'s hypothesis is distance to a
-- CODEWORD state and must be — between arbitrary states the claim is false at `k = 1`, where
-- `(0,0,1)` and `(0,1,1)` are one cell apart and decode oppositely; the attractor consists of
-- codeword states (`omegaLimit_witnessWorld_subset`), which is where the margin reads it.

/-- info: 'PersistenceCapacity.hammingDist_sum_index' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PersistenceCapacity.hammingDist_sum_index

/-- info: 'PersistenceCapacity.macroLens_habitatEnc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PersistenceCapacity.macroLens_habitatEnc

/-- info: 'PersistenceCapacity.hammingDist_habitat_blocks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PersistenceCapacity.hammingDist_habitat_blocks

/-- info: 'PersistenceCapacity.habitat_heals' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PersistenceCapacity.habitat_heals

/-- info: 'PersistenceCapacity.habitatWorld_forgets' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PersistenceCapacity.habitatWorld_forgets

/-- info: 'PersistenceCapacity.macroLens_surjective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PersistenceCapacity.macroLens_surjective

/-- info: 'PersistenceCapacity.macro_square' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PersistenceCapacity.macro_square

/-- info: 'PersistenceCapacity.intertwines_macroLens' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PersistenceCapacity.intertwines_macroLens

/-- info: 'PersistenceCapacity.witnessWorld_conj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PersistenceCapacity.witnessWorld_conj

/-- info: 'PersistenceCapacity.witness_square' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PersistenceCapacity.witness_square

/-- info: 'PersistenceCapacity.intertwines_witnessLens' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PersistenceCapacity.intertwines_witnessLens

/-- info: 'PersistenceCapacity.witnessLens_surjective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PersistenceCapacity.witnessLens_surjective

/-- info: 'PersistenceCapacity.omegaLimit_witnessWorld_subset' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PersistenceCapacity.omegaLimit_witnessWorld_subset

/-- info: 'PersistenceCapacity.witnessWorld_hasMargin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PersistenceCapacity.witnessWorld_hasMargin

/-- info: 'PersistenceCapacity.witnessLens_iterate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PersistenceCapacity.witnessLens_iterate

/-- info: 'PersistenceCapacity.witnessWorld_valid_after_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PersistenceCapacity.witnessWorld_valid_after_one

/-- info: 'PersistenceCapacity.witnessWorld_rejoins' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PersistenceCapacity.witnessWorld_rejoins

/-- info: 'PersistenceCapacity.witnessWorld_margin_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PersistenceCapacity.witnessWorld_margin_ge

/-- info: 'PersistenceCapacity.witness_world_hosts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PersistenceCapacity.witness_world_hosts

-- The pricing bridge: the combinatorics above lives on `Mem ι V`, where a perturbation is a number
-- of cells; the pricing stack lives on `Fin n`, where `n` counts STATES, because that is what a
-- table is indexed by. `stateEquiv` packs a memory state into the numeral its cells spell — cell `i`
-- at weight `2 ^ i`, cell `0` the low bit, the convention of `packMarks` and of Mathlib's
-- `finFunctionFinEquiv`, so `stateEquiv_digit` is the marking price's own digit lemma at base two.
-- `packWorld` transports any memory world onto the priced carrier and respects composition,
-- identity and iteration, so orbits survive; `packPerm` supplies the permutation the `Perm`-carrier
-- results ask for, and `packWorld_square` carries an intertwining square across intact. The bridge
-- makes the witness world EXPRESSIBLE in the pricing vocabulary; exhibiting a short program for its
-- table needs a numeral-level decoder, which is not built here.

/-- info: 'PersistenceCapacity.stateEquiv_val' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PersistenceCapacity.stateEquiv_val

/-- info: 'PersistenceCapacity.stateEquiv_digit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PersistenceCapacity.stateEquiv_digit

/-- info: 'PersistenceCapacity.packWorld_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PersistenceCapacity.packWorld_comp

/-- info: 'PersistenceCapacity.packWorld_id' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PersistenceCapacity.packWorld_id

/-- info: 'PersistenceCapacity.packWorld_iterate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PersistenceCapacity.packWorld_iterate

/-- info: 'PersistenceCapacity.packPerm_coe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PersistenceCapacity.packPerm_coe

/-- info: 'PersistenceCapacity.packLens_surjective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PersistenceCapacity.packLens_surjective

/-- info: 'PersistenceCapacity.packWorld_square' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PersistenceCapacity.packWorld_square

-- The bottom-up anchor. `decRec` recurses top-down, splitting the MOST-significant base-3 digit
-- (`tripleEquiv_val`: sub-block `c` sits at `i + 3 ^ k · c`) and making THREE recursive calls.
-- `reduceBot` collapses the LEAST-significant digit instead — each adjacent triple to its majority —
-- and `decRec_bottomUp` says the two orders agree: both evaluate the same ternary majority tree, one
-- from the root, one from the leaves. That matters because a bottom-up decode makes ONE recursive
-- call on a shrinking argument, which is the shape primitive recursion offers; the anchor licenses
-- reading the tree that way without changing what it computes. The whole proof is
-- `subBlock_reduceBot` — top blocks commute with the bottom reduction — which isolates the index
-- arithmetic `3 · (i + 3 ^ k · c) + r = (3 · i + r) + 3 ^ (k+1) · c` and nothing else.

/-- info: 'PersistenceCapacity.tripleEquiv_val' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PersistenceCapacity.tripleEquiv_val

/-- info: 'PersistenceCapacity.subBlock_reduceBot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PersistenceCapacity.subBlock_reduceBot

/-- info: 'PersistenceCapacity.decRec_bottomUp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PersistenceCapacity.decRec_bottomUp

-- The numeral decoder. Majority of three BITS is halving their sum (`maj3_natBit`, all eight cases,
-- axiom-free) — which keeps the numeral arithmetic free of `Bool`. `packReduce` is `reduceBot` on
-- numerals, and `packReduce_stateEquiv` is the ONLY crossing of the memory/numeral boundary: term-
-- wise, no induction, both sides `∑ j ∈ range (3 ^ k), d j · 2 ^ j` with `stateEquiv_digit`
-- identifying each bit with its cell. `numDecRec` then collapses `k` times and reads the low bit —
-- one recursive call per level, the shape `decRec_bottomUp` licenses — and `numDecRec_stateEquiv`
-- bridges it to `decRec`, each induction step being the square then the anchor and nothing else.

/-- info: 'PersistenceCapacity.maj3_natBit' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms PersistenceCapacity.maj3_natBit

/-- info: 'PersistenceCapacity.packReduce_stateEquiv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PersistenceCapacity.packReduce_stateEquiv

/-- info: 'PersistenceCapacity.numDecRec_stateEquiv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PersistenceCapacity.numDecRec_stateEquiv

-- The decoder as a PROGRAM. `packReduce` is primitive recursive once its `Finset.range` sum becomes
-- a `List` fold (the `markVal` idiom) — its bit extraction is `digitAt` at base two, literally.
-- `numDecRec` recurses on the depth with a CHANGING argument, which `Primrec.nat_rec` does not
-- offer; `numDecIter` carries `(remaining depth, numeral)` as the accumulator, which fits, and
-- `numDecIter_read` says the two agree. The induction closes only by peeling the iteration from the
-- FRONT (`Function.iterate_succ_apply`): peeling from the back leaves the initial depth mismatched
-- against the recursion's own counter. `decBuilder` is then the `markBuilder` idiom verbatim — one
-- program on `⟨depth, packed state⟩` — and `eval_decBuilder_stateEquiv` runs it on a packed memory
-- to return the bit `decRec` reads there.

/-- info: 'PersistenceCapacity.primrec_packReduce' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PersistenceCapacity.primrec_packReduce

/-- info: 'PersistenceCapacity.numDecIter_read' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PersistenceCapacity.numDecIter_read

/-- info: 'PersistenceCapacity.primrec_numDecIter' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PersistenceCapacity.primrec_numDecIter

/-- info: 'PersistenceCapacity.primrec_numDecRec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PersistenceCapacity.primrec_numDecRec

/-- info: 'PersistenceCapacity.eval_decBuilder' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PersistenceCapacity.eval_decBuilder

/-- info: 'PersistenceCapacity.eval_decBuilder_stateEquiv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PersistenceCapacity.eval_decBuilder_stateEquiv

-- The habitat on flat cells. `flatHab` relabels block `i`, position `p` to the flat cell
-- `p + 3 ^ k * i` — `finProdFinEquiv`'s convention, the same `tripleEquiv` uses one level down, so
-- both levels agree about which index is significant without anything being chosen twice. Packed
-- little-endian, a habitat state is then a base-`2 ^ 3 ^ k` numeral whose digit `i` IS the packed
-- block `i` (`stateEquiv_flatHab_blocks`), so extracting a block is extracting a digit and
-- `stateEquiv_flatHab_block` is the marking price's digit lemma at a third base (base `n` for the
-- marks, base two for a memory's cells, base `2 ^ 3 ^ k` for a habitat's blocks).
-- `numDecRec_block` is where the two levels meet: extract digit `i`, run the decoder, out comes the
-- bit `macroLens` reads off block `i`.

/-- info: 'PersistenceCapacity.stateEquiv_flatHab_blocks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PersistenceCapacity.stateEquiv_flatHab_blocks

/-- info: 'PersistenceCapacity.stateEquiv_flatHab_block' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PersistenceCapacity.stateEquiv_flatHab_block

/-- info: 'PersistenceCapacity.numDecRec_block' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PersistenceCapacity.numDecRec_block

-- The blocks' two constants and the macro word. A codeword block packs to all-ones
-- (`2 ^ 3 ^ k - 1`, the geometric sum) or zero (`stateEquiv_encRec`) — the two values a habitat
-- walk writes back. And decoding each block digit and assembling the results little-endian gives
-- exactly the packed macro reading (`macroWord_eq`): the regrouping lemma read backwards one level
-- up, per block the one-cell lemma, across blocks the same digit bookkeeping as everywhere in this
-- layer.

/-- info: 'PersistenceCapacity.stateEquiv_encRec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PersistenceCapacity.stateEquiv_encRec

/-- info: 'PersistenceCapacity.macroWord_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PersistenceCapacity.macroWord_eq

-- The habitat walk, computed on numerals. Three steps, each with its lemma already proved:
-- `macroWordOf` extracts the block digits, decodes each and assembles little-endian (`macroWord_eq`
-- says that is the packed macro reading); a lookup in the macro law's own packed table gives the
-- next macro state (`packWorld_apply`); `habWriteBack` writes the two constants back block by block
-- (`stateEquiv_encRec`), reassembled by `stateEquiv_flatHab_range`. `habStep_stateEquiv` chains the
-- three and nothing else enters — every step was proved before the walk was written. The walk reads
-- the macro law only as the `2 ^ κ`-entry table of its packed form, one entry per state.

/-- info: 'PersistenceCapacity.macroWordOf_stateEquiv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PersistenceCapacity.macroWordOf_stateEquiv

/-- info: 'PersistenceCapacity.habWriteBack_stateEquiv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PersistenceCapacity.habWriteBack_stateEquiv

/-- info: 'PersistenceCapacity.habStep_stateEquiv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PersistenceCapacity.habStep_stateEquiv

-- The walk is primitive recursive. No mathematics — the walk's meaning was settled by
-- `habStep_stateEquiv`; these say only that a program can carry it out, each following the shape
-- the marking price already uses (a bounded sum over `List.range` folded by `primrec_list_sum`,
-- with `/`, `%`, `^` doing the digit work). `macroWordOf` needs the decoder (`primrec_numDecRec`,
-- the pair-accumulator's payoff); `habWriteBack` needs only the two block constants; `habStep`
-- composes them either side of one table lookup.

/-- info: 'PersistenceCapacity.primrec_macroWordOf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PersistenceCapacity.primrec_macroWordOf

/-- info: 'PersistenceCapacity.primrec_habWriteBack' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PersistenceCapacity.primrec_habWriteBack

/-- info: 'PersistenceCapacity.primrec_habStep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PersistenceCapacity.primrec_habStep

-- The habitat world on flat cells. `habitatWorld` lives on `Mem (Fin κ × Fin (3 ^ k)) Bool`; the
-- pricing layer indexes tables by states of a `Mem (Fin N) Bool`, so `flatWorld` is the same world
-- conjugated by the relabelling. `habStep_packWorld` is `habStep_stateEquiv` with both sides named:
-- the walk, run on a packed state, computes `packWorld (flatWorld κ k G)`. Every state of the flat
-- world is a packed habitat and conversely, so the two carry the same information — this one is in
-- the vocabulary a price is written in.

/-- info: 'PersistenceCapacity.flatWorld_flatHab' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PersistenceCapacity.flatWorld_flatHab

/-- info: 'PersistenceCapacity.habStep_packWorld' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PersistenceCapacity.habStep_packWorld

-- The habitat world, priced. Two elaboration walls dissolved once: `lensTable_range` re-lists a
-- table along `List.range` (proved at symbolic `n`) so a bridge to a `2 ^ (κ · 3 ^ k)`-length table
-- never unifies an index; and `habStep` is made irreducible so the `Primrec` proof matches at the
-- head instead of grinding its body. Then the marking-price assembly verbatim: `habTableFn`
-- tabulates the walk, `habTableFn_eq` identifies it with the packed flat world's table,
-- `eval_habBuilder` extracts the code, and `KE_flatWorld_le` prices the world of `2 ^ (κ · 3 ^ k)`
-- states at `elen cG + O(size κ + size k)` — the macro law fed as a CODE and composed, so its length
-- is additive and nothing scales with the state count. The (U)-positive clause in world-table form.

/-- info: 'PersistenceCapacity.lensTable_range' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PersistenceCapacity.lensTable_range

/-- info: 'PersistenceCapacity.primrec_habTableFn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PersistenceCapacity.primrec_habTableFn

/-- info: 'PersistenceCapacity.habTableFn_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PersistenceCapacity.habTableFn_eq

/-- info: 'PersistenceCapacity.eval_habBuilder' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PersistenceCapacity.eval_habBuilder

/-- info: 'PersistenceCapacity.KE_flatWorld_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PersistenceCapacity.KE_flatWorld_le

-- The packaged Witness World. `hostsThreshold_of_capacity` crosses the internalization threshold, consuming
-- [Decoupling] §6.3's capacity polynomial as a black box. `KE_packWitnessWorld_le` prices the full
-- world — the flat habitat world beside an environment, via the endofunction product `prodWorldFinFn`
-- and `prodBuilder` — at `elen cG + elen cπ + O(size κ + size k)`. `card_readable_core_le` is the
-- contrast: the environment permutations admitting a faithful reading of the core world are
-- exponentially few (`KE_factorSnd_le_of_faithful` extracts the environment's rule, `card_KE_le`
-- counts short descriptions). `witness_world` conjoins the five positive clauses into the statement of
-- record — surjective, `G`-lawful from every state, margin `2 ^ k − 1`, cheaply owned, above the
-- threshold — for every member of the class.

/-- info: 'PersistenceCapacity.hostsThreshold_of_capacity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PersistenceCapacity.hostsThreshold_of_capacity

/-- info: 'PersistenceCapacity.KE_packWitnessWorld_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PersistenceCapacity.KE_packWitnessWorld_le

/-- info: 'PersistenceCapacity.card_readable_core_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PersistenceCapacity.card_readable_core_le

/-- info: 'PersistenceCapacity.witness_world' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PersistenceCapacity.witness_world

-- The (U)-positive clause in the capacity vocabulary and the core identification.
-- `CbHue_flatWorld_ge`: when the macro law is a permutation, the flat world's uniform entropic
-- capacity at `elen cG + O(size κ + size k)` is at least the reading's carried entropy — one program
-- reads the macro state back forever (`ownLens` carries the model, `readBuilder` supplies the decoder
-- from `⟨κ, k⟩` alone). `omegaLimit_witnessWorld_eq`: for permutation `G, π` the recurrent core is
-- exactly the codeword-habitat states; `witnessWorld_codeword` is the recurrent dynamics on them —
-- the explicit product permutation `(enc ∘ G ∘ dec) × π`.

/-- info: 'PersistenceCapacity.CbHue_flatWorld_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PersistenceCapacity.CbHue_flatWorld_ge

/-- info: 'PersistenceCapacity.omegaLimit_witnessWorld_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PersistenceCapacity.omegaLimit_witnessWorld_eq

/-- info: 'PersistenceCapacity.witnessWorld_codeword' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PersistenceCapacity.witnessWorld_codeword

-- Emergence: pricing the ceiling of [Decoupling] §3.5. `CbHu_ge_owned` is the reversible case — a
-- surjective owned frame over a permutation host is affordable via `ownership` + `CbHu_ge_of_uniform`.
-- `emergence` is the endofunction case: on the recurrent core `U` has order dividing `n !`, so its
-- inverse there is a forward power and the co-move-after-flow-in guest collapses to `θ ∘ U^[k]`,
-- computed by `emergeBuilder` (`iterTable` + `stepComp`, no core inverse) — an owned guest, lawful
-- from every initial state, at `elen cU + elen cθ + O(1)`.

/-- info: 'PersistenceCapacity.CbHu_ge_owned' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PersistenceCapacity.CbHu_ge_owned

/-- info: 'PersistenceCapacity.emergence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PersistenceCapacity.emergence

-- Basins: a region a permutation world never leaves is setwise invariant (`image_perm_eq`), so the
-- world restricts to a permutation of it and, transported along an enumeration, is a world of its
-- own. Carrying families correspond both ways, and the ledger's frame determination survives. The
-- capacity-level reduction is deliberately absent: transporting a table along the enumeration is an
-- explicit-code obligation, not a free one.

/-- info: 'PersistenceCapacity.image_perm_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PersistenceCapacity.image_perm_eq

/-- info: 'PersistenceCapacity.mem_iff_apply_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PersistenceCapacity.mem_iff_apply_mem

/-- info: 'PersistenceCapacity.pow_mem_of_closed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PersistenceCapacity.pow_mem_of_closed

/-- info: 'PersistenceCapacity.subWorld_pow_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PersistenceCapacity.subWorld_pow_apply

/-- info: 'PersistenceCapacity.permCarriesOn_restrict' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PersistenceCapacity.permCarriesOn_restrict

/-- info: 'PersistenceCapacity.permCarriesOn_extend' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PersistenceCapacity.permCarriesOn_extend

/-- info: 'PersistenceCapacity.permCarriesOn_frame_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PersistenceCapacity.permCarriesOn_frame_one

-- the endofunction substrate: carrying, capacity and the dilated rule over a general world
-- ([Persistence] §2, Definitions 2.1-2.2; §3). `permCarries_iff_carries` is the alignment check --
-- the permutation predicate IS the general one at an invertible update -- and `CbHe_perm` /
-- `CbHue_perm` are the sanity bridge: the general capacities restrict to the permutation ones.
/-- info: 'PersistenceCapacity.carries_coreLens_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PersistenceCapacity.carries_coreLens_eq

/-- info: 'PersistenceCapacity.carries_frame_eqOn_core' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PersistenceCapacity.carries_frame_eqOn_core

-- choice-free: the two predicates are one predicate, and `Equiv.Perm.coe_pow` is the only step.
/-- info: 'PersistenceCapacity.permCarries_iff_carries' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PersistenceCapacity.permCarries_iff_carries

/-- info: 'PersistenceCapacity.card_orbit_mul_prod_fiber_card' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PersistenceCapacity.card_orbit_mul_prod_fiber_card

/-- info: 'PersistenceCapacity.CbHe_le_core_factorial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PersistenceCapacity.CbHe_le_core_factorial

/-- info: 'PersistenceCapacity.CbHe_perm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PersistenceCapacity.CbHe_perm

/-- info: 'PersistenceCapacity.CbHue_perm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PersistenceCapacity.CbHue_perm

/-- info: 'PersistenceCapacity.KE_iterate_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PersistenceCapacity.KE_iterate_le

-- settling from a basin ([Persistence] §10.1, silent self-stabilization, read at §5's budget):
-- `iterate_mem_core` is the space transient (the state space bounds its own settling time);
-- `CbHev_eq_CbHeOn` is the reduction -- eventual capacity from a basin IS exact capacity on its
-- attractor; `CbHue_le_CbHe` compares the two budgets over an arbitrary endofunction, by replacing
-- the family with a clamped reindexing of itself rather than by arguing about the family given;
-- `eventual_descent_iff` is the general-law sibling of `eventual_decoupling_iff`.
/-- info: 'PersistenceCapacity.exists_image_stable_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PersistenceCapacity.exists_image_stable_le

/-- info: 'PersistenceCapacity.iterate_mem_core' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PersistenceCapacity.iterate_mem_core

/-- info: 'PersistenceCapacity.carriesOn_restrict_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PersistenceCapacity.carriesOn_restrict_eq

/-- info: 'PersistenceCapacity.orbit_restrict_iterate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PersistenceCapacity.orbit_restrict_iterate

/-- info: 'PersistenceCapacity.eventualEntropies_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PersistenceCapacity.eventualEntropies_eq

/-- info: 'PersistenceCapacity.CbHev_eq_CbHeOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PersistenceCapacity.CbHev_eq_CbHeOn

/-- info: 'PersistenceCapacity.CbHev_le_factorial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PersistenceCapacity.CbHev_le_factorial

/-- info: 'PersistenceCapacity.CbHue_le_CbHe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PersistenceCapacity.CbHue_le_CbHe

/-- info: 'PersistenceCapacity.eventual_descent_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PersistenceCapacity.eventual_descent_iff

-- the tower ([Persistence] §10.2 + §2): `Intertwines.comp` composes squares and multiplies
-- dilations; `Intertwines.anchored` is the identity-law case (a square that carries a memory);
-- `uniformBudget_comp` adds the budgets through one fixed builder, the dilation charged its
-- bit-length; `tower_no_free_lunch`/`_perm` cap the whole tower by the ITERATED base world's
-- uniform capacity at the summed budget; `entropy_comp_le` makes entropy antitone up the levels.
/-- info: 'PersistenceCapacity.Intertwines.comp' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PersistenceCapacity.Intertwines.comp

/-- info: 'PersistenceCapacity.Intertwines.anchored' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PersistenceCapacity.Intertwines.anchored

/-- info: 'PersistenceCapacity.tower_carries' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PersistenceCapacity.tower_carries

/-- info: 'PersistenceCapacity.compTableFn_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PersistenceCapacity.compTableFn_eq

/-- info: 'PersistenceCapacity.uniformBudget_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PersistenceCapacity.uniformBudget_comp

/-- info: 'PersistenceCapacity.tower_no_free_lunch' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PersistenceCapacity.tower_no_free_lunch

/-- info: 'PersistenceCapacity.tower_no_free_lunch_perm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PersistenceCapacity.tower_no_free_lunch_perm

/-- info: 'PersistenceCapacity.entropy_comp_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PersistenceCapacity.entropy_comp_le

-- The structural category of decoupled simulations (`ALT/DecoupledSimulation.lean`) — the domain
-- [Decoupling] §4.5 asks Conjecture 4.4's functor to start from. A morphism is a hosting square
-- (`Intertwines (U'^[τ]) U ℓ`) plus code-locality: the guest code the reading returns depends on
-- the host state only through the host's code region. STRUCTURAL ONLY — the resource grade on the
-- reading family, and the realizer transport it prices, are NOT here.
-- `code_time_indep`: the reading's code component is time-independent AUTOMATICALLY, from the
-- host's read-only property plus code-locality — no inhabitedness of the work region, no choice.
-- `Simulates.comp`: morphisms compose and dilations multiply, code-locality chaining with them —
-- with `Simulates.id` and the nontrivial `counter_simulates`, the category structure.
/-- info: 'DecoupledSimulation.code_time_indep' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms DecoupledSimulation.code_time_indep

/-- info: 'DecoupledSimulation.Simulates.comp' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DecoupledSimulation.Simulates.comp

-- the robustness margin ([Persistence] §10.1 + §2): `hasMargin_iff` factors the margin condition
-- into basin fatness and local constancy; `hasMargin_margin` attains the supremum, so the margin
-- names a radius at which the reading really is robust; `repair_tax` prices a margin by sphere
-- packing in the memory; `majority_margin` is the worked robust sub-system, margin at least one.
/-- info: 'PersistenceCapacity.hasMargin_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PersistenceCapacity.hasMargin_iff

/-- info: 'PersistenceCapacity.hasMargin_margin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PersistenceCapacity.hasMargin_margin

/-- info: 'PersistenceCapacity.hammingDist_transport' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PersistenceCapacity.hammingDist_transport

/-- info: 'PersistenceCapacity.repair_tax' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PersistenceCapacity.repair_tax

/-- info: 'PersistenceCapacity.repair_tax_surjOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PersistenceCapacity.repair_tax_surjOn

/-- info: 'PersistenceCapacity.majority_margin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PersistenceCapacity.majority_margin

/-- info: 'PersistenceCapacity.repair_tax_tight_majWorld' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PersistenceCapacity.repair_tax_tight_majWorld

-- §5 bounded recursor (FV-2)
/-- info: 'ParameterizedNNO.no_true_nno' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ParameterizedNNO.no_true_nno

-- §6.3 internalization (FV-8) + §5.4 Prop 5.4
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

-- §5: the bounded recursor upgraded to a categorical UNIVERSAL PROPERTY, reusing
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

-- §5 sharpened: a GENUINE, discriminating initial algebra reusing Mathlib's
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

-- §6.4 Corollary 6.4: capacity stratification — the FV-15 object delivered at a work budget `w`
-- that hosts the threshold (monotone in `w`, entered at capacity `2n`, excluded below `n`).
/-- info: 'CategoricalThreshold.hostsAt_threshold' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CategoricalThreshold.hostsAt_threshold

-- §6.5 Proposition 6.5 (FV-19): the reflective decision automaton — a shared-memory update whose
-- code cell is read-only (§3 Decoupling) and whose work cell runs the §6.3 bounded proof search,
-- halting on the §6 true-but-underivable Gödel sentence.
/-- info: 'ReflectiveAutomaton.step_fixes_code' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms ReflectiveAutomaton.step_fixes_code

/-- info: 'ReflectiveAutomaton.decodeCode_faithful' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms ReflectiveAutomaton.decodeCode_faithful

/-- info: 'ReflectiveAutomaton.decodeCode_nonconstant' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms ReflectiveAutomaton.decodeCode_nonconstant

/-- info: 'ReflectiveAutomaton.automaton_persists' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReflectiveAutomaton.automaton_persists

/-- info: 'ReflectiveAutomaton.automaton_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReflectiveAutomaton.automaton_run

/-- info: 'ReflectiveAutomaton.automaton_decides_godel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReflectiveAutomaton.automaton_decides_godel

-- §4 FINITE COPRODUCTS in the realizability category `Asm` (upstreamable):
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

-- §5 FV-18 ON THE GENUINE CARRIER ([Decoupling] §5.5): the endofunctor `X ↦ 𝟙 ⊕ X` on `Asm` (which
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

-- §4.2 coproduct closure of the capacity filtration: `|A ⊕ B| = |A| + |B|` fits in `max sₐ s_b + 1`.
/-- info: 'CapacityLayer.coprodAsm_fitsIn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CapacityLayer.coprodAsm_fitsIn

-- §4.2 THE SUBOBJECT CLASSIFIER OF THE FINITE FRAGMENT (FV-21): the comprehension subobject
-- `subAsm A P`, the one-bit classifier `Bool = 𝟙 ⊕ 𝟙`, and its pullback universal property.
-- `classifier_universal` — the classifying square is a pullback: `u` factors through the
-- comprehension subobject iff `χ_P ∘ u` is constantly `true` (no finiteness on the domain `C`);
-- `chi_unique` — `χ_P` is the unique classifying map, global elements separating the finite carrier.
-- The classification is of comprehension subobjects (the finite fragment); every function out of the
-- classified object being a morphism is the §4.1 property `AllTrackable`, which `finAsm` witnesses.
/-- info: 'RealizabilitySubobject.classifier_universal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RealizabilitySubobject.classifier_universal

/-- info: 'RealizabilitySubobject.chi_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RealizabilitySubobject.chi_unique

-- §4.2 equalizers as comprehension subobjects, with their fork universal property.
/-- info: 'RealizabilitySubobject.equalizer_universal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RealizabilitySubobject.equalizer_universal

-- §4.2 capacity accounting of the classifier inventory: comprehension subobjects cost no capacity
-- (`subAsm_fitsIn`), the classifier is one bit (`boolAsm_fitsIn`), and the power object `[T ⇒ Bool]`
-- fits in `s` work bits IFF `|T| ≤ s` (`powAsm_fitsIn_iff`, exact `2^{|T|}` cardinality) — the
-- higher-order capacity threshold of §4.2.
/-- info: 'CapacityLayer.subAsm_fitsIn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CapacityLayer.subAsm_fitsIn

/-- info: 'CapacityLayer.boolAsm_fitsIn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CapacityLayer.boolAsm_fitsIn

/-- info: 'CapacityLayer.powAsm_fitsIn_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CapacityLayer.powAsm_fitsIn_iff

-- §4.3 realizer-length non-closure (Shannon counting bound) — the realizer-length sibling of
-- FV-14: the SAME `2^s` capacity threshold that overflows the exponential in cardinality forces a
-- genuine morphism to need a realizer of bit-length `> s`. `Classical.choice` is genuine (via
-- `choose` on the short-realizer selector and `realizes_of_finite`).
/-- info: 'Realizability.realizer_length_overflow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Realizability.realizer_length_overflow

/-- info: 'Realizability.exp_realizer_overflow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Realizability.exp_realizer_overflow

-- §4.3 explicit exponential magnitude: the literal `≈ 2^{|s_work|}`-bit figure ([Decoupling] §4.3)
-- — the SAME fitting object needs a realizer of bit-length `≥ s·2^s`, sharpening the
-- linear `> s` figure of `exp_realizer_overflow` (Shannon counting bound at `b = s·2^s − 1`).
/-- info: 'Realizability.exp_realizer_overflow_exponential' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Realizability.exp_realizer_overflow_exponential

-- §4.3/§7.2 almost-all counting form (FV-16): all but `≤ 2^b` of the functions have every
-- realizer longer than `b`; the complement of the `≤ 2^b` short-realizable functions.
/-- info: 'Realizability.shortRealizable_card_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Realizability.shortRealizable_card_le

/-- info: 'Realizability.almost_all_realizer_overflow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Realizability.almost_all_realizer_overflow

/-- info: 'Realizability.almost_all_fatAsm_overflow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Realizability.almost_all_fatAsm_overflow

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

-- [Discovery] §4 — Cheng (2026) Theorem 4 re-checked: necessity core + the necessary-not-sufficient
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

-- [Discovery] Theorem 2.1 eq. (2): the lookup-table coding lower bound, content-checking
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

-- [Discovery] Theorem 2.1 eq. (1): the rule-based two-part code upper bound, content-checking
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

-- [Discovery] Theorem 2.1 CAPSTONE: dominance between actual code lengths — the rule-based two-part
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

-- [Discovery] §3 Theorem 3.1: the central/Bernstein condition (§3.2, proved) and the §3.3 discovery
-- assembly (threshold + Markov arithmetic, proved; GM Thm 22 / Markov / posterior-of-close imported
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

-- [Discovery] §4 Prop 4.2 (retention upper bound): the discovered rule persists under the
-- conditional-regeneration architecture, reusing [Decoupling]'s Decoupling Lemma. `retention_persists`
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

-- [Discovery] §3 Sub-problem B (Bayes-mixture redundancy, realizable-deterministic route toward dropping
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

-- [Discovery] §3.3 Proposition 3.3 (bounded surprise): pigeonhole on the cumulative bound — the steps
-- whose one-step squared Hellinger error exceeds ε number fewer than K(R)·ln2/(2ε), uniformly in n.
-- Carries no separation hypothesis: the surprises are budgeted, but not scheduled.
/-- info: 'BayesRedundancy.sqHellinger_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms BayesRedundancy.sqHellinger_nonneg

/-- info: 'BayesRedundancy.surprise_card_mul_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms BayesRedundancy.surprise_card_mul_le

/-- info: 'BayesRedundancy.surprise_card_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms BayesRedundancy.surprise_card_le

/-- info: 'BayesRedundancy.surprise_card_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms BayesRedundancy.surprise_card_lt

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

-- [Discovery] §3.3 Proposition 3.2 (FV-16): extensional `[R]`-concentration for the near-twin-rich
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

-- [Discovery] §3.3 FV-15: genuine ε₀-Hellinger + the ε₀→query-separation bridge (`HellingerBridge.lean`).
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

-- [SQ] §2 time-bounded Kolmogorov complexity (FV-Kt): on Mathlib's `Code`, the resource
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

-- [SQ] §4 Theorem 4.1 step-(c) total-work accounting (FV-B1): an `O(r·log(1/δ))` search window
-- times an `O(r)` per-step cost gives total work `O(r²·log(1/δ))` — thin product bookkeeping.
/-- info: 'PolyTimeAccounting.polytime_accounting' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PolyTimeAccounting.polytime_accounting

-- [SQ] §5 parity SQ counterexample (FV-A3): every real power of `r` is little-o of the modeled
-- parity statistical dimension `d_SQ` (`poly_isLittleO_dSQ`), so `d_SQ` is not polynomially bounded
-- (`dSQ_not_polyBounded`) — Assumption A fails for parity, hence Theorem 4.1 does not apply to it.
/-- info: 'ParityCounterexample.poly_isLittleO_dSQ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ParityCounterexample.poly_isLittleO_dSQ

/-- info: 'ParityCounterexample.dSQ_not_polyBounded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ParityCounterexample.dSQ_not_polyBounded

-- [SQ] §4 / App. A SQ version-space pruning (FV-A4): the candidate set stays poly-bounded under a
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

-- [SQ] §3.1 window-noise refinement of the FV-A4 pruning geometry: window sufficiency (W) is the
-- DETERMINISM of the one-step predictor `f_R`; it weakens to the window-noise rate
-- `η := μ(o_{t+1} ≠ f_R(w_t))` (W is `η = 0`). The truth survives the UNCHANGED `2τ`-rule when the
-- budget `2η ≤ τ` holds (`truth_survives_pruning_noisy`), and a `> 3τ + 2η`-separated impostor is
-- still pruned (`separated_impostor_pruned_noisy`) — both recovering the noiseless siblings at `η = 0`.
/-- info: 'SQVersionSpace.truth_survives_pruning_noisy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SQVersionSpace.truth_survives_pruning_noisy

/-- info: 'SQVersionSpace.separated_impostor_pruned_noisy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SQVersionSpace.separated_impostor_pruned_noisy

-- [SQ] §4 Theorem 4.1(i) sample complexity (FV-B2): the "Remark on ε₀" absorption collapsing the
-- imported [Discovery] Thm 3.1 discovery bound `O((r+log(1/δ))/ε₀)` to the stated `O(r²·log(1/δ))` under
-- the benign-class `ε₀ = Ω(1/r)`. (Complements FV-B1: B1 = step-(c) total work, this = part-(i) count.)
/-- info: 'SampleComplexity.sample_complexity_r2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SampleComplexity.sample_complexity_r2

-- [SQ] §3 ensemble SQ oracle, Tool (ii) (FV-E): Hoeffding concentration of the empirical SQ
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

-- [SQ] §3.1 the window-noise budget half, genuine content + wiring. A1 (`noise_gap_integral`): two
-- `[−1,1]`-valued measurable observables agreeing off a measurable event `E` differ in integral by
-- `≤ 2·μ(E)`, so a query answer is distorted by at most `2η`, `η := μ(E)` (integrability discharged
-- from boundedness on the probability measure). A3 (`sq_oracle_truth_survives_noisy`): threading the
-- gap through the arithmetic siblings and the `n ≥ (2/τ²)·log(2/δ)` sample complexity, the
-- deterministic truth `predR` survives the `2τ`-rule w.p. `≥ 1−δ` when `2η ≤ τ` — the empirical
-- mean's target `a = 𝔼φ` kept distinct from the truth `predR`.
/-- info: 'SQOracle.noise_gap_integral' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SQOracle.noise_gap_integral

/-- info: 'SQOracle.sq_oracle_truth_survives_noisy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SQOracle.sq_oracle_truth_survives_noisy

-- FV-E → FV-J glue: the finite-query union bound carrying per-query concentration to FV-J's
-- oracle object. `sq_oracle_uniform_tail` — if each of `Qs` fails tolerance `τ` w.p. `≤ δ`, then SOME
-- query fails w.p. `≤ |Qs|·δ` (`measure_biUnion_finset_le`). `empirical_isSQOracle` — off that event
-- (w.p. `≥ 1 − |Qs|·δ`) the `Qs`-restricted empirical answers satisfy `SQObjects.IsSQOracle`.
/-- info: 'SQOracle.sq_oracle_uniform_tail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SQOracle.sq_oracle_uniform_tail

/-- info: 'SQOracle.empirical_isSQOracle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SQOracle.empirical_isSQOracle

-- The per-query i.i.d. instantiation discharging the union bound's
-- `htail` from `sq_oracle_concentration` — `n ≥ (2/τ²)·log(2|Qs|/δ)` samples per query ⇒ the
-- empirical answers fail `IsSQOracle` on `↥Qs` w.p. `≤ δ`.
/-- info: 'SQOracle.empirical_isSQOracle_of_iid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SQOracle.empirical_isSQOracle_of_iid

-- [SQ] App. A Claim 2, post-discovery half (FV-F): geometric decay kills the `2^K` prefactor
-- past `T_discover` (`prefactor_le`), so the accumulated post-discovery pruned mass is `≤ δ/2` by
-- competitor-decay + Kraft alone — no maximal inequality (`accumulated_pruned_mass_le`).
/-- info: 'SQPrunedMass.prefactor_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SQPrunedMass.prefactor_le

/-- info: 'SQPrunedMass.accumulated_pruned_mass_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SQPrunedMass.accumulated_pruned_mass_le

-- [SQ] App. A predictive transfer (FV-H): the Bayes-mixture step that turns a bounded pruned
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

-- [SQ] App. A Claim 2, search-phase half (FV-G): the log-Bayes potential companion to FV-F.
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

-- FV-G CHAINED: `search_phase_mass_ville_chain` wires the two cores together — the
-- accumulated pruned mass exceeds `C + ln(1/δ)` only on the Ville excursion event, so
-- `μ{mass > C + ln(1/δ)} ≤ δ` (the paper's `O(r + log(1/δ))` w.h.p.). The `ln(1/δ)` term is DERIVED
-- from `ville_potential_budget` via `pruned_mass_le_budget`, not assumed. Its remaining hypotheses
-- are discharged below: the supermartingale premise by FV-I, and the Kraft `hΦ0` and the
-- no-excursion-conditional charge `hcharge` by the posterior model.
/-- info: 'SQSearchPhaseMass.search_phase_mass_ville_chain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SQSearchPhaseMass.search_phase_mass_ville_chain

-- FV-G, the Kraft initialization DISCHARGED: the truth's normalized prior weight is `2^{−K(R)}/S`
-- with total mass `S ≤ 1` by Kraft–McMillan (`BinaryKraft`), so `Φ₀ = −ln w₀(R) ≤ ln2·K(R)` — the
-- `hΦ0` the chain used to assume, now derived from the code itself (no assumed normalizer).
/-- info: 'SQSearchPhaseMass.kraft_potential_init_of_code' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SQSearchPhaseMass.kraft_potential_init_of_code

-- FV-G, the per-path charge DISCHARGED: under the posterior step model (prune a normalized mass,
-- renormalize, then Bayes-update), `−ln(1−m)` per prune is EXACTLY the potential drop plus the net
-- Bayes rise (`charge_identity`), and the rise telescopes to `ln (Z n)`, which is `< ln(1/δ)` on the
-- no-excursion event — so `hcharge` is a theorem, not a hypothesis.
/-- info: 'SQSearchPhaseMass.charge_of_posterior_model' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SQSearchPhaseMass.charge_of_posterior_model

-- FV-G CAPSTONE: the search-phase mass bound with BOTH modeled inputs closed. With probability
-- `≥ 1−δ` the accumulated pruned mass is `≤ ln2·K(R) + ln(1/δ)` (the paper's `O(r + log(1/δ))`),
-- and the only remaining premises are the posterior's dynamics — no inequality is assumed.
/-- info: 'SQSearchPhaseMass.search_phase_mass_charged' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SQSearchPhaseMass.search_phase_mass_charged

-- FV-I: the FV-G supermartingale premise DISCHARGED. On the trajectory space
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

-- FV-I hardening: the abstract factor `g` made CONCRETE for the paper's DETERMINISTIC
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

-- FV-J: the SQ objects made GENUINE (`ALT/SQObjects.lean`). The statistical
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

-- FV-L, identifiability-free: the version-space envelope WITHOUT the `2τ`-identifiability hypothesis
-- (the BFJKMR clustering argument), on the FV-J layer (`ALT/SQObjects.lean`). `sqDim_antitone_tol`
-- (antitone in the tolerance) + `exists_maximal_sepFam` (a maximal `2τ`-net exists) + `sepNet_covers`
-- (maximality ⇒ every survivor is `2τ`-close to a net point) + `merge_answer_close` (the mass-merge
-- averaging bound) assemble into `versionSpace_net_envelope`: for ANY version space `V ⊆ M`, a net of
-- card ≤ sqDim with a `2τ`-close retraction — no pairwise-separation hypothesis on the survivors.
/-- info: 'SQObjects.merge_answer_close' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SQObjects.merge_answer_close

/-- info: 'SQObjects.versionSpace_net_envelope' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SQObjects.versionSpace_net_envelope

-- FV-K: the prequential-MDL-with-SQ-pruning ALGORITHM as a Finset object
-- (`ALT/SQAlgorithm.lean`), with the identification theorems tying the standing FV artifacts to it.
-- `alive_mass_eq_Z_det` — the unpruned Bayes-consistent mass IS FV-I's mixture `Z cands w (detFactor
-- pred)` (the "identify g with the algorithm" item). `truth_survives` — App-A Claim 1 for the object
-- (realizable + τ-close truth stays alive, reusing FV-A4's `truth_survives_pruning` at the 2τ rule).
-- `separated_impostor_pruned_alg` — the FV-A4 converse (a 3τ-separated candidate is pruned).
-- `algorithm_damage_le` — FV-H's `accumulated_perturbation_le` at the algorithm's OWN step families
-- (survivors `alive (t+1)` vs pruned-away `prunedAt t`), so `ε_t` is its literal pruned fraction.
-- `posterior_concentration_transfer` — the algorithm's Dirac pmf instantiates [Discovery]'s
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

-- FV-K hardening: Theorem 4.1(i) assembled for the PRUNED algorithm via posterior
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

-- The commitment step's selector (`ALT/CommitmentSeam.lean`) — the [Discovery] §5 Theorem 5.1(iv)
-- bridge from the §3 posterior to the §4 read-only code, hardened on the [SQ] §4 algorithm object.
-- `commits_unique`: at most one candidate reaches the threshold `1 − δ/2`, by normalization — the
-- hypothesis `δ < 1` is load-bearing (at `δ = 1` two candidates can tie at half the mass and the
-- committed rule is genuinely undefined). `commitment_seam`: past the discovery horizon the
-- candidates satisfying the commitment predicate are EXACTLY the true rule, at every such time —
-- existence, uniqueness and time-stability of the selection in one equivalence.
-- What stays an architectural assumption, exactly as the paper states it: the WRITE of the selected
-- rule into the persistent code, and the `δ/2` corruption budget for keeping it there. Neither is
-- established; no code region appears in the module.
/-- info: 'CommitmentSeam.commits_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CommitmentSeam.commits_unique

/-- info: 'CommitmentSeam.commitment_seam' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CommitmentSeam.commitment_seam

-- FV-L: the BFJKMR version-space envelope over FV-J's
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

-- [SQ] §2 prefix-free Kolmogorov complexity `KP` is a SEMIMEASURE (FV-KP): the universal
-- a-priori / Solomonoff–Levin bound `∑ₓ 2⁻ᴷᴾ⁽ˣ⁾ ≤ 1` (`kraft_KP`, via Mathlib's Kraft route +
-- the injective least-index `K`), and the [Discovery] prior `w(R') = 2⁻ᴷᴾ⁽ᵉⁿᶜᵒᵈᵉ ᴿ'⁾` as a
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

-- [SQ] additive AST complexity `KE` (two-machine-invariance core, FV-KE): the additive
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

-- The Prop 2.2 gate (FV-KE cont.): the length-efficient binary constant `bconst`
-- correct (`eval_bconst`) with additive length `O(Nat.size n)` (`elen_bconst_le`) — the
-- `Θ(n)`-vs-`O(log)` fix over `Code.const`. `Classical.choice` is genuinely used (the doubling code
-- `dbl` is extracted from universality via `Classical.choose`).
/-- info: 'AdditiveComplexity.eval_bconst' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdditiveComplexity.eval_bconst

/-- info: 'AdditiveComplexity.elen_bconst_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdditiveComplexity.elen_bconst_le

-- FV-KE payoffs: [SQ] Prop 2.2 `|P|`-component (`S_T ≤ r + O(log n)` via the binary `bconst`,
-- `prop_2_2_core`) and the multiplicative-optimality model-bridge (`KE x ≤ elen d +
-- O(log p) + c`, `invariance_general`).
/-- info: 'AdditiveComplexity.prop_2_2_core' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdditiveComplexity.prop_2_2_core

/-- info: 'AdditiveComplexity.invariance_general' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdditiveComplexity.invariance_general

-- FV-AC ported to [Discovery] §1.1: two-machine invariance of the additive prior measure.
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

-- FV-AC hardening: the collector CONSTRUCTED (`ALT/Collector.lean`), so Prop
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

-- The native sequential-time cost (`ALT/TimeCost.lean`) and its collector payoff.
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

-- The native SPACE cost — the maximum intermediate bitlength (`Nat.size`), companion to `tc`.
-- `spaceCost_prec_le`: the Capacity-Bounded Evaluation crux — where `tc_prec_le` is a SUM linear in the
-- iteration count, the space bound is a `max` INDEPENDENT of it. Under a per-step workspace bound `S`
-- taken relative to a small accumulator (the satisfiable form — a literal `∀ x, spaceCost cg x ≤ S`
-- cannot hold, space grows with input bitlength) and an accumulator-bitlength bound `S`, the whole
-- `prec` stays `≤ max (spaceCost cf a) S`. This is the poly-space-workspace regime a bounded checker
-- lives in — the same loop on which `tc` is astronomically large.
/-- info: 'TimeCost.spaceCost_prec_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeCost.spaceCost_prec_le

-- The search cost (`ALT/SearchCost.lean`) — the cost model extended from the rfind'-free fragment to
-- ALL of `Nat.Partrec.Code`. `eval_eq_valP`: value-agreement UNRESTRICTED — the extended evaluator's
-- value component is `eval` on every code, `rfind'` included, which is what `eval_eq_val` could state
-- only on the fragment. `evalP_eq_evalT`: coherence — on the fragment the extended evaluator returns
-- exactly the total one's `(val, tc)`, so every result proved against `tc` transfers and there is ONE
-- cost model, not two. `evalP_dom`: the extended cost is defined exactly where `eval` halts — the
-- search neither restricts the domain (as a fuel bound would) nor extends it (as a placeholder would).
-- `tcP_rfind'_le`: the `rfind'` analogue of `tc_prec_le` — a uniform per-probe bound `B` gives a
-- search with witness `n` a cost `≤ (n+1)·(B+1)`, linear in the probes actually made. The witness is a
-- hypothesis, not a constant: an unbounded search admits no bound uniform in the input.
/-- info: 'TimeCost.eval_eq_valP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeCost.eval_eq_valP

/-- info: 'TimeCost.evalP_eq_evalT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeCost.evalP_eq_evalT

/-- info: 'TimeCost.evalP_dom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeCost.evalP_dom

/-- info: 'TimeCost.tcP_rfind'_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeCost.tcP_rfind'_le

-- The search WORKSPACE (`ALT/SearchSpace.lean`) — the space sibling of the search cost, making BOTH
-- native cost measures total over `Nat.Partrec.Code`. `eval_eq_valW`: value-agreement unrestricted —
-- the workspace evaluator's value component is `eval` on every code, `rfind'` included, so the
-- workspace is charged along the genuine computation. `evalW_coherent`: on the rfind'-free fragment
-- it returns exactly `(val, spaceCost)`, so `spaceCost_prec_le` is a statement about this one model.
-- `spaceCostP_rfind'`/`spaceCostP_rfind'_le`: the search's space laws — the exact probe-MAXIMUM
-- identity, and the bound `max S (Nat.size (n+m))` in which THE PROBE COUNT IS ABSENT. Where the
-- step account pays `(n+1)·(B+1)` for `n+1` probes, rerunning a probe reuses the same workspace;
-- only holding the answer adds bits.
/-- info: 'TimeCost.eval_eq_valW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeCost.eval_eq_valW

/-- info: 'TimeCost.evalW_coherent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeCost.evalW_coherent

/-- info: 'TimeCost.spaceCostP_rfind'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeCost.spaceCostP_rfind'

/-- info: 'TimeCost.spaceCostP_rfind'_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeCost.spaceCostP_rfind'_le

-- The bounded checker's scratch account (`ALT/CheckerScratch.lean`) — the [Decoupling] §6.3
-- workspace bound assembled from the per-constituent capacity bounds and the native space cost.
-- `checker_scratch_closure`: the enumeration over the `M_chk + 1` candidate proof codes runs in
-- `max (spaceCost cf a) S` workspace, with the budget `M_chk` ABSENT from the bound, stated in
-- §6.3's own bit-length vocabulary (`size_eq_clog` is the whole dictionary). The per-candidate
-- `Δ₀`/poly-time check of a held candidate (Buss 1986) is not constructed: it is the paper-level
-- input, entering as the hypothesis `hstep`. `checker_space_time_contrast`: the same loop priced
-- twice — the budget hypothesis `M_chk ≤ g^2` is consumed by the TIME half alone (exhaustive
-- search, polynomial in the value `g`), never by the space half. `checkerLoop_val_decides`: the
-- native bounded recursion computes the same verdict as the finite fold `Decide`.
/-- info: 'CheckerScratch.checker_scratch_closure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CheckerScratch.checker_scratch_closure

/-- info: 'CheckerScratch.checker_space_time_contrast' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CheckerScratch.checker_space_time_contrast

/-- info: 'CheckerScratch.checkerLoop_val_decides' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CheckerScratch.checkerLoop_val_decides

-- Capacity-bounded evaluation (`ALT/CapacityBoundedEval.lean`) — the evaluator-side half of the
-- [Decoupling] §4.5 crux of Conjecture 4.4. `size_val_le_spaceCost`: the keystone, an output is
-- never wider than the workspace charged for producing it (the `RfindFree` hypothesis is essential,
-- `spaceCost` pricing `rfind'` as the placeholder `0`); `size_valW_le`: the same over the workspace
-- evaluator, unconditional on all of `Nat.Partrec.Code`. `spaceCost_comp_within`: grade closure —
-- a realizer within an `S`-bit workspace, fed a value produced within an `S`-bit workspace, runs
-- within the `S`-bit workspace. The transport clause of the crux (a capacity-respecting simulation
-- carries realizers across without overflowing the budget) is a statement about simulation
-- morphisms, which this development does not define; it is NOT established here.
/-- info: 'TimeCost.size_val_le_spaceCost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeCost.size_val_le_spaceCost

/-- info: 'TimeCost.size_valW_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeCost.size_valW_le

/-- info: 'TimeCost.spaceCost_comp_within' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeCost.spaceCost_comp_within

-- Transporting a realizer across a change of encoding (`ALT/GradeTransport.lean`) — the action on
-- morphisms that [Decoupling] §4.5's Conjecture 4.4 needs, priced in both currencies. The transport
-- is the coded conjugation `comp c_emb (comp r c_proj)`, at FIXED algebra: this is re-encoding
-- within one assembly category, NOT the per-subsystem functor with its state-level layout, which
-- stays paper-level. `realizes_transport`: the conjugate realizes the same function against the
-- re-encoded conventions, given the retraction identity on the input side (the output side needs
-- only a coded map). `spaceCost_transport_le`: workspace grades MAX — `≤ max g b`, with no constant,
-- a conjugation forming no pairs. `elen_transport`: description lengths ADD, exactly, `+ 6` for the
-- two serialized `comp` nodes. The dilation of a hosting square enters NEITHER bound: it prices
-- time at the level of the dynamics, not the workspace of one application.
/-- info: 'GradeTransport.realizes_transport' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GradeTransport.realizes_transport

/-- info: 'GradeTransport.spaceCost_transport_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GradeTransport.spaceCost_transport_le

/-- info: 'GradeTransport.elen_transport' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GradeTransport.elen_transport

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
-- holds at most `codeDepth (ofNat p)` cells, which with `size_stack_le` bounds the workspace. `eval_rfind'_unfold`: unbounded search as a one-probe recurrence — Mathlib
-- states the `rfind'` clause through `Nat.rfind` over an offset, and this is the recurrence the
-- machine implements; of independent use. `machine_sound`: if the machine halts after any number of
-- steps, its answer is a genuine value of the code it was given — exact, no fragment restriction
-- (unbounded search is an ordinary frame) and no fuel. Proved by giving each configuration a
-- denotation and showing a step never changes it. `machine_complete`: the converse, via the fuelled
-- evaluator used as an induction principle only — every value the code produces is reached by the
-- machine. Together the two pin the semantics to `Code.eval` on all of `Nat.Partrec.Code`. What is
-- NOT established is a step-count BOUND; the run is given existentially.
-- `tc_precFree_const`: a code built without bounded recursion charges a step count independent of
-- its input — the exact premise a fixed-skeleton constant-cost step would need. `Nat.Partrec.Code`
-- has no arithmetic primitive beyond `succ`, so realizing this step function needs `prec` for all
-- of its packing and every branch test, and `tc_prec_le` then charges by the VALUE of a counter
-- rather than its bit-length. The workspace side is unaffected (`spaceCost_prec_le` is a `max`).
/-- info: 'BoundedInterp.eval_rfind'_unfold' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms BoundedInterp.eval_rfind'_unfold

/-- info: 'BoundedInterp.machine_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms BoundedInterp.machine_sound

/-- info: 'BoundedInterp.size_stack_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms BoundedInterp.size_stack_le

/-- info: 'BoundedInterp.isStack_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms BoundedInterp.isStack_run

/-- info: 'BoundedInterp.stkDepth_prec_descend' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms BoundedInterp.stkDepth_prec_descend

/-- info: 'BoundedInterp.runMeasure_not_antitone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms BoundedInterp.runMeasure_not_antitone

/-- info: 'BoundedInterp.stkDepth_run_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms BoundedInterp.stkDepth_run_le

/-- info: 'BoundedInterp.machine_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms BoundedInterp.machine_complete

/-- info: 'BoundedInterp.tc_precFree_const' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms BoundedInterp.tc_precFree_const

-- The step function REALIZED as a `Nat.Partrec.Code` (`ALT/CodeArith.lean`, `ALT/CodePacking.lean`)
-- — the interpreter of `ALT/BoundedInterp.lean` built from the eight constructors. `Nat.Partrec.Code`
-- has no arithmetic primitive beyond `succ`, so addition, multiplication, subtraction, division,
-- remainder, powers, bit-length and every comparison are built from bounded recursion first; the
-- packing and accessors follow; then the two group codes and the assembly. `val_stepU`: the code
-- computes the mathematical layer's step function on EVERY numeral, halted and stuck configurations
-- included. `rfindFree_stepU`: nothing in it searches, so the workspace account is total on it.
-- Priced for SPACE only — the native step count charges by the VALUE of a bounded recursion's
-- counter, which is why no time law is claimed (`tc_precFree_const` above records the premise that
-- fails). `not_spaceIO_cDbl`: the WORKSPACE shape "input-or-output width plus a constant" fails
-- already at doubling — a `pair` node is charged the width of the pair it forms, and pairing a
-- value with itself doubles it, so no constant closes the gap. The honest workspace bound for the
-- realized step is a MULTIPLE of the wider of its input and output, not that width plus a constant.
/-- info: 'CodePacking.val_stepU' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CodePacking.val_stepU

/-- info: 'CodePacking.rfindFree_stepU' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms CodePacking.rfindFree_stepU

/-- info: 'CodePacking.not_spaceIO_cDbl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CodePacking.not_spaceIO_cDbl

/-- info: 'CodePacking.spaceCost_stepU_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CodePacking.spaceCost_stepU_le

/-- info: 'CodePacking.val_runU' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CodePacking.val_runU

/-- info: 'CodePacking.spaceCost_runU_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CodePacking.spaceCost_runU_le

/-- info: 'BoundedUniversal.universalAt_holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms BoundedUniversal.universalAt_holds

/-- info: 'AdditiveComplexity.prop_2_2_t_poly' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdditiveComplexity.prop_2_2_t_poly

-- The `PolyTime` predicate and its closure toolkit (`ALT/PolyTime.lean`), downstream
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

-- `PolyTime` validation — the `polyTime_prec` `hiter` blocker, the repaired loop closure, and a
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

-- The data layer for the 1-DL consistency solver (`ALT/DecisionListData.lean`).
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

-- The decode-cost verdict, the flag-cons pivot, and the indexed accessors.
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

-- The inner scan primitives of the greedy 1-DL consistency solver
-- (`ALT/DecisionListSolver.lean`). THE FINDING: the native `tc` makes value-arithmetic (general `=`,
-- `isZero`, `add`) value-linear, so the scan must use a BIT-LOGIC gate library (binary features/labels)
-- and avoid label equality (track `sawZero`/`sawOne` bits instead). `val_cAnd`/`val_cEqBit` — the gate
-- semantics; each gate is bit-closed and `O(1)`-`tc` on bits. `val_cPurity` — the purity primitive `val`
-- law (loop = iterated carried-suffix step). `purity_correct` — the scan realises the covered-label
-- fold over `zip msks exs`. `purity_isPure_iff`/`purity_commonLabel`/`purity_sawAny` — the 3-field
-- verdict `⟨isPure, ⟨commonLabel, sawAny⟩⟩` reads out as "isPure iff not both a covered 0-label and
-- covered 1-label", "commonLabel = sawOne", and "sawAny ≠ 0 iff the literal covers ≥1 remaining
-- example" (the covering bit that stops a vacuous pure literal stalling greedy).
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

-- The per-step cost bound is discharged, so purity is a self-contained
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

-- The greedy outer loop `solve` (`readM inst` rounds of covering-pure-literal
-- selection + mask refinement, output built by prepend then one final `cReverse`). `polyTime_solve` —
-- packaged as `PolyTimeOn SolveWF solveVal`: `O(m²·k²)` native cost (`k` rounds × one `findLit` `O(m·k²)`
-- + one `maskUpdate` `O(m·k)`), and — the crux — the exponential flag-cons OUTPUT stays poly-bit because
-- the instance already pays (exponentially) for its `m` examples: `two_pow_readM_le` gives
-- `2^(readM) ≤ size n + 1`, so `svCnt ≤ readM` rules cost `≤ (size n+1)²·O(size n)` bits (cubic).
-- `maskValid_solve` — the working mask stays a valid length-`m` bit-list every round (`maskValid_svAcc`
-- invariant); `dlModel_svAcc` — the output `svDL` is the flag-`cons` encoding of a genuine `List` of
-- `svCnt` rule-triples (the `List` model that lets `cReverse`/`size_encodeList_le` bound the output).
-- Greedy CORRECTNESS (finalMask all-zero iff a consistent 1-DL exists) is guarded below.
/-- info: 'OneDL.polyTime_solve' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OneDL.polyTime_solve

/-- info: 'OneDL.maskValid_solve' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OneDL.maskValid_solve

/-- info: 'OneDL.findLit_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OneDL.findLit_sound

-- Greedy CORRECTNESS. `progress` (Engine Lemma 1: a consistent 1-DL forces a covering-pure literal
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

-- [Decoupling] §4 CCC stand-in for Rep(S) (`ALT/CartesianClosed.lean`, namespace `RepSCCC`): Prop 4.3
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

-- [Decoupling] §5.3/§6 Gödel threshold (`ALT/GodelThreshold.lean`), tied to D1's `ParamNNO`: the
-- Theorem 6.2 form — depth `> g(T_S)` under incompleteness ⟹ represents-an-underivable-truth. Pure
-- threshold logic, so it is `Classical.choice`-free (`[propext, Quot.sound]`, a strict subset).
/-- info: 'GodelThreshold.reflective_of_depth' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GodelThreshold.reflective_of_depth

-- [Discovery] §1.2 regime consistency (`ALT/RegimeConsistency.lean`): the strict ordering `r<K<L`
-- under C1–C3 (`regime_strict_ordering`) and its non-vacuity witness (`regime_satisfiable`).
/-- info: 'RegimeConsistency.regime_strict_ordering' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RegimeConsistency.regime_strict_ordering

/-- info: 'RegimeConsistency.regime_satisfiable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RegimeConsistency.regime_satisfiable

-- [Discovery] Cor 2.2 capacity threshold (`ALT/CapacityThreshold.lean`): in the regime, C1 entails
-- representability of the rule-based encoding (`representable_of_C1`).
/-- info: 'CapacityThreshold.representable_of_C1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CapacityThreshold.representable_of_C1

-- [Discovery] Thm 2.1 static MDL dominance (`ALT/MDLDominance.lean`): the exact §2.2 Step-3 gap
-- identity (`dominance_gap_eq`) and strict dominance in the regime (`mdl_dominance`).
/-- info: 'MDLDominance.dominance_gap_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MDLDominance.dominance_gap_eq

/-- info: 'MDLDominance.mdl_dominance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MDLDominance.mdl_dominance

-- [Discovery] §4.4 retention overhead (`ALT/RetentionOverhead.lean`): the eq.(4) decomposition
-- (`overhead_eq`) and the `O(r·log(r/δ))` explicit-constant bound (`overhead_bigO`).
/-- info: 'RetentionOverhead.overhead_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RetentionOverhead.overhead_eq

/-- info: 'RetentionOverhead.overhead_bigO' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RetentionOverhead.overhead_bigO

-- Binary Kraft–McMillan, the shared arithmetic (`ALT/BinaryKraft.lean`): Mathlib's inequality
-- specialized to the binary alphabet and reindexed along an injective code, finite
-- (`indexed_finset_sum_le_one`) and countable (`indexed_tsum_le_one`). Both the [Discovery] §1.1
-- prior and the program-length side (`AdditiveComplexity.kraft_KP_E`) consume these.
/-- info: 'BinaryKraft.indexed_finset_sum_le_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms BinaryKraft.indexed_finset_sum_le_one

/-- info: 'BinaryKraft.indexed_tsum_le_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms BinaryKraft.indexed_tsum_le_one

-- [Discovery] §1.1 universal-prior sub-normalization (`ALT/PriorNormalization.lean`): the countable
-- extension read at the hypothesis class — the `∝ 2^{−K}` prior is a semimeasure
-- (`prior_tsum_le_one`).

/-- info: 'PriorNormalization.prior_tsum_le_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PriorNormalization.prior_tsum_le_one

-- [Discovery] §3.3 explicit ε₀ lower bound (`ALT/EpsilonZeroBound.lean`): positivity (`eps0_pos`),
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

-- [Discovery] exact-gap retention break-even (`ALT/ExactBreakeven.lean`): the exact dominance gap is
-- strictly positive in the regime (`domGap_pos`) and B1a's break-even at the exact endpoints
-- (`breakeven_exact`).
/-- info: 'ExactBreakeven.domGap_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ExactBreakeven.domGap_pos

/-- info: 'ExactBreakeven.breakeven_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ExactBreakeven.breakeven_exact

-- [Discovery] K-reconnection (`ALT/KReconnection.lean`): the five load-bearing MDL-corpus theorems
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

-- [Discovery] / [SQ] base Kolmogorov complexity (`ALT/KolmogorovComplexity.lean`): unboundedness of `K`
-- (`K_unbounded`) and the headline uncomputability of `K` (`K_not_computable`).
/-- info: 'KolmogorovComplexity.K_unbounded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KolmogorovComplexity.K_unbounded

/-- info: 'KolmogorovComplexity.K_not_computable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KolmogorovComplexity.K_not_computable

-- [SQ] bit-length Kolmogorov complexity (`ALT/KolmogorovBitlen.lean`, namespace
-- `KolmogorovComplexity`): uncomputability of the paper's `r`-in-bits (`K_bitlen_not_computable`).
/-- info: 'KolmogorovComplexity.K_bitlen_not_computable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KolmogorovComplexity.K_bitlen_not_computable

-- [Inevitability] proof-chain skeleton (`ALT/ProofChainSkeleton.lean`): the §6 assembly is logically
-- connected with no missing link (`inevitability_full`) and bare representational reflection sits off
-- the tractability/retention path (`reflective_core`). Pure propositional logic — NO axioms.
/-- info: 'ProofChainSkeleton.inevitability_full' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms ProofChainSkeleton.inevitability_full

/-- info: 'ProofChainSkeleton.reflective_core' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms ProofChainSkeleton.reflective_core

-- …and the steady-state per-step resource bound ([SQ] Cor 4.4) is likewise off the SQ path
-- (`steady_state_bounded`): reached without the tractability edge and without SQ-learnability.
/-- info: 'ProofChainSkeleton.steady_state_bounded' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms ProofChainSkeleton.steady_state_bounded

-- [Discovery] §2.3 — Kolmogorov structure function, the 45° / geometric lower bound (FV-14,
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

-- [Decoupling] §6.3/§6.4 + [Persistence] §5/§7 — the expressiveness excess order. The graded
-- representational class is a faithful order (`RepClass_subset_iff`: inclusion iff budget ≤); the
-- strict internalization clause (`outgrows`) delivers the [Decoupling] §6.4 reflective object as a
-- predicate on the budget, non-degenerate below the Gödel-sentence size (`outgrows_excludes`); and
-- `witness_outgrows` places the [Persistence] §5/§7 Witness-World guest and the internalization
-- threshold on one carrier. Assembly over already-axiom-clean constituents; no numbered result.
/-- info: 'ExcessOrder.RepClass_subset_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ExcessOrder.RepClass_subset_iff

/-- info: 'ExcessOrder.outgrows' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ExcessOrder.outgrows

/-- info: 'ExcessOrder.outgrows_excludes' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ExcessOrder.outgrows_excludes

/-- info: 'ExcessOrder.witness_outgrows' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ExcessOrder.witness_outgrows
