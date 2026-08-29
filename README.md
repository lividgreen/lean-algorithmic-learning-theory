# lean-algorithmic-learning-theory

[![CI](https://github.com/lividgreen/lean-algorithmic-learning-theory/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/lividgreen/lean-algorithmic-learning-theory/actions/workflows/lean_action_ci.yml)
[![API docs](https://img.shields.io/badge/docs-API%20reference-4c1)](https://lividgreen.github.io/lean-algorithmic-learning-theory/)
[![DOI](https://img.shields.io/badge/DOI-10.5281%2Fzenodo.21284775-blue)](https://doi.org/10.5281/zenodo.21284775)
[![Lean](https://img.shields.io/badge/Lean%204-Mathlib-black)](https://leanprover-community.github.io/)
[![License](https://img.shields.io/badge/license-Apache--2.0-lightgrey)](LICENSE)

**How much can a bounded observer, living inside a system, work out about the
rules of that system — and what does it cost to hold on to what it works out?**

That question has a surprising amount of mathematics behind it, drawn from
learning theory, algorithmic information theory, computability and categorical
logic. This library machine-checks that mathematics in Lean 4, end to end: the
probabilistic tail bounds a bounded learner reasons with, the query model that
says what it can learn at all, a cost model that says what it can afford to
compute, and the representational limits it hits when it tries to model the
system it is part of — including the point where modelling itself becomes
self-reference and Gödel's theorem starts to bite.

Everything here is proved, not sketched: no `sorry`, no `native_decide`,
standard axioms only, with each capstone's exact axiom footprint asserted by a
guard that fails the build if it ever drifts. And where a theorem needs a
system to hold *of*, the library builds one and proves the construction is that
system — junk-satisfiability guards make the degenerate instantiations visible,
so the real witness's named fields are what carry the content.

## Highlights

Three pieces of this development we have not found formalized anywhere else,
in any proof assistant: the **statistical-query model** of learning, **Ville's
inequality**, and a **cost semantics attached to Mathlib's own model of partial
recursive functions** — the last being what lets a learning algorithm be
verified for correctness and running time in the same breath, rather than in a
program logic separate from the mathematics. On top of them sit results we
believe are firsts of their kind: a learner verified **correct and
polynomial-step at once**, a finite machine proved to satisfy a learning
theory's prerequisites **from its own dynamics**, and a growing world whose
own emitted history provably serves as its internal learner's oracle.

**Start here:** the [**API reference**](https://lividgreen.github.io/lean-algorithmic-learning-theory/)
is generated from the source and is the best way in — every definition and
theorem below is a click away, with its statement and its dependencies. Entry
points:

| | |
|---|---|
| [`Ville.lean`](https://lividgreen.github.io/lean-algorithmic-learning-theory/docs/ALT/Ville.html) | Ville's inequality — the anytime-valid tail bound Mathlib does not carry |
| [`SQEnvelope.lean`](https://lividgreen.github.io/lean-algorithmic-learning-theory/docs/ALT/SQEnvelope.html) | statistical-query learning, to our knowledge the first such formalization in any prover |
| [`DecisionListSolver.lean`](https://lividgreen.github.io/lean-algorithmic-learning-theory/docs/ALT/DecisionListSolver.html) | a learner verified **correct *and* polynomial-step**, against a cost model built here |
| [`DecisionListPredictor.lean`](https://lividgreen.github.io/lean-algorithmic-learning-theory/docs/ALT/DecisionListPredictor.html) | asking that learner twice decides what the surviving candidates agree on — or that they do not |
| [`Decoupling.lean`](https://lividgreen.github.io/lean-algorithmic-learning-theory/docs/ALT/Decoupling.html) | when a model a system holds of itself survives the system running |
| [`PersistenceCapacity.lean`](https://lividgreen.github.io/lean-algorithmic-learning-theory/docs/ALT/PersistenceCapacity.html) | what memory costs in a world that overwrites everything — the priced decoder, with exact constants |
| [`GodelThreshold.lean`](https://lividgreen.github.io/lean-algorithmic-learning-theory/docs/ALT/GodelThreshold.html) | the capacity threshold at which self-representation turns into incompleteness |
| [`LearningWitness.lean`](https://lividgreen.github.io/lean-algorithmic-learning-theory/docs/ALT/LearningWitness.html) | an explicit system that meets those prerequisites — built, not assumed to exist |
| [`GrowingHostWitness.lean`](https://lividgreen.github.io/lean-algorithmic-learning-theory/docs/ALT/GrowingHostWitness.html) | a growing world that emits its own learning oracle, membership proved from its own dynamics |
| [`GrowingSeamWitness.lean`](https://lividgreen.github.io/lean-algorithmic-learning-theory/docs/ALT/GrowingSeamWitness.html) | a growing world in both route-classes at once — learning from its own emitted process, emergence from its own growth — at any envelope-profile source |

## Verification standard

- No `sorry`, `admit`, or `native_decide`; standard axioms only
  (`propext`, `Classical.choice`, `Quot.sound`) — several cores are
  choice-free, and the structural capstone depends on no axioms at all.
- **Build-enforced axiom hygiene**: 1120 `#guard_msgs in #print axioms` guards
  assert each capstone's exact axiom set; `lake build` fails on any drift.
- **CI-enforced whole-library audit**: every declaration under `ALT` — not only
  the guarded capstones — is checked against the same allowlist by
  [`axiom-audit`](https://github.com/leanprover-community/axiom-audit) on each
  CI run, so a `sorry`, a `native_decide`, or a home-rolled axiom anywhere in
  the library fails the build. The two are complementary: the guards pin each
  capstone's *exact* axiom set in source, where it renders into the API docs;
  the audit covers everything the guards do not name. Reproduce it locally with
  `lake exe axiom-audit --root ALT` after a build.
- **Targeted imports throughout**: every module names exactly the Mathlib
  files it uses — no monolith `import Mathlib`, one vendored port excepted —
  so the dependency surface is explicit and the build/docs closure stays
  proportionate to what is actually used.
- To *genuinely* re-verify (guards only re-run on true elaboration), delete
  the project's compiled artifacts first:
  `rm -rf .lake/build/lib/lean/ALT*` then `lake build`.

## The public surface

Most of this development is `private`, and that is deliberate: what remains
public is an API rather than an accident of nobody having marked anything.
A declaration is public when something requires it to be —

1. an axiom guard names it (`#guard_msgs in #print axioms` cannot see a private
   name);
2. a companion paper cites it;
3. another module uses it;
4. a public declaration's **statement** mentions it — otherwise you could not
   restate the theorem; or
5. a public **definition** that is not `Code`-valued has it in its body —
   otherwise you could not unfold what the definition means.

Rules 4 and 5 are a transitive closure, and rule 5 stops at
`Nat.Partrec.Code`-valued definitions on purpose: the code constructions are
meant to be opaque, characterized by their exported `val_*`/`tc_*` lemmas rather
than by their syntax trees. One further reason is not mechanical: a declaration
a module's own docstring presents as a **main result** stays public even when
nothing above consumes it — a paper's headline statement should be reachable
whether or not another theorem happens to need it. What the machine does
enforce is that the surface never grows by accident: the closure is recomputed
against the compiled environment and ratcheted per module, so the surface can
narrow freely, while widening it requires an explicit, recorded decision.

**Versioning, plainly: the `v1.*` series does not follow semver.** The library
is pre-stabilization, and curating the public surface is part of the point —
so a minor release may remove or privatize public names, and some already
have. Two things make that livable: every release that loses a public name
lists each one in its release notes rather than counting them, and the install
snippet below pins a tag rather than a branch — nothing changes under you
until you move the pin. Strict semantic versioning is intended from a future
2.0; there is no timeline for it. If a name you actually depend on goes, that
is a good issue to open: a real consumer is a reason to keep something public
that the closure cannot compute.

**If you are looking for reusable pieces** rather than a paper's machine-checked
core, these are the library-shaped modules: `ALT/Code/EvalLaws.lean` (the
`Nat.Partrec.Code` evaluation laws Mathlib omits for `comp`, `left`, `right` and
`pair`), `ALT/Code/SizeArith.lean` (`Nat.size` and pairing arithmetic),
`ALT/Code/BitGates.lean` (Boolean gates as codes), and above them
`ALT/PolyTime.lean`, `ALT/TimeCost.lean` and `ALT/AdditiveComplexity.lean` (the
native cost model over `Nat.Partrec.Code`). These are leaves by construction.

Names follow the papers rather than local readability: where a paper writes
`C_b^{H,u}` or `tc(·)`, the Lean spells it `CbHu` and `tc`, because the
correspondence is worth more to a reader holding both than the extra characters
would be. `ALT/PersistenceCapacity.lean`'s module docstring decodes that
family's suffixes.

## Building

Pinned toolchain (`lean-toolchain`, `lake-manifest.json`):

```bash
lake exe cache get   # fetch the Mathlib cache
lake build           # several minutes of project elaboration on top of the cache
```

The library is `lake`-consumable as a dependency (package name `alt`,
library `ALT`):

```toml
[[require]]
name = "alt"
git = "https://github.com/lividgreen/lean-algorithmic-learning-theory"
rev = "<tag>"  -- pin to a tagged release; see the Releases page below for available tags
```

## What is proved here

The short form of each result, grouped by theme. Every module's docstring
carries the full statement of what it proves and — just as deliberately — what
it does not; the boundary notes below compress those to a line rather than
replace them.

### Tail bounds, information and ergodic tools

- **Ville's inequality** for non-negative supermartingales (`Ville.lean`) —
  the all-time tail bound anytime-valid inference is built on; absent from
  Mathlib (whose Doob maximal inequality is submartingale-only).
- **Finite-case information theory and coding bounds**: the data-processing
  inequality and Fano's inequality on finite types (`FiniteInfoTheory.lean`),
  a prefix-complexity semimeasure (`∑ 2^{−KP} ≤ 1`), an additive
  self-delimiting program-length measure with a length-efficient binary
  constant, and binary index-form Kraft–McMillan bridges (`BinaryKraft.lean`).
- An integrated port of the **pointwise Birkhoff ergodic theorem** (from
  [lua-vr/pointwise-birkhoff](https://github.com/lua-vr/pointwise-birkhoff),
  Apache-2.0 — see NOTICE).

### Statistical-query learning and rule discovery

- **Statistical-query learning** — to our knowledge the first SQ formalization
  in any proof assistant (`SQObjects.lean`, `SQEnvelope.lean`, …): the
  statistical query dimension with its separated-subfamily characterization
  definitional, a survivor pigeonhole, a *linear* version-space envelope under
  2τ-identifiability (Szörényi's maximality argument) with that hypothesis
  proved load-bearing by a near-duplicate guard family, an identifiability-free
  net envelope (`versionSpace_net_envelope`), and parity's `2^n` SQ-dimension
  lower bound derived from character orthogonality.
- **A prequential-MDL discovery chain** (`BayesRedundancy.lean`,
  `DeterministicDiscovery.lean`, `ExtensionalDiscovery.lean`,
  `SQAlgorithm.lean`, …): posterior concentration for realizable deterministic
  prediction, qualitative concentration on the on-trajectory equivalence class
  (rate provably uncomputable), pruning soundness, exact predictive-transfer
  bounds, and the pruned-algorithm discovery theorem — with the commitment
  step's selector provably unique, true under the discovery hypotheses and
  time-stable (`CommitmentSeam.lean`).
- **A mixing hypothesis checked at both ends, and window determinism**
  (`WindowDeterminism.lean`, `BirkhoffTool.lean`): exact window sufficiency
  and quantitative mixing cannot coexist on a finite alphabet — a process each
  of whose observations is determined by the previous `k` is eventually
  periodic, choice-free. The `MixingHoeffding` rate hypothesis is pinned at
  both ends — a *theorem* at the i.i.d. end, a vacuity guard at non-positive
  constants, and genuine refutability at every positive constant, the
  constant being where the hypothesis's content lives — and now **derived
  outright at finite state** (`MarkovHoeffding.lean`): every finite-state
  Markov chain with an operator-norm spectral gap has a machine-checked
  trajectory law and satisfies the tail at it, at an explicit constant
  (`exists_mixingHoeffding_of_gap`, via the transfer-operator induction
  `transferIter_invariant`) — dependent-process concentration of a kind
  Mathlib itself does not yet carry. A horizon-bounded twin
  (`MixingHoeffdingTo N`, what a learner reading one orbit segment actually
  consumes) carries its own vacuity floor and refutations; on it, the oracle
  over a whole scheduled query class is derived from a single orbit segment
  off an event of measure at most `δ`, and composed with the pruned learner's
  own discovery theorem (`FiniteHorizonDiscovery.lean`) into an end-to-end
  statement — the horizon bounds the answering of the schedule, never the run.
  A first genuinely **dependent** instance: the Bernoulli-noise window chain
  satisfies the rate at the named constant `4·k` for coordinate observables,
  at every noise rate (`NoisyWindowChain.lean`, engine in `ParityWalk.lean`).
  Boundary: multi-coordinate queries see a genuinely noise-dependent constant,
  not bounded here; the general spectral-gap theorem stays unproved.

### A cost model on Mathlib's computability, and learners verified against it

- **A two-currency cost model** for `Nat.Partrec.Code` — Mathlib's
  fuel-indexed `evaln` bounds values, not resources. Sequential steps and
  workspace bit-width (`TimeCost.lean`), extended to unbounded search by
  genuinely partial evaluators whose domain is exactly `eval`'s
  (`SearchCost.lean`, `SearchSpace.lean`), with per-constructor workspace
  bound laws — recursion and search enter as a `max` over their steps, never a
  sum (`CapacityBoundedEval.lean`) — and a bounded-enumeration workspace bound
  independent of the enumeration's length (`CheckerWorkspace.lean`).
  Boundary: time is unit-cost AST steps (arithmetic is value-linear), space is
  value bit-width.
- **A learner verified correct and polynomial-step at once**
  (`DecisionListSolver.lean`): the step model carries a greedy decision-list
  learner verified **both correct and `poly(m,k)`-step** — we believe the
  first learning algorithm mechanically verified for correctness and
  complexity together. Built over it, a **version-space read-off**
  (`DecisionListPredictor.lean`): extending the instance by the query point
  labelled each way and asking the verified solver twice *classifies* the
  surviving candidates — none consistent, all agreeing at the query (the
  answer is forced and returned), or two disagreeing — with its own explicit
  step bound. A **second class** carries both theorems
  (`ConjunctionSolver.lean`, `ConjunctionPredictor.lean`), built in a separate
  module against the solver's public API alone, so the transfer between
  classes is exercised rather than asserted.
- **A priced universal interpreter** (`BoundedInterp.lean`, `CodeArith.lean`,
  `CodePacking.lean`, `UniversalAt.lean`): a small-step interpreter for
  `Nat.Partrec.Code` on configuration numerals, proved sound *and* complete
  against `Code.eval`, then realized as an explicit code and priced —
  the reference dynamics runs within workspace *affine in the run's own
  configuration width* (`UniversalAt`). Universality with a constructor
  skeleton, where the usual universal witness is a bare existence statement
  nothing can price.
- **Kolmogorov complexity at two measures, and the load-bearing one is bits**
  (`KolmogorovComplexity.lean`, `KolmogorovBitlen.lean`,
  `KReconnection.lean`, …): the least-index measure `K` is uncomputable by the
  recursion theorem — and so, separately, is the **bit-length** measure
  `Nat.size ∘ encode`, the one the description-length results are stated at
  (`K_bitlen_not_computable`); the second proof re-runs the argument from
  scratch because `Nat.size` is not injective and the reduction genuinely
  fails. The load-bearing MDL theorems are instantiated at the bit-length
  complexity of a concrete rule (`ruleComplexity`). Boundary: two-machine
  invariance is deferred with a documented obstruction — Mathlib exposes a
  single fixed universal machine, and the classical bound needs two.

### Memory, persistence and the price of reading

- **Persistence capacity** (`Decoupling.lean`; `PersistenceCapacity.lean`, an umbrella over four thematic modules in `ALT/Persistence/`):
  the Decoupling Lemma — a faithfully decoded model persists iff the update
  is read-only on its region — and the exact price of evading it with
  time-dependent decoders (lens families, unconstrained, so the bounds are
  absolute). Persistable content is measured by the recurrent core —
  irreversibility, not overwriting, is what obstructs memory; a maximal moving
  family's first two frames determine the world's recurrent rule (`ledger_K`);
  a robustness margin is paid for in carried content (`repair_tax`, three-copy
  majority voting saturating the bound exactly); and sub-systems hosting
  sub-systems compose squares with added budgets — stacking buys structure,
  never generic capacity (`tower_no_free_lunch`). Under those results sits a
  counting core: a family read at any finite set of times is priced by one
  bijection per block of the joint partition its frames induce, and one fixed
  program turns that count into a description of the world
  (`FrameItinerary.lean`). Declining a move up the pricing order costs at most
  twice the declined address, and exactly twice is attained
  (`CanonicalFormLens.lean`); past the crossover where a lens's own address
  exceeds the fibre freedom it removes, "the composite is stronger" is
  **false** (`ExpensiveLens.lean`); and on a cyclic word the disagreements
  with its own `d`-shift are exactly the run boundaries of its `d`-decimation
  (`ReadingWord.lean`).
- **Evolution in a skew-product fiber** (`SkewFiber.lean`,
  `WeightedFiber.lean`, `QuantizationRate.lean`, `EvoAbsorption.lean`): a skew
  product is priced by its ingredients' codes plus a constant, nothing scaling
  in the state count — a `P`-fold blockwise population costs the base's code,
  *one* copy of the fiber's, and two numerals (`powFiber`). A fiber whose
  state is a weight vector updated by fitness-proportional selection has an
  update that *is* Bayes' rule — normalizing the integer multiplicative step
  gives exactly the posterior, term for term. What a finite carrier costs is
  priced both ways: below a sharp exactness horizon the finite run **equals**
  the exact Bayes run; past it, one generation stays within `4C/W` in total
  variation. Which repairs such a host can offer is settled negatively: the
  evolutionary step is *expansive* whenever selection does anything at all,
  and a robustness margin at a settled point forces that point to be the
  strict fitness maximum. Boundary: no projection onto a finite carrier is a
  replicator step; the residual does not telescope over a run.
- **A surprise budget, and decoupling on a growing code region**
  (`SurpriseBudget.lean`, `AccretiveDecoupling.lean`): an unconditional bound
  on how often a prequential mixture is surprised, priced per event against a
  reading's robustness margin — and the formalization corrected the assembly
  it was built from, since a margin does *not* compose across consecutive
  perturbations. Three independent repairs are proved; the third asks nothing
  of the host's dynamics (`survives_of_invariant`), the erasure repair is the
  minimum of a spaced-schedule family with the spacing proved load-bearing,
  and mere **settling** is shown parallel to the three rather than a fourth —
  in both directions, on witnesses. The repairs are pairwise independent but
  not jointly so: erasing every perturbation while never separating two
  memories forces a **single recurrent state**
  (`omegaLimit_subsingleton_of_corrects`), and the boundary is guarded — at a
  radius reaching the whole memory, the only invariant reading distinguishes
  nothing. Separately, the decoupling equivalence holds verbatim on a
  monotonically *growing* code region, with an append-only witness showing
  the statement does not reduce to one fixed partition.

### Realizability, self-representation and incompleteness

- **A realizability (assembly) category over Kleene's first algebra**
  (`Realizability*.lean`, `CapacityLayer.lean`, `RealizerLength.lean`, …):
  Cartesian closed with finite coproducts, a subobject classifier and
  equalizers on the finite fragment (`RealizabilitySubobject.lean`), a
  depth-bounded recursor as an object, a capacity filtration with non-closure
  in both cardinality and realizer length, and an initial-algebra
  characterization of the bounded recursor under which **Lambek's lemma
  provably fails**. On top: the structural category of decoupled learners
  with capacity-respecting simulations (`DecoupledSimulation.lean`), realizer
  transport priced in program length and workspace (`GradeTransport.lean`), a
  capacity-graded exponential with priced application
  (`GradedApplication.lean`, …), and a build-enforced boundary: the
  represent-but-cannot-derive phenomenon is re-exported over an import closure
  from which the exponential object is *absent*, so "no function space is
  needed" is machine-enforced rather than observed (`MinimalityWitness.lean`).
- **A sound bounded checker, and a classical sound-and-complete bounded
  decision** (`GodelChecker.lean`, `GodelCheckerComplete.lean`): two separate
  artifacts, not one — an *executable* sound bounded proof-checker, and a
  *noncomputable* classically-packaged sound-and-complete bounded
  non-provability decision (Foundation ships no `Decidable` instance for its
  own proof relation), axiom-clean for the finite theory PA⁻, with
  incompleteness discharged against
  [FormalizedFormalLogic/Foundation](https://github.com/FormalizedFormalLogic/Foundation);
  run by a two-cell decision automaton whose code cell is read-only — the
  sentence under test persists by the Decoupling Lemma while the work cell
  drives to the Gödel verdict (`ReflectiveAutomaton.lean`,
  `GodelCheckerAutomaton.lean`).
- **An expressiveness excess order** (`ExcessOrder.lean`,
  `ExcessOrderComplete.lean`): representational classes graded by work-bit
  budget, inclusions strict exactly as the budget grows, an internalization
  threshold as a predicate on the budget, and the capstone at Foundation's
  finite `𝗣𝗔⁻`: a cheaply-owned guest that carries its host's law and
  represents a true-but-underivable sentence, the incompleteness antecedent
  discharged rather than hypothesized (`witness_outgrows_paMinus`).
- **A dependency audit of the reflection chain**
  (`ChainDependencyAudit.lean`): which imports each conclusion actually
  consumes, with unused-binder marking so that "off the critical path" is
  compiler-certified rather than asserted. Purely structural: it proves no
  import, all edges being abstract propositions.

### The substrate classes, and the constructed witnesses

- **A substrate class, and a capacity clause that is necessary**
  (`SubstrateClass.lean`): the prerequisites a bounded learner needs in order
  to reach the reflective threshold, as reusable objects — a decoupled
  substrate, a regularity regime, and reflective capacity. The capacity
  requirement is proved **necessary** on an identified family of Gödel
  numbers, and proved *not* necessary on another; the regularity regime is
  machine-checked not to imply the capacity clause. A class-level `𝒮_E`
  constructor (`SubstrateEmergence.lean`) derives emergence-route membership
  for any decoupled update, packing and surjective frame — over a reversible
  update, every surjective frame qualifies (`substrateE_of_perm`). Boundary:
  the codes for table and frame are hypotheses at class level, and whether a
  read-only region is an honest code region is the instance's business.
- **A constructed learner that meets those prerequisites, and survives damage**
  (`LearningWitness.lean`, `FlooredMixture.lean`, `BasinSettling.lean`,
  `RedundantFiber.lean`, `DamageGate.lean`, …): the class is inhabited by an
  explicit system — a Bernoulli-noise window chain whose code region is never
  written — with a realization theorem pinning every statistical clause to the
  substrate's own emitted process, and a junk-inhabitation guard
  (`substrateL_junk_satisfiable`) showing what degenerate instantiations
  would satisfy, so the real witness's named fields carry the content. Its
  theory conditions are discharged at Foundation's finite `𝗣𝗔⁻` by a *single*
  incompleteness invocation threaded through both the capacity threshold and
  the underivable-truth payload (`witness_crossing_genuine_paMinus`). The
  learner riding it is a floored mixture whose run **is** an exponent
  automaton (`wRun_eq_pow_expRun`); off that identity come a surprise bound
  against any reference candidate — with refuting families showing
  realizability is load-bearing — settling from every carrier vector, and, on
  the witness's own trajectory, the identity that the true rule's miss count
  *is* the noise count (`witMiss_zero`). Survival under corruption is proved,
  not assumed: `P` copies reading one stream leave one untouched under any
  schedule touching fewer than `P`, so the composite reads the base's own next
  state (`RedundantFiber.lean`), and the composite's decode is priced with
  `P` entering only through its numeral (`KE_compFrameFlat_le`). Boundary:
  the damage model is a **named hypothesis of the companion paper, not a
  theorem of this library** — `DamageGate.lean` states exactly what that
  costs: a host-applicable gate is provably empty on a noise-free stream, the
  eventually-quiet class (`QuietFrom`) closes host-checkable and
  lifetime-free at once, and the containment itself rides the identification
  `noiseGated_iff_witMiss`, not the mere existence of a finitely-firing event.
- **A finite host certified into both route-classes, from its own dynamics**
  (`BlockPairProfile.lean`, `BlockPairHost.lean`,
  `BlockPairObservability.lean`, `BlockPairWitness.lean`,
  `BlockPairOverlap.lean`, `BlockPairPrice.lean`): a certified two-word signed
  block sequence whose cyclic autocorrelation vanishes on a whole band of lags
  at **every** block count, with an exact spike at the band's top
  (`cyclicCorr_blockSeq_zone`, `cyclicCorr_blockSeq_spike`, balance supplied
  by the Thue–Morse sign); a finite autonomous host — a counter paired with
  the noisy window chain — whose orbit provably emits that sequence and
  returns after one full period from **every** state
  (`hostUpdate_iterate_period_all`); concentration of the emitted process at
  every bounded query on its uniform phase law
  (`mixingHoeffding_of_deviation_bound`); and membership in the learning
  route-class `𝒮_L` proved on the machine's own dynamics
  (`hostWitness_substrateL`). The same host, re-packed onto the pricing
  machinery's numeral carrier, is a member of the emergence route-class as
  well: `hostWitness_overlap` states both memberships from a common threshold
  — the first `𝒮_E` inhabitant in this development, and the first system in
  both route-classes at once. Its rule is an exhibited program: the packed
  step proved primitive recursive and extracted from universality, so the
  grown guest is owned within an absolute constant plus `O(log Π)` with no
  imported code parameter (`hostOwned_cheap`). Registered as *Inevitability*
  Theorem 5.8, rows IN-37…IN-39. Boundary: reaching the threshold, not
  survival by margin (the host's core dynamics is a permutation); constants
  are the ones the proofs derive.
- **The seam at class level, with a deterministic pace and survival**
  (`TapeHost.lean`, `TapeHostObservability.lean`, `TapeHostWitness.lean`,
  `TapeHostOverlap.lean`, `TapeHostSchedule.lean`, `TapeHostFiber.lean`,
  `TapeHostSurvival.lean`, `BlockPairCriterion.lean`): the same architecture
  with its observation sequence a parameter and a window-deviation **profile**
  as hypotheses. From the profile alone, the whole scheduled query class
  mixes at `(2S + W a)² / (2 ln 2)`, and `tapeHost_overlap` puts every
  admissible sequence's host in both route-classes at one numeral set, one
  Gödel size outside every period (*Inevitability* Proposition 5.9). On every
  such host the scheduled SQ oracle is exact from an explicit horizon — no
  tail bound, no measure — and the schedule's pruning rule identifies the true
  literal in a two-sided window that is sharp: every density `η < (1 − μ)/4`
  works and no tolerance above `1/4` does
  (`schedSurvivors_eq_singleton_sharp`, `not_identifies_of_gt_quarter`). The
  single witness's noisy-branch machinery reads on the class
  (`TapeHostFiber.lean`), and a `P`-copy redundant fiber added as extra
  memory carries **survival**: both memberships transport to the composite,
  and under any confined damage schedule with `c · (n · η + W₀/2) < P` some
  copy is never touched (`comp_carries_survival`, `tapeHost_carries_survival`;
  *Inevitability* Propositions 6.10–6.11). Boundary: one architecture,
  parametric in the sequence — not a statement about hosts in general;
  survival in the redundancy form, at a horizon, conditional on the named
  damage model; nothing lifetime-free.

### Growing worlds: observability from the world's own growth

- **Growing worlds, and an accreting witness with one sentence standing
  still** (`GrowingWorld.lean`, `AccretingWitness.lean`,
  `AccretingExcess.lean`): stage-indexed worlds whose updates advance finite
  stages, closed under lawful factors (`advances_guestStage`), with the
  fixed-carrier theory recovered at constant stages. That a reading of a
  growing world must see the stage is a theorem, not a convention: over an
  append-only tape the stage-blind reading admits no guest law at all
  (`not_exists_stagedSquare_tapeDecode`). The accreting healer world — every
  block healed by recursive majority, one protected codeword appended per
  step — hosts a guest from every state, erases bounded perturbations in one
  step, doubles its extent at every stage, and, past an explicit threshold
  stage, hosts and represents a fixed true-but-underivable `𝗣𝗔⁻` sentence at
  every stage: one Gödel sentence, then every budget
  (`outgrows_paMinus_uniform`, `accreting_outgrows_paMinus`).
- **A composite fed by its own growth** (`GrowingComposite.lean`): the noisy
  window chain's noise is no longer supplied from outside but emitted by the
  world's own growing state — the window steps on exactly the bit the tape
  records, and the orbit's window coordinate is the chain's own window
  process (`windowFst_iterate_compUpdate`). Eventual periodicity transports
  between a source and its observation process in both directions, and at a
  single fixed trajectory the mixing hypothesis reduces to an explicit
  per-sample deviation bound (`mixingHoeffding_dirac_iff`) — the reading on
  which the periodic trap and its escape both run (next two bullets). A
  concrete decimated 3-automatic source is named with the guard instantiated
  at it (`mephisto`, `mephDecim`) — resting on two of its values differing,
  nothing more. Boundary: no description-length pricing in these modules;
  whether hosts accrete generically is untouched.
- **The periodic trap, sharpened to a dichotomy**
  (`PeriodicObservability.lean`): an eventually periodic observation carries
  the sampling-rate hypothesis against its own cycle average — at a constant
  of order the period squared, `(2(N + P))² / (2 ln 2)` — and against **no
  other declared answer**, at any positive constant
  (`mixingHoeffding_dirac_of_eventuallyPeriodic`,
  `not_mixingHoeffding_dirac_of_eventuallyPeriodic_ne`); packaged at the
  scheduled query class as one iff (`mixingHoeffding_dirac_pairChar_iff`). A
  finite deterministic host is eventually periodic by pigeonhole, so it is
  representative of its own loop and of nothing else — the door a growing
  world exists to escape. Boundary: the constant is the proof's own, not the
  best an eventually periodic observation can carry.
- **A substitution source with exact statistics, and its identification**
  (`SubstitutionSource.lean`, `SubstitutionSchedule.lean`,
  `SubstitutionComposite.lean`): the fixed point of the primitive
  substitution `a → aabb, b → abba`, block-coded — its exact lag correlations
  computed from the recursion itself, window-deviation bounds at every phase
  and horizon, and non-eventual-periodicity machine-checked
  (`not_eventuallyPeriodic_subObs`). The scheduled learner identifies the
  true literal on it at every phase from an explicit horizon
  (`subObs_identifies`). Fed back through its own window-8 chain
  (`subNoise`, `obs_subNoise`), the source satisfies E1 at itself
  (`subObs_mixingHoeffding`), inhabits the learning route-class with that E1
  (`subObs_witness_substrateL_of_e1`), is genuinely emitted by that
  substrate's own orbit (`subObs_readObs_iterate`) — and the periodic trap
  route is machine-checked **absent** on it
  (`not_eventuallyPeriodic_obs_subNoise`), the first source not designed for
  the purpose on which that is checked. Boundary: the window constants are
  loose relative to the exact block computation; nothing here claims they are
  sharp.
- **The strict-spectral substitution class** (`SubstitutionClass.lean`): the
  `√n`-scaled envelope profile (`EnvelopeProfileNat`) — the hypothesis shape
  the discrepancy dichotomy hands a primitive constant-length substitution
  with a strict spectral gap — with both consumers generalized: mixing at the
  envelope constant (`envelope_mixingHoeffding`) and the sharp identification
  window at a squared horizon (`schedSurvivors_eq_singleton_envelope`). The
  declared trend data is canonical given any envelope
  (`envelope_trend_unique`), and the landed instance inhabits the class
  hypothesis unconditionally. Boundary: the class enters through the envelope
  hypothesis alone — the dichotomy that delivers it for a strict-spectral
  member is a citation (Adamczewski 2004), not machine-checked content; no
  induced substitution or Perron vector is formalized.
- **The growing host's own membership** (`GrowingHostWitness.lean`): the same
  observation hosted on an **append-only** carrier — a window plus a growing
  tape that writes one fresh cell per step, rather than consuming a
  pre-written record — with the realization theorem unconditional (nothing
  reads the code, so no invariant is carried along the orbit), and the
  membership capstone `growingHostWitness_substrateL`: the append-only host
  is a member of `𝒮_L`, its observability drawn from its own emitted process.
  The world grows, and what it grows is its own oracle. Boundary: the code
  region is read-only by construction but carries no computational role — it
  exists because the class asks for a code/work split.
- **The growing core: the merge quotient as the canonical conservation
  guest** (`GrowingCore.lean`, `GrowingCoreCrossing.lean`): two states of a
  growing world eventually merge when some iterate identifies them, and the
  quotient carries an induced law that is injective with no hypothesis at all
  (`mergeLaw_injective`) and closes the staged square at every stage family
  (`stagedSquare_merge`). Every injective-law staged reading factors through
  it (`merges_invariant_of_stagedSquare`, `exists_mergeMk_injective`), so its
  retained profile is the exact ceiling on every conservation guest's extent;
  at a finite constant-stage host it is in bijection with the recurrent core
  (`mergeQuotCoreEquiv`), and robustness is merging by construction — the
  accreting witness's one-step erasure is a one-step merge
  (`accMerges_of_accErasure`). The witness's crossing generalizes from its own
  budget `t + 1` to any monotone unbounded budget profile
  (`eventually_hosts_uniform`). Boundary: no pricing and no ownership claim —
  an affordable canonical-representative selector stays a named hypothesis at
  paper level, and identifying a guest's stage budget with its bit count is
  the interpretive step owed there.
- **The memory width: a clock is not a memory** (`MemoryWidth.lean`): the
  antichain width of the retained profile under the induced law's
  reachability (`memWidth`, `ℕ∞`-valued), monotone with no hypothesis beyond
  `Advances` (`memWidth_mono`). The successor world's retained profile is
  unbounded while its width stays at one (`memWidth_nat_succ_eq_one`), and a
  fast counter meets the flag hypothesis read at set level — its profile in
  bijection with `Bool^t` — with the same width
  (`mergeStage_nat_succ_fastClock_encard`): the raw class count decides
  nothing. The accreting witness's width is at least `2^(t+1)` in any
  environment (`memWidth_accreting_ge`), exact at a trivial one
  (`memWidth_accreting_eq_of_trivialEnv`), and the crossing composes from the
  width (`eventually_hosts_uniform_of_accreting_memWidth`). Boundary: a
  separation, not a dichotomy — an antichain-shaped conservation guest can
  exceed the width (`exists_conservationGuest_extent_gt_memWidth`).
- **The pricing economy's growing form** (`GrowingPrice.lean`): the
  fixed-carrier Collapse Theorem does not transport — determination fails for
  a merely injective stage law (`exists_ne_frames_agreeing_on_range`) — while
  the graded ledger's coset count does, with falling factorials where the
  fixed carrier has factorials (`card_stageLaws`, `card_lawsConsistentWith`)
  and the originals recovered at equal sizes. The Kraft union collapse in pair
  form (`collapse_union_staged`) is non-vacuous (`exists_qualifying_pair_of_pos`)
  and is read at a growing world's own stage law (`collapse_union_growing`).
  The staged capacity `CbHs` is two-sided: capped at `2b + d + 2` outside a
  `2^{-d}` fraction of candidates (`CbHs_collapse`), floored by a marking
  family uniformly in the stage law (`CbHs_ge_marking`), the fixed-carrier
  capacity recovered at the world's own embedding (`CbH_le_CbHs`) — and the
  floor is optimal in its own quantifier: no family floors the staged
  capacity above `2b + 3` uniformly in the stage law
  (`exists_candidate_capacity_le`). A telescope realizes any sequence of
  injections as some growing world's own stage law
  (`telescope_realizes_lawSequence`), which is why growth cannot sharpen the
  bound. Boundary: the complexity-form transport of the ledger's `K(U) ≤ …`
  display is not attempted; the growing-world statements are relative to a
  chosen enumeration of the two retained profiles and price only the
  stage-to-stage law.
- **The growing seam, class-level: one growing world in both route-classes**
  (`GrowingSeamWitness.lean`): the accreting healer world fused with an
  arbitrary fed observation `o`, the appended block carrying `o`'s next value
  read off the habitat's own length, so the decoded word at stage `t` is
  exactly the observation prefix (`seamOrbit_fst`). The emergence package
  transports with no hypothesis on `o` (`seam_outgrows_paMinus`); a packed
  realization folds the habitat into one `Decoupling.Mem` whose own
  observation cell reproduces `o` along its orbit
  (`seamHostSubstrateTraj_eq_obs`); the packed carrier is a member of `𝒮_L`
  at any envelope-profile source, its E1 drawn from the envelope theorem on
  its own process (`seamHostWitness_substrateL`), and a member of `𝒮_E` at any
  `o` whatever, at the same numerals (`seamHostWitness_substrateE`). The
  overlap bundle ties the two at the same dynamics (`growingSeam_overlap`),
  and the substitution instance is recovered exactly
  (`growingSeam_overlap_subObs`). Boundary: the packed realization drops the
  environment coordinate; no description-length pricing appears; the
  witness's affordability and the budget-to-bit-count identification stay
  paper-level.

## Papers

The development machine-checks the load-bearing results of a companion series
of papers on bounded learners in deterministic environments. Docstrings cite
the series by bracketed short-title keys: **[Decoupling]** (decoupling and the
categorical threshold for representational reflection), **[Discovery]** (MDL
dominance and finite-time rule discovery), **[SQ]** (polynomial-time
convergence under statistical queries), **[Persistence]** (resource-bounded
persistence capacity: the priced decoder), **[Guests]** (a description-length
theory of systems running inside finite and growing dynamical systems: priced
factors, the Witness World, emergence, and growing worlds with their growing
core, memory width and staged collapse), **[Growth]** (endogenous
observability on growing hosts: statistical-query learning from substitution
sources at explicit horizons), and **[Inevitability]** (the
realization-synthesis capstone: two independent routes to a reflective
subsystem, and their assembly on one constructed witness in pathwise
and budget form, conditional on a named damage model) — so "[Discovery] §2.2" names a section of that paper. `FV-*` tags name
rows of the papers' formal-verification tables, mirrored by the axiom-audit
guard files, so a claim in a paper can be traced to the exact theorem that
carries it. Preprints are forthcoming — this README will link arXiv IDs as they
appear — and the development is described as a whole in a formalization paper
(in preparation).

The papers are what the library is *for*, but they are not needed to read it:
the module docstrings and the notes above stand on their own.

## Scope, and related formalizations

This is the **query-model, information-theoretic and computational** side of
learning theory: what a bounded learner can identify from queries, what its
representation costs, and what its computation costs. It deliberately does not
formalize the **empirical-process / statistical** side — uniform convergence,
Rademacher complexity, PAC generalization bounds — which is the subject of
[lean-stat-learning-theory](https://github.com/YuanheZ/lean-stat-learning-theory)
(arXiv:2602.02285); the two developments complement each other and share no
overlap that we are aware of. Elsewhere in the ecosystem, PAC learnability has
been machine-checked for decision stumps in Lean 3 (arXiv:1911.00385), and Coq
developments certify concrete generalization guarantees (Bagnall–Stewart, AAAI
2019) and reinforcement-learning convergence (CertRL, Vajjha et al. 2021).

What we have not found formalized anywhere, and therefore built here: the
statistical-query model, Ville's inequality, and a cost semantics attached to
Mathlib's own model of partial recursive functions — the last being what lets a
learning algorithm be verified for correctness and running time in the same
breath, rather than in a program logic separate from the mathematics.

## How this repository is maintained

This is a **curated snapshot**, not the working repository. Development happens
in a private monorepo alongside the companion papers, and each release is
rsynced here as a single reviewed commit — which is why the history is sparse
and why you will not find work-in-progress branches.

Practical consequences, if you want to engage with it:

- **Issues and questions are welcome** — for anything about the mathematics, a
  statement you think is wrong, a boundary you think is overstated, or a piece
  you would like made reusable, please open an issue.
- **Pull requests are awkward** rather than unwelcome: a patch here has to be
  replayed by hand into the private tree, so for anything larger than a typo an
  issue first will save you effort. Upstreamable pieces are a different matter —
  several modules are built as leaves precisely so they can go to Mathlib, and
  help with that is genuinely wanted.
- **The build is the specification.** If CI is green, every theorem stated here
  is proved from the axioms named above; if you find that untrue, that is the
  most valuable issue you could open.

## Citation and license

See `CITATION.cff` — concept DOI
[10.5281/zenodo.21284775](https://doi.org/10.5281/zenodo.21284775)
always resolves to the latest archived version. For a specific tagged
version and its own version DOI, see the
[GitHub Releases page](https://github.com/lividgreen/lean-algorithmic-learning-theory/releases)
and `CITATION.cff`. Code is Apache-2.0 (`LICENSE`); third-party attribution in
`NOTICE`. Developed by Mykola Palamarchuk (independent researcher), with
substantial AI assistance (Claude Code, Anthropic) under the author's
direction and review — every result is machine-checked by Lean and replayed
from a clean cache.
