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
Chaitin's incompleteness theorem is here as well, over Mathlib's universal
machine and for every recursively enumerable consistent extension of 𝗥₀
under consistency alone — to our knowledge the first in that setting, the one prior
machine-checked treatment being an Agda formalization for a purpose-built
machine and Basic Recursive Arithmetic.
Its additive form is here too, on the prefix machine: one constant for every
theory plus the theory's own prefix complexity — Chaitin's own constant under
consistency alone, to our knowledge the first machine-checked additive form —
and along a ladder of theories each placed at its own such threshold, the
theory's prefix complexity grows by at least a bit per rung, so no computable
family names that ladder uniformly.
Levin's coding theorem is here too, over a universal prefix machine built from
the serialized codes: every lower-semicomputable semimeasure lies within an
additive constant of the ideal code length, and the machine's algorithmic
probability is `2^{−K}` up to a constant factor and a universal
lower-semicomputable semimeasure — to our knowledge the first machine-checked
proof of the coding theorem in any prover, on an online Kraft–Chaitin
assignment verified with its invariant.

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
| [`ChaitinIncompleteness.lean`](https://lividgreen.github.io/lean-algorithmic-learning-theory/docs/ALT/ChaitinIncompleteness.html) | Chaitin's incompleteness theorem over Mathlib's universal machine, for every recursively enumerable consistent extension of 𝗥₀ |
| [`KBEnumerable.lean`](https://lividgreen.github.io/lean-algorithmic-learning-theory/docs/ALT/KBEnumerable.html) | Chaitin's theorem in its additive form on a prefix machine — the bound is one constant for every theory plus the theory's own prefix complexity |
| [`ChaitinPrefixLadder.lean`](https://lividgreen.github.io/lean-algorithmic-learning-theory/docs/ALT/ChaitinPrefixLadder.html) | a ladder of theories each placed at its own Chaitin threshold, gaining at least one bit of prefix complexity per rung — no computable family names it uniformly |
| [`CodingTheorem.lean`](https://lividgreen.github.io/lean-algorithmic-learning-theory/docs/ALT/CodingTheorem.html) | Levin's coding theorem on a universal prefix machine — prefix complexity is `−log₂` of algorithmic probability up to an additive constant, and that probability is a universal lower-semicomputable semimeasure |
| [`HaltingProbability.lean`](https://lividgreen.github.io/lean-algorithmic-learning-theory/docs/ALT/HaltingProbability.html) | Chaitin's theorem on the machine's halting probability — a dyadic lower approximation within `2^(-n)` of it has, as the pair `(n, m)`, prefix complexity at least `n − c` |
| [`EndpointClasses.lean`](https://lividgreen.github.io/lean-algorithmic-learning-theory/docs/ALT/EndpointClasses.html) | the whole radius-one rule space bracketed at its table bits — 52 tables accrete by one engine that needs no injectivity, 48 are provably zero, 28 stay undecided |
| [`HindsightCount.lean`](https://lividgreen.github.io/lean-algorithmic-learning-theory/docs/ALT/HindsightCount.html) | the observer's bill: the fewest misses any law on the last `k` readings makes is bounded exactly when the watched column settles — bounded at every zero-class table, unbounded at rule `90`'s cell one |
| [`RegisterClass.lean`](https://lividgreen.github.io/lean-algorithmic-learning-theory/docs/ALT/RegisterClass.html) | the bounded register's surprise bound over a class of learners — five properties of an update, the register's depth as the bill, two members and two non-members showing each property load-bearing |

## Verification standard

- No `sorry`, `admit`, or `native_decide`; standard axioms only
  (`propext`, `Classical.choice`, `Quot.sound`) — several cores are
  choice-free, and the structural capstone depends on no axioms at all.
- **Build-enforced axiom hygiene**: 1388 `#guard_msgs in #print axioms` guards
  assert each capstone's exact axiom set; `lake build` fails on any drift.
- **CI-enforced whole-library audit**: every declaration under `ALT` — not only
  the guarded capstones — is checked against the same allowlist, the checked-in
  `forgive.yml`, by [`forgive`](https://github.com/FormalizedFormalLogic/forgive)
  on each CI run, so a `sorry`, a `native_decide`, or a home-rolled axiom anywhere in
  the library fails the build. The two are complementary: the guards pin each
  capstone's *exact* axiom set in source, where it renders into the API docs;
  the audit covers everything the guards do not name. Reproduce it locally with
  `lake exe forgive ALT` after a build.
- **Targeted imports throughout**: every module names exactly the Mathlib
  files it uses — no monolith `import Mathlib`, one vendored port excepted —
  so the dependency surface is explicit and the build/docs closure stays
  proportionate to what is actually used.
- **Module-system code**: every file is a Lean `module` with explicit
  `public import` lines and an exposed public section, so a consumer on the
  module system imports it directly and a classic file imports it unchanged.
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
   otherwise you could not unfold what the definition means; or
6. Lean's module system requires it: every definition here is exposed
   (`@[expose] public section`), so a name an exposed body reaches — a
   `Code`-valued body, or a proof term inside a definition — must be public
   for the file to compile at all.

Rules 4 and 5 are a transitive closure, and rule 5 stops at
`Nat.Partrec.Code`-valued definitions on purpose: the code constructions are
meant to be opaque, characterized by their exported `val_*`/`tc_*` lemmas rather
than by their syntax trees. Rule 6 is wider than that closure, which is why
the ratchet below counts such names as over-keeps and the baseline records
them as accepted rather than as defects. One further reason is not mechanical: a declaration
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
- **The additive carrier's data rate** (`CodeDataRate.lean`): the
  self-delimiting serialization spends exactly three bits per syntax node
  (`elen_eq_three_mul_nodes`), yet the codes of `n` nodes number at most
  `(11/10)·(159/20)^n` against the `8^n` three bits could carry
  (`card_codesOfNodes_le`), so the additive complexity `KE` is bounded away
  from one bit per bit: for every constant `c` some `x` has
  `500·KE x > 501·size x + 500·c` (`KE_data_rate`). Read at the computable
  measure `μ(x) ∝ 2^{−(1 + 1/500)·size x}`, no constant makes `KE` an ideal
  code for it — the coding theorem cannot live on the additive carrier, which
  is why it is proved on the prefix machine `KB` below. Boundary: the witness
  is existential, no crossing size named; the exact growth constant
  `1 + 4√3 ≈ 7.928` is prose, the artifact carrying the rational bound.

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
  the statement does not reduce to one fixed partition — and it has its first
  theorem consumer, the committing substrate: `seqWrite` commits an arbitrary
  stream append-only, every committed cell held under every later iterate
  (`seqDecode_hereditary`), the permanent region in exact bijection with the
  prefix length (`tapeRegion_bijective`).

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
  classically-packaged sound-and-complete bounded non-provability decision,
  computable in Mathlib's sense (`computable_decide`, over Foundation's own
  bounded-existential lemma for its proof relation) though not runnable
  (Foundation ships no `Decidable` instance for its own proof relation),
  axiom-clean for the finite theory PA⁻, with
  incompleteness discharged against
  [FormalizedFormalLogic/Foundation](https://github.com/FormalizedFormalLogic/Foundation);
  run by a two-cell decision automaton whose code cell is read-only — the
  sentence under test persists by the Decoupling Lemma while the work cell
  drives to the Gödel verdict (`ReflectiveAutomaton.lean`,
  `GodelCheckerAutomaton.lean`).
- **Chaitin's incompleteness theorem over bit-length complexity**
  (`ChaitinIncompleteness.lean`): for every `Δ₁`-axiomatized consistent
  extension of `𝗥₀` — consistency alone, no soundness — the theory proves
  "the bit-length complexity of `s` exceeds `n`" for no `n` at or above the
  bit-length of one fixed-point program (`chaitin_theorem`), so all but
  finitely many such true sentences are unprovable in it
  (`chaitin_true_unprovable`), the exceptions counted at `2^n` at the bound
  `n` (`card_K_bitlen_le`, below), and both hold for every recursively
  enumerable such extension by Craig's trick (`chaitin_theorem_of_RE`,
  `chaitin_true_unprovable_of_RE`); the abstract Berry bound (`chaitin_bound`)
  holds for any computably enumerable relation asserting only true lower
  bounds, and the sentences are Foundation's own Σ₁ representation, negated.
  The constant is a Kleene fixed point's length, named rather than computed.
  The additive form lands on the prefix machine `KB` (`ChaitinPrefix.lean`,
  `SerializationParse.lean`, `KBEnumerable.lean`): one program `c₀` fixed for
  every theory, and `n < elen c₀ + KB(⌜e⌝)` at any program `e` enumerating
  the theory's provable sentences of this form — Chaitin's own constant, the
  theory's prefix complexity, under consistency alone (`chaitin_theoremB`,
  `chaitin_theoremB_RE`), with the true-and-unprovable family at that
  constant (`chaitin_true_unprovableB`) and an enumerator exhibited for every
  `Δ₁` theory (`exists_enumerator_chaitinB`); proved from two leaf
  propositions, each in its own module — a primitive-recursive parser of the
  serialization with its two-way specification (`eParserSpec`) and the
  computable enumeration of "`KB(s) ≤ n`" (`rePred_kleB`) — and assembled
  once both were proved, the hypotheses' joint satisfiability witnessed at
  `𝗣𝗔⁻` (`chaitin_theoremB_nonvacuous`). Boundary: the enumerator is of the
  theorems, not the axioms; the constant is named, not computed.
  The theorem then drives the deep ladder as a third rung selector at `𝗥₀`
  (`ChaitinLadder.lean`): a chain of theories each certifying a description
  length its predecessor could not.

- **The deep ladder: the crossing recurs over each enlarged theory**
  (`DeepLadder.lean`, `ChaitinLadder.lean`): a chain builder parametric in a
  **rung selector** — a rule picking, at each theory in the chain, a sentence
  true in `ℕ` and unprovable in it — with the theory appending that sentence
  and the rung itself at every stage (`RungSelector`, `ladderTheory`, `rung`).
  Every rung is true and unprovable in the theory it extends (`rung_true`,
  `rung_unprovable`), the chain ascends strictly (`ladderTheory_lt_succ`),
  and the internalization crossing recurs at every rung, hosted eventually and
  forever after (`ladder_outgrows`, `accreting_ladder`), under the ladder's
  own capacity bound (`ladder_card_le_at_budget`). Three selectors: a hidden
  one at `𝗣𝗔⁻`, chosen from Foundation's incompleteness theorem
  (`hiddenSelector`); the **explicit** one at `𝗜𝚺₁` — Foundation's own Gödel
  sentence of each stage's standard provability predicate, exhibited rather
  than chosen (`explicitSelector`, `explicitRung_eq_gödel` by `rfl`) — at
  which every rung is provably equivalent to the consistency sentence of the
  theory it extends and each successor theory is deductively equivalent to
  Foundation's consistency extension (`explicitLadder_succ_equiv_con`), the
  ladder as a consistency progression at finite stages, along which some
  proof shortens by more than any computable function at every step
  (`explicitLadder_speedup`); and Chaitin's at
  `𝗥₀` (`chaitin_accreting_ladder`), its rung chosen by an epsilon like the
  hidden one, starting at any `Δ₁`-definable true extension of `𝗥₀`. The
  ladder couples to a growing host's own written code: under a padded commit
  schedule the theory at stage `n` is exactly the code held in the committing
  substrate's written region at the corresponding step, and stays held under
  every later one (`committedTheory_at_commitStep`,
  `ladderTheory_subset_committedTheory`). A fourth selector places Chaitin's
  sentence at each theory's own additive threshold — *Decoupling*
  Theorem 6.7's constant plus the theory's prefix complexity
  (`ChaitinPrefixLadder.lean`, `prefixChaitinSelector`) — and along its
  ladder the theory's enumerator gains at least one bit of prefix complexity
  per rung (`KB_enumeratorB_lt_succ`, `KB_enumeratorB_ge`), so no computable
  family names the ladder's theories uniformly
  (`prefixChaitinLadder_not_uniform`, in `PrefixEliasKB.lean`), on two facts
  about `KB` proved for the purpose: its invariance under computable maps,
  through the universal prefix machine as a code (`PrefixInvarianceKB.lean`,
  `univPrefix`, `KB_map_le`), and its Elias bound `KB n ≤ 2 · size n + c`
  (`KB_le_two_mul_size`). Registered as *Inevitability* Proposition 6.16 and
  Remarks 6.17 to 6.19, rows IN-54…IN-59. Boundary: the rate is in the prefix
  currency, none is stated in the syntactic size of the rungs, and no rung's
  Gödel number is computed; the two coordinates are stated side by side at
  one step index, no product update built; the commit stream is designed.

- **Levin's coding theorem on a universal prefix machine**
  (`PrefixMachine.lean`, `BitStringPrimrec.lean`,
  `AlgorithmicProbability.lean`, `CodingTheoremWeak.lean`,
  `CodingTheoremBitwise.lean`, `CodingTheoremDecoder.lean`,
  `KraftChaitin.lean`, `CodingTheorem.lean`): a description is a machine
  serialized by the self-delimiting `E` followed by a binary argument, the
  machine made prefix-free by stages (`pfy` — partial recursive uniformly in
  the machine, `pfy_partrec`, over a bit-string layer proved primitive
  recursive); the prefix complexity `KB` is Kraft-summable and below the
  additive `KE` by a constant; its algorithmic probability `QB` is
  lower-semicomputable (`QB_lsc`, a computable dyadic approximation rising to
  it). The theorem comes in two forms. With a logarithmic loss,
  `KB x ≤ k + 2·size k + C` whenever `2^{−k} < μ(x)`, for every
  lower-semicomputable semimeasure `μ` (`coding_theorem_weak`) — a
  self-delimiting header code (`gammaCode`), Markov's bound
  (`card_exceeds_lt`) and a partial recursive decoder with a prefix-free
  domain (`decodeFn`, `prefixFree_decodeFn_dom`), needing no online
  assignment. In Levin's `O(1)` form, `KB x ≤ k + C` (`coding_theorem`), with
  `2^{−KB} ≤ QB ≤ 2^C · 2^{−KB}` (`QB_le_two_pow_mul`): an online
  Kraft–Chaitin assignment carrying its invariant (`kcRun_invariant`) is fed
  the semimeasure's request stream, made total by dummy requests at its
  silent steps at the price of one bit. Each constant is a code's length,
  named rather than computed. Restated multiplicatively at a general
  semimeasure (`coding_theorem_mul`), the theorem makes `QB` a universal
  lower-semicomputable semimeasure — it dominates every one up to a constant
  factor (`QB_universal`), the hypotheses' joint satisfiability witnessed at
  the point mass (`QB_universal_nonvacuous`). Boundary: proved over one fixed
  universal prefix machine, where the classical text fixes its universal
  semimeasure as any maximal one — `QB` is *a* universal semimeasure, not a
  unique object.

- **The prefix machine's two textbook inequalities** (`PrefixPairKB.lean`,
  `PrefixModelCost.lean`): subadditivity, `KB (pair x y) ≤ KB x + KB y + c`
  (`KB_pair_le`) — one machine reads two descriptions back to back, the split
  unique because the universal machine's halting domain is prefix-free, and
  the pairing machine's own domain prefix-free in turn
  (`prefixFree_pairMachine_dom`), so no length header is paid — and the model
  cost, `KB x ≤ K_bitlen x + 2 · size (K_bitlen x) + c`
  (`KB_le_K_bitlen_add_two_mul_size`): a plain description made
  self-delimiting at the price of its own length written in the Elias code,
  which is *Discovery* §1.1's model-cost term read on the machine that section
  names. Boundary: constants are code lengths, named rather than computed; the
  converse at a constant factor is the index-cost bullet below, and neither
  additive form between the two currencies is settled.

- **Counting bounds, and the prefix machine's own uncomputability**
  (`PrefixCounting.lean`): a description budget of `L` bits buys at most
  `2^L` naturals, in both currencies and for unrelated reasons — on the
  prefix machine `KB` from its Kraft inequality, each member of the budgeted
  set contributing at least `2^{−L}` to a series bounded by one
  (`finset_card_KB_le`, `card_KB_le`), and on the bit-length measure
  `K_bitlen`, where no Kraft inequality holds, from injectivity into the
  indices below `2^L` (`finset_card_K_bitlen_le`, `card_K_bitlen_le`). Each
  count is stated twice: the `Finset` form carries the bound unconditionally,
  the `Set.ncard` form takes its content from the matching finiteness lemma,
  `ncard` reading `0` on an infinite set. The counts quantify both Chaitin
  theorems' "all but finitely many". And `KB` is uncomputable
  (`KB_not_computable`) by Berry's argument through the already-landed
  partial-map invariance rather than a Kleene fixed point: the search for an
  `s` of complexity above `n` is a partial computable map, its domain
  populated by `KB_unbounded`, priced by `KB_partial_map_le` and then by the
  Elias bound. Boundary: uncomputable, not un-enumerable — the graph of
  "`KB(s) ≤ n`" is computably enumerable (`rePred_kleB`); `2^L` is the best
  the Kraft hypothesis gives, a flat semimeasure attaining it, and the strict
  count `KB`'s own totality would buy is not stated; the two counts share
  a constant and nothing else.

- **The index cost of a description** (`IndexCost.lean`): the index
  bit-length of the least program computing `x` is at most a constant factor
  above its prefix complexity, `K_bitlen x ≤ 32 * KB x + c`
  (`K_bitlen_le_32_mul_KB`), by a balanced `Code.pair` nest over a minimal
  description's bits (`sizeLaw`, `nestSpec`) and one fixed decoder
  (`decoderSpec`). With `KB_le_K_bitlen_add_two_mul_size` it puts the two
  currencies within constant factors of each other; whether either additive
  form holds is open, the first exactly when the plain Kraft weight is
  summable (next bullet).

- **Prefix-complexity minimality** (`KraftMinimality.lean`): an
  upper-semicomputable `f` — `UpperSemicomputable`, a computable non-increasing
  stage sequence attaining `f` — has `KB ≤ f + c` for some `c` exactly when
  `∑ 2^(-f x)` is summable (`KB_le_add_iff_summable`), the coding theorem's
  minimality reading; the plain bit-length is upper-semicomputable
  (`upperSemicomputable_K_bitlen`), so the first additive form between the
  currencies is exactly the plain Kraft weight's summability
  (`KB_le_K_bitlen_add_iff_summable`), decided here in neither direction; the
  computable witness `2 * Nat.size` re-derives the Elias bound
  (`KB_le_two_mul_size'`).

- **The halting probability, and Chaitin's theorem on its approximations**
  (`HaltingProbability.lean`): the total algorithmic probability
  `haltingProb = ∑' x, QB x`, at most one (`haltingProb_le_one`), and the
  theorem stated at a pair rather than a binary expansion — there is a `c`
  such that whenever `m / 2 ^ n` is a lower approximation within `2 ^ (-n)`
  of it, `n ≤ KB (Nat.pair n m) + c`
  (`haltingProb_prefix_incompressible`), both hypotheses met at every `n`
  by the floor (`haltingProb_prefix_incompressible_nonvacuous`). A
  computable stage mass rising to the halting probability and a computable
  list of the values each stage reveals (`stageMass`, `revealedList`) meet
  two specifications (`HaltingMassSpec`, `HaltingRevealedSpec`), and the
  parent over any pair meeting them (`haltingProb_prefix_incompressible_of`)
  searches for the least stage past the *shifted* threshold
  `m / 2 ^ n − 2 ^ (-n)`, takes the least value not yet revealed, and prices
  it by `KB_partial_map_le`. Boundary: the pair, not a prefix of the
  expansion; the constant existential; no randomness or irrationality
  stated; the proof is Shen, Uspensky and Vereshchagin's Theorem 100, and no
  first-ness is claimed.

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
  *is* the noise count (`witMiss_zero`). The register's depth is an exact
  threshold (`LogMassEvent.lean`): from every power-of-two start inside the
  register a lifetime-free surprise bound over every stream with a
  never-missing candidate exists exactly when `C − 1 ≤ θ·(2^b + C − 1)`
  (`floorSurpriseFrom_bounded_iff`, the uniform start's own
  `floorSurprise_bounded_iff`), and from the uniform start it is then at most
  `C·b` (`floorSurprise_card_le_capacity`) — registered as *Discovery*
  Proposition 3.5, rows FV-37 and FV-38. Survival under corruption is proved,
  not assumed: `P` copies reading one stream leave one untouched under any
  schedule touching fewer than `P`, so the composite reads the base's own next
  state (`RedundantFiber.lean`), and the composite's decode is priced with `P`
  entering only through its numeral (`KE_compFrameFlat_le`); the touch bound's
  other side is a guard: two copies hit one per step with the same wrong
  leader installed, on a stream where that leader then misses three steps
  running, leave no verifying copy at those steps and are both recovered at
  the step after (`compRun_synchronized_guard`), so a schedule that touches
  every copy defeats the reading however small its rate. Boundary: the damage
  model is a **named hypothesis of the companion paper, not a theorem of this
  library** — `DamageGate.lean` states exactly what that costs: a
  host-applicable gate is provably empty on a noise-free stream, the
  eventually-quiet class (`QuietFrom`) closes host-checkable and lifetime-free
  at once, and the containment itself rides the identification
  `noiseGated_iff_witMiss`, not the mere existence of a finitely-firing event.
- **The register class: the capacity bound over every learner with its five
  properties** (`RegisterClass.lean`): a step of a level vector capped at `b`
  , driven by a miss vector with a truth that never misses, is in the class
  (`RegisterClass`) when at a rescale — some hitting candidate at the cap —
  the truth's level does not fall, no level rises and every missing candidate
  above the floor loses a level, when off a rescale the truth rises by exactly
  one and no level by more, and when the step keeps the run inside the
  register; the four step properties alone are `RegisterCore` . Over every
  member, every start inside the register, every stream on which the truth
  never misses and every threshold meeting the floor condition
  `C − 1 ≤ θ·(2^b + C − 1)` , the surprise count at every horizon plus `C`
  times the truth's start is at most `C·b` plus the competitors' start
  (`registerClass_card_add_le_capacity`, its hypotheses met at
  `registerClass_card_add_le_capacity_nonvacuous` ). The floored mixture is a
  member (`expStep_registerClass`), its run and surprise set the landed ones
  (`stepRun_expStep`, `stepSurpriseSet_expStep` ), and so is a reset learner
  whose missing candidates return to the floor at a rescale (`resetStep`,
  `resetStep_registerClass` ). The guard pair: the saturating register, which
  caps without a rescale, is not a member and its count is unbounded
  (`saturateStep`, `saturateStep_not_registerClass` ); and a step with the
  four properties that lifts a missing candidate out of the register is not a
  member and its count is unbounded (`liftStep`,
  `liftStep_registerCore_unbounded` ), so the fifth property is load-bearing.
  Registered as *Discovery* Proposition 3.6, rows FV-39 and FV-40; it extends
  *Discovery* Proposition 3.5(i) and *Inevitability* row IN-60 from one
  architecture to the class, and *Inevitability* §7 records it as a class of
  update rules at one bill, short of the class of architectures that section
  asks for. Boundary: the mass of a level is two to the level, fixed; the
  bound is not shown attained; nothing is stated of a truth that misses or of
  the description-length side.
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
- **The certified host as a tower's own rung** (`BlockPairTower.lean`): the
  same block-pair host re-read as the rung law of a `witnessWorld` tower — the
  habitat's blocks running the host's own update beside a free environment
  law — hosts that host as its guest's law-world exactly, surjectively and
  with a full margin at every depth (`tower_hosts_rung`, the landed
  `witness_world_hosts` instantiated, no new proof); loaded at the host's own
  certified state, the tower's outer reading is the host's own trajectory
  (`towerObs_eq_hostTraj`), so the schedule's pruning rule identifies the
  rung's true literal on the tower exactly as on the host
  (`tower_rung_identifies`). Registered as *Inevitability* Proposition 6.13,
  row IN-52. Boundary: finite; the rung's rule identified, not its update; no
  ownership clause (the rung law is not a permutation); level 2 cited from
  `hostWitness_overlap`, not composed onto the tower.
- **A second certified rung, and the differing-rules rung pair**
  (`ShiftedSpikeCriterion.lean`, `ShiftedSpikeHost.lean`,
  `ShiftedSpikeTower.lean`): the second certified word pair of
  `BlockPairProfile.lean` (`wordU2`, `wordV2`; length `22`, spike lag `6`),
  read as a Boolean observation (`designObs2`), meets the window-deviation
  profile at its own correlation bounds and identifies literal `2` under the
  schedule's pruning rule, with slack where the first host met the conditions
  with equality (`shiftedSpike_identifies`; the landed identification
  parametrized at an arbitrary literal, `schedSurvivors_eq_singleton_at`). A
  lag-`6` host carries it — the fresh window bit complementing cell `2` where
  the certified host's complements cell `0` — and its witness substrate
  reproduces the design along its own orbit (`readObs_iterate_loadHost2`);
  re-read as a tower's rung law, the schedule isolates literal `2` on the
  tower exactly as on the host (`towerWorld2`, `tower_rung_identifies2`). The
  capstone puts both rungs together (`descending_pair_commits`): two towers,
  two identified rules, `0` and `2`, differing, and equal to the entries of a
  two-entry stream (`literalStream`) that the committing substrate's
  `seqWrite` holds under every later step — the composition the single rung
  declined at a constant stream is a theorem at the first non-constant one.
  Registered as *Inevitability* Proposition 6.15, row IN-53. Boundary: two
  rungs in two towers, sequenced by the stream, not one tower descended
  twice; the decode identity is stated at stage `2`, the pair's own length;
  each rung's code-region literal is identified, not its update, and no
  ownership is claimed; the second host's route-class membership is
  deliberately not stated.

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
  width (`eventually_hosts_uniform_of_accreting_memWidth`). The width is
  read off a **root set**: a subset of a stage that is already an antichain
  and which every stage class reaches names the width exactly, with no
  hypothesis on the update (`memWidth_eq_encard_of_isRootAntichain`; at a
  state-level root set, `memWidth_eq_encard_of_rootSet`); a root antichain
  always exists at a finite stage (`exists_isRootAntichain_of_finite_stage`,
  classically), and under antisymmetry it is exactly the stage classes no
  other stage class reaches (`memWidth_eq_encard_canonical_of_antisymmOn`),
  each hypothesis pinned by a guard — the canonical set is empty at a finite
  world whose width is positive (`exists_canonicalSet_empty_pos_memWidth`),
  and the successor world on `ℤ` has positive width and no root antichain at
  all (`pos_memWidth_not_exists_isRootAntichain_intSucc`). Boundary: a
  separation, not a dichotomy — an antichain-shaped conservation guest can
  exceed the width (`exists_conservationGuest_extent_gt_memWidth`).
- **Derived worlds, and the width computed exactly at elementary cellular
  automata** (`DerivedStages.lean`, `ExtremeTapWidth.lean`,
  `FiniteWorldWidth.lean`): a world grown from a start region as its iterated
  images (`derivedStages`) has its retained profile, hence its memory width,
  capped by the region's own cardinality at every stage
  (`memWidth_derivedStages_le`), so a finite seed never supplies the
  certificate's crossing. On the finitely-supported configurations of the
  line, the extreme-tap linear rules — elementary tables `90` and `150`
  (`rule90`, `rule150`) — are additive and injective (`rule90_injective`),
  spread their support by exactly one cell per step at each end, and every
  nonzero orbit eventually leaves any fixed finite region
  (`rule90_region_exit`); on the world derived from an `n`-cell region, read
  at the region itself, their width is at least `2^(n−1)`
  (`memWidth_rule90_derived_ge`) and exactly the size of the **root set**, the
  region-supported states with no nonzero region-supported predecessor
  (`rootSet`, `memWidth_rule90_derived_eq`), a count that closes in addition
  form, `(rootSet rule90 n).encard + 2^(n−2) = 2^n + 1` at `2 ≤ n`
  (`rootSet_encard_add`). Both facts are generic in the update and in two
  endpoint-move constants (`memWidth_derived_eq_encard_rootSet`,
  `rootSet_encard_add_of_hyps`), the identity update the guard that separates
  them (`guard_id_rootSet_load_bearing`); a local table with a quiescent zero
  becomes a radius-one rule (`tableRule`), one-sided permutivity in solved
  form gives injectivity on that carrier
  (`tableRule_injective_of_leftPermutive`,
  `tableRule_injective_of_rightPermutive`), and four non-additive tables —
  `30`, `86`, `154`, `210` — meet the hypotheses and share the exact width,
  rule `30`'s equal to rule `90`'s (`memWidth_rule30_derived_eq_rule90`); the
  two shifts, tables `170` and `240`, carry their own width and count at their
  true endpoint moves (`memWidth_rule170_derived_eq`,
  `rootSet_encard_add_rule170`, `memWidth_rule240_derived_eq`), and a guard
  shows quiescence and permutivity alone do not pin the class-level spread
  (`guard_rule170_max'_spread_load_bearing`). At a finite carrier under the
  constant stage family the width is *Persistence*'s component count: the
  induced law is a bijection of the merge quotient (`mergeLaw_bijective`),
  reachability is symmetric (`reaches_symm`), and
  `memWidth_eq_nat_card_orbitSetoid` identifies the two counts — while the
  two-state swap shows the merge quotient is not the component quotient
  (`exists_finiteWorld_component_ne_merge_card`). Registered as *Guests*
  Propositions 7.14–7.21, rows GV-22…GV-29. Boundary: the counts are additive
  (`ℕ∞` subtraction is truncated), the closed forms being the paper's
  restatement; the permutivity-to-injectivity route is classical; the
  finite-world identification relates counts, not capacities; the derived
  cap says nothing about attainment beyond the tables named.
- **The growing width: six catalogue rules accrete, the identity does not**
  (`GrowingWidth.lean`, `LightConeWidth.lean`): the memory width restricted to
  the states whose orbit has unbounded size (`GrowingPart`, `growingWidth`) —
  the part invariant and merge-saturated (`growingPart_of_merge`), the
  restricted family advancing (`advances_growingPart`), the width monotone and
  below the plain one (`growingWidth_mono`, `growingWidth_le_memWidth`), and a
  genuine restriction: `0` against `t + 1` at the identity
  (`growingWidth_id_slowClock_eq_zero_memWidth_eq_succ`). Under the support
  diameter (`diam`) and along the light cone of an `n`-cell window
  (`lightCone`), an update with exact endpoint moves `(1, 1)` has the nonzero
  states as its growing part (`growingPart_eq_ne_zero`), and with a trivial
  kernel and injectivity its growing width is at least `2^(n+t−1)`
  (`two_pow_le_growingWidth_lightCone`), hence unbounded
  (`growingWidth_lightCone_unbounded`) — instantiated at tables `30`, `86`,
  `90`, `150`, `154`, `210` (`growingWidth_lightCone_unbounded_rule30`, …),
  jointly satisfiable at rule `90`, and `0` at the identity and both shifts
  (`growingWidth_lightCone_id_eq_zero`,
  `growingWidth_lightCone_rule170_eq_zero`). The plain width along the same
  cone is unbounded even at the identity, so this is the quantity that sees
  the rule. Registered as *Guests* Definition 7.22 and Proposition 7.23, rows
  GV-30 and GV-31. Boundary: a lower bound, not the value; the rate is the
  presentation's; the diameter is one reading of size; the part is not
  decidable in general; a separation at a hypothesis class, not genericity.
- **The growing width over the whole radius-one rule space: an engine without
  injectivity, and a bracket at the table bits** (`EndpointClasses.lean`): an
  antichain of the retained profile is a set of states with pairwise disjoint
  forward orbits, so at exact endpoint moves `(a, b)` with `a + b ≥ 1` on any
  update-invariant set containing every translate of one state, the
  translates in the light cone are pairwise orbit-disjoint and each is
  growing — the growing width is at least `n + 2t + 1 − diam s₀`
  (`linear_le_growingWidth_lightCone_of_invariant`), hence unbounded
  (`growingWidth_lightCone_unbounded_of_invariant`), with the six hypotheses
  jointly met at table `202` on the right end-word set
  (`growingWidth_lightCone_unbounded_of_invariant_nonvacuous`). The moves are
  read off a table's bits (`tableRule_min'_of_leftTap`,
  `tableRule_max'_of_rightHold`, `tableRule_max'_of_endsOneOne`, …), every
  quiescent table advances the cone (`advances_lightCone_tableRule`), and a
  non-increasing diameter empties the growing part
  (`growingPart_eq_empty_of_diam_le`). Two classes of tables, each a
  disjunction of bit equations: `AccretesByEndpoints` — unbounded growing
  width at every member (`growingWidth_lightCone_unbounded_of_accretesByEndpoints`),
  `52` of the `128` quiescent tables (`card_accretesByEndpoints`,
  `card_quiescent`) — and `ZeroByEndpoints` — width identically `0`
  (`growingWidth_lightCone_eq_zero_of_zeroByEndpoints`), `48` tables
  (`card_zeroByEndpoints`) — disjoint
  (`accretesByEndpoints_zeroByEndpoints_disjoint`). Registered as *Guests*
  Proposition 7.24, rows GV-32 and GV-33. Boundary: the bound is linear where
  the six-table one is exponential; the `28` tables in neither class are not
  decided in either direction; the counts are kernel decisions over the
  256-element table type; the instances at rules `90` and `150` are at tables
  written out here, with no stated identity to `rule90` and `rule150`.
- **The observed column settles wherever the diameter never grows**
  (`ObservedColumn.lean`): the column an observer reads at one cell along an
  orbit (`observedColumn`) is eventually periodic at every quiescent table
  whose diameter never grows (`eventuallyPeriodic_observedColumn_of_diam_le`)
  — the pattern up to translation ranges over a finite set, so it recurs
  with a drift, and the column is periodic at zero drift and eventually `0`
  otherwise — hence at every zero-class table
  (`eventuallyPeriodic_observedColumn_of_zeroByEndpoints`); contrapositively
  a column that is not eventually periodic forces the diameter to grow at
  some stage of that seed's own orbit
  (`exists_diam_lt_iterate_of_not_eventuallyPeriodic`). The hypotheses are
  met at the shift `170` with its center column written out
  (`observedColumn_f170_single`), and the diameter hypothesis is load-bearing
  at rule `30` (`diam_lt_tableRule_f30_single`). The converse fails at a
  checked witness: rule `90` is in the accreting class and its single-seed
  center column is `1` then `0` forever (`observedColumn_f90_single`).
  The rational ray at speed `p/q` reads the cell `e + ⌊pt/q⌋` at step `t`
  (`observedRationalRay`), the column at speed zero
  (`observedRationalRay_zero`); at every quiescent table whose diameter never
  grows every rational ray is eventually periodic
  (`eventuallyPeriodic_observedRationalRay_of_diam_le`), reading one relative
  cell of the drifting pattern for ever when its speed is the drift and zero
  for ever otherwise, hence at every zero-class table
  (`eventuallyPeriodic_observedRationalRay_of_zeroByEndpoints`), the
  hypotheses met at the shift at speed one half
  (`eventuallyPeriodic_observedRationalRay_of_diam_le_nonvacuous`). The
  column's statements are registered as *Guests* Remark 7.25, rows GV-34 and
  GV-35, the rational ray as *Guests* Proposition 7.28, row GV-40. Boundary:
  existence of a
  period only, no bound on it or on the onset; one column or ray, not the
  configuration; beyond that one column of rule `90`, this module says nothing
  about the column or any ray at a table whose diameter grows, rule `30`'s
  included.
- **Driven columns: what settles at every table, and a column that never
  does** (`DrivenColumns.lean`): a sequence in a finite type whose next
  value is, from some step on, a fixed function of its value and of an
  eventually periodic input is eventually periodic
  (`eventuallyPeriodic_of_driven`). Over the table rules this gives, at
  every quiescent table and every finitely-supported state: a window of
  adjacent cells is eventually periodic exactly when the columns at its two
  end cells are (`eventuallyPeriodic_observedWindow_iff`), so the columns
  between two settled columns settle
  (`eventuallyPeriodic_observedColumn_between`); and the rays that move one
  cell a step, in either direction and from every start cell, are
  eventually periodic (`eventuallyPeriodic_observedRay_one`,
  `eventuallyPeriodic_observedRay_neg_one`). At rule `90`, `2^j` steps of
  the rule send a state `s` to `i ↦ s(i − 2^j) + s(i + 2^j)`
  (`iterate_two_pow_f90`), and the single seed's column at cell `1` is not
  eventually periodic
  (`not_eventuallyPeriodic_observedColumn_f90_single_one`): it is live at
  every step `2^(j+1) − 1` and dead strictly between
  (`observedColumn_f90_single_one_live`,
  `observedColumn_f90_single_one_dead_between`). One settled end does not
  settle the cell beside it
  (`eventuallyPeriodic_observedColumn_between_guard`), and the rays'
  statement fails at velocity zero
  (`not_eventuallyPeriodic_observedRay_zero_f90`). Registered as *Guests*
  Proposition 7.26, rows GV-36 and GV-37. Its column at cell `1` is also
  one equality, live exactly at the steps `t` with `t + 1 = 2^j` for some
  `j ≥ 1` (`observedColumn_f90_single_one`), and the driven interior's
  hypotheses are met together at the shift
  (`eventuallyPeriodic_observedColumn_between_nonvacuous`). Boundary:
  existence of a period only; velocities `1` and `−1` only; nothing about
  any other column of rule `90`, any other seed, or any column of another
  accreting table.
- **The hindsight count: a law on the last readings, and what bounds its
  misses** (`HindsightCount.lean`): a sequence is eventually exact at memory
  `k` when one fixed function of its last `k` readings gives the next
  reading from some step on (`EventuallyExact`). An eventually periodic
  sequence is eventually exact at some memory
  (`eventuallyExact_of_eventuallyPeriodic`), and over a finite alphabet the
  converse holds (`eventuallyPeriodic_of_eventuallyExact`), the two together
  one equivalence (`exists_eventuallyExact_iff_eventuallyPeriodic`); the
  finite alphabet is load-bearing, the identity on the naturals being
  eventually exact at memory one and not eventually periodic
  (`eventuallyExact_nat_id_not_eventuallyPeriodic`). The hindsight count at
  a horizon is the fewest misses any such function makes before it, the
  minimum taken at each horizon separately (`lawMisses`, `hindsightCount`);
  over a finite alphabet it is bounded in the horizon exactly when the
  sequence is eventually exact at that memory
  (`hindsightCount_bounded_iff_eventuallyExact`), and bounded at some memory
  exactly when the sequence is eventually periodic
  (`exists_hindsightCount_bounded_iff_eventuallyPeriodic`). At every
  quiescent table and every finitely-supported state, a window of adjacent
  cells meets either condition at some memory exactly when the columns at
  its two end cells do, each at a memory of its own
  (`exists_eventuallyExact_observedWindow_iff`,
  `exists_hindsightCount_bounded_observedWindow_iff`). Over a finite family
  of such functions at one memory, a bound on one member's misses bounds the
  floored mixture's surprise count free of the horizon
  (`floorSurprise_card_mul_le_of_lawMisses_le`, the bound
  `floorSurprise_card_mul_le_missCount` at the family's miss matrix
  `lawMissMatrix`; its two hypotheses are met together at
  `floorSurprise_card_mul_le_of_lawMisses_le_nonvacuous`, over `nvX` and
  `nvLs`). At rule `90` from the single seed the center column is eventually
  exact at memory zero (`eventuallyExact_observedColumn_f90_single`) and the
  column at cell `1` at no memory
  (`not_exists_eventuallyExact_observedColumn_f90_single_one`), its
  hindsight count unbounded at every memory
  (`hindsightCount_observedColumn_f90_single_one_unbounded`). The two are the
  two sides of one class statement: at every table of the zero class, from
  every finitely-supported state and at every cell, some memory gives the
  column's hindsight count a bound in the horizon
  (`exists_hindsightCount_bounded_observedColumn_of_zeroByEndpoints`), and so
  for every window of adjacent cells
  (`exists_hindsightCount_bounded_observedWindow_of_zeroByEndpoints`), both
  hypotheses met at the shift `170`
  (`exists_hindsightCount_bounded_observedColumn_of_zeroByEndpoints_nonvacuous`);
  and the class hypothesis is load-bearing, rule `90` lying in the accreting
  class with its cell-one count unbounded
  (`exists_hindsightCount_bounded_observedColumn_zero_class_guard`) — the
  observer's bill read against the world's growth, bounded wherever the world
  does not accrete. The two window statements are registered as *Guests*
  Proposition 7.27(i), row GV-38; the rest is registered in no paper and
  extends *Guests* Propositions 7.24 and 7.26 and the event bound of
  *Inevitability* row IN-13. Boundary: the memories and the
  bounds on the two sides of an equivalence are separate existentials, none
  given in terms of another; no rate of the count is stated; the class
  statement says nothing at the twenty-eight tables in neither class; the
  mixture bound
  is on the count times the threshold and says nothing at threshold zero.
- **The margin a cell's reading allows** (`LocalMargin.lean`): a function of
  a state reads only a finite set of cells when its value is fixed by them
  (`ReadsOnly`), and holds within `e` at a state when every state differing
  from it at no more than `e` cells gives the same value (`HoldsWithin`). If
  a function reads only `N` and takes different values at two states, the
  two margins at which those values hold sum to less than the number of
  cells of `N` at which the states differ
  (`margins_add_lt_card_of_readsOnly`), the packing inequality of *Guests*
  Law 4 read at what one cell reads; the bound is met with equality on three
  Boolean cells at margins one and one
  (`margins_add_lt_card_of_readsOnly_nonvacuous`), and the inequality fails
  at an instance meeting every hypothesis but that one, at margins one and
  one against a set of one cell (`margins_add_lt_card_guard`). A radius-one
  table's value at a cell after `τ` steps is fixed by the cells within `τ`
  of it (`tableRule_iterate_apply_congr`), so on finitely-supported states
  the margins at which its `τ`-step iterate erases (`ErasesAt`) sum to at
  most `2τ` at two states with different successors
  (`tableRule_margins_add_le_two_mul`, its hypotheses met together at
  `tableRule_margins_add_le_two_mul_nonvacuous`). On all functions of the line
  (`lineRule`, `ErasesWithin`), at a table fixing both constant states: at no
  scale do both erase within two (`not_erasesWithin_two_const`), and at every
  positive scale both erase within one exactly when the table is the majority
  of its three cells (`erasesWithin_one_const_iff`, `majTable`,
  `erasesWithin_one_const_majTable`); the zero state alone can erase within
  two (`erasesWithin_two_const_zero_guard`). At scale one, at every table and
  on all functions of the line, two states each erasing within two have the
  same successor (`lineRule_eq_of_erasesWithin_two`), the two hypotheses met
  at two different states of the constant-zero table
  (`lineRule_eq_of_erasesWithin_two_nonvacuous`); at the majority table a
  margin of one at both constant states leaves the successors different
  (`lineRule_ne_of_erasesWithin_one_guard`). Registered in no paper; it
  extends *Guests* §3's one-step erasure and Law 4. Boundary: the witnesses
  and guards are existential statements, naming their margins and counts and
  not the function, table or state that meets them; the scaled bound's witness
  has one margin zero, so the bound `2τ` is not shown attained; beyond scale
  one nothing is stated about two states that are not constant, and nothing at
  any scale about a table of wider radius or more states, or about whether two
  finitely-supported states can both hold a positive margin.
- **A window's count against its ends'** (`WindowCount.lean`): the hindsight
  count of a reading is the fewest misses, over the functions of the last
  `k` states, in answering a fixed function of the next state
  (`readingMisses`, `readingCount`); at the identity it is the hindsight
  count (`readingCount_id`). A reading's count is at most the state's
  (`readingCount_le_hindsightCount`), and at most the count of the read
  sequence taken on its own (`readingCount_le_hindsightCount_comp`). At
  every quiescent table, every finitely-supported state, every window, every
  memory of at least one and every horizon, the window's hindsight count is
  at most the sum of the counts of its two end cells read with the window as
  context (`hindsightCount_observedWindow_le_add_readingCount`), hence at
  most the sum of its two end columns' hindsight counts
  (`hindsightCount_observedWindow_le_add_columns`); by the first comparison
  it is at least each end reading's count. The memory is load-bearing: at
  memory zero the bound fails at the table that sends everything to zero
  (`hindsightCount_observedWindow_zero_memory_guard`). The end columns' own
  counts give no lower bound: at the shift, a window of two cells has no
  miss in three steps at memory one while the column at its first cell has
  one (`hindsightCount_observedWindow_lt_column_f170`). The translating window
  at a rational speed `p/q` of at most one, read with the phase `t mod q` of
  its own schedule (`movingWindow`), has at every quiescent table, every
  finitely-supported state, every start, every width of at least three, every
  memory of at least one and every horizon a hindsight count at most the sum
  of its two end readings' counts, the trailing end's the cell it sits on and
  the leading end's the two cells it sits on and moves to
  (`hindsightCount_movingWindow_le_add_readingCount`), the hypotheses met at
  table `90` at speed one half
  (`hindsightCount_movingWindow_le_add_readingCount_nonvacuous`) and the
  memory load-bearing at the zero table, where a memory-zero law cannot follow
  the phase (`hindsightCount_movingWindow_zero_memory_guard`). The window at
  rest is registered as *Guests* Proposition 7.27(ii)–(iii), row GV-39; the
  translating window is registered in no paper. Boundary: both sides of each
  bound are at the same memory and horizon; no bound is stated at memory zero,
  none for a window whose ends move at different speeds or at a speed above
  one, and each guard is a single instance.
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
  (`exists_candidate_capacity_le`). The cap also holds uniformly over label
  alphabets, as a bound on `CbHs` itself (`CbHs_collapse_uniform`, and
  `CbHs_collapse_uniform_growing` at a growing world): every pair normalizes
  to the later carrier's alphabet by a first-occurrence rank — orbit sizes
  survive any post-composition injective on the frame's values
  (`orbit_postcomp_card_eq`) — and the normalized pair is priced as one
  object through a fixed extracted program (`rankBuilder`), so the count of
  affordable joint codes replaces the per-frame Kraft union. A telescope realizes any sequence of
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
