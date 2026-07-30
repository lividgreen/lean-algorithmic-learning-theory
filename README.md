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
guard that fails the build if it ever drifts.

**Start here:** the [**API reference**](https://lividgreen.github.io/lean-algorithmic-learning-theory/)
is generated from the source and is the best way in — every definition and
theorem below is a click away, with its statement and its dependencies. A few
entry points, if you want a sense of the range before reading the list:

| | |
|---|---|
| [`Ville.lean`](https://lividgreen.github.io/lean-algorithmic-learning-theory/docs/ALT/Ville.html) | Ville's inequality — the anytime-valid tail bound Mathlib does not carry |
| [`SQEnvelope.lean`](https://lividgreen.github.io/lean-algorithmic-learning-theory/docs/ALT/SQEnvelope.html) | statistical-query learning, to our knowledge the first such formalization in any prover |
| [`DecisionListSolver.lean`](https://lividgreen.github.io/lean-algorithmic-learning-theory/docs/ALT/DecisionListSolver.html) | a learner verified **correct *and* polynomial-step**, against a cost model built here |
| [`Decoupling.lean`](https://lividgreen.github.io/lean-algorithmic-learning-theory/docs/ALT/Decoupling.html) | when a model a system holds of itself survives the system running |
| [`GodelThreshold.lean`](https://lividgreen.github.io/lean-algorithmic-learning-theory/docs/ALT/GodelThreshold.html) | the capacity threshold at which self-representation turns into incompleteness |

## What is proved here

- **Ville's inequality** for non-negative supermartingales (`Ville.lean`) —
  the all-time tail bound anytime-valid inference is built on; absent from
  Mathlib (whose Doob maximal inequality is submartingale-only).
- **Statistical-query learning** — to our knowledge the first SQ formalization
  in any proof assistant (`SQObjects.lean`, `SQEnvelope.lean`, …): the
  statistical dimension with its separated-subfamily characterization
  definitional, a survivor pigeonhole, a *linear* version-space envelope under
  2τ-identifiability (Szörényi's maximality argument), and parity's `2^n`
  SQ-dimension lower bound derived from character orthogonality.
- **A prequential-MDL discovery chain** (`BayesRedundancy.lean`,
  `DeterministicDiscovery.lean`, `ExtensionalDiscovery.lean`,
  `SQAlgorithm.lean`, …): posterior concentration for realizable deterministic
  prediction, qualitative concentration on the on-trajectory equivalence class
  (rate provably uncomputable), pruning soundness, exact predictive-transfer
  bounds, and the pruned-algorithm discovery theorem.
- **A two-currency cost model** for `Nat.Partrec.Code` — Mathlib's
  fuel-indexed `evaln` bounds values, not resources. Sequential steps and
  workspace bit-width (`TimeCost.lean`), extended to unbounded search by
  genuinely partial evaluators whose domain is exactly `eval`'s
  (`SearchCost.lean`, `SearchSpace.lean`), with a per-constructor family of
  workspace bound laws — recursion and search enter as a `max` over their
  steps, never a sum (`CapacityBoundedEval.lean`) — and a bounded-enumeration
  workspace bound independent of the enumeration's length
  (`CheckerWorkspace.lean`). The step model carries a greedy decision-list
  learner verified **both correct and `poly(m,k)`-step**
  (`DecisionListSolver.lean`); we believe this is the first learning algorithm
  mechanically verified for correctness and complexity at once.
  Honest boundary: time is unit-cost AST steps (arithmetic is value-linear,
  hence the solver's binary bit-gate setting); space is value bit-width.
- **A priced universal interpreter** (`BoundedInterp.lean`, `CodeArith.lean`,
  `CodePacking.lean`, `UniversalAt.lean`): a small-step interpreter for
  `Nat.Partrec.Code` on configuration numerals, proved sound *and* complete
  against `Code.eval`, then realized as an explicit code and priced —
  `UniversalAt`: the reference dynamics runs within workspace *affine in the
  run's own configuration width*. Universality with a constructor skeleton,
  where the usual universal witness is a bare existence statement nothing can
  price.
- **Persistence capacity** (`Decoupling.lean`, `PersistenceCapacity.lean`):
  the Decoupling Lemma — a faithfully decoded model persists iff the update
  is read-only on its region — and the exact price of evading it with
  time-dependent decoders (lens families, unconstrained, so the bounds are
  absolute). Persistable content is measured by the recurrent core —
  irreversibility, not overwriting, is what obstructs memory; static capacity
  never exceeds moving capacity, and the gap can be total (rotation: zero at
  a fixed address, the whole memory moving); a maximal moving family's first
  two frames determine the world's recurrent rule (`ledger_K` — the
  complexity is relocated into the decoder, not vanished); a robustness
  margin is paid for in carried content (`repair_tax`, with three-copy
  majority voting saturating the bound exactly); and sub-systems hosting
  sub-systems compose squares with added budgets — stacking buys structure,
  never generic capacity (`tower_no_free_lunch`).
- **A realizability (assembly) category over Kleene's first algebra**
  (`Realizability*.lean`, `CapacityLayer.lean`, `RealizerLength.lean`, …):
  Cartesian closed with finite coproducts, a subobject classifier and
  equalizers on the finite fragment (`RealizabilitySubobject.lean`), a
  depth-bounded recursor as an object, a capacity filtration with non-closure
  in both cardinality and realizer length, and a discriminating
  initial-algebra characterization of the bounded recursor under which
  **Lambek's lemma provably fails**. On top: the structural category of
  decoupled learners with capacity-respecting simulations
  (`DecoupledSimulation.lean`), realizer transport priced in both
  program length and workspace (`GradeTransport.lean`), a capacity-graded
  exponential with priced application and two-way graded transport
  (`GradedApplication.lean`, `GradedConjugation.lean`, `GradedSimulation.lean`),
  and a build-enforced boundary: the represent-but-cannot-derive phenomenon is
  re-exported over an import closure from which the exponential object is
  *absent*, so "no function space is needed" is machine-enforced rather than
  observed (`MinimalityWitness.lean`).
- **Evolution in a skew-product fiber** (`SkewFiber.lean`,
  `WeightedFiber.lean`, `QuantizationRate.lean`): a skew product is priced by
  its ingredients' codes plus a constant, with nothing scaling in the state
  count; and a fiber whose state is a weight vector over candidate rules,
  updated by fitness-proportional selection, has an update that *is* Bayes'
  rule — normalizing the integer multiplicative step gives exactly the
  posterior, term for term, with no division, because the posterior depends on
  the weight vector only through its ray. What a finite carrier costs is then
  priced both ways: below an exactness horizon the finite run **equals** the
  exact Bayes run (the projection has nothing to do, and the horizon is sharp),
  and past it one generation stays within `4C/W` of the exact posterior in
  total variation. Honest boundary: no projection onto a finite carrier is a
  replicator step, the residual does not telescope over a run, and no
  accumulated bound is claimed.
- **A surprise budget, and decoupling on a growing code region**
  (`SurpriseBudget.lean`, `AccretiveDecoupling.lean`): an unconditional bound
  on how often a prequential mixture is surprised, priced per event against a
  reading's robustness margin — and the formalization corrected the assembly it
  was built from, since a margin does *not* compose across consecutive
  perturbations: two independent structural conditions on the host each rescue
  it, and a small counterexample shows neither may be dropped. Separately, the
  decoupling equivalence holds verbatim on a monotonically *growing* code
  region, with an append-only witness on which the limit region is not
  read-only, so the statement does not reduce to one fixed partition.
- **A substrate class, and a capacity clause that is necessary**
  (`SubstrateClass.lean`): the prerequisites a bounded learner needs in order
  to reach the reflective threshold, as reusable objects — a decoupled
  substrate, a regularity regime, and reflective capacity — with the capacity
  clause machine-checked at the working recursor depth the threshold demands,
  placing the reflective object inside the capacity the host has left after its
  code region. The capacity requirement is proved **necessary** on an
  identified family of Gödel numbers, and proved *not* necessary on another;
  no general characterization is claimed. Also machine-checked: the regularity
  regime does not imply the capacity clause, a separation the informal
  presentation is easy to elide.
- **A dependency audit of the reflection chain**
  (`ChainDependencyAudit.lean`): which imports each conclusion actually
  consumes, with unused-binder marking so that "off the critical path" is
  compiler-certified rather than asserted — statistical-query learnability is
  off the path to bare representational reflection, while the steady-state
  per-step bound genuinely consumes retention. Purely structural: it proves no
  import, all edges being abstract propositions.
- **Window determinism, and a mixing hypothesis checked at both ends**
  (`WindowDeterminism.lean`, `BirkhoffTool.lean`): if each observation is
  exactly determined by the window of the previous `k` over a finite
  alphabet, the observation process is eventually periodic — and the initial
  window determines the whole trajectory, choice-free — so exact window
  sufficiency and quantitative mixing cannot coexist on a finite alphabet.
  On the mixing side, the `MixingHoeffding` rate hypothesis is pinned at both
  ends: a *theorem* at the i.i.d. end (the spectral-gap constant at one
  recovers the independent Hoeffding bound exactly), a vacuity guard at
  non-positive constants (the bound then asserts nothing, for every law and
  target), and genuine refutability at every positive constant — so the
  constant is where the hypothesis's content lives, stated rather than
  implied. The window-noise pruning budget now reaches the single-trajectory
  route, not only the i.i.d. ensemble. And a first genuinely **dependent**
  instance is derived (`NoisyWindowChain.lean`, engine in `ParityWalk.lean`):
  the Bernoulli-noise window chain satisfies the rate at the named constant
  `4·k` for coordinate observables, at every noise rate — no `1/η`, the
  relevant eigenvalue being negative, so consecutive time-averages cancel
  rather than accumulate. Honest boundary: multi-coordinate queries see a
  positive eigenvalue and a genuinely noise-dependent constant, not bounded
  here; the general spectral-gap theorem stays unproved.
- **A sound bounded checker, and a classical sound-and-complete bounded
  decision** (`GodelChecker.lean`, `GodelCheckerComplete.lean`): two separate
  artifacts, not one — an *executable* sound bounded proof-checker, and a
  *noncomputable* classically-packaged sound-and-complete bounded
  non-provability decision (Foundation ships no `Decidable` instance for its
  own proof relation, so no single artifact here is both computable and
  complete), axiom-clean for the finite theory PA⁻, with incompleteness
  discharged against
  [FormalizedFormalLogic/Foundation](https://github.com/FormalizedFormalLogic/Foundation);
  run by a two-cell decision automaton over the executable checker, whose
  code cell is read-only — the sentence under test persists by the
  Decoupling Lemma while the work cell drives to the Gödel verdict
  (`ReflectiveAutomaton.lean`, executable at the PA⁻ Gödel sentence in
  `GodelCheckerAutomaton.lean`).
- **An expressiveness excess order** (`ExcessOrder.lean`,
  `ExcessOrderComplete.lean`): representational classes graded by work-bit
  budget, with inclusions strict exactly as the budget grows; an
  internalization threshold packaged as a predicate on the budget; and the
  capstone at Foundation's finite `𝗣𝗔⁻`: a cheaply-owned guest that carries
  its host's law and represents a true-but-underivable sentence, the
  incompleteness antecedent discharged rather than hypothesized
  (`witness_outgrows_paMinus`).
- Supporting infrastructure: prefix-complexity semimeasure (`∑ 2^{−KP} ≤ 1`),
  an additive self-delimiting program-length measure with a length-efficient
  binary constant, binary index-form Kraft–McMillan bridges
  (`BinaryKraft.lean`), the commitment step's selector — provably unique,
  true under the discovery hypotheses, and time-stable
  (`CommitmentSeam.lean`), finite-case information theory (DPI, Fano), and an
  integrated port of the **pointwise Birkhoff ergodic theorem** (from
  [lua-vr/pointwise-birkhoff](https://github.com/lua-vr/pointwise-birkhoff),
  Apache-2.0 — see NOTICE).

## Verification standard

- No `sorry`, `admit`, or `native_decide`; standard axioms only
  (`propext`, `Classical.choice`, `Quot.sound`) — several cores are
  choice-free, and the structural capstone depends on no axioms at all.
- **Build-enforced axiom hygiene**: 689 `#guard_msgs in #print axioms` guards
  assert each capstone's exact axiom set; `lake build` fails on any drift.
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
meant to be opaque, characterized by their exported `val_`/`tc_` lemmas rather
than by their syntax trees. So `OneDL.ExistsConsistentDL` is public because it
*is* what `OneDL.solve_decides` claims, while `OneDL.cSolve` is public as a
cited object whose internals are not.

One further reason is not mechanical and so is not recomputed: a declaration
that a module's own docstring presents as a **main result** stays public even
when nothing in the list above consumes it — a paper's headline statement should
be reachable whether or not another theorem happens to need it. So the public
surface is the closure of rules 1–5 *plus* those advertised results, and it is
deliberately a little wider than what the machine can derive.

What the machine does enforce is that it never grows by accident: the closure is
recomputed against the compiled environment and ratcheted per module, so the
surface can narrow freely, while widening it requires an explicit, recorded
decision rather than a silent drift.

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

## Papers

The development machine-checks the load-bearing results of a companion series
of papers on bounded learners in deterministic environments. Docstrings cite
the series by bracketed short-title keys: **[Decoupling]** (decoupling and the
categorical threshold for representational reflection), **[Discovery]** (MDL
dominance and finite-time rule discovery), **[SQ]** (polynomial-time
convergence under statistical queries), **[Persistence]** (resource-bounded
persistence capacity: the priced decoder), and **[Inevitability]** (the
realization-synthesis capstone: two independent routes to a reflective
subsystem, and the open problem of realizing both on one
witness) — so "[Discovery] §2.2" names a section of that paper. `FV-*` tags name
rows of the papers' formal-verification tables, mirrored by the axiom-audit
guard files, so a claim in a paper can be traced to the exact theorem that
carries it. Preprints are forthcoming — this README will link arXiv IDs as they
appear — and the development is described as a whole in a formalization paper
(in preparation).

The papers are what the library is *for*, but they are not needed to read it:
every module's docstring states what it proves and where its boundary is,
including what it deliberately does **not** claim.

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
