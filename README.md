# lean-algorithmic-learning-theory

[![DOI](https://img.shields.io/badge/DOI-10.5281%2Fzenodo.21284775-blue)](https://doi.org/10.5281/zenodo.21284775)

Machine-checked **algorithmic learning theory** in Lean 4 + Mathlib — the
query-model, information-theoretic, and computational side of learning theory,
complementing the empirical-process/statistical side formalized in
[lean-stat-learning-theory](https://github.com/YuanheZ/lean-stat-learning-theory).

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
  (`CheckerScratch.lean`). The step model carries a greedy decision-list
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
- **A bounded Gödel decision** (`GodelChecker.lean`,
  `GodelCheckerComplete.lean`): an executable sound bounded proof-checker and
  a sound-and-complete bounded non-provability decision, axiom-clean for the
  finite theory PA⁻, with incompleteness discharged against
  [FormalizedFormalLogic/Foundation](https://github.com/FormalizedFormalLogic/Foundation);
  run by a two-cell decision automaton whose code cell is read-only — the
  sentence under test persists by the Decoupling Lemma while the work cell
  drives to the Gödel verdict (`ReflectiveAutomaton.lean`, executable at the
  PA⁻ Gödel sentence in `GodelCheckerAutomaton.lean`).
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
- **Build-enforced axiom hygiene**: 602 `#guard_msgs in #print axioms` guards
  assert each capstone's exact axiom set; `lake build` fails on any drift.
- **Targeted imports throughout**: every module names exactly the Mathlib
  files it uses — no monolith `import Mathlib`, one vendored port excepted —
  so the dependency surface is explicit and the build/docs closure stays
  proportionate to what is actually used.
- To *genuinely* re-verify (guards only re-run on true elaboration), delete
  the project's compiled artifacts first:
  `rm -rf .lake/build/lib/lean/ALT*` then `lake build`.

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
rev = "v1.2"
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
witness) — so "[Discovery] §2.2" names a section of that paper. `FV-*` tags name rows of the
papers' formal-verification tables, mirrored by the axiom-audit guard files.
Preprints are forthcoming — this
README will link arXiv IDs as they appear — and the development is described
as a whole in a formalization paper (in preparation).

## Citation and license

See `CITATION.cff` — archived releases: concept DOI
[10.5281/zenodo.21284775](https://doi.org/10.5281/zenodo.21284775)
— which always resolves to the latest version. This release is v1.2; its version
DOI is recorded here and in `CITATION.cff` once Zenodo mints it from the GitHub
Release. Code is Apache-2.0 (`LICENSE`); third-party attribution in
`NOTICE`. Developed by Mykola Palamarchuk (independent researcher), with
substantial AI assistance (Claude Code, Anthropic) under the author's
direction and review — every result is machine-checked by Lean and replayed
from a clean cache.
