# lean-algorithmic-learning-theory

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.21284775.svg)](https://doi.org/10.5281/zenodo.21284775)

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
- **A step-counting cost model** for `Nat.Partrec.Code` (`TimeCost.lean`) —
  Mathlib's fuel-indexed `evaln` bounds values, not time — carrying a greedy
  decision-list learner verified **both correct and `poly(m,k)`-step**
  (`DecisionListSolver.lean`); we believe this is the first learning algorithm
  mechanically verified for correctness and complexity at once.
  Honest boundary: the measure is unit-cost AST steps, not bit-cost.
- **A realizability (assembly) category over Kleene's first algebra**
  (`Realizability*.lean`, `CapacityLayer.lean`, `RealizerLength.lean`, …):
  Cartesian closed with finite coproducts, a depth-bounded recursor as an
  object, a capacity filtration with non-closure in both cardinality and
  realizer length, and a discriminating initial-algebra characterization of
  the bounded recursor under which **Lambek's lemma provably fails**.
- **A bounded Gödel decision** (`GodelChecker.lean`,
  `GodelCheckerComplete.lean`): an executable sound bounded proof-checker and
  a sound-and-complete bounded non-provability decision, axiom-clean for the
  finite theory PA⁻, with incompleteness discharged against
  [FormalizedFormalLogic/Foundation](https://github.com/FormalizedFormalLogic/Foundation).
- Supporting infrastructure: prefix-complexity semimeasure (`∑ 2^{−KP} ≤ 1`),
  an additive self-delimiting program-length measure, finite-case information
  theory (DPI, Fano), and an integrated port of the **pointwise Birkhoff
  ergodic theorem** (from
  [lua-vr/pointwise-birkhoff](https://github.com/lua-vr/pointwise-birkhoff),
  Apache-2.0 — see NOTICE).

## Verification standard

- No `sorry`, `admit`, or `native_decide`; standard axioms only
  (`propext`, `Classical.choice`, `Quot.sound`) — several cores are
  choice-free, and the structural capstone depends on no axioms at all.
- **Build-enforced axiom hygiene**: 263 `#guard_msgs in #print axioms` guards
  assert each capstone's exact axiom set; `lake build` fails on any drift.
- To *genuinely* re-verify (guards only re-run on true elaboration), delete
  the project's compiled artifacts first:
  `rm -rf .lake/build/lib/lean/ALT*` then `lake build`.

## Building

Pinned toolchain (`lean-toolchain`, `lake-manifest.json`):

```bash
lake exe cache get   # fetch the Mathlib cache
lake build           # ~3 minutes of project elaboration on top of the cache
```

The library is `lake`-consumable as a dependency (package name `alt`,
library `ALT`):

```toml
[[require]]
name = "alt"
git = "https://github.com/lividgreen/lean-algorithmic-learning-theory"
rev = "v1.0"
```

## Papers

The development machine-checks the load-bearing results of a series of papers
on bounded learners in deterministic environments (preprints forthcoming; this
README will link arXiv IDs as they appear), and is described as a whole in a
formalization paper (in preparation).

## Citation and license

See `CITATION.cff` — archived releases: concept DOI
[10.5281/zenodo.21284775](https://doi.org/10.5281/zenodo.21284775)
(v1.0: [10.5281/zenodo.21284776](https://doi.org/10.5281/zenodo.21284776)). Code is Apache-2.0 (`LICENSE`); third-party attribution in
`NOTICE`. Developed by Mykola Palamarchuk (independent researcher), with
substantial AI assistance (Claude Code, Anthropic) under the author's
direction and review — every result is machine-checked by Lean and replayed
from a clean cache.
