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
system — abstract inhabitants that merely typecheck are ruled out by explicit
junk-satisfiability guards, which prove the class in question is satisfiable by
degenerate instantiations and so make the real witness's named ones the thing
that carries the content.

**Start here:** the [**API reference**](https://lividgreen.github.io/lean-algorithmic-learning-theory/)
is generated from the source and is the best way in — every definition and
theorem below is a click away, with its statement and its dependencies. A few
entry points, if you want a sense of the range before reading the list:

| | |
|---|---|
| [`Ville.lean`](https://lividgreen.github.io/lean-algorithmic-learning-theory/docs/ALT/Ville.html) | Ville's inequality — the anytime-valid tail bound Mathlib does not carry |
| [`SQEnvelope.lean`](https://lividgreen.github.io/lean-algorithmic-learning-theory/docs/ALT/SQEnvelope.html) | statistical-query learning, to our knowledge the first such formalization in any prover |
| [`DecisionListSolver.lean`](https://lividgreen.github.io/lean-algorithmic-learning-theory/docs/ALT/DecisionListSolver.html) | a learner verified **correct *and* polynomial-step**, against a cost model built here |
| [`DecisionListPredictor.lean`](https://lividgreen.github.io/lean-algorithmic-learning-theory/docs/ALT/DecisionListPredictor.html) | asking that learner twice decides what the surviving candidates agree on — or that they do not |
| [`Decoupling.lean`](https://lividgreen.github.io/lean-algorithmic-learning-theory/docs/ALT/Decoupling.html) | when a model a system holds of itself survives the system running |
| [`GodelThreshold.lean`](https://lividgreen.github.io/lean-algorithmic-learning-theory/docs/ALT/GodelThreshold.html) | the capacity threshold at which self-representation turns into incompleteness |
| [`LearningWitness.lean`](https://lividgreen.github.io/lean-algorithmic-learning-theory/docs/ALT/LearningWitness.html) | an explicit system that meets those prerequisites — built, not assumed to exist |

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
  Built over it, a **version-space read-off** (`DecisionListPredictor.lean`):
  extending the instance by the query point labelled each way and asking the
  verified solver twice **classifies** the surviving candidates — none consistent,
  all agreeing at the query (so the answer is forced, and it is returned), or
  two of them disagreeing — with its own explicit step bound. The agreement
  case is therefore detected rather than assumed, and the classification needs
  no restriction on the candidates' output labels: one predicting a non-label
  value has its deciding rule firing first on no example, so that label moves
  freely.
  A **second class** carries both theorems (`ConjunctionSolver.lean`,
  `ConjunctionPredictor.lean`): conjunctions over `k` Boolean features get
  their own poly-step consistency decider and the same forced-symbol read-off
  built over it. It is structurally cheaper — a conjunction's output is a bit
  by construction, so the relabelling argument the decision-list case needs is
  not ported — and it was built in a separate module against the solver's
  public API alone, with no `Code`-level bridge across the boundary, so the
  transfer between classes is exercised rather than asserted.
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
  Under those results sits a counting core with its decoder on top. A family
  read at any finite set of times is priced by one bijection per block of the
  joint partition its frames induce; where that itinerary is injective the
  world's own rule is the *unique* permutation consistent with the frames, not
  merely the count's witness; and one fixed program turns that count into a
  description of the world, built from the frame codes, the held times and an
  index into the consistent set (`FrameItinerary.lean`, over
  `ledger_itinerary` in `PersistenceCapacity.lean`). Declining a move up the
  pricing order costs at most twice the declined address, and exactly twice is
  attained — by an incompressible world read through its own canonical-form
  map with two fixed points merged — so that cap's constant is settled rather
  than bracketed (`CanonicalFormLens.lean`). Past the crossover where a lens's
  own address exceeds the fibre freedom it removes, "the composite is
  stronger" is **false**, by a double pigeonhole over an incompressible cycle
  read by position modulo `z` (`ExpensiveLens.lean`). And on the cyclic word a
  reading traces along an orbit, the positions where the word disagrees with
  its own `d`-shift are exactly the run boundaries of its `d`-decimation, at
  any alphabet and — averaged over starting points — with no condition on `d`
  whatever (`ReadingWord.lean`).
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
  count — and a `P`-fold blockwise population over one base is priced the same
  way, the population entering only through its binary numeral, so a fiber
  carrier exponential in `P` costs the base's code, *one* copy of the fiber's,
  and the numerals of `n₁` and `P` (`powFiber`,
  `KE_skewWorldFin_powFiber_le`), where iterating the binary product bound
  would have paid one copy's code `P` times; and a fiber whose state is a
  weight vector over candidate rules,
  updated by fitness-proportional selection, has an update that *is* Bayes'
  rule — normalizing the integer multiplicative step gives exactly the
  posterior, term for term, with no division, because the posterior depends on
  the weight vector only through its ray. What a finite carrier costs is then
  priced both ways: below an exactness horizon the finite run **equals** the
  exact Bayes run (the projection has nothing to do, and the horizon is sharp),
  and past it one generation stays within `4C/W` of the exact posterior in
  total variation. Which repairs such a host can offer is then settled
  negatively (`EvoAbsorption.lean`): the evolutionary step is *expansive*
  whenever selection does anything at all — one changed slot can flip the
  winner, and a flip moves every slot — one-step erasure fails inside the
  construction's own coverage regime rather than at its edge, and a robustness
  margin at a settled point forces that point's codeword to be the strict
  fitness maximum, so margin and full coverage cannot both hold once there are
  two candidates. Honest boundary: no projection onto a finite carrier is a
  replicator step, the residual does not telescope over a run, and no
  accumulated bound is claimed.
- **A surprise budget, and decoupling on a growing code region**
  (`SurpriseBudget.lean`, `AccretiveDecoupling.lean`): an unconditional bound
  on how often a prequential mixture is surprised, priced per event against a
  reading's robustness margin — and the formalization corrected the assembly it
  was built from, since a margin does *not* compose across consecutive
  perturbations, and a small counterexample shows a repair cannot simply be
  dropped. Three independent repairs are proved, and the third asks nothing of
  the host's dynamics at all: the host never separates two states, or it
  *erases* a bounded perturbation, or the reading is constant on a set closed
  under both the host and the damage — the last needing no Hamming distance, no
  finiteness and no margin, since the reading has nowhere to move to
  (`survives_of_invariant`). The erasure repair is in turn the minimum of a
  family: erasure within `T` steps, under a schedule whose hits land more than
  `T` apart, makes the damaged and undamaged trajectories *equal* outside the
  correction windows, so every reading agrees and no margin is consumed
  (`traj_eq_of_correctsWithin_of_spaced`), with the spacing hypothesis proved
  load-bearing by a host erasing within two steps and hit one step apart.
  Nothing is claimed *inside* a window, so the family contains the one-step
  condition rather than replacing it.
  A separate question is what a host that merely **settles** buys, and both
  halves of the answer are machine-checked. If damage keeps the run inside a
  basin every state of which settles, the damaged reading settles too
  (`settles_traj_of_settles`) — on the damage model's own finiteness, with no
  margin, no erasure and no condition on the reading, and with a purely
  dynamical form under a faithful decode whose host is read-only on its own
  ω-limit set (`settles_traj_of_readOnly`). But the reading stops changing
  without necessarily stopping at the *undamaged* value
  (`settles_traj_not_agreement`), and a host can erase every one-cell
  perturbation while its reading alternates forever (`corrects_not_settles`) —
  so settling is parallel to the three repairs rather than a fourth one, in
  both directions and on witnesses rather than on inspection. The three repairs
  themselves are pairwise independent but not jointly so: a host that both
  erases every `c`-perturbation in one step and never separates two memories
  has a **single recurrent state**, fixed — one update strictly shrinks the
  distance from an on-core state to any other, which the core's own permutation
  cannot absorb (`omegaLimit_subsingleton_of_corrects`) — and the third repair
  is then free (`survives_of_invariant_of_corrects`, which needs the erasure
  condition and that fixed point, not non-expansiveness). The boundary is
  guarded rather than described: at a radius reaching the whole memory, the
  only invariant reading is the one that distinguishes nothing
  (`joint_dependence_boundary`). Separately, the
  decoupling equivalence holds verbatim on a monotonically *growing* code
  region, with an append-only witness on which the limit region is not
  read-only, so the statement does not reduce to one fixed partition.
- **Growing worlds, an accreting witness with one sentence standing still, and
  a chain fed by its own growth**
  (`GrowingWorld.lean`, `AccretingWitness.lean`, `AccretingExcess.lean`,
  `GrowingComposite.lean`): a
  stage-indexed world whose update advances finite stages, with the guest of
  one closed under factors — the image stages advance under the guest's own
  law (`advances_guestStage`) — and the fixed-carrier intertwining square
  recovered at the constant family (`stagedSquare_const_iff`). The reading of
  a growing world must see the stage, and that is a theorem rather than a
  convention: over an append-only tape's full stages the stage-blind reading
  admits no guest law at all (`not_exists_stagedSquare_tapeDecode`), while the
  stage-aware reading closes the square with the write law as its own guest
  law. The accreting healer world — every block healed by the
  recursive-majority step, one zero codeword appended per step, the
  environment turning beside — hosts one guest from every state with no
  codeword hypothesis (`stagedSquare_accRead`), erases any perturbation of
  total weight under the healing radius in one step with the accretion inside
  the erased step (`accErasure`), and doubles its extent at every stage
  (`ncard_guestStage_accRead`). Above it, the `𝗣𝗔⁻` excess is proved
  uniform — one Gödel sentence, then every budget (`outgrows_paMinus_uniform`)
  — so the package (`accreting_outgrows_paMinus`) delivers a fixed
  true-but-underivable sentence hosted and represented at every stage past an
  explicit threshold stage (`eventually_hostsAt`, and that lemma is
  constructive). The composite closes the loop between a growing source and
  the noisy window chain: the chain's noise is no longer supplied from outside
  but emitted by the world's own growing state — the window steps on exactly
  the bit the tape records (`compUpdate`), and the orbit's window coordinate
  is the chain's own window process at the recorded word
  (`windowFst_iterate_compUpdate`). The stage-blind lesson recurs there: a
  reading of the window alone admits no guest law once the source's emitted
  bits ever differ (`not_exists_stagedSquare_windowOnly`), while the
  counter-including reading closes the square
  (`stagedSquare_compUpdate_counter`). Eventual periodicity transports between
  the source and its observation process in both directions
  (`eventuallyPeriodic_of_eventuallyPeriodic_obs`,
  `eventuallyPeriodic_obs_of_eventuallyPeriodic`), so the observation process
  of a source that is not eventually periodic never is either
  (`not_eventuallyPeriodic_obs_of_not`) — exactly the property whose forced
  presence traps every finite deterministic host
  (`not_mixingHoeffding_of_periodic_ne`), with the designed quiet source on
  the forced side as the contrast (`eventuallyPeriodic_obs_quietStream`). At a
  single fixed trajectory, the mixing hypothesis reduces to an explicit
  per-sample deviation bound at both horizons (`mixingHoeffding_dirac_iff`,
  `mixingHoeffdingTo_dirac_iff`), and a concrete decimated 3-automatic source
  is named with the guard instantiated at it (`mephisto`, `mephDecim`).
  Honest boundary: the family's description-length price is not
  formalized — no pricing statement appears in these modules — whether
  hosts accrete generically is untouched, and the named source carries no
  non-periodicity or convergence-rate theorem: its guard instantiation rests
  on two of its values differing, nothing more.
- **A block-pair sequence profile, exact at every period**
  (`BlockPairProfile.lean`): the cyclic autocorrelation of a two-word signed
  block concatenation decomposes exactly into within-block and boundary terms
  (`cyclicCorr_blockSeq`), so under two balance conditions on the block signs
  the correlation vanishes at a whole band of lags at **every** block count
  (`cyclicCorr_blockSeq_zone`) and equals a half-count multiple of the words'
  combined aperiodic correlation at the band's top lag
  (`cyclicCorr_blockSeq_spike`). The balance is supplied constructively: the
  Thue–Morse sign is balanced on every even range (`tmSign_balance`), and the
  prefix-product sign sequence built from it satisfies the transition equation
  through the cyclic wrap with both block-index classes summing to zero
  (`blockSign_transition_even`, `blockSign_transition_odd`). A certified pair
  of length-24 words (`wordU`, `wordV`) then yields, for every scale, a
  sequence of period a fixed multiple of that scale with exactly zero
  correlation at lags one through seven and a strictly negative value at lag
  eight (`blockSeq_wordU_wordV_correlation`). The correlations' partial sums
  are controlled as well: every prefix of a zone query is bounded by an
  explicit multiple of the word length, the top-lag query's prefix tracks its
  exact linear trend in integer-scaled form (`cyclicCorrPrefix_blockSeq_zone`,
  `cyclicCorrPrefix_blockSeq_spike`), and every cyclic window of arbitrary
  phase and length inherits both bounds (`cyclicCorrWindow_blockSeq_zone`,
  `cyclicCorrWindow_blockSeq_spike`), instantiated at the certified pair with
  explicit numerals (`cyclicCorrWindow_blockSeq_wordU_wordV_zone` and its
  spike sibling); behind them, the Thue–Morse partial sums are pinned at
  every bound (`tmSign_partial_odd`, `tmSign_partial_abs_le_one`). Honest
  boundary: this module is pure sequence combinatorics — nothing here ties
  these correlations to any observation process, no minimal-period or
  probabilistic statement is made, the window bounds carry the constants the
  proofs derive rather than the sharpest ones that hold, and the two words
  enter as literals with decided sums rather than from any characterized
  family.
- **A finite autonomous host that emits the certified sequence**
  (`BlockPairHost.lean`): a counter paired with the noisy window chain, the
  chain's tape computed from the counter by the certified sequence's own
  cyclic recursion (`designObs`, `hostTape`, `hostUpdate`). Started at the
  design's own window, the iterated state is a closed formula — the design's
  window and counter advance together (`hostUpdate_iterate_designWindow`) —
  so the sequence emitted along the orbit **is** the certified sequence
  (`hostUpdate_iterate_last`) and the designed state returns after one full
  period (`hostUpdate_iterate_period`). The return extends to **every**
  state: the window difference of two states sharing a counter evolves by a
  pure rotation of the window, independently of the tape
  (`windowXor_noisyStep`, `windowXor_hostUpdate_iterate`), and the rotation's
  order divides the period, so the whole state space decomposes into cycles
  of the full period (`hostUpdate_iterate_period_all`). The design's sign
  supply also gains a closed evaluation (`tmPrefix`, `blockSign_eq_tmPrefix`
  in `BlockPairProfile.lean`): the prefix product of the per-class
  Thue–Morse transitions collapses to a two-factor formula. Honest boundary:
  these are exact-orbit facts about a construction — *this module* states no
  statistical property of the emitted process and claims no substrate-class
  membership (the next two modules do), and the period statement is a return,
  its minimality carried by the counter coordinate rather than stated
  separately.
- **The emitted process concentrates, at every bounded query**
  (`BlockPairObservability.lean`): the host's own emitted sequence
  (`hostTraj`), read as the noisy window chain's observation process on the
  host's own tape (`hostTraj_eq_obs`), satisfies the single-orbit mixing
  bound over its uniform phase law (`phaseLaw`) — the empirical mean of any
  two-observation query concentrates on its stationary answer at a rate the
  module derives, for **every** bounded query weight, not only the character
  the correlation work pinned. Two ingredients make this exact rather than
  asymptotic: a general deviation-to-concentration lemma turning any uniform
  window bound into the mixing hypothesis at an explicit constant
  (`mixingHoeffding_of_deviation_bound`), and a single-site discrepancy bound
  for the certified sequence (`singleWindow_blockSeq_wordU_wordV_bound`) — the
  sequence is balanced over its period, so a bounded query's single-coordinate
  parts are controlled beside the correlation the profile module bounds. The
  schedule theorem (`mixingHoeffding_schedule`) delivers the bound at every
  offset the query class ranges over. Honest boundary: the constants are the
  ones the proofs derive, looser than the sharpest that hold; no probability
  beyond the deterministic phase law enters.
- **The finite host meets the learning prerequisites, from its own dynamics**
  (`BlockPairWitness.lean`): the certified host, embedded as a decoupled
  memory with a read-only code region, a window, and a binary counter register
  (`hostSubUpdate`, `loadHost`, `hostCodeRegion`), is a machine-checked member
  of the learning route-class `𝒮_L` (`hostWitness_substrateL`) — a finite,
  deterministic, autonomous machine, its observation process supplied by its
  own update rather than by an external noise source. The observability field
  is discharged by the concentration above, transported onto the substrate's
  own trajectory by a realization theorem (`hostSubstrateTraj_eq_hostTraj`,
  `readObs_iterate_loadHost`) — the reading off the memory along its own orbit
  *is* the emitted process, so every statistical clause is proved on the
  machine's own dynamics. Registered as *Inevitability* Theorem 5.8(a)(b),
  row IN-37. Honest boundary: a membership witness at named parameters — the
  numerals are the chain witness's, the constants are the ones the proofs
  derive, and the rule's cheapness is priced two bullets below rather than
  here.
- **The same host is a member of the emergence route-class too, at one update,
  one code region and one numeral set** (`BlockPairOverlap.lean`): the host's
  memory re-packed onto the numeral carrier the pricing machinery is indexed by
  (`hostPacked`), a frame reading the host's own counter register
  (`hostFrame`) that covers its whole target after one full pass from the loaded orbit's
  closed form alone (`hostFrame_surj_iterate`,
  `BlockPairWitness.readCounter_iterate_loadHost`), the growth clause at the
  emergence theorem's own shape — the guest carries its model from every
  initial state and is owned at the host's rule plus the frame, parametric in
  codes for both (`HostGrowsLawfulGuest`, `hostCarries`, `hostOwned`) — and the
  crossing clause at the standard the Witness World's own crossing uses, a
  Gödel size fixed once that every sufficiently large host's bit count hosts
  (`HostGrownGuestReachesThreshold`, `hostFrameBits_eventually_hostsAt`). So
  `hostWitness_substrateE` puts the host in `𝒮_E`, and `hostWitness_overlap`
  states both memberships together, from a common threshold on the host's
  size — the first `𝒮_E` inhabitant in this development, and the first system
  in both route-classes at once. Honest boundary: two hypothesis sets for
  *reaching* the threshold, nothing about survival (the host's core dynamics
  is a permutation, which bars a positive margin); the codes for the host's
  table and the frame are hypotheses here, as the emergence theorem's are
  (the next module exhibits them); no class-level statement relating the two
  route-classes in this module (the class-level form for this architecture is
  `TapeHostOverlap.tapeHost_overlap`, below); and it is registered as
  *Inevitability* Theorem 5.8(c), row IN-38 — the seam Theorem 5.1(c) leaves
  open, inhabited at a witness.
- **The host's rule as an exhibited program** (`BlockPairPrice.lean`): the
  packed host's own step, rewritten as arithmetic on the packed numeral —
  bit extraction by division and remainder, the decoded window bit, the tape
  bit from the design's sign and word supplies (the Thue–Morse sign as a
  bounded bit-sum, `tmSign_eq_tmBit`), the counter's increment modulo the
  period — proved primitive recursive and identified digit by digit with
  `hostPacked` (`hostStepNum_stateEquiv`), then tabulated and extracted from
  universality as one fixed program `hostBuilder` taking only `M` and the bit
  length of the period as numerals, with a twin `frameBuilder` for the counter
  frame. So the two tables are owned in the development's own currency at a
  fixed program plus logarithms (`KE_hostPacked_le`, `KE_hostFrame_le`), and
  the guest of the module above is owned within an absolute constant plus
  `O(log Π)` with no imported code parameter at all (`hostOwned_cheap`) —
  the emergence theorem's affordability input met by an exhibited program at
  a designed host that is not the Witness World. Honest boundary: description
  length, not computation time; the builders' own lengths stay symbolic
  constants, as every builder's do; registered at *Inevitability* Theorem
  5.8's boundary and row IN-39.
- **The seam at class level, for that architecture** (`TapeHost.lean`,
  `TapeHostObservability.lean`, `TapeHostWitness.lean`, `TapeHostOverlap.lean`,
  `BlockPairCriterion.lean`): the block-pair host with its observation sequence
  a parameter — the tape derived as agreement at lag eight, the window chain's
  step on it, the same orbit facts (`tapeUpdate_iterate_period_all` under
  `8 ∣ N`), the same substrate embedding — and a **profile** as hypotheses:
  single-site character sums bounded by `S` and pair sums at the scheduled
  offsets within `W a` of `n · ρ a`, at every phase and horizon. From the
  profile alone the two-offset queries deviate by at most `2S + W a`
  (`deviation_bound`), so the whole scheduled class mixes on the phase law at
  `(2S + W a)² / (2 ln 2)` (`mixingHoeffding_schedule`), and the host is a
  member of the learning route-class at any capacity clearing the code region
  plus the Gödel size's capacity (`tapeHost_substrateL`); the derived tape's
  density is tied to the sequence's own lag-eight correlation rather than
  declared (`tape_density`). Through the constructor below the same host is in
  the emergence route-class as well, and `tapeHost_overlap` puts every
  admissible sequence's host in both classes at one numeral set with the
  class's Gödel number identified with the crossing's — one Gödel size outside
  every period and sequence — once the period clears that size's capacity. The
  certified block-pair sequence is the instance (`designObs_profile` at
  `S = 56`, spike `−2/3` at lag eight, zone `0` elsewhere; the three definitional
  identities with the certified host; density `1/6` by `blockPair_density`;
  `blockPair_overlap_coupled`). Honest boundary: one architecture, parametric
  in the sequence, not a statement about hosts in general; a machine-checked
  inhabitant at every length `8r` (the family, in the next bullet); codes as
  hypotheses at class level; reaching, not survival by margin (every such host
  is a permutation of window-and-counter — the survival a member carries once
  a redundant fiber is added to it is the survival-witness bullet below); the
  crossing carries content only once the period clears the capacity, the
  membership holding vacuously below; the certified host's own registration
  (`hostWitness_overlap`) is untouched and has its two Gödel sizes uncoupled.
  Registered as *Inevitability* Proposition 5.9, rows IN-41 and IN-42.
- **A deterministic pace on that class** (`TapeHostSchedule.lean`, the instance in
  `BlockPairCriterion.lean`): on every host of the profile class the scheduled
  SQ oracle is exact within `τ` at every phase from an explicit horizon on —
  `scheduleOracle_deterministic`, one line off `deviation_bound`, with no tail
  bound and no measure — and the schedule's `2τ` pruning rule, stated as an
  object (`schedSurvivors`), leaves the true literal alone from horizon
  `⌊(2S + W_max)/τ⌋ + 1` on (`schedSurvivors_eq_singleton`,
  `identificationHorizon`), under the budget `2η ≤ τ`, cross-class trends
  bounded by `μ ≤ τ`, and the separation `3τ + μ ≤ 1` — every wrong literal
  pruned at its own query. The certified block-pair sequence identifies at
  `τ = 1/3` from every `n > 912` (`blockPair_identifies`). Those conditions are
  sufficient, not sharp: taking the error against each margin gives the
  two-sided **window** the schedule identifies in — every density
  `η < (1 − μ)/4` under the budget, and no admissible tolerance above `1/4`
  (`schedSurvivors_eq_singleton_sharp`, `not_identifies_of_gt_quarter`) — so
  `1/4` is the schedule's own limit. The profile class is a **family**, one host
  per length `8r` at density `1/(2r)`, the certified sequence its `r = 3`
  member (`BlockPairFamilyCriterion`, `designObsF_profile`). Honest boundary:
  this is the
  schedule learner of the *SQ* companion at the single-literal class, not the
  weighted fiber; a bounded pace in observation count and statistics per
  decision, nothing about physical time; nothing about survival; one
  architecture; registered as *Inevitability* Proposition 6.10, row IN-43.
- **The single witness's noisy-branch machinery on that class** (`TapeHostFiber.lean`):
  the fiber-facing stream of a profile-class host — its first eight bits the
  observation, then the tape — with the identity `hostTraj = obs 8 tapeStream`,
  so the learner-as-guest theorems of the paper's §6, all stated over an
  arbitrary stream, read on an autonomous host whose observability is its own:
  the true candidate's miss is the tape's own bit (`witMiss_zero_tapeStream`),
  the noise count is the profile's same-class pair sum and tracks `n·η` within
  `W₀/2` (`noiseCount_tapeStream_bounds`), the surprise budget's rate reads
  `28 + 16·(nη + W₀/2)` (`floorSurprise_rate_tapeHost`), and the host-side
  noise gate is a function of the host's own state — the bit it writes at the
  counter's next position — with absorption at any horizon whose gated count
  clears the redundancy (`noiseGated_tapeStream_iff`,
  `exists_untouched_copy_tapeHost`). `tapeStream_fires_forever` states the
  positive fact behind what is NOT on offer: at any positive density the tape
  fires past every horizon, so the lifetime-free absorption clauses (which need
  a quiet stream) and the fiber's settling theorems (which need a never-missing
  or eventually-realizable candidate) do not apply here — a route-absence, not
  an impossibility. Honest boundary: the damage model stays named; nothing
  lifetime-free; one architecture; registered as *Inevitability* Proposition
  6.10, row IN-44.
- **A member of both route-classes carries survival, by redundancy**
  (`TapeHostSurvival.lean`): the profile-class host with a `P`-copy redundant
  floored fiber added as extra memory — one substrate (`CompMem`), the base's
  cells plus one binary register per candidate per copy, whose update runs the
  host's own step on the base cells and one floored-fiber generation on the
  fiber cells, driven by a miss indicator read off the base's own observation
  cell (`compSubUpdate`, `fiberMiss`). The base half is exactly the host's own
  orbit (`compSubUpdate_base_iterate`), so both memberships transport: the
  composite is in `𝒮_L` with every field but the read-only-code witness the
  host's own proof term (`comp_substrateL`) and in `𝒮_E` at the same coupled
  Gödel size through the class-level constructor, the frame reading the base's
  counter off the composite's own packing (`compFrame_surj_iterate`,
  `comp_substrateE`). The fiber's miss indicator along the loaded orbit is the
  witness's miss indicator on the host's own tape stream — every candidate's
  miss, the true candidate's being the tape's own bit (`fiberMiss_eq_witMiss`)
  — so the redundancy route reads on it: under any damage schedule inside a
  horizon `n`, confined to the tape's own firing and touching at most `c` copies
  per hit, whenever `c · (n · η + W₀/2) < P` some copy is never touched and its
  weight vector under the damaged run is the single undamaged fiber's at every
  step (`comp_carries_survival`), and
  `tapeHost_carries_survival` states both memberships and that clause together
  at a Gödel size fixed once. Honest boundary: one witness; survival in the
  redundancy form — the absorption half of the single-witness assembly's
  noisy-branch clause, no margin claimed and none needed — at a horizon,
  conditional on the damage model with the host-side gate in place of (D1),
  nothing lifetime-free, and without the decode-level conclusion (the
  composite's reading equal to the base's next state), which needs a
  never-missing candidate this base denies; the guest that crosses (the counter memory) and
  the guest that survives (the fiber's copies) are distinct structures on one
  substrate, as in the single-witness assembly; survival is stated over the
  fiber's own abstract carrier, the miss identity proved along the undamaged
  orbit being the one fact tying the composite's fiber cells to it; the
  composite is not priced; which systems carry survival beyond this witness
  stays open. Registered as *Inevitability* Proposition 6.11, row IN-46.
- **The class-level `𝒮_E` constructor** (`SubstrateEmergence.lean`): for any
  decoupled update, any packing of its memory onto a numeral carrier and any
  frame surjective off the packed update's own iterate, membership in the
  emergence route-class follows from the numeral conditions and one crossing
  hypothesis at the frame's capacity (`substrateE_of_emergence`); over a
  reversible update every surjective frame qualifies (`substrateE_of_perm`) —
  *Inevitability* Definition 2.3's own sentence, that a decoupled cheap
  reversible world of sufficient capacity is in `𝒮_E`, at the class's Lean
  definition, with one Gödel size shared by the capacity clause and the
  crossing (`grownGuestReachesThresholdAt_uniform`). Honest boundary: the
  codes for the table and the frame are hypotheses at class level (the
  emergence theorem's own currency); the read-only region is taken as given,
  so whether it is an honest code region is the instance's business; the
  block-pair host above is an instance in the literal sense but is registered
  at numerals whose class Gödel number and crossing Gödel size are not
  identified, so it is not re-derived from the constructor; and the Witness
  World's carrier has no code region for the constructor to take. Registered
  as *Inevitability* row IN-40.
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
- **A constructed learner that meets those prerequisites, and survives damage**
  (`LearningWitness.lean`, `LearningWitnessComplete.lean`,
  `FlooredMixture.lean`, `WitnessMixture.lean`, `BasinSettling.lean`,
  `RedundantFiber.lean`, `DamageGate.lean`): the class above is inhabited by an
  explicit system — a Bernoulli-noise window chain, embedded so that its code
  region is never written — rather than by an abstract witness whose fields are
  asserted. What rules out that gluing is a realization theorem: the
  observation read off the substrate's own cell along its own orbit *is* the
  chain's observation, pointwise, so every statistical clause is stated on the
  substrate's process and proved by rewriting along it. A junk-inhabitation
  guard (`substrateL_junk_satisfiable`) shows the class is satisfiable by
  degenerate instantiations — `True` for its propositional fields, an empty
  family, a vacuous rate constant — which is what makes the real witness's
  named ones carry content rather than merely typecheck. Its theory
  conditions are then discharged at Foundation's finite `𝗣𝗔⁻` — ℕ-soundness at
  the faithful "every provable sentence is true" form, consistency derived from
  that rather than assumed beside it — by a *single* incompleteness invocation
  whose Gödel size is threaded through both the capacity threshold and the
  underivable-truth payload (`witness_crossing_genuine_paMinus`).
  The learner riding it is a mixture floored at one quantum per candidate, and
  its dynamics has an exact normal form carrying no hypothesis at all: the run
  **is** an exponent automaton, every weight a power of two throughout, the
  floor being ℕ-subtraction's clip at exponent zero (`wRun_eq_pow_expRun`). Off
  that identity come a surprise bound against *any* reference candidate's own
  errors — with refuting families showing realizability is load-bearing rather
  than convenient — settling of the whole weight vector from every carrier
  vector at every budget of at least one quantum (`BasinSettling.lean`), and,
  on the witness's own trajectory, the identity that the true rule's miss count
  *is* the noise count (`witMiss_zero`), so its damage budget is a rate where a
  never-missing candidate's stays lifetime-free.
  Survival under corruption is proved, not assumed: a damaged fiber settles
  exactly as an undamaged run restarted after its last hit, at a price paid
  once per hit; `P` copies reading one stream, decoded by the least-indexed
  copy whose prediction the base confirms, agree wherever two of them verify;
  and a schedule touching fewer than `P` copies leaves one untouched, so the
  composite reads the base's own next state (`RedundantFiber.lean`). That
  composite's decode is priced as well, and is the cheaper half to name: its
  three ingredient codes carry every structural number but the population size,
  so `P`'s binary numeral is the only one loaded (`KE_compFrameFlat_le`) —
  Both halves are priced on the flat carrier `Fin (n₁ * n₂ ^ P)`, and that this
  is the composite guest's own state space is a theorem on each side rather than
  a reading of the encoding: conjugating the copies through the digit encoding
  gives one application of the per-copy rule per copy, and the flat decode is
  shown equal to the population's own.
  Honest boundary: the damage model — which perturbations are allowed, and how
  far one reaches — is a **named hypothesis of the companion paper, not a
  theorem of this library**, and `DamageGate.lean` states precisely what that
  costs. A gate a host could actually apply, phrased on the noise stream and so
  naming the same times before and after any damage, buys the same conclusion
  (`compPredFrame_eq_next_of_noiseGated`) — but is provably empty on a
  noise-free stream (`noiseGated_eq_empty_of_quiet`), the branch whose budget
  is the zero-miss anchor. What closes the apparent disjointness of
  host-checkable and lifetime-free is the **eventually-quiet** class
  (`QuietFrom`): a stream firing at most `m` times keeps the gated schedule's
  count capped by that same `m` at every horizon
  (`noiseCount_le_of_quietFrom`), so the single redundancy condition
  `c·m < P` buys the untouched copy and the composite's conclusion at every
  horizon at once (`exists_untouched_copy_of_quietFrom`,
  `compPredFrame_eq_next_of_quietFrom`) — a lifetime statement with a
  non-empty gate, witnessed by a designed stream whose designated candidate's
  misses are exactly its `m` firings (`quietStream`,
  `witMiss_quietStream_zero_iff`, `noiseGated_quietStream_iff`) and emitted by
  a saturating counter automaton whose own transient is the firing set
  (`sourceOut_iterate_sourceStep_zero`, `sourceStep_not_injective`).
  What no gate delivers is the containment itself:
  `exists_untouched_copy_of_noiseGated` consumes `NoiseGated`, so every damage
  time must sit on a firing — a hypothesis on every branch. On the noisy
  branch it takes a damage-invariant form — `noiseGated_iff_witMiss` makes the
  noise bit and the true candidate's miss one event — and it is that
  identification, not the mere existence of a finitely-firing event, that the
  argument rests on.
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
  implied. The hypothesis also comes in a **horizon-bounded** form,
  `MixingHoeffdingTo N` — the same statement with its quantifier restricted to
  sample sizes at most `N`, which is what a learner reading one orbit segment
  actually consumes. It carries its own vacuity floor (below a horizon set by
  the constant, *every* law satisfies it, so a bounded claim has to state its
  horizon against its constant) and its own refutations, each naming both
  quantifiers. On it, the oracle over a whole scheduled query class is
  derived: for a fixed finite schedule whose every query is representative
  below `N` at one shared constant, the empirical answers from a single orbit
  segment satisfy the oracle predicate off an event of measure at most `δ`,
  the schedule entering only logarithmically in the sample size. Every
  oracle corollary is stated at that bounded form, each unbounded version
  derived from its own twin rather than proved twice, so a consumer
  holding only a horizon-bounded hypothesis gets the sample-size bound
  and the pruning-survival statement as well as the tail. Composed with the
  pruned learner's own discovery theorem (`FiniteHorizonDiscovery.lean`),
  that yields an end-to-end statement: off an event of measure at most `δ`,
  a learner answering its whole query schedule from one orbit segment
  reaches the concentrated posterior — and the two sample counts are
  unrelated, so the horizon bounds the answering of the schedule, never the
  run. The
  window-noise pruning budget now reaches the single-trajectory
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
- **Kolmogorov complexity at two measures, and the load-bearing one is bits**
  (`KolmogorovComplexity.lean`, `KolmogorovTimeBounded.lean`,
  `KolmogorovBitlen.lean`, `KReconnection.lean`): the least-index measure `K` is
  uncomputable by the recursion theorem — and so, separately, is the
  **bit-length** measure `Nat.size ∘ encode`, which is the one the
  description-length results are stated at (`K_bitlen_not_computable`). That
  second proof re-runs the argument from scratch rather than reducing to the
  first, because `Nat.size` is not injective and the reduction genuinely fails;
  `Nat.size`'s own computability is built here, Mathlib having no such lemma.
  The load-bearing MDL theorems are then instantiated at the bit-length
  complexity of a concrete rule (`ruleComplexity`), so their description-length
  parameter is a real complexity rather than an abstract real left in prose.
  Honest boundary: two-machine invariance is deferred with a documented
  obstruction — Mathlib exposes a single fixed universal machine, and the
  classical bound needs two, one simulating the other.
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
- **Build-enforced axiom hygiene**: 1015 `#guard_msgs in #print axioms` guards
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

**"Narrow freely" is a real consequence, so it is worth saying plainly**: a
release can make a previously public declaration `private`, and one already
has. That is why the install snippet above pins a tag rather than a branch —
nothing changes under you until you move the pin. Every release that loses a
public name lists each one in its release notes rather than counting them, and
if a name you actually depend on goes, that is a good issue to open: a real
consumer is a reason to keep something public that the closure cannot compute.

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
subsystem, and their assembly on one constructed witness in pathwise
and budget form, conditional on a named damage model) — so "[Discovery] §2.2" names a section of that paper. `FV-*` tags name
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
