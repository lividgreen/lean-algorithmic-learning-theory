/-
Copyright (c) 2026 Mykola Palamarchuk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mykola Palamarchuk
-/
import ALT.Reflective
import ALT.RegimeConsistency
import ALT.GodelInternalization
import ALT.CategoricalThreshold
import ALT.Decoupling
import ALT.SQObjects
import ALT.ParityCounterexample
import ALT.BirkhoffTool

-- Formal-check file, not Mathlib-destined: opt out of the house-style header linter.
set_option linter.style.header false
set_option linter.style.longLine false

/-!
# The reflective threshold and the substrate class ([Inevitability] §2, Definitions 2.1–2.3)

Provenance: [Inevitability], §2 (Definition 2.1 the reflective
threshold, Definition 2.2 the substrate class `𝒮`, Definition 2.3 the two route-classes
`𝒮_E`/`𝒮_L`), §4 (the learning route's chain), §5 (Theorem 5.1(b), the learning branch of the
two-regime synthesis).

This is the first Lean object for the paper's own headline: every prior module in this
development formalizes a companion paper's result and is *imported* here; nothing before this
file gave [Inevitability]'s own Definitions 2.1–2.3 a Lean counterpart.

## What this DOES establish
* `ReachesThreshold` (Definition 2.1, the CONDITION): a predicate bundling
  `ReflectiveAssembly.Reflective` (the [Decoupling] §6 stand-in bundle), the four theory
  conditions on `T_S` as CARRIED (uninterpreted) hypotheses, and the existence of indexing/working
  recursor depths `M_idx ≥ g(T_S)`, `M_chk ≥ g(T_S)²` (a concrete degree-2 witness for
  "poly(g(T_S))"). Left exactly as before — see the boundary note for why its `Reflective`
  conjunct alone is still unconditionally satisfiable.
* `DeliversUnderivableTruth` (Definition 2.1, the CONSEQUENCE): the represents-but-cannot-derive
  payload under carried `Incompleteness`. `deliversUnderivableTruth_of_incompleteness_alone` shows
  it needs no capacity or substrate input at all (a plain consequence of `Incompleteness`); the
  companion `incompleteness_not_unconditionally_satisfiable` is the vacuity guard this forces —
  `Incompleteness` itself, not any capacity/substrate hypothesis, is the thing that can fail.
* `Substrate` (Definition 2.2, `𝒮`): a three-field structure — (S1) `Decoupling.Fixes` on a
  code region, (S2) the [Discovery] §1.2 regime with depth (`RegimeConsistency`'s own hypothesis
  shape, reused verbatim), (S3) the reflective-capacity inequality plus the SAME theory
  conditions as `ReachesThreshold`.
* `SubstrateE`/`SubstrateL` (Definition 2.3): the two route-classes extending `Substrate`.
  `SubstrateL` carries [SQ]'s full named statistical set — realizability, Assumption A
  (`ParityCounterexample.PolyBounded` on the genuine `SQObjects.sqDim`), window sufficiency,
  benign separation (`ε₀ = Ω(1/r)`), and E1 (`BirkhoffTool.MixingHoeffding`) — WITHOUT the
  poly-time approximate version-space maintainer ([Inevitability] §2 line 51 excludes it
  explicitly; no field here supplies it).
* `reflectiveCapacity_fitsIn_headroom` (the capacity bridge): from (S3) and `2 ≤ g(T_S)`,
  together with `CategoricalThreshold.categorical_threshold` at working depth `g(T_S)+1`, the
  reflective object built fits inside the HOST's leftover capacity `⌊K - |s_code|⌋₊`, not merely
  its own linear `2n` — the step that makes (S3)'s inequality genuinely consumed.
* `substrateL_reachesThreshold` (Theorem 5.1(b), restated): `SubstrateL → 2 ≤ g(T_S) →
  DeliversUnderivableTruth`, proved via `reflectiveCapacity_fitsIn_headroom` — no longer landing in
  the unconditionally-satisfiable `ReachesThreshold`. See the boundary note for the precise
  accounting of what the proof consumes versus only carries.
* `CoupledDeliverance`, `reflectiveCapacity_coupledDeliverance`, `substrateL_reachesCoupledThreshold`
  (the coupling the honest-limit note below names): the payload stated AT the SAME capacity-bounded
  object's own depth (`Robj.depth = g(T_S)+1`), via `reflectiveAsm_payload_at_depth` — not under a
  second existential. Consumes exactly (S3) and `2 ≤ g(T_S)`, the same accounting as
  `substrateL_reachesThreshold`.
* `coupledDeliverance_fitsIn_below_paperCapacity`, `coupledDeliverance_not_necessary_at_paperCapacity`
  (the necessity direction, CHECKED — and refuted as stated): at every `2 ≤ g(T_S)`, the coupled
  conclusion is already reachable at a host capacity strictly BELOW `sCodeSize + capacity n` — the
  paper's own `2n` figure over-provisions for the single fixed depth `g(T_S)+1` (it is a uniform
  bound good up to `g(T_S)²`, not the tight amount this depth alone needs). See the boundary note.
* `ReachesThresholdAtDepth`: Definition 2.1's depth clause, TIED to a constructed
  `RealizabilityRecursor.ReflectiveAsm` object's own `depth` (`gTS ≤ Robj.depth ∧ gTS ^ 2 ≤
  Robj.depth`) rather than `ReachesThreshold`'s free-floating `∃ Midx Mchk, …` (kept unchanged,
  alongside this one — see the boundary note).
* `CoupledDeliveranceAtRequiredDepth`, `reflectiveCapacity_fitsIn_headroom_atRequiredDepth`,
  `reflectiveCapacity_coupledDeliverance_atRequiredDepth`,
  `substrateL_reachesCoupledThresholdAtRequiredDepth`: the coupled conclusion re-instantiated at
  `M_chk := g(T_S) ^ 2` — the depth Definition 2.1 FORCES exactly (`categorical_threshold` caps
  `M_chk ≤ g(T_S)²`, Definition 2.1 asks `M_chk ≥ poly(g(T_S))`, and this file's own witness
  for "poly" already is `g(T_S)²`). Same accounting as the `g(T_S)+1` forms: consumes exactly (S3)
  and `2 ≤ g(T_S)`. `coupledAtRequiredDepth_reachesThresholdAtDepth` shows this — and, per the
  next bullet's contrast, only this — depth is a genuine `ReachesThresholdAtDepth` witness.
* `tightFamily_capacity_exact`, `tightFamily_not_fitsIn_capacityMinusOne`,
  `coupledAtRequiredDepth_not_reachable_below_paperCapacity_on_family`: **necessity, on the
  family `g(T_S) = 2 ^ n - 1` (`n ≥ 2`)**. At this family `Nat.clog 2 (g(T_S)+1) = n` exactly,
  and (S3) at the paper's own `capacity n = 2n` figure IS load-bearing for
  `CoupledDeliveranceAtRequiredDepth`: one bit under `capacity n` already fails to host the
  required-depth recursor.
* `offFamily_capacity_exact`, `offFamily_fitsIn_below_paperCapacity_atRequiredDepth`: OFF that
  family — witnessed at `g(T_S) = 2 ^ m` (`m ≥ 1`, reaching the concrete `g(T_S) ∈ {2, 4}`
  cases) — the required-depth conclusion is STILL reachable one bit under `capacity n`: necessity
  is family-specific, not a universal fact about every `g(T_S)`.
* `s3_not_implied_by_s2`: (S3) is not implied by (S2) — a concrete witness meeting the regime
  but failing the capacity inequality, machine-checking the paper's own "standing trap" warning.
* `substrate_satisfiable`: the bare `Substrate` structure is non-vacuous, at a `g(T_S) = 2`
  witness where the capacity bridge is non-vacuous (not the degenerate `g(T_S) = 0`).
* `ReachesThresholdWithin`: Definition 2.1 stated **within a work budget**, over
  `CategoricalThreshold.ReflectiveWithin` — a genuine reflective object of the realizability CCC at
  the demanded working depth, whose recursor fits the budget. Added ALONGSIDE `ReachesThreshold`
  and `ReachesThresholdAtDepth`, both kept unchanged. This is the form that can FAIL, and the
  boundary notes below record which of their limitations it removes and which it does not.
* `tightFamily_reflectiveWithin_iff`: on `g(T_S) = 2 ^ n - 1` (`2 ≤ n`), membership holds **iff**
  the budget meets the paper's own `capacity n = 2n` — an exact threshold, quantified over the
  witness's own depth rather than fixed at one (`tightFamily_capacityMinusOne_lt_requiredCard`,
  `tightFamily_not_fitsIn_capacityMinusOne_atDepth` are its reusable counting core).
  `offFamily_reflectiveWithin_below_capacity` shows the same family-dependence off it that the
  coupled results already record.
* `substrateL_reachesThresholdWithin` (Theorem 5.1(b) for the membership form) and
  `reachesThresholdWithin_not_reachable_below_paperCapacity_on_family`: `𝒮_L` reaches the threshold
  at the host's leftover capacity `⌊K − |s_code|⌋₊`, and on the tight family a host one bit short of
  `capacity n` does NOT — so (S3)-shaped capacity is load-bearing for MEMBERSHIP, not only for the
  coupled conclusion.
* `coupledAtRequiredDepth_reachesThresholdWithin`: the coupled chain discharges the new clause from
  its own capacity-bounded witness — contrast `coupledAtRequiredDepth_reachesThresholdAtDepth`,
  which discharges its reflective conjunct with the unconditionally-available
  `ReflectiveAssembly.reflective_satisfiable`.
* `CommittedOn`, `ReachesThresholdWithinAt`: the budgeted threshold indexed by TIME — a
  configuration committed to a pinned reference codeword on the code region, conjoined with the
  atemporal `ReachesThresholdWithin`. Added alongside the three predicates above, all unchanged.
* `fixes_reachesThresholdWithinAt_persists` and its class-level corollary
  `substrate_reachesThresholdWithinAt_persists`: the crossing recurs at every later step, from a
  read-only code region alone. The corollary is the first consumer of `Substrate`'s **(S1)** field
  anywhere in this development — the boundary note below records what that did and did not change.
  The bare-hypothesis form is the general statement (only `Decoupling.Fixes` is needed, none of
  (S2)/(S3)'s parameters); the `Substrate` form is what the class supplies.
* `reachesThresholdWithinAt_lost_on_overwrite`: the guard making that (S1) hypothesis load-bearing
  — a one-cell world whose update overwrites its whole code region holds the crossing at `t = 0`
  and has lost it at `t = 1`, at a static conjunct that holds throughout. [Discovery] Proposition
  4.2's overwrite clause in deterministic skeleton.

## What this does NOT establish (flagged)
* `ReachesThreshold` (kept as the Definition-2.1-faithful CONDITION, unchanged) still wraps
  `ReflectiveAssembly.Reflective`, unconditionally satisfiable for every Gödel number
  (`ReflectiveAssembly.reflective_satisfiable`) — that has NOT changed, and
  `substrateL_reachesThreshold` no longer targets it, precisely because of this. The RESOLUTION is
  `ReachesThresholdWithin`, which replaces that conjunct with the capacity-indexed
  `CategoricalThreshold.ReflectiveWithin` and thereby fails below the Gödel sentence's own size —
  it does not repair `ReachesThreshold`, which is deliberately left as the paper's literal reading.
* **The honest limit of the fix.** `DeliversUnderivableTruth`'s bare conclusion (∃ a representer,
  under carried `Incompleteness`) is ITSELF reachable from `Incompleteness` alone, with no capacity
  or substrate input (`deliversUnderivableTruth_of_incompleteness_alone`): `GodelThreshold.
  godel_threshold` witnesses `M := gTS` directly, since `RepresentsUnderivableTruth` at the
  `GodelCore` level is pure Gödel-numbering (`gnum s ≤ M`), not tied to any capacity-bounded
  object. So `substrateL_reachesThreshold`'s hypotheses `SubstrateL` and `2 ≤ gTS` are NOT
  logically necessary for its stated conclusion — a strictly cheaper proof of the same conclusion
  exists. What the restated theorem's PROOF adds is that `𝒮_L` reaches the payload through the
  paper's own intended capacity-bounded mechanism (`categorical_threshold`'s reflective object,
  genuinely fitting inside (S3)'s leftover capacity via `reflectiveCapacity_fitsIn_headroom`), not
  merely via bare Gödel numbering — a sufficiency demonstration, not a necessity result.
* **The coupled statement's necessity, checked — and it fails too.** Tying the representer to the
  SAME capacity-bounded object (`CoupledDeliverance`, above) closes the existential-leak gap, but
  does NOT make (S3) necessary at the paper's own `capacity n` figure:
  `coupledDeliverance_not_necessary_at_paperCapacity` exhibits, at every `2 ≤ g(T_S)`, a host
  capacity `K` strictly below `sCodeSize + capacity n` at which the coupled conclusion STILL holds.
  The reason is `coupledDeliverance_fitsIn_below_paperCapacity`: `capacity n = 2n` is
  `GodelInternalization.capacity_bound`'s uniform bound, valid for every working depth up to
  `g(T_S)²`, not the tight amount the SINGLE fixed depth `g(T_S)+1` needs (`n+1` bits already
  suffice once `n ≥ 2`, i.e. `2 ≤ g(T_S)` — the same side condition the positive direction needs).
  So `(S3)` at the paper's literal `capacity n` is still not load-bearing for the coupled
  conclusion; what would make it so is restating the paper's threshold at the tight budget the
  fixed depth actually needs, not `2n`. This bullet is entirely about the SHALLOW `g(T_S)+1` depth;
  see the next two bullets for the required depth `g(T_S)²`.
* **At the required depth, necessity is family-dependent, not universal.**
  `coupledAtRequiredDepth_not_reachable_below_paperCapacity_on_family` proves (S3) at `capacity n`
  IS necessary on `g(T_S) = 2^n - 1`; `offFamily_fitsIn_below_paperCapacity_atRequiredDepth` proves
  it is NOT necessary at the off-family witness `g(T_S) = 2^m`. Neither theorem claims to settle
  every `g(T_S)`: no general characterization of exactly which Gödel numbers make `capacity n`
  tight at the required depth is attempted here (the two families were the ones checked).
* `ReachesThresholdAtDepth` fixes ONLY the depth clause's vacuity, not `ReachesThreshold`'s other
  one: it still wraps the same `ReflectiveAssembly.Reflective` stand-in
  (`reflective_satisfiable`, unconditionally satisfiable for every Gödel number) and the same
  carried `TheoryConditions`, unchanged from `ReachesThreshold`. `ReachesThresholdWithin` is the
  form that fixes BOTH — but only by taking a work budget as a parameter, which the depth-tied form
  does not; the two are not comparable statements, and both are kept.
* `ReachesThresholdWithin`'s own limits, stated plainly. (i) The four `TheoryConditions` remain
  CARRIED, uninterpreted, exactly as in the two forms above — the capacity conjunct is what became
  refutable, not they. (ii) It is a condition on the pair `(work budget, g(T_S))`; it says nothing
  about a *particular* subsystem's `Rep(S)` beyond what FV-13/FV-14 check, so the concrete
  `{0,1}^{|s_work|}` layout stays paper-level here as everywhere. (iii) It carries no payload:
  the represents-but-cannot-derive consequence is `CoupledDeliveranceAtRequiredDepth`'s, and
  `coupledAtRequiredDepth_reachesThresholdWithin` runs from the payload form to this one, not back.
  (iv) Necessity of the paper's `2n` figure remains family-dependent — exact on `2 ^ n - 1`, false
  at `2 ^ m`, with no general characterization attempted, the same scope the coupled results have.
* (S1) (`Decoupling.Fixes`) is carried by `Substrate`/`SubstrateL` and is exactly the
  architectural invariant `RetentionUpperBound.retention_persists` consumes, but no theorem on the
  ATEMPORAL route needs it: `DeliversUnderivableTruth` and `ReachesThresholdWithin` alike are
  statements about a configuration (matching `ReachesThreshold`'s own atemporal nature), not claims
  about persistence across iteration, so `substrateL_reachesThreshold` and
  `substrateL_reachesThresholdWithin` neither consume (S1) nor could. Where it IS consumed is the
  time-indexed section at the end of this file — `substrate_reachesThresholdWithinAt_persists`,
  with `reachesThresholdWithinAt_lost_on_overwrite` showing the hypothesis load-bearing. What that
  buys is RETENTION only, and its scope is stated there: a commitment already held is kept.
* (S2) (`RegimeWithDepth`) is likewise carried by `Substrate`/`SubstrateL` but unused by
  `substrateL_reachesThreshold`'s proof: the capacity bridge draws only on (S3).
* `SubstrateL`'s five learning-specific fields (`realizability`, `windowSufficiency`,
  `assumptionA`, `benignSeparation`, `e1`) are likewise CARRIED but UNUSED by
  `substrateL_reachesThreshold`'s proof, for the same reason: the destination type does not ask
  for them. They are present for Definition 2.3 faithfulness (a genuine `𝒮_L` membership needs
  all five), not because the headline theorem's Lean proof consumes them. The time-indexed section
  at the end of this file does NOT reach them either, and does not claim to: it consumes (S1) and
  buys retention, whereas these five would be consumed by the complementary *discovery* half —
  that learning PRODUCES the committed configuration — which needs the learner inside the
  substrate's own dynamics, an object no module here supplies. This file does not manufacture a
  field-consuming proof by weakening the conclusion.
* `SubstrateE`'s two fields (`growsLawfulGuest`, `grownGuestReachesThreshold`) are CARRIED as
  opaque Props, not connected to `PersistenceCapacity.witness_world`: that theorem lives on the
  SPECIFIC carrier `Decoupling.Mem (Fin κ) Bool` built by `witnessWorld κ k G π`, not on
  `Substrate`'s GENERAL `(ι, V, U)`. Bridging the two needs an instantiation argument this file
  does not attempt (Theorem 5.1(a) is explicitly out of scope here — imported verbatim in its own
  home); the class IS inhabited elsewhere, by `BlockPairOverlap.hostWitness_substrateE`.
* This file exhibits no inhabitant of either route-class: `substrate_satisfiable` inhabits only
  the bare three-field `Substrate`. The inhabitants live in their own modules —
  `LearningWitness.witness_substrateL` and `BlockPairWitness.hostWitness_substrateL` for `𝒮_L`,
  `BlockPairOverlap.hostWitness_overlap` for both classes at one host ([Inevitability] §5
  Remark 5.3, Theorem 5.8; rows IN-14, IN-37, IN-38).

## Hypotheses: paper-stated vs added
* Paper-stated / faithful: Definitions 2.1–2.3 verbatim, including (S2)'s explicit constants and
  (S3)'s `K ≥ |s_code| + poly(n)`, `n = ⌈log₂(g(T_S)+1)⌉`.
* Added / modeling: the four theory conditions (`Consistent`, `NSound`, `Delta1Axiomatized`,
  `InterpretsR0`) are CARRIED as uninterpreted `Prop` parameters, never discharged — matching how
  `GodelThreshold.Incompleteness` is carried elsewhere in this development; "poly(g(T_S))" is
  concretely instantiated as `g(T_S)²` (the same degree-2 witness `GodelInternalization`/
  `CategoricalThreshold` use, there in the opposite — upper-bound — role); `SubstrateL`'s
  realizability and window-sufficiency hypotheses are likewise carried as uninterpreted `Prop`
  parameters (no reusable Lean object for either exists elsewhere in the corpus); Assumption A is
  read as a FAMILY statement (`sqDim` polynomially bounded across a family indexed by `r`), matching
  `SQObjects.survivors_polyBounded_of_separated`'s own shape, existentially packaged so `Substrate`'s
  single-system parameters need not themselves index a family.
-/

namespace SubstrateClass

/-! ### Definition 2.1: the reflective threshold -/

/-- The four theory conditions [Inevitability] Definition 2.1 imposes on the internalized theory
`T_S` — consistent, ℕ-sound, `Δ₁`-axiomatized, interprets Robinson–Cobham `𝗥₀` — carried as
uninterpreted `Prop` parameters (no Lean formalization of any of the four is attempted; they are
named hypotheses, exactly as `GodelThreshold.Incompleteness` is carried elsewhere). -/
def TheoryConditions (Consistent NSound Delta1Axiomatized InterpretsR0 : Prop) : Prop :=
  Consistent ∧ NSound ∧ Delta1Axiomatized ∧ InterpretsR0

/-- **Definition 2.1 (the reflective threshold).** A system with internalized-theory Gödel number
`gTS` **reaches the reflective threshold** when its subsystem is `ReflectiveAssembly.Reflective`
([Decoupling] §6's stand-in bundle: `Rep(S)` Cartesian closed up to capacity, via a parameterized
NNO of depth `> gTS`), `T_S` meets the four `TheoryConditions`, and there exist an indexing depth
`M_idx ≥ g(T_S)` and a working depth `M_chk ≥ g(T_S)²` (a concrete instance of "poly(g(T_S))").

`ReflectiveAssembly.Reflective` is a STAND-IN bundle on two separate carriers (see its own module
note) and is unconditionally satisfiable for every `gTS`
(`ReflectiveAssembly.reflective_satisfiable`) — so this predicate's "reflective" conjunct alone
never certifies a genuine `Rep(S)`; see the module boundary note above. -/
def ReachesThreshold (Consistent NSound Delta1Axiomatized InterpretsR0 : Prop) (gTS : ℕ) : Prop :=
  ReflectiveAssembly.Reflective gTS ∧
    TheoryConditions Consistent NSound Delta1Axiomatized InterpretsR0 ∧
    ∃ Midx Mchk : ℕ, gTS ≤ Midx ∧ gTS ^ 2 ≤ Mchk

/-- **Definition 2.1's depth clause, tied to a constructed object.** `ReachesThreshold`'s own
depth conjunct `∃ Midx Mchk, gTS ≤ Midx ∧ gTS ^ 2 ≤ Mchk` is satisfiable by `Midx := gTS`,
`Mchk := gTS ^ 2` with NO object involved — free-floating, not about any particular recursor.
This version replaces the existential with the SAME single depth a constructed
`RealizabilityRecursor.ReflectiveAsm` object actually carries (`Robj.depth`, the one depth
number `categorical_threshold` exhibits, doing duty for both the indexing and the working
depth): `gTS ≤ Robj.depth ∧ gTS ^ 2 ≤ Robj.depth`. Kept ALONGSIDE `ReachesThreshold`, not in
place of it — see the module boundary note. -/
def ReachesThresholdAtDepth (Consistent NSound Delta1Axiomatized InterpretsR0 : Prop) (gTS : ℕ)
    (Robj : RealizabilityRecursor.ReflectiveAsm gTS) : Prop :=
  ReflectiveAssembly.Reflective gTS ∧
    TheoryConditions Consistent NSound Delta1Axiomatized InterpretsR0 ∧
    gTS ≤ Robj.depth ∧ gTS ^ 2 ≤ Robj.depth

/-- **Definition 2.1 with a capacity, and therefore with content.** The two forms above are
unconditionally satisfiable in their categorical clause: both wrap `ReflectiveAssembly.Reflective`,
which `ReflectiveAssembly.reflective_satisfiable` inhabits for every Gödel number — so neither can
fail on that clause, whatever the subsystem's budget. This form replaces it with
`CategoricalThreshold.ReflectiveWithin`, the SAME Definition-2.1 content stated *within a work
budget of `w` bits*: a genuine reflective object of the realizability CCC `Asm` (FV-13), at the
working depth Definition 2.1 demands, whose recursor object fits in `w` (FV-14).

Three consequences distinguish it from `ReachesThreshold`/`ReachesThresholdAtDepth`, which are kept
unchanged alongside it (the file's own precedent for an added form):

* it **fails** below the Gödel sentence's own size — `CategoricalThreshold.
  not_reflectiveWithin_below_sentence_size` — so it is a real condition on the subsystem, not a
  bookkeeping bundle;
* on the family `g(T_S) = 2 ^ n - 1` it is reached **exactly** at the paper's capacity figure
  (`tightFamily_reflectiveWithin_iff`), which makes (S3) load-bearing for MEMBERSHIP
  (`reachesThresholdWithin_not_reachable_below_paperCapacity_on_family`) and not only for the
  coupled conclusion;
* no separate `∃ M_idx M_chk` clause is needed: the depth demands live inside `ReflectiveWithin`,
  tied to its own witness, rather than floating free of any object. -/
def ReachesThresholdWithin (Consistent NSound Delta1Axiomatized InterpretsR0 : Prop)
    (w gTS : ℕ) : Prop :=
  CategoricalThreshold.ReflectiveWithin w gTS ∧
    TheoryConditions Consistent NSound Delta1Axiomatized InterpretsR0

/-- **The reflective threshold's payload** — the consequence Definition 2.1 exists to deliver,
[Decoupling] §6.3's represents-but-cannot-derive fact — under `GodelThreshold.Incompleteness` for
the theory at `gTS`, carried as a named hypothesis exactly as throughout this development
(`CategoricalThreshold.categorical_threshold`, `ReflectiveAssembly.reflective_representsUnderivableTruth`).
`ReachesThreshold` above stays the Definition-2.1-faithful CONDITION; this is the CONSEQUENCE a
system meeting it is entitled to. See `deliversUnderivableTruth_of_incompleteness_alone` and
`incompleteness_not_unconditionally_satisfiable` immediately below for the honest account of what
makes it non-vacuous — and what does not. -/
def DeliversUnderivableTruth {Sentence : Type*} (gnum : Sentence → ℕ)
    (Derivable True_ : Sentence → Prop) (gTS : ℕ) : Prop :=
  GodelThreshold.Incompleteness gnum Derivable True_ gTS →
    ∃ M, GodelThreshold.RepresentsUnderivableTruth gnum Derivable True_ M

/-- **Vacuity check, primary branch — fails.** `DeliversUnderivableTruth` cannot be shown to fail at
any parameters, because it does not need any: `GodelThreshold.godel_threshold` witnesses `M := gTS`
directly from `Incompleteness` alone, with no capacity, no substrate hypothesis, and not even
`2 ≤ gTS`. Recorded so it is stated precisely what `substrateL_reachesThreshold`'s extra hypotheses
buy beyond this bare fact: a capacity-respecting WITNESS (`reflectiveCapacity_fitsIn_headroom`),
not a stronger conclusion. -/
theorem deliversUnderivableTruth_of_incompleteness_alone
    {Sentence : Type*} (gnum : Sentence → ℕ) (Derivable True_ : Sentence → Prop) (gTS : ℕ) :
    DeliversUnderivableTruth gnum Derivable True_ gTS :=
  fun hInc => ⟨gTS, GodelThreshold.godel_threshold gnum Derivable True_ gTS gTS (le_refl gTS) hInc⟩

/-- **Vacuity check, fallback branch — this is the one that bites.** Since the primary check above
cannot fail, the guard falls to its named alternative: `Incompleteness` itself — the hypothesis
`DeliversUnderivableTruth` is carried under — is NOT unconditionally satisfiable. Witness: a theory
that derives every sentence (`Derivable := fun _ => True`) has no undecided sentence to represent,
so `Incompleteness` fails outright. -/
theorem incompleteness_not_unconditionally_satisfiable :
    ∃ (Sentence : Type) (gnum : Sentence → ℕ) (Derivable True_ : Sentence → Prop) (gTS : ℕ),
      ¬ GodelThreshold.Incompleteness gnum Derivable True_ gTS := by
  refine ⟨Unit, fun _ => 0, fun _ => True, fun _ => True, 0, ?_⟩
  intro hInc
  obtain ⟨_, _, _, hnd⟩ := hInc
  exact hnd trivial

/-! ### Definition 2.2: the substrate class `𝒮`, factored into its three prerequisites -/

/-- **(S1) decoupled substrate.** A code/work split on which `U` is read-only on the code region
`R` — [Decoupling] `Fixes`, reused verbatim (Lemma 3.1: equivalently, a faithfully encoded model
persists). -/
abbrev DecoupledSubstrate {ι V : Type*} (U : Decoupling.Mem ι V → Decoupling.Mem ι V)
    (R : Set ι) : Prop :=
  Decoupling.Fixes U R

/-- **(S2) regularity with depth.** [Discovery] §1.2's explicit-constant regime `r ≪ K ≪ L`,
in EXACTLY the hypothesis shape `RegimeConsistency.regime_strict_ordering` consumes: C1
(`K ≥ c₀·r·log(r/δ)`), C2 (`L ≥ c₁·K`, `c₁ > 1`), C3 (`r ≥ c₂`), and the named constant
conditions (`c₀ ≥ 1`, `c₂ ≥ 3`, `δ ∈ (0,1)`) that make the strict ordering `r < K < L` provable. -/
def RegimeWithDepth (r K L c₀ c₁ c₂ δ : ℝ) : Prop :=
  c₀ * r * Real.log (r / δ) ≤ K ∧ c₁ * K ≤ L ∧ c₂ ≤ r ∧
    1 ≤ c₀ ∧ 1 < c₁ ∧ 3 ≤ c₂ ∧ 0 < δ ∧ δ < 1

/-- **(S3) reflective capacity.** [Decoupling] Theorem 6.2's explicit threshold
`K ≥ |s_code| + poly(n)`, `n = ⌈log₂(g(T_S)+1)⌉` — reusing `GodelInternalization.capacity`
(`= 2n`) as the concrete "poly(n)" witness — together with `T_S` meeting the SAME four
`TheoryConditions` `ReachesThreshold` names ("`T_S` in the class of Definition 2.1"). -/
def ReflectiveCapacity (K : ℝ) (sCodeSize gTS : ℕ)
    (Consistent NSound Delta1Axiomatized InterpretsR0 : Prop) : Prop :=
  (sCodeSize : ℝ) + (GodelInternalization.capacity (Nat.clog 2 (gTS + 1)) : ℝ) ≤ K ∧
    TheoryConditions Consistent NSound Delta1Axiomatized InterpretsR0

/-- **Definition 2.2 (the substrate class `𝒮`).** `(M, U) ∈ 𝒮` when it carries exactly the three
prerequisites both routes consume: (S1) `DecoupledSubstrate`, (S2) `RegimeWithDepth`, (S3)
`ReflectiveCapacity`. [Inevitability] §2 is explicit that (S3) is NOT implied by (S2)
(`s3_not_implied_by_s2` below) — C1 buys capacity to represent the rule, (S3) buys capacity to
host the checker. -/
structure Substrate {ι V : Type*} (U : Decoupling.Mem ι V → Decoupling.Mem ι V) (R : Set ι)
    (r K L c₀ c₁ c₂ δ : ℝ) (sCodeSize gTS : ℕ)
    (Consistent NSound Delta1Axiomatized InterpretsR0 : Prop) : Prop where
  /-- (S1): the code region is read-only. -/
  s1 : DecoupledSubstrate U R
  /-- (S2): the regime `r ≪ K ≪ L`, with depth. -/
  s2 : RegimeWithDepth r K L c₀ c₁ c₂ δ
  /-- (S3): reflective capacity, and `T_S` in the class of Definition 2.1. -/
  s3 : ReflectiveCapacity K sCodeSize gTS Consistent NSound Delta1Axiomatized InterpretsR0

/-! ### Definition 2.3: the two route-classes -/

/-- **`𝒮_E` (the emergence route-class).** `Substrate` plus the emergence hypotheses
[Inevitability] §2 Definition 2.3 names: the update grows a lawful, affordably-owned guest from
every initial state ([Guests]'s emergence theorem, `GrowsLawfulGuest`), and that grown guest
reaches Definition 2.1's threshold (`GrownGuestReachesThreshold`). Both are CARRIED as
uninterpreted `Prop` parameters, since `Substrate` is general over `(ι, V, U)` — but the bridge for
any packed host with a surjective frame is `SubstrateEmergence.substrateE_of_emergence`, with
Definition 2.3's own ruled sentence machine-checked as `SubstrateEmergence.substrateE_of_perm`. The
genuine `PersistenceCapacity.witness_world` stays imported rather than instantiated: its carrier
`Decoupling.Mem (Fin κ) Bool` has no code region for the constructor to take as `R` — every habitat
cell moves under healing plus its own macro law, and the environment moves under its own
permutation, so `Fixes` there admits only the empty region ([Inevitability] §5 Remark 5.7 is where
that carrier question turns out to decide the seam between the two route-classes at the witnesses
these papers build, and `BlockPairOverlap.hostWitness_overlap` is where a finite host inhabits both
classes at once — [Inevitability] §5 Theorem 5.8). -/
structure SubstrateE {ι V : Type*} (U : Decoupling.Mem ι V → Decoupling.Mem ι V) (R : Set ι)
    (r K L c₀ c₁ c₂ δ : ℝ) (sCodeSize gTS : ℕ)
    (Consistent NSound Delta1Axiomatized InterpretsR0 : Prop)
    (GrowsLawfulGuest GrownGuestReachesThreshold : Prop) : Prop extends
    Substrate U R r K L c₀ c₁ c₂ δ sCodeSize gTS Consistent NSound Delta1Axiomatized InterpretsR0
    where
  /-- the update grows a lawful, affordably-owned guest from every initial state
  ([Guests]'s emergence theorem). -/
  growsLawfulGuest : GrowsLawfulGuest
  /-- that grown guest reaches Definition 2.1's threshold ([Inevitability] §2 Definition 2.3). -/
  grownGuestReachesThreshold : GrownGuestReachesThreshold

/-- **`𝒮_L` (the learning route-class).** `Substrate` plus [SQ]'s full named statistical set,
carried WITHOUT WEAKENING: `realizability` and `windowSufficiency` (carried, uninterpreted —
no reusable Lean object for either exists in the corpus); `assumptionA` (a rule class of
polynomial statistical dimension, via `ParityCounterexample.PolyBounded` on the genuine
`SQObjects.sqDim`, read as a family indexed by `r`, exactly `SQObjects.survivors_polyBounded_of_separated`'s
own shape); `benignSeparation` (`ε₀ = Ω(1/r)`); and `e1`, observability at a quantitative-mixing
rate, via `BirkhoffTool.MixingHoeffding` — carried, not proved, exactly as its own module
prescribes. [Inevitability] §2 line 51 is explicit that the poly-time approximate version-space
maintainer is NOT a member of `𝒮_L`: no field here supplies it, and nothing below needs it. -/
structure SubstrateL {ι V : Type*} (U : Decoupling.Mem ι V → Decoupling.Mem ι V) (R : Set ι)
    (r K L c₀ c₁ c₂ δ : ℝ) (sCodeSize gTS : ℕ)
    (Consistent NSound Delta1Axiomatized InterpretsR0 : Prop)
    (Realizability WindowSufficiency : Prop) : Prop extends
    Substrate U R r K L c₀ c₁ c₂ δ sCodeSize gTS Consistent NSound Delta1Axiomatized InterpretsR0
    where
  /-- realizability: the true rule lies in the concept class. -/
  realizability : Realizability
  /-- window sufficiency (W): the observed window is long enough for the SQ oracle. -/
  windowSufficiency : WindowSufficiency
  /-- Assumption A: the concept class has polynomially bounded statistical dimension, as a family
  indexed by `r` (the family witnesses `ιQ`/`Q`/`Mfam`/`ansfam`/`τsq` are existentially packaged so
  `Substrate`'s own single-system parameters need not themselves index a family). -/
  assumptionA : ∃ (ιQ Q : Type) (Mfam : ℝ → Finset ιQ) (ansfam : ℝ → Q → ιQ → ℝ) (τsq : ℝ),
    ParityCounterexample.PolyBounded (fun r' => (SQObjects.sqDim (Mfam r') τsq (ansfam r') : ℝ))
  /-- benign separation: `ε₀ = Ω(1/r)`, rendered as a concrete instance (the constant `cbs`
  witnesses the `Ω`). -/
  benignSeparation : ∃ ε₀ cbs : ℝ, 0 < cbs ∧ cbs / r ≤ ε₀
  /-- E1: observability at a quantitative-mixing rate — `BirkhoffTool.MixingHoeffding`, carried
  (not proved) exactly as its own module prescribes. -/
  e1 : ∃ (X : Type) (_inst : MeasurableSpace X) (μ : MeasureTheory.Measure (ℕ → X))
      (Z : ℕ → (ℕ → X) → ℝ) (predZ c : ℝ),
      BirkhoffTool.MixingHoeffding μ Z predZ c

/-! ### Theorem 5.1(b), and the two standing facts about `𝒮`'s prerequisites -/

/-- **The capacity bridge.** (S3)'s inequality does genuine work: together with
`CategoricalThreshold.categorical_threshold` at the working depth `M_chk := gTS + 1` — satisfiable
exactly because `2 ≤ gTS` (`gTS + 1 ≤ gTS ^ 2` fails at `gTS ∈ {0, 1}`, the side condition's exact
boundary) — the reflective object it builds fits not merely inside its OWN linear capacity `2n` but
inside the HOST's *leftover* capacity after the code region: `⌊K - sCodeSize⌋₊` work bits, `K` and
`sCodeSize` (S3)'s own parameters. This is the step that makes (S3)'s inequality consumed rather
than merely carried. -/
theorem reflectiveCapacity_fitsIn_headroom
    {Sentence : Type*} (gnum : Sentence → ℕ) (Derivable True_ : Sentence → Prop)
    {K : ℝ} {sCodeSize gTS : ℕ} {Consistent NSound Delta1Axiomatized InterpretsR0 : Prop}
    (hS3 : ReflectiveCapacity K sCodeSize gTS Consistent NSound Delta1Axiomatized InterpretsR0)
    (hg : 2 ≤ gTS) :
    ∃ Robj : RealizabilityRecursor.ReflectiveAsm gTS,
      Robj.depth = gTS + 1 ∧
      CapacityLayer.FitsIn (RealizabilityRecursor.recursorAsm Robj.depth)
        (Nat.floor (K - (sCodeSize : ℝ))) ∧
      (GodelThreshold.Incompleteness gnum Derivable True_ gTS →
        ∃ M, GodelThreshold.RepresentsUnderivableTruth gnum Derivable True_ M) := by
  have hpoly : gTS + 1 ≤ gTS ^ 2 := by nlinarith [hg]
  obtain ⟨Robj, hdepth, hfits, hcons⟩ :=
    CategoricalThreshold.categorical_threshold gnum Derivable True_ gTS (gTS + 1)
      (Nat.lt_succ_self gTS) hpoly
  refine ⟨Robj, hdepth, ?_, hcons⟩
  have hle : (GodelInternalization.capacity (Nat.clog 2 (gTS + 1)) : ℝ) ≤ K - (sCodeSize : ℝ) := by
    linarith [hS3.1]
  exact hfits.mono (Nat.le_floor hle)

/-- **Theorem 5.1(b) (Learning branch), restated to carry content.** `(M, U) ∈ 𝒮_L` at
`2 ≤ g(T_S)` delivers `DeliversUnderivableTruth` — [Decoupling] §6.3's genuine payload, reached via
`reflectiveCapacity_fitsIn_headroom`'s capacity-respecting construction, not `ReachesThreshold`'s
now-abandoned `Reflective` stand-in. The proof genuinely consumes (S3) (`h.s3`, via the headroom
bridge) and `2 ≤ gTS` (`categorical_threshold`'s side condition); it does NOT need (S1), (S2), or
any of `𝒮_L`'s five learning-specific fields, for the same reason as before — the destination type
does not ask for them. See the module boundary note for the full accounting, including the honest
fact that `DeliversUnderivableTruth`'s bare conclusion is ALSO reachable from `Incompleteness` alone
(`deliversUnderivableTruth_of_incompleteness_alone`) — this theorem's value is that `𝒮_L` reaches it
through the paper's own intended capacity-bounded mechanism, not that it is the only way there. -/
theorem substrateL_reachesThreshold
    {ι V : Type*} {U : Decoupling.Mem ι V → Decoupling.Mem ι V} {R : Set ι}
    {r K L c₀ c₁ c₂ δ : ℝ} {sCodeSize gTS : ℕ}
    {Consistent NSound Delta1Axiomatized InterpretsR0 : Prop}
    {Realizability WindowSufficiency : Prop}
    {Sentence : Type*} (gnum : Sentence → ℕ) (Derivable True_ : Sentence → Prop)
    (h : SubstrateL U R r K L c₀ c₁ c₂ δ sCodeSize gTS
      Consistent NSound Delta1Axiomatized InterpretsR0 Realizability WindowSufficiency)
    (hg : 2 ≤ gTS) :
    DeliversUnderivableTruth gnum Derivable True_ gTS := by
  intro hInc
  obtain ⟨_Robj, _hdepth, _hfits, hcons⟩ :=
    reflectiveCapacity_fitsIn_headroom gnum Derivable True_ h.s3 hg
  exact hcons hInc

/-! ### The coupled conclusion: binding the payload to the capacity-bounded object's own depth -/

/-- **The coupled reflective-threshold payload.** Unlike `DeliversUnderivableTruth`, which wraps
the payload in `∃ M` and is thereby reachable from bare Gödel numbering alone
(`deliversUnderivableTruth_of_incompleteness_alone` witnesses `M := gTS` directly), this states the
represents-but-cannot-derive fact AT the SAME capacity-bounded object's own depth: `Robj.depth =
gTS + 1` is fixed, its recursor `FitsIn` the host's leftover capacity `⌊K - sCodeSize⌋₊`, and the
payload is stated at `Robj.depth`, not under a second, independent existential. -/
def CoupledDeliverance {Sentence : Type*} (gnum : Sentence → ℕ) (Derivable True_ : Sentence → Prop)
    (K : ℝ) (sCodeSize gTS : ℕ) : Prop :=
  ∃ Robj : RealizabilityRecursor.ReflectiveAsm gTS,
    Robj.depth = gTS + 1 ∧
    CapacityLayer.FitsIn (RealizabilityRecursor.recursorAsm Robj.depth)
      (Nat.floor (K - (sCodeSize : ℝ))) ∧
    (GodelThreshold.Incompleteness gnum Derivable True_ gTS →
      GodelThreshold.RepresentsUnderivableTruth gnum Derivable True_ Robj.depth)

/-- Any `ReflectiveAsm` object carries the payload at its OWN depth: the same route
`RealizabilityRecursor.reflectiveAsm_representsUnderivableTruth` takes via
`GodelThreshold.reflective_of_depth` on the object's `orbit`, kept UNWRAPPED here rather than
packaged under `∃ M`. Both `reflectiveCapacity_coupledDeliverance` and the necessity check below
reuse this rather than reproving it. -/
theorem reflectiveAsm_payload_at_depth
    {Sentence : Type*} (gnum : Sentence → ℕ) (Derivable True_ : Sentence → Prop) {gTS : ℕ}
    (Robj : RealizabilityRecursor.ReflectiveAsm gTS) :
    GodelThreshold.Incompleteness gnum Derivable True_ gTS →
      GodelThreshold.RepresentsUnderivableTruth gnum Derivable True_ Robj.depth := by
  intro hInc
  have hgt : gTS < Robj.orbit.depth := by rw [Robj.orbit_depth]; exact Robj.depth_gt
  have hp := GodelThreshold.reflective_of_depth gnum Derivable True_ Robj.orbit gTS hgt hInc
  rwa [Robj.orbit_depth] at hp

/-- **Theorem 5.1(b), coupled form.** `(S3)` at `2 ≤ g(T_S)` delivers `CoupledDeliverance`: the SAME
reflective object `reflectiveCapacity_fitsIn_headroom` builds also carries the payload at its own
depth, via `reflectiveAsm_payload_at_depth` — the strengthening `substrateL_reachesThreshold`'s
honest-limit note names as not attempted there. -/
theorem reflectiveCapacity_coupledDeliverance
    {Sentence : Type*} (gnum : Sentence → ℕ) (Derivable True_ : Sentence → Prop)
    {K : ℝ} {sCodeSize gTS : ℕ} {Consistent NSound Delta1Axiomatized InterpretsR0 : Prop}
    (hS3 : ReflectiveCapacity K sCodeSize gTS Consistent NSound Delta1Axiomatized InterpretsR0)
    (hg : 2 ≤ gTS) :
    CoupledDeliverance gnum Derivable True_ K sCodeSize gTS := by
  obtain ⟨Robj, hdepth, hfits, -⟩ := reflectiveCapacity_fitsIn_headroom gnum Derivable True_ hS3 hg
  exact ⟨Robj, hdepth, hfits, reflectiveAsm_payload_at_depth gnum Derivable True_ Robj⟩

/-- **Theorem 5.1(b), coupled form, from `𝒮_L` directly.** Consumes only `h.s3` (via
`reflectiveCapacity_coupledDeliverance`) and `2 ≤ g(T_S)` — the same accounting as
`substrateL_reachesThreshold`, now for the coupled conclusion. -/
theorem substrateL_reachesCoupledThreshold
    {ι V : Type*} {U : Decoupling.Mem ι V → Decoupling.Mem ι V} {R : Set ι}
    {r K L c₀ c₁ c₂ δ : ℝ} {sCodeSize gTS : ℕ}
    {Consistent NSound Delta1Axiomatized InterpretsR0 : Prop}
    {Realizability WindowSufficiency : Prop}
    {Sentence : Type*} (gnum : Sentence → ℕ) (Derivable True_ : Sentence → Prop)
    (h : SubstrateL U R r K L c₀ c₁ c₂ δ sCodeSize gTS
      Consistent NSound Delta1Axiomatized InterpretsR0 Realizability WindowSufficiency)
    (hg : 2 ≤ gTS) :
    CoupledDeliverance gnum Derivable True_ K sCodeSize gTS :=
  reflectiveCapacity_coupledDeliverance gnum Derivable True_ h.s3 hg

/-! ### The coupled conclusion at Definition 2.1's own required depth `M_chk := g(T_S) ^ 2`

`CoupledDeliverance` above is instantiated at the SHALLOWEST working depth `categorical_threshold`
admits (`gTS + 1`), below Definition 2.1's own `gTS ^ 2 ≤ M_chk`. This section re-instantiates at
`M_chk := gTS ^ 2` — the depth Definition 2.1 FORCES exactly, since `categorical_threshold` caps
`M_chk ≤ gTS ^ 2` while Definition 2.1 requires `M_chk ≥ poly(gTS)`, and this file's concrete
witness for "poly(gTS)" already IS `gTS ^ 2` (`ReachesThreshold`'s own `Mchk` conjunct). -/

/-- **The coupled reflective-threshold payload, at Definition 2.1's own required depth.**
Identical in shape to `CoupledDeliverance`, but `Robj.depth = gTS ^ 2` rather than `gTS + 1`: the
object's own depth now meets Definition 2.1's `gTS ^ 2 ≤ M_chk` with equality, not merely
`ReachesThreshold`'s free-floating existential. -/
def CoupledDeliveranceAtRequiredDepth {Sentence : Type*} (gnum : Sentence → ℕ)
    (Derivable True_ : Sentence → Prop) (K : ℝ) (sCodeSize gTS : ℕ) : Prop :=
  ∃ Robj : RealizabilityRecursor.ReflectiveAsm gTS,
    Robj.depth = gTS ^ 2 ∧
    CapacityLayer.FitsIn (RealizabilityRecursor.recursorAsm Robj.depth)
      (Nat.floor (K - (sCodeSize : ℝ))) ∧
    (GodelThreshold.Incompleteness gnum Derivable True_ gTS →
      GodelThreshold.RepresentsUnderivableTruth gnum Derivable True_ Robj.depth)

/-- **The capacity bridge, at the required depth.** Same idiom as
`reflectiveCapacity_fitsIn_headroom` — (S3)'s inequality composed with `categorical_threshold`'s
`FitsIn` conclusion via the ℝ/ℕ floor bound — but at working depth `M_chk := gTS ^ 2`:
`categorical_threshold` applies directly, since `gTS < gTS ^ 2` holds at `2 ≤ gTS` and
`gTS ^ 2 ≤ gTS ^ 2` is `le_refl`. -/
theorem reflectiveCapacity_fitsIn_headroom_atRequiredDepth
    {Sentence : Type*} (gnum : Sentence → ℕ) (Derivable True_ : Sentence → Prop)
    {K : ℝ} {sCodeSize gTS : ℕ} {Consistent NSound Delta1Axiomatized InterpretsR0 : Prop}
    (hS3 : ReflectiveCapacity K sCodeSize gTS Consistent NSound Delta1Axiomatized InterpretsR0)
    (hg : 2 ≤ gTS) :
    ∃ Robj : RealizabilityRecursor.ReflectiveAsm gTS,
      Robj.depth = gTS ^ 2 ∧
      CapacityLayer.FitsIn (RealizabilityRecursor.recursorAsm Robj.depth)
        (Nat.floor (K - (sCodeSize : ℝ))) ∧
      (GodelThreshold.Incompleteness gnum Derivable True_ gTS →
        ∃ M, GodelThreshold.RepresentsUnderivableTruth gnum Derivable True_ M) := by
  have hidx : gTS < gTS ^ 2 := by nlinarith [hg]
  obtain ⟨Robj, hdepth, hfits, hcons⟩ :=
    CategoricalThreshold.categorical_threshold gnum Derivable True_ gTS (gTS ^ 2) hidx (le_refl _)
  refine ⟨Robj, hdepth, ?_, hcons⟩
  have hle : (GodelInternalization.capacity (Nat.clog 2 (gTS + 1)) : ℝ) ≤ K - (sCodeSize : ℝ) := by
    linarith [hS3.1]
  exact hfits.mono (Nat.le_floor hle)

/-- **Theorem 5.1(b), coupled form, at the required depth.** The SAME object
`reflectiveCapacity_fitsIn_headroom_atRequiredDepth` builds also carries the payload at its own
depth, via `reflectiveAsm_payload_at_depth` — exactly
`reflectiveCapacity_coupledDeliverance`'s move, now at `M_chk = gTS ^ 2`. -/
theorem reflectiveCapacity_coupledDeliverance_atRequiredDepth
    {Sentence : Type*} (gnum : Sentence → ℕ) (Derivable True_ : Sentence → Prop)
    {K : ℝ} {sCodeSize gTS : ℕ} {Consistent NSound Delta1Axiomatized InterpretsR0 : Prop}
    (hS3 : ReflectiveCapacity K sCodeSize gTS Consistent NSound Delta1Axiomatized InterpretsR0)
    (hg : 2 ≤ gTS) :
    CoupledDeliveranceAtRequiredDepth gnum Derivable True_ K sCodeSize gTS := by
  obtain ⟨Robj, hdepth, hfits, -⟩ :=
    reflectiveCapacity_fitsIn_headroom_atRequiredDepth gnum Derivable True_ hS3 hg
  exact ⟨Robj, hdepth, hfits, reflectiveAsm_payload_at_depth gnum Derivable True_ Robj⟩

/-- **Theorem 5.1(b), coupled form at the required depth, from `𝒮_L` directly.** Consumes only
`h.s3` and `2 ≤ g(T_S)` — the same accounting as `substrateL_reachesCoupledThreshold`, now at
`M_chk = gTS ^ 2`. -/
theorem substrateL_reachesCoupledThresholdAtRequiredDepth
    {ι V : Type*} {U : Decoupling.Mem ι V → Decoupling.Mem ι V} {R : Set ι}
    {r K L c₀ c₁ c₂ δ : ℝ} {sCodeSize gTS : ℕ}
    {Consistent NSound Delta1Axiomatized InterpretsR0 : Prop}
    {Realizability WindowSufficiency : Prop}
    {Sentence : Type*} (gnum : Sentence → ℕ) (Derivable True_ : Sentence → Prop)
    (h : SubstrateL U R r K L c₀ c₁ c₂ δ sCodeSize gTS
      Consistent NSound Delta1Axiomatized InterpretsR0 Realizability WindowSufficiency)
    (hg : 2 ≤ gTS) :
    CoupledDeliveranceAtRequiredDepth gnum Derivable True_ K sCodeSize gTS :=
  reflectiveCapacity_coupledDeliverance_atRequiredDepth gnum Derivable True_ h.s3 hg

/-- **The required-depth witness meets the TIED depth clause — unlike the `gTS + 1` witness.**
Any object at `Robj.depth = gTS ^ 2` satisfies `ReachesThresholdAtDepth`'s depth conjuncts with
room to spare: `gTS ≤ gTS ^ 2` (needs only `1 ≤ gTS`) and `gTS ^ 2 ≤ gTS ^ 2` by `le_refl`.
Contrast the `gTS + 1` witness `CoupledDeliverance` builds, for which the second conjunct —
`gTS ^ 2 ≤ gTS + 1` — FAILS at every `gTS ≥ 2`
(`coupledDeliverance_fitsIn_below_paperCapacity`'s own side condition is exactly `2 ≤ gTS`, where
`gTS + 1 < gTS ^ 2`). This is the sense in which the required-depth form, and only it, is a
genuine `ReachesThresholdAtDepth` witness. -/
theorem coupledAtRequiredDepth_reachesThresholdAtDepth
    {Consistent NSound Delta1Axiomatized InterpretsR0 : Prop}
    (hthy : TheoryConditions Consistent NSound Delta1Axiomatized InterpretsR0)
    {gTS : ℕ} (hg : 2 ≤ gTS) {Robj : RealizabilityRecursor.ReflectiveAsm gTS}
    (hdepth : Robj.depth = gTS ^ 2) :
    ReachesThresholdAtDepth Consistent NSound Delta1Axiomatized InterpretsR0 gTS Robj := by
  refine ⟨ReflectiveAssembly.reflective_satisfiable gTS, hthy, ?_, ?_⟩
  · rw [hdepth]; nlinarith [hg]
  · rw [hdepth]

/-! ### The necessity direction, checked — and it does NOT hold as posed -/

/-- **The paper's `capacity n` figure is not the tight budget for THIS fixed depth.** At the SAME
working depth `gTS + 1` the coupled conclusion fixes, the recursor's carrier has exactly
`gTS + 1 + 1` elements, so `FitsIn` already holds at `Nat.clog 2 (gTS + 1) + 1` work bits — strictly
BELOW the paper's `capacity n = 2 * n` once `2 ≤ g(T_S)` (`n ≥ 2`, so `n + 1 < 2 * n`).
`GodelInternalization.capacity_bound`'s `2n` is a uniform bound valid for every working depth up to
`g(T_S)²`, not the amount THIS single depth `g(T_S) + 1` needs. -/
theorem coupledDeliverance_fitsIn_below_paperCapacity {gTS : ℕ} (hg : 2 ≤ gTS) :
    CapacityLayer.FitsIn (RealizabilityRecursor.recursorAsm (gTS + 1))
        (Nat.clog 2 (gTS + 1) + 1) ∧
      Nat.clog 2 (gTS + 1) + 1 < GodelInternalization.capacity (Nat.clog 2 (gTS + 1)) := by
  have h1 : (2 : ℕ) ^ 1 < gTS + 1 := by rw [pow_one]; omega
  have hn2 : 1 < Nat.clog 2 (gTS + 1) := (Nat.lt_clog_iff_pow_lt (by norm_num)).mpr h1
  have hg1 : gTS + 1 ≤ 2 ^ Nat.clog 2 (gTS + 1) := Nat.le_pow_clog (by norm_num) _
  have hpow : (2 : ℕ) ^ (Nat.clog 2 (gTS + 1) + 1) = 2 ^ Nat.clog 2 (gTS + 1) * 2 :=
    pow_succ 2 _
  have hcard : gTS + 1 + 1 ≤ 2 ^ (Nat.clog 2 (gTS + 1) + 1) := by rw [hpow]; omega
  refine ⟨CapacityLayer.recursorAsm_fitsIn (gTS + 1) (Nat.clog 2 (gTS + 1) + 1) hcard, ?_⟩
  simp only [GodelInternalization.capacity]
  omega

/-- **The necessity direction, refuted as stated.** At every `2 ≤ g(T_S)`, `CoupledDeliverance` is
already reachable at a host capacity `K` strictly BELOW `sCodeSize + capacity n` — the parameter
regime the necessity direction names as "insufficient". So neither `substrateL_reachesThreshold` nor
`reflectiveCapacity_coupledDeliverance`'s hypotheses, even coupled to the object's own depth, are
NECESSARY for the coupled conclusion at the paper's own `capacity n = 2n` figure: that figure
over-provisions for the fixed depth `g(T_S) + 1` (`coupledDeliverance_fitsIn_below_paperCapacity`
gives the exact slack). What `(S3)` at `capacity n` certifies is a genuine capacity-respecting
witness — `reflectiveCapacity_coupledDeliverance` itself — not the cheapest possible one.

SCOPE, and it is narrow: this refutation is about the single depth `g(T_S) + 1` that
`CoupledDeliverance` fixes, and that depth is strictly BELOW the working depth the reflective
threshold itself requires (`ReachesThreshold` asks `g(T_S)^2 ≤ M_chk`, and `g + 1 < g^2` for
`2 ≤ g`). So this does NOT show the `2n` figure is loose where it is actually used: at
`M_chk = g(T_S)^2`, `capacity_bound`'s own chain `M_chk + 1 ≤ (g+1)^2 ≤ (2^n)^2` runs tight, and
one bit less does not suffice when `g + 1` is a power of two. Re-instantiating the coupled
conclusion at that required depth is the open item. -/
theorem coupledDeliverance_not_necessary_at_paperCapacity
    {Sentence : Type*} (gnum : Sentence → ℕ) (Derivable True_ : Sentence → Prop)
    {gTS : ℕ} (hg : 2 ≤ gTS) (sCodeSize : ℕ) :
    ∃ K : ℝ, K < (sCodeSize : ℝ) + (GodelInternalization.capacity (Nat.clog 2 (gTS + 1)) : ℝ) ∧
      CoupledDeliverance gnum Derivable True_ K sCodeSize gTS := by
  obtain ⟨hfits, hslack⟩ := coupledDeliverance_fitsIn_below_paperCapacity hg
  refine ⟨(sCodeSize : ℝ) + (Nat.clog 2 (gTS + 1) + 1 : ℕ), ?_,
    CategoricalThreshold.reflectiveAsm_satisfiable_depth gTS (gTS + 1) (Nat.lt_succ_self gTS),
    rfl, ?_,
    reflectiveAsm_payload_at_depth gnum Derivable True_
      (CategoricalThreshold.reflectiveAsm_satisfiable_depth gTS (gTS + 1) (Nat.lt_succ_self gTS))⟩
  · have hcast : ((Nat.clog 2 (gTS + 1) + 1 : ℕ) : ℝ)
        < (GodelInternalization.capacity (Nat.clog 2 (gTS + 1)) : ℝ) := by exact_mod_cast hslack
    linarith
  · have hK : (sCodeSize : ℝ) + (Nat.clog 2 (gTS + 1) + 1 : ℕ) - (sCodeSize : ℝ)
        = ((Nat.clog 2 (gTS + 1) + 1 : ℕ) : ℝ) := by ring
    rw [hK, Nat.floor_natCast]
    exact hfits

/-! ### Necessity at the required depth: exact on the family `g(T_S) = 2 ^ n - 1`, slack off it

`coupledDeliverance_not_necessary_at_paperCapacity` above is scoped to the shallow depth
`gTS + 1`, where the paper's `capacity n = 2n` was shown to over-provision. At the REQUIRED depth
`gTS ^ 2` the question re-opens: is `capacity n` load-bearing there? The answer is family-dependent.
On `g(T_S) = 2 ^ n - 1` (so `g(T_S) + 1 = 2 ^ n` exactly, `Nat.clog` exact), `capacity n` cannot
be relaxed by even one bit. Off that family — witnessed here at `g(T_S) = 2 ^ m` — it still can
be. -/

/-- On the family `g(T_S) = 2 ^ n - 1`, `Nat.clog 2 (g(T_S) + 1) = n` exactly (`g(T_S) + 1 = 2 ^ n`
is a power of two on the nose, not merely bounded by one). -/
theorem tightFamily_capacity_exact (n : ℕ) (hn : 2 ≤ n) :
    Nat.clog 2 ((2 ^ n - 1) + 1) = n := by
  have h4 : (4 : ℕ) ≤ 2 ^ n := by
    calc (4 : ℕ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have heq : (2 ^ n - 1) + 1 = 2 ^ n := by omega
  rw [heq]
  exact Nat.clog_pow 2 n (by norm_num)

/-- **The tight family: `capacity n` cannot be relaxed by even one bit.** At `g(T_S) = 2 ^ n - 1`,
the recursor at the REQUIRED working depth `g(T_S) ^ 2` (carrier `g(T_S) ^ 2 + 1` elements) does
NOT `FitsIn` one bit under `capacity n = 2n`: `(2^n-1)^2 + 1 > 2^(2n-1)`, the exact-power identity
`2^(2n) = (2^n)^2` reducing this to `(g(T_S) - 1)^2 > 0` at `g(T_S) = 2^n - 1 ≥ 3`. -/
theorem tightFamily_not_fitsIn_capacityMinusOne (n : ℕ) (hn : 2 ≤ n) :
    ¬ CapacityLayer.FitsIn (RealizabilityRecursor.recursorAsm ((2 ^ n - 1) ^ 2))
        (GodelInternalization.capacity n - 1) := by
  have h4 : (4 : ℕ) ≤ 2 ^ n := by
    calc (4 : ℕ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  set g := 2 ^ n - 1 with hgdef
  have hg1 : g + 1 = 2 ^ n := by omega
  have hg3 : 3 ≤ g := by omega
  rintro ⟨-, hcard⟩
  have heq : Nat.card (RealizabilityRecursor.recursorAsm (g ^ 2)).carrier = g ^ 2 + 1 := by
    simp [Nat.card_eq_fintype_card, ZMod.card]
  rw [heq] at hcard
  simp only [GodelInternalization.capacity] at hcard
  -- hcard : g ^ 2 + 1 ≤ 2 ^ (2 * n - 1)
  have hpowsucc : (2 : ℕ) * 2 ^ (2 * n - 1) = 2 ^ (2 * n) := by
    rw [← pow_succ']; congr 1; omega
  have hpoweq : (2 : ℕ) ^ (2 * n) = (g + 1) * (g + 1) := by
    rw [two_mul, pow_add, ← hg1]
  have hcard2 : 2 * (g ^ 2 + 1) ≤ 2 * 2 ^ (2 * n - 1) := Nat.mul_le_mul (le_refl 2) hcard
  rw [hpowsucc, hpoweq] at hcard2
  have hexpand : (g + 1) * (g + 1) = g * g + 2 * g + 1 := by ring
  have hgsq : g ^ 2 = g * g := pow_two g
  rw [hexpand, hgsq] at hcard2
  nlinarith [hcard2, hg3]

/-- **Necessity, on the tight family.** At `g(T_S) = 2 ^ n - 1` (`2 ≤ n`), the coupled
conclusion at the REQUIRED depth fails whenever the host's leftover capacity
`⌊K - sCodeSize⌋₊` falls even one bit short of the paper's `capacity n = 2n`: `(S3)` at the
paper's own figure is genuinely load-bearing here — unlike at the shallow `gTS + 1` depth, where
`coupledDeliverance_not_necessary_at_paperCapacity` refutes it. -/
theorem coupledAtRequiredDepth_not_reachable_below_paperCapacity_on_family
    {n : ℕ} (hn : 2 ≤ n) {K : ℝ} {sCodeSize : ℕ}
    (hK : Nat.floor (K - (sCodeSize : ℝ)) < GodelInternalization.capacity n)
    {Sentence : Type*} (gnum : Sentence → ℕ) (Derivable True_ : Sentence → Prop) :
    ¬ CoupledDeliveranceAtRequiredDepth gnum Derivable True_ K sCodeSize (2 ^ n - 1) := by
  rintro ⟨Robj, hdepth, hfits, -⟩
  rw [hdepth] at hfits
  exact tightFamily_not_fitsIn_capacityMinusOne n hn (hfits.mono (by omega))

/-- Off the tight family, `Nat.clog` is no longer exact at `g(T_S) + 1`: at `g(T_S) = 2 ^ m`
(`1 ≤ m`), `g(T_S) + 1 = 2^m + 1` sits one past a power of two, so `Nat.clog 2 (g(T_S)+1) = m + 1`
— the SAME value the tight family's neighbouring index `n = m + 1` gives, but now approached from
below rather than hit exactly. -/
theorem offFamily_capacity_exact (m : ℕ) (_hm : 1 ≤ m) :
    Nat.clog 2 (2 ^ m + 1) = m + 1 := by
  have h2m : (1 : ℕ) ≤ 2 ^ m := by have := Nat.two_pow_pos m; omega
  have hle : (2 : ℕ) ^ m + 1 ≤ 2 ^ (m + 1) := by rw [pow_succ]; omega
  have hlt : (2 : ℕ) ^ m < 2 ^ m + 1 := by omega
  have h1 : Nat.clog 2 (2 ^ m + 1) ≤ m + 1 := Nat.clog_le_of_le_pow hle
  have h2 : m < Nat.clog 2 (2 ^ m + 1) := (Nat.lt_clog_iff_pow_lt (by norm_num)).mpr hlt
  omega

/-- **Off-family slack, at the REQUIRED depth.** At `g(T_S) = 2 ^ m` (`1 ≤ m`), the recursor at
the required working depth `g(T_S) ^ 2` already `FitsIn` `capacity (Nat.clog 2 (g(T_S)+1)) - 1`
work bits — one bit under the paper's own figure at this index (`offFamily_capacity_exact`
identifies that figure as `capacity (m+1)`) — the same over-provisioning phenomenon
`coupledDeliverance_fitsIn_below_paperCapacity` records at the shallow depth, now checked at the
depth Definition 2.1 actually requires. Concretely reaches the user's own worked instances
`g(T_S) = 2` (`m = 1`) and `g(T_S) = 4` (`m = 2`). -/
theorem offFamily_fitsIn_below_paperCapacity_atRequiredDepth (m : ℕ) (hm : 1 ≤ m) :
    CapacityLayer.FitsIn (RealizabilityRecursor.recursorAsm ((2 ^ m) ^ 2))
      (GodelInternalization.capacity (Nat.clog 2 (2 ^ m + 1)) - 1) := by
  rw [offFamily_capacity_exact m hm]
  have h2m : (1 : ℕ) ≤ 2 ^ m := by have := Nat.two_pow_pos m; omega
  apply CapacityLayer.recursorAsm_fitsIn
  simp only [GodelInternalization.capacity]
  -- goal: (2 ^ m) ^ 2 + 1 ≤ 2 ^ (2 * (m + 1) - 1)
  have hpowsucc : (2 : ℕ) ^ (2 * (m + 1) - 1) * 2 = 2 ^ (2 * (m + 1)) := by
    rw [← pow_succ]; congr 1
  have hpoweq : (2 : ℕ) ^ (2 * (m + 1)) = 2 ^ m * 2 * (2 ^ m * 2) := by
    have hstep : (2 : ℕ) ^ (m + 1) = 2 ^ m * 2 := pow_succ 2 m
    rw [two_mul, pow_add, hstep]
  have hone : (1 : ℕ) * 1 ≤ 2 ^ m * 2 ^ m := Nat.mul_le_mul h2m h2m
  have hsq : (2 ^ m) ^ 2 = 2 ^ m * 2 ^ m := pow_two (2 ^ m)
  have hgoal2 : ((2 ^ m) ^ 2 + 1) * 2 ≤ 2 ^ (2 * (m + 1) - 1) * 2 := by
    rw [hpowsucc, hpoweq, hsq]; nlinarith [hone]
  exact le_of_mul_le_mul_right hgoal2 (by norm_num)

/-! ### The membership predicate on the two families, and Definition 2.1's rewiring

The results above are about `CoupledDeliveranceAtRequiredDepth` — a *conclusion* reached from the
threshold. This section carries the same boundary over to the threshold's own MEMBERSHIP condition
`ReachesThresholdWithin`: exact at the paper's capacity figure on the tight family, with slack off
it, and discharged by the coupled chain from its own witness. -/

/-- The counting core of the tight family, stated once and reused. One bit under the paper's figure,
`2 ^ (capacity n - 1) = 2 ^ (2n - 1)` values, is strictly fewer than the `g(T_S) ^ 2 + 1` a recursor
at the REQUIRED working depth carries, at `g(T_S) = 2 ^ n - 1` (`2 ≤ n`): doubling both sides turns
the claim into `(g+1)^2 ≤ 2·g²`, i.e. `2g + 1 ≤ g²`, which holds from `g ≥ 3`. -/
theorem tightFamily_capacityMinusOne_lt_requiredCard (n : ℕ) (hn : 2 ≤ n) :
    2 ^ (GodelInternalization.capacity n - 1) < (2 ^ n - 1) ^ 2 + 1 := by
  have h4 : (4 : ℕ) ≤ 2 ^ n := by
    calc (4 : ℕ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  set g := 2 ^ n - 1 with hgdef
  have hg1 : g + 1 = 2 ^ n := by omega
  have hg3 : 3 ≤ g := by omega
  simp only [GodelInternalization.capacity]
  have hpowsucc : (2 : ℕ) * 2 ^ (2 * n - 1) = 2 ^ (2 * n) := by
    rw [← pow_succ']; congr 1; omega
  have hpoweq : (2 : ℕ) ^ (2 * n) = (g + 1) * (g + 1) := by
    rw [two_mul, pow_add, ← hg1]
  have hdouble : 2 * 2 ^ (2 * n - 1) ≤ 2 * g ^ 2 := by
    rw [hpowsucc, hpoweq]; nlinarith [hg3]
  exact Nat.lt_succ_of_le (Nat.le_of_mul_le_mul_left hdouble (by norm_num))

/-- **The tight family, at ANY depth Definition 2.1 admits.** `tightFamily_not_fitsIn_capacityMinusOne`
refutes the fit at the required depth exactly; this generalizes it to every working depth
`M_chk ≥ g(T_S) ^ 2` — the whole range Definition 2.1's `M_chk ≥ poly(g(T_S))` allows — since a
deeper recursor only carries more values. This is the form the membership predicate needs, whose
witness fixes no particular depth. -/
theorem tightFamily_not_fitsIn_capacityMinusOne_atDepth {n M : ℕ} (hn : 2 ≤ n)
    (hM : (2 ^ n - 1) ^ 2 ≤ M) :
    ¬ CapacityLayer.FitsIn (RealizabilityRecursor.recursorAsm M)
        (GodelInternalization.capacity n - 1) := by
  rintro ⟨-, hcard⟩
  have heq : Nat.card (RealizabilityRecursor.recursorAsm M).carrier = M + 1 := by
    simp [Nat.card_eq_fintype_card, ZMod.card]
  rw [heq] at hcard
  have hlt : M + 1 < (2 ^ n - 1) ^ 2 + 1 :=
    lt_of_le_of_lt hcard (tightFamily_capacityMinusOne_lt_requiredCard n hn)
  exact absurd hM (Nat.not_le.mpr (Nat.lt_of_succ_lt_succ hlt))

/-- **The exact threshold on the tight family.** At `g(T_S) = 2 ^ n - 1` (`2 ≤ n`) the membership
condition `CategoricalThreshold.ReflectiveWithin` is reached **iff** the work budget meets the
paper's own capacity figure `capacity n = 2n` — an equivalence, not a sufficiency:

* *(⇐)* `CategoricalThreshold.reflectiveWithin_at_capacity` at `g(T_S) = 2 ^ n - 1` (where
  `2 ≤ g(T_S)` from `2 ≤ n`), rewritten by `tightFamily_capacity_exact`, then pushed up by
  monotonicity;
* *(⇒)* one bit short already fails, at every admissible depth
  (`tightFamily_not_fitsIn_capacityMinusOne_atDepth`).

This is the sharp statement the coupled results could not make: they fix a depth and refute the fit
there, whereas membership quantifies over the witness's own depth, and the bound survives it. -/
theorem tightFamily_reflectiveWithin_iff {n : ℕ} (hn : 2 ≤ n) (w : ℕ) :
    CategoricalThreshold.ReflectiveWithin w (2 ^ n - 1) ↔
      GodelInternalization.capacity n ≤ w := by
  have h4 : (4 : ℕ) ≤ 2 ^ n := by
    calc (4 : ℕ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  constructor
  · rintro ⟨R, hdepth, hfits⟩
    by_contra hlt
    exact tightFamily_not_fitsIn_capacityMinusOne_atDepth hn hdepth (hfits.mono (by omega))
  · intro hcap
    have hg : 2 ≤ 2 ^ n - 1 := by omega
    have h := CategoricalThreshold.reflectiveWithin_at_capacity hg
    rw [tightFamily_capacity_exact n hn] at h
    exact h.mono hcap

/-- **Off-family slack, for membership.** At `g(T_S) = 2 ^ m` (`1 ≤ m`) the membership condition is
already reached one bit UNDER the paper's figure at this index — the witness is the required-depth
object `g(T_S) ^ 2`, and the fit is exactly `offFamily_fitsIn_below_paperCapacity_atRequiredDepth`.
Together with `tightFamily_reflectiveWithin_iff` this settles the shape of the boundary for
membership as it was already settled for the coupled conclusion: the necessity of the `2n` figure is
family-dependent, and no general characterization is claimed. -/
theorem offFamily_reflectiveWithin_below_capacity (m : ℕ) (hm : 1 ≤ m) :
    CategoricalThreshold.ReflectiveWithin
      (GodelInternalization.capacity (Nat.clog 2 (2 ^ m + 1)) - 1) (2 ^ m) := by
  have h2 : (2 : ℕ) ≤ 2 ^ m := by
    calc (2 : ℕ) = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  have hidx : 2 ^ m < (2 ^ m) ^ 2 := by nlinarith
  exact ⟨CategoricalThreshold.reflectiveAsm_satisfiable_depth (2 ^ m) ((2 ^ m) ^ 2) hidx,
    le_refl _, offFamily_fitsIn_below_paperCapacity_atRequiredDepth m hm⟩

/-- **`𝒮_L` reaches the content-carrying threshold, at its own headroom.** `(M, U) ∈ 𝒮_L` at
`2 ≤ g(T_S)` satisfies `ReachesThresholdWithin` at the work budget the host has left after its code
region, `⌊K − |s_code|⌋₊`: (S3)'s inequality covers `capacity n`, and
`CategoricalThreshold.reflectiveWithin_at_capacity` supplies the object there, monotonicity carrying
it to the headroom (the `reflectiveCapacity_fitsIn_headroom` idiom, now landing in the membership
predicate). The theory conditions are (S3)'s own second component.

This is `substrateL_reachesThreshold`'s destination with the vacuity removed: that theorem's target
`DeliversUnderivableTruth` is reachable from imported incompleteness alone, and
`ReachesThreshold`'s categorical clause is satisfiable for every Gödel number — whereas this
target FAILS below the sentence size, and, on the tight family, fails at every budget under
`capacity n` (`reachesThresholdWithin_not_reachable_below_paperCapacity_on_family`). The proof
consumes (S3) and `2 ≤ g(T_S)`, and — as everywhere on this route — neither (S1), (S2), nor 𝒮_L's
five learning-specific fields. -/
theorem substrateL_reachesThresholdWithin
    {ι V : Type*} {U : Decoupling.Mem ι V → Decoupling.Mem ι V} {R : Set ι}
    {r K L c₀ c₁ c₂ δ : ℝ} {sCodeSize gTS : ℕ}
    {Consistent NSound Delta1Axiomatized InterpretsR0 : Prop}
    {Realizability WindowSufficiency : Prop}
    (h : SubstrateL U R r K L c₀ c₁ c₂ δ sCodeSize gTS
      Consistent NSound Delta1Axiomatized InterpretsR0 Realizability WindowSufficiency)
    (hg : 2 ≤ gTS) :
    ReachesThresholdWithin Consistent NSound Delta1Axiomatized InterpretsR0
      (Nat.floor (K - (sCodeSize : ℝ))) gTS := by
  have hle : (GodelInternalization.capacity (Nat.clog 2 (gTS + 1)) : ℝ) ≤ K - (sCodeSize : ℝ) := by
    linarith [h.s3.1]
  exact ⟨(CategoricalThreshold.reflectiveWithin_at_capacity hg).mono (Nat.le_floor hle), h.s3.2⟩

/-- **(S3)-shaped capacity is necessary for MEMBERSHIP, on the tight family.** At
`g(T_S) = 2 ^ n - 1` (`2 ≤ n`), a host whose leftover capacity `⌊K − |s_code|⌋₊` falls even one bit
short of `capacity n = 2n` does not reach `ReachesThresholdWithin` at all — by
`tightFamily_reflectiveWithin_iff`'s forward direction, and independently of the four theory
conditions, which the failing conjunct is not.

This is the sentence the boundary notes above could not write. The coupled counterpart
`coupledAtRequiredDepth_not_reachable_below_paperCapacity_on_family` establishes the same budget
boundary for the coupled *conclusion*; here it holds for Definition 2.1's own membership condition,
so on this family (S3) at the paper's literal figure is load-bearing for *being* a system that
reaches the threshold, not only for what such a system then delivers. Off the family the necessity again fails
(`offFamily_reflectiveWithin_below_capacity`), exactly as for the coupled conclusion. -/
theorem reachesThresholdWithin_not_reachable_below_paperCapacity_on_family
    {n : ℕ} (hn : 2 ≤ n) {K : ℝ} {sCodeSize : ℕ}
    (hK : Nat.floor (K - (sCodeSize : ℝ)) < GodelInternalization.capacity n)
    (Consistent NSound Delta1Axiomatized InterpretsR0 : Prop) :
    ¬ ReachesThresholdWithin Consistent NSound Delta1Axiomatized InterpretsR0
      (Nat.floor (K - (sCodeSize : ℝ))) (2 ^ n - 1) := by
  rintro ⟨hrw, -⟩
  exact absurd ((tightFamily_reflectiveWithin_iff hn _).mp hrw) (Nat.not_le.mpr hK)

/-- **The coupled chain discharges the new clause from its OWN witness.** A
`CoupledDeliveranceAtRequiredDepth` witness already is a `ReflectiveWithin` witness at the same
budget: its object sits at depth `g(T_S) ^ 2` (meeting Definition 2.1's working-depth demand with
equality) and its recursor already `FitsIn` the host's leftover capacity — the two conjuncts, on the
one object, with nothing added.

Contrast `coupledAtRequiredDepth_reachesThresholdAtDepth`, which discharges its reflective conjunct
by `ReflectiveAssembly.reflective_satisfiable`, available unconditionally for every Gödel number and
therefore carrying no information about the host. Here the witness's own `FitsIn` does that work, so
the conclusion inherits the budget. The theory conditions are carried in, as everywhere. -/
theorem coupledAtRequiredDepth_reachesThresholdWithin
    {Sentence : Type*} (gnum : Sentence → ℕ) (Derivable True_ : Sentence → Prop)
    {K : ℝ} {sCodeSize gTS : ℕ}
    {Consistent NSound Delta1Axiomatized InterpretsR0 : Prop}
    (hthy : TheoryConditions Consistent NSound Delta1Axiomatized InterpretsR0)
    (hc : CoupledDeliveranceAtRequiredDepth gnum Derivable True_ K sCodeSize gTS) :
    ReachesThresholdWithin Consistent NSound Delta1Axiomatized InterpretsR0
      (Nat.floor (K - (sCodeSize : ℝ))) gTS := by
  obtain ⟨Robj, hdepth, hfits, -⟩ := hc
  exact ⟨⟨Robj, by rw [hdepth], hfits⟩, hthy⟩

/-- **(S3) is not implied by (S2).** [Inevitability] §2 names conflating them "the standing trap
on this route": C1 buys capacity to represent the rule, (S3) buys capacity to host the checker.
Witness: the regime constants of `RegimeConsistency.regime_satisfiable`
(`r=3, K=100, L=200, c₀=1, c₁=2, c₂=3, δ=1/2`), with a code size (`sCodeSize = 1000`) that alone
already exceeds `K = 100` — (S2) never bounds `sCodeSize` at all, so it is free to blow the
capacity inequality regardless of the theory conditions (`True` throughout). -/
theorem s3_not_implied_by_s2 :
    ∃ (r K L c₀ c₁ c₂ δ : ℝ) (sCodeSize gTS : ℕ)
      (Consistent NSound Delta1Axiomatized InterpretsR0 : Prop),
      RegimeWithDepth r K L c₀ c₁ c₂ δ ∧
        ¬ ReflectiveCapacity K sCodeSize gTS Consistent NSound Delta1Axiomatized InterpretsR0 := by
  refine ⟨3, 100, 200, 1, 2, 3, 1 / 2, 1000, 0, True, True, True, True, ?_, ?_⟩
  · have h : Real.log (3 / (1 / 2)) ≤ 3 / (1 / 2) - 1 :=
      Real.log_le_sub_one_of_pos (by norm_num)
    refine ⟨by nlinarith [h], by norm_num, by norm_num, by norm_num, by norm_num, by norm_num,
      by norm_num, by norm_num⟩
  · rintro ⟨hK, -⟩
    norm_num [GodelInternalization.capacity] at hK

/-- **Non-vacuity, at a Gödel number the capacity bridge actually reaches.** The bare `Substrate`
structure is satisfiable at `gTS = 2` — where `reflectiveCapacity_fitsIn_headroom`'s side condition
`2 ≤ gTS` first holds, and the capacity term `2 * Nat.clog 2 (gTS+1) = 4` is genuinely positive, not
the degenerate `0` a `gTS = 0` witness gives (`s3` would then be free of any real bound). The
identity update fixes every cell (S1, trivially); the concrete regime constants `r=3, K=100,
L=200, c₀=1, c₁=2, c₂=3, δ=1/2` — the same values `RegimeConsistency.regime_satisfiable` uses —
meet (S2); a zero code size meets (S3) since `0 + 4 ≤ 100`, with the four theory conditions
trivially `True`. This shows Definitions 2.1–2.3 are not statements about an empty class, at a
witness the capacity bridge is non-vacuous for (unlike the previous `gTS = 0` witness). -/
theorem substrate_satisfiable :
    ∃ (ι V : Type) (U : Decoupling.Mem ι V → Decoupling.Mem ι V) (R : Set ι)
      (r K L c₀ c₁ c₂ δ : ℝ) (sCodeSize gTS : ℕ)
      (Consistent NSound Delta1Axiomatized InterpretsR0 : Prop),
      Substrate U R r K L c₀ c₁ c₂ δ sCodeSize gTS Consistent NSound Delta1Axiomatized InterpretsR0 := by
  refine ⟨Unit, Bool, id, Set.univ, 3, 100, 200, 1, 2, 3, 1 / 2, 0, 2, True, True, True, True, ?_⟩
  have hlog : Real.log (3 / (1 / 2)) ≤ 3 / (1 / 2) - 1 :=
    Real.log_le_sub_one_of_pos (by norm_num)
  refine ⟨fun _ _ _ => rfl,
    ⟨by nlinarith [hlog], by norm_num, by norm_num, by norm_num, by norm_num, by norm_num,
      by norm_num, by norm_num⟩, ?_⟩
  have hcap : GodelInternalization.capacity (Nat.clog 2 (2 + 1)) = 4 := by decide
  refine ⟨by rw [hcap]; norm_num, trivial, trivial, trivial, trivial⟩

/-! ### The time-indexed form: a committed configuration, and what (S1) buys it

Everything above is atemporal, and Definition 2.1 stays that way: [Inevitability] §5 Remark 5.5 is
explicit that a time-indexed *definition* would demand an unbounded persistence neither route can
prove, so the crossing is defined instantaneously and its persistence priced separately. That
remark also fixes what the learning branch's price is — "(S1) makes the code region read-only, so
the committed rule survives iteration ([Decoupling] Lemma 3.1) and [Discovery] Proposition 4.2
bounds forgetting by the probability that the code region is itself overwritten: the reflective
configuration recurs at every later step on which (S3) still holds."

This section renders exactly that sentence, as a predicate added ALONGSIDE the three above (the
`ReachesThresholdAtDepth`/`ReachesThresholdWithin` precedent — none of them is modified). It is
where (S1) attaches: `substrate_reachesThresholdWithinAt_persists` is the first theorem in this
development to consume `Substrate`'s `s1` field at all, the boundary note above having recorded
that field as carried and unconsumed.

**Scope, deliberately narrow.** (S2) and `SubstrateL`'s five learning fields are still unconsumed
here, and nothing below moves toward them. Consuming those is the *discovery* half — that learning
PRODUCES the committed configuration — which needs the learner inside the substrate's own
dynamics; no object in this development supplies that, and the predicate below neither states nor
approximates it. What it states is retention only: given a commitment, read-only code keeps it. -/

/-- **A configuration committed to a reference codeword on the code region.** `s` agrees with the
pinned `ρ` at every cell of `R` — "the code region carries *this* model", stated on raw memories
rather than through a decoder, so it composes directly with `Decoupling.fixes_iterate`.

**The pin carries the whole content.** With `ρ` left free this predicate says nothing: every
configuration is committed to its own content (`CommittedOn R s s` holds by `rfl`, at every `R`),
so an unpinned reading of the time-indexed threshold below would be satisfied by any orbit
whatsoever at `t = 0`. It acquires content only against a `ρ` fixed independently of the orbit —
as `LearningWitness.witness_reachesThresholdWithinAt` pins it to the loaded rule encoding, on the
region whose contents that witness's update provably reads. This is the same lesson `SubstrateL`'s
`e1` field records for E1's mixing constant: a free or existentially-quantified parameter can
carry a hypothesis's entire weight. -/
def CommittedOn {ι V : Type*} (R : Set ι) (ρ s : Decoupling.Mem ι V) : Prop :=
  ∀ a ∈ R, s a = ρ a

/-- **Definition 2.1's budgeted form, indexed by time.** The system, started at `s₀` and run `t`
steps of `U`, is *committed* to the reference codeword `ρ` on its code region `R`, and its
subsystem meets `ReachesThresholdWithin` at the work budget `w`. Added alongside
`ReachesThreshold`, `ReachesThresholdAtDepth` and `ReachesThresholdWithin`, none of which changes.

Two things this rendering makes explicit rather than hiding:

* the commitment conjunct is only as strong as its pin — see `CommittedOn`;
* Remark 5.5's qualifier "at every later step **on which (S3) still holds**" is automatic here,
  and for a structural reason rather than a proved one: (S3) enters through
  `ReachesThresholdWithin`, a condition on the pair `(w, g(T_S))` that carries no time index at
  all. A rendering in which (S3) could lapse would have to index the budget by time too; this one
  does not, and so cannot be read as having settled that case.

What is time-indexed is therefore the commitment alone. That is precisely the half Remark 5.5
assigns to (S1), and `substrate_reachesThresholdWithinAt_persists` is what (S1) buys for it. -/
def ReachesThresholdWithinAt {ι V : Type*} (U : Decoupling.Mem ι V → Decoupling.Mem ι V)
    (R : Set ι) (ρ s₀ : Decoupling.Mem ι V) (t : ℕ)
    (Consistent NSound Delta1Axiomatized InterpretsR0 : Prop) (w gTS : ℕ) : Prop :=
  CommittedOn R ρ (U^[t] s₀) ∧
    ReachesThresholdWithin Consistent NSound Delta1Axiomatized InterpretsR0 w gTS

/-- **Commitment is inherited along the orbit of a read-only code region.** The core step, stated
once: under (S1) `Decoupling.fixes_iterate` makes every iterate agree with its starting
configuration pointwise on `R`, so a commitment held by `s` is held by `U^[k] s`. -/
private theorem committedOn_iterate_of_fixes {ι V : Type*}
    {U : Decoupling.Mem ι V → Decoupling.Mem ι V} {R : Set ι} {ρ s : Decoupling.Mem ι V}
    (hU : DecoupledSubstrate U R) (k : ℕ) (h : CommittedOn R ρ s) :
    CommittedOn R ρ (U^[k] s) := by
  intro a ha
  rw [Decoupling.fixes_iterate hU k s a ha]
  exact h a ha

/-- **The crossing recurs at every later step — from (S1) alone.** Remark 5.5's learning-branch
sentence, at the bare `Decoupling.Fixes` hypothesis: a crossing held at time `t` is held at every
`t + dt`. Stated in the forward form the prose uses ("recurs at every later step"); under a
read-only code region commitment is in fact time-*invariant*, since `fixes_iterate` compares every
iterate with `s₀` rather than with its predecessor, so the backward direction holds too and is not
what needed proving.

The static conjunct is untouched: it carries no time index, so the whole of the temporal content
sits in `CommittedOn`, and the whole of the price in (S1). -/
theorem fixes_reachesThresholdWithinAt_persists {ι V : Type*}
    {U : Decoupling.Mem ι V → Decoupling.Mem ι V} {R : Set ι} {ρ s₀ : Decoupling.Mem ι V}
    {Consistent NSound Delta1Axiomatized InterpretsR0 : Prop} {t w gTS : ℕ}
    (hU : DecoupledSubstrate U R)
    (h : ReachesThresholdWithinAt U R ρ s₀ t Consistent NSound Delta1Axiomatized InterpretsR0
      w gTS) (dt : ℕ) :
    ReachesThresholdWithinAt U R ρ s₀ (t + dt) Consistent NSound Delta1Axiomatized
      InterpretsR0 w gTS := by
  refine ⟨?_, h.2⟩
  have hc := committedOn_iterate_of_fixes hU dt h.1
  rwa [← Function.iterate_add_apply U dt t s₀, Nat.add_comm dt t] at hc

/-- **(S1) consumed, at the class level.** `(M, U) ∈ 𝒮` whose configuration crosses the threshold
at time `t` still crosses it at every `t + dt`: `Substrate`'s own `s1` field — (S1), the read-only
code region — is exactly what the previous theorem asks for.

This is the theorem the time-indexed predicate exists for. Before it, every `Substrate` field
except (S3) was carried and consumed by nothing that touches the threshold; this consumes (S1),
and it is still the *only* threshold-coupled consumer of a substrate field other than (S3). (S2)
and `SubstrateL`'s five learning fields remain unconsumed, for the reason the section note gives.

That the (S1) hypothesis is load-bearing rather than decorative is
`reachesThresholdWithinAt_lost_on_overwrite` below, which is [Discovery] Proposition 4.2's
"forgetting is bounded by the probability that the code region is overwritten" in deterministic
skeleton. -/
theorem substrate_reachesThresholdWithinAt_persists {ι V : Type*}
    {U : Decoupling.Mem ι V → Decoupling.Mem ι V} {R : Set ι} {ρ s₀ : Decoupling.Mem ι V}
    {r K L c₀ c₁ c₂ δ : ℝ} {sCodeSize gTS : ℕ}
    {Consistent NSound Delta1Axiomatized InterpretsR0 : Prop} {t w : ℕ}
    (hS : Substrate U R r K L c₀ c₁ c₂ δ sCodeSize gTS Consistent NSound Delta1Axiomatized
      InterpretsR0)
    (h : ReachesThresholdWithinAt U R ρ s₀ t Consistent NSound Delta1Axiomatized InterpretsR0
      w gTS) :
    ∀ dt, ReachesThresholdWithinAt U R ρ s₀ (t + dt) Consistent NSound Delta1Axiomatized
      InterpretsR0 w gTS :=
  fun dt => fixes_reachesThresholdWithinAt_persists hS.s1 h dt

/-- **The overwrite guard: (S1) is load-bearing, and the predicate can lose its crossing.**
[Discovery] Proposition 4.2 bounds forgetting by the probability that the code region is itself
overwritten; in a deterministic skeleton that reads: overwrite ⇒ lost, read-only ⇒ kept. The
previous two theorems are the second half. This is the first.

The witness is a one-cell world (`ι = Fin 1`, `V = Bool`) whose whole memory is code
(`R = Set.univ`) and whose update complements it. Started at the all-`true` configuration and
pinned to it, the system is committed at `t = 0` — trivially, which is exactly `CommittedOn`'s own
caveat — and has lost the commitment at `t = 1`, while the static conjunct, being time-free, holds
throughout: `g(T_S) = 2` at a budget of `4 = capacity ⌈log₂ 3⌉` work bits, the parameters
`CategoricalThreshold.reflectiveWithin_at_capacity` inhabits, with the four theory conditions at
`True` as everywhere on this route.

So `substrate_reachesThresholdWithinAt_persists` cannot be proved without its (S1) hypothesis: the
same predicate, at the same static parameters, flips from held to lost in one step as soon as the
code region is writable — and this update is writable, `¬ DecoupledSubstrate` being the guard's
third conjunct rather than a remark about it. -/
theorem reachesThresholdWithinAt_lost_on_overwrite :
    ∃ (ι V : Type) (U : Decoupling.Mem ι V → Decoupling.Mem ι V) (R : Set ι)
      (ρ s₀ : Decoupling.Mem ι V) (w gTS : ℕ),
      ReachesThresholdWithinAt U R ρ s₀ 0 True True True True w gTS ∧
        ¬ ReachesThresholdWithinAt U R ρ s₀ 1 True True True True w gTS ∧
        ¬ DecoupledSubstrate U R := by
  have hcap : GodelInternalization.capacity (Nat.clog 2 (2 + 1)) = 4 := by decide
  have hstatic : ReachesThresholdWithin True True True True 4 2 := by
    refine ⟨?_, trivial, trivial, trivial, trivial⟩
    have h := CategoricalThreshold.reflectiveWithin_at_capacity (gTS := 2) (le_refl 2)
    rwa [hcap] at h
  refine ⟨Fin 1, Bool, fun s a => !(s a), Set.univ, fun _ => true, fun _ => true, 4, 2,
    ⟨by intro a _; rfl, hstatic⟩, ?_, ?_⟩
  · rintro ⟨hcom, -⟩
    have h1 := hcom 0 (Set.mem_univ 0)
    simp at h1
  · intro hfix
    have h1 := hfix (fun _ => true) 0 (Set.mem_univ 0)
    simp at h1

end SubstrateClass
