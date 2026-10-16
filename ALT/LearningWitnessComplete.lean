module

public import ALT.LearningWitness
public import ALT.ExcessOrder
public import ALT.GodelComplete


/-!
# The learning witness's theory conditions, made genuine at `𝗣𝗔⁻`

Provenance: [Inevitability] §2 Definition 2.1, Remark 5.3, rows IN-14, IN-19 and IN-24.
`ALT/LearningWitness.lean` exhibits a member of `𝒮_L` whose four theory
conditions on `T_S` are carried at `True`, and whose Gödel size `g(T_S) = 2` is a placeholder
attached to no theory (its own docstring says so). Instantiating the four `Prop`s at `True` alone
would be cosmetic — a proved `Prop` is logically `True` — so the genuine upgrade is the COUPLING:
one incompleteness invocation at `𝗣𝗔⁻`, supplying a single Gödel size threaded through both the
threshold predicate and the underivable-truth payload. This module composes that coupling, mirroring
`ALT/ExcessOrderComplete.lean`'s `outgrows_arith`/`outgrows_paMinus` pair.

## Main results

* `PAMinusConsistent`, `PAMinusNSound`, `PAMinusDelta1`, `PAMinusInterpretsR0` — Definition 2.1's
  four conditions, named at `𝗣𝗔⁻`'s own Foundation forms rather than carried at `True`:
  `Δ₁`-axiomatized (`Theory.Δ₁`, a Type-valued class, carried as the `Nonempty` it certifies since
  `Theory.Δ₁.ofFinite` packages a CHOSEN `Δ₁`-definition, not a bare fact), interprets `𝗥₀`
  (`𝗥₀ ⪯ 𝗣𝗔⁻`, already `Prop`-valued), ℕ-sound at the FAITHFUL "every provable sentence is true"
  form (`∀ δ, 𝗣𝗔⁻ ⊢ δ → ℕ↓[ℒₒᵣ] ⊧ δ`, via `FFL.FirstOrder.models_of_provable` — strictly stronger
  than "every axiom is true", which the bare instance `ℕ↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻` alone would give), and
  consistent, derived FROM that ℕ-truth (`FFL.FirstOrder.consistent_of_model` at the standard model)
  rather than assumed separately. `theoryConditions_paMinus` proves
  `ALT.TheoryConditions` at these four.
* `witness_substrateL_paMinus`, `witness_substrateL_paMinus_bernoulli` —
  `ALT.witness_substrateL`/ `_bernoulli` with the four `True`s replaced by the facts
  above, the fixed `gTS = 2` replaced by a variable Gödel size, and the fixed headroom `K = k + 100`
  replaced by a symbolic `K = k + C` under `100 ≤ C` and
  `ALT.capacity (Nat.clog 2 (gTS + 1)) ≤ C` — the existential `gTS` is never a
  computed numeral, matching the discipline `ExcessOrderComplete` and GV-7 already use. Every field
  beyond (S2)/(S3) is `witness_substrateL`'s own proof term, unchanged.
* `witness_reachesThresholdWithin_paMinus`, `witness_reachesThresholdWithinAt_paMinus` — the
  symbolic-`C`/`gTS` counterparts of `ALT.witness_reachesThresholdWithin`/
  `witness_reachesThresholdWithinAt`, composed through
  `ALT.SubstrateL.reachesThresholdWithin` and the same `code_persists`/`CommittedOn`
  plumbing; both additionally require `2 ≤ gTS`, the standing structural side condition
  `SubstrateL.reachesThresholdWithin` itself imposes.
* `witness_crossing_genuine_paMinus` — **the capstone.** ONE invocation of
  `ALT.incompleteness_of_arith 𝗣𝗔⁻` supplies a Gödel size `gTS`, threaded through both:
  for every capacity `C` meeting the two hypotheses above, (i) the time-indexed crossing
  (`ALT.ReachesThresholdWithinAt`) at `𝗣𝗔⁻`'s genuine conditions, at `gTS`, at headroom
  `C` — conditional on `2 ≤ gTS`, reported rather than forced (see the seam note below); and (ii)
  the `ALT.outgrows`-shaped payload at the SAME `gTS`, unconditionally. `C` does double
  duty: it is `SubstrateL`'s headroom for (i) and — since `ALT.hostsAt C gTS`
  unfolds to exactly `ALT.capacity (Nat.clog 2 (gTS + 1)) ≤ C` — the `Outgrows`
  budget `κ` for (ii), with no separate lemma needed to connect them.

## The seam (i)/(ii) do not share, reported rather than forced

(i) additionally needs `2 ≤ gTS`; (ii) does not, because `ALT.outgrows`'s own
`∀ Mchk, hostsAt κ g → g < Mchk → Mchk ≤ g² → …` shape is vacuous rather than false when no such
`Mchk` exists (exactly `outgrows_arith`'s own device). `gTS` here is `Encodable.encode` of the
actual Gödel sentence `exists_true_but_unprovable_sentence_of_sigma1sound 𝗣𝗔⁻` delivers —
deliberately kept opaque, so `2 ≤ gTS` is NOT discharged: nothing in this module pins that
encoding's magnitude from below. Both conjuncts are nonetheless stated under the ONE `∃ gTS` the
capstone binds, per the design record's own escape hatch for exactly this mismatch.

## What this does NOT establish

* `CoupledDeliveranceAtRequiredDepth`'s own strong form — the payload stated AT the object (i)'s
  crossing constructs, rather than under a second, independent `∃ M` — is NOT reached: (i) targets
  `SubstrateL`-membership (`ReachesThresholdWithinAt`) and (ii) targets the `Outgrows`/
  `categorical_threshold` payload directly, and nothing here ties the two objects together.
* The `2 ≤ gTS` side condition (i) needs is carried as a hypothesis, not proved for the specific
  incompleteness witness this module obtains.
* The identification of the substrate's internal theory WITH `𝗣𝗔⁻` — that its code region's content
  is that theory's axioms — remains [Inevitability] §2's modelling step; nothing here formalizes it.
* This synthesis is stated in **no** paper; **no numbered result is claimed machine-checked** by it,
  per `ExcessOrderComplete`'s own precedent for a cross-module composition.
-/


@[expose] public section

namespace ALT

open MeasureTheory ProbabilityTheory
open RealizabilityCCC
open FFL.FirstOrder FFL.FirstOrder.Arithmetic

variable {k : ℕ}

/-! ## Stage A: Definition 2.1's four conditions, genuinely instantiated at `𝗣𝗔⁻` -/

/-- Definition 2.1's `Δ₁`-axiomatized condition at `𝗣𝗔⁻`. `Theory.Δ₁` is a Type-valued Foundation
class (it packages a CHOSEN `𝚫ᴬ₁.Semisentence` witnessing the theory's definability, not a bare
proposition), so it is carried as the `Prop` it certifies: `Nonempty`. -/
def PAMinusDelta1 : Prop := Nonempty (𝗣𝗔⁻ : ArithmeticTheory).Δ₁

/-- `𝗣𝗔⁻` is finite, so `Theory.Δ₁.ofFinite` witnesses `Δ₁`-definability with no definability
theorem needed — the same route `ExcessOrderComplete.outgrows_paMinus` uses. -/
theorem paMinus_delta1 : PAMinusDelta1 := ⟨Theory.Δ₁.ofFinite 𝗣𝗔⁻ PeanoMinus.finite⟩

/-- Definition 2.1's "interprets `𝗥₀`" condition at `𝗣𝗔⁻` — already `Prop`-valued
(`FFL.Entailment.WeakerThan`), so carried verbatim; `𝗥₀ ⪯ 𝗣𝗔⁻` is a global Foundation instance. -/
def PAMinusInterpretsR0 : Prop := 𝗥₀ ⪯ (𝗣𝗔⁻ : ArithmeticTheory)

theorem paMinus_interpretsR0 : PAMinusInterpretsR0 :=
  show 𝗥₀ ⪯ (𝗣𝗔⁻ : ArithmeticTheory) from inferInstance

/-- Definition 2.1's ℕ-soundness condition at `𝗣𝗔⁻`, at the FAITHFUL "every provable sentence is
true" form — strictly stronger than "every axiom is true", which the bare global instance
`ℕ↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻` alone states. `FFL.FirstOrder.models_of_provable` bridges the gap: provability plus
axioms-true gives sentence-true. -/
def PAMinusNSound : Prop := ∀ δ : Sentence ℒₒᵣ, (𝗣𝗔⁻ : ArithmeticTheory) ⊢ δ → ℕ↓[ℒₒᵣ] ⊧ δ

theorem paMinus_nsound : PAMinusNSound :=
  fun _ h => models_of_provable (inferInstance : ℕ↓[ℒₒᵣ] ⊧* (𝗣𝗔⁻ : ArithmeticTheory)) h

/-- Definition 2.1's consistency condition at `𝗣𝗔⁻`, derived FROM ℕ-truth
(`FFL.FirstOrder.consistent_of_model` at the standard model `ℕ`) rather than assumed as a fifth,
independent fact — the route the design record names. -/
def PAMinusConsistent : Prop := FFL.Entailment.Consistent (𝗣𝗔⁻ : ArithmeticTheory)

theorem paMinus_consistent : PAMinusConsistent :=
  show FFL.Entailment.Consistent (𝗣𝗔⁻ : ArithmeticTheory) from
    consistent_of_model (𝗣𝗔⁻ : ArithmeticTheory) ℕ

/-- **Stage A's capstone: the four conditions are genuinely `𝗣𝗔⁻`'s own facts, not `True`s.** -/
theorem theoryConditions_paMinus :
    ALT.TheoryConditions
      PAMinusConsistent PAMinusNSound PAMinusDelta1 PAMinusInterpretsR0 :=
  ⟨paMinus_consistent, paMinus_nsound, paMinus_delta1, paMinus_interpretsR0⟩

/-! ## Stage B: the genuine membership, capacity and Gödel size symbolic -/

/-- **Stage B (general form).** `ALT.witness_substrateL` with the four `True`s replaced
by Stage A's genuine `𝗣𝗔⁻` facts, `gTS = 2` replaced by a variable Gödel size, and the fixed
headroom `K = k + 100` replaced by the symbolic `K = k + C` under `100 ≤ C` and
`capacity (⌈log₂(gTS+1)⌉) ≤ C` — (S2)'s numerals become inequalities in `C` (mechanical), (S3)'s
capacity conjunct is exactly the second hypothesis, and every other field
(`realizability`/`windowSufficiency`/`assumptionA`/`benignSeparation`/`e1`) is
`witness_substrateL`'s own proof term, unchanged. -/
theorem witness_substrateL_paMinus [NeZero k] {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {ξ : ℕ → Ω → Bool} (hmeas : ∀ i, Measurable (ξ i))
    (hindep : iIndepFun ξ P) {η τ : ℝ} (hη0 : 0 < η) (hη1 : η ≤ 1 / 2)
    (hmean : ∀ u, ∫ ω, ALT.zeta (ξ (u + k) ω) ∂P = 2 * η - 1) (hbudget : 2 * η ≤ τ)
    (C gTS : ℕ) (hC100 : 100 ≤ C)
    (hCap : ALT.capacity (Nat.clog 2 (gTS + 1)) ≤ C) :
    ALT.SubstrateL (Wit.chainUpdate (k := k)) (codeRegion k)
      3 ((k : ℝ) + (C : ℝ)) (2 * ((k : ℝ) + (C : ℝ))) 1 2 3 (1 / 2) k gTS
      PAMinusConsistent PAMinusNSound PAMinusDelta1 PAMinusInterpretsR0
      (ChainRealizable k) (ChainWindowBudget k η τ) := by
  have hkR : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  have hCR : (100 : ℝ) ≤ (C : ℝ) := by exact_mod_cast hC100
  have hlog : Real.log (3 / (1 / 2)) ≤ 3 / (1 / 2) - 1 := Real.log_le_sub_one_of_pos (by norm_num)
  have hCapR : (ALT.capacity (Nat.clog 2 (gTS + 1)) : ℝ) ≤ (C : ℝ) := by
    exact_mod_cast hCap
  refine
    { s1 := chainUpdate_fixes
      s2 := ⟨by nlinarith, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num,
        by norm_num, by norm_num⟩
      s3 := ⟨by linarith, theoryConditions_paMinus⟩
      realizability := chainRealizable
      windowSufficiency := chainWindowBudget k (le_of_lt hη0) hbudget
      assumptionA := ?_
      benignSeparation := ⟨1 / 2, 1, by norm_num, by norm_num⟩
      e1 := ?_ }
  · refine ⟨Fin k, Fin k, fun _ => Finset.univ, fun _ => singleLiteralAns, 0, (k : ℝ), 0, ?_⟩
    filter_upwards with r'
    have := sqDim_singleLiteral_le (k := k) (0 : ℝ)
    have hcast : (SQObjects.sqDim (Finset.univ : Finset (Fin k)) 0
        (singleLiteralAns (k := k)) : ℝ) ≤ (k : ℝ) := by exact_mod_cast this
    simpa using hcast
  · exact ⟨Bool, inferInstance, Measure.map (substrateTraj (k := k) ξ) P,
      pairEnsemble pairChar 0 k, samePairMean pairChar (2 * η - 1), samePairConst k, by
        have h := mixingHoeffding_substrateTraj_schedule (k := k) (ξ := ξ) (P := P) hmeas hindep
          hη0 hη1 hmean 0 pairChar abs_pairChar_le_one
        have hz : ((0 : Fin k) : ℕ) = 0 := by simp
        rw [hz] at h
        simpa [scheduledMean, scheduledConst, hz] using h⟩

/-- **Stage B, with no probabilistic hypothesis left standing.** `witness_substrateL_paMinus` at
the Bernoulli(`η`) shift `noiseLaw`, exactly `ALT.witness_substrateL_bernoulli`'s own
specialization. -/
theorem witness_substrateL_paMinus_bernoulli [NeZero k] {η τ : ℝ} (hη0 : 0 < η) (hη1 : η ≤ 1 / 2)
    (hbudget : 2 * η ≤ τ) (C gTS : ℕ) (hC100 : 100 ≤ C)
    (hCap : ALT.capacity (Nat.clog 2 (gTS + 1)) ≤ C) :
    ALT.SubstrateL (Wit.chainUpdate (k := k)) (codeRegion k)
      3 ((k : ℝ) + (C : ℝ)) (2 * ((k : ℝ) + (C : ℝ))) 1 2 3 (1 / 2) k gTS
      PAMinusConsistent PAMinusNSound PAMinusDelta1 PAMinusInterpretsR0
      (ChainRealizable k) (ChainWindowBudget k η τ) := by
  have hp : η ∈ unitInterval := ⟨le_of_lt hη0, by linarith⟩
  refine witness_substrateL_paMinus (P := noiseLaw ⟨η, hp⟩) (ξ := noiseCoord)
    measurable_noiseCoord (iIndepFun_noiseCoord _) hη0 hη1 (fun u => ?_) hbudget C gTS hC100 hCap
  simpa using integral_zeta_noiseCoord ⟨η, hp⟩ (u + k)

/-- The symbolic headroom collapses cleanly: `⌊(k + C) − k⌋ = C`, the `witness_headroom` idiom at a
variable `C` rather than the literal `100`. -/
private theorem witness_headroom_paMinus (k C : ℕ) :
    Nat.floor (((k : ℝ) + (C : ℝ)) - (k : ℝ)) = C := by
  rw [show ((k : ℝ) + (C : ℝ)) - (k : ℝ) = (C : ℝ) by ring]
  exact Nat.floor_natCast C

/-- **The atemporal crossing, symbolic.** `ALT.witness_reachesThresholdWithin`'s
counterpart at `𝗣𝗔⁻`'s genuine conditions, symbolic `C`/`gTS`: composed through
`ALT.SubstrateL.reachesThresholdWithin`, which additionally needs `2 ≤ gTS` — the
standing structural side condition every `(S3)`-bridge theorem in `SubstrateClass.lean` carries. -/
theorem witness_reachesThresholdWithin_paMinus [NeZero k] {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {ξ : ℕ → Ω → Bool} (hmeas : ∀ i, Measurable (ξ i))
    (hindep : iIndepFun ξ P) {η τ : ℝ} (hη0 : 0 < η) (hη1 : η ≤ 1 / 2)
    (hmean : ∀ u, ∫ ω, ALT.zeta (ξ (u + k) ω) ∂P = 2 * η - 1) (hbudget : 2 * η ≤ τ)
    (C gTS : ℕ) (hC100 : 100 ≤ C)
    (hCap : ALT.capacity (Nat.clog 2 (gTS + 1)) ≤ C) (hg : 2 ≤ gTS) :
    ALT.ReachesThresholdWithin
      PAMinusConsistent PAMinusNSound PAMinusDelta1 PAMinusInterpretsR0 C gTS := by
  have h := ALT.SubstrateL.reachesThresholdWithin
    (witness_substrateL_paMinus hmeas hindep hη0 hη1 hmean hbudget C gTS hC100 hCap) hg
  rwa [witness_headroom_paMinus k C] at h

/-- **The time-indexed crossing, symbolic, at every step.**
`ALT.witness_reachesThresholdWithinAt`'s counterpart: the reference codeword is pinned
to `loadChain ω`'s own code cells (`chainUpdate_reads_code` is what makes that pin carry content),
and the commitment persists because `Wit.chainUpdate` never writes the code region (`code_persists`,
(S1)). -/
theorem witness_reachesThresholdWithinAt_paMinus [NeZero k] {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {ξ : ℕ → Ω → Bool} (hmeas : ∀ i, Measurable (ξ i))
    (hindep : iIndepFun ξ P) {η τ : ℝ} (hη0 : 0 < η) (hη1 : η ≤ 1 / 2)
    (hmean : ∀ u, ∫ ω, ALT.zeta (ξ (u + k) ω) ∂P = 2 * η - 1) (hbudget : 2 * η ≤ τ)
    (C gTS : ℕ) (hC100 : 100 ≤ C)
    (hCap : ALT.capacity (Nat.clog 2 (gTS + 1)) ≤ C) (hg : 2 ≤ gTS)
    (ω : ℕ → Bool) (t : ℕ) :
    ALT.ReachesThresholdWithinAt (Wit.chainUpdate (k := k)) (codeRegion k)
      (loadChain (k := k) ω) (loadChain (k := k) ω) t
      PAMinusConsistent PAMinusNSound PAMinusDelta1 PAMinusInterpretsR0 C gTS := by
  refine ⟨?_, witness_reachesThresholdWithin_paMinus hmeas hindep hη0 hη1 hmean hbudget C gTS
    hC100 hCap hg⟩
  rintro _ ⟨i, rfl⟩
  exact code_persists t (loadChain (k := k) ω) i

/-! ## Stage C: the capstone — one incompleteness invocation, shared by threshold and payload -/

/-- **The learning witness's crossing, made genuine at `𝗣𝗔⁻`.** ONE invocation of
`ALT.incompleteness_of_arith 𝗣𝗔⁻` supplies a single Gödel size `gTS`; for every capacity
`C` meeting `100 ≤ C` and `capacity (⌈log₂(gTS+1)⌉) ≤ C`:

(i) **the time-indexed crossing**, at `𝗣𝗔⁻`'s genuine Stage A facts, at `gTS`, at headroom `C` —
    conditional on `2 ≤ gTS`, the seam this module's docstring names rather than forces;
(ii) **the payload**, at the SAME `gTS`, unconditionally: `ALT.outgrows`'s own shape needs
     no such side condition.

`C` does double duty without any connecting lemma: it is `SubstrateL`'s headroom for (i), and —
since `ALT.hostsAt C gTS` unfolds to exactly `hCap`'s own inequality — the
`Outgrows` budget `κ` for (ii). -/
theorem witness_crossing_genuine_paMinus [NeZero k] {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {ξ : ℕ → Ω → Bool} (hmeas : ∀ i, Measurable (ξ i))
    (hindep : iIndepFun ξ P) {η τ : ℝ} (hη0 : 0 < η) (hη1 : η ≤ 1 / 2)
    (hmean : ∀ u, ∫ ω, ALT.zeta (ξ (u + k) ω) ∂P = 2 * η - 1) (hbudget : 2 * η ≤ τ) :
    ∃ gTS : ℕ, ∀ C : ℕ, 100 ≤ C →
      ALT.capacity (Nat.clog 2 (gTS + 1)) ≤ C →
      (2 ≤ gTS → ∀ (ω : ℕ → Bool) (t : ℕ),
        ALT.ReachesThresholdWithinAt (Wit.chainUpdate (k := k)) (codeRegion k)
          (loadChain (k := k) ω) (loadChain (k := k) ω) t
          PAMinusConsistent PAMinusNSound PAMinusDelta1 PAMinusInterpretsR0 C gTS) ∧
      (∀ Mchk : ℕ, gTS < Mchk → Mchk ≤ gTS ^ 2 →
        ∃ R : ReflectiveAsm gTS, R.depth = Mchk ∧
          ALT.FitsIn (recursorAsm R.depth) C ∧
          ∃ M, ALT.RepresentsUnderivableTruth
            (Encodable.encode : Sentence ℒₒᵣ → ℕ)
            (fun δ => (𝗣𝗔⁻ : ArithmeticTheory) ⊢ δ) (fun δ => ℕ↓[ℒₒᵣ] ⊧ δ) M) := by
  obtain ⟨gTS, hInc⟩ := ALT.incompleteness_of_arith (𝗣𝗔⁻ : ArithmeticTheory)
  refine ⟨gTS, fun C hC100 hCap => ⟨fun hg ω t => ?_, fun Mchk h1 h2 => ?_⟩⟩
  · exact witness_reachesThresholdWithinAt_paMinus hmeas hindep hη0 hη1 hmean hbudget C gTS
      hC100 hCap hg ω t
  · obtain ⟨R, hdepth, hfits, himp⟩ :=
      ALT.outgrows C (Encodable.encode : Sentence ℒₒᵣ → ℕ)
        (fun δ => (𝗣𝗔⁻ : ArithmeticTheory) ⊢ δ) (fun δ => ℕ↓[ℒₒᵣ] ⊧ δ) gTS Mchk hCap h1 h2
    exact ⟨R, hdepth, hfits, himp hInc⟩

end ALT

/-! ## Axiom audit

The capstone is `#print axioms`-clean on the standard triple — the whole point of the coupling is
that no incompleteness-shaped axiom survives it, only the standard three. -/


set_option linter.style.longLine false in
/-- info: 'ALT.witness_crossing_genuine_paMinus' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.witness_crossing_genuine_paMinus
