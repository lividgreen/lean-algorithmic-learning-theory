/-
Copyright (c) 2026 Mykola Palamarchuk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mykola Palamarchuk
-/
import ALT.SubstitutionSchedule
import ALT.SubstitutionClass
import ALT.LearningWitness

/-!
# The substitution source, self-fed: E1 with the periodic-trap route absent
([Growth] §4 Theorem 4.4, Proposition 4.5)

`SubstitutionSource.subObs` drives its own window-`8` noisy chain: `subNoise` reads `subObs` itself
`8` steps back, and the chain built on `subNoise` reproduces `subObs` exactly
(`obs_subNoise`). Composed onto `GrowingComposite`'s growing carrier (T68), this realizes `subObs`
as the first coordinate of a genuinely self-consuming orbit; realized instead onto
`LearningWitness`'s single-`Decoupling.Mem` substrate, the same fact
(`subObs_readObs_iterate`) makes `subObs` the substrate's own emitted process, and that substrate
is a member of `𝒮_L` (`subObs_witness_substrateL_of_e1`) with E1 discharged by
`subObs_mixingHoeffding` — a Dirac `MixingHoeffding` at `subObs` itself, fed
`SubstitutionSchedule`'s deviation bound.

This is the first source in the corpus on which `BirkhoffTool.not_mixingHoeffding_of_periodic_ne`'s
trap route is machine-checked absent on a source nobody designed for the purpose:
`not_eventuallyPeriodic_obs_subNoise` transports `SubstitutionSource`'s non-periodicity through
`obs_subNoise` rather than being built in.

## Main results

* `subNoise` — `subObs` fed back through `NoisyWindowChain`'s own window-`8` recursion.
* `obs_subNoise` — the window-`8` chain on `subNoise` reproduces `subObs` exactly.
* `compUpdate_window_eq`, `compUpdate_fst_zero` — the growing composite (T68) driven by `subNoise`,
  from the window `subObs 0, …, subObs 7`: its window process is `windowAt 8 subNoise`, and its
  first coordinate at time `t` is `subObs t`.
* `subObs_mixingHoeffding` — E1 at `subObs` itself: `BirkhoffTool.MixingHoeffding` on
  `Measure.dirac subObs`, at every offset, via `mixingHoeffding_dirac_of_deviation_bound` fed
  `SubstitutionSchedule`'s deviation bound.
* `not_eventuallyPeriodic_obs_subNoise` — the window-`8` chain on `subNoise` is not eventually
  periodic either, transported from `SubstitutionSource.not_eventuallyPeriodic_subObs` through
  `obs_subNoise`.
* `subObs_witness_substrateL_of_e1` — `LearningWitness`'s chain substrate at `k = 8` is a member of
  `𝒮_L`, `e1` discharged by `subObs_mixingHoeffding` — a one-liner off `witness_substrateL_of_e1`,
  since `e1` is a bare existential and does not care which `MixingHoeffding` instance fills it.
* `subObs_readObs_iterate` — **the stretch**: `subObs` is not merely consumed by that substrate but
  genuinely emitted by it — reading `LearningWitness.readObs` off the substrate's own orbit, loaded
  at `subNoise`, reproduces `subObs t` at every `t`, by `readObs_iterate_loadChain` composed with
  `obs_subNoise`.
* `subNoise_eq_derivedNoise` — `subNoise` is `NoisyWindowChain.derivedNoise 8 subObs`,
  definitionally.
* `subObs_envelopeProfile` — `subObs` inhabits `SubstitutionClass.EnvelopeProfileNat`
  unconditionally, since a constant profile is the envelope's constant-bound special case.
* `subObs_envelopeMixingHoeffding_zero` — the class-level `envelope_mixingHoeffding` recovers
  `subObs_mixingHoeffding`'s own constant at `a = 0`.
* `subObs_witness_substrateL_of_e1_budget` — the source's own window budget `(η, τ) = (1/8, 5/16)`
  inhabits `LearningWitness.ChainWindowBudget` directly.

## Scope

`subObs_witness_substrateL_of_e1` and `subObs_readObs_iterate` are about the SAME substrate
(`LearningWitness.chainUpdate (k := 8)`, `LearningWitness.codeRegion 8`): the first is its abstract
membership in `𝒮_L`, load-independent since `SubstrateL` names no state; the second pins the
realization to the specific loaded configuration `loadChain subNoise`, showing `subObs` is what
that configuration's own orbit actually emits. Neither theorem is built from
`GrowingComposite.compUpdate`'s product carrier — `compUpdate_window_eq` / `compUpdate_fst_zero`
establish that composite's own realization independently, and `LearningWitness`'s single-`Mem`
carrier already folds code, window and the growing noise reservoir into one substrate, which is
why it is the packing `subObs_witness_substrateL_of_e1` uses rather than a fresh one built from
`compUpdate`'s pair type.
-/

namespace SubstitutionComposite

open ParityWalk Finset NoisyWindowChain SubstitutionSource BirkhoffTool

/-! ## The self-fed noise, and its chain -/

/-- **`subObs` fed back as its own window-`8` noise.** The first eight values are `subObs`'s own;
past that, `subNoise u` is the noise bit `NoisyWindowChain.obs_add` would need to carry `subObs`'s
window-`8` chain from `subObs (u - 8)` to `subObs u`. -/
def subNoise (u : ℕ) : Bool := if u < 8 then subObs u else !(xor (subObs (u - 8)) (subObs u))

/-- **The window-`8` chain on `subNoise` reproduces `subObs` exactly.** Strong induction on `u`:
below `8` both sides are `subObs`'s own value (`obs_of_lt`); past `8`, `obs_add` and `subNoise`'s
own definition combine to the Boolean identity `!(a ⊕ !(a ⊕ b)) = b`. -/
theorem obs_subNoise : NoisyWindowChain.obs 8 subNoise = subObs := by
  funext u
  induction u using Nat.strong_induction_on with
  | _ u ih =>
    by_cases hu : u < 8
    · rw [NoisyWindowChain.obs_of_lt subNoise hu]
      simp [subNoise, hu]
    · rw [Nat.not_lt] at hu
      obtain ⟨t, rfl⟩ : ∃ t, u = t + 8 := ⟨u - 8, by omega⟩
      have hrec := NoisyWindowChain.obs_add (k := 8) (by norm_num) subNoise t
      rw [hrec, ih t (by omega)]
      have hn : subNoise (t + 8) = !(xor (subObs t) (subObs (t + 8))) := by
        simp only [subNoise]
        rw [if_neg (by omega : ¬ t + 8 < 8)]
        congr 2
      rw [hn]
      cases subObs t <;> cases subObs (t + 8) <;> simp

/-! ## The growing composite driven by `subNoise` -/

/-- The composite's initial window: `subObs`'s own first eight values. -/
noncomputable def compW0 : Fin 8 → Bool := fun i => subObs i

/-- **The composite's window process is `windowAt 8 subNoise`.** `windowFst_iterate_compUpdate`'s
own reindexed word — `compW0` below `8`, `subNoise` shifted back by `7` above it — is `subNoise`
itself on both branches: below `8` because `subNoise` reads `subObs` there too, above it because
the reindexing exactly undoes the shift the composite's own emit convention (`seqWrite`'s
`s 0 + 1`) introduces. -/
theorem compUpdate_window_eq (t : ℕ) :
    ((GrowingComposite.compUpdate 8 (fun v => subNoise (v + 7)))^[t]
        (compW0, fun _ => 0)).1
      = NoisyWindowChain.windowAt 8 subNoise t := by
  have h := GrowingComposite.windowFst_iterate_compUpdate 8 (fun v => subNoise (v + 7)) compW0 t
  rw [h]
  congr 1
  funext u
  by_cases hu : u < 8
  · simp [hu, compW0, subNoise]
  · rw [dif_neg hu]
    have huv : u - 8 + 1 + 7 = u := by omega
    rw [huv]

/-- **The composite's first coordinate at time `t` is `subObs t`.** -/
theorem compUpdate_fst_zero (t : ℕ) :
    ((GrowingComposite.compUpdate 8 (fun v => subNoise (v + 7)))^[t]
        (compW0, fun _ => 0)).1 0
      = subObs t := by
  rw [compUpdate_window_eq, NoisyWindowChain.windowAt]
  simp only [Fin.val_zero, Nat.add_zero]
  rw [← obs_subNoise]

/-! ## E1 at `subObs` itself -/

/-- **E1 at `subObs` itself.** `SubstitutionSchedule.subObs_pair` at phase `0` is exactly the
deterministic deviation bound `mixingHoeffding_dirac_of_deviation_bound` asks for, at the constant
`2S + subW a`, uniform in `a` since `subW` is. -/
theorem subObs_mixingHoeffding (a : Fin 8) :
    BirkhoffTool.MixingHoeffding (MeasureTheory.Measure.dirac subObs)
      (pairEnsemble pairChar (a : ℕ) 8) (subRho a) ((2 * 14 + subW a) ^ 2 / (2 * Real.log 2)) := by
  have hbound : ∀ n : ℕ, 1 ≤ n →
      (n : ℝ) * |SQOracle.empiricalMean (pairEnsemble pairChar (a : ℕ) 8) n subObs - subRho a|
        ≤ 2 * 14 + subW a := by
    intro n hn1
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
    have heq : (n : ℝ) * (SQOracle.empiricalMean (pairEnsemble pairChar (a : ℕ) 8) n subObs
        - subRho a) = ∑ t ∈ range n, chi (subObs (0 + t + (a : ℕ))) * chi (subObs (0 + t + 8))
          - (n : ℝ) * subRho a := by
      rw [SQOracle.empiricalMean]
      have hpe : ∀ t, pairEnsemble pairChar (a : ℕ) 8 t subObs
          = chi (subObs (0 + t + (a : ℕ))) * chi (subObs (0 + t + 8)) := by
        intro t
        simp [pairEnsemble, pairChar]
      simp_rw [hpe]
      field_simp
    have hb := subObs_pair 0 a n
    have habs : |((n : ℝ) * (SQOracle.empiricalMean (pairEnsemble pairChar (a : ℕ) 8) n subObs
        - subRho a))| ≤ subW a := by rw [heq]; exact hb
    rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg n)] at habs
    linarith [habs]
  exact BirkhoffTool.mixingHoeffding_dirac_of_deviation_bound subObs
    (pairEnsemble pairChar (a : ℕ) 8) (subRho a) (2 * 14 + subW a) (by norm_num [subW])
    (fun i => measurable_pairEnsemble pairChar (a : ℕ) 8 i) hbound

/-! ## The trap route, absent -/

/-- **The window-`8` chain on `subNoise` is not eventually periodic.** Transported from
`SubstitutionSource.not_eventuallyPeriodic_subObs` through `obs_subNoise` — the first source in the
corpus on which `BirkhoffTool.not_mixingHoeffding_of_periodic_ne`'s trap route is machine-checked
absent on a source not designed for the purpose. -/
theorem not_eventuallyPeriodic_obs_subNoise :
    ¬ GrowingComposite.EventuallyPeriodic (NoisyWindowChain.obs 8 subNoise) := by
  rw [obs_subNoise]
  exact not_eventuallyPeriodic_subObs

/-! ## Membership in 𝒮_L -/

/-- **`LearningWitness`'s chain substrate at `k = 8` is a member of `𝒮_L`.** A one-liner off
`witness_substrateL_of_e1`: its `e1` field is a bare existential, so `subObs_mixingHoeffding`
discharges it regardless of which literal it names. -/
theorem subObs_witness_substrateL_of_e1 :
    SubstrateClass.SubstrateL (LearningWitness.chainUpdate (k := 8)) (LearningWitness.codeRegion 8)
      3 ((8 : ℝ) + 100) (2 * ((8 : ℝ) + 100)) 1 2 3 (1 / 2) 8 2
      True True True True (LearningWitness.ChainRealizable 8)
      (LearningWitness.ChainWindowBudget 8 0 0) :=
  LearningWitness.witness_substrateL_of_e1 (le_refl 0) (by norm_num)
    ⟨Bool, inferInstance, MeasureTheory.Measure.dirac subObs, pairEnsemble pairChar 0 8,
      subRho 0, (2 * 14 + subW 0) ^ 2 / (2 * Real.log 2), subObs_mixingHoeffding 0⟩

/-- **The stretch: `subObs` is genuinely emitted by that substrate, not merely consumed.** Reading
`LearningWitness.readObs` off the substrate's own orbit, loaded at `subNoise`, reproduces
`subObs t` at every `t` — `readObs_iterate_loadChain` (the realization theorem) composed with
`obs_subNoise`. -/
theorem subObs_readObs_iterate (t : ℕ) :
    LearningWitness.readObs
      ((LearningWitness.chainUpdate (k := 8))^[t] (LearningWitness.loadChain (k := 8) subNoise))
      = subObs t := by
  rw [LearningWitness.readObs_iterate_loadChain, obs_subNoise]

/-! ## The generic bridge, and the class-level envelope at the landed instance -/

/-- **`subNoise` is the generic derived-noise bridge, at `k = 8` and `subObs`.** Both sides unfold
to the same `if`-`else`, so this holds definitionally. -/
theorem subNoise_eq_derivedNoise : subNoise = NoisyWindowChain.derivedNoise 8 subObs := rfl

/-- **`subObs` inhabits the class-level envelope hypothesis, unconditionally.**
`SubstitutionClass.profileNat_toEnvelope` at `subObs_profile`: the landed constant profile is the
constant-bound special case of the `√n` envelope, so every class-level consumer
(`SubstitutionClass.envelope_mixingHoeffding`,
`SubstitutionClass.identifies_of_lt_quarter_envelope`) applies to `subObs` with no further
hypothesis. -/
theorem subObs_envelopeProfile : SubstitutionClass.EnvelopeProfileNat subObs 14 subRho subW :=
  SubstitutionClass.profileNat_toEnvelope SubstitutionSchedule.subObs_profile

/-- **The class route recovers the landed instance's E1 at `a = 0`.**
`SubstitutionClass.envelope_mixingHoeffding` at `subObs_envelopeProfile`, `a = 0`: the constant
`(2 * 14 + subW 0) ^ 2 / (2 * Real.log 2)` is `(2 * 14 + 77) ^ 2 / (2 * Real.log 2)`, the same
constant `subObs_mixingHoeffding` names directly — the class-level theorem and the landed
one-liner agree on the instance, as they must. -/
theorem subObs_envelopeMixingHoeffding_zero :
    BirkhoffTool.MixingHoeffding (MeasureTheory.Measure.dirac subObs)
      (pairEnsemble pairChar ((0 : Fin 8) : ℕ) 8) (subRho 0)
      ((2 * 14 + subW 0) ^ 2 / (2 * Real.log 2)) :=
  SubstitutionClass.envelope_mixingHoeffding subObs_envelopeProfile 0

/-! ## The source's own window budget, at `LearningWitness`'s substrate directly -/

/-- **`LearningWitness.witness_substrateL_of_e1`'s sibling at `subObs`'s own window budget.**
`subObs_witness_substrateL_of_e1` concludes at `ChainWindowBudget 8 0 0`, since `e1`'s existential
does not care which literal it names; this instantiates the same substrate at the source's own
`(η, τ) = (1/8, 5/16)` — `subObs_identifies`'s own window (`2 * (1/8) ≤ 5/16` by `norm_num`) —
concluding at `ChainWindowBudget 8 (1/8) (5/16)` directly. -/
theorem subObs_witness_substrateL_of_e1_budget :
    SubstrateClass.SubstrateL (LearningWitness.chainUpdate (k := 8)) (LearningWitness.codeRegion 8)
      3 ((8 : ℝ) + 100) (2 * ((8 : ℝ) + 100)) 1 2 3 (1 / 2) 8 2
      True True True True (LearningWitness.ChainRealizable 8)
      (LearningWitness.ChainWindowBudget 8 (1 / 8) (5 / 16)) :=
  LearningWitness.witness_substrateL_of_e1 (by norm_num) (by norm_num)
    ⟨Bool, inferInstance, MeasureTheory.Measure.dirac subObs, pairEnsemble pairChar 0 8,
      subRho 0, (2 * 14 + subW 0) ^ 2 / (2 * Real.log 2), subObs_mixingHoeffding 0⟩

end SubstitutionComposite

/-! ## Axiom audit

Every capstone above is `#print axioms`-clean on the standard triple, and the guards below make
that build-enforced. -/

set_option linter.style.longLine false

/-- info: 'SubstitutionComposite.obs_subNoise' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SubstitutionComposite.obs_subNoise

/-- info: 'SubstitutionComposite.compUpdate_window_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SubstitutionComposite.compUpdate_window_eq

/-- info: 'SubstitutionComposite.compUpdate_fst_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SubstitutionComposite.compUpdate_fst_zero

/-- info: 'SubstitutionComposite.subObs_mixingHoeffding' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SubstitutionComposite.subObs_mixingHoeffding

/-- info: 'SubstitutionComposite.not_eventuallyPeriodic_obs_subNoise' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SubstitutionComposite.not_eventuallyPeriodic_obs_subNoise

/-- info: 'SubstitutionComposite.subObs_witness_substrateL_of_e1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SubstitutionComposite.subObs_witness_substrateL_of_e1

/-- info: 'SubstitutionComposite.subObs_readObs_iterate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SubstitutionComposite.subObs_readObs_iterate

/-- info: 'SubstitutionComposite.subNoise_eq_derivedNoise' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SubstitutionComposite.subNoise_eq_derivedNoise

/-- info: 'SubstitutionComposite.subObs_envelopeProfile' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SubstitutionComposite.subObs_envelopeProfile

/-- info: 'SubstitutionComposite.subObs_envelopeMixingHoeffding_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SubstitutionComposite.subObs_envelopeMixingHoeffding_zero

/-- info: 'SubstitutionComposite.subObs_witness_substrateL_of_e1_budget' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SubstitutionComposite.subObs_witness_substrateL_of_e1_budget
