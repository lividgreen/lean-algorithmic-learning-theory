/-
Copyright (c) 2026 Mykola Palamarchuk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mykola Palamarchuk
-/
import ALT.SubstitutionComposite

/-!
# The growing host's own membership: an append-only carrier is a member of `𝒮_L`
([Growth] §4 Proposition 4.6)

`SubstitutionComposite.subObs_witness_substrateL_of_e1` packs `subObs` into
`LearningWitness.chainUpdate`'s single-`Decoupling.Mem` substrate — a carrier that CONSUMES a
pre-written noise stream (`loadChain subNoise`, all of `subNoise` written into memory up front).
This module packs the SAME observation into a different carrier: `GrowingComposite.compUpdate`'s
own product `(window, growing tape)`, whose tape EMITS its history append-only, one fresh cell per
step, exactly as `GrowingComposite.seqWrite` writes it. The two carriers realize the same process;
they differ in how that process is HOSTED — read from a completed record, or produced as the
record grows.

`compUpdate`'s window step reads no code region at all — the noise argument comes from the free
function `ξ`, never from a decoded rule — so the `8` code cells `hostCodeRegion` reserves are
read-only by construction (S1) but carry no computational role; they exist because `SubstrateClass`
asks for a code/work split, not because this dynamics consults one.

`hostProj` projects a packed memory onto `compUpdate`'s own `(Fin 8 → Bool) × Decoupling.Mem ℕ ℕ`
pair; `hostProj_hostSubUpdate` shows the projection commutes with the two updates UNCONDITIONALLY
(no code invariant to carry along the orbit, unlike `BlockPairWitness`/`LearningWitness`, since
nothing here reads the code). The realization theorem then falls straight out of the already-landed
orbit fact `SubstitutionComposite.compUpdate_fst_zero`.

## Main results

* `HostIdx`, `HostMem`, `hostCodeRegion`, `hostCodeRegion_ncard` — the memory layout: `8` code
  cells, `8` window cells, and a `ℕ`-indexed growing tape, folded into one `Decoupling.Mem`.
* `hostSubUpdate`, `loadHost`, `readObs` — the update, its loading at `subObs`'s own initial
  window and an empty tape, and the observation cell.
* `hostSubUpdate_fixes` (S1).
* `readObs_iterate_loadHost` — **the realization theorem**: reading the substrate's own observation
  cell along its own orbit reproduces `subObs`, exactly, at every `t`.
* `hostSubstrateTraj`, `hostSubstrateTraj_eq_subObs` — the substrate's own process, and its
  identification with `subObs`.
* `HostRealizable`, `hostRealizable` — the named realizability `Prop`, proved.
* `growingHostWitness_substrateL` — **the membership capstone**: the append-only host is a member
  of `𝒮_L`, with E1 drawn from `SubstitutionComposite.subObs_mixingHoeffding` on its own process.

## Scope

`assumptionA` and `benignSeparation` are facts about `Fin 8` alone (`LearningWitness`'s own single-
literal class), reused verbatim from `LearningWitness.witness_substrateL_of_e1`'s proof term, not
about which memory carries the process.
-/

namespace GrowingHostWitness

open NoisyWindowChain SubstitutionSource SubstitutionComposite BirkhoffTool

/-! ## The memory layout -/

/-- The witness's cell index: `8` code cells, `8` window cells, and a `ℕ`-indexed growing tape. -/
abbrev HostIdx : Type := Fin 8 ⊕ (Fin 8 ⊕ ℕ)

/-- The witness's memory: `ℕ`-valued throughout, matching `GrowingComposite.seqWrite`'s own tape
(its counter cell genuinely grows without bound, so it cannot be compressed into finitely many
`Bool` cells the way a FINITE host's counter can). Code and window cells carry `0`/`1`. -/
abbrev HostMem : Type := Decoupling.Mem HostIdx ℕ

/-- The **code region**: `8` read-only cells, present for the code/work split `SubstrateClass` asks
for even though `compUpdate`'s own dynamics never reads them. -/
def hostCodeRegion : Set HostIdx := Set.range Sum.inl

/-- **The code region has exactly `8` cells.** -/
theorem hostCodeRegion_ncard : hostCodeRegion.ncard = 8 := by
  rw [hostCodeRegion, ← Set.image_univ, Set.ncard_image_of_injective _ Sum.inl_injective,
    Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin]

private lemma toNat_beq_one (b : Bool) : (b.toNat == 1) = b := by cases b <;> decide

/-- The `(window, tape)` projection of a packed memory — the pair `GrowingComposite.compUpdate`
itself acts on. -/
private def hostProj (s : HostMem) : (Fin 8 → Bool) × Decoupling.Mem ℕ ℕ :=
  (fun i => s (Sum.inr (Sum.inl i)) == 1, fun n => s (Sum.inr (Sum.inr n)))

/-! ## The update, its loading, and the observation -/

/-- **One step of the append-only host's own dynamics**: the window and tape step by
`GrowingComposite.compUpdate` at `ξ := fun v => subNoise (v + 7)`, projected onto the packed
memory and repacked; the code copies through untouched. -/
def hostSubUpdate (s : HostMem) : HostMem := fun x =>
  match x with
  | Sum.inl i => s (Sum.inl i)
  | Sum.inr (Sum.inl i) =>
      ((GrowingComposite.compUpdate 8 (fun v => subNoise (v + 7)) (hostProj s)).1 i).toNat
  | Sum.inr (Sum.inr n) =>
      (GrowingComposite.compUpdate 8 (fun v => subNoise (v + 7)) (hostProj s)).2 n

/-- **Loading the host's own initial state**: the code cells are all `0` (unread, so their value
carries no meaning); the window cells hold `subObs`'s own first `8` values
(`SubstitutionComposite.compW0`); the tape starts empty, matching `compUpdate_fst_zero`'s own
hypothesis. -/
noncomputable def loadHost : HostMem := fun x =>
  match x with
  | Sum.inl _ => 0
  | Sum.inr (Sum.inl i) => (compW0 i).toNat
  | Sum.inr (Sum.inr _) => 0

/-- The observation the substrate emits: its window's oldest bit. -/
def readObs (s : HostMem) : Bool := s (Sum.inr (Sum.inl 0)) == 1

/-! ## (S1): the code is read-only -/

/-- **(S1) by construction.** -/
theorem hostSubUpdate_fixes : Decoupling.Fixes hostSubUpdate hostCodeRegion := by
  rintro s _ ⟨i, rfl⟩
  rfl

/-! ## The realization theorem -/

/-- **The projection commutes with the two updates, unconditionally.** Unlike
`BlockPairWitness.hostProj_hostSubUpdate` / `LearningWitness.chainUpdate`'s own orbit lemma, no
code invariant is needed: `compUpdate`'s window step reads no code cell at all. -/
private theorem hostProj_hostSubUpdate (s : HostMem) :
    hostProj (hostSubUpdate s)
      = GrowingComposite.compUpdate 8 (fun v => subNoise (v + 7)) (hostProj s) := by
  refine Prod.ext ?_ rfl
  funext i
  change (((GrowingComposite.compUpdate 8 (fun v => subNoise (v + 7)) (hostProj s)).1 i).toNat
      == 1) = (GrowingComposite.compUpdate 8 (fun v => subNoise (v + 7)) (hostProj s)).1 i
  exact toNat_beq_one _

private theorem hostProj_loadHost : hostProj loadHost = (compW0, fun _ : ℕ => 0) := by
  refine Prod.ext ?_ rfl
  funext i
  change ((compW0 i).toNat == 1) = compW0 i
  exact toNat_beq_one _

private theorem hostProj_iterate (t : ℕ) :
    hostProj ((hostSubUpdate)^[t] loadHost)
      = (GrowingComposite.compUpdate 8 (fun v => subNoise (v + 7)))^[t] (compW0, fun _ => 0) := by
  induction t with
  | zero => rw [Function.iterate_zero_apply, Function.iterate_zero_apply, hostProj_loadHost]
  | succ t ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', hostProj_hostSubUpdate, ih]

/-- **The realization theorem.** Reading the substrate's own observation cell along its own
update's orbit, from its own loaded state, reproduces `subObs` exactly, at every `t` — sharper
than a "consumed-stream" carrier's realization (`SubstitutionComposite.subObs_readObs_iterate`),
which is only up to what its own load already had to know: here the tape holds nothing but what
the orbit itself has written by time `t`. -/
theorem readObs_iterate_loadHost (t : ℕ) :
    readObs ((hostSubUpdate)^[t] loadHost) = subObs t := by
  have hp := hostProj_iterate t
  have hfst : (hostProj ((hostSubUpdate)^[t] loadHost)).1
      = ((GrowingComposite.compUpdate 8 (fun v => subNoise (v + 7)))^[t]
          (compW0, fun _ => 0)).1 := congrArg Prod.fst hp
  have hz : (hostProj ((hostSubUpdate)^[t] loadHost)).1 0
      = readObs ((hostSubUpdate)^[t] loadHost) := rfl
  rw [← hz, hfst]
  exact compUpdate_fst_zero t

/-- The substrate's OWN observation process, read along its own orbit from its own loaded state. -/
noncomputable def hostSubstrateTraj : ℕ → Bool := fun t => readObs ((hostSubUpdate)^[t] loadHost)

/-- The substrate's own process IS `subObs` — `readObs_iterate_loadHost`, packaged for
rewriting. -/
theorem hostSubstrateTraj_eq_subObs : hostSubstrateTraj = subObs := by
  funext t
  exact readObs_iterate_loadHost t

/-! ## Realizability, and the membership capstone -/

/-- **Realizability, named on the host.** Reading the substrate's own observation cell along its
own orbit reproduces `subObs` exactly, at every `t` — stronger than
`BlockPairWitness.HostRealizable`'s up-to-tape-bit shape, since nothing here is up to anything. -/
def HostRealizable : Prop := ∀ t : ℕ, readObs ((hostSubUpdate)^[t] loadHost) = subObs t

theorem hostRealizable : HostRealizable := readObs_iterate_loadHost

/-- **The membership capstone.** The append-only host — `GrowingComposite.compUpdate`'s own
`(window, growing tape)` carrier, folded into one `Decoupling.Mem` — is a member of `𝒮_L`
([Inevitability] §2 Definition 2.3), with E1 drawn from its own emitted process: at `a = 0`,
`SubstitutionComposite.subObs_mixingHoeffding` rewritten along `hostSubstrateTraj_eq_subObs`.

The three prerequisites and the five learning fields follow
`LearningWitness.witness_substrateL_of_e1`'s own proof term at the same numerals — `r = 3`,
`K = 8 + 100`, `L = 2K`, `c₀ = 1`, `c₁ = 2`, `c₂ = 3`, `δ = 1/2`, `sCodeSize = 8`
(`hostCodeRegion_ncard`), `g(T_S) = 2` — with `assumptionA` and `benignSeparation` reused verbatim
(both are facts about `Fin 8` alone, not about the memory carrying it). This is distinct from
`SubstitutionComposite.subObs_witness_substrateL_of_e1` precisely in that the carrier here EMITS
its history append-only, one fresh cell per step, rather than consuming a pre-written stream. -/
theorem growingHostWitness_substrateL :
    SubstrateClass.SubstrateL hostSubUpdate hostCodeRegion
      3 ((8 : ℝ) + 100) (2 * ((8 : ℝ) + 100)) 1 2 3 (1 / 2) 8 2
      True True True True HostRealizable (LearningWitness.ChainWindowBudget 8 0 0) := by
  have hlog : Real.log (3 / (1 / 2)) ≤ 3 / (1 / 2) - 1 := Real.log_le_sub_one_of_pos (by norm_num)
  have hcap : GodelInternalization.capacity (Nat.clog 2 (2 + 1)) = 4 := by decide
  refine
    { s1 := hostSubUpdate_fixes
      s2 := ⟨by nlinarith, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num,
        by norm_num, by norm_num⟩
      s3 := ⟨by rw [hcap]; norm_num, trivial, trivial, trivial, trivial⟩
      realizability := hostRealizable
      windowSufficiency := LearningWitness.chainWindowBudget 8 (le_refl 0) (by norm_num)
      assumptionA := ?_
      benignSeparation := ⟨1 / 2, 1, by norm_num, by norm_num⟩
      e1 := ⟨Bool, inferInstance, MeasureTheory.Measure.dirac hostSubstrateTraj,
        pairEnsemble pairChar 0 8, subRho 0, (2 * 14 + subW 0) ^ 2 / (2 * Real.log 2),
        by rw [hostSubstrateTraj_eq_subObs]; exact subObs_mixingHoeffding 0⟩ }
  refine ⟨Fin 8, Fin 8, fun _ => Finset.univ, fun _ => LearningWitness.singleLiteralAns, 0,
    (8 : ℝ), 0, ?_⟩
  filter_upwards with r'
  have hle := LearningWitness.sqDim_singleLiteral_le (k := 8) (0 : ℝ)
  have hcast : (SQObjects.sqDim (Finset.univ : Finset (Fin 8)) 0
      (LearningWitness.singleLiteralAns (k := 8)) : ℝ) ≤ (8 : ℝ) := by exact_mod_cast hle
  simpa using hcast

end GrowingHostWitness

/-! ## Axiom audit

Every capstone above is `#print axioms`-clean on the standard triple, and the guards below make
that build-enforced. -/

set_option linter.style.longLine false

/-- info: 'GrowingHostWitness.readObs_iterate_loadHost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GrowingHostWitness.readObs_iterate_loadHost

/-- info: 'GrowingHostWitness.hostRealizable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GrowingHostWitness.hostRealizable

/-- info: 'GrowingHostWitness.growingHostWitness_substrateL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GrowingHostWitness.growingHostWitness_substrateL
