module

public import ALT.SubstitutionComposite

/-!
# The growing host's own membership: an append-only carrier is a member of `𝒮_L`
([Growth] §4 Proposition 4.6)

`subObs_witness_substrateL_of_e1` packs `subObs` into
`ALT.Wit.chainUpdate`'s single-`ALT.Mem` substrate — a carrier that CONSUMES a
pre-written noise stream (`loadChain subNoise`, all of `subNoise` written into memory up front).
This module packs the SAME observation into a different carrier: `compUpdate`'s
own product `(window, growing tape)`, whose tape EMITS its history append-only, one fresh cell per
step, exactly as `seqWrite` writes it. The two carriers realize the same process;
they differ in how that process is HOSTED — read from a completed record, or produced as the
record grows.

`compUpdate`'s window step reads no code region at all — the noise argument comes from the free
function `ξ`, never from a decoded rule — so the `8` code cells `GrowingHost.codeRegion` reserves
are read-only by construction (S1) but carry no computational role; they exist because
`SubstrateClass` asks for a code/work split, not because this dynamics consults one.

`GrowingHost.proj` projects a packed memory onto `compUpdate`'s own `(Fin 8 → Bool) × ALT.Mem ℕ ℕ`
pair; `GrowingHost.proj_subUpdate` shows the projection commutes with the two updates
UNCONDITIONALLY (no code invariant to carry along the orbit, unlike
`BlockPairWitness`/`LearningWitness`, since nothing here reads the code). The realization theorem
then falls straight out of the already-landed orbit fact `compUpdate_fst_zero`.

## Main results

* `GrowingHost.Idx`, `GrowingHost.Mem`, `GrowingHost.codeRegion`, `GrowingHost.codeRegion_ncard` —
  the memory layout: `8` code cells, `8` window cells, and a `ℕ`-indexed growing tape, folded into
  one `ALT.Mem`.
* `GrowingHost.subUpdate`, `GrowingHost.load`, `GrowingHost.readObs` — the update, its loading at
  `subObs`'s own initial window and an empty tape, and the observation cell.
* `GrowingHost.subUpdate_fixes` (S1).
* `GrowingHost.readObs_iterate_load` — **the realization theorem**: reading the substrate's own
  observation cell along its own orbit reproduces `subObs`, exactly, at every `t`.
* `GrowingHost.substrateTraj`, `GrowingHost.substrateTraj_eq_subObs` — the substrate's own process,
  and its identification with `subObs`.
* `GrowingHost.Realizable`, `GrowingHost.realizable` — the named realizability `Prop`, proved.
* `GrowingHost.witness_substrateL` — **the membership capstone**: the append-only host is a member
  of `𝒮_L`, with E1 drawn from `subObs_mixingHoeffding` on its own process.

## Scope

`assumptionA` and `benignSeparation` are facts about `Fin 8` alone (`LearningWitness`'s own single-
literal class), reused verbatim from `ALT.witness_substrateL_of_e1`'s proof term, not
about which memory carries the process.
-/


@[expose] public section

namespace ALT

namespace GrowingHost

/-! ## The memory layout -/

/-- The witness's cell index: `8` code cells, `8` window cells, and a `ℕ`-indexed growing tape. -/
abbrev Idx : Type := Fin 8 ⊕ (Fin 8 ⊕ ℕ)

/-- The witness's memory: `ℕ`-valued throughout, matching `seqWrite`'s own tape
(its counter cell genuinely grows without bound, so it cannot be compressed into finitely many
`Bool` cells the way a FINITE host's counter can). Code and window cells carry `0`/`1`. -/
abbrev Mem : Type := ALT.Mem Idx ℕ

/-- The **code region**: `8` read-only cells, present for the code/work split `SubstrateClass` asks
for even though `compUpdate`'s own dynamics never reads them. -/
def codeRegion : Set Idx := Set.range Sum.inl

/-- **The code region has exactly `8` cells.** -/
theorem codeRegion_ncard : codeRegion.ncard = 8 := by
  rw [codeRegion, ← Set.image_univ, Set.ncard_image_of_injective _ Sum.inl_injective,
    Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin]

private lemma toNat_beq_one (b : Bool) : (b.toNat == 1) = b := by cases b <;> decide

/-- The `(window, tape)` projection of a packed memory — the pair `compUpdate`
itself acts on. -/
def proj (s : Mem) : (Fin 8 → Bool) × ALT.Mem ℕ ℕ :=
  (fun i => s (Sum.inr (Sum.inl i)) == 1, fun n => s (Sum.inr (Sum.inr n)))

/-! ## The update, its loading, and the observation -/

/-- **One step of the append-only host's own dynamics**: the window and tape step by
`compUpdate` at `ξ := fun v => subNoise (v + 7)`, projected onto the packed
memory and repacked; the code copies through untouched. -/
def subUpdate (s : Mem) : Mem := fun x =>
  match x with
  | Sum.inl i => s (Sum.inl i)
  | Sum.inr (Sum.inl i) =>
      ((compUpdate 8 (fun v => subNoise (v + 7)) (proj s)).1 i).toNat
  | Sum.inr (Sum.inr n) =>
      (compUpdate 8 (fun v => subNoise (v + 7)) (proj s)).2 n

/-- **Loading the host's own initial state**: the code cells are all `0` (unread, so their value
carries no meaning); the window cells hold `subObs`'s own first `8` values
(`compW0`); the tape starts empty, matching `compUpdate_fst_zero`'s own
hypothesis. -/
noncomputable def load : Mem := fun x =>
  match x with
  | Sum.inl _ => 0
  | Sum.inr (Sum.inl i) => (compW0 i).toNat
  | Sum.inr (Sum.inr _) => 0

/-- The observation the substrate emits: its window's oldest bit. -/
def readObs (s : Mem) : Bool := s (Sum.inr (Sum.inl 0)) == 1

/-! ## (S1): the code is read-only -/

/-- **(S1) by construction.** -/
theorem subUpdate_fixes : ALT.Fixes subUpdate codeRegion := by
  rintro s _ ⟨i, rfl⟩
  rfl

/-! ## The realization theorem -/

/-- **The projection commutes with the two updates, unconditionally.** Unlike
`BlockPairHost.proj_subUpdate` / `ALT.Wit.chainUpdate`'s own orbit lemma, no
code invariant is needed: `compUpdate`'s window step reads no code cell at all. -/
private theorem proj_subUpdate (s : Mem) :
    proj (subUpdate s)
      = compUpdate 8 (fun v => subNoise (v + 7)) (proj s) := by
  refine Prod.ext ?_ rfl
  funext i
  change (((compUpdate 8 (fun v => subNoise (v + 7)) (proj s)).1 i).toNat
      == 1) = (compUpdate 8 (fun v => subNoise (v + 7)) (proj s)).1 i
  exact toNat_beq_one _

private theorem proj_load : proj load = (compW0, fun _ : ℕ => 0) := by
  refine Prod.ext ?_ rfl
  funext i
  change ((compW0 i).toNat == 1) = compW0 i
  exact toNat_beq_one _

private theorem proj_iterate (t : ℕ) :
    proj ((subUpdate)^[t] load)
      = (compUpdate 8 (fun v => subNoise (v + 7)))^[t] (compW0, fun _ => 0) := by
  induction t with
  | zero => rw [Function.iterate_zero_apply, Function.iterate_zero_apply, proj_load]
  | succ t ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', proj_subUpdate, ih]

/-- **The realization theorem.** Reading the substrate's own observation cell along its own
update's orbit, from its own loaded state, reproduces `subObs` exactly, at every `t` — sharper
than a "consumed-stream" carrier's realization (`subObs_readObs_iterate`),
which is only up to what its own load already had to know: here the tape holds nothing but what
the orbit itself has written by time `t`. -/
theorem readObs_iterate_load (t : ℕ) :
    readObs ((subUpdate)^[t] load) = subObs t := by
  have hp := proj_iterate t
  have hfst : (proj ((subUpdate)^[t] load)).1
      = ((compUpdate 8 (fun v => subNoise (v + 7)))^[t]
          (compW0, fun _ => 0)).1 := congrArg Prod.fst hp
  have hz : (proj ((subUpdate)^[t] load)).1 0
      = readObs ((subUpdate)^[t] load) := rfl
  rw [← hz, hfst]
  exact compUpdate_fst_zero t

/-- The substrate's OWN observation process, read along its own orbit from its own loaded state. -/
noncomputable def substrateTraj : ℕ → Bool := fun t => readObs ((subUpdate)^[t] load)

/-- The substrate's own process IS `subObs` — `readObs_iterate_load`, packaged for
rewriting. -/
theorem substrateTraj_eq_subObs : substrateTraj = subObs := by
  funext t
  exact readObs_iterate_load t

/-! ## Realizability, and the membership capstone -/

/-- **Realizability, named on the host.** Reading the substrate's own observation cell along its
own orbit reproduces `subObs` exactly, at every `t` — stronger than
`BlockPairHost.Realizable`'s up-to-tape-bit shape, since nothing here is up to anything. -/
def Realizable : Prop := ∀ t : ℕ, readObs ((subUpdate)^[t] load) = subObs t

theorem realizable : Realizable := readObs_iterate_load

/-- **The membership capstone.** The append-only host — `compUpdate`'s own
`(window, growing tape)` carrier, folded into one `ALT.Mem` — is a member of `𝒮_L`
([Inevitability] §2 Definition 2.3), with E1 drawn from its own emitted process: at `a = 0`,
`subObs_mixingHoeffding` rewritten along `substrateTraj_eq_subObs`.

The three prerequisites and the five learning fields follow
`ALT.witness_substrateL_of_e1`'s own proof term at the same numerals — `r = 3`,
`K = 8 + 100`, `L = 2K`, `c₀ = 1`, `c₁ = 2`, `c₂ = 3`, `δ = 1/2`, `sCodeSize = 8`
(`codeRegion_ncard`), `g(T_S) = 2` — with `assumptionA` and `benignSeparation` reused verbatim
(both are facts about `Fin 8` alone, not about the memory carrying it). This is distinct from
`subObs_witness_substrateL_of_e1` precisely in that the carrier here EMITS
its history append-only, one fresh cell per step, rather than consuming a pre-written stream. -/
theorem witness_substrateL :
    ALT.SubstrateL subUpdate codeRegion
      3 ((8 : ℝ) + 100) (2 * ((8 : ℝ) + 100)) 1 2 3 (1 / 2) 8 2
      True True True True Realizable (ALT.ChainWindowBudget 8 0 0) := by
  have hlog : Real.log (3 / (1 / 2)) ≤ 3 / (1 / 2) - 1 := Real.log_le_sub_one_of_pos (by norm_num)
  have hcap : ALT.capacity (Nat.clog 2 (2 + 1)) = 4 := by decide
  refine
    { s1 := subUpdate_fixes
      s2 := ⟨by nlinarith, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num,
        by norm_num, by norm_num⟩
      s3 := ⟨by rw [hcap]; norm_num, trivial, trivial, trivial, trivial⟩
      realizability := realizable
      windowSufficiency := ALT.chainWindowBudget 8 (le_refl 0) (by norm_num)
      assumptionA := ?_
      benignSeparation := ⟨1 / 2, 1, by norm_num, by norm_num⟩
      e1 := ⟨Bool, inferInstance, MeasureTheory.Measure.dirac substrateTraj,
        pairEnsemble pairChar 0 8, subRho 0, (2 * 14 + subW 0) ^ 2 / (2 * Real.log 2),
        by rw [substrateTraj_eq_subObs]; exact subObs_mixingHoeffding 0⟩ }
  refine ⟨Fin 8, Fin 8, fun _ => Finset.univ, fun _ => ALT.singleLiteralAns, 0,
    (8 : ℝ), 0, ?_⟩
  filter_upwards with r'
  have hle := ALT.sqDim_singleLiteral_le (k := 8) (0 : ℝ)
  have hcast : (SQObjects.sqDim (Finset.univ : Finset (Fin 8)) 0
      (ALT.singleLiteralAns (k := 8)) : ℝ) ≤ (8 : ℝ) := by exact_mod_cast hle
  simpa using hcast

end GrowingHost

end ALT

/-! ## Axiom audit

Every capstone above is `#print axioms`-clean on the standard triple, and the guards below make
that build-enforced. -/


set_option linter.style.longLine false in
/-- info: 'ALT.GrowingHost.readObs_iterate_load' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.GrowingHost.readObs_iterate_load

/-- info: 'ALT.GrowingHost.realizable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.GrowingHost.realizable

set_option linter.style.longLine false in
/-- info: 'ALT.GrowingHost.witness_substrateL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.GrowingHost.witness_substrateL
