module

public import ALT.BlockPairObservability
public import ALT.LearningWitness

/-!
# The certified block-pair host is a member of `𝒮_L`

`LearningWitness.lean` exhibits one member of the learning route-class `𝒮_L`
([Inevitability] §2 Definition 2.3) on an abstract noise stream. This module exhibits a SECOND
member — the finite, deterministic, autonomous host of `BlockPairObservability.lean` — whose E1 is
drawn from its OWN dynamics rather than from an external probability space.

The embedding mirrors `LearningWitness`'s: `subUpdate` splits its memory into a code region (8
cells, the committed literal), a window (8 cells), and — replacing the chain witness's unconsumed
noise stream — a finite binary counter register (`Nat.size Π` cells, `Π := 2·(2·M)·24`) tracking
the host's own phase. The realization theorem does not re-derive the window/counter recursion from
scratch: it projects onto `update`'s own `(window, counter)` pair and reuses
`update_iterate_designWindow` as a black box, so the code invariant is the only genuinely new
induction here.

## Main results

* `Idx`, `Mem`, `codeRegion`, `codeRegion_ncard` — the memory layout.
* `readCounter`, `writeCounter` — the finite binary counter register and its round trip.
* `decodeRule`, `subUpdate`, `load`, `readObs` — the update and its loading.
* `subUpdate_fixes` (S1), `subUpdate_reads_code`.
* `readObs_iterate_load` — **the realization theorem**: reading the substrate's own observation
  cell along its own orbit reproduces `designObs`, pointwise.
* `substrateTraj`, `substrateTraj_eq_traj` — the substrate's own process, and its
  identification with `traj`.
* `Realizable`, `realizable` — the named realizability `Prop`, proved.
* `witness_substrateL` — **the membership capstone**: the host is a member of `𝒮_L`, with E1
  drawn from `mixingHoeffding_schedule` on its own phase law.

## Scope

Deliberately out of scope, as `BlockPairObservability.lean`'s: `𝒮_E` and the overlap question —
`BlockPairOverlap.lean`'s business. The paper home is [Inevitability] §5 Theorem 5.8(a)(b), row
IN-37, which registers this membership at the boundary stated there.
-/


@[expose] public section

namespace ALT

namespace BlockPairHost

open MeasureTheory MixingHoeffding

variable (M : ℕ) [NeZero (2 * (2 * M))]

/-! ## The memory layout -/

/-- The witness's cell index: `8` code cells, `8` window cells, and a finite binary counter
register of `Nat.size Π` cells (`Π := 2 * (2 * M) * 24`), replacing the chain witness's unconsumed
noise stream. -/
abbrev Idx : Type := Fin 8 ⊕ (Fin 8 ⊕ Fin (Nat.size (2 * (2 * M) * 24)))

/-- The witness's memory, in [Decoupling]'s own shape: one `Bool` per cell. -/
abbrev Mem : Type := ALT.Mem (Idx M) Bool

/-- The **code region**: the cells holding the committed literal. -/
def codeRegion : Set (Idx M) := Set.range Sum.inl

omit [NeZero (2 * (2 * M))] in
/-- **The code region has exactly `8` cells.** -/
theorem codeRegion_ncard : (codeRegion M).ncard = 8 := by
  rw [codeRegion, ← Set.image_univ, Set.ncard_image_of_injective _ Sum.inl_injective,
    Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin]

/-- **Reading the rule off the code cells**, mirroring `ALT.Wit.decodeRule` re-typed on the
host's own index — that lemma is typed on `ALT.Wit k` and cannot be reused as is. -/
def decodeRule (s : Mem M) : Fin 8 :=
  if h : ∃ i : Fin 8, s (Sum.inl i) = true then Fin.find _ h else 0

omit [NeZero (2 * (2 * M))] in
private theorem decodeRule_oneHot (s : Mem M) (i : Fin 8)
    (h : ∀ j : Fin 8, s (Sum.inl j) = true ↔ j = i) : decodeRule M s = i := by
  have hex : ∃ j : Fin 8, s (Sum.inl j) = true := ⟨i, (h i).mpr rfl⟩
  rw [decodeRule, dite_eq_left hex]
  refine le_antisymm (Fin.find_le_of_pos hex ((h i).mpr rfl)) ((Fin.le_find_iff hex i).mpr ?_)
  intro m hm hp
  exact absurd ((h m).mp hp) (ne_of_lt hm)

/-! ## The finite binary counter register, and its round trip -/

/-- The counter register's value stays below `2 ^ Nat.size` of its modulus. -/
lemma counter_val_lt (c : ZMod (2 * (2 * M) * 24)) :
    c.val < 2 ^ Nat.size (2 * (2 * M) * 24) :=
  lt_trans (ZMod.val_lt c) (Nat.lt_size_self _)

/-- **Reading the counter register**: the finite binary word the register cells carry, read as a
`ZMod Π` value via `finFunctionFinEquiv`. -/
def readCounter (s : Mem M) : ZMod (2 * (2 * M) * 24) :=
  ((finFunctionFinEquiv (fun i : Fin (Nat.size (2 * (2 * M) * 24)) =>
    if s (Sum.inr (Sum.inr i)) then (1 : Fin 2) else 0)).val : ℕ)

/-- **Writing the counter register**: the binary word representing `c.val`, well-defined since
`c.val < Π < 2 ^ (Nat.size Π)` (`ZMod.val_lt` against `Nat.lt_size_self`, no digit lemma needed). -/
def writeCounter (c : ZMod (2 * (2 * M) * 24)) (i : Fin (Nat.size (2 * (2 * M) * 24))) : Bool :=
  finFunctionFinEquiv.symm (⟨c.val, counter_val_lt M c⟩ :
    Fin (2 ^ Nat.size (2 * (2 * M) * 24))) i == 1

/-- **The counter round trip.** Whenever a memory's counter cells hold `writeCounter c`, reading
the counter back recovers `c` exactly — `Equiv.apply_symm_apply` plus `ZMod.natCast_zmod_val`. -/
private lemma readCounter_eq_of_counter_cells {s : Mem M} {c : ZMod (2 * (2 * M) * 24)}
    (h : ∀ i, s (Sum.inr (Sum.inr i)) = writeCounter M c i) :
    readCounter M s = c := by
  unfold readCounter
  have heq : (fun i => if s (Sum.inr (Sum.inr i)) then (1 : Fin 2) else 0)
      = finFunctionFinEquiv.symm (⟨c.val, counter_val_lt M c⟩ :
        Fin (2 ^ Nat.size (2 * (2 * M) * 24))) := by
    funext i
    rw [h i]
    unfold writeCounter
    generalize finFunctionFinEquiv.symm (⟨c.val, counter_val_lt M c⟩ :
      Fin (2 ^ Nat.size (2 * (2 * M) * 24))) i = x
    fin_cases x <;> decide
  rw [heq, Equiv.apply_symm_apply]
  exact ZMod.natCast_zmod_val c

/-! ## The update, its loading, and the observation -/

/-- **One step of the host's own dynamics**: `ALT.Wit.chainUpdate`'s own line — code
copied, window shifts with the noise cell replaced by the tape bit the rule computes at the next
counter, counter written one step ahead. -/
def subUpdate (s : Mem M) : Mem M := fun x =>
  match x with
  | Sum.inl i => s (Sum.inl i)
  | Sum.inr (Sum.inl i) =>
      if h : (i : ℕ) + 1 < 8 then s (Sum.inr (Sum.inl ⟨(i : ℕ) + 1, h⟩))
      else xor (!(s (Sum.inr (Sum.inl (decodeRule M s))))) (tape M (readCounter M s + 1))
  | Sum.inr (Sum.inr j) => writeCounter M (readCounter M s + 1) j

/-- **Loading the host's own designed window into the memory.** The code is one-hot at literal `0`;
the window cells take the design's own values ahead of `c`; the counter is written to `c + 7`, the
newest window position, matching `BlockPairHost`'s own convention. -/
def load (c : ZMod (2 * (2 * M) * 24)) : Mem M := fun x =>
  match x with
  | Sum.inl i => decide ((i : ℕ) = 0)
  | Sum.inr (Sum.inl i) => designObs M (c + (i : ℕ))
  | Sum.inr (Sum.inr j) => writeCounter M (c + 7) j

/-- The observation the substrate emits: its window's oldest bit. -/
def readObs (s : Mem M) : Bool := s (Sum.inr (Sum.inl 0))

/-! ## (S1): the code is read-only, and the update nonetheless reads it -/

/-- **(S1) by construction.** -/
theorem subUpdate_fixes : ALT.Fixes (subUpdate M) (codeRegion M) := by
  rintro s _ ⟨i, rfl⟩
  rfl

/-- **The update genuinely consults its code region**, `ALT.chainUpdate_reads_code`
transported line for line. -/
theorem subUpdate_reads_code :
    ∃ s s' : Mem M, (∀ x ∉ codeRegion M, s x = s' x) ∧
      subUpdate M s ≠ subUpdate M s' := by
  refine ⟨fun x => match x with
      | Sum.inl i => decide ((i : ℕ) = 0)
      | Sum.inr (Sum.inl i) => decide ((i : ℕ) = 0)
      | Sum.inr (Sum.inr _) => false,
    fun x => match x with
      | Sum.inl i => decide ((i : ℕ) = 1)
      | Sum.inr (Sum.inl i) => decide ((i : ℕ) = 0)
      | Sum.inr (Sum.inr _) => false, ?_, ?_⟩
  · rintro (i | (i | j)) hx
    · exact absurd ⟨i, rfl⟩ hx
    · rfl
    · rfl
  · intro hcon
    have hdec : decodeRule M (fun x => match x with
        | Sum.inl i => decide ((i : ℕ) = 0)
        | Sum.inr (Sum.inl i) => decide ((i : ℕ) = 0)
        | Sum.inr (Sum.inr _) => false) = ⟨0, by norm_num⟩ :=
      decodeRule_oneHot M _ _ fun j => by
        simp only [decide_eq_true_eq]
        constructor
        · intro hj; exact Fin.ext hj
        · intro hj; rw [hj]
    have hdec' : decodeRule M (fun x => match x with
        | Sum.inl i => decide ((i : ℕ) = 1)
        | Sum.inr (Sum.inl i) => decide ((i : ℕ) = 0)
        | Sum.inr (Sum.inr _) => false) = ⟨1, by norm_num⟩ :=
      decodeRule_oneHot M _ _ fun j => by
        simp only [decide_eq_true_eq]
        constructor
        · intro hj; exact Fin.ext hj
        · intro hj; rw [hj]
    have hrc : readCounter M (fun x => match x with
        | Sum.inl i => decide ((i : ℕ) = 0)
        | Sum.inr (Sum.inl i) => decide ((i : ℕ) = 0)
        | Sum.inr (Sum.inr _) => false) =
      readCounter M (fun x => match x with
        | Sum.inl i => decide ((i : ℕ) = 1)
        | Sum.inr (Sum.inl i) => decide ((i : ℕ) = 0)
        | Sum.inr (Sum.inr _) => false) := rfl
    have h := congrFun hcon (Sum.inr (Sum.inl (7 : Fin 8)))
    rw [subUpdate, subUpdate] at h
    simp only [show ¬ ((7 : Fin 8) : ℕ) + 1 < 8 from by decide, hdec, hdec', hrc] at h
    revert h
    simp

/-! ## The realization theorem: the substrate's own process IS the host

Rather than re-deriving the window/counter recursion from scratch, this section projects onto
`update`'s own `(window, counter)` pair and reuses
`update_iterate_designWindow` as a black box: the only genuinely new induction is the code
invariant (the code stays one-hot at `0` along the loaded orbit), exactly as `chainUpdate_fixes`
makes it for the chain witness. -/

/-- The `(window, counter)` projection of a host memory — the pair `update`
itself acts on. -/
private def proj (s : Mem M) : (Fin 8 → Bool) × ZMod (2 * (2 * M) * 24) :=
  (fun i => s (Sum.inr (Sum.inl i)), readCounter M s)

/-- **The projection commutes with the two updates**, given the code names literal `0`: the window
branch's case split matches `noisyStep`/`windowMap`'s own term for term, and the counter branch is
the round trip. -/
private lemma proj_subUpdate (s : Mem M) (h0 : decodeRule M s = 0) :
    proj M (subUpdate M s) = update M (proj M s) := by
  have hcounter : readCounter M (subUpdate M s) = readCounter M s + 1 :=
    readCounter_eq_of_counter_cells M (fun _ => rfl)
  refine Prod.ext ?_ hcounter
  funext i
  simp only [proj, update, subUpdate,
    ALT.noisyStep, ALT.windowMap]
  split_ifs with h
  · rfl
  · rw [h0]

/-- **The code stays one-hot at `0` along the whole loaded orbit** — the analogue of
`chainUpdate_fixes`'s consequence for the chain witness, and what makes `proj_subUpdate`
applicable at every step. -/
private lemma decodeRule_iterate_load (c : ZMod (2 * (2 * M) * 24)) :
    ∀ t, decodeRule M ((subUpdate M)^[t] (load M c)) = 0 := by
  have hcode : ∀ t, ∀ j : Fin 8,
      ((subUpdate M)^[t] (load M c)) (Sum.inl j) = decide ((j : ℕ) = 0) := by
    intro t
    induction t with
    | zero => intro j; rfl
    | succ t ih =>
      intro j
      rw [Function.iterate_succ_apply']
      exact ih j
  intro t
  apply decodeRule_oneHot M
  intro j
  rw [hcode t j]
  simp only [decide_eq_true_eq]
  constructor
  · intro hj; exact Fin.ext hj
  · intro hj; simp [hj]

/-- **The combined orbit theorem**: the substrate's own `(window, counter)` state after `t` steps
is `update`'s own orbit from the designed initial window. -/
private lemma proj_iterate (c : ZMod (2 * (2 * M) * 24)) (t : ℕ) :
    proj M ((subUpdate M)^[t] (load M c)) =
      (update M)^[t] (proj M (load M c)) := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
      proj_subUpdate M _ (decodeRule_iterate_load M c t), ih]

private lemma proj_load (c : ZMod (2 * (2 * M) * 24)) :
    proj M (load M c) = (designWindow M (c + 7), c + 7) := by
  have hcounter : readCounter M (load M c) = c + 7 :=
    readCounter_eq_of_counter_cells M (fun _ => rfl)
  refine Prod.ext ?_ hcounter
  funext i
  change designObs M (c + (i : ℕ)) = designWindow M (c + 7) i
  unfold designWindow
  congr 1
  ring

/-- **The counter register's own orbit, in closed form.** Reading the counter cells back after `t`
steps from the loaded state at phase `c` recovers `c + 7 + t` exactly — the `.snd` half of
`proj_iterate`/`proj_load` composed with `BlockPairHost`'s own designed-orbit theorem,
exposed as its own public lemma rather than left inside the private orbit machinery, since a later
construction needs the counter's orbit alone, with no window component. -/
theorem readCounter_iterate_load (c : ZMod (2 * (2 * M) * 24)) (t : ℕ) :
    readCounter M ((subUpdate M)^[t] (load M c)) = c + 7 + (t : ℕ) := by
  have hp := proj_iterate M c t
  rw [proj_load, update_iterate_designWindow] at hp
  exact congrArg Prod.snd hp

/-- **The realization theorem.** Reading the substrate's own observation cell along its own
update's orbit, from its own loaded state, reproduces the design exactly — pointwise, with no
measure theory anywhere. This is what makes every statistical clause on this substrate a statement
about the HOST and not about a process glued to it. -/
theorem readObs_iterate_load (c : ZMod (2 * (2 * M) * 24)) (t : ℕ) :
    readObs M ((subUpdate M)^[t] (load M c)) = designObs M (c + (t : ℕ)) := by
  have hp := proj_iterate M c t
  rw [proj_load, update_iterate_designWindow] at hp
  have hfst : (fun i => ((subUpdate M)^[t] (load M c)) (Sum.inr (Sum.inl i)))
      = designWindow M (c + 7 + (t : ℕ)) := congrArg Prod.fst hp
  change ((subUpdate M)^[t] (load M c)) (Sum.inr (Sum.inl 0)) = designObs M (c + (t : ℕ))
  rw [congrFun hfst 0]
  unfold designWindow
  change designObs M (c + 7 + (t : ℕ) - 7 + ((0 : Fin 8) : ℕ)) = designObs M (c + (t : ℕ))
  have hz : ((0 : Fin 8) : ℕ) = 0 := rfl
  rw [hz]
  congr 1
  push_cast
  ring

/-- The substrate's OWN observation process, read along its own orbit from its own loaded state. -/
def substrateTraj (c : ZMod (2 * (2 * M) * 24)) : ℕ → Bool :=
  fun t => readObs M ((subUpdate M)^[t] (load M c))

/-- The substrate's own process is `traj` — `readObs_iterate_load`,
packaged for rewriting. -/
theorem substrateTraj_eq_traj (c : ZMod (2 * (2 * M) * 24)) :
    substrateTraj M c = traj M c := by
  funext t
  exact readObs_iterate_load M c t

/-- **T72's schedule theorem, restated on the substrate's own process.** `phaseLaw M`'s finite
average, taken over `substrateTraj` instead of `traj`, is the SAME statement — by rewriting
through `substrateTraj_eq_traj` — so E1 over the schedule holds on the substrate's own
emitted process, not merely on a process identified with it after the fact. -/
theorem substrate_mixingHoeffding_schedule (a : Fin 8) (ψ : Bool → Bool → ℝ)
    (hψ : ∀ u v, |ψ u v| ≤ 1) :
    MixingHoeffding
      ((Fintype.card (ZMod (2 * (2 * M) * 24)) : ENNReal)⁻¹ •
        ∑ c : ZMod (2 * (2 * M) * 24), Measure.dirac (substrateTraj M c))
      (pairEnsemble ψ (a : ℕ) 8)
      (if (a : ℕ) = 0 then pairMean ψ + pairCoefAB ψ * (-2 / 3) else pairMean ψ)
      ((if (a : ℕ) = 0 then (2 * 56 + 46 : ℝ) else (2 * 56 + 192 : ℝ)) ^ 2 / (2 * Real.log 2)) := by
  simp_rw [substrateTraj_eq_traj]
  exact mixingHoeffding_schedule M a ψ hψ

/-! ## Realizability, and the membership capstone -/

/-- **Realizability, named on the host.** The loaded code decodes to literal `0`, and the
substrate's own observation process obeys that literal's rule up to the tape bit —
`ALT.ChainRealizable`'s shape with the noise word replaced by the host's own tape from
phase `c`. -/
def Realizable : Prop :=
  ∀ c : ZMod (2 * (2 * M) * 24), decodeRule M (load M c) = 0 ∧
    ∀ t : ℕ, readObs M ((subUpdate M)^[t + 8] (load M c))
      = !(xor (readObs M ((subUpdate M)^[t] (load M c))) (tape M (c + (t + 8 : ℕ))))

theorem realizable : Realizable M := by
  intro c
  refine ⟨?_, fun t => ?_⟩
  · have h0 := decodeRule_iterate_load M c 0
    rwa [Function.iterate_zero_apply] at h0
  · rw [readObs_iterate_load, readObs_iterate_load]
    have htape : tape M (c + (t + 8 : ℕ)) =
        (designObs M (c + (t + 8 : ℕ)) == designObs M (c + (t : ℕ))) := by
      unfold tape
      congr 2
      push_cast
      ring
    rw [htape]
    cases designObs M (c + (t + 8 : ℕ)) <;> cases designObs M (c + (t : ℕ)) <;> decide

/-- **The membership capstone.** The certified block-pair host — a finite, deterministic,
autonomous system with memory `16 + Nat.size Π` cells and no external stream — is a member of
`𝒮_L` ([Inevitability] §2 Definition 2.3), with E1 drawn from its own dynamics: the phase law
`phaseLaw`, via `mixingHoeffding_schedule` at `a = 0`, `ψ = pairChar`.

The three prerequisites and the five learning fields follow
`ALT.witness_substrateL_of_e1`'s own proof term at the same numerals — `r = 3`,
`K = 8 + 100`, `L = 2K`, `c₀ = 1`, `c₁ = 2`, `c₂ = 3`, `δ = 1/2`, `sCodeSize = 8`
(`codeRegion_ncard`), `g(T_S) = 2` — with `assumptionA` and
`benignSeparation` reused verbatim from `LearningWitness` (both are facts about `Fin 8` alone, not
about the memory carrying it). -/
theorem witness_substrateL {τ : ℝ} (hτ : 2 * (1 / 6 : ℝ) ≤ τ) :
    ALT.SubstrateL (subUpdate M) (codeRegion M)
      3 ((8 : ℝ) + 100) (2 * ((8 : ℝ) + 100)) 1 2 3 (1 / 2) 8 2
      True True True True (Realizable M) (ALT.ChainWindowBudget 8 (1 / 6) τ) := by
  have hlog : Real.log (3 / (1 / 2)) ≤ 3 / (1 / 2) - 1 := Real.log_le_sub_one_of_pos (by norm_num)
  have hcap : ALT.capacity (Nat.clog 2 (2 + 1)) = 4 := by decide
  refine
    { s1 := subUpdate_fixes M
      s2 := ⟨by nlinarith, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num,
        by norm_num, by norm_num⟩
      s3 := ⟨by rw [hcap]; norm_num, trivial, trivial, trivial, trivial⟩
      realizability := realizable M
      windowSufficiency := ALT.chainWindowBudget 8 (by norm_num) hτ
      assumptionA := ?_
      benignSeparation := ⟨1 / 2, 1, by norm_num, by norm_num⟩
      e1 := ⟨Bool, inferInstance,
        (Fintype.card (ZMod (2 * (2 * M) * 24)) : ENNReal)⁻¹ •
          ∑ c : ZMod (2 * (2 * M) * 24), Measure.dirac (substrateTraj M c),
        pairEnsemble pairChar 0 8, _, _,
        substrate_mixingHoeffding_schedule M 0 pairChar abs_pairChar_le_one⟩ }
  refine ⟨Fin 8, Fin 8, fun _ => Finset.univ, fun _ => ALT.singleLiteralAns, 0,
    (8 : ℝ), 0, ?_⟩
  filter_upwards with r'
  have hle := ALT.sqDim_singleLiteral_le (k := 8) (0 : ℝ)
  have hcast : (SQObjects.sqDim (Finset.univ : Finset (Fin 8)) 0
      (ALT.singleLiteralAns (k := 8)) : ℝ) ≤ (8 : ℝ) := by exact_mod_cast hle
  simpa using hcast

end BlockPairHost

end ALT

/-! ## Axiom audit -/

set_option linter.style.longLine false in
/-- info: 'ALT.BlockPairHost.readObs_iterate_load' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.BlockPairHost.readObs_iterate_load

set_option linter.style.longLine false in
/-- info: 'ALT.BlockPairHost.substrate_mixingHoeffding_schedule' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.BlockPairHost.substrate_mixingHoeffding_schedule

set_option linter.style.longLine false in
/-- info: 'ALT.BlockPairHost.witness_substrateL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.BlockPairHost.witness_substrateL
