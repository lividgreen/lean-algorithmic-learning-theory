/-
Copyright (c) 2026 Mykola Palamarchuk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mykola Palamarchuk
-/
module

public import ALT.TapeHostObservability
public import ALT.LearningWitness

/-!
# The finite autonomous host is a member of `𝒮_L`, over an arbitrary window-deviation profile

`BlockPairWitness.lean` exhibits the certified block-pair host as a member of the learning
route-class `𝒮_L` ([Inevitability] §2 Definition 2.3), with E1 drawn from the host's own dynamics.
This module exhibits the SAME construction over an arbitrary observation sequence `o : ZMod N →
Bool`, at any window-deviation `Profile` (`TapeHostObservability.lean`): the profile-class `𝒮_L`
criterion — the block-pair pipeline's witness layer with its sequence and its profile made
parameters, and its regularity/capacity numerals `(K, gTS)` made parameters as well, IN-24's
coupling standard rather than the certified instance's fixed `K = 108`, `gTS = 2`.

The embedding mirrors `BlockPairWitness`'s own: `hostSubUpdate` splits its memory into a code
region (`8` cells, the committed literal), a window (`8` cells), and a finite binary counter
register (`Nat.size N` cells) tracking the host's own phase. The realization theorem projects onto
`TapeHost.tapeUpdate`'s own `(window, counter)` pair and reuses
`TapeHost.tapeUpdate_iterate_designWindow` as a black box, so the code invariant is the only
genuinely new induction here — `BlockPairWitness`'s own structure, verbatim.

## Main results

* `HostIdx`, `HostMem`, `hostCodeRegion`, `hostCodeRegion_ncard` — the memory layout.
* `readCounter`, `writeCounter` — the finite binary counter register and its round trip.
* `hostDecodeRule`, `hostSubUpdate`, `loadHost`, `readObs` — the update and its loading.
* `hostSubUpdate_fixes` (S1), `hostSubUpdate_reads_code`.
* `readObs_iterate_loadHost` — **the realization theorem**: reading the substrate's own observation
  cell along its own orbit reproduces `o`, pointwise.
* `hostSubstrateTraj`, `hostSubstrateTraj_eq_hostTraj` — the substrate's own process, and its
  identification with `TapeHostObservability.hostTraj`.
* `HostRealizable`, `hostRealizable` — the named realizability `Prop`, proved.
* `tape_density` — the tie between the derived tape's density and `o`'s own exact cyclic lag-`8`
  correlation: `2 * #{tape o = true} = N + ∑ u, χ(o u) · χ(o (u - 8))`.
* `tapeHost_substrateL` — **the profile-class criterion**: at any `Profile`, and any `(K, gTS)`
  clearing `8 + capacity(⌈log₂(gTS+1)⌉)`, the host is a member of `𝒮_L`, with E1 drawn from
  `TapeHostObservability.mixingHoeffding_schedule` on its own phase law.

## Scope

Deliberately out of scope, as `TapeHostObservability.lean`'s: `𝒮_E` and the overlap question —
`TapeHostOverlap.lean`'s business. The paper home is [Inevitability] §5 Theorem 5.8(a)(b), row
IN-37, which registers the certified instance's membership at the boundary stated there; this
module's own criterion is IN-24's coupled standard, not that registered boundary.
-/


@[expose] public section

namespace TapeHostWitness

open TapeHost TapeHostObservability NoisyWindowChain MeasureTheory BirkhoffTool

variable (N : ℕ) [NeZero N] (o : ZMod N → Bool)

/-! ## The memory layout -/

/-- The witness's cell index: `8` code cells, `8` window cells, and a finite binary counter
register of `Nat.size N` cells, replacing the chain witness's unconsumed noise stream. -/
abbrev HostIdx (N : ℕ) : Type := Fin 8 ⊕ (Fin 8 ⊕ Fin (Nat.size N))

/-- The witness's memory, in [Decoupling]'s own shape: one `Bool` per cell. -/
abbrev HostMem (N : ℕ) : Type := Decoupling.Mem (HostIdx N) Bool

/-- The **code region**: the cells holding the committed literal. -/
def hostCodeRegion (N : ℕ) : Set (HostIdx N) := Set.range Sum.inl

/-- **The code region has exactly `8` cells.** -/
theorem hostCodeRegion_ncard (N : ℕ) : (hostCodeRegion N).ncard = 8 := by
  rw [hostCodeRegion, ← Set.image_univ, Set.ncard_image_of_injective _ Sum.inl_injective,
    Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin]

/-- **Reading the rule off the code cells**, `LearningWitness.decodeRule` re-typed on the host's
own index. -/
def hostDecodeRule (N : ℕ) (s : HostMem N) : Fin 8 :=
  if h : ∃ i : Fin 8, s (Sum.inl i) = true then Fin.find _ h else 0

private theorem hostDecodeRule_oneHot (N : ℕ) (s : HostMem N) (i : Fin 8)
    (h : ∀ j : Fin 8, s (Sum.inl j) = true ↔ j = i) : hostDecodeRule N s = i := by
  have hex : ∃ j : Fin 8, s (Sum.inl j) = true := ⟨i, (h i).mpr rfl⟩
  rw [hostDecodeRule, dite_eq_left hex]
  refine le_antisymm (Fin.find_le_of_pos hex ((h i).mpr rfl)) ((Fin.le_find_iff hex i).mpr ?_)
  intro m hm hp
  exact absurd ((h m).mp hp) (ne_of_lt hm)

/-! ## The finite binary counter register, and its round trip -/

/-- `c.val` stays below `2 ^ Nat.size N`, for any `c : ZMod N`. -/
lemma counter_val_lt (c : ZMod N) : c.val < 2 ^ Nat.size N :=
  lt_trans (ZMod.val_lt c) (Nat.lt_size_self _)

/-- **Reading the counter register**: the finite binary word the register cells carry, read as a
`ZMod N` value via `finFunctionFinEquiv`. -/
def readCounter (s : HostMem N) : ZMod N :=
  ((finFunctionFinEquiv (fun i : Fin (Nat.size N) =>
    if s (Sum.inr (Sum.inr i)) then (1 : Fin 2) else 0)).val : ℕ)

/-- **Writing the counter register**: the binary word representing `c.val`, well-defined since
`c.val < N < 2 ^ (Nat.size N)`. -/
def writeCounter (c : ZMod N) (i : Fin (Nat.size N)) : Bool :=
  finFunctionFinEquiv.symm (⟨c.val, counter_val_lt N c⟩ : Fin (2 ^ Nat.size N)) i == 1

/-- **The counter round trip.** -/
private lemma readCounter_eq_of_counter_cells {s : HostMem N} {c : ZMod N}
    (h : ∀ i, s (Sum.inr (Sum.inr i)) = writeCounter N c i) :
    readCounter N s = c := by
  unfold readCounter
  have heq : (fun i => if s (Sum.inr (Sum.inr i)) then (1 : Fin 2) else 0)
      = finFunctionFinEquiv.symm (⟨c.val, counter_val_lt N c⟩ : Fin (2 ^ Nat.size N)) := by
    funext i
    rw [h i]
    unfold writeCounter
    generalize finFunctionFinEquiv.symm (⟨c.val, counter_val_lt N c⟩ :
      Fin (2 ^ Nat.size N)) i = x
    fin_cases x <;> decide
  rw [heq, Equiv.apply_symm_apply]
  exact ZMod.natCast_zmod_val c

/-! ## The update, its loading, and the observation -/

/-- **One step of the host's own dynamics**: code copied, window shifts with the noise cell
replaced by the tape bit the rule computes at the next counter, counter written one step ahead. -/
def hostSubUpdate (s : HostMem N) : HostMem N := fun x =>
  match x with
  | Sum.inl i => s (Sum.inl i)
  | Sum.inr (Sum.inl i) =>
      if h : (i : ℕ) + 1 < 8 then s (Sum.inr (Sum.inl ⟨(i : ℕ) + 1, h⟩))
      else xor (!(s (Sum.inr (Sum.inl (hostDecodeRule N s)))))
        (TapeHost.tape o (readCounter N s + 1))
  | Sum.inr (Sum.inr j) => writeCounter N (readCounter N s + 1) j

/-- **Loading the host's own designed window into the memory.** -/
def loadHost (c : ZMod N) : HostMem N := fun x =>
  match x with
  | Sum.inl i => decide ((i : ℕ) = 0)
  | Sum.inr (Sum.inl i) => o (c + (i : ℕ))
  | Sum.inr (Sum.inr j) => writeCounter N (c + 7) j

/-- The observation the substrate emits: its window's oldest bit. -/
def readObs (s : HostMem N) : Bool := s (Sum.inr (Sum.inl 0))

/-! ## (S1): the code is read-only, and the update nonetheless reads it -/

/-- **(S1) by construction.** -/
theorem hostSubUpdate_fixes : Decoupling.Fixes (hostSubUpdate N o) (hostCodeRegion N) := by
  rintro s _ ⟨i, rfl⟩
  rfl

/-- **The update genuinely consults its code region.** -/
theorem hostSubUpdate_reads_code :
    ∃ s s' : HostMem N, (∀ x ∉ hostCodeRegion N, s x = s' x) ∧
      hostSubUpdate N o s ≠ hostSubUpdate N o s' := by
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
    have hdec : hostDecodeRule N (fun x => match x with
        | Sum.inl i => decide ((i : ℕ) = 0)
        | Sum.inr (Sum.inl i) => decide ((i : ℕ) = 0)
        | Sum.inr (Sum.inr _) => false) = ⟨0, by norm_num⟩ :=
      hostDecodeRule_oneHot N _ _ fun j => by
        simp only [decide_eq_true_eq]
        constructor
        · intro hj; exact Fin.ext hj
        · intro hj; rw [hj]
    have hdec' : hostDecodeRule N (fun x => match x with
        | Sum.inl i => decide ((i : ℕ) = 1)
        | Sum.inr (Sum.inl i) => decide ((i : ℕ) = 0)
        | Sum.inr (Sum.inr _) => false) = ⟨1, by norm_num⟩ :=
      hostDecodeRule_oneHot N _ _ fun j => by
        simp only [decide_eq_true_eq]
        constructor
        · intro hj; exact Fin.ext hj
        · intro hj; rw [hj]
    have hrc : readCounter N (fun x => match x with
        | Sum.inl i => decide ((i : ℕ) = 0)
        | Sum.inr (Sum.inl i) => decide ((i : ℕ) = 0)
        | Sum.inr (Sum.inr _) => false) =
      readCounter N (fun x => match x with
        | Sum.inl i => decide ((i : ℕ) = 1)
        | Sum.inr (Sum.inl i) => decide ((i : ℕ) = 0)
        | Sum.inr (Sum.inr _) => false) := rfl
    have h := congrFun hcon (Sum.inr (Sum.inl (7 : Fin 8)))
    rw [hostSubUpdate, hostSubUpdate] at h
    simp only [show ¬ ((7 : Fin 8) : ℕ) + 1 < 8 from by decide, hdec, hdec', hrc] at h
    revert h
    simp

/-! ## The realization theorem: the substrate's own process IS the host -/

/-- The `(window, counter)` projection of a host memory. -/
private def hostProj (s : HostMem N) : (Fin 8 → Bool) × ZMod N :=
  (fun i => s (Sum.inr (Sum.inl i)), readCounter N s)

private lemma hostProj_hostSubUpdate (s : HostMem N) (h0 : hostDecodeRule N s = 0) :
    hostProj N (hostSubUpdate N o s) = TapeHost.tapeUpdate o (hostProj N s) := by
  have hcounter : readCounter N (hostSubUpdate N o s) = readCounter N s + 1 :=
    readCounter_eq_of_counter_cells N (fun _ => rfl)
  refine Prod.ext ?_ hcounter
  funext i
  simp only [hostProj, TapeHost.tapeUpdate, hostSubUpdate,
    NoisyWindowChain.noisyStep, NoisyWindowChain.windowMap]
  split_ifs with h
  · rfl
  · rw [h0]

private lemma hostDecodeRule_iterate_loadHost (c : ZMod N) :
    ∀ t, hostDecodeRule N ((hostSubUpdate N o)^[t] (loadHost N o c)) = 0 := by
  have hcode : ∀ t, ∀ j : Fin 8,
      ((hostSubUpdate N o)^[t] (loadHost N o c)) (Sum.inl j) = decide ((j : ℕ) = 0) := by
    intro t
    induction t with
    | zero => intro j; rfl
    | succ t ih =>
      intro j
      rw [Function.iterate_succ_apply']
      exact ih j
  intro t
  apply hostDecodeRule_oneHot N
  intro j
  rw [hcode t j]
  simp only [decide_eq_true_eq]
  constructor
  · intro hj; exact Fin.ext hj
  · intro hj; simp [hj]

private lemma hostProj_iterate (c : ZMod N) (t : ℕ) :
    hostProj N ((hostSubUpdate N o)^[t] (loadHost N o c)) =
      (TapeHost.tapeUpdate o)^[t] (hostProj N (loadHost N o c)) := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
      hostProj_hostSubUpdate N o _ (hostDecodeRule_iterate_loadHost N o c t), ih]

private lemma hostProj_loadHost (c : ZMod N) :
    hostProj N (loadHost N o c) = (TapeHost.designWindow o (c + 7), c + 7) := by
  have hcounter : readCounter N (loadHost N o c) = c + 7 :=
    readCounter_eq_of_counter_cells N (fun _ => rfl)
  refine Prod.ext ?_ hcounter
  funext i
  change o (c + (i : ℕ)) = TapeHost.designWindow o (c + 7) i
  unfold TapeHost.designWindow
  congr 1
  ring

/-- **The counter register's own orbit, in closed form.** -/
theorem readCounter_iterate_loadHost (c : ZMod N) (t : ℕ) :
    readCounter N ((hostSubUpdate N o)^[t] (loadHost N o c)) = c + 7 + (t : ℕ) := by
  have hp := hostProj_iterate N o c t
  rw [hostProj_loadHost, TapeHost.tapeUpdate_iterate_designWindow] at hp
  exact congrArg Prod.snd hp

/-- **The realization theorem.** Reading the substrate's own observation cell along its own
update's orbit, from its own loaded state, reproduces `o` exactly — pointwise, with no measure
theory anywhere. -/
theorem readObs_iterate_loadHost (c : ZMod N) (t : ℕ) :
    readObs N ((hostSubUpdate N o)^[t] (loadHost N o c)) = o (c + (t : ℕ)) := by
  have hp := hostProj_iterate N o c t
  rw [hostProj_loadHost, TapeHost.tapeUpdate_iterate_designWindow] at hp
  have hfst : (fun i => ((hostSubUpdate N o)^[t] (loadHost N o c)) (Sum.inr (Sum.inl i)))
      = TapeHost.designWindow o (c + 7 + (t : ℕ)) := congrArg Prod.fst hp
  change ((hostSubUpdate N o)^[t] (loadHost N o c)) (Sum.inr (Sum.inl 0)) = o (c + (t : ℕ))
  rw [congrFun hfst 0]
  unfold TapeHost.designWindow
  change o (c + 7 + (t : ℕ) - 7 + ((0 : Fin 8) : ℕ)) = o (c + (t : ℕ))
  have hz : ((0 : Fin 8) : ℕ) = 0 := rfl
  rw [hz]
  congr 1
  push_cast
  ring

/-- The substrate's OWN observation process, read along its own orbit from its own loaded state. -/
def hostSubstrateTraj (c : ZMod N) : ℕ → Bool :=
  fun t => readObs N ((hostSubUpdate N o)^[t] (loadHost N o c))

/-- The substrate's own process is `TapeHostObservability.hostTraj`. -/
theorem hostSubstrateTraj_eq_hostTraj (c : ZMod N) :
    hostSubstrateTraj N o c = TapeHostObservability.hostTraj o c := by
  funext t
  exact readObs_iterate_loadHost N o c t

variable {S : ℝ} {ρ W : Fin 8 → ℝ}

/-- **The schedule theorem, restated on the substrate's own process.** The finite average of the
per-phase Dirac laws over `hostSubstrateTraj` (not merely `TapeHostObservability.hostTraj`, though
provably the same law) satisfies E1 at any `Profile` — the substrate's own emitted process, not a
process identified with it after the fact. -/
theorem hostSubstrate_mixingHoeffding_schedule (h : TapeHostObservability.Profile o S ρ W)
    (a : Fin 8) (ψ : Bool → Bool → ℝ) (hψ : ∀ u v, |ψ u v| ≤ 1) :
    MixingHoeffding
      ((Fintype.card (ZMod N) : ENNReal)⁻¹ • ∑ c : ZMod N, Measure.dirac (hostSubstrateTraj N o c))
      (pairEnsemble ψ (a : ℕ) 8) (pairMean ψ + pairCoefAB ψ * ρ a)
      ((2 * S + W a) ^ 2 / (2 * Real.log 2)) := by
  simp_rw [hostSubstrateTraj_eq_hostTraj]
  exact TapeHostObservability.mixingHoeffding_schedule o h a ψ hψ

/-! ## Realizability, and the profile-class criterion -/

/-- **Realizability, named on the host.** The loaded code decodes to literal `0`, and the
substrate's own observation process obeys that literal's rule up to the tape bit. -/
def HostRealizable : Prop :=
  ∀ c : ZMod N, hostDecodeRule N (loadHost N o c) = 0 ∧
    ∀ t : ℕ, readObs N ((hostSubUpdate N o)^[t + 8] (loadHost N o c))
      = !(xor (readObs N ((hostSubUpdate N o)^[t] (loadHost N o c)))
          (TapeHost.tape o (c + (t + 8 : ℕ))))

theorem hostRealizable : HostRealizable N o := by
  intro c
  refine ⟨?_, fun t => ?_⟩
  · have h0 := hostDecodeRule_iterate_loadHost N o c 0
    rwa [Function.iterate_zero_apply] at h0
  · rw [readObs_iterate_loadHost, readObs_iterate_loadHost]
    have htape : TapeHost.tape o (c + (t + 8 : ℕ)) =
        (o (c + (t + 8 : ℕ)) == o (c + (t : ℕ))) := by
      unfold TapeHost.tape
      congr 2
      push_cast
      ring
    rw [htape]
    cases o (c + (t + 8 : ℕ)) <;> cases o (c + (t : ℕ)) <;> decide

/-- **The tie between the derived tape's density and `o`'s own exact cyclic lag-`8` correlation.**
`χ(x) · χ(y) = 1` when `x = y` and `-1` otherwise, so the tape's own single-site sum, doubled, is
`N` (the number of positions) plus the signed count of agreements minus disagreements — exactly
`o`'s own lag-`8` correlation sum. No field of `Profile`/`SubstrateL` consumes this; it is stated
beside the membership as the tie behind the derived tape's declared density. -/
theorem tape_density :
    (2 * (Finset.univ.filter (fun u : ZMod N => TapeHost.tape o u = true)).card : ℝ)
      = (N : ℝ) + ∑ u : ZMod N, ParityWalk.chi (o u) * ParityWalk.chi (o (u - 8)) := by
  have hterm : ∀ u : ZMod N,
      ParityWalk.chi (o u) * ParityWalk.chi (o (u - 8))
        = (2 : ℝ) * (if TapeHost.tape o u = true then (1 : ℝ) else 0) - 1 := by
    intro u
    unfold TapeHost.tape
    cases o u <;> cases o (u - 8) <;> norm_num [ParityWalk.chi]
  have hcard : ((Finset.univ.filter (fun u : ZMod N => TapeHost.tape o u = true)).card : ℝ)
      = ∑ u : ZMod N, if TapeHost.tape o u = true then (1 : ℝ) else 0 :=
    Finset.natCast_card_filter (fun u => TapeHost.tape o u = true) Finset.univ
  have hcardN : (Fintype.card (ZMod N) : ℝ) = (N : ℝ) := by rw [ZMod.card]
  rw [Finset.sum_congr rfl (fun u _ => hterm u), Finset.sum_sub_distrib, ← Finset.mul_sum,
    ← hcard, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, hcardN]
  ring

/-- **The profile-class criterion.** At any window-deviation `Profile`, and any `(K, gTS)`
clearing `8 + capacity(⌈log₂(gTS+1)⌉)` — IN-24's coupling standard, `K` and `gTS` made parameters
rather than the certified instance's fixed `K = 108`, `gTS = 2` — the host is a member of `𝒮_L`:
`L := 2 * K`, the rest fixed at `r = 3`, `c₀ = 1`, `c₁ = 2`, `c₂ = 3`, `δ = 1/2`, `sCodeSize = 8`
(`hostCodeRegion_ncard`). `RegimeWithDepth` follows from `hK` via `3 · log 6 ≤ 6 ≤ 8 ≤ K`
(`Real.exp_one_gt_d9` squared gives `6 < exp 2`, hence `log 6 < 2`, via `Real.log_le_iff_le_exp`);
`ReflectiveCapacity` is `hK` itself. `assumptionA`/`benignSeparation` are facts about `Fin 8` alone
(`LearningWitness.sqDim_singleLiteral_le`), reused verbatim from `BlockPairWitness`'s own proof;
`e1` is `hostSubstrate_mixingHoeffding_schedule` at `a = 0`, `ψ = pairChar`. -/
theorem tapeHost_substrateL (h : TapeHostObservability.Profile o S ρ W) (K : ℝ) (gTS : ℕ)
    (hK : (8 : ℝ) + GodelInternalization.capacity (Nat.clog 2 (gTS + 1)) ≤ K)
    {η τ : ℝ} (hη : 0 ≤ η) (hτ : 2 * η ≤ τ) :
    SubstrateClass.SubstrateL (hostSubUpdate N o) (hostCodeRegion N)
      3 K (2 * K) 1 2 3 (1 / 2) 8 gTS
      True True True True (HostRealizable N o) (LearningWitness.ChainWindowBudget 8 η τ) := by
  have hK8 : (8 : ℝ) ≤ K := by
    have hcap_nonneg : (0 : ℝ) ≤ (GodelInternalization.capacity (Nat.clog 2 (gTS + 1)) : ℝ) :=
      Nat.cast_nonneg _
    linarith
  have hexp2 : (6 : ℝ) ≤ Real.exp 2 := by
    have h1 := Real.exp_one_gt_d9
    have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    rw [h2]; nlinarith [h1]
  have hlog6 : Real.log 6 ≤ 2 := (Real.log_le_iff_le_exp (by norm_num)).mpr hexp2
  have hlog : Real.log ((3 : ℝ) / (1 / 2)) ≤ 2 := by
    have heq : (3 / (1 / 2) : ℝ) = 6 := by norm_num
    rw [heq]; exact hlog6
  refine
    { s1 := hostSubUpdate_fixes N o
      s2 := ⟨by linarith, le_refl _, by norm_num, by norm_num, by norm_num, by norm_num,
        by norm_num, by norm_num⟩
      s3 := ⟨hK, trivial, trivial, trivial, trivial⟩
      realizability := hostRealizable N o
      windowSufficiency := LearningWitness.chainWindowBudget 8 hη hτ
      assumptionA := ?_
      benignSeparation := ⟨1 / 2, 1, by norm_num, by norm_num⟩
      e1 := ⟨Bool, inferInstance,
        (Fintype.card (ZMod N) : ENNReal)⁻¹ • ∑ c : ZMod N, Measure.dirac (hostSubstrateTraj N o c),
        pairEnsemble pairChar 0 8, _, _,
        hostSubstrate_mixingHoeffding_schedule N o h 0 pairChar abs_pairChar_le_one⟩ }
  refine ⟨Fin 8, Fin 8, fun _ => Finset.univ, fun _ => LearningWitness.singleLiteralAns, 0,
    (8 : ℝ), 0, ?_⟩
  filter_upwards with r'
  have hle := LearningWitness.sqDim_singleLiteral_le (k := 8) (0 : ℝ)
  have hcast : (SQObjects.sqDim (Finset.univ : Finset (Fin 8)) 0
      (LearningWitness.singleLiteralAns (k := 8)) : ℝ) ≤ (8 : ℝ) := by exact_mod_cast hle
  simpa using hcast

end TapeHostWitness
