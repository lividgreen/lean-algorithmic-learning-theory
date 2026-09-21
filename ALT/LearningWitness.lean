/-
Copyright (c) 2026 Mykola Palamarchuk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mykola Palamarchuk
-/
module

public import ALT.NoisyWindowChain
public import ALT.SubstrateClass
public import Mathlib.Probability.Distributions.Bernoulli
public import Mathlib.Probability.Independence.InfinitePi

/-!
# A constructed member of `𝒮_L` ([Inevitability] §2 Definition 2.3, Remark 5.3)

[Inevitability] Remark 5.3 says inhabitation of the learning route-class `𝒮_L` "is not in doubt in
outline", and the corpus has so far exhibited no member.  This module exhibits one, at named
parameters, on **one system**.

The system is the noisy window chain of `ALT/NoisyWindowChain.lean`, embedded as a
`Decoupling.Mem`-substrate.  Its memory splits into three regions — `k` code cells carrying the
committed rule, `k` window cells, and the unconsumed noise stream — and one update `chainUpdate`
drives all three: it reads the rule off the code, applies it to the window, consumes one noise bit,
and never writes the code.  So (S1) is `Decoupling.Fixes` by construction, and the rule persists
along the whole orbit, which is [Decoupling]'s own picture instantiated on this witness.

## The anti-gluing device

The risk this construction has to avoid is the obvious one: state the abstract class's fields at an
abstract inhabitant and *assert* that they are about the chain.  What rules that out is the
**realization theorem** `readObs_iterate_loadChain`: the observation read off the substrate's own
cell along the substrate's own orbit IS `NoisyWindowChain.obs`, pointwise, with no measure theory
in sight.  Every statistical clause below is therefore stated on `substrateTraj` — the substrate's
own process — and proved by rewriting along that theorem.  Nothing is glued.

## Why membership is three theorems and not one

`SubstrateL` has three self-existential fields (`assumptionA`, `benignSeparation`, `e1`) and two
`Prop` parameters, so a bare inhabitation certifies nothing: `substrateL_junk_satisfiable` proves
exactly that, inhabiting the class with `True` for both Props, the empty family for Assumption A,
and `BirkhoffTool.mixingHoeffding_of_nonpos` at `c := 0` for E1.  The content of the real witness
therefore lives in the NAMES its clauses are instantiated at:

* `witness_substrateL` — membership in Definition 2.3's own class, with `Realizability` and
  `WindowSufficiency` instantiated at the named `ChainRealizable` and `ChainWindowBudget`;
* `mixingHoeffding_schedule` — E1 over the learner's whole scheduled query class, on the
  substrate's own process, at named per-branch constants;
* `substrateL_junk_satisfiable` — the guard that makes the first two carry their content.

## Main results

* `chainUpdate`, `loadChain`, `readObs`, `decodeRule` — the substrate, and the reading of the rule
  off its code region.  `chainUpdate_reads_code` proves the update genuinely consults the code;
  `chainUpdate_fixes` and `code_persists` are (S1) and its orbit form.
* `readObs_iterate_loadChain` — **the realization theorem** (above).
* `noiseLaw`, `iIndepFun_noiseCoord`, `integral_zeta_noiseCoord` — a Bernoulli(`η`) shift making the
  whole hypothesis block inhabited at every noise rate, so the theorems below are not vacuous.
* `singleLiteral_separation` — distinct single-literal predictors disagree on exactly half the
  windows: the named `ε₀ = 1/2`.
* `ChainRealizable`, `ChainWindowBudget` — the two named `Prop`s, the second carrying [SQ] §3.1's
  budget `2η ≤ τ` together with the answer displacement it prices.
* `mixingHoeffding_schedule` — E1 over the schedule `∀ a : Fin k`, on `substrateTraj`: the
  same-class constant `samePairConst k` at `a = 0` (the rule's own literal) and the cross-class
  `pairConst k η` elsewhere.
* `witness_substrateL_of_e1` — the membership capstone abstracted over its `e1` source: every other
  field is proved unconditionally, and `witness_substrateL` re-derives from it at the schedule's own
  instance, statement byte-identical.
* `witness_substrateL` — **the membership capstone**; `witness_substrateL_bernoulli` instantiates
  it at that shift, leaving no probabilistic hypothesis standing.
* `witness_reachesThresholdWithin`, `witness_truth_survives` — the two payoffs: the learning branch
  reaching Definition 2.1's threshold end-to-end on a concrete system, and the witness's own oracle
  never `2τ`-pruning the true rule.
* `witness_truth_survives_to` — payoff 2 at the horizon-bounded hypothesis
  `BirkhoffTool.MixingHoeffdingTo N`, the theorem a periodic (deterministic finite) host's E1 would
  consume; `witness_truth_survives` re-derives from it at `N := n`.
* `witness_reachesThresholdWithinAt` — the first payoff at EVERY step of the orbit, in
  `SubstrateClass.ReachesThresholdWithinAt`'s time-indexed form, with the reference codeword pinned
  to the loaded rule encoding.
* `not_mixingHoeffding_frozen_schedule` — at `η = 0` the scheduled E1 fails at a cross-class query
  of the schedule's own shape, at every positive constant.  The noise is load-bearing for the
  witness, not only for the abstract chain.

## Scope

Definition 2.1 itself is the ATEMPORAL condition (`ReachesThresholdWithin`), and stays so.  What
`witness_reachesThresholdWithinAt` adds is the time index on the *committed configuration* alone —
the budget and the four theory conditions carry none — so it is retention on this witness, not a
learning-produces-the-commitment claim, which nothing here attempts.  The four theory conditions
stay carried and uninterpreted at `True`, as everywhere on this route.  The regime parameters are
named concrete values: nothing in Definition 2.2's Lean form ties `r` to the rule's own
complexity.
-/


@[expose] public section

namespace LearningWitness

open MeasureTheory ProbabilityTheory NoisyWindowChain

/-! ## The memory, and the rule read off its code region -/

/-- The witness's cell index: `k` code cells, `k` window cells, and the unconsumed noise stream. -/
abbrev Idx (k : ℕ) : Type := Fin k ⊕ (Fin k ⊕ ℕ)

/-- The witness's memory, in [Decoupling]'s own shape: one `Bool` per cell. -/
abbrev Wit (k : ℕ) : Type := Decoupling.Mem (Idx k) Bool

/-- The **code region**: the cells holding the committed rule.  `chainUpdate` never writes them
(`chainUpdate_fixes`) and always reads them (`chainUpdate_reads_code`). -/
def codeRegion (k : ℕ) : Set (Idx k) := Set.range Sum.inl

/-- **The code region has exactly `k` cells.**  Nothing in `SubstrateClass.Substrate` ties its
`sCodeSize` parameter to the region it names, so the tie is stated rather than assumed: the
membership capstone below passes `sCodeSize := k`, and this is why that is the honest value. -/
theorem codeRegion_ncard (k : ℕ) : (codeRegion k).ncard = k := by
  rw [codeRegion, ← Set.image_univ, Set.ncard_image_of_injective _ Sum.inl_injective,
    Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin]

variable {k : ℕ}

/-- **Reading the rule off the code cells**: the least index whose code cell is set, and `0` when
none is.  A one-hot code at index `i` therefore decodes to `i`. -/
def decodeRule [NeZero k] (s : Wit k) : Fin k :=
  if h : ∃ i : Fin k, s (Sum.inl i) = true then Fin.find _ h else 0

/-- A one-hot code decodes to its own index. -/
private theorem decodeRule_oneHot [NeZero k] (s : Wit k) (i : Fin k)
    (h : ∀ j : Fin k, s (Sum.inl j) = true ↔ j = i) : decodeRule s = i := by
  have hex : ∃ j : Fin k, s (Sum.inl j) = true := ⟨i, (h i).mpr rfl⟩
  rw [decodeRule, dite_eq_left hex]
  refine le_antisymm (Fin.find_le_of_pos hex ((h i).mpr rfl)) ((Fin.le_find_iff hex i).mpr ?_)
  intro m hm hp
  exact absurd ((h m).mp hp) (ne_of_lt hm)

/-- **One step of the witness's own dynamics.**  The code region is copied unchanged; the window
shifts one place and takes as its new last bit the complement of the coordinate the CODE names,
xored with the next unconsumed noise bit; the noise stream shifts by one.

Only the oldest-bit literal makes the noiseless window map a bijection — any other literal's map
loses the oldest bit while its own target coordinate survives, so the uniform law on windows would
not be stationary.  The substrate's law is therefore the literal-`0` rule, and the other `k − 1`
literals live on the learner's side, as predictors it must rule out. -/
def chainUpdate [NeZero k] (s : Wit k) : Wit k := fun x =>
  match x with
  | Sum.inl i => s (Sum.inl i)
  | Sum.inr (Sum.inl i) =>
      if h : (i : ℕ) + 1 < k then s (Sum.inr (Sum.inl ⟨(i : ℕ) + 1, h⟩))
      else xor (!(s (Sum.inr (Sum.inl (decodeRule s))))) (s (Sum.inr (Sum.inr 0)))
  | Sum.inr (Sum.inr j) => s (Sum.inr (Sum.inr (j + 1)))

/-- The observation the substrate emits at the present time: its window's oldest bit. -/
def readObs [NeZero k] (s : Wit k) : Bool := s (Sum.inr (Sum.inl 0))

/-- **Loading a noise word into the memory.**  The code is one-hot at literal `0`; the window cells
take the word's first `k` bits, which ARE the chain's initial window
(`NoisyWindowChain.obs_of_lt`); and the rest of the word is the unconsumed noise stream. -/
def loadChain [NeZero k] (ω : ℕ → Bool) : Wit k := fun x =>
  match x with
  | Sum.inl i => decide ((i : ℕ) = 0)
  | Sum.inr (Sum.inl i) => ω (i : ℕ)
  | Sum.inr (Sum.inr j) => ω (k + j)

/-! ## (S1): the code is read-only, and the update nonetheless reads it -/

/-- **(S1) by construction.**  `chainUpdate` never writes the code region — `Decoupling.Fixes`
verbatim, the invariant [Decoupling] Lemma 3.1 and `RetentionUpperBound.retention_persists`
consume. -/
theorem chainUpdate_fixes [NeZero k] :
    Decoupling.Fixes (chainUpdate (k := k)) (codeRegion k) := by
  rintro s _ ⟨i, rfl⟩
  rfl

/-- **The committed rule persists along the whole orbit** — (S1) iterated, [Decoupling]'s own
picture on this witness. -/
theorem code_persists [NeZero k] (t : ℕ) (s : Wit k) (i : Fin k) :
    (chainUpdate^[t] s) (Sum.inl i) = s (Sum.inl i) :=
  Decoupling.fixes_iterate chainUpdate_fixes t s _ ⟨i, rfl⟩

/-- **The update genuinely consults its code region.**  Two memories agreeing everywhere OUTSIDE
the code — same window, same noise — can still have different updates, because the update applies
the literal the code names.  So "the code carries the rule" is a theorem about `chainUpdate`, not a
comment on it; together with `chainUpdate_fixes` it is the whole decoupled picture: read-only, and
read. -/
theorem chainUpdate_reads_code [NeZero k] (hk : 2 ≤ k) :
    ∃ s s' : Wit k, (∀ x ∉ codeRegion k, s x = s' x) ∧ chainUpdate s ≠ chainUpdate s' := by
  have h0 : (0 : ℕ) < k := by omega
  have h1 : (1 : ℕ) < k := by omega
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
    have hdec : decodeRule (k := k) (fun x => match x with
        | Sum.inl i => decide ((i : ℕ) = 0)
        | Sum.inr (Sum.inl i) => decide ((i : ℕ) = 0)
        | Sum.inr (Sum.inr _) => false) = ⟨0, h0⟩ :=
      decodeRule_oneHot _ _ fun j => by
        simp only [decide_eq_true_eq]
        constructor
        · intro hj; exact Fin.ext hj
        · intro hj; rw [hj]
    have hdec' : decodeRule (k := k) (fun x => match x with
        | Sum.inl i => decide ((i : ℕ) = 1)
        | Sum.inr (Sum.inl i) => decide ((i : ℕ) = 0)
        | Sum.inr (Sum.inr _) => false) = ⟨1, h1⟩ :=
      decodeRule_oneHot _ _ fun j => by
        simp only [decide_eq_true_eq]
        constructor
        · intro hj; exact Fin.ext hj
        · intro hj; rw [hj]
    have hlast : ((k - 1 : ℕ) : ℕ) + 1 < k → False := by omega
    have h := congrFun hcon (Sum.inr (Sum.inl ⟨k - 1, by omega⟩))
    rw [chainUpdate, chainUpdate] at h
    simp only [dite_eq_right (fun hh => hlast hh), hdec, hdec'] at h
    revert h
    simp

/-! ## The realization theorem: the substrate's own process IS the chain -/

/-- The full loaded-orbit invariant: the code stays one-hot at `0`, window cell `i` holds the
observation `i` steps ahead, and noise cell `j` holds the word's `(k + t + j)`-th bit. -/
private theorem iterate_loadChain [NeZero k] (ω : ℕ → Bool) (t : ℕ) :
    (∀ i : Fin k, (chainUpdate^[t] (loadChain (k := k) ω)) (Sum.inl i) = decide ((i : ℕ) = 0))
      ∧ (∀ i : Fin k, (chainUpdate^[t] (loadChain (k := k) ω)) (Sum.inr (Sum.inl i))
          = obs k ω (t + (i : ℕ)))
      ∧ (∀ j : ℕ, (chainUpdate^[t] (loadChain (k := k) ω)) (Sum.inr (Sum.inr j))
          = ω (k + t + j)) := by
  have hkpos : 0 < k := Nat.pos_of_ne_zero (NeZero.ne k)
  induction t with
  | zero =>
    refine ⟨fun i => rfl, fun i => ?_, fun j => ?_⟩
    · rw [Function.iterate_zero_apply, Nat.zero_add]
      exact (obs_of_lt ω i.isLt).symm
    · rw [Function.iterate_zero_apply, Nat.add_zero]
      rfl
  | succ t ih =>
    obtain ⟨ihc, ihw, ihn⟩ := ih
    have hdec : decodeRule (chainUpdate^[t] (loadChain (k := k) ω)) = ⟨0, hkpos⟩ :=
      decodeRule_oneHot _ _ fun j => by
        rw [ihc j]
        simp only [decide_eq_true_eq]
        constructor
        · intro hj; exact Fin.ext hj
        · intro hj; rw [hj]
    refine ⟨fun i => ?_, fun i => ?_, fun j => ?_⟩
    · rw [Function.iterate_succ_apply', chainUpdate, ihc i]
    · rw [Function.iterate_succ_apply', chainUpdate]
      by_cases h : (i : ℕ) + 1 < k
      · rw [dite_eq_left h, ihw ⟨(i : ℕ) + 1, h⟩]
        congr 1
        change t + ((i : ℕ) + 1) = t + 1 + (i : ℕ)
        omega
      · have hik : (i : ℕ) + 1 = k := by have := i.isLt; omega
        rw [dite_eq_right h, hdec, ihw ⟨0, hkpos⟩, ihn 0]
        have hz : ((⟨0, hkpos⟩ : Fin k) : ℕ) = 0 := rfl
        rw [hz, Nat.add_zero, Nat.add_zero, show t + 1 + (i : ℕ) = t + k by omega,
          obs_add hkpos ω t, show k + t = t + k by omega]
        cases obs k ω t <;> cases ω (t + k) <;> rfl
    · rw [Function.iterate_succ_apply', chainUpdate, ihn (j + 1)]
      congr 1
      omega

/-- **The realization theorem.**  Reading the substrate's own observation cell along its own
update's orbit, from its own loaded state, reproduces `NoisyWindowChain.obs` exactly — pointwise,
with no measure theory anywhere.

This is what makes every statistical clause below a statement about the SUBSTRATE and not about an
abstract process glued to it: E1 over the schedule is stated on `substrateTraj` and proved by
rewriting along this identity. -/
theorem readObs_iterate_loadChain [NeZero k] (ω : ℕ → Bool) (t : ℕ) :
    readObs (chainUpdate^[t] (loadChain (k := k) ω)) = obs k ω t := by
  have h := (iterate_loadChain (k := k) ω t).2.1 0
  rw [readObs, h, show ((0 : Fin k) : ℕ) = 0 from by simp, Nat.add_zero]

/-- The substrate's OWN observation process, read along its own orbit from its own loaded state. -/
def substrateTraj [NeZero k] {Ω : Type*} (ξ : ℕ → Ω → Bool) (ω : Ω) : ℕ → Bool :=
  fun t => readObs (chainUpdate^[t] (loadChain (k := k) (fun i => ξ i ω)))

/-- The substrate's own process is the chain's trajectory — `readObs_iterate_loadChain`, packaged
for rewriting under `Measure.map`. -/
theorem substrateTraj_eq_traj [NeZero k] {Ω : Type*} (ξ : ℕ → Ω → Bool) :
    substrateTraj (k := k) ξ = traj k ξ := by
  funext ω t
  exact readObs_iterate_loadChain _ t

/-! ## The hypothesis block is inhabited: a Bernoulli shift at every noise rate

Every theorem below carries the same three hypotheses on the noise family — measurability, mutual
independence, and a common character mean.  This section exhibits a family meeting all three at
every rate, so none of them is vacuously satisfied and none is unsatisfiable. -/

/-- The Bernoulli(`p`) shift on `ℕ → Bool`: the infinite product of Bernoulli laws, with the
coordinates as the noise family. -/
noncomputable def noiseLaw (p : unitInterval) : Measure (ℕ → Bool) :=
  Measure.infinitePi fun _ : ℕ => ProbabilityTheory.bernoulliMeasure true false p

instance (p : unitInterval) : IsProbabilityMeasure (noiseLaw p) := by
  rw [noiseLaw]; infer_instance

/-- The noise family: the product space's own coordinates. -/
def noiseCoord (i : ℕ) (ω : ℕ → Bool) : Bool := ω i

theorem measurable_noiseCoord (i : ℕ) : Measurable (noiseCoord i) := measurable_pi_apply i

/-- **The coordinates are mutually independent** under the product law. -/
theorem iIndepFun_noiseCoord (p : unitInterval) : iIndepFun noiseCoord (noiseLaw p) :=
  iIndepFun_infinitePi (𝓧 := fun _ : ℕ => Bool) (X := fun _ => id) fun _ => measurable_id

/-- **The noise character's mean is `2p − 1`** — exactly the form the chain's theorems ask for,
so the noise rate `η` of [SQ] §3.1 is this law's own parameter. -/
theorem integral_zeta_noiseCoord (p : unitInterval) (i : ℕ) :
    ∫ ω, ParityWalk.zeta (noiseCoord i ω) ∂(noiseLaw p) = 2 * (p : ℝ) - 1 := by
  have hmap : (noiseLaw p).map (fun ω : ℕ → Bool => ω i)
      = ProbabilityTheory.bernoulliMeasure true false p :=
    Measure.infinitePi_map_eval _ i
  have h : ∫ ω, ParityWalk.zeta (noiseCoord i ω) ∂(noiseLaw p)
      = ∫ b, ParityWalk.zeta b ∂(ProbabilityTheory.bernoulliMeasure true false p) := by
    rw [← hmap, integral_map (measurable_pi_apply i).aemeasurable
      ParityWalk.measurable_zeta.aestronglyMeasurable]
    rfl
  rw [h, ProbabilityTheory.integral_bernoulliMeasure]
  simp only [ParityWalk.zeta, smul_eq_mul]
  norm_num
  ring

/-! ## The single-literal rule class: separation and statistical query (SQ) dimension -/

/-- The `k` single-literal predictors over a length-`k` window: literal `i` predicts the complement
of window coordinate `i`.  Literal `0` is the substrate's own rule; the other `k − 1` are the
alternatives the learner must rule out. -/
def singleLiteral (i : Fin k) (w : Fin k → Bool) : Bool := !(w i)

/-- Flipping one window coordinate — the involution that pairs the windows where two distinct
literals agree with those where they disagree. -/
private def flipAt (j : Fin k) (w : Fin k → Bool) : Fin k → Bool :=
  Function.update w j (!(w j))

private lemma flipAt_involutive (j : Fin k) : Function.Involutive (flipAt j) := by
  intro w
  funext x
  by_cases hx : x = j
  · subst hx; simp [flipAt]
  · simp [flipAt, Function.update_of_ne hx]

/-- **Benign separation, at the named `ε₀ = 1/2`.**  Two distinct single-literal predictors
disagree on exactly half the length-`k` windows: the uniform stationary window law gives them
separation `1/2`, comfortably above the `Ω(1/r)` [Inevitability] Definition 2.3 asks for.

The proof is a counting bijection: flipping coordinate `j` swaps agreement and disagreement. -/
theorem singleLiteral_separation {i j : Fin k} (hij : i ≠ j) :
    2 * (Finset.univ.filter
        fun w : Fin k → Bool => singleLiteral i w ≠ singleLiteral j w).card = 2 ^ k := by
  have hlit : ∀ w : Fin k → Bool, (singleLiteral i w ≠ singleLiteral j w) ↔ w i ≠ w j := by
    intro w
    simp only [singleLiteral]
    cases w i <;> cases w j <;> simp
  have hflip : ∀ w : Fin k → Bool, (flipAt j w) i = w i ∧ (flipAt j w) j = !(w j) := by
    intro w
    exact ⟨by simp [flipAt, Function.update_of_ne hij], by simp [flipAt]⟩
  have hbij : (Finset.univ.filter fun w : Fin k → Bool => w i = w j).card
      = (Finset.univ.filter fun w : Fin k → Bool => ¬ (w i = w j)).card := by
    refine Finset.card_bij' (fun w _ => flipAt j w) (fun w _ => flipAt j w) ?_ ?_ ?_ ?_
    · intro w hw
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
      rw [(hflip w).1, (hflip w).2, hw]
      simp
    · intro w hw
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
      rw [(hflip w).1, (hflip w).2]
      cases hb : w j <;> cases hb' : w i <;> simp_all
    · intro w _; exact flipAt_involutive j w
    · intro w _; exact flipAt_involutive j w
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin k → Bool))) (p := fun w => w i = w j)
  have hcard : (Finset.univ : Finset (Fin k → Bool)).card = 2 ^ k := by
    rw [Finset.card_univ, Fintype.card_fun]
    simp
  have hre : (Finset.univ.filter fun w : Fin k → Bool => singleLiteral i w ≠ singleLiteral j w)
      = Finset.univ.filter fun w : Fin k → Bool => ¬ (w i = w j) :=
    Finset.filter_congr fun w _ => by simpa using hlit w
  rw [hre]
  omega

/-- The answer a single-literal candidate predicts for the schedule's query at offset `a`: the
correlation of literal `a` with the label is `−1` when `a` is the candidate's own literal (the label
is that coordinate's complement) and `0` otherwise (independent coordinates). -/
def singleLiteralAns (a i : Fin k) : ℝ := if a = i then -1 else 0

/-- **Assumption A on the single-literal family.**  Its statistical dimension never exceeds the
family's own size `k`, so the family's dimension is polynomially bounded — at degree `0`, the
constant `k`.  This is `SQObjects.sqDim_le_card` doing its whole job: the sup runs over subfamilies
of a `k`-element family. -/
theorem sqDim_singleLiteral_le (τ : ℝ) :
    SQObjects.sqDim (Finset.univ : Finset (Fin k)) τ (singleLiteralAns (k := k)) ≤ k := by
  have h := SQObjects.sqDim_le_card (Finset.univ : Finset (Fin k)) τ (singleLiteralAns (k := k))
  simpa using h

/-! ## The two named `Prop`s -/

/-- **Realizability, named.**  The loaded code decodes to literal `0`, and the substrate's own
observation process obeys that literal's rule up to the noise bit — the chain's recursion, read on
the substrate rather than asserted about it. -/
def ChainRealizable (k : ℕ) [NeZero k] : Prop :=
  ∀ ω : ℕ → Bool,
    decodeRule (loadChain (k := k) ω) = 0 ∧
      ∀ t : ℕ, readObs (chainUpdate^[t + k] (loadChain (k := k) ω))
        = !(xor (readObs (chainUpdate^[t] (loadChain (k := k) ω))) (ω (t + k)))

theorem chainRealizable [NeZero k] : ChainRealizable k := by
  have hkpos : 0 < k := Nat.pos_of_ne_zero (NeZero.ne k)
  intro ω
  refine ⟨decodeRule_oneHot _ _ fun j => ?_, fun t => ?_⟩
  · change decide ((j : ℕ) = 0) = true ↔ j = 0
    have hz : ((0 : Fin k) : ℕ) = 0 := by simp
    simp only [decide_eq_true_eq]
    constructor
    · intro hj; exact Fin.ext (by omega)
    · intro hj; rw [hj, hz]
  · rw [readObs_iterate_loadChain, readObs_iterate_loadChain, obs_add hkpos]

/-- The stationary answer to the schedule's query at offset `a`, on the witness's own chain: the
same-class displaced answer at `a = 0` — the rule's own literal, read against the label — and the
flat cross-class answer at every other literal. -/
noncomputable def scheduledMean (k : ℕ) (ψ : Bool → Bool → ℝ) (m : ℝ) (a : Fin k) : ℝ :=
  if (a : ℕ) = 0 then samePairMean ψ m else pairMean ψ

/-- The constant E1 holds at, per branch of the schedule: `samePairConst k = 48k` at the rule's own
literal (no noise rate) and `pairConst k η = O(k/η)` at the others. -/
noncomputable def scheduledConst (k : ℕ) (η : ℝ) (a : Fin k) : ℝ :=
  if (a : ℕ) = 0 then samePairConst k else pairConst k η

/-- **Window sufficiency at the noise budget, named.**  [SQ] §3.1 relaxes exact window determinism
to a window-noise rate `η` under the budget `2η ≤ τ`; what that budget has to buy is that every
query the learner schedules has its stationary answer within `2η` of the answer the NOISELESS rule
would give.  This `Prop` is exactly those two facts.

For a cross-class query both answers are the flat `pairMean ψ` and the displacement is `0`; for the
rule's own literal it is `|pairCoefAB ψ| · 2η ≤ 2η`, met with equality at `ψ = pairChar`.  So the
budget is tight, not slack. -/
def ChainWindowBudget (k : ℕ) (η τ : ℝ) : Prop :=
  2 * η ≤ τ ∧
    ∀ ψ : Bool → Bool → ℝ, (∀ u v, |ψ u v| ≤ 1) → ∀ a : Fin k,
      |scheduledMean k ψ (2 * η - 1) a - scheduledMean k ψ (-1) a| ≤ 2 * η

theorem chainWindowBudget (k : ℕ) {η τ : ℝ} (hη0 : 0 ≤ η) (hbudget : 2 * η ≤ τ) :
    ChainWindowBudget k η τ := by
  refine ⟨hbudget, fun ψ hψ a => ?_⟩
  simp only [scheduledMean]
  split_ifs with h
  · refine le_trans (abs_samePairMean_sub hψ (2 * η - 1) (-1)) ?_
    rw [show 2 * η - 1 - (-1) = 2 * η by ring, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 2 * η)]
  · simpa using by linarith

/-! ## E1 over the whole scheduled query class, on the substrate's own process -/

section Schedule

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {ξ : ℕ → Ω → Bool}

/-- **E1 over the schedule.**  For every literal `a` the learner may test, the two-offset query
correlating literal `a` with the label — offsets `(a, k)` — satisfies the FJS-shaped single-orbit
Hoeffding hypothesis on the SUBSTRATE's own observation process, at the named per-branch constant
`scheduledConst k η a` and the named per-branch stationary answer `scheduledMean k ψ (2η−1) a`.

Two branches, and they are the two the chain's own theorems cover.  At `a = 0` — the rule's own
literal against the label it predicts — the offsets sit in one residue class at lag exactly `k`, the
pair character is the noise character, and the constant `48k` carries no noise rate while the answer
is displaced (`NoisyWindowChain.mixingHoeffding_noisyWindowChain_pair_lagK`).  At `a ≠ 0` the
offsets sit in distinct classes, the answer is flat, and the constant is
`pairConst k η = O(k/η)` (`NoisyWindowChain.mixingHoeffding_noisyWindowChain_pair`).  Nothing
outside these two cases is scheduled: a single-literal decision list's every query reads exactly two
observations.

That this is a statement about the substrate and not about a process attached to it is
`substrateTraj_eq_traj`, i.e. the realization theorem. -/
theorem mixingHoeffding_schedule [NeZero k] (hmeas : ∀ i, Measurable (ξ i))
    (hindep : iIndepFun ξ P) {η : ℝ} (hη0 : 0 < η) (hη1 : η ≤ 1 / 2)
    (hmean : ∀ u, ∫ ω, ParityWalk.zeta (ξ (u + k) ω) ∂P = 2 * η - 1)
    (a : Fin k) (ψ : Bool → Bool → ℝ) (hψ : ∀ u v, |ψ u v| ≤ 1) :
    BirkhoffTool.MixingHoeffding (Measure.map (substrateTraj (k := k) ξ) P)
      (pairEnsemble ψ (a : ℕ) k) (scheduledMean k ψ (2 * η - 1) a) (scheduledConst k η a) := by
  have hkpos : 0 < k := Nat.pos_of_ne_zero (NeZero.ne k)
  rw [substrateTraj_eq_traj]
  simp only [scheduledMean, scheduledConst]
  split_ifs with h
  · -- the rule's own literal: the same-class lag-`k` pair
    have hlag := mixingHoeffding_noisyWindowChain_pair_lagK (k := k) (ξ := ξ) (P := P)
      hkpos hmeas hindep hmean (by linarith) (by linarith) (a : ℕ) ψ hψ
    rw [h, Nat.zero_add] at hlag
    rw [h]
    exact hlag
  · -- a wrong literal: the offsets read distinct residue classes
    have hab : ¬ (a : ℕ) ≡ k [MOD k] := by
      intro hc
      have h1 : (a : ℕ) % k = k % k := hc
      rw [Nat.mod_self, Nat.mod_eq_of_lt a.isLt] at h1
      exact h h1
    exact mixingHoeffding_noisyWindowChain_pair hkpos hmeas hindep hη0 hη1 hmean hab ψ hψ

end Schedule

/-! ## The membership capstone, and the two payoffs -/

/-- **A constructed member of `𝒮_L`, abstracted over its `e1` source** ([Inevitability] Definition
2.3), at named parameters.  Every field but `e1` is proved unconditionally here: `chainUpdate_fixes`
is (S1) by construction, the regime numerals are (S2)/(S3), `chainRealizable` and
`sqDim_singleLiteral_le` need no probability hypothesis at all, and `chainWindowBudget` asks only
`0 ≤ η` and the budget `2η ≤ τ` — both carried as ordinary hypotheses here, with no mixing rate
behind them.  So the one field this theorem does NOT discharge is exactly the one `SubstrateL`'s
own docstring already flags as "carried, not proved": `e1` stays a genuine hypothesis, at whatever
probability space supplies it.

`witness_substrateL` below re-derives from this at the schedule's own instance
(`mixingHoeffding_schedule` at `a = 0`), statement byte-identical. -/
theorem witness_substrateL_of_e1 [NeZero k] {η τ : ℝ} (hη0 : 0 ≤ η) (hbudget : 2 * η ≤ τ)
    (he1 : ∃ (X : Type) (_inst : MeasurableSpace X) (μ : MeasureTheory.Measure (ℕ → X))
             (Z : ℕ → (ℕ → X) → ℝ) (predZ c : ℝ), BirkhoffTool.MixingHoeffding μ Z predZ c) :
    SubstrateClass.SubstrateL (chainUpdate (k := k)) (codeRegion k)
      3 ((k : ℝ) + 100) (2 * ((k : ℝ) + 100)) 1 2 3 (1 / 2) k 2
      True True True True (ChainRealizable k) (ChainWindowBudget k η τ) := by
  have hkR : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  have hlog : Real.log (3 / (1 / 2)) ≤ 3 / (1 / 2) - 1 := Real.log_le_sub_one_of_pos (by norm_num)
  have hcap : GodelInternalization.capacity (Nat.clog 2 (2 + 1)) = 4 := by decide
  refine
    { s1 := chainUpdate_fixes
      s2 := ⟨by nlinarith, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num,
        by norm_num, by norm_num⟩
      s3 := ⟨by rw [hcap]; push_cast; linarith, trivial, trivial, trivial, trivial⟩
      realizability := chainRealizable
      windowSufficiency := chainWindowBudget k hη0 hbudget
      assumptionA := ?_
      benignSeparation := ⟨1 / 2, 1, by norm_num, by norm_num⟩
      e1 := he1 }
  refine ⟨Fin k, Fin k, fun _ => Finset.univ, fun _ => singleLiteralAns, 0, (k : ℝ), 0, ?_⟩
  filter_upwards with r'
  have := sqDim_singleLiteral_le (k := k) (0 : ℝ)
  have hcast : (SQObjects.sqDim (Finset.univ : Finset (Fin k)) 0
      (singleLiteralAns (k := k)) : ℝ) ≤ (k : ℝ) := by exact_mod_cast this
  simpa using hcast

/-- **A constructed member of `𝒮_L`** ([Inevitability] Definition 2.3), at named parameters.

The system is the substrate above: `chainUpdate` on `Wit k`, with `codeRegion k` as its read-only
code region and `sCodeSize := k`, the region's actual cardinality (`codeRegion_ncard` — nothing in
`Substrate` ties the two, so the tie is stated).  The regime constants are `r = 3`, `K = k + 100`,
`L = 2K`, `c₀ = 1`, `c₁ = 2`, `c₂ = 3`, `δ = 1/2`, and `g(T_S) = 2` — the smallest Gödel number at
which the capacity bridge is non-degenerate, with `K` leaving a headroom of `100` work bits over the
`4` the reflective object needs.

The three prerequisites, and the five learning fields, are `witness_substrateL_of_e1`'s: this
instantiates its `e1` hypothesis at the schedule's own `a = 0` instance on the substrate's own
process (`mixingHoeffding_schedule`).

`0 < η` is required here even though the bare `e1` field would survive at `η = 0`: the E1 the
witness actually discharges is the SCHEDULED one, and `not_mixingHoeffding_frozen_schedule` refutes
that at `η = 0` at every positive constant.  The four theory conditions stay carried at `True`, as
everywhere on this route — and `substrateL_junk_satisfiable` is why that, plus the two named
`Prop`s, is where this theorem's content has to live. -/
theorem witness_substrateL [NeZero k] {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {ξ : ℕ → Ω → Bool} (hmeas : ∀ i, Measurable (ξ i))
    (hindep : iIndepFun ξ P) {η τ : ℝ} (hη0 : 0 < η) (hη1 : η ≤ 1 / 2)
    (hmean : ∀ u, ∫ ω, ParityWalk.zeta (ξ (u + k) ω) ∂P = 2 * η - 1) (hbudget : 2 * η ≤ τ) :
    SubstrateClass.SubstrateL (chainUpdate (k := k)) (codeRegion k)
      3 ((k : ℝ) + 100) (2 * ((k : ℝ) + 100)) 1 2 3 (1 / 2) k 2
      True True True True (ChainRealizable k) (ChainWindowBudget k η τ) :=
  witness_substrateL_of_e1 (le_of_lt hη0) hbudget
    ⟨Bool, inferInstance, Measure.map (substrateTraj (k := k) ξ) P,
      pairEnsemble pairChar 0 k, samePairMean pairChar (2 * η - 1), samePairConst k, by
        have h := mixingHoeffding_schedule (k := k) (ξ := ξ) (P := P) hmeas hindep hη0 hη1 hmean
          0 pairChar abs_pairChar_le_one
        have hz : ((0 : Fin k) : ℕ) = 0 := by simp
        rw [hz] at h
        simpa [scheduledMean, scheduledConst, hz] using h⟩

/-- **The witness, with no probabilistic hypothesis left standing.**  `witness_substrateL` at the
Bernoulli(`η`) shift `noiseLaw`, whose coordinates discharge measurability, mutual independence and
the character mean all three (`measurable_noiseCoord`, `iIndepFun_noiseCoord`,
`integral_zeta_noiseCoord`).  What remains assumed is what [SQ] and [Inevitability] assume anyway:
the budget `2η ≤ τ`, and the four theory conditions carried at `True`.

This is what makes the non-vacuity witness load-bearing rather than decorative — without it the
membership theorem would be a conditional on a hypothesis block nobody had exhibited. -/
theorem witness_substrateL_bernoulli [NeZero k] {η τ : ℝ} (hη0 : 0 < η) (hη1 : η ≤ 1 / 2)
    (hbudget : 2 * η ≤ τ) :
    SubstrateClass.SubstrateL (chainUpdate (k := k)) (codeRegion k)
      3 ((k : ℝ) + 100) (2 * ((k : ℝ) + 100)) 1 2 3 (1 / 2) k 2
      True True True True (ChainRealizable k) (ChainWindowBudget k η τ) := by
  have hp : η ∈ unitInterval := ⟨le_of_lt hη0, by linarith⟩
  refine witness_substrateL (P := noiseLaw ⟨η, hp⟩) (ξ := noiseCoord)
    measurable_noiseCoord (iIndepFun_noiseCoord _) hη0 hη1 (fun u => ?_) hbudget
  simpa using integral_zeta_noiseCoord ⟨η, hp⟩ (u + k)

/-- The witness's leftover work capacity: `K − |s_code| = 100` bits, against the `4` the reflective
object at `g(T_S) = 2` needs. -/
private theorem witness_headroom (k : ℕ) : Nat.floor (((k : ℝ) + 100) - (k : ℝ)) = 100 := by
  rw [show ((k : ℝ) + 100) - (k : ℝ) = 100 by ring]
  norm_num

/-- **Payoff 1: the learning branch, end to end, on a concrete system.**  The witness reaches
[Inevitability] Definition 2.1's threshold in its content-carrying form
(`SubstrateClass.ReachesThresholdWithin`) at its own headroom of `100` work bits — the form that
FAILS below the Gödel sentence's own size, so this is a real condition met, not a bookkeeping
bundle discharged.

Until now `substrateL_reachesThresholdWithin` had no member of `𝒮_L` to consume; this is its first
application to an exhibited system. -/
theorem witness_reachesThresholdWithin [NeZero k] {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {ξ : ℕ → Ω → Bool} (hmeas : ∀ i, Measurable (ξ i))
    (hindep : iIndepFun ξ P) {η τ : ℝ} (hη0 : 0 < η) (hη1 : η ≤ 1 / 2)
    (hmean : ∀ u, ∫ ω, ParityWalk.zeta (ξ (u + k) ω) ∂P = 2 * η - 1) (hbudget : 2 * η ≤ τ) :
    SubstrateClass.ReachesThresholdWithin True True True True 100 2 := by
  have h := SubstrateClass.substrateL_reachesThresholdWithin
    (witness_substrateL hmeas hindep hη0 hη1 hmean hbudget) (le_refl 2)
  rwa [witness_headroom k] at h

/-- **Payoff 1, at every step of the orbit.**  The same crossing in the time-indexed form
(`SubstrateClass.ReachesThresholdWithinAt`), held at EVERY `t` — not merely at one configuration —
under `witness_reachesThresholdWithin`'s own hypothesis list, unchanged.

The reference codeword is pinned to `loadChain ω`'s own code cells, and that pin is what makes the
commitment conjunct carry something: `CommittedOn`'s docstring records that a configuration is
committed to its own content trivially, so what has to be true of the pin is that the update's
behaviour *depends* on the region it names — which on this witness is a theorem
(`chainUpdate_reads_code`: two memories agreeing off the code region can have different updates),
not an unfolding.  The commitment then persists because `chainUpdate` never writes that region
(`code_persists`, i.e. (S1)), and the static conjunct is `witness_reachesThresholdWithin` verbatim,
carrying no time index.

The four theory conditions stay carried at `True`, and the threshold's *budget* is still the
atemporal one: what has become time-indexed is the committed configuration alone, exactly the half
the substrate class's (S1) field pays for. -/
theorem witness_reachesThresholdWithinAt [NeZero k] {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {ξ : ℕ → Ω → Bool} (hmeas : ∀ i, Measurable (ξ i))
    (hindep : iIndepFun ξ P) {η τ : ℝ} (hη0 : 0 < η) (hη1 : η ≤ 1 / 2)
    (hmean : ∀ u, ∫ ω, ParityWalk.zeta (ξ (u + k) ω) ∂P = 2 * η - 1) (hbudget : 2 * η ≤ τ)
    (ω : ℕ → Bool) (t : ℕ) :
    SubstrateClass.ReachesThresholdWithinAt (chainUpdate (k := k)) (codeRegion k)
      (loadChain (k := k) ω) (loadChain (k := k) ω) t True True True True 100 2 := by
  refine ⟨?_, witness_reachesThresholdWithin hmeas hindep hη0 hη1 hmean hbudget⟩
  rintro _ ⟨i, rfl⟩
  exact code_persists t (loadChain (k := k) ω) i

/-- **Payoff 2, at the horizon-bounded hypothesis.**  `witness_truth_survives` with the schedule's
E1 instance taken directly as `BirkhoffTool.MixingHoeffdingTo N` rather than derived from
`mixingHoeffding_schedule`: a horizon `N` and `n ≤ N` thread through, and `hη0` weakens to `0 ≤ η`
since nothing here calls the schedule theorem, so `hindep`, `hmean` and `η ≤ 1/2` are not needed
either.  What survives unchanged is the noise budget itself — `0 ≤ η` and `2η ≤ τ` still price the
displacement `mixing_oracle_truth_survives_noisy_to`'s own `hnoise` argument consumes.

Why it is worth having: a deterministic finite host has a finite period, so a horizon-bounded E1 is
the only kind it can supply, and this is the theorem such a host would consume.

`witness_truth_survives` below re-derives from this at `N := n`, statement byte-identical, via
`mixingHoeffdingTo_of_mixingHoeffding` and `le_rfl`. -/
theorem witness_truth_survives_to [NeZero k] {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {ξ : ℕ → Ω → Bool} (hmeas : ∀ i, Measurable (ξ i))
    {η τ δ : ℝ} (hη0 : 0 ≤ η) (hbudget : 2 * η ≤ τ)
    (ψ : Bool → Bool → ℝ) (hψ : ∀ u v, |ψ u v| ≤ 1) (N n : ℕ) (hn1 : 1 ≤ n) (hnN : n ≤ N)
    (hτ : 0 < τ) (hδ0 : 0 < δ)
    (hn : (2 * samePairConst k / τ ^ 2) * Real.log (2 / δ) ≤ (n : ℝ))
    (hmix : BirkhoffTool.MixingHoeffdingTo N (Measure.map (substrateTraj (k := k) ξ) P)
      (pairEnsemble ψ 0 k) (samePairMean ψ (2 * η - 1)) (samePairConst k)) :
    1 - δ ≤ (Measure.map (substrateTraj (k := k) ξ) P).real
      {o | |samePairMean ψ (-1)
        - SQOracle.empiricalMean (pairEnsemble ψ 0 k) n o| ≤ 2 * τ} := by
  have hkpos : 0 < k := Nat.pos_of_ne_zero (NeZero.ne k)
  have hkR : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hkpos
  have hc : (0 : ℝ) < samePairConst k := by
    rw [show samePairConst k = 48 * (k : ℝ) from rfl]; linarith
  have : IsProbabilityMeasure (Measure.map (substrateTraj (k := k) ξ) P) := by
    rw [substrateTraj_eq_traj]
    exact (Measure.isProbabilityMeasure_map_iff (measurable_traj hkpos hmeas).aemeasurable).mpr
      inferInstance
  refine BirkhoffTool.mixing_oracle_truth_survives_noisy_to _ _ (samePairMean ψ (-1))
    (samePairMean ψ (2 * η - 1)) (samePairConst k) N n τ δ η hmix hc
    (fun i => measurable_pairEnsemble ψ 0 k i) hn1 hnN hτ hδ0 hn hη0 hbudget ?_
  refine le_trans (abs_samePairMean_sub hψ (2 * η - 1) (-1)) ?_
  rw [show 2 * η - 1 - (-1) = 2 * η by ring, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 2 * η)]

/-- **Payoff 2: the witness's own oracle never prunes the truth.**  On the rule's own query — the
same-class pair at `a = 0` — the single-orbit empirical answer stays within `2τ` of the answer the
NOISELESS rule predicts, with probability `≥ 1 − δ`, at the sample bound
`n ≥ (2c/τ²)·log(2/δ)` with `c = samePairConst k`.  So the unchanged `2τ`-pruning rule of
[SQ] §3.2 never discards the true rule on this system.

This is the composition [Inevitability] Remark 5.3's outline could not complete — window
sufficiency and E1 met together — completed at [SQ] §3.1's own `η`-relaxation: the displacement
`hnoise` is exactly `ChainWindowBudget`'s second clause, and `hbudget` its first.  Reaches
`witness_truth_survives_to` at `N := n` off the schedule's own E1 instance. -/
theorem witness_truth_survives [NeZero k] {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {ξ : ℕ → Ω → Bool} (hmeas : ∀ i, Measurable (ξ i))
    (hindep : iIndepFun ξ P) {η τ δ : ℝ} (hη0 : 0 < η) (hη1 : η ≤ 1 / 2)
    (hmean : ∀ u, ∫ ω, ParityWalk.zeta (ξ (u + k) ω) ∂P = 2 * η - 1) (hbudget : 2 * η ≤ τ)
    (ψ : Bool → Bool → ℝ) (hψ : ∀ u v, |ψ u v| ≤ 1) (n : ℕ) (hn1 : 1 ≤ n) (hτ : 0 < τ)
    (hδ0 : 0 < δ)
    (hn : (2 * samePairConst k / τ ^ 2) * Real.log (2 / δ) ≤ (n : ℝ)) :
    1 - δ ≤ (Measure.map (substrateTraj (k := k) ξ) P).real
      {o | |samePairMean ψ (-1)
        - SQOracle.empiricalMean (pairEnsemble ψ 0 k) n o| ≤ 2 * τ} := by
  have hmix := mixingHoeffding_schedule (k := k) (ξ := ξ) (P := P) hmeas hindep hη0 hη1 hmean
    0 ψ hψ
  have hz : ((0 : Fin k) : ℕ) = 0 := by simp
  rw [hz] at hmix
  simp only [scheduledMean, scheduledConst, hz] at hmix
  exact witness_truth_survives_to hmeas (le_of_lt hη0) hbudget ψ hψ n n hn1 le_rfl hτ hδ0 hn
    (BirkhoffTool.mixingHoeffdingTo_of_mixingHoeffding n _ _ _ _ hmix)

/-! ## The guards -/

/-- The pinning behind the frozen-schedule guard: at the scheduled offsets `(2, 3)` — a *wrong*
literal against the label at `k = 3` — the noiseless observation alternates, so the two observations
are complementary at every time and their pair character never leaves `−1`. -/
private lemma frozen_pin_two_three (t : ℕ) :
    pairChar (obs 3 frozenWord (t + 2)) (obs 3 frozenWord (t + 3)) = -1 := by
  rw [frozen_obs_shift t, frozen_obs_add t, pairChar, ParityWalk.chi_not]
  cases obs 3 frozenWord t <;> norm_num [ParityWalk.chi]

/-- **The frozen-schedule refutation.**  At `η = 0` the scheduled E1 fails, at a query of the
schedule's OWN shape: window length `3`, offsets `(2, 3)` — literal `2` against the label — and the
flat cross-class answer `pairMean ψ` the schedule declares there.  The predicate is refutable at
every positive constant.

So `0 < η` in `witness_substrateL` is load-bearing for the clause the witness actually discharges,
even though the bare `e1` field of `SubstrateL` would survive at `η = 0` — which is exactly the
weakness `substrateL_junk_satisfiable` records.  The perturbation test is the noise itself: restore
any `η > 0` and `NoisyWindowChain.mixingHoeffding_noisyWindowChain_pair` covers this very query at
`pairConst k η`. -/
theorem not_mixingHoeffding_frozen_schedule {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {c : ℝ} (hc : 0 < c) :
    ¬ BirkhoffTool.MixingHoeffding (Measure.map (traj 3 (fun i (_ : Ω) => frozenWord i)) P)
        (pairEnsemble pairChar 2 3) (pairMean pairChar) c := by
  refine not_mixingHoeffding_pinned_pair P (by norm_num) frozenWord pairChar hc
    frozen_pin_two_three ?_
  rw [pairMean_pairChar]; norm_num

/-- **The finite-horizon form.**  At `η = 0` the scheduled E1 fails at every horizon `N` clearing
`BirkhoffTool.not_mixingHoeffdingTo_pinned`'s own threshold, at the same query, window and offsets
as `not_mixingHoeffding_frozen_schedule` — the two-line consequence of the ported pinned device
`not_mixingHoeffdingTo_pinned_pair`. -/
theorem not_mixingHoeffdingTo_frozen_schedule {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {c : ℝ} (hc : 0 < c) {N : ℕ}
    (hN : ⌈2 * c * Real.log 2⌉₊ + 1 ≤ N) :
    ¬ BirkhoffTool.MixingHoeffdingTo N (Measure.map (traj 3 (fun i (_ : Ω) => frozenWord i)) P)
        (pairEnsemble pairChar 2 3) (pairMean pairChar) c := by
  refine not_mixingHoeffdingTo_pinned_pair P (by norm_num) frozenWord pairChar hc hN
    frozen_pin_two_three ?_
  rw [pairMean_pairChar]; norm_num

/-- **The junk-membership guard.**  `SubstrateL` is satisfiable by nothing in particular: its two
`Prop` parameters accept `True`, its `assumptionA` accepts the EMPTY rule family, its
`benignSeparation` accepts any `ε₀` at all, and its `e1` accepts `c := 0`, at which
`BirkhoffTool.mixingHoeffding_of_nonpos` holds for every law and every ensemble.  The witness is the
identity update on a one-cell memory — a system with no dynamics, no rule, and no observations.

This is why `witness_substrateL`'s content lives in the NAMES its clauses are instantiated at —
`ChainRealizable`, `ChainWindowBudget`, and the schedule theorem's own constants — and not in the
membership statement as such. -/
theorem substrateL_junk_satisfiable :
    ∃ (ι V : Type) (U : Decoupling.Mem ι V → Decoupling.Mem ι V) (R : Set ι)
      (r K L c₀ c₁ c₂ δ : ℝ) (sCodeSize gTS : ℕ),
      SubstrateClass.SubstrateL U R r K L c₀ c₁ c₂ δ sCodeSize gTS
        True True True True True True := by
  refine ⟨Unit, Bool, id, Set.univ, 3, 100, 200, 1, 2, 3, 1 / 2, 0, 2, ?_⟩
  have hlog : Real.log (3 / (1 / 2)) ≤ 3 / (1 / 2) - 1 := Real.log_le_sub_one_of_pos (by norm_num)
  have hcap : GodelInternalization.capacity (Nat.clog 2 (2 + 1)) = 4 := by decide
  refine
    { s1 := fun _ _ _ => rfl
      s2 := ⟨by nlinarith, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num,
        by norm_num, by norm_num⟩
      s3 := ⟨by rw [hcap]; norm_num, trivial, trivial, trivial, trivial⟩
      realizability := trivial
      windowSufficiency := trivial
      assumptionA := ⟨Empty, Empty, fun _ => ∅, fun _ _ _ => 0, 0, 0, 0, ?_⟩
      benignSeparation := ⟨1, 1, by norm_num, by norm_num⟩
      e1 := ⟨Bool, inferInstance, Measure.dirac (fun _ => false), fun _ _ => 0, 0, 0,
        BirkhoffTool.mixingHoeffding_of_nonpos _ _ _ _ le_rfl⟩ }
  filter_upwards with r'
  have h := SQObjects.sqDim_le_card (∅ : Finset Empty) (0 : ℝ)
    (fun (_ : Empty) (_ : Empty) => (0 : ℝ))
  simp only [Finset.card_empty, Nat.le_zero] at h
  rw [h]
  norm_num

end LearningWitness

/-! ## Axiom audit

The realization theorem, the schedule's E1, the membership capstone, its two payoffs and the two
guards are all `#print axioms`-clean on the standard triple, and the guards below make that
build-enforced. -/

set_option linter.style.longLine false

/-- info: 'LearningWitness.readObs_iterate_loadChain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LearningWitness.readObs_iterate_loadChain

/-- info: 'LearningWitness.chainUpdate_reads_code' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LearningWitness.chainUpdate_reads_code

/-- info: 'LearningWitness.singleLiteral_separation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LearningWitness.singleLiteral_separation

/-- info: 'LearningWitness.iIndepFun_noiseCoord' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LearningWitness.iIndepFun_noiseCoord

/-- info: 'LearningWitness.integral_zeta_noiseCoord' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LearningWitness.integral_zeta_noiseCoord

/-- info: 'LearningWitness.mixingHoeffding_schedule' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LearningWitness.mixingHoeffding_schedule

/-- info: 'LearningWitness.witness_substrateL_of_e1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LearningWitness.witness_substrateL_of_e1

/-- info: 'LearningWitness.witness_substrateL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LearningWitness.witness_substrateL

/-- info: 'LearningWitness.witness_substrateL_bernoulli' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LearningWitness.witness_substrateL_bernoulli

/-- info: 'LearningWitness.witness_reachesThresholdWithin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LearningWitness.witness_reachesThresholdWithin

/-- info: 'LearningWitness.witness_reachesThresholdWithinAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LearningWitness.witness_reachesThresholdWithinAt

/-- info: 'LearningWitness.witness_truth_survives_to' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LearningWitness.witness_truth_survives_to

/-- info: 'LearningWitness.witness_truth_survives' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LearningWitness.witness_truth_survives

/-- info: 'LearningWitness.not_mixingHoeffding_frozen_schedule' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LearningWitness.not_mixingHoeffding_frozen_schedule

/-- info: 'LearningWitness.not_mixingHoeffdingTo_frozen_schedule' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LearningWitness.not_mixingHoeffdingTo_frozen_schedule

/-- info: 'LearningWitness.substrateL_junk_satisfiable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LearningWitness.substrateL_junk_satisfiable
