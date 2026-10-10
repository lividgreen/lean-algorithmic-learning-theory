/-
Copyright (c) 2026 Mykola Palamarchuk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mykola Palamarchuk
-/
module

public import Mathlib.Data.Fintype.CardEmbedding
public import ALT.Persistence.Counting
public import CellularAutomata.MemoryWidth
-- Formal-check file, not Mathlib-destined: opt out of the house-style header linter.
set_option linter.style.header false

/-!
# The pricing economy's growing form: the counting core ([Persistence] §6, §7; [Guests] §7)

`ALT.Persistence.Counting` prices a description-bounded observer of a FIXED carrier — the graded
ledger (Theorem 6.4) and the Collapse Theorem (Theorem 7.3) are both stated over permutations of a
fixed `n`-state core. `[Guests]` §7 gives the corpus its growing carrier (the merge quotient's
retained profile, `GrowingCore.mergeStage`) but no priced economy over it: Proposition 7.4 there
disclaims carrying over its finite branch's pricing and ownership clauses for a guest, and
`[Persistence]`'s fixed-carrier economy has no growing counterpart at all.
The two fixed-carrier theorems transport by two different routes, because they rest on two different
facts about a permutation world. Theorem 7.3 rests on DETERMINATION — persistence at `t = 1` makes
`U` invertible, so a later frame fixes the earlier world outright — and determination is false for
a stage law that is merely injective (`exists_ne_frames_agreeing_on_range` below): the theorem does
not transport, and no clause below assumes it does. Theorem 6.4 rests only on a COSET count — no
inverse, no group, no transitive action — and that count DOES transport, with falling factorials
where the fixed-carrier count has ordinary ones (`card_lawsConsistentWith`), because an embedding's
consistency with a given pair of frames is a fibrewise condition whether or not the embedding is
invertible.

This module states the counting core at bare enumerated finite types (`Fin n ↪ Fin m`), exactly as
`ALT.Persistence.Counting` states the fixed-carrier collapse at `Perm (Fin n)` rather than at an
abstract world. Connecting a particular growing world's stages to these numerals needs the
finiteness hypothesis a general stage family does not carry (`ALT.GrowingWorld.Advances` has none)
threaded explicitly at each stage — `stageLawEmb` and `collapse_union_growing` below take exactly
that step, at a chosen enumeration of the two retained profiles named finite.

An earlier round of this module landed a hypothesis-form collapse quantified over ALL affordable
frame pairs; that quantifier is VACUOUS — a coarse (constant) frame is always affordable and always
admits the whole law population, so no deductible bound `D` short of the population itself can ever
satisfy it. `PersistenceCapacity.collapse_union` (`[Persistence] §7`, Corollary 7.4) faces exactly
this at a fixed carrier and answers it by tuning the budget PER FRAME to that frame's own carried
entropy and summing with the Kraft inequality rather than fixing one uniform deductible: transported
here, that excludes the constant frame outright, because its deductible IS the whole population.
`collapse_union_staged` below is that transported bound, `kraft_lensCode` the two-frame Kraft step
it needs, and `exists_qualifying_pair_of_pos` the witness proving its exceptional set is not itself
empty — the property the deleted hypothesis-form bound never had.

## Main results

* `exists_ne_frames_agreeing_on_range` — **determination fails**: whenever the domain is strictly
  smaller than the codomain, two distinct later frames can agree on an embedding's whole image and
  differ only off it, so no clause below may assume a later frame is unique.
* `card_stageLaws` — **the law population**: the embeddings `Fin n ↪ Fin m` number the descending
  factorial `m.descFactorial n`, Mathlib's own count, standing where `Sym([n])`'s `n!` stands at a
  fixed carrier.
* `card_lawsConsistentWith` — **the deductible, exact**: the embeddings consistent with a GIVEN pair
  of frames number a product of descending factorials, one per fibre of the earlier frame — falling
  factorials where Theorem 6.4's coset term has ordinary factorials.
* `card_stageLaws_self` / `card_lawsConsistentWith_self` — **the constant-stage recovery**: at equal
  carrier sizes and equal frames, both counts collapse to their fixed-carrier originals
  (`Fintype.card_perm`'s count and `PersistenceCapacity.card_stabilizer_lens`'s coset term), by
  `Nat.descFactorial_self` alone — the degenerate case that makes the growing counts genuine
  generalizations rather than a coincidence of shape.
* `kraft_lensCode` — **the Kraft sum over frames**: `lensCode` is injective at any FIXED domain and
  codomain, so the object-indexed Kraft inequality reindexes along it directly — no restriction to
  surjective lenses is needed, unlike `PersistenceCapacity.collapse_union`'s own Kraft step, which
  must recover injectivity across VARYING codomains.
* `collapse_union_staged` — **the Kraft union collapse, pair form**: since no later frame is
  determined, the growing bound sums the exact per-pair count over ALL frame pairs at once —
  Corollary 7.4's shape rather than Theorem 7.3's, and TWO Kraft factors rather than one, because a
  growing stage law pays for both ends of the pair.
* `exists_qualifying_pair_of_pos` — **non-vacuity**: some pair genuinely lands in
  `collapse_union_staged`'s exceptional set, at the identity lens on a large enough carrier — the
  property whose absence made the deleted hypothesis-form bound vacuous.
* `deductible_smul_invariant`, `sum_deductible_eq_card_stageLaws`, `orbit_mul_deductible_le` —
  **the engine** ([Guests] §7 Theorem 7.13(i)): a frame's relabelling class times its deductible
  against any later frame never exceeds the candidate population, needing neither an inverse nor
  an orbit–stabilizer count at the second carrier.
* `StagedBudgetedEntropies`, `CbHs`, `CbHs_collapse` — **the staged capacity, and its cap**
  ([Guests] §7 Definition 7.12, Theorem 7.13(ii)): the largest carried entropy of a budget-`b`
  frame pair consistent with a candidate, capped outside a `2^{-d}` fraction at `2b + d + 2` —
  proved, like `collapse_union_staged`, at a fixed label count rather than by a union over every
  count.
* `stageLawEmb` — **the stage law, transported**: `GrowingCore.advances_mergeStage` and
  `GrowingCore.mergeStage_injOn` assembled, at a chosen enumeration of the two retained
  profiles, into the embedding the numerals below need.
* `collapse_union_growing` — **the collapse, at a growing world**: `collapse_union_staged` read at
  `stageLawEmb`'s own domain and codomain, together with the fact that the growing world's own
  stage-to-stage law is one genuine inhabitant of the population being priced.
* `markingLens_comp_embedding`, `CbHs_ge_marking`, `CbH_le_CbHs` — **the floor, and the
  constant-stage recovery** ([Guests] §7 Theorem 7.13(iii)–(iv)): a marking family transported
  FORWARD along any candidate floors the staged capacity uniformly in the stage law, and dropping
  `PermCarries`'s surjectivity recovers the fixed-carrier capacity as the staged one at `U`'s own
  embedding.
* `CbHs_collapse_growing` — **the staged cap and floor, at a growing world**: `CbHs_collapse` read
  at `stageLawEmb`'s own domain and codomain, in `collapse_union_growing`'s own shape.
* `exists_candidate_capacity_le` — **the floor is optimal** ([Guests] §7 Theorem 7.13(vi)): no
  family floors the staged capacity above `2b + 3` uniformly in the stage law — some candidate
  holds every affordable pair to that bound, one line from `CbHs_collapse` at `d = 1`.
* `collapse_union_growing_natSucc_slowClock` — **the guard**: `collapse_union_growing` instantiated
  at the successor world's initial-segment stages, an already-landed world, with `t + 1` and `t + 2`
  falling straight out of `MemoryWidth.mergeStage_nat_succ_slowClock_encard`.
* `telescopeU`, `telescopeΩ`, `advances_telescopeU`, `mergeStage_telescope_finite`,
  `mergeStage_telescope_ncard`, `telescope_realizes_lawSequence` — **the telescope**: the
  construction [Guests] §7 Theorem 7.11's boundary paragraph names but the artifact did not build —
  for any sequence of injections between arbitrary stage sizes, a growing world whose own stage law
  is exactly that sequence, transported along a chosen enumeration.

## Scope

The complexity-FORM transport — Theorem 6.4's `K(U) ≤ …` display itself, rather than the population
it counts — is not attempted here: it needs the source module's decoder scaffolding (candidate
enumeration, a validity predicate, a `Primrec` encoding builder) rebuilt at an embedding numeral in
place of `PersistenceCapacity`'s permutation numeral, machinery on the scale of
`ALT.Persistence.Counting`'s own graded-ledger section rather than an addition to it.

The bridge from a particular growing world's stages (`ALT.GrowingWorld.Advances`,
`GrowingCore.mergeStage`) to the bare numerals this module counts IS taken, by `stageLawEmb` and
`collapse_union_growing` below. The stage-to-stage injection a growing world's own law supplies is
already exactly `GrowingCore.mergeStage_injOn` composed with
`GrowingCore.advances_mergeStage`, and building the embedding from it needs nothing further — an
earlier note here predicted `MemoryWidth.reaches_mergeLaw` would be the one further fact a
growing carrier needs, but the landed bridge does not consume it: reachability under the INDUCED
law is a different question from the one stage-to-stage step this bridge transports. The transported
statement is relative to a CHOSEN enumeration of the two retained profiles (`Set.Finite.toFinset`) —
the same enumeration-relativity `[Persistence]` §2.1's encoding convention already carries and
`[Persistence]` §5's `C_b` is stated against — and it prices only the stage-to-stage law itself: it
is silent about the world's law on states outside the two named profiles.
-/


@[expose] public section

namespace GrowingPrice

open PersistenceCapacity AdditiveComplexity GrowingWorld GrowingCore MemoryWidth MulAction
open scoped Nat

-- `orbit`/`•` on lenses is `PersistenceCapacity`'s relabelling action (`(U • ℓ) x = ℓ (U⁻¹ x)`,
-- Mathlib's `arrowAction`); its own local instance does not export past that file's own
-- `section Collapse`, so it is re-opened here for the same reason `FrameItinerary.lean` does.
attribute [local instance] arrowAction

/-- `(U • ℓ) x = ℓ (U⁻¹ x)`, restated because `PersistenceCapacity.smul_lens_apply` is
file-private. -/
private theorem smul_lens_apply' {α β : Type*} (U : Equiv.Perm α) (ℓ : α → β) (x : α) :
    (U • ℓ) x = ℓ (U⁻¹ x) := rfl

/-! ## Determination fails for an injective stage law -/

/-- **Determination fails** ([Persistence] §7, Theorem 7.3's proof): over a permutation world the
proof reads persistence at `t = 1` as `ℓ_1(U s) = ℓ_0(s)` with `U` invertible, so `ℓ_1 = ℓ_0 ∘ U⁻¹`
outright and the later frame is determined by `(ℓ_0, U)`. An injective stage law has no inverse to
invoke: whenever the domain is strictly smaller than the codomain, some point sits outside the
embedding's range, and two frames that agree everywhere on the range can differ there — so the
embedding alone pins down no unique later frame. This is why `collapse_union_staged` below is stated
over PAIRS of frames rather than a single determined one. -/
theorem exists_ne_frames_agreeing_on_range {n m : ℕ} (h : n < m) (μ : Fin n ↪ Fin m) :
    ∃ ℓ' ℓ'' : Fin m → Fin 2, ℓ' ≠ ℓ'' ∧ ∀ q, ℓ' (μ q) = ℓ'' (μ q) := by
  have hnotsurj : ¬ Function.Surjective μ := by
    intro hsurj
    have hle := Fintype.card_le_of_surjective μ hsurj
    simp only [Fintype.card_fin] at hle
    omega
  simp only [Function.Surjective, not_forall, not_exists] at hnotsurj
  obtain ⟨y₀, hy₀⟩ := hnotsurj
  refine ⟨fun _ => 0, fun y => if y = y₀ then 1 else 0, ?_, ?_⟩
  · intro heq
    have hcontra := congrFun heq y₀
    simp at hcontra
  · intro q
    simp only [ite_eq_right (hy₀ q)]

/-! ## The law population -/

/-- **The law population**: the growing analogue of `Fintype.card_perm`'s role at a fixed carrier —
the injective stage laws from an `n`-state world into an `m`-state one number the descending
factorial `m.descFactorial n`, Mathlib's own count for `Fin n ↪ Fin m`
(`Fintype.card_embedding_eq`). -/
theorem card_stageLaws (n m : ℕ) : Nat.card (Fin n ↪ Fin m) = m.descFactorial n := by
  have h : Nat.card (Fin n ↪ Fin m) = Fintype.card (Fin n ↪ Fin m) := Nat.card_eq_fintype_card
  rw [h, Fintype.card_embedding_eq, Fintype.card_fin, Fintype.card_fin]

/-! ## The deductible, exact -/

/-- The fibrewise equivalence behind `card_lawsConsistentWith`: an embedding consistent with a pair
of frames `(ℓ, ℓ')` restricts, fibre by fibre, to an embedding of `ℓ`'s fibre into `ℓ'`'s matching
fibre, and conversely a fibrewise family of embeddings assembles into one global embedding by
`Function.Embedding.sigmaMap` composed with the domain's and codomain's own fibre decompositions
(`Equiv.sigmaFiberEquiv`) — the same fibre bookkeeping `PersistenceCapacity.stabEquivPi` runs at a
single permutation stabilizer, generalized here to two different fibre families. -/
private noncomputable def consistentEquivPi {n m k : ℕ} (ℓ : Fin n → Fin k) (ℓ' : Fin m → Fin k) :
    {μ : Fin n ↪ Fin m // ∀ q, ℓ' (μ q) = ℓ q}
      ≃ ∀ i : Fin k, ({x : Fin n // ℓ x = i} ↪ {y : Fin m // ℓ' y = i}) where
  toFun μ i :=
    { toFun := fun x => ⟨μ.1 x.1, (μ.2 x.1).trans x.2⟩
      inj' := fun x y hxy => Subtype.ext (μ.1.injective (congrArg Subtype.val hxy)) }
  invFun τ :=
    ⟨(Equiv.sigmaFiberEquiv ℓ).symm.toEmbedding.trans
        ((Function.Embedding.sigmaMap (Function.Embedding.refl (Fin k)) τ).trans
          (Equiv.sigmaFiberEquiv ℓ').toEmbedding),
     fun q => (τ (ℓ q) ⟨q, rfl⟩).2⟩
  left_inv μ := by
    apply Subtype.ext
    apply Function.Embedding.ext
    intro x
    rfl
  right_inv τ := by
    funext i
    apply Function.Embedding.ext
    rintro ⟨x, rfl⟩
    rfl

/-- **The deductible, exact** ([Persistence] §6, Theorem 6.4's proof, transported): at a permutation
world the worlds carrying a fixed frame `ℓ_0` to a given later frame `ℓ_1` form one coset of `ℓ_0`'s
fibre stabilizer, of size `∏ᵢ (fiberᵢ)!` (`PersistenceCapacity.card_stabilizer_lens`). At a growing
world the later frame `ℓ'` need not determine — and, by `exists_ne_frames_agreeing_on_range`, in
general does not determine — a unique embedding; what survives is that the embeddings consistent
with a GIVEN pair `(ℓ, ℓ')` are exactly the maps carrying each `ℓ`-fibre injectively into the
matching `ℓ'`-fibre, independently fibre by fibre, so their count is a PRODUCT of descending
factorials rather than a product of factorials — falling factorials where Lemma 7.1's stabilizer
count has ordinary ones, and one term per fibre of the EARLIER frame rather than one coset. -/
theorem card_lawsConsistentWith {n m k : ℕ} (ℓ : Fin n → Fin k) (ℓ' : Fin m → Fin k) :
    Nat.card {μ : Fin n ↪ Fin m // ∀ q, ℓ' (μ q) = ℓ q}
      = ∏ i : Fin k, (Nat.card {y : Fin m // ℓ' y = i}).descFactorial
                       (Nat.card {x : Fin n // ℓ x = i}) := by
  classical
  rw [Nat.card_congr (consistentEquivPi ℓ ℓ'), Nat.card_pi]
  refine Finset.prod_congr rfl fun i _ => ?_
  have h1 : Nat.card ({x : Fin n // ℓ x = i} ↪ {y : Fin m // ℓ' y = i})
      = Fintype.card ({x : Fin n // ℓ x = i} ↪ {y : Fin m // ℓ' y = i}) := Nat.card_eq_fintype_card
  rw [h1, Fintype.card_embedding_eq, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]

/-! ## The constant-stage recovery -/

/-- **The constant-stage recovery, population side**: at `m = n` the injective self-maps of a
finite type are exactly its permutations, and `Nat.descFactorial_self` collapses `card_stageLaws`
to `Fintype.card_perm`'s own count — the finite-collapse population reappearing as the degenerate
case of the growing one, rather than assumed independently. -/
theorem card_stageLaws_self (n : ℕ) : Nat.card (Fin n ↪ Fin n) = n ! :=
  (card_stageLaws n n).trans (Nat.descFactorial_self n)

/-- **The constant-stage recovery, deductible side**: at `m = n` and `ℓ' = ℓ`,
`card_lawsConsistentWith`'s falling factorials collapse, again by `Nat.descFactorial_self`, to the
ordinary factorials of `PersistenceCapacity.card_stabilizer_lens` — Theorem 6.4's coset term
exactly, recovered as the degenerate case rather than assumed. This is the sentence that makes the
growing counts genuine generalizations of the finite collapse rather than a coincidence of shape. -/
theorem card_lawsConsistentWith_self {n k : ℕ} (ℓ : Fin n → Fin k) :
    Nat.card {μ : Fin n ↪ Fin n // ∀ q, ℓ (μ q) = ℓ q}
      = ∏ i : Fin k, (Nat.card {x : Fin n // ℓ x = i})! :=
  (card_lawsConsistentWith ℓ ℓ).trans
    (Finset.prod_congr rfl fun i _ => Nat.descFactorial_self (Nat.card {x : Fin n // ℓ x = i}))

/-! ## The Kraft-weighted union, staged -/

/-- `PersistenceCapacity.lensCode_injective`, re-derived: it is private to
`ALT.Persistence.Counting` and this module needs it at its own two domain sizes. -/
private theorem lensCode_injective' {p q : ℕ} :
    Function.Injective (lensCode (n := p) (m := q)) := by
  intro ℓ ℓ' h
  have h2 : lensTable ℓ = lensTable ℓ' := Encodable.encode_injective h
  funext x
  have hx : ((ℓ x : Fin q) : ℕ) = ((ℓ' x : Fin q) : ℕ) :=
    (List.map_inj_left.mp h2) x (List.mem_finRange x)
  exact Fin.val_injective hx

/-- **The Kraft sum over frames, at a fixed domain and codomain** ([Persistence] §7, Corollary
7.4's Kraft step, transported): `lensCode` is injective at any FIXED `(p, q)`
(`lensCode_injective'`), so — unlike `PersistenceCapacity.collapse_union`'s own Kraft step, which
must first restrict to SURJECTIVE lenses to recover injectivity across VARYING codomains — no such
restriction is needed here: reindexing the object-indexed Kraft inequality
`AdditiveComplexity.kraft_KE` along `lensCode` bounds the frame-indexed sum directly.
`collapse_union_staged` below applies this twice, once per frame named. -/
theorem kraft_lensCode (p q : ℕ) :
    ∑' ℓ : Fin p → Fin q, (1 / 2 : ℝ) ^ KE (lensCode ℓ) ≤ 1 := by
  classical
  rw [tsum_fintype]
  have hminj : Function.Injective minCode := minCode_E_injective.of_comp
  have hφinj : Function.Injective (fun ℓ : Fin p → Fin q => minCode (lensCode ℓ)) :=
    hminj.comp lensCode_injective'
  calc ∑ ℓ : Fin p → Fin q, (1 / 2 : ℝ) ^ KE (lensCode ℓ)
      = ∑ ℓ : Fin p → Fin q, (1 / 2 : ℝ) ^ elen (minCode (lensCode ℓ)) :=
        Finset.sum_congr rfl fun ℓ _ => by rw [elen_minCode]
    _ = ∑ c ∈ (Finset.univ.image fun ℓ : Fin p → Fin q => minCode (lensCode ℓ)),
          (1 / 2 : ℝ) ^ elen c := by
          rw [Finset.sum_image fun x _ y _ h => hφinj h]
    _ ≤ 1 := kraft_sum_le_one _

/-- **The Kraft union collapse, pair form** ([Persistence] §7, Corollary 7.4, transported): summing
the per-pair bound over ALL pairs of frames at once — as `PersistenceCapacity.collapse_union` sums
`PersistenceCapacity.collapse_union_frame` over reference frames — except TWO Kraft factors enter
rather than one, because a growing stage law pays for BOTH ends of the pair
(`exists_ne_frames_agreeing_on_range`: no single frame determines the other, so nothing here can be
priced off one reference frame the way a permutation world's second frame is). For every `d`, the
embeddings admitting a frame pair `(ℓ, ℓ')` whose two-frame description still falls `d + 2` below
the EXACT population its consistency class buys number at most `m.descFactorial n / 2 ^ d` — the
budget-`b`, uniform-deductible shape of the deleted hypothesis-form bound replaced by the
Kraft-summed, budget-free bound this module's docstring calls for. -/
theorem collapse_union_staged {n m k : ℕ} (d : ℕ) :
    {μ : Fin n ↪ Fin m | ∃ (ℓ : Fin n → Fin k) (ℓ' : Fin m → Fin k),
       (∀ q, ℓ' (μ q) = ℓ q) ∧
       2 ^ (KE (lensCode ℓ) + KE (lensCode ℓ') + d + 2)
         * Nat.card {μ' : Fin n ↪ Fin m // ∀ q, ℓ' (μ' q) = ℓ q}
         < m.descFactorial n}.ncard * 2 ^ d
      ≤ m.descFactorial n := by
  classical
  set POP := m.descFactorial n with hPOP
  set idx := Finset.univ.filter fun p : (Fin n → Fin k) × (Fin m → Fin k) =>
      2 ^ (KE (lensCode p.1) + KE (lensCode p.2) + d + 2)
        * Nat.card {μ' : Fin n ↪ Fin m // ∀ q, p.2 (μ' q) = p.1 q} < POP with hidxdef
  set T : (Fin n → Fin k) × (Fin m → Fin k) → Set (Fin n ↪ Fin m) :=
    fun p => {μ | ∀ q, p.2 (μ q) = p.1 q} with hTdef
  have hsub : {μ : Fin n ↪ Fin m | ∃ (ℓ : Fin n → Fin k) (ℓ' : Fin m → Fin k),
       (∀ q, ℓ' (μ q) = ℓ q) ∧
       2 ^ (KE (lensCode ℓ) + KE (lensCode ℓ') + d + 2)
         * Nat.card {μ' : Fin n ↪ Fin m // ∀ q, ℓ' (μ' q) = ℓ q} < POP}
      = ⋃ p ∈ idx, T p := by
    ext μ
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, hTdef, hidxdef, Finset.mem_filter,
      Finset.mem_univ, true_and]
    constructor
    · rintro ⟨ℓ, ℓ', hcons, hq⟩
      exact ⟨(ℓ, ℓ'), hq, hcons⟩
    · rintro ⟨⟨ℓ, ℓ'⟩, hq, hcons⟩
      exact ⟨ℓ, ℓ', hcons, hq⟩
  -- (1) union bound: the count is at most the sum of the per-pair counts
  have hUB : ((⋃ p ∈ idx, T p).ncard : ℝ) ≤ ∑ p ∈ idx,
      (Nat.card {μ' : Fin n ↪ Fin m // ∀ q, p.2 (μ' q) = p.1 q} : ℝ) := by
    have h1 : (⋃ p ∈ idx, T p).ncard ≤ ∑ p ∈ idx, (T p).ncard :=
      Finset.set_ncard_biUnion_le idx T
    have h2 : ∀ p ∈ idx, (T p).ncard = Nat.card {μ' : Fin n ↪ Fin m // ∀ q, p.2 (μ' q) = p.1 q} :=
      fun p _ => by rw [hTdef]; exact (Nat.card_coe_set_eq _).symm
    calc ((⋃ p ∈ idx, T p).ncard : ℝ) ≤ ((∑ p ∈ idx, (T p).ncard : ℕ) : ℝ) := by exact_mod_cast h1
      _ = ((∑ p ∈ idx, Nat.card {μ' : Fin n ↪ Fin m // ∀ q, p.2 (μ' q) = p.1 q} : ℕ) : ℝ) := by
          rw [Finset.sum_congr rfl h2]
      _ = ∑ p ∈ idx, (Nat.card {μ' : Fin n ↪ Fin m // ∀ q, p.2 (μ' q) = p.1 q} : ℝ) := by
          push_cast; ring
  -- (2) per-pair real bound, cleared from the qualifying strict inequality
  have hterm : ∀ p ∈ idx, (Nat.card {μ' : Fin n ↪ Fin m // ∀ q, p.2 (μ' q) = p.1 q} : ℝ)
      ≤ (POP : ℝ) * (1 / 2 : ℝ) ^ (d + 2)
          * (1 / 2 : ℝ) ^ KE (lensCode p.1) * (1 / 2 : ℝ) ^ KE (lensCode p.2) := by
    intro p hp
    have hq : 2 ^ (KE (lensCode p.1) + KE (lensCode p.2) + d + 2)
        * Nat.card {μ' : Fin n ↪ Fin m // ∀ q, p.2 (μ' q) = p.1 q} < POP :=
      (Finset.mem_filter.mp hp).2
    have hcast : (Nat.card {μ' : Fin n ↪ Fin m // ∀ q, p.2 (μ' q) = p.1 q} : ℝ)
        * (2 : ℝ) ^ (KE (lensCode p.1) + KE (lensCode p.2) + d + 2) ≤ (POP : ℝ) := by
      have hqle : Nat.card {μ' : Fin n ↪ Fin m // ∀ q, p.2 (μ' q) = p.1 q}
          * 2 ^ (KE (lensCode p.1) + KE (lensCode p.2) + d + 2) ≤ POP := by
        rw [Nat.mul_comm]; exact le_of_lt hq
      exact_mod_cast hqle
    rw [show (POP : ℝ) * (1 / 2 : ℝ) ^ (d + 2) * (1 / 2 : ℝ) ^ KE (lensCode p.1)
          * (1 / 2 : ℝ) ^ KE (lensCode p.2)
          = (POP : ℝ) / (2 : ℝ) ^ (KE (lensCode p.1) + KE (lensCode p.2) + d + 2) by
        rw [one_div, inv_pow, inv_pow, inv_pow, mul_assoc, mul_assoc, ← mul_inv,
          ← mul_inv, ← pow_add, ← pow_add, ← div_eq_mul_inv]
        congr 2
        omega]
    rw [le_div_iff₀ (by positivity)]
    exact hcast
  -- (3) sum the per-pair bound, extending the sum to ALL pairs (nonneg terms)
  have hextend : ∑ p ∈ idx, (Nat.card {μ' : Fin n ↪ Fin m // ∀ q, p.2 (μ' q) = p.1 q} : ℝ)
      ≤ ∑ p : (Fin n → Fin k) × (Fin m → Fin k),
          (POP : ℝ) * (1 / 2 : ℝ) ^ (d + 2)
            * (1 / 2 : ℝ) ^ KE (lensCode p.1) * (1 / 2 : ℝ) ^ KE (lensCode p.2) :=
    (Finset.sum_le_sum hterm).trans
      (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun p _ _ => by positivity))
  -- (4) the double sum factors as a product of two Kraft sums (`kraft_lensCode` twice)
  have hfactor : ∑ p : (Fin n → Fin k) × (Fin m → Fin k),
      (POP : ℝ) * (1 / 2 : ℝ) ^ (d + 2) * (1 / 2 : ℝ) ^ KE (lensCode p.1)
        * (1 / 2 : ℝ) ^ KE (lensCode p.2)
      = (POP : ℝ) * (1 / 2 : ℝ) ^ (d + 2)
          * ((∑ ℓ : Fin n → Fin k, (1 / 2 : ℝ) ^ KE (lensCode ℓ))
            * (∑ ℓ' : Fin m → Fin k, (1 / 2 : ℝ) ^ KE (lensCode ℓ'))) := by
    rw [Fintype.sum_prod_type, Fintype.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun ℓ _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun ℓ' _ => by ring
  have hkraft_n : ∑ ℓ : Fin n → Fin k, (1 / 2 : ℝ) ^ KE (lensCode ℓ) ≤ 1 := by
    have := kraft_lensCode n k; rwa [tsum_fintype] at this
  have hkraft_m : ∑ ℓ' : Fin m → Fin k, (1 / 2 : ℝ) ^ KE (lensCode ℓ') ≤ 1 := by
    have := kraft_lensCode m k; rwa [tsum_fintype] at this
  have hnn_m : (0 : ℝ) ≤ ∑ ℓ' : Fin m → Fin k, (1 / 2 : ℝ) ^ KE (lensCode ℓ') :=
    Finset.sum_nonneg fun _ _ => by positivity
  have hsum_le : ((⋃ p ∈ idx, T p).ncard : ℝ) ≤ (POP : ℝ) * (1 / 2 : ℝ) ^ (d + 2) := by
    calc ((⋃ p ∈ idx, T p).ncard : ℝ)
        ≤ ∑ p ∈ idx, (Nat.card {μ' : Fin n ↪ Fin m // ∀ q, p.2 (μ' q) = p.1 q} : ℝ) := hUB
      _ ≤ ∑ p : (Fin n → Fin k) × (Fin m → Fin k),
          (POP : ℝ) * (1 / 2 : ℝ) ^ (d + 2) * (1 / 2 : ℝ) ^ KE (lensCode p.1)
            * (1 / 2 : ℝ) ^ KE (lensCode p.2) := hextend
      _ = (POP : ℝ) * (1 / 2 : ℝ) ^ (d + 2)
          * ((∑ ℓ : Fin n → Fin k, (1 / 2 : ℝ) ^ KE (lensCode ℓ))
            * (∑ ℓ' : Fin m → Fin k, (1 / 2 : ℝ) ^ KE (lensCode ℓ'))) := hfactor
      _ ≤ (POP : ℝ) * (1 / 2 : ℝ) ^ (d + 2) * (1 * 1) :=
          mul_le_mul_of_nonneg_left (mul_le_mul hkraft_n hkraft_m hnn_m (by norm_num))
            (by positivity)
      _ = (POP : ℝ) * (1 / 2 : ℝ) ^ (d + 2) := by ring
  -- (5) multiply by `2 ^ d` and clear back to ℕ
  have hfinal : ((⋃ p ∈ idx, T p).ncard : ℝ) * (2 : ℝ) ^ d ≤ (POP : ℝ) := by
    calc ((⋃ p ∈ idx, T p).ncard : ℝ) * (2 : ℝ) ^ d
        ≤ (POP : ℝ) * (1 / 2 : ℝ) ^ (d + 2) * (2 : ℝ) ^ d :=
          mul_le_mul_of_nonneg_right hsum_le (by positivity)
      _ = (POP : ℝ) * (1 / 4 : ℝ) := by
          have h1 : (1 / 2 : ℝ) ^ d * (2 : ℝ) ^ d = 1 := by rw [← mul_pow]; norm_num
          calc (POP : ℝ) * (1 / 2 : ℝ) ^ (d + 2) * (2 : ℝ) ^ d
                = (POP : ℝ) * (1 / 4 : ℝ) * ((1 / 2 : ℝ) ^ d * (2 : ℝ) ^ d) := by
                  rw [show (1 / 2 : ℝ) ^ (d + 2) = (1 / 2 : ℝ) ^ d * (1 / 4 : ℝ) by
                    rw [pow_add]; norm_num]
                  ring
            _ = (POP : ℝ) * (1 / 4 : ℝ) := by rw [h1]; ring
      _ ≤ (POP : ℝ) := by nlinarith [Nat.cast_nonneg (α := ℝ) POP]
  rw [hsub]
  exact_mod_cast hfinal

/-! ## Non-vacuity: a witness -/

/-- **A fixed exponential rate is eventually beaten by the factorial** (a standalone arithmetic
fact; needed only for `exists_qualifying_pair_of_pos`'s witness). Built explicitly rather than
invoked asymptotically: at `c := 2 * A + B + 1` and `n := 2 ^ c`, `(n + n)! ≥ n ^ n = 2 ^ (c * n)`
(`Nat.factorial_mul_pow_le_factorial`, doubled), and `c * n` clears `A * (n + n) + B` because
`n > c` (`Nat.lt_two_pow_self`) swamps the fixed offset `B`. -/
private theorem exists_pow_lt_factorial (A B : ℕ) : ∃ N, 2 ^ (A * N + B) < N ! := by
  set c := 2 * A + B + 1 with hc
  set n := 2 ^ c with hn
  have hcn : c < n := by rw [hn]; exact Nat.lt_two_pow_self
  refine ⟨n + n, ?_⟩
  have hstep1 : n ^ n ≤ (n + n)! := by
    have h1 : n ! * (n + 1) ^ n ≤ (n + n)! := Nat.factorial_mul_pow_le_factorial
    have h2 : n ^ n ≤ (n + 1) ^ n := Nat.pow_le_pow_left (Nat.le_succ n) n
    have h3 : n ^ n ≤ n ! * (n + 1) ^ n := by
      calc n ^ n = 1 * n ^ n := (one_mul _).symm
        _ ≤ n ! * (n + 1) ^ n := Nat.mul_le_mul (Nat.factorial_pos n) h2
    exact h3.trans h1
  have hstep2 : n ^ n = 2 ^ (c * n) := by rw [hn, ← pow_mul]
  have hstep3 : A * (n + n) + B < c * n := by
    have hb1 : (1 : ℕ) ≤ n := by omega
    have hge : B + 1 ≤ (B + 1) * n := by
      calc B + 1 = (B + 1) * 1 := (mul_one _).symm
        _ ≤ (B + 1) * n := Nat.mul_le_mul_left (B + 1) hb1
    have hpos : B < (B + 1) * n := by omega
    have hexp : c * n = 2 * A * n + (B + 1) * n := by
      have hcval : c = 2 * A + (B + 1) := by omega
      rw [hcval]; ring
    calc A * (n + n) + B = 2 * A * n + B := by ring
      _ < 2 * A * n + (B + 1) * n := by omega
      _ = c * n := hexp.symm
  calc 2 ^ (A * (n + n) + B) < 2 ^ (c * n) := Nat.pow_lt_pow_right (by norm_num) hstep3
    _ = n ^ n := hstep2.symm
    _ ≤ (n + n)! := hstep1

/-- **Non-vacuity**: some pair genuinely lands in `collapse_union_staged`'s exceptional set — the
property the deleted hypothesis-form bound never had. At `n = m = k = N` and `ℓ = ℓ' = id`,
consistency forces `μ = id` (`μ q = q` for every `q` pins the embedding down completely), so the
count is exactly `1` against the full population `N !` (`Nat.descFactorial_self`); `id`'s own cost
is `O (Nat.size N)` (`PersistenceCapacity.rangeCode`, `lensCode_id`,
`AdditiveComplexity.invariance_general`), and `N !` beats any FIXED rate of exponential growth in
`N` (`exists_pow_lt_factorial`), so a large enough `N` clears the qualifying threshold with
`d := 0` to spare. -/
theorem exists_qualifying_pair_of_pos : ∃ (n m k d : ℕ) (ℓ : Fin n → Fin k) (ℓ' : Fin m → Fin k),
    0 < Nat.card {μ : Fin n ↪ Fin m // ∀ q, ℓ' (μ q) = ℓ q} ∧
    2 ^ (KE (lensCode ℓ) + KE (lensCode ℓ') + d + 2)
      * Nat.card {μ : Fin n ↪ Fin m // ∀ q, ℓ' (μ q) = ℓ q} < m.descFactorial n := by
  classical
  set κ := 15 + elen dbl with hκ
  set C := elen rangeCode + 3 + κ with hCdef
  have hidcost : ∀ N : ℕ, KE (lensCode (id : Fin N → Fin N)) ≤ κ * N + C := by
    intro N
    have heval : Nat.Partrec.Code.eval rangeCode N
        = Part.some (lensCode (id : Fin N → Fin N)) := by
      rw [eval_rangeCode, ← lensCode_id]
    have hinv := invariance_general rangeCode N (lensCode (id : Fin N → Fin N)) heval
    rw [← hκ] at hinv
    have hsize : Nat.size N ≤ N := Nat.size_le.mpr Nat.lt_two_pow_self
    have hmul : κ * Nat.size N ≤ κ * N := Nat.mul_le_mul_left κ hsize
    omega
  obtain ⟨N, hN⟩ := exists_pow_lt_factorial (κ + κ) (C + C + 2)
  have hcount : Nat.card
      {μ : Fin N ↪ Fin N // ∀ q, (id : Fin N → Fin N) (μ q) = (id : Fin N → Fin N) q} = 1 := by
    rw [Nat.card_eq_one_iff_unique]
    refine ⟨⟨fun a b => ?_⟩, ⟨Function.Embedding.refl (Fin N), fun _ => rfl⟩⟩
    apply Subtype.ext
    apply Function.Embedding.ext
    intro x
    exact (a.2 x).trans (b.2 x).symm
  refine ⟨N, N, N, 0, id, id, by omega, ?_⟩
  rw [hcount, Nat.mul_one, N.descFactorial_self]
  have hb := hidcost N
  have h2b : KE (lensCode (id : Fin N → Fin N)) + KE (lensCode (id : Fin N → Fin N))
      ≤ (κ + κ) * N + (C + C) := by
    have hsum := Nat.add_le_add hb hb
    have hassoc : κ * N + C + (κ * N + C) = (κ + κ) * N + (C + C) := by ring
    omega
  calc 2 ^ (KE (lensCode (id : Fin N → Fin N)) + KE (lensCode (id : Fin N → Fin N)) + 0 + 2)
      ≤ 2 ^ ((κ + κ) * N + (C + C + 2)) := by
        apply Nat.pow_le_pow_right (by norm_num)
        omega
    _ < N ! := hN

/-! ## The engine: the deductible is constant on the earlier frame's relabelling orbit
([Guests] §7 Theorem 7.13(i)): the fact the staged capacity's cap needs to bracket it, built from
`card_stageLaws`, `card_lawsConsistentWith` and `card_orbit_mul_prod_fiber` alone — no
orbit–stabilizer analogue at the SECOND carrier, since the deductible's own invariance under
relabelling the first carrier stands in its place. -/

/-- **The deductible is invariant under relabelling the earlier frame** ([Guests] §7, Theorem
7.13(i), first fact): precomposing a consistent embedding with `σ⁻¹` is a bijection between the
consistency class of `(ℓ, ℓ')` and that of `(ℓ ∘ σ⁻¹, ℓ')` — relabelling the earlier frame by a
permutation of its own domain moves which embedding realizes a given consistency class without
changing that class's SIZE. -/
theorem deductible_smul_invariant {n m k : ℕ} (ℓ : Fin n → Fin k) (ℓ' : Fin m → Fin k)
    (σ : Equiv.Perm (Fin n)) :
    Nat.card {μ : Fin n ↪ Fin m // ∀ q, ℓ' (μ q) = (ℓ ∘ ⇑σ⁻¹) q}
      = Nat.card {μ : Fin n ↪ Fin m // ∀ q, ℓ' (μ q) = ℓ q} := by
  apply Nat.card_congr
  exact
    { toFun := fun ν => ⟨σ.toEmbedding.trans ν.1, fun q => by
        have h := ν.2 (σ q)
        simpa using h⟩
      invFun := fun μ => ⟨σ⁻¹.toEmbedding.trans μ.1, fun q => by
        have h := μ.2 (σ⁻¹ q)
        simpa using h⟩
      left_inv := fun ν => by
        apply Subtype.ext
        apply Function.Embedding.ext
        intro x
        simp [Function.Embedding.trans_apply]
      right_inv := fun μ => by
        apply Subtype.ext
        apply Function.Embedding.ext
        intro x
        simp [Function.Embedding.trans_apply] }

/-- **The deductibles sum to the population** ([Guests] §7, Theorem 7.13(i), second fact): a
candidate `μ` determines exactly one earlier frame `ℓ' ∘ μ` for a FIXED later frame `ℓ'`, so
`card_stageLaws`'s falling-factorial count decomposes, fibre by fibre over `ℓ'`'s target `Fin n →
Fin k`, into the deductibles of every possible earlier frame. -/
theorem sum_deductible_eq_card_stageLaws {n m k : ℕ} (ℓ' : Fin m → Fin k) :
    ∑ ℓ : Fin n → Fin k, Nat.card {μ : Fin n ↪ Fin m // ∀ q, ℓ' (μ q) = ℓ q}
      = m.descFactorial n := by
  classical
  rw [← card_stageLaws n m]
  have h1 := Nat.card_congr (Equiv.sigmaFiberEquiv (fun μ : Fin n ↪ Fin m => (fun q => ℓ' (μ q))))
  rw [Nat.card_sigma] at h1
  rw [← h1]
  exact Finset.sum_congr rfl fun ℓ _ =>
    Nat.card_congr (Equiv.subtypeEquivRight fun _ => funext_iff.symm)

/-- **The engine** ([Guests] §7, Theorem 7.13(i)): a frame `ℓ`'s relabelling class times its
deductible against any later frame `ℓ'` never exceeds the candidate population — the elementary fact
the staged capacity's cap rests on, needing neither an inverse nor an orbit–stabilizer count at the
second carrier. The orbit's members are distinct earlier frames all carrying `ℓ`'s own deductible
value (`deductible_smul_invariant`), and they are summands of `sum_deductible_eq_card_stageLaws`'s
total. -/
theorem orbit_mul_deductible_le {n m k : ℕ} (ℓ : Fin n → Fin k) (ℓ' : Fin m → Fin k) :
    Nat.card ↥(orbit (Equiv.Perm (Fin n)) ℓ)
        * Nat.card {μ : Fin n ↪ Fin m // ∀ q, ℓ' (μ q) = ℓ q}
      ≤ m.descFactorial n := by
  classical
  set D := Nat.card {μ : Fin n ↪ Fin m // ∀ q, ℓ' (μ q) = ℓ q} with hD
  have hfin : (orbit (Equiv.Perm (Fin n)) ℓ).Finite := Set.toFinite _
  have hconst : ∀ ℓ₁ ∈ hfin.toFinset,
      Nat.card {μ : Fin n ↪ Fin m // ∀ q, ℓ' (μ q) = ℓ₁ q} = D := by
    intro ℓ₁ hℓ₁
    rw [Set.Finite.mem_toFinset] at hℓ₁
    obtain ⟨σ, hσ⟩ := MulAction.mem_orbit_iff.mp hℓ₁
    have hσ' : ℓ₁ = ℓ ∘ ⇑σ⁻¹ := by
      rw [← hσ]
      funext x
      exact smul_lens_apply' σ ℓ x
    rw [hσ', hD]
    exact deductible_smul_invariant ℓ ℓ' σ
  have hstep : Nat.card ↥(orbit (Equiv.Perm (Fin n)) ℓ) * D
      = ∑ ℓ₁ ∈ hfin.toFinset, Nat.card {μ : Fin n ↪ Fin m // ∀ q, ℓ' (μ q) = ℓ₁ q} := by
    rw [Finset.sum_congr rfl hconst, Finset.sum_const, smul_eq_mul,
      Nat.card_coe_set_eq, Set.ncard_eq_toFinset_card _ hfin]
  rw [hstep, ← sum_deductible_eq_card_stageLaws (n := n) ℓ']
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => Nat.zero_le _)

/-! ## The staged carried entropy, and its cap ([Guests] §7 Definition 7.12, Theorem 7.13(ii))

The staged capacity is stated at its full, unbounded-label-count generality, matching Definition
7.12's own "a frame pair `(ℓ, ℓ')`" verbatim. Its cap, `CbHs_collapse` below, is proved — like
`collapse_union_staged` itself — at a FIXED label count `k` rather than by a union over every `k`:
`kraft_lensCode`'s Kraft step is injective only at a fixed codomain, and recovering it across
varying codomains needs surjectivity (`PersistenceCapacity.collapse_union`'s own route), which
neither `StagedBudgetedEntropies` nor its cap assumes. This is the same modelling choice
`collapse_union_staged`'s own docstring already makes for Theorem 7.11(v); `CbHs_collapse_growing`
below inherits it in the same shape `collapse_union_growing` inherits `collapse_union_staged`'s. -/

/-- **The staged carried entropies affordable at budget `b`** ([Guests] §7, Definition 7.12): the
relabelling-class sizes `N = Nat.card (orbit ℓ)` of the earlier frames of pairs `(ℓ, ℓ')` consistent
with `μ`, each costing at most `b` bits. The label count `k` is not fixed, matching Definition
7.12's own "a frame pair `(ℓ, ℓ')`" — a maximum over pairs at every label count, not one chosen in
advance. -/
def StagedBudgetedEntropies {n m : ℕ} (μ : Fin n ↪ Fin m) (b : ℕ) : Set ℕ :=
  {N : ℕ | ∃ k : ℕ, ∃ ℓ : Fin n → Fin k, ∃ ℓ' : Fin m → Fin k,
      (∀ q, ℓ' (μ q) = ℓ q) ∧ KE (lensCode ℓ) ≤ b ∧ KE (lensCode ℓ') ≤ b ∧
      N = Nat.card ↥(orbit (Equiv.Perm (Fin n)) ℓ)}

/-- **The staged capacity** ([Guests] §7, Definition 7.12): `C_b^{H,t}(μ)` in cardinality form —
the largest carried entropy, as the relabelling-class size `2 ^ E`, of a frame pair consistent with
`μ` whose two frames cost at most `b` bits each. `sSup ∅ = 0`: a budget affording no such pair
carries nothing. -/
noncomputable def CbHs {n m : ℕ} (μ : Fin n ↪ Fin m) (b : ℕ) : ℕ :=
  sSup (StagedBudgetedEntropies μ b)

/-- No pair distinguishes more than the earlier carrier has to offer: a relabelling class is a set
of lenses reachable from one another by permutations of `Fin n`, so its size is at most `n !`
(`card_orbit_mul_prod_fiber`, the fibre product being at least one) — regardless of the label count
`k`, which is what makes the supremum over all `k` well-defined. -/
private theorem stagedBudgetedEntropies_le {n m : ℕ} {μ : Fin n ↪ Fin m} {b N : ℕ}
    (h : N ∈ StagedBudgetedEntropies μ b) : N ≤ n ! := by
  obtain ⟨k, ℓ, -, -, -, -, rfl⟩ := h
  have hprod : 0 < ∏ i : Fin k, (Nat.card {x : Fin n // ℓ x = i})! :=
    Finset.prod_pos fun i _ => Nat.factorial_pos _
  exact card_orbit_mul_prod_fiber ℓ ▸ Nat.le_mul_of_pos_right _ hprod

private theorem bddAbove_stagedBudgetedEntropies {n m : ℕ} (μ : Fin n ↪ Fin m) (b : ℕ) :
    BddAbove (StagedBudgetedEntropies μ b) :=
  ⟨n !, fun _ h => stagedBudgetedEntropies_le h⟩

/-- **The staged capacity's cap, at a fixed label count** ([Guests] §7, Theorem 7.13(ii);
`collapse_union_staged` folded with the two frames' budgets, exactly as `CbH_collapse` folds
`PermBudget`'s two frame costs into `PersistenceCapacity.collapse_union`): outside a `2 ^ (-d)`
fraction of the candidates, every consistent pair `(ℓ, ℓ')` at label count `k` costing at most `b`
bits each has `Nat.card (orbit ℓ) ≤ 2 ^ (2 * b + d + 2)` — the deduction is one line from
`orbit_mul_deductible_le`: the deductible is non-zero because `μ` is itself consistent with the
pair, so `2 ^ (K(ℓ) + K(ℓ') + d + 2) · deductible ≥ POP ≥ Nat.card (orbit ℓ) · deductible` forces
the cap whenever `μ` clears `collapse_union_staged`'s own threshold. -/
theorem CbHs_collapse {n m : ℕ} (k b d : ℕ) :
    {μ : Fin n ↪ Fin m | ∃ ℓ : Fin n → Fin k, ∃ ℓ' : Fin m → Fin k,
        (∀ q, ℓ' (μ q) = ℓ q) ∧ KE (lensCode ℓ) ≤ b ∧ KE (lensCode ℓ') ≤ b ∧
        2 ^ (2 * b + d + 2) < Nat.card ↥(orbit (Equiv.Perm (Fin n)) ℓ)}.ncard * 2 ^ d
      ≤ m.descFactorial n := by
  refine le_trans (Nat.mul_le_mul_right _ (Set.ncard_le_ncard ?_ (Set.toFinite _)))
    (collapse_union_staged (n := n) (m := m) (k := k) d)
  rintro μ ⟨ℓ, ℓ', hcons, hbℓ, hbℓ', hlt⟩
  refine ⟨ℓ, ℓ', hcons, ?_⟩
  have : Nonempty {μ' : Fin n ↪ Fin m // ∀ q, ℓ' (μ' q) = ℓ q} := ⟨⟨μ, hcons⟩⟩
  have hded : 0 < Nat.card {μ' : Fin n ↪ Fin m // ∀ q, ℓ' (μ' q) = ℓ q} := Nat.card_pos
  calc 2 ^ (KE (lensCode ℓ) + KE (lensCode ℓ') + d + 2)
        * Nat.card {μ' : Fin n ↪ Fin m // ∀ q, ℓ' (μ' q) = ℓ q}
      ≤ 2 ^ (2 * b + d + 2) * Nat.card {μ' : Fin n ↪ Fin m // ∀ q, ℓ' (μ' q) = ℓ q} :=
        Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) (by omega))
    _ < Nat.card ↥(orbit (Equiv.Perm (Fin n)) ℓ)
        * Nat.card {μ' : Fin n ↪ Fin m // ∀ q, ℓ' (μ' q) = ℓ q} :=
        mul_lt_mul_of_pos_right hlt hded
    _ ≤ m.descFactorial n := orbit_mul_deductible_le ℓ ℓ'

/-! ## The bridge: a particular growing world's stage law, transported -/

/-- **The stage law, transported** ([Guests] §7, Definition 7.1 for `Advances`, Definition 7.6 for
`mergeStage`): a growing world's own stage-to-stage law — `GrowingCore.mergeLaw` restricted from the
stage-`t` retained profile to the stage-`(t + 1)` one, `MapsTo` from `advances_mergeStage` and
`InjOn` from `mergeStage_injOn` — transported along a CHOSEN enumeration of the two profiles
(`Set.Finite.toFinset`, via `hf`/`hf'`) into the embedding numeral `collapse_union_growing` below
prices. The object depends on that enumeration: a different choice gives a different embedding,
though the same numerals `hf.toFinset.card`/`hf'.toFinset.card` — the same enumeration-relativity
`[Persistence]` §2.1's encoding convention already carries and `[Persistence]` §5's `C_b` is stated
against. -/
noncomputable def stageLawEmb {X : Type*} {U : X → X} {Ω : ℕ → Set X} (hadv : Advances U Ω) (t : ℕ)
    (hf : (mergeStage U Ω t).Finite) (hf' : (mergeStage U Ω (t + 1)).Finite) :
    Fin hf.toFinset.card ↪ Fin hf'.toFinset.card := by
  haveI := hf.fintype
  haveI := hf'.fintype
  set e1 : ↥(mergeStage U Ω t) ≃ Fin hf.toFinset.card :=
    (Fintype.equivFin _).trans
      (finCongr ((Nat.card_eq_fintype_card (α := ↥(mergeStage U Ω t))).symm.trans
        (Nat.card_eq_card_finite_toFinset hf))) with he1
  set e2 : ↥(mergeStage U Ω (t + 1)) ≃ Fin hf'.toFinset.card :=
    (Fintype.equivFin _).trans
      (finCongr ((Nat.card_eq_fintype_card (α := ↥(mergeStage U Ω (t + 1)))).symm.trans
        (Nat.card_eq_card_finite_toFinset hf'))) with he2
  set emb : ↥(mergeStage U Ω t) ↪ ↥(mergeStage U Ω (t + 1)) :=
    ⟨fun x => ⟨mergeLaw U x.1, advances_mergeStage hadv t x.1 x.2⟩,
     fun x y hxy => Subtype.ext (mergeStage_injOn U Ω t x.2 y.2 (congrArg Subtype.val hxy))⟩
    with hemb
  exact e1.symm.toEmbedding.trans (emb.trans e2.toEmbedding)

/-- **The collapse, at a growing world** ([Persistence] §7 Corollary 7.4 for the bound instantiated,
[Guests] §7 for the objects it is instantiated at): `collapse_union_staged` read at `stageLawEmb`'s
own domain and codomain sizes, together with the fact — new content `hadv` buys, since
`collapse_union_staged` alone is silent on it — that the growing world's own stage-to-stage law is
one genuine inhabitant of `Fin hf.toFinset.card ↪ Fin hf'.toFinset.card`, the population the bound
prices; without `hadv` that population could be empty (`hf.toFinset.card > hf'.toFinset.card`), and
the bound would hold of nothing. This is what makes the conclusion a statement about `(U, Ω)` at
stage `t`, relative to the same chosen enumeration `stageLawEmb`'s docstring names: it prices the
stage-to-stage law of the presented growing world `(X, U, Ω)`, and it is silent about `U`'s law on
states outside the two retained profiles `mergeStage U Ω t`/`mergeStage U Ω (t + 1)` name. -/
theorem collapse_union_growing {X : Type*} {U : X → X} {Ω : ℕ → Set X} (hadv : Advances U Ω)
    (t d : ℕ) (hf : (mergeStage U Ω t).Finite) (hf' : (mergeStage U Ω (t + 1)).Finite) {k : ℕ} :
    Nonempty (Fin hf.toFinset.card ↪ Fin hf'.toFinset.card) ∧
    {μ : Fin hf.toFinset.card ↪ Fin hf'.toFinset.card | ∃ (ℓ : Fin hf.toFinset.card → Fin k)
       (ℓ' : Fin hf'.toFinset.card → Fin k),
       (∀ q, ℓ' (μ q) = ℓ q) ∧
       2 ^ (KE (lensCode ℓ) + KE (lensCode ℓ') + d + 2)
         * Nat.card {μ' : Fin hf.toFinset.card ↪ Fin hf'.toFinset.card // ∀ q, ℓ' (μ' q) = ℓ q}
         < hf'.toFinset.card.descFactorial hf.toFinset.card}.ncard * 2 ^ d
      ≤ hf'.toFinset.card.descFactorial hf.toFinset.card :=
  ⟨⟨stageLawEmb hadv t hf hf'⟩, collapse_union_staged d⟩

/-! ## The floor, and the two recoveries ([Guests] §7 Theorem 7.13(iii)–(iv))

`markingLens`'s transport is FORWARD along an embedding — no permutation, no inverse — which is why
the floor holds uniformly in the stage law rather than needing the law to be a member of any
group. -/

/-- A marked point is read as its own label, restated because `PersistenceCapacity.markingLens_mark`
is file-private. -/
private theorem markingLens_mark' {r n : ℕ} {x : Fin r → Fin n} (hx : Function.Injective x)
    (j : Fin r) : markingLens x (x j) = j.succ := by
  have h : ∃ j', x j' = x j := ⟨j, rfl⟩
  rw [markingLens, dite_eq_left h]
  exact congrArg Fin.succ (hx h.choose_spec)

/-- An unmarked point is read as `0`, restated because `PersistenceCapacity.markingLens_unmark` is
file-private. -/
private theorem markingLens_unmark' {r n : ℕ} {x : Fin r → Fin n} {i : Fin n}
    (h : ¬∃ j, x j = i) : markingLens x i = 0 := by
  rw [markingLens, dite_eq_right h]

/-- **The marks transport forward along an embedding** ([Guests] §7, Theorem 7.13(iii), the
transport step): a marked point's image carries its label, and an unmarked point's image is
unmarked because `μ` separates it from every mark — the stage's `m − n` new classes all reading the
default label, which is what every marking lens gives its unmarked points. -/
theorem markingLens_comp_embedding {n m r : ℕ} (μ : Fin n ↪ Fin m) {x : Fin r → Fin n}
    (hx : Function.Injective x) (q : Fin n) :
    markingLens (n := m) (⇑μ ∘ x) (μ q) = markingLens (n := n) x q := by
  have hμx : Function.Injective (⇑μ ∘ x) := μ.injective.comp hx
  by_cases hex : ∃ j, x j = q
  · obtain ⟨j, hj⟩ := hex
    subst hj
    have heq : (⇑μ ∘ x) j = μ (x j) := rfl
    rw [markingLens_mark' hx j, ← heq, markingLens_mark' hμx j]
  · rw [markingLens_unmark' hex, markingLens_unmark']
    rintro ⟨j, hj⟩
    exact hex ⟨j, μ.injective hj⟩

/-- **The floor, uniform in the stage law** ([Guests] §7, Theorem 7.13(iii)): over every candidate
`μ`, and with no hypothesis on it beyond injectivity, the marking pair `(markingLens x, markingLens
(⇑μ ∘ x))` is consistent with `μ` (`markingLens_comp_embedding`) and carries entropy `log₂ (n ! / (n
− r)!)` as soon as the marking price is met on the LARGER carrier — `KE_markingLens_le` at `m`
already bounds the price at `n`, since `Nat.size n ≤ Nat.size m`. -/
theorem CbHs_ge_marking {n m r : ℕ} {μ : Fin n ↪ Fin m} {x : Fin r → Fin n}
    (hx : Function.Injective x) (hrn : r < n) (hrm : r < m) {b : ℕ}
    (hb : 6 * (15 + elen dbl) * ((r + 1) * Nat.size m)
        + (elen markBuilder + 7 * (15 + elen dbl) + 3) ≤ b) :
    n ! ≤ CbHs μ b * (n - r)! := by
  have hμx : Function.Injective (⇑μ ∘ x) := μ.injective.comp hx
  have hnm : n ≤ m := by
    have h := Fintype.card_le_of_injective (⇑μ) μ.injective
    simpa using h
  have hsize : Nat.size n ≤ Nat.size m := Nat.size_le_size hnm
  have hbn : KE (lensCode (markingLens x)) ≤ b := by
    have h1 := KE_markingLens_le hrn hx
    have h2 : 6 * (15 + elen dbl) * ((r + 1) * Nat.size n)
        ≤ 6 * (15 + elen dbl) * ((r + 1) * Nat.size m) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hsize)
    omega
  have hbm : KE (lensCode (markingLens (⇑μ ∘ x))) ≤ b := by
    have h1 := KE_markingLens_le (n := m) hrm hμx
    omega
  have hmem :
      Nat.card ↥(orbit (Equiv.Perm (Fin n)) (markingLens x)) ∈ StagedBudgetedEntropies μ b :=
    ⟨r + 1, markingLens x, markingLens (⇑μ ∘ x), fun q => markingLens_comp_embedding μ hx q,
      hbn, hbm, rfl⟩
  have hle : Nat.card ↥(orbit (Equiv.Perm (Fin n)) (markingLens x)) ≤ CbHs μ b :=
    le_csSup (bddAbove_stagedBudgetedEntropies μ b) hmem
  calc n ! = Nat.card ↥(orbit (Equiv.Perm (Fin n)) (markingLens x))
        * ∏ l : Fin (r + 1), (Nat.card {i : Fin n // markingLens x i = l})! :=
        (card_orbit_mul_prod_fiber (markingLens x)).symm
    _ = Nat.card ↥(orbit (Equiv.Perm (Fin n)) (markingLens x)) * (n - r)! := by
        rw [prod_fiber_marking hx]
    _ ≤ CbHs μ b * (n - r)! := Nat.mul_le_mul_right _ hle

/-- **The constant-stage recovery** ([Guests] §7, Theorem 7.13(iv)): at a permutation world's own
frame family, dropping `PermCarries`'s surjectivity requirement only enlarges the pairs available,
so the fixed-carrier capacity is bounded by the staged one at the world's own embedding. -/
theorem CbH_le_CbHs {n : ℕ} (U : Equiv.Perm (Fin n)) (b : ℕ) : CbH U b ≤ CbHs U.toEmbedding b :=
  csSup_le_csSup' (bddAbove_stagedBudgetedEntropies U.toEmbedding b) (by
    rintro N ⟨k, ℓ, hcar, hbud, rfl⟩
    refine ⟨k, ℓ 0, ℓ 1, fun q => ?_, hbud 0, hbud 1, rfl⟩
    have h := hcar.2 1 q
    simpa using h)

/-- **The staged cap and floor, at a growing world** ([Guests] §7 Theorem 7.13, read at a growing
world's own stage law, in `collapse_union_growing`'s own shape): `CbHs_collapse` at `stageLawEmb`'s
own domain and codomain sizes, together with the fact that the world's stage law is one genuine
inhabitant of the population it prices — the same pairing `collapse_union_growing` performs for
`collapse_union_staged`. -/
theorem CbHs_collapse_growing {X : Type*} {U : X → X} {Ω : ℕ → Set X} (hadv : Advances U Ω)
    (t k b d : ℕ) (hf : (mergeStage U Ω t).Finite) (hf' : (mergeStage U Ω (t + 1)).Finite) :
    Nonempty (Fin hf.toFinset.card ↪ Fin hf'.toFinset.card) ∧
    {μ : Fin hf.toFinset.card ↪ Fin hf'.toFinset.card |
       ∃ ℓ : Fin hf.toFinset.card → Fin k, ∃ ℓ' : Fin hf'.toFinset.card → Fin k,
       (∀ q, ℓ' (μ q) = ℓ q) ∧ KE (lensCode ℓ) ≤ b ∧ KE (lensCode ℓ') ≤ b ∧
       2 ^ (2 * b + d + 2) < Nat.card ↥(orbit (Equiv.Perm (Fin hf.toFinset.card)) ℓ)}.ncard * 2 ^ d
      ≤ hf'.toFinset.card.descFactorial hf.toFinset.card :=
  ⟨⟨stageLawEmb hadv t hf hf'⟩, CbHs_collapse k b d⟩

/-- **The floor is optimal in its own quantifier** ([Guests] §7, Theorem 7.13(vi)): fix a label
alphabet `k` and a budget `b`. Some candidate `μ` admits no consistent pair, affordable at `b` per
frame, whose earlier frame's relabelling class exceeds `2 ^ (2 * b + 3)` — so no family whatever,
the marking family of Theorem 7.13(iii) or any other, floors the staged capacity above that bound
UNIFORMLY in the stage law: a family that did would put every candidate in `CbHs_collapse`'s own
exceptional set at `d = 1`, making it the whole population, which `card_stageLaws` and `hnm` rule
out. This does NOT bound `CbHs` itself — false at the exceptional candidates — and it does NOT
identify the uniform optimum with `CbHs_ge_marking`'s floor: that floor bounds the capacity from
below, this bounds it from above, and the interval between them is left open here. The alphabet
`k` is a parameter here exactly as it is in `CbHs_collapse`, so this is a per-alphabet statement
like its source, and it has content exactly when `2 ^ (2 * b + 3) < n !`. -/
theorem exists_candidate_capacity_le {n m : ℕ} (hnm : n ≤ m) (k b : ℕ) :
    ∃ μ : Fin n ↪ Fin m, ∀ (ℓ : Fin n → Fin k) (ℓ' : Fin m → Fin k),
      (∀ q, ℓ' (μ q) = ℓ q) → KE (lensCode ℓ) ≤ b → KE (lensCode ℓ') ≤ b →
      Nat.card ↥(orbit (Equiv.Perm (Fin n)) ℓ) ≤ 2 ^ (2 * b + 3) := by
  by_contra hcon
  push Not at hcon
  have huniv : {μ : Fin n ↪ Fin m | ∃ ℓ : Fin n → Fin k, ∃ ℓ' : Fin m → Fin k,
      (∀ q, ℓ' (μ q) = ℓ q) ∧ KE (lensCode ℓ) ≤ b ∧ KE (lensCode ℓ') ≤ b ∧
      2 ^ (2 * b + 1 + 2) < Nat.card ↥(orbit (Equiv.Perm (Fin n)) ℓ)} = Set.univ :=
    Set.eq_univ_of_forall hcon
  have hcollapse := CbHs_collapse (n := n) (m := m) k b 1
  rw [huniv, Set.ncard_univ, card_stageLaws] at hcollapse
  have hpos : 0 < m.descFactorial n := Nat.descFactorial_pos.mpr hnm
  omega

/-! ## The alphabet-uniform cap ([Guests] §7 Theorem 7.13, extended; §9.2's alphabet paragraph)

`CbHs_collapse`'s cap holds at each label alphabet `k` separately: the union behind it
(`collapse_union_staged`) runs `kraft_lensCode`'s Kraft step over frames valued in the SAME `Fin
k`, which is injective only at a fixed codomain, and nothing in `StagedBudgetedEntropies` bounds
the alphabet by `n` or `m`. §9.2 names the gap directly: "no statement here caps the capacity
uniformly over alphabets."

The route below does not repair the per-alphabet Kraft step; it replaces it. Every frame pair
`(ℓ, ℓ')`, at ANY label count `k`, normalizes to one pair at the FIXED alphabet `Fin m` — rank each
label by its first-occurrence position in `ℓ'`'s own table (`rankOf`). `lensTable` mentions no
codomain, so the normalized pair lands at `Fin m` whatever `k` was, and the per-alphabet union that
priced `collapse_union_staged` over frame CODES is replaced by a count over normalized-PAIR codes
(`card_KE_le`) — one fixed alphabet, no Kraft sum, no union over label counts at all. -/

/-! ### The rank map: normalizing a frame pair to the later carrier's own alphabet -/

private theorem lensTable_length {n m : ℕ} (ℓ : Fin n → Fin m) : (lensTable ℓ).length = n := by
  simp [lensTable]

private theorem mem_lensTable_apply {n m : ℕ} (ℓ : Fin n → Fin m) (q : Fin n) :
    ((ℓ q : Fin m) : ℕ) ∈ lensTable ℓ := by
  simp only [lensTable]
  exact List.mem_map_of_mem (List.mem_finRange q)

/-- **The rank map** ([Guests] §7, the alphabet-uniform round, Finding 1): the first-occurrence
position of a label in the LATER frame's own table, landing at the fixed carrier `Fin m` whatever
label count the input came from — `lensTable` mentions no codomain, which is why no union over
alphabets is needed below. -/
private def rankOf {m k : ℕ} (ℓ' : Fin m → Fin k) (hm : 0 < m) : Fin k → Fin m := fun v =>
  if h : List.idxOf (v : ℕ) (lensTable ℓ') < m then ⟨List.idxOf (v : ℕ) (lensTable ℓ'), h⟩
  else ⟨0, hm⟩

private theorem rankOf_eq_idxOf {m k : ℕ} {ℓ' : Fin m → Fin k} {hm : 0 < m} {v : Fin k}
    (h : (v : ℕ) ∈ lensTable ℓ') :
    ((rankOf ℓ' hm v : Fin m) : ℕ) = List.idxOf (v : ℕ) (lensTable ℓ') := by
  have hlt : List.idxOf (v : ℕ) (lensTable ℓ') < m :=
    (List.idxOf_lt_length_of_mem h).trans_eq (lensTable_length ℓ')
  simp only [rankOf, dite_eq_left hlt]

/-- **The rank map is injective on the labels its own frame table carries** ([Guests] §7, Finding
1: "distinct present values have distinct first-occurrence indices"): two present labels agreeing
on their `rankOf` image share the SAME table position (`List.getElem_idxOf`), hence the same
value. -/
private theorem rankOf_injOn_mem {m k : ℕ} (ℓ' : Fin m → Fin k) (hm : 0 < m) :
    Set.InjOn (rankOf ℓ' hm) {v : Fin k | (v : ℕ) ∈ lensTable ℓ'} := by
  intro v1 hv1 v2 hv2 heq
  have e1 : ((rankOf ℓ' hm v1 : Fin m) : ℕ) = List.idxOf (v1 : ℕ) (lensTable ℓ') :=
    rankOf_eq_idxOf hv1
  have e2 : ((rankOf ℓ' hm v2 : Fin m) : ℕ) = List.idxOf (v2 : ℕ) (lensTable ℓ') :=
    rankOf_eq_idxOf hv2
  have hidx : List.idxOf (v1 : ℕ) (lensTable ℓ') = List.idxOf (v2 : ℕ) (lensTable ℓ') := by
    rw [← e1, ← e2, heq]
  have hltL1 : List.idxOf (v1 : ℕ) (lensTable ℓ') < (lensTable ℓ').length :=
    List.idxOf_lt_length_of_mem hv1
  have hltL2 : List.idxOf (v2 : ℕ) (lensTable ℓ') < (lensTable ℓ').length :=
    List.idxOf_lt_length_of_mem hv2
  have hg1 := List.getElem_idxOf hltL1
  have hg2 := List.getElem_idxOf hltL2
  have hv12 : (v1 : ℕ) = (v2 : ℕ) := by
    simp only [hidx] at hg1
    exact hg1.symm.trans hg2
  exact Fin.val_injective hv12

/-- Rank the later frame's own table: needs no hypothesis on `ℓ'`, its own values are trivially
present in it. -/
private theorem lensTable_rankOf_comp_right {m k : ℕ} (ℓ' : Fin m → Fin k) (hm : 0 < m) :
    lensTable (rankOf ℓ' hm ∘ ℓ') = (lensTable ℓ').map fun v => List.idxOf v (lensTable ℓ') := by
  simp only [lensTable, Function.comp_apply, List.map_map]
  exact List.map_congr_left fun q _ => rankOf_eq_idxOf (mem_lensTable_apply ℓ' q)

/-- Rank the earlier frame's table: needs consistency, which puts every value of `ℓ` inside `ℓ'`'s
own table (`ℓ q = ℓ' (μ q)`). -/
private theorem lensTable_rankOf_comp_left {n m k : ℕ} {ℓ : Fin n → Fin k} {ℓ' : Fin m → Fin k}
    {μ : Fin n ↪ Fin m} (hcons : ∀ q, ℓ' (μ q) = ℓ q) (hm : 0 < m) :
    lensTable (rankOf ℓ' hm ∘ ℓ) = (lensTable ℓ).map fun v => List.idxOf v (lensTable ℓ') := by
  simp only [lensTable, Function.comp_apply, List.map_map]
  refine List.map_congr_left fun q _ => ?_
  have hmem : ((ℓ q : Fin k) : ℕ) ∈ lensTable ℓ' := hcons q ▸ mem_lensTable_apply ℓ' (μ q)
  exact rankOf_eq_idxOf hmem

/-- **The normalized pair stays consistent with the same candidate** ([Guests] §7, Finding 1): one
line, `ρ` applied to both sides of the original consistency equation. -/
private theorem rankOf_consistent {n m k : ℕ} {ℓ : Fin n → Fin k} {ℓ' : Fin m → Fin k}
    {μ : Fin n ↪ Fin m} (hcons : ∀ q, ℓ' (μ q) = ℓ q) (hm : 0 < m) :
    ∀ q, (rankOf ℓ' hm ∘ ℓ') (μ q) = (rankOf ℓ' hm ∘ ℓ) q :=
  fun q => congrArg (rankOf ℓ' hm) (hcons q)

/-! ### Orbit preservation under an injective-on-range post-composition -/

private theorem range_orbit_eq {n : ℕ} {β : Type*} (ℓ : Fin n → β) {ℓ₁ : Fin n → β}
    (h : ℓ₁ ∈ orbit (Equiv.Perm (Fin n)) ℓ) : Set.range ℓ₁ = Set.range ℓ := by
  obtain ⟨σ, hσ⟩ := MulAction.mem_orbit_iff.mp h
  have hℓ₁ : ℓ₁ = ℓ ∘ ⇑σ⁻¹ := by rw [← hσ]; funext x; exact smul_lens_apply' σ ℓ x
  rw [hℓ₁]
  exact EquivLike.range_comp ℓ σ⁻¹

private theorem orbit_postcomp_eq_image {n : ℕ} {β γ : Type*} (ρ : β → γ) (ℓ : Fin n → β) :
    orbit (Equiv.Perm (Fin n)) (ρ ∘ ℓ)
      = (fun ℓ₁ : Fin n → β => ρ ∘ ℓ₁) '' orbit (Equiv.Perm (Fin n)) ℓ := by
  ext f
  simp only [Set.mem_image]
  constructor
  · intro hf
    obtain ⟨σ, hσ⟩ := MulAction.mem_orbit_iff.mp hf
    refine ⟨σ • ℓ, ⟨σ, rfl⟩, ?_⟩
    rw [← hσ]
    funext x
    simp only [Function.comp_apply, smul_lens_apply']
  · rintro ⟨ℓ₁, hℓ₁, rfl⟩
    obtain ⟨σ, hσ⟩ := MulAction.mem_orbit_iff.mp hℓ₁
    refine ⟨σ, ?_⟩
    funext x
    simp only [Function.comp_apply, smul_lens_apply', ← hσ]

/-- **Orbit preservation under an injective-on-range post-composition** ([Guests] §7, the
alphabet-uniform round): composing a frame with any map injective on the frame's own values changes
no relabelling class's SIZE — a self-standing fact about any post-composition, with no reference to
`rankOf` at all. -/
theorem orbit_postcomp_card_eq {n : ℕ} {β γ : Type*} (ρ : β → γ) (ℓ : Fin n → β)
    (hρ : Set.InjOn ρ (Set.range ℓ)) :
    Nat.card ↥(orbit (Equiv.Perm (Fin n)) (ρ ∘ ℓ)) = Nat.card ↥(orbit (Equiv.Perm (Fin n)) ℓ) := by
  have hinj : Set.InjOn (fun ℓ₁ : Fin n → β => ρ ∘ ℓ₁) (orbit (Equiv.Perm (Fin n)) ℓ) := by
    intro ℓ₁ h₁ ℓ₂ h₂ heq
    have hr1 := range_orbit_eq ℓ h₁
    have hr2 := range_orbit_eq ℓ h₂
    funext x
    exact hρ (hr1 ▸ ⟨x, rfl⟩) (hr2 ▸ ⟨x, rfl⟩) (congrFun heq x)
  rw [orbit_postcomp_eq_image]
  simp only [Nat.card_coe_set_eq]
  exact Set.InjOn.ncard_image hinj

/-! ### The rank builder: the normalization as a single fixed program -/

/-- The rank the price table transports. -/
def rankFun (p : ℕ) : ℕ :=
  Nat.pair
    (Encodable.encode
      (((Encodable.decode (α := List ℕ) p.unpair.1).getD []).map fun v =>
        List.idxOf v ((Encodable.decode (α := List ℕ) p.unpair.2).getD [])))
    (Encodable.encode
      (((Encodable.decode (α := List ℕ) p.unpair.2).getD []).map fun v =>
        List.idxOf v ((Encodable.decode (α := List ℕ) p.unpair.2).getD [])))

private theorem primrec_rankFun : Primrec rankFun := by
  have hdec1 : Primrec fun p : ℕ => (Encodable.decode (α := List ℕ) p.unpair.1).getD [] :=
    Primrec.option_getD.comp (Primrec.decode.comp (Primrec.fst.comp Primrec.unpair))
      (Primrec.const [])
  have hdec2 : Primrec fun p : ℕ => (Encodable.decode (α := List ℕ) p.unpair.2).getD [] :=
    Primrec.option_getD.comp (Primrec.decode.comp (Primrec.snd.comp Primrec.unpair))
      (Primrec.const [])
  have hg : Primrec fun q : ℕ × ℕ =>
      List.idxOf q.2 ((Encodable.decode (α := List ℕ) q.1.unpair.2).getD []) :=
    Primrec.list_idxOf.comp Primrec.snd (hdec2.comp Primrec.fst)
  have hmap1 : Primrec fun p : ℕ =>
      (((Encodable.decode (α := List ℕ) p.unpair.1).getD []).map fun v =>
        List.idxOf v ((Encodable.decode (α := List ℕ) p.unpair.2).getD [])) :=
    Primrec.list_map hdec1 hg
  have hmap2 : Primrec fun p : ℕ =>
      (((Encodable.decode (α := List ℕ) p.unpair.2).getD []).map fun v =>
        List.idxOf v ((Encodable.decode (α := List ℕ) p.unpair.2).getD [])) :=
    Primrec.list_map hdec2 hg
  exact Primrec₂.natPair.comp (Primrec.encode.comp hmap1) (Primrec.encode.comp hmap2)

/-- `rankFun` is partial recursive. -/
theorem partrec_rankFun : Nat.Partrec rankFun :=
  _root_.Partrec.nat_iff.mp primrec_rankFun.to_comp.partrec

/-- **The fixed rank-normalization program** ([Guests] §7, the alphabet-uniform round): extracted
from universality (`Nat.Partrec.Code.exists_code`), independent of `n`, `m`, `k`, and every frame —
one program whose `elen` is the fixed constant `CbHs_collapse_uniform`'s exponent carries, exactly
as `BinaryConstant.dbl`'s `elen` is a fixed uncontrolled constant. -/
noncomputable def rankBuilder : Nat.Partrec.Code :=
  Classical.choose (Nat.Partrec.Code.exists_code.mp partrec_rankFun)

private theorem eval_rankBuilder (p : ℕ) :
    Nat.Partrec.Code.eval rankBuilder p = Part.some (rankFun p) := by
  have h := congrFun (Classical.choose_spec (Nat.Partrec.Code.exists_code.mp partrec_rankFun)) p
  simpa [rankBuilder] using h

/-- **The rank builder's frame-level law** ([Guests] §7, Finding 3): on the joint code of a
consistent pair, `rankBuilder` computes the joint code of the RANKED pair — `rankFun`'s two
`List.idxOf` maps are, by `lensTable_rankOf_comp_left`/`_right`, exactly `lensTable` of `rankOf ℓ'
hm ∘ ℓ` and of `rankOf ℓ' hm ∘ ℓ'`. -/
private theorem eval_rankBuilder_pair {n m k : ℕ} {ℓ : Fin n → Fin k} {ℓ' : Fin m → Fin k}
    {μ : Fin n ↪ Fin m} (hcons : ∀ q, ℓ' (μ q) = ℓ q) (hm : 0 < m) :
    Nat.Partrec.Code.eval rankBuilder (Nat.pair (lensCode ℓ) (lensCode ℓ'))
      = Part.some (Nat.pair (lensCode (rankOf ℓ' hm ∘ ℓ)) (lensCode (rankOf ℓ' hm ∘ ℓ'))) := by
  rw [eval_rankBuilder]
  simp only [rankFun, lensCode, Nat.unpair_pair, Encodable.encodek, Option.getD_some]
  rw [← lensTable_rankOf_comp_left hcons hm, ← lensTable_rankOf_comp_right ℓ' hm]

/-- **The price, in the composition shape** ([Guests] §7, Finding 2): `minCode` of the input joint
code, composed with the fixed rank builder. `invariance_general`'s LOADED-value route is barred by
the standing trap — it would pay `Nat.size` of the encoded tables themselves; this pays only the
builder's own fixed length plus the input pair's `KE`. -/
private theorem KE_rankBuilder_pair_le {n m k : ℕ} {ℓ : Fin n → Fin k} {ℓ' : Fin m → Fin k}
    {μ : Fin n ↪ Fin m} (hcons : ∀ q, ℓ' (μ q) = ℓ q) (hm : 0 < m) :
    KE (Nat.pair (lensCode (rankOf ℓ' hm ∘ ℓ)) (lensCode (rankOf ℓ' hm ∘ ℓ')))
      ≤ KE (lensCode ℓ) + KE (lensCode ℓ') + elen rankBuilder + 6 := by
  set z := Nat.pair (lensCode ℓ) (lensCode ℓ') with hz
  have hd : Nat.Partrec.Code.eval (minCode z) 0 = Part.some z := (exists_min_E z).choose_spec.1
  have hcomp : KolmogorovComplexity.Computes (Nat.Partrec.Code.comp rankBuilder (minCode z))
      (Nat.pair (lensCode (rankOf ℓ' hm ∘ ℓ)) (lensCode (rankOf ℓ' hm ∘ ℓ'))) := by
    change Nat.Partrec.Code.eval (Nat.Partrec.Code.comp rankBuilder (minCode z)) 0 = _
    rw [CodeEvalLaws.eval_comp_some hd, hz]
    exact eval_rankBuilder_pair hcons hm
  have hle := KE_comp_le hcomp
  have hsub : KE z ≤ KE (lensCode ℓ) + KE (lensCode ℓ') + 3 := KE_subadditive _ _
  rw [elen_minCode] at hle
  omega

/-! ### The count, and the capstone -/

private theorem exists_mem_stagedBudgetedEntropies_gt {n m : ℕ} {μ : Fin n ↪ Fin m} {b E : ℕ}
    (h : 2 ^ E < CbHs μ b) : ∃ N ∈ StagedBudgetedEntropies μ b, 2 ^ E < N := by
  rcases (StagedBudgetedEntropies μ b).eq_empty_or_nonempty with he | hne
  · exfalso
    have h0 : CbHs μ b = 0 := by
      change sSup (StagedBudgetedEntropies μ b) = 0
      simp [he, csSup_empty]
    rw [h0] at h
    exact Nat.not_lt_zero _ h
  · exact exists_lt_of_lt_csSup hne h

/-- **The Kraft-free union collapse, normalized-pair form** ([Guests] §7, the alphabet-uniform
round, Finding 4): the qualifying normalized pairs at the fixed alphabet `Fin m` number at most
`2 ^ (B + 1)` (their joint codes are distinct — `lensCode_injective'` at fixed sizes plus `Nat.pair`
injectivity — and bounded at cost `B`, so `card_KE_le` caps the index), and each contributes at
most `POP / 2 ^ (B + d + 2)` candidates to the union — a single fixed threshold rather than a
per-pair Kraft weight, so the whole bound is arithmetic in `ℕ` with no real-valued sum. -/
private theorem collapse_union_normalized {n m : ℕ} (B d : ℕ) :
    {μ : Fin n ↪ Fin m | ∃ (ℓR : Fin n → Fin m) (ℓR' : Fin m → Fin m),
        (∀ q, ℓR' (μ q) = ℓR q) ∧ KE (Nat.pair (lensCode ℓR) (lensCode ℓR')) ≤ B ∧
        2 ^ (B + d + 2) * Nat.card {μ' : Fin n ↪ Fin m // ∀ q, ℓR' (μ' q) = ℓR q}
          < m.descFactorial n}.ncard * 2 ^ d
      ≤ m.descFactorial n := by
  classical
  set POP := m.descFactorial n with hPOP
  set idx := Finset.univ.filter fun p : (Fin n → Fin m) × (Fin m → Fin m) =>
      KE (Nat.pair (lensCode p.1) (lensCode p.2)) ≤ B ∧
      2 ^ (B + d + 2) * Nat.card {μ' : Fin n ↪ Fin m // ∀ q, p.2 (μ' q) = p.1 q} < POP
    with hidxdef
  set T : (Fin n → Fin m) × (Fin m → Fin m) → Set (Fin n ↪ Fin m) :=
    fun p => {μ | ∀ q, p.2 (μ q) = p.1 q} with hTdef
  have hsub : {μ : Fin n ↪ Fin m | ∃ (ℓR : Fin n → Fin m) (ℓR' : Fin m → Fin m),
        (∀ q, ℓR' (μ q) = ℓR q) ∧ KE (Nat.pair (lensCode ℓR) (lensCode ℓR')) ≤ B ∧
        2 ^ (B + d + 2) * Nat.card {μ' : Fin n ↪ Fin m // ∀ q, ℓR' (μ' q) = ℓR q} < POP}
      = ⋃ p ∈ idx, T p := by
    ext μ
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, hTdef, hidxdef, Finset.mem_filter,
      Finset.mem_univ, true_and]
    constructor
    · rintro ⟨ℓR, ℓR', hcons, hB, hlt⟩
      exact ⟨(ℓR, ℓR'), ⟨hB, hlt⟩, hcons⟩
    · rintro ⟨⟨ℓR, ℓR'⟩, ⟨hB, hlt⟩, hcons⟩
      exact ⟨ℓR, ℓR', hcons, hB, hlt⟩
  have hidxsubcost : idx ⊆ Finset.univ.filter fun p : (Fin n → Fin m) × (Fin m → Fin m) =>
      KE (Nat.pair (lensCode p.1) (lensCode p.2)) ≤ B := by
    intro p hp
    rw [hidxdef, Finset.mem_filter] at hp
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ p, hp.2.1⟩
  have hcardcost : (Finset.univ.filter fun p : (Fin n → Fin m) × (Fin m → Fin m) =>
      KE (Nat.pair (lensCode p.1) (lensCode p.2)) ≤ B).card ≤ 2 ^ (B + 1) := by
    have hinj : Set.InjOn (fun p : (Fin n → Fin m) × (Fin m → Fin m) =>
        Nat.pair (lensCode p.1) (lensCode p.2))
        ↑(Finset.univ.filter fun p : (Fin n → Fin m) × (Fin m → Fin m) =>
          KE (Nat.pair (lensCode p.1) (lensCode p.2)) ≤ B) := by
      intro p _ q _ heq
      obtain ⟨h1, h2⟩ := Nat.pair_eq_pair.mp heq
      exact Prod.ext (lensCode_injective' h1) (lensCode_injective' h2)
    rw [← Finset.card_image_of_injOn hinj]
    have hsubset : (↑((Finset.univ.filter fun p : (Fin n → Fin m) × (Fin m → Fin m) =>
        KE (Nat.pair (lensCode p.1) (lensCode p.2)) ≤ B).image
        fun p => Nat.pair (lensCode p.1) (lensCode p.2)) : Set ℕ) ⊆ {z : ℕ | KE z ≤ B} := by
      intro z hz
      simp only [Finset.coe_image, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_image,
        Set.mem_ofPred_eq] at hz
      obtain ⟨p, hp, rfl⟩ := hz
      exact hp
    calc ((Finset.univ.filter fun p : (Fin n → Fin m) × (Fin m → Fin m) =>
        KE (Nat.pair (lensCode p.1) (lensCode p.2)) ≤ B).image
        fun p => Nat.pair (lensCode p.1) (lensCode p.2)).card
        = (↑((Finset.univ.filter fun p : (Fin n → Fin m) × (Fin m → Fin m) =>
            KE (Nat.pair (lensCode p.1) (lensCode p.2)) ≤ B).image
            fun p => Nat.pair (lensCode p.1) (lensCode p.2)) : Set ℕ).ncard :=
          (Set.ncard_coe_finset _).symm
      _ ≤ {z : ℕ | KE z ≤ B}.ncard := Set.ncard_le_ncard hsubset (finite_KE_le B)
      _ ≤ 2 ^ (B + 1) := card_KE_le B
  have hidxcard : idx.card ≤ 2 ^ (B + 1) := le_trans (Finset.card_le_card hidxsubcost) hcardcost
  have hUB : (⋃ p ∈ idx, T p).ncard ≤ ∑ p ∈ idx, (T p).ncard :=
    Finset.set_ncard_biUnion_le idx T
  have hcardTeq : ∀ p, (T p).ncard = Nat.card {μ' : Fin n ↪ Fin m // ∀ q, p.2 (μ' q) = p.1 q} :=
    fun p => by rw [hTdef]; exact (Nat.card_coe_set_eq _).symm
  have hterm : ∀ p ∈ idx, (T p).ncard * 2 ^ (B + d + 2) ≤ POP := by
    intro p hp
    rw [hidxdef, Finset.mem_filter] at hp
    rw [hcardTeq, Nat.mul_comm]
    exact le_of_lt hp.2.2
  have hsum : (∑ p ∈ idx, (T p).ncard) * 2 ^ (B + d + 2) ≤ idx.card * POP := by
    calc (∑ p ∈ idx, (T p).ncard) * 2 ^ (B + d + 2)
        = ∑ p ∈ idx, (T p).ncard * 2 ^ (B + d + 2) := by rw [Finset.sum_mul]
      _ ≤ ∑ _p ∈ idx, POP := Finset.sum_le_sum hterm
      _ = idx.card * POP := by rw [Finset.sum_const, smul_eq_mul]
  have hfinal : (⋃ p ∈ idx, T p).ncard * 2 ^ (B + d + 2) ≤ 2 ^ (B + 1) * POP :=
    calc (⋃ p ∈ idx, T p).ncard * 2 ^ (B + d + 2)
        ≤ (∑ p ∈ idx, (T p).ncard) * 2 ^ (B + d + 2) := Nat.mul_le_mul_right _ hUB
      _ ≤ idx.card * POP := hsum
      _ ≤ 2 ^ (B + 1) * POP := Nat.mul_le_mul_right _ hidxcard
  have hpoweq : 2 ^ (B + d + 2) = 2 ^ (B + 1) * 2 ^ (d + 1) := by
    rw [← pow_add]; congr 1; omega
  have h2B1 : 0 < 2 ^ (B + 1) := Nat.pow_pos (by norm_num)
  have hcancel : (⋃ p ∈ idx, T p).ncard * 2 ^ (d + 1) ≤ POP := by
    apply Nat.le_of_mul_le_mul_left _ h2B1
    calc 2 ^ (B + 1) * ((⋃ p ∈ idx, T p).ncard * 2 ^ (d + 1))
        = (⋃ p ∈ idx, T p).ncard * (2 ^ (B + 1) * 2 ^ (d + 1)) := by ring
      _ = (⋃ p ∈ idx, T p).ncard * 2 ^ (B + d + 2) := by rw [hpoweq]
      _ ≤ 2 ^ (B + 1) * POP := hfinal
  rw [hsub]
  calc (⋃ p ∈ idx, T p).ncard * 2 ^ d
      ≤ (⋃ p ∈ idx, T p).ncard * 2 ^ (d + 1) :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) (by omega))
    _ ≤ POP := hcancel

/-- **The alphabet-uniform cap** ([Guests] §7, Theorem 7.13(ii) extended; §9.2's alphabet
paragraph): the staged capacity's cap over EVERY label alphabet at once, at the per-alphabet
order — the doubled budget the normalization pays never reaches the exponent, which stays `2 * b`
plus a fixed constant rather than growing with the alphabet. Degenerate carriers (`m = 0`) cost
nothing: `Fin n ↪ Fin 0` forces `n = 0`, whose sole candidate carries at most `0! = 1` at any
budget. -/
theorem CbHs_collapse_uniform {n m : ℕ} (b d : ℕ) :
    {μ : Fin n ↪ Fin m | 2 ^ (2 * b + elen rankBuilder + d + 8) < CbHs μ b}.ncard * 2 ^ d
      ≤ m.descFactorial n := by
  rcases Nat.eq_zero_or_pos m with hm0 | hm
  · subst hm0
    have hempty : {μ : Fin n ↪ Fin 0 | 2 ^ (2 * b + elen rankBuilder + d + 8) < CbHs μ b} = ∅ := by
      ext μ
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_lt]
      have hn0 : n = 0 := by
        have hle := Fintype.card_le_of_embedding μ
        simpa using hle
      subst hn0
      have hcap : CbHs μ b ≤ Nat.factorial 0 :=
        csSup_le' (fun N hN => stagedBudgetedEntropies_le hN)
      have h1 : Nat.factorial 0 ≤ 2 ^ (2 * b + elen rankBuilder + d + 8) := by
        rw [Nat.factorial_zero]
        exact Nat.one_le_two_pow
      omega
    rw [hempty, Set.ncard_empty]
    simp
  · set B := 2 * b + elen rankBuilder + 6 with hBdef
    have hEeq : 2 * b + elen rankBuilder + d + 8 = B + d + 2 := by rw [hBdef]; omega
    have hsub : {μ : Fin n ↪ Fin m | 2 ^ (2 * b + elen rankBuilder + d + 8) < CbHs μ b}
        ⊆ {μ : Fin n ↪ Fin m | ∃ (ℓR : Fin n → Fin m) (ℓR' : Fin m → Fin m),
             (∀ q, ℓR' (μ q) = ℓR q) ∧ KE (Nat.pair (lensCode ℓR) (lensCode ℓR')) ≤ B ∧
             2 ^ (B + d + 2) * Nat.card {μ' : Fin n ↪ Fin m // ∀ q, ℓR' (μ' q) = ℓR q}
               < m.descFactorial n} := by
      intro μ hμ
      simp only [Set.mem_ofPred_eq] at hμ
      rw [hEeq] at hμ
      obtain ⟨N, hN, hNlt⟩ := exists_mem_stagedBudgetedEntropies_gt hμ
      obtain ⟨k, ℓ, ℓ', hcons, hbℓ, hbℓ', hNeq⟩ := hN
      refine ⟨rankOf ℓ' hm ∘ ℓ, rankOf ℓ' hm ∘ ℓ', rankOf_consistent hcons hm, ?_, ?_⟩
      · have hprice := KE_rankBuilder_pair_le hcons hm
        omega
      · have : Nonempty {μ' : Fin n ↪ Fin m //
            ∀ q, (rankOf ℓ' hm ∘ ℓ') (μ' q) = (rankOf ℓ' hm ∘ ℓ) q} :=
          ⟨⟨μ, rankOf_consistent hcons hm⟩⟩
        have hded : 0 < Nat.card {μ' : Fin n ↪ Fin m //
            ∀ q, (rankOf ℓ' hm ∘ ℓ') (μ' q) = (rankOf ℓ' hm ∘ ℓ) q} := Nat.card_pos
        have hInjRange : Set.InjOn (rankOf ℓ' hm) (Set.range ℓ) :=
          (rankOf_injOn_mem ℓ' hm).mono (by
            rintro v ⟨q, rfl⟩
            exact hcons q ▸ mem_lensTable_apply ℓ' (μ q))
        have horbit : Nat.card ↥(orbit (Equiv.Perm (Fin n)) (rankOf ℓ' hm ∘ ℓ)) = N := by
          rw [orbit_postcomp_card_eq (rankOf ℓ' hm) ℓ hInjRange]
          exact hNeq.symm
        have hNlt' :
            2 ^ (B + d + 2) < Nat.card ↥(orbit (Equiv.Perm (Fin n)) (rankOf ℓ' hm ∘ ℓ)) := by
          rw [horbit]; exact hNlt
        calc 2 ^ (B + d + 2) * Nat.card {μ' : Fin n ↪ Fin m //
              ∀ q, (rankOf ℓ' hm ∘ ℓ') (μ' q) = (rankOf ℓ' hm ∘ ℓ) q}
            < Nat.card ↥(orbit (Equiv.Perm (Fin n)) (rankOf ℓ' hm ∘ ℓ)) *
              Nat.card {μ' : Fin n ↪ Fin m //
                ∀ q, (rankOf ℓ' hm ∘ ℓ') (μ' q) = (rankOf ℓ' hm ∘ ℓ) q} :=
              mul_lt_mul_of_pos_right hNlt' hded
          _ ≤ m.descFactorial n := orbit_mul_deductible_le (rankOf ℓ' hm ∘ ℓ) (rankOf ℓ' hm ∘ ℓ')
    calc {μ : Fin n ↪ Fin m | 2 ^ (2 * b + elen rankBuilder + d + 8) < CbHs μ b}.ncard * 2 ^ d
        ≤ {μ : Fin n ↪ Fin m | ∃ (ℓR : Fin n → Fin m) (ℓR' : Fin m → Fin m),
             (∀ q, ℓR' (μ q) = ℓR q) ∧ KE (Nat.pair (lensCode ℓR) (lensCode ℓR')) ≤ B ∧
             2 ^ (B + d + 2) * Nat.card {μ' : Fin n ↪ Fin m // ∀ q, ℓR' (μ' q) = ℓR q}
               < m.descFactorial n}.ncard * 2 ^ d :=
          Nat.mul_le_mul_right _ (Set.ncard_le_ncard hsub (Set.toFinite _))
      _ ≤ m.descFactorial n := collapse_union_normalized B d

/-- **The alphabet-uniform cap, at a growing world** ([Guests] §7 Theorem 7.13's extension, read at
a growing world's own stage law): `CbHs_collapse_uniform` at `stageLawEmb`'s own domain and
codomain sizes, in `CbHs_collapse_growing`'s own shape. -/
theorem CbHs_collapse_uniform_growing {X : Type*} {U : X → X} {Ω : ℕ → Set X} (hadv : Advances U Ω)
    (t b d : ℕ) (hf : (mergeStage U Ω t).Finite) (hf' : (mergeStage U Ω (t + 1)).Finite) :
    Nonempty (Fin hf.toFinset.card ↪ Fin hf'.toFinset.card) ∧
    {μ : Fin hf.toFinset.card ↪ Fin hf'.toFinset.card |
       2 ^ (2 * b + elen rankBuilder + d + 8) < CbHs μ b}.ncard * 2 ^ d
      ≤ hf'.toFinset.card.descFactorial hf.toFinset.card :=
  ⟨⟨stageLawEmb hadv t hf hf'⟩, CbHs_collapse_uniform b d⟩

/-! ## The guard: a real growing world reaches the bridge -/

/-- The successor world's initial-segment stages advance: `s ≤ t` gives `s + 1 ≤ t + 1`. The
cheapest already-landed instance for `collapse_union_growing`'s guard — `MemoryWidth.lean` computes
this world's retained profile already. -/
private theorem advances_natSucc_slowClock : Advances Nat.succ (fun t => Set.Iic t) :=
  fun _t _s hs => Nat.succ_le_succ (Set.mem_Iic.mp hs)

/-- The successor world's stage-`t` retained profile is finite: its `encard` is the finite value
`t + 1` (`mergeStage_nat_succ_slowClock_encard`), never `⊤`. -/
private theorem finite_mergeStage_natSucc_slowClock (t : ℕ) :
    (mergeStage Nat.succ (fun t => Set.Iic t) t).Finite := by
  rw [← Set.encard_ne_top_iff, mergeStage_nat_succ_slowClock_encard]
  exact_mod_cast (ENat.natCast_lt_top t.succ).ne

/-- The chosen enumeration's count matches the paper's own `t + 1`, read off the same `encard`
equation that supplies finiteness. -/
private theorem card_finite_mergeStage_natSucc_slowClock (t : ℕ) :
    (finite_mergeStage_natSucc_slowClock t).toFinset.card = t + 1 := by
  have h := mergeStage_nat_succ_slowClock_encard t
  rw [Set.Finite.encard_eq_coe_toFinset_card (finite_mergeStage_natSucc_slowClock t)] at h
  exact_mod_cast h

/-- **The guard** ([Guests] §7 Theorem 7.11(vi)): `collapse_union_growing` instantiated at the
successor world's initial-segment stages, an already-landed world (`MemoryWidth.lean`'s
`mergeStage_nat_succ_slowClock_encard`), with `n = t + 1` and `m = t + 2` falling straight out of
that world's own retained-profile count — some real growing world reaches the transported collapse,
not merely types against it. -/
theorem collapse_union_growing_natSucc_slowClock (t d : ℕ) {k : ℕ} :
    Nonempty (Fin (t + 1) ↪ Fin (t + 2)) ∧
    {μ : Fin (t + 1) ↪ Fin (t + 2) | ∃ (ℓ : Fin (t + 1) → Fin k) (ℓ' : Fin (t + 2) → Fin k),
       (∀ q, ℓ' (μ q) = ℓ q) ∧
       2 ^ (KE (lensCode ℓ) + KE (lensCode ℓ') + d + 2)
         * Nat.card {μ' : Fin (t + 1) ↪ Fin (t + 2) // ∀ q, ℓ' (μ' q) = ℓ q}
         < (t + 2).descFactorial (t + 1)}.ncard * 2 ^ d
      ≤ (t + 2).descFactorial (t + 1) := by
  have hcard := card_finite_mergeStage_natSucc_slowClock t
  have hcard' := card_finite_mergeStage_natSucc_slowClock (t + 1)
  simp only [show t + 1 + 1 = t + 2 from rfl] at hcard'
  have hmain := collapse_union_growing advances_natSucc_slowClock t d
    (finite_mergeStage_natSucc_slowClock t) (finite_mergeStage_natSucc_slowClock (t + 1)) (k := k)
  rw [hcard, hcard'] at hmain
  exact hmain

/-! ## The telescope: an arbitrary injection sequence realized as a growing world's own stage law

[Guests] §7 Theorem 7.11's boundary paragraph: the candidate population `collapse_union_staged`
prices is exactly the population a growing world can present, because the telescope below realizes
ANY sequence of injections between the stage sizes as a growing world's own stage law. -/

/-- **The telescope's update**: `⟨t, q⟩ ↦ ⟨t + 1, lam t q⟩` — one step of an arbitrary sequence of
injections `lam`, read as a self-map of the disjoint union of the stage carriers. -/
def telescopeU {ns : ℕ → ℕ} (lam : ∀ t, Fin (ns t) ↪ Fin (ns (t + 1))) :
    (Σ t, Fin (ns t)) → Σ t, Fin (ns t) := fun s => ⟨s.1 + 1, lam s.1 s.2⟩

/-- **The telescope's stages**: the `t`-th summand alone. -/
def telescopeΩ (ns : ℕ → ℕ) (t : ℕ) : Set (Σ t, Fin (ns t)) := {s | s.1 = t}

/-- **The telescope advances**: `U` raises the summand index by exactly one, whatever `lam` does
inside it. -/
theorem advances_telescopeU {ns : ℕ → ℕ} (lam : ∀ t, Fin (ns t) ↪ Fin (ns (t + 1))) :
    Advances (telescopeU lam) (telescopeΩ ns) := by
  intro t s hs
  have hs' : s.1 = t := hs
  change (telescopeU lam s).1 = t + 1
  simp only [telescopeU]
  omega

/-- **The telescope's own update is injective**: distinct summand-`t` points step to distinct
summand-`(t + 1)` points (`lam t` injective), and distinct summands step to distinct summands. -/
private theorem telescopeU_injective {ns : ℕ → ℕ} (lam : ∀ t, Fin (ns t) ↪ Fin (ns (t + 1))) :
    Function.Injective (telescopeU lam) := by
  rintro ⟨t, q⟩ ⟨t', q'⟩ h
  simp only [telescopeU, Sigma.mk.injEq] at h
  obtain ⟨ht, hq⟩ := h
  have ht' : t = t' := by omega
  subst ht'
  have hqq' : q = q' := (lam t).injective (eq_of_heq hq)
  subst hqq'
  rfl

/-- **No merging ever happens**: the telescope's own update is injective outright
(`telescopeU_injective`), so the merge relation collapses to bare equality — `mergeMk` is
injective on the whole carrier, not merely per stage. -/
private theorem telescope_mergeMk_injective {ns : ℕ → ℕ}
    (lam : ∀ t, Fin (ns t) ↪ Fin (ns (t + 1))) :
    Function.Injective (mergeMk (telescopeU lam)) := by
  intro s s' h
  obtain ⟨k, hk⟩ := Quotient.exact h
  exact (telescopeU_injective lam).iterate k hk

private theorem sigmaMk_injective (ns : ℕ → ℕ) (t : ℕ) :
    Function.Injective (fun q : Fin (ns t) => (⟨t, q⟩ : Σ t, Fin (ns t))) := by
  intro q q' h
  simp only [Sigma.mk.injEq] at h
  exact eq_of_heq h.2

private theorem telescopeΩ_eq_range (ns : ℕ → ℕ) (t : ℕ) :
    telescopeΩ ns t = Set.range (fun q : Fin (ns t) => (⟨t, q⟩ : Σ t, Fin (ns t))) := by
  ext s
  simp only [telescopeΩ, Set.mem_ofPred_eq, Set.mem_range]
  constructor
  · intro hs
    subst hs
    exact ⟨s.2, rfl⟩
  · rintro ⟨q, rfl⟩
    rfl

private theorem telescopeΩ_finite (ns : ℕ → ℕ) (t : ℕ) : (telescopeΩ ns t).Finite := by
  rw [telescopeΩ_eq_range]
  exact Set.finite_range _

private theorem telescopeΩ_ncard (ns : ℕ → ℕ) (t : ℕ) : (telescopeΩ ns t).ncard = ns t := by
  rw [telescopeΩ_eq_range, ← Set.image_univ,
    Set.ncard_image_of_injective _ (sigmaMk_injective ns t), Set.ncard_univ,
    Nat.card_eq_fintype_card, Fintype.card_fin]

/-- **The `t`-th retained profile is finite.** -/
theorem mergeStage_telescope_finite {ns : ℕ → ℕ}
    (lam : ∀ t, Fin (ns t) ↪ Fin (ns (t + 1))) (t : ℕ) :
    (mergeStage (telescopeU lam) (telescopeΩ ns) t).Finite :=
  (telescopeΩ_finite ns t).image _

/-- **The `t`-th retained profile numbers `ns t`**: no merging happens at all
(`telescope_mergeMk_injective`), so the profile's count is the stage's own count
(`telescopeΩ_ncard`). -/
theorem mergeStage_telescope_ncard {ns : ℕ → ℕ} (lam : ∀ t, Fin (ns t) ↪ Fin (ns (t + 1))) (t : ℕ) :
    (mergeStage (telescopeU lam) (telescopeΩ ns) t).ncard = ns t := by
  change (mergeMk (telescopeU lam) '' telescopeΩ ns t).ncard = ns t
  rw [Set.ncard_image_of_injective _ (telescope_mergeMk_injective lam), telescopeΩ_ncard]

private noncomputable def telescopeEquivA (ns : ℕ → ℕ) (t : ℕ) :
    Fin (ns t) ≃ ↥(Set.range (fun q : Fin (ns t) => (⟨t, q⟩ : Σ t, Fin (ns t)))) :=
  Equiv.ofInjective _ (sigmaMk_injective ns t)

private noncomputable def telescopeEquivB (ns : ℕ → ℕ) (t : ℕ) :
    ↥(Set.range (fun q : Fin (ns t) => (⟨t, q⟩ : Σ t, Fin (ns t)))) ≃ ↥(telescopeΩ ns t) :=
  Set.equivOfEq (telescopeΩ_eq_range ns t).symm

private noncomputable def telescopeEquivC {ns : ℕ → ℕ} (lam : ∀ t, Fin (ns t) ↪ Fin (ns (t + 1)))
    (t : ℕ) :
    ↥(telescopeΩ ns t) ≃ ↥(mergeMk (telescopeU lam) '' telescopeΩ ns t) :=
  Equiv.Set.image _ _ (telescope_mergeMk_injective lam)

/-- The composed enumeration, typed against the raw image (the shape the pieces above compose to
— `telescopeFullEquiv` below retypes it against `mergeStage`, which needs its own `.trans` step,
because the two types are only DEFINITIONALLY equal and an ascription mismatch here breaks the
`simp` computation of `telescopeFullEquiv0_coe`). -/
private noncomputable def telescopeFullEquiv0 {ns : ℕ → ℕ}
    (lam : ∀ t, Fin (ns t) ↪ Fin (ns (t + 1))) (t : ℕ) :
    Fin (ns t) ≃ ↥(mergeMk (telescopeU lam) '' telescopeΩ ns t) :=
  (telescopeEquivA ns t).trans ((telescopeEquivB ns t).trans (telescopeEquivC lam t))

private theorem telescopeFullEquiv0_coe {ns : ℕ → ℕ} (lam : ∀ t, Fin (ns t) ↪ Fin (ns (t + 1)))
    (t : ℕ) (q : Fin (ns t)) :
    (telescopeFullEquiv0 lam t q : MergeQuot (telescopeU lam)) =
      mergeMk (telescopeU lam) (⟨t, q⟩ : Σ t, Fin (ns t)) := by
  simp [telescopeFullEquiv0, telescopeEquivA, telescopeEquivB, telescopeEquivC, Equiv.trans_apply,
    Equiv.Set.image_apply, Set.equivOfEq_apply, Equiv.ofInjective_apply]

/-- **The chosen enumeration** `stageLawEmb`'s own docstring names: `mergeStage`'s stage-`t`
retained profile enumerated by the telescope's own construction, `⟨t, ·⟩` composed with the
merge quotient's reading. -/
private noncomputable def telescopeFullEquiv {ns : ℕ → ℕ} (lam : ∀ t, Fin (ns t) ↪ Fin (ns (t + 1)))
    (t : ℕ) :
    Fin (ns t) ≃ ↥(mergeStage (telescopeU lam) (telescopeΩ ns) t) :=
  (telescopeFullEquiv0 lam t).trans (Set.equivOfEq rfl)

private theorem telescopeFullEquiv_coe {ns : ℕ → ℕ} (lam : ∀ t, Fin (ns t) ↪ Fin (ns (t + 1)))
    (t : ℕ) (q : Fin (ns t)) :
    (telescopeFullEquiv lam t q : MergeQuot (telescopeU lam)) =
      mergeMk (telescopeU lam) (⟨t, q⟩ : Σ t, Fin (ns t)) := by
  change ((telescopeFullEquiv0 lam t).trans (Set.equivOfEq rfl) q :
    MergeQuot (telescopeU lam)) = _
  rw [Equiv.trans_apply, Set.equivOfEq_apply]
  exact telescopeFullEquiv0_coe lam t q

/-- **The telescope's own law IS `lam`, under the chosen enumeration**: `mergeLaw` applied to the
enumeration's stage-`t` reading is the enumeration's stage-`(t + 1)` reading of `lam t`'s value —
`mergeLaw_mergeMk` composed with `telescopeU`'s own definition. This is the fact that makes
`stageLawEmb` (below) realize `lam` rather than some unrelated embedding. -/
private theorem telescopeFullEquiv_succ {ns : ℕ → ℕ} (lam : ∀ t, Fin (ns t) ↪ Fin (ns (t + 1)))
    (t : ℕ) (q : Fin (ns t)) :
    (⟨mergeLaw (telescopeU lam) (telescopeFullEquiv lam t q).1,
      advances_mergeStage (advances_telescopeU lam) t (telescopeFullEquiv lam t q).1
        (telescopeFullEquiv lam t q).2⟩ :
      ↥(mergeStage (telescopeU lam) (telescopeΩ ns) (t + 1)))
      = telescopeFullEquiv lam (t + 1) (lam t q) := by
  apply Subtype.ext
  change mergeLaw (telescopeU lam) (telescopeFullEquiv lam t q).1 =
    (telescopeFullEquiv lam (t + 1) (lam t q) : MergeQuot (telescopeU lam))
  rw [telescopeFullEquiv_coe, telescopeFullEquiv_coe, mergeLaw_mergeMk]
  rfl

/-- **`stageLawEmb` factors through its own choice of enumeration**, named: unfolding its
definition and extracting the two `Fintype.equivFin`-built equivalences and the `mergeLaw`
embedding it composes, verbatim — the general fact any two calls to `stageLawEmb` at the SAME
`hf`/`hf'` share, needed because those two equivalences are otherwise opaque outside the
definition (a `Classical.choice`-derived enumeration, not a formula). -/
private theorem stageLawEmb_factorization {X : Type*} {U : X → X} {Ω : ℕ → Set X}
    (hadv : Advances U Ω) (t : ℕ) (hf : (mergeStage U Ω t).Finite)
    (hf' : (mergeStage U Ω (t + 1)).Finite) :
    ∃ (p1 : ↥(mergeStage U Ω t) ≃ Fin hf.toFinset.card)
      (p2 : ↥(mergeStage U Ω (t + 1)) ≃ Fin hf'.toFinset.card),
      stageLawEmb hadv t hf hf' = p1.symm.toEmbedding.trans
        ((⟨fun x => ⟨mergeLaw U x.1, advances_mergeStage hadv t x.1 x.2⟩,
           fun x y hxy => Subtype.ext (mergeStage_injOn U Ω t x.2 y.2 (congrArg Subtype.val hxy))⟩ :
          ↥(mergeStage U Ω t) ↪ ↥(mergeStage U Ω (t + 1))).trans p2.toEmbedding) := by
  unfold stageLawEmb
  extract_lets ie1 ihe1 ie2 ihe2 iemb ihemb
  exact ⟨ie1, ie2, rfl⟩

/-- **`stageLawEmb` intertwines `mergeLaw`, at its own (unnamed) choice of enumeration**: read at
that choice on both ends, `stageLawEmb` agrees with `mergeLaw` — `stageLawEmb_factorization`
applied to a point and its `Equiv.symm_apply_apply` cancelled against itself. -/
private theorem stageLawEmb_apply_eq {X : Type*} {U : X → X} {Ω : ℕ → Set X}
    (hadv : Advances U Ω) (t : ℕ) (hf : (mergeStage U Ω t).Finite)
    (hf' : (mergeStage U Ω (t + 1)).Finite) :
    ∃ (p1 : ↥(mergeStage U Ω t) ≃ Fin hf.toFinset.card)
      (p2 : ↥(mergeStage U Ω (t + 1)) ≃ Fin hf'.toFinset.card),
      ∀ x : ↥(mergeStage U Ω t), stageLawEmb hadv t hf hf' (p1 x) =
        p2 ⟨mergeLaw U x.1, advances_mergeStage hadv t x.1 x.2⟩ := by
  obtain ⟨p1, p2, hfact⟩ := stageLawEmb_factorization hadv t hf hf'
  refine ⟨p1, p2, fun x => ?_⟩
  rw [hfact]
  simp only [Function.Embedding.trans_apply, Function.Embedding.coeFn_mk,
    Equiv.symm_apply_apply]
  rfl

/-- **The telescope realizes every injection sequence** ([Guests] §7 Theorem 7.11's boundary,
*"Growth does not sharpen the bound"*): for ANY `ns` and ANY sequence of injections `lam` between
the stage sizes, the telescope is a growing world reaching `Advances`, whose `mergeStage` at every
`t` has cardinality `ns t`, and whose `stageLawEmb` — at the SAME chosen enumeration on both ends
— is `lam t` exactly. So the candidate population `collapse_union_staged` prices at `(n, m) :=
(ns t, ns (t + 1))` is precisely the population a growing world's own stage law can present:
nothing here restricts which pair of enumerated finite types arises as `(mergeStage t, mergeStage
(t + 1))` of an actual `(U, Ω)`. The enumeration is EXISTENTIALLY quantified, not asserted equal to
some canonical one — a different choice of `Set.Finite.toFinset` gives a different embedding at the
same two numerals, exactly as `stageLawEmb`'s own docstring states. -/
theorem telescope_realizes_lawSequence (ns : ℕ → ℕ) (lam : ∀ t, Fin (ns t) ↪ Fin (ns (t + 1))) :
    ∃ (X : Type) (U : X → X) (Ω : ℕ → Set X) (hadv : Advances U Ω),
      (∀ t, ∃ hf : (mergeStage U Ω t).Finite, hf.toFinset.card = ns t) ∧
      ∀ t (hf : (mergeStage U Ω t).Finite) (hf' : (mergeStage U Ω (t + 1)).Finite),
        ∃ (e : Fin (ns t) ≃ Fin hf.toFinset.card) (e' : Fin (ns (t + 1)) ≃ Fin hf'.toFinset.card),
          ∀ q : Fin (ns t), stageLawEmb hadv t hf hf' (e q) = e' (lam t q) := by
  refine ⟨Σ t, Fin (ns t), telescopeU lam, telescopeΩ ns, advances_telescopeU lam, ?_, ?_⟩
  · intro t
    refine ⟨mergeStage_telescope_finite lam t, ?_⟩
    rw [← Set.ncard_eq_toFinset_card _ (mergeStage_telescope_finite lam t)]
    exact mergeStage_telescope_ncard lam t
  · intro t hf hf'
    obtain ⟨p1, p2, hkey⟩ := stageLawEmb_apply_eq (advances_telescopeU lam) t hf hf'
    refine ⟨(telescopeFullEquiv lam t).trans p1, (telescopeFullEquiv lam (t + 1)).trans p2,
      fun q => ?_⟩
    change stageLawEmb (advances_telescopeU lam) t hf hf' (p1 (telescopeFullEquiv lam t q))
      = p2 (telescopeFullEquiv lam (t + 1) (lam t q))
    rw [hkey, telescopeFullEquiv_succ]

end GrowingPrice

/-! ## Axiom audit

Every capstone above is `#print axioms`-clean on the standard triple, and the guards below make
that build-enforced. -/

set_option linter.style.longLine false

/-- info: 'GrowingPrice.exists_ne_frames_agreeing_on_range' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GrowingPrice.exists_ne_frames_agreeing_on_range

/-- info: 'GrowingPrice.card_stageLaws' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GrowingPrice.card_stageLaws

/-- info: 'GrowingPrice.card_lawsConsistentWith' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GrowingPrice.card_lawsConsistentWith

/-- info: 'GrowingPrice.card_stageLaws_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GrowingPrice.card_stageLaws_self

/-- info: 'GrowingPrice.card_lawsConsistentWith_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GrowingPrice.card_lawsConsistentWith_self

/-- info: 'GrowingPrice.kraft_lensCode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GrowingPrice.kraft_lensCode

/-- info: 'GrowingPrice.collapse_union_staged' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GrowingPrice.collapse_union_staged

/-- info: 'GrowingPrice.exists_qualifying_pair_of_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GrowingPrice.exists_qualifying_pair_of_pos

/-- info: 'GrowingPrice.stageLawEmb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GrowingPrice.stageLawEmb

/-- info: 'GrowingPrice.collapse_union_growing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GrowingPrice.collapse_union_growing

/-- info: 'GrowingPrice.collapse_union_growing_natSucc_slowClock' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GrowingPrice.collapse_union_growing_natSucc_slowClock

/-- info: 'GrowingPrice.telescope_realizes_lawSequence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GrowingPrice.telescope_realizes_lawSequence

/-- info: 'GrowingPrice.deductible_smul_invariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GrowingPrice.deductible_smul_invariant

/-- info: 'GrowingPrice.sum_deductible_eq_card_stageLaws' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GrowingPrice.sum_deductible_eq_card_stageLaws

/-- info: 'GrowingPrice.orbit_mul_deductible_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GrowingPrice.orbit_mul_deductible_le

/-- info: 'GrowingPrice.CbHs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GrowingPrice.CbHs

/-- info: 'GrowingPrice.CbHs_collapse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GrowingPrice.CbHs_collapse

/-- info: 'GrowingPrice.markingLens_comp_embedding' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GrowingPrice.markingLens_comp_embedding

/-- info: 'GrowingPrice.CbHs_ge_marking' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GrowingPrice.CbHs_ge_marking

/-- info: 'GrowingPrice.CbH_le_CbHs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GrowingPrice.CbH_le_CbHs

/-- info: 'GrowingPrice.CbHs_collapse_growing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GrowingPrice.CbHs_collapse_growing

/-- info: 'GrowingPrice.exists_candidate_capacity_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GrowingPrice.exists_candidate_capacity_le

/-- info: 'GrowingPrice.CbHs_collapse_uniform' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GrowingPrice.CbHs_collapse_uniform

/-- info: 'GrowingPrice.CbHs_collapse_uniform_growing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GrowingPrice.CbHs_collapse_uniform_growing
