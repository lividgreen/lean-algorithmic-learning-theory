/-
Copyright (c) 2026 Mykola Palamarchuk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mykola Palamarchuk
-/
import Batteries.Tactic.OpenPrivate
import Mathlib.Data.Finite.Perm
import Mathlib.Data.Nat.Choose.Multinomial
import ALT.BinaryConstant
import ALT.Collector
import ALT.Persistence.MovingLens

-- Formal-check file, not Mathlib-destined: opt out of the house-style header linter.
set_option linter.style.header false

/-!
# Persistence capacity III: complexity and counting ([Persistence] §5–§8)

Part three of the `PersistenceCapacity` development (umbrella and map: `ALT.PersistenceCapacity`,
whose docstring decodes the capacity names `Cb`, `CbH`, `CbHu`, …). The ledger of
`ALT.Persistence.MovingLens` says the observer stores the world's rule; this module counts what
that storage costs and shows the price is generically unpayable.

## Main results

* `Cb` / `capacity_sandwich` — the **budgeted persistence capacity** ([Persistence] §5): the
  largest model carried by a family whose every frame's core table costs at most `b` bits.
  Monotone in the budget, capped by the core at every budget, and above the static levels past a
  finite one.
* `collapse` / `collapse_balanced` / `collapse_generic` — **the price is generically unpayable**
  ([Persistence] §7): over a permutation world the second frame is forced, a budget of `b` bits
  describes at most `2 ^ (b + 1)` frames, and each frame is hit by exactly one coset of the
  lens's stabilizer.
* `collapse_union` — the same **uniformly over the reference frame** ([Persistence] §7,
  Corollary 7.4), by the Kraft inequality: all but a `2 ^ (-d)` fraction of worlds price *every*
  persistent reading at the entropy it carries. There are no discounts.
* `CbH` / `CbH_collapse` / `CbH_ge_marking'` — **the entropic capacity is pinned at `Θ(b)`**
  ([Persistence] §5, Definition 5.4; §7, Corollary 7.5(i)): the honest currency is the carried
  entropy of the reference frame, and an observer keeps, to within a factor two, exactly the
  entropy it pays for.
* `KE_markingLens_le` — **the marks are provably cheap** ([Persistence] §5, Proposition 5.3): an
  explicit program, uniform over where the marks sit, tabulates `r` marks on `n` states. It
  discharges the marking floor's price hypothesis.
* `CbHu` — the **uniform** capacity (renting versus owning, [Persistence] §5, Definition 5.1's
  uniform variant), with the ownership construction ([Persistence] §8, Proposition 8.1) and
  `CbHu_le_CbH` (owning beats renting by at most the clock, over a permutation world).
* The **graded ledger** ([Persistence] Open problem 8.4's design) and the **ledger at any
  frames** ([Persistence] §6, Theorem 6.5), with Corollary 8.11(i) (what a factor buys, exactly)
  and the **paired frame** ([Persistence] Remark 6.6, and §7's paired table from one uniform
  code): an address is paid once.
* The multiplicative congruential world (cheap dynamics, exhibited), faithful self-reading priced
  at the world's rule, and capacity out to a finite horizon (`CbH_upTo` / `CbHu_upTo`).
-/

namespace PersistenceCapacity

open Decoupling CodeEvalLaws

variable {X ι V M : Type*}

open AdditiveComplexity KolmogorovComplexity Nat.Partrec Nat.Partrec.Code

-- File-boundary bookkeeping for the split development: these helpers stay `private` (they are
-- proof plumbing, not interface), and the sibling modules reach them with `open private`.
open private eval_icode idx_map_finRange primrec_idx from ALT.Persistence.MovingLens

/-! ### The budgeted capacity ([Persistence] §5)

The ceiling of Proposition 3.5 prices the decoder at zero. An observer, however, must STORE the
decoder it runs, and the complexity of a frame is the complexity of its table on the core — the part
of the frame the persistence identity constrains (`ledger_K` fixes exactly this reading of `K (ℓ)`).

`Cb U eC b` is the largest model carried by a family whose EVERY frame costs at most `b` bits: the
budgeted persistence capacity, in cardinality (not logarithmic) form. It is monotone in the budget,
capped by the recurrent core at every budget, and it reaches the static levels of §4 at some finite
budget — the sandwich `static ≤ C_b ≤ |core|`. That the top of the sandwich is generically
unreachable is the collapse of §7 below. -/

section Budget

variable {ι V : Type*} [Finite ι] [Finite V]

/-- The frame's **table on the core**, along a chosen enumeration `eC` of the core: the model index
each core state is read as. This is the finite object the budget prices, and it is the same
tabulation the ledger's complexity form uses (`frameTable`). -/
def coreTable {n m : ℕ} (U : Mem ι V → Mem ι V) (eC : ↥(core U) ≃ Fin n) (f : Mem ι V → Fin m) :
    List ℕ :=
  (List.finRange n).map fun i => ((f ((eC.symm i : ↥(core U)) : Mem ι V) : Fin m) : ℕ)

/-- The family is **affordable at budget `b`**: every frame's core table has complexity at most `b`.
The budget is per-frame (a uniform variant — one program computing `t ↦ ℓ t` — costs each frame an
extra `O (log t)`). -/
def Budgeted {n m : ℕ} (U : Mem ι V → Mem ι V) (eC : ↥(core U) ≃ Fin n) (ℓ : Lens (Mem ι V) (Fin m))
    (b : ℕ) : Prop :=
  ∀ t, KE (Encodable.encode (coreTable U eC (ℓ t))) ≤ b

/-- The model sizes carried by SOME budget-`b` family. -/
def BudgetedSizes {n : ℕ} (U : Mem ι V → Mem ι V) (eC : ↥(core U) ≃ Fin n) (b : ℕ) : Set ℕ :=
  {m : ℕ | ∃ ℓ : Lens (Mem ι V) (Fin m), Carries U ℓ ∧ Budgeted U eC ℓ b}

/-- **The budgeted persistence capacity** ([Persistence] §5, Definition 5.1), in cardinality form:
the largest model carried by a lens family every frame of which costs at most `b` bits. The
unbudgeted limit is the ceiling of Proposition 3.5; the content of the theory is what happens
strictly below it. -/
noncomputable def Cb {n : ℕ} (U : Mem ι V → Mem ι V) (eC : ↥(core U) ≃ Fin n) (b : ℕ) : ℕ :=
  sSup (BudgetedSizes U eC b)

/-- Nothing carried at any budget exceeds the core (Proposition 3.5 applied to the underlying
unbudgeted family). -/
private theorem budgetedSizes_le {n : ℕ} {U : Mem ι V → Mem ι V} {eC : ↥(core U) ≃ Fin n} {b m : ℕ}
    (hm : m ∈ BudgetedSizes U eC b) : m ≤ Nat.card ↥(core U) := by
  obtain ⟨ℓ, hcar, -⟩ := hm
  simpa using capacity_core hcar

private theorem bddAbove_budgetedSizes {n : ℕ} (U : Mem ι V → Mem ι V) (eC : ↥(core U) ≃ Fin n)
    (b : ℕ) : BddAbove (BudgetedSizes U eC b) :=
  ⟨Nat.card ↥(core U), fun _ hm => budgetedSizes_le hm⟩

/-- **The upper half of the sandwich** ([Persistence] §5, Proposition 5.2): no budget buys more than
the recurrent core. -/
theorem Cb_le_core {n : ℕ} (U : Mem ι V → Mem ι V) (eC : ↥(core U) ≃ Fin n) (b : ℕ) :
    Cb U eC b ≤ Nat.card ↥(core U) := by
  rcases Set.eq_empty_or_nonempty (BudgetedSizes U eC b) with hemp | hne
  · simp [Cb, hemp]
  · exact csSup_le hne fun _ hm => budgetedSizes_le hm

/-- More budget never hurts: `Cb` is monotone. -/
theorem Cb_mono {n : ℕ} (U : Mem ι V → Mem ι V) (eC : ↥(core U) ≃ Fin n) {b₁ b₂ : ℕ}
    (h : b₁ ≤ b₂) : Cb U eC b₁ ≤ Cb U eC b₂ :=
  csSup_le_csSup' (bddAbove_budgetedSizes U eC b₂) (by
    rintro m ⟨ℓ, hcar, hbud⟩
    exact ⟨ℓ, hcar, fun t => (hbud t).trans h⟩)

/-- **The lower half of the sandwich, in finite-budget form** ([Persistence] §5, Proposition 5.2). A
static lens is a CONSTANT family, so all its frames have the one complexity its table has — whatever
that is — and every budget from there up carries it. (The paper's explicit threshold `c₀ + log₂ n`
prices that one table; the finite-budget form is what the capacity object needs.) -/
theorem Cb_ge_of_static {n m : ℕ} (U : Mem ι V → Mem ι V) (eC : ↥(core U) ≃ Fin n)
    {f : Mem ι V → Fin m} (hst : ∀ s, f (U s) = f s) (hsurj : Function.Surjective f) :
    ∃ b, m ≤ Cb U eC b := by
  have hiter : ∀ t s, f (U^[t] s) = f s := by
    intro t
    induction t with
    | zero => intro s; rfl
    | succ t ih => intro s; rw [Function.iterate_succ_apply', hst, ih]
  exact ⟨KE (Encodable.encode (coreTable U eC f)),
    le_csSup (bddAbove_budgetedSizes U eC _) ⟨fun _ => f, ⟨hsurj, fun t s => hiter t s⟩,
      fun _ => le_refl _⟩⟩

/-- The whole static stratum of [Persistence] §4 is affordable at some finite budget: the quotient
map onto the components is a static lens (`components_carries`). -/
theorem Cb_ge_components {n : ℕ} (U : Mem ι V → Mem ι V) (eC : ↥(core U) ≃ Fin n) :
    ∃ b, Nat.card (Quotient (orbitSetoid U)) ≤ Cb U eC b := by
  have e := Finite.equivFin (Quotient (orbitSetoid U))
  refine Cb_ge_of_static U eC (f := fun s => e (Quotient.mk (orbitSetoid U) s)) ?_ ?_
  · intro s
    rw [(components_carries U).1 s]
  · exact e.surjective.comp Quotient.mk_surjective

/-- The read-only capacity of [Decoupling] §3 (Corollary 3.3) is affordable at some finite budget —
the L1 stratum through the L2 one (`fix_le_components`). -/
theorem Cb_ge_fix {n : ℕ} (U : Mem ι V → Mem ι V) (eC : ↥(core U) ≃ Fin n) :
    ∃ b, Nat.card V ^ Nat.card ↥(Fix U) ≤ Cb U eC b := by
  obtain ⟨b, hb⟩ := Cb_ge_components U eC
  exact ⟨b, le_trans (fix_le_components U) hb⟩

/-- **The sandwich** ([Persistence] §5, Proposition 5.2): past some finite budget the capacity is
pinned between the static levels of §4 and the recurrent core. Which end it sits at is the question
of §7 — and generically it is the bottom. -/
theorem capacity_sandwich {n : ℕ} (U : Mem ι V → Mem ι V) (eC : ↥(core U) ≃ Fin n) :
    ∃ b₀, ∀ b ≥ b₀, Nat.card (Quotient (orbitSetoid U)) ≤ Cb U eC b ∧
      Cb U eC b ≤ Nat.card ↥(core U) := by
  obtain ⟨b₀, hb₀⟩ := Cb_ge_components U eC
  exact ⟨b₀, fun b hb => ⟨hb₀.trans (Cb_mono U eC hb), Cb_le_core U eC b⟩⟩

end Budget

/-! ### The collapse: counting decoders over the symmetric group ([Persistence] §7)

The ledger says a maximal moving decoder CONTAINS the world's recurrent rule. This section shows the
price is generically unpayable, by counting.

The setting is the one the counting needs, and the one [Persistence] §7 states: the world IS its own
recurrent core — a permutation `U` of `Fin n` — and the model is `Fin m`. There the ledger is
immediate and needs no maximality: persistence at `t = 1` reads `ℓ 1 (U x) = ℓ 0 x`, and `U` is
invertible, so `ℓ 1 = ℓ 0 ∘ U⁻¹` (`permCarries_frame_one`) — the second frame is DETERMINED by the
first frame and the world. (In the cell-structured setting of the rest of this file that is
`lens_bijOn_core` and `ledger`, where invertibility must first be recovered on the core.)

Counting then does the rest. Permutations act on lenses by `U • ℓ = ℓ ∘ U⁻¹`; the stabilizer of `ℓ₀`
is the product of the symmetric groups of its fibers (`card_stabilizer_lens`), so the lenses
reachable from `ℓ₀` — exactly those with `ℓ₀`'s fiber sizes (`mem_orbit_lens_iff`) — number
`n ! / ∏ᵢ (fiberᵢ) !`, and the balanced case is `n ! / ((n / m) !) ^ m` (`card_balancedLenses`). A
budget of `b` bits describes at most `2 ^ (b + 1)` tables (`card_KE_le`), each pulled back to one
coset of the stabilizer, so at most `2 ^ (b + 1) · ∏ᵢ (fiberᵢ) !` permutations admit an affordable
second frame (`collapse_count`). Dividing: all but a `2 ^ (b + 1) / N_bal` fraction of worlds admit
NO budget-`b` family carrying the model at all (`collapse`, `collapse_generic`).

Carrying even one persistent bit by a moving decoder, in a generic world, costs more description
than the world itself holds. -/

section Collapse

open MulAction Equiv Nat AdditiveComplexity

-- Throughout, `•` on lenses is the relabelling action `U • ℓ = ℓ ∘ U⁻¹`. Every statement below is
-- written at a symbolic label count `m`, where that is the only reading: Mathlib's pointwise `Pi`
-- action needs the codomain to be acted on, and `Perm (Fin n)` does not act on `Fin m`. Beware the
-- degenerate case — at `m = n` the pointwise action `(U • ℓ) x = U (ℓ x)` also typechecks and,
-- being a direct instance, WINS over this one (reached through `MulAction.toSMul`). Raising this
-- attribute's priority does not change that. So faithful (`m = n`) frames are stated below as
-- `⇑(U ^ t)⁻¹` outright rather than as `(U ^ t) • id`: the two are definitionally equal, and only
-- the former means the same thing after elaboration.
attribute [local instance] arrowAction

variable {n m : ℕ}

/-- Permutations act on lenses by relabelling the domain: `U • ℓ` reads the cell `U⁻¹ x` where `ℓ`
read `x`. This is the action under which the canonical family of Proposition 3.5 moves its
frames. -/
private theorem smul_lens_apply {α β : Type*} (U : Perm α) (ℓ : α → β) (x : α) :
    (U • ℓ) x = ℓ (U⁻¹ x) := rfl

/-- A permutation stabilizes a lens exactly when it preserves the lens's fibers. -/
private theorem mem_stabilizer_lens {α β : Type*} {U : Perm α} {ℓ : α → β} :
    U ∈ stabilizer (Perm α) ℓ ↔ ∀ x, ℓ (U x) = ℓ x := by
  constructor
  · intro h x
    have := congrFun (mem_stabilizer_iff.mp h) (U x)
    rw [smul_lens_apply] at this
    simpa using this.symm
  · intro h
    refine mem_stabilizer_iff.mpr (funext fun x => ?_)
    rw [smul_lens_apply]
    have := h (U⁻¹ x)
    simpa using this.symm

/-- **The stabilizer of a lens is the product of the symmetric groups of its fibers**
([Persistence] §7, Lemma 7.1). A fiber-preserving permutation is exactly a choice of one permutation
per fiber: forward, restrict; backward, assemble along the fibration of `Fin n` by `ℓ`. -/
private noncomputable def stabEquivPi {α β : Type*} (ℓ : α → β) :
    ↥(stabilizer (Perm α) ℓ) ≃ ∀ i : β, Perm {x : α // ℓ x = i} where
  toFun U := fun i => Equiv.Perm.subtypePerm U.1 (fun x => by
    rw [mem_stabilizer_lens.mp U.2 x])
  invFun τ := ⟨(Equiv.permCongr (Equiv.sigmaFiberEquiv ℓ)) (Equiv.sigmaCongrRight τ),
    mem_stabilizer_lens.mpr fun x => (τ (ℓ x) ⟨x, rfl⟩).2⟩
  left_inv U := by
    ext x
    rfl
  right_inv τ := by
    funext i
    ext y
    obtain ⟨y, rfl⟩ := y
    rfl

/-- **Fiber uniformity, in cardinality form, at any codomain** ([Persistence] §7, Lemma 7.1, stated
codomain-generally): the permutations fixing a lens number `∏ᵢ (fiberᵢ) !`, the product ranging over
the lens's whole codomain rather than over `Fin m`. -/
theorem card_stabilizer_lens_dom {α β : Type*} [Finite α] [Fintype β] (ℓ : α → β) :
    Nat.card ↥(stabilizer (Perm α) ℓ) = ∏ i : β, (Nat.card {x : α // ℓ x = i})! := by
  rw [Nat.card_congr (stabEquivPi ℓ), Nat.card_pi]
  exact Finset.prod_congr rfl fun i _ => Nat.card_perm

/-- **Fiber uniformity, in cardinality form** ([Persistence] §7, Lemma 7.1): the permutations fixing
a lens number `∏ᵢ (fiberᵢ) !`. The `Fin m` case of `card_stabilizer_lens_dom`, kept at its own name
since [Persistence]'s FV-8 row cites it directly. -/
theorem card_stabilizer_lens {α : Type*} [Finite α] (ℓ : α → Fin m) :
    Nat.card ↥(stabilizer (Perm α) ℓ) = ∏ i : Fin m, (Nat.card {x : α // ℓ x = i})! :=
  card_stabilizer_lens_dom ℓ

/-- **The descent coset, as a bijection onto the stabilizer** ([Persistence] §8, Corollary
8.11(i)'s own count): `V ↦ V * U⁻¹` bijects the permutations descending through `κ` with law `W`
onto `stabilizer (Perm (Fin n)) κ`, `U` itself supplying the non-emptiness witness — the identical
move `FrameItinerary.consistentEquivStab` runs for the joint itinerary's stabilizer. -/
private noncomputable def descentEquivStab {z : ℕ} (κ : Fin n → Fin z) (W : Fin z → Fin z)
    {U : Perm (Fin n)} (hU : ∀ x, κ (U x) = W (κ x)) :
    ↥{V : Perm (Fin n) | ∀ x, κ (V x) = W (κ x)} ≃ ↥(stabilizer (Perm (Fin n)) κ) where
  toFun V := ⟨V.1 * U⁻¹, by
    rw [mem_stabilizer_lens]
    intro x
    have h1 : κ (V.1 (U⁻¹ x)) = W (κ (U⁻¹ x)) := V.2 (U⁻¹ x)
    have hux : U (U⁻¹ x) = x := by simp
    have h2 : κ x = W (κ (U⁻¹ x)) := by
      conv_lhs => rw [← hux]
      exact hU (U⁻¹ x)
    rw [Equiv.Perm.mul_apply, h1]
    exact h2.symm⟩
  invFun V' := ⟨V'.1 * U, by
    intro x
    have hV' : κ (V'.1 (U x)) = κ (U x) := mem_stabilizer_lens.mp V'.2 (U x)
    rw [Equiv.Perm.mul_apply, hV']
    exact hU x⟩
  left_inv V := Subtype.ext (by group)
  right_inv V' := Subtype.ext (by group)

/-- **The descent coset** ([Persistence] §8, Corollary 8.11(i)'s own count, corrected against §8's
verification note — the note had listed this as machine-checked already, and it is one coset short
of `card_stabilizer_lens_dom`, the `W = id` case). Given `κ` and a law `W` through which some
permutation `U` descends, the permutations descending through `κ` with that SAME law number exactly
`∏ᵢ (fiberᵢ)!` — Lemma 7.1's count read at `κ` rather than at a stabilizer's own defining lens.
`W` preserving `κ`'s fiber sizes is not an extra hypothesis: it follows from `U` being a permutation
that descends, so no such hypothesis appears below. -/
theorem card_descentCoset {z : ℕ} (κ : Fin n → Fin z) (W : Fin z → Fin z) {U : Perm (Fin n)}
    (hU : ∀ x, κ (U x) = W (κ x)) :
    Nat.card ↥{V : Perm (Fin n) | ∀ x, κ (V x) = W (κ x)}
      = ∏ i : Fin z, (Nat.card {x : Fin n // κ x = i})! := by
  rw [Nat.card_congr (descentEquivStab κ W hU)]
  exact card_stabilizer_lens_dom κ

/-- **Non-vacuity: at `W = id` the descent coset is the fiber-stabilizer itself**, agreeing with
`card_stabilizer_lens_dom` exactly — the check the design round asked for, since nothing in the
tree previously counted the descent set at a general law. -/
theorem card_descentCoset_id {z : ℕ} (κ : Fin n → Fin z) :
    Nat.card ↥{V : Perm (Fin n) | ∀ x, κ (V x) = κ x}
      = Nat.card ↥(stabilizer (Perm (Fin n)) κ) := by
  have h := card_descentCoset κ id (U := 1) (fun x => by simp)
  simp only [id] at h
  rw [h, card_stabilizer_lens_dom]

/-- **The orbit of a lens is the set of lenses with its fiber sizes** ([Persistence] §7, Lemma 7.1,
the surjectivity half). Precomposing with a permutation cannot change how many states a value is
read from; conversely, any lens with the same fiber sizes is reached by matching the fibers up. -/
theorem mem_orbit_lens_iff {α : Type*} [Finite α] (ℓ₀ ℓ : α → Fin m) :
    ℓ ∈ orbit (Perm α) ℓ₀ ↔
      ∀ i, Nat.card {x : α // ℓ x = i} = Nat.card {x : α // ℓ₀ x = i} := by
  classical
  have : Fintype α := Fintype.ofFinite _
  constructor
  · rintro ⟨U, rfl⟩ i
    have hequiv : {x : α // ℓ₀ x = i} ≃ {x : α // (U • ℓ₀) x = i} :=
      Equiv.subtypeEquiv U fun x => by
        change ℓ₀ x = i ↔ ℓ₀ (U⁻¹ (U x)) = i
        simp
    exact (Nat.card_congr hequiv).symm
  · intro h
    have e : ∀ i, {x : α // ℓ x = i} ≃ {x : α // ℓ₀ x = i} := fun i =>
      (Fintype.card_eq.mp (by
        rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]; exact h i)).some
    set τ : Perm α :=
      (Equiv.sigmaFiberEquiv ℓ).symm.trans
        ((Equiv.sigmaCongrRight e).trans (Equiv.sigmaFiberEquiv ℓ₀)) with hτ
    have hτ_apply : ∀ x, ℓ₀ (τ x) = ℓ x := fun x => (e (ℓ x) ⟨x, rfl⟩).2
    refine MulAction.mem_orbit_iff.mpr ⟨τ⁻¹, funext fun x => ?_⟩
    rw [smul_lens_apply, inv_inv, hτ_apply]

/-- **Orbit–stabilizer for lenses, over any finite domain** ([Persistence] §2, Definition 2.2;
§7, Lemma 7.2): a lens's relabelling class on a finite set `S` numbers `|S| ! / ∏ᵢ (fiberᵢ) !` —
stated multiplicatively, which is what the counting consumes.

This is Definition 2.2's carried entropy `E_S (ℓ)` in cardinality form, at the generality the
definition is stated: an arbitrary finite `S`, not merely the whole world.
`card_orbit_mul_prod_fiber` below is the case `S = Fin n` that §7's counting uses; the recurrent
core — the `S` that Definition 2.2 actually prices a persistent family on — is `α = ↥(core U)`. -/
theorem card_orbit_mul_prod_fiber_card {α : Type*} [Finite α] (ℓ : α → Fin m) :
    Nat.card ↥(orbit (Perm α) ℓ) * ∏ i : Fin m, (Nat.card {x : α // ℓ x = i})!
      = (Nat.card α)! := by
  classical
  have : Fintype α := Fintype.ofFinite _
  have : Fintype ↥(orbit (Perm α) ℓ) := Fintype.ofFinite _
  have : Fintype ↥(stabilizer (Perm α) ℓ) := Fintype.ofFinite _
  have h := MulAction.card_orbit_mul_card_stabilizer_eq_card_group (Perm α) ℓ
  rw [← card_stabilizer_lens ℓ, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, h,
    Fintype.card_perm, Nat.card_eq_fintype_card]

/-- **Orbit–stabilizer for lenses** ([Persistence] §7, Lemma 7.2): the lenses with `ℓ`'s fiber sizes
number `n ! / ∏ᵢ (fiberᵢ) !` — stated multiplicatively, which is what the counting consumes. -/
theorem card_orbit_mul_prod_fiber (ℓ : Fin n → Fin m) :
    Nat.card ↥(orbit (Perm (Fin n)) ℓ) * ∏ i : Fin m, (Nat.card {x : Fin n // ℓ x = i})!
      = n ! := by
  simpa using card_orbit_mul_prod_fiber_card ℓ

/-! ### The fiber profile's extremes ([Persistence] Open problem 8.4's design, the graded ledger)

Two elementary facts about a lens's fiber profile, needed to force the marking anatomy at the
incompressible pole: the profile's relabelling class is never much smaller than a binomial
coefficient (`orbitCard_ge_choose`), and a surjective lens with a dominant fiber has few labels
(`card_le_marks_succ`). Neither needs a world or a persistence identity — both read Lemma 7.1's
orbit–stabilizer count against the profile's largest part. -/

/-- The fiber sizes of `ℓ₀` sum to the size of the domain (Definition 2.2's profile, totalled):
`Σᵢ (fiberᵢ) = n`, the sigma-decomposition of `Fin n` by `ℓ₀`. -/
private theorem sum_fiber_card_eq (ℓ₀ : Fin n → Fin m) :
    ∑ i : Fin m, Nat.card {x : Fin n // ℓ₀ x = i} = n := by
  have h := Nat.card_congr (Equiv.sigmaFiberEquiv ℓ₀)
  rw [Nat.card_sigma, Nat.card_eq_fintype_card, Fintype.card_fin] at h
  exact h

/-- **The orbit is never smaller than a binomial coefficient** ([Persistence] Open problem 8.4's
design, the marking-anatomy counting half). Writing `maxFiber` for the largest fiber of `ℓ₀` and
`m' := n − maxFiber` for what sits off it, `∏ᵢ (fiberᵢ)! ≤ maxFiber! · m'!` — a product of
factorials divides the factorial of its sum (`Nat.multinomial_spec`, off the dominant fiber) —
so orbit–stabilizer (`card_orbit_mul_prod_fiber`) gives `n.choose m' ≤ N₀`, sharp at every
two-fiber profile `(n − m', m')` (`orbitCard_eq_choose_of_two_fiber`). -/
theorem orbitCard_ge_choose (ℓ₀ : Fin n → Fin m) :
    n.choose (n - Finset.univ.sup fun i : Fin m => Nat.card {x : Fin n // ℓ₀ x = i})
      ≤ Nat.card ↥(orbit (Perm (Fin n)) ℓ₀) := by
  classical
  set f : Fin m → ℕ := fun i => Nat.card {x : Fin n // ℓ₀ x = i} with hf
  rcases Nat.eq_zero_or_pos n with hn0 | hnpos
  · -- `n = 0`: the domain is empty, the sup over `f` is `0` regardless of `m`, and the orbit of the
    -- (unique) lens on `Fin 0` is a single point.
    subst hn0
    have : Nonempty ↥(orbit (Perm (Fin 0)) ℓ₀) := ⟨⟨ℓ₀, MulAction.mem_orbit_self ℓ₀⟩⟩
    have h1 : 1 ≤ Nat.card ↥(orbit (Perm (Fin 0)) ℓ₀) := Nat.card_pos
    simpa using h1
  · -- `n > 0`: `Fin m` is nonempty (`ℓ₀`'s value at any point witnesses it), so sup is attained.
    have : Nonempty (Fin m) := ⟨ℓ₀ ⟨0, hnpos⟩⟩
    obtain ⟨i₀, -, hi₀⟩ := Finset.exists_mem_eq_sup Finset.univ Finset.univ_nonempty f
    set maxFiber := Finset.univ.sup f with hmaxdef
    set m' := n - maxFiber with hm'def
    have hsum : ∑ i : Fin m, f i = n := sum_fiber_card_eq ℓ₀
    have hmaxle : maxFiber ≤ n := by
      rw [hi₀, ← hsum]
      exact Finset.single_le_sum (fun i _ => Nat.zero_le (f i)) (Finset.mem_univ i₀)
    have hnm' : n - m' = maxFiber := by omega
    have hsum' : ∑ i ∈ Finset.univ.erase i₀, f i = m' := by
      have hadd := Finset.add_sum_erase Finset.univ f (Finset.mem_univ i₀)
      rw [← hi₀] at hadd
      omega
    have hmulti := Nat.multinomial_spec (Finset.univ.erase i₀) f
    rw [hsum'] at hmulti
    have hdvd : (∏ i ∈ Finset.univ.erase i₀, (f i)!) ≤ m' ! := by
      have hpos := Nat.multinomial_pos (Finset.univ.erase i₀) f
      nlinarith [hmulti]
    have hprodsplit : ∏ i : Fin m, (f i)! = (f i₀)! * ∏ i ∈ Finset.univ.erase i₀, (f i)! :=
      (Finset.mul_prod_erase Finset.univ (fun i => (f i)!) (Finset.mem_univ i₀)).symm
    have hprodle : ∏ i : Fin m, (f i)! ≤ maxFiber ! * m' ! := by
      rw [hprodsplit, ← hi₀]
      exact Nat.mul_le_mul_left _ hdvd
    have hcard := card_orbit_mul_prod_fiber ℓ₀
    have hchoose : n.choose m' * (m' ! * maxFiber !) = n ! := by
      have hkey := Nat.choose_mul_factorial_mul_factorial (Nat.sub_le n maxFiber)
      rw [hnm'] at hkey
      rw [← mul_assoc]
      exact hkey
    have hstep : n.choose m' * (m' ! * maxFiber !)
        ≤ Nat.card ↥(orbit (Perm (Fin n)) ℓ₀) * (maxFiber ! * m' !) := by
      rw [hchoose]
      calc n ! = Nat.card ↥(orbit (Perm (Fin n)) ℓ₀) * ∏ i : Fin m, (f i)! := hcard.symm
        _ ≤ Nat.card ↥(orbit (Perm (Fin n)) ℓ₀) * (maxFiber ! * m' !) :=
          Nat.mul_le_mul_left _ hprodle
    have hpos2 : 0 < m' ! * maxFiber ! := Nat.mul_pos (Nat.factorial_pos _) (Nat.factorial_pos _)
    rw [Nat.mul_comm (maxFiber !) (m' !)] at hstep
    exact Nat.le_of_mul_le_mul_right hstep hpos2

/-- **Sharpness of `orbitCard_ge_choose`**: on the two-fiber profile itself — `ℓ₀ : Fin n → Fin 2`
with fiber sizes exactly `(n − m', m')` — the orbit is exactly the binomial coefficient, not merely
bounded below by it. The bound is tight, not slack. -/
theorem orbitCard_eq_choose_of_two_fiber {m' : ℕ} (hmn : m' ≤ n) {ℓ₀ : Fin n → Fin 2}
    (h0 : Nat.card {x : Fin n // ℓ₀ x = 0} = n - m') (h1 : Nat.card {x : Fin n // ℓ₀ x = 1} = m') :
    Nat.card ↥(orbit (Perm (Fin n)) ℓ₀) = n.choose m' := by
  have hcard := card_orbit_mul_prod_fiber ℓ₀
  rw [Fin.prod_univ_two, h0, h1] at hcard
  have hchoose := Nat.choose_mul_factorial_mul_factorial hmn
  have hfact : n.choose m' * (m' ! * (n - m')!) = n ! := by
    rw [show m' ! * (n - m')! = (n - m')! * m' ! from Nat.mul_comm _ _]
    linarith [hchoose]
  have hpos : 0 < (n - m')! * m' ! := Nat.mul_pos (Nat.factorial_pos _) (Nat.factorial_pos _)
  have hfin : Nat.card ↥(orbit (Perm (Fin n)) ℓ₀) * ((n - m')! * m' !)
      = n.choose m' * ((n - m')! * m' !) := by
    rw [hcard]
    linarith [hfact]
  exact Nat.eq_of_mul_eq_mul_right hpos hfin

/-- **A surjective lens with a dominant fiber has few labels** ([Persistence] Open problem 8.4's
design, the marking-anatomy counting half). If every value off the largest fiber sits in one of
`m'` states, a surjective lens has at most `m' + 1` labels: the dominant label plus at most one
label per state off it, since surjectivity gives every other label a nonempty (hence `≥ 1`-sized)
fiber, and those fibers are disjoint subsets of the `m'` remaining states. -/
theorem card_le_marks_succ {ℓ₀ : Fin n → Fin m} (hs : Function.Surjective ℓ₀) :
    m ≤ (n - Finset.univ.sup fun i : Fin m => Nat.card {x : Fin n // ℓ₀ x = i}) + 1 := by
  classical
  set f : Fin m → ℕ := fun i => Nat.card {x : Fin n // ℓ₀ x = i} with hf
  rcases Nat.eq_zero_or_pos m with hm0 | hmpos
  · omega
  · have : Nonempty (Fin m) := ⟨⟨0, hmpos⟩⟩
    obtain ⟨i₀, -, hi₀⟩ := Finset.exists_mem_eq_sup Finset.univ Finset.univ_nonempty f
    have hsum : ∑ i : Fin m, f i = n := sum_fiber_card_eq ℓ₀
    have hpos : ∀ i, 0 < f i := by
      intro i
      rw [hf]
      obtain ⟨x, hx⟩ := hs i
      exact Nat.card_pos_iff.mpr ⟨⟨⟨x, hx⟩⟩, inferInstance⟩
    have hsum' : ∑ i ∈ Finset.univ.erase i₀, f i = n - Finset.univ.sup f := by
      have hadd := Finset.add_sum_erase Finset.univ f (Finset.mem_univ i₀)
      rw [← hi₀] at hadd
      omega
    have hcard_erase : (Finset.univ.erase i₀ : Finset (Fin m)).card = m - 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ i₀), Finset.card_univ, Fintype.card_fin]
    have hge : (Finset.univ.erase i₀ : Finset (Fin m)).card
        ≤ ∑ i ∈ Finset.univ.erase i₀, f i := by
      calc (Finset.univ.erase i₀ : Finset (Fin m)).card
          = ∑ _i ∈ Finset.univ.erase i₀, 1 := by rw [Finset.sum_const, smul_eq_mul, Nat.mul_one]
        _ ≤ ∑ i ∈ Finset.univ.erase i₀, f i := Finset.sum_le_sum fun i _ => hpos i
    rw [hcard_erase, hsum'] at hge
    omega

/-- A lens is **balanced** when every value is read from the same number `n / m` of states — the
extremal case of [Persistence] §7, and the one maximality forces up to the core's cycle
structure. -/
def Balanced (ℓ : Fin n → Fin m) : Prop := ∀ i, Nat.card {x : Fin n // ℓ x = i} = n / m

/-- Balanced lenses exist whenever the model size divides the core size: read the state's index
modulo `m`, whose fibers are the `m` arithmetic progressions of step `m`. -/
theorem exists_balanced (hm : 0 < m) (hdvd : m ∣ n) : ∃ ℓ : Fin n → Fin m, Balanced ℓ := by
  have hmul : n / m * m = n := Nat.div_mul_cancel hdvd
  refine ⟨fun x => ⟨(x : ℕ) % m, Nat.mod_lt _ hm⟩, fun i => ?_⟩
  have hbound : ∀ j : Fin (n / m), (j : ℕ) * m + (i : ℕ) < n := by
    intro j
    have h1 : (j : ℕ) * m + m ≤ n / m * m := by
      calc (j : ℕ) * m + m = ((j : ℕ) + 1) * m := by ring
        _ ≤ n / m * m := Nat.mul_le_mul_right m j.2
    have h2 : (i : ℕ) < m := i.2
    omega
  have e : {x : Fin n // (⟨(x : ℕ) % m, Nat.mod_lt _ hm⟩ : Fin m) = i} ≃ Fin (n / m) :=
    { toFun := fun x => ⟨x.val.val / m, Nat.div_lt_div_of_lt_of_dvd hdvd x.val.isLt⟩
      invFun := fun j => ⟨⟨(j : ℕ) * m + (i : ℕ), hbound j⟩, by
        apply Fin.ext
        simp [Nat.mod_eq_of_lt i.2]⟩
      left_inv := fun x => by
        have hx : x.val.val % m = (i : ℕ) := congrArg Fin.val x.property
        apply Subtype.ext
        apply Fin.ext
        simpa [hx] using Nat.div_add_mod' x.val.val m
      right_inv := fun j => by
        apply Fin.ext
        change ((j : ℕ) * m + (i : ℕ)) / m = (j : ℕ)
        rw [Nat.add_comm, Nat.add_mul_div_right _ _ hm, Nat.div_eq_of_lt i.2, Nat.zero_add] }
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_fin]

private theorem prod_fiber_balanced {ℓ : Fin n → Fin m} (h : Balanced ℓ) :
    ∏ i : Fin m, (Nat.card {x : Fin n // ℓ x = i})! = ((n / m)!) ^ m := by
  rw [Finset.prod_congr rfl fun i (_ : i ∈ Finset.univ) => by rw [h i]]
  simp

/-- **The count of balanced lenses** ([Persistence] §7, Lemma 7.2): `N_bal = n ! / ((n / m) !) ^ m`,
stated multiplicatively. Its logarithm is `κ · n − Θ(2 ^ κ · log n)` for `m = 2 ^ κ` — a Stirling
estimate, and the one presentation-level step this development leaves to the paper. -/
theorem card_balancedLenses {ℓ : Fin n → Fin m} (h : Balanced ℓ) :
    Nat.card ↥(orbit (Perm (Fin n)) ℓ) * ((n / m)!) ^ m = n ! := by
  rw [← prod_fiber_balanced h]
  exact card_orbit_mul_prod_fiber ℓ

/-- The lens, tabulated along `Fin n`: the finite object whose complexity prices the frame. -/
def lensTable (ℓ : Fin n → Fin m) : List ℕ := (List.finRange n).map fun i => (ℓ i : ℕ)

/-- The encoded tabulation. `KE (lensCode ℓ)` is the frame's price, in the sense of `ledger_K`. -/
def lensCode (ℓ : Fin n → Fin m) : ℕ := Encodable.encode (lensTable ℓ)

private theorem lensCode_injective : Function.Injective (lensCode (n := n) (m := m)) := by
  intro ℓ ℓ' h
  have h2 : lensTable ℓ = lensTable ℓ' := Encodable.encode_injective h
  funext x
  have hx : ((ℓ x : Fin m) : ℕ) = ((ℓ' x : Fin m) : ℕ) :=
    (List.map_inj_left.mp h2) x (List.mem_finRange x)
  exact Fin.val_injective hx

/-- **The collapse count** ([Persistence] §7, Theorem 7.3, the counting core). At most
`2 ^ (b + 1) · ∏ᵢ (fiberᵢ) !` permutations have a `b`-affordable relabelled frame.

Two facts multiply. A budget of `b` bits describes at most `2 ^ (b + 1)` tables (`card_KE_le`), and
a lens determines its permutations up to the stabilizer — the permutations sending `ℓ₀` to a GIVEN
lens form one coset, of size `∏ᵢ (fiberᵢ) !` (`card_stabilizer_lens`). Affordable frames are
therefore few, and the permutations that admit one are few times the coset size. -/
theorem collapse_count (ℓ₀ : Fin n → Fin m) (b : ℕ) :
    {U : Perm (Fin n) | KE (lensCode (U • ℓ₀)) ≤ b}.ncard
      ≤ 2 ^ (b + 1) * ∏ i : Fin m, (Nat.card {x : Fin n // ℓ₀ x = i})! := by
  classical
  set f : Perm (Fin n) → ℕ := fun U => lensCode (U • ℓ₀) with hf
  set S : Finset (Perm (Fin n)) := Finset.univ.filter fun U => KE (f U) ≤ b with hSdef
  set T : Finset ℕ := (finite_KE_le b).toFinset with hTdef
  -- each fiber of `f` over `S` injects into the stabilizer: it is (part of) one coset
  have hfib : ∀ v ∈ T, (S.filter fun U => f U = v).card
      ≤ ∏ i : Fin m, (Nat.card {x : Fin n // ℓ₀ x = i})! := by
    intro v _
    rcases Finset.eq_empty_or_nonempty (S.filter fun U => f U = v) with hemp | ⟨W, hW⟩
    · simp [hemp]
    · have hWv : f W = v := (Finset.mem_filter.mp hW).2
      have : Fintype ↥(stabilizer (Perm (Fin n)) ℓ₀) := Fintype.ofFinite _
      have hmaps : ∀ U ∈ S.filter fun U => f U = v,
          W⁻¹ * U ∈ (stabilizer (Perm (Fin n)) ℓ₀ : Set (Perm (Fin n))).toFinset := by
        intro U hU
        have hUv : f U = v := (Finset.mem_filter.mp hU).2
        have hlens : U • ℓ₀ = W • ℓ₀ := lensCode_injective (hUv.trans hWv.symm)
        simp only [Set.mem_toFinset, SetLike.mem_coe, mem_stabilizer_iff, mul_smul, hlens,
          inv_smul_smul]
      have hinj : Set.InjOn (fun U => W⁻¹ * U) ↑(S.filter fun U => f U = v) :=
        fun a _ c _ hac => mul_left_cancel hac
      have hcard := Finset.card_le_card_of_injOn (fun U => W⁻¹ * U) hmaps hinj
      rw [Set.toFinset_card, ← Nat.card_eq_fintype_card] at hcard
      have hstab : Nat.card ↥((stabilizer (Perm (Fin n)) ℓ₀ : Set (Perm (Fin n))))
          = ∏ i : Fin m, (Nat.card {x : Fin n // ℓ₀ x = i})! := card_stabilizer_lens ℓ₀
      exact hstab ▸ hcard
  have hmapsT : ∀ U ∈ S, f U ∈ T := by
    intro U hU
    simpa [hTdef] using (Finset.mem_filter.mp hU).2
  have hmain := Finset.card_le_mul_card_image_of_maps_to hmapsT
    (∏ i : Fin m, (Nat.card {x : Fin n // ℓ₀ x = i})!) hfib
  have hT : T.card ≤ 2 ^ (b + 1) := by
    have := card_KE_le b
    rwa [Set.ncard_eq_toFinset_card _ (finite_KE_le b)] at this
  have hSset : {U : Perm (Fin n) | KE (lensCode (U • ℓ₀)) ≤ b} = ↑S := by
    ext U; simp [hSdef, hf]
  rw [hSset, Set.ncard_coe_finset]
  calc S.card ≤ (∏ i : Fin m, (Nat.card {x : Fin n // ℓ₀ x = i})!) * T.card := hmain
    _ ≤ (∏ i : Fin m, (Nat.card {x : Fin n // ℓ₀ x = i})!) * 2 ^ (b + 1) :=
        Nat.mul_le_mul_left _ hT
    _ = 2 ^ (b + 1) * ∏ i : Fin m, (Nat.card {x : Fin n // ℓ₀ x = i})! := Nat.mul_comm _ _

/-- The collapse count as a FRACTION of the symmetric group ([Persistence] §7, Theorem 7.3): the
permutations with an affordable relabelled frame are at most a `2 ^ (b + 1) / N_bal` fraction of all
`n !` of them, where `N_bal` is the orbit — division-free, by clearing the denominator. -/
theorem collapse_fraction (ℓ₀ : Fin n → Fin m) (b : ℕ) :
    {U : Perm (Fin n) | KE (lensCode (U • ℓ₀)) ≤ b}.ncard
        * Nat.card ↥(orbit (Perm (Fin n)) ℓ₀) ≤ 2 ^ (b + 1) * n ! := by
  have h1 := collapse_count ℓ₀ b
  have h2 := card_orbit_mul_prod_fiber ℓ₀
  calc {U : Perm (Fin n) | KE (lensCode (U • ℓ₀)) ≤ b}.ncard
        * Nat.card ↥(orbit (Perm (Fin n)) ℓ₀)
      ≤ (2 ^ (b + 1) * ∏ i : Fin m, (Nat.card {x : Fin n // ℓ₀ x = i})!)
        * Nat.card ↥(orbit (Perm (Fin n)) ℓ₀) := Nat.mul_le_mul_right _ h1
    _ = 2 ^ (b + 1) * (Nat.card ↥(orbit (Perm (Fin n)) ℓ₀)
        * ∏ i : Fin m, (Nat.card {x : Fin n // ℓ₀ x = i})!) := by ring
    _ = 2 ^ (b + 1) * n ! := by rw [h2]

/-- **The persistence identity alone** ([Persistence] §7): a family carries `U`'s power through
frame `t` back to frame `0`, without `PermCarries`'s further requirement that `ℓ 0` be surjective.
This is everything the graded ledger's own coset argument uses — `permCarries_frame_one` through
`ledger_graded` read a family only through this identity, never through `ℓ 0`'s surjectivity. -/
def PermPersists (U : Perm (Fin n)) (ℓ : ℕ → Fin n → Fin m) : Prop :=
  ∀ t x, ℓ t ((U ^ t) x) = ℓ 0 x

/-- A lens family over a **permutation world** ([Persistence] §7): the world is its own recurrent
core, so `U^t` is a genuine power and the persistence identity is `ℓ t ∘ U ^ t = ℓ 0`. -/
def PermCarries (U : Perm (Fin n)) (ℓ : ℕ → Fin n → Fin m) : Prop :=
  Function.Surjective (ℓ 0) ∧ PermPersists U ℓ

/-- Every frame of the family is affordable at budget `b` ([Persistence] §5, per-frame budget). -/
def PermBudget (ℓ : ℕ → Fin n → Fin m) (b : ℕ) : Prop := ∀ t, KE (lensCode (ℓ t)) ≤ b

/-- **The ledger over a permutation world** ([Persistence] §6, Theorem 6.1, in the §7 setting): the
second frame is DETERMINED by the first frame and the world, `ℓ 1 = ℓ 0 ∘ U⁻¹`. No maximality is
needed here — the world is already invertible — which is why the counting can price `ℓ 1` for every
family at once. (In the cell-structured setting this is `lens_bijOn_core` and `ledger`.) Only the
persistence identity is used, not `PermCarries`'s surjectivity. -/
theorem permCarries_frame_one {U : Perm (Fin n)} {ℓ : ℕ → Fin n → Fin m}
    (h : PermPersists U ℓ) : ℓ 1 = U • ℓ 0 := by
  funext x
  rw [smul_lens_apply]
  have := h 1 (U⁻¹ x)
  simpa using this

/-- **The Collapse Theorem** ([Persistence] §7, Theorem 7.3). For a fixed reference frame `ℓ₀`, the
worlds admitting ANY budget-`b` family that carries the model through `ℓ₀` number at most
`2 ^ (b + 1) · ∏ᵢ (fiberᵢ) !`.

The proof is the ledger plus the count: the family's second frame must be `ℓ₀ ∘ U⁻¹`
(`permCarries_frame_one`), so a world with an affordable family is a world with an affordable
relabelled frame — and those were counted (`collapse_count`). The budget hypothesis is used at
`t = 1` only, so the theorem is if anything stronger than the paper's per-frame form. -/
theorem collapse (ℓ₀ : Fin n → Fin m) (b : ℕ) :
    {U : Perm (Fin n) | ∃ ℓ : ℕ → Fin n → Fin m,
        PermCarries U ℓ ∧ ℓ 0 = ℓ₀ ∧ PermBudget ℓ b}.ncard
      ≤ 2 ^ (b + 1) * ∏ i : Fin m, (Nat.card {x : Fin n // ℓ₀ x = i})! := by
  refine le_trans (Set.ncard_le_ncard ?_ (Set.toFinite _)) (collapse_count ℓ₀ b)
  rintro U ⟨ℓ, hcar, h0, hbud⟩
  have h1 : ℓ 1 = U • ℓ₀ := by rw [permCarries_frame_one hcar.2, h0]
  have hb := hbud 1
  rwa [h1] at hb

/-- **The Collapse Theorem, balanced case** ([Persistence] §7, Theorem 7.3): with `m = 2 ^ κ` values
each read from `n / m` states, at most `2 ^ (b + 1) · ((n / m) !) ^ m` worlds are affordable. Since
`N_bal = n ! / ((n / m) !) ^ m` has `log₂ N_bal = κ · n − Θ(2 ^ κ log n)`, a budget below that
leaves all but a vanishing fraction of worlds with NO affordable moving decoder. -/
theorem collapse_balanced {ℓ₀ : Fin n → Fin m} (hbal : Balanced ℓ₀) (b : ℕ) :
    {U : Perm (Fin n) | ∃ ℓ : ℕ → Fin n → Fin m,
        PermCarries U ℓ ∧ ℓ 0 = ℓ₀ ∧ PermBudget ℓ b}.ncard
      ≤ 2 ^ (b + 1) * ((n / m)!) ^ m := by
  rw [← prod_fiber_balanced hbal]
  exact collapse ℓ₀ b

/-- **The collapse, as a fraction of all worlds** ([Persistence] §7, Theorem 7.3): the worlds
carrying the model under some budget-`b` family are at most a `2 ^ (b + 1) / N_bal` fraction of the
`n !` permutations of the core. For a budget below `log₂ N_bal − d` the fraction is below
`2 ^ (−d)`: **generic worlds admit no affordable moving decoder at all.** -/
theorem collapse_generic (ℓ₀ : Fin n → Fin m) (b : ℕ) :
    {U : Perm (Fin n) | ∃ ℓ : ℕ → Fin n → Fin m,
        PermCarries U ℓ ∧ ℓ 0 = ℓ₀ ∧ PermBudget ℓ b}.ncard
        * Nat.card ↥(orbit (Perm (Fin n)) ℓ₀) ≤ 2 ^ (b + 1) * n ! := by
  refine le_trans (Nat.mul_le_mul_right _ (Set.ncard_le_ncard ?_ (Set.toFinite _)))
    (collapse_fraction ℓ₀ b)
  rintro U ⟨ℓ, hcar, h0, hbud⟩
  have h1 : ℓ 1 = U • ℓ₀ := by rw [permCarries_frame_one hcar.2, h0]
  have hb := hbud 1
  rwa [h1] at hb

/-- The value list of a **surjective** lens recovers its codomain: the labels are exactly
`{0, …, m − 1}`, so `(lensTable ℓ).toFinset = Finset.range m`. This is the joint prefix-freeness
Corollary 7.4's union over lenses of *different* label counts needs: `lensCode` is injective across
codomains once restricted to surjective lenses, even though `lensTable` stores only the values, not
`m`. -/
private theorem toFinset_lensTable_of_surjective {ℓ : Fin n → Fin m} (hs : Function.Surjective ℓ) :
    (lensTable ℓ).toFinset = Finset.range m := by
  ext v
  simp only [List.mem_toFinset, lensTable, List.mem_map, List.mem_finRange, true_and,
    Finset.mem_range]
  constructor
  · rintro ⟨i, rfl⟩; exact (ℓ i).isLt
  · intro hv; obtain ⟨i, hi⟩ := hs ⟨v, hv⟩; exact ⟨i, by rw [hi]⟩

/-- **`lensCode` is injective on surjective lenses, across codomains** ([Persistence] §7, the joint
prefix-freeness Corollary 7.4's Kraft union requires). Two surjective lenses with the same code have
the same label count: their value lists agree, so their value *sets* `Finset.range m` agree, forcing
`m = m'`. (For fixed `m`, `lensCode_injective` then recovers the lens itself.) No change to
`lensCode` is needed — surjectivity alone recovers the codomain size the encoding does not store. -/
theorem lensCode_codomain_of_surjective {m m' : ℕ} {ℓ : Fin n → Fin m} {ℓ' : Fin n → Fin m'}
    (hs : Function.Surjective ℓ) (hs' : Function.Surjective ℓ') (h : lensCode ℓ = lensCode ℓ') :
    m = m' := by
  have ht : lensTable ℓ = lensTable ℓ' := Encodable.encode_injective h
  have hrange : Finset.range m = Finset.range m' := by
    rw [← toFinset_lensTable_of_surjective hs, ← toFinset_lensTable_of_surjective hs', ht]
  have := congrArg Finset.card hrange
  rwa [Finset.card_range, Finset.card_range] at this

/-- **The per-frame collapse budget, division-free** ([Persistence] §7, Corollary 7.4, the per-lens
ingredient). Fix a reference frame `ℓ₀`; write `N := Nat.card (orbit ℓ₀)` for its relabelling-class
size, so the carried entropy is `log₂ N` (`card_orbit_mul_prod_fiber`). Worlds whose determined
second frame `U • ℓ₀` is so cheap that the two-frame description `KE ℓ₀ + KE (U • ℓ₀)` still falls
`d + 2` below the entropy number `N` are few: their count times `2 ^ (KE ℓ₀ + d + 1)` is at most
`n !`. Multiplicative, so the orbit cardinality cancels against `collapse_fraction` with no division
— the per-lens count Corollary 7.4's Kraft union sums. Threshold `Nat.log 2 N ∸ (KE ℓ₀ + d + 2)`;
below the entropy the bad set is empty (the degenerate branch). -/
theorem collapse_union_frame (ℓ₀ : Fin n → Fin m) (d : ℕ) :
    {U : Perm (Fin n) | 2 ^ (KE (lensCode ℓ₀) + KE (lensCode (U • ℓ₀)) + d + 2)
        < Nat.card ↥(orbit (Perm (Fin n)) ℓ₀)}.ncard * 2 ^ (KE (lensCode ℓ₀) + d + 1) ≤ n ! := by
  classical
  set A := KE (lensCode ℓ₀) with hA
  set N := Nat.card ↥(orbit (Perm (Fin n)) ℓ₀) with hN
  have hNpos : 0 < N := by
    have : Nonempty ↥(orbit (Perm (Fin n)) ℓ₀) := ⟨⟨ℓ₀, mem_orbit_self ℓ₀⟩⟩
    have : Finite ↥(orbit (Perm (Fin n)) ℓ₀) := Set.Finite.to_subtype (Set.toFinite _)
    exact hN ▸ Nat.card_pos
  set Bad := {U : Perm (Fin n) | 2 ^ (A + KE (lensCode (U • ℓ₀)) + d + 2) < N} with hBad
  rcases Set.eq_empty_or_nonempty Bad with hemp | ⟨U₀, hU₀⟩
  · simp only [hemp, Set.ncard_empty, Nat.zero_mul]; exact Nat.zero_le _
  · -- nonempty ⇒ the entropy number exceeds the base budget, so the log threshold is exact
    have hU₀' : 2 ^ (A + KE (lensCode (U₀ • ℓ₀)) + d + 2) < N := hU₀
    have hlow : 2 ^ (A + d + 2) ≤ N :=
      le_of_lt (lt_of_le_of_lt (Nat.pow_le_pow_right (by norm_num) (by omega)) hU₀')
    have hloglow : A + d + 2 ≤ Nat.log 2 N :=
      Nat.le_log_of_pow_le (by norm_num) hlow
    set b₀ := Nat.log 2 N - (A + d + 2) with hb₀
    -- every bad world's determined frame is ≤ b₀-affordable
    have hsub : Bad ⊆ {U : Perm (Fin n) | KE (lensCode (U • ℓ₀)) ≤ b₀} := by
      intro U hU
      have hUlt : 2 ^ (A + KE (lensCode (U • ℓ₀)) + d + 2) < N := hU
      have hup : 2 ^ (A + KE (lensCode (U • ℓ₀)) + d + 2) < 2 ^ (Nat.log 2 N + 1) :=
        lt_of_lt_of_le hUlt (le_of_lt (Nat.lt_pow_succ_log_self (by norm_num) N))
      have hexp : A + KE (lensCode (U • ℓ₀)) + d + 2 < Nat.log 2 N + 1 :=
        (Nat.pow_lt_pow_iff_right (by norm_num)).mp hup
      change KE (lensCode (U • ℓ₀)) ≤ b₀
      omega
    -- collapse_fraction at the threshold budget, then cancel the orbit cardinality
    have hcf := collapse_fraction ℓ₀ b₀
    have hbadN : Bad.ncard * N ≤ 2 ^ (b₀ + 1) * n ! :=
      le_trans (Nat.mul_le_mul_right _ (Set.ncard_le_ncard hsub (Set.toFinite _))) hcf
    have hkey : Bad.ncard * 2 ^ (A + d + 1) * N ≤ n ! * N := by
      calc Bad.ncard * 2 ^ (A + d + 1) * N
            = Bad.ncard * N * 2 ^ (A + d + 1) := by ring
        _ ≤ 2 ^ (b₀ + 1) * n ! * 2 ^ (A + d + 1) := Nat.mul_le_mul_right _ hbadN
        _ = 2 ^ (b₀ + 1 + (A + d + 1)) * n ! := by rw [pow_add]; ring
        _ = 2 ^ (Nat.log 2 N) * n ! := by rw [show b₀ + 1 + (A + d + 1) = Nat.log 2 N by omega]
        _ ≤ N * n ! := Nat.mul_le_mul_right _ (Nat.pow_log_le_self 2 hNpos.ne')
        _ = n ! * N := by ring
    exact Nat.le_of_mul_le_mul_right hkey hNpos

/-- **The Kraft union collapse** ([Persistence] §7, Corollary 7.4, logs cleared). Summing the
per-frame count `collapse_union_frame` over *all* reference frames at once: for every `d`, the
permutation worlds admitting a surjective reference frame `ℓ₀` whose two-frame description
`KE ℓ₀ + KE (ℓ₀ ∘ U⁻¹)` still falls `d + 2` below its carried entropy `log₂ (Nat.card (orbit ℓ₀))`
number at most `n ! / 2 ^ d` — a `2 ^ (-d)` fraction, uniformly over the reference frame.
Generically there are **no discounts**: an observer's two-frame budget must cover the entropy it
carries.

The union ranges over lenses of *different* label counts `Fin m`; it is sound because `lensCode` is
jointly injective on surjective lenses (`lensCode_codomain_of_surjective`), so the Kraft inequality
`kraft_sum_le_one` bounds `∑ 2 ^ (-KE ℓ₀) ≤ 1` over the whole family. Surjectivity forces `m ≤ n`,
so the family is finite. -/
theorem collapse_union (d : ℕ) :
    {U : Perm (Fin n) | ∃ m, ∃ ℓ₀ : Fin n → Fin m, Function.Surjective ℓ₀ ∧
        2 ^ (KE (lensCode ℓ₀) + KE (lensCode (ℓ₀ ∘ ⇑U⁻¹)) + d + 2)
          < Nat.card ↥(orbit (Perm (Fin n)) ℓ₀)}.ncard * 2 ^ d ≤ n ! := by
  classical
  -- surjective lenses with codomain ≤ n — a finite index for the union
  let SL := Σ k : Fin (n + 1), {ℓ : Fin n → Fin (k : ℕ) // Function.Surjective ℓ}
  let frameSet : SL → Set (Perm (Fin n)) := fun s =>
    {U | 2 ^ (KE (lensCode s.2.1) + KE (lensCode (U • s.2.1)) + d + 2)
        < Nat.card ↥(orbit (Perm (Fin n)) s.2.1)}
  set B := {U : Perm (Fin n) | ∃ m, ∃ ℓ₀ : Fin n → Fin m, Function.Surjective ℓ₀ ∧
      2 ^ (KE (lensCode ℓ₀) + KE (lensCode (ℓ₀ ∘ ⇑U⁻¹)) + d + 2)
        < Nat.card ↥(orbit (Perm (Fin n)) ℓ₀)} with hBdef
  -- (1) every bad world is caught by some per-frame bad set
  have hcover : B ⊆ ⋃ s : SL, frameSet s := by
    intro U hU
    obtain ⟨m, ℓ₀, hsurj, hlt⟩ := hU
    have hmn : m < n + 1 := by
      have h := Fintype.card_le_of_surjective ℓ₀ hsurj
      simp only [Fintype.card_fin] at h; omega
    refine Set.mem_iUnion.mpr ⟨⟨⟨m, hmn⟩, ⟨ℓ₀, hsurj⟩⟩, ?_⟩
    change 2 ^ (KE (lensCode ℓ₀) + KE (lensCode (U • ℓ₀)) + d + 2)
        < Nat.card ↥(orbit (Perm (Fin n)) ℓ₀)
    rwa [show U • ℓ₀ = ℓ₀ ∘ ⇑U⁻¹ from rfl]
  -- (2) union bound: the count is at most the sum of the per-frame counts
  have hUB : B.ncard ≤ ∑ s : SL, (frameSet s).ncard :=
    le_trans (Set.ncard_le_ncard hcover (Set.toFinite _)) (Set.ncard_iUnion_le_of_fintype _)
  -- (3) Kraft over the lens family: ∑ 2^(-KE) ≤ 1
  have minCode_inj : Function.Injective minCode :=
    fun a b h => minCode_E_injective (congrArg E h)
  have hφinj : Function.Injective (fun s : SL => minCode (lensCode s.2.1)) := by
    rintro ⟨k, ℓ, hℓ⟩ ⟨k', ℓ', hℓ'⟩ h
    have hcode : lensCode ℓ = lensCode ℓ' := minCode_inj h
    obtain rfl : k = k' := Fin.ext (lensCode_codomain_of_surjective hℓ hℓ' hcode)
    obtain rfl : ℓ = ℓ' := lensCode_injective hcode
    rfl
  have hkraft : ∑ s : SL, (1 / 2 : ℝ) ^ KE (lensCode s.2.1) ≤ 1 := by
    have hrw : ∀ s : SL, (1 / 2 : ℝ) ^ KE (lensCode s.2.1)
        = (1 / 2 : ℝ) ^ elen (minCode (lensCode s.2.1)) := fun s => by rw [elen_minCode]
    calc ∑ s : SL, (1 / 2 : ℝ) ^ KE (lensCode s.2.1)
          = ∑ s : SL, (1 / 2 : ℝ) ^ elen (minCode (lensCode s.2.1)) := by
            exact Finset.sum_congr rfl fun s _ => hrw s
      _ = ∑ c ∈ (Finset.univ.image fun s : SL => minCode (lensCode s.2.1)),
            (1 / 2 : ℝ) ^ elen c := by
            rw [Finset.sum_image fun x _ y _ h => hφinj h]
      _ ≤ 1 := kraft_sum_le_one _
  -- (4) assemble in ℝ: per-frame bound + Kraft, then clear to ℕ
  have hterm : ∀ s : SL, ((frameSet s).ncard : ℝ)
      ≤ (n ! : ℝ) * (1 / 2 : ℝ) ^ (d + 1) * (1 / 2 : ℝ) ^ KE (lensCode s.2.1) := by
    intro s
    have hnat := collapse_union_frame s.2.1 d
    have hcast : ((frameSet s).ncard : ℝ) * (2 : ℝ) ^ (KE (lensCode s.2.1) + d + 1)
        ≤ (n ! : ℝ) := by
      exact_mod_cast hnat
    rw [show (n ! : ℝ) * (1 / 2 : ℝ) ^ (d + 1) * (1 / 2 : ℝ) ^ KE (lensCode s.2.1)
          = (n ! : ℝ) / (2 : ℝ) ^ (KE (lensCode s.2.1) + d + 1) by
        rw [one_div, inv_pow, inv_pow, mul_assoc, ← mul_inv, ← pow_add, ← div_eq_mul_inv]
        congr 2
        omega]
    rw [le_div_iff₀ (by positivity)]
    exact hcast
  have hsum : ((B.ncard : ℝ)) ≤ (n ! : ℝ) * (1 / 2 : ℝ) ^ (d + 1) := by
    calc ((B.ncard : ℝ)) ≤ ∑ s : SL, ((frameSet s).ncard : ℝ) := by
            exact_mod_cast hUB
      _ ≤ ∑ s : SL, (n ! : ℝ) * (1 / 2 : ℝ) ^ (d + 1) * (1 / 2 : ℝ) ^ KE (lensCode s.2.1) :=
            Finset.sum_le_sum fun s _ => hterm s
      _ = (n ! : ℝ) * (1 / 2 : ℝ) ^ (d + 1)
            * ∑ s : SL, (1 / 2 : ℝ) ^ KE (lensCode s.2.1) := by rw [← Finset.mul_sum]
      _ ≤ (n ! : ℝ) * (1 / 2 : ℝ) ^ (d + 1) * 1 :=
            mul_le_mul_of_nonneg_left hkraft (by positivity)
      _ = (n ! : ℝ) * (1 / 2 : ℝ) ^ (d + 1) := by ring
  -- (5) multiply by 2^d and cast back to ℕ
  have hfinal : ((B.ncard : ℝ)) * (2 : ℝ) ^ d ≤ (n ! : ℝ) := by
    calc ((B.ncard : ℝ)) * (2 : ℝ) ^ d
          ≤ (n ! : ℝ) * (1 / 2 : ℝ) ^ (d + 1) * (2 : ℝ) ^ d :=
            mul_le_mul_of_nonneg_right hsum (by positivity)
      _ = (n ! : ℝ) * (1 / 2 : ℝ) := by
            have h1 : (1 / 2 : ℝ) ^ d * (2 : ℝ) ^ d = 1 := by rw [← mul_pow]; norm_num
            calc (n ! : ℝ) * (1 / 2 : ℝ) ^ (d + 1) * (2 : ℝ) ^ d
                  = (n ! : ℝ) * (1 / 2 : ℝ) * ((1 / 2 : ℝ) ^ d * (2 : ℝ) ^ d) := by
                    rw [pow_succ]; ring
              _ = (n ! : ℝ) * (1 / 2 : ℝ) := by rw [h1]; ring
      _ ≤ (n ! : ℝ) := by nlinarith [Nat.cast_nonneg (α := ℝ) (n !)]
  exact_mod_cast hfinal

/-! ### The entropic capacity ([Persistence] §5, Definition 5.4)

Definition 5.1's capacity counts *labels*, and §5 argues the label count is the wrong currency: a
handful of moving marks is affordable in every world, however complex, and distinguishes almost
nothing. The currency that survives the collapse is the **carried entropy** of the reference frame.
A frame `ℓ₀`'s relabelling class `orbit ℓ₀` has cardinality `N₀ = n ! / ∏ᵢ (fiberᵢ) !`
(`card_orbit_mul_prod_fiber`), and the entropy `E (ℓ₀)` of [Persistence] §2, Definition 2.2 is
`log₂ N₀`.

The object below is valued in `N₀` itself rather than its logarithm — as with `Cb`, the cardinality
form is the machine-checkable one and the `log₂` is applied paper-side. So `CbH U b` is the paper's
`2 ^ (C_b^H (U))`, and the cap `CbH_collapse` below — no world outside a `2 ^ (-d)` fraction has
`2 ^ (2 * b + d + 2) < CbH U b` — reads `C_b^H (U) ≤ 2 * b + d + 2`, which is Corollary 7.4's
`C_b^H (U) ≤ 2 * b + d + O (1)` with the `O (1)` pinned at `2`. Taking the supremum before the
logarithm loses nothing: `log₂` is monotone and the family of values is finite. -/

/-- The **carried entropies affordable at budget `b`**: the relabelling-class sizes
`N₀ = Nat.card (orbit ℓ₀)` of the reference frames `ℓ₀ = ℓ 0` of those families that carry a
persistent model over `U` at a per-frame cost of `b` bits. The label count is not fixed — the
maximum of [Persistence] §5, Definition 5.4 ranges over families carrying a model of any size. -/
def BudgetedEntropies (U : Perm (Fin n)) (b : ℕ) : Set ℕ :=
  {N : ℕ | ∃ k : ℕ, ∃ ℓ : ℕ → Fin n → Fin k, PermCarries U ℓ ∧ PermBudget ℓ b ∧
      N = Nat.card ↥(orbit (Perm (Fin n)) (ℓ 0))}

/-- **The entropic budgeted capacity** ([Persistence] §5, Definition 5.4) over a permutation world —
§7's setting, where the world is its own recurrent core — in cardinality form: the largest carried
entropy, as the relabelling-class size `2 ^ E` (see above), of a reference frame whose family costs
at most `b` bits per frame. `sSup ∅ = 0`: a budget that affords no family at all carries nothing. -/
noncomputable def CbH (U : Perm (Fin n)) (b : ℕ) : ℕ := sSup (BudgetedEntropies U b)

/-- No reading distinguishes more than the world has to offer: a relabelling class is a set of
lenses reachable from one another by permutations, so its size is at most `n !`
(`card_orbit_mul_prod_fiber`, the fiber product being at least one). This is what makes the
supremum well-defined. -/
private theorem budgetedEntropies_le {U : Perm (Fin n)} {b N : ℕ} (h : N ∈ BudgetedEntropies U b) :
    N ≤ n ! := by
  obtain ⟨k, ℓ, -, -, rfl⟩ := h
  have hprod : 0 < ∏ i : Fin k, (Nat.card {x : Fin n // ℓ 0 x = i})! :=
    Finset.prod_pos fun i _ => Nat.factorial_pos _
  exact card_orbit_mul_prod_fiber (ℓ 0) ▸ Nat.le_mul_of_pos_right _ hprod

private theorem bddAbove_budgetedEntropies (U : Perm (Fin n)) (b : ℕ) :
    BddAbove (BudgetedEntropies U b) :=
  ⟨n !, fun _ h => budgetedEntropies_le h⟩

/-- **The entropic capacity never exceeds a faithful reading** ([Persistence] §5): `log₂ n !` is the
entropy of a bijective frame, and no budget buys more. -/
theorem CbH_le_factorial (U : Perm (Fin n)) (b : ℕ) : CbH U b ≤ n ! := by
  rcases Set.eq_empty_or_nonempty (BudgetedEntropies U b) with hemp | hne
  · simp [CbH, hemp]
  · exact csSup_le hne fun _ h => budgetedEntropies_le h

/-- More budget never hurts: `CbH` is monotone (the `Cb_mono` of the entropic currency). -/
theorem CbH_mono (U : Perm (Fin n)) {b₁ b₂ : ℕ} (h : b₁ ≤ b₂) : CbH U b₁ ≤ CbH U b₂ :=
  csSup_le_csSup' (bddAbove_budgetedEntropies U b₂) (by
    rintro N ⟨k, ℓ, hcar, hbud, rfl⟩
    exact ⟨k, ℓ, hcar, fun t => (hbud t).trans h, rfl⟩)

/-- **The entropic capacity is generically pinned at `2b + d + O (1)`** ([Persistence] §7,
Corollary 7.5(i), the cap; the `O (1)` is `2`). For every `d`, the worlds whose entropic capacity at
budget `b` exceeds `2 * b + d + 2` — i.e. `2 ^ (2 * b + d + 2) < CbH U b`, the division-free reading
of `C_b^H (U) > 2 * b + d + 2` — number at most `n ! / 2 ^ d`, a `2 ^ (-d)` fraction of the worlds.

**An observer keeps, to within a factor two, exactly the entropy it pays for**: there are no
discounts, generically.

The proof is `collapse_union` plus the observation that the supremum is attained. A world with
`2 ^ (2 * b + d + 2) < CbH U b` has an actual budget-`b` family realizing that entropy
(`Nat.sSup_mem`); its reference frame is surjective, and the family's second frame is *determined*
as `ℓ₀ ∘ U⁻¹` (`permCarries_frame_one`), so the two frames cost at most `b` each — putting the world
in the Kraft union's exceptional set, which `collapse_union` has already counted. The budget
hypothesis is consumed at `t = 0` and `t = 1` only. -/
theorem CbH_collapse (b d : ℕ) :
    {U : Perm (Fin n) | 2 ^ (2 * b + d + 2) < CbH U b}.ncard * 2 ^ d ≤ n ! := by
  refine le_trans (Nat.mul_le_mul_right _ (Set.ncard_le_ncard ?_ (Set.toFinite _)))
    (collapse_union d)
  intro U hU
  have hlt : 2 ^ (2 * b + d + 2) < CbH U b := hU
  have hne : (BudgetedEntropies U b).Nonempty := by
    by_contra hcon
    rw [Set.not_nonempty_iff_eq_empty] at hcon
    rw [CbH, hcon, csSup_empty] at hlt
    exact absurd hlt (Nat.not_lt_zero _)
  obtain ⟨k, ℓ, hcar, hbud, hval⟩ : CbH U b ∈ BudgetedEntropies U b :=
    Nat.sSup_mem hne (bddAbove_budgetedEntropies U b)
  refine ⟨k, ℓ 0, hcar.1, ?_⟩
  have h1 : ℓ 1 = U • ℓ 0 := permCarries_frame_one hcar.2
  have hb0 := hbud 0
  have hb1 := hbud 1
  rw [h1, show U • ℓ 0 = ℓ 0 ∘ ⇑U⁻¹ from rfl] at hb1
  calc 2 ^ (KE (lensCode (ℓ 0)) + KE (lensCode (ℓ 0 ∘ ⇑U⁻¹)) + d + 2)
      ≤ 2 ^ (2 * b + d + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
    _ < Nat.card ↥(orbit (Perm (Fin n)) (ℓ 0)) := hval ▸ hlt

/-- **No every-world entropic floor exceeds `2b + 3`** ([Persistence] §7, Corollary 7.5(i), and
§12.2's optimality open). Corollary 7.5(i)'s floor `(1/2 − o(1)) · b` holds over *every*
permutation world, while its cap `2b + d + 2` (`CbH_collapse`) is generic, not universal. This is
the other bound: some world's entropic capacity sits at or below `2 ^ (2 * b + 3)`, one line from
`CbH_collapse` at `d = 1` — the exceeding worlds number at most half of `n !`, so the complement is
inhabited, with no side condition (`n = 0` included). So no floor holding over every world can
exceed `2b + 3`. -/
theorem exists_perm_CbH_le (b : ℕ) : ∃ U : Perm (Fin n), CbH U b ≤ 2 ^ (2 * b + 3) := by
  by_contra hcon
  push Not at hcon
  have huniv : {U : Perm (Fin n) | 2 ^ (2 * b + 1 + 2) < CbH U b} = Set.univ :=
    Set.eq_univ_of_forall hcon
  have hcollapse := CbH_collapse (n := n) b 1
  rw [huniv, Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_perm,
    Fintype.card_fin] at hcollapse
  have hpos := Nat.factorial_pos n
  omega

/-! ### The marking floor ([Persistence] §5, Proposition 5.3)

The cap above is one side of Corollary 7.5(i); this is the other. Mark `r` distinguished points of
the world, sending `x j` to the label `j + 1` and everything else to `0`, and let the marks *ride
the world*: `ℓ t := ℓ₀ ∘ (U ^ t)⁻¹`. Persistence is immediate, and the construction needs no
genericity — it runs over **every** permutation world, however complex the rule.

What the marks carry is exactly computed: the profile is `(n − r, 1, …, 1)`, so the reference
frame's relabelling class has `n ! / (n − r)!` elements (`prod_fiber_marking`) and the carried
entropy is `log₂ (n ! / (n − r)!) ≈ r · log₂ n` — a floor on `CbH` as soon as the budget affords the
family (`CbH_ge_marking`).

Proposition 5.3's own content is the *price* of that family: each frame's table is "the current
positions `U ^ t (x j)`, each with its label, else `0`", which an explicit program loads in
`O (r · log₂ n)` bits. That price is proved below (`KE_markingLens_le`), and `smul_markingLens` is
what makes one such bound suffice for the whole family: every frame of the family *is* a marking
lens, with the marks moved along, so the price is uniform in `t` by construction rather than by
estimate. The floor consuming it is `CbH_ge_marking'`. -/

/-- The **marking lens** ([Persistence] §5, Proposition 5.3): `r` distinguished points `x 0, …,
x (r−1)` are read as the labels `1, …, r`, and every other state is read as `0`. Definitionally the
cheapest nontrivial reading — it distinguishes a handful of points and nothing else. -/
noncomputable def markingLens {r : ℕ} (x : Fin r → Fin n) (i : Fin n) : Fin (r + 1) :=
  if h : ∃ j, x j = i then h.choose.succ else 0

/-- A marked point is read as its own label. -/
private theorem markingLens_mark {r : ℕ} {x : Fin r → Fin n} (hx : Function.Injective x)
    (j : Fin r) : markingLens x (x j) = j.succ := by
  have h : ∃ j', x j' = x j := ⟨j, rfl⟩
  rw [markingLens, dif_pos h]
  exact congrArg Fin.succ (hx h.choose_spec)

/-- An unmarked point is read as `0`. -/
private theorem markingLens_unmark {r : ℕ} {x : Fin r → Fin n} {i : Fin n} (h : ¬∃ j, x j = i) :
    markingLens x i = 0 := by
  rw [markingLens, dif_neg h]

/-- Only the marked points carry labels: reading `j + 1` identifies the state as `x j`. -/
private theorem markingLens_eq_succ_iff {r : ℕ} {x : Fin r → Fin n} (hx : Function.Injective x)
    {i : Fin n} {j : Fin r} : markingLens x i = j.succ ↔ x j = i := by
  constructor
  · intro h
    by_cases hex : ∃ j', x j' = i
    · rw [markingLens, dif_pos hex] at h
      rw [← Fin.succ_injective _ h]
      exact hex.choose_spec
    · rw [markingLens_unmark hex] at h
      exact absurd h.symm (Fin.succ_ne_zero j)
  · rintro rfl
    exact markingLens_mark hx j

/-- The `0`-fiber of the marking lens is everything unmarked: `n − r` states. -/
private theorem card_fiber_marking_zero {r : ℕ} {x : Fin r → Fin n} (hx : Function.Injective x) :
    Nat.card {i : Fin n // markingLens x i = 0} = n - r := by
  classical
  have hset : ∀ i : Fin n, markingLens x i = 0 ↔ i ∉ Set.range x := by
    intro i
    constructor
    · rintro h ⟨j, rfl⟩
      exact absurd ((markingLens_mark hx j).symm.trans h) (Fin.succ_ne_zero j)
    · intro h
      exact markingLens_unmark fun hex => h hex
  have hcong : {i : Fin n // markingLens x i = 0} = {i : Fin n // i ∉ Set.range x} := by
    congr 1
    ext i
    exact hset i
  rw [hcong, Nat.card_eq_fintype_card, Fintype.card_subtype_compl, ← Nat.card_eq_fintype_card,
    ← Nat.card_eq_fintype_card, Nat.card_range_of_injective hx]
  simp

/-- The marking lens is **surjective** as soon as one point is left unmarked: the marks supply the
labels `1, …, r`, and the `n − r` unmarked states supply `0`. -/
private theorem markingLens_surjective {r : ℕ} {x : Fin r → Fin n} (hx : Function.Injective x)
    (hrn : r < n) : Function.Surjective (markingLens x) := by
  intro l
  induction l using Fin.cases with
  | zero =>
      have hpos : 0 < Nat.card {i : Fin n // markingLens x i = 0} := by
        rw [card_fiber_marking_zero hx]; omega
      obtain ⟨⟨i, hi⟩⟩ := (Nat.card_pos_iff.mp hpos).1
      exact ⟨i, hi⟩
  | succ j => exact ⟨x j, markingLens_mark hx j⟩

/-- Each label `j + 1` is carried by exactly one state — the mark `x j`. -/
private theorem card_fiber_marking_succ {r : ℕ} {x : Fin r → Fin n} (hx : Function.Injective x)
    (j : Fin r) : Nat.card {i : Fin n // markingLens x i = j.succ} = 1 := by
  rw [Nat.card_eq_one_iff_unique]
  refine ⟨⟨fun a b => ?_⟩, ⟨⟨x j, markingLens_mark hx j⟩⟩⟩
  have ha : x j = (a : Fin n) := (markingLens_eq_succ_iff hx).mp a.2
  have hb : x j = (b : Fin n) := (markingLens_eq_succ_iff hx).mp b.2
  exact Subtype.ext (ha ▸ hb)

/-- **The marking lens's profile** ([Persistence] §5, Proposition 5.3): fiber sizes `(n − r, 1, …,
1)`, so the fiber product — the size of each relabelling coset — is `(n − r)!`. With
`card_orbit_mul_prod_fiber` this pins the carried entropy at `log₂ (n ! / (n − r)!)` exactly. -/
theorem prod_fiber_marking {r : ℕ} {x : Fin r → Fin n} (hx : Function.Injective x) :
    ∏ l : Fin (r + 1), (Nat.card {i : Fin n // markingLens x i = l})! = (n - r)! := by
  rw [Fin.prod_univ_succ, card_fiber_marking_zero hx]
  have hone : ∀ j : Fin r, (Nat.card {i : Fin n // markingLens x i = j.succ})! = 1 := by
    intro j
    rw [card_fiber_marking_succ hx j]
    rfl
  rw [Finset.prod_congr rfl fun j _ => hone j]
  simp

/-- **Every frame of the marking family is itself a marking lens** — with the marks moved along:
`U • markingLens x = markingLens (U ∘ x)`. This is what "the marks ride the world" means
tabulation-side, and it is why the family's price does not drift with `t`: each frame is the *same
kind of object*, `r` marks on `n` states, differing only in where the marks sit. Proposition 5.3's
per-frame bound is therefore one bound, uniform over the marks — not a bound per time step.

Injectivity is needed: it is what makes the label of a marked point unambiguous on both sides. -/
theorem smul_markingLens {r : ℕ} {x : Fin r → Fin n} (hx : Function.Injective x)
    (U : Perm (Fin n)) : U • markingLens x = markingLens (⇑U ∘ x) := by
  have hUx : Function.Injective (⇑U ∘ x) := U.injective.comp hx
  funext i
  rw [smul_lens_apply]
  by_cases hex : ∃ j, (⇑U ∘ x) j = i
  · obtain ⟨j, hj⟩ := hex
    have hxj : x j = U⁻¹ i := by
      rw [← hj]
      simp
    rw [← hxj, markingLens_mark hx j, ← hj, markingLens_mark hUx j]
  · rw [markingLens_unmark hex, markingLens_unmark]
    rintro ⟨j, hj⟩
    exact hex ⟨j, by simp [hj]⟩

/-- **The marks ride the world** ([Persistence] §5, Proposition 5.3, the persistence half): the
family `ℓ t := ℓ₀ ∘ (U ^ t)⁻¹` carries a persistent model over **every** permutation world. Reading
through the time-`t` frame after `t` steps returns the time-`0` reading, by construction — no
genericity, no maximality, no hypothesis on `U` at all. -/
theorem markCarries {r : ℕ} {U : Perm (Fin n)} {x : Fin r → Fin n} (hx : Function.Injective x)
    (hrn : r < n) : PermCarries U (fun t => (U ^ t) • markingLens x) := by
  constructor
  · simpa using markingLens_surjective hx hrn
  · intro t i
    change markingLens x ((U ^ t)⁻¹ ((U ^ t) i)) = markingLens x ((U ^ 0)⁻¹ i)
    simp

/-- **The marking floor** ([Persistence] §5, Proposition 5.3 + §7, Corollary 7.5(i), the floor).
Over **every** permutation world, a budget that affords the marking family carries entropy
`log₂ (n ! / (n − r)!)` — stated division-free as `n ! ≤ CbH U b * (n − r)!`.

The price enters as the hypothesis `hprice`: **`r` marks on `n` states cost at most `b` bits to
tabulate**, uniformly over where the marks sit. That is exactly Proposition 5.3's own claim
(`(2 ^ κ − 1) · (⌈log₂ n⌉ + κ) + O (1)` bits, "for every `t`"), and `smul_markingLens` is what makes
one such bound cover every frame: each frame *is* a marking lens, with the marks moved along.

This is the general form, taking any price bound whatever. `KE_markingLens_le` proves one, and
`CbH_ge_marking'` is the resulting unconditional floor.

Corollary 7.5(i)'s asymptotic `C_b^H (U) ≥ (1/2 − o(1)) · b` — choose the largest affordable `r` and
compare `log₂ (n ! / (n − r)!) ≥ r · (log₂ n − 1)` against the price — is the paper-level conversion
of this exact floor. -/
theorem CbH_ge_marking {r : ℕ} {U : Perm (Fin n)} {x : Fin r → Fin n} (hx : Function.Injective x)
    (hrn : r < n) {b : ℕ}
    (hprice : ∀ y : Fin r → Fin n, Function.Injective y → KE (lensCode (markingLens y)) ≤ b) :
    n ! ≤ CbH U b * (n - r)! := by
  have hb : ∀ t, KE (lensCode ((U ^ t) • markingLens x)) ≤ b := fun t => by
    rw [smul_markingLens hx (U ^ t)]
    exact hprice _ ((U ^ t).injective.comp hx)
  have hmem : Nat.card ↥(orbit (Perm (Fin n)) (markingLens x)) ∈ BudgetedEntropies U b :=
    ⟨r + 1, fun t => (U ^ t) • markingLens x, markCarries hx hrn, hb, by simp⟩
  have hle : Nat.card ↥(orbit (Perm (Fin n)) (markingLens x)) ≤ CbH U b :=
    le_csSup (bddAbove_budgetedEntropies U b) hmem
  calc n ! = Nat.card ↥(orbit (Perm (Fin n)) (markingLens x))
        * ∏ l : Fin (r + 1), (Nat.card {i : Fin n // markingLens x i = l})! :=
        (card_orbit_mul_prod_fiber (markingLens x)).symm
    _ = Nat.card ↥(orbit (Perm (Fin n)) (markingLens x)) * (n - r)! := by
        rw [prod_fiber_marking hx]
    _ ≤ CbH U b * (n - r)! := Nat.mul_le_mul_right _ hle

/-! ## The price of the marking family

Proposition 5.3's own content — "`r` marks on `n` states cost `O (r · log₂ n)` bits to tabulate,
uniformly over where the marks sit" — proved as an explicit code, discharging `CbH_ge_marking`'s
`hprice`.

The route is forced by the additive carrier. The marks are packed as the **base-`n` numeral**
`∑ⱼ (x j) · n ^ j` (`packMarks`), whose bit-length is `r · ⌈log₂ n⌉`; the `Encodable` list encoding
would pair at every cons and cost `2 ^ r`. That numeral, together with `n` and `r`, is loaded as a
single `Nat.pair`-packed program by the binary constant `bconst`, whose additive length is
`O (Nat.size p)` rather than `Θ (p)`, and fed to **one fixed table-builder** (`markBuilder`), which
is independent of `n`, `r`, and the marks — the uniform-constant discipline of `ledger_K`. The
builder's output value is astronomically large; that is irrelevant, since `KE` prices the program,
not the value.

The machine bound prices **positions only**, the labels being implicit in the digit order — slightly
*stronger* than the display of [Persistence] §5, Proposition 5.3, which pays
`(2 ^ κ − 1) · (⌈log₂ n⌉ + κ) + O (1)` for positions and labels together. -/

/-- The `j`-th digit of the packed marks: the `j`-th mark's position, or `0` past the last mark. -/
def markDigit {r : ℕ} (x : Fin r → Fin n) (j : ℕ) : ℕ := if h : j < r then (x ⟨j, h⟩ : ℕ) else 0

/-- **The marks packed as a base-`n` numeral** ([Persistence] §5, Proposition 5.3, the price). Its
bit-length is `r · ⌈log₂ n⌉`, against the `2 ^ r` of an `Encodable` list of positions. -/
def packMarks {r : ℕ} (x : Fin r → Fin n) : ℕ := ∑ j ∈ Finset.range r, markDigit x j * n ^ j

/-- Every digit is a position, hence `< n`. -/
private theorem markDigit_lt {r : ℕ} (hn : 0 < n) (x : Fin r → Fin n) (j : ℕ) :
    markDigit x j < n := by
  unfold markDigit; split
  · exact (x _).2
  · exact hn

/-- An `r`-digit base-`n` numeral is `< n ^ r`. -/
private theorem sum_digits_lt (d : ℕ → ℕ) (hd : ∀ j, d j < n) :
    ∀ r : ℕ, (∑ j ∈ Finset.range r, d j * n ^ j) < n ^ r := by
  intro r
  induction r with
  | zero => simp
  | succ r ih =>
    rw [Finset.sum_range_succ, pow_succ]
    calc (∑ j ∈ Finset.range r, d j * n ^ j) + d r * n ^ r
        < n ^ r + d r * n ^ r := by omega
      _ = (d r + 1) * n ^ r := by ring
      _ ≤ n * n ^ r := Nat.mul_le_mul_right _ (by have := hd r; omega)
      _ = n ^ r * n := by ring

/-- Base-`n` digit extraction: dividing out the lower digits and reducing mod `n` returns `d k`.
Induction on the digit count, peeling the low digit via `S = d 0 + n · S'`. -/
private theorem sum_digits_div_mod (hn : 0 < n) :
    ∀ (r : ℕ) (d : ℕ → ℕ), (∀ j, d j < n) → ∀ k, k < r →
      (∑ j ∈ Finset.range r, d j * n ^ j) / n ^ k % n = d k := by
  intro r
  induction r with
  | zero => intro d hd k hk; omega
  | succ r ih =>
    intro d hd k hk
    have hpeel : (∑ j ∈ Finset.range (r + 1), d j * n ^ j)
        = d 0 + n * ∑ j ∈ Finset.range r, d (j + 1) * n ^ j := by
      rw [Finset.sum_range_succ']
      simp only [pow_zero, mul_one, pow_succ, Finset.mul_sum]
      ring_nf
      rw [Nat.add_comm]
      congr 1
      exact Finset.sum_congr rfl fun j _ => by ring
    match k with
    | 0 =>
      rw [hpeel, pow_zero, Nat.div_one, Nat.add_mul_mod_self_left]
      exact Nat.mod_eq_of_lt (hd 0)
    | (k + 1) =>
      have hrec : (∑ j ∈ Finset.range (r + 1), d j * n ^ j) / n
          = ∑ j ∈ Finset.range r, d (j + 1) * n ^ j := by
        rw [hpeel, Nat.add_mul_div_left _ _ hn, Nat.div_eq_of_lt (hd 0), Nat.zero_add]
      have hsplit : (∑ j ∈ Finset.range (r + 1), d j * n ^ j) / n ^ (k + 1)
          = ((∑ j ∈ Finset.range (r + 1), d j * n ^ j) / n) / n ^ k := by
        rw [Nat.div_div_eq_div_mul, ← pow_succ']
      rw [hsplit, hrec]
      exact ih (fun j => d (j + 1)) (fun j => hd (j + 1)) k (by omega)

/-- **The packing is faithful**: the numeral's `k`-th base-`n` digit is the `k`-th mark. -/
theorem digit_packMarks (hn : 0 < n) {r : ℕ} (x : Fin r → Fin n) (k : Fin r) :
    packMarks x / n ^ (k : ℕ) % n = (x k : ℕ) := by
  rw [packMarks, sum_digits_div_mod hn r (markDigit x) (markDigit_lt hn x) k k.2]
  unfold markDigit
  rw [dif_pos k.2]

/-- The packing fits in `r` base-`n` digits. -/
private theorem packMarks_lt (hn : 0 < n) {r : ℕ} (x : Fin r → Fin n) : packMarks x < n ^ r :=
  sum_digits_lt _ (markDigit_lt hn x) r

/-- **The packing costs `r · Nat.size n` bits** — linear in `r`, against the `Encodable` list
encoding's `2 ^ r`. This is the whole reason for the numeral. -/
theorem size_packMarks_le (hn : 0 < n) {r : ℕ} (x : Fin r → Fin n) :
    Nat.size (packMarks x) ≤ r * Nat.size n := by
  rw [Nat.size_le]
  calc packMarks x < n ^ r := packMarks_lt hn x
    _ ≤ (2 ^ Nat.size n) ^ r := Nat.pow_le_pow_left (le_of_lt (Nat.lt_size_self n)) r
    _ = 2 ^ (r * Nat.size n) := by rw [← pow_mul, Nat.mul_comm]

private theorem pair_lt_sq (a b : ℕ) : Nat.pair a b < (a + b + 1) ^ 2 := by
  rw [Nat.pair]
  split
  · next h => nlinarith
  · next h => nlinarith [Nat.not_lt.mp h]

/-- **Pairing costs a constant factor in bits**: `Nat.pair` squares the value, hence doubles the
bit-length, up to an additive constant. The bookkeeping that keeps the packed program
logarithmic. -/
private theorem size_pair_le (a b : ℕ) :
    Nat.size (Nat.pair a b) ≤ 2 * (Nat.size a + Nat.size b) + 2 := by
  have hs : Nat.size (a + b + 1) ≤ Nat.size a + Nat.size b + 1 := by
    rw [Nat.size_le]
    have ha := Nat.lt_size_self a
    have hb := Nat.lt_size_self b
    calc a + b + 1 < 2 ^ Nat.size a + 2 ^ Nat.size b := by omega
      _ ≤ 2 ^ (Nat.size a + Nat.size b) + 2 ^ (Nat.size a + Nat.size b) := by
          have h1 : (2 : ℕ) ^ Nat.size a ≤ 2 ^ (Nat.size a + Nat.size b) :=
            Nat.pow_le_pow_right (by norm_num) (by omega)
          have h2 : (2 : ℕ) ^ Nat.size b ≤ 2 ^ (Nat.size a + Nat.size b) :=
            Nat.pow_le_pow_right (by norm_num) (by omega)
          omega
      _ = 2 ^ (Nat.size a + Nat.size b + 1) := by ring
  rw [Nat.size_le]
  calc Nat.pair a b < (a + b + 1) ^ 2 := pair_lt_sq a b
    _ < (2 ^ Nat.size (a + b + 1)) ^ 2 := Nat.pow_lt_pow_left (Nat.lt_size_self _) (by norm_num)
    _ = 2 ^ (2 * Nat.size (a + b + 1)) := by rw [← pow_mul, Nat.mul_comm]
    _ ≤ 2 ^ (2 * (Nat.size a + Nat.size b) + 2) := by
        apply Nat.pow_le_pow_right (by norm_num); omega

/-- The `j`-th base-`n` digit of `v`, at the level the builder works: plain arithmetic on `ℕ`. -/
private def digitAt (n v j : ℕ) : ℕ := v / n ^ j % n

/-- The label the marking lens assigns to state `i`, read off the packed marks: the index of the
mark sitting at `i`, plus one, or `0` if none does. The sum is a bounded search — under injectivity
at most one term survives. -/
private def markVal (n r v i : ℕ) : ℕ :=
  ((List.range r).map fun j => if digitAt n v j = i then j + 1 else 0).sum

/-- **The tabulation, rebuilt from the packed program `⟨n, r, v⟩`** — ONE fixed function of a single
natural number, carrying no dependence on `n`, `r`, or the marks. -/
private def markTableFn (a : ℕ) : ℕ :=
  Encodable.encode ((List.range a.unpair.1).map
    (markVal a.unpair.1 a.unpair.2.unpair.1 a.unpair.2.unpair.2))

private theorem markVal_eq_sum (n r v i : ℕ) :
    markVal n r v i = ∑ j ∈ Finset.range r, (if digitAt n v j = i then j + 1 else 0) := by
  rw [markVal]; simp [Finset.sum, Multiset.range]

/-- **The builder reads the marking lens back off the numeral.** Injectivity is what collapses the
bounded search to a single term: at most one mark sits at any given state. -/
private theorem markVal_eq (hn : 0 < n) {r : ℕ} {x : Fin r → Fin n} (hx : Function.Injective x)
    (i : Fin n) : markVal n r (packMarks x) (i : ℕ) = (markingLens x i : ℕ) := by
  rw [markVal_eq_sum]
  -- the test at index `j < r` fires exactly when the `j`-th mark sits at `i`
  have htest : ∀ (j : ℕ) (hj : j < r),
      (digitAt n (packMarks x) j = (i : ℕ)) ↔ x ⟨j, hj⟩ = i := by
    intro j hj
    rw [show digitAt n (packMarks x) j = (x ⟨j, hj⟩ : ℕ) from digit_packMarks hn x ⟨j, hj⟩]
    exact ⟨fun h => Fin.val_injective h, fun h => congrArg Fin.val h⟩
  by_cases hex : ∃ k : Fin r, x k = i
  · -- marked: injectivity leaves exactly one surviving term
    obtain ⟨k, hk⟩ := hex
    have hml : (markingLens x i : ℕ) = (k : ℕ) + 1 := by
      rw [← hk, markingLens_mark hx k]; simp
    have hc : digitAt n (packMarks x) (k : ℕ) = (i : ℕ) := by
      rw [htest (k : ℕ) k.2, Fin.eta]; exact hk
    have h0 : ∀ j ∈ Finset.range r, j ≠ (k : ℕ) →
        (if digitAt n (packMarks x) j = (i : ℕ) then j + 1 else 0) = 0 := by
      intro j hj hjk
      rw [Finset.mem_range] at hj
      have hnc : ¬(digitAt n (packMarks x) j = (i : ℕ)) := by
        rw [htest j hj]
        exact fun hcontra => hjk (congrArg Fin.val (hx (hcontra.trans hk.symm)))
      rw [if_neg hnc]
    have h1 : (k : ℕ) ∉ Finset.range r →
        (if digitAt n (packMarks x) (k : ℕ) = (i : ℕ) then (k : ℕ) + 1 else 0) = 0 :=
      fun hk' => absurd (Finset.mem_range.mpr k.2) hk'
    rw [Finset.sum_eq_single (k : ℕ) h0 h1, if_pos hc, hml]
  · -- unmarked: every term vanishes
    rw [markingLens_unmark hex, Fin.val_zero]
    refine Finset.sum_eq_zero fun j hj => ?_
    rw [Finset.mem_range] at hj
    have hnc : ¬(digitAt n (packMarks x) j = (i : ℕ)) := by
      rw [htest j hj]
      exact fun hcontra => hex ⟨⟨j, hj⟩, hcontra⟩
    rw [if_neg hnc]

/-- **The builder is correct**: on the packed program `⟨n, r, packMarks x⟩` it outputs exactly the
marking lens's encoded tabulation — the very number whose `KE` is the frame's price. -/
private theorem markTableFn_eq (hn : 0 < n) {r : ℕ} {x : Fin r → Fin n}
    (hx : Function.Injective x) :
    markTableFn (Nat.pair n (Nat.pair r (packMarks x))) = lensCode (markingLens x) := by
  rw [markTableFn, lensCode, lensTable]
  simp only [Nat.unpair_pair]
  congr 1
  have hfr : (List.finRange n).map Fin.val = List.range n := by simp
  rw [← hfr, List.map_map]
  exact List.map_congr_left fun i _ => markVal_eq hn hx i

/-- Summing a primitive-recursive list of naturals is primitive recursive (`List.sum` as a
`foldr`). -/
private theorem primrec_list_sum {α : Type*} [Primcodable α] {f : α → List ℕ} (hf : Primrec f) :
    Primrec fun a => (f a).sum :=
  (Primrec.list_foldr hf (Primrec.const 0)
      (Primrec.nat_add.comp (Primrec.fst.comp Primrec.snd)
        (Primrec.snd.comp Primrec.snd)).to₂).of_eq
    fun a => by simp [List.sum_eq_foldr]

/-- **The builder is primitive recursive.** Digit extraction is `/`, `^`, `%`; the mark's index is a
bounded search over `List.range r`; the tabulation is a `List.map` over `List.range n`. -/
private theorem primrec_markTableFn : Primrec markTableFn := by
  have hN : Primrec fun a : ℕ => a.unpair.1 := Primrec.fst.comp Primrec.unpair
  have hRV : Primrec fun a : ℕ => a.unpair.2 := Primrec.snd.comp Primrec.unpair
  have hR : Primrec fun a : ℕ => a.unpair.2.unpair.1 := Primrec.fst.comp (Primrec.unpair.comp hRV)
  have hV : Primrec fun a : ℕ => a.unpair.2.unpair.2 := Primrec.snd.comp (Primrec.unpair.comp hRV)
  have hpow : Primrec₂ ((· ^ ·) : ℕ → ℕ → ℕ) := Primrec₂.unpaired'.1 Nat.Primrec.pow
  -- the digit test, over `q : (ℕ × ℕ) × ℕ` — `q.1.1` the program, `q.1.2` the state, `q.2` the mark
  have hinner : Primrec₂ fun (p : ℕ × ℕ) (j : ℕ) =>
      if digitAt p.1.unpair.1 p.1.unpair.2.unpair.2 j = p.2 then j + 1 else 0 := by
    have ha : Primrec fun q : (ℕ × ℕ) × ℕ => q.1.1 := Primrec.fst.comp Primrec.fst
    have hdig : Primrec fun q : (ℕ × ℕ) × ℕ =>
        digitAt q.1.1.unpair.1 q.1.1.unpair.2.unpair.2 q.2 :=
      Primrec.nat_mod.comp
        (Primrec.nat_div.comp (hV.comp ha) (hpow.comp (hN.comp ha) Primrec.snd))
        (hN.comp ha)
    exact (Primrec.ite (PrimrecRel.comp Primrec.eq hdig (Primrec.snd.comp Primrec.fst))
      (Primrec.succ.comp Primrec.snd) (Primrec.const 0)).to₂
  -- the label at one state
  have hmarkVal : Primrec₂ fun (a : ℕ) (i : ℕ) =>
      markVal a.unpair.1 a.unpair.2.unpair.1 a.unpair.2.unpair.2 i :=
    (primrec_list_sum (f := fun p : ℕ × ℕ =>
        (List.range p.1.unpair.2.unpair.1).map fun j =>
          if digitAt p.1.unpair.1 p.1.unpair.2.unpair.2 j = p.2 then j + 1 else 0)
      (Primrec.list_map (Primrec.list_range.comp (hR.comp Primrec.fst)) hinner)).to₂
  exact Primrec.encode.comp (Primrec.list_map (Primrec.list_range.comp hN) hmarkVal)

private theorem partrec_markTableFn : Nat.Partrec (fun a : ℕ => (markTableFn a : ℕ)) :=
  _root_.Partrec.nat_iff.mp (Primrec.to_comp primrec_markTableFn).partrec

/-- **The fixed table-builder code.** Extracted from universality, it takes no parameters: one
program, independent of `n`, `r`, and where the marks sit — the uniform constant `ledger_K`'s
discipline demands, and what makes the price below a single bound covering every frame. -/
noncomputable def markBuilder : Nat.Partrec.Code :=
  Classical.choose (Nat.Partrec.Code.exists_code.mp partrec_markTableFn)

/-- The builder's evaluation law. -/
private theorem eval_markBuilder (a : ℕ) :
    Nat.Partrec.Code.eval markBuilder a = Part.some (markTableFn a) := by
  have h := congrFun (Classical.choose_spec
    (Nat.Partrec.Code.exists_code.mp partrec_markTableFn)) a
  simpa [markBuilder] using h

/-- **The marking lens's explicit price** ([Persistence] §5, Proposition 5.3, the cost bound):
`r` marks on `n` states are tabulated by a program of length
`6 · κ · (r + 1) · Nat.size n + O (1)`, with `κ = 15 + elen dbl` and the additive constant
`elen markBuilder + 7 · κ + 3` — both absolute, fixed once and for all.

The bound is **uniform over the marks**: `x` occurs only on the left. That is exactly the quantifier
`CbH_ge_marking`'s `hprice` needs, and with `smul_markingLens` — every frame is itself a marking
lens, with the marks moved along — one such bound prices the whole family, at every `t`.

Assembly: `comp markBuilder (bconst ⟨n, r, packMarks x⟩)`. The marks ride in a base-`n` numeral of
`r · Nat.size n` bits (`size_packMarks_le`), `Nat.pair` costs a constant factor (`size_pair_le`),
`bconst` loads the packed program in `O (Nat.size p)` rather than `Θ (p)` (`elen_bconst_le`), and
`invariance_general` charges the fixed builder once.

Taking `r + 1 = 2 ^ κ ≤ n / 2` this is the proposition's `c₁ · 2 ^ κ · log₂ n`. It prices positions
only — the labels are implicit in the digit order — where the paper's display pays
`(2 ^ κ − 1) · (⌈log₂ n⌉ + κ) + O (1)` for both. -/
theorem KE_markingLens_le {r : ℕ} (hrn : r < n) {x : Fin r → Fin n}
    (hx : Function.Injective x) :
    KE (lensCode (markingLens x))
      ≤ 6 * (15 + elen dbl) * ((r + 1) * Nat.size n)
        + (elen markBuilder + 7 * (15 + elen dbl) + 3) := by
  have hn : 0 < n := by omega
  have heval : Nat.Partrec.Code.eval markBuilder (Nat.pair n (Nat.pair r (packMarks x)))
      = Part.some (lensCode (markingLens x)) := by
    rw [eval_markBuilder, markTableFn_eq hn hx]
  have hinv := invariance_general markBuilder (Nat.pair n (Nat.pair r (packMarks x))) _ heval
  -- the packed program is `O ((r + 1) · Nat.size n)` bits
  have hsr : Nat.size r ≤ Nat.size n := Nat.size_le_size (le_of_lt hrn)
  have hsv : Nat.size (packMarks x) ≤ r * Nat.size n := size_packMarks_le hn x
  have h1 : Nat.size (Nat.pair r (packMarks x)) ≤ 2 * ((r + 1) * Nat.size n) + 2 := by
    have := size_pair_le r (packMarks x)
    have hrw : (r + 1) * Nat.size n = r * Nat.size n + Nat.size n := by ring
    omega
  have hn1 : Nat.size n ≤ (r + 1) * Nat.size n := Nat.le_mul_of_pos_left _ (by omega)
  have h2 : Nat.size (Nat.pair n (Nat.pair r (packMarks x))) ≤ 6 * ((r + 1) * Nat.size n) + 6 := by
    have := size_pair_le n (Nat.pair r (packMarks x))
    omega
  have hkey : (15 + elen dbl) * Nat.size (Nat.pair n (Nat.pair r (packMarks x)))
      ≤ 6 * (15 + elen dbl) * ((r + 1) * Nat.size n) + 6 * (15 + elen dbl) := by
    calc (15 + elen dbl) * Nat.size (Nat.pair n (Nat.pair r (packMarks x)))
        ≤ (15 + elen dbl) * (6 * ((r + 1) * Nat.size n) + 6) := Nat.mul_le_mul_left _ h2
      _ = 6 * (15 + elen dbl) * ((r + 1) * Nat.size n) + 6 * (15 + elen dbl) := by ring
  calc KE (lensCode (markingLens x))
      ≤ elen markBuilder + (15 + elen dbl) * Nat.size (Nat.pair n (Nat.pair r (packMarks x)))
          + (3 + (15 + elen dbl)) := hinv
    _ ≤ elen markBuilder + (6 * (15 + elen dbl) * ((r + 1) * Nat.size n) + 6 * (15 + elen dbl))
          + (3 + (15 + elen dbl)) := Nat.add_le_add_right (Nat.add_le_add_left hkey _) _
    _ = 6 * (15 + elen dbl) * ((r + 1) * Nat.size n)
          + (elen markBuilder + 7 * (15 + elen dbl) + 3) := by ring

/-- **The marking floor, unconditional** ([Persistence] §5, Proposition 5.3 + §7, Corollary 7.5(i)).
`CbH_ge_marking` with its price hypothesis discharged by `KE_markingLens_le`: over **every**
permutation world, a budget that clears the explicit price of `r` marks carries entropy
`log₂ (n ! / (n − r)!)`, stated division-free.

No genericity, no maximality, no hypothesis on `U`, and — now — no named price. -/
theorem CbH_ge_marking' {r : ℕ} {U : Perm (Fin n)} {x : Fin r → Fin n}
    (hx : Function.Injective x) (hrn : r < n) {b : ℕ}
    (hb : 6 * (15 + elen dbl) * ((r + 1) * Nat.size n)
        + (elen markBuilder + 7 * (15 + elen dbl) + 3) ≤ b) :
    n ! ≤ CbH U b * (n - r)! :=
  CbH_ge_marking hx hrn fun _ hy => le_trans (KE_markingLens_le hrn hy) hb

/-! ### General labels on the marks ([Persistence] Open problem 8.4's design, the graded ledger)

The marking family of Proposition 5.3 sends each mark to its OWN index, `j ↦ j + 1` — the cheapest
possible labelling, distinct and increasing by construction. The graded ledger's marking-anatomy
pole needs marks carrying ARBITRARY (possibly repeated) labels: everything off `r` marked points
reads a fixed default value, and each mark `x j` reads an arbitrary `lab j`. The price is the same
shape as `KE_markingLens_le` — one fixed builder, positions and labels each packed as a base-modulus
numeral (`packMarks` reused at the label alphabet's own modulus `k`) — with `k` entering exactly
where `κ = r + 1` entered before. -/

/-- **The labelled marking lens**: `r` distinguished points `x 0, …, x (r − 1)` are read as the
ARBITRARY (possibly repeated) labels `lab 0, …, lab (r − 1)`, and every other state reads the fixed
`default`. `markingLens` is the case `k = r + 1`, `lab = Fin.succ`, `default = 0`. -/
noncomputable def labelledMarkingLens {r k : ℕ} (x : Fin r → Fin n) (lab : Fin r → Fin k)
    (default : Fin k) (i : Fin n) : Fin k :=
  if h : ∃ j, x j = i then lab h.choose else default

/-- A marked point is read as its own (arbitrary) label. -/
private theorem labelledMarkingLens_mark {r k : ℕ} {x : Fin r → Fin n} (hx : Function.Injective x)
    (lab : Fin r → Fin k) (default : Fin k) (j : Fin r) :
    labelledMarkingLens x lab default (x j) = lab j := by
  have h : ∃ j', x j' = x j := ⟨j, rfl⟩
  rw [labelledMarkingLens, dif_pos h]
  exact congrArg lab (hx h.choose_spec)

/-- An unmarked point reads the default. -/
private theorem labelledMarkingLens_unmark {r k : ℕ} {x : Fin r → Fin n} {lab : Fin r → Fin k}
    {default : Fin k} {i : Fin n} (h : ¬∃ j, x j = i) :
    labelledMarkingLens x lab default i = default := by
  rw [labelledMarkingLens, dif_neg h]

/-- The bounded search for the mark sitting at `i`, shifted up by one exactly as `markVal` shifts —
`0` unambiguously means "no mark here" — but returning the LABEL digit rather than the mark's own
index, so a repeated or non-increasing label alphabet is no obstruction. -/
private def labelMatchSum (n r k v pos i : ℕ) : ℕ :=
  ((List.range r).map fun j => if digitAt n pos j = i then digitAt k v j + 1 else 0).sum

/-- The label read off the packed positions and packed labels at state `i`: the shifted search,
un-shifted, or the default when the search finds nothing. -/
private def labelVal (n r k default v pos i : ℕ) : ℕ :=
  if labelMatchSum n r k v pos i = 0 then default else labelMatchSum n r k v pos i - 1

private theorem labelMatchSum_eq_sum (n r k v pos i : ℕ) :
    labelMatchSum n r k v pos i
      = ∑ j ∈ Finset.range r, (if digitAt n pos j = i then digitAt k v j + 1 else 0) := by
  rw [labelMatchSum]; simp [Finset.sum, Multiset.range]

/-- **The builder reads the labelled marking lens back off the two numerals.** Injectivity of `x`
collapses the bounded search to a single term: at most one mark sits at any given state. -/
private theorem labelVal_eq {r k : ℕ} (hn : 0 < n) (hk : 0 < k) {x : Fin r → Fin n}
    (hx : Function.Injective x) (lab : Fin r → Fin k) (default : Fin k) (i : Fin n) :
    labelVal n r k (default : ℕ) (packMarks (n := k) lab) (packMarks x) (i : ℕ)
      = (labelledMarkingLens x lab default i : ℕ) := by
  have htest : ∀ (j : ℕ) (hj : j < r),
      (digitAt n (packMarks x) j = (i : ℕ)) ↔ x ⟨j, hj⟩ = i := by
    intro j hj
    rw [show digitAt n (packMarks x) j = (x ⟨j, hj⟩ : ℕ) from digit_packMarks hn x ⟨j, hj⟩]
    exact ⟨fun h => Fin.val_injective h, fun h => congrArg Fin.val h⟩
  rw [labelVal, labelMatchSum_eq_sum]
  by_cases hex : ∃ j' : Fin r, x j' = i
  · obtain ⟨j₀, hj₀⟩ := hex
    have hml : (labelledMarkingLens x lab default i : ℕ) = (lab j₀ : ℕ) := by
      rw [← hj₀, labelledMarkingLens_mark hx]
    have hc : digitAt n (packMarks x) (j₀ : ℕ) = (i : ℕ) := by
      rw [htest (j₀ : ℕ) j₀.2, Fin.eta]; exact hj₀
    have hlab : digitAt k (packMarks (n := k) lab) (j₀ : ℕ) = (lab j₀ : ℕ) :=
      digit_packMarks (n := k) hk lab j₀
    have h0 : ∀ j ∈ Finset.range r, j ≠ (j₀ : ℕ) →
        (if digitAt n (packMarks x) j = (i : ℕ) then digitAt k (packMarks (n := k) lab) j + 1
          else 0) = 0 := by
      intro j hj hjk
      rw [Finset.mem_range] at hj
      have hnc : ¬(digitAt n (packMarks x) j = (i : ℕ)) := by
        rw [htest j hj]
        exact fun hcontra => hjk (congrArg Fin.val (hx (hcontra.trans hj₀.symm)))
      rw [if_neg hnc]
    have h1 : (j₀ : ℕ) ∉ Finset.range r →
        (if digitAt n (packMarks x) (j₀ : ℕ) = (i : ℕ)
          then digitAt k (packMarks (n := k) lab) (j₀ : ℕ) + 1 else 0) = 0 :=
      fun hk' => absurd (Finset.mem_range.mpr j₀.2) hk'
    rw [Finset.sum_eq_single (j₀ : ℕ) h0 h1, if_pos hc, hlab]
    simp [hml]
  · have h0 : ∀ j ∈ Finset.range r,
        (if digitAt n (packMarks x) j = (i : ℕ) then digitAt k (packMarks (n := k) lab) j + 1
          else 0) = 0 := by
      intro j hj
      rw [Finset.mem_range] at hj
      have hnc : ¬(digitAt n (packMarks x) j = (i : ℕ)) := by
        rw [htest j hj]
        exact fun hcontra => hex ⟨⟨j, hj⟩, hcontra⟩
      rw [if_neg hnc]
    rw [Finset.sum_eq_zero h0, labelledMarkingLens_unmark hex, if_pos rfl]

/-- **The tabulation, rebuilt from the packed program** `⟨n, r, k, default, pos, v⟩` — ONE fixed
function of a single natural number, carrying no dependence on `n`, `r`, `k`, or the marks and
their labels. -/
private def labelledMarkTableFn (a : ℕ) : ℕ :=
  Encodable.encode ((List.range a.unpair.1).map
    (labelVal a.unpair.1 a.unpair.2.unpair.1 a.unpair.2.unpair.2.unpair.1
      a.unpair.2.unpair.2.unpair.2.unpair.1
      a.unpair.2.unpair.2.unpair.2.unpair.2.unpair.2
      a.unpair.2.unpair.2.unpair.2.unpair.2.unpair.1))

/-- **The builder is correct**: on the packed program `⟨n, r, k, default, packMarks x,
packMarks lab⟩` it outputs exactly the labelled marking lens's encoded tabulation. -/
private theorem labelledMarkTableFn_eq {r k : ℕ} (hn : 0 < n) (hk : 0 < k) {x : Fin r → Fin n}
    (hx : Function.Injective x) (lab : Fin r → Fin k) (default : Fin k) :
    labelledMarkTableFn (Nat.pair n (Nat.pair r (Nat.pair k (Nat.pair (default : ℕ)
      (Nat.pair (packMarks x) (packMarks (n := k) lab))))))
      = lensCode (labelledMarkingLens x lab default) := by
  rw [labelledMarkTableFn, lensCode, lensTable]
  simp only [Nat.unpair_pair]
  congr 1
  have hfr : (List.finRange n).map Fin.val = List.range n := by simp
  rw [← hfr, List.map_map]
  exact List.map_congr_left fun i _ => labelVal_eq hn hk hx lab default i

/-- Summing a primitive-recursive list of naturals is primitive recursive (`List.sum` as a
`foldr`), specialized to the labelled-mark search — the general `primrec_list_sum` above,
restated so the two proofs stay independent of one another's internals. -/
private theorem primrec_labelledMarkTableFn : Primrec labelledMarkTableFn := by
  have hN : Primrec fun a : ℕ => a.unpair.1 := Primrec.fst.comp Primrec.unpair
  have hR1 : Primrec fun a : ℕ => a.unpair.2 := Primrec.snd.comp Primrec.unpair
  have hR : Primrec fun a : ℕ => a.unpair.2.unpair.1 := Primrec.fst.comp (Primrec.unpair.comp hR1)
  have hR2 : Primrec fun a : ℕ => a.unpair.2.unpair.2 := Primrec.snd.comp (Primrec.unpair.comp hR1)
  have hK : Primrec fun a : ℕ => a.unpair.2.unpair.2.unpair.1 :=
    Primrec.fst.comp (Primrec.unpair.comp hR2)
  have hR3 : Primrec fun a : ℕ => a.unpair.2.unpair.2.unpair.2 :=
    Primrec.snd.comp (Primrec.unpair.comp hR2)
  have hD : Primrec fun a : ℕ => a.unpair.2.unpair.2.unpair.2.unpair.1 :=
    Primrec.fst.comp (Primrec.unpair.comp hR3)
  have hR4 : Primrec fun a : ℕ => a.unpair.2.unpair.2.unpair.2.unpair.2 :=
    Primrec.snd.comp (Primrec.unpair.comp hR3)
  have hPos : Primrec fun a : ℕ => a.unpair.2.unpair.2.unpair.2.unpair.2.unpair.1 :=
    Primrec.fst.comp (Primrec.unpair.comp hR4)
  have hV : Primrec fun a : ℕ => a.unpair.2.unpair.2.unpair.2.unpair.2.unpair.2 :=
    Primrec.snd.comp (Primrec.unpair.comp hR4)
  have hpow : Primrec₂ ((· ^ ·) : ℕ → ℕ → ℕ) := Primrec₂.unpaired'.1 Nat.Primrec.pow
  have ha : Primrec fun q : (ℕ × ℕ) × ℕ => q.1.1 := Primrec.fst.comp Primrec.fst
  -- the shifted search test, over `q : (ℕ × ℕ) × ℕ` — `q.1.1` the packed program, `q.1.2` the
  -- state `i`, `q.2` the mark index `j`
  have hinner : Primrec₂ fun (p : ℕ × ℕ) (j : ℕ) =>
      if digitAt p.1.unpair.1 p.1.unpair.2.unpair.2.unpair.2.unpair.2.unpair.1 j = p.2
      then digitAt p.1.unpair.2.unpair.2.unpair.1
        p.1.unpair.2.unpair.2.unpair.2.unpair.2.unpair.2 j + 1
      else 0 := by
    have hposdig : Primrec fun q : (ℕ × ℕ) × ℕ =>
        digitAt q.1.1.unpair.1 q.1.1.unpair.2.unpair.2.unpair.2.unpair.2.unpair.1 q.2 :=
      Primrec.nat_mod.comp
        (Primrec.nat_div.comp (hPos.comp ha) (hpow.comp (hN.comp ha) Primrec.snd))
        (hN.comp ha)
    have hlabdig : Primrec fun q : (ℕ × ℕ) × ℕ =>
        digitAt q.1.1.unpair.2.unpair.2.unpair.1
          q.1.1.unpair.2.unpair.2.unpair.2.unpair.2.unpair.2 q.2 :=
      Primrec.nat_mod.comp
        (Primrec.nat_div.comp (hV.comp ha) (hpow.comp (hK.comp ha) Primrec.snd))
        (hK.comp ha)
    exact (Primrec.ite (PrimrecRel.comp Primrec.eq hposdig (Primrec.snd.comp Primrec.fst))
      (Primrec.succ.comp hlabdig) (Primrec.const 0)).to₂
  have hsum : Primrec₂ fun (a : ℕ) (i : ℕ) =>
      labelMatchSum a.unpair.1 a.unpair.2.unpair.1 a.unpair.2.unpair.2.unpair.1
        a.unpair.2.unpair.2.unpair.2.unpair.2.unpair.2
        a.unpair.2.unpair.2.unpair.2.unpair.2.unpair.1 i :=
    (primrec_list_sum (f := fun p : ℕ × ℕ =>
        (List.range p.1.unpair.2.unpair.1).map fun j =>
          if digitAt p.1.unpair.1 p.1.unpair.2.unpair.2.unpair.2.unpair.2.unpair.1 j = p.2
          then digitAt p.1.unpair.2.unpair.2.unpair.1
            p.1.unpair.2.unpair.2.unpair.2.unpair.2.unpair.2 j + 1
          else 0)
      (Primrec.list_map (Primrec.list_range.comp (hR.comp Primrec.fst)) hinner)).to₂
  have hval : Primrec₂ fun (a : ℕ) (i : ℕ) =>
      labelVal a.unpair.1 a.unpair.2.unpair.1 a.unpair.2.unpair.2.unpair.1
        a.unpair.2.unpair.2.unpair.2.unpair.1 a.unpair.2.unpair.2.unpair.2.unpair.2.unpair.2
        a.unpair.2.unpair.2.unpair.2.unpair.2.unpair.1 i := by
    have hsum' : Primrec fun p : ℕ × ℕ =>
        labelMatchSum p.1.unpair.1 p.1.unpair.2.unpair.1 p.1.unpair.2.unpair.2.unpair.1
          p.1.unpair.2.unpair.2.unpair.2.unpair.2.unpair.2
          p.1.unpair.2.unpair.2.unpair.2.unpair.2.unpair.1 p.2 := hsum
    have heq : PrimrecPred fun p : ℕ × ℕ =>
        labelMatchSum p.1.unpair.1 p.1.unpair.2.unpair.1 p.1.unpair.2.unpair.2.unpair.1
          p.1.unpair.2.unpair.2.unpair.2.unpair.2.unpair.2
          p.1.unpair.2.unpair.2.unpair.2.unpair.2.unpair.1 p.2 = 0 :=
      PrimrecRel.comp Primrec.eq hsum' (Primrec.const 0)
    exact (Primrec.ite heq (hD.comp Primrec.fst) (Primrec.nat_sub.comp hsum' (Primrec.const 1))
      ).to₂.of_eq fun a i => by rw [labelVal]
  exact Primrec.encode.comp (Primrec.list_map (Primrec.list_range.comp hN) hval)

private theorem partrec_labelledMarkTableFn :
    Nat.Partrec (fun a : ℕ => (labelledMarkTableFn a : ℕ)) :=
  _root_.Partrec.nat_iff.mp (Primrec.to_comp primrec_labelledMarkTableFn).partrec

/-- **The fixed labelled-mark builder code.** Independent of `n`, `r`, `k`, the marks, their labels,
and the default — one program, exactly as `markBuilder`. -/
noncomputable def labelledMarkBuilder : Nat.Partrec.Code :=
  Classical.choose (Nat.Partrec.Code.exists_code.mp partrec_labelledMarkTableFn)

private theorem eval_labelledMarkBuilder (a : ℕ) :
    Nat.Partrec.Code.eval labelledMarkBuilder a = Part.some (labelledMarkTableFn a) := by
  have h := congrFun (Classical.choose_spec
    (Nat.Partrec.Code.exists_code.mp partrec_labelledMarkTableFn)) a
  simpa [labelledMarkBuilder] using h

/-- **The labelled marking lens's explicit price** ([Persistence] Open problem 8.4's design, the
graded ledger's marking-anatomy pole). `r` marks on `n` states, carrying labels from a `k`-element
alphabet, are tabulated by a program of length `O ((r + 1) · (Nat.size n + Nat.size k))` — the same
shape as `KE_markingLens_le`, with the label alphabet's own modulus `k` priced exactly where the
distinct-label count `r + 1` was priced before (`k = r + 1`, `lab = Fin.succ`, `default = 0`
recovers it). Positions and labels are packed as independent base-modulus numerals
(`packMarks x`, `packMarks lab`) and decoded by one fixed builder. -/
theorem KE_labelledMarkingLens_le {r k : ℕ} (hrn : r < n) (hk : 0 < k) {x : Fin r → Fin n}
    (hx : Function.Injective x) (lab : Fin r → Fin k) (default : Fin k) :
    KE (lensCode (labelledMarkingLens x lab default))
      ≤ 32 * (15 + elen dbl) * ((r + 1) * (Nat.size n + Nat.size k))
        + (elen labelledMarkBuilder + 63 * (15 + elen dbl) + 3) := by
  have hn : 0 < n := by omega
  have heval : Nat.Partrec.Code.eval labelledMarkBuilder
      (Nat.pair n (Nat.pair r (Nat.pair k (Nat.pair (default : ℕ)
        (Nat.pair (packMarks x) (packMarks (n := k) lab))))))
      = Part.some (lensCode (labelledMarkingLens x lab default)) := by
    rw [eval_labelledMarkBuilder, labelledMarkTableFn_eq hn hk hx lab default]
  have hinv := invariance_general labelledMarkBuilder _ _ heval
  have hPosSize : Nat.size (packMarks x) ≤ r * Nat.size n := size_packMarks_le hn x
  have hVSize : Nat.size (packMarks (n := k) lab) ≤ r * Nat.size k := size_packMarks_le hk lab
  have hDSize : Nat.size (default : ℕ) ≤ Nat.size k :=
    Nat.size_le_size (le_of_lt default.isLt)
  have hRSize : Nat.size r ≤ Nat.size n := Nat.size_le_size (le_of_lt hrn)
  have hPV : Nat.size (Nat.pair (packMarks x) (packMarks (n := k) lab))
      ≤ 2 * (r * Nat.size n + r * Nat.size k) + 2 := by
    have := size_pair_le (packMarks x) (packMarks (n := k) lab)
    omega
  have hDPV : Nat.size (Nat.pair (default : ℕ) (Nat.pair (packMarks x) (packMarks (n := k) lab)))
      ≤ 4 * (r * Nat.size n + r * Nat.size k) + 2 * Nat.size k + 6 := by
    have := size_pair_le (default : ℕ) (Nat.pair (packMarks x) (packMarks (n := k) lab))
    omega
  have hKDPV : Nat.size (Nat.pair k
      (Nat.pair (default : ℕ) (Nat.pair (packMarks x) (packMarks (n := k) lab))))
      ≤ 8 * (r * Nat.size n + r * Nat.size k) + 6 * Nat.size k + 14 := by
    have := size_pair_le k
      (Nat.pair (default : ℕ) (Nat.pair (packMarks x) (packMarks (n := k) lab)))
    omega
  have hRKDPV : Nat.size (Nat.pair r (Nat.pair k
      (Nat.pair (default : ℕ) (Nat.pair (packMarks x) (packMarks (n := k) lab)))))
      ≤ 16 * (r * Nat.size n + r * Nat.size k) + 2 * Nat.size n + 12 * Nat.size k + 30 := by
    have := size_pair_le r (Nat.pair k
      (Nat.pair (default : ℕ) (Nat.pair (packMarks x) (packMarks (n := k) lab))))
    omega
  have hFull : Nat.size (Nat.pair n (Nat.pair r (Nat.pair k (Nat.pair (default : ℕ)
      (Nat.pair (packMarks x) (packMarks (n := k) lab))))))
      ≤ 32 * (r * Nat.size n + r * Nat.size k) + 6 * Nat.size n + 24 * Nat.size k + 62 := by
    have := size_pair_le n (Nat.pair r (Nat.pair k
      (Nat.pair (default : ℕ) (Nat.pair (packMarks x) (packMarks (n := k) lab)))))
    omega
  have hexpand : (r + 1) * (Nat.size n + Nat.size k)
      = r * Nat.size n + r * Nat.size k + Nat.size n + Nat.size k := by ring
  have hkey : Nat.size (Nat.pair n (Nat.pair r (Nat.pair k (Nat.pair (default : ℕ)
      (Nat.pair (packMarks x) (packMarks (n := k) lab))))))
      ≤ 32 * ((r + 1) * (Nat.size n + Nat.size k)) + 62 := by
    rw [hexpand]; omega
  calc KE (lensCode (labelledMarkingLens x lab default))
      ≤ elen labelledMarkBuilder + (15 + elen dbl) * Nat.size (Nat.pair n (Nat.pair r
          (Nat.pair k (Nat.pair (default : ℕ)
            (Nat.pair (packMarks x) (packMarks (n := k) lab))))))
        + (3 + (15 + elen dbl)) := hinv
    _ ≤ elen labelledMarkBuilder
          + (15 + elen dbl) * (32 * ((r + 1) * (Nat.size n + Nat.size k)) + 62)
          + (3 + (15 + elen dbl)) := by
        have := Nat.mul_le_mul_left (15 + elen dbl) hkey
        omega
    _ = 32 * (15 + elen dbl) * ((r + 1) * (Nat.size n + Nat.size k))
          + (elen labelledMarkBuilder + 63 * (15 + elen dbl) + 3) := by ring

/-! ## Renting versus owning a reading ([Persistence] §5, Definition 5.1, the uniform variant)

Definition 5.1's budget is **per-frame**: each frame's table must be describable in `b` bits, and
nothing relates the descriptions. An observer meeting it *rents* its reading — it pays the floor
again at every step, forever, and the collapse prices exactly that rent.

The uniform variant named after Definition 5.1 is the other way to hold a reading: one program of
length at most `b` computing `t ↦ ℓ t`. The observer *owns* the reading, paying once. The exchange
rate between the two is the paper's `K (ℓ t) ≤ b + O (log t)`, and `uniformBudget_frame_cost` is
that reduction with both constants explicit and absolute: the owner's program, run at `t`, is a
description of frame `t` — hand `t` to it as a binary constant and `invariance_general` charges the
program once and the clock `O (log t)`.

The reduction is what makes the uniform capacity's cap **horizon-free**. `CbHu_collapse` below is
`CbH_collapse` with the budget shifted by an absolute constant and *no* `log T` term anywhere,
because the collapse consumes frames `0` and `1` only (`permCarries_frame_one`) — and those two
clock inputs are constants, so their `O (log t)` is `O (1)`. Renting and owning collapse alike;
what differs is what the observer pays to get there. -/

/-- **The uniform budget** ([Persistence] §5, Definition 5.1, the uniform variant): a *single*
program of length at most `b` computes every frame's table, `t ↦ lensCode (ℓ t)`. Contrast
`PermBudget`, which asks only that each frame have *some* `b`-bit description of its own — a
uniform budget is strictly the stronger demand, and the observer meeting it pays once rather than
per frame. -/
def UniformBudget (ℓ : ℕ → Fin n → Fin m) (b : ℕ) : Prop :=
  ∃ c : Nat.Partrec.Code, elen c ≤ b ∧ ∀ t, c.eval t = Part.some (lensCode (ℓ t))

/-- A larger budget affords no less: the same program witnesses it. -/
private theorem UniformBudget.mono {ℓ : ℕ → Fin n → Fin m} {b₁ b₂ : ℕ} (h : UniformBudget ℓ b₁)
    (hb : b₁ ≤ b₂) : UniformBudget ℓ b₂ :=
  let ⟨c, hlen, heval⟩ := h
  ⟨c, hlen.trans hb, heval⟩

/-- **The frame-cost reduction** — [Persistence] §5, the uniform variant's
`K (ℓ t) ≤ b + O (log t)`.
An owner's program is a description of every one of its frames, at the price of the clock: run the
program on the binary numeral for `t`. The `O (log t)` is `κ · Nat.size t` with `κ = 15 + elen dbl`
and the additive constant `3 + κ`, both absolute — fixed once and for all, independent of the
family, the world, and `n`.

This is what converts an owned reading into a rented one, and it is the only bridge between the two
budgets used below. -/
theorem uniformBudget_frame_cost {ℓ : ℕ → Fin n → Fin m} {b : ℕ} (h : UniformBudget ℓ b) (t : ℕ) :
    KE (lensCode (ℓ t)) ≤ b + (15 + elen dbl) * Nat.size t + (3 + (15 + elen dbl)) := by
  obtain ⟨c, hlen, heval⟩ := h
  have hinv := invariance_general c t (lensCode (ℓ t)) (heval t)
  omega

/-- **The first two frames cost the budget plus a constant.** The clock inputs `t = 0` and `t = 1`
are themselves constants — `Nat.size t ≤ 1` — so the reduction's `O (log t)` degenerates to `O (1)`
on exactly the frames the collapse reads. No horizon appears, and none can: the bound is uniform in
everything. -/
private theorem uniformBudget_early_cost {ℓ : ℕ → Fin n → Fin m} {b : ℕ} (h : UniformBudget ℓ b)
    {t : ℕ} (ht : t ≤ 1) : KE (lensCode (ℓ t)) ≤ b + (33 + 2 * elen dbl) := by
  have hc := uniformBudget_frame_cost h t
  have hs : Nat.size t ≤ 1 := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp ht with rfl | rfl <;> simp
  have hm := Nat.mul_le_mul (le_refl (15 + elen dbl)) hs
  omega

/-- The **carried entropies affordable to an owner at budget `b`**: `BudgetedEntropies` with the
per-frame predicate replaced by `UniformBudget`. -/
def UniformBudgetedEntropies (U : Perm (Fin n)) (b : ℕ) : Set ℕ :=
  {N : ℕ | ∃ k : ℕ, ∃ ℓ : ℕ → Fin n → Fin k, PermCarries U ℓ ∧ UniformBudget ℓ b ∧
      N = Nat.card ↥(orbit (Perm (Fin n)) (ℓ 0))}

/-- **The uniform entropic capacity** — [Persistence] §5, Definition 5.4 read through Definition
5.1's uniform variant: the largest carried entropy, as the relabelling-class size `2 ^ E` (the
cardinality form of `CbH`, see above), of a reference frame whose family is computed *by one
program* of at most `b` bits. The capacity of an observer that owns its reading rather than renting
it. -/
noncomputable def CbHu (U : Perm (Fin n)) (b : ℕ) : ℕ := sSup (UniformBudgetedEntropies U b)

/-- No reading distinguishes more than the world has to offer (`budgetedEntropies_le`'s argument,
verbatim: the budget plays no part). -/
private theorem uniformBudgetedEntropies_le {U : Perm (Fin n)} {b N : ℕ}
    (h : N ∈ UniformBudgetedEntropies U b) : N ≤ n ! := by
  obtain ⟨k, ℓ, -, -, rfl⟩ := h
  have hprod : 0 < ∏ i : Fin k, (Nat.card {x : Fin n // ℓ 0 x = i})! :=
    Finset.prod_pos fun i _ => Nat.factorial_pos _
  exact card_orbit_mul_prod_fiber (ℓ 0) ▸ Nat.le_mul_of_pos_right _ hprod

private theorem bddAbove_uniformBudgetedEntropies (U : Perm (Fin n)) (b : ℕ) :
    BddAbove (UniformBudgetedEntropies U b) :=
  ⟨n !, fun _ h => uniformBudgetedEntropies_le h⟩

/-- **An owner's capacity never exceeds a faithful reading** either. -/
theorem CbHu_le_factorial (U : Perm (Fin n)) (b : ℕ) : CbHu U b ≤ n ! := by
  rcases Set.eq_empty_or_nonempty (UniformBudgetedEntropies U b) with hemp | hne
  · simp [CbHu, hemp]
  · exact csSup_le hne fun _ h => uniformBudgetedEntropies_le h

/-- More budget never hurts an owner either. -/
theorem CbHu_mono (U : Perm (Fin n)) {b₁ b₂ : ℕ} (h : b₁ ≤ b₂) : CbHu U b₁ ≤ CbHu U b₂ :=
  csSup_le_csSup' (bddAbove_uniformBudgetedEntropies U b₂) (by
    rintro N ⟨k, ℓ, hcar, hbud, rfl⟩
    exact ⟨k, ℓ, hcar, hbud.mono h, rfl⟩)

/-- **Owning does not beat the collapse** — the uniform capacity's cap, horizon-free. For every `d`,
the worlds whose *uniform* entropic capacity at budget `b` exceeds `2 · (b + c) + d + 2` — with the
absolute constant `c = 33 + 2 · elen dbl` — number at most `n ! / 2 ^ d`, a `2 ^ (-d)` fraction.

This is `CbH_collapse` with the budget shifted by `c` and **nothing else changed**: no horizon, no
`log T`, no growing term. The reason is structural rather than incidental. `collapse_union` prices a
world through frames `0` and `1` alone (`permCarries_frame_one` determines the second frame from the
first), the frame-cost reduction charges frame `t` a clock of `O (log t)`, and `log 0` and `log 1`
are `O (1)`. So the whole `O (log t)` slack of the uniform variant is spent before the clock ever
ticks, and an owner faces the same `Θ (b)` ceiling a renter does — at any horizon whatsoever.

Ownership is therefore not a way around the collapse; it is a way to *pay for a reading once*. What
it buys is the subject of the (CD) constructions below. -/
theorem CbHu_collapse (b d : ℕ) :
    {U : Perm (Fin n) | 2 ^ (2 * (b + (33 + 2 * elen dbl)) + d + 2) < CbHu U b}.ncard * 2 ^ d
      ≤ n ! := by
  refine le_trans (Nat.mul_le_mul_right _ (Set.ncard_le_ncard ?_ (Set.toFinite _)))
    (collapse_union d)
  intro U hU
  have hlt : 2 ^ (2 * (b + (33 + 2 * elen dbl)) + d + 2) < CbHu U b := hU
  have hne : (UniformBudgetedEntropies U b).Nonempty := by
    by_contra hcon
    rw [Set.not_nonempty_iff_eq_empty] at hcon
    rw [CbHu, hcon, csSup_empty] at hlt
    exact absurd hlt (Nat.not_lt_zero _)
  obtain ⟨k, ℓ, hcar, hbud, hval⟩ : CbHu U b ∈ UniformBudgetedEntropies U b :=
    Nat.sSup_mem hne (bddAbove_uniformBudgetedEntropies U b)
  refine ⟨k, ℓ 0, hcar.1, ?_⟩
  have h1 : ℓ 1 = U • ℓ 0 := permCarries_frame_one hcar.2
  have hb0 := uniformBudget_early_cost hbud (t := 0) (by norm_num)
  have hb1 := uniformBudget_early_cost hbud (t := 1) (le_refl 1)
  rw [h1, show U • ℓ 0 = ℓ 0 ∘ ⇑U⁻¹ from rfl] at hb1
  calc 2 ^ (KE (lensCode (ℓ 0)) + KE (lensCode (ℓ 0 ∘ ⇑U⁻¹)) + d + 2)
      ≤ 2 ^ (2 * (b + (33 + 2 * elen dbl)) + d + 2) :=
        Nat.pow_le_pow_right (by norm_num) (by omega)
    _ < Nat.card ↥(orbit (Perm (Fin n)) (ℓ 0)) := hval ▸ hlt

/-! ## The ownership construction ([Persistence] §8, Proposition 8.1)

Proposition 8.1 prices the canonical family `ℓ t = θ ∘ (U_∞⁻¹) ^ t ∘ U ^ N` at
`K (U|core) + K (θ) + O (log t)` per frame. `ownership` is the corresponding construction in the §7
permutation setting, where the world is its own recurrent core (no transient `U ^ N`, and
`U_∞ = U`) and the family is `ℓ t = ℓ₀ ∘ (U ^ t)⁻¹`: a code for `ℓ₀`'s table and a code for `U`'s
table assemble — by a *fixed* builder, absolute constant included — into a **uniform** budget for
the whole family.

Two things are worth reading off the statement. First, the world's own table needs no new encoding
apparatus: a permutation of `Fin n` coerces to a function `Fin n → Fin n`, which is a lens, so
`lensCode ⇑U` is the same object the collapse already prices. Second, Proposition 8.1's `O (log t)`
per frame does not appear here — it has been *absorbed* into the definition of `UniformBudget`, and
`uniformBudget_frame_cost` is where it reappears, with the constant made explicit. That is the whole
point of the uniform variant: the clock is not part of what the owner stores.

The construction itself is table transport. `U`'s table is inverted by `idx` — the ledger's own
primitive — and the reading is dragged along it once per step. -/

/-- The canonical family over a permutation world carries a persistent model, for **any** surjective
reference frame ([Persistence] §7). `markCarries`, with the marking lens generalized away: reading
through the time-`t` frame after `t` steps returns the time-`0` reading by construction, over every
permutation world, with no hypothesis on `U`. -/
theorem permCarries_smul {U : Perm (Fin n)} {ℓ₀ : Fin n → Fin m} (h : Function.Surjective ℓ₀) :
    PermCarries U (fun t => (U ^ t) • ℓ₀) := by
  constructor
  · simpa using h
  · intro t i
    change ℓ₀ ((U ^ t)⁻¹ ((U ^ t) i)) = ℓ₀ ((U ^ 0)⁻¹ i)
    simp

/-- One step of **table transport**: the reading `L`, dragged along the world whose own table is
`P`. Entry `i` of the new table is entry `idx i P` of the old — and `idx i P` is the unique `j` with
`U j = i`, that is, `U⁻¹ i`. So `ownStep P` computes `L ↦ L ∘ U⁻¹` on tables, using nothing but the
list operations, and `idx` is the same table inversion the ledger runs on. -/
def ownStep (P L : List ℕ) : List ℕ := (List.range L.length).map fun i => L.getD (idx i P) 0

/-- `t` steps of table transport — the owner's whole computation, once the tables are in hand. -/
def ownIter (P : List ℕ) (t : ℕ) (L : List ℕ) : List ℕ := (ownStep P)^[t] L

/-- Reading an entry out of a tabulation over `Fin n`. -/
theorem getD_map_finRange (g : Fin n → ℕ) (j : Fin n) :
    ((List.finRange n).map g).getD (j : ℕ) 0 = g j := by
  have hj : (j : ℕ) < ((List.finRange n).map g).length := by simp [j.2]
  rw [List.getD_eq_getElem _ _ hj]
  simp

/-! ## The graded ledger ([Persistence] Open problem 8.4's design, §6's argument at every family)

Theorem 6.3's ledger (`ledger_K`) prices a MAXIMAL family: with `|M| = |core|`, the two frames pin
`U` down to one value, and the two-part code is exact. Drop maximality and the two frames pin `U`
down only to a COSET of `ℓ₀`'s fiber-stabilizer (Lemma 7.1's `card_stabilizer_lens`, of size
`∏ᵢ (fiberᵢ)!`) — `ℓ₁ = ℓ₀ ∘ U⁻¹` (`permCarries_frame_one`) says `U` solves `ℓ₁ ∘ W = ℓ₀`, and the
solutions form exactly the right coset `U · stabilizer (ℓ₀)`. The two-part code generalizes to a
THREE-part one: the two tables plus a coset INDEX, at coefficient exactly `1` on the index — a fixed
decoder enumerates candidate tables `W` over `[n]` in one canonical order (a base-`n` numeral,
the `packMarks` idiom reused at the full domain `r = n`), filters for bijective-and-matching,
selects the loaded index. `ledger_K` is the case `∏ᵢ (fiberᵢ)! = 1` (`ledger_graded_faithful`). -/

/-- **Reconstruction**: a numeral `< n ^ r` is recovered exactly from its own `r` base-`n` digits —
the converse of `digit_packMarks`'s extraction, by the same peeling induction. This is what makes
the candidate enumeration below a genuine bijection with `[0, n ^ n)` rather than a many-to-one
search. -/
private theorem digitAt_sum_eq :
    ∀ (r w : ℕ), w < n ^ r → ∑ j ∈ Finset.range r, digitAt n w j * n ^ j = w := by
  intro r
  induction r with
  | zero => intro w hw; simp only [pow_zero] at hw; simp [Nat.lt_one_iff.mp hw]
  | succ r ih =>
    intro w hw
    have hpeel : ∑ j ∈ Finset.range (r + 1), digitAt n w j * n ^ j
        = digitAt n w 0 + n * ∑ j ∈ Finset.range r, digitAt n w (j + 1) * n ^ j := by
      rw [Finset.sum_range_succ']
      simp only [pow_zero, mul_one, pow_succ, Finset.mul_sum]
      ring_nf
      rw [Nat.add_comm]
      congr 1
      exact Finset.sum_congr rfl fun j _ => by ring
    have hd0 : digitAt n w 0 = w % n := by unfold digitAt; simp
    have hdsucc : ∀ j, digitAt n w (j + 1) = digitAt n (w / n) j := by
      intro j
      unfold digitAt
      rw [pow_succ, Nat.mul_comm (n ^ j) n, Nat.div_div_eq_div_mul]
    have hwn : w / n < n ^ r := by
      rw [pow_succ] at hw
      exact Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm] at hw)
    calc ∑ j ∈ Finset.range (r + 1), digitAt n w j * n ^ j
        = digitAt n w 0 + n * ∑ j ∈ Finset.range r, digitAt n w (j + 1) * n ^ j := hpeel
      _ = w % n + n * ∑ j ∈ Finset.range r, digitAt n (w / n) j * n ^ j := by
          rw [hd0]
          congr 2
          exact Finset.sum_congr rfl fun j _ => by rw [hdsucc]
      _ = w % n + n * (w / n) := by rw [ih (w / n) hwn]
      _ = w := by rw [Nat.add_comm]; exact Nat.div_add_mod w n

/-- The decoded table, as a `List ℕ` — reading a `lensCode`/`lensTable` value back through
`Encodable.decode`, exactly the `invcomp`/`markTableFn` idiom's first step. -/
private def rawTable (code : ℕ) : List ℕ := (Encodable.decode (α := List ℕ) code).getD []

private theorem primrec_rawTable : Primrec rawTable :=
  Primrec.option_getD.comp Primrec.decode (Primrec.const [])

/-- `rawTable` inverts `lensCode` exactly — the encode/decode round trip. -/
private theorem rawTable_lensCode (ℓ : Fin n → Fin m) : rawTable (lensCode ℓ) = lensTable ℓ := by
  rw [rawTable, lensCode, Encodable.encodek]; rfl

/-- Summing a primitive-recursive `Bool`-list by `&&` is primitive recursive (`List.all` as a
`foldr`) — the Boolean sibling of `primrec_list_sum`. -/
private theorem primrec_list_all {α : Type*} [Primcodable α] {f : α → List ℕ} {g : α → ℕ → Bool}
    (hf : Primrec f) (hg : Primrec₂ g) : Primrec fun a => (f a).all (g a) :=
  (Primrec.list_foldr hf (Primrec.const true)
      ((Primrec.dom_bool₂ (· && ·)).comp (hg.comp Primrec.fst (Primrec.fst.comp Primrec.snd))
        (Primrec.snd.comp Primrec.snd)).to₂).of_eq
    fun a => by
      induction f a with
      | nil => rfl
      | cons b l ih => simp [List.all_cons, ih]

/-- One pairwise distinctness test, `Bool`-valued: `i = j`, or the digits at `i` and `j` differ. -/
private def pairOK (n w i j : ℕ) : Bool :=
  decide (i = j) || !decide (digitAt n w i = digitAt n w j)

private theorem primrec_pairOK :
    Primrec₂ fun (a : ℕ × ℕ) (j : ℕ) => pairOK a.1.unpair.1 a.1.unpair.2 a.2 j := by
  have hpow : Primrec₂ ((· ^ ·) : ℕ → ℕ → ℕ) := Primrec₂.unpaired'.1 Nat.Primrec.pow
  have hN : Primrec fun q : (ℕ × ℕ) × ℕ => q.1.1.unpair.1 :=
    Primrec.fst.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.fst))
  have hW : Primrec fun q : (ℕ × ℕ) × ℕ => q.1.1.unpair.2 :=
    Primrec.snd.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.fst))
  have hI : Primrec fun q : (ℕ × ℕ) × ℕ => q.1.2 := Primrec.snd.comp Primrec.fst
  have hJ : Primrec fun q : (ℕ × ℕ) × ℕ => q.2 := Primrec.snd
  have hdI : Primrec fun q : (ℕ × ℕ) × ℕ => digitAt q.1.1.unpair.1 q.1.1.unpair.2 q.1.2 :=
    Primrec.nat_mod.comp (Primrec.nat_div.comp hW (hpow.comp hN hI)) hN
  have hdJ : Primrec fun q : (ℕ × ℕ) × ℕ => digitAt q.1.1.unpair.1 q.1.1.unpair.2 q.2 :=
    Primrec.nat_mod.comp (Primrec.nat_div.comp hW (hpow.comp hN hJ)) hN
  have h1 : Primrec fun q : (ℕ × ℕ) × ℕ => decide (q.1.2 = q.2) := Primrec.eq.decide.comp hI hJ
  have h2 : Primrec fun q : (ℕ × ℕ) × ℕ =>
      decide (digitAt q.1.1.unpair.1 q.1.1.unpair.2 q.1.2
        = digitAt q.1.1.unpair.1 q.1.1.unpair.2 q.2) :=
    Primrec.eq.decide.comp hdI hdJ
  exact ((Primrec.dom_bool₂ (fun (b1 b2 : Bool) => b1 || !b2)).comp h1 h2).of_eq fun q => by
    simp [pairOK]

/-- **The bijectivity test**: every digit of `w`'s `n`-digit table differs from every other — the
`Bool`-valued, doubly-bounded pairwise search. Injective on a domain the same size as its codomain
is bijective (`candTable_bijective` below), so this one check both certifies a genuine `Perm (Fin
n)` and, by construction, excludes every non-permutation candidate from the enumeration. -/
private def candBijBool (n w : ℕ) : Bool :=
  (List.range n).all (fun i => (List.range n).all (fun j => pairOK n w i j))

private theorem primrec_candBijBool : Primrec₂ candBijBool := by
  have hInner : Primrec₂ fun (packedNW i : ℕ) =>
      (List.range packedNW.unpair.1).all
        (fun j => pairOK packedNW.unpair.1 packedNW.unpair.2 i j) :=
    primrec_list_all (Primrec.list_range.comp (Primrec.fst.comp (Primrec.unpair.comp Primrec.fst)))
      primrec_pairOK
  have hOuter : Primrec fun packedNW : ℕ =>
      (List.range packedNW.unpair.1).all (fun i =>
        (List.range packedNW.unpair.1).all
          (fun j => pairOK packedNW.unpair.1 packedNW.unpair.2 i j)) :=
    primrec_list_all (Primrec.list_range.comp (Primrec.fst.comp Primrec.unpair)) hInner
  exact hOuter.of_eq fun packedNW => rfl

private theorem candBijBool_iff (n w : ℕ) :
    candBijBool n w = true ↔ ∀ i < n, ∀ j < n, i ≠ j → digitAt n w i ≠ digitAt n w j := by
  simp only [candBijBool, List.all_eq_true, decide_eq_true_eq, List.mem_range, pairOK,
    Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not]
  constructor
  · intro h i hi j hj hij hcontra
    rcases h i hi j hj with heq | hne
    · exact hij heq
    · exact hne hcontra
  · intro h i hi j hj
    by_cases hij : i = j
    · left; exact hij
    · right; exact h i hi j hj hij

/-- The candidate's full table, at domain `[0, n)` — `packMarks`'s digit packing read at the
FULL length `r = n`, so every position is a table entry rather than a sparse mark. -/
private def candTable (n w : ℕ) : List ℕ := (List.range n).map (digitAt n w)

private theorem primrec_candTable : Primrec₂ candTable := by
  have hpow : Primrec₂ ((· ^ ·) : ℕ → ℕ → ℕ) := Primrec₂.unpaired'.1 Nat.Primrec.pow
  have hdig : Primrec₂ fun (a : ℕ × ℕ) (i : ℕ) => digitAt a.1 a.2 i := by
    have hN : Primrec fun q : (ℕ × ℕ) × ℕ => q.1.1 := Primrec.fst.comp Primrec.fst
    have hW : Primrec fun q : (ℕ × ℕ) × ℕ => q.1.2 := Primrec.snd.comp Primrec.fst
    exact (Primrec.nat_mod.comp (Primrec.nat_div.comp hW (hpow.comp hN Primrec.snd)) hN).to₂
  exact Primrec.list_map (Primrec.list_range.comp Primrec.fst) hdig

/-- The candidate's digit function is bijective on `Fin n` exactly when `candBijBool` says so —
injective plus equal domain and codomain size (`Finite.injective_iff_bijective`). -/
private theorem candTable_bijective {n w : ℕ} (hn : 0 < n) (h : candBijBool n w = true) :
    Function.Bijective (fun i : Fin n => (⟨digitAt n w (i : ℕ), Nat.mod_lt _ hn⟩ : Fin n)) := by
  rw [candBijBool_iff] at h
  apply Finite.injective_iff_bijective.mp
  intro i j hij
  by_contra hne
  exact h i i.2 j j.2 (fun hcon => hne (Fin.val_injective hcon))
    (by simpa using congrArg Fin.val hij)

/-- **Reading a genuine permutation's own table back off its packing**: `candTable` at `packMarks`
of a `Fin n → Fin n` function reproduces its `lensTable`, digit for digit (`digit_packMarks`). -/
private theorem candTable_packMarks (hn : 0 < n) (W : Fin n → Fin n) :
    candTable n (packMarks W) = lensTable W := by
  rw [candTable, lensTable]
  have hfr : (List.finRange n).map Fin.val = List.range n := by simp
  rw [← hfr, List.map_map]
  exact List.map_congr_left fun i _ => digit_packMarks hn W i

/-- **Injectivity of the packing, at the full domain**: distinct numerals below `n ^ n` decode to
distinct `n`-digit tables — the converse of `candTable_packMarks`, via the reconstruction identity
`digitAt_sum_eq`. This is what turns "the valid numerals inject into the stabilizer coset" into an
actual cardinality bound rather than a many-to-one count. -/
private theorem candTable_injOn : Set.InjOn (candTable n) {w | w < n ^ n} := by
  intro w1 hw1 w2 hw2 heq
  have h1 : ∑ j ∈ Finset.range n, digitAt n w1 j * n ^ j = w1 := digitAt_sum_eq n w1 hw1
  have h2 : ∑ j ∈ Finset.range n, digitAt n w2 j * n ^ j = w2 := digitAt_sum_eq n w2 hw2
  have hdig : ∀ j ∈ Finset.range n, digitAt n w1 j = digitAt n w2 j := by
    intro j hj
    have hjn : j < n := Finset.mem_range.mp hj
    have heq' : (List.range n).map (digitAt n w1) = (List.range n).map (digitAt n w2) := heq
    exact List.map_eq_map_iff.mp heq' j (List.mem_range.mpr hjn)
  rw [← h1, ← h2]
  exact Finset.sum_congr rfl fun j hj => by rw [hdig j hj]

/-- **A candidate is valid** when its table is a genuine permutation AND transports `ℓ₁`'s table to
`ℓ₀`'s — the two conditions the coset argument needs: `candBijBool` certifies bijectivity, and the
bounded search certifies `ℓ₁ (W i) = ℓ₀ i` for every `i`, read straight off the two tables. -/
private def isValid (n t0 t1 w : ℕ) : Prop :=
  candBijBool n w = true ∧
    ∀ i < n, List.getD (rawTable t1) (digitAt n w i) 0 = List.getD (rawTable t0) i 0

private instance decIsValid (n t0 t1 w : ℕ) : Decidable (isValid n t0 t1 w) := by
  unfold isValid; infer_instance

/-- **Duplicating a bound into the pair a `PrimrecRel.forall_lt` needs.** `forall_lt` bounds its
quantifier by the FIRST coordinate of a pair; when the bound is itself computed from the same
parameter the body needs, pairing the parameter with its own bound (via `Primrec.pair`) and
composing supplies exactly that first coordinate. Reused for both nested bounds `isValid` needs. -/
private theorem primrecPred_dup_nat {R : ℕ → ℕ → Prop} {b : ℕ → ℕ}
    (hR : PrimrecRel R) (hb : Primrec b) : PrimrecPred fun p : ℕ => ∀ i < b p, R i p := by
  have hdup : Primrec fun p : ℕ => ((b p, p) : ℕ × ℕ) := Primrec.pair hb Primrec.id
  have hcast : PrimrecPred fun q : ℕ × ℕ => ∀ i < q.1, R i q.2 := PrimrecRel.forall_lt hR
  exact hcast.comp hdup

/-- **`isValid` is primitive recursive**, over the packed program `⟨n, t0, t1, w⟩`. -/
private theorem primrec_isValid :
    PrimrecPred fun p : ℕ => isValid p.unpair.1 p.unpair.2.unpair.1
      p.unpair.2.unpair.2.unpair.1 p.unpair.2.unpair.2.unpair.2 := by
  have hN : Primrec fun p : ℕ => p.unpair.1 := Primrec.fst.comp Primrec.unpair
  have hR1 : Primrec fun p : ℕ => p.unpair.2 := Primrec.snd.comp Primrec.unpair
  have hT0 : Primrec fun p : ℕ => p.unpair.2.unpair.1 := Primrec.fst.comp (Primrec.unpair.comp hR1)
  have hR2 : Primrec fun p : ℕ => p.unpair.2.unpair.2 := Primrec.snd.comp (Primrec.unpair.comp hR1)
  have hT1 : Primrec fun p : ℕ => p.unpair.2.unpair.2.unpair.1 :=
    Primrec.fst.comp (Primrec.unpair.comp hR2)
  have hW : Primrec fun p : ℕ => p.unpair.2.unpair.2.unpair.2 :=
    Primrec.snd.comp (Primrec.unpair.comp hR2)
  have hpow : Primrec₂ ((· ^ ·) : ℕ → ℕ → ℕ) := Primrec₂.unpaired'.1 Nat.Primrec.pow
  have hBij : PrimrecPred fun p : ℕ =>
      candBijBool p.unpair.1 p.unpair.2.unpair.2.unpair.2 = true := by
    have hb : Primrec fun p : ℕ => candBijBool p.unpair.1 p.unpair.2.unpair.2.unpair.2 := by
      have := primrec_candBijBool.comp hN hW
      exact this
    exact Primrec.eq.comp hb (Primrec.const true)
  have hMatch : PrimrecPred fun p : ℕ => ∀ i < p.unpair.1,
      List.getD (rawTable p.unpair.2.unpair.2.unpair.1)
          (digitAt p.unpair.1 p.unpair.2.unpair.2.unpair.2 i) 0
        = List.getD (rawTable p.unpair.2.unpair.1) i 0 := by
    have hR : PrimrecRel fun (i : ℕ) (p : ℕ) =>
        List.getD (rawTable p.unpair.2.unpair.2.unpair.1)
            (digitAt p.unpair.1 p.unpair.2.unpair.2.unpair.2 i) 0
          = List.getD (rawTable p.unpair.2.unpair.1) i 0 := by
      have hdig : Primrec fun q : ℕ × ℕ =>
          digitAt q.2.unpair.1 q.2.unpair.2.unpair.2.unpair.2 q.1 :=
        Primrec.nat_mod.comp
          (Primrec.nat_div.comp (hW.comp Primrec.snd)
            (hpow.comp (hN.comp Primrec.snd) Primrec.fst))
          (hN.comp Primrec.snd)
      have hf : Primrec fun q : ℕ × ℕ =>
          List.getD (rawTable q.2.unpair.2.unpair.2.unpair.1)
            (digitAt q.2.unpair.1 q.2.unpair.2.unpair.2.unpair.2 q.1) 0 :=
        (Primrec.list_getD 0).comp (primrec_rawTable.comp (hT1.comp Primrec.snd)) hdig
      have hg : Primrec fun q : ℕ × ℕ =>
          List.getD (rawTable q.2.unpair.2.unpair.1) q.1 0 :=
        (Primrec.list_getD 0).comp (primrec_rawTable.comp (hT0.comp Primrec.snd)) Primrec.fst
      exact PrimrecRel.comp Primrec.eq hf hg
    exact primrecPred_dup_nat hR hN
  exact hBij.and hMatch

set_option maxHeartbeats 1000000 in
-- Two multi-level `Nat.unpair`/`Nat.pair` chains meet in the composed term, so the kernel check
-- needs extra headroom (the same shape as `KE_labelledMarkingLens_le`'s nested packing).
/-- **The membership relation is primitive recursive**, over `(w, param)` with `param` packing
`(n, t0, t1)` — `primrec_isValid` at `param` and `w` rebuilt into one packed program. -/
private theorem primrec_isValid_rel :
    PrimrecRel fun (w param : ℕ) =>
      isValid param.unpair.1 param.unpair.2.unpair.1 param.unpair.2.unpair.2 w := by
  have hn' : Primrec fun q : ℕ × ℕ => q.2.unpair.1 :=
    Primrec.fst.comp (Primrec.unpair.comp Primrec.snd)
  have ht0' : Primrec fun q : ℕ × ℕ => q.2.unpair.2.unpair.1 :=
    Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp (Primrec.unpair.comp Primrec.snd)))
  have ht1' : Primrec fun q : ℕ × ℕ => q.2.unpair.2.unpair.2 :=
    Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp (Primrec.unpair.comp Primrec.snd)))
  have hw' : Primrec fun q : ℕ × ℕ => q.1 := Primrec.fst
  have hinner1 : Primrec fun q : ℕ × ℕ => Nat.pair (q.2.unpair.2.unpair.2) (q.1) :=
    Primrec₂.natPair.comp ht1' hw'
  have hinner2 : Primrec fun q : ℕ × ℕ =>
      Nat.pair (q.2.unpair.2.unpair.1) (Nat.pair (q.2.unpair.2.unpair.2) (q.1)) :=
    Primrec₂.natPair.comp ht0' hinner1
  have hfull : Primrec fun q : ℕ × ℕ =>
      Nat.pair (q.2.unpair.1) (Nat.pair (q.2.unpair.2.unpair.1)
        (Nat.pair (q.2.unpair.2.unpair.2) (q.1))) :=
    Primrec₂.natPair.comp hn' hinner2
  have hkey := primrec_isValid.comp hfull
  refine hkey.of_eq fun q => ?_
  simp only [Nat.unpair_pair]

/-- **The candidate list**: every numeral below `n ^ n` whose table is a valid coset element,
in the numeral's own order. Its members are exactly the coset `U · stabilizer (ℓ₀)`'s tables
(`candList_mem_iff`), and its length is bounded by the coset's size (`candList_length_le`). -/
private def candList (n t0 t1 : ℕ) : List ℕ :=
  (List.range (n ^ n)).filter (fun w => decide (isValid n t0 t1 w))

private theorem primrec_candList :
    Primrec fun p : ℕ => candList p.unpair.1 p.unpair.2.unpair.1 p.unpair.2.unpair.2 := by
  have hpow : Primrec₂ ((· ^ ·) : ℕ → ℕ → ℕ) := Primrec₂.unpaired'.1 Nat.Primrec.pow
  have hN : Primrec fun p : ℕ => p.unpair.1 := Primrec.fst.comp Primrec.unpair
  have hL : Primrec fun p : ℕ => List.range (p.unpair.1 ^ p.unpair.1) :=
    Primrec.list_range.comp (hpow.comp hN hN)
  have hfilt := (PrimrecRel.listFilter primrec_isValid_rel).comp hL Primrec.id
  exact hfilt.of_eq fun p => rfl

/-- **The tabulation, rebuilt from the packed program** `⟨n, t0, t1, idx⟩` — ONE fixed function of a
single natural number: filter the candidates and read off the `idx`-th one's table. -/
private def gradedTableFn (a : ℕ) : ℕ :=
  Encodable.encode (candTable a.unpair.1
    (List.getD (candList a.unpair.1 a.unpair.2.unpair.1 a.unpair.2.unpair.2.unpair.1)
      a.unpair.2.unpair.2.unpair.2 0))

set_option maxHeartbeats 1000000 in
-- same headroom reason as `primrec_isValid_rel`: multi-level packing meets `primrec_candList`.
private theorem primrec_gradedTableFn : Primrec gradedTableFn := by
  have hN : Primrec fun a : ℕ => a.unpair.1 := Primrec.fst.comp Primrec.unpair
  have hT0 : Primrec fun a : ℕ => a.unpair.2.unpair.1 :=
    Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))
  have hT1 : Primrec fun a : ℕ => a.unpair.2.unpair.2.unpair.1 :=
    Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp
      (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))))
  have hIdx : Primrec fun a : ℕ => a.unpair.2.unpair.2.unpair.2 :=
    Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp
      (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))))
  have hParam : Primrec fun a : ℕ =>
      Nat.pair a.unpair.1 (Nat.pair a.unpair.2.unpair.1 a.unpair.2.unpair.2.unpair.1) :=
    Primrec₂.natPair.comp hN (Primrec₂.natPair.comp hT0 hT1)
  have hCL : Primrec fun a : ℕ =>
      candList a.unpair.1 a.unpair.2.unpair.1 a.unpair.2.unpair.2.unpair.1 := by
    have := primrec_candList.comp hParam
    refine this.of_eq fun a => ?_
    simp only [Nat.unpair_pair]
  have hSel : Primrec fun a : ℕ =>
      List.getD (candList a.unpair.1 a.unpair.2.unpair.1 a.unpair.2.unpair.2.unpair.1)
        a.unpair.2.unpair.2.unpair.2 0 :=
    (Primrec.list_getD 0).comp hCL hIdx
  exact Primrec.encode.comp (primrec_candTable.comp hN hSel)

private theorem partrec_gradedTableFn : Nat.Partrec (fun a : ℕ => (gradedTableFn a : ℕ)) :=
  _root_.Partrec.nat_iff.mp (Primrec.to_comp primrec_gradedTableFn).partrec

/-- **The fixed graded-ledger builder code.** One program, independent of `n`, the world, and the
lens — the uniform constant the graded ledger's `O (1)` demands. -/
noncomputable def gradedBuilder : Nat.Partrec.Code :=
  Classical.choose (Nat.Partrec.Code.exists_code.mp partrec_gradedTableFn)

private theorem eval_gradedBuilder (a : ℕ) :
    Nat.Partrec.Code.eval gradedBuilder a = Part.some (gradedTableFn a) := by
  have h := congrFun (Classical.choose_spec
    (Nat.Partrec.Code.exists_code.mp partrec_gradedTableFn)) a
  simpa [gradedBuilder] using h

/-- **The world's own table, packed** — `U`, read as a bare `Fin n → Fin n` function and packed by
`packMarks` exactly as any candidate table is. -/
private def worldNumeral (U : Perm (Fin n)) : ℕ := packMarks (fun i : Fin n => U i)

private theorem worldNumeral_lt (hn : 0 < n) (U : Perm (Fin n)) : worldNumeral U < n ^ n :=
  packMarks_lt hn _

private theorem digitAt_worldNumeral (hn : 0 < n) (U : Perm (Fin n)) (i : Fin n) :
    digitAt n (worldNumeral U) (i : ℕ) = (U i : ℕ) :=
  digit_packMarks hn _ i

/-- **The world's own table is a valid candidate**: it is bijective (`U` is a permutation) and it
transports `ℓ₁`'s table to `ℓ₀`'s — `permCarries_frame_one`, read through the encode/decode round
trip and the base-`n` packing. Only the persistence identity is used. -/
private theorem isValid_worldNumeral (hn : 0 < n) {U : Perm (Fin n)} {ℓ : ℕ → Fin n → Fin m}
    (hpers : PermPersists U ℓ) :
    isValid n (lensCode (ℓ 0)) (lensCode (ℓ 1)) (worldNumeral U) := by
  constructor
  · rw [candBijBool_iff]
    intro i hi j hj hij hcontra
    have hdi : digitAt n (worldNumeral U) i = (U (⟨i, hi⟩ : Fin n) : ℕ) :=
      digitAt_worldNumeral hn U ⟨i, hi⟩
    have hdj : digitAt n (worldNumeral U) j = (U (⟨j, hj⟩ : Fin n) : ℕ) :=
      digitAt_worldNumeral hn U ⟨j, hj⟩
    rw [hdi, hdj] at hcontra
    exact hij (congrArg Fin.val (U.injective (Fin.val_injective hcontra)))
  · intro i hi
    have hdig : digitAt n (worldNumeral U) i = (U (⟨i, hi⟩ : Fin n) : ℕ) :=
      digitAt_worldNumeral hn U ⟨i, hi⟩
    have hget1 : List.getD (rawTable (lensCode (ℓ 1))) (U (⟨i, hi⟩ : Fin n) : ℕ) 0
        = (ℓ 1 (U ⟨i, hi⟩) : ℕ) := by
      rw [rawTable_lensCode, lensTable]; exact getD_map_finRange _ _
    have hget0 : List.getD (rawTable (lensCode (ℓ 0))) i 0 = (ℓ 0 (⟨i, hi⟩ : Fin n) : ℕ) := by
      rw [rawTable_lensCode, lensTable]
      exact getD_map_finRange (fun y : Fin n => (ℓ 0 y : ℕ)) ⟨i, hi⟩
    rw [hdig, hget1, hget0]
    have hstep := hpers 1 (⟨i, hi⟩ : Fin n)
    rw [pow_one] at hstep
    exact congrArg (fun x : Fin m => (x : ℕ)) hstep

/-- **The candidate permutation**: a valid numeral's own bijective table, packaged as a genuine
`Perm (Fin n)`. Junk (`1`) off the domain where `candBijBool` fails, since `Function.Bijective`
needs the certificate — only its behaviour on valid numerals is ever used. -/
private noncomputable def candPerm (n w : ℕ) : Perm (Fin n) :=
  if h : 0 < n ∧ candBijBool n w = true then
    Equiv.ofBijective (fun i : Fin n => (⟨digitAt n w i, Nat.mod_lt _ h.1⟩ : Fin n))
      (candTable_bijective h.1 h.2)
  else 1

private theorem candPerm_apply {n w : ℕ} (hn : 0 < n) (hb : candBijBool n w = true) (i : Fin n) :
    (candPerm n w i : ℕ) = digitAt n w i := by
  rw [candPerm, dif_pos ⟨hn, hb⟩]; rfl

/-- **The coset injection**: a valid numeral's candidate permutation, composed with `U⁻¹`, lands in
`ℓ₀`'s fiber-stabilizer — the matching condition says `ℓ₁ ∘ (candPerm) = ℓ₀`, and
`permCarries_frame_one` reads `ℓ₁` itself as `ℓ₀ ∘ U⁻¹`, so `U⁻¹ * candPerm` fixes every `ℓ₀`-fiber
setwise. Only the persistence identity is used. -/
private theorem candPerm_mem_stabilizer {n w : ℕ} (hn : 0 < n) {U : Perm (Fin n)}
    {ℓ : ℕ → Fin n → Fin m} (hpers : PermPersists U ℓ)
    (hv : isValid n (lensCode (ℓ 0)) (lensCode (ℓ 1)) w) :
    U⁻¹ * candPerm n w ∈ stabilizer (Perm (Fin n)) (ℓ 0) := by
  rw [mem_stabilizer_lens]
  intro x
  rw [Equiv.Perm.mul_apply]
  have hb := hv.1
  have hmatch := hv.2
  have h1 : ℓ 1 (candPerm n w x) = ℓ 0 x := by
    have hi : (x : ℕ) < n := x.2
    have hget1 : List.getD (rawTable (lensCode (ℓ 1))) (digitAt n w x) 0
        = (ℓ 1 (⟨digitAt n w x, Nat.mod_lt _ hn⟩ : Fin n) : ℕ) := by
      rw [rawTable_lensCode, lensTable]
      exact getD_map_finRange (fun y : Fin n => (ℓ 1 y : ℕ)) ⟨digitAt n w x, Nat.mod_lt _ hn⟩
    have hget0 : List.getD (rawTable (lensCode (ℓ 0))) (x : ℕ) 0 = (ℓ 0 x : ℕ) := by
      rw [rawTable_lensCode, lensTable]; exact getD_map_finRange _ _
    have hspec := hmatch x hi
    rw [hget1, hget0] at hspec
    have hval : (⟨digitAt n w x, Nat.mod_lt _ hn⟩ : Fin n) = candPerm n w x := by
      apply Fin.val_injective
      rw [candPerm_apply hn hb]
    rw [hval] at hspec
    exact Fin.val_injective hspec
  have h2 : ℓ 1 = ℓ 0 ∘ ⇑U⁻¹ := permCarries_frame_one hpers
  rw [h2] at h1
  simpa using h1

/-- **Injectivity of the coset map**: distinct valid numerals give distinct stabilizer cosets. Two
valid `w₁ ≠ w₂` with the same `U⁻¹ * candPerm` would give the same `candPerm`, hence the same
`n`-digit table (`Equiv.ext`), hence — by the base-`n` packing's injectivity — the same numeral. -/
private theorem candPerm_injOn {n : ℕ} (hn : 0 < n) (t0 t1 : ℕ) (U : Perm (Fin n)) :
    Set.InjOn (fun w => U⁻¹ * candPerm n w) {w | w < n ^ n ∧ isValid n t0 t1 w} := by
  intro w1 hw1 w2 hw2 heq
  have hb1 : candBijBool n w1 = true := hw1.2.1
  have hb2 : candBijBool n w2 = true := hw2.2.1
  have hcp : candPerm n w1 = candPerm n w2 := by
    have := mul_left_cancel (a := U⁻¹) heq
    exact this
  have hdig : ∀ i : Fin n, digitAt n w1 (i : ℕ) = digitAt n w2 (i : ℕ) := by
    intro i
    rw [← candPerm_apply hn hb1 i, ← candPerm_apply hn hb2 i, hcp]
  apply candTable_injOn hw1.1 hw2.1
  change (List.range n).map (digitAt n w1) = (List.range n).map (digitAt n w2)
  refine List.map_congr_left fun j hj => ?_
  exact hdig ⟨j, List.mem_range.mp hj⟩

/-- **The graded ledger's coset bound**: the coset that pins `U` down against a reference frame
`ℓ₀` has size at most `∏ᵢ (fiberᵢ)!` — the count `card_stabilizer_lens` gives Lemma 7.1's
stabilizer, reached here by injecting every valid candidate numeral into it. Only the persistence
identity is used. -/
private theorem candList_length_le (hn : 0 < n) {U : Perm (Fin n)} {ℓ : ℕ → Fin n → Fin m}
    (hpers : PermPersists U ℓ) :
    (candList n (lensCode (ℓ 0)) (lensCode (ℓ 1))).length
      ≤ Nat.card ↥(stabilizer (Perm (Fin n)) (ℓ 0)) := by
  classical
  set t0 := lensCode (ℓ 0) with ht0
  set t1 := lensCode (ℓ 1) with ht1
  have : Fintype ↥(stabilizer (Perm (Fin n)) (ℓ 0)) := Fintype.ofFinite _
  have hnodup : (candList n t0 t1).Nodup := List.nodup_range.filter _
  have hmem : ∀ w ∈ (candList n t0 t1).toFinset, w < n ^ n ∧ isValid n t0 t1 w := by
    intro w hw
    rw [List.mem_toFinset, candList, List.mem_filter, List.mem_range, decide_eq_true_eq] at hw
    exact hw
  set f : ℕ → ↥(stabilizer (Perm (Fin n)) (ℓ 0)) := fun w =>
    if h : isValid n t0 t1 w then ⟨U⁻¹ * candPerm n w, candPerm_mem_stabilizer hn hpers h⟩
    else ⟨1, Subgroup.one_mem _⟩ with hf
  have hcard := Finset.card_le_card_of_injOn f
    (s := (candList n t0 t1).toFinset) (t := Finset.univ)
    (fun w _ => Finset.mem_univ (f w))
    (by
      intro w1 hw1 w2 hw2 heq
      rw [Finset.mem_coe] at hw1 hw2
      have h1 := hmem w1 hw1
      have h2 := hmem w2 hw2
      have hfw1 : f w1 = ⟨U⁻¹ * candPerm n w1, candPerm_mem_stabilizer hn hpers h1.2⟩ :=
        dif_pos h1.2
      have hfw2 : f w2 = ⟨U⁻¹ * candPerm n w2, candPerm_mem_stabilizer hn hpers h2.2⟩ :=
        dif_pos h2.2
      rw [hfw1, hfw2, Subtype.mk_eq_mk] at heq
      exact candPerm_injOn hn t0 t1 U ⟨h1.1, h1.2⟩ ⟨h2.1, h2.2⟩ heq)
  rw [← List.toFinset_card_of_nodup hnodup, Nat.card_eq_fintype_card]
  simpa using hcard

/-- **The graded ledger** ([Persistence] Open problem 8.4's design; Theorem 6.3's argument at
EVERY carried family, maximal or not). The two frames pin `U` down only to a coset of `ℓ₀`'s
fiber-stabilizer, of size `∏ᵢ (fiberᵢ)!` (`card_stabilizer_lens`): a fixed decoder recovers `U`'s
table from the two frame tables plus a coset INDEX, and the index costs `O (Nat.size (∏ᵢ fiberᵢ!))`
bits — logarithmic in the coset, not linear (the `bconst` loading precedent of
`KE_markingLens_le`), no genericity, no maximality. `ledger_K` is the case `∏ᵢ (fiberᵢ)! = 1`
(`ledger_graded_faithful`). Only the persistence identity is used, not `PermCarries`'s surjectivity
of `ℓ 0` — `ledger_graded_lossy` is where that generality is spent, pricing a lossy guest's own
reduction to a persistent one. -/
theorem ledger_graded (hn : 0 < n) {U : Perm (Fin n)} {ℓ : ℕ → Fin n → Fin m}
    (hpers : PermPersists U ℓ) :
    KE (lensCode U) ≤ KE (lensCode (ℓ 0)) + KE (lensCode (ℓ 1))
      + (15 + elen dbl) * Nat.size (∏ i : Fin m, (Nat.card {x : Fin n // ℓ 0 x = i})!)
      + (15 + elen dbl) * Nat.size n
      + (elen gradedBuilder + 2 * (15 + elen dbl) + 39) := by
  set t0 := lensCode (ℓ 0) with ht0
  set t1 := lensCode (ℓ 1) with ht1
  set N := ∏ i : Fin m, (Nat.card {x : Fin n // ℓ 0 x = i})! with hNdef
  have hvalid : isValid n t0 t1 (worldNumeral U) := isValid_worldNumeral hn hpers
  have hlt : worldNumeral U < n ^ n := worldNumeral_lt hn U
  have hmem : worldNumeral U ∈ candList n t0 t1 := by
    rw [candList, List.mem_filter, List.mem_range, decide_eq_true_eq]
    exact ⟨hlt, hvalid⟩
  obtain ⟨idx, hidxlt, hidxeq⟩ := List.getElem_of_mem hmem
  have hlenle : (candList n t0 t1).length ≤ N := by
    rw [hNdef]
    calc (candList n t0 t1).length ≤ Nat.card ↥(stabilizer (Perm (Fin n)) (ℓ 0)) :=
          candList_length_le hn hpers
      _ = N := card_stabilizer_lens (ℓ 0)
  have hidxN : idx < N := lt_of_lt_of_le hidxlt hlenle
  have hgetD : List.getD (candList n t0 t1) idx 0 = worldNumeral U := by
    rw [List.getD_eq_getElem _ _ hidxlt]; exact hidxeq
  have heval : gradedTableFn (Nat.pair n (Nat.pair t0 (Nat.pair t1 idx))) = lensCode U := by
    rw [gradedTableFn]
    simp only [Nat.unpair_pair]
    rw [hgetD]
    exact congrArg Encodable.encode (candTable_packMarks hn U)
  obtain ⟨c0, hc0, hlc0⟩ := exists_min_E t0
  obtain ⟨c1, hc1, hlc1⟩ := exists_min_E t1
  have hz : eval zero (0 : ℕ) = Part.some 0 := rfl
  have hn' : eval (bconst n) 0 = Part.some n := eval_bconst n 0
  have h0 : eval (comp c0 zero) 0 = Part.some t0 := (eval_comp_some hz).trans hc0
  have h1 : eval (comp c1 zero) 0 = Part.some t1 := (eval_comp_some hz).trans hc1
  have hb : eval (bconst idx) 0 = Part.some idx := eval_bconst idx 0
  have hpair3 : eval (pair (comp c1 zero) (bconst idx)) 0 = Part.some (Nat.pair t1 idx) := by
    change Nat.pair <$> _ <*> _ = _
    rw [h1, hb]; simp [Seq.seq]
  have hpair2 : eval (pair (comp c0 zero) (pair (comp c1 zero) (bconst idx))) 0
      = Part.some (Nat.pair t0 (Nat.pair t1 idx)) := by
    change Nat.pair <$> _ <*> _ = _
    rw [h0, hpair3]; simp [Seq.seq]
  have hpair1 : eval (pair (bconst n) (pair (comp c0 zero) (pair (comp c1 zero) (bconst idx)))) 0
      = Part.some (Nat.pair n (Nat.pair t0 (Nat.pair t1 idx))) := by
    change Nat.pair <$> _ <*> _ = _
    rw [hn', hpair2]; simp [Seq.seq]
  have hcomp : Computes
      (comp gradedBuilder
        (pair (bconst n) (pair (comp c0 zero) (pair (comp c1 zero) (bconst idx)))))
      (lensCode U) := by
    change eval (comp gradedBuilder
      (pair (bconst n) (pair (comp c0 zero) (pair (comp c1 zero) (bconst idx))))) 0 = _
    rw [eval_comp_some hpair1, eval_gradedBuilder, heval]
  have hle := KE_le hcomp
  rw [E_len_comp, E_len_pair, E_len_pair, E_len_comp, E_len_pair, E_len_comp] at hle
  have hzlen : elen (zero : Code) = 3 := rfl
  have hbc := elen_bconst_le idx
  have hbn := elen_bconst_le n
  have hidxsize : Nat.size idx ≤ Nat.size N := Nat.size_le_size (le_of_lt hidxN)
  have hidxsize' : (15 + elen dbl) * Nat.size idx ≤ (15 + elen dbl) * Nat.size N :=
    Nat.mul_le_mul_left _ hidxsize
  rw [hzlen, hlc0, hlc1] at hle
  omega

/-- **Non-vacuity: the graded ledger recovers the maximal ledger's shape.** At singleton fibers
(`ℓ₀` bijective) the coset is trivial — `∏ᵢ (fiberᵢ)! = 1` — so the coset INDEX contributes only
its own fixed encoding cost, and the bound collapses to `ledger_K`'s two-frames-plus-`O (1)` shape,
up to the decoder's `O (Nat.size n)` (this decoder, unlike `ledger_K`'s table inversion, must be
told `n` up front to bound its search). -/
theorem ledger_graded_faithful (hn : 0 < n) {U : Perm (Fin n)} {ℓ : ℕ → Fin n → Fin m}
    (hcar : PermCarries U ℓ) (hbij : Function.Bijective (ℓ 0)) :
    KE (lensCode U) ≤ KE (lensCode (ℓ 0)) + KE (lensCode (ℓ 1))
      + (15 + elen dbl) * Nat.size n
      + (elen gradedBuilder + 3 * (15 + elen dbl) + 39) := by
  have hone : ∏ i : Fin m, (Nat.card {x : Fin n // ℓ 0 x = i})! = 1 := by
    refine Finset.prod_eq_one fun i _ => ?_
    have hcard : Nat.card {x : Fin n // ℓ 0 x = i} = 1 := by
      obtain ⟨x, hx, huniq⟩ := hbij.existsUnique i
      exact Nat.card_eq_one_iff_exists.mpr ⟨⟨x, hx⟩, fun y => Subtype.ext (huniq y y.2)⟩
    rw [hcard]; rfl
  have hbound := ledger_graded hn hcar.2
  rw [hone] at hbound
  simp only [Nat.size_one, Nat.mul_one] at hbound
  omega

/-! ## The ledger at any frames ([Persistence] §6, Theorem 6.5) -/

/-- **Consistency with the frames held at `bs`** ([Persistence] §6, Theorem 6.5): a permutation `V`
is consistent when it carries every held time `t`'s frame back to the frame at any OTHER held time
`t'` one step earlier — no ordering, sortedness, or `Nodup` requirement on `bs`, since a repeated or
misordered time imposes no different a constraint than the times it duplicates. -/
def ConsistentWith (ℓ : ℕ → Fin n → Fin m) (bs : List ℕ) : Set (Perm (Fin n)) :=
  {V | ∀ t ∈ bs, ∀ t' ∈ bs, t = t' + 1 → ∀ x, ℓ t (V x) = ℓ t' x}

/-- **One pair's transport test**, `Bool`-valued: skip the pair when `bs`'s `j`-th and `j'`-th
entries are not one apart, else require the `j`-th frame's table to transport the `j'`-th frame's
table exactly as `pairsOK`'s bounded search over `Fin n` reads it — `pairOK`'s own shape, one level
further from the raw digits. -/
private def triOK (n : ℕ) (Ts bs : List ℕ) (w j j' : ℕ) : Bool :=
  (!decide (bs.getD j 0 = bs.getD j' 0 + 1)) ||
    (List.range n).all fun i =>
      decide ((rawTable (Ts.getD j 0)).getD (digitAt n w i) 0
        = (rawTable (Ts.getD j' 0)).getD i 0)

set_option maxHeartbeats 1000000 in
-- Multi-level packing meets the (now triple, not double) nested fold — the same headroom
-- `primrec_isValid_rel`/`primrec_gradedTableFn` need for their own packed compositions.
private theorem primrec_triOK :
    Primrec fun p : (ℕ × List ℕ × List ℕ × ℕ) × ℕ × ℕ =>
      triOK p.1.1 p.1.2.1 p.1.2.2.1 p.1.2.2.2 p.2.1 p.2.2 := by
  have hn : Primrec fun p : (ℕ × List ℕ × List ℕ × ℕ) × ℕ × ℕ => p.1.1 :=
    Primrec.fst.comp Primrec.fst
  have hTs : Primrec fun p : (ℕ × List ℕ × List ℕ × ℕ) × ℕ × ℕ => p.1.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have hbs : Primrec fun p : (ℕ × List ℕ × List ℕ × ℕ) × ℕ × ℕ => p.1.2.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
  have hw : Primrec fun p : (ℕ × List ℕ × List ℕ × ℕ) × ℕ × ℕ => p.1.2.2.2 :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
  have hj : Primrec fun p : (ℕ × List ℕ × List ℕ × ℕ) × ℕ × ℕ => p.2.1 :=
    Primrec.fst.comp Primrec.snd
  have hj' : Primrec fun p : (ℕ × List ℕ × List ℕ × ℕ) × ℕ × ℕ => p.2.2 :=
    Primrec.snd.comp Primrec.snd
  have hbsj : Primrec fun p : (ℕ × List ℕ × List ℕ × ℕ) × ℕ × ℕ => p.1.2.2.1.getD p.2.1 0 :=
    (Primrec.list_getD 0).comp hbs hj
  have hbsj' : Primrec fun p : (ℕ × List ℕ × List ℕ × ℕ) × ℕ × ℕ => p.1.2.2.1.getD p.2.2 0 :=
    (Primrec.list_getD 0).comp hbs hj'
  have hcond : Primrec fun p : (ℕ × List ℕ × List ℕ × ℕ) × ℕ × ℕ =>
      decide (p.1.2.2.1.getD p.2.1 0 = p.1.2.2.1.getD p.2.2 0 + 1) :=
    Primrec.eq.decide.comp hbsj (Primrec.succ.comp hbsj')
  have hTj : Primrec fun p : (ℕ × List ℕ × List ℕ × ℕ) × ℕ × ℕ =>
      rawTable (p.1.2.1.getD p.2.1 0) :=
    primrec_rawTable.comp ((Primrec.list_getD 0).comp hTs hj)
  have hTj' : Primrec fun p : (ℕ × List ℕ × List ℕ × ℕ) × ℕ × ℕ =>
      rawTable (p.1.2.1.getD p.2.2 0) :=
    primrec_rawTable.comp ((Primrec.list_getD 0).comp hTs hj')
  have hinner : Primrec fun p : ((ℕ × List ℕ × List ℕ × ℕ) × ℕ × ℕ) × ℕ =>
      decide ((rawTable (p.1.1.2.1.getD p.1.2.1 0)).getD (digitAt p.1.1.1 p.1.1.2.2.2 p.2) 0
        = (rawTable (p.1.1.2.1.getD p.1.2.2 0)).getD p.2 0) := by
    have hn2 : Primrec fun p : ((ℕ × List ℕ × List ℕ × ℕ) × ℕ × ℕ) × ℕ => p.1.1.1 :=
      hn.comp Primrec.fst
    have hw2 : Primrec fun p : ((ℕ × List ℕ × List ℕ × ℕ) × ℕ × ℕ) × ℕ => p.1.1.2.2.2 :=
      hw.comp Primrec.fst
    have hi : Primrec fun p : ((ℕ × List ℕ × List ℕ × ℕ) × ℕ × ℕ) × ℕ => p.2 := Primrec.snd
    have hpow : Primrec₂ ((· ^ ·) : ℕ → ℕ → ℕ) := Primrec₂.unpaired'.1 Nat.Primrec.pow
    have hdig : Primrec fun p : ((ℕ × List ℕ × List ℕ × ℕ) × ℕ × ℕ) × ℕ =>
        digitAt p.1.1.1 p.1.1.2.2.2 p.2 :=
      Primrec.nat_mod.comp (Primrec.nat_div.comp hw2 (hpow.comp hn2 hi)) hn2
    have hTj2 : Primrec fun p : ((ℕ × List ℕ × List ℕ × ℕ) × ℕ × ℕ) × ℕ =>
        rawTable (p.1.1.2.1.getD p.1.2.1 0) := hTj.comp Primrec.fst
    have hTj'2 : Primrec fun p : ((ℕ × List ℕ × List ℕ × ℕ) × ℕ × ℕ) × ℕ =>
        rawTable (p.1.1.2.1.getD p.1.2.2 0) := hTj'.comp Primrec.fst
    have hL : Primrec fun p : ((ℕ × List ℕ × List ℕ × ℕ) × ℕ × ℕ) × ℕ =>
        (rawTable (p.1.1.2.1.getD p.1.2.1 0)).getD (digitAt p.1.1.1 p.1.1.2.2.2 p.2) 0 :=
      (Primrec.list_getD 0).comp hTj2 hdig
    have hR : Primrec fun p : ((ℕ × List ℕ × List ℕ × ℕ) × ℕ × ℕ) × ℕ =>
        (rawTable (p.1.1.2.1.getD p.1.2.2 0)).getD p.2 0 :=
      (Primrec.list_getD 0).comp hTj'2 hi
    exact Primrec.eq.decide.comp hL hR
  have hall : Primrec fun p : (ℕ × List ℕ × List ℕ × ℕ) × ℕ × ℕ =>
      (List.range p.1.1).all fun i =>
        decide ((rawTable (p.1.2.1.getD p.2.1 0)).getD (digitAt p.1.1 p.1.2.2.2 i) 0
          = (rawTable (p.1.2.1.getD p.2.2 0)).getD i 0) :=
    primrec_list_all (Primrec.list_range.comp hn) hinner.to₂
  exact ((Primrec.dom_bool₂ (fun (b1 b2 : Bool) => (!b1) || b2)).comp hcond hall).of_eq
    fun p => by simp [triOK]

/-- **The triple-fold check** ([Persistence] §6, Theorem 6.5's proof, `V`'s constraint at held
times one apart): every pair of positions in `bs` whose values are one apart transports the
earlier position's frame table to the later's — `candBijBool`'s own bounded-search style, folded
once more, over `bs`'s own positions rather than a fixed pair. -/
private def pairsOK (n : ℕ) (Ts bs : List ℕ) (w : ℕ) : Bool :=
  (List.range bs.length).all fun j =>
    (List.range bs.length).all fun j' => triOK n Ts bs w j j'

set_option maxHeartbeats 1000000 in
-- Same headroom reason as `primrec_triOK`: the packed program meets the fold twice more.
private theorem primrec_pairsOK :
    Primrec fun p : ℕ × List ℕ × List ℕ × ℕ => pairsOK p.1 p.2.1 p.2.2.1 p.2.2.2 := by
  have hn : Primrec fun p : ℕ × List ℕ × List ℕ × ℕ => p.1 := Primrec.fst
  have hTs : Primrec fun p : ℕ × List ℕ × List ℕ × ℕ => p.2.1 := Primrec.fst.comp Primrec.snd
  have hbs : Primrec fun p : ℕ × List ℕ × List ℕ × ℕ => p.2.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hw : Primrec fun p : ℕ × List ℕ × List ℕ × ℕ => p.2.2.2 :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have hinnerAll : Primrec fun q : (ℕ × List ℕ × List ℕ × ℕ) × ℕ =>
      (List.range q.1.2.2.1.length).all fun j' =>
        triOK q.1.1 q.1.2.1 q.1.2.2.1 q.1.2.2.2 q.2 j' := by
    have hq1 : Primrec fun q : (ℕ × List ℕ × List ℕ × ℕ) × ℕ => q.1 := Primrec.fst
    have hq2 : Primrec fun q : (ℕ × List ℕ × List ℕ × ℕ) × ℕ => q.2 := Primrec.snd
    have hbsq : Primrec fun q : (ℕ × List ℕ × List ℕ × ℕ) × ℕ => q.1.2.2.1 := hbs.comp hq1
    have hlen : Primrec fun q : (ℕ × List ℕ × List ℕ × ℕ) × ℕ =>
        List.range q.1.2.2.1.length := Primrec.list_range.comp (Primrec.list_length.comp hbsq)
    have htriOK2 : Primrec₂ fun (q : (ℕ × List ℕ × List ℕ × ℕ) × ℕ) (j' : ℕ) =>
        triOK q.1.1 q.1.2.1 q.1.2.2.1 q.1.2.2.2 q.2 j' :=
      primrec_triOK.comp ((Primrec.fst.comp Primrec.fst).pair
        ((Primrec.snd.comp Primrec.fst).pair Primrec.snd))
    exact primrec_list_all hlen htriOK2
  have houterAll : Primrec fun p : ℕ × List ℕ × List ℕ × ℕ =>
      (List.range p.2.2.1.length).all fun j =>
        (List.range p.2.2.1.length).all fun j' => triOK p.1 p.2.1 p.2.2.1 p.2.2.2 j j' := by
    have hlen : Primrec fun p : ℕ × List ℕ × List ℕ × ℕ => List.range p.2.2.1.length :=
      Primrec.list_range.comp (Primrec.list_length.comp hbs)
    have hg : Primrec₂ fun (p : ℕ × List ℕ × List ℕ × ℕ) (j : ℕ) =>
        (List.range p.2.2.1.length).all fun j' => triOK p.1 p.2.1 p.2.2.1 p.2.2.2 j j' :=
      hinnerAll.comp (Primrec.pair Primrec.fst Primrec.snd)
    exact primrec_list_all hlen hg
  exact houterAll.of_eq fun p => rfl

/-- **`pairsOK`, unfolded** — the raw pairwise-transport statement the `Bool` search certifies. -/
private theorem pairsOK_iff (n : ℕ) (Ts bs : List ℕ) (w : ℕ) :
    pairsOK n Ts bs w = true ↔
      ∀ j < bs.length, ∀ j' < bs.length, bs.getD j 0 = bs.getD j' 0 + 1 →
        ∀ i < n, (rawTable (Ts.getD j 0)).getD (digitAt n w i) 0
          = (rawTable (Ts.getD j' 0)).getD i 0 := by
  simp only [pairsOK, List.all_eq_true, decide_eq_true_eq, List.mem_range, triOK,
    Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not]
  constructor
  · intro h j hj j' hj' heq i hi
    rcases h j hj j' hj' with hne | hok
    · exact absurd heq hne
    · exact hok i hi
  · intro h j hj j' hj'
    by_cases heq : bs.getD j 0 = bs.getD j' 0 + 1
    · right; exact h j hj j' hj' heq
    · left; exact heq

/-- **A candidate is valid for the itinerary**: its table is a genuine permutation AND transports
every held-time pair's frame table as `pairsOK` requires — the two-frame `isValid`'s own shape, at
`bs`'s own list of held frames rather than a fixed pair. -/
private def isValidItin (n : ℕ) (Ts bs : List ℕ) (w : ℕ) : Prop :=
  candBijBool n w = true ∧ pairsOK n Ts bs w = true

private instance decIsValidItin (n : ℕ) (Ts bs : List ℕ) (w : ℕ) :
    Decidable (isValidItin n Ts bs w) := by unfold isValidItin; infer_instance

/-- **The itinerary's candidate list**: every numeral below `n ^ n` whose table is a valid
itinerary member, in the numeral's own order — `candList`'s own shape, at `bs`'s own list of held
frames. -/
private def candListItin (n : ℕ) (Ts bs : List ℕ) : List ℕ :=
  (List.range (n ^ n)).filter (fun w => decide (isValidItin n Ts bs w))

set_option maxHeartbeats 1000000 in
-- multi-level packing meets the triple fold, same reason as primrec_triOK/primrec_pairsOK.
private theorem primrec_candListItin :
    Primrec fun p : ℕ × List ℕ × List ℕ => candListItin p.1 p.2.1 p.2.2 := by
  have hpow : Primrec₂ ((· ^ ·) : ℕ → ℕ → ℕ) := Primrec₂.unpaired'.1 Nat.Primrec.pow
  have hn : Primrec fun p : ℕ × List ℕ × List ℕ => p.1 := Primrec.fst
  have hTs : Primrec fun p : ℕ × List ℕ × List ℕ => p.2.1 := Primrec.fst.comp Primrec.snd
  have hbs : Primrec fun p : ℕ × List ℕ × List ℕ => p.2.2 := Primrec.snd.comp Primrec.snd
  have hL : Primrec fun p : ℕ × List ℕ × List ℕ => List.range (p.1 ^ p.1) :=
    Primrec.list_range.comp (hpow.comp hn hn)
  have hgw : Primrec fun q : ℕ × ℕ × List ℕ × List ℕ => q.1 := Primrec.fst
  have hgn : Primrec fun q : ℕ × ℕ × List ℕ × List ℕ => q.2.1 := Primrec.fst.comp Primrec.snd
  have hgTs : Primrec fun q : ℕ × ℕ × List ℕ × List ℕ => q.2.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hgbs : Primrec fun q : ℕ × ℕ × List ℕ × List ℕ => q.2.2.2 :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have hBij : PrimrecPred fun q : ℕ × ℕ × List ℕ × List ℕ => candBijBool q.2.1 q.1 = true :=
    Primrec.eq.comp (primrec_candBijBool.comp hgn hgw) (Primrec.const true)
  have hPairs : PrimrecPred fun q : ℕ × ℕ × List ℕ × List ℕ =>
      pairsOK q.2.1 q.2.2.1 q.2.2.2 q.1 = true :=
    Primrec.eq.comp (primrec_pairsOK.comp (hgn.pair (hgTs.pair (hgbs.pair hgw))))
      (Primrec.const true)
  have hR : PrimrecRel fun (w : ℕ) (param : ℕ × List ℕ × List ℕ) =>
      isValidItin param.1 param.2.1 param.2.2 w := hBij.and hPairs
  have hfilt := (PrimrecRel.listFilter hR).comp hL (Primrec.pair hn (Primrec.pair hTs hbs))
  exact hfilt.of_eq fun p => rfl

/-- **The itinerary tabulation, rebuilt from the packed program** `⟨n, Ts, bs, idx⟩` — ONE fixed
function of a single natural number, `Ts`/`bs` decoded as `List ℕ`: filter the candidates and read
off the `idx`-th one's table — `gradedTableFn`'s own shape, at a variable-length list of held
frames rather than a fixed pair. -/
private def itinTableFn (a : ℕ) : ℕ :=
  Encodable.encode (candTable a.unpair.1
    (List.getD (candListItin a.unpair.1
        ((Encodable.decode (α := List ℕ) a.unpair.2.unpair.1).getD [])
        ((Encodable.decode (α := List ℕ) a.unpair.2.unpair.2.unpair.1).getD []))
      a.unpair.2.unpair.2.unpair.2 0))

private theorem primrec_itinTableFn : Primrec itinTableFn := by
  have hN : Primrec fun a : ℕ => a.unpair.1 := Primrec.fst.comp Primrec.unpair
  have hdecTs : Primrec fun a : ℕ =>
      (Encodable.decode (α := List ℕ) a.unpair.2.unpair.1).getD [] :=
    Primrec.option_getD.comp
      (Primrec.decode.comp
        (Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))))
      (Primrec.const [])
  have hdecbs : Primrec fun a : ℕ =>
      (Encodable.decode (α := List ℕ) a.unpair.2.unpair.2.unpair.1).getD [] :=
    Primrec.option_getD.comp
      (Primrec.decode.comp (Primrec.fst.comp (Primrec.unpair.comp
        (Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))))))
      (Primrec.const [])
  have hIdx : Primrec fun a : ℕ => a.unpair.2.unpair.2.unpair.2 :=
    Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp
      (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))))
  have hCL : Primrec fun a : ℕ => candListItin a.unpair.1
      ((Encodable.decode (α := List ℕ) a.unpair.2.unpair.1).getD [])
      ((Encodable.decode (α := List ℕ) a.unpair.2.unpair.2.unpair.1).getD []) :=
    primrec_candListItin.comp (hN.pair (hdecTs.pair hdecbs))
  have hSel : Primrec fun a : ℕ => List.getD (candListItin a.unpair.1
      ((Encodable.decode (α := List ℕ) a.unpair.2.unpair.1).getD [])
      ((Encodable.decode (α := List ℕ) a.unpair.2.unpair.2.unpair.1).getD []))
      a.unpair.2.unpair.2.unpair.2 0 :=
    (Primrec.list_getD 0).comp hCL hIdx
  exact Primrec.encode.comp (primrec_candTable.comp hN hSel)

private theorem partrec_itinTableFn : Nat.Partrec (fun a : ℕ => (itinTableFn a : ℕ)) :=
  _root_.Partrec.nat_iff.mp (Primrec.to_comp primrec_itinTableFn).partrec

/-- **The fixed itinerary builder code.** One program, independent of `n`, the world, the lens
family, and the held times `bs`. -/
noncomputable def itinBuilder : Nat.Partrec.Code :=
  Classical.choose (Nat.Partrec.Code.exists_code.mp partrec_itinTableFn)

private theorem eval_itinBuilder (a : ℕ) :
    Nat.Partrec.Code.eval itinBuilder a = Part.some (itinTableFn a) := by
  have h := congrFun (Classical.choose_spec
    (Nat.Partrec.Code.exists_code.mp partrec_itinTableFn)) a
  simpa [itinBuilder] using h

/-- **The fixed range code**: independent of `k`, it expands `k`'s own binary numeral into the
encoded list `List.range k` — what restores Theorem 6.5(i)'s `O (log k)` term, in place of loading
`k` separate times. -/
noncomputable def rangeCode : Nat.Partrec.Code :=
  Classical.choose (Nat.Partrec.Code.exists_code.mp
    (_root_.Partrec.nat_iff.mp (Primrec.to_comp
      (Primrec.encode.comp Primrec.list_range)).partrec))

/-- `rangeCode`'s evaluation law: consumed outside this module by
`GrowingPrice.exists_qualifying_pair_of_pos`'s witness, which prices the identity lens
`id : Fin N → Fin N` (`lensCode_id`) the same way this module prices `k`'s own numeral — hence
public, unlike its `itinBuilder`/`markBuilder` siblings. -/
theorem eval_rangeCode (k : ℕ) :
    Nat.Partrec.Code.eval rangeCode k = Part.some (Encodable.encode (List.range k)) := by
  have h := congrFun (Classical.choose_spec (Nat.Partrec.Code.exists_code.mp
    (_root_.Partrec.nat_iff.mp (Primrec.to_comp
      (Primrec.encode.comp Primrec.list_range)).partrec))) k
  simpa [rangeCode] using h

/-- **The frame-table chain**, `[] ↦ zero`, `t :: r ↦ comp succ (pair (comp (c t) zero) ⟨r⟩)` —
exploiting `Encodable.encode (a :: l) = (Nat.pair (encode a) (encode l)).succ` to compute the
encoded list of frame tables directly, one `c t` per element. -/
private def tableChain (c : ℕ → Nat.Partrec.Code) : List ℕ → Nat.Partrec.Code
  | [] => Nat.Partrec.Code.zero
  | t :: r => Nat.Partrec.Code.comp Nat.Partrec.Code.succ
      (Nat.Partrec.Code.pair (Nat.Partrec.Code.comp (c t) Nat.Partrec.Code.zero) (tableChain c r))

private theorem elen_tableChain (c : ℕ → Nat.Partrec.Code) (bs : List ℕ) :
    elen (tableChain c bs) = 3 + 15 * bs.length + (bs.map fun t => elen (c t)).sum := by
  induction bs with
  | nil => rfl
  | cons t r ih =>
    change elen (Nat.Partrec.Code.comp Nat.Partrec.Code.succ
      (Nat.Partrec.Code.pair (Nat.Partrec.Code.comp (c t) Nat.Partrec.Code.zero)
        (tableChain c r))) = _
    rw [E_len_comp, E_len_pair, E_len_comp]
    simp only [List.length_cons, List.map_cons, List.sum_cons]
    have hz : elen (Nat.Partrec.Code.zero : Nat.Partrec.Code) = 3 := rfl
    have hs : elen (Nat.Partrec.Code.succ : Nat.Partrec.Code) = 3 := rfl
    rw [hz, hs, ih]
    ring

private theorem eval_tableChain (c : ℕ → Nat.Partrec.Code) (f : ℕ → ℕ) (bs : List ℕ)
    (hc : ∀ t ∈ bs, (c t).eval 0 = Part.some (f t)) :
    (tableChain c bs).eval 0 = Part.some (Encodable.encode (bs.map f)) := by
  induction bs with
  | nil => rfl
  | cons t r ih =>
    change Nat.Partrec.Code.eval (Nat.Partrec.Code.comp Nat.Partrec.Code.succ
      (Nat.Partrec.Code.pair (Nat.Partrec.Code.comp (c t) Nat.Partrec.Code.zero)
        (tableChain c r))) 0 = _
    have hz : Nat.Partrec.Code.eval Nat.Partrec.Code.zero (0 : ℕ) = Part.some 0 := rfl
    have hct : Nat.Partrec.Code.eval (Nat.Partrec.Code.comp (c t) Nat.Partrec.Code.zero) 0
        = Part.some (f t) := (eval_comp_some hz).trans (hc t List.mem_cons_self)
    have ihr : (tableChain c r).eval 0 = Part.some (Encodable.encode (r.map f)) :=
      ih (fun t' ht' => hc t' (List.mem_cons_of_mem t ht'))
    have hpair : Nat.Partrec.Code.eval
        (Nat.Partrec.Code.pair (Nat.Partrec.Code.comp (c t) Nat.Partrec.Code.zero)
          (tableChain c r)) 0
        = Part.some (Nat.pair (f t) (Encodable.encode (r.map f))) := by
      change Nat.pair <$> _ <*> _ = _
      rw [hct, ihr]; simp [Seq.seq]
    rw [eval_comp_some hpair]
    change Nat.Partrec.Code.eval Nat.Partrec.Code.succ
      (Nat.pair (f t) (Encodable.encode (r.map f))) = _
    simp only [List.map_cons, Encodable.encode_list_cons]
    simp [Nat.Partrec.Code.eval]

/-- **The held-times chain**, `[] ↦ zero`, `t :: r ↦ comp succ (pair (bconst t) ⟨r⟩)` — the same
`encode (a :: l) = succ (pair (encode a) (encode l))` recursion as `tableChain`, over raw times
loaded by `bconst` instead of run codes. -/
private noncomputable def timeChain : List ℕ → Nat.Partrec.Code
  | [] => Nat.Partrec.Code.zero
  | t :: r => Nat.Partrec.Code.comp Nat.Partrec.Code.succ
      (Nat.Partrec.Code.pair (bconst t) (timeChain r))

private theorem elen_timeChain_le (bs : List ℕ) :
    elen (timeChain bs)
      ≤ 3 + 9 * bs.length + (15 + elen dbl) * (bs.map Nat.size).sum
        + (15 + elen dbl) * bs.length := by
  induction bs with
  | nil => rfl
  | cons t r ih =>
    change elen (Nat.Partrec.Code.comp Nat.Partrec.Code.succ
      (Nat.Partrec.Code.pair (bconst t) (timeChain r))) ≤ _
    rw [E_len_comp, E_len_pair]
    simp only [List.length_cons, List.map_cons, List.sum_cons]
    have hs : elen (Nat.Partrec.Code.succ : Nat.Partrec.Code) = 3 := rfl
    have hbc := elen_bconst_le t
    rw [hs]
    nlinarith [ih, hbc]

private theorem eval_timeChain (bs : List ℕ) :
    (timeChain bs).eval 0 = Part.some (Encodable.encode bs) := by
  induction bs with
  | nil => rfl
  | cons t r ih =>
    change Nat.Partrec.Code.eval (Nat.Partrec.Code.comp Nat.Partrec.Code.succ
      (Nat.Partrec.Code.pair (bconst t) (timeChain r))) 0 = _
    have hbc : Nat.Partrec.Code.eval (bconst t) (0 : ℕ) = Part.some t := eval_bconst t 0
    have hpair : Nat.Partrec.Code.eval (Nat.Partrec.Code.pair (bconst t) (timeChain r)) 0
        = Part.some (Nat.pair t (Encodable.encode r)) := by
      change Nat.pair <$> _ <*> _ = _
      rw [hbc, ih]; simp [Seq.seq]
    rw [eval_comp_some hpair]
    change Nat.Partrec.Code.eval Nat.Partrec.Code.succ (Nat.pair t (Encodable.encode r)) = _
    simp only [Encodable.encode_list_cons]
    simp [Nat.Partrec.Code.eval]

/-- **The world's own table is a valid itinerary candidate**: it is bijective (`U` is a
permutation) and, at every pair of held times one apart, it transports the earlier frame's table
to the later's — `ConsistentWith`'s own defining condition, read through the table encoding
exactly as `isValid_worldNumeral` reads `PermCarries`'s. -/
private theorem isValidItin_worldNumeral (hn : 0 < n) {U : Perm (Fin n)} {ℓ : ℕ → Fin n → Fin m}
    {bs : List ℕ} (hU : U ∈ ConsistentWith ℓ bs) :
    isValidItin n (bs.map fun t => lensCode (ℓ t)) bs (worldNumeral U) := by
  set Ts := bs.map fun t => lensCode (ℓ t) with hTsdef
  have hTsGetD : ∀ j, j < bs.length → Ts.getD j 0 = lensCode (ℓ (bs.getD j 0)) := by
    intro j hj
    have hj' : j < Ts.length := by rw [hTsdef, List.length_map]; exact hj
    rw [hTsdef, List.getD_eq_getElem _ _ hj', List.getD_eq_getElem _ _ hj, List.getElem_map]
  constructor
  · rw [candBijBool_iff]
    intro i hi j hj hij hcontra
    have hdi : digitAt n (worldNumeral U) i = (U (⟨i, hi⟩ : Fin n) : ℕ) :=
      digitAt_worldNumeral hn U ⟨i, hi⟩
    have hdj : digitAt n (worldNumeral U) j = (U (⟨j, hj⟩ : Fin n) : ℕ) :=
      digitAt_worldNumeral hn U ⟨j, hj⟩
    rw [hdi, hdj] at hcontra
    exact hij (congrArg Fin.val (U.injective (Fin.val_injective hcontra)))
  · rw [pairsOK_iff]
    intro j hj j' hj' heq i hi
    rw [hTsGetD j hj, hTsGetD j' hj']
    set t := bs.getD j 0 with htdef
    set t' := bs.getD j' 0 with ht'def
    have hdig : digitAt n (worldNumeral U) i = (U (⟨i, hi⟩ : Fin n) : ℕ) :=
      digitAt_worldNumeral hn U ⟨i, hi⟩
    have hget1 : (rawTable (lensCode (ℓ t))).getD (U (⟨i, hi⟩ : Fin n) : ℕ) 0
        = (ℓ t (U ⟨i, hi⟩) : ℕ) := by
      rw [rawTable_lensCode, lensTable]
      exact getD_map_finRange (fun y : Fin n => (ℓ t y : ℕ)) (U ⟨i, hi⟩)
    have hget0 : (rawTable (lensCode (ℓ t'))).getD i 0 = (ℓ t' (⟨i, hi⟩ : Fin n) : ℕ) := by
      rw [rawTable_lensCode, lensTable]
      exact getD_map_finRange (fun y : Fin n => (ℓ t' y : ℕ)) ⟨i, hi⟩
    rw [hdig, hget1, hget0]
    have htmem : t ∈ bs := by
      rw [htdef, List.getD_eq_getElem _ _ hj]; exact List.getElem_mem hj
    have ht'mem : t' ∈ bs := by
      rw [ht'def, List.getD_eq_getElem _ _ hj']; exact List.getElem_mem hj'
    exact congrArg (fun z : Fin m => (z : ℕ)) (hU t htmem t' ht'mem heq ⟨i, hi⟩)

/-- **The itinerary's coset bound**: the candidates satisfying `isValidItin` inject into the
consistent permutations, so the candidate list is no longer than `Nat.card ↥(ConsistentWith ℓ
bs)` — `candList_length_le`'s own shape, with `candPerm n w` landing directly in `ConsistentWith`
rather than in a coset relative to `U`. -/
private theorem candListItin_length_le (hn : 0 < n) {ℓ : ℕ → Fin n → Fin m} {bs : List ℕ}
    {U : Perm (Fin n)} (hU : U ∈ ConsistentWith ℓ bs) :
    (candListItin n (bs.map fun t => lensCode (ℓ t)) bs).length
      ≤ Nat.card ↥(ConsistentWith ℓ bs) := by
  classical
  set Ts := bs.map fun t => lensCode (ℓ t) with hTsdef
  have : Fintype ↥(ConsistentWith ℓ bs) := Fintype.ofFinite _
  have hnodup : (candListItin n Ts bs).Nodup := List.nodup_range.filter _
  have hmem : ∀ w ∈ (candListItin n Ts bs).toFinset, w < n ^ n ∧ isValidItin n Ts bs w := by
    intro w hw
    rw [List.mem_toFinset, candListItin, List.mem_filter, List.mem_range, decide_eq_true_eq] at hw
    exact hw
  have hcandmem : ∀ {w}, isValidItin n Ts bs w → candPerm n w ∈ ConsistentWith ℓ bs := by
    intro w hv t ht t' ht' hstep x
    obtain ⟨j, hj, hjeq⟩ := List.getElem_of_mem ht
    obtain ⟨j', hj', hj'eq⟩ := List.getElem_of_mem ht'
    have hTsGetD : ∀ k, k < bs.length → Ts.getD k 0 = lensCode (ℓ (bs.getD k 0)) := by
      intro k hk
      have hk' : k < Ts.length := by rw [hTsdef, List.length_map]; exact hk
      rw [hTsdef, List.getD_eq_getElem _ _ hk', List.getD_eq_getElem _ _ hk, List.getElem_map]
    have hjbs : bs.getD j 0 = t := by rw [List.getD_eq_getElem _ _ hj]; exact hjeq
    have hj'bs : bs.getD j' 0 = t' := by rw [List.getD_eq_getElem _ _ hj']; exact hj'eq
    have hjstep : bs.getD j 0 = bs.getD j' 0 + 1 := by rw [hjbs, hj'bs]; exact hstep
    have hb := hv.1
    have hpairs := (pairsOK_iff n Ts bs w).mp hv.2 j hj j' hj' hjstep (x : ℕ) x.2
    rw [hTsGetD j hj, hTsGetD j' hj', hjbs, hj'bs] at hpairs
    have hcx : (candPerm n w x : ℕ) = digitAt n w (x : ℕ) := candPerm_apply hn hb x
    have hget1 : (rawTable (lensCode (ℓ t))).getD (candPerm n w x : ℕ) 0
        = (ℓ t (candPerm n w x) : ℕ) := by
      rw [rawTable_lensCode, lensTable]
      exact getD_map_finRange (fun y : Fin n => (ℓ t y : ℕ)) (candPerm n w x)
    have hget0 : (rawTable (lensCode (ℓ t'))).getD (x : ℕ) 0 = (ℓ t' x : ℕ) := by
      rw [rawTable_lensCode, lensTable]
      exact getD_map_finRange (fun y : Fin n => (ℓ t' y : ℕ)) x
    rw [← hcx] at hpairs
    rw [hget1, hget0] at hpairs
    exact Fin.val_injective hpairs
  set f : ℕ → ↥(ConsistentWith ℓ bs) := fun w =>
    if h : isValidItin n Ts bs w then ⟨candPerm n w, hcandmem h⟩ else ⟨U, hU⟩ with hf
  have hcard := Finset.card_le_card_of_injOn f
    (s := (candListItin n Ts bs).toFinset) (t := Finset.univ)
    (fun w _ => Finset.mem_univ (f w))
    (by
      intro w1 hw1 w2 hw2 heq
      rw [Finset.mem_coe] at hw1 hw2
      have h1 := hmem w1 hw1
      have h2 := hmem w2 hw2
      have hfw1 : f w1 = ⟨candPerm n w1, hcandmem h1.2⟩ := dif_pos h1.2
      have hfw2 : f w2 = ⟨candPerm n w2, hcandmem h2.2⟩ := dif_pos h2.2
      rw [hfw1, hfw2, Subtype.mk_eq_mk] at heq
      have hb1 : candBijBool n w1 = true := h1.2.1
      have hb2 : candBijBool n w2 = true := h2.2.1
      have hdig : ∀ i : Fin n, digitAt n w1 (i : ℕ) = digitAt n w2 (i : ℕ) := by
        intro i
        rw [← candPerm_apply hn hb1 i, ← candPerm_apply hn hb2 i, heq]
      apply candTable_injOn h1.1 h2.1
      change (List.range n).map (digitAt n w1) = (List.range n).map (digitAt n w2)
      refine List.map_congr_left fun j hj => ?_
      exact hdig ⟨j, List.mem_range.mp hj⟩)
  rw [← List.toFinset_card_of_nodup hnodup, Nat.card_eq_fintype_card]
  simpa using hcard

/-- **The ledger at any frames** ([Persistence] §6, Theorem 6.5(ii)). A fixed decoder recovers `U`
from the frame codes held at `bs`, the held times themselves, and an index into the consistent set
`ConsistentWith ℓ bs` — priced by the caller's own bound `N` on that set's size, since the set's
card is not itself computed here (that count is `consistent_card`'s content, over `Bminus bs`).
`bs` need not be sorted or `Nodup`; repeated or misordered entries impose no different a
constraint. -/
theorem ledger_itinerary (hn : 0 < n) {U : Perm (Fin n)} {ℓ : ℕ → Fin n → Fin m}
    (bs : List ℕ) (hU : U ∈ ConsistentWith ℓ bs)
    (c : ℕ → Nat.Partrec.Code)
    (hc : ∀ t ∈ bs, (c t).eval 0 = Part.some (lensCode (ℓ t)))
    (N : ℕ) (hN : Nat.card ↥(ConsistentWith ℓ bs) ≤ N) :
    KE (lensCode U)
      ≤ (bs.map fun t => elen (c t)).sum
        + (15 + elen dbl) * (bs.map Nat.size).sum
        + (39 + elen dbl) * bs.length
        + (15 + elen dbl) * Nat.size N
        + (15 + elen dbl) * Nat.size n
        + (elen itinBuilder + 2 * (15 + elen dbl) + 18) := by
  set Ts := bs.map fun t => lensCode (ℓ t) with hTsdef
  have hvalid : isValidItin n Ts bs (worldNumeral U) := isValidItin_worldNumeral hn hU
  have hlt : worldNumeral U < n ^ n := worldNumeral_lt hn U
  have hmem : worldNumeral U ∈ candListItin n Ts bs := by
    rw [candListItin, List.mem_filter, List.mem_range, decide_eq_true_eq]
    exact ⟨hlt, hvalid⟩
  obtain ⟨idx, hidxlt, hidxeq⟩ := List.getElem_of_mem hmem
  have hlenle : (candListItin n Ts bs).length ≤ N :=
    le_trans (candListItin_length_le hn hU) hN
  have hidxN : idx < N := lt_of_lt_of_le hidxlt hlenle
  have hgetD : List.getD (candListItin n Ts bs) idx 0 = worldNumeral U := by
    rw [List.getD_eq_getElem _ _ hidxlt]; exact hidxeq
  have heval : itinTableFn (Nat.pair n (Nat.pair (Encodable.encode Ts)
      (Nat.pair (Encodable.encode bs) idx))) = lensCode U := by
    rw [itinTableFn]
    simp only [Nat.unpair_pair, Encodable.encodek, Option.getD_some]
    rw [hgetD]
    exact congrArg Encodable.encode (candTable_packMarks hn U)
  have htc : (tableChain c bs).eval 0 = Part.some (Encodable.encode Ts) := by
    rw [hTsdef]; exact eval_tableChain c (fun t => lensCode (ℓ t)) bs hc
  have hti : (timeChain bs).eval 0 = Part.some (Encodable.encode bs) := eval_timeChain bs
  have hbi : eval (bconst idx) (0 : ℕ) = Part.some idx := eval_bconst idx 0
  have hbn : eval (bconst n) (0 : ℕ) = Part.some n := eval_bconst n 0
  have hpair3 : eval (pair (timeChain bs) (bconst idx)) 0
      = Part.some (Nat.pair (Encodable.encode bs) idx) := by
    change Nat.pair <$> _ <*> _ = _
    rw [hti, hbi]; simp [Seq.seq]
  have hpair2 : eval (pair (tableChain c bs) (pair (timeChain bs) (bconst idx))) 0
      = Part.some (Nat.pair (Encodable.encode Ts) (Nat.pair (Encodable.encode bs) idx)) := by
    change Nat.pair <$> _ <*> _ = _
    rw [htc, hpair3]; simp [Seq.seq]
  have hpair1 : eval
      (pair (bconst n) (pair (tableChain c bs) (pair (timeChain bs) (bconst idx)))) 0
      = Part.some (Nat.pair n
          (Nat.pair (Encodable.encode Ts) (Nat.pair (Encodable.encode bs) idx))) := by
    change Nat.pair <$> _ <*> _ = _
    rw [hbn, hpair2]; simp [Seq.seq]
  have hcomp : Computes
      (comp itinBuilder
        (pair (bconst n) (pair (tableChain c bs) (pair (timeChain bs) (bconst idx)))))
      (lensCode U) := by
    change eval (comp itinBuilder
      (pair (bconst n) (pair (tableChain c bs) (pair (timeChain bs) (bconst idx))))) 0 = _
    rw [eval_comp_some hpair1, eval_itinBuilder, heval]
  have hle := KE_le hcomp
  rw [E_len_comp, E_len_pair, E_len_pair, E_len_pair] at hle
  have htcelen := elen_tableChain c bs
  have htielen := elen_timeChain_le bs
  have hbnbound := elen_bconst_le n
  have hbibound := elen_bconst_le idx
  have hidxsize : Nat.size idx ≤ Nat.size N := Nat.size_le_size (le_of_lt hidxN)
  have hidxsize' : (15 + elen dbl) * Nat.size idx ≤ (15 + elen dbl) * Nat.size N :=
    Nat.mul_le_mul_left _ hidxsize
  rw [htcelen] at hle
  nlinarith [hle, htielen, hbnbound, hbibound, hidxsize']

set_option linter.style.longLine false in
/-- info: 'PersistenceCapacity.ledger_itinerary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ledger_itinerary

/-- **The ledger at `k` consecutive frames** ([Persistence] §6, Theorem 6.5(i)). `rangeCode`
replaces the held-times chain: instead of loading `k` separate times at `Θ (k log k)` total, one
`bconst k` runs through the fixed `rangeCode` program, restoring the paper's own `O (log k)`
term. -/
theorem ledger_itinerary_consecutive (hn : 0 < n) {U : Perm (Fin n)} {ℓ : ℕ → Fin n → Fin m}
    (k : ℕ) (hU : U ∈ ConsistentWith ℓ (List.range k))
    (c : ℕ → Nat.Partrec.Code)
    (hc : ∀ t < k, (c t).eval 0 = Part.some (lensCode (ℓ t)))
    (N : ℕ) (hN : Nat.card ↥(ConsistentWith ℓ (List.range k)) ≤ N) :
    KE (lensCode U)
      ≤ ((List.range k).map fun t => elen (c t)).sum
        + 15 * k
        + (15 + elen dbl) * Nat.size k
        + (15 + elen dbl) * Nat.size N
        + (15 + elen dbl) * Nat.size n
        + (elen itinBuilder + elen rangeCode + 3 * (15 + elen dbl) + 18) := by
  set bs := List.range k with hbsdef
  set Ts := bs.map fun t => lensCode (ℓ t) with hTsdef
  have hvalid : isValidItin n Ts bs (worldNumeral U) := isValidItin_worldNumeral hn hU
  have hlt : worldNumeral U < n ^ n := worldNumeral_lt hn U
  have hmem : worldNumeral U ∈ candListItin n Ts bs := by
    rw [candListItin, List.mem_filter, List.mem_range, decide_eq_true_eq]
    exact ⟨hlt, hvalid⟩
  obtain ⟨idx, hidxlt, hidxeq⟩ := List.getElem_of_mem hmem
  have hlenle : (candListItin n Ts bs).length ≤ N :=
    le_trans (candListItin_length_le hn hU) hN
  have hidxN : idx < N := lt_of_lt_of_le hidxlt hlenle
  have hgetD : List.getD (candListItin n Ts bs) idx 0 = worldNumeral U := by
    rw [List.getD_eq_getElem _ _ hidxlt]; exact hidxeq
  have heval : itinTableFn (Nat.pair n (Nat.pair (Encodable.encode Ts)
      (Nat.pair (Encodable.encode bs) idx))) = lensCode U := by
    rw [itinTableFn]
    simp only [Nat.unpair_pair, Encodable.encodek, Option.getD_some]
    rw [hgetD]
    exact congrArg Encodable.encode (candTable_packMarks hn U)
  have htc : (tableChain c bs).eval 0 = Part.some (Encodable.encode Ts) := by
    rw [hTsdef]; exact eval_tableChain c (fun t => lensCode (ℓ t)) bs
      (fun t ht => hc t (by rw [hbsdef, List.mem_range] at ht; exact ht))
  have hti : eval (comp rangeCode (bconst k)) 0 = Part.some (Encodable.encode bs) := by
    rw [hbsdef]
    have hbk : eval (bconst k) (0 : ℕ) = Part.some k := eval_bconst k 0
    exact (eval_comp_some hbk).trans (eval_rangeCode k)
  have hbi : eval (bconst idx) (0 : ℕ) = Part.some idx := eval_bconst idx 0
  have hbn : eval (bconst n) (0 : ℕ) = Part.some n := eval_bconst n 0
  have hpair3 : eval (pair (comp rangeCode (bconst k)) (bconst idx)) 0
      = Part.some (Nat.pair (Encodable.encode bs) idx) := by
    change Nat.pair <$> _ <*> _ = _
    rw [hti, hbi]; simp [Seq.seq]
  have hpair2 : eval (pair (tableChain c bs) (pair (comp rangeCode (bconst k)) (bconst idx))) 0
      = Part.some (Nat.pair (Encodable.encode Ts) (Nat.pair (Encodable.encode bs) idx)) := by
    change Nat.pair <$> _ <*> _ = _
    rw [htc, hpair3]; simp [Seq.seq]
  have hpair1 : eval
      (pair (bconst n)
        (pair (tableChain c bs) (pair (comp rangeCode (bconst k)) (bconst idx)))) 0
      = Part.some (Nat.pair n
          (Nat.pair (Encodable.encode Ts) (Nat.pair (Encodable.encode bs) idx))) := by
    change Nat.pair <$> _ <*> _ = _
    rw [hbn, hpair2]; simp [Seq.seq]
  have hcomp : Computes
      (comp itinBuilder
        (pair (bconst n)
          (pair (tableChain c bs) (pair (comp rangeCode (bconst k)) (bconst idx)))))
      (lensCode U) := by
    change eval (comp itinBuilder
      (pair (bconst n)
        (pair (tableChain c bs) (pair (comp rangeCode (bconst k)) (bconst idx))))) 0 = _
    rw [eval_comp_some hpair1, eval_itinBuilder, heval]
  have hle := KE_le hcomp
  rw [E_len_comp, E_len_pair, E_len_pair, E_len_pair, E_len_comp] at hle
  have htcelen := elen_tableChain c bs
  have hbnbound := elen_bconst_le n
  have hbibound := elen_bconst_le idx
  have hbkbound := elen_bconst_le k
  have hidxsize : Nat.size idx ≤ Nat.size N := Nat.size_le_size (le_of_lt hidxN)
  have hidxsize' : (15 + elen dbl) * Nat.size idx ≤ (15 + elen dbl) * Nat.size N :=
    Nat.mul_le_mul_left _ hidxsize
  have hklen : bs.length = k := by rw [hbsdef, List.length_range]
  rw [htcelen, hklen] at hle
  nlinarith [hle, hbnbound, hbibound, hbkbound, hidxsize']

set_option linter.style.longLine false in
/-- info: 'PersistenceCapacity.ledger_itinerary_consecutive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ledger_itinerary_consecutive

/-! ### Two hypotheses proved load-bearing (in-module witnesses) -/

/-- **The `t = t' + 1` side condition is load-bearing**: at `bs = [0, 2]`, no two held times are
one apart, so `ConsistentWith ℓ bs` is unconstrained — every permutation is consistent, including
the identity. Requiring instead that EVERY pair of distinct held times constrain `V` — the
condition with `t = t' + 1` dropped in favor of `t ≠ t'` — is a strictly sharper set that the
identity fails: at `ℓ 0 = id`, `ℓ 2 = swap 0 1`, the sharper condition forces `V 0 = ℓ 0 (V 0) =
ℓ 2 0 = 1 ≠ 0`, so the identity is excluded from it while `ConsistentWith` admits it. -/
theorem guard_consistentWith_step_load_bearing :
    ∃ (ℓ : ℕ → Fin 2 → Fin 2),
      ConsistentWith ℓ [0, 2] = Set.univ ∧
      (1 : Perm (Fin 2)) ∉ {V : Perm (Fin 2) | ∀ t ∈ ([0, 2] : List ℕ), ∀ t' ∈ ([0, 2] : List ℕ),
        t ≠ t' → ∀ x, ℓ t (V x) = ℓ t' x} := by
  refine ⟨fun t => if t = 2 then Equiv.swap 0 1 else ⇑(1 : Perm (Fin 2)), ?_, ?_⟩
  · ext V
    simp only [ConsistentWith, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
    intro t ht t' ht' hstep x
    fin_cases ht <;> fin_cases ht' <;> omega
  · intro h
    exact absurd (h 0 (by decide) 2 (by decide) (by decide) 0) (by decide)

/-- **The `candBijBool` conjunct is load-bearing**: at a constant, single-label reference frame
(codomain `Fin 1`, so `ℓ t x = 0` for every `t` and `x`), `pairsOK` holds for EVERY numeral `w`
below `n ^ n` — the transport condition reads `0 = 0` regardless of `w`'s own digits — while
`ConsistentWith` is unconstrained for the same reason, so its cardinality is the full symmetric
group, `n !`. Without the bijectivity conjunct the enumeration therefore has `n ^ n` members
against the true count `n !`; checked at `n = 4`: `256` against `24`. -/
theorem guard_isValidItin_candBijBool_load_bearing :
    Nat.card ↥(ConsistentWith (n := 4) (m := 1) (fun _ _ => (0 : Fin 1)) [0, 2])
        = Nat.factorial 4 ∧
      ∀ w < 4 ^ 4, pairsOK 4 (([0, 2] : List ℕ).map fun _ => lensCode
        (fun _ : Fin 4 => (0 : Fin 1))) [0, 2] w = true := by
  constructor
  · have huniv : ConsistentWith (n := 4) (m := 1) (fun _ _ => (0 : Fin 1)) [0, 2] = Set.univ := by
      ext V
      simp only [ConsistentWith, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
      simp
    rw [huniv]
    have : Nat.card ↥(Set.univ : Set (Perm (Fin 4))) = Nat.card (Perm (Fin 4)) :=
      Nat.card_congr (Equiv.Set.univ _)
    rw [this, Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
  · intro w _
    rw [pairsOK_iff]
    intro j hj j' hj' _ i _
    have hzero : ∀ (y : Fin 4 → Fin 1) (d : ℕ), (rawTable (lensCode y)).getD d 0 = 0 := by
      intro y d
      rw [rawTable_lensCode, lensTable]
      have hrep : ((List.finRange 4).map fun i => ((y i : Fin 1) : ℕ)) = List.replicate 4 0 := by
        apply List.eq_replicate_of_mem
        intro a ha
        obtain ⟨i, _, rfl⟩ := List.mem_map.mp ha
        exact Fin.val_eq_zero (y i)
      rw [hrep]
      rcases Nat.lt_or_ge d 4 with hd | hd
      · rw [List.getD_eq_getElem _ _ (by simpa using hd), List.getElem_replicate]
      · rw [List.getD_eq_default _ _ (by simpa using hd)]
    have hconst : ∀ k, k < 2 → (([0, 2] : List ℕ).map fun _ => lensCode
        (fun _ : Fin 4 => (0 : Fin 1))).getD k 0 = lensCode (fun _ : Fin 4 => (0 : Fin 1)) := by
      intro k hk
      rcases k with _ | _ | k
      · rfl
      · rfl
      · omega
    rw [hconst j hj, hconst j' hj', hzero, hzero]

/-! ## Corollary 8.11(i): what a factor buys, exactly

`ledger_graded` recovers `U` from two frame tables plus an index into the coset
`{V | ℓ₁ ∘ V = ℓ₀}`. [Persistence] §8, Corollary 8.11(i) recovers `U` from `κ`'s table, `W`'s table,
and an index into the coset `{V | κ ∘ V = W ∘ κ}` — the SAME stabilizer (`card_descentCoset`,
above), at a different translate. So the display below is `ledger_graded`'s own
enumerate-filter-select decoder with one predicate swapped: "carries the two frames" becomes
"descends through `κ` with law `W`". `candBijBool`, `candTable`, `candPerm`, `worldNumeral` and
`candTable_packMarks` are reused unchanged; only the matching predicate, the candidate list, and
the tabulation built from it are new. -/

/-- **A candidate descends through the packed `κ`-table with the packed `W`-table's law**: its
table is a genuine permutation, and reading `κ`'s table at the candidate's value agrees with reading
`W`'s table at `κ`'s own value — `κ (candidate i) = W (κ i)` for every `i`, read straight off the
three tables. -/
private def isValidDescent (n t0 t1 w : ℕ) : Prop :=
  candBijBool n w = true ∧
    ∀ i < n, List.getD (rawTable t0) (digitAt n w i) 0
      = List.getD (rawTable t1) (List.getD (rawTable t0) i 0) 0

private instance decIsValidDescent (n t0 t1 w : ℕ) : Decidable (isValidDescent n t0 t1 w) := by
  unfold isValidDescent; infer_instance

/-- **`isValidDescent` is primitive recursive**, over the packed program `⟨n, t0, t1, w⟩` — the
bijectivity half unchanged from `primrec_isValid`, the matching half reading `t0`'s table twice
(once at the candidate's value, once at `i` itself) and `t1`'s table once, at that second
reading. -/
private theorem primrec_isValidDescent :
    PrimrecPred fun p : ℕ => isValidDescent p.unpair.1 p.unpair.2.unpair.1
      p.unpair.2.unpair.2.unpair.1 p.unpair.2.unpair.2.unpair.2 := by
  have hN : Primrec fun p : ℕ => p.unpair.1 := Primrec.fst.comp Primrec.unpair
  have hR1 : Primrec fun p : ℕ => p.unpair.2 := Primrec.snd.comp Primrec.unpair
  have hT0 : Primrec fun p : ℕ => p.unpair.2.unpair.1 := Primrec.fst.comp (Primrec.unpair.comp hR1)
  have hR2 : Primrec fun p : ℕ => p.unpair.2.unpair.2 := Primrec.snd.comp (Primrec.unpair.comp hR1)
  have hT1 : Primrec fun p : ℕ => p.unpair.2.unpair.2.unpair.1 :=
    Primrec.fst.comp (Primrec.unpair.comp hR2)
  have hW : Primrec fun p : ℕ => p.unpair.2.unpair.2.unpair.2 :=
    Primrec.snd.comp (Primrec.unpair.comp hR2)
  have hpow : Primrec₂ ((· ^ ·) : ℕ → ℕ → ℕ) := Primrec₂.unpaired'.1 Nat.Primrec.pow
  have hBij : PrimrecPred fun p : ℕ =>
      candBijBool p.unpair.1 p.unpair.2.unpair.2.unpair.2 = true := by
    have hb : Primrec fun p : ℕ => candBijBool p.unpair.1 p.unpair.2.unpair.2.unpair.2 := by
      have := primrec_candBijBool.comp hN hW
      exact this
    exact Primrec.eq.comp hb (Primrec.const true)
  have hMatch : PrimrecPred fun p : ℕ => ∀ i < p.unpair.1,
      List.getD (rawTable p.unpair.2.unpair.1)
          (digitAt p.unpair.1 p.unpair.2.unpair.2.unpair.2 i) 0
        = List.getD (rawTable p.unpair.2.unpair.2.unpair.1)
            (List.getD (rawTable p.unpair.2.unpair.1) i 0) 0 := by
    have hR : PrimrecRel fun (i : ℕ) (p : ℕ) =>
        List.getD (rawTable p.unpair.2.unpair.1)
            (digitAt p.unpair.1 p.unpair.2.unpair.2.unpair.2 i) 0
          = List.getD (rawTable p.unpair.2.unpair.2.unpair.1)
              (List.getD (rawTable p.unpair.2.unpair.1) i 0) 0 := by
      have hdig : Primrec fun q : ℕ × ℕ =>
          digitAt q.2.unpair.1 q.2.unpair.2.unpair.2.unpair.2 q.1 :=
        Primrec.nat_mod.comp
          (Primrec.nat_div.comp (hW.comp Primrec.snd)
            (hpow.comp (hN.comp Primrec.snd) Primrec.fst))
          (hN.comp Primrec.snd)
      have hf : Primrec fun q : ℕ × ℕ =>
          List.getD (rawTable q.2.unpair.2.unpair.1)
            (digitAt q.2.unpair.1 q.2.unpair.2.unpair.2.unpair.2 q.1) 0 :=
        (Primrec.list_getD 0).comp (primrec_rawTable.comp (hT0.comp Primrec.snd)) hdig
      have hinner : Primrec fun q : ℕ × ℕ =>
          List.getD (rawTable q.2.unpair.2.unpair.1) q.1 0 :=
        (Primrec.list_getD 0).comp (primrec_rawTable.comp (hT0.comp Primrec.snd)) Primrec.fst
      have hg : Primrec fun q : ℕ × ℕ =>
          List.getD (rawTable q.2.unpair.2.unpair.2.unpair.1)
            (List.getD (rawTable q.2.unpair.2.unpair.1) q.1 0) 0 :=
        (Primrec.list_getD 0).comp (primrec_rawTable.comp (hT1.comp Primrec.snd)) hinner
      exact PrimrecRel.comp Primrec.eq hf hg
    exact primrecPred_dup_nat hR hN
  exact hBij.and hMatch

set_option maxHeartbeats 1000000 in
-- same headroom reason as `primrec_isValid_rel`: multi-level packing meets `primrec_isValidDescent`.
/-- **The membership relation is primitive recursive**, over `(w, param)` with `param` packing
`(n, t0, t1)` — `primrec_isValidDescent` at `param` and `w` rebuilt into one packed program. -/
private theorem primrec_isValidDescent_rel :
    PrimrecRel fun (w param : ℕ) =>
      isValidDescent param.unpair.1 param.unpair.2.unpair.1 param.unpair.2.unpair.2 w := by
  have hn' : Primrec fun q : ℕ × ℕ => q.2.unpair.1 :=
    Primrec.fst.comp (Primrec.unpair.comp Primrec.snd)
  have ht0' : Primrec fun q : ℕ × ℕ => q.2.unpair.2.unpair.1 :=
    Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp (Primrec.unpair.comp Primrec.snd)))
  have ht1' : Primrec fun q : ℕ × ℕ => q.2.unpair.2.unpair.2 :=
    Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp (Primrec.unpair.comp Primrec.snd)))
  have hw' : Primrec fun q : ℕ × ℕ => q.1 := Primrec.fst
  have hinner1 : Primrec fun q : ℕ × ℕ => Nat.pair (q.2.unpair.2.unpair.2) (q.1) :=
    Primrec₂.natPair.comp ht1' hw'
  have hinner2 : Primrec fun q : ℕ × ℕ =>
      Nat.pair (q.2.unpair.2.unpair.1) (Nat.pair (q.2.unpair.2.unpair.2) (q.1)) :=
    Primrec₂.natPair.comp ht0' hinner1
  have hfull : Primrec fun q : ℕ × ℕ =>
      Nat.pair (q.2.unpair.1) (Nat.pair (q.2.unpair.2.unpair.1)
        (Nat.pair (q.2.unpair.2.unpair.2) (q.1))) :=
    Primrec₂.natPair.comp hn' hinner2
  have hkey := primrec_isValidDescent.comp hfull
  refine hkey.of_eq fun q => ?_
  simp only [Nat.unpair_pair]

/-- **The descending-candidate list**: every numeral below `n ^ n` whose table both is a genuine
permutation and descends through `κ`'s packed table with `W`'s packed law, in the numeral's own
order — `candList`'s own skeleton at `isValidDescent` in place of `isValid`. -/
private def candListDescent (n t0 t1 : ℕ) : List ℕ :=
  (List.range (n ^ n)).filter (fun w => decide (isValidDescent n t0 t1 w))

private theorem primrec_candListDescent :
    Primrec fun p : ℕ => candListDescent p.unpair.1 p.unpair.2.unpair.1 p.unpair.2.unpair.2 := by
  have hpow : Primrec₂ ((· ^ ·) : ℕ → ℕ → ℕ) := Primrec₂.unpaired'.1 Nat.Primrec.pow
  have hN : Primrec fun p : ℕ => p.unpair.1 := Primrec.fst.comp Primrec.unpair
  have hL : Primrec fun p : ℕ => List.range (p.unpair.1 ^ p.unpair.1) :=
    Primrec.list_range.comp (hpow.comp hN hN)
  have hfilt := (PrimrecRel.listFilter primrec_isValidDescent_rel).comp hL Primrec.id
  exact hfilt.of_eq fun p => rfl

/-- **The tabulation, rebuilt from the packed program** `⟨n, t0, t1, idx⟩` — `gradedTableFn`'s own
skeleton, filtering `candListDescent` instead of `candList`; `candTable` itself is reused
unchanged. -/
private def gradedTableFnDescent (a : ℕ) : ℕ :=
  Encodable.encode (candTable a.unpair.1
    (List.getD (candListDescent a.unpair.1 a.unpair.2.unpair.1 a.unpair.2.unpair.2.unpair.1)
      a.unpair.2.unpair.2.unpair.2 0))

set_option maxHeartbeats 1000000 in
-- same headroom reason as `primrec_isValidDescent_rel`: multi-level packing meets
-- `primrec_candListDescent`.
private theorem primrec_gradedTableFnDescent : Primrec gradedTableFnDescent := by
  have hN : Primrec fun a : ℕ => a.unpair.1 := Primrec.fst.comp Primrec.unpair
  have hT0 : Primrec fun a : ℕ => a.unpair.2.unpair.1 :=
    Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))
  have hT1 : Primrec fun a : ℕ => a.unpair.2.unpair.2.unpair.1 :=
    Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp
      (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))))
  have hIdx : Primrec fun a : ℕ => a.unpair.2.unpair.2.unpair.2 :=
    Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp
      (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))))
  have hParam : Primrec fun a : ℕ =>
      Nat.pair a.unpair.1 (Nat.pair a.unpair.2.unpair.1 a.unpair.2.unpair.2.unpair.1) :=
    Primrec₂.natPair.comp hN (Primrec₂.natPair.comp hT0 hT1)
  have hCL : Primrec fun a : ℕ =>
      candListDescent a.unpair.1 a.unpair.2.unpair.1 a.unpair.2.unpair.2.unpair.1 := by
    have := primrec_candListDescent.comp hParam
    refine this.of_eq fun a => ?_
    simp only [Nat.unpair_pair]
  have hSel : Primrec fun a : ℕ =>
      List.getD (candListDescent a.unpair.1 a.unpair.2.unpair.1 a.unpair.2.unpair.2.unpair.1)
        a.unpair.2.unpair.2.unpair.2 0 :=
    (Primrec.list_getD 0).comp hCL hIdx
  exact Primrec.encode.comp (primrec_candTable.comp hN hSel)

private theorem partrec_gradedTableFnDescent :
    Nat.Partrec (fun a : ℕ => (gradedTableFnDescent a : ℕ)) :=
  _root_.Partrec.nat_iff.mp (Primrec.to_comp primrec_gradedTableFnDescent).partrec

/-- **The fixed factor-ledger builder code.** One program, independent of `n`, `κ` and `W` —
`gradedBuilder`'s own role, at the descent predicate. -/
noncomputable def gradedBuilderDescent : Nat.Partrec.Code :=
  Classical.choose (Nat.Partrec.Code.exists_code.mp partrec_gradedTableFnDescent)

private theorem eval_gradedBuilderDescent (a : ℕ) :
    Nat.Partrec.Code.eval gradedBuilderDescent a = Part.some (gradedTableFnDescent a) := by
  have h := congrFun (Classical.choose_spec
    (Nat.Partrec.Code.exists_code.mp partrec_gradedTableFnDescent)) a
  simpa [gradedBuilderDescent] using h

/-- **`U`'s own table is a valid descending candidate**: it is bijective (`U` is a permutation) and
it descends through `κ` with law `W` by hypothesis — read through the encode/decode round trip and
the base-`n` packing, with no appeal to any `permCarries`-style rewriting: the hypothesis already
has the shape the candidate's matching condition asks for. -/
private theorem isValidDescent_worldNumeral (hn : 0 < n) {z : ℕ} {κ : Fin n → Fin z}
    {W : Fin z → Fin z} {U : Perm (Fin n)} (hU : ∀ x, κ (U x) = W (κ x)) :
    isValidDescent n (lensCode κ) (lensCode W) (worldNumeral U) := by
  constructor
  · rw [candBijBool_iff]
    intro i hi j hj hij hcontra
    have hdi : digitAt n (worldNumeral U) i = (U (⟨i, hi⟩ : Fin n) : ℕ) :=
      digitAt_worldNumeral hn U ⟨i, hi⟩
    have hdj : digitAt n (worldNumeral U) j = (U (⟨j, hj⟩ : Fin n) : ℕ) :=
      digitAt_worldNumeral hn U ⟨j, hj⟩
    rw [hdi, hdj] at hcontra
    exact hij (congrArg Fin.val (U.injective (Fin.val_injective hcontra)))
  · intro i hi
    have hdig : digitAt n (worldNumeral U) i = (U (⟨i, hi⟩ : Fin n) : ℕ) :=
      digitAt_worldNumeral hn U ⟨i, hi⟩
    have hgetKappaU : List.getD (rawTable (lensCode κ)) (U (⟨i, hi⟩ : Fin n) : ℕ) 0
        = (κ (U ⟨i, hi⟩) : ℕ) := by
      rw [rawTable_lensCode, lensTable]
      exact getD_map_finRange (fun y : Fin n => (κ y : ℕ)) (U ⟨i, hi⟩)
    have hgetKappaI : List.getD (rawTable (lensCode κ)) i 0 = (κ (⟨i, hi⟩ : Fin n) : ℕ) := by
      rw [rawTable_lensCode, lensTable]
      exact getD_map_finRange (fun y : Fin n => (κ y : ℕ)) ⟨i, hi⟩
    have hgetW : List.getD (rawTable (lensCode W)) (κ (⟨i, hi⟩ : Fin n) : ℕ) 0
        = (W (κ ⟨i, hi⟩) : ℕ) := by
      rw [rawTable_lensCode, lensTable]
      exact getD_map_finRange (fun y : Fin z => (W y : ℕ)) (κ ⟨i, hi⟩)
    rw [hdig, hgetKappaU, hgetKappaI, hgetW]
    exact congrArg (fun x : Fin z => (x : ℕ)) (hU ⟨i, hi⟩)

/-- **The descent injection**: a valid numeral's candidate permutation descends through `κ` with
law `W` outright, `κ (candidate x) = W (κ x)` at every `x` — read straight off `isValidDescent`'s
matching condition through the encode/decode round trip, with no multiplication by any world
needed (unlike `candPerm_mem_stabilizer`, whose predicate was phrased relative to a reference
frame's own inverse). -/
private theorem candPerm_mem_descentSet {n w z : ℕ} (hn : 0 < n) {κ : Fin n → Fin z}
    {W : Fin z → Fin z} (hv : isValidDescent n (lensCode κ) (lensCode W) w) :
    ∀ x, κ (candPerm n w x) = W (κ x) := by
  intro x
  have hb := hv.1
  have hmatch := hv.2
  have hi : (x : ℕ) < n := x.2
  have hval : (⟨digitAt n w x, Nat.mod_lt _ hn⟩ : Fin n) = candPerm n w x := by
    apply Fin.val_injective
    rw [candPerm_apply hn hb]
  have hgetKappaCand : List.getD (rawTable (lensCode κ)) (digitAt n w x) 0
      = (κ (⟨digitAt n w x, Nat.mod_lt _ hn⟩ : Fin n) : ℕ) := by
    rw [rawTable_lensCode, lensTable]
    exact getD_map_finRange (fun y : Fin n => (κ y : ℕ)) ⟨digitAt n w x, Nat.mod_lt _ hn⟩
  have hgetKappaX : List.getD (rawTable (lensCode κ)) (x : ℕ) 0 = (κ x : ℕ) := by
    rw [rawTable_lensCode, lensTable]; exact getD_map_finRange _ _
  have hgetW : List.getD (rawTable (lensCode W)) (κ x : ℕ) 0 = (W (κ x) : ℕ) := by
    rw [rawTable_lensCode, lensTable]
    exact getD_map_finRange (fun y : Fin z => (W y : ℕ)) (κ x)
  have hspec := hmatch x hi
  rw [hgetKappaCand, hgetKappaX, hgetW, hval] at hspec
  exact Fin.val_injective hspec

/-- **The factor ledger's coset bound**: the descent set that a coset argument pins `U` down to
against `κ` and `W` has size at most `∏ᵢ (fiberᵢ)!` — `card_descentCoset`'s count, reached here by
injecting every valid descending candidate directly into the descent set (`candPerm n w` itself,
with no world-relative multiplication), and falling back on `U` itself — always a member, by
hypothesis — off the valid domain. -/
private theorem candListDescent_length_le (hn : 0 < n) {z : ℕ} {κ : Fin n → Fin z}
    {W : Fin z → Fin z} {U : Perm (Fin n)} (hU : ∀ x, κ (U x) = W (κ x)) :
    (candListDescent n (lensCode κ) (lensCode W)).length
      ≤ Nat.card ↥{V : Perm (Fin n) | ∀ x, κ (V x) = W (κ x)} := by
  classical
  set t0 := lensCode κ with ht0
  set t1 := lensCode W with ht1
  have : Fintype ↥{V : Perm (Fin n) | ∀ x, κ (V x) = W (κ x)} := Fintype.ofFinite _
  have hnodup : (candListDescent n t0 t1).Nodup := List.nodup_range.filter _
  have hmem : ∀ w ∈ (candListDescent n t0 t1).toFinset, w < n ^ n ∧ isValidDescent n t0 t1 w := by
    intro w hw
    rw [List.mem_toFinset, candListDescent, List.mem_filter, List.mem_range,
      decide_eq_true_eq] at hw
    exact hw
  set f : ℕ → ↥{V : Perm (Fin n) | ∀ x, κ (V x) = W (κ x)} := fun w =>
    if h : isValidDescent n t0 t1 w then ⟨candPerm n w, candPerm_mem_descentSet hn h⟩
    else ⟨U, hU⟩ with hf
  have hcard := Finset.card_le_card_of_injOn f
    (s := (candListDescent n t0 t1).toFinset) (t := Finset.univ)
    (fun w _ => Finset.mem_univ (f w))
    (by
      intro w1 hw1 w2 hw2 heq
      rw [Finset.mem_coe] at hw1 hw2
      have h1 := hmem w1 hw1
      have h2 := hmem w2 hw2
      have hfw1 : f w1 = ⟨candPerm n w1, candPerm_mem_descentSet hn h1.2⟩ := dif_pos h1.2
      have hfw2 : f w2 = ⟨candPerm n w2, candPerm_mem_descentSet hn h2.2⟩ := dif_pos h2.2
      rw [hfw1, hfw2, Subtype.mk_eq_mk] at heq
      have hb1 : candBijBool n w1 = true := h1.2.1
      have hb2 : candBijBool n w2 = true := h2.2.1
      have hdig : ∀ i : Fin n, digitAt n w1 (i : ℕ) = digitAt n w2 (i : ℕ) := by
        intro i
        rw [← candPerm_apply hn hb1 i, ← candPerm_apply hn hb2 i, heq]
      apply candTable_injOn h1.1 h2.1
      change (List.range n).map (digitAt n w1) = (List.range n).map (digitAt n w2)
      refine List.map_congr_left fun j hj => ?_
      exact hdig ⟨j, List.mem_range.mp hj⟩)
  rw [← List.toFinset_card_of_nodup hnodup, Nat.card_eq_fintype_card]
  simpa using hcard

/-- **The factor ledger's display** ([Persistence] §8, Corollary 8.11(i)): `ledger_graded`'s own
enumerate-filter-select decoder, at the descent predicate — `κ`'s table, `W`'s table, and a coset
INDEX into the descent set `card_descentCoset` counts recover `U`'s table exactly, at the same
`O (Nat.size (∏ᵢ fiberᵢ!))` index cost and the same `O (Nat.size n)` search-bound term
`ledger_graded` pays. This target moves where `ledger_graded`'s own encoding boundary SITS — a
factor's law rather than a second frame — and claims no more: the display's unit-coefficient
length-conditional index field stays paper-level, exactly as it does at two frames. -/
theorem ledger_descent (hn : 0 < n) {z : ℕ} (κ : Fin n → Fin z) (W : Fin z → Fin z)
    {U : Perm (Fin n)} (hU : ∀ x, κ (U x) = W (κ x)) :
    KE (lensCode U) ≤ KE (lensCode κ) + KE (lensCode W)
      + (15 + elen dbl) * Nat.size (∏ i : Fin z, (Nat.card {x : Fin n // κ x = i})!)
      + (15 + elen dbl) * Nat.size n
      + (elen gradedBuilderDescent + 2 * (15 + elen dbl) + 39) := by
  set t0 := lensCode κ with ht0
  set t1 := lensCode W with ht1
  set N := ∏ i : Fin z, (Nat.card {x : Fin n // κ x = i})! with hNdef
  have hvalid : isValidDescent n t0 t1 (worldNumeral U) := isValidDescent_worldNumeral hn hU
  have hlt : worldNumeral U < n ^ n := worldNumeral_lt hn U
  have hmem : worldNumeral U ∈ candListDescent n t0 t1 := by
    rw [candListDescent, List.mem_filter, List.mem_range, decide_eq_true_eq]
    exact ⟨hlt, hvalid⟩
  obtain ⟨idx, hidxlt, hidxeq⟩ := List.getElem_of_mem hmem
  have hlenle : (candListDescent n t0 t1).length ≤ N := by
    rw [hNdef]
    calc (candListDescent n t0 t1).length
        ≤ Nat.card ↥{V : Perm (Fin n) | ∀ x, κ (V x) = W (κ x)} :=
          candListDescent_length_le hn hU
      _ = N := card_descentCoset κ W hU
  have hidxN : idx < N := lt_of_lt_of_le hidxlt hlenle
  have hgetD : List.getD (candListDescent n t0 t1) idx 0 = worldNumeral U := by
    rw [List.getD_eq_getElem _ _ hidxlt]; exact hidxeq
  have heval : gradedTableFnDescent (Nat.pair n (Nat.pair t0 (Nat.pair t1 idx))) = lensCode U := by
    rw [gradedTableFnDescent]
    simp only [Nat.unpair_pair]
    rw [hgetD]
    exact congrArg Encodable.encode (candTable_packMarks hn U)
  obtain ⟨c0, hc0, hlc0⟩ := exists_min_E t0
  obtain ⟨c1, hc1, hlc1⟩ := exists_min_E t1
  have hz : eval zero (0 : ℕ) = Part.some 0 := rfl
  have hn' : eval (bconst n) 0 = Part.some n := eval_bconst n 0
  have h0 : eval (comp c0 zero) 0 = Part.some t0 := (eval_comp_some hz).trans hc0
  have h1 : eval (comp c1 zero) 0 = Part.some t1 := (eval_comp_some hz).trans hc1
  have hb : eval (bconst idx) 0 = Part.some idx := eval_bconst idx 0
  have hpair3 : eval (pair (comp c1 zero) (bconst idx)) 0 = Part.some (Nat.pair t1 idx) := by
    change Nat.pair <$> _ <*> _ = _
    rw [h1, hb]; simp [Seq.seq]
  have hpair2 : eval (pair (comp c0 zero) (pair (comp c1 zero) (bconst idx))) 0
      = Part.some (Nat.pair t0 (Nat.pair t1 idx)) := by
    change Nat.pair <$> _ <*> _ = _
    rw [h0, hpair3]; simp [Seq.seq]
  have hpair1 : eval (pair (bconst n) (pair (comp c0 zero) (pair (comp c1 zero) (bconst idx)))) 0
      = Part.some (Nat.pair n (Nat.pair t0 (Nat.pair t1 idx))) := by
    change Nat.pair <$> _ <*> _ = _
    rw [hn', hpair2]; simp [Seq.seq]
  have hcomp : Computes
      (comp gradedBuilderDescent
        (pair (bconst n) (pair (comp c0 zero) (pair (comp c1 zero) (bconst idx)))))
      (lensCode U) := by
    change eval (comp gradedBuilderDescent
      (pair (bconst n) (pair (comp c0 zero) (pair (comp c1 zero) (bconst idx))))) 0 = _
    rw [eval_comp_some hpair1, eval_gradedBuilderDescent, heval]
  have hle := KE_le hcomp
  rw [E_len_comp, E_len_pair, E_len_pair, E_len_comp, E_len_pair, E_len_comp] at hle
  have hzlen : elen (zero : Code) = 3 := rfl
  have hbc := elen_bconst_le idx
  have hbn := elen_bconst_le n
  have hidxsize : Nat.size idx ≤ Nat.size N := Nat.size_le_size (le_of_lt hidxN)
  have hidxsize' : (15 + elen dbl) * Nat.size idx ≤ (15 + elen dbl) * Nat.size N :=
    Nat.mul_le_mul_left _ hidxsize
  rw [hzlen, hlc0, hlc1] at hle
  omega

/-! ## Remark 6.6: the paired frame — an address is paid once

[Persistence] §6, Remark 6.6: Theorem 6.4's decoder never needs its two frames separately, only the
two tables *together*. Writing `ℓ₀ ⊗ ℓ₁ : [n] → M × M` for the paired frame and pricing it via
`Nat.pair` rather than a genuine product type keeps the loaded alphabet at `m * m` — no size
parameter beyond `m` itself enters, which is what keeps the decoder's constant absolute.
The remark's two displays are `K(U) ≤ K(ℓ₀ ⊗ ℓ₁) + log₂ ∏ᵢ fᵢ! + O(1)` and
`K(ℓ₀ ⊗ ℓ₁) ≤ K(ℓ₀) + K(ℓ₁) + O(1)`; the first is `ledger_graded_paired` below, reusing
`ledger_graded`'s own decoder read off one table instead of two, and the second is
`KE_lensCode_pairLens_le`. Both are machine-checked; the boundary is FV-17's, unchanged — the
display's unit-coefficient length-conditional index field stays paper-level,
exactly as it does at two separate frames. -/

private theorem pair_lt_mul_self {a b k : ℕ} (ha : a < k) (hb : b < k) : Nat.pair a b < k * k := by
  rw [Nat.pair]
  split
  · next h => nlinarith
  · next h => nlinarith

/-- **The paired frame, as a lens** ([Persistence] §6, Remark 6.6): the two frames read together,
`x ↦ Nat.pair (ℓ₀ x) (ℓ₁ x)`, landing in `Fin (m * m)` by `pair_lt_mul_self`. The pairing fills
that alphabet rather than embedding into a larger one, so `M × M` is the honest
codomain; only the upper bound is proved here, which is all the ledger below consumes.
`Nat.pair`, not `finProdFinEquiv`, is a fidelity
requirement: a `finProdFinEquiv` pairing would have to LOAD `m` to reconstruct itself, charging
`Nat.size m` and turning the remark's `O(1)` into an `O(log₂ m)` the paper does not claim. -/
def pairLens (ℓ₀ ℓ₁ : Fin n → Fin m) : Fin n → Fin (m * m) :=
  fun x => ⟨Nat.pair (ℓ₀ x : ℕ) (ℓ₁ x : ℕ), pair_lt_mul_self (ℓ₀ x).2 (ℓ₁ x).2⟩

/-- Projection recovers the first frame. -/
theorem pairLens_left (ℓ₀ ℓ₁ : Fin n → Fin m) (x : Fin n) :
    (Nat.unpair (pairLens ℓ₀ ℓ₁ x : ℕ)).1 = (ℓ₀ x : ℕ) := by
  simp [pairLens]

/-- Projection recovers the second frame. -/
theorem pairLens_right (ℓ₀ ℓ₁ : Fin n → Fin m) (x : Fin n) :
    (Nat.unpair (pairLens ℓ₀ ℓ₁ x : ℕ)).2 = (ℓ₁ x : ℕ) := by
  simp [pairLens]

/-- **Composing on the right commutes with pairing**: the paired frame of two precomposed lenses is
the precomposition of the paired frame — near-definitional, and the reason one description of a
region serves both frames at once (consumed by `pairLens_descends_iff`). -/
theorem pairLens_comp {k : ℕ} (ℓ₀ ℓ₁ : Fin n → Fin m) (φ : Fin k → Fin n) :
    pairLens ℓ₀ ℓ₁ ∘ φ = pairLens (ℓ₀ ∘ φ) (ℓ₁ ∘ φ) := by
  funext x
  simp [pairLens, Function.comp_apply]

/-- **The transport clause, as descent** ([Persistence] §6, Remark 6.6: "the quotient of the pair is
the pair of the quotients"): a map descends the paired frame exactly when it descends both frames
separately. The economy is exactly `pairLens_comp`'s: composing on the right commutes with pairing,
so a single description of the region or the quotient carries both frames' descent conditions at
once, and the address for one is the address for the other. -/
theorem pairLens_descends_iff {α : Type*} (κ : Fin n → α) (ℓ₀ ℓ₁ : Fin n → Fin m) :
    (∀ x y, κ x = κ y → pairLens ℓ₀ ℓ₁ x = pairLens ℓ₀ ℓ₁ y) ↔
      ((∀ x y, κ x = κ y → ℓ₀ x = ℓ₀ y) ∧ (∀ x y, κ x = κ y → ℓ₁ x = ℓ₁ y)) := by
  constructor
  · intro h
    refine ⟨fun x y hxy => ?_, fun x y hxy => ?_⟩
    · have hp := congrArg (fun z : Fin (m * m) => (Nat.unpair (z : ℕ)).1) (h x y hxy)
      simp only [pairLens_left] at hp
      exact Fin.val_injective hp
    · have hp := congrArg (fun z : Fin (m * m) => (Nat.unpair (z : ℕ)).2) (h x y hxy)
      simp only [pairLens_right] at hp
      exact Fin.val_injective hp
  · rintro ⟨h0, h1⟩ x y hxy
    apply Fin.val_injective
    change Nat.pair (ℓ₀ x : ℕ) (ℓ₁ x : ℕ) = Nat.pair (ℓ₀ y : ℕ) (ℓ₁ y : ℕ)
    rw [h0 x y hxy, h1 x y hxy]

/-- **Two tables, zipped**: entrywise `Nat.pair`, read off the position each shares — the list
operation the paired frame's builder performs on two lens tables. Both operands here are always
equal-length (two `lensTable`s of the same domain `Fin n`), so `List.range T₀.length` indexes every
shared position. -/
def zipLists (T₀ T₁ : List ℕ) : List ℕ := (List.range T₀.length).map fun i => Nat.pair (T₀.getD i 0)
  (T₁.getD i 0)

private theorem primrec_zipLists : Primrec fun q : List ℕ × List ℕ => zipLists q.1 q.2 := by
  have hrange : Primrec fun q : List ℕ × List ℕ => List.range q.1.length :=
    Primrec.list_range.comp (Primrec.list_length.comp Primrec.fst)
  have hg : Primrec fun p : (List ℕ × List ℕ) × ℕ =>
      Nat.pair (p.1.1.getD p.2 0) (p.1.2.getD p.2 0) := by
    have hl0 : Primrec fun p : (List ℕ × List ℕ) × ℕ => p.1.1 := Primrec.fst.comp Primrec.fst
    have hl1 : Primrec fun p : (List ℕ × List ℕ) × ℕ => p.1.2 := Primrec.snd.comp Primrec.fst
    have hi : Primrec fun p : (List ℕ × List ℕ) × ℕ => p.2 := Primrec.snd
    have hg0 : Primrec fun p : (List ℕ × List ℕ) × ℕ => p.1.1.getD p.2 0 :=
      (Primrec.list_getD 0).comp hl0 hi
    have hg1 : Primrec fun p : (List ℕ × List ℕ) × ℕ => p.1.2.getD p.2 0 :=
      (Primrec.list_getD 0).comp hl1 hi
    exact Primrec₂.natPair.comp hg0 hg1
  exact Primrec.list_map hrange hg

/-- **Zipping the two tables is tabulating the paired frame**: the fidelity fact that lets the
paired-frame builder work on the two ordinary `lensTable`s. -/
theorem zipLists_eq_lensTable (ℓ₀ ℓ₁ : Fin n → Fin m) :
    zipLists (lensTable ℓ₀) (lensTable ℓ₁) = lensTable (pairLens ℓ₀ ℓ₁) := by
  have hlen : (lensTable ℓ₀).length = n := by simp [lensTable]
  rw [zipLists, hlen, lensTable, lensTable, lensTable]
  have hfr : (List.finRange n).map Fin.val = List.range n := by simp
  rw [← hfr, List.map_map]
  refine List.map_congr_left fun i _ => ?_
  simp only [Function.comp_apply]
  rw [getD_map_finRange (fun x : Fin n => (ℓ₀ x : ℕ)) i,
    getD_map_finRange (fun x : Fin n => (ℓ₁ x : ℕ)) i]
  rfl

/-- **The zip builder's table function**: reads `p`'s two halves as encoded lists and returns their
`Nat.pair`-zip, encoded — the fixed function `KE_lensCode_pairLens_le`'s builder runs on the two
given frame codes. -/
private def zipTableFn (p : ℕ) : ℕ :=
  Encodable.encode
    (zipLists ((Encodable.decode (α := List ℕ) p.unpair.1).getD [])
      ((Encodable.decode (α := List ℕ) p.unpair.2).getD []))

private theorem primrec_zipTableFn : Primrec zipTableFn := by
  have hdec1 : Primrec fun p : ℕ => (Encodable.decode (α := List ℕ) p.unpair.1).getD [] :=
    Primrec.option_getD.comp (Primrec.decode.comp (Primrec.fst.comp Primrec.unpair))
      (Primrec.const [])
  have hdec2 : Primrec fun p : ℕ => (Encodable.decode (α := List ℕ) p.unpair.2).getD [] :=
    Primrec.option_getD.comp (Primrec.decode.comp (Primrec.snd.comp Primrec.unpair))
      (Primrec.const [])
  exact Primrec.encode.comp (primrec_zipLists.comp (Primrec.pair hdec1 hdec2))

/-- **The builder is correct**: on `⟨ℓ₀'s table, ℓ₁'s table⟩` it outputs the paired frame's encoded
tabulation. -/
theorem zipTableFn_eq (ℓ₀ ℓ₁ : Fin n → Fin m) :
    zipTableFn (Nat.pair (lensCode ℓ₀) (lensCode ℓ₁)) = lensCode (pairLens ℓ₀ ℓ₁) := by
  have hd0 : (Encodable.decode (α := List ℕ) (lensCode ℓ₀)).getD [] = lensTable ℓ₀ := by
    rw [lensCode, Encodable.encodek]; rfl
  have hd1 : (Encodable.decode (α := List ℕ) (lensCode ℓ₁)).getD [] = lensTable ℓ₁ := by
    rw [lensCode, Encodable.encodek]; rfl
  rw [zipTableFn]
  simp only [Nat.unpair_pair]
  rw [hd0, hd1, zipLists_eq_lensTable]
  rfl

private theorem partrec_zipTableFn : Nat.Partrec (fun p : ℕ => (zipTableFn p : ℕ)) :=
  _root_.Partrec.nat_iff.mp (Primrec.to_comp primrec_zipTableFn).partrec

/-- **The fixed zip-builder code.** One program, independent of `n`, `m`, and the two lenses. -/
noncomputable def zipBuilder : Nat.Partrec.Code :=
  Classical.choose (Nat.Partrec.Code.exists_code.mp partrec_zipTableFn)

private theorem eval_zipBuilder (p : ℕ) :
    Nat.Partrec.Code.eval zipBuilder p = Part.some (zipTableFn p) := by
  have h := congrFun (Classical.choose_spec
    (Nat.Partrec.Code.exists_code.mp partrec_zipTableFn)) p
  simpa [zipBuilder] using h

/-- **A fixed program zips two tables** ([Persistence] §6, Remark 6.6): `K(ℓ₀ ⊗ ℓ₁) ≤ K(ℓ₀) + K(ℓ₁)
+ O(1)`, with the constant a closed numeral in `elen` — no `Nat.size n` or `Nat.size m` term, which
is what makes the paired display a strengthening rather than a trade. -/
noncomputable def pairZipConst : ℕ := elen zipBuilder + 6

theorem KE_lensCode_pairLens_le (ℓ₀ ℓ₁ : Fin n → Fin m) :
    KE (lensCode (pairLens ℓ₀ ℓ₁)) ≤ KE (lensCode ℓ₀) + KE (lensCode ℓ₁) + pairZipConst := by
  obtain ⟨c₀, hc₀, hlc₀⟩ := exists_min_E (lensCode ℓ₀)
  obtain ⟨c₁, hc₁, hlc₁⟩ := exists_min_E (lensCode ℓ₁)
  have hp : eval (pair c₀ c₁) 0 = Part.some (Nat.pair (lensCode ℓ₀) (lensCode ℓ₁)) := by
    change Nat.pair <$> _ <*> _ = _
    rw [hc₀, hc₁]; simp [Seq.seq]
  have hcomp : Computes (comp zipBuilder (pair c₀ c₁)) (lensCode (pairLens ℓ₀ ℓ₁)) := by
    change eval (comp zipBuilder (pair c₀ c₁)) 0 = _
    rw [eval_comp_some hp, eval_zipBuilder, zipTableFn_eq]
  have hle := KE_le hcomp
  rw [E_len_comp, E_len_pair] at hle
  rw [pairZipConst]
  omega

/-! ## The paired table from one uniform code ([Persistence] §7, the v13 sharpening)

A `UniformBudget` witness `c` is a *single* program computing every frame's table from its clock
input, not two independent per-frame descriptions. Reading `c` off at `t = 0` and `t = 1` separately
and zipping the results (`KE_lensCode_pairLens_le`'s route) embeds `c` *twice* — once per frame —
and pays `2 · elen c`. `pairFromUniformCode` below embeds `c` exactly *once*: it is a fixed two-step
primitive-recursive iterator whose step calls `c` on the recursion's own index (`comp c projIdx`)
rather than on a hardcoded clock constant, so the same subterm is *run* twice at evaluation time
without being *written* twice in the assembled program. This is `Collector.lean`'s `collector`/
`stepWrap` template (`elen (collector cR) = elen cR + 60`, paid once regardless of how many times
the rule iterates) specialized to exactly two calls at the recursion index rather than at the
accumulated state. -/

/-- Extracts the recursion index `n` from a `prec`-step input `Nat.pair a (Nat.pair n prev)` — the
companion projection to `AdditiveComplexity.projIH` (which extracts `prev`). -/
private def projIdx : Code := comp left right

private theorem eval_projIdx (a n prev : ℕ) :
    eval projIdx (Nat.pair a (Nat.pair n prev)) = Part.some n := by
  rw [projIdx, eval_comp_some (eval_right' _), eval_left']
  simp

private theorem elen_projIdx : elen projIdx = 9 := by decide

/-- **The step function**: pairs the accumulator so far with `c` run at the current recursion index.
`c` occurs exactly once, composed with `projIdx` rather than hardcoded to a clock value. -/
private def pairStep (c : Code) : Code := pair projIH (comp c projIdx)

private theorem eval_pairStep {c : Code} {v : ℕ → ℕ} (hc : ∀ t, eval c t = Part.some (v t))
    (a n prev : ℕ) :
    eval (pairStep c) (Nat.pair a (Nat.pair n prev)) = Part.some (Nat.pair prev (v n)) := by
  have h1 : eval projIH (Nat.pair a (Nat.pair n prev)) = Part.some prev := eval_projIH a n prev
  have h2 : eval (comp c projIdx) (Nat.pair a (Nat.pair n prev)) = Part.some (v n) := by
    rw [eval_comp_some (eval_projIdx a n prev), hc]
  change Nat.pair <$> eval projIH _ <*> eval (comp c projIdx) _ = _
  rw [h1, h2]
  simp [Seq.seq]

private theorem elen_pairStep (c : Code) : elen (pairStep c) = elen c + 24 := by
  rw [pairStep, E_len_pair, E_len_comp, elen_projIH, elen_projIdx]
  omega

/-- **The fixed two-step iterator**: primitive recursion with base `zero` and step `pairStep c`.
`elen (pairFromCode c) = elen c + 30` (`elen_pairFromCode`) — a fixed constant plus `c`, paid once
regardless of the two calls the recursion makes. -/
private def pairFromCode (c : Code) : Code := prec Code.zero (pairStep c)

/-- The accumulator `pairFromCode` builds: `pairAcc v 0 = 0`,
`pairAcc v (k+1) = (pairAcc v k, v k)`. Mirrors `Collector.orbitAcc`'s shape. -/
private def pairAcc (v : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => Nat.pair (pairAcc v k) (v k)

private theorem eval_pairFromCode {c : Code} {v : ℕ → ℕ} (hc : ∀ t, eval c t = Part.some (v t))
    (a k : ℕ) : eval (pairFromCode c) (Nat.pair a k) = Part.some (pairAcc v k) := by
  induction k with
  | zero => rw [pairFromCode, eval_prec_zero]; rfl
  | succ j ih =>
    rw [pairFromCode, eval_prec_succ]
    rw [show pairFromCode c = Code.zero.prec (pairStep c) from rfl] at ih
    rw [ih]
    rw [show (Part.some (pairAcc v j)) >>= (fun i => eval (pairStep c) (Nat.pair a (Nat.pair j i)))
        = eval (pairStep c) (Nat.pair a (Nat.pair j (pairAcc v j))) from Part.bind_some _ _]
    rw [eval_pairStep hc a j (pairAcc v j)]
    rfl

private theorem elen_pairFromCode (c : Code) : elen (pairFromCode c) = elen c + 30 := by
  rw [pairFromCode, E_len_prec, elen_pairStep]
  have hz : elen (Code.zero) = 3 := rfl
  omega

/-- **Extraction**: unwinds `pairFromCode`'s two-step accumulator `((0, x), y)` into `(x, y)`. -/
private def pairExtract : Code := pair (comp right left) right

private theorem eval_pairExtract (x y : ℕ) :
    eval pairExtract (Nat.pair (Nat.pair 0 x) y) = Part.some (Nat.pair x y) := by
  have h1 : eval (comp right left) (Nat.pair (Nat.pair 0 x) y) = Part.some x := by
    rw [eval_comp_some (eval_left' _), eval_right']
    simp
  have h2 : eval right (Nat.pair (Nat.pair 0 x) y) = Part.some y := by rw [eval_right']; simp
  change Nat.pair <$> eval (comp right left) _ <*> eval right _ = _
  rw [h1, h2]
  simp [Seq.seq]

private theorem elen_pairExtract : elen pairExtract = 15 := by decide

/-- **A uniformly-budgeted family's first two frames, read as one paired code**: `c` embedded
exactly once, run at the fixed two-step iterator's own recursion index, then unwound. -/
noncomputable def pairFromUniformCode (c : Code) : Code :=
  comp pairExtract (comp (pairFromCode c) (pair Code.zero (bconst 2)))

private theorem eval_pairFromUniformCode {c : Code} {v : ℕ → ℕ}
    (hc : ∀ t, eval c t = Part.some (v t)) :
    eval (pairFromUniformCode c) 0 = Part.some (Nat.pair (v 0) (v 1)) := by
  have hin : eval (pair Code.zero (bconst 2)) 0 = Part.some (Nat.pair 0 2) := by
    have hz : eval (Code.zero) (0 : ℕ) = Part.some 0 := rfl
    change Nat.pair <$> eval Code.zero 0 <*> eval (bconst 2) 0 = _
    rw [hz, eval_bconst]; simp [Seq.seq]
  have hacc : pairAcc v 2 = Nat.pair (Nat.pair 0 (v 0)) (v 1) := rfl
  have hmid : eval (pairFromCode c) (Nat.pair 0 2)
      = Part.some (Nat.pair (Nat.pair 0 (v 0)) (v 1)) := by
    rw [eval_pairFromCode hc 0 2, hacc]
  have hcomp2 : eval (comp (pairFromCode c) (pair Code.zero (bconst 2))) 0
      = Part.some (Nat.pair (Nat.pair 0 (v 0)) (v 1)) := by
    rw [eval_comp_some hin, hmid]
  rw [pairFromUniformCode, eval_comp_some hcomp2, eval_pairExtract]

private theorem elen_pairFromUniformCode (c : Code) :
    elen (pairFromUniformCode c) = elen c + (57 + elen (bconst 2)) := by
  rw [pairFromUniformCode, E_len_comp, E_len_comp, E_len_pair, elen_pairFromCode, elen_pairExtract]
  have hz : elen (Code.zero) = 3 := rfl
  omega

/-- **Target A — the paired table costs one budget, not two.** From a `UniformBudget` witness of
length at most `b`, the paired frame of frames `0` and `1` is computable at `b` plus an absolute
constant — coefficient `1` on `b`, not the `2` that reading the two frames off separately and
zipping them (`KE_lensCode_pairLens_le`) would pay. The clock inputs are constants (`t = 0, 1`), so
`bconst 2`'s own cost is the only variable term, and it is bounded by `Nat.size 2 = 2`, an absolute
numeral. -/
theorem uniformBudget_pairLens_le {ℓ : ℕ → Fin n → Fin m} {b : ℕ} (h : UniformBudget ℓ b) :
    KE (lensCode (pairLens (ℓ 0) (ℓ 1)))
      ≤ b + (57 + 3 * (15 + elen dbl) + elen zipBuilder + 6) := by
  obtain ⟨c, hlen, heval⟩ := h
  have hcomp : Computes (comp zipBuilder (pairFromUniformCode c))
      (lensCode (pairLens (ℓ 0) (ℓ 1))) := by
    change eval (comp zipBuilder (pairFromUniformCode c)) 0 = _
    rw [eval_comp_some (eval_pairFromUniformCode heval), eval_zipBuilder, zipTableFn_eq]
  have hle := KE_le hcomp
  rw [E_len_comp, elen_pairFromUniformCode] at hle
  have hb2 : elen (bconst 2) ≤ 3 * (15 + elen dbl) := by
    have := elen_bconst_le 2
    have hs : Nat.size 2 = 2 := rfl
    rw [hs] at this
    omega
  omega

/-! ### Remark 6.6's display: the frame term at one address -/

/-- Recovering the first frame's table from a zipped one: `Nat.unpair` applied entrywise. -/
private def unzipFst (T : List ℕ) : List ℕ := T.map fun e => (Nat.unpair e).1

/-- Recovering the second frame's table from a zipped one. -/
private def unzipSnd (T : List ℕ) : List ℕ := T.map fun e => (Nat.unpair e).2

private theorem primrec_unzipFst : Primrec unzipFst :=
  Primrec.list_map Primrec.id (Primrec.fst.comp (Primrec.unpair.comp Primrec.snd))

private theorem primrec_unzipSnd : Primrec unzipSnd :=
  Primrec.list_map Primrec.id (Primrec.snd.comp (Primrec.unpair.comp Primrec.snd))

/-- Unzipping the paired frame's table recovers the first frame's table — the converse fidelity
fact to `zipLists_eq_lensTable`. -/
private theorem unzipFst_lensTable_pairLens (ℓ₀ ℓ₁ : Fin n → Fin m) :
    unzipFst (lensTable (pairLens ℓ₀ ℓ₁)) = lensTable ℓ₀ := by
  rw [unzipFst, lensTable, lensTable, List.map_map]
  refine List.map_congr_left fun i _ => ?_
  simp only [Function.comp_apply]
  exact pairLens_left ℓ₀ ℓ₁ i

/-- Unzipping the paired frame's table recovers the second frame's table. -/
private theorem unzipSnd_lensTable_pairLens (ℓ₀ ℓ₁ : Fin n → Fin m) :
    unzipSnd (lensTable (pairLens ℓ₀ ℓ₁)) = lensTable ℓ₁ := by
  rw [unzipSnd, lensTable, lensTable, List.map_map]
  refine List.map_congr_left fun i _ => ?_
  simp only [Function.comp_apply]
  exact pairLens_right ℓ₀ ℓ₁ i

/-- **The paired-frame tabulation, rebuilt from the packed program** `⟨n, pairCode, idx⟩`: unzip
the paired table back into the two frame tables and hand them to `gradedTableFn`'s own decoder — ONE
fixed function reusing Theorem 6.4's decoder rather than duplicating it, so the frame term the
resulting bound pays occurs exactly once. -/
private def pairedGradedTableFn (a : ℕ) : ℕ :=
  gradedTableFn
    (Nat.pair a.unpair.1
      (Nat.pair
        (Encodable.encode
          (unzipFst ((Encodable.decode (α := List ℕ) a.unpair.2.unpair.1).getD [])))
        (Nat.pair
          (Encodable.encode
            (unzipSnd ((Encodable.decode (α := List ℕ) a.unpair.2.unpair.1).getD [])))
          a.unpair.2.unpair.2)))

set_option maxHeartbeats 1000000 in
-- multi-level packing meets `primrec_gradedTableFn`, the same headroom reason as
-- `primrec_gradedTableFn` itself needs against `primrec_candList`.
private theorem primrec_pairedGradedTableFn : Primrec pairedGradedTableFn := by
  have hN : Primrec fun a : ℕ => a.unpair.1 := Primrec.fst.comp Primrec.unpair
  have hPC : Primrec fun a : ℕ => a.unpair.2.unpair.1 :=
    Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))
  have hIdx : Primrec fun a : ℕ => a.unpair.2.unpair.2 :=
    Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))
  have hDec : Primrec fun a : ℕ => (Encodable.decode (α := List ℕ) a.unpair.2.unpair.1).getD [] :=
    Primrec.option_getD.comp (Primrec.decode.comp hPC) (Primrec.const [])
  have hT0 : Primrec fun a : ℕ => Encodable.encode (unzipFst
      ((Encodable.decode (α := List ℕ) a.unpair.2.unpair.1).getD [])) :=
    Primrec.encode.comp (primrec_unzipFst.comp hDec)
  have hT1 : Primrec fun a : ℕ => Encodable.encode (unzipSnd
      ((Encodable.decode (α := List ℕ) a.unpair.2.unpair.1).getD [])) :=
    Primrec.encode.comp (primrec_unzipSnd.comp hDec)
  have hPacked : Primrec fun a : ℕ =>
      Nat.pair a.unpair.1 (Nat.pair (Encodable.encode (unzipFst
        ((Encodable.decode (α := List ℕ) a.unpair.2.unpair.1).getD [])))
        (Nat.pair (Encodable.encode (unzipSnd
          ((Encodable.decode (α := List ℕ) a.unpair.2.unpair.1).getD [])))
          a.unpair.2.unpair.2)) :=
    Primrec₂.natPair.comp hN (Primrec₂.natPair.comp hT0 (Primrec₂.natPair.comp hT1 hIdx))
  exact primrec_gradedTableFn.comp hPacked

/-- **The builder is correct**: unzipping the paired code before running `gradedTableFn`'s decoder
is the same as running it on the two separate frame codes — this is the whole content of "an address
is paid once". -/
private theorem pairedGradedTableFn_eq (n idx : ℕ) {m : ℕ} (ℓ₀ ℓ₁ : Fin n → Fin m) :
    pairedGradedTableFn (Nat.pair n (Nat.pair (lensCode (pairLens ℓ₀ ℓ₁)) idx))
      = gradedTableFn (Nat.pair n (Nat.pair (lensCode ℓ₀) (Nat.pair (lensCode ℓ₁) idx))) := by
  have hpc : (Encodable.decode (α := List ℕ) (lensCode (pairLens ℓ₀ ℓ₁))).getD []
      = lensTable (pairLens ℓ₀ ℓ₁) := by rw [lensCode, Encodable.encodek]; rfl
  rw [pairedGradedTableFn]
  simp only [Nat.unpair_pair]
  rw [hpc, unzipFst_lensTable_pairLens, unzipSnd_lensTable_pairLens]
  rfl

private theorem partrec_pairedGradedTableFn :
    Nat.Partrec (fun a : ℕ => (pairedGradedTableFn a : ℕ)) :=
  _root_.Partrec.nat_iff.mp (Primrec.to_comp primrec_pairedGradedTableFn).partrec

/-- **The fixed paired-graded-ledger builder code.** One program, independent of `n`, the world, and
the two lenses. -/
noncomputable def pairedGradedBuilder : Nat.Partrec.Code :=
  Classical.choose (Nat.Partrec.Code.exists_code.mp partrec_pairedGradedTableFn)

private theorem eval_pairedGradedBuilder (a : ℕ) :
    Nat.Partrec.Code.eval pairedGradedBuilder a = Part.some (pairedGradedTableFn a) := by
  have h := congrFun (Classical.choose_spec
    (Nat.Partrec.Code.exists_code.mp partrec_pairedGradedTableFn)) a
  simpa [pairedGradedBuilder] using h

/-- **The paired ledger's constant**: one fixed builder plus the assembly's opcodes — `n`, the
paired frame code, and the coset index, three loaded pieces against `ledger_graded`'s four. -/
noncomputable def pairedLedgerConst : ℕ := elen pairedGradedBuilder + 2 * (15 + elen dbl) + 15

/-- **The graded ledger, at the paired frame, from the persistence identity alone** ([Persistence]
§6, Remark 6.6): the `PermPersists`-only base `ledger_graded_paired` corollaries from, exactly as
`ledger_graded` is the base `ledger_graded_lossy` reduces to — the coset argument below never reads
`ℓ 0`'s surjectivity, only its persistence. Theorem 6.4's own decoder, unzipping the paired frame's
table before running `ledger_graded`'s search, so the frame term occurs ONCE —
`KE (lensCode (pairLens (ℓ 0) (ℓ 1)))` rather than the two separate frame prices `ledger_graded`
charges. Everything upstream of the code assembly — the coset argument, the world's own numeral as a
valid candidate, the index bound by the coset size — is `ledger_graded`'s own, unchanged; only where
the candidate table's two halves come from differs. -/
private theorem ledger_graded_paired_persists (hn : 0 < n) {U : Perm (Fin n)}
    {ℓ : ℕ → Fin n → Fin m} (hpers : PermPersists U ℓ) :
    KE (lensCode U) ≤ KE (lensCode (pairLens (ℓ 0) (ℓ 1)))
      + (15 + elen dbl) * Nat.size (∏ i : Fin m, (Nat.card {x : Fin n // ℓ 0 x = i})!)
      + (15 + elen dbl) * Nat.size n
      + pairedLedgerConst := by
  set t0 := lensCode (ℓ 0) with ht0
  set t1 := lensCode (ℓ 1) with ht1
  set N := ∏ i : Fin m, (Nat.card {x : Fin n // ℓ 0 x = i})! with hNdef
  have hvalid : isValid n t0 t1 (worldNumeral U) := isValid_worldNumeral hn hpers
  have hlt : worldNumeral U < n ^ n := worldNumeral_lt hn U
  have hmem : worldNumeral U ∈ candList n t0 t1 := by
    rw [candList, List.mem_filter, List.mem_range, decide_eq_true_eq]
    exact ⟨hlt, hvalid⟩
  obtain ⟨idx, hidxlt, hidxeq⟩ := List.getElem_of_mem hmem
  have hlenle : (candList n t0 t1).length ≤ N := by
    rw [hNdef]
    calc (candList n t0 t1).length ≤ Nat.card ↥(stabilizer (Perm (Fin n)) (ℓ 0)) :=
          candList_length_le hn hpers
      _ = N := card_stabilizer_lens (ℓ 0)
  have hidxN : idx < N := lt_of_lt_of_le hidxlt hlenle
  have hgetD : List.getD (candList n t0 t1) idx 0 = worldNumeral U := by
    rw [List.getD_eq_getElem _ _ hidxlt]; exact hidxeq
  have heval : gradedTableFn (Nat.pair n (Nat.pair t0 (Nat.pair t1 idx))) = lensCode U := by
    rw [gradedTableFn]
    simp only [Nat.unpair_pair]
    rw [hgetD]
    exact congrArg Encodable.encode (candTable_packMarks hn U)
  have hevalp : pairedGradedTableFn (Nat.pair n (Nat.pair (lensCode (pairLens (ℓ 0) (ℓ 1))) idx))
      = lensCode U := by
    rw [pairedGradedTableFn_eq]
    exact heval
  obtain ⟨cp, hcp, hlcp⟩ := exists_min_E (lensCode (pairLens (ℓ 0) (ℓ 1)))
  have hz : eval zero (0 : ℕ) = Part.some 0 := rfl
  have hn' : eval (bconst n) 0 = Part.some n := eval_bconst n 0
  have hp0 : eval (comp cp zero) 0 = Part.some (lensCode (pairLens (ℓ 0) (ℓ 1))) :=
    (eval_comp_some hz).trans hcp
  have hb : eval (bconst idx) 0 = Part.some idx := eval_bconst idx 0
  have hpair3 : eval (pair (comp cp zero) (bconst idx)) 0
      = Part.some (Nat.pair (lensCode (pairLens (ℓ 0) (ℓ 1))) idx) := by
    change Nat.pair <$> _ <*> _ = _
    rw [hp0, hb]; simp [Seq.seq]
  have hpair1 : eval (pair (bconst n) (pair (comp cp zero) (bconst idx))) 0
      = Part.some (Nat.pair n (Nat.pair (lensCode (pairLens (ℓ 0) (ℓ 1))) idx)) := by
    change Nat.pair <$> _ <*> _ = _
    rw [hn', hpair3]; simp [Seq.seq]
  have hcomp : Computes
      (comp pairedGradedBuilder (pair (bconst n) (pair (comp cp zero) (bconst idx))))
      (lensCode U) := by
    change eval (comp pairedGradedBuilder
      (pair (bconst n) (pair (comp cp zero) (bconst idx)))) 0 = _
    rw [eval_comp_some hpair1, eval_pairedGradedBuilder, hevalp]
  have hle := KE_le hcomp
  rw [E_len_comp, E_len_pair, E_len_pair, E_len_comp] at hle
  have hzlen : elen (zero : Code) = 3 := rfl
  have hbc := elen_bconst_le idx
  have hbn := elen_bconst_le n
  have hidxsize : Nat.size idx ≤ Nat.size N := Nat.size_le_size (le_of_lt hidxN)
  have hidxsize' : (15 + elen dbl) * Nat.size idx ≤ (15 + elen dbl) * Nat.size N :=
    Nat.mul_le_mul_left _ hidxsize
  rw [hzlen, hlcp] at hle
  rw [pairedLedgerConst]
  omega

/-- **The graded ledger, at the paired frame** ([Persistence] §6, Remark 6.6): Theorem 6.4's own
decoder, unzipping the paired frame's table before running `ledger_graded`'s search, so the frame
term occurs ONCE — `KE (lensCode (pairLens (ℓ 0) (ℓ 1)))` rather than the two separate frame prices
`ledger_graded` charges. A corollary of `ledger_graded_paired_persists`, whose own coset argument
never reads `PermCarries`'s surjectivity of `ℓ 0` — only the persistence identity `hcar.2`. -/
theorem ledger_graded_paired (hn : 0 < n) {U : Perm (Fin n)} {ℓ : ℕ → Fin n → Fin m}
    (hcar : PermCarries U ℓ) :
    KE (lensCode U) ≤ KE (lensCode (pairLens (ℓ 0) (ℓ 1)))
      + (15 + elen dbl) * Nat.size (∏ i : Fin m, (Nat.card {x : Fin n // ℓ 0 x = i})!)
      + (15 + elen dbl) * Nat.size n
      + pairedLedgerConst :=
  ledger_graded_paired_persists hn hcar.2

/-- **Non-vacuity: the paired ledger recovers the maximal ledger's shape.** At singleton fibres
(`ℓ 0` bijective) the coset is trivial, exactly as in `ledger_graded_faithful`, and the paired bound
collapses the same way — with the frame term paid once. -/
theorem ledger_graded_paired_faithful (hn : 0 < n) {U : Perm (Fin n)} {ℓ : ℕ → Fin n → Fin m}
    (hcar : PermCarries U ℓ) (hbij : Function.Bijective (ℓ 0)) :
    KE (lensCode U) ≤ KE (lensCode (pairLens (ℓ 0) (ℓ 1)))
      + (15 + elen dbl) * Nat.size n
      + pairedLedgerConst + (15 + elen dbl) := by
  have hone : ∏ i : Fin m, (Nat.card {x : Fin n // ℓ 0 x = i})! = 1 := by
    refine Finset.prod_eq_one fun i _ => ?_
    have hcard : Nat.card {x : Fin n // ℓ 0 x = i} = 1 := by
      obtain ⟨x, hx, huniq⟩ := hbij.existsUnique i
      exact Nat.card_eq_one_iff_exists.mpr ⟨⟨x, hx⟩, fun y => Subtype.ext (huniq y y.2)⟩
    rw [hcard]; rfl
  have hbound := ledger_graded_paired hn hcar
  rw [hone] at hbound
  simp only [Nat.size_one, Nat.mul_one] at hbound
  omega

/-- **Target C — the general paired uniform cap.** `ledger_graded_paired_faithful` without the
bijectivity hypothesis: for *any* family carried at a uniform budget `b`, the world's table costs
one budget plus its own fibre defect — `KE (lensCode U) ≤ b + O (log n) + κ · Nat.size (∏ fiber!)`,
the coefficient-`1` reading of `ledger_graded_paired` once Target A supplies its frame term. The
fibre-product term is the same "defect" `ledger_graded_paired` already charges a non-faithful
reading, here run through Target A's cheaper frame term rather than two separate frame codes.
`ledger_graded_paired_faithful` (Target B) is the singleton-fibre special case, where the defect
term vanishes; `CbHu_collapse` stays beside both, unsuperseded — it bounds the FRACTION of worlds
exceeding a threshold across every reference frame at once, a statement this one does not make. -/
theorem uniformBudget_ledger_paired_le (hn : 0 < n) {U : Perm (Fin n)} {ℓ : ℕ → Fin n → Fin m}
    {b : ℕ} (hcar : PermCarries U ℓ) (hbud : UniformBudget ℓ b) :
    KE (lensCode U) ≤ b + (15 + elen dbl) * Nat.size n
      + (15 + elen dbl) * Nat.size (∏ i : Fin m, (Nat.card {x : Fin n // ℓ 0 x = i})!)
      + (63 + 3 * (15 + elen dbl) + elen zipBuilder + pairedLedgerConst) := by
  have hA := uniformBudget_pairLens_le hbud
  have hB := ledger_graded_paired hn hcar
  omega

/-- **The graded ledger's capstone**: at the family attaining `C_b^H (U)`, the coset's complementary
factor `N'` — with `C_b^H (U) · N' = n !` exactly (`card_orbit_mul_prod_fiber`, the entropic
capacity's own currency) — prices the world's complexity: `ledger_graded` plus the attained family's
per-frame budget caps `KE (lensCode U)` at the two-frame budget plus `N'`'s own bit-length.

**Reading.** Multiplying through, this is the paper's card form
`C_b^H (U) · 2^(KE(U)) ≤ 2^(2b+c) · n!` whenever the coset index is priced at coefficient `1` on
`Nat.size N'`; this development's `bconst` loading prices it at coefficient `15 + elen dbl` instead
(`elen_bconst_le`, the same loading `KE_markingLens_le`'s marks pay), which the CARD form cannot
absorb — at any coefficient `> 1` it turns vacuous over incompressible worlds, so the capstone is
stated here in the log-additive currency `ledger_graded` actually proves, with the
`n!`-factorization named explicitly rather than folded into a (false) product inequality. A literal
coefficient-`1` index encoding is future work. -/
theorem CbH_le_pointwise (hn : 0 < n) (U : Perm (Fin n)) (b : ℕ)
    (hne : (BudgetedEntropies U b).Nonempty) :
    ∃ N' : ℕ, CbH U b * N' = n ! ∧
      KE (lensCode U) ≤ 2 * b + (15 + elen dbl) * Nat.size N' + (15 + elen dbl) * Nat.size n
        + (elen gradedBuilder + 2 * (15 + elen dbl) + 39) := by
  obtain ⟨k, ℓ, hcar, hbud, hval⟩ : CbH U b ∈ BudgetedEntropies U b :=
    Nat.sSup_mem hne (bddAbove_budgetedEntropies U b)
  refine ⟨∏ i : Fin k, (Nat.card {x : Fin n // ℓ 0 x = i})!, ?_, ?_⟩
  · rw [hval]; exact card_orbit_mul_prod_fiber (ℓ 0)
  · have hbound := ledger_graded hn hcar.2
    have hb0 := hbud 0
    have hb1 := hbud 1
    omega

/-- **Table transport is composition with `U⁻¹`**: one step of `ownStep` against the world's own
table is exactly one step of the canonical family. Injectivity of `U` is what makes `idx` invert the
table (`idx_map_finRange`). -/
private theorem ownStep_lensTable (U : Perm (Fin n)) (ℓ : Fin n → Fin m) :
    ownStep (lensTable ⇑U) (lensTable ℓ) = lensTable (ℓ ∘ ⇑U⁻¹) := by
  have hfinj : Function.Injective (fun j : Fin n => ((U j : Fin n) : ℕ)) :=
    Fin.val_injective.comp U.injective
  have hlen : (lensTable ℓ).length = n := by simp [lensTable]
  have hfr : (List.finRange n).map Fin.val = List.range n := by simp
  rw [ownStep, hlen, ← hfr, List.map_map]
  refine List.map_congr_left fun i _ => ?_
  -- `idx i (lensTable ⇑U) = U⁻¹ i`: the table is an injective tabulation, so `idx` inverts it
  have hidx : idx (i : ℕ) (lensTable ⇑U) = ((U⁻¹ i : Fin n) : ℕ) := by
    have h := idx_map_finRange (fun j : Fin n => ((U j : Fin n) : ℕ)) hfinj (U⁻¹ i)
    simpa [lensTable] using h
  simp only [Function.comp_apply]
  rw [hidx, lensTable, getD_map_finRange]

/-- Iterated transport realizes the canonical family: `t` steps of `ownStep` against `U`'s table
turn `ℓ₀`'s table into frame `t`'s. -/
theorem ownIter_lensTable (U : Perm (Fin n)) (ℓ₀ : Fin n → Fin m) (t : ℕ) :
    ownIter (lensTable ⇑U) t (lensTable ℓ₀) = lensTable ((U ^ t) • ℓ₀) := by
  induction t with
  | zero => simp [ownIter]
  | succ t ih =>
    have hstep : ownIter (lensTable ⇑U) (t + 1) (lensTable ℓ₀)
        = ownStep (lensTable ⇑U) (ownIter (lensTable ⇑U) t (lensTable ℓ₀)) :=
      Function.iterate_succ_apply' _ _ _
    -- transport by `U⁻¹` IS the action of `U`, and `U * U ^ t = U ^ (t + 1)`
    have hcomp : ((U ^ t) • ℓ₀) ∘ ⇑U⁻¹ = (U ^ (t + 1)) • ℓ₀ := by
      rw [show ((U ^ t) • ℓ₀) ∘ ⇑U⁻¹ = U • ((U ^ t) • ℓ₀) from rfl, ← mul_smul,
        ← _root_.pow_succ']
    rw [hstep, ih, ownStep_lensTable, hcomp]

/-- **The owner's program, rebuilt from `⟨⟨ℓ₀'s table, U's table⟩, t⟩`** — ONE fixed function of a
single natural number, carrying no dependence on `n`, the world, or the reading: decode the two
tables, transport `t` times, re-encode. -/
def ownTableFn (a : ℕ) : ℕ :=
  Encodable.encode
    (ownIter ((Encodable.decode (α := List ℕ) a.unpair.1.unpair.2).getD [])
      a.unpair.2
      ((Encodable.decode (α := List ℕ) a.unpair.1.unpair.1).getD []))

private theorem primrec_ownStep : Primrec₂ ownStep := by
  have hg : Primrec₂ fun (q : List ℕ × List ℕ) (i : ℕ) => q.2.getD (idx i q.1) 0 :=
    ((Primrec.list_getD 0).comp (Primrec.snd.comp Primrec.fst)
      (primrec_idx.comp (Primrec.pair Primrec.snd (Primrec.fst.comp Primrec.fst)))).to₂
  exact (Primrec.list_map
    (Primrec.list_range.comp (Primrec.list_length.comp Primrec.snd)) hg).to₂

/-- `Nat.rec` on a constant motive is iteration. -/
private theorem natRec_iterate {α : Type*} (f : α → α) (x : α) : ∀ t : ℕ,
    (Nat.rec (motive := fun _ => α) x (fun _ IH => f IH) t) = f^[t] x
  | 0 => rfl
  | t + 1 => by
    rw [Function.iterate_succ_apply']
    exact congrArg f (natRec_iterate f x t)

private theorem primrec_ownIter :
    Primrec₂ fun (q : List ℕ × List ℕ) (t : ℕ) => ownIter q.1 t q.2 := by
  have hg : Primrec₂ fun (q : List ℕ × List ℕ) (p : ℕ × List ℕ) => ownStep q.1 p.2 :=
    (primrec_ownStep.comp (Primrec.fst.comp Primrec.fst)
      (Primrec.snd.comp Primrec.snd)).to₂
  exact (Primrec.nat_rec (f := fun q : List ℕ × List ℕ => q.2) Primrec.snd hg).of_eq
    fun q t => natRec_iterate (ownStep q.1) q.2 t

/-- **The owner's builder is primitive recursive.** Decoding is `Primrec.decode`, transport is a
`List.map` over `List.range` composed with the ledger's table inversion, and the iteration is
`Nat.rec`. -/
private theorem primrec_ownTableFn : Primrec ownTableFn := by
  have hLP : Primrec fun a : ℕ => a.unpair.1 := Primrec.fst.comp Primrec.unpair
  have hdecL : Primrec fun a : ℕ =>
      (Encodable.decode (α := List ℕ) a.unpair.1.unpair.1).getD [] :=
    Primrec.option_getD.comp
      (Primrec.decode.comp (Primrec.fst.comp (Primrec.unpair.comp hLP))) (Primrec.const [])
  have hdecP : Primrec fun a : ℕ =>
      (Encodable.decode (α := List ℕ) a.unpair.1.unpair.2).getD [] :=
    Primrec.option_getD.comp
      (Primrec.decode.comp (Primrec.snd.comp (Primrec.unpair.comp hLP))) (Primrec.const [])
  have hT : Primrec fun a : ℕ => a.unpair.2 := Primrec.snd.comp Primrec.unpair
  exact Primrec.encode.comp
    (primrec_ownIter.comp (Primrec.pair hdecP hdecL) hT)

private theorem partrec_ownTableFn : Nat.Partrec (fun a : ℕ => (ownTableFn a : ℕ)) :=
  _root_.Partrec.nat_iff.mp (Primrec.to_comp primrec_ownTableFn).partrec

/-- **The fixed iterate-compose builder code.** One program, independent of the world, the reading,
and `n` — the whole `c₀` of `ownership` below. -/
noncomputable def ownBuilder : Nat.Partrec.Code :=
  Classical.choose (Nat.Partrec.Code.exists_code.mp partrec_ownTableFn)

/-- The builder's evaluation law. -/
private theorem eval_ownBuilder (a : ℕ) :
    Nat.Partrec.Code.eval ownBuilder a = Part.some (ownTableFn a) := by
  have h := congrFun (Classical.choose_spec
    (Nat.Partrec.Code.exists_code.mp partrec_ownTableFn)) a
  simpa [ownBuilder] using h

/-- A lens table decodes back to itself. -/
theorem decode_lensCode (ℓ : Fin n → Fin m) :
    (Encodable.decode (α := List ℕ) (lensCode ℓ)).getD [] = lensTable ℓ := by
  rw [lensCode, Encodable.encodek]; rfl

/-- **The builder is correct**: on `⟨⟨ℓ₀'s table, U's table⟩, t⟩` it outputs frame `t`'s encoded
tabulation. -/
private theorem ownTableFn_eq (U : Perm (Fin n)) (ℓ₀ : Fin n → Fin m) (t : ℕ) :
    ownTableFn (Nat.pair (Nat.pair (lensCode ℓ₀) (lensCode ⇑U)) t)
      = lensCode ((U ^ t) • ℓ₀) := by
  rw [ownTableFn]
  simp only [Nat.unpair_pair, decode_lensCode]
  rw [ownIter_lensTable]
  rfl

/-- **The ownership construction**, after [Persistence] §8, Proposition 8.1. Given a code for the
reading's table and a code for the *world's* table, the canonical family `ℓ t = ℓ₀ ∘ (U ^ t)⁻¹` is
**owned** at `elen cℓ + elen cU + c₀`, with the absolute constant
`c₀ = elen ownBuilder + 30` — one fixed builder plus the assembly's opcodes, independent of the
world, the reading, and `n`.

The assembled program is `comp ownBuilder (pair (pair (comp cℓ zero) (comp cU zero)) id)`: on input
`t` it runs the two given codes to recover the tables, hands them to the builder together with `t`,
and the builder transports the reading `t` steps along the world.

The rent/own contrast is the reason to have this. A renter pays the collapse's floor at every frame,
forever. An owner pays `K (ℓ₀) + K (U)` **once** — and since `K (U) ≤ log₂ n ! + O (1)` for every
world whatsoever, owning is never the more expensive option. What makes it *cheap* is a cheap world:
`KE_lcgWorld_le` exhibits one where `elen cU` is `O (log n)`.

Note what is NOT claimed. This is the permutation-setting construction, not Proposition 8.1's own
statement, which is set in the cell-structured world over the recurrent core `Mem_∞` and carries the
transient `U ^ N`; that plumbing is deliberately not built here. And Proposition 8.1's per-frame
`O (log t)` does not appear above because `UniformBudget` does not charge for the clock —
`uniformBudget_frame_cost` is where that cost is recovered, and `CbHu_collapse` is where it is shown
not to help. The bound is in terms of the *given* codes' lengths, not `KE`; the two coincide when
the codes are `KE`-optimal, which is how `CbHu_ge_lcg` consumes it. -/
theorem ownership {U : Perm (Fin n)} {ℓ₀ : Fin n → Fin m} (cℓ cU : Nat.Partrec.Code)
    (hℓ : cℓ.eval 0 = Part.some (lensCode ℓ₀))
    (hU : cU.eval 0 = Part.some (lensCode ⇑U)) :
    UniformBudget (fun t => (U ^ t) • ℓ₀) (elen cℓ + elen cU + (elen ownBuilder + 30)) := by
  classical
  refine ⟨Nat.Partrec.Code.comp ownBuilder
    (Nat.Partrec.Code.pair
      (Nat.Partrec.Code.pair (Nat.Partrec.Code.comp cℓ Nat.Partrec.Code.zero)
        (Nat.Partrec.Code.comp cU Nat.Partrec.Code.zero))
      Nat.Partrec.Code.id), ?_, ?_⟩
  · have hz : elen Nat.Partrec.Code.zero = 3 := rfl
    have hid : elen Nat.Partrec.Code.id = 9 := rfl
    simp only [E_len_comp, E_len_pair, hz, hid]
    omega
  · intro t
    have hz : Nat.Partrec.Code.eval Nat.Partrec.Code.zero t = Part.some 0 := rfl
    have hcl : Nat.Partrec.Code.eval (Nat.Partrec.Code.comp cℓ Nat.Partrec.Code.zero) t
        = Part.some (lensCode ℓ₀) := (eval_comp_some hz).trans hℓ
    have hcu : Nat.Partrec.Code.eval (Nat.Partrec.Code.comp cU Nat.Partrec.Code.zero) t
        = Part.some (lensCode ⇑U) := (eval_comp_some hz).trans hU
    have hp1 : Nat.Partrec.Code.eval
        (Nat.Partrec.Code.pair (Nat.Partrec.Code.comp cℓ Nat.Partrec.Code.zero)
          (Nat.Partrec.Code.comp cU Nat.Partrec.Code.zero)) t
        = Part.some (Nat.pair (lensCode ℓ₀) (lensCode ⇑U)) := by
      change Nat.pair <$> _ <*> _ = _
      rw [hcl, hcu]; simp [Seq.seq]
    have hp2 : Nat.Partrec.Code.eval
        (Nat.Partrec.Code.pair
          (Nat.Partrec.Code.pair (Nat.Partrec.Code.comp cℓ Nat.Partrec.Code.zero)
            (Nat.Partrec.Code.comp cU Nat.Partrec.Code.zero))
          Nat.Partrec.Code.id) t
        = Part.some (Nat.pair (Nat.pair (lensCode ℓ₀) (lensCode ⇑U)) t) := by
      change Nat.pair <$> _ <*> _ = _
      rw [hp1, Nat.Partrec.Code.eval_id]; simp [Seq.seq]
    rw [eval_comp_some hp2, eval_ownBuilder, ownTableFn_eq]

/-! ## The multiplicative congruential world: cheap dynamics, exhibited

[Persistence] §8, Proposition 8.3 names the **(CD) cheap-dynamics** regime — `K (U|core)` of order
`b + log n` — and shows it is exactly where a world's readings admit cheap generation. §8's
discussion exhibits (CD) by *rotation*. Here is the other textbook example, and a more instructive
one: `x ↦ a · x mod m`, the division-remainder pseudo-random generator.

The point of the example is the gap between how a world *looks* and what it *costs*. The orbit of a
seed under `x ↦ a · x mod m` is the output of a pseudo-random generator: it passes for random at any
horizon short of the period, and an observer watching it sees no order at all. Yet the rule is two
numbers. `KE_lcgWorld_le` prices the whole world at `O (Nat.size a + Nat.size m)` bits — `O (log m)`
— with explicit absolute constants: however chaotic the *view*, the world is (CD), and every
[Persistence] §8 conclusion about kind worlds applies to it.

That is the honest form of "order appears from chaos" in this framework: nothing about the world
changes. What changes is whether an observer can afford the rule. -/

/-- **The multiplicative congruential world** `x ↦ a · x mod m` — the textbook division-remainder
pseudo-random generator — as a permutation of `Fin m`. Coprimality of `a` and `m` is what makes the
map injective, hence (on a finite type) bijective: `a · x ≡ a · y` cancels to `x ≡ y` exactly when
`a` is invertible mod `m`. -/
noncomputable def lcgWorld (a m : ℕ) (h : Nat.Coprime a m) : Perm (Fin m) :=
  Equiv.ofBijective
    (fun x : Fin m => ⟨a * (x : ℕ) % m, Nat.mod_lt _ ((Nat.zero_le _).trans_lt x.isLt)⟩)
    (Finite.injective_iff_bijective.mp (by
      intro x y hxy
      have h1 : a * (x : ℕ) % m = a * (y : ℕ) % m := congrArg Fin.val hxy
      have h3 : (x : ℕ) % m = (y : ℕ) % m := Nat.ModEq.cancel_left_of_coprime h.symm h1
      rw [Nat.mod_eq_of_lt x.isLt, Nat.mod_eq_of_lt y.isLt] at h3
      exact Fin.ext h3))

/-- The world's rule, read off: the state `x` steps to `a · x mod m`. -/
@[simp] private theorem lcgWorld_apply (a m : ℕ) (h : Nat.Coprime a m) (x : Fin m) :
    ((lcgWorld a m h x : Fin m) : ℕ) = a * (x : ℕ) % m := rfl

/-- **The world's table, rebuilt from the packed rule `⟨a, m⟩`** — ONE fixed function of a single
natural number, carrying no dependence on `a` or `m`: tabulate `i ↦ a · i mod m` over `List.range m`
by plain digit arithmetic. This is the `markBuilder` idiom, and the source of the `O (1)` in the
price below. -/
private def lcgTableFn (p : ℕ) : ℕ :=
  Encodable.encode ((List.range p.unpair.2).map fun i => p.unpair.1 * i % p.unpair.2)

/-- **The builder is primitive recursive.** The table is a `List.map` of one multiplication and one
remainder over `List.range m`. -/
private theorem primrec_lcgTableFn : Primrec lcgTableFn := by
  have hA : Primrec fun p : ℕ => p.unpair.1 := Primrec.fst.comp Primrec.unpair
  have hM : Primrec fun p : ℕ => p.unpair.2 := Primrec.snd.comp Primrec.unpair
  have hinner : Primrec₂ fun (p : ℕ) (i : ℕ) => p.unpair.1 * i % p.unpair.2 :=
    (Primrec.nat_mod.comp
      (Primrec.nat_mul.comp (hA.comp Primrec.fst) Primrec.snd)
      (hM.comp Primrec.fst)).to₂
  exact Primrec.encode.comp (Primrec.list_map (Primrec.list_range.comp hM) hinner)

/-- **The builder is correct**: on the packed rule `⟨a, m⟩` it outputs exactly the world's encoded
tabulation — the very number whose `KE` is the world's price. -/
private theorem lcgTableFn_eq (a m : ℕ) (h : Nat.Coprime a m) :
    lcgTableFn (Nat.pair a m) = lensCode ⇑(lcgWorld a m h) := by
  rw [lcgTableFn, lensCode, lensTable]
  simp only [Nat.unpair_pair]
  congr 1
  have hfr : (List.finRange m).map Fin.val = List.range m := by simp
  rw [← hfr, List.map_map]
  exact List.map_congr_left fun i _ => (lcgWorld_apply a m h i).symm

private theorem partrec_lcgTableFn : Nat.Partrec (fun p : ℕ => (lcgTableFn p : ℕ)) :=
  _root_.Partrec.nat_iff.mp (Primrec.to_comp primrec_lcgTableFn).partrec

/-- **The fixed congruential-world builder code.** One program, independent of `a` and `m`. -/
noncomputable def lcgBuilder : Nat.Partrec.Code :=
  Classical.choose (Nat.Partrec.Code.exists_code.mp partrec_lcgTableFn)

/-- The builder's evaluation law. -/
private theorem eval_lcgBuilder (p : ℕ) :
    Nat.Partrec.Code.eval lcgBuilder p = Part.some (lcgTableFn p) := by
  have h := congrFun (Classical.choose_spec
    (Nat.Partrec.Code.exists_code.mp partrec_lcgTableFn)) p
  simpa [lcgBuilder] using h

/-- **The congruential world is cheap** — an explicit `(CD)` witness ([Persistence] §8, Proposition
8.3's cheap-dynamics condition). The whole world `x ↦ a · x mod m` is described in
`2 · κ · (Nat.size a + Nat.size m) + O (1)` bits, with `κ = 15 + elen dbl` and the additive constant
`elen lcgBuilder + 3 · κ + 3` — both absolute, fixed once and for all, independent of `a` and `m`.
Since `Nat.size a` and `Nat.size m` are the bit-lengths, this is `O (log m)` for `a < m`.

Assembly: `comp lcgBuilder (bconst ⟨a, m⟩)`. The rule rides in a pair of numerals, `Nat.pair` costs
a constant factor (`size_pair_le`), `bconst` loads it in `O (Nat.size p)` rather than `Θ (p)`
(`elen_bconst_le`), and `invariance_general` charges the fixed builder once.

The contrast with [Persistence] §8's incompressible `n`-cycle is the whole content: *most* worlds
cost `Θ (n log n)` to describe (the counting argument of Proposition 8.3), and this one — whose
orbits are what a pseudo-random generator emits — costs `O (log m)`. Locally random, globally a
two-number rule. -/
theorem KE_lcgWorld_le (a m : ℕ) (h : Nat.Coprime a m) :
    KE (lensCode ⇑(lcgWorld a m h))
      ≤ 2 * (15 + elen dbl) * (Nat.size a + Nat.size m)
        + (elen lcgBuilder + 3 * (15 + elen dbl) + 3) := by
  have heval : Nat.Partrec.Code.eval lcgBuilder (Nat.pair a m)
      = Part.some (lensCode ⇑(lcgWorld a m h)) := by
    rw [eval_lcgBuilder, lcgTableFn_eq]
  have hinv := invariance_general lcgBuilder (Nat.pair a m) _ heval
  have hkey : (15 + elen dbl) * Nat.size (Nat.pair a m)
      ≤ 2 * (15 + elen dbl) * (Nat.size a + Nat.size m) + 2 * (15 + elen dbl) := by
    calc (15 + elen dbl) * Nat.size (Nat.pair a m)
        ≤ (15 + elen dbl) * (2 * (Nat.size a + Nat.size m) + 2) :=
          Nat.mul_le_mul_left _ (size_pair_le a m)
      _ = 2 * (15 + elen dbl) * (Nat.size a + Nat.size m) + 2 * (15 + elen dbl) := by ring
  calc KE (lensCode ⇑(lcgWorld a m h))
      ≤ elen lcgBuilder + (15 + elen dbl) * Nat.size (Nat.pair a m)
          + (3 + (15 + elen dbl)) := hinv
    _ ≤ elen lcgBuilder + (2 * (15 + elen dbl) * (Nat.size a + Nat.size m) + 2 * (15 + elen dbl))
          + (3 + (15 + elen dbl)) := Nat.add_le_add_right (Nat.add_le_add_left hkey _) _
    _ = 2 * (15 + elen dbl) * (Nat.size a + Nat.size m)
          + (elen lcgBuilder + 3 * (15 + elen dbl) + 3) := by ring

/-- **Ownership over a cheap world: every reading, affordable forever.** The showcase corollary —
`ownership` run over `lcgWorld`, with the world's price discharged by `KE_lcgWorld_le`.

Over the congruential world `x ↦ a · x mod m`, an owner holding `O (log m)` bits for the *rule* and
`KE (lensCode ℓ₀)` bits for its *reading* owns the whole family `ℓ t = ℓ₀ ∘ (U ^ t)⁻¹` — and its
uniform entropic capacity reaches `ℓ₀`'s full relabelling class, the entropy of the reference frame
in its entirety. The `O (1)` is `elen lcgBuilder + elen ownBuilder + 3 · κ + 33`, absolute.

Compare what a renter pays. `CbHu_collapse` says an owner is capped like everybody else at
`Θ (b)` — but here `b` is `KE (lensCode ℓ₀) + O (log m)`, so the *world* is nearly free and the
observer's whole budget goes on its reading. That is the (CD) regime's content, exhibited on the
textbook pseudo-random generator: the orbits look like noise at every horizon short of the period,
and the rule costs two numbers. -/
theorem CbHu_ge_lcg {a m : ℕ} (h : Nat.Coprime a m) {k : ℕ} {ℓ₀ : Fin m → Fin k}
    (hsurj : Function.Surjective ℓ₀) {b : ℕ}
    (hb : 2 * (15 + elen dbl) * (Nat.size a + Nat.size m) + KE (lensCode ℓ₀)
        + (elen lcgBuilder + elen ownBuilder + 3 * (15 + elen dbl) + 33) ≤ b) :
    Nat.card ↥(orbit (Perm (Fin m)) ℓ₀) ≤ CbHu (lcgWorld a m h) b := by
  -- the world's own code: the fixed builder loaded with the packed rule `⟨a, m⟩`
  have hcU : Nat.Partrec.Code.eval
      (Nat.Partrec.Code.comp lcgBuilder (bconst (Nat.pair a m))) 0
      = Part.some (lensCode ⇑(lcgWorld a m h)) := by
    rw [eval_comp_some (eval_bconst (Nat.pair a m) 0), eval_lcgBuilder, lcgTableFn_eq]
  have hown := ownership (U := lcgWorld a m h) (ℓ₀ := ℓ₀) (minCode (lensCode ℓ₀))
    (Nat.Partrec.Code.comp lcgBuilder (bconst (Nat.pair a m)))
    (minCode_computes (lensCode ℓ₀)) hcU
  -- the assembled owner fits the budget
  have hlen : elen (minCode (lensCode ℓ₀))
      + elen (Nat.Partrec.Code.comp lcgBuilder (bconst (Nat.pair a m)))
      + (elen ownBuilder + 30) ≤ b := by
    refine le_trans ?_ hb
    rw [E_len_comp, elen_minCode]
    have hbc : elen (bconst (Nat.pair a m))
        ≤ 2 * (15 + elen dbl) * (Nat.size a + Nat.size m) + 3 * (15 + elen dbl) := by
      refine le_trans (elen_bconst_le (Nat.pair a m)) ?_
      have hkey : (15 + elen dbl) * Nat.size (Nat.pair a m)
          ≤ 2 * (15 + elen dbl) * (Nat.size a + Nat.size m) + 2 * (15 + elen dbl) := by
        calc (15 + elen dbl) * Nat.size (Nat.pair a m)
            ≤ (15 + elen dbl) * (2 * (Nat.size a + Nat.size m) + 2) :=
              Nat.mul_le_mul_left _ (size_pair_le a m)
          _ = 2 * (15 + elen dbl) * (Nat.size a + Nat.size m) + 2 * (15 + elen dbl) := by ring
      omega
    omega
  have hmem : Nat.card ↥(orbit (Perm (Fin m)) ℓ₀)
      ∈ UniformBudgetedEntropies (lcgWorld a m h) b :=
    ⟨k, fun t => ((lcgWorld a m h) ^ t) • ℓ₀, permCarries_smul hsurj, hown.mono hlen, by simp⟩
  exact le_csSup (bddAbove_uniformBudgetedEntropies _ b) hmem

/-! ## Faithful self-reading is priced at the world's rule

A reading is **faithful** when its reference frame is bijective: the observer resolves every state
of the world, losing nothing. This section prices exactly that, in both directions, and finds the
world's own rule on both sides of the ledger.

**Owning** (`faithful_ownership`): a code for the world's table `⇑U` — and nothing else — buys the
faithful family `ℓ t = (U ^ t) • id` outright, at `elen cU + O (1)`. The identity frame needs no
description of its own: the world's table *is* a list of length `n`, so one fixed builder reads `n`
off it and tabulates `[0, …, n − 1]` for free. This is `ownership` at `ℓ₀ = id`, with the reading's
price collapsed to a constant.

**Extraction** (`faithful_rule_cost`): conversely, any faithful family owned at budget `b` *hands
back* the world's rule, `KE (lensCode ⇑U) ≤ 2 · b + O (1)`. The owner's own program, run at `0` and
at `1`, is a description of the two frames the ledger consumes; `ℓ 0` bijective makes `ℓ 1`
injective, so the ledger's table inversion (`invcomp`, `idx`) reads `U = ℓ₁⁻¹ ∘ ℓ₀` straight off
them. The factor two is the code appearing twice in the assembly, and it is inherent to this route:
no self-interpreter is chased to remove it.

Together the two bound the least faithful budget `b*` by
`(b* ≥) (KE (lensCode ⇑U) − O (1)) / 2` and `b* ≤ KE (lensCode ⇑U) + O (1)`, with **absolute**
constants — no `n`, no world, no reading. What a subsystem can faithfully read of its own world is
priced at the world's rule, to within a factor two.

`CbHu_attains_ceiling` is the capstone: where the rule is affordable, the uniform entropic capacity
is not merely large but *exactly* `n !` — the absolute ceiling of `CbHu_le_factorial`, attained. A
bijective frame has all-singleton fibres, so its relabelling class is the whole symmetric group.

Read against the collapse this is the entire rent/own story in one line. `CbHu_collapse` says an
owner is generically capped at `Θ (b)`, and `log₂ n !` is `Θ (n log n)` — so the worlds meeting the
ceiling here are exactly the exceptional ones, those whose rule is cheap enough to buy. The
congruential world above is one: `KE_lcgWorld_le` prices it at `O (log m)`, so it reads itself
faithfully, forever, out of a logarithmic budget.

Anchors: [Persistence] §5, Definition 5.5 (the uniform budget) and §6 (the ledger, read as the rent
side), over the ownership construction of §8, Proposition 8.1. Both directions are statements of
this development, not of any numbered result there; nothing in [Persistence] is claimed
machine-checked by their presence. -/

/-- The identity frame's table is `[0, …, n − 1]`: reading every state as itself tabulates the
range. -/
theorem lensCode_id : lensCode (id : Fin n → Fin n) = Encodable.encode (List.range n) := by
  rw [lensCode, lensTable]
  congr 1
  simp

/-- **The identity frame, rebuilt from the world's own table** — ONE fixed function of a single
natural number. A table for a world over `Fin n` is a list of length `n`, so its length is the only
input the identity frame's tabulation needs: decode, measure, and tabulate the range. This is why a
faithful reading costs nothing beyond the rule. -/
def idFromTableFn (a : ℕ) : ℕ :=
  Encodable.encode (List.range ((Encodable.decode (α := List ℕ) a).getD []).length)

/-- The rebuild is correct: from *any* frame's table over `Fin n` — the world's own included — it
recovers the identity frame's table. -/
private theorem idFromTableFn_eq (ℓ : Fin n → Fin m) :
    idFromTableFn (lensCode ℓ) = lensCode (id : Fin n → Fin n) := by
  rw [idFromTableFn, decode_lensCode, lensCode_id, lensTable]
  simp

private theorem primrec_idFromTableFn : Primrec idFromTableFn := by
  have hdec : Primrec fun a : ℕ => (Encodable.decode (α := List ℕ) a).getD [] :=
    Primrec.option_getD.comp Primrec.decode (Primrec.const [])
  exact Primrec.encode.comp (Primrec.list_range.comp (Primrec.list_length.comp hdec))

/-- **The faithful-family builder**: on `⟨the world's table, t⟩` it rebuilds the identity frame from
the world's table and transports it `t` steps along the world. One program, independent of the world
and of `n` — `ownTableFn`'s table transport with the reading supplied for free. -/
def faithTableFn (p : ℕ) : ℕ :=
  ownTableFn (Nat.pair (Nat.pair (idFromTableFn p.unpair.1) p.unpair.1) p.unpair.2)

private theorem primrec_faithTableFn : Primrec faithTableFn := by
  have hA : Primrec fun p : ℕ => p.unpair.1 := Primrec.fst.comp Primrec.unpair
  have hT : Primrec fun p : ℕ => p.unpair.2 := Primrec.snd.comp Primrec.unpair
  exact primrec_ownTableFn.comp
    (Primrec₂.natPair.comp
      (Primrec₂.natPair.comp (primrec_idFromTableFn.comp hA) hA) hT)

/-- **The builder is correct**: on `⟨U's table, t⟩` it outputs frame `t` of the faithful family —
the world's own inverse iterate `(U ^ t)⁻¹`, which is what transporting the identity frame `t` steps
*is*. -/
theorem faithTableFn_eq (U : Perm (Fin n)) (t : ℕ) :
    faithTableFn (Nat.pair (lensCode ⇑U) t) = lensCode ⇑((U ^ t)⁻¹) := by
  rw [faithTableFn]
  simp only [Nat.unpair_pair, idFromTableFn_eq]
  rw [ownTableFn_eq U (id : Fin n → Fin n) t]
  rfl

/-- **The faithful family carries a persistent model**, over every permutation world: read the state
`x` at time `t` as the state it came from, `(U ^ t)⁻¹ x`. The persistence identity is then immediate
— `(U ^ t)⁻¹ ((U ^ t) x) = x` — and the reference frame is the identity, which resolves every state.
This is `permCarries_smul` at `ℓ₀ = id`, spelled without the action (see the note on `arrowAction`
above). -/
private theorem permCarries_inv (U : Perm (Fin n)) : PermCarries U (fun t => ⇑((U ^ t)⁻¹)) := by
  refine ⟨?_, fun t x => ?_⟩ <;> simp [Function.surjective_id]

/-- The faithful family's reference frame is **bijective**: it is the identity. -/
private theorem bijective_faithful_frame (U : Perm (Fin n)) :
    Function.Bijective (⇑((U ^ 0)⁻¹) : Fin n → Fin n) := by
  simp

/-- **An owned family's carried entropy is affordable**: the `le_csSup` step of the uniform
capacity, isolated. Stated at a symbolic label count `k`, which is what keeps its `orbit` the
relabelling one. -/
theorem CbHu_ge_of_uniform {U : Perm (Fin n)} {k b : ℕ} {ℓ : ℕ → Fin n → Fin k}
    (hcar : PermCarries U ℓ) (hbud : UniformBudget ℓ b) :
    Nat.card ↥(orbit (Perm (Fin n)) (ℓ 0)) ≤ CbHu U b :=
  le_csSup (bddAbove_uniformBudgetedEntropies U b) ⟨k, ℓ, hcar, hbud, rfl⟩

private theorem partrec_faithTableFn : Nat.Partrec (fun p : ℕ => (faithTableFn p : ℕ)) :=
  _root_.Partrec.nat_iff.mp (Primrec.to_comp primrec_faithTableFn).partrec

/-- **The fixed faithful-family builder code.** One program, independent of everything. -/
noncomputable def faithBuilder : Nat.Partrec.Code :=
  Classical.choose (Nat.Partrec.Code.exists_code.mp partrec_faithTableFn)

/-- The builder's evaluation law. -/
private theorem eval_faithBuilder (p : ℕ) :
    Nat.Partrec.Code.eval faithBuilder p = Part.some (faithTableFn p) := by
  have h := congrFun (Classical.choose_spec
    (Nat.Partrec.Code.exists_code.mp partrec_faithTableFn)) p
  simpa [faithBuilder] using h

/-- **Owning a faithful reading costs the rule, and nothing else** (⇐). A code for the world's table
buys a family that carries a persistent model, reads the world *bijectively* — losing no state at
all — and is **owned**: one program of length `elen cU + O (1)` computes every frame. The additive
constant `elen faithBuilder + 21` is absolute — one fixed builder plus the assembly's opcodes,
independent of the world and of `n`.

The assembled program is `comp faithBuilder (pair (comp cU zero) id)`: on input `t` it runs `cU` to
recover the world's table, and hands the builder that table together with `t`. No description of the
*reading* appears anywhere, because none is needed — the identity frame is read off the world's
table's length (`idFromTableFn`).

This is the ownership construction at `ℓ₀ = id` ([Persistence] §8, Proposition 8.1's family in the
§7 permutation setting), and `faithful_rule_cost` is its converse. -/
theorem faithful_ownership {U : Perm (Fin n)} (cU : Nat.Partrec.Code)
    (hU : cU.eval 0 = Part.some (lensCode ⇑U)) :
    ∃ ℓ : ℕ → Fin n → Fin n, PermCarries U ℓ ∧ Function.Bijective (ℓ 0) ∧
      UniformBudget ℓ (elen cU + (elen faithBuilder + 21)) := by
  refine ⟨fun t => ⇑((U ^ t)⁻¹), permCarries_inv U, bijective_faithful_frame U, ?_⟩
  · refine ⟨Nat.Partrec.Code.comp faithBuilder
      (Nat.Partrec.Code.pair (Nat.Partrec.Code.comp cU Nat.Partrec.Code.zero)
        Nat.Partrec.Code.id), ?_, ?_⟩
    · have hz : elen Nat.Partrec.Code.zero = 3 := rfl
      have hid : elen Nat.Partrec.Code.id = 9 := rfl
      simp only [E_len_comp, E_len_pair, hz, hid]
      omega
    · intro t
      have hz : Nat.Partrec.Code.eval Nat.Partrec.Code.zero t = Part.some 0 := rfl
      have hcu : Nat.Partrec.Code.eval (Nat.Partrec.Code.comp cU Nat.Partrec.Code.zero) t
          = Part.some (lensCode ⇑U) := (eval_comp_some hz).trans hU
      have hp : Nat.Partrec.Code.eval
          (Nat.Partrec.Code.pair (Nat.Partrec.Code.comp cU Nat.Partrec.Code.zero)
            Nat.Partrec.Code.id) t
          = Part.some (Nat.pair (lensCode ⇑U) t) := by
        change Nat.pair <$> _ <*> _ = _
        rw [hcu, Nat.Partrec.Code.eval_id]; simp [Seq.seq]
      rw [eval_comp_some hp, eval_faithBuilder, faithTableFn_eq]

/-- **The ledger over a faithful frame**: the world's table is recovered from the family's first two
frames by the fixed invert-and-compose program — the same `invcomp` the general ledger runs on.

`ℓ 1 = ℓ 0 ∘ U⁻¹` (`permCarries_frame_one`) and `ℓ 0` bijective make `ℓ 1` injective, so `U i` is
the *unique* state `ℓ 1` reads as `ℓ 0` reads `i` — and `idx`, table inversion, finds it. -/
theorem invcomp_permFrames {U : Perm (Fin n)} {ℓ : ℕ → Fin n → Fin m}
    (hcar : PermCarries U ℓ) (hbij : Function.Bijective (ℓ 0)) :
    invcomp (Nat.pair (lensCode (ℓ 0)) (lensCode (ℓ 1))) = lensCode ⇑U := by
  set f₀ : Fin n → ℕ := fun i => ((ℓ 0 i : Fin m) : ℕ) with hf₀
  set f₁ : Fin n → ℕ := fun i => ((ℓ 1 i : Fin m) : ℕ) with hf₁
  have h1 : ℓ 1 = ℓ 0 ∘ ⇑U⁻¹ := permCarries_frame_one hcar.2
  have hinj₁ : Function.Injective f₁ := by
    rw [hf₁]
    intro i j hij
    have hv := Fin.val_injective hij
    rw [h1] at hv
    exact (Equiv.injective U⁻¹) (hbij.1 hv)
  simp only [invcomp, Nat.unpair_pair, lensCode, lensTable, Encodable.encodek, Option.getD_some,
    List.map_map, ← hf₀, ← hf₁]
  refine congrArg Encodable.encode (List.map_congr_left fun i _ => ?_)
  have hstep : f₁ (U i) = f₀ i := by
    have := hcar.2 1 i
    simp only [pow_one] at this
    simp only [hf₀, hf₁, this]
  change idx (f₀ i) ((List.finRange n).map f₁) = ((U i : Fin n) : ℕ)
  rw [← hstep]
  exact idx_map_finRange f₁ hinj₁ (U i)

/-- **A faithful reading hands back the rule** (⇒), the converse of `faithful_ownership`. Any
family that carries a persistent model, reads the world bijectively, and is owned at budget `b`
contains a description of the world itself: `KE (lensCode ⇑U) ≤ 2 · b + O (1)`, with the constant
`elen icode + 3 · κ + 12` absolute (`κ = 15 + elen dbl`).

The assembly is `comp icode (pair (comp c (bconst 0)) (comp c (bconst 1)))`: the owner's single
program `c`, run at the two clock values the ledger needs, feeds the fixed inverter. The **factor
two is the code written twice** — `c` appears at both `t = 0` and `t = 1` — and it is what makes the
characterization exact only to within a factor two. Nothing weaker is available on this route: the
two frames are separate inputs to the inverter, and only a self-interpreter could share the text.

This is the ledger of [Persistence] §6 read against the uniform budget of Definition 5.5: an owner
of a faithful reading does not merely pay the rule's price — it *stores* the rule. -/
theorem faithful_rule_cost {U : Perm (Fin n)} {ℓ : ℕ → Fin n → Fin m} {b : ℕ}
    (hcar : PermCarries U ℓ) (hbij : Function.Bijective (ℓ 0)) (hbud : UniformBudget ℓ b) :
    KE (lensCode ⇑U) ≤ 2 * b + (elen icode + 3 * (15 + elen dbl) + 12) := by
  obtain ⟨c, hlen, heval⟩ := hbud
  have h0 : Nat.Partrec.Code.eval (Nat.Partrec.Code.comp c (bconst 0)) 0
      = Part.some (lensCode (ℓ 0)) := (eval_comp_some (eval_bconst 0 0)).trans (heval 0)
  have h1 : Nat.Partrec.Code.eval (Nat.Partrec.Code.comp c (bconst 1)) 0
      = Part.some (lensCode (ℓ 1)) := (eval_comp_some (eval_bconst 1 0)).trans (heval 1)
  have hp : Nat.Partrec.Code.eval
      (Nat.Partrec.Code.pair (Nat.Partrec.Code.comp c (bconst 0))
        (Nat.Partrec.Code.comp c (bconst 1))) 0
      = Part.some (Nat.pair (lensCode (ℓ 0)) (lensCode (ℓ 1))) := by
    change Nat.pair <$> _ <*> _ = _
    rw [h0, h1]; simp [Seq.seq]
  have hcomp : Computes (Nat.Partrec.Code.comp icode
      (Nat.Partrec.Code.pair (Nat.Partrec.Code.comp c (bconst 0))
        (Nat.Partrec.Code.comp c (bconst 1)))) (lensCode ⇑U) := by
    change Nat.Partrec.Code.eval _ 0 = _
    rw [eval_comp_some hp, eval_icode, invcomp_permFrames hcar hbij]
  have hle := KE_le hcomp
  rw [E_len_comp, E_len_pair, E_len_comp, E_len_comp] at hle
  have hb0 : elen (bconst 0) ≤ 15 + elen dbl := by
    have := elen_bconst_le 0
    simpa using this
  have hb1 : elen (bconst 1) ≤ 2 * (15 + elen dbl) := by
    have := elen_bconst_le 1
    have hs : Nat.size 1 = 1 := rfl
    rw [hs] at this
    omega
  omega

/-- **Target B — the faithful extraction at coefficient one.** For a faithful family carried by a
*uniform* budget `b` (`faithful_rule_cost`'s own hypotheses), the world's table costs one budget —
`KE (lensCode ⇑U) ≤ b + O (log n)`, not `faithful_rule_cost`'s `2 * b`. The route is Target A
(`uniformBudget_pairLens_le`) feeding `ledger_graded_paired_faithful`: at a faithful reference frame
the coset term collapses (singleton fibres, `∏ fiber! = 1`), so nothing beyond
`ledger_graded_paired_faithful`'s own `Nat.size n` term survives. `faithful_rule_cost` stays beside
it, unsuperseded — its `2 * b` is the icode/invcomp route's own shadow, worth keeping for its
smaller, `n`-free constant. -/
theorem uniformBudget_faithful_rule_cost_le (hn : 0 < n) {U : Perm (Fin n)}
    {ℓ : ℕ → Fin n → Fin m} {b : ℕ} (hcar : PermCarries U ℓ) (hbij : Function.Bijective (ℓ 0))
    (hbud : UniformBudget ℓ b) :
    KE (lensCode ⇑U) ≤ b + (15 + elen dbl) * Nat.size n
      + (63 + 4 * (15 + elen dbl) + elen zipBuilder + pairedLedgerConst) := by
  have hA := uniformBudget_pairLens_le hbud
  have hB := ledger_graded_paired_faithful hn hcar hbij
  omega

/-- A **faithful** frame's fibres are singletons, so the fibre product of the orbit–stabilizer count
is `1`: a bijective reading has a trivial stabilizer. -/
theorem prod_fiber_bijective {ℓ : Fin n → Fin m} (h : Function.Bijective ℓ) :
    ∏ i : Fin m, (Nat.card {x : Fin n // ℓ x = i})! = 1 := by
  refine Finset.prod_eq_one fun i _ => ?_
  have hone : Nat.card {x : Fin n // ℓ x = i} = 1 := by
    obtain ⟨x, hx, huniq⟩ := h.existsUnique i
    exact Nat.card_eq_one_iff_exists.mpr ⟨⟨x, hx⟩, fun y => Subtype.ext (huniq y y.2)⟩
  rw [hone]
  rfl

/-- **Self-ownership attains the absolute ceiling** — a machine-checked *equality*. If the world's
own table is affordable at all — some code `cU` for `lensCode ⇑U` fitting inside `b` with the
faithful family's absolute constant to spare — then the uniform entropic capacity is **exactly**
`n !`, the ceiling of `CbHu_le_factorial`.

Both directions are needed and both are here: `CbHu_le_factorial` caps every reading at `n !`, and
`faithful_ownership` exhibits a family attaining it — bijective, so its fibres are singletons
(`prod_fiber_bijective`) and its relabelling class is all of `n !` by orbit–stabilizer
(`card_orbit_mul_prod_fiber`).

The reading of the equality is the point. `CbHu_collapse` prices a generic world's owner at
`Θ (b)`, and `log₂ n !` is `Θ (n log n)`: so a world at this ceiling is *exceptional*, and what
makes it exceptional is precisely that its rule is cheap. Everything a subsystem can faithfully read
of its own world is bought, in full, at the price of the world's rule and an absolute constant —
`faithful_rule_cost` is the converse showing nothing cheaper does it. The congruential world
`x ↦ a · x mod m` is the worked instance (`KE_lcgWorld_le`): `O (log m)` bits, every state resolved,
forever. -/
theorem CbHu_attains_ceiling {U : Perm (Fin n)} {b : ℕ} (cU : Nat.Partrec.Code)
    (hU : cU.eval 0 = Part.some (lensCode ⇑U))
    (hb : elen cU + (elen faithBuilder + 21) ≤ b) :
    CbHu U b = n ! := by
  refine le_antisymm (CbHu_le_factorial U b) ?_
  obtain ⟨ℓ, hcar, hbij, hbud⟩ := faithful_ownership (U := U) cU hU
  have hge := CbHu_ge_of_uniform hcar (hbud.mono hb)
  have hcard := card_orbit_mul_prod_fiber (ℓ 0)
  rw [prod_fiber_bijective hbij, Nat.mul_one] at hcard
  exact hcard ▸ hge

/-! ## Capacity out to a horizon

Every capacity above is unbounded-horizon: the persistence identity is demanded at every `t`, and
the budget prices every frame, forever. An observer with a finite life demands less. The objects
below index by a horizon `T` — carry the model, and pay for it, out to time `T` only — and they are
where the uniform (owned) and per-frame (rented) budgets can finally be compared *honestly*.

Why the horizon is the natural setting for that comparison. The exchange rate between the budgets is
`uniformBudget_frame_cost`: an owner's program run at `t` describes frame `t` at `b + O (log t)`.
Truncate at `T` and the clock is bounded — `O (log T)` — and the comparison is immediate
(`CbHu_upTo_le_CbH_upTo`). The horizon is not a technicality here; it is what the `log` is a
function of.

It is *not*, however, the only setting: `CbHu_le_CbH` at the end of this section gives the same
comparison with no horizon at all, at cost `O (log n !)`, because a carried family over a
permutation world repeats with the world's period. The two differ in what the constant depends on —
`T` there, `n` here — and neither is absolute.

What does *not* need a horizon is the collapse. `CbH_upTo_collapse` is `CbH_collapse` with the cap
unchanged, at every `T ≥ 1`, because the counting consumes frames `0` and `1` and nothing else
(`permCarries_frame_one`): the collapse is a horizon-1 statement already, and truncating the object
it speaks about cannot weaken it. A short-lived observer gets no discount for being short-lived.

Anchors: [Persistence] §5, Definition 5.4 and Definition 5.5, read out to a horizon; §7, Theorem 7.3
and Corollary 7.5(i) for the cap. The horizon-indexed objects are this development's; no numbered
result of [Persistence] is claimed machine-checked by their presence. -/

/-- **Carrying a model out to horizon `T`** ([Persistence] §7's `PermCarries`, truncated): the
reference frame still resolves the world (`ℓ 0` surjective), but the persistence identity is
demanded only for `t ≤ T`. Frames past the horizon are unconstrained — the observer is not asked to
outlive its own reading. -/
def PermCarriesUpTo (U : Perm (Fin n)) (ℓ : ℕ → Fin n → Fin m) (T : ℕ) : Prop :=
  Function.Surjective (ℓ 0) ∧ ∀ t ≤ T, ∀ x, ℓ t ((U ^ t) x) = ℓ 0 x

/-- An unbounded-horizon family satisfies every truncation of itself. -/
private theorem PermCarries.upTo {U : Perm (Fin n)} {ℓ : ℕ → Fin n → Fin m} (h : PermCarries U ℓ)
    (T : ℕ) : PermCarriesUpTo U ℓ T :=
  ⟨h.1, fun t _ x => h.2 t x⟩

/-- **The per-frame budget out to horizon `T`**: every frame up to `T` is affordable at `b`. -/
def PermBudgetUpTo (ℓ : ℕ → Fin n → Fin m) (b T : ℕ) : Prop := ∀ t ≤ T, KE (lensCode (ℓ t)) ≤ b

/-- **The uniform budget out to horizon `T`**: one program of length at most `b` computes every
frame's table up to `T`. What the program does past the horizon is not asked. -/
def UniformBudgetUpTo (ℓ : ℕ → Fin n → Fin m) (b T : ℕ) : Prop :=
  ∃ c : Nat.Partrec.Code, elen c ≤ b ∧ ∀ t ≤ T, c.eval t = Part.some (lensCode (ℓ t))

private theorem UniformBudget.upTo {ℓ : ℕ → Fin n → Fin m} {b : ℕ} (h : UniformBudget ℓ b) (T : ℕ) :
    UniformBudgetUpTo ℓ b T :=
  let ⟨c, hlen, heval⟩ := h
  ⟨c, hlen, fun t _ => heval t⟩

/-- **The ledger survives truncation**: at any horizon `T ≥ 1` the second frame is still determined
by the first and the world (`permCarries_frame_one`'s argument, which reads `t = 1` only). -/
theorem permCarriesUpTo_frame_one {U : Perm (Fin n)} {ℓ : ℕ → Fin n → Fin m} {T : ℕ}
    (h : PermCarriesUpTo U ℓ T) (hT : 1 ≤ T) : ℓ 1 = U • ℓ 0 := by
  funext x
  rw [smul_lens_apply]
  have := h.2 1 hT (U⁻¹ x)
  simpa using this

/-- The **carried entropies affordable at budget `b` out to horizon `T`** — `BudgetedEntropies`
with both conditions truncated. -/
def BudgetedEntropiesUpTo (U : Perm (Fin n)) (b T : ℕ) : Set ℕ :=
  {N : ℕ | ∃ k : ℕ, ∃ ℓ : ℕ → Fin n → Fin k, PermCarriesUpTo U ℓ T ∧ PermBudgetUpTo ℓ b T ∧
      N = Nat.card ↥(orbit (Perm (Fin n)) (ℓ 0))}

/-- **The entropic capacity out to horizon `T`** ([Persistence] §5, Definition 5.4 truncated): the
largest carried entropy of a reference frame whose family carries the model, and pays `b` per frame,
out to time `T`. -/
noncomputable def CbH_upTo (U : Perm (Fin n)) (b T : ℕ) : ℕ := sSup (BudgetedEntropiesUpTo U b T)

/-- The **owner's** carried entropies out to horizon `T`. -/
def UniformBudgetedEntropiesUpTo (U : Perm (Fin n)) (b T : ℕ) : Set ℕ :=
  {N : ℕ | ∃ k : ℕ, ∃ ℓ : ℕ → Fin n → Fin k, PermCarriesUpTo U ℓ T ∧ UniformBudgetUpTo ℓ b T ∧
      N = Nat.card ↥(orbit (Perm (Fin n)) (ℓ 0))}

/-- **The uniform entropic capacity out to horizon `T`** ([Persistence] §5, Definition 5.5
truncated): the capacity of an observer that owns its reading and needs it only until `T`. -/
noncomputable def CbHu_upTo (U : Perm (Fin n)) (b T : ℕ) : ℕ :=
  sSup (UniformBudgetedEntropiesUpTo U b T)

private theorem budgetedEntropiesUpTo_le {U : Perm (Fin n)} {b T N : ℕ}
    (h : N ∈ BudgetedEntropiesUpTo U b T) : N ≤ n ! := by
  obtain ⟨k, ℓ, -, -, rfl⟩ := h
  have hprod : 0 < ∏ i : Fin k, (Nat.card {x : Fin n // ℓ 0 x = i})! :=
    Finset.prod_pos fun i _ => Nat.factorial_pos _
  exact card_orbit_mul_prod_fiber (ℓ 0) ▸ Nat.le_mul_of_pos_right _ hprod

private theorem bddAbove_budgetedEntropiesUpTo (U : Perm (Fin n)) (b T : ℕ) :
    BddAbove (BudgetedEntropiesUpTo U b T) :=
  ⟨n !, fun _ h => budgetedEntropiesUpTo_le h⟩

private theorem uniformBudgetedEntropiesUpTo_le {U : Perm (Fin n)} {b T N : ℕ}
    (h : N ∈ UniformBudgetedEntropiesUpTo U b T) : N ≤ n ! := by
  obtain ⟨k, ℓ, -, -, rfl⟩ := h
  have hprod : 0 < ∏ i : Fin k, (Nat.card {x : Fin n // ℓ 0 x = i})! :=
    Finset.prod_pos fun i _ => Nat.factorial_pos _
  exact card_orbit_mul_prod_fiber (ℓ 0) ▸ Nat.le_mul_of_pos_right _ hprod

private theorem bddAbove_uniformBudgetedEntropiesUpTo (U : Perm (Fin n)) (b T : ℕ) :
    BddAbove (UniformBudgetedEntropiesUpTo U b T) :=
  ⟨n !, fun _ h => uniformBudgetedEntropiesUpTo_le h⟩

/-- **A longer horizon never helps**: `CbH_upTo` is antitone in `T`. A family carrying the model out
to `T₂` carries it out to every `T₁ ≤ T₂`, and pays for fewer frames doing so — more horizon is
strictly more constraint, never more capacity. -/
theorem CbH_upTo_antitone (U : Perm (Fin n)) (b : ℕ) {T₁ T₂ : ℕ} (h : T₁ ≤ T₂) :
    CbH_upTo U b T₂ ≤ CbH_upTo U b T₁ :=
  csSup_le_csSup' (bddAbove_budgetedEntropiesUpTo U b T₁) (by
    rintro N ⟨k, ℓ, hcar, hbud, rfl⟩
    exact ⟨k, ℓ, ⟨hcar.1, fun t ht => hcar.2 t (ht.trans h)⟩,
      fun t ht => hbud t (ht.trans h), rfl⟩)

/-- **The unbounded-horizon capacity is below every truncation** — the full object satisfies every
truncation of itself, so nothing is lost by asking less. -/
theorem CbH_le_CbH_upTo (U : Perm (Fin n)) (b T : ℕ) : CbH U b ≤ CbH_upTo U b T :=
  csSup_le_csSup' (bddAbove_budgetedEntropiesUpTo U b T) (by
    rintro N ⟨k, ℓ, hcar, hbud, rfl⟩
    exact ⟨k, ℓ, hcar.upTo T, fun t _ => hbud t, rfl⟩)

/-- **The collapse does not care about the horizon** ([Persistence] §7, Corollary 7.5(i)'s cap, out
to `T`). For every `d` and every horizon `T ≥ 1`, the worlds whose entropic capacity *out to `T`* at
budget `b` exceeds `2 * b + d + 2` number at most `n ! / 2 ^ d` — the **same** cap as
`CbH_collapse`, with nothing given away for the shorter life.

The reason is structural. The counting consumes frames `0` and `1` and no others: `ℓ 1` is
determined by `ℓ 0` and the world (`permCarriesUpTo_frame_one`), and the budget is read at those two
frames alone. So `CbH_collapse` was *already* a horizon-1 statement, and truncating the capacity
object it bounds cannot weaken it. An observer that only needs its reading until tomorrow pays the
same generic price as one that needs it forever. -/
theorem CbH_upTo_collapse (b d : ℕ) {T : ℕ} (hT : 1 ≤ T) :
    {U : Perm (Fin n) | 2 ^ (2 * b + d + 2) < CbH_upTo U b T}.ncard * 2 ^ d ≤ n ! := by
  refine le_trans (Nat.mul_le_mul_right _ (Set.ncard_le_ncard ?_ (Set.toFinite _)))
    (collapse_union d)
  intro U hU
  have hlt : 2 ^ (2 * b + d + 2) < CbH_upTo U b T := hU
  have hne : (BudgetedEntropiesUpTo U b T).Nonempty := by
    by_contra hcon
    rw [Set.not_nonempty_iff_eq_empty] at hcon
    rw [CbH_upTo, hcon, csSup_empty] at hlt
    exact absurd hlt (Nat.not_lt_zero _)
  obtain ⟨k, ℓ, hcar, hbud, hval⟩ : CbH_upTo U b T ∈ BudgetedEntropiesUpTo U b T :=
    Nat.sSup_mem hne (bddAbove_budgetedEntropiesUpTo U b T)
  refine ⟨k, ℓ 0, hcar.1, ?_⟩
  have h1 : ℓ 1 = U • ℓ 0 := permCarriesUpTo_frame_one hcar hT
  have hb0 := hbud 0 (Nat.zero_le _)
  have hb1 := hbud 1 hT
  rw [h1, show U • ℓ 0 = ℓ 0 ∘ ⇑U⁻¹ from rfl] at hb1
  calc 2 ^ (KE (lensCode (ℓ 0)) + KE (lensCode (ℓ 0 ∘ ⇑U⁻¹)) + d + 2)
      ≤ 2 ^ (2 * b + d + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
    _ < Nat.card ↥(orbit (Perm (Fin n)) (ℓ 0)) := hval ▸ hlt

/-- **The frame-cost reduction, out to a horizon**: an owner's program prices every frame it is
asked about at `b + O (log T)` — the clock is read at `t ≤ T`, so `Nat.size t ≤ Nat.size T` bounds
it uniformly over the frames in question. -/
theorem uniformBudgetUpTo_frame_cost {ℓ : ℕ → Fin n → Fin m} {b T : ℕ}
    (h : UniformBudgetUpTo ℓ b T) {t : ℕ} (ht : t ≤ T) :
    KE (lensCode (ℓ t)) ≤ b + (15 + elen dbl) * Nat.size T + (3 + (15 + elen dbl)) := by
  obtain ⟨c, hlen, heval⟩ := h
  have hinv := invariance_general c t (lensCode (ℓ t)) (heval t ht)
  have hsize : Nat.size t ≤ Nat.size T := Nat.size_le_size ht
  have hmul := Nat.mul_le_mul_left (15 + elen dbl) hsize
  omega

/-- **Owning buys at most the clock** — the true uniform-versus-per-frame comparison, and the reason
it must be horizon-indexed.

Out to horizon `T`, an owner at budget `b` carries no more entropy than a renter at
`b + O (log T)`: the owner's program, run at each `t ≤ T`, *is* a per-frame description, costing the
program plus the clock (`uniformBudgetUpTo_frame_cost`), and `t ≤ T` bounds the clock at
`κ · Nat.size T` with `κ = 15 + elen dbl` absolute.

What the horizon buys is a constant that does not grow with `n`. Dropping it entirely still leaves a
comparison — `CbHu_le_CbH`, at `O (log n !)`, over the frames' period — but no route gives an
**absolute** constant here. The statement that *is* absolute is the collapse (`CbHu_collapse`),
which needs only frames `0` and `1`, whose clocks are constants.

So the ledger of renting versus owning reads: owning is amortization worth exactly the clock, and
the clock is worth `O (log T)`. It buys no entropy the renter cannot have for `O (log T)` more
bits — and, generically, `CbH_upTo_collapse` caps them both at `Θ (b)` anyway. -/
theorem CbHu_upTo_le_CbH_upTo (U : Perm (Fin n)) (b T : ℕ) :
    CbHu_upTo U b T ≤ CbH_upTo U (b + (15 + elen dbl) * Nat.size T + (3 + (15 + elen dbl))) T :=
  csSup_le_csSup' (bddAbove_budgetedEntropiesUpTo U _ T) (by
    rintro N ⟨k, ℓ, hcar, hbud, rfl⟩
    exact ⟨k, ℓ, hcar, fun t ht => uniformBudgetUpTo_frame_cost hbud ht, rfl⟩)

/-! ### The horizon runs out: a family over a permutation world repeats

The clock is unbounded in `t`, but the *frames are not*. Over a permutation world the persistence
identity determines every frame from the reference one — `ℓ t = ℓ 0 ∘ (U ^ t)⁻¹` — so the family
inherits the world's own period, and only `orderOf U ≤ n !` distinct frames ever exist. The clock
therefore never has to count past the period: an owner's `O (log t)` is really `O (log orderOf U)`,
which is `O (log n !) = O (n log n)` at worst.

So the uniform-to-per-frame comparison *does* hold with no horizon at all
(`CbHu_le_CbH`) — the cost is a constant in `n`, not an absolute one. This is worth stating
precisely, because "unbounded in `t`" invites the stronger reading that no horizon-free comparison
exists; over these worlds one does. What is genuinely unavailable horizon-free is an **absolute**
constant, independent of `n`: `CbHu_upTo_le_CbH_upTo` pays `O (log T)` and `CbHu_le_CbH` pays
`O (log n !)`, and neither degenerates to `O (1)`. -/

/-- **Every frame is the reference frame, relabelled** — the persistence identity solved for `ℓ t`.
`U ^ t` is invertible, so `ℓ t ∘ U ^ t = ℓ 0` reads as `ℓ t = ℓ 0 ∘ (U ^ t)⁻¹`: over a permutation
world a family carrying a model has no freedom past its reference frame. -/
theorem permCarries_frame_eq {U : Perm (Fin n)} {ℓ : ℕ → Fin n → Fin m} (h : PermCarries U ℓ)
    (t : ℕ) : ℓ t = ℓ 0 ∘ ⇑((U ^ t)⁻¹) := by
  funext y
  have := h.2 t ((U ^ t)⁻¹ y)
  simpa using this

/-- **The family repeats with the world's period**: frame `t` is frame `t % orderOf U`. A carried
family over a permutation world takes only `orderOf U` distinct values, however long it runs. -/
theorem permCarries_frame_mod {U : Perm (Fin n)} {ℓ : ℕ → Fin n → Fin m} (h : PermCarries U ℓ)
    (t : ℕ) : ℓ (t % orderOf U) = ℓ t := by
  rw [permCarries_frame_eq h, permCarries_frame_eq h (t := t), pow_mod_orderOf]

/-- **Owning beats renting by at most the world's period** — the uniform-to-per-frame comparison,
horizon-free after all.

An owner at budget `b` carries no more entropy than a renter at `b + O (log n !)`, with **no horizon
anywhere**: the frames of a carried family repeat with the world's period (`permCarries_frame_mod`),
so the owner's program never needs its clock past `orderOf U ≤ n !`, and the `O (log t)` of
`uniformBudget_frame_cost` is really `O (log orderOf U)`.

The constant `κ · Nat.size (n !) + (3 + κ)` depends on `n` and on nothing else — not the world, not
the reading, not the family. That dependence is the whole difference between this and
`CbHu_upTo_le_CbH_upTo`, which pays `O (log T)` for a horizon `T` that may be far below the period.
What no route gives is an **absolute** constant: over an unbounded horizon the clock genuinely must
count to the period, and `log n !` is `Θ (n log n)`.

Set against `CbHu_collapse`, whose cap *is* absolute in exactly this sense, the shape of the
rent/own ledger is complete: owning never escapes the generic ceiling, and it never buys more than
the
clock. -/
theorem CbHu_le_CbH (U : Perm (Fin n)) (b : ℕ) :
    CbHu U b ≤ CbH U (b + (15 + elen dbl) * Nat.size (n !) + (3 + (15 + elen dbl))) := by
  refine csSup_le_csSup' (bddAbove_budgetedEntropies U _) ?_
  rintro N ⟨k, ℓ, hcar, hbud, rfl⟩
  refine ⟨k, ℓ, hcar, fun t => ?_, rfl⟩
  rw [← permCarries_frame_mod hcar t]
  have hc := uniformBudget_frame_cost hbud (t % orderOf U)
  have hpos : 0 < orderOf U := orderOf_pos U
  have hcard : orderOf U ≤ n ! := by
    have h := orderOf_le_card_univ (x := U)
    rwa [Fintype.card_perm, Fintype.card_fin] at h
  have hsize : Nat.size (t % orderOf U) ≤ Nat.size (n !) :=
    Nat.size_le_size (le_trans (Nat.le_of_lt (Nat.mod_lt _ hpos)) hcard)
  have hmul := Nat.mul_le_mul_left (15 + elen dbl) hsize
  omega

end Collapse

end PersistenceCapacity
