module

public import Nonautonomous.ReachabilityWidth
public import ALT.Persistence.Core


/-!
# The finite-world identification: the memory width is the component count
([Guests] §7 Proposition 7.18's boundary paragraph; [Persistence] §4, Proposition 4.1)

At a finite carrier `X` under the constant stage family — [Guests] Definition 7.1's own degenerate
case — the memory width of `ReachabilityWidth.lean` and the component count of
`Persistence/Core.lean`'s static-lens stratum are readings of the SAME quantity:
`width U (fun _ => Set.univ) t` equals `Nat.card (Quotient (ALT.orbitSetoid U))` at
every stage `t`. So [Persistence]'s L2 capacity, `log₂ #components(U)`, is `log₂` of [Guests]' width
at this degenerate case — a relation between COUNTS, kept apart deliberately from a relation between
capacities: no result below claims the width itself IS a capacity.

The identification is NOT that the merge quotient (`Nonautonomous.MergeQuot`) is the component
quotient (`ALT.orbitSetoid`'s quotient) — it is not, and the two-state swap
(`Bool`, `Bool.not`) is the guard witness: one component, two merge classes, since `Merges` asks
for eventual EQUALITY of iterates and the swap's iterates alternate forever.
What coincides is one level up: at a finite carrier the induced law `Nonautonomous.mergeLaw` is a
BIJECTION of the merge quotient (`mergeLaw_bijective`), so `Nonautonomous.Reaches` there is
symmetric (`reaches_symm`) — "lies on the same orbit of a permutation" — and its largest antichain
is a transversal of those orbits, one per orbit.
Each orbit of `mergeLaw` over the merge quotient corresponds to exactly one component of `U`'s own
transition graph over `X` (`reaches_mergeMk_iff_orbitRel`); a component whose cycle has length `L`
carries `L` merge classes, all folded into that one orbit — which is why the width, an ORBIT count,
is the smaller of the two quantities the merge quotient and the component quotient separately name.

## Main results

* `mergeLaw_bijective` — at a finite carrier, `mergeLaw U` is a bijection of the merge quotient:
  `mergeLaw_injective` (`GrowingCore`, no hypothesis) plus finiteness of a quotient of a finite
  type.
* `reaches_symm` — at a finite carrier, `Reaches U` is symmetric: every `mergeLaw`-orbit is a
  genuine cycle, with no tail, since the law is a bijection there.
* `merges_imp_orbitRel` — eventual merging already implies component-membership, with **no**
  finiteness hypothesis at all: two states that eventually agree lie in the same weakly-connected
  component of `U`'s own graph, whether or not that graph is finite.
* `reaches_mergeMk_iff_orbitRel` — the structural bridge, at a finite carrier: two states' merge
  classes are `Reaches`-related exactly when the states themselves lie in the same component of
  `U`'s transition graph.
* `memWidth_eq_nat_card_orbitSetoid` — **the identification**: at a finite carrier and every
  stage `t`, `width U (fun _ => Set.univ) t` equals `Nat.card (Quotient (orbitSetoid U))`, cast
  to `ℕ∞`.
* `exists_finiteWorld_component_ne_merge_card` — **the guard**: the two-state swap has exactly one
  component and exactly two merge classes, while the identification above still computes the same
  width, `1`, from the (smaller) component side — the merge quotient is not the component quotient,
  even at the case where their orbit counts coincide.

## Scope

The mathematics is elementary and none of it is new: that a finite bijection's orbits are cycles is
folklore, and "count the attractors" as a static-lens capacity is [Persistence] §4's own cited
framing.
What this module owns is the LINK between two of the corpus's own machine-checked objects at a
degenerate case — [Guests]' growing-branch invariant restricting to [Persistence]'s finite-branch
invariant — and nothing about the classical statistics of random mappings, which stays outside the
artifact.
-/


@[expose] public section

namespace ALT

open Nonautonomous

variable {X : Type*}

/-! ## The merge quotient is a permutation, at a finite carrier -/

/-- **At a finite carrier, `mergeLaw U` is a bijection of the merge quotient**: `mergeLaw_injective`
carries no hypothesis at all, and an injective self-map of a finite type is bijective. -/
theorem mergeLaw_bijective (U : X → X) [Finite X] : Function.Bijective (mergeLaw U) :=
  Finite.injective_iff_bijective.mp (mergeLaw_injective U)

/-- Every point of a finite injective self-map's orbit is periodic: two of its forward iterates
must coincide by finiteness (`Finite.exists_ne_map_eq_of_infinite`), and injectivity of the shared
prefix cancels it, leaving a genuine period. -/
private theorem exists_period_pos {α : Type*} [Finite α] {g : α → α} (hg : Function.Injective g)
    (a : α) : ∃ p, 0 < p ∧ g^[p] a = a := by
  classical
  obtain ⟨i, j, hij, he⟩ := Finite.exists_ne_map_eq_of_infinite (fun k : ℕ => g^[k] a)
  rcases Nat.lt_or_gt_of_ne hij with hlt | hlt
  · refine ⟨j - i, by omega, ?_⟩
    have h2 : g^[i] (g^[j - i] a) = g^[i] a := by
      rw [← Function.iterate_add_apply, Nat.add_sub_cancel' hlt.le]
      exact he.symm
    exact hg.iterate i h2
  · refine ⟨i - j, by omega, ?_⟩
    have h2 : g^[j] (g^[i - j] a) = g^[j] a := by
      rw [← Function.iterate_add_apply, Nat.add_sub_cancel' hlt.le]
      exact he
    exact hg.iterate j h2

/-- A period propagates to every one of its multiples: iterating the fixed point stays fixed. -/
private theorem iterate_period_mul {α : Type*} {g : α → α} {a : α} {p : ℕ} (hp : g^[p] a = a) :
    ∀ k, g^[p * k] a = a := fun k => by
  rw [Function.iterate_mul]; exact Function.iterate_fixed hp k

/-- **`Reaches` is symmetric at a finite carrier**: `mergeLaw U` is a permutation of the merge
quotient (`mergeLaw_bijective`), so its orbit through any class is a genuine cycle with no tail —
going forward all the way around a period brings a witness back. -/
theorem reaches_symm (U : X → X) [Finite X] {q q' : MergeQuot U} (h : Reaches U q q') :
    Reaches U q' q := by
  obtain ⟨j, hj⟩ := h
  obtain ⟨p, hp0, hp⟩ := exists_period_pos (mergeLaw_injective U) q
  refine ⟨p * j - j, ?_⟩
  have hge : j ≤ p * j := Nat.le_mul_of_pos_left j hp0
  have hpj : (mergeLaw U)^[p * j] q = q := iterate_period_mul hp j
  rw [← Nat.sub_add_cancel hge, Function.iterate_add_apply, hj] at hpj
  exact hpj

/-! ## The structural bridge: merge-quotient reachability is component-membership -/

/-- **Eventual merging already implies component-membership**, with no finiteness at all: two
states that eventually agree under some common number of steps are joined by a chain through that
common image, hence lie in the same weakly-connected component of `U`'s own graph. -/
theorem merges_imp_orbitRel {U : X → X} {s t : X} (h : Merges U s t) : orbitRel U s t := by
  obtain ⟨k, hk⟩ := h
  have h1 : orbitRel U s (U^[k] s) := orbitRel_iterate U s k
  have h2 : orbitRel U t (U^[k] t) := orbitRel_iterate U t k
  rw [hk] at h1
  exact Relation.EqvGen.trans _ _ _ h1 (Relation.EqvGen.symm _ _ h2)

/-- **Component-membership descends to merge-quotient reachability, at a finite carrier**: the
generating step of `orbitRel` is exactly `mergeLaw`'s own generating step under `mergeMk`
(`mergeLaw_mergeMk`), so the claim follows by induction over the generated equivalence, with
`reaches_symm` closing the one case that is neither reflexivity nor transitivity. -/
private theorem orbitRel_imp_reaches_mergeMk {U : X → X} [Finite X] {s t : X} (h : orbitRel U s t) :
    Reaches U (mergeMk U s) (mergeMk U t) := by
  induction h with
  | rel x y hxy => subst hxy; simpa using reaches_mergeMk_iterate U x 1
  | refl x => exact Reaches.refl U _
  | symm _ _ _ ih => exact reaches_symm U ih
  | trans _ _ _ _ _ ih₁ ih₂ => exact Reaches.trans ih₁ ih₂

/-- The converse leg, needing no finiteness: a `Reaches` witness on the merge classes is a common
image after some number of steps, hence an eventual merge that `merges_imp_orbitRel` already reads
as component-membership; chase back to `s` through `orbitRel_iterate`. -/
private theorem reaches_mergeMk_imp_orbitRel {U : X → X} {s t : X}
    (h : Reaches U (mergeMk U s) (mergeMk U t)) : orbitRel U s t := by
  obtain ⟨j, hj⟩ := h
  rw [mergeLaw_iterate_mergeMk] at hj
  exact Relation.EqvGen.trans _ _ _ (orbitRel_iterate U s j)
    (merges_imp_orbitRel (Quotient.exact hj))

/-- **The structural bridge**: at a finite carrier, two states' merge classes are `Reaches`-related
exactly when the states themselves lie in the same component of `U`'s own transition graph. -/
theorem reaches_mergeMk_iff_orbitRel (U : X → X) [Finite X] (s t : X) :
    Reaches U (mergeMk U s) (mergeMk U t) ↔ orbitRel U s t :=
  ⟨reaches_mergeMk_imp_orbitRel, orbitRel_imp_reaches_mergeMk⟩

/-! ## The identification -/

/-- **The identification** ([Guests] §7 Proposition 7.18's boundary paragraph made positive;
[Persistence] §4, Proposition 4.1, L2): at a finite carrier and the constant stage family —
Definition 7.1's own degenerate case — the memory width equals the component count, at every stage.
The two objects were never put beside each other before this module: `orbitSetoid` reads
`Persistence/Core.lean`'s own transition graph on `X`, and `width` reads `ReachabilityWidth.lean`'s
antichain width on the merge quotient — related here through `reaches_mergeMk_iff_orbitRel` and a
chosen transversal of each side's classes, never through the merge quotient BEING the component
quotient, which `exists_finiteWorld_component_ne_merge_card` below shows it is not. -/
theorem memWidth_eq_nat_card_orbitSetoid (U : X → X) [Finite X] (t : ℕ) :
    width U (fun _ => Set.univ) t = (Nat.card (Quotient (orbitSetoid U)) : ℕ∞) := by
  classical
  let reachSetoid : Setoid (MergeQuot U) :=
    { r := Reaches U, iseqv := ⟨Reaches.refl U, reaches_symm U, Reaches.trans⟩ }
  set Q : Set (MergeQuot U) := Set.range (Quotient.out (s := reachSetoid)) with hQ
  have hstage : mergeFiber U (fun _ => (Set.univ : Set X)) t = Set.univ := by
    change mergeMk U '' Set.univ = Set.univ
    rw [Set.image_univ]
    exact Set.range_eq_univ.mpr Quotient.mk_surjective
  have hanti : IsAntichain (Reaches U) Q := by
    rintro _ ⟨c1, rfl⟩ _ ⟨c2, rfl⟩ hne hreach
    apply hne
    have hrel : reachSetoid.r (Quotient.out c1) (Quotient.out c2) := hreach
    have hc : (Quotient.mk reachSetoid (Quotient.out c1) : Quotient reachSetoid) =
        Quotient.mk reachSetoid (Quotient.out c2) := Quotient.sound hrel
    rw [Quotient.out_eq, Quotient.out_eq] at hc
    exact congrArg (Quotient.out (s := reachSetoid)) hc
  have hcover : ∀ q ∈ mergeFiber U (fun _ => (Set.univ : Set X)) t, ∃ p ∈ Q, Reaches U p q := by
    intro q _
    refine ⟨Quotient.out (Quotient.mk reachSetoid q), ⟨_, rfl⟩, ?_⟩
    exact Quotient.exact (Quotient.out_eq (Quotient.mk reachSetoid q))
  have hwidth : width U (fun _ => Set.univ) t = Q.encard :=
    width_eq_encard_of_is_root_antichain (hstage ▸ Set.subset_univ Q) hanti hcover
  have hQinj : Function.Injective (Quotient.out (s := reachSetoid)) := by
    intro c1 c2 h
    have := congrArg (Quotient.mk reachSetoid) h
    rwa [Quotient.out_eq, Quotient.out_eq] at this
  have hQcard : Q.encard = (Nat.card (Quotient reachSetoid) : ℕ∞) := by
    rw [hQ, ← Set.image_univ, hQinj.encard_image, Set.encard_univ, ENat.card_eq_coe_natCard]
  have hbij : Function.Bijective
      (Quotient.map (mergeMk U) (fun a b h => (reaches_mergeMk_iff_orbitRel U a b).mpr h) :
        Quotient (orbitSetoid U) → Quotient reachSetoid) := by
    constructor
    · intro c1 c2
      induction c1 using Quotient.inductionOn with
      | _ a => induction c2 using Quotient.inductionOn with
        | _ b =>
          intro h
          have hr : Reaches U (mergeMk U a) (mergeMk U b) := Quotient.exact h
          exact Quotient.sound ((reaches_mergeMk_iff_orbitRel U a b).mp hr)
    · intro q
      obtain ⟨s, rfl⟩ := Quotient.exists_rep q
      obtain ⟨x, rfl⟩ := Quotient.exists_rep s
      exact ⟨Quotient.mk (orbitSetoid U) x, Quotient.map_mk _ _ x⟩
  have hcardEq : Nat.card (Quotient (orbitSetoid U)) = Nat.card (Quotient reachSetoid) :=
    Nat.card_congr (Equiv.ofBijective _ hbij)
  rw [hwidth, hQcard, hcardEq]

/-! ## Guard: the merge quotient is not the component quotient -/

/-- Every pair of `Bool`s is `orbitRel`-related under the swap: one step in either direction. -/
private theorem orbitRel_bool_not (s t : Bool) : orbitRel Bool.not s t := by
  cases s <;> cases t <;>
    first
      | exact Relation.EqvGen.refl _
      | exact orbitRel_step Bool.not _

/-- The two-state swap has exactly **one component**: `orbitRel_bool_not` relates every pair. -/
theorem card_orbitSetoid_bool_not : Nat.card (Quotient (orbitSetoid Bool.not)) = 1 := by
  have hsub : Subsingleton (Quotient (orbitSetoid Bool.not)) := by
    constructor
    intro a b
    induction a using Quotient.inductionOn with
    | _ s => induction b using Quotient.inductionOn with
      | _ t => exact Quotient.sound (orbitRel_bool_not s t)
  exact Nat.card_eq_one_iff_unique.mpr ⟨hsub, ⟨Quotient.mk _ true⟩⟩

/-- The two-state swap has exactly **two merge classes**: `Bool.not` is injective, so no two
distinct states ever merge — the same fact `ReachabilityWidth`'s own guard (a) uses inside its
proof, stated here for what it separates. -/
theorem card_mergeQuot_bool_not : Nat.card (MergeQuot Bool.not) = 2 := by
  have hinj : Function.Injective (mergeMk Bool.not) := mergeMk_injective_of_injective (by decide)
  have hbij : Function.Bijective (mergeMk Bool.not) := ⟨hinj, Quotient.mk_surjective⟩
  rw [← Nat.card_congr (Equiv.ofBijective _ hbij), Nat.card_eq_fintype_card, Fintype.card_bool]

/-- **The guard**: at the two-state swap, the component quotient and the merge quotient carry
DIFFERENT counts — one component against two merge classes — while the identification above
still computes the same width, `1`, from the component side; the merge quotient is not the
component quotient, even at the shared degenerate case where both determine the same width. -/
theorem exists_finiteWorld_component_ne_merge_card :
    ∃ (X : Type) (_ : Finite X) (U : X → X) (t : ℕ),
      Nat.card (Quotient (orbitSetoid U)) = 1 ∧
      Nat.card (MergeQuot U) = 2 ∧
      width U (fun _ => Set.univ) t = 1 := by
  refine ⟨Bool, inferInstance, Bool.not, 0, card_orbitSetoid_bool_not, card_mergeQuot_bool_not, ?_⟩
  rw [memWidth_eq_nat_card_orbitSetoid, card_orbitSetoid_bool_not]; rfl

end ALT

/-! ## Axiom audit

Every capstone above is `#print axioms`-clean on the standard triple, and the guards below make
that build-enforced. -/


/-- info: 'ALT.mergeLaw_bijective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.mergeLaw_bijective

/-- info: 'ALT.reaches_symm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.reaches_symm

/-- info: 'ALT.merges_imp_orbitRel' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.merges_imp_orbitRel

set_option linter.style.longLine false in
/-- info: 'ALT.reaches_mergeMk_iff_orbitRel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.reaches_mergeMk_iff_orbitRel

set_option linter.style.longLine false in
/-- info: 'ALT.memWidth_eq_nat_card_orbitSetoid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.memWidth_eq_nat_card_orbitSetoid

set_option linter.style.longLine false in
/-- info: 'ALT.exists_finiteWorld_component_ne_merge_card' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.exists_finiteWorld_component_ne_merge_card
