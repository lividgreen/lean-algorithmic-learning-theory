/-
Copyright (c) 2026 Mykola Palamarchuk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mykola Palamarchuk
-/
import ALT.GrowingCore
import ALT.GrowingCoreCrossing

-- Formal-check file, not Mathlib-destined: opt out of the house-style header linter.
set_option linter.style.header false

/-!
# The memory width: the antichain width of the retained profile
([Guests] §7 Theorem 7.7's boundary paragraph)

Theorem 7.7's certificate crosses the internalization threshold once the merge quotient's retained
profile carries "a full-binary flag of unbounded dimension" — a hypothesis stated, at paper level,
against a bare counter world: successor on the naturals has an unbounded retained profile too, and
its content is a clock, not a memory. This file turns that boundary paragraph into a theorem.

On the merge quotient (`GrowingCore.MergeQuot`) write `q` reaches `q'` when some number of
`mergeLaw` steps carries `q` to `q'`. The **memory width** at stage `t` is the largest antichain of
that relation inside the retained profile `mergeStage U Ω t` — the largest set of retained classes
no one of which is a later version of another.

## Main results

* `Reaches` — the reachability relation `mergeLaw` induces on the merge quotient.
* `reaches_mergeLaw` — `mergeLaw` is monotone for `Reaches`: the one further fact, beyond
  `GrowingCore`'s own stage-to-stage injection, that a growing carrier's law needs.
* `mergeLaw_iterate_mergeMk` / `reaches_mergeMk_iterate` — the iterate transport `mergeLaw`
  induces on classes, and its `Reaches` corollary: every consumer that computes `Reaches` along a
  representative's orbit factors through these two lines.
* `memWidth_le_encard_mergeStage` — the generic width-profile inequality, no antichain hypothesis
  consumed: every antichain witnessing the width is a subset of the retained profile.
* `memWidth_eq_encard_of_isRootAntichain` — the class-level root-antichain width lemma: given a
  subset of a stage that is already an antichain and which every stage class reaches, the width
  equals that subset's cardinality exactly — no injectivity of the update and no notion of
  "component" enters either half. `memWidth_eq_encard_of_rootSet` is its corollary at a *state*-
  level root set `R` (`Q := mergeMk U '' R`); `ExtremeTapWidth.lean`'s exact-width capstones
  instantiate the corollary at a concrete root set.
* `exists_isRootAntichain_of_finite` / `exists_isRootAntichain_of_finite_stage` — **a root
  antichain always exists at a finite stage** ([Guests] §7 Proposition 7.16's own boundary
  paragraph — "the proposition says nothing about when one exists or how to find it" — answered):
  descend the reachability preorder to its minimal elements and pick one representative per
  mutual-reachability class among them.
* `memWidth_eq_encard_canonical_of_antisymmOn` — the "how to find it" half, under an antisymmetry
  hypothesis: the root antichain is exactly the stage classes no OTHER stage class reaches, the
  form every growing instance the corpus carries actually sits at. Guard (a),
  `exists_canonicalSet_empty_pos_memWidth`, shows antisymmetry is load-bearing: at Definition 7.1's
  own degenerate case, the finite world, the canonical set is empty while the width is positive.
* `pos_memWidth_not_exists_isRootAntichain_intSucc` — **guard (b)**: the successor world on `ℤ`
  pins the finiteness hypothesis of `exists_isRootAntichain_of_finite` — a bi-infinite chain has a
  positive width but no root antichain at all, so finiteness is not decorative.
* `memWidth` — the memory width, `ℕ∞`-valued (`Set.encard`, not `Set.ncard`: an antichain inside an
  infinite retained profile can itself be infinite, and `ℕ`'s supremum of an unbounded set is
  silently `0`).
* `memWidth_mono` — **monotone**, with no hypothesis on the world beyond `Advances`: `mergeLaw`'s
  bare injectivity carries an antichain to an antichain of the same size one stage later.
* `memWidth_nat_succ_eq_one` — **the clock theorem**: the successor world's retained profile is a
  chain at any stage family, so its width is `1` throughout, at both a nested and a level
  stage schedule, while the profile itself is unbounded.
* `exists_conservationGuest_extent_gt_memWidth` — **the ceiling does not hold in general**: a
  conservation guest whose own stage extent is antichain-shaped under its own law can still exceed
  the memory width — a two-line counterexample at the nested clock, reported rather than forced.
* `memWidth_accreting_ge` — **the witness's lower bound**, unconditional in the environment: the
  accreting healer world's width is at least `2 ^ (t + 1)`.
* `memWidth_accreting_eq_of_trivialEnv` — **the witness's exact value** at a trivial environment,
  matching the certificate's own budget profile `κ = t + 1` exactly.
* `mergeStage_nat_succ_fastClock_encard` — **the guard family**: the fast counter's retained
  profile is in bijection with `Bool^t` at every stage — meeting the flag hypothesis read at set
  level — while its width is `1` throughout, making the structural (width) hypothesis load-bearing
  rather than decorative.
* `eventually_hosts_uniform_of_accreting_memWidth` — **the crossing, from the width**: at the
  trivial-environment witness the width's bit form is exactly the certificate's own budget profile
  (`memWidth_accreting_log_eq_of_trivialEnv`), so the crossing is a direct composition with the
  existing `AccretingWitness.eventually_hosts_uniform` — no new content.

## Scope

**Not a dichotomy — a separation**, and the module docstring says so where the certificate's own
prose claims exhaustiveness: the ceiling half (an antichain-shaped conservation guest's extent is
at most the memory width) is FALSE in general
(`exists_conservationGuest_extent_gt_memWidth`), so what is machine-checked is that unbounded width
gives the crossing (`memWidth_mono` is the general fact; the witness closes it in explicit closed
form) and that the retained profile's raw class count decides neither direction (the clock theorem
and the guard family). Recovering the certificate's stated exhaustiveness would need a hypothesis
beyond "antichain-shaped under its own law" — not supplied here.

`memWidth`'s value is a property of the *presented* world `(X, U, Ω)`, not of `(X, U)` alone: a
world presented by its own trajectory (singleton stages) has width `1` whatever it is, since there
is nothing co-present to store. This is not a defect — `mergeStage` already depends on `Ω`, and
every instance below presents a world by a genuine stage family rather than by its bare orbit.

The accreting healer world's exact width (`memWidth_accreting_eq_of_trivialEnv`) is stated at a
trivial environment (`Mem Empty Bool`, a one-element type): at a general environment the width can
exceed `2 ^ (t + 1)` when the environment law never merges distinct environment values, since two
states with identical habitat content but permanently-distinct environments never merge either — a
dependence already disclaimed for a general environment at [Guests] Theorem 7.5's own FV row. The
lower bound (`memWidth_accreting_ge`) needs no such restriction.

**Root sets.** `exists_isRootAntichain_of_finite`'s existence half and
`memWidth_eq_encard_canonical_of_antisymmOn`'s "how to find it" half are independent: the first
needs only finiteness of the stage, the second needs `Reaches` antisymmetric on the stage as well,
and neither hypothesis is dropped for free — guard (a) refutes the canonical description without
antisymmetry, guard (b) refutes existence itself without finiteness. The count a root antichain
supplies is of minimal *mutual-reachability classes*, not of minimal states or of minimal classes:
at a finite world (a constant stage family over a finite carrier, Definition 2.1's degenerate case
of Definition 7.1) `mergeLaw` is a bijection of the merge quotient, so every class is periodic and
none is canonical in the antisymmetric sense, which is exactly guard (a)'s content. No numbered
statement is claimed here: the order-theoretic content — a preorder generated by a function has
chain up-sets, and the maximum antichain of a finite such preorder is its minimal-class count — is
elementary and unattributed.
-/

namespace MemoryWidth

open GrowingCore GrowingWorld

variable {X : Type*}

/-! ## The reachability relation, and the memory width -/

/-- **The reachability relation** `mergeLaw` induces on the merge quotient: `q` reaches `q'` when
some number of `mergeLaw` steps carries `q` to `q'`. Reflexive (`reaches_refl`) and transitive
(`reaches_trans`), so a preorder. -/
def Reaches (U : X → X) (q q' : MergeQuot U) : Prop := ∃ j, (mergeLaw U)^[j] q = q'

/-- **`Reaches` is reflexive**: zero steps. -/
theorem reaches_refl (U : X → X) (q : MergeQuot U) : Reaches U q q := ⟨0, rfl⟩

/-- **`Reaches` is transitive**: sum the witnessing exponents. -/
theorem reaches_trans {U : X → X} {p q r : MergeQuot U} (h1 : Reaches U p q) (h2 : Reaches U q r) :
    Reaches U p r := by
  obtain ⟨i, hi⟩ := h1
  obtain ⟨j, hj⟩ := h2
  exact ⟨j + i, by rw [Function.iterate_add_apply, hi, hj]⟩

/-- **`mergeLaw` is monotone for reachability**: if `q` reaches `q'`, then `mergeLaw U q` reaches
`mergeLaw U q'` — `mergeLaw` commuting with its own iterates. The one further fact a growing
carrier's stage-to-stage law needs beyond `GrowingCore.mergeStage_injOn` and
`GrowingCore.advances_mergeStage`, and a fixed carrier does not: a bound on how much a stage's
retained classes can be *saved* by the growing law is NOT a further consequence of this fact alone
— it is false in general, at the widths this file's own witnesses compute. -/
theorem reaches_mergeLaw {U : X → X} {q q' : MergeQuot U} (h : Reaches U q q') :
    Reaches U (mergeLaw U q) (mergeLaw U q') := by
  obtain ⟨j, hj⟩ := h
  refine ⟨j, ?_⟩
  rw [← Function.iterate_succ_apply, Function.iterate_succ_apply', hj]

/-- **The memory width at stage `t`**: the extended-natural cardinality of the largest antichain of
`Reaches` inside the retained profile `mergeStage U Ω t`. Valued in `ℕ∞` (`Set.encard`) rather than
`ℕ`: an antichain inside an infinite retained profile can itself be infinite, and `ℕ`'s supremum of
an unbounded set is silently `0`, which would corrupt exactly the unbounded case the certificate
cares about. -/
noncomputable def memWidth (U : X → X) (Ω : ℕ → Set X) (t : ℕ) : ℕ∞ :=
  sSup (Set.encard '' {A : Set (MergeQuot U) | A ⊆ mergeStage U Ω t ∧ IsAntichain (Reaches U) A})

/-! ## Monotonicity: `mergeLaw`'s bare injectivity is the whole argument -/

/-- **Peeling one step**: if `mergeLaw U a` reaches `mergeLaw U b`, then `a` already reaches `b` —
`mergeLaw_injective` peeling the outer application off the witnessing iterate. The whole reason an
antichain's `mergeLaw`-image is again an antichain. -/
private theorem reaches_of_reaches_mergeLaw {U : X → X} {a b : MergeQuot U}
    (h : Reaches U (mergeLaw U a) (mergeLaw U b)) : Reaches U a b := by
  obtain ⟨j, hj⟩ := h
  refine ⟨j, mergeLaw_injective U ?_⟩
  calc mergeLaw U ((mergeLaw U)^[j] a) = (mergeLaw U)^[j + 1] a :=
        (Function.iterate_succ_apply' (mergeLaw U) j a).symm
    _ = (mergeLaw U)^[j] (mergeLaw U a) := Function.iterate_succ_apply (mergeLaw U) j a
    _ = mergeLaw U b := hj

/-- **`mergeLaw`'s image of an antichain is an antichain of the same size** (Finding 4): the
injective law never collapses distinct classes, and `reaches_of_reaches_mergeLaw` shows it never
manufactures a fresh comparability either. -/
private theorem isAntichain_image_mergeLaw {U : X → X} {A : Set (MergeQuot U)}
    (hA : IsAntichain (Reaches U) A) : IsAntichain (Reaches U) (mergeLaw U '' A) := by
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ hne hreach
  exact hA ha hb (fun hab => hne (hab ▸ rfl)) (reaches_of_reaches_mergeLaw hreach)

/-- **Monotone, with no hypothesis on the world beyond `Advances`** (Finding 4): the image of a
stage-`t` antichain under `mergeLaw` is a stage-`(t+1)` antichain of the same cardinality, so the
supremum only grows. This is the fact that makes the memory width a legal budget profile for
`AccretingWitness.eventually_hosts_uniform`. -/
theorem memWidth_mono {U : X → X} {Ω : ℕ → Set X} (hadv : Advances U Ω) :
    Monotone (memWidth U Ω) := by
  apply monotone_nat_of_le_succ
  intro t
  apply sSup_le
  rintro _ ⟨A, ⟨hAsub, hAanti⟩, rfl⟩
  have hsub : mergeLaw U '' A ⊆ mergeStage U Ω (t + 1) := by
    rintro _ ⟨a, ha, rfl⟩
    exact advances_mergeStage hadv t a (hAsub ha)
  have himg : (mergeLaw U '' A).encard = A.encard :=
    Function.Injective.encard_image (mergeLaw_injective U) A
  rw [← himg]
  exact le_sSup ⟨mergeLaw U '' A, ⟨hsub, isAntichain_image_mergeLaw hAanti⟩, rfl⟩

/-! ## A reusable fact: `mergeLaw` iterated is `mergeMk` of `U` iterated -/

/-- `mergeLaw`'s iterate along a class is the class of `U`'s iterate along a representative — the
handle every instance below computes `Reaches` through. Public: `DerivedStages.lean`'s antichain
argument destructs a `Reaches` witness through this identity directly. -/
theorem mergeLaw_iterate_mergeMk (U : X → X) (j : ℕ) (s : X) :
    (mergeLaw U)^[j] (mergeMk U s) = mergeMk U (U^[j] s) := by
  induction j with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, mergeLaw_mergeMk, Function.iterate_succ_apply']

/-- **`mergeMk` of an iterate is `Reaches`**: the one-line corollary `ExtremeTapWidth.lean`'s
antichain witness converts through. -/
theorem reaches_mergeMk_iterate (U : X → X) (s : X) (j : ℕ) :
    Reaches U (mergeMk U s) (mergeMk U (U^[j] s)) :=
  ⟨j, mergeLaw_iterate_mergeMk U j s⟩

/-- **The generic width-profile inequality**: every antichain witnessing the width is a subset of
the retained profile, so its cardinality never exceeds the profile's own — no antichain hypothesis
consumed, a pure profile fact. `DerivedStages.lean`'s grade-A bound is exactly this composed with a
bound on the profile itself. -/
theorem memWidth_le_encard_mergeStage (U : X → X) (Ω : ℕ → Set X) (t : ℕ) :
    memWidth U Ω t ≤ (mergeStage U Ω t).encard := by
  apply sSup_le
  rintro _ ⟨A, ⟨hAsub, -⟩, rfl⟩
  exact Set.encard_mono hAsub

/-- **The exact width at a class-level root antichain**: given `Q ⊆ mergeStage U Ω t` that is
already an antichain (`hanti`) and which every stage-`t` class reaches (`hcover`), the width is
exactly `Q`'s own cardinality. Neither half consumes injectivity of `U`, and no notion of
"component" is ever defined: `≥` is `le_sSup` at `Q` itself, and `≤` sends each element of a
competing antichain `A` to a chosen member of `Q` beneath it, an injective map on `A` because two
elements sharing the same chosen root would be `Reaches`-comparable to each other, contradicting
`A`'s own antichain property. `memWidth_eq_encard_of_rootSet` below is the corollary at
`Q := mergeMk U '' R` for a *state*-level root set `R`: the more general, class-level form is what
`exists_isRootAntichain_of_finite`'s existence argument actually produces, since its witness is not
handed to it as the image of a chosen set of states. -/
theorem memWidth_eq_encard_of_isRootAntichain {U : X → X} {Ω : ℕ → Set X} {t : ℕ}
    {Q : Set (MergeQuot U)} (hsub : Q ⊆ mergeStage U Ω t)
    (hanti : IsAntichain (Reaches U) Q)
    (hcover : ∀ q ∈ mergeStage U Ω t, ∃ p ∈ Q, Reaches U p q) :
    memWidth U Ω t = Q.encard := by
  classical
  apply le_antisymm
  · apply sSup_le
    rintro _ ⟨A, ⟨hAsub, hAanti⟩, rfl⟩
    set f : MergeQuot U → MergeQuot U := fun a =>
      if h : ∃ r ∈ Q, Reaches U r a then h.choose else a with hf_def
    have hex : ∀ {a : MergeQuot U}, a ∈ A → ∃ r ∈ Q, Reaches U r a := by
      intro a ha
      exact hcover a (hAsub ha)
    have hfR : ∀ a ∈ A, f a ∈ Q := by
      intro a ha
      rw [hf_def]
      simp only [dif_pos (hex ha)]
      exact (hex ha).choose_spec.1
    have hfReach : ∀ a ∈ A, Reaches U (f a) a := by
      intro a ha
      rw [hf_def]
      simp only [dif_pos (hex ha)]
      exact (hex ha).choose_spec.2
    have hfInj : Set.InjOn f A := by
      intro a ha b hb hab
      have hra := hfReach a ha
      rw [hab] at hra
      obtain ⟨i, hi⟩ := hra
      obtain ⟨j, hj⟩ := hfReach b hb
      rcases le_total i j with hij | hij
      · have e : (mergeLaw U)^[j - i] a = b := by
          rw [← hi, ← Function.iterate_add_apply, Nat.sub_add_cancel hij]
          exact hj
        by_contra hne
        exact hAanti ha hb hne ⟨j - i, e⟩
      · have e : (mergeLaw U)^[i - j] b = a := by
          rw [← hj, ← Function.iterate_add_apply, Nat.sub_add_cancel hij]
          exact hi
        by_contra hne
        exact hAanti hb ha (Ne.symm hne) ⟨i - j, e⟩
    calc A.encard = (f '' A).encard := hfInj.encard_image.symm
      _ ≤ Q.encard := Set.encard_mono (Set.image_subset_iff.mpr hfR)
  · exact le_sSup ⟨Q, ⟨hsub, hanti⟩, rfl⟩

/-- **The exact width at a root set**: given `R ⊆ Ω t` whose `mergeMk`-image is already an
antichain (`hanti`) and which every stage-`t` state reaches (`hcover`), the width is exactly that
image's cardinality. The corollary of `memWidth_eq_encard_of_isRootAntichain` at
`Q := mergeMk U '' R`. `ExtremeTapWidth.lean`'s exact-count capstones instantiate this at a
concrete root set. -/
theorem memWidth_eq_encard_of_rootSet {U : X → X} {Ω : ℕ → Set X} {t : ℕ} {R : Set X}
    (hsub : R ⊆ Ω t) (hanti : IsAntichain (Reaches U) (mergeMk U '' R))
    (hcover : ∀ s ∈ Ω t, ∃ r ∈ R, Reaches U (mergeMk U r) (mergeMk U s)) :
    memWidth U Ω t = (mergeMk U '' R).encard := by
  apply memWidth_eq_encard_of_isRootAntichain (Set.image_mono hsub) hanti
  rintro _ ⟨s, hs, rfl⟩
  obtain ⟨r, hr, hreach⟩ := hcover s hs
  exact ⟨mergeMk U r, ⟨r, hr, rfl⟩, hreach⟩

/-! ## Root sets: existence at a finite stage -/

/-- **A root antichain always exists at a finite stage**: a witness for
`memWidth_eq_encard_of_isRootAntichain`'s hypotheses, built by descending the reachability
preorder to its minimal elements and picking one representative per mutual-reachability class
among them. Distinct such representatives are incomparable: comparable-and-mutual puts them in one
class, comparable-and-not forces the target's own minimality to make it mutual after all — so no
two representatives of distinct classes can reach one another. -/
theorem exists_isRootAntichain_of_finite {U : X → X} {Ω : ℕ → Set X} {t : ℕ}
    (hfin : (mergeStage U Ω t).Finite) :
    ∃ Q ⊆ mergeStage U Ω t, IsAntichain (Reaches U) Q ∧
      ∀ q ∈ mergeStage U Ω t, ∃ p ∈ Q, Reaches U p q := by
  classical
  let : Preorder (MergeQuot U) :=
    { le := Reaches U, le_refl := reaches_refl U, le_trans := fun _ _ _ => reaches_trans }
  set S := mergeStage U Ω t with hS
  set M : Set (MergeQuot U) := {p | p ∈ S ∧ Minimal (· ∈ S) p} with hM
  let mutSetoid : Setoid (MergeQuot U) :=
    { r := fun p q => Reaches U p q ∧ Reaches U q p
      iseqv := ⟨fun p => ⟨reaches_refl U p, reaches_refl U p⟩,
        fun h => ⟨h.2, h.1⟩,
        fun h1 h2 => ⟨reaches_trans h1.1 h2.1, reaches_trans h2.2 h1.2⟩⟩ }
  let sM : Setoid ↥M := mutSetoid.comap (Subtype.val : ↥M → MergeQuot U)
  set Q : Set (MergeQuot U) := Set.range (fun c : Quotient sM => (Quotient.out c : ↥M).1) with hQ
  refine ⟨Q, ?_, ?_, ?_⟩
  · rintro _ ⟨c, rfl⟩
    exact (Quotient.out c : ↥M).2.1
  · rintro _ ⟨c1, rfl⟩ _ ⟨c2, rfl⟩ hne hreach
    apply hne
    have hp1 := (Quotient.out c1 : ↥M).2
    have hp2 := (Quotient.out c2 : ↥M).2
    have hmut : Reaches U (Quotient.out c2 : ↥M).1 (Quotient.out c1 : ↥M).1 :=
      hp2.2.le_of_le hp1.1 hreach
    have hrel : sM (Quotient.out c1 : ↥M) (Quotient.out c2 : ↥M) :=
      (Setoid.comap_rel _ _ _ _).mpr ⟨hreach, hmut⟩
    have hc : (Quotient.mk sM (Quotient.out c1 : ↥M) : Quotient sM) = Quotient.mk sM
        (Quotient.out c2 : ↥M) := Quotient.sound hrel
    rw [Quotient.out_eq, Quotient.out_eq] at hc
    exact congrArg (fun c : Quotient sM => (Quotient.out c : ↥M).1) hc
  · intro q hq
    obtain ⟨p, hple, hpmin⟩ := hfin.exists_le_minimal hq
    have hpM : p ∈ M := ⟨hpmin.1, hpmin⟩
    set c : Quotient sM := Quotient.mk sM (⟨p, hpM⟩ : ↥M) with hc_def
    have hrel : sM (Quotient.out c : ↥M) (⟨p, hpM⟩ : ↥M) := Quotient.exact (Quotient.out_eq c)
    have hreach : Reaches U (Quotient.out c : ↥M).1 p :=
      ((Setoid.comap_rel _ _ _ _).mp hrel).1
    exact ⟨(Quotient.out c : ↥M).1, ⟨c, rfl⟩, reaches_trans hreach hple⟩

/-- **The corollary at a finite state stage**: Definition 7.1's own finiteness clause is on `Ω t`,
not directly on `mergeStage U Ω t`, and `mergeStage` is `mergeMk U`'s image of it, so a root
antichain exists whenever the *state* stage is finite — the form the growing-world definition
actually supplies. -/
theorem exists_isRootAntichain_of_finite_stage {U : X → X} {Ω : ℕ → Set X} {t : ℕ}
    (hfin : (Ω t).Finite) :
    ∃ Q ⊆ mergeStage U Ω t, IsAntichain (Reaches U) Q ∧
      ∀ q ∈ mergeStage U Ω t, ∃ p ∈ Q, Reaches U p q :=
  exists_isRootAntichain_of_finite (hfin.image _)

/-! ## The canonical description, under antisymmetry -/

/-- **The canonical description, under antisymmetry**: at a finite stage where `Reaches` is
antisymmetric, the root antichain is exactly the stage classes no OTHER stage class reaches — the
"how to find it" half, and the form every growing instance the corpus carries actually sits at
(`ExtremeTapWidth.rootSet`; Definition 7.8's own remark is the case where `Reaches` happens to be
antisymmetric on the whole quotient). Antisymmetry is load-bearing, not cosmetic: guard (a) below
refutes this description at Definition 7.1's own degenerate case, the finite world, where the
canonical set is empty while the width is positive. -/
theorem memWidth_eq_encard_canonical_of_antisymmOn {U : X → X} {Ω : ℕ → Set X} {t : ℕ}
    (hfin : (mergeStage U Ω t).Finite)
    (hasymm : ∀ p ∈ mergeStage U Ω t, ∀ q ∈ mergeStage U Ω t,
        Reaches U p q → Reaches U q p → p = q) :
    memWidth U Ω t
      = {q ∈ mergeStage U Ω t |
          ∀ p ∈ mergeStage U Ω t, Reaches U p q → p = q}.encard := by
  classical
  let : Preorder (MergeQuot U) :=
    { le := Reaches U, le_refl := reaches_refl U, le_trans := fun _ _ _ => reaches_trans }
  set S := mergeStage U Ω t with hS
  set C : Set (MergeQuot U) := {q ∈ S | ∀ p ∈ S, Reaches U p q → p = q} with hC
  apply memWidth_eq_encard_of_isRootAntichain
  · exact fun q hq => hq.1
  · rintro p ⟨hpS, -⟩ q ⟨hqS, hq⟩ hne hpq
    exact hne (hq p hpS hpq)
  · intro q hq
    obtain ⟨p, hple, hpmin⟩ := hfin.exists_le_minimal hq
    refine ⟨p, ⟨hpmin.1, ?_⟩, hple⟩
    intro y hyS hyp
    exact hasymm y hyS p hpmin.1 hyp (hpmin.le_of_le hyS hyp)

/-! ## Guard families -/

/-- **Guard (a)**: the two-state swap pins `memWidth_eq_encard_canonical_of_antisymmOn`'s
antisymmetry hypothesis. `Bool.not` is injective, so `Merges` is equality and the merge quotient
over the constant stage has exactly the two classes `mergeMk true` and `mergeMk false`, each
reaching the other in one step (`Bool.not` swaps them) — so the canonical set is EMPTY while the
width is positive. This is the smallest witness for Definition 7.1's own degenerate case, the
finite world: there `mergeLaw` is an injective self-map of a finite quotient, hence a bijection,
hence every class is periodic, so the canonical set is always empty there. -/
theorem exists_canonicalSet_empty_pos_memWidth :
    ∃ (U : Bool → Bool) (Ω : ℕ → Set Bool) (t : ℕ),
      {q ∈ mergeStage U Ω t | ∀ p ∈ mergeStage U Ω t, Reaches U p q → p = q} = ∅ ∧
      (1 : ℕ∞) ≤ memWidth U Ω t := by
  classical
  refine ⟨Bool.not, fun _ => Set.univ, 0, ?_, ?_⟩
  · have hBoolInj : Function.Injective Bool.not := by decide
    rw [Set.eq_empty_iff_forall_notMem]
    rintro q ⟨-, hq⟩
    induction q using Quotient.inductionOn with
    | _ s =>
      cases s with
      | true =>
        have hreach : Reaches Bool.not (mergeMk Bool.not false) (mergeMk Bool.not true) :=
          ⟨1, by simp⟩
        have heq := hq (mergeMk Bool.not false) ⟨false, Set.mem_univ _, rfl⟩ hreach
        obtain ⟨k, hk⟩ := Quotient.exact heq
        exact absurd (hBoolInj.iterate k hk) (by decide)
      | false =>
        have hreach : Reaches Bool.not (mergeMk Bool.not true) (mergeMk Bool.not false) :=
          ⟨1, by simp⟩
        have heq := hq (mergeMk Bool.not true) ⟨true, Set.mem_univ _, rfl⟩ hreach
        obtain ⟨k, hk⟩ := Quotient.exact heq
        exact absurd (hBoolInj.iterate k hk) (by decide)
  · exact le_sSup ⟨{mergeMk Bool.not true}, ⟨by
      rintro _ rfl; exact ⟨true, Set.mem_univ _, rfl⟩, IsAntichain.singleton⟩,
      Set.encard_singleton _⟩

/-- **Guard (b)**: the successor world on `ℤ` pins `exists_isRootAntichain_of_finite`'s finiteness
hypothesis. `(· + 1)` is injective, so `Merges` is again equality and the retained profile is a
bi-infinite chain — the width is positive — yet NO root antichain exists at all: covering
`mergeMk 0` supplies some `p = mergeMk m ∈ Q`, and covering `mergeMk (m - 1)` supplies some
`p' ∈ Q` reaching it, hence also reaching `p` one step later; `p' ≠ p` (their witnessing integers
differ, since `p'`'s integer is `≤ m - 1` while `p`'s is `m`, so they cannot be the same class of
an injective-law quotient with `p' ≠ p`) contradicts `Q`'s own antichain property. So a stage can
carry a positive width and no root antichain at all — finiteness is not decorative. -/
theorem pos_memWidth_not_exists_isRootAntichain_intSucc :
    (1 : ℕ∞) ≤ memWidth (fun n : ℤ => n + 1) (fun _ => Set.univ) 0 ∧
    ¬ ∃ Q ⊆ mergeStage (fun n : ℤ => n + 1) (fun _ => Set.univ) 0,
        IsAntichain (Reaches (fun n : ℤ => n + 1)) Q ∧
        ∀ q ∈ mergeStage (fun n : ℤ => n + 1) (fun _ => Set.univ) 0,
          ∃ p ∈ Q, Reaches (fun n : ℤ => n + 1) p q := by
  set U : ℤ → ℤ := fun n => n + 1 with hUdef
  have hUinj : Function.Injective U := fun a b h => by simp only [hUdef] at h; omega
  have hiter : ∀ (j : ℕ) (x : ℤ), U^[j] x = x + (j : ℤ) := by
    intro j
    induction j with
    | zero => intro x; simp
    | succ n ih => intro x; rw [Function.iterate_succ_apply', ih]; simp [hUdef]; ring
  refine ⟨le_sSup ⟨{mergeMk U 0}, ⟨by
    rintro _ rfl; exact ⟨0, Set.mem_univ _, rfl⟩, IsAntichain.singleton⟩,
    Set.encard_singleton _⟩, ?_⟩
  rintro ⟨Q, hQsub, hQanti, hQcover⟩
  obtain ⟨p, hpQ, hpreach⟩ := hQcover (mergeMk U 0) ⟨0, Set.mem_univ _, rfl⟩
  obtain ⟨m, -, rfl⟩ := hQsub hpQ
  obtain ⟨p', hp'Q, hp'reach⟩ := hQcover (mergeMk U (m - 1)) ⟨m - 1, Set.mem_univ _, rfl⟩
  have hstep : Reaches U (mergeMk U (m - 1)) (mergeMk U m) := by
    have := reaches_mergeMk_iterate U (m - 1) 1
    rwa [show U^[1] (m - 1) = m from by rw [hiter]; push_cast; ring] at this
  have hp'p : Reaches U p' (mergeMk U m) := reaches_trans hp'reach hstep
  have hne : p' ≠ mergeMk U m := by
    rintro rfl
    obtain ⟨j, hj⟩ := hp'reach
    rw [mergeLaw_iterate_mergeMk] at hj
    have hval : U^[j] m = m - 1 := mergeMk_injective_of_injective hUinj hj
    rw [hiter] at hval
    omega
  exact hQanti hp'Q hpQ hne hp'p

/-! ## The clock theorem: a chain-shaped retained profile has width one -/

/-- **The successor world's retained profile is always a chain**, at any stage family
whatsoever: `Merges Nat.succ` is equality (`Nat.succ` is injective), so on the quotient `Reaches`
is total — `Nat.le_total` transported through `mergeLaw_iterate_mergeMk`. -/
private theorem isChain_mergeStage_nat_succ (Ω : ℕ → Set ℕ) (t : ℕ) :
    IsChain (Reaches Nat.succ) (mergeStage Nat.succ Ω t) := by
  rintro _ ⟨s, -, rfl⟩ _ ⟨s', -, rfl⟩ hne
  rcases le_total s s' with h | h
  · exact Or.inl ⟨s' - s, by
      rw [mergeLaw_iterate_mergeMk, Nat.succ_iterate, Nat.add_sub_cancel' h]⟩
  · exact Or.inr ⟨s - s', by
      rw [mergeLaw_iterate_mergeMk, Nat.succ_iterate, Nat.add_sub_cancel' h]⟩

/-- **The clock theorem, at any stage family** ([Guests] §7 Theorem 7.9(ii)): a chain-shaped
retained profile has width exactly `1`, provided a stage is ever admitted. Instantiated below at
both a nested and a level presentation of the same successor world. -/
theorem memWidth_nat_succ_eq_one {Ω : ℕ → Set ℕ} {t : ℕ} (hne : (Ω t).Nonempty) :
    memWidth Nat.succ Ω t = 1 := by
  obtain ⟨s, hs⟩ := hne
  have hle : memWidth Nat.succ Ω t ≤ 1 := by
    apply sSup_le
    rintro _ ⟨A, ⟨hAsub, hAanti⟩, rfl⟩
    exact Set.encard_le_one_iff_subsingleton.mpr
      (subsingleton_of_isChain_of_isAntichain
        (IsChain.mono hAsub (isChain_mergeStage_nat_succ Ω t)) hAanti)
  have hge : (1 : ℕ∞) ≤ memWidth Nat.succ Ω t :=
    le_sSup ⟨{mergeMk Nat.succ s}, ⟨by
      rintro _ rfl; exact ⟨s, hs, rfl⟩, IsAntichain.singleton⟩,
      Set.encard_singleton _⟩
  exact le_antisymm hle hge

/-- `mergeMk Nat.succ` is injective: `Merges Nat.succ` is equality, `Nat.succ` being injective. -/
private theorem mergeMk_nat_succ_injective : Function.Injective (mergeMk Nat.succ) := by
  intro a b hab
  obtain ⟨k, hk⟩ := Quotient.exact hab
  simpa [Nat.succ_iterate] using hk

/-- **The retained profile, counted**: at any stage family, the successor world's stage-`t`
retained profile has exactly as many classes as the stage itself admits states — `mergeMk` never
collapsing two of them. -/
private theorem mergeStage_nat_succ_encard (Ω : ℕ → Set ℕ) (t : ℕ) :
    (mergeStage Nat.succ Ω t).encard = (Ω t).encard :=
  Function.Injective.encard_image mergeMk_nat_succ_injective (Ω t)

/-- **The clock theorem, at a nested (level-set) stage schedule** ([Guests] §7 Theorem
7.9(ii)): `Ω t = {n | n ≤ t}` presents the successor world with an unbounded retained profile
(`t + 1` classes at stage `t`) whose width is nonetheless `1` throughout — unbounded retained
profile with width one, the slow clock. -/
theorem memWidth_nat_succ_slowClock (t : ℕ) :
    memWidth Nat.succ (fun t => Set.Iic t) t = 1 :=
  memWidth_nat_succ_eq_one ⟨0, Set.mem_Iic.mpr (Nat.zero_le t)⟩

theorem mergeStage_nat_succ_slowClock_encard (t : ℕ) :
    (mergeStage Nat.succ (fun t => Set.Iic t) t).encard = t + 1 := by
  rw [mergeStage_nat_succ_encard]
  simp [Set.Finite.encard_eq_coe_toFinset_card (Set.finite_Iic t), Nat.card_Iic]

/-- **The clock theorem, at a level (fast) stage schedule** ([Guests] §7 Theorem 7.9(ii)):
`Ω t = {n | n < 2 ^ t}` presents the SAME update at a faster admission rate — `2 ^ t` classes at
stage `t`, again with width `1`. This is the fast counter of [Guests] §7 Theorem 7.9(iii),
restated as
`memWidth`'s own computation rather than assumed: the retained profile is in bijection with
`Bool ^ t` (`mergeStage_nat_succ_fastClock_encard` below) — the certificate's flag hypothesis,
read at set level — while the width stays `1`, so that reading of the hypothesis does not suffice
for the crossing (`eventually_hosts_uniform_of_accreting_memWidth`'s route needs the width, not
the raw count). -/
theorem memWidth_nat_succ_fastClock (t : ℕ) :
    memWidth Nat.succ (fun t => {n | n < 2 ^ t}) t = 1 :=
  memWidth_nat_succ_eq_one ⟨0, pow_pos (show (0 : ℕ) < 2 by norm_num) t⟩

/-- **The guard family** ([Guests] §7 Theorem 7.9(iii)): the fast counter's retained profile meets
the flag hypothesis read at set level — in bijection with `Bool ^ t`, i.e. `2 ^ t` classes at
stage `t` — at every stage, while `memWidth_nat_succ_fastClock` shows its width is `1` throughout.
So "the retained profile is in bijection with a full-binary flag of unbounded dimension," read at
set level with no compatibility to the law demanded, does NOT suffice for the crossing: the
strengthened, structural (antichain-width) hypothesis is load-bearing, not decorative. -/
theorem mergeStage_nat_succ_fastClock_encard (t : ℕ) :
    (mergeStage Nat.succ (fun t => {n | n < 2 ^ t}) t).encard = 2 ^ t := by
  rw [mergeStage_nat_succ_encard]
  have hfin : ({n | n < 2 ^ t} : Set ℕ).Finite := Set.finite_Iio (2 ^ t)
  rw [Set.Finite.encard_eq_coe_toFinset_card hfin]
  simp

/-! ## The ceiling does not hold in general -/

/-- The trivial guest law for the counterexample below: identity on `Bool`, injective for free. -/
private def ceilingCounterF : Bool → Bool := id

/-- The counterexample reading: the parity of the elapsed time since a state was admitted. -/
private def ceilingCounterRead (t s : ℕ) : Bool := decide (Odd (t - s))

private theorem ceilingCounter_stagedSquare :
    GrowingWorld.StagedSquare Nat.succ ceilingCounterF ceilingCounterRead (fun t => Set.Iic t) := by
  intro t s _
  simp only [ceilingCounterF, ceilingCounterRead, id, Nat.succ_sub_succ]

private theorem ceilingCounter_guestStage_one :
    GrowingWorld.guestStage ceilingCounterRead (fun t => Set.Iic t) 1 = {true, false} := by
  apply Set.eq_of_subset_of_subset
  · rintro _ ⟨s, hs, rfl⟩
    have hs1 : s ≤ 1 := Set.mem_Iic.mp hs
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hs1 with rfl | rfl <;> simp [ceilingCounterRead]
  · rintro x hx
    rcases hx with rfl | rfl
    · exact ⟨0, Set.mem_Iic.mpr (by norm_num), by simp [ceilingCounterRead]⟩
    · exact ⟨1, Set.mem_Iic.mpr (by norm_num), by simp [ceilingCounterRead]⟩

/-- **The ceiling does not hold in general** ([Guests] §7 Theorem 7.9's boundary
paragraph): a conservation guest whose stage extent is antichain-shaped under its own law can still
exceed the memory width. At the nested successor world, `memWidth ≡ 1` throughout
(`memWidth_nat_succ_slowClock`) — a chain — yet the trivial guest law `id` makes EVERY subset of
its extent antichain-shaped (`id`'s own iterate never leaves a point), and the parity-reading
guest's stage-`1` extent is all of `Bool`, of cardinality `2`. So "the guest's extent is
antichain-shaped under its own law" is not by itself enough to bound it by `memWidth`: recovering
a ceiling needs a hypothesis beyond that one, not supplied here. -/
theorem exists_conservationGuest_extent_gt_memWidth :
    ∃ (F : Bool → Bool) (ℓ : ℕ → ℕ → Bool),
      Function.Injective F ∧
      GrowingWorld.StagedSquare Nat.succ F ℓ (fun t => Set.Iic t) ∧
      IsAntichain (fun a b => ∃ j, F^[j] a = b)
        (GrowingWorld.guestStage ℓ (fun t => Set.Iic t) 1) ∧
      memWidth Nat.succ (fun t => Set.Iic t) 1 <
        (GrowingWorld.guestStage ℓ (fun t => Set.Iic t) 1).encard :=
  ⟨ceilingCounterF, ceilingCounterRead, Function.injective_id, ceilingCounter_stagedSquare,
    fun a _ b _ hne ⟨j, hj⟩ => hne (by simpa [ceilingCounterF, Function.iterate_id] using hj), by
      rw [ceilingCounter_guestStage_one, memWidth_nat_succ_slowClock,
        Set.encard_pair (by decide)]
      decide⟩

/-! ## The witness theorem: the accreting healer world -/

open AccretingWitness Decoupling PersistenceCapacity RealizabilityCCC RealizabilityRecursor
open FFL.FirstOrder FFL.FirstOrder.Arithmetic

/-- A generic fact reusable elsewhere: the sup over subsets of a set that is ITSELF an antichain
is the set's own cardinality — no larger antichain can be found, and the set is a legal witness
for itself. -/
theorem memWidth_eq_encard_of_isAntichain {U : X → X} {Ω : ℕ → Set X} {t : ℕ}
    (h : IsAntichain (Reaches U) (mergeStage U Ω t)) :
    memWidth U Ω t = (mergeStage U Ω t).encard := by
  apply le_antisymm
  · apply sSup_le
    rintro _ ⟨A, ⟨hAsub, -⟩, rfl⟩
    exact Set.encard_mono hAsub
  · exact le_sSup ⟨mergeStage U Ω t, ⟨Set.Subset.rfl, h⟩, rfl⟩

/-- The habitat's block-list lengthens by exactly one at every accreting step. -/
private theorem accUpdate_length {ι_J : Type*} (k : ℕ) (π : Mem ι_J Bool → Mem ι_J Bool)
    (s : List (Mem (Fin (3 ^ k)) Bool) × Mem ι_J Bool) :
    (accUpdate k π s).1.length = s.1.length + 1 := by
  simp [accUpdate]

/-- Iterated: `n` accreting steps lengthen the habitat by exactly `n`. -/
private theorem accUpdate_iterate_length {ι_J : Type*} (k : ℕ) (π : Mem ι_J Bool → Mem ι_J Bool)
    (s : List (Mem (Fin (3 ^ k)) Bool) × Mem ι_J Bool) (n : ℕ) :
    ((accUpdate k π)^[n] s).1.length = s.1.length + n := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [Function.iterate_succ_apply', accUpdate_length, ih]
    omega

/-- **The retained profile is unconditionally an antichain at the accreting witness**: the
habitat's own length strictly advances at every step, so two DISTINCT classes admitted at the
SAME stage `t` (the same block-list length `t + 1`) can never be `Reaches`-related — reaching in
`j` steps would force the length to shift by `j`, so same-stage `Reaches` forces `j = 0`. -/
theorem mergeStage_accUpdate_isAntichain {ι_J : Type*} (k t : ℕ)
    (π : Mem ι_J Bool → Mem ι_J Bool) :
    IsAntichain (Reaches (accUpdate k π)) (mergeStage (accUpdate k π) (accStage k) t) := by
  rintro _ ⟨s1, hs1, rfl⟩ _ ⟨s2, hs2, rfl⟩ hne ⟨j, hj⟩
  rw [mergeLaw_iterate_mergeMk] at hj
  obtain ⟨m, hm⟩ := Quotient.exact hj
  have hcomb : (accUpdate k π)^[m + j] s1 = (accUpdate k π)^[m] s2 := by
    rw [Function.iterate_add_apply]; exact hm
  have hlen := congrArg (fun s => s.1.length) hcomb
  simp only [accUpdate_iterate_length] at hlen
  have hs1' : s1.1.length = t + 1 := hs1
  have hs2' : s2.1.length = t + 1 := hs2
  have hj0 : j = 0 := by omega
  subst hj0
  simp only [add_zero] at hcomb
  exact hne (Quotient.sound ⟨m, hcomb⟩)

/-- The witness's extent, in `ℕ∞`: a cast of `AccretingWitness.ncard_guestStage_accRead`. -/
private theorem encard_guestStage_accRead (ι_J : Type*) (k t : ℕ) :
    (GrowingWorld.guestStage (accRead (ι_J := ι_J) k) (accStage k) t).encard = 2 ^ (t + 1) := by
  have hn := ncard_guestStage_accRead ι_J k t
  have hfin := Set.finite_of_ncard_ne_zero (s :=
    GrowingWorld.guestStage (accRead (ι_J := ι_J) k) (accStage k) t) (by rw [hn]; positivity)
  have hcast := Set.Finite.cast_ncard_eq hfin
  rw [hn] at hcast
  exact_mod_cast hcast.symm

/-- **The witness's lower bound, unconditional in the environment** ([Guests] §7 Theorem
7.9(iv), where `accStage k t` admits every length-`(t + 1)` habitat): the decoded-word
reading already
injects into the merge classes at stage `t` (`GrowingCore.exists_mergeMk_injective`), giving at
least `2 ^ (t + 1)` of them, at every depth `k`, environment law `π` and environment type. -/
theorem memWidth_accreting_ge {ι_J : Type*} (k t : ℕ) (π : Mem ι_J Bool → Mem ι_J Bool) :
    (2 : ℕ∞) ^ (t + 1) ≤ memWidth (accUpdate k π) (accStage k) t := by
  rw [memWidth_eq_encard_of_isAntichain (mergeStage_accUpdate_isAntichain k t π)]
  obtain ⟨g, hgmem, hginj⟩ :=
    exists_mergeMk_injective accLaw_injective (advances_accUpdate k π) (stagedSquare_accRead k π) t
  have hle : (GrowingWorld.guestStage (accRead (ι_J := ι_J) k) (accStage k) t).encard ≤
      (mergeStage (accUpdate k π) (accStage k) t).encard :=
    Function.Embedding.encard_le ⟨fun m => ⟨g m, hgmem m⟩, fun m1 m2 heq =>
      hginj (by simpa using congrArg Subtype.val heq)⟩
  rw [← encard_guestStage_accRead ι_J k t]
  exact hle

/-- **The witness's exact value, at a trivial environment** ([Guests] §7 Theorem 7.9(iv), stated
at a trivial environment for the reason this module's own boundary note gives): two habitats
with the same decoded word heal, in one step, to the
identical state — `healWorld k x = encRec k (decRec k x)` by `healWorld`'s own definition, so the
healed block depends only on the decode — and at a trivial environment (`Mem Empty Bool`, a
one-element type) the environment component always agrees too, so the two habitats merge outright.
So the retained profile is, at this instance, exactly as large as the decoded-word extent: no
larger than `2 ^ (t + 1)` either, matching `memWidth_accreting_ge`'s lower bound with equality —
recovering the certificate's own budget profile `κ = t + 1` on the nose. A general environment can
exceed this (the module boundary note records why), so the restriction is load-bearing, not
cosmetic. -/
theorem memWidth_accreting_eq_of_trivialEnv (k t : ℕ) (π : Mem Empty Bool → Mem Empty Bool) :
    memWidth (accUpdate k π) (accStage k) t = 2 ^ (t + 1) := by
  refine le_antisymm ?_ (memWidth_accreting_ge k t π)
  rw [memWidth_eq_encard_of_isAntichain (mergeStage_accUpdate_isAntichain k t π),
    ← encard_guestStage_accRead Empty k t]
  classical
  choose s hsmem hseq using fun q : ↥(mergeStage (accUpdate k π) (accStage k) t) => q.2
  refine Function.Embedding.encard_le ⟨fun q =>
    (⟨accRead k t (s q), s q, hsmem q, rfl⟩ :
      ↥(GrowingWorld.guestStage (accRead (ι_J := Empty) k) (accStage k) t)), ?_⟩
  rintro q1 q2 heq
  have hread : accRead k t (s q1) = accRead k t (s q2) := congrArg Subtype.val heq
  have hheal : (s q1).1.map (healWorld k) = (s q2).1.map (healWorld k) := by
    have e1 : (s q1).1.map (healWorld k) = (accRead k t (s q1)).map (encRec k) := by
      simp [accRead, healWorld, List.map_map, Function.comp]
    have e2 : (s q2).1.map (healWorld k) = (accRead k t (s q2)).map (encRec k) := by
      simp [accRead, healWorld, List.map_map, Function.comp]
    rw [e1, e2, hread]
  have henv : (s q1).2 = (s q2).2 := Subsingleton.elim _ _
  have hstep : accUpdate k π (s q1) = accUpdate k π (s q2) := by
    simp only [accUpdate]; rw [hheal, henv]
  have hmerge : Merges (accUpdate k π) (s q1) (s q2) := ⟨1, by simpa using hstep⟩
  exact Subtype.ext (by rw [← hseq q1, ← hseq q2]; exact Quotient.sound hmerge)

/-! ## The crossing, from the width -/

/-- **The identification**: at the trivial-environment witness, the memory width's bit form —
`Nat.log 2` of the width — is EXACTLY the certificate's own budget profile `κ = t + 1`. -/
theorem memWidth_accreting_log_eq_of_trivialEnv (k t : ℕ) (π : Mem Empty Bool → Mem Empty Bool) :
    Nat.log 2 (memWidth (accUpdate k π) (accStage k) t).toNat = t + 1 := by
  rw [memWidth_accreting_eq_of_trivialEnv]
  have h2 : ((2 : ℕ∞) ^ (t + 1)).toNat = 2 ^ (t + 1) := by
    rw [show ((2 : ℕ∞) = ((2 : ℕ) : ℕ∞)) from rfl, ← Nat.cast_pow, ENat.toNat_natCast]
  rw [h2]
  exact Nat.log_pow (by norm_num) (t + 1)

/-- **The crossing, from the width, at the trivial-environment witness** ([Guests] §7 Theorem
7.9(v)): the budget profile is the memory width's OWN bit form —
`memWidth_accreting_log_eq_of_trivialEnv` identifies it with `t + 1`, from which monotonicity and
unboundedness are trivial nat facts — and the crossing itself is a direct composition of
`AccretingWitness.eventually_hosts_uniform` at that profile: no further argument beyond the
identification. This is the sufficiency half of the certificate — see the module boundary note for
the ceiling half this does NOT recover. -/
theorem eventually_hosts_uniform_of_accreting_memWidth (k : ℕ)
    (π : Mem Empty Bool → Mem Empty Bool) :
    ∃ gTS, (∃ t₀, ∀ t, t₀ ≤ t → CategoricalThreshold.hostsAt
        (Nat.log 2 (memWidth (accUpdate k π) (accStage k) t).toNat) gTS) ∧
      ∀ t Mchk, CategoricalThreshold.hostsAt
          (Nat.log 2 (memWidth (accUpdate k π) (accStage k) t).toNat) gTS →
        gTS < Mchk → Mchk ≤ gTS ^ 2 →
        ∃ R : ReflectiveAsm gTS, R.depth = Mchk ∧
          CapacityLayer.FitsIn (recursorAsm R.depth)
            (Nat.log 2 (memWidth (accUpdate k π) (accStage k) t).toNat) ∧
          ∃ M, GodelThreshold.RepresentsUnderivableTruth (Encodable.encode : Sentence ℒₒᵣ → ℕ)
            (fun δ => (𝗣𝗔⁻ : ArithmeticTheory) ⊢ δ) (fun δ => ℕ↓[ℒₒᵣ] ⊧ δ) M := by
  have hmono : Monotone (fun t => Nat.log 2 (memWidth (accUpdate k π) (accStage k) t).toNat) := by
    intro a b hab
    simp only [memWidth_accreting_log_eq_of_trivialEnv]
    omega
  have hunb : ∀ N, ∃ t, N ≤ Nat.log 2 (memWidth (accUpdate k π) (accStage k) t).toNat := by
    intro N
    refine ⟨N, ?_⟩
    rw [memWidth_accreting_log_eq_of_trivialEnv]
    omega
  exact AccretingWitness.eventually_hosts_uniform hmono hunb

end MemoryWidth

/-! ## Axiom audit

Every capstone above is `#print axioms`-clean on the standard triple, and the guards below make
that build-enforced. -/

set_option linter.style.longLine false

/-- info: 'MemoryWidth.reaches_mergeLaw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MemoryWidth.reaches_mergeLaw

/-- info: 'MemoryWidth.mergeLaw_iterate_mergeMk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MemoryWidth.mergeLaw_iterate_mergeMk

/-- info: 'MemoryWidth.reaches_mergeMk_iterate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MemoryWidth.reaches_mergeMk_iterate

/-- info: 'MemoryWidth.memWidth_le_encard_mergeStage' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MemoryWidth.memWidth_le_encard_mergeStage

/-- info: 'MemoryWidth.memWidth_eq_encard_of_rootSet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MemoryWidth.memWidth_eq_encard_of_rootSet

/-- info: 'MemoryWidth.memWidth_eq_encard_of_isRootAntichain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MemoryWidth.memWidth_eq_encard_of_isRootAntichain

/-- info: 'MemoryWidth.exists_isRootAntichain_of_finite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MemoryWidth.exists_isRootAntichain_of_finite

/-- info: 'MemoryWidth.memWidth_eq_encard_canonical_of_antisymmOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MemoryWidth.memWidth_eq_encard_canonical_of_antisymmOn

/-- info: 'MemoryWidth.exists_canonicalSet_empty_pos_memWidth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MemoryWidth.exists_canonicalSet_empty_pos_memWidth

/-- info: 'MemoryWidth.pos_memWidth_not_exists_isRootAntichain_intSucc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MemoryWidth.pos_memWidth_not_exists_isRootAntichain_intSucc

/-- info: 'MemoryWidth.memWidth_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MemoryWidth.memWidth_mono

/-- info: 'MemoryWidth.memWidth_nat_succ_eq_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MemoryWidth.memWidth_nat_succ_eq_one

/-- info: 'MemoryWidth.mergeStage_nat_succ_fastClock_encard' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MemoryWidth.mergeStage_nat_succ_fastClock_encard

/-- info: 'MemoryWidth.exists_conservationGuest_extent_gt_memWidth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MemoryWidth.exists_conservationGuest_extent_gt_memWidth

/-- info: 'MemoryWidth.memWidth_accreting_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MemoryWidth.memWidth_accreting_ge

/-- info: 'MemoryWidth.memWidth_accreting_eq_of_trivialEnv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MemoryWidth.memWidth_accreting_eq_of_trivialEnv

/-- info: 'MemoryWidth.eventually_hosts_uniform_of_accreting_memWidth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MemoryWidth.eventually_hosts_uniform_of_accreting_memWidth
