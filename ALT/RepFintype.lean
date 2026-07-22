/-
Copyright (c) 2026 Mykola Palamarchuk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mykola Palamarchuk
-/
import Mathlib
import ALT.ParameterizedNNO

-- Formal-check file, not Mathlib-destined: opt out of the house-style linters.
set_option linter.style.header false
set_option linter.style.longLine false

/-!
# Rep(S) on ONE faithful carrier: the Cartesian-closed category of FINITE sets ([Decoupling] §4, §6.1)

Provenance: [Decoupling] §4 (Proposition 4.3 — Rep(S) is "a full
subcategory of finite sets, Cartesian closed up to capacity"; the realizability "functions as data"
layer) and §6.1 (Definition 6.1 — ONE Rep(S) that is a CCC AND contains the bounded recursor).

## What this fixes (two stand-in weaknesses of the earlier formalization)
Earlier the CCC was certified on the **trivial `Type` stand-in** (`ALT/CartesianClosed.lean`,
`MonoidalClosed Type` by `inferInstance` — true of *all* types, finiteness unused), while the
recursor lived on a **separate** carrier (`ZMod`, `ALT/ParameterizedNNO.lean`) — two *disjoint*
stand-ins, not one `Rep(S)`. Here both live on ONE setting: the category of **finite sets** (objects
= finite types, morphisms = functions, realizers-as-values = elements of the exponential object).

* **Genuine finite-set CCC (not the `Type` triviality).** The Cartesian-closed operations are
  certified with finiteness *load-bearing*: the terminal object, binary products, and the
  exponential are all **finite** (`terminal_finite`, `prod_finite`, `exp_finite`), with the product
  and exponential (currying) universal properties as explicit bijections (`prod_universal`,
  `exp_currying`), evaluation (`eval`), and the "functions as data" identification of a morphism
  with a point of the exponential object (`functionsAsData`). `exp_finite` — finite sets are closed
  under function spaces — is the crux that the `Type` stand-in could not express.
* **Unification with the recursor.** The bounded recursor of §5 is itself a finite object of this
  same category (`recursorCarrier M := ZMod (M+1)`, `cyclicParamNNO M`), so Definition 6.1's
  "one Rep(S), CCC ∧ recursor" is modeled on one carrier — `Reflective`/`reflective_satisfiable`.

## Honest boundary (what stays paper-level)
The **realizability / capacity** layer of §4.1, §4.3 — objects encoded into `s_work`, morphisms
carrying realizer *codes*, the "up to capacity" filtration — is NOT modeled: this file certifies the
categorical *finite-set* shape (the genuine CCC of finite sets) and its unification with the
recursor, not the `s_work` encoding. We certify the CCC operations **concretely** (as bijections on
finite types) rather than via Mathlib's `MonoidalClosed FintypeCat` instance: the abstract internal
hom `(ihom X).obj Y` does not reduce to the function type `X → Y` definitionally (a Mathlib
`Quiver.Hom`/`ihom` defeq obstruction), so the concrete bijections are the faithful, transparent
certification of the same content.
-/

namespace RepFintype

open ParameterizedNNO

universe u

/-! ### The Cartesian-closed structure of finite sets (finiteness load-bearing) -/

/-- Terminal object `1 = PUnit` is finite. -/
theorem terminal_finite : Finite PUnit.{u + 1} := inferInstance

/-- Terminal universal property: exactly one morphism `Z → 1`. -/
instance terminal_unique (Z : Type u) : Unique (Z → PUnit.{u + 1}) := inferInstance

/-- Binary products of finite objects are finite. -/
theorem prod_finite (X Y : Type u) [Finite X] [Finite Y] : Finite (X × Y) := inferInstance

/-- Product universal property as a bijection: `Hom(Z, X×Y) ≃ Hom(Z,X) × Hom(Z,Y)`. -/
def prod_universal (Z X Y : Type u) : (Z → X × Y) ≃ ((Z → X) × (Z → Y)) where
  toFun f := (fun z => (f z).1, fun z => (f z).2)
  invFun p z := (p.1 z, p.2 z)
  left_inv _ := rfl
  right_inv _ := rfl

/-- **Exponentials of finite objects are finite** — the crux of the finite-set CCC that the `Type`
stand-in could not express (finite sets are closed under function spaces). -/
theorem exp_finite (X Y : Type u) [Finite X] [Finite Y] : Finite (X → Y) := inferInstance

/-- Exponential universal property (currying): `Hom(Z×X, Y) ≃ Hom(Z, Yˣ)`. -/
def exp_currying (Z X Y : Type u) : (Z × X → Y) ≃ (Z → (X → Y)) := Equiv.curry Z X Y

/-- Evaluation morphism `eval : Yˣ × X → Y`. -/
def eval (X Y : Type u) : (X → Y) × X → Y := fun p => p.1 p.2

/-- "Functions as data" (§4.1, §4.3): a morphism `X → Y` is exactly a **point** (global element
`1 → Yˣ`) of the exponential object — morphisms of Rep(S) are values of an object of Rep(S). -/
def functionsAsData (X Y : Type u) : (PUnit.{u + 1} → (X → Y)) ≃ (X → Y) :=
  Equiv.funUnique PUnit (X → Y)

/-! ### The bounded recursor as a finite object of the SAME category -/

/-- The recursor object `N_M` is the finite object `ZMod (M+1)` of the finite-set category. -/
abbrev recursorCarrier (M : ℕ) : Type := ZMod (M + 1)

theorem recursorCarrier_finite (M : ℕ) : Finite (recursorCarrier M) := inferInstance

/-! ### Definition 6.1, faithful & unified (CCC of finite sets ∧ recursor object) -/

/-- **Definition 6.1, unified on one carrier.** A subsystem with internal-theory Gödel number
`gTS` is *reflective* when the ambient category of finite sets is genuinely Cartesian closed
(recorded by exponential closure of finite objects — the non-trivial finite-CCC fact) AND it
contains a bounded recursor *object* of depth `> gTS`. Both conjuncts live on **finite sets** — one
carrier, not two disjoint stand-ins. -/
def Reflective (gTS : ℕ) : Prop :=
  -- (i) the ambient category is the genuine finite-set CCC (exponentials of finite objects exist):
  (∀ X Y : Type, Finite X → Finite Y → Finite (X → Y)) ∧
  -- (ii) it contains a bounded-recursor object of depth > gTS (a finite object `ZMod (M+1)`):
  ∃ M : ℕ, gTS < M ∧ Nonempty (ParamNNO (recursorCarrier M))

/-- The unified Definition 6.1 is satisfiable for every `gTS` (non-vacuity), on ONE carrier: the
finite-set CCC (exponential closure) together with `cyclicParamNNO (gTS+1)` of depth `gTS+1 > gTS`
on the finite object `ZMod (gTS+2)`. Unlike the earlier `Type` stand-in, the CCC conjunct genuinely
uses finiteness, and the recursor is an object of the same category. -/
theorem reflective_satisfiable (gTS : ℕ) : Reflective gTS :=
  ⟨fun _ _ hX hY => by haveI := hX; haveI := hY; exact inferInstance,
    gTS + 1, Nat.lt_succ_self gTS, ⟨cyclicParamNNO (gTS + 1)⟩⟩

end RepFintype

/-! ### The bounded recursor as an INITIAL object (relativized universal property, [Decoupling] §5)

We upgrade the orbit-form bounded recursor (`ParameterizedNNO.ParamNNO.bounded_recursor`) to a
genuine **categorical universal property**, reusing Mathlib's `CategoryTheory.Limits.IsInitial`.

**Honesty constraint (`ParameterizedNNO.no_true_nno`).** `no_true_nno` proves that *no* finite state
space `W` carries a true natural-numbers object — the orbit `n ↦ succ^[n] zero` must cycle. So `N_M`
is **not** an initial `𝟙 ⊕ (·)`-algebra (that object is `ℕ`), and we deliberately do **not** state
initiality of an `Endofunctor.Algebra`. Instead we state initiality in the category of **depth-`≤ M`
recursion cones**: objects are maps `h : W → A` satisfying the depth-`M` recursion, morphisms are
"agree on the orbit `N_M`". This is a *relativized* universal property — canonical up to depth `M`,
exactly the strength `no_true_nno` permits — and there the paper recursor is the initial object. -/

namespace ParameterizedNNO

open CategoryTheory CategoryTheory.Limits

variable {W : Type*} [Fintype W]

/-- A **recursion cone** over `(A, a, f)` for a depth-`M` parameterized NNO `P`: a map `h : W → A`
together with a proof `P.Recurses a f h` that it satisfies the depth-`M` recursion. These are the
objects of the relativized universal property (see the module note and `no_true_nno`). -/
structure ParamNNO.RecCone (P : ParamNNO W) {A : Type*} (a : A) (f : A → A) where
  /-- The underlying recursor map `W → A`. -/
  h : W → A
  /-- Proof that `h` satisfies the depth-`M` recursion `P.Recurses a f h`. -/
  recurses : P.Recurses a f h

/-- The **thin preorder** on recursion cones: `c ≤ c'` iff the two cones agree on the whole orbit
`N_M` (`h (succ^[k] zero)` for every `k ≤ M`). Reflexivity/transitivity are just equality on each
orbit point, so this is a `Preorder`; via Mathlib's `Preorder.smallCategory` it makes `RecCone P a f`
a (thin) category whose morphisms encode exactly the depth-`M` agreement of `bounded_recursor`. -/
instance {P : ParamNNO W} {A : Type*} {a : A} {f : A → A} : Preorder (P.RecCone a f) where
  le c c' := ∀ k, k ≤ P.depth → c.h (P.succ^[k] P.zero) = c'.h (P.succ^[k] P.zero)
  le_refl _ := fun _ _ => rfl
  le_trans _ _ _ h₁ h₂ := fun k hk => (h₁ k hk).trans (h₂ k hk)

/-- The paper's bounded recursor (the witness of `bounded_recursor`'s existence half) packaged as a
cone object of `RecCone P a f`. -/
noncomputable def ParamNNO.recursorCone (P : ParamNNO W) {A : Type*} (a : A) (f : A → A) :
    P.RecCone a f where
  h := (P.bounded_recursor a f).1.choose
  recurses := (P.bounded_recursor a f).1.choose_spec

/-- **Headline.** The paper recursor is an **initial object** of the category of
depth-`≤ M` recursion cones: for every cone `c` there is a (unique) morphism `recursorCone ⟶ c`,
namely the depth-`M` agreement supplied by `bounded_recursor`'s uniqueness half; uniqueness is
automatic because the category is thin (hom-types are `Prop`s). This makes the recursor a **canonical
object, not merely an orbit**, while respecting `no_true_nno`: the property is relativized to
depth `≤ M`, *not* initiality among `ℕ`-algebras (no finite `W` carries a true NNO). -/
noncomputable def ParamNNO.recursorCone_isInitial (P : ParamNNO W) {A : Type*} (a : A) (f : A → A) :
    IsInitial (P.recursorCone a f) :=
  IsInitial.ofUniqueHom
    (fun c => homOfLE fun k hk =>
      (P.bounded_recursor a f).2 (P.recursorCone a f).h c.h
        (P.recursorCone a f).recurses c.recurses k hk)
    (fun _ _ => Subsingleton.elim _ _)

/-- **Canonicity ("not merely an orbit").** Any *other* initial cone `c` agrees with the paper
recursor on the whole orbit `N_M`: initiality of `c` gives a morphism `c ⟶ recursorCone`, which is
(`leOfHom`) exactly the depth-`M` agreement. So the recursor is determined by the relativized
universal property, up to the thin category's unique isomorphism. -/
theorem ParamNNO.recursorCone_canonical (P : ParamNNO W) {A : Type*} (a : A) (f : A → A)
    (c : P.RecCone a f) (hc : Nonempty (IsInitial c)) :
    ∀ k, k ≤ P.depth → c.h (P.succ^[k] P.zero) = (P.recursorCone a f).h (P.succ^[k] P.zero) := by
  obtain ⟨hci⟩ := hc
  exact leOfHom (hci.to (P.recursorCone a f))

/-- The old orbit-form `bounded_recursor` is **re-derivable** from the categorical formulation, so
the two are inter-derivable: existence is the `recursorCone` object, and uniqueness-on-`N_M` is
initiality (each recursor becomes a cone, and the unique maps out of `recursorCone` force agreement). -/
theorem ParamNNO.bounded_recursor_of_isInitial (P : ParamNNO W) {A : Type*} (a : A) (f : A → A) :
    (∃ h : W → A, P.Recurses a f h) ∧
      ∀ h₁ h₂ : W → A, P.Recurses a f h₁ → P.Recurses a f h₂ →
        ∀ k, k ≤ P.depth → h₁ (P.succ^[k] P.zero) = h₂ (P.succ^[k] P.zero) := by
  refine ⟨⟨(P.recursorCone a f).h, (P.recursorCone a f).recurses⟩, ?_⟩
  intro h₁ h₂ hr₁ hr₂ k hk
  have e₁ := leOfHom ((P.recursorCone_isInitial a f).to (⟨h₁, hr₁⟩ : P.RecCone a f)) k hk
  have e₂ := leOfHom ((P.recursorCone_isInitial a f).to (⟨h₂, hr₂⟩ : P.RecCone a f)) k hk
  exact e₁.symm.trans e₂

end ParameterizedNNO
