/-
Copyright (c) 2026 Mykola Palamarchuk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mykola Palamarchuk
-/
import Mathlib
import ALT.RealizabilityCCC
import ALT.RealizabilityCoproduct

-- Formal-check file, not Mathlib-destined: opt out of the house-style linters.
set_option linter.style.header false
set_option linter.style.longLine false
-- Definitional `show` (unfolding assembly/composition projections to a defeq goal) is idiomatic here.
set_option linter.style.show false

/-!
# The subobject classifier of the finite fragment of `Rep(S)` ([Decoupling] §4.2)

Provenance: [Decoupling] §4.2 (the block "Subobjects and the classifier"). `ALT/RealizabilityCCC.lean`
built the realizability category `Asm` and proved it Cartesian closed; `ALT/RealizabilityCoproduct.lean`
added finite coproducts. This file completes the first-order inventory of §4.2 on that same carrier:
**comprehension subobjects**, the **one-bit subobject classifier** `Bool = 𝟙 ⊕ 𝟙`, its pullback
universal property, and **equalizers**.

## What this establishes
* `boolAsm := coprodAsm terminalAsm terminalAsm` — the classifier object `Bool = 𝟙 ⊕ 𝟙`, exactly one
  tag bit; `tru : 𝟙 ⟶ boolAsm` is its first injection ([Decoupling] §4.2, "`true : 1 → Bool` its first
  injection").
* `subAsm A P` — the comprehension subobject `{ a : A | P a }`, carrier the subtype, realizability
  inherited from `A`; its inclusion `subIncl` is realized by the identity program (encodings shared),
  so subobjects cost no capacity.
* `chi A P hA : A ⟶ boolAsm` — the characteristic map, a morphism because every function out of a
  finite object is realized ([Decoupling] §4.1, here the hypothesis `AllTrackable A`, which `finAsm`
  satisfies).
* `chi_comp_subIncl` + `classifier_universal` — the classifying square commutes and is a pullback:
  `u : C ⟶ A` factors through the comprehension subobject **iff** `χ_P ∘ u` is constantly `true`; the
  factorization carries `u`'s own realizer (no finiteness on `C`).
* `chi_unique` — the characteristic map is the *unique* morphism making that square a pullback, global
  elements (constant maps out of `𝟙`) separating the finite carrier.
* `eqAsm` + `equalizer_universal` — equalizers as comprehension subobjects, with their fork universal
  property.

## Fidelity boundary ([Decoupling] §4.2)
The classifier claim is for the **finite fragment**: it needs every function out of the classified
object to be a morphism (`AllTrackable`), which is the §4.1 property of *encoded finite objects*
(`finAsm` witnesses it) and not a property of general assemblies — for assemblies over a partial
combinatory algebra no full classifier exists (a quasitopos, not a topos; van Oosten 2008). The
comprehension subobjects are classified here; that a *mono* between finite objects is isomorphic to a
comprehension subobject (upgrading the classification to all monos) is stated at paper level.
-/

namespace RealizabilitySubobject

open RealizabilityCCC RealizabilityCoproduct CategoryTheory

/-! ### The terminal projection as a bundled morphism -/

/-- The unique morphism into the terminal object `𝟙`, bundled (`RealizabilityCCC.trackable_toTerminal`
supplies the tracking). -/
def toTerminal (A : Asm) : A ⟶ terminalAsm :=
  ⟨fun _ => PUnit.unit, trackable_toTerminal A⟩

/-! ### Global elements: every element of a carrier is a point `𝟙 ⟶ A` -/

/-- A constant-`m` code (`r · n = m` for all `n`); the realizer of a global element. -/
theorem exists_constCode (m : ℕ) : ∃ r : ℕ, ∀ n, ap r n = Part.some m := by
  have hc : Computable (fun _ : ℕ => m) := (Primrec.const m).to_comp
  obtain ⟨c, hc'⟩ := Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp hc)
  exact ⟨Encodable.encode c, fun n => by rw [ap_encode]; exact congrFun hc' n⟩

/-- The **global element** picking out `a : A.carrier`: the constant morphism `𝟙 ⟶ A`. Every element
is realized (the `Asm.realized` field), so the point exists — this is what lets global elements
separate a finite carrier in `chi_unique`. -/
noncomputable def globalElt (A : Asm) (a : A.carrier) : terminalAsm ⟶ A :=
  ⟨fun _ => a, (exists_constCode (A.realized a).choose).choose, by
    intro _ n _
    exact ⟨(A.realized a).choose,
      by rw [(exists_constCode (A.realized a).choose).choose_spec]; exact Part.mem_some _,
      (A.realized a).choose_spec⟩⟩

@[simp] theorem globalElt_apply (A : Asm) (a : A.carrier) (x : terminalAsm.carrier) :
    (globalElt A a).1 x = a := rfl

/-! ### The classifier object `Bool = 𝟙 ⊕ 𝟙` -/

/-- The **subobject classifier** `Bool := 𝟙 ⊕ 𝟙`, the coproduct of two singletons — exactly one tag
bit ([Decoupling] §4.2). -/
def boolAsm : Asm := coprodAsm terminalAsm terminalAsm

/-- `true : 𝟙 ⟶ Bool`, the first injection ([Decoupling] §4.2). -/
def tru : terminalAsm ⟶ boolAsm := inl terminalAsm terminalAsm

/-- The classifier carrier has exactly two global values, `true = inl ⋆` and `false = inr ⋆`. -/
theorem boolAsm_eq_or (z : boolAsm.carrier) :
    z = Sum.inl PUnit.unit ∨ z = Sum.inr PUnit.unit := by
  rcases z with u | u
  · exact Or.inl (by cases u; rfl)
  · exact Or.inr (by cases u; rfl)

/-- The classifier carrier is the two-element type `Bool` (`𝟙 ⊕ 𝟙 ≅ Bool`). -/
def boolEquiv : boolAsm.carrier ≃ Bool where
  toFun := fun z => match z with | Sum.inl _ => true | Sum.inr _ => false
  invFun := fun b => if b then Sum.inl PUnit.unit else Sum.inr PUnit.unit
  left_inv := by intro z; rcases z with ⟨⟩ | ⟨⟩ <;> rfl
  right_inv := by intro b; cases b <;> rfl

instance : Fintype boolAsm.carrier := Fintype.ofEquiv Bool boolEquiv.symm

/-- The classifier has exactly two elements — `|Bool| = 2` (the one tag bit of §4.2). -/
@[simp] theorem boolAsm_card : Fintype.card boolAsm.carrier = 2 := by
  rw [Fintype.card_congr boolEquiv]; exact Fintype.card_bool

/-! ### Comprehension subobjects -/

/-- The **comprehension subobject** `{ a : A | P a }`: carrier the subtype `{ a // P a }`, a code
realizes `⟨a, h⟩` exactly when it realizes `a` in `A` (encoding inherited from `A`). -/
def subAsm (A : Asm) (P : A.carrier → Prop) : Asm where
  carrier := { a : A.carrier // P a }
  realizes n x := A.realizes n x.1
  realized x := A.realized x.1

/-- The inclusion `{ a : A | P a } ↪ A` is realized by the identity program (`idCode`): the
comprehension subobject shares `A`'s encodings, so its inclusion costs no capacity. -/
def subIncl (A : Asm) (P : A.carrier → Prop) : subAsm A P ⟶ A :=
  ⟨Subtype.val, idCode, fun x n hn => ⟨n, by rw [ap_idCode]; exact Part.mem_some n, hn⟩⟩

@[simp] theorem subIncl_apply (A : Asm) (P : A.carrier → Prop) (x : { a // P a }) :
    (subIncl A P).1 x = x.1 := rfl

/-- **Factorization through a comprehension subobject.** A morphism `u : C ⟶ A` whose image lands in
`{ a : A | P a }` factors *uniquely* through the inclusion, and the factor carries `u`'s own realizer
(shared encodings) — so no finiteness on `C` is needed. This is the shared core of the classifier and
equalizer universal properties. -/
theorem subAsm_factor {A : Asm} (P : A.carrier → Prop) {C : Asm} (u : C ⟶ A)
    (hP : ∀ c, P (u.1 c)) :
    ∃! v : C ⟶ subAsm A P, v ≫ subIncl A P = u := by
  refine ⟨⟨fun c => ⟨u.1 c, hP c⟩, u.2.choose, ?_⟩, ?_, ?_⟩
  · intro c n hn
    obtain ⟨m, hm, hu⟩ := u.2.choose_spec c n hn
    exact ⟨m, hm, hu⟩
  · apply Subtype.ext; funext c; rfl
  · intro v' hv'
    apply Subtype.ext; funext c; apply Subtype.ext
    exact congrArg (fun m => m.1 c) hv'

/-! ### Finite objects: every function out of them is a morphism ([Decoupling] §4.1) -/

/-- The [Decoupling] §4.1 property of an *encoded finite object*: every function out of `A` is realized (a
morphism). It is what makes a characteristic map a morphism. General assemblies need not have it — the
realizability relation may fail to separate elements — but `finAsm` does (`finAsm_allTrackable`), and
so do the encoded finite objects of `Rep(S)`. -/
def AllTrackable (A : Asm) : Prop := ∀ (B : Asm) (g : A.carrier → B.carrier), Trackable A B g

/-- The finite assembly `finAsm M` is an encoded finite object: every function out of it is a
morphism (`RealizabilityCoproduct.trackable_of_finDom`). -/
theorem finAsm_allTrackable (M : ℕ) : AllTrackable (finAsm M) :=
  fun B g => trackable_of_finDom M B g

/-! ### The characteristic map and the classifier property -/

/-- The characteristic function of `P`: `true = inl ⋆` on `{ a | P a }`, `false = inr ⋆` off it. -/
def charFn {A : Asm} (P : A.carrier → Prop) [DecidablePred P] : A.carrier → boolAsm.carrier :=
  fun a => if P a then Sum.inl PUnit.unit else Sum.inr PUnit.unit

theorem charFn_eq_true_iff {A : Asm} (P : A.carrier → Prop) [DecidablePred P] (a : A.carrier) :
    charFn P a = Sum.inl PUnit.unit ↔ P a := by
  unfold charFn
  by_cases h : P a
  · exact iff_of_true (if_pos h) h
  · refine iff_of_false ?_ h
    rw [if_neg h]; simp

/-- The **characteristic map** `χ_P : A ⟶ Bool` of a comprehension subobject ([Decoupling] §4.2). A
morphism because `A` is a finite object out of which every function is realized (`hA`, the §4.1
property). -/
def chi (A : Asm) (P : A.carrier → Prop) [DecidablePred P] (hA : AllTrackable A) : A ⟶ boolAsm :=
  ⟨charFn P, hA boolAsm (charFn P)⟩

@[simp] theorem chi_apply (A : Asm) (P : A.carrier → Prop) [DecidablePred P] (hA : AllTrackable A)
    (a : A.carrier) : (chi A P hA).1 a = charFn P a := rfl

/-- Two morphisms out of the terminal object agree iff they agree at the single point. -/
theorem hom_from_terminal_ext {B : Asm} (p q : terminalAsm ⟶ B)
    (h : p.1 PUnit.unit = q.1 PUnit.unit) : p = q := by
  apply Subtype.ext; funext x
  cases x
  exact h

/-- **The classifying square commutes** ([Decoupling] §4.2): `i ≫ χ_P = ! ≫ true`, i.e. `χ_P` is constantly
`true` on the subobject. -/
theorem chi_comp_subIncl (A : Asm) (P : A.carrier → Prop) [DecidablePred P] (hA : AllTrackable A) :
    subIncl A P ≫ chi A P hA = toTerminal (subAsm A P) ≫ tru := by
  apply Subtype.ext; funext x
  show charFn P x.1 = Sum.inl PUnit.unit
  exact (charFn_eq_true_iff P x.1).mpr x.2

/-- **The classifier universal property (pullback).** For every `u : C ⟶ A`, the outer square with
`true` commutes — `u ≫ χ_P = ! ≫ true` — **iff** `u` factors (uniquely) through the comprehension
subobject `{ a : A | P a }`. Equivalently, the classifying square is a pullback. No finiteness on `C`
is needed: the factor carries `u`'s own realizer (`subAsm_factor`). -/
theorem classifier_universal (A : Asm) (P : A.carrier → Prop) [DecidablePred P] (hA : AllTrackable A)
    {C : Asm} (u : C ⟶ A) :
    u ≫ chi A P hA = toTerminal C ≫ tru ↔
      ∃! v : C ⟶ subAsm A P, v ≫ subIncl A P = u := by
  constructor
  · intro hsq
    have hP : ∀ c, P (u.1 c) := by
      intro c
      have hc : charFn P (u.1 c) = Sum.inl PUnit.unit := congrArg (fun m => m.1 c) hsq
      exact (charFn_eq_true_iff P (u.1 c)).mp hc
    exact subAsm_factor P u hP
  · rintro ⟨v, hv, -⟩
    have hP : ∀ c, P (u.1 c) := by
      intro c
      have hval : (v.1 c).1 = u.1 c := congrArg (fun m => m.1 c) hv
      have := (v.1 c).2
      rwa [hval] at this
    apply Subtype.ext; funext c
    show charFn P (u.1 c) = Sum.inl PUnit.unit
    exact (charFn_eq_true_iff P (u.1 c)).mpr (hP c)

/-- **Uniqueness of the classifying map** ([Decoupling] §4.2): any `χ' : A ⟶ Bool` making the same square a
pullback of the same comprehension subobject equals `χ_P`. Global elements (constant morphisms out of
`𝟙`, one per element of the carrier) separate the finite carrier: at each `a`, testing the pullback
condition against the point `a` forces `χ' a = true ↔ P a`. -/
theorem chi_unique (A : Asm) (P : A.carrier → Prop) [DecidablePred P] (hA : AllTrackable A)
    (χ' : A ⟶ boolAsm)
    (hχ' : ∀ {C : Asm} (u : C ⟶ A),
      u ≫ χ' = toTerminal C ≫ tru ↔ ∃! v : C ⟶ subAsm A P, v ≫ subIncl A P = u) :
    χ' = chi A P hA := by
  apply Subtype.ext; funext a
  show χ'.1 a = charFn P a
  -- Claim A: the square at the point `a` is equivalent to `χ' a = true`.
  have hA_sq : (globalElt A a ≫ χ' = toTerminal terminalAsm ≫ tru) ↔ χ'.1 a = Sum.inl PUnit.unit := by
    constructor
    · intro heq; exact congrArg (fun m => m.1 PUnit.unit) heq
    · intro heq; exact hom_from_terminal_ext _ _ heq
  -- Claim B: the pullback condition at the point `a` is equivalent to `P a`.
  have hB : (∃! v : terminalAsm ⟶ subAsm A P, v ≫ subIncl A P = globalElt A a) ↔ P a := by
    constructor
    · rintro ⟨v, hv, -⟩
      have hval : (v.1 PUnit.unit).1 = a := congrArg (fun m => m.1 PUnit.unit) hv
      have hPv := (v.1 PUnit.unit).2
      rwa [hval] at hPv
    · intro hPa
      refine ⟨globalElt (subAsm A P) ⟨a, hPa⟩, hom_from_terminal_ext _ _ rfl, ?_⟩
      intro v' hv'
      apply hom_from_terminal_ext
      apply Subtype.ext
      exact congrArg (fun m => m.1 PUnit.unit) hv'
  have hkey : χ'.1 a = Sum.inl PUnit.unit ↔ P a := by
    rw [← hA_sq, hχ' (globalElt A a)]; exact hB
  by_cases hPa : P a
  · rw [(charFn_eq_true_iff P a).mpr hPa]; exact hkey.mpr hPa
  · have h2 : charFn P a = Sum.inr PUnit.unit := by unfold charFn; exact if_neg hPa
    rw [h2]
    rcases boolAsm_eq_or (χ'.1 a) with h | h
    · exact absurd ((hkey.mp h)) hPa
    · exact h

/-! ### Equalizers as comprehension subobjects -/

/-- The **equalizer** of `f, g : A ⟶ B` as a comprehension subobject `{ a : A | f a = g a }` ([Decoupling]
§4.2: equality of encodings is decidable on finite objects, so equalizers are comprehension
subobjects, fitting wherever `A` does). -/
def eqAsm {A B : Asm} (f g : A ⟶ B) : Asm := subAsm A (fun a => f.1 a = g.1 a)

/-- The equalizer inclusion `Eq(f,g) ↪ A`. -/
def eqIncl {A B : Asm} (f g : A ⟶ B) : eqAsm f g ⟶ A := subIncl A (fun a => f.1 a = g.1 a)

/-- **The equalizer universal property (fork).** `u : C ⟶ A` coequalizes `f` and `g` — `u ≫ f = u ≫ g`
— **iff** it factors (uniquely) through the equalizer. No finiteness on `C`: the factor carries `u`'s
realizer (`subAsm_factor`). -/
theorem equalizer_universal {A B : Asm} (f g : A ⟶ B) {C : Asm} (u : C ⟶ A) :
    u ≫ f = u ≫ g ↔ ∃! v : C ⟶ eqAsm f g, v ≫ eqIncl f g = u := by
  constructor
  · intro hu
    exact subAsm_factor (fun a => f.1 a = g.1 a) u (fun c => congrArg (fun m => m.1 c) hu)
  · rintro ⟨v, hv, -⟩
    have hu : ∀ c, u.1 c = (v.1 c).1 := fun c => (congrArg (fun m => m.1 c) hv).symm
    apply Subtype.ext; funext c
    show f.1 (u.1 c) = g.1 (u.1 c)
    rw [hu c]; exact (v.1 c).2

end RealizabilitySubobject
