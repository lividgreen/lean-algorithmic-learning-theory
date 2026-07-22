/-
Copyright (c) 2026 Mykola Palamarchuk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mykola Palamarchuk
-/
import Mathlib

-- Formal-check file, not Mathlib-destined: opt out of the house-style linters.
set_option linter.style.header false
set_option linter.style.longLine false

/-!
# A genuine, discriminating initial algebra for the bounded recursor ([Decoupling] §5)

Provenance: [Decoupling] §5 (bounded recursor).
Companion / upgrade to the FV-17 material in `ALT/RepFintype.lean`
(`ParameterizedNNO.ParamNNO.recursorCone_isInitial`).

## Why this is sharper than FV-17
FV-17 states initiality of the recursor in a category of *recursion cones* whose hom-order is
"agree on the orbit `N_M`". That order is **symmetric** (agreement is an equivalence), so the cone
category is **thin/chaotic**: *every* object is initial and uniqueness is `Subsingleton.elim`. Its
initiality therefore does **not discriminate** — it is a universal property with a trivial (Prop)
hom-structure.

Here we give a *genuine* initial object of Mathlib's `CategoryTheory.Endofunctor.Algebra`, whose
morphisms are honest algebra homomorphisms (functions commuting with the structure map), **not**
`Prop`s. Distinct algebras give distinct recursors, so uniqueness is a real **induction over the
orbit**, not `Subsingleton`. This is the discriminating universal property FV-17 could not express.

## Honest boundary (`ParameterizedNNO.no_true_nno`)
The unrestricted initial algebra of `F X = 𝟙 ⊕ X` is `ℕ` (an infinite object), and `no_true_nno`
proves *no finite* state space carries such a true NNO. So a finite carrier is **never** initial in
all of `Endofunctor.Algebra succEndo`. We therefore restrict to the **full subcategory of
orbit-saturating algebras** (`Sat M`): those whose `z`-orbit reaches an `s`-fixed point by step `M`.
There the finite `Fin (M+1)` *saturating*-successor algebra is genuinely initial. This is a
**sharper-but-narrower** universal property than FV-17's arbitrary-target relativized recursor: the
successor saturates (it does not wrap, unlike the `ZMod` `cyclicParamNNO`) and the target class is
restricted, but within that class initiality is discriminating and the uniqueness is a genuine
induction.
-/

namespace RecursorAlgebra

open CategoryTheory CategoryTheory.Limits

/-! ### The endofunctor `F X = 𝟙 ⊕ X` and the `z`/`s` reading of its algebras -/

/-- The endofunctor `F X = 𝟙 ⊕ X` (`PUnit ⊕ X`) on `Type`. Its algebras `(A, str)` are exactly a
basepoint `z := str (inl ⋆)` together with a unary successor `s := str ∘ inr`; its *unrestricted*
initial algebra is `ℕ` (so no finite algebra is initial in all of `Algebra succEndo`). -/
def succEndo : Type ⥤ Type where
  obj X := PUnit ⊕ X
  map g := ↾(Sum.map id g)
  map_id X := by
    apply ConcreteCategory.ext_apply
    intro x; rcases x with u | a <;> simp
  map_comp f g := by
    apply ConcreteCategory.ext_apply
    intro x; rcases x with u | a <;> simp

@[simp] lemma succEndo_obj (X : Type) : succEndo.obj X = (PUnit ⊕ X) := rfl

@[simp] lemma succEndo_map_apply {X Y : Type} (g : X ⟶ Y) (x : succEndo.obj X) :
    succEndo.map g x = Sum.map id g x := rfl

/-- The basepoint `z = str (inl ⋆)` of an `F`-algebra. -/
def z (alg : Endofunctor.Algebra succEndo) : alg.a :=
  alg.str (Sum.inl PUnit.unit : succEndo.obj alg.a)

/-- The successor `s a = str (inr a)` of an `F`-algebra. -/
def s (alg : Endofunctor.Algebra succEndo) (a : alg.a) : alg.a :=
  alg.str (Sum.inr a : succEndo.obj alg.a)

lemma alg_str_inl (alg : Endofunctor.Algebra succEndo) :
    alg.str (Sum.inl PUnit.unit : succEndo.obj alg.a) = z alg := rfl

lemma alg_str_inr (alg : Endofunctor.Algebra succEndo) (a : alg.a) :
    alg.str (Sum.inr a : succEndo.obj alg.a) = s alg a := rfl

/-! ### The saturation predicate and the saturating full subcategory -/

/-- **Saturation.** `Sat M alg` says the `z`-orbit reaches an `s`-fixed point by step `M`:
`s (sᴹ z) = sᴹ z`. The algebras where the finite saturating recursor is the initial object. -/
def Sat (M : ℕ) (alg : Endofunctor.Algebra succEndo) : Prop :=
  s alg ((s alg)^[M] (z alg)) = (s alg)^[M] (z alg)

/-- The full subcategory of `F`-algebras satisfying `Sat M`. Its morphisms are the ambient
`Endofunctor.Algebra.Hom`s (genuine algebra homomorphisms), so the category is **not thin**. -/
abbrev SatAlg (M : ℕ) : Type _ :=
  ObjectProperty.FullSubcategory (fun alg : Endofunctor.Algebra succEndo => Sat M alg)

/-! ### The candidate: the `Fin (M+1)` saturating-successor algebra -/

/-- The **saturating successor** on `Fin (M+1)`: `k ↦ min (k+1) M`, i.e. climb `0,1,…,M` and then
stay at `M = Fin.last M`. (Equivalently `if k = Fin.last M then Fin.last M else k + 1`; the `min`
form avoids `Fin` wrap-around bookkeeping.) -/
def boundedSucc (M : ℕ) (k : Fin (M + 1)) : Fin (M + 1) :=
  ⟨min (k.val + 1) M, by omega⟩

/-- The candidate algebra: carrier `Fin (M+1)`, basepoint `0`, successor the saturating successor. -/
def boundedAlg (M : ℕ) : Endofunctor.Algebra succEndo where
  a := Fin (M + 1)
  str := ↾(Sum.elim (fun _ : PUnit => (0 : Fin (M + 1))) (boundedSucc M))

@[simp] lemma boundedAlg_str_inl (M : ℕ) (u : PUnit) :
    (boundedAlg M).str (Sum.inl u : succEndo.obj (Fin (M + 1))) = (0 : Fin (M + 1)) := rfl

@[simp] lemma boundedAlg_str_inr (M : ℕ) (k : Fin (M + 1)) :
    (boundedAlg M).str (Sum.inr k : succEndo.obj (Fin (M + 1))) = boundedSucc M k := rfl

@[simp] lemma boundedAlg_z (M : ℕ) : z (boundedAlg M) = (0 : Fin (M + 1)) := rfl

@[simp] lemma boundedAlg_s (M : ℕ) (k : Fin (M + 1)) : s (boundedAlg M) k = boundedSucc M k := rfl

/-- The orbit value climbs and saturates: `(sⁿ z).val = min n M`. -/
lemma boundedAlg_orbit_val (M n : ℕ) :
    ((s (boundedAlg M))^[n] (z (boundedAlg M))).val = min n M := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply', boundedAlg_s]
      change min (((s (boundedAlg M))^[n] (z (boundedAlg M))).val + 1) M = min (n + 1) M
      rw [ih]; omega

/-- The orbit reaches `Fin.last M` at step `M`. -/
lemma boundedAlg_orbit_M (M : ℕ) :
    (s (boundedAlg M))^[M] (z (boundedAlg M)) = Fin.last M := by
  apply Fin.ext
  rw [boundedAlg_orbit_val, Fin.val_last]; omega

/-- The saturating successor fixes `Fin.last M`. -/
lemma boundedSucc_last (M : ℕ) : boundedSucc M (Fin.last M) = Fin.last M := by
  apply Fin.ext
  change min ((Fin.last M).val + 1) M = (Fin.last M).val
  rw [Fin.val_last]; omega

/-- The candidate algebra is orbit-saturating. -/
lemma boundedAlg_sat (M : ℕ) : Sat M (boundedAlg M) := by
  change s (boundedAlg M) ((s (boundedAlg M))^[M] (z (boundedAlg M)))
      = (s (boundedAlg M))^[M] (z (boundedAlg M))
  rw [boundedAlg_orbit_M, boundedAlg_s, boundedSucc_last]

/-- The candidate as an object of the saturating subcategory `SatAlg M`. -/
def boundedInitialAlgebra (M : ℕ) : SatAlg M where
  obj := boundedAlg M
  property := boundedAlg_sat M

/-! ### The unique morphism out: the bounded recursor `k ↦ sᵏ z` -/

/-- The underlying map of the unique morphism `boundedAlg M ⟶ alg`: the bounded recursor
`k ↦ sᵏ z`. This is the saturating (`Fin`) counterpart of the wrapping (`ZMod`)
`ParameterizedNNO.cyclicParamNNO`. -/
def rec (M : ℕ) (alg : Endofunctor.Algebra succEndo) : Fin (M + 1) → alg.a :=
  fun k => (s alg)^[k.val] (z alg)

@[simp] lemma rec_zero (M : ℕ) (alg : Endofunctor.Algebra succEndo) : rec M alg 0 = z alg := by
  simp only [rec, Fin.val_zero, Function.iterate_zero_apply]

/-- The successor-square identity, using `Sat`: `s (sᵏ z) = s^{min (k+1) M} z`. For `k < M` the RHS
is `sᵏ⁺¹ z`; at `k = M` the RHS is `sᴹ z` and the identity is exactly `Sat M alg`. -/
lemma iterate_succ_sat (M : ℕ) (alg : Endofunctor.Algebra succEndo) (hsat : Sat M alg)
    (k : Fin (M + 1)) :
    s alg ((s alg)^[k.val] (z alg)) = (s alg)^[min (k.val + 1) M] (z alg) := by
  rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp k.isLt) with hlt | heq
  · rw [min_eq_left (by omega : k.val + 1 ≤ M), Function.iterate_succ_apply']
  · rw [heq, min_eq_right (by omega : M ≤ M + 1)]
    exact hsat

/-- The recursor square holds **pointwise**: at `inl ⋆` both sides are `z`; at `inr k` both are
`sᵏ⁺¹ z` (using `Sat M alg` at the saturating endpoint `k = M`). -/
lemma square_pointwise (M : ℕ) (alg : Endofunctor.Algebra succEndo) (hsat : Sat M alg)
    (x : PUnit ⊕ Fin (M + 1)) :
    alg.str (Sum.map id (rec M alg) x) = rec M alg ((boundedAlg M).str x) := by
  rcases x with u | k
  · cases u
    exact (rec_zero M alg).symm
  · change s alg ((s alg)^[k.val] (z alg)) = (s alg)^[min (k.val + 1) M] (z alg)
    exact iterate_succ_sat M alg hsat k

/-- The bounded recursor **is** an algebra homomorphism `boundedAlg M ⟶ alg`, for every saturating
`alg` (existence half of initiality). -/
def toSatHom (M : ℕ) (alg : Endofunctor.Algebra succEndo) (hsat : Sat M alg) :
    boundedAlg M ⟶ alg where
  f := ↾(rec M alg)
  h := by
    apply ConcreteCategory.ext_apply
    intro x
    exact square_pointwise M alg hsat x

/-- The `inl`-square, extracted from `g`'s hom law: `g 0 = z`. -/
lemma hom_zero (M : ℕ) (alg : Endofunctor.Algebra succEndo) (g : boundedAlg M ⟶ alg) :
    g.f (0 : Fin (M + 1)) = z alg := by
  have h := ConcreteCategory.congr_hom g.h (Sum.inl PUnit.unit : succEndo.obj (Fin (M + 1)))
  simp only [types_comp_apply] at h
  exact h.symm

/-- The `inr`-square, extracted from `g`'s hom law: `g (succ k) = s (g k)`. -/
lemma hom_succ (M : ℕ) (alg : Endofunctor.Algebra succEndo) (g : boundedAlg M ⟶ alg)
    (k : Fin (M + 1)) : g.f (boundedSucc M k) = s alg (g.f k) := by
  have h := ConcreteCategory.congr_hom g.h (Sum.inr k : succEndo.obj (Fin (M + 1)))
  simp only [types_comp_apply] at h
  exact h.symm

/-- **Uniqueness on the orbit** (a genuine induction, not `Subsingleton`): any algebra hom
`g : boundedAlg M ⟶ alg` has `g.f ⟨n, _⟩ = sⁿ z`. The base uses the `inl`-square (`g 0 = z`); the
step uses the `inr`-square at `⟨n, _⟩` with `n < M` (there the saturating successor is the honest
`n+1`), giving `g ⟨n+1,_⟩ = s (g ⟨n,_⟩)`. -/
lemma hom_f_orbit (M : ℕ) (alg : Endofunctor.Algebra succEndo) (g : boundedAlg M ⟶ alg) :
    ∀ (n : ℕ) (hn : n < M + 1), g.f (⟨n, hn⟩ : Fin (M + 1)) = (s alg)^[n] (z alg) := by
  intro n
  induction n with
  | zero =>
      intro hn
      have h0 : (⟨0, hn⟩ : Fin (M + 1)) = (0 : Fin (M + 1)) := by apply Fin.ext; simp
      rw [h0, Function.iterate_zero_apply]
      exact hom_zero M alg g
  | succ n ih =>
      intro hn
      have hn' : n < M + 1 := by omega
      have hlt : n < M := by omega
      have hpt : boundedSucc M (⟨n, hn'⟩ : Fin (M + 1)) = (⟨n + 1, hn⟩ : Fin (M + 1)) := by
        apply Fin.ext
        change min (n + 1) M = n + 1
        omega
      have hs := hom_succ M alg g (⟨n, hn'⟩ : Fin (M + 1))
      rw [hpt] at hs
      rw [hs, ih hn', Function.iterate_succ_apply']

/-- Consequently `g.f = ↾(rec M alg)` for every algebra hom `g : boundedAlg M ⟶ alg`. -/
lemma hom_f_eq_rec (M : ℕ) (alg : Endofunctor.Algebra succEndo) (g : boundedAlg M ⟶ alg) :
    g.f = ↾(rec M alg) := by
  apply ConcreteCategory.ext_apply
  intro k
  exact hom_f_orbit M alg g k.val k.isLt

/-! ### The discriminating initiality -/

/-- **Headline.** `boundedInitialAlgebra M` is a *genuine* `IsInitial` object of the
saturating full subcategory `SatAlg M` of `Endofunctor.Algebra succEndo`. Discharged via
`IsInitial.ofUniqueHom`: existence is the recursor hom `toSatHom`, uniqueness is the orbit induction
`hom_f_eq_rec`.

Honesty (three points):
* **(a) Genuine & discriminating.** Morphisms here are honest algebra homomorphisms, not `Prop`s
  (contrast FV-17's thin cone category, where initiality is `Subsingleton.elim`). Distinct algebras
  give distinct recursors, so uniqueness is a real induction over the orbit.
* **(b) Only in the subcategory.** Initiality holds **only** in the saturating subcategory `SatAlg M`,
  **not** in all of `Endofunctor.Algebra succEndo`: the unrestricted initial `𝟙 ⊕ (·)`-algebra is
  `ℕ`, and `ParameterizedNNO.no_true_nno` proves no finite carrier is a true NNO. Correspondingly the
  structure map is **not** an isomorphism here (`boundedAlg_str_not_injective`), so Lambek's
  `Endofunctor.Algebra.Initial.str_isIso` — which needs initiality in the *whole* algebra category —
  does not apply; a true (Lambek-iso-structure) initial `𝟙 ⊕ (·)`-algebra would be the infinite `ℕ`.
* **(c) Sharper-but-narrower.** A saturating successor and a restricted target class — a sharper
  (discriminating, non-thin) but narrower universal property than FV-17's arbitrary-target
  relativized recursor. -/
def boundedInitialAlgebra_isInitial (M : ℕ) : IsInitial (boundedInitialAlgebra M) :=
  IsInitial.ofUniqueHom
    (fun Y => ObjectProperty.homMk (toSatHom M Y.obj Y.property))
    (fun Y m => by
      apply ObjectProperty.hom_ext
      apply Endofunctor.Algebra.ext
      exact hom_f_eq_rec M Y.obj m.hom)

/-- The unique morphism out of the initial object has underlying map the bounded recursor
`k ↦ sᵏ z` — the saturating (`Fin`) counterpart of the wrapping (`ZMod`)
`ParameterizedNNO.cyclicParamNNO`. -/
lemma toSatHom_f_apply (M : ℕ) (alg : Endofunctor.Algebra succEndo) (hsat : Sat M alg)
    (k : Fin (M + 1)) : (toSatHom M alg hsat).f k = (s alg)^[k.val] (z alg) := rfl

/-- **Honesty (Lambek does not apply here).** The structure map of `boundedInitialAlgebra M` is not
injective (its domain `PUnit ⊕ Fin (M+1)` has `M+2` elements, its codomain `M+1`), hence not an
isomorphism. So the finite initial object of the saturating subcategory is *not* a Lambek fixed
point — exactly the finite-capacity obstruction of `no_true_nno`. -/
theorem boundedAlg_str_not_injective (M : ℕ) :
    ¬ Function.Injective (boundedAlg M).str := by
  intro hinj
  have hle : Fintype.card (PUnit.{1} ⊕ Fin (M + 1)) ≤ Fintype.card (Fin (M + 1)) :=
    Fintype.card_le_of_injective
      (show PUnit.{1} ⊕ Fin (M + 1) → Fin (M + 1) from (boundedAlg M).str) hinj
  simp only [Fintype.card_sum, Fintype.card_fin, Fintype.card_punit] at hle
  omega

end RecursorAlgebra
