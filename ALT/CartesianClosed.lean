/-
Copyright (c) 2026 Mykola Palamarchuk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mykola Palamarchuk
-/
import Mathlib

-- Formal-check file, not Mathlib-destined: opt out of the house-style header linter.
set_option linter.style.header false

/-!
# Cartesian-closedness of a stand-in for Rep(S) (Paper I §4)

Provenance: Paper I, §4.1 (objects/morphisms of `Rep(S)`),
§4.2 (products), §4.3 (exponentials — "this is where functions become data", the heart), §4.4
(the Rule-30 example), §4.5 (what is / isn't constructed). Built on Mathlib's `MonoidalClosed`
(cartesian-closed = monoidal-closed over the cartesian monoidal structure).

Status: PROVED. This is the CCC/exponential machinery `Rep(S)` needs, exhibited on a **stand-in**
(`Type u`) — the CCC conjunct for the eventual full-`Reflective` assembly (D2 ∧ D1 ∧ D4).

## Stand-in status (read this — `Type u` is NOT `Rep(S)`)
`Rep(S)`'s objects are finite types `⊆ {0,1}^|s_work|` and its morphisms are `s_code`-implemented
computable functions (under program-equivalence). Mathlib's `FintypeCat` has no `MonoidalCategory`
instance, so a genuinely-finite CCC would be build-from-scratch — out of scope per §4.5. We use
`Type u`, which ships the cartesian-closed structure with the right *shape* (objects = types,
morphisms = functions, exponential = function object), and exhibit the §4.3/§4.5 content — not the
content-free bare instance. The `Fin m`/`Fin n` instantiation exhibits the finite-types /
finitely-many-programs flavor. This file establishes "the CCC/exponential machinery Rep(S) needs,
on a stand-in", which is the correct role for the CCC conjunct.

Superseded as the genuine carrier by `RepFintype.lean` (the finite-set CCC, FV-10) and
`RealizabilityCCC.lean` (the realizability CCC, FV-12); retained as the D2 stand-in that
`Reflective.lean` assembles.

## What this DOES establish
* `repS_cartesianClosed`: Proposition 4.3 (stand-in) — the category is Cartesian closed (terminal,
  products, exponentials).
* `expCurrying`: §4.3 — the exponential's evaluation/currying universal property, as the bijection
  `(A ⊗ Y ⟶ X) ≃ (Y ⟶ (A ⟹ X))`.
* `functionsAsData`: §4.5 — morphisms `A → B` correspond to the global elements of the exponential
  object `(A ⟹ B)`, i.e. "morphisms of Rep(S) are *described by* elements of an object of Rep(S)".
* `exp_finite`: §4.4 (miniature of "[State ⇒ State] has ≈ 2²⁰⁰ elements") — for finite objects the
  exponential has finitely many global elements ("finitely many programs").

## What this does NOT establish (flagged / other steps)
* NOT full `Rep(S)`: no `s_code`/`s_work`, no program-equivalence classes, no computability /
  bounded-budget restriction on morphisms, no universal-evaluator construction (§4.5: it is
  per-architecture, out of scope).
* NOT the §4.4 Rule-30 cellular-automaton construction.
* NOT the NNO (D1) or the Gödel threshold (D4) — only the CCC/exponential structure.
* `Type u` is a stand-in, NOT `Rep(S)` itself — objects/morphisms are unrestricted.

## Hypotheses: paper-stated vs added
* Paper-stated / faithful: Prop 4.3 (CCC); §4.3 exponential universal property; §4.5 functions-data;
  §4.4 exponential finiteness.
* Added / modeling: `Type u` as stand-in (objects not restricted to finite types, morphisms not
  restricted to `s_code`-computable functions); finite flavor only via the `Fin` instantiation.
-/

namespace RepSCCC

open CategoryTheory MonoidalCategory MonoidalClosed Limits

universe u

/-- Proposition 4.3 (stand-in): the category of types is Cartesian closed — terminal object,
binary products (the cartesian `⊗`), and exponentials (`ihom`). `Type u` stands in for `Rep(S)`. -/
theorem repS_cartesianClosed : Nonempty (MonoidalClosed (Type u)) := ⟨inferInstance⟩

/-- §4.3, the exponential's universal property (evaluation + currying as a bijection): maps
`A ⊗ Y → X` correspond to maps `Y → (A ⟹ X)`. The forward direction is currying; its inverse uses
evaluation. This is the categorical content of the functions-as-data architecture. -/
noncomputable def expCurrying (A X Y : Type u) : (A ⊗ Y ⟶ X) ≃ (Y ⟶ (ihom A).obj X) :=
  (ihom.adjunction A).homEquiv Y X

/-- §4.5, **functions as data**: morphisms `A → B` are in bijection with the global elements of the
exponential object `(A ⟹ B)` (maps from the unit `𝟙_`, the terminal object). This is exactly
"morphisms of Rep(S) are *described by* elements of a specific object of Rep(S)". -/
noncomputable def functionsAsData (A B : Type u) :
    (A ⟶ B) ≃ (𝟙_ (Type u) ⟶ (ihom A).obj B) :=
  (Iso.homCongr (ρ_ A).symm (Iso.refl B)).trans ((ihom.adjunction A).homEquiv (𝟙_ (Type u)) B)

/-- §4.4 (miniature of "[State ⇒ State] has ≈ 2²⁰⁰ elements"): for finite objects the exponential
has finitely many global elements — finitely many "programs". -/
theorem exp_finite (m n : ℕ) : Finite (𝟙_ (Type) ⟶ (ihom (Fin m)).obj (Fin n)) := by
  have hfin : Finite (Fin m ⟶ Fin n) :=
    Finite.of_injective (fun g : Fin m ⟶ Fin n => (g : Fin m → Fin n))
      (fun _ _ h => ConcreteCategory.hom_injective (DFunLike.coe_injective h))
  exact Finite.of_equiv _ ((Iso.homCongr (ρ_ (Fin m)).symm (Iso.refl (Fin n))).trans
      ((ihom.adjunction (Fin m)).homEquiv (𝟙_ (Type)) (Fin n)))

end RepSCCC
