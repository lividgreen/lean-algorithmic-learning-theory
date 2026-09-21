/-
Copyright (c) 2026 Mykola Palamarchuk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mykola Palamarchuk
-/
module

public import ALT.MemoryWidth

-- Formal-check file, not Mathlib-destined: opt out of the house-style header linter.
set_option linter.style.header false

/-!
# Derived stages: a world grown from a finite start set has bounded memory width

([Guests] §7 Definition 7.1's derived presentation)

Definition 7.1 allows a growing world's stages to be *given* (how a designed witness is built) or
*derived* from a designated finite start region as iterated images.
This file is the derived reading, literally: stage `t` is the `t`-th iterated image of a start set
`S` under the update `U`.
On such a world the memory width is bounded by the start set's own cardinality at every stage — a
pure profile fact, since it needs no antichain hypothesis at all — which closes the fixed-seed
route to unbounded width for every update at once: a finite start set can never supply the
certificate's crossing.

## Main results

* `derivedStages` — the derived presentation, `derivedStages U S t := U^[t] '' S`.
* `advances_derivedStages` — a world derived this way satisfies `GrowingWorld.Advances` with
  equality: `U '' (U^[t] '' S) = U^[t + 1] '' S`.
* `mergeStage_derivedStages_encard_le` — the derived world's stage-`t` retained profile is an image
  of an image of `S`, so its cardinality never exceeds `S`'s.
* `memWidth_derivedStages_le` — hence the memory width itself is capped by `S`'s cardinality at
  every stage, composing the above with `MemoryWidth.memWidth_le_encard_mergeStage`.
* `memWidth_derivedStages_ne_top` — at a finite start set the width stays finite at every stage.

## Scope

The bound is a profile fact: it consumes no antichain structure, so it says nothing about whether
the cap is attained or how far below it the true width sits at a particular update — `[grade B]`
(`ExtremeTapWidth.lean`) is where a concrete update's width is computed exactly.
-/


@[expose] public section

namespace DerivedStages

open MemoryWidth GrowingCore GrowingWorld

variable {X : Type*}

/-- **The derived presentation** ([Guests] §7 Definition 7.1): stage `t` is the `t`-th iterated
image of the start set `S` under the update `U`. -/
def derivedStages (U : X → X) (S : Set X) (t : ℕ) : Set X := U^[t] '' S

/-- **A derived world advances, with equality**: `U` carries the stage-`t` iterated image into the
stage-`(t + 1)` one, `Function.iterate_succ_apply'` supplying the one further step. -/
theorem advances_derivedStages (U : X → X) (S : Set X) :
    Advances U (derivedStages U S) := by
  intro t s hs
  obtain ⟨x, hx, rfl⟩ := hs
  exact ⟨x, hx, Function.iterate_succ_apply' U t x⟩

/-- **The retained profile is an image of an image of `S`**: `mergeStage` unfolds to `mergeMk U ''
(U^[t] '' S)`, and `Set.encard_image_le` fires twice. -/
theorem mergeStage_derivedStages_encard_le (U : X → X) (S : Set X) (t : ℕ) :
    (mergeStage U (derivedStages U S) t).encard ≤ S.encard :=
  calc (mergeStage U (derivedStages U S) t).encard
      = (mergeMk U '' (U^[t] '' S)).encard := rfl
    _ ≤ (U^[t] '' S).encard := Set.encard_image_le _ _
    _ ≤ S.encard := Set.encard_image_le _ _

/-- **Grade A**: the memory width of a world derived from `S` never exceeds `S`'s own cardinality,
at every stage — the fixed-seed route to the certificate's crossing is closed for every update at
once, since the certificate's width reading needs it unbounded. -/
theorem memWidth_derivedStages_le (U : X → X) (S : Set X) (t : ℕ) :
    memWidth U (derivedStages U S) t ≤ S.encard :=
  (memWidth_le_encard_mergeStage U (derivedStages U S) t).trans
    (mergeStage_derivedStages_encard_le U S t)

/-- At a finite start set the width stays finite at every stage: it is capped by `S.encard`, which
is itself finite. -/
theorem memWidth_derivedStages_ne_top (U : X → X) {S : Set X} (hS : S.Finite) (t : ℕ) :
    memWidth U (derivedStages U S) t ≠ ⊤ :=
  (lt_of_le_of_lt (memWidth_derivedStages_le U S t) hS.encard_lt_top).ne

end DerivedStages

/-! ## Axiom audit

Every capstone above is `#print axioms`-clean on the standard triple, and the guards below make
that build-enforced. -/

set_option linter.style.longLine false

/-- info: 'DerivedStages.advances_derivedStages' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DerivedStages.advances_derivedStages

/-- info: 'DerivedStages.mergeStage_derivedStages_encard_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DerivedStages.mergeStage_derivedStages_encard_le

/-- info: 'DerivedStages.memWidth_derivedStages_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DerivedStages.memWidth_derivedStages_le

/-- info: 'DerivedStages.memWidth_derivedStages_ne_top' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DerivedStages.memWidth_derivedStages_ne_top
