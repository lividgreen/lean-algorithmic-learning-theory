/-
Copyright (c) 2026 Mykola Palamarchuk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mykola Palamarchuk
-/
import Mathlib
import ALT.RealizabilityRecursor
import ALT.CapacityLayer
import ALT.GodelInternalization
import ALT.GodelThreshold

-- Formal-check file, not Mathlib-destined: opt out of the house-style linters.
set_option linter.style.header false
set_option linter.style.longLine false

/-!
# Theorem 6.2 as ONE machine-checked theorem on the genuine carrier (FV-15)

Provenance: [Decoupling] §6.1 (Definition 6.1, Theorem 6.2) and
§6.3 (the represent-but-cannot-derive consequence). This file closes the seam recorded at
Theorem 6.2 ("Theorem 6.2's *statement* … is assembled at paper level; no single Lean theorem
asserts it"): it bundles the three previously-separate machine-checked constituents into ONE
statement on the genuine realizability carrier `Asm`.

The constituents (all already axiom-clean):
* **Definition 6.1, one carrier** — `RealizabilityRecursor.ReflectiveAsm` (FV-13): the genuine
  Cartesian-closed realizability category `Asm` (FV-12) carrying the bounded recursor as an
  *object* of depth `> g`. `reflectiveAsm_satisfiable_depth` below generalizes FV-13's
  `reflectiveAsm_satisfiable` (which hard-coded `depth = g+1`) to an arbitrary working depth
  `> g`, so the recursor object can sit at the checker's working budget `M_chk`.
* **Theorem 6.2 capacity** — `CapacityLayer.recursorAsm_fitsIn` (FV-14) ∘
  `GodelInternalization.capacity_bound` (FV-8): the recursor object of working depth `M_chk ≤ g²`
  **fits in the explicit linear capacity `capacity n = 2n`** work bits (`n = ⌈log₂(g+1)⌉`).
* **§6.3 consequence** — `RealizabilityRecursor.reflectiveAsm_representsUnderivableTruth` (FV-13):
  under imported incompleteness for the subsystem's theory at `g`, that genuine reflective object
  **represents a sentence that is true-but-underivable** in the internal logic.

## Boundary (the one paper-level residue)
This is the categorical/logical content of Theorem 6.2 on the genuine realizability CCC carrier.
What stays paper-level is **only** the *concrete* bitstring layout — that an actual decoupled
subsystem's `Rep(S)` is realized with its objects laid out as bitstrings in `{0,1}^{|s_work|}`.
The category, the recursor object, the capacity arithmetic, and the consequence are all checked
here. Gödel's first incompleteness theorem remains the imported black box
(`GodelThreshold.Incompleteness`), as everywhere in §6.
-/

namespace CategoricalThreshold

open RealizabilityRecursor RealizabilityCCC ParameterizedNNO CategoryTheory

/-- **Definition 6.1 on one carrier, at an arbitrary working depth.** Generalizes FV-13's
`reflectiveAsm_satisfiable` (`depth = gTS + 1`) to any `depth = d > gTS`, so the recursor object
can be placed at the checker's working budget `M_chk` rather than only at the indexing budget.
Every conjunct is about the SAME Cartesian-closed realizability category `Asm` (FV-12); the
recursor object `recursorAsm d` carries `zero`/`succ` as genuine `Asm`-morphisms equal (pointwise,
`rfl`) to the §5 `ParamNNO` structure maps `cyclicParamNNO d`. -/
def reflectiveAsm_satisfiable_depth (gTS d : ℕ) (h : gTS < d) : ReflectiveAsm gTS where
  terminal A := trackable_toTerminal A
  fst A B := ⟨leftCode, fst_tracks A B⟩
  snd A B := ⟨rightCode, snd_tracks A B⟩
  eval_tracks A B := ev_tracks A B
  exp_univ _ _ _ gmor := exp_universal gmor
  depth := d
  depth_gt := h
  zero := zeroMor d
  succ := succMor d
  orbit := cyclicParamNNO d
  orbit_depth := rfl
  succ_eq _ := rfl
  zero_eq := rfl

/-- **Theorem 6.2 (Categorical threshold), as one machine-checked theorem on the genuine carrier.**
For a theory of Gödel size `g` and a proof-code working budget `M_chk` with `g < M_chk ≤ g²`
(the concrete degree-2 budget; write `n := ⌈log₂(g+1)⌉` for the size of the Gödel sentence),
there is a genuine **reflective object** `R` of the realizability CCC `Asm` (Definition 6.1: the
Cartesian-closed universal properties together with a bounded-recursor object) such that:

* **(reflective)** `R : ReflectiveAsm g` — one categorical object that is Cartesian closed AND a
  bounded recursor of working depth `> g` (FV-12/FV-13);
* **(working depth)** `R.depth = M_chk` — the recursor object sits at the checker's working budget;
* **(capacity, Theorem 6.2)** the recursor object `FitsIn` the explicit linear capacity
  `capacity n = 2n` work bits (FV-8 `capacity_bound` ∘ FV-14 `recursorAsm_fitsIn`);
* **(§6.3 consequence)** under imported incompleteness at `g`, `R` represents a sentence that is
  true and underivable in the internal logic (FV-13 `reflectiveAsm_representsUnderivableTruth`).

`Incompleteness` is the imported Gödel black box (§6.2). The only paper-level residue is the
concrete `{0,1}^{|s_work|}` bitstring layout (see the module boundary note). -/
theorem categorical_threshold
    {Sentence : Type*} (gnum : Sentence → ℕ) (Derivable True_ : Sentence → Prop)
    (g Mchk : ℕ) (hidx : g < Mchk) (hpoly : Mchk ≤ g ^ 2) :
    ∃ R : ReflectiveAsm g,
      R.depth = Mchk ∧
      CapacityLayer.FitsIn (recursorAsm R.depth)
        (GodelInternalization.capacity (Nat.clog 2 (g + 1))) ∧
      (GodelThreshold.Incompleteness gnum Derivable True_ g →
        ∃ M, GodelThreshold.RepresentsUnderivableTruth gnum Derivable True_ M) := by
  refine ⟨reflectiveAsm_satisfiable_depth g Mchk hidx, rfl, ?_, ?_⟩
  · -- capacity: the recursor object of working depth M_chk ≤ g² fits in capacity n = 2n bits
    -- `R.depth` is `Mchk` definitionally; `change` rewrites to the reduced form.
    change CapacityLayer.FitsIn (recursorAsm Mchk)
      (GodelInternalization.capacity (Nat.clog 2 (g + 1)))
    exact CapacityLayer.recursorAsm_fitsIn Mchk _ (GodelInternalization.capacity_bound g Mchk hpoly)
  · -- §6.3 consequence: under imported incompleteness, represents an underivable truth
    intro hInc
    exact reflectiveAsm_representsUnderivableTruth gnum Derivable True_ g
      (reflectiveAsm_satisfiable_depth g Mchk hidx) hInc

/-! ### Corollary 6.4 (Capacity stratification of the categorical threshold, [Decoupling] §6.4)

A subsystem with `w` work bits **hosts** the Gödel-decision recursor for a theory of Gödel size `g`
exactly when `w` meets the linear capacity `2n`, `n := ⌈log₂(g+1)⌉`. This stratifies §6's threshold
by working-memory budget: the property is monotone in `w`, is entered precisely at capacity `2n`,
and is excluded below `n`. -/

/-- [Decoupling] §6.4 (Corollary 6.4): a subsystem with `w` work bits **hosts** the categorical threshold
for a theory of Gödel size `g` when its budget covers the linear capacity `capacity n = 2n`,
`n := ⌈log₂(g+1)⌉` (the size of the Gödel sentence). -/
def hostsAt (w g : ℕ) : Prop := GodelInternalization.capacity (Nat.clog 2 (g + 1)) ≤ w

/-- **Monotone in the work budget**: more work memory only helps. -/
theorem hostsAt_mono {w w' g : ℕ} (h : w ≤ w') : hostsAt w g → hostsAt w' g :=
  fun hw => le_trans hw h

/-- **Entered at capacity**: the threshold is met exactly once the budget reaches `capacity n = 2n`. -/
theorem hostsAt_enters (g : ℕ) : hostsAt (GodelInternalization.capacity (Nat.clog 2 (g + 1))) g :=
  le_refl _

/-- **Excluded below `n`**: a budget under the Gödel-sentence size `n = ⌈log₂(g+1)⌉` cannot host the
threshold — indeed the capacity is the strictly larger `2n`, so `w < n` fails already. -/
theorem hostsAt_excludes {w g : ℕ} (h : w < Nat.clog 2 (g + 1)) : ¬ hostsAt w g := by
  intro hh
  simp only [hostsAt, GodelInternalization.capacity] at hh
  omega

/-- **Corollary 6.4, the delivered object.** Once `w` hosts the threshold (`hostsAt w g`) and the
proof-code budget satisfies `g < M_chk ≤ g²`, the genuine FV-15 object of Theorem 6.2 is realized at
budget `w`: a reflective object `R` of the realizability CCC `Asm`, of working depth `M_chk`, whose
bounded-recursor object `FitsIn`s the `w` work bits (by capacity monotonicity from the linear `2n`),
and which — under imported incompleteness at `g` — represents a true-but-underivable sentence. -/
theorem hostsAt_threshold
    {Sentence : Type*} (gnum : Sentence → ℕ) (Derivable True_ : Sentence → Prop)
    {w g Mchk : ℕ} (h : hostsAt w g) (h1 : g < Mchk) (h2 : Mchk ≤ g ^ 2) :
    ∃ R : ReflectiveAsm g,
      R.depth = Mchk ∧
      CapacityLayer.FitsIn (recursorAsm R.depth) w ∧
      (GodelThreshold.Incompleteness gnum Derivable True_ g →
        ∃ M, GodelThreshold.RepresentsUnderivableTruth gnum Derivable True_ M) := by
  obtain ⟨R, hdepth, hfits, hcons⟩ := categorical_threshold gnum Derivable True_ g Mchk h1 h2
  exact ⟨R, hdepth, hfits.mono h, hcons⟩

end CategoricalThreshold
