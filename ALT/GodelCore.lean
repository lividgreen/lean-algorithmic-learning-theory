/-
Copyright (c) 2026 Mykola Palamarchuk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mykola Palamarchuk
-/
-- Targeted (non-umbrella) import: gives ℕ order + `omega` without pulling
-- `Mathlib.LinearAlgebra.Matrix.Defs`, so this file stays co-importable with Foundation.
import Mathlib.Order.Basic

set_option linter.style.header false

/-!
# Gödel threshold — pure-logic core (Paper I §5.3 + §6)

Mathlib-free core of `ALT/GodelThreshold.lean` (D4): the abstract predicates and the threshold
lemma, in `namespace GodelThreshold` so all existing references (`GodelThreshold.Incompleteness`,
`…RepresentsUnderivableTruth`, `…godel_threshold`, `…Representable`) resolve unchanged.

This file deliberately imports **nothing** (core Lean only). That lets BOTH the Mathlib side
(`ALT/GodelThreshold.lean`, which adds the D1-NNO–tied `reflective_of_depth`) and the Foundation
side (`ALT/GodelComplete.lean`, which discharges `Incompleteness` from the ported Gödel theorem)
import these definitions. The split is forced: `ALT/*` files use the `import Mathlib` umbrella,
whose `Matrix.map` collides with `Foundation.Vorspiel.Matrix`'s root-namespace `Matrix.map`, so a
single file cannot import both Foundation and (umbrella-)Mathlib. Keeping the core Mathlib-free is
the clean bridge: the literal `GodelThreshold.Incompleteness` symbol lives here and is shared.

Status: PROVED as pure logic (`#print axioms` → standard axioms only).
-/

namespace GodelThreshold

universe u

variable {Sentence : Type u} (gnum : Sentence → ℕ) (Derivable True_ : Sentence → Prop)

/-- §5.3: a sentence is representable in the depth-`M` NNO `N_M` iff its Gödel number is within the
depth — i.e. it is one of the `M+1` orbit elements indexed `0…M` of D1's `ParamNNO`. -/
def Representable (M : ℕ) (s : Sentence) : Prop := gnum s ≤ M

/-- Def 6.1's operative consequence (§6): the subsystem contains a representable sentence that is
true in the standard model but not derivable in its internal logic. This is NOT the full
Definition 6.1 (CCC + NNO + `M > g(T_S)`) — see `ALT/Reflective.lean`. -/
def RepresentsUnderivableTruth (M : ℕ) : Prop :=
  ∃ s, Representable gnum M s ∧ True_ s ∧ ¬ Derivable s

/-- Gödel's first incompleteness theorem for `T_S` as an abstract statement: a sentence `G` with
Gödel number `gTS`, true in the standard model but not derivable. In D4 this was an imported
HYPOTHESIS; `ALT/GodelComplete.lean` discharges it from the Foundation port. -/
def Incompleteness (gTS : ℕ) : Prop := ∃ G, gnum G = gTS ∧ True_ G ∧ ¬ Derivable G

/-- The Gödel threshold (Prop 5.3 + Def 6.1): if the depth `M` reaches the Gödel number `gTS`
(`gTS ≤ M`, so `G` is representable in `N_M`) and incompleteness holds, then the subsystem
represents a true sentence it cannot derive. Pure logic — the value is the statement. -/
theorem godel_threshold (M gTS : ℕ) (hM : gTS ≤ M)
    (hInc : Incompleteness gnum Derivable True_ gTS) :
    RepresentsUnderivableTruth gnum Derivable True_ M := by
  obtain ⟨G, hgnum, htrue, hnd⟩ := hInc
  refine ⟨G, ?_, htrue, hnd⟩
  change gnum G ≤ M
  omega

end GodelThreshold
