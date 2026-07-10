/-
Copyright (c) 2026 Mykola Palamarchuk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mykola Palamarchuk
-/
import Mathlib
import ALT.GodelCore
import ALT.ParameterizedNNO

-- Formal-check file, not Mathlib-destined: opt out of the house-style header linter.
set_option linter.style.header false

/-!
# Gödel threshold skeleton (Paper I §5.3 + §6)

Provenance: Paper I, §5.3 (Proposition 5.3, the Gödel depth
condition) and §6 (Definition 6.1 representational reflection, Theorem 6.2 categorical threshold).
Pure propositional/predicate logic, in the spirit of B4 (`ALT/ProofChainSkeleton.lean`).

The abstract predicates and the threshold lemma now live in the Mathlib-free `ALT/GodelCore.lean`
(`GodelThreshold.Representable`, `…RepresentsUnderivableTruth`, `…Incompleteness`,
`…godel_threshold`) — so the Foundation side (`ALT/GodelComplete.lean`) can import and discharge
the *literal* `GodelThreshold.Incompleteness` symbol without the `import Mathlib`/Foundation
`Matrix.map` collision. This file adds the part that genuinely needs Mathlib: the D1-NNO–tied
`reflective_of_depth`.

Status: PROVED as pure logic. The incompleteness theorem itself is an imported HYPOTHESIS in the
threshold lemma; it is discharged from the Foundation port in `ALT/GodelComplete.lean`.

## What this DOES establish
* `reflective_of_depth`: the Theorem 6.2 form, tied to D1 — a subsystem whose parameterized NNO
  (`ParameterizedNNO.ParamNNO`) has depth strictly exceeding `gTS` (exactly Def 6.1's `M > g(T_S)`),
  under incompleteness, represents-an-underivable-truth.

(For `Representable`/`RepresentsUnderivableTruth`/`Incompleteness`/`godel_threshold`, see
`ALT/GodelCore.lean`.)

## What this does NOT establish (flagged / other steps)
* Does NOT prove Gödel incompleteness — imported as the `GodelCore` `Incompleteness` hypothesis;
  discharged in `ALT/GodelComplete.lean` via the `FormalizedFormalLogic/Foundation` port.
* NOT the arithmetization / Gödel numbering (`gnum` abstract); NOT the theory `T_S` (`Q` plus
  `Δ₀`-induction); NOT `Rep(S)`, the CCC (D2), or the parameterized-NNO *existence* (D1).
* NOT the full Def 6.1 conjunction (CCC + NNO + `M > g(T_S)`) — only its representable-but-
  underivable-truth core (see `ALT/Reflective.lean`).
* No physical or mathematical content; pure threshold logic.

## Hypotheses: paper-stated vs added
* Paper-stated / faithful: Prop 5.3 (representable when depth exceeds `g(T_S)`); Def 6.1's operative
  consequence; incompleteness yields a true underivable `G`.
* Added / modeling: `Sentence`/`gnum`/`Derivable`/`True_` abstract; `reflective_of_depth` uses
  Def 6.1's strict `gTS < M`.
-/

namespace GodelThreshold

variable {Sentence : Type*} (gnum : Sentence → ℕ) (Derivable True_ : Sentence → Prop)

/-- Theorem 6.2 form, tied to D1: a subsystem whose parameterized NNO has depth strictly exceeding
the Gödel number (`g(T_S) < M`, exactly Def 6.1's `M > g(T_S)`), under incompleteness, represents
an underivable truth. `P.depth` is the depth `M` of `ParameterizedNNO.ParamNNO`. -/
theorem reflective_of_depth {W : Type*} [Fintype W]
    (P : ParameterizedNNO.ParamNNO W) (gTS : ℕ) (hM : gTS < P.depth)
    (hInc : Incompleteness gnum Derivable True_ gTS) :
    RepresentsUnderivableTruth gnum Derivable True_ P.depth :=
  godel_threshold gnum Derivable True_ P.depth gTS (le_of_lt hM) hInc

end GodelThreshold
