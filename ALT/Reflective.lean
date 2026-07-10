/-
Copyright (c) 2026 Mykola Palamarchuk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mykola Palamarchuk
-/
import Mathlib
import ALT.CartesianClosed
import ALT.ParameterizedNNO
import ALT.GodelThreshold

-- Formal-check file, not Mathlib-destined: opt out of the house-style header linter.
set_option linter.style.header false

/-!
# Full representational reflection assembly (Paper I §6, capstone of D1 ∧ D2 ∧ D4)

Provenance: Paper I, §6 (Definition 6.1 representational
reflection, Theorem 6.2, and the closing "Consequence"). Ties together the three skeleton
components:
D2 (`ALT/CartesianClosed.lean`, CCC), D1 (`ALT/ParameterizedNNO.lean`, the parameterized NNO
+ depth), D4 (`ALT/GodelThreshold.lean`, the Gödel threshold).

Status: PROVED. Completes the Paper I chain at the SKELETON level — the faithful Def-6.1 assembly
plus the §6 Consequence composing through it.
Superseded as the genuine carrier by `RealizabilityRecursor.lean` (CCC ∧ recursor unified on ONE
object, FV-13) and `CategoricalThreshold.lean` (Theorem 6.2 on that carrier, FV-15); retained as
the guarded D1 ∧ D2 ∧ D4 skeleton capstone.

## Stand-in mismatch (read this — the CCC and the NNO are on SEPARATE stand-ins)
Definition 6.1 wants ONE object `Rep(S)` that is a CCC AND contains the NNO. Our components live on
DIFFERENT stand-ins: D2's CCC is on `Type` (`MonoidalClosed Type`), while D1's NNO is a
combinatorial `ParamNNO` on a *finite* type `W`. They are NOT a single unified `Rep(S)` object. So
`Reflective` below BUNDLES the three Def-6.1 ingredients on their respective stand-ins — it is NOT a
proof that one constructed `Rep(S)` is reflective.

## Finding: the CCC conjunct is off the critical path (cf. B4)
The §6 Consequence (`reflective_representsUnderivableTruth`) flows through the **NNO depth + Gödel
incompleteness** only; the CCC conjunct (`Nonempty (MonoidalClosed Type)`) is destructured as
`_hCCC` and never used. It is carried for Definition-6.1 faithfulness but is OFF the critical path
to this consequence — exactly as B4 found SQ-learnability off-path to bare representational
reflection. Moreover,
on the `Type` stand-in `Nonempty (MonoidalClosed Type)` is trivially true (`Type` is always
cartesian closed), so here the conjunct is structurally-present-but-content-light — another honest
face of the stand-in mismatch. For a real `Rep(S)` it would be the substantive Proposition 4.3.

## What this DOES establish
* `Reflective gTS`: Definition 6.1 assembled — `Nonempty (MonoidalClosed Type)` (D2's CCC stand-in)
  AND a parameterized NNO (D1) of depth `> gTS` on some finite `W`.
* `reflective_representsUnderivableTruth`: the §6 Consequence — `Reflective` + `Incompleteness` ⟹
  the subsystem represents a true-but-underivable sentence (at its NNO depth), via D4's
  `reflective_of_depth`.
* `reflective_satisfiable`: the bundle is satisfiable on the stand-ins for every `gTS`
  (non-vacuity).

## What this does NOT establish (flagged)
* The stand-in mismatch: CCC on `Type` (D2), NNO on finite `W` (D1) — two separate stand-ins, NOT
  one unified `Rep(S)`. Not a proof that a constructed `Rep(S)` is reflective.
* Incompleteness is still imported (`GodelThreshold.Incompleteness` hypothesis) — discharged later
  by the `FormalizedFormalLogic/Foundation` port (the Plan's "one PORT").
* No physical / `Rep(S)` realization: no `s_code`/`s_work`, no Decoupling Lemma, no Theorem 6.2
  (`K > g(r,δ)` ⟹ reflective via a real subsystem); `gnum`/`Derivable`/`True_`/`Sentence` abstract.
* The CCC conjunct is required by Def 6.1 and carried in `Reflective`, but the consequence flows
  through the NNO + Gödel — CCC is off the critical path (cf. B4).
* `reflective_satisfiable` is non-vacuity on the stand-ins, not a claim that every subsystem is
  reflective.

## Hypotheses: paper-stated vs added
* Paper-stated / faithful: Def 6.1 as CCC ∧ NNO-depth `> g(T_S)`; the §6 Consequence; §5.3
  satisfiability.
* Added / modeling: the CCC and NNO on separate stand-ins (not unified `Rep(S)`);
  `Sentence`/`gnum`/`Derivable`/`True_` abstract; incompleteness imported.
-/

namespace ReflectiveAssembly

open CategoryTheory MonoidalClosed

/-- Definition 6.1 (assembled on stand-ins): a subsystem with internal-theory Gödel number `gTS`
is reflective iff (i) its representation category is Cartesian closed — D2's `Type` stand-in — and
(ii) it contains a parameterized NNO (D1) of depth `M > g(T_S)`. The CCC (on `Type`) and the NNO
(on a finite `W`) are SEPARATE stand-ins, not one unified `Rep(S)` — see the module note. -/
def Reflective (gTS : ℕ) : Prop :=
  Nonempty (MonoidalClosed Type) ∧
    ∃ (W : Type) (inst : Fintype W) (P : @ParameterizedNNO.ParamNNO W inst), gTS < P.depth

/-- §6 **Consequence** (the capstone): a reflective subsystem, under incompleteness for its theory,
represents a sentence true-but-underivable in its internal logic — at its NNO depth. The NNO-depth
conjunct supplies the threshold via D4's `reflective_of_depth`; the CCC conjunct `_hCCC` is carried
for Def-6.1 faithfulness but is OFF the critical path to this consequence (cf. B4). -/
theorem reflective_representsUnderivableTruth
    {Sentence : Type*} (gnum : Sentence → ℕ) (Derivable True_ : Sentence → Prop) (gTS : ℕ)
    (hMA : Reflective gTS)
    (hInc : GodelThreshold.Incompleteness gnum Derivable True_ gTS) :
    ∃ M, GodelThreshold.RepresentsUnderivableTruth gnum Derivable True_ M := by
  obtain ⟨_hCCC, W, instW, P, hdepth⟩ := hMA
  exact ⟨P.depth,
    @GodelThreshold.reflective_of_depth Sentence gnum Derivable True_ W instW P gTS hdepth hInc⟩

/-- The Def-6.1 bundle is satisfiable on the stand-ins for every `gTS` (non-vacuity): `Type` is a
CCC (D2's `repS_cartesianClosed`), and `cyclicParamNNO` (D1) gives a depth-`(gTS+1)` NNO, which
exceeds `gTS`. This shows the capstone is not vacuous — NOT that every subsystem is reflective
(that needs a real `Rep(S)`). -/
theorem reflective_satisfiable (gTS : ℕ) : Reflective gTS :=
  ⟨RepSCCC.repS_cartesianClosed, ZMod (gTS + 2), inferInstance,
    ParameterizedNNO.cyclicParamNNO (gTS + 1), Nat.lt_succ_self gTS⟩

end ReflectiveAssembly
