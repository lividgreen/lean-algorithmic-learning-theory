/-
Copyright (c) 2026 Mykola Palamarchuk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mykola Palamarchuk
-/
import Mathlib
import ALT.ParameterizedNNO

-- Formal-check file, not Mathlib-destined: opt out of the house-style header linter.
set_option linter.style.header false

/-!
# A second concrete `learner → CCC/NNO` instance: the modular counter

Provenance: [Decoupling], §4 (Rep(S) as a CCC), §4.4 (the Rule-30
cellular-automaton worked example), §4.5 / Conjecture 4.4 (the general functor
`DecoupledLearner → CCC_NNO` is OPEN). This file is a supporting win toward it: a SECOND concrete
decoupled-learner instance beyond Rule-30 — the modular counter (state `ZMod (n+1)`, update =
successor) — exhibiting its rules-as-data object, its iteration, its finiteness, and the fact that
its iterated-successor dynamics realize the cyclic parameterized NNO already built in D1
(`ALT/ParameterizedNNO.lean`).

Status: PROVED as concrete `ZMod` arithmetic. A supporting instance, not the functor.

## What this DOES establish
* `State`/`step`/`Rules`/`stepAsData`/`applyRule`: a concrete decoupled learner — state
  `ZMod (n+1)`, update = successor, the update held as a first-class datum (§4.5 functions-as-data).
* `apply_stepAsData`: the learner applies its own rule-as-data.
* `step_iterate`: multi-step prediction by iterating the rule-as-data advances the counter by `k`.
* `rules_card`: the rules-as-data object is finite, with `(n+1)^(n+1)` elements (§4.4 concretely).
* `step_eq_nno_succ` + `nno_orbit`: the counter's successor IS the successor of D1's
  `cyclicParamNNO (n+1)`, and its iterated dynamics realize that NNO's orbit
  (`succ^[k] zero = k`) — so the D1 parameterized NNO represents this iterating learner.

## What this does NOT establish (flagged)
* INSTANCE, not the functor. A second concrete instance (the modular counter) beyond Rule-30 — it
  demonstrates generality; Conjecture 4.4 (the general `DecoupledLearner → CCC_NNO` functor) remains
  OPEN.
* The representation category is still the `Type` stand-in (D2, `RepSCCC.repS_cartesianClosed`), NOT
  a bespoke per-learner `Rep(S)`. `Rules n = State n → State n` is its (Type-level) exponential
  object; D2 exhibits the abstract exponential's universal property
  (`expCurrying`/`functionsAsData`) and its finiteness (`exp_finite`). This file CROSS-REFERENCES D2
  in prose rather than re-deriving the categorical exponential (Mathlib's `ihom` object is abstract,
  not defeq to `→` — see D2).
* "Decoupled" is modeled minimally here (the rule `step` held as a separate datum `stepAsData`
  applied to state), NOT the full D1–D4 decoupling of [Decoupling] §3.
* Reuses `cyclicParamNNO` (D1) and (in prose) the `Type` CCC (D2); proves NO new categorical
  machinery.

## Hypotheses: paper-stated vs added
* Paper-stated / faithful: §4.5 functions-as-data (rules held as a first-class object), §4.4
  finiteness, the parameterized NNO as the representation of an iterating learner.
* Added / modeling: the concrete modular-counter instance (`ZMod (n+1)`, successor); the `Type` CCC
  stand-in (D2) as the ambient category.
-/

namespace CounterLearner

open ParameterizedNNO

/-- A concrete decoupled learner (second instance, distinct from the Rule-30 CA): state =
`ZMod (n+1)`, one-step update = successor (a modular counter). -/
abbrev State (n : ℕ) : Type := ZMod (n + 1)

/-- The one-step update: advance the counter by one. -/
def step (n : ℕ) : State n → State n := fun s => s + 1

/-- The functions-as-data object: this learner's one-step update rules ([Decoupling] §4.5).
This is the `Type`-level exponential `State n ⇒ State n` of the D2 CCC stand-in. -/
abbrev Rules (n : ℕ) : Type := State n → State n

/-- The update rule held as a first-class datum. -/
def stepAsData (n : ℕ) : Rules n := step n

/-- Applying a rule-as-data to a state. -/
def applyRule (n : ℕ) (f : Rules n) (s : State n) : State n := f s

/-- The learner applies its own rule-as-data (functions-as-data, §4.5). -/
theorem apply_stepAsData (n : ℕ) (s : State n) : applyRule n (stepAsData n) s = s + 1 := rfl

/-- Multi-step prediction by iterating the rule-as-data: `k` steps advance the counter by `k`. -/
theorem step_iterate (n k : ℕ) (s : State n) : (step n)^[k] s = s + (k : State n) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih]
    simp only [step]
    push_cast
    ring

/-- The functions-as-data object is finite ([Decoupling] §4.4 `exp_finite`, concretely). -/
instance (n : ℕ) : Fintype (Rules n) := inferInstance

/-- Its cardinality: `(n+1)^(n+1)` one-step rules over a state space of `n+1` configurations. -/
theorem rules_card (n : ℕ) : Fintype.card (Rules n) = (n + 1) ^ (n + 1) := by
  simp only [Rules, State, Fintype.card_fun, ZMod.card]

/-- NNO tie (the centerpiece): the counter's successor step IS the successor map of D1's
`cyclicParamNNO n` on `ZMod (n+1)`. -/
theorem step_eq_nno_succ (n : ℕ) : step n = (cyclicParamNNO n).succ := rfl

/-- The counter's iterated-successor dynamics realize the parameterized NNO's orbit (D1): the
`k`-th iterate of `succ` from `zero` is `k`. (Depth `(cyclicParamNNO n).depth = n`, so the orbit
`zero, …, succ^n zero` is the full `(n+1)`-cycle of `State n`.) -/
theorem nno_orbit (n k : ℕ) :
    (cyclicParamNNO n).succ^[k] (cyclicParamNNO n).zero = (k : State n) := by
  rw [← step_eq_nno_succ]
  change (step n)^[k] (0 : State n) = (k : State n)
  rw [step_iterate]
  simp

end CounterLearner
