/-
Copyright (c) 2026 Mykola Palamarchuk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mykola Palamarchuk
-/
import ALT.Decoupling
import ALT.GodelInternalization
import ALT.ParameterizedNNO

-- Formal-check file, not Mathlib-destined: opt out of the house-style linters.
set_option linter.style.header false
set_option linter.style.longLine false

/-!
# The reflective decision automaton ([Decoupling] §6.5, Proposition 6.5, FV-19)

Provenance: [Decoupling] §6.5 (Proposition 6.5). This assembles the two
threads of §3 and §6 into ONE object: a shared-memory update `step` on a two-cell memory whose
**code cell is read-only** (so a decoded model persists — the Decoupling Lemma, §3) and whose
**work cell runs the bounded proof search** of §6.3 to decide bounded non-provability, producing
the §6 Gödel verdict on the true-but-underivable sentence.

## The machine
The memory has two cells, `false` (code) and `true` (work), over the alphabet
`Val C := C.Formula ⊕ (ℕ × Bool)`. The code cell holds `Sum.inl φ` (the sentence under test); the
work cell holds `Sum.inr (k, b)` — a step counter `k` and the running verdict `b`. One `step`:

* **always fixes the code cell** (`step_fixes_code`), so the read-out sentence never changes; and
* advances the work cell `Sum.inr (k, b) ↦ Sum.inr (k+1, b && !(Prf φ k))` while `k ≤ M_chk`,
  folding the checker `C.Prf φ ·` over the proof codes `0, 1, …, M_chk`.

## What this establishes
* `step_fixes_code` / `decodeCode_faithful` — §3 D1/D2 on this machine: the code region `{false}`
  is read-only and the decoder is faithful on it;
* `automaton_persists` — the decoded sentence survives every iteration, routed through the
  Decoupling Lemma (`Decoupling.model_persists`), not a bespoke re-proof;
* `automaton_run` — after `M_chk + 1` steps the read-out Boolean is exactly the §6.3 decision
  `GodelInternalization.Decide C φ` (an invariant induction: after `j` steps the work cell holds
  `Sum.inr (j, decide (∀ p < j, Prf φ p = false))`);
* `automaton_decides_godel` — combining the two, under imported incompleteness at `g` the automaton
  halts reading `true` on a sentence that is true in the standard model but underivable: the
  reflective subsystem **is a decision automaton** for the Gödel phenomenon of §6.

`GodelThreshold.Incompleteness` is the imported Gödel black box (§6.2), consumed only as a
hypothesis; the checker `C : GodelInternalization.BoundedChecker` is the abstract §6.3 interface,
discharged concretely on the Foundation side.
-/

namespace ReflectiveAutomaton

open GodelInternalization

variable (C : BoundedChecker)

/-- §6.5 cell alphabet: a code cell holds a `Formula` (`Sum.inl`), a work cell holds a step counter
and running verdict `(ℕ × Bool)` (`Sum.inr`). -/
abbrev Val (C : BoundedChecker) : Type := C.Formula ⊕ (ℕ × Bool)

/-- §6.5 machine state: the two-cell shared memory of §3 with cells indexed by `Bool`
(`false` = code cell, `true` = work cell). -/
abbrev State (C : BoundedChecker) : Type := Decoupling.Mem Bool (Val C)

/-- The work-cell update given the current code and work cells. On a well-formed configuration
(code `Sum.inl φ`, work `Sum.inr (k, b)`) with the counter within budget (`k ≤ M_chk`), it folds one
more proof code into the verdict: `Sum.inr (k+1, b && !(Prf φ k))`. Otherwise the work cell is left
unchanged. -/
def workNext (C : BoundedChecker) (code work : Val C) : Val C :=
  match code, work with
  | Sum.inl φ, Sum.inr (k, b) =>
      if k ≤ C.Mchk then Sum.inr (k + 1, b && !(C.Prf φ k)) else work
  | _, _ => work

/-- §6.5 one machine step: the code cell (`false`) is **always fixed**; the work cell (`true`)
advances by `workNext`, reading the sentence off the code cell. -/
def step (C : BoundedChecker) (s : State C) : State C := fun
  | false => s false
  | true => workNext C (s false) (s true)

/-- Initial configuration for testing `φ`: code cell `Sum.inl φ`, work cell `Sum.inr (0, true)`
(counter `0`, verdict `true`). -/
def init (C : BoundedChecker) (φ : C.Formula) : State C := fun
  | false => Sum.inl φ
  | true => Sum.inr (0, true)

/-- Read out the running verdict: the work cell's Boolean, or `false` on an ill-typed work cell. -/
def readout (C : BoundedChecker) (s : State C) : Bool :=
  Sum.elim (fun _ => false) Prod.snd (s true)

/-- Decode the code cell (§3's model read-out). -/
def decodeCode (C : BoundedChecker) (s : State C) : Val C := s false

/-! ### D1/D2 on the machine ([Decoupling] §3) -/

/-- §3 D1 — the code region `{false}` is **read-only** under `step`, by construction. -/
theorem step_fixes_code : Decoupling.Fixes (step C) ({false} : Set Bool) := by
  intro s a ha
  rw [Set.mem_singleton_iff] at ha
  subst ha
  rfl

/-- §3 D2 — the code decoder is **faithful** on `{false}`: equal decode ⟺ agreement on the code
region. -/
theorem decodeCode_faithful : Decoupling.Faithful (decodeCode C) ({false} : Set Bool) := by
  intro s t
  constructor
  · intro h a ha
    rw [Set.mem_singleton_iff] at ha
    subst ha
    exact h
  · intro h
    exact h false (Set.mem_singleton_iff.mpr rfl)

/-- The code decoder is **non-constant**: distinct configurations decode differently (a faithful,
non-degenerate model — §3). -/
theorem decodeCode_nonconstant : ∃ s t : State C, decodeCode C s ≠ decodeCode C t :=
  ⟨fun _ => Sum.inr (0, true), fun _ => Sum.inr (0, false), by simp [decodeCode]⟩

/-- §3 (Lemma 3.1, sufficiency) on the machine — the decoded sentence **persists across every
iteration**, obtained through the Decoupling Lemma (`Decoupling.model_persists`) from
`step_fixes_code` and faithfulness, not a bespoke re-proof. -/
theorem automaton_persists : ∀ k s, decodeCode C ((step C)^[k] s) = decodeCode C s :=
  Decoupling.model_persists (step_fixes_code C) (decodeCode_faithful C).dependsOn

/-! ### The run ([Decoupling] §6.5 / §6.3) -/

/-- One fold step of the running verdict: extending the search by the next proof code multiplies in
`!(P j)`, i.e. `decide (∀ p < j, P p = false) && !(P j) = decide (∀ p < j+1, P p = false)`. -/
theorem decide_and_not (P : ℕ → Bool) (j : ℕ) :
    (decide (∀ p, p < j → P p = false) && !(P j))
      = decide (∀ p, p < j + 1 → P p = false) := by
  cases hj : P j with
  | false =>
    simp only [Bool.not_false, Bool.and_true]
    apply decide_eq_decide.mpr
    constructor
    · intro h p hp
      by_cases hpj : p = j
      · subst hpj; exact hj
      · exact h p (by omega)
    · intro h p hp; exact h p (by omega)
  | true =>
    simp only [Bool.not_true, Bool.and_false]
    symm
    rw [decide_eq_false_iff_not]
    intro h
    have hjf := h j (by omega)
    rw [hj] at hjf
    exact absurd hjf (by decide)

/-- **Run invariant** ([Decoupling] §6.5): after `j ≤ M_chk + 1` steps from `init C φ`, the work cell is
`Sum.inr (j, decide (∀ p < j, Prf φ p = false))` — the counter is `j` and the verdict is the partial
conjunction over the first `j` proof codes. -/
theorem step_run_invariant (φ : C.Formula) :
    ∀ j, j ≤ C.Mchk + 1 →
      ((step C)^[j] (init C φ)) true
        = Sum.inr (j, decide (∀ p, p < j → C.Prf φ p = false)) := by
  intro j
  induction j with
  | zero =>
    intro _
    have hz : ((step C)^[0] (init C φ)) true = Sum.inr (0, true) := rfl
    rw [hz]
    simp
  | succ j ih =>
    intro hj
    have hjm : j ≤ C.Mchk := by omega
    have hcode : ((step C)^[j] (init C φ)) false = Sum.inl φ :=
      Decoupling.fixes_iterate (step_fixes_code C) j (init C φ) false
        (Set.mem_singleton_iff.mpr rfl)
    have hwork := ih (by omega)
    rw [Function.iterate_succ_apply']
    change workNext C (((step C)^[j] (init C φ)) false) (((step C)^[j] (init C φ)) true)
      = Sum.inr (j + 1, decide (∀ p, p < j + 1 → C.Prf φ p = false))
    rw [hcode, hwork]
    dsimp only [workNext]
    rw [if_pos hjm, decide_and_not (C.Prf φ) j]

/-- **§6.5, Proposition 6.5 (the run).** After `M_chk + 1` steps the read-out Boolean is exactly the
§6.3 bounded-non-provability decision `GodelInternalization.Decide C φ`. -/
theorem automaton_run (φ : C.Formula) :
    readout C ((step C)^[C.Mchk + 1] (init C φ)) = Decide C φ := by
  have hinv := step_run_invariant C φ (C.Mchk + 1) (le_refl _)
  have hro : readout C ((step C)^[C.Mchk + 1] (init C φ))
      = decide (∀ p, p < C.Mchk + 1 → C.Prf φ p = false) := by
    simp only [readout, hinv, Sum.elim_inr]
  rw [hro]
  unfold Decide
  apply decide_eq_decide.mpr
  constructor
  · intro hA p; exact hA p.val (Nat.lt_succ_of_le p.2)
  · intro hB p hp; exact hB ⟨p, by omega⟩

/-- **§6.5, Proposition 6.5 (the verdict).** Under imported incompleteness at `g` (§6.2), the
reflective automaton halts after `M_chk + 1` steps reading `true` on a sentence `G` that is true in
the standard model and underivable in the internal logic: representational reflection **is a
decision automaton** for the §6 Gödel phenomenon. -/
theorem automaton_decides_godel (True_ : C.Formula → Prop) (g : ℕ)
    (hInc : GodelThreshold.Incompleteness C.gnum C.Derivable True_ g) :
    ∃ G, C.gnum G = g ∧ True_ G ∧
      readout C ((step C)^[C.Mchk + 1] (init C G)) = true := by
  obtain ⟨G, hgnum, htrue, hdec⟩ := decide_godel C True_ g hInc
  refine ⟨G, hgnum, htrue, ?_⟩
  rw [automaton_run C G]
  exact hdec

end ReflectiveAutomaton
