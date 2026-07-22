/-
Copyright (c) 2026 Mykola Palamarchuk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mykola Palamarchuk
-/
import ALT.GodelChecker

-- Formal-check file, not Mathlib-destined: opt out of the house-style linters.
set_option linter.style.header false
set_option linter.style.longLine false

/-!
# The reflective decision automaton over the concrete checker ([Decoupling] §6.5, the Level-2 witness)

Provenance: [Decoupling] §6.5 (Proposition 6.5). This is the concrete,
executable counterpart of the abstract decision automaton: it runs the very same two-cell machine
directly over the **executable** bounded proof-checker `GodelChecker.Prf Ax : Sentence ℒₒᵣ → ℕ → Bool`
of §6.3, so the §6.5 verdict is obtained for a **real** Gödel sentence of `𝗣𝗔⁻`.

Like `ALT/GodelChecker.lean`, the machine and its run are restated here directly against the
concrete checker rather than instantiating the abstract structure. The
**categorical** Decoupling statements (the code region is read-only; the decoder is faithful;
persistence via the Decoupling Lemma) stay on the Mathlib side; here we keep only the plain
read-only equation of the code cell and drive the run to the Gödel verdict.

## The machine
Cells indexed by `Bool` (`false` = code, `true` = work) over `S ⊕ (ℕ × Bool)`. One `step` fixes the
code cell (`step_readonly_code`) and advances the work cell by folding the checker over the next
proof code (`step`/`workNext`). After `M_chk + 1` steps the read-out Boolean is the conjunction of
`¬Prf(G, p)` over all `p ≤ M_chk` (`automaton_run`); at the `𝗣𝗔⁻` Gödel sentence this is `true`
(`paMinus_automaton_decides`), mirroring `GodelChecker.paMinus_decides_bounded_nonprovability`.
-/

namespace GodelCheckerAutomaton

open LO LO.Entailment LO.FirstOrder LO.FirstOrder.Arithmetic GodelChecker

/-- Cell alphabet: a code cell holds a sentence (`Sum.inl`), a work cell holds a step counter and
running verdict (`Sum.inr`). -/
abbrev AVal : Type := S ⊕ (ℕ × Bool)

/-- Machine state: the two-cell shared memory indexed by `Bool`. -/
abbrev AState : Type := Bool → AVal

/-- The work-cell update: on a well-formed configuration within budget, fold one more proof code of
the concrete checker `GodelChecker.Prf Ax` into the verdict. -/
def workNext (Ax : List S) (Mchk : ℕ) (code work : AVal) : AVal :=
  match code, work with
  | Sum.inl φ, Sum.inr (k, b) =>
      if k ≤ Mchk then Sum.inr (k + 1, b && !(GodelChecker.Prf Ax φ k)) else work
  | _, _ => work

/-- One machine step: the code cell (`false`) is always fixed; the work cell (`true`) advances by
`workNext`, reading the sentence off the code cell. -/
def step (Ax : List S) (Mchk : ℕ) (s : AState) : AState := fun
  | false => s false
  | true => workNext Ax Mchk (s false) (s true)

/-- Initial configuration for testing `φ`: code cell `Sum.inl φ`, work cell `Sum.inr (0, true)`. -/
def init (φ : S) : AState := fun
  | false => Sum.inl φ
  | true => Sum.inr (0, true)

/-- Read out the running verdict: the work cell's Boolean, or `false` on an ill-typed work cell. -/
def readout (s : AState) : Bool :=
  Sum.elim (fun _ => false) Prod.snd (s true)

/-- §3 (read-only code cell) on the concrete machine — the categorical Decoupling statements are on
the Mathlib side; here we keep only this plain equation. -/
theorem step_readonly_code (Ax : List S) (Mchk : ℕ) :
    ∀ s : AState, step Ax Mchk s false = s false := fun _ => rfl

/-- The code cell is fixed across all iterations (proved locally, without the Mathlib-side
Decoupling Lemma). -/
theorem code_fixed (Ax : List S) (Mchk : ℕ) (φ : S) :
    ∀ j, ((step Ax Mchk)^[j] (init φ)) false = Sum.inl φ := by
  intro j
  induction j with
  | zero => rfl
  | succ k ihk =>
    rw [Function.iterate_succ_apply']
    exact ihk

/-- One fold step of the running verdict — extending the search by the next proof code multiplies in
`!(P j)`. -/
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

/-- Run invariant: after `j ≤ M_chk + 1` steps from `init φ`, the work cell is
`Sum.inr (j, decide (∀ p < j, Prf Ax φ p = false))`. -/
theorem step_run_invariant (Ax : List S) (Mchk : ℕ) (φ : S) :
    ∀ j, j ≤ Mchk + 1 →
      ((step Ax Mchk)^[j] (init φ)) true
        = Sum.inr (j, decide (∀ p, p < j → GodelChecker.Prf Ax φ p = false)) := by
  intro j
  induction j with
  | zero =>
    intro _
    have hz : ((step Ax Mchk)^[0] (init φ)) true = Sum.inr (0, true) := rfl
    rw [hz]
    simp
  | succ j ih =>
    intro hj
    have hjm : j ≤ Mchk := by omega
    have hcode := code_fixed Ax Mchk φ j
    have hwork := ih (by omega)
    rw [Function.iterate_succ_apply']
    change workNext Ax Mchk (((step Ax Mchk)^[j] (init φ)) false) (((step Ax Mchk)^[j] (init φ)) true)
      = Sum.inr (j + 1, decide (∀ p, p < j + 1 → GodelChecker.Prf Ax φ p = false))
    rw [hcode, hwork]
    dsimp only [workNext]
    rw [if_pos hjm, decide_and_not (GodelChecker.Prf Ax φ) j]

/-- After `M_chk + 1` steps the read-out Boolean is the conjunction of `¬Prf(φ, p)` over the whole
bounded range `p ≤ M_chk` (§6.3's decision, concretely). -/
theorem automaton_run (Ax : List S) (Mchk : ℕ) (φ : S) :
    readout ((step Ax Mchk)^[Mchk + 1] (init φ))
      = decide (∀ p, p < Mchk + 1 → GodelChecker.Prf Ax φ p = false) := by
  have hinv := step_run_invariant Ax Mchk φ (Mchk + 1) (le_refl _)
  simp only [readout, hinv, Sum.elim_inr]

/-- **§6.5 Proposition 6.5 — the concrete `𝗣𝗔⁻` verdict.** For the executable sound checker over any
`𝗣𝗔⁻`-provable axiom list, the reflective automaton halts after `M_chk + 1` steps reading `true` on
the actual Gödel sentence `G` of `𝗣𝗔⁻` — true in the standard model, unprovable in `𝗣𝗔⁻`. Mirrors
`GodelChecker.paMinus_decides_bounded_nonprovability`, driven through the machine run. -/
theorem paMinus_automaton_decides (Ax : List S)
    (hAx : ∀ c ∈ Ax, (𝗣𝗔⁻ : ArithmeticTheory) ⊢ c) (Mchk : ℕ) :
    ∃ G : S, (ℕ↓[ℒₒᵣ] ⊧ G) ∧ ((𝗣𝗔⁻ : ArithmeticTheory) ⊬ G) ∧
      readout ((step Ax Mchk)^[Mchk + 1] (init G)) = true := by
  obtain ⟨G, htrue, hunprov, hbounded⟩ :=
    GodelChecker.paMinus_decides_bounded_nonprovability Ax hAx Mchk
  refine ⟨G, htrue, hunprov, ?_⟩
  rw [automaton_run Ax Mchk G, decide_eq_true_eq]
  intro p hp
  exact hbounded p (by omega)

end GodelCheckerAutomaton
