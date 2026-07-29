/-
Copyright (c) 2026 Mykola Palamarchuk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mykola Palamarchuk
-/
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Fintype.Pi

set_option linter.style.header false
set_option linter.style.longLine false

/-!
# Exact window sufficiency forces eventual periodicity

Provenance: [SQ] §3.1, the window-sufficiency assumption (W) — "the window determines the next
observation" — taken in its EXACT (noiseless) form: `o_{t+1} = f(w_t)` for a fixed one-step
predictor `f` on a window of fixed length `k`.

## What is proved here

* `window` — the length-`k` observation window at time `t`.
* `WindowDeterministic` — (W) taken exactly: the window determines the next observation, for a
  fixed predictor `f`.
* `eq_of_window_eq` — two `WindowDeterministic` sequences that share a one-step predictor `f` and
  agree on their initial window are equal everywhere: the initial window determines the whole
  sequence.
* `exists_eventually_periodic` — over a FINITE observation alphabet, a `WindowDeterministic`
  sequence is eventually periodic, with pre-period and period together bounded by the number of
  possible windows `|X|^k`: a single trajectory visits only finitely many distinct windows, and
  once one repeats, window-determinism forces the sequence to repeat with it.

## What this does NOT establish

* Not any relaxation to window-noise (the `η`-budget of [SQ] §3.1, `η := P_μ(o_{t+1} ≠ f_R(w_t))`)
  or any claim about which invariant measure a resulting periodic orbit carries: this module treats
  the exact, noiseless predictor only.
* Not membership of any particular system in a substrate class: this is a structural fact about
  sequences obeying (W) exactly, independent of every other hypothesis.
-/

namespace WindowDeterminism

variable {X : Type*} [Fintype X] {k : ℕ}

/-- **The length-`k` observation window at time `t`** ([SQ] §3.1): `window o t j = o (t + j)` for
`j : Fin k`. -/
def window (o : ℕ → X) (t : ℕ) : Fin k → X := fun j => o (t + (j : ℕ))

/-- **Window sufficiency (W), taken exactly** ([SQ] §3.1): the window determines the next
observation, under a fixed one-step predictor `f`. -/
def WindowDeterministic (f : (Fin k → X) → X) (o : ℕ → X) : Prop :=
  ∀ t, o (t + k) = f (window o t)

omit [Fintype X] in
/-- **Determination by the initial window.** Two `WindowDeterministic` sequences sharing the same
predictor `f` and agreeing on their first `k` observations are equal everywhere: (W), taken
exactly, lets the initial window determine the whole trajectory. -/
theorem eq_of_window_eq (f : (Fin k → X) → X) {o o' : ℕ → X}
    (ho : WindowDeterministic f o) (ho' : WindowDeterministic f o')
    (h : ∀ j : Fin k, o (j : ℕ) = o' (j : ℕ)) :
    o = o' := by
  funext t
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    rcases lt_or_ge t k with htk | htk
    · exact h ⟨t, htk⟩
    · have hteq : t - k + k = t := Nat.sub_add_cancel htk
      have hwin : window (k := k) o (t - k) = window o' (t - k) := by
        funext j
        have hj := j.isLt
        change o (t - k + (j : ℕ)) = o' (t - k + (j : ℕ))
        exact ih (t - k + (j : ℕ)) (by omega)
      calc o t = o (t - k + k) := by rw [hteq]
        _ = f (window o (t - k)) := ho (t - k)
        _ = f (window o' (t - k)) := by rw [hwin]
        _ = o' (t - k + k) := (ho' (t - k)).symm
        _ = o' t := by rw [hteq]

omit [Fintype X] in
/-- **Window-equality propagates forward.** If two `WindowDeterministic` sequences (over the same
predictor `f`) have equal windows at times `n₁` and `n₂`, their windows stay equal `j` steps later,
for every `j`: the shared recurrence carries the coincidence forward. -/
private theorem window_eq_forward (f : (Fin k → X) → X) {o : ℕ → X}
    (ho : WindowDeterministic f o) {n₁ n₂ : ℕ}
    (heq : window (k := k) o n₁ = window o n₂) :
    ∀ j, window (k := k) o (n₁ + j) = window o (n₂ + j) := by
  intro j
  induction j with
  | zero => simpa using heq
  | succ j ih =>
    funext i
    have hi := i.isLt
    rcases lt_or_ge ((i : ℕ) + 1) k with hik | hik
    · change o (n₁ + (j + 1) + (i : ℕ)) = o (n₂ + (j + 1) + (i : ℕ))
      have e1 : n₁ + (j + 1) + (i : ℕ) = n₁ + j + ((⟨(i : ℕ) + 1, hik⟩ : Fin k) : ℕ) := by
        simp; omega
      have e2 : n₂ + (j + 1) + (i : ℕ) = n₂ + j + ((⟨(i : ℕ) + 1, hik⟩ : Fin k) : ℕ) := by
        simp; omega
      rw [e1, e2]
      exact congrFun ih ⟨(i : ℕ) + 1, hik⟩
    · have hik' : (i : ℕ) + 1 = k := by omega
      change o (n₁ + (j + 1) + (i : ℕ)) = o (n₂ + (j + 1) + (i : ℕ))
      have e1 : n₁ + (j + 1) + (i : ℕ) = n₁ + j + k := by omega
      have e2 : n₂ + (j + 1) + (i : ℕ) = n₂ + j + k := by omega
      rw [e1, e2, ho (n₁ + j), ho (n₂ + j), ih]

omit [Fintype X] in
/-- **Eventual periodicity from a repeated window.** If two `WindowDeterministic` (predictor `f`)
windows coincide at times `n₁ < n₂`, the sequence is periodic with period `n₂ − n₁` from time `n₁`
onward. -/
private theorem eventually_periodic_of_window_eq (f : (Fin k → X) → X) {o : ℕ → X}
    (ho : WindowDeterministic f o) (hk : 0 < k) {n₁ n₂ : ℕ} (hlt : n₁ < n₂)
    (heq : window (k := k) o n₁ = window o n₂) :
    0 < n₂ - n₁ ∧ ∀ t, n₁ ≤ t → o (t + (n₂ - n₁)) = o t := by
  refine ⟨by omega, fun t ht => ?_⟩
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le ht
  have hwin := window_eq_forward f ho heq j
  have := congrFun hwin ⟨0, hk⟩
  simp only [window] at this
  have e1 : n₁ + j + (n₂ - n₁) = n₂ + j := by omega
  rw [e1]
  simpa using this.symm

/-- **Eventual periodicity over a finite observation alphabet** ([SQ] §3.1's (W), exact form; the
structural half of the window-sufficiency story). A `WindowDeterministic` sequence over a finite
alphabet `X` visits only `Fintype.card (Fin k → X) = |X|^k` distinct windows, so by pigeonhole two
of the first `Fintype.card (Fin k → X) + 1` windows coincide; window-determinism then forces the
sequence to repeat from that point on, with pre-period and period together bounded by the number
of possible windows. -/
theorem exists_eventually_periodic (hk : 0 < k) (f : (Fin k → X) → X) {o : ℕ → X}
    (ho : WindowDeterministic f o) :
    ∃ m p, 0 < p ∧ m + p ≤ Fintype.card (Fin k → X) ∧ ∀ t, m ≤ t → o (t + p) = o t := by
  set N := Fintype.card (Fin k → X) with hN
  have hcard : Fintype.card (Fin k → X) < Fintype.card (Fin (N + 1)) := by
    rw [Fintype.card_fin]; omega
  obtain ⟨x, y, hxy, hfeq⟩ :=
    Fintype.exists_ne_map_eq_of_card_lt (fun i : Fin (N + 1) => window o (i : ℕ)) hcard
  have hxyval : (x : ℕ) ≠ (y : ℕ) := fun h => hxy (Fin.ext h)
  rcases lt_or_gt_of_ne hxyval with hlt | hgt
  · obtain ⟨hpos, hper⟩ := eventually_periodic_of_window_eq f ho hk hlt hfeq
    refine ⟨(x : ℕ), (y : ℕ) - (x : ℕ), hpos, ?_, hper⟩
    have hyle : (y : ℕ) ≤ N := Nat.lt_succ_iff.mp y.isLt
    omega
  · obtain ⟨hpos, hper⟩ := eventually_periodic_of_window_eq f ho hk hgt hfeq.symm
    refine ⟨(y : ℕ), (x : ℕ) - (y : ℕ), hpos, ?_, hper⟩
    have hxle : (x : ℕ) ≤ N := Nat.lt_succ_iff.mp x.isLt
    omega

/-- info: 'WindowDeterminism.eq_of_window_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms eq_of_window_eq

/-- info: 'WindowDeterminism.exists_eventually_periodic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms exists_eventually_periodic

end WindowDeterminism
