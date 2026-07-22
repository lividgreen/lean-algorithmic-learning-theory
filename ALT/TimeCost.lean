/-
Copyright (c) 2026 Mykola Palamarchuk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mykola Palamarchuk
-/
import Mathlib

-- Formal-check file, not Mathlib-destined: opt out of the house-style linters.
set_option linter.style.header false
set_option linter.style.longLine false

/-!
# A native sequential-time cost on the rfind'-free fragment of `Nat.Partrec.Code`

The root of the native cost model. Companion to `ALT/Collector.lean`, whose
`prop_2_2_t_exists` is the honest ∃-budget fallback forced by the `evaln` value-cap wall; this file
supplies the magnitude-INDEPENDENT step count that discharges that wall for the collector.

## The wall this routes around
Mathlib's clocked evaluator `Nat.Partrec.Code.evaln : ℕ → Code → ℕ → Option ℕ` caps intermediate
VALUES (`evaln_bound : x ∈ evaln k c n → n < k`), so its fuel `k` is a value ceiling, not a faithful
sequential-time measure: the `collector` runs in linearly-many `prec` unfoldings, yet its accumulator
`orbitAcc rs n` grows super-exponentially, so NO polynomial `evaln` budget exists. We want a cost that
charges each `prec`/`comp` unfolding `O(1)` regardless of the magnitude of the values flowing through.

## The vehicle — a total paired evaluator `evalT : Code → ℕ → ℕ × ℕ`
`evalT c n = (value, cost)` mirrors `Code.eval` node-for-node (so the value component reconstructs
`eval` on the fragment — `eval_eq_val`), while the second component counts one unit per constructor
unfolding. It is a TOTAL structural recursion on `Code` (the `prec` numeric recursion is `Nat.rec`, not
a recursive `evalT` call), so the step laws hold UNCONDITIONALLY — no `Part.Dom` side goals. The value
it computes carries no cap: `eval c n = Part.some (val c n)` for rfind'-free `c`.

## Scope
Only the rfind'-free fragment (`zero succ left right pair comp prec`), on which `eval` is total.
`rfind'` is a placeholder `(0, 0)` — OUT of the fragment; value-agreement is stated only for
`RfindFree c`; the search accounts live in `ALT/SearchCost.lean` / `ALT/SearchSpace.lean`. The
collector payoff (`tc_prec_le`) needs
no value-agreement at all: it is pure step-law bookkeeping, and the per-call rule cost enters as a
uniform bound `hcg`, which is exactly why the resulting linear bound is value-magnitude-independent.
-/

namespace TimeCost

open Nat.Partrec (Code)
open Nat.Partrec.Code

/-! ## The paired evaluator, and the value / cost projections -/

/-- **The paired evaluator.** `evalT c n = (value, cost)`, mirroring `Code.eval` node-for-node and
charging one step per constructor unfolding. Total structural recursion on `Code`: the `prec` numeric
recursion is `Nat.rec` (the recursive `evalT` calls are on the structural subterms `cf`, `cg`), so no
partiality and no well-founded recursion. `rfind'` is a placeholder (out of fragment). -/
def evalT : Code → ℕ → ℕ × ℕ
  | zero => fun _ => (0, 1)
  | succ => fun n => (n + 1, 1)
  | left => fun n => (n.unpair.1, 1)
  | right => fun n => (n.unpair.2, 1)
  | pair cf cg => fun n =>
      (Nat.pair (evalT cf n).1 (evalT cg n).1, (evalT cf n).2 + (evalT cg n).2 + 1)
  | comp cf cg => fun n =>
      ((evalT cf (evalT cg n).1).1, (evalT cg n).2 + (evalT cf (evalT cg n).1).2 + 1)
  | prec cf cg =>
      Nat.unpaired fun a n =>
        n.rec ((evalT cf a).1, (evalT cf a).2 + 1)
          (fun y IH =>
            ((evalT cg (Nat.pair a (Nat.pair y IH.1))).1,
              IH.2 + (evalT cg (Nat.pair a (Nat.pair y IH.1))).2 + 1))
  | rfind' _ => fun _ => (0, 0)

/-- The value component of `evalT` (equals `eval` on the fragment — see `eval_eq_val`). -/
def val (c : Code) (n : ℕ) : ℕ := (evalT c n).1

/-- The native sequential-time cost: the step count of `evalT`. -/
def tc (c : Code) (n : ℕ) : ℕ := (evalT c n).2

/-! ## Step laws — all UNCONDITIONAL (no `Part.Dom` side goals) -/

@[simp] theorem tc_zero (n : ℕ) : tc zero n = 1 := rfl
@[simp] theorem tc_succ (n : ℕ) : tc succ n = 1 := rfl
@[simp] theorem tc_left (n : ℕ) : tc left n = 1 := rfl
@[simp] theorem tc_right (n : ℕ) : tc right n = 1 := rfl

theorem tc_pair (f g : Code) (n : ℕ) : tc (pair f g) n = tc f n + tc g n + 1 := rfl

/-- The `comp` step law: `g` runs on `n`, then `f` runs on `g`'s VALUE. -/
theorem tc_comp (f g : Code) (n : ℕ) : tc (comp f g) n = tc g n + tc f (val g n) + 1 := rfl

theorem val_pair (f g : Code) (n : ℕ) : val (pair f g) n = Nat.pair (val f n) (val g n) := rfl
theorem val_comp (f g : Code) (n : ℕ) : val (comp f g) n = val f (val g n) := rfl

theorem tc_prec_zero (cf cg : Code) (a : ℕ) : tc (prec cf cg) (Nat.pair a 0) = tc cf a + 1 := by
  simp only [tc, evalT, Nat.unpaired, Nat.unpair_pair, Nat.rec_zero]

theorem val_prec_zero (cf cg : Code) (a : ℕ) : val (prec cf cg) (Nat.pair a 0) = val cf a := by
  simp only [val, evalT, Nat.unpaired, Nat.unpair_pair, Nat.rec_zero]

theorem tc_prec_succ (cf cg : Code) (a m : ℕ) :
    tc (prec cf cg) (Nat.pair a (m + 1)) =
      tc (prec cf cg) (Nat.pair a m)
        + tc cg (Nat.pair a (Nat.pair m (val (prec cf cg) (Nat.pair a m)))) + 1 := by
  simp only [tc, val, evalT, Nat.unpaired, Nat.unpair_pair]

theorem val_prec_succ (cf cg : Code) (a m : ℕ) :
    val (prec cf cg) (Nat.pair a (m + 1)) =
      val cg (Nat.pair a (Nat.pair m (val (prec cf cg) (Nat.pair a m)))) := by
  simp only [val, evalT, Nat.unpaired, Nat.unpair_pair]

/-! ## Value-agreement: the cost carries NO value cap -/

/-- The rfind'-free fragment: `eval` is total here and `evalT` faithfully reconstructs it. -/
def RfindFree : Code → Prop
  | zero | succ | left | right => True
  | pair cf cg | comp cf cg | prec cf cg => RfindFree cf ∧ RfindFree cg
  | rfind' _ => False

/-- **Value-agreement.** On the rfind'-free fragment the value component of `evalT` is exactly `eval`:
`eval c n = Part.some (val c n)`. So the cost `tc` is charged along the GENUINE computation — the
value flowing through is the true `eval` value, uncapped (contrast `evaln`'s value ceiling). -/
theorem eval_eq_val : ∀ {c : Code}, RfindFree c → ∀ n, eval c n = Part.some (val c n) := by
  intro c
  induction c with
  | zero => intro _ n; rfl
  | succ => intro _ n; rfl
  | left => intro _ n; rfl
  | right => intro _ n; rfl
  | pair cf cg ihf ihg =>
      intro hc n
      obtain ⟨hf, hg⟩ := hc
      simp only [eval]
      rw [ihf hf n, ihg hg n, val_pair]
      simp [Seq.seq]
  | comp cf cg ihf ihg =>
      intro hc n
      obtain ⟨hf, hg⟩ := hc
      simp only [eval]
      rw [ihg hg n, Part.bind_eq_bind, Part.bind_some, ihf hf (val cg n), val_comp]
  | prec cf cg ihf ihg =>
      intro hc n
      obtain ⟨hf, hg⟩ := hc
      obtain ⟨a, m, rfl⟩ : ∃ a m, n = Nat.pair a m :=
        ⟨n.unpair.1, n.unpair.2, (Nat.pair_unpair n).symm⟩
      induction m with
      | zero => rw [eval_prec_zero, ihf hf a, val_prec_zero]
      | succ k ihm =>
          rw [eval_prec_succ, ihm, Part.bind_eq_bind, Part.bind_some, ihg hg _, val_prec_succ]
  | rfind' cf _ => intro hc; exact hc.elim

/-! ## The collector payoff — a magnitude-INDEPENDENT linear bound for `prec`

The generic engine: if the step code `cg` costs at most `B` on EVERY input (a uniform bound), then
`prec cf cg` on `Nat.pair a n` costs at most `tc cf a + (B+1)·n + 1` — LINEAR in the number of
iterations `n`, with NO dependence on the intermediate accumulator values `val (prec cf cg) (…)`.
This is the whole contrast with `evaln`: `B` bounds one step regardless of how large the value
threaded through it is, so the total never sees the super-exponential accumulator. -/
theorem tc_prec_le {cf cg : Code} {B : ℕ} (hcg : ∀ x, tc cg x ≤ B) (a n : ℕ) :
    tc (prec cf cg) (Nat.pair a n) ≤ tc cf a + (B + 1) * n + 1 := by
  induction n with
  | zero => rw [tc_prec_zero]; omega
  | succ m ih =>
      rw [tc_prec_succ, Nat.mul_succ]
      have hb := hcg (Nat.pair a (Nat.pair m (val (prec cf cg) (Nat.pair a m))))
      omega

/-! ## A native SPACE cost: the maximum intermediate bitlength

`spaceCost c n` tracks the largest `Nat.size` (bitlength) of any value appearing as an argument or a
result of a constructor unfolding of `c` on input `n` — a native *workspace* measure, the space
companion to `tc`. It is charged along the SAME values `evalT` computes (`val`), so on the rfind'-free
fragment it measures space along the genuine `eval` computation (`eval_eq_val`).

The accounting, node by node:
* a base node (`zero`/`succ`/`left`/`right`) holds its input and its output — the `max` of their
  bitlengths;
* `pair cf cg` — the two sub-workspaces, joined with the bitlength of the paired result it forms;
* `comp cf cg` — `cg`'s workspace, then `cf`'s workspace on `cg`'s VALUE (whose bitlength is already
  inside `cf`'s I/O accounting, so it needs no separate term);
* `prec cf cg` — `Nat.rec` exactly as `evalT`: base `spaceCost cf a`; each step `max`es the running
  workspace with `cg`'s workspace on `⟨a, ⟨y, accumulator⟩⟩`, the accumulator's bitlength charged
  inside that `cg` I/O account.

The contrast worth naming: `tc` and the values themselves can be astronomically large (`tc` is
`Θ(value)`; an accumulator can grow super-exponentially), yet `spaceCost` — the bitlength of the values
a bounded checker actually holds — can stay polynomial. `spaceCost_prec_le` is that statement for the
loop: a per-step workspace bound `S` together with an accumulator-bitlength bound `S` caps the whole
`prec` at `max (spaceCost cf a) S`, with NO growth in the iteration count `n` (a `max`, not the `tc`
sum). `rfind'` is the placeholder `0` (out of fragment), keeping the parallel with `tc`. -/
def spaceCost : Code → ℕ → ℕ
  | zero => fun n => max (Nat.size n) (Nat.size 0)
  | succ => fun n => max (Nat.size n) (Nat.size (n + 1))
  | left => fun n => max (Nat.size n) (Nat.size n.unpair.1)
  | right => fun n => max (Nat.size n) (Nat.size n.unpair.2)
  | pair cf cg => fun n =>
      max (max (spaceCost cf n) (spaceCost cg n)) (Nat.size (Nat.pair (val cf n) (val cg n)))
  | comp cf cg => fun n =>
      max (spaceCost cg n) (spaceCost cf (val cg n))
  | prec cf cg =>
      Nat.unpaired fun a n =>
        n.rec (spaceCost cf a)
          (fun y IH =>
            max IH (spaceCost cg (Nat.pair a (Nat.pair y (val (prec cf cg) (Nat.pair a y))))))
  | rfind' _ => fun _ => 0

/-! ## Space step laws — all UNCONDITIONAL (same `Nat.rec` structure ⇒ no `Part.Dom` side goals) -/

theorem spaceCost_zero (n : ℕ) : spaceCost zero n = max (Nat.size n) (Nat.size 0) := rfl
theorem spaceCost_succ (n : ℕ) : spaceCost succ n = max (Nat.size n) (Nat.size (n + 1)) := rfl
theorem spaceCost_left (n : ℕ) : spaceCost left n = max (Nat.size n) (Nat.size n.unpair.1) := rfl
theorem spaceCost_right (n : ℕ) : spaceCost right n = max (Nat.size n) (Nat.size n.unpair.2) := rfl

theorem spaceCost_pair (f g : Code) (n : ℕ) :
    spaceCost (pair f g) n =
      max (max (spaceCost f n) (spaceCost g n)) (Nat.size (Nat.pair (val f n) (val g n))) := rfl

/-- The `comp` space law: `g`'s workspace, then `f`'s workspace on `g`'s VALUE (the intermediate
`val g n` bitlength is already inside `f`'s I/O account, so no separate term). -/
theorem spaceCost_comp (f g : Code) (n : ℕ) :
    spaceCost (comp f g) n = max (spaceCost g n) (spaceCost f (val g n)) := rfl

theorem spaceCost_prec_zero (cf cg : Code) (a : ℕ) :
    spaceCost (prec cf cg) (Nat.pair a 0) = spaceCost cf a := by
  simp only [spaceCost, Nat.unpaired, Nat.unpair_pair, Nat.rec_zero]

theorem spaceCost_prec_succ (cf cg : Code) (a m : ℕ) :
    spaceCost (prec cf cg) (Nat.pair a (m + 1)) =
      max (spaceCost (prec cf cg) (Nat.pair a m))
        (spaceCost cg (Nat.pair a (Nat.pair m (val (prec cf cg) (Nat.pair a m))))) := by
  simp only [spaceCost, Nat.unpaired, Nat.unpair_pair]

/-! ## The Capacity-Bounded Evaluation crux — a magnitude-INDEPENDENT `max` bound for `prec`

The space analogue of `tc_prec_le`, and the shape is the whole point: where the time bound is a SUM
linear in the iteration count `n`, the space bound is a `max` INDEPENDENT of `n`.

A note on the hypotheses. The time engine takes `∀ x, tc cg x ≤ B` — a genuine uniform bound, because a
straight-line code's step count does not depend on the MAGNITUDE of its input. Its literal space analogue
`∀ x, spaceCost cg x ≤ S` is UNSATISFIABLE: a base node holds its input, so `Nat.size x ≤ spaceCost cg x`
for every real `cg`, and no `S` bounds `Nat.size x` over all `x`. Space, unlike step count, must grow with
input bitlength. So the faithful — and satisfiable — hypothesis is the per-step bound RELATIVE to a small
accumulator: `cg` uses `≤ S` workspace on `⟨a, ⟨m, b⟩⟩` whenever the accumulator slot `b` is itself `≤ S`
bits (`hcg`), together with the accumulator-bitlength bound that keeps the actual accumulators in that
regime (`hacc`). Both are genuinely consumed; together they are exactly the poly-space-workspace regime a
bounded checker lives in (bounded per-step verification `hcg`, bounded carried verdict `hacc`) — the same
loop on which `tc` is instead astronomically large. -/
theorem spaceCost_prec_le {cf cg : Code} {S a n : ℕ}
    (hcg : ∀ m b, m ≤ n → Nat.size b ≤ S →
      spaceCost cg (Nat.pair a (Nat.pair m b)) ≤ S)
    (hacc : ∀ m, m ≤ n → Nat.size (val (prec cf cg) (Nat.pair a m)) ≤ S) :
    spaceCost (prec cf cg) (Nat.pair a n) ≤ max (spaceCost cf a) S := by
  revert hcg hacc
  induction n with
  | zero =>
      intro _ _
      rw [spaceCost_prec_zero]
      exact le_max_left _ _
  | succ m ih =>
      intro hcg hacc
      rw [spaceCost_prec_succ]
      refine max_le ?_ ?_
      · exact ih (fun m' b hm' hb => hcg m' b (Nat.le_succ_of_le hm') hb)
          (fun m' hm' => hacc m' (Nat.le_succ_of_le hm'))
      · exact le_max_of_le_right
          (hcg m _ (Nat.le_succ m) (hacc m (Nat.le_succ m)))

/-- **Space is measured along the genuine computation.** `spaceCost` maxes over the bitlengths of the
values `val` produces, and on the rfind'-free fragment those are exactly the `eval` values
(`eval_eq_val`). In particular the accumulator whose bitlength `spaceCost_prec_le`'s `hacc` bounds is
the true `eval` output of the partial `prec`, so the space bound is a bound along the real computation,
not along a surrogate. -/
theorem eval_prec_acc {cf cg : Code} (hc : RfindFree (prec cf cg)) (a m : ℕ) :
    eval (prec cf cg) (Nat.pair a m) = Part.some (val (prec cf cg) (Nat.pair a m)) :=
  eval_eq_val hc (Nat.pair a m)

end TimeCost
