import Mathlib

-- Tier-1 formal check, not Mathlib-destined: opt out of the house-style linters.
set_option linter.style.header false
set_option linter.style.longLine false

/-!
# A native sequential-time cost on the rfind'-free fragment of `Nat.Partrec.Code` (F20 Stage A)

Provenance: the native-cost-model workstream. Companion to `ALT/Collector.lean`, whose
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

## Scope (Stage A)
Only the rfind'-free fragment (`zero succ left right pair comp prec`), on which `eval` is total.
`rfind'` is a Stage-A placeholder `(0, 0)` — OUT of the fragment; value-agreement is stated only for
`RfindFree c`, and later stages add the search-cost account. The collector payoff (`tc_prec_le`) needs
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
partiality and no well-founded recursion. `rfind'` is a Stage-A placeholder (out of fragment). -/
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

end TimeCost
