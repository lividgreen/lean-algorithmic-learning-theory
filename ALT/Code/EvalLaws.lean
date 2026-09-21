/-
Copyright (c) 2026 Mykola Palamarchuk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mykola Palamarchuk
-/
module

public import Mathlib.Computability.PartrecCode

/-!
# Structural evaluation laws for `Nat.Partrec.Code`

Upstream states `Nat.Partrec.Code.eval` at the recursion constructor (`eval_prec_zero`,
`eval_prec_succ`) and at the derived codes (`eval_const`, `eval_id`, `eval_curry`), but not at
`comp`, `left`, `right` or `pair`, whose clauses are left to unfold definitionally at each use.
This module states those four, once.

* `eval_comp_some` — composition in the common case where the inner code converges: once `b`
  outputs `v` on `j`, running `comp a b` on `j` is running `a` on `v`.
* `eval_left'`, `eval_right'` — the two projections are the halves of `Nat.unpair`.
* `eval_pair_bind` — pairing in `bind`/`map` form. Upstream's clause is written with `<*>`, which
  does not meet a `bind`-shaped goal.

The module is deliberately a leaf: it knows codes and their evaluation, and nothing about the
step-counting cost model built on top of them.
-/

-- "deliberately a leaf: … nothing about the step-counting cost model"

@[expose] public section

assert_not_exists TimeCost.tc

namespace CodeEvalLaws

open Nat.Partrec (Code)
open Nat.Partrec.Code

/-- If `b` outputs `v` on input `j`, then `comp a b` runs `a` on `v` (the `comp` eval law is
definitional, then `Part.bind_some`). -/
theorem eval_comp_some {a b : Code} {j v : ℕ} (hv : eval b j = Part.some v) :
    eval (comp a b) j = eval a v := by
  change eval b j >>= eval a = eval a v
  rw [hv]
  exact Part.bind_some v (eval a)

/-- Base eval law: `left` is left unpairing. -/
theorem eval_left' (x : ℕ) : eval left x = Part.some x.unpair.1 := rfl

/-- Base eval law: `right` is right unpairing. -/
theorem eval_right' (x : ℕ) : eval right x = Part.some x.unpair.2 := rfl

/-- `eval`'s `pair` clause in bind/map form (upstream states it with `<*>`). -/
theorem eval_pair_bind (cf cg : Code) (n : ℕ) :
    eval (pair cf cg) n = (eval cf n).bind fun u => (eval cg n).map (Nat.pair u) := by
  ext x
  simp [eval, Seq.seq]

end CodeEvalLaws
