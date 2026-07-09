import Mathlib
import ALT.AdditiveComplexity

-- Tier-1 formal check, not Mathlib-destined: opt out of the house-style header linter.
set_option linter.style.header false

/-!
# Length-efficient binary constant `bconst` (Stage ② gate for Prop 2.2 / A2b)

Provenance: `03_polynomial_convergence_under_SQ.md` §2.2 (Prop 2.2, the `S_T ≤ r + O(log)` bound)
and the two-machine-invariance / A2b model-bridge. Extends `ALT/AdditiveComplexity.lean`
(`E`, `elen`, `KE`).

Status: **PROVED**. `eval_bconst` and `elen_bconst_le` (with `κ = 15 + elen dbl`) are proved and
CI-guarded in `ALT/AxiomAuditMathlib.lean`; both depend only on `[propext, Classical.choice,
Quot.sound]` (`Classical.choice` genuinely used — `dbl` is extracted from universality).

## Why a new constant (the gate)
`AdditiveComplexity` documents that Mathlib's `Code.const` is a **unary tower**
(`const (n+1) = comp succ (const n)`), so `elen (Code.const n) = Θ(n)` — exponential in bit-length.
Both Prop 2.2's `O(log T)` and the A2b bound `KE(x) ≤ K_d(x) + c_d` need a constant whose additive
length is `O(Nat.size n)` (linear in *bits*). `bconst` builds `n` in Horner (binary) form: a fixed
doubling code `dbl` (`x ↦ 2x`, via universality) plus one `succ`/`id` per bit, so the AST has
`O(Nat.size n)` nodes.

## What this file establishes
* `dbl`, `eval_dbl`: a fixed doubling code and its eval law (from universality + `choose_spec`).
* `bconst`, `eval_bconst`: the binary constant and its correctness `eval (bconst n) m = n`.
* `elen_bconst_le`: the `O(Nat.size n)` length bound — the gate deliverable.
* `size_succ_div_two`, `eval_comp_some`: supporting lemmas (binary-length recursion; `comp` eval on
  a `some` output).
-/

namespace AdditiveComplexity

open Nat.Partrec Nat.Partrec.Code KolmogorovComplexity

/-- The binary-length recursion `Nat.size (n+1) = Nat.size ((n+1)/2) + 1`. Mathlib has no direct
`size (n/2)` lemma; derive it from `Nat.size_bit` + `Nat.bit_bodd_div2` + `Nat.div2_val`. -/
theorem size_succ_div_two (n : ℕ) : Nat.size (n + 1) = Nat.size ((n + 1) / 2) + 1 := by
  have hne : Nat.bit (n + 1).bodd (n + 1).div2 ≠ 0 := by
    rw [Nat.bit_bodd_div2]; exact Nat.succ_ne_zero n
  conv_lhs => rw [← Nat.bit_bodd_div2 (n + 1)]
  rw [Nat.size_bit hne, Nat.div2_val]

/-- `x ↦ 2x` is partial recursive. Bridge chain (report item 1): `Primrec.nat_mul` →
`Primrec (2 * ·)` → `Primrec.to_comp` → `Computable` → `Computable.partrec` → `_root_.Partrec` →
`Partrec.nat_iff.mp` → `Nat.Partrec`. -/
theorem partrec_dbl : Nat.Partrec (fun x : ℕ => (2 * x : ℕ)) := by
  have h : Primrec (fun x : ℕ => 2 * x) := Primrec.nat_mul.comp (Primrec.const 2) Primrec.id
  exact Partrec.nat_iff.mp h.to_comp.partrec

/-- A fixed doubling code, extracted from universality (`exists_code`). Noncomputable —
`Classical.choose` picks an arbitrary such code; its `elen` is a fixed (uncontrolled) constant
`elen dbl`. -/
noncomputable def dbl : Code := Classical.choose (exists_code.mp partrec_dbl)

/-- The doubling code's evaluation law: `eval dbl x = 2x`. From `Classical.choose_spec`
(`eval dbl = ↑(fun x => 2*x)`), applied pointwise. -/
theorem eval_dbl (x : ℕ) : dbl.eval x = Part.some (2 * x) := by
  have h := congrFun (Classical.choose_spec (exists_code.mp partrec_dbl)) x
  simpa [dbl] using h

/-- **Length-efficient binary constant**: `bconst n` computes `n` from any input, with
`O(Nat.size n)` AST nodes (vs `Θ(n)` for `Code.const`). Horner form: `n+1 = 2·((n+1)/2) + (n+1)%2`,
so double the code for `(n+1)/2` and add the low bit via `succ` (odd) or `id` (even). -/
noncomputable def bconst : ℕ → Code
  | 0 => Code.zero
  | n + 1 => comp (if (n + 1) % 2 = 0 then Code.id else Code.succ) (comp dbl (bconst ((n + 1) / 2)))
decreasing_by exact Nat.div_lt_self (Nat.succ_pos n) (by omega)

/-- If `b` outputs `v` on input `j`, then `comp a b` runs `a` on `v` (the `comp` eval law is
definitional, then `Part.bind_some`). -/
private theorem eval_comp_some {a b : Code} {j v : ℕ} (hv : eval b j = Part.some v) :
    eval (comp a b) j = eval a v := by
  change eval b j >>= eval a = eval a v
  rw [hv]; exact Part.bind_some v (eval a)

/-- Correctness: `bconst n` outputs `n` from any input (the constant ignores its argument). -/
theorem eval_bconst (n m : ℕ) : (bconst n).eval m = Part.some n := by
  induction n using bconst.induct with
  | case1 => rw [bconst]; rfl
  | case2 n ih =>
    rw [bconst]
    -- inner `comp dbl (bconst ((n+1)/2))` outputs `2 · ((n+1)/2)` (IH then `eval_dbl`)
    have h1 : eval (comp dbl (bconst ((n + 1) / 2))) m = Part.some (2 * ((n + 1) / 2)) :=
      (eval_comp_some ih).trans (eval_dbl _)
    rw [eval_comp_some h1]
    -- goal: `eval (if (n+1)%2=0 then id else succ) (2·((n+1)/2)) = Part.some (n+1)`
    split
    · rw [eval_id]; congr 1; omega
    · have hs : eval Code.succ (2 * ((n + 1) / 2)) = Part.some (2 * ((n + 1) / 2) + 1) := rfl
      rw [hs]; congr 1; omega

/-- **The gate deliverable**: `bconst`'s additive length is `O(Nat.size n)` — linear in the number
of *bits* of `n`, not in `n`. The explicit constant `κ = 15 + elen dbl` (per-step: two `comp`s = 6,
one `succ`/`id` ≤ 9, plus the fixed `elen dbl`), induction mirroring the `n ↦ (n+1)/2` recursion via
`Nat.size_bit`. -/
theorem elen_bconst_le (n : ℕ) :
    elen (bconst n) ≤ (15 + elen dbl) * Nat.size n + (15 + elen dbl) := by
  induction n using bconst.induct with
  | case1 =>
    rw [bconst, Nat.size_zero, Nat.mul_zero, Nat.zero_add]
    have h0 : elen Code.zero = 3 := rfl
    omega
  | case2 n ih =>
    -- the low-bit code (`id` or `succ`) has length ≤ 9
    have hX : elen (if (n + 1) % 2 = 0 then Code.id else Code.succ) ≤ 9 := by
      split <;> decide
    -- unfold, split the two `comp`s additively, expand `κ · size(n+1) = κ · size((n+1)/2) + κ`
    rw [bconst, E_len_comp, E_len_comp, size_succ_div_two, Nat.mul_add, Nat.mul_one]
    -- omega abstracts the nonlinear `κ · size((n+1)/2)` (shared with `ih`) and closes
    omega

/-! ## Payoffs: Prop 2.2 (time-bounded `|P|` bound) and multiplicative optimality (A2b) -/

/-- **Paper III Prop 2.2 (`|P|`-component)**: the length-`n` trajectory `y` produced within budget
`T` by `comp coll (comp cR (bconst n))` (rule code `cR`, `elen cR = r`; collector `coll`) has
time-bounded additive complexity `S_T ≤ r + O(log n)`. The `O(log n)` is `κ · Nat.size n`
(`κ = 15 + elen dbl`) — logarithmic in the horizon because `bconst` is binary, not the `Θ(n)` of
`Code.const`. Modeled premise: the assembled code computes `y` within `T` steps. -/
theorem prop_2_2_core (coll cR : Code) (n T y : ℕ)
    (h : y ∈ Code.evaln T (comp coll (comp cR (bconst n))) 0) :
    KE_t T y ≤
      (elen cR + (15 + elen dbl) * Nat.size n + (6 + elen coll + (15 + elen dbl)) : ℕ) := by
  have h1 := KE_t_le h
  rw [E_len_comp, E_len_comp] at h1
  have h2 := elen_bconst_le n
  refine h1.trans ?_
  have key : 3 + elen coll + (3 + elen cR + elen (bconst n))
      ≤ elen cR + (15 + elen dbl) * Nat.size n + (6 + elen coll + (15 + elen dbl)) := by omega
  exact_mod_cast key

/-- **Multiplicative optimality of `KE` (honest A2b)**: for any number-input description method `d`
with `d.eval p = x`, `KE x ≤ elen d + κ · Nat.size p + (3 + κ)` (`κ = 15 + elen dbl`). Hardcode the
program `p` as data via the binary constant `bconst p` (whose additive length is `O(Nat.size p)`,
not `Θ(p)`), then `comp d (bconst p)` computes `x` — the `+ O(log p)` model-bridge the `encodeCode`
measures cannot give additively. -/
theorem invariance_general (d : Code) (p x : ℕ) (h : d.eval p = Part.some x) :
    KE x ≤ elen d + (15 + elen dbl) * Nat.size p + (3 + (15 + elen dbl)) := by
  have hc : Computes (comp d (bconst p)) x := (eval_comp_some (eval_bconst p 0)).trans h
  have h1 := KE_le hc
  rw [E_len_comp] at h1
  have h2 := elen_bconst_le p
  omega

end AdditiveComplexity
