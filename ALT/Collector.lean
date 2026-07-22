/-
Copyright (c) 2026 Mykola Palamarchuk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mykola Palamarchuk
-/
import Mathlib
import ALT.BinaryConstant
import ALT.TimeCost

-- Formal-check file, not Mathlib-destined: opt out of the house-style linters.
set_option linter.style.header false
set_option linter.style.longLine false

/-!
# The orbit collector `collector cR` — discharging Prop 2.2's modeled premise

Provenance: [SQ] §2.2 / Prop 2.2 (~lines 107–119), the FV-AC row.
Extends `ALT/AdditiveComplexity.lean` (`E`, `elen`, `KE`, `KE_t`, `E_len_comp`) and
`ALT/BinaryConstant.lean` (`bconst`, `eval_bconst`, `elen_bconst_le`, `prop_2_2_core`).

Status: PROVED (eval level). Target B (an explicit `evaln` budget) is a documented WALL; Target C
(`H_T`) is a declared model boundary. See the boundary note below.

## What this replaces
`prop_2_2_core` (in `BinaryConstant.lean`) took the collector `coll : Code` as an ARBITRARY code and
ASSUMED the assembly halts on some output `y` (`h : y ∈ evaln T (comp coll (comp cR (bconst n))) 0`).
That is the "modeled premise". This file CONSTRUCTS a genuine collector and PROVES the assembly
computes the orbit prefix, so the premise is discharged at the eval level.

## The construction — a fixed iterator template with the rule plugged in
A rule-INDEPENDENT collector receiving `cR(n)` cannot re-run `cR` (first-order `Code`, no internalized
universal evaluator). So the collector is a fixed template `collector · := prec zero (stepWrap ·)`
applied to the rule code `cR` — the rule appears as the subterm `comp cR projState` inside `stepWrap`.
This is faithful: `elen (collector cR) = elen cR + 60` (a fixed constant plus the rule), so the
assembled length is still `elen cR + O(log n) = r + O(log n)`.

## I/O convention (fixed here; consumed by `prop_2_2_eval`)
* Step map: `rs : ℕ → ℕ` (state ↦ next state), computed by `cR` (`hcR : ∀ x, eval cR x = some (rs x)`;
  the rule is a total deterministic step, as in Prop 2.2).
* Initial condition `x₀ = 0` (absorbed into the fixed `O(1)` collector — the paper puts the IC in the
  `H_T` residual).
* Orbit: `o_t := rs^[t] 0` (certified by `orbitAcc_fst`).
* Accumulator / encoded prefix: `orbitAcc rs n : ℕ`, defined by the same recursion the code runs:
  `orbitAcc rs 0 = 0` and `orbitAcc rs (k+1) = pair (rs sₖ) (pair encₖ sₖ)` where
  `sₖ = (orbitAcc rs k).unpair.1` (current state) and `encₖ = (orbitAcc rs k).unpair.2` (prefix).
  So `orbitAcc rs n = Nat.pair (o_n) ⟨encoded o_0 … o_{n-1}⟩` — a single `ℕ` encoding the length-`n`
  orbit prefix. This is Prop 2.2's `o_{1:n}` object.
* Assembly: `assembly cR n := comp (collector cR) (pair zero (bconst n))`. On input `0`:
  `bconst n → n`, `pair zero (bconst n) → Nat.pair 0 n`, `collector cR` iterates → `orbitAcc rs n`.

## Boundaries
* **Target B (explicit `evaln` budget) — WALL.** `evaln`'s single budget `k` guards `n ≤ k` at every
  node (and `evaln_bound` forces every intermediate value `≤ k`), so any budget for the iterator is at
  least its largest intermediate value `orbitAcc rs n` — super-exponential in `n`, NOT polynomial.
  `evaln`'s `k` is fuel-with-a-value-ceiling, not the paper's TIME budget `T`. Honest fallback shipped:
  `prop_2_2_t_exists` (∃ SOME budget, via `evaln_complete`). See the module note on the documented wall.
* **Target C (`H_T`) — model boundary.** `H_T = E_X[log 1/P*(X)]` lives on a probabilistic-program
  semantics (argmin over `P_T`, expected log-loss) Mathlib lacks. The deterministic-regime rendering
  (per-step log-loss `= 0`) is `0 = 0` — no content; the `log|O|` initial residual needs the
  probabilistic layer. Declared a boundary, consistent with `S_T` itself being imported.
-/

namespace AdditiveComplexity

open Nat.Partrec Nat.Partrec.Code KolmogorovComplexity

/-! ## Length law for `prec` and base eval helpers -/

/-- The additive length law for `prec` (identical shape to `E_len_comp`/`E_len_pair`). -/
theorem E_len_prec (cf cg : Code) : elen (prec cf cg) = 3 + elen cf + elen cg := by
  simp only [elen, E, List.length_append, List.length_cons, List.length_nil]

/-- Base eval law: `left` is left unpairing. -/
theorem eval_left' (x : ℕ) : eval left x = Part.some x.unpair.1 := rfl

/-- Base eval law: `right` is right unpairing. -/
theorem eval_right' (x : ℕ) : eval right x = Part.some x.unpair.2 := rfl

/-- If `b` outputs `v` on input `j`, then `comp a b` runs `a` on `v` (the `comp` eval law is
definitional, then `Part.bind_some`). Local copy of `BinaryConstant`'s private helper. -/
theorem eval_comp_some {a b : Code} {j v : ℕ} (hv : eval b j = Part.some v) :
    eval (comp a b) j = eval a v := by
  change eval b j >>= eval a = eval a v
  rw [hv]; exact Part.bind_some v (eval a)

/-! ## The orbit accumulator (Lean-level) and its orbit certification -/

/-- The encoded orbit prefix: a single `ℕ` built by the same recursion the collector code runs.
`orbitAcc rs n = Nat.pair (current state) (encoded prefix o_0 … o_{n-1})`. -/
def orbitAcc (rs : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 =>
    Nat.pair (rs (orbitAcc rs k).unpair.1)
      (Nat.pair (orbitAcc rs k).unpair.2 (orbitAcc rs k).unpair.1)

/-- Orbit certification: the current-state component after `n` steps is exactly `rs^[n] 0` — so the
collected stream genuinely is the rule's orbit `o_t = rs^[t] x₀` with `x₀ = 0`. -/
theorem orbitAcc_fst (rs : ℕ → ℕ) (n : ℕ) : (orbitAcc rs n).unpair.1 = rs^[n] 0 := by
  induction n with
  | zero => rfl
  | succ k ih =>
    rw [orbitAcc, Nat.unpair_pair, Function.iterate_succ_apply', ih]

/-! ## The collector code -/

/-- Extract the recursion accumulator from a `prec`-step input `Nat.pair a (Nat.pair y m)`: two right
unpairings give `m`. -/
def projIH : Code := comp right right

/-- The current-state projection: `left` of the accumulator. -/
def projState : Code := comp left projIH

/-- The prefix projection: `right` of the accumulator. -/
def projEnc : Code := comp right projIH

/-- The step template: given `Nat.pair a (Nat.pair y m)`, output `Nat.pair (rs m₁) (Nat.pair m₂ m₁)`
where `m₁ = m.unpair.1`, `m₂ = m.unpair.2`. The rule `cR` enters as the subterm `comp cR projState`. -/
def stepWrap (cR : Code) : Code := pair (comp cR projState) (pair projEnc projState)

/-- **The collector** (fixed iterator template with the rule plugged in): primitive recursion with
base `zero` (= `orbitAcc rs 0`) and step `stepWrap cR`. On `Nat.pair 0 n` it outputs `orbitAcc rs n`. -/
def collector (cR : Code) : Code := prec Code.zero (stepWrap cR)

/-- **The assembly** `collector ∘ (pair zero (bconst n))`: on input `0`, forms `Nat.pair 0 n` from the
binary constant and iterates. This is the honest realization of the paper's `collector ∘ R ∘ bconst n`
(the rule is inside `collector cR`, not a separate middle factor — see the module note). -/
noncomputable def assembly (cR : Code) (n : ℕ) : Code :=
  comp (collector cR) (pair Code.zero (bconst n))

/-! ## Eval correctness -/

/-- Projection eval laws on a step input `Nat.pair a (Nat.pair y m)`. -/
theorem eval_projIH (a y m : ℕ) : eval projIH (Nat.pair a (Nat.pair y m)) = Part.some m := by
  rw [projIH, eval_comp_some (eval_right' _), eval_right']
  simp

theorem eval_projState (a y m : ℕ) :
    eval projState (Nat.pair a (Nat.pair y m)) = Part.some m.unpair.1 := by
  rw [projState, eval_comp_some (eval_projIH a y m), eval_left']

theorem eval_projEnc (a y m : ℕ) :
    eval projEnc (Nat.pair a (Nat.pair y m)) = Part.some m.unpair.2 := by
  rw [projEnc, eval_comp_some (eval_projIH a y m), eval_right']

/-- The step template's eval law: advance the state via `cR` and append the current state. -/
theorem eval_stepWrap {cR : Code} {rs : ℕ → ℕ} (hcR : ∀ x, eval cR x = Part.some (rs x))
    (a y m : ℕ) :
    eval (stepWrap cR) (Nat.pair a (Nat.pair y m)) =
      Part.some (Nat.pair (rs m.unpair.1) (Nat.pair m.unpair.2 m.unpair.1)) := by
  have hnew : eval (comp cR projState) (Nat.pair a (Nat.pair y m)) = Part.some (rs m.unpair.1) := by
    rw [eval_comp_some (eval_projState a y m), hcR]
  have happ : eval (pair projEnc projState) (Nat.pair a (Nat.pair y m)) =
      Part.some (Nat.pair m.unpair.2 m.unpair.1) := by
    change Nat.pair <$> eval projEnc _ <*> eval projState _ = _
    rw [eval_projEnc, eval_projState]
    simp [Seq.seq]
  change Nat.pair <$> eval (comp cR projState) _ <*> eval (pair projEnc projState) _ = _
  rw [hnew, happ]
  simp [Seq.seq]

/-- The collector iterates the rule: on `Nat.pair 0 n` it outputs `orbitAcc rs n`. Induction on `n`
via `eval_prec_zero`/`eval_prec_succ` and the step law. -/
theorem eval_collector {cR : Code} {rs : ℕ → ℕ} (hcR : ∀ x, eval cR x = Part.some (rs x)) (n : ℕ) :
    eval (collector cR) (Nat.pair 0 n) = Part.some (orbitAcc rs n) := by
  induction n with
  | zero =>
    rw [collector, eval_prec_zero]
    rfl
  | succ k ih =>
    rw [collector, eval_prec_succ]
    rw [show collector cR = prec Code.zero (stepWrap cR) from rfl] at ih
    rw [ih]
    -- reduce the `Part.some (orbitAcc rs k) >>= …` bind (the `Bind.bind` head resists a bare
    -- `rw [Part.bind_some]`, so force the `>>=` form via an explicit `show … from Part.bind_some`)
    rw [show (Part.some (orbitAcc rs k)) >>=
          (fun i => (stepWrap cR).eval (Nat.pair 0 (Nat.pair k i)))
        = (stepWrap cR).eval (Nat.pair 0 (Nat.pair k (orbitAcc rs k))) from Part.bind_some _ _,
      eval_stepWrap hcR]
    rfl

/-- **Eval correctness of the full assembly**: on input `0` it computes the orbit prefix
`orbitAcc rs n` — the collector premise DISCHARGED. -/
theorem eval_assembly {cR : Code} {rs : ℕ → ℕ} (hcR : ∀ x, eval cR x = Part.some (rs x)) (n : ℕ) :
    eval (assembly cR n) 0 = Part.some (orbitAcc rs n) := by
  have hz : eval Code.zero 0 = Part.some 0 := rfl
  have hin : eval (pair Code.zero (bconst n)) 0 = Part.some (Nat.pair 0 n) := by
    change Nat.pair <$> eval Code.zero 0 <*> eval (bconst n) 0 = _
    rw [hz, eval_bconst]
    simp [Seq.seq]
  rw [assembly, eval_comp_some hin, eval_collector hcR]

/-- The assembly computes `orbitAcc rs n` from input `0` (the `Computes` form). -/
theorem computes_assembly {cR : Code} {rs : ℕ → ℕ} (hcR : ∀ x, eval cR x = Part.some (rs x))
    (n : ℕ) : Computes (assembly cR n) (orbitAcc rs n) := eval_assembly hcR n

/-! ## Length accounting -/

/-- `projIH`, `projState`, `projEnc` are fixed codes of length `9`, `15`, `15`. -/
theorem elen_projIH : elen projIH = 9 := by decide
theorem elen_projState : elen projState = 15 := by decide
theorem elen_projEnc : elen projEnc = 15 := by decide

/-- The step template's length is a fixed constant plus the rule's length. -/
theorem elen_stepWrap (cR : Code) : elen (stepWrap cR) = elen cR + 54 := by
  rw [stepWrap, E_len_pair, E_len_comp, E_len_pair, elen_projState, elen_projEnc]
  omega

/-- **The collector's length is a fixed `O(1)` plus the rule** — `elen (collector cR) = elen cR + 60`.
So the collector contributes only a constant to the assembled program length. -/
theorem elen_collector (cR : Code) : elen (collector cR) = elen cR + 60 := by
  rw [collector, E_len_prec, elen_stepWrap]
  have hz : elen Code.zero = 3 := rfl
  omega

/-- The assembled program's length: `elen cR + elen (bconst n) + 69`. -/
theorem elen_assembly (cR : Code) (n : ℕ) :
    elen (assembly cR n) = elen cR + elen (bconst n) + 69 := by
  rw [assembly, E_len_comp, elen_collector, E_len_pair]
  have hz : elen Code.zero = 3 := rfl
  omega

/-! ## Prop 2.2 core, DISCHARGED at the eval level -/

/-- **Prop 2.2 `|P|`-component, collector premise DISCHARGED (eval level).** For a rule `cR` computing
a total step map `rs`, the length-`n` orbit prefix `orbitAcc rs n` has additive complexity
`KE ≤ elen cR + κ·Nat.size n + (84 + elen dbl)` with `κ = 15 + elen dbl` — i.e. `r + O(log n)`, with
the collector CONSTRUCTED (not modeled). The witness is `assembly cR n`; its length is additive by
`elen_assembly`, and `elen (bconst n) = O(Nat.size n)` by `elen_bconst_le`. -/
theorem prop_2_2_eval {cR : Code} {rs : ℕ → ℕ} (hcR : ∀ x, eval cR x = Part.some (rs x)) (n : ℕ) :
    KE (orbitAcc rs n) ≤ elen cR + (15 + elen dbl) * Nat.size n + (84 + elen dbl) := by
  have h1 := KE_le (computes_assembly hcR n)
  rw [elen_assembly] at h1
  have h2 := elen_bconst_le n
  omega

/-! ## Target B — the honest ∃-budget fallback (explicit budget is walled; see the module note) -/

/-- **Prop 2.2 `|P|`-component, time-bounded form (∃-budget fallback).** There EXISTS a step budget
`T` under which `KE_t T (orbitAcc rs n) ≤ elen cR + κ·Nat.size n + (84 + elen dbl)`. The budget is
existential (via `evaln_complete`), NOT an explicit polynomial in `n`: `evaln`'s `k` caps intermediate
values, so any explicit budget for this iterator is ≥ `orbitAcc rs n` (super-exponential in `n`). The
explicit-polynomial budget is a documented wall (module note), mirroring `KE_t_eventually`. -/
theorem prop_2_2_t_exists {cR : Code} {rs : ℕ → ℕ} (hcR : ∀ x, eval cR x = Part.some (rs x)) (n : ℕ) :
    ∃ T, KE_t T (orbitAcc rs n) ≤
      (elen cR + (15 + elen dbl) * Nat.size n + (84 + elen dbl) : ℕ) := by
  obtain ⟨T, hT⟩ := evaln_complete.1 (Part.eq_some_iff.mp (eval_assembly hcR n))
  refine ⟨T, ?_⟩
  refine (KE_t_le hT).trans ?_
  have h2 := elen_bconst_le n
  rw [elen_assembly]
  exact_mod_cast (by omega : elen cR + elen (bconst n) + 69
    ≤ elen cR + (15 + elen dbl) * Nat.size n + (84 + elen dbl))

/-! ## The native-cost LINEAR bound, discharged for the collector

`prop_2_2_t_exists` above ships an EXISTENTIAL `evaln` budget because `evaln`'s fuel caps intermediate
VALUES (`evaln_bound`), so no explicit polynomial budget exists for this value-growing iterator. The
native step count `TimeCost.tc` (see `ALT/TimeCost.lean`) instead charges each `prec`/`comp`
unfolding `O(1)` regardless of value magnitude, so it DOES admit an explicit linear bound. The
projection/stepWrap cost lemmas below feed the generic `TimeCost.tc_prec_le` engine. -/

open TimeCost

/-- `tc projIH x = 3` — a fixed cost (`comp right right`), independent of `x`. -/
theorem tc_projIH (x : ℕ) : tc projIH x = 3 := by
  simp [projIH, tc_comp]

/-- `tc projState x = 5` — a fixed cost (`comp left projIH`), independent of `x` AND of the value
`val projIH x` threaded through it (the outer `left` discards its argument's magnitude). -/
theorem tc_projState (x : ℕ) : tc projState x = 5 := by
  simp [projState, tc_comp, tc_projIH]

/-- `tc projEnc x = 5` — a fixed cost (`comp right projIH`), independent of `x` and of the value. -/
theorem tc_projEnc (x : ℕ) : tc projEnc x = 5 := by
  simp [projEnc, tc_comp, tc_projIH]

/-- **One collector step costs a fixed `18` plus one call to the rule `cR`.** The `18` is the
proj/pair/comp overhead of `stepWrap`; the only value-dependent term is `tc cR (val projState x)`,
which a uniform per-call bound caps WITHOUT reference to the magnitude of `val projState x`. -/
theorem tc_stepWrap (cR : Code) (x : ℕ) :
    tc (stepWrap cR) x = 18 + tc cR (val projState x) := by
  rw [stepWrap]
  simp only [tc_pair, tc_comp, tc_projState, tc_projEnc]
  omega

/-- **Prop 2.2 `|P|`-component, native-time LINEAR bound — DISCHARGED for the
collector.** For a rule `cR` whose per-call native cost is `≤ K` uniformly (`hK`), the collector's
native sequential-time cost on `Nat.pair a n` is `≤ (K + 19)·n + 19` — LINEAR in the number of orbit
steps `n`, with the explicit fixed constant `C = 19` (the `stepWrap` proj/pair/comp overhead). The
bound is MAGNITUDE-INDEPENDENT: it never mentions the accumulator values `rs^[i] 0` — which grow
super-exponentially and are exactly what forced the `evaln` value-cap wall behind `prop_2_2_t_exists`
— because each step's rule call is capped by the uniform `hK`, not by the value threaded through it.
This is the wall discharged: `TimeCost.tc` charges `O(1)` per `prec`/`comp` unfolding regardless of
value size (value-agreement `TimeCost.eval_eq_val` certifies the value carries no cap). `hcR` (the rule
genuinely computes the total step map `rs`) is unused in the bound; it certifies `collector cR` is the
honest orbit collector of `eval_collector`, keeping the statement parallel to `prop_2_2_t_exists`. -/
theorem prop_2_2_t_poly {cR : Code} {rs : ℕ → ℕ} (_hcR : ∀ x, eval cR x = Part.some (rs x))
    {K : ℕ} (hK : ∀ x, tc cR x ≤ K) (a n : ℕ) :
    tc (collector cR) (Nat.pair a n) ≤ (K + 19) * n + 19 := by
  have hstep : ∀ x, tc (stepWrap cR) x ≤ 18 + K := by
    intro x
    rw [tc_stepWrap]
    have := hK (val projState x)
    omega
  have hbound := tc_prec_le (cf := Code.zero) hstep a n
  rw [collector]
  have h0 : tc Code.zero a = 1 := tc_zero a
  rw [h0] at hbound
  have heq : (18 + K + 1) * n = (K + 19) * n := by ring
  rw [heq] at hbound
  omega

end AdditiveComplexity
