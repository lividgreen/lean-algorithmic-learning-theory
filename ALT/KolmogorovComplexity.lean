/-
Copyright (c) 2026 Mykola Palamarchuk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mykola Palamarchuk
-/
import Mathlib

-- Formal-check file, not Mathlib-destined: opt out of the house-style header linter.
set_option linter.style.header false

/-!
# Kolmogorov complexity on Mathlib's universal machine (Paper II §1.1, Paper III §2)

Provenance: Paper II, §1.1 (`K(R) = r` relative to a fixed universal
reference machine `U_ref`, with the invariance-constant caveat). Built directly on Mathlib's
`Nat.Partrec.Code` (the universal partial-recursive machine `Code.eval`) and Kleene's recursion
theorem `Nat.Partrec.Code.fixed_point₂`.

Status: PROVED. A genuine Kolmogorov complexity with its basic API, unboundedness, and
uncomputability — on the **least-index** measure (see the length-measure note).

## Length measure: least-INDEX complexity (read this — value is NOT the paper's `r`)
We take `codelen c := Encodable.encode c`, the code's **index** (Gödel number). So `K x` here is
*least-index complexity*: the smallest index of a program outputting `x`. This is a deliberate
Slice-1 pragmatism — `codelen` is then trivially `Computable`, avoiding a `Nat.size`-computability
detour.

The paper's `r` is a **bit-length**: `r = Nat.size (encode c)` (number of bits of the index).
Relation to this file's measure:
* same minimizer — `Nat.size` is monotone, so the index-minimizing program is also the
  bit-length-minimizing one;
* but the **values differ exponentially**: paper-`r` `= Nat.size (K_index x) ≈ log₂ (K_index x)`,
  i.e. this file's `K x` is exponentially larger than the paper's `r`.

**Consequently no later step may read this `K x` as the paper's `r`** — the regime `r ≪ K ≪ L` is
in bits. The bit-length refinement `Nat.size ∘ encode` is the natural companion when `K` is later
reconnected to `r` (a separate, deferred step).

The qualitative headlines — **uncomputability** and **unboundedness** — transfer to the bit-length
measure unchanged (the recursion-theorem proof never uses the value of `codelen`, only that it is
computable and that `K` is unbounded), so they are faithful even though the value is not `r`.

## What this DOES establish
* `K`: Kolmogorov (least-index) complexity on `Code.eval`, well-defined via `Code.const x`.
* `K_le`, `exists_min_code`, `K_le_const`: the basic minimization API + a concrete witness.
* `setOf_K_le_finite`, `K_unbounded`: only finitely many `x` have `K x ≤ n`; incompressible objects
  of every complexity exist.
* `K_not_computable`: **Kolmogorov complexity is uncomputable** — via Kleene's recursion theorem
  (`fixed_point₂`), so it needs no program-size/encoding bound. (Mathlib's `encodeCode` uses the
  quadratic `Nat.pair`, which would defeat a Berry-paradox proof; the recursion theorem sidesteps
  that by handing the self-referential program its own code.)

## What this does NOT establish (flagged / other steps)
* Does NOT reconnect `K` to the abstract `r`/`K` of the existing files — a separate later step, and
  it requires the bit-length measure (see above), not this index measure.
* NOT time-bounded `K_t` / epiplexity (Paper III §2.1) — a later slice (the `evaln`-set is empty for
  small budgets, so `K ≤ K_t` needs budget/nonemptiness care).
* NOT two-machine invariance (Mathlib has one fixed `eval`; faithful restatement = constant overhead
  under a computable re-encoding — deferred).
* NOT the structure function (§2.3); NOT prefix-free `K` or the `∑ 2^{−K} ≤ 1` link to A4 — this is
  **plain**, not prefix, complexity.

## Hypotheses: paper-stated vs added
* Paper-stated / faithful: `K` as least program length for `x`; uncomputability; unboundedness.
* Added / modeling: one fixed machine (`Code.eval`) for `U_ref` (so invariance is deferred); the
  least-**index** length measure; the input-`0` ("output from nothing") convention.
-/

namespace KolmogorovComplexity

open Nat.Partrec Nat.Partrec.Code

/-- Program "length": the code's index (Gödel number). This is the **least-index** measure; the
paper's bit-length `r` is `Nat.size (encode c)` (same minimizer, exponentially smaller value). -/
def codelen (c : Code) : ℕ := Encodable.encode c

/-- `c` computes `x`, output-from-nothing convention: run on input `0`. -/
def Computes (c : Code) (x : ℕ) : Prop := c.eval 0 = Part.some x

/-- Kolmogorov (least-index) complexity on Mathlib's universal machine `Code.eval`: the least
program length over codes outputting `x` from input `0`. Well-defined — `Code.const x` computes
`x`, so the minimand is nonempty. (Paper II §1.1 `K(R) = r`, relative to a fixed machine.) -/
noncomputable def K (x : ℕ) : ℕ := sInf { l | ∃ c, Computes c x ∧ codelen c = l }

/-- The constant code outputs `x` from any input. -/
theorem const_computes (x : ℕ) : Computes (Code.const x) x := by
  simp [Computes, eval_const]

/-- Any program computing `x` bounds `K x`. -/
theorem K_le {c : Code} {x : ℕ} (h : Computes c x) : K x ≤ codelen c :=
  Nat.sInf_le ⟨c, h, rfl⟩

/-- `K x` is achieved by some code. -/
theorem exists_min_code (x : ℕ) : ∃ c, Computes c x ∧ codelen c = K x := by
  have hne : { l | ∃ c, Computes c x ∧ codelen c = l }.Nonempty :=
    ⟨codelen (Code.const x), Code.const x, const_computes x, rfl⟩
  obtain ⟨c, hc, hl⟩ := Nat.sInf_mem hne
  exact ⟨c, hc, hl⟩

/-- The trivial generator bound: the constant program witnesses finiteness/totality of `K`. -/
theorem K_le_const (x : ℕ) : K x ≤ codelen (Code.const x) :=
  K_le (const_computes x)

/-- Only finitely many `x` have `K x ≤ n`: finitely many short programs, each outputting at most
one value. -/
theorem setOf_K_le_finite (n : ℕ) : { x | K x ≤ n }.Finite := by
  classical
  -- finitely many codes of bounded length
  have hcodes : { c : Code | codelen c ≤ n }.Finite := by
    apply Set.Finite.ofFinset ((Finset.range (n + 1)).preimage Encodable.encode
      (Encodable.encode_injective.injOn))
    intro c
    simp [codelen]
  -- each `x` with `K x ≤ n` is the (total-ified) output of one of those codes
  apply (hcodes.image (fun c => if h : (c.eval 0).Dom then (c.eval 0).get h else 0)).subset
  intro x hx
  obtain ⟨c, hcomp, hlen⟩ := exists_min_code x
  refine ⟨c, ?_, ?_⟩
  · change codelen c ≤ n
    rw [hlen]; exact hx
  · have hdom : (c.eval 0).Dom := by rw [hcomp]; exact trivial
    change (if h : (c.eval 0).Dom then (c.eval 0).get h else 0) = x
    rw [dif_pos hdom]
    exact Part.get_eq_iff_eq_some.mpr hcomp

/-- `K` is unbounded: incompressible numbers of every complexity exist. -/
theorem K_unbounded (n : ℕ) : ∃ x, n < K x := by
  by_contra h
  have hall : ∀ x, K x ≤ n := fun x => by
    by_contra hx; exact h ⟨x, not_le.mp hx⟩
  -- `{x | K x ≤ n} = univ` then contradicts its finiteness
  exact Set.infinite_univ ((setOf_K_le_finite n).subset (fun x _ => hall x))

/-- **Uncomputability of Kolmogorov complexity** (the headline). Via Kleene's recursion theorem
(`fixed_point₂`): were `K` computable, a self-referential program `c₀` could output the least `x`
with `codelen c₀ < K x`, forcing `K x ≤ codelen c₀ < K x`. The recursion theorem supplies `c₀`
with its own code, so no program-size/encoding bound is needed (sidestepping the quadratic-pairing
blowup of `encodeCode`). -/
theorem K_not_computable : ¬ Computable K := by
  intro hK
  -- `decide (· < ·)` is computable (the `Decidable` instance is bundled in `PrimrecRel`'s `∃`).
  have hlt : Computable fun p : ℕ × ℕ => decide (p.1 < p.2) := by
    have hpr := Primrec.nat_lt.choose_spec.to_comp
    have heq : (fun a : ℕ × ℕ => @decide _ (Primrec.nat_lt.choose a)) =
        fun p : ℕ × ℕ => decide (p.1 < p.2) := by funext a; congr 1
    rw [← heq]; exact hpr
  -- The Berry predicate `codelen c < K x` is computable in `(c, x)`.
  have hg : Computable fun r : (Code × ℕ) × ℕ => decide (codelen r.1.1 < K r.2) := by
    have c1 : Computable fun r : (Code × ℕ) × ℕ => codelen r.1.1 :=
      Computable.encode.comp (Computable.fst.comp Computable.fst)
    have c2 : Computable fun r : (Code × ℕ) × ℕ => K r.2 := hK.comp Computable.snd
    exact hlt.comp (c1.pair c2)
  -- The Berry search (an `rfind`, ignoring the second argument) is `Partrec₂`.
  have hf : Partrec₂ (fun (c : Code) (_ : ℕ) =>
      Nat.rfind fun x => Part.some (decide (codelen c < K x))) :=
    Partrec.rfind (p := fun (q : Code × ℕ) (x : ℕ) =>
      Part.some (decide (codelen q.1 < K x))) hg.partrec
  -- Recursion theorem: a code `c₀` equal to the search at its own code.
  obtain ⟨c₀, hc₀⟩ := fixed_point₂ hf
  -- The search halts (`K` is unbounded), giving a witness `x₀`.
  obtain ⟨x₀, hx₀⟩ := K_unbounded (codelen c₀)
  set p₀ : ℕ →. Bool := fun x => Part.some (decide (codelen c₀ < K x)) with hp₀
  have heval : c₀.eval 0 = Nat.rfind p₀ := by rw [hc₀]
  have hdom : (Nat.rfind p₀).Dom := by
    rw [Nat.rfind_dom]
    exact ⟨x₀, by simp [hp₀, hx₀], fun {m} _ => trivial⟩
  set w : ℕ := (Nat.rfind p₀).get hdom with hw
  -- `w` is the least `x` with `codelen c₀ < K x`.
  have hwspec : codelen c₀ < K w := by
    have h : true ∈ p₀ w := Nat.rfind_spec (Part.get_mem hdom)
    simpa [hp₀] using h
  -- But `c₀` computes `w` from input `0`, so `K w ≤ codelen c₀`.
  have hcomp : Computes c₀ w := by
    rw [Computes, heval]
    exact Part.get_eq_iff_eq_some.mp hw.symm
  exact absurd (K_le hcomp) (not_le.mpr hwspec)

end KolmogorovComplexity
