/-
Copyright (c) 2026 Mykola Palamarchuk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mykola Palamarchuk
-/
import ALT.KolmogorovComplexity
import ALT.KolmogorovTimeBounded

-- Formal-check file, not Mathlib-destined: opt out of the house-style header linter.
set_option linter.style.header false

/-!
# Bit-length Kolmogorov complexity: uncomputability (Slice 3)

Provenance: [Discovery], §1.1 (`r = K(R)`, "program length in bits", and the
invariance-constant caveat). Extends `ALT/KolmogorovComplexity.lean` (Slice 1: `codelen`,
`Computes`, `K`, `K_le`, `K_unbounded`, `K_not_computable` via `fixed_point₂`) and
`ALT/KolmogorovTimeBounded.lean` (Slice 2: `codelen' = Nat.size ∘ encode`, `K_bitlen`,
`K_bitlen_eq`, `K_bitlen_unbounded`).

Status: PROVED.

## What this DOES establish
* `computable_nat_size`: `Nat.size` is computable. Mathlib lacks this; built from
  `Nat.size_le : size m ≤ n ↔ m < 2^n`, which makes `size m` the least `n` with `m < 2^n` — an
  `rfind`.
* `K_bitlen_le`: any program computing `x` bounds its bit-length complexity by its own bit-length.
* `K_bitlen_not_computable`: the paper's **bit-length** Kolmogorov complexity (`r` in bits) is
  uncomputable — the same Kleene-`fixed_point₂` Berry argument as Slice-1's `K_not_computable`, now
  with the bit-length measure `codelen'` (computable since `Nat.size` is).

  Route note: a naive reduction from `K_not_computable` via `K_bitlen_eq : K_bitlen = Nat.size ∘ K`
  does NOT work (`Nat.size` is not injective, so `K_bitlen` computable does not give `K`
  computable). We re-run the recursion-theorem argument directly instead.

## What this does NOT establish (flagged)
* Two-machine invariance (`K_U ≤ K_V + c_{U,V}`) is DEFERRED with a documented obstruction.
  Mathlib exposes a single fixed universal machine `Code.eval` with no parameterization over
  alternative universal machines (the classical bound needs two, one simulating the other via a
  constant-size interpreter). And a "complexity relative to a computable re-encoding `f`"
  restatement gives no clean ADDITIVE constant, because `encodeCode` uses quadratic `Nat.pair` (same
  pathology that blocked Berry in Slice 1, sidestepped there only by the recursion theorem):
  wrapping a code blows up `encode` super-linearly. A faithful version would need a second
  `Nat.Partrec` universal function plus a simulation theorem — a sub-project.
* Does NOT reconnect `K`/`K_bitlen` to the abstract `r`/`K` reals of the other files (separate later
  step). NOT the structure function (§2.3); NOT the SQ framework. `K_bitlen` is `Nat.size` of the
  least-index `K` (Slice-2 `K_bitlen_eq`).

## Hypotheses: paper-stated vs added
* Paper-stated / faithful: bit-length `K` is uncomputable.
* Added / modeling: `Computable Nat.size` via `rfind`; the Berry argument reuses Slice-1's
  `fixed_point₂` (recursion theorem), dodging the `encodeCode` quadratic-pairing blowup.
-/

namespace KolmogorovComplexity

open Nat.Partrec Nat.Partrec.Code

set_option maxHeartbeats 400000 in
-- The `Partrec.rfind` elaboration + `Primrec₂.nat_iff` bridge are instance-heavy in this imported
-- environment; the default 200k heartbeats is just short.
/-- `Nat.size` is computable. `Nat.size_le : size m ≤ n ↔ m < 2 ^ n` makes `size m` the least `n`
with `m < 2 ^ n`, i.e. `Nat.rfind (fun n => m < 2 ^ n)`. -/
theorem computable_nat_size : Computable Nat.size := by
  -- `decide (· < ·)` is computable (bundled `Decidable` instance in `PrimrecRel`'s `∃`).
  have hlt : Computable fun p : ℕ × ℕ => decide (p.1 < p.2) := by
    have hpr := Primrec.nat_lt.choose_spec.to_comp
    have heq : (fun a : ℕ × ℕ => @decide _ (Primrec.nat_lt.choose a)) =
        fun p : ℕ × ℕ => decide (p.1 < p.2) := by funext a; congr 1
    rw [← heq]; exact hpr
  -- the search predicate `fun (m, n) => decide (m < 2 ^ n)` is computable
  have hpow : Computable fun p : ℕ × ℕ => 2 ^ p.2 := by
    have hp : Primrec₂ (fun m n : ℕ => m ^ n) :=
      Primrec₂.nat_iff.mpr (by simpa using Nat.Primrec.succ.comp Nat.Primrec.pow)
    exact (hp.comp (Primrec.const 2) Primrec.snd).to_comp
  have hpred : Computable fun p : ℕ × ℕ => decide (p.1 < 2 ^ p.2) :=
    hlt.comp (Computable.fst.pair hpow)
  -- the `rfind` search is `Partrec` and total, hence computes `Nat.size`
  have hpartrec : Partrec fun m => Nat.rfind fun n => Part.some (decide (m < 2 ^ n)) :=
    Partrec.rfind hpred.partrec
  have heq : (fun m => Nat.rfind fun n => Part.some (decide (m < 2 ^ n)))
      = fun m => (Part.some (Nat.size m) : Part ℕ) := by
    funext m
    apply Part.eq_some_iff.mpr
    rw [Nat.mem_rfind]
    constructor
    · simp [Nat.size_le.mp (le_refl (Nat.size m))]
    · intro k hk
      simp [not_lt.mpr (Nat.lt_size.mp hk)]
  exact hpartrec.of_eq (fun m => congrFun heq m)

/-- The bit-length program measure `codelen' = Nat.size ∘ encode` is computable. A named lemma, so
the heavy `computable_nat_size` proof term is not re-elaborated inside `K_bitlen_not_computable`. -/
theorem computable_codelen' : Computable codelen' :=
  computable_nat_size.comp Computable.encode

/-- Any program computing `x` bounds `K_bitlen x` by its own bit-length. -/
theorem K_bitlen_le {c : Code} {x : ℕ} (h : Computes c x) : K_bitlen x ≤ codelen' c :=
  Nat.sInf_le ⟨c, h, rfl⟩

-- Mark `codelen'` irreducible for the Berry proof: otherwise `whnf` unfolds `codelen'` to
-- `Nat.size (encode …)` and loops on `Nat.size`'s `binaryRec` during the `Computable` unification.
-- (Established `computable_codelen'`/`K_bitlen_le` above first, where `codelen'` must reduce.)
attribute [local irreducible] codelen'

/-- **Uncomputability of bit-length Kolmogorov complexity** (the paper's `r` in bits). Mirrors
Slice-1's `K_not_computable` with the bit-length measure `codelen'`, computable via
`computable_nat_size`. -/
theorem K_bitlen_not_computable : ¬ Computable K_bitlen := by
  intro hK
  -- `codelen'` is computable (the named lemma — avoids re-elaborating `computable_nat_size`).
  have hcodelen' : Computable codelen' := computable_codelen'
  -- `decide (· < ·)` computable.
  have hlt : Computable fun p : ℕ × ℕ => decide (p.1 < p.2) := by
    have hpr := Primrec.nat_lt.choose_spec.to_comp
    have heq : (fun a : ℕ × ℕ => @decide _ (Primrec.nat_lt.choose a)) =
        fun p : ℕ × ℕ => decide (p.1 < p.2) := by funext a; congr 1
    rw [← heq]; exact hpr
  -- the Berry predicate `codelen' c < K_bitlen x` is computable in `(c, x)`.
  have hg : Computable fun r : (Code × ℕ) × ℕ => decide (codelen' r.1.1 < K_bitlen r.2) := by
    have c1 : Computable fun r : (Code × ℕ) × ℕ => codelen' r.1.1 :=
      hcodelen'.comp (Computable.fst.comp Computable.fst)
    have c2 : Computable fun r : (Code × ℕ) × ℕ => K_bitlen r.2 := hK.comp Computable.snd
    exact hlt.comp (c1.pair c2)
  -- the Berry search (an `rfind`, ignoring the second argument) is `Partrec₂`.
  have hf : Partrec₂ (fun (c : Code) (_ : ℕ) =>
      Nat.rfind fun x => Part.some (decide (codelen' c < K_bitlen x))) :=
    Partrec.rfind (p := fun (q : Code × ℕ) (x : ℕ) =>
      Part.some (decide (codelen' q.1 < K_bitlen x))) hg.partrec
  obtain ⟨c₀, hc₀⟩ := fixed_point₂ hf
  obtain ⟨x₀, hx₀⟩ := K_bitlen_unbounded (codelen' c₀)
  set p₀ : ℕ →. Bool := fun x => Part.some (decide (codelen' c₀ < K_bitlen x)) with hp₀
  have heval : c₀.eval 0 = Nat.rfind p₀ := by rw [hc₀]
  have hdom : (Nat.rfind p₀).Dom := by
    rw [Nat.rfind_dom]
    exact ⟨x₀, by simp [hp₀, hx₀], fun {m} _ => trivial⟩
  set w : ℕ := (Nat.rfind p₀).get hdom with hw
  have hwspec : codelen' c₀ < K_bitlen w := by
    have h : true ∈ p₀ w := Nat.rfind_spec (Part.get_mem hdom)
    simpa [hp₀] using h
  have hcomp : Computes c₀ w := by
    rw [Computes, heval]
    exact Part.get_eq_iff_eq_some.mp hw.symm
  exact absurd (K_bitlen_le hcomp) (not_le.mpr hwspec)

end KolmogorovComplexity
