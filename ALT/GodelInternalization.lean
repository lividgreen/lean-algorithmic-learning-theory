/-
Copyright (c) 2026 Mykola Palamarchuk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mykola Palamarchuk
-/
import Mathlib
import ALT.GodelCore
import ALT.ParameterizedNNO

-- Formal-check file, not Mathlib-destined: opt out of the house-style linters.
set_option linter.style.header false
set_option linter.style.longLine false

/-!
# Internalizing the bounded proof relation (Paper I §6.3, Theorem 6.3, Levels L2a/L2b)

Provenance: Paper I, §4.6 (Proposition 4.5, minimality —
finite products + bounded recursor, no exponential), §5.4 (Proposition 5.4, the necessity
counterpart), §6.1–6.3 (Definition 6.1, Theorem 6.2, Theorem 6.3 the internalization).

This extends the Level-1 Gödel skeleton (`ALT/GodelCore.lean`, `…GodelThreshold.lean`,
`…Reflective.lean`) to the **concrete §6.3 internalization**, machine-checking an explicit capacity
polynomial. Gödel incompleteness stays the imported black box (the `GodelThreshold.Incompleteness`
hypothesis, discharged from Foundation in `ALT/GodelComplete.lean`); we do NOT re-prove it.
By Proposition 4.5 the whole construction lives in the finite-product + bounded-recursor fragment
`Rep₀(S)` — **no Cartesian-closed structure** is used here.

## The quantitative model (the point of this file)
For a Gödel number `g`, write `n := Nat.clog 2 (g+1)` — the bit-length of `g` (the size of the
Gödel sentence, §5.3). Two budgets enter (Definition 6.1), kept apart:
* `M_idx ≥ g` indexes the sentence (Level 1);
* `M_chk ≥ poly(g)` is the value range of proof codes the checker enumerates (the larger budget).

Capacities are **bit-lengths**: hosting depth `M_chk` costs working memory `|s_work| ≥ log₂ M_chk`.
The explicit capacity polynomial is `capacity n := 2 * n` (§6.3: `|s_work| = poly(n)`): with
`M_chk ≤ g^2` (a concrete `poly(g)`) we prove `M_chk + 1 ≤ 2 ^ (capacity n)` by `Nat`/`omega`
reasoning, and tie the necessity direction to the sharp pigeonhole `depth_succ_le_two_pow` of D1.
The bounded search ranges over `ProofCode M_chk := {p // p ≤ M_chk}` (a `Fintype`) and is the finite
fold along the orbit of the bounded recursor `cyclicParamNNO M_chk` of D1 — no exponential.

## What this DOES establish (the abstract conditional — axiom-clean)
* `BoundedChecker`: the abstract §6.3 interface — a `Formula` type, a decidable bounded proof
  relation `Prf : Formula → ℕ → Bool`, the size map `gnum`, a recursion budget `Mchk`, and the
  **soundness** field `Prf φ p = true → Derivable φ` (accepts ⇒ derivable — one direction).
* `Decide`/`decide_eq_true_iff`: the L2b decision morphism `Decide φ = ⋀_{p ≤ M_chk} ¬Prf(φ,p)` is
  total (a `Fintype` fold) and `Decide φ = true ↔ ∀ p ≤ M_chk, ¬Prf(φ,p)`.
* `decide_eq_true_iff_orbit`: the same fold expressed along the **recursor orbit** of
  `cyclicParamNNO M_chk` (`ProofCode` enumerated by the D1 orbit, valued by `ZMod.val`).
* `decide_godel` (the L2b ∧ L3 capstone): from `GodelThreshold.Incompleteness` (imported Gödel) and
  the soundness field, `Decide(G_{T_S}) = true` — Rep(S) decides bounded non-provability.
* `capacity_bound`: explicit `M_chk + 1 ≤ 2 ^ (capacity n)` for `M_chk ≤ g^2` (capacity polynomial).
* `proofCodes_embed`: `ProofCode M_chk ↪ S_work` once `M_chk + 1 ≤ 2^{|s_work|}` (i.e. `ProofCode
  ⊆ S_work`).
* `prop_5_4` (Proposition 5.4, necessity): a recursor on `W` with `|W| = 2^{|s_work|}` indexing `g`
  forces `|s_work| ≥ Nat.clog 2 (g+1)` — the two-sided threshold's lower edge, from D1's pigeonhole.
* `internalization` (Theorem 6.3, L1 ∧ L2b ∧ capacity bundled): the concrete §6.3 statement.

## What this does NOT establish (flagged)
* NOT Gödel incompleteness — imported (`GodelThreshold.Incompleteness`); discharged in
  `ALT/GodelComplete.lean`. NOT the exponential / Cartesian closure (Proposition 4.5: unused).
* `Formula` is kept abstract (the L2a *carving* of `Formula := {c ≤ M_chk ∧ Wff c}` as a subobject
  of `S_work` is a modeling choice deferred to the concrete witness); `gnum`/`Derivable` abstract.
* The concrete discharge of the `BoundedChecker` interface lives on the Foundation side
  (`ALT/GodelChecker.lean`, `paMinus_decides_bounded_nonprovability` — the axiom-clean `𝗣𝗔⁻`
  capstone; the earlier `𝗜𝚺₁` witnesses are retired): it cannot share this file
  because Foundation's root `Matrix.map` collides with umbrella-Mathlib's (the same Mathlib/Foundation
  import divide that keeps the Foundation-side files separate).

## Hypotheses: paper-stated vs added
* Paper-stated / faithful: the §6.3 `Prf`/`Decide` construction; Proposition 5.4; the two budgets;
  the capacity polynomial `poly(n)`; soundness (accepts ⇒ derivable).
* Added / modeling: `Formula`/`gnum`/`Derivable` abstract; the concrete `poly(g) := g^2` witness for
  `M_chk`; `capacity n := 2*n`; the recursor on `ZMod (M_chk+1)` (D1's `cyclicParamNNO`).
-/

namespace GodelInternalization

open ParameterizedNNO

/-! ### The proof-code index set and its recursor orbit -/

/-- §6.3: `ProofCode := {p ∈ S_work : p ≤ M_chk}`, the proof codes within the working budget.
A `Fintype` of cardinality `M_chk + 1`, in bijection with the orbit `Fin (M_chk+1)` of the bounded
recursor `cyclicParamNNO M_chk` (D1). -/
abbrev ProofCode (Mchk : ℕ) : Type := {p : ℕ // p ≤ Mchk}

/-- `ProofCode M_chk ≃ Fin (M_chk+1)`: the proof codes are exactly the recursor's orbit indices. -/
def proofCodeEquiv (Mchk : ℕ) : ProofCode Mchk ≃ Fin (Mchk + 1) where
  toFun p := ⟨p.1, by omega⟩
  invFun k := ⟨k.1, by omega⟩
  left_inv p := by cases p; rfl
  right_inv k := by cases k; rfl

instance (Mchk : ℕ) : Fintype (ProofCode Mchk) :=
  Fintype.ofEquiv (Fin (Mchk + 1)) (proofCodeEquiv Mchk).symm

theorem proofCodes_card (Mchk : ℕ) : Fintype.card (ProofCode Mchk) = Mchk + 1 := by
  rw [Fintype.card_congr (proofCodeEquiv Mchk), Fintype.card_fin]

/-- The cyclic recursor's orbit enumerates the proof codes: the `k`-th orbit element of
`cyclicParamNNO M_chk` has `ZMod.val` equal to `k`. This is the §6.3 statement that the bounded
search (`⋀_{p ≤ M_chk}`) is a finite fold along the orbit of the bounded recursor `N_{M_chk}`. -/
theorem cyclicParamNNO_orbit_val (M : ℕ) (k : Fin (M + 1)) :
    ZMod.val ((cyclicParamNNO M).orbit k) = k.val := by
  have key : ∀ j : ℕ,
      (cyclicParamNNO M).succ^[j] (cyclicParamNNO M).zero = (j : ZMod (M + 1)) := by
    intro j
    induction j with
    | zero => simp [cyclicParamNNO]
    | succ j ih =>
        rw [Function.iterate_succ_apply', ih]
        change (j : ZMod (M + 1)) + 1 = ((j + 1 : ℕ) : ZMod (M + 1))
        push_cast; ring
  change ZMod.val ((cyclicParamNNO M).succ^[k.val] (cyclicParamNNO M).zero) = k.val
  rw [key k.val, ZMod.val_natCast, Nat.mod_eq_of_lt k.isLt]

/-! ### The bounded-proof interface and the L2b decision morphism -/

/-- The abstract §6.3 bounded-proof interface (Theorem 6.3, L2a inputs): a `Formula` type with a
size map `gnum`, an internal `Derivable` predicate, a recursion budget `Mchk`, and a **decidable**
bounded proof relation `Prf φ p` ("`p` is a proof of `φ`," codes `p ≤ Mchk`) that is **sound** —
accepting a code implies derivability (one direction; the only direction §6.3 L2b needs). -/
structure BoundedChecker where
  Formula : Type
  gnum : Formula → ℕ
  Derivable : Formula → Prop
  Mchk : ℕ
  Prf : Formula → ℕ → Bool
  sound : ∀ φ p, Prf φ p = true → Derivable φ

variable (C : BoundedChecker)

/-- §6.3 L2b — the decision morphism `Decide(φ) = ⋀_{p ≤ M_chk} ¬Prf(φ, p)`. Total by construction:
a decidable `Fintype` fold over `ProofCode M_chk` (finite products + bounded recursor — no
exponential, Proposition 4.5). -/
def Decide (φ : C.Formula) : Bool :=
  decide (∀ p : ProofCode C.Mchk, C.Prf φ p.val = false)

/-- `Decide φ = true ↔ no proof code within budget is accepted` — the defining property of the L2b
bounded-non-provability decision. -/
theorem decide_eq_true_iff (φ : C.Formula) :
    Decide C φ = true ↔ ∀ p, p ≤ C.Mchk → C.Prf φ p = false := by
  rw [Decide, decide_eq_true_eq]
  exact ⟨fun h p hp => h ⟨p, hp⟩, fun h p => h p.1 p.2⟩

/-- The L2b fold as a finite fold **along the recursor orbit** of `cyclicParamNNO M_chk` (D1):
`Decide φ = true` iff `¬Prf(φ, p)` for every `p` enumerated as `ZMod.val` of an orbit element. This
is the precise §6.3 sense in which the bounded search is "a single finite fold along the orbit of
the bounded recursor `N_{M_chk}`". -/
theorem decide_eq_true_iff_orbit (φ : C.Formula) :
    Decide C φ = true ↔
      ∀ k : Fin (C.Mchk + 1), C.Prf φ (ZMod.val ((cyclicParamNNO C.Mchk).orbit k)) = false := by
  rw [decide_eq_true_iff]
  simp only [cyclicParamNNO_orbit_val]
  exact ⟨fun h k => h k.val (by omega), fun h m hm => h ⟨m, by omega⟩⟩

/-- §6.3 L2b ∧ L3 (the capstone): from the imported Gödel fact `GodelThreshold.Incompleteness` (a
representable sentence `G`, true and **not derivable**) and the checker's soundness, the decision
morphism returns `true` on `G`: Rep(S) **decides bounded non-provability** of `G_{T_S}`. The step
from "no bounded proof" (decided here) to "no proof of any length" is L3, the imported theorem —
used only as the hypothesis `¬ Derivable G`. -/
theorem decide_godel (True_ : C.Formula → Prop) (gTS : ℕ)
    (hInc : GodelThreshold.Incompleteness C.gnum C.Derivable True_ gTS) :
    ∃ G, C.gnum G = gTS ∧ True_ G ∧ Decide C G = true := by
  obtain ⟨G, hg, htrue, hnd⟩ := hInc
  refine ⟨G, hg, htrue, ?_⟩
  rw [decide_eq_true_iff]
  intro p _
  by_contra h
  exact hnd (C.sound G p (by simpa using h))

/-! ### The explicit capacity polynomial (§6.3 / Theorem 6.2) and Proposition 5.4 -/

/-- The explicit §6.3 capacity polynomial `P(n) = 2n` (work-memory bit-count): for the concrete
proof-code budget `M_chk ≤ g^2` it hosts the recursor of depth `M_chk` (`M_chk + 1 ≤ 2^{P(n)}`). -/
def capacity (n : ℕ) : ℕ := 2 * n

/-- Explicit capacity bound (Theorem 6.2 / §6.3): with `M_chk ≤ g^2` (a concrete `poly(g)`), the
recursor depth `M_chk` is hosted by `capacity n = 2n` work bits, `n := Nat.clog 2 (g+1)` the size of
the Gödel sentence: `M_chk + 1 ≤ 2 ^ (capacity n)`. Pure `Nat`/`omega` reasoning. -/
theorem capacity_bound (g Mchk : ℕ) (hM : Mchk ≤ g ^ 2) :
    Mchk + 1 ≤ 2 ^ capacity (Nat.clog 2 (g + 1)) := by
  set n := Nat.clog 2 (g + 1) with hn
  have hg : g + 1 ≤ 2 ^ n := Nat.le_pow_clog (by norm_num) _
  have hpow : (2 : ℕ) ^ capacity n = (2 ^ n) ^ 2 := by
    rw [capacity, two_mul, pow_add, sq]
  calc Mchk + 1 ≤ g ^ 2 + 1 := by omega
    _ ≤ (g + 1) ^ 2 := by nlinarith
    _ ≤ (2 ^ n) ^ 2 := by nlinarith [hg, Nat.zero_le g]
    _ = 2 ^ capacity n := hpow.symm

/-- §5.4 / §6.3 — the per-proof **verification workspace** is within the linear capacity `2n`. Every
candidate proof code `p ≤ M_chk` (hence the workspace to *hold* one candidate proof, the part that
was previously flagged "not yet bounded") fits in `capacity n = 2n` work bits, `n := Nat.clog 2
(g+1)`, given the concrete budget `M_chk ≤ g^2`. So the per-proof workspace is `poly(n)` — indeed
within the *same* `2n` as the syntax objects and the recursor — and the two-sidedness of Proposition
5.4 is tight up to a constant, not open at the verification step. (The remaining `Δ₀`/poly-time check
of a held candidate, Buss 1986, runs in `poly(n)` scratch — paper-level.) -/
theorem proofcode_workspace_bound (g Mchk : ℕ) (hM : Mchk ≤ g ^ 2) {p : ℕ} (hp : p ≤ Mchk) :
    Nat.clog 2 (p + 1) ≤ capacity (Nat.clog 2 (g + 1)) := by
  calc Nat.clog 2 (p + 1)
      ≤ Nat.clog 2 (Mchk + 1) := Nat.clog_mono_right _ (by omega)
    _ ≤ Nat.clog 2 (2 ^ capacity (Nat.clog 2 (g + 1))) :=
          Nat.clog_mono_right _ (capacity_bound g Mchk hM)
    _ = capacity (Nat.clog 2 (g + 1)) := Nat.clog_pow _ _ (by norm_num)

/-- §6.3 "`ProofCode ⊆ S_work`": once the work memory `W` (with `|W| = 2^{|s_work|}`) is large
enough to host the recursor depth `M_chk` (`M_chk + 1 ≤ 2^{|s_work|}`), the proof codes embed into
it. `Fintype.card (ProofCode M_chk) = M_chk + 1 ≤ |W|`. -/
theorem proofCodes_embed (Mchk sworkBits : ℕ) {W : Type*} [Fintype W]
    (hW : Fintype.card W = 2 ^ sworkBits) (h : Mchk + 1 ≤ 2 ^ sworkBits) :
    Nonempty (ProofCode Mchk ↪ W) := by
  rw [Function.Embedding.nonempty_iff_card_le, proofCodes_card, hW]
  exact h

/-- **Proposition 5.4 (Necessity of capacity; two-sided threshold).** A bounded recursor on work
memory `W` with `|W| = 2^{|s_work|}` whose indexing depth reaches `g` (`g ≤ P.depth`, i.e. `g` is
in range, Level 1) forces `|s_work| ≥ Nat.clog 2 (g+1)`. Below this capacity no decoupled subsystem
even indexes `G_{T_S}`, hence none of the Gödel phenomenon of §6. Rides the machine-checked
pigeonhole `depth_succ_le_two_pow` (D1). -/
theorem prop_5_4 {W : Type*} [Fintype W] (P : ParamNNO W) (sworkBits g : ℕ)
    (hW : Fintype.card W = 2 ^ sworkBits) (hg : g ≤ P.depth) :
    Nat.clog 2 (g + 1) ≤ sworkBits := by
  have hd : P.depth + 1 ≤ 2 ^ sworkBits := P.depth_succ_le_two_pow 0 sworkBits (by simpa using hW)
  have hgw : g + 1 ≤ 2 ^ sworkBits := by omega
  calc Nat.clog 2 (g + 1) ≤ Nat.clog 2 (2 ^ sworkBits) := Nat.clog_mono_right _ hgw
    _ = sworkBits := Nat.clog_pow _ _ (by norm_num)

/-! ### Theorem 6.3 (the bundled internalization: L1 ∧ L2b ∧ capacity) -/

/-- **Theorem 6.3 (Internalization), Levels L1 ∧ L2b with the capacity bound.** For a bounded
checker with budget `M_chk ≤ g^2`, indexing budget reaching `g` (`g ≤ M_chk`, so `g` is in range —
L1), under imported incompleteness at `gTS = g`:
* **(L1)** `g ≤ M_chk`: the Gödel number is a value of the recursor (in range);
* **(L2b)** `Decide(G) = true`: Rep(S) decides bounded non-provability of `G`;
* **(capacity)** `M_chk + 1 ≤ 2 ^ (capacity n)`, `n := Nat.clog 2 (g+1)`: hosted by `poly(n)` bits.
Uses finite products + the bounded recursor only (Proposition 4.5); incompleteness imported
(L3/L4). -/
theorem internalization (True_ : C.Formula → Prop) (g : ℕ)
    (hidx : g ≤ C.Mchk) (hpoly : C.Mchk ≤ g ^ 2)
    (hInc : GodelThreshold.Incompleteness C.gnum C.Derivable True_ g) :
    ∃ G, C.gnum G = g ∧ True_ G ∧
      g ≤ C.Mchk ∧
      Decide C G = true ∧
      C.Mchk + 1 ≤ 2 ^ capacity (Nat.clog 2 (g + 1)) := by
  obtain ⟨G, hg, htrue, hdec⟩ := decide_godel C True_ g hInc
  exact ⟨G, hg, htrue, hidx, hdec, capacity_bound g C.Mchk hpoly⟩

end GodelInternalization
