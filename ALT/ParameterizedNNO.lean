/-
Copyright (c) 2026 Mykola Palamarchuk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mykola Palamarchuk
-/
import Mathlib

-- Formal-check file, not Mathlib-destined: opt out of the house-style header linter.
set_option linter.style.header false

/-!
# Parameterized Natural Numbers Object + depth bound (Paper I, §4–§5)

Provenance: Paper I, §5.1 (why *parameterized*, not a *true*,
NNO), §5.2 (Definition 5.1 + Proposition 5.2 depth bound), with the capacity model of §3
(a subsystem has `≤ 2^K` distinguishable states) and §6's depth `M ≤ 2^{K−|s_code|}`.

Status: PROVED as finite-combinatorial statements on a finite state space. This is the
finite/structural core of §5.1–§5.2 — NOT the categorical (slice-category) universal property.

## Modeling the capacity split
Capacity `K` (bits) splits as code `r = |s_code|` and working memory `K − r = |s_work|`, so the
working state space `W` has `|W| = 2^{K−r}`. Here `K − r` is ℕ truncated subtraction: if `r ≥ K`
the bound degenerates to `|W| = 1` (no working bits ⇒ depth `0`). That is harmless — the regime of
interest is `r ≪ K`, where `K − r` is the genuine working-bit count.

## What this DOES establish
* `no_true_nno`: §5.1 — a finite-state subsystem admits **no true NNO**. A true NNO needs an
  infinite hierarchy of distinct successors (an injective orbit `n ↦ succ^[n] zero`); on finite `W`
  the Pigeonhole Principle forbids it (the successor must eventually cycle).
* `ParamNNO`: Definition 5.1's data — `zero`, `succ`, a depth `M`, and bullet 1 (the `M+1` iterates
  `zero, …, succ^M zero` are pairwise distinct, i.e. `orbit_injective`).
* `ParamNNO.bounded_recursor`: Definition 5.1 bullet 2 in **orbit form** — for any `(A, a, f)` a
  recursor `h` exists satisfying the depth-`M` recursion on the orbit `N_M`, and is unique on `N_M`.
  **Existence crucially uses `orbit_injective`** (well-definedness of `h` on `N_M`): without
  distinctness, two indices `k ≠ k'` could collide at one point of `W` while `f^[k] a ≠ f^[k'] a`,
  and no `h` would exist. This is exactly the §5.1–§5.2 link.
* `ParamNNO.depth_succ_le_card` / `…_two_pow`: Proposition 5.2's first (pigeonhole) bound —
  `M + 1 ≤ |W| = 2^{K−r}`, hence `M ≤ 2^{K−r}`.
* `cyclicParamNNO`: a concrete depth-`M` parameterized NNO on `ZMod (M+1)` (`succ = (· + 1)`) whose
  orbit enumerates `0,…,M` distinctly, **saturating** the bound (`depth + 1 = |ZMod (M+1)|`).
  Witnesses non-vacuity and the achievability behind §6's `M ≥ 2^{K−r}` (take `M + 1 = 2^{K−r}`).

## What this does NOT establish (stays in prose / other targets)
* NOT the full categorical universal property of Definition 5.1 (the slice-category formulation,
  the recursor as a morphism with a categorical uniqueness); we give the elementary orbit recursor.
* NOT `Rep(S)`, its products/exponentials, the CCC structure, or the §4.4 Rule-30 construction —
  that machinery is target **D2** (Cartesian-closedness).
* NOT Proposition 5.2's second (thermal) bound `exp(ΔE/kT)/|s_code|` — physical, prose.
* NOT the Gödel threshold (§5.3 / Def 6.1 / Thm 6.2: `M > g(T_S)`, depth-suffices-for-Gödel) —
  that is target **D4** + the Foundation port. NOT Curry–Howard–Lambek.
* `K` here is the §3 **capacity bit-count**, NOT Kolmogorov complexity (which is target **D3**);
  `r, K` stay abstract `ℕ`.

## Hypotheses: paper-stated vs added
* Paper-stated / faithful: finite state space (§3); Def 5.1 bullet 1 (distinct iterates) and
  bullet 2 (recursion, orbit form); the pigeonhole bound; §5.1 cycling.
* Added / modeling: rendering working memory as an abstract `Fintype W` with `|W| = 2^{K−r}` (and
  the `K = r + (K−r)` split); the `ZMod (M+1)` minimal instance (not the Rule-30 CA). No constant
  strengthened.
-/

namespace ParameterizedNNO

open Function

/-- Paper I §5.1: no finite-state subsystem admits a *true* NNO. A true NNO needs an infinite
hierarchy of distinct successors — an injective orbit `n ↦ succ^[n] zero` — which the Pigeonhole
Principle forbids on a finite state space (the successor must eventually cycle). -/
theorem no_true_nno {W : Type*} [Finite W] (zero : W) (succ : W → W) :
    ¬ Injective (fun n : ℕ => succ^[n] zero) :=
  not_injective_infinite_finite _

/-- Paper I Definition 5.1 (finite/combinatorial core): a depth-`M` parameterized NNO on a finite
state space `W`. The basepoint `zero`, successor `succ`, depth `M = depth`, and bullet 1 — the
`M+1` iterates `zero, succ zero, …, succ^M zero` are pairwise distinct (`orbit_injective`). The
defining recursion (bullet 2) is the derived `ParamNNO.bounded_recursor`. -/
structure ParamNNO (W : Type*) [Fintype W] where
  zero : W
  succ : W → W
  depth : ℕ
  orbit_injective : Injective (fun k : Fin (depth + 1) => succ^[k.val] zero)

variable {W : Type*} [Fintype W]

/-- The counter orbit `k ↦ succ^[k] zero` for `k ≤ M`; its image is `N_M`. -/
def ParamNNO.orbit (P : ParamNNO W) : Fin (P.depth + 1) → W := fun k => P.succ^[k.val] P.zero

theorem ParamNNO.orbit_inj (P : ParamNNO W) : Injective P.orbit := P.orbit_injective

/-- Proposition 5.2, first bound (pigeonhole): `M + 1 ≤ |W|`. -/
theorem ParamNNO.depth_succ_le_card (P : ParamNNO W) : P.depth + 1 ≤ Fintype.card W := by
  have h := Fintype.card_le_of_injective P.orbit P.orbit_inj
  simpa using h

/-- Proposition 5.2 / §6 depth bound: with working memory `K − r` bits (`|W| = 2^{K−r}`), the
parameterized-NNO depth satisfies `M + 1 ≤ 2^{K−r}` (hence `M ≤ 2^{K−r}`). -/
theorem ParamNNO.depth_succ_le_two_pow (P : ParamNNO W) (r K : ℕ)
    (hW : Fintype.card W = 2 ^ (K - r)) : P.depth + 1 ≤ 2 ^ (K - r) := by
  rw [← hW]; exact P.depth_succ_le_card

/-- The depth-`M` recursion on the orbit `N_M` (Def 5.1 bullet 2): `h zero = a` and
`h (succ^[k+1] zero) = f (h (succ^[k] zero))` for every `k < M`. -/
def ParamNNO.Recurses (P : ParamNNO W) {A : Type*} (a : A) (f : A → A) (h : W → A) : Prop :=
  h P.zero = a ∧ ∀ k : ℕ, k < P.depth → h (P.succ^[k + 1] P.zero) = f (h (P.succ^[k] P.zero))

/-- A recursor's values on the orbit are forced: `h (succ^[k] zero) = f^[k] a` for `k ≤ M`. -/
theorem ParamNNO.Recurses.orbit_eq {P : ParamNNO W} {A : Type*} {a : A} {f : A → A} {h : W → A}
    (hr : P.Recurses a f h) : ∀ k, k ≤ P.depth → h (P.succ^[k] P.zero) = f^[k] a := by
  intro k
  induction k with
  | zero => intro _; simpa using hr.1
  | succ k ih => intro hk; rw [hr.2 k (by omega), ih (by omega), Function.iterate_succ_apply']

/-- Paper I Definition 5.1 bullet 2 (orbit form, the §5.1–§5.2 link): for any `(A, a, f)` there is
a recursor `h` satisfying the depth-`M` recursion, and any two such recursors agree on `N_M`.

Existence **uses `orbit_injective`**: `h` is well-defined on `N_M` precisely because the `M+1`
iterates are distinct. Uniqueness on `N_M` does not need it (the recursion pins the values). -/
theorem ParamNNO.bounded_recursor (P : ParamNNO W) {A : Type*} (a : A) (f : A → A) :
    (∃ h : W → A, P.Recurses a f h) ∧
      ∀ h₁ h₂ : W → A, P.Recurses a f h₁ → P.Recurses a f h₂ →
        ∀ k, k ≤ P.depth → h₁ (P.succ^[k] P.zero) = h₂ (P.succ^[k] P.zero) := by
  classical
  haveI : Nonempty (Fin (P.depth + 1)) := ⟨0⟩
  -- The inverse of the (injective) orbit map recovers the index `k` of each orbit point.
  have hg : ∀ k : ℕ, k ≤ P.depth →
      (Function.invFun P.orbit (P.succ^[k] P.zero)).val = k := by
    intro k hk
    have hko : P.succ^[k] P.zero = P.orbit ⟨k, by omega⟩ := rfl
    rw [hko, Function.leftInverse_invFun P.orbit_inj ⟨k, by omega⟩]
  refine ⟨⟨fun w => f^[(Function.invFun P.orbit w).val] a, ?_, ?_⟩, ?_⟩
  · -- `h zero = a`
    change f^[(Function.invFun P.orbit (P.succ^[0] P.zero)).val] a = a
    rw [hg 0 (Nat.zero_le _)]
    simp
  · -- recursion step
    intro k hk
    change f^[(Function.invFun P.orbit (P.succ^[k + 1] P.zero)).val] a
        = f (f^[(Function.invFun P.orbit (P.succ^[k] P.zero)).val] a)
    rw [hg (k + 1) (by omega), hg k (by omega), Function.iterate_succ_apply']
  · -- uniqueness on the orbit
    intro h₁ h₂ hr₁ hr₂ k hk
    rw [hr₁.orbit_eq k hk, hr₂.orbit_eq k hk]

/-- A concrete depth-`M` parameterized NNO on `ZMod (M+1)` with `succ = (· + 1)`: the orbit
enumerates `0, 1, …, M` distinctly, saturating the pigeonhole bound (`depth + 1 = |ZMod (M+1)|`).
Witnesses non-vacuity and the achievability behind §6's `M ≥ 2^{K−r}` (take `M + 1 = 2^{K−r}`). -/
def cyclicParamNNO (M : ℕ) : ParamNNO (ZMod (M + 1)) where
  zero := 0
  succ := (· + 1)
  depth := M
  orbit_injective := by
    have key : ∀ j : ℕ, (fun x : ZMod (M + 1) => x + 1)^[j] 0 = (j : ZMod (M + 1)) := by
      intro j
      induction j with
      | zero => simp
      | succ j ih => rw [Function.iterate_succ_apply', ih]; push_cast; ring
    intro k₁ k₂ h
    simp only [key] at h
    have hval := congrArg ZMod.val h
    rw [ZMod.val_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt k₁.isLt,
      Nat.mod_eq_of_lt k₂.isLt] at hval
    exact Fin.ext hval

end ParameterizedNNO
