/-
Copyright (c) 2026 Mykola Palamarchuk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mykola Palamarchuk
-/
module

public import Mathlib.Data.Nat.Size
public import ALT.AdditiveComplexity

-- Formal-check file, not Mathlib-destined: opt out of the house-style header linter.
set_option linter.style.header false

/-!
# The data rate of the additive complexity `KE` is bounded away from one bit per bit

Provenance: [Discovery] §1.1 (the `2^{−K}` prior over a fixed reference machine). Extends
`ALT/AdditiveComplexity.lean` (`E`, `elen`, `KE`, `minCode`, `card_KE_le`) with a node-counted
refinement of the counting bound.

## What this establishes
* `nodes`: the AST-node count of a `Code`, with `elen c = 3 * nodes c`
  (`elen_eq_three_mul_nodes`) — the serialization spends exactly three bits per node.
* `codesOfNodes n`: the finite set of codes with exactly `n` nodes (`mem_codesOfNodes`).
* `card_codesOfNodes_le`: the counted codes grow strictly slower than the `8ⁿ` three bits could
  carry — `10 · 20ⁿ · |codesOfNodes n| ≤ 11 · 159ⁿ`, i.e. at most `(11/10)·(159/20)ⁿ` codes of `n`
  nodes, against a ceiling of `8ⁿ`.
* `sum_card_codesOfNodes_le`: the same bound, summed over all node-counts up to `N`.
* `card_KE_le_nodes`: the counting bound on `KE`, reindexed through node-counts rather than raw
  bit-strings.
* `KE_data_rate`: **the data rate of `KE` is bounded away from one bit per bit** — for every
  constant `c`, some `x` has `500 · KE x > 501 · Nat.size x + 500 · c`. Consequently no constant
  `c_μ` makes `KE x ≤ −log₂ μ(x) + c_μ` for every `x` at the computable measure
  `μ(x) := 2^{−⌈(1 + 1/500)·Nat.size x⌉ − 1}` (whose total mass is under one) — `KE` is not an
  ideal code even for its own computable measures.

## Why node counts, not raw bit-strings
`card_KE_le` (`AdditiveComplexity.lean`) bounds `{x | KE x ≤ L}` by the bit-strings of length at
most `L`, of which there are `< 2^(L+1)` — the bound a general prefix code would need. `E`'s
serialization is tighter than that: its opcode alternates a 1-in-8 fixed choice among a 3-bit
budget with a binary/leaf structural constraint, so the codes of `n` nodes number only
`Θ((1 + 4√3)ⁿ) ≈ Θ(7.928ⁿ)`, not `Θ(8ⁿ)`. This file makes that gap a machine-checked bound and
draws the consequence for `KE`'s data rate.

## Hypotheses: paper-stated vs added
* Paper-stated / faithful: none — this is a boundary result about the artifact's own carrier `KE`,
  not a claim any paper currently makes.
* Added / modeling: the fixed serialization `E` and its opcode budget (inherited from
  `AdditiveComplexity.lean`).
-/


@[expose] public section

namespace CodeDataRate

open Nat.Partrec Nat.Partrec.Code AdditiveComplexity

/-- Codes carry decidable equality (via their `Denumerable` encoding), needed to form `Finset
Code`s below. -/
instance : DecidableEq Code := Encodable.decidableEqOfEncodable Code

/-- The number of AST nodes of a code: one per constructor application. -/
def nodes : Code → ℕ
  | .zero | .succ | .left | .right => 1
  | .pair cf cg | .comp cf cg | .prec cf cg => 1 + nodes cf + nodes cg
  | .rfind' cf => 1 + nodes cf

/-- `E` spends exactly three bits per AST node. -/
theorem elen_eq_three_mul_nodes (c : Code) : elen c = 3 * nodes c := by
  induction c with
  | zero => rfl
  | succ => rfl
  | left => rfl
  | right => rfl
  | pair cf cg ihf ihg => simp only [E_len_pair, nodes, ihf, ihg]; ring
  | comp cf cg ihf ihg => simp only [E_len_comp, nodes, ihf, ihg]; ring
  | prec cf cg ihf ihg =>
      have h : elen (Code.prec cf cg) = 3 + elen cf + elen cg := by
        simp only [elen, E, List.length_append, List.length_cons, List.length_nil]
      simp only [h, nodes, ihf, ihg]; ring
  | rfind' cf ihf =>
      have h : elen (Code.rfind' cf) = 3 + elen cf := by
        simp only [elen, E, List.length_append, List.length_cons, List.length_nil]
      simp only [h, nodes, ihf]; ring

/-- Every code has at least one node. -/
private theorem one_le_nodes (c : Code) : 1 ≤ nodes c := by
  cases c <;> simp [nodes] <;> omega

/-! ## Counting codes by node count

`codesOfNodes n` enumerates the codes with exactly `n` nodes. It is built with an explicit fuel
parameter (`codesOfNodesFuel`) so the recursive calls are on a strictly smaller *first* argument —
plain structural recursion, avoiding a well-founded-recursion obligation over a `Finset.biUnion`
closure that carries no bound on its argument. `fuel = n` always suffices
(`mem_codesOfNodesFuel`), which is all `codesOfNodes` ever needs. -/

/-- Codes of exactly `n` AST nodes, computed with `fuel` levels of recursion depth; correct once
`fuel ≥ n` (`mem_codesOfNodesFuel`). -/
def codesOfNodesFuel : ℕ → ℕ → Finset Code
  | 0, _ => ∅
  | _ + 1, 0 => ∅
  | _ + 1, 1 => {Code.zero, Code.succ, Code.left, Code.right}
  | fuel + 1, n + 2 =>
      (codesOfNodesFuel fuel (n + 1)).image Code.rfind' ∪
      (Finset.antidiagonal (n + 1)).biUnion (fun ij =>
        ((codesOfNodesFuel fuel ij.1 ×ˢ codesOfNodesFuel fuel ij.2).image
          fun p => Code.pair p.1 p.2) ∪
        ((codesOfNodesFuel fuel ij.1 ×ˢ codesOfNodesFuel fuel ij.2).image
          fun p => Code.comp p.1 p.2) ∪
        ((codesOfNodesFuel fuel ij.1 ×ˢ codesOfNodesFuel fuel ij.2).image
          fun p => Code.prec p.1 p.2))

/-- Codes with exactly `n` AST nodes. `n` fuel levels always suffice (`mem_codesOfNodes`). -/
def codesOfNodes (n : ℕ) : Finset Code := codesOfNodesFuel n n

/-- Sufficient fuel: a code is found at its own node count once the fuel is at least that many. -/
private theorem mem_codesOfNodesFuel : ∀ (c : Code) {fuel : ℕ}, nodes c ≤ fuel →
    c ∈ codesOfNodesFuel fuel (nodes c) := by
  intro c
  induction c with
  | zero => intro fuel h; simp only [nodes] at h
            obtain ⟨f, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : fuel ≠ 0)
            simp [nodes, codesOfNodesFuel]
  | succ => intro fuel h; simp only [nodes] at h
            obtain ⟨f, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : fuel ≠ 0)
            simp [nodes, codesOfNodesFuel]
  | left => intro fuel h; simp only [nodes] at h
            obtain ⟨f, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : fuel ≠ 0)
            simp [nodes, codesOfNodesFuel]
  | right => intro fuel h; simp only [nodes] at h
             obtain ⟨f, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : fuel ≠ 0)
             simp [nodes, codesOfNodesFuel]
  | pair cf cg ihf ihg =>
      intro fuel h
      have h1 := one_le_nodes cf
      have h2 := one_le_nodes cg
      simp only [nodes] at h
      obtain ⟨f, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : fuel ≠ 0)
      have hn : nodes (Code.pair cf cg) = (nodes cf + nodes cg - 1) + 2 := by
        simp only [nodes]; omega
      rw [hn, codesOfNodesFuel]
      have hij : (nodes cf, nodes cg) ∈ Finset.antidiagonal (nodes cf + nodes cg - 1 + 1) := by
        simp [Finset.mem_antidiagonal]; omega
      apply Finset.mem_union_right
      apply Finset.mem_biUnion.mpr
      refine ⟨(nodes cf, nodes cg), hij, ?_⟩
      apply Finset.mem_union_left
      apply Finset.mem_union_left
      apply Finset.mem_image.mpr
      refine ⟨(cf, cg), ?_, rfl⟩
      apply Finset.mem_product.mpr
      exact ⟨ihf (by omega), ihg (by omega)⟩
  | comp cf cg ihf ihg =>
      intro fuel h
      have h1 := one_le_nodes cf
      have h2 := one_le_nodes cg
      simp only [nodes] at h
      obtain ⟨f, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : fuel ≠ 0)
      have hn : nodes (Code.comp cf cg) = (nodes cf + nodes cg - 1) + 2 := by
        simp only [nodes]; omega
      rw [hn, codesOfNodesFuel]
      have hij : (nodes cf, nodes cg) ∈ Finset.antidiagonal (nodes cf + nodes cg - 1 + 1) := by
        simp [Finset.mem_antidiagonal]; omega
      apply Finset.mem_union_right
      apply Finset.mem_biUnion.mpr
      refine ⟨(nodes cf, nodes cg), hij, ?_⟩
      apply Finset.mem_union_left
      apply Finset.mem_union_right
      apply Finset.mem_image.mpr
      refine ⟨(cf, cg), ?_, rfl⟩
      apply Finset.mem_product.mpr
      exact ⟨ihf (by omega), ihg (by omega)⟩
  | prec cf cg ihf ihg =>
      intro fuel h
      have h1 := one_le_nodes cf
      have h2 := one_le_nodes cg
      simp only [nodes] at h
      obtain ⟨f, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : fuel ≠ 0)
      have hn : nodes (Code.prec cf cg) = (nodes cf + nodes cg - 1) + 2 := by
        simp only [nodes]; omega
      rw [hn, codesOfNodesFuel]
      have hij : (nodes cf, nodes cg) ∈ Finset.antidiagonal (nodes cf + nodes cg - 1 + 1) := by
        simp [Finset.mem_antidiagonal]; omega
      apply Finset.mem_union_right
      apply Finset.mem_biUnion.mpr
      refine ⟨(nodes cf, nodes cg), hij, ?_⟩
      apply Finset.mem_union_right
      apply Finset.mem_image.mpr
      refine ⟨(cf, cg), ?_, rfl⟩
      apply Finset.mem_product.mpr
      exact ⟨ihf (by omega), ihg (by omega)⟩
  | rfind' cf ihf =>
      intro fuel h
      have h1 := one_le_nodes cf
      simp only [nodes] at h
      obtain ⟨f, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : fuel ≠ 0)
      have hn : nodes (Code.rfind' cf) = (nodes cf - 1) + 2 := by
        simp only [nodes]; omega
      rw [hn, codesOfNodesFuel]
      have heq : nodes cf - 1 + 1 = nodes cf := by omega
      rw [heq]
      apply Finset.mem_union_left
      apply Finset.mem_image.mpr
      exact ⟨cf, ihf (by omega), rfl⟩

/-- **`codesOfNodes` finds every code at its own node count.** -/
theorem mem_codesOfNodes (c : Code) : c ∈ codesOfNodes (nodes c) :=
  mem_codesOfNodesFuel c (le_refl _)

/-- Extra fuel beyond what is needed does not change the result: `codesOfNodesFuel` at any two
sufficient fuel levels agree. -/
private theorem codesOfNodesFuel_eq_of_le : ∀ (m : ℕ) {fuel fuel' : ℕ}, m ≤ fuel → m ≤ fuel' →
    codesOfNodesFuel fuel m = codesOfNodesFuel fuel' m := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro fuel fuel' hf hf'
    match m, hf, hf' with
    | 0, _, _ => rcases fuel with _ | f <;> rcases fuel' with _ | f' <;> rfl
    | 1, hf, hf' =>
        obtain ⟨f, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show fuel ≠ 0 by omega)
        obtain ⟨f', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show fuel' ≠ 0 by omega)
        rfl
    | n + 2, hf, hf' =>
        obtain ⟨f, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show fuel ≠ 0 by omega)
        obtain ⟨f', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show fuel' ≠ 0 by omega)
        simp only [codesOfNodesFuel]
        have e1 : codesOfNodesFuel f (n + 1) = codesOfNodesFuel f' (n + 1) :=
          ih (n + 1) (by omega) (by omega) (by omega)
        rw [e1]
        congr 1
        apply Finset.biUnion_congr rfl
        intro ij hij
        have hb := Finset.mem_antidiagonal.mp hij
        have e2 : codesOfNodesFuel f ij.1 = codesOfNodesFuel f' ij.1 :=
          ih ij.1 (by omega) (by omega) (by omega)
        have e3 : codesOfNodesFuel f ij.2 = codesOfNodesFuel f' ij.2 :=
          ih ij.2 (by omega) (by omega) (by omega)
        rw [e2, e3]

/-- **The recursive cardinality bound.** A code with `n + 2` nodes is either `rfind'` applied to
an `(n + 1)`-node code, or a binary node (`pair`/`comp`/`prec`) over two smaller codes whose node
counts sum to `n + 1`. -/
private theorem card_codesOfNodes_add_two_le (n : ℕ) :
    (codesOfNodes (n + 2)).card ≤ (codesOfNodes (n + 1)).card +
      3 * ∑ ij ∈ Finset.antidiagonal (n + 1),
        (codesOfNodes ij.1).card * (codesOfNodes ij.2).card := by
  have hu0 : codesOfNodes (n + 2) =
      (codesOfNodes (n + 1)).image Code.rfind' ∪
      (Finset.antidiagonal (n + 1)).biUnion (fun ij =>
        ((codesOfNodesFuel (n + 1) ij.1 ×ˢ codesOfNodesFuel (n + 1) ij.2).image
          fun p => Code.pair p.1 p.2) ∪
        ((codesOfNodesFuel (n + 1) ij.1 ×ˢ codesOfNodesFuel (n + 1) ij.2).image
          fun p => Code.comp p.1 p.2) ∪
        ((codesOfNodesFuel (n + 1) ij.1 ×ˢ codesOfNodesFuel (n + 1) ij.2).image
          fun p => Code.prec p.1 p.2)) := rfl
  have hu : codesOfNodes (n + 2) =
      (codesOfNodes (n + 1)).image Code.rfind' ∪
      (Finset.antidiagonal (n + 1)).biUnion (fun ij =>
        ((codesOfNodes ij.1 ×ˢ codesOfNodes ij.2).image fun p => Code.pair p.1 p.2) ∪
        ((codesOfNodes ij.1 ×ˢ codesOfNodes ij.2).image fun p => Code.comp p.1 p.2) ∪
        ((codesOfNodes ij.1 ×ˢ codesOfNodes ij.2).image fun p => Code.prec p.1 p.2)) := by
    rw [hu0]
    congr 1
    apply Finset.biUnion_congr rfl
    intro ij hij
    have hb := Finset.mem_antidiagonal.mp hij
    have e1 : codesOfNodesFuel (n + 1) ij.1 = codesOfNodes ij.1 :=
      codesOfNodesFuel_eq_of_le ij.1 (by omega) (le_refl _)
    have e2 : codesOfNodesFuel (n + 1) ij.2 = codesOfNodes ij.2 :=
      codesOfNodesFuel_eq_of_le ij.2 (by omega) (le_refl _)
    rw [e1, e2]
  rw [hu]
  refine (Finset.card_union_le _ _).trans (Nat.add_le_add Finset.card_image_le ?_)
  refine Finset.card_biUnion_le.trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum (fun ij _ => ?_)
  have himg : ∀ f : Code × Code → Code,
      ((codesOfNodes ij.1 ×ˢ codesOfNodes ij.2).image f).card
        ≤ (codesOfNodes ij.1).card * (codesOfNodes ij.2).card := fun f =>
    Finset.card_image_le.trans_eq (Finset.card_product _ _)
  have h1 := himg (fun p => Code.pair p.1 p.2)
  have h2 := himg (fun p => Code.comp p.1 p.2)
  have h3 := himg (fun p => Code.prec p.1 p.2)
  have h4 := Finset.card_union_le
      (((codesOfNodes ij.1 ×ˢ codesOfNodes ij.2).image fun p : Code × Code => Code.pair p.1 p.2) ∪
        ((codesOfNodes ij.1 ×ˢ codesOfNodes ij.2).image fun p : Code × Code => Code.comp p.1 p.2))
      ((codesOfNodes ij.1 ×ˢ codesOfNodes ij.2).image fun p : Code × Code => Code.prec p.1 p.2)
  have h5 := Finset.card_union_le
      ((codesOfNodes ij.1 ×ˢ codesOfNodes ij.2).image fun p : Code × Code => Code.pair p.1 p.2)
      ((codesOfNodes ij.1 ×ˢ codesOfNodes ij.2).image fun p : Code × Code => Code.comp p.1 p.2)
  omega

private theorem codesOfNodes_zero : codesOfNodes 0 = ∅ := rfl

private theorem card_codesOfNodes_one : (codesOfNodes 1).card = 4 := by decide

/-! ## The growth bound

A truncated-Cauchy-square inequality (`sum_antidiagonal_sq_le`) turns the recursive cardinality
bound into a bound on the weighted partial sums `∑ (codesOfNodes n).card · zⁿ`, uniformly `≤ 11/10`
at `z = 20/159`; the pointwise and tail-sum growth bounds follow. -/

/-- Truncated Cauchy square: for nonnegative `g`, the antidiagonal cross terms up to `N` are
bounded by the square of the partial sum up to `N`. -/
private theorem sum_antidiagonal_sq_le (g : ℕ → ℚ) (hg : ∀ i, 0 ≤ g i) (N : ℕ) :
    ∑ m ∈ Finset.range (N + 1), ∑ ij ∈ Finset.antidiagonal m, g ij.1 * g ij.2
      ≤ (∑ k ∈ Finset.range (N + 1), g k) ^ 2 := by
  have hantidiag : ∀ m, ∑ ij ∈ Finset.antidiagonal m, g ij.1 * g ij.2
      = ∑ k ∈ Finset.range (m + 1), g k * g (m - k) := fun m =>
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun a b => g a * g b) m
  simp_rw [hantidiag]
  have hflip := Finset.sum_range_diag_flip (N + 1) (fun k l => g k * g l)
  rw [hflip]
  have hsub : ∑ m ∈ Finset.range (N + 1), ∑ k ∈ Finset.range (N + 1 - m), g m * g k
      ≤ ∑ m ∈ Finset.range (N + 1), g m * ∑ k ∈ Finset.range (N + 1), g k := by
    apply Finset.sum_le_sum
    intro m _
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro x hx
      simp only [Finset.mem_range] at hx ⊢
      omega
    · intro k _ _
      exact mul_nonneg (hg m) (hg k)
  refine hsub.trans ?_
  rw [← Finset.sum_mul, sq]

/-- The weight of the `n`-node codes at `z = 20/159`. -/
private def g (n : ℕ) : ℚ := (codesOfNodes n).card * (20 / 159 : ℚ) ^ n

private theorem g_nonneg (n : ℕ) : 0 ≤ g n := by unfold g; positivity

private theorem g_zero : g 0 = 0 := by simp [g, codesOfNodes_zero]

private theorem g_one : g 1 = 4 * (20 / 159 : ℚ) := by
  simp only [g, card_codesOfNodes_one, pow_one]
  norm_num

/-- Termwise recursive bound on `g`, uniform in `i` via an indicator for the leaf base case. -/
private theorem g_step (i : ℕ) : g (i + 1) ≤
    (if i = 0 then 4 * (20 / 159 : ℚ) else 0) + (20 / 159 : ℚ) * g i +
      3 * (20 / 159 : ℚ) * ∑ ij ∈ Finset.antidiagonal i, g ij.1 * g ij.2 := by
  rcases eq_or_ne i 0 with hi | hi
  · subst hi
    simp [g_one, g_zero]
  · obtain ⟨i', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hi
    simp only [Nat.succ_eq_add_one]
    rw [ite_eq_right (by omega)]
    have hcard := card_codesOfNodes_add_two_le i'
    have hcard' : ((codesOfNodes (i' + 1 + 1)).card : ℚ) ≤ ((codesOfNodes (i' + 1)).card : ℚ) +
        3 * ∑ ij ∈ Finset.antidiagonal (i' + 1),
          ((codesOfNodes ij.1).card : ℚ) * (codesOfNodes ij.2).card := by
      exact_mod_cast hcard
    have step1 : g (i' + 1 + 1) ≤
        (((codesOfNodes (i' + 1)).card : ℚ) + 3 * ∑ ij ∈ Finset.antidiagonal (i' + 1),
          ((codesOfNodes ij.1).card : ℚ) * (codesOfNodes ij.2).card) *
        (20 / 159 : ℚ) ^ (i' + 1 + 1) := by
      have hg : g (i' + 1 + 1) =
          ((codesOfNodes (i' + 1 + 1)).card : ℚ) * (20 / 159 : ℚ) ^ (i' + 1 + 1) := rfl
      rw [hg]
      exact mul_le_mul_of_nonneg_right hcard' (by positivity)
    refine step1.trans ?_
    have hexpand : (((codesOfNodes (i' + 1)).card : ℚ) + 3 * ∑ ij ∈ Finset.antidiagonal (i' + 1),
          ((codesOfNodes ij.1).card : ℚ) * (codesOfNodes ij.2).card) *
        (20 / 159 : ℚ) ^ (i' + 1 + 1)
        = (20 / 159 : ℚ) * g (i' + 1) + 3 * (20 / 159 : ℚ) *
          ∑ ij ∈ Finset.antidiagonal (i' + 1), g ij.1 * g ij.2 := by
      rw [add_mul]
      congr 1
      · change ((codesOfNodes (i' + 1)).card : ℚ) * (20 / 159 : ℚ) ^ (i' + 1 + 1)
            = (20 / 159 : ℚ) * (((codesOfNodes (i' + 1)).card : ℚ) * (20 / 159 : ℚ) ^ (i' + 1))
        ring
      · rw [Finset.mul_sum, Finset.sum_mul, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro ij hij
        have hb := Finset.mem_antidiagonal.mp hij
        change 3 * (((codesOfNodes ij.1).card : ℚ) * (codesOfNodes ij.2).card) *
              (20 / 159 : ℚ) ^ (i' + 1 + 1)
            = 3 * (20 / 159 : ℚ) *
              (((codesOfNodes ij.1).card : ℚ) * (20 / 159 : ℚ) ^ ij.1 *
                (((codesOfNodes ij.2).card : ℚ) * (20 / 159 : ℚ) ^ ij.2))
        have hpoweq : (20 / 159 : ℚ) ^ (i' + 1 + 1) =
            (20 / 159 : ℚ) ^ ij.1 * (20 / 159 : ℚ) ^ ij.2 * (20 / 159 : ℚ) := by
          rw [← pow_add, ← pow_succ]
          congr 1
          omega
        rw [hpoweq]
        ring
    rw [hexpand, zero_add]

/-- Summed over one more level, `g_step` gives the partial-sum recursion the singularity analysis
runs on. -/
private theorem wsum_succ_le (N : ℕ) :
    ∑ n ∈ Finset.range (N + 2), g n ≤
      4 * (20 / 159 : ℚ) + (20 / 159 : ℚ) * (∑ n ∈ Finset.range (N + 1), g n) +
        3 * (20 / 159 : ℚ) * (∑ n ∈ Finset.range (N + 1), g n) ^ 2 := by
  have hsplit : ∑ n ∈ Finset.range (N + 2), g n = ∑ i ∈ Finset.range (N + 1), g (i + 1) := by
    rw [show N + 2 = (N + 1) + 1 from rfl, Finset.sum_range_succ']
    simp [g_zero]
  rw [hsplit]
  have hstep : ∑ i ∈ Finset.range (N + 1), g (i + 1) ≤
      ∑ i ∈ Finset.range (N + 1),
        ((if i = 0 then 4 * (20 / 159 : ℚ) else 0) + (20 / 159 : ℚ) * g i +
          3 * (20 / 159 : ℚ) * ∑ ij ∈ Finset.antidiagonal i, g ij.1 * g ij.2) :=
    Finset.sum_le_sum (fun i _ => g_step i)
  refine hstep.trans ?_
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  have h1 : ∑ i ∈ Finset.range (N + 1),
      (if i = 0 then (4 : ℚ) * (20 / 159) else 0) = 4 * (20 / 159) := by
    rw [Finset.sum_range_succ']
    simp
  have h2 : ∑ i ∈ Finset.range (N + 1), (20 / 159 : ℚ) * g i
      = (20 / 159 : ℚ) * ∑ i ∈ Finset.range (N + 1), g i := by
    rw [Finset.mul_sum]
  have h3 : ∑ i ∈ Finset.range (N + 1),
      3 * (20 / 159 : ℚ) * ∑ ij ∈ Finset.antidiagonal i, g ij.1 * g ij.2
      = 3 * (20 / 159 : ℚ) *
        ∑ i ∈ Finset.range (N + 1), ∑ ij ∈ Finset.antidiagonal i, g ij.1 * g ij.2 := by
    rw [Finset.mul_sum]
  have h4 : ∑ i ∈ Finset.range (N + 1), ∑ ij ∈ Finset.antidiagonal i, g ij.1 * g ij.2
      ≤ (∑ i ∈ Finset.range (N + 1), g i) ^ 2 := sum_antidiagonal_sq_le g g_nonneg N
  rw [h1, h2, h3]
  have h5 := mul_le_mul_of_nonneg_left h4 (by norm_num : (0 : ℚ) ≤ 3 * (20 / 159))
  linarith

/-- **The weighted partial sums stay bounded by `11/10`**, at `z = 20/159`. -/
private theorem wsum_le : ∀ N : ℕ, ∑ n ∈ Finset.range (N + 1), g n ≤ (11 / 10 : ℚ) := by
  intro N
  induction N with
  | zero => simp [g_zero]; norm_num
  | succ N ih =>
      have hkey := wsum_succ_le N
      have hSnonneg : (0 : ℚ) ≤ ∑ n ∈ Finset.range (N + 1), g n :=
        Finset.sum_nonneg (fun i _ => g_nonneg i)
      have harith : 4 * (20 / 159 : ℚ) + (20 / 159 : ℚ) * (∑ n ∈ Finset.range (N + 1), g n) +
          3 * (20 / 159 : ℚ) * (∑ n ∈ Finset.range (N + 1), g n) ^ 2 ≤ 11 / 10 := by
        nlinarith [ih, hSnonneg]
      calc ∑ n ∈ Finset.range (N + 1 + 1), g n = ∑ n ∈ Finset.range (N + 2), g n := by
            norm_num
        _ ≤ _ := hkey
        _ ≤ 11 / 10 := harith

/-- **The growth bound.** At most `(11/10)·(159/20)ⁿ` codes have `n` nodes — the singularity of
the counting generating function is at `1 + 4√3 ≈ 7.928`, below the `8` the three-bit-per-node
budget could carry. -/
theorem card_codesOfNodes_le (n : ℕ) : 10 * 20 ^ n * (codesOfNodes n).card ≤ 11 * 159 ^ n := by
  have hterm : g n ≤ ∑ i ∈ Finset.range (n + 1), g i :=
    Finset.single_le_sum (fun i _ => g_nonneg i) (Finset.self_mem_range_succ n)
  have hle : g n ≤ (11 / 10 : ℚ) := hterm.trans (wsum_le n)
  have hgeq : g n = (codesOfNodes n).card * (20 / 159 : ℚ) ^ n := rfl
  rw [hgeq] at hle
  have hclear : ((codesOfNodes n).card : ℚ) * 20 ^ n * 10 ≤ 11 * 159 ^ n := by
    have hmul := mul_le_mul_of_nonneg_right hle (by positivity : (0 : ℚ) ≤ 10 * 159 ^ n)
    calc ((codesOfNodes n).card : ℚ) * 20 ^ n * 10
        = ((codesOfNodes n).card : ℚ) * (20 / 159 : ℚ) ^ n * (10 * 159 ^ n) := by
          rw [div_pow]
          field_simp
      _ ≤ 11 / 10 * (10 * 159 ^ n) := hmul
      _ = 11 * 159 ^ n := by ring
  have hcast : ((10 * 20 ^ n * (codesOfNodes n).card : ℕ) : ℚ) ≤ ((11 * 159 ^ n : ℕ) : ℚ) := by
    push_cast
    linarith [hclear]
  exact_mod_cast hcast

/-- **The tail-sum growth bound**: the same rate, summed over every node count up to `N`. -/
theorem sum_card_codesOfNodes_le (N : ℕ) :
    10 * 20 ^ N * ∑ n ∈ Finset.range (N + 1), (codesOfNodes n).card ≤ 11 * 159 ^ N := by
  have hS := wsum_le N
  have hlow : ∀ n ∈ Finset.range (N + 1), ((codesOfNodes n).card : ℚ) * (20 / 159 : ℚ) ^ N
      ≤ ((codesOfNodes n).card : ℚ) * (20 / 159 : ℚ) ^ n := by
    intro n hn
    have hn' : n ≤ N := by simpa [Nat.lt_succ_iff] using Finset.mem_range.mp hn
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact pow_le_pow_of_le_one (by positivity) (by norm_num) hn'
  have hsum_le : ∑ n ∈ Finset.range (N + 1), ((codesOfNodes n).card : ℚ) * (20 / 159 : ℚ) ^ N
      ≤ ∑ n ∈ Finset.range (N + 1), g n :=
    Finset.sum_le_sum hlow
  have hfactor : ∑ n ∈ Finset.range (N + 1), ((codesOfNodes n).card : ℚ) * (20 / 159 : ℚ) ^ N
      = (∑ n ∈ Finset.range (N + 1), ((codesOfNodes n).card : ℚ)) * (20 / 159 : ℚ) ^ N := by
    rw [Finset.sum_mul]
  rw [hfactor] at hsum_le
  have hle : (∑ n ∈ Finset.range (N + 1), ((codesOfNodes n).card : ℚ)) * (20 / 159 : ℚ) ^ N
      ≤ (11 / 10 : ℚ) := hsum_le.trans hS
  have hclear : (∑ n ∈ Finset.range (N + 1), ((codesOfNodes n).card : ℚ)) * 20 ^ N * 10
      ≤ 11 * 159 ^ N := by
    have hmul := mul_le_mul_of_nonneg_right hle (by positivity : (0 : ℚ) ≤ 10 * 159 ^ N)
    calc (∑ n ∈ Finset.range (N + 1), ((codesOfNodes n).card : ℚ)) * 20 ^ N * 10
        = (∑ n ∈ Finset.range (N + 1), ((codesOfNodes n).card : ℚ)) * (20 / 159 : ℚ) ^ N *
            (10 * 159 ^ N) := by
          rw [div_pow]
          field_simp
      _ ≤ 11 / 10 * (10 * 159 ^ N) := hmul
      _ = 11 * 159 ^ N := by ring
  have hcast : ((10 * 20 ^ N * ∑ n ∈ Finset.range (N + 1), (codesOfNodes n).card : ℕ) : ℚ)
      ≤ ((11 * 159 ^ N : ℕ) : ℚ) := by
    push_cast
    linarith [hclear]
  exact_mod_cast hcast

/-! ## The counting bound on `KE`, reindexed by node counts -/

/-- **The counting bound on `KE`, counted by node budget rather than by raw bit-strings.** Each
`x` with `KE x ≤ L` has its own shortest program (`minCode`, injective by `minCode_E_injective`),
and that program has at most `L / 3` nodes (`elen = 3 · nodes`). -/
theorem card_KE_le_nodes (L : ℕ) :
    {x : ℕ | KE x ≤ L}.ncard ≤ ∑ n ∈ Finset.range (L / 3 + 1), (codesOfNodes n).card := by
  have hmaps : ∀ x ∈ {x : ℕ | KE x ≤ L},
      minCode x ∈ (↑((Finset.range (L / 3 + 1)).biUnion codesOfNodes) : Set Code) := by
    intro x hx
    simp only [Set.mem_ofPred_eq] at hx
    apply Finset.mem_coe.mpr
    apply Finset.mem_biUnion.mpr
    refine ⟨nodes (minCode x), Finset.mem_range.mpr ?_, mem_codesOfNodes (minCode x)⟩
    have he : elen (minCode x) = KE x := elen_minCode x
    have h3 : elen (minCode x) = 3 * nodes (minCode x) := elen_eq_three_mul_nodes _
    omega
  have hminj : Function.Injective minCode := minCode_E_injective.of_comp
  have hle := Set.ncard_le_ncard_of_injOn minCode hmaps hminj.injOn
      ((Finset.range (L / 3 + 1)).biUnion codesOfNodes).finite_toSet
  rw [Set.ncard_coe_finset] at hle
  exact hle.trans Finset.card_biUnion_le

/-! ## The data rate of `KE` -/

set_option maxRecDepth 4000 in
set_option exponentiation.threshold 600 in
/-- The arithmetic fact behind the crossing: raised to any power `t`, the ratio
`159 ^ 501 / (20 ^ 501 · 2 ^ 1500)` is below one, since `159 < 20 · 8 = 160` already at `t = 1`. -/
private theorem crossing_base : (159 : ℕ) ^ 501 < 20 ^ 501 * 8 ^ 500 := by
  decide

private theorem crossing_ratio_lt_one :
    ((159 : ℚ) ^ 501) / ((20 : ℚ) ^ 501 * (2 : ℚ) ^ 1500) < 1 := by
  rw [div_lt_one (by positivity)]
  have h8 : (8 : ℚ) ^ 500 = (2 : ℚ) ^ 1500 := by
    have h83 : (8 : ℚ) = 2 ^ 3 := by norm_num
    rw [h83, ← pow_mul]
  have := crossing_base
  have hcast : ((159 : ℕ) ^ 501 : ℚ) < ((20 : ℕ) ^ 501 * (8 : ℕ) ^ 500 : ℚ) := by
    exact_mod_cast this
  push_cast at hcast
  rw [h8] at hcast
  exact hcast

set_option maxRecDepth 4000 in
/-- **The data rate of `KE` is bounded away from one bit per bit.** No constant `c` makes
`KE x ≤ (1 + 1/500) · Nat.size x + c` for every `x`. Consequently no constant makes `KE` an ideal
code for the computable measure `μ_ε(x) := 2^{−⌈(1 + 1/500) · Nat.size x⌉ − 1}`, whose total mass
is under one. -/
theorem KE_data_rate (c : ℕ) : ∃ x : ℕ, 501 * Nat.size x + 500 * c < 500 * KE x := by
  by_contra hcon
  push Not at hcon
  set r : ℚ := ((159 : ℚ) ^ 501) / ((20 : ℚ) ^ 501 * (2 : ℚ) ^ 1500) with hr_def
  have hr_pos : 0 < r := by positivity
  have hr_lt : r < 1 := crossing_ratio_lt_one
  have htarget_pos : (0 : ℚ) < 5 / (11 * 159 ^ c) := by positivity
  obtain ⟨t₀, ht₀⟩ := exists_pow_lt_of_lt_one htarget_pos hr_lt
  set t : ℕ := t₀ + 1 with ht_def
  have ht_pos : 1 ≤ t := by omega
  have hrt : r ^ t < 5 / (11 * 159 ^ c) := by
    calc r ^ t = r ^ t₀ * r := by rw [ht_def, pow_succ]
      _ ≤ r ^ t₀ := by nlinarith [pow_nonneg hr_pos.le t₀, hr_lt.le]
      _ < 5 / (11 * 159 ^ c) := ht₀
  set s : ℕ := 1500 * t with hs_def
  have hs_pos : 1 ≤ s := by rw [hs_def]; omega
  set L : ℕ := (501 * s + 500 * c) / 500 with hL_def
  set M : ℕ := L / 3 with hM_def
  have hL_lb : 1503 * t ≤ L := by
    have h1 : 501 * s / 500 ≤ L := Nat.div_le_div_right (by omega)
    have h2 : 501 * s / 500 = 1503 * t := by rw [hs_def]; omega
    omega
  have hL_ub : L * 500 ≤ 501 * s + 500 * c := Nat.div_mul_le_self _ _
  have hM_lb : 501 * t ≤ M := by
    have h1 : 1503 * t / 3 ≤ L / 3 := Nat.div_le_div_right hL_lb
    have h2 : 1503 * t / 3 = 501 * t := by omega
    rw [hM_def]; omega
  have hM_ub : M ≤ 501 * t + c := by
    have h1 : M * 3 ≤ L := Nat.div_mul_le_self _ _
    have h2 : 1500 * M ≤ 500 * L := by omega
    rw [hs_def] at hL_ub
    omega
  have hsub : (↑(Finset.Ico (2 ^ (s - 1)) (2 ^ s)) : Set ℕ) ⊆ {x : ℕ | KE x ≤ L} := by
    intro x hx
    simp only [Finset.coe_Ico, Set.mem_Ico] at hx
    have hxlt : x < 2 ^ s := hx.2
    have hsize : Nat.size x ≤ s := Nat.size_le.mpr hxlt
    have hh := hcon x
    have : 500 * KE x ≤ 501 * s + 500 * c := by
      have : 501 * Nat.size x ≤ 501 * s := by omega
      omega
    simp only [Set.mem_ofPred_eq]
    rw [hL_def]
    exact (Nat.le_div_iff_mul_le (by norm_num)).mpr (by omega)
  have hfin : {x : ℕ | KE x ≤ L}.Finite := AdditiveComplexity.finite_KE_le L
  have hcardIco : (Finset.Ico (2 ^ (s - 1)) (2 ^ s)).card = 2 ^ (s - 1) := by
    rw [Nat.card_Ico]
    have : 2 ^ s = 2 * 2 ^ (s - 1) := by
      rw [← pow_succ']
      congr 1
    omega
  have hlow : 2 ^ (s - 1) ≤ {x : ℕ | KE x ≤ L}.ncard := by
    have := Set.ncard_le_ncard hsub hfin
    rwa [Set.ncard_coe_finset, hcardIco] at this
  have hmid := card_KE_le_nodes L
  rw [← hM_def] at hmid
  have hcount_lb : 2 ^ (s - 1) ≤ ∑ n ∈ Finset.range (M + 1), (codesOfNodes n).card :=
    hlow.trans hmid
  have hcount_ub := sum_card_codesOfNodes_le M
  have hcombine : 10 * 20 ^ M * 2 ^ (s - 1) ≤ 11 * 159 ^ M := by
    calc 10 * 20 ^ M * 2 ^ (s - 1)
        ≤ 10 * 20 ^ M * ∑ n ∈ Finset.range (M + 1), (codesOfNodes n).card := by
          exact Nat.mul_le_mul_left _ hcount_lb
      _ ≤ 11 * 159 ^ M := hcount_ub
  have hpow20 : (20 : ℕ) ^ (501 * t) ≤ 20 ^ M := Nat.pow_le_pow_right (by norm_num) hM_lb
  have hpow159 : (159 : ℕ) ^ M ≤ 159 ^ (501 * t) * 159 ^ c := by
    rw [← pow_add]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hfinal : 10 * 20 ^ (501 * t) * 2 ^ (s - 1) ≤ 11 * (159 ^ (501 * t) * 159 ^ c) := by
    calc 10 * 20 ^ (501 * t) * 2 ^ (s - 1)
        ≤ 10 * 20 ^ M * 2 ^ (s - 1) := by
          exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hpow20)
      _ ≤ 11 * 159 ^ M := hcombine
      _ ≤ 11 * (159 ^ (501 * t) * 159 ^ c) := Nat.mul_le_mul_left _ hpow159
  have hfinalQ : (10 : ℚ) * 20 ^ (501 * t) * 2 ^ (s - 1) ≤ 11 * (159 ^ (501 * t) * 159 ^ c) := by
    exact_mod_cast hfinal
  have hpow2 : (2 : ℚ) ^ (s - 1) * 2 = 2 ^ s := by
    rw [← pow_succ]
    congr 1
  have hrpow : (159 : ℚ) ^ (501 * t) = r ^ t * (20 ^ (501 * t) * 2 ^ s) := by
    have hs' : s = 1500 * t := hs_def
    rw [hs', hr_def, div_pow, mul_pow, ← pow_mul, ← pow_mul, ← pow_mul]
    have hden : (20 : ℚ) ^ (501 * t) * (2 : ℚ) ^ (1500 * t) ≠ 0 := by positivity
    field_simp
  have hpos20 : (0 : ℚ) < 20 ^ (501 * t) := by positivity
  have hpos2s : (0 : ℚ) < 2 ^ s := by positivity
  have hstep : (5 : ℚ) ≤ 11 * r ^ t * 159 ^ c := by
    have hle : (10 : ℚ) * 20 ^ (501 * t) * 2 ^ (s - 1) ≤
        11 * (r ^ t * (20 ^ (501 * t) * 2 ^ s)) * 159 ^ c := by
      rw [← hrpow]
      linarith [hfinalQ]
    have heq : (10 : ℚ) * 20 ^ (501 * t) * 2 ^ (s - 1) =
        5 * (20 ^ (501 * t) * 2 ^ s) := by
      rw [← hpow2]; ring
    rw [heq] at hle
    have hcancel : (5 : ℚ) * (20 ^ (501 * t) * 2 ^ s) ≤
        (11 * r ^ t * 159 ^ c) * (20 ^ (501 * t) * 2 ^ s) := by
      calc (5 : ℚ) * (20 ^ (501 * t) * 2 ^ s)
          ≤ 11 * (r ^ t * (20 ^ (501 * t) * 2 ^ s)) * 159 ^ c := hle
        _ = (11 * r ^ t * 159 ^ c) * (20 ^ (501 * t) * 2 ^ s) := by ring
    exact le_of_mul_le_mul_right hcancel (by positivity)
  have hcontra : (5 : ℚ) / (11 * 159 ^ c) ≤ r ^ t := by
    rw [div_le_iff₀ (by positivity)]
    linarith [hstep]
  linarith [hrt, hcontra]

end CodeDataRate
