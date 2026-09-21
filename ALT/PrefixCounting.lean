/-
Copyright (c) 2026 Mykola Palamarchuk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mykola Palamarchuk
-/
module

public import ALT.PrefixEliasKB
public import ALT.PrefixComplexity

-- Formal-check file, not Mathlib-destined: opt out of the house-style header linter.
set_option linter.style.header false

/-!
# Counting bounds on `KB` and `K_bitlen`, and `KB`'s non-computability
([Decoupling] §6.6, [Discovery] §1.1)

Provenance: [Decoupling] §6.6 (Theorem 6.6(iii), FV-28) and (Theorem 6.7(iii), FV-29) quantify
their unprovable families as "all but finitely many `s`", over the finiteness lemmas
`setOf_K_bitlen_le_finite` (`ALT/ChaitinIncompleteness.lean`) and `setOf_KB_le_finite`
(`ALT/KBEnumerable.lean`) respectively — neither of which carries a count. [Discovery] §1.1's row
FV-20 lists `KB`'s Kraft inequality (`kraft_KB`) beside every other property of the machine except
its non-computability, unlike `K` (FV-2) and `KP` (FV-13).

## What this establishes

Three independent results, none consuming another.

* `finset_card_KB_le`, `card_KB_le` — **the counting bound on `KB`**: a description budget of `L`
  bits describes at most `2 ^ L` naturals, directly from `kraft_KB`'s semimeasure property
  (`ALT/PrefixMachine.lean`) — every member of the budgeted set contributes at least `2 ^ (-L)` to
  a series bounded by one. The `Finset` form is the content (no finiteness hypothesis can make it
  vacuous); the `ncard` form is its corollary through `setOf_KB_le_finite`.
* `finset_card_K_bitlen_le`, `card_K_bitlen_le` — **the same count on `K_bitlen`**, at the same
  constant `2 ^ L`, for an unrelated reason: no Kraft inequality is proved for `K_bitlen` (whether
  `∑ 2^{-K_bitlen}` converges is not settled), so the bound comes from injectivity instead —
  `K_bitlen s ≤ L` is `K s < 2 ^ L` (`K_bitlen_eq`, `Nat.size_le`), and `K_injective` caps the
  values below `2 ^ L` at that many.
* `KB_not_computable` — **`KB` is not computable**. The Berry argument runs through the
  already-landed partial-map invariance `KB_partial_map_le` rather than through a Kleene fixed
  point: no totality step is needed, unlike `KP_not_computable`'s route through `fixed_point₂` over
  `Code.eval`, an evaluation `pfy` does not share.

## What this does NOT establish (flagged)

* The `Finset` counting bounds are tight at `2 ^ L` and no sharper: a flat semimeasure on exactly
  `2 ^ L` points at mass one attains it, so `< 2 ^ L` is not available from the Kraft hypothesis
  alone. `KB`'s own totality on the infinite domain `ℕ` would buy a strict bound at the cost of
  naming one point outside the set and its positive weight; that sharpening is not commissioned
  here.
* Nothing here relates `KB` and `K_bitlen` to each other beyond the two counts landing on the same
  constant by unrelated routes (prefix-freeness against index injectivity);
  `ALT/PrefixModelCost.lean`'s boundary on the two currencies is unchanged.
-/


@[expose] public section

namespace PrefixMachine

open Nat.Partrec Nat.Partrec.Code KolmogorovComplexity PrefixComplexity

/-! ## The counting bound on `KB` -/

/-- **The counting bound on `KB`, `Finset` form**: at most `2 ^ L` naturals are describable within
a budget of `L` bits. Each member of `F` contributes at least `2 ^ (-L)` to the Kraft series
(`pow_le_pow_of_le_one`), so `F.card` copies of that weight sit below the series' partial sum over
`F` (`Finset.sum_le_sum`), below the full series (`Summable.sum_le_tsum`, at
`summable_two_pow_neg_KB`), below one (`kraft_KB`) — the cast arithmetic closing exactly as
`CodingTheoremWeak.card_exceeds_lt`'s does. -/
theorem finset_card_KB_le (L : ℕ) (F : Finset ℕ) (hF : ∀ x ∈ F, KB x ≤ L) :
    F.card ≤ 2 ^ L := by
  have hpow : ∀ x ∈ F, (1 / 2 : ℝ) ^ L ≤ (1 / 2 : ℝ) ^ KB x := fun x hx =>
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (hF x hx)
  have hsum1 : ∑ x ∈ F, (1 / 2 : ℝ) ^ L ≤ ∑ x ∈ F, (1 / 2 : ℝ) ^ KB x := Finset.sum_le_sum hpow
  have hsum2 : ∑ x ∈ F, (1 / 2 : ℝ) ^ KB x ≤ ∑' x : ℕ, (1 / 2 : ℝ) ^ KB x :=
    summable_two_pow_neg_KB.sum_le_tsum F (fun x _ => by positivity)
  have hconst : ∑ x ∈ F, (1 / 2 : ℝ) ^ L = (F.card : ℝ) * (1 / 2 : ℝ) ^ L := by
    rw [Finset.sum_const, nsmul_eq_mul]
  have hfinal : (F.card : ℝ) * (1 / 2 : ℝ) ^ L ≤ 1 := by
    rw [← hconst]; linarith [kraft_KB]
  have h2 : ((2 ^ L : ℕ) : ℝ) * (1 / 2 : ℝ) ^ L = 1 := by
    push_cast
    rw [mul_comm, ← mul_pow]
    norm_num
  have hpos : (0 : ℝ) < (1 / 2 : ℝ) ^ L := by positivity
  have hcard_le : (F.card : ℝ) ≤ ((2 ^ L : ℕ) : ℝ) := by
    have heq : (F.card : ℝ) * (1 / 2 : ℝ) ^ L ≤ ((2 ^ L : ℕ) : ℝ) * (1 / 2 : ℝ) ^ L := by
      rw [h2]; exact hfinal
    exact le_of_mul_le_mul_right heq hpos
  exact_mod_cast hcard_le

/-- **The counting bound on `KB`, `ncard` form**: `finset_card_KB_le`'s corollary at the finiteness
`setOf_KB_le_finite` supplies, over its own `Finite.toFinset`. Stated separately from the `Finset`
form because `Set.ncard` of an infinite set is `0`, so this sentence alone could not fail; the
`Finset` form is what a reader needs to see the bound bite. -/
theorem card_KB_le (L : ℕ) : {x : ℕ | KB x ≤ L}.ncard ≤ 2 ^ L := by
  have hfin := setOf_KB_le_finite L
  rw [Set.ncard_eq_toFinset_card _ hfin]
  exact finset_card_KB_le L hfin.toFinset (fun x hx => hfin.mem_toFinset.mp hx)

/-! ## The same count on `K_bitlen`, by injectivity -/

/-- **The counting bound on `K_bitlen`, `Finset` form**: at most `2 ^ L` naturals have bit-length
complexity at most `L`. No Kraft inequality is proved here (whether `∑ 2^{-K_bitlen}` converges is
not settled); the bound is `K`'s injectivity into the indices below `2 ^ L` instead —
`K_bitlen s ≤ L` unfolds to `K s < 2 ^ L` (`K_bitlen_eq`, `Nat.size_le`), so `F.image K` sits
inside `Finset.range (2 ^ L)` and has `F`'s own cardinality (`Finset.card_image_of_injOn`, at
`K_injective`). -/
theorem finset_card_K_bitlen_le (L : ℕ) (F : Finset ℕ) (hF : ∀ s ∈ F, K_bitlen s ≤ L) :
    F.card ≤ 2 ^ L := by
  have hmaps : ∀ s ∈ F, K s ∈ Finset.range (2 ^ L) := by
    intro s hs
    rw [Finset.mem_range, ← Nat.size_le, ← K_bitlen_eq]
    exact hF s hs
  have hinj : Set.InjOn K F := fun x _ y _ h => K_injective h
  calc F.card = (F.image K).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ (Finset.range (2 ^ L)).card := Finset.card_le_card (Finset.image_subset_iff.mpr hmaps)
    _ = 2 ^ L := Finset.card_range _

/-- **The counting bound on `K_bitlen`, `ncard` form**: `finset_card_K_bitlen_le`'s corollary at
`setOf_K_bitlen_le_finite`, the same shape as `card_KB_le`. -/
theorem card_K_bitlen_le (L : ℕ) : {s : ℕ | K_bitlen s ≤ L}.ncard ≤ 2 ^ L := by
  have hfin := setOf_K_bitlen_le_finite L
  rw [Set.ncard_eq_toFinset_card _ hfin]
  exact finset_card_K_bitlen_le L hfin.toFinset (fun s hs => hfin.mem_toFinset.mp hs)

/-! ## `KB` is not computable -/

set_option maxHeartbeats 400000 in
-- the `Computable`-instance bridge through `KB` composed with the Berry predicate is
-- instance-heavy in this imported environment; the default 200k heartbeats is just short.
/-- **`KB` is not computable.** Were it computable, the partial map `f n := Nat.rfind (fun s =>
decide (n < KB s))` would be `Partrec` (the search predicate is computable in `(n, s)`); at each
`n`, `KB_unbounded` puts a witness in `f n`'s domain (no totality step, unlike `KP_not_computable`'s
route through a Kleene fixed point over `Code.eval`), so some `w ∈ f n` has `n < KB w`
(`Nat.rfind_spec`); `KB`'s own partial-map invariance (`KB_partial_map_le`) then gives `KB w ≤ KB n
+ c`, and `KB_le_two_mul_size` gives `KB n ≤ 2 * Nat.size n + c'`, so `n < 2 * Nat.size n + c' + c`
at every `n` — contradicted at `n := 2 ^ (c + c' + 4)`, where `Nat.size n = c + c' + 5`
(`Nat.size_pow`) reduces the claim to `3 * (c + c') + 10 ≤ 16 * 2 ^ (c + c')`, true at every
value of `c + c'` (`Nat.lt_two_pow_self`). -/
theorem KB_not_computable : ¬ Computable KB := by
  intro hK
  have hlt : Computable fun p : ℕ × ℕ => decide (p.1 < p.2) := by
    have hpr := Primrec.nat_lt.choose_spec.to_comp
    have heq : (fun a : ℕ × ℕ => @decide _ (Primrec.nat_lt.choose a)) =
        fun p : ℕ × ℕ => decide (p.1 < p.2) := by funext a; congr 1
    rw [← heq]; exact hpr
  have hg : Computable fun p : ℕ × ℕ => decide (p.1 < KB p.2) :=
    hlt.comp (Computable.fst.pair (hK.comp Computable.snd))
  set p : ℕ → ℕ →. Bool := fun n s => Part.some (decide (n < KB s)) with hp
  have hf : Partrec fun n : ℕ => Nat.rfind (p n) :=
    Partrec.rfind (p := p) hg.partrec
  obtain ⟨c, hc⟩ := KB_partial_map_le _ hf
  obtain ⟨c', hc'⟩ := KB_le_two_mul_size
  set n : ℕ := 2 ^ (c + c' + 4) with hndef
  obtain ⟨w, hw⟩ := DeepLadder.KB_unbounded n
  have hdom : (Nat.rfind (p n)).Dom := by
    rw [Nat.rfind_dom]
    exact ⟨w, by simp [hp, hw], fun {m} _ => trivial⟩
  have hymem : (Nat.rfind (p n)).get hdom ∈ (fun n : ℕ => Nat.rfind (p n)) n := Part.get_mem hdom
  have hyspec : n < KB ((Nat.rfind (p n)).get hdom) := by
    have h := Nat.rfind_spec (Part.get_mem hdom)
    simpa [hp] using h
  have hyle : KB ((Nat.rfind (p n)).get hdom) ≤ KB n + c := hc n _ hymem
  have hnle : KB n ≤ 2 * Nat.size n + c' := hc' n
  have hsize : Nat.size n = c + c' + 5 := by rw [hndef]; exact Nat.size_pow
  have hnval : n = 16 * 2 ^ (c + c') := by rw [hndef]; ring
  have hfinal : 3 * (c + c') + 10 ≤ 16 * 2 ^ (c + c') := by
    have h1 : (c + c') < 2 ^ (c + c') := Nat.lt_two_pow_self
    have h2 : 1 ≤ 2 ^ (c + c') := Nat.one_le_two_pow
    nlinarith
  omega

end PrefixMachine
