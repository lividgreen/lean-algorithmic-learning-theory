/-
Copyright (c) 2026 Mykola Palamarchuk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mykola Palamarchuk
-/
import Mathlib.GroupTheory.Perm.Cycle.Basic
import Mathlib.GroupTheory.Perm.Fin
import ALT.AdditiveComplexity
import ALT.PersistenceCapacity

-- Formal-check file, not Mathlib-destined: opt out of the house-style header linter.
set_option linter.style.header false

/-!
# The canonical-form-lens counting core: the cap's constant is exactly two
([Persistence] §8, Propositions 8.35(iii), 8.36, Remark 8.37)

Proposition 8.35(iii) bounds the loss from declining a move up the order on pricing points by
twice the declined move's address; Proposition 8.36(iii) attains that cap at one times the
address. This module machine-checks a construction attaining it at **twice** the address, so the
cap's constant is exactly two — an incompressible world read through its own canonical-form map,
with its two fixed points merged.

**The construction.** `canonW n` is the permutation of `Fin n` fixing `0` and `1` and cycling
`{2, …, n−1}` by `+1`; `mergeMap n` glues the labels `0, 1` into a single label of `Fin (n−1)`;
`canonWt n` is the corresponding one-fixed-point law, and `mergeMap` descends `canonW` to it
(`descent`). For an arbitrary relabelling `V`, `convW V := V⁻¹ * canonW n * V` and
`convLens hn V := mergeMap n _ ∘ V` transport this: `convLens hn V` descends `convW V` to the same
`canonWt` (`convDescent`), and the reading `convReading hn V` — the indicator of `{V⁻¹ 0, V⁻¹
1}` — persists under `convW V` (`convReading_invariant`), factors through `convLens hn V`
(`convReading_factors`), and its true set is exactly `convW V`'s fixed-point set
(`convW_fixedPoints`). So `([n], convLens hn V)` and `([n], id)` are both Proposition 8.29 pricing
points for the constant family this reading generates.

**The counting.** A permutation centralizing `canonW n` permutes its two fixed points and, by the
cycle's own transitivity (`canonW_exists_pow_eq`), is determined on the cycled part by the image
of one point — at most `2n` such permutations (`canonW_centralizer_card_le`; the exact value
`2(n−2)` is not needed). The map `V ↦ convW V` has fibres bounded by centralizer cosets, giving
the same counting shape as `PersistenceCapacity.collapse_count` (`convW_collapse_count`); past the
arithmetic threshold this undercuts `n!`, some realized `convW V`'s table costs more than `L` bits
(`convW_world_floor`) — Finding 2's `K(U) ≥ log₂ n! − O(log₂ n)`. Separately, the merged lens
determines the world exactly: `convLens hn U = convLens hn W` forces `convW U = convW W`
(`convW_recovery`), because the two preimages of the merged label differ only by the swap of `0`
and `1`, and any permutation fixing the cycled part and permuting `{0, 1}` setwise commutes with
`canonW n` (`centralizes_of_fixes_outside01`).

**The capstone** (`canonicalFormLens_family`) bundles descent, the reading's invariance and
factoring, and the world floor into one `∃`-statement, with a concrete instance at `n = 6`
(`canonicalFormLens_instance`). It claims only the counts: the `K`-displays and the `A`-arithmetic
of Proposition 8.35 stay on §8's standing transport boundary and are not restated here. Cite
`[Persistence] §8` at Propositions 8.35(iii) and 8.36 with Remark 8.37.
-/

namespace CanonicalFormLens

open Equiv Equiv.Perm AdditiveComplexity PersistenceCapacity Nat

/-! ### A general shifted-cycle helper -/

/-- The bijection between `Fin (n - k)` and the "upper part" `{x : Fin n // k ≤ x.val}`,
shifting an index up by `k`. Defined for all `k, n` (no side condition): when `k > n` both sides
are empty and the equations hold vacuously. -/
noncomputable def shiftEquiv (k n : ℕ) : Fin (n - k) ≃ {x : Fin n // k ≤ x.val} where
  toFun j := ⟨⟨j.val + k, by omega⟩, by simp⟩
  invFun x := ⟨x.1.val - k, by have := x.2; have := x.1.isLt; omega⟩
  left_inv j := by apply Fin.ext; simp
  right_inv x := by
    apply Subtype.ext
    apply Fin.ext
    have := x.2
    simp
    omega

/-- The permutation of `Fin n` fixing `{0, …, k−1}` pointwise and cycling `{k, …, n−1}` by `+1`
(wrapping `n−1 ↦ k`). Built by transporting `finRotate (n − k)` along `shiftEquiv`. -/
noncomputable def shiftedCycle (k n : ℕ) : Equiv.Perm (Fin n) :=
  (finRotate (n - k)).extendDomain (shiftEquiv k n)

private theorem shiftedCycle_apply_of_lt {k n : ℕ} {x : Fin n} (hx : x.val < k) :
    shiftedCycle k n x = x := by
  unfold shiftedCycle
  rw [Equiv.Perm.extendDomain_apply_not_subtype]
  omega

private theorem shiftedCycle_apply_of_le {k n : ℕ} {x : Fin n} (hx : k ≤ x.val) :
    (shiftedCycle k n x).val
      = ((finRotate (n - k)) ⟨x.val - k, by omega⟩ : Fin (n - k)).val + k := by
  unfold shiftedCycle
  have heq := Equiv.Perm.extendDomain_apply_subtype (finRotate (n - k)) (shiftEquiv k n) hx
  rw [heq]
  simp [shiftEquiv]

/-- `finRotate`'s action as a closed Nat formula — avoids the dependent-motive trap of rewriting
inside a `finRotate`'s own `Fin`-valued argument (its index proof term depends on the value). -/
private theorem finRotate_val_eq {m : ℕ} (_hm : 0 < m) (j : Fin m) :
    (finRotate m j).val = (j.val + 1) % m := by
  haveI : NeZero m := ⟨by omega⟩
  rw [finRotate_apply, Fin.val_add, Fin.val_one']
  simp [Nat.add_mod]

/-- `shiftedCycle`'s moving action as a closed Nat formula, for the same reason. -/
private theorem shiftedCycle_val_of_le {k n : ℕ} (hm : 0 < n - k) {x : Fin n} (hx : k ≤ x.val) :
    (shiftedCycle k n x).val = (x.val - k + 1) % (n - k) + k := by
  rw [shiftedCycle_apply_of_le hx, finRotate_val_eq hm]

private theorem mod_succ_ne {m : ℕ} (hm : 2 ≤ m) (j : ℕ) (hj : j < m) : (j + 1) % m ≠ j := by
  rcases lt_or_eq_of_le (show j + 1 ≤ m by omega) with h | h
  · rw [Nat.mod_eq_of_lt h]; omega
  · rw [h, Nat.mod_self]; omega

/-- `shiftedCycle` moves every point of the part it cycles, as long as that part has at least two
elements. Together with `shiftedCycle_apply_of_lt` this pins the fixed-point set exactly at
`{0, …, k−1}`. -/
private theorem shiftedCycle_ne_of_le {k n : ℕ} (hm : 2 ≤ n - k) {x : Fin n} (hx : k ≤ x.val) :
    shiftedCycle k n x ≠ x := by
  intro heq
  have hv : (shiftedCycle k n x).val = x.val := congrArg Fin.val heq
  rw [shiftedCycle_val_of_le (by omega) hx] at hv
  have hj : x.val - k < n - k := by have := x.isLt; omega
  exact mod_succ_ne hm (x.val - k) hj (by omega)

/-! ### The constructive core: `canonW`, `mergeMap`, `canonWt` -/

/-- The permutation of `Fin n` fixing `0` and `1` and cycling `{2, …, n−1}` by `+1`. -/
noncomputable def canonW (n : ℕ) : Equiv.Perm (Fin n) := shiftedCycle 2 n

/-- The permutation of `Fin (n−1)` fixing `0` and cycling `{1, …, n−2}` by `+1` — the law `canonW`
descends to after `mergeMap` glues labels `0, 1`. -/
noncomputable def canonWt (n : ℕ) : Equiv.Perm (Fin (n - 1)) := shiftedCycle 1 (n - 1)

/-- **`canonW`'s fixed-point set is exactly `{0, 1}`** ([Persistence] §8, Finding 1's "two fixed
points"): the object every downstream count and invariance argument rests on. -/
theorem canonW_fixed_iff {n : ℕ} (hn : 4 ≤ n) (x : Fin n) : canonW n x = x ↔ x.val ≤ 1 := by
  constructor
  · intro h
    by_contra hx'
    exact shiftedCycle_ne_of_le (k := 2) (by omega) (by omega) h
  · intro h
    exact shiftedCycle_apply_of_lt (by omega)

/-- The map gluing labels `0, 1` of `Fin n` into a single label `0` of `Fin (n − 1)`, and
shifting every other label down by one. Total for `n ≥ 2`; needs `n ≥ 4` only through `canonW`. -/
def mergeMap (n : ℕ) (hn : 2 ≤ n) : Fin n → Fin (n - 1) := fun x =>
  if h : x.val ≤ 1 then ⟨0, by omega⟩ else ⟨x.val - 1, by omega⟩

private theorem mergeMap_apply_of_le {n : ℕ} (hn : 2 ≤ n) {x : Fin n} (hx : x.val ≤ 1) :
    (mergeMap n hn x).val = 0 := by
  unfold mergeMap; simp [hx]

private theorem mergeMap_apply_of_gt {n : ℕ} (hn : 2 ≤ n) {x : Fin n} (hx : 1 < x.val) :
    (mergeMap n hn x).val = x.val - 1 := by
  unfold mergeMap; simp [Nat.not_le.mpr hx]

/-- **Descent** ([Persistence] §8, the construction behind Proposition 8.36(iii)): `mergeMap`
descends `canonW` to `canonWt`. -/
theorem descent {n : ℕ} (hn : 4 ≤ n) (x : Fin n) :
    mergeMap n (by omega) (canonW n x) = canonWt n (mergeMap n (by omega) x) := by
  apply Fin.ext
  rcases Nat.lt_or_ge x.val 2 with hx | hx
  · have hx1 : x.val ≤ 1 := by omega
    have hcw : canonW n x = x := shiftedCycle_apply_of_lt (k := 2) (by omega)
    have hcwt : canonWt n (mergeMap n (by omega) x) = mergeMap n (by omega) x :=
      shiftedCycle_apply_of_lt (k := 1) (by rw [mergeMap_apply_of_le (by omega) hx1]; omega)
    rw [hcw, hcwt]
  · have hval : (canonW n x).val = (x.val - 2 + 1) % (n - 2) + 2 :=
      shiftedCycle_val_of_le (k := 2) (by omega) hx
    have hgt : 1 < (canonW n x).val := by omega
    have hmx : (mergeMap n (by omega) x).val = x.val - 1 := mergeMap_apply_of_gt (by omega) hx
    have hy : (1 : ℕ) ≤ (mergeMap n (by omega) x).val := by omega
    have hval2 : (canonWt n (mergeMap n (by omega) x)).val
        = ((mergeMap n (by omega) x).val - 1 + 1) % (n - 1 - 1) + 1 :=
      shiftedCycle_val_of_le (k := 1) (by omega) hy
    rw [mergeMap_apply_of_gt (by omega) hgt, hval, hval2, hmx]
    have he : x.val - 2 + 1 = x.val - 1 - 1 + 1 := by omega
    have hmod : n - 1 - 1 = n - 2 := by omega
    rw [he, hmod]
    omega

/-- `canonW n y ∈ {0, 1} ↔ y ∈ {0, 1}` ([Persistence] §8, Finding 1: `canonW`'s two fixed points
are exactly `0` and `1`, so it preserves that pair setwise). -/
theorem canonW_mem01_iff {n : ℕ} (hn : 4 ≤ n) (y : Fin n) :
    (canonW n y = ⟨0, by omega⟩ ∨ canonW n y = ⟨1, by omega⟩)
      ↔ (y = ⟨0, by omega⟩ ∨ y = ⟨1, by omega⟩) := by
  constructor
  · rintro (h | h)
    · left
      have h0 : canonW n ⟨0, by omega⟩ = ⟨0, by omega⟩ := (canonW_fixed_iff hn _).mpr (by simp)
      exact (canonW n).injective (h.trans h0.symm)
    · right
      have h1 : canonW n ⟨1, by omega⟩ = ⟨1, by omega⟩ := (canonW_fixed_iff hn _).mpr (by simp)
      exact (canonW n).injective (h.trans h1.symm)
  · rintro (h | h) <;> subst h
    · exact Or.inl ((canonW_fixed_iff hn _).mpr (by simp))
    · exact Or.inr ((canonW_fixed_iff hn _).mpr (by simp))

/-- The membership form of `canonW_mem01_iff`, read against `Fin.val`. -/
private theorem canonW_val_le_one_iff {n : ℕ} (hn : 4 ≤ n) (z : Fin n) :
    (canonW n z).val ≤ 1 ↔ z.val ≤ 1 := by
  have h := canonW_mem01_iff hn z
  constructor
  · intro hle
    have hor : canonW n z = ⟨0, by omega⟩ ∨ canonW n z = ⟨1, by omega⟩ := by
      rcases (show (canonW n z).val = 0 ∨ (canonW n z).val = 1 by omega) with h0 | h1
      · exact Or.inl (Fin.ext h0)
      · exact Or.inr (Fin.ext h1)
    rcases h.mp hor with h0 | h1
    · have hv := congrArg Fin.val h0; dsimp only at hv; omega
    · have hv := congrArg Fin.val h1; dsimp only at hv; omega
  · intro hle
    have hor : z = ⟨0, by omega⟩ ∨ z = ⟨1, by omega⟩ := by
      rcases (show z.val = 0 ∨ z.val = 1 by omega) with h0 | h1
      · exact Or.inl (Fin.ext h0)
      · exact Or.inr (Fin.ext h1)
    rcases h.mpr hor with h0 | h1
    · have hv := congrArg Fin.val h0; dsimp only at hv; omega
    · have hv := congrArg Fin.val h1; dsimp only at hv; omega

/-! ### Conjugation transport and the constant reading -/

/-- `U_V := V⁻¹ * canonW * V`, the conjugate of `canonW` by an arbitrary relabelling `V`. -/
noncomputable def convW {n : ℕ} (V : Equiv.Perm (Fin n)) : Equiv.Perm (Fin n) :=
  V⁻¹ * canonW n * V

/-- `κ_V := mergeMap ∘ V`, the merged lens transported by `V`. -/
noncomputable def convLens {n : ℕ} (hn : 4 ≤ n) (V : Equiv.Perm (Fin n)) : Fin n → Fin (n - 1) :=
  mergeMap n (by omega) ∘ ⇑V

private theorem convW_apply {n : ℕ} (V : Equiv.Perm (Fin n)) (x : Fin n) :
    convW V x = V.symm (canonW n (V x)) := by
  unfold convW
  simp [Equiv.Perm.mul_apply]

/-- **Conjugation transports the descent** ([Persistence] §8, Finding 1's conjugation algebra):
`convLens hn V` descends `convW V` to the same law `canonWt`, for every `V`. -/
theorem convDescent {n : ℕ} (hn : 4 ≤ n) (V : Equiv.Perm (Fin n)) (x : Fin n) :
    convLens hn V (convW V x) = canonWt n (convLens hn V x) := by
  unfold convLens
  simp only [Function.comp_apply]
  rw [convW_apply]
  simp only [apply_symm_apply]
  exact descent hn (V x)

/-- **`U_V`'s fixed-point set is `{V⁻¹ 0, V⁻¹ 1}`** ([Persistence] §8, Finding 1: the reading
`ℓ_V`), read here as the equivalent membership test `(V x).val ≤ 1`. -/
theorem convW_fixed_iff {n : ℕ} (hn : 4 ≤ n) (V : Equiv.Perm (Fin n)) (x : Fin n) :
    convW V x = x ↔ (V x).val ≤ 1 := by
  rw [convW_apply, Equiv.symm_apply_eq]
  exact canonW_fixed_iff hn (V x)

/-- The membership test `x ∈ {V⁻¹ 0, V⁻¹ 1}` unfolds to `(V x).val ≤ 1`. -/
private theorem mem_convW_fixedPoints_iff {n : ℕ} (hn : 4 ≤ n) (V : Equiv.Perm (Fin n))
    (x : Fin n) :
    (x = V.symm ⟨0, by omega⟩ ∨ x = V.symm ⟨1, by omega⟩) ↔ (V x).val ≤ 1 := by
  simp only [Equiv.eq_symm_apply]
  constructor
  · rintro (h | h)
    · simp [h]
    · simp [h]
  · intro h
    rcases (show (V x).val = 0 ∨ (V x).val = 1 by omega) with h0 | h1
    · exact Or.inl (Fin.ext h0)
    · exact Or.inr (Fin.ext h1)

/-- **`{V⁻¹ 0, V⁻¹ 1}` is exactly `U_V`'s fixed-point set** ([Persistence] §8, Finding 1: the
constant family's persistence). -/
theorem convW_fixedPoints {n : ℕ} (hn : 4 ≤ n) (V : Equiv.Perm (Fin n)) :
    {x : Fin n | convW V x = x} = {V.symm ⟨0, by omega⟩, V.symm ⟨1, by omega⟩} := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  rw [convW_fixed_iff hn, mem_convW_fixedPoints_iff hn]

/-- **The reading `ℓ_V`**: the indicator of `{V⁻¹ 0, V⁻¹ 1}`. -/
noncomputable def convReading {n : ℕ} (hn : 4 ≤ n) (V : Equiv.Perm (Fin n)) : Fin n → Bool :=
  fun x => decide (x = V.symm ⟨0, by omega⟩ ∨ x = V.symm ⟨1, by omega⟩)

private theorem convReading_eq_decide_le {n : ℕ} (hn : 4 ≤ n) (V : Equiv.Perm (Fin n)) (x : Fin n) :
    convReading hn V x = decide ((V x).val ≤ 1) := by
  unfold convReading
  rw [decide_eq_decide]
  exact mem_convW_fixedPoints_iff hn V x

/-- **The reading persists** ([Persistence] §8, Finding 1: `ℓ_V ∘ U_V = ℓ_V`). -/
theorem convReading_invariant {n : ℕ} (hn : 4 ≤ n) (V : Equiv.Perm (Fin n)) (x : Fin n) :
    convReading hn V (convW V x) = convReading hn V x := by
  rw [convReading_eq_decide_le hn V (convW V x), convW_apply]
  simp only [apply_symm_apply]
  rw [convReading_eq_decide_le hn V x, decide_eq_decide]
  exact canonW_val_le_one_iff hn (V x)

/-- **The reading factors through `κ_V`** ([Persistence] §8, Finding 1). -/
theorem convReading_factors {n : ℕ} (hn : 4 ≤ n) (V : Equiv.Perm (Fin n)) (x y : Fin n)
    (h : convLens hn V x = convLens hn V y) : convReading hn V x = convReading hn V y := by
  rw [convReading_eq_decide_le hn V x, convReading_eq_decide_le hn V y]
  unfold convLens at h
  simp only [Function.comp_apply] at h
  have hv : (mergeMap n (by omega) (V x)).val = (mergeMap n (by omega) (V y)).val :=
    congrArg Fin.val h
  rcases Nat.lt_or_ge (V x).val 2 with hx | hx
  · rcases Nat.lt_or_ge (V y).val 2 with hy | hy
    · simp [show (V x).val ≤ 1 by omega, show (V y).val ≤ 1 by omega]
    · rw [mergeMap_apply_of_le (by omega) (by omega : (V x).val ≤ 1),
        mergeMap_apply_of_gt (by omega) hy] at hv
      omega
  · rcases Nat.lt_or_ge (V y).val 2 with hy | hy
    · rw [mergeMap_apply_of_gt (by omega) hx,
        mergeMap_apply_of_le (by omega) (by omega : (V y).val ≤ 1)] at hv
      omega
    · simp [show ¬ (V x).val ≤ 1 by omega, show ¬ (V y).val ≤ 1 by omega]

/-! ### The centralizer bound -/

private theorem canonW_val_of_le {n : ℕ} (hn : 4 ≤ n) {x : Fin n} (hx : 2 ≤ x.val) :
    (canonW n x).val = (x.val - 2 + 1) % (n - 2) + 2 :=
  shiftedCycle_val_of_le (by omega) hx

/-- The `k`-th iterate of `canonW` on the cycled part, as a closed Nat formula. -/
private theorem canonW_iterate_val {n : ℕ} (hn : 4 ≤ n) {a : Fin n} (ha : 2 ≤ a.val) (k : ℕ) :
    (((canonW n) ^ k) a).val = (a.val - 2 + k) % (n - 2) + 2 := by
  induction k with
  | zero =>
      simp only [pow_zero, Equiv.Perm.coe_one, id_eq]
      rw [Nat.mod_eq_of_lt (by omega)]
      omega
  | succ k ih =>
      have hstep : (((canonW n) ^ (k + 1)) a) = canonW n (((canonW n) ^ k) a) := by
        rw [_root_.pow_succ']; rfl
      rw [hstep]
      have hSle : 2 ≤ (((canonW n) ^ k) a).val := by rw [ih]; omega
      rw [canonW_val_of_le hn hSle, ih]
      have he : (a.val - 2 + k) % (n - 2) + 2 - 2 + 1 = (a.val - 2 + k) % (n - 2) + 1 := by omega
      rw [he]
      have hfin : ((a.val - 2 + k) % (n - 2) + 1) % (n - 2)
          = (a.val - 2 + k + 1) % (n - 2) := by simp [Nat.add_mod]
      have hassoc : a.val - 2 + k + 1 = a.val - 2 + (k + 1) := by omega
      rw [hfin, hassoc]

/-- **Transitivity on the cycled part** ([Persistence] §8, Finding 1: the cycle is a single
orbit): any two points with `val ≥ 2` are connected by some power of `canonW`. -/
theorem canonW_exists_pow_eq {n : ℕ} (hn : 4 ≤ n) {a b : Fin n} (ha : 2 ≤ a.val)
    (hb : 2 ≤ b.val) : ∃ k : ℕ, ((canonW n) ^ k) a = b := by
  refine ⟨(b.val - 2) + (n - 2) - (a.val - 2), ?_⟩
  apply Fin.ext
  rw [canonW_iterate_val hn ha]
  have hA : a.val - 2 < n - 2 := by have := a.isLt; omega
  have hB : b.val - 2 < n - 2 := by have := b.isLt; omega
  have h1 : a.val - 2 + (b.val - 2 + (n - 2) - (a.val - 2)) = (b.val - 2) + (n - 2) := by omega
  rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt hB]
  omega

private theorem canonW_comm_apply {n : ℕ} (g : Equiv.Perm (Fin n)) (h : g * canonW n = canonW n * g)
    (y : Fin n) : g (canonW n y) = canonW n (g y) := by
  have := congrFun (congrArg (fun e : Equiv.Perm (Fin n) => (e : Fin n → Fin n)) h) y
  simpa [Equiv.Perm.mul_apply] using this

private theorem canonW_comm_apply_pow {n : ℕ} (g : Equiv.Perm (Fin n))
    (h : g * canonW n = canonW n * g)
    (k : ℕ) (y : Fin n) : g (((canonW n) ^ k) y) = ((canonW n) ^ k) (g y) := by
  induction k with
  | zero => simp
  | succ k ih =>
      calc g (((canonW n) ^ (k + 1)) y) = g (canonW n (((canonW n) ^ k) y)) := by
            rw [_root_.pow_succ', Equiv.Perm.mul_apply]
        _ = canonW n (g (((canonW n) ^ k) y)) := canonW_comm_apply g h _
        _ = canonW n (((canonW n) ^ k) (g y)) := by rw [ih]
        _ = ((canonW n) ^ (k + 1)) (g y) := by rw [_root_.pow_succ', Equiv.Perm.mul_apply]

/-- A commuting permutation carries `canonW`'s fixed points ([Persistence] §8, Finding 1: "a
commuting `g` permutes the two fixed points"). -/
theorem canonW_centralizer_mem01 {n : ℕ} (hn : 4 ≤ n) (g : Equiv.Perm (Fin n))
    (h : g * canonW n = canonW n * g) (y : Fin n) (hy : y.val ≤ 1) : (g y).val ≤ 1 := by
  have h1 : canonW n y = y := (canonW_fixed_iff hn y).mpr hy
  have h2 := canonW_comm_apply g h y
  rw [h1] at h2
  exact (canonW_fixed_iff hn (g y)).mp h2.symm

/-- **A centralizing permutation is determined by its values at `0` and one cycled point**
([Persistence] §8, Finding 1: "on the cycle is determined by the image of one point"). No general
cycle-centralizer theorem is used — `canonW_exists_pow_eq` supplies the transitivity directly. -/
theorem canonW_centralizer_eq_of_agree {n : ℕ} (hn : 4 ≤ n) (g g' : Equiv.Perm (Fin n))
    (h : g * canonW n = canonW n * g) (h' : g' * canonW n = canonW n * g')
    (p0 p1 p2 : Fin n) (hp0 : p0.val = 0) (hp1 : p1.val = 1) (hp2 : p2.val = 2)
    (h0 : g p0 = g' p0) (hx0 : g p2 = g' p2) : g = g' := by
  have h0v : (g p0).val = (g' p0).val := congrArg Fin.val h0
  have hg0 : (g p0).val ≤ 1 := canonW_centralizer_mem01 hn g h p0 (by omega)
  have hg1 : (g p1).val ≤ 1 := canonW_centralizer_mem01 hn g h p1 (by omega)
  have hg0' : (g' p0).val ≤ 1 := canonW_centralizer_mem01 hn g' h' p0 (by omega)
  have hg1' : (g' p1).val ≤ 1 := canonW_centralizer_mem01 hn g' h' p1 (by omega)
  have hne : g p0 ≠ g p1 :=
    fun hc => (by omega : p0.val ≠ p1.val) (congrArg Fin.val (g.injective hc))
  have hne' : g' p0 ≠ g' p1 :=
    fun hc => (by omega : p0.val ≠ p1.val) (congrArg Fin.val (g'.injective hc))
  have hnev : (g p0).val ≠ (g p1).val := fun hc => hne (Fin.ext hc)
  have hnev' : (g' p0).val ≠ (g' p1).val := fun hc => hne' (Fin.ext hc)
  have h1v : (g p1).val = (g' p1).val := by omega
  apply Equiv.ext
  intro y
  rcases Nat.lt_or_ge y.val 2 with hy | hy
  · have hy01 : y = p0 ∨ y = p1 := by
      rcases (show y.val = 0 ∨ y.val = 1 by omega) with hv | hv
      · exact Or.inl (Fin.ext (by omega))
      · exact Or.inr (Fin.ext (by omega))
    rcases hy01 with rfl | rfl
    · exact h0
    · exact Fin.ext h1v
  · obtain ⟨k, hk⟩ := canonW_exists_pow_eq hn (a := p2) (b := y) (by omega) hy
    rw [← hk, canonW_comm_apply_pow g h, canonW_comm_apply_pow g' h', hx0]

/-- **The centralizer bound** ([Persistence] §8, Finding 1: "a commuting `g` permutes the two
fixed points (≤ 2 choices) and on the cycle is determined by the image of one point (≤ n
choices)"): at most `2n` permutations conjugation-fix `canonW`. The exact value `2(n − 2)` is not
needed — this ≤ `2n` bound is what the world floor uses. -/
theorem canonW_centralizer_card_le {n : ℕ} (hn : 4 ≤ n) :
    (Finset.univ.filter
      (fun g : Equiv.Perm (Fin n) => g * canonW n * g⁻¹ = canonW n)).card ≤ 2 * n := by
  classical
  set p0 : Fin n := ⟨0, by omega⟩ with hp0def
  set p1 : Fin n := ⟨1, by omega⟩ with hp1def
  set p2 : Fin n := ⟨2, by omega⟩ with hp2def
  have hp0 : p0.val = 0 := rfl
  have hp1 : p1.val = 1 := rfl
  have hp2 : p2.val = 2 := rfl
  have hinj : Set.InjOn (fun g : Equiv.Perm (Fin n) => (decide (g p0 = p1), g p2))
      ↑(Finset.univ.filter
        (fun g : Equiv.Perm (Fin n) => g * canonW n * g⁻¹ = canonW n)) := by
    intro g hg g' hg' heq
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hg hg'
    replace hg : g * canonW n = canonW n * g := mul_inv_eq_iff_eq_mul.mp hg
    replace hg' : g' * canonW n = canonW n * g' := mul_inv_eq_iff_eq_mul.mp hg'
    simp only [Prod.mk.injEq] at heq
    obtain ⟨hb, hx0⟩ := heq
    rw [decide_eq_decide] at hb
    have hmemg : g p0 = p0 ∨ g p0 = p1 := by
      have := canonW_centralizer_mem01 hn g hg p0 (by omega)
      rcases (show (g p0).val = 0 ∨ (g p0).val = 1 by omega) with hv | hv
      · exact Or.inl (Fin.ext (by omega))
      · exact Or.inr (Fin.ext (by omega))
    have hmemg' : g' p0 = p0 ∨ g' p0 = p1 := by
      have := canonW_centralizer_mem01 hn g' hg' p0 (by omega)
      rcases (show (g' p0).val = 0 ∨ (g' p0).val = 1 by omega) with hv | hv
      · exact Or.inl (Fin.ext (by omega))
      · exact Or.inr (Fin.ext (by omega))
    have h0 : g p0 = g' p0 := by
      rcases hmemg with hgv | hgv <;> rcases hmemg' with hgv' | hgv' <;>
        simp_all [Fin.ext_iff]
    exact canonW_centralizer_eq_of_agree hn g g' hg hg' p0 p1 p2 hp0 hp1 hp2 h0 hx0
  have hcard := Finset.card_le_card_of_injOn _ (fun a _ => Finset.mem_univ _) hinj
  simpa [Fintype.card_prod, Fintype.card_bool] using hcard

/-! ### The world floor -/

private theorem lensCode_inj' {n m : ℕ} : Function.Injective (lensCode (n := n) (m := m)) := by
  intro ℓ ℓ' h
  have h2 : lensTable ℓ = lensTable ℓ' := Encodable.encode_injective h
  funext x
  have hx : ((ℓ x : Fin m) : ℕ) = ((ℓ' x : Fin m) : ℕ) :=
    (List.map_inj_left.mp h2) x (List.mem_finRange x)
  exact Fin.val_injective hx

/-- **The fibres of `V ↦ U_V` are centralizer cosets** ([Persistence] §8, Finding 2: "the realized
worlds number `n!/(2(n−2))`" — this bounds the fibres by the `≤ 2n` centralizer, giving the same
counting shape as `PersistenceCapacity.collapse_count`). -/
theorem convW_collapse_count {n : ℕ} (hn : 4 ≤ n) (L : ℕ) :
    {V : Equiv.Perm (Fin n) | KE (lensCode (⇑(convW V))) ≤ L}.ncard ≤ 2 ^ (L + 1) * (2 * n) := by
  classical
  set f : Equiv.Perm (Fin n) → ℕ := fun V => lensCode (⇑(convW V)) with hf
  set S : Finset (Equiv.Perm (Fin n)) := Finset.univ.filter fun V => KE (f V) ≤ L with hSdef
  set T : Finset ℕ := (finite_KE_le L).toFinset with hTdef
  have hfib : ∀ v ∈ T, (S.filter fun V => f V = v).card ≤ 2 * n := by
    intro v _
    rcases Finset.eq_empty_or_nonempty (S.filter fun V => f V = v) with hemp | ⟨W, hW⟩
    · simp [hemp]
    · have hWv : f W = v := (Finset.mem_filter.mp hW).2
      have hmaps : ∀ U ∈ S.filter fun V => f V = v,
          U * W⁻¹ ∈ Finset.univ.filter
            fun g : Equiv.Perm (Fin n) => g * canonW n * g⁻¹ = canonW n := by
        intro U hU
        have hUv : f U = v := (Finset.mem_filter.mp hU).2
        have hUW : (⇑(convW U) : Fin n → Fin n) = ⇑(convW W) := lensCode_inj' (hUv.trans hWv.symm)
        have hUW' : convW U = convW W := Equiv.coe_fn_injective hUW
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        change (U * W⁻¹) * canonW n * (U * W⁻¹)⁻¹ = canonW n
        have hcw : convW U = convW W := hUW'
        unfold convW at hcw
        calc (U * W⁻¹) * canonW n * (U * W⁻¹)⁻¹
            = U * (W⁻¹ * canonW n * W) * U⁻¹ := by group
          _ = U * (U⁻¹ * canonW n * U) * U⁻¹ := by rw [← hcw]
          _ = canonW n := by group
      have hinj : Set.InjOn (fun U => U * W⁻¹) ↑(S.filter fun V => f V = v) :=
        fun a _ c _ hac => by
          have heq : a * W⁻¹ * W = c * W⁻¹ * W := congrArg (· * W) hac
          simpa using heq
      have hcard := Finset.card_le_card_of_injOn (fun U => U * W⁻¹) hmaps hinj
      exact le_trans hcard (canonW_centralizer_card_le hn)
  have hmapsT : ∀ U ∈ S, f U ∈ T := by
    intro U hU
    simpa [hTdef] using (Finset.mem_filter.mp hU).2
  have hmain := Finset.card_le_mul_card_image_of_maps_to hmapsT (2 * n) hfib
  have hT : T.card ≤ 2 ^ (L + 1) := by
    have := card_KE_le L
    rwa [Set.ncard_eq_toFinset_card _ (finite_KE_le L)] at this
  have hSset : {V : Equiv.Perm (Fin n) | KE (f V) ≤ L} = ↑S := by
    ext V; simp [hSdef]
  rw [show {V : Equiv.Perm (Fin n) | KE (lensCode (⇑(convW V))) ≤ L}
      = {V : Equiv.Perm (Fin n) | KE (f V) ≤ L} from rfl, hSset, Set.ncard_coe_finset]
  calc S.card ≤ (2 * n) * T.card := hmain
    _ ≤ (2 * n) * 2 ^ (L + 1) := Nat.mul_le_mul_left _ hT
    _ = 2 ^ (L + 1) * (2 * n) := Nat.mul_comm _ _

/-- **The world floor** ([Persistence] §8, Finding 2: "one of them satisfies `K(U) ≥ log₂ n! −
O(log₂ n)`"): whenever the centralizer-coset count undercuts `n!`, some realized `U_V`'s table
costs more than `L`. -/
theorem convW_world_floor {n : ℕ} (hn : 4 ≤ n) (L : ℕ) (hL : 2 ^ (L + 1) * (2 * n) < n !) :
    ∃ V : Equiv.Perm (Fin n), L < KE (lensCode (⇑(convW V))) := by
  by_contra hc
  push Not at hc
  have hall : {V : Equiv.Perm (Fin n) | KE (lensCode (⇑(convW V))) ≤ L} = Set.univ := by
    ext V; simpa using hc V
  have hcard := convW_collapse_count hn L
  rw [hall, Set.ncard_univ] at hcard
  have huniv : Nat.card (Equiv.Perm (Fin n)) = n ! := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
  rw [huniv] at hcard
  omega

/-- Any permutation fixing the cycled part pointwise and mapping `{0, 1}` into itself commutes
with `canonW` — covers both `1` and `swap p0 p1`, which is all `convW_recovery` needs. -/
private theorem centralizes_of_fixes_outside01 {n : ℕ} (hn : 4 ≤ n) (τ : Equiv.Perm (Fin n))
    (hfix : ∀ x, 2 ≤ x.val → τ x = x) (hmap : ∀ x, x.val ≤ 1 → (τ x).val ≤ 1) :
    τ * canonW n = canonW n * τ := by
  have hmap' : ∀ x, x.val ≤ 1 → (τ.symm x).val ≤ 1 := by
    intro x hx
    by_contra hc
    have hx2 : 2 ≤ (τ.symm x).val := by omega
    have hτ := hfix (τ.symm x) hx2
    rw [Equiv.apply_symm_apply] at hτ
    omega
  apply Equiv.ext
  intro y
  change τ (canonW n y) = canonW n (τ y)
  rcases Nat.lt_or_ge y.val 2 with hy | hy
  · have hy1 : y.val ≤ 1 := by omega
    have h1 : canonW n y = y := (canonW_fixed_iff hn y).mpr hy1
    have hty : (τ y).val ≤ 1 := hmap y hy1
    have h2 : canonW n (τ y) = τ y := (canonW_fixed_iff hn (τ y)).mpr hty
    rw [h1, h2]
  · have hcw : (canonW n y).val = 2 ∨ 2 ≤ (canonW n y).val := by
      have := (canonW_val_le_one_iff hn y).not
      omega
    have hcw2 : 2 ≤ (canonW n y).val := by omega
    rw [hfix (canonW n y) hcw2, hfix y hy]

/-- **Recovery** ([Persistence] §8, Finding 2: "the merged lens determines the world exactly …
because the two preimages differ by the swap of the fixed labels, which centralizes `canonW`"). -/
theorem convW_recovery {n : ℕ} (hn : 4 ≤ n) (U W : Equiv.Perm (Fin n))
    (h : convLens hn U = convLens hn W) : convW U = convW W := by
  have hpt : ∀ y, mergeMap n (by omega) (U y) = mergeMap n (by omega) (W y) :=
    fun y => congrFun h y
  have hval : ∀ y, (mergeMap n (by omega) (U y)).val = (mergeMap n (by omega) (W y)).val :=
    fun y => congrArg Fin.val (hpt y)
  have hstep1 : ∀ y, 2 ≤ (U y).val → W y = U y := by
    intro y hy
    have hv := hval y
    rw [mergeMap_apply_of_gt (by omega) (by omega : 1 < (U y).val)] at hv
    have hwy2 : 2 ≤ (W y).val := by
      by_contra hc
      have hc' : (W y).val ≤ 1 := by omega
      rw [mergeMap_apply_of_le (by omega) hc'] at hv
      omega
    rw [mergeMap_apply_of_gt (by omega) (by omega : 1 < (W y).val)] at hv
    have hveq : (U y).val = (W y).val := by omega
    exact Fin.ext hveq.symm
  have hstep2 : ∀ y, (U y).val ≤ 1 → (W y).val ≤ 1 := by
    intro y hy
    have hv := hval y
    rw [mergeMap_apply_of_le (by omega) hy] at hv
    by_contra hc
    have hwy2 : 1 < (W y).val := by omega
    rw [mergeMap_apply_of_gt (by omega) hwy2] at hv
    omega
  set τ : Equiv.Perm (Fin n) := W * U⁻¹ with hτdef
  have hfix : ∀ x, 2 ≤ x.val → τ x = x := by
    intro x hx
    have hy : U (U⁻¹ x) = x := Equiv.apply_symm_apply U x
    have hxU : 2 ≤ (U (U⁻¹ x)).val := by rw [hy]; exact hx
    have hWU := hstep1 (U⁻¹ x) hxU
    change W (U⁻¹ x) = x
    rw [hWU, hy]
  have hmap : ∀ x, x.val ≤ 1 → (τ x).val ≤ 1 := by
    intro x hx
    have hy : U (U⁻¹ x) = x := Equiv.apply_symm_apply U x
    have hxU : (U (U⁻¹ x)).val ≤ 1 := by rw [hy]; exact hx
    change (W (U⁻¹ x)).val ≤ 1
    exact hstep2 (U⁻¹ x) hxU
  have hcomm : τ * canonW n = canonW n * τ := centralizes_of_fixes_outside01 hn τ hfix hmap
  have hτW : W = τ * U := by rw [hτdef]; group
  have hconj : τ⁻¹ * canonW n * τ = canonW n := by
    calc τ⁻¹ * canonW n * τ = τ⁻¹ * (canonW n * τ) := by group
      _ = τ⁻¹ * (τ * canonW n) := by rw [← hcomm]
      _ = canonW n := by group
  change U⁻¹ * canonW n * U = W⁻¹ * canonW n * W
  rw [hτW]
  calc U⁻¹ * canonW n * U = U⁻¹ * (τ⁻¹ * canonW n * τ) * U := by rw [hconj]
    _ = (τ * U)⁻¹ * canonW n * (τ * U) := by group

/-! ### The capstone -/

/-- **The canonical-form-lens pricing family** ([Persistence] §8, Propositions 8.35(iii) and
8.36, Remark 8.37: the cap of Proposition 8.35(iii) — the loss from declining a move up the order
on pricing points, bounded by twice the declined move's address — is attained at twice the
address by this very pair, so together with Proposition 8.36(iii)'s attainment at once, the cap's
constant is exactly two).

This bundles the counting core the pricing argument consumes: `κ_V` descends `U_V` to `canonWt`
(`convDescent`); the reading `ℓ_V` persists under `U_V` and factors through `κ_V`
(`convReading_invariant`, `convReading_factors`) — so `([n], κ_V)` and `([n], id)` are both
Proposition 8.29 pricing points for the constant family `ℓ_V` generates; and, past the arithmetic
threshold `hL`, some realized `U_V`'s table costs more than `L` bits (`convW_world_floor`) — the
counting floor Finding 2 reads as `K(U) ≥ log₂ n! − O(log₂ n)`. The `K`-displays themselves and
the `A`-arithmetic of Proposition 8.35 stay on §8's standing transport boundary and are not
claimed here; only the counts are. -/
theorem canonicalFormLens_family {n : ℕ} (hn : 4 ≤ n) (L : ℕ) (hL : 2 ^ (L + 1) * (2 * n) < n !) :
    ∃ V : Equiv.Perm (Fin n),
      (∀ x, convLens hn V (convW V x) = canonWt n (convLens hn V x))
      ∧ (∀ x, convReading hn V (convW V x) = convReading hn V x)
      ∧ (∀ x y, convLens hn V x = convLens hn V y → convReading hn V x = convReading hn V y)
      ∧ L < KE (lensCode (⇑(convW V))) := by
  obtain ⟨V, hV⟩ := convW_world_floor hn L hL
  exact ⟨V, convDescent hn V, convReading_invariant hn V, convReading_factors hn V, hV⟩

/-- **A concrete instance** ([Persistence] §8, Remark 8.37's growing margin): `n = 6` clears the
threshold `L = 4` with `2 ^ 5 · 12 = 384 < 720 = 6!`, checked by `decide` on the explicit
numerals. -/
theorem canonicalFormLens_instance :
    ∃ V : Equiv.Perm (Fin 6),
      (∀ x, convLens (show 4 ≤ 6 by norm_num) V (convW V x)
          = canonWt 6 (convLens (show 4 ≤ 6 by norm_num) V x))
      ∧ (∀ x, convReading (show 4 ≤ 6 by norm_num) V (convW V x)
          = convReading (show 4 ≤ 6 by norm_num) V x)
      ∧ (∀ x y, convLens (show 4 ≤ 6 by norm_num) V x = convLens (show 4 ≤ 6 by norm_num) V y →
          convReading (show 4 ≤ 6 by norm_num) V x = convReading (show 4 ≤ 6 by norm_num) V y)
      ∧ 4 < KE (lensCode (⇑(convW V))) :=
  canonicalFormLens_family (show 4 ≤ 6 by norm_num) 4 (by decide)

end CanonicalFormLens

/-- info: 'CanonicalFormLens.canonicalFormLens_family' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CanonicalFormLens.canonicalFormLens_family

/-- info: 'CanonicalFormLens.canonicalFormLens_instance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CanonicalFormLens.canonicalFormLens_instance
