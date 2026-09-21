/-
Copyright (c) 2026 Mykola Palamarchuk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mykola Palamarchuk
-/
module

public import ALT.CodingTheoremWeak
public import ALT.BitStringPrimrec

-- Formal-check file, not Mathlib-destined: opt out of the house-style header linter.
set_option linter.style.header false

/-!
# The online Kraft–Chaitin assignment ([Discovery] §1.1, FV-21)

Provenance: [Discovery] §1.1 and FV-21, over the fixed-width code `PrefixMachine.bitsFixed` of
`ALT/CodingTheoremWeak.lean` and the bit-string computability layer of `ALT/BitStringPrimrec.lean`.

## What this establishes

The online Kraft–Chaitin codeword assignment, effective and invariant-preserving:

* `kcServe`, `kcRun`, `kcWord`: serve a stream of length requests against a free space of dyadic
  intervals, greedily, one request per step.
* `primrec₂_kcServe`, `computable_kcRun`, `computable_kcWord`: the assignment is effective.
* `kcRun_invariant`: at every step of a request stream whose partial sums stay at most one, the
  free lengths stay pairwise distinct, every request so far was served at its own requested length,
  the assigned words are pairwise prefix-free, and the assigned mass plus the free measure is one.
* `kcWord_prefixFree`: the assigned words, over the whole stream, are pairwise prefix-free.

## What this does NOT establish (flagged)

The coding theorem this assignment serves — the `O(1)` form over a lower-semicomputable
semimeasure's own request stream — is not attempted here.
-/


@[expose] public section

namespace PrefixMachine

open Nat.Partrec Nat.Partrec.Code AdditiveComplexity CodeEvalLaws KolmogorovComplexity

/-- Free dyadic intervals `[a / 2 ^ l, (a + 1) / 2 ^ l)`, as `(length, numerator)` pairs. -/
abbrev FreeSpace := List (ℕ × ℕ)

/-! ## `bitsFixed` is primitive recursive -/

/-- One step of peeling `bitsFixed`'s low bit: idle once the counter has bottomed out, otherwise
decrement the counter, halve the value, and cons the peeled bit onto the accumulator. -/
private def bitsFixedStep (st : ℕ × ℕ × List Bool) : ℕ × ℕ × List Bool :=
  if st.1 = 0 then st else (st.1 - 1, st.2.1 / 2, decide (st.2.1 % 2 = 1) :: st.2.2)

/-- `bitsFixed` by fuel: peel `k` low bits of `i`, consing each, over the state `(k, i, acc)`. -/
private def bitsFixedFuel (k i : ℕ) : List Bool :=
  (bitsFixedStep^[k] (k, i, [])).2.2

private theorem bitsFixedStep_iterate_acc (k i : ℕ) (acc : List Bool) :
    bitsFixedStep^[k] (k, i, acc) = (0, i / 2 ^ k, bitsFixed k i ++ acc) := by
  induction k generalizing i acc with
  | zero => simp [bitsFixed]
  | succ k ih =>
      rw [Function.iterate_succ_apply]
      have hstep : bitsFixedStep (k + 1, i, acc) = (k, i / 2, decide (i % 2 = 1) :: acc) := by
        simp [bitsFixedStep]
      rw [hstep, ih (i / 2) (decide (i % 2 = 1) :: acc)]
      have hpow : i / 2 / 2 ^ k = i / 2 ^ (k + 1) := by
        rw [Nat.div_div_eq_div_mul, pow_succ, mul_comm]
      rw [hpow]
      have hbf : bitsFixed (k + 1) i = bitsFixed k (i / 2) ++ [decide (i % 2 = 1)] := rfl
      rw [hbf, List.append_assoc]
      simp

private theorem bitsFixedFuel_eq (k i : ℕ) : bitsFixedFuel k i = bitsFixed k i := by
  unfold bitsFixedFuel
  rw [bitsFixedStep_iterate_acc, List.append_nil]

private theorem primrec_bitsFixedStep : Primrec bitsFixedStep := by
  have hc : Primrec fun st : ℕ × ℕ × List Bool => decide (st.1 = 0) :=
    Primrec.eq.decide.comp Primrec.fst (Primrec.const 0)
  have hpred : Primrec fun st : ℕ × ℕ × List Bool => st.1 - 1 :=
    Primrec.nat_sub.comp Primrec.fst (Primrec.const 1)
  have hdiv : Primrec fun st : ℕ × ℕ × List Bool => st.2.1 / 2 :=
    Primrec.nat_div.comp (Primrec.fst.comp Primrec.snd) (Primrec.const 2)
  have hbit : Primrec fun st : ℕ × ℕ × List Bool => decide (st.2.1 % 2 = 1) :: st.2.2 :=
    Primrec.list_cons.comp
      (Primrec.eq.decide.comp
        (Primrec.nat_mod.comp (Primrec.fst.comp Primrec.snd) (Primrec.const 2))
        (Primrec.const 1))
      (Primrec.snd.comp Primrec.snd)
  have hfalse : Primrec fun st : ℕ × ℕ × List Bool =>
      (st.1 - 1, st.2.1 / 2, decide (st.2.1 % 2 = 1) :: st.2.2) :=
    hpred.pair (hdiv.pair hbit)
  have := Primrec.cond hc Primrec.id hfalse
  refine this.of_eq fun st => ?_
  unfold bitsFixedStep
  simp only [id]
  rw [Bool.cond_decide]

private theorem primrec₂_bitsFixedFuel : Primrec₂ bitsFixedFuel := by
  have hh : Primrec₂ fun (_ : ℕ × ℕ) (x : ℕ × ℕ × List Bool) => bitsFixedStep x :=
    primrec_bitsFixedStep.comp Primrec.snd
  have := Primrec.nat_iterate (α := ℕ × ℕ) Primrec.fst
    (Primrec.fst.pair (Primrec.snd.pair (Primrec.const ([] : List Bool)))) hh
  exact (Primrec.snd.comp (Primrec.snd.comp this)).of_eq fun p => rfl

private theorem primrec₂_bitsFixed : Primrec₂ bitsFixed := by
  have := primrec₂_bitsFixedFuel
  exact this.of_eq bitsFixedFuel_eq

/-! ## The word–interval dictionary -/

/-- Splitting a fixed width into a high and a low part. -/
private theorem bitsFixed_add (m n a : ℕ) :
    bitsFixed (m + n) a = bitsFixed m (a / 2 ^ n) ++ bitsFixed n a := by
  induction n generalizing a with
  | zero => simp [bitsFixed]
  | succ n ih =>
      have hL : bitsFixed (m + (n + 1)) a = bitsFixed (m + n) (a / 2) ++ [decide (a % 2 = 1)] := rfl
      have hR : bitsFixed (n + 1) a = bitsFixed n (a / 2) ++ [decide (a % 2 = 1)] := rfl
      rw [hL, ih (a / 2), hR, List.append_assoc]
      congr 2
      rw [Nat.div_div_eq_div_mul, pow_succ, mul_comm]

/-- `(l, a)`'s dyadic interval contains `(l', a')`'s: `l ≤ l'` and `a` is `a'`'s ancestor at
level `l`. Exactly the prefix relation of the two `bitsFixed` codewords, given both numerators are
within their own width (`bitsFixed_prefix_iff`). -/
def Nested (l a l' a' : ℕ) : Prop := l ≤ l' ∧ a' / 2 ^ (l' - l) = a

/-- Either code prefixes the other. -/
def Comparable (l a l' a' : ℕ) : Prop := Nested l a l' a' ∨ Nested l' a' l a

private theorem Nested.trans {l1 a1 l2 a2 l3 a3 : ℕ} (h12 : Nested l1 a1 l2 a2)
    (h23 : Nested l2 a2 l3 a3) : Nested l1 a1 l3 a3 := by
  obtain ⟨hle12, he12⟩ := h12
  obtain ⟨hle23, he23⟩ := h23
  refine ⟨hle12.trans hle23, ?_⟩
  rw [← Nat.sub_add_sub_cancel hle23 hle12, pow_add, ← Nat.div_div_eq_div_mul, he23, he12]

/-- **Refinement preserves incomparability**: a code incomparable with `(l', a')` stays
incomparable after being refined to any sub-code `(l'', a'')` nested inside it. -/
private theorem not_comparable_of_nested {l a l' a' l'' a'' : ℕ} (hn : Nested l a l'' a'')
    (hnc : ¬ Comparable l a l' a') : ¬ Comparable l'' a'' l' a' := by
  rintro (h | h)
  · exact hnc (Or.inl (hn.trans h))
  · obtain ⟨hle', he'⟩ := h
    obtain ⟨hle_l, he_l⟩ := hn
    rcases le_total l l' with hle | hle
    · refine hnc (Or.inl ⟨hle, ?_⟩)
      rw [← he', Nat.div_div_eq_div_mul, ← pow_add, Nat.sub_add_sub_cancel hle' hle, he_l]
    · refine hnc (Or.inr ⟨hle, ?_⟩)
      rw [← he_l, Nat.div_div_eq_div_mul, ← pow_add, Nat.sub_add_sub_cancel hle_l hle, he']

/-- **The word–interval dictionary.** -/
theorem bitsFixed_prefix_iff {l a l' a' : ℕ} (ha : a < 2 ^ l) (ha' : a' < 2 ^ l') :
    bitsFixed l a <+: bitsFixed l' a' ↔ Nested l a l' a' := by
  unfold Nested
  constructor
  · intro hpre
    have hlen : l ≤ l' := by
      have hle := hpre.length_le
      rwa [length_bitsFixed, length_bitsFixed] at hle
    have hsplit : bitsFixed l' a' = bitsFixed l (a' / 2 ^ (l' - l)) ++ bitsFixed (l' - l) a' := by
      rw [← bitsFixed_add, Nat.add_sub_cancel' hlen]
    rw [hsplit,
      List.isPrefix_append_of_length (by rw [length_bitsFixed, length_bitsFixed])] at hpre
    have heq : bitsFixed l a = bitsFixed l (a' / 2 ^ (l' - l)) := by
      have h1 := List.prefix_iff_eq_take.mp hpre
      rw [length_bitsFixed] at h1
      rwa [List.take_of_length_le (length_bitsFixed l _).le] at h1
    have hmul : a' < 2 ^ l * 2 ^ (l' - l) := by
      rw [← pow_add, Nat.add_sub_cancel' hlen]; exact ha'
    have hb : a' / 2 ^ (l' - l) < 2 ^ l := Nat.div_lt_of_lt_mul (by rwa [mul_comm] at hmul)
    exact ⟨hlen, by rw [← ofBitsFixed_bitsFixed ha, heq, ofBitsFixed_bitsFixed hb]⟩
  · rintro ⟨hle, heq⟩
    calc bitsFixed l a = bitsFixed l (a' / 2 ^ (l' - l)) := by rw [heq]
      _ <+: bitsFixed l (a' / 2 ^ (l' - l)) ++ bitsFixed (l' - l) a' := List.prefix_append _ _
      _ = bitsFixed l' a' := by rw [← bitsFixed_add, Nat.add_sub_cancel' hle]

/-- **The `Comparable`/prefix dictionary.** -/
private theorem comparable_iff_prefix {l a l' a' : ℕ} (ha : a < 2 ^ l) (ha' : a' < 2 ^ l') :
    Comparable l a l' a' ↔
      bitsFixed l a <+: bitsFixed l' a' ∨ bitsFixed l' a' <+: bitsFixed l a := by
  unfold Comparable
  rw [bitsFixed_prefix_iff ha ha', bitsFixed_prefix_iff ha' ha]

/-- A nested code's numerator stays within its own width, once the ancestor's does. -/
private theorem Nested.snd_lt {l a l' a' : ℕ} (h : Nested l a l' a') (ha : a < 2 ^ l) :
    a' < 2 ^ l' := by
  obtain ⟨hle, he⟩ := h
  have hdm := Nat.div_add_mod a' (2 ^ (l' - l))
  have hmod : a' % 2 ^ (l' - l) < 2 ^ (l' - l) := Nat.mod_lt _ (Nat.two_pow_pos _)
  rw [he] at hdm
  have : a' < 2 ^ (l' - l) * (a + 1) := by rw [Nat.mul_add, Nat.mul_one]; omega
  calc a' < 2 ^ (l' - l) * (a + 1) := this
    _ ≤ 2 ^ (l' - l) * 2 ^ l := by
        apply Nat.mul_le_mul_left
        omega
    _ = 2 ^ l' := by rw [← pow_add]; congr 1; omega

/-- Two codes of equal length and distinct numerators are never comparable. -/
private theorem not_comparable_of_eq_len_ne {l a a' : ℕ} (h : a ≠ a') : ¬ Comparable l a l a' := by
  rintro (⟨-, he⟩ | ⟨-, he⟩) <;> simp_all

private theorem Comparable.symm {l a l' a' : ℕ} (h : Comparable l a l' a') : Comparable l' a' l a :=
  Or.symm h

/-- A `2 ^ (n+1)`-multiple, plus one, divided by that same power, is the multiplier: the `+1`
never reaches a whole extra unit. -/
private theorem two_pow_mul_add_one_div (n a : ℕ) : (2 ^ (n + 1) * a + 1) / 2 ^ (n + 1) = a := by
  have h2 : (2 : ℕ) ≤ 2 ^ (n + 1) := by
    calc (2 : ℕ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (n + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  rw [Nat.mul_add_div (Nat.two_pow_pos _)]
  have h1 : (1 : ℕ) / 2 ^ (n + 1) = 0 := Nat.div_eq_of_lt (by omega)
  omega

/-! ## `splitBuild`: the pieces produced by one online split -/

/-- Splits the piece `(j, a)` down to width `k = j + m`, freeing the intermediate right-hand
pieces: `splitBuild j a m = (2 ^ m * a, [(j + m, 2 ^ m * a + 1), …, (j + 1, 2 * a + 1)])`. -/
def splitBuild (j a : ℕ) : ℕ → ℕ × FreeSpace
  | 0 => (a, [])
  | i + 1 => let r := splitBuild j a i
             (2 * r.1, (j + i + 1, 2 * r.1 + 1) :: r.2)

private theorem splitBuild_fst (j a : ℕ) : ∀ m, (splitBuild j a m).1 = 2 ^ m * a
  | 0 => by simp [splitBuild]
  | m + 1 => by
      change 2 * (splitBuild j a m).1 = 2 ^ (m + 1) * a
      rw [splitBuild_fst j a m, pow_succ]; ring

/-- The freed list at step `m + 1`, in the canonical `2 ^ (m + 1) * a` form. -/
private theorem splitBuild_snd_succ (j a m : ℕ) :
    (splitBuild j a (m + 1)).2 = (j + m + 1, 2 ^ (m + 1) * a + 1) :: (splitBuild j a m).2 := by
  have hrfl : (splitBuild j a (m + 1)).2
      = (j + m + 1, 2 * (splitBuild j a m).1 + 1) :: (splitBuild j a m).2 := rfl
  rw [hrfl, splitBuild_fst j a m]
  congr 2
  rw [pow_succ]; ring

/-- **The split invariant**: every freed piece stays a genuine descendant of `(j, a)` at a length
strictly between `j` and `j + m`, the freed pieces are pairwise incomparable, and the final
continuing piece `(j + m, 2 ^ m * a)` is incomparable with every one of them. -/
private theorem splitBuild_inv (j a : ℕ) : ∀ m,
    (∀ p ∈ (splitBuild j a m).2, j < p.1 ∧ p.1 ≤ j + m ∧ Nested j a p.1 p.2) ∧
      (∀ p ∈ (splitBuild j a m).2, ¬ Comparable (j + m) (2 ^ m * a) p.1 p.2) ∧
      (∀ p ∈ (splitBuild j a m).2, ∀ q ∈ (splitBuild j a m).2,
        p.1 ≠ q.1 → ¬ Comparable p.1 p.2 q.1 q.2) ∧
      ((splitBuild j a m).2.map Prod.fst).Nodup
  | 0 => by simp [splitBuild]
  | m + 1 => by
      obtain ⟨hmem, hfinal, hpair, hnodup⟩ := splitBuild_inv j a m
      have hsnd : (splitBuild j a (m + 1)).2
          = (j + m + 1, 2 ^ (m + 1) * a + 1) :: (splitBuild j a m).2 := splitBuild_snd_succ j a m
      have hnew : Nested (j + m) (2 ^ m * a) (j + m + 1) (2 ^ (m + 1) * a + 1) := by
        refine ⟨by omega, ?_⟩
        rw [show j + m + 1 - (j + m) = 1 from by omega,
          show 2 ^ (m + 1) * a + 1 = 2 ^ 1 * (2 ^ m * a) + 1 from by rw [pow_succ]; ring]
        exact two_pow_mul_add_one_div 0 (2 ^ m * a)
      have hcont : Nested (j + m) (2 ^ m * a) (j + (m + 1)) (2 ^ (m + 1) * a) := by
        refine ⟨by omega, ?_⟩
        rw [show j + (m + 1) - (j + m) = 1 from by omega, pow_one,
          show 2 ^ (m + 1) * a = 2 ^ m * a * 2 from by rw [pow_succ]; ring]
        exact Nat.mul_div_cancel _ (by norm_num)
      refine ⟨?_, ?_, ?_, ?_⟩
      · rintro p hp
        rw [hsnd, List.mem_cons] at hp
        rcases hp with rfl | hp
        · refine ⟨by omega, by omega, by omega, ?_⟩
          rw [show j + m + 1 - j = m + 1 from by omega]
          exact two_pow_mul_add_one_div m a
        · obtain ⟨h1, h2, h3⟩ := hmem p hp
          exact ⟨h1, by omega, h3⟩
      · rintro p hp
        rw [hsnd, List.mem_cons] at hp
        rcases hp with rfl | hp
        · exact not_comparable_of_eq_len_ne (by omega)
        · exact not_comparable_of_nested hcont (hfinal p hp)
      · rintro p hp q hq hne
        rw [hsnd, List.mem_cons] at hp hq
        rcases hp with rfl | hp <;> rcases hq with rfl | hq
        · exact absurd rfl hne
        · exact not_comparable_of_nested hnew (hfinal q hq)
        · exact fun hc => (not_comparable_of_nested hnew (hfinal p hp)) hc.symm
        · exact hpair p hp q hq hne
      · rw [hsnd]
        simp only [List.map_cons, List.nodup_cons]
        refine ⟨fun hmem' => ?_, hnodup⟩
        simp only [List.mem_map] at hmem'
        obtain ⟨p, hp, hpeq⟩ := hmem'
        obtain ⟨_, h2, _⟩ := hmem p hp
        omega

private theorem splitBuild_fst_bound {j a : ℕ} (ha : a < 2 ^ j) (m : ℕ) :
    (splitBuild j a m).1 < 2 ^ (j + m) := by
  rw [splitBuild_fst]
  calc 2 ^ m * a < 2 ^ m * 2 ^ j := mul_lt_mul_of_pos_left ha (Nat.two_pow_pos m)
    _ = 2 ^ (j + m) := by rw [← pow_add, Nat.add_comm]

private theorem splitBuild_snd_bound {j a : ℕ} (ha : a < 2 ^ j) (m : ℕ) :
    ∀ p ∈ (splitBuild j a m).2, p.2 < 2 ^ p.1 := fun p hp =>
  ((splitBuild_inv j a m).1 p hp).2.2.snd_lt ha

private theorem primrec₂_splitBuild :
    Primrec₂ (fun (ja : ℕ × ℕ) (m : ℕ) => splitBuild ja.1 ja.2 m) := by
  have hf : Primrec fun ja : ℕ × ℕ => ((ja.2, ([] : FreeSpace)) : ℕ × FreeSpace) :=
    Primrec.snd.pair (Primrec.const [])
  have hg : Primrec₂ fun (ja : ℕ × ℕ) (nr : ℕ × (ℕ × FreeSpace)) =>
      ((2 * nr.2.1, (ja.1 + nr.1 + 1, 2 * nr.2.1 + 1) :: nr.2.2) : ℕ × FreeSpace) := by
    have h1 : Primrec fun p : (ℕ × ℕ) × ℕ × ℕ × FreeSpace => 2 * p.2.2.1 :=
      Primrec.nat_mul.comp (Primrec.const 2) (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
    have h2 : Primrec fun p : (ℕ × ℕ) × ℕ × ℕ × FreeSpace => p.1.1 + p.2.1 + 1 :=
      Primrec.succ.comp
        (Primrec.nat_add.comp (Primrec.fst.comp Primrec.fst) (Primrec.fst.comp Primrec.snd))
    have h3 : Primrec fun p : (ℕ × ℕ) × ℕ × ℕ × FreeSpace => 2 * p.2.2.1 + 1 := Primrec.succ.comp h1
    have h4 : Primrec fun p : (ℕ × ℕ) × ℕ × ℕ × FreeSpace => p.2.2.2 :=
      Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
    exact h1.pair (Primrec.list_cons.comp (h2.pair h3) h4)
  have hres := Primrec.nat_rec hf hg
  refine hres.of_eq fun ja m => ?_
  induction m with
  | zero => rfl
  | succ m ih =>
      change
        (2 * (Nat.rec (ja.2, []) _ m : ℕ × FreeSpace).1,
          (ja.1 + m + 1, 2 * (Nat.rec (ja.2, []) _ m : ℕ × FreeSpace).1 + 1) ::
            (Nat.rec (ja.2, []) _ m : ℕ × FreeSpace).2)
          = splitBuild ja.1 ja.2 (m + 1)
      rw [ih]
      rfl

/-! ## `bestFreePair`: the largest free length at most `k` -/

/-- The free pair of the largest length at most `k`, found by a descending search: the length-`k`
entry if there is one, else the best among lengths below `k`. -/
def bestFreePair (free : FreeSpace) : ℕ → Option (ℕ × ℕ)
  | 0 => (free.filter (fun p => p.1 = 0)).head?
  | k + 1 => match (free.filter (fun p => p.1 = k + 1)).head? with
      | some p => some p
      | Option.none => bestFreePair free k

private theorem bestFreePair_spec (free : FreeSpace) : ∀ k,
    (∀ p, bestFreePair free k = some p → p ∈ free ∧ p.1 ≤ k ∧
      ∀ q ∈ free, q.1 ≤ k → q.1 ≤ p.1) ∧
    (bestFreePair free k = Option.none → ∀ p ∈ free, k < p.1)
  | 0 => by
      constructor
      · intro p hp
        unfold bestFreePair at hp
        rw [List.head?_eq_some_iff] at hp
        obtain ⟨tl, hp⟩ := hp
        have hmem : p ∈ free.filter (fun p => p.1 = 0) := by rw [hp]; exact List.mem_cons_self
        rw [List.mem_filter] at hmem
        obtain ⟨hmemf, heq0⟩ := hmem
        simp only [decide_eq_true_eq] at heq0
        exact ⟨hmemf, by omega, fun q _ hq0 => by omega⟩
      · intro hnone p hp
        unfold bestFreePair at hnone
        rw [List.head?_eq_none_iff, List.filter_eq_nil_iff] at hnone
        by_contra hle
        push Not at hle
        exact absurd (by simp; omega : decide (p.1 = 0) = true) (by simpa using hnone p hp)
  | k + 1 => by
      obtain ⟨hsome, hnone⟩ := bestFreePair_spec free k
      unfold bestFreePair
      rcases hmatch : (free.filter (fun p => p.1 = k + 1)).head? with _ | hd
      · simp only [hmatch]
        refine ⟨fun p hp => ?_, fun hnone' p hp => ?_⟩
        · obtain ⟨hmem, hle, hmax⟩ := hsome p hp
          refine ⟨hmem, by omega, fun q hq hqk => ?_⟩
          rcases Nat.lt_or_ge q.1 (k + 1) with hlt | hge
          · exact (hmax q hq (by omega)).trans (by omega)
          · exfalso
            rw [List.head?_eq_none_iff, List.filter_eq_nil_iff] at hmatch
            have hq1 : q.1 = k + 1 := by omega
            exact absurd (by simp [hq1] : decide (q.1 = k + 1) = true) (by simpa using hmatch q hq)
        · have hk : k < p.1 := hnone hnone' p hp
          rw [List.head?_eq_none_iff, List.filter_eq_nil_iff] at hmatch
          have hne : p.1 ≠ k + 1 := fun heq =>
            absurd (by simp [heq] : decide (p.1 = k + 1) = true) (by simpa using hmatch p hp)
          omega
      · simp only [hmatch]
        have hmem : hd ∈ free.filter (fun p => p.1 = k + 1) := by
          rw [List.head?_eq_some_iff] at hmatch
          obtain ⟨tl, htl⟩ := hmatch
          rw [htl]; exact List.mem_cons_self
        rw [List.mem_filter] at hmem
        obtain ⟨hmemf, heq⟩ := hmem
        simp only [decide_eq_true_eq] at heq
        refine ⟨fun p hp => ?_, fun hnone' => by simp at hnone'⟩
        cases hp
        exact ⟨hmemf, by omega, fun q _ hqk => by omega⟩

private theorem bestFreePair_mem {free : FreeSpace} {k : ℕ} {p : ℕ × ℕ}
    (h : bestFreePair free k = some p) : p ∈ free := ((bestFreePair_spec free k).1 p h).1

private theorem bestFreePair_le {free : FreeSpace} {k : ℕ} {p : ℕ × ℕ}
    (h : bestFreePair free k = some p) : p.1 ≤ k := ((bestFreePair_spec free k).1 p h).2.1

private theorem bestFreePair_max {free : FreeSpace} {k : ℕ} {p : ℕ × ℕ}
    (h : bestFreePair free k = some p)
    {q : ℕ × ℕ} (hq : q ∈ free) (hqk : q.1 ≤ k) : q.1 ≤ p.1 :=
  ((bestFreePair_spec free k).1 p h).2.2 q hq hqk

private theorem bestFreePair_none {free : FreeSpace} {k : ℕ} (h : bestFreePair free k = Option.none)
    {p : ℕ × ℕ} (hp : p ∈ free) : k < p.1 := (bestFreePair_spec free k).2 h p hp

private theorem primrecRel_fst_eq : PrimrecRel fun (p : ℕ × ℕ) (n : ℕ) => p.1 = n :=
  ⟨inferInstance, Primrec.eq.decide.comp (Primrec.fst.comp Primrec.fst) Primrec.snd⟩

private theorem primrec₂_filterLen : Primrec₂ fun (free : FreeSpace) (n : ℕ) =>
    (free.filter (fun p => p.1 = n)).head? :=
  Primrec.list_head?.comp₂ (PrimrecRel.listFilter primrecRel_fst_eq)

private theorem primrec₂_bestFreePair : Primrec₂ bestFreePair := by
  have hbase : Primrec fun free : FreeSpace => (free.filter (fun p => p.1 = 0)).head? :=
    primrec₂_filterLen.comp Primrec.id (Primrec.const 0)
  have hfiltSucc : Primrec₂ fun (free : FreeSpace) (n : ℕ) =>
      (free.filter (fun p => p.1 = n + 1)).head? :=
    primrec₂_filterLen.comp₂ Primrec₂.left (Primrec.succ.comp₂ Primrec₂.right)
  have hg : Primrec₂ fun (free : FreeSpace) (nr : ℕ × Option (ℕ × ℕ)) =>
      (match (free.filter (fun p => p.1 = nr.1 + 1)).head? with
        | some p => some p
        | Option.none => nr.2 : Option (ℕ × ℕ)) := by
    have hfilt2 : Primrec fun q : FreeSpace × ℕ × Option (ℕ × ℕ) =>
        (q.1.filter (fun p => p.1 = q.2.1 + 1)).head? :=
      hfiltSucc.comp Primrec.fst (Primrec.fst.comp Primrec.snd)
    have hnoneCase : Primrec fun q : FreeSpace × ℕ × Option (ℕ × ℕ) => q.2.2 :=
      Primrec.snd.comp Primrec.snd
    have hsomeCase : Primrec₂ fun (q : FreeSpace × ℕ × Option (ℕ × ℕ)) (p : ℕ × ℕ) =>
        (some p : Option (ℕ × ℕ)) :=
      Primrec.option_some.comp₂ Primrec₂.right
    have := Primrec.option_casesOn hfilt2 hnoneCase hsomeCase
    exact this.of_eq fun q => by
      cases hm : (q.1.filter (fun p => p.1 = q.2.1 + 1)).head? <;> simp [hm]
  have hres := Primrec.nat_rec hbase hg
  refine hres.of_eq fun free m => ?_
  induction m with
  | zero => rfl
  | succ m ih =>
      change
        (match (free.filter (fun p => p.1 = m + 1)).head? with
          | some p => some p
          | Option.none => (Nat.rec _ _ m : Option (ℕ × ℕ)))
          = bestFreePair free (m + 1)
      rw [ih]
      rfl

/-! ## `kcServe`: one online Kraft–Chaitin step -/

/-- The structural invariant on a free space: pairwise distinct lengths, each numerator within its
own width, and no two entries comparable. -/
def FreeInv (free : FreeSpace) : Prop :=
  (free.map Prod.fst).Nodup ∧ (∀ p ∈ free, p.2 < 2 ^ p.1) ∧
    (∀ p ∈ free, ∀ q ∈ free, p.1 ≠ q.1 → ¬ Comparable p.1 p.2 q.1 q.2)

private theorem freeInv_init : FreeInv [(0, 0)] := by
  refine ⟨by simp, by simp, ?_⟩
  simp only [List.mem_singleton]
  rintro p rfl q rfl h
  exact absurd rfl h

/-- Serve one request of length `k` against the free space, in `(length, numerator)` pair form. -/
def kcServe' (free : FreeSpace) (k : ℕ) : Option ((ℕ × ℕ) × FreeSpace) :=
  (bestFreePair free k).map (fun jp =>
    let free1 := free.filter (fun p => p.1 ≠ jp.1)
    let build := splitBuild jp.1 jp.2 (k - jp.1)
    ((k, build.1), build.2 ++ free1))

/-- Serve one request of length `k`: the assigned word and the updated free space. -/
def kcServe (free : FreeSpace) (k : ℕ) : Option (List Bool × FreeSpace) :=
  (kcServe' free k).map (fun q => (bitsFixed q.1.1 q.1.2, q.2))

private theorem primrecRel_fst_ne : PrimrecRel fun (p : ℕ × ℕ) (n : ℕ) => p.1 ≠ n :=
  ⟨inferInstance,
    (Primrec.not.comp
        (Primrec.eq.decide.comp (Primrec.fst.comp Primrec.fst) Primrec.snd)).of_eq fun q => by
      simp [Ne, decide_not]⟩

private theorem primrec₂_kcServe' : Primrec₂ kcServe' := by
  have hbuild : Primrec₂ fun (freek : FreeSpace × ℕ) (jp : ℕ × ℕ) =>
      splitBuild jp.1 jp.2 (freek.2 - jp.1) :=
    primrec₂_splitBuild.comp₂ Primrec₂.right
      (Primrec.nat_sub.comp₂ (Primrec.snd.comp₂ Primrec₂.left) (Primrec.fst.comp₂ Primrec₂.right))
  have hfree1 : Primrec₂ fun (freek : FreeSpace × ℕ) (jp : ℕ × ℕ) =>
      freek.1.filter (fun p => p.1 ≠ jp.1) :=
    (PrimrecRel.listFilter primrecRel_fst_ne).comp₂ (Primrec.fst.comp₂ Primrec₂.left)
      (Primrec.fst.comp₂ Primrec₂.right)
  have hg : Primrec₂ fun (freek : FreeSpace × ℕ) (jp : ℕ × ℕ) =>
      (((freek.2, (splitBuild jp.1 jp.2 (freek.2 - jp.1)).1),
        (splitBuild jp.1 jp.2 (freek.2 - jp.1)).2 ++ freek.1.filter (fun p => p.1 ≠ jp.1))
        : (ℕ × ℕ) × FreeSpace) := by
    have h1 : Primrec₂ fun (freek : FreeSpace × ℕ) (jp : ℕ × ℕ) => freek.2 :=
      Primrec.snd.comp₂ Primrec₂.left
    have h2 : Primrec₂ fun (freek : FreeSpace × ℕ) (jp : ℕ × ℕ) =>
        (splitBuild jp.1 jp.2 (freek.2 - jp.1)).1 := Primrec.fst.comp₂ hbuild
    have h3 : Primrec₂ fun (freek : FreeSpace × ℕ) (jp : ℕ × ℕ) =>
        (splitBuild jp.1 jp.2 (freek.2 - jp.1)).2 ++ freek.1.filter (fun p => p.1 ≠ jp.1) :=
      Primrec₂.comp₂ Primrec.list_append (Primrec.snd.comp₂ hbuild) hfree1
    exact Primrec.pair (Primrec.pair h1 h2) h3
  exact (Primrec.option_map primrec₂_bestFreePair hg).of_eq fun freek => by
    unfold kcServe'; rfl

theorem primrec₂_kcServe : Primrec₂ kcServe := by
  have hg : Primrec₂ fun (_ : FreeSpace × ℕ) (q : (ℕ × ℕ) × FreeSpace) =>
      ((bitsFixed q.1.1 q.1.2, q.2) : List Bool × FreeSpace) := by
    have hw : Primrec₂ fun (_ : FreeSpace × ℕ) (q : (ℕ × ℕ) × FreeSpace) =>
        bitsFixed q.1.1 q.1.2 :=
      primrec₂_bitsFixed.comp₂ (Primrec.fst.comp₂ (Primrec.fst.comp₂ Primrec₂.right))
        (Primrec.snd.comp₂ (Primrec.fst.comp₂ Primrec₂.right))
    exact Primrec.pair hw
      (Primrec.snd.comp Primrec.snd :
        Primrec fun p : (FreeSpace × ℕ) × (ℕ × ℕ) × FreeSpace => p.2.2)
  exact Primrec.option_map primrec₂_kcServe' hg

/-! ## `kcRun`: the run over a request stream -/

/-- One step of the run, in `(length, numerator)` pair form. -/
def kcStep' (state : FreeSpace × List (ℕ × ℕ)) (req : ℕ) : FreeSpace × List (ℕ × ℕ) :=
  match kcServe' state.1 req with
  | Option.none => state
  | some (p, free') => (free', state.2 ++ [p])

/-- The run over a request stream, by steps, in `(length, numerator)` pair form. -/
def kcRunPairs (req : ℕ → ℕ) : ℕ → FreeSpace × List (ℕ × ℕ)
  | 0 => ([(0, 0)], [])
  | m + 1 => kcStep' (kcRunPairs req m) (req m)

/-- One step of the run: the free space and the words assigned so far. -/
def kcStep (state : FreeSpace × List (List Bool)) (req : ℕ) : FreeSpace × List (List Bool) :=
  match kcServe state.1 req with
  | Option.none => state
  | some (w, free') => (free', state.2 ++ [w])

/-- The run over a request stream, by steps: the free space and the words assigned so far. -/
def kcRun (req : ℕ → ℕ) : ℕ → FreeSpace × List (List Bool)
  | 0 => ([(0, 0)], [])
  | m + 1 => kcStep (kcRun req m) (req m)

/-- The word assigned at step `m`. -/
def kcWord (req : ℕ → ℕ) (m : ℕ) : Option (List Bool) :=
  (kcServe (kcRun req m).1 (req m)).map Prod.fst

private theorem kcRun_eq_kcRunPairs (req : ℕ → ℕ) : ∀ m,
    kcRun req m = ((kcRunPairs req m).1, (kcRunPairs req m).2.map (fun p => bitsFixed p.1 p.2))
  | 0 => rfl
  | m + 1 => by
      have ih := kcRun_eq_kcRunPairs req m
      have hgoal : kcRun req (m + 1) = kcStep (kcRun req m) (req m) := rfl
      have hgoal2 : kcRunPairs req (m + 1) = kcStep' (kcRunPairs req m) (req m) := rfl
      rw [hgoal, ih, hgoal2]
      unfold kcStep kcStep' kcServe
      cases kcServe' (kcRunPairs req m).1 (req m) with
      | none => rfl
      | some q => simp [List.map_append]

theorem computable_kcRun {req : ℕ → ℕ} (h : Computable req) : Computable (kcRun req) := by
  have hh : Computable₂ fun (_ : ℕ) (nstate : ℕ × (FreeSpace × List (List Bool))) =>
      kcStep nstate.2 (req nstate.1) := by
    have hreq : Computable fun nstate : ℕ × (FreeSpace × List (List Bool)) => req nstate.1 :=
      h.comp Primrec.fst.to_comp
    have hserve := primrec₂_kcServe.to_comp.comp
      (Primrec.fst.comp Primrec.snd).to_comp hreq
    have hnone : Computable fun nstate : ℕ × (FreeSpace × List (List Bool)) => nstate.2 :=
      Primrec.snd.to_comp
    have hsome : Computable₂ fun (nstate : ℕ × (FreeSpace × List (List Bool)))
        (wf : List Bool × FreeSpace) => (wf.2, nstate.2.2 ++ [wf.1]) := by
      have h1 : Computable fun p : (ℕ × (FreeSpace × List (List Bool))) × (List Bool × FreeSpace) =>
          p.2.2 := (Primrec.snd.comp Primrec.snd).to_comp
      have h2 : Computable fun p : (ℕ × (FreeSpace × List (List Bool))) × (List Bool × FreeSpace) =>
          p.1.2.2 ++ [p.2.1] :=
        (Primrec.list_append.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
          (Primrec.list_cons.comp (Primrec.fst.comp Primrec.snd)
            (Primrec.const ([] : List (List Bool))))).to_comp
      exact (Computable.pair h1 h2).of_eq fun p => rfl
    have hcore := Computable.option_casesOn hserve hnone hsome
    exact (hcore.comp Primrec.snd.to_comp).of_eq fun p => by
      change
        Option.casesOn (kcServe p.2.2.1 (req p.2.1)) p.2.2 (fun wf => (wf.2, p.2.2.2 ++ [wf.1]))
          = kcStep p.2.2 (req p.2.1)
      unfold kcStep
      cases kcServe p.2.2.1 (req p.2.1) <;> rfl
  have hres := Computable.nat_rec (f := fun m : ℕ => m) Computable.id
    (g := fun _ : ℕ => (([(0, 0)], []) : FreeSpace × List (List Bool))) (Computable.const _) hh
  refine hres.of_eq fun m => ?_
  induction m with
  | zero => rfl
  | succ m ih =>
      change kcStep (Nat.rec _ _ m) (req m) = kcRun req (m + 1)
      rw [ih]
      rfl

theorem computable_kcWord {req : ℕ → ℕ} (h : Computable req) : Computable (kcWord req) := by
  have hrun := computable_kcRun h
  have hreq : Computable fun m : ℕ => req m := h
  have hserve := primrec₂_kcServe.to_comp.comp
    (Primrec.fst.to_comp.comp hrun) hreq
  exact Computable.option_map hserve (Primrec.fst.to_comp.comp₂ Primrec₂.right.to_comp)

/-- **The single-step invariant.** -/
theorem kcServe'_inv {free : FreeSpace} (hinv : FreeInv free) {k : ℕ} {a : ℕ} {free' : FreeSpace}
    (h : kcServe' free k = some ((k, a), free')) :
    FreeInv free' ∧ a < 2 ^ k ∧ (∀ q ∈ free', ¬ Comparable k a q.1 q.2) ∧
      ∃ jp ∈ free, Nested jp.1 jp.2 k a ∧ ∀ q ∈ free', q ∈ free ∨ Nested jp.1 jp.2 q.1 q.2 := by
  obtain ⟨hnodup, hbound, hpair⟩ := hinv
  unfold kcServe' at h
  rcases hbest : bestFreePair free k with _ | jp
  · simp [hbest] at h
  · simp only [hbest, Option.map_some] at h
    set j := jp.1 with hjdef
    set a0 := jp.2 with ha0def
    set m := k - j with hmdef
    set free1 := free.filter (fun p => p.1 ≠ j) with hfree1def
    set build := splitBuild j a0 m with hbuilddef
    have heq : ((k, build.1), build.2 ++ free1) = ((k, a), free') := Option.some.inj h
    simp only [Prod.mk.injEq] at heq
    obtain ⟨⟨-, haeq⟩, hfree'eq⟩ := heq
    have hjk : j ≤ k := bestFreePair_le hbest
    have hjmem : jp ∈ free := bestFreePair_mem hbest
    have hjbound : a0 < 2 ^ j := hbound jp hjmem
    have hfst : build.1 = 2 ^ m * a0 := splitBuild_fst j a0 m
    have hjm : j + m = k := by rw [hmdef]; omega
    have hNestedFinal : Nested j a0 k build.1 := by
      refine ⟨hjk, ?_⟩
      rw [hfst, hmdef, mul_comm]
      exact Nat.mul_div_cancel a0 (Nat.two_pow_pos (k - j))
    obtain ⟨hbmem, hbfinal, hbpair, hbnodup⟩ := splitBuild_inv j a0 m
    rw [hjm] at hbmem hbfinal
    rw [← hfst] at hbfinal
    -- the old free space, minus `jp`, keeps `FreeInv`
    have hfree1sub : ∀ p ∈ free1, p ∈ free := fun p hp => (List.mem_filter.mp hp).1
    have hfree1ne : ∀ p ∈ free1, p.1 ≠ j := fun p hp => by
      simpa using (List.mem_filter.mp hp).2
    refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, jp, hjmem, ?_, ?_⟩
    · -- nodup of free'
      rw [← hfree'eq, List.map_append, List.nodup_append]
      refine ⟨hbnodup, ?_, ?_⟩
      · exact hnodup.sublist (List.Sublist.map _ List.filter_sublist)
      · intro l hl l' hl'
        simp only [List.mem_map] at hl hl'
        obtain ⟨p, hp, rfl⟩ := hl
        obtain ⟨q, hq, rfl⟩ := hl'
        intro hcontra
        obtain ⟨hjlt, hjle, -⟩ := hbmem p hp
        have hqfree : q ∈ free := hfree1sub q hq
        have hqk : q.1 ≤ k := by omega
        have hqj := bestFreePair_max hbest hqfree hqk
        omega
    · -- bound
      intro p hp
      rw [← hfree'eq] at hp
      rcases List.mem_append.mp hp with hp | hp
      · exact splitBuild_snd_bound hjbound m p hp
      · exact hbound p (hfree1sub p hp)
    · -- pairwise
      intro p hp q hq hne
      rw [← hfree'eq] at hp hq
      rcases List.mem_append.mp hp with hp | hp <;> rcases List.mem_append.mp hq with hq | hq
      · exact hbpair p hp q hq hne
      · have hpnest : Nested j a0 p.1 p.2 := (hbmem p hp).2.2
        have hqnc : ¬ Comparable j a0 q.1 q.2 :=
          hpair jp hjmem q (hfree1sub q hq) (Ne.symm (hfree1ne q hq))
        exact not_comparable_of_nested hpnest hqnc
      · have hqnest : Nested j a0 q.1 q.2 := (hbmem q hq).2.2
        have hpnc : ¬ Comparable j a0 p.1 p.2 :=
          hpair jp hjmem p (hfree1sub p hp) (Ne.symm (hfree1ne p hp))
        exact fun hc => (not_comparable_of_nested hqnest hpnc) hc.symm
      · exact hpair p (hfree1sub p hp) q (hfree1sub q hq) hne
    · -- bound on the assigned value
      rw [← haeq, ← hjm]
      exact splitBuild_fst_bound hjbound m
    · -- assigned incomparable with everything remaining
      intro q hq
      rw [← hfree'eq] at hq
      rw [← haeq]
      rcases List.mem_append.mp hq with hq | hq
      · exact hbfinal q hq
      · exact not_comparable_of_nested hNestedFinal
          (hpair jp hjmem q (hfree1sub q hq) (Ne.symm (hfree1ne q hq)))
    · -- the served piece is nested inside `jp`
      rw [← haeq]; exact hNestedFinal
    · -- every remaining free piece is either untouched or nested inside `jp`
      intro q hq
      rw [← hfree'eq] at hq
      rcases List.mem_append.mp hq with hq | hq
      · exact Or.inr (hbmem q hq).2.2
      · exact Or.inl (hfree1sub q hq)

/-! ## `kcMass`: the free measure -/

/-- The free measure: the total mass of the free dyadic intervals. -/
noncomputable def kcMass (free : FreeSpace) : ℝ := (free.map (fun p => (1 / 2 : ℝ) ^ p.1)).sum

private theorem kcMass_filter_add_filter_ne (free : FreeSpace) (j : ℕ) :
    kcMass (free.filter (fun p => p.1 = j)) + kcMass (free.filter (fun p => p.1 ≠ j))
      = kcMass free := by
  unfold kcMass
  have hperm := (List.filter_append_perm (fun p : ℕ × ℕ => decide (p.1 = j)) free).map
    (fun p : ℕ × ℕ => (1 / 2 : ℝ) ^ p.1)
  have hsum := hperm.sum_eq
  rw [List.map_append, List.sum_append] at hsum
  simpa using hsum

/-- Under `FreeInv`'s nodup clause, at most (hence, via a witness, exactly) one free piece has a
given length. -/
private theorem freeInv_filter_len_singleton {free : FreeSpace} (hnodup : (free.map Prod.fst).Nodup)
    {jp : ℕ × ℕ} (hjmem : jp ∈ free) :
    (free.filter (fun p => p.1 = jp.1)).length = 1 := by
  have hlen_le1 : (free.filter (fun p => p.1 = jp.1)).length ≤ 1 := by
    rcases hL : free.filter (fun p => p.1 = jp.1) with _ | ⟨x, _ | ⟨y, rest⟩⟩
    · rw [hL]; simp
    · rw [hL]; simp
    · exfalso
      have hnodupF : ((x :: y :: rest).map Prod.fst).Nodup := by
        rw [← hL]; exact hnodup.sublist (List.Sublist.map _ List.filter_sublist)
      have hxj : x.1 = jp.1 := by
        have hx : x ∈ free.filter (fun p => p.1 = jp.1) := by rw [hL]; exact List.mem_cons_self
        simpa using (List.mem_filter.mp hx).2
      have hyj : y.1 = jp.1 := by
        have hy : y ∈ free.filter (fun p => p.1 = jp.1) := by
          rw [hL]; exact List.mem_cons_of_mem _ List.mem_cons_self
        simpa using (List.mem_filter.mp hy).2
      simp only [List.map_cons, List.nodup_cons] at hnodupF
      exact hnodupF.1 (List.mem_cons.mpr (Or.inl (by rw [hxj, hyj])))
  have hmemF : jp ∈ free.filter (fun p => p.1 = jp.1) := List.mem_filter.mpr ⟨hjmem, by simp⟩
  have hlen_ge1 : 1 ≤ (free.filter (fun p => p.1 = jp.1)).length := List.length_pos_of_mem hmemF
  omega

private theorem kcMass_filter_eq {free : FreeSpace} (hnodup : (free.map Prod.fst).Nodup)
    {jp : ℕ × ℕ} (hjmem : jp ∈ free) :
    kcMass (free.filter (fun p => p.1 = jp.1)) = (1 / 2 : ℝ) ^ jp.1 := by
  have hlen1 := freeInv_filter_len_singleton hnodup hjmem
  unfold kcMass
  rcases hL : free.filter (fun p => p.1 = jp.1) with _ | ⟨q, rest⟩
  · rw [hL] at hlen1; simp at hlen1
  · rw [hL] at hlen1
    have hrest : rest = [] := by
      simp only [List.length_cons] at hlen1
      exact List.eq_nil_of_length_eq_zero (by omega)
    subst hrest
    have hq1 : q.1 = jp.1 := by
      have hqmem : q ∈ free.filter (fun p => p.1 = jp.1) := by rw [hL]; exact List.mem_cons_self
      simpa using (List.mem_filter.mp hqmem).2
    rw [hL]
    simp [hq1]

/-- **A split conserves mass**: the freed pieces plus the continuing piece total the split
piece's own mass. -/
private theorem splitBuild_mass (j a : ℕ) : ∀ m,
    kcMass (splitBuild j a m).2 + (1 / 2 : ℝ) ^ (j + m) = (1 / 2 : ℝ) ^ j
  | 0 => by simp [splitBuild, kcMass]
  | m + 1 => by
      have ih := splitBuild_mass j a m
      have hexp : (1 / 2 : ℝ) ^ (j + m + 1) = (1 / 2 : ℝ) ^ (j + m) * (1 / 2) := pow_succ _ _
      rw [show j + (m + 1) = j + m + 1 from by omega, splitBuild_snd_succ]
      unfold kcMass at ih ⊢
      simp only [List.map_cons, List.sum_cons]
      linarith [ih, hexp]

/-- **The single-step mass identity**: serving a request spends exactly `2 ^ (-k)` of the free
measure. -/
theorem kcServe'_mass {free : FreeSpace} (hnodup : (free.map Prod.fst).Nodup) {k a : ℕ}
    {free' : FreeSpace} (h : kcServe' free k = some ((k, a), free')) :
    kcMass free = (1 / 2 : ℝ) ^ k + kcMass free' := by
  unfold kcServe' at h
  rcases hbest : bestFreePair free k with _ | jp
  · simp [hbest] at h
  · simp only [hbest, Option.map_some] at h
    set j := jp.1 with hjdef
    set a0 := jp.2 with ha0def
    set m := k - j with hmdef
    set free1 := free.filter (fun p => p.1 ≠ j) with hfree1def
    set build := splitBuild j a0 m with hbuilddef
    have heq : ((k, build.1), build.2 ++ free1) = ((k, a), free') := Option.some.inj h
    simp only [Prod.mk.injEq] at heq
    obtain ⟨-, hfree'eq⟩ := heq
    have hjmem : jp ∈ free := bestFreePair_mem hbest
    have hjk : j ≤ k := bestFreePair_le hbest
    have hjm : j + m = k := by rw [hmdef]; omega
    have hmassJ : kcMass (free.filter (fun p => p.1 = j)) = (1 / 2 : ℝ) ^ j :=
      kcMass_filter_eq hnodup hjmem
    have hpart : kcMass (free.filter (fun p => p.1 = j)) + kcMass free1 = kcMass free :=
      kcMass_filter_add_filter_ne free j
    have hmassBuild : kcMass build.2 + (1 / 2 : ℝ) ^ k = (1 / 2 : ℝ) ^ j := by
      rw [← hjm]; exact splitBuild_mass j a0 m
    rw [← hfree'eq]
    unfold kcMass
    rw [List.map_append, List.sum_append]
    unfold kcMass at hmassJ hpart hmassBuild
    linarith [hmassJ, hpart, hmassBuild]

/-! ## Distinct lengths above `k` carry mass below `2 ^ (-k)` -/

private theorem mem_le_foldr_max (L : List ℕ) : ∀ l ∈ L, l ≤ L.foldr max 0 := by
  induction L with
  | nil => simp
  | cons a l ih =>
      intro x hx
      rw [List.foldr_cons]
      rcases List.mem_cons.mp hx with rfl | hx
      · exact le_max_left _ _
      · exact le_trans (ih x hx) (le_max_right _ _)

private theorem foldr_max_le_of_forall_le (L : List ℕ) (M : ℕ) (h : ∀ l ∈ L, l ≤ M) :
    L.foldr max 0 ≤ M := by
  induction L with
  | nil => simp
  | cons a l ih =>
      rw [List.foldr_cons]
      exact max_le (h a List.mem_cons_self) (ih (fun x hx => h x (List.mem_cons_of_mem _ hx)))

theorem two_pow_neg_succ_double (n : ℕ) : (1 / 2 : ℝ) ^ n = 2 * (1 / 2 : ℝ) ^ (n + 1) := by
  rw [pow_succ]; ring

theorem two_pow_neg_antitone {m n : ℕ} (h : m ≤ n) : (1 / 2 : ℝ) ^ n ≤ (1 / 2 : ℝ) ^ m :=
  pow_le_pow_of_le_one (by norm_num) (by norm_num) h

/-- **A finite nodup list of naturals, all above `k`, carries mass strictly below `2 ^ (-k)`.** -/
private theorem sum_two_pow_neg_bound : ∀ (d : ℕ) (L : List ℕ) (k : ℕ), L.foldr max 0 ≤ k + d →
    L.Nodup → (∀ l ∈ L, k < l) →
    (L.map (fun l => (1 / 2 : ℝ) ^ l)).sum ≤ (1 / 2 : ℝ) ^ k - (1 / 2 : ℝ) ^ (k + L.length) := by
  intro d
  induction d with
  | zero =>
      intro L k hbound hnd hgt
      have hLnil : L = [] := by
        rcases L with _ | ⟨l0, rest⟩
        · rfl
        · exfalso
          have h1 := hgt l0 List.mem_cons_self
          have h2 := mem_le_foldr_max (l0 :: rest) l0 List.mem_cons_self
          omega
      subst hLnil
      simp
  | succ d ih =>
      intro L k hbound hnd hgt
      rcases L with _ | ⟨l0, rest⟩
      · simp
      · by_cases hmem : (k + 1) ∈ (l0 :: rest)
        · have hperm := List.perm_cons_erase hmem
          have hnd' : ((k + 1) :: (l0 :: rest).erase (k + 1)).Nodup := hperm.nodup_iff.mp hnd
          have hnotmem : (k + 1) ∉ (l0 :: rest).erase (k + 1) := (List.nodup_cons.mp hnd').1
          have hgt' : ∀ l ∈ (l0 :: rest).erase (k + 1), k + 1 < l := by
            intro l hl
            have hlL : l ∈ (l0 :: rest) := List.mem_of_mem_erase hl
            have hne : l ≠ k + 1 := fun he => hnotmem (he ▸ hl)
            have := hgt l hlL
            omega
          have hboundE : ((l0 :: rest).erase (k + 1)).foldr max 0 ≤ (k + 1) + d := by
            apply foldr_max_le_of_forall_le
            intro l hl
            have hlL : l ∈ (l0 :: rest) := List.mem_of_mem_erase hl
            have := mem_le_foldr_max (l0 :: rest) l hlL
            omega
          have hndE : ((l0 :: rest).erase (k + 1)).Nodup := hnd.erase _
          have hlen : (l0 :: rest).length = ((l0 :: rest).erase (k + 1)).length + 1 := by
            have hpl := hperm.length_eq
            simpa using hpl
          have hsum : ((l0 :: rest).map (fun l => (1 / 2 : ℝ) ^ l)).sum
              = (1 / 2 : ℝ) ^ (k + 1)
                + (((l0 :: rest).erase (k + 1)).map (fun l => (1 / 2 : ℝ) ^ l)).sum := by
            have hps := (hperm.map (fun l => (1 / 2 : ℝ) ^ l)).sum_eq
            simpa using hps
          have hIH := ih ((l0 :: rest).erase (k + 1)) (k + 1) hboundE hndE hgt'
          rw [hsum, hlen]
          have hexp : (1 / 2 : ℝ) ^ (k + (((l0 :: rest).erase (k + 1)).length + 1))
              = (1 / 2 : ℝ) ^ ((k + 1) + ((l0 :: rest).erase (k + 1)).length) := by
            congr 1; omega
          rw [hexp]
          have hdbl := two_pow_neg_succ_double k
          linarith [hIH, hdbl]
        · have hbound' : (l0 :: rest).foldr max 0 ≤ (k + 1) + d := by omega
          have hgt' : ∀ l ∈ (l0 :: rest), k + 1 < l := by
            intro l hl
            have hne : l ≠ k + 1 := fun he => hmem (he ▸ hl)
            have := hgt l hl
            omega
          have hIH := ih (l0 :: rest) (k + 1) hbound' hnd hgt'
          have hdbl1 := two_pow_neg_succ_double k
          have hdbl2 := two_pow_neg_succ_double (k + (l0 :: rest).length)
          have hexp : k + (l0 :: rest).length + 1 = (k + 1) + (l0 :: rest).length := by omega
          rw [hexp] at hdbl2
          have hnn := two_pow_neg_antitone
            (show k + 1 ≤ (k + 1) + (l0 :: rest).length from by omega)
          linarith [hIH, hdbl1, hdbl2, hnn]

/-- **Under `FreeInv`, a request that fails leaves the whole free measure below `2 ^ (-k)`.** -/
theorem kcMass_lt_of_bestFreePair_none {free : FreeSpace} (hnd : (free.map Prod.fst).Nodup)
    {k : ℕ} (hnone : bestFreePair free k = Option.none) : kcMass free < (1 / 2 : ℝ) ^ k := by
  have hgt : ∀ l ∈ free.map Prod.fst, k < l := by
    intro l hl
    simp only [List.mem_map] at hl
    obtain ⟨p, hp, rfl⟩ := hl
    exact bestFreePair_none hnone hp
  have hbound : (free.map Prod.fst).foldr max 0 ≤ k + (free.map Prod.fst).foldr max 0 := by omega
  have hb := sum_two_pow_neg_bound ((free.map Prod.fst).foldr max 0) (free.map Prod.fst) k
    hbound hnd hgt
  have heq : (free.map Prod.fst).map (fun l => (1 / 2 : ℝ) ^ l)
      = free.map (fun p => (1 / 2 : ℝ) ^ p.1) := by
    rw [List.map_map]; rfl
  rw [heq] at hb
  have hlt : (0:ℝ) < (1 / 2 : ℝ) ^ (k + (free.map Prod.fst).length) := by positivity
  unfold kcMass
  linarith [hb, hlt]

/-! ## `RunInv`: the run-level invariant, over the whole request history -/

/-- Every past assignment stays incomparable with the current free space and with every other
past assignment. -/
def RunInv (free : FreeSpace) (assigned : List (ℕ × ℕ)) : Prop :=
  FreeInv free ∧
    (∀ p ∈ assigned, p.2 < 2 ^ p.1) ∧
    (∀ p ∈ assigned, ∀ q ∈ free, ¬ Comparable p.1 p.2 q.1 q.2) ∧
    (∀ p ∈ assigned, ∀ q ∈ assigned, p ≠ q → ¬ Comparable p.1 p.2 q.1 q.2)

private theorem runInv_init : RunInv [(0, 0)] [] :=
  ⟨freeInv_init, by simp, by simp, by simp⟩

private theorem runInv_step {free : FreeSpace} {assigned : List (ℕ × ℕ)}
    (hinv : RunInv free assigned)
    {k a : ℕ} {free' : FreeSpace} (h : kcServe' free k = some ((k, a), free')) :
    RunInv free' (assigned ++ [(k, a)]) := by
  obtain ⟨hfree, hbound, hafree, hapair⟩ := hinv
  obtain ⟨hfree', haK, hafinal, jp, hjpmem, hjpnest, hdichot⟩ := kcServe'_inv hfree h
  have hjp_vs_p : ∀ p ∈ assigned, ¬ Comparable jp.1 jp.2 p.1 p.2 := fun p hp hc =>
    hafree p hp jp hjpmem hc.symm
  refine ⟨hfree', ?_, ?_, ?_⟩
  · intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · exact hbound p hp
    · simp only [List.mem_singleton] at hp; subst hp; exact haK
  · intro p hp q hq
    rcases List.mem_append.mp hp with hp | hp
    · rcases hdichot q hq with hqfree | hqnest
      · exact hafree p hp q hqfree
      · exact fun hc => (not_comparable_of_nested hqnest (hjp_vs_p p hp)) hc.symm
    · simp only [List.mem_singleton] at hp
      subst hp
      exact hafinal q hq
  · intro p hp q hq hne
    rcases List.mem_append.mp hp with hp | hp <;> rcases List.mem_append.mp hq with hq | hq
    · exact hapair p hp q hq hne
    · simp only [List.mem_singleton] at hq
      subst hq
      exact fun hc => (not_comparable_of_nested hjpnest (hjp_vs_p p hp)) hc.symm
    · simp only [List.mem_singleton] at hp
      subst hp
      exact not_comparable_of_nested hjpnest (hjp_vs_p q hq)
    · simp only [List.mem_singleton] at hp hq
      exact absurd (hp.trans hq.symm) hne

/-! ## The run-level induction -/

/-- The pair assigned at step `i`, in `(length, numerator)` form. -/
def kcWordPair (req : ℕ → ℕ) (i : ℕ) : Option (ℕ × ℕ) :=
  (kcServe' (kcRunPairs req i).1 (req i)).map Prod.fst

theorem kcWord_eq_kcWordPair (req : ℕ → ℕ) (i : ℕ) :
    kcWord req i = (kcWordPair req i).map (fun p => bitsFixed p.1 p.2) := by
  unfold kcWord kcWordPair
  rw [kcRun_eq_kcRunPairs]
  unfold kcServe
  cases kcServe' (kcRunPairs req i).1 (req i) with
  | none => rfl
  | some q => rfl

private theorem kcServe'_none_iff (free : FreeSpace) (k : ℕ) :
    kcServe' free k = Option.none ↔ bestFreePair free k = Option.none := by
  unfold kcServe'
  cases bestFreePair free k <;> simp

theorem kcServe'_fst_eq (free : FreeSpace) (k : ℕ) {p : ℕ × ℕ} {free' : FreeSpace}
    (h : kcServe' free k = some (p, free')) : p.1 = k := by
  unfold kcServe' at h
  rcases hbest : bestFreePair free k with _ | jp
  · simp [hbest] at h
  · simp only [hbest, Option.map_some, Option.some.injEq] at h
    exact (congrArg Prod.fst (congrArg Prod.fst h)).symm

private theorem kcMass_init : kcMass [(0, 0)] = 1 := by simp [kcMass]

theorem kcRunPairs_inv {req : ℕ → ℕ}
    (hmass : ∀ N, ∑ i ∈ Finset.range N, (1 / 2 : ℝ) ^ req i ≤ 1) : ∀ m,
    RunInv (kcRunPairs req m).1 (kcRunPairs req m).2 ∧
      kcMass (kcRunPairs req m).1 + ∑ i ∈ Finset.range m, (1 / 2 : ℝ) ^ req i = 1 ∧
      ∀ i < m, ∃ p, kcWordPair req i = some p ∧ p.1 = req i
  | 0 => ⟨runInv_init, by simp [kcRunPairs, kcMass_init], by omega⟩
  | m + 1 => by
      obtain ⟨hrun, hmasseq, hwit⟩ := kcRunPairs_inv hmass m
      have hnodup : ((kcRunPairs req m).1.map Prod.fst).Nodup := hrun.1.1
      have hkey : (1 / 2 : ℝ) ^ req m ≤ kcMass (kcRunPairs req m).1 := by
        have h1 := hmass (m + 1)
        rw [Finset.sum_range_succ] at h1
        linarith [hmasseq]
      have hsucc : kcServe' (kcRunPairs req m).1 (req m) ≠ Option.none := by
        intro hnone
        have hbnone : bestFreePair (kcRunPairs req m).1 (req m) = Option.none :=
          (kcServe'_none_iff _ _).mp hnone
        have := kcMass_lt_of_bestFreePair_none hnodup hbnone
        linarith
      obtain ⟨⟨⟨k0, a⟩, free'⟩, hserve⟩ := Option.ne_none_iff_exists'.mp hsucc
      have hk0 : k0 = req m := kcServe'_fst_eq _ _ hserve
      subst hk0
      have hstep : kcRunPairs req (m + 1) = (free', (kcRunPairs req m).2 ++ [(req m, a)]) := by
        have heq : kcRunPairs req (m + 1) = kcStep' (kcRunPairs req m) (req m) := rfl
        rw [heq]
        unfold kcStep'
        rw [hserve]
      have hrun' : RunInv free' ((kcRunPairs req m).2 ++ [(req m, a)]) := runInv_step hrun hserve
      have hmassstep : kcMass (kcRunPairs req m).1 = (1 / 2 : ℝ) ^ req m + kcMass free' :=
        kcServe'_mass hnodup hserve
      have hwordpair : kcWordPair req m = some (req m, a) := by
        unfold kcWordPair
        rw [hserve]; rfl
      refine ⟨?_, ?_, ?_⟩
      · rw [hstep]; exact hrun'
      · rw [hstep]
        rw [Finset.sum_range_succ]
        linarith [hmasseq, hmassstep]
      · intro i hi
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | hi
        · exact hwit i hi
        · rw [hi]; exact ⟨(req m, a), hwordpair, rfl⟩

/-- **Once assigned, a pair stays in the run's assigned list forever after.** -/
theorem kcWordPair_mem_kcRunPairs {req : ℕ → ℕ} {i : ℕ} {p : ℕ × ℕ}
    (hp : kcWordPair req i = some p) : ∀ n, i < n → p ∈ (kcRunPairs req n).2 := by
  intro n hn
  induction n with
  | zero => omega
  | succ n ih =>
      rcases Nat.lt_succ_iff_lt_or_eq.mp hn with hn | hn
      · have hmem := ih hn
        change p ∈ (kcStep' (kcRunPairs req n) (req n)).2
        unfold kcStep'
        cases kcServe' (kcRunPairs req n).1 (req n) with
        | none => exact hmem
        | some q => exact List.mem_append_left _ hmem
      · subst hn
        unfold kcWordPair at hp
        obtain ⟨q, hserve, hq⟩ := Option.map_eq_some_iff.mp hp
        change p ∈ (kcStep' (kcRunPairs req i) (req i)).2
        unfold kcStep'
        rw [hserve]
        exact List.mem_append_right _ (by simp [← hq])

/-- **`kcRun`'s invariant**: at every step of a request stream whose partial sums stay at most
one, the free lengths stay pairwise distinct, every request so far was served at its own
requested length, the assigned words are pairwise prefix-free, and the assigned mass plus the
free measure is one. -/
theorem kcRun_invariant {req : ℕ → ℕ}
    (hmass : ∀ N, ∑ m ∈ Finset.range N, (1 / 2 : ℝ) ^ req m ≤ 1) (m : ℕ) :
    ((kcRun req m).1.map Prod.fst).Nodup ∧
      (∀ i < m, ∃ w, kcWord req i = some w ∧ w.length = req i) ∧
      PrefixFree {w | ∃ i < m, kcWord req i = some w} ∧
      kcMass (kcRun req m).1 + ∑ i ∈ Finset.range m, (1 / 2 : ℝ) ^ req i = 1 := by
  obtain ⟨hrun, hmasseq, hwit⟩ := kcRunPairs_inv hmass m
  have hR := kcRun_eq_kcRunPairs req m
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hR]; exact hrun.1.1
  · intro i hi
    obtain ⟨p, hp, hpk⟩ := hwit i hi
    refine ⟨bitsFixed p.1 p.2, ?_, ?_⟩
    · rw [kcWord_eq_kcWordPair, hp]; rfl
    · rw [length_bitsFixed, hpk]
  · rintro w ⟨i, hi, hwi⟩ w' ⟨i', hi', hwi'⟩ hpre
    rw [kcWord_eq_kcWordPair] at hwi hwi'
    obtain ⟨p, hp, hpwi⟩ := Option.map_eq_some_iff.mp hwi
    obtain ⟨p', hp', hpwi'⟩ := Option.map_eq_some_iff.mp hwi'
    have hmemP : p ∈ (kcRunPairs req (m + 1)).2 := kcWordPair_mem_kcRunPairs hp (m + 1) (by omega)
    have hmemP' : p' ∈ (kcRunPairs req (m + 1)).2 :=
      kcWordPair_mem_kcRunPairs hp' (m + 1) (by omega)
    have hrun' := (kcRunPairs_inv hmass (m + 1)).1
    by_cases hpp' : p = p'
    · rw [← hpwi, ← hpwi', hpp']
    · exfalso
      have hb1 : p.2 < 2 ^ p.1 := hrun'.2.1 p hmemP
      have hb2 : p'.2 < 2 ^ p'.1 := hrun'.2.1 p' hmemP'
      have hpre' : bitsFixed p.1 p.2 <+: bitsFixed p'.1 p'.2 := by rw [hpwi, hpwi']; exact hpre
      have hnested : Nested p.1 p.2 p'.1 p'.2 := (bitsFixed_prefix_iff hb1 hb2).mp hpre'
      exact hrun'.2.2.2 p hmemP p' hmemP' hpp' (Or.inl hnested)
  · rw [hR]; exact hmasseq

/-- **The assigned words, over the whole stream, are pairwise prefix-free.** -/
theorem kcWord_prefixFree {req : ℕ → ℕ}
    (hmass : ∀ N, ∑ m ∈ Finset.range N, (1 / 2 : ℝ) ^ req m ≤ 1) :
    PrefixFree {w | ∃ i, kcWord req i = some w} := by
  rintro w ⟨i, hwi⟩ w' ⟨i', hwi'⟩ hpre
  exact (kcRun_invariant hmass (max i i' + 1)).2.2.1
    w ⟨i, by omega, hwi⟩ w' ⟨i', by omega, hwi'⟩ hpre

end PrefixMachine
