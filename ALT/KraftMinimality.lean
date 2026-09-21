/-
Copyright (c) 2026 Mykola Palamarchuk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mykola Palamarchuk
-/
module

public import ALT.CodingTheorem
public import ALT.KolmogorovTimeBounded
public import ALT.KolmogorovBitlen
public import Mathlib.Analysis.PSeries

-- Formal-check file, not Mathlib-destined: opt out of the house-style header linter.
set_option linter.style.header false

/-!
# Prefix-complexity minimality, and the plain bit-length's additive form ([Discovery] §1.1, FV-25)

Provenance: [Discovery] §1.1, rows FV-25 (the coding theorem this instantiates), FV-28 (the bound
the witness below re-derives) and FV-29/FV-33 (the two additive forms between `KB` and `K_bitlen`,
both open in either direction).

## What this establishes

* `UpperSemicomputable`: the integer-valued mirror of `LowerSemicomputable` — a computable stage
  sequence, non-increasing, everywhere at least the function, attaining it at some stage.
* `lowerSemicomputable_two_pow_neg_of_upperSemicomputable`: an upper-semicomputable `f` gives a
  lower-semicomputable Kraft weight `2⁻⁽ᶠ⁺ᵏ⁾`.
* `KB_le_add_of_upperSemicomputable_summable`, its `_nonvacuous` witness,
  `summable_of_KB_le_add` and `KB_le_add_iff_summable`: **prefix complexity is, up to an additive
  constant, the least upper-semicomputable function with a summable Kraft weight** — the
  minimality reading of Levin's coding theorem (FV-25).
* `upperSemicomputable_K_bitlen`: the plain bit-length `K_bitlen` is upper-semicomputable, by a
  staged least-index search with the constant code as sentinel.
* `KB_le_K_bitlen_add_iff_summable`: the first additive form between `KB` and `K_bitlen`
  (FV-29's residue) is exactly the summability of `∑ 2⁻ᴷᵇⁱᵗˡᵉⁿ` — **not decided here in either
  direction**.
* `KB_le_two_mul_size'`: a second proof of FV-28's Elias bound `KB n ≤ 2 · size n + c`, through the
  coding theorem in place of the Elias decoder — no comparison of the two constants is claimed.

## What this does NOT establish (flagged)

Whether `∑ x, 2⁻ᴷᵇⁱᵗˡᵉⁿ⁽ˣ⁾` converges, in either direction, is untouched; so is the second additive
form `K_bitlen ≤ KB + c` (FV-33's own residue). Nothing here compares `KB_le_two_mul_size'`'s
constant against FV-28's `PrefixEliasKB.KB_le_two_mul_size`.
-/


@[expose] public section

namespace PrefixMachine

open Nat.Partrec Nat.Partrec.Code AdditiveComplexity CodeEvalLaws KolmogorovComplexity

/-! ## `UpperSemicomputable`: the integer-valued mirror of `LowerSemicomputable` -/

/-- Upper semicomputability of an integer-valued function: a computable stage sequence,
non-increasing in the stage, everywhere at least the function, and attaining it at some stage. -/
def UpperSemicomputable (f : ℕ → ℕ) : Prop :=
  ∃ b : ℕ → ℕ → ℕ, Computable₂ b ∧ (∀ t x, b (t + 1) x ≤ b t x) ∧ (∀ t x, f x ≤ b t x) ∧
    (∀ x, ∃ t, b t x = f x)

/-- Once `b` (non-increasing, everywhere at least `f`) touches `f x` at some stage, it stays there
at every later stage. -/
private theorem UpperSemicomputable.stage_eq_of_touch {b : ℕ → ℕ → ℕ} {f : ℕ → ℕ}
    (hb_anti : ∀ t x, b (t + 1) x ≤ b t x) (hb_ge : ∀ t x, f x ≤ b t x)
    {t₀ x : ℕ} (h0 : b t₀ x = f x) : ∀ t, t₀ ≤ t → b t x = f x := by
  intro t ht
  induction t, ht using Nat.le_induction with
  | base => exact h0
  | succ t ht ih =>
      have h1 := hb_anti t x
      have h2 := hb_ge (t + 1) x
      omega

/-! ## The weight lemma: an upper-semicomputable `f` gives a lower-semicomputable Kraft weight -/

/-- The dyadic approximation witnessing `lowerSemicomputable_two_pow_neg_of_upperSemicomputable`:
`2 ^ (t - b t x - k)` once the budget `t` covers `b t x + k`, else `0`. Named (rather than an
inline lambda) so later `rw`/`ite_eq_left`/`ite_eq_right` steps see the `if` head directly, not a
beta-redex, of the kind `computable_level` in `ALT/CodingTheorem.lean` avoids the same way. -/
private def weightApprox (b : ℕ → ℕ → ℕ) (k t x : ℕ) : ℕ :=
  if b t x + k ≤ t then 2 ^ (t - b t x - k) else 0

private theorem computable_weightApprox {b : ℕ → ℕ → ℕ} (hb : Computable₂ b) (k : ℕ) :
    Computable₂ (weightApprox b k) := by
  have hB : Computable fun tx : ℕ × ℕ => b tx.1 tx.2 :=
    hb.comp Primrec.fst.to_comp Primrec.snd.to_comp
  have hadd : Computable₂ ((· + ·) : ℕ → ℕ → ℕ) := Primrec.nat_add.to_comp
  have hBk : Computable fun tx : ℕ × ℕ => b tx.1 tx.2 + k :=
    Computable₂.comp hadd hB (Computable.const k)
  have hcond : Computable fun tx : ℕ × ℕ => decide (b tx.1 tx.2 + k ≤ tx.1) :=
    (Primrec.nat_le.decide.to_comp).comp hBk Primrec.fst.to_comp
  have hsub : Computable₂ ((· - ·) : ℕ → ℕ → ℕ) := Primrec.nat_sub.to_comp
  have hexp : Computable fun tx : ℕ × ℕ => tx.1 - b tx.1 tx.2 - k :=
    Computable₂.comp hsub (Computable₂.comp hsub Primrec.fst.to_comp hB) (Computable.const k)
  have hpow : Computable₂ ((· ^ ·) : ℕ → ℕ → ℕ) :=
    (Primrec₂.unpaired'.1 Nat.Primrec.pow).to_comp
  have hval : Computable fun tx : ℕ × ℕ => (2 : ℕ) ^ (tx.1 - b tx.1 tx.2 - k) :=
    Computable₂.comp hpow (Computable.const 2) hexp
  exact (Computable.cond hcond hval (Computable.const 0)).of_eq fun tx => by
    unfold weightApprox; rw [Bool.cond_decide]

/-- The real-number identity a valid `weightApprox` term realizes: divided by `2 ^ t`, a Kraft
weight truncated at budget `t` (given the budget covers `m + k`) is exactly `(1/2) ^ (m + k)`. -/
private theorem two_pow_sub_cast_div {t m k : ℕ} (h : m + k ≤ t) :
    ((2 ^ (t - m - k) : ℕ) : ℝ) / 2 ^ t = (1 / 2 : ℝ) ^ (m + k) := by
  have hsub : t - m - k = t - (m + k) := by omega
  push_cast
  rw [hsub, pow_sub₀ (2 : ℝ) (by norm_num) h, one_div, inv_pow]
  rw [mul_comm, mul_div_assoc, div_self (by positivity : (2:ℝ) ^ t ≠ 0), mul_one]

theorem lowerSemicomputable_two_pow_neg_of_upperSemicomputable {f : ℕ → ℕ}
    (hf : UpperSemicomputable f) (k : ℕ) :
    LowerSemicomputable (fun x => (1 / 2 : ℝ) ^ (f x + k)) := by
  obtain ⟨b, hb_comp, hb_anti, hb_ge, hb_attain⟩ := hf
  refine ⟨weightApprox b k, computable_weightApprox hb_comp k, ?_, ?_, ?_⟩
  · -- monotone in the stage
    intro t x
    dsimp only [weightApprox]
    by_cases hg : b t x + k ≤ t
    · have hg' : b (t + 1) x + k ≤ t + 1 := by
        have := hb_anti t x; omega
      rw [ite_eq_left hg, ite_eq_left hg', two_pow_sub_cast_div hg, two_pow_sub_cast_div hg']
      exact two_pow_neg_antitone (by have := hb_anti t x; omega)
    · by_cases hg2 : b (t + 1) x + k ≤ t + 1
      · rw [ite_eq_right hg, ite_eq_left hg2]
        simp only [Nat.cast_zero, zero_div]
        positivity
      · rw [ite_eq_right hg, ite_eq_right hg2]
        simp
  · -- lower bound
    intro t x
    dsimp only [weightApprox]
    by_cases hg : b t x + k ≤ t
    · rw [ite_eq_left hg, two_pow_sub_cast_div hg]
      exact two_pow_neg_antitone (by have := hb_ge t x; omega)
    · rw [ite_eq_right hg]
      simp only [Nat.cast_zero, zero_div]
      positivity
  · -- limit
    intro x q hq
    dsimp only at hq
    obtain ⟨t₀, ht₀⟩ := hb_attain x
    have hstage : ∀ t, t₀ ≤ t → b t x = f x :=
      UpperSemicomputable.stage_eq_of_touch hb_anti hb_ge ht₀
    refine ⟨max t₀ (f x + k), ?_⟩
    dsimp only [weightApprox]
    set t := max t₀ (f x + k) with htdef
    have hbt : b t x = f x := hstage t (le_max_left _ _)
    have hg : b t x + k ≤ t := by rw [hbt]; exact le_max_right _ _
    rw [ite_eq_left hg, two_pow_sub_cast_div hg, hbt]
    exact hq

/-! ## Minimality: prefix complexity is the least upper-semicomputable function with a summable
Kraft weight -/

theorem KB_le_add_of_upperSemicomputable_summable {f : ℕ → ℕ} (hf : UpperSemicomputable f)
    (hs : Summable fun x : ℕ => (1 / 2 : ℝ) ^ f x) :
    ∃ c : ℕ, ∀ x, KB x ≤ f x + c := by
  obtain ⟨k₀, hk₀⟩ :=
    pow_unbounded_of_one_lt (∑' x : ℕ, (1 / 2 : ℝ) ^ f x) (show (1 : ℝ) < 2 by norm_num)
  set μ : ℕ → ℝ := fun x => (1 / 2 : ℝ) ^ (f x + k₀) with hμdef
  have hnn : ∀ x, 0 ≤ μ x := fun x => by simp only [hμdef]; positivity
  have hsumF : ∀ F : Finset ℕ, ∑ x ∈ F, μ x ≤ 1 := by
    intro F
    have h1 : ∑ x ∈ F, (1 / 2 : ℝ) ^ f x ≤ ∑' x : ℕ, (1 / 2 : ℝ) ^ f x :=
      Summable.sum_le_tsum F (fun _ _ => by positivity) hs
    have h2 : ∑ x ∈ F, μ x = (1 / 2 : ℝ) ^ k₀ * ∑ x ∈ F, (1 / 2 : ℝ) ^ f x := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      simp only [hμdef]
      rw [pow_add]; ring
    rw [h2]
    have h4 : (1 / 2 : ℝ) ^ k₀ * (2 : ℝ) ^ k₀ = 1 := by rw [← mul_pow]; norm_num
    nlinarith [h1, hk₀.le, h4, pow_pos (show (0:ℝ) < 1/2 by norm_num) k₀]
  obtain ⟨C, hC⟩ :=
    coding_theorem (lowerSemicomputable_two_pow_neg_of_upperSemicomputable hf k₀) hnn hsumF
  refine ⟨k₀ + 1 + C, fun x => ?_⟩
  have hstrict : (1 / 2 : ℝ) ^ (f x + k₀ + 1) < μ x := by
    simp only [hμdef]
    have hdbl := two_pow_neg_succ_double (f x + k₀)
    have hpos : (0 : ℝ) < (1 / 2 : ℝ) ^ (f x + k₀ + 1) := by positivity
    linarith
  have hKB := hC x (f x + k₀ + 1) hstrict
  omega

/-- A joint witness to `KB_le_add_of_upperSemicomputable_summable`'s two hypotheses, at
`f := fun n => 2 * Nat.size n`: computable at constant stages, hence upper-semicomputable, and its
Kraft weight is summable by comparison with `∑ 1/(n+1)²`. -/
theorem KB_le_add_of_upperSemicomputable_summable_nonvacuous :
    UpperSemicomputable (fun n => 2 * Nat.size n) ∧
      Summable fun n : ℕ => (1 / 2 : ℝ) ^ (2 * Nat.size n) := by
  constructor
  · refine ⟨fun _ n => 2 * Nat.size n, ?_, fun _ _ => le_refl _, fun _ _ => le_refl _,
      fun x => ⟨0, rfl⟩⟩
    have hmul : Computable₂ ((· * ·) : ℕ → ℕ → ℕ) := Primrec.nat_mul.to_comp
    exact Computable₂.comp hmul (Computable.const 2)
      (computable_nat_size.comp Primrec.snd.to_comp)
  · have h1 : Summable fun n : ℕ => (1 / (n : ℝ) ^ 2) :=
      Real.summable_one_div_nat_pow.mpr (by norm_num)
    have h2 : Summable fun n : ℕ => (1 / ((n + 1 : ℕ) : ℝ) ^ 2) :=
      (summable_nat_add_iff (f := fun n : ℕ => 1 / (n : ℝ) ^ 2) 1).mpr h1
    have hcomp : Summable fun n : ℕ => (1 / ((n : ℝ) + 1) ^ 2) := by
      simpa using h2
    apply hcomp.of_nonneg_of_le (fun n => by positivity)
    intro n
    have hlt : n < 2 ^ Nat.size n := Nat.lt_size_self n
    have hle : (n : ℝ) + 1 ≤ (2 : ℝ) ^ Nat.size n := by
      have hnat : n + 1 ≤ 2 ^ Nat.size n := hlt
      exact_mod_cast hnat
    have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hstep : (1 : ℝ) / (2 : ℝ) ^ Nat.size n ≤ 1 / ((n : ℝ) + 1) :=
      one_div_le_one_div_of_le hpos hle
    have hnn : (0 : ℝ) ≤ 1 / (2 : ℝ) ^ Nat.size n := by positivity
    have heq : (1 / 2 : ℝ) ^ (2 * Nat.size n) = (1 / (2 : ℝ) ^ Nat.size n) ^ 2 := by
      rw [div_pow, one_pow, div_pow, one_pow, ← pow_mul, mul_comm (Nat.size n) 2]
    rw [heq]
    calc (1 / (2 : ℝ) ^ Nat.size n) ^ 2 ≤ (1 / ((n : ℝ) + 1)) ^ 2 :=
          pow_le_pow_left₀ hnn hstep 2
      _ = 1 / ((n : ℝ) + 1) ^ 2 := by rw [div_pow, one_pow]

theorem summable_of_KB_le_add {f : ℕ → ℕ} {c : ℕ} (h : ∀ x, KB x ≤ f x + c) :
    Summable fun x : ℕ => (1 / 2 : ℝ) ^ f x := by
  have hmaj : Summable fun x : ℕ => (2 : ℝ) ^ c * (1 / 2 : ℝ) ^ KB x :=
    summable_two_pow_neg_KB.mul_left _
  apply hmaj.of_nonneg_of_le (fun x => by positivity)
  intro x
  have hle : (1 / 2 : ℝ) ^ (f x + c) ≤ (1 / 2 : ℝ) ^ KB x := two_pow_neg_antitone (h x)
  have heq1 : (1 / 2 : ℝ) ^ (f x + c) = (1 / 2 : ℝ) ^ f x * (1 / 2 : ℝ) ^ c := pow_add _ _ _
  have hcancel : (1 / 2 : ℝ) ^ (f x + c) * (2 : ℝ) ^ c = (1 / 2 : ℝ) ^ f x := by
    rw [heq1, mul_assoc, ← mul_pow]
    norm_num
  have h2cpos : (0 : ℝ) ≤ (2 : ℝ) ^ c := by positivity
  calc (1 / 2 : ℝ) ^ f x = (1 / 2 : ℝ) ^ (f x + c) * (2 : ℝ) ^ c := hcancel.symm
    _ ≤ (1 / 2 : ℝ) ^ KB x * (2 : ℝ) ^ c := mul_le_mul_of_nonneg_right hle h2cpos
    _ = (2 : ℝ) ^ c * (1 / 2 : ℝ) ^ KB x := by ring

theorem KB_le_add_iff_summable {f : ℕ → ℕ} (hf : UpperSemicomputable f) :
    (∃ c : ℕ, ∀ x, KB x ≤ f x + c) ↔ Summable fun x : ℕ => (1 / 2 : ℝ) ^ f x :=
  ⟨fun ⟨_, hc⟩ => summable_of_KB_le_add hc,
    fun hs => KB_le_add_of_upperSemicomputable_summable hf hs⟩

/-! ## The plain bit-length is upper-semicomputable -/

/-- The least index `< t` whose code computes `x` (from input `0`) within `t` `evaln`-steps,
combined via `min` over the whole search rather than by priority-override: `min`'s commutativity
makes the search's monotonicity in the budget elementary. -/
private def indexMinFold (t x : ℕ) : ℕ :=
  (List.range t).foldr
    (fun c acc => if evaln t (Denumerable.ofNat Code c) 0 = some x then min c acc else acc)
    (Encodable.encode (Code.const x))

/-- The generic `min`-fold `indexMinFold` specializes: folding `min c acc` on a hit, `acc`
unchanged on a miss, over an arbitrary predicate and list. -/
private def minFold (Q : ℕ → Prop) [DecidablePred Q] (l : List ℕ) (S : ℕ) : ℕ :=
  l.foldr (fun c acc => if Q c then min c acc else acc) S

private theorem indexMinFold_eq_minFold (t x : ℕ) :
    indexMinFold t x =
      minFold (fun c => evaln t (Denumerable.ofNat Code c) 0 = some x) (List.range t)
        (Encodable.encode (Code.const x)) := rfl

private theorem minFold_cons (Q : ℕ → Prop) [DecidablePred Q] (a : ℕ) (l : List ℕ) (S : ℕ) :
    minFold Q (a :: l) S = if Q a then min a (minFold Q l S) else minFold Q l S := rfl

private theorem minFold_le_of_mem {Q : ℕ → Prop} [DecidablePred Q] {l : List ℕ} {S c : ℕ}
    (hc : c ∈ l) (hQc : Q c) : minFold Q l S ≤ c := by
  induction l with
  | nil => cases hc
  | cons a l ih =>
      rw [minFold_cons]
      rcases List.mem_cons.mp hc with rfl | hc'
      · rw [ite_eq_left hQc]; exact min_le_left _ _
      · by_cases ha : Q a
        · rw [ite_eq_left ha]; exact le_trans (min_le_right _ _) (ih hc')
        · rw [ite_eq_right ha]; exact ih hc'

private theorem le_size_minFold_of {Q : ℕ → Prop} [DecidablePred Q] {l : List ℕ} {S V : ℕ}
    (hS : V ≤ Nat.size S) (hl : ∀ c ∈ l, Q c → V ≤ Nat.size c) :
    V ≤ Nat.size (minFold Q l S) := by
  induction l with
  | nil => simpa [minFold] using hS
  | cons a l ih =>
      have ihl : V ≤ Nat.size (minFold Q l S) :=
        ih (fun c hc hQc => hl c (List.mem_cons_of_mem _ hc) hQc)
      rw [minFold_cons]
      by_cases ha : Q a
      · rw [ite_eq_left ha]
        have hVa : V ≤ Nat.size a := hl a List.mem_cons_self ha
        rcases le_total a (minFold Q l S) with h | h
        · rwa [min_eq_left h]
        · rwa [min_eq_right h]
      · rwa [ite_eq_right ha]

private theorem minFold_mono_init {Q : ℕ → Prop} [DecidablePred Q] {l : List ℕ} {S1 S2 : ℕ}
    (h : S1 ≤ S2) : minFold Q l S1 ≤ minFold Q l S2 := by
  induction l with
  | nil => exact h
  | cons a l ih =>
      rw [minFold_cons, minFold_cons]
      by_cases ha : Q a
      · rw [ite_eq_left ha, ite_eq_left ha]; exact min_le_min le_rfl ih
      · rw [ite_eq_right ha, ite_eq_right ha]; exact ih

private theorem minFold_le_minFold_of_imp {Q Q' : ℕ → Prop} [DecidablePred Q] [DecidablePred Q']
    {l : List ℕ} {S : ℕ} (himp : ∀ c ∈ l, Q c → Q' c) :
    minFold Q' l S ≤ minFold Q l S := by
  induction l with
  | nil => exact le_refl S
  | cons a l ih =>
      have ihl : minFold Q' l S ≤ minFold Q l S :=
        ih (fun c hc hQc => himp c (List.mem_cons_of_mem _ hc) hQc)
      rw [minFold_cons, minFold_cons]
      by_cases ha : Q a
      · have ha' : Q' a := himp a List.mem_cons_self ha
        rw [ite_eq_left ha, ite_eq_left ha']
        exact min_le_min le_rfl ihl
      · rw [ite_eq_right ha]
        by_cases ha' : Q' a
        · rw [ite_eq_left ha']; exact le_trans (min_le_right _ _) ihl
        · rw [ite_eq_right ha']; exact ihl

/-- **`indexMinFold` is non-increasing in the budget**: more budget only persists old matches
(`evaln_mono`) and can only add new candidates, and `min` folds candidates order-independently. -/
private theorem indexMinFold_succ_le (t x : ℕ) : indexMinFold (t + 1) x ≤ indexMinFold t x := by
  set Qt : ℕ → Prop := fun c => evaln t (Denumerable.ofNat Code c) 0 = some x with hQt
  set Qt1 : ℕ → Prop := fun c => evaln (t + 1) (Denumerable.ofNat Code c) 0 = some x with hQt1
  set S : ℕ := Encodable.encode (Code.const x) with hSdef
  have hrange : List.range (t + 1) = List.range t ++ [t] := List.range_succ
  have hstep : indexMinFold (t + 1) x = minFold Qt1 (List.range t) (minFold Qt1 [t] S) := by
    rw [indexMinFold_eq_minFold, hrange]
    change (List.range t ++ [t]).foldr (fun c acc => if Qt1 c then min c acc else acc) S = _
    rw [List.foldr_append]
    rfl
  have hSinit_le : minFold Qt1 [t] S ≤ S := by
    change (if Qt1 t then min t S else S) ≤ S
    by_cases ht : Qt1 t
    · rw [ite_eq_left ht]; exact min_le_right _ _
    · rw [ite_eq_right ht]
  have himp : ∀ c ∈ List.range t, Qt c → Qt1 c := fun c _ hc =>
    evaln_mono (Nat.le_succ t) hc
  calc indexMinFold (t + 1) x = minFold Qt1 (List.range t) (minFold Qt1 [t] S) := hstep
    _ ≤ minFold Qt1 (List.range t) S := minFold_mono_init hSinit_le
    _ ≤ minFold Qt (List.range t) S := minFold_le_minFold_of_imp himp
    _ = indexMinFold t x := (indexMinFold_eq_minFold t x).symm

private theorem primrec_indexMinFold : Primrec₂ indexMinFold := by
  have hf : Primrec fun p : ℕ × ℕ => List.range p.1 := Primrec.list_range.comp Primrec.fst
  have hg : Primrec fun p : ℕ × ℕ => Encodable.encode (Code.const p.2) :=
    Primrec.encode.comp (Nat.Partrec.Code.primrec_const.comp Primrec.snd)
  have hh : Primrec₂ (fun (p : ℕ × ℕ) (ca : ℕ × ℕ) =>
      if evaln p.1 (Denumerable.ofNat Code ca.1) 0 = some p.2 then min ca.1 ca.2 else ca.2) := by
    have hc : Primrec fun q : (ℕ × ℕ) × ℕ × ℕ => Denumerable.ofNat Code q.2.1 :=
      (Primrec.ofNat Code).comp (Primrec.fst.comp Primrec.snd)
    have ht : Primrec fun q : (ℕ × ℕ) × ℕ × ℕ => q.1.1 := Primrec.fst.comp Primrec.fst
    have hev : Primrec fun q : (ℕ × ℕ) × ℕ × ℕ =>
        evaln q.1.1 (Denumerable.ofNat Code q.2.1) 0 := by
      have hq : Primrec fun q : (ℕ × ℕ) × ℕ × ℕ => ((q.1.1, Denumerable.ofNat Code q.2.1), 0) :=
        (ht.pair hc).pair (Primrec.const 0)
      exact Primrec.comp Nat.Partrec.Code.primrec_evaln hq
    have hSomeX : Primrec fun q : (ℕ × ℕ) × ℕ × ℕ => (some q.1.2 : Option ℕ) :=
      Primrec.option_some.comp (Primrec.snd.comp Primrec.fst)
    have hcond : Primrec fun q : (ℕ × ℕ) × ℕ × ℕ =>
        decide (evaln q.1.1 (Denumerable.ofNat Code q.2.1) 0 = some q.1.2) :=
      (Primrec.eq.comp hev hSomeX).decide
    have hmin : Primrec fun q : (ℕ × ℕ) × ℕ × ℕ => min q.2.1 q.2.2 :=
      Primrec.nat_min.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)
    have hacc : Primrec fun q : (ℕ × ℕ) × ℕ × ℕ => q.2.2 := Primrec.snd.comp Primrec.snd
    exact (Primrec.cond hcond hmin hacc).of_eq fun q => by simp
  exact Primrec.list_foldr hf hg hh

/-- The stage sequence witnessing `K_bitlen`'s upper-semicomputability: `Nat.size` of the least
index found so far. -/
private def bStage (t x : ℕ) : ℕ := Nat.size (indexMinFold t x)

private theorem computable_bStage : Computable₂ bStage :=
  computable_nat_size.comp primrec_indexMinFold.to_comp

private theorem bStage_anti (t x : ℕ) : bStage (t + 1) x ≤ bStage t x :=
  Nat.size_le_size (indexMinFold_succ_le t x)

private theorem K_bitlen_le_bStage (t x : ℕ) : K_bitlen x ≤ bStage t x := by
  apply le_size_minFold_of
  · have h := K_bitlen_le (const_computes x)
    simpa [codelen', codelen] using h
  · intro c _ hQc
    have hcomputes : Computes (Denumerable.ofNat Code c) x :=
      Part.eq_some_iff.mpr (evaln_sound hQc)
    have h := K_bitlen_le hcomputes
    rwa [codelen', codelen, Denumerable.encode_ofNat] at h

private theorem bStage_attains (x : ℕ) : ∃ t, bStage t x = K_bitlen x := by
  obtain ⟨c₀, hc₀comp, hc₀len⟩ := exists_min_code x
  obtain ⟨T, hT⟩ := evaln_complete.mp (Part.eq_some_iff.mp hc₀comp)
  set t := max T (codelen c₀ + 1) with htdef
  refine ⟨t, le_antisymm ?_ (K_bitlen_le_bStage t x)⟩
  have hmemrange : codelen c₀ ∈ List.range t := List.mem_range.mpr (by omega)
  have hTt : T ≤ t := le_max_left _ _
  have hev' : evaln t c₀ 0 = some x := evaln_mono hTt hT
  have hofnat : Denumerable.ofNat Code (codelen c₀) = c₀ := Denumerable.ofNat_encode c₀
  have hQ : evaln t (Denumerable.ofNat Code (codelen c₀)) 0 = some x := by
    rw [hofnat]; exact hev'
  have hle : indexMinFold t x ≤ codelen c₀ := minFold_le_of_mem hmemrange hQ
  calc bStage t x = Nat.size (indexMinFold t x) := rfl
    _ ≤ Nat.size (codelen c₀) := Nat.size_le_size hle
    _ = Nat.size (K x) := by rw [hc₀len]
    _ = K_bitlen x := (K_bitlen_eq x).symm

theorem upperSemicomputable_K_bitlen : UpperSemicomputable K_bitlen :=
  ⟨bStage, computable_bStage, bStage_anti, K_bitlen_le_bStage, bStage_attains⟩

theorem KB_le_K_bitlen_add_iff_summable :
    (∃ c : ℕ, ∀ x, KB x ≤ K_bitlen x + c) ↔ Summable fun x : ℕ => (1 / 2 : ℝ) ^ K_bitlen x :=
  KB_le_add_iff_summable upperSemicomputable_K_bitlen

/-! ## A second route to FV-28's Elias bound -/

/-- **A second proof of `PrefixEliasKB.KB_le_two_mul_size`** (FV-28), through the coding theorem's
minimality in place of the Elias decoder — no comparison of the two constants is claimed. -/
theorem KB_le_two_mul_size' : ∃ c : ℕ, ∀ n, KB n ≤ 2 * Nat.size n + c :=
  KB_le_add_of_upperSemicomputable_summable
    KB_le_add_of_upperSemicomputable_summable_nonvacuous.1
    KB_le_add_of_upperSemicomputable_summable_nonvacuous.2

end PrefixMachine
