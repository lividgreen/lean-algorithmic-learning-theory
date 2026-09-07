/-
Copyright (c) 2026 Mykola Palamarchuk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mykola Palamarchuk
-/
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.Group.Units.Equiv
import Mathlib.Tactic.LinearCombination

/-!
# Block-pair correlation profile

## Main results

* `cyclicCorr`, `aperiodicCorr`, `crossTail` — the three correlation sums: cyclic (over `ZMod N`),
  aperiodic (over a finite word), and cross-tail (the wrap-around remainder between two words).
* `blockSeq`, `blockSeq_val` — a two-word, sign-modulated block sequence, and its value.
* `cyclicCorr_blockSeq`, `cyclicCorr_blockSeq_zone`, `cyclicCorr_blockSeq_spike` — the block
  sequence's own cyclic correlation, split into its "zone" (bulk) and "spike" (boundary) parts.
* `cyclicCorrPrefix`, `cyclicCorrWindow` — the prefix and sliding-window correlation sums, with
  `cyclicCorrPrefix_add_period`, `cyclicCorrPrefix_mod_period`, `cyclicCorrWindow_eq_sub` their
  periodicity and telescoping identities.
* `cyclicCorrPrefix_blockSeq_zone`/`_spike`, `cyclicCorrWindow_blockSeq_zone`/`_spike`,
  `cyclicCorrWindow_blockSeq_family_zone` — the block sequence's own prefix and window
  correlations, zone and spike parts.
* `singleWindow` — the single-offset sliding window sum.
* `tmSign`, `tau`, `blockSign`, `tmPrefix` — the Thue–Morse sign, its block-paired form, the
  running block sign, and its prefix product, with `tmSign_balance`, `tmSign_partial_odd`,
  `tmSign_partial_abs_le_one`, `tau_partial_even_abs_le_one`, `tau_partial_odd_abs_le_one`,
  `blockSign_sq`, `blockSign_mul_noWrap`, `blockSign_mul_wrap`, `blockSign_transition_even`/`_odd`,
  `tmPrefix_two_mul`/`_add_one`, `blockSign_eq_tmPrefix` their bounds and identities.
* `wordU`, `wordV` — the certified length-`24` design pair, with `blockSeq_wordU_wordV_correlation`
  and its prefix/window specializations (`cyclicCorrPrefix_blockSeq_wordU_wordV_zone`/`_spike`,
  `cyclicCorrWindow_blockSeq_wordU_wordV_zone`/`_spike`, `singleWindow_blockSeq_wordU_wordV_bound`,
  `blockSeq_wordU_wordV_sq`) the exact correlation profile `BlockPairHost`/`BlockPairCriterion`
  consume.
-/

namespace BlockPairProfile

def cyclicCorr {N : ℕ} [NeZero N] (x : ZMod N → ℤ) (d : ℕ) : ℤ :=
  ∑ t : ZMod N, x t * x (t + d)

def aperiodicCorr {L : ℕ} (w : Fin L → ℤ) (d : ℕ) : ℤ :=
  ∑ p : Fin L, if h : p.val + d < L then w p * w ⟨p.val + d, h⟩ else 0

def crossTail {L : ℕ} (w w' : Fin L → ℤ) (d : ℕ) : ℤ :=
  ∑ i : Fin L, if h : i.val < d then w ⟨L - d + i.val, by omega⟩ * w' i else 0

def tmSign (i : ℕ) : ℤ := if (Nat.digits 2 i).count 1 % 2 = 0 then 1 else -1

private def blockIdx {m L : ℕ} [NeZero m] [NeZero L] (t : ZMod (m * L)) : Fin m :=
  ⟨t.val / L, (Nat.div_lt_iff_lt_mul (NeZero.pos L)).mpr (ZMod.val_lt t)⟩

private def blockOff {m L : ℕ} [NeZero m] [NeZero L] (t : ZMod (m * L)) : Fin L :=
  ⟨t.val % L, Nat.mod_lt _ (NeZero.pos L)⟩

private def combine {m L : ℕ} (j : Fin m) (p : Fin L) : ZMod (m * L) :=
  ((L * j.val + p.val : ℕ) : ZMod (m * L))

def blockSeq {m L : ℕ} [NeZero m] [NeZero L] (u v : Fin L → ℤ) (ε : Fin m → ℤ)
    (t : ZMod (m * L)) : ℤ :=
  if Even (blockIdx t).val then ε (blockIdx t) * u (blockOff t)
  else ε (blockIdx t) * v (blockOff t)

/-- **`blockSeq` unfolded on the block/offset pair**: `blockIdx t`/`blockOff t` made explicit as
`t.val / L`, `t.val % L`, exposing what those private helpers compute for a numeral-level reader. -/
theorem blockSeq_val {m L : ℕ} [NeZero m] [NeZero L] (u v : Fin L → ℤ) (ε : Fin m → ℤ)
    (t : ZMod (m * L)) :
    blockSeq u v ε t =
      if Even (t.val / L) then
        ε ⟨t.val / L, (Nat.div_lt_iff_lt_mul (NeZero.pos L)).mpr (ZMod.val_lt t)⟩
          * u ⟨t.val % L, Nat.mod_lt _ (NeZero.pos L)⟩
      else
        ε ⟨t.val / L, (Nat.div_lt_iff_lt_mul (NeZero.pos L)).mpr (ZMod.val_lt t)⟩
          * v ⟨t.val % L, Nat.mod_lt _ (NeZero.pos L)⟩ := by
  unfold blockSeq blockIdx blockOff
  rfl

private lemma combine_val {m L : ℕ} [NeZero m] [NeZero L] (j : Fin m) (p : Fin L) :
    (combine j p : ZMod (m * L)).val = L * j.val + p.val :=
  ZMod.val_cast_of_lt (by nlinarith [j.isLt, p.isLt])

private lemma blockIdx_combine {m L : ℕ} [NeZero m] [NeZero L] (j : Fin m) (p : Fin L) :
    blockIdx (combine j p) = j := by
  ext
  change (combine j p).val / L = j.val
  rw [combine_val, Nat.mul_add_div (NeZero.pos L), Nat.div_eq_of_lt p.isLt, add_zero]

private lemma blockOff_combine {m L : ℕ} [NeZero m] [NeZero L] (j : Fin m) (p : Fin L) :
    blockOff (combine j p) = p := by
  ext
  change (combine j p).val % L = p.val
  rw [combine_val, Nat.mul_add_mod, Nat.mod_eq_of_lt p.isLt]

private lemma combine_blockIdx_blockOff {m L : ℕ} [NeZero m] [NeZero L] (t : ZMod (m * L)) :
    combine (blockIdx t) (blockOff t) = t := by
  change ((L * (t.val / L) + t.val % L : ℕ) : ZMod (m * L)) = t
  rw [Nat.div_add_mod]
  exact ZMod.natCast_rightInverse t

private lemma sum_combine {m L : ℕ} [NeZero m] [NeZero L] (F : ZMod (m * L) → ℤ) :
    ∑ t : ZMod (m * L), F t = ∑ j : Fin m, ∑ p : Fin L, F (combine j p) := by
  rw [← Fintype.sum_prod_type']
  apply Finset.sum_nbij' (fun t => (blockIdx t, blockOff t)) (fun jp => combine jp.1 jp.2)
  · intros; exact Finset.mem_univ _
  · intros; exact Finset.mem_univ _
  · intro t _; exact combine_blockIdx_blockOff t
  · intro jp _; simp [blockIdx_combine, blockOff_combine]
  · intro t _; simp [combine_blockIdx_blockOff]

/-- The cyclic successor block index, `(j.val + 1) % m`. -/
private def nextBlock {m : ℕ} [NeZero m] (j : Fin m) : Fin m :=
  ⟨(j.val + 1) % m, Nat.mod_lt _ (NeZero.pos m)⟩

private lemma nextBlock_eq_add_one {m : ℕ} [NeZero m] (j : Fin m) : nextBlock j = j + 1 := by
  ext
  change (j.val + 1) % m = (j + 1).val
  rw [Fin.val_add, Fin.val_one']
  exact Nat.ModEq.add_left j.val (Nat.mod_modEq 1 m).symm

private lemma shift_inBlock {m L : ℕ} [NeZero m] [NeZero L] (j : Fin m) (p : Fin L) (d : ℕ)
    (h : p.val + d < L) :
    combine j p + (d : ZMod (m * L)) = combine j ⟨p.val + d, h⟩ := by
  change ((L * j.val + p.val : ℕ) : ZMod (m * L)) + ((d : ℕ) : ZMod (m * L))
      = ((L * j.val + (p.val + d) : ℕ) : ZMod (m * L))
  rw [← Nat.cast_add]
  congr 1
  omega

private lemma shift_crossBlock {m L : ℕ} [NeZero m] [NeZero L] (j : Fin m) (p : Fin L) (d : ℕ)
    (hd : d ≤ L) (h : L ≤ p.val + d) :
    combine j p + (d : ZMod (m * L)) = combine (nextBlock j) ⟨p.val + d - L, by omega⟩ := by
  change ((L * j.val + p.val : ℕ) : ZMod (m * L)) + ((d : ℕ) : ZMod (m * L))
      = ((L * (nextBlock j).val + (p.val + d - L) : ℕ) : ZMod (m * L))
  rw [← Nat.cast_add, ZMod.natCast_eq_natCast_iff]
  have hr : (nextBlock j).val ≡ j.val + 1 [MOD m] := Nat.mod_modEq (j.val + 1) m
  have hrL : (nextBlock j).val * L ≡ (j.val + 1) * L [MOD m * L] := hr.mul_right' L
  have hexp : (j.val + 1) * L = L * j.val + L := by ring
  have heq : L * j.val + p.val + d = (j.val + 1) * L + (p.val + d - L) := by omega
  calc L * j.val + p.val + d = (j.val + 1) * L + (p.val + d - L) := heq
    _ ≡ (nextBlock j).val * L + (p.val + d - L) [MOD m * L] := (hrL.symm).add_right _
    _ = L * (nextBlock j).val + (p.val + d - L) := by rw [mul_comm]

private def rotFwd {L : ℕ} (d : ℕ) (x : Fin L) : Fin L :=
  if h : x.val < d then ⟨L - d + x.val, by omega⟩ else ⟨x.val - d, by omega⟩

private def rotBwd {L : ℕ} (d : ℕ) (hd : d ≤ L) (y : Fin L) : Fin L :=
  if h : L ≤ y.val + d then ⟨y.val + d - L, by omega⟩ else ⟨y.val + d, by omega⟩

private lemma rotFwd_val_lt {L : ℕ} (d : ℕ) (x : Fin L) (h : x.val < d) :
    (rotFwd d x).val = L - d + x.val := by rw [rotFwd, dif_pos h]

private lemma rotFwd_val_ge {L : ℕ} (d : ℕ) (x : Fin L) (h : ¬ x.val < d) :
    (rotFwd d x).val = x.val - d := by rw [rotFwd, dif_neg h]

private lemma rotBwd_val_lt {L : ℕ} (d : ℕ) (hd : d ≤ L) (y : Fin L) (h : L ≤ y.val + d) :
    (rotBwd d hd y).val = y.val + d - L := by rw [rotBwd, dif_pos h]

private lemma rotBwd_val_ge {L : ℕ} (d : ℕ) (hd : d ≤ L) (y : Fin L) (h : ¬ L ≤ y.val + d) :
    (rotBwd d hd y).val = y.val + d := by rw [rotBwd, dif_neg h]

private lemma rotBwd_rotFwd {L : ℕ} (d : ℕ) (hd : d ≤ L) (x : Fin L) :
    rotBwd d hd (rotFwd d x) = x := by
  by_cases h : x.val < d
  · have e1 : (rotFwd d x).val = L - d + x.val := rotFwd_val_lt d x h
    have e2 : L ≤ (rotFwd d x).val + d := by omega
    apply Fin.ext
    rw [rotBwd_val_lt d hd (rotFwd d x) e2, e1]
    omega
  · have e1 : (rotFwd d x).val = x.val - d := rotFwd_val_ge d x h
    have e2 : ¬ L ≤ (rotFwd d x).val + d := by omega
    apply Fin.ext
    rw [rotBwd_val_ge d hd (rotFwd d x) e2, e1]
    omega

private lemma rotFwd_rotBwd {L : ℕ} (d : ℕ) (hd : d ≤ L) (y : Fin L) :
    rotFwd d (rotBwd d hd y) = y := by
  by_cases h : L ≤ y.val + d
  · have e1 : (rotBwd d hd y).val = y.val + d - L := rotBwd_val_lt d hd y h
    have e2 : (rotBwd d hd y).val < d := by omega
    apply Fin.ext
    rw [rotFwd_val_lt d (rotBwd d hd y) e2, e1]
    omega
  · have e1 : (rotBwd d hd y).val = y.val + d := rotBwd_val_ge d hd y h
    have e2 : ¬ (rotBwd d hd y).val < d := by omega
    apply Fin.ext
    rw [rotFwd_val_ge d (rotBwd d hd y) e2, e1]
    omega

private lemma crossTail_eq_sum_p {L : ℕ} (w w' : Fin L → ℤ) (d : ℕ) (hd : d ≤ L) :
    crossTail w w' d =
      ∑ p : Fin L, if h : L ≤ p.val + d then w p * w' ⟨p.val + d - L, by omega⟩ else 0 := by
  unfold crossTail
  apply Finset.sum_nbij' (rotFwd d) (rotBwd d hd)
  · intros; exact Finset.mem_univ _
  · intros; exact Finset.mem_univ _
  · intro x _; exact rotBwd_rotFwd d hd x
  · intro y _; exact rotFwd_rotBwd d hd y
  · intro x _
    by_cases h : x.val < d
    · have e1 : (rotFwd d x).val = L - d + x.val := rotFwd_val_lt d x h
      have e2 : L ≤ (rotFwd d x).val + d := by omega
      rw [dif_pos h, dif_pos e2]
      have hfx : (⟨L - d + x.val, by omega⟩ : Fin L) = rotFwd d x := Fin.ext e1.symm
      have hidx : (⟨(rotFwd d x).val + d - L, by omega⟩ : Fin L) = x := by
        apply Fin.ext
        change (rotFwd d x).val + d - L = x.val
        omega
      rw [hfx, hidx]
    · have e1 : (rotFwd d x).val = x.val - d := rotFwd_val_ge d x h
      have e2 : ¬ L ≤ (rotFwd d x).val + d := by omega
      rw [dif_neg h, dif_neg e2]

/-- The word carried by block `j`: `u` on even blocks, `v` on odd blocks. -/
private def wordAt {m L : ℕ} (u v : Fin L → ℤ) (j : Fin m) : Fin L → ℤ :=
  if Even j.val then u else v

private lemma blockSeq_combine {m L : ℕ} [NeZero m] [NeZero L] (u v : Fin L → ℤ) (ε : Fin m → ℤ)
    (j : Fin m) (p : Fin L) :
    blockSeq u v ε (combine j p) = ε j * wordAt u v j p := by
  unfold blockSeq wordAt
  rw [blockIdx_combine, blockOff_combine]
  split_ifs <;> rfl

private lemma inner_sum_eq {m L : ℕ} [NeZero m] [NeZero L] (u v : Fin L → ℤ) (ε : Fin m → ℤ)
    (hε : ∀ j, ε j * ε j = 1) (j : Fin m) (d : ℕ) (hd : d ≤ L) :
    ∑ p : Fin L, blockSeq u v ε (combine j p) * blockSeq u v ε (combine j p + (d : ZMod (m * L))) =
      aperiodicCorr (wordAt u v j) d +
        ε j * ε (nextBlock j) * crossTail (wordAt u v j) (wordAt u v (nextBlock j)) d := by
  have hpt : ∀ p : Fin L,
      blockSeq u v ε (combine j p) * blockSeq u v ε (combine j p + (d : ZMod (m * L))) =
        (if h : p.val + d < L then wordAt u v j p * wordAt u v j ⟨p.val + d, h⟩ else 0) +
          (if h : L ≤ p.val + d then
              ε j * ε (nextBlock j) *
                (wordAt u v j p * wordAt u v (nextBlock j) ⟨p.val + d - L, by omega⟩)
            else 0) := by
    intro p
    rw [blockSeq_combine]
    by_cases h : p.val + d < L
    · rw [shift_inBlock j p d h, blockSeq_combine, dif_pos h,
        dif_neg (show ¬ (L ≤ p.val + d) by omega)]
      have hring : ε j * wordAt u v j p * (ε j * wordAt u v j ⟨p.val + d, h⟩) =
          ε j * ε j * (wordAt u v j p * wordAt u v j ⟨p.val + d, h⟩) := by ring
      rw [hring, hε j, one_mul, add_zero]
    · rw [shift_crossBlock j p d hd (by omega), blockSeq_combine, dif_neg h,
        dif_pos (show L ≤ p.val + d by omega)]
      rw [zero_add]
      ring
  simp_rw [hpt]
  rw [Finset.sum_add_distrib]
  congr 1
  rw [show (∑ p : Fin L, if h : L ≤ p.val + d then
        ε j * ε (nextBlock j) *
          (wordAt u v j p * wordAt u v (nextBlock j) ⟨p.val + d - L, by omega⟩)
      else 0) =
      ε j * ε (nextBlock j) * ∑ p : Fin L, if h : L ≤ p.val + d then
        wordAt u v j p * wordAt u v (nextBlock j) ⟨p.val + d - L, by omega⟩
      else 0 from by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p _
    split_ifs with h
    · ring
    · ring]
  rw [← crossTail_eq_sum_p (wordAt u v j) (wordAt u v (nextBlock j)) d hd]

private def evenIdx {M' : ℕ} (i : Fin M') : Fin (2 * M') := ⟨2 * i.val, by omega⟩

private def oddIdx {M' : ℕ} (i : Fin M') : Fin (2 * M') := ⟨2 * i.val + 1, by omega⟩

private lemma evenIdx_even {M' : ℕ} (i : Fin M') : Even (evenIdx i).val := ⟨i.val, two_mul i.val⟩

private lemma oddIdx_odd {M' : ℕ} (i : Fin M') : Odd (oddIdx i).val := ⟨i.val, rfl⟩

private lemma nextBlock_evenIdx {M' : ℕ} [NeZero (2 * M')] (i : Fin M') :
    nextBlock (evenIdx i) = oddIdx i := by
  apply Fin.ext
  change (2 * i.val + 1) % (2 * M') = 2 * i.val + 1
  exact Nat.mod_eq_of_lt (by omega)

private lemma nextBlock_oddIdx {M' : ℕ} [NeZero M'] [NeZero (2 * M')] (i : Fin M') :
    nextBlock (oddIdx i) = evenIdx ⟨(i.val + 1) % M', Nat.mod_lt _ (NeZero.pos M')⟩ := by
  apply Fin.ext
  change (2 * i.val + 1 + 1) % (2 * M') = 2 * ((i.val + 1) % M')
  have : 2 * i.val + 1 + 1 = 2 * (i.val + 1) := by ring
  rw [this, Nat.mul_mod_mul_left]

private lemma wordAt_evenIdx {M' L : ℕ} (u v : Fin L → ℤ) (i : Fin M') :
    wordAt u v (evenIdx i) = u := by
  unfold wordAt
  rw [if_pos (evenIdx_even i)]

private lemma wordAt_oddIdx {M' L : ℕ} (u v : Fin L → ℤ) (i : Fin M') :
    wordAt u v (oddIdx i) = v := by
  unfold wordAt
  rw [if_neg (Nat.not_even_iff_odd.mpr (oddIdx_odd i))]

private lemma sum_filter_even {M' : ℕ} [NeZero (2 * M')] (G : Fin (2 * M') → ℤ) :
    ∑ j ∈ Finset.univ.filter (fun j : Fin (2 * M') => Even j.val), G j =
      ∑ i : Fin M', G (evenIdx i) := by
  apply Finset.sum_nbij' (fun j => (⟨j.val / 2, by omega⟩ : Fin M')) evenIdx
  · intros; exact Finset.mem_univ _
  · intro i _
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, evenIdx_even i⟩
  · intro x hx
    obtain ⟨-, hxe⟩ := Finset.mem_filter.mp hx
    apply Fin.ext
    obtain ⟨c, hc⟩ := hxe
    change 2 * (x.val / 2) = x.val
    omega
  · intro i _
    apply Fin.ext
    change (evenIdx i).val / 2 = i.val
    change (2 * i.val) / 2 = i.val
    omega
  · intro x hx
    obtain ⟨-, hxe⟩ := Finset.mem_filter.mp hx
    obtain ⟨c, hc⟩ := hxe
    have hxv : x = evenIdx (⟨x.val / 2, by omega⟩ : Fin M') := by
      apply Fin.ext
      change x.val = 2 * (x.val / 2)
      omega
    exact congrArg G hxv

private lemma sum_filter_odd {M' : ℕ} [NeZero (2 * M')] (G : Fin (2 * M') → ℤ) :
    ∑ j ∈ Finset.univ.filter (fun j : Fin (2 * M') => Odd j.val), G j =
      ∑ i : Fin M', G (oddIdx i) := by
  apply Finset.sum_nbij' (fun j => (⟨j.val / 2, by omega⟩ : Fin M')) oddIdx
  · intros; exact Finset.mem_univ _
  · intro i _
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, oddIdx_odd i⟩
  · intro x hx
    obtain ⟨-, hxo⟩ := Finset.mem_filter.mp hx
    apply Fin.ext
    obtain ⟨c, hc⟩ := hxo
    change 2 * (x.val / 2) + 1 = x.val
    omega
  · intro i _
    apply Fin.ext
    change (oddIdx i).val / 2 = i.val
    change (2 * i.val + 1) / 2 = i.val
    omega
  · intro x hx
    obtain ⟨-, hxo⟩ := Finset.mem_filter.mp hx
    obtain ⟨c, hc⟩ := hxo
    have hxv : x = oddIdx (⟨x.val / 2, by omega⟩ : Fin M') := by
      apply Fin.ext
      change x.val = 2 * (x.val / 2) + 1
      omega
    exact congrArg G hxv

private lemma sum_even_add_odd {M' : ℕ} [NeZero (2 * M')] (F : Fin (2 * M') → ℤ) :
    ∑ j : Fin (2 * M'), F j =
      (∑ j ∈ Finset.univ.filter (fun j : Fin (2 * M') => Even j.val), F j) +
        ∑ j ∈ Finset.univ.filter (fun j : Fin (2 * M') => Odd j.val), F j := by
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun j : Fin (2 * M') => Even j.val) F]
  congr 1
  apply Finset.sum_congr _ (fun _ _ => rfl)
  ext j
  simp [Nat.not_even_iff_odd]

/-- The block-pair correlation decomposition: for a period-`2 * M' * L` sequence assembled from
two length-`L` words alternated by block and scaled by `±1` block signs, the cyclic correlation at
a lag inside the block splits into a within-block term (an average of the two words' aperiodic
correlations) and a boundary term (the block-transition sign sums against the cross-tail terms). -/
theorem cyclicCorr_blockSeq {L : ℕ} [NeZero L] {m M' : ℕ} [NeZero m] (hm : m = 2 * M')
    (u v : Fin L → ℤ) (ε : Fin m → ℤ) (hε : ∀ j, ε j * ε j = 1)
    {d k : ℕ} (_hd1 : 1 ≤ d) (hdk : d ≤ k) (hkL : k < L) :
    cyclicCorr (blockSeq u v ε) d =
      (M' : ℤ) * (aperiodicCorr u d + aperiodicCorr v d) +
        (∑ j ∈ Finset.univ.filter (fun j : Fin m => Even j.val), ε j * ε (j + 1)) *
          crossTail u v d +
        (∑ j ∈ Finset.univ.filter (fun j : Fin m => Odd j.val), ε j * ε (j + 1)) *
          crossTail v u d := by
  subst hm
  have hd : d ≤ L := by omega
  have : NeZero M' := ⟨fun h => (NeZero.ne (2 * M')) (by rw [h, mul_zero])⟩
  unfold cyclicCorr
  rw [sum_combine]
  simp_rw [inner_sum_eq u v ε hε _ d hd]
  rw [sum_even_add_odd, sum_filter_even, sum_filter_odd,
    sum_filter_even (fun j : Fin (2 * M') => ε j * ε (j + 1)),
    sum_filter_odd (fun j : Fin (2 * M') => ε j * ε (j + 1))]
  have heven : ∀ i : Fin M', ε (evenIdx i) * ε (evenIdx i + 1) = ε (evenIdx i) * ε (oddIdx i) := by
    intro i; rw [← nextBlock_eq_add_one, nextBlock_evenIdx]
  have hodd : ∀ i : Fin M', ε (oddIdx i) * ε (oddIdx i + 1)
      = ε (oddIdx i) * ε (nextBlock (oddIdx i)) := by
    intro i; rw [← nextBlock_eq_add_one]
  simp_rw [heven, hodd]
  have hwe : ∀ i : Fin M',
      aperiodicCorr (wordAt u v (evenIdx i)) d +
        ε (evenIdx i) * ε (nextBlock (evenIdx i)) *
          crossTail (wordAt u v (evenIdx i)) (wordAt u v (nextBlock (evenIdx i))) d
        = aperiodicCorr u d + ε (evenIdx i) * ε (oddIdx i) * crossTail u v d := by
    intro i; rw [wordAt_evenIdx, nextBlock_evenIdx, wordAt_oddIdx]
  have hwo : ∀ i : Fin M',
      aperiodicCorr (wordAt u v (oddIdx i)) d +
        ε (oddIdx i) * ε (nextBlock (oddIdx i)) *
          crossTail (wordAt u v (oddIdx i)) (wordAt u v (nextBlock (oddIdx i))) d
        = aperiodicCorr v d + ε (oddIdx i) * ε (nextBlock (oddIdx i)) * crossTail v u d := by
    intro i
    have hev : Even (nextBlock (oddIdx i)).val := by rw [nextBlock_oddIdx]; exact evenIdx_even _
    rw [wordAt_oddIdx, wordAt, if_pos hev]
  simp_rw [hwe, hwo]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul,
    Finset.sum_const, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    nsmul_eq_mul]
  ring

/-- The zone corollary: once both block-transition sign sums vanish and the two words' aperiodic
correlations cancel at a lag, the assembled sequence's cyclic correlation vanishes there too. -/
theorem cyclicCorr_blockSeq_zone {L : ℕ} [NeZero L] {m M' : ℕ} [NeZero m] (hm : m = 2 * M')
    (u v : Fin L → ℤ) (ε : Fin m → ℤ) (hε : ∀ j, ε j * ε j = 1)
    {d k : ℕ} (hd1 : 1 ≤ d) (hdk : d ≤ k) (hkL : k < L)
    (hzero : aperiodicCorr u d + aperiodicCorr v d = 0)
    (heven0 : ∑ j ∈ Finset.univ.filter (fun j : Fin m => Even j.val), ε j * ε (j + 1) = 0)
    (hodd0 : ∑ j ∈ Finset.univ.filter (fun j : Fin m => Odd j.val), ε j * ε (j + 1) = 0) :
    cyclicCorr (blockSeq u v ε) d = 0 := by
  rw [cyclicCorr_blockSeq hm u v ε hε hd1 hdk hkL, hzero, heven0, hodd0]
  ring

/-- The spike corollary: under the same block-transition balance, the cyclic correlation at the
band's own top lag `k` is exactly `M'` times the two words' combined aperiodic correlation. -/
theorem cyclicCorr_blockSeq_spike {L : ℕ} [NeZero L] {m M' : ℕ} [NeZero m] (hm : m = 2 * M')
    (u v : Fin L → ℤ) (ε : Fin m → ℤ) (hε : ∀ j, ε j * ε j = 1)
    {k : ℕ} (hk1 : 1 ≤ k) (hkL : k < L)
    (heven0 : ∑ j ∈ Finset.univ.filter (fun j : Fin m => Even j.val), ε j * ε (j + 1) = 0)
    (hodd0 : ∑ j ∈ Finset.univ.filter (fun j : Fin m => Odd j.val), ε j * ε (j + 1) = 0) :
    cyclicCorr (blockSeq u v ε) k = (M' : ℤ) * (aperiodicCorr u k + aperiodicCorr v k) := by
  rw [cyclicCorr_blockSeq hm u v ε hε hk1 (le_refl k) hkL, heven0, hodd0]
  ring

/-! ## The deviation envelope -/

private lemma sum_range_natCast_eq_univ {N : ℕ} [NeZero N] (g : ZMod N → ℤ) :
    ∑ i ∈ Finset.range N, g ((i : ℕ) : ZMod N) = ∑ x : ZMod N, g x := by
  rw [← Fin.sum_univ_eq_sum_range (fun i => g ((i : ℕ) : ZMod N)) N]
  apply Finset.sum_nbij' (fun i : Fin N => ((i.val : ℕ) : ZMod N))
    (fun x : ZMod N => (⟨x.val, ZMod.val_lt x⟩ : Fin N))
  · intros; exact Finset.mem_univ _
  · intros; exact Finset.mem_univ _
  · intro i _
    apply Fin.ext
    change ((i.val : ℕ) : ZMod N).val = i.val
    exact ZMod.val_cast_of_lt i.isLt
  · intro x _
    exact ZMod.natCast_rightInverse x
  · intro i _; rfl

private lemma sum_range_shift_natCast_eq_univ {N : ℕ} [NeZero N] (T : ℕ) (g : ZMod N → ℤ) :
    ∑ i ∈ Finset.range N, g (((T + i : ℕ) : ZMod N)) = ∑ x : ZMod N, g x := by
  have h1 : ∀ i : ℕ, ((T + i : ℕ) : ZMod N) = (T : ZMod N) + (i : ZMod N) := by
    intro i; push_cast; ring
  simp_rw [h1]
  rw [sum_range_natCast_eq_univ (fun x => g ((T : ZMod N) + x)),
    ← Equiv.sum_comp (Equiv.addLeft (T : ZMod N)) g]
  simp [Equiv.coe_addLeft]

/-- The `T`-term prefix of the ℕ-indexed lag-`d` cyclic query: the same sum `cyclicCorr` takes over
the whole period, truncated to its first `T` terms. -/
def cyclicCorrPrefix {N : ℕ} [NeZero N] (x : ZMod N → ℤ) (d T : ℕ) : ℤ :=
  ∑ t ∈ Finset.range T, x (t : ZMod N) * x ((t : ZMod N) + d)

/-- **Exact periodicity**: one further whole period beyond `T` adds exactly the full-period sum
`cyclicCorr`, since a full period's worth of the ℕ-indexed reading covers every residue once. -/
theorem cyclicCorrPrefix_add_period {N : ℕ} [NeZero N] (x : ZMod N → ℤ) (d T : ℕ) :
    cyclicCorrPrefix x d (T + N) = cyclicCorrPrefix x d T + cyclicCorr x d := by
  unfold cyclicCorrPrefix cyclicCorr
  rw [Finset.sum_range_add]
  congr 1
  exact sum_range_shift_natCast_eq_univ T (fun r => x r * x (r + d))

/-- The length-`n` cyclic window starting at ℕ-phase `p`. -/
def cyclicCorrWindow {N : ℕ} [NeZero N] (x : ZMod N → ℤ) (d p n : ℕ) : ℤ :=
  ∑ i ∈ Finset.range n, x (((p + i : ℕ) : ZMod N)) * x (((p + i : ℕ) : ZMod N) + d)

/-- A window is a difference of two prefixes. -/
theorem cyclicCorrWindow_eq_sub {N : ℕ} [NeZero N] (x : ZMod N → ℤ) (d p n : ℕ) :
    cyclicCorrWindow x d p n = cyclicCorrPrefix x d (p + n) - cyclicCorrPrefix x d p := by
  unfold cyclicCorrWindow cyclicCorrPrefix
  rw [Finset.sum_range_add]
  ring

/-- **Reduction mod the period**: any prefix length decomposes into whole periods (each
contributing the full-period sum exactly) plus a within-period remainder. -/
theorem cyclicCorrPrefix_mod_period {N : ℕ} [NeZero N] (x : ZMod N → ℤ) (d : ℕ) (T : ℕ) :
    cyclicCorrPrefix x d T =
      ((T / N : ℕ) : ℤ) * cyclicCorr x d + cyclicCorrPrefix x d (T % N) := by
  induction T using Nat.strong_induction_on with
  | _ T ih =>
    by_cases hTN : T < N
    · rw [Nat.div_eq_of_lt hTN, Nat.mod_eq_of_lt hTN]
      simp
    · have hNpos := NeZero.pos N
      have hlt : T - N < T := by omega
      have heqT : T - N + N = T := by omega
      have hstep : cyclicCorrPrefix x d T = cyclicCorrPrefix x d (T - N) + cyclicCorr x d := by
        have hp := cyclicCorrPrefix_add_period x d (T - N)
        rwa [heqT] at hp
      have hq : T / N = (T - N) / N + 1 := by
        conv_lhs => rw [← heqT]
        rw [Nat.add_div_right _ (NeZero.pos N)]
      have hr : T % N = (T - N) % N := by
        conv_lhs => rw [← heqT]
        rw [Nat.add_mod_right]
      rw [hstep, ih (T - N) hlt, hq, hr]
      push_cast
      ring

/-! ## The single-site deviation envelope -/

/-- The `T`-term ℕ-indexed prefix of a single-site query on a period-`N` sequence: the lag-free
analogue of `cyclicCorrPrefix`, without the correlation product. -/
private def singlePrefix {N : ℕ} [NeZero N] (x : ZMod N → ℤ) (T : ℕ) : ℤ :=
  ∑ t ∈ Finset.range T, x (t : ZMod N)

/-- **Exact periodicity**, the single-site analogue of `cyclicCorrPrefix_add_period`: one further
whole period beyond `T` adds exactly the full-period sum. -/
private theorem singlePrefix_add_period {N : ℕ} [NeZero N] (x : ZMod N → ℤ) (T : ℕ) :
    singlePrefix x (T + N) = singlePrefix x T + ∑ t : ZMod N, x t := by
  unfold singlePrefix
  rw [Finset.sum_range_add]
  congr 1
  exact sum_range_shift_natCast_eq_univ T x

/-- The length-`n` single-site cyclic window starting at ℕ-phase `p`, the lag-free analogue of
`cyclicCorrWindow`. -/
def singleWindow {N : ℕ} [NeZero N] (x : ZMod N → ℤ) (p n : ℕ) : ℤ :=
  ∑ i ∈ Finset.range n, x (((p + i : ℕ) : ZMod N))

/-- A single-site window is a difference of two prefixes. -/
private theorem singleWindow_eq_sub {N : ℕ} [NeZero N] (x : ZMod N → ℤ) (p n : ℕ) :
    singleWindow x p n = singlePrefix x (p + n) - singlePrefix x p := by
  unfold singleWindow singlePrefix
  rw [Finset.sum_range_add]
  ring

/-- **Reduction mod the period**, the single-site analogue of `cyclicCorrPrefix_mod_period`. -/
private theorem singlePrefix_mod_period {N : ℕ} [NeZero N] (x : ZMod N → ℤ) (T : ℕ) :
    singlePrefix x T =
      ((T / N : ℕ) : ℤ) * (∑ t : ZMod N, x t) + singlePrefix x (T % N) := by
  induction T using Nat.strong_induction_on with
  | _ T ih =>
    by_cases hTN : T < N
    · rw [Nat.div_eq_of_lt hTN, Nat.mod_eq_of_lt hTN]
      simp
    · have hNpos := NeZero.pos N
      have hlt : T - N < T := by omega
      have heqT : T - N + N = T := by omega
      have hstep : singlePrefix x T = singlePrefix x (T - N) + ∑ t : ZMod N, x t := by
        have hp := singlePrefix_add_period x (T - N)
        rwa [heqT] at hp
      have hq : T / N = (T - N) / N + 1 := by
        conv_lhs => rw [← heqT]
        rw [Nat.add_div_right _ (NeZero.pos N)]
      have hr : T % N = (T - N) % N := by
        conv_lhs => rw [← heqT]
        rw [Nat.add_mod_right]
      rw [hstep, ih (T - N) hlt, hq, hr]
      push_cast
      ring

/-- A full-period single-site prefix is exactly the `Fintype`-indexed full sum. -/
private theorem singlePrefix_eq_full_sum {N : ℕ} [NeZero N] (x : ZMod N → ℤ) :
    singlePrefix x N = ∑ t : ZMod N, x t := by
  unfold singlePrefix
  exact sum_range_natCast_eq_univ x

/-- The word carried by ℕ-indexed block `j`, depending only on its parity: `u` on even blocks, `v`
on odd blocks. -/
private def wordAtNat {L : ℕ} (u v : Fin L → ℤ) (j : ℕ) : Fin L → ℤ := if Even j then u else v

/-- The sign carried by ℕ-indexed block `j`, read through the cyclic supply by reduction mod `m`. -/
private def signAtNat {m : ℕ} [NeZero m] (ε : Fin m → ℤ) (j : ℕ) : ℤ :=
  ε ⟨j % m, Nat.mod_lt _ (NeZero.pos m)⟩

private lemma wordAt_eq_wordAtNat {m L : ℕ} (u v : Fin L → ℤ) (j : Fin m) :
    wordAt u v j = wordAtNat u v j.val := rfl

private lemma signAtNat_val_eq {m : ℕ} [NeZero m] (ε : Fin m → ℤ) (j : Fin m) :
    signAtNat ε j.val = ε j := by
  unfold signAtNat
  congr 1
  apply Fin.ext
  exact Nat.mod_eq_of_lt j.isLt

private lemma sign_nextBlock_eq_signAtNat_succ {m : ℕ} [NeZero m] (ε : Fin m → ℤ) (j : Fin m) :
    ε (nextBlock j) = signAtNat ε (j.val + 1) := rfl

private lemma wordAt_nextBlock_eq_wordAtNat_succ {m L : ℕ} [NeZero m] (hm2 : Even m)
    (u v : Fin L → ℤ) (j : Fin m) :
    wordAt u v (nextBlock j) = wordAtNat u v (j.val + 1) := by
  unfold wordAt wordAtNat
  by_cases hwrap : j.val + 1 < m
  · have hv : (nextBlock j).val = j.val + 1 := Nat.mod_eq_of_lt hwrap
    rw [hv]
  · have hjlt := j.isLt
    have hjm : j.val + 1 = m := by omega
    have hv : (nextBlock j).val = 0 := by
      change (j.val + 1) % m = 0
      rw [hjm]; exact Nat.mod_self m
    rw [hv, hjm]
    simp [hm2]

private lemma blockContribNat_eq {m L : ℕ} [NeZero m] [NeZero L] (hm2 : Even m)
    (u v : Fin L → ℤ) (ε : Fin m → ℤ) (hε : ∀ j, ε j * ε j = 1) (d : ℕ) (hd : d ≤ L)
    (J : ℕ) (hJ : J < m) :
    ∑ p : Fin L, blockSeq u v ε (combine (⟨J, hJ⟩ : Fin m) p) *
        blockSeq u v ε (combine (⟨J, hJ⟩ : Fin m) p + (d : ZMod (m * L))) =
      aperiodicCorr (wordAtNat u v J) d +
        signAtNat ε J * signAtNat ε (J + 1) *
          crossTail (wordAtNat u v J) (wordAtNat u v (J + 1)) d := by
  rw [inner_sum_eq u v ε hε ⟨J, hJ⟩ d hd, wordAt_eq_wordAtNat,
    wordAt_nextBlock_eq_wordAtNat_succ hm2, sign_nextBlock_eq_signAtNat_succ ε,
    ← signAtNat_val_eq ε (⟨J, hJ⟩ : Fin m)]

private lemma prefixTerm_eq_combine {m L : ℕ} [NeZero m] [NeZero L] (u v : Fin L → ℤ)
    (ε : Fin m → ℤ) (d n : ℕ) (hn : n < m) (p : Fin L) :
    blockSeq u v ε ((n * L + p.val : ℕ) : ZMod (m * L)) *
        blockSeq u v ε (((n * L + p.val : ℕ) : ZMod (m * L)) + (d : ZMod (m * L))) =
      blockSeq u v ε (combine (⟨n, hn⟩ : Fin m) p) *
        blockSeq u v ε (combine (⟨n, hn⟩ : Fin m) p + (d : ZMod (m * L))) := by
  have hce : ((n * L + p.val : ℕ) : ZMod (m * L)) = combine (⟨n, hn⟩ : Fin m) p := by
    unfold combine
    congr 1
    ring
  rw [hce]

/-- **The exact block decomposition of a prefix**: the prefix over the first `J` complete blocks
splits into the two words' aperiodic correlations, weighted by how many blocks of each parity
occur, plus the running signed sum of block-transition products against each word's cross-tail. -/
private lemma cyclicCorrPrefix_blockSeq_blocks {L : ℕ} [NeZero L] {m : ℕ} [NeZero m]
    (hm2 : Even m) (u v : Fin L → ℤ) (ε : Fin m → ℤ) (hε : ∀ j, ε j * ε j = 1)
    {d : ℕ} (hdL : d ≤ L) :
    ∀ J, J ≤ m → cyclicCorrPrefix (blockSeq u v ε) d (J * L) =
      (((J + 1) / 2 : ℕ) : ℤ) * aperiodicCorr u d + ((J / 2 : ℕ) : ℤ) * aperiodicCorr v d +
        (∑ j ∈ Finset.range J, if Even j then signAtNat ε j * signAtNat ε (j + 1) else 0) *
          crossTail u v d +
        (∑ j ∈ Finset.range J, if Odd j then signAtNat ε j * signAtNat ε (j + 1) else 0) *
          crossTail v u d := by
  intro J
  induction J with
  | zero => intro _; simp [cyclicCorrPrefix]
  | succ n ih =>
    intro hJm
    have hn : n ≤ m := by omega
    have hnm : n < m := by omega
    have heq := ih hn
    have hstep : cyclicCorrPrefix (blockSeq u v ε) d ((n + 1) * L) =
        cyclicCorrPrefix (blockSeq u v ε) d (n * L) +
          (aperiodicCorr (wordAtNat u v n) d +
            signAtNat ε n * signAtNat ε (n + 1) *
              crossTail (wordAtNat u v n) (wordAtNat u v (n + 1)) d) := by
      unfold cyclicCorrPrefix
      rw [show (n + 1) * L = n * L + L from by ring, Finset.sum_range_add]
      congr 1
      rw [← blockContribNat_eq hm2 u v ε hε d hdL n hnm,
        ← Fin.sum_univ_eq_sum_range
          (fun p => blockSeq u v ε ((n * L + p : ℕ) : ZMod (m * L)) *
            blockSeq u v ε (((n * L + p : ℕ) : ZMod (m * L)) + (d : ZMod (m * L)))) L]
      exact Finset.sum_congr rfl (fun p _ => prefixTerm_eq_combine u v ε d n hnm p)
    rw [hstep, heq]
    rcases Nat.even_or_odd n with hen | hon
    · have hmod : n % 2 = 0 := Nat.even_iff.mp hen
      have hcnt1 : (n + 1 + 1) / 2 = (n + 1) / 2 + 1 := by omega
      have hcnt2 : (n + 1) / 2 = n / 2 := by omega
      rw [Finset.sum_range_succ, Finset.sum_range_succ, if_pos hen,
        if_neg (by rw [Nat.odd_iff]; omega : ¬ Odd n)]
      have hwe : wordAtNat u v n = u := if_pos hen
      have hwo : wordAtNat u v (n + 1) = v := by
        unfold wordAtNat; rw [if_neg (by rw [Nat.even_iff]; omega : ¬ Even (n + 1))]
      rw [hwe, hwo, hcnt1, hcnt2]
      push_cast
      ring
    · have hmod : n % 2 = 1 := Nat.odd_iff.mp hon
      have hcnt1 : (n + 1 + 1) / 2 = (n + 1) / 2 := by omega
      have hcnt2 : (n + 1) / 2 = n / 2 + 1 := by omega
      rw [Finset.sum_range_succ, Finset.sum_range_succ,
        if_neg (by rw [Nat.even_iff]; omega : ¬ Even n), if_pos hon]
      have hwo : wordAtNat u v n = v := by
        unfold wordAtNat; rw [if_neg (by rw [Nat.even_iff]; omega : ¬ Even n)]
      have hwe : wordAtNat u v (n + 1) = u := by
        unfold wordAtNat; rw [if_pos (by rw [Nat.even_iff]; omega : Even (n + 1))]
      rw [hwo, hwe, hcnt1, hcnt2]
      push_cast
      ring

private lemma blockSeq_shift_eq {m L : ℕ} [NeZero m] [NeZero L] (u v : Fin L → ℤ) (ε : Fin m → ℤ)
    (hε : ∀ j, ε j * ε j = 1) (j : Fin m) (p : Fin L) (d : ℕ) (hd : d ≤ L) :
    blockSeq u v ε (combine j p) * blockSeq u v ε (combine j p + (d : ZMod (m * L))) =
      (if h : p.val + d < L then wordAt u v j p * wordAt u v j ⟨p.val + d, h⟩ else 0) +
        (if h : L ≤ p.val + d then
            ε j * ε (nextBlock j) *
              (wordAt u v j p * wordAt u v (nextBlock j) ⟨p.val + d - L, by omega⟩)
          else 0) := by
  rw [blockSeq_combine]
  by_cases h : p.val + d < L
  · rw [shift_inBlock j p d h, blockSeq_combine, dif_pos h,
      dif_neg (show ¬ (L ≤ p.val + d) by omega)]
    have hring : ε j * wordAt u v j p * (ε j * wordAt u v j ⟨p.val + d, h⟩) =
        ε j * ε j * (wordAt u v j p * wordAt u v j ⟨p.val + d, h⟩) := by ring
    rw [hring, hε j, one_mul, add_zero]
  · rw [shift_crossBlock j p d hd (by omega), blockSeq_combine, dif_neg h,
      dif_pos (show L ≤ p.val + d by omega)]
    rw [zero_add]
    ring

/-- The block-local raw remainder over the first `r` positions of a single block: the same
per-position query the full block decomposition sums, truncated short of the block boundary. -/
private def blockRemainder {L : ℕ} [NeZero L] (w w' : Fin L → ℤ) (η : ℤ) (d r : ℕ) : ℤ :=
  ∑ i ∈ Finset.range r, if h : i < L then
      (if h2 : i + d < L then w ⟨i, h⟩ * w ⟨i + d, h2⟩
       else η * (w ⟨i, h⟩ * w' ⟨(i + d - L) % L, Nat.mod_lt _ (NeZero.pos L)⟩))
    else 0

private lemma blockRemainder_eq {m L : ℕ} [NeZero m] [NeZero L] (hm2 : Even m)
    (u v : Fin L → ℤ) (ε : Fin m → ℤ) (hε : ∀ j, ε j * ε j = 1) (d : ℕ) (hd : d ≤ L)
    (J : ℕ) (hJ : J < m) (r : ℕ) (hr : r ≤ L) :
    ∑ i ∈ Finset.range r, blockSeq u v ε ((J * L + i : ℕ) : ZMod (m * L)) *
        blockSeq u v ε (((J * L + i : ℕ) : ZMod (m * L)) + (d : ZMod (m * L))) =
      blockRemainder (wordAtNat u v J) (wordAtNat u v (J + 1))
        (signAtNat ε J * signAtNat ε (J + 1)) d r := by
  unfold blockRemainder
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mem_range] at hi
  have hiL : i < L := by omega
  rw [dif_pos hiL]
  have hce : ((J * L + i : ℕ) : ZMod (m * L)) = combine (⟨J, hJ⟩ : Fin m) ⟨i, hiL⟩ := by
    unfold combine; congr 1; ring
  rw [hce, blockSeq_shift_eq u v ε hε ⟨J, hJ⟩ ⟨i, hiL⟩ d hd]
  by_cases h2 : i + d < L
  · rw [dif_pos h2, dif_pos h2, dif_neg (show ¬ (L ≤ i + d) by omega), add_zero,
      wordAt_eq_wordAtNat]
  · have hmodeq : (i + d - L) % L = i + d - L := Nat.mod_eq_of_lt (by omega)
    rw [dif_neg h2, dif_neg h2, dif_pos (show L ≤ i + d by omega), zero_add,
      wordAt_eq_wordAtNat, wordAt_nextBlock_eq_wordAtNat_succ hm2,
      sign_nextBlock_eq_signAtNat_succ ε, ← signAtNat_val_eq ε (⟨J, hJ⟩ : Fin m)]
    simp only [hmodeq]

private lemma abs_le_one_of_sq_eq_one {a : ℤ} (h : a * a = 1) : |a| ≤ 1 := by
  have hz : (a - 1) * (a + 1) = 0 := by nlinarith
  rcases mul_eq_zero.mp hz with h1 | h1
  · have : a = 1 := by omega
    simp [this]
  · have : a = -1 := by omega
    simp [this]

private lemma abs_sum_fin_le {L : ℕ} (f : Fin L → ℤ) (h : ∀ i, |f i| ≤ 1) :
    |∑ i : Fin L, f i| ≤ (L : ℤ) := by
  calc |∑ i : Fin L, f i| ≤ ∑ i : Fin L, |f i| := Finset.abs_sum_le_sum_abs f Finset.univ
    _ ≤ ∑ _i : Fin L, (1 : ℤ) := Finset.sum_le_sum (fun i _ => h i)
    _ = L := by simp

/-- **Every value of the assembled sequence is bounded by `1`** in absolute value, given `±1`
block signs and `±1`-bounded words. -/
private lemma blockSeq_abs_le_one {m L : ℕ} [NeZero m] [NeZero L] (u v : Fin L → ℤ)
    (ε : Fin m → ℤ) (hε : ∀ j, ε j * ε j = 1) (hu1 : ∀ p, |u p| ≤ 1) (hv1 : ∀ p, |v p| ≤ 1)
    (t : ZMod (m * L)) : |blockSeq u v ε t| ≤ 1 := by
  unfold blockSeq
  split_ifs
  · rw [abs_mul]
    calc |ε (blockIdx t)| * |u (blockOff t)| ≤ 1 * 1 :=
          mul_le_mul (abs_le_one_of_sq_eq_one (hε _)) (hu1 _) (abs_nonneg _) (by norm_num)
      _ = 1 := by norm_num
  · rw [abs_mul]
    calc |ε (blockIdx t)| * |v (blockOff t)| ≤ 1 * 1 :=
          mul_le_mul (abs_le_one_of_sq_eq_one (hε _)) (hv1 _) (abs_nonneg _) (by norm_num)
      _ = 1 := by norm_num

private lemma aperiodicCorr_abs_le {L : ℕ} (w : Fin L → ℤ) (hw1 : ∀ p, |w p| ≤ 1) (d : ℕ) :
    |aperiodicCorr w d| ≤ (L : ℤ) := by
  unfold aperiodicCorr
  apply abs_sum_fin_le
  intro p
  split_ifs with h
  · rw [abs_mul]
    calc |w p| * |w ⟨p.val + d, h⟩| ≤ 1 * 1 :=
          mul_le_mul (hw1 _) (hw1 _) (abs_nonneg _) (by norm_num)
      _ = 1 := by norm_num
  · simp

private lemma crossTail_abs_le {L : ℕ} (w w' : Fin L → ℤ) (hw1 : ∀ p, |w p| ≤ 1)
    (hw'1 : ∀ p, |w' p| ≤ 1) (d : ℕ) : |crossTail w w' d| ≤ (L : ℤ) := by
  unfold crossTail
  apply abs_sum_fin_le
  intro i
  split_ifs with h
  · rw [abs_mul]
    calc |w ⟨L - d + i.val, by omega⟩| * |w' i| ≤ 1 * 1 :=
          mul_le_mul (hw1 _) (hw'1 _) (abs_nonneg _) (by norm_num)
      _ = 1 := by norm_num
  · simp

private lemma sum_range_ite_lt (L d : ℕ) (hd : d ≤ L) :
    (∑ i ∈ Finset.range L, if i < d then (1 : ℤ) else 0) = d := by
  rw [show L = d + (L - d) from by omega, Finset.sum_range_add]
  have h1 : (∑ i ∈ Finset.range d, if i < d then (1 : ℤ) else 0) =
      ∑ _i ∈ Finset.range d, (1 : ℤ) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mem_range] at hi
    rw [if_pos hi]
  have h2 : (∑ i ∈ Finset.range (L - d), if d + i < d then (1 : ℤ) else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    rw [if_neg (by omega)]
  rw [h1, h2, add_zero]
  simp

/-- **The cross-tail is bounded by the lag `d`** rather than the crudely-bounded `L`: only `d` of
its `L` summands can be nonzero. -/
private lemma crossTail_abs_le_d {L : ℕ} (w w' : Fin L → ℤ) (hw1 : ∀ p, |w p| ≤ 1)
    (hw'1 : ∀ p, |w' p| ≤ 1) (d : ℕ) (hd : d ≤ L) : |crossTail w w' d| ≤ (d : ℤ) := by
  unfold crossTail
  have hstep : |∑ i : Fin L, if h : i.val < d then w ⟨L - d + i.val, by omega⟩ * w' i else 0| ≤
      ∑ i : Fin L, if i.val < d then (1 : ℤ) else 0 := by
    calc |∑ i : Fin L, if h : i.val < d then w ⟨L - d + i.val, by omega⟩ * w' i else 0|
        ≤ ∑ i : Fin L, |if h : i.val < d then w ⟨L - d + i.val, by omega⟩ * w' i else 0| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i : Fin L, if i.val < d then (1 : ℤ) else 0 := by
          apply Finset.sum_le_sum
          intro i _
          split_ifs with h
          · rw [abs_mul]
            calc |w ⟨L - d + i.val, by omega⟩| * |w' i| ≤ 1 * 1 :=
                  mul_le_mul (hw1 _) (hw'1 _) (abs_nonneg _) (by norm_num)
              _ = 1 := by norm_num
          · simp
  have hcard : (∑ i : Fin L, if i.val < d then (1 : ℤ) else 0) = (d : ℤ) := by
    rw [Fin.sum_univ_eq_sum_range (fun i => if i < d then (1 : ℤ) else 0) L]
    exact sum_range_ite_lt L d hd
  rw [hcard] at hstep
  exact hstep

/-- **The zone prefix bound**: at a lag where the two words' aperiodic correlations cancel and the
block-transition sign sums stay within `P` at every prefix, every ℕ-indexed prefix of the
assembled sequence's lag-`d` query — not just the full period — deviates from zero by at most an
`L`-scaled constant that does not depend on the block count. -/
theorem cyclicCorrPrefix_blockSeq_zone {L : ℕ} [NeZero L] {m M' : ℕ} [NeZero m] (hm : m = 2 * M')
    (u v : Fin L → ℤ) (ε : Fin m → ℤ) (hε : ∀ j, ε j * ε j = 1)
    (hu1 : ∀ p, |u p| ≤ 1) (hv1 : ∀ p, |v p| ≤ 1)
    {d k : ℕ} (_hd1 : 1 ≤ d) (hdk : d ≤ k) (hkL : k < L)
    (hzero : aperiodicCorr u d + aperiodicCorr v d = 0) (P : ℤ)
    (hPeven : ∀ J, J ≤ m → |∑ j ∈ Finset.range J,
        if Even j then signAtNat ε j * signAtNat ε (j + 1) else 0| ≤ P)
    (hPodd : ∀ J, J ≤ m → |∑ j ∈ Finset.range J,
        if Odd j then signAtNat ε j * signAtNat ε (j + 1) else 0| ≤ P)
    (T : ℕ) (hT : T ≤ m * L) :
    |cyclicCorrPrefix (blockSeq u v ε) d T| ≤ (2 + 2 * P) * (L : ℤ) := by
  subst hm
  have hd : d ≤ L := by omega
  have : NeZero M' := ⟨fun h => (NeZero.ne (2 * M')) (by rw [h, mul_zero])⟩
  have hm2 : Even (2 * M') := ⟨M', by ring⟩
  set J := T / L with hJdef
  set r := T % L with hrdef
  have hde := Nat.div_add_mod T L
  have hTeq : J * L + r = T := by rw [hJdef, hrdef, mul_comm]; omega
  have hrL : r < L := Nat.mod_lt _ (NeZero.pos L)
  have hJm : J ≤ 2 * M' := by
    have hJLle : J * L ≤ (2 * M') * L := by omega
    exact Nat.le_of_mul_le_mul_right hJLle (NeZero.pos L)
  have hAJ := cyclicCorrPrefix_blockSeq_blocks hm2 u v ε hε hd J hJm
  have hb1 : |aperiodicCorr u d| ≤ (L : ℤ) := aperiodicCorr_abs_le u hu1 d
  have hb3 : |crossTail u v d| ≤ (L : ℤ) := crossTail_abs_le u v hu1 hv1 d
  have hb4 : |crossTail v u d| ≤ (L : ℤ) := crossTail_abs_le v u hv1 hu1 d
  have hb5 := hPeven J hJm
  have hb6 := hPodd J hJm
  have haperiodic : |(((J + 1) / 2 : ℕ) : ℤ) * aperiodicCorr u d +
      ((J / 2 : ℕ) : ℤ) * aperiodicCorr v d| ≤ (L : ℤ) := by
    rcases Nat.even_or_odd J with hJe | hJo
    · have hmod : J % 2 = 0 := Nat.even_iff.mp hJe
      have hc : (J + 1) / 2 = J / 2 := by omega
      have heq : ((J / 2 : ℕ) : ℤ) * aperiodicCorr u d + ((J / 2 : ℕ) : ℤ) * aperiodicCorr v d
          = ((J / 2 : ℕ) : ℤ) * (aperiodicCorr u d + aperiodicCorr v d) := by ring
      rw [hc, heq, hzero, mul_zero]
      simp
    · have hmod : J % 2 = 1 := Nat.odd_iff.mp hJo
      have hc : (J + 1) / 2 = J / 2 + 1 := by omega
      rw [hc, Nat.cast_add, Nat.cast_one]
      have heq : (((J / 2 : ℕ) : ℤ) + 1) * aperiodicCorr u d + ((J / 2 : ℕ) : ℤ) *
            aperiodicCorr v d
          = ((J / 2 : ℕ) : ℤ) * (aperiodicCorr u d + aperiodicCorr v d) + aperiodicCorr u d := by
        ring
      rw [heq, hzero, mul_zero, zero_add]
      exact hb1
  have hPnn : 0 ≤ P := (abs_nonneg _).trans hb5
  have hmain : |cyclicCorrPrefix (blockSeq u v ε) d (J * L)| ≤ (1 + 2 * P) * (L : ℤ) := by
    rw [hAJ]
    set B := (∑ j ∈ Finset.range J,
        if Even j then signAtNat ε j * signAtNat ε (j + 1) else 0) * crossTail u v d with hBdef
    set C := (∑ j ∈ Finset.range J,
        if Odd j then signAtNat ε j * signAtNat ε (j + 1) else 0) * crossTail v u d with hCdef
    have hBbound : |B| ≤ P * (L : ℤ) := by
      rw [hBdef, abs_mul]; exact mul_le_mul hb5 hb3 (abs_nonneg _) hPnn
    have hCbound : |C| ≤ P * (L : ℤ) := by
      rw [hCdef, abs_mul]; exact mul_le_mul hb6 hb4 (abs_nonneg _) hPnn
    have h1 := abs_add_le
      ((((J + 1) / 2 : ℕ) : ℤ) * aperiodicCorr u d + ((J / 2 : ℕ) : ℤ) * aperiodicCorr v d + B) C
    have h2 := abs_add_le
      ((((J + 1) / 2 : ℕ) : ℤ) * aperiodicCorr u d + ((J / 2 : ℕ) : ℤ) * aperiodicCorr v d) B
    linarith [haperiodic, hBbound, hCbound, h1, h2]
  have hremBound : |∑ i ∈ Finset.range r,
      blockSeq u v ε (((J * L + i : ℕ) : ZMod ((2 * M') * L))) *
        blockSeq u v ε (((J * L + i : ℕ) : ZMod ((2 * M') * L)) + (d : ZMod ((2 * M') * L)))| ≤
      (L : ℤ) := by
    have hstep : |∑ i ∈ Finset.range r, blockSeq u v ε (((J * L + i : ℕ) : ZMod ((2 * M') * L))) *
          blockSeq u v ε (((J * L + i : ℕ) : ZMod ((2 * M') * L)) + (d : ZMod ((2 * M') * L)))| ≤
        ∑ i ∈ Finset.range r, |blockSeq u v ε (((J * L + i : ℕ) : ZMod ((2 * M') * L))) *
            blockSeq u v ε (((J * L + i : ℕ) : ZMod ((2 * M') * L)) + (d : ZMod ((2 * M') * L)))| :=
      Finset.abs_sum_le_sum_abs _ _
    have hterm : ∑ i ∈ Finset.range r,
        |blockSeq u v ε (((J * L + i : ℕ) : ZMod ((2 * M') * L))) *
            blockSeq u v ε (((J * L + i : ℕ) : ZMod ((2 * M') * L)) + (d : ZMod ((2 * M') * L)))|
          ≤ ∑ _i ∈ Finset.range r, (1 : ℤ) := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul]
      have := mul_le_mul (blockSeq_abs_le_one u v ε hε hu1 hv1
          (((J * L + i : ℕ) : ZMod ((2 * M') * L))))
        (blockSeq_abs_le_one u v ε hε hu1 hv1
          (((J * L + i : ℕ) : ZMod ((2 * M') * L)) + (d : ZMod ((2 * M') * L))))
        (abs_nonneg _) (by norm_num)
      linarith
    have hsum1 : ∑ _i ∈ Finset.range r, (1 : ℤ) = (r : ℤ) := by simp
    have hrLcast : (r : ℤ) ≤ (L : ℤ) := by exact_mod_cast hrL.le
    linarith
  have hrem : cyclicCorrPrefix (blockSeq u v ε) d T =
      cyclicCorrPrefix (blockSeq u v ε) d (J * L) +
        ∑ i ∈ Finset.range r, blockSeq u v ε (((J * L + i : ℕ) : ZMod ((2 * M') * L))) *
          blockSeq u v ε (((J * L + i : ℕ) : ZMod ((2 * M') * L)) + (d : ZMod ((2 * M') * L))) := by
    rw [← hTeq]
    exact Finset.sum_range_add _ (J * L) r
  rw [hrem]
  have h3 := abs_add_le (cyclicCorrPrefix (blockSeq u v ε) d (J * L))
    (∑ i ∈ Finset.range r, blockSeq u v ε (((J * L + i : ℕ) : ZMod ((2 * M') * L))) *
      blockSeq u v ε (((J * L + i : ℕ) : ZMod ((2 * M') * L)) + (d : ZMod ((2 * M') * L))))
  linarith

/-- **The spike prefix bound**: with the two words' aperiodic correlations equal at the top lag,
every ℕ-indexed prefix of the assembled sequence's query there tracks its exact linear trend
`T * s / (2 * L)` to within an `L`-scaled constant, once both the transition sums and the
within-block deviation from that trend stay controlled uniformly in the prefix length. -/
theorem cyclicCorrPrefix_blockSeq_spike {L : ℕ} [NeZero L] {m M' : ℕ} [NeZero m] (hm : m = 2 * M')
    (u v : Fin L → ℤ) (ε : Fin m → ℤ) (hε : ∀ j, ε j * ε j = 1)
    (hu1 : ∀ p, |u p| ≤ 1) (hv1 : ∀ p, |v p| ≤ 1)
    {k : ℕ} (_hk1 : 1 ≤ k) (hkL : k < L)
    (huv : aperiodicCorr u k = aperiodicCorr v k) (P : ℤ)
    (hPeven : ∀ J, J ≤ m → |∑ j ∈ Finset.range J,
        if Even j then signAtNat ε j * signAtNat ε (j + 1) else 0| ≤ P)
    (hPodd : ∀ J, J ≤ m → |∑ j ∈ Finset.range J,
        if Odd j then signAtNat ε j * signAtNat ε (j + 1) else 0| ≤ P)
    (Q : ℤ)
    (hRemU : ∀ η : ℤ, η * η = 1 → ∀ r, r ≤ L →
      |2 * (L : ℤ) * blockRemainder u v η k r -
          (r : ℤ) * (aperiodicCorr u k + aperiodicCorr v k)| ≤ Q * (L : ℤ))
    (hRemV : ∀ η : ℤ, η * η = 1 → ∀ r, r ≤ L →
      |2 * (L : ℤ) * blockRemainder v u η k r -
          (r : ℤ) * (aperiodicCorr u k + aperiodicCorr v k)| ≤ Q * (L : ℤ))
    (T : ℕ) (hT : T ≤ m * L) :
    |2 * (L : ℤ) * cyclicCorrPrefix (blockSeq u v ε) k T -
        (T : ℤ) * (aperiodicCorr u k + aperiodicCorr v k)| ≤
      (4 * P * (k : ℤ) + Q) * (L : ℤ) := by
  subst hm
  have hd : k ≤ L := by omega
  have : NeZero M' := ⟨fun h => (NeZero.ne (2 * M')) (by rw [h, mul_zero])⟩
  have hm2 : Even (2 * M') := ⟨M', by ring⟩
  set J := T / L with hJdef
  set r := T % L with hrdef
  have hde := Nat.div_add_mod T L
  have hTeq : J * L + r = T := by rw [hJdef, hrdef, mul_comm]; omega
  have hrL : r < L := Nat.mod_lt _ (NeZero.pos L)
  have hJm : J ≤ 2 * M' := by
    have hJLle : J * L ≤ (2 * M') * L := by omega
    exact Nat.le_of_mul_le_mul_right hJLle (NeZero.pos L)
  have hAJ := cyclicCorrPrefix_blockSeq_blocks hm2 u v ε hε hd J hJm
  have hb5 := hPeven J hJm
  have hb6 := hPodd J hJm
  have hPnn : 0 ≤ P := (abs_nonneg _).trans hb5
  have hb3 : |crossTail u v k| ≤ (k : ℤ) := crossTail_abs_le_d u v hu1 hv1 k hd
  have hb4 : |crossTail v u k| ≤ (k : ℤ) := crossTail_abs_le_d v u hv1 hu1 k hd
  have hcountsum : (J + 1) / 2 + J / 2 = J := by omega
  have hcast : (((J + 1) / 2 : ℕ) : ℤ) + ((J / 2 : ℕ) : ℤ) = (J : ℤ) := by
    exact_mod_cast hcountsum
  have haperiodic_eq : (((J + 1) / 2 : ℕ) : ℤ) * aperiodicCorr u k +
      ((J / 2 : ℕ) : ℤ) * aperiodicCorr v k = (J : ℤ) * aperiodicCorr u k := by
    rw [← huv]
    calc (((J + 1) / 2 : ℕ) : ℤ) * aperiodicCorr u k + ((J / 2 : ℕ) : ℤ) * aperiodicCorr u k
        = ((((J + 1) / 2 : ℕ) : ℤ) + ((J / 2 : ℕ) : ℤ)) * aperiodicCorr u k := by ring
      _ = (J : ℤ) * aperiodicCorr u k := by rw [hcast]
  set B := (∑ j ∈ Finset.range J,
      if Even j then signAtNat ε j * signAtNat ε (j + 1) else 0) * crossTail u v k with hBdef
  set C := (∑ j ∈ Finset.range J,
      if Odd j then signAtNat ε j * signAtNat ε (j + 1) else 0) * crossTail v u k with hCdef
  have hBbound : |B| ≤ P * (k : ℤ) := by
    rw [hBdef, abs_mul]; exact mul_le_mul hb5 hb3 (abs_nonneg _) hPnn
  have hCbound : |C| ≤ P * (k : ℤ) := by
    rw [hCdef, abs_mul]; exact mul_le_mul hb6 hb4 (abs_nonneg _) hPnn
  have hmain_eq : 2 * (L : ℤ) * cyclicCorrPrefix (blockSeq u v ε) k (J * L) -
      ((J : ℤ) * (L : ℤ)) * (aperiodicCorr u k + aperiodicCorr v k) = 2 * (L : ℤ) * (B + C) := by
    rw [hAJ, ← huv]
    have hthis : (((J + 1) / 2 : ℕ) : ℤ) * aperiodicCorr u k +
        ((J / 2 : ℕ) : ℤ) * aperiodicCorr u k = (J : ℤ) * aperiodicCorr u k := by
      rw [← add_mul, hcast]
    linear_combination 2 * (L : ℤ) * hthis
  have hmain_bound : |2 * (L : ℤ) * cyclicCorrPrefix (blockSeq u v ε) k (J * L) -
      ((J : ℤ) * (L : ℤ)) * (aperiodicCorr u k + aperiodicCorr v k)| ≤
      4 * P * (k : ℤ) * (L : ℤ) := by
    rw [hmain_eq]
    have hBC := (abs_add_le B C).trans (add_le_add hBbound hCbound)
    have hLnn : (0 : ℤ) ≤ (L : ℤ) := Nat.cast_nonneg L
    have h2Lnn : (0 : ℤ) ≤ 2 * (L : ℤ) := by linarith
    calc |2 * (L : ℤ) * (B + C)| = |2 * (L : ℤ)| * |B + C| := abs_mul _ _
      _ = 2 * (L : ℤ) * |B + C| := by rw [abs_of_nonneg h2Lnn]
      _ ≤ 2 * (L : ℤ) * (P * (k : ℤ) + P * (k : ℤ)) := mul_le_mul_of_nonneg_left hBC h2Lnn
      _ = 4 * P * (k : ℤ) * (L : ℤ) := by ring
  have hremBound : |2 * (L : ℤ) * (∑ i ∈ Finset.range r,
      blockSeq u v ε (((J * L + i : ℕ) : ZMod ((2 * M') * L))) *
        blockSeq u v ε (((J * L + i : ℕ) : ZMod ((2 * M') * L)) + (k : ZMod ((2 * M') * L)))) -
      (r : ℤ) * (aperiodicCorr u k + aperiodicCorr v k)| ≤ Q * (L : ℤ) := by
    rcases eq_or_lt_of_le hJm with hJeq | hJlt
    · have hXY : J * L = 2 * M' * L := by rw [hJeq]
      have hr0 : r = 0 := by omega
      have hz := hRemU 1 (by norm_num) 0 (NeZero.pos L).le
      unfold blockRemainder at hz
      simp [hr0] at hz ⊢
      linarith [hz]
    · have heqrem := blockRemainder_eq hm2 u v ε hε k hd J hJlt r hrL.le
      rw [heqrem]
      have hη2 :
          signAtNat ε J * signAtNat ε (J + 1) * (signAtNat ε J * signAtNat ε (J + 1)) = 1 := by
        have e1 : signAtNat ε J * signAtNat ε J = 1 := by unfold signAtNat; exact hε _
        have e2 : signAtNat ε (J + 1) * signAtNat ε (J + 1) = 1 := by
          unfold signAtNat; exact hε _
        calc signAtNat ε J * signAtNat ε (J + 1) * (signAtNat ε J * signAtNat ε (J + 1))
            = (signAtNat ε J * signAtNat ε J) * (signAtNat ε (J + 1) * signAtNat ε (J + 1)) := by
              ring
          _ = 1 := by rw [e1, e2]; ring
      rcases Nat.even_or_odd J with hJe | hJo
      · have hmod : J % 2 = 0 := Nat.even_iff.mp hJe
        have hwe : wordAtNat u v J = u := if_pos hJe
        have hwo : wordAtNat u v (J + 1) = v := by
          unfold wordAtNat; rw [if_neg (by rw [Nat.even_iff]; omega : ¬ Even (J + 1))]
        rw [hwe, hwo]
        exact hRemU _ hη2 r hrL.le
      · have hmod : J % 2 = 1 := Nat.odd_iff.mp hJo
        have hwo : wordAtNat u v J = v := by
          unfold wordAtNat; rw [if_neg (by rw [Nat.even_iff]; omega : ¬ Even J)]
        have hwe : wordAtNat u v (J + 1) = u := by
          unfold wordAtNat; rw [if_pos (by rw [Nat.even_iff]; omega : Even (J + 1))]
        rw [hwo, hwe]
        exact hRemV _ hη2 r hrL.le
  have hrem : cyclicCorrPrefix (blockSeq u v ε) k T =
      cyclicCorrPrefix (blockSeq u v ε) k (J * L) +
        ∑ i ∈ Finset.range r, blockSeq u v ε (((J * L + i : ℕ) : ZMod ((2 * M') * L))) *
          blockSeq u v ε (((J * L + i : ℕ) : ZMod ((2 * M') * L)) + (k : ZMod ((2 * M') * L))) := by
    rw [← hTeq]
    exact Finset.sum_range_add _ (J * L) r
  have hTcast : (T : ℤ) = (J : ℤ) * (L : ℤ) + (r : ℤ) := by exact_mod_cast hTeq.symm
  rw [hrem, hTcast]
  have hsplit : 2 * (L : ℤ) * (cyclicCorrPrefix (blockSeq u v ε) k (J * L) +
      ∑ i ∈ Finset.range r, blockSeq u v ε (((J * L + i : ℕ) : ZMod ((2 * M') * L))) *
        blockSeq u v ε (((J * L + i : ℕ) : ZMod ((2 * M') * L)) + (k : ZMod ((2 * M') * L)))) -
      ((J : ℤ) * (L : ℤ) + (r : ℤ)) * (aperiodicCorr u k + aperiodicCorr v k) =
      (2 * (L : ℤ) * cyclicCorrPrefix (blockSeq u v ε) k (J * L) -
        ((J : ℤ) * (L : ℤ)) * (aperiodicCorr u k + aperiodicCorr v k)) +
      (2 * (L : ℤ) * (∑ i ∈ Finset.range r,
        blockSeq u v ε (((J * L + i : ℕ) : ZMod ((2 * M') * L))) *
          blockSeq u v ε (((J * L + i : ℕ) : ZMod ((2 * M') * L)) + (k : ZMod ((2 * M') * L)))) -
        (r : ℤ) * (aperiodicCorr u k + aperiodicCorr v k)) := by ring
  rw [hsplit]
  have h5 := abs_add_le
    (2 * (L : ℤ) * cyclicCorrPrefix (blockSeq u v ε) k (J * L) -
        ((J : ℤ) * (L : ℤ)) * (aperiodicCorr u k + aperiodicCorr v k))
    (2 * (L : ℤ) * (∑ i ∈ Finset.range r,
        blockSeq u v ε (((J * L + i : ℕ) : ZMod ((2 * M') * L))) *
          blockSeq u v ε (((J * L + i : ℕ) : ZMod ((2 * M') * L)) + (k : ZMod ((2 * M') * L)))) -
      (r : ℤ) * (aperiodicCorr u k + aperiodicCorr v k))
  linarith [hmain_bound, hremBound, h5]

/-- **The zone window corollary**: every cyclic window — of arbitrary phase and length, not just a
period-aligned prefix — deviates from zero by at most twice the zone prefix constant, since a
window is a difference of two prefixes and each period-reduces to one within a single period. -/
theorem cyclicCorrWindow_blockSeq_zone {L : ℕ} [NeZero L] {m M' : ℕ} [NeZero m] (hm : m = 2 * M')
    (u v : Fin L → ℤ) (ε : Fin m → ℤ) (hε : ∀ j, ε j * ε j = 1)
    (hu1 : ∀ p, |u p| ≤ 1) (hv1 : ∀ p, |v p| ≤ 1)
    {d k : ℕ} (hd1 : 1 ≤ d) (hdk : d ≤ k) (hkL : k < L)
    (hzero : aperiodicCorr u d + aperiodicCorr v d = 0)
    (heven0 : ∑ j ∈ Finset.univ.filter (fun j : Fin m => Even j.val), ε j * ε (j + 1) = 0)
    (hodd0 : ∑ j ∈ Finset.univ.filter (fun j : Fin m => Odd j.val), ε j * ε (j + 1) = 0) (P : ℤ)
    (hPeven : ∀ J, J ≤ m → |∑ j ∈ Finset.range J,
        if Even j then signAtNat ε j * signAtNat ε (j + 1) else 0| ≤ P)
    (hPodd : ∀ J, J ≤ m → |∑ j ∈ Finset.range J,
        if Odd j then signAtNat ε j * signAtNat ε (j + 1) else 0| ≤ P) (p n : ℕ) :
    |cyclicCorrWindow (blockSeq u v ε) d p n| ≤ 2 * (2 + 2 * P) * (L : ℤ) := by
  have hcyc0 : cyclicCorr (blockSeq u v ε) d = 0 :=
    cyclicCorr_blockSeq_zone hm u v ε hε hd1 hdk hkL hzero heven0 hodd0
  rw [cyclicCorrWindow_eq_sub]
  have h1 := cyclicCorrPrefix_mod_period (blockSeq u v ε) d (p + n)
  have h2 := cyclicCorrPrefix_mod_period (blockSeq u v ε) d p
  rw [hcyc0, mul_zero, zero_add] at h1 h2
  rw [h1, h2]
  have hmLpos : 0 < m * L := NeZero.pos (m * L)
  have b1 : |cyclicCorrPrefix (blockSeq u v ε) d ((p + n) % (m * L))| ≤ (2 + 2 * P) * (L : ℤ) :=
    cyclicCorrPrefix_blockSeq_zone hm u v ε hε hu1 hv1 hd1 hdk hkL hzero P hPeven hPodd
      ((p + n) % (m * L)) (le_of_lt (Nat.mod_lt _ hmLpos))
  have b2 : |cyclicCorrPrefix (blockSeq u v ε) d (p % (m * L))| ≤ (2 + 2 * P) * (L : ℤ) :=
    cyclicCorrPrefix_blockSeq_zone hm u v ε hε hu1 hv1 hd1 hdk hkL hzero P hPeven hPodd
      (p % (m * L)) (le_of_lt (Nat.mod_lt _ hmLpos))
  have h4 := abs_add_le (cyclicCorrPrefix (blockSeq u v ε) d ((p + n) % (m * L)))
    (-cyclicCorrPrefix (blockSeq u v ε) d (p % (m * L)))
  rw [abs_neg, ← sub_eq_add_neg] at h4
  linarith [b1, b2, h4]

/-- **The spike window corollary**: every cyclic window's `2 * L`-scaled trend deviation at the top
lag is bounded by twice the spike prefix constant, by the same period-reduction as the zone case. -/
theorem cyclicCorrWindow_blockSeq_spike {L : ℕ} [NeZero L] {m M' : ℕ} [NeZero m] (hm : m = 2 * M')
    (u v : Fin L → ℤ) (ε : Fin m → ℤ) (hε : ∀ j, ε j * ε j = 1)
    (hu1 : ∀ p, |u p| ≤ 1) (hv1 : ∀ p, |v p| ≤ 1)
    {k : ℕ} (hk1 : 1 ≤ k) (hkL : k < L)
    (heven0 : ∑ j ∈ Finset.univ.filter (fun j : Fin m => Even j.val), ε j * ε (j + 1) = 0)
    (hodd0 : ∑ j ∈ Finset.univ.filter (fun j : Fin m => Odd j.val), ε j * ε (j + 1) = 0)
    (huv : aperiodicCorr u k = aperiodicCorr v k) (P : ℤ)
    (hPeven : ∀ J, J ≤ m → |∑ j ∈ Finset.range J,
        if Even j then signAtNat ε j * signAtNat ε (j + 1) else 0| ≤ P)
    (hPodd : ∀ J, J ≤ m → |∑ j ∈ Finset.range J,
        if Odd j then signAtNat ε j * signAtNat ε (j + 1) else 0| ≤ P) (Q : ℤ)
    (hRemU : ∀ η : ℤ, η * η = 1 → ∀ r, r ≤ L →
      |2 * (L : ℤ) * blockRemainder u v η k r -
          (r : ℤ) * (aperiodicCorr u k + aperiodicCorr v k)| ≤ Q * (L : ℤ))
    (hRemV : ∀ η : ℤ, η * η = 1 → ∀ r, r ≤ L →
      |2 * (L : ℤ) * blockRemainder v u η k r -
          (r : ℤ) * (aperiodicCorr u k + aperiodicCorr v k)| ≤ Q * (L : ℤ)) (p n : ℕ) :
    |2 * (L : ℤ) * cyclicCorrWindow (blockSeq u v ε) k p n -
        (n : ℤ) * (aperiodicCorr u k + aperiodicCorr v k)| ≤
      2 * (4 * P * (k : ℤ) + Q) * (L : ℤ) := by
  have : NeZero M' := ⟨fun h => (NeZero.ne m) (by rw [hm, h, mul_zero])⟩
  have hcycspike : cyclicCorr (blockSeq u v ε) k =
      (M' : ℤ) * (aperiodicCorr u k + aperiodicCorr v k) :=
    cyclicCorr_blockSeq_spike hm u v ε hε hk1 hkL heven0 hodd0
  have hmLpos : 0 < m * L := NeZero.pos (m * L)
  have hNeq : (m : ℤ) * (L : ℤ) = 2 * (M' : ℤ) * (L : ℤ) := by rw [hm]; push_cast; ring
  have h1 := cyclicCorrPrefix_mod_period (blockSeq u v ε) k (p + n)
  have h2 := cyclicCorrPrefix_mod_period (blockSeq u v ε) k p
  rw [hcycspike] at h1 h2
  have b1 := cyclicCorrPrefix_blockSeq_spike hm u v ε hε hu1 hv1 hk1 hkL huv P hPeven hPodd Q hRemU
    hRemV ((p + n) % (m * L)) (le_of_lt (Nat.mod_lt _ hmLpos))
  have b2 := cyclicCorrPrefix_blockSeq_spike hm u v ε hε hu1 hv1 hk1 hkL huv P hPeven hPodd Q hRemU
    hRemV (p % (m * L)) (le_of_lt (Nat.mod_lt _ hmLpos))
  rw [cyclicCorrWindow_eq_sub]
  have heq1 : 2 * (L : ℤ) * cyclicCorrPrefix (blockSeq u v ε) k (p + n) -
      ((p + n : ℕ) : ℤ) * (aperiodicCorr u k + aperiodicCorr v k) =
      (2 * (L : ℤ) * cyclicCorrPrefix (blockSeq u v ε) k ((p + n) % (m * L)) -
        (((p + n) % (m * L) : ℕ) : ℤ) * (aperiodicCorr u k + aperiodicCorr v k)) := by
    rw [h1]
    have hdm := Nat.div_add_mod (p + n) (m * L)
    have hdmZ : ((m * L : ℕ) : ℤ) * (((p + n) / (m * L) : ℕ) : ℤ) +
        (((p + n) % (m * L) : ℕ) : ℤ) = ((p + n : ℕ) : ℤ) := by exact_mod_cast hdm
    rw [Nat.cast_mul, hNeq] at hdmZ
    linear_combination (aperiodicCorr u k + aperiodicCorr v k) * hdmZ
  have heq2 : 2 * (L : ℤ) * cyclicCorrPrefix (blockSeq u v ε) k p -
      (p : ℤ) * (aperiodicCorr u k + aperiodicCorr v k) =
      (2 * (L : ℤ) * cyclicCorrPrefix (blockSeq u v ε) k (p % (m * L)) -
        ((p % (m * L) : ℕ) : ℤ) * (aperiodicCorr u k + aperiodicCorr v k)) := by
    rw [h2]
    have hdm := Nat.div_add_mod p (m * L)
    have hdmZ : ((m * L : ℕ) : ℤ) * ((p / (m * L) : ℕ) : ℤ) +
        ((p % (m * L) : ℕ) : ℤ) = (p : ℤ) := by exact_mod_cast hdm
    rw [Nat.cast_mul, hNeq] at hdmZ
    linear_combination (aperiodicCorr u k + aperiodicCorr v k) * hdmZ
  have hcomb : 2 * (L : ℤ) * (cyclicCorrPrefix (blockSeq u v ε) k (p + n) -
      cyclicCorrPrefix (blockSeq u v ε) k p) - (n : ℤ) * (aperiodicCorr u k + aperiodicCorr v k) =
      (2 * (L : ℤ) * cyclicCorrPrefix (blockSeq u v ε) k (p + n) -
        ((p + n : ℕ) : ℤ) * (aperiodicCorr u k + aperiodicCorr v k)) -
      (2 * (L : ℤ) * cyclicCorrPrefix (blockSeq u v ε) k p -
        (p : ℤ) * (aperiodicCorr u k + aperiodicCorr v k)) := by push_cast; ring
  rw [hcomb, heq1, heq2]
  have h5 := abs_add_le
    (2 * (L : ℤ) * cyclicCorrPrefix (blockSeq u v ε) k ((p + n) % (m * L)) -
        (((p + n) % (m * L) : ℕ) : ℤ) * (aperiodicCorr u k + aperiodicCorr v k))
    (-(2 * (L : ℤ) * cyclicCorrPrefix (blockSeq u v ε) k (p % (m * L)) -
        ((p % (m * L) : ℕ) : ℤ) * (aperiodicCorr u k + aperiodicCorr v k)))
  rw [abs_neg, ← sub_eq_add_neg] at h5
  linarith [b1, b2, h5]

/-! ## The single-site block decomposition and its bound -/

/-- **The exact block decomposition of a single-site prefix**: the prefix over the first `J`
complete blocks is exactly the running signed sum of each block's own word-sum — the lag-free
analogue of `cyclicCorrPrefix_blockSeq_blocks`. -/
private lemma singlePrefix_blockSeq_blocks {L : ℕ} [NeZero L] {m : ℕ} [NeZero m]
    (u v : Fin L → ℤ) (ε : Fin m → ℤ) :
    ∀ J, J ≤ m → singlePrefix (blockSeq u v ε) (J * L) =
      ∑ j ∈ Finset.range J, signAtNat ε j * (∑ p : Fin L, wordAtNat u v j p) := by
  intro J
  induction J with
  | zero => intro _; simp [singlePrefix]
  | succ n ih =>
    intro hJm
    have hnm : n < m := by omega
    have heq := ih (by omega)
    have hstep : singlePrefix (blockSeq u v ε) ((n + 1) * L) =
        singlePrefix (blockSeq u v ε) (n * L) +
          signAtNat ε n * (∑ p : Fin L, wordAtNat u v n p) := by
      unfold singlePrefix
      rw [show (n + 1) * L = n * L + L from by ring, Finset.sum_range_add]
      congr 1
      rw [signAtNat_val_eq ε (⟨n, hnm⟩ : Fin m), Finset.mul_sum,
        ← Fin.sum_univ_eq_sum_range
          (fun p => blockSeq u v ε ((n * L + p : ℕ) : ZMod (m * L))) L]
      apply Finset.sum_congr rfl
      intro p _
      have hce : ((n * L + p.val : ℕ) : ZMod (m * L)) = combine (⟨n, hnm⟩ : Fin m) p := by
        unfold combine; congr 1; ring
      rw [hce, blockSeq_combine, wordAt_eq_wordAtNat]
    rw [hstep, heq, Finset.sum_range_succ]

/-- **The single-site prefix bound**: given pointwise word bounds and a bound `P` on every prefix
of the running signed word-sum, every ℕ-indexed prefix (up to one period) of the assembled
sequence's own single-site query deviates from zero by at most `P` from the complete blocks plus
`L` from the last (possibly partial) block. -/
private theorem singlePrefix_blockSeq_bound {L : ℕ} [NeZero L] {m : ℕ} [NeZero m]
    (u v : Fin L → ℤ) (ε : Fin m → ℤ) (hε : ∀ j, ε j * ε j = 1)
    (hu1 : ∀ p, |u p| ≤ 1) (hv1 : ∀ p, |v p| ≤ 1) (P : ℤ)
    (hSum : ∀ J, J ≤ m → |∑ j ∈ Finset.range J,
        signAtNat ε j * (∑ p : Fin L, wordAtNat u v j p)| ≤ P)
    (T : ℕ) (hT : T ≤ m * L) :
    |singlePrefix (blockSeq u v ε) T| ≤ P + (L : ℤ) := by
  set J := T / L with hJdef
  set r := T % L with hrdef
  have hde := Nat.div_add_mod T L
  have hTeq : J * L + r = T := by rw [hJdef, hrdef, mul_comm]; omega
  have hrL : r < L := Nat.mod_lt _ (NeZero.pos L)
  have hJm : J ≤ m := by
    have hJLle : J * L ≤ m * L := by omega
    exact Nat.le_of_mul_le_mul_right hJLle (NeZero.pos L)
  have hmain := singlePrefix_blockSeq_blocks u v ε J hJm
  have hmainBound : |singlePrefix (blockSeq u v ε) (J * L)| ≤ P := by
    rw [hmain]; exact hSum J hJm
  have hremBound : |∑ i ∈ Finset.range r,
      blockSeq u v ε (((J * L + i : ℕ) : ZMod (m * L)))| ≤ (L : ℤ) := by
    have hstep : |∑ i ∈ Finset.range r, blockSeq u v ε (((J * L + i : ℕ) : ZMod (m * L)))| ≤
        ∑ i ∈ Finset.range r, |blockSeq u v ε (((J * L + i : ℕ) : ZMod (m * L)))| :=
      Finset.abs_sum_le_sum_abs _ _
    have hterm : ∑ i ∈ Finset.range r, |blockSeq u v ε (((J * L + i : ℕ) : ZMod (m * L)))| ≤
        ∑ _i ∈ Finset.range r, (1 : ℤ) := by
      apply Finset.sum_le_sum
      intro i _
      exact blockSeq_abs_le_one u v ε hε hu1 hv1 _
    have hsum1 : ∑ _i ∈ Finset.range r, (1 : ℤ) = (r : ℤ) := by simp
    have hrLcast : (r : ℤ) ≤ (L : ℤ) := by exact_mod_cast hrL.le
    linarith
  have hrem : singlePrefix (blockSeq u v ε) T = singlePrefix (blockSeq u v ε) (J * L) +
      ∑ i ∈ Finset.range r, blockSeq u v ε (((J * L + i : ℕ) : ZMod (m * L))) := by
    unfold singlePrefix
    rw [← hTeq]
    exact Finset.sum_range_add _ (J * L) r
  rw [hrem]
  have h3 := abs_add_le (singlePrefix (blockSeq u v ε) (J * L))
    (∑ i ∈ Finset.range r, blockSeq u v ε (((J * L + i : ℕ) : ZMod (m * L))))
  linarith

/-- **The single-site window bound**: every cyclic window — of arbitrary phase and length — of the
assembled sequence's single-site query deviates from zero by at most twice the prefix bound, once
the sequence balances over the whole period. -/
private theorem singleWindow_blockSeq_bound {L : ℕ} [NeZero L] {m : ℕ} [NeZero m]
    (u v : Fin L → ℤ) (ε : Fin m → ℤ) (hε : ∀ j, ε j * ε j = 1)
    (hu1 : ∀ p, |u p| ≤ 1) (hv1 : ∀ p, |v p| ≤ 1)
    (hzero : ∑ t : ZMod (m * L), blockSeq u v ε t = 0) (P : ℤ)
    (hSum : ∀ J, J ≤ m → |∑ j ∈ Finset.range J,
        signAtNat ε j * (∑ p : Fin L, wordAtNat u v j p)| ≤ P) (p n : ℕ) :
    |singleWindow (blockSeq u v ε) p n| ≤ 2 * (P + (L : ℤ)) := by
  rw [singleWindow_eq_sub]
  have h1 := singlePrefix_mod_period (blockSeq u v ε) (p + n)
  have h2 := singlePrefix_mod_period (blockSeq u v ε) p
  rw [hzero, mul_zero, zero_add] at h1 h2
  rw [h1, h2]
  have hmLpos : 0 < m * L := NeZero.pos (m * L)
  have b1 : |singlePrefix (blockSeq u v ε) ((p + n) % (m * L))| ≤ P + (L : ℤ) :=
    singlePrefix_blockSeq_bound u v ε hε hu1 hv1 P hSum
      ((p + n) % (m * L)) (le_of_lt (Nat.mod_lt _ hmLpos))
  have b2 : |singlePrefix (blockSeq u v ε) (p % (m * L))| ≤ P + (L : ℤ) :=
    singlePrefix_blockSeq_bound u v ε hε hu1 hv1 P hSum
      (p % (m * L)) (le_of_lt (Nat.mod_lt _ hmLpos))
  have h4 := abs_add_le (singlePrefix (blockSeq u v ε) ((p + n) % (m * L)))
    (-singlePrefix (blockSeq u v ε) (p % (m * L)))
  rw [abs_neg, ← sub_eq_add_neg] at h4
  linarith [b1, b2, h4]

private lemma digits2_two_mul (i : ℕ) :
    (Nat.digits 2 (2 * i)).count 1 = (Nat.digits 2 i).count 1 := by
  rcases Nat.eq_zero_or_pos i with hi | hi
  · subst hi; rfl
  · rw [Nat.digits_def' (by norm_num) (by omega)]
    have h1 : 2 * i % 2 = 0 := by omega
    have h2 : 2 * i / 2 = i := by omega
    rw [h1, h2]
    simp

private lemma digits2_two_mul_add_one (i : ℕ) :
    (Nat.digits 2 (2 * i + 1)).count 1 = (Nat.digits 2 i).count 1 + 1 := by
  rw [Nat.digits_def' (by norm_num) (by omega)]
  have h1 : (2 * i + 1) % 2 = 1 := by omega
  have h2 : (2 * i + 1) / 2 = i := by omega
  rw [h1, h2]
  simp

private lemma tmSign_two_mul (i : ℕ) : tmSign (2 * i) = tmSign i := by
  unfold tmSign; rw [digits2_two_mul]

private lemma tmSign_two_mul_add_one (i : ℕ) : tmSign (2 * i + 1) = - tmSign i := by
  unfold tmSign
  rw [digits2_two_mul_add_one]
  split_ifs with h1 h2 h2 <;> omega

/-- **The bit-sum, extended past its own bit count is unchanged**: every term added past index `q`
is `0`, since `q < 2 ^ q ≤ 2 ^ k` once `k > q`. Isolates the one piece of index arithmetic the
bit-sum recursion below needs. -/
private lemma bitsum_range_ext (q : ℕ) {N : ℕ} (h : q + 1 ≤ N) :
    ∑ k ∈ Finset.range N, (q / 2 ^ k % 2) = ∑ k ∈ Finset.range (q + 1), (q / 2 ^ k % 2) := by
  refine (Finset.sum_subset (Finset.range_subset_range.mpr h) ?_).symm
  intro k _ hk'
  simp only [Finset.mem_range, not_lt] at hk'
  have hqk : q < 2 ^ k :=
    lt_of_lt_of_le (Nat.lt_two_pow_self) (Nat.pow_le_pow_right (by norm_num) (by omega))
  simp [Nat.div_eq_of_lt hqk]

/-- **The bit-sum's own recursion**, one low bit peeled off: `bitsum (i)`, `range (i+1)`-wide,
splits into its own bit `i % 2` plus `bitsum (i / 2)`, `range (i/2+1)`-wide (the extra terms
`range (i/2+1)` through `range i` contribute `0` by `bitsum_range_ext`). -/
private lemma bitsum_succ (i : ℕ) (hi : 1 ≤ i) :
    ∑ j ∈ Finset.range (i + 1), (i / 2 ^ j % 2)
      = i % 2 + ∑ j ∈ Finset.range (i / 2 + 1), (i / 2 / 2 ^ j % 2) := by
  rw [Finset.sum_range_succ' (fun j => i / 2 ^ j % 2) i]
  have hshift : ∀ k, i / 2 ^ (k + 1) % 2 = i / 2 / 2 ^ k % 2 := by
    intro k
    rw [pow_succ', ← Nat.div_div_eq_div_mul]
  rw [Finset.sum_congr rfl (fun k _ => hshift k), bitsum_range_ext (i / 2) (by omega), pow_zero,
    Nat.div_one, add_comm]

/-- **The Thue–Morse sign as a bounded bit-sum**: `tmSign i = (-1) ^ (popcount)`, the popcount
computed as a bit-sum over `List.range (i+1)` rather than through `Nat.digits`/`List.count` —
the shape a numeral-level program can compute directly with `/`, `%`, `^`. Proved by strong
induction on `i` through `tmSign_two_mul`/`tmSign_two_mul_add_one` and the bit-sum's own recursion
(`bitsum_succ`); `Nat.digits` is not touched. -/
theorem tmSign_eq_bitsum (i : ℕ) :
    tmSign i = (-1 : ℤ) ^ (∑ j ∈ Finset.range (i + 1), i / 2 ^ j % 2) := by
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    match i, ih with
    | 0, _ => simp [tmSign]
    | (t + 1), ih =>
      rcases Nat.even_or_odd (t + 1) with he | ho
      · obtain ⟨q, hq⟩ := he
        have hq2 : t + 1 = 2 * q := by omega
        have hqlt : q < t + 1 := by omega
        rw [hq2, tmSign_two_mul, ih q hqlt, bitsum_succ (2 * q) (by omega)]
        have : (2 * q) / 2 = q := by omega
        rw [this]
        have h2 : (2 * q) % 2 = 0 := by omega
        rw [h2]
        ring
      · obtain ⟨q, hq⟩ := ho
        have hqlt : q < t + 1 := by omega
        rw [hq, tmSign_two_mul_add_one, ih q hqlt, bitsum_succ (2 * q + 1) (by omega)]
        have hdiv : (2 * q + 1) / 2 = q := by omega
        have hmod : (2 * q + 1) % 2 = 1 := by omega
        rw [hdiv, hmod]
        ring

/-- The Thue–Morse sign sequence balances to zero over every even-length initial range: the
digit-count parity pairs `2 * i` against `2 * i + 1` with opposite signs at every `i`. -/
theorem tmSign_balance (M : ℕ) : ∑ i ∈ Finset.range (2 * M), tmSign i = 0 := by
  induction M with
  | zero => simp
  | succ n ih =>
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 from by ring, Finset.sum_range_succ,
      Finset.sum_range_succ, ih, zero_add, tmSign_two_mul_add_one, tmSign_two_mul]
    ring

/-- **The odd-length partial identity**: an odd-length initial range of the Thue–Morse sign
sequence sums to a single half-index value, since the even-length range below it vanishes
(`tmSign_balance`) and the added top term is `tmSign` at the half index. -/
theorem tmSign_partial_odd (t : ℕ) : ∑ i ∈ Finset.range (2 * t + 1), tmSign i = tmSign t := by
  rw [Finset.sum_range_succ, tmSign_balance t, zero_add, tmSign_two_mul]

/-- **Every partial sum of the Thue–Morse sign sequence is bounded by `1`** in absolute value: an
even-length prefix vanishes and an odd-length prefix is a single `±1` value. -/
theorem tmSign_partial_abs_le_one (n : ℕ) : |∑ i ∈ Finset.range n, tmSign i| ≤ 1 := by
  rcases Nat.even_or_odd n with ⟨t, ht⟩ | ⟨t, ht⟩
  · rw [ht, ← two_mul, tmSign_balance]
    norm_num
  · rw [ht, tmSign_partial_odd]
    unfold tmSign
    split_ifs <;> norm_num

/-- The transition source read off the Thue–Morse sign at half-index: `tau (2 * i) = tau (2 * i +
1) = tmSign i`. -/
def tau (i : ℕ) : ℤ := tmSign (i / 2)

private lemma tau_sq (i : ℕ) : tau i * tau i = 1 := by
  unfold tau tmSign
  split_ifs <;> ring

/-- The block-sign supply: the prefix product of `tau`, so that consecutive-block products read
off `tau` directly (`blockSign_mul_noWrap`, `blockSign_mul_wrap`). -/
def blockSign (m : ℕ) (j : Fin m) : ℤ := ∏ i ∈ Finset.range j.val, tau i

private lemma prefixProd_sq (n : ℕ) :
    (∏ i ∈ Finset.range n, tau i) * (∏ i ∈ Finset.range n, tau i) = 1 := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Finset.prod_range_succ]
    calc (∏ i ∈ Finset.range k, tau i) * tau k * ((∏ i ∈ Finset.range k, tau i) * tau k)
        = (∏ i ∈ Finset.range k, tau i) * (∏ i ∈ Finset.range k, tau i) * (tau k * tau k) := by
          ring
      _ = 1 * 1 := by rw [ih, tau_sq k]
      _ = 1 := by ring

theorem blockSign_sq (m : ℕ) (j : Fin m) : blockSign m j * blockSign m j = 1 :=
  prefixProd_sq j.val

theorem blockSign_mul_noWrap (m : ℕ) [NeZero m] (j : Fin m) (h : j.val + 1 < m) :
    blockSign m j * blockSign m (nextBlock j) = tau j.val := by
  have hval : (nextBlock j).val = j.val + 1 := Nat.mod_eq_of_lt h
  unfold blockSign
  rw [hval, Finset.prod_range_succ]
  calc (∏ i ∈ Finset.range j.val, tau i) * ((∏ i ∈ Finset.range j.val, tau i) * tau j.val)
      = (∏ i ∈ Finset.range j.val, tau i) * (∏ i ∈ Finset.range j.val, tau i) * tau j.val := by
        ring
    _ = 1 * tau j.val := by rw [prefixProd_sq j.val]
    _ = tau j.val := by ring

private lemma prefixProd_four_mul (M : ℕ) : ∏ i ∈ Finset.range (2 * (2 * M)), tau i = 1 := by
  rw [show 2 * (2 * M) = 4 * M from by ring]
  induction M with
  | zero => simp
  | succ n ih =>
    have key : ∏ i ∈ Finset.range (4 * (n + 1)), tau i =
        (∏ i ∈ Finset.range (4 * n), tau i) *
          (tau (4 * n) * tau (4 * n + 1) * tau (4 * n + 2) * tau (4 * n + 3)) := by
      rw [show 4 * (n + 1) = 4 * n + 3 + 1 from by ring, Finset.prod_range_succ,
        show 4 * n + 3 = 4 * n + 2 + 1 from by ring, Finset.prod_range_succ,
        show 4 * n + 2 = 4 * n + 1 + 1 from by ring, Finset.prod_range_succ,
        Finset.prod_range_succ]
      ring
    rw [key, ih]
    have e1 : tau (4 * n + 1) = tau (4 * n) := by unfold tau; congr 1; omega
    have e2 : tau (4 * n + 3) = tau (4 * n + 2) := by unfold tau; congr 1; omega
    rw [e1, e2, one_mul]
    calc tau (4 * n) * tau (4 * n) * tau (4 * n + 2) * tau (4 * n + 2)
        = tau (4 * n) * tau (4 * n) * (tau (4 * n + 2) * tau (4 * n + 2)) := by ring
      _ = 1 * 1 := by rw [tau_sq (4 * n), tau_sq (4 * n + 2)]
      _ = 1 := by ring

theorem blockSign_mul_wrap (M : ℕ) [NeZero (2 * (2 * M))] (j : Fin (2 * (2 * M)))
    (h : j.val + 1 = 2 * (2 * M)) :
    blockSign (2 * (2 * M)) j * blockSign (2 * (2 * M)) (nextBlock j) = tau j.val := by
  have hval : (nextBlock j).val = 0 := by
    change (j.val + 1) % (2 * (2 * M)) = 0
    rw [h]; exact Nat.mod_self _
  unfold blockSign
  rw [hval, Finset.range_zero, Finset.prod_empty, mul_one]
  have hfull : ∏ i ∈ Finset.range (2 * (2 * M)), tau i = 1 := prefixProd_four_mul M
  rw [show 2 * (2 * M) = j.val + 1 from h.symm, Finset.prod_range_succ] at hfull
  calc (∏ i ∈ Finset.range j.val, tau i)
      = (∏ i ∈ Finset.range j.val, tau i) * (tau j.val * tau j.val) := by
        rw [tau_sq j.val, mul_one]
    _ = (∏ i ∈ Finset.range j.val, tau i) * tau j.val * tau j.val := by ring
    _ = 1 * tau j.val := by rw [hfull]
    _ = tau j.val := by ring

private lemma tau_evenIdx {M : ℕ} (i : Fin (2 * M)) : tau (evenIdx i).val = tmSign i.val := by
  unfold tau
  congr 1
  change 2 * i.val / 2 = i.val
  omega

private lemma tau_oddIdx {M : ℕ} (i : Fin (2 * M)) : tau (oddIdx i).val = tmSign i.val := by
  unfold tau
  congr 1
  change (2 * i.val + 1) / 2 = i.val
  omega

private lemma sum_tau_even (M : ℕ) [NeZero (2 * (2 * M))] :
    ∑ j ∈ Finset.univ.filter (fun j : Fin (2 * (2 * M)) => Even j.val), tau j.val = 0 := by
  rw [sum_filter_even (fun j : Fin (2 * (2 * M)) => tau j.val)]
  simp_rw [tau_evenIdx]
  rw [Fin.sum_univ_eq_sum_range (fun i => tmSign i) (2 * M)]
  exact tmSign_balance M

private lemma sum_tau_odd (M : ℕ) [NeZero (2 * (2 * M))] :
    ∑ j ∈ Finset.univ.filter (fun j : Fin (2 * (2 * M)) => Odd j.val), tau j.val = 0 := by
  rw [sum_filter_odd (fun j : Fin (2 * (2 * M)) => tau j.val)]
  simp_rw [tau_oddIdx]
  rw [Fin.sum_univ_eq_sum_range (fun i => tmSign i) (2 * M)]
  exact tmSign_balance M

private lemma tauPartialEven_two_mul (t : ℕ) :
    (∑ j ∈ Finset.range (2 * t), if Even j then tau j else 0) =
      ∑ i ∈ Finset.range t, tmSign i := by
  induction t with
  | zero => simp
  | succ n ih =>
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 from by ring, Finset.sum_range_succ,
      Finset.sum_range_succ, ih, Finset.sum_range_succ]
    have he : Even (2 * n) := ⟨n, two_mul n⟩
    have ho : ¬ Even (2 * n + 1) := by simp
    have h1 : tau (2 * n) = tmSign n := by unfold tau; congr 1; omega
    rw [if_pos he, if_neg ho, h1]
    ring

private lemma tauPartialEven_two_mul_add_one (t : ℕ) :
    (∑ j ∈ Finset.range (2 * t + 1), if Even j then tau j else 0) =
      ∑ i ∈ Finset.range (t + 1), tmSign i := by
  rw [Finset.sum_range_succ, tauPartialEven_two_mul]
  have he : Even (2 * t) := ⟨t, two_mul t⟩
  have h1 : tau (2 * t) = tmSign t := by unfold tau; congr 1; omega
  rw [if_pos he, h1, Finset.sum_range_succ]

private lemma tauPartialOdd_two_mul (t : ℕ) :
    (∑ j ∈ Finset.range (2 * t), if Odd j then tau j else 0) =
      ∑ i ∈ Finset.range t, tmSign i := by
  induction t with
  | zero => simp
  | succ n ih =>
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 from by ring, Finset.sum_range_succ,
      Finset.sum_range_succ, ih, Finset.sum_range_succ]
    have hno : ¬ Odd (2 * n) := by rintro ⟨k, hk⟩; omega
    have ho : Odd (2 * n + 1) := ⟨n, rfl⟩
    have h1 : tau (2 * n + 1) = tmSign n := by unfold tau; congr 1; omega
    rw [if_neg hno, if_pos ho, h1]
    ring

private lemma tauPartialOdd_two_mul_add_one (t : ℕ) :
    (∑ j ∈ Finset.range (2 * t + 1), if Odd j then tau j else 0) =
      ∑ i ∈ Finset.range t, tmSign i := by
  rw [Finset.sum_range_succ, tauPartialOdd_two_mul]
  have hno : ¬ Odd (2 * t) := by rintro ⟨k, hk⟩; omega
  rw [if_neg hno, add_zero]

/-- **The even-class partial transition sum is bounded by `1`**: the class reads `tmSign` at the
half-index, so this is `tmSign_partial_abs_le_one` transported along `tauPartialEven_two_mul`/
`tauPartialEven_two_mul_add_one`. -/
theorem tau_partial_even_abs_le_one (J : ℕ) :
    |∑ j ∈ Finset.range J, if Even j then tau j else 0| ≤ 1 := by
  rcases Nat.even_or_odd J with ⟨t, ht⟩ | ⟨t, ht⟩
  · rw [ht, ← two_mul, tauPartialEven_two_mul]
    exact tmSign_partial_abs_le_one t
  · rw [ht, tauPartialEven_two_mul_add_one]
    exact tmSign_partial_abs_le_one (t + 1)

/-- **The odd-class partial transition sum is bounded by `1`**, dually to
`tau_partial_even_abs_le_one`. -/
theorem tau_partial_odd_abs_le_one (J : ℕ) :
    |∑ j ∈ Finset.range J, if Odd j then tau j else 0| ≤ 1 := by
  rcases Nat.even_or_odd J with ⟨t, ht⟩ | ⟨t, ht⟩
  · rw [ht, ← two_mul, tauPartialOdd_two_mul]
    exact tmSign_partial_abs_le_one t
  · rw [ht, tauPartialOdd_two_mul_add_one]
    exact tmSign_partial_abs_le_one t

private lemma blockSign_mul_succ (M : ℕ) [NeZero (2 * (2 * M))] (j : Fin (2 * (2 * M))) :
    blockSign (2 * (2 * M)) j * blockSign (2 * (2 * M)) (nextBlock j) = tau j.val := by
  by_cases h : j.val + 1 < 2 * (2 * M)
  · exact blockSign_mul_noWrap (2 * (2 * M)) j h
  · exact blockSign_mul_wrap M j (by omega)

/-- **Both block-transition sign sums vanish** at the even class: the prefix-product supply pairs
`ε j * ε (j + 1)` with `tau j.val`, and `tau` itself balances to zero over the even class by
`tmSign_balance`. -/
theorem blockSign_transition_even (M : ℕ) [NeZero (2 * (2 * M))] :
    ∑ j ∈ Finset.univ.filter (fun j : Fin (2 * (2 * M)) => Even j.val),
      blockSign (2 * (2 * M)) j * blockSign (2 * (2 * M)) (j + 1) = 0 := by
  rw [← sum_tau_even M]
  apply Finset.sum_congr rfl
  intro j _
  rw [← nextBlock_eq_add_one]
  exact blockSign_mul_succ M j

/-- **Both block-transition sign sums vanish** at the odd class, dually to
`blockSign_transition_even`. -/
theorem blockSign_transition_odd (M : ℕ) [NeZero (2 * (2 * M))] :
    ∑ j ∈ Finset.univ.filter (fun j : Fin (2 * (2 * M)) => Odd j.val),
      blockSign (2 * (2 * M)) j * blockSign (2 * (2 * M)) (j + 1) = 0 := by
  rw [← sum_tau_odd M]
  apply Finset.sum_congr rfl
  intro j _
  rw [← nextBlock_eq_add_one]
  exact blockSign_mul_succ M j

/-! ### The sign supply's closed form -/

/-- The prefix product of `tmSign` itself, at home beside `blockSign`'s own prefix product of
`tau`. -/
def tmPrefix (n : ℕ) : ℤ := ∏ i ∈ Finset.range n, tmSign i

private lemma tmSign_sq (i : ℕ) : tmSign i * tmSign i = 1 := by
  unfold tmSign; split_ifs <;> ring

private lemma tmPrefix_sq (n : ℕ) : tmPrefix n * tmPrefix n = 1 := by
  induction n with
  | zero => simp [tmPrefix]
  | succ k ih =>
    unfold tmPrefix at ih ⊢
    rw [Finset.prod_range_succ]
    calc (∏ i ∈ Finset.range k, tmSign i) * tmSign k *
          ((∏ i ∈ Finset.range k, tmSign i) * tmSign k)
        = (∏ i ∈ Finset.range k, tmSign i) * (∏ i ∈ Finset.range k, tmSign i) *
            (tmSign k * tmSign k) := by ring
      _ = 1 * 1 := by rw [ih, tmSign_sq k]
      _ = 1 := by ring

private lemma tmPrefix_succ (n : ℕ) : tmPrefix (n + 1) = tmPrefix n * tmSign n :=
  Finset.prod_range_succ _ _

/-- **`tmPrefix` at an even index**: the prefix product collapses to the alternating sign, one
factor of `-1` per cancelling pair `tmSign (2i)`, `tmSign (2i+1)`. -/
theorem tmPrefix_two_mul (t : ℕ) : tmPrefix (2 * t) = (-1) ^ t := by
  induction t with
  | zero => simp [tmPrefix]
  | succ s ih =>
    have hstep : tmPrefix (2 * (s + 1)) =
        tmPrefix (2 * s) * (tmSign (2 * s) * tmSign (2 * s + 1)) := by
      rw [show 2 * (s + 1) = 2 * s + 1 + 1 from by ring, tmPrefix_succ, tmPrefix_succ]
      ring
    rw [hstep, ih, tmSign_two_mul, tmSign_two_mul_add_one]
    have hsq : tmSign s * tmSign s = 1 := tmSign_sq s
    calc (-1 : ℤ) ^ s * (tmSign s * -tmSign s)
        = -((-1 : ℤ) ^ s * (tmSign s * tmSign s)) := by ring
      _ = -((-1 : ℤ) ^ s * 1) := by rw [hsq]
      _ = (-1 : ℤ) ^ (s + 1) := by ring

/-- **`tmPrefix` at an odd index**: one further, un-cancelled factor of `tmSign t`. -/
theorem tmPrefix_two_mul_add_one (t : ℕ) : tmPrefix (2 * t + 1) = (-1) ^ t * tmSign t := by
  rw [tmPrefix_succ, tmPrefix_two_mul, tmSign_two_mul]

private lemma tauProd_two_mul (t : ℕ) : ∏ i ∈ Finset.range (2 * t), tau i = 1 := by
  induction t with
  | zero => simp
  | succ s ih =>
    rw [show 2 * (s + 1) = 2 * s + 1 + 1 from by ring, Finset.prod_range_succ,
      Finset.prod_range_succ, ih]
    have h1 : tau (2 * s) = tmSign s := by unfold tau; congr 1; omega
    have h2 : tau (2 * s + 1) = tmSign s := by unfold tau; congr 1; omega
    rw [h1, h2, one_mul]
    exact tmSign_sq s

private lemma tauProd_two_mul_add_one (t : ℕ) :
    ∏ i ∈ Finset.range (2 * t + 1), tau i = tmSign t := by
  rw [Finset.prod_range_succ, tauProd_two_mul]
  have h1 : tau (2 * t) = tmSign t := by unfold tau; congr 1; omega
  rw [h1, one_mul]

/-- **The sign supply's closed form.** `blockSign` at any block index is the product of two
`tmPrefix` values straddling the index halved — the same pairing `tauProd_two_mul`/
`tauProd_two_mul_add_one` isolate, restated without reference to `tau`. -/
theorem blockSign_eq_tmPrefix (m : ℕ) (j : Fin m) :
    blockSign m j = tmPrefix ((j.val + 1) / 2) * tmPrefix (j.val / 2) := by
  unfold blockSign
  rcases Nat.even_or_odd j.val with he | ho
  · obtain ⟨t, ht⟩ := he
    have ht2 : j.val = 2 * t := by omega
    rw [ht2, tauProd_two_mul]
    have he1 : (2 * t + 1) / 2 = t := by omega
    have he2 : (2 * t) / 2 = t := by omega
    rw [he1, he2]
    exact (tmPrefix_sq t).symm
  · obtain ⟨t, ht⟩ := ho
    rw [ht, tauProd_two_mul_add_one]
    have ho1 : (2 * t + 1 + 1) / 2 = t + 1 := by omega
    have ho2 : (2 * t + 1) / 2 = t := by omega
    rw [ho1, ho2, tmPrefix_succ]
    have hsq : tmPrefix t * tmPrefix t = 1 := tmPrefix_sq t
    calc tmSign t = 1 * tmSign t := (one_mul _).symm
      _ = (tmPrefix t * tmPrefix t) * tmSign t := by rw [hsq]
      _ = tmPrefix t * tmSign t * tmPrefix t := by ring

/-- **The sign supply is exactly `1` at every even block index**: `blockSign_eq_tmPrefix`'s two
`tmPrefix` factors coincide at an even index, so `tmPrefix_sq` collapses their product. -/
private lemma signAtNat_blockSign_even (m : ℕ) [NeZero m] (t : ℕ) (h : 2 * t < m) :
    signAtNat (blockSign m) (2 * t) = 1 := by
  rw [signAtNat_val_eq (blockSign m) (⟨2 * t, h⟩ : Fin m), blockSign_eq_tmPrefix]
  have h1 : (2 * t + 1) / 2 = t := by omega
  have h2 : (2 * t) / 2 = t := by omega
  rw [h1, h2]
  exact tmPrefix_sq t

/-- **The sign supply is exactly the Thue–Morse sign at every odd block index**:
`blockSign_eq_tmPrefix`'s two `tmPrefix` factors are one `tmPrefix_succ` apart, so their product
collapses to the one uncancelled `tmSign` factor. -/
private lemma signAtNat_blockSign_odd (m : ℕ) [NeZero m] (t : ℕ) (h : 2 * t + 1 < m) :
    signAtNat (blockSign m) (2 * t + 1) = tmSign t := by
  rw [signAtNat_val_eq (blockSign m) (⟨2 * t + 1, h⟩ : Fin m), blockSign_eq_tmPrefix]
  have h1 : (2 * t + 1 + 1) / 2 = t + 1 := by omega
  have h2 : (2 * t + 1) / 2 = t := by omega
  rw [h1, h2, tmPrefix_succ]
  have hsq : tmPrefix t * tmPrefix t = 1 := tmPrefix_sq t
  calc tmPrefix t * tmSign t * tmPrefix t = tmPrefix t * tmPrefix t * tmSign t := by ring
    _ = 1 * tmSign t := by rw [hsq]
    _ = tmSign t := by ring

/-! ## The instance -/

/-- The first length-`24` word of the certified pair. -/
def wordU : Fin 24 → ℤ :=
  ![-1, -1, 1, -1, -1, 1, 1, 1, 1, 1, -1, 1, 1, -1, -1, -1, -1, -1, 1, -1, -1, 1, 1, 1]

/-- The second length-`24` word of the certified pair. -/
def wordV : Fin 24 → ℤ :=
  ![1, 1, -1, 1, -1, 1, 1, 1, -1, -1, 1, -1, 1, -1, -1, -1, 1, 1, -1, 1, -1, 1, 1, 1]

private lemma aperiodicCorr_wordU_wordV_zone (d : ℕ) (hd1 : 1 ≤ d) (hd7 : d ≤ 7) :
    aperiodicCorr wordU d + aperiodicCorr wordV d = 0 := by
  interval_cases d <;> decide

private lemma aperiodicCorr_wordU_wordV_spike :
    aperiodicCorr wordU 8 + aperiodicCorr wordV 8 = -32 := by decide

/-- **The assembled theorem.** For every block-repetition count `M`, the period-`96 * M`
sequence built from `wordU`/`wordV` alternated by block and scaled by the prefix-product sign
supply has vanishing cyclic correlation at every lag `1` through `7`, and cyclic correlation
`-64 * M` at lag `8`. -/
theorem blockSeq_wordU_wordV_correlation (M : ℕ) [NeZero (2 * (2 * M))] :
    (∀ d, 1 ≤ d → d ≤ 7 →
        cyclicCorr (blockSeq wordU wordV (blockSign (2 * (2 * M)))) d = 0) ∧
      cyclicCorr (blockSeq wordU wordV (blockSign (2 * (2 * M)))) 8 = -64 * (M : ℤ) := by
  refine ⟨fun d hd1 hd7 => ?_, ?_⟩
  · exact cyclicCorr_blockSeq_zone rfl wordU wordV (blockSign (2 * (2 * M))) (blockSign_sq _)
      hd1 hd7 (by norm_num) (aperiodicCorr_wordU_wordV_zone d hd1 hd7)
      (blockSign_transition_even M) (blockSign_transition_odd M)
  · rw [cyclicCorr_blockSeq_spike rfl wordU wordV (blockSign (2 * (2 * M))) (blockSign_sq _)
      (by norm_num) (by norm_num) (blockSign_transition_even M) (blockSign_transition_odd M),
      aperiodicCorr_wordU_wordV_spike]
    push_cast
    ring

private lemma wordU_abs_le_one (p : Fin 24) : |wordU p| ≤ 1 := by fin_cases p <;> decide

private lemma wordV_abs_le_one (p : Fin 24) : |wordV p| ≤ 1 := by fin_cases p <;> decide

private lemma aperiodicCorr_wordU_eq_wordV_spike :
    aperiodicCorr wordU 8 = aperiodicCorr wordV 8 := by decide

private lemma eq_one_or_neg_one_of_sq_eq_one {a : ℤ} (h : a * a = 1) : a = 1 ∨ a = -1 := by
  have hz : (a - 1) * (a + 1) = 0 := by nlinarith
  rcases mul_eq_zero.mp hz with h1 | h1
  · left; omega
  · right; omega

/-- The block-sign supply's transition product, at any in-range block index, is `tau` there:
the ℕ-indexed reading (`signAtNat`) is exactly `blockSign`'s own `blockSign_mul_succ`. -/
private lemma signAtNat_blockSign_eq_tau (M : ℕ) [NeZero (2 * (2 * M))] (j : ℕ)
    (hj : j < 2 * (2 * M)) :
    signAtNat (blockSign (2 * (2 * M))) j * signAtNat (blockSign (2 * (2 * M))) (j + 1) =
      tau j := by
  rw [signAtNat_val_eq (blockSign (2 * (2 * M))) (⟨j, hj⟩ : Fin (2 * (2 * M))),
    ← sign_nextBlock_eq_signAtNat_succ (blockSign (2 * (2 * M))) (⟨j, hj⟩ : Fin (2 * (2 * M)))]
  exact blockSign_mul_succ M ⟨j, hj⟩

private lemma hPeven_blockSign (M : ℕ) [NeZero (2 * (2 * M))] :
    ∀ J, J ≤ 2 * (2 * M) →
      |∑ j ∈ Finset.range J, if Even j then signAtNat (blockSign (2 * (2 * M))) j *
          signAtNat (blockSign (2 * (2 * M))) (j + 1) else 0| ≤ (1 : ℤ) := by
  intro J _
  have heq : (∑ j ∈ Finset.range J, if Even j then signAtNat (blockSign (2 * (2 * M))) j *
      signAtNat (blockSign (2 * (2 * M))) (j + 1) else 0) =
      ∑ j ∈ Finset.range J, if Even j then tau j else 0 := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.mem_range] at hj
    split_ifs with he
    · exact signAtNat_blockSign_eq_tau M j (by omega)
    · rfl
  rw [heq]
  exact tau_partial_even_abs_le_one J

private lemma hPodd_blockSign (M : ℕ) [NeZero (2 * (2 * M))] :
    ∀ J, J ≤ 2 * (2 * M) →
      |∑ j ∈ Finset.range J, if Odd j then signAtNat (blockSign (2 * (2 * M))) j *
          signAtNat (blockSign (2 * (2 * M))) (j + 1) else 0| ≤ (1 : ℤ) := by
  intro J _
  have heq : (∑ j ∈ Finset.range J, if Odd j then signAtNat (blockSign (2 * (2 * M))) j *
      signAtNat (blockSign (2 * (2 * M))) (j + 1) else 0) =
      ∑ j ∈ Finset.range J, if Odd j then tau j else 0 := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.mem_range] at hj
    split_ifs with ho
    · exact signAtNat_blockSign_eq_tau M j (by omega)
    · rfl
  rw [heq]
  exact tau_partial_odd_abs_le_one J

private lemma hRemU_wordU_wordV (η : ℤ) (hη : η * η = 1) (r : ℕ) (hr : r ≤ 24) :
    |2 * (24 : ℤ) * blockRemainder wordU wordV η 8 r -
        (r : ℤ) * (aperiodicCorr wordU 8 + aperiodicCorr wordV 8)| ≤ (14 : ℤ) * 24 := by
  rcases eq_one_or_neg_one_of_sq_eq_one hη with rfl | rfl <;> interval_cases r <;> decide

private lemma hRemV_wordU_wordV (η : ℤ) (hη : η * η = 1) (r : ℕ) (hr : r ≤ 24) :
    |2 * (24 : ℤ) * blockRemainder wordV wordU η 8 r -
        (r : ℤ) * (aperiodicCorr wordU 8 + aperiodicCorr wordV 8)| ≤ (14 : ℤ) * 24 := by
  rcases eq_one_or_neg_one_of_sq_eq_one hη with rfl | rfl <;> interval_cases r <;> decide

/-- **The zone prefix bound, instantiated.** Every ℕ-indexed prefix (up to the period) of the
`wordU`/`wordV` block sequence's query at a lag `1 ≤ d ≤ 7` deviates from zero by at most `4 * 24`,
independent of the block-repetition count `M`. -/
theorem cyclicCorrPrefix_blockSeq_wordU_wordV_zone (M : ℕ) [NeZero (2 * (2 * M))]
    {d : ℕ} (hd1 : 1 ≤ d) (hd7 : d ≤ 7) (T : ℕ) (hT : T ≤ 2 * (2 * M) * 24) :
    |cyclicCorrPrefix (blockSeq wordU wordV (blockSign (2 * (2 * M)))) d T| ≤
      (2 + 2 * 1) * (24 : ℤ) :=
  cyclicCorrPrefix_blockSeq_zone rfl wordU wordV (blockSign (2 * (2 * M))) (blockSign_sq _)
    wordU_abs_le_one wordV_abs_le_one hd1 (le_refl d) (by omega)
    (aperiodicCorr_wordU_wordV_zone d hd1 hd7) 1 (hPeven_blockSign M) (hPodd_blockSign M) T hT

/-- **The spike prefix bound, instantiated.** At the top lag `8`, every ℕ-indexed prefix's
`2 * 24`-scaled deviation from the exact linear trend is at most `(4 * 8 + 14) * 24`, independent
of `M`; the certified pair's own combined aperiodic correlation there is `-32`
(`aperiodicCorr_wordU_wordV_spike`). -/
theorem cyclicCorrPrefix_blockSeq_wordU_wordV_spike (M : ℕ) [NeZero (2 * (2 * M))] (T : ℕ)
    (hT : T ≤ 2 * (2 * M) * 24) :
    |2 * (24 : ℤ) * cyclicCorrPrefix (blockSeq wordU wordV (blockSign (2 * (2 * M)))) 8 T -
        (T : ℤ) * (aperiodicCorr wordU 8 + aperiodicCorr wordV 8)| ≤ (4 * 1 * (8 : ℤ) + 14) * 24 :=
  cyclicCorrPrefix_blockSeq_spike rfl wordU wordV (blockSign (2 * (2 * M))) (blockSign_sq _)
    wordU_abs_le_one wordV_abs_le_one (by norm_num) (by norm_num)
    aperiodicCorr_wordU_eq_wordV_spike 1 (hPeven_blockSign M) (hPodd_blockSign M) 14
    hRemU_wordU_wordV hRemV_wordU_wordV T hT

/-- **The zone window corollary, instantiated.** Every cyclic window of the `wordU`/`wordV` block
sequence at a lag `1 ≤ d ≤ 7`, of arbitrary phase and length, deviates from zero by at most
`2 * (4 * 24)`. -/
theorem cyclicCorrWindow_blockSeq_wordU_wordV_zone (M : ℕ) [NeZero (2 * (2 * M))]
    {d : ℕ} (hd1 : 1 ≤ d) (hd7 : d ≤ 7) (p n : ℕ) :
    |cyclicCorrWindow (blockSeq wordU wordV (blockSign (2 * (2 * M)))) d p n| ≤
      2 * ((2 + 2 * 1) * (24 : ℤ)) :=
  cyclicCorrWindow_blockSeq_zone rfl wordU wordV (blockSign (2 * (2 * M))) (blockSign_sq _)
    wordU_abs_le_one wordV_abs_le_one hd1 (le_refl d) (by omega)
    (aperiodicCorr_wordU_wordV_zone d hd1 hd7) (blockSign_transition_even M)
    (blockSign_transition_odd M) 1 (hPeven_blockSign M) (hPodd_blockSign M) p n

/-- **The spike window corollary, instantiated.** Every cyclic window at the top lag `8`, of
arbitrary phase and length, has `2 * 24`-scaled trend deviation at most
`2 * ((4 * 8 + 14) * 24)`. -/
theorem cyclicCorrWindow_blockSeq_wordU_wordV_spike (M : ℕ) [NeZero (2 * (2 * M))] (p n : ℕ) :
    |2 * (24 : ℤ) * cyclicCorrWindow (blockSeq wordU wordV (blockSign (2 * (2 * M)))) 8 p n -
        (n : ℤ) * (aperiodicCorr wordU 8 + aperiodicCorr wordV 8)| ≤
      2 * ((4 * 1 * (8 : ℤ) + 14) * 24) :=
  cyclicCorrWindow_blockSeq_spike rfl wordU wordV (blockSign (2 * (2 * M))) (blockSign_sq _)
    wordU_abs_le_one wordV_abs_le_one (by norm_num) (by norm_num) (blockSign_transition_even M)
    (blockSign_transition_odd M) aperiodicCorr_wordU_eq_wordV_spike 1 (hPeven_blockSign M)
    (hPodd_blockSign M) 14 hRemU_wordU_wordV hRemV_wordU_wordV p n

/-! ### The single-site instance -/

private lemma wordU_sum : (∑ p : Fin 24, wordU p) = 0 := by decide

private lemma wordV_sum : (∑ p : Fin 24, wordV p) = 4 := by decide

private lemma wordSumAtNat_wordU_wordV_even (t : ℕ) :
    (∑ p : Fin 24, wordAtNat wordU wordV (2 * t) p) = 0 := by
  have heq : wordAtNat wordU wordV (2 * t) = wordU := by
    unfold wordAtNat; rw [if_pos ⟨t, two_mul t⟩]
  rw [heq, wordU_sum]

private lemma wordSumAtNat_wordU_wordV_odd (t : ℕ) :
    (∑ p : Fin 24, wordAtNat wordU wordV (2 * t + 1) p) = 4 := by
  have heq : wordAtNat wordU wordV (2 * t + 1) = wordV := by
    unfold wordAtNat; rw [if_neg (by rw [Nat.even_iff]; omega : ¬ Even (2 * t + 1))]
  rw [heq, wordV_sum]

/-- The running signed word-sum, at an even-length prefix: it reads off `4` times a Thue–Morse
partial sum, since `wordU`'s zero balance kills every even-block term. -/
private lemma wordSumPartial_two_mul (M : ℕ) [NeZero (2 * (2 * M))] :
    ∀ t, 2 * t ≤ 2 * (2 * M) →
      (∑ j ∈ Finset.range (2 * t), signAtNat (blockSign (2 * (2 * M))) j *
          (∑ p : Fin 24, wordAtNat wordU wordV j p)) = 4 * ∑ i ∈ Finset.range t, tmSign i := by
  intro t
  induction t with
  | zero => intro _; simp
  | succ n ih =>
    intro ht
    have hstep : (∑ j ∈ Finset.range (2 * (n + 1)),
        signAtNat (blockSign (2 * (2 * M))) j * (∑ p : Fin 24, wordAtNat wordU wordV j p)) =
        (∑ j ∈ Finset.range (2 * n),
          signAtNat (blockSign (2 * (2 * M))) j * (∑ p : Fin 24, wordAtNat wordU wordV j p)) +
        signAtNat (blockSign (2 * (2 * M))) (2 * n) *
          (∑ p : Fin 24, wordAtNat wordU wordV (2 * n) p) +
        signAtNat (blockSign (2 * (2 * M))) (2 * n + 1) *
          (∑ p : Fin 24, wordAtNat wordU wordV (2 * n + 1) p) := by
      rw [show 2 * (n + 1) = 2 * n + 1 + 1 from by ring, Finset.sum_range_succ,
        Finset.sum_range_succ]
    rw [hstep, ih (by omega), signAtNat_blockSign_even _ n (by omega),
      wordSumAtNat_wordU_wordV_even, signAtNat_blockSign_odd _ n (by omega),
      wordSumAtNat_wordU_wordV_odd, Finset.sum_range_succ]
    ring

/-- The odd-length sibling of `wordSumPartial_two_mul`: the added top term is an even block index,
whose `wordU` contribution vanishes, so the value is unchanged. -/
private lemma wordSumPartial_two_mul_add_one (M : ℕ) [NeZero (2 * (2 * M))] :
    ∀ t, 2 * t + 1 ≤ 2 * (2 * M) →
      (∑ j ∈ Finset.range (2 * t + 1), signAtNat (blockSign (2 * (2 * M))) j *
          (∑ p : Fin 24, wordAtNat wordU wordV j p)) = 4 * ∑ i ∈ Finset.range t, tmSign i := by
  intro t ht
  rw [Finset.sum_range_succ, wordSumPartial_two_mul M t (by omega),
    signAtNat_blockSign_even _ t (by omega), wordSumAtNat_wordU_wordV_even]
  ring

/-- **The running signed word-sum is bounded by `4`** at every prefix, independent of the
block-repetition count `M`: `tmSign_partial_abs_le_one` transported along
`wordSumPartial_two_mul`/`wordSumPartial_two_mul_add_one`. -/
private lemma abs_wordSumPartial_le_four (M : ℕ) [NeZero (2 * (2 * M))] (J : ℕ)
    (hJ : J ≤ 2 * (2 * M)) :
    |∑ j ∈ Finset.range J, signAtNat (blockSign (2 * (2 * M))) j *
        (∑ p : Fin 24, wordAtNat wordU wordV j p)| ≤ (4 : ℤ) := by
  have hfour : ∀ t : ℕ, |(4 : ℤ) * ∑ i ∈ Finset.range t, tmSign i| ≤ (4 : ℤ) := by
    intro t
    have h1 := tmSign_partial_abs_le_one t
    have heq : |(4 : ℤ) * ∑ i ∈ Finset.range t, tmSign i|
        = 4 * |∑ i ∈ Finset.range t, tmSign i| := by rw [abs_mul]; norm_num
    rw [heq]; linarith
  rcases Nat.even_or_odd J with ⟨t, ht⟩ | ⟨t, ht⟩
  · rw [ht, ← two_mul, wordSumPartial_two_mul M t (by omega)]
    exact hfour t
  · rw [ht, wordSumPartial_two_mul_add_one M t (by omega)]
    exact hfour t

/-- **The single-site prefix bound, instantiated.** Every ℕ-indexed prefix (up to the period) of
the `wordU`/`wordV` block sequence's own single-site query deviates from zero by at most `4 + 24`,
independent of `M`. -/
private theorem singlePrefix_blockSeq_wordU_wordV_bound (M : ℕ) [NeZero (2 * (2 * M))] (T : ℕ)
    (hT : T ≤ 2 * (2 * M) * 24) :
    |singlePrefix (blockSeq wordU wordV (blockSign (2 * (2 * M)))) T| ≤ (4 : ℤ) + 24 :=
  singlePrefix_blockSeq_bound wordU wordV (blockSign (2 * (2 * M))) (blockSign_sq _)
    wordU_abs_le_one wordV_abs_le_one 4 (abs_wordSumPartial_le_four M) T hT

/-- The certified pair's own sequence balances over the whole period: the full-period prefix is
the `M = 2 * M` case of `wordSumPartial_two_mul`, against `tmSign_balance`. -/
private lemma singlePrefix_blockSeq_wordU_wordV_full (M : ℕ) [NeZero (2 * (2 * M))] :
    singlePrefix (blockSeq wordU wordV (blockSign (2 * (2 * M)))) (2 * (2 * M) * 24) = 0 := by
  have hb := singlePrefix_blockSeq_blocks wordU wordV (blockSign (2 * (2 * M)))
    (2 * (2 * M)) le_rfl
  rw [hb, wordSumPartial_two_mul M (2 * M) le_rfl, tmSign_balance M, mul_zero]

private lemma singlePrefix_blockSeq_wordU_wordV_period_zero (M : ℕ) [NeZero (2 * (2 * M))] :
    ∑ t : ZMod (2 * (2 * M) * 24), blockSeq wordU wordV (blockSign (2 * (2 * M))) t = 0 := by
  rw [← singlePrefix_eq_full_sum]
  exact singlePrefix_blockSeq_wordU_wordV_full M

/-- **The single-site window bound, instantiated.** Every cyclic window of the `wordU`/`wordV`
block sequence's own single-site query, of arbitrary phase and length, deviates from zero by at
most `2 * (4 + 24)`, independent of `M`. -/
theorem singleWindow_blockSeq_wordU_wordV_bound (M : ℕ) [NeZero (2 * (2 * M))] (p n : ℕ) :
    |singleWindow (blockSeq wordU wordV (blockSign (2 * (2 * M)))) p n| ≤ 2 * ((4 : ℤ) + 24) :=
  singleWindow_blockSeq_bound wordU wordV (blockSign (2 * (2 * M))) (blockSign_sq _)
    wordU_abs_le_one wordV_abs_le_one (singlePrefix_blockSeq_wordU_wordV_period_zero M)
    4 (abs_wordSumPartial_le_four M) p n

private lemma wordU_sq (p : Fin 24) : wordU p * wordU p = 1 := by fin_cases p <;> decide

private lemma wordV_sq (p : Fin 24) : wordV p * wordV p = 1 := by fin_cases p <;> decide

/-- **The design is exactly `±1`-valued**: `blockSeq` at the certified pair squares to `1`
everywhere, since both the sign supply (`blockSign_sq`) and the two words are themselves exactly
`±1`-valued. This is what lets `designObs` (`BlockPairHost.lean`) read the design as a genuine
Boolean observation rather than merely a bounded one. -/
theorem blockSeq_wordU_wordV_sq (M : ℕ) [NeZero (2 * (2 * M))]
    (x : ZMod (2 * (2 * M) * 24)) :
    blockSeq wordU wordV (blockSign (2 * (2 * M))) x *
      blockSeq wordU wordV (blockSign (2 * (2 * M))) x = 1 := by
  unfold blockSeq
  have hε := blockSign_sq (2 * (2 * M)) (blockIdx x)
  split_ifs
  · have hu := wordU_sq (blockOff x)
    calc blockSign (2 * (2 * M)) (blockIdx x) * wordU (blockOff x) *
          (blockSign (2 * (2 * M)) (blockIdx x) * wordU (blockOff x))
        = (blockSign (2 * (2 * M)) (blockIdx x) * blockSign (2 * (2 * M)) (blockIdx x)) *
            (wordU (blockOff x) * wordU (blockOff x)) := by ring
      _ = 1 * 1 := by rw [hε, hu]
      _ = 1 := by ring
  · have hv := wordV_sq (blockOff x)
    calc blockSign (2 * (2 * M)) (blockIdx x) * wordV (blockOff x) *
          (blockSign (2 * (2 * M)) (blockIdx x) * wordV (blockOff x))
        = (blockSign (2 * (2 * M)) (blockIdx x) * blockSign (2 * (2 * M)) (blockIdx x)) *
            (wordV (blockOff x) * wordV (blockOff x)) := by ring
      _ = 1 * 1 := by rw [hε, hv]
      _ = 1 := by ring

/-! ## The profile-class family: the same seeds, extended to every length `8 * r`

The certified pair `wordU`/`wordV` (`r = 3`) is the antiperiodic extension of two 8-bit seeds,
blocks `(a, -a, a)`/`(b, -b, b)`; the same two seeds extend to every length `8 * r` and keep the
exact zone, with the extremal spike at lag `8`. -/

/-- The first 8-bit seed: `wordU`'s own first block. -/
def seedU : Fin 8 → ℤ := ![-1, -1, 1, -1, -1, 1, 1, 1]

/-- The second 8-bit seed: `wordV`'s own first block. -/
def seedV : Fin 8 → ℤ := ![1, 1, -1, 1, -1, 1, 1, 1]

/-- The ℕ-indexed reading of the antiperiodic extension, at home beside `antiExt`:
`antiExt s r i = antiExtNat s i.val` by `rfl`. -/
private def antiExtNat (s : Fin 8 → ℤ) (i : ℕ) : ℤ :=
  s ⟨i % 8, Nat.mod_lt _ (by norm_num)⟩ * (-1) ^ (i / 8)

/-- **The antiperiodic extension.** An 8-bit seed repeated `r` times with alternating block sign,
`(a, -a, a, -a, …)` — the family whose `r = 3` member is the certified pair. -/
def antiExt (s : Fin 8 → ℤ) (r : ℕ) : Fin (8 * r) → ℤ :=
  fun i => s ⟨i.val % 8, Nat.mod_lt _ (by norm_num)⟩ * (-1) ^ (i.val / 8)

private lemma antiExt_eq_antiExtNat (s : Fin 8 → ℤ) (r : ℕ) (i : Fin (8 * r)) :
    antiExt s r i = antiExtNat s i.val := rfl

/-- **The extension read block by block**: at ℕ-index `8 * t + off` with `off < 8`, the extension
is the seed's own `off`-th value times the block sign `(-1) ^ t`. -/
private lemma antiExtNat_add_block (s : Fin 8 → ℤ) (t off : ℕ) (hoff : off < 8) :
    antiExtNat s (8 * t + off) = s ⟨off, hoff⟩ * (-1 : ℤ) ^ t := by
  unfold antiExtNat
  have hmod : (8 * t + off) % 8 = off := by omega
  have hdiv : (8 * t + off) / 8 = t := by omega
  simp only [hmod, hdiv]

private lemma s_eq_antiExtNat (s : Fin 8 → ℤ) (p : Fin 8) : s p = antiExtNat s p.val := by
  have h := antiExtNat_add_block s 0 p.val p.isLt
  simpa using h.symm

private lemma antiExt_one (s : Fin 8 → ℤ) : antiExt s 1 = s := by
  funext i
  unfold antiExt
  simp only [Nat.mod_eq_of_lt i.isLt, Nat.div_eq_of_lt i.isLt, pow_zero, mul_one]

/-- **The certified pair is the `r = 3` member.** -/
theorem antiExt_seedU_three : antiExt seedU 3 = wordU := by
  funext i
  fin_cases i <;> decide

/-- **The certified pair is the `r = 3` member.** -/
theorem antiExt_seedV_three : antiExt seedV 3 = wordV := by
  funext i
  fin_cases i <;> decide

/-- `seedU` is `±1`-valued, squared. -/
theorem seedU_sq (i : Fin 8) : seedU i * seedU i = 1 := by fin_cases i <;> decide

/-- `seedV` is `±1`-valued, squared. -/
theorem seedV_sq (i : Fin 8) : seedV i * seedV i = 1 := by fin_cases i <;> decide

private theorem seedU_abs_le_one (i : Fin 8) : |seedU i| ≤ 1 := by fin_cases i <;> decide

private theorem seedV_abs_le_one (i : Fin 8) : |seedV i| ≤ 1 := by fin_cases i <;> decide

/-- **The extension is `±1`-valued** whenever the seed is. -/
theorem abs_antiExt_le_one (s : Fin 8 → ℤ) (hs : ∀ i, |s i| ≤ 1) (r : ℕ) (i : Fin (8 * r)) :
    |antiExt s r i| ≤ 1 := by
  unfold antiExt
  rw [abs_mul]
  have h1 : |(-1 : ℤ) ^ (i.val / 8)| = 1 := by
    rcases Nat.even_or_odd (i.val / 8) with he | ho
    · rw [Even.neg_one_pow he]; norm_num
    · rw [Odd.neg_one_pow ho]; norm_num
  rw [h1, mul_one]
  exact hs _

/-- **The extension is exactly `±1`-valued** whenever the seed is: the seed's own square is `1` at
every offset, and the block sign squares away. -/
theorem antiExt_sq (s : Fin 8 → ℤ) (hs : ∀ i, s i * s i = 1) (r : ℕ) (i : Fin (8 * r)) :
    antiExt s r i * antiExt s r i = 1 := by
  unfold antiExt
  have h := hs ⟨i.val % 8, Nat.mod_lt _ (by norm_num)⟩
  have hpow : ((-1 : ℤ) ^ (i.val / 8)) * ((-1 : ℤ) ^ (i.val / 8)) = 1 := by
    rw [← pow_add, show i.val / 8 + i.val / 8 = 2 * (i.val / 8) by ring, pow_mul]
    norm_num
  calc s ⟨i.val % 8, Nat.mod_lt _ (by norm_num)⟩ * (-1 : ℤ) ^ (i.val / 8) *
        (s ⟨i.val % 8, Nat.mod_lt _ (by norm_num)⟩ * (-1 : ℤ) ^ (i.val / 8))
      = (s ⟨i.val % 8, Nat.mod_lt _ (by norm_num)⟩ * s ⟨i.val % 8, Nat.mod_lt _ (by norm_num)⟩) *
          ((-1 : ℤ) ^ (i.val / 8) * (-1 : ℤ) ^ (i.val / 8)) := by ring
    _ = 1 * 1 := by rw [h, hpow]
    _ = 1 := by ring

/-! ### The aperiodic-correlation closed forms, along the extension length -/

/-- `aperiodicCorr` as a plain ℕ-range sum, without the boundary `dite`: the top `d` positions are
exactly the ones the boundary condition excludes, once `d ≤ L`. -/
private lemma aperiodicCorr_eq_sum_range {L : ℕ} (w : Fin L → ℤ) (wn : ℕ → ℤ)
    (hw : ∀ p : Fin L, w p = wn p.val) (d : ℕ) (hd : d ≤ L) :
    aperiodicCorr w d = ∑ p ∈ Finset.range (L - d), wn p * wn (p + d) := by
  unfold aperiodicCorr
  have heq : ∀ p : Fin L, (if h : p.val + d < L then w p * w ⟨p.val + d, h⟩ else 0) =
      (if h : p.val + d < L then wn p.val * wn (p.val + d) else 0) := by
    intro p
    split_ifs with h
    · rw [hw p, hw ⟨p.val + d, h⟩]
    · rfl
  simp_rw [heq]
  rw [Fin.sum_univ_eq_sum_range (fun n => if h : n + d < L then wn n * wn (n + d) else 0) L]
  have heq2 : ∀ p ∈ Finset.range L,
      (if h : p + d < L then wn p * wn (p + d) else 0) =
      (if p + d < L then wn p * wn (p + d) else 0) := by
    intro p _; split_ifs <;> rfl
  rw [Finset.sum_congr rfl heq2, ← Finset.sum_filter]
  congr 1
  ext p
  simp only [Finset.mem_filter, Finset.mem_range]
  omega

/-- `crossTail` as a plain ℕ-range sum, the `crossTail` analogue of `aperiodicCorr_eq_sum_range`. -/
private lemma crossTail_eq_sum_range {L : ℕ} (w w' : Fin L → ℤ) (wn w'n : ℕ → ℤ)
    (hw : ∀ p : Fin L, w p = wn p.val) (hw' : ∀ p : Fin L, w' p = w'n p.val)
    (d : ℕ) (hd : d ≤ L) :
    crossTail w w' d = ∑ i ∈ Finset.range d, wn (L - d + i) * w'n i := by
  unfold crossTail
  have heq : ∀ p : Fin L, (if h : p.val < d then w ⟨L - d + p.val, by omega⟩ * w' p else 0) =
      (if h : p.val < d then wn (L - d + p.val) * w'n p.val else 0) := by
    intro p
    split_ifs with h
    · rw [hw ⟨L - d + p.val, by omega⟩, hw' p]
    · rfl
  simp_rw [heq]
  rw [Fin.sum_univ_eq_sum_range (fun n => if h : n < d then wn (L - d + n) * w'n n else 0) L]
  have heq2 : ∀ p ∈ Finset.range L,
      (if h : p < d then wn (L - d + p) * w'n p else 0) =
      (if p < d then wn (L - d + p) * w'n p else 0) := by
    intro p _; split_ifs <;> rfl
  rw [Finset.sum_congr rfl heq2, ← Finset.sum_filter]
  congr 1
  ext p
  simp only [Finset.mem_filter, Finset.mem_range]
  omega

/-- **The recursive step, along the extension length, at a zone lag.** Extending by one more block
adds the seed's own aperiodic correlation at `d` (the new block's within-block term, sign-squared
away) minus the seed's own cross-tail at `d` (the one new boundary, whose sign product is always
`-1`). -/
private theorem aperiodicCorr_antiExt_succ (s : Fin 8 → ℤ) (r d : ℕ) (hr : 1 ≤ r) (hd1 : 1 ≤ d)
    (hd7 : d ≤ 7) :
    aperiodicCorr (antiExt s (r + 1)) d = aperiodicCorr (antiExt s r) d +
      aperiodicCorr s d - crossTail s s d := by
  have hstep : aperiodicCorr (antiExt s (r + 1)) d =
      ∑ p ∈ Finset.range (8 * (r + 1) - d), antiExtNat s p * antiExtNat s (p + d) :=
    aperiodicCorr_eq_sum_range (antiExt s (r + 1)) (antiExtNat s)
      (fun p => antiExt_eq_antiExtNat s (r + 1) p) d (by omega)
  have hbase : aperiodicCorr (antiExt s r) d =
      ∑ p ∈ Finset.range (8 * r - d), antiExtNat s p * antiExtNat s (p + d) :=
    aperiodicCorr_eq_sum_range (antiExt s r) (antiExtNat s)
      (fun p => antiExt_eq_antiExtNat s r p) d (by omega)
  have hsplit : 8 * (r + 1) - d = (8 * r - d) + 8 := by omega
  rw [hstep, hsplit, Finset.sum_range_add, ← hbase]
  have hpiece : ∑ i ∈ Finset.range 8, antiExtNat s (8 * r - d + i) *
      antiExtNat s (8 * r - d + i + d) = aperiodicCorr s d - crossTail s s d := by
    have hac : aperiodicCorr s d =
        ∑ p ∈ Finset.range (8 - d), antiExtNat s p * antiExtNat s (p + d) :=
      aperiodicCorr_eq_sum_range s (antiExtNat s) (s_eq_antiExtNat s) d (by omega)
    have hct : crossTail s s d =
        ∑ i ∈ Finset.range d, antiExtNat s (8 - d + i) * antiExtNat s i :=
      crossTail_eq_sum_range s s (antiExtNat s) (antiExtNat s) (s_eq_antiExtNat s)
        (s_eq_antiExtNat s) d (by omega)
    rw [hac, hct]
    have hterm : ∀ i ∈ Finset.range 8, antiExtNat s (8 * r - d + i) *
        antiExtNat s (8 * r - d + i + d) =
        if i < d then -(antiExtNat s (8 - d + i) * antiExtNat s i)
        else antiExtNat s (i - d) * antiExtNat s i := by
      intro i hi
      rw [Finset.mem_range] at hi
      split_ifs with h
      · have e1 : 8 * r - d + i = 8 * (r - 1) + (8 - d + i) := by omega
        have e2 : 8 * (r - 1) + (8 - d + i) + d = 8 * r + i := by omega
        rw [e1, e2, antiExtNat_add_block s (r - 1) (8 - d + i) (by omega),
          antiExtNat_add_block s r i hi, ← s_eq_antiExtNat s ⟨8 - d + i, by omega⟩,
          ← s_eq_antiExtNat s ⟨i, hi⟩]
        have hodd : (-1 : ℤ) ^ (r - 1) * (-1) ^ r = -1 := by
          have hrr : r - 1 + r = 2 * (r - 1) + 1 := by omega
          rw [show (-1:ℤ)^(r-1) * (-1)^r = (-1:ℤ)^(r - 1 + r) by rw [pow_add], hrr,
            pow_add, pow_mul]
          norm_num
        calc s ⟨8 - d + i, by omega⟩ * (-1 : ℤ) ^ (r - 1) *
              (s ⟨i, hi⟩ * (-1 : ℤ) ^ r)
            = (s ⟨8 - d + i, by omega⟩ * s ⟨i, hi⟩) * ((-1:ℤ)^(r-1) * (-1)^r) := by ring
          _ = -(s ⟨8 - d + i, by omega⟩ * s ⟨i, hi⟩) := by rw [hodd]; ring
      · have hidlt : i - d < 8 := by omega
        have e1 : 8 * r - d + i = 8 * r + (i - d) := by omega
        have e2 : 8 * r + (i - d) + d = 8 * r + i := by omega
        rw [e1, e2, antiExtNat_add_block s r (i - d) hidlt, antiExtNat_add_block s r i hi,
          ← s_eq_antiExtNat s ⟨i - d, hidlt⟩, ← s_eq_antiExtNat s ⟨i, hi⟩]
        have heven : (-1 : ℤ) ^ r * (-1) ^ r = 1 := by
          rw [← pow_add, show r + r = 2 * r by ring, pow_mul]; norm_num
        calc s ⟨i - d, hidlt⟩ * (-1 : ℤ) ^ r * (s ⟨i, hi⟩ * (-1 : ℤ) ^ r)
            = (s ⟨i - d, hidlt⟩ * s ⟨i, hi⟩) * ((-1:ℤ)^r * (-1)^r) := by ring
          _ = s ⟨i - d, hidlt⟩ * s ⟨i, hi⟩ := by rw [heven]; ring
    rw [Finset.sum_congr rfl hterm, Finset.sum_ite]
    have hfilter1 : (Finset.range 8).filter (fun i => i < d) = Finset.range d := by
      ext i; simp only [Finset.mem_filter, Finset.mem_range]; omega
    rw [hfilter1, Finset.sum_neg_distrib]
    have hreindex : ∑ i ∈ (Finset.range 8).filter (fun i => ¬ i < d),
        antiExtNat s (i - d) * antiExtNat s i =
        ∑ j ∈ Finset.range (8 - d), antiExtNat s j * antiExtNat s (j + d) := by
      apply Finset.sum_nbij' (fun i => i - d) (fun j => j + d)
      · intro i hi
        simp only [Finset.mem_filter, Finset.mem_range] at hi
        simp only [Finset.mem_range]; omega
      · intro j hj
        simp only [Finset.mem_range] at hj
        simp only [Finset.mem_filter, Finset.mem_range]; omega
      · intro i hi
        simp only [Finset.mem_filter, Finset.mem_range] at hi
        omega
      · intro j hj
        simp only [Finset.mem_range] at hj
        omega
      · intro i hi
        simp only [Finset.mem_filter, Finset.mem_range] at hi
        have hh : i - d + d = i := by omega
        rw [hh]
    rw [hreindex]
    ring
  rw [hpiece]
  ring

/-- **The recursive step at the spike lag.** Extending by one more block adds exactly `-8`: the one
new boundary's sign product is always `-1`, and the seed's own square is `1` at every offset. -/
private theorem aperiodicCorr_antiExt_spike_succ (s : Fin 8 → ℤ) (hs : ∀ i, s i * s i = 1)
    (r : ℕ) (hr : 1 ≤ r) :
    aperiodicCorr (antiExt s (r + 1)) 8 = aperiodicCorr (antiExt s r) 8 - 8 := by
  have hstep : aperiodicCorr (antiExt s (r + 1)) 8 =
      ∑ p ∈ Finset.range (8 * (r + 1) - 8), antiExtNat s p * antiExtNat s (p + 8) :=
    aperiodicCorr_eq_sum_range (antiExt s (r + 1)) (antiExtNat s)
      (fun p => antiExt_eq_antiExtNat s (r + 1) p) 8 (by omega)
  have hbase : aperiodicCorr (antiExt s r) 8 =
      ∑ p ∈ Finset.range (8 * r - 8), antiExtNat s p * antiExtNat s (p + 8) :=
    aperiodicCorr_eq_sum_range (antiExt s r) (antiExtNat s)
      (fun p => antiExt_eq_antiExtNat s r p) 8 (by omega)
  have hsplit : 8 * (r + 1) - 8 = (8 * r - 8) + 8 := by omega
  rw [hstep, hsplit, Finset.sum_range_add, ← hbase]
  have hpiece : ∑ i ∈ Finset.range 8, antiExtNat s (8 * r - 8 + i) *
      antiExtNat s (8 * r - 8 + i + 8) = -8 := by
    have hterm : ∀ i ∈ Finset.range 8, antiExtNat s (8 * r - 8 + i) *
        antiExtNat s (8 * r - 8 + i + 8) = (-1 : ℤ) := by
      intro i hi
      rw [Finset.mem_range] at hi
      have e1 : 8 * r - 8 + i = 8 * (r - 1) + i := by omega
      have e2 : 8 * (r - 1) + i + 8 = 8 * r + i := by omega
      rw [e1, e2, antiExtNat_add_block s (r - 1) i hi, antiExtNat_add_block s r i hi]
      have hodd : (-1 : ℤ) ^ (r - 1) * (-1) ^ r = -1 := by
        have hrr : r - 1 + r = 2 * (r - 1) + 1 := by omega
        rw [show (-1:ℤ)^(r-1) * (-1)^r = (-1:ℤ)^(r - 1 + r) by rw [pow_add], hrr,
          pow_add, pow_mul]
        norm_num
      calc s ⟨i, hi⟩ * (-1 : ℤ) ^ (r - 1) * (s ⟨i, hi⟩ * (-1 : ℤ) ^ r)
          = (s ⟨i, hi⟩ * s ⟨i, hi⟩) * ((-1:ℤ)^(r-1) * (-1)^r) := by ring
        _ = 1 * (-1) := by rw [hs ⟨i, hi⟩, hodd]
        _ = -1 := by ring
    rw [Finset.sum_congr rfl hterm]
    simp
  rw [hpiece]
  ring

/-- **The zone closed form.** For every extension count `r ≥ 1` and every lag `1 ≤ d ≤ 7`, the two
seeds' aperiodic correlations still cancel exactly — the recursive step adds the SAME increment to
both, and that increment is zero at the seed level (an 8-element check, `interval_cases`/`decide`).
-/
theorem aperiodicCorr_antiExt_zone (r : ℕ) (hr : 1 ≤ r) {d : ℕ} (hd1 : 1 ≤ d) (hd7 : d ≤ 7) :
    aperiodicCorr (antiExt seedU r) d + aperiodicCorr (antiExt seedV r) d = 0 := by
  induction r, hr using Nat.le_induction with
  | base =>
    rw [antiExt_one, antiExt_one]
    interval_cases d <;> decide
  | succ n hn ih =>
    rw [aperiodicCorr_antiExt_succ seedU n d hn hd1 hd7,
      aperiodicCorr_antiExt_succ seedV n d hn hd1 hd7]
    have hzero : aperiodicCorr seedU d + aperiodicCorr seedV d -
        crossTail seedU seedU d - crossTail seedV seedV d = 0 := by
      interval_cases d <;> decide
    linarith [ih, hzero]

/-- **The spike closed form**, generic in a `±1`-valued seed: at extension count `r ≥ 1`, the
antiperiodic extension's own lag-`8` correlation is `-(8 * r - 8)`, each of the `r - 1` block
transitions contributing a full `-8` and the base case `r = 1` contributing `0` (lag `8` exceeds
the single block's own width). Both `seedU` and `seedV` satisfy the hypothesis, so they share this
closed form and are therefore equal at lag `8`. -/
theorem aperiodicCorr_antiExt_spike (s : Fin 8 → ℤ) (hs : ∀ i, s i * s i = 1) (r : ℕ)
    (hr : 1 ≤ r) :
    aperiodicCorr (antiExt s r) 8 = -(8 * (r : ℤ) - 8) := by
  induction r, hr using Nat.le_induction with
  | base =>
    rw [antiExt_one]
    unfold aperiodicCorr
    have h0 : ∀ p : Fin 8, (if h : p.val + 8 < 8 then s p * s ⟨p.val + 8, h⟩ else 0) = 0 := by
      intro p; rw [dif_neg]; omega
    simp_rw [h0]
    simp
  | succ n hn ih =>
    rw [aperiodicCorr_antiExt_spike_succ s hs n hn, ih]
    push_cast
    ring

/-! ### The total sum over one extension, and the outer partial-sum bound -/

private lemma antiExt_sum_eq_range (s : Fin 8 → ℤ) (r : ℕ) :
    ∑ p : Fin (8 * r), antiExt s r p = ∑ p ∈ Finset.range (8 * r), antiExtNat s p :=
  Fin.sum_univ_eq_sum_range (antiExtNat s) (8 * r)

private lemma sumRange_antiExtNat (s : Fin 8 → ℤ) (r : ℕ) :
    ∑ p ∈ Finset.range (8 * r), antiExtNat s p =
      (∑ j ∈ Finset.range r, (-1 : ℤ) ^ j) * (∑ i : Fin 8, s i) := by
  induction r with
  | zero => simp
  | succ n ih =>
    have hblock : ∑ i ∈ Finset.range 8, antiExtNat s (8 * n + i) =
        (-1 : ℤ) ^ n * ∑ i : Fin 8, s i := by
      rw [Finset.mul_sum, ← Fin.sum_univ_eq_sum_range (fun i => antiExtNat s (8 * n + i)) 8]
      apply Finset.sum_congr rfl
      intro p _
      rw [antiExtNat_add_block s n p.val p.isLt]
      ring
    rw [show 8 * (n + 1) = 8 * n + 8 by ring, Finset.sum_range_add, ih, hblock,
      Finset.sum_range_succ]
    ring

/-- **The total sum over one extension.** `Σ p, antiExt s r p` is the alternating block-count sum
times the seed's own total. -/
private theorem antiExt_sum (s : Fin 8 → ℤ) (r : ℕ) :
    ∑ p : Fin (8 * r), antiExt s r p =
      (∑ j ∈ Finset.range r, (-1 : ℤ) ^ j) * (∑ i : Fin 8, s i) := by
  rw [antiExt_sum_eq_range, sumRange_antiExtNat]

private lemma alt_sum_two_mul (t : ℕ) : ∑ j ∈ Finset.range (2 * t), (-1 : ℤ) ^ j = 0 := by
  induction t with
  | zero => simp
  | succ n ih =>
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ, ih]
    have he : Even (2 * n) := ⟨n, by ring⟩
    have ho : Odd (2 * n + 1) := ⟨n, by ring⟩
    rw [Even.neg_one_pow he, Odd.neg_one_pow ho]
    ring

private lemma alt_sum_two_mul_add_one (t : ℕ) :
    ∑ j ∈ Finset.range (2 * t + 1), (-1 : ℤ) ^ j = 1 := by
  rw [Finset.sum_range_succ, alt_sum_two_mul]
  have he : Even (2 * t) := ⟨t, by ring⟩
  rw [Even.neg_one_pow he]
  ring

private lemma abs_alt_sum_le_one (r : ℕ) : |∑ j ∈ Finset.range r, (-1 : ℤ) ^ j| ≤ 1 := by
  rcases Nat.even_or_odd r with ⟨t, ht⟩ | ⟨t, ht⟩
  · rw [ht, ← two_mul, alt_sum_two_mul]; norm_num
  · rw [ht, alt_sum_two_mul_add_one]; norm_num

private lemma antiExt_wordSumAtNat_even (r t : ℕ) :
    (∑ p : Fin (8 * r), wordAtNat (antiExt seedU r) (antiExt seedV r) (2 * t) p) = 0 := by
  have heq : wordAtNat (antiExt seedU r) (antiExt seedV r) (2 * t) = antiExt seedU r := by
    unfold wordAtNat; rw [if_pos ⟨t, two_mul t⟩]
  rw [heq, antiExt_sum]
  have hsum0 : (∑ i : Fin 8, seedU i) = 0 := by decide
  rw [hsum0, mul_zero]

private lemma antiExt_wordSumAtNat_odd (r t : ℕ) :
    (∑ p : Fin (8 * r), wordAtNat (antiExt seedU r) (antiExt seedV r) (2 * t + 1) p) =
      (∑ j ∈ Finset.range r, (-1 : ℤ) ^ j) * 4 := by
  have heq : wordAtNat (antiExt seedU r) (antiExt seedV r) (2 * t + 1) = antiExt seedV r := by
    unfold wordAtNat; rw [if_neg (by rw [Nat.even_iff]; omega : ¬ Even (2 * t + 1))]
  rw [heq, antiExt_sum]
  have hsum4 : (∑ i : Fin 8, seedV i) = 4 := by decide
  rw [hsum4]

private lemma antiExt_wordSumPartial_two_mul (M r : ℕ) [NeZero (2 * (2 * M))] :
    ∀ t, 2 * t ≤ 2 * (2 * M) →
      (∑ j ∈ Finset.range (2 * t), signAtNat (blockSign (2 * (2 * M))) j *
          (∑ p : Fin (8 * r), wordAtNat (antiExt seedU r) (antiExt seedV r) j p)) =
        (∑ j ∈ Finset.range r, (-1 : ℤ) ^ j) * 4 * ∑ i ∈ Finset.range t, tmSign i := by
  intro t
  induction t with
  | zero => intro _; simp
  | succ n ih =>
    intro ht
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ,
      ih (by omega), signAtNat_blockSign_even _ n (by omega), antiExt_wordSumAtNat_even,
      signAtNat_blockSign_odd _ n (by omega), antiExt_wordSumAtNat_odd, Finset.sum_range_succ]
    ring

private lemma antiExt_wordSumPartial_two_mul_add_one (M r : ℕ) [NeZero (2 * (2 * M))] :
    ∀ t, 2 * t + 1 ≤ 2 * (2 * M) →
      (∑ j ∈ Finset.range (2 * t + 1), signAtNat (blockSign (2 * (2 * M))) j *
          (∑ p : Fin (8 * r), wordAtNat (antiExt seedU r) (antiExt seedV r) j p)) =
        (∑ j ∈ Finset.range r, (-1 : ℤ) ^ j) * 4 * ∑ i ∈ Finset.range t, tmSign i := by
  intro t ht
  rw [Finset.sum_range_succ, antiExt_wordSumPartial_two_mul M r t (by omega),
    signAtNat_blockSign_even _ t (by omega), antiExt_wordSumAtNat_even]
  ring

/-- **The family's own outer partial-sum bound**, the `abs_wordSumPartial_le_four` analogue: the
running signed sum of block-pair sums is bounded by `4` at every prefix, independent of both the
block-repetition count `M` and the extension count `r` — `seedU`'s zero total kills the even-block
terms, and `seedV`'s total-`4` term is scaled by an alternating count bounded by `1` in absolute
value (`abs_alt_sum_le_one`), just as the Thue–Morse partial sum was for the certified pair. -/
theorem abs_antiExt_sumPartial_le_four (M r : ℕ) [NeZero (2 * (2 * M))] (J : ℕ)
    (hJ : J ≤ 2 * (2 * M)) :
    |∑ j ∈ Finset.range J, signAtNat (blockSign (2 * (2 * M))) j *
        (∑ p : Fin (8 * r), wordAtNat (antiExt seedU r) (antiExt seedV r) j p)| ≤ (4 : ℤ) := by
  have hfour : ∀ t : ℕ,
      |(∑ j ∈ Finset.range r, (-1 : ℤ) ^ j) * 4 * ∑ i ∈ Finset.range t, tmSign i| ≤ 4 := by
    intro t
    have h1 := tmSign_partial_abs_le_one t
    have halt := abs_alt_sum_le_one r
    calc |(∑ j ∈ Finset.range r, (-1 : ℤ) ^ j) * 4 * ∑ i ∈ Finset.range t, tmSign i|
        = |∑ j ∈ Finset.range r, (-1 : ℤ) ^ j| * 4 * |∑ i ∈ Finset.range t, tmSign i| := by
          rw [abs_mul, abs_mul]; norm_num
      _ ≤ 1 * 4 * 1 :=
          mul_le_mul (mul_le_mul_of_nonneg_right halt (by norm_num)) h1 (abs_nonneg _)
            (by norm_num)
      _ = 4 := by ring
  rcases Nat.even_or_odd J with ⟨t, ht⟩ | ⟨t, ht⟩
  · rw [ht, ← two_mul, antiExt_wordSumPartial_two_mul M r t (by omega)]
    exact hfour t
  · rw [ht, antiExt_wordSumPartial_two_mul_add_one M r t (by omega)]
    exact hfour t

/-- The family's own sequence balances over the whole period, exactly as the certified pair's does
(`singlePrefix_blockSeq_wordU_wordV_full`): the full-period prefix is the `J = 2 * (2 * M)` case of
`antiExt_wordSumPartial_two_mul`, against `tmSign_balance`. -/
private theorem singlePrefix_blockSeq_antiExt_full (M r : ℕ) [NeZero (2 * (2 * M))]
    [NeZero r] :
    singlePrefix (blockSeq (antiExt seedU r) (antiExt seedV r) (blockSign (2 * (2 * M))))
      (2 * (2 * M) * (8 * r)) = 0 := by
  have hb := singlePrefix_blockSeq_blocks (antiExt seedU r) (antiExt seedV r)
    (blockSign (2 * (2 * M))) (2 * (2 * M)) le_rfl
  rw [hb, antiExt_wordSumPartial_two_mul M r (2 * M) le_rfl, tmSign_balance M, mul_zero]

/-- **The family's own period-zero fact.** -/
private theorem singlePrefix_blockSeq_antiExt_period_zero (M r : ℕ) [NeZero (2 * (2 * M))]
    [NeZero r] :
    ∑ t : ZMod (2 * (2 * M) * (8 * r)),
      blockSeq (antiExt seedU r) (antiExt seedV r) (blockSign (2 * (2 * M))) t = 0 := by
  rw [← singlePrefix_eq_full_sum]
  exact singlePrefix_blockSeq_antiExt_full M r

/-! ### The spike remainder bound, at general `r` -/

/-- **`blockRemainder` for the extension, as a plain range sum.** Once `plen ≤ 8 * r`, every
in-range term (`i + 8 < 8 * r`) reads `s1` against itself, and every wraparound term reads `s1`
against `s2` at the wrapped ℕ index — the `dite`-free reading `cyclicCorrWindow_blockSeq_spike`'s
own remainder needs. -/
private lemma blockRemainder_antiExt_eq (s1 s2 : Fin 8 → ℤ) (r : ℕ) [NeZero r] (η : ℤ)
    (plen : ℕ) (hplen : plen ≤ 8 * r) :
    blockRemainder (antiExt s1 r) (antiExt s2 r) η 8 plen =
      ∑ i ∈ Finset.range plen,
        if i + 8 < 8 * r then antiExtNat s1 i * antiExtNat s1 (i + 8)
        else η * (antiExtNat s1 i * antiExtNat s2 (i + 8 - 8 * r)) := by
  unfold blockRemainder
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mem_range] at hi
  have hiL : i < 8 * r := by omega
  rw [dif_pos hiL]
  split_ifs with h2
  · change antiExtNat s1 i * antiExtNat s1 (i + 8) = antiExtNat s1 i * antiExtNat s1 (i + 8)
    rfl
  · have hmod : (i + 8 - 8 * r) % (8 * r) = i + 8 - 8 * r := Nat.mod_eq_of_lt (by omega)
    change η * (antiExtNat s1 i * antiExtNat s2 ((i + 8 - 8 * r) % (8 * r))) =
      η * (antiExtNat s1 i * antiExtNat s2 (i + 8 - 8 * r))
    rw [hmod]

/-- **The spike remainder bound, at general `r`.** A crude but robust route: the in-range part is
EXACTLY `-1` per position (`s1`'s own square is `1`, and the two blocks straddling any in-range
pair carry opposite sign), so its `2 * L`-scaled deviation from the linear trend is a plain
`16 * L` triangle-inequality bound; the wraparound part is at most `8` terms, each bounded by `1`
in absolute value, contributing at most `16 * L` more. Looser than the certified pair's own tight
`14` (an `interval_cases` brute force that does not scale to symbolic `r`), but valid uniformly. -/
private theorem blockRemainder_antiExt_bound (s1 s2 : Fin 8 → ℤ) (hs1 : ∀ i, s1 i * s1 i = 1)
    (hs2 : ∀ i, s2 i * s2 i = 1) (r : ℕ) [NeZero r] (η : ℤ) (hη : η * η = 1) (plen : ℕ)
    (hplen : plen ≤ 8 * r) :
    |2 * (8 * r : ℤ) * blockRemainder (antiExt s1 r) (antiExt s2 r) η 8 plen -
        (plen : ℤ) * (aperiodicCorr (antiExt s1 r) 8 + aperiodicCorr (antiExt s2 r) 8)|
      ≤ 32 * (8 * r : ℤ) := by
  have hr1 : 1 ≤ r := NeZero.pos r
  have heq := blockRemainder_antiExt_eq s1 s2 r η plen hplen
  have hsp1 := aperiodicCorr_antiExt_spike s1 hs1 r hr1
  have hsp2 := aperiodicCorr_antiExt_spike s2 hs2 r hr1
  rw [heq, hsp1, hsp2]
  have hLcast : (8 * r : ℤ) = ((8 * r : ℕ) : ℤ) := by push_cast; ring
  rw [hLcast]
  set L : ℕ := 8 * r with hL
  set inLen : ℕ := min plen (L - 8) with hInLen
  have hsplitSum : ∑ i ∈ Finset.range plen,
      (if i + 8 < L then antiExtNat s1 i * antiExtNat s1 (i + 8)
        else η * (antiExtNat s1 i * antiExtNat s2 (i + 8 - L))) =
      (∑ i ∈ Finset.range inLen, antiExtNat s1 i * antiExtNat s1 (i + 8)) +
      (∑ i ∈ Finset.range (plen - inLen),
        η * (antiExtNat s1 (inLen + i) * antiExtNat s2 (inLen + i + 8 - L))) := by
    have hmin1 : inLen ≤ plen := by rw [hInLen]; exact Nat.min_le_left _ _
    have hmin2 : inLen ≤ L - 8 := by rw [hInLen]; exact Nat.min_le_right _ _
    have hmineq : inLen = plen ∨ inLen = L - 8 := by
      by_cases hc : plen ≤ L - 8
      · left; rw [hInLen, min_eq_left hc]
      · right; rw [hInLen, min_eq_right (by omega)]
    rw [show plen = inLen + (plen - inLen) by omega]
    rw [Finset.sum_range_add, Nat.add_sub_cancel_left]
    congr 1
    · apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mem_range] at hi
      rw [if_pos (by omega : i + 8 < L)]
    · apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mem_range] at hi
      rw [if_neg (by omega : ¬ inLen + i + 8 < L)]
  have hinExact : ∑ i ∈ Finset.range inLen, antiExtNat s1 i * antiExtNat s1 (i + 8) =
      -(inLen : ℤ) := by
    have hterm : ∀ i ∈ Finset.range inLen,
        antiExtNat s1 i * antiExtNat s1 (i + 8) = (-1 : ℤ) := by
      intro i hi
      rw [Finset.mem_range] at hi
      set t := i / 8 with hti
      have hoff : i % 8 < 8 := Nat.mod_lt _ (by norm_num)
      have hie : i = 8 * t + i % 8 := (Nat.div_add_mod i 8).symm
      have hie8 : 8 * t + i % 8 + 8 = 8 * (t + 1) + i % 8 := by ring
      rw [hie, hie8, antiExtNat_add_block s1 t (i % 8) hoff,
        antiExtNat_add_block s1 (t + 1) (i % 8) hoff]
      have hodd : (-1 : ℤ) ^ t * (-1) ^ (t + 1) = -1 := by
        rw [pow_succ]
        rcases Nat.even_or_odd t with he | ho
        · rw [Even.neg_one_pow he]; ring
        · rw [Odd.neg_one_pow ho]; ring
      calc s1 ⟨i % 8, hoff⟩ * (-1 : ℤ) ^ t * (s1 ⟨i % 8, hoff⟩ * (-1 : ℤ) ^ (t + 1))
          = (s1 ⟨i % 8, hoff⟩ * s1 ⟨i % 8, hoff⟩) * ((-1:ℤ)^t * (-1)^(t+1)) := by ring
        _ = 1 * (-1) := by rw [hs1 ⟨i % 8, hoff⟩, hodd]
        _ = -1 := by ring
    rw [Finset.sum_congr rfl hterm]
    simp
  have hcount : plen - inLen ≤ 8 := by omega
  have hwrapBound : |∑ i ∈ Finset.range (plen - inLen),
      η * (antiExtNat s1 (inLen + i) * antiExtNat s2 (inLen + i + 8 - L))| ≤ (8 : ℤ) := by
    calc |∑ i ∈ Finset.range (plen - inLen),
        η * (antiExtNat s1 (inLen + i) * antiExtNat s2 (inLen + i + 8 - L))|
        ≤ ∑ i ∈ Finset.range (plen - inLen),
            |η * (antiExtNat s1 (inLen + i) * antiExtNat s2 (inLen + i + 8 - L))| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i ∈ Finset.range (plen - inLen), (1 : ℤ) := by
          apply Finset.sum_le_sum
          intro i _
          have hb1 : |antiExtNat s1 (inLen + i)| ≤ 1 := by
            unfold antiExtNat
            rw [abs_mul]
            have hp : |s1 ⟨(inLen + i) % 8, Nat.mod_lt _ (by norm_num)⟩| ≤ 1 :=
              abs_le_one_of_sq_eq_one (hs1 _)
            have hp2 : |(-1 : ℤ) ^ ((inLen + i) / 8)| = 1 := by
              rcases Nat.even_or_odd ((inLen + i) / 8) with he | ho
              · rw [Even.neg_one_pow he]; norm_num
              · rw [Odd.neg_one_pow ho]; norm_num
            calc |s1 ⟨(inLen + i) % 8, Nat.mod_lt _ (by norm_num)⟩| *
                |(-1 : ℤ) ^ ((inLen + i) / 8)| ≤ 1 * 1 := by
                  apply mul_le_mul hp (le_of_eq hp2) (abs_nonneg _) (by norm_num)
              _ = 1 := by ring
          have hb2 : |antiExtNat s2 (inLen + i + 8 - L)| ≤ 1 := by
            unfold antiExtNat
            rw [abs_mul]
            have hp : |s2 ⟨(inLen + i + 8 - L) % 8, Nat.mod_lt _ (by norm_num)⟩| ≤ 1 :=
              abs_le_one_of_sq_eq_one (hs2 _)
            have hp2 : |(-1 : ℤ) ^ ((inLen + i + 8 - L) / 8)| = 1 := by
              rcases Nat.even_or_odd ((inLen + i + 8 - L) / 8) with he | ho
              · rw [Even.neg_one_pow he]; norm_num
              · rw [Odd.neg_one_pow ho]; norm_num
            calc |s2 ⟨(inLen + i + 8 - L) % 8, Nat.mod_lt _ (by norm_num)⟩| *
                |(-1 : ℤ) ^ ((inLen + i + 8 - L) / 8)| ≤ 1 * 1 := by
                  apply mul_le_mul hp (le_of_eq hp2) (abs_nonneg _) (by norm_num)
              _ = 1 := by ring
          calc |η * (antiExtNat s1 (inLen + i) * antiExtNat s2 (inLen + i + 8 - L))|
              = |η| * (|antiExtNat s1 (inLen + i)| * |antiExtNat s2 (inLen + i + 8 - L)|) := by
                rw [abs_mul, abs_mul]
            _ ≤ 1 * (1 * 1) := by
                have hηabs : |η| ≤ 1 := abs_le_one_of_sq_eq_one hη
                exact mul_le_mul hηabs (mul_le_mul hb1 hb2 (abs_nonneg _) (by norm_num))
                  (by positivity) (by norm_num)
            _ = 1 := by ring
      _ = (plen - inLen : ℕ) * (1 : ℤ) := by rw [Finset.sum_const, Finset.card_range]; ring
      _ ≤ 8 * (1 : ℤ) := by
          have hle8 : (plen - inLen : ℕ) ≤ 8 := hcount
          have hcast : ((plen - inLen : ℕ) : ℤ) ≤ 8 := by exact_mod_cast hle8
          nlinarith [hcast]
      _ = 8 := by ring
  rw [hsplitSum, hinExact]
  have hLge : (8 : ℤ) ≤ (L : ℤ) := by
    have h8L : 8 ≤ L := by rw [hL]; omega
    exact_mod_cast h8L
  have hInLenLe : (inLen : ℤ) ≤ (L : ℤ) := by
    have hle : inLen ≤ L := by omega
    exact_mod_cast hle
  have hInLenLe' : (inLen : ℤ) ≤ (L : ℤ) - 8 := by
    have hle : inLen ≤ L - 8 := Nat.min_le_right _ _
    have hcast : (inLen : ℤ) ≤ ((L - 8 : ℕ) : ℤ) := by exact_mod_cast hle
    rwa [Nat.cast_sub (by omega : 8 ≤ L)] at hcast
  have hPlenLe : (plen : ℤ) ≤ (L : ℤ) := by exact_mod_cast hplen
  have hPlenGe : (inLen : ℤ) ≤ (plen : ℤ) := by
    have hle : inLen ≤ plen := Nat.min_le_left _ _
    exact_mod_cast hle
  have hPlenSub : (plen : ℤ) - (inLen : ℤ) ≤ 8 := by
    have hle : inLen ≤ plen := Nat.min_le_left _ _
    have hsub : ((plen - inLen : ℕ) : ℤ) = (plen : ℤ) - (inLen : ℤ) := Nat.cast_sub hle
    rw [← hsub]
    exact_mod_cast hcount
  set W : ℤ := ∑ i ∈ Finset.range (plen - inLen),
    η * (antiExtNat s1 (inLen + i) * antiExtNat s2 (inLen + i + 8 - L)) with hW
  have key : |2 * (L : ℤ) * (-(inLen : ℤ) + W) - (plen : ℤ) * (-((L:ℤ) - 8) +
      -((L:ℤ) - 8))| ≤ 32 * (L : ℤ) := by
    have hexpand : 2 * (L : ℤ) * (-(inLen : ℤ) + W) - (plen : ℤ) * (-((L:ℤ) - 8) +
        -((L:ℤ) - 8)) =
        (2 * (plen : ℤ) * ((L:ℤ) - 8) - 2 * (L:ℤ) * (inLen:ℤ)) + 2 * (L:ℤ) * W := by
      ring
    rw [hexpand]
    have hpart1 : |2 * (plen : ℤ) * ((L:ℤ) - 8) - 2 * (L:ℤ) * (inLen:ℤ)| ≤ 16 * (L : ℤ) := by
      rw [abs_le]
      constructor
      · nlinarith [hInLenLe', hPlenGe, hLge, hInLenLe, hPlenLe, hPlenSub]
      · nlinarith [hInLenLe', hPlenGe, hLge, hInLenLe, hPlenLe, hPlenSub]
    have hpart2 : |2 * (L : ℤ) * W| ≤ 16 * (L : ℤ) := by
      rw [abs_mul]
      have h2L : |(2 : ℤ) * (L : ℤ)| = 2 * (L : ℤ) := by
        rw [abs_of_nonneg]; positivity
      rw [h2L]
      calc 2 * (L : ℤ) * |W| ≤ 2 * (L : ℤ) * 8 := by
            apply mul_le_mul_of_nonneg_left hwrapBound (by positivity)
        _ = 16 * (L : ℤ) := by ring
    calc |(2 * (plen : ℤ) * ((L:ℤ) - 8) - 2 * (L:ℤ) * (inLen:ℤ)) + 2 * (L:ℤ) * W|
        ≤ |2 * (plen : ℤ) * ((L:ℤ) - 8) - 2 * (L:ℤ) * (inLen:ℤ)| + |2 * (L:ℤ) * W| :=
          abs_add_le _ _
      _ ≤ 16 * (L:ℤ) + 16 * (L:ℤ) := by linarith [hpart1, hpart2]
      _ = 32 * (L:ℤ) := by ring
  linarith [key]

/-! ### The certified corollaries' proofs, at general `r` -/

/-- **The zone window corollary, at general `r`.** `cyclicCorrWindow_blockSeq_zone`'s own proof,
with the certified pair's word facts replaced by the family's (`abs_antiExt_le_one`,
`aperiodicCorr_antiExt_zone`) and `24` by `8 * r`; the block-transition sign facts
(`blockSign_transition_even/odd`, `hPeven_blockSign`, `hPodd_blockSign`) are word-free and carry
over unchanged. -/
theorem cyclicCorrWindow_blockSeq_family_zone (M r : ℕ) [NeZero (2 * (2 * M))] [NeZero r]
    {d : ℕ} (hd1 : 1 ≤ d) (hd7 : d ≤ 7) (p n : ℕ) :
    |cyclicCorrWindow (blockSeq (antiExt seedU r) (antiExt seedV r) (blockSign (2 * (2 * M))))
        d p n| ≤ 2 * ((2 + 2 * 1) * (8 * r : ℤ)) := by
  have h := cyclicCorrWindow_blockSeq_zone rfl (antiExt seedU r) (antiExt seedV r)
    (blockSign (2 * (2 * M))) (blockSign_sq _) (abs_antiExt_le_one seedU seedU_abs_le_one r)
    (abs_antiExt_le_one seedV seedV_abs_le_one r) hd1 (le_refl d)
    (by have hr1 := NeZero.pos r; omega)
    (aperiodicCorr_antiExt_zone r (NeZero.pos r) hd1 hd7) (blockSign_transition_even M)
    (blockSign_transition_odd M) 1 (hPeven_blockSign M) (hPodd_blockSign M) p n
  push_cast at h ⊢
  linarith [h]

/-- **The spike window corollary, at general `r ≥ 2`.** `cyclicCorrWindow_blockSeq_spike`'s own
proof, with the certified pair's word facts and remainder bound replaced by the family's
(`abs_antiExt_le_one`, `aperiodicCorr_antiExt_spike`, `blockRemainder_antiExt_bound`) and `24` by
`8 * r`; the remainder constant is `32`, the family's own crude bound, in place of the certified
pair's tight `14` (`blockRemainder_antiExt_bound`'s own docstring). `r ≥ 2` is needed for the lag
`8` to stay below the extension's own length `8 * r`. -/
theorem cyclicCorrWindow_blockSeq_family_spike (M r : ℕ) [NeZero (2 * (2 * M))] [NeZero r]
    (hr2 : 2 ≤ r) (p n : ℕ) :
    |2 * (8 * r : ℤ) *
        cyclicCorrWindow (blockSeq (antiExt seedU r) (antiExt seedV r) (blockSign (2 * (2 * M))))
          8 p n -
      (n : ℤ) * (aperiodicCorr (antiExt seedU r) 8 + aperiodicCorr (antiExt seedV r) 8)| ≤
      2 * ((4 * 1 * (8 : ℤ) + 32) * (8 * r : ℤ)) := by
  have h := cyclicCorrWindow_blockSeq_spike rfl (antiExt seedU r) (antiExt seedV r)
    (blockSign (2 * (2 * M))) (blockSign_sq _) (abs_antiExt_le_one seedU seedU_abs_le_one r)
    (abs_antiExt_le_one seedV seedV_abs_le_one r) (by norm_num) (by omega)
    (blockSign_transition_even M) (blockSign_transition_odd M)
    (by rw [aperiodicCorr_antiExt_spike seedU seedU_sq r (by omega),
        aperiodicCorr_antiExt_spike seedV seedV_sq r (by omega)])
    1 (hPeven_blockSign M) (hPodd_blockSign M) 32
    (blockRemainder_antiExt_bound seedU seedV seedU_sq seedV_sq r)
    (fun η hη plen hplen => by
      have hb := blockRemainder_antiExt_bound seedV seedU seedV_sq seedU_sq r η hη plen hplen
      rwa [add_comm (aperiodicCorr (antiExt seedV r) 8) (aperiodicCorr (antiExt seedU r) 8)] at hb)
    p n
  push_cast at h ⊢
  linarith [h]

/-- **The single-site window corollary, at general `r`.** `singleWindow_blockSeq_bound`'s own
proof, with the certified pair's word facts and outer partial-sum bound replaced by the family's
(`abs_antiExt_le_one`, `singlePrefix_blockSeq_antiExt_period_zero`,
`abs_antiExt_sumPartial_le_four`) and `24` by `8 * r`. -/
theorem singleWindow_blockSeq_family_bound (M r : ℕ) [NeZero (2 * (2 * M))] [NeZero r]
    (p n : ℕ) :
    |singleWindow (blockSeq (antiExt seedU r) (antiExt seedV r) (blockSign (2 * (2 * M)))) p n|
      ≤ 2 * ((4 : ℤ) + 8 * r) :=
  singleWindow_blockSeq_bound (antiExt seedU r) (antiExt seedV r) (blockSign (2 * (2 * M)))
    (blockSign_sq _) (abs_antiExt_le_one seedU seedU_abs_le_one r)
    (abs_antiExt_le_one seedV seedV_abs_le_one r)
    (singlePrefix_blockSeq_antiExt_period_zero M r) 4 (abs_antiExt_sumPartial_le_four M r) p n

/-! ## A second certified pair: literal `2`, length `22`, spike lag `6`

A second word pair, found by exhaustive search (`../annex/probes/e1_shifted_spike_pair.py`,
committed and self-asserting): length `22`, with its spike — the lag where the two words'
aperiodic correlations agree rather than cancel — at `6` instead of the certified pair's `8`. This
is what makes literal `2` (rather than `0`) the rule this pair identifies, since the schedule's own
offset `a` correlates against lag `8 - a` (`BlockPairObservability.chiProd_eq_cyclicCorrWindow`),
and `8 - 2 = 6`. Every lemma below mirrors the certified pair's own instance section (`wordU`/
`wordV` through `blockSeq_wordU_wordV_sq`), transposed to this pair, its length, and its spike lag;
only the window-level bounds are stated, since the profile-class criterion needs no more. -/

/-- The first length-`22` word of the second certified pair. -/
def wordU2 : Fin 22 → ℤ :=
  ![-1, -1, -1, 1, -1, 1, 1, 1, 1, -1, 1, -1, -1, -1, -1, 1, -1, 1, 1, 1, 1, -1]

/-- The second length-`22` word of the second certified pair. -/
def wordV2 : Fin 22 → ℤ :=
  ![-1, -1, 1, -1, -1, -1, 1, 1, -1, 1, 1, 1, -1, -1, 1, -1, -1, -1, 1, 1, -1, 1]

private lemma aperiodicCorr_wordU2_wordV2_zone {d : ℕ} (hd1 : 1 ≤ d) (hd8 : d ≤ 8) (hd6 : d ≠ 6) :
    aperiodicCorr wordU2 d + aperiodicCorr wordV2 d = 0 := by
  interval_cases d <;> first | omega | decide

private lemma aperiodicCorr_wordU2_wordV2_spike :
    aperiodicCorr wordU2 6 + aperiodicCorr wordV2 6 = -32 := by decide

private lemma wordU2_abs_le_one (p : Fin 22) : |wordU2 p| ≤ 1 := by fin_cases p <;> decide

private lemma wordV2_abs_le_one (p : Fin 22) : |wordV2 p| ≤ 1 := by fin_cases p <;> decide

private lemma aperiodicCorr_wordU2_eq_wordV2_spike :
    aperiodicCorr wordU2 6 = aperiodicCorr wordV2 6 := by decide

private lemma hRemU2_wordU2_wordV2 (η : ℤ) (hη : η * η = 1) (r : ℕ) (hr : r ≤ 22) :
    |2 * (22 : ℤ) * blockRemainder wordU2 wordV2 η 6 r -
        (r : ℤ) * (aperiodicCorr wordU2 6 + aperiodicCorr wordV2 6)| ≤ (10 : ℤ) * 22 := by
  rcases eq_one_or_neg_one_of_sq_eq_one hη with rfl | rfl <;> interval_cases r <;> decide

private lemma hRemV2_wordU2_wordV2 (η : ℤ) (hη : η * η = 1) (r : ℕ) (hr : r ≤ 22) :
    |2 * (22 : ℤ) * blockRemainder wordV2 wordU2 η 6 r -
        (r : ℤ) * (aperiodicCorr wordU2 6 + aperiodicCorr wordV2 6)| ≤ (10 : ℤ) * 22 := by
  rcases eq_one_or_neg_one_of_sq_eq_one hη with rfl | rfl <;> interval_cases r <;> decide

/-- **The zone window bound, instantiated at the second certified pair.** Every cyclic window at a
lag `1 ≤ d ≤ 8`, `d ≠ 6`, of arbitrary phase and length, deviates from zero by at most
`2 * (4 * 22)`. -/
theorem cyclicCorrWindow_blockSeq_wordU2_wordV2_zone (M : ℕ) [NeZero (2 * (2 * M))]
    {d : ℕ} (hd1 : 1 ≤ d) (hd8 : d ≤ 8) (hd6 : d ≠ 6) (p n : ℕ) :
    |cyclicCorrWindow (blockSeq wordU2 wordV2 (blockSign (2 * (2 * M)))) d p n| ≤
      2 * ((2 + 2 * 1) * (22 : ℤ)) :=
  cyclicCorrWindow_blockSeq_zone rfl wordU2 wordV2 (blockSign (2 * (2 * M))) (blockSign_sq _)
    wordU2_abs_le_one wordV2_abs_le_one hd1 (le_refl d) (by omega)
    (aperiodicCorr_wordU2_wordV2_zone hd1 hd8 hd6) (blockSign_transition_even M)
    (blockSign_transition_odd M) 1 (hPeven_blockSign M) (hPodd_blockSign M) p n

/-- **The spike window bound, instantiated at the second certified pair.** Every cyclic window at
the spike lag `6`, of arbitrary phase and length, has `2 * 22`-scaled trend deviation at most
`2 * ((4 * 6 + 10) * 22)`. -/
theorem cyclicCorrWindow_blockSeq_wordU2_wordV2_spike (M : ℕ) [NeZero (2 * (2 * M))] (p n : ℕ) :
    |2 * (22 : ℤ) * cyclicCorrWindow (blockSeq wordU2 wordV2 (blockSign (2 * (2 * M)))) 6 p n -
        (n : ℤ) * (aperiodicCorr wordU2 6 + aperiodicCorr wordV2 6)| ≤
      2 * ((4 * 1 * (6 : ℤ) + 10) * 22) :=
  cyclicCorrWindow_blockSeq_spike rfl wordU2 wordV2 (blockSign (2 * (2 * M))) (blockSign_sq _)
    wordU2_abs_le_one wordV2_abs_le_one (by norm_num) (by norm_num) (blockSign_transition_even M)
    (blockSign_transition_odd M) aperiodicCorr_wordU2_eq_wordV2_spike 1 (hPeven_blockSign M)
    (hPodd_blockSign M) 10 hRemU2_wordU2_wordV2 hRemV2_wordU2_wordV2 p n

/-! ### The single-site instance -/

private lemma wordU2_sum : (∑ p : Fin 22, wordU2 p) = 0 := by decide

private lemma wordV2_sum : (∑ p : Fin 22, wordV2 p) = -2 := by decide

private lemma wordSumAtNat_wordU2_wordV2_even (t : ℕ) :
    (∑ p : Fin 22, wordAtNat wordU2 wordV2 (2 * t) p) = 0 := by
  have heq : wordAtNat wordU2 wordV2 (2 * t) = wordU2 := by
    unfold wordAtNat; rw [if_pos ⟨t, two_mul t⟩]
  rw [heq, wordU2_sum]

private lemma wordSumAtNat_wordU2_wordV2_odd (t : ℕ) :
    (∑ p : Fin 22, wordAtNat wordU2 wordV2 (2 * t + 1) p) = -2 := by
  have heq : wordAtNat wordU2 wordV2 (2 * t + 1) = wordV2 := by
    unfold wordAtNat; rw [if_neg (by rw [Nat.even_iff]; omega : ¬ Even (2 * t + 1))]
  rw [heq, wordV2_sum]

/-- The running signed word-sum, at an even-length prefix: `wordU2`'s zero balance kills every
even-block term (`signAtNat_blockSign_even` reads the sign constantly `1` there), so the value is
`-2` times a Thue–Morse partial sum, `wordV2`'s own sum. -/
private lemma wordSumPartial_wordU2_wordV2_two_mul (M : ℕ) [NeZero (2 * (2 * M))] :
    ∀ t, 2 * t ≤ 2 * (2 * M) →
      (∑ j ∈ Finset.range (2 * t), signAtNat (blockSign (2 * (2 * M))) j *
          (∑ p : Fin 22, wordAtNat wordU2 wordV2 j p)) = -2 * ∑ i ∈ Finset.range t, tmSign i := by
  intro t
  induction t with
  | zero => intro _; simp
  | succ n ih =>
    intro ht
    have hstep : (∑ j ∈ Finset.range (2 * (n + 1)),
        signAtNat (blockSign (2 * (2 * M))) j * (∑ p : Fin 22, wordAtNat wordU2 wordV2 j p)) =
        (∑ j ∈ Finset.range (2 * n),
          signAtNat (blockSign (2 * (2 * M))) j * (∑ p : Fin 22, wordAtNat wordU2 wordV2 j p)) +
        signAtNat (blockSign (2 * (2 * M))) (2 * n) *
          (∑ p : Fin 22, wordAtNat wordU2 wordV2 (2 * n) p) +
        signAtNat (blockSign (2 * (2 * M))) (2 * n + 1) *
          (∑ p : Fin 22, wordAtNat wordU2 wordV2 (2 * n + 1) p) := by
      rw [show 2 * (n + 1) = 2 * n + 1 + 1 from by ring, Finset.sum_range_succ,
        Finset.sum_range_succ]
    rw [hstep, ih (by omega), signAtNat_blockSign_even _ n (by omega),
      wordSumAtNat_wordU2_wordV2_even, signAtNat_blockSign_odd _ n (by omega),
      wordSumAtNat_wordU2_wordV2_odd, Finset.sum_range_succ]
    ring

private lemma wordSumPartial_wordU2_wordV2_two_mul_add_one (M : ℕ) [NeZero (2 * (2 * M))] :
    ∀ t, 2 * t + 1 ≤ 2 * (2 * M) →
      (∑ j ∈ Finset.range (2 * t + 1), signAtNat (blockSign (2 * (2 * M))) j *
          (∑ p : Fin 22, wordAtNat wordU2 wordV2 j p)) = -2 * ∑ i ∈ Finset.range t, tmSign i := by
  intro t ht
  rw [Finset.sum_range_succ, wordSumPartial_wordU2_wordV2_two_mul M t (by omega),
    signAtNat_blockSign_even _ t (by omega), wordSumAtNat_wordU2_wordV2_even]
  ring

/-- **The running signed word-sum is bounded by `2`** at every prefix, independent of `M`:
`tmSign_partial_abs_le_one` transported along `wordSumPartial_wordU2_wordV2_two_mul`/
`_two_mul_add_one`. -/
private lemma abs_wordSumPartial_wordU2_wordV2_le_two (M : ℕ) [NeZero (2 * (2 * M))] (J : ℕ)
    (hJ : J ≤ 2 * (2 * M)) :
    |∑ j ∈ Finset.range J, signAtNat (blockSign (2 * (2 * M))) j *
        (∑ p : Fin 22, wordAtNat wordU2 wordV2 j p)| ≤ (2 : ℤ) := by
  have htwo : ∀ t : ℕ, |(-2 : ℤ) * ∑ i ∈ Finset.range t, tmSign i| ≤ (2 : ℤ) := by
    intro t
    have h1 := tmSign_partial_abs_le_one t
    have heq : |(-2 : ℤ) * ∑ i ∈ Finset.range t, tmSign i|
        = 2 * |∑ i ∈ Finset.range t, tmSign i| := by rw [abs_mul]; norm_num
    rw [heq]; linarith
  rcases Nat.even_or_odd J with ⟨t, ht⟩ | ⟨t, ht⟩
  · rw [ht, ← two_mul, wordSumPartial_wordU2_wordV2_two_mul M t (by omega)]
    exact htwo t
  · rw [ht, wordSumPartial_wordU2_wordV2_two_mul_add_one M t (by omega)]
    exact htwo t

private theorem singlePrefix_blockSeq_wordU2_wordV2_bound (M : ℕ) [NeZero (2 * (2 * M))] (T : ℕ)
    (hT : T ≤ 2 * (2 * M) * 22) :
    |singlePrefix (blockSeq wordU2 wordV2 (blockSign (2 * (2 * M)))) T| ≤ (2 : ℤ) + 22 :=
  singlePrefix_blockSeq_bound wordU2 wordV2 (blockSign (2 * (2 * M))) (blockSign_sq _)
    wordU2_abs_le_one wordV2_abs_le_one 2 (abs_wordSumPartial_wordU2_wordV2_le_two M) T hT

private lemma singlePrefix_blockSeq_wordU2_wordV2_full (M : ℕ) [NeZero (2 * (2 * M))] :
    singlePrefix (blockSeq wordU2 wordV2 (blockSign (2 * (2 * M)))) (2 * (2 * M) * 22) = 0 := by
  have hb := singlePrefix_blockSeq_blocks wordU2 wordV2 (blockSign (2 * (2 * M)))
    (2 * (2 * M)) le_rfl
  rw [hb, wordSumPartial_wordU2_wordV2_two_mul M (2 * M) le_rfl, tmSign_balance M, mul_zero]

private lemma singlePrefix_blockSeq_wordU2_wordV2_period_zero (M : ℕ) [NeZero (2 * (2 * M))] :
    ∑ t : ZMod (2 * (2 * M) * 22), blockSeq wordU2 wordV2 (blockSign (2 * (2 * M))) t = 0 := by
  rw [← singlePrefix_eq_full_sum]
  exact singlePrefix_blockSeq_wordU2_wordV2_full M

/-- **The single-site window bound, instantiated at the second certified pair.** Every cyclic
window of arbitrary phase and length deviates from zero by at most `2 * (2 + 22)`. -/
theorem singleWindow_blockSeq_wordU2_wordV2_bound (M : ℕ) [NeZero (2 * (2 * M))] (p n : ℕ) :
    |singleWindow (blockSeq wordU2 wordV2 (blockSign (2 * (2 * M)))) p n| ≤ 2 * ((2 : ℤ) + 22) :=
  singleWindow_blockSeq_bound wordU2 wordV2 (blockSign (2 * (2 * M))) (blockSign_sq _)
    wordU2_abs_le_one wordV2_abs_le_one (singlePrefix_blockSeq_wordU2_wordV2_period_zero M)
    2 (abs_wordSumPartial_wordU2_wordV2_le_two M) p n

private lemma wordU2_sq (p : Fin 22) : wordU2 p * wordU2 p = 1 := by fin_cases p <;> decide

private lemma wordV2_sq (p : Fin 22) : wordV2 p * wordV2 p = 1 := by fin_cases p <;> decide

/-- **The second certified design is exactly `±1`-valued**: `blockSeq` at this pair squares to `1`
everywhere, mirroring `blockSeq_wordU_wordV_sq`. -/
theorem blockSeq_wordU2_wordV2_sq (M : ℕ) [NeZero (2 * (2 * M))]
    (x : ZMod (2 * (2 * M) * 22)) :
    blockSeq wordU2 wordV2 (blockSign (2 * (2 * M))) x *
      blockSeq wordU2 wordV2 (blockSign (2 * (2 * M))) x = 1 := by
  unfold blockSeq
  have hε := blockSign_sq (2 * (2 * M)) (blockIdx x)
  split_ifs
  · have hu := wordU2_sq (blockOff x)
    calc blockSign (2 * (2 * M)) (blockIdx x) * wordU2 (blockOff x) *
          (blockSign (2 * (2 * M)) (blockIdx x) * wordU2 (blockOff x))
        = (blockSign (2 * (2 * M)) (blockIdx x) * blockSign (2 * (2 * M)) (blockIdx x)) *
            (wordU2 (blockOff x) * wordU2 (blockOff x)) := by ring
      _ = 1 * 1 := by rw [hε, hu]
      _ = 1 := by ring
  · have hv := wordV2_sq (blockOff x)
    calc blockSign (2 * (2 * M)) (blockIdx x) * wordV2 (blockOff x) *
          (blockSign (2 * (2 * M)) (blockIdx x) * wordV2 (blockOff x))
        = (blockSign (2 * (2 * M)) (blockIdx x) * blockSign (2 * (2 * M)) (blockIdx x)) *
            (wordV2 (blockOff x) * wordV2 (blockOff x)) := by ring
      _ = 1 * 1 := by rw [hε, hv]
      _ = 1 := by ring

end BlockPairProfile
