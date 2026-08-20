/-
Copyright (c) 2026 Mykola Palamarchuk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mykola Palamarchuk
-/
import ALT.GrowingComposite

/-!
# A substitution source: exact block correlations and non-periodicity
([Growth] §4 Definition 4.1, Proposition 4.2)

The fixed point of the primitive substitution `a → aabb, b → abba` under the letter reading
`a = false`, `b = true`, block-coded by the word `w = +−−−`. Reading the substitution's images
position by position gives a plain quaternary recursion for the fixed point itself, and the block
code gives an explicit observation process whose exact correlations are computed directly from that
recursion — no unique ergodicity, no Perron vector, no discrepancy theorem.

## Main results

* `subFix` — the substitution's fixed point, by its four-way recursion on `n % 4`.
* `subFix_four_mul`, `subFix_four_mul_add_one`, `subFix_four_mul_add_two`,
  `subFix_four_mul_add_three` — the recursion itself.
* `subFix_block_sum`, `subFix_block_lag1`, `subFix_block_lag2` — the three exact four-term block
  identities the recursion gives: the letter sum, the lag-1 product sum, and the lag-2 product sum
  over one block.
* `subFix_sum_abs_le_two`, `subFix_lag1_sum_abs_le_three`, `subFix_lag2_sum_abs_le` — the bounded
  partial sums the block identities telescope into, at every horizon: the lag-2 sum is within a
  small constant of the linear trend `-3n/4`, the other two are outright bounded.
* `subObs` — the block-coded observation, `w = +−−−` applied to `subFix`.
* `subObs_four_mul`, `subObs_four_mul_add_one`, `subObs_four_mul_add_two`,
  `subObs_four_mul_add_three` — the block code read off `subFix`.
* `subObs_single` — the observation's own window-deviation bound, at every phase and horizon.
* `subRho`, `subW` — the observation's exact lag correlations (`Fin 8`-indexed, lag `8 - a`) and
  an explicit window bound against them.
* `subObs_pair` — the two-offset window-deviation bound against `subRho`, at every phase, offset
  and horizon.
* `not_eventuallyPeriodic_subFix`, `not_eventuallyPeriodic_subObs` — neither the fixed point nor
  its observation is eventually periodic.

## Scope

Every window bound here is loose relative to what the exact block computation could deliver at a
single fixed phase: `subObs_single` and `subObs_pair` are proved by splitting an arbitrary window
into a block-aligned run (governed by the exact identities above) plus a short remainder, then
doubling the block-aligned bound to cover an arbitrary starting phase. Nothing here claims these
constants are sharp — only that they hold at every phase and horizon, which is what a window
profile needs. Nothing here uses `GrowingComposite`'s composite carrier; it is imported only for
`EventuallyPeriodic` and its transport lemmas.
-/

namespace SubstitutionSource

open ParityWalk Finset

/-! ## The fixed point -/

/-- **The substitution's fixed point.** The fixed point of `a → aabb, b → abba` under the letter
reading `a = false`, `b = true`: reading the substitution's images position by position gives
`subFix (4n) = false`, `subFix (4n+1) = subFix n`, `subFix (4n+2) = true`,
`subFix (4n+3) = !subFix n`, well-founded on `n / 4`. -/
def subFix (n : ℕ) : Bool :=
  if n % 4 = 0 then false
  else if n % 4 = 1 then subFix (n / 4)
  else if n % 4 = 2 then true
  else !subFix (n / 4)
termination_by n
decreasing_by
  all_goals (first
    | (have h := Nat.div_lt_self (n := n) (k := 4) (by omega) (by omega); omega))

theorem subFix_four_mul (n : ℕ) : subFix (4 * n) = false := by
  rw [subFix, if_pos (by omega : (4 * n) % 4 = 0)]

theorem subFix_four_mul_add_one (n : ℕ) : subFix (4 * n + 1) = subFix n := by
  rw [subFix, if_neg (by omega : ¬ (4 * n + 1) % 4 = 0), if_pos (by omega : (4 * n + 1) % 4 = 1),
    show (4 * n + 1) / 4 = n by omega]

theorem subFix_four_mul_add_two (n : ℕ) : subFix (4 * n + 2) = true := by
  rw [subFix, if_neg (by omega : ¬ (4 * n + 2) % 4 = 0), if_neg (by omega : ¬ (4 * n + 2) % 4 = 1),
    if_pos (by omega : (4 * n + 2) % 4 = 2)]

theorem subFix_four_mul_add_three (n : ℕ) : subFix (4 * n + 3) = !subFix n := by
  rw [subFix, if_neg (by omega : ¬ (4 * n + 3) % 4 = 0), if_neg (by omega : ¬ (4 * n + 3) % 4 = 1),
    if_neg (by omega : ¬ (4 * n + 3) % 4 = 2), show (4 * n + 3) / 4 = n by omega]

private theorem chi_false' : chi false = 1 := rfl
private theorem chi_true' : chi true = -1 := rfl
private theorem abs_chi_le_one (b : Bool) : |chi b| ≤ 1 := by cases b <;> norm_num [chi]

private theorem abs_sum_range_le (r : ℕ) (g : ℕ → ℝ) (hg : ∀ i, |g i| ≤ 1) :
    |∑ i ∈ range r, g i| ≤ r := by
  calc |∑ i ∈ range r, g i| ≤ ∑ i ∈ range r, |g i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ range r, (1 : ℝ) := Finset.sum_le_sum (fun i _ => hg i)
    _ = r := by simp

private theorem shift_bound (f : ℕ → ℝ) (C : ℝ) (hC : ∀ N, |∑ u ∈ range N, f u| ≤ C)
    (c n : ℕ) : |∑ t ∈ range n, f (c + t)| ≤ 2 * C := by
  have hsplit : ∑ t ∈ range n, f (c + t) = ∑ u ∈ range (c + n), f u - ∑ u ∈ range c, f u := by
    have := Finset.sum_range_add f c n
    linarith [this]
  rw [hsplit]
  have h1 := hC (c + n)
  have h2 := hC c
  calc |∑ u ∈ range (c + n), f u - ∑ u ∈ range c, f u|
      ≤ |∑ u ∈ range (c + n), f u| + |∑ u ∈ range c, f u| := abs_sub _ _
    _ ≤ C + C := by linarith
    _ = 2 * C := by ring

/-! ## The exact block identities -/

/-- **The block letter sum, exact.** Over any four consecutive values starting at a multiple of
`4`, the characters cancel completely: `1 + s - 1 - s = 0` with `s = χ(subFix n)`. -/
theorem subFix_block_sum (n : ℕ) :
    ∑ i ∈ range 4, chi (subFix (4 * n + i)) = 0 := by
  have e0 : subFix (4 * n + 0) = false := by rw [Nat.add_zero]; exact subFix_four_mul n
  have e1 : subFix (4 * n + 1) = subFix n := subFix_four_mul_add_one n
  have e2 : subFix (4 * n + 2) = true := subFix_four_mul_add_two n
  have e3 : subFix (4 * n + 3) = !subFix n := subFix_four_mul_add_three n
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, e0, e1, e2, e3, chi_not,
    chi_false', chi_true']
  ring

/-- **The block lag-1 product sum, exact.** The four consecutive products
`s, -s, s, -s` cancel completely. -/
theorem subFix_block_lag1 (n : ℕ) :
    ∑ i ∈ range 4, chi (subFix (4 * n + i)) * chi (subFix (4 * n + i + 1)) = 0 := by
  have e0 : subFix (4 * n + 0) = false := by rw [Nat.add_zero]; exact subFix_four_mul n
  have e1 : subFix (4 * n + 1) = subFix n := subFix_four_mul_add_one n
  have e2 : subFix (4 * n + 2) = true := subFix_four_mul_add_two n
  have e3 : subFix (4 * n + 3) = !subFix n := subFix_four_mul_add_three n
  have e4 : subFix (4 * n + 4) = false := by
    have h : 4 * n + 4 = 4 * (n + 1) := by ring
    rw [h]; exact subFix_four_mul (n + 1)
  have r1 : 4 * n + 0 + 1 = 4 * n + 1 := by ring
  have r2 : 4 * n + 1 + 1 = 4 * n + 2 := by ring
  have r3 : 4 * n + 2 + 1 = 4 * n + 3 := by ring
  have r4 : 4 * n + 3 + 1 = 4 * n + 4 := by ring
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, r1, r2, r3, r4, e0, e1, e2,
    e3, e4, chi_not, chi_false', chi_true']
  ring

/-- **The block lag-2 product sum, exact.** The four consecutive products are `-1, -1, -1, -s·s'`
with `s' = χ(subFix (n+1))`. Telescoped over `N` blocks this is where the linear trend `-3n/4`
comes from, up to the (separately bounded) lag-1 sum this displaces. -/
theorem subFix_block_lag2 (n : ℕ) :
    ∑ i ∈ range 4, chi (subFix (4 * n + i)) * chi (subFix (4 * n + i + 2))
      = -3 - chi (subFix n) * chi (subFix (n + 1)) := by
  have e0 : subFix (4 * n + 0) = false := by rw [Nat.add_zero]; exact subFix_four_mul n
  have e1 : subFix (4 * n + 1) = subFix n := subFix_four_mul_add_one n
  have e2 : subFix (4 * n + 2) = true := subFix_four_mul_add_two n
  have e3 : subFix (4 * n + 3) = !subFix n := subFix_four_mul_add_three n
  have e4 : subFix (4 * n + 4) = false := by
    have h : 4 * n + 4 = 4 * (n + 1) := by ring
    rw [h]; exact subFix_four_mul (n + 1)
  have e5 : subFix (4 * n + 5) = subFix (n + 1) := by
    have h : 4 * n + 5 = 4 * (n + 1) + 1 := by ring
    rw [h]; exact subFix_four_mul_add_one (n + 1)
  have r2 : 4 * n + 0 + 2 = 4 * n + 2 := by ring
  have r3 : 4 * n + 1 + 2 = 4 * n + 3 := by ring
  have r4 : 4 * n + 2 + 2 = 4 * n + 4 := by ring
  have r5 : 4 * n + 3 + 2 = 4 * n + 5 := by ring
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, r2, r3, r4, r5, e0, e1, e2,
    e3, e4, e5, chi_not, chi_false', chi_true']
  have hs : chi (subFix n) * chi (subFix n) = 1 := by cases subFix n <;> norm_num
  nlinarith [hs]

/-! ## The bounded partial sums -/

private theorem subFix_sum_four_mul (q : ℕ) : ∑ t ∈ range (4 * q), chi (subFix t) = 0 := by
  induction q with
  | zero => simp
  | succ q ih =>
    have hsplit : 4 * (q + 1) = 4 * q + 4 := by ring
    rw [hsplit, Finset.sum_range_add, ih, zero_add]
    exact subFix_block_sum q

/-- **The letter partial sum, bounded at every horizon.** -/
theorem subFix_sum_abs_le_two (n : ℕ) : |∑ t ∈ range n, chi (subFix t)| ≤ 2 := by
  have hn_eq : n = 4 * (n / 4) + n % 4 := (Nat.div_add_mod n 4).symm
  have hr4 : n % 4 < 4 := Nat.mod_lt n (by norm_num)
  conv_lhs => rw [hn_eq]
  rw [Finset.sum_range_add, subFix_sum_four_mul (n / 4), zero_add]
  set q := n / 4
  interval_cases h : (n % 4)
  · simp
  · simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    rw [show 4 * q + 0 = 4 * q by ring, subFix_four_mul q]
    norm_num [chi]
  · simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    rw [show 4 * q + 0 = 4 * q by ring, show 4 * q + 1 = 4 * q + 1 by ring, subFix_four_mul q,
      subFix_four_mul_add_one q]
    have h1 := abs_chi_le_one (subFix q)
    rw [abs_le] at h1 ⊢
    constructor <;> nlinarith [h1.1, h1.2, chi_false']
  · simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    rw [show 4 * q + 0 = 4 * q by ring, subFix_four_mul q, subFix_four_mul_add_one q,
      subFix_four_mul_add_two q]
    have h1 := abs_chi_le_one (subFix q)
    rw [abs_le] at h1 ⊢
    constructor <;> nlinarith [h1.1, h1.2, chi_false', chi_true']

private theorem subFix_lag1_sum_four_mul (q : ℕ) :
    ∑ t ∈ range (4 * q), chi (subFix t) * chi (subFix (t + 1)) = 0 := by
  induction q with
  | zero => simp
  | succ q ih =>
    have hsplit : 4 * (q + 1) = 4 * q + 4 := by ring
    rw [hsplit, Finset.sum_range_add, ih, zero_add]
    exact subFix_block_lag1 q

/-- **The lag-1 product partial sum, bounded at every horizon.** -/
theorem subFix_lag1_sum_abs_le_three (n : ℕ) :
    |∑ t ∈ range n, chi (subFix t) * chi (subFix (t + 1))| ≤ 3 := by
  set q := n / 4
  set r := n % 4 with hr
  have hn_eq : n = 4 * q + r := (Nat.div_add_mod n 4).symm
  have hr4 : r < 4 := Nat.mod_lt n (by norm_num)
  have hsum : ∑ t ∈ range n, chi (subFix t) * chi (subFix (t + 1))
      = ∑ t ∈ range (4 * q), chi (subFix t) * chi (subFix (t + 1))
        + ∑ i ∈ range r, chi (subFix (4 * q + i)) * chi (subFix (4 * q + i + 1)) := by
    conv_lhs => rw [hn_eq]
    exact Finset.sum_range_add _ _ _
  rw [hsum, subFix_lag1_sum_four_mul q, zero_add]
  have hRem := abs_sum_range_le r (fun i => chi (subFix (4 * q + i)) * chi (subFix (4 * q + i + 1)))
    (fun i => by
      have h1 := abs_chi_le_one (subFix (4 * q + i))
      have h2 := abs_chi_le_one (subFix (4 * q + i + 1))
      rw [abs_mul]
      nlinarith [abs_nonneg (chi (subFix (4 * q + i))), abs_nonneg (chi (subFix (4 * q + i + 1)))])
  have hrR : (r : ℝ) ≤ 3 := by exact_mod_cast (by omega : r ≤ 3)
  linarith [hRem, hrR]

private theorem subFix_lag2_sum_four_mul (q : ℕ) :
    ∑ t ∈ range (4 * q), chi (subFix t) * chi (subFix (t + 2))
      = -3 * (q : ℝ) - ∑ j ∈ range q, chi (subFix j) * chi (subFix (j + 1)) := by
  induction q with
  | zero => simp
  | succ q ih =>
    have hsplit : 4 * (q + 1) = 4 * q + 4 := by ring
    rw [hsplit, Finset.sum_range_add, ih, subFix_block_lag2 q, Finset.sum_range_succ]
    push_cast
    ring

/-- **The lag-2 product partial sum, within a small explicit constant of the linear trend `-3n/4`
at every horizon.** This is where `ρ₂ = -3/4` comes from: the trend is exact in the block-aligned
limit, and this is the bound off it, inherited entirely from the lag-1 bound the block identity
displaces. -/
theorem subFix_lag2_sum_abs_le (n : ℕ) :
    |∑ t ∈ range n, chi (subFix t) * chi (subFix (t + 2)) + 3 * (n : ℝ) / 4| ≤ 33 / 4 := by
  set q := n / 4
  set r := n % 4 with hr
  have hn_eq : n = 4 * q + r := (Nat.div_add_mod n 4).symm
  have hr4 : r < 4 := Nat.mod_lt n (by norm_num)
  have hsum : ∑ t ∈ range n, chi (subFix t) * chi (subFix (t + 2))
      = ∑ t ∈ range (4 * q), chi (subFix t) * chi (subFix (t + 2))
        + ∑ i ∈ range r, chi (subFix (4 * q + i)) * chi (subFix (4 * q + i + 2)) := by
    conv_lhs => rw [hn_eq]
    exact Finset.sum_range_add _ _ _
  rw [hsum, subFix_lag2_sum_four_mul q]
  have hL1 := subFix_lag1_sum_abs_le_three q
  have hRem := abs_sum_range_le r (fun i => chi (subFix (4 * q + i)) * chi (subFix (4 * q + i + 2)))
    (fun i => by
      have h1 := abs_chi_le_one (subFix (4 * q + i))
      have h2 := abs_chi_le_one (subFix (4 * q + i + 2))
      rw [abs_mul]
      nlinarith [abs_nonneg (chi (subFix (4 * q + i))), abs_nonneg (chi (subFix (4 * q + i + 2)))])
  have hrR : (r : ℝ) ≤ 3 := by exact_mod_cast (by omega : r ≤ 3)
  have hnR : (n : ℝ) = 4 * (q : ℝ) + r := by exact_mod_cast hn_eq
  rw [hnR]
  rw [abs_le] at hL1 hRem ⊢
  constructor <;> nlinarith [hL1.1, hL1.2, hRem.1, hRem.2, hrR]

/-! ## The block-coded observation -/

/-- **The block-coded observation.** The word `w = +−−−` applied to `subFix`:
`subObs (4m) = subFix m`, `subObs (4m + i) = !subFix m` for `i = 1, 2, 3`. -/
def subObs (t : ℕ) : Bool := if t % 4 = 0 then subFix (t / 4) else !subFix (t / 4)

theorem subObs_four_mul (n : ℕ) : subObs (4 * n) = subFix n := by
  rw [subObs, if_pos (by omega : (4 * n) % 4 = 0), show (4 * n) / 4 = n by omega]

theorem subObs_four_mul_add_one (n : ℕ) : subObs (4 * n + 1) = !subFix n := by
  rw [subObs, if_neg (by omega : ¬ (4 * n + 1) % 4 = 0), show (4 * n + 1) / 4 = n by omega]

theorem subObs_four_mul_add_two (n : ℕ) : subObs (4 * n + 2) = !subFix n := by
  rw [subObs, if_neg (by omega : ¬ (4 * n + 2) % 4 = 0), show (4 * n + 2) / 4 = n by omega]

theorem subObs_four_mul_add_three (n : ℕ) : subObs (4 * n + 3) = !subFix n := by
  rw [subObs, if_neg (by omega : ¬ (4 * n + 3) % 4 = 0), show (4 * n + 3) / 4 = n by omega]

/-! ## The observation's own window bounds -/

private theorem subObs_block_single (p : ℕ) :
    ∑ s ∈ range 4, chi (subObs (4 * p + s)) = -2 * chi (subFix p) := by
  have e0 : subObs (4 * p + 0) = subFix p := by rw [Nat.add_zero]; exact subObs_four_mul p
  have e1 : subObs (4 * p + 1) = !subFix p := subObs_four_mul_add_one p
  have e2 : subObs (4 * p + 2) = !subFix p := subObs_four_mul_add_two p
  have e3 : subObs (4 * p + 3) = !subFix p := subObs_four_mul_add_three p
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, e0, e1, e2, e3, chi_not]
  ring

private theorem subObs_sum_four_mul (q : ℕ) :
    ∑ u ∈ range (4 * q), chi (subObs u) = -2 * ∑ j ∈ range q, chi (subFix j) := by
  induction q with
  | zero => simp
  | succ q ih =>
    have hsplit : 4 * (q + 1) = 4 * q + 4 := by ring
    rw [hsplit, Finset.sum_range_add, ih, subObs_block_single q, Finset.sum_range_succ]
    ring

private theorem subObs_sum_abs_le (N : ℕ) : |∑ u ∈ range N, chi (subObs u)| ≤ 7 := by
  have hN_eq : N = 4 * (N / 4) + N % 4 := (Nat.div_add_mod N 4).symm
  have hr4 : N % 4 < 4 := Nat.mod_lt N (by norm_num)
  have hsum : ∑ u ∈ range N, chi (subObs u)
      = ∑ u ∈ range (4 * (N / 4)), chi (subObs u)
        + ∑ i ∈ range (N % 4), chi (subObs (4 * (N / 4) + i)) := by
    conv_lhs => rw [hN_eq]
    exact Finset.sum_range_add _ _ _
  rw [hsum, subObs_sum_four_mul (N / 4)]
  have h2 : |∑ j ∈ range (N / 4), chi (subFix j)| ≤ 2 := subFix_sum_abs_le_two (N / 4)
  have hRem := abs_sum_range_le (N % 4) (fun i => chi (subObs (4 * (N / 4) + i)))
    (fun i => by cases subObs (4 * (N / 4) + i) <;> norm_num [chi])
  have hrR : ((N % 4 : ℕ) : ℝ) ≤ 3 := by exact_mod_cast (by omega : N % 4 ≤ 3)
  calc |(-2) * ∑ j ∈ range (N / 4), chi (subFix j)
        + ∑ i ∈ range (N % 4), chi (subObs (4 * (N / 4) + i))|
      ≤ |(-2) * ∑ j ∈ range (N / 4), chi (subFix j)|
          + |∑ i ∈ range (N % 4), chi (subObs (4 * (N / 4) + i))| := abs_add_le _ _
    _ ≤ 4 + 3 := by
        rw [abs_mul]
        have h3 : |(-2 : ℝ)| = 2 := by norm_num
        rw [h3]
        nlinarith [h2, hRem, hrR]
    _ = 7 := by norm_num

/-- **The observation's window-deviation bound, at every phase and horizon.** -/
theorem subObs_single (c n : ℕ) : |∑ t ∈ range n, chi (subObs (c + t))| ≤ 14 := by
  have h := shift_bound (fun u => chi (subObs u)) 7 subObs_sum_abs_le c n
  linarith [h]

/-! ## The exact pair correlations -/

private theorem subObs_block_lag8 (p : ℕ) :
    ∑ s ∈ range 4, chi (subObs (4 * p + s)) * chi (subObs (4 * p + s + 8))
      = 4 * (chi (subFix p) * chi (subFix (p + 2))) := by
  have e0 : subObs (4 * p + 0) = subFix p := by rw [Nat.add_zero]; exact subObs_four_mul p
  have e1 : subObs (4 * p + 1) = !subFix p := subObs_four_mul_add_one p
  have e2 : subObs (4 * p + 2) = !subFix p := subObs_four_mul_add_two p
  have e3 : subObs (4 * p + 3) = !subFix p := subObs_four_mul_add_three p
  have f0 : subObs (4 * p + 0 + 8) = subFix (p + 2) := by
    have h : 4 * p + 0 + 8 = 4 * (p + 2) := by ring
    rw [h]; exact subObs_four_mul (p + 2)
  have f1 : subObs (4 * p + 1 + 8) = !subFix (p + 2) := by
    have h : 4 * p + 1 + 8 = 4 * (p + 2) + 1 := by ring
    rw [h]; exact subObs_four_mul_add_one (p + 2)
  have f2 : subObs (4 * p + 2 + 8) = !subFix (p + 2) := by
    have h : 4 * p + 2 + 8 = 4 * (p + 2) + 2 := by ring
    rw [h]; exact subObs_four_mul_add_two (p + 2)
  have f3 : subObs (4 * p + 3 + 8) = !subFix (p + 2) := by
    have h : 4 * p + 3 + 8 = 4 * (p + 2) + 3 := by ring
    rw [h]; exact subObs_four_mul_add_three (p + 2)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, e0, e1, e2, e3, f0, f1, f2,
    f3, chi_not]
  ring

private theorem subObs_block_lag7 (p : ℕ) :
    ∑ s ∈ range 4, chi (subObs (4 * p + s)) * chi (subObs (4 * p + s + 7))
      = -(chi (subFix p) * chi (subFix (p + 1))) + chi (subFix p) * chi (subFix (p + 2)) := by
  have e0 : subObs (4 * p + 0) = subFix p := by rw [Nat.add_zero]; exact subObs_four_mul p
  have e1 : subObs (4 * p + 1) = !subFix p := subObs_four_mul_add_one p
  have e2 : subObs (4 * p + 2) = !subFix p := subObs_four_mul_add_two p
  have e3 : subObs (4 * p + 3) = !subFix p := subObs_four_mul_add_three p
  have f0 : subObs (4 * p + 0 + 7) = !subFix (p + 1) := by
    have h : 4 * p + 0 + 7 = 4 * (p + 1) + 3 := by ring
    rw [h]; exact subObs_four_mul_add_three (p + 1)
  have f1 : subObs (4 * p + 1 + 7) = subFix (p + 2) := by
    have h : 4 * p + 1 + 7 = 4 * (p + 2) := by ring
    rw [h]; exact subObs_four_mul (p + 2)
  have f2 : subObs (4 * p + 2 + 7) = !subFix (p + 2) := by
    have h : 4 * p + 2 + 7 = 4 * (p + 2) + 1 := by ring
    rw [h]; exact subObs_four_mul_add_one (p + 2)
  have f3 : subObs (4 * p + 3 + 7) = !subFix (p + 2) := by
    have h : 4 * p + 3 + 7 = 4 * (p + 2) + 2 := by ring
    rw [h]; exact subObs_four_mul_add_two (p + 2)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, e0, e1, e2, e3, f0, f1, f2,
    f3, chi_not]
  ring

private theorem subObs_block_lag6 (p : ℕ) :
    ∑ s ∈ range 4, chi (subObs (4 * p + s)) * chi (subObs (4 * p + s + 6)) = 0 := by
  have e0 : subObs (4 * p + 0) = subFix p := by rw [Nat.add_zero]; exact subObs_four_mul p
  have e1 : subObs (4 * p + 1) = !subFix p := subObs_four_mul_add_one p
  have e2 : subObs (4 * p + 2) = !subFix p := subObs_four_mul_add_two p
  have e3 : subObs (4 * p + 3) = !subFix p := subObs_four_mul_add_three p
  have f0 : subObs (4 * p + 0 + 6) = !subFix (p + 1) := by
    have h : 4 * p + 0 + 6 = 4 * (p + 1) + 2 := by ring
    rw [h]; exact subObs_four_mul_add_two (p + 1)
  have f1 : subObs (4 * p + 1 + 6) = !subFix (p + 1) := by
    have h : 4 * p + 1 + 6 = 4 * (p + 1) + 3 := by ring
    rw [h]; exact subObs_four_mul_add_three (p + 1)
  have f2 : subObs (4 * p + 2 + 6) = subFix (p + 2) := by
    have h : 4 * p + 2 + 6 = 4 * (p + 2) := by ring
    rw [h]; exact subObs_four_mul (p + 2)
  have f3 : subObs (4 * p + 3 + 6) = !subFix (p + 2) := by
    have h : 4 * p + 3 + 6 = 4 * (p + 2) + 1 := by ring
    rw [h]; exact subObs_four_mul_add_one (p + 2)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, e0, e1, e2, e3, f0, f1, f2,
    f3, chi_not]
  ring

private theorem subObs_block_lag5 (p : ℕ) :
    ∑ s ∈ range 4, chi (subObs (4 * p + s)) * chi (subObs (4 * p + s + 5))
      = chi (subFix p) * chi (subFix (p + 1)) - chi (subFix p) * chi (subFix (p + 2)) := by
  have e0 : subObs (4 * p + 0) = subFix p := by rw [Nat.add_zero]; exact subObs_four_mul p
  have e1 : subObs (4 * p + 1) = !subFix p := subObs_four_mul_add_one p
  have e2 : subObs (4 * p + 2) = !subFix p := subObs_four_mul_add_two p
  have e3 : subObs (4 * p + 3) = !subFix p := subObs_four_mul_add_three p
  have f0 : subObs (4 * p + 0 + 5) = !subFix (p + 1) := by
    have h : 4 * p + 0 + 5 = 4 * (p + 1) + 1 := by ring
    rw [h]; exact subObs_four_mul_add_one (p + 1)
  have f1 : subObs (4 * p + 1 + 5) = !subFix (p + 1) := by
    have h : 4 * p + 1 + 5 = 4 * (p + 1) + 2 := by ring
    rw [h]; exact subObs_four_mul_add_two (p + 1)
  have f2 : subObs (4 * p + 2 + 5) = !subFix (p + 1) := by
    have h : 4 * p + 2 + 5 = 4 * (p + 1) + 3 := by ring
    rw [h]; exact subObs_four_mul_add_three (p + 1)
  have f3 : subObs (4 * p + 3 + 5) = subFix (p + 2) := by
    have h : 4 * p + 3 + 5 = 4 * (p + 2) := by ring
    rw [h]; exact subObs_four_mul (p + 2)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, e0, e1, e2, e3, f0, f1, f2,
    f3, chi_not]
  ring

private theorem subObs_block_lag4 (p : ℕ) :
    ∑ s ∈ range 4, chi (subObs (4 * p + s)) * chi (subObs (4 * p + s + 4))
      = 4 * (chi (subFix p) * chi (subFix (p + 1))) := by
  have e0 : subObs (4 * p + 0) = subFix p := by rw [Nat.add_zero]; exact subObs_four_mul p
  have e1 : subObs (4 * p + 1) = !subFix p := subObs_four_mul_add_one p
  have e2 : subObs (4 * p + 2) = !subFix p := subObs_four_mul_add_two p
  have e3 : subObs (4 * p + 3) = !subFix p := subObs_four_mul_add_three p
  have f0 : subObs (4 * p + 0 + 4) = subFix (p + 1) := by
    have h : 4 * p + 0 + 4 = 4 * (p + 1) := by ring
    rw [h]; exact subObs_four_mul (p + 1)
  have f1 : subObs (4 * p + 1 + 4) = !subFix (p + 1) := by
    have h : 4 * p + 1 + 4 = 4 * (p + 1) + 1 := by ring
    rw [h]; exact subObs_four_mul_add_one (p + 1)
  have f2 : subObs (4 * p + 2 + 4) = !subFix (p + 1) := by
    have h : 4 * p + 2 + 4 = 4 * (p + 1) + 2 := by ring
    rw [h]; exact subObs_four_mul_add_two (p + 1)
  have f3 : subObs (4 * p + 3 + 4) = !subFix (p + 1) := by
    have h : 4 * p + 3 + 4 = 4 * (p + 1) + 3 := by ring
    rw [h]; exact subObs_four_mul_add_three (p + 1)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, e0, e1, e2, e3, f0, f1, f2,
    f3, chi_not]
  ring

private theorem subObs_block_lag3 (p : ℕ) :
    ∑ s ∈ range 4, chi (subObs (4 * p + s)) * chi (subObs (4 * p + s + 3))
      = -1 + chi (subFix p) * chi (subFix (p + 1)) := by
  have e0 : subObs (4 * p + 0) = subFix p := by rw [Nat.add_zero]; exact subObs_four_mul p
  have e1 : subObs (4 * p + 1) = !subFix p := subObs_four_mul_add_one p
  have e2 : subObs (4 * p + 2) = !subFix p := subObs_four_mul_add_two p
  have e3 : subObs (4 * p + 3) = !subFix p := subObs_four_mul_add_three p
  have f0 : subObs (4 * p + 0 + 3) = !subFix p := by
    have h : 4 * p + 0 + 3 = 4 * p + 3 := by ring
    rw [h]; exact subObs_four_mul_add_three p
  have f1 : subObs (4 * p + 1 + 3) = subFix (p + 1) := by
    have h : 4 * p + 1 + 3 = 4 * (p + 1) := by ring
    rw [h]; exact subObs_four_mul (p + 1)
  have f2 : subObs (4 * p + 2 + 3) = !subFix (p + 1) := by
    have h : 4 * p + 2 + 3 = 4 * (p + 1) + 1 := by ring
    rw [h]; exact subObs_four_mul_add_one (p + 1)
  have f3 : subObs (4 * p + 3 + 3) = !subFix (p + 1) := by
    have h : 4 * p + 3 + 3 = 4 * (p + 1) + 2 := by ring
    rw [h]; exact subObs_four_mul_add_two (p + 1)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, e0, e1, e2, e3, f1, f2,
    f3, chi_not]
  have hs : chi (subFix p) * chi (subFix p) = 1 := by cases subFix p <;> norm_num
  nlinarith [hs]

private theorem subObs_block_lag2 (p : ℕ) :
    ∑ s ∈ range 4, chi (subObs (4 * p + s)) * chi (subObs (4 * p + s + 2)) = 0 := by
  have e0 : subObs (4 * p + 0) = subFix p := by rw [Nat.add_zero]; exact subObs_four_mul p
  have e1 : subObs (4 * p + 1) = !subFix p := subObs_four_mul_add_one p
  have e2 : subObs (4 * p + 2) = !subFix p := subObs_four_mul_add_two p
  have e3 : subObs (4 * p + 3) = !subFix p := subObs_four_mul_add_three p
  have f0 : subObs (4 * p + 0 + 2) = !subFix p := by
    have h : 4 * p + 0 + 2 = 4 * p + 2 := by ring
    rw [h]; exact subObs_four_mul_add_two p
  have f1 : subObs (4 * p + 1 + 2) = !subFix p := by
    have h : 4 * p + 1 + 2 = 4 * p + 3 := by ring
    rw [h]; exact subObs_four_mul_add_three p
  have f2 : subObs (4 * p + 2 + 2) = subFix (p + 1) := by
    have h : 4 * p + 2 + 2 = 4 * (p + 1) := by ring
    rw [h]; exact subObs_four_mul (p + 1)
  have f3 : subObs (4 * p + 3 + 2) = !subFix (p + 1) := by
    have h : 4 * p + 3 + 2 = 4 * (p + 1) + 1 := by ring
    rw [h]; exact subObs_four_mul_add_one (p + 1)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, e0, e1, e2, e3, f2,
    f3, chi_not]
  have hs : chi (subFix p) * chi (subFix p) = 1 := by cases subFix p <;> norm_num
  nlinarith [hs]

private theorem subObs_block_lag1 (p : ℕ) :
    ∑ s ∈ range 4, chi (subObs (4 * p + s)) * chi (subObs (4 * p + s + 1))
      = 1 - chi (subFix p) * chi (subFix (p + 1)) := by
  have e0 : subObs (4 * p + 0) = subFix p := by rw [Nat.add_zero]; exact subObs_four_mul p
  have e1 : subObs (4 * p + 1) = !subFix p := subObs_four_mul_add_one p
  have e2 : subObs (4 * p + 2) = !subFix p := subObs_four_mul_add_two p
  have e3 : subObs (4 * p + 3) = !subFix p := subObs_four_mul_add_three p
  have f0 : subObs (4 * p + 0 + 1) = !subFix p := by
    have h : 4 * p + 0 + 1 = 4 * p + 1 := by ring
    rw [h]; exact subObs_four_mul_add_one p
  have f1 : subObs (4 * p + 1 + 1) = !subFix p := by
    have h : 4 * p + 1 + 1 = 4 * p + 2 := by ring
    rw [h]; exact subObs_four_mul_add_two p
  have f2 : subObs (4 * p + 2 + 1) = !subFix p := by
    have h : 4 * p + 2 + 1 = 4 * p + 3 := by ring
    rw [h]; exact subObs_four_mul_add_three p
  have f3 : subObs (4 * p + 3 + 1) = subFix (p + 1) := by
    have h : 4 * p + 3 + 1 = 4 * (p + 1) := by ring
    rw [h]; exact subObs_four_mul (p + 1)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, e0, e1, e2, e3,
    f3, chi_not]
  have hs : chi (subFix p) * chi (subFix p) = 1 := by cases subFix p <;> norm_num
  nlinarith [hs]

private theorem subObs_pair_sum_four_mul (d : ℕ) (γ α β : ℝ)
    (hblock : ∀ p, ∑ s ∈ range 4, chi (subObs (4 * p + s)) * chi (subObs (4 * p + s + d))
                 = γ + α * (chi (subFix p) * chi (subFix (p + 1)))
                     + β * (chi (subFix p) * chi (subFix (p + 2))))
    (q : ℕ) :
    ∑ u ∈ range (4 * q), chi (subObs u) * chi (subObs (u + d))
      = γ * q + α * (∑ j ∈ range q, chi (subFix j) * chi (subFix (j + 1)))
          + β * (∑ j ∈ range q, chi (subFix j) * chi (subFix (j + 2))) := by
  induction q with
  | zero => simp
  | succ q ih =>
    have hsplit : 4 * (q + 1) = 4 * q + 4 := by ring
    rw [hsplit, Finset.sum_range_add, ih, hblock q, Finset.sum_range_succ, Finset.sum_range_succ]
    push_cast
    ring

private theorem subObs_pair_zero_bound (d : ℕ) (γ α β ρ C0 : ℝ) (hρ : ρ = γ / 4 - 3 * β / 16)
    (hC0 : (|α|) * 3 + (|β|) * (33 / 4) + 3 + 3 * (|ρ|) ≤ C0)
    (hblock : ∀ p, ∑ s ∈ range 4, chi (subObs (4 * p + s)) * chi (subObs (4 * p + s + d))
                 = γ + α * (chi (subFix p) * chi (subFix (p + 1)))
                     + β * (chi (subFix p) * chi (subFix (p + 2))))
    (N : ℕ) :
    |∑ u ∈ range N, (chi (subObs u) * chi (subObs (u + d)) - ρ)| ≤ C0 := by
  have hN_eq : N = 4 * (N / 4) + N % 4 := (Nat.div_add_mod N 4).symm
  have hr4 : N % 4 < 4 := Nat.mod_lt N (by norm_num)
  have hsum1 : ∑ u ∈ range N, (chi (subObs u) * chi (subObs (u + d)) - ρ)
      = (∑ u ∈ range N, chi (subObs u) * chi (subObs (u + d))) - N * ρ := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hsum2 : ∑ u ∈ range N, chi (subObs u) * chi (subObs (u + d))
      = ∑ u ∈ range (4 * (N / 4)), chi (subObs u) * chi (subObs (u + d))
        + ∑ i ∈ range (N % 4),
            chi (subObs (4 * (N / 4) + i)) * chi (subObs (4 * (N / 4) + i + d)) := by
    conv_lhs => rw [hN_eq]
    exact Finset.sum_range_add _ _ _
  rw [hsum1, hsum2, subObs_pair_sum_four_mul d γ α β hblock (N / 4)]
  set q := N / 4
  set r := N % 4
  have hL1 := subFix_lag1_sum_abs_le_three q
  have hL2 := subFix_lag2_sum_abs_le q
  have hRem := abs_sum_range_le r (fun i => chi (subObs (4 * q + i)) * chi (subObs (4 * q + i + d)))
    (fun i => by
      have h1 := abs_chi_le_one (subObs (4 * q + i))
      have h2 := abs_chi_le_one (subObs (4 * q + i + d))
      rw [abs_mul]
      nlinarith [abs_nonneg (chi (subObs (4 * q + i))), abs_nonneg (chi (subObs (4 * q + i + d)))])
  have hrR : (r : ℝ) ≤ 3 := by exact_mod_cast (by omega : r ≤ 3)
  have hNq : (N : ℝ) = 4 * (q : ℝ) + r := by exact_mod_cast hN_eq
  rw [abs_le] at hL1 hL2
  refine le_trans ?_ hC0
  have expand : γ * (q : ℝ) + α * (∑ j ∈ range q, chi (subFix j) * chi (subFix (j + 1)))
      + β * (∑ j ∈ range q, chi (subFix j) * chi (subFix (j + 2)))
      + ∑ i ∈ range r, chi (subObs (4 * q + i)) * chi (subObs (4 * q + i + d)) - (N : ℝ) * ρ
      = α * (∑ j ∈ range q, chi (subFix j) * chi (subFix (j + 1)))
        + β * ((∑ j ∈ range q, chi (subFix j) * chi (subFix (j + 2))) + 3 * (q : ℝ) / 4)
        + (∑ i ∈ range r, chi (subObs (4 * q + i)) * chi (subObs (4 * q + i + d)) - r * ρ)
        + (γ * (q : ℝ) - 4 * (q : ℝ) * ρ - β * 3 * (q : ℝ) / 4) := by
    rw [hNq]; ring
  rw [expand]
  have hlast : γ * (q : ℝ) - 4 * (q : ℝ) * ρ - β * 3 * (q : ℝ) / 4 = 0 := by rw [hρ]; ring
  rw [hlast, add_zero]
  have hrρ : |(r : ℝ) * ρ| = (r : ℝ) * (|ρ|) := by
    rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg r)]
  have hb3 : |∑ i ∈ range r, chi (subObs (4 * q + i)) * chi (subObs (4 * q + i + d)) - (r : ℝ) * ρ|
      ≤ (r : ℝ) + (r : ℝ) * (|ρ|) := by
    calc |∑ i ∈ range r, chi (subObs (4 * q + i)) * chi (subObs (4 * q + i + d)) - (r : ℝ) * ρ|
        ≤ |∑ i ∈ range r, chi (subObs (4 * q + i)) * chi (subObs (4 * q + i + d))|
            + |(r : ℝ) * ρ| := abs_sub _ _
      _ = |∑ i ∈ range r, chi (subObs (4 * q + i)) * chi (subObs (4 * q + i + d))|
            + (r : ℝ) * (|ρ|) := by rw [hrρ]
      _ ≤ (r : ℝ) + (r : ℝ) * (|ρ|) := by linarith [hRem]
  calc |α * (∑ j ∈ range q, chi (subFix j) * chi (subFix (j + 1)))
        + β * ((∑ j ∈ range q, chi (subFix j) * chi (subFix (j + 2))) + 3 * (q : ℝ) / 4)
        + (∑ i ∈ range r, chi (subObs (4 * q + i)) * chi (subObs (4 * q + i + d)) - r * ρ)|
      ≤ |α * (∑ j ∈ range q, chi (subFix j) * chi (subFix (j + 1)))|
        + |β * ((∑ j ∈ range q, chi (subFix j) * chi (subFix (j + 2))) + 3 * (q : ℝ) / 4)|
        + |∑ i ∈ range r, chi (subObs (4 * q + i)) * chi (subObs (4 * q + i + d)) - r * ρ| := by
        calc _
            ≤ _ + |(∑ i ∈ range r,
                chi (subObs (4 * q + i)) * chi (subObs (4 * q + i + d)) - r * ρ)| :=
              abs_add_le _ _
          _ ≤ _ := by
              have := abs_add_le (α * (∑ j ∈ range q, chi (subFix j) * chi (subFix (j + 1))))
                (β * ((∑ j ∈ range q, chi (subFix j) * chi (subFix (j + 2))) + 3 * (q : ℝ) / 4))
              linarith [this]
    _ ≤ (|α|) * 3 + (|β|) * (33 / 4) + ((r : ℝ) + (r : ℝ) * (|ρ|)) := by
        rw [abs_mul, abs_mul]
        have hb1 : |∑ j ∈ range q, chi (subFix j) * chi (subFix (j + 1))| ≤ 3 := by
          rw [abs_le]; exact ⟨hL1.1, hL1.2⟩
        have hb2 : |(∑ j ∈ range q, chi (subFix j) * chi (subFix (j + 2))) + 3 * (q : ℝ) / 4|
            ≤ 33 / 4 := by
          rw [abs_le]; exact ⟨hL2.1, hL2.2⟩
        gcongr
    _ ≤ (|α|) * 3 + (|β|) * (33 / 4) + 3 + 3 * (|ρ|) := by nlinarith [hrR, abs_nonneg ρ]

private theorem subObs_pair_generic (d aa : ℕ) (γ α β ρ C0 : ℝ) (had : aa + d = 8)
    (hρ : ρ = γ / 4 - 3 * β / 16)
    (hC0 : (|α|) * 3 + (|β|) * (33 / 4) + 3 + 3 * (|ρ|) ≤ C0)
    (hblock : ∀ p, ∑ s ∈ range 4, chi (subObs (4 * p + s)) * chi (subObs (4 * p + s + d))
                 = γ + α * (chi (subFix p) * chi (subFix (p + 1)))
                     + β * (chi (subFix p) * chi (subFix (p + 2))))
    (c n : ℕ) :
    |∑ t ∈ range n, chi (subObs (c + t + aa)) * chi (subObs (c + t + 8))
        - (n : ℝ) * ρ| ≤ 2 * C0 := by
  have key := shift_bound (fun u => chi (subObs u) * chi (subObs (u + d)) - ρ) C0
    (subObs_pair_zero_bound d γ α β ρ C0 hρ hC0 hblock) (c + aa) n
  have heq : ∀ t, (fun u => chi (subObs u) * chi (subObs (u + d)) - ρ) ((c + aa) + t)
      = chi (subObs (c + t + aa)) * chi (subObs (c + t + 8)) - ρ := by
    intro t
    simp only []
    congr 1
    congr 1
    · congr 1; congr 1; omega
    · congr 1; congr 1; omega
  simp only [heq] at key
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at key
  exact key

/-- **The exact lag correlations of `subObs`**, in the `Fin 8`-window indexing where `ρ a` is the
lag-`(8 - a)` correlation: `ρ = (-3/4, -3/16, 0, 3/16, 0, -1/4, 0, 1/4)`. Only the lag-`0, 1, 2`
correlations of `subFix` (`1, 0, -3/4`) ever enter, since every window lag from `1` to `8` reduces
to one of those three plus at most one exact `chi(subFix p)² = 1` term. -/
noncomputable def subRho : Fin 8 → ℝ := ![-3 / 4, -3 / 16, 0, 3 / 16, 0, -1 / 4, 0, 1 / 4]

/-- **An explicit window bound against `subRho`**, uniform over every offset. -/
noncomputable def subW : Fin 8 → ℝ := fun _ => 77

/-- **The two-offset window-deviation bound, at every phase, offset and horizon.** -/
theorem subObs_pair (c : ℕ) (a : Fin 8) (n : ℕ) :
    |∑ t ∈ range n, chi (subObs (c + t + (a : ℕ))) * chi (subObs (c + t + 8))
        - (n : ℝ) * subRho a| ≤ subW a := by
  have h77 : ∀ x : ℝ, x ≤ 77 → x ≤ subW a := fun x hx => by simpa [subW] using hx
  fin_cases a
  · exact h77 _ (le_trans
      (subObs_pair_generic 8 0 0 0 4 (subRho 0) (153 / 4) (by norm_num)
        (by simp [subRho]; try norm_num) (by simp [subRho]; try norm_num)
        (fun p => by rw [subObs_block_lag8 p]; ring) c n)
      (by norm_num))
  · exact h77 _ (le_trans
      (subObs_pair_generic 7 1 0 (-1) 1 (subRho 1) (237 / 16) (by norm_num)
        (by simp [subRho]; try norm_num) (by simp [subRho]; try norm_num)
        (fun p => by rw [subObs_block_lag7 p]; ring) c n)
      (by norm_num))
  · exact h77 _ (le_trans
      (subObs_pair_generic 6 2 0 0 0 (subRho 2) 3 (by norm_num) (by simp [subRho]; try norm_num)
        (by simp [subRho]; try norm_num) (fun p => by rw [subObs_block_lag6 p]; ring) c n)
      (by norm_num))
  · exact h77 _ (le_trans
      (subObs_pair_generic 5 3 0 1 (-1) (subRho 3) (237 / 16) (by norm_num)
        (by simp [subRho]; try norm_num) (by simp [subRho]; try norm_num)
        (fun p => by rw [subObs_block_lag5 p]; ring) c n)
      (by norm_num))
  · exact h77 _ (le_trans
      (subObs_pair_generic 4 4 0 4 0 (subRho 4) 15 (by norm_num) (by simp [subRho]; try norm_num)
        (by simp [subRho]; try norm_num) (fun p => by rw [subObs_block_lag4 p]; ring) c n)
      (by norm_num))
  · exact h77 _ (le_trans
      (subObs_pair_generic 3 5 (-1) 1 0 (subRho 5) (27 / 4) (by norm_num)
        (by simp [subRho]; try norm_num) (by simp [subRho]; try norm_num)
        (fun p => by rw [subObs_block_lag3 p]; ring) c n)
      (by norm_num))
  · exact h77 _ (le_trans
      (subObs_pair_generic 2 6 0 0 0 (subRho 6) 3 (by norm_num) (by simp [subRho]; try norm_num)
        (by simp [subRho]; try norm_num) (fun p => by rw [subObs_block_lag2 p]; ring) c n)
      (by norm_num))
  · exact h77 _ (le_trans
      (subObs_pair_generic 1 7 1 (-1) 0 (subRho 7) (27 / 4) (by norm_num)
        (by simp [subRho]; try norm_num) (by simp [subRho]; try norm_num)
        (fun p => by rw [subObs_block_lag1 p]; ring) c n)
      (by norm_num))

/-! ## Non-periodicity -/

private theorem subFix_not_eventually_const :
    ¬ ∃ (N' : ℕ) (b : Bool), ∀ m, N' ≤ m → subFix m = b := by
  rintro ⟨N', b, hconst⟩
  have h1 := hconst (4 * N') (by omega)
  have h2 := hconst (4 * N' + 2) (by omega)
  rw [subFix_four_mul] at h1
  rw [subFix_four_mul_add_two] at h2
  rw [← h1] at h2
  exact absurd h2 (by decide)

private theorem no_period_subFix :
    ∀ P, 0 < P → ∀ N, (∀ u, N ≤ u → subFix (u + P) = subFix u) → False := by
  intro P
  induction P using Nat.strong_induction_on with
  | _ P ih =>
    intro hP N hper
    have hPeq : P = 4 * (P / 4) + P % 4 := (Nat.div_add_mod P 4).symm
    have hr4 : P % 4 < 4 := Nat.mod_lt P (by norm_num)
    set k := P / 4
    interval_cases h : (P % 4)
    · have hk0 : 0 < k := by omega
      have hklt : k < P := by omega
      refine ih k hklt hk0 N (fun n hn => ?_)
      have e1 : subFix (4 * n + 1 + P) = subFix (4 * n + 1) := hper (4 * n + 1) (by omega)
      have hPk : 4 * n + 1 + P = 4 * (n + k) + 1 := by omega
      rw [hPk, subFix_four_mul_add_one, subFix_four_mul_add_one] at e1
      exact e1
    · exfalso
      apply subFix_not_eventually_const
      refine ⟨N + k, false, fun m hm => ?_⟩
      obtain ⟨n, rfl⟩ : ∃ n, m = n + k := ⟨m - k, by omega⟩
      have e1 : subFix (4 * n + P) = subFix (4 * n) := hper (4 * n) (by omega)
      rw [subFix_four_mul] at e1
      have hPk : 4 * n + P = 4 * (n + k) + 1 := by omega
      rw [hPk, subFix_four_mul_add_one] at e1
      exact e1
    · exfalso
      have e1 : subFix (4 * N + P) = subFix (4 * N) := hper (4 * N) (by omega)
      rw [subFix_four_mul] at e1
      have hPk : 4 * N + P = 4 * (N + k) + 2 := by omega
      rw [hPk, subFix_four_mul_add_two] at e1
      exact absurd e1.symm (by decide)
    · exfalso
      apply subFix_not_eventually_const
      refine ⟨N + k, true, fun m hm => ?_⟩
      obtain ⟨n, rfl⟩ : ∃ n, m = n + k := ⟨m - k, by omega⟩
      have e1 : subFix (4 * n + P) = subFix (4 * n) := hper (4 * n) (by omega)
      rw [subFix_four_mul] at e1
      have hPk : 4 * n + P = 4 * (n + k) + 3 := by omega
      rw [hPk, subFix_four_mul_add_three] at e1
      cases hb : subFix (n + k) <;> rw [hb] at e1; simp_all

/-- **Neither `subFix` nor its observation is eventually periodic.** The recursion pins
`subFix (4n) = false` and `subFix (4n + 2) = true`, so any eventual period `P` is forced to `4 ∣ P`
(any other residue collapses `subFix` to an eventually-constant sequence, ruled out directly); a
period `P = 4P'` then transports through `subFix (4n+1) = subFix n` to the smaller period `P'`,
giving an infinite descent — closed by strong induction on `P`. -/
theorem not_eventuallyPeriodic_subFix : ¬ GrowingComposite.EventuallyPeriodic subFix := by
  rintro ⟨P, N, hP, hper⟩
  exact no_period_subFix P hP N hper

/-- **`subObs` is not eventually periodic either.** A period `P` for `subObs` splits the same way:
`4 ∣ P` reduces, through `subObs`'s own block code, to an eventual period for `subFix` itself
(`not_eventuallyPeriodic_subFix`); the other residues either force `subFix (n+k) = !subFix (n+k)`
directly (two adjacent instantiations) or, at the remaining residue, give `subFix` an
anti-periodicity that composes with itself into a genuine period. -/
theorem not_eventuallyPeriodic_subObs : ¬ GrowingComposite.EventuallyPeriodic subObs := by
  rintro ⟨P, N, hP, hper⟩
  have hPeq : P = 4 * (P / 4) + P % 4 := (Nat.div_add_mod P 4).symm
  have hr4 : P % 4 < 4 := Nat.mod_lt P (by norm_num)
  set k := P / 4
  interval_cases h : (P % 4)
  · have hk0 : 0 < k := by omega
    apply not_eventuallyPeriodic_subFix
    refine ⟨k, N, hk0, fun n hn => ?_⟩
    have e1 : subObs (4 * n + P) = subObs (4 * n) := hper (4 * n) (by omega)
    rw [subObs_four_mul] at e1
    have hPk : 4 * n + P = 4 * (n + k) := by omega
    rw [hPk, subObs_four_mul] at e1
    exact e1
  · exfalso
    have e1 : subObs (4 * N + P) = subObs (4 * N) := hper (4 * N) (by omega)
    have e2 : subObs (4 * N + 1 + P) = subObs (4 * N + 1) := hper (4 * N + 1) (by omega)
    rw [subObs_four_mul] at e1
    rw [subObs_four_mul_add_one] at e2
    have hPk1 : 4 * N + P = 4 * (N + k) + 1 := by omega
    have hPk2 : 4 * N + 1 + P = 4 * (N + k) + 2 := by omega
    rw [hPk1, subObs_four_mul_add_one] at e1
    rw [hPk2, subObs_four_mul_add_two] at e2
    rw [← e1] at e2
    simp only [Bool.not_not] at e2
    cases hb : subFix (N + k) <;> rw [hb] at e2 <;> exact absurd e2 (by decide)
  · exfalso
    have e1 : subObs (4 * N + P) = subObs (4 * N) := hper (4 * N) (by omega)
    have e2 : subObs (4 * N + 1 + P) = subObs (4 * N + 1) := hper (4 * N + 1) (by omega)
    rw [subObs_four_mul] at e1
    rw [subObs_four_mul_add_one] at e2
    have hPk1 : 4 * N + P = 4 * (N + k) + 2 := by omega
    have hPk2 : 4 * N + 1 + P = 4 * (N + k) + 3 := by omega
    rw [hPk1, subObs_four_mul_add_two] at e1
    rw [hPk2, subObs_four_mul_add_three] at e2
    rw [← e1] at e2
    simp only [Bool.not_not] at e2
    cases hb : subFix (N + k) <;> rw [hb] at e2 <;> exact absurd e2 (by decide)
  · apply not_eventuallyPeriodic_subFix
    rcases Nat.eq_zero_or_pos k with hk0 | hkpos
    · exfalso
      have e1 : subObs (4 * N + P) = subObs (4 * N) := hper (4 * N) (by omega)
      rw [subObs_four_mul] at e1
      have hPk : 4 * N + P = 4 * (N + k) + 3 := by omega
      rw [hPk, subObs_four_mul_add_three] at e1
      rw [hk0, Nat.add_zero] at e1
      cases hb : subFix N <;> rw [hb] at e1 <;> exact absurd e1 (by decide)
    · refine ⟨2 * k, N, by omega, fun n hn => ?_⟩
      have e1 : subObs (4 * n + P) = subObs (4 * n) := hper (4 * n) (by omega)
      have e2 : subObs (4 * (n + k) + P) = subObs (4 * (n + k)) := hper (4 * (n + k)) (by omega)
      rw [subObs_four_mul] at e1
      rw [subObs_four_mul] at e2
      have hPk1 : 4 * n + P = 4 * (n + k) + 3 := by omega
      have hPk2 : 4 * (n + k) + P = 4 * (n + 2 * k) + 3 := by omega
      rw [hPk1, subObs_four_mul_add_three] at e1
      rw [hPk2, subObs_four_mul_add_three] at e2
      rw [← e2] at e1
      simp only [Bool.not_not] at e1
      exact e1

end SubstitutionSource

/-! ## Axiom audit

Every capstone above is `#print axioms`-clean on the standard triple or a subset of it, and the
guards below make that build-enforced. -/

set_option linter.style.longLine false

/-- info: 'SubstitutionSource.subFix_four_mul' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SubstitutionSource.subFix_four_mul

/-- info: 'SubstitutionSource.subFix_four_mul_add_one' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SubstitutionSource.subFix_four_mul_add_one

/-- info: 'SubstitutionSource.subFix_four_mul_add_two' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SubstitutionSource.subFix_four_mul_add_two

/-- info: 'SubstitutionSource.subFix_four_mul_add_three' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SubstitutionSource.subFix_four_mul_add_three

/-- info: 'SubstitutionSource.subFix_block_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SubstitutionSource.subFix_block_sum

/-- info: 'SubstitutionSource.subFix_block_lag1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SubstitutionSource.subFix_block_lag1

/-- info: 'SubstitutionSource.subFix_block_lag2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SubstitutionSource.subFix_block_lag2

/-- info: 'SubstitutionSource.subFix_sum_abs_le_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SubstitutionSource.subFix_sum_abs_le_two

/-- info: 'SubstitutionSource.subFix_lag1_sum_abs_le_three' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SubstitutionSource.subFix_lag1_sum_abs_le_three

/-- info: 'SubstitutionSource.subFix_lag2_sum_abs_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SubstitutionSource.subFix_lag2_sum_abs_le

/-- info: 'SubstitutionSource.subObs_four_mul' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SubstitutionSource.subObs_four_mul

/-- info: 'SubstitutionSource.subObs_four_mul_add_one' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SubstitutionSource.subObs_four_mul_add_one

/-- info: 'SubstitutionSource.subObs_four_mul_add_two' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SubstitutionSource.subObs_four_mul_add_two

/-- info: 'SubstitutionSource.subObs_four_mul_add_three' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SubstitutionSource.subObs_four_mul_add_three

/-- info: 'SubstitutionSource.subObs_single' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SubstitutionSource.subObs_single

/-- info: 'SubstitutionSource.subObs_pair' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SubstitutionSource.subObs_pair

/-- info: 'SubstitutionSource.not_eventuallyPeriodic_subFix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SubstitutionSource.not_eventuallyPeriodic_subFix

/-- info: 'SubstitutionSource.not_eventuallyPeriodic_subObs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SubstitutionSource.not_eventuallyPeriodic_subObs
