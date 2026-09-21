/-
Copyright (c) 2026 Mykola Palamarchuk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mykola Palamarchuk
-/
module

public import ALT.KraftChaitin
public import ALT.CodingTheoremDecoder

-- Formal-check file, not Mathlib-destined: opt out of the house-style header linter.
set_option linter.style.header false

/-!
# Levin's coding theorem, `O(1)` form ([Discovery] §1.1, FV-21)

Provenance: [Discovery] §1.1 and FV-21, over the online Kraft–Chaitin assignment
`PrefixMachine.kcRun`/`kcWord` of `ALT/KraftChaitin.lean` and the universal prefix machine
`PrefixMachine.KB` of `ALT/PrefixMachine.lean`.

## What this establishes

* `level`, `improves`, `levinReq`: a total request stream over a lower-semicomputable witness `a`,
  every improving step requesting its own level plus two, every silent step requesting its own
  index plus two.
* `levinReq_mass`: the stream's partial sums stay at most one, for any semimeasure `a` approximates.
* `levinDecode`: replay the assignment until the input word is found, and output its request's
  second coordinate.
* `coding_theorem`, `coding_theorem_QB`, `QB_le_two_pow_mul`: the coding theorem with an additive
  constant loss (no logarithmic term), and both directions of the `QB` estimate it gives.
* `coding_theorem_mul`, `QB_universal`, `QB_universal_nonvacuous`: the coding theorem in
  multiplicative form at a general semimeasure, its universality corollary — `QB` dominates every
  lower-semicomputable semimeasure up to a constant factor — and a witness to the joint
  satisfiability of that corollary's hypotheses.

## What this does NOT establish (flagged)

Nothing further is deferred: this closes the boundary `ALT/KraftChaitin.lean` and
`ALT/CodingTheoremDecoder.lean` both flag.
-/


@[expose] public section

namespace PrefixMachine

open Nat.Partrec Nat.Partrec.Code AdditiveComplexity CodeEvalLaws KolmogorovComplexity

/-! ## `Nat.size` is primitive recursive -/

/-- `Nat.size` by cases: `0` at `0`, else one plus the bit-length of `m - 1`. -/
private theorem primrec_natSize : Primrec Nat.size := by
  have hcond : Primrec fun m : ℕ => decide (m = 0) :=
    Primrec.eq.decide.comp Primrec.id (Primrec.const 0)
  have hpos : Primrec fun m : ℕ => (natToBits (m - 1)).length + 1 :=
    Primrec.succ.comp (Primrec.list_length.comp
      (primrec_natToBits.comp (Primrec.nat_sub.comp Primrec.id (Primrec.const 1))))
  have hres := Primrec.cond hcond (Primrec.const 0) hpos
  refine hres.of_eq fun m => ?_
  rcases m with _ | m
  · simp
  · have hne : (m + 1 ≠ 0) := Nat.succ_ne_zero m
    simp only [hne, decide_false, Bool.cond_false, Nat.add_sub_cancel]
    exact length_natToBits m

/-! ## `level`: the least `k` clearing the level-`k` threshold -/

/-- The level of `y` at stage `t`: the least `k` with `2 ^ t ≤ 2 ^ k * a t y` (`k = t` suffices once
`a t y ≥ 1`), and `0` when `a t y = 0`, a case the stream never requests on. -/
def level (a : ℕ → ℕ → ℕ) (t y : ℕ) : ℕ :=
  if a t y = 0 then 0 else t - (Nat.size (a t y) - 1)

private theorem computable_level {a : ℕ → ℕ → ℕ} (ha : Computable₂ a) : Computable₂ (level a) := by
  have hA : Computable fun ty : ℕ × ℕ => a ty.1 ty.2 :=
    ha.comp Primrec.fst.to_comp Primrec.snd.to_comp
  have hcond : Computable fun ty : ℕ × ℕ => decide (a ty.1 ty.2 = 0) :=
    (Primrec.eq.decide.to_comp).comp hA (Computable.const 0)
  have helse : Computable fun ty : ℕ × ℕ => ty.1 - (Nat.size (a ty.1 ty.2) - 1) :=
    (Primrec.nat_sub.to_comp).comp Primrec.fst.to_comp
      ((Primrec.nat_sub.to_comp).comp (primrec_natSize.to_comp.comp hA) (Computable.const 1))
  have hres := Computable.cond hcond (Computable.const 0) helse
  exact hres.of_eq fun ty => by unfold level; rw [Bool.cond_decide]

/-! ## `level`'s arithmetic: minimality and monotonicity -/

private theorem two_pow_size_sub_one_le {A : ℕ} (hA : 0 < A) : 2 ^ (Nat.size A - 1) ≤ A := by
  have h1 : Nat.size A - 1 < Nat.size A := by
    have := Nat.size_pos.mpr hA
    omega
  exact Nat.lt_size.mp h1

/-- **`level`'s minimality**: the level clears its own threshold, and nothing smaller does. -/
private theorem level_spec {a : ℕ → ℕ → ℕ} {t y : ℕ} (hpos : 0 < a t y) :
    2 ^ t ≤ 2 ^ (level a t y) * a t y ∧ ∀ k, k < level a t y → 2 ^ k * a t y < 2 ^ t := by
  set A := a t y with hAdef
  set s := Nat.size A with hsdef
  have hspos : 0 < s := Nat.size_pos.mpr hpos
  have hlow : 2 ^ (s - 1) ≤ A := two_pow_size_sub_one_le hpos
  have hhigh : A < 2 ^ s := Nat.lt_size_self A
  have hlevel : level a t y = t - (s - 1) := ite_eq_right (by omega : A ≠ 0)
  by_cases hle : s - 1 ≤ t
  · rw [hlevel]
    have hteq : t - (s - 1) + (s - 1) = t := Nat.sub_add_cancel hle
    constructor
    · calc 2 ^ t = 2 ^ (t - (s - 1) + (s - 1)) := by rw [hteq]
        _ = 2 ^ (t - (s - 1)) * 2 ^ (s - 1) := by rw [pow_add]
        _ ≤ 2 ^ (t - (s - 1)) * A := by gcongr
    · intro k hk
      have hks : k + s ≤ t := by omega
      calc 2 ^ k * A < 2 ^ k * 2 ^ s := by gcongr
        _ = 2 ^ (k + s) := by rw [pow_add]
        _ ≤ 2 ^ t := Nat.pow_le_pow_right (by norm_num) hks
  · have hlevel0 : t - (s - 1) = 0 := by omega
    rw [hlevel, hlevel0]
    refine ⟨?_, fun k hk => absurd hk (by omega)⟩
    simp only [pow_zero, one_mul]
    have : (2 : ℕ) ^ t < 2 ^ (s - 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
    exact this.le.trans hlow

/-- **Monotonicity of the ratio forces monotonicity (in fact doubling) of `a`.** -/
private theorem a_double_le {a : ℕ → ℕ → ℕ}
    (ha_mono : ∀ t x, (a t x : ℝ) / 2 ^ t ≤ (a (t + 1) x : ℝ) / 2 ^ (t + 1)) (t y : ℕ) :
    2 * a t y ≤ a (t + 1) y := by
  have h := ha_mono t y
  have hpow_pos : (0 : ℝ) < 2 ^ t := by positivity
  rw [div_le_div_iff₀ (by positivity) (by positivity), pow_succ] at h
  have h3 : (2 : ℝ) * a t y ≤ a (t + 1) y := by nlinarith [h, hpow_pos]
  exact_mod_cast h3

private theorem a_mono {a : ℕ → ℕ → ℕ}
    (ha_mono : ∀ t x, (a t x : ℝ) / 2 ^ t ≤ (a (t + 1) x : ℝ) / 2 ^ (t + 1)) (y : ℕ) :
    Monotone (fun t => a t y) := by
  apply monotone_nat_of_le_succ
  intro t
  have := a_double_le ha_mono t y
  omega

/-- **Doubling, iterated**: `a` grows by at least a factor `2 ^ d` over `d` steps. -/
private theorem a_pow_le {a : ℕ → ℕ → ℕ}
    (ha_mono : ∀ t x, (a t x : ℝ) / 2 ^ t ≤ (a (t + 1) x : ℝ) / 2 ^ (t + 1)) (y t d : ℕ) :
    2 ^ d * a t y ≤ a (t + d) y := by
  induction d with
  | zero => simp
  | succ d ih =>
      have hstep := a_double_le ha_mono (t + d) y
      calc 2 ^ (d + 1) * a t y = 2 * (2 ^ d * a t y) := by ring
        _ ≤ 2 * a (t + d) y := by omega
        _ ≤ a (t + d + 1) y := hstep
        _ = a (t + (d + 1)) y := by congr 1

/-- **`level` is antitone once positive**: the level never rises across stages at which `y`'s
witness stays positive. -/
private theorem level_antitone {a : ℕ → ℕ → ℕ}
    (ha_mono : ∀ t x, (a t x : ℝ) / 2 ^ t ≤ (a (t + 1) x : ℝ) / 2 ^ (t + 1))
    {t1 t2 y : ℕ} (hle : t1 ≤ t2) (hpos : 0 < a t1 y) : level a t2 y ≤ level a t1 y := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hle
  have hpow := a_pow_le ha_mono y t1 d
  have hpos2 : 0 < a (t1 + d) y := by
    have h2d : 0 < 2 ^ d * a t1 y := Nat.mul_pos (Nat.two_pow_pos d) hpos
    omega
  have hspos : 0 < Nat.size (a t1 y) := Nat.size_pos.mpr hpos
  have hsize : Nat.size (a t1 y) + d ≤ Nat.size (a (t1 + d) y) := by
    have hlow : 2 ^ (Nat.size (a t1 y) - 1) ≤ a t1 y := two_pow_size_sub_one_le hpos
    have hchain : 2 ^ (d + (Nat.size (a t1 y) - 1)) ≤ a (t1 + d) y := by
      calc 2 ^ (d + (Nat.size (a t1 y) - 1))
          = 2 ^ d * 2 ^ (Nat.size (a t1 y) - 1) := by rw [pow_add]
        _ ≤ 2 ^ d * a t1 y := by gcongr
        _ ≤ a (t1 + d) y := hpow
    have := Nat.lt_size.mpr hchain
    omega
  unfold level
  rw [ite_eq_right hpos.ne', ite_eq_right hpos2.ne']
  omega

/-! ## `improves`: an improving step vs. a silent step -/

/-- The step improves when `a t y > 0` and either `t = 0`, or `a (t - 1) y = 0`, or the level
dropped. -/
def improves (a : ℕ → ℕ → ℕ) (m : ℕ) : Bool :=
  decide (0 < a m.unpair.1 m.unpair.2) &&
    (decide (m.unpair.1 = 0) || decide (a (m.unpair.1 - 1) m.unpair.2 = 0) ||
      decide (level a m.unpair.1 m.unpair.2 < level a (m.unpair.1 - 1) m.unpair.2))

set_option maxHeartbeats 1000000 in
-- `Computable₂.comp` over this nested `ℕ × ℕ` shape is heavy to elaborate; mirrors
-- `computable₂_firesAt`'s own bump in `ALT/CodingTheoremDecoder.lean`.
private theorem computable_improves {a : ℕ → ℕ → ℕ} (ha : Computable₂ a) :
    Computable (improves a) := by
  have ht : Primrec fun m : ℕ => (Nat.unpair m).1 := Primrec.fst.comp Primrec.unpair
  have hy : Primrec fun m : ℕ => (Nat.unpair m).2 := Primrec.snd.comp Primrec.unpair
  have hApos : Computable fun m : ℕ => decide (0 < a (Nat.unpair m).1 (Nat.unpair m).2) :=
    (Primrec.nat_lt.decide.to_comp.comp (Computable.const 0) (ha.comp ht.to_comp hy.to_comp))
  have ht0 : Computable fun m : ℕ => decide ((Nat.unpair m).1 = 0) :=
    (Primrec.eq.decide.comp ht (Primrec.const 0)).to_comp
  have hAprev0 : Computable fun m : ℕ => decide (a ((Nat.unpair m).1 - 1) (Nat.unpair m).2 = 0) :=
    (Primrec.eq.decide.to_comp).comp
      (ha.comp (Primrec.nat_sub.comp ht (Primrec.const 1)).to_comp hy.to_comp) (Computable.const 0)
  have hlvlcur : Computable fun m : ℕ => level a (Nat.unpair m).1 (Nat.unpair m).2 :=
    Computable₂.comp (computable_level ha) ht.to_comp hy.to_comp
  have hlvlprev : Computable fun m : ℕ => level a ((Nat.unpair m).1 - 1) (Nat.unpair m).2 :=
    Computable₂.comp (computable_level ha)
      (Primrec.nat_sub.comp ht (Primrec.const 1)).to_comp hy.to_comp
  have hdrop : Computable fun m : ℕ =>
      decide (level a (Nat.unpair m).1 (Nat.unpair m).2
        < level a ((Nat.unpair m).1 - 1) (Nat.unpair m).2) :=
    Primrec.nat_lt.decide.to_comp.comp hlvlcur hlvlprev
  have hor : Computable fun m : ℕ =>
      decide ((Nat.unpair m).1 = 0) || decide (a ((Nat.unpair m).1 - 1) (Nat.unpair m).2 = 0) ||
        decide (level a (Nat.unpair m).1 (Nat.unpair m).2
          < level a ((Nat.unpair m).1 - 1) (Nat.unpair m).2) :=
    Primrec.or.to_comp.comp (Primrec.or.to_comp.comp ht0 hAprev0) hdrop
  exact (Primrec.and.to_comp.comp hApos hor).of_eq fun m => rfl

/-! ## `levinReq`: the total request stream -/

/-- The request stream, total: an improving step asks for its level plus two, a silent step for
its own index plus two. -/
def levinReq (a : ℕ → ℕ → ℕ) (m : ℕ) : ℕ :=
  if improves a m then level a m.unpair.1 m.unpair.2 + 2 else m + 2

theorem computable_levinReq {a : ℕ → ℕ → ℕ} (ha : Computable₂ a) : Computable (levinReq a) := by
  have himp := computable_improves ha
  have hy : Computable fun m : ℕ => level a (Nat.unpair m).1 (Nat.unpair m).2 + 2 :=
    Computable.succ.comp (Computable.succ.comp
      (Computable₂.comp (computable_level ha) (Primrec.fst.comp Primrec.unpair).to_comp
        (Primrec.snd.comp Primrec.unpair).to_comp))
  have hn : Computable fun m : ℕ => m + 2 := Computable.succ.comp Computable.succ
  exact (Computable.cond himp hy hn).of_eq fun m => by
    unfold levinReq; cases improves a m <;> rfl

/-! ## A Finset bound: distinct naturals above (or at) a threshold carry bounded mass -/

/-- **A finite Finset of naturals all above `k` carries mass at most `2 ^ (-k)`.** Mirrors
`sum_two_pow_neg_bound` of `ALT/KraftChaitin.lean`, at the `Finset` level. -/
private theorem sum_two_pow_neg_bound_finset : ∀ (d : ℕ) (S : Finset ℕ) (k : ℕ),
    (∀ l ∈ S, l ≤ k + d) → (∀ l ∈ S, k < l) →
    ∑ l ∈ S, (1 / 2 : ℝ) ^ l ≤ (1 / 2 : ℝ) ^ k - (1 / 2 : ℝ) ^ (k + S.card) := by
  intro d
  induction d with
  | zero =>
      intro S k hbound hgt
      have hSempty : S = ∅ := by
        rcases S.eq_empty_or_nonempty with h | ⟨l0, hl0⟩
        · exact h
        · exact absurd (hbound l0 hl0) (by have := hgt l0 hl0; omega)
      subst hSempty
      simp
  | succ d ih =>
      intro S k hbound hgt
      by_cases hmem : (k + 1) ∈ S
      · set S' := S.erase (k + 1) with hS'def
        have hcard : S.card = S'.card + 1 := (Finset.card_erase_add_one hmem).symm
        have hgt' : ∀ l ∈ S', k + 1 < l := by
          intro l hl
          have hlS : l ∈ S := Finset.mem_of_mem_erase hl
          have hne : l ≠ k + 1 := Finset.ne_of_mem_erase hl
          have := hgt l hlS
          omega
        have hbound' : ∀ l ∈ S', l ≤ (k + 1) + d := by
          intro l hl
          have hlS : l ∈ S := Finset.mem_of_mem_erase hl
          have := hbound l hlS
          omega
        have hIH := ih S' (k + 1) hbound' hgt'
        have hsum : ∑ l ∈ S, (1 / 2 : ℝ) ^ l
            = (1 / 2 : ℝ) ^ (k + 1) + ∑ l ∈ S', (1 / 2 : ℝ) ^ l :=
          (Finset.add_sum_erase S _ hmem).symm
        rw [hsum, hcard]
        have hexp : (1 / 2 : ℝ) ^ (k + (S'.card + 1)) = (1 / 2 : ℝ) ^ ((k + 1) + S'.card) := by
          congr 1; omega
        rw [hexp]
        have hdbl := two_pow_neg_succ_double k
        linarith [hIH, hdbl]
      · have hbound' : ∀ l ∈ S, l ≤ (k + 1) + d := by
          intro l hl
          have hne : l ≠ k + 1 := fun he => hmem (he ▸ hl)
          have := hbound l hl
          omega
        have hgt' : ∀ l ∈ S, k + 1 < l := by
          intro l hl
          have hne : l ≠ k + 1 := fun he => hmem (he ▸ hl)
          have := hgt l hl
          omega
        have hIH := ih S (k + 1) hbound' hgt'
        have hdbl1 := two_pow_neg_succ_double k
        have hdbl2 := two_pow_neg_succ_double (k + S.card)
        have hexp : k + S.card + 1 = (k + 1) + S.card := by omega
        rw [hexp] at hdbl2
        have hnn := two_pow_neg_antitone (show k + 1 ≤ (k + 1) + S.card from by omega)
        linarith [hIH, hdbl1, hdbl2, hnn]

/-- **The general, factor-`2`-safe bound**: a Finset of naturals all at least `k` carries mass at
most `2 ^ (1 - k)`. Safe at `k = 0` too, unlike the strict form above. -/
private theorem sum_two_pow_neg_bound_ge (S : Finset ℕ) (k : ℕ) (hge : ∀ l ∈ S, k ≤ l) :
    ∑ l ∈ S, (1 / 2 : ℝ) ^ l ≤ 2 * (1 / 2 : ℝ) ^ k := by
  by_cases hk : k ∈ S
  · have hsplit : ∑ l ∈ S, (1 / 2 : ℝ) ^ l
        = (1 / 2 : ℝ) ^ k + ∑ l ∈ S.erase k, (1 / 2 : ℝ) ^ l :=
      (Finset.add_sum_erase S _ hk).symm
    have hgt : ∀ l ∈ S.erase k, k < l := by
      intro l hl
      have hlS := Finset.mem_of_mem_erase hl
      have hne := Finset.ne_of_mem_erase hl
      have := hge l hlS
      omega
    have hboundk : ∀ l ∈ S.erase k, l ≤ k + (S.erase k).sup id := fun l hl =>
      (Finset.le_sup (f := id) hl).trans (Nat.le_add_left _ _)
    have hbound2 := sum_two_pow_neg_bound_finset ((S.erase k).sup id) (S.erase k) k hboundk hgt
    have hnn : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ (k + (S.erase k).card) := by positivity
    rw [hsplit]
    linarith [hbound2, hnn]
  · have hgt : ∀ l ∈ S, k < l := fun l hl => lt_of_le_of_ne (hge l hl) (fun he => hk (he ▸ hl))
    have hboundk : ∀ l ∈ S, l ≤ k + S.sup id := fun l hl =>
      (Finset.le_sup (f := id) hl).trans (Nat.le_add_left _ _)
    have hbound2 := sum_two_pow_neg_bound_finset (S.sup id) S k hboundk hgt
    have hnn : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ (k + S.card) := by positivity
    have hnn2 : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ k := by positivity
    linarith [hbound2, hnn, hnn2]

/-! ## `levinReq_mass`: the stream's partial sums stay at most one -/

private theorem level_le_iff_real (a : ℕ → ℕ → ℕ) (k t y : ℕ) :
    2 ^ t ≤ 2 ^ k * a t y ↔ (1 / 2 : ℝ) ^ k ≤ (a t y : ℝ) / 2 ^ t := by
  rw [show ((1 : ℝ) / 2) ^ k = 1 / 2 ^ k from by rw [div_pow, one_pow]]
  rw [div_le_div_iff₀ (by positivity) (by positivity), one_mul, mul_comm ((a t y : ℝ)) (2 ^ k)]
  constructor
  · intro h; exact_mod_cast h
  · intro h; exact_mod_cast h

/-- **Clearing a level-`k` threshold puts the level itself at most `k`.** -/
private theorem level_le_of_crossing {a : ℕ → ℕ → ℕ} {t k x : ℕ} (h : 2 ^ t ≤ 2 ^ k * a t x) :
    level a t x ≤ k := by
  have hpos : 0 < a t x := by
    rcases Nat.eq_zero_or_pos (a t x) with h0 | h0
    · exfalso
      rw [h0, mul_zero] at h
      have := Nat.two_pow_pos t
      omega
    · exact h0
  by_contra hgt
  have hlt := (level_spec hpos).2 k (by omega)
  omega

/-- **A level's threshold is genuinely below the semimeasure it approximates.** -/
private theorem level_le_mu {a : ℕ → ℕ → ℕ} {μ : ℕ → ℝ} (ha_le : ∀ t x, (a t x : ℝ) / 2 ^ t ≤ μ x)
    {t y : ℕ} (hpos : 0 < a t y) : (1 / 2 : ℝ) ^ (level a t y) ≤ μ y :=
  ((level_le_iff_real a (level a t y) t y).mp (level_spec hpos).1).trans (ha_le t y)

private theorem improves_pos {a : ℕ → ℕ → ℕ} {m : ℕ} (h : improves a m = true) :
    0 < a (Nat.unpair m).1 (Nat.unpair m).2 := by
  unfold improves at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1

/-- **The level strictly drops between consecutive improving steps for the same `y`.** -/
private theorem level_strictAnti_of_improves {a : ℕ → ℕ → ℕ}
    (ha_mono : ∀ t x, (a t x : ℝ) / 2 ^ t ≤ (a (t + 1) x : ℝ) / 2 ^ (t + 1))
    {y t1 t2 : ℕ} (ht : t1 < t2)
    (h1 : improves a (Nat.pair t1 y) = true) (h2 : improves a (Nat.pair t2 y) = true) :
    level a t2 y < level a t1 y := by
  have hunpair1 : Nat.unpair (Nat.pair t1 y) = (t1, y) := Nat.unpair_pair t1 y
  have hunpair2 : Nat.unpair (Nat.pair t2 y) = (t2, y) := Nat.unpair_pair t2 y
  have hApos1 : 0 < a t1 y := by
    have hp := improves_pos h1
    rwa [hunpair1] at hp
  unfold improves at h2
  rw [hunpair2] at h2
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h2
  obtain ⟨-, hcase2⟩ := h2
  have ht2ne : t2 ≠ 0 := by omega
  have hab : a t1 y ≤ a (t2 - 1) y := a_mono ha_mono y (show t1 ≤ t2 - 1 by omega)
  have ht2prevne : a (t2 - 1) y ≠ 0 := by omega
  have hdrop : level a t2 y < level a (t2 - 1) y := by
    rcases hcase2 with (h | h) | h
    · exact absurd h ht2ne
    · exact absurd h ht2prevne
    · exact h
  have hanti : level a (t2 - 1) y ≤ level a t1 y :=
    level_antitone ha_mono (show t1 ≤ t2 - 1 by omega) hApos1
  omega

/-- **Distinct improving steps for the same `y` carry distinct levels.** -/
private theorem level_injOn_of_improves {a : ℕ → ℕ → ℕ}
    (ha_mono : ∀ t x, (a t x : ℝ) / 2 ^ t ≤ (a (t + 1) x : ℝ) / 2 ^ (t + 1)) (y : ℕ)
    {S : Finset ℕ} (hS : ∀ m ∈ S, improves a m = true ∧ (Nat.unpair m).2 = y) :
    Set.InjOn (fun m => level a (Nat.unpair m).1 y) S := by
  intro m1 hm1 m2 hm2 heq
  obtain ⟨himp1, hy1⟩ := hS m1 hm1
  obtain ⟨himp2, hy2⟩ := hS m2 hm2
  simp only at heq
  have hm1eq : m1 = Nat.pair (Nat.unpair m1).1 y := by
    conv_lhs => rw [← Nat.pair_unpair m1]
    rw [hy1]
  have hm2eq : m2 = Nat.pair (Nat.unpair m2).1 y := by
    conv_lhs => rw [← Nat.pair_unpair m2]
    rw [hy2]
  have h1' : improves a (Nat.pair (Nat.unpair m1).1 y) = true := by rw [← hm1eq]; exact himp1
  have h2' : improves a (Nat.pair (Nat.unpair m2).1 y) = true := by rw [← hm2eq]; exact himp2
  rcases lt_trichotomy (Nat.unpair m1).1 (Nat.unpair m2).1 with hlt | heqt | hgt
  · exact absurd heq (ne_of_gt (level_strictAnti_of_improves ha_mono hlt h1' h2'))
  · rw [hm1eq, hm2eq, heqt]
  · exact absurd heq.symm (ne_of_gt (level_strictAnti_of_improves ha_mono hgt h2' h1'))

/-- **Each fiber's improving mass is at most half its own semimeasure weight.** -/
private theorem fiber_sum_le {a : ℕ → ℕ → ℕ} {μ : ℕ → ℝ}
    (ha_mono : ∀ t x, (a t x : ℝ) / 2 ^ t ≤ (a (t + 1) x : ℝ) / 2 ^ (t + 1))
    (ha_le : ∀ t x, (a t x : ℝ) / 2 ^ t ≤ μ x) (hnn : ∀ x, 0 ≤ μ x) (y : ℕ) {S : Finset ℕ}
    (hS : ∀ m ∈ S, improves a m = true ∧ (Nat.unpair m).2 = y) :
    ∑ m ∈ S, (1 / 2 : ℝ) ^ (levinReq a m) ≤ (1 / 2 : ℝ) * μ y := by
  classical
  rcases S.eq_empty_or_nonempty with hSe | hSne
  · subst hSe; simp [hnn y]
  have hlevinReq : ∀ m ∈ S, levinReq a m = level a (Nat.unpair m).1 y + 2 := by
    intro m hm
    unfold levinReq
    rw [ite_eq_left (hS m hm).1, (hS m hm).2]
  have heq1 : ∑ m ∈ S, (1 / 2 : ℝ) ^ (levinReq a m)
      = (1 / 4 : ℝ) * ∑ m ∈ S, (1 / 2 : ℝ) ^ (level a (Nat.unpair m).1 y) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun m hm => by rw [hlevinReq m hm]; ring
  set L : Finset ℕ := S.image (fun m => level a (Nat.unpair m).1 y) with hLdef
  have hinj := level_injOn_of_improves ha_mono y hS
  have heq2 : ∑ m ∈ S, (1 / 2 : ℝ) ^ (level a (Nat.unpair m).1 y) = ∑ l ∈ L, (1 / 2 : ℝ) ^ l := by
    rw [hLdef, Finset.sum_image]
    intro m1 hm1 m2 hm2 h
    exact hinj hm1 hm2 h
  have hLne : L.Nonempty := hSne.image _
  have hbound := sum_two_pow_neg_bound_ge L (L.min' hLne) (fun l hl => L.min'_le l hl)
  have hminmemL : L.min' hLne ∈ L := L.min'_mem hLne
  obtain ⟨m0, hm0S, hm0eq⟩ := Finset.mem_image.mp hminmemL
  have ht0pos : 0 < a (Nat.unpair m0).1 y := by
    have hp := improves_pos (hS m0 hm0S).1
    rwa [(hS m0 hm0S).2] at hp
  have hkey : (1 / 2 : ℝ) ^ (L.min' hLne) ≤ μ y := by
    have hp := level_le_mu ha_le ht0pos
    rwa [hm0eq] at hp
  rw [heq1, heq2]
  linarith [hbound, hkey]

/-- **The budget.** The dummies cost less than half and the real requests at most half. -/
theorem levinReq_mass {a : ℕ → ℕ → ℕ} {μ : ℕ → ℝ}
    (ha_mono : ∀ t x, (a t x : ℝ) / 2 ^ t ≤ (a (t + 1) x : ℝ) / 2 ^ (t + 1))
    (ha_le : ∀ t x, (a t x : ℝ) / 2 ^ t ≤ μ x) (hnn : ∀ x, 0 ≤ μ x)
    (hsum : ∀ F : Finset ℕ, ∑ x ∈ F, μ x ≤ 1) :
    ∀ N, ∑ m ∈ Finset.range N, (1 / 2 : ℝ) ^ levinReq a m ≤ 1 := by
  intro N
  classical
  set Mimp : Finset ℕ := (Finset.range N).filter (fun m => improves a m = true) with hMimpdef
  set Msil : Finset ℕ := (Finset.range N).filter (fun m => ¬ improves a m = true) with hMsildef
  have hpart : ∑ m ∈ Mimp, (1 / 2 : ℝ) ^ (levinReq a m) + ∑ m ∈ Msil, (1 / 2 : ℝ) ^ (levinReq a m)
      = ∑ m ∈ Finset.range N, (1 / 2 : ℝ) ^ (levinReq a m) := by
    rw [hMimpdef, hMsildef]
    exact Finset.sum_filter_add_sum_filter_not (Finset.range N) _ _
  have hsil_eq : ∀ m ∈ Msil, levinReq a m = m + 2 := by
    intro m hm
    have hmi : ¬ improves a m = true := (Finset.mem_filter.mp hm).2
    unfold levinReq
    rw [ite_eq_right hmi]
  have hsil_sum : ∑ m ∈ Msil, (1 / 2 : ℝ) ^ (levinReq a m) ≤ 1 / 2 := by
    have heq : ∑ m ∈ Msil, (1 / 2 : ℝ) ^ (levinReq a m)
        = (1 / 4 : ℝ) * ∑ m ∈ Msil, (1 / 2 : ℝ) ^ m := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun m hm => by rw [hsil_eq m hm]; ring
    rw [heq]
    have hb := sum_two_pow_neg_bound_ge Msil 0 (fun l _ => Nat.zero_le l)
    simp only [pow_zero, mul_one] at hb
    linarith [hb]
  set g : ℕ → ℕ := fun m => (Nat.unpair m).2 with hgdef
  have hmaps : ∀ m ∈ Mimp, g m ∈ Mimp.image g := fun m hm => Finset.mem_image_of_mem g hm
  have hfiber := Finset.sum_fiberwise_of_maps_to hmaps (fun m => (1 / 2 : ℝ) ^ (levinReq a m))
  have himp_sum : ∑ m ∈ Mimp, (1 / 2 : ℝ) ^ (levinReq a m) ≤ 1 / 2 := by
    rw [← hfiber]
    have hfibound : ∀ y ∈ Mimp.image g,
        ∑ m ∈ Mimp.filter (fun m => g m = y), (1 / 2 : ℝ) ^ (levinReq a m) ≤ (1 / 2 : ℝ) * μ y := by
      intro y _
      apply fiber_sum_le ha_mono ha_le hnn y
      intro m hm
      obtain ⟨hmMimp, hmy⟩ := Finset.mem_filter.mp hm
      exact ⟨(Finset.mem_filter.mp hmMimp).2, hmy⟩
    calc ∑ y ∈ Mimp.image g, ∑ m ∈ Mimp.filter (fun m => g m = y), (1 / 2 : ℝ) ^ (levinReq a m)
        ≤ ∑ y ∈ Mimp.image g, (1 / 2 : ℝ) * μ y := Finset.sum_le_sum hfibound
      _ = (1 / 2 : ℝ) * ∑ y ∈ Mimp.image g, μ y := (Finset.mul_sum _ _ _).symm
      _ ≤ 1 / 2 := by have := hsum (Mimp.image g); linarith
  linarith [hpart, hsil_sum, himp_sum]

/-! ## The KC assignment never repeats a served pair or a served word -/

/-- **A served `(length, numerator)` pair is never re-served at a different step.** -/
private theorem kcWordPair_injective {req : ℕ → ℕ}
    (hmass : ∀ N, ∑ m ∈ Finset.range N, (1 / 2 : ℝ) ^ req m ≤ 1) {i i' : ℕ} {p : ℕ × ℕ}
    (hi : kcWordPair req i = some p) (hi' : kcWordPair req i' = some p) : i = i' := by
  by_contra hne
  wlog hlt : i < i' generalizing i i' with H
  · exact H hi' hi (Ne.symm hne) (by omega)
  obtain ⟨q, hserve, hq1⟩ := Option.map_eq_some_iff.mp hi'
  subst hq1
  have hp1eq : q.1.1 = req i' := kcServe'_fst_eq (kcRunPairs req i').1 (req i') hserve
  rw [← hp1eq] at hserve
  have hinv := (kcRunPairs_inv hmass i').1
  obtain ⟨-, -, -, jp, hjpmem, hjpnest, -⟩ := kcServe'_inv hinv.1 hserve
  have hpmem : q.1 ∈ (kcRunPairs req i').2 := kcWordPair_mem_kcRunPairs hi i' hlt
  have hcontra : ¬ Comparable q.1.1 q.1.2 jp.1 jp.2 := hinv.2.2.1 q.1 hpmem jp hjpmem
  exact hcontra (Or.inr hjpnest)

/-- **A served word determines its step: `kcWord` is injective on its `some`-fibers.** -/
theorem kcWord_injective {req : ℕ → ℕ}
    (hmass : ∀ N, ∑ m ∈ Finset.range N, (1 / 2 : ℝ) ^ req m ≤ 1) {i i' : ℕ} {w : List Bool}
    (hi : kcWord req i = some w) (hi' : kcWord req i' = some w) : i = i' := by
  rw [kcWord_eq_kcWordPair] at hi hi'
  obtain ⟨p, hp, hpw⟩ := Option.map_eq_some_iff.mp hi
  obtain ⟨p', hp', hpw'⟩ := Option.map_eq_some_iff.mp hi'
  have hb1 : p.2 < 2 ^ p.1 :=
    ((kcRunPairs_inv hmass (i + 1)).1).2.1 p (kcWordPair_mem_kcRunPairs hp (i + 1) (by omega))
  have hb2 : p'.2 < 2 ^ p'.1 :=
    ((kcRunPairs_inv hmass (i' + 1)).1).2.1 p' (kcWordPair_mem_kcRunPairs hp' (i' + 1) (by omega))
  have hlen : p.1 = p'.1 := by
    have h1 := congrArg List.length hpw
    have h2 := congrArg List.length hpw'
    rw [length_bitsFixed] at h1 h2
    omega
  have hpp' : p = p' := by
    have heq : bitsFixed p.1 p.2 = bitsFixed p'.1 p'.2 := by rw [hpw, hpw']
    rw [hlen] at hb1 heq
    have hnum : p.2 = p'.2 := by
      have hcong := congrArg ofBitsFixed heq
      rwa [ofBitsFixed_bitsFixed hb1, ofBitsFixed_bitsFixed hb2] at hcong
    exact Prod.ext hlen hnum
  exact kcWordPair_injective hmass hp (hpp' ▸ hp')

/-! ## `levinDecode`: replay the assignment until the input word is found -/

/-- Replay the assignment until an improving step's word is the input, and output that step's
`y`. -/
def levinDecode (a : ℕ → ℕ → ℕ) : ℕ →. ℕ :=
  fun n => (Nat.rfind fun m => Part.some (decide (improves a m = true ∧
      kcWord (levinReq a) m = some (natToBits n)))) >>= fun m => Part.some (Nat.unpair m).2

theorem partrec_levinDecode {a : ℕ → ℕ → ℕ} (ha_comp : Computable₂ a) :
    Partrec (levinDecode a) := by
  have himp : Computable fun nm : ℕ × ℕ => improves a nm.2 :=
    (computable_improves ha_comp).comp Primrec.snd.to_comp
  have hkc : Computable fun nm : ℕ × ℕ => kcWord (levinReq a) nm.2 :=
    (computable_kcWord (computable_levinReq ha_comp)).comp Primrec.snd.to_comp
  have hnb : Computable fun nm : ℕ × ℕ => (some (natToBits nm.1) : Option (List Bool)) :=
    (Primrec.option_some.comp (primrec_natToBits.comp Primrec.fst)).to_comp
  have heq : Computable fun nm : ℕ × ℕ =>
      decide (kcWord (levinReq a) nm.2 = some (natToBits nm.1)) :=
    Primrec.eq.decide.to_comp.comp hkc hnb
  have hres : Computable fun nm : ℕ × ℕ =>
      improves a nm.2 && decide (kcWord (levinReq a) nm.2 = some (natToBits nm.1)) :=
    Primrec.and.to_comp.comp himp heq
  have hcond : Computable₂ fun (n m : ℕ) => decide (improves a m = true ∧
      kcWord (levinReq a) m = some (natToBits n)) :=
    hres.of_eq fun nm => by simp only [Bool.decide_and, Bool.decide_eq_true]
  have hpart : Partrec₂ fun (n m : ℕ) => (Part.some (decide (improves a m = true ∧
      kcWord (levinReq a) m = some (natToBits n))) : Part Bool) := hcond.partrec₂
  have hrfind : Partrec fun n => Nat.rfind fun m => Part.some (decide (improves a m = true ∧
      kcWord (levinReq a) m = some (natToBits n))) := Partrec.rfind hpart
  have hmap : Computable₂ fun (_ : ℕ) (m : ℕ) => (Nat.unpair m).2 :=
    (Primrec.snd.comp Primrec.unpair).to_comp.comp₂ Primrec₂.right.to_comp
  exact (Partrec.map hrfind hmap).of_eq fun n => by
    unfold levinDecode
    exact (Part.bind_some_eq_map _ _).symm

/-- **`Nat.rfind` locates the request whose word matches, at the least request satisfying it.** -/
private theorem rfind_levinDecode_eq {a : ℕ → ℕ → ℕ} (n : ℕ)
    (h : ∃ m, improves a m = true ∧ kcWord (levinReq a) m = some (natToBits n)) :
    Nat.rfind (fun m => Part.some (decide (improves a m = true ∧
        kcWord (levinReq a) m = some (natToBits n)))) = Part.some (Nat.find h) := by
  apply Part.eq_some_iff.mpr
  apply Nat.mem_rfind.mpr
  have hspec := Nat.find_spec h
  refine ⟨?_, fun {m'} hm' => ?_⟩
  · rw [Part.mem_some_iff]
    simp [hspec.1, hspec.2]
  · rw [Part.mem_some_iff]
    exact (decide_eq_false_iff_not.mpr (Nat.find_min h hm')).symm

/-- **The domain of the decoder, read as bit-strings, is prefix-free.** -/
theorem prefixFree_levinDecode_dom {a : ℕ → ℕ → ℕ} {μ : ℕ → ℝ}
    (ha_mono : ∀ t x, (a t x : ℝ) / 2 ^ t ≤ (a (t + 1) x : ℝ) / 2 ^ (t + 1))
    (ha_le : ∀ t x, (a t x : ℝ) / 2 ^ t ≤ μ x) (hnn : ∀ x, 0 ≤ μ x)
    (hsum : ∀ F : Finset ℕ, ∑ x ∈ F, μ x ≤ 1) :
    PrefixFree (natToBits '' (levinDecode a).Dom) := by
  have hmass : ∀ N, ∑ m ∈ Finset.range N, (1 / 2 : ℝ) ^ (levinReq a m) ≤ 1 :=
    levinReq_mass ha_mono ha_le hnn hsum
  have hsub : natToBits '' (levinDecode a).Dom ⊆ {w | ∃ i, kcWord (levinReq a) i = some w} := by
    rintro w ⟨n, hn, rfl⟩
    unfold levinDecode at hn
    obtain ⟨v, hv⟩ := Part.dom_iff_mem.mp hn
    obtain ⟨m, hm, -⟩ := Part.mem_bind_iff.mp hv
    have hm' := Nat.rfind_spec hm
    have hm'' : decide (improves a m = true ∧
        kcWord (levinReq a) m = some (natToBits n)) = true := (Part.mem_some_iff.mp hm').symm
    have hcond : improves a m = true ∧ kcWord (levinReq a) m = some (natToBits n) := by
      simpa using hm''
    exact ⟨m, hcond.2⟩
  exact fun w1 hw1 w2 hw2 hpre => kcWord_prefixFree hmass w1 (hsub hw1) w2 (hsub hw2) hpre

/-- **Correctness on the intended input**: the decoder outputs `x` from the word its
improving step is served, at any step it is genuinely improving. -/
private theorem levinDecode_eq_of_witness {a : ℕ → ℕ → ℕ} {t x : ℕ} {w : List Bool}
    (hmass : ∀ N, ∑ m ∈ Finset.range N, (1 / 2 : ℝ) ^ (levinReq a m) ≤ 1)
    (himp : improves a (Nat.pair t x) = true)
    (hw : kcWord (levinReq a) (Nat.pair t x) = some w) :
    levinDecode a (bitsToNat w) = Part.some x := by
  have h : ∃ m, improves a m = true ∧ kcWord (levinReq a) m = some (natToBits (bitsToNat w)) :=
    ⟨Nat.pair t x, himp, by rw [natToBits_bitsToNat]; exact hw⟩
  have hfind := rfind_levinDecode_eq (bitsToNat w) h
  have hfindeq : Nat.find h = Nat.pair t x := by
    have hspec := Nat.find_spec h
    have hspec2' : kcWord (levinReq a) (Nat.find h) = some w := by
      rw [hspec.2, natToBits_bitsToNat]
    exact kcWord_injective hmass hspec2' hw
  unfold levinDecode
  rw [hfind, hfindeq]
  simp [Nat.unpair_pair]

/-! ## The coding theorem, `O(1)` form -/

/-- **Levin's coding theorem, the upper bound**: on the prefix machine every lower-semicomputable
semimeasure is an ideal code up to an additive constant. -/
theorem coding_theorem {μ : ℕ → ℝ} (hμ : LowerSemicomputable μ) (hnn : ∀ x, 0 ≤ μ x)
    (hsum : ∀ F : Finset ℕ, ∑ x ∈ F, μ x ≤ 1) :
    ∃ C : ℕ, ∀ x k : ℕ, (1 / 2 : ℝ) ^ k < μ x → KB x ≤ k + C := by
  obtain ⟨a, ha_comp, ha_mono, ha_le, ha_lt⟩ := hμ
  obtain ⟨d, hd⟩ := exists_code.mp (Partrec.nat_iff.mp (partrec_levinDecode ha_comp))
  have hdom_prefixFree : PrefixFree (natToBits '' d.eval.Dom) := by
    rw [hd]; exact prefixFree_levinDecode_dom ha_mono ha_le hnn hsum
  have hpfy_eq : pfy d = d.eval := pfy_eq_of_prefixFree d hdom_prefixFree
  have hmass : ∀ N, ∑ m ∈ Finset.range N, (1 / 2 : ℝ) ^ (levinReq a m) ≤ 1 :=
    levinReq_mass ha_mono ha_le hnn hsum
  refine ⟨elen d + 2, fun x k hx => ?_⟩
  obtain ⟨t0, ht0⟩ := ha_lt x ((1 / 2 : ℝ) ^ k) hx
  have hcross0 : 2 ^ t0 ≤ 2 ^ k * a t0 x := (level_le_iff_real a k t0 x).mpr ht0.le
  have hApos0 : 0 < a t0 x := by
    by_contra hz
    have haz : a t0 x = 0 := by omega
    rw [haz, mul_zero] at hcross0
    have := Nat.two_pow_pos t0
    omega
  have hex : ∃ t, 0 < a t x ∧ level a t x ≤ k := ⟨t0, hApos0, level_le_of_crossing hcross0⟩
  set t := Nat.find hex with htdef
  clear_value t
  have hspec := Nat.find_spec hex
  rw [← htdef] at hspec
  obtain ⟨hApos, hlevelk⟩ := hspec
  have hmin : ∀ t' < t, ¬ (0 < a t' x ∧ level a t' x ≤ k) := by
    rw [htdef]
    exact fun t' ht' => Nat.find_min hex ht'
  have himp : improves a (Nat.pair t x) = true := by
    unfold improves
    rw [Nat.unpair_pair]
    simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq]
    refine ⟨hApos, ?_⟩
    rcases Nat.eq_zero_or_pos t with ht0' | htpos
    · exact Or.inl (Or.inl ht0')
    · by_cases hprev : a (t - 1) x = 0
      · exact Or.inl (Or.inr hprev)
      · have hprevpos : 0 < a (t - 1) x := Nat.pos_of_ne_zero hprev
        have hnotk := hmin (t - 1) (by omega)
        have hprevgt : k < level a (t - 1) x := by
          by_contra hle
          exact hnotk ⟨hprevpos, by omega⟩
        exact Or.inr (by omega)
  have hlevinReq : levinReq a (Nat.pair t x) = level a t x + 2 := by
    unfold levinReq
    rw [ite_eq_left himp, Nat.unpair_pair]
  obtain ⟨w, hw, hwlen⟩ := (kcRun_invariant hmass (Nat.pair t x + 1)).2.1
    (Nat.pair t x) (Nat.lt_succ_self _)
  rw [hlevinReq] at hwlen
  have hdec := levinDecode_eq_of_witness hmass himp hw
  have heval : x ∈ d.eval (bitsToNat w) := by rw [hd, hdec]; exact Part.mem_some x
  have hpfyx : x ∈ pfy d (bitsToNat w) := by rw [hpfy_eq]; exact heval
  have hKB := KB_le hpfyx
  omega

/-- **The instance at `QB`.** -/
theorem coding_theorem_QB : ∃ C : ℕ, ∀ x k : ℕ, (1 / 2 : ℝ) ^ k < QB x → KB x ≤ k + C :=
  coding_theorem QB_lsc QB_nonneg sum_QB_le_one

/-- **The coding theorem, multiplicative form, at a general semimeasure**: `coding_theorem`'s
additive-in-the-exponent bound restated as a multiplicative one, over any lower-semicomputable
semimeasure `μ` (not only `QB`). -/
theorem coding_theorem_mul {μ : ℕ → ℝ} (hμ : LowerSemicomputable μ) (hnn : ∀ x, 0 ≤ μ x)
    (hsum : ∀ F : Finset ℕ, ∑ x ∈ F, μ x ≤ 1) :
    ∃ C : ℕ, ∀ x : ℕ, μ x ≤ 2 ^ C * (1 / 2 : ℝ) ^ (KB x) := by
  obtain ⟨C, hC⟩ := coding_theorem hμ hnn hsum
  refine ⟨C + 1, fun x => ?_⟩
  by_cases hex : ∃ k, (1 / 2 : ℝ) ^ k < μ x
  · set k0 := Nat.find hex with hk0def
    have hk0spec : (1 / 2 : ℝ) ^ k0 < μ x := Nat.find_spec hex
    have hKBle : KB x ≤ k0 + C := hC x k0 hk0spec
    have hμx1 : μ x ≤ 1 := by have := hsum {x}; simpa using this
    have hk0pos : 0 < k0 := by
      rcases Nat.eq_zero_or_pos k0 with hz | hpos
      · exfalso
        rw [hz, pow_zero] at hk0spec
        linarith
      · exact hpos
    have hnotmin : ¬ (1 / 2 : ℝ) ^ (k0 - 1) < μ x := Nat.find_min hex (by omega)
    have hμle : μ x ≤ (1 / 2 : ℝ) ^ (k0 - 1) := not_lt.mp hnotmin
    have hstep : μ x * (1 / 2 : ℝ) ^ (C + 1) ≤ (1 / 2 : ℝ) ^ (KB x) :=
      calc μ x * (1 / 2 : ℝ) ^ (C + 1)
          ≤ (1 / 2 : ℝ) ^ (k0 - 1) * (1 / 2 : ℝ) ^ (C + 1) :=
            mul_le_mul_of_nonneg_right hμle (by positivity)
        _ = (1 / 2 : ℝ) ^ (k0 + C) := by rw [← pow_add]; congr 1; omega
        _ ≤ (1 / 2 : ℝ) ^ (KB x) := two_pow_neg_antitone hKBle
    have hone : (2 : ℝ) ^ (C + 1) * (1 / 2 : ℝ) ^ (C + 1) = 1 := by rw [← mul_pow]; norm_num
    calc μ x = μ x * ((2 : ℝ) ^ (C + 1) * (1 / 2 : ℝ) ^ (C + 1)) := by rw [hone, mul_one]
      _ = (2 : ℝ) ^ (C + 1) * (μ x * (1 / 2 : ℝ) ^ (C + 1)) := by ring
      _ ≤ (2 : ℝ) ^ (C + 1) * (1 / 2 : ℝ) ^ (KB x) :=
          mul_le_mul_of_nonneg_left hstep (by positivity)
  · have hμx0 : μ x ≤ 0 := by
      by_contra hpos
      have hpos' : 0 < μ x := not_le.mp hpos
      obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hpos' (show (1 / 2 : ℝ) < 1 from by norm_num)
      exact hex ⟨n, hn⟩
    have hμnn := hnn x
    have hμ0 : μ x = 0 := le_antisymm hμx0 hμnn
    rw [hμ0]
    positivity

/-- **Both directions at `QB`**: with `two_pow_neg_KB_le_QB`,
`2 ^ (-KB x) ≤ QB x ≤ 2 ^ C · 2 ^ (-KB x)`. -/
theorem QB_le_two_pow_mul : ∃ C : ℕ, ∀ x : ℕ, QB x ≤ 2 ^ C * (1 / 2 : ℝ) ^ (KB x) :=
  coding_theorem_mul QB_lsc QB_nonneg sum_QB_le_one

/-- **`QB` is a universal (maximal) lower-semicomputable semimeasure** ([Discovery] §1.1, FV-25):
it dominates every lower-semicomputable semimeasure up to a constant factor. The classical
statement fixes its `m` as ANY maximal such semimeasure, so this shows `QB` is a universal
semimeasure — never "the" universal semimeasure. -/
theorem QB_universal {μ : ℕ → ℝ} (hμ : LowerSemicomputable μ) (hnn : ∀ x, 0 ≤ μ x)
    (hsum : ∀ F : Finset ℕ, ∑ x ∈ F, μ x ≤ 1) :
    ∃ C : ℕ, ∀ x : ℕ, μ x ≤ 2 ^ C * QB x := by
  obtain ⟨C, hC⟩ := coding_theorem_mul hμ hnn hsum
  refine ⟨C, fun x => ?_⟩
  calc μ x ≤ 2 ^ C * (1 / 2 : ℝ) ^ (KB x) := hC x
    _ ≤ 2 ^ C * QB x := mul_le_mul_of_nonneg_left (two_pow_neg_KB_le_QB x) (by positivity)

/-- **A witness to the joint satisfiability of `QB_universal`'s hypotheses**, beyond the instance
the theorem already proves at `μ = QB` (true there at `C = 0`) and the instance it makes vacuous at
`μ = 0` (whose conclusion is `0 ≤ 2 ^ C * QB x`): the point mass at `0`, lower-semicomputable via
the dyadic approximation `a t x := if x = 0 then 2 ^ t else 0`, is a genuine semimeasure the
theorem says something about — it forces `1 ≤ 2 ^ C * QB 0`. -/
theorem QB_universal_nonvacuous :
    ∃ μ : ℕ → ℝ, LowerSemicomputable μ ∧ (∀ x, 0 ≤ μ x) ∧
      (∀ F : Finset ℕ, ∑ x ∈ F, μ x ≤ 1) ∧ μ 0 = 1 := by
  refine ⟨fun x => if x = 0 then 1 else 0, ⟨fun t x => if x = 0 then 2 ^ t else 0, ?_, ?_, ?_, ?_⟩,
    ?_, ?_, ?_⟩
  · have hsel : PrimrecPred (fun p : ℕ × ℕ => p.2 = 0) :=
      Primrec.eq.comp Primrec.snd (Primrec.const 0)
    have hpow2 : Primrec₂ ((· ^ ·) : ℕ → ℕ → ℕ) := Primrec₂.unpaired'.1 Nat.Primrec.pow
    have hpowP : Primrec fun p : ℕ × ℕ => (2 : ℕ) ^ p.1 :=
      hpow2.comp (Primrec.const 2) Primrec.fst
    exact (Primrec.ite hsel hpowP (Primrec.const 0)).to_comp
  · intro t x
    by_cases hx : x = 0
    · simp [hx, pow_succ]
    · simp [hx]
  · intro t x
    by_cases hx : x = 0
    · simp [hx]
    · simp [hx]
  · intro x q hq
    by_cases hx : x = 0
    · subst hx
      exact ⟨0, by simpa using hq⟩
    · simp only [ite_eq_right hx] at hq
      exact ⟨0, by simpa [hx] using hq⟩
  · intro x
    by_cases hx : x = 0 <;> simp [hx]
  · intro F
    simp only [Finset.sum_ite_eq']
    split <;> norm_num
  · simp

end PrefixMachine
