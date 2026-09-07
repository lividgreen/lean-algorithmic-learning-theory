/-
Copyright (c) 2026 Mykola Palamarchuk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mykola Palamarchuk
-/
import ALT.CodingTheoremBitwise

-- Formal-check file, not Mathlib-destined: opt out of the house-style header linter.
set_option linter.style.header false

/-!
# The coding theorem with a logarithmic loss ([Discovery] §1.1, FV-21)

Provenance: [Discovery] §1.1 and FV-21, over the universal prefix machine `PrefixMachine.KB`, a
`LowerSemicomputable` semimeasure, and the combinatorial ingredients of `ALT/CodingTheoremWeak.lean`
(`gammaCode`, `bitsFixed`, `card_exceeds_lt`).

## What this establishes

* `coding_theorem_weak`: for a lower-semicomputable semimeasure `μ`, `∃ C, ∀ x k, (1/2)^k < μ x →
  KB x ≤ k + 2 * Nat.size k + C` — the coding theorem with a logarithmic loss.
* `coding_theorem_weak_QB`: the instance at `PrefixMachine.QB`.
* The decoder behind it: `firesAt`/`firingCountBefore`, the level-`k` request/firing search over a
  `LowerSemicomputable` witness `a`; `parseBits`, recovering `(k, i)` from a `gammaCode`/`bitsFixed`
  bit-string; `decodeFn`, the two composed into one partial recursive function, and
  `prefixFree_decodeFn_dom`, its domain's prefix-freeness.

## What this does NOT establish (flagged)

* The `O(1)` coding theorem and the online Kraft–Chaitin invariant it needs are not attempted here.
-/

namespace PrefixMachine

open Nat.Partrec Nat.Partrec.Code AdditiveComplexity CodeEvalLaws KolmogorovComplexity

/-! ## The level-`k` request/firing combinatorics -/

section Decoder

variable (a : ℕ → ℕ → ℕ)

/-- `y`'s dyadic approximation has crossed the level-`k` threshold by stage `t`. -/
abbrev Crossed (k t y : ℕ) : Prop := 2 ^ t < 2 ^ k * a t y

private theorem crossed_iff_real (k t y : ℕ) :
    Crossed a k t y ↔ (1 / 2 : ℝ) ^ k < (a t y : ℝ) / 2 ^ t := by
  unfold Crossed
  rw [show ((1 : ℝ) / 2) ^ k = 1 / 2 ^ k from by rw [div_pow, one_pow]]
  rw [div_lt_div_iff₀ (by positivity) (by positivity), one_mul, mul_comm ((a t y : ℝ)) (2 ^ k)]
  constructor
  · intro h; exact_mod_cast h
  · intro h; exact_mod_cast h

/-- Once crossed, `y` stays crossed: the dyadic ratio only rises. -/
private theorem crossed_succ
    (ha_mono : ∀ t x, (a t x : ℝ) / 2 ^ t ≤ (a (t + 1) x : ℝ) / 2 ^ (t + 1))
    (k t y : ℕ) (h : Crossed a k t y) : Crossed a k (t + 1) y := by
  rw [crossed_iff_real] at h ⊢
  exact lt_of_lt_of_le h (ha_mono t y)

private theorem crossed_mono
    (ha_mono : ∀ t x, (a t x : ℝ) / 2 ^ t ≤ (a (t + 1) x : ℝ) / 2 ^ (t + 1))
    (k y : ℕ) : ∀ {t t' : ℕ}, t ≤ t' → Crossed a k t y → Crossed a k t' y := by
  intro t t' hle h
  induction t', hle using Nat.le_induction with
  | base => exact h
  | succ n _ ih => exact crossed_succ a ha_mono k n y ih

/-- A value `y` with `(1/2) ^ k < μ y` eventually crosses the level-`k` threshold. -/
private theorem exists_first_cross {μ : ℕ → ℝ}
    (ha_lt : ∀ x (q : ℝ), q < μ x → ∃ t, q < (a t x : ℝ) / 2 ^ t)
    (k y : ℕ) (hy : (1 / 2 : ℝ) ^ k < μ y) : ∃ t, Crossed a k t y :=
  (ha_lt y ((1 / 2 : ℝ) ^ k) hy).imp fun t ht => (crossed_iff_real a k t y).mpr ht

/-- Conversely, a value that ever crosses satisfies `(1/2) ^ k < μ y`. -/
private theorem lt_mu_of_crossed {μ : ℕ → ℝ} (ha_le : ∀ t x, (a t x : ℝ) / 2 ^ t ≤ μ x)
    (k t y : ℕ) (h : Crossed a k t y) : (1 / 2 : ℝ) ^ k < μ y :=
  lt_of_lt_of_le ((crossed_iff_real a k t y).mp h) (ha_le t y)

/-- The level-`k` request encoded at step `m = Nat.pair t y` fires: `t` is the first stage at which
`y` crosses. -/
def firesAt (k m : ℕ) : Bool :=
  decide (Crossed a k m.unpair.1 m.unpair.2) &&
    (decide (m.unpair.1 = 0) || !decide (Crossed a k (m.unpair.1 - 1) m.unpair.2))

private theorem firesAt_iff (ha_mono : ∀ t x, (a t x : ℝ) / 2 ^ t ≤ (a (t + 1) x : ℝ) / 2 ^ (t + 1))
    (k t y : ℕ) :
    firesAt a k (Nat.pair t y) = true ↔ Crossed a k t y ∧ ∀ t' < t, ¬ Crossed a k t' y := by
  unfold firesAt
  simp only [Nat.unpair_pair, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq,
    Bool.not_eq_true', decide_eq_false_iff_not]
  constructor
  · rintro ⟨hcross, ht0 | hnotprev⟩
    · exact ⟨hcross, fun t' ht' => absurd ht' (by omega)⟩
    · refine ⟨hcross, fun t' ht' hcross' => hnotprev ?_⟩
      exact crossed_mono a ha_mono k y (show t' ≤ t - 1 by omega) hcross'
  · rintro ⟨hcross, hnone⟩
    refine ⟨hcross, ?_⟩
    rcases Nat.eq_zero_or_pos t with ht0 | htpos
    · exact Or.inl ht0
    · exact Or.inr (hnone (t - 1) (by omega))

private theorem firesAt_iff_eq_find
    (ha_mono : ∀ t x, (a t x : ℝ) / 2 ^ t ≤ (a (t + 1) x : ℝ) / 2 ^ (t + 1))
    (k y : ℕ) (h : ∃ t, Crossed a k t y) (t : ℕ) :
    firesAt a k (Nat.pair t y) = true ↔ t = Nat.find h := by
  rw [firesAt_iff a ha_mono k t y, eq_comm, Nat.find_eq_iff]

/-- Firing steps sharing the same target `y` coincide. -/
private theorem firesAt_eq_of_same_y
    (ha_mono : ∀ t x, (a t x : ℝ) / 2 ^ t ≤ (a (t + 1) x : ℝ) / 2 ^ (t + 1))
    (k m1 m2 : ℕ) (h1 : firesAt a k m1 = true) (h2 : firesAt a k m2 = true)
    (hy : (Nat.unpair m1).2 = (Nat.unpair m2).2) : m1 = m2 := by
  set t1 := (Nat.unpair m1).1 with ht1def
  set y := (Nat.unpair m1).2 with hydef
  set t2 := (Nat.unpair m2).1 with ht2def
  have hm1eq : m1 = Nat.pair t1 y := (Nat.pair_unpair m1).symm
  have hm2eq : m2 = Nat.pair t2 y := by rw [hy]; exact (Nat.pair_unpair m2).symm
  rw [hm1eq] at h1
  rw [hm2eq] at h2
  have hex : ∃ t, Crossed a k t y := ⟨t1, ((firesAt_iff a ha_mono k t1 y).mp h1).1⟩
  have ht1eq : t1 = Nat.find hex := (firesAt_iff_eq_find a ha_mono k y hex t1).mp h1
  have ht2eq : t2 = Nat.find hex := (firesAt_iff_eq_find a ha_mono k y hex t2).mp h2
  rw [hm1eq, hm2eq, ht1eq, ht2eq]

/-- **Markov's bound for the firing steps**: at level `k`, fewer than `2 ^ k` firing steps occur by
any stage `N`. -/
theorem card_firesAt_lt {μ : ℕ → ℝ}
    (ha_mono : ∀ t x, (a t x : ℝ) / 2 ^ t ≤ (a (t + 1) x : ℝ) / 2 ^ (t + 1))
    (ha_le : ∀ t x, (a t x : ℝ) / 2 ^ t ≤ μ x)
    (hnn : ∀ x, 0 ≤ μ x) (hsum : ∀ F : Finset ℕ, ∑ x ∈ F, μ x ≤ 1) (k N : ℕ) :
    ((Finset.range (N + 1)).filter (fun m => firesAt a k m = true)).card < 2 ^ k := by
  classical
  set S := (Finset.range (N + 1)).filter (fun m => firesAt a k m = true) with hSdef
  have hinj : Set.InjOn (fun m => (Nat.unpair m).2) S := by
    intro m1 hm1 m2 hm2 heq
    simp only [hSdef, Finset.coe_filter, Set.mem_ofPred_eq] at hm1 hm2
    exact firesAt_eq_of_same_y a ha_mono k m1 m2 hm1.2 hm2.2 heq
  rw [(Finset.card_image_of_injOn hinj).symm]
  apply card_exceeds_lt hnn hsum
  intro y hy
  simp only [Finset.mem_image] at hy
  obtain ⟨m, hmS, hmy⟩ := hy
  simp only [hSdef, Finset.mem_filter] at hmS
  subst hmy
  exact lt_mu_of_crossed a ha_le k (Nat.unpair m).1 (Nat.unpair m).2
    (((firesAt_iff a ha_mono k (Nat.unpair m).1 (Nat.unpair m).2).mp
      (by rw [Nat.pair_unpair]; exact hmS.2)).1)

/-- The number of level-`k` firing steps strictly before `m`. -/
def firingCountBefore (k m : ℕ) : ℕ :=
  m.rec 0 (fun m' acc => acc + if firesAt a k m' then 1 else 0)

private theorem firingCountBefore_succ (k m : ℕ) :
    firingCountBefore a k (m + 1)
      = firingCountBefore a k m + if firesAt a k m then 1 else 0 := rfl

private theorem firingCountBefore_eq (k m : ℕ) :
    firingCountBefore a k m = ((Finset.range m).filter (fun m' => firesAt a k m')).card := by
  induction m with
  | zero => rfl
  | succ m ih =>
      rw [firingCountBefore_succ, ih, Finset.range_add_one, Finset.filter_insert]
      split
      · rw [Finset.card_insert_of_notMem (by simp)]
      · simp

private theorem firingCountBefore_mono (k : ℕ) : Monotone (firingCountBefore a k) := by
  intro m m' hle
  simp only [firingCountBefore_eq]
  refine Finset.card_le_card (Finset.filter_subset_filter _ ?_)
  exact Finset.range_subset.mpr fun i hi => Finset.mem_range.mpr (by omega)

/-- No earlier step can also be the `(i+1)`-th firing. -/
private theorem firesAt_count_least (k m i : ℕ) (_hfire : firesAt a k m = true)
    (hcount : firingCountBefore a k m = i) :
    ∀ m' < m, ¬ (firesAt a k m' = true ∧ firingCountBefore a k m' = i) := by
  rintro m' hm' ⟨hfire', hcount'⟩
  have h1 : firingCountBefore a k (m' + 1) = firingCountBefore a k m' + 1 := by
    rw [firingCountBefore_succ, if_pos hfire']
  have h2 : firingCountBefore a k (m' + 1) ≤ firingCountBefore a k m :=
    firingCountBefore_mono a k (by omega)
  omega

/-- `Nat.rfind` locates the `(i+1)`-th firing at the step witnessing its existence. -/
private theorem rfind_firesAt_eq
    (k i : ℕ) (h : ∃ m, firesAt a k m = true ∧ firingCountBefore a k m = i) :
    Nat.rfind (fun m => Part.some (firesAt a k m && decide (firingCountBefore a k m = i)))
      = Part.some (Nat.find h) := by
  apply Part.eq_some_iff.mpr
  apply Nat.mem_rfind.mpr
  have hspec := Nat.find_spec h
  have hleast := firesAt_count_least a k (Nat.find h) i hspec.1 hspec.2
  refine ⟨?_, fun {m'} hm' => ?_⟩
  · rw [Part.mem_some_iff, hspec.1, hspec.2]
    simp
  · rw [Part.mem_some_iff]
    symm
    rw [Bool.and_eq_false_iff]
    by_cases hf : firesAt a k m' = true
    · refine Or.inr (decide_eq_false_iff_not.mpr fun hcount' => ?_)
      exact hleast m' hm' ⟨hf, hcount'⟩
    · exact Or.inl (Bool.not_eq_true _ ▸ hf)

/-- **The rank bound**: a firing's own count of earlier firings never reaches `2 ^ k`. -/
private theorem firingCountBefore_lt_of_fires {μ : ℕ → ℝ}
    (ha_mono : ∀ t x, (a t x : ℝ) / 2 ^ t ≤ (a (t + 1) x : ℝ) / 2 ^ (t + 1))
    (ha_le : ∀ t x, (a t x : ℝ) / 2 ^ t ≤ μ x)
    (hnn : ∀ x, 0 ≤ μ x) (hsum : ∀ F : Finset ℕ, ∑ x ∈ F, μ x ≤ 1) (k m : ℕ)
    (hfire : firesAt a k m = true) : firingCountBefore a k m < 2 ^ k := by
  have h1 : firingCountBefore a k (m + 1) = firingCountBefore a k m + 1 := by
    rw [firingCountBefore_succ, if_pos hfire]
  have h2 : firingCountBefore a k (m + 1) < 2 ^ k := by
    rw [firingCountBefore_eq]
    exact card_firesAt_lt a ha_mono ha_le hnn hsum k m
  omega

/-! ### Computability of the request/firing machinery -/

private theorem primrec_pow' : Primrec₂ ((· ^ ·) : ℕ → ℕ → ℕ) :=
  Primrec₂.unpaired'.1 Nat.Primrec.pow

set_option maxHeartbeats 1000000 in
-- `Computable₂.comp` over this nested `ℕ × ℕ × ℕ` shape is heavy to elaborate; the default 200k
-- heartbeats is short (mirrors the Berry-search elaboration in `ALT/ChaitinIncompleteness.lean`).
private theorem computable_crossedBool (ha_comp : Computable₂ a) :
    Computable fun p : ℕ × ℕ × ℕ => decide (Crossed a p.1 p.2.1 p.2.2) := by
  have hpow_t : Primrec fun p : ℕ × ℕ × ℕ => (2 : ℕ) ^ p.2.1 :=
    primrec_pow'.comp (Primrec.const 2) (Primrec.fst.comp Primrec.snd)
  have hpow_k : Primrec fun p : ℕ × ℕ × ℕ => (2 : ℕ) ^ p.1 :=
    primrec_pow'.comp (Primrec.const 2) Primrec.fst
  have hat : Computable fun p : ℕ × ℕ × ℕ => a p.2.1 p.2.2 :=
    ha_comp.comp (Primrec.fst.comp Primrec.snd).to_comp (Primrec.snd.comp Primrec.snd).to_comp
  have hrhs : Computable fun p : ℕ × ℕ × ℕ => (2 : ℕ) ^ p.1 * a p.2.1 p.2.2 :=
    Primrec.nat_mul.to_comp.comp hpow_k.to_comp hat
  exact Primrec.nat_lt.decide.to_comp.comp hpow_t.to_comp hrhs

set_option maxHeartbeats 1000000 in
-- Same reason as `computable_crossedBool` above.
private theorem computable₂_firesAt (ha_comp : Computable₂ a) : Computable₂ (firesAt a) := by
  have ht : Primrec fun p : ℕ × ℕ => (Nat.unpair p.2).1 :=
    Primrec.fst.comp (Primrec.unpair.comp Primrec.snd)
  have hy : Primrec fun p : ℕ × ℕ => (Nat.unpair p.2).2 :=
    Primrec.snd.comp (Primrec.unpair.comp Primrec.snd)
  have hk : Primrec fun p : ℕ × ℕ => p.1 := Primrec.fst
  have hq1 : Primrec fun p : ℕ × ℕ => (p.1, (Nat.unpair p.2).1, (Nat.unpair p.2).2) :=
    hk.pair (ht.pair hy)
  have hc1 : Computable fun p : ℕ × ℕ =>
      decide (Crossed a p.1 (Nat.unpair p.2).1 (Nat.unpair p.2).2) :=
    ((computable_crossedBool a ha_comp).comp hq1.to_comp).of_eq fun p => rfl
  have hq0 : Primrec fun p : ℕ × ℕ => (p.1, (Nat.unpair p.2).1 - 1, (Nat.unpair p.2).2) :=
    hk.pair ((Primrec.nat_sub.comp ht (Primrec.const 1)).pair hy)
  have hc0 : Computable fun p : ℕ × ℕ =>
      decide (Crossed a p.1 ((Nat.unpair p.2).1 - 1) (Nat.unpair p.2).2) :=
    ((computable_crossedBool a ha_comp).comp hq0.to_comp).of_eq fun p => rfl
  have heq0 : Primrec fun p : ℕ × ℕ => decide ((Nat.unpair p.2).1 = 0) :=
    Primrec.eq.decide.comp ht (Primrec.const 0)
  have hcond : Computable fun p : ℕ × ℕ =>
      decide ((Nat.unpair p.2).1 = 0) || !decide (Crossed a p.1 ((Nat.unpair p.2).1 - 1)
        (Nat.unpair p.2).2) :=
    (Primrec.or.to_comp.comp heq0.to_comp (Primrec.not.to_comp.comp hc0)).of_eq fun p => rfl
  have hres : Computable fun p : ℕ × ℕ =>
      decide (Crossed a p.1 (Nat.unpair p.2).1 (Nat.unpair p.2).2) &&
        (decide ((Nat.unpair p.2).1 = 0) ||
          !decide (Crossed a p.1 ((Nat.unpair p.2).1 - 1) (Nat.unpair p.2).2)) :=
    (Primrec.and.to_comp.comp hc1 hcond).of_eq fun p => rfl
  exact hres.of_eq fun p => rfl

private theorem computable₂_firingCountBefore (ha_comp : Computable₂ a) :
    Computable₂ (firingCountBefore a) := by
  have hh : Computable₂ fun (p : ℕ × ℕ) (yacc : ℕ × ℕ) =>
      yacc.2 + if firesAt a p.1 yacc.1 then 1 else 0 := by
    have hfires : Computable fun q : (ℕ × ℕ) × ℕ × ℕ => firesAt a q.1.1 q.2.1 :=
      (Computable.comp (computable₂_firesAt a ha_comp)
        ((Primrec.fst.comp Primrec.fst).pair (Primrec.fst.comp Primrec.snd)).to_comp).of_eq
        fun q => rfl
    have := Computable.cond hfires
      (Computable.succ.comp (Primrec.snd.comp Primrec.snd).to_comp)
      (Primrec.snd.comp Primrec.snd).to_comp
    exact this.of_eq fun q => by cases hfa : firesAt a q.1.1 q.2.1 <;> simp [hfa]
  have := Computable.nat_rec (f := fun p : ℕ × ℕ => p.2) (Primrec.snd.to_comp)
    (g := fun _ : ℕ × ℕ => (0 : ℕ)) (Computable.const 0) hh
  exact this.of_eq fun p => by
    induction p.2 with
    | zero => rfl
    | succ m ih => simp [firingCountBefore_succ, ih]

/-- Search over steps for the `(i + 1)`-th level-`k` firing, and output its target. -/
def searchFiring (k i : ℕ) : Part ℕ :=
  (Nat.rfind fun m => Part.some (firesAt a k m && decide (firingCountBefore a k m = i))).map
    fun m => (Nat.unpair m).2

private theorem computable_searchCond (ha_comp : Computable₂ a) :
    Computable fun p : (ℕ × ℕ) × ℕ =>
      firesAt a p.1.1 p.2 && decide (firingCountBefore a p.1.1 p.2 = p.1.2) := by
  have hfires : Computable fun p : (ℕ × ℕ) × ℕ => firesAt a p.1.1 p.2 :=
    (Computable.comp (computable₂_firesAt a ha_comp)
      ((Primrec.fst.comp Primrec.fst).pair Primrec.snd).to_comp).of_eq fun p => rfl
  have hfc : Computable fun p : (ℕ × ℕ) × ℕ => firingCountBefore a p.1.1 p.2 :=
    (Computable.comp (computable₂_firingCountBefore a ha_comp)
      ((Primrec.fst.comp Primrec.fst).pair Primrec.snd).to_comp).of_eq fun p => rfl
  have hcount : Computable fun p : (ℕ × ℕ) × ℕ =>
      decide (firingCountBefore a p.1.1 p.2 = p.1.2) :=
    (Primrec.eq.decide.to_comp.comp hfc (Primrec.snd.comp Primrec.fst).to_comp).of_eq fun p => rfl
  exact (Primrec.and.to_comp.comp hfires hcount).of_eq fun p => rfl

private theorem partrec₂_searchFiring (ha_comp : Computable₂ a) : Partrec₂ (searchFiring a) := by
  have hcond2 : Computable₂ fun (ki : ℕ × ℕ) (m : ℕ) =>
      firesAt a ki.1 m && decide (firingCountBefore a ki.1 m = ki.2) :=
    computable_searchCond a ha_comp
  have hpart : Partrec₂ fun (ki : ℕ × ℕ) (m : ℕ) =>
      (Part.some (firesAt a ki.1 m && decide (firingCountBefore a ki.1 m = ki.2)) : Part Bool) :=
    (Computable₂.partrec₂ hcond2).of_eq fun n => rfl
  have hrfind : Partrec fun ki : ℕ × ℕ =>
      Nat.rfind fun m =>
        Part.some (firesAt a ki.1 m && decide (firingCountBefore a ki.1 m = ki.2)) :=
    Partrec.rfind hpart
  have hmap : Computable₂ fun (_ : ℕ × ℕ) (m : ℕ) => (Nat.unpair m).2 :=
    (Primrec.snd.comp Primrec.unpair).to_comp.comp Primrec.snd.to_comp
  exact (Partrec.map hrfind hmap).of_eq fun ki => rfl

/-- **The search finds `x` at its own rank among the level-`k` firings.** -/
private theorem searchFiring_eq {μ : ℕ → ℝ}
    (ha_mono : ∀ t x, (a t x : ℝ) / 2 ^ t ≤ (a (t + 1) x : ℝ) / 2 ^ (t + 1))
    (ha_lt : ∀ x (q : ℝ), q < μ x → ∃ t, q < (a t x : ℝ) / 2 ^ t)
    (k x : ℕ) (hx : (1 / 2 : ℝ) ^ k < μ x) :
    searchFiring a k
        (firingCountBefore a k (Nat.pair (Nat.find (exists_first_cross a ha_lt k x hx)) x))
      = Part.some x := by
  set t_x := Nat.find (exists_first_cross a ha_lt k x hx) with ht_xdef
  set m_x := Nat.pair t_x x with hm_xdef
  set r_x := firingCountBefore a k m_x with hr_xdef
  have hfire_x : firesAt a k m_x = true :=
    (firesAt_iff_eq_find a ha_mono k x (exists_first_cross a ha_lt k x hx) t_x).mpr rfl
  have h_ex : ∃ m, firesAt a k m = true ∧ firingCountBefore a k m = r_x := ⟨m_x, hfire_x, rfl⟩
  have hleast := firesAt_count_least a k m_x r_x hfire_x rfl
  have hfindeq : Nat.find h_ex = m_x := (Nat.find_eq_iff h_ex).mpr ⟨⟨hfire_x, rfl⟩, hleast⟩
  unfold searchFiring
  rw [rfind_firesAt_eq a k r_x h_ex, hfindeq]
  simp [hm_xdef]

end Decoder

/-! ## The parser: recovering `(k, i)` from an input's `gammaCode`/`bitsFixed` structure -/

private theorem primrec_ofBitsFixed : Primrec ofBitsFixed := by
  have hstep : Primrec₂ fun (acc : ℕ) (b : Bool) => 2 * acc + b.toNat :=
    Primrec.nat_add.comp
      (Primrec.nat_mul.comp (Primrec.const 2) Primrec.fst)
      ((Primrec.dom_bool Bool.toNat).comp Primrec.snd)
  have hh : Primrec₂ fun (_ : List Bool) (sb : ℕ × Bool) => 2 * sb.1 + sb.2.toNat :=
    Primrec.comp₂ hstep Primrec₂.right
  exact Primrec.list_foldl Primrec.id (Primrec.const 0) hh

/-- Parse a bit-string as `gammaCode k ++ bitsFixed k i`: the leading `false`-run's length gives
`k`'s own header length; the next block of that length gives `k` itself; what remains, if it has
exactly `k` bits, gives `i`. -/
def parseBits (w : List Bool) : Option (ℕ × ℕ) :=
  let L := (w.takeWhile (fun b => !b)).length
  let k := bitsToNat ((w.drop (L + 1)).take L)
  if w.length = 2 * L + 1 + k then some (k, ofBitsFixed (w.drop (2 * L + 1))) else none

theorem primrec_parseBits : Primrec parseBits := by
  have hL : Primrec fun w : List Bool => (w.takeWhile (fun b => !b)).length :=
    Primrec.list_length.comp (Primrec.list_takeWhile Primrec.not)
  have hwL : Primrec fun w : List Bool => (w, (w.takeWhile (fun b => !b)).length) :=
    Primrec.id.pair hL
  have hdrop : Primrec fun p : List Bool × ℕ => (p.1.drop (p.2 + 1)) :=
    Primrec.list_drop.comp (Primrec.succ.comp Primrec.snd) Primrec.fst
  have htake : Primrec fun p : List Bool × ℕ => (p.1.drop (p.2 + 1)).take p.2 :=
    Primrec.list_take.comp Primrec.snd hdrop
  have hkOfWL : Primrec fun p : List Bool × ℕ => bitsToNat ((p.1.drop (p.2 + 1)).take p.2) :=
    primrec_bitsToNat.comp htake
  have hk : Primrec fun w : List Bool => bitsToNat ((w.drop
      ((w.takeWhile (fun b => !b)).length + 1)).take (w.takeWhile (fun b => !b)).length) :=
    hkOfWL.comp hwL
  have hq : Primrec fun w : List Bool =>
      ((w, (w.takeWhile (fun b => !b)).length),
        bitsToNat ((w.drop ((w.takeWhile (fun b => !b)).length + 1)).take
          (w.takeWhile (fun b => !b)).length)) :=
    hwL.pair hk
  have hcond : Primrec fun q : (List Bool × ℕ) × ℕ =>
      decide (q.1.1.length = 2 * q.1.2 + 1 + q.2) :=
    Primrec.eq.decide.comp
      (Primrec.list_length.comp (Primrec.fst.comp Primrec.fst))
      (Primrec.nat_add.comp
        (Primrec.nat_add.comp
          (Primrec.nat_mul.comp (Primrec.const 2) (Primrec.snd.comp Primrec.fst))
          (Primrec.const 1))
        Primrec.snd)
  have houtput : Primrec fun q : (List Bool × ℕ) × ℕ =>
      (some (q.2, ofBitsFixed (q.1.1.drop (2 * q.1.2 + 1))) : Option (ℕ × ℕ)) :=
    Primrec.option_some.comp
      (Primrec.snd.pair (primrec_ofBitsFixed.comp
        (Primrec.list_drop.comp
          (Primrec.nat_add.comp
            (Primrec.nat_mul.comp (Primrec.const 2) (Primrec.snd.comp Primrec.fst))
            (Primrec.const 1))
          (Primrec.fst.comp Primrec.fst))))
  have hres := Primrec.cond hcond houtput (Primrec.const none)
  have hcomp := hres.comp hq
  refine hcomp.of_eq fun w => ?_
  unfold parseBits
  simp only [Bool.cond_eq_ite, decide_eq_true_eq]

private theorem takeWhile_not_replicate_true_append (L : ℕ) (tail : List Bool) :
    (List.replicate L false ++ (true :: tail)).takeWhile (fun b => !b)
      = List.replicate L false := by
  induction L with
  | zero => simp
  | succ L ih => simp [List.replicate_succ, ih]

/-- On its intended input, the parser recovers `(k, i)` exactly. -/
theorem parseBits_gammaCode_bitsFixed (k i : ℕ) (hi : i < 2 ^ k) :
    parseBits (gammaCode k ++ bitsFixed k i) = some (k, i) := by
  set L := (natToBits k).length with hLdef
  have hgc : gammaCode k ++ bitsFixed k i
      = List.replicate L false ++ (true :: (natToBits k ++ bitsFixed k i)) := by
    rw [hLdef]
    unfold gammaCode
    simp [List.append_assoc]
  have hgc2 : gammaCode k ++ bitsFixed k i
      = (List.replicate L false ++ [true]) ++ (natToBits k ++ bitsFixed k i) := by
    rw [hgc]; simp
  have hLen1 : (List.replicate L false ++ [true]).length = L + 1 := by simp
  have hdrop1 : (gammaCode k ++ bitsFixed k i).drop (L + 1)
      = natToBits k ++ bitsFixed k i := by
    rw [hgc2, ← hLen1]; exact List.drop_left
  have htake1 : (natToBits k ++ bitsFixed k i).take L = natToBits k := by
    rw [hLdef]; exact List.take_left
  have hLenGC : (gammaCode k).length = 2 * L + 1 := length_gammaCode_eq k
  have hdrop2 : (gammaCode k ++ bitsFixed k i).drop (2 * L + 1)
      = bitsFixed k i := by
    rw [← hLenGC]; exact List.drop_left
  have hlen : (gammaCode k ++ bitsFixed k i).length = 2 * L + 1 + k := by
    rw [List.length_append, hLenGC, length_bitsFixed]
  unfold parseBits
  rw [hgc, takeWhile_not_replicate_true_append]
  simp only [List.length_replicate, ← hgc]
  rw [hdrop1, htake1, bitsToNat_natToBits, if_pos hlen, hdrop2, ofBitsFixed_bitsFixed hi]

/-- The leading `false`-run of any bit-string, read back, is a run of `false`s whose length is its
own — and either exhausts the string or is immediately followed by a `true`. -/
private theorem takeWhile_not_spec (w : List Bool) :
    w.takeWhile (fun b => !b) = List.replicate (w.takeWhile (fun b => !b)).length false ∧
      (w.drop (w.takeWhile (fun b => !b)).length = [] ∨
        (w.drop (w.takeWhile (fun b => !b)).length).head? = some true) := by
  induction w with
  | nil => simp
  | cons b w ih =>
    obtain ⟨ih1, ih2⟩ := ih
    obtain ⟨n, hn⟩ : ∃ n, List.takeWhile (fun b => !b) w = List.replicate n false := ⟨_, ih1⟩
    rw [hn] at ih1 ih2
    simp only [List.length_replicate] at ih1 ih2
    cases b with
    | false =>
        rw [List.takeWhile_cons_of_pos (by simp), hn]
        refine ⟨?_, ?_⟩
        · rw [List.length_cons, List.length_replicate, List.replicate_succ]
        · simpa using ih2
    | true =>
        rw [List.takeWhile_cons_of_neg (by simp)]
        simp

/-- `bitsFixed` and `ofBitsFixed` are mutual inverses: `bitsFixed` recovers a length-matched
bit-string from its own `ofBitsFixed` value. -/
private theorem bitsFixed_ofBitsFixed (q : List Bool) : bitsFixed q.length (ofBitsFixed q) = q := by
  induction q using List.reverseRecOn with
  | nil => rfl
  | append_singleton q b ih =>
      have hstep : ofBitsFixed (q ++ [b]) = 2 * ofBitsFixed q + b.toNat := by
        unfold ofBitsFixed
        rw [List.foldl_append]
        simp
      rw [List.length_append, List.length_singleton, hstep]
      unfold bitsFixed
      have hi2 : (2 * ofBitsFixed q + b.toNat) / 2 = ofBitsFixed q := by
        rcases b with - | - <;> simp
        omega
      have hmod : (2 * ofBitsFixed q + b.toNat) % 2 = b.toNat := by
        cases b <;> simp
      rw [hi2, hmod, ih, bool_decide_toNat_eq_one]

/-- **Every input the parser accepts has `gammaCode`/`bitsFixed` shape.** -/
private theorem parseBits_eq_some (w : List Bool) (k i : ℕ) (h : parseBits w = some (k, i)) :
    w = gammaCode k ++ bitsFixed k i := by
  unfold parseBits at h
  set L := (w.takeWhile (fun b => !b)).length with hLdef
  set k' := bitsToNat ((w.drop (L + 1)).take L) with hk'def
  by_cases hcond : w.length = 2 * L + 1 + k'
  · rw [if_pos hcond] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨hk, hi⟩ := h
    obtain ⟨hTW, hrest⟩ := takeWhile_not_spec w
    rw [← hLdef] at hTW hrest
    have hLlt : L < w.length := by omega
    have hne : w.drop L ≠ [] := by
      intro hcontra
      have hzero : (w.drop L).length = 0 := by rw [hcontra]; rfl
      rw [List.length_drop] at hzero
      omega
    have hhead : (w.drop L).head? = some true := hrest.resolve_left hne
    have hcons : w.drop L = w[L] :: w.drop (L + 1) := List.drop_eq_getElem_cons hLlt
    have hgetL : w[L] = true := by
      have h2 := hhead
      rw [hcons, List.head?_cons] at h2
      exact Option.some.inj h2
    have htakeL : w.take L = List.replicate L false := by
      have hpre := List.takeWhile_prefix (fun b => !b) (l := w)
      rw [List.prefix_iff_eq_take] at hpre
      rw [← hLdef] at hpre
      rw [← hpre, hTW]
    have hsplit1 : w = List.replicate L false ++ w.drop L := by
      conv_lhs => rw [← List.take_append_drop L w, htakeL]
    have hsplit2 : w.drop L = true :: w.drop (L + 1) := by rw [hcons, hgetL]
    have hkeq : (w.drop (L + 1)).take L = natToBits k := by
      rw [← hk]; exact (natToBits_bitsToNat _).symm
    have hklen : (natToBits k).length = L := by
      have hlenle : L ≤ (w.drop (L + 1)).length := by
        rw [List.length_drop]; omega
      rw [← hkeq, List.length_take, min_eq_left hlenle]
    have hsplit3 : w.drop (L + 1) = natToBits k ++ (w.drop (L + 1)).drop L := by
      conv_lhs => rw [← List.take_append_drop L (w.drop (L + 1)), hkeq]
    have hdroplen : (w.drop (L + 1)).drop L = w.drop (2 * L + 1) := by
      rw [List.drop_drop]; congr 1; omega
    have hqlen : (w.drop (2 * L + 1)).length = k := by
      rw [List.length_drop]; omega
    have hbf : bitsFixed k i = w.drop (2 * L + 1) := by
      rw [← hi, ← hqlen]; exact bitsFixed_ofBitsFixed _
    rw [hsplit1, hsplit2, hsplit3, hdroplen]
    change List.replicate L false ++ true :: (natToBits k ++ w.drop (2 * L + 1))
      = gammaCode k ++ bitsFixed k i
    rw [hbf, ← hklen]
    unfold gammaCode
    simp [List.append_assoc]
  · rw [if_neg hcond] at h
    exact absurd h (by simp)

/-- **The `gammaCode`/`bitsFixed` descriptions are prefix-free.** -/
private theorem prefixFree_gammaCode_bitsFixed :
    PrefixFree {w : List Bool | ∃ k i, w = gammaCode k ++ bitsFixed k i} := by
  rintro w1 ⟨k1, i1, rfl⟩ w2 ⟨k2, i2, rfl⟩ hpre
  by_cases hk : k1 = k2
  · subst hk
    obtain ⟨r, hr⟩ := hpre
    rw [List.append_assoc] at hr
    have hcancel : bitsFixed k1 i1 ++ r = bitsFixed k1 i2 := List.append_cancel_left hr
    have hlen1 := length_bitsFixed k1 i1
    have hlen2 := length_bitsFixed k1 i2
    have hrnil : r = [] := by
      have hlc := congrArg List.length hcancel
      rw [List.length_append, hlen1, hlen2] at hlc
      have : r.length = 0 := by omega
      exact List.eq_nil_of_length_eq_zero this
    rw [hrnil, List.append_nil] at hcancel
    rw [hcancel]
  · obtain ⟨r, hr⟩ := hpre
    rw [List.append_assoc] at hr
    have := gammaCode_append_inj k1 k2 (bitsFixed k1 i1 ++ r) (bitsFixed k2 i2) hr
    exact absurd this.1 hk

/-- **The parser's domain is prefix-free.** -/
private theorem prefixFree_parseBits_dom :
    PrefixFree {w : List Bool | (parseBits w).isSome} := by
  intro w1 hw1 w2 hw2 hpre
  simp only [Set.mem_ofPred_eq] at hw1 hw2
  obtain ⟨⟨k1, i1⟩, hw1'⟩ := Option.isSome_iff_exists.mp hw1
  obtain ⟨⟨k2, i2⟩, hw2'⟩ := Option.isSome_iff_exists.mp hw2
  have he1 := parseBits_eq_some w1 k1 i1 hw1'
  have he2 := parseBits_eq_some w2 k2 i2 hw2'
  exact prefixFree_gammaCode_bitsFixed w1 ⟨k1, i1, he1⟩ w2 ⟨k2, i2, he2⟩ hpre

/-! ## The decoder: parser and search combined -/

section Decoder2

variable (a : ℕ → ℕ → ℕ)

/-- **The decoder**: parse the input's bit-string as `gammaCode k ++ bitsFixed k i`, then search
for the `(i + 1)`-th level-`k` firing and output its target. -/
def decodeFn : ℕ →. ℕ :=
  fun n => (parseBits (natToBits n) : Part (ℕ × ℕ)) >>= fun ki => searchFiring a ki.1 ki.2

theorem partrec_decodeFn (ha_comp : Computable₂ a) : Partrec (decodeFn a) := by
  have hparse : Computable fun n => parseBits (natToBits n) :=
    (Primrec.comp primrec_parseBits primrec_natToBits).to_comp
  have hf : Partrec fun n => (parseBits (natToBits n) : Part (ℕ × ℕ)) :=
    Computable.ofOption hparse
  have hg' : Partrec₂ fun (_ : ℕ) (ki : ℕ × ℕ) => searchFiring a ki.1 ki.2 :=
    (Partrec.comp (partrec₂_searchFiring a ha_comp) Primrec.snd.to_comp).of_eq fun p => rfl
  exact (Partrec.bind hf hg').of_eq fun n => rfl

/-- **Correctness on the intended input**: the decoder outputs `x` from the `gammaCode`/`bitsFixed`
description of its own rank among the level-`k` firings. -/
private theorem decodeFn_eq {μ : ℕ → ℝ}
    (ha_mono : ∀ t x, (a t x : ℝ) / 2 ^ t ≤ (a (t + 1) x : ℝ) / 2 ^ (t + 1))
    (ha_lt : ∀ x (q : ℝ), q < μ x → ∃ t, q < (a t x : ℝ) / 2 ^ t)
    (k x : ℕ) (hx : (1 / 2 : ℝ) ^ k < μ x)
    (hrank : firingCountBefore a k (Nat.pair (Nat.find (exists_first_cross a ha_lt k x hx)) x)
      < 2 ^ k) :
    decodeFn a (bitsToNat (gammaCode k ++
        bitsFixed k (firingCountBefore a k
          (Nat.pair (Nat.find (exists_first_cross a ha_lt k x hx)) x))))
      = Part.some x := by
  set rank := firingCountBefore a k (Nat.pair (Nat.find (exists_first_cross a ha_lt k x hx)) x)
    with hrankdef
  unfold decodeFn
  rw [natToBits_bitsToNat, parseBits_gammaCode_bitsFixed k rank hrank, Part.coe_some]
  exact (Part.bind_some (k, rank) _).trans (searchFiring_eq a ha_mono ha_lt k x hx)

/-- **The domain of the decoder, read as bit-strings, is prefix-free.** -/
theorem prefixFree_decodeFn_dom : PrefixFree (natToBits '' (decodeFn a).Dom) := by
  rintro p ⟨n1, hn1, rfl⟩ q ⟨n2, hn2, rfl⟩ hpre
  have hp1 : natToBits n1 ∈ {w : List Bool | (parseBits w).isSome} := by
    simp only [Set.mem_ofPred_eq]
    rcases Option.eq_none_or_eq_some (parseBits (natToBits n1)) with h0 | ⟨ki, hki⟩
    · exfalso
      have : n1 ∉ (decodeFn a).Dom := by
        unfold decodeFn
        simp [h0]
      exact this hn1
    · simp [hki]
  have hp2 : natToBits n2 ∈ {w : List Bool | (parseBits w).isSome} := by
    simp only [Set.mem_ofPred_eq]
    rcases Option.eq_none_or_eq_some (parseBits (natToBits n2)) with h0 | ⟨ki, hki⟩
    · exfalso
      have : n2 ∉ (decodeFn a).Dom := by
        unfold decodeFn
        simp [h0]
      exact this hn2
    · simp [hki]
  exact prefixFree_parseBits_dom (natToBits n1) hp1 (natToBits n2) hp2 hpre

end Decoder2

/-! ## The coding theorem with a logarithmic loss -/

/-- **The coding theorem with a logarithmic loss.** -/
theorem coding_theorem_weak {μ : ℕ → ℝ} (hμ : LowerSemicomputable μ) (hnn : ∀ x, 0 ≤ μ x)
    (hsum : ∀ F : Finset ℕ, ∑ x ∈ F, μ x ≤ 1) :
    ∃ C : ℕ, ∀ x k : ℕ, (1 / 2 : ℝ) ^ k < μ x → KB x ≤ k + 2 * Nat.size k + C := by
  obtain ⟨a, ha_comp, ha_mono, ha_le, ha_lt⟩ := hμ
  obtain ⟨d, hd⟩ := exists_code.mp (Partrec.nat_iff.mp (partrec_decodeFn a ha_comp))
  have hdom_prefixFree : PrefixFree (natToBits '' d.eval.Dom) := by
    rw [hd]; exact prefixFree_decodeFn_dom a
  have hpfy_eq : pfy d = d.eval := pfy_eq_of_prefixFree d hdom_prefixFree
  refine ⟨elen d + 1, fun x k hx => ?_⟩
  set t_x := Nat.find (exists_first_cross a ha_lt k x hx) with ht_xdef
  set rank := firingCountBefore a k (Nat.pair t_x x) with hrankdef
  have hrank : rank < 2 ^ k :=
    firingCountBefore_lt_of_fires a ha_mono ha_le hnn hsum k (Nat.pair t_x x)
      ((firesAt_iff_eq_find a ha_mono k x (exists_first_cross a ha_lt k x hx) t_x).mpr rfl)
  have hdec : decodeFn a (bitsToNat (gammaCode k ++ bitsFixed k rank)) = Part.some x :=
    decodeFn_eq a ha_mono ha_lt k x hx hrank
  have heval : x ∈ d.eval (bitsToNat (gammaCode k ++ bitsFixed k rank)) := by
    rw [hd, hdec]; exact Part.mem_some x
  have hpfyx : x ∈ pfy d (bitsToNat (gammaCode k ++ bitsFixed k rank)) := by
    rw [hpfy_eq]; exact heval
  have hKB := KB_le hpfyx
  have hlen : (gammaCode k ++ bitsFixed k rank).length ≤ k + 2 * Nat.size k + 1 := by
    rw [List.length_append, length_bitsFixed]
    have := length_gammaCode k
    omega
  omega

/-- **The instance at `QB`.** -/
theorem coding_theorem_weak_QB :
    ∃ C : ℕ, ∀ x k : ℕ, (1 / 2 : ℝ) ^ k < QB x → KB x ≤ k + 2 * Nat.size k + C :=
  coding_theorem_weak QB_lsc QB_nonneg sum_QB_le_one

end PrefixMachine
