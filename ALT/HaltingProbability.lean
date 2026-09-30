/-
Copyright (c) 2026 Mykola Palamarchuk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mykola Palamarchuk
-/
module

public import ALT.CodingTheoremBitwise
import all ALT.CodingTheoremBitwise
public import ALT.PrefixInvarianceKB

-- Formal-check file, not Mathlib-destined: opt out of the house-style header linter.
set_option linter.style.header false
-- The `#guard_msgs` axiom-guard expectations below cannot be wrapped (the line must match
-- compiler output verbatim); the exemption is for those three lines, per `formal/CLAUDE.md`.
set_option linter.style.longLine false

/-!
# The halting probability of the prefix machine ([Discovery] §1.1, FV-21, FV-26)

Provenance: [Discovery] §1.1, over the algorithmic probability `PrefixMachine.QB` (FV-21: its
semimeasure bound `two_pow_neg_KB_le_QB` and its sum bounds) and the universal-machine invariance
`PrefixMachine.KB_partial_map_le`. Extends `ALT/CodingTheoremBitwise.lean` and
`ALT/PrefixInvarianceKB.lean`. No paper sentence consumes `haltingProb` yet.

## What this establishes

* `haltingProb`: the total algorithmic probability `∑' x, QB x`, with `haltingProb_nonneg` and
  `haltingProb_le_one`.
* `HaltingMassSpec`, `HaltingRevealedSpec`: two specifications a computable construction can meet
  — a stage mass rising to `haltingProb` and a revealed list whose absent values sit inside the
  mass still missing at that stage.
* `haltingProb_prefix_incompressible_of`: Chaitin's theorem on this machine's halting probability,
  conditional on the two specifications — any dyadic lower approximation `m / 2 ^ n` to
  `haltingProb` within `2 ^ (-n)` of it has, as the pair `(n, m)`, prefix complexity at least
  `n − c`. The threshold is shifted by `2 ^ (-n)` rather than exact: the plain threshold `m / 2 ^ n`
  need never be passed by a rising approximation, whereas the shifted one is passed unconditionally
  whenever `m / 2 ^ n ≤ haltingProb`.
* `haltingProb_prefix_incompressible_nonvacuous`: the theorem's two hypotheses are met at every
  precision `n`, by the floor of `haltingProb · 2 ^ n` — needing nothing about `haltingProb` beyond
  `0 ≤ haltingProb`.
* `revealedList`, `stageMass`: a computable revealed list and stage mass meeting
  `HaltingRevealedSpec` and `HaltingMassSpec` respectively (`revealedList_spec`, `stageMass_spec`).
* `haltingProb_prefix_incompressible`: **Chaitin's theorem on this machine's halting probability**,
  unconditional — `haltingProb_prefix_incompressible_of` applied to the two constructions above.

## What this does NOT establish (flagged)

* Nothing: the boundary this module once flagged — a construction of `a` and `r` meeting
  `HaltingMassSpec` and `HaltingRevealedSpec` — is closed by `stageMass` and `revealedList`, so
  `haltingProb_prefix_incompressible` is unconditional.
-/


@[expose] public section

namespace PrefixMachine

open Nat.Partrec Nat.Partrec.Code AdditiveComplexity CodeEvalLaws KolmogorovComplexity

/-! ## The halting probability -/

open scoped Classical in
/-- **The halting probability of the prefix machine**: the total algorithmic probability. -/
noncomputable def haltingProb : ℝ := ∑' x : ℕ, QB x

theorem summable_QB' : Summable QB := summable_of_sum_le QB_nonneg sum_QB_le_one

theorem haltingProb_nonneg : 0 ≤ haltingProb := tsum_nonneg QB_nonneg

theorem haltingProb_le_one : haltingProb ≤ 1 := tsum_QB_le_one

/-! ## The two specifications a construction can meet -/

/-- A stage mass for the halting probability: a computable dyadic numerator whose reading
`a t / 2 ^ t` rises with the stage, stays below the halting probability, and reaches every real
under it. -/
def HaltingMassSpec (a : ℕ → ℕ) : Prop :=
  Computable a ∧
    (∀ t, (a t : ℝ) / 2 ^ t ≤ (a (t + 1) : ℝ) / 2 ^ (t + 1)) ∧
    (∀ t, (a t : ℝ) / 2 ^ t ≤ haltingProb) ∧
    (∀ q : ℝ, q < haltingProb → ∃ t, q < (a t : ℝ) / 2 ^ t)

/-- A revealed list for a stage mass: a computable list of the values seen by stage `t`, such that
a value absent from it has its whole algorithmic probability inside the mass still missing at that
stage. -/
def HaltingRevealedSpec (a : ℕ → ℕ) (r : ℕ → List ℕ) : Prop :=
  Computable r ∧ ∀ t x, x ∉ r t → QB x ≤ haltingProb - (a t : ℝ) / 2 ^ t

/-! ## The search: the shifted-threshold stage, then the least value it has not yet revealed -/

section Search

variable (a : ℕ → ℕ) (r : ℕ → List ℕ)

/-- The shifted-threshold predicate on the stage `t`, at precision `n` and dyadic numerator `m`:
either `m` is `0` (the threshold is trivially below the mass) or the numerator has passed
`(m − 1) / 2 ^ n`, read through the cross-multiplication `(m − 1) * 2 ^ t < a t * 2 ^ n`. -/
def searchPred (n m t : ℕ) : Bool :=
  decide (m = 0) || decide ((m - 1) * 2 ^ t < a t * 2 ^ n)

private theorem primrec_pow'' : Primrec₂ ((· ^ ·) : ℕ → ℕ → ℕ) :=
  Primrec₂.unpaired'.1 Nat.Primrec.pow

private theorem computable₂_searchPred (ha : Computable a) :
    Computable₂ fun (p t : ℕ) => searchPred a p.unpair.1 p.unpair.2 t := by
  have hm : Primrec fun q : ℕ × ℕ => (Nat.unpair q.1).2 :=
    Primrec.snd.comp (Primrec.unpair.comp Primrec.fst)
  have hn : Primrec fun q : ℕ × ℕ => (Nat.unpair q.1).1 :=
    Primrec.fst.comp (Primrec.unpair.comp Primrec.fst)
  have ht : Primrec fun q : ℕ × ℕ => q.2 := Primrec.snd
  have heqm0 : Primrec fun q : ℕ × ℕ => decide ((Nat.unpair q.1).2 = 0) :=
    Primrec.eq.decide.comp hm (Primrec.const 0)
  have hat : Computable fun q : ℕ × ℕ => a q.2 := ha.comp ht.to_comp
  have hpow_t : Primrec fun q : ℕ × ℕ => (2 : ℕ) ^ q.2 := primrec_pow''.comp (Primrec.const 2) ht
  have hpow_n : Primrec fun q : ℕ × ℕ => (2 : ℕ) ^ (Nat.unpair q.1).1 :=
    primrec_pow''.comp (Primrec.const 2) hn
  have hsub : Primrec fun q : ℕ × ℕ => (Nat.unpair q.1).2 - 1 :=
    Primrec.nat_sub.comp hm (Primrec.const 1)
  have hlhs : Primrec fun q : ℕ × ℕ => ((Nat.unpair q.1).2 - 1) * 2 ^ q.2 :=
    Primrec.nat_mul.comp hsub hpow_t
  have hrhs : Computable fun q : ℕ × ℕ => a q.2 * 2 ^ (Nat.unpair q.1).1 :=
    Primrec.nat_mul.to_comp.comp hat hpow_n.to_comp
  have hlt : Computable fun q : ℕ × ℕ =>
      decide (((Nat.unpair q.1).2 - 1) * 2 ^ q.2 < a q.2 * 2 ^ (Nat.unpair q.1).1) :=
    Primrec.nat_lt.decide.to_comp.comp hlhs.to_comp hrhs
  exact (Primrec.or.to_comp.comp heqm0.to_comp hlt).of_eq fun q => rfl

/-- The shifted-threshold predicate, at its real reading: `searchPred` holds at `t` exactly when
the stage-`t` mass has passed `m / 2 ^ n − 1 / 2 ^ n`. -/
private theorem searchPred_real_iff (n m t : ℕ) :
    searchPred a n m t = true ↔ (m : ℝ) / 2 ^ n - 1 / 2 ^ n < (a t : ℝ) / 2 ^ t := by
  simp only [searchPred, Bool.or_eq_true, decide_eq_true_eq]
  constructor
  · rintro (hm0 | h)
    · subst hm0
      have h1 : (0 : ℝ) ≤ (a t : ℝ) / 2 ^ t := by positivity
      have h2 : (0 : ℝ) < 1 / 2 ^ n := by positivity
      simp only [Nat.cast_zero, zero_div]
      linarith
    · have hcast : ((m - 1 : ℕ) : ℝ) * 2 ^ t < (a t : ℝ) * 2 ^ n := by exact_mod_cast h
      have hdiv : ((m - 1 : ℕ) : ℝ) / 2 ^ n < (a t : ℝ) / 2 ^ t := by
        rw [div_lt_div_iff₀ (by positivity) (by positivity)]
        nlinarith [hcast]
      have hle : (m : ℝ) - 1 ≤ ((m - 1 : ℕ) : ℝ) := by
        rcases Nat.eq_zero_or_pos m with hm0' | hm0'
        · simp [hm0']
        · have hcast2 : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
            have := Nat.cast_sub (R := ℝ) hm0'
            simpa using this
          linarith [hcast2]
      have hstep : (m : ℝ) / 2 ^ n - 1 / 2 ^ n ≤ ((m - 1 : ℕ) : ℝ) / 2 ^ n := by
        rw [div_sub_div_same]
        gcongr
      linarith [hdiv, hstep]
  · intro hlt
    rcases eq_or_ne m 0 with hm0 | hm0
    · exact Or.inl hm0
    · right
      have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm0
      have hcast2 : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
        have := Nat.cast_sub (R := ℝ) hm1
        simpa using this
      have hdiv : ((m - 1 : ℕ) : ℝ) / 2 ^ n < (a t : ℝ) / 2 ^ t := by
        rw [hcast2]
        have heq : (m : ℝ) / 2 ^ n - 1 / 2 ^ n = ((m : ℝ) - 1) / 2 ^ n := by ring
        rw [← heq]
        exact hlt
      rw [div_lt_div_iff₀ (by positivity) (by positivity)] at hdiv
      have : ((m - 1 : ℕ) : ℝ) * 2 ^ t < (a t : ℝ) * 2 ^ n := by nlinarith [hdiv]
      exact_mod_cast this

/-- The least stage at which the enumerated mass has passed the shifted threshold, from a natural
`p` read as the pair `(n, m)`. -/
def stageOf (p : ℕ) : Part ℕ :=
  Nat.rfind fun t => Part.some (searchPred a p.unpair.1 p.unpair.2 t)

private theorem partrec_stageOf (ha : Computable a) : Partrec (stageOf a) := by
  have hcomp := computable₂_searchPred a ha
  have hpart : Partrec₂ fun (p t : ℕ) =>
      (Part.some (searchPred a p.unpair.1 p.unpair.2 t) : Part Bool) :=
    (Computable₂.partrec₂ hcomp).of_eq fun _ => rfl
  exact (Partrec.rfind hpart).of_eq fun p => rfl

/-- The least value absent from the stage-`t` revealed list. -/
def leastAbsent (t : ℕ) : Part ℕ :=
  Nat.rfind fun x => Part.some (decide (x ∉ r t))

private theorem computable₂_notMem (hr : Computable r) :
    Computable₂ fun (t x : ℕ) => decide (x ∉ r t) := by
  have hidx : Primrec fun p : ℕ × List ℕ => List.idxOf p.1 p.2 := Primrec.list_idxOf
  have hlen : Primrec fun p : ℕ × List ℕ => p.2.length := Primrec.list_length.comp Primrec.snd
  have hnotmem : Primrec fun p : ℕ × List ℕ => decide (p.1 ∉ p.2) := by
    have heq : Primrec fun p : ℕ × List ℕ => decide (List.idxOf p.1 p.2 = p.2.length) :=
      Primrec.eq.decide.comp hidx hlen
    refine heq.of_eq fun p => ?_
    simp [List.idxOf_eq_length_iff]
  have hrt : Computable fun q : ℕ × ℕ => r q.1 := hr.comp Primrec.fst.to_comp
  have hpair : Computable fun q : ℕ × ℕ => (q.2, r q.1) := Computable.pair Primrec.snd.to_comp hrt
  exact (hnotmem.to_comp.comp hpair).of_eq fun q => rfl

private theorem partrec_leastAbsent (hr : Computable r) : Partrec (leastAbsent r) := by
  have hcomp := computable₂_notMem r hr
  have hpart : Partrec₂ fun (t x : ℕ) => (Part.some (decide (x ∉ r t)) : Part Bool) :=
    (Computable₂.partrec₂ hcomp).of_eq fun _ => rfl
  exact (Partrec.rfind hpart).of_eq fun t => rfl

/-- The search this theorem's proof is built on: from `p` read as `(n, m)`, the least value absent
from the revealed list once the enumerated mass has passed the shifted threshold. -/
def searchValue (p : ℕ) : Part ℕ := stageOf a p >>= leastAbsent r

private theorem partrec_searchValue (ha : Computable a) (hr : Computable r) :
    Partrec (searchValue a r) := by
  have hf : Partrec (stageOf a) := partrec_stageOf a ha
  have hg : Partrec₂ fun (_ : ℕ) (t : ℕ) => leastAbsent r t :=
    Partrec.comp (partrec_leastAbsent r hr) Primrec.snd.to_comp
  exact (Partrec.bind hf hg).of_eq fun p => rfl

end Search

/-- A value whose algorithmic probability is below `2 / 2 ^ n` has prefix complexity at least
`n`: the shortest description is one term of the sum (`two_pow_neg_KB_le_QB`), and the constant is
exactly why the conclusion is `n` rather than `n + 1`. -/
private theorem le_KB_of_QB_lt {x n : ℕ} (h : QB x < 2 / 2 ^ n) : n ≤ KB x := by
  have h1 : (1 / 2 : ℝ) ^ KB x < 2 / 2 ^ n := lt_of_le_of_lt (two_pow_neg_KB_le_QB x) h
  have h2 : (1 : ℝ) / 2 ^ KB x < 2 / 2 ^ n := by rwa [div_pow, one_pow] at h1
  rw [div_lt_div_iff₀ (by positivity) (by positivity)] at h2
  have h3 : (2 : ℝ) ^ n < 2 ^ (KB x + 1) := by rw [pow_succ]; nlinarith [h2]
  have h4 : n < KB x + 1 := (pow_lt_pow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).mp h3
  omega

/-! ## The parent theorem -/

/-- **Chaitin's theorem on the prefix machine's halting probability**, at a pair rather than a
binary expansion: any dyadic lower approximation `m / 2 ^ n` to `haltingProb` within `2 ^ (-n)` of
it has, as the pair `(n, m)`, prefix complexity at least `n − c`. Conditional on a stage mass and a
revealed list meeting `HaltingMassSpec` and `HaltingRevealedSpec`. The constant `c` is existential,
as in `KB_partial_map_le`. -/
theorem haltingProb_prefix_incompressible_of {a : ℕ → ℕ} {r : ℕ → List ℕ}
    (ha : HaltingMassSpec a) (hr : HaltingRevealedSpec a r) :
    ∃ c : ℕ, ∀ n m : ℕ,
      (m : ℝ) / 2 ^ n ≤ haltingProb → haltingProb - (m : ℝ) / 2 ^ n ≤ 1 / 2 ^ n →
        n ≤ KB (Nat.pair n m) + c := by
  obtain ⟨ha_comp, -, -, ha_lt⟩ := ha
  obtain ⟨hr_comp, hr_spec⟩ := hr
  have hpart : Partrec (searchValue a r) := partrec_searchValue a r ha_comp hr_comp
  obtain ⟨c, hc⟩ := KB_partial_map_le (searchValue a r) hpart
  refine ⟨c, fun n m hm_le hm_close => ?_⟩
  have hex_t : ∃ t, searchPred a n m t = true := by
    rcases eq_or_ne m 0 with hm0 | hm0
    · exact ⟨0, by simp [searchPred, hm0]⟩
    · have hq_lt : (m : ℝ) / 2 ^ n - 1 / 2 ^ n < haltingProb := by
        have hpos : (0 : ℝ) < 1 / 2 ^ n := by positivity
        linarith
      obtain ⟨t, ht⟩ := ha_lt _ hq_lt
      exact ⟨t, (searchPred_real_iff a n m t).mpr ht⟩
  set t₀ := Nat.find hex_t with ht0def
  have ht0_true : searchPred a n m t₀ = true := Nat.find_spec hex_t
  have hpassed : (m : ℝ) / 2 ^ n - 1 / 2 ^ n < (a t₀ : ℝ) / 2 ^ t₀ :=
    (searchPred_real_iff a n m t₀).mp ht0_true
  have hmiss : haltingProb - (a t₀ : ℝ) / 2 ^ t₀ < 2 / 2 ^ n := by
    have hsplit : (2 : ℝ) / 2 ^ n = 1 / 2 ^ n + 1 / 2 ^ n := by ring
    rw [hsplit]
    linarith [hpassed, hm_close]
  have hex_x : ∃ x, x ∉ r t₀ := by
    have := Infinite.exists_notMem_finset (r t₀).toFinset
    simpa using this
  set x₀ := Nat.find hex_x with hx0def
  have hsv_eq : searchValue a r (Nat.pair n m) = Part.some x₀ := by
    have hstage : stageOf a (Nat.pair n m) = Part.some t₀ := by
      apply Part.eq_some_iff.mpr
      apply Nat.mem_rfind.mpr
      refine ⟨?_, ?_⟩
      · show true ∈ (Part.some (searchPred a (Nat.pair n m).unpair.1 (Nat.pair n m).unpair.2 t₀) :
            Part Bool)
        simp [Nat.unpair_pair, ht0_true]
      · intro m' hm'
        show false ∈ (Part.some
            (searchPred a (Nat.pair n m).unpair.1 (Nat.pair n m).unpair.2 m') : Part Bool)
        have hlt := Nat.find_min hex_t hm'
        simp only [Nat.unpair_pair]
        simp only [Bool.not_eq_true] at hlt
        simp [hlt]
    unfold searchValue
    rw [hstage]
    simp only [Part.bind_eq_bind, Part.bind_some]
    apply Part.eq_some_iff.mpr
    apply Nat.mem_rfind.mpr
    refine ⟨?_, ?_⟩
    · show true ∈ (Part.some (decide (x₀ ∉ r t₀)) : Part Bool)
      simp [hx0def, Nat.find_spec hex_x]
    · intro m' hm'
      show false ∈ (Part.some (decide (m' ∉ r t₀)) : Part Bool)
      have := Nat.find_min hex_x hm'
      simp [this]
  have hmem : x₀ ∈ searchValue a r (Nat.pair n m) := by rw [hsv_eq]; exact Part.mem_some _
  have hKBc : KB x₀ ≤ KB (Nat.pair n m) + c := hc (Nat.pair n m) x₀ hmem
  have hQB : QB x₀ ≤ haltingProb - (a t₀ : ℝ) / 2 ^ t₀ := hr_spec t₀ x₀ (Nat.find_spec hex_x)
  have hQB_lt : QB x₀ < 2 / 2 ^ n := lt_of_le_of_lt hQB hmiss
  have hle : n ≤ KB x₀ := le_KB_of_QB_lt hQB_lt
  omega

/-- **The joint-satisfiability witness**: both hypotheses of the incompressibility statement are
met at every precision `n`, by the floor of `haltingProb · 2 ^ n`; nothing about `haltingProb`
beyond `0 ≤ haltingProb` is used — no positivity, no irrationality. -/
theorem haltingProb_prefix_incompressible_nonvacuous (n : ℕ) :
    ∃ m : ℕ, (m : ℝ) / 2 ^ n ≤ haltingProb ∧ haltingProb - (m : ℝ) / 2 ^ n ≤ 1 / 2 ^ n := by
  refine ⟨⌊haltingProb * 2 ^ n⌋₊, ?_, ?_⟩
  · rw [div_le_iff₀ (by positivity : (0 : ℝ) < 2 ^ n)]
    exact Nat.floor_le (mul_nonneg haltingProb_nonneg (by positivity))
  · have h1 : haltingProb * 2 ^ n < (⌊haltingProb * 2 ^ n⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
    have h2 : haltingProb ≤ ((⌊haltingProb * 2 ^ n⌋₊ : ℝ) + 1) / 2 ^ n := by
      rw [le_div_iff₀ (by positivity : (0 : ℝ) < 2 ^ n)]
      linarith
    have h3 : ((⌊haltingProb * 2 ^ n⌋₊ : ℝ) + 1) / 2 ^ n
        = (⌊haltingProb * 2 ^ n⌋₊ : ℝ) / 2 ^ n + 1 / 2 ^ n := by ring
    linarith [h2, h3]

/-! ## The revealed list: the values seen by stage `t` -/

/-- The values revealed at stage `t`: the output of every description of at most `t` bits that
`acceptedList` admits and `evaln` decides within `t` steps. -/
def revealedList (t : ℕ) : List ℕ :=
  (List.range t).flatMap fun k =>
    (List.range (2 ^ (t + 1) - 1)).filterMap fun n =>
      let c := Denumerable.ofNat Code k
      if elen c + (natToBits n).length ≤ t ∧ n ∈ acceptedList c t then evaln t c n else none

private theorem primrec_revealedTerm :
    Primrec fun p : (ℕ × ℕ) × ℕ =>
      (if elen (Denumerable.ofNat Code p.1.2) + (natToBits p.2).length ≤ p.1.1 ∧
          p.2 ∈ acceptedList (Denumerable.ofNat Code p.1.2) p.1.1
        then evaln p.1.1 (Denumerable.ofNat Code p.1.2) p.2 else none) := by
  have hc : Primrec fun p : (ℕ × ℕ) × ℕ => Denumerable.ofNat Code p.1.2 :=
    (Primrec.ofNat Code).comp (Primrec.snd.comp Primrec.fst)
  have ht : Primrec fun p : (ℕ × ℕ) × ℕ => p.1.1 := Primrec.fst.comp Primrec.fst
  have hn' : Primrec fun p : (ℕ × ℕ) × ℕ => p.2 := Primrec.snd
  have hL : Primrec fun p : (ℕ × ℕ) × ℕ =>
      elen (Denumerable.ofNat Code p.1.2) + (natToBits p.2).length :=
    Primrec.nat_add.comp (primrec_elen.comp hc)
      (Primrec.list_length.comp (primrec_natToBits.comp hn'))
  have hLe : Primrec fun p : (ℕ × ℕ) × ℕ =>
      decide (elen (Denumerable.ofNat Code p.1.2) + (natToBits p.2).length ≤ p.1.1) :=
    Primrec.nat_le.decide.comp hL ht
  have hmem : Primrec fun p : (ℕ × ℕ) × ℕ =>
      decide (p.2 ∈ acceptedList (Denumerable.ofNat Code p.1.2) p.1.1) := by
    have hAccList : Primrec fun p : (ℕ × ℕ) × ℕ =>
        acceptedList (Denumerable.ofNat Code p.1.2) p.1.1 :=
      Primrec.comp primrec₂_acceptedList (hc.pair ht)
    exact (primrec_mem_list.comp hAccList hn').decide
  have hcondBool : Primrec fun p : (ℕ × ℕ) × ℕ =>
      decide (elen (Denumerable.ofNat Code p.1.2) + (natToBits p.2).length ≤ p.1.1) &&
        decide (p.2 ∈ acceptedList (Denumerable.ofNat Code p.1.2) p.1.1) :=
    Primrec.and.comp hLe hmem
  have hev : Primrec fun p : (ℕ × ℕ) × ℕ => evaln p.1.1 (Denumerable.ofNat Code p.1.2) p.2 := by
    have hq : Primrec fun p : (ℕ × ℕ) × ℕ => ((p.1.1, Denumerable.ofNat Code p.1.2), p.2) :=
      (ht.pair hc).pair hn'
    exact Primrec.comp Nat.Partrec.Code.primrec_evaln hq
  have := Primrec.cond hcondBool hev (Primrec.const none)
  refine this.of_eq fun p => ?_
  simp

private theorem primrec_revealedList : Primrec revealedList := by
  have hinner : Primrec₂ fun (t k : ℕ) =>
      (List.range (2 ^ (t + 1) - 1)).filterMap fun n =>
        (if elen (Denumerable.ofNat Code k) + (natToBits n).length ≤ t ∧
            n ∈ acceptedList (Denumerable.ofNat Code k) t
          then evaln t (Denumerable.ofNat Code k) n else none) :=
    Primrec.listFilterMap
      (Primrec.list_range.comp
        (Primrec.nat_sub.comp
          (primrec_pow''.comp (Primrec.const 2) (Primrec.succ.comp Primrec.fst))
          (Primrec.const 1)))
      primrec_revealedTerm
  exact (Primrec.list_flatMap Primrec.list_range hinner).of_eq fun t => rfl

theorem computable_revealedList : Computable revealedList := primrec_revealedList.to_comp

/-- Membership is exactly a positive term: `x ∈ revealedList t` iff some admitted description at
stage `t` contributes a nonzero `QBApproxTerm`. -/
theorem mem_revealedList_iff (t x : ℕ) :
    x ∈ revealedList t ↔ ∃ k ∈ Finset.range t, ∃ n ∈ Finset.range (2 ^ (t + 1) - 1),
      QBApproxTerm t x k n ≠ 0 := by
  simp only [Finset.mem_range]
  unfold revealedList
  rw [List.mem_flatMap]
  constructor
  · rintro ⟨k, hk, hx⟩
    rw [List.mem_filterMap] at hx
    obtain ⟨n, hnr, hev⟩ := hx
    rw [List.mem_range] at hnr
    refine ⟨k, List.mem_range.mp hk, n, hnr, ?_⟩
    unfold QBApproxTerm
    by_cases hcond2 : elen (Denumerable.ofNat Code k) + (natToBits n).length ≤ t ∧
        n ∈ acceptedList (Denumerable.ofNat Code k) t
    · rw [ite_eq_left hcond2] at hev
      rw [ite_eq_left (show elen (Denumerable.ofNat Code k) + (natToBits n).length ≤ t ∧
          n ∈ acceptedList (Denumerable.ofNat Code k) t ∧
          evaln t (Denumerable.ofNat Code k) n = some x from ⟨hcond2.1, hcond2.2, hev⟩)]
      exact pow_ne_zero _ two_ne_zero
    · rw [ite_eq_right hcond2] at hev
      exact absurd hev (by simp)
  · rintro ⟨k, hk, n, hnr, hne⟩
    refine ⟨k, List.mem_range.mpr hk, ?_⟩
    rw [List.mem_filterMap]
    refine ⟨n, List.mem_range.mpr hnr, ?_⟩
    unfold QBApproxTerm at hne
    by_cases hcond3 : elen (Denumerable.ofNat Code k) + (natToBits n).length ≤ t ∧
        n ∈ acceptedList (Denumerable.ofNat Code k) t ∧
        evaln t (Denumerable.ofNat Code k) n = some x
    · rw [ite_eq_left (show elen (Denumerable.ofNat Code k) + (natToBits n).length ≤ t ∧
          n ∈ acceptedList (Denumerable.ofNat Code k) t from ⟨hcond3.1, hcond3.2.1⟩)]
      exact hcond3.2.2
    · rw [ite_eq_right hcond3] at hne
      exact absurd rfl hne

/-- Once revealed, a value stays revealed: `acceptedList`'s and `evaln`'s own monotonicity, through
the widening stage bound on the inner range. -/
theorem revealedList_mono {t t' : ℕ} (h : t ≤ t') {x : ℕ} (hx : x ∈ revealedList t) :
    x ∈ revealedList t' := by
  rw [mem_revealedList_iff] at hx ⊢
  simp only [Finset.mem_range] at hx ⊢
  obtain ⟨k, hk, n, hn, hne⟩ := hx
  have h2 : (2 : ℕ) ^ (t + 1) ≤ 2 ^ (t' + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  refine ⟨k, by omega, n, by omega, ?_⟩
  unfold QBApproxTerm at hne ⊢
  by_cases hcond : elen (Denumerable.ofNat Code k) + (natToBits n).length ≤ t ∧
      n ∈ acceptedList (Denumerable.ofNat Code k) t ∧ evaln t (Denumerable.ofNat Code k) n = some x
  · obtain ⟨hL, hacc, hev⟩ := hcond
    have hL' : elen (Denumerable.ofNat Code k) + (natToBits n).length ≤ t' := by omega
    have hacc' : n ∈ acceptedList (Denumerable.ofNat Code k) t' := acceptedList_mono h hacc
    have hev' : evaln t' (Denumerable.ofNat Code k) n = some x := evaln_mono h hev
    rw [ite_eq_left ⟨hL', hacc', hev'⟩]
    exact pow_ne_zero _ two_ne_zero
  · rw [ite_eq_right hcond] at hne
    exact absurd rfl hne

private theorem QBApprox_eq_zero_of_notMem {t x : ℕ} (h : x ∉ revealedList t) :
    QBApprox t x = 0 := by
  have hall : ∀ k ∈ Finset.range t, ∀ n ∈ Finset.range (2 ^ (t + 1) - 1),
      QBApproxTerm t x k n = 0 := by
    intro k hk n hn
    by_contra hne
    exact h ((mem_revealedList_iff t x).mpr ⟨k, hk, n, hn, hne⟩)
  unfold QBApprox
  exact Finset.sum_eq_zero fun k hk => Finset.sum_eq_zero fun n hn => hall k hk n hn

/-! ## The stage mass: the total revealed weight, deduplicated -/

/-- Accumulate a list's members without duplication: keep `acc` unless `n` is already present. -/
def dedupStep (acc : List ℕ) (n : ℕ) : List ℕ := if n ∈ acc then acc else acc ++ [n]

/-- A duplicate-free copy of `l`, in first-occurrence order. -/
def dedupList (l : List ℕ) : List ℕ := l.foldl dedupStep []

private theorem mem_foldl_dedupStep_iff (l acc : List ℕ) (x : ℕ) :
    x ∈ l.foldl dedupStep acc ↔ x ∈ acc ∨ x ∈ l := by
  induction l generalizing acc with
  | nil => simp
  | cons a l ih =>
      rw [List.foldl_cons, ih, List.mem_cons]
      unfold dedupStep
      split
      · rename_i h
        constructor
        · rintro (h1 | h2)
          · exact Or.inl h1
          · exact Or.inr (Or.inr h2)
        · rintro (h1 | rfl | h2)
          · exact Or.inl h1
          · exact Or.inl h
          · exact Or.inr h2
      · rename_i h
        simp only [List.mem_append, List.mem_singleton]
        tauto

private theorem mem_dedupList_iff (l : List ℕ) (x : ℕ) : x ∈ dedupList l ↔ x ∈ l := by
  unfold dedupList
  rw [mem_foldl_dedupStep_iff]
  simp

private theorem foldl_dedupStep_nodup (l : List ℕ) {acc : List ℕ} (h : acc.Nodup) :
    (l.foldl dedupStep acc).Nodup := by
  induction l generalizing acc with
  | nil => simpa using h
  | cons a l ih =>
      apply ih
      unfold dedupStep
      split
      · exact h
      · rename_i hn
        refine h.append (List.nodup_singleton a) ?_
        intro y hy hya
        exact hn ((List.mem_singleton.mp hya) ▸ hy)

private theorem dedupList_nodup (l : List ℕ) : (dedupList l).Nodup :=
  foldl_dedupStep_nodup l List.nodup_nil

private theorem dedupList_toFinset (l : List ℕ) : (dedupList l).toFinset = l.toFinset :=
  Finset.ext fun x => by simp [mem_dedupList_iff]

private theorem primrec₂_dedupStep : Primrec₂ dedupStep :=
  Primrec.ite primrec_mem_list Primrec.fst Primrec.list_concat

private theorem primrec_dedupList : Primrec dedupList := by
  have hh : Primrec₂ fun (_ : List ℕ) (sb : List ℕ × ℕ) => dedupStep sb.1 sb.2 :=
    Primrec.comp₂ primrec₂_dedupStep Primrec₂.right
  exact (Primrec.list_foldl Primrec.id (Primrec.const ([] : List ℕ)) hh).of_eq fun l => rfl

/-- **The stage mass**: the total weight, over the values revealed at stage `t`, of each one's
`QBApprox` reading — each value counted once. -/
def stageMass (t : ℕ) : ℕ := ((dedupList (revealedList t)).map (QBApprox t)).sum

theorem computable_stageMass : Computable stageMass := by
  have hmap : Primrec fun t : ℕ => (dedupList (revealedList t)).map (QBApprox t) :=
    Primrec.list_map (primrec_dedupList.comp primrec_revealedList) primrec₂_QBApprox
  exact (primrec_list_sum hmap).to_comp

/-- The stage mass, read as the `Finset` sum a specification proof consumes. -/
theorem stageMass_eq_finset_sum (t : ℕ) :
    stageMass t = ∑ x ∈ (revealedList t).toFinset, QBApprox t x := by
  unfold stageMass
  rw [← dedupList_toFinset]
  exact (List.sum_toFinset (QBApprox t) (dedupList_nodup (revealedList t))).symm

private theorem QBApprox_mono' {x : ℕ} : ∀ {t t' : ℕ}, t ≤ t' →
    (QBApprox t x : ℝ) / 2 ^ t ≤ (QBApprox t' x : ℝ) / 2 ^ t' := by
  intro t t' h
  induction t', h using Nat.le_induction with
  | base => exact le_refl _
  | succ n _ ih => exact ih.trans (QBApprox_mono n x)

private theorem stageMass_mono_real (t : ℕ) :
    (stageMass t : ℝ) / 2 ^ t ≤ (stageMass (t + 1) : ℝ) / 2 ^ (t + 1) := by
  rw [stageMass_eq_finset_sum, stageMass_eq_finset_sum]
  push_cast
  rw [sum_div_eq, sum_div_eq]
  have hsub : (revealedList t).toFinset ⊆ (revealedList (t + 1)).toFinset := by
    intro x hx
    rw [List.mem_toFinset] at hx ⊢
    exact revealedList_mono (Nat.le_succ t) hx
  calc ∑ x ∈ (revealedList t).toFinset, (QBApprox t x : ℝ) / 2 ^ t
      ≤ ∑ x ∈ (revealedList t).toFinset, (QBApprox (t + 1) x : ℝ) / 2 ^ (t + 1) :=
        Finset.sum_le_sum fun x _ => QBApprox_mono t x
    _ ≤ ∑ x ∈ (revealedList (t + 1)).toFinset, (QBApprox (t + 1) x : ℝ) / 2 ^ (t + 1) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun x _ _ => by positivity

private theorem stageMass_le_haltingProb (t : ℕ) : (stageMass t : ℝ) / 2 ^ t ≤ haltingProb := by
  rw [stageMass_eq_finset_sum]
  push_cast
  rw [sum_div_eq]
  calc ∑ x ∈ (revealedList t).toFinset, (QBApprox t x : ℝ) / 2 ^ t
      ≤ ∑ x ∈ (revealedList t).toFinset, QB x := Finset.sum_le_sum fun x _ => QBApprox_le t x
    _ ≤ haltingProb := Summable.sum_le_tsum _ (fun x _ => QB_nonneg x) summable_QB'

private theorem stageMass_reaches (q : ℝ) (hq : q < haltingProb) :
    ∃ t, q < (stageMass t : ℝ) / 2 ^ t := by
  have htendsto : Filter.Tendsto (fun N => ∑ x ∈ Finset.range N, QB x) Filter.atTop
      (nhds haltingProb) := summable_QB'.hasSum.tendsto_sum_nat
  obtain ⟨N, hN⟩ := ((tendsto_order.mp htendsto).1 q hq).exists
  rcases Nat.eq_zero_or_pos N with hN0 | hNpos
  · refine ⟨0, ?_⟩
    subst hN0
    simp only [Finset.range_zero, Finset.sum_empty] at hN
    have hge : (0 : ℝ) ≤ (stageMass 0 : ℝ) / 2 ^ 0 := by positivity
    linarith
  · set ε : ℝ := (∑ x ∈ Finset.range N, QB x - q) / N with hεdef
    have hgap_pos : (0 : ℝ) < ∑ x ∈ Finset.range N, QB x - q := by linarith
    have hNpos' : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hNpos
    have hεpos : 0 < ε := div_pos hgap_pos hNpos'
    have hstep : ∀ x : ℕ, ∃ t, QB x - ε < (QBApprox t x : ℝ) / 2 ^ t :=
      fun x => QBApprox_lt x (QB x - ε) (by linarith)
    choose tf htf using hstep
    set t : ℕ := (Finset.range N).sup tf with htdef
    have hqlt : q < ∑ x ∈ Finset.range N, (QBApprox t x : ℝ) / 2 ^ t := by
      have hterm : ∀ x ∈ Finset.range N, QB x - ε < (QBApprox t x : ℝ) / 2 ^ t := by
        intro x hx
        have hle : tf x ≤ t := Finset.le_sup hx
        exact lt_of_lt_of_le (htf x) (QBApprox_mono' hle)
      have hne : (Finset.range N).Nonempty := Finset.nonempty_range_iff.mpr (by omega)
      have hsum_lt : ∑ x ∈ Finset.range N, (QB x - ε) <
          ∑ x ∈ Finset.range N, (QBApprox t x : ℝ) / 2 ^ t :=
        Finset.sum_lt_sum_of_nonempty hne hterm
      have hsum_eq : ∑ x ∈ Finset.range N, (QB x - ε)
          = (∑ x ∈ Finset.range N, QB x) - N * ε := by
        rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range]
        ring
      have hNe : (N : ℝ) * ε = ∑ x ∈ Finset.range N, QB x - q := by rw [hεdef]; field_simp
      linarith [hsum_lt, hsum_eq, hNe]
    have hbound : ∑ x ∈ Finset.range N, (QBApprox t x : ℝ) / 2 ^ t
        ≤ ∑ x ∈ (revealedList t).toFinset, (QBApprox t x : ℝ) / 2 ^ t := by
      set S := Finset.range N ∪ (revealedList t).toFinset with hSdef
      have heq : ∑ x ∈ (revealedList t).toFinset, (QBApprox t x : ℝ) / 2 ^ t
          = ∑ x ∈ S, (QBApprox t x : ℝ) / 2 ^ t := by
        apply Finset.sum_subset Finset.subset_union_right
        intro x _ hxF
        have hxnot : x ∉ revealedList t := fun hmem => hxF (List.mem_toFinset.mpr hmem)
        rw [QBApprox_eq_zero_of_notMem hxnot]
        simp
      rw [heq]
      exact Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left
        fun x _ _ => by positivity
    refine ⟨t, ?_⟩
    rw [stageMass_eq_finset_sum]
    push_cast
    rw [sum_div_eq]
    linarith [hqlt, hbound]

/-- **The stage-mass specification is met**: `stageMass` is computable, monotone, always below
`haltingProb`, and reaches every real under it. -/
theorem stageMass_spec : HaltingMassSpec stageMass :=
  ⟨computable_stageMass, stageMass_mono_real, stageMass_le_haltingProb, stageMass_reaches⟩

/-- **The revealed-list specification is met**: `revealedList` is computable, and a value it has
not yet revealed at stage `t` has its whole algorithmic probability inside the mass still
missing there. -/
theorem revealedList_spec : HaltingRevealedSpec stageMass revealedList := by
  refine ⟨computable_revealedList, ?_⟩
  intro t x hx
  have hxF : x ∉ (revealedList t).toFinset := by rwa [List.mem_toFinset]
  have hstep1 : (stageMass t : ℝ) / 2 ^ t ≤ ∑ y ∈ (revealedList t).toFinset, QB y := by
    rw [stageMass_eq_finset_sum]
    push_cast
    rw [sum_div_eq]
    exact Finset.sum_le_sum fun y _ => QBApprox_le t y
  have hstep2 : QB x + ∑ y ∈ (revealedList t).toFinset, QB y
      = ∑ y ∈ insert x (revealedList t).toFinset, QB y := (Finset.sum_insert hxF).symm
  have hstep3 : ∑ y ∈ insert x (revealedList t).toFinset, QB y ≤ haltingProb :=
    Summable.sum_le_tsum _ (fun y _ => QB_nonneg y) summable_QB'
  linarith [hstep1, hstep2, hstep3]

/-! ## The capstone: unconditional -/

/-- **Chaitin's theorem on the prefix machine's halting probability**, unconditional: any dyadic
lower approximation `m / 2 ^ n` to `haltingProb` within `2 ^ (-n)` of it has, as the pair `(n, m)`,
prefix complexity at least `n − c`. The two hypotheses `haltingProb_prefix_incompressible_of` once
carried are discharged by `stageMass` and `revealedList` (`stageMass_spec`, `revealedList_spec`);
its own two inner hypotheses, at every precision `n`, are witnessed by
`haltingProb_prefix_incompressible_nonvacuous`. Cf. Shen, Uspensky and Vereshchagin, *Kolmogorov
Complexity and Algorithmic Randomness*, §5.7 Theorem 100. -/
theorem haltingProb_prefix_incompressible :
    ∃ c : ℕ, ∀ n m : ℕ,
      (m : ℝ) / 2 ^ n ≤ haltingProb → haltingProb - (m : ℝ) / 2 ^ n ≤ 1 / 2 ^ n →
        n ≤ KB (Nat.pair n m) + c :=
  haltingProb_prefix_incompressible_of stageMass_spec revealedList_spec

/-- info: 'PrefixMachine.haltingProb_le_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms haltingProb_le_one

/-- info: 'PrefixMachine.haltingProb_prefix_incompressible_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms haltingProb_prefix_incompressible_of

/-- info: 'PrefixMachine.haltingProb_prefix_incompressible_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms haltingProb_prefix_incompressible_nonvacuous

/-- info: 'PrefixMachine.stageMass_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms stageMass_spec

/-- info: 'PrefixMachine.revealedList_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms revealedList_spec

/-- info: 'PrefixMachine.haltingProb_prefix_incompressible' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms haltingProb_prefix_incompressible

end PrefixMachine
