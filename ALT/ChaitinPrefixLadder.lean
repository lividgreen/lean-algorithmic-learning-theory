/-
Copyright (c) 2026 Mykola Palamarchuk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mykola Palamarchuk
-/
module

public import ALT.ChaitinLadder
public import ALT.KBEnumerable

-- Formal-check file, not Mathlib-destined: opt out of the house-style linters.
set_option linter.style.header false
set_option linter.style.longLine false

/-!
# The prefix-Chaitin ladder: prefix complexity strictly increases at every rung
([Inevitability] §6 Proposition 6.16(vi), [Decoupling] §6.6 Theorem 6.7)

Provenance: [Inevitability] §6 Proposition 6.16(vi) and [Decoupling] §6.6 Theorem 6.7. A fourth
rung selector at base `𝗥₀`, placing the Chaitin sentence at each theory's own additive threshold
`elen c₀ + KB ⌜e_T⌝` (the FIXED Berry code `c₀` chosen once, outside every theory, plus that
theory's own enumerator's prefix complexity) rather than at a fresh per-theory bound: along its
ladder, the chosen enumerator's prefix complexity strictly increases from rung to rung, hence at
least the base's plus the rung index.

## Main results

* `enumeratorB`, `prefixChaitinCode`, `prefixThreshold`, `prefixChaitinWitness`,
  `prefixChaitinPick`, `prefixChaitinSelector` — the selector, built so that the Berry code is
  chosen ONCE, before any theory, and so contributes the same constant to every theory's
  threshold.
* `prefixChaitinLadder`, `prefixChaitinRung` — the ladder built from this selector.
* `KB_enumeratorB_lt_succ`, `KB_enumeratorB_ge` — the chosen enumerator's prefix complexity
  strictly increases at every rung, hence grows at least linearly in the rung index.
* `prefixChaitinLadder_not_uniform_of` — given `KB`'s invariance under a computable map and an
  Elias bound on `KB`, no computable family of codes enumerates, uniformly in the rung index, the
  theorems of this form provable in the ladder's theories.

## What this does NOT establish (flagged)

* The parent theorem's two hypotheses — `KB`'s invariance under computable maps and an Elias
  bound on `KB` — are proved nowhere in this file; each is a leaf proposition proved elsewhere.
* A non-vacuity witness for the parent theorem is owed once both leaves are in the tree; only
  `KB_enumeratorB_lt_succ`'s own non-vacuity, unconditional, is shown here.
-/


@[expose] public section

namespace DeepLadder

open Nat.Partrec Nat.Partrec.Code
open FFL.FirstOrder FFL.FirstOrder.Arithmetic KolmogorovComplexity AdditiveComplexity PrefixMachine

/-! ## `KB` is unbounded -/

/-- `KB` is unbounded: incompressible numbers of every prefix complexity exist — the twin of
`KolmogorovComplexity.K_unbounded` at `KB` in place of `K`. -/
theorem KB_unbounded (m : ℕ) : ∃ s, m < KB s := by
  by_contra h
  have hall : ∀ s, KB s ≤ m := fun s => by
    by_contra hs; exact h ⟨s, not_le.mp hs⟩
  exact Set.infinite_univ ((setOf_KB_le_finite m).subset (fun s _ => hall s))

/-! ## The selector's ingredients -/

/-- An enumerator of `T`'s provable sentences of this form, epsilon-chosen from
`exists_enumerator_chaitinB`. `T`'s `Δ₁` data is taken EXPLICITLY (mirroring `ladderDelta1`
rather than `chaitin_theoremB`'s own `[T.Δ₁]`), since below `T` ranges over ladder-derived
theories with no registered global instance. -/
noncomputable def enumeratorB (T : ArithmeticTheory) (_dT : T.Δ₁) : Code :=
  Classical.epsilon (fun e : Code =>
    ∀ a, (e.eval a).Dom ↔ T ⊢ chaitinSentenceB (Nat.unpair a).1 (Nat.unpair a).2)

theorem enumeratorB_spec (T : ArithmeticTheory) (dT : T.Δ₁) :
    ∀ a, ((enumeratorB T dT).eval a).Dom ↔
      T ⊢ chaitinSentenceB (Nat.unpair a).1 (Nat.unpair a).2 :=
  Classical.epsilon_spec (exists_enumerator_chaitinB T)

/-- The Berry code underlying `chaitin_theoremB`, epsilon-chosen ONCE, outside every theory — the
whole point being that no theory argument enters here, so the constant it contributes below is
the same for every theory. -/
noncomputable def prefixChaitinCode : Code :=
  Classical.epsilon (fun c₀ : Code => ∀ (T : ArithmeticTheory) [T.Δ₁] [𝗥₀ ⪯ T]
    [FFL.Entailment.Consistent T] (e : Code),
    (∀ a, (e.eval a).Dom ↔ T ⊢ chaitinSentenceB (Nat.unpair a).1 (Nat.unpair a).2) →
    ∀ s n, T ⊢ chaitinSentenceB s n → n < elen c₀ + KB (Encodable.encode e))

theorem prefixChaitinCode_spec : ∀ (T : ArithmeticTheory) [T.Δ₁] [𝗥₀ ⪯ T]
    [FFL.Entailment.Consistent T] (e : Code),
    (∀ a, (e.eval a).Dom ↔ T ⊢ chaitinSentenceB (Nat.unpair a).1 (Nat.unpair a).2) →
    ∀ s n, T ⊢ chaitinSentenceB s n → n < elen prefixChaitinCode + KB (Encodable.encode e) :=
  Classical.epsilon_spec chaitin_theoremB

/-- `T`'s own additive threshold: the fixed Berry code's length plus `T`'s own enumerator's
prefix complexity. -/
noncomputable def prefixThreshold (T : ArithmeticTheory) (dT : T.Δ₁) : ℕ :=
  elen prefixChaitinCode + KB (Encodable.encode (enumeratorB T dT))

/-- A witness whose prefix complexity exceeds `T`'s own threshold, epsilon-chosen from
`KB_unbounded`. -/
noncomputable def prefixChaitinWitness (T : ArithmeticTheory) (dT : T.Δ₁) : ℕ :=
  Classical.epsilon (fun s => prefixThreshold T dT < KB s)

theorem prefixChaitinWitness_spec (T : ArithmeticTheory) (dT : T.Δ₁) :
    prefixThreshold T dT < KB (prefixChaitinWitness T dT) :=
  Classical.epsilon_spec (KB_unbounded (prefixThreshold T dT))

/-- The rung sentence: the Chaitin sentence on `KB`, at `T`'s own additive threshold and an
incompressible-enough witness. -/
noncomputable def prefixChaitinPick (T : ArithmeticTheory) (d : T.Δ₁) : Sentence ℒₒᵣ :=
  chaitinSentenceB (prefixChaitinWitness T d) (prefixThreshold T d)

/-- The rung selector at base `𝗥₀`: Chaitin's additive-form theorem on `KB`, at each theory's own
threshold — unprovability follows because the threshold itself is exactly the bound
`prefixChaitinCode_spec` gives, so a proof would force the threshold below itself. -/
noncomputable def prefixChaitinSelector : RungSelector (𝗥₀ : ArithmeticTheory) where
  pick := prefixChaitinPick
  true_pick T d := by
    intro _ _
    change ℕ↓[ℒₒᵣ] ⊧ chaitinSentenceB (prefixChaitinWitness T d) (prefixThreshold T d)
    exact (models_chaitinSentenceB_iff rePred_kleB _ _).mpr (prefixChaitinWitness_spec T d)
  unprovable_pick T d := by
    intro _ _
    change T ⊬ chaitinSentenceB (prefixChaitinWitness T d) (prefixThreshold T d)
    intro hprov
    have hbound := prefixChaitinCode_spec T (enumeratorB T d) (enumeratorB_spec T d)
      (prefixChaitinWitness T d) (prefixThreshold T d) hprov
    unfold prefixThreshold at hbound
    omega

/-! ## The ladder built from the selector -/

variable (T₀ : ArithmeticTheory) (d₀ : T₀.Δ₁) [(𝗥₀ : ArithmeticTheory) ⪯ T₀]
  [ℕ↓[ℒₒᵣ] ⊧* T₀]

/-- The prefix-Chaitin ladder started at `T₀`, at `prefixChaitinSelector`. -/
noncomputable abbrev prefixChaitinLadder (n : ℕ) : ArithmeticTheory :=
  ladderTheory prefixChaitinSelector T₀ d₀ n

/-- The `n`-th rung of the prefix-Chaitin ladder. -/
noncomputable abbrev prefixChaitinRung (n : ℕ) : Sentence ℒₒᵣ :=
  rung prefixChaitinSelector T₀ d₀ n

/-- The `Δ₁`-definability data of stage `n`'s theory, read off `ladderDelta1` at the selector —
named so the statements below can read `prefixEnumAt` rather than repeating this projection. -/
@[reducible] noncomputable def prefixChaitinDelta1 (n : ℕ) : (prefixChaitinLadder T₀ d₀ n).Δ₁ :=
  ladderDelta1 prefixChaitinSelector T₀ d₀ n

/-- The chosen enumerator of the ladder's stage `n`: `enumeratorB` at stage `n`'s own `Δ₁` data. -/
noncomputable def prefixEnumAt (n : ℕ) : Code :=
  enumeratorB (prefixChaitinLadder T₀ d₀ n) (prefixChaitinDelta1 T₀ d₀ n)

/-! ## The rate: strict increase at every rung -/

/-- **The rate, one rung at a time**: ANY enumerator of stage `n + 1` has strictly greater prefix
complexity than stage `n`'s chosen enumerator — the fixed Berry code cancels between the two
applications of `prefixChaitinCode_spec`, since the rung is placed exactly at stage `n`'s own
threshold. -/
theorem KB_enumerator_succ_gt (n : ℕ) (e' : Code)
    (he' : ∀ a, (e'.eval a).Dom ↔
      prefixChaitinLadder T₀ d₀ (n + 1) ⊢ chaitinSentenceB (Nat.unpair a).1 (Nat.unpair a).2) :
    KB (Encodable.encode (prefixEnumAt T₀ d₀ n)) < KB (Encodable.encode e') := by
  have := prefixChaitinDelta1 T₀ d₀ (n + 1)
  have := base_le_ladderTheory prefixChaitinSelector T₀ d₀ (n + 1)
  have := models_ladderTheory prefixChaitinSelector T₀ d₀ (n + 1)
  have hprov : prefixChaitinLadder T₀ d₀ (n + 1) ⊢
      chaitinSentenceB (prefixChaitinWitness (prefixChaitinLadder T₀ d₀ n)
          (prefixChaitinDelta1 T₀ d₀ n))
        (prefixThreshold (prefixChaitinLadder T₀ d₀ n) (prefixChaitinDelta1 T₀ d₀ n)) :=
    FFL.Entailment.Axiomatized.by_axm (rung_mem_succ prefixChaitinSelector T₀ d₀ n)
  have hbound := prefixChaitinCode_spec (prefixChaitinLadder T₀ d₀ (n + 1)) e' he'
    (prefixChaitinWitness (prefixChaitinLadder T₀ d₀ n) (prefixChaitinDelta1 T₀ d₀ n))
    (prefixThreshold (prefixChaitinLadder T₀ d₀ n) (prefixChaitinDelta1 T₀ d₀ n)) hprov
  unfold prefixThreshold at hbound
  unfold prefixEnumAt
  omega

/-- **The chosen enumerator's own prefix complexity strictly increases at every rung**:
`KB_enumerator_succ_gt` at the next stage's OWN chosen enumerator. -/
theorem KB_enumeratorB_lt_succ (n : ℕ) :
    KB (Encodable.encode (prefixEnumAt T₀ d₀ n)) <
      KB (Encodable.encode (prefixEnumAt T₀ d₀ (n + 1))) := by
  unfold prefixEnumAt
  exact KB_enumerator_succ_gt T₀ d₀ n (enumeratorB (prefixChaitinLadder T₀ d₀ (n + 1))
      (prefixChaitinDelta1 T₀ d₀ (n + 1)))
    (enumeratorB_spec (prefixChaitinLadder T₀ d₀ (n + 1)) (prefixChaitinDelta1 T₀ d₀ (n + 1)))

/-- **At least one bit of theory per rung**: the chosen enumerator's prefix complexity at stage
`n` is at least the base's plus `n`. -/
theorem KB_enumeratorB_ge (n : ℕ) :
    KB (Encodable.encode (prefixEnumAt T₀ d₀ 0)) + n ≤
      KB (Encodable.encode (prefixEnumAt T₀ d₀ n)) := by
  induction n with
  | zero => omega
  | succ n ih =>
    have hlt := KB_enumeratorB_lt_succ T₀ d₀ n
    omega

/-- `KB_enumeratorB_lt_succ`'s hypotheses are jointly met, unconditionally, at `𝗣𝗔⁻`. -/
theorem KB_enumeratorB_lt_succ_nonvacuous (n : ℕ) :
    KB (Encodable.encode (prefixEnumAt (𝗣𝗔⁻ : ArithmeticTheory) inferInstance n)) <
      KB (Encodable.encode (prefixEnumAt (𝗣𝗔⁻ : ArithmeticTheory) inferInstance (n + 1))) :=
  KB_enumeratorB_lt_succ (𝗣𝗔⁻ : ArithmeticTheory) inferInstance n

/-! ## No uniform computable naming -/

private theorem four_mul_add_lt_two_pow (c : ℕ) : 4 * c + 17 < 2 ^ (c + 5) := by
  induction c with
  | zero => decide
  | succ c ih =>
    have hstep : 2 ^ (c + 1 + 5) = 2 * 2 ^ (c + 5) := by
      rw [show c + 1 + 5 = (c + 5) + 1 from by omega, pow_succ, mul_comm]
    omega

/-- **No computable family of codes enumerates the ladder's theories of this form uniformly in
the rung index.** Given `KB`'s invariance under a computable map (`hinv`) and an Elias bound on
`KB` (`helias`): such a family would, through the composed code's length, bound the chosen
enumerator's prefix complexity by `2 * Nat.size (n + 1) + c` at every rung `n`, against the
linear floor `KB_enumeratorB_ge` forces — refuted from `n = 4 * (c₁ + c₂) + 16` on. -/
theorem prefixChaitinLadder_not_uniform_of
    (hinv : ∀ f : ℕ → ℕ, Computable f → ∃ c, ∀ x, KB (f x) ≤ KB x + c)
    (helias : ∃ c, ∀ n, KB n ≤ 2 * Nat.size n + c) :
    ¬ ∃ f : ℕ → Code, Computable f ∧ ∀ n a, ((f n).eval a).Dom ↔
      prefixChaitinLadder T₀ d₀ n ⊢ chaitinSentenceB (Nat.unpair a).1 (Nat.unpair a).2 := by
  rintro ⟨f, hf, hf_spec⟩
  obtain ⟨c₁, hc₁⟩ := hinv (fun n => Encodable.encode (f n)) (Computable.encode.comp hf)
  obtain ⟨c₂, hc₂⟩ := helias
  have hgen : ∀ n, n < 2 * Nat.size (n + 1) + (c₁ + c₂) := by
    intro n
    have h1 := KB_enumeratorB_ge T₀ d₀ n
    have h2 := KB_enumerator_succ_gt T₀ d₀ n (f (n + 1)) (hf_spec (n + 1))
    have h3 : KB (Encodable.encode (f (n + 1))) ≤ KB (n + 1) + c₁ := hc₁ (n + 1)
    have h4 : KB (n + 1) ≤ 2 * Nat.size (n + 1) + c₂ := hc₂ (n + 1)
    omega
  have hpow := four_mul_add_lt_two_pow (c₁ + c₂)
  have hsize : Nat.size (4 * (c₁ + c₂) + 17) ≤ (c₁ + c₂) + 5 := Nat.size_le.mpr hpow
  have hn := hgen (4 * (c₁ + c₂) + 16)
  have heq : 4 * (c₁ + c₂) + 16 + 1 = 4 * (c₁ + c₂) + 17 := by ring
  rw [heq] at hn
  omega

end DeepLadder
