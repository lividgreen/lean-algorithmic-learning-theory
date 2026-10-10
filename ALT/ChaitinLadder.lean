/-
Copyright (c) 2026 Mykola Palamarchuk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mykola Palamarchuk
-/
module

public import ChaitinIncompleteness.ChaitinIncompleteness
public import ChaitinIncompleteness.SelectorLadder

-- Formal-check file, not Mathlib-destined: opt out of the house-style linters.
set_option linter.style.header false
set_option linter.style.longLine false

/-!
# Chaitin's incompleteness theorem as a rung selector ([Inevitability] §6 Proposition 6.16)

Provenance: instantiates `DeepLadder.RungSelector` (`ChaitinIncompleteness/SelectorLadder.lean`) at base `𝗥₀`, using
`KolmogorovComplexity.chaitin_theorem` (`ChaitinIncompleteness/ChaitinIncompleteness.lean`) as the rung-picking
principle, in the shape of the module's `hiddenSelector` — chosen via `Classical.epsilon`, since
`RungSelector.pick` receives neither `𝗥₀ ⪯ T` nor truth in `ℕ` (those hypotheses arrive only in
`true_pick`/`unprovable_pick`).

## Main results

* `chaitinCode` / `chaitinWitness` / `chaitinPick` — the epsilon-chosen fixed-point program and
  incompressible witness underlying the selector, and the rung sentence they build.
* `chaitinSelector` — the rung selector at base `𝗥₀`: at every theory `T` extending `𝗥₀` and true in
  `ℕ`, `chaitinPick T` is the Chaitin sentence "the bit-length complexity of `chaitinWitness T`
  exceeds `codelen' (chaitinCode T)`" — true in `ℕ` and unprovable in `T`.
* `chaitinLadder` / `chaitinRung`, with `chaitin_rung_true`, `chaitin_rung_unprovable` and
  `chaitin_ladderTheory_lt_succ` — the chain builder's behavior (every rung true and unprovable in
  its predecessor, strict ascent) restated at this selector.
-/


@[expose] public section

namespace DeepLadder

open Nat.Partrec Nat.Partrec.Code
open FFL.FirstOrder FFL.FirstOrder.Arithmetic KolmogorovComplexity

/-- The epsilon-chosen fixed-point code for `T`: bounds every `n` for which `T` proves the Chaitin
sentence at `(s, n)`, whenever such a code exists (`chaitin_theorem`). Well-defined for any `T`
(`Code` is `Inhabited`), independent of `T.Δ₁`/`𝗥₀ ⪯ T`/consistency — those are needed only to prove
the epsilon-defining property holds, in `chaitinCode_spec` below. -/
noncomputable def chaitinCode (T : ArithmeticTheory) : Code :=
  Classical.epsilon (fun c₀ : Code => ∀ s n, T ⊢ chaitinSentence s n → n < codelen' c₀)

/-- The epsilon-chosen incompressible witness at `chaitinCode T`'s own bit-length: some `s` whose
bit-length complexity exceeds it (`K_bitlen_unbounded`, unconditional). -/
noncomputable def chaitinWitness (T : ArithmeticTheory) : ℕ :=
  Classical.epsilon (fun s : ℕ => codelen' (chaitinCode T) < K_bitlen s)

/-- The rung sentence: the Chaitin sentence at the epsilon-chosen witness and fixed-point bound. -/
noncomputable def chaitinPick (T : ArithmeticTheory) (_ : T.Δ₁) : Sentence ℒₒᵣ :=
  chaitinSentence (chaitinWitness T) (codelen' (chaitinCode T))

variable {T : ArithmeticTheory} [T.Δ₁] [𝗥₀ ⪯ T] [FFL.Entailment.Consistent T]

/-- `chaitinCode T` actually bounds every `n` for which `T` proves the Chaitin sentence at `(s, n)`
— the epsilon-defining property, discharged by `chaitin_theorem`. -/
theorem chaitinCode_spec :
    ∀ s n, T ⊢ chaitinSentence s n → n < codelen' (chaitinCode T) :=
  Classical.epsilon_spec (chaitin_theorem T)

omit [T.Δ₁] [𝗥₀ ⪯ T] [FFL.Entailment.Consistent T] in
/-- `chaitinWitness T`'s bit-length complexity actually exceeds `codelen' (chaitinCode T)` — the
epsilon-defining property, unconditional (`K_bitlen_unbounded`). -/
theorem chaitinWitness_spec : codelen' (chaitinCode T) < K_bitlen (chaitinWitness T) :=
  Classical.epsilon_spec (K_bitlen_unbounded (codelen' (chaitinCode T)))

/-- The rung selector at base `𝗥₀`: Chaitin's incompleteness theorem, at the epsilon-chosen
fixed-point code and witness. -/
noncomputable def chaitinSelector : RungSelector (𝗥₀ : ArithmeticTheory) where
  pick := chaitinPick
  true_pick T _ := by
    intro _ _
    change ℕ↓[ℒₒᵣ] ⊧ chaitinSentence (chaitinWitness T) (codelen' (chaitinCode T))
    exact (models_chaitinSentence_iff (chaitinWitness T) (codelen' (chaitinCode T))).mpr
      chaitinWitness_spec
  unprovable_pick T _ := by
    intro _ _
    change T ⊬ chaitinSentence (chaitinWitness T) (codelen' (chaitinCode T))
    intro hprov
    exact absurd (chaitinCode_spec (chaitinWitness T) (codelen' (chaitinCode T)) hprov)
      (_root_.lt_irrefl _)

/-! ## The ladder and its basic behavior, restated at `chaitinSelector` -/

variable (T₀ : ArithmeticTheory) (d₀ : T₀.Δ₁) [(𝗥₀ : ArithmeticTheory) ⪯ T₀]
  [ℕ↓[ℒₒᵣ] ⊧* T₀]

/-- The Chaitin ladder started at `T₀`, at `chaitinSelector`. -/
noncomputable abbrev chaitinLadder (n : ℕ) : ArithmeticTheory :=
  ladderTheory chaitinSelector T₀ d₀ n

/-- The `n`-th rung of the Chaitin ladder: the Chaitin sentence at the epsilon-chosen witness and
fixed-point bound of `chaitinLadder n`. -/
noncomputable abbrev chaitinRung (n : ℕ) : Sentence ℒₒᵣ :=
  rung chaitinSelector T₀ d₀ n

/-- Every rung of the Chaitin ladder is true in `ℕ` ([Inevitability] §6 Proposition 6.16). -/
theorem chaitin_rung_true (n : ℕ) : ℕ↓[ℒₒᵣ] ⊧ chaitinRung T₀ d₀ n :=
  rung_true chaitinSelector T₀ d₀ n

/-- Every rung of the Chaitin ladder is unprovable in the theory that precedes it
([Inevitability] §6 Proposition 6.16). -/
theorem chaitin_rung_unprovable (n : ℕ) : chaitinLadder T₀ d₀ n ⊬ chaitinRung T₀ d₀ n :=
  rung_unprovable chaitinSelector T₀ d₀ n

/-- The Chaitin ladder ascends strictly ([Inevitability] §6 Proposition 6.16). -/
theorem chaitin_ladderTheory_lt_succ (n : ℕ) :
    chaitinLadder T₀ d₀ n ⪱ chaitinLadder T₀ d₀ (n + 1) :=
  ladderTheory_lt_succ chaitinSelector T₀ d₀ n

end DeepLadder
