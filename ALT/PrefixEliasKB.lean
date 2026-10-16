module

public import AIT.EliasBound
public import ALT.ChaitinPrefixLadder
public import AIT.PrefixInvarianceKB


/-!
# The prefix-Chaitin ladder's non-uniformity ([Discovery] §1.1, [Inevitability] §6)

Provenance: [Inevitability] §6 Remark 6.19 consumes `KB`'s Elias bound
(`AIT/EliasBound.lean`) as
one of two premises of `prefixChaitinLadder_not_uniform_of`
(`ALT/ChaitinPrefixLadder.lean`); this module puts the two together.

## What this establishes

* `prefixChaitinLadder_not_uniform`, `..._nonvacuous`: the ladder's non-uniformity
  theorem, put together from `PrefixMachine.KB_map_le` and `PrefixMachine.KB_le_two_mul_size`, and
  its non-vacuity witness at `𝗣𝗔⁻`.
-/


@[expose] public section

namespace ALT

open Nat.Partrec Nat.Partrec.Code KolmogorovComplexity AdditiveComplexity PrefixMachine
open FFL.FirstOrder FFL.FirstOrder.Arithmetic

/-! ## Assembling the ladder's non-uniformity theorem -/

/-- **No computable family of codes enumerates the ladder's theories of this form uniformly in
the rung index** — the assembly of `prefixChaitinLadder_not_uniform_of` at its two
premises, `PrefixMachine.KB_map_le` (`AIT/PrefixInvarianceKB.lean`) and
`PrefixMachine.KB_le_two_mul_size` (`AIT/EliasBound.lean`). -/
theorem prefixChaitinLadder_not_uniform (T₀ : ArithmeticTheory) (d₀ : T₀.Δ₁)
    [(𝗥₀ : ArithmeticTheory) ⪯ T₀] [ℕ↓[ℒₒᵣ] ⊧* T₀] :
    ¬ ∃ f : ℕ → Code, Computable f ∧ ∀ n a, ((f n).eval a).Dom ↔
      prefixChaitinLadder T₀ d₀ n ⊢ chaitinSentenceB (Nat.unpair a).1 (Nat.unpair a).2 :=
  prefixChaitinLadder_not_uniform_of T₀ d₀ KB_map_le KB_le_two_mul_size

/-- `prefixChaitinLadder_not_uniform`'s hypotheses are jointly met, unconditionally, at `𝗣𝗔⁻`
(mirroring `KB_enumeratorB_lt_succ_nonvacuous`). -/
theorem prefixChaitinLadder_not_uniform_nonvacuous :
    ¬ ∃ f : ℕ → Code, Computable f ∧ ∀ n a, ((f n).eval a).Dom ↔
      prefixChaitinLadder (𝗣𝗔⁻ : ArithmeticTheory) inferInstance n ⊢
        chaitinSentenceB (Nat.unpair a).1 (Nat.unpair a).2 :=
  prefixChaitinLadder_not_uniform (𝗣𝗔⁻ : ArithmeticTheory) inferInstance

end ALT
