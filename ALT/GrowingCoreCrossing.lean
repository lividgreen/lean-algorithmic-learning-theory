/-
Copyright (c) 2026 Mykola Palamarchuk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mykola Palamarchuk
-/
module

public import ALT.AccretingExcess

-- Formal-check file, not Mathlib-destined: opt out of the house-style header linter.
set_option linter.style.header false

/-!
# The generalized crossing: an arbitrary monotone unbounded budget profile
([Guests] §7 Theorem 7.7(vi))

`ALT/AccretingExcess.lean` crosses the internalization threshold at the accreting healer world's own
budget, `t + 1`. Its two theorems, `outgrows_paMinus_uniform` and `eventually_hostsAt`, consume the
budget only through `CategoricalThreshold.hostsAt`, so the same crossing holds for ANY monotone,
unbounded budget profile — this is not a new argument, only pulling the `t + 1` specialization back
out. Extends `AccretingWitness`'s own namespace, matching `AccretingExcess.lean`: nothing here needs
the merge quotient (`GrowingCore.lean`), so it is kept separate to keep that module light.

## Main results

* `eventually_hostsAt_ofBudget` — eventual hosting at an arbitrary monotone unbounded budget
  profile `κ`, generalizing `eventually_hostsAt`'s fixed `t + 1`.
* `eventually_hosts_uniform` — the assembled crossing: one Gödel sentence, fixed with the theory,
  that every stage past an explicit threshold hosts under `κ`.

## Scope

Capacity arithmetic only, exactly as `AccretingExcess.lean`'s own package: identifying a guest's
stage budget with its bit count (so `κ` is genuinely a bit count, not merely a number) is the
interpretive step owed at paper level for any instance this is applied to.
-/


@[expose] public section

namespace AccretingWitness

open ExcessOrder
open RealizabilityCCC RealizabilityRecursor
open PersistenceCapacity Decoupling AdditiveComplexity
open FFL.FirstOrder FFL.FirstOrder.Arithmetic

/-- **Eventual hosting at an arbitrary monotone unbounded budget profile** ([Guests] §7 Theorem
7.7(vi)): generalizes `eventually_hostsAt`'s fixed `t + 1` to any `κ` that is monotone and
unbounded. `hostsAt_mono` is the whole glue — past the first stage whose budget clears the
threshold, every later budget clears it too, by monotonicity of `κ` alone. -/
theorem eventually_hostsAt_ofBudget {κ : ℕ → ℕ} (hmono : Monotone κ)
    (hunb : ∀ N, ∃ t, N ≤ κ t) (g : ℕ) :
    ∃ t₀, ∀ t, t₀ ≤ t → CategoricalThreshold.hostsAt (κ t) g := by
  obtain ⟨t', ht'⟩ := hunb (GodelInternalization.capacity (Nat.clog 2 (g + 1)))
  refine ⟨t', fun t ht => CategoricalThreshold.hostsAt_mono (le_trans ht' (hmono ht)) ?_⟩
  exact CategoricalThreshold.hostsAt_enters g

/-- **The generalized crossing, assembled** ([Guests] §7 Theorem 7.7(vi)): threading an arbitrary
monotone unbounded budget profile `κ` through `outgrows_paMinus_uniform` and
`eventually_hostsAt_ofBudget` — one Gödel size `gTS`, fixed with the theory, that every stage past
an explicit threshold hosts and at which capacity `κ t` delivers a reflective object representing an
underivable `𝗣𝗔⁻` truth. The witness's own crossing (`accreting_outgrows_paMinus`) is the case
`κ = fun t => t + 1`. -/
theorem eventually_hosts_uniform {κ : ℕ → ℕ} (hmono : Monotone κ) (hunb : ∀ N, ∃ t, N ≤ κ t) :
    ∃ gTS, (∃ t₀, ∀ t, t₀ ≤ t → CategoricalThreshold.hostsAt (κ t) gTS) ∧
      ∀ t Mchk, CategoricalThreshold.hostsAt (κ t) gTS → gTS < Mchk → Mchk ≤ gTS ^ 2 →
        ∃ R : ReflectiveAsm gTS, R.depth = Mchk ∧
          CapacityLayer.FitsIn (recursorAsm R.depth) (κ t) ∧
          ∃ M, GodelThreshold.RepresentsUnderivableTruth (Encodable.encode : Sentence ℒₒᵣ → ℕ)
            (fun δ => (𝗣𝗔⁻ : ArithmeticTheory) ⊢ δ) (fun δ => ℕ↓[ℒₒᵣ] ⊧ δ) M := by
  obtain ⟨gTS, hInc⟩ := outgrows_paMinus_uniform
  exact ⟨gTS, eventually_hostsAt_ofBudget hmono hunb gTS, fun t => hInc (κ t)⟩

end AccretingWitness
