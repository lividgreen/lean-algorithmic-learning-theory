/-
Copyright (c) 2026 Mykola Palamarchuk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mykola Palamarchuk
-/
import ALT.Decoupling
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic

-- Formal-check file, not Mathlib-destined: opt out of the house-style linters.
set_option linter.style.header false
set_option linter.style.longLine false

/-!
# Retention upper bound — [Discovery] §4, Proposition 4.2 (the architectural side)

Provenance: [Discovery] §4.1–§4.4. Cheng's Theorem 4 (the *necessity* /
lower-bound side: context capacity is needed to avoid catastrophic forgetting) is machine-checked in
`ALT/ChengCCC.lean`. Its lower bound is **vacuous** once `C_ctx ≥ H(T)`
(`ChengCCC.cccLower_vacuous`), so it cannot supply the *upper* bound — that the discovered rule
actually persists. That upper bound is an **architectural** fact about [Discovery]'s
conditional-regeneration design, previously stated only in prose; we machine-check it here by reusing
[Decoupling]'s Decoupling Lemma (`ALT/Decoupling.lean`, FV-7).

## The architecture (§4.1), as the named modelling premise
In conditional regeneration the work memory `s_work` is **recomputed from `s_code` each step**, rather
than updated in place. Hence the update `U` is **read-only on the code region** `R = s_code`:
`Decoupling.Fixes U R`. The discovered rule lives in `s_code` and is read off by a faithful decoder,
`Decoupling.Faithful decode R`. These two are the modelling inputs (the architectural invariant + a
real code), exactly as in Decoupling.

## What is PROVED vs. ASSUMED
* PROVED (reusing Decoupling, no new persistence proof): from the architectural invariant `Fixes U R`
  and a faithful decoder, the decoded rule is **unchanged across the entire operational lifetime**
  (`retention_persists`), so forgetting **never happens** (`retention_upper_bound`) and the expected
  forgetting is exactly `0` (`expected_forgetting_zero`).
* ASSUMED (the modelling inputs): `Fixes U R` (the conditional-regeneration invariant — `U` does not
  overwrite `s_code`) and `Faithful decode R` (the rule is genuinely encoded in `s_code`). These are
  architectural premises, not consequences of Cheng's Theorem 4.

The point of §4.4: retention's upper bound (zero forgetting) is purchased by the **architecture**
(`Fixes`), independently of the context-capacity lower bound; Cheng's `Fgt̄ ≥ …` is silent here.
-/

namespace RetentionUpperBound

open Decoupling

variable {ι V M : Type*}

/-- **Retention (persistence of the discovered rule).** Under the conditional-regeneration invariant
`Fixes U R` (the update never overwrites the code region `R = s_code`) and a faithful decoder
`Faithful decode R`, the decoded rule is unchanged across *all* `k` operational steps from *every*
initial state — zero drift over the entire lifetime. This is the `(⇒)` direction of [Decoupling]'s
`Decoupling.decoupling_iff_persists_all`, reused verbatim. -/
theorem retention_persists {U : Mem ι V → Mem ι V} {R : Set ι} {decode : Mem ι V → M}
    (hU : Fixes U R) (hf : Faithful decode R) :
    ∀ k s, decode (U^[k] s) = decode s :=
  (decoupling_iff_persists_all hf).mp hU

/-- The discovered rule is "forgotten" from initial state `s` if *some* number of update steps
changes the decoded model. -/
def Forgotten (U : Mem ι V → Mem ι V) (decode : Mem ι V → M) (s : Mem ι V) : Prop :=
  ∃ k, decode (U^[k] s) ≠ decode s

/-- **Retention upper bound (zero forgetting).** Under the architectural invariant, the rule is
*never* forgotten, from any initial state: the forgetting event is empty. This is the §4.4 upper
bound — it comes from `Fixes` (the architecture), not from Cheng's Theorem 4. -/
theorem retention_upper_bound {U : Mem ι V → Mem ι V} {R : Set ι} {decode : Mem ι V → M}
    (hU : Fixes U R) (hf : Faithful decode R) (s : Mem ι V) :
    ¬ Forgotten U decode s := by
  rintro ⟨k, hk⟩
  exact hk (retention_persists hU hf k s)

/-- **Expected forgetting `Fgt̄ = 0`.** Quantitatively: for any finite sample of `(step, initial
state)` pairs with any weights `μ`, the weighted forgetting indicator
`1[decode (U^[k] s) ≠ decode s]` sums to `0`. This is the architectural upper bound in the same units
as Cheng's `Fgt̄`: zero, purchased by `Fixes`, independent of the (vacuous-here) capacity lower bound
`ChengCCC.cccLower_vacuous`. -/
theorem expected_forgetting_zero [DecidableEq M] {U : Mem ι V → Mem ι V} {R : Set ι}
    {decode : Mem ι V → M} (hU : Fixes U R) (hf : Faithful decode R)
    {Ω : Type*} [Fintype Ω] (μ : Ω → ℝ) (step : Ω → ℕ) (init : Ω → Mem ι V) :
    (∑ ω, μ ω * (if decode (U^[step ω] (init ω)) = decode (init ω) then 0 else 1)) = 0 := by
  refine Finset.sum_eq_zero (fun ω _ => ?_)
  rw [if_pos (retention_persists hU hf (step ω) (init ω)), mul_zero]

end RetentionUpperBound
