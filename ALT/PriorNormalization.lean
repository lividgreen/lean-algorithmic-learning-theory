/-
Copyright (c) 2026 Mykola Palamarchuk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mykola Palamarchuk
-/
import Mathlib

-- Formal-check file, not Mathlib-destined: opt out of the house-style header linter.
set_option linter.style.header false

/-!
# Universal-prior sub-normalization (Paper II, §1.1)

Provenance: Paper II, §1.1 (the prequential-MDL Bayesian mixture
`P̄(o_t | o_{<t}) = Σ_{R' ∈ M} w(R' | o_{<t}) P_{R'}(o_t | o_{<t})` over a countable hypothesis
class `M`, with prior `w(R') ∝ 2^{−K(R')}`). For the proportionality `∝` to define a
(sub-)probability — and hence the mixture to be well-defined — the unnormalized weights must have
finite total mass `≤ 1`. That is the Kraft–McMillan inequality.

Status: PROVED as pure code-length statements, on top of Mathlib's `kraft_mcmillan_inequality`.
This is the *arithmetic core* of §1.1's well-definedness only.

## What this DOES establish
* `uniquelyDecodable_of_subset`: a subset of a uniquely-decodable code is uniquely decodable
  (a one-line bridge absent upstream — Mathlib's `UniquelyDecodable` file has only
  `epsilon_not_mem`/`flatten_injective`).
* `prior_finset_sum_le_one`: the binary (`α = Bool`) specialization of Kraft–McMillan —
  for a finite uniquely-decodable binary code, `∑_{w ∈ S} (1/2)^{|w|} ≤ 1`.
* `prior_tsum_le_one`: the countable extension — for a hypothesis class enumerated without
  repeats by a uniquely-decodable binary code, the unnormalized weights `2^{−ℓ(R)}` sum to
  `≤ 1`, so the §1.1 prior `w(R') ∝ 2^{−K(R')}` normalizes and the Bayesian mixture is
  well-defined.

## What this does NOT establish (stays in prose; no overclaiming)
* No Kolmogorov complexity `K`: `ℓ(R) = (code R).length` is an abstract codeword length; we do
  not formalize `K(R)`, the universal reference machine `U_ref`, or `K(R) = r`.
* Not the Kraft–Chaitin bridge that shortest programs / minimal descriptions form a
  uniquely-decodable (prefix-free) set — i.e. that one may take code-lengths `= K(R)`. That
  bridge stays prose; we ASSUME the class is presented by a uniquely-decodable code (`hUD`).
* Sub-normalization only (`≤ 1`, not `= 1`): the paper writes `∝`, so `≤ 1` is exactly what
  well-definedness needs. We do not claim equality (it generally fails — the prior is normalized
  by dividing by the total mass).

## Hypotheses: paper-stated vs added/strengthened
* Paper-stated / faithful: countable class `M`; binary weights `2^{−ℓ}`; the implicit `≤ 1`
  behind `∝`.
* Added/strengthened (scope choices, flagged): (a) binary alphabet `Bool` (faithful to base 2);
  (b) `hUD` — the unique-decodability the paper leaves implicit in "`2^{−K}`", made an explicit
  named hypothesis (this is what makes Kraft apply); (c) `hinj` — distinct hypotheses map to
  distinct codewords (an injective enumeration of `M`); (d) `≤ 1`, not `= 1`.
-/

namespace PriorNormalization

open InformationTheory

/-- A subset of a uniquely-decodable code is uniquely decodable. The unique-decodability test on
`S` only ever quantifies over codewords that lie in `S ⊆ T`, so it is inherited from `T`.
(Absent upstream; small bridge lemma.) -/
theorem uniquelyDecodable_of_subset {α : Type*} {S T : Set (List α)}
    (hsub : S ⊆ T) (h : UniquelyDecodable T) : UniquelyDecodable S :=
  fun L₁ L₂ h1 h2 hflat =>
    h L₁ L₂ (fun w hw => hsub (h1 w hw)) (fun w hw => hsub (h2 w hw)) hflat

/-- Binary specialization of Kraft–McMillan (Paper II §1.1, finite form): for a finite
uniquely-decodable binary code, the weights `2^{−|w|}` sum to `≤ 1`.
Uses `Fintype.card Bool = 2`. -/
theorem prior_finset_sum_le_one {S : Finset (List Bool)}
    (hUD : UniquelyDecodable (S : Set (List Bool))) :
    ∑ w ∈ S, (1 / 2 : ℝ) ^ w.length ≤ 1 := by
  have h := kraft_mcmillan_inequality hUD
  simpa [Fintype.card_bool] using h

/-- Paper II §1.1: the Kolmogorov-weighted prior is a sub-probability. For a countable hypothesis
class enumerated without repeats by a uniquely-decodable binary code, the unnormalized weights
`2^{−ℓ(R)}` sum to `≤ 1`, so the prior `w(R') ∝ 2^{−K(R')}` normalizes and the §1.1 Bayesian
mixture is well-defined.

The countable bound follows from the finite one by `Real.tsum_le_of_sum_range_le`: every partial
sum reindexes (injectivity of `code`) onto a finite subset of the code, which is uniquely
decodable by `uniquelyDecodable_of_subset`, hence bounded by `1` via `prior_finset_sum_le_one`. -/
theorem prior_tsum_le_one
    (code : ℕ → List Bool)
    (hinj : Function.Injective code)
    (hUD : UniquelyDecodable (Set.range code)) :
    ∑' n, (1 / 2 : ℝ) ^ (code n).length ≤ 1 := by
  apply Real.tsum_le_of_sum_range_le
  · -- terms are nonnegative
    intro n; positivity
  · -- every partial sum is ≤ 1
    intro n
    have hinjOn : Set.InjOn code (Finset.range n) := hinj.injOn
    have hsub : ((Finset.range n).image code : Set (List Bool)) ⊆ Set.range code := by
      intro w hw
      simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_range] at hw
      obtain ⟨i, _, rfl⟩ := hw
      exact ⟨i, rfl⟩
    have hUDS : UniquelyDecodable ((Finset.range n).image code : Set (List Bool)) :=
      uniquelyDecodable_of_subset hsub hUD
    calc ∑ i ∈ Finset.range n, (1 / 2 : ℝ) ^ (code i).length
        = ∑ w ∈ (Finset.range n).image code, (1 / 2 : ℝ) ^ w.length :=
          (Finset.sum_image (f := fun w : List Bool => (1 / 2 : ℝ) ^ w.length) hinjOn).symm
      _ ≤ 1 := prior_finset_sum_le_one hUDS

end PriorNormalization
