/-
Copyright (c) 2026 Mykola Palamarchuk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mykola Palamarchuk
-/
import Mathlib.InformationTheory.Coding.KraftMcMillan
import Mathlib.Topology.Algebra.InfiniteSum.Real

-- Formal-check file, not Mathlib-destined: opt out of the house-style header linter.
set_option linter.style.header false

/-!
# Binary Kraft–McMillan bridges

Mathlib proves Kraft–McMillan (`InformationTheory.kraft_mcmillan_inequality`) for a finite
uniquely-decodable code over a finite alphabet, as a statement about `Fintype.card α` raised to
minus the codeword lengths.  Every use of it in this development wants one of two things instead:
the *binary* form `∑ (1/2)^|w| ≤ 1`, and the sum taken over an *index type* — a hypothesis class,
a type of programs — rather than over the codewords themselves.  This module is that adapter, and
it is deliberately a leaf: it imports only Mathlib, so both the universal-prior side ([Discovery]
§1.1) and the program-length side (the additive complexity `KE`) can use it without either
importing the other for a generic list lemma.

## Contents

* `uniquelyDecodable_of_subset` — unique decodability passes to subsets (absent upstream: the
  `UniquelyDecodable` file has only `epsilon_not_mem` / `flatten_injective`).
* `finset_sum_le_one` — the binary (`α = Bool`) specialization of Kraft–McMillan, over a finite
  set of codewords.
* `indexed_finset_sum_le_one` — the same bound with the sum reindexed along an injective code
  `code : ι → List Bool`, over any finite set of indices.  Injectivity is what lets the sum move
  from codewords to indices; unique decodability of the *whole* range is what lets an arbitrary
  finite subset inherit Kraft (via `uniquelyDecodable_of_subset`).
* `indexed_tsum_le_one` — the countable extension: every finite subtotal is `≤ 1` and the summands
  are nonnegative, so the sum over all of `ι` is `≤ 1`.  This is the form both callers want — a
  sub-probability over an index type.

## Scope

These are *code-length* statements throughout.  Nothing here claims that shortest programs, or
minimal descriptions, form a uniquely-decodable set — that a code exists with lengths `= K(·)` is
a separate fact, supplied by the caller (a concrete serialization proved uniquely decodable, or an
explicit hypothesis).  The bound is `≤ 1`, not `= 1`: a uniquely-decodable code need not be
complete, and sub-normalization is what the `∝ 2^{−K}` prior of [Discovery] §1.1 needs.
-/

namespace BinaryKraft

open InformationTheory

/-- A subset of a uniquely-decodable code is uniquely decodable.  The unique-decodability test on
`S` only ever quantifies over codewords that lie in `S ⊆ T`, so it is inherited from `T`. -/
theorem uniquelyDecodable_of_subset {α : Type*} {S T : Set (List α)}
    (hsub : S ⊆ T) (h : UniquelyDecodable T) : UniquelyDecodable S :=
  fun L₁ L₂ h1 h2 hflat =>
    h L₁ L₂ (fun w hw => hsub (h1 w hw)) (fun w hw => hsub (h2 w hw)) hflat

/-- **Binary Kraft–McMillan**: for a finite uniquely-decodable binary code, the weights `2^{−|w|}`
sum to `≤ 1`.  Mathlib's inequality specialized at `Fintype.card Bool = 2`. -/
theorem finset_sum_le_one {S : Finset (List Bool)}
    (hUD : UniquelyDecodable (S : Set (List Bool))) :
    ∑ w ∈ S, (1 / 2 : ℝ) ^ w.length ≤ 1 := by
  have h := kraft_mcmillan_inequality hUD
  simpa [Fintype.card_bool] using h

/-- **Binary Kraft–McMillan, reindexed along an injective code.**  For `code : ι → List Bool`
injective with uniquely-decodable range, any finite set of indices carries total weight `≤ 1`.

The finite image is uniquely decodable because the whole range is (`uniquelyDecodable_of_subset`),
and injectivity of `code` transports the sum from the codewords back to the indices. -/
theorem indexed_finset_sum_le_one {ι : Type*} (code : ι → List Bool)
    (hinj : Function.Injective code) (hUD : UniquelyDecodable (Set.range code))
    (F : Finset ι) :
    ∑ i ∈ F, (1 / 2 : ℝ) ^ (code i).length ≤ 1 := by
  classical
  have hsub : ((F.image code : Finset (List Bool)) : Set (List Bool)) ⊆ Set.range code := by
    intro w hw
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hw
    obtain ⟨i, _, rfl⟩ := hw
    exact Set.mem_range_self i
  have h := finset_sum_le_one (uniquelyDecodable_of_subset hsub hUD)
  rwa [Finset.sum_image (fun a _ b _ hab => hinj hab)] at h

/-- **Binary Kraft–McMillan over the whole index type.**  For an injective code with
uniquely-decodable range, `∑' i, 2^{−|code i|} ≤ 1`: the weights `2^{−|code i|}` are a
sub-probability on `ι`.

Every finite subtotal is at most one (`indexed_finset_sum_le_one`) and the summands are
nonnegative, so the sum over all of `ι` is too — no summability hypothesis is needed, since a
nonnegative family with bounded finite subtotals is summable. -/
theorem indexed_tsum_le_one {ι : Type*} (code : ι → List Bool)
    (hinj : Function.Injective code) (hUD : UniquelyDecodable (Set.range code)) :
    ∑' i, (1 / 2 : ℝ) ^ (code i).length ≤ 1 :=
  Real.tsum_le_of_sum_le (fun _ => by positivity) (indexed_finset_sum_le_one code hinj hUD)

/-- The weights of a uniquely-decodable code are summable: nonnegative, with every finite subtotal
bounded by `1` (`indexed_finset_sum_le_one`). -/
theorem indexed_summable {ι : Type*} (code : ι → List Bool)
    (hinj : Function.Injective code) (hUD : UniquelyDecodable (Set.range code)) :
    Summable fun i => (1 / 2 : ℝ) ^ (code i).length :=
  summable_of_sum_le (fun _ => by positivity) (indexed_finset_sum_le_one code hinj hUD)

/-- The total mass of the code's weights is *positive*: every weight is, and the family is summable.
Together with `indexed_tsum_le_one` this says the normalizer of a `2^{−ℓ}` prior lies in `(0, 1]` —
the two facts a normalization step needs. -/
theorem indexed_tsum_pos {ι : Type*} (code : ι → List Bool)
    (hinj : Function.Injective code) (hUD : UniquelyDecodable (Set.range code)) (i₀ : ι) :
    0 < ∑' i, (1 / 2 : ℝ) ^ (code i).length :=
  (indexed_summable code hinj hUD).tsum_pos (fun _ => by positivity) i₀ (by positivity)

end BinaryKraft
