/-
Copyright (c) 2026 Mykola Palamarchuk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mykola Palamarchuk
-/
import ALT.BinaryKraft

-- Formal-check file, not Mathlib-destined: opt out of the house-style header linter.
set_option linter.style.header false

/-!
# Universal-prior sub-normalization ([Discovery], §1.1)

Provenance: [Discovery], §1.1 (the prequential-MDL Bayesian mixture
`P̄(o_t | o_{<t}) = Σ_{R' ∈ M} w(R' | o_{<t}) P_{R'}(o_t | o_{<t})` over a countable hypothesis
class `M`, with prior `w(R') ∝ 2^{−K(R')}`). For the proportionality `∝` to define a
(sub-)probability — and hence the mixture to be well-defined — the unnormalized weights must have
finite total mass `≤ 1`. That is the Kraft–McMillan inequality.

Status: PROVED as pure code-length statements, on top of Mathlib's `kraft_mcmillan_inequality`.
This is the *arithmetic core* of §1.1's well-definedness only.

## What this DOES establish
* `prior_tsum_le_one`: for a hypothesis class enumerated without repeats by a uniquely-decodable
  binary code, the unnormalized weights `2^{−ℓ(R)}` sum to `≤ 1`, so the §1.1 prior
  `w(R') ∝ 2^{−K(R')}` normalizes and the Bayesian mixture is well-defined.

The Kraft arithmetic itself — unique decodability passing to subsets, the binary specialization of
Kraft–McMillan, and its reindexing along an injective code — is generic, and lives in
`BinaryKraft`; this module is the [Discovery] §1.1 reading of it.

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

/-- [Discovery] §1.1: the Kolmogorov-weighted prior is a sub-probability. For a countable hypothesis
class enumerated without repeats by a uniquely-decodable binary code, the unnormalized weights
`2^{−ℓ(R)}` sum to `≤ 1`, so the prior `w(R') ∝ 2^{−K(R')}` normalizes and the §1.1 Bayesian
mixture is well-defined.

This is `BinaryKraft.indexed_tsum_le_one` read at the hypothesis class: the enumeration `code` is
the injective code, its codeword lengths are the `ℓ(R)`, and Kraft–McMillan prices them. -/
theorem prior_tsum_le_one
    (code : ℕ → List Bool)
    (hinj : Function.Injective code)
    (hUD : UniquelyDecodable (Set.range code)) :
    ∑' n, (1 / 2 : ℝ) ^ (code n).length ≤ 1 :=
  BinaryKraft.indexed_tsum_le_one code hinj hUD

end PriorNormalization
