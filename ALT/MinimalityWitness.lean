/-
Copyright (c) 2026 Mykola Palamarchuk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mykola Palamarchuk
-/
import ALT.GodelInternalization
import ALT.GodelChecker

/-!
# Minimality witness: the internalization needs no exponential ([Decoupling] §4.6, Prop 4.5)

[Decoupling] Proposition 4.5 (Minimality) isolates the fragment of the representation category
`Rep(S)` that carries the represent-but-cannot-derive phenomenon: the **cartesian–recursor
fragment** `Rep₀(S)` — a terminal object, finite products, and the bounded recursor of §5, with
*no* exponential (function-space) object and no Cartesian closure. The §6 internalization — the
decision morphism `Decide φ = ⋀_{p ≤ M_chk} ¬Prf(φ, p)`, the explicit capacity polynomial
`capacity n = 2n`, and the verdict `Decide(G_{T_S}) = true` — lives entirely in that fragment.

This module upgrades the "no exponential" clause from **observed to machine-enforced**. It imports
*only* the finite-product-plus-bounded-recursor chain the internalization is built on — the
abstract bounded-checker development (`GodelInternalization`, over the bounded recursor
`cyclicParamNNO M_chk`) and the concrete executable `𝗣𝗔⁻` checker (`GodelChecker`) — and it
re-exports the two capstones, `fragment_internalization` and `fragment_decides_godel`, as its
public surface.

The exponential object `expAsm` of the realizability category ([Decoupling] §4.3) and the graded
exponential modality of §4.5 are therefore *absent from this module's import closure*. The
`assert_not_exists` guards below hold the module to that fact: were either the strict or the graded
exponential ever pulled onto the internalization's dependency path, this file would fail to compile.
This complements FV-13 (`RealizabilityRecursor.reflectiveAsm_representsUnderivableTruth`), where the
exponential is present and genuine yet the §6 consequence still flows through the recursor and
imported incompleteness alone: there the exponential is off the critical path; here it is out of the
build.

Status: PROVED — a re-export of the FV-8 internalization capstones over a deliberately
exponential-free import closure (`#print axioms` → standard axioms only; guarded in
`ALT.AxiomAuditFoundation`).
-/

-- "the exponential object `expAsm` … [is] absent from this module's import closure": the strict
-- §4.3 exponential — the closed (function-space) structure of `Rep(S)` Proposition 4.5 excises.
assert_not_exists RealizabilityCCC.expAsm
-- "and the graded exponential modality of §4.5 [is] absent from this module's import closure": the
-- capacity-graded exponential of the §4.5 general-functor conjecture. It is defined over `expAsm`,
-- so excluding the strict exponential already excludes it; asserted explicitly to keep the §4.5
-- boundary self-evident to a reader of this file.
assert_not_exists GradedApplication.gradedExp

namespace MinimalityWitness

/-- **[Decoupling] §6.3 Theorem 6.3 over the cartesian–recursor fragment (§4.6, Prop 4.5; FV-8).**
For a bounded checker with budget `M_chk ≤ g²` whose indexing budget reaches `g`, under imported
incompleteness: the Gödel number is in range (`g ≤ M_chk`), the decision morphism returns
`Decide(G) = true`, and the recursor depth is hosted by the linear capacity `2n`,
`n = ⌈log₂(g+1)⌉`. A re-export of `GodelInternalization.internalization`: the whole statement is
assembled from finite products and the bounded recursor `cyclicParamNNO M_chk`, and the exponential
object is `assert_not_exists`-absent from this module — Proposition 4.5, machine-enforced. -/
alias fragment_internalization := GodelInternalization.internalization

/-- **[Decoupling] §6.3 Theorem 6.3, Level L2b — concrete, real Gödel sentence (FV-8).** For the
finite theory `𝗣𝗔⁻` and any provable axiom list, the actual Gödel sentence `G` (true in `ℕ`,
`𝗣𝗔⁻`-unprovable) is decided as bounded-non-provable by the executable sound checker:
`Prf Ax G p = false` for every proof code `p ≤ M_chk`. A re-export of
`GodelChecker.paMinus_decides_bounded_nonprovability`: like the abstract form it is built from
finite products and the bounded recursor only — no exponential object enters this module's closure
(Proposition 4.5, machine-enforced). Axiom-clean. -/
alias fragment_decides_godel := GodelChecker.paMinus_decides_bounded_nonprovability

end MinimalityWitness
