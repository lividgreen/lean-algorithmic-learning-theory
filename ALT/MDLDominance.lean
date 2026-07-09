import Mathlib
import ALT.CapacityThreshold

-- Tier-1 formal check, not Mathlib-destined: opt out of the house-style header linter.
set_option linter.style.header false

/-!
# Static MDL dominance (Paper II, Theorem 2.1 / Sub-problem A)

Provenance: `02_mdl_dominance_and_discovery.md`, §1.2 (regime constants C1–C3), §2.1 (the
theorem), §2.2 (its proof: eq. (1) rule cost, eq. (2) table cost, Step 3 subtraction),
§2.3 (structure-function connection). Reuses `CapacityThreshold.Kmin` (the §2.2 model cost
`r + 2 log r + c₃`) from the Cor 2.2 warm-up.

Status: PROVED as pure real-arithmetic statements. This is the *arithmetic core* of
Sub-problem A only.

## What this DOES establish
* `dominance_gap_eq`: the §2.2 Step-3 identity — the lookup-minus-rule advantage is *exactly*
  `(L − r) − logCorr`, where `logCorr = 2 log r + log|O| + log n + c₃ + cd` is the `O(log L)`
  correction of §2.1. Pure algebra, no regime, no strengthened constants.
* `mdl_dominance`: under an explicit NAMED regime margin `hReg`, the rule-based two-part code
  is strictly shorter than the lookup table, `Lrule < Ltable`.

## What this does NOT establish (stays in prose; no overclaiming)
* No Kolmogorov complexity: `r`, `c₃`, `cd`, `O`, `n` are abstract reals; we do not formalize
  `r = K(R)`, and `O` is a real standing for `|O|` (not a finite type's cardinality).
* We do not prove the two coding bounds themselves: eq. (1) `MDL₂(rule) ≤ Lrule` and eq. (2)
  `MDL₂(lookup) ≥ L`. Those §2.2 counting arguments stay in prose. The Lean theorems prove the
  resulting arithmetic, taking `Lrule` (an upper bound on the true rule MDL) and `Ltable = L`
  (a lower bound on the true table MDL) as the named quantities; `Lrule < Ltable` then implies
  the paper's `MDL₂(rule) < MDL₂(lookup)`.
* We do not prove the §2.3 structure-function identity `min_α[α + Λ_x(α)] = K(x) + O(1)` — prose.

## On `K` and the hypothesis `L > K`
Theorem 2.1's hypotheses include `L > K` (capacity in bits). `K` enters *only* in the prose
derivation of eq. (2): a `K`-bit table holds at most `K/log|O|` of the `n` windows, so
`MDL₂(lookup) ≥ K + (L − K) = L`, and `L > K` is what makes the table unable to memorize all
`n` windows. Since the Lean arithmetic takes `Ltable = L` as given (the eq. (2) lower bound),
neither `K` nor `L > K` appears in the signatures — they live in the prose justification of
eq. (2). We deliberately do NOT add an unused `K` to the statements.

## Sign convention
The paper states the rule−lookup difference as `MDL₂(rule) − MDL₂(lookup) ≤ −(L − r) + O(log L)`
(a negative quantity). We state the equivalent lookup−rule *advantage*
`Ltable − Lrule = (L − r) − logCorr` (a positive quantity). Same content, negated.

## Hypotheses: paper-stated vs added/strengthened
* Paper-stated / faithful: `n ≥ 2` (verbatim §2.1); `c₃, cd ≥ 0`; the gap identity (no hyps).
* `hReg` ASSUMES a concrete form of what the paper DERIVES: in §2.2 Step 3 the regime gives
  `L > K ≥ c₀·r·log(r/δ) ≫ r` asymptotically, so the `O(log L)` correction is eventually below
  `L − r`. We replace that asymptotic "≪" with one explicit, non-asymptotic *sufficient* margin
  `hReg` — the same concrete-instance pattern as the warm-up's C1 constants.
* Strengthened (flagged): `O ≥ 3` is the natural-log analog of the warm-up's `r ≥ 3` — it forces
  `log|O| > 1`. It EXCLUDES the binary case `|O| = 2` (which the paper allows): there
  `log 2 < 1`, and dominance holds only for asymptotically larger `n`, needing a lossier bound.
  `r ≥ 3` is the concrete C3 buffer (`r ≥ c₂`).

`Real.log` is the natural logarithm; constant base-change factors are absorbed into the O(1)
overheads, as in the paper's "O(·) with constants traceable in principle" convention.
-/

namespace MDLDominance

open CapacityThreshold

/-- Rule-based two-part code length (Paper II §2.2 eq. (1), upper bound): the model cost
`Kmin r c₃ = r + 2 log r + c₃` plus the data-given-model cost `log|O| + log n + cd`. -/
noncomputable def Lrule (r c₃ O n cd : ℝ) : ℝ :=
  Kmin r c₃ + Real.log O + Real.log n + cd

/-- Optimal lookup-table length (Paper II §2.2 eq. (2), lower bound): `MDL₂(lookup) ≥ L`, with
`L = n · log|O|` the raw observation length of §2.1. -/
noncomputable def Ltable (O n : ℝ) : ℝ := n * Real.log O

/-- The logarithmic correction term — the `O(log L)` of the §2.1 statement. -/
noncomputable def logCorr (r O n c₃ cd : ℝ) : ℝ :=
  2 * Real.log r + Real.log O + Real.log n + c₃ + cd

/-- §2.2 Step 3 (exact form, no regime needed): the lookup-minus-rule advantage is exactly
`(L − r)` minus the logarithmic corrections. Pure algebra — fully faithful, no strengthened
constants. (Negate for the paper's `rule − lookup ≤ −(L − r) + O(log L)` sign convention.) -/
theorem dominance_gap_eq (r c₃ O n cd : ℝ) :
    Ltable O n - Lrule r c₃ O n cd = (Ltable O n - r) - logCorr r O n c₃ cd := by
  simp only [Ltable, Lrule, logCorr, Kmin]; ring

/-- Theorem 2.1 (arithmetic core): in the regime, the rule-based two-part code is strictly
shorter than the lookup table. The operative hypotheses are `hn` and the named regime margin
`hReg`; `_hr, _hO, _hc₃, _hcd` document the regime constants (C3 buffer, alphabet ≥ 3, nonneg
overheads) but are subsumed by `hReg`, so they are `_`-marked. (Paper II §1.2 + §2.1/§2.2.) -/
theorem mdl_dominance (r c₃ O n cd : ℝ)
    (_hr : 3 ≤ r) -- C3 buffer r ≥ c₂ ≥ 3 (paper: r ≥ c₂; concrete instance)
    (_hO : 3 ≤ O) -- alphabet ≥ 3 (paper: |O| ≥ 2; STRENGTHENED → log O > 1, excludes binary)
    (hn : 2 ≤ n) -- n ≥ 2 (paper §2.1, verbatim)
    (_hc₃ : 0 ≤ c₃) (_hcd : 0 ≤ cd) -- O(1) overheads ≥ 0
    (hReg : r + 2 * Real.log r + c₃ + cd + 1 ≤ (n - 1) * (Real.log O - 1)) :
    Lrule r c₃ O n cd < Ltable O n := by
  have hn0 : 0 < n := by linarith
  -- `log n ≤ n − 1`, the only nontrivial estimate; the rest is `hReg`.
  have hlogn : Real.log n ≤ n - 1 := Real.log_le_sub_one_of_pos hn0
  simp only [Lrule, Ltable, Kmin]
  nlinarith [hReg, hlogn]

end MDLDominance
