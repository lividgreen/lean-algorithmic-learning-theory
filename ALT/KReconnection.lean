import Mathlib
import ALT.KolmogorovComplexity
import ALT.KolmogorovTimeBounded
import ALT.CapacityThreshold
import ALT.MDLDominance
import ALT.RegimeConsistency
import ALT.RetentionOverhead
import ALT.PolyTimeAccounting

-- Tier-1 formal check, not Mathlib-destined: opt out of the house-style header linter.
set_option linter.style.header false

/-!
# Cross-file `K`-reconnection: the abstract `r` is the real Kolmogorov complexity

Provenance: `02_mdl_dominance_and_discovery.md`, §1.1 (`r = K(R)`, "program length in bits"). Ties
the abstract `r : ℝ` of the MDL-corpus theorems to the genuine bit-length Kolmogorov complexity
(`ALT/KolmogorovTimeBounded.lean`, `K_bitlen`/`K_bitlen_eq`) of a concrete rule `R`.

Status: PROVED. **Deliberately THIN — instantiation, not new math.** Each corollary is the
already-proved abstract theorem applied at `r := ↑(ruleComplexity R)`.

## What this DOES establish
* `ruleComplexity R := K_bitlen (encode R)` ties the abstract `r` to the real bit-length Kolmogorov
  complexity of a rule `R` (modelled as a `Code`); by `K_bitlen_eq` this is
  `Nat.size (K (encode R))`, the bit-length of the least-index complexity of `R`'s Gödel number.
* Five corollaries re-state the LOAD-BEARING abstract theorems about that real `r`: Corollary 2.2
  (`representable_of_C1`), Theorem 2.1 (`mdl_dominance`), regime consistency
  (`regime_strict_ordering`), retention overhead (`overhead_bigO`), poly-time accounting
  (`polytime_accounting`). This closes the "K stays in prose / `r` is an abstract real" boundary
  across the whole MDL corpus.

## What this does NOT establish (flagged plainly)
* INSTANTIATION ONLY — no new content. Each corollary is literally the abstract theorem at
  `r := ↑(ruleComplexity R)`.
* The regime hypotheses are NOT proven — `hC1`, `hReg`, `hC2`/`hC3`, the constant conditions all
  REMAIN ASSUMPTIONS. Proving they hold for a physical rule `R` (that `K_bitlen (encode R)` actually
  satisfies C1, etc.) is Layer-2 / physical, OUT OF SCOPE here.
* `r` reconnects to the BIT-LENGTH `K_bitlen` (`= Nat.size ∘ index-K`, per `K_bitlen_eq`), not the
  index `K` (which is exponentially larger).
* No claim that any particular `R` *achieves* a given complexity, nor that the regime is
  *satisfiable* for a given `R`. The abstract files' strengthened constants (`c₀≥3`, `c₁>1`, `O≥3`,
  …) carry over unchanged.

## Hypotheses: paper-stated vs added
* Paper-stated / faithful: `r = K(R)` in bits (§1.1); the five abstract theorems (already proved).
* Added / modeling: `R` modelled as a `Nat.Partrec.Code`; `K(R)` as `K_bitlen (encode R)`; the
  `ℕ → ℝ` coercion at the boundary.
-/

namespace KReconnection

open KolmogorovComplexity

/-- The paper's `r = K(R)` in **bits** (Paper II §1.1), as the real Kolmogorov complexity of a rule
`R` (modelled as a `Nat.Partrec.Code`). By `K_bitlen_eq`, this is `Nat.size (K (encode R))`
— the bit-length of the least-index complexity of `R`'s Gödel number. -/
noncomputable def ruleComplexity (R : Nat.Partrec.Code) : ℕ := K_bitlen (Encodable.encode R)

/-- Corollary 2.2 (representability) at the genuine `r = K(R)`. Instantiation of
`CapacityThreshold.representable_of_C1`; the C1/C3 hypotheses remain assumptions. -/
theorem representable_of_C1 (R : Nat.Partrec.Code) (K c₀ c₂ c₃ δ : ℝ)
    (hC1 : c₀ * (ruleComplexity R) * Real.log ((ruleComplexity R) / δ) ≤ K)
    (hc₀ : 3 ≤ c₀) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hC3 : c₂ ≤ (ruleComplexity R)) (hc₂ : 3 ≤ c₂) (_hc₃0 : 0 ≤ c₃) (hc₃ : c₃ ≤ c₂) :
    CapacityThreshold.Representable K (ruleComplexity R) c₃ :=
  CapacityThreshold.representable_of_C1 K (ruleComplexity R) c₀ c₂ c₃ δ
    hC1 hc₀ hδ0 hδ1 hC3 hc₂ _hc₃0 hc₃

/-- Theorem 2.1 (static MDL dominance) at the genuine `r = K(R)`. Instantiation of
`MDLDominance.mdl_dominance`; the regime margin `hReg` remains an assumption. -/
theorem mdl_dominance (R : Nat.Partrec.Code) (c₃ O n cd : ℝ)
    (hr : 3 ≤ (ruleComplexity R : ℝ)) (hO : 3 ≤ O) (hn : 2 ≤ n) (hc₃ : 0 ≤ c₃) (hcd : 0 ≤ cd)
    (hReg : (ruleComplexity R) + 2 * Real.log (ruleComplexity R) + c₃ + cd + 1
              ≤ (n - 1) * (Real.log O - 1)) :
    MDLDominance.Lrule (ruleComplexity R) c₃ O n cd < MDLDominance.Ltable O n :=
  MDLDominance.mdl_dominance (ruleComplexity R) c₃ O n cd hr hO hn hc₃ hcd hReg

/-- Regime consistency `r < K < L` at the genuine `r = K(R)`. Instantiation of
`RegimeConsistency.regime_strict_ordering`; the C1–C3 hypotheses remain assumptions. -/
theorem regime_strict_ordering (R : Nat.Partrec.Code) (K L c₀ c₁ c₂ δ : ℝ)
    (hC1 : c₀ * (ruleComplexity R) * Real.log ((ruleComplexity R) / δ) ≤ K) (hC2 : c₁ * K ≤ L)
    (hC3 : c₂ ≤ (ruleComplexity R)) (hc₀ : 1 ≤ c₀) (hc₁ : 1 < c₁) (hc₂ : 3 ≤ c₂)
    (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    ((ruleComplexity R : ℕ) : ℝ) < K ∧ K < L :=
  RegimeConsistency.regime_strict_ordering (ruleComplexity R) K L c₀ c₁ c₂ δ
    hC1 hC2 hC3 hc₀ hc₁ hc₂ hδ0 hδ1

/-- Retention capacity overhead `O(r·log(r/δ))` at the genuine `r = K(R)`. Instantiation of
`RetentionOverhead.overhead_bigO`; the regime constants remain assumptions. -/
theorem overhead_bigO (R : Nat.Partrec.Code) (δ c₆ c₇ : ℝ)
    (hr : 3 ≤ (ruleComplexity R : ℝ)) (hδ0 : 0 < δ) (hδ1 : δ < 1) (hc₆ : 0 ≤ c₆) (hc₇ : 0 ≤ c₇) :
    RetentionOverhead.g (ruleComplexity R) δ c₆ c₇
      ≤ (c₆ + c₇ + 3) * (ruleComplexity R) * Real.log ((ruleComplexity R) / δ) :=
  RetentionOverhead.overhead_bigO (ruleComplexity R) δ c₆ c₇ hr hδ0 hδ1 hc₆ hc₇

/-- Poly-time accounting `O(r²·log(1/δ))` at the genuine `r = K(R)`. Instantiation of
`PolyTimeAccounting.polytime_accounting`; the sample/per-step bounds remain assumptions. -/
theorem polytime_accounting (R : Nat.Partrec.Code) (Tsearch cstep a b δ : ℝ)
    (hT : Tsearch ≤ a * (ruleComplexity R) * Real.log (1 / δ)) (hc : cstep ≤ b * (ruleComplexity R))
    (ha : 0 ≤ a) (_hb : 0 ≤ b) (hr : 1 ≤ (ruleComplexity R : ℝ))
    (_hT0 : 0 ≤ Tsearch) (hc0 : 0 ≤ cstep) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    Tsearch * cstep ≤ a * b * (ruleComplexity R) ^ 2 * Real.log (1 / δ) :=
  PolyTimeAccounting.polytime_accounting Tsearch cstep (ruleComplexity R) a b δ
    hT hc ha _hb hr _hT0 hc0 hδ0 hδ1

end KReconnection
