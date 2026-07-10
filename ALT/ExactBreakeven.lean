/-
Copyright (c) 2026 Mykola Palamarchuk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mykola Palamarchuk
-/
import Mathlib
import ALT.MDLDominance
import ALT.PressureWindow

-- Formal-check file, not Mathlib-destined: opt out of the house-style header linter.
set_option linter.style.header false

/-!
# Exact-gap retention break-even (unifying FV-4 dominance and B1a retention)

Provenance: Paper II, §2.1 / Theorem 2.1 (FV-4, the static MDL dominance
gap `Ltable − Lrule`) and the conjectural retention break-even framing (B1a). B1a
(`ALT/PressureWindow.lean`) proved the break-even using the LEADING gap `(L − r)` and flagged the
exact gap as an optional refinement; this file delivers that refinement by instantiating B1a's
`breakeven` at the exact dominance endpoints `L := Ltable`, `r := Lrule`, so the payoff is the EXACT
gap `Ltable − Lrule` (which carries FV-4's `−O(log L)` correction and explicit constants) times the
per-prediction value.

Status: PROVED. Mostly reuse; the one genuinely new fact is `domGap_pos` (the exact gap is strictly
positive under the dominance regime, from `mdl_dominance`).

## What this DOES establish
* `domGap := Ltable − Lrule`: the exact MDL dominance gap (FV-4).
* `domGap_pos`: under the Theorem 2.1 dominance regime, the exact gap is strictly positive.
* `breakeven_exact`: B1a's `breakeven` at the exact endpoints — the rule pays to retain
  (`upkeep < domGap · v`) iff the observation length `Ltable` exceeds the break-even threshold
  `L_be (Lrule) v …`.
* `retention_pays`: once `v` clears the `upkeep / gap` ratio, retention has strictly positive net
  benefit at the exact gap.
* `exists_value_threshold`: under the regime (`domGap > 0`), the explicit per-prediction-value
  threshold `v₀ = upkeep / domGap` above which retention pays.

## What this does NOT establish (flagged)
* This is the EXACT-GAP refinement of B1a — it sharpens the leading `(L − r)` to the real dominance
  gap `Ltable − Lrule`. Pure arithmetic + reuse; no new learning-theory content.
* Reuses `MDLDominance` (FV-4) and `PressureWindow` (B1a, `upkeep`/`breakeven`); the dominance gap's
  coding bounds (eq. (1) / eq. (2)) stay where FV-4 established them (prose there), NOT re-proved.
* `v`, `p_err`, `kT` are modeled reals; `kT · ln 2` is the cited Landauer input. No pressure-window
  causal claim — this is the retention criterion only.

## Hypotheses: paper-stated vs added
* Paper-stated / faithful: the Theorem 2.1 regime hypotheses (carried verbatim from
  `mdl_dominance`); the Landauer upkeep `p_err · |s_code| · kT · ln 2`.
* Added / modeling: `v`, `p_err`, `scode`, `kT` abstract reals; the break-even needs only `0 < v`
  (and the regime hypotheses for strict positivity of the gap).
-/

namespace ExactBreakeven

open Real

/-- The EXACT MDL dominance gap (FV-4): lookup cost minus rule cost. -/
noncomputable def domGap (r c₃ O n cd : ℝ) : ℝ :=
  MDLDominance.Ltable O n - MDLDominance.Lrule r c₃ O n cd

/-- Under the dominance regime, the exact gap is strictly positive (from `mdl_dominance`). -/
theorem domGap_pos (r c₃ O n cd : ℝ) (hr : 3 ≤ r) (hO : 3 ≤ O) (hn : 2 ≤ n) (hc₃ : 0 ≤ c₃)
    (hcd : 0 ≤ cd) (hReg : r + 2 * Real.log r + c₃ + cd + 1 ≤ (n - 1) * (Real.log O - 1)) :
    0 < domGap r c₃ O n cd :=
  sub_pos.mpr (MDLDominance.mdl_dominance r c₃ O n cd hr hO hn hc₃ hcd hReg)

/-- Exact-gap retention break-even: instantiate `PressureWindow.breakeven` at the dominance
endpoints (`L := Ltable`, `r := Lrule`), so the payoff is the EXACT gap `× v`. The rule pays to
retain iff upkeep is below the exact gap times value. -/
theorem breakeven_exact (r c₃ O n cd v p_err scode kT : ℝ) (hv : 0 < v) :
    PressureWindow.upkeep p_err scode kT < domGap r c₃ O n cd * v
      ↔ PressureWindow.L_be (MDLDominance.Lrule r c₃ O n cd) v p_err scode kT
          < MDLDominance.Ltable O n :=
  PressureWindow.breakeven (MDLDominance.Ltable O n) (MDLDominance.Lrule r c₃ O n cd)
    v p_err scode kT hv

/-- Once the per-prediction value clears the upkeep/gap ratio, retention has strictly positive net
benefit at the exact gap. -/
theorem retention_pays (r c₃ O n cd v p_err scode kT : ℝ) (_hv : 0 < v)
    (hval : PressureWindow.upkeep p_err scode kT < domGap r c₃ O n cd * v) :
    0 < domGap r c₃ O n cd * v - PressureWindow.upkeep p_err scode kT := by
  linarith

/-- Under the regime (`domGap > 0`), there is an explicit value threshold `v₀ = upkeep / domGap`
above which retention pays. -/
theorem exists_value_threshold (r c₃ O n cd p_err scode kT : ℝ)
    (hgap : 0 < domGap r c₃ O n cd) :
    ∃ v₀, ∀ v, v₀ < v → PressureWindow.upkeep p_err scode kT < domGap r c₃ O n cd * v := by
  refine ⟨PressureWindow.upkeep p_err scode kT / domGap r c₃ O n cd, fun v hv₀ => ?_⟩
  rw [div_lt_iff₀ hgap] at hv₀
  rwa [mul_comm] at hv₀

end ExactBreakeven
