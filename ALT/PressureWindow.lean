import Mathlib

-- Tier-1 formal check, not Mathlib-destined: opt out of the house-style header linter.
set_option linter.style.header false

/-!
# Pressure window Π: break-even (B1a) + interval structure (B1b)

Provenance: the conjectural pressure-window framing ("usefulness and retention are the same ratio", target **B1a**)
and its ratio form ("the pressure ratio `Π = L_struct / K_avail`" and its two-sided window, target
**B1b**). B1a: the rule is worth retaining exactly when the selective payoff of the MDL dominance
gap exceeds the Landauer upkeep, iff the observation length exceeds an explicit break-even
threshold `(L − r) · v > p_err · |s_code| · kT · ln 2`. B1b: the localized regime band is an
explicit interval in the pressure ratio `Π`, naming its edges `Π_low`, `Π_high`.

Builds conceptually on the existing cores `ALT/MDLDominance.lean` (FV-4: the dominance gap
`(L − r) − O(log L)`, the *usefulness* side) and `ALT/RetentionOverhead.lean` (FV-6: the
conditional-regeneration capacity overhead). Those are inspected and cross-referenced but NOT
imported: `upkeep` here is a Landauer maintenance *flux* (energy), a different quantity from
`RetentionOverhead.g` (capacity *bits*), and `payoff` parameterizes the leading dominance gap
abstractly, so a clean reuse is not available — B1a is kept self-contained.

Status: PROVED as pure real-arithmetic (a break-even iff, B1a; an interval iff, B1b; the dynamical
scissors under two POSITED monotonicities, S2).

## What this DOES establish
* `breakeven` (B1a): with positive per-prediction value `v`, retaining the rule pays
  (`upkeep < payoff`) iff the observation length `L` exceeds the explicit threshold
  `L_be = r + upkeep / v`.
* `netBenefit_pos` (B1a): the same fact in the `0 < netBenefit` form that §1.3 states
  (`netBenefit > 0 ↔ L_be < L`).
* `regimeBand_iff_pi_mem` (B1b): with positive capacity, the localized regime band holds iff the
  pressure `Π = L_struct / K_avail` lies in the interval `[Π_low, Π_high]` — making the two-sided
  pressure window well-defined as an interval and naming its edges. Plus `pi_pos` (positivity) and
  `Pi_mono_left` (`Π` increasing in the structured flux).
* `pi_antitone` (S2): under the two POSITED monotonicities `AccessDegrading L_struct` (structured
  flux ↓) and `CapacityConcentrating K_avail` (capacity ↑, positive), the pressure
  `Π(t) = L_struct t / K_avail t` is antitone in time (the §1.2 "scissors").
* `window_is_interval` + `dynamical_window` (S2): for any antitone `Π`, the window is a TIME
  interval — `Π` sweeps down through it (in at `Π_high`, out at `Π_low`); the capstone phrases this
  via B1b's `RegimeBand`.

## What this does NOT establish (flagged)
* This is the arithmetic core / break-even *threshold*, NOT the full retention theorem; the Cheng
  (2026) Context-Channel-Capacity / conditional-regeneration argument stays in prose.
* `payoff` uses the LEADING gap `(L − r)`. The exact dominance gap (with the `−O(log L)` correction)
  is `MDLDominance.dominance_gap_eq`; a tighter break-even via that correction is an optional
  refinement, NOT claimed here.
* The numerator is Paper II's `L` (the proved dominance gap). the framing's `L_struct`
  (epiplexity flux) is the conjectural pressure-window numerator; replacing `L` by `L_struct` is the
  CONJECTURAL step and is NOT done here.
* `v`, `p_err`, `kT` are modeled real parameters; `kT · ln 2` is the physical Landauer input (cited,
  not derived). The break-even algebra is sign-agnostic — it needs only `0 < v`; the physical regime
  `p_err, kT ≥ 0` (which makes `upkeep ≥ 0`) is not required and is not assumed.
* (B1b) `regimeBand_iff_pi_mem` is a REPARAMETRIZATION only — thin by design (cf.
  `PolyTimeAccounting`). It rewrites the band conditions in the `Π` variable and names the edges; it
  does NOT derive `Π_low` / `Π_high`. `Π_high` in particular is not derived from any throughput /
  access model — that is the conjectural access-degradation operator `S2`, the anticipated
  expressivity wall (documented): S2 below formalizes only the DOWNSTREAM
  consequence of `S2`, taking its monotonicity as a posited hypothesis.
* (B1b) `L_struct` is the conjectural epiplexity flux (§1.1 / §3.3) — NOT raw entropy, and NOT Paper
  II's proved `L`. The whole `Π` object is conjectural framing; this lemma establishes only its
  interval structure. No causal content ("firehose swamps / trickle insufficient ⇒ no
  representational reflection") is proved — only the interval algebra. (In prose the lower edge
  relates to the B1a break-even `L_be`, the "worth compressing" threshold, but the precise
  identification of
  `L_struct` with `L` is conjectural and is NOT formalized.)
* (S2) The two monotonicities `AccessDegrading L_struct` and `CapacityConcentrating K_avail` are
  POSITED, NOT derived. Deriving `AccessDegrading` (local `S_T`/`L_struct` ↓ under expansion) from
  conservation + expansion is the EXPRESSIVITY WALL: no existing theorem links local
  bounded-observer epiplexity dynamics to global conservation/expansion (the entropy-density,
  `E[K]=H`, DPI, and ergodic-mixing routes all require building the missing bridge). Recorded as
  Graveyard G8. `t` is an abstract time parameter; "expansion" is modeled ONLY as these two
  monotonicities.
* (S2) This proves the scissors logic only — monotone inputs ⟹ `Π` antitone ⟹ the window is a time
  interval. It makes NO claim that any physical system's `L_struct`/`K_avail` are actually monotone
  (Layer-2), NO rate claim, and NO non-emptiness claim (whether `t₁ ≤ t₂`, i.e. whether the window
  is actually entered, depends on quantitative inputs we do not have). No causal content about
  representational reflection — only the dynamical interval algebra.

## Hypotheses: paper-stated vs added
* Paper-stated / faithful: the §1.3 break-even inequality `(L − r) · v > upkeep`; the Landauer
  upkeep form `p_err · |s_code| · kT · ln 2`; the §1.1 ratio `Π = L_struct / K_avail`.
* Added / modeling: `L`, `r`, `v`, `p_err`, `scode`, `kT`, `L_struct`, `K_avail`, `Π_low`, `Π_high`
  are abstract reals; B1a needs only `0 < v`, B1b only `0 < K_avail`.
* POSITED (S2, the wall): `AccessDegrading L_struct` (`L_struct` antitone + nonneg) and
  `CapacityConcentrating K_avail` (`K_avail` monotone + positive) — assumptions about the time
  dynamics, not derived (see the does-NOT block / Graveyard G8).

`Real.log` is the natural logarithm; `Real.log 2 = ln 2` is the Landauer constant.
-/

namespace PressureWindow

open Real

/-- Landauer maintenance flux to hold `scode` bits at per-bit error rate `p_err`, temperature `kT`
(in energy units): each corrected error dissipates ≥ `kT · ln 2`. -/
noncomputable def upkeep (p_err scode kT : ℝ) : ℝ := p_err * scode * kT * Real.log 2

/-- Selective payoff of the MDL dominance gap `(L − r)` at value `v` per correct prediction. -/
def payoff (L r v : ℝ) : ℝ := (L - r) * v

/-- Net selective benefit of retaining the rule: payoff minus upkeep. -/
noncomputable def netBenefit (L r v p_err scode kT : ℝ) : ℝ :=
  payoff L r v - upkeep p_err scode kT

/-- The break-even observation length: `r` plus the upkeep in per-prediction-value units. -/
noncomputable def L_be (r v p_err scode kT : ℝ) : ℝ := r + upkeep p_err scode kT / v

/-- BREAK-EVEN (the Tier-1 core, §1.3): with positive per-prediction value `v`, retaining the rule
pays (`upkeep < payoff`) iff the observation length exceeds the explicit threshold
`L_be = r + upkeep / v`. -/
theorem breakeven (L r v p_err scode kT : ℝ) (hv : 0 < v) :
    upkeep p_err scode kT < payoff L r v ↔ L_be r v p_err scode kT < L := by
  rw [payoff, L_be, ← div_lt_iff₀ hv, lt_sub_iff_add_lt, add_comm]

/-- The §1.3 form: net benefit is positive iff the observation length exceeds the break-even
threshold. -/
theorem netBenefit_pos (L r v p_err scode kT : ℝ) (hv : 0 < v) :
    0 < netBenefit L r v p_err scode kT ↔ L_be r v p_err scode kT < L := by
  rw [netBenefit, sub_pos]
  exact breakeven L r v p_err scode kT hv

/-! ## B1b — the pressure ratio Π and its two-sided window -/

/-- Structured-flux-to-capacity ratio: `Π = L_struct / K_avail`, where
`L_struct` is the structured/compressible local flux and `K_avail` is the locally available
capacity. -/
noncomputable def Pi (L_struct K_avail : ℝ) : ℝ := L_struct / K_avail

/-- Localized regime band in absolute flux/capacity terms: the structured flux sits between a lower
fraction `Π_low` and an upper fraction `Π_high` of available capacity. -/
def RegimeBand (Pi_low Pi_high L_struct K_avail : ℝ) : Prop :=
  Pi_low * K_avail ≤ L_struct ∧ L_struct ≤ Pi_high * K_avail

/-- THE WINDOW IS AN INTERVAL IN Π (B1b core): with positive capacity, the regime band holds iff the
pressure `Π` lies in `[Π_low, Π_high]`. Exhibits `Π_high` and `Π_low` as explicit repackaged regime
constants and renders the two-sided pressure window (conjectural framing). Reparametrization only —
it names the edges, it does not derive them (see the does-NOT note). -/
theorem regimeBand_iff_pi_mem (Pi_low Pi_high L_struct K_avail : ℝ) (hK : 0 < K_avail) :
    RegimeBand Pi_low Pi_high L_struct K_avail ↔
      Pi_low ≤ Pi L_struct K_avail ∧ Pi L_struct K_avail ≤ Pi_high := by
  rw [RegimeBand, Pi, le_div_iff₀ hK, div_le_iff₀ hK]

/-- `Π` is positive when both structured flux and capacity are. -/
theorem pi_pos {L_struct K_avail : ℝ} (hL : 0 < L_struct) (hK : 0 < K_avail) :
    0 < Pi L_struct K_avail :=
  div_pos hL hK

/-- `Π` is monotone (nondecreasing) in the structured flux at fixed positive capacity. -/
theorem Pi_mono_left {L₁ L₂ K_avail : ℝ} (hK : 0 < K_avail) (h : L₁ ≤ L₂) :
    Pi L₁ K_avail ≤ Pi L₂ K_avail := by
  rw [Pi, Pi]; gcongr

/-! ## S2 — access degradation and the dynamical window (conjectural framing).
The two monotonicities below are POSITED (the S2 operator + the Jeans/L3 input), NOT derived —
deriving `L_struct`↓ from conservation + expansion is the expressivity wall (Graveyard G8). -/

/-- The access-degradation operator's defining property: structured local flux is non-increasing in
time and non-negative. (POSITED; the conjectural epiplexity `L_struct`.) -/
def AccessDegrading (L_struct : ℝ → ℝ) : Prop := Antitone L_struct ∧ ∀ t, 0 ≤ L_struct t

/-- Capacity concentration (Jeans/L3 input): available capacity is non-decreasing and positive.
(POSITED.) -/
def CapacityConcentrating (K_avail : ℝ → ℝ) : Prop := Monotone K_avail ∧ ∀ t, 0 < K_avail t

/-- The scissors (§1.2): under access degradation and capacity concentration, the pressure
`Π = L_struct / K_avail` is antitone in time. -/
theorem pi_antitone {L_struct K_avail : ℝ → ℝ}
    (hL : AccessDegrading L_struct) (hK : CapacityConcentrating K_avail) :
    Antitone (fun t => Pi (L_struct t) (K_avail t)) := by
  intro s t hst
  have hLts : L_struct t ≤ L_struct s := hL.1 hst
  have hKst : K_avail s ≤ K_avail t := hK.1 hst
  have hLt : 0 ≤ L_struct t := hL.2 t
  have hLs : 0 ≤ L_struct s := hLt.trans hLts
  have hKs : 0 < K_avail s := hK.2 s
  simp only [Pi]
  gcongr

/-- For any antitone `Π`, the pressure window is a time interval: if `Π` is below the upper edge by
time `t₁` and still above the lower edge by time `t₂`, then throughout `[t₁, t₂]` it lies in
`[Π_low, Π_high]`. (`Π` sweeps down through the window — in at `Π_high`, out at `Π_low`.) -/
theorem window_is_interval {P : ℝ → ℝ} (hP : Antitone P) {Pi_low Pi_high t₁ t₂ t : ℝ}
    (h₁ : P t₁ ≤ Pi_high) (h₂ : Pi_low ≤ P t₂) (ht₁ : t₁ ≤ t) (ht₂ : t ≤ t₂) :
    Pi_low ≤ P t ∧ P t ≤ Pi_high :=
  ⟨le_trans h₂ (hP ht₂), le_trans (hP ht₁) h₁⟩

/-- Capstone: under the two posited monotonicities, the dynamical window is a time interval,
expressed via B1b's `RegimeBand`. -/
theorem dynamical_window {L_struct K_avail : ℝ → ℝ}
    (hL : AccessDegrading L_struct) (hK : CapacityConcentrating K_avail)
    {Pi_low Pi_high t₁ t₂ t : ℝ}
    (h₁ : Pi (L_struct t₁) (K_avail t₁) ≤ Pi_high)
    (h₂ : Pi_low ≤ Pi (L_struct t₂) (K_avail t₂))
    (ht₁ : t₁ ≤ t) (ht₂ : t ≤ t₂) :
    RegimeBand Pi_low Pi_high (L_struct t) (K_avail t) :=
  (regimeBand_iff_pi_mem Pi_low Pi_high (L_struct t) (K_avail t) (hK.2 t)).mpr
    (window_is_interval (pi_antitone hL hK) h₁ h₂ ht₁ ht₂)

end PressureWindow
