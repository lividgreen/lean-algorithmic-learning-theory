/-
Copyright (c) 2026 Mykola Palamarchuk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mykola Palamarchuk
-/
import Mathlib
import ALT.FiniteInfoTheory

-- Formal-check file, not Mathlib-destined: opt out of the house-style linters.
set_option linter.style.header false
set_option linter.style.longLine false

/-!
# Cheng (2026) Theorem 4: a NECESSITY (lower) bound — not a sufficiency result (ChengCCC)

Provenance: re-checking `Cheng, R. (2026), Context Channel Capacity` (arXiv:2603.07415), the import
behind [Discovery] ([Discovery]) §4 retention (Proposition 4.2).

Cheng's Theorem 4 is the LOWER bound
  `Fgt̄ ≥ max(0, 1 − C_ctx / H(T)) · Fgt̄_max`,
which makes context capacity `C_ctx ≥ H(T)` **necessary** for low forgetting (`C_ctx = 0` forces
`Fgt̄ ≥ Fgt̄_max`, i.e. catastrophic forgetting). [Discovery]'s Prop 4.2 reads "the right side
vanishes, giving zero expected forgetting" — i.e. it treats the *vacuous* lower bound (all the
theorem yields once `C_ctx ≥ H(T)`) as if it were an *upper* bound of zero. That is a
necessary-as-sufficient error: a vanishing LOWER bound says nothing about an upper bound on
forgetting.

`cccLower_vacuous` machine-checks exactly this: when `C_ctx ≥ H(T)` Cheng's Theorem-4 right-hand
side is `0`, so the theorem then asserts only `Fgt̄ ≥ 0` — true of every learner — and provides NO
upper bound on forgetting. Retention must come from a separate (conditional-regeneration) argument,
not from Theorem 4.

The rigorous information-theoretic core (data-processing inequality + Fano ⟹ a misidentification
lower bound) is developed in `ALT/FiniteInfoTheory.lean`; the informal `misID ⟹ forgetting` step
of Cheng's proof appears here only as a named hypothesis.
-/

namespace ChengCCC

/-- Cheng (2026) Theorem 4 right-hand side: the lower bound on expected forgetting,
`max(0, 1 − C_ctx / H(T)) · Fgt̄_max`. -/
noncomputable def cccLower (Cctx HT Fgtmax : ℝ) : ℝ := max 0 (1 - Cctx / HT) * Fgtmax

/-- **The necessary-not-sufficient point, machine-checked.** Once `C_ctx ≥ H(T)` (with `H(T) > 0`),
Cheng's Theorem-4 lower bound equals `0`. So Theorem 4 then asserts only `Fgt̄ ≥ 0` — vacuous — and
gives NO upper bound on forgetting. [Discovery]'s Prop 4.2, which infers "zero expected forgetting"
from this vanishing, misuses a *necessary* condition as a *sufficient* one. -/
theorem cccLower_vacuous (Cctx HT Fgtmax : ℝ) (hHT : 0 < HT) (hsuff : HT ≤ Cctx) :
    cccLower Cctx HT Fgtmax = 0 := by
  have hcancel : Cctx / HT * HT = Cctx := div_mul_cancel₀ Cctx (ne_of_gt hHT)
  have h1 : 1 - Cctx / HT ≤ 0 := by nlinarith [hcancel, hHT, hsuff]
  unfold cccLower
  rw [max_eq_left h1, zero_mul]

/-! ### The rigorous information-theoretic core (Cheng's proof, Steps 1–3)

Cheng's Theorem-4 proof has a rigorous core (data-processing inequality + Fano) and one informal
step (misidentification ⟹ forgetting). We machine-check the core here, taking the two
information-theoretic facts as named hypotheses — `hDPI` (data processing: `I(T;θ) ≤ C_ctx`) and
`hFano` (Fano: `P_e ≥ (H(T|θ) − 1)/log(K−1)`) — which `ALT/FiniteInfoTheory.lean` discharges.
`hCond` is the identity `H(T|θ) = H(T) − I(T;θ)`. -/

/-- **Misidentification lower bound (DPI + Fano).** From data processing `mi ≤ C_ctx`, the
conditional-entropy identity `condEnt = H(T) − mi`, and Fano `(condEnt − 1)/log(K−1) ≤ P_e`, the
task-misidentification probability obeys `P_e ≥ (H(T) − C_ctx − 1)/log(K−1)`. This is the rigorous
content of Cheng's Theorem 4 (Steps 1–3). `K ≥ 3` makes `log(K−1) > 0`. -/
theorem misid_lower_bound (HT Cctx mi condEnt Pe K : ℝ)
    (hK : 3 ≤ K) (hDPI : mi ≤ Cctx) (hCond : condEnt = HT - mi)
    (hFano : (condEnt - 1) / Real.log (K - 1) ≤ Pe) :
    (HT - Cctx - 1) / Real.log (K - 1) ≤ Pe := by
  have hlog : 0 < Real.log (K - 1) := Real.log_pos (by linarith)
  refine le_trans ?_ hFano
  exact (div_le_div_iff_of_pos_right hlog).mpr (by rw [hCond]; linarith)

/-- **Forgetting lower bound (Cheng Theorem 4, full chain).** Adding Cheng's *informal* Step 4 as
the explicit hypothesis `hConn : P_e · Fgt_max ≤ Fgt̄` (wrong-task parameters degrade accuracy to
chance), the expected forgetting obeys `Fgt̄ ≥ ((H(T) − C_ctx − 1)/log(K−1)) · Fgt_max` — a *lower*
bound. Surfacing `hConn` makes explicit which part of Cheng's Theorem 4 is rigorous (the
information-theoretic core) and which is a modeling assumption. -/
theorem forgetting_lower_bound (HT Cctx mi condEnt Pe Fgt Fgtmax K : ℝ)
    (hK : 3 ≤ K) (hFmax : 0 ≤ Fgtmax)
    (hDPI : mi ≤ Cctx) (hCond : condEnt = HT - mi)
    (hFano : (condEnt - 1) / Real.log (K - 1) ≤ Pe)
    (hConn : Pe * Fgtmax ≤ Fgt) :
    ((HT - Cctx - 1) / Real.log (K - 1)) * Fgtmax ≤ Fgt := by
  have hmis := misid_lower_bound HT Cctx mi condEnt Pe K hK hDPI hCond hFano
  calc ((HT - Cctx - 1) / Real.log (K - 1)) * Fgtmax
      ≤ Pe * Fgtmax := mul_le_mul_of_nonneg_right hmis hFmax
    _ ≤ Fgt := hConn

/-! ### Fully discharged misidentification bound

`misid_lower_bound` above takes the three information-theoretic facts (DPI, the conditional-entropy
identity, Fano) as named hypotheses. `cheng_misid_bound_discharged` removes all three: each is now
supplied by `ALT/FiniteInfoTheory.lean` for the Markov chain `T → c → θ`. The *only* explicit
hypotheses left are the modelling setup — a joint pmf `ν` with the Markov condition, the task decoder
`g`, the capacity bound `hcap : I(c;θ) ≤ C_ctx`, and `K = |T| ≥ 3`. (Cheng's informal
`misID ⟹ forgetting` step is not involved here; it only enters `forgetting_lower_bound`.) -/

open FiniteInfoTheory in
/-- **Misidentification bound with the information-theoretic hypotheses discharged.** For the Markov
chain `T → c → θ` (`hM : MarkovCI ν`) with task decoder `g : θ → T` and context-channel-capacity
bound `hcap : I(c;θ) ≤ C_ctx`, the task-misidentification probability `Pe` obeys
`(H(T) − C_ctx − 1)/log(K−1) ≤ Pe` (`K = |T| ≥ 3`). DPI (`dataProcessing'`), the identity
`I(T;θ) = H(T) − H(T|θ)` (`mutualInfo_eq_sub_condEntropy`) and Fano (`fano'`) are all machine-proved,
not assumed. -/
theorem cheng_misid_bound_discharged {T c θ : Type*} [Fintype T] [Fintype c] [Fintype θ]
    [DecidableEq T] (ν : T → c → θ → ℝ) (g : θ → T)
    (hnn : ∀ t y z, 0 ≤ ν t y z) (hsum : ∑ t, ∑ y, ∑ z, ν t y z = 1)
    (hM : MarkovCI ν) (Cctx : ℝ) (hcap : mutualInfo (margYZ ν) ≤ Cctx)
    (hK : 3 ≤ Fintype.card T) :
    (entropy (marg₁ (margXZ ν)) - Cctx - 1) / Real.log ((Fintype.card T : ℝ) - 1)
      ≤ ∑ t, ∑ z, (if t = g z then 0 else margXZ ν t z) := by
  have hnnXZ : ∀ t z, 0 ≤ margXZ ν t z := fun t z => Finset.sum_nonneg fun y _ => hnn t y z
  have hsumXZ : ∑ t, ∑ z, margXZ ν t z = 1 := by
    unfold margXZ
    rw [Finset.sum_congr rfl fun t _ => Finset.sum_comm]
    exact hsum
  -- The three information-theoretic facts, each from the library.
  have hCond : condEntropy (margXZ ν) = entropy (marg₁ (margXZ ν)) - mutualInfo (margXZ ν) := by
    have := mutualInfo_eq_sub_condEntropy (margXZ ν) hnnXZ; linarith
  have hDPI : mutualInfo (margXZ ν) ≤ Cctx := le_trans (dataProcessing' ν hnn hsum hM) hcap
  have hFano := fano' (margXZ ν) g hnnXZ hsumXZ hK
  have hKr : (3 : ℝ) ≤ (Fintype.card T : ℝ) := by exact_mod_cast hK
  exact misid_lower_bound (entropy (marg₁ (margXZ ν))) Cctx (mutualInfo (margXZ ν))
    (condEntropy (margXZ ν)) (∑ t, ∑ z, (if t = g z then 0 else margXZ ν t z))
    (Fintype.card T : ℝ) hKr hDPI hCond hFano

open FiniteInfoTheory in
/-- **Forgetting lower bound with the information-theoretic hypotheses discharged.** The forgetting
analogue of `cheng_misid_bound_discharged`: for the Markov chain `T → c → θ` (`hM : MarkovCI ν`) with
task decoder `g`, capacity bound `hcap : I(c;θ) ≤ C_ctx`, `K = |T| ≥ 3`, and Cheng's *informal*
Step-4 modelling link `hConn : Pe · Fgt_max ≤ Fgt̄` (wrong-task parameters degrade accuracy to
chance, with `Pe` the concrete task-misidentification probability), the expected forgetting obeys
`Fgt̄ ≥ ((H(T) − C_ctx − 1)/log(K−1)) · Fgt_max`. DPI (`dataProcessing'`), the identity
`I(T;θ) = H(T) − H(T|θ)` (`mutualInfo_eq_sub_condEntropy`) and Fano (`fano'`) are all machine-proved
via `cheng_misid_bound_discharged`, not assumed; the *only* explicit hypotheses left are the
modelling setup (joint `ν` + `MarkovCI`, decoder `g`, capacity bound, `K ≥ 3`) plus `hConn` — the one
genuinely informal step of Cheng's Theorem 4. -/
theorem cheng_forgetting_bound_discharged {T c θ : Type*} [Fintype T] [Fintype c] [Fintype θ]
    [DecidableEq T] (ν : T → c → θ → ℝ) (g : θ → T)
    (hnn : ∀ t y z, 0 ≤ ν t y z) (hsum : ∑ t, ∑ y, ∑ z, ν t y z = 1)
    (hM : MarkovCI ν) (Cctx : ℝ) (hcap : mutualInfo (margYZ ν) ≤ Cctx)
    (hK : 3 ≤ Fintype.card T) (Fgt Fgtmax : ℝ) (hFmax : 0 ≤ Fgtmax)
    (hConn : (∑ t, ∑ z, (if t = g z then 0 else margXZ ν t z)) * Fgtmax ≤ Fgt) :
    ((entropy (marg₁ (margXZ ν)) - Cctx - 1) / Real.log ((Fintype.card T : ℝ) - 1)) * Fgtmax ≤ Fgt := by
  have hmis := cheng_misid_bound_discharged ν g hnn hsum hM Cctx hcap hK
  calc ((entropy (marg₁ (margXZ ν)) - Cctx - 1) / Real.log ((Fintype.card T : ℝ) - 1)) * Fgtmax
      ≤ (∑ t, ∑ z, (if t = g z then 0 else margXZ ν t z)) * Fgtmax :=
        mul_le_mul_of_nonneg_right hmis hFmax
    _ ≤ Fgt := hConn

end ChengCCC
