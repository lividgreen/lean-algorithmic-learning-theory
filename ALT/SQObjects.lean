/-
Copyright (c) 2026 Mykola Palamarchuk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mykola Palamarchuk
-/
import ALT.SQVersionSpace
import Mathlib

-- Formal-check file, not Mathlib-destined: opt out of the house-style header linter.
set_option linter.style.header false
-- `SepFam` is an undecidable predicate over abstract types, so the `filter` in `sqDim` needs a
-- classical instance; scope-level `open scoped Classical` (Framework §) is deliberate here.
set_option linter.style.openClassical false

/-!
# Genuine SQ objects: concept class, statistical dimension, oracle ([SQ] §3, FV-J)

Provenance: [SQ], §3.1 (the SQ oracle answers a query
`φ : Input → [−1,1]` with an estimate of `E_D[φ]` within tolerance `τ`), §3.4 (the statistical
dimension: "every `τ`-separated subfamily of `M` has size at most `d_SQ(M, μ)`" — distribution-
SPECIFIC, the BQ1 point of §3), §5 (parity has `d_SQ = 2^Ω(n)`), and Appendix A ("a query separates
`R'` from the truth whenever `|E_{R'}[φ] − E_R[φ]| > 2τ`").

FV-J makes these objects GENUINE, replacing the real-valued stand-ins of FV-A3
(`ALT/ParityCounterexample.lean`, where `dSQ` is a bare exponential) and FV-A4
(`ALT/SQVersionSpace.lean`). Candidates are indexed by an abstract type `ι` (as in the other SQ
files, to avoid `DecidableEq`-on-functions pain), the answer functional `ans : Q → ι → ℝ` is
abstract (covering both the distributional `E_{R'}[φ]` and the correlational parity form), and the
statistical dimension is the genuine max separated-subfamily size.

The headline: parity's `d_SQ = 2^Ω(n)` becomes a THEOREM (`sqDim_parity_ge`, via character
orthogonality), bridging FV-A3's previously-MODELED exponential premise (`parity_dSQ_ge_exp`).

## What this DOES establish
* `Separates`, `SepFam`, `sqDim`, `IsSQOracle` — the SQ objects as genuine definitions.
* `sepFam_card_le_sqDim` — the §3.4 characterization, now DEFINITIONAL (`Finset.le_sup`): every
  `τ`-separated subfamily has card `≤ sqDim`.
* `survivors_card_le_sqDim` — the pigeonhole upgrade of FV-A4's envelope: a pairwise-separated
  survivor set `V ⊆ M` has `V.card ≤ sqDim M τ ans`.
* `survivors_polyBounded_of_separated` — reusing `ParityCounterexample.PolyBounded` verbatim:
  Assumption A on the GENUINE `sqDim` (as a family) plus pairwise separation ⇒ survivor count is
  `poly`. (For the envelope under `2τ`-identifiability see `SQEnvelope.lean`; the unconditional
  version is not formalized.)
* `sqDim_mono_queries` (BQ1) — fewer separating queries ⇒ smaller-or-equal dimension: the
  distribution-specificity of `d_SQ(M, μ)` (a distribution-specific `ans` never exceeds a
  distribution-free `ans'` that can realize all its separations).
* Parity (`ι = Q = Finset (Fin n)`, uniform weights): `chi_add_single`, `sum_chi_eq_zero`,
  correlational `ansPar` with exact orthogonality `ansPar_eq`, and the headline
  `sqDim_parity_ge : 2^n ≤ sqDim univ τ ansPar` for `τ < 1`, bridged to FV-A3 by
  `parity_dSQ_ge_exp` (`dSQ (log 2) n ≤ sqDim`, since `exp(n·log 2) = 2^n`).

## What this does NOT establish (out of scope here; no overclaiming)
* Not the BFJKMR envelope theorem proper (the version-space bound WITHOUT the pairwise-separation
  hypothesis) — that is the statistical-dimension machinery beyond this file.
* Not the query-schedule construction, nor connecting `ansPar` to actual dynamics/rules
  (the algorithm layer — `SQAlgorithm.lean`).
* Not Raz's `Ω(r²)` memory lower bound (context citation), nor the FV-E union-bound glue
  (`sq_oracle_concentration`) — de-scoped; the oracle predicate `IsSQOracle` is supplied, but the
  finite-query union bound is left as residue.
-/

namespace SQObjects

section Framework

open scoped Classical

variable {ι Q : Type*}

/-- A query `φ` **separates** candidates `i, j` (at tolerance `τ`) when their answers differ by more
than `τ` (Appendix A: `|E_{R'}[φ] − E_R[φ]|` exceeds the threshold). -/
def Separates (τ : ℝ) (ans : Q → ι → ℝ) (φ : Q) (i j : ι) : Prop :=
  τ < |ans φ i - ans φ j|

/-- A **separated subfamily** `S ⊆ M`: every two distinct members are distinguished by some query
(§3.4, "τ-separated subfamily of `M`"). -/
def SepFam (M : Finset ι) (τ : ℝ) (ans : Q → ι → ℝ) (S : Finset ι) : Prop :=
  S ⊆ M ∧ ∀ i ∈ S, ∀ j ∈ S, i ≠ j → ∃ φ, Separates τ ans φ i j

/-- The **statistical dimension** `d_SQ(M, μ)` (§3.4): the largest size of a `τ`-separated subfamily
of `M`. Genuine max over the (finite) powerset — no longer a bare exponential stand-in. -/
noncomputable def sqDim (M : Finset ι) (τ : ℝ) (ans : Q → ι → ℝ) : ℕ :=
  (M.powerset.filter (SepFam M τ ans)).sup Finset.card

/-- The §3.4 characterization, now definitional: **every** `τ`-separated subfamily has size at most
`sqDim` (`Finset.le_sup` on the filtered powerset). -/
theorem sepFam_card_le_sqDim (M : Finset ι) (τ : ℝ) (ans : Q → ι → ℝ)
    {S : Finset ι} (hS : SepFam M τ ans S) : S.card ≤ sqDim M τ ans := by
  apply Finset.le_sup
  rw [Finset.mem_filter, Finset.mem_powerset]
  exact ⟨hS.1, hS⟩

/-- Survivor pigeonhole (the definitional upgrade of FV-A4's version-space envelope): a survivor set
`V ⊆ M` that is pairwise `τ`-separated has `V.card ≤ sqDim M τ ans`. -/
theorem survivors_card_le_sqDim (M : Finset ι) (τ : ℝ) (ans : Q → ι → ℝ)
    {V : Finset ι} (hV : V ⊆ M)
    (hsep : ∀ i ∈ V, ∀ j ∈ V, i ≠ j → ∃ φ, Separates τ ans φ i j) :
    V.card ≤ sqDim M τ ans :=
  sepFam_card_le_sqDim M τ ans ⟨hV, hsep⟩

/-- BQ1 (distribution-specificity of `d_SQ(M, μ)`): if every separation achievable by `ans` is also
achievable by `ans'`, then `sqDim …ans ≤ sqDim …ans'`. A distribution-specific answer functional
(fewer queries) never has larger statistical dimension than a distribution-free one that can realize
all its separations. -/
theorem sqDim_mono_queries {Q' : Type*} (M : Finset ι) (τ : ℝ)
    (ans : Q → ι → ℝ) (ans' : Q' → ι → ℝ)
    (h : ∀ i j : ι, ∀ φ : Q, Separates τ ans φ i j → ∃ ψ, Separates τ ans' ψ i j) :
    sqDim M τ ans ≤ sqDim M τ ans' := by
  apply Finset.sup_mono
  intro S hS
  rw [Finset.mem_filter, Finset.mem_powerset] at hS ⊢
  obtain ⟨hSM, hsub, hpair⟩ := hS
  refine ⟨hSM, hsub, fun i hi j hj hij => ?_⟩
  obtain ⟨φ, hφ⟩ := hpair i hi j hj hij
  exact h i j φ hφ

/-- The statistical dimension is **antitone in the tolerance**: a coarser separation threshold
admits fewer separated subfamilies. If `τ₁ ≤ τ₂` then every `τ₂`-separated subfamily is already
`τ₁`-separated (from `τ₁ ≤ τ₂ < |·|`), so the filtered powerset shrinks and its sup of cardinalities
can only decrease. No nonnegativity needed; this is what lets a `2τ`-net be bounded by `sqDim` at
the working tolerance `τ`. -/
theorem sqDim_antitone_tol (M : Finset ι) (ans : Q → ι → ℝ) {τ₁ τ₂ : ℝ} (h : τ₁ ≤ τ₂) :
    sqDim M τ₂ ans ≤ sqDim M τ₁ ans := by
  apply Finset.sup_mono
  intro S hS
  rw [Finset.mem_filter, Finset.mem_powerset] at hS ⊢
  obtain ⟨hSM, hsub, hpair⟩ := hS
  refine ⟨hSM, hsub, fun i hi j hj hij => ?_⟩
  obtain ⟨φ, hφ⟩ := hpair i hi j hj hij
  exact ⟨φ, lt_of_le_of_lt h hφ⟩

/-- A **maximum-cardinality `2τ`-separated subfamily** (a `2τ`-net) of a finite candidate set `V`
exists: the powerset of `V` filtered by `SepFam M (2τ)` is finite and nonempty (`∅` is separated),
so it has a cardinality-maximal element `N`. The filtering predicate is `SepFam M`, which already
entails `N ⊆ M`, so `sqDim M` measures the net at the same threshold (no `V ⊆ M` hypothesis needed).
Its linear `sqDim` bound and covering by maximality drive the identifiability-free envelope. -/
theorem exists_maximal_sepFam (M : Finset ι) (τ : ℝ) (ans : Q → ι → ℝ) {V : Finset ι} :
    ∃ N, N ⊆ V ∧ SepFam M (2 * τ) ans N ∧
      ∀ S, S ⊆ V → SepFam M (2 * τ) ans S → S.card ≤ N.card := by
  classical
  have hemp : SepFam M (2 * τ) ans ∅ :=
    ⟨Finset.empty_subset M, fun i hi => absurd hi (Finset.notMem_empty i)⟩
  have hPne : (V.powerset.filter (SepFam M (2 * τ) ans)).Nonempty := by
    refine ⟨∅, ?_⟩
    rw [Finset.mem_filter, Finset.mem_powerset]
    exact ⟨Finset.empty_subset V, hemp⟩
  obtain ⟨N, hNP, hNmax⟩ :=
    (V.powerset.filter (SepFam M (2 * τ) ans)).exists_max_image Finset.card hPne
  rw [Finset.mem_filter, Finset.mem_powerset] at hNP
  refine ⟨N, hNP.1, hNP.2, fun S hSV hS => ?_⟩
  apply hNmax
  rw [Finset.mem_filter, Finset.mem_powerset]
  exact ⟨hSV, hS⟩

/-- **Maximality ⇒ covering.** A cardinality-maximal `2τ`-separated subfamily `N ⊆ V` is a `2τ`-net
of `V`: every `v ∈ V` lies within `2τ` of some `n ∈ N` on *every* query. Indeed, if `v` were
`2τ`-separated from all of `N`, then `insert v N` would be a larger `2τ`-separated subfamily of `V`,
contradicting maximality — no transitivity is used, only closeness to a representative. The
`v ∈ N` case (take `n := v`) needs `0 ≤ τ`. -/
theorem sepNet_covers (M : Finset ι) (τ : ℝ) (ans : Q → ι → ℝ) (hτ : 0 ≤ τ)
    {V N : Finset ι} (hNV : N ⊆ V) (hVM : V ⊆ M)
    (hNsep : SepFam M (2 * τ) ans N)
    (hNmax : ∀ S, S ⊆ V → SepFam M (2 * τ) ans S → S.card ≤ N.card) :
    ∀ v ∈ V, ∃ n ∈ N, ∀ φ, |ans φ v - ans φ n| ≤ 2 * τ := by
  classical
  intro v hv
  by_cases hvN : v ∈ N
  · exact ⟨v, hvN, fun φ => by rw [sub_self, abs_zero]; linarith⟩
  · by_contra hcon
    -- `v` is `2τ`-separated from every `n ∈ N`.
    simp only [not_exists, not_and, not_forall, not_le] at hcon
    have hvsep : ∀ n ∈ N, ∃ φ, Separates (2 * τ) ans φ v n := fun n hn => hcon n hn
    have hsymm : ∀ (φ : Q) (x y : ι),
        Separates (2 * τ) ans φ x y → Separates (2 * τ) ans φ y x := by
      intro φ x y hxy
      change 2 * τ < |ans φ y - ans φ x|
      rwa [abs_sub_comm]
    have hins_sub : insert v N ⊆ V := Finset.insert_subset hv hNV
    have hSep : SepFam M (2 * τ) ans (insert v N) := by
      refine ⟨hins_sub.trans hVM, ?_⟩
      intro a ha b hb hab
      rcases Finset.mem_insert.mp ha with hav | haN
      · rcases Finset.mem_insert.mp hb with hbv | hbN
        · exact absurd (hav.trans hbv.symm) hab
        · rw [hav]; exact hvsep b hbN
      · rcases Finset.mem_insert.mp hb with hbv | hbN
        · rw [hbv]; exact (hvsep a haN).imp fun φ h => hsymm φ v a h
        · exact hNsep.2 a haN b hbN hab
    have hle := hNmax (insert v N) hins_sub hSep
    rw [Finset.card_insert_of_notMem hvN] at hle
    omega

/-- The **mass-merge averaging bound**, fully abstract (no net object needed). Reassigning each
`v ∈ V` to a representative `ρ v` that is `2τ`-close on every query, and summing the *nonnegative*
masses `w v`, moves each query answer by a mass-weighted average of `2τ`-close values: the merged
answer differs from the full answer by at most `2τ · Σ w`. Dividing by `Σ w > 0` gives the
normalized statement `|A_full − A_merge| ≤ 2τ`; this unnormalized form is the clean core. -/
theorem merge_answer_close (τ : ℝ) (ans : Q → ι → ℝ) (V : Finset ι) (w : ι → ℝ)
    (hw : ∀ v ∈ V, 0 ≤ w v) (ρ : ι → ι)
    (hclose : ∀ v ∈ V, ∀ φ, |ans φ v - ans φ (ρ v)| ≤ 2 * τ) (φ : Q) :
    |∑ v ∈ V, w v * (ans φ v - ans φ (ρ v))| ≤ 2 * τ * ∑ v ∈ V, w v := by
  calc |∑ v ∈ V, w v * (ans φ v - ans φ (ρ v))|
      ≤ ∑ v ∈ V, |w v * (ans φ v - ans φ (ρ v))| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ v ∈ V, w v * (2 * τ) := by
        apply Finset.sum_le_sum
        intro v hv
        rw [abs_mul, abs_of_nonneg (hw v hv)]
        exact mul_le_mul_of_nonneg_left (hclose v hv φ) (hw v hv)
    _ = 2 * τ * ∑ v ∈ V, w v := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro v _
        ring

/-- The **identifiability-free version-space envelope** (the BFJKMR clustering argument). For any
version space `V ⊆ M` and `0 ≤ τ`, there is a net `N ⊆ V` of card `≤ sqDim M τ ans`, with a
retraction `ρ : ι → ι` sending every `v ∈ V` into `N` within `2τ` on every query. Crucially there
is **no** pairwise-separation / identifiability hypothesis on `V`: `N` is a maximal `2τ`-separated
subfamily (`exists_maximal_sepFam`), bounded by `sqDim` at threshold `2τ ≥ τ` via antitonicity
(`sepFam_card_le_sqDim` + `sqDim_antitone_tol`), and covering by maximality (`sepNet_covers`).
Composed with `merge_answer_close` (masses merged onto `ρ`) this bounds the merged predictor's
answer shift by `2τ`. This is the object [SQ] Thm 4.1 / Appendix A cites in place of
`2τ`-identifiability: a learner-side net-and-merge available under Assumption A alone. -/
theorem versionSpace_net_envelope (M : Finset ι) (τ : ℝ) (ans : Q → ι → ℝ) (hτ : 0 ≤ τ)
    {V : Finset ι} (hVM : V ⊆ M) :
    ∃ (N : Finset ι) (ρ : ι → ι), N ⊆ V ∧ N.card ≤ sqDim M τ ans ∧
      (∀ v ∈ V, ρ v ∈ N) ∧ (∀ v ∈ V, ∀ φ, |ans φ v - ans φ (ρ v)| ≤ 2 * τ) := by
  classical
  obtain ⟨N, hNV, hNsep, hNmax⟩ := exists_maximal_sepFam M τ ans (V := V)
  have hcov := sepNet_covers M τ ans hτ hNV hVM hNsep hNmax
  have hcard : N.card ≤ sqDim M τ ans :=
    le_trans (sepFam_card_le_sqDim M (2 * τ) ans hNsep)
      (sqDim_antitone_tol M ans (by linarith))
  refine ⟨N, fun v => if hv : v ∈ V then (hcov v hv).choose else v, hNV, hcard, ?_, ?_⟩
  · intro v hv
    simp only [dif_pos hv]
    exact (hcov v hv).choose_spec.1
  · intro v hv φ
    simp only [dif_pos hv]
    exact (hcov v hv).choose_spec.2 φ

/-- The SQ oracle of §3.1 as an object: `answer` estimates the truth's query values within `τ`. -/
def IsSQOracle (answer truth : Q → ℝ) (τ : ℝ) : Prop := ∀ φ, |answer φ - truth φ| ≤ τ

/-- Reusing `ParityCounterexample.PolyBounded` verbatim: if the GENUINE statistical dimension of a
family is polynomially bounded (Assumption A) and each survivor set is pairwise `τ`-separated, then
the survivor count is `poly`. This is FV-A4's `candidates_polyBounded` instantiated with the
`A = m = 1` envelope supplied by `survivors_card_le_sqDim`. -/
theorem survivors_polyBounded_of_separated (τ : ℝ)
    (Mfam Vfam : ℝ → Finset ι) (ansfam : ℝ → Q → ι → ℝ)
    (hV : ∀ r, Vfam r ⊆ Mfam r)
    (hsep : ∀ r, ∀ i ∈ Vfam r, ∀ j ∈ Vfam r, i ≠ j → ∃ φ, Separates τ (ansfam r) φ i j)
    (hpoly : ParityCounterexample.PolyBounded (fun r => (sqDim (Mfam r) τ (ansfam r) : ℝ))) :
    ParityCounterexample.PolyBounded (fun r => ((Vfam r).card : ℝ)) := by
  refine SQVersionSpace.candidates_polyBounded _ _ hpoly 1 1 (by norm_num) ?_ ?_
  · filter_upwards with r
    have hle := survivors_card_le_sqDim (Mfam r) τ (ansfam r) (hV r) (hsep r)
    have hcast : ((Vfam r).card : ℝ) ≤ (sqDim (Mfam r) τ (ansfam r) : ℝ) := by exact_mod_cast hle
    simpa using hcast
  · filter_upwards with r
    positivity

end Framework

section Parity

variable {n : ℕ}

/-- The parity character `χ_S(x) = (−1)^{⟨S, x⟩}`, valued in `{±1} ⊆ ℝ`, for `S ⊆ Fin n` and
`x : Fin n → ZMod 2`. -/
def χ (S : Finset (Fin n)) (x : Fin n → ZMod 2) : ℝ :=
  if (∑ i ∈ S, x i) = 0 then 1 else -1

/-- Characters are `±1`, hence square to `1`. -/
lemma chi_sq (S : Finset (Fin n)) (x : Fin n → ZMod 2) : χ S x * χ S x = 1 := by
  unfold χ; split_ifs <;> norm_num

/-- Flipping coordinate `i` (adding `Pi.single i 1`) negates `χ_S` when `i ∈ S`, and fixes it
otherwise: the single-coordinate translation law that drives orthogonality. -/
lemma chi_add_single (S : Finset (Fin n)) (i : Fin n) (x : Fin n → ZMod 2) :
    χ S (x + Pi.single i 1) = if i ∈ S then -χ S x else χ S x := by
  unfold χ
  simp only [Pi.add_apply, Finset.sum_add_distrib, Pi.single_apply, Finset.sum_ite_eq']
  by_cases hiS : i ∈ S
  · simp only [if_pos hiS]
    have hdich : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
    rcases hdich (∑ j ∈ S, x j) with ha | ha
    · rw [ha, if_neg (by decide), if_pos (by decide)]
    · rw [ha, if_pos (by decide), if_neg (by decide)]; norm_num
  · simp only [if_neg hiS, add_zero]

/-- `∑_x χ_S(x) = 0` for `S ≠ ∅`: pick `i ∈ S`; the coordinate-`i` translation negates `χ_S` but
preserves the sum over the whole cube, so `∑ = −∑`. -/
lemma sum_chi_eq_zero (S : Finset (Fin n)) (hS : S ≠ ∅) :
    ∑ x : Fin n → ZMod 2, χ S x = 0 := by
  obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr hS
  have key : ∀ x, χ S (x + Pi.single i 1) = -χ S x := by
    intro x; rw [chi_add_single, if_pos hi]
  set T := ∑ x : Fin n → ZMod 2, χ S x with hT
  have hself : T = -T := by
    calc T = ∑ x : Fin n → ZMod 2, χ S (x + Pi.single i 1) :=
          (Equiv.sum_comp (Equiv.addRight (Pi.single i 1)) _).symm
      _ = ∑ x : Fin n → ZMod 2, -χ S x := by simp_rw [key]
      _ = -T := by rw [hT, Finset.sum_neg_distrib]
  linarith

/-- Correlational answer functional on the parity class: `ansPar φ S` is the normalized correlation
`⟨χ_φ, χ_S⟩` of two characters (queries = characters too). -/
noncomputable def ansPar (φ S : Finset (Fin n)) : ℝ :=
  (2 ^ n : ℝ)⁻¹ * ∑ x : Fin n → ZMod 2, χ φ x * χ S x

/-- The product-of-characters sum vanishes off the diagonal: for `φ ≠ S`, pick `i ∈ φ ∆ S`; the
coordinate-`i` translation negates exactly one factor, so `∑ = −∑ = 0`. -/
lemma sum_chi_mul_eq_zero (φ S : Finset (Fin n)) (h : φ ≠ S) :
    ∑ x : Fin n → ZMod 2, χ φ x * χ S x = 0 := by
  have hne : (symmDiff φ S).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty, ne_eq, ← Finset.bot_eq_empty, symmDiff_eq_bot]
    exact h
  obtain ⟨i, hi⟩ := hne
  rw [Finset.mem_symmDiff] at hi
  have key : ∀ x, χ φ (x + Pi.single i 1) * χ S (x + Pi.single i 1) = -(χ φ x * χ S x) := by
    intro x
    rw [chi_add_single, chi_add_single]
    rcases hi with ⟨hiφ, hiS⟩ | ⟨hiS, hiφ⟩
    · rw [if_pos hiφ, if_neg hiS]; ring
    · rw [if_neg hiφ, if_pos hiS]; ring
  set T := ∑ x : Fin n → ZMod 2, χ φ x * χ S x with hT
  have hself : T = -T := by
    have hshift : T = ∑ x : Fin n → ZMod 2,
        χ φ (Equiv.addRight (Pi.single i 1) x) * χ S (Equiv.addRight (Pi.single i 1) x) :=
      (Equiv.sum_comp (Equiv.addRight (Pi.single i 1)) (fun x => χ φ x * χ S x)).symm
    calc T = ∑ x : Fin n → ZMod 2,
              χ φ (Equiv.addRight (Pi.single i 1) x) * χ S (Equiv.addRight (Pi.single i 1) x) :=
            hshift
      _ = ∑ x : Fin n → ZMod 2, -(χ φ x * χ S x) := by
            simp only [Equiv.coe_addRight]; simp_rw [key]
      _ = -T := by rw [Finset.sum_neg_distrib, ← hT]
  linarith

/-- Exact orthogonality: `ansPar φ S = 1` iff `S = φ`, else `0`. Diagonal from `χ_φ² = 1` summed to
`2^n`; off-diagonal from `sum_chi_mul_eq_zero`. -/
theorem ansPar_eq (φ S : Finset (Fin n)) : ansPar φ S = if S = φ then 1 else 0 := by
  unfold ansPar
  rcases eq_or_ne S φ with h | h
  · rw [h, if_pos rfl]
    have hsum : ∑ x : Fin n → ZMod 2, χ φ x * χ φ x = (2 : ℝ) ^ n := by
      simp_rw [chi_sq]
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, ZMod.card, Fintype.card_fin,
          nsmul_eq_mul, mul_one]
      push_cast; ring
    rw [hsum, inv_mul_cancel₀ (by positivity)]
  · rw [if_neg h, sum_chi_mul_eq_zero φ S (Ne.symm h), mul_zero]

/-- **Headline (§5)**: parity's statistical dimension is `≥ 2^n` for any `τ < 1` — the whole
`2^n`-element class `Finset.univ` is `τ`-separated (query `φ = S` gives `|ansPar S S − ansPar S T| =
1`). Upgrades FV-A3's MODELED `d_SQ = 2^Ω(n)` premise to a theorem. -/
theorem sqDim_parity_ge {τ : ℝ} (hτ : τ < 1) :
    2 ^ n ≤ sqDim (Finset.univ : Finset (Finset (Fin n))) τ ansPar := by
  have hsep : SepFam (Finset.univ : Finset (Finset (Fin n))) τ ansPar Finset.univ := by
    refine ⟨Finset.subset_univ _, fun S _ T _ hST => ⟨S, ?_⟩⟩
    unfold Separates
    rw [ansPar_eq, ansPar_eq, if_pos rfl, if_neg (Ne.symm hST)]
    simpa using hτ
  have hle := sepFam_card_le_sqDim (Finset.univ : Finset (Finset (Fin n))) τ ansPar hsep
  rwa [Finset.card_univ, Fintype.card_finset, Fintype.card_fin] at hle

/-- FV-A3 bridge: the GENUINE parity dimension dominates FV-A3's modeled exponential stand-in
(`dSQ (log 2) n = exp(n·log 2) = 2^n`). Composed with `ParityCounterexample.dSQ_not_polyBounded`,
this makes "`d_SQ = 2^Ω(n)` for parity" machine-checked rather than modeled. -/
theorem parity_dSQ_ge_exp {τ : ℝ} (hτ : τ < 1) :
    ParityCounterexample.dSQ (Real.log 2) (n : ℝ)
      ≤ (sqDim (Finset.univ : Finset (Finset (Fin n))) τ ansPar : ℝ) := by
  have hdeq : ParityCounterexample.dSQ (Real.log 2) (n : ℝ) = (2 : ℝ) ^ n := by
    rw [ParityCounterexample.dSQ, ← Real.rpow_natCast (2 : ℝ) n,
        Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 2)]
  rw [hdeq]
  calc (2 : ℝ) ^ n = ((2 ^ n : ℕ) : ℝ) := by push_cast; ring
    _ ≤ (sqDim (Finset.univ : Finset (Finset (Fin n))) τ ansPar : ℝ) := by
        exact_mod_cast sqDim_parity_ge hτ

end Parity

end SQObjects
