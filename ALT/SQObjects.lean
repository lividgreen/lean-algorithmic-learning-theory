import ALT.SQVersionSpace
import Mathlib

-- Tier-1 formal check, not Mathlib-destined: opt out of the house-style header linter.
set_option linter.style.header false
-- `SepFam` is an undecidable predicate over abstract types, so the `filter` in `sqDim` needs a
-- classical instance; scope-level `open scoped Classical` (Framework §) is deliberate here.
set_option linter.style.openClassical false

/-!
# Genuine SQ objects: concept class, statistical dimension, oracle (Paper III §3, FV-J)

Provenance: `03_polynomial_convergence_under_SQ.md`, §3.1 (the SQ oracle answers a query
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
  `poly`. (The full BFJKMR envelope WITHOUT the separation hypothesis is stage 6.)
* `sqDim_mono_queries` (BQ1) — fewer separating queries ⇒ smaller-or-equal dimension: the
  distribution-specificity of `d_SQ(M, μ)` (a distribution-specific `ans` never exceeds a
  distribution-free `ans'` that can realize all its separations).
* Parity (`ι = Q = Finset (Fin n)`, uniform weights): `chi_add_single`, `sum_chi_eq_zero`,
  correlational `ansPar` with exact orthogonality `ansPar_eq`, and the headline
  `sqDim_parity_ge : 2^n ≤ sqDim univ τ ansPar` for `τ < 1`, bridged to FV-A3 by
  `parity_dSQ_ge_exp` (`dSQ (log 2) n ≤ sqDim`, since `exp(n·log 2) = 2^n`).

## What this does NOT establish (out of scope / later stages; no overclaiming)
* Not the BFJKMR envelope theorem proper (the version-space bound WITHOUT the pairwise-separation
  hypothesis) — that is the statistical-dimension machinery, stage 6.
* Not the query-schedule construction (stage 5/6), nor connecting `ansPar` to actual dynamics/rules
  (the algorithm layer, stage 5).
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
