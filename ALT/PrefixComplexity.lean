import Mathlib
import ALT.KolmogorovComplexity
import ALT.KolmogorovBitlen

-- Tier-1 formal check, not Mathlib-destined: opt out of the house-style header linter.
set_option linter.style.header false

/-!
# Prefix-free Kolmogorov complexity `KP` is a semimeasure

Paper II §1.1 prior (FV-13); Solomonoff/Levin.

Provenance: extends `ALT/KolmogorovComplexity.lean` (Slice 1: `Computes`, `codelen`, `K`, `K_le`,
`exists_min_code`). Formalizes the **universal a-priori semimeasure** bound `∑ₓ 2⁻ᴷᴾ⁽ˣ⁾ ≤ 1`
(Levin's coding theorem / Solomonoff prior), the defining property of a *prefix-free* Kolmogorov
complexity. Connects to Paper II §1.1 (`K(R)`, program length in bits) and Paper III §2.

## Why this is genuine content (not reusable from the existing measures)
The plain bit-length complexity `K_bitlen` (`ALT/KolmogorovBitlen.lean`) is **not** a
semimeasure: `∑ₓ 2⁻ᴷᵇⁱᵗˡᵉⁿ⁽ˣ⁾` diverges (there are `≈ 2ⁿ` strings of complexity `n`). The
semimeasure bound holds only after paying the *prefix premium*: descriptions must be
self-delimiting. We charge that premium with an Elias-γ-class length `plen m = 2 · Nat.size (m + 1)`
on program indices, so that the description set is prefix-free and its Kraft sum is `≤ 1`.

## What this establishes
* `plen`: a self-delimiting (Elias-γ-class) bit-length on program indices, `2 · Nat.size (m+1)`.
* `KP`: prefix-free Kolmogorov complexity — least `plen`-length over codes computing `x` from `0`.
* `plen_mono`, `KP_eq : KP x = plen (K x)`: `KP` factors through the existing least-index `K`.
* `K_injective`: distinct outputs have distinct least-index programs.
* `kraft_plen : ∑' m, 2⁻¹ ^ plen m ≤ 1`: the Kraft inequality for the `plen` code (the crux).
* `kraft_KP : ∑' x, 2⁻¹ ^ KP x ≤ 1`: **the headline** — `KP` is a semimeasure.
* `kraft_prior : ∑' i : ι, 2⁻¹ ^ KP (Encodable.encode i) ≤ 1`: the Paper II prior bridge — the prior
  `w(R') ∝ 2⁻ᴷᴾ⁽ᵉⁿᶜᵒᵈᵉ ᴿ'⁾` over any encodable rule class is a semimeasure (closes Paper II FV-1's
  caveat; this file is Paper II **FV-13**).
* `KP_not_computable`: `KP` is genuinely **uncomputable** (Berry argument, mirroring
  `K_bitlen_not_computable`).

## What this does NOT establish (out of scope)
* Two-machine / prefix-machine additive invariance — out of scope (single fixed `Code.eval`; see the
  documented obstruction in `ALT/KolmogorovBitlen.lean`).
* Does NOT reconnect `KP` to the abstract `r` reals of the MDL corpus.

## Hypotheses: paper-stated vs added
* Paper-stated / faithful: `∑ₓ 2⁻ᴷᴾ⁽ˣ⁾ ≤ 1` for a prefix-free complexity `KP`.
* Added / modeling: one fixed machine (`Code.eval`); the Elias-γ-class length `2 · Nat.size (·+1)`
  as the concrete self-delimiting code; the input-`0` ("output from nothing") convention inherited
  from Slice 1.
-/

namespace PrefixComplexity

open Nat.Partrec Nat.Partrec.Code KolmogorovComplexity
open scoped ENNReal

/-- A self-delimiting (Elias-γ-class) bit-length on program indices: twice the number of bits of
`m + 1`. The doubling is the prefix premium that makes the code's Kraft sum `≤ 1`. -/
def plen (m : ℕ) : ℕ := 2 * Nat.size (m + 1)

/-- **Prefix-free Kolmogorov complexity**: the least self-delimiting description length `plen` over
codes that output `x` from input `0`. Well-defined — `Code.const x` computes `x` (Slice 1). -/
noncomputable def KP (x : ℕ) : ℕ := sInf {l | ∃ c, Computes c x ∧ plen (Encodable.encode c) = l}

/-- `plen` is monotone: more bits in the index ⇒ longer self-delimiting description. -/
theorem plen_mono : Monotone plen := by
  intro m n h
  unfold plen
  gcongr
  exact Nat.size_le_size (by omega)

/-- The least-index complexity `K` is injective: distinct outputs need distinct least-index
programs (a code has a unique output, and `Encodable.encode` is injective). -/
theorem K_injective : Function.Injective K := by
  intro x y h
  obtain ⟨cx, hcx, hlx⟩ := exists_min_code x
  obtain ⟨cy, hcy, hly⟩ := exists_min_code y
  have hcc : cx = cy := by
    apply Encodable.encode_injective
    change codelen cx = codelen cy
    rw [hlx, hly, h]
  subst hcc
  simp only [Computes] at hcx hcy
  rw [hcx] at hcy
  exact Part.some_inj.mp hcy

/-- `KP` factors through the existing least-index `K`: minimizing a monotone length over the same
index set is the length of the minimizing index. -/
theorem KP_eq (x : ℕ) : KP x = plen (K x) := by
  apply le_antisymm
  · -- `≤`: the minimizing code `c` (with `encode c = K x`) witnesses `plen (K x) ∈` the set.
    obtain ⟨c, hc, hlc⟩ := exists_min_code x
    exact Nat.sInf_le ⟨c, hc, congrArg plen (show Encodable.encode c = K x from hlc)⟩
  · -- `≥`: `plen (K x)` lower-bounds the set; close with `plen_mono` + `K_le`.
    have hne : {l | ∃ c, Computes c x ∧ plen (Encodable.encode c) = l}.Nonempty := by
      obtain ⟨c, hc, _⟩ := exists_min_code x
      exact ⟨_, c, hc, rfl⟩
    obtain ⟨c, hc, hlc⟩ := Nat.sInf_mem hne
    calc plen (K x) ≤ plen (Encodable.encode c) := plen_mono (K_le hc)
      _ = KP x := hlc

/-- **Kraft inequality for the `plen` code** (the crux): the self-delimiting `plen` lengths satisfy
`∑' m, 2⁻¹ ^ plen m ≤ 1`. Each weight is `≤ ((m+2)²)⁻¹` (via `Nat.lt_size_self`), and the additive
telescoping bound `2⁻¹ ^ plen m + (m+2)⁻¹ ≤ (m+1)⁻¹` controls every partial sum. -/
theorem kraft_plen : ∑' m, (2⁻¹ : ℝ≥0∞) ^ (plen m) ≤ 1 := by
  -- Additive telescoping step: `2⁻¹ ^ plen n + (n+2)⁻¹ ≤ (n+1)⁻¹`.
  have key : ∀ n : ℕ,
      (2⁻¹ : ℝ≥0∞) ^ (plen n) + ((n : ℝ≥0∞) + 2)⁻¹ ≤ ((n : ℝ≥0∞) + 1)⁻¹ := by
    intro n
    -- The size bound `n + 2 ≤ 2 ^ size (n+1)` gives `(n+2)² ≤ 2 ^ plen n`.
    have hb : ((n : ℝ≥0∞) + 2) ^ 2 ≤ (2 : ℝ≥0∞) ^ (plen n) := by
      have hP : (n + 2 : ℕ) ≤ 2 ^ Nat.size (n + 1) := by
        have := Nat.lt_size_self (n + 1); omega
      calc ((n : ℝ≥0∞) + 2) ^ 2
          = (((n + 2 : ℕ) : ℝ≥0∞)) ^ 2 := by push_cast; ring
        _ ≤ (((2 ^ Nat.size (n + 1) : ℕ) : ℝ≥0∞)) ^ 2 := by gcongr
        _ = (2 : ℝ≥0∞) ^ (plen n) := by rw [plen]; push_cast; rw [← pow_mul, Nat.mul_comm]
    -- (I) each weight is dominated by `((n+2)²)⁻¹`.
    have hI : (2⁻¹ : ℝ≥0∞) ^ (plen n) ≤ (((n : ℝ≥0∞) + 2) ^ 2)⁻¹ := by
      rw [← ENNReal.inv_pow]
      exact ENNReal.inv_le_inv' hb
    -- (II) combine with the arithmetic `1/(n+2)² + 1/(n+2) ≤ 1/(n+1)`, transferred to `ℝ`.
    calc (2⁻¹ : ℝ≥0∞) ^ (plen n) + ((n : ℝ≥0∞) + 2)⁻¹
        ≤ (((n : ℝ≥0∞) + 2) ^ 2)⁻¹ + ((n : ℝ≥0∞) + 2)⁻¹ := add_le_add_left hI _
      _ ≤ ((n : ℝ≥0∞) + 1)⁻¹ := by
          rw [show ((n : ℝ≥0∞) + 2) = ((n + 2 : ℕ) : ℝ≥0∞) by push_cast; ring,
              show ((n : ℝ≥0∞) + 1) = ((n + 1 : ℕ) : ℝ≥0∞) by push_cast; ring,
              ← ENNReal.toReal_le_toReal (by finiteness) (by finiteness),
              ENNReal.toReal_add (by finiteness) (by finiteness)]
          simp only [ENNReal.toReal_inv, ENNReal.toReal_pow, ENNReal.toReal_natCast]
          push_cast
          rw [← sub_nonneg, sub_add_eq_sub_sub]
          have h1 : ((n : ℝ) + 1) ≠ 0 := by positivity
          have h2 : ((n : ℝ) + 2) ≠ 0 := by positivity
          have heq : ((n : ℝ) + 1)⁻¹ - (((n : ℝ) + 2) ^ 2)⁻¹ - ((n : ℝ) + 2)⁻¹
              = (((n : ℝ) + 1) * ((n : ℝ) + 2) ^ 2)⁻¹ := by field_simp; ring
          rw [heq]; positivity
  -- Telescoping induction: `∑_{m<n} 2⁻¹ ^ plen m + (n+1)⁻¹ ≤ 1`, hence every partial sum `≤ 1`.
  have psum : ∀ n : ℕ,
      (∑ m ∈ Finset.range n, (2⁻¹ : ℝ≥0∞) ^ (plen m)) + ((n : ℝ≥0∞) + 1)⁻¹ ≤ 1 := by
    intro n
    induction n with
    | zero => simp
    | succ k ih =>
      rw [Finset.sum_range_succ, add_assoc]
      have hc : ((k + 1 : ℕ) : ℝ≥0∞) + 1 = (k : ℝ≥0∞) + 2 := by push_cast; ring
      calc (∑ m ∈ Finset.range k, (2⁻¹ : ℝ≥0∞) ^ (plen m))
              + ((2⁻¹ : ℝ≥0∞) ^ (plen k) + (((k + 1 : ℕ) : ℝ≥0∞) + 1)⁻¹)
          ≤ (∑ m ∈ Finset.range k, (2⁻¹ : ℝ≥0∞) ^ (plen m)) + ((k : ℝ≥0∞) + 1)⁻¹ := by
            rw [hc]; exact add_le_add_right (key k) _
        _ ≤ 1 := ih
  refine ENNReal.tsum_le_of_sum_range_le (fun n => ?_)
  exact le_trans le_self_add (psum n)

/-- **Headline: `KP` is a semimeasure** — `∑' x, 2⁻¹ ^ KP x ≤ 1` (Levin's coding theorem /
universal a-priori semimeasure). Inject outputs into descriptions via the injective least-index
`K` (`tsum_comp_le_tsum_of_injective`), then apply the Kraft bound `kraft_plen`. -/
theorem kraft_KP : ∑' x, (2⁻¹ : ℝ≥0∞) ^ (KP x) ≤ 1 := by
  simp_rw [KP_eq]
  exact (ENNReal.tsum_comp_le_tsum_of_injective K_injective
    (fun m => (2⁻¹ : ℝ≥0∞) ^ (plen m))).trans kraft_plen

/-- **The Paper II prior `w(R') = 2⁻ᴷᴾ⁽ᵉⁿᶜᵒᵈᵉ ᴿ'⁾` is a semimeasure** over any encodable rule class
`ι`: `∑' R' : ι, 2⁻¹ ^ KP (encode R') ≤ 1`. Re-index `kraft_KP` along the injective `encode : ι → ℕ`
(`tsum_comp_le_tsum_of_injective`). This is the prior used in the MDL/discovery corpus. -/
theorem kraft_prior {ι : Type*} [Encodable ι] :
    ∑' i : ι, (2⁻¹ : ℝ≥0∞) ^ (KP (Encodable.encode i)) ≤ 1 :=
  (ENNReal.tsum_comp_le_tsum_of_injective Encodable.encode_injective
    (fun m => (2⁻¹ : ℝ≥0∞) ^ (KP m))).trans kraft_KP

/-! ## Uncomputability of `KP` (sanity follow-on; not load-bearing for the semimeasure headline) -/

/-- The self-delimiting length of code `c` — the quantity minimized by `KP`
(`KP x = sInf { plenc c | Computes c x }`). -/
def plenc (c : Code) : ℕ := plen (Encodable.encode c)

/-- Any program computing `x` bounds `KP x` by its own self-delimiting length. -/
theorem KP_le {c : Code} {x : ℕ} (h : Computes c x) : KP x ≤ plenc c :=
  Nat.sInf_le ⟨c, h, rfl⟩

/-- `KP` is unbounded — from `K_unbounded` via `KP_eq` and the growth of `Nat.size`. -/
theorem KP_unbounded (n : ℕ) : ∃ x, n < KP x := by
  obtain ⟨x, hx⟩ := K_unbounded (2 ^ n)
  refine ⟨x, ?_⟩
  rw [KP_eq, plen]
  have hs : n < Nat.size (K x + 1) := by rw [Nat.lt_size]; omega
  omega

/-- `plenc = plen ∘ encode` is computable: `Nat.size` is computable (`computable_nat_size`),
composed with `· + 1` and `2 * ·`. -/
theorem computable_plenc : Computable plenc := by
  have hsize : Computable (fun m : ℕ => Nat.size (m + 1)) :=
    computable_nat_size.comp Primrec.succ.to_comp
  have hmul : Computable (fun m : ℕ => 2 * Nat.size (m + 1)) :=
    (Primrec.nat_mul.comp (Primrec.const 2) Primrec.id).to_comp.comp hsize
  exact hmul.comp Computable.encode

-- Mark `plenc` irreducible for the Berry proof: otherwise `whnf` unfolds it through `Nat.size`'s
-- `binaryRec` and loops during `Computable` unification (cf. `KolmogorovBitlen.codelen'`).
attribute [local irreducible] plenc

/-- **Uncomputability of prefix-free Kolmogorov complexity** `KP`. The same Kleene-`fixed_point₂`
Berry argument as `K_bitlen_not_computable`: were `KP` computable, a self-referential program `c₀`
would output the least `x` with `plenc c₀ < KP x`, forcing `KP x ≤ plenc c₀ < KP x`. -/
theorem KP_not_computable : ¬ Computable KP := by
  intro hK
  have hplenc : Computable plenc := computable_plenc
  have hlt : Computable fun p : ℕ × ℕ => decide (p.1 < p.2) := by
    have hpr := Primrec.nat_lt.choose_spec.to_comp
    have heq : (fun a : ℕ × ℕ => @decide _ (Primrec.nat_lt.choose a)) =
        fun p : ℕ × ℕ => decide (p.1 < p.2) := by funext a; congr 1
    rw [← heq]; exact hpr
  have hg : Computable fun r : (Code × ℕ) × ℕ => decide (plenc r.1.1 < KP r.2) := by
    have c1 : Computable fun r : (Code × ℕ) × ℕ => plenc r.1.1 :=
      hplenc.comp (Computable.fst.comp Computable.fst)
    have c2 : Computable fun r : (Code × ℕ) × ℕ => KP r.2 := hK.comp Computable.snd
    exact hlt.comp (c1.pair c2)
  have hf : Partrec₂ (fun (c : Code) (_ : ℕ) =>
      Nat.rfind fun x => Part.some (decide (plenc c < KP x))) :=
    Partrec.rfind (p := fun (q : Code × ℕ) (x : ℕ) =>
      Part.some (decide (plenc q.1 < KP x))) hg.partrec
  obtain ⟨c₀, hc₀⟩ := fixed_point₂ hf
  obtain ⟨x₀, hx₀⟩ := KP_unbounded (plenc c₀)
  set p₀ : ℕ →. Bool := fun x => Part.some (decide (plenc c₀ < KP x)) with hp₀
  have heval : c₀.eval 0 = Nat.rfind p₀ := by rw [hc₀]
  have hdom : (Nat.rfind p₀).Dom := by
    rw [Nat.rfind_dom]
    exact ⟨x₀, by simp [hp₀, hx₀], fun {m} _ => trivial⟩
  set w : ℕ := (Nat.rfind p₀).get hdom with hw
  have hwspec : plenc c₀ < KP w := by
    have h : true ∈ p₀ w := Nat.rfind_spec (Part.get_mem hdom)
    simpa [hp₀] using h
  have hcomp : Computes c₀ w := by
    rw [Computes, heval]
    exact Part.get_eq_iff_eq_some.mp hw.symm
  exact absurd (KP_le hcomp) (not_le.mpr hwspec)

end PrefixComplexity
