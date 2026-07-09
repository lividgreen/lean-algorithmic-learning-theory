import Mathlib
import ALT.KolmogorovComplexity

-- Tier-1 formal check, not Mathlib-destined: opt out of the house-style header linter.
set_option linter.style.header false

/-!
# Time-bounded Kolmogorov complexity + bit-length refinement (D3 Slice 2)

Provenance: `03_polynomial_convergence_under_SQ.md`, §2.1 (time-bounded Kolmogorov complexity) and
§2.2 (Prop 2.2, the deterministic bridge); `02_mdl_dominance_and_discovery.md`, §1.1 (`r = K(R)`,
"program length in bits"). Extends `ALT/KolmogorovComplexity.lean` (Slice 1: `codelen`,
`Computes`, `K`, `K_le`, `exists_min_code`, `K_unbounded`, `K_not_computable`).

Status: PROVED. Slice 2 adds the time-bounded measure and the bit-length value-reconnection.

## `K_t` is classical time-bounded K — NOT the epiplexity functional `S_T`
`K_t` below is **classical time-bounded Kolmogorov complexity**: the least program length over
*deterministic* codes outputting a fixed `x` within a step budget. This is distinct from Paper III
§2.1's **epiplexity** `S_T(X) := |P*|`, `P* = argmin_{P ∈ P_T} { |P| + E_X[log(1/P(X))] }`, which
minimizes description length **plus expected log-loss** over **probabilistic** programs for a random
variable `X` (the `H_T` residual-entropy term). `S_T`/epiplexity is a distinct, load-bearing notion
across the project and stays OUT of scope here.

The honest bridge is Proposition 2.2: for a *deterministic* rule the `H_T` term vanishes (exact
prediction ⇒ `E[log 1/P] → 0`), so `S_T` reduces to the `|P|` component, ≈ time-bounded K. So `K_t`
faithfully renders the `|P|` part of `S_T` in the deterministic regime — not `S_T` itself.

## What this DOES establish
* `K_t`: time-bounded (least-index) Kolmogorov complexity — least program length over codes
  outputting `x` from input `0` within `t` `evaln`-steps; `⊤ : ℕ∞` if none halts in budget `t`.
* `K_le_K_t`, `K_t_antitone`, `K_t_eventually`: `K ≤ K_t`; antitone in the budget; and `K_t = K`
  for all large enough budgets (the optimal program halts in finite time).
* `K_bitlen` (= the paper's `r` in *bits*) with `K_bitlen_eq : K_bitlen x = Nat.size (K x)` — the
  precise reconnection to Slice-1's index `K` (same minimizer; `Nat.size` monotone) — and
  `K_bitlen_unbounded`.

## What this does NOT establish (flagged)
* Does NOT reconnect `K`/`K_t`/`K_bitlen` to the abstract `r`/`K` reals of the other files
  (CapacityThreshold/MDLDominance/…) — `K_bitlen` reconnects the *measure* to bit-length, but
  substituting it for those files' abstract variables is a separate later step.
* `K_t` is the program-length part, NOT the §2.1 epiplexity functional `S_T = |P*|` (probabilistic
  programs + `E[log 1/P]`); see the note above.
* `K_t` uses the *index* `codelen` (consistent with Slice-1 `K`), so it inherits Slice 1's
  index-vs-bit-length caveat; the paper's `|P|` is in bits. A bit-length time-bounded version
  `Nat.size ∘ K_t` is DEFERRED (alongside the other bit-length items).
* `K_bitlen_not_computable` is DEFERRED — it needs `Computable Nat.size`, absent from Mathlib
  (would need a `Primrec Nat.size` detour); Slice 1's `K_not_computable` already lands the
  uncomputability headline, and `K_bitlen = Nat.size ∘ K` differs only by a computable monotone map.
  Two-machine invariance is also DEFERRED.
* NOT the structure function (§2.3); NOT the SQ framework.

## Hypotheses: paper-stated vs added
* Paper-stated / faithful: time-bounded complexity + monotonicity/limit; bit-length `r`; `= ∞` on
  empty budget.
* Added / modeling: `t` = `evaln` step-count as the budget; `ℕ∞`/`⊤` rendering; least-**index**
  still underlies `K` (bit-length is `Nat.size` of it).
-/

namespace KolmogorovComplexity

open Nat.Partrec Nat.Partrec.Code

/-- Code-lengths of programs outputting `x` from input `0` within `t` steps (`evaln`). -/
def tCodelens (t x : ℕ) : Set ℕ := { l | ∃ c, x ∈ Code.evaln t c 0 ∧ codelen c = l }

/-- Time-bounded (least-index) Kolmogorov complexity (Paper III §2.1): least program length over
codes that output `x` from input `0` within `t` `evaln`-steps; `⊤` if none halts in budget `t`.

This is *classical* time-bounded K — the deterministic `|P|` component of §2.1's epiplexity `S_T`
(which additionally has the probabilistic `E[log 1/P]` term); see the module note. -/
noncomputable def K_t (t x : ℕ) : ℕ∞ := sInf ((Nat.cast : ℕ → ℕ∞) '' tCodelens t x)

/-- More compute never hurts the unbounded bound: `K x ≤ K_t t x` — the `t`-bounded programs are a
sub-collection of all programs (`evaln_sound`). -/
theorem K_le_K_t (t x : ℕ) : (K x : ℕ∞) ≤ K_t t x := by
  apply le_sInf
  rintro _ ⟨_, ⟨c, hev, rfl⟩, rfl⟩
  exact_mod_cast K_le (Part.eq_some_iff.mpr (evaln_sound hev))

/-- Antitone in the budget: more steps ⇒ no larger `K_t` (more programs qualify, `evaln_mono`). -/
theorem K_t_antitone {t₁ t₂ : ℕ} (h : t₁ ≤ t₂) (x : ℕ) : K_t t₂ x ≤ K_t t₁ x := by
  apply sInf_le_sInf
  apply Set.image_mono
  rintro l ⟨c, hev, rfl⟩
  exact ⟨c, evaln_mono h hev, rfl⟩

/-- Eventually meets the unbounded `K`: the optimal program halts in finite time, so for every
budget at least that, `K_t t x = K x`. -/
theorem K_t_eventually (x : ℕ) : ∃ T, ∀ t, T ≤ t → K_t t x = (K x : ℕ∞) := by
  obtain ⟨c, hcomp, hlen⟩ := exists_min_code x
  obtain ⟨T, hT⟩ := evaln_complete.1 (Part.eq_some_iff.mp hcomp)
  refine ⟨T, fun t ht => le_antisymm ?_ (K_le_K_t t x)⟩
  -- `c` halts within budget `t ≥ T`, so its length `K x` is in the budget-`t` set.
  apply csInf_le'
  exact ⟨codelen c, ⟨c, evaln_mono ht hT, rfl⟩, by rw [hlen]⟩

/-- Bit-length program measure: `Nat.size (encode c)` — the paper's `r` in *bits* (§1.1),
vs Slice-1's `codelen = encode c` (index). -/
def codelen' (c : Code) : ℕ := Nat.size (codelen c)

/-- Bit-length Kolmogorov complexity. -/
noncomputable def K_bitlen (x : ℕ) : ℕ := sInf { l | ∃ c, Computes c x ∧ codelen' c = l }

/-- Value-reconnection: the bit-length complexity is exactly `Nat.size` of Slice-1's index `K`
(same minimizer — `Nat.size` is monotone; value = bit-length of the index). This is the precise
"paper-`r` = `Nat.size ∘` (index-`K`)" link flagged in Slice 1. -/
theorem K_bitlen_eq (x : ℕ) : K_bitlen x = Nat.size (K x) := by
  apply le_antisymm
  · -- the K-minimizing code witnesses `Nat.size (K x)` in the bit-length set
    obtain ⟨c, hcomp, hlen⟩ := exists_min_code x
    exact Nat.sInf_le ⟨c, hcomp, by simp [codelen', hlen]⟩
  · -- `Nat.size (K x)` lower-bounds the bit-length set (size monotone, `K x ≤ codelen c`)
    apply le_csInf
    · exact ⟨codelen' (Code.const x), Code.const x, const_computes x, rfl⟩
    · rintro l ⟨c, hcomp, rfl⟩
      exact Nat.size_le_size (K_le hcomp)

/-- `K_bitlen` is unbounded (incompressible objects in bits too). -/
theorem K_bitlen_unbounded (n : ℕ) : ∃ x, n < K_bitlen x := by
  obtain ⟨x, hx⟩ := K_unbounded (2 ^ n)
  refine ⟨x, ?_⟩
  rw [K_bitlen_eq, Nat.lt_size]
  exact le_of_lt hx

end KolmogorovComplexity
