/-
Copyright (c) 2026 Mykola Palamarchuk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mykola Palamarchuk
-/
import Mathlib
import ALT.BinaryConstant
import ALT.PrefixComplexity

-- Formal-check file, not Mathlib-destined: opt out of the house-style linters.
set_option linter.style.header false
set_option linter.style.longLine false

/-!
# Two-machine invariance of the Paper II prior complexity (P-II item 2; FV-AC ported)

Provenance: Paper II §1.1 — `K(R) = r` "relative to a fixed universal
reference machine `U_ref`", with the explicit caveat *"Invariance-constant caveats apply; we assume
`r` is large enough that the reference-machine dependence is a lower-order correction."* This file
formalizes that caveat as the **two-machine (interpreter) invariance** of the additive program-length
complexity underlying the `w(R') ∝ 2^{−K(R')}` prior.

## Carrier verdict (probe-first): the ADDITIVE measure `KE`, not the index measure `KP`

Two candidate carriers were probed:
* **(a) the existing prefix measure `KP`** (`PrefixComplexity.KP x = 2·Nat.size (K x + 1)`, the
  self-delimiting *index* bit-length). **Walled.** `KP` measures the Gödel index `encode c`, and
  Mathlib's `encodeCode (comp cf cg) = 2·(2·Nat.pair (encode cf) (encode cg) + 1) + 4` pairs children
  with the quadratic `Nat.pair`, so `Nat.size (encode (comp cf cg)) = 2·max (size cf) (size cg) + O(1)`
  and hence `KP` is *multiplicative* (factor 2) **even at `comp`**: no additive
  `KP (I⟦x⟧) ≤ KP x + O(1)` exists. The additive-compose target is provably
  unreachable on `KP`.
* **(b) the additive serialization measure `KE`** (`AdditiveComplexity.KE`, over the 3-bit Polish
  length `elen`, additive by construction: `elen (comp cf cg) = 3 + elen cf + elen cg`). Here the
  additive-compose bound is native. **Chosen.**

So the invariance is carried by `KE` (Paper III's additive measure) — the ONLY carrier on which the
additive form is true. The `2^{−KP}` prior itself (`PrefixComplexity.kraft_prior`) is unchanged and
remains the semimeasure. **Full unification** — a `KE`-based prior semimeasure `∑_x 2^{−KE x} ≤ 1`
(`kraft_KP_E`) plus a `KP_E ↔ KP` comparison — is **not** a clean transfer and is deliberately NOT
shipped: `kraft_plen`'s Elias telescoping is specific to `plen`; `∑_c 2^{−elen c} ≤ 1` needs the
*deferred* unique-decodability of the Polish `E` code (a separate mini-development); and `elen` vs
`plen ∘ encode` live on incomparable scales (`elen` is ≈ the log of the index bit-length). Left as a
documented follow-on rather than forced.

## What this establishes
* `computes_comp`: the compose eval law in `Computes` form (interpreter `I` run on a program `c`).
* `KE_interp_le` — **additive two-machine invariance (compose-method)**: for an interpreter `I` with
  `I.eval x = x'`, `KE x' ≤ KE x + elen I + 3`. The interpreter costs only its own additive length
  plus `O(1)`; **no size-of-data term** (contrast the general case below).
* `prior_weight_machine_indep_compose` — **§1.1 fidelity corollary**: the prior weight is
  machine-independent up to the fixed multiplicative constant `2^{−(elen I + 3)} = 2^{−O(1)}` for a
  compose-interpreter `I`: `2^{−KE x} · 2^{−(elen I + 3)} ≤ 2^{−KE x'}`.

The **general-method** case (an arbitrary description method reading its argument as a *number*) is
`AdditiveComplexity.invariance_general`: `d.eval p = x ⟹ KE x ≤ elen d + κ·Nat.size p + (3 + κ)`
(`κ = 15 + elen dbl`) — κ-**multiplicative** in the data size, because hardcoding the datum `p` costs
a binary constant of additive length `O(Nat.size p)`. This is the honest FV-AC dichotomy: additive
for a program composed as *code*, multiplicative-in-size for data read as a *number*. The additive
form for arbitrary methods is barred by the same run-on-`0` / AST-data model feature documented there.

## Boundary (the index-measure wall)
Additive two-machine invariance of the **index** measure `KP` remains barred by `encodeCode`'s
quadratic pairing (above) — the reason this item is carried by `KE`. `kraft_KP_E` and the
`KP_E ↔ KP` comparison are not shipped (not a clean transfer; see the carrier verdict).
-/

namespace PrefixInvariance

open Nat.Partrec Nat.Partrec.Code KolmogorovComplexity AdditiveComplexity
open scoped ENNReal

/-- Compose eval law in `Computes` form: if program `c` outputs `x` from input `0` and interpreter
`I` maps `x ↦ x'`, then `comp I c` outputs `x'` from input `0`
(`eval (comp I c) 0 = eval c 0 >>= eval I`). -/
theorem computes_comp {I c : Code} {x x' : ℕ}
    (hc : Computes c x) (hI : I.eval x = Part.some x') : Computes (comp I c) x' := by
  rw [Computes] at hc ⊢
  change c.eval 0 >>= I.eval = Part.some x'
  rw [hc]
  exact (Part.bind_some x I.eval).trans hI

/-- **Additive two-machine invariance (compose-method).** For an interpreter `I` with
`I.eval x = x'`, applying `I` to `x` costs only `I`'s own additive length plus `O(1)`:
`KE x' ≤ KE x + elen I + 3`. Take the `KE`-optimal program `cx` for `x` (`exists_min_E`) and compose
`I` with it (`computes_comp`); `KE_comp_le` on `comp I cx` gives
`KE x' ≤ elen I + elen cx + 3 = KE x + elen I + 3`. The absence of any `Nat.size`-of-data term is
exactly what the additive carrier buys — contrast `AdditiveComplexity.invariance_general`, whose
`κ·Nat.size p` is the price of reading the argument as a number. -/
theorem KE_interp_le (I : Code) (x x' : ℕ) (hI : I.eval x = Part.some x') :
    KE x' ≤ KE x + elen I + 3 := by
  obtain ⟨cx, hcx, hlx⟩ := exists_min_E x
  have hcomp : Computes (comp I cx) x' := computes_comp hcx hI
  have hle := KE_comp_le hcomp
  rw [hlx] at hle
  omega

/-- **§1.1 fidelity: machine-independence of the prior weight (compose-interpreters).** The prior
weight `2^{−KE}` changes by at most the fixed factor `2^{−(elen I + 3)} = 2^{−O(1)}` under a
compose-interpreter `I` (`I.eval x = x'`): `2^{−KE x} · 2^{−(elen I + 3)} ≤ 2^{−KE x'}`. This is
exactly §1.1's "`K(R) = r` up to the reference-machine constant, a lower-order correction": the prior
is machine-independent up to a multiplicative `2^{−O(1)}` for compose-interpreters. Immediate from
`KE_interp_le` and the antitonicity of `a ↦ (2⁻¹)^a` on `ℝ≥0∞` (`2⁻¹ ≤ 1`, `pow_le_pow_of_le_one`). -/
theorem prior_weight_machine_indep_compose (I : Code) (x x' : ℕ)
    (hI : I.eval x = Part.some x') :
    (2⁻¹ : ℝ≥0∞) ^ (KE x) * (2⁻¹ : ℝ≥0∞) ^ (elen I + 3) ≤ (2⁻¹ : ℝ≥0∞) ^ (KE x') := by
  have h : KE x' ≤ KE x + (elen I + 3) := by have := KE_interp_le I x x' hI; omega
  rw [← pow_add]
  exact pow_le_pow_of_le_one (by positivity) (ENNReal.inv_le_one.mpr one_le_two) h

end PrefixInvariance
