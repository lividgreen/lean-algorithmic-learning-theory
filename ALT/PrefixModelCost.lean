/-
Copyright (c) 2026 Mykola Palamarchuk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mykola Palamarchuk
-/
module

public import ALT.PrefixEliasKB
public import ALT.PrefixComplexity
public import ALT.KReconnection

-- Formal-check file, not Mathlib-destined: opt out of the house-style header linter.
set_option linter.style.header false

/-!
# The model cost on the prefix machine: `KB` at `K_bitlen`, `KP`, and `ruleComplexity`

Provenance: [Discovery] §1.1's `r` — the plain bit-length complexity `K_bitlen`
(`ALT/KolmogorovTimeBounded.lean`) — and its `U_ref`, the universal prefix machine `KB`
(`ALT/PrefixMachine.lean`, FV-20). Relates them, and the prefix complexity `KP` of FV-13
(`ALT/PrefixComplexity.lean`) and the reconnected rule complexity of `ALT/KReconnection.lean`,
none of which any landed statement connects to `KB`.

## What this establishes

Six theorems relating `KB` to `K_bitlen`, `KP`, and `ruleComplexity` — three of them over
hypotheses this module takes as given rather than proves, three unconditional corollaries
discharging every one of those hypotheses at a landed statement:

* `KB_le_K_bitlen_add_two_mul_size_of` — `KB x ≤ K_bitlen x + 2 * Nat.size (K_bitlen x) + c`, from
  a partial-map invariance for `KB` (`hinv`, stronger than the landed `PrefixMachine.KB_map_le`,
  which covers only total computable maps) and an unabsorbed Elias bound for `KB` (`helias`,
  distinct from the landed `PrefixMachine.KB_le_two_mul_size`). The route: the map
  `n ↦ (Denumerable.ofNat Code n).eval 0` is partial recursive (Mathlib's `Code.eval_part`
  composed with `Computable.ofNat` and a constant); `KolmogorovComplexity.exists_min_code` gives,
  for `x`, a code whose index is `K x` and which evaluates to `x` at that map, via
  `Denumerable.ofNat_encode`; `hinv` at that map gives `KB x ≤ KB (K x) + c₁`; `helias` at `K x`,
  rewritten along `KolmogorovComplexity.K_bitlen_eq`, gives the rest.
* `KB_le_K_bitlen_add_two_mul_size` — the first theorem's `hinv` and `helias` discharged at the
  landed `PrefixMachine.KB_partial_map_le` and `PrefixMachine.KB_le_size_add_two_mul_size_size`
  (`ALT/PrefixInvarianceKB.lean`, `ALT/PrefixEliasKB.lean`): unconditional.
* `KB_le_KP_of` — `KB x ≤ KP x + c`, from `hinv` alone (no `helias`): the same route to
  `KB x ≤ KB (K x) + c₁`, then the landed `PrefixMachine.KB_le_two_mul_size` at `K x` and
  `PrefixComplexity.KP_eq` with `Nat.size`'s monotonicity.
* `KB_le_KP` — `KB_le_KP_of`'s `hinv` discharged at the landed
  `PrefixMachine.KB_partial_map_le` (`ALT/PrefixInvarianceKB.lean`): `∃ c, ∀ x, KB x ≤ KP x + c`,
  unconditionally, needing no Elias bound at all.
* `KB_le_ruleComplexity_add_two_mul_size_of` — the first theorem at `x := Encodable.encode R`,
  since `KReconnection.ruleComplexity R` is `K_bitlen (Encodable.encode R)` by definition.
* `KB_le_ruleComplexity_add_two_mul_size` — `KB_le_ruleComplexity_add_two_mul_size_of`'s `hinv` and
  `helias` discharged the same way as `KB_le_K_bitlen_add_two_mul_size`: unconditional.

## What this does NOT establish (flagged)

* `hinv` and `helias` are hypotheses of the three `_of` theorems only, not proved here — this
  module states what follows from them, nothing about their own status. Each of the three
  unconditional corollaries discharges every hypothesis it needs at a landed statement instead.
* This is not a sharpening of `PrefixMachine.KB_le_two_mul_size`: that bound and
  `KB_le_K_bitlen_add_two_mul_size_of`'s price `x` in different currencies (bit-length of `x`
  against bit-length of `x`'s own complexity), and neither dominates the other everywhere.
* No constant here is computed: every hypothesis's own constant is existential, and every combined
  constant, the unconditional corollaries' included, is a sum of those.
-/


@[expose] public section

namespace PrefixMachine

open Nat.Partrec Nat.Partrec.Code KolmogorovComplexity PrefixComplexity KReconnection

/-- **`KB` at `K_bitlen`.** From a partial-map invariance for `KB` and an unabsorbed Elias bound
for `KB` (both hypotheses; see the module docstring), `KB x ≤ K_bitlen x + 2 * Nat.size (K_bitlen x)
+ c`. -/
theorem KB_le_K_bitlen_add_two_mul_size_of
    (hinv : ∀ f : ℕ →. ℕ, Partrec f → ∃ c, ∀ x y, y ∈ f x → KB y ≤ KB x + c)
    (helias : ∃ c, ∀ n, KB n ≤ Nat.size n + 2 * Nat.size (Nat.size n) + c) :
    ∃ c, ∀ x, KB x ≤ K_bitlen x + 2 * Nat.size (K_bitlen x) + c := by
  have hfpartrec :
      Partrec (fun n : ℕ => Nat.Partrec.Code.eval (Denumerable.ofNat Nat.Partrec.Code n) 0) :=
    Nat.Partrec.Code.eval_part.comp (Computable.ofNat Nat.Partrec.Code) (Computable.const 0)
  obtain ⟨c₁, hc₁⟩ := hinv _ hfpartrec
  obtain ⟨c₂, hc₂⟩ := helias
  refine ⟨c₁ + c₂, fun x => ?_⟩
  obtain ⟨cc, hcomp, hlen⟩ := exists_min_code x
  have hspec : Denumerable.ofNat Nat.Partrec.Code (K x) = cc := by
    rw [← hlen]; exact Denumerable.ofNat_encode cc
  have hmem : x ∈ Nat.Partrec.Code.eval (Denumerable.ofNat Nat.Partrec.Code (K x)) 0 := by
    rw [hspec]; exact Part.eq_some_iff.mp hcomp
  have hstep1 : KB x ≤ KB (K x) + c₁ := hc₁ (K x) x hmem
  have hstep2 : KB (K x) ≤ Nat.size (K x) + 2 * Nat.size (Nat.size (K x)) + c₂ := hc₂ (K x)
  rw [← K_bitlen_eq x] at hstep2
  omega

/-- **`KB` at `K_bitlen`, unconditionally.** `KB_le_K_bitlen_add_two_mul_size_of`'s `hinv` and
`helias` discharged at the landed `PrefixMachine.KB_partial_map_le` and
`PrefixMachine.KB_le_size_add_two_mul_size_size`. -/
theorem KB_le_K_bitlen_add_two_mul_size :
    ∃ c, ∀ x, KB x ≤ K_bitlen x + 2 * Nat.size (K_bitlen x) + c :=
  KB_le_K_bitlen_add_two_mul_size_of (fun f hf => KB_partial_map_le f hf)
    KB_le_size_add_two_mul_size_size

/-- **`KB` at `KP`.** From a partial-map invariance for `KB` alone (no unabsorbed Elias bound
needed — that independence is the point of stating this separately), `KB x ≤ KP x + c`. -/
theorem KB_le_KP_of
    (hinv : ∀ f : ℕ →. ℕ, Partrec f → ∃ c, ∀ x y, y ∈ f x → KB y ≤ KB x + c) :
    ∃ c, ∀ x, KB x ≤ KP x + c := by
  have hfpartrec :
      Partrec (fun n : ℕ => Nat.Partrec.Code.eval (Denumerable.ofNat Nat.Partrec.Code n) 0) :=
    Nat.Partrec.Code.eval_part.comp (Computable.ofNat Nat.Partrec.Code) (Computable.const 0)
  obtain ⟨c₁, hc₁⟩ := hinv _ hfpartrec
  obtain ⟨c₃, hc₃⟩ := KB_le_two_mul_size
  refine ⟨c₁ + c₃, fun x => ?_⟩
  obtain ⟨cc, hcomp, hlen⟩ := exists_min_code x
  have hspec : Denumerable.ofNat Nat.Partrec.Code (K x) = cc := by
    rw [← hlen]; exact Denumerable.ofNat_encode cc
  have hmem : x ∈ Nat.Partrec.Code.eval (Denumerable.ofNat Nat.Partrec.Code (K x)) 0 := by
    rw [hspec]; exact Part.eq_some_iff.mp hcomp
  have hstep1 : KB x ≤ KB (K x) + c₁ := hc₁ (K x) x hmem
  have hstep2 : KB (K x) ≤ 2 * Nat.size (K x) + c₃ := hc₃ (K x)
  have hmono : Nat.size (K x) ≤ Nat.size (K x + 1) := Nat.size_le_size (by omega)
  have hKP : KP x = 2 * Nat.size (K x + 1) := KP_eq x
  omega

/-- **`KB` at `KP`, unconditionally.** `KB_le_KP_of`'s `hinv` discharged at the landed
`PrefixMachine.KB_partial_map_le` — the partial-map invariance is exactly what this particular
corollary needs, and nothing else. -/
theorem KB_le_KP : ∃ c, ∀ x, KB x ≤ KP x + c := KB_le_KP_of fun f hf => KB_partial_map_le f hf

/-- **`KB` at `ruleComplexity`.** `KB_le_K_bitlen_add_two_mul_size_of` at `x := Encodable.encode R`,
since `ruleComplexity R = K_bitlen (Encodable.encode R)` by definition. -/
theorem KB_le_ruleComplexity_add_two_mul_size_of
    (hinv : ∀ f : ℕ →. ℕ, Partrec f → ∃ c, ∀ x y, y ∈ f x → KB y ≤ KB x + c)
    (helias : ∃ c, ∀ n, KB n ≤ Nat.size n + 2 * Nat.size (Nat.size n) + c) :
    ∃ c, ∀ R : Nat.Partrec.Code,
      KB (Encodable.encode R) ≤ ruleComplexity R + 2 * Nat.size (ruleComplexity R) + c := by
  obtain ⟨c, hc⟩ := KB_le_K_bitlen_add_two_mul_size_of hinv helias
  exact ⟨c, fun R => hc (Encodable.encode R)⟩

/-- **`KB` at `ruleComplexity`, unconditionally.** `KB_le_ruleComplexity_add_two_mul_size_of`'s
`hinv` and `helias` discharged the same way as `KB_le_K_bitlen_add_two_mul_size`. -/
theorem KB_le_ruleComplexity_add_two_mul_size :
    ∃ c, ∀ R : Nat.Partrec.Code,
      KB (Encodable.encode R) ≤ ruleComplexity R + 2 * Nat.size (ruleComplexity R) + c :=
  KB_le_ruleComplexity_add_two_mul_size_of (fun f hf => KB_partial_map_le f hf)
    KB_le_size_add_two_mul_size_size

end PrefixMachine
