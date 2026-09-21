/-
Copyright (c) 2026 Mykola Palamarchuk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mykola Palamarchuk
-/
module

public import ALT.CodingTheoremDecoder
public import ALT.ChaitinPrefixLadder
public import ALT.PrefixInvarianceKB

-- Formal-check file, not Mathlib-destined: opt out of the house-style header linter.
set_option linter.style.header false

/-!
# `KB`'s Elias bound: the prefix-Chaitin ladder's rate ([Discovery] §1.1, [Inevitability] §6)

Provenance: [Discovery] §1.1's `KB` (FV-20) and its Elias-γ encoding overhead. [Inevitability] §6
Remark 6.19 consumes this statement as one of two leaf hypotheses of
`DeepLadder.prefixChaitinLadder_not_uniform_of` (`ALT/ChaitinPrefixLadder.lean`).

## What this establishes

* `eliasDecoder`: a `Code` parsing an input's `gammaCode`/`bitsFixed` structure
  (`ALT/CodingTheoremDecoder.lean`'s `parseBits`) and outputting the encoded value directly.
* `prefixFree_eliasDecoder_dom`: its halting domain, read as bit-strings, is prefix-free.
* `KB_le_size_add_two_mul_size_size` — **`KB`'s Elias bound, unabsorbed**: `∃ c, ∀ n, KB n ≤
  Nat.size n + 2 * Nat.size (Nat.size n) + c` — the same self-delimiting description, one step
  before its two bit-length terms are absorbed together.
* `KB_le_two_mul_size` — **`KB`'s Elias bound**, now a corollary of the unabsorbed bound at
  `two_mul_size_size_le`: `∃ c, ∀ n, KB n ≤ 2 * Nat.size n + c` — every natural has a
  self-delimiting description on the prefix machine at twice its own bit-length plus a constant,
  the Elias-γ overhead over a fixed-width binary block.
* `DeepLadder.prefixChaitinLadder_not_uniform`, `..._nonvacuous`: the ladder's non-uniformity
  theorem, put together from `PrefixMachine.KB_map_le` and `KB_le_two_mul_size`, and its
  non-vacuity witness at `𝗣𝗔⁻`.

## What this does NOT establish (flagged)

* The `O(1)` coding theorem (`ALT/CodingTheoremDecoder.lean`'s own boundary) is unrelated to and
  unaffected by this bound.
-/


@[expose] public section

namespace PrefixMachine

open Nat.Partrec Nat.Partrec.Code AdditiveComplexity

/-! ## The Elias decoder, as a code -/

private theorem primrec_eliasDecoderFn :
    Primrec fun m : ℕ => (parseBits (natToBits m)).map Prod.snd :=
  Primrec.option_map (primrec_parseBits.comp primrec_natToBits) (Primrec.snd.comp Primrec.snd)

/-- The Elias decoder's underlying partial function is partial recursive. -/
theorem partrec_eliasDecoderFn :
    Nat.Partrec (fun m : ℕ => (((parseBits (natToBits m)).map Prod.snd : Option ℕ) : Part ℕ)) :=
  Partrec.nat_iff.mp (Computable.ofOption primrec_eliasDecoderFn.to_comp)

/-- **The Elias decoder, as a code.** Parses an input's bit-string as `gammaCode k ++ bitsFixed k i`
(`ALT/CodingTheoremDecoder.lean`'s `parseBits`) and outputs `i` directly. -/
noncomputable def eliasDecoder : Code :=
  Classical.choose (exists_code.mp partrec_eliasDecoderFn)

theorem eliasDecoder_eval :
    eliasDecoder.eval =
      fun m : ℕ => (((parseBits (natToBits m)).map Prod.snd : Option ℕ) : Part ℕ) :=
  Classical.choose_spec (exists_code.mp partrec_eliasDecoderFn)

/-- **`eliasDecoder`'s own halting domain, read as bit-strings, is prefix-free.** Its domain is
contained in the parser's own domain (`eliasDecoder_eval`, `Option.map` preserving `isSome`), and
that domain is prefix-free (`ALT.CodingTheoremDecoder.prefixFree_parseBits_dom`). -/
theorem prefixFree_eliasDecoder_dom : PrefixFree (natToBits '' eliasDecoder.eval.Dom) := by
  have hsub : eliasDecoder.eval.Dom ⊆ {m : ℕ | (parseBits (natToBits m)).isSome} := by
    intro m hm
    have hv : (eliasDecoder.eval m).Dom := hm
    rw [congrFun eliasDecoder_eval m] at hv
    simpa [Part.Dom, Option.isSome_iff_exists] using hv
  intro p hp q hq hpq
  obtain ⟨m, hm, rfl⟩ := hp
  obtain ⟨m', hm', rfl⟩ := hq
  exact prefixFree_parseBits_dom (natToBits m) (hsub hm) (natToBits m') (hsub hm') hpq

/-! ## `KB`'s Elias bound -/

/-- The elementary bound `2 * Nat.size (Nat.size n) ≤ Nat.size n + 2`, tight at `n = 2, 3, 8`. -/
private theorem two_mul_size_size_le (m : ℕ) : 2 * Nat.size m ≤ m + 2 := by
  induction m using Nat.strongRecOn with
  | ind m ih =>
    match m with
    | 0 => decide
    | 1 => decide
    | 2 => decide
    | 3 => decide
    | (k + 4) =>
      have hlt : (k + 4) / 2 < k + 4 := by omega
      have hne : Nat.bit (k + 4).bodd (k + 4).div2 ≠ 0 := by
        rw [Nat.bit_bodd_div2]; omega
      have hrec : Nat.size (k + 4) = Nat.size ((k + 4) / 2) + 1 := by
        conv_lhs => rw [← Nat.bit_bodd_div2 (k + 4)]
        rw [Nat.size_bit hne, Nat.div2_val]
      have hih := ih ((k + 4) / 2) hlt
      omega

/-- **`KB`'s Elias bound, unabsorbed.** Every natural `n` has a self-delimiting description on the
prefix machine — `gammaCode (Nat.size n) ++ bitsFixed (Nat.size n) n`, decoded by `eliasDecoder` —
at its own bit-length plus twice the bit-length of that, plus a constant: the same description
`KB_le_two_mul_size` uses, one step before `two_mul_size_size_le` absorbs the two bit-length terms
together. -/
theorem KB_le_size_add_two_mul_size_size :
    ∃ c, ∀ n, KB n ≤ Nat.size n + 2 * Nat.size (Nat.size n) + c := by
  refine ⟨elen eliasDecoder + 1, fun n => ?_⟩
  set k := Nat.size n with hkdef
  have hnk : n < 2 ^ k := Nat.lt_size_self n
  set p := gammaCode k ++ bitsFixed k n with hpdef
  have hparse : parseBits p = some (k, n) := parseBits_gammaCode_bitsFixed k n hnk
  have heval : eliasDecoder.eval (bitsToNat p) = Part.some n := by
    rw [congrFun eliasDecoder_eval, natToBits_bitsToNat, hparse]
    simp
  have hpfy_eq : pfy eliasDecoder = eliasDecoder.eval :=
    pfy_eq_of_prefixFree _ prefixFree_eliasDecoder_dom
  have hmem : n ∈ pfy eliasDecoder (bitsToNat p) := by
    rw [hpfy_eq, heval]; exact Part.mem_some n
  have hKB : KB n ≤ elen eliasDecoder + p.length := KB_le hmem
  have hlen : p.length ≤ 2 * Nat.size k + 1 + k := by
    rw [hpdef, List.length_append, length_bitsFixed]
    have := length_gammaCode k
    omega
  omega

/-- **`KB`'s Elias bound**, a corollary of the unabsorbed bound `KB_le_size_add_two_mul_size_size`
at the elementary `two_mul_size_size_le`: every natural `n` has a self-delimiting description on
the prefix machine at twice its own bit-length plus a constant, the Elias-γ overhead over a
fixed-width binary block. -/
theorem KB_le_two_mul_size : ∃ c, ∀ n, KB n ≤ 2 * Nat.size n + c := by
  obtain ⟨c, hc⟩ := KB_le_size_add_two_mul_size_size
  refine ⟨c + 2, fun n => ?_⟩
  have h1 := hc n
  have h2 := two_mul_size_size_le (Nat.size n)
  omega

end PrefixMachine

namespace DeepLadder

open Nat.Partrec Nat.Partrec.Code KolmogorovComplexity AdditiveComplexity PrefixMachine
open FFL.FirstOrder FFL.FirstOrder.Arithmetic

/-! ## Assembling the ladder's non-uniformity theorem -/

/-- **No computable family of codes enumerates the ladder's theories of this form uniformly in
the rung index** — the assembly of `prefixChaitinLadder_not_uniform_of` at its two leaf
hypotheses, `PrefixMachine.KB_map_le` (`ALT/PrefixInvarianceKB.lean`) and
`PrefixMachine.KB_le_two_mul_size` above. -/
theorem prefixChaitinLadder_not_uniform (T₀ : ArithmeticTheory) (d₀ : T₀.Δ₁)
    [(𝗥₀ : ArithmeticTheory) ⪯ T₀] [ℕ↓[ℒₒᵣ] ⊧* T₀] :
    ¬ ∃ f : ℕ → Code, Computable f ∧ ∀ n a, ((f n).eval a).Dom ↔
      prefixChaitinLadder T₀ d₀ n ⊢ chaitinSentenceB (Nat.unpair a).1 (Nat.unpair a).2 :=
  prefixChaitinLadder_not_uniform_of T₀ d₀ KB_map_le KB_le_two_mul_size

/-- `prefixChaitinLadder_not_uniform`'s hypotheses are jointly met, unconditionally, at `𝗣𝗔⁻`
(mirroring `KB_enumeratorB_lt_succ_nonvacuous`). -/
theorem prefixChaitinLadder_not_uniform_nonvacuous :
    ¬ ∃ f : ℕ → Code, Computable f ∧ ∀ n a, ((f n).eval a).Dom ↔
      prefixChaitinLadder (𝗣𝗔⁻ : ArithmeticTheory) inferInstance n ⊢
        chaitinSentenceB (Nat.unpair a).1 (Nat.unpair a).2 :=
  prefixChaitinLadder_not_uniform (𝗣𝗔⁻ : ArithmeticTheory) inferInstance

end DeepLadder
