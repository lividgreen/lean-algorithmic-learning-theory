/-
Copyright (c) 2026 Mykola Palamarchuk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mykola Palamarchuk
-/
module

public import ALT.SerializationParse

-- Formal-check file, not Mathlib-destined: opt out of the house-style header linter.
set_option linter.style.header false

/-!
# `KB`'s invariance under computable maps ([Discovery] §1.1, [Inevitability] §6)

Provenance: [Discovery] §1.1's universal-machine invariance, over the prefix complexity `KB` of
`ALT/PrefixMachine.lean` in place of the additive measure `KE` `ALT/PrefixInvariance.lean`
already carries. [Inevitability] §6 Remark 6.19 consumes this statement as one of two leaf
hypotheses of `DeepLadder.prefixChaitinLadder_not_uniform_of` (`ALT/ChaitinPrefixLadder.lean`).

## What this establishes
* `univPrefix`, `univPrefix_eval`: the universal prefix machine, as a `Code`, extracted from
  universality over `EParserSpec`'s concrete witness `AdditiveComplexity.parseE` — run a
  description's serialized machine and trailing argument through `PrefixMachine.pfy`.
* `univPrefix_spec`: `univPrefix` reproduces `pfy d` on any serialized-machine-plus-argument
  description `E d ++ q`.
* `prefixFree_univPrefix_dom`: `univPrefix`'s own halting domain, read as bit-strings, is
  prefix-free — the same argument `KolmogorovComplexity.chaitin_bound_KB_of` makes for its own
  self-referential machine, here for `univPrefix` alone.
* `KB_partial_map_le` — **`KB`'s invariance under PARTIAL computable maps**: for `f : ℕ →. ℕ`
  with `hf : Partrec f`, `∃ c, ∀ x y, y ∈ f x → KB y ≤ KB x + c`. `Nat.Partrec.Code.exists_code`
  already gives a code `cf` with `cf.eval = f` outright, so no totality step is needed before
  composing `cf` with `univPrefix`: the composed machine's halting domain is contained in
  `univPrefix`'s, hence prefix-free too, so `pfy` reproduces its `eval` exactly and
  `PrefixMachine.KB_le` applies directly.
* `KB_map_le` — **`KB`'s invariance under (total) computable maps**, now a corollary of
  `KB_partial_map_le` at `f`'s total-to-partial coercion: for a computable `f : ℕ → ℕ`,
  `∃ c, ∀ x, KB (f x) ≤ KB x + c`.

## What this does NOT establish (flagged)
* The constant `c` is uniform in `f` only through the fixed code `univPrefix`; it still depends
  on `f`'s own code `cf` (`elen cf`), exactly as any two-machine invariance constant must — for
  both `KB_partial_map_le` and `KB_map_le`.
-/


@[expose] public section

namespace PrefixMachine

open Nat.Partrec Nat.Partrec.Code AdditiveComplexity CodeEvalLaws

/-! ## The universal prefix machine, as a code -/

/-- The universal prefix machine's simulation step is partial recursive. -/
theorem partrec_univPrefixFn :
    Nat.Partrec (fun m : ℕ => (parseE (natToBits m) : Part (Code × List Bool)).bind
      fun dq => pfy dq.1 (bitsToNat dq.2)) := by
  have hparseNB : Primrec fun m : ℕ => parseE (natToBits m) :=
    primrec_parseE.comp primrec_natToBits
  have hstage1 : Partrec fun m : ℕ => (parseE (natToBits m) : Part (Code × List Bool)) :=
    Computable.ofOption hparseNB.to_comp
  have hmap : Primrec fun p : ℕ × (Code × List Bool) => (p.2.1, bitsToNat p.2.2) :=
    (Primrec.fst.comp Primrec.snd).pair (primrec_bitsToNat.comp (Primrec.snd.comp Primrec.snd))
  have hg1 : Partrec₂ (fun (_ : ℕ) (dq : Code × List Bool) => pfy dq.1 (bitsToNat dq.2)) :=
    (Partrec.comp pfy_partrec hmap.to_comp).of_eq fun _ => rfl
  exact Partrec.nat_iff.mp ((Partrec.bind hstage1 hg1).of_eq fun _ => rfl)

/-- **The universal prefix machine, as a code.** Parses a description's serialized machine `d`
and trailing argument `q` off any input (read as bits), then runs `d` on `q` through `pfy`. -/
noncomputable def univPrefix : Code :=
  Classical.choose (exists_code.mp partrec_univPrefixFn)

theorem univPrefix_eval :
    univPrefix.eval = fun m : ℕ =>
      (parseE (natToBits m) : Part (Code × List Bool)).bind fun dq => pfy dq.1 (bitsToNat dq.2) :=
  Classical.choose_spec (exists_code.mp partrec_univPrefixFn)

/-- **`univPrefix` reproduces `pfy d`** on any serialized-machine-plus-argument description
`E d ++ q`. -/
theorem univPrefix_spec (d : Code) (q : List Bool) :
    univPrefix.eval (bitsToNat (E d ++ q)) = pfy d (bitsToNat q) := by
  have heval := congrFun univPrefix_eval (bitsToNat (E d ++ q))
  rw [natToBits_bitsToNat] at heval
  have hparse : (parseE (E d ++ q) : Part (Code × List Bool)) = Part.some (d, q) := by
    rw [Part.eq_some_iff, Part.mem_ofOption]
    exact parseE_E_append d q
  rw [hparse, Part.bind_some] at heval
  exact heval

/-- Any input `univPrefix` halts on decodes, through `parseE`, to a serialized machine `d` and
an argument `q` genuinely in `pfy d`'s domain. -/
private theorem univPrefix_decomp {m : ℕ} (hm : m ∈ univPrefix.eval.Dom) :
    ∃ (d : Code) (q : List Bool), natToBits m = E d ++ q ∧ q ∈ natToBits '' (pfy d).Dom := by
  obtain ⟨v, hv⟩ := Part.dom_iff_mem.mp hm
  rw [congrFun univPrefix_eval m] at hv
  obtain ⟨dq, hdq, hBdq⟩ := Part.mem_bind_iff.mp hv
  have hparse_eq : parseE (natToBits m) = some dq := Part.mem_ofOption.mp hdq
  have hspec : natToBits m = E dq.1 ++ dq.2 := parseE_eq_some (natToBits m) dq.1 dq.2 hparse_eq
  refine ⟨dq.1, dq.2, hspec, ?_⟩
  have hbcdom : bitsToNat dq.2 ∈ (pfy dq.1).Dom := Part.dom_iff_mem.mpr ⟨v, hBdq⟩
  exact ⟨bitsToNat dq.2, hbcdom, natToBits_bitsToNat _⟩

/-- **`univPrefix`'s own halting domain, read as bit-strings, is prefix-free.** Two accepted
inputs decompose (`univPrefix_decomp`) to serialized machines and arguments; a prefix relation
between them forces the same machine (`E_append_inj`) and then the same argument
(`pfy_prefixFree`). -/
theorem prefixFree_univPrefix_dom : PrefixFree (natToBits '' univPrefix.eval.Dom) := by
  intro p₁ hp₁ p₂ hp₂ hpre
  obtain ⟨m₁, hm₁, rfl⟩ := hp₁
  obtain ⟨m₂, hm₂, rfl⟩ := hp₂
  obtain ⟨d₁, q₁, heq₁, hq₁⟩ := univPrefix_decomp hm₁
  obtain ⟨d₂, q₂, heq₂, hq₂⟩ := univPrefix_decomp hm₂
  rw [heq₁, heq₂] at hpre ⊢
  obtain ⟨r, hr⟩ := hpre
  rw [List.append_assoc] at hr
  obtain ⟨hd, hqr⟩ := E_append_inj d₁ d₂ (q₁ ++ r) q₂ hr
  subst hd
  have hq12 : q₁ = q₂ := pfy_prefixFree d₁ q₁ hq₁ q₂ hq₂ ⟨r, hqr⟩
  rw [hq12]

/-! ## `KB`'s invariance under computable maps -/

/-- Composing any code `cf` after `univPrefix` never halts on more inputs than `univPrefix`
alone: `comp cf univPrefix`'s eval law is a bind over `univPrefix.eval` first. -/
private theorem dom_comp_univPrefix_subset (cf : Code) :
    (comp cf univPrefix).eval.Dom ⊆ univPrefix.eval.Dom := by
  intro n hn
  obtain ⟨v, hv⟩ := Part.dom_iff_mem.mp hn
  have hv' : v ∈ univPrefix.eval n >>= cf.eval := hv
  obtain ⟨u, hu, -⟩ := Part.mem_bind_iff.mp hv'
  exact Part.dom_iff_mem.mpr ⟨u, hu⟩

private theorem prefixFree_comp_univPrefix_dom (cf : Code) :
    PrefixFree (natToBits '' (comp cf univPrefix).eval.Dom) := by
  intro p hp q hq hpq
  obtain ⟨m, hm, rfl⟩ := hp
  obtain ⟨m', hm', rfl⟩ := hq
  exact prefixFree_univPrefix_dom (natToBits m) ⟨m, dom_comp_univPrefix_subset cf hm, rfl⟩
    (natToBits m') ⟨m', dom_comp_univPrefix_subset cf hm', rfl⟩ hpq

/-- **`KB`'s invariance under partial computable maps.** Applying a `Partrec` partial `f` to any
`x, y` with `y ∈ f x` costs only `f`'s own code's length plus `univPrefix`'s, plus `O(1)`:
`KB y ≤ KB x + c`. `exists_code` gives a code `cf` with `cf.eval = f` outright — no totality step
is needed, unlike `KB_map_le`'s original route through a total `f`. Take the `KB`-optimal
description `(d, q)` for `x` (`exists_min_KB`) and compose `cf` with `univPrefix`: `comp cf
univPrefix` outputs `y` on `E d ++ q`'s bits (`univPrefix_spec`, then
`CodeEvalLaws.eval_comp_some`), and its domain is prefix-free (`prefixFree_comp_univPrefix_dom`,
a subset of `univPrefix`'s own), so `pfy` reproduces it exactly and `KB_le` applies. -/
theorem KB_partial_map_le (f : ℕ →. ℕ) (hf : Partrec f) :
    ∃ c, ∀ x y, y ∈ f x → KB y ≤ KB x + c := by
  obtain ⟨cf, hcf⟩ := exists_code.mp (Partrec.nat_iff.mp hf)
  refine ⟨elen cf + elen univPrefix + 3, fun x y hxy => ?_⟩
  obtain ⟨d, q, hdq, hlen⟩ := exists_min_KB x
  have hux : univPrefix.eval (bitsToNat (E d ++ q)) = Part.some x := by
    rw [univPrefix_spec]
    exact Part.eq_some_iff.mpr hdq
  have hcx : cf.eval x = Part.some y := (congrFun hcf x).trans (Part.eq_some_iff.mpr hxy)
  have hval : (comp cf univPrefix).eval (bitsToNat (E d ++ q)) = Part.some y :=
    (eval_comp_some hux).trans hcx
  have hpf : PrefixFree (natToBits '' (comp cf univPrefix).eval.Dom) :=
    prefixFree_comp_univPrefix_dom cf
  have hpfy_eq : pfy (comp cf univPrefix) = (comp cf univPrefix).eval :=
    pfy_eq_of_prefixFree _ hpf
  have hmem : y ∈ pfy (comp cf univPrefix) (bitsToNat (E d ++ q)) := by
    rw [hpfy_eq, hval]
    exact Part.mem_some _
  have hKBle : KB y ≤ elen (comp cf univPrefix) + (E d ++ q).length := KB_le hmem
  have hlen1 : elen (comp cf univPrefix) = 3 + elen cf + elen univPrefix := E_len_comp cf univPrefix
  have hlen2 : (E d ++ q).length = elen d + q.length := by simp [elen]
  rw [hlen1, hlen2] at hKBle
  omega

/-- **`KB`'s invariance under computable maps**, a corollary of `KB_partial_map_le` at `f`'s
total-to-partial coercion (`Part.mem_some` witnesses `f x ∈ (↑f) x`). -/
theorem KB_map_le (f : ℕ → ℕ) (hf : Computable f) : ∃ c, ∀ x, KB (f x) ≤ KB x + c := by
  obtain ⟨c, hc⟩ := KB_partial_map_le (f : ℕ →. ℕ) hf.partrec
  exact ⟨c, fun x => hc x (f x) (Part.mem_some _)⟩

end PrefixMachine
