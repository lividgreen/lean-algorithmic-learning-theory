/-
Copyright (c) 2026 Mykola Palamarchuk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mykola Palamarchuk
-/
import Mathlib.Data.Nat.Size
import ALT.AdditiveComplexity
import ALT.BinaryKraft
import ALT.Code.EvalLaws

-- Formal-check file, not Mathlib-destined: opt out of the house-style header linter.
set_option linter.style.header false

/-!
# A universal prefix machine: `KB`, the prefix complexity `KE` is about

Provenance: [Discovery] §1.1 ("a finite program — a binary string for `U_ref`") and FV-13.
Extends `ALT/AdditiveComplexity.lean` (`E`, `elen`, `KE`) and `ALT/BinaryKraft.lean`.

## What this establishes

A description is a machine `c : Code`, serialized by `E`, followed by a binary argument `p`; the
machine is made prefix-free the standard way (prefix-free-ification by stages) rather than assumed
so.

* `bitsToNat`, `natToBits`: a bit-string/natural bijection, `[] ↦ 0`.
* `PrefixFree`: no member of a set of bit-strings is a proper prefix of another.
* `uniquelyDecodable_of_prefixFree`, `kraft_of_prefixFree`: a prefix-free set of bit-strings is
  uniquely decodable, hence satisfies Kraft's inequality.
* `pfy`: the prefix-free-ification of a code by stages; `pfy_prefixFree`, `pfy_sub`,
  `pfy_eq_of_prefixFree`.
* `KB`: prefix complexity — least `elen c + p.length` over a serialized machine and a binary
  argument; `KB_le_KE` (`KB` is additively below `KE`); `kraft_KB` (`KB` is a semimeasure).

## What this does NOT establish (flagged)

* The algorithmic probability `QB`, its lower-semicomputability, and the coding theorem itself
  (general or instance form) are not attempted here.

`pfy_partrec` (`Partrec₂ pfy`, uniformity in `c`) — the boundary this module once flagged — is
established in `ALT/BitStringPrimrec.lean`, over the bit-string computability layer it adds.

## Hypotheses: paper-stated vs added

* Paper-stated / faithful: a universal prefix machine over binary programs, `[Discovery] §1.1`'s
  "a finite program (a binary string for `U_ref`)".
* Added / modeling: the concrete prefix-free-ification by stages (a fixed effective enumeration);
  the machine-plus-binary-argument description shape (`E c ++ p`).
-/

namespace PrefixMachine

open Nat.Partrec Nat.Partrec.Code AdditiveComplexity CodeEvalLaws KolmogorovComplexity
open scoped ENNReal

/-! ## A bit-string / natural bijection -/

/-- Bit-strings as naturals, most-significant-bit first: the number whose binary digits are
`1 :: p`, less one. `[] ↦ 0`. -/
def bitsToNat (p : List Bool) : ℕ :=
  p.foldl (fun acc b => 2 * acc + b.toNat) 1 - 1

/-- The inverse of `bitsToNat`: the bits of `n + 1`, most-significant-bit first, with the leading
`1` dropped. Well-founded recursion, peeling the low bit at each step. -/
def natToBits (n : ℕ) : List Bool :=
  if h : n + 1 < 2 then []
  else natToBits ((n + 1) / 2 - 1) ++ [decide ((n + 1) % 2 = 1)]
termination_by n
decreasing_by omega

theorem natToBits_zero : natToBits 0 = [] := by
  rw [natToBits]; simp

private theorem bitsToNat_nil : bitsToNat [] = 0 := rfl

/-- The fold underlying `bitsToNat` only ever grows the accumulator. -/
private theorem le_bitsFold (p : List Bool) (acc : ℕ) :
    acc ≤ p.foldl (fun acc b => 2 * acc + b.toNat) acc := by
  induction p generalizing acc with
  | nil => simp
  | cons b p ih => exact le_trans (by cases b <;> simp <;> omega) (ih _)

private theorem bitsToNat_append_bit (p : List Bool) (b : Bool) :
    bitsToNat (p ++ [b]) = 2 * (bitsToNat p + 1) + b.toNat - 1 := by
  simp only [bitsToNat, List.foldl_append, List.foldl_cons, List.foldl_nil]
  have hpos := le_bitsFold p 1
  omega

/-- `x ↦ x % 2` of a doubled-plus-bit quantity recovers the bit. -/
private theorem bool_toNat_mod_two (m : ℕ) (b : Bool) : (2 * m + b.toNat) % 2 = b.toNat := by
  cases b <;> simp

/-- `decide (x = 1)` recovers a bit from its `Bool.toNat`. -/
theorem bool_decide_toNat_eq_one (b : Bool) : decide (b.toNat = 1) = b := by cases b <;> rfl

theorem bitsToNat_natToBits (n : ℕ) : bitsToNat (natToBits n) = n := by
  induction n using natToBits.induct with
  | case1 n h =>
      rw [natToBits]
      simp only [dif_pos h]
      have hn0 : n = 0 := by omega
      subst hn0
      simp [bitsToNat]
  | case2 n h ih =>
      rw [natToBits]
      simp only [dif_neg h]
      rw [bitsToNat_append_bit, ih]
      have hq : (n + 1) / 2 - 1 + 1 = (n + 1) / 2 := by omega
      have hmod : (decide ((n + 1) % 2 = 1)).toNat = (n + 1) % 2 := by
        rcases Nat.mod_two_eq_zero_or_one (n + 1) with he | he <;> simp [he]
      have hdiv : 2 * ((n + 1) / 2) + (n + 1) % 2 = n + 1 := Nat.div_add_mod (n + 1) 2
      omega

theorem natToBits_bitsToNat : ∀ p : List Bool, natToBits (bitsToNat p) = p := by
  intro p
  induction p using List.reverseRecOn with
  | nil => rw [bitsToNat_nil, natToBits_zero]
  | append_singleton p b ih =>
      have hb : bitsToNat (p ++ [b]) + 1 = 2 * (bitsToNat p + 1) + b.toNat := by
        have h1 := bitsToNat_append_bit p b
        have h2 : 1 ≤ b.toNat + 2 * (bitsToNat p + 1) := by cases b <;> omega
        omega
      rw [natToBits]
      have hge2 : ¬ bitsToNat (p ++ [b]) + 1 < 2 := by omega
      simp only [dif_neg hge2]
      have hbnat : b.toNat ≤ 1 := by cases b <;> simp
      have heq1 : (bitsToNat (p ++ [b]) + 1) / 2 - 1 = bitsToNat p := by omega
      have heq2 : decide ((bitsToNat (p ++ [b]) + 1) % 2 = 1) = b := by
        have hm : (bitsToNat (p ++ [b]) + 1) % 2 = b.toNat := by
          rw [hb]; exact bool_toNat_mod_two _ b
        rw [hm]; exact bool_decide_toNat_eq_one b
      rw [heq1, heq2, ih]

theorem length_natToBits (n : ℕ) : (natToBits n).length + 1 = Nat.size (n + 1) := by
  induction n using natToBits.induct with
  | case1 n h =>
      rw [natToBits]
      simp only [dif_pos h]
      have hn0 : n = 0 := by omega
      subst hn0
      decide
  | case2 n h ih =>
      rw [natToBits]
      simp only [dif_neg h]
      simp only [List.length_append, List.length_singleton]
      have hsize : Nat.size (n + 1) = Nat.size ((n + 1) / 2) + 1 := by
        have hne : Nat.bit (n + 1).bodd (n + 1).div2 ≠ 0 := by
          rw [Nat.bit_bodd_div2]; exact Nat.succ_ne_zero n
        conv_lhs => rw [← Nat.bit_bodd_div2 (n + 1)]
        rw [Nat.size_bit hne, Nat.div2_val]
      have harg : (n + 1) / 2 - 1 + 1 = (n + 1) / 2 := by omega
      rw [harg] at ih
      omega

/-! ## Prefix-free sets are uniquely decodable

A prefix-free set of codewords (none the empty word, no member a proper prefix of another) is
uniquely decodable: the generalization of `AdditiveComplexity.uniquelyDecodable_range_E`'s peeling
argument from `E`'s range to any prefix-free set. -/

/-- No member is a proper prefix of another. (A prefix-free set containing `[]` is forced,
by this very property, down to `{[]}` — see `eq_singleton_of_nil_mem` below; unique decodability
needs the extra hypothesis `[] ∉ S` ruling that degenerate case out.) -/
def PrefixFree (S : Set (List Bool)) : Prop :=
  ∀ p ∈ S, ∀ q ∈ S, p <+: q → p = q

/-- Two codewords of a prefix-free set that prefix a common list coincide, and so do the
remainders: the peeling step behind unique decodability. -/
private theorem prefixFree_peel {S : Set (List Bool)} (h : PrefixFree S)
    {w w' r1 r2 : List Bool} (hw : w ∈ S) (hw' : w' ∈ S) (heq : w ++ r1 = w' ++ r2) :
    w = w' ∧ r1 = r2 := by
  have hww' : w = w' := by
    rcases le_total w.length w'.length with hle | hle
    · have hp : w <+: w' ++ r2 := ⟨r1, heq⟩
      exact h w hw w' hw' ((List.isPrefix_append_of_length hle).mp hp)
    · have hp : w' <+: w ++ r1 := ⟨r2, heq.symm⟩
      exact (h w' hw' w hw ((List.isPrefix_append_of_length hle).mp hp)).symm
  refine ⟨hww', ?_⟩
  rw [hww'] at heq
  exact List.append_cancel_left heq

/-- A prefix-free set containing the empty word is forced down to `{[]}`: `[]` is a prefix of
everything, so prefix-freeness identifies every member with it. -/
private theorem eq_singleton_of_nil_mem {S : Set (List Bool)} (h : PrefixFree S) (hnil : [] ∈ S) :
    S = {[]} := by
  ext q
  refine ⟨fun hq => (h [] hnil q hq List.nil_prefix).symm, fun hq => hq ▸ hnil⟩

/-- **A prefix-free set not containing the empty word is uniquely decodable.** -/
theorem uniquelyDecodable_of_prefixFree {S : Set (List Bool)} (h : PrefixFree S)
    (hnil : [] ∉ S) : InformationTheory.UniquelyDecodable S := by
  intro L₁
  induction L₁ with
  | nil =>
      rintro (_ | ⟨v, vs⟩) - h₂ hflat
      · rfl
      · exfalso
        have hv := h₂ v (by simp)
        simp only [List.flatten_nil, List.flatten_cons] at hflat
        have hv0 : v = [] := (List.append_eq_nil_iff.mp hflat.symm).1
        rw [hv0] at hv
        exact hnil hv
  | cons w ws ih =>
      rintro (_ | ⟨v, vs⟩) h₁ h₂ hflat
      · exfalso
        have hw := h₁ w (by simp)
        simp only [List.flatten_nil, List.flatten_cons] at hflat
        have hw0 : w = [] := (List.append_eq_nil_iff.mp hflat).1
        rw [hw0] at hw
        exact hnil hw
      · have hw := h₁ w (by simp)
        have hv := h₂ v (by simp)
        simp only [List.flatten_cons] at hflat
        obtain ⟨rfl, htail⟩ := prefixFree_peel h hw hv hflat
        rw [ih vs (fun x hx => h₁ x (List.mem_cons_of_mem _ hx))
              (fun x hx => h₂ x (List.mem_cons_of_mem _ hx)) htail]

/-- **Kraft's inequality for a prefix-free set of bit-strings** — including the degenerate case
`S = {[]}`, where the single term `2⁻⁰ = 1` meets the bound with equality. -/
theorem kraft_of_prefixFree {S : Set (List Bool)} (h : PrefixFree S) :
    ∑' p : S, (1 / 2 : ℝ) ^ (p : List Bool).length ≤ 1 := by
  by_cases hnil : [] ∈ S
  · have hSeq := eq_singleton_of_nil_mem h hnil
    subst hSeq
    rw [tsum_eq_single (⟨[], rfl⟩ : ({[]} : Set (List Bool)))]
    · simp
    · intro p hp
      exact absurd (Subtype.ext (Set.mem_singleton_iff.mp p.2)) hp
  · have hud := uniquelyDecodable_of_prefixFree h hnil
    simpa using BinaryKraft.indexed_tsum_le_one (fun p : S => (p : List Bool))
      Subtype.coe_injective (by simpa using hud)

/-! ## Prefix-free-ification of a code, by stages

`accepted c s` greedily accepts, at each stage, the inputs newly halting there whose bit-strings
are comparable to nothing accepted so far — the standard effective enumeration of prefix machines,
with `E c` (via `pfy`'s caller) in place of the usual index prefix. Input `0` (the empty
bit-string `[]`) is a candidate like any other: if it halts, prefix-freeness (`[]` a prefix of
everything) forces it to be the ONLY thing ever accepted, which is exactly the guard-code
construction `KB_le_KE` needs. -/

/-- Reject `n` if some element of `acc` is comparable (prefix or extension) to `n`; otherwise
append it. -/
def foldStep (acc : List ℕ) (n : ℕ) : List ℕ :=
  if ∃ m ∈ acc, natToBits m <+: natToBits n ∨ natToBits n <+: natToBits m
  then acc else acc ++ [n]

private theorem foldStep_eq_of_pos {acc : List ℕ} {n : ℕ}
    (h : ∃ m ∈ acc, natToBits m <+: natToBits n ∨ natToBits n <+: natToBits m) :
    foldStep acc n = acc := if_pos h

private theorem foldStep_eq_of_neg {acc : List ℕ} {n : ℕ}
    (h : ¬ ∃ m ∈ acc, natToBits m <+: natToBits n ∨ natToBits n <+: natToBits m) :
    foldStep acc n = acc ++ [n] := if_neg h

/-- The inputs newly halting at stage `s + 1`. -/
def newlyHalting (c : Code) (s : ℕ) : List ℕ :=
  (List.range (s + 1)).filter (fun n => (evaln (s + 1) c n).isSome && !(evaln s c n).isSome)

/-- The accepted inputs at stage `s`: greedily, by `foldStep`, over what newly halts at each
earlier stage. -/
def acceptedList (c : Code) : ℕ → List ℕ
  | 0 => []
  | s + 1 => (newlyHalting c s).foldl foldStep (acceptedList c s)

/-- `foldStep` only ever keeps or appends: nothing already present is ever removed. -/
private theorem mem_of_mem_foldStep_foldl (l : List ℕ) (acc : List ℕ) {n : ℕ} (hn : n ∈ acc) :
    n ∈ l.foldl foldStep acc := by
  induction l generalizing acc with
  | nil => simpa using hn
  | cons a l ih =>
      apply ih
      unfold foldStep
      split
      · exact hn
      · exact List.mem_append_left _ hn

/-- Anything appearing in a fold's result was either already in the accumulator or came from the
folded list. -/
private theorem mem_foldl_foldStep (l : List ℕ) (acc : List ℕ) {n : ℕ}
    (hn : n ∈ l.foldl foldStep acc) : n ∈ acc ∨ n ∈ l := by
  induction l generalizing acc with
  | nil => exact Or.inl (by simpa using hn)
  | cons a l ih =>
      rw [List.foldl_cons] at hn
      rcases ih (foldStep acc a) hn with h | h
      · unfold foldStep at h
        split at h
        · exact Or.inl h
        · rcases List.mem_append.mp h with h' | h'
          · exact Or.inl h'
          · simp only [List.mem_singleton] at h'
            exact Or.inr (h' ▸ List.mem_cons_self)
      · exact Or.inr (List.mem_cons_of_mem _ h)

/-- Once accepted, an input stays accepted at every later stage. -/
theorem acceptedList_mono {c : Code} : ∀ {s s' : ℕ}, s ≤ s' → ∀ {n : ℕ},
    n ∈ acceptedList c s → n ∈ acceptedList c s' := by
  intro s s' hs
  induction s' with
  | zero =>
      intro n hn
      have : s = 0 := by omega
      simpa [this] using hn
  | succ s' ih =>
      intro n hn
      rcases eq_or_lt_of_le hs with rfl | hlt
      · exact hn
      · have hn' : n ∈ acceptedList c s' := ih (by omega) hn
        rw [acceptedList]
        exact mem_of_mem_foldStep_foldl _ _ hn'

/-- Anything accepted at stage `s + 1` has halted by then. -/
theorem evaln_isSome_of_mem_acceptedList (c : Code) :
    ∀ s {n : ℕ}, n ∈ acceptedList c s → (evaln s c n).isSome := by
  intro s
  induction s with
  | zero => intro n hn; simp [acceptedList] at hn
  | succ s ih =>
      intro n hn
      rw [acceptedList] at hn
      rcases mem_foldl_foldStep _ _ hn with h | h
      · obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp (ih h)
        exact Option.isSome_iff_exists.mpr ⟨v, evaln_mono (Nat.le_succ s) hv⟩
      · simp only [newlyHalting, List.mem_filter, List.mem_range, Bool.and_eq_true] at h
        exact h.2.1

/-- `foldStep`, folded over any list, preserves pairwise incomparability of the accumulator. -/
private theorem foldStep_pairwise (l : List ℕ) {acc : List ℕ}
    (hacc : acc.Pairwise
      (fun m n => ¬ (natToBits m <+: natToBits n ∨ natToBits n <+: natToBits m))) :
    (l.foldl foldStep acc).Pairwise
      (fun m n => ¬ (natToBits m <+: natToBits n ∨ natToBits n <+: natToBits m)) := by
  induction l generalizing acc with
  | nil => simpa using hacc
  | cons a l ih =>
      apply ih
      by_cases hany : ∃ m ∈ acc, natToBits m <+: natToBits a ∨ natToBits a <+: natToBits m
      · rwa [foldStep_eq_of_pos hany]
      · rw [foldStep_eq_of_neg hany, List.pairwise_append]
        refine ⟨hacc, List.pairwise_singleton _ _, ?_⟩
        intro m hm a' ha'
        simp only [List.mem_singleton] at ha'
        subst ha'
        intro hcomp
        exact hany ⟨m, hm, hcomp⟩

/-- The accepted set is pairwise incomparable under prefix, at every stage. -/
private theorem acceptedList_pairwise (c : Code) (s : ℕ) :
    (acceptedList c s).Pairwise
      (fun m n => ¬ (natToBits m <+: natToBits n ∨ natToBits n <+: natToBits m)) := by
  induction s with
  | zero => simp [acceptedList]
  | succ s ih =>
      rw [acceptedList]
      exact foldStep_pairwise _ ih

open scoped Classical in
/-- **The prefix-free-ification of `c`.** `n`'s output is `evaln s c n` at the first stage `s`
where `n` is accepted, if any. -/
noncomputable def pfy (c : Code) : ℕ →. ℕ := fun n =>
  if h : ∃ s, n ∈ acceptedList c s then
    Part.some ((evaln (Nat.find h) c n).get
      (evaln_isSome_of_mem_acceptedList c (Nat.find h) (Nat.find_spec h)))
  else Part.none

theorem mem_pfy_dom_iff (c : Code) (n : ℕ) : n ∈ (pfy c).Dom ↔ ∃ s, n ∈ acceptedList c s := by
  change (pfy c n).Dom ↔ _
  unfold pfy
  split <;> simp_all

/-- **`pfy` is a restriction of `eval`**: every output `pfy` gives is an output `eval` gives. -/
theorem pfy_sub (c : Code) (n v : ℕ) (h : v ∈ pfy c n) : v ∈ c.eval n := by
  unfold pfy at h
  split at h
  · rename_i hex
    rw [Part.mem_some_iff] at h
    have hmem : v ∈ evaln (Nat.find hex) c n := h ▸ Option.get_mem _
    exact evaln_sound hmem
  · exact absurd h (Part.notMem_none v)

/-- **`pfy c`'s domain, read as bit-strings, is prefix-free.** -/
theorem pfy_prefixFree (c : Code) : PrefixFree (natToBits '' (pfy c).Dom) := by
  intro p hp q hq hpq
  simp only [Set.mem_image] at hp hq
  obtain ⟨n, hn, rfl⟩ := hp
  obtain ⟨n', hn', rfl⟩ := hq
  by_cases hnn' : n = n'
  · rw [hnn']
  · exfalso
    obtain ⟨sn, hsn⟩ := (mem_pfy_dom_iff c n).mp hn
    obtain ⟨sn', hsn'⟩ := (mem_pfy_dom_iff c n').mp hn'
    have hboth1 : n ∈ acceptedList c (max sn sn') := acceptedList_mono (le_max_left _ _) hsn
    have hboth2 : n' ∈ acceptedList c (max sn sn') := acceptedList_mono (le_max_right _ _) hsn'
    have hsymm : Std.Symm
        (fun m k => ¬ (natToBits m <+: natToBits k ∨ natToBits k <+: natToBits m)) :=
      ⟨fun a b hab => by tauto⟩
    exact List.Pairwise.forall (acceptedList_pairwise c (max sn sn')) hboth1 hboth2 hnn'
      (Or.inl hpq)

/-- Under a global prefix-free hypothesis on `c`'s halting domain, nothing ever gets rejected: a
domain element appearing in the candidate list `l` ends up in the fold's result, provided it is
not already in the (domain-contained) accumulator. -/
private theorem mem_foldl_foldStep_of_dom {c : Code} (h : PrefixFree (natToBits '' c.eval.Dom))
    (l acc : List ℕ) (hacc : ∀ m ∈ acc, m ∈ c.eval.Dom) (hl : ∀ m ∈ l, m ∈ c.eval.Dom)
    (hlnodup : l.Nodup) {n : ℕ} (hn : n ∈ l) (hnacc : n ∉ acc) :
    n ∈ l.foldl foldStep acc := by
  induction l generalizing acc with
  | nil => cases hn
  | cons a l ih =>
      rcases List.mem_cons.mp hn with rfl | hn'
      · have hnotcomp :
            ¬ ∃ m ∈ acc, natToBits m <+: natToBits n ∨ natToBits n <+: natToBits m := by
          rintro ⟨m, hm, hcomp⟩
          have hmS : m ∈ c.eval.Dom := hacc m hm
          have hnS : n ∈ c.eval.Dom := hl n List.mem_cons_self
          have hmn : m ≠ n := fun he => hnacc (he ▸ hm)
          have heqbits : natToBits m = natToBits n := by
            rcases hcomp with hc | hc
            · exact h (natToBits m) ⟨m, hmS, rfl⟩ (natToBits n) ⟨n, hnS, rfl⟩ hc
            · exact (h (natToBits n) ⟨n, hnS, rfl⟩ (natToBits m) ⟨m, hmS, rfl⟩ hc).symm
          exact hmn (by simpa [bitsToNat_natToBits] using congrArg bitsToNat heqbits)
        rw [List.foldl_cons, foldStep_eq_of_neg hnotcomp]
        exact mem_of_mem_foldStep_foldl _ _ (List.mem_append_right _ (by simp))
      · rw [List.foldl_cons]
        apply ih (foldStep acc a)
        · intro m hm
          by_cases hcase : ∃ k ∈ acc, natToBits k <+: natToBits a ∨ natToBits a <+: natToBits k
          · rw [foldStep_eq_of_pos hcase] at hm
            exact hacc m hm
          · rw [foldStep_eq_of_neg hcase] at hm
            rcases List.mem_append.mp hm with hm' | hm'
            · exact hacc m hm'
            · simp only [List.mem_singleton] at hm'
              exact hm' ▸ hl a List.mem_cons_self
        · exact fun m hm => hl m (List.mem_cons_of_mem _ hm)
        · exact hlnodup.of_cons
        · exact hn'
        · intro hmem
          by_cases hcase : ∃ k ∈ acc, natToBits k <+: natToBits a ∨ natToBits a <+: natToBits k
          · rw [foldStep_eq_of_pos hcase] at hmem
            exact hnacc hmem
          · rw [foldStep_eq_of_neg hcase] at hmem
            rcases List.mem_append.mp hmem with hmem' | hmem'
            · exact hnacc hmem'
            · simp only [List.mem_singleton] at hmem'
              exact (List.nodup_cons.mp hlnodup).1 (hmem' ▸ hn')

/-- **`pfy` reproduces `eval` exactly, once `eval`'s halting domain is already prefix-free.** -/
theorem pfy_eq_of_prefixFree (c : Code) (h : PrefixFree (natToBits '' c.eval.Dom)) :
    pfy c = c.eval := by
  have hdom_sub : ∀ s n, n ∈ acceptedList c s → n ∈ c.eval.Dom := by
    intro s
    induction s with
    | zero => intro n hn; simp [acceptedList] at hn
    | succ s ih =>
        intro n hn
        rw [acceptedList] at hn
        rcases mem_foldl_foldStep _ _ hn with h' | h'
        · exact ih n h'
        · simp only [newlyHalting, List.mem_filter, List.mem_range, Bool.and_eq_true] at h'
          obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp h'.2.1
          exact Part.dom_iff_mem.mpr ⟨v, evaln_sound hv⟩
  have main : ∀ s n, n ∈ c.eval.Dom → (evaln s c n).isSome → n ∈ acceptedList c s := by
    intro s
    induction s with
    | zero => intro n _ hs; simp [evaln] at hs
    | succ s ih =>
        intro n hnd hs
        by_cases hprev : (evaln s c n).isSome
        · have hin := ih n hnd hprev
          rw [acceptedList]
          exact mem_of_mem_foldStep_foldl _ _ hin
        · have hnl : n ∈ newlyHalting c s := by
            simp only [newlyHalting, List.mem_filter, List.mem_range, Bool.and_eq_true]
            obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hs
            exact ⟨evaln_bound hv, hs, by simpa using hprev⟩
          have hnacc : n ∉ acceptedList c s := fun hmem =>
            hprev (evaln_isSome_of_mem_acceptedList c s hmem)
          have hlnodup : (newlyHalting c s).Nodup := List.Nodup.filter _ List.nodup_range
          have hlmem : ∀ m ∈ newlyHalting c s, m ∈ c.eval.Dom := by
            intro m hm
            simp only [newlyHalting, List.mem_filter, List.mem_range, Bool.and_eq_true] at hm
            obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hm.2.1
            exact Part.dom_iff_mem.mpr ⟨v, evaln_sound hv⟩
          have haccmem : ∀ m ∈ acceptedList c s, m ∈ c.eval.Dom := fun m hm => hdom_sub s m hm
          rw [acceptedList]
          exact mem_foldl_foldStep_of_dom h _ _ haccmem hlmem hlnodup hnl hnacc
  funext n
  apply Part.ext
  intro v
  constructor
  · exact pfy_sub c n v
  · intro hv
    have hnd : n ∈ c.eval.Dom := Part.dom_iff_mem.mpr ⟨v, hv⟩
    obtain ⟨k, hk⟩ := evaln_complete.mp hv
    have hacc := main k n hnd (Option.isSome_iff_exists.mpr ⟨v, hk⟩)
    have hpdom : n ∈ (pfy c).Dom := (mem_pfy_dom_iff c n).mpr ⟨k, hacc⟩
    obtain ⟨v', hv'⟩ := Part.dom_iff_mem.mp hpdom
    have hv'eval := pfy_sub c n v' hv'
    have hvv' : v = v' := Part.mem_unique hv hv'eval
    rwa [hvv']

/-! ## `KB`: prefix complexity over the universal prefix machine `pfy`

A description is a serialized machine `E c`, followed by a binary argument `p`; `KB x` is the
least total length `elen c + p.length` over descriptions decoding, via `pfy`, to `x`. -/

/-- **Prefix complexity**: least `elen c + p.length` over a serialized machine and a binary
argument decoding to `x` via `pfy`. -/
noncomputable def KB (x : ℕ) : ℕ :=
  sInf {l | ∃ (c : Code) (p : List Bool), x ∈ pfy c (bitsToNat p) ∧ elen c + p.length = l}

theorem KB_le {c : Code} {p : List Bool} {x : ℕ} (h : x ∈ pfy c (bitsToNat p)) :
    KB x ≤ elen c + p.length :=
  Nat.sInf_le ⟨c, p, h, rfl⟩

/-- The partial function halting only on input `0`, with value `0`. -/
private theorem partrec_guard0 :
    Nat.Partrec (fun n : ℕ => Nat.rfind fun _ : ℕ => Part.some (decide (n = 0))) := by
  have hc : Computable fun p : ℕ × ℕ => decide (p.1 ≤ p.2) := by
    have hpr := Primrec.nat_le.choose_spec.to_comp
    have heq : (fun a : ℕ × ℕ => @decide _ (Primrec.nat_le.choose a)) =
        fun p : ℕ × ℕ => decide (p.1 ≤ p.2) := by funext a; congr 1
    rw [← heq]; exact hpr
  have hle0 : Computable fun n : ℕ => decide (n ≤ 0) :=
    hc.comp (Computable.id.pair (Computable.const 0))
  have heq0 : (fun n : ℕ => decide (n ≤ 0)) = fun n : ℕ => decide (n = 0) := by
    funext n; simp
  rw [heq0] at hle0
  have hg : Computable fun p : ℕ × ℕ => decide (p.1 = 0) := hle0.comp Computable.fst
  exact Partrec.nat_iff.mp (Partrec.rfind hg.partrec)

/-- A fixed guard code, halting on input `0` alone with value `0`. -/
private noncomputable def guard0 : Code := Classical.choose (exists_code.mp partrec_guard0)

private theorem eval_guard0 (n : ℕ) :
    guard0.eval n = Nat.rfind fun _ : ℕ => Part.some (decide (n = 0)) := by
  have h := congrFun (Classical.choose_spec (exists_code.mp partrec_guard0)) n
  simpa [guard0] using h

private theorem eval_guard0_zero : guard0.eval 0 = Part.some 0 := by
  rw [eval_guard0]
  apply Part.eq_some_iff.mpr
  exact Nat.mem_rfind.mpr ⟨by simp, fun hm => absurd hm (Nat.not_lt_zero _)⟩

private theorem domain_comp_guard0 {c : Code} {x : ℕ} (h : Computes c x) :
    (comp c guard0).eval = fun n => if n = 0 then Part.some x else Part.none := by
  funext n
  by_cases hn : n = 0
  · subst hn
    simp only [if_true]
    exact (eval_comp_some eval_guard0_zero).trans (by simpa [Computes] using h)
  · simp only [if_neg hn]
    have hguard : guard0.eval n = Part.none := by
      rw [eval_guard0, Part.eq_none_iff]
      rintro v hv
      have hspec := Nat.rfind_spec hv
      simp only [Part.mem_some_iff] at hspec
      simp [hn] at hspec
    change guard0.eval n >>= c.eval = Part.none
    rw [hguard]
    exact Part.bind_none c.eval

/-- **`KB` is additively below `KE` (`KB_le_KE`).** Hardcoding a datum-free guard: `comp c guard0`
halts on input `0` alone, so its domain — the singleton `{0}`, i.e. `{[]}` in bit-strings — is
(trivially) prefix-free, and `pfy` reproduces it exactly. -/
private theorem exists_KB_desc (x : ℕ) : x ∈ pfy (comp (minCode x) guard0) (bitsToNat []) := by
  have hc : Computes (minCode x) x := minCode_computes x
  have hdom : (comp (minCode x) guard0).eval = fun n => if n = 0 then Part.some x else Part.none :=
    domain_comp_guard0 hc
  have hpf : PrefixFree (natToBits '' (comp (minCode x) guard0).eval.Dom) := by
    intro p hp q hq _
    simp only [Set.mem_image, hdom] at hp hq
    obtain ⟨n, hn, rfl⟩ := hp
    obtain ⟨n', hn', rfl⟩ := hq
    have hn0 : n = 0 := by
      by_contra hne
      exact absurd (show (if n = 0 then Part.some x else Part.none : Part ℕ).Dom from hn)
        (by simp [hne])
    have hn'0 : n' = 0 := by
      by_contra hne
      exact absurd (show (if n' = 0 then Part.some x else Part.none : Part ℕ).Dom from hn')
        (by simp [hne])
    rw [hn0, hn'0]
  have hpfy : pfy (comp (minCode x) guard0) = (comp (minCode x) guard0).eval :=
    pfy_eq_of_prefixFree _ hpf
  rw [hpfy, bitsToNat_nil, hdom]
  simp

theorem KB_le_KE : ∃ c₀ : ℕ, ∀ x : ℕ, KB x ≤ KE x + c₀ := by
  refine ⟨elen guard0 + 3, fun x => ?_⟩
  have hle := KB_le (exists_KB_desc x)
  rw [E_len_comp, elen_minCode] at hle
  simp only [List.length_nil, add_zero] at hle
  omega

/-- `KB x` is achieved by some serialized-machine-plus-argument description. -/
theorem exists_min_KB (x : ℕ) :
    ∃ (c : Code) (p : List Bool), x ∈ pfy c (bitsToNat p) ∧ elen c + p.length = KB x := by
  have hne : {l | ∃ (c : Code) (p : List Bool),
      x ∈ pfy c (bitsToNat p) ∧ elen c + p.length = l}.Nonempty :=
    ⟨_, comp (minCode x) guard0, [], exists_KB_desc x, rfl⟩
  exact Nat.sInf_mem hne

/-- A shortest description for `x` (`exists_min_KB` makes the choice possible). -/
noncomputable def minDescCode (x : ℕ) : Code := (exists_min_KB x).choose

/-- Its binary argument. -/
noncomputable def minDescArg (x : ℕ) : List Bool := (exists_min_KB x).choose_spec.choose

theorem minDesc_spec (x : ℕ) :
    x ∈ pfy (minDescCode x) (bitsToNat (minDescArg x)) ∧
      elen (minDescCode x) + (minDescArg x).length = KB x :=
  (exists_min_KB x).choose_spec.choose_spec

/-- **Distinct values have distinct shortest descriptions.** -/
private theorem minDesc_injective :
    Function.Injective fun x => (⟨minDescCode x, minDescArg x⟩ : Code × List Bool) := by
  intro x y hxy
  have hx := (minDesc_spec x).1
  have hy := (minDesc_spec y).1
  rw [Prod.mk.injEq] at hxy
  rw [hxy.1, hxy.2] at hx
  exact Part.mem_unique hx hy

open scoped Classical in
/-- The Kraft weight of a description, zeroed out unless its argument is genuinely in `pfy c`'s
domain (read as a bit-string). A nonnegative function on `Code × List Bool` whose row sums (fixed
`c`) are Kraft-bounded by `kraft_of_prefixFree`, and whose column sum over `c` (`kraft_KP_E`)
bounds the whole. -/
noncomputable def kbWeight (cp : Code × List Bool) : ℝ :=
  if cp.2 ∈ natToBits '' (pfy cp.1).Dom then (1 / 2 : ℝ) ^ (elen cp.1 + cp.2.length) else 0

theorem kbWeight_nonneg (cp : Code × List Bool) : 0 ≤ kbWeight cp := by
  unfold kbWeight; split <;> positivity

theorem summable_row (c : Code) : Summable (fun p => kbWeight (c, p)) := by
  have hpf := pfy_prefixFree c
  have hnil : [] ∉ natToBits '' (pfy c).Dom ∨ natToBits '' (pfy c).Dom = {[]} := by
    by_cases hnil : [] ∈ natToBits '' (pfy c).Dom
    · exact Or.inr (eq_singleton_of_nil_mem hpf hnil)
    · exact Or.inl hnil
  have heq : (fun p => kbWeight (c, p)) =
      (natToBits '' (pfy c).Dom).indicator (fun p => (1 / 2 : ℝ) ^ (elen c + p.length)) := by
    funext p
    by_cases hp : p ∈ natToBits '' (pfy c).Dom
    · simp [kbWeight, hp]
    · simp [kbWeight, hp]
  rw [heq, ← summable_subtype_iff_indicator]
  have : (fun q : (natToBits '' (pfy c).Dom) => (1 / 2 : ℝ) ^ (elen c + (q : List Bool).length))
      = fun q : (natToBits '' (pfy c).Dom) =>
        (1 / 2 : ℝ) ^ elen c * (1 / 2 : ℝ) ^ (q : List Bool).length := by
    funext q; rw [pow_add]
  rw [Function.comp_def, this]
  apply Summable.mul_left
  rcases hnil with hnil | hnil
  · have hud := uniquelyDecodable_of_prefixFree hpf hnil
    refine BinaryKraft.indexed_summable (fun q : (natToBits '' (pfy c).Dom) => (q : List Bool))
      Subtype.coe_injective ?_
    rwa [Subtype.range_coe]
  · rw [hnil]
    have : Finite (↥({[]} : Set (List Bool))) := (Set.finite_singleton _).to_subtype
    exact Summable.of_finite

theorem tsum_row_le (c : Code) : ∑' p, kbWeight (c, p) ≤ (1 / 2 : ℝ) ^ elen c := by
  have hpf := pfy_prefixFree c
  have heq : (fun p => kbWeight (c, p)) =
      (natToBits '' (pfy c).Dom).indicator (fun p => (1 / 2 : ℝ) ^ (elen c + p.length)) := by
    funext p
    by_cases hp : p ∈ natToBits '' (pfy c).Dom
    · simp [kbWeight, hp]
    · simp [kbWeight, hp]
  rw [heq, ← tsum_subtype (natToBits '' (pfy c).Dom) (fun p => (1 / 2 : ℝ) ^ (elen c + p.length))]
  have heq2 : (fun q : (natToBits '' (pfy c).Dom) =>
      (1 / 2 : ℝ) ^ (elen c + (q : List Bool).length))
      = fun q : (natToBits '' (pfy c).Dom) =>
        (1 / 2 : ℝ) ^ elen c * (1 / 2 : ℝ) ^ (q : List Bool).length := by
    funext q; rw [pow_add]
  rw [heq2, tsum_mul_left]
  have hkraft := kraft_of_prefixFree hpf
  calc (1 / 2 : ℝ) ^ elen c *
        ∑' q : (natToBits '' (pfy c).Dom), (1 / 2 : ℝ) ^ (q : List Bool).length
      ≤ (1 / 2 : ℝ) ^ elen c * 1 := by
        apply mul_le_mul_of_nonneg_left hkraft (by positivity)
    _ = (1 / 2 : ℝ) ^ elen c := mul_one _

theorem summable_elen : Summable fun c : Code => (1 / 2 : ℝ) ^ elen c := by
  simpa [elen] using BinaryKraft.indexed_summable E E_injective uniquelyDecodable_range_E

theorem summable_tsum_row : Summable fun c : Code => ∑' p, kbWeight (c, p) :=
  summable_elen.of_nonneg_of_le (fun c => tsum_nonneg fun p => kbWeight_nonneg (c, p)) tsum_row_le

theorem summable_kbWeight : Summable kbWeight := by
  rw [summable_prod_of_nonneg kbWeight_nonneg]
  exact ⟨summable_row, summable_tsum_row⟩

/-- **Kraft's inequality for `KB`**: `∑ₓ 2⁻ᴷᴮ⁽ˣ⁾ ≤ 1` — `KB` is a semimeasure. Each `x` contributes
the weight of its own shortest description; the descriptions are pairwise distinct
(`minDesc_injective`), and for a fixed machine `c` the arguments range over `pfy c`'s domain,
prefix-free by `pfy_prefixFree`, hence Kraft-summable by `kraft_of_prefixFree`. -/
theorem kraft_KB : ∑' x : ℕ, (1 / 2 : ℝ) ^ KB x ≤ 1 := by
  set Φ : ℕ → Code × List Bool := fun x => (minDescCode x, minDescArg x) with hΦ
  have hΦinj : Function.Injective Φ := by
    intro x y hxy
    exact minDesc_injective hxy
  have hval : ∀ x : ℕ, (1 / 2 : ℝ) ^ KB x ≤ kbWeight (Φ x) := by
    intro x
    have hspec := minDesc_spec x
    have hmemS : minDescArg x ∈ natToBits '' (pfy (minDescCode x)).Dom :=
      ⟨bitsToNat (minDescArg x), Part.dom_iff_mem.mpr ⟨x, hspec.1⟩, natToBits_bitsToNat _⟩
    have : kbWeight (Φ x) = (1 / 2 : ℝ) ^ (elen (minDescCode x) + (minDescArg x).length) := by
      unfold kbWeight; simp only [hΦ]; rw [if_pos hmemS]
    rw [this, hspec.2]
  have hf : Summable fun x : ℕ => (1 / 2 : ℝ) ^ KB x :=
    summable_kbWeight.comp_injective hΦinj |>.of_nonneg_of_le
      (fun x => by positivity) hval
  have hle : ∑' x : ℕ, (1 / 2 : ℝ) ^ KB x ≤ ∑' cp : Code × List Bool, kbWeight cp :=
    Summable.tsum_le_tsum_of_inj Φ hΦinj (fun cp _ => kbWeight_nonneg cp) hval hf summable_kbWeight
  refine hle.trans ?_
  rw [summable_kbWeight.tsum_prod' summable_row]
  calc ∑' c : Code, ∑' p, kbWeight (c, p) ≤ ∑' c : Code, (1 / 2 : ℝ) ^ elen c :=
        Summable.tsum_le_tsum tsum_row_le summable_tsum_row summable_elen
    _ ≤ 1 := by simpa [elen] using kraft_KP_E

end PrefixMachine
