/-
Copyright (c) 2026 Mykola Palamarchuk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mykola Palamarchuk
-/
import Mathlib
import ALT.MDLDominance
import ALT.KolmogorovComplexity

-- Formal-check file, not Mathlib-destined: opt out of the house-style linters.
set_option linter.style.header false
set_option linter.style.longLine false

/-!
# Lookup-table coding bound — [Discovery], Theorem 2.1 eq. (2)

Provenance: [Discovery] §2.2 eq. (2), the lookup-table (direct-storage)
lower bound `MDL₂(lookup) ≥ L = n·log₂|O|`. `ALT/MDLDominance.lean` proves the dominance
*arithmetic* taking `Ltable = n·log|O|` as a definition; this file derives that table cost from an
explicit binary coding model so the bound is content-checked, not just named. Mathlib has no coding
theory; the argument here is elementary counting (`Nat.clog`, pigeonhole/cardinality).

## Model (stated explicitly)
* **Alphabet** `A`: any finite type, `O := Fintype.card A` symbols.
* **Sequence**: a length-`n` word is `Fin n → A`.
* **Code**: a binary code is a function into `List Bool`; its *length* on input `s` is
  `(enc s).length`. A code is lossless iff it is injective.

## What is proved (this file — the off-by-one-free "fixed-width memorization" form)
A concrete lossless code `tableEnc` storing each symbol in a fixed `⌈log₂ O⌉`-bit block:
* `tableEnc_length`  : `(tableEnc s).length = n · ⌈log₂ O⌉`  (here `⌈log₂ O⌉ = Nat.clog 2 O`);
* `tableEnc_injective` : it is lossless;
* `tableEnc_length_ge` : `n · log₂ O ≤ (tableEnc s).length` — **off-by-one-free**, the only gap is
  the genuine `⌈log₂ O⌉ ≥ log₂ O` ceiling (a real coding cost, not a proof artefact);
* `ltable_lower_bound` : `MDLDominance.Ltable O n ≤ (tableEnc s).length`, i.e. the §2.2 `Ltable = L`
  (in natural-log units) is a genuine lower bound on this code's length. (Bits ≥ nats, since
  `log₂ x = ln x / ln 2 ≥ ln x` as `ln 2 < 1`; the base-change factor is the O(1) the paper absorbs.)

`Nat.clog 2 O` is `⌈log₂ O⌉`; the bound uses `Nat.le_pow_clog` (`O ≤ 2^⌈log₂ O⌉`). No `sorry`.
-/

namespace MDLCoding

open scoped BigOperators

variable (A : Type*) [Fintype A]

/-- Block width: `⌈log₂ |A|⌉` bits per symbol. -/
def tableWidth : ℕ := Nat.clog 2 (Fintype.card A)

/-- `|A| ≤ 2^⌈log₂ |A|⌉` — each symbol fits in a `tableWidth`-bit block. -/
lemma card_le_two_pow_width : Fintype.card A ≤ 2 ^ tableWidth A :=
  Nat.le_pow_clog Nat.one_lt_two _

/-- There are exactly `2^tableWidth` width-bit blocks. -/
lemma card_block : Fintype.card (Fin (tableWidth A) → Bool) = 2 ^ tableWidth A := by
  rw [Fintype.card_fun]; simp

/-- A lossless assignment of each symbol to a distinct `tableWidth`-bit block (exists because
`|A| ≤ 2^tableWidth`). -/
noncomputable def blockEmb : A ↪ (Fin (tableWidth A) → Bool) :=
  (Function.Embedding.nonempty_of_card_le (by rw [card_block]; exact card_le_two_pow_width A)).some

variable (n : ℕ)

/-- The fixed-width lookup-table encoder: concatenate the `tableWidth`-bit block of each of the `n`
symbols, as one bitstring of length `n · tableWidth`. -/
noncomputable def tableEnc (s : Fin n → A) : List Bool :=
  List.ofFn fun p : Fin (n * tableWidth A) =>
    blockEmb A (s (finProdFinEquiv.symm p).1) (finProdFinEquiv.symm p).2

/-- The code length is exactly `n · ⌈log₂ |A|⌉` bits. -/
lemma tableEnc_length (s : Fin n → A) : (tableEnc A n s).length = n * tableWidth A := by
  rw [tableEnc, List.length_ofFn]

/-- The lookup-table code is lossless (injective). -/
lemma tableEnc_injective : Function.Injective (tableEnc A n) := by
  intro s s' h
  rw [tableEnc, tableEnc, List.ofFn_inj] at h
  funext i
  apply (blockEmb A).injective
  funext j
  have hij := congrFun h (finProdFinEquiv (i, j))
  simpa using hij

/-- `log₂ |A| ≤ ⌈log₂ |A|⌉` — the genuine ceiling gap (`Nat.clog 2 |A| ≥ Real.logb 2 |A|`). -/
lemma logb_le_tableWidth : Real.logb 2 (Fintype.card A) ≤ (tableWidth A : ℝ) := by
  rcases Nat.eq_zero_or_pos (Fintype.card A) with h | h
  · simp [tableWidth, h, Real.logb]
  · rw [Real.logb_le_iff_le_rpow (by norm_num) (by exact_mod_cast h), Real.rpow_natCast]
    exact_mod_cast Nat.le_pow_clog Nat.one_lt_two (Fintype.card A)

/-- Natural log ≤ base-2 log (since `ln 2 < 1`); used to relate the bit length to `Ltable`'s nats. -/
lemma log_le_logb_two (O : ℕ) : Real.log O ≤ Real.logb 2 O := by
  rcases Nat.eq_zero_or_pos O with h | h
  · subst h; simp [Real.logb]
  · rw [Real.logb, le_div_iff₀ (Real.log_pos (by norm_num))]
    have hO : (1 : ℝ) ≤ O := by exact_mod_cast h
    nlinarith [Real.log_nonneg hO,
      Real.log_lt_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num) (by norm_num)]

/-- **Lookup-table lower bound, off-by-one-free.** The modeled table code stores `n` symbols in
`n · ⌈log₂ |A|⌉` bits, which is `≥ n · log₂ |A| = L`. -/
theorem tableEnc_length_ge (s : Fin n → A) :
    (n : ℝ) * Real.logb 2 (Fintype.card A) ≤ ((tableEnc A n s).length : ℝ) := by
  rw [tableEnc_length]
  push_cast
  nlinarith [logb_le_tableWidth A, Nat.cast_nonneg (α := ℝ) n]

/-- **Connection to `MDLDominance.Ltable`.** The §2.2 eq. (2) quantity `Ltable |A| n = n·log|A|`
(natural-log units) is a genuine lower bound on the modeled table code's length. -/
theorem ltable_lower_bound (s : Fin n → A) :
    MDLDominance.Ltable (Fintype.card A) n ≤ ((tableEnc A n s).length : ℝ) := by
  rw [tableEnc_length, MDLDominance.Ltable]
  push_cast
  nlinarith [log_le_logb_two (Fintype.card A), logb_le_tableWidth A, Nat.cast_nonneg (α := ℝ) n]

/-! ## The genuine bound: pigeonhole lower bound on ANY lossless code

The fixed-width code above is one specific code; the real eq. (2) content is that *every* lossless
code costs `≥ L`. Counting: there are `|A|^n` sequences but only `2^L − 1` bitstrings of length
`< L`, so an injective code must use a codeword of length `≥ ⌊log₂(|A|^n)⌋`, i.e. `length + 1 ≥
n·log₂|A|`. The `+1` is the genuine integer-counting gap (a length-`<L` set has `2^L − 1 < 2^L`
elements), not removable by pure counting. -/

variable [Nonempty A]

/-- **Pigeonhole lower bound (the genuine eq. (2) bound).** For ANY lossless (injective) binary code
`enc` of the `n`-symbol sequences over `A`, some sequence has a codeword with
`n·log₂|A| ≤ length + 1`. Proof: `|A|^n` sequences inject into the `2^(M+1)−1` bitstrings of length
`≤ M` (`M` = the longest codeword), forcing `|A|^n < 2^(M+1)`, i.e. `n·log₂|A| < M + 1`. The `+1`
is the intrinsic integer gap (flagged); it is absorbed into the O(1) overheads of §2.1. -/
theorem exists_long_codeword (enc : (Fin n → A) → List Bool) (henc : Function.Injective enc) :
    ∃ o : Fin n → A, (n : ℝ) * Real.logb 2 (Fintype.card A) ≤ ((enc o).length : ℝ) + 1 := by
  obtain ⟨omax, hM⟩ := Finite.exists_max (fun o => (enc o).length)
  set M := (enc omax).length with hMdef
  refine ⟨omax, ?_⟩
  -- Inject sequences into `Σ k < M+1, length-k bitvectors`.
  let F : (Fin n → A) → Σ k : Fin (M + 1), List.Vector Bool (k : ℕ) :=
    fun o => ⟨⟨(enc o).length, Nat.lt_succ_of_le (hM o)⟩, ⟨enc o, rfl⟩⟩
  have hFinj : Function.Injective F := by
    have hcomp : (fun x : Σ k : Fin (M + 1), List.Vector Bool (k : ℕ) => x.2.toList) ∘ F = enc :=
      rfl
    exact (hcomp ▸ henc).of_comp
  -- Counting: `|A|^n ≤ 2^(M+1) − 1`.
  have hle : (Fintype.card A) ^ n ≤ 2 ^ (M + 1) - 1 := by
    have h1 := Fintype.card_le_of_injective F hFinj
    rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_sigma] at h1
    simp only [card_vector, Fintype.card_bool] at h1
    rw [Fin.sum_univ_eq_sum_range (fun m => 2 ^ m)] at h1
    simpa [Nat.geomSum_eq] using h1
  have hlt : (Fintype.card A) ^ n < 2 ^ (M + 1) := by
    have : 0 < 2 ^ (M + 1) := pow_pos (by norm_num) _
    omega
  -- Take base-2 logs.
  have hO : 0 < Fintype.card A := Fintype.card_pos
  have hOr : (0 : ℝ) < (Fintype.card A : ℝ) := by exact_mod_cast hO
  have key : Real.logb 2 ((Fintype.card A : ℝ) ^ n) ≤ (M : ℝ) + 1 := by
    rw [Real.logb_le_iff_le_rpow (by norm_num) (pow_pos hOr n)]
    rw [show ((M : ℝ) + 1) = ((M + 1 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
    calc (Fintype.card A : ℝ) ^ n = ((Fintype.card A ^ n : ℕ) : ℝ) := by push_cast; ring
      _ ≤ ((2 ^ (M + 1) : ℕ) : ℝ) := by exact_mod_cast hlt.le
      _ = (2 : ℝ) ^ (M + 1) := by push_cast; ring
  rwa [Real.logb_pow] at key

/-! ## Rule-based two-part code — [Discovery], Theorem 2.1 eq. (1) (upper bound)

Provenance: [Discovery] §2.2 eq. (1), `MDL₂(rule) ≤ Lrule = r + 2·log₂ r +
c₃ + log₂|O| + log₂ n + O(1)`. `MDLDominance.Lrule` takes this as a definition; here we build an
explicit two-part code and bound its length, so `Lrule` is a proved upper bound on a real code.

The substance is the **self-delimiting** length prefix: a program of `r` bits whose length is a
priori unknown must be framed so the decoder finds its end, and the cheapest framing (Elias-γ)
costs `r + 2·log₂ r + O(1)` — the `2 log r` term of `Kmin`.

### Units (flagged)
This is a genuine *binary* (`MDL₂`) code, so its length is in **bits** (`Real.logb 2`).
`MDLDominance.Lrule`/`Kmin` are written in `Real.log` (nats). Bits = nats / `ln 2` and `ln 2 < 1`,
so the bit cost is the *larger* of the two: the bound here is `≤ r + 2·log₂ r + log₂|O| + log₂ n +
O(1)`, the faithful MDL₂ cost. (We do NOT claim `≤` the natural-log `Lrule`, which is smaller; the
per-term base-change factor is the O(1)-per-log the paper's `O(·)` absorbs, and dominance is
unaffected since every term is `O(log)` against `Ltable = Θ(n log O)`.)

### What is proved vs. assumed
* `selfDelim_length_le` — the self-delimiting bound `(selfDelim p).length ≤ |p| + 2·log₂|p| + 1`,
  fully proved (the only gap is the genuine `⌊·⌋ ≤ log₂` floor, a real coding saving).
* `lrule_upper_bound` — the assembled two-part code length `≤ r + 2·log₂ r + log₂|O| + log₂ n + 3`.
* The "data-given-model" fields (`log₂|O| + log₂ n`) are built concretely as plain binary
  (`dataInfo`); the `r = K_bitlen(program)` identification is the model interpretation (the program
  is any `r`-bit rule), not re-derived here. Decoder/losslessness: see the injectivity section.
-/

/-- `⌊log₂ m⌋ ≤ log₂ m` — the floor gap (a real coding saving, flagged). -/
lemma natLog_le_logb (m : ℕ) : (Nat.log 2 m : ℝ) ≤ Real.logb 2 m := by
  rcases Nat.eq_zero_or_pos m with h | h
  · subst h; simp [Real.logb]
  · rw [Real.le_logb_iff_rpow_le (by norm_num) (by exact_mod_cast h), Real.rpow_natCast]
    exact_mod_cast Nat.pow_log_le_self 2 h.ne'

/-- Elias-γ code of `m`: `⌊log₂ m⌋` zeros followed by the binary digits of `m`
(length `2·⌊log₂ m⌋ + 1` for `m ≥ 1`). Self-delimiting: the zero-run marks where the digits start. -/
def eliasγ (m : ℕ) : List Bool :=
  List.replicate (Nat.log 2 m) false ++ (Nat.digits 2 m).reverse.map (· != 0)

/-- `(eliasγ m).length ≤ 2·⌊log₂ m⌋ + 1` (equality for `m ≥ 1`; `eliasγ 0 = []`). -/
lemma eliasγ_length_le (m : ℕ) : (eliasγ m).length ≤ 2 * Nat.log 2 m + 1 := by
  unfold eliasγ
  rw [List.length_append, List.length_replicate, List.length_map, List.length_reverse]
  rcases Nat.eq_zero_or_pos m with h | h
  · subst h; simp
  · rw [Nat.length_digits 2 m (by norm_num) h.ne']; omega

/-- Self-delimiting wrapper: prepend the Elias-γ encoding of the payload's length. -/
def selfDelim (p : List Bool) : List Bool := eliasγ p.length ++ p

/-- **Self-delimiting length bound** `(selfDelim p).length ≤ |p| + 2·log₂|p| + 1`. The `2·log₂|p|`
is the cost of framing an a-priori-unknown-length program — the `Kmin` `2 log r` term, content-checked. -/
theorem selfDelim_length_le (p : List Bool) :
    ((selfDelim p).length : ℝ) ≤ (p.length : ℝ) + 2 * Real.logb 2 p.length + 1 := by
  have h1 : (selfDelim p).length ≤ p.length + (2 * Nat.log 2 p.length + 1) := by
    unfold selfDelim; rw [List.length_append]
    have := eliasγ_length_le p.length; omega
  calc ((selfDelim p).length : ℝ)
      ≤ ((p.length + (2 * Nat.log 2 p.length + 1) : ℕ) : ℝ) := by exact_mod_cast h1
    _ = (p.length : ℝ) + 2 * (Nat.log 2 p.length : ℝ) + 1 := by push_cast; ring
    _ ≤ (p.length : ℝ) + 2 * Real.logb 2 p.length + 1 := by linarith [natLog_le_logb p.length]

/-- **Cor 2.2 content-check.** The model part of the rule-based two-part code for a program `p`
of bit-length `r = |p|` is the self-delimiting code `selfDelim p`, whose length meets the
bits-form capacity threshold `KminBits r 1`. So Cor 2.2's `2 log r` overhead is a *real* code
length, not an assertion — exactly as eq.(1)/eq.(2) ground `MDLDominance`. -/
theorem selfDelim_realizes_KminBits (p : List Bool) :
    ((selfDelim p).length : ℝ) ≤ CapacityThreshold.KminBits (p.length : ℝ) 1 := by
  unfold CapacityThreshold.KminBits
  exact selfDelim_length_le p

/-- Plain binary encoding of `m` (no framing), length `≤ log₂ m + 1`. -/
def binCode (m : ℕ) : List Bool := (Nat.digits 2 m).map (· != 0)

lemma binCode_length_le (m : ℕ) : (binCode m).length ≤ Nat.log 2 m + 1 := by
  unfold binCode; rw [List.length_map]
  rcases Nat.eq_zero_or_pos m with h | h
  · subst h; simp
  · exact le_of_eq (Nat.length_digits 2 m (by norm_num) h.ne')

/-- Data-given-model field: the alphabet size `|O|` and step count `n`, in plain binary. -/
def dataInfo (O n : ℕ) : List Bool := binCode O ++ binCode n

lemma dataInfo_length_le (O n : ℕ) :
    ((dataInfo O n).length : ℝ) ≤ Real.logb 2 O + Real.logb 2 n + 2 := by
  unfold dataInfo; rw [List.length_append]
  have hnat : (binCode O).length + (binCode n).length ≤ Nat.log 2 O + 1 + (Nat.log 2 n + 1) := by
    have := binCode_length_le O; have := binCode_length_le n; omega
  calc (((binCode O).length + (binCode n).length : ℕ) : ℝ)
      ≤ ((Nat.log 2 O + 1 + (Nat.log 2 n + 1) : ℕ) : ℝ) := by exact_mod_cast hnat
    _ = (Nat.log 2 O : ℝ) + (Nat.log 2 n : ℝ) + 2 := by push_cast; ring
    _ ≤ Real.logb 2 O + Real.logb 2 n + 2 := by linarith [natLog_le_logb O, natLog_le_logb n]

/-- The rule-based two-part code: self-delimited program, then the data-given-model field. -/
def ruleCode (p : List Bool) (O n : ℕ) : List Bool := selfDelim p ++ dataInfo O n

/-- **Theorem 2.1 eq. (1) (upper bound), in bits.** The two-part code for an `r`-bit rule program
`p` generating an `n`-symbol sequence over an `|O|`-symbol alphabet has length
`≤ r + 2·log₂ r + log₂|O| + log₂ n + 3`, i.e. `Lrule` (in bits) is a proved upper bound on an actual
lossless code. The `+3` is the O(1); the `2·log₂ r` self-delimiting cost is the content-checked
`Kmin` term. -/
theorem lrule_upper_bound (p : List Bool) (O n : ℕ) :
    ((ruleCode p O n).length : ℝ)
      ≤ (p.length : ℝ) + 2 * Real.logb 2 p.length + Real.logb 2 O + Real.logb 2 n + 3 := by
  unfold ruleCode; rw [List.length_append]
  push_cast
  linarith [selfDelim_length_le p, dataInfo_length_le O n]

/-! ### Losslessness of the self-delimited program code

`selfDelim` is injective: the program is recovered from its self-delimited encoding. We prove this
via the length channel — `a ↦ (eliasγ a).length + a` is strictly monotone, so equal codes force
equal payload lengths, after which the (now identical) γ-prefix cancels. (This is the lossless
encoding of the *program*. The full two-part decoder that also separates the program from the
trailing data field by parsing the γ zero-run — `(p, data) ↦ selfDelim p ++ data` injective for
nonempty `p` — is the standard Elias-γ prefix property; its formalization is the residual and is not
needed for the length bound `lrule_upper_bound`.) -/

/-- `eliasγ`'s length is monotone in its argument (`Nat.log` and digit-length are). -/
lemma eliasγ_len_mono {a a' : ℕ} (h : a ≤ a') : (eliasγ a).length ≤ (eliasγ a').length := by
  unfold eliasγ
  simp only [List.length_append, List.length_replicate, List.length_map, List.length_reverse]
  have h2 : (Nat.digits 2 a).length ≤ (Nat.digits 2 a').length := by
    rcases Nat.eq_zero_or_pos a with ha | ha
    · subst ha; simp
    · rw [Nat.length_digits 2 a (by norm_num) ha.ne',
          Nat.length_digits 2 a' (by norm_num) (by omega)]
      have := Nat.log_mono_right (b := 2) h; omega
  have h1 := Nat.log_mono_right (b := 2) h
  omega

/-- **`selfDelim` is lossless (injective):** the program is uniquely recovered from its
self-delimited encoding. -/
theorem selfDelim_injective : Function.Injective selfDelim := by
  have hmono : StrictMono (fun a => (eliasγ a).length + a) := by
    intro a a' haa'
    have := eliasγ_len_mono (le_of_lt haa')
    simp only; omega
  intro p₁ p₂ h
  have hlen : (eliasγ p₁.length).length + p₁.length
      = (eliasγ p₂.length).length + p₂.length := by
    have hh : (selfDelim p₁).length = (selfDelim p₂).length := by rw [h]
    simpa [selfDelim, List.length_append] using hh
  have hpeq : p₁.length = p₂.length := hmono.injective hlen
  unfold selfDelim at h
  rw [hpeq] at h
  exact List.append_cancel_left h

/-! ### The two-part code is genuinely lossless (Elias-γ prefix property)

`selfDelim_injective` recovers the program from its *standalone* self-delimited encoding. Here we
close the residual: the program is recovered even with a **trailing data field** — the map
`(p, data) ↦ selfDelim p ++ data` is injective (for nonempty programs). The proof builds the actual
Elias-γ decoder: read the leading zero-run to get `⌊log₂|p|⌋`, hence the γ-prefix length; split off
the prefix and recover `|p|` from its binary digits (`recoverNat`); then split `p` from `data`. This
makes `ruleCode` a genuinely lossless two-part code, not merely a length bound. (Nonemptiness is
required and flagged: `selfDelim [] = []`, so an empty program cannot be delimited from the data.) -/

/-- Decode a binary-digit block (the Elias-γ payload) back to its natural number: undo
`(Nat.digits 2 m).reverse.map (·≠0)`. -/
def recoverNat (D : List Bool) : ℕ :=
  Nat.ofDigits 2 (D.reverse.map (fun b => bif b then 1 else 0))

/-- `recoverNat` inverts the Elias-γ digit block: `recoverNat (digits-of m) = m`. -/
theorem recoverNat_digitPart (m : ℕ) :
    recoverNat ((Nat.digits 2 m).reverse.map (· != 0)) = m := by
  unfold recoverNat
  have hmap : ((Nat.digits 2 m).reverse.map (· != 0)).reverse.map (fun b => bif b then 1 else 0)
      = Nat.digits 2 m := by
    rw [← List.map_reverse, List.reverse_reverse, List.map_map]
    refine (List.map_congr_left (fun d hd => ?_)).trans (List.map_id _)
    have : d < 2 := Nat.digits_lt_base (by norm_num) hd
    interval_cases d <;> rfl
  rw [hmap, Nat.ofDigits_digits]

/-- For `m ≥ 1` the digit block starts with `true` (the MSB is `1`): the zero-run ends exactly at the
γ-payload, so the leading-zero count recovers `⌊log₂ m⌋`. -/
theorem digitPart_cons (m : ℕ) (hm : 1 ≤ m) :
    ∃ rest, (Nat.digits 2 m).reverse.map (· != 0) = true :: rest := by
  have hne : Nat.digits 2 m ≠ [] := by rw [Nat.digits_ne_nil_iff_ne_zero]; omega
  have hlast : (Nat.digits 2 m).getLast hne ≠ 0 := Nat.getLast_digit_ne_zero 2 (by omega)
  refine ⟨(Nat.digits 2 m).dropLast.reverse.map (· != 0), ?_⟩
  conv_lhs => rw [← List.dropLast_append_getLast hne]
  rw [List.reverse_append]
  simp only [List.reverse_singleton, List.singleton_append, List.map_cons]
  rw [show ((Nat.digits 2 m).getLast hne != 0) = true from by simp [hlast]]

/-- The leading zero-run after `replicate L false` (then a `true`) has length exactly `L`. -/
theorem takeWhile_prefix (L : ℕ) (t : List Bool) :
    (List.replicate L false ++ (true :: t)).takeWhile (fun b => !b) = List.replicate L false := by
  induction L with
  | zero => simp
  | succ L ih => rw [List.replicate_succ, List.cons_append, List.takeWhile_cons]; simp [ih]

/-- Exact Elias-γ length for `m ≥ 1`: `2·⌊log₂ m⌋ + 1`. -/
theorem eliasγ_length_eq (m : ℕ) (hm : 1 ≤ m) : (eliasγ m).length = 2 * Nat.log 2 m + 1 := by
  unfold eliasγ
  rw [List.length_append, List.length_replicate, List.length_map, List.length_reverse,
      Nat.length_digits 2 m (by norm_num) (by omega)]; omega

/-- The decoder reads `⌊log₂|p|⌋` from the leading zero-run of `selfDelim p ++ data` (nonempty `p`). -/
theorem takeWhile_selfDelim (p data : List Bool) (hp : p ≠ []) :
    (selfDelim p ++ data).takeWhile (fun b => !b) = List.replicate (Nat.log 2 p.length) false := by
  obtain ⟨rest, hrest⟩ := digitPart_cons p.length (List.length_pos_iff.mpr hp)
  unfold selfDelim eliasγ
  rw [hrest]
  simp only [List.append_assoc, List.cons_append]
  exact takeWhile_prefix _ _

/-- Dropping the zero-run recovers `m` from `eliasγ m` (holds for all `m`; `eliasγ 0 = []`). -/
theorem eliasγ_recover (m : ℕ) : recoverNat ((eliasγ m).drop (Nat.log 2 m)) = m := by
  unfold eliasγ
  rw [List.drop_left' (by rw [List.length_replicate])]
  exact recoverNat_digitPart m

/-- **Two-part losslessness (Elias-γ prefix property).** For nonempty programs, the self-delimited
program followed by an arbitrary data field uniquely determines both: `selfDelim p₁ ++ d₁ =
selfDelim p₂ ++ d₂ → p₁ = p₂ ∧ d₁ = d₂`. This closes the eq.(1) residual — `ruleCode` is a genuinely
lossless two-part code. -/
theorem twoPart_injective {p₁ p₂ d₁ d₂ : List Bool} (h₁ : p₁ ≠ []) (h₂ : p₂ ≠ [])
    (h : selfDelim p₁ ++ d₁ = selfDelim p₂ ++ d₂) : p₁ = p₂ ∧ d₁ = d₂ := by
  have hp1 : 1 ≤ p₁.length := List.length_pos_iff.mpr h₁
  have hp2 : 1 ≤ p₂.length := List.length_pos_iff.mpr h₂
  -- (1) the leading zero-runs match ⇒ equal `⌊log₂|p|⌋`.
  have hL : Nat.log 2 p₁.length = Nat.log 2 p₂.length := by
    have htw := congrArg (List.takeWhile (fun b => !b)) h
    rw [takeWhile_selfDelim p₁ d₁ h₁, takeWhile_selfDelim p₂ d₂ h₂] at htw
    simpa [List.length_replicate] using congrArg List.length htw
  -- (2) equal γ-prefix lengths ⇒ split off equal prefixes.
  have hlen : (eliasγ p₁.length).length = (eliasγ p₂.length).length := by
    rw [eliasγ_length_eq _ hp1, eliasγ_length_eq _ hp2, hL]
  have h' : eliasγ p₁.length ++ (p₁ ++ d₁) = eliasγ p₂.length ++ (p₂ ++ d₂) := by
    simpa [selfDelim, List.append_assoc] using h
  obtain ⟨hpre, htail⟩ := List.append_inj h' hlen
  -- (3) recover `|p|` from the prefix; (4) split `p` from `data`.
  have hpl : p₁.length = p₂.length := by
    have e1 := eliasγ_recover p₁.length
    rw [hpre, hL] at e1
    rw [← e1, eliasγ_recover p₂.length]
  exact List.append_inj htail hpl

/-- The same, packaged as injectivity of the two-part encoder on nonempty programs. -/
theorem twoPart_injOn :
    Set.InjOn (fun pd : List Bool × List Bool => selfDelim pd.1 ++ pd.2) {pd | pd.1 ≠ []} := by
  rintro ⟨p₁, d₁⟩ h₁ ⟨p₂, d₂⟩ h₂ h
  obtain ⟨hp, hd⟩ := twoPart_injective h₁ h₂ h
  exact Prod.ext hp hd

/-! ## Capstone: dominance between actual code lengths (Theorem 2.1)

Combining the two derived coding bounds — eq. (1) `lrule_upper_bound` and eq. (2) `tableEnc_length_ge`
— with a regime margin gives the headline of Theorem 2.1 at the level of *actual binary codes*: the
rule-based two-part code is strictly shorter than the lookup table.

### Units (route A)
Both coding bounds are in **bits** (`Real.logb 2`), so we prove the dominance arithmetic directly in
bits (a logb-2 analogue of `MDLDominance.mdl_dominance`'s natural-log proof). The only estimate is
`Real.logb 2 n ≤ n − 1` for integer `n ≥ 1` (`logb_two_nat_le_sub_one`, via `n ≤ 2^(n−1)`), the bit
analogue of `Real.log n ≤ n − 1`. We do NOT route through `mdl_dominance` itself: its `r` (a raw bit
count) and its `Ltable = n log O` (a log term) scale differently under base change, so a clean
divide-through is not available; the direct bit proof is shorter.

### Scope (what the comparison asserts)
This compares the **lengths** of two codes that each losslessly represent the sequence: the table
fully (`tableEnc_injective`), the rule *program* via `selfDelim_injective`. The decode-correctness
residual (that running the program `n` steps regenerates the sequence — `Code`/`Computes`) is, as
previously noted, NOT formalized; it is not needed for the `MDL₂` *length* comparison, which is
exactly what Theorem 2.1 asserts. -/

/-- `log₂ m ≤ m − 1` for integer `m ≥ 1` (bit analogue of `Real.log m ≤ m − 1`); proved from
`m ≤ 2^(m−1)`. The integrality is essential — it fails for real `x` (e.g. `log₂ 1.5 > 0.5`). -/
lemma logb_two_nat_le_sub_one {m : ℕ} (hm : 1 ≤ m) : Real.logb 2 m ≤ (m : ℝ) - 1 := by
  have hle : (m : ℝ) ≤ (2 : ℝ) ^ (m - 1) := by
    have h2 : m ≤ 2 ^ (m - 1) := by have := Nat.lt_two_pow_self (n := m - 1); omega
    calc (m : ℝ) ≤ ((2 ^ (m - 1) : ℕ) : ℝ) := by exact_mod_cast h2
      _ = (2 : ℝ) ^ (m - 1) := by push_cast; ring
  have hmono : Real.logb 2 m ≤ Real.logb 2 ((2 : ℝ) ^ (m - 1)) := by
    rw [Real.logb, Real.logb, div_le_div_iff_of_pos_right (Real.log_pos (by norm_num))]
    exact Real.log_le_log (by exact_mod_cast hm) hle
  rw [Real.logb_pow, Real.logb_self_eq_one (show (1 : ℝ) < 2 by norm_num), mul_one,
      Nat.cast_sub hm, Nat.cast_one] at hmono
  exact hmono

omit [Nonempty A] in
/-- **Theorem 2.1 (codes).** Under the bit-unit regime margin `hReg`, the rule-based two-part code
for an `r`-bit program `p` generating the length-`n` sequence `s` over the `|A|`-symbol alphabet is
strictly shorter than the lookup-table code. `_hO` (`|A| ≥ 3`, strengthened from the paper's `≥ 2`)
documents the regime constant subsumed by `hReg` (it forces `log₂|A| > 1`). -/
theorem mdl_dominance_codes (p : List Bool) (s : Fin n → A)
    (_hO : 3 ≤ Fintype.card A) (hn : 2 ≤ n)
    (hReg : (p.length : ℝ) + 2 * Real.logb 2 p.length + 4
        ≤ ((n : ℝ) - 1) * (Real.logb 2 (Fintype.card A) - 1)) :
    (ruleCode p (Fintype.card A) n).length < (tableEnc A n s).length := by
  have hlogn : Real.logb 2 n ≤ (n : ℝ) - 1 := logb_two_nat_le_sub_one (by omega)
  -- Bit-unit dominance: `Lrule_bits < Ltable_bits = n·log₂|A|`.
  have hdom : (p.length : ℝ) + 2 * Real.logb 2 p.length + Real.logb 2 (Fintype.card A)
        + Real.logb 2 n + 3 < (n : ℝ) * Real.logb 2 (Fintype.card A) := by
    nlinarith [hReg, hlogn]
  -- Chain: ruleCode ≤ Lrule_bits < Ltable_bits ≤ tableEnc.
  have hchain : ((ruleCode p (Fintype.card A) n).length : ℝ) < ((tableEnc A n s).length : ℝ) :=
    calc ((ruleCode p (Fintype.card A) n).length : ℝ)
        ≤ (p.length : ℝ) + 2 * Real.logb 2 p.length + Real.logb 2 (Fintype.card A)
            + Real.logb 2 n + 3 := lrule_upper_bound p (Fintype.card A) n
      _ < (n : ℝ) * Real.logb 2 (Fintype.card A) := hdom
      _ ≤ ((tableEnc A n s).length : ℝ) := tableEnc_length_ge A n s
  exact_mod_cast hchain

/-! ## Decode-correctness: linking the program to the generated sequence (eq.(1) residual 2)

The program field of `ruleCode` is the binary index of a `Code` (Mathlib's universal machine
`Nat.Partrec.Code`, via `ALT/KolmogorovComplexity.lean`). "The rule `c` generates the output `x`"
is `KolmogorovComplexity.Computes c x` (`c.eval 0 = Part.some x`) — the paper's modelling premise
(imported, taken as a hypothesis, *not* re-derived: Mathlib has the universal machine but we do not
re-execute it). With the two-part losslessness (`twoPart_injective`) and injectivity of the binary
index, the rule code **uniquely determines the generated output** (`ruleEncode_lossless`) — closing
the decode-correctness residual at the coding level. -/

/-- `binCode` (plain binary) is injective: recover `m` from its digits. -/
theorem binCode_injective : Function.Injective binCode := by
  have key : ∀ m, Nat.ofDigits 2 ((binCode m).map (fun b => bif b then 1 else 0)) = m := by
    intro m
    unfold binCode
    rw [List.map_map, (List.map_congr_left (fun d hd => ?_)).trans (List.map_id _)]
    · exact Nat.ofDigits_digits 2 m
    · have : d < 2 := Nat.digits_lt_base (by norm_num) hd
      interval_cases d <;> rfl
  intro m₁ m₂ h
  rw [← key m₁, ← key m₂, h]

/-- A nonzero index has a nonempty binary program. -/
theorem binCode_ne_nil (m : ℕ) (hm : 1 ≤ m) : binCode m ≠ [] := by
  simp only [binCode, ne_eq, List.map_eq_nil_iff, Nat.digits_eq_nil_iff_eq_zero]; omega

/-- The rule code of a generating `Code` `c`: the program is `c`'s binary index (shifted by `1` so it
is nonzero, hence a nonempty program), framed self-delimitingly, followed by the data field. -/
def ruleEncode (c : Nat.Partrec.Code) (O n : ℕ) : List Bool :=
  ruleCode (binCode (Encodable.encode c + 1)) O n

/-- **Decode-correctness (losslessness of the generated output).** If `c₁` generates `x₁` and `c₂`
generates `x₂`, then equal rule codes force equal generated outputs. The two-part decoder recovers
the program (`twoPart_injective`), `binCode`/`Encodable.encode` injectivity recover the `Code`, and
the generation hypotheses then equate the outputs `x₁ = x₂`. So `ruleEncode` is a lossless encoding
of the rule-generated output. -/
theorem ruleEncode_lossless {c₁ c₂ : Nat.Partrec.Code} {x₁ x₂ O n : ℕ}
    (h₁ : KolmogorovComplexity.Computes c₁ x₁) (h₂ : KolmogorovComplexity.Computes c₂ x₂)
    (h : ruleEncode c₁ O n = ruleEncode c₂ O n) : x₁ = x₂ := by
  unfold ruleEncode ruleCode at h
  obtain ⟨hp, -⟩ :=
    twoPart_injective (binCode_ne_nil _ (by omega)) (binCode_ne_nil _ (by omega)) h
  have he : Encodable.encode c₁ = Encodable.encode c₂ := by have := binCode_injective hp; omega
  have hc : c₁ = c₂ := Encodable.encode_injective he
  have heval : Part.some x₁ = Part.some x₂ := by
    rw [← h₁, ← h₂, hc]
  exact Part.some_inj.mp heval

omit [Nonempty A] in
/-- **Theorem 2.1 (codes), linked to the generated sequence.** When the program `c` *generates* the
sequence `s` (`hgen : Computes c (encode s)` — the paper's premise, so both sides describe the *same*
`s`: the table encodes `s` directly and losslessly via `tableEnc_injective`, the rule encodes `s` via
`c` losslessly via `ruleEncode_lossless`), the rule-based code of `s` is strictly shorter than the
lookup-table code of `s`, under the same regime margin. The length comparison reuses
`mdl_dominance_codes`; `hgen` is the modelling premise that fixes the *common* sequence (it is not
needed for the length inequality itself, only to make "same `s` on both sides" honest). -/
theorem mdl_dominance_codes_generated [Encodable A] (c : Nat.Partrec.Code) (s : Fin n → A)
    (_hgen : KolmogorovComplexity.Computes c (Encodable.encode s))
    (_hO : 3 ≤ Fintype.card A) (hn : 2 ≤ n)
    (hReg : ((binCode (Encodable.encode c + 1)).length : ℝ)
          + 2 * Real.logb 2 (binCode (Encodable.encode c + 1)).length + 4
        ≤ ((n : ℝ) - 1) * (Real.logb 2 (Fintype.card A) - 1)) :
    (ruleEncode c (Fintype.card A) n).length < (tableEnc A n s).length := by
  unfold ruleEncode
  exact mdl_dominance_codes A n (binCode (Encodable.encode c + 1)) s _hO hn hReg

end MDLCoding
