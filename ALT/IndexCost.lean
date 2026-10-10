/-
Copyright (c) 2026 Mykola Palamarchuk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mykola Palamarchuk
-/
module

public import AIT.KolmogorovBitlen
public import AIT.PrefixInvarianceKB
public import CodeLayer.BitStringPrimrec
public import CodeLayer.Code.SizeArith
public import Mathlib.Data.Nat.Log
public import Mathlib.Data.List.Forall2

-- Formal-check file, not Mathlib-destined: opt out of the house-style header linter.
set_option linter.style.header false

/-!
# The index cost of a description

Provenance: [Discovery] §1.1 (the reference machine) and [Decoupling] Theorem 6.7 (the two
currencies, index-length vs. description-length). Registered in [Discovery] §1.1's formalization
note as FV row FV-33.

`K_bitlen` prices a program by its Gödel INDEX's bit-length (`codelen'`, `AIT.KolmogorovBitlen`),
while `KB` prices a description by its LENGTH (`AIT.PrefixMachine`). Mathlib's `encodeCode` sends
`pair a b`/`comp a b` to `4 * Nat.pair (ea) (eb) + O(1)`, so an index's bit-length DOUBLES at each
node of a code's tree: an arithmetic literal of chain depth `size w` costs about `2 ^ size w`,
which is why no arithmetic literal of the description may appear in a `K_bitlen`-vs-`KB` bound. A
BALANCED tree over the description's bits costs only about its leaf count instead, and the
construction here is that tree.

## What this establishes

* `nestValue`, `bitNest`: fold a bit list into a balanced nest, under `Nat.pair` (naturals) and
  under `Code.pair` (codes, with `Code.zero`/`Code.succ` as the two cheapest leaf codes); the
  supporting one-round helpers `pairUp`/`pairUpCode` and their length bounds.
* `nestUnpack`: the depth-indexed inverse, unpairing a value `2 ^ h` times into its leaf bits.
* `stripPad`: drops trailing padding falses and the marker `true` a padded description carries.
* `SizeLaw`, `NestSpec`, `DecoderSpec`: three specifications — `codelen'`'s growth law at
  `pair`/`comp`, the nest's own evaluation/size/round-trip facts, and a decoder reading the padded
  nest back through `PrefixMachine.univPrefix`. All three are proved. `SizeLaw` is proved
  (`sizeLaw`, from `encodeCode`'s own clauses and `CodeLayer.Code.SizeArith`'s bit-length
  arithmetic);
  `NestSpec` is proved (`nestSpec`, from `sizeLaw` alone: the fold's own evaluation law by
  well-founded recursion over a `Forall₂` witness on its leaves, its size law by induction on the
  depth against `sizeLaw`, and its round-trip law by induction on the depth, splitting the bit
  list at its midpoint and reading the folded value's two halves back out through
  `Nat.unpair_pair`); `DecoderSpec` is proved (`decoderSpec`, from a code `decoderCode` for the
  primitive-recursive depth-indexed unpacking (`nestUnpack`, primitive recursive by iterating a
  numeric splitting step) composed with `PrefixMachine.univPrefix`'s own partial recursiveness,
  taken by `Nat.Partrec.Code.exists_code`).
* `K_bitlen_le_32_mul_KB_of`: the conditional lemma these three specifications assemble into,
  proved from them as hypotheses: assembling a minimal `KB`-description into a padded,
  depth-tagged nest and running it through the decoder bounds `K_bitlen x` by `32 * KB x + c` —
  the converse, at a constant factor, of `PrefixMachine.KB_le_K_bitlen_add_two_mul_size`.
* `K_bitlen_le_32_mul_KB`: **the index cost of a description, unconditional** — `sizeLaw`,
  `nestSpec` and `decoderSpec` discharge every hypothesis of `K_bitlen_le_32_mul_KB_of`, so
  `K_bitlen x ≤ 32 * KB x + c` holds outright.

## What this does NOT establish (flagged)

* `codelen'_const_add_three_le` is a further consequence, not one of the three specifications
  itself: `Code.const` is Mathlib's own unary tower, and its growth law is proved here from
  `SizeLaw` by induction.
* Registered as [Discovery] §1.1's FV row FV-33; no numbered statement of a paper carries it.

## Hypotheses: paper-stated vs added

* Paper-stated / faithful: none — a formalization note registers the bound (FV-33), no numbered
  statement does.
* Added / modeling: the balanced-nest encoding of a description (`nestValue`/`bitNest`), the
  depth-tag-plus-marker-bit padding scheme, and the decoder `decoderCode` reading it back through
  `univPrefix` — none paper-stated, and all of `SizeLaw`, `NestSpec` and `DecoderSpec` are proved
  rather than taken as hypotheses.
-/


@[expose] public section

namespace IndexCost

open Nat.Partrec Nat.Partrec.Code KolmogorovComplexity PrefixMachine AdditiveComplexity
  CodeEvalLaws CodeSizeArith

/-! ## The balanced nest, over naturals and over codes -/

/-- One pairing round: pairs up neighbouring values with `Nat.pair`, carrying an odd tail value
up unchanged to the next round. -/
def pairUp : List ℕ → List ℕ
  | [] => []
  | [x] => [x]
  | x :: y :: rest => Nat.pair x y :: pairUp rest

theorem pairUp_length_le : ∀ l : List ℕ, (pairUp l).length ≤ l.length
  | [] => le_refl _
  | [_] => le_refl _
  | _ :: _ :: rest => by
      have ih := pairUp_length_le rest
      simp only [pairUp, List.length_cons]
      omega

theorem pairUp_length_lt (x y : ℕ) (rest : List ℕ) :
    (pairUp (x :: y :: rest)).length < (x :: y :: rest).length := by
  have ih := pairUp_length_le rest
  simp only [pairUp, List.length_cons]
  omega

/-- Repeatedly `pairUp`s a list of naturals down to one value. -/
def natNestFold : List ℕ → ℕ
  | [] => 0
  | [x] => x
  | x :: y :: rest => natNestFold (pairUp (x :: y :: rest))
termination_by l => l.length
decreasing_by exact pairUp_length_lt x y rest

/-- **Folds a bit list into a balanced nest under `Nat.pair`**, pairing neighbours and carrying an
odd tail up. -/
def nestValue (bs : List Bool) : ℕ := natNestFold (bs.map Bool.toNat)

/-- The `Code`-valued one pairing round, mirroring `pairUp`. -/
def pairUpCode : List Code → List Code
  | [] => []
  | [c] => [c]
  | c :: d :: rest => Code.pair c d :: pairUpCode rest

theorem pairUpCode_length_le : ∀ l : List Code, (pairUpCode l).length ≤ l.length
  | [] => le_refl _
  | [_] => le_refl _
  | _ :: _ :: rest => by
      have ih := pairUpCode_length_le rest
      simp only [pairUpCode, List.length_cons]
      omega

theorem pairUpCode_length_lt (c d : Code) (rest : List Code) :
    (pairUpCode (c :: d :: rest)).length < (c :: d :: rest).length := by
  have ih := pairUpCode_length_le rest
  simp only [pairUpCode, List.length_cons]
  omega

/-- Repeatedly `pairUpCode`s a list of codes down to one code. -/
def codeNestFold : List Code → Code
  | [] => Code.zero
  | [c] => c
  | c :: d :: rest => codeNestFold (pairUpCode (c :: d :: rest))
termination_by l => l.length
decreasing_by exact pairUpCode_length_lt c d rest

/-- **The `Code`-valued balanced nest**: `Code.zero`/`Code.succ` for `false`/`true` — the two
cheapest codes in the encoding, evaluating at `0` to the bit they stand for — folded the same way
as `nestValue`. -/
def bitNest (bs : List Bool) : Code :=
  codeNestFold (bs.map fun b => if b then Code.succ else Code.zero)

/-- **The depth-indexed inverse**: unpairs a value `h` times into its `2 ^ h` leaf bits. Correct
on values built by `nestValue`/`bitNest` from a list of length exactly `2 ^ h` (`NestSpec`'s third
clause), where no round ever carries an odd tail. -/
def nestUnpack : ℕ → ℕ → List Bool
  | 0, v => [decide (v ≠ 0)]
  | h + 1, v => nestUnpack h v.unpair.1 ++ nestUnpack h v.unpair.2

/-- **Drops trailing padding falses and then one marker `true`.** Correct on any
`base ++ true :: List.replicate k false` regardless of `base`'s own content
(`stripPad_append_marker_pad`), since the marker `true` stops the trailing-false scan before it
ever reaches `base`. -/
def stripPad (bs : List Bool) : List Bool :=
  ((bs.reverse.dropWhile fun b => !b).drop 1).reverse

private theorem dropWhile_not_replicate_append (k : ℕ) (rest : List Bool) :
    (List.replicate k false ++ (true :: rest)).dropWhile (fun b => !b) = true :: rest := by
  induction k with
  | zero => simp
  | succ k ih => simp [List.replicate_succ, ih]

/-- **`stripPad` recovers the un-padded, un-marked prefix.** -/
private theorem stripPad_append_marker_pad (base : List Bool) (k : ℕ) :
    stripPad (base ++ true :: List.replicate k false) = base := by
  unfold stripPad
  have hrev : (base ++ true :: List.replicate k false).reverse
      = List.replicate k false ++ (true :: base.reverse) := by
    rw [List.reverse_append, List.reverse_cons, List.reverse_replicate]
    simp
  rw [hrev, dropWhile_not_replicate_append k base.reverse]
  simp

/-! ## The three specifications, taken as hypotheses -/

/-- **`codelen'`'s growth law at `pair`/`comp`**: pairing/composing two codes costs at most twice
the wider child plus three (the three attained). -/
def SizeLaw : Prop := ∀ a b : Code,
  codelen' (Code.pair a b) ≤ 2 * max (codelen' a) (codelen' b) + 3 ∧
  codelen' (Code.comp a b) ≤ 2 * max (codelen' a) (codelen' b) + 3

/-- **`SizeLaw`, proved.** `encodeCode`'s own clauses at `pair`/`comp` are `4 * Nat.pair (encodeCode
cf) (encodeCode cg) + 4` and `+ 6`; `size_four_mul_add_four_le`/`size_four_mul_add_six_le` turn that
`+ 4`/`+ 6` into `+ 3` bits over the pairing's own bit-length, and `size_pair_le_max` bounds the
pairing by twice the wider child's bit-length. -/
theorem sizeLaw : SizeLaw := by
  intro a b
  have hpair : codelen (Code.pair a b) = 4 * Nat.pair (codelen a) (codelen b) + 4 := by
    simp only [codelen, Nat.Partrec.Code.encodeCode_eq, Nat.Partrec.Code.encodeCode]
    ring
  have hcomp : codelen (Code.comp a b) = 4 * Nat.pair (codelen a) (codelen b) + 6 := by
    simp only [codelen, Nat.Partrec.Code.encodeCode_eq, Nat.Partrec.Code.encodeCode]
    ring
  refine ⟨?_, ?_⟩
  · unfold codelen'
    rw [hpair]
    have h1 := size_four_mul_add_four_le (Nat.pair (codelen a) (codelen b))
    have h2 := size_pair_le_max (codelen a) (codelen b)
    omega
  · unfold codelen'
    rw [hcomp]
    have h1 := size_four_mul_add_six_le (Nat.pair (codelen a) (codelen b))
    have h2 := size_pair_le_max (codelen a) (codelen b)
    omega

/-- **The nest's own evaluation, size and round-trip facts.** -/
def NestSpec : Prop :=
  (∀ bs, (bitNest bs).eval 0 = Part.some (nestValue bs)) ∧
  (∀ (bs : List Bool) (h : ℕ), bs.length = 2 ^ h → codelen' (bitNest bs) + 3 ≤ 4 * 2 ^ h) ∧
  (∀ (bs : List Bool) (h : ℕ), bs.length = 2 ^ h → nestUnpack h (nestValue bs) = bs)

/-- **A decoder reading a depth-tagged, padded nest back through `univPrefix`.** -/
def DecoderSpec : Prop := ∃ U : Code, ∀ h V : ℕ,
  U.eval (Nat.pair h V) = univPrefix.eval (bitsToNat (stripPad (nestUnpack h V)))

/-! ## `Code.const`'s own growth law, proved from `SizeLaw`

`Code.const` is Mathlib's own unary successor tower (`const (n + 1) = comp succ (const n)`), not
one of the three hypotheses, so its `codelen'` growth is proved here from `SizeLaw`. -/

private theorem codelen'_zero_eq : codelen' Code.zero = 0 := by
  simp [codelen', KolmogorovComplexity.codelen, Nat.Partrec.Code.encodeCode_eq,
    Nat.Partrec.Code.encodeCode]

private theorem codelen'_succ_eq : codelen' Code.succ = 1 := by
  simp [codelen', KolmogorovComplexity.codelen, Nat.Partrec.Code.encodeCode_eq,
    Nat.Partrec.Code.encodeCode]

/-- **`Code.const h`'s own `codelen'` growth law**, matching `NestSpec`'s second clause's shape:
proved by induction on `h`, using `SizeLaw`'s `comp` clause at each unary step. -/
theorem codelen'_const_add_three_le (hsize : SizeLaw) :
    ∀ h : ℕ, codelen' (Code.const h) + 3 ≤ 4 * 2 ^ h
  | 0 => by
      have h0 : codelen' (Code.const 0) = 0 := codelen'_zero_eq
      simp only [pow_zero]
      omega
  | h + 1 => by
      have ih := codelen'_const_add_three_le hsize h
      have hcomp := (hsize Code.succ (Code.const h)).2
      have hconst_eq : Code.const (h + 1) = Code.comp Code.succ (Code.const h) := rfl
      have hpow : (1 : ℕ) ≤ 2 ^ h := Nat.one_le_two_pow
      have e1 : codelen' Code.succ + 3 ≤ 4 * 2 ^ h := by rw [codelen'_succ_eq]; omega
      have hmax : max (codelen' Code.succ) (codelen' (Code.const h)) + 3 ≤ 4 * 2 ^ h := by
        rcases le_total (codelen' Code.succ) (codelen' (Code.const h)) with hle | hle
        · rw [max_eq_right hle]; exact ih
        · rw [max_eq_left hle]; exact e1
      have hpowsucc : (2 : ℕ) ^ (h + 1) = 2 * 2 ^ h := by rw [pow_succ]; ring
      rw [hconst_eq]
      omega

/-! ## `NestSpec`, proved -/

/-- **One round of `pairUpCode` preserves the eval-correspondence a `Forall₂` witness carries.**
If every code of `cs` evaluates at `0` to the matching entry of `vs`, so does every code of one
`pairUpCode` round, against the matching `pairUp` round: a `pair`'s eval law composes two
already-related entries into one. -/
private theorem forall₂_pairUp_pairUpCode :
    ∀ (cs : List Code) (vs : List ℕ),
      List.Forall₂ (fun c v => c.eval 0 = Part.some v) cs vs →
      List.Forall₂ (fun c v => c.eval 0 = Part.some v) (pairUpCode cs) (pairUp vs)
  | [], [], _ => by simp [pairUpCode, pairUp]
  | [], _ :: _, h => by cases h
  | [_c], [], h => by cases h
  | [c], [v], h => by
      obtain ⟨hcv, _⟩ := List.forall₂_cons.mp h
      simpa [pairUpCode, pairUp] using hcv
  | [_c], _v :: _w :: _vs', h => by cases h with | cons _ htail => cases htail
  | _c :: _d :: _cs', [], h => by cases h
  | _c :: _d :: _cs', [_v], h => by cases h with | cons _ htail => cases htail
  | c :: d :: cs', v :: w :: vs', h => by
      obtain ⟨hcv, htail⟩ := List.forall₂_cons.mp h
      obtain ⟨hdw, hrest⟩ := List.forall₂_cons.mp htail
      have hpair : (Code.pair c d).eval 0 = Part.some (Nat.pair v w) := by
        rw [eval_pair_bind, hcv, hdw]; simp
      have ih := forall₂_pairUp_pairUpCode cs' vs' hrest
      have result : List.Forall₂ (fun x y => x.eval 0 = Part.some y)
          (Code.pair c d :: pairUpCode cs') (Nat.pair v w :: pairUp vs') :=
        List.Forall₂.cons hpair ih
      simpa [pairUpCode, pairUp] using result

/-- **The fold's own eval law, from a `Forall₂` witness on its leaves.** Well-founded recursion
mirroring `codeNestFold`/`natNestFold`'s own recursion, discharging each new round through
`forall₂_pairUp_pairUpCode`. -/
private theorem nestFold_eval :
    ∀ (cs : List Code) (vs : List ℕ),
      List.Forall₂ (fun c v => c.eval 0 = Part.some v) cs vs →
      (codeNestFold cs).eval 0 = Part.some (natNestFold vs)
  | [], [], _ => by simp only [codeNestFold, natNestFold]; rfl
  | [], _ :: _, h => by cases h
  | [_c], [], h => by cases h
  | [c], [v], h => by
      obtain ⟨hcv, _⟩ := List.forall₂_cons.mp h
      simpa [codeNestFold, natNestFold] using hcv
  | [_c], _v :: _w :: _vs', h => by cases h with | cons _ htail => cases htail
  | _c :: _d :: _cs', [], h => by cases h
  | _c :: _d :: _cs', [_v], h => by cases h with | cons _ htail => cases htail
  | c :: d :: cs', v :: w :: vs', h => by
      have hround := forall₂_pairUp_pairUpCode (c :: d :: cs') (v :: w :: vs') h
      have result := nestFold_eval (pairUpCode (c :: d :: cs')) (pairUp (v :: w :: vs')) hround
      simpa [codeNestFold, natNestFold] using result
termination_by cs _ _ => cs.length
decreasing_by exact pairUpCode_length_lt c d cs'

/-- Each leaf code evaluates at `0` to the bit it stands for, so `bitNest`'s and `nestValue`'s
own leaf lists are `Forall₂`-related. -/
private theorem forall₂_eval_bitNest (bs : List Bool) :
    List.Forall₂ (fun c v => c.eval 0 = Part.some v)
      (bs.map fun b => if b then Code.succ else Code.zero) (bs.map Bool.toNat) := by
  induction bs with
  | nil => simp
  | cons b bs ih =>
      apply List.Forall₂.cons _ ih
      cases b <;> rfl

/-- **`NestSpec`'s first clause.** -/
private theorem nestSpec_eval (bs : List Bool) :
    (bitNest bs).eval 0 = Part.some (nestValue bs) :=
  nestFold_eval _ _ (forall₂_eval_bitNest bs)

/-- `pairUpCode` halves a list's length, rounding up: `(pairUpCode l).length = (l.length+1)/2`
unconditionally. -/
private theorem pairUpCode_length_eq :
    ∀ l : List Code, (pairUpCode l).length = (l.length + 1) / 2
  | [] => by simp [pairUpCode]
  | [_c] => by simp [pairUpCode]
  | c :: d :: rest => by
      have ih := pairUpCode_length_eq rest
      simp only [pairUpCode, List.length_cons]
      omega

/-- **One `pairUpCode` round costs one more `SizeLaw` step**: if every code of `cs` obeys the
bound at level `k`, every code of one `pairUpCode` round obeys it at level `k + 1`. -/
private theorem pairUpCode_mem_size_le (hsize : SizeLaw) (k : ℕ) :
    ∀ cs : List Code, (∀ c ∈ cs, codelen' c + 3 ≤ 4 * 2 ^ k) →
      ∀ c' ∈ pairUpCode cs, codelen' c' + 3 ≤ 4 * 2 ^ (k + 1)
  | [], _, c', hc' => by simp [pairUpCode] at hc'
  | [x], hb, c', hc' => by
      have heq : c' = x := by simpa [pairUpCode] using hc'
      rw [heq]
      have hc := hb x (by simp)
      have hpow : (4 : ℕ) * 2 ^ k ≤ 4 * 2 ^ (k + 1) := by
        have h2 : (2 : ℕ) ^ k ≤ 2 ^ (k + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
      omega
  | c :: d :: rest, hb, c', hc' => by
      simp only [pairUpCode, List.mem_cons] at hc'
      rcases hc' with heq | hc'
      · rw [heq]
        have hc := hb c (by simp)
        have hd := hb d (by simp)
        have hpair := (hsize c d).1
        have hpow : (2 : ℕ) ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ]; ring
        have hmax : max (codelen' c) (codelen' d) + 3 ≤ 4 * 2 ^ k := by
          rcases le_total (codelen' c) (codelen' d) with hle | hle
          · rw [max_eq_right hle]; exact hd
          · rw [max_eq_left hle]; exact hc
        omega
      · exact pairUpCode_mem_size_le hsize k rest (fun y hy => hb y (by simp [hy])) c' hc'

/-- **The fold's own size law, `h` rounds from a per-leaf bound at level `k`.** Induction on `h`:
each round costs one `pairUpCode_mem_size_le` step, and `pairUpCode_length_eq` keeps the round's
length a power of two so the next round applies again. -/
private theorem codeNestFold_size_le (hsize : SizeLaw) :
    ∀ (h k : ℕ) (cs : List Code), cs.length = 2 ^ h →
      (∀ c ∈ cs, codelen' c + 3 ≤ 4 * 2 ^ k) →
      codelen' (codeNestFold cs) + 3 ≤ 4 * 2 ^ (h + k) := by
  intro h
  induction h with
  | zero =>
      intro k cs hlen hb
      match cs, hlen with
      | [c], _ => simpa [codeNestFold] using hb c (by simp)
  | succ h ih =>
      intro k cs hlen hb
      have hcslen2 : 2 ≤ cs.length := by
        rw [hlen, pow_succ]
        have := Nat.one_le_two_pow (n := h)
        omega
      have hstep : codeNestFold cs = codeNestFold (pairUpCode cs) := by
        match cs, hcslen2 with
        | _c :: _d :: _rest, _ => simp [codeNestFold]
      have hpairlen : (pairUpCode cs).length = 2 ^ h := by
        rw [pairUpCode_length_eq, hlen, pow_succ]
        omega
      have hpairbound : ∀ c' ∈ pairUpCode cs, codelen' c' + 3 ≤ 4 * 2 ^ (k + 1) :=
        pairUpCode_mem_size_le hsize k cs hb
      have hrec := ih (k + 1) (pairUpCode cs) hpairlen hpairbound
      rw [hstep]
      have hexp : h + (k + 1) = (h + 1) + k := by omega
      rw [hexp] at hrec
      exact hrec

/-- **`NestSpec`'s second clause.** Every leaf of `bitNest`'s own tree costs `codelen' + 3 ≤ 4`
(`Code.zero`/`Code.succ` at `codelen' = 0`/`1`), and `codeNestFold_size_le` carries that bound
through `h` rounds. -/
private theorem nestSpec_size (bs : List Bool) (h : ℕ) (hlen : bs.length = 2 ^ h) :
    codelen' (bitNest bs) + 3 ≤ 4 * 2 ^ h := by
  have hmapLen : (bs.map fun b => if b then Code.succ else Code.zero).length = 2 ^ h := by
    simp [hlen]
  have hleafBound : ∀ c ∈ bs.map (fun b => if b then Code.succ else Code.zero),
      codelen' c + 3 ≤ 4 * 2 ^ 0 := by
    intro c hc
    simp only [List.mem_map] at hc
    obtain ⟨b, _, hbc⟩ := hc
    subst hbc
    cases b <;> simp [codelen'_zero_eq, codelen'_succ_eq]
  simpa [bitNest] using codeNestFold_size_le sizeLaw h 0 _ hmapLen hleafBound

/-- `pairUp` halves a list's length, rounding up: `(pairUp l).length = (l.length+1)/2`
unconditionally. -/
private theorem pairUp_length_eq :
    ∀ l : List ℕ, (pairUp l).length = (l.length + 1) / 2
  | [] => by simp [pairUp]
  | [_x] => by simp [pairUp]
  | x :: y :: rest => by
      have ih := pairUp_length_eq rest
      simp only [pairUp, List.length_cons]
      omega

/-- **`pairUp` distributes over an append at an even-length left part.** -/
private theorem pairUp_append_of_length_even :
    ∀ l₁ l₂ : List ℕ, l₁.length % 2 = 0 → pairUp (l₁ ++ l₂) = pairUp l₁ ++ pairUp l₂
  | [], l₂, _ => by simp [pairUp]
  | [_x], _l₂, he => by simp at he
  | x :: y :: rest, l₂, he => by
      have he' : rest.length % 2 = 0 := by
        simp only [List.length_cons] at he
        omega
      have ih := pairUp_append_of_length_even rest l₂ he'
      simp only [List.cons_append, pairUp, ih]

/-- A length-`≥ 2` list's fold is one `pairUp` round of its own fold, by `natNestFold`'s own
equation. -/
private theorem natNestFold_eq_fold_pairUp :
    ∀ {l : List ℕ}, 2 ≤ l.length → natNestFold l = natNestFold (pairUp l)
  | [], hl => by simp at hl
  | [_x], hl => by simp at hl
  | _x :: _y :: _rest, _ => by simp [natNestFold]

/-- **The fold splits over an append of two equal powers-of-two-length halves**, as `Nat.pair`
of the two halves' own folds. Induction on the shared depth `h`, using
`pairUp_append_of_length_even` to push one round through the append and
`natNestFold_eq_fold_pairUp` to align both sides with the next round. -/
private theorem natNestFold_append_pow :
    ∀ (h : ℕ) (l₁ l₂ : List ℕ), l₁.length = 2 ^ h → l₂.length = 2 ^ h →
      natNestFold (l₁ ++ l₂) = Nat.pair (natNestFold l₁) (natNestFold l₂) := by
  intro h
  induction h with
  | zero =>
      intro l₁ l₂ h1 h2
      match l₁, h1 with
      | [x], _ =>
        match l₂, h2 with
        | [y], _ => simp [natNestFold, pairUp]
  | succ h ih =>
      intro l₁ l₂ h1 h2
      have hl1len2 : 2 ≤ l₁.length := by rw [h1]; have := Nat.one_le_two_pow (n := h); omega
      have hl2len2 : 2 ≤ l₂.length := by rw [h2]; have := Nat.one_le_two_pow (n := h); omega
      have hl1even : l₁.length % 2 = 0 := by rw [h1, pow_succ]; omega
      have happendlen2 : 2 ≤ (l₁ ++ l₂).length := by
        rw [List.length_append]; omega
      have step1 : natNestFold (l₁ ++ l₂) = natNestFold (pairUp (l₁ ++ l₂)) :=
        natNestFold_eq_fold_pairUp happendlen2
      have step2 : pairUp (l₁ ++ l₂) = pairUp l₁ ++ pairUp l₂ :=
        pairUp_append_of_length_even l₁ l₂ hl1even
      have hp1len : (pairUp l₁).length = 2 ^ h := by
        rw [pairUp_length_eq, h1, pow_succ]; omega
      have hp2len : (pairUp l₂).length = 2 ^ h := by
        rw [pairUp_length_eq, h2, pow_succ]; omega
      have step3 := ih (pairUp l₁) (pairUp l₂) hp1len hp2len
      have step4 : natNestFold l₁ = natNestFold (pairUp l₁) := natNestFold_eq_fold_pairUp hl1len2
      have step5 : natNestFold l₂ = natNestFold (pairUp l₂) := natNestFold_eq_fold_pairUp hl2len2
      rw [step1, step2, step3, ← step4, ← step5]

/-- **`NestSpec`'s third clause.** Induction on `h`: split `bs` at its midpoint, use
`natNestFold_append_pow` to read `nestValue bs` as `Nat.pair` of the two halves' own values, and
`Nat.unpair_pair` to recover each half before closing with the two half-length hypotheses. -/
private theorem nestSpec_roundTrip :
    ∀ (h : ℕ) (bs : List Bool), bs.length = 2 ^ h → nestUnpack h (nestValue bs) = bs
  | 0, bs, hlen => by
      match bs, hlen with
      | [b], _ => cases b <;> simp [nestUnpack, nestValue, natNestFold]
  | h + 1, bs, hlen => by
      set bs1 := bs.take (2 ^ h) with hbs1
      set bs2 := bs.drop (2 ^ h) with hbs2
      have hsplit : bs = bs1 ++ bs2 := (List.take_append_drop (2 ^ h) bs).symm
      have hbs1len : bs1.length = 2 ^ h := by
        rw [hbs1, List.length_take, hlen, pow_succ]
        omega
      have hbs2len : bs2.length = 2 ^ h := by
        rw [hbs2, List.length_drop, hlen, pow_succ]
        omega
      have hnest : nestValue bs = Nat.pair (nestValue bs1) (nestValue bs2) := by
        rw [hsplit]
        unfold nestValue
        rw [List.map_append]
        exact natNestFold_append_pow h (bs1.map Bool.toNat) (bs2.map Bool.toNat)
          (by simp [hbs1len]) (by simp [hbs2len])
      have hih1 := nestSpec_roundTrip h bs1 hbs1len
      have hih2 := nestSpec_roundTrip h bs2 hbs2len
      change nestUnpack (h + 1) (nestValue bs) = bs
      rw [hnest]
      simp only [nestUnpack]
      rw [Nat.unpair_pair]
      change nestUnpack h (nestValue bs1) ++ nestUnpack h (nestValue bs2) = bs
      rw [hih1, hih2, hsplit]

/-- **`NestSpec`, proved**: the nest's own evaluation law (`nestSpec_eval`), its size law from
`sizeLaw` (`nestSpec_size`), and its round-trip law (`nestSpec_roundTrip`) — nothing beyond
`sizeLaw` assumed. -/
theorem nestSpec : NestSpec :=
  ⟨nestSpec_eval, nestSpec_size, fun bs h hlen => nestSpec_roundTrip h bs hlen⟩

/-! ## `DecoderSpec`, proved -/

/-- One round of the depth-indexed unpacking's numeric halves, before a leaf's non-zero test turns
it into a bit: splits every value of a list into its two `Nat.unpair` children. Iterating it `h`
times from a singleton list and then testing each leaf reproduces `nestUnpack h`
(`nestUnpack_eq_iterate`), which is what makes `nestUnpack` primitive recursive despite its own
recursion running on two different arguments at once. -/
private def splitPair (l : List ℕ) : List ℕ := l.flatMap fun w => [w.unpair.1, w.unpair.2]

private theorem splitPair_primrec : Primrec splitPair := by
  unfold splitPair
  have hg : Primrec₂ (fun (_ : List ℕ) (w : ℕ) => [w.unpair.1, w.unpair.2]) :=
    (Primrec.list_cons.comp
      ((Primrec.fst.comp (Primrec.unpair.comp Primrec.snd)))
      (Primrec.list_cons.comp
        (Primrec.snd.comp (Primrec.unpair.comp Primrec.snd))
        (Primrec.const ([] : List ℕ))))
  exact Primrec.list_flatMap Primrec.id hg

private theorem primrec_decideNe0 : Primrec (fun w : ℕ => decide (w ≠ 0)) := by
  have h1 : Primrec (fun w : ℕ => (w == 0)) := Primrec.beq.comp Primrec.id (Primrec.const 0)
  have h2 : Primrec (fun w : ℕ => !(w == 0)) := Primrec.not.comp h1
  exact h2.of_eq fun w => by simp [show (w == 0) = decide (w = 0) from rfl]

private theorem primrec_iterSplit : Primrec fun p : ℕ × ℕ => splitPair^[p.1] [p.2] :=
  Primrec.nat_iterate Primrec.fst
    (Primrec.list_cons.comp Primrec.snd (Primrec.const ([] : List ℕ)))
    (splitPair_primrec.comp Primrec.snd)

private theorem primrec_nestUnpackIter :
    Primrec fun p : ℕ × ℕ => (splitPair^[p.1] [p.2]).map fun w => decide (w ≠ 0) :=
  Primrec.list_map primrec_iterSplit (primrec_decideNe0.comp Primrec.snd)

private theorem splitPair_append (l₁ l₂ : List ℕ) :
    splitPair (l₁ ++ l₂) = splitPair l₁ ++ splitPair l₂ := by
  simp [splitPair, List.flatMap_append]

private theorem splitPair_iterate_append :
    ∀ (h : ℕ) (l₁ l₂ : List ℕ), splitPair^[h] (l₁ ++ l₂) = splitPair^[h] l₁ ++ splitPair^[h] l₂
  | 0, l₁, l₂ => by simp
  | h+1, l₁, l₂ => by
      rw [Function.iterate_succ_apply, splitPair_append,
        splitPair_iterate_append h (splitPair l₁) (splitPair l₂),
        ← Function.iterate_succ_apply, ← Function.iterate_succ_apply]

/-- **`nestUnpack` restated as an iterated `splitPair`.** Induction on the depth: the recursive
call's two branches read off `IH` at `v.unpair.1`/`v.unpair.2`, and `splitPair_iterate_append`
pushes one more `splitPair` round through the list-append that joins them back into a single
`splitPair [v]` iterate. -/
private theorem nestUnpack_eq_iterate :
    ∀ (h v : ℕ), nestUnpack h v = (splitPair^[h] [v]).map fun w => decide (w ≠ 0)
  | 0, v => by simp [nestUnpack]
  | h+1, v => by
      have hstep : splitPair [v] = [v.unpair.1] ++ [v.unpair.2] := by simp [splitPair]
      change nestUnpack h v.unpair.1 ++ nestUnpack h v.unpair.2 = _
      rw [nestUnpack_eq_iterate h v.unpair.1, nestUnpack_eq_iterate h v.unpair.2,
        ← List.map_append, ← splitPair_iterate_append, ← hstep, ← Function.iterate_succ_apply]

/-- **`nestUnpack` is primitive recursive**, via `Primrec.nat_iterate` over `splitPair` and a
final per-leaf non-zero test (`nestUnpack_eq_iterate` bridges the two definitions). -/
private theorem primrec_nestUnpack : Primrec fun p : ℕ × ℕ => nestUnpack p.1 p.2 :=
  primrec_nestUnpackIter.of_eq fun p => (nestUnpack_eq_iterate p.1 p.2).symm

/-- `stripPad` is primitive recursive: a reverse, a `dropWhile`, a `drop`, a reverse. -/
private theorem stripPad_primrec : Primrec stripPad := by
  unfold stripPad
  have h1 : Primrec (fun bs : List Bool => bs.reverse) := Primrec.list_reverse
  have h2 : Primrec (fun bs : List Bool => (bs.reverse).dropWhile fun b => !b) :=
    (Primrec.list_dropWhile Primrec.not).comp h1
  have h3 : Primrec (fun bs : List Bool => ((bs.reverse).dropWhile fun b => !b).drop 1) :=
    Primrec.list_drop.comp (Primrec.const 1) h2
  exact Primrec.list_reverse.comp h3

private theorem primrec_decoderArg :
    Primrec fun n : ℕ => bitsToNat (stripPad (nestUnpack n.unpair.1 n.unpair.2)) :=
  primrec_bitsToNat.comp (stripPad_primrec.comp (primrec_nestUnpack.comp Primrec.unpair))

/-- **The decoder's defining function is partial recursive**: `univPrefix.eval` composed after the
primitive-recursive stripped-nest bits, by `Nat.Partrec.Code.eval_part` at the constant code
`univPrefix`. -/
theorem partrec_decoderFn :
    Nat.Partrec fun n : ℕ =>
      univPrefix.eval (bitsToNat (stripPad (nestUnpack n.unpair.1 n.unpair.2))) :=
  Partrec.nat_iff.mp
    (Nat.Partrec.Code.eval_part.comp (Computable.const univPrefix) primrec_decoderArg.to_comp)

/-- **The decoder, as a code**: reads a depth-tagged, padded nest back through `univPrefix`, taken
by `Nat.Partrec.Code.exists_code` at `partrec_decoderFn`. -/
noncomputable def decoderCode : Code :=
  Classical.choose (Nat.Partrec.Code.exists_code.mp partrec_decoderFn)

theorem decoderCode_eval : decoderCode.eval =
    fun n : ℕ => univPrefix.eval (bitsToNat (stripPad (nestUnpack n.unpair.1 n.unpair.2))) :=
  Classical.choose_spec (Nat.Partrec.Code.exists_code.mp partrec_decoderFn)

/-- **`DecoderSpec`, proved.** `decoderCode` reads `Nat.pair h V` back to `univPrefix.eval` on the
padded nest's stripped bits, at every `h` and `V` — `decoderCode`'s own defining property, read at
`Nat.pair h V` through `Nat.unpair_pair`. -/
theorem decoderSpec : DecoderSpec := by
  refine ⟨decoderCode, fun h V => ?_⟩
  have heval := congrFun decoderCode_eval (Nat.pair h V)
  rwa [Nat.unpair_pair] at heval

/-! ## The conditional theorem -/

/-- **The index cost of a description**: `K_bitlen x ≤ 32 * KB x + c`, `c` carrying only the
decoder's own index. Proved from the three specifications: assemble a `KB`-minimal
description into a padded, depth-tagged balanced nest, and run it through the decoder `U`. -/
theorem K_bitlen_le_32_mul_KB_of (hsize : SizeLaw) (hnest : NestSpec) (hdec : DecoderSpec) :
    ∃ c, ∀ x, K_bitlen x ≤ 32 * KB x + c := by
  obtain ⟨U, hU⟩ := hdec
  obtain ⟨hnestEval, hnestSize, hnestRoundTrip⟩ := hnest
  refine ⟨2 * codelen' U + 29, fun x => ?_⟩
  obtain ⟨c₀, p, hmem, hlen⟩ := exists_min_KB x
  set base : List Bool := E c₀ ++ p with hbase
  have hbaseLen : base.length = KB x := by
    rw [hbase, List.length_append]
    exact hlen
  set preBits : List Bool := base ++ [true] with hpreBits
  set h : ℕ := Nat.clog 2 preBits.length with hh
  have hpreLen : preBits.length = KB x + 1 := by
    rw [hpreBits, List.length_append, List.length_singleton, hbaseLen]
  have hpreLe : preBits.length ≤ 2 ^ h := Nat.le_pow_clog (by norm_num) _
  set k : ℕ := 2 ^ h - preBits.length with hk
  set bs : List Bool := preBits ++ List.replicate k false with hbs
  have hbsLen : bs.length = 2 ^ h := by
    simp only [hbs, List.length_append, List.length_replicate]
    omega
  have hstrip : stripPad bs = base := by
    have hbs' : bs = base ++ true :: List.replicate k false := by
      simp [hbs, hpreBits]
    rw [hbs']
    exact stripPad_append_marker_pad base k
  -- the description decoded through `univPrefix`
  have huniv : univPrefix.eval (bitsToNat base) = pfy c₀ (bitsToNat p) := by
    simpa [hbase] using univPrefix_spec c₀ p
  have hxmem : x ∈ univPrefix.eval (bitsToNat base) := huniv ▸ hmem
  -- the assembled code: `comp U (pair (const h) (bitNest bs))`
  have hconstEval : (Code.const h).eval 0 = Part.some h := Nat.Partrec.Code.eval_const h 0
  have hnestEvalBs : (bitNest bs).eval 0 = Part.some (nestValue bs) := hnestEval bs
  have hpairEval : (Code.pair (Code.const h) (bitNest bs)).eval 0
      = Part.some (Nat.pair h (nestValue bs)) := by
    rw [eval_pair_bind, hconstEval, hnestEvalBs, Part.bind_some, Part.map_some]
  have hcompEval : (Code.comp U (Code.pair (Code.const h) (bitNest bs))).eval 0
      = U.eval (Nat.pair h (nestValue bs)) :=
    eval_comp_some hpairEval
  have hroundTrip : nestUnpack h (nestValue bs) = bs := hnestRoundTrip bs h hbsLen
  have hUeval : U.eval (Nat.pair h (nestValue bs))
      = univPrefix.eval (bitsToNat (stripPad (nestUnpack h (nestValue bs)))) := hU h (nestValue bs)
  rw [hroundTrip, hstrip] at hUeval
  have hcode : Computes (Code.comp U (Code.pair (Code.const h) (bitNest bs))) x := by
    rw [Computes, hcompEval, hUeval]
    exact Part.eq_some_iff.mpr hxmem
  have hKbitlenLe : K_bitlen x ≤ codelen' (Code.comp U (Code.pair (Code.const h) (bitNest bs))) :=
    K_bitlen_le hcode
  -- the size chain: `const h`/`bitNest bs` each cost `+3 ≤ 4·2^h`, the `pair` `+3 ≤ 8·2^h`, the
  -- `comp` `+3 ≤ 16·2^h + 2·codelen' U`, and `2^h ≤ 2·(KB x + 1)` closes it at `32·KB x + c`.
  have hconstSize := codelen'_const_add_three_le hsize h
  have hnestSizeBs := hnestSize bs h hbsLen
  have hmaxConstNest :
      max (codelen' (Code.const h)) (codelen' (bitNest bs)) + 3 ≤ 4 * 2 ^ h := by
    rcases le_total (codelen' (Code.const h)) (codelen' (bitNest bs)) with hle | hle
    · rw [max_eq_right hle]; exact hnestSizeBs
    · rw [max_eq_left hle]; exact hconstSize
  have hpairSize := (hsize (Code.const h) (bitNest bs)).1
  have hpairSizeBound :
      codelen' (Code.pair (Code.const h) (bitNest bs)) + 3 ≤ 8 * 2 ^ h := by omega
  have hcompSize := (hsize U (Code.pair (Code.const h) (bitNest bs))).2
  have hmaxCrude :
      max (codelen' U) (codelen' (Code.pair (Code.const h) (bitNest bs)))
        ≤ codelen' U + codelen' (Code.pair (Code.const h) (bitNest bs)) := by
    omega
  have hcompSizeBound :
      codelen' (Code.comp U (Code.pair (Code.const h) (bitNest bs))) + 3
        ≤ 16 * 2 ^ h + 2 * codelen' U := by omega
  have hclogBound : 2 ^ h ≤ 2 * (KB x + 1) := by
    rw [hh, ← hpreLen]
    rcases eq_or_lt_of_le (show 1 ≤ preBits.length by omega) with h1 | h1
    · rw [← h1]; simp
    · have hpos : 0 < Nat.clog 2 preBits.length := Nat.clog_pos (by norm_num) h1
      have hlt := Nat.pow_pred_clog_lt_self (b := 2) (by norm_num) h1
      have hsucc : (Nat.clog 2 preBits.length).pred.succ = Nat.clog 2 preBits.length :=
        Nat.succ_pred_eq_of_pos hpos
      have hpow2 : (2:ℕ) ^ Nat.clog 2 preBits.length
          = 2 * 2 ^ (Nat.clog 2 preBits.length).pred := by
        conv_lhs => rw [← hsucc, pow_succ]
        ring
      omega
  omega

/-- **The index cost of a description, unconditional.** `sizeLaw`, `nestSpec` and `decoderSpec`
discharge every hypothesis of `K_bitlen_le_32_mul_KB_of`, so `K_bitlen x ≤ 32 * KB x + c` holds
outright, `c` carrying only the decoder's own index. -/
theorem K_bitlen_le_32_mul_KB : ∃ c, ∀ x, K_bitlen x ≤ 32 * KB x + c :=
  K_bitlen_le_32_mul_KB_of sizeLaw nestSpec decoderSpec

end IndexCost
