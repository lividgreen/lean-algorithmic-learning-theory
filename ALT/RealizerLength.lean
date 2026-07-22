/-
Copyright (c) 2026 Mykola Palamarchuk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mykola Palamarchuk
-/
import Mathlib
import ALT.Realizability
set_option linter.style.header false
set_option linter.style.longLine false

/-!
# Realizer-length non-closure ([Decoupling] §4.3 — categorical Kolmogorov / Shannon counting bound)

FV-14 (`exp_card_overflow`) shows the exponential overflows capacity in *element count*
(`|α→α| = |α|^|α| > 2^s`). This is the **realizer-length** half: by a counting bound, since
`#{codes of bit-length ≤ b} ≤ 2^b` but there are `|B|^|A|` functions, once `2^b < |B|^|A|` some
morphism `A → B` has **no realizer of bit-length ≤ b** — it needs a code longer than `b`. At the
capacity threshold `b = s`, the same object whose exponential overflows in cardinality has a genuine
morphism (every function is realized, `realizes_of_finite`) whose every realizer exceeds `s` bits.
-/

namespace Realizability

open Nat.Partrec

/-- Every assembly has **decidable equality** — its encoding `enc` into ℕ is injective
(`Function.Injective.decidableEq`), constructively. This is what makes the function space
`A.carrier → B.carrier` a `Fintype`, so its cardinality (the count in the Shannon bound) is defined. -/
instance instDecidableEqCarrier (A : Assembly) : DecidableEq A.carrier := A.enc_inj.decidableEq

/-- Bit-length of a code: `Nat.size` of its Gödel index (the paper's realizer length `r`). -/
def bitlen (r : Code) : ℕ := Nat.size (Encodable.encode r)

/-- `r` tracks `f` (the un-existentialized `Realizes`): `Realizes f ↔ ∃ r, RealizesBy r f` (defeq). -/
def RealizesBy {A B : Assembly} (r : Code) (f : A.carrier → B.carrier) : Prop :=
  ∀ x, r.eval (A.enc x) = Part.some (B.enc (f x))

/-- A code realizes at most one function (extensionally) — `B.enc` is injective. -/
theorem realizes_unique {A B : Assembly} {r : Code} {f g : A.carrier → B.carrier}
    (hf : RealizesBy r f) (hg : RealizesBy r g) : f = g := by
  funext x
  exact B.enc_inj (Part.some_inj.mp ((hf x).symm.trans (hg x)))

/-- **Shannon counting bound.** More functions than short codes ⇒ some function needs a
realizer of bit-length `> b`. -/
theorem realizer_length_overflow {A B : Assembly} (b : ℕ)
    (hcard : 2 ^ b < Fintype.card (A.carrier → B.carrier)) :
    ∃ f : A.carrier → B.carrier, ∀ r : Code, RealizesBy r f → b < bitlen r := by
  by_contra h
  push Not at h            -- h : ∀ f, ∃ r, RealizesBy r f ∧ bitlen r ≤ b
  choose r hr hb using h    -- r : (A→B)→Code, hr : RealizesBy (r f) f, hb : bitlen (r f) ≤ b
  -- φ f := index of a short realizer, landing in Fin (2^b) via `Nat.size_le`
  have hlt : ∀ f, Encodable.encode (r f) < 2 ^ b := fun f => Nat.size_le.mp (hb f)
  let φ : (A.carrier → B.carrier) → Fin (2 ^ b) := fun f => ⟨Encodable.encode (r f), hlt f⟩
  have hφinj : Function.Injective φ := by
    intro f g hfg
    have hcode : r f = r g :=
      Encodable.encode_injective (by simpa [φ, Fin.mk.injEq] using hfg)
    have : RealizesBy (r f) g := by rw [hcode]; exact hr g
    exact realizes_unique (hr f) this
  have hle := Fintype.card_le_of_injective φ hφinj
  rw [Fintype.card_fin] at hle
  omega

/-- A capacity-filling assembly (carrier `Fin (2^s)`, `enc = Fin.val`), fitting in `s` bits. -/
def fatAsm (s : ℕ) : Assembly where
  carrier := Fin (2 ^ s)
  enc := Fin.val
  enc_inj := Fin.val_injective

theorem fatAsm_fitsIn (s : ℕ) : (fatAsm s).FitsIn s := fun x => x.isLt

/-- **Capacity form** (sibling of `exp_card_overflow`): a fitting object whose exponential has a
genuine morphism (`Realizes f`) every realizer of which exceeds capacity `s` bits. -/
theorem exp_realizer_overflow (s : ℕ) (hs : 1 ≤ s) :
    ∃ A : Assembly, A.FitsIn s ∧
      ∃ f : A.carrier → A.carrier, Realizes f ∧ ∀ r : Code, RealizesBy r f → s < bitlen r := by
  refine ⟨fatAsm s, fatAsm_fitsIn s, ?_⟩
  have hk : 1 < 2 ^ s := by
    calc 1 < 2 := by norm_num
      _ = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ s := Nat.pow_le_pow_right (by norm_num) hs
  have hc : Fintype.card (fatAsm s).carrier = 2 ^ s := by
    change Fintype.card (Fin (2 ^ s)) = 2 ^ s
    simp
  have hcard : 2 ^ s < Fintype.card ((fatAsm s).carrier → (fatAsm s).carrier) := by
    rw [Fintype.card_fun, hc]
    exact Nat.lt_pow_self hk
  obtain ⟨f, hf⟩ := realizer_length_overflow s hcard
  exact ⟨f, realizes_of_finite f, hf⟩

/-- **Explicit exponential magnitude** ([Decoupling] §4.3). Sharpens
`exp_realizer_overflow` from the linear `> s`-bit figure to the paper's literal `≈ 2^{|s_work|}`-bit
figure: the SAME fitting object `fatAsm s` (working carrier `Fin (2^s)`, so `|s_work| = s`) carries a
genuine morphism (`Realizes f`) every realizer of which has bit-length `≥ s · 2^s`. The core is the
Shannon counting bound at the threshold `b = s·2^s − 1`: with `|α→α| = (2^s)^{2^s} = 2^{s·2^s}`
functions but only `≤ 2^b` codes of length `≤ b`, some morphism has no realizer of length `≤ b`,
i.e. length `≥ s·2^s`. -/
theorem exp_realizer_overflow_exponential (s : ℕ) (hs : 1 ≤ s) :
    ∃ A : Assembly, A.FitsIn s ∧
      ∃ f : A.carrier → A.carrier, Realizes f ∧ ∀ r : Code, RealizesBy r f → s * 2 ^ s ≤ bitlen r := by
  refine ⟨fatAsm s, fatAsm_fitsIn s, ?_⟩
  have hc : Fintype.card (fatAsm s).carrier = 2 ^ s := by
    change Fintype.card (Fin (2 ^ s)) = 2 ^ s
    simp
  -- `|α→α| = (2^s)^{2^s} = 2^{s·2^s}`.
  have hcardEq : Fintype.card ((fatAsm s).carrier → (fatAsm s).carrier) = 2 ^ (s * 2 ^ s) := by
    rw [Fintype.card_fun, hc, ← pow_mul]
  -- `s·2^s ≥ 1`, so the threshold `s·2^s − 1` is genuine and `2^{s·2^s−1} < 2^{s·2^s}`.
  have hpos : 0 < s * 2 ^ s := mul_pos (by omega) (by positivity)
  have hmono : 2 ^ (s * 2 ^ s - 1) < 2 ^ (s * 2 ^ s) :=
    Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hcard : 2 ^ (s * 2 ^ s - 1) < Fintype.card ((fatAsm s).carrier → (fatAsm s).carrier) := by
    rw [hcardEq]; exact hmono
  obtain ⟨f, hf⟩ := realizer_length_overflow (s * 2 ^ s - 1) hcard
  refine ⟨f, realizes_of_finite f, ?_⟩
  intro r hr
  have hlen := hf r hr
  omega

/-! ### Almost-all form of the counting bound ([Decoupling] §4.3 / §7.2, FV-16) -/

open Classical in
/-- **Counting bound, cardinality form.** At most `2 ^ b` functions `A → B` admit a realizer of
bit-length `≤ b`. Each such function chooses a short realizer, whose Gödel code lands in `Fin (2^b)`
(via `Nat.size_le`), and a code realizes at most one function (`realizes_unique`), so the choice is
injective. -/
theorem shortRealizable_card_le (A B : Assembly) (b : ℕ) :
    Fintype.card {f : A.carrier → B.carrier // ∃ r : Code, bitlen r ≤ b ∧ RealizesBy r f} ≤ 2 ^ b := by
  have hlt : ∀ f : {f : A.carrier → B.carrier // ∃ r : Code, bitlen r ≤ b ∧ RealizesBy r f},
      Encodable.encode f.2.choose < 2 ^ b :=
    fun f => Nat.size_le.mp f.2.choose_spec.1
  let φ : {f : A.carrier → B.carrier // ∃ r : Code, bitlen r ≤ b ∧ RealizesBy r f} → Fin (2 ^ b) :=
    fun f => ⟨Encodable.encode f.2.choose, hlt f⟩
  have hφinj : Function.Injective φ := by
    intro f g hfg
    have hcode : f.2.choose = g.2.choose :=
      Encodable.encode_injective (by simpa [φ, Fin.mk.injEq] using hfg)
    apply Subtype.ext
    have hrf : RealizesBy f.2.choose f.1 := f.2.choose_spec.2
    have hrg : RealizesBy f.2.choose g.1 := by rw [hcode]; exact g.2.choose_spec.2
    exact realizes_unique hrf hrg
  have hle := Fintype.card_le_of_injective φ hφinj
  rwa [Fintype.card_fin] at hle

open Classical in
/-- **Almost-all form** ([Decoupling] §4.3 / §7.2). All but at most `2 ^ b` of the functions `A → B` have
**every** realizer longer than `b` bits: the "long-realizer" set is the complement of the
short-realizable set, whose cardinality is `≤ 2 ^ b` by `shortRealizable_card_le`. -/
theorem almost_all_realizer_overflow (A B : Assembly) (b : ℕ) :
    Fintype.card (A.carrier → B.carrier) - 2 ^ b ≤
      Fintype.card {f : A.carrier → B.carrier // ∀ r : Code, RealizesBy r f → b < bitlen r} := by
  have hiff : ∀ f : A.carrier → B.carrier,
      (∀ r : Code, RealizesBy r f → b < bitlen r) ↔ ¬ ∃ r : Code, bitlen r ≤ b ∧ RealizesBy r f := by
    intro f
    constructor
    · rintro h ⟨r, hb, hr⟩
      have := h r hr
      omega
    · intro h r hr
      by_contra hlt
      exact h ⟨r, by omega, hr⟩
  rw [Fintype.card_congr (Equiv.subtypeEquivRight hiff), Fintype.card_subtype_compl]
  have := shortRealizable_card_le A B b
  omega

open Classical in
/-- **Capacity instantiation** ([Decoupling] §4.3, the "generic element"). For the capacity-filling
`fatAsm s` (working carrier `Fin (2^s)`, so `|s_work| = s`), all but at most `2^(s·2^s − 1)` of the
`2^(s·2^s)` endomorphisms need a realizer of bit-length `≥ s·2^s`: the generic morphism between
capacity objects has no short realizer. -/
theorem almost_all_fatAsm_overflow (s : ℕ) (hs : 1 ≤ s) :
    2 ^ (s * 2 ^ s) - 2 ^ (s * 2 ^ s - 1) ≤
      Fintype.card {f : (fatAsm s).carrier → (fatAsm s).carrier //
        ∀ r : Code, RealizesBy r f → s * 2 ^ s ≤ bitlen r} := by
  have hpos : 0 < s * 2 ^ s := mul_pos (by omega) (by positivity)
  have hcong : Fintype.card {f : (fatAsm s).carrier → (fatAsm s).carrier //
        ∀ r : Code, RealizesBy r f → (s * 2 ^ s - 1) < bitlen r} =
      Fintype.card {f : (fatAsm s).carrier → (fatAsm s).carrier //
        ∀ r : Code, RealizesBy r f → s * 2 ^ s ≤ bitlen r} := by
    apply Fintype.card_congr
    apply Equiv.subtypeEquivRight
    intro f
    constructor
    · intro h r hr; have := h r hr; omega
    · intro h r hr; have := h r hr; omega
  have hcardEq : Fintype.card ((fatAsm s).carrier → (fatAsm s).carrier) = 2 ^ (s * 2 ^ s) := by
    have hc : Fintype.card (fatAsm s).carrier = 2 ^ s := by
      change Fintype.card (Fin (2 ^ s)) = 2 ^ s; simp
    rw [Fintype.card_fun, hc, ← pow_mul]
  have key := almost_all_realizer_overflow (fatAsm s) (fatAsm s) (s * 2 ^ s - 1)
  rw [hcardEq, hcong] at key
  exact key

end Realizability
