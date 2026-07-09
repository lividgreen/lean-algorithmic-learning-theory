import Mathlib
import ALT.Realizability
set_option linter.style.header false
set_option linter.style.longLine false

/-!
# Realizer-length non-closure (Paper I §4.3, F4 — categorical Kolmogorov / Shannon counting bound)

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

/-- **Shannon counting bound (F4 core).** More functions than short codes ⇒ some function needs a
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

/-- **F4, capacity form** (sibling of `exp_card_overflow`): a fitting object whose exponential has a
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

/-- **Explicit exponential magnitude** (Paper I §4.3). Sharpens
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

end Realizability
