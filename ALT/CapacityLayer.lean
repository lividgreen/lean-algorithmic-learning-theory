/-
Copyright (c) 2026 Mykola Palamarchuk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mykola Palamarchuk
-/
import Mathlib
import ALT.RealizabilityCCC
import ALT.RealizabilityRecursor
import ALT.RealizabilityCoproduct
import ALT.RealizabilitySubobject

-- Formal-check file, not Mathlib-destined: opt out of the house-style linters.
set_option linter.style.header false
set_option linter.style.longLine false
-- Definitional `show` (unfolding an assembly's carrier to a defeq goal) is idiomatic here.
set_option linter.style.show false

/-!
# Rep(S) "up to capacity": the finite full subcategory and the honest non-closure (FV-14)

Provenance: [Decoupling] §4.2–§4.3 — Rep(S) is "a full subcategory of
finite sets, **Cartesian closed up to capacity**", presented as the capacity filtration
`Rep(S) = colim_d Rep(S)_{≤d}`; global closure *fails* because the exponential `[T₁ ⇒ T₂]` has
`|T₂|^{|T₁|}` elements, overflowing `2^{|s_work|}`.

This file makes "up to capacity" precise on the genuine realizability CCC `Asm` (FV-12/FV-13):
* `FitsIn A s` — the capacity predicate (carrier finite, `≤ 2^s` elements: ⊆ `{0,1}^s`);
* `RepS s` — **Rep(S) as the finite full subcategory** of `Asm` of objects that fit;
* `recursorAsm_fitsIn` — the §5 bounded recursor fits (`M+1 ≤ 2^s`), tying to `prop_5_4`/the `2n`
  capacity on the unified carrier (FV-13);
* `prodAsm_fitsIn` — **products stay in the filtration** (`|A×B| = |A|·|B|`, fits in `sₐ+s_b`);
* `exp_card_overflow` — **global closure FAILS on cardinality grounds**: a fitting object whose
  function-space exponential `|α→α| = |α|^{|α|}` overflows `2^s`.

## Honest residual (NOT closed here)
The *cardinality* side of "global closure fails" is machine-checked below. The **realizer-length**
side of §4.3 (a generic exponential element needs a realizer of length `~2^{|s_work|}`, by the
Shannon/Li–Vitányi counting bound) rests on a **categorical treatment of Kolmogorov complexity**,
which does not exist (the paper records this as an open *method*; cf. `KolmogorovComplexity.lean` for
the non-categorical counting infrastructure). So FV-14 earns the element-count non-closure, not the
realizer-length non-closure.
-/

namespace CapacityLayer

open RealizabilityCCC RealizabilityRecursor CategoryTheory

/-- §4.1/§4.3 — the **capacity predicate** on the realizability CCC `Asm` ("up to capacity"): the
object's carrier is finite and encodes into `s` work bits (`≤ 2^s` elements, i.e. ⊆ `{0,1}^s`). -/
def FitsIn (A : Asm) (s : ℕ) : Prop := Finite A.carrier ∧ Nat.card A.carrier ≤ 2 ^ s

/-- The capacity predicate is **monotone in the bit budget**: an object that fits in `s` work bits
fits in any larger budget `s' ≥ s` (`Nat.card A ≤ 2^s ≤ 2^{s'}`). -/
theorem FitsIn.mono {A : Asm} {s s' : ℕ} (h : FitsIn A s) (hss : s ≤ s') : FitsIn A s' :=
  ⟨h.1, h.2.trans (Nat.pow_le_pow_right (by norm_num) hss)⟩

/-- §4.2/§4.3 — **Rep(S) is the finite full subcategory** of the realizability CCC `Asm`: the objects
that fit in the work memory `s`, with all `Asm`-morphisms between them. A genuine
`CategoryTheory.Category` (full subcategory), of which the FV-12 CCC `Asm` is the un-capacitated
ambient. -/
abbrev RepS (s : ℕ) := ObjectProperty.FullSubcategory (fun A : Asm => FitsIn A s)

/-- §5.4/§6.3 — the **bounded-recursor object fits**: `recursorAsm M` (carrier `ZMod (M+1)`) encodes
into `s` work bits exactly when `M + 1 ≤ 2^s` — the FV-8 capacity arithmetic (`prop_5_4`), now on the
unified `Asm` carrier (FV-13). At the degree-2 budget this is the linear `2n` capacity. -/
theorem recursorAsm_fitsIn (M s : ℕ) (h : M + 1 ≤ 2 ^ s) : FitsIn (recursorAsm M) s := by
  refine ⟨inferInstance, ?_⟩
  have hcard : Nat.card (recursorAsm M).carrier = M + 1 := by
    simp [Nat.card_eq_fintype_card, ZMod.card]
  rw [hcard]; exact h

/-- §4.2/§4.3 — **products stay within the capacity filtration.** If `A` fits in `sₐ` work bits and
`B` in `s_b`, then `A × B` fits in `sₐ + s_b` (`|A × B| = |A|·|B|`): the controlled growth that makes
`Rep(S) = colim_d Rep(S)_{≤d}` a genuine filtration rather than a single closed level. -/
theorem prodAsm_fitsIn {A B : Asm} {sa sb : ℕ} (hA : FitsIn A sa) (hB : FitsIn B sb) :
    FitsIn (prodAsm A B) (sa + sb) := by
  obtain ⟨hAf, hAc⟩ := hA
  obtain ⟨hBf, hBc⟩ := hB
  haveI := hAf; haveI := hBf
  refine ⟨inferInstanceAs (Finite (A.carrier × B.carrier)), ?_⟩
  have hcard : Nat.card (prodAsm A B).carrier = Nat.card A.carrier * Nat.card B.carrier :=
    Nat.card_prod _ _
  rw [hcard, pow_add]
  exact Nat.mul_le_mul hAc hBc

/-- [Decoupling] §4.2 — **coproducts stay within the capacity filtration.** If `A` fits in `sₐ` work bits
and `B` in `s_b`, then the tagged-union coproduct `A ⊕ B` fits in `max sₐ s_b + 1`
(`|A ⊕ B| = |A| + |B| ≤ 2^{sₐ} + 2^{s_b} ≤ 2·2^{max sₐ s_b} = 2^{max sₐ s_b + 1}`): the additive
companion to `prodAsm_fitsIn`, keeping `Rep(S) = colim_d Rep(S)_{≤d}` a genuine filtration under
finite coproducts. -/
theorem coprodAsm_fitsIn {A B : Asm} {sa sb : ℕ}
    (hA : FitsIn A sa) (hB : FitsIn B sb) :
    FitsIn (RealizabilityCoproduct.coprodAsm A B) (max sa sb + 1) := by
  obtain ⟨hAf, hAc⟩ := hA
  obtain ⟨hBf, hBc⟩ := hB
  haveI := hAf; haveI := hBf
  refine ⟨inferInstanceAs (Finite (A.carrier ⊕ B.carrier)), ?_⟩
  have hcard : Nat.card (RealizabilityCoproduct.coprodAsm A B).carrier
      = Nat.card A.carrier + Nat.card B.carrier := Nat.card_sum
  rw [hcard]
  calc Nat.card A.carrier + Nat.card B.carrier
      ≤ 2 ^ (max sa sb) + 2 ^ (max sa sb) :=
        Nat.add_le_add
          (hAc.trans (Nat.pow_le_pow_right (by norm_num) (le_max_left sa sb)))
          (hBc.trans (Nat.pow_le_pow_right (by norm_num) (le_max_right sa sb)))
    _ = 2 ^ (max sa sb + 1) := by rw [pow_succ]; ring

/-- [Decoupling] §4.2 — the terminal object fits in `0` work bits (`|𝟙| = 1 ≤ 2^0`). -/
theorem terminalAsm_fitsIn : FitsIn terminalAsm 0 := by
  refine ⟨inferInstanceAs (Finite PUnit), ?_⟩
  show Nat.card PUnit ≤ 2 ^ 0
  simp [Nat.card_eq_fintype_card]

/-- [Decoupling] §4.2 — **comprehension subobjects cost no capacity.** The comprehension subobject
`{ a : A | P a }` fits in every budget `A` fits in (`|{a | P a}| ≤ |A|`, `Finite.card_subtype_le`):
the encoding is inherited from `A`, so carving out a decidable predicate never grows the object. -/
theorem subAsm_fitsIn {A : Asm} {P : A.carrier → Prop} {s : ℕ} (h : FitsIn A s) :
    FitsIn (RealizabilitySubobject.subAsm A P) s := by
  obtain ⟨hfin, hcard⟩ := h
  haveI := hfin
  refine ⟨inferInstanceAs (Finite {a : A.carrier // P a}), ?_⟩
  calc Nat.card (RealizabilitySubobject.subAsm A P).carrier
      = Nat.card {a : A.carrier // P a} := rfl
    _ ≤ Nat.card A.carrier := Finite.card_subtype_le P
    _ ≤ 2 ^ s := hcard

/-- [Decoupling] §4.2 — **the subobject classifier `Bool = 𝟙 ⊕ 𝟙` fits in exactly one work bit**
(`|Bool| = 2 ≤ 2^1`), the tag-bit accounting of `coprodAsm_fitsIn` at `s₁ = s₂ = 0`. -/
theorem boolAsm_fitsIn : FitsIn RealizabilitySubobject.boolAsm 1 := by
  have h := coprodAsm_fitsIn terminalAsm_fitsIn terminalAsm_fitsIn
  simp only [max_self, zero_add] at h
  exact h

/-- [Decoupling] §4.2 — **the power object `[T ⇒ Bool]` fits in `s` work bits iff `|T| ≤ s`.** The
realizability exponential into the classifier has carrier the trackable functions `T → Bool`, which —
`T` being a finite object out of which every function is a morphism (`AllTrackable`) — is *all* of
`T → Bool`, so `|[T ⇒ Bool]| = 2^{|T|}`; then `2^{|T|} ≤ 2^s ↔ |T| ≤ s`. This is the exact-cardinality
higher-order threshold of §4.2: power objects exist within capacity only for objects at most one
element per work bit. -/
theorem powAsm_fitsIn_iff (A : Asm) [Fintype A.carrier]
    (hA : RealizabilitySubobject.AllTrackable A) (s : ℕ) :
    FitsIn (expAsm A RealizabilitySubobject.boolAsm) s ↔ Fintype.card A.carrier ≤ s := by
  classical
  -- Every function `A → Bool` is a morphism (`hA`), so the exponential carrier is the full function
  -- space: `{ f // Trackable A Bool f } ≃ (A → Bool)`.
  have e : (expAsm A RealizabilitySubobject.boolAsm).carrier ≃
      (A.carrier → RealizabilitySubobject.boolAsm.carrier) :=
    { toFun := Subtype.val
      invFun := fun f => ⟨f, hA _ f⟩
      left_inv := fun _ => Subtype.ext rfl
      right_inv := fun _ => rfl }
  haveI : Finite (expAsm A RealizabilitySubobject.boolAsm).carrier :=
    Finite.of_equiv _ e.symm
  have hcard : Nat.card (expAsm A RealizabilitySubobject.boolAsm).carrier
      = 2 ^ Fintype.card A.carrier := by
    rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_fun,
      RealizabilitySubobject.boolAsm_card]
  unfold FitsIn
  rw [hcard]
  constructor
  · rintro ⟨-, hle⟩
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp hle
  · intro h
    exact ⟨inferInstance, (Nat.pow_le_pow_iff_right (by norm_num)).mpr h⟩

/-- §4.3 — **global Cartesian closure FAILS on capacity (cardinality) grounds.** For every capacity
`s ≥ 1` there is a fitting object `α` (`|α| = 2^s ≤ 2^s`) whose exponential — the function space
`α → α`, with `|α → α| = |α|^{|α|} = (2^s)^{2^s}` (§4.3's `|T₂|^{|T₁|}`) — **overflows** `2^s`. So no
fixed work memory is closed under the exponential, even though each exponential remains a perfectly
good finite set. (This `α → α` is exactly §4.3's function-space exponential `|T₂|^{|T₁|}`. For finite
assemblies every function is trackable, so the realizability exponential `expAsm α α` has the *same*
carrier `α → α` and overflows identically — that coincidence is true but not separately formalized
here, so we state the non-closure about the function space, the §4.3 quantity.) -/
theorem exp_card_overflow (s : ℕ) (hs : 1 ≤ s) :
    ∃ (α : Type) (_ : Fintype α), Nat.card α ≤ 2 ^ s ∧ 2 ^ s < Nat.card (α → α) := by
  refine ⟨Fin (2 ^ s), inferInstance, ?_, ?_⟩
  · rw [Nat.card_eq_fintype_card, Fintype.card_fin]
  · have hk : 1 < 2 ^ s := by
      calc 1 < 2 := by norm_num
        _ = 2 ^ 1 := (pow_one 2).symm
        _ ≤ 2 ^ s := Nat.pow_le_pow_right (by norm_num) hs
    rw [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_fin]
    exact Nat.lt_pow_self hk

end CapacityLayer
