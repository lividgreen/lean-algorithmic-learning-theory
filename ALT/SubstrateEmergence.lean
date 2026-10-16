module

public import ALT.SubstrateClass
public import ALT.PersistenceCapacity
public import ALT.AccretingExcess


/-!
# The class-level `𝒮_E` constructor ([Inevitability] §2 Definition 2.3)

`BlockPairHost.witness_substrateE` builds `𝒮_E` membership for one host, and its proof is
host-specific in exactly one field — the read-only code region (`s1`); every other field is a
statement about `(κ, gTS)` alone, or about a packed update `(U, θ)` alone, with the host's own
name entering nowhere. This module extracts that observation as a theorem: for ANY decoupled
system `(U, R)`, any packing onto a numeral carrier, and any frame surjective off the packed
update's own iterate, `SubstrateE` follows from the numeral conditions and one crossing hypothesis
— [Inevitability] §2 Definition 2.3's ruled sentence, "met by a decoupled cheap reversible world of
sufficient capacity," read as a theorem rather than a remark.

The tie between the packed update and the system's own update is BY CONSTRUCTION: `SubstrateE`'s
two emergence fields are carried `Prop` parameters, so a constructor over an untied endofunction
would type-check against them and prove nothing about `U` itself. `packedUpdate` is defined FROM
`U` and the packing equivalence, mirroring `BlockPairHost.packed`'s own shape.

## Main results

* `packedUpdate`, `packedUpdate_iterate` — the packed update, defined from a system's own update
  and a packing equivalence onto a numeral carrier, and the one transport law its orbit needs.
* `GrowsLawfulGuestOf`, `growsLawfulGuestOf_of_surj` — the growth clause
  ([Guests] §6 Theorem 6.1's own shape), parametric in the packed update and the frame, discharged
  from surjectivity of the frame off the update's own iterate.
* `GrownGuestReachesThresholdAt`, `grownGuestReachesThresholdAt_uniform` — the crossing clause, at
  a Gödel size fixed once across every capacity, a Gödel size every sufficiently large capacity
  hosts.
* `substrateE_of_emergence` — the constructor: `Fixes U R`, a packing equivalence, a frame
  surjective off the packed update's own iterate, the numeral conditions, and the crossing
  hypothesis together give `SubstrateE U R …`.
* `substrateE_of_perm` — the reversible corollary, Definition 2.3's own sentence: a bijective `U`
  and a surjective frame suffice, since a packed permutation's iterate is again a bijection and any
  surjective frame is surjective off it.

## Scope

The constructor takes `R` as given: whether a particular world's region is an honest code region —
one the update actually reads, rather than an inert region satisfying `Fixes` vacuously
([Decoupling] §2 Definition 2.1's own vacuity remark on `R = ∅`) — is the instance's business, not
this module's. Nothing here says anything about survival: `SubstrateE` carries none, by the
author's ruling recorded in [Inevitability] §2 Definition 2.3. The growth clause is stated in
[Guests] Theorem 6.1's own currency — the codes for the packed rule and the frame are hypotheses,
not built objects — so no absolute cheapness is claimed at class level; [Inevitability] Theorem
5.8's block-pair host prices ONE instance's codes separately (row IN-39). This is not the
profile-class `𝒮_L` criterion, and it is not the class-level bridge: a membership constructor
relates no learning-world count to any guest-world bit.

Anchors: [Inevitability] §2 Definition 2.3, §5 Remark 5.6, §5 Theorem 5.8, [Guests] §6 Theorem 6.1,
[Decoupling] §2 Definition 2.1, rows IN-5, IN-38.
-/


@[expose] public section

namespace ALT

open Equiv MulAction
open RealizabilityCCC
open AdditiveComplexity
open FFL.FirstOrder FFL.FirstOrder.Arithmetic

attribute [local instance] arrowAction

/-! ## The packed update, and the one transport law its orbit needs -/

/-- **The system's own update, packed onto a numeral carrier.** Defined FROM `U` and the packing
equivalence `e`, so the growth clause built on it is a statement about `U` itself, never about an
unrelated `Fin n` map — `BlockPairHost.packed`'s own shape, at a general carrier and a
general packing. -/
def packedUpdate {ι V : Type*} {n : ℕ} (e : ALT.Mem ι V ≃ Fin n)
    (U : ALT.Mem ι V → ALT.Mem ι V) : Fin n → Fin n :=
  fun s => e (U (e.symm s))

private lemma packedUpdate_apply {ι V : Type*} {n : ℕ} (e : ALT.Mem ι V ≃ Fin n)
    (U : ALT.Mem ι V → ALT.Mem ι V) (x : ALT.Mem ι V) :
    packedUpdate e U (e x) = e (U x) := by
  rw [packedUpdate, Equiv.symm_apply_apply]

/-- **Orbits survive the packing**: `t` steps of the packed update from a packed state are the
packing of `t` steps of the system's own update. -/
theorem packedUpdate_iterate {ι V : Type*} {n : ℕ} (e : ALT.Mem ι V ≃ Fin n)
    (U : ALT.Mem ι V → ALT.Mem ι V) (t : ℕ) (x : ALT.Mem ι V) :
    (packedUpdate e U)^[t] (e x) = e (U^[t] x) := by
  induction t with
  | zero => simp
  | succ t ih =>
      rw [Function.iterate_succ_apply', ih, packedUpdate_apply, Function.iterate_succ_apply']

/-- **A packed bijection is a bijection.** `packedUpdate e U` is `e ∘ U ∘ e.symm`, a composite of
bijections whenever `U` is one. -/
theorem packedUpdate_bijective {ι V : Type*} {n : ℕ} (e : ALT.Mem ι V ≃ Fin n)
    {U : ALT.Mem ι V → ALT.Mem ι V} (hU : Function.Bijective U) :
    Function.Bijective (packedUpdate e U) :=
  e.bijective.comp (hU.comp e.symm.bijective)

/-! ## The growth clause, at [Guests] Theorem 6.1's own shape -/

/-- **The growth clause** ([Guests] §6 Theorem 6.1's own shape, [Inevitability] §2 Definition 2.3's
first clause), parametric in the packed update `U` and the frame `θ` —
`BlockPairHost.GrowsLawfulGuest`'s body at a general `(U, θ)`. Parametric in the codes `cU`, `cθ`:
owned at
the update's own description cost, no absolute cheapness claimed. -/
def GrowsLawfulGuestOf {n m : ℕ} (U : Fin n → Fin n) (θ : Fin n → Fin m) : Prop :=
  ALT.Carries U (ALT.emergeLens U θ) ∧
    ∀ cU cθ : Nat.Partrec.Code,
      cU.eval 0 = Part.some (ALT.lensCode U) →
      cθ.eval 0 = Part.some (ALT.lensCode θ) →
      Nat.card ↥(orbit (Perm ↥(ALT.core U))
          (ALT.coreLens U (ALT.emergeLens U θ 0)))
        ≤ ALT.CbHue U
            (AdditiveComplexity.elen ALT.emergeBuilder + AdditiveComplexity.elen cU
              + AdditiveComplexity.elen cθ + 30)

/-- **The growth clause, discharged from surjectivity off the update's own iterate.**
[Guests] §6 Theorem 6.1: a reference frame surjective off the `n`-th iterate reads a full model off
the recurrent core, and both conjuncts of `GrowsLawfulGuestOf` are `ALT.emergence`
applied to `(U, θ)`. -/
theorem growsLawfulGuestOf_of_surj {n m : ℕ} {U : Fin n → Fin n} {θ : Fin n → Fin m}
    (hsurj : Function.Surjective (fun s => θ (U^[n] s))) :
    GrowsLawfulGuestOf U θ :=
  ⟨ALT.carries_emergeLens U θ hsurj,
    fun cU cθ hU hθ => (ALT.emergence U θ cU cθ hsurj hU hθ).2⟩

/-! ## The crossing clause: a Gödel size every sufficiently large capacity hosts -/

/-- **The crossing clause** ([Inevitability] §5 Theorem 5.1(a)'s own standard), parametric in the
capacity `κ` — `BlockPairHost.GrownGuestReachesThreshold`'s body at a general `κ`. -/
def GrownGuestReachesThresholdAt (κ gTS : ℕ) : Prop :=
  (∀ g, ALT.hostsAt κ g → ALT.hostsThreshold κ g) ∧
    (∀ Mchk, ALT.hostsAt κ gTS → gTS < Mchk → Mchk ≤ gTS ^ 2 →
      ∃ R : ReflectiveAsm gTS, R.depth = Mchk ∧
        ALT.FitsIn (recursorAsm R.depth) κ ∧
        ∃ N, ALT.RepresentsUnderivableTruth (Encodable.encode : Sentence ℒₒᵣ → ℕ)
          (fun δ => (𝗣𝗔⁻ : ArithmeticTheory) ⊢ δ) (fun δ => ℕ↓[ℒₒᵣ] ⊧ δ) N)

/-- **A Gödel size fixed once, that every sufficiently hosting capacity represents** —
`BlockPairHost.grownGuestReachesThreshold`'s content with the host's own bit count
generalized to an arbitrary `κ`. From `ALT.outgrows_paMinus_uniform`'s own `gTS`,
obtained outside any particular capacity. -/
theorem grownGuestReachesThresholdAt_uniform :
    ∃ gTS, ∀ κ, GrownGuestReachesThresholdAt κ gTS := by
  obtain ⟨gTS, hgTS⟩ := ALT.outgrows_paMinus_uniform
  refine ⟨gTS, fun κ => ?_⟩
  exact ⟨fun g h => ALT.hostsThreshold_of_capacity h,
    fun Mchk h1 h2 h3 => hgTS κ Mchk h1 h2 h3⟩

/-! ## The constructor -/

/-- **The class-level `𝒮_E` constructor.** For any decoupled `(U, R)`, any packing `e` onto a
numeral carrier, and any frame `θ` surjective off the packed update's own `n`-th iterate, the
numeral conditions `(S2)`/`(S3)` and one crossing hypothesis at the packed update's own capacity
`κ` together give `SubstrateE`. `BlockPairHost.witness_substrateE`'s proof is this theorem's proof
term with the host's own names substituted for the hypotheses: `s1` is `hfix`, `s2`/`s3` are the
carried numeral conditions, `growsLawfulGuest` is `growsLawfulGuestOf_of_surj` applied to `hsurj`,
and
`grownGuestReachesThreshold` is `hE` itself. -/
theorem substrateE_of_emergence {ι V : Type*} (U : ALT.Mem ι V → ALT.Mem ι V)
    (R : Set ι) (hfix : ALT.Fixes U R) {n κ : ℕ} (e : ALT.Mem ι V ≃ Fin n)
    (θ : Fin n → Fin (2 ^ κ))
    (hsurj : Function.Surjective (fun s => θ ((packedUpdate e U)^[n] s)))
    (r K L c₀ c₁ c₂ δ : ℝ) (sCodeSize gTS : ℕ)
    (Consistent NSound Delta1Axiomatized InterpretsR0 : Prop)
    (hS2 : ALT.RegimeWithDepth r K L c₀ c₁ c₂ δ)
    (hS3 : ALT.ReflectiveCapacity K sCodeSize gTS
      Consistent NSound Delta1Axiomatized InterpretsR0)
    (hE : GrownGuestReachesThresholdAt κ gTS) :
    ALT.SubstrateE U R r K L c₀ c₁ c₂ δ sCodeSize gTS
      Consistent NSound Delta1Axiomatized InterpretsR0
      (GrowsLawfulGuestOf (packedUpdate e U) θ) (GrownGuestReachesThresholdAt κ gTS) :=
  { s1 := hfix
    s2 := hS2
    s3 := hS3
    growsLawfulGuest := growsLawfulGuestOf_of_surj hsurj
    grownGuestReachesThreshold := hE }

/-- **The reversible corollary — [Inevitability] §2 Definition 2.3's ruled sentence, machine-checked
at the class's own definition.** Every decoupled reversible finite world with a surjective `κ`-frame
at `κ` meeting the crossing hypothesis is in `𝒮_E`: "decoupled" is `Fixes U R`, "reversible" is
`Function.Bijective U` — under which the packed update is a bijection, its `n`-th iterate is a
bijection, and ANY surjective `θ` is surjective off it, `[Guests]` Theorem 6.1's core-size input met
because the core is everything — "sufficient capacity" is the crossing hypothesis at `κ` together
with the numeral conditions, and "cheap" is Theorem 6.1's own currency: the codes for the packed
rule and the frame are hypotheses of the growth clause, owned at
`elen cU + elen cθ + O(1)`, no absolute cheapness claimed at class level
([Inevitability] Theorem 5.8's host is priced separately, row IN-39). What this does NOT say,
because the adjective invites it: nothing about survival (`SubstrateE` carries none); nothing about
the honesty of `R` — the constructor takes `R` as given, and an inert region is `Fixes` for a
trivial reason ([Decoupling] §2 Definition 2.1's own vacuity remark); nothing about which frame is
cheap. -/
theorem substrateE_of_perm {ι V : Type*} (U : ALT.Mem ι V → ALT.Mem ι V)
    (R : Set ι) (hfix : ALT.Fixes U R) (hbij : Function.Bijective U)
    {n κ : ℕ} (e : ALT.Mem ι V ≃ Fin n) (θ : Fin n → Fin (2 ^ κ))
    (hθ : Function.Surjective θ)
    (r K L c₀ c₁ c₂ δ : ℝ) (sCodeSize gTS : ℕ)
    (Consistent NSound Delta1Axiomatized InterpretsR0 : Prop)
    (hS2 : ALT.RegimeWithDepth r K L c₀ c₁ c₂ δ)
    (hS3 : ALT.ReflectiveCapacity K sCodeSize gTS
      Consistent NSound Delta1Axiomatized InterpretsR0)
    (hE : GrownGuestReachesThresholdAt κ gTS) :
    ALT.SubstrateE U R r K L c₀ c₁ c₂ δ sCodeSize gTS
      Consistent NSound Delta1Axiomatized InterpretsR0
      (GrowsLawfulGuestOf (packedUpdate e U) θ) (GrownGuestReachesThresholdAt κ gTS) :=
  substrateE_of_emergence U R hfix e θ
    (hθ.comp ((packedUpdate_bijective e hbij).iterate n).surjective)
    r K L c₀ c₁ c₂ δ sCodeSize gTS Consistent NSound Delta1Axiomatized InterpretsR0 hS2 hS3 hE

end ALT
