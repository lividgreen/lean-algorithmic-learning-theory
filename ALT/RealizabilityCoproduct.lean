/-
Copyright (c) 2026 Mykola Palamarchuk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mykola Palamarchuk
-/
import ALT.Realizability
import ALT.RealizabilityCCC
import ALT.RecursorAlgebra

-- Formal-check file, not Mathlib-destined: opt out of the house-style linters.
set_option linter.style.header false
set_option linter.style.longLine false
-- Definitional `show` (unfolding assembly/algebra projections) is used idiomatically here.
set_option linter.style.show false

/-!
# Finite coproducts in the realizability category `Asm`, and the recursor's initial-algebra
universal property ON THE GENUINE CARRIER ([Decoupling] §4, §5; upstreamable)

Provenance: [Decoupling] §4 (Rep(S) as a realizability category) and
§5 (the bounded recursor). `ALT/RealizabilityCCC.lean` (FV-12) built the genuine carrier
`RealizabilityCCC.Asm` — assemblies over Kleene's first PCA (`Nat.Partrec.Code`) — and proved it
**Cartesian closed** (terminal + products + exponentials). This file adds the missing **finite
coproducts** (initial object + binary coproduct with its copairing universal property) and uses them
to lift the FV-18 discriminating initial `𝟙 ⊕ (·)`-algebra of `ALT/RecursorAlgebra.lean` from the
`Type` stand-in onto **the same carrier `Asm`** as the CCC and the §6.3 checkers.

## Why this is new infrastructure (upstreamable)
The 2026 realizability sweep found **no** realizability-coproduct in Lean/Mathlib (nor a realizability
category at all beyond what FV-11/FV-12 built here). Coproducts of assemblies are the standard "tagged
union" construction: a realizer of a left/right injection is a code carrying a **tag** (`0`/`1`, via
`Nat.pair`) alongside a realizer of the injected element; copairing runs one of two realizers
according to the tag (`Partrec.cond`). We build that layer directly on `Nat.Partrec.Code`, reusing the
FV-11 universal machinery (`exists_code`, `Code.eval_part`). It is genuinely upstreamable.

## What this establishes
* `initialAsm` — the empty assembly; `initialAsm_isInitial` : it is an **initial object** of `Asm`
  (the unique map out is `Empty.elim`, trackable vacuously; uniqueness is `Empty → B` subsingleton).
* `coprodAsm A B` — the binary coproduct: carrier `A ⊕ B`, a code realizes `inl a` iff it is
  `Nat.pair 0 (a-realizer)` and `inr b` iff `Nat.pair 1 (b-realizer)`.
* `inl`/`inr` are **tracked** morphisms, and `coprod_universal` is the copairing universal property —
  existence **and** uniqueness of the mediating realized morphism `[f, g] : A ⊕ B ⟶ C`.
* `succEndoAsm : Asm ⥤ Asm`, the endofunctor `X ↦ 𝟙 ⊕ X` (`𝟙 = terminalAsm`) — it exists precisely
  *because* coproducts now do — and `boundedInitialAlgebraAsm_isInitial` : the finite saturating
  recursor is a **genuine, discriminating** initial `𝟙 ⊕ (·)`-algebra in the saturating subcategory,
  now on `Asm` (honest algebra-hom morphisms, uniqueness a real orbit induction — the FV-18 headline
  transported to the carrier that also carries the CCC).

## Honest boundary
`boundedInitialAlgebraAsm_isInitial` is initial **only** in the saturating subcategory `SatAlgAsm M`,
never in all of `Endofunctor.Algebra succEndoAsm`: the unrestricted initial `𝟙 ⊕ (·)`-algebra is the
infinite `ℕ`, and `ParameterizedNNO.no_true_nno` forbids a true NNO on a finite carrier (mirrored
here by `finAsm` being finite). This is exactly the same honest boundary as the `Type`-level FV-18;
the upgrade is that the carrier is now the genuine PCA-realizability `Asm`.
-/

namespace RealizabilityCoproduct

open RealizabilityCCC Nat.Partrec CategoryTheory CategoryTheory.Limits

/-! ### The initial object: the empty assembly -/

/-- The **initial assembly**: the empty carrier. Realizability is vacuous, and the unique map out of
it (`Empty.elim`) is trackable by any code. This is the standard initial object of a category of
assemblies. -/
def initialAsm : Asm where
  carrier := Empty
  realizes := fun _ x => x.elim
  realized := fun x => x.elim

/-- **`initialAsm` is an initial object of `Asm`.** For every assembly `B` the unique morphism
`initialAsm ⟶ B` has underlying map `Empty.elim`, trackable vacuously (no element of `Empty` has a
realizer, so *every* code tracks it — we pick `idCode`); uniqueness is `Empty → B.carrier` being a
subsingleton. -/
def initialAsm_isInitial : IsInitial initialAsm :=
  IsInitial.ofUniqueHom
    (fun B => ⟨Empty.elim, idCode, fun x _ _ => x.elim⟩)
    (fun _ _ => by apply Subtype.ext; funext x; exact x.elim)

/-! ### Binary coproducts: the tagged-union assembly -/

/-- **Coproduct assembly** `A ⊕ B`: a code realizes `inl a` iff its first `Nat.pair` component is the
tag `0` and its second realizes `a`; symmetrically `inr b` with tag `1`. -/
def coprodAsm (A B : Asm) : Asm where
  carrier := A.carrier ⊕ B.carrier
  realizes n x :=
    match x with
    | Sum.inl a => n.unpair.1 = 0 ∧ A.realizes n.unpair.2 a
    | Sum.inr b => n.unpair.1 = 1 ∧ B.realizes n.unpair.2 b
  realized x := by
    cases x with
    | inl a =>
        obtain ⟨na, ha⟩ := A.realized a
        exact ⟨Nat.pair 0 na, by
          change (Nat.pair 0 na).unpair.1 = 0 ∧ A.realizes (Nat.pair 0 na).unpair.2 a
          rw [Nat.unpair_pair]; exact ⟨rfl, ha⟩⟩
    | inr b =>
        obtain ⟨nb, hb⟩ := B.realized b
        exact ⟨Nat.pair 1 nb, by
          change (Nat.pair 1 nb).unpair.1 = 1 ∧ B.realizes (Nat.pair 1 nb).unpair.2 b
          rw [Nat.unpair_pair]; exact ⟨rfl, hb⟩⟩

@[simp] theorem coprodAsm_realizes_inl (A B : Asm) (n : ℕ) (a : A.carrier) :
    (coprodAsm A B).realizes n (Sum.inl a) ↔ (n.unpair.1 = 0 ∧ A.realizes n.unpair.2 a) := Iff.rfl

@[simp] theorem coprodAsm_realizes_inr (A B : Asm) (n : ℕ) (b : B.carrier) :
    (coprodAsm A B).realizes n (Sum.inr b) ↔ (n.unpair.1 = 1 ∧ B.realizes n.unpair.2 b) := Iff.rfl

/-! ### The injection and copairing realizer codes -/

/-- A code that tags an argument with `0`: `r · n = ⟨0, n⟩`. Built from `Nat.pair 0 ·` via
`exists_code`. -/
theorem exists_inlCode : ∃ r : ℕ, ∀ n, ap r n = Part.some (Nat.pair 0 n) := by
  have hc : Computable (fun n => Nat.pair 0 n) :=
    (Primrec₂.natPair.comp (Primrec.const 0) Primrec.id).to_comp
  obtain ⟨c, hc'⟩ := Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp hc)
  exact ⟨Encodable.encode c, fun n => by rw [ap_encode]; exact congrFun hc' n⟩

/-- A code that tags an argument with `1`: `r · n = ⟨1, n⟩`. -/
theorem exists_inrCode : ∃ r : ℕ, ∀ n, ap r n = Part.some (Nat.pair 1 n) := by
  have hc : Computable (fun n => Nat.pair 1 n) :=
    (Primrec₂.natPair.comp (Primrec.const 1) Primrec.id).to_comp
  obtain ⟨c, hc'⟩ := Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp hc)
  exact ⟨Encodable.encode c, fun n => by rw [ap_encode]; exact congrFun hc' n⟩

/-- The **copairing realizer**: a single code that reads the tag `n.unpair.1` and runs `rf` on the
payload if the tag is `0`, else `rg`. Built by *arithmetically selecting* the realizer code
(`Primrec.ite` at the ℕ level) and feeding it to the FV-11 universal evaluator
`Realizability.universal_evaluator`. -/
theorem exists_copairCode (rf rg : ℕ) :
    ∃ r : ℕ, ∀ n, ap r n =
      (if n.unpair.1 = 0 then ap rf n.unpair.2 else ap rg n.unpair.2) := by
  obtain ⟨E, hE⟩ := Realizability.universal_evaluator
  have hsel : PrimrecPred (fun n : ℕ => n.unpair.1 = 0) :=
    Primrec.eq.comp (Primrec.fst.comp Primrec.unpair) (Primrec.const 0)
  have harg : Computable (fun n : ℕ => Nat.pair (if n.unpair.1 = 0 then rf else rg) n.unpair.2) :=
    (Primrec₂.natPair.comp
      (Primrec.ite hsel (Primrec.const rf) (Primrec.const rg))
      (Primrec.snd.comp Primrec.unpair)).to_comp
  have hpf : Partrec
      (fun n : ℕ => E.eval (Nat.pair (if n.unpair.1 = 0 then rf else rg) n.unpair.2)) :=
    Code.eval_part.comp (Computable.const E) harg
  obtain ⟨c, hc'⟩ := Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp hpf)
  refine ⟨Encodable.encode c, fun n => ?_⟩
  rw [ap_encode, congrFun hc' n]
  by_cases h : n.unpair.1 = 0
  · simp only [if_pos h]
    have hEr := hE (Denumerable.ofNat Code rf) n.unpair.2
    rw [Denumerable.encode_ofNat] at hEr
    exact hEr
  · simp only [if_neg h]
    have hEr := hE (Denumerable.ofNat Code rg) n.unpair.2
    rw [Denumerable.encode_ofNat] at hEr
    exact hEr

/-- Chosen injection/copairing codes (realizers are values; `.choose` uses only `Classical.choice`). -/
noncomputable def inlCode : ℕ := exists_inlCode.choose
noncomputable def inrCode : ℕ := exists_inrCode.choose
noncomputable def copairCode (rf rg : ℕ) : ℕ := (exists_copairCode rf rg).choose

theorem ap_inlCode (n : ℕ) : ap inlCode n = Part.some (Nat.pair 0 n) := exists_inlCode.choose_spec n
theorem ap_inrCode (n : ℕ) : ap inrCode n = Part.some (Nat.pair 1 n) := exists_inrCode.choose_spec n

theorem ap_copairCode (rf rg n : ℕ) :
    ap (copairCode rf rg) n =
      (if n.unpair.1 = 0 then ap rf n.unpair.2 else ap rg n.unpair.2) :=
  (exists_copairCode rf rg).choose_spec n

/-! ### Injections and copairing are tracked -/

/-- The left injection `Sum.inl` is tracked, by `inlCode` (tag `0`). -/
theorem tracks_inl (A B : Asm) : Tracks A (coprodAsm A B) inlCode Sum.inl := by
  intro a n hn
  refine ⟨Nat.pair 0 n, by rw [ap_inlCode]; exact Part.mem_some _, ?_⟩
  rw [coprodAsm_realizes_inl, Nat.unpair_pair]
  exact ⟨rfl, hn⟩

/-- The right injection `Sum.inr` is tracked, by `inrCode` (tag `1`). -/
theorem tracks_inr (A B : Asm) : Tracks B (coprodAsm A B) inrCode Sum.inr := by
  intro b n hn
  refine ⟨Nat.pair 1 n, by rw [ap_inrCode]; exact Part.mem_some _, ?_⟩
  rw [coprodAsm_realizes_inr, Nat.unpair_pair]
  exact ⟨rfl, hn⟩

/-- Copairing preserves tracking: if `rf` tracks `f : A → C` and `rg` tracks `g : B → C`, then
`copairCode rf rg` tracks `[f, g] = Sum.elim f g : A ⊕ B → C`. -/
theorem tracks_copair {A B C : Asm} {rf rg : ℕ} {f : A.carrier → C.carrier} {g : B.carrier → C.carrier}
    (hrf : Tracks A C rf f) (hrg : Tracks B C rg g) :
    Tracks (coprodAsm A B) C (copairCode rf rg) (Sum.elim f g) := by
  intro x n hn
  cases x with
  | inl a =>
      rw [coprodAsm_realizes_inl] at hn
      obtain ⟨htag, ha⟩ := hn
      obtain ⟨m, hm, hc⟩ := hrf a n.unpair.2 ha
      refine ⟨m, ?_, hc⟩
      rw [ap_copairCode, if_pos htag]
      exact hm
  | inr b =>
      rw [coprodAsm_realizes_inr] at hn
      obtain ⟨htag, hb⟩ := hn
      obtain ⟨m, hm, hc⟩ := hrg b n.unpair.2 hb
      refine ⟨m, ?_, hc⟩
      rw [ap_copairCode, if_neg (by omega)]
      exact hm

/-! ### The coproduct as a categorical object of `Asm` -/

/-- The left injection as a morphism `A ⟶ A ⊕ B`. -/
def inl (A B : Asm) : A ⟶ coprodAsm A B := ⟨Sum.inl, inlCode, tracks_inl A B⟩

/-- The right injection as a morphism `B ⟶ A ⊕ B`. -/
def inr (A B : Asm) : B ⟶ coprodAsm A B := ⟨Sum.inr, inrCode, tracks_inr A B⟩

/-- The copairing (mediating) morphism `[f, g] : A ⊕ B ⟶ C`. -/
noncomputable def copair {A B C : Asm} (f : A ⟶ C) (g : B ⟶ C) : coprodAsm A B ⟶ C :=
  ⟨Sum.elim f.1 g.1, copairCode f.2.choose g.2.choose,
    tracks_copair f.2.choose_spec g.2.choose_spec⟩

@[simp] theorem inl_apply (A B : Asm) (a : A.carrier) : (inl A B).1 a = Sum.inl a := rfl
@[simp] theorem inr_apply (A B : Asm) (b : B.carrier) : (inr A B).1 b = Sum.inr b := rfl
@[simp] theorem copair_apply {A B C : Asm} (f : A ⟶ C) (g : B ⟶ C) (x : A.carrier ⊕ B.carrier) :
    (copair f g).1 x = Sum.elim f.1 g.1 x := rfl

/-- **The copairing universal property (finite coproduct on the genuine carrier).** For every pair
`f : A ⟶ C`, `g : B ⟶ C` there is a *unique* realized morphism `u : A ⊕ B ⟶ C` with
`u ∘ inl = f` and `u ∘ inr = g` (stated pointwise). Existence is `copair f g`; uniqueness is
extensional (morphism equality in `Asm` is function equality, the realizer existentially quantified),
by cases on `Sum`. -/
theorem coprod_universal {A B C : Asm} (f : A ⟶ C) (g : B ⟶ C) :
    ∃! u : coprodAsm A B ⟶ C,
      (∀ a, u.1 (Sum.inl a) = f.1 a) ∧ (∀ b, u.1 (Sum.inr b) = g.1 b) := by
  refine ⟨copair f g, ⟨fun _ => rfl, fun _ => rfl⟩, ?_⟩
  intro t ht
  apply Subtype.ext
  funext x
  cases x with
  | inl a => exact ht.1 a
  | inr b => exact ht.2 b

/-! ## FV-18 on the genuine carrier: the endofunctor `X ↦ 𝟙 ⊕ X` and its initial algebra

With coproducts in hand, the endofunctor `X ↦ 𝟙 ⊕ X` (`𝟙 = terminalAsm`) exists on `Asm`, so the
`ALT/RecursorAlgebra.lean` discriminating initial `𝟙 ⊕ (·)`-algebra (FV-18) can be restated on the
**same carrier** as the CCC (`RealizabilityCCC.lean`) and the §6.3 checkers — no longer the `Type`
stand-in. As in FV-18 the initial object lives only in the *saturating* subcategory (a finite carrier
is never a true NNO; `ParameterizedNNO.no_true_nno`), and the successor saturates rather than wraps. -/

/-- The endofunctor `F X = 𝟙 ⊕ X` on `Asm` (`𝟙 = terminalAsm`). Its functorial action on a morphism
`g` is `[inl, inr ∘ g]` — built from the copairing universal property, so trackability is inherited. -/
noncomputable def succEndoAsm : Asm ⥤ Asm where
  obj X := coprodAsm terminalAsm X
  map {X Y} g := copair (inl terminalAsm Y) (g ≫ inr terminalAsm Y)
  map_id X := by apply Subtype.ext; funext x; cases x <;> rfl
  map_comp g h := by apply Subtype.ext; funext x; cases x <;> rfl

@[simp] theorem succEndoAsm_obj (X : Asm) : succEndoAsm.obj X = coprodAsm terminalAsm X := rfl

/-- The basepoint `z = str (inl ⋆)` of an `F`-algebra on `Asm`. -/
def zA (alg : Endofunctor.Algebra succEndoAsm) : alg.a.carrier :=
  alg.str.1 (Sum.inl PUnit.unit)

/-- The successor `s a = str (inr a)` of an `F`-algebra on `Asm`. -/
def sA (alg : Endofunctor.Algebra succEndoAsm) (a : alg.a.carrier) : alg.a.carrier :=
  alg.str.1 (Sum.inr a)

/-- **Saturation** on `Asm`-algebras: the `z`-orbit reaches an `s`-fixed point by step `M`. -/
def Sat (M : ℕ) (alg : Endofunctor.Algebra succEndoAsm) : Prop :=
  sA alg ((sA alg)^[M] (zA alg)) = (sA alg)^[M] (zA alg)

/-- The full subcategory of `Asm`-algebras satisfying `Sat M` (honest algebra-hom morphisms — not
thin). -/
abbrev SatAlgAsm (M : ℕ) : Type _ :=
  ObjectProperty.FullSubcategory (fun alg : Endofunctor.Algebra succEndoAsm => Sat M alg)

/-- The successor-square identity from `Sat` (the `Asm` analogue of `RecursorAlgebra.iterate_succ_sat`). -/
lemma iterate_succ_sat (M : ℕ) (alg : Endofunctor.Algebra succEndoAsm) (hsat : Sat M alg)
    (k : Fin (M + 1)) :
    sA alg ((sA alg)^[k.val] (zA alg)) = (sA alg)^[min (k.val + 1) M] (zA alg) := by
  rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp k.isLt) with hlt | heq
  · rw [min_eq_left (by omega : k.val + 1 ≤ M), Function.iterate_succ_apply']
  · rw [heq, min_eq_right (by omega : M ≤ M + 1)]
    exact hsat

/-! ### The finite carrier assembly and finite-domain trackability -/

/-- The finite assembly on `Fin (M+1)`, each element realized by (exactly) its own value. -/
def finAsm (M : ℕ) : Asm where
  carrier := Fin (M + 1)
  realizes n k := n = k.val
  realized k := ⟨k.val, rfl⟩

@[simp] theorem finAsm_realizes (M : ℕ) (n : ℕ) (k : Fin (M + 1)) :
    (finAsm M).realizes n k ↔ n = k.val := Iff.rfl

/-- **Finite-domain trackability.** Every function out of the finite assembly `finAsm M` is trackable
(a morphism of `Asm`) — the realizer is a finite table keyed on the input value, extracted via
`Realizability.tableFn` and `Nat.Partrec.Code.exists_code`. This is the `Asm`-level counterpart of
`Realizability.realizes_of_finite`, and it makes the bounded recursor a genuine morphism. -/
theorem trackable_of_finDom (M : ℕ) (B : Asm) (f : Fin (M + 1) → B.carrier) :
    Trackable (finAsm M) B f := by
  classical
  set pts : List (ℕ × ℕ) :=
    (Finset.univ.toList).map (fun k : Fin (M + 1) => (k.val, (B.realized (f k)).choose)) with hpts
  obtain ⟨c, hc⟩ :=
    Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp (Realizability.tableFn_primrec pts).to_comp)
  refine ⟨Encodable.encode c, fun (k : Fin (M + 1)) n hn => ?_⟩
  have hnk : n = k.val := hn
  subst hnk
  refine ⟨(B.realized (f k)).choose, ?_, (B.realized (f k)).choose_spec⟩
  rw [ap_encode]
  have hmem : (k.val, (B.realized (f k)).choose) ∈ pts := by
    rw [hpts, List.mem_map]
    exact ⟨k, Finset.mem_toList.mpr (Finset.mem_univ k), rfl⟩
  have huniq : ∀ k' v', (k', v') ∈ pts → k' = k.val → v' = (B.realized (f k)).choose := by
    intro k' v' hk'mem hk'eq
    rw [hpts, List.mem_map] at hk'mem
    obtain ⟨j, _, hj⟩ := hk'mem
    rw [Prod.mk.injEq] at hj
    obtain ⟨hj1, hj2⟩ := hj
    have hjk : j = k := Fin.val_injective (by rw [hj1, hk'eq])
    rw [← hj2, hjk]
  have hkey : Realizability.tableFn pts k.val = (B.realized (f k)).choose :=
    Realizability.tableFn_eval pts hmem huniq
  have heval : c.eval k.val = Part.some (Realizability.tableFn pts k.val) := by rw [hc]; rfl
  rw [heval, hkey]
  exact Part.mem_some _

/-- A constant-`0` code (`r · n = 0` for all `n`), the realizer of the algebra basepoint. -/
theorem exists_const0Code : ∃ r : ℕ, ∀ n, ap r n = Part.some 0 := by
  have hc : Computable (fun _ : ℕ => (0 : ℕ)) := (Primrec.const 0).to_comp
  obtain ⟨c, hc'⟩ := Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp hc)
  exact ⟨Encodable.encode c, fun n => by rw [ap_encode]; exact congrFun hc' n⟩

/-- The constant-`0` morphism `𝟙 ⟶ finAsm M` (the algebra basepoint as a realized map). -/
noncomputable def toZeroMor (M : ℕ) : terminalAsm ⟶ finAsm M :=
  ⟨fun _ => (0 : Fin (M + 1)), exists_const0Code.choose, by
    intro _ n _
    refine ⟨0, by rw [exists_const0Code.choose_spec]; exact Part.mem_some _, ?_⟩
    rw [finAsm_realizes]; simp⟩

/-- The saturating-successor morphism `finAsm M ⟶ finAsm M` (tracked by finite-domain lookup). -/
noncomputable def boundedSuccMor (M : ℕ) : finAsm M ⟶ finAsm M :=
  ⟨RecursorAlgebra.boundedSucc M, trackable_of_finDom M (finAsm M) (RecursorAlgebra.boundedSucc M)⟩

/-- **The bounded algebra on `Asm`.** Carrier `finAsm M`; structure map the copairing of the
basepoint `𝟙 ⟶ finAsm M` and the saturating successor `finAsm M ⟶ finAsm M` — so it lives on the
genuine PCA-realizability carrier. -/
noncomputable def boundedAlgAsm (M : ℕ) : Endofunctor.Algebra succEndoAsm where
  a := finAsm M
  str := copair (toZeroMor M) (boundedSuccMor M)

theorem sA_boundedAlgAsm_eq (M : ℕ) : sA (boundedAlgAsm M) = RecursorAlgebra.boundedSucc M := rfl
theorem zA_boundedAlgAsm_eq (M : ℕ) : zA (boundedAlgAsm M) = (0 : Fin (M + 1)) := rfl

/-- The orbit value climbs and saturates (`Asm` analogue of `RecursorAlgebra.boundedAlg_orbit_val`). -/
lemma boundedAlgAsm_orbit_val (M n : ℕ) :
    ((sA (boundedAlgAsm M))^[n] (zA (boundedAlgAsm M))).val = min n M := by
  induction n with
  | zero => rw [zA_boundedAlgAsm_eq]; simp
  | succ n ih =>
      rw [Function.iterate_succ_apply', sA_boundedAlgAsm_eq]
      change min (((sA (boundedAlgAsm M))^[n] (zA (boundedAlgAsm M))).val + 1) M = min (n + 1) M
      rw [ih]; omega

/-- The candidate algebra is orbit-saturating. -/
lemma boundedAlgAsm_sat (M : ℕ) : Sat M (boundedAlgAsm M) := by
  have hM : (sA (boundedAlgAsm M))^[M] (zA (boundedAlgAsm M)) = Fin.last M := by
    apply Fin.ext; rw [boundedAlgAsm_orbit_val, Fin.val_last]; omega
  show sA (boundedAlgAsm M) ((sA (boundedAlgAsm M))^[M] (zA (boundedAlgAsm M)))
      = (sA (boundedAlgAsm M))^[M] (zA (boundedAlgAsm M))
  rw [hM, sA_boundedAlgAsm_eq]
  exact RecursorAlgebra.boundedSucc_last M

/-! ### The unique morphism out: the bounded recursor `k ↦ sᵏ z` -/

/-- The underlying map of the unique morphism `boundedAlgAsm M ⟶ alg`: the bounded recursor
`k ↦ sᵏ z` (the saturating `Fin` counterpart of `ParameterizedNNO.cyclicParamNNO`). -/
noncomputable def recFn (M : ℕ) (alg : Endofunctor.Algebra succEndoAsm) : Fin (M + 1) → alg.a.carrier :=
  fun k => (sA alg)^[k.val] (zA alg)

@[simp] lemma recFn_zero (M : ℕ) (alg : Endofunctor.Algebra succEndoAsm) :
    recFn M alg 0 = zA alg := by simp [recFn]

/-- The bounded recursor as a *realized* morphism `finAsm M ⟶ alg.a` — tracked by finite-domain
lookup (`trackable_of_finDom`), so it is a genuine morphism of the realizability category. -/
noncomputable def recMor (M : ℕ) (alg : Endofunctor.Algebra succEndoAsm) : finAsm M ⟶ alg.a :=
  ⟨recFn M alg, trackable_of_finDom M alg.a (recFn M alg)⟩

/-- The bounded recursor **is** an algebra homomorphism `boundedAlgAsm M ⟶ alg`, for every saturating
`alg` (existence half of initiality). The pointwise recursor square uses `iterate_succ_sat` at the
saturating endpoint. -/
noncomputable def toSatHomAsm (M : ℕ) (alg : Endofunctor.Algebra succEndoAsm) (hsat : Sat M alg) :
    boundedAlgAsm M ⟶ alg where
  f := recMor M alg
  h := by
    apply Subtype.ext
    funext x
    show alg.str.1 ((succEndoAsm.map (recMor M alg)).1 x)
        = (recMor M alg).1 ((boundedAlgAsm M).str.1 x)
    cases x with
    | inl u =>
        cases u
        show zA alg = recFn M alg 0
        rw [recFn_zero]
    | inr k =>
        show sA alg ((sA alg)^[k.val] (zA alg)) = (sA alg)^[min (k.val + 1) M] (zA alg)
        exact iterate_succ_sat M alg hsat k

lemma toSatHomAsm_f_apply (M : ℕ) (alg : Endofunctor.Algebra succEndoAsm) (hsat : Sat M alg)
    (k : Fin (M + 1)) : (toSatHomAsm M alg hsat).f.1 k = (sA alg)^[k.val] (zA alg) := rfl

/-! ### Uniqueness: a genuine orbit induction (not `Subsingleton`) -/

/-- The algebra-hom law of `g`, read pointwise on the underlying functions. -/
lemma hom_pointwise (M : ℕ) (alg : Endofunctor.Algebra succEndoAsm) (g : boundedAlgAsm M ⟶ alg)
    (x : PUnit ⊕ Fin (M + 1)) :
    alg.str.1 ((succEndoAsm.map g.f).1 x) = g.f.1 ((boundedAlgAsm M).str.1 x) :=
  congrArg (fun m => m.1 x) g.h

/-- The `inl`-square: `g 0 = z`. -/
lemma hom_zero (M : ℕ) (alg : Endofunctor.Algebra succEndoAsm) (g : boundedAlgAsm M ⟶ alg) :
    g.f.1 (0 : Fin (M + 1)) = zA alg := (hom_pointwise M alg g (Sum.inl PUnit.unit)).symm

/-- The `inr`-square: `g (succ k) = s (g k)`. -/
lemma hom_succ (M : ℕ) (alg : Endofunctor.Algebra succEndoAsm) (g : boundedAlgAsm M ⟶ alg)
    (k : Fin (M + 1)) : g.f.1 (RecursorAlgebra.boundedSucc M k) = sA alg (g.f.1 k) :=
  (hom_pointwise M alg g (Sum.inr k)).symm

/-- **Uniqueness on the orbit** (a genuine induction): any algebra hom `g : boundedAlgAsm M ⟶ alg`
has `g.f.1 ⟨n, _⟩ = sⁿ z`. Base: `inl`-square; step: `inr`-square at `n < M` (there the saturating
successor is the honest `n+1`). -/
lemma hom_f_orbit (M : ℕ) (alg : Endofunctor.Algebra succEndoAsm) (g : boundedAlgAsm M ⟶ alg) :
    ∀ (n : ℕ) (hn : n < M + 1), g.f.1 (⟨n, hn⟩ : Fin (M + 1)) = (sA alg)^[n] (zA alg) := by
  intro n
  induction n with
  | zero =>
      intro hn
      have h0 : (⟨0, hn⟩ : Fin (M + 1)) = (0 : Fin (M + 1)) := by apply Fin.ext; simp
      rw [h0, Function.iterate_zero_apply]
      exact hom_zero M alg g
  | succ n ih =>
      intro hn
      have hn' : n < M + 1 := by omega
      have hlt : n < M := by omega
      have hpt : RecursorAlgebra.boundedSucc M (⟨n, hn'⟩ : Fin (M + 1)) = (⟨n + 1, hn⟩ : Fin (M + 1)) := by
        apply Fin.ext
        change min (n + 1) M = n + 1
        omega
      have hs := hom_succ M alg g (⟨n, hn'⟩ : Fin (M + 1))
      rw [hpt] at hs
      rw [hs, ih hn', Function.iterate_succ_apply']

/-- Consequently `g.f = recMor M alg` for every algebra hom `g` (the underlying maps agree on the
whole orbit `Fin (M+1)`), so the mediating morphism is unique. -/
lemma hom_f_eq_rec (M : ℕ) (alg : Endofunctor.Algebra succEndoAsm) (g : boundedAlgAsm M ⟶ alg) :
    g.f = recMor M alg := by
  apply Subtype.ext
  funext k
  show g.f.1 k = (sA alg)^[k.val] (zA alg)
  exact hom_f_orbit M alg g k.val k.isLt

/-! ### The discriminating initiality on the genuine carrier -/

/-- The candidate as an object of the saturating subcategory `SatAlgAsm M`. -/
noncomputable def boundedInitialAlgebraAsm (M : ℕ) : SatAlgAsm M where
  obj := boundedAlgAsm M
  property := boundedAlgAsm_sat M

/-- **FV-18 on the genuine carrier (headline).** `boundedInitialAlgebraAsm M` is a *genuine*
`IsInitial` object of the saturating full subcategory `SatAlgAsm M` of
`Endofunctor.Algebra succEndoAsm`, where `succEndoAsm` is the endofunctor `X ↦ 𝟙 ⊕ X` on the
realizability category `Asm` (the same carrier as the CCC of `RealizabilityCCC.lean`). Discharged via
`IsInitial.ofUniqueHom`: existence is the recursor hom `toSatHomAsm`, uniqueness is the orbit
induction `hom_f_eq_rec`.

Honesty (as in the `Type`-level FV-18): morphisms here are honest algebra homomorphisms (tracked
functions commuting with the structure map), **not** `Prop`s, so uniqueness is a real induction over
the orbit; and initiality holds **only** in the saturating subcategory — the unrestricted initial
`𝟙 ⊕ (·)`-algebra is the infinite `ℕ`, and `ParameterizedNNO.no_true_nno` forbids a true NNO on a
finite carrier (recorded by `boundedAlgAsm_str_not_injective`: the structure map is not injective,
hence not a Lambek iso). -/
noncomputable def boundedInitialAlgebraAsm_isInitial (M : ℕ) :
    IsInitial (boundedInitialAlgebraAsm M) :=
  IsInitial.ofUniqueHom
    (fun Y => ObjectProperty.homMk (toSatHomAsm M Y.obj Y.property))
    (fun Y m => by
      apply ObjectProperty.hom_ext
      apply Endofunctor.Algebra.ext
      exact hom_f_eq_rec M Y.obj m.hom)

/-- **Honesty (Lambek does not apply here).** The structure map of `boundedAlgAsm M` is not injective
(its domain `𝟙 ⊕ Fin (M+1)` has `M+2` elements, its codomain `M+1`), hence not an isomorphism. So the
finite initial object of the saturating subcategory is *not* a Lambek fixed point — the same
finite-capacity obstruction (`ParameterizedNNO.no_true_nno`) as the `Type`-level FV-18. -/
theorem boundedAlgAsm_str_not_injective (M : ℕ) :
    ¬ Function.Injective (boundedAlgAsm M).str.1 := by
  intro hinj
  have hle : Fintype.card (PUnit.{1} ⊕ Fin (M + 1)) ≤ Fintype.card (Fin (M + 1)) :=
    Fintype.card_le_of_injective
      (show PUnit.{1} ⊕ Fin (M + 1) → Fin (M + 1) from (boundedAlgAsm M).str.1) hinj
  simp only [Fintype.card_sum, Fintype.card_fin, Fintype.card_punit] at hle
  omega

end RealizabilityCoproduct
