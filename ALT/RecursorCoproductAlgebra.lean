module

public import Realizability.RealizabilityCoproduct
public import ALT.RecursorAlgebra


/-!
# The recursor's initial algebra on the genuine carrier `Asm` ([Decoupling] §4, §5)

The endofunctor `X ↦ 𝟙 ⊕ X` on the realizability category `RealizabilityCCC.Asm`, built from its
finite coproducts (`Realizability/RealizabilityCoproduct.lean`), and the discriminating initial
`𝟙 ⊕ (·)`-algebra of `ALT/RecursorAlgebra.lean` lifted onto that carrier: `succEndoAsm`,
`SatAlgAsm M`, and `boundedInitialAlgebraAsmIsInitial`, initial only in the saturating
subcategory.
-/


@[expose] public section

namespace ALT.AssemblyRecursorAlgebra

open RealizabilityCoproduct RealizabilityCCC Nat.Partrec CategoryTheory CategoryTheory.Limits

/-! ## FV-18 on the genuine carrier: the endofunctor `X ↦ 𝟙 ⊕ X` and its initial algebra

With coproducts in hand, the endofunctor `X ↦ 𝟙 ⊕ X` (`𝟙 = terminalAsm`) exists on `Asm`, so the
`ALT/RecursorAlgebra.lean` discriminating initial `𝟙 ⊕ (·)`-algebra (FV-18) can be restated on the
**same carrier** as the CCC (`RealizabilityCCC.lean`) and the §6.3 checkers — no longer the `Type`
stand-in. As in FV-18 the initial object lives only in the *saturating* subcategory (a finite
carrier is never a true NNO; `no_true_nno`), and the successor saturates rather
than wraps. -/

/-- The endofunctor `F X = 𝟙 ⊕ X` on `Asm` (`𝟙 = terminalAsm`). Its functorial action on a morphism
`g` is `[inl, inr ∘ g]` — built from the copairing universal property, so trackability is inherited.
-/
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

/-- The successor-square identity from `Sat` (the `Asm` analogue of
`TypeRecursorAlgebra.Sat.iterate_succ`). -/
lemma Sat.iterate_succ (M : ℕ) (alg : Endofunctor.Algebra succEndoAsm) (hsat : Sat M alg)
    (k : Fin (M + 1)) :
    sA alg ((sA alg)^[k.val] (zA alg)) = (sA alg)^[min (k.val + 1) M] (zA alg) := by
  rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp k.isLt) with hlt | heq
  · rw [min_eq_left (by omega : k.val + 1 ≤ M), Function.iterate_succ_apply']
  · rw [heq, min_eq_right (by omega : M ≤ M + 1)]
    exact hsat

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
  ⟨TypeRecursorAlgebra.boundedSucc M,
    trackable_of_fin_dom M (finAsm M) (TypeRecursorAlgebra.boundedSucc M)⟩

/-- **The bounded algebra on `Asm`.** Carrier `finAsm M`; structure map the copairing of the
basepoint `𝟙 ⟶ finAsm M` and the saturating successor `finAsm M ⟶ finAsm M` — so it lives on the
genuine PCA-realizability carrier. -/
noncomputable def boundedAlgAsm (M : ℕ) : Endofunctor.Algebra succEndoAsm where
  a := finAsm M
  str := copair (toZeroMor M) (boundedSuccMor M)

theorem sA_boundedAlgAsm_eq (M : ℕ) :
    sA (boundedAlgAsm M) = TypeRecursorAlgebra.boundedSucc M := rfl
theorem zA_boundedAlgAsm_eq (M : ℕ) : zA (boundedAlgAsm M) = (0 : Fin (M + 1)) := rfl

/-- The orbit value climbs and saturates (`Asm` analogue of
`TypeRecursorAlgebra.boundedAlg_orbit_val`). -/
lemma boundedAlgAsm_orbit_val (M n : ℕ) :
    ((sA (boundedAlgAsm M))^[n] (zA (boundedAlgAsm M))).val = min n M := by
  induction n with
  | zero => rw [zA_boundedAlgAsm_eq]; simp; rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', sA_boundedAlgAsm_eq]
      change min (((sA (boundedAlgAsm M))^[n] (zA (boundedAlgAsm M))).val + 1) M = min (n + 1) M
      rw [ih]; omega

/-- The candidate algebra is orbit-saturating. -/
lemma boundedAlgAsm_sat (M : ℕ) : Sat M (boundedAlgAsm M) := by
  have hM : (sA (boundedAlgAsm M))^[M] (zA (boundedAlgAsm M)) = Fin.last M := by
    apply Fin.ext; rw [boundedAlgAsm_orbit_val, Fin.val_last]; omega
  change sA (boundedAlgAsm M) ((sA (boundedAlgAsm M))^[M] (zA (boundedAlgAsm M)))
      = (sA (boundedAlgAsm M))^[M] (zA (boundedAlgAsm M))
  rw [hM, sA_boundedAlgAsm_eq]
  exact TypeRecursorAlgebra.boundedSucc_last M

/-! ### The unique morphism out: the bounded recursor `k ↦ sᵏ z` -/

/-- The underlying map of the unique morphism `boundedAlgAsm M ⟶ alg`: the bounded recursor
`k ↦ sᵏ z` (the saturating `Fin` counterpart of `cyclicParamNNO`). -/
noncomputable def recFn (M : ℕ) (alg : Endofunctor.Algebra succEndoAsm) : Fin (M + 1) →
    alg.a.carrier :=
  fun k => (sA alg)^[k.val] (zA alg)

@[simp] lemma recFn_zero (M : ℕ) (alg : Endofunctor.Algebra succEndoAsm) :
    recFn M alg 0 = zA alg := by simp [recFn]

/-- The bounded recursor as a *realized* morphism `finAsm M ⟶ alg.a` — tracked by finite-domain
lookup (`trackable_of_fin_dom`), so it is a genuine morphism of the realizability category. -/
noncomputable def recMor (M : ℕ) (alg : Endofunctor.Algebra succEndoAsm) : finAsm M ⟶ alg.a :=
  ⟨recFn M alg, trackable_of_fin_dom M alg.a (recFn M alg)⟩

/-- The bounded recursor **is** an algebra homomorphism `boundedAlgAsm M ⟶ alg`, for every
saturating `alg` (existence half of initiality). The pointwise recursor square uses
`Sat.iterate_succ` at the saturating endpoint. -/
noncomputable def toSatHomAsm (M : ℕ) (alg : Endofunctor.Algebra succEndoAsm) (hsat : Sat M alg) :
    boundedAlgAsm M ⟶ alg where
  f := recMor M alg
  h := by
    apply Subtype.ext
    funext x
    change alg.str.1 ((succEndoAsm.map (recMor M alg)).1 x)
        = (recMor M alg).1 ((boundedAlgAsm M).str.1 x)
    cases x with
    | inl u =>
        cases u
        change zA alg = recFn M alg 0
        rw [recFn_zero]
    | inr k =>
        change sA alg ((sA alg)^[k.val] (zA alg)) = (sA alg)^[min (k.val + 1) M] (zA alg)
        exact Sat.iterate_succ M alg hsat k

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
    (k : Fin (M + 1)) : g.f.1 (TypeRecursorAlgebra.boundedSucc M k) = sA alg (g.f.1 k) :=
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
      have hpt : TypeRecursorAlgebra.boundedSucc M (⟨n, hn'⟩ : Fin (M + 1)) =
          (⟨n + 1, hn⟩ : Fin (M + 1)) := by
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
  change g.f.1 k = (sA alg)^[k.val] (zA alg)
  exact hom_f_orbit M alg g k.val k.isLt

/-! ### The discriminating initiality on the genuine carrier -/

/-- The candidate as an object of the saturating subcategory `SatAlgAsm M`. -/
noncomputable def boundedInitialAlgebraAsm (M : ℕ) : SatAlgAsm M where
  obj := boundedAlgAsm M
  property := boundedAlgAsm_sat M

/-- **FV-18 on the genuine carrier (headline).** `boundedInitialAlgebraAsm M` is a *genuine*
`IsInitial` object of the saturating full subcategory `SatAlgAsm M` of
`Endofunctor.Algebra succEndoAsm`, where `succEndoAsm` is the endofunctor `X ↦ 𝟙 ⊕ X` on the
realizability category `Asm` (the same carrier as the CCC of `RealizabilityCCC.lean`). Discharged
via `IsInitial.ofUniqueHom`: existence is the recursor hom `toSatHomAsm`, uniqueness is the orbit
induction `hom_f_eq_rec`.

Honesty (as in the `Type`-level FV-18): morphisms here are honest algebra homomorphisms (tracked
functions commuting with the structure map), **not** `Prop`s, so uniqueness is a real induction over
the orbit; and initiality holds **only** in the saturating subcategory — the unrestricted initial
`𝟙 ⊕ (·)`-algebra is the infinite `ℕ`, and `no_true_nno` forbids a true NNO on a
finite carrier (recorded by `boundedAlgAsm_str_not_injective`: the structure map is not injective,
hence not a Lambek iso). -/
noncomputable def boundedInitialAlgebraAsmIsInitial (M : ℕ) :
    IsInitial (boundedInitialAlgebraAsm M) :=
  IsInitial.ofUniqueHom
    (fun Y => ObjectProperty.homMk (toSatHomAsm M Y.obj Y.property))
    (fun Y m => by
      apply ObjectProperty.hom_ext
      apply Endofunctor.Algebra.ext
      exact hom_f_eq_rec M Y.obj m.hom)

/-- **Honesty (Lambek does not apply here).** The structure map of `boundedAlgAsm M` is not
injective (its domain `𝟙 ⊕ Fin (M+1)` has `M+2` elements, its codomain `M+1`), hence not an
isomorphism. So the finite initial object of the saturating subcategory is *not* a Lambek fixed
point — the same finite-capacity obstruction (`no_true_nno`) as the `Type`-level
FV-18. -/
theorem boundedAlgAsm_str_not_injective (M : ℕ) :
    ¬ Function.Injective (boundedAlgAsm M).str.1 := by
  intro hinj
  have hle : Fintype.card (PUnit.{1} ⊕ Fin (M + 1)) ≤ Fintype.card (Fin (M + 1)) :=
    Fintype.card_le_of_injective
      (show PUnit.{1} ⊕ Fin (M + 1) → Fin (M + 1) from (boundedAlgAsm M).str.1) hinj
  simp only [Fintype.card_sum, Fintype.card_fin, Fintype.card_punit] at hle
  omega

end ALT.AssemblyRecursorAlgebra
