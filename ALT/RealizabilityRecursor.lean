/-
Copyright (c) 2026 Mykola Palamarchuk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mykola Palamarchuk
-/
import ALT.Realizability
import ALT.RealizabilityCCC
import ALT.ParameterizedNNO
import ALT.GodelThreshold

-- Formal-check file, not Mathlib-destined: opt out of the house-style linters.
set_option linter.style.header false
set_option linter.style.longLine false

/-!
# Rep(S) unified on ONE carrier: the bounded recursor as an object of the realizability CCC (FV-13)

Provenance: [Decoupling] §4 + §6.1 (Definition 6.1 — ONE `Rep(S)`
that is Cartesian closed AND contains the bounded recursor). This file closes the "stand-in
mismatch" the earlier formalizations recorded:

* `ALT/Reflective.lean` (FV-5) bundled a CCC **on `Type`** (`MonoidalClosed Type`, trivially true)
  with a recursor **on a separate `ZMod`** — two disjoint stand-ins.
* `ALT/RepFintype.lean` (FV-10) improved the CCC to genuine finite sets, but its `Reflective`
  predicate still conjoined a (true-by-`inferInstance`) finite-closure `Prop` with a *separately*
  existing recursor — not one categorical object carrying both.

Here both live on the **same** category: the genuine Cartesian-closed realizability category `Asm`
of `ALT/RealizabilityCCC.lean` (FV-12: terminal, products, exponential with the transpose
universal property `exp_universal`, over Kleene's first PCA on `Nat.Partrec.Code`). The bounded
recursor of §5 is exhibited as an **object** `recursorAsm M : Asm` (carrier `ZMod (M+1)`), with its
`zero`/`succ` genuine `Asm`-**morphisms** (`zeroMor`/`succMor`, realized by codes — functions as
data), and the §5 `ParamNNO` orbit structure living on that object's carrier. The unified
`ReflectiveAsm gTS` thus asserts Definition 6.1 on ONE carrier, and `reflectiveAsm_satisfiable`
discharges it for every `gTS`.

## Boundary
This is the **un-capacitated** realizability CCC (no `s_work` size bound); the capacity filtration
("up to capacity", `Rep(S)` as the finite full subcategory) is `ALT/CapacityLayer.lean` (FV-14).
The recursor successor is realized concretely; its iterates' distinctness (the depth bound) is the
`ParamNNO.orbit_injective` of `cyclicParamNNO`, reused here on the same carrier.
-/

namespace RealizabilityRecursor

open RealizabilityCCC ParameterizedNNO Nat.Partrec CategoryTheory

/-! ### The bounded recursor as an object of the realizability CCC `Asm` -/

/-- The bounded-recursor object `N_M` as an assembly of the CCC `Asm`: carrier `ZMod (M+1)`, each
element realized by its own value-code. The SAME category `Asm` that is Cartesian closed (FV-12).
`abbrev` (reducible) so the carrier's `ZMod (M+1)` `Add`/`OfNat`/`Fintype` instances and the
`realizes` relation are visible at use sites — the same pattern as FV-11's `counterAssembly`. -/
abbrev recursorAsm (M : ℕ) : Asm :=
  { carrier := ZMod (M + 1)
    realizes := fun r z => r = ZMod.val z
    realized := fun z => ⟨ZMod.val z, rfl⟩ }

/-- The successor `z ↦ z+1` on `recursorAsm M` is **tracked** by a code (functions as data): the
realizer is `exists_code_tracks_succ`, bridged to `ap` by `ap_encode`. -/
theorem succ_trackable (M : ℕ) :
    Trackable (recursorAsm M) (recursorAsm M) (fun z : ZMod (M + 1) => z + 1) := by
  obtain ⟨c, hc⟩ := Realizability.exists_code_tracks_succ M
  refine ⟨Encodable.encode c, ?_⟩
  intro z n hn
  obtain rfl : n = @ZMod.val (M + 1) z := hn
  refine ⟨ZMod.val (z + 1), ?_, rfl⟩
  rw [ap_encode, hc z]
  exact Part.mem_some _

/-- Zero `⋆ ↦ 0` is tracked, by the constant code `Code.const 0`. -/
theorem zero_trackable (M : ℕ) :
    Trackable terminalAsm (recursorAsm M) (fun _ : PUnit => (0 : ZMod (M + 1))) := by
  refine ⟨Encodable.encode (Code.const 0), ?_⟩
  intro _ n _
  refine ⟨0, ?_, ?_⟩
  · rw [ap_encode, Nat.Partrec.Code.eval_const]
    exact Part.mem_some 0
  · change (0 : ℕ) = ZMod.val (0 : ZMod (M + 1))
    rw [ZMod.val_zero]

/-- The successor **morphism** `recursorAsm M ⟶ recursorAsm M` of the CCC `Asm`. -/
def succMor (M : ℕ) : recursorAsm M ⟶ recursorAsm M :=
  ⟨fun z => z + 1, succ_trackable M⟩

/-- The zero **morphism** (global element) `terminalAsm ⟶ recursorAsm M` of `Asm`. -/
def zeroMor (M : ℕ) : terminalAsm ⟶ recursorAsm M :=
  ⟨fun _ => 0, zero_trackable M⟩

/-! ### Definition 6.1, unified on ONE carrier (the CCC `Asm` ∧ a recursor object) -/

/-- **Definition 6.1 on one carrier.** The SAME realizability category `Asm` is Cartesian closed —
terminal object, binary products, and the exponential transpose universal property (all cited from
FV-12) — AND it contains a bounded-recursor *object* `recursorAsm depth` of depth `> gTS`, whose
`zero`/`succ` are genuine `Asm`-morphisms equal (pointwise) to the §5 `ParamNNO` structure maps on
the SAME carrier `ZMod (depth+1)`. Unlike `RepFintype.Reflective` (a trivially-true finite-closure
`Prop` plus a *separate* recursor), every conjunct here is about one categorical object. -/
structure ReflectiveAsm (gTS : ℕ) where
  /-- (i-a) terminal object of `Asm`. -/
  terminal : ∀ A : Asm, Trackable A terminalAsm (fun _ => PUnit.unit)
  /-- (i-b) binary products of `Asm` (projections). -/
  fst : ∀ A B : Asm, Trackable (prodAsm A B) A Prod.fst
  snd : ∀ A B : Asm, Trackable (prodAsm A B) B Prod.snd
  /-- (i-c) the exponential: evaluation and the transpose universal property (Cartesian closure). -/
  eval_tracks : ∀ A B : Asm, Trackable (prodAsm (expAsm A B) A) B (fun p => p.1.1 p.2)
  exp_univ : ∀ (C A B : Asm) (g : prodAsm C A ⟶ B),
      ∃! t : C ⟶ expAsm A B, ∀ c a, (t.1 c).1 a = g.1 (c, a)
  /-- (ii) a bounded-recursor OBJECT of depth `> gTS` in the SAME category. -/
  depth : ℕ
  depth_gt : gTS < depth
  zero : terminalAsm ⟶ recursorAsm depth
  succ : recursorAsm depth ⟶ recursorAsm depth
  orbit : ParamNNO (ZMod (depth + 1))
  /-- the recursor object's own depth parameter is the structure depth, so the §5 depth bound
  (`orbit.orbit_injective`) witnesses `gTS < orbit.depth` — exactly the Level-1 indexing precondition
  the §6 Consequence needs (used in `reflectiveAsm_representsUnderivableTruth`). -/
  orbit_depth : orbit.depth = depth
  /-- (iii) the recursor morphisms ARE the `ParamNNO` structure maps on the shared carrier
  `ZMod (depth+1) = (recursorAsm depth).carrier` (pointwise — `succ.1` is `succMor`, `orbit.succ`
  is `cyclicParamNNO`'s successor; the orbit's `orbit_injective` is the depth bound). -/
  succ_eq : ∀ z : ZMod (depth + 1), succ.1 z = orbit.succ z
  zero_eq : zero.1 PUnit.unit = orbit.zero

/-- **Definition 6.1 is satisfiable on one carrier, for every `gTS`** (FV-13). The CCC conjuncts are
the FV-12 universal properties of `Asm`; the recursor object is `recursorAsm (gTS+1)` with
`zeroMor`/`succMor`, and the orbit is `cyclicParamNNO (gTS+1)` on the same carrier `ZMod (gTS+2)`.
The successor/zero morphisms equal the orbit maps definitionally (`rfl`), so this is genuinely ONE
object that is both Cartesian closed and a bounded recursor — not two disjoint stand-ins. -/
def reflectiveAsm_satisfiable (gTS : ℕ) : ReflectiveAsm gTS where
  terminal A := trackable_toTerminal A
  fst A B := ⟨leftCode, fst_tracks A B⟩
  snd A B := ⟨rightCode, snd_tracks A B⟩
  eval_tracks A B := ev_tracks A B
  exp_univ _ _ _ g := exp_universal g
  depth := gTS + 1
  depth_gt := Nat.lt_succ_self gTS
  zero := zeroMor (gTS + 1)
  succ := succMor (gTS + 1)
  orbit := cyclicParamNNO (gTS + 1)
  orbit_depth := rfl
  succ_eq _ := rfl
  zero_eq := rfl

/-- **The genuine single-carrier object yields the §6 Consequence** (closes the seam that the
consequence previously flowed only through `ALT/Reflective.lean`'s trivially-true `Type`-CCC
stand-in, FV-5). From a `ReflectiveAsm gTS` — Definition 6.1 on the ONE Cartesian-closed realizability
category `Asm` (FV-12/FV-13), carrying a bounded-recursor *object* of depth `> gTS` — together with
imported incompleteness for the subsystem's theory at `gTS`, the subsystem represents a sentence that
is true-but-underivable in its internal logic. The recursor object's `ParamNNO` (whose
`orbit_injective` is the §5 depth bound) supplies the Level-1 indexing threshold via
`GodelThreshold.reflective_of_depth`. Unlike `ReflectiveAssembly.reflective_representsUnderivableTruth`,
the CCC here is genuine and on the same carrier as the recursor — no trivially-true unused conjunct. -/
theorem reflectiveAsm_representsUnderivableTruth
    {Sentence : Type*} (gnum : Sentence → ℕ) (Derivable True_ : Sentence → Prop) (gTS : ℕ)
    (R : ReflectiveAsm gTS)
    (hInc : GodelThreshold.Incompleteness gnum Derivable True_ gTS) :
    ∃ M, GodelThreshold.RepresentsUnderivableTruth gnum Derivable True_ M :=
  ⟨R.orbit.depth,
    GodelThreshold.reflective_of_depth gnum Derivable True_ R.orbit gTS
      (by rw [R.orbit_depth]; exact R.depth_gt) hInc⟩

end RealizabilityRecursor
