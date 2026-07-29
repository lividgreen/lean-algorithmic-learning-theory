/-
Copyright (c) 2026 Mykola Palamarchuk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mykola Palamarchuk
-/
import ALT.RealizabilityCCC
import ALT.RealizerLength
import ALT.UniversalAt
import ALT.PolyTime
import ALT.CapacityLayer

-- Formal-check file, not Mathlib-destined: opt out of the house-style header linter.
set_option linter.style.header false

/-!
# The graded exponential, and what applying one costs ([Decoupling] §4.5)

A bounded work memory cannot carry a strict function space: no capacity is closed under the
exponential, neither in element count (FV-14) nor in realizer length (FV-16). What survives is a
*graded* exponential: for each resource grade `g`, the morphisms that own a realizer within `g`.
This module builds that object over Kleene's first algebra on `Nat.Partrec.Code` and prices its
application.

## The grade currency
A grade bounds a realizer's **description length**, `Nat.size` of its Gödel index. This is not a
free choice: it is the currency the priced universal evaluator already charges in, so a grade can
be spent directly in that account without a conversion factor. It is also, on the nose, the
realizer length of the counting bound (`Realizability.bitlen`) transported along the
`Code ≃ ℕ` numbering — `grade_encode` and `bitlen_ofNat` record the identification, so the
non-closure theorems and the grading here speak of one quantity, not two that happen to agree.
What the identification is *about* is the measure alone: the counting bound is stated over
assemblies whose elements carry one name each, while the exponential graded here is the
many-realizers form; the two settings meet where naming is unambiguous, the condition isolated
below (`Modest`).

## Application goes through the reference dynamics
The partial combinatory algebra applies by decoding: `ap a b` decodes `a` to a code and runs it.
That decode is an existence statement with no constructor skeleton, so nothing about the run can
be priced — which is exactly what the priced evaluator was built to replace. So application is
repackaged here as a **run of the reference dynamics**: `appRun r x τ` is the configuration the
small-step machine reaches after `τ` steps from `⟨r, x⟩`, and `appValue_mem_ap` /
`exists_appRun_of_mem_ap` say that this run computes the algebra's application and nothing else.
Both directions are the machine's own soundness and completeness against `Code.eval`, applied at
the application interface; no new semantics is introduced.

## What a grade buys, and what it does not
`appConfig_size_le` is the whole of what a grade provably buys on the workspace side: the
**initial** configuration's width is affine in the grade and the argument's width. Every later
configuration holds values the computation has produced, which are outputs rather than functions
of the code's shape, so nothing bounds them from the grade alone. The workspace account therefore
stays relative to a named width hypothesis `W`, exactly as bounded universality itself is — and
`gradedApp_workspace` is that account: under the hypothesis, the evaluator's workspace on the
application is `F` of the wider of `W` and a grade-derived affine budget. An affine bound free of
`W`, derived from the grade alone, would make this false, not merely unproved — a W-free bound as
such need not be (a trivial max over finitely many inputs is W-free), only the affine, grade-derived
one.

## Deliberately absent
No functoriality statement: transporting graded realizers along a change of algebra is the
applicative-morphism question, settled territory that this development does not re-enter. No
graded Cartesian closed structure: `gradedExp` is built and priced as an object, with the
inclusion and grade-monotonicity morphisms it needs, and nothing is claimed about closure of the
grading itself. Both are scope decisions rather than gaps.

## Prior art
Resource-graded exponential modalities are the bounded-linear-logic tradition (Girard–Scedrov–Scott
1992), with a semantics on assemblies given by Fukihara–Katsumata (2021). Nothing about the concept
is new here; what is new is the concrete instantiation on `Nat.Partrec.Code` together with a
machine-checked affine price for applying it.
-/

namespace GradedApplication

open Nat.Partrec (Code)
open TimeCost RealizabilityCCC BoundedUniversal CodeSizeArith

/-! ## The grade currency -/

/-- **The grade of a realizer**: the bit-length of its Gödel index — `Nat.size` of the code's
encoding. Realizers in the realizability category are already numbers, so the round trip through
`Code` is the identity (`grade_eq_size`); it is written out here because the *measure* is a
property of the code, not of the numeral that happens to name it. -/
def grade (r : ℕ) : ℕ := Nat.size (Encodable.encode (Denumerable.ofNat Code r))

@[simp] theorem grade_eq_size (r : ℕ) : grade r = Nat.size r := by
  rw [grade, Denumerable.encode_ofNat]

/-- The grade of a code's index **is** its realizer length in the sense of the counting bound
(`Realizability.bitlen`). The two accounts — the non-closure theorems, which measure a realizer's
length, and the grading here, which budgets it — use one quantity. -/
theorem grade_encode (c : Code) : grade (Encodable.encode c) = Realizability.bitlen c := by
  rw [grade_eq_size]; rfl

/-- The same identification read the other way: the realizer length of the code a numeral names is
that numeral's grade. -/
theorem bitlen_ofNat (r : ℕ) : Realizability.bitlen (Denumerable.ofNat Code r) = grade r := by
  rw [Realizability.bitlen, grade]

/-! ## The graded exponential -/

/-- **The graded exponential** `[A ⇒ B]_g`: the sub-assembly of the exponential `expAsm A B` whose
elements own a realizer of grade at most `g`, realized by exactly those realizers.

Two clauses, and both are load-bearing. The carrier condition is what makes the object *inhabited
by affordable morphisms*; the realizability condition is what makes a realizer drawn from the
object affordable in turn, which is what the application account below consumes. Every element is
realized (`realized`) precisely because the carrier condition says so. -/
def gradedExp (g : ℕ) (A B : Asm) : Asm where
  carrier := { f : (expAsm A B).carrier // ∃ r, grade r ≤ g ∧ Tracks A B r f.1 }
  realizes r f := grade r ≤ g ∧ Tracks A B r f.1.1
  realized f := f.2

/-- The function underlying an element of the graded exponential. An element carries a morphism
`A ⟶ B` together with the evidence that it is affordable; this reads off the morphism. -/
def fn {A B : Asm} {g : ℕ} (f : (gradedExp g A B).carrier) : A.carrier → B.carrier := f.1.1

/-- A realizer drawn from the graded exponential is within grade — the clause the workspace
account spends. -/
theorem grade_le_of_realizes {A B : Asm} {g r : ℕ} {f : (gradedExp g A B).carrier}
    (h : (gradedExp g A B).realizes r f) : grade r ≤ g := h.1

/-- A realizer drawn from the graded exponential tracks the underlying morphism. -/
theorem tracks_of_realizes {A B : Asm} {g r : ℕ} {f : (gradedExp g A B).carrier}
    (h : (gradedExp g A B).realizes r f) : Tracks A B r (fn f) := h.2

/-- The inclusion of the graded exponential into the exponential: forget the grade. -/
def incl (g : ℕ) (A B : Asm) : (gradedExp g A B).carrier → (expAsm A B).carrier := Subtype.val

/-- **The inclusion is a morphism**, tracked by the identity code: forgetting a grade changes no
realizer. -/
theorem incl_tracks (g : ℕ) (A B : Asm) :
    Tracks (gradedExp g A B) (expAsm A B) idCode (incl g A B) := by
  intro f n hn
  exact ⟨n, by rw [ap_idCode]; exact Part.mem_some n, hn.2⟩

/-- The inclusion is trackable, hence a morphism `[A ⇒ B]_g ⟶ [A ⇒ B]`. -/
theorem incl_trackable (g : ℕ) (A B : Asm) :
    Trackable (gradedExp g A B) (expAsm A B) (incl g A B) :=
  ⟨idCode, incl_tracks g A B⟩

/-- Relaxing the budget: an element affordable at grade `g` is affordable at any larger grade. -/
def relax {A B : Asm} {g g' : ℕ} (h : g ≤ g') (f : (gradedExp g A B).carrier) :
    (gradedExp g' A B).carrier :=
  ⟨f.1, f.2.imp fun _ hr => ⟨le_trans hr.1 h, hr.2⟩⟩

/-- **Grade monotonicity.** The graded exponentials form an increasing family, and the inclusion of
one grade into a larger one is a morphism tracked by the identity code — a realizer affordable at
`g` is affordable at `g'`, and no re-coding is needed to say so. -/
theorem relax_tracks {A B : Asm} {g g' : ℕ} (h : g ≤ g') :
    Tracks (gradedExp g A B) (gradedExp g' A B) idCode (relax h) := by
  intro f n hn
  exact ⟨n, by rw [ap_idCode]; exact Part.mem_some n, le_trans hn.1 h, hn.2⟩

/-- The grade-relaxing map is trackable, hence a morphism `[A ⇒ B]_g ⟶ [A ⇒ B]_{g'}`. -/
theorem relax_trackable {A B : Asm} {g g' : ℕ} (h : g ≤ g') :
    Trackable (gradedExp g A B) (gradedExp g' A B) (relax h) :=
  ⟨idCode, relax_tracks h⟩

/-! ## Application, as a run of the reference dynamics -/

/-- **The application argument**: what the universal evaluator is handed to run the realizer `r` on
the input `x` for `τ` steps. -/
def appInput (r x τ : ℕ) : ℕ := Nat.pair (Nat.pair r x) τ

/-- **The application run**: the configuration the reference dynamics reaches after `τ` steps from
the initial configuration of `r` on `x`. This — not the algebra's decode — is what gets priced. -/
def appRun (r x τ : ℕ) : ℕ := BoundedInterp.stepUFn^[τ] (BoundedInterp.initConfig r x)

/-- Has the application run finished after `τ` steps? -/
def appHalted (r x τ : ℕ) : Bool := BoundedInterp.isHalt (appRun r x τ)

/-- The value a finished application run holds. -/
def appValue (r x τ : ℕ) : ℕ := BoundedInterp.haltVal (appRun r x τ)

/-- **The run computes the application** (soundness half). If the run has finished, its value is a
genuine value of the algebra's application `r · x`. -/
theorem appValue_mem_ap {r x τ : ℕ} (h : appHalted r x τ = true) : appValue r x τ ∈ ap r x :=
  BoundedInterp.machine_sound r x h

/-- **The run computes the application** (completeness half). Every value the algebra's application
`r · x` produces is reached by the run, at some number of steps. -/
theorem exists_appRun_of_mem_ap {r x v : ℕ} (h : v ∈ ap r x) :
    ∃ τ, appHalted r x τ = true ∧ appValue r x τ = v := by
  obtain ⟨τ, hhalt, hval⟩ :=
    BoundedInterp.machine_complete (c := Denumerable.ofNat Code r) (n := x) h
  rw [Denumerable.encode_ofNat] at hhalt hval
  exact ⟨τ, hhalt, hval⟩

/-- **Tracking, through the run.** If `r` tracks `f` and `n` names `a`, then the application run of
`r` on `n` finishes, and the value it holds names `f a`. This is the tracking condition of the
realizability category stated at the application interface the price is charged against. -/
theorem tracks_appValue {A B : Asm} {r : ℕ} {f : A.carrier → B.carrier}
    (hr : Tracks A B r f) {a : A.carrier} {n : ℕ} (hn : A.realizes n a) :
    ∃ τ, appHalted r n τ = true ∧ B.realizes (appValue r n τ) (f a) := by
  obtain ⟨m, hm, hB⟩ := hr a n hn
  obtain ⟨τ, hhalt, hval⟩ := exists_appRun_of_mem_ap hm
  exact ⟨τ, hhalt, by rw [hval]; exact hB⟩

/-- **A halted run stays where it stopped.** A halted configuration is a fixed point of the step
function, so continuing to step it changes nothing. -/
theorem appRun_of_halted {r x τ : ℕ} (h : appHalted r x τ = true) (j : ℕ) :
    appRun r x (τ + j) = appRun r x τ := by
  induction j with
  | zero => rfl
  | succ i ih =>
      have hstep : appRun r x (τ + (i + 1)) = BoundedInterp.stepUFn (appRun r x (τ + i)) :=
        Function.iterate_succ_apply' _ _ _
      rw [hstep, ih, BoundedInterp.stepUFn_halt h]

/-- **The run's width hypothesis is not vacuous.** On an application that finishes, the widths of
the configurations the run passes through are bounded uniformly: the initial segment is finite, and
past the halting step the run is constant (`appRun_of_halted`).

So the hypothesis carried through the workspace account is *quantitative* — which `W` — rather than
existential. What no grade supplies is the value of `W`, since the configurations hold values the
computation produced. -/
theorem exists_width_bound {r x τ : ℕ} (h : appHalted r x τ = true) :
    ∃ W, ∀ k, Nat.size (appRun r x k) ≤ W := by
  have hseg : ∀ t : ℕ, ∃ V, ∀ k, k ≤ t → Nat.size (appRun r x k) ≤ V := by
    intro t
    induction t with
    | zero => exact ⟨Nat.size (appRun r x 0), fun k hk => by rw [Nat.le_zero.mp hk]⟩
    | succ s ih =>
        obtain ⟨V, hV⟩ := ih
        refine ⟨max V (Nat.size (appRun r x (s + 1))), fun k hk => ?_⟩
        rcases Nat.eq_or_lt_of_le hk with heq | hlt
        · rw [heq]; exact le_max_right _ _
        · exact le_trans (hV k (by omega)) (le_max_left _ _)
  obtain ⟨V, hV⟩ := hseg τ
  refine ⟨V, fun k => ?_⟩
  rcases Nat.lt_or_ge k τ with hk | hk
  · exact hV k (le_of_lt hk)
  · obtain ⟨j, rfl⟩ : ∃ j, k = τ + j := ⟨k - τ, by omega⟩
    rw [appRun_of_halted h]
    exact hV τ le_rfl

/-! ## What the grade bounds: the initial width -/

/-- **The grade-derived width budget** for the evaluator's argument: affine in the grade, the
argument's width, and the step counter's width. -/
def appWidth (g sx sτ : ℕ) : ℕ := 2 * g + 2 * sx + sτ + 2

/-- **The evaluator's own width measure is within the grade-derived budget.** Bounded universality
charges its price against the wider of the code–argument pair and the step counter; both are
inside `appWidth` once the realizer is within grade. Square pairing has width affine in its
components' widths, which is the whole of the arithmetic. -/
theorem width_le_appWidth {r x τ g : ℕ} (hg : grade r ≤ g) :
    max (Nat.size (Nat.pair r x)) (Nat.size τ) ≤ appWidth g (Nat.size x) (Nat.size τ) := by
  have hp := size_pair_le r x
  rw [grade_eq_size] at hg
  simp only [appWidth]
  omega

/-- **What a grade buys on the workspace side, exactly.** The *initial* configuration of the
application run is affine in the grade and the argument's width — unconditionally, with no
hypothesis about the run.

This is also the boundary. Every later configuration of the run holds values the computation has
produced; those are outputs of the computation rather than functions of the code's shape, so no
grade bounds them. That is why the workspace account below is relative to a named width hypothesis
and not derived from the grade alone. -/
theorem appConfig_size_le {r x g : ℕ} (hg : grade r ≤ g) :
    Nat.size (BoundedInterp.initConfig r x) ≤ 8 * g + 8 * Nat.size x + 14 := by
  rw [grade_eq_size] at hg
  have h1 := size_pair_le r x
  have h2 := size_pair_le (Nat.pair r x) 0
  have h3 := size_pair_le 0 (Nat.pair (Nat.pair r x) 0)
  have hinit : BoundedInterp.initConfig r x = Nat.pair 0 (Nat.pair (Nat.pair r x) 0) := rfl
  rw [hinit]
  simp only [Nat.size_zero] at h2 h3
  omega

/-! ## The workspace account of a graded application -/

/-- **The graded application's workspace, for a given priced evaluator.** An evaluator that obeys
the bounded-universality price pays, on the application of a grade-`g` realizer, at most `F` of the
wider of the run's own width bound `W` and the grade-derived budget. The grade enters only through
the evaluator's argument; `W` carries everything the run itself does. -/
theorem spaceCost_appInput_le {F : ℕ → ℕ} (hF : Monotone F) {u : Code}
    (hu : ∀ p y σ V : ℕ, (∀ k, k ≤ σ → Nat.size (appRun p y k) ≤ V) →
      spaceCost u (appInput p y σ) ≤ F (max V (max (Nat.size (Nat.pair p y)) (Nat.size σ))))
    {r x τ W g : ℕ} (hg : grade r ≤ g)
    (hW : ∀ k, k ≤ τ → Nat.size (appRun r x k) ≤ W) :
    spaceCost u (appInput r x τ) ≤ F (max W (appWidth g (Nat.size x) (Nat.size τ))) :=
  le_trans (hu r x τ W hW) (hF (max_le_max le_rfl (width_le_appWidth hg)))

/-- **The graded application's workspace account** ([Decoupling] §4.5, "the universal evaluator's
application combinator runs within the work memory", grade-relative). Under bounded universality
at `F`, some code runs the application of a grade-`g` realizer — computing the reference dynamics
on every input, so the semantics is the algebra's own — within `F` of the wider of the run's width
bound and a budget affine in the grade, the argument's width, and the counter's width.

The width hypothesis `W` stays a hypothesis. Grades bound the initial configuration
(`appConfig_size_le`) and nothing further, so an *affine* bound free of `W`, derived from the
grade alone, would not be a stronger theorem but a false one — a W-free bound as such need not
be (a trivial max over finitely many inputs is W-free), only the affine, grade-derived one. -/
theorem gradedApp_workspace {F : ℕ → ℕ} (hF : Monotone F) (hU : UniversalAt F)
    {r x τ W g : ℕ} (hg : grade r ≤ g)
    (hW : ∀ k, k ≤ τ → Nat.size (appRun r x k) ≤ W) :
    ∃ u : Code, (∀ p y σ : ℕ, val u (appInput p y σ) = appRun p y σ) ∧
      spaceCost u (appInput r x τ) ≤ F (max W (appWidth g (Nat.size x) (Nat.size τ))) := by
  obtain ⟨u, hval, hcost⟩ := hU
  exact ⟨u, hval, spaceCost_appInput_le hF hcost hg hW⟩

/-- The price bounded universality is actually discharged at is monotone, so it can serve as the
budget the account is stated against. -/
theorem monotone_universalCost : Monotone universalCost := by
  intro a b h
  simp only [universalCost]
  omega

/-- **The account, unconditionally.** Bounded universality holds at an affine price, so the graded
application's workspace bound needs no hypothesis about `F` at all: only the run's width. -/
theorem gradedApp_workspace_affine {r x τ W g : ℕ} (hg : grade r ≤ g)
    (hW : ∀ k, k ≤ τ → Nat.size (appRun r x k) ≤ W) :
    ∃ u : Code, (∀ p y σ : ℕ, val u (appInput p y σ) = appRun p y σ) ∧
      spaceCost u (appInput r x τ)
        ≤ universalCost (max W (appWidth g (Nat.size x) (Nat.size τ))) :=
  gradedApp_workspace monotone_universalCost universalAt_holds hg hW

/-- **The account, at the graded exponential.** A realizer drawn from `[A ⇒ B]_g` is within grade
by construction, so the workspace bound applies to it with no side condition beyond the run's
width. -/
theorem gradedExp_app_workspace {A B : Asm} {g r : ℕ} {f : (gradedExp g A B).carrier}
    (hr : (gradedExp g A B).realizes r f) {F : ℕ → ℕ} (hF : Monotone F) (hU : UniversalAt F)
    {x τ W : ℕ} (hW : ∀ k, k ≤ τ → Nat.size (appRun r x k) ≤ W) :
    ∃ u : Code, (∀ p y σ : ℕ, val u (appInput p y σ) = appRun p y σ) ∧
      spaceCost u (appInput r x τ) ≤ F (max W (appWidth g (Nat.size x) (Nat.size τ))) :=
  gradedApp_workspace hF hU (grade_le_of_realizes hr) hW

/-! ## Semantic closure -/

/-- **The graded application realizes its value.** Applying an element of `[A ⇒ B]_g` to a named
argument, through the reference dynamics, produces a value that names the applied result in `B`.
The grading restricts which morphisms are present; it does not change what applying one means. -/
theorem gradedExp_app_realizes {A B : Asm} {g r : ℕ} {f : (gradedExp g A B).carrier}
    (hr : (gradedExp g A B).realizes r f) {a : A.carrier} {n : ℕ} (hn : A.realizes n a) :
    ∃ τ, appHalted r n τ = true ∧ B.realizes (appValue r n τ) (fn f a) :=
  tracks_appValue (tracks_of_realizes hr) hn

/-- **The graded application, semantics and price together** ([Decoupling] §4.5). On a run whose
configurations never exceed `W` bits, applying an element of `[A ⇒ B]_g` to a named argument both
finishes with a genuine realizer of the applied value and is carried out by a single evaluator
within `F` of the wider of `W` and the grade-derived budget.

The width hypothesis is stated over all step counts rather than up to a fixed one because the step
count at which the application finishes is produced by the run, not chosen in advance; it remains
satisfiable for exactly that reason (`exists_width_bound`). -/
theorem gradedExp_app_realizes_within {A B : Asm} {g r : ℕ} {f : (gradedExp g A B).carrier}
    (hr : (gradedExp g A B).realizes r f) {a : A.carrier} {n : ℕ} (hn : A.realizes n a)
    {F : ℕ → ℕ} (hF : Monotone F) (hU : UniversalAt F)
    {W : ℕ} (hW : ∀ k, Nat.size (appRun r n k) ≤ W) :
    ∃ (τ : ℕ) (u : Code), appHalted r n τ = true ∧ B.realizes (appValue r n τ) (fn f a) ∧
      (∀ p y σ : ℕ, val u (appInput p y σ) = appRun p y σ) ∧
      spaceCost u (appInput r n τ) ≤ F (max W (appWidth g (Nat.size n) (Nat.size τ))) := by
  obtain ⟨τ, hhalt, hreal⟩ := gradedExp_app_realizes hr hn
  obtain ⟨u, hval, hcost⟩ :=
    gradedExp_app_workspace hr hF hU (τ := τ) (W := W) (fun k _ => hW k)
  exact ⟨τ, u, hhalt, hreal, hval, hcost⟩

/-! ## The grade meets the capacity filtration -/

/-- An assembly is **modest** when no code names two different elements. This is the direction an
assembly need not have — an element may still own many realizers — and it holds automatically
whenever the elements are named by an injective encoding. -/
def Modest (B : Asm) : Prop :=
  ∀ (m : ℕ) (b b' : B.carrier), B.realizes m b → B.realizes m b' → b = b'

/-- **A grade caps the exponential's element count.** The graded exponential fits in exactly its
grade: an element is determined by any realizer it owns — application in the algebra is
single-valued, and a modest codomain names unambiguously — so the carrier injects into the codes of
grade at most `g`, of which there are at most `2 ^ g`.

Set beside the non-closure theorems, this is what the grading is for. No capacity is closed under
the ungraded exponential, in element count or in realizer length; a graded exponential is a
capacity object again, with the grade as its budget. What is bought is not closure — the morphisms
priced out are genuinely absent — but a filtration whose every level fits. -/
theorem gradedExp_fitsIn {A B : Asm} (g : ℕ) (hB : Modest B) :
    CapacityLayer.FitsIn (gradedExp g A B) g := by
  classical
  -- every element's chosen realizer is a code of grade `≤ g`, hence a numeral below `2 ^ g`
  have hlt : ∀ f : (gradedExp g A B).carrier, f.2.choose < 2 ^ g :=
    fun f => Nat.size_le.mp (by simpa using f.2.choose_spec.1)
  -- and it determines the element: application is single-valued, and so is `B`'s naming
  have hinj : Function.Injective
      (fun f : (gradedExp g A B).carrier => (⟨f.2.choose, hlt f⟩ : Fin (2 ^ g))) := by
    intro f f' hff
    have hcode : f.2.choose = f'.2.choose := by simpa [Fin.mk.injEq] using hff
    refine Subtype.ext (Subtype.ext (funext fun a => ?_))
    obtain ⟨n, hn⟩ := A.realized a
    obtain ⟨m, hm, hb⟩ := f.2.choose_spec.2 a n hn
    obtain ⟨m', hm', hb'⟩ := f'.2.choose_spec.2 a n hn
    rw [← hcode] at hm'
    exact hB m _ _ hb (Part.mem_unique hm' hm ▸ hb')
  refine ⟨Finite.of_injective _ hinj, ?_⟩
  calc Nat.card (gradedExp g A B).carrier
      ≤ Nat.card (Fin (2 ^ g)) := Nat.card_le_card_of_injective _ hinj
    _ = 2 ^ g := by simp

end GradedApplication
