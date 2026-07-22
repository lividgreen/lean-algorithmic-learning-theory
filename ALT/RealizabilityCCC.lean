/-
Copyright (c) 2026 Mykola Palamarchuk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mykola Palamarchuk
-/
import Mathlib.Combinatorics.Quiver.ReflQuiver
import ALT.Realizability

-- Formal-check file, not Mathlib-destined: opt out of the house-style linters.
set_option linter.style.header false
set_option linter.style.longLine false

/-!
# The realizability category is Cartesian closed ([Decoupling] §4.3, the genuine CCC)

Provenance: [Decoupling] §4.1–§4.3 — Rep(S) is "Cartesian closed
(up to capacity)", with the exponential `[A ⇒ B]` the set of realizer-codes implementing morphisms
"under extensional equality". `ALT/Realizability.lean` (FV-11) established the realizability
*category* and *products* on a single-encoding assembly, but found the exponential needs the
**modest / relational** assembly form (each morphism realized by *many* codes — exactly the
"extensional equality" subtlety). This file builds that form and proves the category **Cartesian
closed**, concretely (terminal + product + exponential universal properties as natural bijections).

## The PCA and assemblies
Realizers are natural numbers; application is Kleene's first PCA over `Nat.Partrec.Code`:
`ap a b := (ofNat Code a).eval b`. An **assembly** is a type with a realizability relation
`realizes : ℕ → carrier → Prop` (every element realized by ≥1 code). A morphism is a function
*tracked* by a realizer code (`Tracks`), and `A ⟶ B` is the trackable functions — a genuine
`CategoryTheory.Category`. (Finiteness, the paper's "up to capacity", is the finite full
subcategory; the CCC structure does not need it, so it is omitted here for the general result.)
-/

namespace RealizabilityCCC

open Nat.Partrec CategoryTheory

/-- Kleene's first PCA application on ℕ: decode `a` to a code and run it on `b`. -/
def ap (a b : ℕ) : Part ℕ := (Denumerable.ofNat Code a).eval b

@[simp] theorem ap_encode (c : Code) (b : ℕ) : ap (Encodable.encode c) b = c.eval b := by
  simp [ap, Denumerable.ofNat_encode]

/-- An **assembly** over the PCA: a carrier with a realizability relation, every element realized. -/
structure Asm where
  carrier : Type
  realizes : ℕ → carrier → Prop
  realized : ∀ x, ∃ n, realizes n x

/-- `r` **tracks** `f` : on any realizer `n` of `x`, `r·n` is defined and realizes `f x`. -/
def Tracks (A B : Asm) (r : ℕ) (f : A.carrier → B.carrier) : Prop :=
  ∀ (x : A.carrier) (n : ℕ), A.realizes n x → ∃ m, m ∈ ap r n ∧ B.realizes m (f x)

/-- `f` is **trackable** (a morphism): some code tracks it ("functions as data"). -/
def Trackable (A B : Asm) (f : A.carrier → B.carrier) : Prop := ∃ r, Tracks A B r f

/-- Identity realizer code. -/
def idCode : ℕ := Encodable.encode Code.id

/-- Composition realizer code ("apply `rf` then `rg`"). -/
def compCode (rg rf : ℕ) : ℕ :=
  Encodable.encode (Code.comp (Denumerable.ofNat Code rg) (Denumerable.ofNat Code rf))

@[simp] theorem ap_idCode (n : ℕ) : ap idCode n = Part.some n := by
  simp [idCode, Code.eval_id]

theorem ap_compCode (rg rf n : ℕ) : ap (compCode rg rf) n = (ap rf n).bind (ap rg) := by
  rw [compCode, ap_encode]; rfl

theorem tracks_id (A : Asm) : Tracks A A idCode id :=
  fun x n hn => ⟨n, by rw [ap_idCode]; exact Part.mem_some n, hn⟩

theorem tracks_comp {A B C : Asm} {rf rg : ℕ} {f : A.carrier → B.carrier} {g : B.carrier → C.carrier}
    (hrf : Tracks A B rf f) (hrg : Tracks B C rg g) : Tracks A C (compCode rg rf) (g ∘ f) := by
  intro x n hn
  obtain ⟨m1, hm1, hb⟩ := hrf x n hn
  obtain ⟨m2, hm2, hc⟩ := hrg (f x) m1 hb
  exact ⟨m2, by rw [ap_compCode]; exact Part.mem_bind hm1 hm2, hc⟩

/-- The **realizability category**: objects are assemblies, morphisms the trackable functions. -/
instance : Category Asm where
  Hom A B := { f : A.carrier → B.carrier // Trackable A B f }
  id A := ⟨id, idCode, tracks_id A⟩
  comp f g := ⟨g.1 ∘ f.1, compCode g.2.choose f.2.choose,
    tracks_comp f.2.choose_spec g.2.choose_spec⟩
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

/-! ### Terminal object -/

/-- The terminal assembly: a single point, realized by every code. -/
def terminalAsm : Asm where
  carrier := PUnit
  realizes _ _ := True
  realized _ := ⟨0, trivial⟩

/-- The unique map into the terminal assembly is trackable (by `idCode`). -/
theorem trackable_toTerminal (A : Asm) :
    Trackable A terminalAsm (fun _ => PUnit.unit) :=
  ⟨idCode, fun x n hn => ⟨n, by rw [ap_idCode]; exact Part.mem_some n, trivial⟩⟩

/-! ### Binary products -/

/-- Product assembly: a code realizes `(a,b)` iff its two halves realize `a` and `b`. -/
def prodAsm (A B : Asm) : Asm where
  carrier := A.carrier × B.carrier
  realizes n p := A.realizes n.unpair.1 p.1 ∧ B.realizes n.unpair.2 p.2
  realized p := by
    obtain ⟨na, ha⟩ := A.realized p.1
    obtain ⟨nb, hb⟩ := B.realized p.2
    exact ⟨Nat.pair na nb, by simp only [Nat.unpair_pair]; exact ⟨ha, hb⟩⟩

def leftCode : ℕ := Encodable.encode Code.left
def rightCode : ℕ := Encodable.encode Code.right

@[simp] theorem ap_leftCode (n : ℕ) : ap leftCode n = Part.some n.unpair.1 := by
  rw [leftCode, ap_encode]; rfl

@[simp] theorem ap_rightCode (n : ℕ) : ap rightCode n = Part.some n.unpair.2 := by
  rw [rightCode, ap_encode]; rfl

/-- The first projection is tracked, by `Code.left`. -/
theorem fst_tracks (A B : Asm) :
    Tracks (prodAsm A B) A leftCode (Prod.fst : A.carrier × B.carrier → A.carrier) :=
  fun _ n hn => ⟨n.unpair.1, by rw [ap_leftCode]; exact Part.mem_some _, hn.1⟩

/-- The second projection is tracked, by `Code.right`. -/
theorem snd_tracks (A B : Asm) :
    Tracks (prodAsm A B) B rightCode (Prod.snd : A.carrier × B.carrier → B.carrier) :=
  fun _ n hn => ⟨n.unpair.2, by rw [ap_rightCode]; exact Part.mem_some _, hn.2⟩

/-- Pairing realizer code from the two component realizers. -/
def pairCode (rf rg : ℕ) : ℕ :=
  Encodable.encode (Code.pair (Denumerable.ofNat Code rf) (Denumerable.ofNat Code rg))

theorem ap_pairCode (rf rg n : ℕ) :
    ap (pairCode rf rg) n = (Nat.pair <$> ap rf n <*> ap rg n) := by
  rw [pairCode, ap_encode]; rfl

/-- Pairing of tracked maps is tracked. -/
theorem pair_tracks {A B C : Asm} {rf rg : ℕ}
    {f : C.carrier → A.carrier} {g : C.carrier → B.carrier}
    (hf : Tracks C A rf f) (hg : Tracks C B rg g) :
    Tracks C (prodAsm A B) (pairCode rf rg) (fun c => (f c, g c)) := by
  intro c n hn
  obtain ⟨ma, hma, hfa⟩ := hf c n hn
  obtain ⟨mb, hmb, hgb⟩ := hg c n hn
  refine ⟨Nat.pair ma mb, ?_, ?_⟩
  · rw [ap_pairCode]
    exact Part.mem_bind (Part.mem_map Nat.pair hma) (Part.mem_map (Nat.pair ma) hmb)
  · change A.realizes (Nat.pair ma mb).unpair.1 (f c) ∧ B.realizes (Nat.pair ma mb).unpair.2 (g c)
    rw [Nat.unpair_pair]
    exact ⟨hfa, hgb⟩

/-! ### Exponentials — the realizability category is Cartesian closed -/

/-- Exponential assembly `[A ⇒ B]`: the carrier is the morphisms `A ⟶ B` (trackable functions),
and a code realizes a morphism iff it **tracks** it — the many-realizers ("under extensional
equality") structure the single-encoding assembly could not express. -/
def expAsm (A B : Asm) : Asm where
  carrier := { f : A.carrier → B.carrier // Trackable A B f }
  realizes r f := Tracks A B r f.1
  realized f := f.2

/-- **Evaluation is tracked** — `ev : [A ⇒ B] × A ⟶ B`, `(f, a) ↦ f a`, realized by the universal
evaluator code (`Realizability.universal_evaluator`). -/
theorem ev_tracks (A B : Asm) :
    Trackable (prodAsm (expAsm A B) A) B (fun p => p.1.1 p.2) := by
  obtain ⟨E, hE⟩ := Realizability.universal_evaluator
  refine ⟨Encodable.encode E, ?_⟩
  rintro ⟨f, a⟩ n hn
  obtain ⟨hf, ha⟩ := hn
  obtain ⟨k, hk, hbk⟩ := hf a n.unpair.2 ha
  refine ⟨k, ?_, hbk⟩
  have key : E.eval n = ap n.unpair.1 n.unpair.2 := by
    have hpair : Nat.pair (Encodable.encode (Denumerable.ofNat Code n.unpair.1)) n.unpair.2 = n := by
      rw [Denumerable.encode_ofNat]; exact Nat.pair_unpair n
    have h := hE (Denumerable.ofNat Code n.unpair.1) n.unpair.2
    rw [hpair] at h
    exact h
  rw [ap_encode, key]; exact hk

/-- A currying realizer code: a single code `L` with `L · rc = ⌜curry (ofNat rh) rc⌝` — it
specializes the realizer `rh` of a two-argument map at a realizer `rc` of the first argument.
Built from Mathlib's primitive-recursive `curry` via `exists_code`. -/
theorem exists_curryCode (rh : ℕ) :
    ∃ L : ℕ, ∀ rc, ap L rc =
      Part.some (Encodable.encode (Code.curry (Denumerable.ofNat Code rh) rc)) := by
  have hcomp : Computable
      (fun rc => Encodable.encode (Code.curry (Denumerable.ofNat Code rh) rc)) :=
    Computable.encode.comp
      ((Nat.Partrec.Code.primrec₂_curry.to_comp).comp (Computable.const _) Computable.id)
  obtain ⟨L, hL⟩ := Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp hcomp)
  refine ⟨Encodable.encode L, fun rc => ?_⟩
  rw [ap_encode]; exact congrFun hL rc

/-- If `rh` tracks `h : C × A → B`, then for any realizer `rc` of `c`, the code
`⌜curry (ofNat rh) rc⌝` tracks the residual `a ↦ h(c,a)`. (s-m-n / `eval_curry`.) -/
theorem curry_inner_tracks {C A B : Asm} {rh : ℕ} {h : C.carrier × A.carrier → B.carrier}
    (hrh : Tracks (prodAsm C A) B rh h) (c : C.carrier) {rc : ℕ} (hrc : C.realizes rc c) :
    Tracks A B (Encodable.encode (Code.curry (Denumerable.ofNat Code rh) rc)) (fun a => h (c, a)) := by
  intro a na hna
  have hcr : ap (Encodable.encode (Code.curry (Denumerable.ofNat Code rh) rc)) na
      = ap rh (Nat.pair rc na) := by
    rw [ap_encode, Nat.Partrec.Code.eval_curry]; rfl
  rw [hcr]
  have hpair : (prodAsm C A).realizes (Nat.pair rc na) (c, a) := by
    change C.realizes (Nat.pair rc na).unpair.1 c ∧ A.realizes (Nat.pair rc na).unpair.2 a
    rw [Nat.unpair_pair]; exact ⟨hrc, hna⟩
  exact hrh (c, a) (Nat.pair rc na) hpair

/-- The curried map `c ↦ (a ↦ h(c,a))` into the exponential. -/
noncomputable def curryFn {C A B : Asm} (rh : ℕ) (h : C.carrier × A.carrier → B.carrier)
    (hrh : Tracks (prodAsm C A) B rh h) (c : C.carrier) : (expAsm A B).carrier :=
  ⟨fun a => h (c, a),
    Encodable.encode (Code.curry (Denumerable.ofNat Code rh) (C.realized c).choose),
    curry_inner_tracks hrh c (C.realized c).choose_spec⟩

/-- The curried map is itself a morphism `C ⟶ [A ⇒ B]` (tracked by the currying code). -/
theorem curry_tracks {C A B : Asm} {rh : ℕ} {h : C.carrier × A.carrier → B.carrier}
    (hrh : Tracks (prodAsm C A) B rh h) : Trackable C (expAsm A B) (curryFn rh h hrh) := by
  obtain ⟨L, hL⟩ := exists_curryCode rh
  refine ⟨L, fun c rc hrc => ?_⟩
  exact ⟨_, hL rc ▸ Part.mem_some _, curry_inner_tracks hrh c hrc⟩

/-- **The realizability category is Cartesian closed** — the exponential's universal property: every
morphism `g : C × A ⟶ B` has a *unique* transpose `t : C ⟶ [A ⇒ B]` factoring it through
evaluation, `(t c) a = g (c, a)`. Together with the terminal object and binary products, this is
Cartesian closure. The transpose is `curryFn`; uniqueness is extensional (morphism equality is
function equality, the realizer existentially quantified). -/
theorem exp_universal {C A B : Asm} (g : (prodAsm C A) ⟶ B) :
    ∃! t : C ⟶ expAsm A B, ∀ c a, (t.1 c).1 a = g.1 (c, a) := by
  obtain ⟨rg, hrg⟩ := g.2
  refine ⟨⟨curryFn rg g.1 hrg, curry_tracks hrg⟩, fun c a => rfl, ?_⟩
  intro t ht
  apply Subtype.ext; funext c; apply Subtype.ext; funext a
  exact ht c a

end RealizabilityCCC
