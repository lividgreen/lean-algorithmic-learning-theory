/-
Copyright (c) 2026 Mykola Palamarchuk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mykola Palamarchuk
-/
import Mathlib

-- Formal-check file, not Mathlib-destined: opt out of the house-style linters.
set_option linter.style.header false
set_option linter.style.longLine false

/-!
# The realizability layer of Rep(S): finite assemblies over a universal machine (Paper I §4.1)

Provenance: Paper I §4.1 (Definition 4.1) — the realizability
content of Rep(S): objects are finite sets encoded into work memory, and **every morphism carries a
code that is itself a value** ("functions as data"). FV-10 (`RepFintype.lean`) certified the
finite-set categorical *shape*; this file adds the **realizability layer** FV-10 explicitly left
paper-level — morphisms are *realized* by codes for an actual universal machine.

## Why this is novel infrastructure
A 2026 deep-research sweep found that realizability / assembly categories / PCAs are **absent from
Lean / Mathlib**. The nearest prior art in any prover is UniMath's Coq category of partial
equivalence relations (a Cartesian-closed realizability category in the sense of van Oosten 2008),
which is tied to univalent foundations and not portable to Lean. What Mathlib *does* ship is the full
substrate of Kleene's first partial combinatory algebra — `Nat.Partrec.Code` with a universal `eval`,
the s-m-n theorem (`curry`/`eval_curry`), identity (`Code.id`/`eval_id`), composition (`Code.comp`,
`eval (comp cf cg) n = eval cg n >>= eval cf`), and `exists_code` — but never assembles it into a
realizability structure. We build that layer here, directly on `Nat.Partrec.Code`: realizers are
genuine codes (`Denumerable Code`, so each realizer *is a value*), the evaluator is Mathlib's
verified universal `eval`, and no bespoke universal machine is introduced.

## What this establishes
* `Assembly`: a finite carrier with an injective encoding `enc : carrier → ℕ` into codes (the
  `s_work` encoding of an object). `Assembly.FitsIn sworkBits`: all codes `< 2^{sworkBits}`.
* `Realizes f`: the **functions-as-data** predicate — a code `r` *tracks* `f`, i.e.
  `eval r (enc x) = enc (f x)` for all `x`. The realizer is a value (a `Code`).
* `realizes_id`, `realizes_comp`: identity (`Code.id`) and composition (`Code.comp`) are realized —
  so realized functions are closed under the categorical operations.
* `instance : Category Assembly` with `Hom A B := { f // Realizes f }`: the **realizability category**
  of finite assemblies — a genuine `CategoryTheory.Category`, morphisms being exactly the
  code-realizable functions (the realizer existentially witnessed = "functions as data").

## Boundary
Objects here are finite assemblies with a *single-valued* encoding (each element is its code), the
faithful reading of §4.1's "objects as subsets of `{0,1}^{|s_work|}`". The Cartesian-closed structure
of this realizability category (exponentials as codes realizing morphisms — combinatory completeness
via k/s) is the next increment; this file establishes the category and the functions-as-data layer.
-/

namespace Realizability

open Nat.Partrec CategoryTheory

/-- A finite **assembly**: a finite carrier together with an injective encoding of its elements as
codes (numbers) — an object of Rep(S) encoded into work memory (§4.1). -/
structure Assembly where
  carrier : Type
  [fin : Fintype carrier]
  /-- the `s_work` encoding: each element gets a code -/
  enc : carrier → ℕ
  /-- the encoding is faithful (distinct elements, distinct codes) -/
  enc_inj : Function.Injective enc

attribute [instance] Assembly.fin

/-- The assembly's codes fit in `sworkBits` bits of work memory (§4.1: objects ⊆ `{0,1}^{|s_work|}`). -/
def Assembly.FitsIn (A : Assembly) (sworkBits : ℕ) : Prop := ∀ x, A.enc x < 2 ^ sworkBits

/-- **Functions as data** (§4.1): a function `f` is *realized* if some code `r` tracks it — the
universal evaluator applied to `r` and an element's code returns the code of the image. The realizer
`r` is itself a value (a `Code`). -/
def Realizes {A B : Assembly} (f : A.carrier → B.carrier) : Prop :=
  ∃ r : Code, ∀ x, r.eval (A.enc x) = Part.some (B.enc (f x))

/-- The identity is realized, by `Code.id`. -/
theorem realizes_id (A : Assembly) : Realizes (A := A) (B := A) id :=
  ⟨Code.id, fun x => by simp [Code.eval_id]⟩

/-- Realized functions compose, with realizer `Code.comp` (= "apply `f` then `g`"). -/
theorem realizes_comp {A B C : Assembly} {g : B.carrier → C.carrier} {f : A.carrier → B.carrier}
    (hg : Realizes g) (hf : Realizes f) : Realizes (g ∘ f) := by
  obtain ⟨rf, hrf⟩ := hf
  obtain ⟨rg, hrg⟩ := hg
  refine ⟨rg.comp rf, fun x => ?_⟩
  have hcomp : (rg.comp rf).eval (A.enc x) = (rf.eval (A.enc x)).bind rg.eval := rfl
  rw [hcomp, hrf x, Part.bind_some]
  exact hrg (f x)

/-- The **realizability category** of finite assemblies: morphisms are exactly the code-realizable
functions (the realizer existentially witnessed — functions as data). A genuine
`CategoryTheory.Category`. -/
instance : Category Assembly where
  Hom A B := { f : A.carrier → B.carrier // Realizes f }
  id A := ⟨id, realizes_id A⟩
  comp f g := ⟨g.1 ∘ f.1, realizes_comp g.2 f.2⟩
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

/-! ### Every function between finite assemblies is a morphism (the §4.1 finiteness fact)

§4.1 records, as the reason no "computation budget" clause is needed, that *because the objects are
finite, every morphism is a total function that halts on every input*. We machine-check exactly that
converse-free fact: **every** function between finite assemblies is realized by a code, so it is a
genuine morphism of the realizability category — not merely a total set-function. The realizer is a
code doing finite table lookup over the (injectively encoded) domain, built by folding `Primrec.ite`
over `Finset.univ` and extracting a code via `Nat.Partrec.Code.exists_code`.

**Consequence for §6.3 (Theorem 6.3, L2a/L2b).** The bounded proof-checker `Prf : Formula × ProofCode
→ Bool` and the decision morphism `Decide : Formula → Bool` are functions between *finite* objects
(`GodelChecker.Formula`/`ProofCode` are `Fintype`s), so by `realizes_of_finite` they are morphisms of
Rep(S). This discharges, at the level of the realizability category, the "`Prf`/`Decide` is a
morphism of Rep(S)" step that §6.3 previously asserted from finiteness — now machine-checked. -/

/-- Finite table lookup at the ℕ level: the value paired with the first matching key, else `0`.
The realizer-defining function behind `realizes_of_finite`. -/
def tableFn : List (ℕ × ℕ) → ℕ → ℕ
  | [], _ => 0
  | (k, v) :: rest, n => if n = k then v else tableFn rest n

/-- `tableFn l` is primitive recursive (a finite `if`-cascade over a fixed list). -/
theorem tableFn_primrec : ∀ l : List (ℕ × ℕ), Primrec (tableFn l)
  | [] => by
      change Primrec (fun _ : ℕ => (0 : ℕ))
      exact Primrec.const 0
  | (k, v) :: rest => by
      have hcp : PrimrecPred (fun n : ℕ => n = k) :=
        Primrec.eq.comp Primrec.id (Primrec.const k)
      change Primrec (fun n : ℕ => if n = k then v else tableFn rest n)
      exact Primrec.ite hcp (Primrec.const v) (tableFn_primrec rest)

/-- Evaluation of `tableFn` at a key present in the list, when the list is *functional* at that key
(every pair sharing the key shares the value) — so the first-match result is the intended value. -/
theorem tableFn_eval {k v : ℕ} : ∀ l : List (ℕ × ℕ), (k, v) ∈ l →
    (∀ k' v', (k', v') ∈ l → k' = k → v' = v) → tableFn l k = v := by
  intro l
  induction l with
  | nil => intro hmem _; simp at hmem
  | cons hd rest ih =>
      obtain ⟨k0, v0⟩ := hd
      intro hmem huniq
      rw [List.mem_cons] at hmem
      by_cases hk : k = k0
      · have hv : v0 = v := huniq k0 v0 List.mem_cons_self hk.symm
        change (if k = k0 then v0 else tableFn rest k) = v
        rw [if_pos hk, hv]
      · have hmem' : (k, v) ∈ rest := by
          rcases hmem with h | h
          · exact absurd (congrArg Prod.fst h) hk
          · exact h
        have hrec : tableFn rest k = v :=
          ih hmem' (fun k' v' hk'mem hk'eq => huniq k' v' (List.mem_cons_of_mem _ hk'mem) hk'eq)
        change (if k = k0 then v0 else tableFn rest k) = v
        rw [if_neg hk, hrec]

/-- **Every function between finite assemblies is realized** — a morphism of the realizability
category. The §4.1 fact that finiteness makes every total function a morphism (functions-as-data: the
realizer is an explicit code). In particular the §6.3 `Prf`/`Decide` maps on finite
`Formula`/`ProofCode` objects are morphisms of Rep(S), not merely total Boolean functions. -/
theorem realizes_of_finite {A B : Assembly} (f : A.carrier → B.carrier) : Realizes f := by
  classical
  set pts : List (ℕ × ℕ) := (Finset.univ.toList).map (fun x => (A.enc x, B.enc (f x))) with hpts
  obtain ⟨c, hc⟩ :=
    Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp (tableFn_primrec pts).to_comp)
  refine ⟨c, fun x => ?_⟩
  have hmem : (A.enc x, B.enc (f x)) ∈ pts := by
    rw [hpts, List.mem_map]
    exact ⟨x, Finset.mem_toList.mpr (Finset.mem_univ x), rfl⟩
  have huniq : ∀ k' v', (k', v') ∈ pts → k' = A.enc x → v' = B.enc (f x) := by
    intro k' v' hk'mem hk'eq
    rw [hpts, List.mem_map] at hk'mem
    obtain ⟨y, _, hy⟩ := hk'mem
    rw [Prod.mk.injEq] at hy
    obtain ⟨hy1, hy2⟩ := hy
    have hyx : y = x := A.enc_inj (by rw [hy1, hk'eq])
    rw [← hy2, hyx]
  have hkey : tableFn pts (A.enc x) = B.enc (f x) := tableFn_eval pts hmem huniq
  have heval : c.eval (A.enc x) = Part.some (tableFn pts (A.enc x)) := by rw [hc]; rfl
  rw [heval, hkey]

/-! ### Products of assemblies (realized projections and pairing) -/

/-- Product assembly: carrier `A.carrier × B.carrier`, encoded by `Nat.pair` of the codes. -/
def prodAsm (A B : Assembly) : Assembly where
  carrier := A.carrier × B.carrier
  enc p := Nat.pair (A.enc p.1) (B.enc p.2)
  enc_inj p q h := by
    have h2 := congrArg Nat.unpair h
    simp only [Nat.unpair_pair, Prod.mk.injEq] at h2
    exact Prod.ext (A.enc_inj h2.1) (B.enc_inj h2.2)

/-- The first projection is realized, by `Code.left`. -/
theorem fst_realizes (A B : Assembly) :
    Realizes (A := prodAsm A B) (B := A) (Prod.fst : A.carrier × B.carrier → A.carrier) := by
  refine ⟨Code.left, ?_⟩
  rintro ⟨a, b⟩
  change Code.left.eval (Nat.pair (A.enc a) (B.enc b)) = Part.some (A.enc a)
  have h : Code.left.eval (Nat.pair (A.enc a) (B.enc b))
      = Part.some ((Nat.pair (A.enc a) (B.enc b)).unpair.1) := rfl
  rw [h, Nat.unpair_pair]

/-- The second projection is realized, by `Code.right`. -/
theorem snd_realizes (A B : Assembly) :
    Realizes (A := prodAsm A B) (B := B) (Prod.snd : A.carrier × B.carrier → B.carrier) := by
  refine ⟨Code.right, ?_⟩
  rintro ⟨a, b⟩
  change Code.right.eval (Nat.pair (A.enc a) (B.enc b)) = Part.some (B.enc b)
  have h : Code.right.eval (Nat.pair (A.enc a) (B.enc b))
      = Part.some ((Nat.pair (A.enc a) (B.enc b)).unpair.2) := rfl
  rw [h, Nat.unpair_pair]

/-- Pairing of realized maps is realized, by `Code.pair`. -/
theorem pair_realizes {A B C : Assembly} {f : C.carrier → A.carrier} {g : C.carrier → B.carrier}
    (hf : Realizes f) (hg : Realizes g) :
    Realizes (A := C) (B := prodAsm A B) (fun c => (f c, g c)) := by
  obtain ⟨rf, hrf⟩ := hf
  obtain ⟨rg, hrg⟩ := hg
  refine ⟨Code.pair rf rg, fun c => ?_⟩
  change (Code.pair rf rg).eval (C.enc c) = Part.some (Nat.pair (A.enc (f c)) (B.enc (g c)))
  have h : (Code.pair rf rg).eval (C.enc c)
      = (Nat.pair <$> rf.eval (C.enc c) <*> rg.eval (C.enc c)) := rfl
  rw [h, hrf c, hrg c]
  simp [Seq.seq, Part.bind_some, Part.map_some]

/-! ### Combinatory completeness: the evaluation and currying realizers (toward the exponential)

The realizability *exponential* `[A ⇒ B]` of §4.3 needs two computational ingredients — a code that
*applies* a realizer to an argument (evaluation), and one that *specializes* a realizer in its first
argument (currying / s-m-n). Both are provided here over `Nat.Partrec.Code`. These are the
"functions as data" universal-property content: realizer codes can themselves be applied and built.
(Packaging `[A ⇒ B]` as an assembly *object* additionally needs the **modest/relational** form of
`Assembly` — each morphism realized by *many* codes, "under extensional equality" §4.3 — a
generalization of the single-encoding `Assembly` here; see the module note.) -/

/-- **The universal evaluator as a code** (the evaluation realizer): a single code `E` that applies
an encoded realizer to an argument — `E · ⟨⌜r⌝, a⟩ = r · a`. Built from Mathlib's universal `eval`
(`Code.eval_part : Partrec₂ eval`) via `exists_code`. -/
theorem universal_evaluator :
    ∃ E : Nat.Partrec.Code, ∀ (r : Nat.Partrec.Code) (a : ℕ),
      E.eval (Nat.pair (Encodable.encode r) a) = r.eval a := by
  have hp : Nat.Partrec (fun n : ℕ => Code.eval (Denumerable.ofNat Code n.unpair.1) n.unpair.2) := by
    rw [← Partrec.nat_iff]
    exact Code.eval_part.comp
      ((Computable.ofNat Code).comp (Computable.fst.comp Primrec.unpair.to_comp))
      (Computable.snd.comp Primrec.unpair.to_comp)
  obtain ⟨E, hE⟩ := Nat.Partrec.Code.exists_code.mp hp
  refine ⟨E, fun r a => ?_⟩
  have h2 := congrFun hE (Nat.pair (Encodable.encode r) a)
  simpa only [Nat.unpair_pair, Denumerable.ofNat_encode] using h2

/-- **The currying realizer** (s-m-n): specializing a realizer `r` of a two-argument map in its
first argument `c` yields a realizer `curry r c` of the one-argument residual —
`(curry r c) · a = r · ⟨c, a⟩`. This is Mathlib's `eval_curry`, the form §4.3 uses to build
`[A ⇒ B]` (a realizer for `a ↦ g(c,a)` from one for `g`). -/
theorem currying_realizer (r : Nat.Partrec.Code) (c a : ℕ) :
    (Nat.Partrec.Code.curry r c).eval a = r.eval (Nat.pair c a) :=
  Nat.Partrec.Code.eval_curry r c a

/-! ### The modular-counter instance: the FV-6 successor is functions-as-data -/

/-- The modular-counter assembly (the FV-6 carrier `ZMod (n+1)`, encoded by `ZMod.val`).
Reducible so the carrier's `Add`/`One`/`ZMod.val` instances are visible at use sites. -/
abbrev counterAssembly (n : ℕ) : Assembly :=
  { carrier := ZMod (n + 1)
    enc := ZMod.val
    enc_inj := ZMod.val_injective (n + 1) }

/-- The core fact on the explicit carrier `ZMod (n+1)`: a code tracks the modular successor on
`ZMod.val`-encodings. Obtained from the computable `m ↦ (m+1) % (n+1)` via Mathlib's `exists_code`. -/
theorem exists_code_tracks_succ (n : ℕ) :
    ∃ c : Nat.Partrec.Code, ∀ x : ZMod (n + 1),
      c.eval (ZMod.val x) = Part.some (ZMod.val (x + 1)) := by
  haveI : NeZero (n + 1) := ⟨n.succ_ne_zero⟩
  have hg : Computable (fun m => (m + 1) % (n + 1)) :=
    (Primrec.nat_mod.comp Primrec.succ (Primrec.const (n + 1))).to_comp
  obtain ⟨c, hc⟩ := Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp hg)
  refine ⟨c, fun x => ?_⟩
  have hcx : c.eval (ZMod.val x) = Part.some ((ZMod.val x + 1) % (n + 1)) := by rw [hc]; rfl
  have e : (x + 1 : ZMod (n + 1)) = ((ZMod.val x + 1 : ℕ) : ZMod (n + 1)) := by
    rw [Nat.cast_add, Nat.cast_one, ZMod.natCast_zmod_val]
  rw [hcx, e, ZMod.val_natCast]

/-- **The counter's successor is realized** (functions-as-data, concretely): the modular successor
`step : x ↦ x + 1` on `ZMod (n+1)` — the FV-6 bounded-recursor successor — is a morphism of the
realizability category, its realizer a value (a `Nat.Partrec.Code`). Packaged from
`exists_code_tracks_succ` by defeq (`counterAssembly`'s carrier is `ZMod (n+1)`, `enc` is `ZMod.val`). -/
theorem counter_step_realizes (n : ℕ) :
    Realizes (A := counterAssembly n) (B := counterAssembly n) (fun x : ZMod (n + 1) => x + 1) :=
  exists_code_tracks_succ n

end Realizability
