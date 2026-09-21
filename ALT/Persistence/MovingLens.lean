/-
Copyright (c) 2026 Mykola Palamarchuk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mykola Palamarchuk
-/
module

public import Batteries.Tactic.OpenPrivate
public import Mathlib.Data.List.GetD
public import ALT.AdditiveComplexity
public import ALT.Code.EvalLaws
public import ALT.Persistence.Core
import all ALT.Persistence.Core

-- Formal-check file, not Mathlib-destined: opt out of the house-style header linter.
set_option linter.style.header false

/-!
# Persistence capacity II: determination and the observer's ledger ([Decoupling] §3.5(iii))

Part two of the `PersistenceCapacity` development (umbrella and map: `ALT.PersistenceCapacity`).
`ALT.Persistence.Core` bounds WHAT a moving decoder can carry; this module states what carrying
it COSTS: on the recurrent core the family has no freedom left, and the world's recurrent rule
can be read off the observer's first two frames.

## Main results

* `corePerm` / `carries_coreLens_eq` / `carries_frame_eqOn_core` / `carries_frame_zero_congr` —
  **the frames are determined on the core, and the reference frame is pinned everywhere**: over
  ANY endofunction world, `U` restricted to the core is a permutation `corePerm`, and a carried
  family satisfies `ℓ t = ℓ 0 ∘ (corePerm U ^ t)⁻¹` there. `ℓ 0` itself is forced through the
  retraction onto the core; what stays free are the later frames, off the image of `U^[t]`.
* `lens_bijOn_core` / `ledger` / `ledger_determines` — the price of the escape: if the family
  carries a MAXIMAL model then every frame is a bijection on the core and `U` restricted to the
  core is `ℓ₁⁻¹ ∘ ℓ₀` — the world's recurrent rule is recoverable from the observer's first two
  frames.
* `ledger_K` — the same in complexity form: `KE (U ↾ core) ≤ KE ℓ₀ + KE ℓ₁ + O(1)`, the constant
  being the length of a single fixed invert-and-compose program (`icode`) that depends on neither
  the world, the lens, the enumerations, nor the size of the memory. The complexity has not
  vanished; it has been relocated, out of the world and into the decoder.
-/

@[expose] public section

namespace PersistenceCapacity

open Decoupling CodeEvalLaws

variable {X ι V M : Type*}

-- File-boundary bookkeeping for the split development: these helpers stay `private` (they are
-- proof plumbing, not interface), and the sibling modules reach them with `open private`.
open private bijOn_iterate core_eq_image invFunOn_iterate_left univ_closed from
  ALT.Persistence.Core

/-! ### Determination on the core: every frame is the reference frame, transported

[Persistence] §2, Definition 2.2 prices an entire persistent family by the carried entropy of its
reference frame *on the recurrent core*, on the ground that "on the core every frame is `ℓ₀`
composed with a power of the core permutation, so all frames share one profile". This section proves
that, for an arbitrary endofunction world.

Off the core the identity is not silent: it still pins the reference frame. `ℓ 0` is forced through
the retraction onto the core, so it already agrees on any two states the dynamics ever merges
(`carries_frame_zero_congr`). What it leaves free are the LATER frames — `ℓ t` for `t ≥ 1` may read
a state off the image of `U^[t]` however it likes, and the identity says nothing there. On the core
`U` *is* a bijection (`core_bijOn`), hence a genuine permutation `corePerm` of the core, and the
identity solves for `ℓ t` there exactly as it does over a permutation world
(`permCarries_frame_eq`) — the difference being that here the inverse exists only after
restricting. -/

/-- **The recurrent rule, as a permutation of the core.** `U` restricts to a bijection there
(`core_bijOn`), so the core carries a genuine `Equiv.Perm`: the world's reversible part, extracted
from an update that need not be reversible anywhere else. -/
noncomputable def corePerm [Finite X] (U : X → X) : Equiv.Perm ↥(core U) :=
  Set.BijOn.equiv U (core_bijOn U)

@[simp] private theorem corePerm_apply [Finite X] (U : X → X) (x : ↥(core U)) :
    ((corePerm U x : X)) = U x := rfl

/-- The core permutation's powers are the world's iterates, read on the core. -/
private theorem corePerm_pow_apply [Finite X] (U : X → X) (t : ℕ) (x : ↥(core U)) :
    (((corePerm U ^ t) x : X)) = U^[t] x := by
  induction t generalizing x with
  | zero => rfl
  | succ t ih =>
      rw [pow_succ, Equiv.Perm.mul_apply, ih, corePerm_apply, Function.iterate_succ_apply]

/-- **The rule on an attractor, as a permutation.** `U` restricts to a bijection on the ω-limit set
of any closed `B` (`omegaLimit_bijOn`), so an attractor carries a genuine `Equiv.Perm`: the
recurrent rule of the sub-world that orbits from `B` settle into. `corePerm` is the case
`B = univ`. -/
noncomputable def omegaPerm [Finite X] (U : X → X) {B : Set X} (hB : ∀ s ∈ B, U s ∈ B) :
    Equiv.Perm ↥(omegaLimit U B) :=
  Set.BijOn.equiv U (omegaLimit_bijOn U hB)

@[simp] private theorem omegaPerm_apply [Finite X] (U : X → X) {B : Set X} (hB : ∀ s ∈ B, U s ∈ B)
    (x : ↥(omegaLimit U B)) : ((omegaPerm U hB x : X)) = U x := rfl

/-- The attractor permutation's powers are the world's iterates, read on the attractor. -/
private theorem omegaPerm_pow_apply [Finite X] (U : X → X) {B : Set X} (hB : ∀ s ∈ B, U s ∈ B)
    (t : ℕ) (x : ↥(omegaLimit U B)) : (((omegaPerm U hB ^ t) x : X)) = U^[t] x := by
  induction t generalizing x with
  | zero => rfl
  | succ t ih =>
      rw [pow_succ, Equiv.Perm.mul_apply, ih, omegaPerm_apply, Function.iterate_succ_apply]

/-- A lens **restricted to the recurrent core** — the only part of it the persistence identity
constrains, and the part [Persistence] §2, Definition 2.2 measures the carried entropy of. This is
`Set.domRestrict` at `core U`; the ω-limit sections below use `Set.domRestrict` directly. -/
def coreLens (U : X → X) (f : X → M) : ↥(core U) → M := fun x => f x

/-- **Every frame is the reference frame, transported by the recurrent rule** — the endofunction
analogue of `permCarries_frame_eq`, and the fact [Persistence] §2, Definition 2.2 appeals to when it
prices a whole family by `E (ℓ₀)`.

`corePerm U ^ t` is invertible, so the persistence identity `ℓ t ∘ U^[t] = ℓ 0` solves on the core
for `ℓ t = ℓ 0 ∘ (corePerm U ^ t)⁻¹`: a carried family has no freedom on the core past its reference
frame, over ANY endofunction world — the recurrent part of every reading is one relabelling of
`ℓ 0`. Off the core it is only the LATER frames that are unconstrained: `ℓ t` for `t ≥ 1` may read a
transient state off the image of `U^[t]` however it likes. `ℓ 0` itself is pinned everywhere, forced
through the retraction onto the core (`carries_frame_zero_congr`).

Spelled as an explicit composition rather than through the relabelling action, for the reason given
at `arrowAction` below: the two are definitionally equal, and only this one means what it says after
elaboration. -/
theorem carries_coreLens_eq [Finite X] {U : X → X} {ℓ : Lens X M} (h : Carries U ℓ) (t : ℕ) :
    coreLens U (ℓ t) = coreLens U (ℓ 0) ∘ ⇑(corePerm U ^ t)⁻¹ := by
  funext x
  have hy := h.2 t (((corePerm U ^ t)⁻¹ x : ↥(core U)) : X)
  rw [← corePerm_pow_apply U t ((corePerm U ^ t)⁻¹ x)] at hy
  simpa [coreLens] using hy

/-- **The reference frame factors through the retraction onto the core** ([Persistence] §2,
Definition 2.2; §6, Theorem 6.1's own proof step). Persistence at any `t` merging two states forces
`ℓ 0` to read them alike — no finiteness and no stabilizing index needed, this holds at whatever `t`
merges the two states, which is the sharp form. Only the LATER frames are free, and only off the
image of `U^[t]` (`carries_coreLens_eq`). Over a permutation world the content is empty: the
retraction is the identity, and every state is already its own image. -/
theorem carries_frame_zero_congr {U : X → X} {ℓ : Lens X M} (h : Carries U ℓ) {s s' : X} {t : ℕ}
    (hst : U^[t] s = U^[t] s') : ℓ 0 s = ℓ 0 s' := by
  rw [← h.2 t s, ← h.2 t s', hst]

/-- **Determination on the core, ambiently**: the same statement read back in `X`, with the core
permutation's inverse spelled as `U`'s inverse along the core. `Set.EqOn` is the honest form —
off the core THIS equation says nothing, `invFunOn` having no meaning there. The identity itself is
not silent off the core: it pins `ℓ 0` everywhere (`carries_frame_zero_congr`). -/
theorem carries_frame_eqOn_core [Finite X] [Nonempty X] {U : X → X} {ℓ : Lens X M}
    (h : Carries U ℓ) (t : ℕ) :
    Set.EqOn (ℓ t) (ℓ 0 ∘ (Function.invFunOn U (core U))^[t]) (core U) := by
  intro x hx
  obtain ⟨z, hz, rfl⟩ := (bijOn_iterate (core_bijOn U) t).surjOn hx
  simp only [Function.comp_apply, invFunOn_iterate_left U hz t]
  exact h.2 t z

/-! ### The observer's ledger: the price of a moving lens ([Decoupling] §3.5(iii))

If the family carries the MAXIMAL model then every frame is a bijection on the core, and the world's
recurrent rule falls out of the observer's first two frames. The complexity does not vanish; it is
relocated, out of the world and into the decoder. -/

/-- Every frame of a maximal family is a bijection from the core onto the model. -/
theorem lens_bijOn_core [Finite ι] [Finite V] [Fintype M] {U : Mem ι V → Mem ι V}
    {ℓ : Lens (Mem ι V) M} (h : Carries U ℓ) (hmax : Fintype.card M = Nat.card (core U)) (t : ℕ) :
    Set.BijOn (ℓ t) (core U) Set.univ := by
  obtain ⟨N, hcore, hstab⟩ := core_eq_image U
  -- past the stabilization index, surjectivity onto the model plus a cardinality count
  have hbase : ∀ T, N ≤ T → Set.BijOn (ℓ T) (core U) Set.univ := by
    intro T hT
    have hsurj : Set.SurjOn (ℓ T) (core U) Set.univ := by
      intro m _
      obtain ⟨s, hs⟩ := h.1 m
      refine ⟨U^[T] s, ?_, by rw [h.2 T s, hs]⟩
      rw [hcore, ← hstab T hT]
      exact ⟨s, Set.mem_univ _, rfl⟩
    have himg : (ℓ T) '' (core U) = Set.univ :=
      Set.eq_univ_of_univ_subset (fun m hm => hsurj hm)
    have hncard : ((ℓ T) '' (core U)).ncard = (core U).ncard := by
      rw [himg, Set.ncard_univ, ← Nat.card_coe_set_eq, ← hmax, Nat.card_eq_fintype_card]
    exact ⟨fun x _ => Set.mem_univ _, Set.injOn_of_ncard_image_eq hncard (Set.toFinite _), hsurj⟩
  -- a general frame is the stabilized frame precomposed with `U^[N]`, a bijection of the core
  have hUN : Set.BijOn (U^[N]) (core U) (core U) := bijOn_iterate (core_bijOn U) N
  have heq : Set.EqOn (ℓ (t + N) ∘ U^[N]) (ℓ t) (core U) := by
    intro x hx
    have hxt : x ∈ (U^[t]) '' Set.univ := Set.mem_iInter.mp hx t
    obtain ⟨z, -, rfl⟩ := hxt
    have h1 : (U^[N]) (U^[t] z) = U^[t + N] z := by
      rw [← Function.iterate_add_apply, Nat.add_comm]
    simp only [Function.comp_apply, h1, h.2 (t + N) z, h.2 t z]
  exact ((hbase (t + N) (by omega)).comp hUN).congr heq

/-- **The ledger** ([Decoupling] §3.5(iii)). For a maximal model, `U` restricted to the core is
`ℓ₁⁻¹ ∘ ℓ₀`: the observer's first two frames DETERMINE the world's recurrent update rule. The
complexity has not vanished — it has moved out of the world and into the decoder. -/
theorem ledger [Finite ι] [Finite V] [Fintype M] [Nonempty (Mem ι V)] {U : Mem ι V → Mem ι V}
    {ℓ : Lens (Mem ι V) M} (h : Carries U ℓ) (hmax : Fintype.card M = Nat.card (core U))
    {s : Mem ι V} (hs : s ∈ core U) :
    U s = Function.invFunOn (ℓ 1) (core U) (ℓ 0 s) := by
  have hb := lens_bijOn_core h hmax 1
  have hUs : U s ∈ core U := (core_bijOn U).mapsTo hs
  have h1 : ℓ 1 (U s) = ℓ 0 s := by simpa using h.2 1 s
  have hinv := hb.injOn.leftInvOn_invFunOn hUs
  rw [← h1, hinv]

/-- **The ledger, choice-free form.** Two worlds with the same recurrent core, observed by families
whose first two frames agree, have the SAME recurrent rule. This is the determination content of
`ledger` — "the world's rule is recoverable from the observer's first two frames" — with no inverse
function, hence no choice. The Kolmogorov reading `K (U ↾ core) ≤ K ℓ₀ + K ℓ₁ + O(1)` rides the
standard encoding of these finite tables. -/
theorem ledger_determines [Finite ι] [Finite V] [Fintype M] {U U' : Mem ι V → Mem ι V}
    {ℓ ℓ' : Lens (Mem ι V) M} (h : Carries U ℓ) (hmax : Fintype.card M = Nat.card (core U))
    (h' : Carries U' ℓ') (hcore : core U = core U')
    (h0 : ℓ 0 = ℓ' 0) (h1 : ℓ 1 = ℓ' 1) : ∀ s ∈ core U, U s = U' s := by
  intro s hs
  have hinj := (lens_bijOn_core h hmax 1).injOn
  have hUs : U s ∈ core U := (core_bijOn U).mapsTo hs
  have hU's : U' s ∈ core U := by
    rw [hcore]
    exact (core_bijOn U').mapsTo (hcore ▸ hs)
  refine hinj hUs hU's ?_
  have e1 : ℓ 1 (U s) = ℓ 0 s := by simpa using h.2 1 s
  have e2 : ℓ' 1 (U' s) = ℓ' 0 s := by simpa using h'.2 1 s
  rw [e1, h1] at *
  rw [h0]
  rw [← e2, h1]

/-! ### The ledger in complexity form ([Decoupling] §3.5(iii))

The identity `U ↾ core = ℓ₁⁻¹ ∘ ℓ₀` becomes a Kolmogorov bound once the three finite objects are
tabulated. Fix an enumeration `eC` of the core and `eM` of the model; a frame tabulates as the list
of model indices it reads off the core states (`frameTable`), and the world's recurrent rule
tabulates as the list of core indices it steps to (`worldTable`). Then ONE program — invert the
second table and compose it with the first (`invcomp`, a single fixed `Code`, `icode`) — recovers
the world's table from the observer's first two frames, so

`KE (worldTable) ≤ KE (frameTable 0) + KE (frameTable 1) + O(1)`

with a constant that does not depend on the world, the lens, the enumerations, or the memory size.
The world's recurrent rule is no more complex than the observer's first two frames: the complexity
has not vanished, it has been relocated into the decoder. -/

open AdditiveComplexity KolmogorovComplexity Nat.Partrec Nat.Partrec.Code

/-- First-occurrence index of `v` in a list of naturals (`0` if absent) — table inversion. -/
def idx (v : ℕ) (L : List ℕ) : ℕ :=
  L.rec 0 fun b _ IH => if b = v then 0 else IH + 1

@[simp] private theorem idx_nil (v : ℕ) : idx v [] = 0 := rfl

@[simp] private theorem idx_cons (v b : ℕ) (L : List ℕ) :
    idx v (b :: L) = if b = v then 0 else idx v L + 1 := rfl

/-- Table inversion is correct on a duplicate-free table: the index of the `i`-th entry is `i`. -/
private theorem idx_getElem :
    ∀ {L : List ℕ}, L.Nodup → ∀ {i : ℕ} (hi : i < L.length), idx L[i] L = i
  | [], _, i, hi => absurd hi (by simp)
  | b :: T, _, 0, _ => by simp
  | b :: T, hL, (k + 1), hk => by
      rw [List.nodup_cons] at hL
      have hlt : k < T.length := by simpa using hk
      have hne : b ≠ T[k] := fun hcon => hL.1 (hcon ▸ List.getElem_mem hlt)
      have hrec : idx T[k] T = k := idx_getElem hL.2 hlt
      simpa [hne] using hrec

/-- Table inversion on an injective tabulation over `Fin n`. -/
private theorem idx_map_finRange {n : ℕ} (f : Fin n → ℕ) (hf : Function.Injective f) (j : Fin n) :
    idx (f j) ((List.finRange n).map f) = (j : ℕ) := by
  have hnodup : ((List.finRange n).map f).Nodup :=
    (List.nodup_finRange n).map hf
  have hlen : ((List.finRange n).map f).length = n := by simp
  have hj : (j : ℕ) < ((List.finRange n).map f).length := by rw [hlen]; exact j.2
  have hget : ((List.finRange n).map f)[(j : ℕ)] = f j := by simp
  have := idx_getElem hnodup hj
  rwa [hget] at this

/-- **The fixed invert-and-compose program.** On the pair of encoded tables `⟨t₀, t₁⟩` it maps each
entry of `t₀` to its position in `t₁` — that is, it computes `t₁⁻¹ ∘ t₀`. -/
def invcomp (p : ℕ) : ℕ :=
  Encodable.encode
    (((Encodable.decode (α := List ℕ) p.unpair.1).getD []).map fun v =>
      idx v ((Encodable.decode (α := List ℕ) p.unpair.2).getD []))

private theorem primrec_idx : Primrec fun p : ℕ × List ℕ => idx p.1 p.2 := by
  have h : Primrec₂ fun (p : ℕ × List ℕ) (t : ℕ × List ℕ × ℕ) =>
      if t.1 = p.1 then 0 else t.2.2 + 1 :=
    Primrec.ite (Primrec.eq.comp (Primrec.fst.comp Primrec.snd) (Primrec.fst.comp Primrec.fst))
      (Primrec.const 0) (Primrec.succ.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
  exact Primrec.list_rec Primrec.snd (Primrec.const 0) h

private theorem primrec_invcomp : Primrec invcomp := by
  have hdec1 : Primrec fun p : ℕ => (Encodable.decode (α := List ℕ) p.unpair.1).getD [] :=
    Primrec.option_getD.comp (Primrec.decode.comp (Primrec.fst.comp Primrec.unpair))
      (Primrec.const [])
  have hdec2 : Primrec fun p : ℕ => (Encodable.decode (α := List ℕ) p.unpair.2).getD [] :=
    Primrec.option_getD.comp (Primrec.decode.comp (Primrec.snd.comp Primrec.unpair))
      (Primrec.const [])
  have hg : Primrec₂ fun (p : ℕ) (v : ℕ) =>
      idx v ((Encodable.decode (α := List ℕ) p.unpair.2).getD []) :=
    primrec_idx.comp (Primrec.pair Primrec.snd (hdec2.comp Primrec.fst))
  exact Primrec.encode.comp (Primrec.list_map hdec1 hg)

/-- `invcomp` is partial recursive. -/
theorem partrec_invcomp : Nat.Partrec invcomp :=
  Partrec.nat_iff.mp primrec_invcomp.to_comp.partrec

/-- The invert-and-compose program as a single fixed `Code`: its length `elen icode` is the whole
constant in `ledger_K`, and it depends on nothing else. -/
noncomputable def icode : Code := Classical.choose (exists_code.mp partrec_invcomp)

private theorem eval_icode (p : ℕ) : icode.eval p = Part.some (invcomp p) := by
  have h := congrFun (Classical.choose_spec (exists_code.mp partrec_invcomp)) p
  simpa [icode] using h

/-- The observer's frame `t`, **tabulated**: the model index each core state is read as, listed
along an enumeration `eC` of the core. -/
def frameTable {n : ℕ} (U : Mem ι V → Mem ι V) (ℓ : Lens (Mem ι V) M) (t : ℕ)
    (eC : ↥(core U) ≃ Fin n) (eM : M ≃ Fin n) : List ℕ :=
  (List.finRange n).map fun i => ((eM (ℓ t ((eC.symm i : ↥(core U)) : Mem ι V)) : Fin n) : ℕ)

/-- The world's recurrent rule, **tabulated**: the core index each core state steps to. -/
noncomputable def worldTable [Finite ι] [Finite V] {n : ℕ} (U : Mem ι V → Mem ι V)
    (eC : ↥(core U) ≃ Fin n) : List ℕ :=
  (List.finRange n).map fun i =>
    ((eC ⟨U ((eC.symm i : ↥(core U)) : Mem ι V),
      (core_bijOn U).mapsTo (eC.symm i).2⟩ : Fin n) : ℕ)

/-- The fixed program recovers the world's table from the observer's first two frames. -/
private theorem invcomp_frameTables [Finite ι] [Finite V] [Fintype M] {U : Mem ι V → Mem ι V}
    {ℓ : Lens (Mem ι V) M} (h : Carries U ℓ) (hmax : Fintype.card M = Nat.card (core U))
    {n : ℕ} (eC : ↥(core U) ≃ Fin n) (eM : M ≃ Fin n) :
    invcomp (Nat.pair (Encodable.encode (frameTable U ℓ 0 eC eM))
      (Encodable.encode (frameTable U ℓ 1 eC eM))) = Encodable.encode (worldTable U eC) := by
  -- the two tabulations, as functions on the index set
  set f₀ : Fin n → ℕ := fun i => ((eM (ℓ 0 ((eC.symm i : ↥(core U)) : Mem ι V)) : Fin n) : ℕ)
    with hf₀
  set f₁ : Fin n → ℕ := fun i => ((eM (ℓ 1 ((eC.symm i : ↥(core U)) : Mem ι V)) : Fin n) : ℕ)
    with hf₁
  -- `ℓ 1` is injective on the core (maximal model), so its tabulation is injective
  have hinj₁ : Function.Injective f₁ := by
    intro i j hij
    have h1 : ℓ 1 ((eC.symm i : ↥(core U)) : Mem ι V) = ℓ 1 ((eC.symm j : ↥(core U)) : Mem ι V) :=
      eM.injective (Fin.val_injective hij)
    have h2 := (lens_bijOn_core h hmax 1).injOn (eC.symm i).2 (eC.symm j).2 h1
    exact eC.symm.injective (Subtype.ext h2)
  simp only [invcomp, Nat.unpair_pair, Encodable.encodek, Option.getD_some, frameTable, worldTable,
    List.map_map, ← hf₀, ← hf₁]
  refine congrArg Encodable.encode (List.map_congr_left fun i _ => ?_)
  -- the ledger, in index form: the core state `U s` is the unique one `ℓ 1` reads as `ℓ 0 s`
  set j₀ : Fin n := eC ⟨U ((eC.symm i : ↥(core U)) : Mem ι V),
    (core_bijOn U).mapsTo (eC.symm i).2⟩ with hj₀
  have hstep : f₁ j₀ = f₀ i := by
    have hval : ((eC.symm j₀ : ↥(core U)) : Mem ι V) = U ((eC.symm i : ↥(core U)) : Mem ι V) := by
      rw [hj₀, Equiv.symm_apply_apply]
    have hcarry : ℓ 1 (U ((eC.symm i : ↥(core U)) : Mem ι V))
        = ℓ 0 ((eC.symm i : ↥(core U)) : Mem ι V) := by
      simpa using h.2 1 ((eC.symm i : ↥(core U)) : Mem ι V)
    simp only [hf₀, hf₁, hval, hcarry]
  change idx (f₀ i) ((List.finRange n).map f₁) = (j₀ : ℕ)
  rw [← hstep]
  exact idx_map_finRange f₁ hinj₁ j₀

/-- **The ledger, in complexity form** ([Decoupling] §3.5(iii)). The world's recurrent rule is no
more complex than the observer's first two frames: `KE (U ↾ core) ≤ KE ℓ₀ + KE ℓ₁ + O(1)`, where the
constant is the length of the single fixed invert-and-compose program and depends on nothing —
neither the world, nor the lens, nor the enumerations, nor the size of the memory.

The complexity has not vanished; it has been RELOCATED, out of the world and into the decoder. An
observer that evades the Total-Overwrite Exclusion with a moving lens must therefore store, in its
first two frames, a description of the world's recurrent rule. -/
theorem ledger_K [Finite ι] [Finite V] [Fintype M] {U : Mem ι V → Mem ι V} {ℓ : Lens (Mem ι V) M}
    (h : Carries U ℓ) (hmax : Fintype.card M = Nat.card (core U))
    {n : ℕ} (eC : ↥(core U) ≃ Fin n) (eM : M ≃ Fin n) :
    KE (Encodable.encode (worldTable U eC))
      ≤ KE (Encodable.encode (frameTable U ℓ 0 eC eM))
        + KE (Encodable.encode (frameTable U ℓ 1 eC eM)) + (elen icode + 6) := by
  set a := Encodable.encode (frameTable U ℓ 0 eC eM) with ha
  set b := Encodable.encode (frameTable U ℓ 1 eC eM) with hb
  -- a shortest program for the pair of frames, extended by the fixed inverter
  obtain ⟨d, hd, hdlen⟩ := exists_min_E (Nat.pair a b)
  have hcomp : Computes (comp icode d) (Encodable.encode (worldTable U eC)) := by
    change eval (comp icode d) 0 = _
    rw [eval_comp_some hd, eval_icode, invcomp_frameTables h hmax eC eM]
  have hle := KE_comp_le hcomp
  have hsub := KE_subadditive a b
  omega

end PersistenceCapacity
