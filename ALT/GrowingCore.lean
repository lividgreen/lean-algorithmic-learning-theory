/-
Copyright (c) 2026 Mykola Palamarchuk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mykola Palamarchuk
-/
import ALT.GrowingWorld
import ALT.AccretingWitness
import ALT.PersistenceCapacity

-- Formal-check file, not Mathlib-destined: opt out of the house-style header linter.
set_option linter.style.header false

/-!
# The growing core: the merge quotient as the canonical conservation guest
([Guests] §6 Theorem 6.1 and §7 Theorem 7.7)

`GrowingWorld.lean` states the staged square a guest of a growing host must close; this file
manufactures one from the host alone. For `U : X → X`, two states **eventually merge** when some
finite iterate identifies them (`Merges`), and the quotient by that relation carries an induced law
that is automatically injective — a **conservation guest** built with no hypothesis at all, from
`U` alone, at every stage family.

Every conservation guest (one whose law is injective) factors through this quotient: any
merge-invariant staged reading is forced by the square's own iterates
(`merges_invariant_of_stagedSquare`), so the merge quotient's retained profile is the exact ceiling
on every conservation guest's extent.
At a finite, constant-stage host, the quotient coincides with `PersistenceCapacity.core`: distinct
core states never merge (the core is where `U` restricts to a bijection), and every state merges
with the core state its transient reaches (`mergeQuotCoreEquiv`), recovering the finite theorem's
"the core is big" as "the retained profile is big."

Robustness is merging by construction: `AccretingWitness.accErasure`'s one-step erasure is exactly a
one-step merge, so the accreting healer world's quotient is invariant under its own healing margin,
and `AccretingWitness.accLaw`'s injectivity (append one bit) makes it the theorem's first concrete
consumer — the landed decode reading factors through the merge quotient at every stage.

## Main results

* `Merges` / `mergesSetoid` / `MergeQuot` — **the manufacture**: eventual merging is an equivalence
  (`merges_refl` / `merges_symm` / `merges_trans`), and its quotient is the canonical carrier.
* `mergeLaw` / `mergeLaw_injective` / `stagedSquare_merge` — the induced law is well-defined,
  injective with no hypothesis, and closes the staged square identically at every stage family.
* `merges_invariant_of_stagedSquare` — **universality**: any injective-law staged-square reading is
  merge-invariant per stage, so it factors through the quotient (`exists_mergeMk_injective`).
* `mergeStage` / `advances_mergeStage` / `mergeStage_injOn` — **the retained profile** `R_t`: the
  quotient's own guest stage, advancing under `Advances` and injected stage-to-stage by `mergeLaw`.
* `mergeQuotCoreEquiv` / `nat_card_mergeQuot_eq_core` — **the finite bridge**: at a finite carrier
  the merge quotient is in bijection with `PersistenceCapacity.core`, matching class counts exactly.
* `mergeRead_eq_of_merges` / `accMerges_of_accErasure` — **robustness is merging**: a healed
  perturbation is, by definition of the quotient, invisible to the merge reading.
* `accLaw_injective` / `accRead_merges_invariant` — the accreting healer world's landed decode
  reading is merge-invariant at every stage — universality's first concrete consumer.

## Scope

No pricing and no ownership claim: an affordable canonical-representative selector stays a named
hypothesis at paper level, exactly as the note's own accounting records. The crossing grade (a fixed
Gödel sentence, threaded through an arbitrary monotone unbounded budget profile rather than the
witness's own `t + 1`) is a separate module, `GrowingCoreCrossing.lean`: it consumes only
`CategoricalThreshold`/`AccretingWitness.outgrows_paMinus_uniform` and needs nothing from the merge
quotient built here.
-/

namespace GrowingCore

open Decoupling PersistenceCapacity AccretingWitness

variable {X M : Type*}

/-! ## The manufacture: eventual merging and its quotient -/

/-- **Eventual merging**: two states whose orbits are eventually identified by some common number of
steps. An equivalence relation (`merges_refl` / `merges_symm` / `merges_trans`), and the object the
whole file is built on: it needs nothing beyond `U` itself, no reading and no law. -/
def Merges (U : X → X) (s s' : X) : Prop := ∃ k, U^[k] s = U^[k] s'

/-- If two iterates agree at some exponent, they agree at every larger exponent — the monotonicity
that makes `Merges` transitive and that peels an injective law's iterate back to its base case. -/
private theorem merges_of_iterate_eq_ge {U : X → X} {s s' : X} {k m : ℕ}
    (h : U^[k] s = U^[k] s') (hm : k ≤ m) : U^[m] s = U^[m] s' := by
  have e : m - k + k = m := Nat.sub_add_cancel hm
  calc U^[m] s = U^[m - k] (U^[k] s) := by rw [← Function.iterate_add_apply, e]
    _ = U^[m - k] (U^[k] s') := by rw [h]
    _ = U^[m] s' := by rw [← Function.iterate_add_apply, e]

theorem merges_refl (U : X → X) (s : X) : Merges U s s := ⟨0, rfl⟩

theorem merges_symm {U : X → X} {s s' : X} (h : Merges U s s') : Merges U s' s :=
  ⟨h.choose, h.choose_spec.symm⟩

theorem merges_trans {U : X → X} {s s' s'' : X} (h1 : Merges U s s') (h2 : Merges U s' s'') :
    Merges U s s'' := by
  obtain ⟨k, hk⟩ := h1
  obtain ⟨k', hk'⟩ := h2
  exact ⟨max k k', by
    rw [merges_of_iterate_eq_ge hk (le_max_left k k'),
      merges_of_iterate_eq_ge hk' (le_max_right k k')]⟩

/-- The setoid of eventual merging, over an arbitrary update `U`. -/
def mergesSetoid (U : X → X) : Setoid X where
  r := Merges U
  iseqv := ⟨merges_refl U, merges_symm, merges_trans⟩

/-- The quotient by eventual merging — the canonical carrier every conservation guest factors
through (`exists_mergeMk_injective`). Reducible: kept transparent so tactics see through it to the
underlying `Quotient` the way they see through any other type synonym in this development. -/
abbrev MergeQuot (U : X → X) : Type _ := Quotient (mergesSetoid U)

/-- The quotient map, spelled out so call sites need not spell the setoid. Reducible, for the same
reason as `MergeQuot`. -/
abbrev mergeMk (U : X → X) (s : X) : MergeQuot U := Quotient.mk (mergesSetoid U) s

/-- `U` respects eventual merging: stepping both sides by `U` preserves any common iterate one step
later. What makes `mergeLaw` well-defined. -/
private theorem mergeRespects (U : X → X) :
    ∀ ⦃s s' : X⦄, Merges U s s' → Merges U (U s) (U s') := by
  rintro s s' ⟨k, hk⟩
  refine ⟨k, ?_⟩
  calc U^[k] (U s) = U^[k + 1] s := (Function.iterate_succ_apply U k s).symm
    _ = U (U^[k] s) := Function.iterate_succ_apply' U k s
    _ = U (U^[k] s') := congrArg U hk
    _ = U^[k + 1] s' := (Function.iterate_succ_apply' U k s').symm
    _ = U^[k] (U s') := Function.iterate_succ_apply U k s'

/-- The converse step: if the `U`-images merge, so did the states themselves — one more step of
iterate bookkeeping. What makes `mergeLaw` injective. -/
private theorem merges_of_merges_apply {U : X → X} {s s' : X} (h : Merges U (U s) (U s')) :
    Merges U s s' := by
  obtain ⟨k, hk⟩ := h
  refine ⟨k + 1, ?_⟩
  calc U^[k + 1] s = U^[k] (U s) := Function.iterate_succ_apply U k s
    _ = U^[k] (U s') := hk
    _ = U^[k + 1] s' := (Function.iterate_succ_apply U k s').symm

/-- **The induced law, well-defined with no hypothesis**: `mergeLaw U ⟦s⟧ = ⟦U s⟧`. -/
def mergeLaw (U : X → X) : MergeQuot U → MergeQuot U := Quotient.map U (mergeRespects U)

@[simp] theorem mergeLaw_mergeMk (U : X → X) (s : X) : mergeLaw U (mergeMk U s) = mergeMk U (U s) :=
  Quotient.map_mk U (mergeRespects U) s

/-- **The induced law is injective, with no hypothesis at all**: this is the whole reason eventual
merging manufactures a conservation guest rather than merely a guest. -/
theorem mergeLaw_injective (U : X → X) : Function.Injective (mergeLaw U) := by
  intro x y
  induction x using Quotient.inductionOn with
  | _ s => induction y using Quotient.inductionOn with
    | _ s' =>
      intro hxy
      rw [mergeLaw_mergeMk, mergeLaw_mergeMk] at hxy
      exact Quotient.sound (merges_of_merges_apply (Quotient.exact hxy))

/-- **The staged square, at every stage family, with no hypothesis**: the quotient map is a
time-independent reading that closes the square against `mergeLaw` identically — this is the
manufacture, [Guests] §7 Theorem 7.7(i). -/
theorem stagedSquare_merge (U : X → X) (Ω : ℕ → Set X) :
    GrowingWorld.StagedSquare U (mergeLaw U) (fun _ s => mergeMk U s) Ω := by
  intro _t s _
  exact (mergeLaw_mergeMk U s).symm

/-! ## Universality: every conservation guest factors through the quotient -/

/-- The host's forward orbit stays in its stages: `k` steps from a stage-`t` state lands in stage
`t + k`. Repeated `Advances`. -/
private theorem mem_stage_of_advances {U : X → X} {Ω : ℕ → Set X} (hadv : GrowingWorld.Advances U Ω)
    {t : ℕ} {s : X} (hs : s ∈ Ω t) : ∀ k, U^[k] s ∈ Ω (t + k) := by
  intro k
  induction k with
  | zero => simpa using hs
  | succ k ih =>
    have h := hadv (t + k) (U^[k] s) ih
    rw [Function.iterate_succ_apply']
    exact h

/-- The iterated square: `k` host steps, read `k` stages later, is `k` law steps applied to the
current reading. Needs `Advances` to keep the intermediate points in their stages. -/
private theorem iterate_stagedSquare {U : X → X} {F : M → M} {ℓ : ℕ → X → M} {Ω : ℕ → Set X}
    (hadv : GrowingWorld.Advances U Ω) (hsq : GrowingWorld.StagedSquare U F ℓ Ω)
    {t : ℕ} {s : X} (hs : s ∈ Ω t) :
    ∀ k, ℓ (t + k) (U^[k] s) = F^[k] (ℓ t s) := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    have hmem : U^[k] s ∈ Ω (t + k) := mem_stage_of_advances hadv hs k
    have hstep := hsq (t + k) (U^[k] s) hmem
    have hidx : t + (k + 1) = t + k + 1 := rfl
    calc ℓ (t + (k + 1)) (U^[k + 1] s)
        = ℓ (t + k + 1) (U (U^[k] s)) := by rw [hidx, Function.iterate_succ_apply']
      _ = F (ℓ (t + k) (U^[k] s)) := hstep
      _ = F (F^[k] (ℓ t s)) := by rw [ih]
      _ = F^[k + 1] (ℓ t s) := (Function.iterate_succ_apply' F k (ℓ t s)).symm

/-- **Universality** ([Guests] §7 Theorem 7.7(ii)): any staged-square reading with an INJECTIVE law
is merge-invariant per stage — two states admitted at the same stage that eventually merge are read
identically. So every conservation guest factors through the merge quotient. -/
theorem merges_invariant_of_stagedSquare {U : X → X} {F : M → M} {ℓ : ℕ → X → M} {Ω : ℕ → Set X}
    (hF : Function.Injective F) (hadv : GrowingWorld.Advances U Ω)
    (hsq : GrowingWorld.StagedSquare U F ℓ Ω) :
    ∀ t, ∀ s ∈ Ω t, ∀ s' ∈ Ω t, Merges U s s' → ℓ t s = ℓ t s' := by
  rintro t s hs s' hs' ⟨k, hk⟩
  have h1 := iterate_stagedSquare hadv hsq hs k
  have h2 := iterate_stagedSquare hadv hsq hs' k
  rw [hk, h2] at h1
  exact hF.iterate k h1.symm

/-- **The stage-`t` extent of any conservation guest injects into the merge classes over `Ω t`**
([Guests] §7 Theorem 7.7(ii)): the merge quotient is the maximal conservation guest, so its retained
profile ceilings every other one's. -/
theorem exists_mergeMk_injective {U : X → X} {F : M → M} {ℓ : ℕ → X → M} {Ω : ℕ → Set X}
    (hF : Function.Injective F) (hadv : GrowingWorld.Advances U Ω)
    (hsq : GrowingWorld.StagedSquare U F ℓ Ω) (t : ℕ) :
    ∃ g : ↥(GrowingWorld.guestStage ℓ Ω t) → MergeQuot U,
      (∀ m, g m ∈ GrowingWorld.guestStage (fun _ s => mergeMk U s) Ω t) ∧ Function.Injective g := by
  classical
  choose s hsmem hseq using fun m : ↥(GrowingWorld.guestStage ℓ Ω t) => m.2
  refine ⟨fun m => mergeMk U (s m), fun m => ⟨s m, hsmem m, rfl⟩, ?_⟩
  intro m m' hmm'
  have hmerges : Merges U (s m) (s m') := Quotient.exact hmm'
  have heq := merges_invariant_of_stagedSquare hF hadv hsq t (s m) (hsmem m) (s m') (hsmem m')
    hmerges
  exact Subtype.ext (by rw [← hseq m, ← hseq m', heq])

/-! ## The retained profile -/

/-- **The retained profile `R_t`** ([Guests] §7 Definition 7.6): the merge quotient's own guest
stage — the classes represented among the states `Ω` admits at stage `t`. Reuses
`GrowingWorld.guestStage` directly; no new machinery. -/
def mergeStage (U : X → X) (Ω : ℕ → Set X) (t : ℕ) : Set (MergeQuot U) :=
  GrowingWorld.guestStage (fun _ s => mergeMk U s) Ω t

/-- **The stage-to-stage injection**: `mergeLaw` carries the stage-`t` retained classes into the
stage-`(t + 1)` ones, since the quotient is itself a guest of `(U, Ω)` (`stagedSquare_merge`) and
factor closure (`GrowingWorld.advances_guestStage`) applies with no further hypothesis. -/
theorem advances_mergeStage {U : X → X} {Ω : ℕ → Set X} (hadv : GrowingWorld.Advances U Ω) :
    GrowingWorld.Advances (mergeLaw U) (mergeStage U Ω) :=
  GrowingWorld.advances_guestStage hadv (stagedSquare_merge U Ω)

/-- The stage-to-stage map is injective — `mergeLaw` never collapses distinct classes, at any
stage. -/
theorem mergeStage_injOn (U : X → X) (Ω : ℕ → Set X) (t : ℕ) :
    Set.InjOn (mergeLaw U) (mergeStage U Ω t) :=
  (mergeLaw_injective U).injOn

/-! ## The finite bridge -/

/-- A bijection of a set iterates to a bijection of that set (re-derived: `PersistenceCapacity.lean`
keeps its own copy private, and the fact is five lines). -/
private theorem bijOn_iterate {U : X → X} {s : Set X} (h : Set.BijOn U s s) (n : ℕ) :
    Set.BijOn (U^[n]) s s := by
  induction n with
  | zero => simpa using Set.bijOn_id s
  | succ k ih => rw [Function.iterate_succ]; exact ih.comp h

/-- Two merged states already agree at the transient bound `Nat.card X`: extend the witnessing
exponent up to `max k (Nat.card X)`, then use that `U^[j]` is injective on the core
(from `core_bijOn`) to bring the two core-landed points, `j` steps apart from that bound, back
together. -/
private theorem coreOf_welldef {U : X → X} [Finite X] {s s' : X} (h : Merges U s s') :
    U^[Nat.card X] s = U^[Nat.card X] s' := by
  obtain ⟨k, hk⟩ := h
  set N := Nat.card X with hNdef
  set M := max k N with hMdef
  have hM : U^[M] s = U^[M] s' := merges_of_iterate_eq_ge hk (le_max_left k N)
  have hjN : (M - N) + N = M := Nat.sub_add_cancel (le_max_right k N)
  have ha : U^[N] s ∈ core U := iterate_mem_core U le_rfl s
  have ha' : U^[N] s' ∈ core U := iterate_mem_core U le_rfl s'
  have e1 : U^[M] s = U^[M - N] (U^[N] s) := by
    conv_lhs => rw [← hjN]
    rw [Function.iterate_add_apply]
  have e2 : U^[M] s' = U^[M - N] (U^[N] s') := by
    conv_lhs => rw [← hjN]
    rw [Function.iterate_add_apply]
  have hinj : Set.InjOn (U^[M - N]) (core U) := (bijOn_iterate (core_bijOn U) (M - N)).injOn
  exact hinj ha ha' (by rw [← e1, ← e2, hM])

/-- **The finite bridge, as a genuine map into the core** ([Guests] §7 Theorem 7.7(iv)): every merge
class is read off at the transient bound, landing in `PersistenceCapacity.core`. -/
noncomputable def coreOf (U : X → X) [Finite X] : MergeQuot U → ↥(core U) :=
  Quotient.lift (fun s => (⟨U^[Nat.card X] s, iterate_mem_core U le_rfl s⟩ : ↥(core U)))
    (fun _ _ hab => Subtype.ext (coreOf_welldef hab))

private theorem coreOf_injective (U : X → X) [Finite X] : Function.Injective (coreOf U) := by
  intro x y
  induction x using Quotient.inductionOn with
  | _ s => induction y using Quotient.inductionOn with
    | _ s' =>
      intro hxy
      exact Quotient.sound ⟨Nat.card X, congrArg Subtype.val hxy⟩

private theorem coreOf_surjective (U : X → X) [Finite X] : Function.Surjective (coreOf U) := by
  rintro ⟨c, hc⟩
  obtain ⟨s, hs, hsc⟩ := (bijOn_iterate (core_bijOn U) (Nat.card X)).surjOn hc
  exact ⟨mergeMk U s, Subtype.ext hsc⟩

/-- **The finite bridge**: at a finite carrier the merge quotient is in bijection with the recurrent
core — distinct core states never merge (`coreOf_injective`, via injectivity on the core) and every
state merges with the core state its transient reaches (`coreOf_surjective`, via surjectivity on the
core). Generalizes the finite theorem's "the core is big" verbatim to "the retained profile is
big." -/
noncomputable def mergeQuotCoreEquiv (U : X → X) [Finite X] : MergeQuot U ≃ ↥(core U) :=
  Equiv.ofBijective (coreOf U) ⟨coreOf_injective U, coreOf_surjective U⟩

/-- The class-count equality the finite bridge exists for. -/
theorem nat_card_mergeQuot_eq_core (U : X → X) [Finite X] :
    Nat.card (MergeQuot U) = Nat.card ↥(core U) :=
  Nat.card_congr (mergeQuotCoreEquiv U)

/-! ## Robustness is merging -/

/-- **Robustness is merging, by construction** ([Guests] §7 Theorem 7.7(v)): stated anyway, since it
is the certificate's robustness clause in the exact form consumers cite. -/
theorem mergeRead_eq_of_merges {U : X → X} {s s' : X} (h : Merges U s s') :
    mergeMk U s = mergeMk U s' := Quotient.sound h

variable {ι_J : Type*}

/-- **The witness instantiation**: `AccretingWitness.accErasure`'s one-step erasure is, verbatim, a
one-step merge — a total-weight-bounded habitat perturbation with agreeing environment merges with
the unperturbed state in one step, so the quotient reading is invariant under exactly the witness's
margin. -/
theorem accMerges_of_accErasure (k : ℕ) (π : Mem ι_J Bool → Mem ι_J Bool) (t : ℕ)
    {s : List (Mem (Fin (3 ^ k)) Bool) × Mem ι_J Bool} (hs : s ∈ accCode k t)
    {s' : List (Mem (Fin (3 ^ k)) Bool) × Mem ι_J Bool} (hlen : s'.1.length = s.1.length)
    (henv : s'.2 = s.2) (hsum : (List.zipWith hammingDist s'.1 s.1).sum < 2 ^ k) :
    Merges (accUpdate k π) s' s :=
  ⟨1, by simpa using accErasure k π t hs hlen henv hsum⟩

/-- `accLaw` appends one fixed bit, so it is injective — checked at its declaration rather than
assumed. -/
theorem accLaw_injective : Function.Injective accLaw := List.append_left_injective [false]

/-- **The landed decode reading factors through the merge quotient** ([Guests] §7 Theorem 7.7(v)):
universality's first concrete consumer, `accLaw` being injective. Two states admitted at the same
stage that eventually merge under the accreting update decode identically. -/
theorem accRead_merges_invariant (k : ℕ) (π : Mem ι_J Bool → Mem ι_J Bool) :
    ∀ t, ∀ s ∈ accStage k t, ∀ s' ∈ accStage k t,
      Merges (accUpdate k π) s s' → accRead k t s = accRead k t s' :=
  merges_invariant_of_stagedSquare accLaw_injective (advances_accUpdate k π)
    (stagedSquare_accRead k π)

end GrowingCore
