module

public import Batteries.Tactic.OpenPrivate
public import Nonautonomous.MergeQuotient
public import ALT.GrowingWorld
public import ALT.AccretingWitness
public import ALT.PersistenceCapacity
import all Nonautonomous.MergeQuotient

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
(`Semiconj.merges_invariant`), so the merge quotient's retained profile is the exact
ceiling on every conservation guest's extent.
At a finite, constant-stage host, the quotient coincides with `ALT.core`: distinct
core states never merge (the core is where `U` restricts to a bijection), and every state merges
with the core state its transient reaches (`mergeQuotCoreEquiv`), recovering the finite theorem's
"the core is big" as "the retained profile is big."

Robustness is merging by construction: `ALT.accUpdate_eq_of_sum_lt`'s one-step erasure is exactly a
one-step merge, so the accreting healer world's quotient is invariant under its own healing margin,
and `ALT.accLaw`'s injectivity (append one bit) makes it the theorem's first concrete
consumer — the landed decode reading factors through the merge quotient at every stage.

## Main results

* `Merges` / `mergesSetoid` / `MergeQuot` — **the manufacture**: eventual merging is an equivalence
  (`Merges.refl` / `Merges.symm` / `Merges.trans`), and its quotient is the canonical carrier.
* `mergeLaw` / `mergeLaw_injective` / `semiconj_merge` — the induced law is
  well-defined, injective with no hypothesis, and closes the staged square identically at every
  stage family.
* `mergeMk_injective_of_injective` — at an injective `U`, `mergeMk U` is itself injective: no two
  distinct states ever merge, since an injective law's iterates cancel the witnessing equation
  outright.
* `Semiconj.merges_invariant` — **universality**: any injective-law staged-square
  reading is merge-invariant per stage, so it factors through the quotient
  (`exists_mergeMk_injective`).
* `mergeFiber` / `positivelyInvariant_mergeFiber` / `mergeFiber_injOn` — **the retained profile**
  `R_t`: the quotient's own guest stage, advancing under `PositivelyInvariant` and injected
  stage-to-stage by `mergeLaw`.
* `mergeQuotCoreEquiv` / `nat_card_mergeQuot_eq_core` — **the finite bridge**: at a finite carrier
  the merge quotient is in bijection with `ALT.core`, matching class counts exactly.
* `mergeRead_eq_of_merges` / `accMerges_of_accUpdate_eq_of_sum_lt` — **robustness is merging**: a
  healed perturbation is, by definition of the quotient, invisible to the merge reading.
* `accLaw_injective` / `accRead_merges_invariant` — the accreting healer world's landed decode
  reading is merge-invariant at every stage — universality's first concrete consumer.

## Scope

No pricing and no ownership claim: an affordable canonical-representative selector stays a named
hypothesis at paper level, exactly as the note's own accounting records. The crossing grade (a fixed
Gödel sentence, threaded through an arbitrary monotone unbounded budget profile rather than the
witness's own `t + 1`) is a separate module, `GrowingCoreCrossing.lean`: it consumes only
`CategoricalThreshold`/`ALT.outgrows_paMinus_uniform` and needs nothing from the merge
quotient built here.
-/


@[expose] public section

open private merges_of_iterate_eq_ge from Nonautonomous.MergeQuotient

namespace ALT

open Nonautonomous

variable {X M : Type*}

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
theorem coreOf_welldef {U : X → X} [Finite X] {s s' : X} (h : Merges U s s') :
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
class is read off at the transient bound, landing in `ALT.core`. -/
noncomputable def coreOf (U : X → X) [Finite X] : MergeQuot U → ↥(core U) :=
  Quotient.lift (fun s => (⟨U^[Nat.card X] s, iterate_mem_core U le_rfl s⟩ : ↥(core U)))
    (fun _ _ hab => Subtype.ext (coreOf_welldef hab))

/-- `coreOf U` is injective. -/
theorem coreOf_injective (U : X → X) [Finite X] : Function.Injective (coreOf U) := by
  intro x y
  induction x using Quotient.inductionOn with
  | _ s => induction y using Quotient.inductionOn with
    | _ s' =>
      intro hxy
      exact Quotient.sound ⟨Nat.card X, congrArg Subtype.val hxy⟩

/-- `coreOf U` is surjective. -/
theorem coreOf_surjective (U : X → X) [Finite X] : Function.Surjective (coreOf U) := by
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

/-- **The witness instantiation**: `ALT.accUpdate_eq_of_sum_lt`'s one-step erasure is, verbatim, a
one-step merge — a total-weight-bounded habitat perturbation with agreeing environment merges with
the unperturbed state in one step, so the quotient reading is invariant under exactly the witness's
margin. -/
theorem accMerges_of_accUpdate_eq_of_sum_lt (k : ℕ) (π : Mem ι_J Bool → Mem ι_J Bool) (t : ℕ)
    {s : List (Mem (Fin (3 ^ k)) Bool) × Mem ι_J Bool} (hs : s ∈ accCode k t)
    {s' : List (Mem (Fin (3 ^ k)) Bool) × Mem ι_J Bool} (hlen : s'.1.length = s.1.length)
    (henv : s'.2 = s.2) (hsum : (List.zipWith hammingDist s'.1 s.1).sum < 2 ^ k) :
    Merges (accUpdate k π) s' s :=
  ⟨1, by simpa using accUpdate_eq_of_sum_lt k π t hs hlen henv hsum⟩

/-- `accLaw` appends one fixed bit, so it is injective — checked at its declaration rather than
assumed. -/
theorem accLaw_injective : Function.Injective accLaw := List.append_left_injective [false]

/-- **The landed decode reading factors through the merge quotient** ([Guests] §7 Theorem 7.7(v)):
universality's first concrete consumer, `accLaw` being injective. Two states admitted at the same
stage that eventually merge under the accreting update decode identically. -/
theorem accRead_merges_invariant (k : ℕ) (π : Mem ι_J Bool → Mem ι_J Bool) :
    ∀ t, ∀ s ∈ accStage k t, ∀ s' ∈ accStage k t,
      Merges (accUpdate k π) s s' → accRead k t s = accRead k t s' :=
  Semiconj.merges_invariant accLaw_injective (advances_accUpdate k π)
    (stagedSquare_accRead k π)

end ALT
