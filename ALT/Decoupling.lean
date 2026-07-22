/-
Copyright (c) 2026 Mykola Palamarchuk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mykola Palamarchuk
-/
import Mathlib

-- Formal-check file, not Mathlib-destined: opt out of the house-style header linter.
set_option linter.style.header false

/-!
# The Decoupling Lemma: structural core + necessity ([Decoupling] §3 Lemma 3.1)

Provenance: [Decoupling], §3 (Lemma 3.1, the Decoupling Lemma: D1
persistence — a faithfully-encoded model survives multi-step iteration iff its code region is
read-only under the update).

Modeling. A subsystem is ONE shared memory `Mem ι V := ι → V` with ONE update `U : Mem → Mem`.
"Code vs work" is EARNED, not assumed: which cells `U` writes is what distinguishes them. A model is
read out by `decode : Mem → M` over a region `R` (the candidate code region). The result —
decoupling (`U` read-only on `R`) ⟺ a faithfully-encoded model survives all `k` iterations — so
decoupling is DERIVED in both directions, not posited. This captures "applying the model on shared
degrees of freedom overwrites it unless the code cells are read-only".

Status: PROVED as the information-theoretic core (pure shared-memory algebra), both directions.

## What this DOES establish
* `fixes_iterate` / `model_persists`: SUFFICIENCY (D1) — cells `U` never writes stay fixed across
  all `k` iterations, so a model read from a read-only region persists.
* `model_destroyed_by_write`: the concrete no-go — writing the read-out cell changes the model in
  one step.
* `fixes_of_persists`: NECESSITY — if a FAITHFUL model is preserved by `U` on every state, then `U`
  must be read-only on `R`; decoupling is FORCED.
* `decoupling_iff_persists_all`: THE EQUIVALENCE (Lemma 3.1 core, multi-step) — for a
  faithfully-encoded model, decoupling holds IFF the model persists across all `k` prediction steps.

## What this does NOT establish (flagged)
* Formalizes the D1 structural core + necessity on a SHARED-MEMORY model only. QUARANTINED (NOT
  here): D3 (thermal stability `ΔE ≫ kT`) and D4 (maintenance flux / Landauer) — physical premises;
  and the statistical step "predictive efficiency `η > η_chance` ⇒ a fixed model is being iterated"
  — the core starts from "there IS a faithfully-encoded model".
* `Faithful` models "the model is exactly the code-region cells". Necessity holds for faithful
  (genuinely `R`-encoding) models; a degenerate/constant model needs no decoupling (correctly). NO
  capacity / Kolmogorov-nontriviality is modeled (the model may be small); D2 work-dynamics beyond
  "cells outside `R` are unconstrained" is not developed.
* Abstract cells / values; no physical substrate; NO claim any physical system decouples (Layer-2).
  This discharges the structural skeleton of Lemma 3.1 (a bare premise everywhere until now), not
  the full lemma.

## Hypotheses: paper-stated vs added
* Paper-stated / faithful: Lemma 3.1's D1 persistence ⟺ read-only code region; faithfulness =
  "there is a real (`R`-encoding) model".
* Added / modeling: the single shared memory `ι → V`, single update `U`, region `R`, and `decode`;
  "code vs work" earned by `Fixes U R`.
-/

namespace Decoupling

variable {ι V M : Type*}

/-- A subsystem's memory: a single shared field of cells `ι` holding values `V`. -/
abbrev Mem (ι V : Type*) := ι → V

/-- `U` is read-only on region `R`: it never writes cells in `R` (the candidate code region). -/
def Fixes (U : Mem ι V → Mem ι V) (R : Set ι) : Prop := ∀ s, ∀ a ∈ R, U s a = s a

/-- `decode` depends only on region `R` (the model is read from `R`). -/
def DependsOn (decode : Mem ι V → M) (R : Set ι) : Prop :=
  ∀ s t, (∀ a ∈ R, s a = t a) → decode s = decode t

/-- `decode` *faithfully encodes* `R`: equal decode ⟺ agreement on `R` (it both depends only on `R`
and separates every `R`-difference). Models "the model is exactly the code-region cells". -/
def Faithful (decode : Mem ι V → M) (R : Set ι) : Prop :=
  ∀ s t, decode s = decode t ↔ (∀ a ∈ R, s a = t a)

/-- A faithful model depends only on its region. -/
theorem Faithful.dependsOn {decode : Mem ι V → M} {R} (hf : Faithful decode R) :
    DependsOn decode R := fun s t h => (hf s t).mpr h

/-- D1 mechanism: cells the update never writes stay fixed across ALL `k` iterations. -/
theorem fixes_iterate {U : Mem ι V → Mem ι V} {R} (h : Fixes U R) :
    ∀ k s, ∀ a ∈ R, (U^[k] s) a = s a := by
  intro k; induction k with
  | zero => intro s a _; rfl
  | succ k ih => intro s a ha; rw [Function.iterate_succ_apply', h _ a ha]; exact ih s a ha

/-- Sufficiency (D1): a model read from a read-only region survives every iteration. -/
theorem model_persists {U} {R} {decode : Mem ι V → M}
    (hU : Fixes U R) (hd : DependsOn decode R) :
    ∀ k s, decode (U^[k] s) = decode s :=
  fun k s => hd _ _ (fun a ha => fixes_iterate hU k s a ha)

/-- The concrete no-go ("applying destroys it"): if the update writes the cell the model is read
from, one application changes the model. -/
theorem model_destroyed_by_write {U : Mem ι V → Mem ι V} (s : Mem ι V) (a : ι)
    (h : U s a ≠ s a) : (fun m : Mem ι V => m a) (U s) ≠ (fun m => m a) s := h

/-- NECESSITY (the deeper direction): if a *faithful* model is preserved by `U` on every state, then
`U` must be read-only on `R` — decoupling is FORCED. (A degenerate model needs no decoupling;
faithfulness is exactly "there is a real model".) -/
theorem fixes_of_persists {U} {R} {decode : Mem ι V → M}
    (hf : Faithful decode R) (hpers : ∀ s, decode (U s) = decode s) : Fixes U R := by
  intro s a ha; exact (hf (U s) s).mp (hpers s) a ha

/-- THE EQUIVALENCE (Lemma 3.1 core, multi-step): for a faithfully-encoded model, decoupling
(read-only code region) holds IFF the model persists across all `k` prediction steps. -/
theorem decoupling_iff_persists_all {U} {R} {decode : Mem ι V → M} (hf : Faithful decode R) :
    Fixes U R ↔ ∀ k s, decode (U^[k] s) = decode s := by
  constructor
  · intro hU k s; exact model_persists hU hf.dependsOn k s
  · intro hall
    exact fixes_of_persists hf (fun s => by have := hall 1 s; rwa [Function.iterate_one] at this)

/-- [Decoupling] §3, Corollary 3.2 (Total-Overwrite Exclusion): if the update rewrites every cell
somewhere (no cell is read-only under `U`), then no faithful model on a non-empty region persists
across iterations. The packaged contrapositive of `fixes_of_persists`: persistence would force `U`
read-only on `R`, but with `R` non-empty that contradicts total overwrite at any `a ∈ R`. -/
theorem total_overwrite_exclusion {U : Mem ι V → Mem ι V}
    (hall : ∀ a : ι, ∃ s, U s a ≠ s a)
    {decode : Mem ι V → M} {R : Set ι}
    (hne : R.Nonempty) (hf : Faithful decode R) :
    ¬ ∀ k s, decode (U^[k] s) = decode s := by
  intro hpers
  have hfix : Fixes U R :=
    fixes_of_persists hf (fun s => by have := hpers 1 s; rwa [Function.iterate_one] at this)
  obtain ⟨a, ha⟩ := hne
  obtain ⟨s, hs⟩ := hall a
  exact hs (hfix s a ha)

/-- **The faithfulness (injectivity) hypothesis is load-bearing for necessity.** The necessity
direction (`fixes_of_persists`) needs the full `Faithful` biconditional, *not* merely `DependsOn`
(the model depends only on `R`). This exhibits a lossy decoder where `DependsOn` and persistence
both hold yet `U` rewrites a cell of `R` — so without faithfulness, persistence does **not** force
a read-only code region. Witness: two Boolean cells, a decoder reading only cell `false` (so cell
`true ∈ R` is redundant), and the update that flips cell `true`. The model persists (it never reads
the flipped cell) while `R` is rewritten. This is the "no redundancy in the code encoding" content
of Definition 2.1(D2): a code region with cells the decoder ignores breaks necessity. -/
theorem necessity_needs_faithful :
    ∃ (ι V M : Type) (decode : Mem ι V → M) (U : Mem ι V → Mem ι V) (R : Set ι),
      DependsOn decode R ∧ (∀ s, decode (U s) = decode s) ∧ ¬ Fixes U R := by
  refine ⟨Bool, Bool, Bool, fun s => s false,
    fun s a => if a then !(s a) else s a, Set.univ, ?_, ?_, ?_⟩
  · intro s t h; exact h false (Set.mem_univ false)
  · intro s; simp
  · intro hfix
    have h := hfix (fun _ => false) true (Set.mem_univ true)
    simp at h

/-! ### The decoupling dichotomy ([Decoupling] §3, Corollary 3.3)

The maximality statement, in two halves and packaged. Persistence of a *faithful* model forces a
read-only cell (`exists_fixed_cell_of_persists` / `subset_fixed_of_persists`, the ⇒ direction), and
conversely a single read-only cell already supports a faithful, non-constant, persisting model
(`persists_of_fixed_cell`, the ⇐ direction). Over the value type these combine into the
biconditional `decoupling_dichotomy`. -/

/-- [Decoupling] §3, Corollary 3.3 (⇒, maximality). If a faithful model on a non-empty region
persists across every iteration, then the update has a genuinely read-only cell: some `a` fixed
by `U` on every state. One step off `fixes_of_persists` (persistence read at `k = 1`). -/
theorem exists_fixed_cell_of_persists {U : Mem ι V → Mem ι V} {R : Set ι} {decode : Mem ι V → M}
    (hne : R.Nonempty) (hf : Faithful decode R)
    (hpers : ∀ k s, decode (U^[k] s) = decode s) :
    ∃ a, ∀ s, U s a = s a := by
  have hfix : Fixes U R :=
    fixes_of_persists hf (fun s => by have := hpers 1 s; rwa [Function.iterate_one] at this)
  obtain ⟨a, ha⟩ := hne
  exact ⟨a, fun s => hfix s a ha⟩

/-- [Decoupling] §3, Corollary 3.3 (⇒, set form). The whole code region is read-only: every cell
of `R` is fixed by `U` on every state. Same content as `exists_fixed_cell_of_persists`, which
additionally
uses `R` non-empty to name one witness. -/
theorem subset_fixed_of_persists {U : Mem ι V → Mem ι V} {R : Set ι} {decode : Mem ι V → M}
    (hf : Faithful decode R) (hpers : ∀ k s, decode (U^[k] s) = decode s) :
    R ⊆ {a | ∀ s, U s a = s a} := by
  have hfix : Fixes U R :=
    fixes_of_persists hf (fun s => by have := hpers 1 s; rwa [Function.iterate_one] at this)
  exact fun a ha s => hfix s a ha

/-- [Decoupling] §3, Corollary 3.3 (⇐, witness). A single read-only cell already carries a faithful,
non-constant model that persists across every iteration. Witness: the singleton region `{a₀}` with
the one-cell decoder `s ↦ s a₀` — faithfulness is definitional, non-constancy comes from two
constant states at distinct values (`Nontrivial V`), and persistence is `model_persists`. -/
theorem persists_of_fixed_cell [Nontrivial V] {U : Mem ι V → Mem ι V} (a₀ : ι)
    (h : ∀ s, U s a₀ = s a₀) :
    ∃ (R : Set ι) (decode : Mem ι V → V), R.Nonempty ∧ Faithful decode R ∧
      (∃ s t, decode s ≠ decode t) ∧ ∀ k s, decode (U^[k] s) = decode s := by
  refine ⟨{a₀}, fun s => s a₀, Set.singleton_nonempty a₀, ?_, ?_, ?_⟩
  · intro s t
    constructor
    · intro hst a ha; rw [Set.mem_singleton_iff] at ha; subst ha; exact hst
    · intro hst; exact hst a₀ rfl
  · obtain ⟨x, y, hxy⟩ := exists_pair_ne V
    exact ⟨fun _ => x, fun _ => y, hxy⟩
  · have hfix : Fixes U ({a₀} : Set ι) := by
      intro s a ha; rw [Set.mem_singleton_iff] at ha; subst ha; exact h s
    have hdep : DependsOn (fun s : Mem ι V => s a₀) ({a₀} : Set ι) :=
      fun s t hst => hst a₀ rfl
    exact model_persists hfix hdep

/-- [Decoupling] §3, Corollary 3.3 (the decoupling dichotomy). Over the value type `V`, existence
of a faithful, non-constant model that persists across all prediction steps is *equivalent* to the
update having a read-only cell. Forward is the maximality half `exists_fixed_cell_of_persists`
(its non-constancy hypothesis is unused); backward is the witness `persists_of_fixed_cell`. -/
theorem decoupling_dichotomy [Nontrivial V] {U : Mem ι V → Mem ι V} :
    (∃ (R : Set ι) (decode : Mem ι V → V), R.Nonempty ∧ Faithful decode R ∧
      (∃ s t, decode s ≠ decode t) ∧ ∀ k s, decode (U^[k] s) = decode s)
    ↔ ∃ a, ∀ s, U s a = s a := by
  constructor
  · rintro ⟨R, decode, hne, hf, -, hpers⟩
    exact exists_fixed_cell_of_persists hne hf hpers
  · rintro ⟨a₀, h⟩
    exact persists_of_fixed_cell a₀ h

/-! ### The relativized Decoupling Lemma ([Decoupling] §3, Proposition 3.4)

The equivalence relativized to an update-closed set of states `Ω` (`∀ s ∈ Ω, U s ∈ Ω`): decoupling
need only hold *on* `Ω`, and persistence is then read only along `Ω`-orbits. Recovers the global
`decoupling_iff_persists_all` at `Ω = Set.univ`. -/

/-- [Decoupling] §3, Proposition 3.4 (mechanism, relativized). On an update-closed set `Ω`, cells
the update fixes throughout `Ω` stay fixed across every iteration of any `Ω`-orbit. The
`fixes_iterate`
induction, with `Ω`-membership threaded through the closure hypothesis `hΩ`. -/
theorem fixes_iterate_on {U : Mem ι V → Mem ι V} {R : Set ι} {Ω : Set (Mem ι V)}
    (hΩ : ∀ s ∈ Ω, U s ∈ Ω) (hfix : ∀ s ∈ Ω, ∀ a ∈ R, U s a = s a) :
    ∀ k, ∀ s ∈ Ω, ∀ a ∈ R, (U^[k] s) a = s a := by
  intro k
  induction k with
  | zero => intro s _ a _; rfl
  | succ k ih =>
      intro s hs a ha
      rw [Function.iterate_succ_apply, ih (U s) (hΩ s hs) a ha]
      exact hfix s hs a ha

/-- [Decoupling] §3, Proposition 3.4 (the relativized equivalence). For a faithful model and an
update-closed set of states `Ω`, decoupling *on* `Ω` (the update is read-only on `R` at every state
of `Ω`) holds iff the model persists across every iteration along `Ω`-orbits. The mirror of
`decoupling_iff_persists_all`; the ⇐ direction uses persistence at `k = 1` only. -/
theorem decoupling_iff_persists_on {U : Mem ι V → Mem ι V} {R : Set ι} {decode : Mem ι V → M}
    {Ω : Set (Mem ι V)} (hf : Faithful decode R) (hΩ : ∀ s ∈ Ω, U s ∈ Ω) :
    (∀ s ∈ Ω, ∀ a ∈ R, U s a = s a) ↔ (∀ s ∈ Ω, ∀ k, decode (U^[k] s) = decode s) := by
  constructor
  · intro hfix s hs k
    exact hf.dependsOn _ _ (fun a ha => fixes_iterate_on hΩ hfix k s hs a ha)
  · intro hpers s hs a ha
    have h1 : decode (U s) = decode s := by
      have := hpers s hs 1; rwa [Function.iterate_one] at this
    exact (hf (U s) s).mp h1 a ha

/-- Coherence: the global `decoupling_iff_persists_all` is exactly the `Ω = Set.univ` instance of
`decoupling_iff_persists_on` (`U`-closure of `Set.univ` is trivial). -/
example {U : Mem ι V → Mem ι V} {R : Set ι} {decode : Mem ι V → M} (hf : Faithful decode R) :
    Fixes U R ↔ ∀ k s, decode (U^[k] s) = decode s := by
  have h := decoupling_iff_persists_on (U := U) (R := R) (decode := decode)
    (Ω := Set.univ) hf (fun s _ => Set.mem_univ _)
  constructor
  · intro hU k s
    exact h.mp (fun s _ a ha => hU s a ha) s (Set.mem_univ s) k
  · intro hall s a ha
    exact h.mpr (fun s _ k => hall k s) s (Set.mem_univ s) a ha

end Decoupling
