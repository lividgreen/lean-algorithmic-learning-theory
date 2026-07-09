import Mathlib

-- Tier-1 formal check, not Mathlib-destined: opt out of the house-style header linter.
set_option linter.style.header false

/-!
# The Decoupling Lemma: structural core + necessity (Paper I §3 Lemma 3.1, target F2)

Provenance: `01_decoupling_and_categorical_threshold.md`, §3 (Lemma 3.1, the Decoupling Lemma: D1
persistence — a faithfully-encoded model survives multi-step iteration iff its code region is
read-only under the update). Tier-2 lynchpin, first increment.

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

end Decoupling
