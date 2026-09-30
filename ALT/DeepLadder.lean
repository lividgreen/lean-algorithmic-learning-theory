/-
Copyright (c) 2026 Mykola Palamarchuk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mykola Palamarchuk
-/
module

public import ALT.AccretingExcess
public import ALT.AccretiveDecoupling
public import Foundation.FirstOrder.Incompleteness.Speedup

-- Formal-check file, not Mathlib-destined: opt out of the house-style linters.
set_option linter.style.header false
set_option linter.style.longLine false

/-!
# The deep ladder: the recurrence of the crossing over each enlarged theory ([Inevitability] §6)

[Inevitability] §6 (the paragraph beginning "Iterated, this would be a reflection ladder") reads
the corpus's crossing as a ladder: the guest crosses the internalization threshold for the host's
current theory, evolution appends the represented reflection principle, and the enlarged host
admits a guest that outgrows it. Among its unproved ingredients is "the recurrence of the crossing
over each enlarged theory `T_{n+1}`". This module builds that recurrence as a corollary of two
parametric landed facts (`AccretingWitness.eventually_hostsAt`, `ExcessOrderComplete.outgrows_arith`)
and Foundation's per-theory incompleteness, together with `ALT/AccretiveDecoupling.lean`'s
committing substrate, which supplies the ladder's coupling to a growing host's own written code.

## Main results

* `RungSelector` / `ladderTheory` / `rung` — a chain builder, parametric in a **rung selector**:
  given a rule for picking, at each theory `T` in the chain, a sentence true in `ℕ` and unprovable
  in `T`, builds the theory that appends it, and the rung sentence itself, at every stage.
* `rung_true` / `rung_unprovable` / `rung_injective` — the chain's basic behavior: every rung is
  true and unprovable in the theory that precedes it, and distinct rungs are distinct sentences.
* `ladderTheory_lt_succ` — the ladder ascends STRICTLY: each theory is strictly weaker than its
  successor, at any selector.
* `hiddenSelector` — the canonical rung selector at `𝗣𝗔⁻`, built from Foundation's incompleteness
  theorem via `Classical.epsilon`.
* `explicitSelector` — the EXPLICIT rung selector at base `𝗜𝚺₁`: Foundation's own Gödel sentence of
  each theory's standard provability predicate, exhibited rather than chosen; `explicitLadder` /
  `explicitRung` instantiate the chain at it, with `explicitRung_eq_gödel` the `rfl` identification.
* `ladder_outgrows` / `accreting_ladder` — **the recurrence itself**: at every rung `n`, the crossing
  (`ExcessOrder.Outgrows`, unconditionally discharged) recurs, hosted eventually and forever after
  (`AccretingWitness.eventually_hostsAt`'s pattern), exactly as [Inevitability] §6 asks.
* `ladder_card_le_at_budget` — the ladder's own capacity bound (`CategoricalThreshold.ladder_card_le`,
  [Inevitability] §6 Remark 6.4), read off through the rungs' Gödel numbers.
* `committedTheory` / `committedTheory_at_commitStep` / `ladderTheory_subset_committedTheory` — the
  **coupling**: a padded commit schedule onto `AccretiveDecoupling.seqWrite`'s committing substrate,
  so that the ladder's theory at stage `n` is EXACTLY the code held in a growing host's written
  region at the corresponding commit step, and stays held under every later step.
* `explicit_rung_true` / `explicit_rung_unprovable` / `explicit_accreting_ladder` /
  `explicit_ladder_card_le_at_budget` / `explicit_committedTheory_at_commitStep` — the module's
  main results, all instantiated at the canonical `explicitSelector`/`𝗜𝚺₁` base with no remaining
  hypothesis.
* `explicitRung_iff_consistent` / `explicitLadder_proves_rung_iff_consistent` /
  `explicitLadder_succ_equiv_con` — the explicit ladder AS a consistency progression
  ([Inevitability] §6 Proposition 6.16): every rung is, provably over `𝗜𝚺₁`, equivalent to the
  consistency sentence of the theory it extends (Foundation's `gödel_iff_con` at that theory's own
  standard provability predicate), and each successor theory is deductively equivalent to
  Foundation's own consistency extension `T ∪ T.Con`. This is the module's first use of
  Foundation's `Theory.Con` / `Theory.consistent`.

## Scope

The content this module commissions is in two places, as the design record found: the COUPLING
(above) and the RATE, a property of the theory definitions the ladder carries rather than of the
crossing recurrence itself. The rate — the growth of each rung's defining data under
`Theory.Δ₁.insert` — is **not** built here; the identification of a ladder rung's guest with a
decoupled subsystem carrying an internal theory ([Inevitability] §2's own modelling step) also stays
paper-level, exactly as `CategoricalThreshold.lean`'s own ladder section already records.
-/


@[expose] public section

namespace DeepLadder

open ExcessOrder
open RealizabilityCCC RealizabilityRecursor
open PersistenceCapacity Decoupling AdditiveComplexity
open FFL.FirstOrder FFL.FirstOrder.Arithmetic

/-! ## Piece 1: the chain builder -/

variable {B : ArithmeticTheory}

/-- A rung selector at base `B`: for every theory carrying its definability data, a sentence, true
in `ℕ` and unprovable in the theory, whenever the theory extends `B` and is true in `ℕ`. -/
structure RungSelector (B : ArithmeticTheory) where
  pick : (T : ArithmeticTheory) → T.Δ₁ → Sentence ℒₒᵣ
  true_pick : ∀ (T : ArithmeticTheory) (d : T.Δ₁) [B ⪯ T] [ℕ↓[ℒₒᵣ] ⊧* T], ℕ↓[ℒₒᵣ] ⊧ pick T d
  unprovable_pick : ∀ (T : ArithmeticTheory) (d : T.Δ₁) [B ⪯ T] [ℕ↓[ℒₒᵣ] ⊧* T], T ⊬ pick T d

variable (sel : RungSelector B) (T₀ : ArithmeticTheory) (d₀ : T₀.Δ₁)

/-- The chain, as a theory-plus-its-definability-data pair, by explicit `Nat.rec` (so the defining
equations below hold by `rfl`, not merely propositionally). -/
noncomputable def ladderPair : ℕ → Σ T : ArithmeticTheory, T.Δ₁ :=
  fun n => Nat.rec (motive := fun _ => Σ T : ArithmeticTheory, T.Δ₁) ⟨T₀, d₀⟩
    (fun _ p => ⟨insert (sel.pick p.1 p.2) p.1, by haveI := p.2; infer_instance⟩) n

/-- The theory at stage `n` of the ladder built from `sel` starting at `(T₀, d₀)`. -/
noncomputable def ladderTheory (n : ℕ) : ArithmeticTheory := (ladderPair sel T₀ d₀ n).1

/-- The `Δ₁`-definability data of `ladderTheory sel T₀ d₀ n`. -/
@[reducible] noncomputable def ladderDelta1 (n : ℕ) : (ladderTheory sel T₀ d₀ n).Δ₁ :=
  (ladderPair sel T₀ d₀ n).2

/-- The sentence appended at stage `n`: the selector's pick for the theory then current. -/
noncomputable def rung (n : ℕ) : Sentence ℒₒᵣ := sel.pick (ladderTheory sel T₀ d₀ n) (ladderDelta1 sel T₀ d₀ n)

theorem ladderTheory_zero : ladderTheory sel T₀ d₀ 0 = T₀ := rfl

theorem ladderTheory_succ (n : ℕ) :
    ladderTheory sel T₀ d₀ (n + 1) = insert (rung sel T₀ d₀ n) (ladderTheory sel T₀ d₀ n) := rfl

/-- The stage-`n` theory is exactly the base plus the first `n` rungs. -/
theorem ladderTheory_eq_union (n : ℕ) :
    ladderTheory sel T₀ d₀ n = T₀ ∪ {φ | ∃ i < n, φ = rung sel T₀ d₀ i} := by
  induction n with
  | zero => rw [ladderTheory_zero]; simp
  | succ n ih =>
    rw [ladderTheory_succ, ih]
    ext φ
    simp only [Set.mem_insert_iff, Set.mem_union, Set.mem_ofPred_eq]
    constructor
    · rintro (h | h | ⟨i, hi, hφ⟩)
      · exact Or.inr ⟨n, by omega, h⟩
      · exact Or.inl h
      · exact Or.inr ⟨i, by omega, hφ⟩
    · rintro (h | ⟨i, hi, hφ⟩)
      · exact Or.inr (Or.inl h)
      · rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi' | hi'
        · exact Or.inr (Or.inr ⟨i, hi', hφ⟩)
        · subst hi'; exact Or.inl hφ

theorem ladderTheory_subset {n m : ℕ} (h : n ≤ m) :
    ladderTheory sel T₀ d₀ n ⊆ ladderTheory sel T₀ d₀ m := by
  rw [ladderTheory_eq_union, ladderTheory_eq_union]
  apply Set.union_subset_union_right
  rintro φ ⟨i, hi, hφ⟩
  exact ⟨i, by omega, hφ⟩

theorem base_le_ladderTheory [B ⪯ T₀] (n : ℕ) : B ⪯ ladderTheory sel T₀ d₀ n := by
  have hsub : T₀ ⊆ ladderTheory sel T₀ d₀ n := by
    rw [ladderTheory_eq_union]; exact Set.subset_union_left
  exact FFL.Entailment.WeakerThan.trans (inferInstance : B ⪯ T₀) (FFL.Entailment.Axiomatized.le_of_subset hsub)

theorem rung_mem_succ (n : ℕ) : rung sel T₀ d₀ n ∈ ladderTheory sel T₀ d₀ (n + 1) := by
  rw [ladderTheory_succ]; exact Set.mem_insert _ _

variable [B ⪯ T₀] [ℕ↓[ℒₒᵣ] ⊧* T₀]

/-- The three per-stage facts, proved together: `models_ladderTheory`, `rung_true` and
`rung_unprovable` are mutually dependent (stage `n+1`'s model fact needs stage `n`'s rung-truth,
which itself needs stage `n`'s model fact to invoke the selector), so one induction proves all
three at once; they are restated as separate named theorems below for citation. -/
theorem ladder_facts (n : ℕ) :
    (ℕ↓[ℒₒᵣ] ⊧* ladderTheory sel T₀ d₀ n) ∧ (ℕ↓[ℒₒᵣ] ⊧ rung sel T₀ d₀ n) ∧
      (ladderTheory sel T₀ d₀ n ⊬ rung sel T₀ d₀ n) := by
  induction n with
  | zero =>
    have : ℕ↓[ℒₒᵣ] ⊧* ladderTheory sel T₀ d₀ 0 := by rw [ladderTheory_zero]; infer_instance
    have : B ⪯ ladderTheory sel T₀ d₀ 0 := base_le_ladderTheory sel T₀ d₀ 0
    exact ⟨inferInstance, sel.true_pick _ _, sel.unprovable_pick _ _⟩
  | succ n ih =>
    have : ℕ↓[ℒₒᵣ] ⊧* ladderTheory sel T₀ d₀ (n + 1) := by
      rw [ladderTheory_succ]; simp [ih.1, ih.2.1]
    have : B ⪯ ladderTheory sel T₀ d₀ (n + 1) := base_le_ladderTheory sel T₀ d₀ (n + 1)
    exact ⟨inferInstance, sel.true_pick _ _, sel.unprovable_pick _ _⟩

theorem models_ladderTheory (n : ℕ) : ℕ↓[ℒₒᵣ] ⊧* ladderTheory sel T₀ d₀ n :=
  (ladder_facts sel T₀ d₀ n).1

theorem rung_true (n : ℕ) : ℕ↓[ℒₒᵣ] ⊧ rung sel T₀ d₀ n :=
  (ladder_facts sel T₀ d₀ n).2.1

theorem rung_unprovable (n : ℕ) : ladderTheory sel T₀ d₀ n ⊬ rung sel T₀ d₀ n :=
  (ladder_facts sel T₀ d₀ n).2.2

theorem rung_injective : Function.Injective (rung sel T₀ d₀) := by
  intro m n hmn
  rcases lt_trichotomy m n with hlt | heq | hlt
  · exfalso
    have hmem : rung sel T₀ d₀ m ∈ ladderTheory sel T₀ d₀ n :=
      ladderTheory_subset sel T₀ d₀ (by omega) (rung_mem_succ sel T₀ d₀ m)
    have hprov : ladderTheory sel T₀ d₀ n ⊢ rung sel T₀ d₀ n := by
      rw [← hmn]; exact FFL.Entailment.Axiomatized.by_axm hmem
    exact rung_unprovable sel T₀ d₀ n hprov
  · exact heq
  · exfalso
    have hmem : rung sel T₀ d₀ n ∈ ladderTheory sel T₀ d₀ m :=
      ladderTheory_subset sel T₀ d₀ (by omega) (rung_mem_succ sel T₀ d₀ n)
    have hprov : ladderTheory sel T₀ d₀ m ⊢ rung sel T₀ d₀ m := by
      rw [hmn]; exact FFL.Entailment.Axiomatized.by_axm hmem
    exact rung_unprovable sel T₀ d₀ m hprov

/-- The ladder ascends strictly: each theory is strictly weaker than its successor, which proves
the rung the earlier theory cannot ([Inevitability] §6 Proposition 6.16). -/
theorem ladderTheory_lt_succ (n : ℕ) :
    ladderTheory sel T₀ d₀ n ⪱ ladderTheory sel T₀ d₀ (n + 1) := by
  have : ladderTheory sel T₀ d₀ n ⪯ ladderTheory sel T₀ d₀ (n + 1) :=
    FFL.Entailment.Axiomatized.le_of_subset (ladderTheory_subset sel T₀ d₀ (Nat.le_succ n))
  exact FFL.Entailment.StrictlyWeakerThan.of_unprovable_provable (rung_unprovable sel T₀ d₀ n)
    (FFL.Entailment.Axiomatized.by_axm (rung_mem_succ sel T₀ d₀ n))

theorem encode_rung_injective : Function.Injective (fun n => Encodable.encode (rung sel T₀ d₀ n)) := by
  intro m n hmn
  exact rung_injective sel T₀ d₀ (Encodable.encode_injective hmn)

/-! ## Piece 2: the hidden selector at base `𝗣𝗔⁻` -/

/-- The canonical rung selector at `𝗣𝗔⁻`, built from Foundation's incompleteness theorem via
`Classical.epsilon`: `pick T _` does not itself assume `T` extends `𝗣𝗔⁻` or is true in `ℕ` (those
hypotheses arrive only in `true_pick`/`unprovable_pick`), so its witness is chosen without appeal to
`exists_true_but_unprovable_sentence_of_sigma1sound T`, which needs exactly those hypotheses to typecheck. -/
noncomputable def hiddenSelector : RungSelector (𝗣𝗔⁻ : ArithmeticTheory) where
  pick T _ := by
    haveI : Nonempty (Sentence ℒₒᵣ) := ⟨(⊥ : Sentence ℒₒᵣ)⟩
    exact Classical.epsilon (fun δ : Sentence ℒₒᵣ => (ℕ↓[ℒₒᵣ] ⊧ δ) ∧ T ⊬ δ)
  true_pick T d := by
    intro _ _
    have : Nonempty (Sentence ℒₒᵣ) := ⟨(⊥ : Sentence ℒₒᵣ)⟩
    have := d
    exact (Classical.epsilon_spec
      (FFL.FirstOrder.Arithmetic.exists_true_but_unprovable_sentence_of_sigma1sound T)).1
  unprovable_pick T d := by
    intro _ _
    have : Nonempty (Sentence ℒₒᵣ) := ⟨(⊥ : Sentence ℒₒᵣ)⟩
    have := d
    exact (Classical.epsilon_spec
      (FFL.FirstOrder.Arithmetic.exists_true_but_unprovable_sentence_of_sigma1sound T)).2

/-! ## Piece 2′: the explicit selector at base `𝗜𝚺₁` -/

/-- Truth in `ℕ` of Foundation's Gödel sentence for the standard provability predicate: for a
`Δ₁`-definable arithmetic theory extending `𝗜𝚺₁` and true in `ℕ`, the fixed point of the negated
provability predicate holds in `ℕ`. -/
theorem models_gödel_standardProvability (T : ArithmeticTheory) [T.Δ₁] [𝗜𝚺₁ ⪯ T]
    [ℕ↓[ℒₒᵣ] ⊧* T] :
    ℕ↓[ℒₒᵣ] ⊧ ProvabilityAbstraction.gödel T.standardProvability := by
  by_contra hG
  have hspec : (𝗜𝚺₁ : ArithmeticTheory) ⊢
      ProvabilityAbstraction.gödel T.standardProvability 🡘
        ∼(T.standardProvability (ProvabilityAbstraction.gödel T.standardProvability)) :=
    ProvabilityAbstraction.gödel_spec
  have hmodels : ℕ↓[ℒₒᵣ] ⊧
      (ProvabilityAbstraction.gödel T.standardProvability 🡘
        ∼(T.standardProvability (ProvabilityAbstraction.gödel T.standardProvability))) :=
    models_of_provable inferInstance hspec
  simp at hmodels
  have hBG : ℕ↓[ℒₒᵣ] ⊧ (T.standardProvability (ProvabilityAbstraction.gödel T.standardProvability)) := by
    by_contra hnB
    exact hG (hmodels.mpr hnB)
  have hproof : T ⊢ ProvabilityAbstraction.gödel T.standardProvability :=
    T.standardProvability.sound_on hBG
  exact ProvabilityAbstraction.unprovable_gödel hproof

/-- The `pick` function underlying `explicitSelector`, named so the selector's fields can `show`
against it instead of forcing a defeq check through an inline tactic term. -/
noncomputable def explicitPick (T : ArithmeticTheory) (d : T.Δ₁) : Sentence ℒₒᵣ :=
  ProvabilityAbstraction.gödel (@Theory.standardProvability ℒₒᵣ _ _ T d)

/-- The explicit rung selector at base `𝗜𝚺₁`: at each theory, Foundation's own Gödel sentence of its
standard provability predicate — exhibited, where `hiddenSelector`'s is chosen. -/
noncomputable def explicitSelector : RungSelector (𝗜𝚺₁ : ArithmeticTheory) where
  pick := explicitPick
  true_pick T d := by
    intro _ _
    change ℕ↓[ℒₒᵣ] ⊧ ProvabilityAbstraction.gödel (@Theory.standardProvability ℒₒᵣ _ _ T d)
    exact models_gödel_standardProvability T
  unprovable_pick T d := by
    intro _ _
    change T ⊬ ProvabilityAbstraction.gödel (@Theory.standardProvability ℒₒᵣ _ _ T d)
    exact ProvabilityAbstraction.unprovable_gödel

/-- The explicit ladder's rung IS Foundation's Gödel sentence of the stage theory, at that theory's
own definability data — by `rfl`, since `rung` unfolds to the selector's `pick`. -/
theorem explicitRung_eq_gödel (T₀ : ArithmeticTheory) (d₀ : T₀.Δ₁) (n : ℕ) :
    rung explicitSelector T₀ d₀ n =
      ProvabilityAbstraction.gödel
        (@Theory.standardProvability ℒₒᵣ _ _ (ladderTheory explicitSelector T₀ d₀ n)
          (ladderDelta1 explicitSelector T₀ d₀ n)) :=
  rfl

/-! ## Piece 3: the recurrence at the accreting witness, and the count on the ladder -/

/-- The crossing stage of rung `n`: `eventually_hostsAt`'s `t₀`, read at the rung's own code. -/
noncomputable def rungStage (n : ℕ) : ℕ :=
  GodelInternalization.capacity (Nat.clog 2 (Encodable.encode (rung sel T₀ d₀ n) + 1))

theorem rung_incompleteness (n : ℕ) :
    GodelThreshold.Incompleteness (Encodable.encode : Sentence ℒₒᵣ → ℕ)
      (fun δ => ladderTheory sel T₀ d₀ n ⊢ δ) (fun δ => ℕ↓[ℒₒᵣ] ⊧ δ)
      (Encodable.encode (rung sel T₀ d₀ n)) :=
  ⟨rung sel T₀ d₀ n, rfl, rung_true sel T₀ d₀ n, rung_unprovable sel T₀ d₀ n⟩

omit [B ⪯ T₀] [ℕ↓[ℒₒᵣ] ⊧* T₀] in
theorem hostsAt_rung (n t : ℕ) (h : rungStage sel T₀ d₀ n ≤ t) :
    CategoricalThreshold.hostsAt (t + 1) (Encodable.encode (rung sel T₀ d₀ n)) :=
  CategoricalThreshold.hostsAt_mono (show rungStage sel T₀ d₀ n ≤ t + 1 by omega)
    (CategoricalThreshold.hostsAt_enters _)

omit [B ⪯ T₀] [ℕ↓[ℒₒᵣ] ⊧* T₀] in
theorem not_hostsAt_rung (n w : ℕ) (h : w < Nat.clog 2 (Encodable.encode (rung sel T₀ d₀ n) + 1)) :
    ¬ CategoricalThreshold.hostsAt w (Encodable.encode (rung sel T₀ d₀ n)) :=
  CategoricalThreshold.hostsAt_excludes h

/-- **The recurrence itself**: at every rung `n`, the internalization threshold recurs,
unconditionally discharged — `ExcessOrder.outgrows` at the rung's own code, with
`rung_incompleteness` closing the incompleteness antecedent that `Outgrows` otherwise leaves
imported. -/
theorem ladder_outgrows (n t Mchk : ℕ)
    (hhost : CategoricalThreshold.hostsAt (t + 1) (Encodable.encode (rung sel T₀ d₀ n)))
    (h1 : Encodable.encode (rung sel T₀ d₀ n) < Mchk)
    (h2 : Mchk ≤ (Encodable.encode (rung sel T₀ d₀ n)) ^ 2) :
    ∃ R : ReflectiveAsm (Encodable.encode (rung sel T₀ d₀ n)), R.depth = Mchk ∧
      CapacityLayer.FitsIn (recursorAsm R.depth) (t + 1) ∧
      ∃ M, GodelThreshold.RepresentsUnderivableTruth (Encodable.encode : Sentence ℒₒᵣ → ℕ)
        (fun δ => ladderTheory sel T₀ d₀ n ⊢ δ) (fun δ => ℕ↓[ℒₒᵣ] ⊧ δ) M := by
  obtain ⟨R, hdepth, hfits, himp⟩ :=
    ExcessOrder.outgrows (t + 1) (Encodable.encode : Sentence ℒₒᵣ → ℕ)
      (fun δ => ladderTheory sel T₀ d₀ n ⊢ δ) (fun δ => ℕ↓[ℒₒᵣ] ⊧ δ)
      (Encodable.encode (rung sel T₀ d₀ n)) Mchk hhost h1 h2
  exact ⟨R, hdepth, hfits, himp (rung_incompleteness sel T₀ d₀ n)⟩

/-- **The ladder's own capacity bound** ([Inevitability] §6 Remark 6.4, read through the rungs'
Gödel numbers): a finite set of rungs, each reaching the threshold within a common budget `w`, has
at most `2 ^ w` elements. `CategoricalThreshold.ladder_card_le` counted Gödel numbers directly; this
transports the count along `rung`'s injectivity. -/
theorem ladder_card_le_at_budget (w : ℕ) (s : Finset ℕ)
    (hs : ∀ n ∈ s, 2 ≤ Encodable.encode (rung sel T₀ d₀ n) ∧
      CategoricalThreshold.hostsAt w (Encodable.encode (rung sel T₀ d₀ n))) :
    s.card ≤ 2 ^ w := by
  have hinj : Function.Injective (fun n => Encodable.encode (rung sel T₀ d₀ n)) :=
    encode_rung_injective sel T₀ d₀
  rw [← Finset.card_image_of_injective s hinj]
  apply CategoricalThreshold.ladder_card_le
  intro g hg
  simp only [Finset.mem_image] at hg
  obtain ⟨n, hn, hgn⟩ := hg
  obtain ⟨h2, hhost⟩ := hs n hn
  subst hgn
  exact (CategoricalThreshold.reflectiveWithin_at_capacity h2).mono hhost

/-- The ladder's crossing recurrence, packaged in the shape of [Inevitability] §6's own ask: at
every rung `n`, eventual hosting (a fixed `t₀` hosted forever after) beside the unconditional
excess it delivers. -/
theorem accreting_ladder (n : ℕ) :
    (∃ t₀, ∀ t, t₀ ≤ t → CategoricalThreshold.hostsAt (t + 1) (Encodable.encode (rung sel T₀ d₀ n))) ∧
    ∀ t Mchk, CategoricalThreshold.hostsAt (t + 1) (Encodable.encode (rung sel T₀ d₀ n)) →
      Encodable.encode (rung sel T₀ d₀ n) < Mchk → Mchk ≤ (Encodable.encode (rung sel T₀ d₀ n)) ^ 2 →
      ∃ R : ReflectiveAsm (Encodable.encode (rung sel T₀ d₀ n)), R.depth = Mchk ∧
        CapacityLayer.FitsIn (recursorAsm R.depth) (t + 1) ∧
        ∃ M, GodelThreshold.RepresentsUnderivableTruth (Encodable.encode : Sentence ℒₒᵣ → ℕ)
          (fun δ => ladderTheory sel T₀ d₀ n ⊢ δ) (fun δ => ℕ↓[ℒₒᵣ] ⊧ δ) M :=
  ⟨⟨rungStage sel T₀ d₀ n, fun t ht => hostsAt_rung sel T₀ d₀ n t ht⟩,
    fun t Mchk hhost h1 h2 => ladder_outgrows sel T₀ d₀ n t Mchk hhost h1 h2⟩

/-! ## Piece 4: the coupling to the committing substrate at the padded schedule -/

/-- The theory a committing substrate's state carries: the base plus every sentence whose code is
written in the region (cells `1 … s 0`); the blank `0` decodes to nothing, every sentence's code
being positive (`encode_sentence_pos`). -/
def committedTheory (T₀ : ArithmeticTheory) (s : Decoupling.Mem ℕ ℕ) : ArithmeticTheory :=
  T₀ ∪ {φ | ∃ a, 1 ≤ a ∧ a ≤ s 0 ∧ Encodable.encode φ = s a}

/-- Every sentence's code is positive: `Semiformula.toNat` ends every constructor case in `+ 1`,
which is exactly what lets `committedTheory` read "occupied" off a nonzero cell with no separate
decode tag. -/
theorem encode_sentence_pos (φ : Sentence ℒₒᵣ) : 0 < Encodable.encode φ := by
  rw [Semiformula.encode_eq_toNat]
  cases φ <;> simp only [Semiformula.toNat] <;> omega

theorem committedTheory_seqStart (T₀ : ArithmeticTheory) :
    committedTheory T₀ Decoupling.seqStart = T₀ := by
  unfold committedTheory
  ext φ
  simp only [Set.mem_union, Set.mem_ofPred_eq, or_iff_left_iff_imp]
  rintro ⟨a, ha1, ha2, -⟩
  simp only [Decoupling.seqStart] at ha2
  omega

/-- The padded schedule: rung `n` is committed no earlier than its crossing stage and strictly
after the previous commit, by explicit `Nat.rec` (so the defining equations hold by `rfl`). -/
noncomputable def commitStep : ℕ → ℕ :=
  fun n => Nat.rec (rungStage sel T₀ d₀ 0)
    (fun k prev => max (rungStage sel T₀ d₀ (k + 1)) (prev + 1)) n

private theorem commitStep_zero : commitStep sel T₀ d₀ 0 = rungStage sel T₀ d₀ 0 := rfl

private theorem commitStep_succ (n : ℕ) :
    commitStep sel T₀ d₀ (n + 1) = max (rungStage sel T₀ d₀ (n + 1)) (commitStep sel T₀ d₀ n + 1) := rfl

private theorem commitStep_lt_succ (n : ℕ) :
    commitStep sel T₀ d₀ n < commitStep sel T₀ d₀ (n + 1) := by
  rw [commitStep_succ]
  exact lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_right _ _)

theorem commitStep_strictMono : StrictMono (commitStep sel T₀ d₀) :=
  strictMono_nat_of_lt_succ (commitStep_lt_succ sel T₀ d₀)

theorem rungStage_le_commitStep (n : ℕ) : rungStage sel T₀ d₀ n ≤ commitStep sel T₀ d₀ n := by
  cases n with
  | zero => exact le_refl _
  | succ n => rw [commitStep_succ]; exact le_max_left _ _

theorem hostsAt_rung_at_commitStep (n : ℕ) :
    CategoricalThreshold.hostsAt (commitStep sel T₀ d₀ n + 1) (Encodable.encode (rung sel T₀ d₀ n)) :=
  hostsAt_rung sel T₀ d₀ n (commitStep sel T₀ d₀ n) (rungStage_le_commitStep sel T₀ d₀ n)

open Classical in
/-- The stream a `seqWrite` commitment writes: rung `n`'s code at its own commit step, blank (`0`)
at every other step. -/
noncomputable def ladderStream (k : ℕ) : ℕ :=
  if h : ∃ n, commitStep sel T₀ d₀ n = k then
    Encodable.encode (rung sel T₀ d₀ (Classical.choose h))
  else 0

theorem ladderStream_commitStep (n : ℕ) :
    ladderStream sel T₀ d₀ (commitStep sel T₀ d₀ n) = Encodable.encode (rung sel T₀ d₀ n) := by
  have hex : ∃ m, commitStep sel T₀ d₀ m = commitStep sel T₀ d₀ n := ⟨n, rfl⟩
  have heq : Classical.choose hex = n :=
    (commitStep_strictMono sel T₀ d₀).injective (Classical.choose_spec hex)
  simp only [ladderStream, dite_eq_left hex, heq]

theorem ladderStream_eq_zero (k : ℕ) (h : ∀ n, commitStep sel T₀ d₀ n ≠ k) :
    ladderStream sel T₀ d₀ k = 0 := by
  unfold ladderStream
  rw [dite_eq_right (not_exists.mpr h)]

/-- **EXACT**: at the commit step of rung `n` the region carries exactly the first `n` rungs — the
ladder's theory at stage `n` is precisely the code held in the committing substrate's written
region at that step. -/
theorem committedTheory_at_commitStep (n : ℕ) :
    committedTheory T₀
        ((Decoupling.seqWrite (ladderStream sel T₀ d₀))^[commitStep sel T₀ d₀ n] Decoupling.seqStart)
      = ladderTheory sel T₀ d₀ n := by
  rw [Decoupling.seqWrite_iterate_seqStart, ladderTheory_eq_union]
  simp only [committedTheory, ite_true]
  set t := commitStep sel T₀ d₀ n with ht
  ext φ
  simp only [Set.mem_union, Set.mem_ofPred_eq]
  constructor
  · rintro (hφ | ⟨a, ha1, ha2, hφ⟩)
    · exact Or.inl hφ
    · right
      rw [ite_eq_right (show a ≠ 0 by omega), ite_eq_left ⟨ha1, ha2⟩] at hφ
      have hpos : 0 < Encodable.encode φ := encode_sentence_pos φ
      by_cases hex : ∃ i, commitStep sel T₀ d₀ i = a - 1
      · obtain ⟨i, hi⟩ := hex
        have hival : ladderStream sel T₀ d₀ (a - 1) = Encodable.encode (rung sel T₀ d₀ i) := by
          rw [← hi]; exact ladderStream_commitStep sel T₀ d₀ i
        rw [hival] at hφ
        have hphi : φ = rung sel T₀ d₀ i := Encodable.encode_injective hφ
        refine ⟨i, ?_, hphi⟩
        have hlt : commitStep sel T₀ d₀ i < t := by omega
        exact (commitStep_strictMono sel T₀ d₀).lt_iff_lt.mp hlt
      · exfalso
        push Not at hex
        have hz : ladderStream sel T₀ d₀ (a - 1) = 0 := ladderStream_eq_zero sel T₀ d₀ (a - 1) hex
        rw [hz] at hφ
        omega
  · rintro (hφ | ⟨i, hin, hφ⟩)
    · exact Or.inl hφ
    · right
      have ha1 : 1 ≤ commitStep sel T₀ d₀ i + 1 := by omega
      have ha2 : commitStep sel T₀ d₀ i + 1 ≤ t := by
        have hlt := commitStep_lt_succ sel T₀ d₀ i
        have hmono := (commitStep_strictMono sel T₀ d₀).monotone (show i + 1 ≤ n by omega)
        omega
      refine ⟨commitStep sel T₀ d₀ i + 1, ha1, ha2, ?_⟩
      rw [ite_eq_right (show commitStep sel T₀ d₀ i + 1 ≠ 0 by omega), ite_eq_left ⟨ha1, ha2⟩]
      have heq : commitStep sel T₀ d₀ i + 1 - 1 = commitStep sel T₀ d₀ i := by omega
      rw [heq, ladderStream_commitStep, hφ]

/-- **HELD**: every later step holds rung `n` (and everything before it) — the code committed by
stage `n + 1` stays in the region at every later step `k`. -/
theorem ladderTheory_subset_committedTheory (n k : ℕ) (hk : commitStep sel T₀ d₀ n < k) :
    ladderTheory sel T₀ d₀ (n + 1) ⊆
      committedTheory T₀ ((Decoupling.seqWrite (ladderStream sel T₀ d₀))^[k] Decoupling.seqStart) := by
  rw [Decoupling.seqWrite_iterate_seqStart, ladderTheory_eq_union]
  simp only [committedTheory, ite_true]
  intro φ hφ
  simp only [Set.mem_union, Set.mem_ofPred_eq] at hφ ⊢
  rcases hφ with hφ | ⟨i, hi, hφ⟩
  · exact Or.inl hφ
  · right
    have hin : i ≤ n := by omega
    have ha1 : 1 ≤ commitStep sel T₀ d₀ i + 1 := by omega
    have ha2 : commitStep sel T₀ d₀ i + 1 ≤ k := by
      have hmono := (commitStep_strictMono sel T₀ d₀).monotone hin
      omega
    refine ⟨commitStep sel T₀ d₀ i + 1, ha1, ha2, ?_⟩
    rw [ite_eq_right (show commitStep sel T₀ d₀ i + 1 ≠ 0 by omega), ite_eq_left ⟨ha1, ha2⟩]
    have heq : commitStep sel T₀ d₀ i + 1 - 1 = commitStep sel T₀ d₀ i := by omega
    rw [heq, ladderStream_commitStep, hφ]

/-! ## The explicit ladder from `𝗜𝚺₁` itself -/

/-- The explicit ladder started at `𝗜𝚺₁` with Foundation's own `Δ₁` data
(its synthesized `𝗜𝚺₁.Δ₁` instance). -/
noncomputable abbrev explicitLadder (n : ℕ) : ArithmeticTheory :=
  ladderTheory explicitSelector 𝗜𝚺₁ inferInstance n

/-- The `n`-th rung of the explicit ladder from `𝗜𝚺₁`: the Gödel sentence of `explicitLadder n`. -/
noncomputable abbrev explicitRung (n : ℕ) : Sentence ℒₒᵣ :=
  rung explicitSelector 𝗜𝚺₁ inferInstance n

/-- Every rung of the explicit ladder is true in `ℕ` ([Inevitability] §6 Proposition 6.16). -/
theorem explicit_rung_true (n : ℕ) : ℕ↓[ℒₒᵣ] ⊧ explicitRung n :=
  rung_true explicitSelector 𝗜𝚺₁ inferInstance n

/-- Every rung of the explicit ladder is unprovable in the theory that precedes it
([Inevitability] §6 Proposition 6.16). -/
theorem explicit_rung_unprovable (n : ℕ) : explicitLadder n ⊬ explicitRung n :=
  rung_unprovable explicitSelector 𝗜𝚺₁ inferInstance n

/-- The crossing recurrence at the explicit ladder from `𝗜𝚺₁`, at every rung
([Inevitability] §6 Proposition 6.16). -/
theorem explicit_accreting_ladder (n : ℕ) :
    (∃ t₀, ∀ t, t₀ ≤ t → CategoricalThreshold.hostsAt (t + 1) (Encodable.encode (explicitRung n))) ∧
    ∀ t Mchk, CategoricalThreshold.hostsAt (t + 1) (Encodable.encode (explicitRung n)) →
      Encodable.encode (explicitRung n) < Mchk → Mchk ≤ (Encodable.encode (explicitRung n)) ^ 2 →
      ∃ R : ReflectiveAsm (Encodable.encode (explicitRung n)), R.depth = Mchk ∧
        CapacityLayer.FitsIn (recursorAsm R.depth) (t + 1) ∧
        ∃ M, GodelThreshold.RepresentsUnderivableTruth (Encodable.encode : Sentence ℒₒᵣ → ℕ)
          (fun δ => explicitLadder n ⊢ δ) (fun δ => ℕ↓[ℒₒᵣ] ⊧ δ) M :=
  accreting_ladder explicitSelector 𝗜𝚺₁ inferInstance n

/-- The explicit ladder's own capacity bound ([Inevitability] §6 Proposition 6.16, Remark 6.4). -/
theorem explicit_ladder_card_le_at_budget (w : ℕ) (s : Finset ℕ)
    (hs : ∀ n ∈ s, 2 ≤ Encodable.encode (explicitRung n) ∧
      CategoricalThreshold.hostsAt w (Encodable.encode (explicitRung n))) :
    s.card ≤ 2 ^ w :=
  ladder_card_le_at_budget explicitSelector 𝗜𝚺₁ inferInstance w s hs

/-- The explicit ladder's coupling to the committing substrate ([Inevitability] §6
Proposition 6.16): the theory at stage `n` is exactly the code held in the written region at the
corresponding commit step. -/
theorem explicit_committedTheory_at_commitStep (n : ℕ) :
    committedTheory 𝗜𝚺₁
        ((Decoupling.seqWrite (ladderStream explicitSelector 𝗜𝚺₁ inferInstance))^[
              commitStep explicitSelector 𝗜𝚺₁ inferInstance n]
          Decoupling.seqStart)
      = explicitLadder n :=
  committedTheory_at_commitStep explicitSelector 𝗜𝚺₁ inferInstance n

/-! ## The explicit ladder's rungs as consistency sentences -/

/-- The `Δ₁`-definability data needed to state `(explicitLadder n).consistent`, read off
`ladderDelta1` at the explicit selector. -/
noncomputable instance explicitLadderDelta1 (n : ℕ) : (explicitLadder n).Δ₁ :=
  ladderDelta1 explicitSelector 𝗜𝚺₁ inferInstance n

/-- At every rung of the explicit ladder, `𝗜𝚺₁` proves the rung equivalent to the consistency
sentence of the theory it extends ([Inevitability] §6 Proposition 6.16): Foundation's
`gödel_iff_con` at that theory's standard provability predicate, the rung being that predicate's
Gödel sentence by `explicitRung_eq_gödel`. -/
theorem explicitRung_iff_consistent (n : ℕ) :
    (𝗜𝚺₁ : ArithmeticTheory) ⊢ explicitRung n 🡘 (explicitLadder n).consistent := by
  have : (𝗜𝚺₁ : ArithmeticTheory) ⪯ explicitLadder n :=
    base_le_ladderTheory explicitSelector 𝗜𝚺₁ inferInstance n
  have : (𝗣𝗔⁻ : ArithmeticTheory) ⪯ explicitLadder n :=
    FFL.Entailment.WeakerThan.trans (inferInstance : (𝗣𝗔⁻ : ArithmeticTheory) ⪯ 𝗜𝚺₁)
      (base_le_ladderTheory explicitSelector 𝗜𝚺₁ inferInstance n)
  have heq : explicitRung n =
      ProvabilityAbstraction.gödel (@Theory.standardProvability ℒₒᵣ _ _ (explicitLadder n)
        (explicitLadderDelta1 n)) :=
    explicitRung_eq_gödel 𝗜𝚺₁ inferInstance n
  rw [heq, Arithmetic.Bootstrapping.consistent_eq]
  exact ProvabilityAbstraction.gödel_iff_con

/-- The theory-level form of `explicitRung_iff_consistent`, weakened along
`𝗜𝚺₁ ⪯ explicitLadder n` ([Inevitability] §6 Proposition 6.16). -/
theorem explicitLadder_proves_rung_iff_consistent (n : ℕ) :
    explicitLadder n ⊢ explicitRung n 🡘 (explicitLadder n).consistent := by
  have : (𝗜𝚺₁ : ArithmeticTheory) ⪯ explicitLadder n :=
    base_le_ladderTheory explicitSelector 𝗜𝚺₁ inferInstance n
  exact FFL.Entailment.WeakerThan.pbl (explicitRung_iff_consistent n)

/-- The successor theory of the explicit ladder is deductively equivalent to Foundation's own
consistency extension of the theory it extends ([Inevitability] §6 Proposition 6.16): the ladder's
step is the consistency step, at each theory's own standard provability predicate. -/
theorem explicitLadder_succ_equiv_con (n : ℕ) :
    explicitLadder (n + 1) ≊ explicitLadder n ∪ (explicitLadder n).Con := by
  have hle0 : (𝗜𝚺₁ : ArithmeticTheory) ⪯ explicitLadder n :=
    base_le_ladderTheory explicitSelector 𝗜𝚺₁ inferInstance n
  have hunion : explicitLadder n ∪ (explicitLadder n).Con
      = insert (explicitLadder n).consistent.val (explicitLadder n) := Set.union_singleton
  have hsucc : explicitLadder (n + 1) = insert (explicitRung n) (explicitLadder n) :=
    ladderTheory_succ explicitSelector 𝗜𝚺₁ inferInstance n
  rw [FFL.Entailment.Equiv.antisymm_iff]
  constructor
  · rw [FFL.Entailment.weakerThan_iff]
    intro φ hφ
    rw [hsucc] at hφ
    have hφ' : explicitLadder n ⊢ explicitRung n 🡒 φ := FFL.Entailment.deduction_iff.mp hφ
    have hleT' : explicitLadder n ⪯ (explicitLadder n ∪ (explicitLadder n).Con) :=
      FFL.Entailment.Axiomatized.le_of_subset Set.subset_union_left
    have hφ'' : (explicitLadder n ∪ (explicitLadder n).Con) ⊢ explicitRung n 🡒 φ :=
      FFL.Entailment.WeakerThan.pbl hφ'
    have hCon : (explicitLadder n ∪ (explicitLadder n).Con) ⊢ (explicitLadder n).consistent.val :=
      FFL.Entailment.Axiomatized.by_axm (Set.mem_union_right _ rfl)
    have hleT : (𝗜𝚺₁ : ArithmeticTheory) ⪯ (explicitLadder n ∪ (explicitLadder n).Con) :=
      FFL.Entailment.WeakerThan.trans hle0 hleT'
    have hEquiv : (explicitLadder n ∪ (explicitLadder n).Con) ⊢
        explicitRung n 🡘 (explicitLadder n).consistent :=
      FFL.Entailment.WeakerThan.pbl (explicitRung_iff_consistent n)
    exact hφ'' ⨀ (FFL.Entailment.iff_of_E hEquiv).mpr hCon
  · rw [FFL.Entailment.weakerThan_iff]
    intro φ hφ
    rw [hunion] at hφ
    have hφ' : explicitLadder n ⊢ (explicitLadder n).consistent.val 🡒 φ :=
      FFL.Entailment.deduction_iff.mp hφ
    have hleS' : explicitLadder n ⪯ explicitLadder (n + 1) :=
      FFL.Entailment.Axiomatized.le_of_subset (by rw [hsucc]; exact Set.subset_insert _ _)
    have hφ'' : explicitLadder (n + 1) ⊢ (explicitLadder n).consistent.val 🡒 φ :=
      FFL.Entailment.WeakerThan.pbl hφ'
    have hleS : (𝗜𝚺₁ : ArithmeticTheory) ⪯ explicitLadder (n + 1) :=
      FFL.Entailment.WeakerThan.trans hle0 hleS'
    have hRungMem : explicitLadder (n + 1) ⊢ explicitRung n := by
      apply FFL.Entailment.Axiomatized.by_axm
      rw [hsucc]; exact Set.mem_insert _ _
    have hEquiv : explicitLadder (n + 1) ⊢ explicitRung n 🡘 (explicitLadder n).consistent :=
      FFL.Entailment.WeakerThan.pbl (explicitRung_iff_consistent n)
    exact hφ'' ⨀ (FFL.Entailment.iff_of_E hEquiv).mp hRungMem

/-- The Ehrenfeucht–Mycielski speedup at the explicit ladder ([Inevitability] §6 Proposition 6.16):
every stage admits a sentence whose minimal-proof length drops, at the successor theory, below any
computable function of its predecessor's. The currency is proof length (`Theory.minProof`), not the
description length the ladder's rate is about. -/
theorem explicitLadder_speedup (n : ℕ) (f : ℕ → ℕ) (hf : Computable f) :
    ∃ π : ArithmeticSentence, explicitLadder n ⊢ π ∧
      f ((explicitLadder (n + 1)).minProof π) < (explicitLadder n).minProof π := by
  have : (𝗜𝚺₁ : ArithmeticTheory) ⪯ explicitLadder n :=
    base_le_ladderTheory explicitSelector 𝗜𝚺₁ inferInstance n
  have hσ : explicitLadder n ⊬ explicitRung n := explicit_rung_unprovable n
  exact Arithmetic.Bootstrapping.ehrenfeucht_mycielski_speedup_arithmetic hσ f hf

end DeepLadder
