/-
Copyright (c) 2026 Mykola Palamarchuk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mykola Palamarchuk
-/
module

public import ALT.Decoupling

-- Formal-check file, not Mathlib-destined: opt out of the house-style header linter.
set_option linter.style.header false

/-!
# Accretive decoupling: the equivalence on a growing code region ([Inevitability] §6)

[Decoupling] §3 states its equivalence for a **fixed** code region. A host whose code *accretes* —
written cells never rewritten, fresh cells appended on a frontier — needs the equivalence for a
region that grows with time, and needs the heredity claim to hold *across* the growth: a cell
written by stage `t` must stay fixed under every later step, not merely under the step taken at `t`.
This file states that extension and proves it.

The setting is stage-indexed. `R : ℕ → Set ι` is the region written by each stage, `Ω : ℕ → Set (Mem
ι V)` the states that stage admits; `Advances` says one update carries stage `t` into stage `t + 1`,
and `Accretes` says that at every stage the update is read-only on the region written *so far*.
Growth is `Monotone R`.

## The result, and what it costs

The extension is a **corollary of the relativized equivalence** ([Decoupling] §3, Proposition 3.4),
not an independent development, and the reduction is one construction: fix a stage `t` and pass to
`stagesFrom Ω t`, the states admitted at `t` or later. That set is update-closed, and on it the
update is read-only on the *single* region `R t`, because monotonicity carries `R t` inside every
later stage's region — so the fixed-partition machinery applies verbatim and returns heredity from
stage `t`. `accretive_fixes_iterate` is `fixes_iterate_on` under `stagesFrom` and nothing else.
Monotonicity is used exactly once, at that step; without it `R t` need not be read-only later and
the reduction fails.

What the reduction does *not* do is make the extension a restatement. The **limit** region — the
union of all the stages' regions — is in general not read-only, precisely because the frontier is
where writing happens, so one cannot recover the accretive statement by applying the fixed-partition
lemma to the union and reading off the stages. `not_accretes_tapeLimit` exhibits that failure on the
running instance below. The stage-indexed family is doing work; its *proof* is a corollary.

## Main results

* `Advances` / `Accretes` — the two stage-indexed hypotheses: the update advances the stage, and at
  every stage it is read-only on the region written so far.
* `accretive_fixes_iterate` — **heredity**: under monotone growth, a cell in the region written by
  stage `t` keeps its value under every iterate, from every state that stage admits.
* `accretive_persists` — the model read off stage `t`'s region survives every later step.
* `accretes_of_persists` — necessity: staged faithfulness plus one-step persistence at each stage
  forces the accretive read-only condition, mirroring `fixes_of_persists`.
* `accretive_decoupling_iff` — **the equivalence on a growing region**: for a staged faithful
  reading, accretion holds iff each stage's model persists along that stage's orbits.
* `accretive_iff_persists_on_const` — coherence: at the constant family the equivalence *is*
  [Decoupling] §3, Proposition 3.4. The fixed-partition lemma is the degenerate case, as a theorem
  rather than a remark.
* `exists_strictly_accretive_decoupling` — a **strictly growing** instance: an append-only tape
  whose written region grows by one cell per stage, with both hypotheses discharged, a staged
  faithful reading, disjoint stages, and the limit region *not* read-only. Without it every
  statement above would be satisfied by the constant family and the extension would be the old
  lemma in new clothes.
* `seqWrite` / `seqDecode_hereditary` — **the committing substrate** ([Inevitability] §6,
  `accretive_decoupling_iff`'s first theorem consumer): an arbitrary stream, one entry per stage,
  committed onto the same append-only tape; every entry it writes is held under every later
  commitment, at a footprint (`tapeRegion_bijective`) in bijection with the stream's own prefix,
  cell for cell. What the stream's entries *are*, or how they are chosen, is outside this file.

## Scope

Same shared-memory algebra as [Decoupling] §3 and nothing more: abstract cells and values, no
substrate, no description-length pricing, and no claim that any particular host accretes. What the
frontier is *written with* — how a variant is proposed, scored, and committed — is outside this
file; accretion is assumed here, not derived. The reflection ladder that [Inevitability] §6 builds
on a growing host needs, beyond this, the recurrence of the threshold crossing at each enlarged
stage, which is untouched here.
-/


@[expose] public section

namespace Decoupling

-- "Same shared-memory algebra … and nothing more": one witness per excluded territory.
assert_not_exists Nat.Partrec.Code
assert_not_exists PersistenceCapacity.emergence
assert_not_exists MeasureTheory.Measure

variable {ι V M : Type*}

/-! ## The stage-indexed hypotheses -/

/-- One update advances the stage: a state admitted at stage `t` is carried into stage `t + 1`. -/
def Advances (U : Mem ι V → Mem ι V) (Ω : ℕ → Set (Mem ι V)) : Prop :=
  ∀ t, ∀ s ∈ Ω t, U s ∈ Ω (t + 1)

/-- At every stage, `U` is read-only on the region written *so far*. This is the per-snapshot
decoupling condition; on its own it says nothing about later stages, which is exactly the gap the
results below close. -/
def Accretes (U : Mem ι V → Mem ι V) (R : ℕ → Set ι) (Ω : ℕ → Set (Mem ι V)) : Prop :=
  ∀ t, ∀ s ∈ Ω t, ∀ a ∈ R t, U s a = s a

/-- The states admitted at stage `t` **or later**. Passing to this set is the whole reduction of the
accretive statement to the fixed-partition one: it is update-closed, and `R t` sits inside every
region it can meet. -/
def stagesFrom (Ω : ℕ → Set (Mem ι V)) (t : ℕ) : Set (Mem ι V) := {s | ∃ j, s ∈ Ω (t + j)}

theorem mem_stagesFrom {Ω : ℕ → Set (Mem ι V)} {t : ℕ} {s : Mem ι V} (hs : s ∈ Ω t) :
    s ∈ stagesFrom Ω t := ⟨0, hs⟩

/-- `stagesFrom Ω t` is update-closed: advancing a stage keeps you at stage `t` or later. This is
Proposition 3.4's closure hypothesis, supplied by `Advances`. -/
theorem advances_stagesFrom {U : Mem ι V → Mem ι V} {Ω : ℕ → Set (Mem ι V)} (hadv : Advances U Ω)
    (t : ℕ) : ∀ s ∈ stagesFrom Ω t, U s ∈ stagesFrom Ω t :=
  fun _ ⟨j, hj⟩ => ⟨j + 1, hadv (t + j) _ hj⟩

/-- On `stagesFrom Ω t` the update is read-only on the *single* region `R t`. **This is the only
place growth is used**: a state at a later stage is only guaranteed read-only on that later stage's
region, and monotonicity is what puts `R t` inside it. -/
theorem accretes_stagesFrom {U : Mem ι V → Mem ι V} {R : ℕ → Set ι} {Ω : ℕ → Set (Mem ι V)}
    (hR : Monotone R) (hacc : Accretes U R Ω) (t : ℕ) :
    ∀ s ∈ stagesFrom Ω t, ∀ a ∈ R t, U s a = s a :=
  fun _ ⟨j, hj⟩ a ha => hacc (t + j) _ hj a (hR (Nat.le_add_right t j) ha)

/-! ## Heredity, and the equivalence -/

/-- **Heredity as the code accretes** ([Inevitability] §6): a cell in the region written by stage
`t` keeps its value under *every* iterate, from every state that stage admits — not merely under the
single step taken at `t`.

Proof: Proposition 3.4's mechanism (`fixes_iterate_on`) on the update-closed set `stagesFrom Ω t`
with the fixed region `R t`. -/
theorem accretive_fixes_iterate {U : Mem ι V → Mem ι V} {R : ℕ → Set ι} {Ω : ℕ → Set (Mem ι V)}
    (hR : Monotone R) (hadv : Advances U Ω) (hacc : Accretes U R Ω) :
    ∀ t k, ∀ s ∈ Ω t, ∀ a ∈ R t, (U^[k] s) a = s a :=
  fun t k s hs a ha =>
    fixes_iterate_on (advances_stagesFrom hadv t) (accretes_stagesFrom hR hacc t) k s
      (mem_stagesFrom hs) a ha

/-- Sufficiency, staged: a model read off the region written by stage `t` survives every later
step. The persistence half of the growing-host claim. -/
theorem accretive_persists {U : Mem ι V → Mem ι V} {R : ℕ → Set ι} {Ω : ℕ → Set (Mem ι V)}
    {decode : ℕ → Mem ι V → M} (hR : Monotone R) (hadv : Advances U Ω) (hacc : Accretes U R Ω)
    (hdep : ∀ t, DependsOn (decode t) (R t)) :
    ∀ t k, ∀ s ∈ Ω t, decode t (U^[k] s) = decode t s :=
  fun t k s hs => hdep t _ _ fun a ha => accretive_fixes_iterate hR hadv hacc t k s hs a ha

/-- Necessity, staged (mirroring `fixes_of_persists`): if each stage's *faithful* reading is
preserved by one step from every state that stage admits, then the update accretes. Neither growth
nor `Advances` is needed — one step never leaves the stage it started in. -/
theorem accretes_of_persists {U : Mem ι V → Mem ι V} {R : ℕ → Set ι} {Ω : ℕ → Set (Mem ι V)}
    {decode : ℕ → Mem ι V → M} (hf : ∀ t, Faithful (decode t) (R t))
    (hpers : ∀ t, ∀ s ∈ Ω t, decode t (U s) = decode t s) :
    Accretes U R Ω :=
  fun t s hs a ha => (hf t (U s) s).mp (hpers t s hs) a ha

/-- **The Decoupling equivalence on a growing code region** ([Inevitability] §6, the accretive
extension). For a staged faithful reading of a monotonically growing region under a stage-advancing
update: the update accretes — is read-only, at every stage, on everything written so far — **iff**
each stage's model persists across every iteration along that stage's orbits.

Forward is `accretive_persists`; backward is `accretes_of_persists`, reading persistence at `k = 1`.
[Decoupling] §3, Proposition 3.4 is the constant-family case, which
`accretive_iff_persists_on_const` derives from this statement. -/
theorem accretive_decoupling_iff {U : Mem ι V → Mem ι V} {R : ℕ → Set ι} {Ω : ℕ → Set (Mem ι V)}
    {decode : ℕ → Mem ι V → M} (hR : Monotone R) (hadv : Advances U Ω)
    (hf : ∀ t, Faithful (decode t) (R t)) :
    Accretes U R Ω ↔ ∀ t, ∀ s ∈ Ω t, ∀ k, decode t (U^[k] s) = decode t s := by
  constructor
  · intro hacc t s hs k
    exact accretive_persists hR hadv hacc (fun u => (hf u).dependsOn) t k s hs
  · intro hpers
    refine accretes_of_persists hf fun t s hs => ?_
    have h1 := hpers t s hs 1
    rwa [Function.iterate_one] at h1

/-- Coherence: **the fixed-partition lemma is the degenerate case**. Instantiating
`accretive_decoupling_iff` at the constant family (`R t = R`, `Ω t = Ω`) reproduces [Decoupling] §3,
Proposition 3.4 exactly — the stage index becomes vacuous and `Advances` becomes update-closure.
[Inevitability] §6 asserts this; here it is a theorem. -/
theorem accretive_iff_persists_on_const {U : Mem ι V → Mem ι V} {R : Set ι} {Ω : Set (Mem ι V)}
    {decode : Mem ι V → M} (hf : Faithful decode R) (hΩ : ∀ s ∈ Ω, U s ∈ Ω) :
    (∀ s ∈ Ω, ∀ a ∈ R, U s a = s a) ↔ (∀ s ∈ Ω, ∀ k, decode (U^[k] s) = decode s) := by
  have h := accretive_decoupling_iff (U := U) (R := fun _ => R) (Ω := fun _ => Ω)
    (decode := fun _ => decode) monotone_const (fun _ s hs => hΩ s hs) (fun _ => hf)
  exact ⟨fun hfix s hs k => h.mp (fun _ => hfix) 0 s hs k,
    fun hpers => h.mpr (fun _ => hpers) 0⟩

/-! ## A strictly growing instance

Everything above is satisfied by the constant family, under which it collapses to the
fixed-partition lemma. The instance below is what makes the extension say something new: an
**append-only tape**.

Cell `0` holds the stage counter; cells `1, 2, …` are the code. One update bumps the counter and
writes the single fresh cell just past the written region. So the region written by stage `t` is
`{1, …, t}`, it grows strictly at every stage, the admitted states `{s | s 0 = t}` are pairwise
disjoint across stages, and the update is read-only on everything already written — while the
**limit** region `{a | 1 ≤ a}` is not read-only at any stage, since that is where the writing goes.
-/

section GrowingCode

/-- The append-only update: bump the stage counter in cell `0`, and write the one fresh cell just
past the written region. -/
def tapeWrite (s : Mem ℕ ℕ) : Mem ℕ ℕ :=
  fun a => if a = 0 then s 0 + 1 else if a = s 0 + 1 then 1 else s a

/-- The code written by stage `t`: cells `1, …, t`. -/
def tapeRegion (t : ℕ) : Set ℕ := {a | 1 ≤ a ∧ a ≤ t}

/-- The states stage `t` admits: those whose counter reads `t`. -/
def tapeStage (t : ℕ) : Set (Mem ℕ ℕ) := {s | s 0 = t}

/-- Reading the code written by stage `t`: the written cells, and a canonical value elsewhere. -/
def tapeDecode (t : ℕ) (s : Mem ℕ ℕ) : ℕ → ℕ := fun a => if 1 ≤ a ∧ a ≤ t then s a else 0

/-- The limit region: every cell the tape will ever write. -/
def tapeLimit : Set ℕ := {a | 1 ≤ a}

theorem mem_tapeRegion {a t : ℕ} : a ∈ tapeRegion t ↔ 1 ≤ a ∧ a ≤ t := Iff.rfl

theorem mem_tapeStage {s : Mem ℕ ℕ} {t : ℕ} : s ∈ tapeStage t ↔ s 0 = t := Iff.rfl

/-- The code region grows. -/
theorem tapeRegion_monotone : Monotone tapeRegion :=
  fun _ _ htu _ ha => ⟨ha.1, ha.2.trans htu⟩

/-- The code region grows **strictly**: stage `t + 1` writes cell `t + 1`, which stage `t` had
not. Without this the instance would be the constant family in disguise. -/
theorem tapeRegion_ssubset (t : ℕ) : tapeRegion t ⊂ tapeRegion (t + 1) :=
  (Set.ssubset_iff_of_subset (tapeRegion_monotone (Nat.le_succ t))).mpr
    ⟨t + 1, ⟨by omega, le_refl _⟩, fun h => absurd h.2 (by omega)⟩

/-- The stages are genuinely distinct: no state is admitted by two consecutive stages. -/
theorem tapeStage_disjoint (t : ℕ) : ∀ s ∈ tapeStage t, s ∉ tapeStage (t + 1) := by
  intro s hs hs'
  rw [mem_tapeStage] at hs hs'
  omega

/-- The update advances the stage: writing bumps the counter. -/
theorem advances_tapeWrite : Advances tapeWrite tapeStage := by
  intro t s hs
  rw [mem_tapeStage] at hs ⊢
  simp [tapeWrite, hs]

/-- The update accretes: at stage `t` it touches only the counter and the fresh cell `t + 1`, both
outside the written region `{1, …, t}`. -/
theorem accretes_tapeWrite : Accretes tapeWrite tapeRegion tapeStage := by
  intro t s hs a ha
  rw [mem_tapeStage] at hs
  rw [mem_tapeRegion] at ha
  simp only [tapeWrite]
  rw [ite_eq_right (by omega), ite_eq_right (by omega)]

/-- Each stage's reading is faithful on that stage's region: it separates exactly the written
cells. -/
theorem faithful_tapeDecode (t : ℕ) : Faithful (tapeDecode t) (tapeRegion t) := by
  refine fun s s' => ⟨fun h a ha => ?_, fun h => ?_⟩
  · rw [mem_tapeRegion] at ha
    have hc := congrFun h a
    simpa only [tapeDecode, ite_eq_left ha] using hc
  · funext a
    simp only [tapeDecode]
    by_cases ha : 1 ≤ a ∧ a ≤ t
    · rw [ite_eq_left ha, ite_eq_left ha]
      exact h a (mem_tapeRegion.mpr ha)
    · rw [ite_eq_right ha, ite_eq_right ha]

/-- The limit region is exactly the union of the stages' regions. -/
theorem tapeLimit_eq_iUnion : tapeLimit = {a | ∃ t, a ∈ tapeRegion t} := by
  ext a
  simp only [tapeLimit, mem_tapeRegion, Set.mem_ofPred_eq]
  exact ⟨fun h => ⟨a, h, le_refl a⟩, fun ⟨_, h, _⟩ => h⟩

/-- **The union of the regions is not read-only.** So the accretive statement is *not* recoverable
by applying the fixed-partition lemma once to the limit region: the frontier is where the writing
happens, and it belongs to the limit. The stage-indexed family is doing real work — even though its
proof reduces, stage by stage, to the fixed-partition machinery. -/
theorem not_accretes_tapeLimit : ¬ Accretes tapeWrite (fun _ => tapeLimit) tapeStage := by
  intro h
  have h1 := h 0 (fun _ => 0) (mem_tapeStage.mpr rfl) 1 (le_refl 1)
  simp [tapeWrite] at h1

/-- Heredity on the instance: the code written by stage `t` reads back unchanged forever. -/
theorem tapeDecode_hereditary (t k : ℕ) (s : Mem ℕ ℕ) (hs : s ∈ tapeStage t) :
    tapeDecode t (tapeWrite^[k] s) = tapeDecode t s :=
  accretive_persists tapeRegion_monotone advances_tapeWrite accretes_tapeWrite
    (fun u => (faithful_tapeDecode u).dependsOn) t k s hs

/-- **The accretive extension is non-degenerate**: there is a growing host on which every hypothesis
holds, the region grows strictly at every stage, the stages are pairwise distinct, the staged
reading is faithful — and the limit region is *not* read-only, so no single fixed partition
reproduces the conclusion. -/
theorem exists_strictly_accretive_decoupling :
    ∃ (ι V M : Type) (U : Mem ι V → Mem ι V) (R : ℕ → Set ι) (Ω : ℕ → Set (Mem ι V))
      (decode : ℕ → Mem ι V → M),
      Monotone R ∧ (∀ t, R t ⊂ R (t + 1)) ∧ (∀ t, ∀ s ∈ Ω t, s ∉ Ω (t + 1)) ∧
        Advances U Ω ∧ Accretes U R Ω ∧ (∀ t, Faithful (decode t) (R t)) ∧
        ¬ Accretes U (fun _ => {a | ∃ u, a ∈ R u}) Ω :=
  ⟨ℕ, ℕ, ℕ → ℕ, tapeWrite, tapeRegion, tapeStage, tapeDecode,
    tapeRegion_monotone, tapeRegion_ssubset, tapeStage_disjoint,
    advances_tapeWrite, accretes_tapeWrite, faithful_tapeDecode,
    by rw [← tapeLimit_eq_iUnion]; exact not_accretes_tapeLimit⟩

end GrowingCode

/-! ## An arbitrary committed stream

`tapeWrite` commits a single fixed symbol, `1`, at each stage. `seqWrite` generalizes it to commit
an arbitrary stream `c : ℕ → ℕ`, one entry per stage — [Inevitability] §6, Proposition 6.2's first
theorem consumer. `tapeRegion`, `tapeStage` and `tapeDecode` never mention what was written, only
where, so they are reused verbatim; only the write itself changes. What survives is exactly what
Proposition 6.2 gives: every committed cell held under every later step, at a footprint equal to
the stream's own prefix length. What the stream's entries *are* — successive law-codes, or how they
are chosen — is paper-side, not claimed here.
-/

section SequentialCommit

variable (c : ℕ → ℕ)

/-- Commit stream `c`, one entry per stage: bump the counter in cell `0`, write `c`'s `s 0`-th entry
at the fresh cell just past the written region, and leave every other cell alone. Reduces to
`tapeWrite` at the constant stream `fun _ => 1`. -/
def seqWrite (c : ℕ → ℕ) (s : Mem ℕ ℕ) : Mem ℕ ℕ :=
  fun a => if a = 0 then s 0 + 1 else if a = s 0 + 1 then c (s 0) else s a

/-- The blank state before any commitment: counter `0`, every cell `0`. -/
def seqStart : Mem ℕ ℕ := fun _ => 0

/-- `seqWrite c` advances the stage exactly as `tapeWrite` does: the counter bump does not depend
on what is written. -/
theorem advances_seqWrite : Advances (seqWrite c) tapeStage := by
  intro t s hs
  rw [mem_tapeStage] at hs ⊢
  simp [seqWrite, hs]

/-- `seqWrite c` accretes on the same region as `tapeWrite`, by the same argument: at stage `t` it
touches only the counter and the fresh cell `t + 1`, both outside `{1, …, t}`. -/
theorem accretes_seqWrite : Accretes (seqWrite c) tapeRegion tapeStage := by
  intro t s hs a ha
  rw [mem_tapeStage] at hs
  rw [mem_tapeRegion] at ha
  simp only [seqWrite]
  rw [ite_eq_right (by omega), ite_eq_right (by omega)]

/-- The canonical run from the blank state: after `t` commitments the counter reads `t`, and cell
`a` holds the `(a - 1)`-th entry of `c` for every written cell `1 ≤ a ≤ t`, `0` elsewhere. -/
theorem seqWrite_iterate_seqStart (t : ℕ) :
    (seqWrite c)^[t] seqStart =
      fun a => if a = 0 then t else if 1 ≤ a ∧ a ≤ t then c (a - 1) else 0 := by
  induction t with
  | zero => funext a; simp only [Function.iterate_zero_apply, seqStart]; split_ifs <;> omega
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih]
    funext a
    simp only [seqWrite]
    split_ifs with h1 h2 h3 h4 h5 h6 <;> first | omega | (congr 1; omega)

/-- The canonical run lands in stage `t`, so `accretive_persists` applies to it. -/
theorem mem_tapeStage_seqWrite_iterate (t : ℕ) : (seqWrite c)^[t] seqStart ∈ tapeStage t := by
  rw [mem_tapeStage, seqWrite_iterate_seqStart]
  simp

/-- **The committing substrate** ([Inevitability] §6, Proposition 6.2's first theorem consumer):
every symbol `seqWrite` commits is held under every later commitment, forever. For every stage `t`
and every later step `k`, the reading of the code region written by stage `t` is exactly the
stream's own prefix — cell `a` holds `c (a - 1)` for `1 ≤ a ≤ t`, `0` elsewhere — no matter how many
further commitments have since been made.

Proof: `accretive_persists` at the canonical run, `(seqWrite c)^[t] seqStart`, which
`mem_tapeStage_seqWrite_iterate` places in stage `t`; the run identification then evaluates both
sides. This is the accretive equivalence consumed, not reproved — everything about *what* the
stream commits, or how, stays outside this file. -/
theorem seqDecode_hereditary (t k : ℕ) :
    tapeDecode t ((seqWrite c)^[t + k] seqStart) =
      fun a => if 1 ≤ a ∧ a ≤ t then c (a - 1) else 0 := by
  have hstage := mem_tapeStage_seqWrite_iterate c t
  have hpersist := accretive_persists tapeRegion_monotone (advances_seqWrite c)
    (accretes_seqWrite c) (fun u => (faithful_tapeDecode u).dependsOn) t k _ hstage
  rw [show t + k = k + t from by omega, Function.iterate_add_apply, hpersist,
    seqWrite_iterate_seqStart]
  funext a
  simp only [tapeDecode]
  split_ifs with h1 h2 <;> first | rfl | omega

/-- **The committed footprint is exactly the prefix length**: the region held permanently after `t`
commitments is in bijection with `Fin t` — `t` cells, with no slack. -/
theorem tapeRegion_bijective (t : ℕ) :
    Set.BijOn (fun i : Fin t => (i : ℕ) + 1) Set.univ (tapeRegion t) := by
  refine ⟨fun i _ => ?_, fun i _ j _ hij => ?_, fun a ha => ?_⟩
  · rw [mem_tapeRegion]
    have := i.isLt
    simp only
    omega
  · simp only at hij
    exact Fin.ext (by omega)
  · rw [mem_tapeRegion] at ha
    refine ⟨⟨a - 1, by omega⟩, Set.mem_univ _, ?_⟩
    simp only
    omega

end SequentialCommit

end Decoupling
