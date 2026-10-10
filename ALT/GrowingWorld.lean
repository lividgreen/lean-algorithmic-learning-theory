/-
Copyright (c) 2026 Mykola Palamarchuk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mykola Palamarchuk
-/
module

public import CellularAutomata.MergeQuotient
public import ALT.AccretiveDecoupling
public import ALT.PersistenceCapacity

-- Formal-check file, not Mathlib-destined: opt out of the house-style header linter.
set_option linter.style.header false

/-!
# The growing-world skeleton: staged squares, factor closure, and a tape's guest
([Guests] §2 objects over [Inevitability] §6's stage machinery; [Guests] §7)

A **guest** of a world is a factor: a law of its own, reached by a reading that intertwines the
host's step with it ([Guests] §2, Definitions 2.1–2.3). `[Inevitability]` §6's ratchet needs that
notion over a *growing* host — a world whose stages `Ω : ℕ → Set X` only ever admit more, via
`Advances` ([Inevitability] §6 Proposition 6.2, `AccretiveDecoupling.lean`) — and asks whether the
class of guests is closed under growth in the same sense.

This file states the staged square that answers that at arbitrary carrier types, proves the factor
closure it exists for, identifies the fixed-carrier degenerate case with
`PersistenceCapacity.Intertwines` ([Persistence] §10.2), and stress-tests both against
`AccretiveDecoupling.lean`'s append-only tape: the counter-free reading `tapeDecode` admits **no**
guest law over the full stages at all, while a reading that also carries the counter does, with a
strictly growing extent.

## Main results

* `Advances` — the general-carrier form of the root-namespace `Decoupling.Advances`
  (`AccretiveDecoupling.lean`); `advances_iff` is the coherence theorem that the two agree at
  `Mem ι V`, by `Iff.rfl`.
* `StagedSquare` — the staged form of `PersistenceCapacity.Intertwines`: one host step, read one
  stage later, is the guest's own law applied to the current reading.
* `guestStage` — a guest's stage-`t` extent, the image of the host's stage `t` under the reading.
* `advances_guestStage` — **factor closure**, the module's reason to exist: a guest of a growing
  world is itself a growing world, its stages advancing under the guest's own law.
* `stagedSquare_const_iff` — **coherence with the fixed-carrier form**: at the constant stage
  family, `StagedSquare` is exactly `PersistenceCapacity.Intertwines`.
* `not_exists_stagedSquare_tapeDecode` — **the guard**: over the tape's full stages, the
  counter-free reading `Decoupling.tapeDecode` admits no guest law at all. This is what makes the
  counter-including reading below a theorem rather than a taste.
* `tapeRead` / `stagedSquare_tapeRead` — the counter-including reading, and the staged square it
  closes with the tape's own write law as the guest law.
* `tapeStageB` / `advances_tapeStageB` — the binary-content sub-stages, and their own advance under
  the write law.
* `ncard_guestStage_tapeStageB` — **strictly growing extent**: the guest's stage-`t` extent over
  the binary sub-stages has exactly `2 ^ t` elements. On these stages `tapeRead` turns out to be the
  identity — a stage state already looks like its own reading — so the extent is `tapeStageB t`
  itself, counted by an explicit bijection with `Fin t → Bool`.

## Scope

Same shared-memory algebra as `AccretiveDecoupling.lean` and nothing more: the two imports are its
stage-indexed hypotheses and the tape instance, and `PersistenceCapacity.Intertwines` for the
constant-family coherence theorem. No description-length pricing, no ownership, no claim that any
guest here is *owned* in `[Guests]` §2's sense — this file is the factor-closure skeleton the
priced notion sits on, not the priced notion itself.
`Advances`, `StagedSquare`, `guestStage` and `advances_guestStage` are stated in
`MergeQuotient.lean`, which imports nothing of this development, under the namespace
`GrowingWorld`.
-/


@[expose] public section

namespace GrowingWorld

variable {X M : Type*}

/-- **Coherence**: at the shared-memory carrier `Mem ι V`, the root-namespace `Decoupling.Advances`
(`AccretiveDecoupling.lean`) and this file's general-carrier `Advances` are the same hypothesis,
definitionally. -/
theorem advances_iff {ι V : Type*} (U : Decoupling.Mem ι V → Decoupling.Mem ι V)
    (Ω : ℕ → Set (Decoupling.Mem ι V)) : Decoupling.Advances U Ω ↔ Advances U Ω := Iff.rfl

/-! ## The constant case: coherence with `Intertwines` -/

/-- **Coherence with the fixed-carrier form**: at the constant stage family, the staged square is
exactly `PersistenceCapacity.Intertwines` ([Persistence] §10.2) — the stage-indexed hypothesis
becomes vacuous and the reading's own time-indexing carries the whole content, as it already does
there. -/
theorem stagedSquare_const_iff {U : X → X} {F : M → M} {ℓ : ℕ → X → M} :
    StagedSquare U F ℓ (fun _ => Set.univ) ↔ PersistenceCapacity.Intertwines U F ℓ :=
  ⟨fun h t s => h t s (Set.mem_univ s), fun h t s _ => h t s⟩

/-! ## The tape's guest -/

/-- **The guard**: over the tape's full stages (`Decoupling.tapeStage`), the counter-free reading
`Decoupling.tapeDecode` admits **no** guest law at all. Two states admitted at different counters
— `t = 0` with every cell zero, and `t = 1` with every written cell (there are none yet, cell `1`
is unwritten) also zero — read identically, since neither has a written cell for `tapeDecode` to
show. The square then forces the guest law to send that one reading to two different values: the
fresh `1` the write law places lands at cell `1` from the first state and at cell `2` from the
second. This is what makes the counter-including reading below a theorem rather than a taste. -/
theorem not_exists_stagedSquare_tapeDecode :
    ¬ ∃ F : (ℕ → ℕ) → ℕ → ℕ,
      StagedSquare Decoupling.tapeWrite F Decoupling.tapeDecode Decoupling.tapeStage := by
  rintro ⟨F, hF⟩
  have h0 : (fun _ : ℕ => (0 : ℕ)) ∈ Decoupling.tapeStage 0 := rfl
  have h1 : (fun a : ℕ => if a = 0 then (1 : ℕ) else 0) ∈ Decoupling.tapeStage 1 := rfl
  have hzero : Decoupling.tapeDecode 0 (fun _ => 0) =
      Decoupling.tapeDecode 1 (fun a => if a = 0 then (1 : ℕ) else 0) := by
    funext a
    simp only [Decoupling.tapeDecode]
    split_ifs with ha ha' <;> omega
  have e0 := hF 0 (fun _ => 0) h0
  have e1 := hF 1 (fun a => if a = 0 then (1 : ℕ) else 0) h1
  rw [hzero, ← e1] at e0
  have hval := congrFun e0 1
  simp only [Decoupling.tapeWrite, Decoupling.tapeDecode] at hval
  norm_num at hval

/-- **The counter-including reading**: unlike `Decoupling.tapeDecode`, it also reports the stage
counter at cell `0`. -/
def tapeRead (t : ℕ) (s : Decoupling.Mem ℕ ℕ) : Decoupling.Mem ℕ ℕ :=
  fun a => if a = 0 then s 0 else if 1 ≤ a ∧ a ≤ t then s a else 0

/-- **The square the counter buys**: with the counter included in the reading, the tape's own
write law closes the staged square against itself — the decoded table's step is the decode of the
host's step, cell by cell. -/
theorem stagedSquare_tapeRead :
    StagedSquare Decoupling.tapeWrite Decoupling.tapeWrite tapeRead Decoupling.tapeStage := by
  intro t s hs
  have hs0 : s 0 = t := Decoupling.mem_tapeStage.mp hs
  funext a
  simp only [tapeRead, Decoupling.tapeWrite, hs0]
  split_ifs <;> omega

/-- `StagedSquare` is antitone in the admitted stages: restricting to a subfamily costs nothing. -/
private theorem stagedSquare_antitone {U : X → X} {F : M → M} {ℓ : ℕ → X → M} {Ω Ω' : ℕ → Set X}
    (hΩ : ∀ t, Ω' t ⊆ Ω t) (h : StagedSquare U F ℓ Ω) : StagedSquare U F ℓ Ω' :=
  fun t s hs => h t s (hΩ t hs)

/-- **Binary stages**: the sub-stages of `Decoupling.tapeStage` whose written cells all carry `0`
or `1`. The extent theorem below is stated over these — the full stages carry no bound on cell
content at all, so they have no finite extent to count. -/
def tapeStageB (t : ℕ) : Set (Decoupling.Mem ℕ ℕ) :=
  {s | s 0 = t ∧ (∀ a, 1 ≤ a → a ≤ t → s a ≤ 1) ∧ ∀ a, t < a → s a = 0}

private theorem tapeStageB_subset_tapeStage (t : ℕ) : tapeStageB t ⊆ Decoupling.tapeStage t :=
  fun _ hs => Decoupling.mem_tapeStage.mpr hs.1

/-- The write law carries the binary sub-stages into the binary sub-stages: the fresh cell gets
`1`, and the accretive discipline keeps every other cell as it was. -/
theorem advances_tapeStageB : Advances Decoupling.tapeWrite tapeStageB := by
  rintro t s ⟨h0, hbin, hzero⟩
  refine ⟨?_, ?_, ?_⟩
  · simp [Decoupling.tapeWrite, h0]
  · intro a ha1 ha2
    simp only [Decoupling.tapeWrite]
    rw [ite_eq_right (by omega : a ≠ 0)]
    by_cases hb : a = s 0 + 1
    · simp [hb]
    · rw [ite_eq_right hb]
      exact hbin a ha1 (by omega)
  · intro a ha
    simp only [Decoupling.tapeWrite]
    rw [ite_eq_right (by omega : a ≠ 0), ite_eq_right (by rw [h0]; omega : a ≠ s 0 + 1)]
    exact hzero a (by omega)

/-- On the binary sub-stages, `tapeRead` is the identity: a stage state already looks like its own
reading, since it already carries its own counter at cell `0` and reads as `0` past `t` — the same
fact `tapeStageB`'s own third conjunct states. -/
private theorem tapeRead_eq_self_of_mem_tapeStageB {t : ℕ} {s : Decoupling.Mem ℕ ℕ}
    (hs : s ∈ tapeStageB t) : tapeRead t s = s := by
  obtain ⟨-, -, hzero⟩ := hs
  funext a
  simp only [tapeRead]
  split_ifs with ha0 hrange
  · rw [ha0]
  · rfl
  · exact (hzero a (by omega)).symm

/-- So the guest's stage-`t` extent over the binary sub-stages is the sub-stage itself. -/
private theorem guestStage_tapeStageB_eq (t : ℕ) :
    guestStage tapeRead tapeStageB t = tapeStageB t := by
  apply Set.eq_of_subset_of_subset
  · rintro _ ⟨s, hs, rfl⟩
    rwa [tapeRead_eq_self_of_mem_tapeStageB hs]
  · intro s hs
    exact ⟨s, hs, tapeRead_eq_self_of_mem_tapeStageB hs⟩

/-- Encodes a binary table on cells `1, …, t` as a stage-`t` binary tape state. -/
def encode (t : ℕ) (f : Fin t → Bool) : Decoupling.Mem ℕ ℕ :=
  fun a => if a = 0 then t else
    if h : 1 ≤ a ∧ a ≤ t then (f ⟨a - 1, by omega⟩).toNat else 0

theorem encode_mem (t : ℕ) (f : Fin t → Bool) : encode t f ∈ tapeStageB t := by
  refine ⟨by simp [encode], ?_, ?_⟩
  · intro a ha1 ha2
    simp only [encode, ite_eq_right (show a ≠ 0 by omega),
      dite_eq_left (⟨ha1, ha2⟩ : 1 ≤ a ∧ a ≤ t)]
    cases f ⟨a - 1, by omega⟩ <;> simp [Bool.toNat]
  · intro a ha
    simp only [encode, ite_eq_right (show a ≠ 0 by omega),
      dite_eq_right (show ¬ (1 ≤ a ∧ a ≤ t) by omega)]

private theorem encode_injective (t : ℕ) : Function.Injective (encode t) := by
  intro f₁ f₂ h
  funext i
  have hi := congrFun h (i.1 + 1)
  simp only [encode, ite_eq_right (show i.1 + 1 ≠ 0 by omega),
    dite_eq_left (show 1 ≤ i.1 + 1 ∧ i.1 + 1 ≤ t by omega)] at hi
  have hfin : (⟨i.1 + 1 - 1, by omega⟩ : Fin t) = i := by
    ext; simp
  rw [hfin] at hi
  cases hb1 : f₁ i <;> cases hb2 : f₂ i <;> simp_all [Bool.toNat]

private theorem encode_surjOn (t : ℕ) : tapeStageB t ⊆ encode t '' Set.univ := by
  intro s hs
  refine ⟨fun i => decide (s (i.1 + 1) = 1), Set.mem_univ _, ?_⟩
  obtain ⟨h0, hbin, hzero⟩ := hs
  funext a
  simp only [encode]
  split_ifs with ha0 hrange
  · rw [ha0, h0]
  · have ha1 : a - 1 + 1 = a := by omega
    have hle := hbin a hrange.1 hrange.2
    simp only [ha1]
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hle with h | h <;> simp [h]
  · exact (hzero a (by omega)).symm

theorem ncard_guestStage_tapeStageB (t : ℕ) :
    (guestStage tapeRead tapeStageB t).ncard = 2 ^ t := by
  rw [guestStage_tapeStageB_eq]
  have himg : encode t '' Set.univ = tapeStageB t :=
    Set.Subset.antisymm (by rintro _ ⟨f, -, rfl⟩; exact encode_mem t f) (encode_surjOn t)
  rw [← himg, Set.ncard_image_of_injective _ (encode_injective t), Set.ncard_univ]
  simp [Nat.card_eq_fintype_card]

end GrowingWorld
