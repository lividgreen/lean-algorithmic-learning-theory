/-
Copyright (c) 2026 Mykola Palamarchuk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mykola Palamarchuk
-/
import ALT.GrowingWorld
import ALT.PersistenceCapacity

-- Formal-check file, not Mathlib-destined: opt out of the house-style header linter.
set_option linter.style.header false

/-!
# The accreting healer world: the escape witness's skeleton
([Guests] §3 + §5, §7 Theorem 7.5)

`GrowingWorld.lean` states the staged square a guest of a growing host must close
([Inevitability] §6); this file builds the instance that closes it while keeping [Guests] §5's
robustness margin across every growth event. The carrier is a growing list of
`PersistenceCapacity.healWorld`'s recursive-majority habitats beside a turning environment; the
update heals every habitat block, appends one fresh block already at its zero codeword, and turns
the environment — so accretion writes a constant block, and the stage is the state's own block
count rather than a separate counter a perturbation could corrupt. The reading is one uniform
family, majority-decoding every block; the guest's own law appends `false` to the decoded word.

## Main results

* `accUpdate` / `accStage` / `advances_accUpdate` — the carrier and its stage-advancing update.
* `accRead` / `accLaw` / `stagedSquare_accRead` — **the staged square, from every state, with no
  codeword hypothesis**: both closing identities reduce to `PersistenceCapacity.decRec_encRec`'s
  roundtrip — decoding a healed block is decoding the block, and the appended block decodes to
  `false`.
* `accCode` / `accErasure` — **the staged margin, as one-step erasure** ([Guests] §3): a codeword
  state absorbs any perturbation totalling fewer than `2 ^ k` flipped habitat cells in one step,
  landing on the exact same update as the unperturbed state — `PersistenceCapacity.healWorld_heals`
  applied block by block, the margin profile constantly `≥ 2 ^ k − 1` across every accretion event.
* `guestStage_accRead_eq` / `ncard_guestStage_accRead` — **the extent**: the guest's stage-`t`
  reading is exactly the length-`(t + 1)` Boolean words, carrying exactly `2 ^ (t + 1)` values —
  strictly growing without bound.

## Scope

Same shared-memory algebra as `GrowingWorld.lean` and the same recursive-majority healer as
`PersistenceCapacity.lean`, and nothing more: no description-length pricing, no ownership claim,
and no internalization-threshold crossing ([Guests] §5, clause (iv)) — that needs a carrier bridge
from list words to fixed-length words and is a separate target.
-/

namespace AccretingWitness

open Decoupling PersistenceCapacity

variable {ι_J : Type*}

/-! ## Carrier, update, stages -/

/-- The habitat blocks (each a depth-`k` healing habitat, `3 ^ k` cells) beside the turning
environment. The update below appends on every step, so the stage is this list's own length — no
separate schedule counter for a perturbation to exploit. -/
def accUpdate (k : ℕ) (π : Mem ι_J Bool → Mem ι_J Bool) :
    List (Mem (Fin (3 ^ k)) Bool) × Mem ι_J Bool →
      List (Mem (Fin (3 ^ k)) Bool) × Mem ι_J Bool :=
  fun s => (s.1.map (healWorld k) ++ [encRec k false], π s.2)

/-- The states admitted at stage `t`: exactly `t + 1` habitat blocks — one block at stage zero, so
the habitat is never empty. -/
def accStage (k : ℕ) (t : ℕ) : Set (List (Mem (Fin (3 ^ k)) Bool) × Mem ι_J Bool) :=
  {s | s.1.length = t + 1}

/-- The update advances the stage: appending lengthens the habitat by exactly one block. -/
theorem advances_accUpdate (k : ℕ) (π : Mem ι_J Bool → Mem ι_J Bool) :
    GrowingWorld.Advances (accUpdate k π) (accStage k) := by
  intro t s hs
  have hs' : s.1.length = t + 1 := hs
  change (accUpdate k π s).1.length = t + 1 + 1
  simp [accUpdate, hs']

/-! ## The square, from every state -/

/-- The reading: majority-decode every habitat block. Time-independent — constant in `t`, since
nothing about a block's decode depends on how many other blocks accompany it. -/
def accRead (k : ℕ) (_t : ℕ) (s : List (Mem (Fin (3 ^ k)) Bool) × Mem ι_J Bool) : List Bool :=
  s.1.map (decRec k)

/-- The guest's own law: append `false`, matching the fresh zero-codeword block the update appends.
-/
def accLaw : List Bool → List Bool := fun m => m ++ [false]

/-- Decoding a healed block is decoding the block — the healer's roundtrip
(`PersistenceCapacity.decRec_encRec`), unfolded through `healWorld`'s own definition. -/
private theorem decRec_healWorld_eq (k : ℕ) (x : Mem (Fin (3 ^ k)) Bool) :
    decRec k (healWorld k x) = decRec k x := by
  change decRec k (encRec k (decRec k x)) = decRec k x
  exact decRec_encRec k (decRec k x)

/-- A codeword is already healed: the healer fixes it. -/
private theorem healWorld_encRec_eq (k : ℕ) (b : Bool) :
    healWorld k (encRec k b) = encRec k b := by
  change encRec k (decRec k (encRec k b)) = encRec k b
  rw [decRec_encRec]

/-- **The staged square, from every state, with no codeword hypothesis**: one host step, read one
stage later, is the guest law applied to the current reading. Both closing identities are
`decRec_encRec`'s roundtrip: healing a block does not move its decode, and the appended block
decodes to `false`. -/
theorem stagedSquare_accRead (k : ℕ) (π : Mem ι_J Bool → Mem ι_J Bool) :
    GrowingWorld.StagedSquare (accUpdate k π) accLaw (accRead k) (accStage k) := by
  intro t s _
  show accRead k (t + 1) (accUpdate k π s) = accLaw (accRead k t s)
  simp only [accRead, accUpdate, accLaw, List.map_append, List.map_map, List.map_singleton,
    decRec_encRec]
  congr 1
  exact List.map_congr_left (fun x _ => decRec_healWorld_eq k x)

/-! ## The staged margin -/

/-- The codeword states at stage `t`: every habitat block is a codeword. -/
def accCode (k t : ℕ) : Set (List (Mem (Fin (3 ^ k)) Bool) × Mem ι_J Bool) :=
  {s | s ∈ accStage k t ∧ ∃ m : List Bool, s.1 = m.map (encRec k)}

/-- The block-by-block healing argument, generalized over a pair of habitats of matching length:
a total flip budget under `2 ^ k`, split across blocks pointwise by the healing lemma applied to
each perturbed block against its own (already-healed) codeword. -/
private theorem healWorld_map_eq_of_sum_lt {k : ℕ} :
    ∀ (l l' : List (Mem (Fin (3 ^ k)) Bool)) (m : List Bool),
      l = m.map (encRec k) → l'.length = l.length →
      (List.zipWith hammingDist l' l).sum < 2 ^ k →
      l'.map (healWorld k) = l.map (healWorld k) := by
  intro l
  induction l with
  | nil =>
    intro l' m hl hlen _
    have hl' : l' = [] := List.length_eq_zero_iff.mp (by simpa using hlen)
    simp [hl']
  | cons hd tl ih =>
    intro l' m hl hlen hsum
    cases m with
    | nil => simp at hl
    | cons mb mtl =>
      simp only [List.map_cons, List.cons.injEq] at hl
      obtain ⟨hhd, htl⟩ := hl
      cases l' with
      | nil =>
        simp only [List.length_nil, List.length_cons] at hlen
        omega
      | cons hd' tl' =>
        simp only [List.length_cons] at hlen
        have hlen' : tl'.length = tl.length := by omega
        simp only [List.zipWith_cons_cons, List.sum_cons] at hsum
        have hhd_sum : hammingDist hd' hd < 2 ^ k := by omega
        have htl_sum : (List.zipWith hammingDist tl' tl).sum < 2 ^ k := by omega
        have hmapheal : tl'.map (healWorld k) = tl.map (healWorld k) :=
          ih tl' mtl htl hlen' htl_sum
        have hhdheal : healWorld k hd' = healWorld k hd := by
          rw [hhd, healWorld_heals k hd' mb (by rw [hhd] at hhd_sum; exact hhd_sum),
            healWorld_encRec_eq]
        rw [List.map_cons, List.map_cons, hhdheal, hmapheal]

/-- **The staged margin, as one-step erasure** ([Guests] §3, §7 Theorem 7.5): from a
codeword state at stage `t`,
any habitat perturbation totalling fewer than `2 ^ k` flipped cells — same length, same environment
— is erased in one step: the update lands on the exact same next state. Every habitat block absorbs
at most the total budget, so each individually stays within the healing radius
(`PersistenceCapacity.healWorld_heals`), and the perturbed and unperturbed blocks heal to the same
codeword. The margin profile this witnesses is constantly `≥ 2 ^ k − 1`, accretion events included,
by the fixed healer's own argument applied per block — no protected schedule coordinate is needed,
since the stage is the habitat's own length. -/
theorem accErasure (k : ℕ) (π : Mem ι_J Bool → Mem ι_J Bool) (t : ℕ)
    {s : List (Mem (Fin (3 ^ k)) Bool) × Mem ι_J Bool} (hs : s ∈ accCode k t)
    {s' : List (Mem (Fin (3 ^ k)) Bool) × Mem ι_J Bool} (hlen : s'.1.length = s.1.length)
    (henv : s'.2 = s.2) (hsum : (List.zipWith hammingDist s'.1 s.1).sum < 2 ^ k) :
    accUpdate k π s' = accUpdate k π s := by
  obtain ⟨-, m, hm⟩ := hs
  have hmap : s'.1.map (healWorld k) = s.1.map (healWorld k) :=
    healWorld_map_eq_of_sum_lt s.1 s'.1 m hm hlen hsum
  simp only [accUpdate]
  rw [hmap, henv]

/-! ## The extent -/

/-- The guest's stage-`t` extent is exactly the length-`(t + 1)` Boolean words: every such word is
read off the state encoding it block by block, and every reading has that length by construction. -/
theorem guestStage_accRead_eq (ι_J : Type*) (k t : ℕ) :
    GrowingWorld.guestStage (accRead (ι_J := ι_J) k) (accStage k) t =
      {L : List Bool | L.length = t + 1} := by
  apply Set.eq_of_subset_of_subset
  · rintro _ ⟨s, hs, rfl⟩
    have hs' : s.1.length = t + 1 := hs
    simp [accRead, hs']
  · intro L hL
    have hL' : L.length = t + 1 := hL
    refine ⟨(L.map (encRec k), fun _ => false), ?_, ?_⟩
    · change (L.map (encRec k)).length = t + 1
      simpa using hL'
    · change (L.map (encRec k)).map (decRec k) = L
      rw [List.map_map]
      have hid : decRec k ∘ encRec k = (id : Bool → Bool) := funext (decRec_encRec k)
      rw [hid, List.map_id]

/-- **The extent, counted**: the guest's stage-`t` extent carries exactly `2 ^ (t + 1)` values —
strictly growing without bound, via the bijection with `Fin (t + 1) → Bool` (the `GrowingWorld.lean`
counting pattern, here over `List.ofFn`). -/
theorem ncard_guestStage_accRead (ι_J : Type*) (k t : ℕ) :
    (GrowingWorld.guestStage (accRead (ι_J := ι_J) k) (accStage k) t).ncard = 2 ^ (t + 1) := by
  rw [guestStage_accRead_eq]
  have himg :
      (List.ofFn '' (Set.univ : Set (Fin (t + 1) → Bool))) = {L : List Bool | L.length = t + 1} :=
    Set.Subset.antisymm
      (by rintro _ ⟨f, -, rfl⟩; exact List.length_ofFn)
      (fun L hL => ⟨fun i => L[(Fin.cast hL.symm i).val], Set.mem_univ _, by
        rw [← List.ofFn_congr hL (fun i : Fin L.length => L[i.val])]
        exact List.ofFn_getElem⟩)
  rw [← himg, Set.ncard_image_of_injective _ List.ofFn_injective, Set.ncard_univ]
  simp [Nat.card_eq_fintype_card]

end AccretingWitness
