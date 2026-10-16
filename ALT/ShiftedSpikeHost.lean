module

public import ALT.ShiftedSpikeCriterion
public import ALT.Decoupling

/-!
# The lag-`6` host and witness substrate for the second certified design

The certified block-pair host (`BlockPairHost.lean`, `BlockPairWitness.lean`) carries literal `0`'s
own recursion `o u = ¬(o (u - 8)) ⊕ noise`: window width `8` and recursion lag `8` coincide, so the
window's own shift-and-complement structure (`ALT.noisyStep`, complementing window
cell `0`, the OLDEST cell) already computes it. Literal `2`'s recursion is `o u = ¬(o (u - 6)) ⊕
noise` — window width stays `8` (`[Inevitability] Definition 2.3`'s eight-literal code region), but
the lag is `6`, so the cell that must be complemented is not the oldest but window cell `2`: at
target counter `u`, `TapeHost.designWindow`'s convention "cell `i` holds the observation at
`u - 8 + i`" gives `u - 8 + i = u - 6` exactly at `i = 2`. This is the one genuinely
literal-specific layer, and it is confined to two bespoke definitions below (`windowMap2`,
`tape2`); everything else mirrors `BlockPairHost.lean`/`BlockPairWitness.lean` line for line
with the design, the modulus (`22` in place of `24`), and the loaded literal (`2` in place of `0`)
substituted.

`BlockPairHost.subUpdate`'s own window-shift branch already reads
`s (Sum.inr (Sum.inl (BlockPairHost.decodeRule M s)))` — the DECODED literal's own cell, not a
hardcoded `0` — so the witness substrate below (`subUpdate2`) needs no change to that structure at
all: loaded one-hot at `2`, `decodeRule2` reads back `2`, and the same branch automatically consults
window cell `2`. Only the correction term (`BlockPairHost.tape`, becoming `tape2`) and the loaded
code are literal-specific.

## Main results

* `tape2`, `windowMap2`, `noisyStep2`, `update2`, `designWindow2` — the lag-`6` host.
* `update2_iterate_designWindow2` — **the designed orbit**: started at its own window, the
  host's state after `t` steps is the design's window ending `t` further along, mirroring
  `TapeHost.tapeUpdate_iterate_designWindow`.
* `Idx`, `Mem`, `codeRegion2`, `decodeRule2`, `subUpdate2`, `load2`,
  `readObs2` — the witness substrate, mirroring `BlockPairWitness.lean`'s memory layout and update,
  at the modulus `2 * (2 * M) * 22` and the literal `2`.
* `readObs_iterate_load2` — **the realization theorem**: reading the substrate's own
  observation cell along its own orbit reproduces `designObs2`, pointwise.

## Scope

Deliberately out of scope, as this pair statement does not need it and [Inevitability] registers
`𝒮_L` membership only for the landed (literal-`0`) host: the membership capstone
(`BlockPairHost.witness_substrateL`'s analogue), (S1)'s witness clause
(`BlockPairHost.subUpdate_reads_code`'s analogue), and the counter's own closed-form orbit
(`BlockPairHost.readCounter_iterate_load`'s analogue) — none of these are consumed by the tower rung
this substrate feeds. Also out of scope, as `BlockPairHost.lean`'s own periodicity section is for
the certified host: the parallel-cycle theorem
(`BlockPairHost.windowXor`/`BlockPairHost.rot8`/`BlockPairHost.update_iterate_period_all`'s
analogues) — the rung witness needs only the designed orbit.
-/


@[expose] public section

namespace ALT

namespace ShiftedSpikeHost

variable (M : ℕ) [NeZero (2 * (2 * M))]

/-! ## The lag-`6` host -/

/-- The tape's own bit at `u`, at literal `2`'s own lag `6`: whether the design agrees with its
value six steps back. -/
def tape2 (u : ZMod (2 * (2 * M) * 22)) : Bool :=
  designObs2 M u == designObs2 M (u - 6)

/-- **The literal-`2` window-shift map**: `ALT.windowMap`'s own shape, with the
complemented cell moved from `0` to `2`. -/
def windowMap2 (w : Fin 8 → Bool) : Fin 8 → Bool :=
  fun i => if h : (i : ℕ) + 1 < 8 then w ⟨(i : ℕ) + 1, h⟩ else !(w 2)

/-- **The literal-`2` noisy step**: `ALT.noisyStep`'s own shape over `windowMap2`. -/
def noisyStep2 (w : Fin 8 → Bool) (b : Bool) : Fin 8 → Bool :=
  fun i => if (i : ℕ) + 1 < 8 then windowMap2 w i else xor (windowMap2 w i) b

/-- One step of the lag-`6` host: the window steps by `noisyStep2` on the tape bit at the counter's
next position, while the counter itself advances by one. -/
def update2 :
    (Fin 8 → Bool) × ZMod (2 * (2 * M) * 22) → (Fin 8 → Bool) × ZMod (2 * (2 * M) * 22) :=
  fun p => (noisyStep2 p.1 (tape2 M (p.2 + 1)), p.2 + 1)

/-- The design's own length-`8` window ending at counter `c`: the oldest coordinate first, mirroring
`TapeHost.designWindow`. -/
def designWindow2 (c : ZMod (2 * (2 * M) * 22)) : Fin 8 → Bool :=
  fun i => designObs2 M (c - 7 + ((i : ℕ) : ZMod (2 * (2 * M) * 22)))

private lemma xor_not_beq (a b : Bool) : xor (!b) (a == b) = a := by
  cases a <;> cases b <;> decide

private theorem update2_designWindow2 (c : ZMod (2 * (2 * M) * 22)) :
    update2 M (designWindow2 M c, c) = (designWindow2 M (c + 1), c + 1) := by
  change (noisyStep2 (designWindow2 M c) (tape2 M (c + 1)), c + 1)
    = (designWindow2 M (c + 1), c + 1)
  congr 1
  funext i
  change noisyStep2 (designWindow2 M c) (tape2 M (c + 1)) i
    = designObs2 M (c + 1 - 7 + ((i : ℕ) : ZMod (2 * (2 * M) * 22)))
  rw [noisyStep2, windowMap2]
  by_cases h : (i : ℕ) + 1 < 8
  · rw [ite_eq_left h, dite_eq_left h]
    change designObs2 M (c - 7 + (((⟨(i : ℕ) + 1, h⟩ : Fin 8) : ℕ) : ZMod (2 * (2 * M) * 22)))
      = designObs2 M (c + 1 - 7 + ((i : ℕ) : ZMod (2 * (2 * M) * 22)))
    congr 1
    push_cast
    ring
  · rw [ite_eq_right h, dite_eq_right h]
    have hi7 : (i : ℕ) = 7 := by have := i.isLt; omega
    change xor (!(designWindow2 M c 2)) (tape2 M (c + 1))
      = designObs2 M (c + 1 - 7 + ((i : ℕ) : ZMod (2 * (2 * M) * 22)))
    have h2 : designWindow2 M c 2 = designObs2 M (c - 5) := by
      change designObs2 M (c - 7 + (((2 : Fin 8) : ℕ) : ZMod (2 * (2 * M) * 22)))
        = designObs2 M (c - 5)
      congr 1
      simp
      ring
    have htape : tape2 M (c + 1) = (designObs2 M (c + 1) == designObs2 M (c - 5)) := by
      change (designObs2 M (c + 1) == designObs2 M (c + 1 - 6)) = _
      congr 2
      ring
    have hrhs : c + 1 - 7 + ((i : ℕ) : ZMod (2 * (2 * M) * 22)) = c + 1 := by
      rw [hi7]; push_cast; ring
    rw [h2, htape, hrhs]
    exact xor_not_beq (designObs2 M (c + 1)) (designObs2 M (c - 5))

/-- **The designed orbit.** Started at the design's own window ending at counter `c`, the host's
state after `t` steps is the design's window ending `t` further along, mirroring
`TapeHost.tapeUpdate_iterate_designWindow`. -/
theorem update2_iterate_designWindow2 (c : ZMod (2 * (2 * M) * 22)) (t : ℕ) :
    (update2 M)^[t] (designWindow2 M c, c)
      = (designWindow2 M (c + (t : ZMod _)), c + (t : ZMod _)) := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [Function.iterate_succ_apply', ih, update2_designWindow2]
    have hstep : c + (t : ZMod (2 * (2 * M) * 22)) + 1
        = c + ((t + 1 : ℕ) : ZMod (2 * (2 * M) * 22)) := by
      push_cast; ring
    rw [hstep]

/-! ## The witness substrate: memory layout, update, and loading -/

/-- The witness's cell index at literal `2`: `8` code cells, `8` window cells, and a finite binary
counter register of `Nat.size (2 * (2 * M) * 22)` cells, mirroring `BlockPairHost.Idx` at
this pair's own modulus. -/
abbrev Idx : Type := Fin 8 ⊕ (Fin 8 ⊕ Fin (Nat.size (2 * (2 * M) * 22)))

/-- The witness's memory, in [Decoupling]'s own shape: one `Bool` per cell. -/
abbrev Mem : Type := ALT.Mem (Idx M) Bool

/-- The **code region**: the cells holding the committed literal. -/
def codeRegion2 : Set (Idx M) := Set.range Sum.inl

omit [NeZero (2 * (2 * M))] in
/-- **The code region has exactly `8` cells.** -/
private theorem codeRegion2_ncard : (codeRegion2 M).ncard = 8 := by
  rw [codeRegion2, ← Set.image_univ, Set.ncard_image_of_injective _ Sum.inl_injective,
    Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin]

/-- **Reading the rule off the code cells**, mirroring `BlockPairHost.decodeRule`. -/
def decodeRule2 (s : Mem M) : Fin 8 :=
  if h : ∃ i : Fin 8, s (Sum.inl i) = true then Fin.find _ h else 0

omit [NeZero (2 * (2 * M))] in
private theorem decodeRule2_oneHot (s : Mem M) (i : Fin 8)
    (h : ∀ j : Fin 8, s (Sum.inl j) = true ↔ j = i) : decodeRule2 M s = i := by
  have hex : ∃ j : Fin 8, s (Sum.inl j) = true := ⟨i, (h i).mpr rfl⟩
  rw [decodeRule2, dite_eq_left hex]
  refine le_antisymm (Fin.find_le_of_pos hex ((h i).mpr rfl)) ((Fin.le_find_iff hex i).mpr ?_)
  intro m hm hp
  exact absurd ((h m).mp hp) (ne_of_lt hm)

/-- The counter register's value stays below `2 ^ Nat.size` of its modulus. -/
lemma counter_val_lt2 (c : ZMod (2 * (2 * M) * 22)) :
    c.val < 2 ^ Nat.size (2 * (2 * M) * 22) :=
  lt_trans (ZMod.val_lt c) (Nat.lt_size_self _)

/-- **Reading the counter register**, mirroring `BlockPairHost.readCounter`. -/
def readCounter2 (s : Mem M) : ZMod (2 * (2 * M) * 22) :=
  ((finFunctionFinEquiv (fun i : Fin (Nat.size (2 * (2 * M) * 22)) =>
    if s (Sum.inr (Sum.inr i)) then (1 : Fin 2) else 0)).val : ℕ)

/-- **Writing the counter register**, mirroring `BlockPairHost.writeCounter`. -/
def writeCounter2 (c : ZMod (2 * (2 * M) * 22)) (i : Fin (Nat.size (2 * (2 * M) * 22))) : Bool :=
  finFunctionFinEquiv.symm (⟨c.val, counter_val_lt2 M c⟩ :
    Fin (2 ^ Nat.size (2 * (2 * M) * 22))) i == 1

private lemma readCounter2_eq_of_counter_cells {s : Mem M} {c : ZMod (2 * (2 * M) * 22)}
    (h : ∀ i, s (Sum.inr (Sum.inr i)) = writeCounter2 M c i) :
    readCounter2 M s = c := by
  unfold readCounter2
  have heq : (fun i => if s (Sum.inr (Sum.inr i)) then (1 : Fin 2) else 0)
      = finFunctionFinEquiv.symm (⟨c.val, counter_val_lt2 M c⟩ :
        Fin (2 ^ Nat.size (2 * (2 * M) * 22))) := by
    funext i
    rw [h i]
    unfold writeCounter2
    generalize finFunctionFinEquiv.symm (⟨c.val, counter_val_lt2 M c⟩ :
      Fin (2 ^ Nat.size (2 * (2 * M) * 22))) i = x
    fin_cases x <;> decide
  rw [heq, Equiv.apply_symm_apply]
  exact ZMod.natCast_zmod_val c

/-- **One step of the substrate's own dynamics at literal `2`.** `BlockPairHost.subUpdate`'s
own line, verbatim: the window-shift branch already reads the DECODED literal's own cell
(`decodeRule2 M s`), so nothing there changes; only the correction term is literal-specific
(`tape2` in place of `BlockPairHost.tape`). -/
def subUpdate2 (s : Mem M) : Mem M := fun x =>
  match x with
  | Sum.inl i => s (Sum.inl i)
  | Sum.inr (Sum.inl i) =>
      if h : (i : ℕ) + 1 < 8 then s (Sum.inr (Sum.inl ⟨(i : ℕ) + 1, h⟩))
      else xor (!(s (Sum.inr (Sum.inl (decodeRule2 M s))))) (tape2 M (readCounter2 M s + 1))
  | Sum.inr (Sum.inr j) => writeCounter2 M (readCounter2 M s + 1) j

/-- **Loading the substrate's own designed window into the memory, at literal `2`.** The code is
one-hot at literal `2` (in place of `0`); the window and counter loading are otherwise
`BlockPairHost.load`'s own line. -/
def load2 (c : ZMod (2 * (2 * M) * 22)) : Mem M := fun x =>
  match x with
  | Sum.inl i => decide ((i : ℕ) = 2)
  | Sum.inr (Sum.inl i) => designObs2 M (c + (i : ℕ))
  | Sum.inr (Sum.inr j) => writeCounter2 M (c + 7) j

/-- The observation the substrate emits: its window's oldest bit, mirroring
`BlockPairHost.readObs`. -/
def readObs2 (s : Mem M) : Bool := s (Sum.inr (Sum.inl 0))

/-- **(S1) by construction.** -/
theorem subUpdate2_fixes : ALT.Fixes (subUpdate2 M) (codeRegion2 M) := by
  rintro s _ ⟨i, rfl⟩
  rfl

/-! ## The realization theorem: the substrate's own process IS the lag-`6` host

Mirroring `BlockPairWitness.lean`'s own realization section: the `(window, counter)` projection
commutes with the two updates given the code names literal `2`, the code stays one-hot at `2`
along the whole loaded orbit, and the combined orbit theorem transports
`update2_iterate_designWindow2` as a black box. -/

/-- The `(window, counter)` projection of a substrate memory. -/
private def proj2 (s : Mem M) : (Fin 8 → Bool) × ZMod (2 * (2 * M) * 22) :=
  (fun i => s (Sum.inr (Sum.inl i)), readCounter2 M s)

/-- **The projection commutes with the two updates**, given the code names literal `2`: the window
branch's case split matches `noisyStep2`/`windowMap2`'s own term for term at `decodeRule2 M s =
2`, and the counter branch is the round trip. -/
private lemma proj2_subUpdate2 (s : Mem M) (h2 : decodeRule2 M s = 2) :
    proj2 M (subUpdate2 M s) = update2 M (proj2 M s) := by
  have hcounter : readCounter2 M (subUpdate2 M s) = readCounter2 M s + 1 :=
    readCounter2_eq_of_counter_cells M (fun _ => rfl)
  refine Prod.ext ?_ hcounter
  funext i
  simp only [proj2, update2, subUpdate2, noisyStep2, windowMap2]
  split_ifs with h
  · rfl
  · rw [h2]

/-- **The code stays one-hot at `2` along the whole loaded orbit.** -/
private lemma decodeRule2_iterate_load2 (c : ZMod (2 * (2 * M) * 22)) :
    ∀ t, decodeRule2 M ((subUpdate2 M)^[t] (load2 M c)) = 2 := by
  have hcode : ∀ t, ∀ j : Fin 8,
      ((subUpdate2 M)^[t] (load2 M c)) (Sum.inl j) = decide ((j : ℕ) = 2) := by
    intro t
    induction t with
    | zero => intro j; rfl
    | succ t ih =>
      intro j
      rw [Function.iterate_succ_apply']
      exact ih j
  intro t
  apply decodeRule2_oneHot
  intro j
  rw [hcode t j]
  simp only [decide_eq_true_eq]
  constructor
  · intro hj; exact Fin.ext hj
  · intro hj; simp [hj]

/-- **The combined orbit theorem**: the substrate's own `(window, counter)` state after `t` steps
is `update2`'s own orbit from the designed initial window. -/
private lemma proj2_iterate (c : ZMod (2 * (2 * M) * 22)) (t : ℕ) :
    proj2 M ((subUpdate2 M)^[t] (load2 M c)) =
      (update2 M)^[t] (proj2 M (load2 M c)) := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
      proj2_subUpdate2 M _ (decodeRule2_iterate_load2 M c t), ih]

private lemma proj2_load2 (c : ZMod (2 * (2 * M) * 22)) :
    proj2 M (load2 M c) = (designWindow2 M (c + 7), c + 7) := by
  have hcounter : readCounter2 M (load2 M c) = c + 7 :=
    readCounter2_eq_of_counter_cells M (fun _ => rfl)
  refine Prod.ext ?_ hcounter
  funext i
  change designObs2 M (c + (i : ℕ)) = designWindow2 M (c + 7) i
  unfold designWindow2
  congr 1
  ring

/-- **The realization theorem.** Reading the substrate's own observation cell along its own
update's orbit, from its own loaded state, reproduces `designObs2` exactly —
pointwise, mirroring `BlockPairHost.readObs_iterate_load`. -/
theorem readObs_iterate_load2 (c : ZMod (2 * (2 * M) * 22)) (t : ℕ) :
    readObs2 M ((subUpdate2 M)^[t] (load2 M c)) = designObs2 M (c + (t : ℕ)) := by
  have hp := proj2_iterate M c t
  rw [proj2_load2, update2_iterate_designWindow2] at hp
  have hfst : (fun i => ((subUpdate2 M)^[t] (load2 M c)) (Sum.inr (Sum.inl i)))
      = designWindow2 M (c + 7 + (t : ℕ)) := congrArg Prod.fst hp
  change ((subUpdate2 M)^[t] (load2 M c)) (Sum.inr (Sum.inl 0)) = designObs2 M (c + (t : ℕ))
  rw [congrFun hfst 0]
  unfold designWindow2
  change designObs2 M (c + 7 + (t : ℕ) - 7 + ((0 : Fin 8) : ℕ)) = designObs2 M (c + (t : ℕ))
  have hz : ((0 : Fin 8) : ℕ) = 0 := rfl
  rw [hz]
  congr 1
  push_cast
  ring

end ShiftedSpikeHost

end ALT

/-! ## Axiom audit -/

set_option linter.style.longLine false in
/-- info: 'ALT.ShiftedSpikeHost.update2_iterate_designWindow2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.ShiftedSpikeHost.update2_iterate_designWindow2

set_option linter.style.longLine false in
/-- info: 'ALT.ShiftedSpikeHost.subUpdate2_fixes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.ShiftedSpikeHost.subUpdate2_fixes

set_option linter.style.longLine false in
/-- info: 'ALT.ShiftedSpikeHost.readObs_iterate_load2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.ShiftedSpikeHost.readObs_iterate_load2
