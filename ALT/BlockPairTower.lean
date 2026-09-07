/-
Copyright (c) 2026 Mykola Palamarchuk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mykola Palamarchuk
-/
import ALT.BlockPairCriterion

/-!
# The finite rung witness: the certified block-pair host as a tower's own rung

[Inevitability] §6, Proposition 6.12's boundary paragraph reads the committing substrate of
Proposition 6.2 "as a sequence of identified law-codes — each rung of a guest tower identified at
its own fixed parameters and committed", and records as open "whether any landed tower has one rung
meeting the landed identification hypotheses". This module answers that question at a finite
instance: the certified block-pair host of [Inevitability] §5 Theorem 5.8
(`BlockPairWitness.hostSubUpdate`, `BlockPairCriterion.blockPair_identifies`), re-read as the RUNG
LAW of a `PersistenceCapacity.witnessWorld` tower (`rungLaw`, `towerWorld`), meets
`blockPair_identifies`'s identification hypotheses at every state of the tower, from the tower's
own loaded start.

The construction is [Guests] §4 Law 3's object at two levels. Level 1 is the tower built here: the
host's own update `hostSubUpdate`, re-packed at its habitat cells (`hostMacro`) and hosted inside a
`witnessWorld` beside a free environment law — [Guests] §5 Theorem 5.1(i), row GV-4
(`PersistenceCapacity.witness_world_hosts`) instantiated at that rung with no new proof
(`tower_hosts_rung`). Level 2 is the host's OWN grown guest, already landed at the SAME update and
code region by `BlockPairOverlap.hostWitness_overlap` ([Inevitability] §5 Theorem 5.8(c)); this
module cites that membership rather than composing it onto the tower — see Scope.

What is identified is the tower's OUTER reading of the rung's own observation cell (`towerObs`),
read through the habitat's lens from the tower's loaded start (`towerStart`): it equals the
certified host's own trajectory (`towerObs_eq_hostTraj`), so `TapeHostSchedule.schedSurvivors`'s
`2τ`-pruning rule isolates the rung's true literal from the horizon on
(`tower_rung_identifies`), exactly as it does for the host read directly (`blockPair_identifies`).

## Main results

* `hostCells`, `hostMacro` — the host's own cells, re-indexed onto the habitat's flat carrier.
* `rungLaw`, `rungLaw_iterate` — the rung's own law: the host's update, conjugated onto the habitat
  cells, and its telescoped orbit.
* `towerWorld`, `tower_hosts_rung` — the tower, and `witness_world_hosts` instantiated at its rung:
  the rung's habitat cells host a guest at exactly the rung's own law, surjectively, with a full
  robustness margin at every environment law.
* `towerStart`, `towerObs`, `witnessLens_towerWorld_iterate`, `towerObs_eq_hostTraj` — the tower
  loaded at the host's own certified initial state, and its outer reading identified with the
  host's own trajectory.
* `tower_rung_identifies` — **the capstone**: the schedule's pruning rule isolates the rung's true
  literal at every environment law and every horizon past `912`, transporting
  `BlockPairCriterion.blockPair_identifies` onto the tower's own outer reading.

## Scope

This does NOT claim ownership: `witness_world_hosts` carries no ownership or typical-member clause
(that is `PersistenceCapacity.witness_world`'s, stated for a PERMUTATION law), and `rungLaw` is not
injective — `hostSubUpdate` drops the window's oldest bit each step, so no ownership argument
applies here. It does NOT compose level 2 onto the tower: `hostWitness_overlap`'s grown guest is a
separate `HostGrowsLawfulGuest` witness at the SAME update, cited beside this rung rather than
assembled into one three-level object, since `PersistenceCapacity.Carries` is not an `Intertwines`
and no bridge between the two is built here. And it says nothing about towers at scales other than
one, or about survival ([Inevitability] §6) — [Guests] Law 4's recurrent-core argument is exactly
as unavailable to this rung as it is to the host directly (`BlockPairOverlap.lean`'s own Scope
paragraph).
-/

namespace BlockPairTower

open PersistenceCapacity Decoupling BlockPairWitness

variable (M : ℕ) [NeZero (2 * (2 * M))] {ι_J : Type*}

/-! ## The rung: the host's own update, re-packed at its habitat cells -/

/-- The host's own cell count — the habitat's macro width. -/
abbrev hostCells : ℕ := 8 + (8 + Nat.size (2 * (2 * M) * 24))

/-- The host's cells, re-indexed onto the habitat's flat carrier — values untouched. -/
abbrev hostMacro : HostMem M ≃ Mem (Fin (hostCells M)) Bool :=
  Equiv.arrowCongr (BlockPairOverlap.hostIdxEquiv M) (Equiv.refl Bool)

/-- **The rung's own law**: the block-pair host's update, conjugated onto the habitat cells. -/
def rungLaw : Mem (Fin (hostCells M)) Bool → Mem (Fin (hostCells M)) Bool :=
  fun m => hostMacro M (hostSubUpdate M ((hostMacro M).symm m))

/-- **The rung's orbit telescopes**: `t` steps of `rungLaw` from a re-packed host state are the
re-packing of `t` steps of the host's own update. -/
theorem rungLaw_iterate (t : ℕ) (s : HostMem M) :
    (rungLaw M)^[t] (hostMacro M s) = hostMacro M ((hostSubUpdate M)^[t] s) := by
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [Function.iterate_succ_apply', ih]
      unfold rungLaw
      rw [Equiv.symm_apply_apply, ← Function.iterate_succ_apply' (hostSubUpdate M) t s]

/-! ## The tower: the rung hosted inside a witness world -/

/-- **The tower**: the rung's own law, hosted inside a `witnessWorld` beside a free environment
law `π`. -/
abbrev towerWorld (k : ℕ) (π : Mem ι_J Bool → Mem ι_J Bool) :
    Mem ((Fin (hostCells M) × Fin (3 ^ k)) ⊕ ι_J) Bool →
      Mem ((Fin (hostCells M) × Fin (3 ^ k)) ⊕ ι_J) Bool :=
  witnessWorld (hostCells M) k (rungLaw M) π

/-- **The tower hosts its rung**: `witness_world_hosts` ([Guests] §5 Theorem 5.1(i), row GV-4)
instantiated at `rungLaw M` — surjectively, with the exact square, and a full robustness margin at
every environment law `π`. No new proof; the landed theorem read at this rung. -/
theorem tower_hosts_rung [Fintype ι_J] [Nonempty (Mem ι_J Bool)] (k : ℕ)
    (π : Mem ι_J Bool → Mem ι_J Bool) :
    Function.Surjective (witnessLens (ι_J := ι_J) (hostCells M) k) ∧
      Intertwines (towerWorld M k π) (rungLaw M) (fun _ => witnessLens (hostCells M) k) ∧
      ∀ e < 2 ^ k, HasMargin (towerWorld M k π) Set.univ (witnessLens (hostCells M) k) e :=
  witness_world_hosts (hostCells M) k (rungLaw M) π

/-! ## The tower loaded at the host's own certified state -/

/-- **The loaded start**: the habitat codeword of the host's own certified loaded state, beside an
arbitrary environment state `env`. -/
def towerStart (k : ℕ) (c : ZMod (2 * (2 * M) * 24)) (env : Mem ι_J Bool) :
    Mem ((Fin (hostCells M) × Fin (3 ^ k)) ⊕ ι_J) Bool :=
  Sum.elim (habitatEnc (hostCells M) k (hostMacro M (loadHost M c))) env

/-- **The tower's outer reading**: the rung's own observation cell, read through the habitat's
lens, from the loaded start. -/
def towerObs (k : ℕ) (π : Mem ι_J Bool → Mem ι_J Bool) (c : ZMod (2 * (2 * M) * 24))
    (env : Mem ι_J Bool) : ℕ → Bool :=
  fun t => readObs M ((hostMacro M).symm
    (witnessLens (hostCells M) k ((towerWorld M k π)^[t] (towerStart M k c env))))

/-- **The tower's macro state telescopes to the host's own orbit**: at every step, the tower's
habitat reading from the loaded start is the re-packing of the host's own update, iterated from
its own loaded state. -/
theorem witnessLens_towerWorld_iterate (k : ℕ) (π : Mem ι_J Bool → Mem ι_J Bool)
    (c : ZMod (2 * (2 * M) * 24)) (env : Mem ι_J Bool) (t : ℕ) :
    witnessLens (hostCells M) k ((towerWorld M k π)^[t] (towerStart M k c env))
      = hostMacro M ((hostSubUpdate M)^[t] (loadHost M c)) := by
  induction t with
  | zero =>
      rw [Function.iterate_zero_apply, Function.iterate_zero_apply]
      unfold witnessLens towerStart
      rw [Sum.elim_comp_inl, macroLens_habitatEnc]
  | succ t ih =>
      rw [Function.iterate_succ_apply', witness_square, ih]
      unfold rungLaw
      rw [Equiv.symm_apply_apply,
        ← Function.iterate_succ_apply' (hostSubUpdate M) t (loadHost M c)]

/-- **The tower's outer reading IS the certified host's own trajectory** — from every environment
law and every environment state, the tower loaded at phase `c` emits exactly
`BlockPairObservability.hostTraj M c`. -/
theorem towerObs_eq_hostTraj (k : ℕ) (π : Mem ι_J Bool → Mem ι_J Bool)
    (c : ZMod (2 * (2 * M) * 24)) (env : Mem ι_J Bool) :
    towerObs M k π c env = BlockPairObservability.hostTraj M c := by
  funext t
  unfold towerObs
  rw [witnessLens_towerWorld_iterate, Equiv.symm_apply_apply, readObs_iterate_loadHost]
  rfl

/-- **The finite rung witness — the capstone.** The schedule's `2τ`-pruning rule, at `τ = 1/3` and
every horizon `n > 912`, isolates the rung's true literal `0` from the tower's own outer reading,
at every environment law `π`, every environment state `env`, and every depth `k` — transporting
`BlockPairCriterion.blockPair_identifies` from the host read directly onto the host read as one
rung of a `witnessWorld` tower. This is [Inevitability] §6, Proposition 6.12's boundary question,
answered YES at this finite instance. -/
theorem tower_rung_identifies (k : ℕ) (π : Mem ι_J Bool → Mem ι_J Bool)
    (c : ZMod (2 * (2 * M) * 24)) (env : Mem ι_J Bool) {n : ℕ} (hn : 912 < n) :
    TapeHostSchedule.schedSurvivors (1 / 3) n (towerObs M k π c env) = {0} := by
  rw [towerObs_eq_hostTraj]
  exact BlockPairCriterion.blockPair_identifies M c hn

end BlockPairTower

/-! ## Axiom audit -/

/-- info: 'BlockPairTower.tower_hosts_rung' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms BlockPairTower.tower_hosts_rung

/-- info: 'BlockPairTower.tower_rung_identifies' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms BlockPairTower.tower_rung_identifies
