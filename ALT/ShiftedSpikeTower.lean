/-
Copyright (c) 2026 Mykola Palamarchuk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mykola Palamarchuk
-/
module

public import ALT.ShiftedSpikeHost
public import ALT.BlockPairTower
public import ALT.AccretiveDecoupling

/-!
# The second rung, and the differing-rules rung pair

`ShiftedSpikeHost.lean`'s witness substrate at literal `2`, re-read as the rung law of a
`PersistenceCapacity.witnessWorld` tower — `BlockPairTower.lean`'s own construction, transposed to
this substrate — mirroring [Guests] §4 Law 3's object at the SAME level `BlockPairTower.lean`
builds it at. The tower's outer reading of the rung's own observation cell is identified with
`ShiftedSpikeCriterion.shiftedSpike_identifies`, exactly as `BlockPairTower.tower_rung_identifies`
does for the landed (literal-`0`) rung.

The pair capstone (`descending_pair_commits`) then puts both rungs together: two towers, two
identified rules — `0` and `2` — differing, and read off as the entries of a
`Decoupling.seqWrite` stream committed by `Decoupling.seqDecode_hereditary`, held under every later
step. This is [Inevitability] §6 Remark 6.14's finite degeneracy clause, lifted at this instance:
clause (ii) — one literal across all landed rungs — no longer holds, while clause (i) — one
identifiable rung per tower — stands unchanged (the pair is two rungs in TWO towers, sequenced by
the stream, not one tower with two identifiable rungs). This is also the first stream at which
[Inevitability] Proposition 6.12's substrate is genuinely `Decoupling.seqWrite` rather than its
constant-stream reduction `Decoupling.tapeWrite`.

## Main results

* `hostCells2`, `hostMacro2` — the second host's own cells, re-indexed onto the habitat's flat
  carrier, mirroring `BlockPairTower.hostCells`/`hostMacro`.
* `rungLaw2`, `rungLaw2_iterate` — the second rung's own law, and its telescoped orbit.
* `towerWorld2`, `tower_hosts_rung2` — the second tower, and `witness_world_hosts` instantiated at
  its rung.
* `towerStart2`, `towerObs2`, `witnessLens_towerWorld2_iterate`, `towerObs2_eq_hostTraj2` — the
  second tower loaded at the second host's own certified initial state, and its outer reading
  identified with the second host's own trajectory.
* `tower_rung_identifies2` — the schedule's pruning rule isolates the second rung's true literal
  `2` at every environment law and every horizon past `816`.
* `literalStream` — the two-entry stream of identified literals, `0` then `2`.
* `descending_pair_commits` — **the capstone**: both rungs identified at their own literal, the
  literals differing, and equal to `literalStream`'s own entries, which `Decoupling.seqWrite`
  commits under every later step.

## Scope

As `BlockPairTower.lean`'s own Scope paragraph, transposed: no ownership is claimed (`rungLaw2` is
not injective — `hostSubUpdate2` drops the window's oldest bit each step, exactly as `rungLaw`
does), nothing about towers at scales other than one, nothing about survival, and no composition of
the two rungs' towers into a single joint object beyond `literalStream`'s own two-entry commitment
— the two towers stay separate objects, sequenced only by the stream reading off their identified
literals.
-/


@[expose] public section

namespace ShiftedSpikeTower

open PersistenceCapacity Decoupling ShiftedSpikeHost ShiftedSpikeCriterion

variable (M : ℕ) [NeZero (2 * (2 * M))] {ι_J : Type*}

/-! ## The second rung: the second host's own update, re-packed at its habitat cells -/

/-- The second host's own cell count — the habitat's macro width. -/
abbrev hostCells2 : ℕ := 8 + (8 + Nat.size (2 * (2 * M) * 22))

/-- **The re-indexing equivalence** identifying the second host's own three-part cell index with a
flat `Fin`, mirroring `BlockPairOverlap.hostIdxEquiv` at this pair's own modulus. -/
def hostIdxEquiv2 : HostIdx2 M ≃ Fin (hostCells2 M) :=
  (Equiv.sumCongr (Equiv.refl (Fin 8)) finSumFinEquiv).trans finSumFinEquiv

/-- The second host's cells, re-indexed onto the habitat's flat carrier — values untouched. -/
abbrev hostMacro2 : HostMem2 M ≃ Mem (Fin (hostCells2 M)) Bool :=
  Equiv.arrowCongr (hostIdxEquiv2 M) (Equiv.refl Bool)

/-- **The second rung's own law**: the second host's update, conjugated onto the habitat cells. -/
def rungLaw2 : Mem (Fin (hostCells2 M)) Bool → Mem (Fin (hostCells2 M)) Bool :=
  fun m => hostMacro2 M (hostSubUpdate2 M ((hostMacro2 M).symm m))

/-- **The second rung's orbit telescopes**: `t` steps of `rungLaw2` from a re-packed host state are
the re-packing of `t` steps of the second host's own update. -/
theorem rungLaw2_iterate (t : ℕ) (s : HostMem2 M) :
    (rungLaw2 M)^[t] (hostMacro2 M s) = hostMacro2 M ((hostSubUpdate2 M)^[t] s) := by
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [Function.iterate_succ_apply', ih]
      unfold rungLaw2
      rw [Equiv.symm_apply_apply, ← Function.iterate_succ_apply' (hostSubUpdate2 M) t s]

/-! ## The second tower: the second rung hosted inside a witness world -/

/-- **The second tower**: the second rung's own law, hosted inside a `witnessWorld` beside a free
environment law `π`. -/
abbrev towerWorld2 (k : ℕ) (π : Mem ι_J Bool → Mem ι_J Bool) :
    Mem ((Fin (hostCells2 M) × Fin (3 ^ k)) ⊕ ι_J) Bool →
      Mem ((Fin (hostCells2 M) × Fin (3 ^ k)) ⊕ ι_J) Bool :=
  witnessWorld (hostCells2 M) k (rungLaw2 M) π

/-- **The second tower hosts its rung**: `witness_world_hosts` instantiated at `rungLaw2 M` — no
new proof, mirroring `BlockPairTower.tower_hosts_rung`. -/
theorem tower_hosts_rung2 [Fintype ι_J] [Nonempty (Mem ι_J Bool)] (k : ℕ)
    (π : Mem ι_J Bool → Mem ι_J Bool) :
    Function.Surjective (witnessLens (ι_J := ι_J) (hostCells2 M) k) ∧
      Intertwines (towerWorld2 M k π) (rungLaw2 M) (fun _ => witnessLens (hostCells2 M) k) ∧
      ∀ e < 2 ^ k, HasMargin (towerWorld2 M k π) Set.univ (witnessLens (hostCells2 M) k) e :=
  witness_world_hosts (hostCells2 M) k (rungLaw2 M) π

/-! ## The second tower loaded at the second host's own certified state -/

/-- **The loaded start**: the habitat codeword of the second host's own certified loaded state,
beside an arbitrary environment state `env`. -/
def towerStart2 (k : ℕ) (c : ZMod (2 * (2 * M) * 22)) (env : Mem ι_J Bool) :
    Mem ((Fin (hostCells2 M) × Fin (3 ^ k)) ⊕ ι_J) Bool :=
  Sum.elim (habitatEnc (hostCells2 M) k (hostMacro2 M (loadHost2 M c))) env

/-- **The second tower's outer reading**: the second rung's own observation cell, read through the
habitat's lens, from the loaded start. -/
def towerObs2 (k : ℕ) (π : Mem ι_J Bool → Mem ι_J Bool) (c : ZMod (2 * (2 * M) * 22))
    (env : Mem ι_J Bool) : ℕ → Bool :=
  fun t => readObs2 M ((hostMacro2 M).symm
    (witnessLens (hostCells2 M) k ((towerWorld2 M k π)^[t] (towerStart2 M k c env))))

/-- **The second tower's macro state telescopes to the second host's own orbit**. -/
theorem witnessLens_towerWorld2_iterate (k : ℕ) (π : Mem ι_J Bool → Mem ι_J Bool)
    (c : ZMod (2 * (2 * M) * 22)) (env : Mem ι_J Bool) (t : ℕ) :
    witnessLens (hostCells2 M) k ((towerWorld2 M k π)^[t] (towerStart2 M k c env))
      = hostMacro2 M ((hostSubUpdate2 M)^[t] (loadHost2 M c)) := by
  induction t with
  | zero =>
      rw [Function.iterate_zero_apply, Function.iterate_zero_apply]
      unfold witnessLens towerStart2
      rw [Sum.elim_comp_inl, macroLens_habitatEnc]
  | succ t ih =>
      rw [Function.iterate_succ_apply', witness_square, ih]
      unfold rungLaw2
      rw [Equiv.symm_apply_apply,
        ← Function.iterate_succ_apply' (hostSubUpdate2 M) t (loadHost2 M c)]

/-- **The second tower's outer reading IS the second host's own trajectory.** -/
theorem towerObs2_eq_hostTraj2 (k : ℕ) (π : Mem ι_J Bool → Mem ι_J Bool)
    (c : ZMod (2 * (2 * M) * 22)) (env : Mem ι_J Bool) :
    towerObs2 M k π c env = TapeHostObservability.hostTraj (designObs2 M) c := by
  funext t
  unfold towerObs2
  rw [witnessLens_towerWorld2_iterate, Equiv.symm_apply_apply, readObs_iterate_loadHost2]
  rfl

/-- **The second finite rung witness.** The schedule's `2τ`-pruning rule, at `τ = 1/3` and every
horizon `n > 816`, isolates the second rung's true literal `2` from the second tower's own outer
reading, at every environment law `π`, every environment state `env`, and every depth `k` —
transporting `ShiftedSpikeCriterion.shiftedSpike_identifies` onto the second host read as one rung
of a `witnessWorld` tower, mirroring `BlockPairTower.tower_rung_identifies`. -/
theorem tower_rung_identifies2 (k : ℕ) (π : Mem ι_J Bool → Mem ι_J Bool)
    (c : ZMod (2 * (2 * M) * 22)) (env : Mem ι_J Bool) {n : ℕ} (hn : 816 < n) :
    TapeHostSchedule.schedSurvivors (1 / 3) n (towerObs2 M k π c env) = {(2 : Fin 8)} := by
  rw [towerObs2_eq_hostTraj2]
  exact shiftedSpike_identifies M c hn

/-! ## The two-entry committed stream -/

/-- **The stream of the two identified literals**: `0` at stage `0`, `2` from stage `1` on. -/
def literalStream : ℕ → ℕ := fun t => if t = 0 then 0 else 2

/-! ## The pair capstone -/

/-- **The differing-rules rung pair — the capstone.** Two tower rungs, in two SEPARATE towers: the
landed literal-`0` rung (`BlockPairTower.towerObs`) and the second, literal-`2` rung (`towerObs2`).
Each still has exactly one identifiable rung in its own tower — [Inevitability] §6 Remark 6.14's
degeneracy clause (i) stands — but their identified rules differ, which is clause (ii) lifted: no
landed pair before this one supplied two rungs whose identified rules differ. The two literals are
exactly `literalStream`'s own two entries, and `Decoupling.seqDecode_hereditary` commits both under
every later step — the first instance at which [Inevitability] Proposition 6.12's substrate is
genuinely `Decoupling.seqWrite` rather than its constant-stream reduction `Decoupling.tapeWrite`. -/
theorem descending_pair_commits (M k : ℕ) [NeZero (2 * (2 * M))] {ι_J : Type*}
    (π : Mem ι_J Bool → Mem ι_J Bool) (c : ZMod (2 * (2 * M) * 24)) (env : Mem ι_J Bool)
    (M' k' : ℕ) [NeZero (2 * (2 * M'))] {ι_J' : Type*}
    (π' : Mem ι_J' Bool → Mem ι_J' Bool) (c' : ZMod (2 * (2 * M') * 22)) (env' : Mem ι_J' Bool)
    {n n' : ℕ} (hn : 912 < n) (hn' : 816 < n') :
    TapeHostSchedule.schedSurvivors (1 / 3) n (BlockPairTower.towerObs M k π c env)
        = {(0 : Fin 8)} ∧
      TapeHostSchedule.schedSurvivors (1 / 3) n' (towerObs2 M' k' π' c' env') = {(2 : Fin 8)} ∧
      literalStream 0 = 0 ∧ literalStream 1 = 2 ∧ literalStream 0 ≠ literalStream 1 ∧
      ∀ k'', tapeDecode 2 ((seqWrite literalStream)^[2 + k''] seqStart) =
        fun a => if 1 ≤ a ∧ a ≤ 2 then literalStream (a - 1) else 0 :=
  ⟨BlockPairTower.tower_rung_identifies M k π c env hn,
    tower_rung_identifies2 M' k' π' c' env' hn',
    rfl, rfl, by decide, fun k'' => seqDecode_hereditary literalStream 2 k''⟩

end ShiftedSpikeTower

/-! ## Axiom audit -/

/-- info: 'ShiftedSpikeTower.tower_hosts_rung2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ShiftedSpikeTower.tower_hosts_rung2

/-- info: 'ShiftedSpikeTower.tower_rung_identifies2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ShiftedSpikeTower.tower_rung_identifies2

/-- info: 'ShiftedSpikeTower.descending_pair_commits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ShiftedSpikeTower.descending_pair_commits
