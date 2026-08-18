/-
Copyright (c) 2026 Mykola Palamarchuk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mykola Palamarchuk
-/
import ALT.TapeHostFiber
import ALT.TapeHostOverlap
import ALT.RedundantFiber
import ALT.SubstrateEmergence

/-!
# A member of both route-classes carries survival, by redundancy ([Inevitability] §5, §6)

[Inevitability] §5 Theorem 5.8's boundary paragraph leaves open "whether any member of both [route-
classes] can carry survival," naming the reason a permutation host cannot: `H_M`'s core dynamics is
a permutation, so *Guests* Law 4 puts a positive intrinsic margin out of its reach ([Inevitability]
§2 Definition 2.3). But survival in this corpus has a second, independent form — the redundancy
route, §6 Proposition 6.1(iii)'s third sufficient condition, delivered "with no margin inequality
entering at all" — and that route is available to any host whose observations drive a redundant
floored fiber, margin or none.

This module exhibits a witness: the tape host's substrate (`TapeHostWitness`/`TapeHostOverlap`, at
any window-deviation profile) with a `P`-copy redundant floored fiber (`RedundantFiber`) added as
extra memory, packaged as one `Decoupling.Mem`-substrate (`CompMem`). The fiber's own cells never
write the base's, and the base's own update never reads the fiber's, so both of the base's
memberships — `𝒮_L` (`TapeHostWitness.tapeHost_substrateL`) and `𝒮_E`
(`TapeHostOverlap.tapeHost_substrateE`) — transport to the composite unchanged in every field but
the read-only-code witness, which is a direct re-proof. The fiber's miss indicator is read off the
base's own observation cell (`compSubUpdate`'s fiber branch consults nothing else), and it is
exactly `WitnessMixture.witMiss` on `TapeHostFiber.tapeStream` (`fiberMiss_eq_witMiss`) — the same
identity `TapeHostFiber`'s own rate and absorption theorems already consume. Survival is then
`TapeHostFiber.exists_untouched_copy_tapeHost` (an untouched copy exists, from the profile's own
bound on the base's noise count) composed with `RedundantFiber.compRun_eq_wRunFrom_of_untouched`
(that copy's reading, under any damage schedule confined to the untouched set, is the single
undamaged floored fiber's) — [Inevitability] §6 Theorem 6.6(v′), its absorption half, with no
margin entering anywhere.

## Main results

* `FiberIdx`, `CompIdx`, `CompMem` — the composite carrier: the host's own cells plus a `P`-copy
  population of length-`Nat.size W` binary registers, one per candidate per copy.
* `writeFiberCell`, `readFiberCell`, `readFiberCell_writeFiberCell` — the fiber's own round trip,
  `TapeHostWitness.writeCounter`/`readCounter`'s pattern applied per cell.
* `fiberMiss`, `fiberMiss_eq_witMiss` — the fiber's miss indicator, read off the base's own
  `readObs` at nine forward iterates, and its identification with `WitnessMixture.witMiss` along the
  loaded orbit.
* `compSubUpdate`, `compSubUpdate_base_eq`, `compSubUpdate_base_iterate`, `compSubUpdate_fixes` —
  the composite's own update, and the four facts that its base half is exactly `hostSubUpdate`'s,
  read-only code included: the whole content of the transport lemmas below.
* `compLoad`, `compFrame`, `compFrame_surj_iterate` — the composite's own loaded state, the frame
  reading its base's counter through `TapeHostOverlap.hostFrame` unchanged, and its surjectivity off
  the composite's own packed iterate, from `TapeHostWitness.readCounter_iterate_loadHost` alone.
* `comp_substrateL` — the composite is a member of `𝒮_L`, at any `Profile` and any `(K, gTS)`
  clearing `8 + capacity(⌈log₂(gTS+1)⌉)`: every field but `s1` is `TapeHostWitness.tapeHost_
  substrateL`'s own, untouched.
* `comp_substrateE` — the composite is a member of `𝒮_E`, at the same coupled `(K, gTS)`, via
  `SubstrateEmergence.substrateE_of_emergence` at the composite's own packing and frame.
* `comp_carries_survival` — **the redundancy route**: an untouched copy exists and its reading, at
  every step, is the single undamaged floored fiber's — [Inevitability] Theorem 6.6(v′), its
  absorption half, on the composite's own miss indicator; not the decode-level conclusion, which
  needs a never-missing candidate this base denies.
* `tapeHost_carries_survival` — **the capstone**: at a Gödel size fixed once, a member of both
  route-classes that carries survival by redundancy, at a horizon, conditional on the damage model.

## Scope

**Survival here is the redundancy route, not the margin.** No margin is claimed, so *Guests* Law 4
does not enter, whether or not the composite's update is reversible. What is claimed is
[Inevitability] §6 Theorem 6.6(v′), its absorption half — an untouched copy exists and its reading
is the single undamaged floored fiber's — at a horizon, with the host-side gate in place of (D1),
(D2) unchanged, the gate endogenous — confined to the tape's own firing (`DamageGate.NoiseGated`) —
not lifetime-free: the tape fires past every horizon at a positive-density profile
(`TapeHostFiber.tapeStream_fires_forever`), so (v)/(v″)'s quiet-stream gates are not on offer here,
exactly as they are not for `TapeHostFiber` itself. Nor is the decode-level conclusion — the
composite's reading equal to the base's next state — on offer: it needs the settling theorems'
never-missing hypothesis, which this base denies at positive density, exactly as `TapeHostFiber`'s
own docstrings say of settling. One witness; the class-level question — which systems carry
survival — stays open.

`compSubUpdate`'s fiber branch is a genuine one-step implementation of `RedundantFiber.wGen`, fed by
`fiberMiss` — not a placeholder — so the composite substrate honestly carries the fiber it claims
to, rather than merely type-checking against `𝒮_L`/`𝒮_E`'s opaque fields. What is **not** attempted
is a theorem identifying `compSubUpdate`'s own bit-level fiber iterate, across `P` copies and a
damage schedule, with `RedundantFiber.compRun` at the `CompMem` level: `comp_carries_survival` is
stated over `compRun`'s own abstract carrier `Fin P → WeightedFiber.WVec 8 W`, exactly as
`TapeHostFiber.exists_untouched_copy_tapeHost` already is, and every hypothesis of that theorem is
independent of what `compSubUpdate`'s fiber branch computes — the identity connecting the two is
`fiberMiss_eq_witMiss`, proved for the *undamaged* orbit, which is what the redundancy route needs.

The base modules (`TapeHostWitness`, `TapeHostOverlap`, `TapeHostFiber`) are untouched — every fact
this module needs from them is public. `RedundantFiber` and `SubstrateEmergence` are consumed as
cited black boxes.

[Inevitability] §2 Definition 2.3, §5 Theorem 5.8, §6 Proposition 6.1, Theorem 6.6, rows IN-25,
IN-28, IN-41, IN-42.
-/

namespace TapeHostSurvival

variable {N : ℕ} [NeZero N] (o : ZMod N → Bool) {P W : ℕ} [NeZero P]

/-! ## The composite carrier -/

/-- **The fiber's own cells**: for each of the `P` copies, one length-`Nat.size W` binary register
per candidate — `TapeHostWitness.writeCounter`/`readCounter`'s pattern, per cell of the candidate's
quantized weight. -/
abbrev FiberIdx (P W : ℕ) : Type := Fin P × Fin 8 × Fin (Nat.size W)

/-- **The composite's own cell index**: the host's `TapeHostWitness.HostIdx` plus the fiber's own
cells, a clean sum with no interleaving — the choice that keeps `TapeHostOverlap.hostFrame` (and its
surjectivity) unchanged below. -/
abbrev CompIdx (N P W : ℕ) : Type := TapeHostWitness.HostIdx N ⊕ FiberIdx P W

/-- **The composite memory**, in [Decoupling]'s own shape. -/
abbrev CompMem (N P W : ℕ) : Type := Decoupling.Mem (CompIdx N P W) Bool

private lemma fiberVal_lt {W : ℕ} (x : Fin (W + 1)) : (x : ℕ) < 2 ^ Nat.size W :=
  lt_of_le_of_lt (Nat.lt_succ_iff.mp x.isLt) (Nat.lt_size_self _)

/-- **Writing a population of weight vectors into the fiber's own cells.** -/
def writeFiberCell {P W : ℕ} (v : Fin P → WeightedFiber.WVec 8 W) : FiberIdx P W → Bool :=
  fun pci => finFunctionFinEquiv.symm
    (⟨(v pci.1 pci.2.1 : ℕ), fiberVal_lt (v pci.1 pci.2.1)⟩ : Fin (2 ^ Nat.size W)) pci.2.2 == 1

/-- **Reading a population of weight vectors back out of the fiber's own cells.** -/
def readFiberCell {P W : ℕ} (g : FiberIdx P W → Bool) : Fin P → WeightedFiber.WVec 8 W :=
  fun p c => ⟨min ((finFunctionFinEquiv
      (fun i : Fin (Nat.size W) => if g (p, c, i) then (1 : Fin 2) else 0)).val) W,
    Nat.lt_succ_of_le (min_le_right _ _)⟩

/-- **The fiber's own round trip.** -/
theorem readFiberCell_writeFiberCell {P W : ℕ} (v : Fin P → WeightedFiber.WVec 8 W) :
    readFiberCell (writeFiberCell v) = v := by
  funext p c
  apply Fin.ext
  change min ((finFunctionFinEquiv
      (fun i : Fin (Nat.size W) => if writeFiberCell v (p, c, i) then (1 : Fin 2) else 0)).val) W
      = (v p c : ℕ)
  have heq : (fun i : Fin (Nat.size W) => if writeFiberCell v (p, c, i) then (1 : Fin 2) else 0)
      = finFunctionFinEquiv.symm (⟨(v p c : ℕ), fiberVal_lt (v p c)⟩ : Fin (2 ^ Nat.size W)) := by
    funext i
    unfold writeFiberCell
    generalize finFunctionFinEquiv.symm (⟨(v p c : ℕ), fiberVal_lt (v p c)⟩ :
      Fin (2 ^ Nat.size W)) i = x
    fin_cases x <;> decide
  rw [heq, Equiv.apply_symm_apply]
  exact Nat.min_eq_left (Nat.lt_succ_iff.mp (v p c).isLt)

/-! ## The fiber's own miss indicator, read off the base's `readObs` alone -/

/-- **The fiber's miss indicator.** Candidate `i`'s miss, read off the base's own `readObs` at `i`
and `8` forward iterates of `hostSubUpdate` — nothing else of the base is consulted, and nothing of
the fiber is. -/
def fiberMiss (N : ℕ) [NeZero N] (o : ZMod N → Bool) (b : TapeHostWitness.HostMem N) :
    Fin 8 → Bool :=
  fun i => !(xor (TapeHostWitness.readObs N ((TapeHostWitness.hostSubUpdate N o)^[(i : ℕ)] b))
      (TapeHostWitness.readObs N ((TapeHostWitness.hostSubUpdate N o)^[8] b)))

/-- **The fiber's miss indicator is `WitnessMixture.witMiss` on `TapeHostFiber.tapeStream`**, along
the loaded orbit. `TapeHostWitness.readObs_iterate_loadHost` applied at horizons `t + i` and `t + 8`
(via `Function.iterate_add_apply`), then `TapeHostFiber.hostTraj_eq_obs` ties the result to `obs 8`
on the stream, matching `WitnessMixture.witMiss_eq_not_xor`'s own normal form exactly. -/
theorem fiberMiss_eq_witMiss (c : ZMod N) (t : ℕ) :
    fiberMiss N o ((TapeHostWitness.hostSubUpdate N o)^[t] (TapeHostWitness.loadHost N o c))
      = WitnessMixture.witMiss 8 (TapeHostFiber.tapeStream o c) t := by
  funext i
  change (!(xor
      (TapeHostWitness.readObs N ((TapeHostWitness.hostSubUpdate N o)^[(i : ℕ)]
        ((TapeHostWitness.hostSubUpdate N o)^[t] (TapeHostWitness.loadHost N o c))))
      (TapeHostWitness.readObs N ((TapeHostWitness.hostSubUpdate N o)^[8]
        ((TapeHostWitness.hostSubUpdate N o)^[t] (TapeHostWitness.loadHost N o c))))))
      = WitnessMixture.witMiss 8 (TapeHostFiber.tapeStream o c) t i
  rw [← Function.iterate_add_apply (TapeHostWitness.hostSubUpdate N o) (i : ℕ) t,
    ← Function.iterate_add_apply (TapeHostWitness.hostSubUpdate N o) 8 t,
    TapeHostWitness.readObs_iterate_loadHost, TapeHostWitness.readObs_iterate_loadHost,
    WitnessMixture.witMiss_eq_not_xor]
  have h1 : o (c + ((i : ℕ) + t : ℕ))
      = NoisyWindowChain.obs 8 (TapeHostFiber.tapeStream o c) (t + (i : ℕ)) := by
    have hobs := congrFun (TapeHostFiber.hostTraj_eq_obs o c) (t + (i : ℕ))
    unfold TapeHostObservability.hostTraj at hobs
    rw [← hobs]
    congr 2
    push_cast
    ring
  have h2 : o (c + (8 + t : ℕ))
      = NoisyWindowChain.obs 8 (TapeHostFiber.tapeStream o c) (t + 8) := by
    have hobs := congrFun (TapeHostFiber.hostTraj_eq_obs o c) (t + 8)
    unfold TapeHostObservability.hostTraj at hobs
    rw [← hobs]
    congr 2
    push_cast
    ring
  rw [h1, h2]

/-! ## The composite's own update -/

/-- **The composite's own update**: `hostSubUpdate` on the base cells, reading only the base cells
(`s ∘ Sum.inl`); the fiber's own `wGen` step on the fiber cells, driven by `fiberMiss` of the base
cells alone and the fiber's own current population. Neither half reads the other's newly-written
cells — this is the whole content of the transport lemmas below. -/
def compSubUpdate (N P W : ℕ) [NeZero N] (o : ZMod N → Bool) : CompMem N P W → CompMem N P W :=
  fun s => Sum.elim
    (fun i => TapeHostWitness.hostSubUpdate N o (s ∘ Sum.inl) i)
    (fun fi => writeFiberCell
      (fun p => WeightedFiber.wGen W
        (fun i => if fiberMiss N o (s ∘ Sum.inl) i then 1 else 2)
        (readFiberCell (s ∘ Sum.inr) p)) fi)

omit [NeZero P] in
/-- **The composite's base half is exactly `hostSubUpdate`'s own step**, by construction. -/
theorem compSubUpdate_base_eq (s : CompMem N P W) (i : TapeHostWitness.HostIdx N) :
    compSubUpdate N P W o s (Sum.inl i) = TapeHostWitness.hostSubUpdate N o (s ∘ Sum.inl) i := rfl

omit [NeZero P] in
/-- **The composite's base half is exactly `hostSubUpdate`'s own orbit**, at every horizon: the base
cells evolve independently of the fiber cells, so the composite's iterate restricted to
`Sum.inl` is `hostSubUpdate`'s own iterate of the restriction. -/
theorem compSubUpdate_base_iterate (s : CompMem N P W) (t : ℕ) :
    (compSubUpdate N P W o)^[t] s ∘ Sum.inl
      = (TapeHostWitness.hostSubUpdate N o)^[t] (s ∘ Sum.inl) := by
  induction t with
  | zero => rfl
  | succ t ih =>
      funext i
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      change compSubUpdate N P W o ((compSubUpdate N P W o)^[t] s) (Sum.inl i) = _
      rw [compSubUpdate_base_eq, ih]

omit [NeZero P] in
/-- **The composite's code region is read-only** ([Inevitability] §2 (S1), embedded through
`Sum.inl`): the base's own guard (`TapeHostWitness.hostSubUpdate_fixes`), transported through
`compSubUpdate_base_eq`. -/
theorem compSubUpdate_fixes :
    Decoupling.Fixes (compSubUpdate N P W o) (Sum.inl '' TapeHostWitness.hostCodeRegion N) := by
  rintro s _ ⟨i, hi, rfl⟩
  rw [compSubUpdate_base_eq]
  exact TapeHostWitness.hostSubUpdate_fixes N o (s ∘ Sum.inl) i hi

/-- **The composite's own loaded state**: the base loaded exactly as `TapeHostWitness.loadHost`
does, the fiber loaded at an arbitrary initial population `v₀`. -/
def compLoad (N P W : ℕ) [NeZero N] (o : ZMod N → Bool) (c : ZMod N)
    (v₀ : Fin P → WeightedFiber.WVec 8 W) : CompMem N P W :=
  Sum.elim (TapeHostWitness.loadHost N o c) (writeFiberCell v₀)

omit [NeZero P] in
private theorem compLoad_base (c : ZMod N) (v₀ : Fin P → WeightedFiber.WVec 8 W) :
    compLoad N P W o c v₀ ∘ Sum.inl = TapeHostWitness.loadHost N o c := rfl

/-! ## The composite's own packing, and its frame -/

/-- **The composite, packed onto a numeral carrier.** The host's own packing
(`TapeHostOverlap.hostIdxEquiv`) on the base cells, an analogous flat packing on the fiber cells, a
clean sum, then `PersistenceCapacity.stateEquiv`'s own `Bool`-cell-to-numeral convention — the same
shape `TapeHostOverlap.hostStateEquiv` uses, over the larger carrier. -/
def compStateEquiv (N P W : ℕ) [NeZero N] :
    CompMem N P W ≃ Fin (2 ^ ((8 + (8 + Nat.size N)) + P * (8 * Nat.size W))) :=
  (Equiv.arrowCongr
      ((Equiv.sumCongr (TapeHostOverlap.hostIdxEquiv N)
          ((Equiv.prodCongr (Equiv.refl (Fin P)) finProdFinEquiv).trans finProdFinEquiv)).trans
        finSumFinEquiv)
      (Equiv.refl Bool)).trans
    (PersistenceCapacity.stateEquiv ((8 + (8 + Nat.size N)) + P * (8 * Nat.size W)))

/-- **The composite's own update, packed.** -/
def compPacked (N P W : ℕ) [NeZero N] (o : ZMod N → Bool) :
    Fin (2 ^ ((8 + (8 + Nat.size N)) + P * (8 * Nat.size W))) →
      Fin (2 ^ ((8 + (8 + Nat.size N)) + P * (8 * Nat.size W))) :=
  SubstrateEmergence.packedUpdate (compStateEquiv N P W) (compSubUpdate N P W o)

/-- **The composite's own frame**: decode the flat state, restrict to the base cells, and read
`TapeHostOverlap.hostFrame` off them unchanged — the fiber cells are never consulted. -/
def compFrame (N P W : ℕ) [NeZero N] (o : ZMod N → Bool) :
    Fin (2 ^ ((8 + (8 + Nat.size N)) + P * (8 * Nat.size W))) →
      Fin (2 ^ TapeHostOverlap.hostFrameBits N) :=
  fun s => TapeHostOverlap.hostFrame N o
    (TapeHostOverlap.hostStateEquiv N ((compStateEquiv N P W).symm s ∘ Sum.inl))

omit [NeZero P] in
/-- **The composite's own frame surjects after one full pass through its own carrier.** Exactly
`TapeHostOverlap.hostFrame_surj_iterate`'s proof: the phase `c` chosen so the loaded orbit's own
closed-form counter (`TapeHostWitness.readCounter_iterate_loadHost`) lands on the target after
however many steps the composite's own carrier size demands — the choice of `c` absorbs the horizon
exactly, so the argument does not depend on what that horizon numerically is. No permutation-
transport argument, and no appeal to periodicity: `compSubUpdate_base_iterate` is the only fact
about the composite's own dynamics this proof consumes. -/
private theorem compFrame_surj_at (K : ℕ) :
    Function.Surjective (fun s : Fin (2 ^ ((8 + (8 + Nat.size N)) + P * (8 * Nat.size W))) =>
      compFrame N P W o ((compPacked N P W o)^[K] s)) := by
  intro y
  have hNne : (N : ℕ) ≠ 0 := NeZero.ne _
  set c : ZMod N := ((y : ℕ) : ZMod N) - 7 - ((K : ℕ) : ZMod N) with hc
  refine ⟨compStateEquiv N P W (compLoad N P W o c (fun _ _ => 0)), ?_⟩
  have hiter : (compPacked N P W o)^[K] (compStateEquiv N P W (compLoad N P W o c (fun _ _ => 0)))
      = compStateEquiv N P W
          ((compSubUpdate N P W o)^[K] (compLoad N P W o c (fun _ _ => 0))) :=
    SubstrateEmergence.packedUpdate_iterate (compStateEquiv N P W) (compSubUpdate N P W o) K _
  have hbase : (compSubUpdate N P W o)^[K] (compLoad N P W o c (fun _ _ => 0)) ∘ Sum.inl
      = (TapeHostWitness.hostSubUpdate N o)^[K] (TapeHostWitness.loadHost N o c) := by
    rw [compSubUpdate_base_iterate, compLoad_base]
  simp only [hiter, compFrame, Equiv.symm_apply_apply, hbase,
    TapeHostOverlap.hostFrame, TapeHostWitness.readCounter_iterate_loadHost]
  apply Fin.ext
  have hval : c + 7 + (K : ℕ) = ((y : ℕ) : ZMod N) := by rw [hc]; ring
  change (c + 7 + (K : ℕ) : ZMod N).val % 2 ^ TapeHostOverlap.hostFrameBits N = (y : ℕ)
  rw [hval]
  have hylt : (y : ℕ) < N := lt_of_lt_of_le y.isLt (Nat.pow_log_le_self 2 hNne)
  rw [ZMod.val_cast_of_lt hylt]
  exact Nat.mod_eq_of_lt y.isLt

omit [NeZero P] in
theorem compFrame_surj_iterate :
    Function.Surjective (fun s : Fin (2 ^ ((8 + (8 + Nat.size N)) + P * (8 * Nat.size W))) =>
      compFrame N P W o
        ((compPacked N P W o)^[2 ^ ((8 + (8 + Nat.size N)) + P * (8 * Nat.size W))] s)) :=
  compFrame_surj_at o _

/-! ## The composite is a member of `𝒮_L` -/

/-- **The tight numeric bound `3 · log 6 ≤ 6`**, `TapeHostOverlap.log_three_div_half_le_two`'s
proof, re-derived: that lemma is private, and the numeral is short enough to redo directly. -/
private theorem log_three_div_half_le_two' : Real.log ((3 : ℝ) / (1 / 2)) ≤ 2 := by
  have h1 := Real.exp_one_gt_d9
  have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
  have hexp2 : (6 : ℝ) ≤ Real.exp 2 := by rw [h2]; nlinarith [h1]
  have hlog6 : Real.log 6 ≤ 2 := (Real.log_le_iff_le_exp (by norm_num)).mpr hexp2
  have heq : (3 / (1 / 2) : ℝ) = 6 := by norm_num
  rw [heq]; exact hlog6

omit [NeZero P] in
/-- **The composite is a member of `𝒮_L`**, at any window-deviation `Profile` and any `(K, gTS)`
clearing `8 + capacity(⌈log₂(gTS+1)⌉)`. Every field but `s1` is
`TapeHostWitness.tapeHost_substrateL`'s own: none of `SubstrateClass.Substrate`'s or `SubstrateL`'s
other fields is typed against the update or the code region, so the base's own proof terms transport
verbatim. -/
theorem comp_substrateL {S : ℝ} {ρ Wp : Fin 8 → ℝ} (h : TapeHostObservability.Profile o S ρ Wp)
    (K : ℝ) (gTS : ℕ) (hK : (8 : ℝ) + GodelInternalization.capacity (Nat.clog 2 (gTS + 1)) ≤ K)
    {η τ : ℝ} (hη : 0 ≤ η) (hτ : 2 * η ≤ τ) :
    SubstrateClass.SubstrateL (compSubUpdate N P W o) (Sum.inl '' TapeHostWitness.hostCodeRegion N)
      3 K (2 * K) 1 2 3 (1 / 2) 8 gTS True True True True
      (TapeHostWitness.HostRealizable N o) (LearningWitness.ChainWindowBudget 8 η τ) := by
  have hSL := TapeHostWitness.tapeHost_substrateL N o h K gTS hK hη hτ
  exact
    { s1 := compSubUpdate_fixes o
      s2 := hSL.s2
      s3 := hSL.s3
      realizability := hSL.realizability
      windowSufficiency := hSL.windowSufficiency
      assumptionA := hSL.assumptionA
      benignSeparation := hSL.benignSeparation
      e1 := hSL.e1 }

/-! ## The composite is a member of `𝒮_E` -/

omit [NeZero P] in
/-- **The composite is a member of `𝒮_E`**, at the same coupled `(K, gTS)` — `SubstrateEmergence.
substrateE_of_emergence` at the composite's own packing (`compStateEquiv`) and frame (`compFrame`),
surjective off the composite's own packed iterate (`compFrame_surj_iterate`). -/
theorem comp_substrateE (K : ℝ) (gTS : ℕ)
    (hK : (8 : ℝ) + GodelInternalization.capacity (Nat.clog 2 (gTS + 1)) ≤ K)
    (hE : SubstrateEmergence.GrownGuestReachesThresholdAt (TapeHostOverlap.hostFrameBits N) gTS) :
    SubstrateClass.SubstrateE (compSubUpdate N P W o) (Sum.inl '' TapeHostWitness.hostCodeRegion N)
      3 K (2 * K) 1 2 3 (1 / 2) 8 gTS True True True True
      (SubstrateEmergence.GrowsLawfulGuestOf (compPacked N P W o) (compFrame N P W o))
      (SubstrateEmergence.GrownGuestReachesThresholdAt (TapeHostOverlap.hostFrameBits N) gTS) := by
  have hK8 : (8 : ℝ) ≤ K := by
    have hcap_nonneg : (0 : ℝ) ≤ (GodelInternalization.capacity (Nat.clog 2 (gTS + 1)) : ℝ) :=
      Nat.cast_nonneg _
    linarith
  have hlog := log_three_div_half_le_two'
  exact SubstrateEmergence.substrateE_of_emergence (compSubUpdate N P W o)
    (Sum.inl '' TapeHostWitness.hostCodeRegion N) (compSubUpdate_fixes o)
    (compStateEquiv N P W) (compFrame N P W o) (compFrame_surj_iterate o)
    3 K (2 * K) 1 2 3 (1 / 2) 8 gTS True True True True
    ⟨by linarith, le_refl _, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num,
      by norm_num⟩
    ⟨hK, trivial, trivial, trivial, trivial⟩ hE

/-! ## Survival by redundancy ([Inevitability] §6 Theorem 6.6(v′), its absorption half) -/

omit [NeZero N] in
/-- **The redundancy route, on the composite's own fiber.** An untouched copy exists
(`TapeHostFiber.exists_untouched_copy_tapeHost`, from the profile's own bound on the base's noise
count within a damage schedule confined to `TapeHostFiber.tapeStream`'s own firing), and that
copy's reading under the damaged run is exactly the single undamaged floored fiber's
(`RedundantFiber.compRun_eq_wRunFrom_of_untouched`, definitional, for any schedule and any weight
budget). No margin enters: this copy-level identity is the redundancy Proposition 6.1(iii)'s third
sufficient condition rides on, not the constant decoded value that condition speaks of. -/
theorem comp_carries_survival {S : ℝ} {ρ Wp : Fin 8 → ℝ}
    (h : TapeHostObservability.Profile o S ρ Wp) {η : ℝ} (hρ0 : ρ 0 = 2 * η - 1)
    (c : ZMod N) {n cnt : ℕ} {H : Finset ℕ} (hH : H ⊆ Finset.range n)
    (hgate : DamageGate.NoiseGated 8 (TapeHostFiber.tapeStream o c) H)
    (col : ℕ → Finset (Fin P)) (hcol : ∀ t, (col t).card ≤ cnt)
    (hP : (cnt : ℝ) * ((n : ℝ) * η + Wp 0 / 2) < (P : ℝ))
    (v₀ : Fin P → WeightedFiber.WVec 8 W) (land : ℕ → Fin P → WeightedFiber.WVec 8 W) :
    ∃ i₀ : Fin P, (∀ t ∈ H, i₀ ∉ col t) ∧ ∀ t,
      WeightedFiber.compRun W (WitnessMixture.witMiss 8 (TapeHostFiber.tapeStream o c))
          v₀ H col land t i₀
        = WeightedFiber.wRunFrom W
            (WeightedFiber.missFit (WitnessMixture.witMiss 8 (TapeHostFiber.tapeStream o c)))
            (v₀ i₀) t := by
  obtain ⟨i₀, hi₀⟩ := TapeHostFiber.exists_untouched_copy_tapeHost o h hρ0 c hH hgate col hcol hP
  exact ⟨i₀, hi₀, fun t =>
    WeightedFiber.compRun_eq_wRunFrom_of_untouched W _ v₀ H col land hi₀ t⟩

/-! ## The capstone: a member of both route-classes, carrying survival -/

/-- **A member of both route-classes carries survival, by redundancy, at a horizon** —
[Inevitability] §5 Theorem 5.8's boundary paragraph, sharpened: a permutation host cannot carry
the MARGIN form of survival (*Guests* Law 4), but the composite here is not a permutation, and it
carries the REDUNDANCY form (Proposition 6.1(iii)'s third condition) at the coupled `(K, gTS)` that
also puts it in `𝒮_E ∩ 𝒮_L`. Conditional on the damage model (D1)/(D2), the gate confined to the
base's own firing — not lifetime-free (`TapeHostFiber.tapeStream_fires_forever`). One witness; the
class-level question stays. -/
theorem tapeHost_carries_survival :
    ∃ gTS, ∀ (N : ℕ) [NeZero N] (o : ZMod N → Bool) (P W : ℕ) [NeZero P]
      (S : ℝ) (ρ Wp : Fin 8 → ℝ), TapeHostObservability.Profile o S ρ Wp →
      ∀ (η τ : ℝ), 0 ≤ η → 2 * η ≤ τ → ρ 0 = 2 * η - 1 → ∀ (K : ℝ),
      (8 : ℝ) + GodelInternalization.capacity (Nat.clog 2 (gTS + 1)) ≤ K →
      CategoricalThreshold.hostsAt (TapeHostOverlap.hostFrameBits N) gTS →
      SubstrateClass.SubstrateE (compSubUpdate N P W o)
        (Sum.inl '' TapeHostWitness.hostCodeRegion N)
        3 K (2 * K) 1 2 3 (1 / 2) 8 gTS True True True True
        (SubstrateEmergence.GrowsLawfulGuestOf (compPacked N P W o) (compFrame N P W o))
        (SubstrateEmergence.GrownGuestReachesThresholdAt (TapeHostOverlap.hostFrameBits N) gTS) ∧
      SubstrateClass.SubstrateL (compSubUpdate N P W o)
        (Sum.inl '' TapeHostWitness.hostCodeRegion N)
        3 K (2 * K) 1 2 3 (1 / 2) 8 gTS True True True True
        (TapeHostWitness.HostRealizable N o) (LearningWitness.ChainWindowBudget 8 η τ) ∧
      ∀ (c : ZMod N) {n cnt : ℕ} {H : Finset ℕ}, H ⊆ Finset.range n →
        DamageGate.NoiseGated 8 (TapeHostFiber.tapeStream o c) H →
        ∀ (col : ℕ → Finset (Fin P)), (∀ t, (col t).card ≤ cnt) →
        (cnt : ℝ) * ((n : ℝ) * η + Wp 0 / 2) < (P : ℝ) →
        ∀ (v₀ : Fin P → WeightedFiber.WVec 8 W) (land : ℕ → Fin P → WeightedFiber.WVec 8 W),
        ∃ i₀ : Fin P, (∀ t ∈ H, i₀ ∉ col t) ∧ ∀ t,
          WeightedFiber.compRun W (WitnessMixture.witMiss 8 (TapeHostFiber.tapeStream o c))
              v₀ H col land t i₀
            = WeightedFiber.wRunFrom W
                (WeightedFiber.missFit (WitnessMixture.witMiss 8 (TapeHostFiber.tapeStream o c)))
                (v₀ i₀) t := by
  obtain ⟨gTS, hgTS⟩ := SubstrateEmergence.grownGuestReachesThresholdAt_uniform
  refine ⟨gTS, fun N _ o P W _ S ρ Wp h η τ hη hτ hρ0 K hK _hhost => ?_⟩
  refine ⟨comp_substrateE o K gTS hK (hgTS (TapeHostOverlap.hostFrameBits N)),
    comp_substrateL o h K gTS hK hη hτ, ?_⟩
  intro c n cnt H hH hgate col hcol hP v₀ land
  exact comp_carries_survival o h hρ0 c hH hgate col hcol hP v₀ land

end TapeHostSurvival

/-- info: 'TapeHostSurvival.comp_substrateL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TapeHostSurvival.comp_substrateL

/-- info: 'TapeHostSurvival.comp_substrateE' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TapeHostSurvival.comp_substrateE

/-- info: 'TapeHostSurvival.comp_carries_survival' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TapeHostSurvival.comp_carries_survival

/-- info: 'TapeHostSurvival.tapeHost_carries_survival' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TapeHostSurvival.tapeHost_carries_survival
