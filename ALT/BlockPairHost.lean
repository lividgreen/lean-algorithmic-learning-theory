/-
Copyright (c) 2026 Mykola Palamarchuk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mykola Palamarchuk
-/
import ALT.BlockPairProfile
import ALT.NoisyWindowChain

/-!
# The finite autonomous host carrying the certified block-pair design

`BlockPairProfile.lean` certifies a single period-`(2 * (2 * M)) * 24` sequence of `±1` values.
This file wraps that sequence into a **finite autonomous host**: a length-`8` window over a
counter valued in `ZMod ((2 * (2 * M)) * 24)`, stepped by `NoisyWindowChain.noisyStep` on a tape
bit read off the design itself rather than supplied from outside.

The tape bit at `u` is defined to be exactly the bit the noisy window chain's own recursion needs
in order to carry the design forward — `hostTape` compares the design's value at `u` against its
value eight steps back, and the identity that makes this work is a plain two-`Bool` tautology.
Started at the design's own length-`8` window, the host therefore reproduces the design along its
orbit exactly (`hostUpdate_iterate_designWindow`), and
every state of the host — not only the designed one — lies on a cycle of the full period: the
difference between any two orbits sharing a counter evolves by a fixed rotation of the window
coordinates, independent of the tape (`windowXor_hostUpdate_iterate`), and that rotation's own
period divides `8`, which divides the design's period.

## Main results

* `designObs`, `hostTape`, `hostUpdate` — the design read as a Boolean observation, the tape bit
  it supplies, and one step of the host.
* `designWindow` — the design's own length-`8` window ending at a counter, oldest coordinate first.
* `hostUpdate_iterate_designWindow` — **the designed orbit**: started at its own window, the host's
  state after `t` steps is the design's window ending `t` further along.
* `hostUpdate_iterate_last`, `hostUpdate_iterate_period` — the orbit's last coordinate reproduces
  the design at the counter, and the designed state returns after one full period.
* `windowXor`, `rot8` — the coordinatewise difference of two windows, and the fixed rotation of
  `Fin 8`.
* `windowXor_noisyStep` — **the difference-rotation lemma**: one step of the noisy window chain,
  applied to two windows sharing a noise bit, moves their difference by `rot8` alone.
* `windowXor_hostUpdate_iterate` — the same fact carried along the host's own orbit.
* `hostUpdate_iterate_period_all` — **the parallel-cycle theorem**: every state of the host, not
  only the designed one, returns to itself after one full period.

## Scope

No claim about the design's own statistical or correlation content is repeated here — that is
`BlockPairProfile.lean`'s business. This file states only what the host does with the design once
it is read as a tape: it reproduces it, and every state of the machine is periodic.
-/

namespace BlockPairHost

open BlockPairProfile

/-! ## The pure rotation of `Fin 8` -/

/-- The coordinatewise difference of two windows. -/
def windowXor (w1 w2 : Fin 8 → Bool) : Fin 8 → Bool := fun i => xor (w1 i) (w2 i)

/-- The fixed rotation of window coordinates: `v ↦ (v 1, …, v 7, v 0)`, `windowMap`'s own shape
without the final complement. -/
def rot8 (v : Fin 8 → Bool) : Fin 8 → Bool :=
  fun i => if h : (i : ℕ) + 1 < 8 then v ⟨(i : ℕ) + 1, h⟩ else v ⟨0, by norm_num⟩

private lemma rot8_iterate_val (t : ℕ) (v : Fin 8 → Bool) (i : Fin 8) :
    (rot8)^[t] v i = v ⟨(i.val + t) % 8, Nat.mod_lt _ (by norm_num)⟩ := by
  induction t generalizing i with
  | zero =>
    have hi := i.isLt
    rw [Function.iterate_zero_apply]
    congr 1
    apply Fin.ext
    change i.val = (i.val + 0) % 8
    omega
  | succ t ih =>
    rw [Function.iterate_succ_apply', rot8]
    by_cases h : (i : ℕ) + 1 < 8
    · rw [dif_pos h, ih]
      congr 1
      apply Fin.ext
      change (i.val + 1 + t) % 8 = (i.val + (t + 1)) % 8
      omega
    · rw [dif_neg h, ih]
      have hi := i.isLt
      have hi7 : i.val = 7 := by omega
      congr 1
      apply Fin.ext
      change (0 + t) % 8 = (i.val + (t + 1)) % 8
      omega

/-- **`rot8` has order dividing `8`.** -/
theorem rot8_iterate_eight : (rot8)^[8] = id := by
  funext v
  funext i
  rw [rot8_iterate_val 8 v i]
  have hi := i.isLt
  congr 1
  apply Fin.ext
  change (i.val + 8) % 8 = i.val
  omega

/-- **`rot8` iterated any multiple of `8` times is the identity.** -/
theorem rot8_iterate_dvd {n : ℕ} (h8 : 8 ∣ n) : (rot8)^[n] = id := by
  obtain ⟨q, hq⟩ := h8
  rw [hq, Function.iterate_mul, rot8_iterate_eight]
  funext v
  simp

/-- **The difference-rotation lemma.** One step of the noisy window chain, applied to two windows
under the *same* noise bit, moves their coordinatewise difference by `rot8` alone: the tape bit
written to the last coordinate cancels, and the complement `windowMap` applies there cancels too. -/
theorem windowXor_noisyStep (w1 w2 : Fin 8 → Bool) (b : Bool) :
    windowXor (NoisyWindowChain.noisyStep 8 w1 b) (NoisyWindowChain.noisyStep 8 w2 b)
      = rot8 (windowXor w1 w2) := by
  funext i
  change xor (NoisyWindowChain.noisyStep 8 w1 b i) (NoisyWindowChain.noisyStep 8 w2 b i) = _
  rw [NoisyWindowChain.noisyStep, NoisyWindowChain.noisyStep, rot8]
  by_cases h : (i : ℕ) + 1 < 8
  · rw [if_pos h, if_pos h, dif_pos h, NoisyWindowChain.windowMap, NoisyWindowChain.windowMap,
      dif_pos h, dif_pos h]
    rfl
  · rw [if_neg h, if_neg h, dif_neg h, NoisyWindowChain.windowMap, NoisyWindowChain.windowMap,
      dif_neg h, dif_neg h]
    change xor (xor (!(w1 0)) b) (xor (!(w2 0)) b) = xor (w1 0) (w2 0)
    cases w1 0 <;> cases w2 0 <;> cases b <;> decide

/-! ## The design, its tape, and one step of the host -/

variable (M : ℕ) [NeZero (2 * (2 * M))]

/-- The certified block-pair design, read as a Boolean observation: `true` exactly where the
design's value is `-1`. -/
def designObs (u : ZMod (2 * (2 * M) * 24)) : Bool :=
  decide (blockSeq wordU wordV (blockSign (2 * (2 * M))) u = -1)

/-- The tape's own bit at `u`: whether the design agrees with its value eight steps back. Solved
for `hostTape`, this is exactly the bit the noisy window chain's recursion needs to carry the
design from `u - 8` to `u`. -/
def hostTape (u : ZMod (2 * (2 * M) * 24)) : Bool :=
  designObs M u == designObs M (u - 8)

/-- One step of the finite autonomous host: the window steps by the noisy window chain's own
update on the tape bit at the counter's next position, while the counter itself advances by one. -/
def hostUpdate :
    (Fin 8 → Bool) × ZMod (2 * (2 * M) * 24) → (Fin 8 → Bool) × ZMod (2 * (2 * M) * 24) :=
  fun p => (NoisyWindowChain.noisyStep 8 p.1 (hostTape M (p.2 + 1)), p.2 + 1)

/-- The design's own length-`8` window ending at counter `c`: the oldest coordinate first. -/
def designWindow (c : ZMod (2 * (2 * M) * 24)) : Fin 8 → Bool :=
  fun i => designObs M (c - 7 + ((i : ℕ) : ZMod (2 * (2 * M) * 24)))

/-! ## The designed orbit -/

private lemma xor_not_beq (a b : Bool) : xor (!b) (a == b) = a := by
  cases a <;> cases b <;> decide

private theorem hostUpdate_designWindow (c : ZMod (2 * (2 * M) * 24)) :
    hostUpdate M (designWindow M c, c) = (designWindow M (c + 1), c + 1) := by
  change (NoisyWindowChain.noisyStep 8 (designWindow M c) (hostTape M (c + 1)), c + 1)
    = (designWindow M (c + 1), c + 1)
  congr 1
  funext i
  change NoisyWindowChain.noisyStep 8 (designWindow M c) (hostTape M (c + 1)) i
    = designObs M (c + 1 - 7 + ((i : ℕ) : ZMod (2 * (2 * M) * 24)))
  rw [NoisyWindowChain.noisyStep, NoisyWindowChain.windowMap]
  by_cases h : (i : ℕ) + 1 < 8
  · rw [if_pos h, dif_pos h]
    change designObs M (c - 7 + (((⟨(i : ℕ) + 1, h⟩ : Fin 8) : ℕ) : ZMod (2 * (2 * M) * 24)))
      = designObs M (c + 1 - 7 + ((i : ℕ) : ZMod (2 * (2 * M) * 24)))
    congr 1
    push_cast
    ring
  · rw [if_neg h, dif_neg h]
    have hi7 : (i : ℕ) = 7 := by have := i.isLt; omega
    change xor (!(designWindow M c 0)) (hostTape M (c + 1))
      = designObs M (c + 1 - 7 + ((i : ℕ) : ZMod (2 * (2 * M) * 24)))
    have h0 : designWindow M c 0 = designObs M (c - 7) := by
      change designObs M (c - 7 + ((0 : ℕ) : ZMod (2 * (2 * M) * 24))) = designObs M (c - 7)
      congr 1; push_cast; ring
    have htape : hostTape M (c + 1) = (designObs M (c + 1) == designObs M (c - 7)) := by
      change (designObs M (c + 1) == designObs M (c + 1 - 8)) = _
      congr 2
      ring
    have hrhs : c + 1 - 7 + ((i : ℕ) : ZMod (2 * (2 * M) * 24)) = c + 1 := by
      rw [hi7]; push_cast; ring
    rw [h0, htape, hrhs]
    exact xor_not_beq (designObs M (c + 1)) (designObs M (c - 7))

/-- **The designed orbit.** Started at the design's own window ending at counter `c`, the host's
state after `t` steps is the design's window ending `t` further along. -/
theorem hostUpdate_iterate_designWindow (c : ZMod (2 * (2 * M) * 24)) (t : ℕ) :
    (hostUpdate M)^[t] (designWindow M c, c)
      = (designWindow M (c + (t : ZMod _)), c + (t : ZMod _)) := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [Function.iterate_succ_apply', ih, hostUpdate_designWindow]
    have hstep : c + (t : ZMod (2 * (2 * M) * 24)) + 1
        = c + ((t + 1 : ℕ) : ZMod (2 * (2 * M) * 24)) := by
      push_cast; ring
    rw [hstep]

private lemma designWindow_last (c' : ZMod (2 * (2 * M) * 24)) :
    designWindow M c' 7 = designObs M c' := by
  have h7 : ((7 : Fin 8) : ℕ) = 7 := by decide
  change designObs M (c' - 7 + (((7 : Fin 8) : ℕ) : ZMod (2 * (2 * M) * 24))) = designObs M c'
  rw [h7]
  congr 1
  push_cast
  ring

/-- The window's last coordinate along the design's own orbit reproduces the design at the
counter: the sequence emitted along the orbit *is* the design. -/
theorem hostUpdate_iterate_last (c : ZMod (2 * (2 * M) * 24)) (t : ℕ) :
    ((hostUpdate M)^[t] (designWindow M c, c)).1 7 = designObs M (c + (t : ZMod _)) := by
  rw [hostUpdate_iterate_designWindow]
  exact designWindow_last M _

/-- **The designed state returns after one full period.** Automatic in `ZMod ((2 * (2 * M)) *
24)`, since the period itself casts to `0` there. -/
theorem hostUpdate_iterate_period (c : ZMod (2 * (2 * M) * 24)) :
    (hostUpdate M)^[2 * (2 * M) * 24] (designWindow M c, c) = (designWindow M c, c) := by
  rw [hostUpdate_iterate_designWindow, ZMod.natCast_self, add_zero]

/-! ## Every state is periodic -/

private theorem hostUpdate_iterate_snd (c : ZMod (2 * (2 * M) * 24)) (w : Fin 8 → Bool) (t : ℕ) :
    ((hostUpdate M)^[t] (w, c)).2 = c + (t : ZMod (2 * (2 * M) * 24)) := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [Function.iterate_succ_apply']
    change ((hostUpdate M)^[t] (w, c)).2 + 1
      = c + ((t + 1 : ℕ) : ZMod (2 * (2 * M) * 24))
    rw [ih]
    push_cast
    ring

private theorem hostUpdate_iterate_fst_succ (c : ZMod (2 * (2 * M) * 24)) (w : Fin 8 → Bool)
    (t : ℕ) :
    ((hostUpdate M)^[t + 1] (w, c)).1
      = NoisyWindowChain.noisyStep 8 ((hostUpdate M)^[t] (w, c)).1
          (hostTape M (c + (t : ZMod (2 * (2 * M) * 24)) + 1)) := by
  rw [Function.iterate_succ_apply']
  change NoisyWindowChain.noisyStep 8 ((hostUpdate M)^[t] (w, c)).1
      (hostTape M (((hostUpdate M)^[t] (w, c)).2 + 1)) = _
  rw [hostUpdate_iterate_snd]

private theorem xor_right_cancel {a b c : Bool} (h : xor a c = xor b c) : a = b := by
  cases a <;> cases b <;> cases c <;> simp_all

/-- **The difference-rotation lemma, carried along the host's own orbit.** Two states sharing a
counter differ, after `t` steps, by `rot8` iterated `t` times on their starting difference. -/
theorem windowXor_hostUpdate_iterate (c : ZMod (2 * (2 * M) * 24)) (w1 w2 : Fin 8 → Bool)
    (t : ℕ) :
    windowXor ((hostUpdate M)^[t] (w1, c)).1 ((hostUpdate M)^[t] (w2, c)).1
      = (rot8)^[t] (windowXor w1 w2) := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [hostUpdate_iterate_fst_succ, hostUpdate_iterate_fst_succ, windowXor_noisyStep, ih,
      Function.iterate_succ_apply']

/-- **The parallel-cycle theorem.** Every state of the host — not only the designed one — lies on
a cycle of the full period: the difference from the designed orbit evolves by `rot8` alone
(`windowXor_hostUpdate_iterate`), and `rot8`'s own period divides `8`, which divides the design's
period, so the difference — and with it the state itself — returns unchanged. -/
theorem hostUpdate_iterate_period_all (w : Fin 8 → Bool) (c : ZMod (2 * (2 * M) * 24)) :
    (hostUpdate M)^[2 * (2 * M) * 24] (w, c) = (w, c) := by
  have hdiff := windowXor_hostUpdate_iterate M c w (designWindow M c) (2 * (2 * M) * 24)
  have hdvd : (8 : ℕ) ∣ 2 * (2 * M) * 24 := ⟨2 * (2 * M) * 3, by ring⟩
  rw [rot8_iterate_dvd hdvd] at hdiff
  have hdesign := hostUpdate_iterate_period M c
  have hfst_design : ((hostUpdate M)^[2 * (2 * M) * 24] (designWindow M c, c)).1
      = designWindow M c := congrArg Prod.fst hdesign
  rw [hfst_design] at hdiff
  simp only [id_eq] at hdiff
  have hfst : ((hostUpdate M)^[2 * (2 * M) * 24] (w, c)).1 = w := by
    funext i
    have hxi := congrFun hdiff i
    simp only [windowXor] at hxi
    exact xor_right_cancel hxi
  have hsnd : ((hostUpdate M)^[2 * (2 * M) * 24] (w, c)).2 = c := by
    rw [hostUpdate_iterate_snd, ZMod.natCast_self, add_zero]
  exact Prod.ext hfst hsnd

end BlockPairHost
