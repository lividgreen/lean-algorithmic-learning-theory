/-
Copyright (c) 2026 Mykola Palamarchuk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mykola Palamarchuk
-/
module

public import ALT.BlockPairHost

/-!
# The finite autonomous host, over an arbitrary observation sequence

[Inevitability] §5 Theorem 5.8.

`BlockPairHost.lean` wraps the certified block-pair design into a finite autonomous host: a
length-`8` window over a counter valued in `ZMod N`, stepped by `NoisyWindowChain.noisyStep` on a
tape bit read off the design's own observation sequence, at a fixed period
`N := (2 * (2 * M)) * 24`. This module restates that construction with the observation sequence
`o : ZMod N → Bool` and the modulus `N` themselves as parameters, in place of the certified design
and its specific period — the block-pair pipeline's host layer with its sequence made a parameter.

Every proof below is `BlockPairHost.lean`'s own proof, verbatim, with `designObs M` read as the
parameter `o` and the certified period read as `N`. The pure rotation lemmas `windowXor`, `rot8`,
`rot8_iterate_dvd`, `windowXor_noisyStep` carry no dependence on the design or its period even in
`BlockPairHost.lean` (they are stated before that file introduces its own period), so this module
consumes them directly by name rather than restating or relocating them.

## Main results

* `tape`, `tapeUpdate` — the observation sequence read as the tape bit, and one step of the host.
* `designWindow` — the sequence's own length-`8` window ending at a counter, oldest coordinate
  first.
* `tapeUpdate_iterate_designWindow` — **the designed orbit**: started at its own window, the
  host's state after `t` steps is the sequence's window ending `t` further along.
* `tapeUpdate_iterate_last`, `tapeUpdate_iterate_period` — the orbit's last coordinate reproduces
  the sequence at the counter, and the designed state returns after one full period `N`.
* `windowXor_tapeUpdate_iterate` — the difference-rotation lemma, carried along the host's own
  orbit.
* `tapeUpdate_iterate_period_all` — **the parallel-cycle theorem**: at `8 ∣ N`, every state of the
  host, not only the designed one, returns to itself after one full period.

## Scope

No claim about the observation sequence's own statistical or correlation content is stated here —
that is a hypothesis of every downstream module, never discharged here. This file states only what
the host does with `o` once it is read as a tape: it reproduces it, and (at `8 ∣ N`) every state of
the machine is periodic.
-/


@[expose] public section

namespace TapeHost

open NoisyWindowChain

variable {N : ℕ} [NeZero N] (o : ZMod N → Bool)

/-- The tape's own bit at `u`: whether the sequence agrees with its value eight steps back. Solved
for `tape`, this is exactly the bit the noisy window chain's recursion needs in order to carry the
sequence from `u - 8` to `u`. -/
def tape (u : ZMod N) : Bool := o u == o (u - 8)

/-- One step of the finite autonomous host: the window steps by the noisy window chain's own
update on the tape bit at the counter's next position, while the counter itself advances by one. -/
def tapeUpdate : (Fin 8 → Bool) × ZMod N → (Fin 8 → Bool) × ZMod N :=
  fun p => (NoisyWindowChain.noisyStep 8 p.1 (tape o (p.2 + 1)), p.2 + 1)

/-- The sequence's own length-`8` window ending at counter `c`: the oldest coordinate first. -/
def designWindow (c : ZMod N) : Fin 8 → Bool :=
  fun i => o (c - 7 + ((i : ℕ) : ZMod N))

/-! ## The designed orbit -/

private lemma xor_not_beq (a b : Bool) : xor (!b) (a == b) = a := by
  cases a <;> cases b <;> decide

omit [NeZero N] in
private theorem tapeUpdate_designWindow (c : ZMod N) :
    tapeUpdate o (designWindow o c, c) = (designWindow o (c + 1), c + 1) := by
  change (NoisyWindowChain.noisyStep 8 (designWindow o c) (tape o (c + 1)), c + 1)
    = (designWindow o (c + 1), c + 1)
  congr 1
  funext i
  change NoisyWindowChain.noisyStep 8 (designWindow o c) (tape o (c + 1)) i
    = o (c + 1 - 7 + ((i : ℕ) : ZMod N))
  rw [NoisyWindowChain.noisyStep, NoisyWindowChain.windowMap]
  by_cases h : (i : ℕ) + 1 < 8
  · rw [ite_eq_left h, dite_eq_left h]
    change o (c - 7 + (((⟨(i : ℕ) + 1, h⟩ : Fin 8) : ℕ) : ZMod N))
      = o (c + 1 - 7 + ((i : ℕ) : ZMod N))
    congr 1
    push_cast
    ring
  · rw [ite_eq_right h, dite_eq_right h]
    have hi7 : (i : ℕ) = 7 := by have := i.isLt; omega
    change xor (!(designWindow o c 0)) (tape o (c + 1))
      = o (c + 1 - 7 + ((i : ℕ) : ZMod N))
    have h0 : designWindow o c 0 = o (c - 7) := by
      change o (c - 7 + ((0 : ℕ) : ZMod N)) = o (c - 7)
      congr 1; push_cast; ring
    have htape : tape o (c + 1) = (o (c + 1) == o (c - 7)) := by
      change (o (c + 1) == o (c + 1 - 8)) = _
      congr 2
      ring
    have hrhs : c + 1 - 7 + ((i : ℕ) : ZMod N) = c + 1 := by
      rw [hi7]; push_cast; ring
    rw [h0, htape, hrhs]
    exact xor_not_beq (o (c + 1)) (o (c - 7))

omit [NeZero N] in
/-- **The designed orbit.** Started at the sequence's own window ending at counter `c`, the host's
state after `t` steps is the sequence's window ending `t` further along. -/
theorem tapeUpdate_iterate_designWindow (c : ZMod N) (t : ℕ) :
    (tapeUpdate o)^[t] (designWindow o c, c)
      = (designWindow o (c + (t : ZMod N)), c + (t : ZMod N)) := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [Function.iterate_succ_apply', ih, tapeUpdate_designWindow]
    have hstep : c + (t : ZMod N) + 1 = c + ((t + 1 : ℕ) : ZMod N) := by push_cast; ring
    rw [hstep]

omit [NeZero N] in
private lemma designWindow_last (c' : ZMod N) :
    designWindow o c' 7 = o c' := by
  have h7 : ((7 : Fin 8) : ℕ) = 7 := by decide
  change o (c' - 7 + (((7 : Fin 8) : ℕ) : ZMod N)) = o c'
  rw [h7]
  congr 1
  push_cast
  ring

omit [NeZero N] in
/-- The window's last coordinate along the sequence's own orbit reproduces the sequence at the
counter: the sequence emitted along the orbit *is* `o`. -/
theorem tapeUpdate_iterate_last (c : ZMod N) (t : ℕ) :
    ((tapeUpdate o)^[t] (designWindow o c, c)).1 7 = o (c + (t : ZMod N)) := by
  rw [tapeUpdate_iterate_designWindow]
  exact designWindow_last o _

omit [NeZero N] in
/-- **The designed state returns after one full period.** Automatic in `ZMod N`, since `N` itself
casts to `0` there. -/
theorem tapeUpdate_iterate_period (c : ZMod N) :
    (tapeUpdate o)^[N] (designWindow o c, c) = (designWindow o c, c) := by
  rw [tapeUpdate_iterate_designWindow, ZMod.natCast_self, add_zero]

/-! ## Every state is periodic -/

omit [NeZero N] in
private theorem tapeUpdate_iterate_snd (c : ZMod N) (w : Fin 8 → Bool) (t : ℕ) :
    ((tapeUpdate o)^[t] (w, c)).2 = c + (t : ZMod N) := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [Function.iterate_succ_apply']
    change ((tapeUpdate o)^[t] (w, c)).2 + 1 = c + ((t + 1 : ℕ) : ZMod N)
    rw [ih]
    push_cast
    ring

omit [NeZero N] in
private theorem tapeUpdate_iterate_fst_succ (c : ZMod N) (w : Fin 8 → Bool) (t : ℕ) :
    ((tapeUpdate o)^[t + 1] (w, c)).1
      = NoisyWindowChain.noisyStep 8 ((tapeUpdate o)^[t] (w, c)).1
          (tape o (c + (t : ZMod N) + 1)) := by
  rw [Function.iterate_succ_apply']
  change NoisyWindowChain.noisyStep 8 ((tapeUpdate o)^[t] (w, c)).1
      (tape o (((tapeUpdate o)^[t] (w, c)).2 + 1)) = _
  rw [tapeUpdate_iterate_snd]

private theorem xor_right_cancel {a b c : Bool} (h : xor a c = xor b c) : a = b := by
  cases a <;> cases b <;> cases c <;> simp_all

omit [NeZero N] in
/-- **The difference-rotation lemma, carried along the host's own orbit.** Two states sharing a
counter differ, after `t` steps, by `BlockPairHost.rot8` iterated `t` times on their starting
difference. -/
theorem windowXor_tapeUpdate_iterate (c : ZMod N) (w1 w2 : Fin 8 → Bool) (t : ℕ) :
    BlockPairHost.windowXor ((tapeUpdate o)^[t] (w1, c)).1 ((tapeUpdate o)^[t] (w2, c)).1
      = (BlockPairHost.rot8)^[t] (BlockPairHost.windowXor w1 w2) := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [tapeUpdate_iterate_fst_succ, tapeUpdate_iterate_fst_succ, BlockPairHost.windowXor_noisyStep,
      ih, Function.iterate_succ_apply']

omit [NeZero N] in
/-- **The parallel-cycle theorem.** At `8 ∣ N`, every state of the host — not only the designed
one — lies on a cycle of the full period: the difference from the designed orbit evolves by
`BlockPairHost.rot8` alone (`windowXor_tapeUpdate_iterate`), and `rot8`'s own period divides `8`,
which divides `N` by hypothesis, so the difference — and with it the state itself — returns
unchanged. -/
theorem tapeUpdate_iterate_period_all (h8 : 8 ∣ N) (w : Fin 8 → Bool) (c : ZMod N) :
    (tapeUpdate o)^[N] (w, c) = (w, c) := by
  have hdiff := windowXor_tapeUpdate_iterate o c w (designWindow o c) N
  rw [BlockPairHost.rot8_iterate_dvd h8] at hdiff
  have hdesign := tapeUpdate_iterate_period o c
  have hfst_design : ((tapeUpdate o)^[N] (designWindow o c, c)).1 = designWindow o c :=
    congrArg Prod.fst hdesign
  rw [hfst_design] at hdiff
  simp only [id_eq] at hdiff
  have hfst : ((tapeUpdate o)^[N] (w, c)).1 = w := by
    funext i
    have hxi := congrFun hdiff i
    simp only [BlockPairHost.windowXor] at hxi
    exact xor_right_cancel hxi
  have hsnd : ((tapeUpdate o)^[N] (w, c)).2 = c := by
    rw [tapeUpdate_iterate_snd, ZMod.natCast_self, add_zero]
  exact Prod.ext hfst hsnd

end TapeHost
