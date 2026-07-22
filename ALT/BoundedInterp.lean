/-
Copyright (c) 2026 Mykola Palamarchuk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mykola Palamarchuk
-/
import ALT.TimeCost
import Mathlib.Data.Nat.Size
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

-- Formal-check file, not Mathlib-destined: opt out of the house-style header linter.
set_option linter.style.header false

/-!
# A small-step interpreter for `Nat.Partrec.Code`, on configuration numerals

Provenance: [Decoupling] §4.5 (the evaluator a general representation functor must carry) and §6.3
(the bounded checker that runs inside a capacity). Both want a universal evaluator that is
*structurally presented* — built from constructors, so that its resource use can be read off —
rather than obtained as an existence witness.

## What is here, and what is not
This module is the machine's **mathematics**: the encoding of configurations as numerals, the
small-step function as a plain Lean definition, and its agreement with `Nat.Partrec.Code.eval`. The
realization of that step function as an actual `Nat.Partrec.Code`, and the workspace and step-count
laws that realization carries, are **deliberately absent** — they are a separate construction on top
of this one. Nothing below prices anything; `stepUFn` is a function `ℕ → ℕ`, not a code.

The definitions are nevertheless written so that the realization can mirror them: every case of
`stepUFn` is a tag test, an `unpair`, a `Nat.pair`, or a bounded dispatch on a decoded constructor.
No case iterates.

Two further things a resource account would want are **not** established here, and the reason is
recorded rather than left to be discovered:
* a *bound* on the number of steps a computation takes. `machine_complete` gives the run
  existentially; pinning an explicit budget means carrying an inequality through every composition
  rather than an iterate count, and its bounded-recursion contribution is a sum over counters, each
  bounded by the fuel the evaluator needed. That is a quantitative refinement of a settled result,
  not an open question about the machine.

## The configuration layout
A configuration is one numeral. Layouts are fixed here once, because the realization must reproduce
them exactly.

| object | numeral |
| --- | --- |
| configuration | `Nat.pair mode (Nat.pair current stack)` |
| mode `0` — *descend* | `current = Nat.pair c n`: evaluate the code numbered `c` at input `n` |
| mode `1` — *return* | `current = v`: the value `v` is being handed back to the stack |
| stack, empty | `0` |
| stack, non-empty | `2 * (hdr + frame * 2 ^ (L + 1) + rest * 2 ^ (2 * L + 1)) + 1` |
| — its header | `hdr = 2 ^ L - 1`, i.e. `L` low bits of `1`, where `L = frameBits frame` |
| frame | `Nat.pair tag payload` |

Two levels, two packings, and the difference is the point. A configuration wraps a *fixed* number
of components, so nesting `Nat.pair` there costs a constant factor. The stack **spine** nests once
per pending frame, so it is packed by concatenation instead: a cell writes its frame's bits and its
tail's bits side by side, prefixed by a unary header giving the frame's width. A cell therefore
costs the sum of its parts (`size_stkCons_le`), and a stack of depth `d` is linear in `d`
(`size_stack_le`) — where a nested pairing would make each cell at least the square of its tail,
and the depth cost bits exponentially.

The low bit of `1` separates a cell from the empty stack `0`. The header is unary because it must
be self-delimiting: a fixed-width length field would cap the frames a cell can hold, and frames
carry code numerals of unbounded size. Reading it (`trailOnes`) scans the header's bits, so it is
the one accessor that is not a constant number of operations — its cost is linear in the frame's
width. Everything else is a shift.

`stkIsCons` asks whether a numeral is what packing its own head and tail produces. Stating the test
as a round-trip makes reassembly hold by definition, and gives the termination fact
(`stkTail_lt`: a cell exceeds its tail) that makes the stack's denotation well-founded on *every*
numeral, well-formed or not.

The five frames, with their payloads and their meaning as "what to do with the value `v` that is
about to be returned":

| tag | payload | on return of `v` |
| --- | --- | --- |
| `0` | `Nat.pair cg n` | `v` is a pair's left value: evaluate `cg` at `n`, remembering `v` |
| `1` | `w` | `v` is a pair's right value: return `Nat.pair w v` |
| `2` | `cf` | `v` is a composition's inner value: evaluate `cf` at `v` |
| `3` | `⟨cg, ⟨a, ⟨y, r⟩⟩⟩` | the bounded-recursion loop (below) |
| `4` | `Nat.pair cf (Nat.pair a m)` | if `v = 0` return `m`, else probe `cf` at `⟨a, m+1⟩` |

The loop frame (tag `3`) is how bounded recursion is evaluated: `y` is the counter reached so far
and `r` the turns remaining. On return of the accumulator `v`, if `r = 0` the loop is done and `v`
goes to the tail; otherwise `cg` runs at `⟨a, ⟨y, v⟩⟩` and comes back with `y + 1` and `r - 1`,
*replacing* the same cell. So bounded recursion climbs from the base case under one stack cell
rather than unrolling its counter onto the stack — one cell per node, whatever the counter
(`stkDepth_prec_descend`), which is also how `TimeCost.spaceCost` prices it.

Unbounded search is a frame like any other (tag `4`), so the machine interprets *all* of
`Nat.Partrec.Code` — there is no fragment restriction anywhere below.

## What the workspace account gets
The packing is additive (`size_stkCons_le`), a well-formed stack of depth `d` costs `O(d)` bits
(`size_stack_le`), bounded recursion costs one cell whatever its counter
(`stkDepth_prec_descend`), and along any run the stack holds at most `codeDepth (ofNat p)` cells
(`stkDepth_run_le`). Together: a run of the code numbered `p` occupies at most
`codeDepth (ofNat p) * (2F + 2)` bits of stack, `F` the widest frame it holds.

The depth bound is not a numeric measure — the obvious one is refuted
(`runMeasure_not_antitone`) — but a per-frame invariant, `StackOK`, charging each cell for the code
it stores together with the cells beneath it.

## Agreement, in both directions
`machine_sound` and `machine_complete` together pin the machine's semantics to `Code.eval` on all of
`Nat.Partrec.Code`: it halts with a value exactly when the code has that value. Soundness needs no
fuel and no fragment restriction; completeness goes through the fuelled evaluator as its induction
principle only, never as the statement.

## How agreement is proved
Not by tracking the machine forward, but by giving every configuration a **denotation** — the value
the whole remaining computation would produce — and showing one step never changes it
(`step_denote`). Halting configurations are fixed points of the step function, so the invariance
extends to any number of steps by a bare induction (`denote_iterate`). Soundness is then immediate:
the initial configuration denotes `eval (ofNat p) x`, a halted one denotes its own answer, and the
two are equal.

The stack's denotation is where the frames earn their meanings: `stackDenote k v` is what the
machine finally returns if the value `v` is handed to the stack `k`. Configurations whose stack is
not a well-formed cell denote nothing, and the step function leaves them alone, so the invariance
holds on all numerals without a well-formedness hypothesis.

One auxiliary fact about `Nat.Partrec.Code.eval` is proved on the way and is of independent use:
`eval_rfind'_unfold`, which turns Mathlib's `rfind'` clause — stated through `Nat.rfind` over an
offset — into the one-probe recurrence the machine actually implements.
-/

namespace BoundedInterp

open Nat.Partrec (Code)
open Nat.Partrec.Code

/-! ## The stack: bit-concatenation with a self-delimiting length header

A cell lays its three parts side by side in binary rather than nesting them in a pairing function.
Low to high: a **unary length header** for the frame (`frameBits f` ones, then a zero), then the
frame's own `frameBits f` bits, then the tail. The whole is shifted up one place and given a low
bit of `1`, which is what distinguishes a cell from the empty stack `0`.

Concatenation is the point: a cell's bit-length is the sum of its parts' bit-lengths plus a header
proportional to the frame alone (`size_stkCons_le`), so a stack of depth `d` is linear in `d`, not
exponential. The header is unary because it must be self-delimiting — a fixed-width field would cap
the frames a cell can hold, and the machine's frames carry code numerals of unbounded size.

Decoding is arithmetic: `stkBody` drops the flag bit, `trailOnes` reads the header, and the frame
and tail come out by division and remainder at powers of two.
-/

/-- Positivity of a power of two, used throughout the packing arithmetic. -/
private theorem two_pow_pos (n : ℕ) : 0 < 2 ^ n := by positivity

/-- The number of consecutive `1` bits at the bottom of a numeral — the unary header's reader. -/
def trailOnes : ℕ → ℕ
  | 0 => 0
  | n + 1 => if (n + 1) % 2 = 1 then trailOnes ((n + 1) / 2) + 1 else 0

theorem trailOnes_even {n : ℕ} (h : n % 2 = 0) : trailOnes n = 0 := by
  cases n with
  | zero => simp [trailOnes]
  | succ m => rw [trailOnes, if_neg (by omega)]

theorem trailOnes_odd {n : ℕ} (h : n % 2 = 1) : trailOnes n = trailOnes (n / 2) + 1 := by
  cases n with
  | zero => omega
  | succ m => rw [trailOnes, if_pos h]

/-- **The header reads back its own length.** A numeral whose bottom is `L` ones followed by a zero
bit reports header length `L`, whatever sits above. -/
theorem trailOnes_pack (L m : ℕ) : trailOnes ((2 ^ L - 1) + 2 ^ (L + 1) * m) = L := by
  induction L with
  | zero =>
      have h : (2 ^ 0 - 1) + 2 ^ (0 + 1) * m = 2 * m := by norm_num
      rw [h, trailOnes_even (by omega)]
  | succ L ih =>
      have hp := two_pow_pos L
      have h1 : (2 : ℕ) ^ (L + 1) = 2 * 2 ^ L := by ring
      have h2 : (2 : ℕ) ^ (L + 1 + 1) = 2 * 2 ^ (L + 1) := by ring
      have hm : (2 : ℕ) ^ (L + 1 + 1) * m = 2 * (2 ^ (L + 1) * m) := by rw [h2]; ring
      have hval : (2 ^ (L + 1) - 1) + 2 ^ (L + 1 + 1) * m
          = 2 * ((2 ^ L - 1) + 2 ^ (L + 1) * m) + 1 := by omega
      have hdiv : (2 * ((2 ^ L - 1) + 2 ^ (L + 1) * m) + 1) / 2
          = (2 ^ L - 1) + 2 ^ (L + 1) * m := by omega
      rw [hval, trailOnes_odd (by omega), hdiv, ih]

/-- Doubling commutes with remainder on an odd numeral. -/
theorem two_mul_add_one_mod (a b : ℕ) (hb : 0 < b) :
    (2 * a + 1) % (2 * b) = 2 * (a % b) + 1 := by
  have h1 : (2 * a) % (2 * b) = 2 * (a % b) := Nat.mul_mod_mul_left 2 a b
  have h2 : a % b < b := Nat.mod_lt _ hb
  have h3 : (1 : ℕ) % (2 * b) = 1 := Nat.mod_eq_of_lt (by omega)
  calc (2 * a + 1) % (2 * b) = ((2 * a) % (2 * b) + 1 % (2 * b)) % (2 * b) := by rw [Nat.add_mod]
    _ = (2 * (a % b) + 1) % (2 * b) := by rw [h1, h3]
    _ = 2 * (a % b) + 1 := Nat.mod_eq_of_lt (by omega)

/-- **The header's length, in closed form.** `trailOnes n` is the least `L` at which the bottom
`L + 1` bits of `n` are *not* all ones — equivalently, `L` is below it exactly when they are.

Stated as this equivalence rather than as a description of the minimum because that is the form a
bounded fold consumes: a fold that raises its accumulator while the test holds computes
`min (trailOnes n) m`, with no separate minimality argument.

The induction is on the numeral, halving: an odd numeral's bottom bits are one more than its half's,
an even one has none, and zero has none. -/
theorem trailOnes_lt_iff : ∀ (n L : ℕ),
    L < trailOnes n ↔ n % 2 ^ (L + 1) = 2 ^ (L + 1) - 1 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
      intro L
      have hp2 : (2 : ℕ) ^ (L + 1) = 2 * 2 ^ L := by ring
      have hpL := two_pow_pos L
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · rw [trailOnes_even (by omega)]
        constructor
        · omega
        · intro h
          rw [Nat.zero_mod] at h
          omega
      · by_cases hpar : n % 2 = 1
        · rw [trailOnes_odd hpar]
          cases L with
          | zero =>
              constructor
              · intro _
                simpa using hpar
              · intro _
                omega
          | succ j =>
              have hhalf : n / 2 < n := by omega
              have hn2 : n = 2 * (n / 2) + 1 := by omega
              have hsplit : (2 : ℕ) ^ (j + 1 + 1) = 2 * 2 ^ (j + 1) := by ring
              have hpj := two_pow_pos (j + 1)
              have key : n % 2 ^ (j + 1 + 1) = 2 * ((n / 2) % 2 ^ (j + 1)) + 1 := by
                conv_lhs => rw [hn2]
                rw [hsplit]
                exact two_mul_add_one_mod _ _ hpj
              rw [key]
              have hih := ih (n / 2) hhalf j
              constructor
              · intro h
                have hj : j < trailOnes (n / 2) := by omega
                have := hih.1 hj
                omega
              · intro h
                have : (n / 2) % 2 ^ (j + 1) = 2 ^ (j + 1) - 1 := by omega
                have := hih.2 this
                omega
        · rw [trailOnes_even (by omega)]
          constructor
          · omega
          · intro h
            have hdvd : (2 : ℕ) ∣ 2 ^ (L + 1) := dvd_pow_self 2 (Nat.succ_ne_zero L)
            have h1 : n % 2 ^ (L + 1) % 2 = n % 2 := Nat.mod_mod_of_dvd n hdvd
            rw [h] at h1
            omega

/-! ### The packing arithmetic -/

/-- Regrouping a packed cell body: header at the bottom, frame and tail above it. -/
private theorem pack_eq (L f k : ℕ) :
    (2 ^ L - 1) + f * 2 ^ (L + 1) + k * 2 ^ (2 * L + 1)
      = 2 ^ (L + 1) * (f + k * 2 ^ L) + (2 ^ L - 1) := by
  have h : (2 : ℕ) ^ (2 * L + 1) = 2 ^ (L + 1) * 2 ^ L := by
    rw [← pow_add]; ring_nf
  rw [h]; ring

/-- The header fits below the frame. -/
private theorem hdr_lt (L : ℕ) : 2 ^ L - 1 < 2 ^ (L + 1) := by
  have := two_pow_pos L
  rw [pow_succ]
  omega

/-- The header and the frame together fit below the tail. -/
private theorem low_lt {L f : ℕ} (hf : f < 2 ^ L) :
    (2 ^ L - 1) + f * 2 ^ (L + 1) < 2 ^ (2 * L + 1) := by
  have hpos := two_pow_pos L
  have hmul : f * 2 ^ (L + 1) ≤ (2 ^ L - 1) * 2 ^ (L + 1) :=
    Nat.mul_le_mul_right _ (by omega)
  have hsub : (2 ^ L - 1) + 1 = 2 ^ L := by omega
  have hprod : (2 ^ L - 1) * 2 ^ (L + 1) + 2 ^ (L + 1) = 2 ^ (2 * L + 1) := by
    calc (2 ^ L - 1) * 2 ^ (L + 1) + 2 ^ (L + 1) = ((2 ^ L - 1) + 1) * 2 ^ (L + 1) := by ring
      _ = 2 ^ L * 2 ^ (L + 1) := by rw [hsub]
      _ = 2 ^ (2 * L + 1) := by rw [← pow_add]; ring_nf
  have hh := hdr_lt L
  omega

/-- The number of bits a frame occupies in a cell. -/
def frameBits (f : ℕ) : ℕ := Nat.size f

/-- **A non-empty stack cell.** Low to high: the unary header `1^L 0` for `L = frameBits f`, the
frame's `L` bits, then the tail — all shifted up one place, with a low bit of `1` marking the cell
apart from the empty stack. -/
def stkCons (f k : ℕ) : ℕ :=
  2 * ((2 ^ frameBits f - 1) + f * 2 ^ (frameBits f + 1)
    + k * 2 ^ (2 * frameBits f + 1)) + 1

/-- A cell with its flag bit removed. -/
def stkBody (s : ℕ) : ℕ := s / 2

/-- The frame width a cell declares, read off its unary header. -/
def stkLen (s : ℕ) : ℕ := trailOnes (stkBody s)

/-- The frame of a stack cell: the `stkLen s` bits sitting just above the header. -/
def stkHead (s : ℕ) : ℕ := (stkBody s / 2 ^ (stkLen s + 1)) % 2 ^ stkLen s

/-- The tail of a stack cell: everything above the header and the frame. -/
def stkTail (s : ℕ) : ℕ := stkBody s / 2 ^ (2 * stkLen s + 1)

/-- Is this numeral a stack cell? Exactly when it is what packing its own head and tail produces.
Stating the test as a round-trip makes `stkCons_head_tail` hold by definition, which is what the
denotation's recursion needs on numerals that were never built by `stkCons`. -/
def stkIsCons (s : ℕ) : Bool := stkCons (stkHead s) (stkTail s) == s

theorem stkBody_cons (f k : ℕ) :
    stkBody (stkCons f k) =
      (2 ^ frameBits f - 1) + f * 2 ^ (frameBits f + 1) + k * 2 ^ (2 * frameBits f + 1) := by
  rw [stkBody, stkCons]
  omega

@[simp] theorem stkLen_cons (f k : ℕ) : stkLen (stkCons f k) = frameBits f := by
  rw [stkLen, stkBody_cons, pack_eq, Nat.add_comm]
  exact trailOnes_pack _ _

@[simp] theorem stkHead_cons (f k : ℕ) : stkHead (stkCons f k) = f := by
  have hlt : f < 2 ^ frameBits f := Nat.lt_size_self f
  rw [stkHead, stkLen_cons, stkBody_cons, pack_eq, Nat.mul_add_div (two_pow_pos _),
    Nat.div_eq_of_lt (hdr_lt _), Nat.add_zero, Nat.add_mul_mod_self_right,
    Nat.mod_eq_of_lt hlt]

@[simp] theorem stkTail_cons (f k : ℕ) : stkTail (stkCons f k) = k := by
  have hlt : f < 2 ^ frameBits f := Nat.lt_size_self f
  rw [stkTail, stkLen_cons, stkBody_cons,
    show (2 ^ frameBits f - 1) + f * 2 ^ (frameBits f + 1) + k * 2 ^ (2 * frameBits f + 1)
        = 2 ^ (2 * frameBits f + 1) * k
            + ((2 ^ frameBits f - 1) + f * 2 ^ (frameBits f + 1)) from by ring,
    Nat.mul_add_div (two_pow_pos _), Nat.div_eq_of_lt (low_lt hlt), Nat.add_zero]

@[simp] theorem stkIsCons_cons (f k : ℕ) : stkIsCons (stkCons f k) = true := by
  simp [stkIsCons]

@[simp] theorem stkIsCons_zero : stkIsCons 0 = false := by
  have h : stkCons (stkHead 0) (stkTail 0) ≠ 0 := by rw [stkCons]; omega
  simpa [stkIsCons] using h

/-- Reassembling a cell from its head and tail is the identity on cells — by construction, since
that round-trip is what `stkIsCons` tests. -/
theorem stkCons_head_tail {s : ℕ} (h : stkIsCons s = true) :
    stkCons (stkHead s) (stkTail s) = s := by simpa [stkIsCons] using h

/-- **The termination fact.** A cell is strictly larger than its tail: the tail sits above the
header and the frame, so it is shifted up by at least one place. This is what makes the stack's
denotation well-founded on *every* numeral, well-formed or not. -/
theorem stkTail_lt {s : ℕ} (h : stkIsCons s = true) : stkTail s < s := by
  have hs := stkCons_head_tail h
  have hle : stkTail s ≤ stkTail s * 2 ^ (2 * frameBits (stkHead s) + 1) :=
    Nat.le_mul_of_pos_right _ (two_pow_pos _)
  have hgoal : stkTail s < stkCons (stkHead s) (stkTail s) := by
    rw [stkCons]; omega
  rwa [hs] at hgoal

/-- **The packing is additive.** A cell costs its tail's bits, its frame's bits, and a header
proportional to the frame — never a multiple of the whole. So a stack of depth `d` holding frames
of at most `F` bits occupies `O(d · F)` bits, linear in the depth.

This is the property a nested-pairing layout could not have: there a cell is at least the square of
its tail, so depth costs bits exponentially. -/
theorem size_stkCons_le (f k : ℕ) :
    Nat.size (stkCons f k) ≤ 2 * Nat.size f + Nat.size k + 2 := by
  have hlt : f < 2 ^ frameBits f := Nat.lt_size_self f
  have hk : k < 2 ^ Nat.size k := Nat.lt_size_self k
  have hlow := low_lt (L := frameBits f) hlt
  have hmul : k * 2 ^ (2 * frameBits f + 1) + 2 ^ (2 * frameBits f + 1)
      ≤ 2 ^ Nat.size k * 2 ^ (2 * frameBits f + 1) := by
    calc k * 2 ^ (2 * frameBits f + 1) + 2 ^ (2 * frameBits f + 1)
        = (k + 1) * 2 ^ (2 * frameBits f + 1) := by ring
      _ ≤ 2 ^ Nat.size k * 2 ^ (2 * frameBits f + 1) :=
          Nat.mul_le_mul_right _ (by omega)
  have hpow : (2 : ℕ) ^ (2 * Nat.size f + Nat.size k + 2)
      = 2 * (2 ^ Nat.size k * 2 ^ (2 * frameBits f + 1)) := by
    rw [frameBits, ← pow_add, ← pow_succ']
    congr 1
    omega
  rw [Nat.size_le, stkCons]
  omega

/-! ## Frames and configurations -/

/-- A frame: a tag and a payload. -/
def frame (tag pay : ℕ) : ℕ := Nat.pair tag pay

/-- A frame's tag. -/
def frTag (f : ℕ) : ℕ := f.unpair.1

/-- A frame's payload. -/
def frPay (f : ℕ) : ℕ := f.unpair.2

@[simp] theorem frTag_frame (t p : ℕ) : frTag (frame t p) = t := by simp [frTag, frame]

@[simp] theorem frPay_frame (t p : ℕ) : frPay (frame t p) = p := by simp [frPay, frame]

/-- A configuration: a mode, the current object, and the stack. -/
def config (mode cur stk : ℕ) : ℕ := Nat.pair mode (Nat.pair cur stk)

/-- The configuration's mode (`0` descend, `1` return). -/
def cfMode (s : ℕ) : ℕ := s.unpair.1

/-- The configuration's current object. -/
def cfCur (s : ℕ) : ℕ := s.unpair.2.unpair.1

/-- The configuration's stack. -/
def cfStk (s : ℕ) : ℕ := s.unpair.2.unpair.2

@[simp] theorem cfMode_config (m c k : ℕ) : cfMode (config m c k) = m := by simp [cfMode, config]

@[simp] theorem cfCur_config (m c k : ℕ) : cfCur (config m c k) = c := by simp [cfCur, config]

@[simp] theorem cfStk_config (m c k : ℕ) : cfStk (config m c k) = k := by simp [cfStk, config]

/-- A descending configuration: evaluate the code numbered `c` at input `n`. -/
def descend (c n k : ℕ) : ℕ := config 0 (Nat.pair c n) k

/-- A returning configuration: hand the value `v` back to the stack. -/
def ret (v k : ℕ) : ℕ := config 1 v k

/-- The initial configuration: evaluate the code numbered `p` at input `x`, with nothing pending. -/
def initConfig (p x : ℕ) : ℕ := descend p x 0

/-- Has the machine finished? It has when it is returning a value to the empty stack. -/
def isHalt (s : ℕ) : Bool := (cfMode s == 1) && (cfStk s == 0)

/-- The answer of a halted configuration. -/
def haltVal (s : ℕ) : ℕ := cfCur s

@[simp] theorem isHalt_ret_zero (v : ℕ) : isHalt (ret v 0) = true := by simp [isHalt, ret]

@[simp] theorem haltVal_ret (v k : ℕ) : haltVal (ret v k) = v := by simp [haltVal, ret]

/-! ## The step function -/

/-- One step from a descending configuration: decode the constructor and either answer outright, or
push the frame that records what remains to be done. Bounded recursion at a positive counter steps
*down* by one and pushes a frame; unbounded search probes its predicate and pushes a search
frame. -/
def stepDescend (c n k : ℕ) : ℕ :=
  match Denumerable.ofNat Code c with
  | Code.zero => ret 0 k
  | Code.succ => ret (n + 1) k
  | Code.left => ret n.unpair.1 k
  | Code.right => ret n.unpair.2 k
  | Code.pair cf cg =>
      descend (Encodable.encode cf) n (stkCons (frame 0 (Nat.pair (Encodable.encode cg) n)) k)
  | Code.comp cf cg =>
      descend (Encodable.encode cg) n (stkCons (frame 2 (Encodable.encode cf)) k)
  | Code.prec cf cg =>
      descend (Encodable.encode cf) n.unpair.1
        (stkCons (frame 3 (Nat.pair (Encodable.encode cg)
          (Nat.pair n.unpair.1 (Nat.pair 0 n.unpair.2)))) k)
  | Code.rfind' cf =>
      descend (Encodable.encode cf) n (stkCons (frame 4 (Nat.pair (Encodable.encode cf) n)) k)

/-- One step from a returning configuration, dispatching on the top frame's tag. -/
def stepReturn (v f k : ℕ) : ℕ :=
  match frTag f with
  | 0 => descend (frPay f).unpair.1 (frPay f).unpair.2 (stkCons (frame 1 v) k)
  | 1 => ret (Nat.pair (frPay f) v) k
  | 2 => descend (frPay f) v k
  | 3 =>
      if (frPay f).unpair.2.unpair.2.unpair.2 = 0 then ret v k
      else
        descend (frPay f).unpair.1
          (Nat.pair (frPay f).unpair.2.unpair.1
            (Nat.pair (frPay f).unpair.2.unpair.2.unpair.1 v))
          (stkCons (frame 3 (Nat.pair (frPay f).unpair.1
            (Nat.pair (frPay f).unpair.2.unpair.1
              (Nat.pair ((frPay f).unpair.2.unpair.2.unpair.1 + 1)
                ((frPay f).unpair.2.unpair.2.unpair.2 - 1))))) k)
  | 4 =>
      if v = 0 then ret (frPay f).unpair.2.unpair.2 k
      else
        descend (frPay f).unpair.1
          (Nat.pair (frPay f).unpair.2.unpair.1 ((frPay f).unpair.2.unpair.2 + 1))
          (stkCons (frame 4 (Nat.pair (frPay f).unpair.1
            (Nat.pair (frPay f).unpair.2.unpair.1 ((frPay f).unpair.2.unpair.2 + 1)))) k)
  | _ => ret v (stkCons f k)

/-- **The small-step function.** Total on all numerals. A halted configuration is a fixed point, as
is any configuration whose stack is neither empty nor a well-formed cell — so the machine is never
undefined and never falls off its own encoding. -/
def stepUFn (s : ℕ) : ℕ :=
  if isHalt s then s
  else if cfMode s = 0 then stepDescend (cfCur s).unpair.1 (cfCur s).unpair.2 (cfStk s)
  else if stkIsCons (cfStk s) then stepReturn (cfCur s) (stkHead (cfStk s)) (stkTail (cfStk s))
  else s

theorem stepUFn_halt {s : ℕ} (h : isHalt s = true) : stepUFn s = s := by simp [stepUFn, h]

theorem stepUFn_descend (c n k : ℕ) : stepUFn (descend c n k) = stepDescend c n k := by
  simp [stepUFn, isHalt, descend, config, cfMode, cfCur, cfStk]

theorem stepUFn_ret_cons (v f k : ℕ) :
    stepUFn (ret v (stkCons f k)) = stepReturn v f k := by
  have h : stkCons f k ≠ 0 := by rw [stkCons]; omega
  simp [stepUFn, isHalt, ret, config, cfMode, cfCur, cfStk, h]

/-! ## Bounded recursion as an upward loop -/

/-- Two continuations that agree pointwise bind the same. -/
private theorem bind_congr_right {o : Part ℕ} {f g : ℕ → Part ℕ} (h : ∀ v, f v = g v) :
    o.bind f = o.bind g := by rw [funext h]

/-- **The bounded-recursion loop, semantically.** `precLoop cgn a r y v` is the value bounded
recursion reaches from accumulator `v` at counter `y` with `r` iterations left: apply the step code
`cgn` to `⟨a, ⟨y, v⟩⟩`, advance the counter, and count down.

The machine runs this loop under a *single* stack cell, so bounded recursion costs one frame however
large its counter — the account `TimeCost.spaceCost` already gives it, where the counter appears in
a `max` and not in a sum. -/
def precLoop (cgn a : ℕ) : ℕ → ℕ → ℕ → Part ℕ
  | 0, _y, v => Part.some v
  | r + 1, y, v =>
      (eval (Denumerable.ofNat Code cgn) (Nat.pair a (Nat.pair y v))).bind fun w =>
        precLoop cgn a r (y + 1) w

@[simp] theorem precLoop_zero (cgn a y v : ℕ) : precLoop cgn a 0 y v = Part.some v := rfl

theorem precLoop_succ (cgn a r y v : ℕ) :
    precLoop cgn a (r + 1) y v =
      (eval (Denumerable.ofNat Code cgn) (Nat.pair a (Nat.pair y v))).bind fun w =>
        precLoop cgn a r (y + 1) w := rfl

/-- **The loop computes bounded recursion.** Running the loop for `r` iterations from the value
bounded recursion has at counter `y` gives the value it has at counter `y + r`. At `y = 0` this is
the whole of `eval (prec cf cg)`, which is what lets the machine start from the base case and climb
rather than unroll the counter onto the stack. -/
theorem precLoop_eval (cf cg : Code) (a : ℕ) : ∀ (r y : ℕ),
    (eval (Code.prec cf cg) (Nat.pair a y)).bind
        (fun v => precLoop (Encodable.encode cg) a r y v)
      = eval (Code.prec cf cg) (Nat.pair a (y + r)) := by
  intro r
  induction r with
  | zero => intro y; simp [Part.bind_some_right]
  | succ r ih =>
      intro y
      have hstep : ∀ v : ℕ, precLoop (Encodable.encode cg) a (r + 1) y v
          = (eval cg (Nat.pair a (Nat.pair y v))).bind fun w =>
              precLoop (Encodable.encode cg) a r (y + 1) w := by
        intro v
        rw [precLoop_succ, Denumerable.ofNat_encode]
      calc (eval (Code.prec cf cg) (Nat.pair a y)).bind
              (fun v => precLoop (Encodable.encode cg) a (r + 1) y v)
          = (eval (Code.prec cf cg) (Nat.pair a y)).bind
              (fun v => (eval cg (Nat.pair a (Nat.pair y v))).bind
                fun w => precLoop (Encodable.encode cg) a r (y + 1) w) :=
              bind_congr_right hstep
        _ = ((eval (Code.prec cf cg) (Nat.pair a y)).bind
              fun v => eval cg (Nat.pair a (Nat.pair y v))).bind
                (fun w => precLoop (Encodable.encode cg) a r (y + 1) w) :=
              (Part.bind_assoc _ _ _).symm
        _ = (eval (Code.prec cf cg) (Nat.pair a (y + 1))).bind
              (fun w => precLoop (Encodable.encode cg) a r (y + 1) w) := by
              rw [eval_prec_succ, Part.bind_eq_bind]
        _ = eval (Code.prec cf cg) (Nat.pair a (y + 1 + r)) := ih (y + 1)
        _ = eval (Code.prec cf cg) (Nat.pair a (y + (r + 1))) := by
              rw [show y + 1 + r = y + (r + 1) from by omega]

/-! ## The denotation of a stack, and of a configuration -/

/-- **What the stack will do with a value.** `stackDenote k v` is the answer the machine finally
returns when the value `v` reaches the stack `k`: the empty stack returns it, each frame consumes it
in the way its tag says, and a numeral that is neither empty nor a cell returns nothing.

The recursion is on the numeral itself and terminates by `stkTail_lt` — the cell flag guarantees a
strict decrease, so no well-formedness hypothesis is needed. -/
def stackDenote (s : ℕ) (v : ℕ) : Part ℕ :=
  if _h : stkIsCons s = true then
    match frTag (stkHead s) with
    | 0 => (eval (Denumerable.ofNat Code (frPay (stkHead s)).unpair.1)
              (frPay (stkHead s)).unpair.2).bind fun w =>
                stackDenote (stkTail s) (Nat.pair v w)
    | 1 => stackDenote (stkTail s) (Nat.pair (frPay (stkHead s)) v)
    | 2 => (eval (Denumerable.ofNat Code (frPay (stkHead s))) v).bind (stackDenote (stkTail s))
    | 3 => (precLoop (frPay (stkHead s)).unpair.1 (frPay (stkHead s)).unpair.2.unpair.1
              (frPay (stkHead s)).unpair.2.unpair.2.unpair.2
              (frPay (stkHead s)).unpair.2.unpair.2.unpair.1 v).bind (stackDenote (stkTail s))
    | 4 =>
        if v = 0 then stackDenote (stkTail s) (frPay (stkHead s)).unpair.2.unpair.2
        else (eval (Code.rfind' (Denumerable.ofNat Code (frPay (stkHead s)).unpair.1))
                (Nat.pair (frPay (stkHead s)).unpair.2.unpair.1
                  ((frPay (stkHead s)).unpair.2.unpair.2 + 1))).bind (stackDenote (stkTail s))
    | _ => Part.none
  else if s = 0 then Part.some v
  else Part.none
termination_by s
decreasing_by all_goals exact stkTail_lt _h

@[simp] theorem stackDenote_zero (v : ℕ) : stackDenote 0 v = Part.some v := by
  rw [stackDenote]; simp

/-- The stack denotation unfolded at a cell — the form every step-case proof uses. -/
theorem stackDenote_cons (f k v : ℕ) :
    stackDenote (stkCons f k) v =
      (match frTag f with
        | 0 => (eval (Denumerable.ofNat Code (frPay f).unpair.1) (frPay f).unpair.2).bind fun w =>
                  stackDenote k (Nat.pair v w)
        | 1 => stackDenote k (Nat.pair (frPay f) v)
        | 2 => (eval (Denumerable.ofNat Code (frPay f)) v).bind (stackDenote k)
        | 3 => (precLoop (frPay f).unpair.1 (frPay f).unpair.2.unpair.1
                  (frPay f).unpair.2.unpair.2.unpair.2
                  (frPay f).unpair.2.unpair.2.unpair.1 v).bind (stackDenote k)
        | 4 => if v = 0 then stackDenote k (frPay f).unpair.2.unpair.2
               else (eval (Code.rfind' (Denumerable.ofNat Code (frPay f).unpair.1))
                       (Nat.pair (frPay f).unpair.2.unpair.1
                         ((frPay f).unpair.2.unpair.2 + 1))).bind (stackDenote k)
        | _ => Part.none) := by
  rw [stackDenote]
  simp only [stkIsCons_cons, stkHead_cons, stkTail_cons, dif_pos]

/-- **The denotation of a configuration**: what the whole remaining computation will produce. -/
def denote (s : ℕ) : Part ℕ :=
  if cfMode s = 0 then
    (eval (Denumerable.ofNat Code (cfCur s).unpair.1) (cfCur s).unpair.2).bind
      (stackDenote (cfStk s))
  else stackDenote (cfStk s) (cfCur s)

@[simp] theorem denote_descend (c n k : ℕ) :
    denote (descend c n k) = (eval (Denumerable.ofNat Code c) n).bind (stackDenote k) := by
  simp [denote, descend]

@[simp] theorem denote_ret (v k : ℕ) : denote (ret v k) = stackDenote k v := by
  simp [denote, ret]

/-! ## Unbounded search, as a one-probe recurrence -/

/-- A search probe reports `true` exactly when the probed code returns `0`. -/
theorem probe_true {o : Part ℕ} : (true ∈ (fun x => decide (x = 0)) <$> o) ↔ 0 ∈ o := by
  rw [Part.map_eq_map, Part.mem_map_iff]
  constructor
  · rintro ⟨z, hz, hz0⟩
    have : z = 0 := by simpa using hz0
    exact this ▸ hz
  · intro h
    exact ⟨0, h, by simp⟩

/-- A search probe reports `false` exactly when the probed code returns something non-zero. -/
theorem probe_false {o : Part ℕ} :
    (false ∈ (fun x => decide (x = 0)) <$> o) ↔ ∃ z ∈ o, z ≠ 0 := by
  rw [Part.map_eq_map, Part.mem_map_iff]
  constructor
  · rintro ⟨z, hz, hz0⟩
    exact ⟨z, hz, by simpa using hz0⟩
  · rintro ⟨z, hz, hz0⟩
    exact ⟨z, hz, by simpa using hz0⟩

/-- **The `rfind'` recurrence.** Mathlib defines `eval (rfind' cf)` through `Nat.rfind` over an
offset; the machine instead probes once and either answers or moves the offset up by one. The two
agree: searching from `m` is probing at `m` and, if the probe is non-zero, searching from `m + 1`.

This is the only fact about `Code.eval` proved here rather than imported, and it is what lets the
search frame be an ordinary frame instead of a nested loop. -/
theorem eval_rfind'_unfold (cf : Code) (a m : ℕ) :
    eval (Code.rfind' cf) (Nat.pair a m) =
      (eval cf (Nat.pair a m)).bind fun v =>
        if v = 0 then Part.some m else eval (Code.rfind' cf) (Nat.pair a (m + 1)) := by
  have hev : ∀ b : ℕ, eval (Code.rfind' cf) (Nat.pair a b) =
      (Nat.rfind fun n =>
        (fun x => decide (x = 0)) <$> eval cf (Nat.pair a (n + b))).map (· + b) := by
    intro b
    simp only [eval, Nat.unpaired, Nat.unpair_pair]
  apply Part.ext
  intro x
  rw [hev m, Part.mem_map_iff, Part.mem_bind_iff]
  constructor
  · rintro ⟨n, hn, rfl⟩
    rw [Nat.mem_rfind] at hn
    obtain ⟨hspec, hmin⟩ := hn
    rw [probe_true] at hspec
    cases n with
    | zero => exact ⟨0, by simpa using hspec, by simp⟩
    | succ n' =>
        obtain ⟨w, hw, hwne⟩ := probe_false.1 (hmin (Nat.succ_pos n'))
        refine ⟨w, by simpa using hw, ?_⟩
        rw [if_neg hwne, hev (m + 1), Part.mem_map_iff]
        refine ⟨n', ?_, by omega⟩
        rw [Nat.mem_rfind]
        refine ⟨probe_true.2 ?_, ?_⟩
        · rw [show n' + (m + 1) = n' + 1 + m from by omega]
          exact hspec
        · intro i hi
          refine probe_false.2 ?_
          obtain ⟨z, hz, hzne⟩ := probe_false.1 (hmin (by omega : i + 1 < n' + 1))
          exact ⟨z, by rw [show i + (m + 1) = i + 1 + m from by omega]; exact hz, hzne⟩
  · rintro ⟨v, hv, hx⟩
    by_cases hv0 : v = 0
    · subst hv0
      rw [if_pos rfl, Part.mem_some_iff] at hx
      subst hx
      refine ⟨0, ?_, by omega⟩
      rw [Nat.mem_rfind]
      refine ⟨probe_true.2 (by simpa using hv), ?_⟩
      intro i hi
      exact absurd hi (Nat.not_lt_zero i)
    · rw [if_neg hv0, hev (m + 1), Part.mem_map_iff] at hx
      obtain ⟨n', hn', rfl⟩ := hx
      rw [Nat.mem_rfind] at hn'
      obtain ⟨hspec, hmin⟩ := hn'
      refine ⟨n' + 1, ?_, by omega⟩
      rw [Nat.mem_rfind]
      refine ⟨probe_true.2 ?_, ?_⟩
      · rw [show n' + 1 + m = n' + (m + 1) from by omega]
        exact probe_true.1 hspec
      · intro i hi
        refine probe_false.2 ?_
        cases i with
        | zero => exact ⟨v, by simpa using hv, hv0⟩
        | succ i' =>
            obtain ⟨z, hz, hzne⟩ := probe_false.1 (hmin (by omega : i' < n'))
            exact ⟨z, by rw [show i' + 1 + m = i' + (m + 1) from by omega]; exact hz, hzne⟩

/-! ## One step does not change the denotation -/

/-- The search frame's clause is exactly the `rfind'` recurrence, bound through the rest of the
stack. Used both when unbounded search is entered and when it goes round again. -/
theorem rfind_frame_bind (cfn a m k : ℕ) :
    (eval (Denumerable.ofNat Code cfn) (Nat.pair a m)).bind
        (stackDenote (stkCons (frame 4 (Nat.pair cfn (Nat.pair a m))) k))
      = (eval (Code.rfind' (Denumerable.ofNat Code cfn)) (Nat.pair a m)).bind
          (stackDenote k) := by
  rw [eval_rfind'_unfold, Part.bind_assoc]
  congr 1
  funext v
  rw [stackDenote_cons]
  simp only [frTag_frame, frPay_frame, Nat.unpair_pair]
  by_cases h : v = 0 <;> simp [h]

/-- The pair frame's clause reassembles the applicative product of the two components. -/
theorem pair_frame_bind (cfn cgn n k : ℕ) :
    (eval (Denumerable.ofNat Code cfn) n).bind
        (stackDenote (stkCons (frame 0 (Nat.pair cgn n)) k))
      = (Nat.pair <$> eval (Denumerable.ofNat Code cfn) n <*>
          eval (Denumerable.ofNat Code cgn) n).bind (stackDenote k) := by
  apply Part.ext
  intro x
  rw [Part.mem_bind_iff, Part.mem_bind_iff]
  constructor
  · rintro ⟨v, hv, hx⟩
    rw [stackDenote_cons] at hx
    simp only [frTag_frame, frPay_frame, Nat.unpair_pair, Part.mem_bind_iff] at hx
    obtain ⟨w, hw, hx⟩ := hx
    refine ⟨Nat.pair v w, ?_, hx⟩
    simp only [Seq.seq, Part.mem_bind_iff, Part.map_eq_map, Part.mem_map_iff]
    exact ⟨Nat.pair v, ⟨v, hv, rfl⟩, w, hw, rfl⟩
  · rintro ⟨y, hy, hx⟩
    simp only [Seq.seq, Part.mem_bind_iff, Part.map_eq_map, Part.mem_map_iff] at hy
    obtain ⟨gf, ⟨v, hv, rfl⟩, w, hw, rfl⟩ := hy
    refine ⟨v, hv, ?_⟩
    rw [stackDenote_cons]
    simp only [frTag_frame, frPay_frame, Nat.unpair_pair, Part.mem_bind_iff]
    exact ⟨w, hw, hx⟩

/-- A descending step keeps the denotation: the pending work the new configuration records is
exactly the semantics of the constructor it decoded. One case per constructor. -/
theorem denote_stepDescend (c n k : ℕ) :
    denote (stepDescend c n k) = (eval (Denumerable.ofNat Code c) n).bind (stackDenote k) := by
  cases hc : Denumerable.ofNat Code c with
  | zero =>
      simp only [stepDescend, hc, denote_ret, eval]
      exact (Part.bind_some 0 (stackDenote k)).symm
  | succ =>
      simp only [stepDescend, hc, denote_ret, eval]
      exact (Part.bind_some (n + 1) (stackDenote k)).symm
  | left =>
      simp only [stepDescend, hc, denote_ret, eval]
      exact (Part.bind_some n.unpair.1 (stackDenote k)).symm
  | right =>
      simp only [stepDescend, hc, denote_ret, eval]
      exact (Part.bind_some n.unpair.2 (stackDenote k)).symm
  | pair cf cg =>
      simp only [stepDescend, hc, denote_descend, eval]
      have hpf := pair_frame_bind (Encodable.encode cf) (Encodable.encode cg) n k
      simpa only [Denumerable.ofNat_encode] using hpf
  | comp cf cg =>
      simp only [stepDescend, hc, denote_descend, Denumerable.ofNat_encode, eval,
        Part.bind_eq_bind, Part.bind_assoc]
      congr 1
      funext v
      rw [stackDenote_cons]
      simp only [frTag_frame, frPay_frame, Denumerable.ofNat_encode]
  | prec cf cg =>
      obtain ⟨a, m, rfl⟩ : ∃ a m, n = Nat.pair a m :=
        ⟨n.unpair.1, n.unpair.2, (Nat.pair_unpair n).symm⟩
      simp only [stepDescend, hc, Nat.unpair_pair, denote_descend, Denumerable.ofNat_encode]
      have hclause : ∀ v : ℕ,
          stackDenote (stkCons (frame 3 (Nat.pair (Encodable.encode cg)
              (Nat.pair a (Nat.pair 0 m)))) k) v
            = (precLoop (Encodable.encode cg) a m 0 v).bind (stackDenote k) := by
        intro v
        rw [stackDenote_cons]
        simp only [frTag_frame, frPay_frame, Nat.unpair_pair]
      calc (eval cf a).bind (stackDenote (stkCons (frame 3 (Nat.pair (Encodable.encode cg)
              (Nat.pair a (Nat.pair 0 m)))) k))
          = (eval cf a).bind fun v => (precLoop (Encodable.encode cg) a m 0 v).bind
              (stackDenote k) := bind_congr_right hclause
        _ = ((eval cf a).bind fun v => precLoop (Encodable.encode cg) a m 0 v).bind
              (stackDenote k) := by rw [Part.bind_assoc]
        _ = (eval (Code.prec cf cg) (Nat.pair a m)).bind (stackDenote k) := by
              rw [show eval cf a = eval (Code.prec cf cg) (Nat.pair a 0) from
                (eval_prec_zero cf cg a).symm, precLoop_eval cf cg a m 0]
              simp
  | rfind' cf =>
      obtain ⟨a, m, rfl⟩ : ∃ a m, n = Nat.pair a m :=
        ⟨n.unpair.1, n.unpair.2, (Nat.pair_unpair n).symm⟩
      simp only [stepDescend, hc, denote_descend]
      rw [rfind_frame_bind (Encodable.encode cf) a m k]
      simp only [Denumerable.ofNat_encode]

/-- A returning step keeps the denotation: each frame's action is its clause of `stackDenote`. -/
theorem denote_stepReturn (v f k : ℕ) :
    denote (stepReturn v f k) = stackDenote (stkCons f k) v := by
  rw [stackDenote_cons]
  rcases ht : frTag f with _ | _ | _ | _ | _ | t
  · simp only [stepReturn, ht, denote_descend]
    congr 1
    funext w
    rw [stackDenote_cons]
    simp only [frTag_frame, frPay_frame]
  · simp [stepReturn, ht]
  · simp [stepReturn, ht]
  · -- the bounded-recursion loop frame
    obtain ⟨cgn, aa, yy, rr, hp⟩ :
        ∃ cgn aa yy rr, frPay f = Nat.pair cgn (Nat.pair aa (Nat.pair yy rr)) :=
      ⟨(frPay f).unpair.1, (frPay f).unpair.2.unpair.1,
        (frPay f).unpair.2.unpair.2.unpair.1, (frPay f).unpair.2.unpair.2.unpair.2, by
          simp [Nat.pair_unpair]⟩
    cases rr with
    | zero => simp [stepReturn, ht, hp]
    | succ r =>
        simp only [stepReturn, ht, hp, Nat.unpair_pair, Nat.succ_ne_zero, if_false,
          Nat.succ_sub_one, denote_descend, precLoop_succ, Part.bind_assoc]
        refine bind_congr_right fun w => ?_
        rw [stackDenote_cons]
        simp only [frTag_frame, frPay_frame, Nat.unpair_pair]
  · by_cases hv : v = 0
    · simp [stepReturn, ht, hv]
    · simp only [stepReturn, ht, if_neg hv, denote_descend]
      rw [rfind_frame_bind (frPay f).unpair.1 (frPay f).unpair.2.unpair.1
        ((frPay f).unpair.2.unpair.2 + 1) k]
  · simp only [stepReturn, ht, denote_ret, stackDenote_cons]

/-- **The invariance.** One step of the machine never changes what the configuration denotes —
including at halted and at stuck configurations, which the step function fixes. -/
theorem step_denote (s : ℕ) : denote (stepUFn s) = denote s := by
  by_cases hh : isHalt s = true
  · rw [stepUFn_halt hh]
  · by_cases hm : cfMode s = 0
    · have hstep : stepUFn s = stepDescend (cfCur s).unpair.1 (cfCur s).unpair.2 (cfStk s) := by
        simp [stepUFn, hh, hm]
      rw [hstep, denote_stepDescend, denote, if_pos hm]
    · by_cases hc : stkIsCons (cfStk s) = true
      · have hstep : stepUFn s =
            stepReturn (cfCur s) (stkHead (cfStk s)) (stkTail (cfStk s)) := by
          simp [stepUFn, hh, hm, hc]
        rw [hstep, denote_stepReturn, stkCons_head_tail hc, denote, if_neg hm]
      · have hstep : stepUFn s = s := by
          simp [stepUFn, hh, hm, hc]
        rw [hstep]

/-- Any number of steps leaves the denotation alone. The induction peels a step off the **front**
(`Function.iterate_succ_apply`), with the configuration generalized. -/
theorem denote_iterate : ∀ (τ : ℕ) (s : ℕ), denote (stepUFn^[τ] s) = denote s := by
  intro τ
  induction τ with
  | zero => intro s; rfl
  | succ t ih =>
      intro s
      rw [Function.iterate_succ_apply, ih (stepUFn s), step_denote]

/-! ## Soundness -/

/-- **Soundness.** If the machine halts, its answer is a genuine value of the code it was given.
Exact, with no fragment restriction and no fuel: the initial configuration denotes
`eval (ofNat p) x`, a halted configuration denotes its own answer, and `denote_iterate` identifies
the two. -/
theorem machine_sound (p x : ℕ) {tau : ℕ} (h : isHalt (stepUFn^[tau] (initConfig p x)) = true) :
    haltVal (stepUFn^[tau] (initConfig p x)) ∈ eval (Denumerable.ofNat Code p) x := by
  set s := stepUFn^[tau] (initConfig p x) with hs
  obtain ⟨hmode1, hstk0⟩ : cfMode s = 1 ∧ cfStk s = 0 := by simpa [isHalt] using h
  have hden : denote s = Part.some (haltVal s) := by
    rw [denote, if_neg (by omega : ¬ cfMode s = 0), hstk0, stackDenote_zero, haltVal]
  have hinit : denote (initConfig p x) = eval (Denumerable.ofNat Code p) x := by
    apply Part.ext
    intro y
    rw [initConfig, denote_descend, Part.mem_bind_iff]
    constructor
    · rintro ⟨v, hv, hy⟩
      rw [stackDenote_zero, Part.mem_some_iff] at hy
      exact hy ▸ hv
    · intro hy
      exact ⟨y, hy, by rw [stackDenote_zero]; exact Part.mem_some _⟩
  have hiter := denote_iterate tau (initConfig p x)
  rw [← hs, hden, hinit] at hiter
  rw [← hiter]
  exact Part.mem_some _

/-! ## Well-formed stacks, their depth, and the size bound the packing buys

A stack is well formed when it is the empty stack or a cell whose tail is well formed. Its **depth**
is the number of cells, and its **frame width** the widest frame it holds. `size_stack_le` is what
the additive packing was for: a well-formed stack of depth `d` whose frames are at most `F` bits
occupies at most `d · (2F + 2)` bits — linear in the depth, with the constant `2` on `F` being the
unary header (a frame pays for its own length in bits) and the `+ 2` the flag and the header's
terminating zero.

This is the shape a workspace account for the machine consumes: the run's workspace is the widest
configuration it holds, and a configuration is a bounded wrapper around its stack.
-/

/-- A well-formed stack: the empty stack, or a cell whose tail is well formed. -/
def IsStack (s : ℕ) : Prop :=
  if _h : stkIsCons s = true then IsStack (stkTail s) else s = 0
termination_by s
decreasing_by exact stkTail_lt _h

@[simp] theorem isStack_zero : IsStack 0 := by rw [IsStack]; simp

theorem isStack_cons {f k : ℕ} (h : IsStack k) : IsStack (stkCons f k) := by
  rw [IsStack]
  simpa using h

/-- The number of cells in a stack. -/
def stkDepth (s : ℕ) : ℕ :=
  if _h : stkIsCons s = true then stkDepth (stkTail s) + 1 else 0
termination_by s
decreasing_by exact stkTail_lt _h

/-- The widest frame a stack holds, in bits. -/
def stkMaxFrame (s : ℕ) : ℕ :=
  if _h : stkIsCons s = true then max (Nat.size (stkHead s)) (stkMaxFrame (stkTail s)) else 0
termination_by s
decreasing_by exact stkTail_lt _h

theorem stkDepth_cons (f k : ℕ) : stkDepth (stkCons f k) = stkDepth k + 1 := by
  rw [stkDepth]; simp

theorem stkMaxFrame_cons (f k : ℕ) :
    stkMaxFrame (stkCons f k) = max (Nat.size f) (stkMaxFrame k) := by
  rw [stkMaxFrame]; simp

/-- **The stack is linear in its depth.** A well-formed stack of depth `d` whose frames are at most
`F` bits wide occupies at most `d · (2F + 2)` bits. The factor `2` on `F` is the unary header, the
`+ 2` the flag bit and the header's terminator; neither depends on how deep the stack already is,
which is exactly what the additive packing buys and a nested pairing cannot. -/
theorem size_stack_le :
    ∀ (s : ℕ), IsStack s → Nat.size s ≤ stkDepth s * (2 * stkMaxFrame s + 2) := by
  intro s
  induction s using Nat.strong_induction_on with
  | _ s ih =>
      intro hwf
      by_cases h : stkIsCons s = true
      · have hs := stkCons_head_tail h
        have hlt := stkTail_lt h
        have htail : IsStack (stkTail s) := by rw [IsStack] at hwf; simpa [h] using hwf
        have hd : stkDepth s = stkDepth (stkTail s) + 1 := by
          conv_lhs => rw [← hs]
          rw [stkDepth_cons]
        have hm : stkMaxFrame s = max (Nat.size (stkHead s)) (stkMaxFrame (stkTail s)) := by
          conv_lhs => rw [← hs]
          rw [stkMaxFrame_cons]
        have hsize : Nat.size s ≤ 2 * Nat.size (stkHead s) + Nat.size (stkTail s) + 2 := by
          conv_lhs => rw [← hs]
          exact size_stkCons_le _ _
        have h1 : Nat.size (stkHead s) ≤ stkMaxFrame s := by rw [hm]; exact le_max_left _ _
        have h2 : stkMaxFrame (stkTail s) ≤ stkMaxFrame s := by rw [hm]; exact le_max_right _ _
        have iht := ih (stkTail s) hlt htail
        have h3 : stkDepth (stkTail s) * (2 * stkMaxFrame (stkTail s) + 2)
            ≤ stkDepth (stkTail s) * (2 * stkMaxFrame s + 2) :=
          Nat.mul_le_mul_left _ (by omega)
        have hexp : (stkDepth (stkTail s) + 1) * (2 * stkMaxFrame s + 2)
            = stkDepth (stkTail s) * (2 * stkMaxFrame s + 2) + (2 * stkMaxFrame s + 2) := by ring
        rw [hd]
        omega
      · have hz : s = 0 := by rw [IsStack] at hwf; simpa [h] using hwf
        subst hz
        simp

/-! ## The depth of a code

The AST depth of a code, with leaves at `1` so that the depth of any code is positive and a bound
stated as a multiple of it never degenerates. -/

/-- The AST depth of a code: leaves count `1`, an internal node one more than its deepest child. -/
def codeDepth : Code → ℕ
  | Code.zero => 1
  | Code.succ => 1
  | Code.left => 1
  | Code.right => 1
  | Code.pair cf cg => 1 + max (codeDepth cf) (codeDepth cg)
  | Code.comp cf cg => 1 + max (codeDepth cf) (codeDepth cg)
  | Code.prec cf cg => 1 + max (codeDepth cf) (codeDepth cg)
  | Code.rfind' cf => 1 + codeDepth cf

theorem codeDepth_pos (c : Code) : 0 < codeDepth c := by
  cases c <;> simp [codeDepth]

theorem codeDepth_pair_left (cf cg : Code) : codeDepth cf < codeDepth (Code.pair cf cg) := by
  simp only [codeDepth]; omega

theorem codeDepth_pair_right (cf cg : Code) : codeDepth cg < codeDepth (Code.pair cf cg) := by
  simp only [codeDepth]; omega

theorem codeDepth_comp_left (cf cg : Code) : codeDepth cf < codeDepth (Code.comp cf cg) := by
  simp only [codeDepth]; omega

theorem codeDepth_comp_right (cf cg : Code) : codeDepth cg < codeDepth (Code.comp cf cg) := by
  simp only [codeDepth]; omega

theorem codeDepth_prec_left (cf cg : Code) : codeDepth cf < codeDepth (Code.prec cf cg) := by
  simp only [codeDepth]; omega

theorem codeDepth_prec_right (cf cg : Code) : codeDepth cg < codeDepth (Code.prec cf cg) := by
  simp only [codeDepth]; omega

theorem codeDepth_rfind' (cf : Code) : codeDepth cf < codeDepth (Code.rfind' cf) := by
  simp only [codeDepth]; omega

/-! ## Well-formedness is preserved along a run -/

@[simp] theorem cfStk_descend (c n k : ℕ) : cfStk (descend c n k) = k := by simp [descend]

@[simp] theorem cfStk_ret (v k : ℕ) : cfStk (ret v k) = k := by simp [ret]

theorem isStack_stepDescend {c n k : ℕ} (h : IsStack k) :
    IsStack (cfStk (stepDescend c n k)) := by
  cases hc : Denumerable.ofNat Code c with
  | zero => simpa [stepDescend, hc] using h
  | succ => simpa [stepDescend, hc] using h
  | left => simpa [stepDescend, hc] using h
  | right => simpa [stepDescend, hc] using h
  | pair cf cg => simpa [stepDescend, hc] using isStack_cons (f := _) h
  | comp cf cg => simpa [stepDescend, hc] using isStack_cons (f := _) h
  | prec cf cg => simpa [stepDescend, hc] using isStack_cons (f := _) h
  | rfind' cf => simpa [stepDescend, hc] using isStack_cons (f := _) h

theorem isStack_stepReturn {v f k : ℕ} (h : IsStack k) :
    IsStack (cfStk (stepReturn v f k)) := by
  rcases ht : frTag f with _ | _ | _ | _ | _ | t
  · simpa [stepReturn, ht] using isStack_cons (f := _) h
  · simpa [stepReturn, ht] using h
  · simpa [stepReturn, ht] using h
  · obtain ⟨cgn, aa, yy, rr, hp⟩ :
        ∃ cgn aa yy rr, frPay f = Nat.pair cgn (Nat.pair aa (Nat.pair yy rr)) :=
      ⟨(frPay f).unpair.1, (frPay f).unpair.2.unpair.1,
        (frPay f).unpair.2.unpair.2.unpair.1, (frPay f).unpair.2.unpair.2.unpair.2, by
          simp [Nat.pair_unpair]⟩
    cases rr with
    | zero => simpa [stepReturn, ht, hp] using h
    | succ r => simpa [stepReturn, ht, hp] using isStack_cons (f := _) h
  · by_cases hv : v = 0
    · simpa [stepReturn, ht, hv] using h
    · simpa [stepReturn, ht, hv] using isStack_cons (f := _) h
  · simpa [stepReturn, ht] using isStack_cons (f := _) h

/-- **One step keeps the stack well formed.** Each case either leaves the stack alone, pushes a
cell onto it, or pops to its tail — and a cell's tail is well formed whenever the cell is. -/
theorem isStack_step {s : ℕ} (h : IsStack (cfStk s)) : IsStack (cfStk (stepUFn s)) := by
  by_cases hh : isHalt s = true
  · rwa [stepUFn_halt hh]
  · by_cases hm : cfMode s = 0
    · have hstep : stepUFn s = stepDescend (cfCur s).unpair.1 (cfCur s).unpair.2 (cfStk s) := by
        simp [stepUFn, hh, hm]
      rw [hstep]
      exact isStack_stepDescend h
    · by_cases hc : stkIsCons (cfStk s) = true
      · have hstep : stepUFn s =
            stepReturn (cfCur s) (stkHead (cfStk s)) (stkTail (cfStk s)) := by
          simp [stepUFn, hh, hm, hc]
        have htail : IsStack (stkTail (cfStk s)) := by
          rw [IsStack] at h; simpa [hc] using h
        rw [hstep]
        exact isStack_stepReturn htail
      · have hstep : stepUFn s = s := by simp [stepUFn, hh, hm, hc]
        rwa [hstep]

/-- **The stack stays well formed along any run.** The invariant the run's workspace account
consumes for the stack side: every configuration reachable from `initConfig` has a well-formed
stack, so `size_stack_le` applies to it. -/
theorem isStack_run (p x : ℕ) : ∀ τ : ℕ, IsStack (cfStk (stepUFn^[τ] (initConfig p x))) := by
  have hgen : ∀ (τ : ℕ) (s : ℕ), IsStack (cfStk s) → IsStack (cfStk (stepUFn^[τ] s)) := by
    intro τ
    induction τ with
    | zero => intro s h; exact h
    | succ t ih =>
        intro s h
        rw [Function.iterate_succ_apply]
        exact ih (stepUFn s) (isStack_step h)
  intro τ
  exact hgen τ _ (by simp [initConfig])

/-! ## How deep the stack goes: bounded recursion costs one cell

With the loop, every constructor pushes at most one cell per AST node and pops it when that node's
evaluation finishes. Bounded recursion is no longer the exception: it pushes its loop cell on the
way in, replaces that same cell on each turn of the loop, and pops it on the way out — one cell,
whatever the counter. The two facts below are the per-case account.

This is also the coherence the cost model already asserted: `TimeCost.spaceCost` prices bounded
recursion with the counter inside a `max` rather than a sum, and the machine now computes the way
that account counts. -/

/-- **Bounded recursion costs one stack cell, whatever its counter.** Entering `prec cf cg` at any
counter pushes exactly one loop cell and descends into the base case. -/
theorem stkDepth_prec_descend (cf cg : Code) (a m k : ℕ) :
    stkDepth (cfStk (stepUFn (descend (Encodable.encode (Code.prec cf cg)) (Nat.pair a m) k)))
      = stkDepth k + 1 := by
  rw [stepUFn_descend]
  simp only [stepDescend, Denumerable.ofNat_encode, Nat.unpair_pair, cfStk_descend]
  exact stkDepth_cons _ _

/-- **The loop never accumulates.** A turn of the loop replaces its cell and leaving the loop pops
it, so a configuration returning into a loop frame is never more than one cell above the frame's
tail — no matter how many turns remain. -/
theorem stkDepth_precFrame_return {v f k : ℕ} (h : frTag f = 3) :
    stkDepth (cfStk (stepReturn v f k)) ≤ stkDepth k + 1 := by
  obtain ⟨cgn, aa, yy, rr, hp⟩ :
      ∃ cgn aa yy rr, frPay f = Nat.pair cgn (Nat.pair aa (Nat.pair yy rr)) :=
    ⟨(frPay f).unpair.1, (frPay f).unpair.2.unpair.1,
      (frPay f).unpair.2.unpair.2.unpair.1, (frPay f).unpair.2.unpair.2.unpair.2, by
        simp [Nat.pair_unpair]⟩
  cases rr with
  | zero => simp [stepReturn, h, hp]
  | succ r => simp [stepReturn, h, hp, stkDepth_cons]

@[simp] theorem stkDepth_zero : stkDepth 0 = 0 := by rw [stkDepth]; simp

/-! ## The candidate run measure, and why it does not settle the depth bound

With the loop in place the stack finally holds one cell per *currently active* AST node, so the
bound `stkDepth ≤ codeDepth` is no longer refuted by bounded recursion. It is still not proved by
the obvious measure. `runMeasure` — the depth of the code about to be entered plus the stack's
depth — is non-increasing on every descending transition, but it **rises** on the transitions where
a frame is popped and the machine descends into the code that frame had stored: the second
component of a pair, the outer code of a composition, the step code of the loop. Those codes are
pending work that the measure does not see while it sits on the stack.

`runMeasure_not_antitone` exhibits it: a composition frame holding a code of depth two, returned to
over an empty stack, takes the measure from one to two.

What the bound needs instead is a per-frame invariant rather than a numeric measure — each frame
charged for the code it stores *and* for the frames beneath it:

  `StackOK k D` := at every cell, `codeDepth (stored code) + stkDepth (tail) + 1 ≤ D`

together with `pendingDepth + stkDepth ≤ D`. Pushing a cell leaves the older cells' obligations
untouched (they are stated against the frames below them, which do not move), and a return
discharges exactly the popped cell's obligation into the new pending depth. That is `StackOK`, in
the next section, and it settles the bound. -/

/-- The candidate run measure: the depth of the code still to be entered, plus the stack's depth. -/
def runMeasure (s : ℕ) : ℕ :=
  (if cfMode s = 0 then codeDepth (Denumerable.ofNat Code (cfCur s).unpair.1) else 0)
    + stkDepth (cfStk s)

/-- **The candidate measure is not non-increasing.** Returning into a frame that has stored a code
makes that code pending, and its depth enters the measure from nowhere. So `runMeasure` cannot
witness the depth bound, however the machine evaluates bounded recursion — the obstruction is the
storing of codes in frames, not the shape of any one constructor's rule. -/
theorem runMeasure_not_antitone :
    ∃ s : ℕ, runMeasure s < runMeasure (stepUFn s) := by
  refine ⟨ret 0 (stkCons (frame 2 (Encodable.encode (Code.comp Code.succ Code.succ))) 0), ?_⟩
  rw [stepUFn_ret_cons]
  simp [runMeasure, stepReturn, ret, descend, frTag_frame, frPay_frame, stkDepth_cons,
    Denumerable.ofNat_encode, codeDepth]

/-! ## The per-frame invariant, and the depth bound

Each stack cell is charged for the code it has stored *and* for the cells beneath it: at every cell,
`framePend (frame) + stkDepth (tail) + 1 ≤ D`. Paired with `pendingDepth + stkDepth ≤ D` this is
preserved by every step, and it settles the depth bound the run measure could not.

Why it works where a numeric measure does not: a cell's obligation is stated against the frames
*beneath* it, which never move, so pushing leaves every older obligation untouched. And a return
discharges exactly the popped cell's obligation into the new pending depth — the code that was
stored becomes the code that is pending, and its charge was already paid for. -/

/-- The depth of the code a frame will descend into when it is popped. -/
def framePend (f : ℕ) : ℕ :=
  match frTag f with
  | 0 => codeDepth (Denumerable.ofNat Code (frPay f).unpair.1)
  | 1 => 0
  | 2 => codeDepth (Denumerable.ofNat Code (frPay f))
  | 3 => codeDepth (Denumerable.ofNat Code (frPay f).unpair.1)
  | 4 => codeDepth (Denumerable.ofNat Code (frPay f).unpair.1)
  | _ => 0

/-- The depth of the code a configuration is about to enter, if it is descending. -/
def pendingDepth (s : ℕ) : ℕ :=
  if cfMode s = 0 then codeDepth (Denumerable.ofNat Code (cfCur s).unpair.1) else 0

@[simp] theorem pendingDepth_descend (c n k : ℕ) :
    pendingDepth (descend c n k) = codeDepth (Denumerable.ofNat Code c) := by
  simp [pendingDepth, descend]

@[simp] theorem pendingDepth_ret (v k : ℕ) : pendingDepth (ret v k) = 0 := by
  simp [pendingDepth, ret]

/-- **The per-frame obligation.** Every cell is charged for the code it stores together with the
cells beneath it. -/
def StackOK (k D : ℕ) : Prop :=
  if _h : stkIsCons k = true then
    framePend (stkHead k) + stkDepth (stkTail k) + 1 ≤ D ∧ StackOK (stkTail k) D
  else True
termination_by k
decreasing_by exact stkTail_lt _h

@[simp] theorem stackOK_zero (D : ℕ) : StackOK 0 D := by rw [StackOK]; simp

@[simp] theorem stackOK_cons (f k D : ℕ) :
    StackOK (stkCons f k) D ↔ (framePend f + stkDepth k + 1 ≤ D ∧ StackOK k D) := by
  rw [StackOK]; simp

/-- A configuration meets its budget: what it is about to do fits above its stack, and every cell
of that stack meets its own obligation. -/
def ConfigOK (s D : ℕ) : Prop :=
  pendingDepth s + stkDepth (cfStk s) ≤ D ∧ StackOK (cfStk s) D

theorem framePend_tag0 {f : ℕ} (h : frTag f = 0) :
    framePend f = codeDepth (Denumerable.ofNat Code (frPay f).unpair.1) := by simp [framePend, h]

theorem framePend_tag1 {f : ℕ} (h : frTag f = 1) : framePend f = 0 := by simp [framePend, h]

theorem framePend_tag2 {f : ℕ} (h : frTag f = 2) :
    framePend f = codeDepth (Denumerable.ofNat Code (frPay f)) := by simp [framePend, h]

theorem framePend_tag3 {f : ℕ} (h : frTag f = 3) :
    framePend f = codeDepth (Denumerable.ofNat Code (frPay f).unpair.1) := by simp [framePend, h]

theorem framePend_tag4 {f : ℕ} (h : frTag f = 4) :
    framePend f = codeDepth (Denumerable.ofNat Code (frPay f).unpair.1) := by simp [framePend, h]

theorem framePend_other {f t : ℕ} (h : frTag f = t + 5) : framePend f = 0 := by
  simp [framePend, h]

theorem configOK_stepDescend {c n k D : ℕ}
    (hd : codeDepth (Denumerable.ofNat Code c) + stkDepth k ≤ D) (hs : StackOK k D) :
    ConfigOK (stepDescend c n k) D := by
  cases hc : Denumerable.ofNat Code c with
  | zero =>
      rw [hc] at hd; simp only [codeDepth] at hd
      exact ⟨by simp only [stepDescend, hc, cfStk_ret, pendingDepth_ret]; omega,
        by simpa only [stepDescend, hc, cfStk_ret] using hs⟩
  | succ =>
      rw [hc] at hd; simp only [codeDepth] at hd
      exact ⟨by simp only [stepDescend, hc, cfStk_ret, pendingDepth_ret]; omega,
        by simpa only [stepDescend, hc, cfStk_ret] using hs⟩
  | left =>
      rw [hc] at hd; simp only [codeDepth] at hd
      exact ⟨by simp only [stepDescend, hc, cfStk_ret, pendingDepth_ret]; omega,
        by simpa only [stepDescend, hc, cfStk_ret] using hs⟩
  | right =>
      rw [hc] at hd; simp only [codeDepth] at hd
      exact ⟨by simp only [stepDescend, hc, cfStk_ret, pendingDepth_ret]; omega,
        by simpa only [stepDescend, hc, cfStk_ret] using hs⟩
  | pair cf cg =>
      rw [hc] at hd; simp only [codeDepth] at hd
      refine ⟨?_, ?_⟩ <;>
        simp only [stepDescend, hc, cfStk_descend, pendingDepth_descend, Denumerable.ofNat_encode,
          stkDepth_cons, stackOK_cons, framePend, frTag_frame, frPay_frame, Nat.unpair_pair]
      · omega
      · exact ⟨by omega, hs⟩
  | comp cf cg =>
      rw [hc] at hd; simp only [codeDepth] at hd
      refine ⟨?_, ?_⟩ <;>
        simp only [stepDescend, hc, cfStk_descend, pendingDepth_descend, Denumerable.ofNat_encode,
          stkDepth_cons, stackOK_cons, framePend, frTag_frame, frPay_frame]
      · omega
      · exact ⟨by omega, hs⟩
  | prec cf cg =>
      rw [hc] at hd; simp only [codeDepth] at hd
      refine ⟨?_, ?_⟩ <;>
        simp only [stepDescend, hc, cfStk_descend, pendingDepth_descend, Denumerable.ofNat_encode,
          stkDepth_cons, stackOK_cons, framePend, frTag_frame, frPay_frame, Nat.unpair_pair]
      · omega
      · exact ⟨by omega, hs⟩
  | rfind' cf =>
      rw [hc] at hd; simp only [codeDepth] at hd
      refine ⟨?_, ?_⟩ <;>
        simp only [stepDescend, hc, cfStk_descend, pendingDepth_descend, Denumerable.ofNat_encode,
          stkDepth_cons, stackOK_cons, framePend, frTag_frame, frPay_frame, Nat.unpair_pair]
      · omega
      · exact ⟨by omega, hs⟩

theorem configOK_stepReturn {v f k D : ℕ}
    (hf : framePend f + stkDepth k + 1 ≤ D) (hs : StackOK k D) :
    ConfigOK (stepReturn v f k) D := by
  rcases ht : frTag f with _ | _ | _ | _ | _ | tg
  · -- a pair's left value: run the second component, remember this one
    rw [framePend_tag0 ht] at hf
    refine ⟨?_, ?_⟩ <;>
      simp only [stepReturn, ht, cfStk_descend, pendingDepth_descend, stkDepth_cons,
        stackOK_cons, framePend, frTag_frame]
    · omega
    · exact ⟨by omega, hs⟩
  · -- a pair's right value: form the pair and return it
    exact ⟨by simp only [stepReturn, ht, cfStk_ret, pendingDepth_ret]; omega,
      by simpa only [stepReturn, ht, cfStk_ret] using hs⟩
  · -- a composition's inner value: run the outer code
    rw [framePend_tag2 (by simpa using ht)] at hf
    exact ⟨by simp only [stepReturn, ht, cfStk_descend, pendingDepth_descend]; omega,
      by simpa only [stepReturn, ht, cfStk_descend] using hs⟩
  · -- the bounded-recursion loop
    obtain ⟨cgn, aa, yy, rr, hp⟩ :
        ∃ cgn aa yy rr, frPay f = Nat.pair cgn (Nat.pair aa (Nat.pair yy rr)) :=
      ⟨(frPay f).unpair.1, (frPay f).unpair.2.unpair.1,
        (frPay f).unpair.2.unpair.2.unpair.1, (frPay f).unpair.2.unpair.2.unpair.2, by
          simp [Nat.pair_unpair]⟩
    rw [framePend_tag3 (by simpa using ht), hp, Nat.unpair_pair] at hf
    cases rr with
    | zero =>
        exact ⟨by simp only [stepReturn, ht, hp, Nat.unpair_pair, if_true, cfStk_ret,
                    pendingDepth_ret]
                  omega,
          by simpa only [stepReturn, ht, hp, Nat.unpair_pair, eq_self_iff_true, if_true,
                cfStk_ret] using hs⟩
    | succ r =>
        refine ⟨?_, ?_⟩ <;>
          simp only [stepReturn, ht, hp, Nat.unpair_pair, Nat.succ_ne_zero, if_false,
            Nat.succ_sub_one, cfStk_descend, pendingDepth_descend, stkDepth_cons, stackOK_cons,
            framePend, frTag_frame, frPay_frame]
        · omega
        · exact ⟨by omega, hs⟩
  · -- the search frame
    obtain ⟨cfn, aa, mm, hp⟩ : ∃ cfn aa mm, frPay f = Nat.pair cfn (Nat.pair aa mm) :=
      ⟨(frPay f).unpair.1, (frPay f).unpair.2.unpair.1, (frPay f).unpair.2.unpair.2, by
        simp [Nat.pair_unpair]⟩
    rw [framePend_tag4 (by simpa using ht), hp, Nat.unpair_pair] at hf
    by_cases hv : v = 0
    · exact ⟨by simp only [stepReturn, ht, hp, hv, Nat.unpair_pair, if_true, cfStk_ret,
                  pendingDepth_ret]
                omega,
        by simpa only [stepReturn, ht, hp, hv, Nat.unpair_pair, eq_self_iff_true, if_true,
              cfStk_ret] using hs⟩
    · refine ⟨?_, ?_⟩ <;>
        simp only [stepReturn, ht, hp, hv, if_false, Nat.unpair_pair, cfStk_descend,
          pendingDepth_descend, stkDepth_cons, stackOK_cons, framePend, frTag_frame, frPay_frame]
      · omega
      · exact ⟨by omega, hs⟩
  · -- an unrecognized frame: the machine is stuck, the stack is unchanged
    exact ⟨by simp only [stepReturn, ht, cfStk_ret, pendingDepth_ret, stkDepth_cons]; omega,
      by simp only [stepReturn, ht, cfStk_ret, stackOK_cons]; exact ⟨hf, hs⟩⟩

/-- **One step keeps a configuration within its budget.** All thirteen cases: a descent spends one
level of the code it decoded, a return spends the obligation of the cell it popped, and a halted or
stuck configuration does not move. -/
theorem configOK_step {s D : ℕ} (h : ConfigOK s D) : ConfigOK (stepUFn s) D := by
  by_cases hh : isHalt s = true
  · rwa [stepUFn_halt hh]
  · by_cases hm : cfMode s = 0
    · have hstep : stepUFn s = stepDescend (cfCur s).unpair.1 (cfCur s).unpair.2 (cfStk s) := by
        simp [stepUFn, hh, hm]
      rw [hstep]
      exact configOK_stepDescend (by simpa [pendingDepth, hm] using h.1) h.2
    · by_cases hc : stkIsCons (cfStk s) = true
      · have hstep : stepUFn s =
            stepReturn (cfCur s) (stkHead (cfStk s)) (stkTail (cfStk s)) := by
          simp [stepUFn, hh, hm, hc]
        have hok := h.2
        rw [StackOK, dif_pos hc] at hok
        rw [hstep]
        exact configOK_stepReturn hok.1 hok.2
      · have hstep : stepUFn s = s := by simp [stepUFn, hh, hm, hc]
        rwa [hstep]

/-- The initial configuration meets the budget its own code sets. -/
theorem configOK_init (p x : ℕ) :
    ConfigOK (initConfig p x) (codeDepth (Denumerable.ofNat Code p)) :=
  ⟨by simp [initConfig], by simp [initConfig]⟩

/-- **The stack never goes deeper than the code.** Along any run from `initConfig p x`, the stack
holds at most `codeDepth (ofNat p)` cells — one per active node of the code being interpreted, with
bounded recursion contributing one apiece however large its counters.

With `size_stack_le` this bounds the workspace a run occupies: a stack of at most `codeDepth` cells
whose frames are at most `F` bits wide costs at most `codeDepth * (2F + 2)` bits. -/
theorem stkDepth_run_le (p x : ℕ) : ∀ τ : ℕ,
    stkDepth (cfStk (stepUFn^[τ] (initConfig p x))) ≤ codeDepth (Denumerable.ofNat Code p) := by
  have hgen : ∀ (τ : ℕ) (s D : ℕ), ConfigOK s D → ConfigOK (stepUFn^[τ] s) D := by
    intro τ
    induction τ with
    | zero => intro s D h; exact h
    | succ t ih =>
        intro s D h
        rw [Function.iterate_succ_apply]
        exact ih (stepUFn s) D (configOK_step h)
  intro τ
  have h := hgen τ (initConfig p x) _ (configOK_init p x)
  exact le_trans (Nat.le_add_left _ _) h.1

/-! ## Runs: composing the machine's transitions

`Reaches s t` says the machine gets from `s` to `t` in some number of steps. Runs compose by adding
iterate counts, which is all the algebra the completeness argument needs: each constructor's run is
a step, a sub-run, a step, a sub-run, and so on.

The transition lemmas below are the machine's rules in the form a run-composition proof uses —
one per descending constructor and one per frame, with the frame payloads already destructured. -/

/-- The machine gets from `s` to `t` in some number of steps. -/
def Reaches (s t : ℕ) : Prop := ∃ τ : ℕ, stepUFn^[τ] s = t

theorem Reaches.refl (s : ℕ) : Reaches s s := ⟨0, rfl⟩

theorem Reaches.trans {s t u : ℕ} (h₁ : Reaches s t) (h₂ : Reaches t u) : Reaches s u := by
  obtain ⟨τ₁, h₁⟩ := h₁
  obtain ⟨τ₂, h₂⟩ := h₂
  exact ⟨τ₂ + τ₁, by rw [Function.iterate_add_apply, h₁, h₂]⟩

/-- One transition, then a run. -/
theorem Reaches.head {s t u : ℕ} (h₁ : stepUFn s = t) (h₂ : Reaches t u) : Reaches s u :=
  Reaches.trans ⟨1, by simpa using h₁⟩ h₂

/-- A halted configuration reports its value. -/
theorem isHalt_of_reaches_ret {s v : ℕ} (h : Reaches s (ret v 0)) :
    ∃ τ, isHalt (stepUFn^[τ] s) = true ∧ haltVal (stepUFn^[τ] s) = v := by
  obtain ⟨τ, hτ⟩ := h
  exact ⟨τ, by rw [hτ]; simp, by rw [hτ]; simp⟩

/-! ### The descending transitions -/

theorem step_zero (n stk : ℕ) :
    stepUFn (descend (Encodable.encode Code.zero) n stk) = ret 0 stk := by
  rw [stepUFn_descend]; simp [stepDescend]

theorem step_succ (n stk : ℕ) :
    stepUFn (descend (Encodable.encode Code.succ) n stk) = ret (n + 1) stk := by
  rw [stepUFn_descend]; simp [stepDescend]

theorem step_left (n stk : ℕ) :
    stepUFn (descend (Encodable.encode Code.left) n stk) = ret n.unpair.1 stk := by
  rw [stepUFn_descend]; simp [stepDescend]

theorem step_right (n stk : ℕ) :
    stepUFn (descend (Encodable.encode Code.right) n stk) = ret n.unpair.2 stk := by
  rw [stepUFn_descend]; simp [stepDescend]

theorem step_pair (cf cg n stk : ℕ) :
    stepUFn (descend (Encodable.encode (Code.pair (Denumerable.ofNat Code cf)
        (Denumerable.ofNat Code cg))) n stk)
      = descend cf n (stkCons (frame 0 (Nat.pair cg n)) stk) := by
  rw [stepUFn_descend]
  simp [stepDescend, Denumerable.encode_ofNat]

theorem step_comp (cf cg n stk : ℕ) :
    stepUFn (descend (Encodable.encode (Code.comp (Denumerable.ofNat Code cf)
        (Denumerable.ofNat Code cg))) n stk)
      = descend cg n (stkCons (frame 2 cf) stk) := by
  rw [stepUFn_descend]
  simp [stepDescend, Denumerable.encode_ofNat]

theorem step_prec (cf cg a m stk : ℕ) :
    stepUFn (descend (Encodable.encode (Code.prec (Denumerable.ofNat Code cf)
        (Denumerable.ofNat Code cg))) (Nat.pair a m) stk)
      = descend cf a (stkCons (frame 3 (Nat.pair cg (Nat.pair a (Nat.pair 0 m)))) stk) := by
  rw [stepUFn_descend]
  simp [stepDescend, Denumerable.encode_ofNat]

theorem step_rfind (cf a m stk : ℕ) :
    stepUFn (descend (Encodable.encode (Code.rfind' (Denumerable.ofNat Code cf)))
        (Nat.pair a m) stk)
      = descend cf (Nat.pair a m)
          (stkCons (frame 4 (Nat.pair cf (Nat.pair a m))) stk) := by
  rw [stepUFn_descend]
  simp [stepDescend, Denumerable.encode_ofNat]

/-! ### The returning transitions -/

theorem step_ret_pairR (v cg n stk : ℕ) :
    stepUFn (ret v (stkCons (frame 0 (Nat.pair cg n)) stk))
      = descend cg n (stkCons (frame 1 v) stk) := by
  rw [stepUFn_ret_cons]; simp [stepReturn]

theorem step_ret_pairL (v w stk : ℕ) :
    stepUFn (ret w (stkCons (frame 1 v) stk)) = ret (Nat.pair v w) stk := by
  rw [stepUFn_ret_cons]; simp [stepReturn]

theorem step_ret_comp (v cf stk : ℕ) :
    stepUFn (ret v (stkCons (frame 2 cf) stk)) = descend cf v stk := by
  rw [stepUFn_ret_cons]; simp [stepReturn]

theorem step_ret_loop_done (v cg a y stk : ℕ) :
    stepUFn (ret v (stkCons (frame 3 (Nat.pair cg (Nat.pair a (Nat.pair y 0)))) stk))
      = ret v stk := by
  rw [stepUFn_ret_cons]; simp [stepReturn]

theorem step_ret_loop_turn (v cg a y r stk : ℕ) :
    stepUFn (ret v (stkCons (frame 3 (Nat.pair cg (Nat.pair a (Nat.pair y (r + 1))))) stk))
      = descend cg (Nat.pair a (Nat.pair y v))
          (stkCons (frame 3 (Nat.pair cg (Nat.pair a (Nat.pair (y + 1) r)))) stk) := by
  rw [stepUFn_ret_cons]; simp [stepReturn]

theorem step_ret_search_found (cf a m stk : ℕ) :
    stepUFn (ret 0 (stkCons (frame 4 (Nat.pair cf (Nat.pair a m))) stk)) = ret m stk := by
  rw [stepUFn_ret_cons]; simp [stepReturn]

theorem step_ret_search_again {v : ℕ} (hv : v ≠ 0) (cf a m stk : ℕ) :
    stepUFn (ret v (stkCons (frame 4 (Nat.pair cf (Nat.pair a m))) stk))
      = descend cf (Nat.pair a (m + 1))
          (stkCons (frame 4 (Nat.pair cf (Nat.pair a (m + 1)))) stk) := by
  rw [stepUFn_ret_cons]; simp [stepReturn, hv]

/-! ## Transition rules, stated at codes -/

theorem step_pair' (cf cg : Code) (n stk : ℕ) :
    stepUFn (descend (Encodable.encode (Code.pair cf cg)) n stk)
      = descend (Encodable.encode cf) n
          (stkCons (frame 0 (Nat.pair (Encodable.encode cg) n)) stk) := by
  rw [stepUFn_descend]; simp [stepDescend]

theorem step_comp' (cf cg : Code) (n stk : ℕ) :
    stepUFn (descend (Encodable.encode (Code.comp cf cg)) n stk)
      = descend (Encodable.encode cg) n (stkCons (frame 2 (Encodable.encode cf)) stk) := by
  rw [stepUFn_descend]; simp [stepDescend]

theorem step_prec' (cf cg : Code) (a m stk : ℕ) :
    stepUFn (descend (Encodable.encode (Code.prec cf cg)) (Nat.pair a m) stk)
      = descend (Encodable.encode cf) a
          (stkCons (frame 3 (Nat.pair (Encodable.encode cg)
            (Nat.pair a (Nat.pair 0 m)))) stk) := by
  rw [stepUFn_descend]; simp [stepDescend]

theorem step_rfind' (cf : Code) (a m stk : ℕ) :
    stepUFn (descend (Encodable.encode (Code.rfind' cf)) (Nat.pair a m) stk)
      = descend (Encodable.encode cf) (Nat.pair a m)
          (stkCons (frame 4 (Nat.pair (Encodable.encode cf) (Nat.pair a m))) stk) := by
  rw [stepUFn_descend]; simp [stepDescend]

/-- A descending configuration is never a returning one. -/
theorem descend_ne_ret (c n k v k' : ℕ) : descend c n k ≠ ret v k' := by
  intro h
  have : cfMode (descend c n k) = cfMode (ret v k') := by rw [h]
  simp [descend, ret] at this

/-- Peel the first transition off a run that must take at least one. -/
theorem Reaches.tail {s t u : ℕ} (hst : stepUFn s = t) (hne : s ≠ u) (h : Reaches s u) :
    Reaches t u := by
  obtain ⟨τ, hτ⟩ := h
  cases τ with
  | zero => exact absurd hτ hne
  | succ j => exact ⟨j, by rw [← hst, ← Function.iterate_succ_apply]; exact hτ⟩

/-! ## Facts about the fuelled evaluator's bounded recursion

Two facts about Mathlib's `evaln` at `prec`, with no machine content. They reconcile the two
directions in which bounded recursion can be computed: the fuelled evaluator descends from the
counter, spending a level of fuel each time, while a stack machine that keeps one loop frame climbs
from the base case. What the climb needs is the chain of intermediate values, and these recover it —
the clause at counter `y + 1` names the value at `y`, and fuel monotonicity lifts it back. -/

set_option linter.flexible false in
/-- **Downward closure.** If bounded recursion is defined at counter `j + 1`, it is defined at `j`:
the clause at `j + 1` evaluates it, one level of fuel down, and fuel monotonicity lifts the witness
back up. -/
theorem evaln_prec_defined_below {k : ℕ} {cf cg : Code} {a j w : ℕ}
    (hw : w ∈ evaln (k + 1) (Code.prec cf cg) (Nat.pair a (j + 1))) :
    ∃ v, v ∈ evaln (k + 1) (Code.prec cf cg) (Nat.pair a j) := by
  simp [evaln, Option.bind_eq_some_iff] at hw
  obtain ⟨-, i, hi, -⟩ := hw
  exact ⟨i, evaln_mono (Nat.le_succ k) hi⟩

set_option linter.flexible false in
/-- **The value chain.** If bounded recursion gives `v` at counter `y` and `w` at counter `y + 1`,
then `w` is what the step code produces from `v`. This is what lets the climb take its next turn.

Proof: the clause at `y + 1` exhibits some `i` at counter `y` one level of fuel down; monotonicity
puts `i` at this fuel, and a partial function has at most one value, so `i = v`. -/
theorem evaln_prec_stepUp {k : ℕ} {cf cg : Code} {a y v w : ℕ}
    (hv : v ∈ evaln (k + 1) (Code.prec cf cg) (Nat.pair a y))
    (hw : w ∈ evaln (k + 1) (Code.prec cf cg) (Nat.pair a (y + 1))) :
    w ∈ evaln (k + 1) cg (Nat.pair a (Nat.pair y v)) := by
  simp [evaln, Option.bind_eq_some_iff] at hw
  obtain ⟨-, i, hi, hcg⟩ := hw
  have hi' : i ∈ evaln (k + 1) (Code.prec cf cg) (Nat.pair a y) :=
    evaln_mono (Nat.le_succ k) hi
  have : i = v := Option.mem_unique hi' hv
  subst this
  exact hcg

set_option linter.flexible false in
/-- Bounded recursion at counter zero is the base code. -/
theorem evaln_prec_base {k : ℕ} {cf cg : Code} {a v : ℕ}
    (h : v ∈ evaln (k + 1) (Code.prec cf cg) (Nat.pair a 0)) : v ∈ evaln (k + 1) cf a := by
  simp [evaln, Option.bind_eq_some_iff] at h
  exact h.2

/-- Downward closure, iterated: defined at `m` means defined everywhere below. -/
theorem evaln_prec_defined_le {k : ℕ} {cf cg : Code} {a : ℕ} : ∀ (m x : ℕ),
    x ∈ evaln (k + 1) (Code.prec cf cg) (Nat.pair a m) →
    ∀ j ≤ m, ∃ v, v ∈ evaln (k + 1) (Code.prec cf cg) (Nat.pair a j) := by
  intro m
  induction m with
  | zero => intro x hx j hj; rw [Nat.le_zero.1 hj]; exact ⟨x, hx⟩
  | succ m ihm =>
      intro x hx j hj
      rcases Nat.lt_or_ge j (m + 1) with hlt | hge
      · obtain ⟨v, hv⟩ := evaln_prec_defined_below hx
        exact ihm v hv j (by omega)
      · rw [show j = m + 1 from by omega]
        exact ⟨x, hx⟩

/-! ## The loop, run -/

set_option linter.flexible false in
/-- **The bounded-recursion loop's run.** From the loop frame at counter `y` holding the value
bounded recursion has there, the machine reaches the return of the value at counter `y + r`.

Induction on the turns remaining. Each turn takes one transition into the step code
(`step_ret_loop_turn`), a sub-run of that code — which `evaln_prec_stepUp` certifies computes the
next value — and lands back on the loop frame one counter up; the last turn leaves by
`step_ret_loop_done`. -/
theorem prec_loop_reaches {k : ℕ} {cf cg : Code} {a : ℕ}
    (ihg : ∀ (n x stk : ℕ), x ∈ evaln (k + 1) cg n →
        Reaches (descend (Encodable.encode cg) n stk) (ret x stk)) :
    ∀ (r y v x stk : ℕ),
      v ∈ evaln (k + 1) (Code.prec cf cg) (Nat.pair a y) →
      x ∈ evaln (k + 1) (Code.prec cf cg) (Nat.pair a (y + r)) →
      Reaches (ret v (stkCons (frame 3 (Nat.pair (Encodable.encode cg)
          (Nat.pair a (Nat.pair y r)))) stk)) (ret x stk) := by
  intro r
  induction r with
  | zero =>
      intro y v x stk hv hx
      rw [Nat.add_zero] at hx
      have hvx : v = x := Option.mem_unique hv hx
      subst hvx
      exact Reaches.head (step_ret_loop_done _ _ _ _ _) (Reaches.refl _)
  | succ r ihr =>
      intro y v x stk hv hx
      obtain ⟨w, hw⟩ := evaln_prec_defined_le (y + (r + 1)) x hx (y + 1) (by omega)
      have hcg := evaln_prec_stepUp hv hw
      refine Reaches.head (step_ret_loop_turn _ _ _ _ _ _) ?_
      refine Reaches.trans (ihg _ _ _ hcg) ?_
      exact ihr (y + 1) w x stk hw (by rw [show y + 1 + r = y + (r + 1) from by omega]; exact hx)

/-! ## Completeness -/

set_option linter.flexible false in
/-- **Every fuelled computation is a run of the machine.** If the fuelled evaluator produces `x`
from `c` at `n`, then the machine, started descending into `c` at `n` above any stack, returns `x`
onto that same stack.

Induction on the fuel, with a nested structural induction on the code: the sub-calls at the same
fuel are on structurally smaller codes, and the sub-calls one level of fuel down — bounded
recursion's counter and unbounded search's next probe — are the outer hypothesis. The stack is
universally quantified, which is what makes the sub-runs composable. -/
theorem evaln_reaches : ∀ (K : ℕ) (c : Code) (n x : ℕ), x ∈ evaln K c n →
    ∀ stk, Reaches (descend (Encodable.encode c) n stk) (ret x stk) := by
  intro K
  induction K with
  | zero => intro c n x h; simp [evaln] at h
  | succ k ih =>
      intro c
      induction c with
      | zero =>
          intro n x h stk
          simp [evaln, Option.bind_eq_some_iff] at h
          obtain ⟨-, rfl⟩ := h
          exact Reaches.head (step_zero _ _) (Reaches.refl _)
      | succ =>
          intro n x h stk
          simp [evaln, Option.bind_eq_some_iff] at h
          obtain ⟨-, rfl⟩ := h
          exact Reaches.head (step_succ _ _) (Reaches.refl _)
      | left =>
          intro n x h stk
          simp [evaln, Option.bind_eq_some_iff] at h
          obtain ⟨-, rfl⟩ := h
          exact Reaches.head (step_left _ _) (Reaches.refl _)
      | right =>
          intro n x h stk
          simp [evaln, Option.bind_eq_some_iff] at h
          obtain ⟨-, rfl⟩ := h
          exact Reaches.head (step_right _ _) (Reaches.refl _)
      | pair cf cg ihf ihg =>
          intro n x h stk
          simp [evaln, Option.bind_eq_some_iff, Seq.seq] at h
          obtain ⟨-, u, hu, v, hv, rfl⟩ := h
          refine Reaches.head (step_pair' cf cg n stk) ?_
          refine Reaches.trans (ihf n u hu _) ?_
          refine Reaches.head (step_ret_pairR u (Encodable.encode cg) n stk) ?_
          refine Reaches.trans (ihg n v hv _) ?_
          exact Reaches.head (step_ret_pairL u v stk) (Reaches.refl _)
      | comp cf cg ihf ihg =>
          intro n x h stk
          simp [evaln, Option.bind_eq_some_iff] at h
          obtain ⟨-, u, hu, hx⟩ := h
          refine Reaches.head (step_comp' cf cg n stk) ?_
          refine Reaches.trans (ihg n u hu _) ?_
          refine Reaches.head (step_ret_comp u (Encodable.encode cf) stk) ?_
          exact ihf u x hx stk
      | prec cf cg ihf ihg =>
          intro n x h stk
          obtain ⟨a, m, rfl⟩ : ∃ a m, n = Nat.pair a m :=
            ⟨n.unpair.1, n.unpair.2, (Nat.pair_unpair n).symm⟩
          obtain ⟨v0, hv0⟩ := evaln_prec_defined_le m x h 0 (Nat.zero_le m)
          refine Reaches.head (step_prec' cf cg a m stk) ?_
          refine Reaches.trans (ihf a v0 (evaln_prec_base hv0) _) ?_
          exact prec_loop_reaches (fun nn xx sk hxx => ihg nn xx hxx sk) m 0 v0 x stk hv0
            (by rw [Nat.zero_add]; exact h)
      | rfind' cf ihf =>
          intro n x h stk
          obtain ⟨a, m, rfl⟩ : ∃ a m, n = Nat.pair a m :=
            ⟨n.unpair.1, n.unpair.2, (Nat.pair_unpair n).symm⟩
          simp [evaln, Option.bind_eq_some_iff] at h
          obtain ⟨-, u, hu, hx⟩ := h
          refine Reaches.head (step_rfind' cf a m stk) ?_
          refine Reaches.trans (ihf (Nat.pair a m) u hu _) ?_
          by_cases hu0 : u = 0
          · subst hu0
            simp at hx
            subst hx
            exact Reaches.head (step_ret_search_found _ _ _ _) (Reaches.refl _)
          · rw [if_neg hu0] at hx
            refine Reaches.head (step_ret_search_again hu0 _ _ _ _) ?_
            have hrun := ih (Code.rfind' cf) (Nat.pair a (m + 1)) x hx stk
            exact Reaches.tail (step_rfind' cf a (m + 1) stk) (descend_ne_ret _ _ _ _ _) hrun

/-- **Completeness.** Every value the code produces is reached by the machine: if `x ∈ eval c n`
then some number of steps from `initConfig` halts with `x`.

With `machine_sound` this closes the machine's semantics against `Code.eval` — the two directions
together, on all of `Nat.Partrec.Code`, with no fragment restriction. -/
theorem machine_complete {c : Code} {n x : ℕ} (h : x ∈ eval c n) :
    ∃ τ : ℕ, isHalt (stepUFn^[τ] (initConfig (Encodable.encode c) n)) = true ∧
      haltVal (stepUFn^[τ] (initConfig (Encodable.encode c) n)) = x := by
  obtain ⟨K, hK⟩ := evaln_complete.1 h
  exact isHalt_of_reaches_ret (evaln_reaches K c n x hK 0)

/-! ## Realizing the step function: what the toolkit charges

`stepUFn` is a function on numerals. Turning it into a `Nat.Partrec.Code` raises a question the
mathematical layer never had to answer — what the eight constructors actually charge for the
operations it performs. The inventory, taken against the definitions above:

**Available directly**, as compositions of `left`, `right`, `pair`, `succ` and `zero`, with a step
count independent of the input: the configuration accessors (`cfMode`, `cfCur`, `cfStk`), the frame
accessors (`frTag`, `frPay`), the constructors `descend`, `ret`, `frame`, the four-deep `unpair`
chains that read a loop or search payload, and the successor on a counter.

**Not available**, at any cost, without bounded recursion: `Nat.Partrec.Code` has eight
constructors and no arithmetic primitive beyond `succ`. Addition of two variables, multiplication,
truncated subtraction, division, remainder, powers with a variable exponent, `Nat.size`,
`trailOnes`, and every equality or comparison test must each be built from `prec`. That covers the
whole of the stack's packing (`stkCons`, `stkBody`, `stkLen`, `stkHead`, `stkTail`, `stkIsCons`),
the halt test, every branch condition, and the arithmetic form of the constructor dispatch.

**Why this matters for cost, and not only for size.** `tc_precFree_const` below makes the premise
exact: a code built without bounded recursion or search charges a number of steps that does not
depend on its input at all. That is what would license an absolute constant for one step of the
machine. Bounded recursion breaks it in a specific way — `TimeCost.tc_prec_le` charges
`(B + 1) * n` for a counter `n`, linear in the *value* of the counter rather than in its
bit-length. So a realization that builds addition from `prec` pays a number of steps proportional
to the numbers it is adding, not to how many bits they occupy.

The workspace side is untouched by this: `TimeCost.spaceCost_prec_le` bounds bounded recursion by a
`max` rather than a sum, so a realization can still occupy workspace proportional to the
configuration it holds while taking astronomically many steps. That contrast is already recorded
elsewhere in this development for the bounded checker; it applies here for the same reason. -/

/-- Codes built without bounded recursion or unbounded search. -/
def PrecFree : Code → Prop
  | Code.zero => True
  | Code.succ => True
  | Code.left => True
  | Code.right => True
  | Code.pair cf cg => PrecFree cf ∧ PrecFree cg
  | Code.comp cf cg => PrecFree cf ∧ PrecFree cg
  | Code.prec _ _ => False
  | Code.rfind' _ => False

/-- **A code without bounded recursion takes the same number of steps on every input.** Its step
count is a property of its syntax alone: leaves cost one, `pair` and `comp` add their parts' costs
and one more, and no clause consults the value flowing through.

This is the exact content of "a fixed constructor-free-of-recursion skeleton costs an absolute
constant per step" — and, read the other way, it is what a realization gives up the moment it needs
bounded recursion to add two numbers. -/
theorem tc_precFree_const :
    ∀ {c : Code}, PrecFree c → ∀ m n, TimeCost.tc c m = TimeCost.tc c n := by
  intro c
  induction c with
  | zero => intro _ m n; rfl
  | succ => intro _ m n; rfl
  | left => intro _ m n; rfl
  | right => intro _ m n; rfl
  | pair cf cg ihf ihg =>
      intro h m n
      obtain ⟨hf, hg⟩ := h
      rw [TimeCost.tc_pair, TimeCost.tc_pair, ihf hf m n, ihg hg m n]
  | comp cf cg ihf ihg =>
      intro h m n
      obtain ⟨hf, hg⟩ := h
      rw [TimeCost.tc_comp, TimeCost.tc_comp, ihg hg m n,
        ihf hf (TimeCost.val cg m) (TimeCost.val cg n)]
  | prec cf cg _ _ => intro h; exact h.elim
  | rfind' cf _ => intro h; exact h.elim

end BoundedInterp
