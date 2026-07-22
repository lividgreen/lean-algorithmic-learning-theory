/-
Copyright (c) 2026 Mykola Palamarchuk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mykola Palamarchuk
-/
import ALT.CapacityBoundedEval
import ALT.AdditiveComplexity
import ALT.Realizability

-- Formal-check file, not Mathlib-destined: opt out of the house-style header linter.
set_option linter.style.header false

/-!
# Transporting a realizer, and what it costs in each currency ([Decoupling] §4.5)

Provenance: [Decoupling] §4.5 — the action on realizers that a general representation functor
(Conjecture 4.4) must have, priced.

## What a transport is
A change of encoding convention does not change which function is being computed, only how its
arguments and values are written down. On a fixed partial combinatory algebra that change is itself
coded: given a coded retraction pair `(c_emb, c_proj)` for the input convention and a coded map
`c_emb` for the output convention, a realizer `r` is carried to the **conjugation**

  `transport c_emb c_proj r = comp c_emb (comp r c_proj)`

— re-encode the argument back to the old convention, run `r`, re-encode the result. `eval_transport`
and `realizes_transport` say this conjugate realizes the same function against the new conventions,
given the retraction identity on the codes actually used. Finiteness is what supplies such pairs in
the intended setting: every map between finite assemblies is realized.

## Boundary
This is the **fixed-PCA transport** — re-encoding within one assembly category, over Kleene's first
algebra as realized on `Nat.Partrec.Code`. The full per-subsystem functor, with its connection to
the state-level bitstring layout, stays paper-level and is not established here. Nothing below
quantifies over subsystems or mentions a state layout.

## The two currencies, and the variable that is absent
The point of pricing the conjugation is that its two costs obey *different* algebras:

* **description length ADDS** — `elen_transport` is an exact identity,
  `elen (transport …) = elen c_emb + elen r + elen c_proj + 6`, the two `+3`s being the
  serialization's own overhead for the two `comp` nodes;
* **workspace MAXES** — `spaceCost_transport_le` bounds the conjugate by `max g b`, where `g` is the
  realizer's own workspace grade and `b` the re-encoders'. Composition never sums workspace, so
  conjugating a realizer costs no more room than the wider of the two jobs.

The pairing factor of `2` that the workspace family charges elsewhere does not appear: a conjugation
is built from `comp` alone and never forms a pair, so no packing is paid for.

**The dilation `τ` does not occur in either currency, and this is a finding rather than an
omission.** A dilation relates the *clocks* of two dynamical systems — it multiplies along a tower
of hosting squares and prices time. The transport lemma prices one application of one realizer, and
a re-encoding does not run the host any longer or shorter. So the grade law reads: lengths add,
workspaces max, and dilations multiply somewhere else entirely — at the level of the dynamics, not
of the per-application realizer cost. A reader who expects `τ` in the bound should read this
paragraph rather than look for a dropped variable.
-/

namespace GradeTransport

open Nat.Partrec (Code)
open Nat.Partrec.Code
open TimeCost AdditiveComplexity Realizability

/-! ## The coded conjugation -/

/-- **The transport of a realizer along a change of encoding**: re-encode the argument back to the
source convention with `c_proj`, run `r`, then re-encode the result with `c_emb`. A single code,
built from `comp` alone. -/
def transport (c_emb c_proj r : Code) : Code := comp c_emb (comp r c_proj)

/-! ## Correctness: the conjugate computes the same function -/

/-- **The tracking equation transports.** If `r` takes the source encoding of `x` to the source
encoding of `f x`, and `c_proj` undoes the new input encoding on the codes actually used
(`hretr` — the retraction identity), then the conjugate takes the *new* encoding of `x` to the new
encoding of `f x`.

`r` needs no fragment hypothesis: its behaviour enters already as an `eval` equation. The two
re-encoding codes do, since the retraction identity is stated in the total value model `val`, and
`eval_eq_val` is the bridge. -/
theorem eval_transport {c_emb c_proj r : Code} {α β : Type*} {encA encA' : α → ℕ} {encB : β → ℕ}
    {f : α → β} (hemb : RfindFree c_emb) (hproj : RfindFree c_proj)
    (hretr : ∀ x, val c_proj (encA' x) = encA x)
    (hr : ∀ x, eval r (encA x) = Part.some (encB (f x))) (x : α) :
    eval (transport c_emb c_proj r) (encA' x) = Part.some (val c_emb (encB (f x))) := by
  have hcomp : ∀ (a b : Code) (n : ℕ), eval (comp a b) n = (eval b n).bind fun u => eval a u :=
    fun _ _ _ => rfl
  rw [transport, hcomp, hcomp, eval_eq_val hproj (encA' x), Part.bind_some, hretr x, hr x,
    Part.bind_some, eval_eq_val hemb (encB (f x))]

/-- **Re-encoding an assembly along a code**: the same finite carrier, each element now written as
the value `c` computes from its old code. Injectivity of the new encoding is the hypothesis — it is
what keeps the result an assembly, and it is exactly what a retraction pair supplies. -/
def reencode (A : Assembly) (c : Code) (hinj : Function.Injective fun x => val c (A.enc x)) :
    Assembly where
  carrier := A.carrier
  enc := fun x => val c (A.enc x)
  enc_inj := hinj

/-- **Realization is preserved by transport.** A function realized between two assemblies is still
realized between their re-encodings, by the conjugate code — given the retraction identity on the
input side. This is the functor's action on morphisms at fixed algebra: the *same* function, the
*same* carriers, a new pair of conventions and a new realizer for them.

Note the asymmetry the two sides play. The input side needs a genuine retraction (`hretr`): the
conjugate has to recover the old code of `x` before `r` can be run on it. The output side needs only
a coded map — `c_emb` is applied to `r`'s result and nothing has to be undone. -/
theorem realizes_transport {A B : Assembly} {f : A.carrier → B.carrier}
    {c_embA c_emb c_proj r : Code} (hemb : RfindFree c_emb) (hproj : RfindFree c_proj)
    (hinjA : Function.Injective fun x => val c_embA (A.enc x))
    (hinjB : Function.Injective fun y => val c_emb (B.enc y))
    (hretr : ∀ x, val c_proj (val c_embA (A.enc x)) = A.enc x)
    (hr : ∀ x, eval r (A.enc x) = Part.some (B.enc (f x))) :
    Realizes (A := reencode A c_embA hinjA) (B := reencode B c_emb hinjB) f :=
  ⟨transport c_emb c_proj r,
    eval_transport (encA := A.enc) (encA' := fun x => val c_embA (A.enc x))
      (encB := B.enc) hemb hproj hretr hr⟩

/-! ## The workspace currency: grades MAX -/

/-- **Capacity-bounded transport ([Decoupling] §4.5).** If the input re-encoder runs within `b` bits
on the argument, the realizer runs within `g` bits on every value the re-encoder can hand it, and
the output re-encoder runs within `b` bits on every value the realizer can produce, then the whole
conjugation runs within `max g b`. Grades do not accumulate along a conjugation.

Two features of the bound are worth stating. The `max` is the composition law of the workspace
family — the parts share one workspace rather than each needing its own. And no constant appears:
the family charges a factor `2` for *pairing*, and a conjugation forms no pairs.

The hypotheses are conditioned rather than uniform, as every workspace hypothesis must be — a leaf
node holds its input, so no constant bounds the workspace of a code over all inputs. Each condition
is stated at exactly the values that code actually meets: `c_proj` at the argument, `r` at the
re-encoder's outputs (`≤ b` bits), `c_emb` at the realizer's outputs (`≤ g` bits). -/
theorem spaceCost_transport_le {c_emb c_proj r : Code} {n b g : ℕ}
    (hr : RfindFree r) (hproj : RfindFree c_proj)
    (hprojn : spaceCost c_proj n ≤ b)
    (hrun : ∀ v, Nat.size v ≤ b → spaceCost r v ≤ g)
    (hembn : ∀ v, Nat.size v ≤ g → spaceCost c_emb v ≤ b) :
    spaceCost (transport c_emb c_proj r) n ≤ max g b := by
  -- the inner conjugate `comp r c_proj` is the composition law of the family, at `max b g`
  have hinner : spaceCost (comp r c_proj) n ≤ max b g :=
    spaceCost_comp_le hproj hprojn hrun
  -- the value it produces is within grade `g`: the argument reaches `r` within `b` bits
  have hmid : Nat.size (val (comp r c_proj) n) ≤ g := by
    rw [val_comp]
    exact le_trans (size_val_le_spaceCost hr (val c_proj n))
      (hrun (val c_proj n) (le_trans (size_val_le_spaceCost hproj n) hprojn))
  rw [transport, spaceCost_comp]
  refine max_le (le_trans hinner (le_of_eq (max_comm b g))) ?_
  exact le_trans (hembn _ hmid) (le_max_right g b)

/-! ## The description-length currency: grades ADD -/

/-- **The length of a transport is exact, and additive.** The serialization's `comp` law charges
three bits of structure per node, and a conjugation has two nodes — so the conjugate's length is the
sum of the three parts' lengths plus six, with no slack and no inequality.

Set beside `spaceCost_transport_le`, this is the module's point: the same syntactic operation is
priced by a *sum* in description length and by a *maximum* in workspace. The two currencies of a
capacity grade do not obey the same algebra, and a graded semantics over this carrier has to carry
both. -/
theorem elen_transport (c_emb c_proj r : Code) :
    elen (transport c_emb c_proj r) = elen c_emb + elen r + elen c_proj + 6 := by
  rw [transport, E_len_comp, E_len_comp]
  omega

end GradeTransport
