/-
Copyright (c) 2026 Mykola Palamarchuk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mykola Palamarchuk
-/
import ALT.GradeTransport
import ALT.GradedApplication

-- Formal-check file, not Mathlib-destined: opt out of the house-style header linter.
set_option linter.style.header false

/-!
# Transport at grade: conjugating a graded realizer between re-encodings ([Decoupling] §4.5)

Conjecture 4.4's load-bearing step asks a capacity-respecting simulation to *transport a realizer
without overflowing the budget*. `ALT/GradeTransport.lean` priced the conjugation on a single
injective encoding (an `Assembly`); this module runs the same transport one level up, on the
**many-realizers** assemblies (`Asm`) over which the graded exponential `[A ⇒ B]_g` is built, and
reads the price off as a grade.

## What is transported
`reencodeAsm A c` re-encodes an assembly: an element keeps its identity, but a realizer index `m` of
it is carried to `val c m`, the value the code `c` computes on `m`. This is the **direct-image**
realizability relation (`∃ m, A.realizes m a ∧ n = val c m`); unlike the `Assembly`-level
`GradeTransport.reencode`, it asks for **no injectivity** of the new naming, because a
many-realizers assembly already tolerates many names per element.

`transportIdx c_emb c_proj r` transports a realizer *index*: decode `r` to a code, conjugate it with
the coded retraction pair `(c_emb, c_proj)` (`GradeTransport.transport`), re-encode the result. Its
tracking law (`tracks_transportIdx`) and its grade law (`grade_transportIdx_le`) are the two halves;
`gradedTransport` packages them, carrying an element of `[A ⇒ B]_g` to an element of
`[reencodeAsm A c_embA ⇒ reencodeAsm B c_emb]_{4·max g b + 9}`.

The **pullback** direction (`pullbackAsm`, `tracks_pullback`, `gradedPullback`) is the mirror: a new
index realizes an element when *reading it back* lands on an old realizer, and the same conjugation
transports the tracker with the reading in the source slot. It reuses the identical index arithmetic
(`grade_transportIdx_le`), so the grade law is unchanged — only the retraction's side flips, from
input to output.

## The retraction, and its asymmetry
`tracks_transportIdx` inherits the asymmetry of the `Assembly`-level
`GradeTransport.realizes_transport` (cross-referenced for orientation, not consumed here — the two
live over different assembly notions). The input side needs a genuine retraction (`hretr`: `c_proj`
undoes `c_embA` on the realizer indices actually in use), because the conjugate must recover the old
index before the realizer can run on it; the output side needs only a coded map `c_emb`, applied to
the result with nothing to undo. The realizer `r` itself needs neither a fragment hypothesis nor
totality — its behaviour enters only as the membership `k ∈ ap r m`. The retraction is conditioned
over the indices in use, as every realizer hypothesis in this development is, never over all of ℕ.

## The price
`grade_transportIdx_le` is the §4.5 transport clause at grade: the index length of the conjugate is
at most `4 · max g b + 9`, where `g` bounds the realizer's grade and `b` the re-encoders'. It is the
one-hop max-affine law of `GradeTransport.bitlen_transport_le` read through the `Code ≃ ℕ` numbering
(`grade_encode`, `bitlen_ofNat`). The semantic conjunct needs no separate statement: it is exactly
`gradedExp`'s tracking clause, holding on the transported element by `tracks_transportIdx`.

## Deliberately absent
One partial combinatory algebra (Kleene's first, on `Nat.Partrec.Code`), one hop. Nothing here
iterates the transport or claims a functor: the leading factor of the max-affine law compounds once
per hop (the `×4` is `2²`, for the two nested `comp` nodes), so an iterated transport grows the
index budget geometrically — the one-hop law is a theorem while the full functor of Conjecture 4.4
stays open. The packaging map `gradedTransport` is a function on carriers; it is **not** itself
claimed trackable — conjugation-as-code, the functor's action on realizers, is the boundary this
module stops at. No tightness is claimed for the constant `4 · max g b + 9`, and no host-side
assembly map is built (the assembly induced by a hosting square is a separate construction).
-/

namespace GradedConjugation

open Nat.Partrec (Code)
open Nat.Partrec.Code
open RealizabilityCCC GradedApplication TimeCost

/-! ## Re-encoding a many-realizers assembly, and transporting an index -/

/-- **Re-encoding an `Asm` along a code.** The carrier is unchanged; a realizer index `m` of an
element is carried to `val c m`. The relation is the **direct image** of `A`'s under `val c`, so it
needs no injectivity — a many-realizers assembly already names each element by many codes. -/
def reencodeAsm (A : Asm) (c : Code) : Asm where
  carrier := A.carrier
  realizes n a := ∃ m, A.realizes m a ∧ n = val c m
  realized a := by
    obtain ⟨m, hm⟩ := A.realized a
    exact ⟨val c m, m, hm, rfl⟩

/-- **Transporting a realizer index.** Decode the index `r` to a code, conjugate it with the coded
retraction pair `(c_emb, c_proj)` (`GradeTransport.transport`), and re-encode the conjugate. This is
the action `transportIdx` a capacity-respecting simulation has on realizer indices. -/
def transportIdx (c_emb c_proj : Code) (r : ℕ) : ℕ :=
  Encodable.encode (GradeTransport.transport c_emb c_proj (Denumerable.ofNat Code r))

/-! ## The tracking law transports -/

/-- **The tracking condition transports along a re-encoding.** If `r` tracks `f : A ⟶ B` and
`(c_embA, c_proj)` is a retraction pair on the indices `A` actually uses (`hretr`), then the
transported index `transportIdx c_emb c_proj r` tracks the *same* function `f` between the
re-encodings `reencodeAsm A c_embA` and `reencodeAsm B c_emb`.

The realizer `r` enters only through the membership `k ∈ ap r m`, so it needs neither an
`rfind`-free fragment nor totality; the two re-encoding codes `c_proj`/`c_emb` are run, so they are
`RfindFree`. The
input side undoes `c_embA` with `c_proj`; the output side only applies `c_emb`. -/
theorem tracks_transportIdx {A B : Asm} {f : A.carrier → B.carrier}
    {c_embA c_emb c_proj : Code} {r : ℕ}
    (hemb : RfindFree c_emb) (hproj : RfindFree c_proj)
    (hretr : ∀ (a : A.carrier) (m : ℕ), A.realizes m a → val c_proj (val c_embA m) = m)
    (hr : Tracks A B r f) :
    Tracks (reencodeAsm A c_embA) (reencodeAsm B c_emb) (transportIdx c_emb c_proj r) f := by
  intro x n hn
  obtain ⟨m, hm, hnm⟩ := hn
  subst hnm
  obtain ⟨k, hk, hBk⟩ := hr x m hm
  refine ⟨val c_emb k, ?_, ⟨k, hBk, rfl⟩⟩
  have hdecode : ap (transportIdx c_emb c_proj r) (val c_embA m)
      = eval (comp c_emb (comp (Denumerable.ofNat Code r) c_proj)) (val c_embA m) := by
    simp only [ap, transportIdx, Denumerable.ofNat_encode, GradeTransport.transport]
  rw [hdecode]
  have hcomp : ∀ (a b : Code) (t : ℕ), eval (comp a b) t = (eval b t).bind fun u => eval a u :=
    fun _ _ _ => rfl
  rw [hcomp, hcomp]
  have hmem_proj : m ∈ eval c_proj (val c_embA m) := by
    rw [eval_eq_val hproj, hretr x m hm]; exact Part.mem_some m
  have hmem_emb : val c_emb k ∈ eval c_emb k := by
    rw [eval_eq_val hemb]; exact Part.mem_some _
  exact Part.mem_bind (Part.mem_bind hmem_proj hk) hmem_emb

/-! ## The grade law, and the packaged transport -/

/-- **The transported index stays within the max-affine budget ([Decoupling] §4.5).** If the two
re-encoders have index length at most `b` and the realizer has grade at most `g`, the transported
index has grade at most `4 · max g b + 9`. This is `GradeTransport.bitlen_transport_le` read through
the `Code ≃ ℕ` numbering (`grade_encode`, `bitlen_ofNat`): the counting-bound realizer length and
the exponential's grade are one quantity. -/
theorem grade_transportIdx_le {c_emb c_proj : Code} {r b g : ℕ}
    (hemb : Realizability.bitlen c_emb ≤ b) (hproj : Realizability.bitlen c_proj ≤ b)
    (hg : grade r ≤ g) :
    grade (transportIdx c_emb c_proj r) ≤ 4 * max g b + 9 := by
  have hbr : Realizability.bitlen (Denumerable.ofNat Code r) ≤ g := by
    rw [bitlen_ofNat]; exact hg
  have hkey : grade (transportIdx c_emb c_proj r)
      = Realizability.bitlen (GradeTransport.transport c_emb c_proj (Denumerable.ofNat Code r)) :=
    grade_encode _
  rw [hkey]
  exact GradeTransport.bitlen_transport_le hemb hproj hbr

/-- **The transport clause of Conjecture 4.4, at grade.** A capacity-respecting re-encoding takes a
morphism affordable at grade `g` — an element of the graded exponential `[A ⇒ B]_g` — to a morphism
of the re-encoded assemblies affordable at grade `4 · max g b + 9`, where `b` bounds the two
re-encoders' index lengths. The underlying function is unchanged (`gradedTransport_fn`); the new
realizer is the conjugated index, whose grade the max-affine one-hop law bounds
(`grade_transportIdx_le`) and whose tracking `tracks_transportIdx` supplies. The budget of a
capacity-respecting transport does not overflow — it grows by one max-affine hop. -/
noncomputable def gradedTransport {A B : Asm} {b g : ℕ} {c_embA c_emb c_proj : Code}
    (hemb : RfindFree c_emb) (hproj : RfindFree c_proj)
    (hbe : Realizability.bitlen c_emb ≤ b) (hbp : Realizability.bitlen c_proj ≤ b)
    (hretr : ∀ (a : A.carrier) (m : ℕ), A.realizes m a → val c_proj (val c_embA m) = m)
    (f : (gradedExp g A B).carrier) :
    (gradedExp (4 * max g b + 9) (reencodeAsm A c_embA) (reencodeAsm B c_emb)).carrier :=
  ⟨⟨f.1.1, transportIdx c_emb c_proj f.2.choose,
      tracks_transportIdx hemb hproj hretr f.2.choose_spec.2⟩,
    transportIdx c_emb c_proj f.2.choose,
    grade_transportIdx_le hbe hbp f.2.choose_spec.1,
    tracks_transportIdx hemb hproj hretr f.2.choose_spec.2⟩

/-- **The transport leaves the underlying function untouched.** `gradedTransport` re-encodes
realizers, not elements; the morphism it produces computes the same map on carriers as its input. -/
theorem gradedTransport_fn {A B : Asm} {b g : ℕ} {c_embA c_emb c_proj : Code}
    (hemb : RfindFree c_emb) (hproj : RfindFree c_proj)
    (hbe : Realizability.bitlen c_emb ≤ b) (hbp : Realizability.bitlen c_proj ≤ b)
    (hretr : ∀ (a : A.carrier) (m : ℕ), A.realizes m a → val c_proj (val c_embA m) = m)
    (f : (gradedExp g A B).carrier) :
    fn (gradedTransport hemb hproj hbe hbp hretr f) = fn f := rfl

/-! ## The pullback direction: re-encoding by reading, and its inverted asymmetry -/

/-- **Pulling an `Asm` back along a reading.** The carrier is unchanged; a new index `n` realizes an
element exactly when *reading it back* with `c_read` lands on an old realizer — `A.realizes
(val c_read n) a`. Where `reencodeAsm` pushes realizers forward through a code, this pulls them
back: the reading `c_read` is applied to the *candidate* index. The section `c_sect` (with the
retraction `hsect`) supplies a witness index, so the object stays inhabited by realizers. -/
def pullbackAsm (A : Asm) (c_read c_sect : Code)
    (hsect : ∀ (a : A.carrier) (m : ℕ), A.realizes m a → val c_read (val c_sect m) = m) : Asm where
  carrier := A.carrier
  realizes n a := A.realizes (val c_read n) a
  realized a := by
    obtain ⟨m, hm⟩ := A.realized a
    exact ⟨val c_sect m, by rw [hsect a m hm]; exact hm⟩

/-- **Tracking transports along a pullback — the mirror of `tracks_transportIdx`.** The transported
index is the *same* conjugation, but with the reading in the source slot: `transportIdx c_sect
c_read` runs `c_read` first, then the realizer, then `c_sect`.

The asymmetry inverts. In the pushforward the retraction sat on the **input** — the conjugate had to
recover the old index before running. Here the input is free: the pullback hands the guest index to
`c_read` directly, and the realizer runs on `val c_read n`. The genuine retraction is on the
**output** (`hsB`, over `B`'s realizers in use): the result is re-encoded by `c_sect` and `c_read`
must read it back. `hsA` does no tracking work at all — it only builds the domain object. This is a
sibling proof, not an instance of `tracks_transportIdx`. -/
theorem tracks_pullback {A B : Asm} {f : A.carrier → B.carrier} {c_read c_sect : Code} {r : ℕ}
    (hread : RfindFree c_read) (hsectRF : RfindFree c_sect)
    (hsA : ∀ (a : A.carrier) (m : ℕ), A.realizes m a → val c_read (val c_sect m) = m)
    (hsB : ∀ (b' : B.carrier) (m : ℕ), B.realizes m b' → val c_read (val c_sect m) = m)
    (hr : Tracks A B r f) :
    Tracks (pullbackAsm A c_read c_sect hsA) (pullbackAsm B c_read c_sect hsB)
      (transportIdx c_sect c_read r) f := by
  intro x n hn
  -- hn : A.realizes (val c_read n) x
  obtain ⟨k, hk, hBk⟩ := hr x (val c_read n) hn
  refine ⟨val c_sect k, ?_, ?_⟩
  · have hdecode : ap (transportIdx c_sect c_read r) n
        = eval (comp c_sect (comp (Denumerable.ofNat Code r) c_read)) n := by
      simp only [ap, transportIdx, Denumerable.ofNat_encode, GradeTransport.transport]
    rw [hdecode]
    have hcomp : ∀ (a b : Code) (t : ℕ), eval (comp a b) t = (eval b t).bind fun u => eval a u :=
      fun _ _ _ => rfl
    rw [hcomp, hcomp]
    have hmem_read : val c_read n ∈ eval c_read n := by
      rw [eval_eq_val hread]; exact Part.mem_some _
    have hmem_sect : val c_sect k ∈ eval c_sect k := by
      rw [eval_eq_val hsectRF]; exact Part.mem_some _
    exact Part.mem_bind (Part.mem_bind hmem_read hk) hmem_sect
  · change B.realizes (val c_read (val c_sect k)) (f x)
    rw [hsB (f x) k hBk]; exact hBk

/-- **The pullback clause of Conjecture 4.4, at grade.** The host-side counterpart of
`gradedTransport`: a morphism affordable at grade `g` between guest assemblies is carried to a
morphism affordable at grade `4 · max g b + 9` between their pullbacks along a reading pair of index
length at most `b`. The grade law is `grade_transportIdx_le` at `(c_sect, c_read)` — the same
max-affine index arithmetic; only the conjugation's argument order differs. -/
noncomputable def gradedPullback {A B : Asm} {b g : ℕ} {c_read c_sect : Code}
    (hread : RfindFree c_read) (hsectRF : RfindFree c_sect)
    (hbr : Realizability.bitlen c_read ≤ b) (hbs : Realizability.bitlen c_sect ≤ b)
    (hsA : ∀ (a : A.carrier) (m : ℕ), A.realizes m a → val c_read (val c_sect m) = m)
    (hsB : ∀ (b' : B.carrier) (m : ℕ), B.realizes m b' → val c_read (val c_sect m) = m)
    (f : (gradedExp g A B).carrier) :
    (gradedExp (4 * max g b + 9) (pullbackAsm A c_read c_sect hsA)
      (pullbackAsm B c_read c_sect hsB)).carrier :=
  ⟨⟨f.1.1, transportIdx c_sect c_read f.2.choose,
      tracks_pullback hread hsectRF hsA hsB f.2.choose_spec.2⟩,
    transportIdx c_sect c_read f.2.choose,
    grade_transportIdx_le hbs hbr f.2.choose_spec.1,
    tracks_pullback hread hsectRF hsA hsB f.2.choose_spec.2⟩

/-- **The pullback leaves the underlying function untouched**, exactly as the pushforward does. -/
theorem gradedPullback_fn {A B : Asm} {b g : ℕ} {c_read c_sect : Code}
    (hread : RfindFree c_read) (hsectRF : RfindFree c_sect)
    (hbr : Realizability.bitlen c_read ≤ b) (hbs : Realizability.bitlen c_sect ≤ b)
    (hsA : ∀ (a : A.carrier) (m : ℕ), A.realizes m a → val c_read (val c_sect m) = m)
    (hsB : ∀ (b' : B.carrier) (m : ℕ), B.realizes m b' → val c_read (val c_sect m) = m)
    (f : (gradedExp g A B).carrier) :
    fn (gradedPullback hread hsectRF hbr hbs hsA hsB f) = fn f := rfl

end GradedConjugation
