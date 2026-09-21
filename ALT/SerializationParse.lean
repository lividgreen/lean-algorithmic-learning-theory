/-
Copyright (c) 2026 Mykola Palamarchuk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mykola Palamarchuk
-/
module

public import ALT.ChaitinPrefix

-- Formal-check file, not Mathlib-destined: opt out of the house-style header linter.
set_option linter.style.header false

/-!
# A computable, self-delimiting parser for `E` ([Decoupling] §6.6)

Provenance: [Decoupling] §6.6, over `AdditiveComplexity.E`, the prefix (Polish-form) AST
serialization of `ALT/AdditiveComplexity.lean`. `E` is a prefix code by construction
(`E_append_inj`); this module exhibits the computable decoder that recovers a serialized
program and its trailing bits from any description, discharging `KolmogorovComplexity.EParserSpec`.

## What this establishes
* `parseE`, `primrec_parseE`: a total, `Primrec` parser `List Bool → Option (Code × List Bool)`.
* `parseE_E_append`: `parseE` recovers exactly `(e, r)` from any `E e ++ r`.
* `parseE_eq_some`: the domain characterization — a successful parse consumed exactly a
  serialization, `parseE w = some (e, r) → w = E e ++ r`.
* `eParserSpec`: the packaged witness of `KolmogorovComplexity.EParserSpec`.

## What this does NOT establish (flagged)
* `KolmogorovComplexity.REPred kleB`, the sibling leaf hypothesis of `EParserSpec`, and the
  theory-level assembly consuming both — left to a companion module.
-/


@[expose] public section

namespace AdditiveComplexity

open Nat.Partrec Nat.Partrec.Code KolmogorovComplexity

/-! ## The parser: a nested fold over an explicit stack of open frames -/

/-- The 3-bit opcode of an `E`-node, in the same order `E` itself matches on. -/
abbrev Tag := Bool × Bool × Bool

/-- An open frame on the parse stack: a node's opcode together with the children parsed for it
so far, in the order they were parsed. -/
abbrev Frame := Tag × List Code

/-- The number of children a tag's node takes: `0` for the four leaves, `2` for `pair`/`comp`/
`prec`, `1` for `rfind'` — read off `E`'s own case split. -/
def opArity (t : Tag) : ℕ :=
  bif t.1 then (bif (t.2.1 && t.2.2) then 1 else 2) else 0

/-- Builds the `Code` a completed tag denotes from its (already-parsed) children, taken in the
order collected. Only ever applied where `cs.length = opArity t` (`opArity_buildOp_eq_E`
records what this produces there); off that domain `cs.headI`/`cs.tail.headI` pad with a junk
default and the result carries no meaning. -/
def buildOp (t : Tag) (cs : List Code) : Code :=
  let c0 := cs.headI
  let c1 := cs.tail.headI
  bif t.1 then
    (bif t.2.1 then (bif t.2.2 then Code.rfind' c0 else Code.prec c0 c1)
     else (bif t.2.2 then Code.comp c0 c1 else Code.pair c0 c1))
  else
    (bif t.2.1 then (bif t.2.2 then Code.right else Code.left)
     else (bif t.2.2 then Code.succ else Code.zero))

/-- One step of absorbing a newly-completed child `c` into the innermost open frame: if it
completes that frame, the built code becomes the next child to absorb into the frame below
(cascading); otherwise absorption stops there, and every frame from that point on (the state's
first component turns `false`) passes through unchanged. -/
def absorbStep (st : Bool × Code × List Frame) (fr : Frame) : Bool × Code × List Frame :=
  bif st.1 then
    let cs' := fr.2 ++ [st.2.1]
    bif decide (cs'.length = opArity fr.1) then
      (true, buildOp fr.1 cs', st.2.2)
    else
      (false, st.2.1, st.2.2 ++ [(fr.1, cs')])
  else
    (false, st.2.1, st.2.2 ++ [fr])

/-- Absorbs a newly-completed code `c0` into a parse stack, cascading as far as it goes: `true`
with the completed top-level code if the whole stack collapses, `false` with the resulting
(shorter or equal-length) stack otherwise. -/
def absorbFold (stack : List Frame) (c0 : Code) : Bool × Code × List Frame :=
  stack.foldl absorbStep (true, c0, [])

/-- The parser's running state: the partial (0/1/2-bit) tag being read, the stack of open
frames (innermost first), and, once a top-level code has been read off, its slot together with
every bit seen since. -/
abbrev PState := List Bool × List Frame × Option (Code × List Bool)

/-- One bit's transition: if the slot is already filled, the bit is just appended to the
trailing remainder; otherwise it extends the partial tag, and a completed 3-bit tag either
opens a new frame (arity > 0) or is immediately absorbed (arity 0, a leaf). -/
def bitStep (st : PState) (b : Bool) : PState :=
  match st.2.2 with
  | some (c, tr) => (st.1, st.2.1, some (c, tr ++ [b]))
  | Option.none =>
      let tag' := st.1 ++ [b]
      bif decide (tag'.length < 3) then
        (tag', st.2.1, Option.none)
      else
        let t : Tag := (tag'.headI, tag'.tail.headI, tag'.tail.tail.headI)
        bif decide (opArity t = 0) then
          let (absorbing, c, newStack) := absorbFold st.2.1 (buildOp t [])
          bif absorbing then ([], [], some (c, [])) else ([], newStack, Option.none)
        else
          ([], (t, []) :: st.2.1, Option.none)

/-- Folds `bitStep` over a bit-list from the fresh state. -/
def parseFold (w : List Bool) : PState := w.foldl bitStep ([], [], Option.none)

/-- **The parser.** Total; `primrec_parseE` below is its computability, `parseE_E_append` and
`parseE_eq_some` its correctness. -/
def parseE (w : List Bool) : Option (Code × List Bool) := (parseFold w).2.2

/-! ## Bit-level identities -/

/-- The bits an open frame accounts for so far: its own opcode, then its collected children's
own serializations, in order. -/
private def frameBits (fr : Frame) : List Bool :=
  (fr.1.1 :: fr.1.2.1 :: fr.1.2.2 :: []) ++ (fr.2.map E).flatten

/-- The bits a whole parse stack accounts for so far, outermost frame first (the order the
bits were actually read in): the tail of the (innermost-first) stack contributes its own bits
before the head's. -/
private def stackBits : List Frame → List Bool
  | [] => []
  | fr :: rest => stackBits rest ++ frameBits fr

/-- A frame's children never exceed its own arity: the parser only ever holds frames genuinely
still open. Threaded through `absorbFold`'s and the main invariant's inductions. -/
private def OpenFrame (fr : Frame) : Prop := fr.2.length < opArity fr.1

private theorem stackBits_cons (fr : Frame) (rest : List Frame) :
    stackBits (fr :: rest) = stackBits rest ++ frameBits fr := rfl

/-- Extending a frame's collected children by one extends its `frameBits` by that child's own
serialization. -/
private theorem frameBits_snoc (t : Tag) (cs : List Code) (c : Code) :
    frameBits (t, cs ++ [c]) = frameBits (t, cs) ++ E c := by
  simp [frameBits]

/-- **`buildOp` inverts `E`-concatenation.** At a children list of exactly the tag's own arity,
the opcode bits followed by the children's own serializations, concatenated, is exactly the
serialization of the code `buildOp` builds from them. The content of `E`'s eight cases, read
in the direction a parser needs. -/
private theorem opArity_buildOp_eq_E (t : Tag) (cs : List Code) (h : cs.length = opArity t) :
    (t.1 :: t.2.1 :: t.2.2 :: []) ++ (cs.map E).flatten = E (buildOp t cs) := by
  obtain ⟨b0, b1, b2⟩ := t
  cases b0 <;> cases b1 <;> cases b2 <;>
    simp only [opArity, Bool.cond_true, Bool.cond_false] at h <;>
    rcases cs with _ | ⟨c0, _ | ⟨c1, _ | ⟨c2, cs⟩⟩⟩ <;> simp_all [buildOp, E]

/-- Restated with `frameBits`, at a frame just reaching its own arity: `frameBits` collapses to
the serialization of the built code. -/
private theorem frameBits_eq_E_of_arity (t : Tag) (cs : List Code) (h : cs.length = opArity t) :
    frameBits (t, cs) = E (buildOp t cs) :=
  opArity_buildOp_eq_E t cs h

/-! ## `absorbFold`: reconstruction -/

/-- **Folding `absorbStep` once absorption has stopped is a plain append.** Every remaining
frame passes through unchanged, in order. -/
private theorem absorbFold_not_absorbing (rest : List Frame) :
    ∀ (c : Code) (ds : List Frame),
      rest.foldl absorbStep (false, c, ds) = (false, c, ds ++ rest) := by
  induction rest with
  | nil => intro c ds; simp
  | cons fr rest ih =>
      intro c ds
      change rest.foldl absorbStep (absorbStep (false, c, ds) fr) = _
      simp only [absorbStep, Bool.cond_false]
      rw [ih]
      simp

/-- **Absorption reconstruction.** Absorbing `c0` into `stack` (every frame of which is
genuinely open) either collapses the whole stack — and then the stack's own accounted bits,
followed by `c0`'s serialization, is exactly the serialization of the fully-built code — or
stops partway, leaving a shorter open stack accounting for exactly the same bits. -/
private theorem absorbFold_spec (stack : List Frame) (hopen : ∀ fr ∈ stack, OpenFrame fr)
    (c0 : Code) :
    ((absorbFold stack c0).1 = true →
        stackBits stack ++ E c0 = E (absorbFold stack c0).2.1)
    ∧ ((absorbFold stack c0).1 = false →
        stackBits stack ++ E c0 = stackBits (absorbFold stack c0).2.2
        ∧ ∀ fr ∈ (absorbFold stack c0).2.2, OpenFrame fr) := by
  induction stack generalizing c0 with
  | nil =>
      refine ⟨fun _ => by simp [absorbFold, stackBits], fun h => by simp [absorbFold] at h⟩
  | cons fr rest ih =>
      have hfr : fr.2.length < opArity fr.1 := hopen fr List.mem_cons_self
      have hrest : ∀ fr' ∈ rest, OpenFrame fr' :=
        fun fr' hm => hopen fr' (List.mem_cons_of_mem _ hm)
      have hstep : absorbFold (fr :: rest) c0
          = rest.foldl absorbStep (absorbStep (true, c0, []) fr) := rfl
      have hlen_eq : (fr.2 ++ [c0]).length = fr.2.length + 1 := by simp
      by_cases hlen : fr.2.length + 1 = opArity fr.1
      · have hstepEq : absorbStep (true, c0, []) fr = (true, buildOp fr.1 (fr.2 ++ [c0]), []) := by
          simp [absorbStep, hlen_eq, hlen]
        rw [hstep, hstepEq]
        have hrecon : stackBits (fr :: rest) ++ E c0
            = stackBits rest ++ E (buildOp fr.1 (fr.2 ++ [c0])) := by
          rw [stackBits_cons, List.append_assoc, ← frameBits_snoc,
            frameBits_eq_E_of_arity fr.1 (fr.2 ++ [c0]) (by rw [hlen_eq]; exact hlen)]
        obtain ⟨ihT, ihF⟩ := ih hrest (buildOp fr.1 (fr.2 ++ [c0]))
        refine ⟨fun h => ?_, fun h => ?_⟩
        · rw [hrecon]; exact ihT h
        · rw [hrecon]; exact ihF h
      · have hstepEq : absorbStep (true, c0, []) fr = (false, c0, [(fr.1, fr.2 ++ [c0])]) := by
          simp [absorbStep, hlen_eq, hlen]
        rw [hstep, hstepEq, absorbFold_not_absorbing]
        refine ⟨fun h => by simp at h, fun _ => ?_⟩
        have hrecon : stackBits (fr :: rest) ++ E c0
            = stackBits rest ++ frameBits (fr.1, fr.2 ++ [c0]) := by
          rw [stackBits_cons, List.append_assoc, ← frameBits_snoc]
        refine ⟨?_, ?_⟩
        · rw [hrecon]
          exact (stackBits_cons (fr.1, fr.2 ++ [c0]) rest).symm
        · intro fr' hm
          simp only [List.mem_append, List.mem_singleton] at hm
          rcases hm with h1 | h2
          · subst h1
            change (fr.2 ++ [c0]).length < opArity fr.1
            rw [hlen_eq]; omega
          · exact hrest fr' h2

/-! ## The main forward invariant, and `parseE_eq_some` -/

/-- **The parse invariant.** Folding `bitStep` over any prefix of bits from the fresh state
either lands with the slot empty — the partial tag short, the open stack accounting for exactly
the bits read — or with the slot filled by exactly the code and trailing bits those bits
serialize. -/
private theorem parseFold_spec (p : List Bool) :
    ((parseFold p).2.2 = Option.none →
        stackBits (parseFold p).2.1 ++ (parseFold p).1 = p
        ∧ (parseFold p).1.length ≤ 2
        ∧ ∀ fr ∈ (parseFold p).2.1, OpenFrame fr)
    ∧ (∀ e r, (parseFold p).2.2 = some (e, r) → p = E e ++ r) := by
  induction p using List.reverseRecOn with
  | nil => refine ⟨fun _ => by simp [parseFold, stackBits], fun e r he => by simp [parseFold] at he⟩
  | append_singleton p b ih =>
      have hfold : parseFold (p ++ [b]) = bitStep (parseFold p) b := by
        change (p ++ [b]).foldl bitStep ([], [], Option.none) = _
        rw [List.foldl_append]
        rfl
      rcases hnone : (parseFold p).2.2 with _ | ⟨e, r⟩
      · obtain ⟨hrecon, htaglen, hopen⟩ := ih.1 hnone
        have hlen_app : ((parseFold p).1 ++ [b]).length = (parseFold p).1.length + 1 := by simp
        have hpeq : parseFold p = ((parseFold p).1, (parseFold p).2.1, Option.none) := by
          rw [← hnone]
        -- `bitStep`'s definition, restated with NO opaque internal `let`s: a `rfl`-check (kernel
        -- defeq sees through them) against a term spelled out with the caller's own names, so
        -- every later `simp`/`rw` on it matches syntactically instead of missing through them.
        have hbv0 : bitStep (parseFold p) b =
            bif decide (((parseFold p).1 ++ [b]).length < 3) then
              ((parseFold p).1 ++ [b], (parseFold p).2.1, Option.none)
            else
              bif decide (opArity (((parseFold p).1 ++ [b]).headI,
                  ((parseFold p).1 ++ [b]).tail.headI,
                  ((parseFold p).1 ++ [b]).tail.tail.headI) = 0) then
                (let (absorbing, c, newStack) := absorbFold (parseFold p).2.1
                    (buildOp (((parseFold p).1 ++ [b]).headI, ((parseFold p).1 ++ [b]).tail.headI,
                      ((parseFold p).1 ++ [b]).tail.tail.headI) [])
                 bif absorbing then ([], [], some (c, [])) else ([], newStack, Option.none))
              else
                ([], ((((parseFold p).1 ++ [b]).headI, ((parseFold p).1 ++ [b]).tail.headI,
                    ((parseFold p).1 ++ [b]).tail.tail.headI), []) :: (parseFold p).2.1,
                  Option.none) := by
          rw [hpeq]; rfl
        by_cases hlt : (parseFold p).1.length + 1 < 3
        · have hbv : bitStep (parseFold p) b
              = ((parseFold p).1 ++ [b], (parseFold p).2.1, Option.none) := by
            rw [hbv0]; simp [hlt]
          refine ⟨fun hslot2 => ?_, fun e r he => ?_⟩
          · rw [hfold, hbv] at hslot2 ⊢
            refine ⟨?_, by change ((parseFold p).1 ++ [b]).length ≤ 2; omega, hopen⟩
            rw [← List.append_assoc, hrecon]
          · rw [hfold, hbv] at he
            simp at he
        · have hlen3 : ((parseFold p).1 ++ [b]).length = 3 := by omega
          have htag_eq : (parseFold p).1 ++ [b]
              = [((parseFold p).1 ++ [b]).headI, ((parseFold p).1 ++ [b]).tail.headI,
                  ((parseFold p).1 ++ [b]).tail.tail.headI] := by
            match hh : (parseFold p).1 ++ [b], hlen3 with
            | [x, y, z], _ => rfl
          set t : Tag := (((parseFold p).1 ++ [b]).headI, ((parseFold p).1 ++ [b]).tail.headI,
            ((parseFold p).1 ++ [b]).tail.tail.headI) with ht
          have hrec2 : p ++ [b] = stackBits (parseFold p).2.1 ++ (t.1 :: t.2.1 :: t.2.2 :: []) := by
            have hteq2 : (t.1 :: t.2.1 :: t.2.2 :: ([] : List Bool)) = (parseFold p).1 ++ [b] :=
              htag_eq.symm
            rw [hteq2, ← List.append_assoc, hrecon]
          by_cases harity : opArity t = 0
          · have hbv1 : bitStep (parseFold p) b =
                (let (absorbing, c, newStack) := absorbFold (parseFold p).2.1 (buildOp t [])
                 bif absorbing then ([], [], some (c, [])) else ([], newStack, Option.none)) := by
              rw [hbv0]; simp [hlt, harity]
            obtain ⟨habs1, habs2⟩ := absorbFold_spec (parseFold p).2.1 hopen (buildOp t [])
            have hopArityNil : ([] : List Code).length = opArity t := by simp [harity]
            have hE0 : (t.1 :: t.2.1 :: t.2.2 :: []) ++ (([] : List Code).map E).flatten
                = E (buildOp t []) := opArity_buildOp_eq_E t [] hopArityNil
            simp only [List.map_nil, List.flatten_nil, List.append_nil] at hE0
            by_cases habsorbing : (absorbFold (parseFold p).2.1 (buildOp t [])).1 = true
            · refine ⟨fun hslot2 => ?_, fun e r he => ?_⟩
              · exfalso
                rw [hfold, hbv1] at hslot2
                simp [habsorbing] at hslot2
              · rw [hfold, hbv1] at he
                simp only [habsorbing, Bool.cond_true, Option.some.injEq, Prod.mk.injEq] at he
                obtain ⟨he1, he2⟩ := he
                have hres : p ++ [b] = E (absorbFold (parseFold p).2.1 (buildOp t [])).2.1 := by
                  rw [hrec2, hE0]; exact habs1 habsorbing
                rw [← he2, List.append_nil, hres, he1]
            · have habsorbingF : (absorbFold (parseFold p).2.1 (buildOp t [])).1 = false := by
                cases hb : (absorbFold (parseFold p).2.1 (buildOp t [])).1 with
                | false => rfl
                | true => exact absurd hb habsorbing
              obtain ⟨hrecon2, hopen2⟩ := habs2 habsorbingF
              refine ⟨fun hslot2 => ?_, fun e r he => ?_⟩
              · rw [hfold, hbv1] at hslot2 ⊢
                simp only [habsorbingF, Bool.cond_false] at hslot2 ⊢
                refine ⟨?_, by simp, hopen2⟩
                rw [hrec2, hE0, List.append_nil]
                exact hrecon2.symm
              · exfalso
                rw [hfold, hbv1] at he
                simp [habsorbingF] at he
          · have hbv1 : bitStep (parseFold p) b
                = ([], (t, []) :: (parseFold p).2.1, Option.none) := by
              rw [hbv0]; simp [hlt, harity]
            refine ⟨fun hslot2 => ?_, fun e r he => ?_⟩
            · rw [hfold, hbv1] at hslot2 ⊢
              refine ⟨?_, by simp, ?_⟩
              · rw [stackBits_cons]
                have hfb : frameBits (t, ([] : List Code)) = [t.1, t.2.1, t.2.2] := by
                  simp [frameBits]
                rw [hfb, List.append_nil]
                exact hrec2.symm
              · intro fr' hm
                rcases List.mem_cons.mp hm with h1 | h2
                · subst h1
                  change ([] : List Code).length < opArity t
                  simpa using Nat.pos_of_ne_zero harity
                · exact hopen fr' h2
            · exfalso
              rw [hfold, hbv1] at he
              simp at he
      · have heq := ih.2 e r hnone
        refine ⟨fun hslot2 => ?_, fun e' r' he' => ?_⟩
        · exfalso
          rw [hfold] at hslot2
          unfold bitStep at hslot2
          rw [hnone] at hslot2
          simp at hslot2
        · rw [hfold] at he'
          unfold bitStep at he'
          rw [hnone] at he'
          simp only [Option.some.injEq, Prod.mk.injEq] at he'
          obtain ⟨he1, he2⟩ := he'
          rw [← he1, ← he2, heq, List.append_assoc]

/-- **Domain characterization**: a successful parse consumed exactly a serialization. The
third clause of `EParserSpec`. -/
theorem parseE_eq_some (w : List Bool) (e : Code) (r : List Bool) (h : parseE w = some (e, r)) :
    w = E e ++ r :=
  (parseFold_spec w).2 e r h

/-! ## `parseE` recovers a serialization: `parseE_E_append` -/

/-- **`parseE` recovers exactly what `E` serialized**, together with any trailing bits. The
second clause of `EParserSpec`. Proved by induction on `e`, generalized over the context stack
the bits are read into. -/
private theorem foldl_bitStep_E : ∀ (e : Code) (stack : List Frame),
    List.foldl bitStep ([], stack, Option.none) (E e) =
      bif (absorbFold stack e).1 then ([], [], some ((absorbFold stack e).2.1, []))
      else ([], (absorbFold stack e).2.2, Option.none) := by
  intro e
  induction e with
  | zero => intro stack; rfl
  | succ => intro stack; rfl
  | left => intro stack; rfl
  | right => intro stack; rfl
  | pair cf cg ihf ihg =>
      intro stack
      change List.foldl bitStep ([], stack, Option.none)
          ([true, false, false] ++ E cf ++ E cg) = _
      rw [List.foldl_append, List.foldl_append]
      have h1 : List.foldl bitStep ([], stack, Option.none) [true, false, false]
          = ([], ((true, false, false), []) :: stack, Option.none) := rfl
      rw [h1, ihf ((((true : Bool), false, false), ([] : List Code)) :: stack)]
      have habs1 : absorbFold ((((true : Bool), false, false), ([] : List Code)) :: stack) cf
          = (false, cf, ((true, false, false), [cf]) :: stack) := by
        change (((((true : Bool), false, false), ([] : List Code)) :: stack)).foldl
            absorbStep (true, cf, []) = _
        change List.foldl absorbStep (absorbStep (true, cf, []) (((true : Bool), false, false), []))
            stack = _
        have : absorbStep (true, cf, []) (((true : Bool), false, false), ([] : List Code))
            = (false, cf, [((((true : Bool), false, false)), [cf])]) := by
          simp [absorbStep, opArity]
        rw [this, absorbFold_not_absorbing]
        simp
      rw [habs1]
      simp only [Bool.cond_false]
      rw [ihg (((((true : Bool), false, false)), [cf]) :: stack)]
      have habs2 : absorbFold (((((true : Bool), false, false)), [cf]) :: stack) cg
          = absorbFold stack (Code.pair cf cg) := by
        change (((((true : Bool), false, false)), [cf]) :: stack).foldl absorbStep
            (true, cg, []) = _
        change List.foldl absorbStep
            (absorbStep (true, cg, []) ((((true : Bool), false, false)), [cf])) stack
            = absorbFold stack (Code.pair cf cg)
        have hstepEq : absorbStep (true, cg, []) ((((true : Bool), false, false)), [cf])
            = (true, Code.pair cf cg, []) := by
          simp [absorbStep, opArity, buildOp]
        rw [hstepEq]
        rfl
      rw [habs2]
  | comp cf cg ihf ihg =>
      intro stack
      change List.foldl bitStep ([], stack, Option.none)
          ([true, false, true] ++ E cf ++ E cg) = _
      rw [List.foldl_append, List.foldl_append]
      have h1 : List.foldl bitStep ([], stack, Option.none) [true, false, true]
          = ([], ((true, false, true), []) :: stack, Option.none) := rfl
      rw [h1, ihf ((((true : Bool), false, true), ([] : List Code)) :: stack)]
      have habs1 : absorbFold ((((true : Bool), false, true), ([] : List Code)) :: stack) cf
          = (false, cf, ((true, false, true), [cf]) :: stack) := by
        change List.foldl absorbStep (absorbStep (true, cf, []) (((true : Bool), false, true), []))
            stack = _
        have : absorbStep (true, cf, []) (((true : Bool), false, true), ([] : List Code))
            = (false, cf, [((((true : Bool), false, true)), [cf])]) := by
          simp [absorbStep, opArity]
        rw [this, absorbFold_not_absorbing]
        simp
      rw [habs1]
      simp only [Bool.cond_false]
      rw [ihg (((((true : Bool), false, true)), [cf]) :: stack)]
      have habs2 : absorbFold (((((true : Bool), false, true)), [cf]) :: stack) cg
          = absorbFold stack (Code.comp cf cg) := by
        change List.foldl absorbStep
            (absorbStep (true, cg, []) ((((true : Bool), false, true)), [cf])) stack
            = absorbFold stack (Code.comp cf cg)
        have hstepEq : absorbStep (true, cg, []) ((((true : Bool), false, true)), [cf])
            = (true, Code.comp cf cg, []) := by
          simp [absorbStep, opArity, buildOp]
        rw [hstepEq]
        rfl
      rw [habs2]
  | prec cf cg ihf ihg =>
      intro stack
      change List.foldl bitStep ([], stack, Option.none)
          ([true, true, false] ++ E cf ++ E cg) = _
      rw [List.foldl_append, List.foldl_append]
      have h1 : List.foldl bitStep ([], stack, Option.none) [true, true, false]
          = ([], ((true, true, false), []) :: stack, Option.none) := rfl
      rw [h1, ihf ((((true : Bool), true, false), ([] : List Code)) :: stack)]
      have habs1 : absorbFold ((((true : Bool), true, false), ([] : List Code)) :: stack) cf
          = (false, cf, ((true, true, false), [cf]) :: stack) := by
        change List.foldl absorbStep (absorbStep (true, cf, []) (((true : Bool), true, false), []))
            stack = _
        have : absorbStep (true, cf, []) (((true : Bool), true, false), ([] : List Code))
            = (false, cf, [((((true : Bool), true, false)), [cf])]) := by
          simp [absorbStep, opArity]
        rw [this, absorbFold_not_absorbing]
        simp
      rw [habs1]
      simp only [Bool.cond_false]
      rw [ihg (((((true : Bool), true, false)), [cf]) :: stack)]
      have habs2 : absorbFold (((((true : Bool), true, false)), [cf]) :: stack) cg
          = absorbFold stack (Code.prec cf cg) := by
        change List.foldl absorbStep
            (absorbStep (true, cg, []) ((((true : Bool), true, false)), [cf])) stack
            = absorbFold stack (Code.prec cf cg)
        have hstepEq : absorbStep (true, cg, []) ((((true : Bool), true, false)), [cf])
            = (true, Code.prec cf cg, []) := by
          simp [absorbStep, opArity, buildOp]
        rw [hstepEq]
        rfl
      rw [habs2]
  | rfind' cf ihf =>
      intro stack
      change List.foldl bitStep ([], stack, Option.none) ([true, true, true] ++ E cf) = _
      rw [List.foldl_append]
      have h1 : List.foldl bitStep ([], stack, Option.none) [true, true, true]
          = ([], ((true, true, true), []) :: stack, Option.none) := rfl
      rw [h1, ihf ((((true : Bool), true, true), ([] : List Code)) :: stack)]
      have habs1 : absorbFold ((((true : Bool), true, true), ([] : List Code)) :: stack) cf
          = absorbFold stack (Code.rfind' cf) := by
        change List.foldl absorbStep (absorbStep (true, cf, []) (((true : Bool), true, true), []))
            stack = _
        have hstepEq : absorbStep (true, cf, []) (((true : Bool), true, true), ([] : List Code))
            = (true, Code.rfind' cf, []) := by
          simp [absorbStep, opArity, buildOp]
        rw [hstepEq]
        rfl
      rw [habs1]

/-- **`parseE` recovers exactly what `E` serialized**, together with any trailing bits. The
second clause of `EParserSpec`. -/
theorem parseE_E_append (e : Code) (r : List Bool) : parseE (E e ++ r) = some (e, r) := by
  change (parseFold (E e ++ r)).2.2 = some (e, r)
  change (List.foldl bitStep ([], [], Option.none) (E e ++ r)).2.2 = some (e, r)
  rw [List.foldl_append, foldl_bitStep_E e []]
  have habs : absorbFold [] e = (true, e, []) := rfl
  rw [habs]
  simp only [Bool.cond_true]
  change (List.foldl bitStep ([], [], some (e, [])) r).2.2 = some (e, r)
  have hslot : ∀ (L : List Bool) (c : Code) (tr : List Bool) (tag : List Bool)
      (stack : List Frame),
      List.foldl bitStep (tag, stack, some (c, tr)) L = (tag, stack, some (c, tr ++ L)) := by
    intro L
    induction L with
    | nil => intro c tr tag stack; simp
    | cons b L ih =>
        intro c tr tag stack
        change List.foldl bitStep (bitStep (tag, stack, some (c, tr)) b) L = _
        have : bitStep (tag, stack, some (c, tr)) b = (tag, stack, some (c, tr ++ [b])) := rfl
        rw [this, ih]
        simp
  rw [hslot r e [] [] []]
  simp

/-! ## `parseE` is `Primrec` -/

private theorem primrec_opArity : Primrec opArity := by
  have h1 : Primrec fun t : Tag => t.2.1 && t.2.2 :=
    Primrec.dom_bool₂ Bool.and |>.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)
  have h2 : Primrec fun t : Tag => (bif (t.2.1 && t.2.2) then 1 else 2 : ℕ) :=
    Primrec.cond h1 (Primrec.const 1) (Primrec.const 2)
  exact Primrec.cond Primrec.fst h2 (Primrec.const 0)

private theorem primrec_buildOp : Primrec₂ buildOp := by
  have hb0 : Primrec fun p : Tag × List Code => p.1.1 := Primrec.fst.comp Primrec.fst
  have hb1 : Primrec fun p : Tag × List Code => p.1.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have hb2 : Primrec fun p : Tag × List Code => p.1.2.2 :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.fst)
  have hc0 : Primrec fun p : Tag × List Code => p.2.headI := Primrec.list_headI.comp Primrec.snd
  have hc1 : Primrec fun p : Tag × List Code => p.2.tail.headI :=
    Primrec.list_headI.comp (Primrec.list_tail.comp Primrec.snd)
  have hrfind : Primrec fun p : Tag × List Code => Code.rfind' p.2.headI :=
    Nat.Partrec.Code.primrec_rfind'.comp hc0
  have hprec : Primrec fun p : Tag × List Code => Code.prec p.2.headI p.2.tail.headI :=
    Nat.Partrec.Code.primrec₂_prec.comp hc0 hc1
  have hcomp : Primrec fun p : Tag × List Code => Code.comp p.2.headI p.2.tail.headI :=
    Nat.Partrec.Code.primrec₂_comp.comp hc0 hc1
  have hpair : Primrec fun p : Tag × List Code => Code.pair p.2.headI p.2.tail.headI :=
    Nat.Partrec.Code.primrec₂_pair.comp hc0 hc1
  have hArity2 : Primrec fun p : Tag × List Code =>
      (bif p.1.2.2 then Code.rfind' p.2.headI else Code.prec p.2.headI p.2.tail.headI) :=
    Primrec.cond hb2 hrfind hprec
  have hCompPair : Primrec fun p : Tag × List Code =>
      (bif p.1.2.2 then Code.comp p.2.headI p.2.tail.headI
       else Code.pair p.2.headI p.2.tail.headI) :=
    Primrec.cond hb2 hcomp hpair
  have hArityTop : Primrec fun p : Tag × List Code =>
      (bif p.1.2.1 then
          (bif p.1.2.2 then Code.rfind' p.2.headI else Code.prec p.2.headI p.2.tail.headI)
        else
          (bif p.1.2.2 then Code.comp p.2.headI p.2.tail.headI
            else Code.pair p.2.headI p.2.tail.headI)) :=
    Primrec.cond hb1 hArity2 hCompPair
  have hLeaf2 : Primrec fun p : Tag × List Code => (bif p.1.2.2 then Code.right else Code.left) :=
    Primrec.cond hb2 (Primrec.const Code.right) (Primrec.const Code.left)
  have hLeaf2' : Primrec fun p : Tag × List Code => (bif p.1.2.2 then Code.succ else Code.zero) :=
    Primrec.cond hb2 (Primrec.const Code.succ) (Primrec.const Code.zero)
  have hLeafTop : Primrec fun p : Tag × List Code =>
      (bif p.1.2.1 then (bif p.1.2.2 then Code.right else Code.left)
        else (bif p.1.2.2 then Code.succ else Code.zero)) :=
    Primrec.cond hb1 hLeaf2 hLeaf2'
  exact (Primrec.cond hb0 hArityTop hLeafTop).of_eq fun p => by simp [buildOp]

private theorem primrec₂_absorbStep : Primrec₂ absorbStep := by
  have hst1 : Primrec fun p : (Bool × Code × List Frame) × Frame => p.1.1 :=
    Primrec.fst.comp Primrec.fst
  have hst2c : Primrec fun p : (Bool × Code × List Frame) × Frame => p.1.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have hst2ds : Primrec fun p : (Bool × Code × List Frame) × Frame => p.1.2.2 :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.fst)
  have hfr1 : Primrec fun p : (Bool × Code × List Frame) × Frame => p.2.1 :=
    Primrec.fst.comp Primrec.snd
  have hfr2 : Primrec fun p : (Bool × Code × List Frame) × Frame => p.2.2 :=
    Primrec.snd.comp Primrec.snd
  have hcs' : Primrec fun p : (Bool × Code × List Frame) × Frame => p.2.2 ++ [p.1.2.1] :=
    Primrec.list_concat.comp hfr2 hst2c
  have hlen : Primrec fun p : (Bool × Code × List Frame) × Frame => (p.2.2 ++ [p.1.2.1]).length :=
    Primrec.list_length.comp hcs'
  have harityFr1 : Primrec fun p : (Bool × Code × List Frame) × Frame => opArity p.2.1 :=
    primrec_opArity.comp hfr1
  have hdecide : Primrec fun p : (Bool × Code × List Frame) × Frame =>
      decide ((p.2.2 ++ [p.1.2.1]).length = opArity p.2.1) :=
    Primrec.eq.decide.comp hlen harityFr1
  have hbuildOp' : Primrec fun p : (Bool × Code × List Frame) × Frame =>
      buildOp p.2.1 (p.2.2 ++ [p.1.2.1]) := Primrec₂.comp primrec_buildOp hfr1 hcs'
  have htrueVal : Primrec fun p : (Bool × Code × List Frame) × Frame =>
      (true, buildOp p.2.1 (p.2.2 ++ [p.1.2.1]), p.1.2.2) :=
    (Primrec.const true).pair (hbuildOp'.pair hst2ds)
  have hpairFrCs : Primrec fun p : (Bool × Code × List Frame) × Frame =>
      (p.2.1, p.2.2 ++ [p.1.2.1]) := hfr1.pair hcs'
  have hstack' : Primrec fun p : (Bool × Code × List Frame) × Frame =>
      p.1.2.2 ++ [(p.2.1, p.2.2 ++ [p.1.2.1])] := Primrec.list_concat.comp hst2ds hpairFrCs
  have hfalseVal1 : Primrec fun p : (Bool × Code × List Frame) × Frame =>
      (false, p.1.2.1, p.1.2.2 ++ [(p.2.1, p.2.2 ++ [p.1.2.1])]) :=
    (Primrec.const false).pair (hst2c.pair hstack')
  have hInner : Primrec fun p : (Bool × Code × List Frame) × Frame =>
      (bif decide ((p.2.2 ++ [p.1.2.1]).length = opArity p.2.1) then
          (true, buildOp p.2.1 (p.2.2 ++ [p.1.2.1]), p.1.2.2)
        else (false, p.1.2.1, p.1.2.2 ++ [(p.2.1, p.2.2 ++ [p.1.2.1])])) :=
    Primrec.cond hdecide htrueVal hfalseVal1
  have hstackFr : Primrec fun p : (Bool × Code × List Frame) × Frame => p.1.2.2 ++ [p.2] :=
    Primrec.list_concat.comp hst2ds Primrec.snd
  have hOuterFalse : Primrec fun p : (Bool × Code × List Frame) × Frame =>
      (false, p.1.2.1, p.1.2.2 ++ [p.2]) :=
    (Primrec.const false).pair (hst2c.pair hstackFr)
  exact (Primrec.cond hst1 hInner hOuterFalse).of_eq fun p => by
    obtain ⟨⟨s1, s2, s3⟩, fr⟩ := p
    simp [absorbStep]

private theorem primrec₂_absorbFold : Primrec₂ absorbFold := by
  have hg : Primrec fun a : List Frame × Code => (true, a.2, ([] : List Frame)) :=
    (Primrec.const true).pair (Primrec.snd.pair (Primrec.const ([] : List Frame)))
  have hh : Primrec₂ fun (_ : List Frame × Code) (sb : (Bool × Code × List Frame) × Frame) =>
      absorbStep sb.1 sb.2 := Primrec.comp₂ primrec₂_absorbStep Primrec₂.right
  have := Primrec.list_foldl Primrec.fst hg hh
  exact this.of_eq fun a => rfl

private theorem primrec₂_bitStep : Primrec₂ bitStep := by
  have hst1 : Primrec fun p : PState × Bool => p.1.1 := Primrec.fst.comp Primrec.fst
  have hst2s : Primrec fun p : PState × Bool => p.1.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have hst2o : Primrec fun p : PState × Bool => p.1.2.2 :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.fst)
  have hbb : Primrec fun p : PState × Bool => p.2 := Primrec.snd
  -- the `Option.none` branch: mirrors `bitStep`'s own case split, closed form
  have htag' : Primrec fun p : PState × Bool => p.1.1 ++ [p.2] := Primrec.list_concat.comp hst1 hbb
  have htaglen : Primrec fun p : PState × Bool => (p.1.1 ++ [p.2]).length :=
    Primrec.list_length.comp htag'
  have hltdec : Primrec fun p : PState × Bool => decide ((p.1.1 ++ [p.2]).length < 3) :=
    Primrec.nat_lt.decide.comp htaglen (Primrec.const 3)
  have hTrueVal : Primrec fun p : PState × Bool =>
      (p.1.1 ++ [p.2], p.1.2.1, (Option.none : Option (Code × List Bool))) :=
    htag'.pair (hst2s.pair (Primrec.const Option.none))
  have hc0 : Primrec fun p : PState × Bool => (p.1.1 ++ [p.2]).headI :=
    Primrec.list_headI.comp htag'
  have hc1 : Primrec fun p : PState × Bool => (p.1.1 ++ [p.2]).tail.headI :=
    Primrec.list_headI.comp (Primrec.list_tail.comp htag')
  have hc2 : Primrec fun p : PState × Bool => (p.1.1 ++ [p.2]).tail.tail.headI :=
    Primrec.list_headI.comp (Primrec.list_tail.comp (Primrec.list_tail.comp htag'))
  have ht : Primrec fun p : PState × Bool =>
      ((p.1.1 ++ [p.2]).headI, (p.1.1 ++ [p.2]).tail.headI, (p.1.1 ++ [p.2]).tail.tail.headI) :=
    hc0.pair (hc1.pair hc2)
  have harityT : Primrec fun p : PState × Bool =>
      opArity ((p.1.1 ++ [p.2]).headI, (p.1.1 ++ [p.2]).tail.headI,
        (p.1.1 ++ [p.2]).tail.tail.headI) := primrec_opArity.comp ht
  have harityDec : Primrec fun p : PState × Bool =>
      decide (opArity ((p.1.1 ++ [p.2]).headI, (p.1.1 ++ [p.2]).tail.headI,
        (p.1.1 ++ [p.2]).tail.tail.headI) = 0) := Primrec.eq.decide.comp harityT (Primrec.const 0)
  have hbuildOpNil : Primrec fun p : PState × Bool =>
      buildOp ((p.1.1 ++ [p.2]).headI, (p.1.1 ++ [p.2]).tail.headI,
        (p.1.1 ++ [p.2]).tail.tail.headI) ([] : List Code) :=
    Primrec₂.comp primrec_buildOp ht (Primrec.const [])
  have habsFold : Primrec fun p : PState × Bool =>
      absorbFold p.1.2.1 (buildOp ((p.1.1 ++ [p.2]).headI, (p.1.1 ++ [p.2]).tail.headI,
        (p.1.1 ++ [p.2]).tail.tail.headI) []) := Primrec₂.comp primrec₂_absorbFold hst2s hbuildOpNil
  have habsorbing : Primrec fun p : PState × Bool =>
      (absorbFold p.1.2.1 (buildOp ((p.1.1 ++ [p.2]).headI, (p.1.1 ++ [p.2]).tail.headI,
        (p.1.1 ++ [p.2]).tail.tail.headI) [])).1 := Primrec.fst.comp habsFold
  have hcVal : Primrec fun p : PState × Bool =>
      (absorbFold p.1.2.1 (buildOp ((p.1.1 ++ [p.2]).headI, (p.1.1 ++ [p.2]).tail.headI,
        (p.1.1 ++ [p.2]).tail.tail.headI) [])).2.1 :=
    Primrec.fst.comp (Primrec.snd.comp habsFold)
  have hnewStack : Primrec fun p : PState × Bool =>
      (absorbFold p.1.2.1 (buildOp ((p.1.1 ++ [p.2]).headI, (p.1.1 ++ [p.2]).tail.headI,
        (p.1.1 ++ [p.2]).tail.tail.headI) [])).2.2 :=
    Primrec.snd.comp (Primrec.snd.comp habsFold)
  have hAbsorbTrueVal :=
    (Primrec.const ([] : List Bool)).pair ((Primrec.const ([] : List Frame)).pair
      (Primrec.option_some.comp (hcVal.pair (Primrec.const ([] : List Bool)))))
  have hAbsorbFalseVal :=
    (Primrec.const ([] : List Bool)).pair
      (hnewStack.pair (Primrec.const (Option.none : Option (Code × List Bool))))
  have hArity0Val := Primrec.cond habsorbing hAbsorbTrueVal hAbsorbFalseVal
  have htNilPair := ht.pair (Primrec.const ([] : List Code))
  have hconsStack := Primrec.list_cons.comp htNilPair hst2s
  have hPushVal :=
    (Primrec.const ([] : List Bool)).pair
      (hconsStack.pair (Primrec.const (Option.none : Option (Code × List Bool))))
  have hFalseOuterVal := Primrec.cond harityDec hArity0Val hPushVal
  have hf := Primrec.cond hltdec hTrueVal hFalseOuterVal
  have hg : Primrec₂ fun (p : PState × Bool) (x : Code × List Bool) =>
      (p.1.1, p.1.2.1, some (x.1, x.2 ++ [p.2])) := by
    have hp1 : Primrec fun q : (PState × Bool) × (Code × List Bool) => q.1.1.1 :=
      Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
    have hp2s : Primrec fun q : (PState × Bool) × (Code × List Bool) => q.1.1.2.1 :=
      Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
    have hqb : Primrec fun q : (PState × Bool) × (Code × List Bool) => q.1.2 :=
      Primrec.snd.comp Primrec.fst
    have hxc : Primrec fun q : (PState × Bool) × (Code × List Bool) => q.2.1 :=
      Primrec.fst.comp Primrec.snd
    have hxtr : Primrec fun q : (PState × Bool) × (Code × List Bool) => q.2.2 :=
      Primrec.snd.comp Primrec.snd
    have hxtr' : Primrec fun q : (PState × Bool) × (Code × List Bool) => q.2.2 ++ [q.1.2] :=
      Primrec.list_concat.comp hxtr hqb
    have hsome : Primrec fun q : (PState × Bool) × (Code × List Bool) =>
        some (q.2.1, q.2.2 ++ [q.1.2]) := Primrec.option_some.comp (hxc.pair hxtr')
    exact hp1.pair (hp2s.pair hsome)
  exact (Primrec.option_casesOn hst2o hf hg).of_eq fun p => by
    obtain ⟨⟨s1, s2, s3⟩, b⟩ := p
    cases s3 with
    | none => simp [bitStep]
    | some x => obtain ⟨c, tr⟩ := x; simp [bitStep]

private theorem primrec_parseFold : Primrec parseFold := by
  have hh : Primrec₂ fun (_ : List Bool) (sb : PState × Bool) => bitStep sb.1 sb.2 :=
    Primrec.comp₂ primrec₂_bitStep Primrec₂.right
  have := Primrec.list_foldl Primrec.id
    (Primrec.const (([], [], Option.none) : PState)) hh
  exact this.of_eq fun w => rfl

/-- **`parseE` is `Primrec`.** The first clause of `EParserSpec`. -/
theorem primrec_parseE : Primrec parseE :=
  (Primrec.snd.comp (Primrec.snd.comp primrec_parseFold))

/-! ## The packaged witness -/

/-- **The parser specification, discharged.** `parseE` is `Primrec`, recovers `(e, r)` from
`E e ++ r`, and only from a description of that shape. -/
theorem eParserSpec : EParserSpec :=
  ⟨parseE, primrec_parseE, parseE_E_append, parseE_eq_some⟩

/-! ## Axiom guards -/

-- The axiom-list expectations below cannot be wrapped (`#guard_msgs` matches one line per
-- expectation); scoped to this block rather than the whole file.
set_option linter.style.longLine false in
/-- info: 'AdditiveComplexity.parseE_E_append' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms parseE_E_append

set_option linter.style.longLine false in
/-- info: 'AdditiveComplexity.parseE_eq_some' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms parseE_eq_some

set_option linter.style.longLine false in
/-- info: 'AdditiveComplexity.primrec_parseE' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms primrec_parseE

set_option linter.style.longLine false in
/-- info: 'AdditiveComplexity.eParserSpec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms eParserSpec

end AdditiveComplexity
