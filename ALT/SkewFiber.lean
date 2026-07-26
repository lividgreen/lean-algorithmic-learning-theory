/-
Copyright (c) 2026 Mykola Palamarchuk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mykola Palamarchuk
-/
import Mathlib.Algebra.BigOperators.Fin
import ALT.PersistenceCapacity

-- Formal-check file, not Mathlib-destined: opt out of the house-style header linter.
set_option linter.style.header false

/-!
# The skew-product fiber: an evolving population, priced by emergence ([Inevitability] §6)

A **skew product** `U (x, y) = (S x, F x y)` runs a base rule `S` in the first coordinate and a
*base-driven* fiber rule `F` in the second: the fiber reads the base, the base ignores the fiber.
This file builds the finite, tabulated form of that shape and prices it, then instantiates the
fiber with **one deterministic generation of variation and selection** over a population of
candidate codewords, whose fittest member is read back as the guest.

This is the combinatorial skeleton of the mechanism [Inevitability] §6 proposes — evolution in the
fiber of a skew product — and only that. What §6 leaves open, this file leaves open.

The pricing is the point. A skew world on `n₁ · C ^ P` states has an exponentially long table, so
the only affordable description of it is the **composition** of its two ingredients' descriptions:
`skewBuilder` takes a code for the base rule's table and a code for the fiber step's table and
outputs the whole world's table, reading both structural sizes off the tables' own lengths. The
world therefore costs `elen cS + elen cF + O(1)` (`KE_skewWorldFin_le`) — the base rule plus the
evolutionary rule plus an absolute constant, with nothing that scales with the state count. Feeding
the world's own table as a loaded numeral instead would price the table rather than the law, and the
resulting bound would be vacuous.

## Main results

* `skewWorldFin` / `lensTable_skewWorldFin` — the finite skew product and its table: entry `q` is
  the fiber step's entry `q` shifted by the fiber width times the base rule's entry `q / width`.
  Both the width and the base index are recovered by division from the tables' lengths, so no size
  parameter is loaded.
* `skewBuilder` / `KE_skewWorldFin_le` — **skew products are cheap when their ingredients are**:
  one fixed builder, so the world's description length is the two rules' lengths plus
  `elen skewBuilder + 6`, an absolute constant independent of the world and of `n₁`, `C`, `P`.
* `gaGen` / `evoFiber` / `fittestFrame` — one deterministic generation in the fiber (mutate every
  slot by the base-driven mutation, then select the fittest), transported onto the numeral carrier
  `Fin (C ^ P)`, and the frame that reads the current fittest codeword back.
* `fiber_emergence_pricing` — **the assembly**: given the composed cheap code for the skew world, a
  code for the fittest-reading frame, and — as a NAMED, imported hypothesis — that the frame reads a
  full model off the recurrent core, the existing `emergence` theorem hands back an owned guest
  priced at `elen cS + elen cF + elen cθ + O(1)`.
* `surjective_fittestFrame_of_fixed` — **the imported hypothesis is satisfiable**, so the pricing
  theorem is not vacuous: at an evolutionary fixed point a uniform population stands still and the
  fittest reading is surjective, on any fitness.

## Scope

The convergence hypothesis is imported, not proved. `fiber_emergence_pricing` takes
`Function.Surjective (fun s => θ (U^[N] s))` as a hypothesis: the operational form of "the fiber's
population has settled on a faithful reading of the core". Discharging it is a separate matter
entirely — it is where selection-by-predictive-fitness has to be shown to converge, and where the
basin of initial conditions from which it does has to be exhibited.

Two further gaps are deliberate and are not narrowed here. The base of this construction is a
finite endofunction on `Fin n₁`, carrying no measure and no mixing hypothesis; the mixing base and
its invariant measure are analytic objects that this finite, combinatorial layer does not host. And
the host here is of fixed size, so nothing about a *growing* host — code accreting on a frontier
while the written region stays fixed — is represented. This file is the pricing skeleton only.

No numbered result is claimed machine-checked by this file.
-/

namespace SkewFiber

open PersistenceCapacity Decoupling AdditiveComplexity
open Equiv MulAction

-- `•` on the recurrent-core reading is the relabelling action `U • ℓ = ℓ ∘ U⁻¹`; the same local
-- instance `PersistenceCapacity.emergence` is stated under.
attribute [local instance] arrowAction

/-! ## The skew product, tabulated -/

section Skew

variable {n₁ n₂ : ℕ}

/-- If `b` outputs `v` on input `j`, then `comp a b` runs `a` on `v` (the `comp` eval law is
definitional). Local copy of the same helper `PersistenceCapacity` keeps private. -/
private theorem eval_comp_some {a b : Nat.Partrec.Code} {j v : ℕ}
    (hv : Nat.Partrec.Code.eval b j = Part.some v) :
    Nat.Partrec.Code.eval (Nat.Partrec.Code.comp a b) j = Nat.Partrec.Code.eval a v := by
  change Nat.Partrec.Code.eval b j >>= Nat.Partrec.Code.eval a = Nat.Partrec.Code.eval a v
  rw [hv]
  exact Part.bind_some v (Nat.Partrec.Code.eval a)

/-- **The finite skew product** ([Inevitability] §6): the base coordinate steps by `S` alone, the
fiber coordinate steps by `F` *read at the current base state*. The fiber sees the base; the base
does not see the fiber. The Cartesian product world `prodWorldFinFn` is the degenerate case in
which `F` ignores its first argument.

`F` is a general base-driven fiber rule; the cocycle form `U (x, y) = (S x, y ⊕ φ x)` that
[Inevitability] §6 writes is the special case where the fiber's step is a group translation by a
function of the base. The general form is what an evolutionary fiber needs. -/
def skewWorldFin (S : Fin n₁ → Fin n₁) (F : Fin n₁ → Fin n₂ → Fin n₂) :
    Fin (n₁ * n₂) → Fin (n₁ * n₂) :=
  fun p => finProdFinEquiv
    (S (finProdFinEquiv.symm p).1, F (finProdFinEquiv.symm p).1 (finProdFinEquiv.symm p).2)

@[simp] theorem skewWorldFin_apply (S : Fin n₁ → Fin n₁) (F : Fin n₁ → Fin n₂ → Fin n₂)
    (i : Fin n₁) (j : Fin n₂) :
    skewWorldFin S F (finProdFinEquiv (i, j)) = finProdFinEquiv (S i, F i j) := by
  simp [skewWorldFin]

/-- **The fiber step, uncurried onto the flat carrier**: the one `Fin (n₁ * n₂) → Fin n₂` function
whose table carries everything the fiber rule does. This — not the curried `F` — is what enters the
price, because it is what has a table. -/
def fiberFlat (F : Fin n₁ → Fin n₂ → Fin n₂) : Fin (n₁ * n₂) → Fin n₂ :=
  fun p => F (finProdFinEquiv.symm p).1 (finProdFinEquiv.symm p).2

@[simp] theorem fiberFlat_apply (F : Fin n₁ → Fin n₂ → Fin n₂) (i : Fin n₁) (j : Fin n₂) :
    fiberFlat F (finProdFinEquiv (i, j)) = F i j := by
  simp [fiberFlat]

/-- **The base rule's table and the fiber rule's table, woven**: entry `q` of the skew world's table
is the fiber's own entry `q`, shifted by the fiber width times the base's entry at `q / width`.

Both structural numbers are read off the two tables — the width is `T₂.length / T₁.length`, since a
table is as long as its state space and the fiber's state space is the whole product — so, exactly
as for `prodAppend`, no size parameter appears. -/
def skewAppend (T₁ T₂ : List ℕ) : List ℕ :=
  (List.range T₂.length).map fun q =>
    T₂.getD q 0 + (T₂.length / T₁.length) * T₁.getD (q / (T₂.length / T₁.length)) 0

theorem primrec_skewAppend : Primrec fun q : List ℕ × List ℕ => skewAppend q.1 q.2 := by
  have hw : Primrec fun q : List ℕ × List ℕ => q.2.length / q.1.length :=
    Primrec.nat_div.comp (Primrec.list_length.comp Primrec.snd)
      (Primrec.list_length.comp Primrec.fst)
  refine Primrec.list_map (Primrec.list_range.comp (Primrec.list_length.comp Primrec.snd)) ?_
  refine Primrec₂.mk ?_
  have hfst : Primrec fun p : (List ℕ × List ℕ) × ℕ => p.1 := Primrec.fst
  have hq : Primrec fun p : (List ℕ × List ℕ) × ℕ => p.2 := Primrec.snd
  have hw' : Primrec fun p : (List ℕ × List ℕ) × ℕ => p.1.2.length / p.1.1.length := hw.comp hfst
  exact Primrec.nat_add.comp
    ((Primrec.list_getD 0).comp (Primrec.snd.comp hfst) hq)
    (Primrec.nat_mul.comp hw'
      ((Primrec.list_getD 0).comp (Primrec.fst.comp hfst) (Primrec.nat_div.comp hq hw')))

/-- A lens table's entry at a flat index, read through the raw natural number, not a `Fin`. -/
theorem lensTable_getD {N m : ℕ} (ℓ : Fin N → Fin m) {q : ℕ} (h : q < N) :
    (lensTable ℓ).getD q 0 = (ℓ ⟨q, h⟩ : ℕ) := by
  rw [lensTable]
  exact getD_map_finRange (fun j : Fin N => ((ℓ j : Fin m) : ℕ)) ⟨q, h⟩

/-- **The skew world's table is its two rules' tables, woven.** The weave is the flat-index
arithmetic of `finProdFinEquiv`: the state `q` splits as base `q / n₂` and fiber `q % n₂`, the fiber
table already lists `F` at every such pair in that order, and the base contributes the block
shift. -/
theorem lensTable_skewWorldFin (S : Fin n₁ → Fin n₁) (F : Fin n₁ → Fin n₂ → Fin n₂) :
    lensTable (skewWorldFin S F) = skewAppend (lensTable S) (lensTable (fiberFlat F)) := by
  rcases Nat.eq_zero_or_pos n₁ with hn₁ | hn₁
  · subst hn₁
    simp [skewAppend, lensTable]
  have hw : (lensTable (fiberFlat F)).length / (lensTable S).length = n₂ := by
    rw [lensTable_length, lensTable_length]
    exact Nat.mul_div_cancel_left n₂ hn₁
  rw [skewAppend, hw, lensTable_length, lensTable_range]
  refine List.map_congr_left fun q hq => ?_
  have hqlt : q < n₁ * n₂ := List.mem_range.mp hq
  have hn₂ : 0 < n₂ := Nat.pos_of_ne_zero fun h => by simp [h] at hqlt
  have hdiv : q / n₂ < n₁ := Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm] at hqlt)
  rw [dif_pos hqlt, lensTable_getD _ hqlt, lensTable_getD _ hdiv]
  have hidx : (⟨q, hqlt⟩ : Fin (n₁ * n₂))
      = finProdFinEquiv (⟨q / n₂, hdiv⟩, ⟨q % n₂, Nat.mod_lt _ hn₂⟩) := by
    have hmd : q % n₂ + n₂ * (q / n₂) = q := Nat.mod_add_div q n₂
    apply Fin.ext
    simp only [finProdFinEquiv_apply_val]
    omega
  rw [hidx, skewWorldFin_apply, fiberFlat_apply, finProdFinEquiv_apply_val]

/-! ### The builder: one fixed program that weaves any two rules -/

/-- **The skew-world builder**: on `⟨the base rule's table, the fiber rule's table⟩` it outputs the
skew world's table. ONE fixed function, with no size parameters at all. -/
def skewTableFn (p : ℕ) : ℕ :=
  Encodable.encode
    (skewAppend ((Encodable.decode (α := List ℕ) p.unpair.1).getD [])
      ((Encodable.decode (α := List ℕ) p.unpair.2).getD []))

theorem primrec_skewTableFn : Primrec skewTableFn := by
  have hdec1 : Primrec fun p : ℕ => (Encodable.decode (α := List ℕ) p.unpair.1).getD [] :=
    Primrec.option_getD.comp (Primrec.decode.comp (Primrec.fst.comp Primrec.unpair))
      (Primrec.const [])
  have hdec2 : Primrec fun p : ℕ => (Encodable.decode (α := List ℕ) p.unpair.2).getD [] :=
    Primrec.option_getD.comp (Primrec.decode.comp (Primrec.snd.comp Primrec.unpair))
      (Primrec.const [])
  exact Primrec.encode.comp (primrec_skewAppend.comp (Primrec.pair hdec1 hdec2))

/-- **The builder is correct**: it outputs exactly the skew world's encoded table. -/
theorem skewTableFn_eq (S : Fin n₁ → Fin n₁) (F : Fin n₁ → Fin n₂ → Fin n₂) :
    skewTableFn (Nat.pair (lensCode S) (lensCode (fiberFlat F)))
      = lensCode (skewWorldFin S F) := by
  rw [skewTableFn]
  simp only [Nat.unpair_pair, decode_lensCode]
  rw [← lensTable_skewWorldFin]
  rfl

theorem partrec_skewTableFn : Nat.Partrec (fun p : ℕ => (skewTableFn p : ℕ)) :=
  _root_.Partrec.nat_iff.mp (Primrec.to_comp primrec_skewTableFn).partrec

/-- **The fixed skew-world builder code.** -/
noncomputable def skewBuilder : Nat.Partrec.Code :=
  Classical.choose (Nat.Partrec.Code.exists_code.mp partrec_skewTableFn)

theorem eval_skewBuilder (p : ℕ) :
    Nat.Partrec.Code.eval skewBuilder p = Part.some (skewTableFn p) := by
  have h := congrFun (Classical.choose_spec
    (Nat.Partrec.Code.exists_code.mp partrec_skewTableFn)) p
  simpa [skewBuilder] using h

/-! ### The cheap code for the whole world

The composition shape, and deliberately not the load-the-value shape. `Code.const (lensCode U)`
would also compute the world's table, but its length is the length of that table's numeral — which
grows with the state count, here exponentially in the population — and the resulting capacity bound
would say nothing. The code below instead *runs* the two rules' codes and lets the fixed builder do
the weaving, so its length is additive in the two rules. -/

/-- **The skew world's cheap code**: run the base rule's code and the fiber rule's code, pair the
two tables, hand them to the fixed builder. -/
noncomputable def skewCode (cS cF : Nat.Partrec.Code) : Nat.Partrec.Code :=
  Nat.Partrec.Code.comp skewBuilder (Nat.Partrec.Code.pair cS cF)

/-- The composed code is additive in its two ingredients, over one absolute constant. -/
theorem elen_skewCode (cS cF : Nat.Partrec.Code) :
    elen (skewCode cS cF) = elen skewBuilder + elen cS + elen cF + 6 := by
  rw [skewCode, E_len_comp, E_len_pair]
  omega

/-- The composed code computes the skew world's table. -/
theorem eval_skewCode (S : Fin n₁ → Fin n₁) (F : Fin n₁ → Fin n₂ → Fin n₂)
    (cS cF : Nat.Partrec.Code) (hS : cS.eval 0 = Part.some (lensCode S))
    (hF : cF.eval 0 = Part.some (lensCode (fiberFlat F))) :
    (skewCode cS cF).eval 0 = Part.some (lensCode (skewWorldFin S F)) := by
  have hp : Nat.Partrec.Code.eval (Nat.Partrec.Code.pair cS cF) 0
      = Part.some (Nat.pair (lensCode S) (lensCode (fiberFlat F))) := by
    change Nat.pair <$> _ <*> _ = _
    rw [hS, hF]; simp [Seq.seq]
  rw [skewCode, eval_comp_some hp, eval_skewBuilder, skewTableFn_eq]

/-- **Skew products are cheap when their ingredients are.** The base rule's code and the fiber
rule's code, plus the absolute constant `elen skewBuilder + 6` — one fixed builder and the
assembly's opcodes, independent of the two worlds and of `n₁`, `n₂`.

This is `KE_prodWorldFin_le`'s statement with the fiber allowed to read the base: coupling one
cheap rule to another cheap rule, even one-directionally, cannot make the pair expensive to
describe. It is the load-bearing half of the fiber construction's price, because a skew world on
`n₁ · n₂` states has a table of that length and no bound stated in the table's own currency would
mean anything. -/
theorem KE_skewWorldFin_le (S : Fin n₁ → Fin n₁) (F : Fin n₁ → Fin n₂ → Fin n₂)
    (cS cF : Nat.Partrec.Code) (hS : cS.eval 0 = Part.some (lensCode S))
    (hF : cF.eval 0 = Part.some (lensCode (fiberFlat F))) :
    KE (lensCode (skewWorldFin S F)) ≤ elen cS + elen cF + (elen skewBuilder + 6) := by
  have hle := KE_le (c := skewCode cS cF) (eval_skewCode S F cS cF hS hF)
  rw [elen_skewCode] at hle
  omega

end Skew

/-! ## Evolution in the fiber

One deterministic generation of variation and selection, driven by the base coordinate. A
**population** is `P` slots holding candidate codewords from `Fin C`; a generation mutates every
slot by the base-driven, slot-indexed mutation and then selects the fittest mutant, which is copied
out to the whole population. Slot-indexed mutation is what regenerates diversity at the next step,
so this is a working `(1, P)` selection scheme rather than a fixed point.

Nothing here is claimed to converge. These are the definitions the pricing theorem instantiates;
the dynamics' behaviour is exactly what `fiber_emergence_pricing` imports as a hypothesis. -/

section Evolution

variable {n₁ P C : ℕ}

/-- A **population**: `P` slots, each holding a candidate codeword. -/
abbrev Pop (P C : ℕ) := Fin P → Fin C

/-- **The fittest member of a population**, by a left-to-right fold that keeps the incumbent on
ties. Deterministic, and total on a nonempty population. -/
def fittest [NeZero P] (fit : Fin C → ℕ) (p : Pop P C) : Fin C :=
  (List.finRange P).foldl (fun c i => if fit c < fit (p i) then p i else c) (p 0)

/-- **One generation** ([Inevitability] §6, "variation and selection"): vary, then select. Every
slot is mutated by its own base-driven mutation, the mutants are scored, and the fittest is copied
out — variation and selection in a single deterministic step. -/
def gaGen [NeZero P] (fit : Fin C → ℕ) (vary : Fin P → Fin C → Fin C) (p : Pop P C) : Pop P C :=
  fun _ => fittest fit fun i => vary i (p i)

/-- **Predictive fitness against the observed base transition** ([Inevitability] §6). A candidate
codeword is read as a hypothesis about the base rule via a fixed decoding `dec`; it scores at a base
state exactly when the rule it encodes predicts where the base actually goes. This is the fitness
the construction is about — selection on prediction of `x ↦ S x`, not on an extrinsic objective. -/
def predFit (S : Fin n₁ → Fin n₁) (dec : Fin C → Fin n₁ → Fin n₁) (x : Fin n₁) (c : Fin C) : ℕ :=
  if dec c x = S x then 1 else 0

/-- **The evolutionary fiber step**, transported onto the numeral carrier `Fin (C ^ P)` the tables
index: unpack the population, run one generation at the current base state's fitness and mutation,
pack it back. -/
def evoFiber [NeZero P] (fit : Fin n₁ → Fin C → ℕ) (vary : Fin n₁ → Fin P → Fin C → Fin C) :
    Fin n₁ → Fin (C ^ P) → Fin (C ^ P) :=
  fun x y => finFunctionFinEquiv (gaGen (fit x) (vary x) (finFunctionFinEquiv.symm y))

/-- **The evolving host**: a skew product whose base runs `S` and whose fiber runs one generation of
the population per base step. Its state count is `n₁ · C ^ P`, exponential in the population size,
which is why only the composed code prices it. -/
def evoWorld [NeZero P] (S : Fin n₁ → Fin n₁) (fit : Fin n₁ → Fin C → ℕ)
    (vary : Fin n₁ → Fin P → Fin C → Fin C) : Fin (n₁ * C ^ P) → Fin (n₁ * C ^ P) :=
  skewWorldFin S (evoFiber fit vary)

/-- **The fittest reading** ([Inevitability] §6, "with the fittest reading as the guest"): decode
the population out of the fiber coordinate and hand back its currently fittest codeword, scored at
the current base state. This is the candidate guest — the frame whose carried entropy the pricing
theorem bounds. -/
def fittestFrame (P : ℕ) [NeZero P] (fit : Fin n₁ → Fin C → ℕ) : Fin (n₁ * C ^ P) → Fin C :=
  fun p => fittest (fit (finProdFinEquiv.symm p).1)
    (finFunctionFinEquiv.symm (finProdFinEquiv.symm p).2)

/-! ### The convergence hypothesis is satisfiable

`fiber_emergence_pricing` imports its convergence as a hypothesis, and a hypothesis nobody has
exhibited an instance of makes a theorem worth nothing. The lemmas below discharge that worry
without touching the real question: at an **evolutionary fixed point** — variation switched off, so
selection has nothing left to act on — a uniform population sits still forever and the fittest
reading hands back its codeword, whatever the fitness. The hypothesis therefore holds, for arbitrary
`fit`, on that configuration.

This is a satisfiability witness and nothing more. It exhibits the *settled* state the hypothesis
describes; it says nothing about whether selection under real variation reaches such a state, which
is the whole of the open problem. -/

/-- A uniform population is its own fittest member: with every slot holding the same codeword the
fold never moves off it, on any fitness. -/
theorem fittest_const (P : ℕ) [NeZero P] (fit : Fin C → ℕ) (c : Fin C) :
    fittest fit (fun _ : Fin P => c) = c := by
  rw [fittest]
  generalize (List.finRange P) = l
  induction l with
  | nil => rfl
  | cons i l ih => simpa using ih

/-- **Variation off, uniform population: an evolutionary fixed point.** Selection copies the fittest
mutant out to every slot, and with no mutation the mutants *are* the population, so a uniform
population reproduces itself — at every base state, on any fitness. -/
theorem evoFiber_const (P : ℕ) [NeZero P] (fit : Fin n₁ → Fin C → ℕ) (x : Fin n₁) (c : Fin C) :
    evoFiber (P := P) fit (fun _ _ d => d) x (finFunctionFinEquiv fun _ : Fin P => c)
      = finFunctionFinEquiv fun _ : Fin P => c := by
  have hgen : gaGen (fit x) (fun (_ : Fin P) (d : Fin C) => d) (fun _ => c) = fun _ => c := by
    funext i
    exact fittest_const P (fit x) c
  simp [evoFiber, hgen]

/-- The fixed point survives iteration: the base runs on, the fiber stands still. -/
theorem iterate_evoWorld_const (P : ℕ) [NeZero P] (S : Fin n₁ → Fin n₁) (fit : Fin n₁ → Fin C → ℕ)
    (t : ℕ) (x : Fin n₁) (c : Fin C) :
    (evoWorld (P := P) S fit fun _ _ d => d)^[t]
        (finProdFinEquiv (x, finFunctionFinEquiv fun _ : Fin P => c))
      = finProdFinEquiv (S^[t] x, finFunctionFinEquiv fun _ : Fin P => c) := by
  have hstep : ∀ y : Fin n₁, (evoWorld (P := P) S fit fun _ _ d => d)
      (finProdFinEquiv (y, finFunctionFinEquiv fun _ : Fin P => c))
      = finProdFinEquiv (S y, finFunctionFinEquiv fun _ : Fin P => c) := by
    intro y
    rw [evoWorld, skewWorldFin_apply, evoFiber_const]
  induction t generalizing x with
  | zero => rfl
  | succ t ih =>
      rw [Function.iterate_succ_apply, hstep, ih, ← Function.iterate_succ_apply]

/-- The frame reads a uniform population's codeword straight back. -/
theorem fittestFrame_const (P : ℕ) [NeZero P] (fit : Fin n₁ → Fin C → ℕ) (x : Fin n₁) (c : Fin C) :
    fittestFrame P fit (finProdFinEquiv (x, finFunctionFinEquiv fun _ : Fin P => c)) = c := by
  rw [fittestFrame]
  simp [fittest_const]

/-- **The imported hypothesis is satisfiable.** On the variation-free dynamics every codeword is
read off its own uniform population, which the world leaves untouched, so the frame is surjective
after any number of steps — the hypothesis `fiber_emergence_pricing` takes, met on a settled
configuration and for arbitrary fitness. `fiber_emergence_pricing` is therefore not vacuous. -/
theorem surjective_fittestFrame_of_fixed (P : ℕ) [NeZero P] (S : Fin n₁ → Fin n₁)
    (fit : Fin n₁ → Fin C → ℕ) (hn₁ : 0 < n₁) :
    Function.Surjective fun s =>
      fittestFrame P fit ((evoWorld (P := P) S fit fun _ _ d => d)^[n₁ * C ^ P] s) := by
  intro c
  exact ⟨finProdFinEquiv (⟨0, hn₁⟩, finFunctionFinEquiv fun _ : Fin P => c),
    by simp only [iterate_evoWorld_const, fittestFrame_const]⟩

/-! ### The pricing assembly -/

/-- **The evolving fiber's guest, priced** ([Inevitability] §6) — the skew-product construction
assembled onto `PersistenceCapacity.emergence`.

Given a base rule `S` with a code, the evolutionary fiber step with a code, the fittest-reading
frame with a code, and — as a **named, imported hypothesis** — that flowing into the recurrent core
leaves the frame reading a full `Fin C`-valued model, the fittest reading is:

* a guest that **carries its model from every initial state**, co-moving with the recurrent rule;
  and
* **owned** at `elen cS + elen cF + elen cθ + O(1)` — the base rule, the evolutionary rule, the
  frame, and an absolute constant — so the world's uniform entropic capacity at that budget is at
  least the guest's carried entropy.

The price is the content. The host has `n₁ · C ^ P` states, so its own table is exponential in the
population; the bound is affordable only because the world enters through `skewCode` — the base
rule's code and the fiber rule's code composed into one fixed builder — rather than as a loaded
table. Nothing in the budget scales with the state count.

The surjectivity hypothesis is where the evolutionary content sits, and it is imported wholesale.
It says the population has settled on a faithful reading of the core; that selection by predictive
fitness in fact converges to such a reading, and from which initial states, is not addressed
here. -/
theorem fiber_emergence_pricing [NeZero P] (S : Fin n₁ → Fin n₁) (fit : Fin n₁ → Fin C → ℕ)
    (vary : Fin n₁ → Fin P → Fin C → Fin C) (cS cF cθ : Nat.Partrec.Code)
    (hconv : Function.Surjective fun s =>
      fittestFrame P fit ((evoWorld S fit vary)^[n₁ * C ^ P] s))
    (hS : cS.eval 0 = Part.some (lensCode S))
    (hF : cF.eval 0 = Part.some (lensCode (fiberFlat (evoFiber fit vary))))
    (hθ : cθ.eval 0 = Part.some (lensCode (fittestFrame P fit))) :
    Carries (evoWorld S fit vary) (emergeLens (evoWorld S fit vary) (fittestFrame P fit)) ∧
    Nat.card ↥(orbit (Perm ↥(core (evoWorld S fit vary)))
        (coreLens (evoWorld S fit vary)
          (emergeLens (evoWorld S fit vary) (fittestFrame P fit) 0)))
      ≤ CbHue (evoWorld S fit vary)
          (elen cS + elen cF + elen cθ + (elen emergeBuilder + elen skewBuilder + 36)) := by
  have hU : (skewCode cS cF).eval 0 = Part.some (lensCode (evoWorld S fit vary)) :=
    eval_skewCode S (evoFiber fit vary) cS cF hS hF
  obtain ⟨hcar, hprice⟩ :=
    emergence (evoWorld S fit vary) (fittestFrame P fit) (skewCode cS cF) cθ hconv hU hθ
  refine ⟨hcar, hprice.trans (CbHue_mono _ ?_)⟩
  rw [elen_skewCode]
  omega

/-- The same assembly with the fitness fixed to **predictive fitness against the base transition**:
candidates are hypotheses about `S`, scored by whether they predict where the base actually goes. -/
theorem fiber_emergence_pricing_predictive [NeZero P] (S : Fin n₁ → Fin n₁)
    (dec : Fin C → Fin n₁ → Fin n₁) (vary : Fin n₁ → Fin P → Fin C → Fin C)
    (cS cF cθ : Nat.Partrec.Code)
    (hconv : Function.Surjective fun s =>
      fittestFrame P (predFit S dec) ((evoWorld S (predFit S dec) vary)^[n₁ * C ^ P] s))
    (hS : cS.eval 0 = Part.some (lensCode S))
    (hF : cF.eval 0 = Part.some (lensCode (fiberFlat (evoFiber (predFit S dec) vary))))
    (hθ : cθ.eval 0 = Part.some (lensCode (fittestFrame P (predFit S dec)))) :
    Carries (evoWorld S (predFit S dec) vary)
        (emergeLens (evoWorld S (predFit S dec) vary) (fittestFrame P (predFit S dec))) ∧
    Nat.card ↥(orbit (Perm ↥(core (evoWorld S (predFit S dec) vary)))
        (coreLens (evoWorld S (predFit S dec) vary)
          (emergeLens (evoWorld S (predFit S dec) vary) (fittestFrame P (predFit S dec)) 0)))
      ≤ CbHue (evoWorld S (predFit S dec) vary)
          (elen cS + elen cF + elen cθ + (elen emergeBuilder + elen skewBuilder + 36)) :=
  fiber_emergence_pricing S (predFit S dec) vary cS cF cθ hconv hS hF hθ

end Evolution

end SkewFiber
