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
* `predFrame` — **the base-reading frame**: the fittest candidate's *prediction of the base*, rather
  than its codeword. Its codomain is the base's own state space, so the values it takes are supplied
  by the base coordinate and not by the population.
* `not_surjective_fittestFrame_of_converged` / `surjective_predFrame_of_converged` — **the two
  frames separate by theorem**. One fixed fittest codeword from every initial state refutes the
  codeword frame's hypothesis once `2 ≤ C`, and leaves the base-reading frame's standing.
* `surjective_predFrame_of_faithful` / `predFrame_emergence_pricing` — the base-reading frame's own
  satisfiability witness, and the pricing assembly restated over it at the same constant.
* `powFiber` / `powFibBuilder` / `KE_skewWorldFin_powFiber_le` — **[Inevitability] Theorem 6.6(vi),
  "P copies"**: `P` copies of one fiber, product over the fiber coordinate per base index, cost the
  *one-copy* fiber's code plus `O (log n₁ + log P)` for the two loaded numerals — a `P`-fold larger
  population is a `log P`-more expensive description, not a `P`-times-more expensive one.

## Scope

The frame's hypothesis is imported, not proved, and it is a **coverage** condition rather than a
convergence one. `fiber_emergence_pricing` takes `Function.Surjective (fun s => θ (U^[N] s))`: as
the *initial state* ranges over the state space, the reading must take every value in the frame's
codomain — which is what makes it a full model worth pricing at all.

For `fittestFrame`, whose codomain is the candidate alphabet, coverage and settling compete. A
population that had converged on one codeword from every initial state would make that reading
constant, and a constant map is not surjective once `2 ≤ C`. So the codeword frame can draw its
coverage only from the initial condition — which is exactly what `surjective_fittestFrame_of_fixed`
does, by switching variation off. Proving that selection converges would not discharge that
hypothesis; it would refute it.

`predFrame` moves the coverage off the population and onto the base coordinate, which the fiber
reads but never writes. Settling then becomes compatible with the hypothesis instead of fatal to
it, so a convergence theorem for the fiber has somewhere to land. This file adds that frame; it
does not replace the other, and everything stated over `fittestFrame` stands unchanged.

Whether selection under real variation settles at all, and from which initial states, is untouched
here — as is the basin those initial states would form.

Two further gaps are deliberate and are not narrowed here. The base of this construction is a
finite endofunction on `Fin n₁`, carrying no measure and no mixing hypothesis; the mixing base and
its invariant measure are analytic objects that this finite, combinatorial layer does not host. And
the host here is of fixed size, so nothing about a *growing* host — code accreting on a frontier
while the written region stays fixed — is represented. This file is the pricing skeleton only.

`KE_skewWorldFin_powFiber_le` machine-checks the "P copies" half of [Inevitability] Theorem
6.6(vi)'s remaining step — the composite guest's code is `P` copies of one fiber's code, at the
stated price. The clause's other half, the decode (a bounded search over the copies), is a separate
construction addressed elsewhere, and is not touched by this file. Every other result here remains
combinatorial skeleton only, with no numbered result claimed machine-checked.
-/

namespace SkewFiber

open PersistenceCapacity Decoupling AdditiveComplexity CodeEvalLaws
open Equiv MulAction

-- `•` on the recurrent-core reading is the relabelling action `U • ℓ = ℓ ∘ U⁻¹`; the same local
-- instance `PersistenceCapacity.emergence` is stated under.
attribute [local instance] arrowAction

/-! ## The skew product, tabulated -/

section Skew

variable {n₁ n₂ : ℕ}

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

/-- **The base does not see the fiber, in one step.** Projecting a skew step onto the base
coordinate gives the base rule applied to the base coordinate — whatever the fiber rule did. -/
theorem base_skewWorldFin (S : Fin n₁ → Fin n₁) (F : Fin n₁ → Fin n₂ → Fin n₂)
    (p : Fin (n₁ * n₂)) :
    (finProdFinEquiv.symm (skewWorldFin S F p)).1 = S (finProdFinEquiv.symm p).1 := by
  rw [skewWorldFin, Equiv.symm_apply_apply]

/-- **…and not over a run either**: the base coordinate of the `t`-th iterate is the base rule's
`t`-th iterate at the base coordinate. The fiber is driven by the base and never feeds back, so a
skew run projects onto a base run exactly — which is what lets a frame reading the base coordinate
inherit the base rule's own coverage. -/
theorem base_iterate_skewWorldFin (S : Fin n₁ → Fin n₁) (F : Fin n₁ → Fin n₂ → Fin n₂) (t : ℕ)
    (p : Fin (n₁ * n₂)) :
    (finProdFinEquiv.symm ((skewWorldFin S F)^[t] p)).1 = S^[t] (finProdFinEquiv.symm p).1 := by
  induction t generalizing p with
  | zero => rfl
  | succ t ih =>
      rw [Function.iterate_succ_apply, ih, base_skewWorldFin, Function.iterate_succ_apply]

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

/-! ### The blockwise `P`-fold fiber ([Inevitability] Theorem 6.6(vi), "P copies")

The composite guest clause (vi) prices is `P` copies of one fiber over one base: the product acts
on the fiber coordinate only, per base index. `powFiber` self-composes `skewWorldFin`'s own fiber
argument along a fresh coordinate rather than along the clock. -/

/-- **`P` copies of one fiber, product over the fiber coordinate, per base index.** At `P = 0` the
fiber carrier is `Fin 1` and every base index maps the sole point to itself; at `P + 1` the low
`Fin n₂` copy runs `F` and the remaining `Fin (n₂ ^ P)` copies run one level down, woven by
`finProdFinEquiv` exactly as `skewWorldFin` weaves base and fiber. -/
def powFiber (F : Fin n₁ → Fin n₂ → Fin n₂) : (P : ℕ) → Fin n₁ → Fin (n₂ ^ P) → Fin (n₂ ^ P)
  | 0 => fun _ => id
  | P + 1 => fun i w =>
      finProdFinEquiv (powFiber F P i (finProdFinEquiv.symm w).1, F i (finProdFinEquiv.symm w).2)

/-- A table read back through its own range recovers itself. The reconstruction `powFibTable_one`
needs, at the base case where the accumulator table is trivial. -/
private theorem range_map_getD (l : List ℕ) :
    (List.range l.length).map (fun i => l.getD i 0) = l := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    rw [List.getElem_map, List.getElem_range]
    exact List.getD_eq_getElem l 0 h2

/-- **Weaving one more copy in**: entry `q` of the `P + 1`-copy table is the `P`-copy table's own
entry at the same base block, shifted by `n₂` (the width one more fiber copy adds) and combined with
the fresh copy's entry — `skewAppend`'s weave, replayed inside every base block rather than once
globally. `n₁` is carried explicitly: it is not recoverable from `Tk.length` and `T₁.length` alone
(`powFibTable`'s guard below exhibits two legal choices of `n₁` at the same table giving different
lengths after two weaves). -/
def fibProdAppend (n₁ : ℕ) (Tk T₁ : List ℕ) : List ℕ :=
  (List.range (n₁ * ((Tk.length / n₁) * (T₁.length / n₁)))).map fun q =>
    let wk := Tk.length / n₁
    let n₂ := T₁.length / n₁
    let i := q / (wk * n₂)
    let w₁ := (q % (wk * n₂)) / n₂
    let w₂ := q % n₂
    Tk.getD (i * wk + w₁) 0 * n₂ + T₁.getD (i * n₂ + w₂) 0

/-- **The `P`-copy composite table**, by iterating `fibProdAppend` from the trivial `P = 0` table (a
single point per base index, i.e. `n₁` zeros — `Fin (n₂ ^ 0) = Fin 1` has one element). -/
def powFibTable (n₁ : ℕ) (T₁ : List ℕ) (P : ℕ) : List ℕ :=
  Nat.rec (List.replicate n₁ 0) (fun _ IH => fibProdAppend n₁ IH T₁) P

/-- **`n₁` is load-bearing**: `[0,1,0,1]` is a legal fiber table both at `(n₁, n₂) = (2, 2)` and
at `(1, 4)`, and its `P = 2` powers differ in length — so `n₁` cannot be recovered from `T₁` and
must be carried, as `powFibTable` carries it. -/
example : (powFibTable 2 [0,1,0,1] 2).length ≠ (powFibTable 1 [0,1,0,1] 2).length := by decide

/-- **The grading check**: one copy is the table itself. -/
theorem powFibTable_one (n₁ : ℕ) (T₁ : List ℕ) (h : n₁ ∣ T₁.length) :
    powFibTable n₁ T₁ 1 = T₁ := by
  rcases Nat.eq_zero_or_pos n₁ with hn₁ | hn₁
  · subst hn₁
    have hT : T₁.length = 0 := Nat.zero_dvd.mp h
    simp [powFibTable, fibProdAppend, List.length_eq_zero_iff.mp hT]
  obtain ⟨n₂, hn₂⟩ := h
  have hwk : (List.replicate n₁ 0).length / n₁ = 1 := by
    rw [List.length_replicate, Nat.div_self hn₁]
  have hn₂' : T₁.length / n₁ = n₂ := by rw [hn₂, Nat.mul_div_cancel_left n₂ hn₁]
  change fibProdAppend n₁ (List.replicate n₁ 0) T₁ = T₁
  simp only [fibProdAppend, hwk, hn₂', one_mul, mul_one]
  rw [← hn₂]
  trans (List.range T₁.length).map (fun q => T₁.getD q 0)
  swap
  · exact range_map_getD T₁
  refine List.map_congr_left fun q hq => ?_
  have hqlt : q < n₁ * n₂ := by simpa [hn₂] using List.mem_range.mp hq
  have hn₂pos : 0 < n₂ := Nat.pos_of_ne_zero fun h0 => by simp [h0] at hqlt
  have hidiv : q / n₂ < n₁ := Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm] at hqlt)
  have hmod : q % n₂ / n₂ = 0 := Nat.div_eq_of_lt (Nat.mod_lt _ hn₂pos)
  have hqi : q / n₂ * n₂ + q % n₂ = q := Nat.div_add_mod' q n₂
  rw [hmod, Nat.add_zero, List.getD_replicate 0 hidiv, hqi, Nat.zero_mul, Nat.zero_add]

/-- A table over the trivial fiber `Fin 1` is all zeros: `Fin 1`'s sole value reads back as
`0`. -/
private theorem lensTable_const_zero {m : ℕ} (f : Fin m → Fin 1) :
    lensTable f = List.replicate m 0 := by
  have hf : (fun i : Fin m => (f i : ℕ)) = fun _ => 0 :=
    funext fun i => Fin.val_eq_zero (f i)
  rw [lensTable, hf, List.map_const', List.length_finRange]

/-- A `fiberFlat` table's entry at the flat index a base/fiber pair weaves to, read directly. -/
private theorem lensTable_getD_fiberFlat {n₁ n₂ : ℕ} (G : Fin n₁ → Fin n₂ → Fin n₂)
    (i : Fin n₁) (w : Fin n₂) :
    (lensTable (fiberFlat G)).getD ((i : ℕ) * n₂ + w) 0 = (G i w : ℕ) := by
  have hval : (i : ℕ) * n₂ + w = (finProdFinEquiv (i, w) : ℕ) := by
    rw [finProdFinEquiv_apply_val]; ring
  rw [hval, lensTable_getD _ (finProdFinEquiv (i, w)).isLt, fiberFlat_apply]

/-- **`powFiber`'s successor step, in raw values**: the new copy's contribution is read off the
low `n₂` bits and the accumulated `P` copies off the rest — `skewWorldFin`'s own weave, replayed on
the fiber coordinate. The unfolding is `rfl` (`Nat.pow`'s recursion equation is exactly
`finProdFinEquiv`'s domain-matching identity); the surrounding `congrArg`/`.trans` keep the proof at
the value level throughout, since `rw` on the underlying `Fin`-typed equation does not survive the
`n₂ ^ (P + 1)` vs `n₂ ^ P * n₂` mismatch under the tactic framework's reduced transparency. -/
private theorem powFiber_succ_val {n₁ n₂ : ℕ} (F : Fin n₁ → Fin n₂ → Fin n₂) (P : ℕ)
    (i : Fin n₁) (w : Fin (n₂ ^ (P + 1))) :
    (powFiber F (P + 1) i w : ℕ)
      = (F i w.modNat : ℕ) + n₂ * (powFiber F P i w.divNat : ℕ) := by
  have h : powFiber F (P + 1) i w = finProdFinEquiv (powFiber F P i w.divNat, F i w.modNat) := rfl
  exact (congrArg Fin.val h).trans (finProdFinEquiv_apply_val _)

/-- **The composite table is the iterated weave** ([Inevitability] Theorem 6.6(vi), "`P` copies"):
`powFiber`'s own table, built by `finProdFinEquiv` at every level, is exactly `fibProdAppend`
iterated `P` times from the trivial table — the argument of `lensTable_skewWorldFin`, replayed one
level down at each step. -/
theorem lensTable_powFiber (F : Fin n₁ → Fin n₂ → Fin n₂) (P : ℕ) :
    lensTable (fiberFlat (powFiber F P)) = powFibTable n₁ (lensTable (fiberFlat F)) P := by
  induction P with
  | zero =>
      simpa [pow_zero, mul_one, powFibTable] using lensTable_const_zero (fiberFlat (powFiber F 0))
  | succ P ih =>
      change lensTable (fiberFlat (powFiber F (P + 1)))
        = fibProdAppend n₁ (powFibTable n₁ (lensTable (fiberFlat F)) P) (lensTable (fiberFlat F))
      rw [← ih]
      rcases Nat.eq_zero_or_pos n₁ with hn₁ | hn₁
      · subst hn₁
        simp [fibProdAppend, lensTable]
      have hwk : (lensTable (fiberFlat (powFiber F P))).length / n₁ = n₂ ^ P := by
        rw [lensTable_length, Nat.mul_div_cancel_left _ hn₁]
      have hn2 : (lensTable (fiberFlat F)).length / n₁ = n₂ := by
        rw [lensTable_length, Nat.mul_div_cancel_left _ hn₁]
      simp only [fibProdAppend, hwk, hn2]
      rw [lensTable_range]
      refine List.map_congr_left fun q hq => ?_
      have hqlt : q < n₁ * n₂ ^ (P + 1) := List.mem_range.mp hq
      have hqlt2 : q < n₁ * (n₂ ^ P * n₂) := by rw [pow_succ] at hqlt; exact hqlt
      have hn2pos : 0 < n₂ := by
        rcases Nat.eq_zero_or_pos n₂ with h0 | h0
        · exact absurd hqlt2 (by simp [h0])
        · exact h0
      have hplen : 0 < n₂ ^ P * n₂ := Nat.mul_pos (pow_pos hn2pos P) hn2pos
      have hilt : q / (n₂ ^ P * n₂) < n₁ :=
        Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm n₁ (n₂ ^ P * n₂)] at hqlt2; exact hqlt2)
      have hrlt : q % (n₂ ^ P * n₂) < n₂ ^ P * n₂ := Nat.mod_lt _ hplen
      have hw1lt : q % (n₂ ^ P * n₂) / n₂ < n₂ ^ P :=
        Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm n₂ (n₂ ^ P)]; exact hrlt)
      have hw2lt : q % n₂ < n₂ := Nat.mod_lt _ hn2pos
      have hmm : q % (n₂ ^ P * n₂) % n₂ = q % n₂ :=
        Nat.mod_mod_of_dvd q ⟨n₂ ^ P, by ring⟩
      have hilt' : q / n₂ ^ (P + 1) < n₁ := Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm] at hqlt)
      have hrlt' : q % n₂ ^ (P + 1) < n₂ ^ (P + 1) := Nat.mod_lt _ (pow_pos hn2pos (P + 1))
      rw [dif_pos hqlt]
      have hidx' : (⟨q, hqlt⟩ : Fin (n₁ * n₂ ^ (P + 1)))
          = finProdFinEquiv (⟨q / n₂ ^ (P + 1), hilt'⟩, ⟨q % n₂ ^ (P + 1), hrlt'⟩) := by
        apply Fin.ext
        simp only [finProdFinEquiv_apply_val]
        exact (Nat.mod_add_div q (n₂ ^ (P + 1))).symm
      rw [hidx', fiberFlat_apply, powFiber_succ_val]
      have hival : (⟨q / n₂ ^ (P + 1), hilt'⟩ : Fin n₁) = ⟨q / (n₂ ^ P * n₂), hilt⟩ := by
        apply Fin.ext
        change q / n₂ ^ (P + 1) = q / (n₂ ^ P * n₂)
        rw [pow_succ]
      have hdival : (⟨q % n₂ ^ (P + 1), hrlt'⟩ : Fin (n₂ ^ (P + 1))).divNat
          = (⟨q % (n₂ ^ P * n₂) / n₂, hw1lt⟩ : Fin (n₂ ^ P)) := by
        apply Fin.ext
        change ((⟨q % n₂ ^ (P + 1), hrlt'⟩ : Fin (n₂ ^ (P + 1))).divNat : ℕ)
          = q % (n₂ ^ P * n₂) / n₂
        rw [Fin.coe_divNat]
        congr 1
      have hmodval : (⟨q % n₂ ^ (P + 1), hrlt'⟩ : Fin (n₂ ^ (P + 1))).modNat
          = (⟨q % n₂, hw2lt⟩ : Fin n₂) := by
        apply Fin.ext
        change ((⟨q % n₂ ^ (P + 1), hrlt'⟩ : Fin (n₂ ^ (P + 1))).modNat : ℕ) = q % n₂
        rw [Fin.coe_modNat, ← hmm]
        congr 1
      rw [hival, hdival, hmodval,
        lensTable_getD_fiberFlat (powFiber F P) ⟨q / (n₂ ^ P * n₂), hilt⟩
          ⟨q % (n₂ ^ P * n₂) / n₂, hw1lt⟩,
        lensTable_getD_fiberFlat F ⟨q / (n₂ ^ P * n₂), hilt⟩ ⟨q % n₂, hw2lt⟩]
      ring

/-! ### The builder: one fixed program that weaves any fiber table `P` times over itself -/

/-- `fibProdAppend` is primitive recursive in its base index, its accumulator table, and its
one-copy table — `n₁` is a loaded numeral, not a table, so it enters as plain `ℕ` data. -/
private theorem primrec_fibProdAppend :
    Primrec fun q : ℕ × List ℕ × List ℕ => fibProdAppend q.1 q.2.1 q.2.2 := by
  have hn1 : Primrec fun q : ℕ × List ℕ × List ℕ => q.1 := Primrec.fst
  have hTk : Primrec fun q : ℕ × List ℕ × List ℕ => q.2.1 := Primrec.fst.comp Primrec.snd
  have hT1 : Primrec fun q : ℕ × List ℕ × List ℕ => q.2.2 := Primrec.snd.comp Primrec.snd
  have hwk : Primrec fun q : ℕ × List ℕ × List ℕ => q.2.1.length / q.1 :=
    Primrec.nat_div.comp (Primrec.list_length.comp hTk) hn1
  have hn2 : Primrec fun q : ℕ × List ℕ × List ℕ => q.2.2.length / q.1 :=
    Primrec.nat_div.comp (Primrec.list_length.comp hT1) hn1
  refine Primrec.list_map
    (Primrec.list_range.comp (Primrec.nat_mul.comp hn1 (Primrec.nat_mul.comp hwk hn2))) ?_
  refine Primrec₂.mk ?_
  have hqfst : Primrec fun p : (ℕ × List ℕ × List ℕ) × ℕ => p.1 := Primrec.fst
  have hidx : Primrec fun p : (ℕ × List ℕ × List ℕ) × ℕ => p.2 := Primrec.snd
  have hwk' : Primrec fun p : (ℕ × List ℕ × List ℕ) × ℕ => p.1.2.1.length / p.1.1 := hwk.comp hqfst
  have hn2' : Primrec fun p : (ℕ × List ℕ × List ℕ) × ℕ => p.1.2.2.length / p.1.1 := hn2.comp hqfst
  have hwkn2 : Primrec fun p : (ℕ × List ℕ × List ℕ) × ℕ =>
      p.1.2.1.length / p.1.1 * (p.1.2.2.length / p.1.1) := Primrec.nat_mul.comp hwk' hn2'
  have hi : Primrec fun p : (ℕ × List ℕ × List ℕ) × ℕ =>
      p.2 / (p.1.2.1.length / p.1.1 * (p.1.2.2.length / p.1.1)) :=
    Primrec.nat_div.comp hidx hwkn2
  have hmodwkn2 : Primrec fun p : (ℕ × List ℕ × List ℕ) × ℕ =>
      p.2 % (p.1.2.1.length / p.1.1 * (p.1.2.2.length / p.1.1)) :=
    Primrec.nat_mod.comp hidx hwkn2
  have hw1 : Primrec fun p : (ℕ × List ℕ × List ℕ) × ℕ =>
      p.2 % (p.1.2.1.length / p.1.1 * (p.1.2.2.length / p.1.1)) / (p.1.2.2.length / p.1.1) :=
    Primrec.nat_div.comp hmodwkn2 hn2'
  have hw2 : Primrec fun p : (ℕ × List ℕ × List ℕ) × ℕ => p.2 % (p.1.2.2.length / p.1.1) :=
    Primrec.nat_mod.comp hidx hn2'
  have hiwk : Primrec fun p : (ℕ × List ℕ × List ℕ) × ℕ =>
      p.2 / (p.1.2.1.length / p.1.1 * (p.1.2.2.length / p.1.1)) * (p.1.2.1.length / p.1.1)
        + p.2 % (p.1.2.1.length / p.1.1 * (p.1.2.2.length / p.1.1)) / (p.1.2.2.length / p.1.1) :=
    Primrec.nat_add.comp (Primrec.nat_mul.comp hi hwk') hw1
  have hin2 : Primrec fun p : (ℕ × List ℕ × List ℕ) × ℕ =>
      p.2 / (p.1.2.1.length / p.1.1 * (p.1.2.2.length / p.1.1)) * (p.1.2.2.length / p.1.1)
        + p.2 % (p.1.2.2.length / p.1.1) :=
    Primrec.nat_add.comp (Primrec.nat_mul.comp hi hn2') hw2
  exact Primrec.nat_add.comp
    (Primrec.nat_mul.comp ((Primrec.list_getD 0).comp (hTk.comp hqfst) hiwk) hn2')
    ((Primrec.list_getD 0).comp (hT1.comp hqfst) hin2)

/-- **`powFibTable` is primitive recursive**, jointly in `n₁` (fixed across iterations) and `T₁`
(fixed across iterations), by `Nat.rec` on `P`. The two landed precedents for this shape are
`primrec_iterTable` and `primrec_ownIter`. -/
private theorem primrec_powFibTable :
    Primrec₂ fun (a : ℕ × List ℕ) (P : ℕ) => powFibTable a.1 a.2 P := by
  have hbase : Primrec fun a : ℕ × List ℕ => List.replicate a.1 0 :=
    (Primrec.list_map (Primrec.list_range.comp Primrec.fst) (Primrec.const 0).to₂).of_eq
      fun a => by rw [List.map_const', List.length_range]
  have hstep : Primrec₂ fun (a : ℕ × List ℕ) (p : ℕ × List ℕ) => fibProdAppend a.1 p.2 a.2 :=
    (primrec_fibProdAppend.comp
      (Primrec.pair (Primrec.fst.comp Primrec.fst) (Primrec.pair (Primrec.snd.comp Primrec.snd)
        (Primrec.snd.comp Primrec.fst)))).to₂
  exact (Primrec.nat_rec hbase hstep).of_eq fun a P => rfl

/-- **The `P`-fold fiber builder, from `⟨fiber table code, ⟨n₁, P⟩⟩`** — ONE fixed function, with
no size parameters loaded except the two raw numerals `n₁` and `P`. -/
private def powFibTableFn (p : ℕ) : ℕ :=
  Encodable.encode
    (powFibTable p.unpair.2.unpair.1
      ((Encodable.decode (α := List ℕ) p.unpair.1).getD []) p.unpair.2.unpair.2)

private theorem primrec_powFibTableFn : Primrec powFibTableFn := by
  have hdecT : Primrec fun p : ℕ => (Encodable.decode (α := List ℕ) p.unpair.1).getD [] :=
    Primrec.option_getD.comp
      (Primrec.decode.comp (Primrec.fst.comp Primrec.unpair)) (Primrec.const [])
  have hn1 : Primrec fun p : ℕ => p.unpair.2.unpair.1 :=
    Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))
  have hP : Primrec fun p : ℕ => p.unpair.2.unpair.2 :=
    Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))
  exact Primrec.encode.comp (primrec_powFibTable.comp (Primrec.pair hn1 hdecT) hP)

private theorem partrec_powFibTableFn : Nat.Partrec (fun p : ℕ => (powFibTableFn p : ℕ)) :=
  _root_.Partrec.nat_iff.mp (Primrec.to_comp primrec_powFibTableFn).partrec

/-- **The fixed `P`-fold builder code.** One program, independent of the fiber, of `n₁`, and
of `P`. -/
noncomputable def powFibBuilder : Nat.Partrec.Code :=
  Classical.choose (Nat.Partrec.Code.exists_code.mp partrec_powFibTableFn)

private theorem eval_powFibBuilder (p : ℕ) :
    Nat.Partrec.Code.eval powFibBuilder p = Part.some (powFibTableFn p) := by
  have h := congrFun (Classical.choose_spec
    (Nat.Partrec.Code.exists_code.mp partrec_powFibTableFn)) p
  simpa [powFibBuilder] using h

/-- **The builder is correct**: on `⟨the one-copy fiber table's code, ⟨n₁, P⟩⟩` it outputs the
`P`-fold fiber's encoded table. -/
theorem powFibTableFn_eq (F : Fin n₁ → Fin n₂ → Fin n₂) (P : ℕ) :
    powFibTableFn (Nat.pair (lensCode (fiberFlat F)) (Nat.pair n₁ P))
      = lensCode (fiberFlat (powFiber F P)) := by
  rw [powFibTableFn]
  simp only [Nat.unpair_pair, decode_lensCode]
  rw [← lensTable_powFiber]
  rfl

/-! ### The price: `P` copies cost the one-copy code plus `O (log n₁ + log P)`

`n₁` and `P` are loaded as numerals via `bconst`, not as tables — the composition shape
(`comp powFibBuilder (pair cF (pair (bconst n₁) (bconst P)))`), never the load-the-value shape. -/

/-- **The `P`-fold fiber's cheap code**: run the one-copy fiber's code, load `n₁` and `P` as binary
numerals, hand all three to the fixed builder. -/
noncomputable def powFibCode (cF : Nat.Partrec.Code) (n₁ P : ℕ) : Nat.Partrec.Code :=
  Nat.Partrec.Code.comp powFibBuilder
    (Nat.Partrec.Code.pair cF (Nat.Partrec.Code.pair (bconst n₁) (bconst P)))

/-- The composed code's length is the one-copy code's, plus `O (log n₁ + log P)` for the two
loaded numerals, plus one absolute constant. -/
theorem elen_powFibCode_le (cF : Nat.Partrec.Code) (n₁ P : ℕ) :
    elen (powFibCode cF n₁ P)
      ≤ elen cF + (15 + elen dbl) * (Nat.size n₁ + Nat.size P)
        + (elen powFibBuilder + 2 * (15 + elen dbl) + 9) := by
  rw [powFibCode, E_len_comp, E_len_pair, E_len_pair]
  have h1 := elen_bconst_le n₁
  have h2 := elen_bconst_le P
  have hsum : (15 + elen dbl) * Nat.size n₁ + (15 + elen dbl) * Nat.size P
      = (15 + elen dbl) * (Nat.size n₁ + Nat.size P) := by ring
  omega

/-- The composed code computes the `P`-fold fiber's table. -/
theorem eval_powFibCode (F : Fin n₁ → Fin n₂ → Fin n₂) (cF : Nat.Partrec.Code)
    (hF : cF.eval 0 = Part.some (lensCode (fiberFlat F))) (P : ℕ) :
    (powFibCode cF n₁ P).eval 0 = Part.some (lensCode (fiberFlat (powFiber F P))) := by
  have hpn : Nat.Partrec.Code.eval (Nat.Partrec.Code.pair (bconst n₁) (bconst P)) 0
      = Part.some (Nat.pair n₁ P) := by
    change Nat.pair <$> _ <*> _ = _
    rw [eval_bconst, eval_bconst]; simp [Seq.seq]
  have hp : Nat.Partrec.Code.eval
      (Nat.Partrec.Code.pair cF (Nat.Partrec.Code.pair (bconst n₁) (bconst P))) 0
      = Part.some (Nat.pair (lensCode (fiberFlat F)) (Nat.pair n₁ P)) := by
    change Nat.pair <$> _ <*> _ = _
    rw [hF, hpn]; simp [Seq.seq]
  rw [powFibCode, eval_comp_some hp, eval_powFibBuilder, powFibTableFn_eq]

/-- **`P` copies of a fiber cost one copy plus `O (log n₁ + log P)`** ([Inevitability] Theorem
6.6(vi), "P copies" — the theorem's one remaining paper-level step, save for the decode).

Assembled from `KE_skewWorldFin_le` with the fiber code replaced by `powFibCode cF n₁ P`: the base
rule's code, the *one-copy* fiber code, plus the two loaded numerals `n₁` and `P` at
`(15 + elen dbl) · (log n₁ + log P)`, plus an absolute constant independent of the world, of `n₁`,
of `n₂`, and of `P`.

`n₁` and `P` enter through `Nat.size` and nowhere else — a `P`-fold larger population is a
`log P`-more expensive description, not a `P`-times-more expensive one, because the composed code
*runs* the one-copy fiber's code `P` times over rather than carrying a `P`-fold table. This is the
"P copies" half of clause (vi); "and the decode" is `ALT/RedundantFiber.lean`'s construction and is
untouched here. -/
theorem KE_skewWorldFin_powFiber_le (S : Fin n₁ → Fin n₁) (F : Fin n₁ → Fin n₂ → Fin n₂)
    (cS cF : Nat.Partrec.Code) (hS : cS.eval 0 = Part.some (lensCode S))
    (hF : cF.eval 0 = Part.some (lensCode (fiberFlat F))) (P : ℕ) :
    KE (lensCode (skewWorldFin S (powFiber F P)))
      ≤ elen cS + elen cF + (15 + elen dbl) * (Nat.size n₁ + Nat.size P)
        + (elen skewBuilder + elen powFibBuilder + 2 * (15 + elen dbl) + 15) := by
  have hle := KE_skewWorldFin_le S (powFiber F P) cS (powFibCode cF n₁ P) hS
    (eval_powFibCode F cF hF P)
  have hb := elen_powFibCode_le cF n₁ P
  omega

set_option linter.style.longLine false in
/-- info: 'SkewFiber.KE_skewWorldFin_powFiber_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KE_skewWorldFin_powFiber_le

end Skew

/-! ## Evolution in the fiber

One deterministic generation of variation and selection, driven by the base coordinate. A
**population** is `P` slots holding candidate codewords from `Fin C`; a generation mutates every
slot by the base-driven, slot-indexed mutation and then selects the fittest mutant, which is copied
out to the whole population. Slot-indexed mutation is what regenerates diversity at the next step,
so this is a working `(1, P)` selection scheme rather than a fixed point.

Nothing here is claimed to converge. These are the definitions the pricing theorem instantiates;
what `fiber_emergence_pricing` imports as a hypothesis is not the dynamics' behaviour but the
coverage its frame achieves as the initial state varies. -/

section Evolution

variable {n₁ P C : ℕ}

/-- A **population**: `P` slots, each holding a candidate codeword. -/
abbrev Pop (P C : ℕ) := Fin P → Fin C

/-- **The fittest member of a population**, by a left-to-right fold that keeps the incumbent on
ties. Deterministic, and total on a nonempty population. -/
def fittest [NeZero P] (fit : Fin C → ℕ) (p : Pop P C) : Fin C :=
  (List.finRange P).foldl (fun c i => if fit c < fit (p i) then p i else c) (p 0)

/-- The fold underlying `fittest` never drops below its starting fitness, and never below any slot
it has already visited: the fitness invariant one induction step of `fittest_ge`/`fittest_mem`
needs. -/
private theorem foldl_fittest_ge (fit : Fin C → ℕ) (p : Pop P C) (l : List (Fin P)) (c : Fin C) :
    fit c ≤ fit (l.foldl (fun c i => if fit c < fit (p i) then p i else c) c) ∧
      ∀ j ∈ l, fit (p j) ≤ fit (l.foldl (fun c i => if fit c < fit (p i) then p i else c) c) := by
  induction l generalizing c with
  | nil => simp
  | cons i l ih =>
      simp only [List.foldl_cons, List.mem_cons]
      by_cases hcond : fit c < fit (p i)
      · rw [if_pos hcond]
        obtain ⟨hge, hall⟩ := ih (p i)
        refine ⟨hcond.le.trans hge, fun j hj => ?_⟩
        rcases hj with rfl | hj
        · exact hge
        · exact hall j hj
      · rw [if_neg hcond]
        obtain ⟨hge, hall⟩ := ih c
        refine ⟨hge, fun j hj => ?_⟩
        rcases hj with rfl | hj
        · exact (not_lt.mp hcond).trans hge
        · exact hall j hj

/-- **`fittest` attains the population's maximum fitness**: no slot beats the fold's winner. -/
theorem fittest_ge [NeZero P] (fit : Fin C → ℕ) (p : Pop P C) (i : Fin P) :
    fit (p i) ≤ fit (fittest fit p) :=
  (foldl_fittest_ge fit p (List.finRange P) (p 0)).2 i (List.mem_finRange i)

/-- The fold underlying `fittest` never leaves the population: starting from a slot's value, it
stays a slot's value. -/
private theorem foldl_fittest_mem (fit : Fin C → ℕ) (p : Pop P C) (l : List (Fin P)) (i₀ : Fin P) :
    ∃ i, l.foldl (fun c i => if fit c < fit (p i) then p i else c) (p i₀) = p i := by
  induction l generalizing i₀ with
  | nil => exact ⟨i₀, rfl⟩
  | cons i l ih =>
      simp only [List.foldl_cons]
      split
      · exact ih i
      · exact ih i₀

/-- **`fittest` returns one of the population's own members**: the fold never invents a
codeword. -/
theorem fittest_mem [NeZero P] (fit : Fin C → ℕ) (p : Pop P C) : ∃ i, fittest fit p = p i :=
  foldl_fittest_mem fit p (List.finRange P) 0

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

/-! ### The coverage hypothesis is satisfiable

`fiber_emergence_pricing` imports its coverage as a hypothesis, and a hypothesis nobody has
exhibited an instance of makes a theorem worth nothing. The lemmas below discharge that worry
without touching the real question: at an **evolutionary fixed point** — variation switched off, so
selection has nothing left to act on — a uniform population sits still forever and the fittest
reading hands back its codeword, whatever the fitness. Distinct initial populations therefore sit
on distinct codewords, and the hypothesis holds for arbitrary `fit`.

This is a satisfiability witness and nothing more. It is also the plainest reading of what the
hypothesis asks for: the coverage comes from the initial condition and from nothing the dynamics
did. It could not come from the dynamics — a reading that settled on one fixed codeword from every
initial state is constant, hence not surjective once `2 ≤ C`, which the next section proves. -/

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
after any number of steps — the hypothesis `fiber_emergence_pricing` takes, met for arbitrary
fitness. `fiber_emergence_pricing` is therefore not vacuous. The whole of the coverage is carried
by the initial condition: each state stands still on its own codeword, and it is ranging over them
that reaches every value. -/
theorem surjective_fittestFrame_of_fixed (P : ℕ) [NeZero P] (S : Fin n₁ → Fin n₁)
    (fit : Fin n₁ → Fin C → ℕ) (hn₁ : 0 < n₁) :
    Function.Surjective fun s =>
      fittestFrame P fit ((evoWorld (P := P) S fit fun _ _ d => d)^[n₁ * C ^ P] s) := by
  intro c
  exact ⟨finProdFinEquiv (⟨0, hn₁⟩, finFunctionFinEquiv fun _ : Fin P => c),
    by simp only [iterate_evoWorld_const, fittestFrame_const]⟩

/-! ### The base-reading frame

`fittestFrame` reads the fittest *codeword*, so its codomain is the candidate alphabet and its
coverage can only ever come from the initial population. The frame below reads instead what the
fittest candidate *predicts the base will do*: decode the fittest codeword into a rule and apply
that rule to the current base state. Its codomain is the base's own state space, so the values it
takes are supplied by the base coordinate, which the fiber never feeds back into.

The two frames then separate by theorem. A population that has settled on one codeword from every
initial state makes `fittestFrame` constant, and a constant map into `Fin C` is not surjective once
`2 ≤ C` (`not_surjective_fittestFrame_of_converged`). The very same settling leaves `predFrame`'s
coverage intact, provided the codeword settled on decodes to the base rule and that rule is
surjective (`surjective_predFrame_of_converged`). Coverage and settling compete for one frame and
coexist for the other.

Nothing here proves that the fiber settles. That question is untouched — the point is that a
theorem about it would now have somewhere to land. -/

/-- **The base-reading frame** ([Inevitability] §6): read the fittest candidate's *prediction of
the base*. The fittest codeword is decoded into a rule by `dec` and that rule is applied to the
current base state, so the frame's value is a base state rather than a codeword.

This is `fittestFrame` composed with the decoding and evaluated at the base coordinate. The change
that matters is the codomain: coverage of `Fin n₁` is a question about the base coordinate, where a
surjective base rule supplies it outright, and not about which codewords the population happens to
hold. -/
def predFrame (P : ℕ) [NeZero P] (fit : Fin n₁ → Fin C → ℕ) (dec : Fin C → Fin n₁ → Fin n₁) :
    Fin (n₁ * C ^ P) → Fin n₁ :=
  fun p => dec (fittestFrame P fit p) (finProdFinEquiv.symm p).1

/-- The evolving host's base coordinate runs the base rule alone, for any variation. -/
theorem base_iterate_evoWorld [NeZero P] (S : Fin n₁ → Fin n₁) (fit : Fin n₁ → Fin C → ℕ)
    (vary : Fin n₁ → Fin P → Fin C → Fin C) (t : ℕ) (s : Fin (n₁ * C ^ P)) :
    (finProdFinEquiv.symm ((evoWorld S fit vary)^[t] s)).1 = S^[t] (finProdFinEquiv.symm s).1 :=
  base_iterate_skewWorldFin S (evoFiber fit vary) t s

/-- **Settling refutes the codeword frame's hypothesis.** Suppose the fittest reading after a full
state-count of steps is one fixed codeword from every initial state — the conclusion shape a
convergence theorem for the fiber would have. With at least two candidate codewords that reading is
constant and therefore not surjective, so it fails exactly the hypothesis
`fiber_emergence_pricing` imports.

The hypothesis is a **coverage** condition on the frame's codomain as the initial state varies, not
a convergence one, and this is the two pulling apart: coverage of `Fin C` by a codeword-valued
frame has to be charged to the initial conditions, and a dynamics that erased their differences
would take it away. -/
theorem not_surjective_fittestFrame_of_converged [NeZero P] (S : Fin n₁ → Fin n₁)
    (fit : Fin n₁ → Fin C → ℕ) (vary : Fin n₁ → Fin P → Fin C → Fin C) (c₀ : Fin C) (hC : 2 ≤ C)
    (hconv : ∀ s, fittestFrame P fit ((evoWorld S fit vary)^[n₁ * C ^ P] s) = c₀) :
    ¬ Function.Surjective fun s =>
        fittestFrame P fit ((evoWorld S fit vary)^[n₁ * C ^ P] s) := by
  intro hsurj
  haveI : Nontrivial (Fin C) := Fin.nontrivial_iff_two_le.mpr hC
  obtain ⟨c₁, hc₁⟩ := exists_ne c₀
  obtain ⟨s, hs⟩ := hsurj c₁
  exact hc₁ (hs.symm.trans (hconv s))

/-- **The base-reading frame's hypothesis is satisfiable**, on the same variation-free dynamics
`surjective_fittestFrame_of_fixed` uses. If some codeword decodes to the base rule itself and that
rule is surjective, then starting from the uniform population on that codeword the fiber stands
still, the frame's prediction is the base rule's own next state, and the reading after `N` steps is
`S^[N + 1]` of the initial base coordinate — surjective as a composite of surjections.

The coverage now comes from the base coordinate. The population contributes only the *identity* of
the rule being applied, and it contributes the same one from every initial state used here. -/
theorem surjective_predFrame_of_faithful (P : ℕ) [NeZero P] (S : Fin n₁ → Fin n₁)
    (fit : Fin n₁ → Fin C → ℕ) (dec : Fin C → Fin n₁ → Fin n₁) (c₀ : Fin C) (hdec : dec c₀ = S)
    (hS : Function.Surjective S) :
    Function.Surjective fun s =>
      predFrame P fit dec ((evoWorld (P := P) S fit fun _ _ d => d)^[n₁ * C ^ P] s) := by
  intro z
  obtain ⟨x, hx⟩ := hS.iterate (n₁ * C ^ P + 1) z
  rw [Function.iterate_succ_apply'] at hx
  refine ⟨finProdFinEquiv (x, finFunctionFinEquiv fun _ : Fin P => c₀), ?_⟩
  simp only [predFrame, iterate_evoWorld_const, fittestFrame_const, Equiv.symm_apply_apply]
  rw [hdec]
  exact hx

/-- **Settling is compatible with the base-reading frame's hypothesis.** Under the very
convergence hypothesis that refutes `fittestFrame`'s coverage — one fixed codeword from every
initial state — `predFrame`'s coverage holds, provided the settled codeword decodes to the base
rule and that rule is surjective.

Together with `not_surjective_fittestFrame_of_converged` this separates the two frames by theorem
rather than by argument. The same antecedent kills one hypothesis and leaves the other standing, so
a convergence result for the fiber would refute the pricing assembly stated over the codeword frame
and discharge the one stated over the base-reading frame. Which frame the assembly is stated over
is therefore not a presentational choice.

Note what is doing the work: the fiber never feeds back into the base
(`base_iterate_evoWorld`), so the base coordinate sweeps its whole state space regardless of what
the population does. -/
theorem surjective_predFrame_of_converged [NeZero P] (S : Fin n₁ → Fin n₁)
    (fit : Fin n₁ → Fin C → ℕ) (dec : Fin C → Fin n₁ → Fin n₁)
    (vary : Fin n₁ → Fin P → Fin C → Fin C) (c₀ : Fin C) (hdec : dec c₀ = S)
    (hS : Function.Surjective S)
    (hconv : ∀ s, fittestFrame P fit ((evoWorld S fit vary)^[n₁ * C ^ P] s) = c₀) :
    Function.Surjective fun s =>
      predFrame P fit dec ((evoWorld S fit vary)^[n₁ * C ^ P] s) := by
  intro z
  obtain ⟨x, hx⟩ := hS.iterate (n₁ * C ^ P + 1) z
  rw [Function.iterate_succ_apply'] at hx
  refine ⟨finProdFinEquiv (x, finFunctionFinEquiv fun _ : Fin P => c₀), ?_⟩
  simp only [predFrame, hconv, base_iterate_evoWorld, Equiv.symm_apply_apply]
  rw [hdec]
  exact hx

/-! #### The settled antecedent is inhabited

The two theorems above are implications, and an implication whose antecedent nothing meets
separates nothing. A variation rule that overwrites every slot with one codeword produces exactly
the settled shape they hypothesise, so the separation below is a fact about a single dynamics
rather than a pair of conditionals.

It is a witness for the hypothesis' *shape* and not for selection: the codeword is imposed by the
variation rather than found by the fitness, which is not even consulted. Whether predictive fitness
reaches such a state, and from where, is exactly what this file does not address. -/

/-- Variation that ignores the incumbent and writes one codeword makes the fiber uniform on it in a
single generation, whatever the population was and whatever the fitness says. -/
theorem evoFiber_const_vary [NeZero P] (fit : Fin n₁ → Fin C → ℕ) (c₀ : Fin C) (x : Fin n₁)
    (y : Fin (C ^ P)) :
    evoFiber (P := P) fit (fun _ _ _ => c₀) x y = finFunctionFinEquiv fun _ : Fin P => c₀ := by
  have hgen : gaGen (fit x) (fun (_ : Fin P) (_ : Fin C) => c₀)
      (finFunctionFinEquiv.symm y) = fun _ : Fin P => c₀ := by
    funext i
    exact fittest_const P (fit x) c₀
  rw [evoFiber, hgen]

/-- One step of the overwriting dynamics: the base advances and the fiber lands on the uniform
population, from any state at all. -/
theorem evoWorld_const_vary [NeZero P] (S : Fin n₁ → Fin n₁) (fit : Fin n₁ → Fin C → ℕ)
    (c₀ : Fin C) (p : Fin (n₁ * C ^ P)) :
    (evoWorld S fit fun _ _ _ => c₀) p
      = finProdFinEquiv
          (S (finProdFinEquiv.symm p).1, finFunctionFinEquiv fun _ : Fin P => c₀) := by
  rw [evoWorld, skewWorldFin, evoFiber_const_vary]

/-- **The settled shape is reached from every initial state, after a single step.** -/
theorem fittestFrame_iterate_const_vary [NeZero P] (S : Fin n₁ → Fin n₁)
    (fit : Fin n₁ → Fin C → ℕ) (c₀ : Fin C) (t : ℕ) (s : Fin (n₁ * C ^ P)) :
    fittestFrame P fit ((evoWorld S fit fun _ _ _ => c₀)^[t + 1] s) = c₀ := by
  rw [Function.iterate_succ_apply', evoWorld_const_vary, fittestFrame_const]

/-- The same at the run length the pricing assembly reads at, which is positive once the base has a
state to be in. -/
theorem fittestFrame_const_vary [NeZero P] (S : Fin n₁ → Fin n₁) (fit : Fin n₁ → Fin C → ℕ)
    (c₀ : Fin C) (hn₁ : 0 < n₁) (s : Fin (n₁ * C ^ P)) :
    fittestFrame P fit ((evoWorld S fit fun _ _ _ => c₀)^[n₁ * C ^ P] s) = c₀ := by
  have hpos : 0 < n₁ * C ^ P := Nat.mul_pos hn₁ (Nat.pow_pos c₀.pos)
  have h := fittestFrame_iterate_const_vary S fit c₀ (n₁ * C ^ P - 1) s
  rwa [Nat.sub_add_cancel hpos] at h

/-- **The two frames separate on one dynamics.** With every slot overwritten by a single codeword
that decodes to a surjective base rule, the codeword frame's coverage hypothesis **fails** and the
base-reading frame's **holds** — the same world, the same run length, the same fitness.

So the choice of frame is not presentational. `fiber_emergence_pricing` is unavailable here and
`predFrame_emergence_pricing` applies, and what makes the difference is where each frame's values
come from: the population, whose differences this dynamics has erased, or the base coordinate,
which the fiber cannot touch. -/
theorem frames_separate_of_settled [NeZero P] (S : Fin n₁ → Fin n₁) (fit : Fin n₁ → Fin C → ℕ)
    (dec : Fin C → Fin n₁ → Fin n₁) (c₀ : Fin C) (hn₁ : 0 < n₁) (hC : 2 ≤ C) (hdec : dec c₀ = S)
    (hS : Function.Surjective S) :
    (¬ Function.Surjective fun s =>
        fittestFrame P fit ((evoWorld S fit fun _ _ _ => c₀)^[n₁ * C ^ P] s)) ∧
      Function.Surjective fun s =>
        predFrame P fit dec ((evoWorld S fit fun _ _ _ => c₀)^[n₁ * C ^ P] s) :=
  ⟨not_surjective_fittestFrame_of_converged S fit _ c₀ hC (fittestFrame_const_vary S fit c₀ hn₁),
    surjective_predFrame_of_converged S fit dec _ c₀ hdec hS
      (fittestFrame_const_vary S fit c₀ hn₁)⟩

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
It is a **coverage** condition: as the initial state ranges over the state space, the fittest
reading must take every value in `Fin C`. It does not say the population has settled — settling on
one codeword from every initial state would refute it outright once `2 ≤ C`
(`not_surjective_fittestFrame_of_converged`). So what would discharge it is a change of frame
(`predFrame`, and `predFrame_emergence_pricing` below), not a convergence theorem. -/
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

/-- **The evolving fiber's guest, priced through the base-reading frame** ([Inevitability] §6).
`fiber_emergence_pricing` with `θ := predFrame P fit dec`: same host, same composed code, same
constant, and the frame swapped.

That it transports at all is the reusable fact. `skewCode`'s pricing and
`PersistenceCapacity.emergence` are parametric in the fiber rule and in the frame, so the assembly
never depended on reading a codeword; only the imported coverage hypothesis did. The guest here is
`Fin n₁`-valued rather than `Fin C`-valued — it carries the fittest candidate's prediction of the
base — and the budget is unchanged at `elen cS + elen cF + elen cθ + O(1)`.

What the swap buys is where the hypothesis can be met: `surjective_predFrame_of_converged`
discharges it from a settled population, which `not_surjective_fittestFrame_of_converged` shows is
incompatible with the codeword frame's version. That the fiber does settle is still not proved
anywhere here. -/
theorem predFrame_emergence_pricing [NeZero P] (S : Fin n₁ → Fin n₁) (fit : Fin n₁ → Fin C → ℕ)
    (dec : Fin C → Fin n₁ → Fin n₁) (vary : Fin n₁ → Fin P → Fin C → Fin C)
    (cS cF cθ : Nat.Partrec.Code)
    (hcov : Function.Surjective fun s =>
      predFrame P fit dec ((evoWorld S fit vary)^[n₁ * C ^ P] s))
    (hS : cS.eval 0 = Part.some (lensCode S))
    (hF : cF.eval 0 = Part.some (lensCode (fiberFlat (evoFiber fit vary))))
    (hθ : cθ.eval 0 = Part.some (lensCode (predFrame P fit dec))) :
    Carries (evoWorld S fit vary) (emergeLens (evoWorld S fit vary) (predFrame P fit dec)) ∧
    Nat.card ↥(orbit (Perm ↥(core (evoWorld S fit vary)))
        (coreLens (evoWorld S fit vary)
          (emergeLens (evoWorld S fit vary) (predFrame P fit dec) 0)))
      ≤ CbHue (evoWorld S fit vary)
          (elen cS + elen cF + elen cθ + (elen emergeBuilder + elen skewBuilder + 36)) := by
  have hU : (skewCode cS cF).eval 0 = Part.some (lensCode (evoWorld S fit vary)) :=
    eval_skewCode S (evoFiber fit vary) cS cF hS hF
  obtain ⟨hcar, hprice⟩ :=
    emergence (evoWorld S fit vary) (predFrame P fit dec) (skewCode cS cF) cθ hcov hU hθ
  refine ⟨hcar, hprice.trans (CbHue_mono _ ?_)⟩
  rw [elen_skewCode]
  omega

end Evolution

end SkewFiber
