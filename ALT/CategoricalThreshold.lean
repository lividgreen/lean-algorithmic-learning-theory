/-
Copyright (c) 2026 Mykola Palamarchuk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mykola Palamarchuk
-/
import ALT.RealizabilityRecursor
import ALT.CapacityLayer
import ALT.GodelInternalization
import ALT.GodelThreshold

-- Formal-check file, not Mathlib-destined: opt out of the house-style linters.
set_option linter.style.header false
set_option linter.style.longLine false

/-!
# Theorem 6.2 as ONE machine-checked theorem on the genuine carrier (FV-15)

Provenance: [Decoupling] §6.1 (Definition 6.1, Theorem 6.2) and
§6.3 (the represent-but-cannot-derive consequence). This file closes the seam recorded at
Theorem 6.2 ("Theorem 6.2's *statement* … is assembled at paper level; no single Lean theorem
asserts it"): it bundles the three previously-separate machine-checked constituents into ONE
statement on the genuine realizability carrier `Asm`.

The constituents (all already axiom-clean):
* **Definition 6.1, one carrier** — `RealizabilityRecursor.ReflectiveAsm` (FV-13): the genuine
  Cartesian-closed realizability category `Asm` (FV-12) carrying the bounded recursor as an
  *object* of depth `> g`. `reflectiveAsm_satisfiable_depth` below generalizes FV-13's
  `reflectiveAsm_satisfiable` (which hard-coded `depth = g+1`) to an arbitrary working depth
  `> g`, so the recursor object can sit at the checker's working budget `M_chk`.
* **Theorem 6.2 capacity** — `CapacityLayer.recursorAsm_fitsIn` (FV-14) ∘
  `GodelInternalization.capacity_bound` (FV-8): the recursor object of working depth `M_chk ≤ g²`
  **fits in the explicit linear capacity `capacity n = 2n`** work bits (`n = ⌈log₂(g+1)⌉`).
* **§6.3 consequence** — `RealizabilityRecursor.reflectiveAsm_representsUnderivableTruth` (FV-13):
  under imported incompleteness for the subsystem's theory at `g`, that genuine reflective object
  **represents a sentence that is true-but-underivable** in the internal logic.

## Corollary 6.4 and the membership condition
`hostsAt` stratifies the threshold by working-memory budget (§6.4). `ReflectiveWithin` — the last
section — states the threshold itself as a capacity-indexed **membership condition**, in the form
[Inevitability] §2 Definition 2.1 asks for: a reflective object at the demanded working depth whose
recursor fits the budget. That predicate, unlike the un-capacitated `ReflectiveAsm` (satisfiable for
every `gTS`, FV-13), **can fail** — `not_reflectiveWithin_below_sentence_size` — and is reached
exactly at the capacity of Theorem 6.2 (`reflectiveWithin_at_capacity`).

## Boundary (the one paper-level residue)
This is the categorical/logical content of Theorem 6.2 on the genuine realizability CCC carrier.
What stays paper-level is **only** the *concrete* bitstring layout — that an actual decoupled
subsystem's `Rep(S)` is realized with its objects laid out as bitstrings in `{0,1}^{|s_work|}`.
The category, the recursor object, the capacity arithmetic, and the consequence are all checked
here. Gödel's first incompleteness theorem remains the imported black box
(`GodelThreshold.Incompleteness`), as everywhere in §6.

`ReflectiveWithin` inherits that same residue and adds no other: its Cartesian-closed conjuncts are
`Asm`'s ambient universal properties, and the capacity filtration enters through FV-14's `FitsIn`,
per §4.3's demarcation — the Cartesian-closed shape is ambient, and what a finite budget can fail is
*hosting*.
-/

namespace CategoricalThreshold

open RealizabilityRecursor RealizabilityCCC ParameterizedNNO CategoryTheory

/-- **Definition 6.1 on one carrier, at an arbitrary working depth.** Generalizes FV-13's
`reflectiveAsm_satisfiable` (`depth = gTS + 1`) to any `depth = d > gTS`, so the recursor object
can be placed at the checker's working budget `M_chk` rather than only at the indexing budget.
Every conjunct is about the SAME Cartesian-closed realizability category `Asm` (FV-12); the
recursor object `recursorAsm d` carries `zero`/`succ` as genuine `Asm`-morphisms equal (pointwise,
`rfl`) to the §5 `ParamNNO` structure maps `cyclicParamNNO d`. -/
def reflectiveAsm_satisfiable_depth (gTS d : ℕ) (h : gTS < d) : ReflectiveAsm gTS where
  terminal A := trackable_toTerminal A
  fst A B := ⟨leftCode, fst_tracks A B⟩
  snd A B := ⟨rightCode, snd_tracks A B⟩
  eval_tracks A B := ev_tracks A B
  exp_univ _ _ _ gmor := exp_universal gmor
  depth := d
  depth_gt := h
  zero := zeroMor d
  succ := succMor d
  orbit := cyclicParamNNO d
  orbit_depth := rfl
  succ_eq _ := rfl
  zero_eq := rfl

/-- **Theorem 6.2 (Categorical threshold), as one machine-checked theorem on the genuine carrier.**
For a theory of Gödel size `g` and a proof-code working budget `M_chk` with `g < M_chk ≤ g²`
(the concrete degree-2 budget; write `n := ⌈log₂(g+1)⌉` for the size of the Gödel sentence),
there is a genuine **reflective object** `R` of the realizability CCC `Asm` (Definition 6.1: the
Cartesian-closed universal properties together with a bounded-recursor object) such that:

* **(reflective)** `R : ReflectiveAsm g` — one categorical object that is Cartesian closed AND a
  bounded recursor of working depth `> g` (FV-12/FV-13);
* **(working depth)** `R.depth = M_chk` — the recursor object sits at the checker's working budget;
* **(capacity, Theorem 6.2)** the recursor object `FitsIn` the explicit linear capacity
  `capacity n = 2n` work bits (FV-8 `capacity_bound` ∘ FV-14 `recursorAsm_fitsIn`);
* **(§6.3 consequence)** under imported incompleteness at `g`, `R` represents a sentence that is
  true and underivable in the internal logic (FV-13 `reflectiveAsm_representsUnderivableTruth`).

`Incompleteness` is the imported Gödel black box (§6.2). The only paper-level residue is the
concrete `{0,1}^{|s_work|}` bitstring layout (see the module boundary note). -/
theorem categorical_threshold
    {Sentence : Type*} (gnum : Sentence → ℕ) (Derivable True_ : Sentence → Prop)
    (g Mchk : ℕ) (hidx : g < Mchk) (hpoly : Mchk ≤ g ^ 2) :
    ∃ R : ReflectiveAsm g,
      R.depth = Mchk ∧
      CapacityLayer.FitsIn (recursorAsm R.depth)
        (GodelInternalization.capacity (Nat.clog 2 (g + 1))) ∧
      (GodelThreshold.Incompleteness gnum Derivable True_ g →
        ∃ M, GodelThreshold.RepresentsUnderivableTruth gnum Derivable True_ M) := by
  refine ⟨reflectiveAsm_satisfiable_depth g Mchk hidx, rfl, ?_, ?_⟩
  · -- capacity: the recursor object of working depth M_chk ≤ g² fits in capacity n = 2n bits
    -- `R.depth` is `Mchk` definitionally; `change` rewrites to the reduced form.
    change CapacityLayer.FitsIn (recursorAsm Mchk)
      (GodelInternalization.capacity (Nat.clog 2 (g + 1)))
    exact CapacityLayer.recursorAsm_fitsIn Mchk _ (GodelInternalization.capacity_bound g Mchk hpoly)
  · -- §6.3 consequence: under imported incompleteness, represents an underivable truth
    intro hInc
    exact reflectiveAsm_representsUnderivableTruth gnum Derivable True_ g
      (reflectiveAsm_satisfiable_depth g Mchk hidx) hInc

/-! ### Corollary 6.4 (Capacity stratification of the categorical threshold, [Decoupling] §6.4)

A subsystem with `w` work bits **hosts** the Gödel-decision recursor for a theory of Gödel size `g`
exactly when `w` meets the linear capacity `2n`, `n := ⌈log₂(g+1)⌉`. This stratifies §6's threshold
by working-memory budget: the property is monotone in `w`, is entered precisely at capacity `2n`,
and is excluded below `n`. -/

/-- [Decoupling] §6.4 (Corollary 6.4): a subsystem with `w` work bits **hosts** the categorical threshold
for a theory of Gödel size `g` when its budget covers the linear capacity `capacity n = 2n`,
`n := ⌈log₂(g+1)⌉` (the size of the Gödel sentence). -/
def hostsAt (w g : ℕ) : Prop := GodelInternalization.capacity (Nat.clog 2 (g + 1)) ≤ w

/-- **Monotone in the work budget**: more work memory only helps. -/
theorem hostsAt_mono {w w' g : ℕ} (h : w ≤ w') : hostsAt w g → hostsAt w' g :=
  fun hw => le_trans hw h

/-- **Entered at capacity**: the threshold is met exactly once the budget reaches `capacity n = 2n`. -/
theorem hostsAt_enters (g : ℕ) : hostsAt (GodelInternalization.capacity (Nat.clog 2 (g + 1))) g :=
  le_refl _

/-- **Excluded below `n`**: a budget under the Gödel-sentence size `n = ⌈log₂(g+1)⌉` cannot host the
threshold — indeed the capacity is the strictly larger `2n`, so `w < n` fails already. -/
theorem hostsAt_excludes {w g : ℕ} (h : w < Nat.clog 2 (g + 1)) : ¬ hostsAt w g := by
  intro hh
  simp only [hostsAt, GodelInternalization.capacity] at hh
  omega

/-- **Corollary 6.4, the delivered object.** Once `w` hosts the threshold (`hostsAt w g`) and the
proof-code budget satisfies `g < M_chk ≤ g²`, the genuine FV-15 object of Theorem 6.2 is realized at
budget `w`: a reflective object `R` of the realizability CCC `Asm`, of working depth `M_chk`, whose
bounded-recursor object `FitsIn`s the `w` work bits (by capacity monotonicity from the linear `2n`),
and which — under imported incompleteness at `g` — represents a true-but-underivable sentence. -/
theorem hostsAt_threshold
    {Sentence : Type*} (gnum : Sentence → ℕ) (Derivable True_ : Sentence → Prop)
    {w g Mchk : ℕ} (h : hostsAt w g) (h1 : g < Mchk) (h2 : Mchk ≤ g ^ 2) :
    ∃ R : ReflectiveAsm g,
      R.depth = Mchk ∧
      CapacityLayer.FitsIn (recursorAsm R.depth) w ∧
      (GodelThreshold.Incompleteness gnum Derivable True_ g →
        ∃ M, GodelThreshold.RepresentsUnderivableTruth gnum Derivable True_ M) := by
  obtain ⟨R, hdepth, hfits, hcons⟩ := categorical_threshold gnum Derivable True_ g Mchk h1 h2
  exact ⟨R, hdepth, hfits.mono h, hcons⟩

/-! ### The threshold as a capacity-indexed MEMBERSHIP condition ([Inevitability] §2, Def. 2.1)

`hostsAt` above stratifies the threshold by budget, but it is a bare inequality on `w`: no object
appears in it. `ReflectiveWithin` below is the membership condition itself — *there is* a reflective
object at the working depth Definition 2.1 demands, and it fits the budget.

The distinction matters because the un-capacitated predicates cannot fail. `ReflectiveAsm gTS` is
inhabited for every `gTS` (FV-13 `reflectiveAsm_satisfiable`), and so is its arbitrary-depth
generalization `reflectiveAsm_satisfiable_depth`; a threshold predicate built from the categorical
data alone therefore certifies nothing about a *budgeted* subsystem. Adding the FV-14 capacity
conjunct is what makes the predicate refutable: `not_reflectiveWithin_below_sentence_size` is the
vacuity guard, and it fails exactly where §6.4's `hostsAt_excludes` does — below the Gödel
sentence's own size. -/

/-- **The reflective threshold within a work budget of `w` bits** ([Inevitability] §2 Def. 2.1, over
[Decoupling] §6.1 Definition 6.1). The subsystem reaches the threshold for an internalized
theory of Gödel size `gTS` when there is a reflective object `R` of the realizability CCC `Asm`
(FV-13: the Cartesian-closed universal properties together with a bounded-recursor object) such that

* **working depth** — `gTS ^ 2 ≤ R.depth`, Definition 2.1's `M_chk ≥ poly(g(T_S))` at the degree-2
  representative §6.1 fixes; the **indexing** demand `M_idx ≥ g(T_S)` comes free from `R.depth_gt`,
  the one number `R.depth` carrying both budgets (so `M_idx ≤ M_chk` holds by construction);
* **capacity** — the recursor object `FitsIn` the `w` work bits (FV-14): "Cartesian closed up to
  capacity" read as *hosting*, per §4.3's demarcation that the Cartesian-closed shape is ambient to
  `Asm` while what a finite budget can fail is which objects it holds.

Both clauses are tied to the SAME witness `R`; neither is a free-floating existential. Unlike the
un-capacitated `ReflectiveAsm`, this predicate can fail — see
`not_reflectiveWithin_below_sentence_size`, `ReflectiveWithin.mono` and
`reflectiveWithin_at_capacity` for the boundary, the monotonicity and the entry point. -/
def ReflectiveWithin (w gTS : ℕ) : Prop :=
  ∃ R : ReflectiveAsm gTS,
    gTS ^ 2 ≤ R.depth ∧ CapacityLayer.FitsIn (recursorAsm R.depth) w

/-- **The vacuity guard: below the Gödel sentence's own size the threshold is not reached.** A work
budget `w < n = ⌈log₂(g(T_S)+1)⌉` hosts at most `2 ^ w < g(T_S) + 1` distinct values, while any
witness carries a recursor object of `R.depth + 1 ≥ g(T_S) + 2` of them (`R.depth_gt`). So
`ReflectiveWithin w g(T_S)` fails outright — the same exclusion §6.4's `hostsAt_excludes` records
for the budget inequality, now for the membership condition.

This is the clause the capacity conjunct buys: drop `FitsIn` from `ReflectiveWithin` and the
statement becomes FALSE at every `g(T_S)`, since `reflectiveAsm_satisfiable_depth` inhabits the
remaining depth clause at, for instance, `depth = g(T_S) ^ 2 + 1`. No side condition on `g(T_S)` is
needed: at `g(T_S) = 0` the hypothesis `w < ⌈log₂ 1⌉ = 0` is already vacuous. -/
theorem not_reflectiveWithin_below_sentence_size {w gTS : ℕ}
    (h : w < Nat.clog 2 (gTS + 1)) : ¬ ReflectiveWithin w gTS := by
  rintro ⟨R, -, -, hcard⟩
  have hcarrier : Nat.card (recursorAsm R.depth).carrier = R.depth + 1 := by
    simp [Nat.card_eq_fintype_card, ZMod.card]
  rw [hcarrier] at hcard
  have hdepth : gTS < R.depth := R.depth_gt
  have hpow : 2 ^ w < gTS + 1 := (Nat.lt_clog_iff_pow_lt (by norm_num)).mp h
  omega

/-- **Monotone in the work budget**: a threshold reached within `w` bits is reached within any
larger budget — the membership counterpart of `hostsAt_mono`, by `CapacityLayer.FitsIn.mono` on
the same witness. -/
theorem ReflectiveWithin.mono {w w' gTS : ℕ}
    (h : ReflectiveWithin w gTS) (hw : w ≤ w') : ReflectiveWithin w' gTS := by
  obtain ⟨R, hdepth, hfits⟩ := h
  exact ⟨R, hdepth, hfits.mono hw⟩

/-- **The threshold IS reached at [Decoupling] Theorem 6.2's capacity.** At `2 ≤ g(T_S)` the budget
`capacity n = 2n` (`n = ⌈log₂(g(T_S)+1)⌉`) suffices: the witness is the reflective object of working
depth exactly `g(T_S) ^ 2` — Definition 2.1's own demand, met with equality — and its recursor fits
by FV-8 `capacity_bound` composed with FV-14 `recursorAsm_fitsIn`, precisely the capacity step of
FV-15.

The side condition is tight at the same boundary as the rest of this development: `g(T_S) < g(T_S)²`
fails at `g(T_S) ∈ {0, 1}`, so the depth demand and `ReflectiveAsm`'s `depth_gt` are incompatible
there. Note the statement mentions no `Sentence`/`gnum` parameters — membership is a condition on
the pair `(w, g(T_S))` alone; the §6.3 consequence is `categorical_threshold`'s business. -/
theorem reflectiveWithin_at_capacity {gTS : ℕ} (hg : 2 ≤ gTS) :
    ReflectiveWithin (GodelInternalization.capacity (Nat.clog 2 (gTS + 1))) gTS := by
  have hidx : gTS < gTS ^ 2 := by nlinarith
  refine ⟨reflectiveAsm_satisfiable_depth gTS (gTS ^ 2) hidx, le_refl _, ?_⟩
  change CapacityLayer.FitsIn (recursorAsm (gTS ^ 2))
    (GodelInternalization.capacity (Nat.clog 2 (gTS + 1)))
  exact CapacityLayer.recursorAsm_fitsIn _ _
    (GodelInternalization.capacity_bound gTS (gTS ^ 2) (le_refl _))

/-! ### The reflection ladder's capacity bound ([Inevitability] §6 Remark 6.4)

A fixed host's reflection ladder appends, at each rung, a Gödel sentence for its own
currently-internalized theory; Remark 6.4 bounds how many such rungs a host of a given work-memory
budget can climb. `ReflectiveWithin w g` already states the per-rung threshold at Gödel size `g`;
`ladder_card_le` is the counting step Remark 6.4 draws from it, a pigeonhole over
`not_reflectiveWithin_below_sentence_size` and nothing more.

Not built here: the identification of a ladder rung's guest with a decoupled subsystem carrying an
internal theory ([Inevitability] §2's own modelling step), and Remark 6.4's two entropy-side
clauses (the one-point guest's maximality, the coarsening/bijective dichotomy). Both stay
paper-level. -/

/-- **The ladder's capacity bound** ([Inevitability] §6 Remark 6.4; over [Decoupling] Proposition
5.4, machine-checked there as FV-8 `prop_5_4`, in its budget-indexed form
`not_reflectiveWithin_below_sentence_size` above). A finite set of Gödel numbers, each reaching the
threshold within a common work budget of `w` bits, has at most `2 ^ w` elements: distinct elements
of `s` are distinct Gödel numbers, and none of them can reach `2 ^ w` or above.

Inherits [Decoupling] §5.4's representation condition rather than sidestepping it:
`ReflectiveWithin` is stated for the §5.3 orbit-value indexing, so this count is
representation-relative in exactly the sense Proposition 5.4 is, not a
representation-independent bound. -/
theorem ladder_card_le {w : ℕ} (s : Finset ℕ)
    (hs : ∀ g ∈ s, ReflectiveWithin w g) : s.card ≤ 2 ^ w := by
  have hsub : s ⊆ Finset.range (2 ^ w) := by
    intro g hg
    rw [Finset.mem_range]
    by_contra hge
    have hlt : w < Nat.clog 2 (g + 1) := (Nat.lt_clog_iff_pow_lt (by norm_num)).mpr (by omega)
    exact not_reflectiveWithin_below_sentence_size hlt (hs g hg)
  calc s.card ≤ (Finset.range (2 ^ w)).card := Finset.card_le_card hsub
    _ = 2 ^ w := Finset.card_range _

/-- **Non-vacuity**: `ladder_card_le`'s hypothesis is satisfiable, not merely vacuous on the empty
set. At Gödel size `2` the threshold is reached exactly at capacity
(`reflectiveWithin_at_capacity`), so the singleton `{2}` is a genuine one-rung instance of the
hypothesis. -/
theorem ladder_card_le_nonvacuous :
    ∀ g ∈ ({2} : Finset ℕ),
      ReflectiveWithin (GodelInternalization.capacity (Nat.clog 2 3)) g := by
  intro g hg
  simp only [Finset.mem_singleton] at hg
  subst hg
  exact reflectiveWithin_at_capacity (le_refl 2)

end CategoricalThreshold
