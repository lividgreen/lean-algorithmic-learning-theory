/-
Copyright (c) 2026 Mykola Palamarchuk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mykola Palamarchuk
-/
module

public import ALT.DerivedStages
public import Mathlib.Data.Finsupp.Basic
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic.Abel

-- Formal-check file, not Mathlib-destined: opt out of the house-style header linter.
set_option linter.style.header false

/-!
# The extreme-tap rules: at least half the derived-stage cap, and the exact width

([Guests] §7 Definition 7.1's derived presentation; grades B1 and B2)

The two extreme-tap linear rules on finitely-supported `ℤ →₀ ZMod 2` configurations — elementary
tables `90` and `150` at radius one, `(U s) i = s (i - 1) ± s i ± s (i + 1)` — are additive and
injective, spread their support by exactly one cell per step at each end, and never stay inside a
fixed region past finitely many steps.
On the world derived (`DerivedStages.derivedStages`) from the full state set of an `n`-cell start
region, the left-edge seeds (those with a `1` in cell `0`) form an antichain of size `2 ^ (n - 1)`
under `Reaches`, giving a memory width of at least half `DerivedStages.memWidth_derivedStages_le`'s
cap (`[grade B1]`).

The exact width (`[grade B2]`) is a root count: `rootSet` is the region-supported states with no
`U`-preimage in the region's open interior, and `MemoryWidth.memWidth_eq_encard_of_rootSet` (the
generic root-set width lemma) applies since every region-supported state is reached from a root
(`rootSet_cover`) and the roots are pairwise `Reaches`-incomparable (`rootSet_antichain`) — neither
argument consumes a notion of "component". At `rule90`/`rule150`, the root set's own cardinality
closes in addition form (`rootSet_encard_add` / `rootSet_encard_add_rule150`): the region's `2 ^ n`
states split exactly into the roots and the images of the interior's `2 ^ (n - 2) - 1` nonzero
states. `rootSet_cover` and `rootSet_antichain` are generic in the update, consuming exactly the
hypotheses `memWidth_derived_eq_encard_rootSet` and `rootSet_encard_add_of_hyps` below package.

The endpoint-move generalization replaces the exact spread's shared constant `1` at each end by
two independent integers `a`/`b`: `rule90`/`rule150` and the four non-additive tables below all
still instantiate at `(a, b) = (1, 1)`, while `rule170`/`rule240` instantiate at `(1, -1)` and
`(-1, 1)`. The root COUNT (`rootSet_encard_add_of_hyps`) holds at every `(a, b)`, `(0, 0)`
included; the exact WIDTH (`memWidth_derived_eq_encard_rootSet`, hence `rootSet_cover`) needs
`(a, b) ≠ (0, 0)` — `guard_id_rootSet_load_bearing` is the witness that separates the two claims,
at the identity update.

A local table `f : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2` with `f 0 0 0 = 0` (quiescence) becomes a
radius-one rule via `tableRule`; ONE-SIDED PERMUTIVITY of `f`, in its solved (additive) form, is
what a downward or upward induction from beyond the support uses to recover a state from its image
— on the finitely-supported configurations of the line, this is a CLASSICAL route to injectivity,
not a new argument. Four non-additive elementary tables (`rule30`, `rule210`, `rule86`, `rule154`)
meet the class's hypotheses this way and so share `rule90`/`rule150`'s exact width, and a guard
(`rule170`) shows quiescence and permutivity alone do not suffice to pin the class-level spread
lemmas — `rule170`'s own exact spread is `(1, -1)`, not `(1, 1)`, and its width and count are now
proved at that pair rather than left open.

## Main results

* `rule90` / `rule150` — the two rules, each a sum of `Finsupp.mapDomain` shifts.
* `rule90_apply` / `rule150_apply` — the pointwise formula each rule computes.
* `rule90_injective` / `rule150_injective` — additive with trivial kernel: a nonzero state's
  leftmost cell forces a nonzero value one cell further left after one step.
* `rule90_region_exit` / `rule150_region_exit` — every nonzero orbit eventually leaves any fixed
  finite region, the leftmost support index strictly decreasing at every step.
* `rule90_support_min'_spread` / `rule90_support_max'_spread` (and the `rule150` twins) — the exact
  spread: the leftmost cell moves left by one, the rightmost right by one, at every nonzero state.
* `regionStates` — the states supported on an `n`-cell region, `{0, …, n - 1}`.
* `memWidth_rule90_derived_ge` / `memWidth_rule150_derived_ge` — **grade B1**: on the world derived
  from `regionStates n`, the memory width is at least `2 ^ (n - 1)`.
* `interiorStates` / `rootSet` — the nonzero states region-supported with a region-supported
  `U`-image, and the region-supported states with no `U`-preimage among them; at `(a, b) = (1, 1)`
  `interiorStates` is exactly the old `[1, n - 2]` window (`interiorStates_eq_window`).
* `memWidth_rule90_derived_eq` / `memWidth_rule150_derived_eq` — **grade B2, the capstones**: the
  memory width equals `(rootSet U n).encard` exactly, on the world derived from `regionStates n`.
* `rootSet_encard_add` / `rootSet_encard_add_rule150` — **grade B2, the count**: at each rule,
  `(rootSet U n).encard + 2 ^ (n - 2) = 2 ^ n + 1`, in addition form (`ℕ∞` subtraction is
  truncated) — the paper's closed form `2 ^ n - 2 ^ (n - 2) + 1` is this equation's own elementary
  restatement.
* `memWidth_derived_eq_encard_rootSet` / `rootSet_encard_add_of_hyps` — the capstone and the count,
  generic in the update AND in the two endpoint-move spread constants `a`/`b`: the capstones and
  counts above are their one-line corollaries.
* `interiorStates_eq_window` — the interior is exactly the window `[a⁺, n - 1 - b⁺]` (`x⁺` for
  `max x 0`), under the trivial kernel and the two exact spread identities.
* `hUspread_sign_nonneg` — the two spread constants always sum to something non-negative,
  `0 ≤ a + b`, forced by the exact spread identities alone.
* `guard_id_rootSet_load_bearing` — **the identity guard**: at `(a, b) = (0, 0)` the count still
  holds (`rootSet id n` has one element, matching `rootSet_encard_add_of_hyps` at `m = 0`) but the
  width does not — the retained profile is the whole region, `2 ^ n`, not `1`.
* `tableRule` / `tableRule_apply` — a local table `f` with `f 0 0 0 = 0`, as a radius-one rule.
* `tableRule_injective_of_leftPermutive` / `tableRule_injective_of_rightPermutive` — one-sided
  permutivity in solved form (`f a b c = a + g b c` / `f a b c = c + h a b`) plus quiescence gives
  injectivity on the finitely-supported configurations of the line, at any `g`/`h` whatsoever.
* `leftPermutive_support_max'_spread` / `rightPermutive_support_min'_spread` — one exact spread
  direction is free from quiescence alone; `leftPermutive_support_min'_spread` /
  `rightPermutive_support_max'_spread` — the other needs one further bit on `g`/`h`.
* `rule30` / `rule210` / `rule86` / `rule154` — four non-additive elementary tables meeting the
  class's hypotheses, each with its own capstone and count
  (`memWidth_rule30_derived_eq`/`rootSet_encard_add_rule30` and the three twins).
* `memWidth_rule30_derived_eq_rule90` — rule `30`'s derived-stage width from an `n`-cell region is
  exactly rule `90`'s, at `2 ≤ n`.
* `rule170` / `guard_rule170_max'_spread_load_bearing` — **the guard**: table `170`'s pure shift is
  quiescent and (right-)permutive, and `rightPermutive_support_max'_spread`'s CLASS-LEVEL exact
  right-spread hypothesis still fails there — permutivity and quiescence alone do not pin it.
* `rule170_support_min'_spread` / `rule170_support_max'_spread` and the capstone/count
  `memWidth_rule170_derived_eq` / `rootSet_encard_add_rule170` — the guard's own table, at its
  TRUE spread pair `(1, -1)` rather than the class-level lemma the guard shows insufficient.
* `rule240` — the mirror pure LEFT shift, `(a, b) = (-1, 1)`, with its own capstone/count
  `memWidth_rule240_derived_eq` / `rootSet_encard_add_rule240`: the only instantiation in this file
  exercising `rootSet_cover`/`rootSet_antichain`'s negative-`a` branch.

## Scope

`memWidth_rule90_derived_eq` / `memWidth_rule150_derived_eq` give the width exactly, as a root
count, at both rules, and `rootSet_encard_add` / `rootSet_encard_add_rule150` close that count to a
numeral at each. `rootSet`'s defining property alone (`s ≠ 0` in `interiorStates`, keeping the zero
state its own root) is what every argument above relies on; no other characterisation of the root
set — parity-based or otherwise — is used anywhere in this file.

The endpoint-move generalization's two spread constants `a`/`b` enter no definition but
`interiorStates`/`rootSet` (through `U`, not directly) and no argument but `rootSet_cover` (which
needs `0 < a⁺ + b⁺`) and `rootSet_antichain` (which needs neither hypothesis nor sign case beyond
what its own two branches supply); `rootSet_encard_add_of_hyps` needs no sign hypothesis at all.
No claim in this file states or uses which pairs `(a, b)` are realized by an elementary table
beyond the six checked (`(1, 1)` at four, `(1, -1)`, `(-1, 1)`); that classification question is
open here.

The four non-additive tables and the guard are instances of a class this file does not name or
classify: `tableRule`'s one-sided-permutivity facts are stated generically in `g`/`h`, and which
elementary tables (beyond the six checked here) meet them is not decided in this file. No
declaration here claims injectivity, or any other property, off the finitely-supported carrier —
the same rules are known to fail injectivity on other carriers, and this file makes no claim there
either way.
-/


@[expose] public section

namespace ExtremeTapWidth

open DerivedStages MemoryWidth GrowingCore GrowingWorld

/-! ## Shared shift arithmetic -/

private theorem mapDomain_succ_apply (s : ℤ →₀ ZMod 2) (i : ℤ) :
    Finsupp.mapDomain (· + 1) s i = s (i - 1) := by
  have h : i = (i - 1) + 1 := by omega
  conv_lhs => rw [h]
  exact Finsupp.mapDomain_apply_of_injective (add_left_injective 1) s (i - 1)

private theorem mapDomain_pred_apply (s : ℤ →₀ ZMod 2) (i : ℤ) :
    Finsupp.mapDomain (· - 1) s i = s (i + 1) := by
  have h : i = (i + 1) - 1 := by omega
  conv_lhs => rw [h]
  exact Finsupp.mapDomain_apply_of_injective sub_left_injective s (i + 1)

/-! ## Rule 90 -/

/-- **Elementary table `90`, radius one**: `(rule90 s) i = s (i - 1) + s (i + 1)`, the XOR of the
two neighbours. -/
noncomputable def rule90 (s : ℤ →₀ ZMod 2) : ℤ →₀ ZMod 2 :=
  Finsupp.mapDomain (· + 1) s + Finsupp.mapDomain (· - 1) s

theorem rule90_apply (s : ℤ →₀ ZMod 2) (i : ℤ) :
    rule90 s i = s (i - 1) + s (i + 1) := by
  simp [rule90, mapDomain_succ_apply, mapDomain_pred_apply]

/-- **Additive**: `Finsupp.mapDomain` distributes over `+`, so `rule90` does too. -/
theorem rule90_add (s s' : ℤ →₀ ZMod 2) : rule90 (s + s') = rule90 s + rule90 s' := by
  simp only [rule90, Finsupp.mapDomain_add]; abel

private theorem rule90_sub (s s' : ℤ →₀ ZMod 2) : rule90 (s - s') = rule90 s - rule90 s' := by
  simp only [rule90, Finsupp.mapDomain_sub]; abel

private theorem rule90_zero : rule90 0 = 0 := by simp [rule90]

/-- **Trivial kernel**: at a nonzero `s`, evaluating `rule90 s` one cell below the leftmost support
index returns exactly the leftmost value — the cell two below vanishes because it undershoots the
support, so nothing else can cancel it. -/
theorem rule90_eq_zero_iff {s : ℤ →₀ ZMod 2} : rule90 s = 0 ↔ s = 0 := by
  constructor
  · intro h
    by_contra hs
    have hne := Finsupp.support_nonempty_iff.mpr hs
    have hmem : s.support.min' hne ∈ s.support := Finset.min'_mem _ hne
    have hsm : s (s.support.min' hne) ≠ 0 := Finsupp.mem_support_iff.mp hmem
    have hzero : s (s.support.min' hne - 2) = 0 := by
      by_contra hc
      have hc' : s.support.min' hne - 2 ∈ s.support := Finsupp.mem_support_iff.mpr hc
      have hle := Finset.min'_le s.support (s.support.min' hne - 2) hc'
      omega
    have hval : rule90 s (s.support.min' hne - 1) = 0 := by rw [h]; simp
    rw [rule90_apply] at hval
    have e1 : s.support.min' hne - 1 - 1 = s.support.min' hne - 2 := by omega
    have e2 : s.support.min' hne - 1 + 1 = s.support.min' hne := by omega
    rw [e1, e2, hzero, zero_add] at hval
    exact hsm hval
  · intro h; rw [h]; simp [rule90]

/-- **Injective**: additivity plus trivial kernel. -/
theorem rule90_injective : Function.Injective rule90 := by
  intro a b hab
  have hz : rule90 (a - b) = 0 := by rw [rule90_sub, hab, sub_self]
  exact sub_eq_zero.mp (rule90_eq_zero_iff.mp hz)

private theorem rule90_one_of_zero {s : ℤ →₀ ZMod 2} {b : ℤ} (hb : rule90 s b ≠ 0) :
    s (b - 1) ≠ 0 ∨ s (b + 1) ≠ 0 := by
  rw [rule90_apply] at hb
  rw [← not_and_or]
  rintro ⟨h1, h2⟩
  exact hb (by rw [h1, h2, add_zero])

/-- **The exact spread, leftmost**: the leftmost support cell moves left by exactly one. -/
theorem rule90_support_min'_spread {s : ℤ →₀ ZMod 2} (hne : s.support.Nonempty)
    (hne' : (rule90 s).support.Nonempty) :
    (rule90 s).support.min' hne' = s.support.min' hne - 1 := by
  set m := s.support.min' hne with hm_def
  rw [Finset.min'_eq_iff]
  refine ⟨?_, ?_⟩
  · rw [Finsupp.mem_support_iff, rule90_apply]
    have h1 : s (m - 1 - 1) = 0 := by
      by_contra hc
      have hmem : m - 1 - 1 ∈ s.support := Finsupp.mem_support_iff.mpr hc
      have := Finset.min'_le s.support (m - 1 - 1) hmem
      omega
    have h2 : s (m - 1 + 1) = s m := by
      have e : m - 1 + 1 = m := by omega
      rw [e]
    rw [h1, h2, zero_add]
    exact Finsupp.mem_support_iff.mp (Finset.min'_mem s.support hne)
  · intro b hb
    rcases rule90_one_of_zero (Finsupp.mem_support_iff.mp hb) with h | h
    · have hmem : b - 1 ∈ s.support := Finsupp.mem_support_iff.mpr h
      have := Finset.min'_le s.support (b - 1) hmem; omega
    · have hmem : b + 1 ∈ s.support := Finsupp.mem_support_iff.mpr h
      have := Finset.min'_le s.support (b + 1) hmem; omega

/-- **The exact spread, rightmost**: the rightmost support cell moves right by exactly one. -/
theorem rule90_support_max'_spread {s : ℤ →₀ ZMod 2} (hne : s.support.Nonempty)
    (hne' : (rule90 s).support.Nonempty) :
    (rule90 s).support.max' hne' = s.support.max' hne + 1 := by
  set M := s.support.max' hne with hM_def
  rw [Finset.max'_eq_iff]
  refine ⟨?_, ?_⟩
  · rw [Finsupp.mem_support_iff, rule90_apply]
    have h1 : s (M + 1 + 1) = 0 := by
      by_contra hc
      have hmem : M + 1 + 1 ∈ s.support := Finsupp.mem_support_iff.mpr hc
      have := Finset.le_max' s.support (M + 1 + 1) hmem
      omega
    have h2 : s (M + 1 - 1) = s M := by
      have e : M + 1 - 1 = M := by omega
      rw [e]
    rw [h1, h2, add_zero]
    exact Finsupp.mem_support_iff.mp (Finset.max'_mem s.support hne)
  · intro b hb
    rcases rule90_one_of_zero (Finsupp.mem_support_iff.mp hb) with h | h
    · have hmem : b - 1 ∈ s.support := Finsupp.mem_support_iff.mpr h
      have := Finset.le_max' s.support (b - 1) hmem; omega
    · have hmem : b + 1 ∈ s.support := Finsupp.mem_support_iff.mpr h
      have := Finset.le_max' s.support (b + 1) hmem; omega

/-- The leftmost-cell invariant, propagated one step: if everything below `m` vanishes and `m`
itself does not, the same holds one step later at `m - 1`. The induction `rule90_region_exit` and
the antichain argument in `memWidth_rule90_derived_ge` both run on, without ever forming a
`Finset.Nonempty` witness for an iterated support (which `Function.iterate_succ_apply'` cannot be
rewritten under, the nonempty proof depending on the exact term being rewritten). -/
private theorem rule90_leftWitness_step {s : ℤ →₀ ZMod 2} {m : ℤ}
    (hbelow : ∀ x < m, s x = 0) (hm : s m ≠ 0) :
    (∀ x < m - 1, rule90 s x = 0) ∧ rule90 s (m - 1) ≠ 0 := by
  refine ⟨fun x hx => ?_, ?_⟩
  · rw [rule90_apply, hbelow (x - 1) (by omega), hbelow (x + 1) (by omega), add_zero]
  · rw [rule90_apply]
    have h1 : s (m - 1 - 1) = 0 := hbelow (m - 1 - 1) (by omega)
    have e : m - 1 + 1 = m := by omega
    rw [h1, e, zero_add]
    exact hm

private theorem rule90_leftWitness_iterate {s : ℤ →₀ ZMod 2} {m : ℤ}
    (hbelow : ∀ x < m, s x = 0) (hm : s m ≠ 0) (t : ℕ) :
    (∀ x < m - t, (rule90^[t] s) x = 0) ∧ (rule90^[t] s) (m - t) ≠ 0 := by
  induction t with
  | zero => simpa using ⟨hbelow, hm⟩
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    have step := rule90_leftWitness_step ih.1 ih.2
    have e : (m - (k : ℤ)) - 1 = m - (↑(k + 1) : ℤ) := by omega
    rwa [e] at step

/-- **Region exit** ([Guests] §7's G2, stated directly): a nonzero state's orbit under `rule90`
eventually leaves any fixed finite region — the leftmost support index walks left by exactly one
cell per step, so past finitely many steps it falls below every element `R` names. -/
theorem rule90_region_exit {s : ℤ →₀ ZMod 2} (hs : s ≠ 0) (R : Finset ℤ) :
    ∃ t : ℕ, ¬ (rule90^[t] s).support ⊆ R := by
  classical
  have hne := Finsupp.support_nonempty_iff.mpr hs
  have hbelow : ∀ x < s.support.min' hne, s x = 0 := fun x hx => by
    by_contra hc
    have hmem : x ∈ s.support := Finsupp.mem_support_iff.mpr hc
    have := Finset.min'_le s.support x hmem
    omega
  have hm : s (s.support.min' hne) ≠ 0 :=
    Finsupp.mem_support_iff.mp (Finset.min'_mem s.support hne)
  set L := if h : R.Nonempty then R.min' h else 0 with hL_def
  have hL : ∀ r ∈ R, L ≤ r := by
    intro r hr
    rw [hL_def]
    split
    · next h => exact Finset.min'_le R r hr
    · next h => exact absurd ⟨r, hr⟩ h
  set t : ℕ := (s.support.min' hne - L).natAbs + 1 with ht_def
  have htbig : (t : ℤ) > s.support.min' hne - L := by
    have := Int.le_natAbs (a := s.support.min' hne - L)
    omega
  refine ⟨t, fun hsub => ?_⟩
  obtain ⟨-, hnz⟩ := rule90_leftWitness_iterate hbelow hm t
  have := hL _ (hsub (Finsupp.mem_support_iff.mpr hnz))
  omega

/-! ## Rule 150 -/

/-- **Elementary table `150`, radius one**: `(rule150 s) i = s (i - 1) + s i + s (i + 1)`. -/
noncomputable def rule150 (s : ℤ →₀ ZMod 2) : ℤ →₀ ZMod 2 :=
  Finsupp.mapDomain (· + 1) s + s + Finsupp.mapDomain (· - 1) s

theorem rule150_apply (s : ℤ →₀ ZMod 2) (i : ℤ) :
    rule150 s i = s (i - 1) + s i + s (i + 1) := by
  simp [rule150, mapDomain_succ_apply, mapDomain_pred_apply]

theorem rule150_add (s s' : ℤ →₀ ZMod 2) : rule150 (s + s') = rule150 s + rule150 s' := by
  simp only [rule150, Finsupp.mapDomain_add]; abel

private theorem rule150_sub (s s' : ℤ →₀ ZMod 2) : rule150 (s - s') = rule150 s - rule150 s' := by
  simp only [rule150, Finsupp.mapDomain_sub]; abel

private theorem rule150_zero : rule150 0 = 0 := by simp [rule150]

/-- **Trivial kernel**, as `rule90_eq_zero_iff`: the leftmost support cell forces a nonzero value
one cell further left, the two cells that could cancel it — `m - 1` and `m - 2` — both undershooting
the support. -/
theorem rule150_eq_zero_iff {s : ℤ →₀ ZMod 2} : rule150 s = 0 ↔ s = 0 := by
  constructor
  · intro h
    by_contra hs
    have hne := Finsupp.support_nonempty_iff.mpr hs
    have hmem : s.support.min' hne ∈ s.support := Finset.min'_mem _ hne
    have hsm : s (s.support.min' hne) ≠ 0 := Finsupp.mem_support_iff.mp hmem
    have hzero2 : s (s.support.min' hne - 2) = 0 := by
      by_contra hc
      have hc' : s.support.min' hne - 2 ∈ s.support := Finsupp.mem_support_iff.mpr hc
      have hle := Finset.min'_le s.support (s.support.min' hne - 2) hc'
      omega
    have hzero1 : s (s.support.min' hne - 1) = 0 := by
      by_contra hc
      have hc' : s.support.min' hne - 1 ∈ s.support := Finsupp.mem_support_iff.mpr hc
      have hle := Finset.min'_le s.support (s.support.min' hne - 1) hc'
      omega
    have hval : rule150 s (s.support.min' hne - 1) = 0 := by rw [h]; simp
    rw [rule150_apply] at hval
    have e1 : s.support.min' hne - 1 - 1 = s.support.min' hne - 2 := by omega
    have e2 : s.support.min' hne - 1 + 1 = s.support.min' hne := by omega
    rw [e1, e2, hzero2, hzero1, zero_add, zero_add] at hval
    exact hsm hval
  · intro h; rw [h]; simp [rule150]

theorem rule150_injective : Function.Injective rule150 := by
  intro a b hab
  have hz : rule150 (a - b) = 0 := by rw [rule150_sub, hab, sub_self]
  exact sub_eq_zero.mp (rule150_eq_zero_iff.mp hz)

private theorem rule150_one_of_zero {s : ℤ →₀ ZMod 2} {b : ℤ} (hb : rule150 s b ≠ 0) :
    s (b - 1) ≠ 0 ∨ s b ≠ 0 ∨ s (b + 1) ≠ 0 := by
  rw [rule150_apply] at hb
  by_contra hcon
  rw [not_or, not_or] at hcon
  obtain ⟨h1, h2, h3⟩ := hcon
  simp only [not_not] at h1 h2 h3
  exact hb (by rw [h1, h2, h3, add_zero, add_zero])

theorem rule150_support_min'_spread {s : ℤ →₀ ZMod 2} (hne : s.support.Nonempty)
    (hne' : (rule150 s).support.Nonempty) :
    (rule150 s).support.min' hne' = s.support.min' hne - 1 := by
  set m := s.support.min' hne with hm_def
  rw [Finset.min'_eq_iff]
  refine ⟨?_, ?_⟩
  · rw [Finsupp.mem_support_iff, rule150_apply]
    have h1 : s (m - 1 - 1) = 0 := by
      by_contra hc
      have hmem : m - 1 - 1 ∈ s.support := Finsupp.mem_support_iff.mpr hc
      have := Finset.min'_le s.support (m - 1 - 1) hmem
      omega
    have h1' : s (m - 1) = 0 := by
      by_contra hc
      have hmem : m - 1 ∈ s.support := Finsupp.mem_support_iff.mpr hc
      have := Finset.min'_le s.support (m - 1) hmem
      omega
    have h2 : s (m - 1 + 1) = s m := by
      have e : m - 1 + 1 = m := by omega
      rw [e]
    rw [h1, h1', h2, zero_add, zero_add]
    exact Finsupp.mem_support_iff.mp (Finset.min'_mem s.support hne)
  · intro b hb
    rcases rule150_one_of_zero (Finsupp.mem_support_iff.mp hb) with h | h | h
    · have hmem : b - 1 ∈ s.support := Finsupp.mem_support_iff.mpr h
      have := Finset.min'_le s.support (b - 1) hmem; omega
    · have hmem : b ∈ s.support := Finsupp.mem_support_iff.mpr h
      have := Finset.min'_le s.support b hmem; omega
    · have hmem : b + 1 ∈ s.support := Finsupp.mem_support_iff.mpr h
      have := Finset.min'_le s.support (b + 1) hmem; omega

theorem rule150_support_max'_spread {s : ℤ →₀ ZMod 2} (hne : s.support.Nonempty)
    (hne' : (rule150 s).support.Nonempty) :
    (rule150 s).support.max' hne' = s.support.max' hne + 1 := by
  set M := s.support.max' hne with hM_def
  rw [Finset.max'_eq_iff]
  refine ⟨?_, ?_⟩
  · rw [Finsupp.mem_support_iff, rule150_apply]
    have h1 : s (M + 1 + 1) = 0 := by
      by_contra hc
      have hmem : M + 1 + 1 ∈ s.support := Finsupp.mem_support_iff.mpr hc
      have := Finset.le_max' s.support (M + 1 + 1) hmem
      omega
    have h1' : s (M + 1) = 0 := by
      by_contra hc
      have hmem : M + 1 ∈ s.support := Finsupp.mem_support_iff.mpr hc
      have := Finset.le_max' s.support (M + 1) hmem
      omega
    have h2 : s (M + 1 - 1) = s M := by
      have e : M + 1 - 1 = M := by omega
      rw [e]
    rw [h1, h1', h2, add_zero, add_zero]
    exact Finsupp.mem_support_iff.mp (Finset.max'_mem s.support hne)
  · intro b hb
    rcases rule150_one_of_zero (Finsupp.mem_support_iff.mp hb) with h | h | h
    · have hmem : b - 1 ∈ s.support := Finsupp.mem_support_iff.mpr h
      have := Finset.le_max' s.support (b - 1) hmem; omega
    · have hmem : b ∈ s.support := Finsupp.mem_support_iff.mpr h
      have := Finset.le_max' s.support b hmem; omega
    · have hmem : b + 1 ∈ s.support := Finsupp.mem_support_iff.mpr h
      have := Finset.le_max' s.support (b + 1) hmem; omega

private theorem rule150_leftWitness_step {s : ℤ →₀ ZMod 2} {m : ℤ}
    (hbelow : ∀ x < m, s x = 0) (hm : s m ≠ 0) :
    (∀ x < m - 1, rule150 s x = 0) ∧ rule150 s (m - 1) ≠ 0 := by
  refine ⟨fun x hx => ?_, ?_⟩
  · rw [rule150_apply, hbelow (x - 1) (by omega), hbelow x (by omega), hbelow (x + 1) (by omega)]
    ring
  · rw [rule150_apply]
    have h1 : s (m - 1 - 1) = 0 := hbelow (m - 1 - 1) (by omega)
    have h1' : s (m - 1) = 0 := hbelow (m - 1) (by omega)
    have e : m - 1 + 1 = m := by omega
    rw [h1, h1', e, zero_add, zero_add]
    exact hm

private theorem rule150_leftWitness_iterate {s : ℤ →₀ ZMod 2} {m : ℤ}
    (hbelow : ∀ x < m, s x = 0) (hm : s m ≠ 0) (t : ℕ) :
    (∀ x < m - t, (rule150^[t] s) x = 0) ∧ (rule150^[t] s) (m - t) ≠ 0 := by
  induction t with
  | zero => simpa using ⟨hbelow, hm⟩
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    have step := rule150_leftWitness_step ih.1 ih.2
    have e : (m - (k : ℤ)) - 1 = m - (↑(k + 1) : ℤ) := by omega
    rwa [e] at step

theorem rule150_region_exit {s : ℤ →₀ ZMod 2} (hs : s ≠ 0) (R : Finset ℤ) :
    ∃ t : ℕ, ¬ (rule150^[t] s).support ⊆ R := by
  classical
  have hne := Finsupp.support_nonempty_iff.mpr hs
  have hbelow : ∀ x < s.support.min' hne, s x = 0 := fun x hx => by
    by_contra hc
    have hmem : x ∈ s.support := Finsupp.mem_support_iff.mpr hc
    have := Finset.min'_le s.support x hmem
    omega
  have hm : s (s.support.min' hne) ≠ 0 :=
    Finsupp.mem_support_iff.mp (Finset.min'_mem s.support hne)
  set L := if h : R.Nonempty then R.min' h else 0 with hL_def
  have hL : ∀ r ∈ R, L ≤ r := by
    intro r hr
    rw [hL_def]
    split
    · next h => exact Finset.min'_le R r hr
    · next h => exact absurd ⟨r, hr⟩ h
  set t : ℕ := (s.support.min' hne - L).natAbs + 1 with ht_def
  have htbig : (t : ℤ) > s.support.min' hne - L := by
    have := Int.le_natAbs (a := s.support.min' hne - L)
    omega
  refine ⟨t, fun hsub => ?_⟩
  obtain ⟨-, hnz⟩ := rule150_leftWitness_iterate hbelow hm t
  have := hL _ (hsub (Finsupp.mem_support_iff.mpr hnz))
  omega

/-! ## The `n`-cell region, its left-edge antichain, and the two capstones -/

/-- **The states supported on an `n`-cell region** `{0, …, n - 1}`. -/
def regionStates (n : ℕ) : Set (ℤ →₀ ZMod 2) := {s | ∀ i ∈ s.support, 0 ≤ i ∧ i < (n : ℤ)}

/-- **The left-edge family**: cell `0` pinned to `1`, cells `1, …, n - 1` free. An embedding of the
`2 ^ (n - 1)` functions `Fin (n - 1) → ZMod 2` into `regionStates n`. -/
private noncomputable def leftEdgeMember (n : ℕ) (g : Fin (n - 1) → ZMod 2) : ℤ →₀ ZMod 2 :=
  Finsupp.single (0 : ℤ) 1 +
    Finsupp.mapDomain (fun i : Fin (n - 1) => (i : ℤ) + 1) (Finsupp.equivFunOnFinite.symm g)

private theorem shiftEmbed_injective (n : ℕ) :
    Function.Injective (fun i : Fin (n - 1) => (i : ℤ) + 1) := by
  intro a b hab
  simp only at hab
  exact Fin.ext (by omega)

private theorem leftEdgeMember_apply_shift (n : ℕ) (g : Fin (n - 1) → ZMod 2) (i : Fin (n - 1)) :
    leftEdgeMember n g ((i : ℤ) + 1) = g i := by
  have hne : (0 : ℤ) ≠ (i : ℤ) + 1 := by positivity
  rw [leftEdgeMember, Finsupp.add_apply, Finsupp.single_apply, ite_eq_right hne, zero_add]
  simpa using Finsupp.mapDomain_apply_of_injective (shiftEmbed_injective n)
    (Finsupp.equivFunOnFinite.symm g) i

private theorem leftEdgeMember_zero (n : ℕ) (g : Fin (n - 1) → ZMod 2) :
    leftEdgeMember n g 0 = 1 := by
  rw [leftEdgeMember, Finsupp.add_apply, Finsupp.single_eq_same]
  have hz : Finsupp.mapDomain (fun i : Fin (n - 1) => (i : ℤ) + 1)
      (Finsupp.equivFunOnFinite.symm g) 0 = 0 := by
    apply Finsupp.mapDomain_of_notMem_range
    rintro ⟨i, hi⟩
    simp only [] at hi
    have h1 : (0 : ℤ) ≤ (i : ℤ) := by positivity
    omega
  rw [hz, add_zero]

private theorem leftEdgeMember_outside (n : ℕ) (g : Fin (n - 1) → ZMod 2) (x : ℤ)
    (hx0 : x ≠ 0) (hxrange : ¬ (0 < x ∧ x < n)) :
    leftEdgeMember n g x = 0 := by
  rw [leftEdgeMember, Finsupp.add_apply, Finsupp.single_apply, ite_eq_right (Ne.symm hx0), zero_add]
  apply Finsupp.mapDomain_of_notMem_range
  rintro ⟨i, hi⟩
  simp only [] at hi
  apply hxrange
  have h1 : (0 : ℤ) ≤ (i : ℤ) := by positivity
  have h2 : (i : ℕ) < n - 1 := i.isLt
  omega

private theorem leftEdgeMember_mem_regionStates (n : ℕ) (hn : 1 ≤ n) (g : Fin (n - 1) → ZMod 2) :
    leftEdgeMember n g ∈ regionStates n := by
  intro x hx
  by_contra hcon
  rw [not_and_or, not_le, not_lt] at hcon
  have hx0 : x ≠ 0 := by rcases hcon with h | h <;> omega
  have hout : leftEdgeMember n g x = 0 :=
    leftEdgeMember_outside n g x hx0 (by rintro ⟨h1, h2⟩; rcases hcon with h | h <;> omega)
  exact (Finsupp.mem_support_iff.mp hx) hout

private theorem leftEdgeMember_injective (n : ℕ) : Function.Injective (leftEdgeMember n) := by
  intro g g' hgg'
  funext i
  rw [← leftEdgeMember_apply_shift n g i, ← leftEdgeMember_apply_shift n g' i, hgg']

/-- **`2 ^ (n - 1)` free left-edge configurations, cast to `ℕ∞`**: the size of the domain
`leftEdgeMember` embeds. -/
private theorem card_leftEdge (n : ℕ) :
    (2 ^ (n - 1) : ℕ∞) = ENat.card (Fin (n - 1) → ZMod 2) := by
  rw [ENat.card_eq_coe_fintype_card, Fintype.card_fun]; simp [ZMod.card]

/-- **Grade B1, the capstone for `rule90`**: on the world derived from the full state set of an
`n`-cell start region, the memory width is at least `2 ^ (n - 1)` — at least half
`DerivedStages.memWidth_derivedStages_le`'s cap `2 ^ n`.

Route: the left-edge seeds (`leftEdgeMember n`'s image) form an antichain of `Reaches` — a witness
`(mergeLaw rule90)^[j] (mergeMk rule90 s) = mergeMk rule90 s'` converts, through
`MemoryWidth.mergeLaw_iterate_mergeMk` and `GrowingCore.mergeMk_injective_of_injective`, to
`rule90^[j] s = s'`; at `j = 0` this forces `s = s'`, excluded by the antichain's own distinctness
hypothesis, and at `j ≥ 1` the iterated spread puts a negative index (`-j`) in the left support
while `s'` is region-supported, so `s' ≠ rule90^[j] s`. The antichain's cardinality — an injection
of the `2 ^ (n - 1)` free left-edge configurations, since `mergeMk rule90` is globally injective —
transports to the width by `le_sSup`. -/
theorem memWidth_rule90_derived_ge {n : ℕ} (hn : 1 ≤ n) :
    (2 ^ (n - 1) : ℕ∞) ≤ memWidth rule90 (derivedStages rule90 (regionStates n)) 0 := by
  classical
  set L : Set (ℤ →₀ ZMod 2) := {s | s ∈ regionStates n ∧ s 0 = 1} with hL_def
  have hsub : mergeMk rule90 '' L ⊆
      mergeStage rule90 (derivedStages rule90 (regionStates n)) 0 := by
    rintro _ ⟨s, ⟨hs, -⟩, rfl⟩
    exact ⟨s, by simp [derivedStages, hs], rfl⟩
  have hanti : IsAntichain (Reaches rule90) (mergeMk rule90 '' L) := by
    rintro _ ⟨a, ⟨ha, ha0⟩, rfl⟩ _ ⟨b, ⟨hb, hb0⟩, rfl⟩ hne ⟨j, hj⟩
    rw [mergeLaw_iterate_mergeMk] at hj
    have heq : rule90^[j] a = b := mergeMk_injective_of_injective rule90_injective hj
    rcases Nat.eq_zero_or_pos j with hj0 | hj1
    · subst hj0
      simp only [Function.iterate_zero, id] at heq
      exact hne (by rw [heq])
    · have hbelow : ∀ x < (0 : ℤ), a x = 0 := fun x hx => by
        by_contra hc
        exact absurd (ha x (Finsupp.mem_support_iff.mpr hc)).1 (by omega)
      obtain ⟨-, hnz⟩ := rule90_leftWitness_iterate hbelow (by rw [ha0]; decide) j
      have hbneg : b (0 - (j : ℤ)) ≠ 0 := heq ▸ hnz
      have := (hb (0 - (j : ℤ)) (Finsupp.mem_support_iff.mpr hbneg)).1
      omega
  have hcard : (2 ^ (n - 1) : ℕ∞) ≤ (mergeMk rule90 '' L).encard := by
    rw [Function.Injective.encard_image (mergeMk_injective_of_injective rule90_injective) L,
      card_leftEdge]
    calc ENat.card (Fin (n - 1) → ZMod 2)
        ≤ (Set.range (leftEdgeMember n)).encard := (leftEdgeMember_injective n).encard_range.ge
      _ ≤ L.encard := Set.encard_mono (by
          rintro _ ⟨g, rfl⟩
          exact ⟨leftEdgeMember_mem_regionStates n hn g, leftEdgeMember_zero n g⟩)
  exact hcard.trans (le_sSup ⟨mergeMk rule90 '' L, ⟨hsub, hanti⟩, rfl⟩)

/-- **Grade B1, the capstone for `rule150`** — identical route to `memWidth_rule90_derived_ge`. -/
theorem memWidth_rule150_derived_ge {n : ℕ} (hn : 1 ≤ n) :
    (2 ^ (n - 1) : ℕ∞) ≤ memWidth rule150 (derivedStages rule150 (regionStates n)) 0 := by
  classical
  set L : Set (ℤ →₀ ZMod 2) := {s | s ∈ regionStates n ∧ s 0 = 1} with hL_def
  have hsub : mergeMk rule150 '' L ⊆
      mergeStage rule150 (derivedStages rule150 (regionStates n)) 0 := by
    rintro _ ⟨s, ⟨hs, -⟩, rfl⟩
    exact ⟨s, by simp [derivedStages, hs], rfl⟩
  have hanti : IsAntichain (Reaches rule150) (mergeMk rule150 '' L) := by
    rintro _ ⟨a, ⟨ha, ha0⟩, rfl⟩ _ ⟨b, ⟨hb, hb0⟩, rfl⟩ hne ⟨j, hj⟩
    rw [mergeLaw_iterate_mergeMk] at hj
    have heq : rule150^[j] a = b := mergeMk_injective_of_injective rule150_injective hj
    rcases Nat.eq_zero_or_pos j with hj0 | hj1
    · subst hj0
      simp only [Function.iterate_zero, id] at heq
      exact hne (by rw [heq])
    · have hbelow : ∀ x < (0 : ℤ), a x = 0 := fun x hx => by
        by_contra hc
        exact absurd (ha x (Finsupp.mem_support_iff.mpr hc)).1 (by omega)
      obtain ⟨-, hnz⟩ := rule150_leftWitness_iterate hbelow (by rw [ha0]; decide) j
      have hbneg : b (0 - (j : ℤ)) ≠ 0 := heq ▸ hnz
      have := (hb (0 - (j : ℤ)) (Finsupp.mem_support_iff.mpr hbneg)).1
      omega
  have hcard : (2 ^ (n - 1) : ℕ∞) ≤ (mergeMk rule150 '' L).encard := by
    rw [Function.Injective.encard_image (mergeMk_injective_of_injective rule150_injective) L,
      card_leftEdge]
    calc ENat.card (Fin (n - 1) → ZMod 2)
        ≤ (Set.range (leftEdgeMember n)).encard := (leftEdgeMember_injective n).encard_range.ge
      _ ≤ L.encard := Set.encard_mono (by
          rintro _ ⟨g, rfl⟩
          exact ⟨leftEdgeMember_mem_regionStates n hn g, leftEdgeMember_zero n g⟩)
  exact hcard.trans (le_sSup ⟨mergeMk rule150 '' L, ⟨hsub, hanti⟩, rfl⟩)

/-! ## The exact width at both rules (grade B2)

The left-edge bound above is half the cap; this section computes the width exactly, as a root
count, generic in `U` and, since the endpoint-move generalization, in the update's own two spread
constants `a b : ℤ` ([Guests] Proposition 7.20): the leftmost support cell moves by `a`, the
rightmost
by `b`, rather than by exactly one cell each. Writing `x⁺` for `max x 0`, `rule90`/`rule150` and
the four non-additive tables below all instantiate at `(a, b) = (1, 1)`; `rule170`/`rule240`
later in this file instantiate at `(1, -1)` and `(-1, 1)`. The root COUNT holds at every `(a, b)`,
`(0, 0)` included; the exact WIDTH (`memWidth_derived_eq_encard_rootSet`, hence `rootSet_cover`)
needs `(a, b) ≠ (0, 0)` — the identity update at the end of this section is the witness that
separates the two claims. -/

/-- **The interior of the region**: nonzero states supported inside the region whose `U`-image is
also region-supported. Under `hUmin'`/`hUmax'`'s exact spread and the trivial kernel this is
exactly the window `[a⁺, n - 1 - b⁺]` (`interiorStates_eq_window`) — at `(a, b) = (1, 1)` the old
`[1, n - 2]` window this definition replaces. The two spread constants `a`/`b` enter no other
definition in this file: every other declaration below is stated purely in terms of `U`. -/
def interiorStates (U : (ℤ →₀ ZMod 2) → (ℤ →₀ ZMod 2)) (n : ℕ) : Set (ℤ →₀ ZMod 2) :=
  {s | s ≠ 0 ∧ s ∈ regionStates n ∧ U s ∈ regionStates n}

/-- **The root set**: the region-supported states with no `U`-preimage inside the interior. The
`s ≠ 0` qualifier in `interiorStates` is load-bearing: it keeps the zero state a root — `U 0 = 0`
but `0 ∉ interiorStates U n` — so `rootSet` carries the zero class as its own separate component,
exactly the `+ 1` in the closed count `rootSet_encard_add`. -/
def rootSet (U : (ℤ →₀ ZMod 2) → (ℤ →₀ ZMod 2)) (n : ℕ) : Set (ℤ →₀ ZMod 2) :=
  regionStates n \ U '' interiorStates U n

private theorem iterate_ne_zero {U : (ℤ →₀ ZMod 2) → (ℤ →₀ ZMod 2)}
    (hUeqZero : ∀ {s : ℤ →₀ ZMod 2}, U s = 0 ↔ s = 0) {s : ℤ →₀ ZMod 2} (hs : s ≠ 0) :
    ∀ t : ℕ, U^[t] s ≠ 0 := by
  intro t
  induction t with
  | zero => simpa using hs
  | succ k ih => rw [Function.iterate_succ_apply']; exact fun h => ih (hUeqZero.mp h)

private theorem zero_mem_rootSet {U : (ℤ →₀ ZMod 2) → (ℤ →₀ ZMod 2)}
    (hUeqZero : ∀ {s : ℤ →₀ ZMod 2}, U s = 0 ↔ s = 0) (n : ℕ) :
    (0 : ℤ →₀ ZMod 2) ∈ rootSet U n := by
  refine ⟨fun i hi => by simp at hi, ?_⟩
  rintro ⟨t, ht, hUt⟩
  exact ht.1 (hUeqZero.mp hUt)

/-! ### Generic infrastructure for the endpoint-move generalization

`Finset.min'`/`Finset.max'` carry a `Finset.Nonempty` witness as an explicit argument, so two
calls at the SAME finset but different witnesses are already defeq by `Prop`'s proof irrelevance;
`minCongr`/`maxCongr` below are for the one case that needs more — two calls at PROPOSITIONALLY
(not syntactically) equal finsets, the shape `Function.iterate_succ_apply'` produces and which a
bare `rw` cannot be carried under (the trap `rule90_leftWitness_step`'s docstring records). -/

private theorem minCongr {s t : Finset ℤ} (h : s = t) (hs : s.Nonempty) (ht : t.Nonempty) :
    s.min' hs = t.min' ht := by subst h; rfl

private theorem maxCongr {s t : Finset ℤ} (h : s = t) (hs : s.Nonempty) (ht : t.Nonempty) :
    s.max' hs = t.max' ht := by subst h; rfl

/-- **The iterated left spread**: `t` steps move the leftmost support cell by `t * a`. -/
private theorem iterate_min'_spread
    {U : (ℤ →₀ ZMod 2) → (ℤ →₀ ZMod 2)} {a : ℤ}
    (hUeqZero : ∀ {s : ℤ →₀ ZMod 2}, U s = 0 ↔ s = 0)
    (hUmin' : ∀ {s : ℤ →₀ ZMod 2} (hne : s.support.Nonempty) (hne' : (U s).support.Nonempty),
      (U s).support.min' hne' = s.support.min' hne - a)
    {s : ℤ →₀ ZMod 2} (hs : s ≠ 0) (hne : s.support.Nonempty) :
    ∀ (k : ℕ) (hne' : (U^[k] s).support.Nonempty),
      (U^[k] s).support.min' hne' = s.support.min' hne - k * a := by
  intro k
  induction k with
  | zero =>
    intro hne'
    rw [minCongr (congrArg Finsupp.support (rfl : U^[0] s = s)) hne' hne]; simp
  | succ j ih =>
    intro hne'
    have hjne' : (U^[j] s).support.Nonempty :=
      Finsupp.support_nonempty_iff.mpr (iterate_ne_zero hUeqZero hs j)
    have e : U^[j + 1] s = U (U^[j] s) := Function.iterate_succ_apply' U j s
    have hUjne' : (U (U^[j] s)).support.Nonempty := by rw [← e]; exact hne'
    rw [minCongr (congrArg Finsupp.support e) hne' hUjne', hUmin' hjne' hUjne', ih hjne']
    push_cast; ring

/-- **The iterated right spread**: `t` steps move the rightmost support cell by `t * b`. -/
private theorem iterate_max'_spread
    {U : (ℤ →₀ ZMod 2) → (ℤ →₀ ZMod 2)} {b : ℤ}
    (hUeqZero : ∀ {s : ℤ →₀ ZMod 2}, U s = 0 ↔ s = 0)
    (hUmax' : ∀ {s : ℤ →₀ ZMod 2} (hne : s.support.Nonempty) (hne' : (U s).support.Nonempty),
      (U s).support.max' hne' = s.support.max' hne + b)
    {s : ℤ →₀ ZMod 2} (hs : s ≠ 0) (hne : s.support.Nonempty) :
    ∀ (k : ℕ) (hne' : (U^[k] s).support.Nonempty),
      (U^[k] s).support.max' hne' = s.support.max' hne + k * b := by
  intro k
  induction k with
  | zero =>
    intro hne'
    rw [maxCongr (congrArg Finsupp.support (rfl : U^[0] s = s)) hne' hne]; simp
  | succ j ih =>
    intro hne'
    have hjne' : (U^[j] s).support.Nonempty :=
      Finsupp.support_nonempty_iff.mpr (iterate_ne_zero hUeqZero hs j)
    have e : U^[j + 1] s = U (U^[j] s) := Function.iterate_succ_apply' U j s
    have hUjne' : (U (U^[j] s)).support.Nonempty := by rw [← e]; exact hne'
    rw [maxCongr (congrArg Finsupp.support e) hne' hUjne', hUmax' hjne' hUjne', ih hjne']
    push_cast; ring

/-- **The sign law**: the two spread constants always sum to something non-negative. Route: at
ANY nonzero `s`, the support diameter `(U^[k] s).support.max' - (U^[k] s).support.min'` is
non-negative for every `k` (`Finset.min'_le_max'`) and, by the two iterated spreads above, equals
`(s.support.max' - s.support.min') + k * (a + b)` — so `a + b < 0` is refuted by any `k` beyond
the starting diameter. Never applied inside this file (`rootSet_cover`/`rootSet_antichain` case on
the SIGN of `a`/`b` directly, which is what their own inductions need): a standalone fact about
what the two exact-spread hypotheses already force, corollary `max a 0 + max b 0 > 0 ↔
(a, b) ≠ (0, 0)` the reading the identity guard below witnesses one direction of. -/
theorem hUspread_sign_nonneg
    {U : (ℤ →₀ ZMod 2) → (ℤ →₀ ZMod 2)} {a b : ℤ}
    (hUeqZero : ∀ {s : ℤ →₀ ZMod 2}, U s = 0 ↔ s = 0)
    (hUmin' : ∀ {s : ℤ →₀ ZMod 2} (hne : s.support.Nonempty) (hne' : (U s).support.Nonempty),
      (U s).support.min' hne' = s.support.min' hne - a)
    (hUmax' : ∀ {s : ℤ →₀ ZMod 2} (hne : s.support.Nonempty) (hne' : (U s).support.Nonempty),
      (U s).support.max' hne' = s.support.max' hne + b) :
    0 ≤ a + b := by
  set s : ℤ →₀ ZMod 2 := Finsupp.single (0 : ℤ) (1 : ZMod 2) with hs_def
  have hs : s ≠ 0 := by
    rw [hs_def]; intro h
    have := DFunLike.congr_fun h (0 : ℤ)
    simp at this
  have hne : s.support.Nonempty := Finsupp.support_nonempty_iff.mpr hs
  by_contra hcon
  push Not at hcon
  set C : ℤ := s.support.max' hne - s.support.min' hne with hC_def
  have hCnn : 0 ≤ C := by rw [hC_def]; have := Finset.min'_le_max' s.support hne; omega
  set k : ℕ := C.toNat + 1 with hk_def
  have hkval : (k : ℤ) = C + 1 := by rw [hk_def]; push_cast; omega
  have hkne : (U^[k] s) ≠ 0 := iterate_ne_zero hUeqZero hs k
  have hkne' : (U^[k] s).support.Nonempty := Finsupp.support_nonempty_iff.mpr hkne
  have hmin := iterate_min'_spread hUeqZero hUmin' hs hne k hkne'
  have hmax := iterate_max'_spread hUeqZero hUmax' hs hne k hkne'
  have hle : (U^[k] s).support.min' hkne' ≤ (U^[k] s).support.max' hkne' :=
    Finset.min'_le_max' _ hkne'
  rw [hmin, hmax] at hle
  nlinarith [hkval, hCnn]

/-- **The window characterization** (Target 1's own deliverable): under the trivial kernel and the
two exact spread identities, `interiorStates U n` is exactly the nonzero states supported in
`[a⁺, n - 1 - b⁺]` — at `(a, b) = (1, 1)` the old `[1, n - 2]` window. Route: `s`'s own region
membership gives `0 ≤ s.min'`/`s.max' < n` directly; `U s`'s region membership, combined with the
spread identities, gives `s.min' ≥ a` / `s.max' ≤ n - 1 - b`; the two combine to `s.min' ≥ a⁺` /
`s.max' ≤ n - 1 - b⁺` since `a⁺ ≥ a`/`a⁺ ≥ 0` (and the `b` mirror) always — no case split on the
sign of `a`/`b` is needed here, unlike in `rootSet_cover`/`rootSet_antichain` below. -/
theorem interiorStates_eq_window
    {U : (ℤ →₀ ZMod 2) → (ℤ →₀ ZMod 2)} {a b : ℤ}
    (hUeqZero : ∀ {s : ℤ →₀ ZMod 2}, U s = 0 ↔ s = 0)
    (hUmin' : ∀ {s : ℤ →₀ ZMod 2} (hne : s.support.Nonempty) (hne' : (U s).support.Nonempty),
      (U s).support.min' hne' = s.support.min' hne - a)
    (hUmax' : ∀ {s : ℤ →₀ ZMod 2} (hne : s.support.Nonempty) (hne' : (U s).support.Nonempty),
      (U s).support.max' hne' = s.support.max' hne + b)
    (n : ℕ) :
    interiorStates U n =
      {s | s ≠ 0 ∧ ∀ i ∈ s.support, max a 0 ≤ i ∧ i ≤ (n : ℤ) - 1 - max b 0} := by
  ext s
  simp only [interiorStates, regionStates, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hs0, hsreg, hUsreg⟩
    refine ⟨hs0, fun i hi => ?_⟩
    have hne : s.support.Nonempty := Finsupp.support_nonempty_iff.mpr hs0
    have hUsne : U s ≠ 0 := fun h => hs0 (hUeqZero.mp h)
    have hUne' : (U s).support.Nonempty := Finsupp.support_nonempty_iff.mpr hUsne
    have hmin := hUmin' hne hUne'
    have hmax := hUmax' hne hUne'
    have h1 : 0 ≤ s.support.min' hne := (hsreg _ (Finset.min'_mem s.support hne)).1
    have h2 : s.support.max' hne < (n : ℤ) := (hsreg _ (Finset.max'_mem s.support hne)).2
    have h3 : 0 ≤ (U s).support.min' hUne' := (hUsreg _ (Finset.min'_mem _ hUne')).1
    have h4 : (U s).support.max' hUne' < (n : ℤ) := (hUsreg _ (Finset.max'_mem _ hUne')).2
    have hile := Finset.min'_le s.support i hi
    have hige := Finset.le_max' s.support i hi
    omega
  · rintro ⟨hs0, hwin⟩
    have hne : s.support.Nonempty := Finsupp.support_nonempty_iff.mpr hs0
    have hUsne : U s ≠ 0 := fun h => hs0 (hUeqZero.mp h)
    have hUne' : (U s).support.Nonempty := Finsupp.support_nonempty_iff.mpr hUsne
    have hmin := hUmin' hne hUne'
    have hmax := hUmax' hne hUne'
    have h1 : max a 0 ≤ s.support.min' hne := (hwin _ (Finset.min'_mem s.support hne)).1
    have h2 : s.support.max' hne ≤ (n : ℤ) - 1 - max b 0 :=
      (hwin _ (Finset.max'_mem s.support hne)).2
    refine ⟨hs0, fun i hi => ?_, fun i hi => ?_⟩
    · have hile := Finset.min'_le s.support i hi
      have hige := Finset.le_max' s.support i hi
      omega
    · have hile2 := Finset.min'_le (U s).support i hi
      have hige2 := Finset.le_max' (U s).support i hi
      omega

/-- **The cover**: every region-supported state is reached, by iterating `U`, from a root — strong
induction on a measure combining both ends, `a⁺ * (n - 1 - s.min') + b⁺ * s.max'`, non-negative on
the region and dropping by exactly `a⁺ * a + b⁺ * b = (a⁺)² + (b⁺)²` at each backward step (an
interior preimage's own spread identities), which is what needs `0 < a⁺ + b⁺` — at `(a, b) =
(0, 0)` the identity update is the witness this fails: nothing is ever reached from `{0}` but `0`
itself (`hUspread_sign_nonneg`'s boundary). -/
private theorem rootSet_cover
    {U : (ℤ →₀ ZMod 2) → (ℤ →₀ ZMod 2)} {a b : ℤ}
    (hUeqZero : ∀ {s : ℤ →₀ ZMod 2}, U s = 0 ↔ s = 0)
    (hUmin' : ∀ {s : ℤ →₀ ZMod 2} (hne : s.support.Nonempty) (hne' : (U s).support.Nonempty),
      (U s).support.min' hne' = s.support.min' hne - a)
    (hUmax' : ∀ {s : ℤ →₀ ZMod 2} (hne : s.support.Nonempty) (hne' : (U s).support.Nonempty),
      (U s).support.max' hne' = s.support.max' hne + b)
    (hab : 0 < max a 0 + max b 0)
    (n : ℕ) :
    ∀ s ∈ regionStates n, ∃ r ∈ rootSet U n, ∃ j : ℕ, U^[j] r = s := by
  have hdrop_pos : 0 < max a 0 * a + max b 0 * b := by
    have e1 : max a 0 * a = (max a 0) ^ 2 := by
      rcases le_total 0 a with h | h
      · rw [max_eq_left h]; ring
      · rw [max_eq_right h]; ring
    have e2 : max b 0 * b = (max b 0) ^ 2 := by
      rcases le_total 0 b with h | h
      · rw [max_eq_left h]; ring
      · rw [max_eq_right h]; ring
    rw [e1, e2]
    have h1 : (0 : ℤ) ≤ max a 0 := le_max_right a 0
    rcases lt_or_eq_of_le h1 with ha | ha
    · nlinarith [sq_nonneg (max b 0), pow_pos ha 2]
    · nlinarith [sq_nonneg (max a 0), pow_pos (by omega : (0 : ℤ) < max b 0) 2]
  have main : ∀ k : ℕ, ∀ s : ℤ →₀ ZMod 2, ∀ hs0 : s ≠ 0,
      (max a 0 * ((n : ℤ) - 1 - s.support.min' (Finsupp.support_nonempty_iff.mpr hs0)) +
        max b 0 * s.support.max' (Finsupp.support_nonempty_iff.mpr hs0)).toNat = k →
      s ∈ regionStates n → ∃ r ∈ rootSet U n, ∃ j : ℕ, U^[j] r = s := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro s hs0 hk hsreg
      by_cases hroot : s ∈ rootSet U n
      · exact ⟨s, hroot, 0, rfl⟩
      · have hsu : s ∈ U '' interiorStates U n := by
          by_contra hc; exact hroot ⟨hsreg, hc⟩
        obtain ⟨r, hrint, hUr⟩ := hsu
        subst hUr
        have hrne : r ≠ 0 := hrint.1
        have hrreg : r ∈ regionStates n := hrint.2.1
        have hrne' : r.support.Nonempty := Finsupp.support_nonempty_iff.mpr hrne
        have hUrne' : (U r).support.Nonempty := Finsupp.support_nonempty_iff.mpr hs0
        have hspreadMin := hUmin' hrne' hUrne'
        have hspreadMax := hUmax' hrne' hUrne'
        have hrmin_ge : 0 ≤ r.support.min' hrne' := (hrreg _ (Finset.min'_mem r.support hrne')).1
        have hrmax_lt : r.support.max' hrne' < (n : ℤ) :=
          (hrreg _ (Finset.max'_mem r.support hrne')).2
        have hrmin_le_max : r.support.min' hrne' ≤ r.support.max' hrne' :=
          Finset.min'_le_max' r.support hrne'
        have hMr_nonneg :
            0 ≤ max a 0 * ((n : ℤ) - 1 - r.support.min' hrne') +
              max b 0 * r.support.max' hrne' := by
          have h1 : (0 : ℤ) ≤ max a 0 := le_max_right a 0
          have h2 : (0 : ℤ) ≤ max b 0 := le_max_right b 0
          have h3 : (0 : ℤ) ≤ (n : ℤ) - 1 - r.support.min' hrne' := by omega
          have h4 : (0 : ℤ) ≤ r.support.max' hrne' := by omega
          positivity
        rw [hspreadMin, hspreadMax] at hk
        have hexp :
            max a 0 * ((n : ℤ) - 1 - (r.support.min' hrne' - a)) +
                max b 0 * (r.support.max' hrne' + b) =
              (max a 0 * ((n : ℤ) - 1 - r.support.min' hrne') +
                  max b 0 * r.support.max' hrne') +
                (max a 0 * a + max b 0 * b) := by ring
        rw [hexp] at hk
        have hk' :
            (max a 0 * ((n : ℤ) - 1 - r.support.min' hrne') +
                max b 0 * r.support.max' hrne').toNat < k := by omega
        obtain ⟨r0, hr0root, j, hj⟩ := ih _ hk' r hrne rfl hrreg
        exact ⟨r0, hr0root, j + 1, by rw [Function.iterate_succ_apply', hj]⟩
  intro s hs
  by_cases h0 : s = 0
  · subst h0
    exact ⟨0, zero_mem_rootSet hUeqZero n, 0, rfl⟩
  · exact main _ s h0 rfl hs

/-- **The antichain**: root classes are pairwise `Reaches`-incomparable — a positive number of
steps from one root to another passes through an interior state one step before landing, and the
target's own region membership pins that intermediate state's OWN region membership: at the end
whose spread constant is non-negative, directly (one step, `U`'s own spread identity); at the end
whose spread constant is negative, from the source root's own region membership instead, carried
along by the iterated spread (`iterate_min'_spread`/`iterate_max'_spread`) — the case
`rootSet_cover`'s docstring notes `hUspread_sign_nonneg` is never needed for. No hypothesis on the
sign of `a`/`b` is added here: unlike `rootSet_cover`, the antichain property holds at every
`(a, b)`, `(0, 0)` included (there vacuously, `rootSet id n` being a singleton). -/
private theorem rootSet_antichain
    {U : (ℤ →₀ ZMod 2) → (ℤ →₀ ZMod 2)} {a b : ℤ}
    (hUzero : U 0 = 0)
    (hUeqZero : ∀ {s : ℤ →₀ ZMod 2}, U s = 0 ↔ s = 0)
    (hUinj : Function.Injective U)
    (hUmin' : ∀ {s : ℤ →₀ ZMod 2} (hne : s.support.Nonempty) (hne' : (U s).support.Nonempty),
      (U s).support.min' hne' = s.support.min' hne - a)
    (hUmax' : ∀ {s : ℤ →₀ ZMod 2} (hne : s.support.Nonempty) (hne' : (U s).support.Nonempty),
      (U s).support.max' hne' = s.support.max' hne + b)
    (n : ℕ) :
    IsAntichain (Reaches U) (mergeMk U '' rootSet U n) := by
  have hUiter_zero : ∀ t : ℕ, U^[t] (0 : ℤ →₀ ZMod 2) = 0 := by
    intro t
    induction t with
    | zero => simp
    | succ k ih => rw [Function.iterate_succ_apply', ih, hUzero]
  rintro _ ⟨r1, hr1, rfl⟩ _ ⟨r2, hr2, rfl⟩ hne ⟨j, hj⟩
  rw [mergeLaw_iterate_mergeMk] at hj
  have heq : U^[j] r1 = r2 := mergeMk_injective_of_injective hUinj hj
  subst heq
  have hr1r2 : r1 ≠ U^[j] r1 := fun h => hne (congrArg (mergeMk U) h)
  have hr1ne : r1 ≠ 0 := by
    rintro rfl
    exact hr1r2 (hUiter_zero j).symm
  have hj1 : 1 ≤ j := by
    rcases Nat.eq_zero_or_pos j with hj0 | hj1
    · exfalso; apply hr1r2; rw [hj0]; simp
    · exact hj1
  have hmne : U^[j - 1] r1 ≠ 0 := iterate_ne_zero hUeqZero hr1ne (j - 1)
  have hmne' : (U^[j - 1] r1).support.Nonempty := Finsupp.support_nonempty_iff.mpr hmne
  have hUmne : U (U^[j - 1] r1) ≠ 0 := fun h => hmne (hUeqZero.mp h)
  have hUmne' : (U (U^[j - 1] r1)).support.Nonempty := Finsupp.support_nonempty_iff.mpr hUmne
  have e : U^[j - 1 + 1] r1 = U (U^[j - 1] r1) := Function.iterate_succ_apply' U (j - 1) r1
  rw [Nat.sub_add_cancel hj1] at e
  rw [e] at hr2
  have hspreadMin := hUmin' hmne' hUmne'
  have hspreadMax := hUmax' hmne' hUmne'
  obtain ⟨hUmmin_ge, -⟩ := hr2.1 _ (Finset.min'_mem (U (U^[j - 1] r1)).support hUmne')
  obtain ⟨-, hUmmax_lt⟩ := hr2.1 _ (Finset.max'_mem (U (U^[j - 1] r1)).support hUmne')
  have hr1ne' : r1.support.Nonempty := Finsupp.support_nonempty_iff.mpr hr1ne
  have hr1min_ge : 0 ≤ r1.support.min' hr1ne' := (hr1.1 _ (Finset.min'_mem r1.support hr1ne')).1
  have hr1max_lt : r1.support.max' hr1ne' < (n : ℤ) :=
    (hr1.1 _ (Finset.max'_mem r1.support hr1ne')).2
  have hmmin1 : max a 0 ≤ (U^[j - 1] r1).support.min' hmne' := by
    rcases le_total 0 a with ha | ha
    · rw [max_eq_left ha]; omega
    · rw [max_eq_right ha]
      have hiter := iterate_min'_spread hUeqZero hUmin' hr1ne hr1ne' (j - 1) hmne'
      have hnn : (0 : ℤ) ≤ ((j - 1 : ℕ) : ℤ) * (-a) :=
        mul_nonneg (Int.natCast_nonneg _) (by omega)
      nlinarith [hiter, hr1min_ge, hnn]
  have hmmax2 : (U^[j - 1] r1).support.max' hmne' ≤ (n : ℤ) - 1 - max b 0 := by
    rcases le_total 0 b with hb | hb
    · rw [max_eq_left hb]; omega
    · rw [max_eq_right hb]
      have hiter := iterate_max'_spread hUeqZero hUmax' hr1ne hr1ne' (j - 1) hmne'
      have hnp : ((j - 1 : ℕ) : ℤ) * b ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (Int.natCast_nonneg _) hb
      nlinarith [hiter, hr1max_lt, hnp]
  have hmint : U^[j - 1] r1 ∈ interiorStates U n := by
    refine ⟨hmne, ?_, hr2.1⟩
    intro i hi
    have h1 := Finset.min'_le (U^[j - 1] r1).support i hi
    have h2 := Finset.le_max' (U^[j - 1] r1).support i hi
    have hmge0 : (0 : ℤ) ≤ max a 0 := le_max_right a 0
    have hbge0 : (0 : ℤ) ≤ max b 0 := le_max_right b 0
    exact ⟨by omega, by omega⟩
  exact hr2.2 ⟨U^[j - 1] r1, hmint, rfl⟩

/-- **The exact width, generic in the update AND in the two spread constants**: the same route as
`memWidth_rule90_derived_eq` and `memWidth_rule150_derived_eq` below, with the rule replaced by a
free `U` and the rule-specific facts by exactly the hypotheses `rootSet_cover`/`rootSet_antichain`
themselves consume. The added `hab : 0 < max a 0 + max b 0` is `rootSet_cover`'s own hypothesis,
not `rootSet_antichain`'s — the identity guard below (`(a, b) = (0, 0)`) is exactly the boundary
this draws. Route: the two supply `MemoryWidth.memWidth_eq_encard_of_rootSet`'s two hypotheses at
stage `0`, where the derived world's own stage is `regionStates n` (`Function.iterate_zero`,
`Set.image_id`); the image collapses to the root set's own cardinality by `U`'s injectivity. -/
theorem memWidth_derived_eq_encard_rootSet
    {U : (ℤ →₀ ZMod 2) → (ℤ →₀ ZMod 2)} {a b : ℤ}
    (hUzero : U 0 = 0)
    (hUeqZero : ∀ {s : ℤ →₀ ZMod 2}, U s = 0 ↔ s = 0)
    (hUinj : Function.Injective U)
    (hUmin' : ∀ {s : ℤ →₀ ZMod 2} (hne : s.support.Nonempty) (hne' : (U s).support.Nonempty),
      (U s).support.min' hne' = s.support.min' hne - a)
    (hUmax' : ∀ {s : ℤ →₀ ZMod 2} (hne : s.support.Nonempty) (hne' : (U s).support.Nonempty),
      (U s).support.max' hne' = s.support.max' hne + b)
    (hab : 0 < max a 0 + max b 0)
    (n : ℕ) :
    memWidth U (derivedStages U (regionStates n)) 0 = (rootSet U n).encard := by
  have hst : derivedStages U (regionStates n) 0 = regionStates n := by simp [derivedStages]
  have hsub : rootSet U n ⊆ derivedStages U (regionStates n) 0 := by
    rw [hst]; exact Set.sdiff_subset
  have hanti := rootSet_antichain hUzero hUeqZero hUinj hUmin' hUmax' n
  have hcover : ∀ s ∈ derivedStages U (regionStates n) 0, ∃ r ∈ rootSet U n,
      Reaches U (mergeMk U r) (mergeMk U s) := by
    rw [hst]
    intro s hs
    obtain ⟨r, hr, j, hj⟩ := rootSet_cover hUeqZero hUmin' hUmax' hab n s hs
    exact ⟨r, hr, j, by rw [mergeLaw_iterate_mergeMk, hj]⟩
  rw [memWidth_eq_encard_of_rootSet hsub hanti hcover]
  exact Function.Injective.encard_image (mergeMk_injective_of_injective hUinj) _

/-- **Grade B2, the capstone for `rule90`**: `memWidth_derived_eq_encard_rootSet` at `rule90`'s own
five facts, `(a, b) = (1, 1)`. -/
theorem memWidth_rule90_derived_eq {n : ℕ} :
    memWidth rule90 (derivedStages rule90 (regionStates n)) 0 = (rootSet rule90 n).encard :=
  memWidth_derived_eq_encard_rootSet (a := 1) (b := 1) rule90_zero rule90_eq_zero_iff
    rule90_injective rule90_support_min'_spread rule90_support_max'_spread (by norm_num) n

/-! ## The exact count, at `rule90` (grade B2, the count)

A window-indexed family, generic in its integer offset `a` and its width `w`, embeds
`Fin w → ZMod 2` bijectively onto the states supported on `[a, a + w)` — the same construction as
`leftEdgeMember` above, minus its pinned cell, instantiated at `[0, n)` for `regionStates` and at
`[1, n - 2]` for `interiorStates`. -/

private noncomputable def windowMember (a : ℤ) (w : ℕ) (g : Fin w → ZMod 2) : ℤ →₀ ZMod 2 :=
  Finsupp.mapDomain (fun i : Fin w => (i : ℤ) + a) (Finsupp.equivFunOnFinite.symm g)

private theorem windowEmbed_injective (a : ℤ) (w : ℕ) :
    Function.Injective (fun i : Fin w => (i : ℤ) + a) := by
  intro x y hxy
  simp only [add_left_inj] at hxy
  exact Fin.ext (by exact_mod_cast hxy)

private theorem windowMember_apply_mem (a : ℤ) (w : ℕ) (g : Fin w → ZMod 2) (i : Fin w) :
    windowMember a w g ((i : ℤ) + a) = g i := by
  simpa [windowMember] using
    Finsupp.mapDomain_apply_of_injective (windowEmbed_injective a w)
      (Finsupp.equivFunOnFinite.symm g) i

private theorem windowMember_outside (a : ℤ) (w : ℕ) (g : Fin w → ZMod 2) (x : ℤ)
    (hx : ¬ (a ≤ x ∧ x < a + w)) : windowMember a w g x = 0 := by
  apply Finsupp.mapDomain_of_notMem_range
  rintro ⟨i, hi⟩
  simp only [] at hi
  apply hx
  have h1 : (0 : ℤ) ≤ (i : ℤ) := by positivity
  have h2 : (i : ℕ) < w := i.isLt
  omega

private theorem windowMember_injective (a : ℤ) (w : ℕ) : Function.Injective (windowMember a w) := by
  intro g g' hgg'
  funext i
  rw [← windowMember_apply_mem a w g i, ← windowMember_apply_mem a w g' i, hgg']

private theorem windowMember_zero (a : ℤ) (w : ℕ) : windowMember a w 0 = 0 := by
  ext x
  by_cases hx : a ≤ x ∧ x < a + w
  · obtain ⟨i, hi⟩ : ∃ i : Fin w, (i : ℤ) + a = x := ⟨⟨(x - a).toNat, by omega⟩, by simp; omega⟩
    rw [← hi, windowMember_apply_mem]
    simp
  · rw [windowMember_outside a w 0 x hx]
    simp

private theorem card_window (w : ℕ) : (2 ^ w : ℕ∞) = ENat.card (Fin w → ZMod 2) := by
  rw [ENat.card_eq_coe_fintype_card, Fintype.card_fun]; simp [ZMod.card]

/-- The equality version of `Function.Injective.encard_range` (this Mathlib pin's own is stated as
`≤`, its proof's own middle step); reused at both windows below. -/
private theorem encard_range_of_injective {α β : Type*} {f : α → β} (hf : Function.Injective f) :
    (Set.range f).encard = ENat.card α := by
  rw [← Set.image_univ, hf.encard_image, Set.encard_univ]

private theorem regionStates_eq_range (n : ℕ) :
    regionStates n = Set.range (windowMember 0 n) := by
  apply Set.eq_of_subset_of_subset
  · intro s hs
    refine ⟨fun i => s ((i : ℤ) + 0), ?_⟩
    ext x
    by_cases hx : (0 : ℤ) ≤ x ∧ x < (0 : ℤ) + n
    · obtain ⟨i, hi⟩ : ∃ i : Fin n, (i : ℤ) + 0 = x := ⟨⟨x.toNat, by omega⟩, by simp; omega⟩
      rw [← hi, windowMember_apply_mem]
    · rw [windowMember_outside 0 n _ x hx]
      by_contra hne
      have hb := hs x (Finsupp.mem_support_iff.mpr (Ne.symm hne))
      exact hx ⟨hb.1, by omega⟩
  · rintro _ ⟨g, rfl⟩ i hi
    by_contra hcon
    rw [not_and_or, not_le, not_lt] at hcon
    have hz : windowMember 0 n g i = 0 := by
      apply windowMember_outside
      rintro ⟨h1, h2⟩
      rcases hcon with h | h <;> omega
    exact (Finsupp.mem_support_iff.mp hi) hz

private theorem card_regionStates (n : ℕ) : (regionStates n).encard = 2 ^ n := by
  rw [regionStates_eq_range, encard_range_of_injective (windowMember_injective 0 n)]
  exact (card_window n).symm

/-- **A window characterized by inequalities is a `windowMember` range**: the general form
`interiorStates_eq_window` above lands in, at an arbitrary offset `A` and width `w` (`A` here is a
BOUND VARIABLE local to this lemma, unrelated to the spread constant `a` elsewhere in this
section) — this is what `interiorStates_eq_range_diff` inlined at the one instance `[1, n - 2]`
before the endpoint-move generalization needed it at `[a⁺, n - 1 - b⁺]` too. -/
private theorem windowSet_eq_range_diff (A : ℤ) (w : ℕ) :
    {s : ℤ →₀ ZMod 2 | s ≠ 0 ∧ ∀ i ∈ s.support, A ≤ i ∧ i ≤ A + (w : ℤ) - 1} =
      Set.range (windowMember A w) \ {0} := by
  apply Set.eq_of_subset_of_subset
  · rintro s ⟨hs0, hsb⟩
    refine ⟨⟨fun i => s ((i : ℤ) + A), ?_⟩, hs0⟩
    ext x
    by_cases hx : A ≤ x ∧ x < A + w
    · obtain ⟨i, hi⟩ : ∃ i : Fin w, (i : ℤ) + A = x := ⟨⟨(x - A).toNat, by omega⟩, by
        simp; omega⟩
      rw [← hi, windowMember_apply_mem]
    · rw [windowMember_outside A w _ x hx]
      by_contra hne
      have hb := hsb x (Finsupp.mem_support_iff.mpr (Ne.symm hne))
      exact hx ⟨hb.1, by omega⟩
  · rintro s ⟨⟨g, rfl⟩, hg0⟩
    refine ⟨hg0, fun i hi => ?_⟩
    by_contra hcon
    rw [not_and_or, not_le, not_le] at hcon
    have hz : windowMember A w g i = 0 := by
      apply windowMember_outside
      rintro ⟨h1, h2⟩
      rcases hcon with h | h <;> omega
    exact (Finsupp.mem_support_iff.mp hi) hz

/-- **`card_interiorStates`, generic in the update and the two spread constants**: restated as
`(interiorStates U n).encard + 1 = 2 ^ (n - m)` for a natural `m` with `(m : ℤ) = a⁺ + b⁺` — at
`(a, b) = (1, 1)`, `m = 2`, the old statement this replaces. Route: `interiorStates_eq_window`
gives the inequality form, `windowSet_eq_range_diff` converts it to a `windowMember` range at
offset `a⁺` and width `n - m` (the bound arithmetic closing by `hm`/`hn`), and the rest is the
`windowMember`-cardinality argument `card_regionStates` already runs, minus the pinned zero
state. -/
private theorem card_interiorStates_of_hyps
    {U : (ℤ →₀ ZMod 2) → (ℤ →₀ ZMod 2)} {a b : ℤ}
    (hUeqZero : ∀ {s : ℤ →₀ ZMod 2}, U s = 0 ↔ s = 0)
    (hUmin' : ∀ {s : ℤ →₀ ZMod 2} (hne : s.support.Nonempty) (hne' : (U s).support.Nonempty),
      (U s).support.min' hne' = s.support.min' hne - a)
    (hUmax' : ∀ {s : ℤ →₀ ZMod 2} (hne : s.support.Nonempty) (hne' : (U s).support.Nonempty),
      (U s).support.max' hne' = s.support.max' hne + b)
    {n m : ℕ} (hm : (m : ℤ) = max a 0 + max b 0) (hn : m ≤ n) :
    (interiorStates U n).encard + 1 = 2 ^ (n - m) := by
  have hbeq : (n : ℤ) - 1 - max b 0 = max a 0 + ((n - m : ℕ) : ℤ) - 1 := by
    rw [Nat.cast_sub hn]; omega
  have hset : interiorStates U n =
      {s : ℤ →₀ ZMod 2 | s ≠ 0 ∧
        ∀ i ∈ s.support, max a 0 ≤ i ∧ i ≤ max a 0 + ((n - m : ℕ) : ℤ) - 1} := by
    rw [interiorStates_eq_window hUeqZero hUmin' hUmax' n, hbeq]
  rw [hset, windowSet_eq_range_diff (max a 0) (n - m)]
  have hzero_mem : (0 : ℤ →₀ ZMod 2) ∈ Set.range (windowMember (max a 0) (n - m)) :=
    ⟨0, windowMember_zero (max a 0) (n - m)⟩
  have heq := Set.encard_sdiff_add_encard_of_subset (Set.singleton_subset_iff.mpr hzero_mem)
  rw [Set.encard_singleton] at heq
  rw [encard_range_of_injective (windowMember_injective (max a 0) (n - m))] at heq
  rw [← card_window] at heq
  exact heq

/-- **The count, generic in the update and the two spread constants**: the region's `2 ^ n` states
split exactly into the roots and the images of the interior's `2 ^ (n - m) - 1` nonzero states,
`U` injective on the split, in addition form (`ℕ∞` subtraction is truncated) — at `(a, b) = (1,
1)`, `m = 2`, the paper's closed form `2 ^ n - 2 ^ (n - 2) + 1` this equation restates. NO sign
hypothesis on `a`/`b`: unlike `rootSet_cover`/`memWidth_derived_eq_encard_rootSet`, this holds at
every `(a, b)`, `(0, 0)` included (`guard_id_rootSet_load_bearing` below checks it there
directly). The route no longer needs the min'/max' spread identities for `himg` — the intrinsic
`interiorStates` already carries `U s ∈ regionStates n` as its own third conjunct. -/
theorem rootSet_encard_add_of_hyps
    {U : (ℤ →₀ ZMod 2) → (ℤ →₀ ZMod 2)} {a b : ℤ}
    (hUeqZero : ∀ {s : ℤ →₀ ZMod 2}, U s = 0 ↔ s = 0)
    (hUinj : Function.Injective U)
    (hUmin' : ∀ {s : ℤ →₀ ZMod 2} (hne : s.support.Nonempty) (hne' : (U s).support.Nonempty),
      (U s).support.min' hne' = s.support.min' hne - a)
    (hUmax' : ∀ {s : ℤ →₀ ZMod 2} (hne : s.support.Nonempty) (hne' : (U s).support.Nonempty),
      (U s).support.max' hne' = s.support.max' hne + b)
    {n m : ℕ} (hm : (m : ℤ) = max a 0 + max b 0) (hn : m ≤ n) :
    (rootSet U n).encard + 2 ^ (n - m) = 2 ^ n + 1 := by
  have himg : U '' interiorStates U n ⊆ regionStates n := by
    rintro _ ⟨r, hrint, rfl⟩
    exact hrint.2.2
  have h1 : (rootSet U n).encard + (U '' interiorStates U n).encard =
      (regionStates n).encard := Set.encard_sdiff_add_encard_of_subset himg
  have h2 : (U '' interiorStates U n).encard = (interiorStates U n).encard :=
    Function.Injective.encard_image hUinj (interiorStates U n)
  have h3 := card_regionStates n
  have h4 := card_interiorStates_of_hyps hUeqZero hUmin' hUmax' hm hn
  calc (rootSet U n).encard + 2 ^ (n - m)
      = (rootSet U n).encard + ((interiorStates U n).encard + 1) := by rw [h4]
    _ = ((rootSet U n).encard + (interiorStates U n).encard) + 1 := by rw [add_assoc]
    _ = ((rootSet U n).encard + (U '' interiorStates U n).encard) + 1 := by rw [h2]
    _ = (regionStates n).encard + 1 := by rw [h1]
    _ = 2 ^ n + 1 := by rw [h3]

/-- **Grade B2, the count for `rule90`** — `rootSet_encard_add_of_hyps` at `rule90`'s own facts,
`(a, b) = (1, 1)`, `m = 2`. -/
theorem rootSet_encard_add {n : ℕ} (hn : 2 ≤ n) :
    (rootSet rule90 n).encard + 2 ^ (n - 2) = 2 ^ n + 1 :=
  rootSet_encard_add_of_hyps (a := 1) (b := 1) rule90_eq_zero_iff rule90_injective
    rule90_support_min'_spread rule90_support_max'_spread (m := 2) (by norm_num) hn

/-- **Grade B2, the count for `rule150`**: the table-`150` twin `rootSet_encard_add` left paper-
level — `rootSet_encard_add_of_hyps` at `rule150`'s own facts, free once the generic form exists. -/
theorem rootSet_encard_add_rule150 {n : ℕ} (hn : 2 ≤ n) :
    (rootSet rule150 n).encard + 2 ^ (n - 2) = 2 ^ n + 1 :=
  rootSet_encard_add_of_hyps (a := 1) (b := 1) rule150_eq_zero_iff rule150_injective
    rule150_support_min'_spread rule150_support_max'_spread (m := 2) (by norm_num) hn

/-- **Grade B2, the capstone for `rule150`** — `memWidth_derived_eq_encard_rootSet` at `rule150`'s
own five facts, `(a, b) = (1, 1)`. -/
theorem memWidth_rule150_derived_eq {n : ℕ} :
    memWidth rule150 (derivedStages rule150 (regionStates n)) 0 = (rootSet rule150 n).encard :=
  memWidth_derived_eq_encard_rootSet (a := 1) (b := 1) rule150_zero rule150_eq_zero_iff
    rule150_injective rule150_support_min'_spread rule150_support_max'_spread (by norm_num) n

/-- **The identity guard, and it is load-bearing rather than decorative**: `id` meets all four
non-spread hypotheses at `(a, b) = (0, 0)` — `id 0 = 0`, the trivial kernel, injectivity, and both
spread identities at the constant `0` — yet the retained profile is the WHOLE region rather than a
size-one root count: `id` never merges anything (`Reaches id q q' ↔ q = q'`, since `mergeLaw id`
fixes every merge class), so the retained profile is its own antichain
(`MemoryWidth.memWidth_eq_encard_of_isAntichain`) of size `2 ^ n`, while `rootSet id n = {0}` has
a single element — matching `rootSet_encard_add_of_hyps` at `m = 0` (`1 + 2 ^ n = 2 ^ n + 1`) but
NOT `memWidth_derived_eq_encard_rootSet`, whose `hab` hypothesis fails exactly here
(`hUspread_sign_nonneg`'s boundary). The two sides of that would-be equation disagree outright,
`2 ^ n` against `1`, rather than merely lacking a proof. -/
theorem guard_id_rootSet_load_bearing (n : ℕ) :
    memWidth (id : (ℤ →₀ ZMod 2) → (ℤ →₀ ZMod 2))
        (derivedStages id (regionStates n)) 0 = 2 ^ n ∧
      (rootSet (id : (ℤ →₀ ZMod 2) → (ℤ →₀ ZMod 2)) n).encard = 1 := by
  constructor
  · have hst : derivedStages (id : (ℤ →₀ ZMod 2) → (ℤ →₀ ZMod 2)) (regionStates n) 0 =
        regionStates n := by simp [derivedStages]
    have hms : mergeStage (id : (ℤ →₀ ZMod 2) → (ℤ →₀ ZMod 2))
        (derivedStages id (regionStates n)) 0 = mergeMk id '' regionStates n := by
      change GrowingWorld.guestStage (fun _ s => mergeMk id s)
        (derivedStages id (regionStates n)) 0 = _
      rw [GrowingWorld.guestStage, hst]
    have hML : ∀ (j : ℕ) (q : MergeQuot (id : (ℤ →₀ ZMod 2) → (ℤ →₀ ZMod 2))),
        (mergeLaw (id : (ℤ →₀ ZMod 2) → (ℤ →₀ ZMod 2)))^[j] q = q := by
      intro j
      have hstep :
          ∀ q' : MergeQuot (id : (ℤ →₀ ZMod 2) → (ℤ →₀ ZMod 2)), mergeLaw id q' = q' := by
        intro q'
        induction q' using Quotient.ind with
        | _ a => rfl
      intro q
      induction j with
      | zero => simp
      | succ k ih => rw [Function.iterate_succ_apply', hstep, ih]
    have hanti : IsAntichain (Reaches (id : (ℤ →₀ ZMod 2) → (ℤ →₀ ZMod 2)))
        (mergeStage id (derivedStages id (regionStates n)) 0) := by
      rintro q1 - q2 - hne ⟨j, hj⟩
      rw [hML] at hj
      exact hne hj
    rw [memWidth_eq_encard_of_isAntichain hanti, hms,
      Function.Injective.encard_image (mergeMk_injective_of_injective Function.injective_id)]
    exact card_regionStates n
  · have hzero_mem : (0 : ℤ →₀ ZMod 2) ∈ regionStates n := fun i hi => by simp at hi
    have hint_eq : interiorStates (id : (ℤ →₀ ZMod 2) → (ℤ →₀ ZMod 2)) n =
        regionStates n \ {0} := by
      ext s
      simp only [interiorStates, id_eq, Set.mem_sdiff, Set.mem_ofPred_eq, Set.mem_singleton_iff]
      tauto
    have hrs : rootSet (id : (ℤ →₀ ZMod 2) → (ℤ →₀ ZMod 2)) n = {0} := by
      rw [rootSet, hint_eq,
        show (id : (ℤ →₀ ZMod 2) → (ℤ →₀ ZMod 2)) '' (regionStates n \ {0}) = regionStates n \ {0}
          from Set.image_id _]
      ext s
      simp only [Set.mem_sdiff, Set.mem_singleton_iff]
      constructor
      · rintro ⟨hreg, hnot⟩
        by_contra hne
        exact hnot ⟨hreg, hne⟩
      · rintro rfl
        exact ⟨hzero_mem, fun ⟨_, h⟩ => h rfl⟩
    rw [hrs, Set.encard_singleton]

/-! ## The permutive class at radius one

`rule90` and `rule150` are built as `Finsupp.mapDomain` shift sums, available only because both are
additive; a non-additive elementary table (rule `30` among them) needs the general construction.
A local table `f : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2` with `f 0 0 0 = 0` (quiescence, keeping the
image finitely supported) becomes a radius-one rule via `Finsupp.onFinset`; ONE-SIDED PERMUTIVITY,
in its solved (additive) form — `f a b c = a + g b c` on the left, `f a b c = c + h a b` on the
right, for some `g`/`h` — is exactly what a downward (resp. upward) induction from beyond the
support consumes to recover `s` from its image.

That a one-sided permutive quiescent local rule is injective on the finitely-supported
configurations of the line is CLASSICAL, not a new result of this module: the induction below is
proof economy, one route to that fact, over the carrier this development already works in. -/

/-- **A local table as a radius-one rule**, given quiescence: `Finsupp.onFinset` with the support
bound `s.support` widened by one at each end — if none of the three cells feeding `i` are in
`s.support`, quiescence forces the value at `i` to vanish too. -/
noncomputable def tableRule (f : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2) (hq : f 0 0 0 = 0)
    (s : ℤ →₀ ZMod 2) : ℤ →₀ ZMod 2 :=
  Finsupp.onFinset
    (s.support.image (· + 1) ∪ s.support.image (· - 1) ∪ s.support)
    (fun i => f (s (i - 1)) (s i) (s (i + 1)))
    (fun i hi => by
      by_contra hcon
      apply hi
      have h1 : s (i - 1) = 0 := by
        by_contra hc
        exact hcon (Finset.mem_union_left _ (Finset.mem_union_left _
          (Finset.mem_image.mpr ⟨i - 1, Finsupp.mem_support_iff.mpr hc, by omega⟩)))
      have h2 : s (i + 1) = 0 := by
        by_contra hc
        exact hcon (Finset.mem_union_left _ (Finset.mem_union_right _
          (Finset.mem_image.mpr ⟨i + 1, Finsupp.mem_support_iff.mpr hc, by omega⟩)))
      have h3 : s i = 0 := by
        by_contra hc
        exact hcon (Finset.mem_union_right _ (Finsupp.mem_support_iff.mpr hc))
      rw [h1, h2, h3]
      exact hq)

theorem tableRule_apply (f : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2) (hq : f 0 0 0 = 0)
    (s : ℤ →₀ ZMod 2) (i : ℤ) :
    tableRule f hq s i = f (s (i - 1)) (s i) (s (i + 1)) :=
  Finsupp.onFinset_apply

private theorem tableRule_zero (f : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2) (hq : f 0 0 0 = 0) :
    tableRule f hq 0 = 0 := by
  ext i
  rw [tableRule_apply]
  simpa using hq

private theorem zmod2_eq_one_of_ne_zero : ∀ a : ZMod 2, a ≠ 0 → a = 1 := by decide

/-- **Quiescence in `g`-form**: `f 0 0 0 = 0` becomes `g 0 0 = 0` under the left-permutive solved
form — the fact the right-spread lemma below draws on, with no further hypothesis. -/
private theorem leftPermutive_g00 {f : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2} (hq : f 0 0 0 = 0)
    {g : ZMod 2 → ZMod 2 → ZMod 2} (hg : ∀ a b c, f a b c = a + g b c) : g 0 0 = 0 := by
  have h := hg 0 0 0
  rw [hq] at h
  simpa using h.symm

/-- **Quiescence in `h`-form**, the right-permutive mirror of `leftPermutive_g00`. -/
private theorem rightPermutive_h00 {f : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2} (hq : f 0 0 0 = 0)
    {h : ZMod 2 → ZMod 2 → ZMod 2} (hh : ∀ a b c, f a b c = c + h a b) : h 0 0 = 0 := by
  have he := hh 0 0 0
  rw [hq] at he
  simpa using he.symm

private theorem tableRule_apply_leftPermutive {f : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2}
    (hq : f 0 0 0 = 0) {g : ZMod 2 → ZMod 2 → ZMod 2} (hg : ∀ a b c, f a b c = a + g b c)
    (s : ℤ →₀ ZMod 2) (i : ℤ) :
    tableRule f hq s i = s (i - 1) + g (s i) (s (i + 1)) := by
  rw [tableRule_apply, hg]

private theorem tableRule_apply_rightPermutive {f : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2}
    (hq : f 0 0 0 = 0) {h : ZMod 2 → ZMod 2 → ZMod 2} (hh : ∀ a b c, f a b c = c + h a b)
    (s : ℤ →₀ ZMod 2) (i : ℤ) :
    tableRule f hq s i = s (i + 1) + h (s (i - 1)) (s i) := by
  rw [tableRule_apply, hh]

/-- **Injective, left-permutive**, on the finitely-supported configurations of the line: a
downward induction from beyond both supports, tracking two consecutive cells at once —
knowing `s i` and `s (i + 1)` and the shared value `(U s) i`, the solved form `s (i - 1) = (U s) i +
g (s i) (s (i + 1))` determines `s (i - 1)`, so `U s = U s'` forces the two states equal cell by
cell, all the way down. No particular value of `g` is used — only that it is a well-defined
function — so this holds at every left-permutive quiescent table, not merely the four instantiated
below. -/
theorem tableRule_injective_of_leftPermutive {f : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2}
    (hq : f 0 0 0 = 0) {g : ZMod 2 → ZMod 2 → ZMod 2} (hg : ∀ a b c, f a b c = a + g b c) :
    Function.Injective (tableRule f hq) := by
  intro s s' hss'
  have hpt : ∀ i, s (i - 1) + g (s i) (s (i + 1)) = s' (i - 1) + g (s' i) (s' (i + 1)) := by
    intro i
    have h := DFunLike.congr_fun hss' i
    rwa [tableRule_apply_leftPermutive hq hg, tableRule_apply_leftPermutive hq hg] at h
  by_cases hU : (s.support ∪ s'.support).Nonempty
  · set N := (s.support ∪ s'.support).max' hU with hN_def
    have hb1 : s (N + 1) = 0 := by
      by_contra hc
      have hmem : N + 1 ∈ s.support ∪ s'.support :=
        Finset.mem_union_left _ (Finsupp.mem_support_iff.mpr hc)
      have := Finset.le_max' _ _ hmem
      omega
    have hb2 : s (N + 2) = 0 := by
      by_contra hc
      have hmem : N + 2 ∈ s.support ∪ s'.support :=
        Finset.mem_union_left _ (Finsupp.mem_support_iff.mpr hc)
      have := Finset.le_max' _ _ hmem
      omega
    have hb1' : s' (N + 1) = 0 := by
      by_contra hc
      have hmem : N + 1 ∈ s.support ∪ s'.support :=
        Finset.mem_union_right _ (Finsupp.mem_support_iff.mpr hc)
      have := Finset.le_max' _ _ hmem
      omega
    have hb2' : s' (N + 2) = 0 := by
      by_contra hc
      have hmem : N + 2 ∈ s.support ∪ s'.support :=
        Finset.mem_union_right _ (Finsupp.mem_support_iff.mpr hc)
      have := Finset.le_max' _ _ hmem
      omega
    have main : ∀ t : ℕ, s (N + 1 - t) = s' (N + 1 - t) ∧ s (N + 2 - t) = s' (N + 2 - t) := by
      intro t
      induction t with
      | zero =>
        simp only [Nat.cast_zero, sub_zero]
        exact ⟨hb1.trans hb1'.symm, hb2.trans hb2'.symm⟩
      | succ k ih =>
        obtain ⟨ih1, ih2⟩ := ih
        have hstep := hpt (N + 1 - (k : ℤ))
        have e1 : (N + 1 - (k : ℤ)) - 1 = N - (k : ℤ) := by omega
        have e2 : (N + 1 - (k : ℤ)) + 1 = N + 2 - (k : ℤ) := by omega
        rw [e1, e2] at hstep
        rw [ih1, ih2] at hstep
        have hcancel : s (N - (k : ℤ)) = s' (N - (k : ℤ)) := add_right_cancel hstep
        refine ⟨?_, ?_⟩
        · have e : N + 1 - ((↑(k + 1) : ℤ)) = N - (k : ℤ) := by push_cast; omega
          rw [e]; exact hcancel
        · have e : N + 2 - ((↑(k + 1) : ℤ)) = N + 1 - (k : ℤ) := by push_cast; omega
          rw [e]; exact ih1
    ext i
    by_cases hi : i ≤ N
    · have hnn : (0 : ℤ) ≤ N + 1 - i := by omega
      obtain ⟨t, ht⟩ : ∃ t : ℕ, (t : ℤ) = N + 1 - i := ⟨(N + 1 - i).toNat, Int.toNat_of_nonneg hnn⟩
      have hmain := (main t).1
      have e : N + 1 - (t : ℤ) = i := by omega
      rwa [e] at hmain
    · push Not at hi
      have hSi : s i = 0 := by
        by_contra hc
        have hmem : i ∈ s.support ∪ s'.support :=
          Finset.mem_union_left _ (Finsupp.mem_support_iff.mpr hc)
        have := Finset.le_max' _ _ hmem
        omega
      have hSi' : s' i = 0 := by
        by_contra hc
        have hmem : i ∈ s.support ∪ s'.support :=
          Finset.mem_union_right _ (Finsupp.mem_support_iff.mpr hc)
        have := Finset.le_max' _ _ hmem
        omega
      rw [hSi, hSi']
  · push Not at hU
    rw [Finset.union_eq_empty] at hU
    have hs0 : s = 0 := Finsupp.support_eq_empty.mp hU.1
    have hs0' : s' = 0 := Finsupp.support_eq_empty.mp hU.2
    rw [hs0, hs0']

/-- **Injective, right-permutive** — the mirror of `tableRule_injective_of_leftPermutive`: an
upward induction from beyond both supports, using `s (i + 1) = (U s) i + h (s (i - 1)) (s i)`. -/
theorem tableRule_injective_of_rightPermutive {f : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2}
    (hq : f 0 0 0 = 0) {h : ZMod 2 → ZMod 2 → ZMod 2} (hh : ∀ a b c, f a b c = c + h a b) :
    Function.Injective (tableRule f hq) := by
  intro s s' hss'
  have hpt : ∀ i, s (i + 1) + h (s (i - 1)) (s i) = s' (i + 1) + h (s' (i - 1)) (s' i) := by
    intro i
    have he := DFunLike.congr_fun hss' i
    rwa [tableRule_apply_rightPermutive hq hh, tableRule_apply_rightPermutive hq hh] at he
  by_cases hU : (s.support ∪ s'.support).Nonempty
  · set L := (s.support ∪ s'.support).min' hU with hL_def
    have hb1 : s (L - 1) = 0 := by
      by_contra hc
      have hmem : L - 1 ∈ s.support ∪ s'.support :=
        Finset.mem_union_left _ (Finsupp.mem_support_iff.mpr hc)
      have := Finset.min'_le _ _ hmem
      omega
    have hb2 : s (L - 2) = 0 := by
      by_contra hc
      have hmem : L - 2 ∈ s.support ∪ s'.support :=
        Finset.mem_union_left _ (Finsupp.mem_support_iff.mpr hc)
      have := Finset.min'_le _ _ hmem
      omega
    have hb1' : s' (L - 1) = 0 := by
      by_contra hc
      have hmem : L - 1 ∈ s.support ∪ s'.support :=
        Finset.mem_union_right _ (Finsupp.mem_support_iff.mpr hc)
      have := Finset.min'_le _ _ hmem
      omega
    have hb2' : s' (L - 2) = 0 := by
      by_contra hc
      have hmem : L - 2 ∈ s.support ∪ s'.support :=
        Finset.mem_union_right _ (Finsupp.mem_support_iff.mpr hc)
      have := Finset.min'_le _ _ hmem
      omega
    have main : ∀ t : ℕ, s (L - 2 + t) = s' (L - 2 + t) ∧ s (L - 1 + t) = s' (L - 1 + t) := by
      intro t
      induction t with
      | zero =>
        simp only [Nat.cast_zero, add_zero]
        exact ⟨hb2.trans hb2'.symm, hb1.trans hb1'.symm⟩
      | succ k ih =>
        obtain ⟨ih1, ih2⟩ := ih
        have hstep := hpt (L - 1 + (k : ℤ))
        have e1 : (L - 1 + (k : ℤ)) - 1 = L - 2 + (k : ℤ) := by omega
        have e2 : (L - 1 + (k : ℤ)) + 1 = L + (k : ℤ) := by omega
        rw [e1, e2] at hstep
        rw [ih1, ih2] at hstep
        have hcancel : s (L + (k : ℤ)) = s' (L + (k : ℤ)) := add_right_cancel hstep
        refine ⟨?_, ?_⟩
        · have e : L - 2 + ((↑(k + 1) : ℤ)) = L - 1 + (k : ℤ) := by push_cast; omega
          rw [e]; exact ih2
        · have e : L - 1 + ((↑(k + 1) : ℤ)) = L + (k : ℤ) := by push_cast; omega
          rw [e]; exact hcancel
    ext i
    by_cases hi : L ≤ i
    · have hnn : (0 : ℤ) ≤ i - (L - 1) := by omega
      obtain ⟨t, ht⟩ : ∃ t : ℕ, (t : ℤ) = i - (L - 1) :=
        ⟨(i - (L - 1)).toNat, Int.toNat_of_nonneg hnn⟩
      have hmain := (main t).2
      have e : L - 1 + (t : ℤ) = i := by omega
      rwa [e] at hmain
    · push Not at hi
      have hSi : s i = 0 := by
        by_contra hc
        have hmem : i ∈ s.support ∪ s'.support :=
          Finset.mem_union_left _ (Finsupp.mem_support_iff.mpr hc)
        have := Finset.min'_le _ _ hmem
        omega
      have hSi' : s' i = 0 := by
        by_contra hc
        have hmem : i ∈ s.support ∪ s'.support :=
          Finset.mem_union_right _ (Finsupp.mem_support_iff.mpr hc)
        have := Finset.min'_le _ _ hmem
        omega
      rw [hSi, hSi']
  · push Not at hU
    rw [Finset.union_eq_empty] at hU
    have hs0 : s = 0 := Finsupp.support_eq_empty.mp hU.1
    have hs0' : s' = 0 := Finsupp.support_eq_empty.mp hU.2
    rw [hs0, hs0']

/-- **Left-permutive, exact right spread — free from quiescence alone**: `f 1 0 0 = 1 + g 0 0 = 1`
is the same condition as `hq`'s own `g 0 0 = 0`, so no further hypothesis on `g` is needed. -/
theorem leftPermutive_support_max'_spread
    {f : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2} (hq : f 0 0 0 = 0)
    {g : ZMod 2 → ZMod 2 → ZMod 2} (hg : ∀ a b c, f a b c = a + g b c)
    {s : ℤ →₀ ZMod 2} (hne : s.support.Nonempty) (hne' : (tableRule f hq s).support.Nonempty) :
    (tableRule f hq s).support.max' hne' = s.support.max' hne + 1 := by
  have hg00 : g 0 0 = 0 := leftPermutive_g00 hq hg
  set M := s.support.max' hne with hM_def
  rw [Finset.max'_eq_iff]
  refine ⟨?_, ?_⟩
  · rw [Finsupp.mem_support_iff, tableRule_apply_leftPermutive hq hg]
    have h1 : s (M + 1) = 0 := by
      by_contra hc
      have hmem : M + 1 ∈ s.support := Finsupp.mem_support_iff.mpr hc
      have := Finset.le_max' s.support (M + 1) hmem
      omega
    have h2 : s (M + 1 + 1) = 0 := by
      by_contra hc
      have hmem : M + 1 + 1 ∈ s.support := Finsupp.mem_support_iff.mpr hc
      have := Finset.le_max' s.support (M + 1 + 1) hmem
      omega
    have h3 : s (M + 1 - 1) = s M := by
      have e : M + 1 - 1 = M := by omega
      rw [e]
    rw [h3, h1, h2, hg00, add_zero]
    exact Finsupp.mem_support_iff.mp (Finset.max'_mem s.support hne)
  · intro b hb
    rw [Finsupp.mem_support_iff, tableRule_apply_leftPermutive hq hg] at hb
    by_contra hlt
    push Not at hlt
    apply hb
    have h1 : s (b - 1) = 0 := by
      by_contra hc
      have hmem : b - 1 ∈ s.support := Finsupp.mem_support_iff.mpr hc
      have := Finset.le_max' s.support (b - 1) hmem
      omega
    have h2 : s b = 0 := by
      by_contra hc
      have hmem : b ∈ s.support := Finsupp.mem_support_iff.mpr hc
      have := Finset.le_max' s.support b hmem
      omega
    have h3 : s (b + 1) = 0 := by
      by_contra hc
      have hmem : b + 1 ∈ s.support := Finsupp.mem_support_iff.mpr hc
      have := Finset.le_max' s.support (b + 1) hmem
      omega
    rw [h1, h2, h3, hg00, add_zero]

/-- **Left-permutive, exact left spread — the one further bit beyond quiescence**: `f 0 0 1 = g 0 1`
must be `1` (table `30`/`90`/`150`/`210` all meet it; the class this hypothesis excludes is exactly
what the guard at the end of this section exhibits). -/
theorem leftPermutive_support_min'_spread
    {f : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2} (hq : f 0 0 0 = 0)
    {g : ZMod 2 → ZMod 2 → ZMod 2} (hg : ∀ a b c, f a b c = a + g b c) (hg01 : g 0 1 = 1)
    {s : ℤ →₀ ZMod 2} (hne : s.support.Nonempty) (hne' : (tableRule f hq s).support.Nonempty) :
    (tableRule f hq s).support.min' hne' = s.support.min' hne - 1 := by
  set m := s.support.min' hne with hm_def
  rw [Finset.min'_eq_iff]
  refine ⟨?_, ?_⟩
  · rw [Finsupp.mem_support_iff, tableRule_apply_leftPermutive hq hg]
    have h1 : s (m - 1 - 1) = 0 := by
      by_contra hc
      have hmem : m - 1 - 1 ∈ s.support := Finsupp.mem_support_iff.mpr hc
      have := Finset.min'_le s.support (m - 1 - 1) hmem
      omega
    have h2 : s (m - 1) = 0 := by
      by_contra hc
      have hmem : m - 1 ∈ s.support := Finsupp.mem_support_iff.mpr hc
      have := Finset.min'_le s.support (m - 1) hmem
      omega
    have h3 : s (m - 1 + 1) = s m := by
      have e : m - 1 + 1 = m := by omega
      rw [e]
    have hsm : s m = 1 :=
      zmod2_eq_one_of_ne_zero _ (Finsupp.mem_support_iff.mp (Finset.min'_mem s.support hne))
    rw [h1, h2, h3, hsm, hg01]
    decide
  · intro b hb
    rw [Finsupp.mem_support_iff, tableRule_apply_leftPermutive hq hg] at hb
    by_contra hlt
    push Not at hlt
    apply hb
    have h1 : s (b - 1) = 0 := by
      by_contra hc
      have hmem : b - 1 ∈ s.support := Finsupp.mem_support_iff.mpr hc
      have := Finset.min'_le s.support (b - 1) hmem
      omega
    have h2 : s b = 0 := by
      by_contra hc
      have hmem : b ∈ s.support := Finsupp.mem_support_iff.mpr hc
      have := Finset.min'_le s.support b hmem
      omega
    have h3 : s (b + 1) = 0 := by
      by_contra hc
      have hmem : b + 1 ∈ s.support := Finsupp.mem_support_iff.mpr hc
      have := Finset.min'_le s.support (b + 1) hmem
      omega
    rw [h1, h2, h3, leftPermutive_g00 hq hg, add_zero]

/-- **Right-permutive, exact left spread — free from quiescence alone**, the mirror of
`leftPermutive_support_max'_spread`. -/
theorem rightPermutive_support_min'_spread
    {f : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2} (hq : f 0 0 0 = 0)
    {h : ZMod 2 → ZMod 2 → ZMod 2} (hh : ∀ a b c, f a b c = c + h a b)
    {s : ℤ →₀ ZMod 2} (hne : s.support.Nonempty) (hne' : (tableRule f hq s).support.Nonempty) :
    (tableRule f hq s).support.min' hne' = s.support.min' hne - 1 := by
  have hh00 : h 0 0 = 0 := rightPermutive_h00 hq hh
  set m := s.support.min' hne with hm_def
  rw [Finset.min'_eq_iff]
  refine ⟨?_, ?_⟩
  · rw [Finsupp.mem_support_iff, tableRule_apply_rightPermutive hq hh]
    have h1 : s (m - 1 - 1) = 0 := by
      by_contra hc
      have hmem : m - 1 - 1 ∈ s.support := Finsupp.mem_support_iff.mpr hc
      have := Finset.min'_le s.support (m - 1 - 1) hmem
      omega
    have h2 : s (m - 1) = 0 := by
      by_contra hc
      have hmem : m - 1 ∈ s.support := Finsupp.mem_support_iff.mpr hc
      have := Finset.min'_le s.support (m - 1) hmem
      omega
    have h3 : s (m - 1 + 1) = s m := by
      have e : m - 1 + 1 = m := by omega
      rw [e]
    rw [h3, h1, h2, hh00, add_zero]
    exact Finsupp.mem_support_iff.mp (Finset.min'_mem s.support hne)
  · intro b hb
    rw [Finsupp.mem_support_iff, tableRule_apply_rightPermutive hq hh] at hb
    by_contra hlt
    push Not at hlt
    apply hb
    have h1 : s (b - 1) = 0 := by
      by_contra hc
      have hmem : b - 1 ∈ s.support := Finsupp.mem_support_iff.mpr hc
      have := Finset.min'_le s.support (b - 1) hmem
      omega
    have h2 : s b = 0 := by
      by_contra hc
      have hmem : b ∈ s.support := Finsupp.mem_support_iff.mpr hc
      have := Finset.min'_le s.support b hmem
      omega
    have h3 : s (b + 1) = 0 := by
      by_contra hc
      have hmem : b + 1 ∈ s.support := Finsupp.mem_support_iff.mpr hc
      have := Finset.min'_le s.support (b + 1) hmem
      omega
    rw [h1, h2, h3, hh00, add_zero]

/-- **Right-permutive, exact right spread — the one further bit beyond quiescence**: `f 1 0 0 =
h 1 0` must be `1` (tables `86`/`154` meet it; table `170`'s guard at the end of this section is
exactly this bit failing). The mirror of `leftPermutive_support_min'_spread`. -/
theorem rightPermutive_support_max'_spread
    {f : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2} (hq : f 0 0 0 = 0)
    {h : ZMod 2 → ZMod 2 → ZMod 2} (hh : ∀ a b c, f a b c = c + h a b) (hh10 : h 1 0 = 1)
    {s : ℤ →₀ ZMod 2} (hne : s.support.Nonempty) (hne' : (tableRule f hq s).support.Nonempty) :
    (tableRule f hq s).support.max' hne' = s.support.max' hne + 1 := by
  set M := s.support.max' hne with hM_def
  rw [Finset.max'_eq_iff]
  refine ⟨?_, ?_⟩
  · rw [Finsupp.mem_support_iff, tableRule_apply_rightPermutive hq hh]
    have h1 : s (M + 1 + 1) = 0 := by
      by_contra hc
      have hmem : M + 1 + 1 ∈ s.support := Finsupp.mem_support_iff.mpr hc
      have := Finset.le_max' s.support (M + 1 + 1) hmem
      omega
    have h2 : s (M + 1) = 0 := by
      by_contra hc
      have hmem : M + 1 ∈ s.support := Finsupp.mem_support_iff.mpr hc
      have := Finset.le_max' s.support (M + 1) hmem
      omega
    have h3 : s (M + 1 - 1) = s M := by
      have e : M + 1 - 1 = M := by omega
      rw [e]
    have hsM : s M = 1 :=
      zmod2_eq_one_of_ne_zero _ (Finsupp.mem_support_iff.mp (Finset.max'_mem s.support hne))
    rw [h1, h2, h3, hsM, hh10]
    decide
  · intro b hb
    rw [Finsupp.mem_support_iff, tableRule_apply_rightPermutive hq hh] at hb
    by_contra hlt
    push Not at hlt
    apply hb
    have h1 : s (b - 1) = 0 := by
      by_contra hc
      have hmem : b - 1 ∈ s.support := Finsupp.mem_support_iff.mpr hc
      have := Finset.le_max' s.support (b - 1) hmem
      omega
    have h2 : s b = 0 := by
      by_contra hc
      have hmem : b ∈ s.support := Finsupp.mem_support_iff.mpr hc
      have := Finset.le_max' s.support b hmem
      omega
    have h3 : s (b + 1) = 0 := by
      by_contra hc
      have hmem : b + 1 ∈ s.support := Finsupp.mem_support_iff.mpr hc
      have := Finset.le_max' s.support (b + 1) hmem
      omega
    rw [h1, h2, h3, rightPermutive_h00 hq hh, add_zero]

/-! ## Four non-additive elementary tables, at radius one

`rule30`/`rule210` (left-permutive) and `rule86`/`rule154` (right-permutive), each with its local
rule given explicitly and checked against the standard elementary-CA numbering (bit `4a + 2b + c`
of the rule number) by direct computation. Each `g`/`h` is read straight off the row:
no `decide` over the table space is needed to instantiate the class capstone. -/

private theorem eqZero_of_injective_of_zero {U : (ℤ →₀ ZMod 2) → (ℤ →₀ ZMod 2)} (hUzero : U 0 = 0)
    (hUinj : Function.Injective U) {s : ℤ →₀ ZMod 2} : U s = 0 ↔ s = 0 :=
  ⟨fun h => hUinj (h.trans hUzero.symm), fun h => h ▸ hUzero⟩

private theorem encard_pow_ne_top (n : ℕ) : (2 : ℕ∞) ^ n ≠ ⊤ := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [pow_succ]
    exact WithTop.mul_ne_top ih (by decide)

/-- **Any two tables meeting `rootSet_encard_add_of_hyps`'s hypotheses at the same `n` have the
same root count**: both root sets satisfy the same additive equation, and the added term
`2 ^ (n - 2)` is finite, so `WithTop.add_right_cancel` determines the same `encard` on both
sides. -/
private theorem rootSet_encard_eq_of_hyps_eq {U V : (ℤ →₀ ZMod 2) → (ℤ →₀ ZMod 2)} {n : ℕ}
    (hU : (rootSet U n).encard + 2 ^ (n - 2) = 2 ^ n + 1)
    (hV : (rootSet V n).encard + 2 ^ (n - 2) = 2 ^ n + 1) :
    (rootSet U n).encard = (rootSet V n).encard :=
  WithTop.add_right_cancel (encard_pow_ne_top (n - 2)) (hU.trans hV.symm)

/-- **Table `30`**, `f a b c = a + b + c + b·c`: left-permutive, `g b c = b + c + b·c`,
non-additive. -/
def f30 (a b c : ZMod 2) : ZMod 2 := a + b + c + b * c

private def g30 (b c : ZMod 2) : ZMod 2 := b + c + b * c

/-- `f30 0 0 0 = 0`. -/
theorem hq30 : f30 0 0 0 = 0 := by decide

private theorem hg30 : ∀ a b c, f30 a b c = a + g30 b c := by
  intro a b c; unfold f30 g30; ring

private theorem hg30_01 : g30 0 1 = 1 := by decide

/-- **Elementary table `30`, radius one**, as a `tableRule`. -/
noncomputable def rule30 : (ℤ →₀ ZMod 2) → (ℤ →₀ ZMod 2) := tableRule f30 hq30

private theorem rule30_zero : rule30 0 = 0 := tableRule_zero f30 hq30

private theorem rule30_injective : Function.Injective rule30 :=
  tableRule_injective_of_leftPermutive hq30 hg30

private theorem rule30_eq_zero_iff : ∀ {s : ℤ →₀ ZMod 2}, rule30 s = 0 ↔ s = 0 :=
  eqZero_of_injective_of_zero rule30_zero rule30_injective

private theorem rule30_support_min'_spread {s : ℤ →₀ ZMod 2} (hne : s.support.Nonempty)
    (hne' : (rule30 s).support.Nonempty) :
    (rule30 s).support.min' hne' = s.support.min' hne - 1 :=
  leftPermutive_support_min'_spread hq30 hg30 hg30_01 hne hne'

private theorem rule30_support_max'_spread {s : ℤ →₀ ZMod 2} (hne : s.support.Nonempty)
    (hne' : (rule30 s).support.Nonempty) :
    (rule30 s).support.max' hne' = s.support.max' hne + 1 :=
  leftPermutive_support_max'_spread hq30 hg30 hne hne'

/-- **Grade B2, the capstone for `rule30`**. -/
theorem memWidth_rule30_derived_eq {n : ℕ} :
    memWidth rule30 (derivedStages rule30 (regionStates n)) 0 = (rootSet rule30 n).encard :=
  memWidth_derived_eq_encard_rootSet (a := 1) (b := 1) rule30_zero rule30_eq_zero_iff
    rule30_injective rule30_support_min'_spread rule30_support_max'_spread (by norm_num) n

/-- **Grade B2, the count for `rule30`**. -/
theorem rootSet_encard_add_rule30 {n : ℕ} (hn : 2 ≤ n) :
    (rootSet rule30 n).encard + 2 ^ (n - 2) = 2 ^ n + 1 :=
  rootSet_encard_add_of_hyps (a := 1) (b := 1) rule30_eq_zero_iff rule30_injective
    rule30_support_min'_spread rule30_support_max'_spread (m := 2) (by norm_num) hn

/-- **The headline**: rule `30`'s derived-stage width from an `n`-cell region is exactly rule
`90`'s, at `2 ≤ n` — both root sets satisfy the same additive equation. -/
theorem memWidth_rule30_derived_eq_rule90 {n : ℕ} (hn : 2 ≤ n) :
    memWidth rule30 (derivedStages rule30 (regionStates n)) 0 =
      memWidth rule90 (derivedStages rule90 (regionStates n)) 0 := by
  rw [memWidth_rule30_derived_eq, memWidth_rule90_derived_eq,
    rootSet_encard_eq_of_hyps_eq (rootSet_encard_add_rule30 hn) (rootSet_encard_add hn)]

/-- **Table `210`**, `f a b c = a + c + b·c`: left-permutive, `g b c = c + b·c`, non-additive. -/
def f210 (a b c : ZMod 2) : ZMod 2 := a + c + b * c

private def g210 (b c : ZMod 2) : ZMod 2 := c + b * c

/-- `f210 0 0 0 = 0`. -/
theorem hq210 : f210 0 0 0 = 0 := by decide

private theorem hg210 : ∀ a b c, f210 a b c = a + g210 b c := by
  intro a b c; unfold f210 g210; ring

private theorem hg210_01 : g210 0 1 = 1 := by decide

/-- **Elementary table `210`, radius one**, as a `tableRule`. -/
noncomputable def rule210 : (ℤ →₀ ZMod 2) → (ℤ →₀ ZMod 2) := tableRule f210 hq210

private theorem rule210_zero : rule210 0 = 0 := tableRule_zero f210 hq210

private theorem rule210_injective : Function.Injective rule210 :=
  tableRule_injective_of_leftPermutive hq210 hg210

private theorem rule210_eq_zero_iff : ∀ {s : ℤ →₀ ZMod 2}, rule210 s = 0 ↔ s = 0 :=
  eqZero_of_injective_of_zero rule210_zero rule210_injective

private theorem rule210_support_min'_spread {s : ℤ →₀ ZMod 2} (hne : s.support.Nonempty)
    (hne' : (rule210 s).support.Nonempty) :
    (rule210 s).support.min' hne' = s.support.min' hne - 1 :=
  leftPermutive_support_min'_spread hq210 hg210 hg210_01 hne hne'

private theorem rule210_support_max'_spread {s : ℤ →₀ ZMod 2} (hne : s.support.Nonempty)
    (hne' : (rule210 s).support.Nonempty) :
    (rule210 s).support.max' hne' = s.support.max' hne + 1 :=
  leftPermutive_support_max'_spread hq210 hg210 hne hne'

/-- **Grade B2, the capstone for `rule210`**. -/
theorem memWidth_rule210_derived_eq {n : ℕ} :
    memWidth rule210 (derivedStages rule210 (regionStates n)) 0 = (rootSet rule210 n).encard :=
  memWidth_derived_eq_encard_rootSet (a := 1) (b := 1) rule210_zero rule210_eq_zero_iff
    rule210_injective rule210_support_min'_spread rule210_support_max'_spread (by norm_num) n

/-- **Grade B2, the count for `rule210`**. -/
theorem rootSet_encard_add_rule210 {n : ℕ} (hn : 2 ≤ n) :
    (rootSet rule210 n).encard + 2 ^ (n - 2) = 2 ^ n + 1 :=
  rootSet_encard_add_of_hyps (a := 1) (b := 1) rule210_eq_zero_iff rule210_injective
    rule210_support_min'_spread rule210_support_max'_spread (m := 2) (by norm_num) hn

/-- **Table `86`**, `f a b c = a + b + c + a·b`: right-permutive, `h a b = a + b + a·b`,
non-additive. -/
def f86 (a b c : ZMod 2) : ZMod 2 := a + b + c + a * b

private def h86 (a b : ZMod 2) : ZMod 2 := a + b + a * b

/-- `f86 0 0 0 = 0`. -/
theorem hq86 : f86 0 0 0 = 0 := by decide

private theorem hh86 : ∀ a b c, f86 a b c = c + h86 a b := by
  intro a b c; unfold f86 h86; ring

private theorem hh86_10 : h86 1 0 = 1 := by decide

/-- **Elementary table `86`, radius one**, as a `tableRule`. -/
noncomputable def rule86 : (ℤ →₀ ZMod 2) → (ℤ →₀ ZMod 2) := tableRule f86 hq86

private theorem rule86_zero : rule86 0 = 0 := tableRule_zero f86 hq86

private theorem rule86_injective : Function.Injective rule86 :=
  tableRule_injective_of_rightPermutive hq86 hh86

private theorem rule86_eq_zero_iff : ∀ {s : ℤ →₀ ZMod 2}, rule86 s = 0 ↔ s = 0 :=
  eqZero_of_injective_of_zero rule86_zero rule86_injective

private theorem rule86_support_min'_spread {s : ℤ →₀ ZMod 2} (hne : s.support.Nonempty)
    (hne' : (rule86 s).support.Nonempty) :
    (rule86 s).support.min' hne' = s.support.min' hne - 1 :=
  rightPermutive_support_min'_spread hq86 hh86 hne hne'

private theorem rule86_support_max'_spread {s : ℤ →₀ ZMod 2} (hne : s.support.Nonempty)
    (hne' : (rule86 s).support.Nonempty) :
    (rule86 s).support.max' hne' = s.support.max' hne + 1 :=
  rightPermutive_support_max'_spread hq86 hh86 hh86_10 hne hne'

/-- **Grade B2, the capstone for `rule86`**. -/
theorem memWidth_rule86_derived_eq {n : ℕ} :
    memWidth rule86 (derivedStages rule86 (regionStates n)) 0 = (rootSet rule86 n).encard :=
  memWidth_derived_eq_encard_rootSet (a := 1) (b := 1) rule86_zero rule86_eq_zero_iff
    rule86_injective rule86_support_min'_spread rule86_support_max'_spread (by norm_num) n

/-- **Grade B2, the count for `rule86`**. -/
theorem rootSet_encard_add_rule86 {n : ℕ} (hn : 2 ≤ n) :
    (rootSet rule86 n).encard + 2 ^ (n - 2) = 2 ^ n + 1 :=
  rootSet_encard_add_of_hyps (a := 1) (b := 1) rule86_eq_zero_iff rule86_injective
    rule86_support_min'_spread rule86_support_max'_spread (m := 2) (by norm_num) hn

/-- **Table `154`**, `f a b c = a + c + a·b`: right-permutive, `h a b = a + a·b`, non-additive. -/
def f154 (a b c : ZMod 2) : ZMod 2 := a + c + a * b

private def h154 (a b : ZMod 2) : ZMod 2 := a + a * b

/-- `f154 0 0 0 = 0`. -/
theorem hq154 : f154 0 0 0 = 0 := by decide

private theorem hh154 : ∀ a b c, f154 a b c = c + h154 a b := by
  intro a b c; unfold f154 h154; ring

private theorem hh154_10 : h154 1 0 = 1 := by decide

/-- **Elementary table `154`, radius one**, as a `tableRule`. -/
noncomputable def rule154 : (ℤ →₀ ZMod 2) → (ℤ →₀ ZMod 2) := tableRule f154 hq154

private theorem rule154_zero : rule154 0 = 0 := tableRule_zero f154 hq154

private theorem rule154_injective : Function.Injective rule154 :=
  tableRule_injective_of_rightPermutive hq154 hh154

private theorem rule154_eq_zero_iff : ∀ {s : ℤ →₀ ZMod 2}, rule154 s = 0 ↔ s = 0 :=
  eqZero_of_injective_of_zero rule154_zero rule154_injective

private theorem rule154_support_min'_spread {s : ℤ →₀ ZMod 2} (hne : s.support.Nonempty)
    (hne' : (rule154 s).support.Nonempty) :
    (rule154 s).support.min' hne' = s.support.min' hne - 1 :=
  rightPermutive_support_min'_spread hq154 hh154 hne hne'

private theorem rule154_support_max'_spread {s : ℤ →₀ ZMod 2} (hne : s.support.Nonempty)
    (hne' : (rule154 s).support.Nonempty) :
    (rule154 s).support.max' hne' = s.support.max' hne + 1 :=
  rightPermutive_support_max'_spread hq154 hh154 hh154_10 hne hne'

/-- **Grade B2, the capstone for `rule154`**. -/
theorem memWidth_rule154_derived_eq {n : ℕ} :
    memWidth rule154 (derivedStages rule154 (regionStates n)) 0 = (rootSet rule154 n).encard :=
  memWidth_derived_eq_encard_rootSet (a := 1) (b := 1) rule154_zero rule154_eq_zero_iff
    rule154_injective rule154_support_min'_spread rule154_support_max'_spread (by norm_num) n

/-- **Grade B2, the count for `rule154`**. -/
theorem rootSet_encard_add_rule154 {n : ℕ} (hn : 2 ≤ n) :
    (rootSet rule154 n).encard + 2 ^ (n - 2) = 2 ^ n + 1 :=
  rootSet_encard_add_of_hyps (a := 1) (b := 1) rule154_eq_zero_iff rule154_injective
    rule154_support_min'_spread rule154_support_max'_spread (m := 2) (by norm_num) hn

/-! ## The shift guard: quiescent and permutive is not enough

Table `170`, `f a b c = c`, is the pure right shift: right-permutive trivially (`h ≡ 0`) and
quiescent, exactly like `rule86`/`rule154` above, but its spread is one-sided — `f 1 0 0 = 0`, so
`rightPermutive_support_max'_spread`'s extra bit (`h 1 0 = 1`) fails, and the right-hand end does
not advance, it retreats. Exact spread controls the VALUE the count closes to, not merely whether
the machinery applies: the shift is permutive and quiescent and still gets a different root count
(`2 ^ (n - 1) + 1`, proved below at the endpoint-move generalization's own `(a, b) = (1, -1)`, not
via the class-level lemma this guard shows insufficient) from the six tables above. -/

/-- **Table `170`**, `f a b c = c`: the pure right shift, `(rule170 s) i = s (i + 1)`,
right-permutive trivially (`h ≡ 0`). -/
def f170 (_a _b c : ZMod 2) : ZMod 2 := c

/-- `f170 0 0 0 = 0`. -/
theorem hq170 : f170 0 0 0 = 0 := by decide

/-- **The pure shift, as a table rule**: `(rule170 s) i = s (i + 1)`. -/
noncomputable def rule170 : (ℤ →₀ ZMod 2) → (ℤ →₀ ZMod 2) := tableRule f170 hq170

theorem rule170_apply (s : ℤ →₀ ZMod 2) (i : ℤ) : rule170 s i = s (i + 1) := by
  change tableRule f170 hq170 s i = s (i + 1)
  rw [tableRule_apply]
  rfl

/-- **Guard**: the exact right-spread hypothesis is not implied by quiescence and (right-)
permutivity alone. Witness `Finsupp.single 0 1`: its `rule170`-image is supported only at `-1`, one
BELOW its own support max `0`, not one above. -/
theorem guard_rule170_max'_spread_load_bearing :
    ∃ (s : ℤ →₀ ZMod 2) (hne : s.support.Nonempty) (hne' : (rule170 s).support.Nonempty),
      (rule170 s).support.max' hne' ≠ s.support.max' hne + 1 := by
  have hne : (Finsupp.single (0 : ℤ) (1 : ZMod 2)).support.Nonempty := by simp
  have hmemU : (-1 : ℤ) ∈ (rule170 (Finsupp.single (0 : ℤ) (1 : ZMod 2))).support := by
    have e : (-1 : ℤ) + 1 = 0 := by ring
    rw [Finsupp.mem_support_iff, rule170_apply, e, Finsupp.single_eq_same]
    decide
  have hne' : (rule170 (Finsupp.single (0 : ℤ) (1 : ZMod 2))).support.Nonempty := ⟨-1, hmemU⟩
  refine ⟨Finsupp.single (0 : ℤ) (1 : ZMod 2), hne, hne', ?_⟩
  have hsmax : (Finsupp.single (0 : ℤ) (1 : ZMod 2)).support.max' hne = 0 := by simp
  have hUmax_le : (rule170 (Finsupp.single (0 : ℤ) (1 : ZMod 2))).support.max' hne' ≤ -1 := by
    apply Finset.max'_le
    intro b hb
    rw [Finsupp.mem_support_iff, rule170_apply] at hb
    by_contra hc
    push Not at hc
    apply hb
    rw [Finsupp.single_apply, ite_eq_right (by omega : ¬ (0 : ℤ) = b + 1)]
  omega

/-! ## The two shifts, at the endpoint-move generalization

The guard above shows `rule170`'s exact right spread is `-1`, not `+1` — outside the class-level
lemmas' reach, but squarely inside `memWidth_derived_eq_encard_rootSet`/`rootSet_encard_add_of_hyps`
at `(a, b) = (1, -1)`. Its mirror, `rule240` (`f a _b _c = a`, the pure LEFT shift), is new to this
file: left-permutive with `g ≡ 0` gives injectivity and the free max' spread (`b = 1`) for nothing,
but its own exact LEFT spread is `-1` (`a = -1`) rather than `leftPermutive_support_min'_spread`'s
`+1` — `rule240` is the ONLY instantiation in this file exercising `rootSet_cover`/
`rootSet_antichain`'s negative-`a` branch; without it that branch is untested code. -/

private theorem rule170_zero : rule170 0 = 0 := tableRule_zero f170 hq170

private def h170 (_a _b : ZMod 2) : ZMod 2 := 0

private theorem hh170 : ∀ a b c, f170 a b c = c + h170 a b := by
  intro a b c; unfold f170 h170; ring

private theorem rule170_injective : Function.Injective rule170 :=
  tableRule_injective_of_rightPermutive hq170 hh170

private theorem rule170_eq_zero_iff : ∀ {s : ℤ →₀ ZMod 2}, rule170 s = 0 ↔ s = 0 :=
  eqZero_of_injective_of_zero rule170_zero rule170_injective

/-- **The exact left spread, free from quiescence alone** (`rightPermutive_support_min'_spread`
would give this too; proved directly off `rule170_apply` to match `rule170_support_max'_spread`'s
style below). -/
theorem rule170_support_min'_spread {s : ℤ →₀ ZMod 2} (hne : s.support.Nonempty)
    (hne' : (rule170 s).support.Nonempty) :
    (rule170 s).support.min' hne' = s.support.min' hne - 1 := by
  set m := s.support.min' hne with hm_def
  rw [Finset.min'_eq_iff]
  refine ⟨?_, ?_⟩
  · rw [Finsupp.mem_support_iff, rule170_apply]
    have e : m - 1 + 1 = m := by omega
    rw [e]
    exact Finsupp.mem_support_iff.mp (Finset.min'_mem s.support hne)
  · intro b hb
    rw [Finsupp.mem_support_iff, rule170_apply] at hb
    have hmem : b + 1 ∈ s.support := Finsupp.mem_support_iff.mpr hb
    have := Finset.min'_le s.support (b + 1) hmem
    omega

/-- **The exact right spread, the guard's own witness turned into the true value**: `-1`, not
`+1` — the support moves left by one, matching `rule170_apply`'s own `s (i + 1)` reading. -/
theorem rule170_support_max'_spread {s : ℤ →₀ ZMod 2} (hne : s.support.Nonempty)
    (hne' : (rule170 s).support.Nonempty) :
    (rule170 s).support.max' hne' = s.support.max' hne - 1 := by
  set M := s.support.max' hne with hM_def
  rw [Finset.max'_eq_iff]
  refine ⟨?_, ?_⟩
  · rw [Finsupp.mem_support_iff, rule170_apply]
    have e : M - 1 + 1 = M := by omega
    rw [e]
    exact Finsupp.mem_support_iff.mp (Finset.max'_mem s.support hne)
  · intro b hb
    rw [Finsupp.mem_support_iff, rule170_apply] at hb
    have hmem : b + 1 ∈ s.support := Finsupp.mem_support_iff.mpr hb
    have := Finset.le_max' s.support (b + 1) hmem
    omega

/-- **Grade B2, the capstone for `rule170`**, `(a, b) = (1, -1)`. -/
theorem memWidth_rule170_derived_eq {n : ℕ} :
    memWidth rule170 (derivedStages rule170 (regionStates n)) 0 = (rootSet rule170 n).encard :=
  memWidth_derived_eq_encard_rootSet (a := 1) (b := -1) rule170_zero rule170_eq_zero_iff
    rule170_injective rule170_support_min'_spread rule170_support_max'_spread (by norm_num) n

/-- **Grade B2, the count for `rule170`**, `m = 1`: the shift's own root count
([Guests] Proposition 7.20), which Proposition 7.19's boundary points forward to. -/
theorem rootSet_encard_add_rule170 {n : ℕ} (hn : 1 ≤ n) :
    (rootSet rule170 n).encard + 2 ^ (n - 1) = 2 ^ n + 1 :=
  rootSet_encard_add_of_hyps (a := 1) (b := -1) rule170_eq_zero_iff rule170_injective
    rule170_support_min'_spread rule170_support_max'_spread (m := 1) (by norm_num) hn

/-- **Table `240`**, `f a _b _c = a`: the pure LEFT shift, `(rule240 s) i = s (i - 1)`,
left-permutive trivially (`g ≡ 0`). -/
def f240 (a _b _c : ZMod 2) : ZMod 2 := a

private def g240 (_b _c : ZMod 2) : ZMod 2 := 0

/-- `f240 0 0 0 = 0`. -/
theorem hq240 : f240 0 0 0 = 0 := by decide

private theorem hg240 : ∀ a b c, f240 a b c = a + g240 b c := by
  intro a b c; unfold f240 g240; ring

/-- **Elementary table `240`, radius one**, as a `tableRule`. -/
noncomputable def rule240 : (ℤ →₀ ZMod 2) → (ℤ →₀ ZMod 2) := tableRule f240 hq240

theorem rule240_apply (s : ℤ →₀ ZMod 2) (i : ℤ) : rule240 s i = s (i - 1) := by
  change tableRule f240 hq240 s i = s (i - 1)
  rw [tableRule_apply]
  rfl

private theorem rule240_zero : rule240 0 = 0 := tableRule_zero f240 hq240

private theorem rule240_injective : Function.Injective rule240 :=
  tableRule_injective_of_leftPermutive hq240 hg240

private theorem rule240_eq_zero_iff : ∀ {s : ℤ →₀ ZMod 2}, rule240 s = 0 ↔ s = 0 :=
  eqZero_of_injective_of_zero rule240_zero rule240_injective

/-- **The exact right spread, free from quiescence alone** (`leftPermutive_support_max'_spread`). -/
theorem rule240_support_max'_spread {s : ℤ →₀ ZMod 2} (hne : s.support.Nonempty)
    (hne' : (rule240 s).support.Nonempty) :
    (rule240 s).support.max' hne' = s.support.max' hne + 1 :=
  leftPermutive_support_max'_spread hq240 hg240 hne hne'

/-- **The exact left spread**: `+1`, not `-1` — `g ≡ 0` fails `leftPermutive_support_min'_spread`'s
own extra bit (`g 0 1 = 1`), since `g240 0 1 = 0`, so this is proved directly off `rule240_apply`
rather than through that lemma. The negative-`a` instance `rootSet_cover`/`rootSet_antichain`'s own
docstrings point at. -/
theorem rule240_support_min'_spread {s : ℤ →₀ ZMod 2} (hne : s.support.Nonempty)
    (hne' : (rule240 s).support.Nonempty) :
    (rule240 s).support.min' hne' = s.support.min' hne + 1 := by
  set m := s.support.min' hne with hm_def
  rw [Finset.min'_eq_iff]
  refine ⟨?_, ?_⟩
  · rw [Finsupp.mem_support_iff, rule240_apply]
    have e : m + 1 - 1 = m := by omega
    rw [e]
    exact Finsupp.mem_support_iff.mp (Finset.min'_mem s.support hne)
  · intro b hb
    rw [Finsupp.mem_support_iff, rule240_apply] at hb
    have hmem : b - 1 ∈ s.support := Finsupp.mem_support_iff.mpr hb
    have := Finset.min'_le s.support (b - 1) hmem
    omega

/-- **Grade B2, the capstone for `rule240`**, `(a, b) = (-1, 1)`. -/
theorem memWidth_rule240_derived_eq {n : ℕ} :
    memWidth rule240 (derivedStages rule240 (regionStates n)) 0 = (rootSet rule240 n).encard :=
  memWidth_derived_eq_encard_rootSet (a := -1) (b := 1) rule240_zero rule240_eq_zero_iff
    rule240_injective rule240_support_min'_spread rule240_support_max'_spread (by norm_num) n

/-- **Grade B2, the count for `rule240`**, `m = 1`. -/
theorem rootSet_encard_add_rule240 {n : ℕ} (hn : 1 ≤ n) :
    (rootSet rule240 n).encard + 2 ^ (n - 1) = 2 ^ n + 1 :=
  rootSet_encard_add_of_hyps (a := -1) (b := 1) rule240_eq_zero_iff rule240_injective
    rule240_support_min'_spread rule240_support_max'_spread (m := 1) (by norm_num) hn

end ExtremeTapWidth

/-! ## Axiom audit

Every capstone above is `#print axioms`-clean on the standard triple, and the guards below make
that build-enforced. -/

set_option linter.style.longLine false

/-- info: 'ExtremeTapWidth.rule90_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ExtremeTapWidth.rule90_injective

/-- info: 'ExtremeTapWidth.rule90_region_exit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ExtremeTapWidth.rule90_region_exit

/-- info: 'ExtremeTapWidth.rule150_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ExtremeTapWidth.rule150_injective

/-- info: 'ExtremeTapWidth.rule150_region_exit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ExtremeTapWidth.rule150_region_exit

/-- info: 'ExtremeTapWidth.memWidth_rule90_derived_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ExtremeTapWidth.memWidth_rule90_derived_ge

/-- info: 'ExtremeTapWidth.memWidth_rule150_derived_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ExtremeTapWidth.memWidth_rule150_derived_ge

/-- info: 'ExtremeTapWidth.memWidth_rule90_derived_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ExtremeTapWidth.memWidth_rule90_derived_eq

/-- info: 'ExtremeTapWidth.memWidth_rule150_derived_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ExtremeTapWidth.memWidth_rule150_derived_eq

/-- info: 'ExtremeTapWidth.rootSet_encard_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ExtremeTapWidth.rootSet_encard_add

/-- info: 'ExtremeTapWidth.rootSet_encard_add_rule150' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ExtremeTapWidth.rootSet_encard_add_rule150

/-- info: 'ExtremeTapWidth.memWidth_derived_eq_encard_rootSet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ExtremeTapWidth.memWidth_derived_eq_encard_rootSet

/-- info: 'ExtremeTapWidth.rootSet_encard_add_of_hyps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ExtremeTapWidth.rootSet_encard_add_of_hyps

/-- info: 'ExtremeTapWidth.tableRule_injective_of_leftPermutive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ExtremeTapWidth.tableRule_injective_of_leftPermutive

/-- info: 'ExtremeTapWidth.tableRule_injective_of_rightPermutive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ExtremeTapWidth.tableRule_injective_of_rightPermutive

/-- info: 'ExtremeTapWidth.memWidth_rule30_derived_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ExtremeTapWidth.memWidth_rule30_derived_eq

/-- info: 'ExtremeTapWidth.rootSet_encard_add_rule30' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ExtremeTapWidth.rootSet_encard_add_rule30

/-- info: 'ExtremeTapWidth.memWidth_rule30_derived_eq_rule90' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ExtremeTapWidth.memWidth_rule30_derived_eq_rule90

/-- info: 'ExtremeTapWidth.memWidth_rule210_derived_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ExtremeTapWidth.memWidth_rule210_derived_eq

/-- info: 'ExtremeTapWidth.rootSet_encard_add_rule210' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ExtremeTapWidth.rootSet_encard_add_rule210

/-- info: 'ExtremeTapWidth.memWidth_rule86_derived_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ExtremeTapWidth.memWidth_rule86_derived_eq

/-- info: 'ExtremeTapWidth.rootSet_encard_add_rule86' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ExtremeTapWidth.rootSet_encard_add_rule86

/-- info: 'ExtremeTapWidth.memWidth_rule154_derived_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ExtremeTapWidth.memWidth_rule154_derived_eq

/-- info: 'ExtremeTapWidth.rootSet_encard_add_rule154' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ExtremeTapWidth.rootSet_encard_add_rule154

/-- info: 'ExtremeTapWidth.guard_rule170_max'_spread_load_bearing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ExtremeTapWidth.guard_rule170_max'_spread_load_bearing

/-- info: 'ExtremeTapWidth.hUspread_sign_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ExtremeTapWidth.hUspread_sign_nonneg

/-- info: 'ExtremeTapWidth.interiorStates_eq_window' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ExtremeTapWidth.interiorStates_eq_window

/-- info: 'ExtremeTapWidth.guard_id_rootSet_load_bearing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ExtremeTapWidth.guard_id_rootSet_load_bearing

/-- info: 'ExtremeTapWidth.memWidth_rule170_derived_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ExtremeTapWidth.memWidth_rule170_derived_eq

/-- info: 'ExtremeTapWidth.rootSet_encard_add_rule170' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ExtremeTapWidth.rootSet_encard_add_rule170

/-- info: 'ExtremeTapWidth.memWidth_rule240_derived_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ExtremeTapWidth.memWidth_rule240_derived_eq

/-- info: 'ExtremeTapWidth.rootSet_encard_add_rule240' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ExtremeTapWidth.rootSet_encard_add_rule240
