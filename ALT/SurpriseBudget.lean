/-
Copyright (c) 2026 Mykola Palamarchuk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mykola Palamarchuk
-/
import ALT.BayesRedundancy
import ALT.PersistenceCapacity

-- Formal-check file, not Mathlib-destined: opt out of the house-style header linter.
set_option linter.style.header false

/-!
# The surprise budget: a learner's damage debt against a host's margin ([Inevitability] §6)

A guest learning its host mispredicts only finitely often: the number of `ε`-surprises over its
*entire existence* is bounded by the true rule's description length alone, with no separation
hypothesis and no dependence on the horizon ([Discovery] §3.3, Proposition 3.3, machine-checked as
`BayesRedundancy.surprise_card_le`). If each surprise damages the guest's memory by a bounded number
of cells, the guest's total damage debt is therefore a *constant*. On the other side, a settled
reading has a **robustness margin** — a radius within which a perturbation of an attractor state
leaves the decoded value unchanged ([Persistence] §10.1, `PersistenceCapacity.HasMargin`) — and that
margin is paid for in carried content by the repair tax.

This file joins the three: the event count, the margin, and the tax. The joining is the content —
each ingredient is already machine-checked in its own development, and nothing had connected them.

## The damage model is a hypothesis, not a theorem

`Damage` bundles the two clauses the assembly needs: the guest's memory is perturbed **only** at
surprise steps, and each such step perturbs at most `radius` cells. Neither is derived. How
misprediction couples to corruption is not something this development establishes, and the results
below are conditional on it, by design.

## What is proved, and one thing that is *not*

* `debt_le` — the debt is a constant. With the surprise set taken to be exactly [Discovery]'s, the
  total number of cells ever perturbed is at most `radius · K(R)·ln 2 / (2ε)`, independent of the
  guest's lifetime, of the horizon, and of the host's state count.
* `survives_of_margin` — **a margin covering the debt buys survival, given non-expansiveness.** If
  the host never separates two states in Hamming distance, damage accumulates additively, so a
  margin at least the total debt keeps the damaged reading equal to the undamaged one at every step,
  whatever the arrival pattern.
* `survives_of_corrects` — **or, given one-step erasure, the *per-event* radius suffices** and the
  total debt plays no role at all. A host that undoes a `c`-cell perturbation in a single step never
  lets damage accumulate, so `radius ≤ margin` is the whole condition.
* `badWorld_not_survives` — **and some such hypothesis is not optional.** There is a three-cell host
  with margin `2`, an attractor state, and a schedule of two one-cell perturbations — total debt
  `2`, inside the margin — after which the reading is *wrong*. So "the debt fits in the margin" does
  **not** by itself imply survival.
* `capacity_price` — the margin the debt demands is bought in expressiveness: by the repair tax, a
  reading with margin at least the debt has at most `|Mem| / |Ball_debt|` distinguishable values.

The counterexample is the reason this file is not three lines. `HasMargin` licenses exactly one
inference: a perturbation of an **attractor** state, by at most `e` cells, keeps the value. It says
nothing about a perturbation of a state the host has since moved *off* the attractor — and after the
first hit that is precisely where the guest is. Chaining perturbations across consecutive steps
therefore needs a hypothesis about what the host does with a displacement it is already carrying,
and an expansive host defeats a margin far larger than the total damage.

The two repairs are independent, and **which one holds decides which inequality is the right one**.
Non-expansiveness makes displacements sum, so the *total* debt must fit the margin. One-step erasure
makes each hit independent, so only the *per-event* radius must fit, and the debt is irrelevant. The
majority-vote world of [Persistence] §10.1 — the corpus's worked witness that margins exist at all —
satisfies the second and fails the first (`majWorld_corrects`, `majWorld_not_nonexpansive`), so on
that example the operative condition is the per-event one. Non-expansiveness in Hamming distance
essentially forbids a host from coupling its cells, and a computing host tends to fail it;
`nonexpansive_satisfiable` records that it is not vacuous, with a degenerate witness. A third route
— bounding the host's recovery time against the surprises' inter-arrival gaps — would reintroduce a
timing hypothesis, which is what pricing the race as a budget exists to avoid.

## Scope

`Damage`'s two clauses are named hypotheses. So are non-expansiveness and one-step erasure: both are
real restrictions on the host, stated rather than assumed away, and the counterexample shows neither
can simply be dropped. Nothing here says when the surprises arrive — every result is uniform over
arrival patterns, which is the point of a budget.
-/

namespace SurpriseBudget

open PersistenceCapacity Decoupling

/-! ## The debt: [Discovery]'s event count, priced in cells -/

section Debt

variable {ι V : Type*} [Fintype ι] [DecidableEq V]

/-- A **damage model** ([Inevitability] §6, the (D1)/(D2) hypotheses). The guest's memory is
perturbed only at the steps in `surprises`, and each such perturbation moves at most `radius` cells.

Both clauses are hypotheses. The corpus prices repair but does not derive how misprediction couples
to corruption, so nothing below claims a particular host and guest satisfy this. -/
structure Damage (ι V : Type*) [Fintype ι] [DecidableEq V] where
  /-- (D1) the steps at which the guest's memory is perturbed. -/
  surprises : Finset ℕ
  /-- (D2) the per-event perturbation radius, in cells. -/
  radius : ℕ
  /-- The perturbation applied across the step from time `t` to time `t + 1`. -/
  perturb : ℕ → Mem ι V → Mem ι V
  /-- (D1) a step that is not a surprise does not perturb. -/
  quiet : ∀ t ∉ surprises, ∀ x, perturb t x = x
  /-- (D2) a perturbation moves at most `radius` cells. -/
  bounded : ∀ t x, hammingDist x (perturb t x) ≤ radius

/-- **The debt is a constant** ([Inevitability] §6, Proposition 6.1(i)). Taking the damage model's
surprise set to be exactly [Discovery]'s `ε`-surprise set — which is what (D1) says — the total
number of cells the guest is ever perturbed in is at most `radius · K(R)·ln 2 / (2ε)`: independent
of the horizon `n`, of the guest's lifetime, and of the host's state count.

The right-hand side is [Discovery] §3.3, Proposition 3.3 ([Discovery] eq. (7),
`BayesRedundancy.surprise_card_le`) multiplied by the per-event radius, and that bound carries no
separation hypothesis — which is why the debt exists at all on classes where a chronological
discovery rate provably does not. -/
theorem debt_le {A J : Type*} [Fintype A] [DecidableEq A] [Fintype J]
    {q : J → ℕ → A → ℝ} {w : J → ℝ} {ω : ℕ → A} {R : J}
    (hq : ∀ i s x, 0 ≤ q i s x) (hw : ∀ i, 0 ≤ w i) (hreal : ∀ s, q R s (ω s) = 1)
    (hsumw : ∑ i, w i = 1) (hqsum : ∀ i s, ∑ x, q i s x = 1)
    (k : ℕ) (hwR : w R = (2 : ℝ) ^ (-(k : ℝ))) {ε : ℝ} (hε : 0 < ε) (n : ℕ)
    (D : Damage ι V) (hD : D.surprises = BayesRedundancy.surpriseSet q w ω ε n) :
    ((D.radius * D.surprises.card : ℕ) : ℝ) ≤ D.radius * ((k : ℝ) * Real.log 2 / (2 * ε)) := by
  have hcount : ((D.surprises.card : ℕ) : ℝ) ≤ (k : ℝ) * Real.log 2 / (2 * ε) := by
    rw [hD]
    exact BayesRedundancy.surprise_card_le hq hw hreal hsumw hqsum k hwR hε n
  push_cast
  exact mul_le_mul_of_nonneg_left hcount (Nat.cast_nonneg _)

end Debt

/-! ## The damaged trajectory -/

section Trajectory

variable {ι V M : Type*} [Fintype ι] [DecidableEq V]

/-- The guest's **actual** trajectory: at each step the host updates and then the damage lands. The
undamaged trajectory is `U^[t]`. -/
def traj (U : Mem ι V → Mem ι V) (D : Damage ι V) : ℕ → Mem ι V → Mem ι V
  | 0, s => s
  | t + 1, s => D.perturb t (U (traj U D t s))

@[simp] theorem traj_zero (U : Mem ι V → Mem ι V) (D : Damage ι V) (s : Mem ι V) :
    traj U D 0 s = s := rfl

@[simp] theorem traj_succ (U : Mem ι V → Mem ι V) (D : Damage ι V) (t : ℕ) (s : Mem ι V) :
    traj U D (t + 1) s = D.perturb t (U (traj U D t s)) := rfl

omit [Fintype ι] [DecidableEq V] in
/-- The undamaged trajectory stays on the attractor: `ω(B)` is invariant. -/
theorem iterate_mem_omegaLimit [Finite ι] [Finite V] {U : Mem ι V → Mem ι V} {B : Set (Mem ι V)}
    (hB : ∀ s ∈ B, U s ∈ B) {s : Mem ι V} (hs : s ∈ omegaLimit U B) (t : ℕ) :
    U^[t] s ∈ omegaLimit U B := by
  induction t with
  | zero => exact hs
  | succ t ih =>
      rw [Function.iterate_succ_apply']
      exact (omegaLimit_bijOn U hB).mapsTo ih

/-- **The host never separates two states.** A Hamming-Lipschitz-1 condition: one step cannot
increase the number of cells in which two memories differ. It is what makes damage *accumulate*
rather than *amplify*, and `badWorld_not_survives` shows the budget argument fails without it. -/
def HammingNonexpansive (U : Mem ι V → Mem ι V) : Prop :=
  ∀ x y, hammingDist (U x) (U y) ≤ hammingDist x y

/-- The surprises strictly before time `t`. -/
def spent (D : Damage ι V) (t : ℕ) : ℕ := (D.surprises ∩ Finset.range t).card

theorem spent_zero (D : Damage ι V) : spent D 0 = 0 := by simp [spent]

theorem spent_le (D : Damage ι V) (t : ℕ) : spent D t ≤ D.surprises.card :=
  Finset.card_le_card Finset.inter_subset_left

theorem spent_succ_of_mem {D : Damage ι V} {t : ℕ} (ht : t ∈ D.surprises) :
    spent D (t + 1) = spent D t + 1 := by
  have hins : D.surprises ∩ Finset.range (t + 1) = insert t (D.surprises ∩ Finset.range t) := by
    ext u
    simp only [Finset.mem_inter, Finset.mem_range, Finset.mem_insert, Nat.lt_succ_iff_lt_or_eq]
    constructor
    · rintro ⟨hu, hlt | rfl⟩
      · exact Or.inr ⟨hu, hlt⟩
      · exact Or.inl rfl
    · rintro (rfl | ⟨hu, hlt⟩)
      · exact ⟨ht, Or.inr rfl⟩
      · exact ⟨hu, Or.inl hlt⟩
  simp only [spent, hins]
  exact Finset.card_insert_of_notMem (by simp)

theorem spent_succ_of_not_mem {D : Damage ι V} {t : ℕ} (ht : t ∉ D.surprises) :
    spent D (t + 1) = spent D t := by
  have hins : D.surprises ∩ Finset.range (t + 1) = D.surprises ∩ Finset.range t := by
    ext u
    simp only [Finset.mem_inter, Finset.mem_range, Nat.lt_succ_iff_lt_or_eq]
    constructor
    · rintro ⟨hu, hlt | rfl⟩
      · exact ⟨hu, hlt⟩
      · exact absurd hu ht
    · rintro ⟨hu, hlt⟩
      exact ⟨hu, Or.inl hlt⟩
  simp only [spent, hins]

/-- **Damage accumulates, it does not amplify** — provided the host is non-expansive. After `t`
steps the damaged trajectory is within `radius` times the number of surprises *spent so far* of the
undamaged one. Non-expansiveness is used at every step: without it a single early perturbation can
grow without bound and the sum on the right is no bound at all. -/
theorem hammingDist_traj_le {U : Mem ι V → Mem ι V} (hne : HammingNonexpansive U)
    (D : Damage ι V) (s : Mem ι V) (t : ℕ) :
    hammingDist (U^[t] s) (traj U D t s) ≤ D.radius * spent D t := by
  induction t with
  | zero => simp [spent_zero]
  | succ t ih =>
      have hstep : hammingDist (U^[t + 1] s) (traj U D (t + 1) s)
          ≤ hammingDist (U (U^[t] s)) (U (traj U D t s))
            + hammingDist (U (traj U D t s)) (D.perturb t (U (traj U D t s))) := by
        rw [Function.iterate_succ_apply', traj_succ]
        exact hammingDist_triangle _ _ _
      have hcarry : hammingDist (U (U^[t] s)) (U (traj U D t s)) ≤ D.radius * spent D t :=
        le_trans (hne _ _) ih
      by_cases ht : t ∈ D.surprises
      · have hhit := D.bounded t (U (traj U D t s))
        rw [spent_succ_of_mem ht, Nat.mul_add, Nat.mul_one]
        omega
      · have hquiet : D.perturb t (U (traj U D t s)) = U (traj U D t s) :=
          D.quiet t ht (U (traj U D t s))
        rw [spent_succ_of_not_mem ht]
        rw [hquiet, hammingDist_self] at hstep
        omega

/-- **A margin covering the debt buys survival** ([Inevitability] §6, Proposition 6.1(iii),
repaired). For a non-expansive host with a settling reading of margin at least the total debt
`radius · |surprises|`, the damaged guest reads, at *every* step, exactly what the undamaged guest
would have read — and its state is back in the basin.

The conclusion is uniform in the arrival pattern: nothing here says when the surprises fall, which
is the whole point of pricing the race as a budget rather than as a deadline. What it is *not*
uniform in is the host: `badWorld_not_survives` exhibits a host with margin `2` and a debt of `2`
whose guest is destroyed, so the non-expansiveness hypothesis carries real weight. -/
theorem survives_of_margin [Finite V] {U : Mem ι V → Mem ι V} {B : Set (Mem ι V)}
    {v : Mem ι V → M} {E : ℕ} (hB : ∀ s ∈ B, U s ∈ B) (hne : HammingNonexpansive U)
    (hm : HasMargin U B v E) (D : Damage ι V) (hdebt : D.radius * D.surprises.card ≤ E)
    {s : Mem ι V} (hs : s ∈ omegaLimit U B) (t : ℕ) :
    traj U D t s ∈ B ∧ v (traj U D t s) = v (U^[t] s) := by
  have hdist : hammingDist (U^[t] s) (traj U D t s) ≤ E :=
    le_trans (hammingDist_traj_le hne D s t)
      (le_trans (Nat.mul_le_mul_left _ (spent_le D t)) hdebt)
  exact hm _ (iterate_mem_omegaLimit hB hs t) _ hdist

/-! ### The other repair: a host that erases each hit before the next lands

`survives_of_margin` makes displacements *sum*, so the quantity that has to fit the margin is the
**total** debt. The alternative is a host that erases each perturbation in a single step. Then the
hits never interact and the quantity that has to fit is the **per-event** radius — the total debt
does not enter at all. The two hypotheses are independent, and neither implies the other. -/

/-- **One-step error correction on the attractor**: a perturbation of at most `c` cells is undone by
a single update, which is what "the host erases it before the next one lands" has to mean. This is
strictly more than `HasMargin`, which constrains the *reading* at the perturbed state and says
nothing about where the host sends it. -/
def Corrects (U : Mem ι V → Mem ι V) (B : Set (Mem ι V)) (c : ℕ) : Prop :=
  ∀ s ∈ omegaLimit U B, ∀ s' ∈ hball c s, U s' = U s

/-- Under one-step correction the damage never accumulates: at every step the damaged trajectory is
within a *single* event radius of the undamaged one, however many hits have landed. -/
theorem traj_mem_hball_of_corrects [Finite V] {U : Mem ι V → Mem ι V} {B : Set (Mem ι V)} {c : ℕ}
    (hB : ∀ s ∈ B, U s ∈ B) (hcorr : Corrects U B c) (D : Damage ι V) (hrad : D.radius ≤ c)
    {s : Mem ι V} (hs : s ∈ omegaLimit U B) (t : ℕ) :
    hammingDist (U^[t] s) (traj U D t s) ≤ D.radius := by
  induction t with
  | zero => simp
  | succ t ih =>
      have hcl : U^[t] s ∈ omegaLimit U B := iterate_mem_omegaLimit hB hs t
      have hfix : U (traj U D t s) = U (U^[t] s) :=
        hcorr _ hcl _ (le_trans ih hrad)
      rw [Function.iterate_succ_apply', traj_succ, hfix]
      exact D.bounded t (U (U^[t] s))

/-- **A host that erases each hit survives any debt** ([Inevitability] §6 — the repair of
Proposition 6.1(ii)/(iii) that fits the corpus's own margin witness). Under one-step correction at
the event radius, the damaged guest reads what the undamaged guest reads at every step, and the
condition is `radius ≤ margin`: the **per-event** cost, with the total debt playing no role.

This matters for what §6 should claim. `majWorld_corrects` shows the majority-vote world — the
worked margin witness of [Persistence] §10.1 — satisfies this and *not* non-expansiveness
(`majWorld_not_nonexpansive`). So on the corpus's own example the total-debt inequality is not the
operative condition; the per-event one is. -/
theorem survives_of_corrects [Finite V] {U : Mem ι V → Mem ι V} {B : Set (Mem ι V)}
    {v : Mem ι V → M} {c E : ℕ} (hB : ∀ s ∈ B, U s ∈ B) (hcorr : Corrects U B c)
    (hm : HasMargin U B v E) (D : Damage ι V) (hrad : D.radius ≤ c) (hrE : D.radius ≤ E)
    {s : Mem ι V} (hs : s ∈ omegaLimit U B) (t : ℕ) :
    traj U D t s ∈ B ∧ v (traj U D t s) = v (U^[t] s) :=
  hm _ (iterate_mem_omegaLimit hB hs t) _
    (le_trans (traj_mem_hball_of_corrects hB hcorr D hrad hs t) hrE)

end Trajectory

/-! ## The counterexample: a margin covering the debt is not enough

`HasMargin` speaks about perturbations of states **on the attractor**. After the first hit the guest
is off the attractor, and the host may carry that displacement outward before the next hit lands.
The witness below does exactly that: a three-cell memory whose reading has margin `2`, damaged twice
by one cell each — a total debt of `2`, inside the margin — and destroyed. -/

section Counterexample

/-- The all-`false` memory; the witness's single attractor state. -/
def z : Mem (Fin 3) Bool := fun _ => false

/-- The all-`true` memory; the one state the witness's reading distinguishes. -/
def o : Mem (Fin 3) Bool := fun _ => true

/-- Weight one: cell `0` set. -/
def e₀ : Mem (Fin 3) Bool := fun i => i = 0

/-- Weight two: cells `0` and `1` set — where the host carries `e₀`. -/
def d₀₁ : Mem (Fin 3) Bool := fun i => i ≠ 2

/-- **An amplifying host.** Everything collapses to the attractor `z` in at most two steps, except
that the single perturbed state `e₀` is first carried *outward*, to the weight-two state `d₀₁`. That
one expansive transition is the whole counterexample. -/
def badWorld : Mem (Fin 3) Bool → Mem (Fin 3) Bool := fun x => if x = e₀ then d₀₁ else z

/-- The reading: it distinguishes the all-`true` memory from everything else. Constant on the
radius-`2` ball about the attractor, since `o` is three cells away. -/
def badRead : Mem (Fin 3) Bool → Bool := fun x => decide (x = o)

/-- Two one-cell hits, at the first two steps. -/
def badPerturb : ℕ → Mem (Fin 3) Bool → Mem (Fin 3) Bool
  | 0, x => Function.update x 0 (!x 0)
  | 1, x => Function.update x 2 (!x 2)
  | _, x => x

/-- The schedule: surprises at steps `0` and `1`, one cell each — a total debt of `2`. -/
def badDamage : Damage (Fin 3) Bool where
  surprises := {0, 1}
  radius := 1
  perturb := badPerturb
  quiet := by
    intro t ht x
    match t with
    | 0 => simp at ht
    | 1 => simp at ht
    | (_ + 2) => rfl
  bounded := by
    intro t x
    match t with
    | 0 => revert x; decide
    | 1 => revert x; decide
    | (_ + 2) => simp [badPerturb]

theorem badWorld_fixed_z : badWorld z = z := by decide

/-- Everything is at the attractor after two steps, so the ω-limit set is exactly `{z}`. -/
theorem badWorld_omegaLimit : omegaLimit badWorld Set.univ = {z} := by
  have hall : ∀ y : Mem (Fin 3) Bool, badWorld^[2] y = z := by decide
  refine Set.Subset.antisymm (fun x hx => ?_) (fun x hx => ?_)
  · obtain ⟨y, -, hy⟩ := Set.mem_iInter.mp hx 2
    rw [hall y] at hy
    exact hy.symm
  · rw [Set.mem_singleton_iff] at hx
    subst hx
    exact Set.mem_iInter.mpr fun t => ⟨z, Set.mem_univ z, Function.iterate_fixed badWorld_fixed_z t⟩

/-- The reading has margin `2`: the all-`true` memory is three cells from the attractor, so every
two-cell perturbation of `z` still reads `false`. -/
theorem badWorld_hasMargin : HasMargin badWorld Set.univ badRead 2 := by
  intro s hs s' hs'
  rw [badWorld_omegaLimit, Set.mem_singleton_iff] at hs
  subst hs
  refine ⟨Set.mem_univ _, ?_⟩
  revert hs'
  revert s'
  decide

/-- The host is **expansive**, and that is exactly the hypothesis it fails: one cell of difference
between `z` and `e₀` becomes two between their images. -/
theorem badWorld_not_nonexpansive : ¬ HammingNonexpansive badWorld := by
  intro h
  have := h z e₀
  revert this
  decide

/-- **The budget alone does not buy survival** ([Inevitability] §6 — a counterexample to
Proposition 6.1(iii) as stated). The witness has a settling reading of margin `2` on the attractor
`{z}`, and a damage schedule whose *total* debt is `2` — the whole debt fits inside the margin — yet
after two steps the damaged guest reads `true` where the undamaged guest reads `false`.

What fails is not the arithmetic but the chaining. The first hit leaves the guest inside the margin,
where `HasMargin` does guarantee the value; the host then carries that one-cell displacement out to
two cells, and the second hit — again only one cell — lands on a state the margin has nothing to say
about. `survives_of_margin` recovers the intended conclusion by forbidding exactly this
amplification, and `badWorld_not_nonexpansive` confirms the witness violates that and nothing
else. -/
theorem badWorld_not_survives :
    HasMargin badWorld Set.univ badRead 2 ∧
      z ∈ omegaLimit badWorld Set.univ ∧
      badDamage.radius * badDamage.surprises.card ≤ 2 ∧
      badRead (traj badWorld badDamage 2 z) ≠ badRead (badWorld^[2] z) := by
  refine ⟨badWorld_hasMargin, ?_, by decide, by decide⟩
  rw [badWorld_omegaLimit]
  rfl

/-- The two hits, step by step, so the mechanism is visible: the first lands one cell off the
attractor, the host carries it out to two cells, and the second — again one cell — completes the
all-`true` memory that the reading gets wrong. -/
theorem badWorld_trajectory :
    traj badWorld badDamage 1 z = e₀ ∧ badWorld (traj badWorld badDamage 1 z) = d₀₁ ∧
      traj badWorld badDamage 2 z = o := by decide

end Counterexample

/-! ## Which repair the corpus's own witness satisfies

The majority-vote world of [Persistence] §10.1 — the worked example that a positive margin exists at
all — **erases** a one-cell perturbation in one step, so `survives_of_corrects` applies to it. It is
**not** non-expansive: one cell of disagreement between two unsettled states becomes three after the
vote. So the two repairs are genuinely different hypotheses, and on the corpus's own witness the
operative condition is the per-event radius, not the total debt. -/

section Witnesses

/-- **The majority world erases a one-cell hit in a single step.** From a consensus state, flipping
one copy leaves the vote unchanged — which is exactly the one-step erasure [Inevitability] §6(ii)
appeals to, here as a hypothesis discharged on a concrete host. -/
theorem majWorld_corrects : Corrects majWorld Set.univ 1 := by
  have key : ∀ s s' : Mem (Fin 3) Bool, (s 0 = s 1 ∧ s 1 = s 2) → hammingDist s s' ≤ 1 →
      majWorld s' = majWorld s := by decide
  intro s hs s' hs'
  rw [← core_eq_omegaLimit, core_majWorld] at hs
  exact key s s' hs hs'

/-- **And it is not non-expansive.** Two states one cell apart on opposite sides of the vote are
sent to the two constant memories, three cells apart. So `survives_of_margin`'s hypothesis excludes
the corpus's own margin witness, and `survives_of_corrects` is the branch that covers it. -/
theorem majWorld_not_nonexpansive : ¬ HammingNonexpansive majWorld := by
  intro h
  have hbad := h (fun i => i = 2) (fun i => i ≠ 0)
  revert hbad
  decide

/-- Non-expansiveness is satisfiable, but the witness is degenerate: a host that snaps every state
to the attractor in one step separates nothing, and carries a margin for free. Recorded so
`survives_of_margin` is not vacuous — the substantive witness is `majWorld_corrects`, for the other
branch. Non-expansiveness in Hamming distance essentially forbids a host from coupling its cells,
which is why a computing host tends to fail it. -/
theorem nonexpansive_satisfiable :
    HammingNonexpansive (fun _ : Mem (Fin 3) Bool => z) ∧
      HasMargin (fun _ : Mem (Fin 3) Bool => z) Set.univ badRead 2 := by
  refine ⟨fun x y => by simp, ?_⟩
  have hcl : omegaLimit (fun _ : Mem (Fin 3) Bool => z) Set.univ ⊆ {z} := by
    intro x hx
    obtain ⟨y, -, hy⟩ := Set.mem_iInter.mp hx 1
    exact hy.symm
  intro s hs s' hs'
  rw [Set.mem_singleton_iff.mp (hcl hs)] at hs' ⊢
  refine ⟨Set.mem_univ _, ?_⟩
  revert hs'
  revert s'
  decide

end Witnesses

/-! ## The price: what the margin costs in expressiveness -/

section Price

variable {ι V M : Type*} [Fintype ι] [DecidableEq V] [Finite V]

/-- **The margin the debt demands is bought in carried content** ([Inevitability] §6, Proposition
6.1(iv)). By the repair tax ([Persistence] §10.1, `PersistenceCapacity.repair_tax`) a reading whose
margin covers the debt `E` has `E`-ball-disjoint value classes, so the number of settled values it
can distinguish is at most `|Mem| / |Ball_E|`.

How much this costs depends on which margin the guest actually needs, and that is decided by the
host, not by the learning problem. Under `survives_of_margin` the needed margin is the whole debt,
so a guest with more to learn — a longer rule, a finer `ε` — is pushed to a wider margin and, since
the ball grows fast in its radius, to correspondingly fewer distinguishable values: the learning
debt is then paid in expressiveness. Under `survives_of_corrects` the needed margin is only the
per-event radius, and the price does **not** scale with what the guest has to learn. The theorem
below is stated for any `E` below the margin and is silent on which regime applies.

Note this needs only `HasMargin` at radius `E`, which `HasMargin.mono` supplies from any larger
margin — so no ball-cardinality monotonicity is involved. -/
theorem capacity_price {U : Mem ι V → Mem ι V} {B : Set (Mem ι V)} {v : Mem ι V → M} {e E : ℕ}
    (hm : HasMargin U B v e) (hEe : E ≤ e) (c : Mem ι V) :
    Nat.card ↥(v '' omegaLimit U B) * Nat.card ↥(hball E c) ≤ Nat.card (Mem ι V) :=
  repair_tax (hm.mono hEe) c

end Price

end SurpriseBudget
