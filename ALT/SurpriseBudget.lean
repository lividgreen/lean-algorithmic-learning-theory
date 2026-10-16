module

public import Learning.BayesRedundancy
public import ALT.PersistenceCapacity


/-!
# The surprise budget: a learner's damage debt against a host's margin ([Inevitability] §6)

A guest learning its host mispredicts only finitely often: the number of `ε`-surprises over its
*entire existence* is bounded by the true rule's description length alone, with no separation
hypothesis and no dependence on the horizon ([Discovery] §3.3, Proposition 3.3, machine-checked as
`BayesRedundancy.errorTimes_card_le`). If each surprise damages the guest's memory by a bounded
number of cells, the guest's total damage debt is therefore a *constant*. On the other side, a
settled reading has a **robustness margin** — a radius within which a perturbation of an attractor
state leaves the decoded value unchanged ([Persistence] §10.1, `ALT.HasMargin`) —
and that margin is paid for in carried content by the repair tax.

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
* `Corrects.survives` — **or, given one-step erasure, the *per-event* radius suffices** and the
  total debt plays no role at all. A host that undoes a `c`-cell perturbation in a single step never
  lets damage accumulate, so `radius ≤ margin` is the whole condition.
* `survives_of_invariant` — **or, given a set the host and the damage cannot leave, on which the
  reading is constant, survival needs no margin at all.** This third repair constrains the reading
  rather than the dynamics: nothing accumulates because there is nowhere for the value to move to.
* `badWorld_not_survives` — **and some such hypothesis is not optional.** There is a three-cell host
  with margin `2`, an attractor state, and a schedule of two one-cell perturbations — total debt
  `2`, inside the margin — after which the reading is *wrong*. So "the debt fits in the margin" does
  **not** by itself imply survival.
* `capacity_price` — the margin the debt demands is bought in expressiveness: by the repair tax, a
  reading with margin at least the debt has at most `|Mem| / |Ball_debt|` distinguishable values.
* `Corrects.survives_of_invariant` — **and the third repair's hypothesis is met for free, once
  the first two hold together.** `Corrects` and `HammingNonexpansive` at the same radius `c ≥ 1`
  force the ω-limit set down to a lone fixed point (`Corrects.exists_fixedPoint`), and the ball
  of radius `c` about it is then exactly the invariant set the third repair needs — degenerate only
  once `c` reaches the cell count (`joint_dependence_boundary`).

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

## Settling is a separate question from agreement

`settles_traj_of_settles` and its purely dynamical form `settles_traj_of_readOnly` answer a
different question from the three repairs above: given only that the undamaged reading is
*eventually* constant along every orbit ([Persistence] §10.1, `ALT.Settles`), the
damaged reading is eventually constant too. That is **not** a fourth repair — it does not conclude
that the damaged and undamaged readings agree, only that each stops changing on its own.
`settles_traj_not_agreement` is why the distinction matters: it exhibits a host, a region, a damage
schedule and a start meeting every hypothesis `settles_traj_of_readOnly` needs, where both readings
settle and settle to **different** values.

`corrects_not_settles` places [Inevitability] §6's erasure disjunct beside `Settles` rather than
inside it: a host satisfying `Corrects _ _ 1` — the disjunct at its least interesting radius —
whose reading never settles at all. The two conditions are parallel questions about the same host,
and neither implies the other.

## The two dynamical repairs are pairwise independent, jointly not

`Corrects` and `HammingNonexpansive` constrain the host's dynamics in different ways, and neither
implies the other (`majWorld_corrects`/`majWorld_not_nonexpansive` witness one direction;
`nonexpansive_satisfiable` the other). Held together, at any radius `c ≥ 1`, they force the ω-limit
set to a single point (`Corrects.omegaLimit_subsingleton`, `Corrects.exists_fixedPoint`): two
distinct core points cannot both survive `Corrects.hammingDist_image_lt`'s strict contraction,
applied enough times to drive a bounded natural number below zero. The ball of radius `c` about
that point is then exactly the third repair's invariant set (`Corrects.survives_of_invariant`).

So the third repair is a genuine *alternative* to the first two only while they do not both hold;
once they do, it is what the first two are secretly buying. `joint_dependence_boundary` witnesses
the one place this collapses to nothing: at radius `c` equal to the memory's own cell count,
`Corrects` forces the host constant outright, and the only reading its ball admits is a constant
one — one radius lower, a genuinely non-constant reading (`badRead`) survives.

## Scope

`Damage`'s two clauses are named hypotheses. So are non-expansiveness and one-step erasure: both are
real restrictions on the host, stated rather than assumed away, and the counterexample shows neither
can simply be dropped. Nothing here says when the surprises arrive — every result is uniform over
arrival patterns, which is the point of a budget.
-/


@[expose] public section

namespace ALT


/-! ## The debt: [Discovery]'s event count, priced in cells -/

section Debt

variable {ι V : Type*} [Fintype ι] [DecidableEq V]

/-- A **damage model** ([Inevitability] §6, the (DM1)/(DM2) hypotheses). The guest's memory is
perturbed only at the steps in `surprises`, and each such perturbation moves at most `radius` cells.

Both clauses are hypotheses. The corpus prices repair but does not derive how misprediction couples
to corruption, so nothing below claims a particular host and guest satisfy this. -/
structure Damage (ι V : Type*) [Fintype ι] [DecidableEq V] where
  /-- (DM1) the steps at which the guest's memory is perturbed. -/
  surprises : Finset ℕ
  /-- (DM2) the per-event perturbation radius, in cells. -/
  radius : ℕ
  /-- The perturbation applied across the step from time `t` to time `t + 1`. -/
  perturb : ℕ → Mem ι V → Mem ι V
  /-- (DM1) a step that is not a surprise does not perturb. -/
  quiet : ∀ t ∉ surprises, ∀ x, perturb t x = x
  /-- (DM2) a perturbation moves at most `radius` cells. -/
  bounded : ∀ t x, hammingDist x (perturb t x) ≤ radius

/-- **The debt is a constant** ([Inevitability] §6, Proposition 6.1(i)). Taking the damage model's
surprise set to be exactly [Discovery]'s `ε`-surprise set — which is what (DM1) says — the total
number of cells the guest is ever perturbed in is at most `radius · K(R)·ln 2 / (2ε)`: independent
of the horizon `n`, of the guest's lifetime, and of the host's state count.

The right-hand side is [Discovery] §3.3, Proposition 3.3 ([Discovery] eq. (7),
`BayesRedundancy.errorTimes_card_le`) multiplied by the per-event radius, and that bound carries no
separation hypothesis — which is why the debt exists at all on classes where a chronological
discovery rate provably does not. -/
theorem debt_le {A J : Type*} [Fintype A] [DecidableEq A] [Fintype J]
    {q : J → ℕ → A → ℝ} {w : J → ℝ} {ω : ℕ → A} {R : J}
    (hq : ∀ i s x, 0 ≤ q i s x) (hw : ∀ i, 0 ≤ w i) (hreal : ∀ s, q R s (ω s) = 1)
    (hsumw : ∑ i, w i = 1) (hqsum : ∀ i s, ∑ x, q i s x = 1)
    (k : ℕ) (hwR : w R = (2 : ℝ) ^ (-(k : ℝ))) {ε : ℝ} (hε : 0 < ε) (n : ℕ)
    (D : Damage ι V) (hD : D.surprises = BayesRedundancy.errorTimes q w ω ε n) :
    ((D.radius * D.surprises.card : ℕ) : ℝ) ≤ D.radius * ((k : ℝ) * Real.log 2 / (2 * ε)) := by
  have hcount : ((D.surprises.card : ℕ) : ℝ) ≤ (k : ℝ) * Real.log 2 / (2 * ε) := by
    rw [hD]
    exact BayesRedundancy.errorTimes_card_le hq hw hreal hsumw hqsum k hwR hε n
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

@[simp] private theorem traj_zero (U : Mem ι V → Mem ι V) (D : Damage ι V) (s : Mem ι V) :
    traj U D 0 s = s := rfl

@[simp] private theorem traj_succ (U : Mem ι V → Mem ι V) (D : Damage ι V) (t : ℕ) (s : Mem ι V) :
    traj U D (t + 1) s = D.perturb t (U (traj U D t s)) := rfl

omit [Fintype ι] [DecidableEq V] in
/-- The undamaged trajectory stays on the attractor: `ω(B)` is invariant. -/
private theorem iterate_mem_omegaLimit_of_mem [Finite ι] [Finite V] {U : Mem ι V → Mem ι V}
    {B : Set (Mem ι V)} (hB : ∀ s ∈ B, U s ∈ B) {s : Mem ι V} (hs : s ∈ omegaLimit U B) (t : ℕ) :
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
private def Damage.spent (D : Damage ι V) (t : ℕ) : ℕ := (D.surprises ∩ Finset.range t).card

private theorem spent_zero (D : Damage ι V) : Damage.spent D 0 = 0 := by simp [Damage.spent]

private theorem spent_le (D : Damage ι V) (t : ℕ) : Damage.spent D t ≤ D.surprises.card :=
  Finset.card_le_card Finset.inter_subset_left

private theorem spent_succ_of_mem {D : Damage ι V} {t : ℕ} (ht : t ∈ D.surprises) :
    Damage.spent D (t + 1) = Damage.spent D t + 1 := by
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
  simp only [Damage.spent, hins]
  exact Finset.card_insert_of_notMem (by simp)

private theorem spent_succ_of_not_mem {D : Damage ι V} {t : ℕ} (ht : t ∉ D.surprises) :
    Damage.spent D (t + 1) = Damage.spent D t := by
  have hins : D.surprises ∩ Finset.range (t + 1) = D.surprises ∩ Finset.range t := by
    ext u
    simp only [Finset.mem_inter, Finset.mem_range, Nat.lt_succ_iff_lt_or_eq]
    constructor
    · rintro ⟨hu, hlt | rfl⟩
      · exact ⟨hu, hlt⟩
      · exact absurd hu ht
    · rintro ⟨hu, hlt⟩
      exact ⟨hu, Or.inl hlt⟩
  simp only [Damage.spent, hins]

/-- **Damage accumulates, it does not amplify** — provided the host is non-expansive. After `t`
steps the damaged trajectory is within `radius` times the number of surprises *spent so far* of the
undamaged one. Non-expansiveness is used at every step: without it a single early perturbation can
grow without bound and the sum on the right is no bound at all. -/
private theorem hammingDist_traj_le {U : Mem ι V → Mem ι V} (hne : HammingNonexpansive U)
    (D : Damage ι V) (s : Mem ι V) (t : ℕ) :
    hammingDist (U^[t] s) (traj U D t s) ≤ D.radius * Damage.spent D t := by
  induction t with
  | zero => simp [spent_zero]
  | succ t ih =>
      have hstep : hammingDist (U^[t + 1] s) (traj U D (t + 1) s)
          ≤ hammingDist (U (U^[t] s)) (U (traj U D t s))
            + hammingDist (U (traj U D t s)) (D.perturb t (U (traj U D t s))) := by
        rw [Function.iterate_succ_apply', traj_succ]
        exact hammingDist_triangle _ _ _
      have hcarry : hammingDist (U (U^[t] s)) (U (traj U D t s)) ≤ D.radius * Damage.spent D t :=
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
  exact hm _ (iterate_mem_omegaLimit_of_mem hB hs t) _ hdist

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
private theorem Corrects.traj_mem_hball [Finite V] {U : Mem ι V → Mem ι V}
    {B : Set (Mem ι V)} {c : ℕ} (hB : ∀ s ∈ B, U s ∈ B) (hcorr : Corrects U B c)
    (D : Damage ι V) (hrad : D.radius ≤ c)
    {s : Mem ι V} (hs : s ∈ omegaLimit U B) (t : ℕ) :
    hammingDist (U^[t] s) (traj U D t s) ≤ D.radius := by
  induction t with
  | zero => simp
  | succ t ih =>
      have hcl : U^[t] s ∈ omegaLimit U B := iterate_mem_omegaLimit_of_mem hB hs t
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
theorem Corrects.survives [Finite V] {U : Mem ι V → Mem ι V} {B : Set (Mem ι V)}
    {v : Mem ι V → M} {c E : ℕ} (hB : ∀ s ∈ B, U s ∈ B) (hcorr : Corrects U B c)
    (hm : HasMargin U B v E) (D : Damage ι V) (hrad : D.radius ≤ c) (hrE : D.radius ≤ E)
    {s : Mem ι V} (hs : s ∈ omegaLimit U B) (t : ℕ) :
    traj U D t s ∈ B ∧ v (traj U D t s) = v (U^[t] s) :=
  hm _ (iterate_mem_omegaLimit_of_mem hB hs t) _
    (le_trans (Corrects.traj_mem_hball hB hcorr D hrad hs t) hrE)

/-! ### Generalizing one-step erasure: correction within a window

`Corrects` is the case `T = 1` of a family: a host that undoes a `c`-cell perturbation not on the
very next step but within `T` updates. The window buys nothing when hits arrive faster than it
closes — a second hit landing before the first correction completes can compound with it into a
state the correction promise says nothing about, exactly as `badWorld` compounds under
non-expansiveness's absence. So the family additionally needs the hits **spaced** more than `T`
apart; `correctsWithin_needs_spaced` below shows that hypothesis is not optional either.

Outside the windows a hit opens, this is *stronger* than `Corrects.survives`: the trajectories
agree exactly, not merely under the same reading, and the conclusion needs no `HasMargin` at all.
Inside a window the two damaged and undamaged trajectories genuinely separate — nothing here claims
otherwise, and `Corrects.traj_mem_hball`'s every-step bound does not generalize to `T > 1`. -/

/-- **Erasure within `T` steps**: a `c`-cell perturbation of an attractor state is undone after `T`
further updates. `Corrects` is exactly the case `T = 1` (`correctsWithin_one_iff_corrects`). -/
def CorrectsWithin (U : Mem ι V → Mem ι V) (B : Set (Mem ι V)) (c T : ℕ) : Prop :=
  ∀ s ∈ omegaLimit U B, ∀ s' ∈ hball c s, U^[T] s' = U^[T] s

/-- **`CorrectsWithin` at `T = 1` is `Corrects`.** The base case of the family is the one-step
condition, verbatim. -/
theorem correctsWithin_one_iff_corrects {U : Mem ι V → Mem ι V} {B : Set (Mem ι V)} {c : ℕ} :
    CorrectsWithin U B c 1 ↔ Corrects U B c := by
  simp only [CorrectsWithin, Corrects, Function.iterate_one]

/-- **Hits land more than `T` apart.** The spacing a within-`T` correction needs: any two
surprises, in arrival order, are separated by more than `T` steps — room for the window the earlier
one opens to close before the later one lands. -/
def Damage.Spaced (D : Damage ι V) (T : ℕ) : Prop :=
  ∀ a ∈ D.surprises, ∀ b ∈ D.surprises, a < b → a + T < b

theorem traj_add_of_quiet (U : Mem ι V → Mem ι V) (D : Damage ι V) (x : Mem ι V) {a : ℕ} (n : ℕ)
    (hquiet : ∀ j, a ≤ j → j < a + n → j ∉ D.surprises) :
    traj U D (a + n) x = U^[n] (traj U D a x) := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hj : ∀ j, a ≤ j → j < a + n → j ∉ D.surprises := fun j h1 h2 => hquiet j h1 (by omega)
      have han : a + n ∉ D.surprises := hquiet (a + n) (by omega) (by omega)
      have hstep : a + (n + 1) = (a + n) + 1 := by omega
      rw [hstep, traj_succ, ih hj, Function.iterate_succ_apply']
      exact D.quiet (a + n) han _

/-- **The quiet tail, transported past any starting point.** The special case of
`traj_add_of_quiet` that `settles_traj_of_settles` below actually needs: once every step from `t₀`
on is quiet, the damaged trajectory from `t₀` onward is just `U` iterated. -/
theorem traj_add_of_quiet_after {U : Mem ι V → Mem ι V} (D : Damage ι V) {t₀ : ℕ}
    (h : ∀ t ≥ t₀, t ∉ D.surprises) (j : ℕ) (s : Mem ι V) :
    traj U D (t₀ + j) s = U^[j] (traj U D t₀ s) :=
  traj_add_of_quiet U D s j (fun t' ht' _ => h t' ht')

/-- **Erasure within `T` steps, given spacing, keeps the two trajectories in exact sync outside a
correction window** ([Inevitability] §6, Proposition 6.1(iii), the within-`T` generalization of the
one-step repair). If every surprise up to `t` clears its window before `t` — the hypothesis
`hclean`, which the theorem needs only at `t` itself, not along the whole history — the damaged and
undamaged trajectories coincide exactly at `t`, not merely in a shared reading.

The proof takes the *last* surprise `u` before `t`. `Damage.Spaced` supplies exactly the same
"window closes before the next hit" hypothesis at `u`, one level down, so strong induction gives
`traj U D u s = U^[u] s`: the trajectory up to and including `u` is undamaged. The hit at `u` then
lands as a fresh `c`-cell perturbation of the attractor point `U^[u+1] s`, `CorrectsWithin` erases
it within `T` further steps, and `u` being the *last* surprise below `t` means nothing else perturbs
the run from `u + 1` to `t`, so the erased state coasts on plain `U`-steps the rest of the way. -/
theorem CorrectsWithin.traj_eq_of_spaced [Finite V]
    {U : Mem ι V → Mem ι V} {B : Set (Mem ι V)} {c T : ℕ}
    (hB : ∀ s ∈ B, U s ∈ B) (hcorr : CorrectsWithin U B c T)
    (D : Damage ι V) (hrad : D.radius ≤ c) (hsp : Damage.Spaced D T)
    {s : Mem ι V} (hs : s ∈ omegaLimit U B) {t : ℕ}
    (hclean : ∀ u ∈ D.surprises, u < t → u + T < t) :
    traj U D t s = U^[t] s := by
  revert hclean
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    intro hclean
    by_cases hexists : ∃ u ∈ D.surprises, u < t
    · obtain ⟨u₀, hu₀mem, hu₀lt⟩ := hexists
      have hSne : (D.surprises ∩ Finset.range t).Nonempty :=
        ⟨u₀, Finset.mem_inter.mpr ⟨hu₀mem, Finset.mem_range.mpr hu₀lt⟩⟩
      set u := (D.surprises ∩ Finset.range t).max' hSne with hudef
      have huS := (D.surprises ∩ Finset.range t).max'_mem hSne
      have humem : u ∈ D.surprises := (Finset.mem_inter.mp huS).1
      have hult : u < t := Finset.mem_range.mp (Finset.mem_inter.mp huS).2
      have humax : ∀ v ∈ D.surprises, v < t → v ≤ u := fun v hv hvt =>
        (D.surprises ∩ Finset.range t).le_max' v
          (Finset.mem_inter.mpr ⟨hv, Finset.mem_range.mpr hvt⟩)
      have hucleen : ∀ w ∈ D.surprises, w < u → w + T < u := fun w hw hwu => hsp w hw u humem hwu
      have hutraj : traj U D u s = U^[u] s := ih u hult hucleen
      have hcore' : U^[u + 1] s ∈ omegaLimit U B := iterate_mem_omegaLimit_of_mem hB hs (u + 1)
      have hpert : traj U D (u + 1) s = D.perturb u (U^[u + 1] s) := by
        rw [traj_succ, hutraj, Function.iterate_succ_apply']
      have hclose : hammingDist (U^[u + 1] s) (traj U D (u + 1) s) ≤ c := by
        rw [hpert]
        exact le_trans (D.bounded u (U^[u + 1] s)) hrad
      have hTeq : U^[T] (traj U D (u + 1) s) = U^[T] (U^[u + 1] s) := hcorr _ hcore' _ hclose
      have hutt : u + T < t := hclean u humem hult
      have hquiet : ∀ j, u + 1 ≤ j → j < (u + 1) + (t - (u + 1)) → j ∉ D.surprises := by
        intro j hj1 hj2 hjmem
        exact absurd (humax j hjmem (by omega)) (by omega)
      have htail : traj U D t s = U^[t - (u + 1)] (traj U D (u + 1) s) := by
        have heq : (u + 1) + (t - (u + 1)) = t := by omega
        have h := traj_add_of_quiet U D s (t - (u + 1)) hquiet
        rwa [heq] at h
      set k := t - (u + 1) - T with hkdef
      have hkT : k + T = t - (u + 1) := by omega
      have hlift : U^[t - (u + 1)] (traj U D (u + 1) s) = U^[t - (u + 1)] (U^[u + 1] s) := by
        rw [← hkT, Function.iterate_add_apply, Function.iterate_add_apply, hTeq]
      have hfinal : U^[t - (u + 1)] (U^[u + 1] s) = U^[t] s := by
        rw [← Function.iterate_add_apply, Nat.sub_add_cancel (by omega : u + 1 ≤ t)]
      rw [htail, hlift, hfinal]
    · push Not at hexists
      have hnotlt : ∀ w ∈ D.surprises, t ≤ w := fun w hw => by
        have := hexists w hw; omega
      have hquiet : ∀ j, 0 ≤ j → j < 0 + t → j ∉ D.surprises := fun j _ hjt hjmem =>
        absurd (hnotlt j hjmem) (by omega)
      have h := traj_add_of_quiet U D s t hquiet
      simpa using h

/-- **The within-`T` repair, given spacing, needs no margin at all.** Under `CorrectsWithin` and
`Damage.Spaced`, any reading `v` agrees on the damaged and undamaged trajectories at every clean
time `t` — an immediate corollary of the exact state equality, unlike `Corrects.survives`, which
needs `HasMargin` to turn a Hamming bound into a reading equality. -/
theorem CorrectsWithin.survives [Finite V] {U : Mem ι V → Mem ι V} {B : Set (Mem ι V)}
    {v : Mem ι V → M} {c T : ℕ} (hB : ∀ s ∈ B, U s ∈ B) (hcorr : CorrectsWithin U B c T)
    (D : Damage ι V) (hrad : D.radius ≤ c) (hsp : Damage.Spaced D T)
    {s : Mem ι V} (hs : s ∈ omegaLimit U B) {t : ℕ}
    (hclean : ∀ u ∈ D.surprises, u < t → u + T < t) :
    v (traj U D t s) = v (U^[t] s) :=
  congrArg v (CorrectsWithin.traj_eq_of_spaced hB hcorr D hrad hsp hs hclean)

/-! ### A third repair: an invariant set on which the reading does not move

The two repairs above both constrain the *dynamics*: the host never separates two states
(`HammingNonexpansive`), or it erases a bounded perturbation in one step (`Corrects`). The repair
below constrains the *reading* instead — a set closed under the host and under damage of the host's
own image, on which the reading is constant. It needs no Hamming distance, no finiteness, and no
margin at all: the reading cannot move because it has nowhere to move to. -/

/-- **A reading constant on an invariant-under-damage set survives any debt, at any radius**
([Inevitability] §6, a third repair of Proposition 6.1(iii)). `B'` is closed under the host, and
closed under damage applied to the host's own image — at *every* time `t`, not only the ones the
schedule actually uses, since the theorem is uniform over damage schedules. If the reading agrees at
any two points of `B'`, the damaged and undamaged trajectories read the same value at every step,
for any arrival pattern and any total debt.

Unlike `survives_of_margin` and `Corrects.survives`, this needs no `HasMargin`, no Hamming
distance, and no finiteness of `V`: once `traj U D t s` and `U^[t] s` are both shown to lie in `B'`,
`hv` supplies the equality directly, with no accumulation argument at all. -/
theorem survives_of_invariant {U : Mem ι V → Mem ι V} {B' : Set (Mem ι V)} {v : Mem ι V → M}
    (hU : ∀ s ∈ B', U s ∈ B') (D : Damage ι V)
    (hD : ∀ t, ∀ s ∈ B', D.perturb t (U s) ∈ B')
    (hv : ∀ s ∈ B', ∀ s' ∈ B', v s = v s')
    {s : Mem ι V} (hs : s ∈ B') (t : ℕ) :
    traj U D t s ∈ B' ∧ v (traj U D t s) = v (U^[t] s) := by
  have hiter : ∀ n, U^[n] s ∈ B' := by
    intro n
    induction n with
    | zero => simpa using hs
    | succ n ih => rw [Function.iterate_succ_apply']; exact hU _ ih
  have htraj : ∀ n, traj U D n s ∈ B' := by
    intro n
    induction n with
    | zero => simpa using hs
    | succ n ih => rw [traj_succ]; exact hD n _ ih
  exact ⟨htraj t, hv _ (htraj t) _ (hiter t)⟩

/-! ### The two dynamical repairs, together: a lone fixed point

`Corrects` and `HammingNonexpansive` constrain the dynamics in different ways, and neither implies
the other (`majWorld_corrects`/`majWorld_not_nonexpansive` below witness one direction;
`nonexpansive_satisfiable` the other). Held **together**, at any radius `c ≥ 1`, they force the
host's entire recurrent behaviour down to a single point: two distinct core points could not both
survive the interpolation argument below, since each step of it strictly shrinks the distance
between them. The invariant repair's hypothesis is then met for free, on the ball of radius `c`
about that point — so the third repair is a genuine alternative to the first two only while they do
not both hold; once they do, it is what the first two are secretly buying. -/

open Classical in
/-- A `hammingDist`/`Function.update` fact Mathlib does not carry: overwriting one cell moves at
most one cell. -/
private theorem hammingDist_update_le_one (s : Mem ι V) (i : ι) (a : V) :
    hammingDist (Function.update s i a) s ≤ 1 := by
  have hsub : (Finset.univ.filter (fun j => Function.update s i a j ≠ s j)) ⊆ {i} := by
    intro j hj
    rw [Finset.mem_filter] at hj
    rw [Finset.mem_singleton]
    by_contra hne
    exact hj.2 (Function.update_of_ne hne a s)
  calc hammingDist (Function.update s i a) s
      = (Finset.univ.filter (fun j => Function.update s i a j ≠ s j)).card := rfl
    _ ≤ ({i} : Finset ι).card := Finset.card_le_card hsub
    _ = 1 := Finset.card_singleton i

open Classical in
/-- The other `hammingDist`/`Function.update` fact: overwriting the one cell where `s` and `z`
disagree, onto `z`'s own value there, moves strictly closer to `z` — the single-cell interpolation
step the contraction below chains. -/
private theorem hammingDist_update_lt (s z : Mem ι V) {i : ι} (h : s i ≠ z i) :
    hammingDist (Function.update s i (z i)) z < hammingDist s z := by
  have heq : (Finset.univ.filter (fun j => Function.update s i (z i) j ≠ z j))
      = (Finset.univ.filter (fun j => s j ≠ z j)).erase i := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
    by_cases hji : j = i
    · subst hji
      simp [Function.update_self]
    · rw [Function.update_of_ne hji]
      simp [hji]
  have hmem : i ∈ (Finset.univ.filter (fun j => s j ≠ z j)) := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact h
  calc hammingDist (Function.update s i (z i)) z
      = (Finset.univ.filter (fun j => Function.update s i (z i) j ≠ z j)).card := rfl
    _ = ((Finset.univ.filter (fun j => s j ≠ z j)).erase i).card := by rw [heq]
    _ < (Finset.univ.filter (fun j => s j ≠ z j)).card := Finset.card_erase_lt_of_mem hmem
    _ = hammingDist s z := rfl

open Classical in
/-- **A strict contraction** ([Inevitability] §6, Proposition 6.1(iii)'s joint-dependence
mechanism). At a `Corrects`-radius `c ≥ 1`, one non-expansive step
strictly shrinks the distance from any core point `s` to any other point `z`: overwrite the single
cell where they disagree onto `z`'s own value there, landing within `hball c s`
(`hammingDist_update_le_one`, using `1 ≤ c`), where `Corrects` fixes the image at `U s`; the
overwritten point is itself strictly closer to `z` (`hammingDist_update_lt`), and non-expansiveness
carries that gain through the step untouched. -/
theorem Corrects.hammingDist_image_lt [Finite V] {U : Mem ι V → Mem ι V} {B : Set (Mem ι V)}
    {c : ℕ} (hc : 1 ≤ c) (hcorr : Corrects U B c) (hne : HammingNonexpansive U)
    {s z : Mem ι V} (hs : s ∈ omegaLimit U B) (hsz : s ≠ z) :
    hammingDist (U s) (U z) < hammingDist s z := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hsz
  set s' := Function.update s i (z i) with hs'def
  have hs'mem : s' ∈ hball c s := by
    change hammingDist s s' ≤ c
    rw [hammingDist_comm]
    exact le_trans (hammingDist_update_le_one s i (z i)) hc
  have hUs' : U s' = U s := hcorr s hs s' hs'mem
  calc hammingDist (U s) (U z) = hammingDist (U s') (U z) := by rw [hUs']
    _ ≤ hammingDist s' z := hne s' z
    _ < hammingDist s z := hammingDist_update_lt s z hi

/-- **The recurrent core collapses to a single point** ([Inevitability] §6, Proposition 6.1(iii)'s
joint-dependence mechanism). Two distinct core points cannot both
survive `Corrects.hammingDist_image_lt` applied `hammingDist s z + 1` times: each application
strictly drops a natural number, and injectivity on the core (`omegaLimit_bijOn`) keeps the
iterates apart throughout, driving a bounded quantity below zero. -/
theorem Corrects.omegaLimit_subsingleton [Finite V] {U : Mem ι V → Mem ι V} {B : Set (Mem ι V)}
    {c : ℕ} (hc : 1 ≤ c) (hB : ∀ s ∈ B, U s ∈ B) (hcorr : Corrects U B c)
    (hne : HammingNonexpansive U) :
    (omegaLimit U B).Subsingleton := by
  intro s hs z hz
  by_contra hsz
  have hinj : Set.InjOn U (omegaLimit U B) := (omegaLimit_bijOn U hB).injOn
  have hne_iter : ∀ k, U^[k] s ≠ U^[k] z := by
    intro k
    induction k with
    | zero => simpa using hsz
    | succ k ih =>
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
        intro hcontra
        exact ih (hinj (iterate_mem_omegaLimit_of_mem hB hs k)
          (iterate_mem_omegaLimit_of_mem hB hz k) hcontra)
  have hdrop : ∀ k, hammingDist (U^[k] s) (U^[k] z) + k ≤ hammingDist s z := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        have hlt : hammingDist (U^[k + 1] s) (U^[k + 1] z) < hammingDist (U^[k] s) (U^[k] z) := by
          rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
          exact Corrects.hammingDist_image_lt hc hcorr hne (iterate_mem_omegaLimit_of_mem hB hs k)
            (hne_iter k)
        omega
  have hbound := hdrop (hammingDist s z + 1)
  omega

omit [DecidableEq V] [Fintype ι] in
/-- The ω-limit set of a nonempty `U`-closed set is nonempty — reproved locally from the public
`exists_image_stable_le` rather than reaching into `PersistenceCapacity`'s file-private
stabilization lemmas: the point `U^[N] b`, for `b` a witness of `B` and `N` a stabilization index,
lies in every `(U^[t]) '' B`, forward by `hN` and backward by peeling `U` off `U^[N - t] b`. -/
private theorem omegaLimit_nonempty_of_nonempty [Finite ι] [Finite V] {U : Mem ι V → Mem ι V}
    {B : Set (Mem ι V)} (hB : ∀ s ∈ B, U s ∈ B) (hBne : B.Nonempty) :
    (omegaLimit U B).Nonempty := by
  obtain ⟨N, -, hN⟩ := exists_image_stable_le U hB
  obtain ⟨b, hb⟩ := hBne
  have hiter : ∀ n, U^[n] b ∈ B := by
    intro n
    induction n with
    | zero => simpa using hb
    | succ n ih => rw [Function.iterate_succ_apply']; exact hB _ ih
  refine ⟨U^[N] b, Set.mem_iInter.mpr fun t => ?_⟩
  rcases Nat.lt_or_ge t N with ht | ht
  · refine ⟨U^[N - t] b, hiter (N - t), ?_⟩
    rw [← Function.iterate_add_apply]
    congr 1
    omega
  · rw [hN t ht]
    exact ⟨b, hb, rfl⟩

/-- **The lone fixed point, packaged** ([Inevitability] §6, Proposition 6.1(iii)'s joint-dependence
mechanism). On a nonempty `U`-closed `B`, `Corrects`-radius `c ≥ 1`
together with `HammingNonexpansive` force the ω-limit set down to a single state `s₀`, and `s₀` is
a fixed point of `U` — the ω-limit set is `U`-invariant (`omegaLimit_bijOn`), so `U s₀` is trapped
in a singleton alongside `s₀` itself. -/
theorem Corrects.exists_fixedPoint [Finite V] {U : Mem ι V → Mem ι V} {B : Set (Mem ι V)}
    {c : ℕ} (hc : 1 ≤ c) (hB : ∀ s ∈ B, U s ∈ B) (hcorr : Corrects U B c)
    (hne : HammingNonexpansive U) (hBne : B.Nonempty) :
    ∃ s₀, omegaLimit U B = {s₀} ∧ U s₀ = s₀ := by
  obtain ⟨s₀, hs₀⟩ := omegaLimit_nonempty_of_nonempty hB hBne
  have hsingle : omegaLimit U B = {s₀} :=
    (Corrects.omegaLimit_subsingleton hc hB hcorr hne).eq_singleton_of_mem hs₀
  refine ⟨s₀, hsingle, ?_⟩
  have hmem : U s₀ ∈ omegaLimit U B := (omegaLimit_bijOn U hB).mapsTo hs₀
  rw [hsingle, Set.mem_singleton_iff] at hmem
  exact hmem

/-- Half of `survives_of_invariant`'s hypothesis, once `s₀` is `U`'s lone fixed core point:
`Corrects` sends every point of `hball c s₀` to `U s₀`, which is `s₀` itself, and `s₀` sits at the
centre of its own ball. -/
private theorem Corrects.hball_closed {U : Mem ι V → Mem ι V} {B : Set (Mem ι V)} {c : ℕ}
    {s₀ : Mem ι V} (hs₀ : s₀ ∈ omegaLimit U B) (hfix : U s₀ = s₀) (hcorr : Corrects U B c) :
    ∀ s ∈ hball c s₀, U s ∈ hball c s₀ := by
  intro s hs
  have hUs : U s = s₀ := (hcorr s₀ hs₀ s hs).trans hfix
  rw [hUs]
  change hammingDist s₀ s₀ ≤ c
  rw [hammingDist_self]
  exact Nat.zero_le c

/-- The other half of `survives_of_invariant`'s hypothesis: `hball c s₀` absorbs any damage of the
host's own image, uniformly over `Damage` schedules of radius at most `c` — every such point maps to
`s₀` under `U` (as in `Corrects.hball_closed`), and `D.bounded` keeps the perturbation within `c` of
`s₀`. -/
private theorem Corrects.hball_damage_closed {U : Mem ι V → Mem ι V} {B : Set (Mem ι V)} {c : ℕ}
    {s₀ : Mem ι V} (hs₀ : s₀ ∈ omegaLimit U B) (hfix : U s₀ = s₀) (hcorr : Corrects U B c)
    (D : Damage ι V) (hrad : D.radius ≤ c) :
    ∀ t, ∀ s ∈ hball c s₀, D.perturb t (U s) ∈ hball c s₀ := by
  intro t s hs
  have hUs : U s = s₀ := (hcorr s₀ hs₀ s hs).trans hfix
  rw [hUs]
  change hammingDist s₀ (D.perturb t s₀) ≤ c
  exact le_trans (D.bounded t s₀) hrad

/-- **The third repair's hypothesis is met, once the first two hold together** ([Inevitability] §6,
Proposition 6.1(iii)'s joint-dependence payoff). Once `s₀` is
the lone fixed point `Corrects` and `HammingNonexpansive` force (`Corrects.exists_fixedPoint`),
`hball c s₀` is exactly the invariant set `survives_of_invariant` asks for: any reading constant on
it agrees, at every step and under any damage schedule of radius at most `c`, on the damaged and
undamaged trajectories — no margin, no further use of non-expansiveness at this step, and no
finiteness beyond what built `s₀` in the first place.

Read as advice rather than as a curiosity: the two dynamical repairs are not two levers a designer
can pull together for redundancy. Pulling both collapses the recurrent core, at which point this
third condition is free and the first two are doing no work it does not already do — so `(ii)`'s
margin route and `(iii)`'s erasure route apply to nearly disjoint host classes, and a reader
choosing which disjunct to verify is choosing, not hedging. -/
theorem Corrects.survives_of_invariant {U : Mem ι V → Mem ι V} {B : Set (Mem ι V)}
    {v : Mem ι V → M} {c : ℕ} {s₀ : Mem ι V} (hs₀ : s₀ ∈ omegaLimit U B) (hfix : U s₀ = s₀)
    (hcorr : Corrects U B c) (D : Damage ι V) (hrad : D.radius ≤ c)
    (hv : ∀ x ∈ hball c s₀, ∀ y ∈ hball c s₀, v x = v y)
    {s : Mem ι V} (hs : s ∈ hball c s₀) (t : ℕ) :
    traj U D t s ∈ hball c s₀ ∧ v (traj U D t s) = v (U^[t] s) :=
  ALT.survives_of_invariant (Corrects.hball_closed hs₀ hfix hcorr) D
    (Corrects.hball_damage_closed hs₀ hfix hcorr D hrad) hv hs t

/-! ### Settling versus agreement

The three repairs above all conclude that the damaged reading equals the undamaged one. The pair
below answers a different, companion question: given only that the undamaged reading is eventually
constant, is the damaged reading eventually constant too? Yes — but "eventually constant" is not
"equal to the undamaged run", and `settles_traj_not_agreement` below is the reason that distinction
is load-bearing rather than a hedge. -/

/-- **The damaged trajectory settles whenever the undamaged reading does** ([Inevitability] §6,
Proposition 6.1(iii) — a companion question to the three repairs above, not a fourth one). Those
three conclude that the damaged reading equals the undamaged one; this concludes only that the
damaged reading eventually stops changing, which `settles_traj_not_agreement` below shows is
genuinely weaker.

The argument is short because `D.surprises` is a `Finset`: past its largest element every step is
quiet (`Damage.quiet`), so the damaged trajectory from there on is just `U` iterated
(`traj_add_of_quiet_after`). That state is still in the basin (`hB`, `hD`, by induction), so `hset`
already settles it, and its own settling time transports back through the quiet tail. -/
theorem settles_traj_of_settles {U : Mem ι V → Mem ι V} {decode : Mem ι V → M}
    {B : Set (Mem ι V)}
    (D : Damage ι V) (hD : ∀ t, ∀ s ∈ B, D.perturb t (U s) ∈ B)
    (hset : ∀ s ∈ B, Settles U decode s)
    {s : Mem ι V} (hs : s ∈ B) :
    ∃ T, ∀ k ≥ T, decode (traj U D k s) = decode (traj U D T s) := by
  set t₀ := D.surprises.sup id + 1 with ht₀def
  have hquiet : ∀ t ≥ t₀, t ∉ D.surprises := by
    intro t ht hmem
    have hle : t ≤ D.surprises.sup id := Finset.le_sup (f := id) hmem
    omega
  have htmem : traj U D t₀ s ∈ B := by
    have hind : ∀ n, traj U D n s ∈ B := by
      intro n
      induction n with
      | zero => simpa using hs
      | succ n ih => rw [traj_succ]; exact hD n _ ih
    exact hind t₀
  obtain ⟨T', hT'⟩ := hset _ htmem
  refine ⟨t₀ + T', fun k hk => ?_⟩
  have hkt₀ : t₀ ≤ k := le_trans (Nat.le_add_right t₀ T') hk
  have heqk : traj U D k s = U^[k - t₀] (traj U D t₀ s) := by
    have h : traj U D (t₀ + (k - t₀)) s = U^[k - t₀] (traj U D t₀ s) :=
      traj_add_of_quiet_after D hquiet (k - t₀) s
    rwa [Nat.add_sub_cancel' hkt₀] at h
  have heqT : traj U D (t₀ + T') s = U^[T'] (traj U D t₀ s) :=
    traj_add_of_quiet_after D hquiet T' s
  rw [heqk, heqT]
  exact hT' _ (by omega)

/-- **The purely dynamical form** ([Inevitability] §6, Proposition 6.1(iii); [Persistence] §10.1,
`eventual_decoupling_iff`). The hypothesis is a condition on the host alone — `U` is read-only on
its own ω-limit set — mentioning neither the damage schedule nor the guest's margin, which is the
whole reason this form is worth stating: a host-side condition delivers the same conclusion as
`settles_traj_of_settles`. -/
theorem settles_traj_of_readOnly [Finite ι] [Finite V] {U : Mem ι V → Mem ι V} {R : Set ι}
    {decode : Mem ι V → M} {B : Set (Mem ι V)} (hf : Faithful decode R)
    (hB : ∀ s ∈ B, U s ∈ B)
    (hro : ∀ s ∈ omegaLimit U B, ∀ a ∈ R, U s a = s a)
    (D : Damage ι V) (hD : ∀ t, ∀ s ∈ B, D.perturb t (U s) ∈ B)
    {s : Mem ι V} (hs : s ∈ B) :
    ∃ T, ∀ k ≥ T, decode (traj U D k s) = decode (traj U D T s) :=
  settles_traj_of_settles D hD ((eventual_decoupling_iff hf hB).mpr hro) hs

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

private theorem badWorld_fixed_z : badWorld z = z := by decide

/-- Everything is at the attractor after two steps, so the ω-limit set is exactly `{z}`. -/
private theorem badWorld_omegaLimit : omegaLimit badWorld Set.univ = {z} := by
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
private theorem badWorld_hasMargin : HasMargin badWorld Set.univ badRead 2 := by
  intro s hs s' hs'
  rw [badWorld_omegaLimit, Set.mem_singleton_iff] at hs
  subst hs
  refine ⟨Set.mem_univ _, ?_⟩
  revert hs'
  revert s'
  decide

/-- The host is **expansive**, and that is exactly the hypothesis it fails: one cell of difference
between `z` and `e₀` becomes two between their images. -/
private theorem badWorld_not_nonexpansive : ¬ HammingNonexpansive badWorld := by
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
private theorem badWorld_trajectory :
    traj badWorld badDamage 1 z = e₀ ∧ badWorld (traj badWorld badDamage 1 z) = d₀₁ ∧
      traj badWorld badDamage 2 z = o := by decide

/-- **`badWorld` also erases any single-cell perturbation of the attractor within two steps** —
`CorrectsWithin badWorld Set.univ 1 2`, checked over the finitely many states within radius `1` of
`z`. The perturbation at cell `0` needs the full two-step window (`e₀ → d₀₁ → z`); the other two
cells clear in one. -/
theorem badWorld_correctsWithin : CorrectsWithin badWorld Set.univ 1 2 := by
  intro s hs s' hs'
  rw [badWorld_omegaLimit, Set.mem_singleton_iff] at hs
  subst hs
  revert hs'
  revert s'
  decide

private theorem badDamage_not_spaced : ¬ Damage.Spaced badDamage 2 := by
  intro h
  have h01 : (0 : ℕ) + 2 < 1 := h 0 (by decide) 1 (by decide) (by decide)
  omega

end Counterexample

/-! ## The same witness shows the spacing hypothesis is load-bearing too

`CorrectsWithin` promises exactly one thing: a perturbation of an **attractor** state, of at most
`c` cells, is undone within `T` further updates. It says nothing about a state reached mid-window.
`badWorld` already erases any single-cell perturbation of `z` within two steps
(`badWorld_correctsWithin`), and its own schedule `badDamage` already lands its two hits one step
apart (`badDamage_not_spaced`) — well inside that window — so no second witness is needed: the same
host and schedule that show the budget alone does not buy survival (`badWorld_not_survives`) show
equally that erasure-within-a-window needs `Damage.Spaced` as a genuine second hypothesis. -/

/-- **Erasure within a window is not enough without spacing** ([Inevitability] §6 — the within-`T`
repair needs `Damage.Spaced` as a genuine second hypothesis, not an artifact of the proof).
`badWorld` erases any single-cell hit at the attractor within two steps (`badWorld_correctsWithin`),
and its schedule's per-event radius is within that bound — yet the damaged and undamaged
trajectories disagree at `t = 2` (`badWorld_trajectory`): the first hit perturbs the attractor `z`
to `e₀`, `badWorld`'s own dynamics carries that in-progress correction out to `d₀₁` before the
window closes, and the second hit — one step after the first, inside the window
(`badDamage_not_spaced`) — lands on that mid-correction state rather than the attractor, completing
the weight-three state `o` the reading gets wrong. -/
theorem correctsWithin_needs_spaced :
    CorrectsWithin badWorld Set.univ 1 2 ∧
      z ∈ omegaLimit badWorld Set.univ ∧
      badDamage.radius ≤ 1 ∧
      traj badWorld badDamage 2 z ≠ badWorld^[2] z := by
  refine ⟨badWorld_correctsWithin, ?_, by decide, by decide⟩
  rw [badWorld_omegaLimit]
  rfl

/-! ## Which repair the corpus's own witness satisfies

The majority-vote world of [Persistence] §10.1 — the worked example that a positive margin exists at
all — **erases** a one-cell perturbation in one step, so `Corrects.survives` applies to it. It is
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
the corpus's own margin witness, and `Corrects.survives` is the branch that covers it. -/
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
private theorem nonexpansive_satisfiable :
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

/-! ## Guard families for the settling question

`settles_traj_of_settles` and `settles_traj_of_readOnly` answer a companion question to
Proposition 6.1(iii), not a fourth instance of it: their conclusion is that the damaged reading
eventually stops changing, never that it agrees with what the undamaged guest would have read. The
two families below are why that distinction is load-bearing rather than a hedge. -/

section SettlingGuards

/-! ### Settling is not agreement

Two limit cycles, one reachable only by damage. A single hit knocks the run from one basin into the
other; both readings settle, and settle to different values. -/

/-- The all-`false` memory: one of `raceU`'s two fixed points. -/
def raceZero : Mem (Fin 2) Bool := fun _ => false

/-- The all-`true` memory: `raceU`'s other fixed point, and the undamaged start. -/
def raceOne : Mem (Fin 2) Bool := fun _ => true

/-- **Two basins, one host.** `raceOne` is fixed; every other state — `raceZero` included — falls
to `raceZero` in one step. There is no third settled value and no slow approach. -/
def raceU : Mem (Fin 2) Bool → Mem (Fin 2) Bool := fun x =>
  if x = raceOne then raceOne else raceZero

/-- Reads cell `0`: `false` on `raceZero`, `true` on `raceOne`. -/
def raceRead : Mem (Fin 2) Bool → Bool := fun x => x 0

private theorem raceU_fixed_zero : raceU raceZero = raceZero := by decide

private theorem raceU_fixed_one : raceU raceOne = raceOne := by decide

/-- **`raceRead` is faithful to region `{0}`**: reading cell `0` alone already separates every
state `raceRead` can distinguish, because that is all it reads. -/
private theorem raceRead_faithful : Faithful raceRead ({0} : Set (Fin 2)) := by
  intro s t
  simp only [raceRead, Set.mem_singleton_iff]
  constructor
  · rintro h a rfl; exact h
  · intro h; exact h 0 rfl

/-- **`raceU`'s ω-limit set is exactly its two fixed points.** Every state falls into one of them
in a single step, and neither is displaced afterward. -/
private theorem raceU_omegaLimit : omegaLimit raceU Set.univ = {raceZero, raceOne} := by
  have hrange : ∀ y : Mem (Fin 2) Bool, raceU y = raceZero ∨ raceU y = raceOne := by decide
  apply Set.Subset.antisymm
  · intro x hx
    obtain ⟨y, -, hy⟩ := Set.mem_iInter.mp hx 1
    simp only [Function.iterate_one] at hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    rcases hrange y with h | h
    · exact Or.inl (by rw [← hy, h])
    · exact Or.inr (by rw [← hy, h])
  · rintro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact Set.mem_iInter.mpr fun t =>
        ⟨raceZero, Set.mem_univ _, Function.iterate_fixed raceU_fixed_zero t⟩
    · exact Set.mem_iInter.mpr fun t =>
        ⟨raceOne, Set.mem_univ _, Function.iterate_fixed raceU_fixed_one t⟩

/-- **`raceU` is read-only on its own ω-limit set** — it fixes both states there outright, so it
is read-only on every region, `{0}` included. -/
private theorem raceU_readOnly :
    ∀ s ∈ omegaLimit raceU Set.univ, ∀ a ∈ ({0} : Set (Fin 2)), raceU s a = s a := by
  intro s hs a _
  rw [raceU_omegaLimit] at hs
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
  rcases hs with rfl | rfl
  · rw [raceU_fixed_zero]
  · rw [raceU_fixed_one]

/-- The single hit: at step `0`, the state is overwritten to `raceZero` outright. -/
def racePerturb : ℕ → Mem (Fin 2) Bool → Mem (Fin 2) Bool
  | 0, _ => raceZero
  | _ + 1, x => x

/-- The schedule: one surprise, at step `0`, radius `2` — the whole memory, since two cells is all
`Mem (Fin 2) Bool` has. -/
def raceDamage : Damage (Fin 2) Bool where
  surprises := {0}
  radius := 2
  perturb := racePerturb
  quiet := by
    intro t ht x
    match t with
    | 0 => simp at ht
    | (_ + 1) => rfl
  bounded := by
    intro t x
    match t with
    | 0 => revert x; decide
    | (_ + 1) => simp [racePerturb]

/-- **The conclusion cannot be strengthened to agreement** ([Inevitability] §6, Proposition
6.1(iii) — the reason `settles_traj_of_settles`/`settles_traj_of_readOnly` are a companion question
rather than a fourth sufficient condition). Every hypothesis `settles_traj_of_readOnly` needs holds
here: `raceRead` is faithful to `{0}`, `raceU` closes `Set.univ`, `raceU` is read-only on its own
ω-limit set, and the damage schedule respects the basin. So both the damaged and the undamaged
reading settle — and settle to *different* values. The undamaged reading is `true` forever; a
single hit at step `0` sends the damaged run to `raceZero`, where it reads `false` from that step
on. -/
theorem settles_traj_not_agreement :
    Faithful raceRead ({0} : Set (Fin 2)) ∧
      (∀ s ∈ omegaLimit raceU Set.univ, ∀ a ∈ ({0} : Set (Fin 2)), raceU s a = s a) ∧
      (∃ T, ∀ k ≥ T, raceRead (raceU^[k] raceOne) = raceRead (raceU^[T] raceOne)) ∧
      (∃ T, ∀ k ≥ T, raceRead (traj raceU raceDamage k raceOne)
        = raceRead (traj raceU raceDamage T raceOne)) ∧
      raceRead (traj raceU raceDamage 1 raceOne) ≠ raceRead (raceU^[1] raceOne) := by
  refine ⟨raceRead_faithful, raceU_readOnly, ?_, ?_, by decide⟩
  · exact (eventual_decoupling_iff raceRead_faithful (fun _ _ => Set.mem_univ _)).mpr
      raceU_readOnly raceOne (Set.mem_univ _)
  · exact settles_traj_of_readOnly raceRead_faithful (fun _ _ => Set.mem_univ _) raceU_readOnly
      raceDamage (fun _ _ _ => Set.mem_univ _) (Set.mem_univ _)

/-! ### The two forms are parallel, not nested

`Corrects U Set.univ 1` is [Inevitability] §6's erasure disjunct at the smallest interesting
radius. It says nothing about the reading settling at all, and the witness below shows it cannot: a
host that erases every one-cell hit in a single step, whose reading nonetheless alternates forever.
Two cells do not suffice for this — every radius-`1` ball in `Mem (Fin 2) Bool` already holds three
of the four states, so two disjoint such balls cannot sit at the two ends of a `2`-cycle there. -/

/-- The all-`false` memory: one end of `cycleU`'s `2`-cycle. -/
def cycleZero : Mem (Fin 3) Bool := fun _ => false

/-- The all-`true` memory: the other end. -/
def cycleOne : Mem (Fin 3) Bool := fun _ => true

/-- **A host that erases any single-cell perturbation of either end of its own `2`-cycle in one
step.** States within radius `1` of `cycleZero` land on `cycleOne`; every other state, `cycleOne`
included, lands on `cycleZero`. The two radius-`1` balls this needs disjoint — one around each end
— cover `4 + 4 = 8` of `Mem (Fin 3) Bool`'s `8` states exactly, which is why three cells are the
least this construction can use. -/
def cycleU : Mem (Fin 3) Bool → Mem (Fin 3) Bool := fun x =>
  if hammingDist cycleZero x ≤ 1 then cycleOne else cycleZero

/-- Reads cell `0`: `false` on `cycleZero`, `true` on `cycleOne`. -/
def cycleRead : Mem (Fin 3) Bool → Bool := fun x => x 0

private theorem cycleU_zero_eq_one : cycleU cycleZero = cycleOne := by decide

private theorem cycleU_one_eq_zero : cycleU cycleOne = cycleZero := by decide

/-- **The two-cycle, at every step count of either parity.** `cycleU` swaps `cycleZero` and
`cycleOne` and nothing else recurs, so a single induction stepping two iterations at a time proves
both parities together. -/
private theorem cycleU_two_cycle (m : ℕ) :
    cycleU^[2 * m] cycleZero = cycleZero ∧ cycleU^[2 * m + 1] cycleZero = cycleOne ∧
      cycleU^[2 * m] cycleOne = cycleOne ∧ cycleU^[2 * m + 1] cycleOne = cycleZero := by
  induction m with
  | zero =>
      refine ⟨rfl, ?_, rfl, ?_⟩
      · change cycleU^[1] cycleZero = cycleOne
        rw [Function.iterate_one]; exact cycleU_zero_eq_one
      · change cycleU^[1] cycleOne = cycleZero
        rw [Function.iterate_one]; exact cycleU_one_eq_zero
  | succ m ih =>
      obtain ⟨ih1, ih2, ih3, ih4⟩ := ih
      have e1 : 2 * (m + 1) = (2 * m + 1) + 1 := by ring
      have e2 : 2 * (m + 1) + 1 = (2 * m + 1) + 1 + 1 := by ring
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [e1, Function.iterate_succ_apply', ih2, cycleU_one_eq_zero]
      · rw [e2, Function.iterate_succ_apply', Function.iterate_succ_apply', ih2,
          cycleU_one_eq_zero, cycleU_zero_eq_one]
      · rw [e1, Function.iterate_succ_apply', ih4, cycleU_zero_eq_one]
      · rw [e2, Function.iterate_succ_apply', Function.iterate_succ_apply', ih4,
          cycleU_zero_eq_one, cycleU_one_eq_zero]

/-- **`cycleU`'s ω-limit set is exactly its `2`-cycle.** Every state falls onto it in one step,
and the cycle then recurs at every step count via `cycleU_two_cycle`. -/
private theorem cycleU_omegaLimit : omegaLimit cycleU Set.univ = {cycleZero, cycleOne} := by
  have hrange : ∀ y : Mem (Fin 3) Bool, cycleU y = cycleZero ∨ cycleU y = cycleOne := by decide
  apply Set.Subset.antisymm
  · intro x hx
    obtain ⟨y, -, hy⟩ := Set.mem_iInter.mp hx 1
    simp only [Function.iterate_one] at hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    rcases hrange y with h | h
    · exact Or.inl (by rw [← hy, h])
    · exact Or.inr (by rw [← hy, h])
  · rintro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · refine Set.mem_iInter.mpr fun t => ?_
      rcases Nat.even_or_odd t with ⟨m, hm⟩ | ⟨m, hm⟩
      · have heq : t = 2 * m := by omega
        exact ⟨cycleZero, Set.mem_univ _, by rw [heq]; exact (cycleU_two_cycle m).1⟩
      · have heq : t = 2 * m + 1 := by omega
        exact ⟨cycleOne, Set.mem_univ _, by rw [heq]; exact (cycleU_two_cycle m).2.2.2⟩
    · refine Set.mem_iInter.mpr fun t => ?_
      rcases Nat.even_or_odd t with ⟨m, hm⟩ | ⟨m, hm⟩
      · have heq : t = 2 * m := by omega
        exact ⟨cycleOne, Set.mem_univ _, by rw [heq]; exact (cycleU_two_cycle m).2.2.1⟩
      · have heq : t = 2 * m + 1 := by omega
        exact ⟨cycleZero, Set.mem_univ _, by rw [heq]; exact (cycleU_two_cycle m).2.1⟩

/-- **`cycleU` erases any single-cell hit on its own `2`-cycle in one step** — `Corrects` at
`c = 1`, [Inevitability] §6's erasure disjunct at the least interesting radius. -/
private theorem cycleU_corrects : Corrects cycleU Set.univ 1 := by
  intro s hs s' hs'
  rw [cycleU_omegaLimit] at hs
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
  rcases hs with rfl | rfl
  · have hs'' : hammingDist cycleZero s' ≤ 1 := hs'
    have h0 : hammingDist cycleZero cycleZero ≤ 1 := by decide
    unfold cycleU
    rw [ite_eq_left hs'', ite_eq_left h0]
  · have hd' : hammingDist cycleOne s' ≤ 1 := hs'
    have hnot_s' : ¬ hammingDist cycleZero s' ≤ 1 := by
      intro hbad
      have htri := hammingDist_triangle cycleZero s' cycleOne
      have hdist : hammingDist cycleZero cycleOne = 3 := by decide
      have hsymm : hammingDist s' cycleOne = hammingDist cycleOne s' :=
        hammingDist_comm s' cycleOne
      omega
    have hnot_one : ¬ hammingDist cycleZero cycleOne ≤ 1 := by decide
    unfold cycleU
    rw [ite_eq_right hnot_s', ite_eq_right hnot_one]

/-- **`cycleU`'s reading never settles.** Along the `2`-cycle from `cycleZero`, cell `0`
alternates `false, true, false, true, …` forever, so no tail is ever constant. -/
private theorem not_settles_cycleU : ¬ Settles cycleU cycleRead cycleZero := by
  rintro ⟨T, hT⟩
  have e1 := hT (2 * (T + 1)) (by omega)
  have e2 := hT (2 * (T + 1) + 1) (by omega)
  rw [(cycleU_two_cycle (T + 1)).1] at e1
  rw [(cycleU_two_cycle (T + 1)).2.1] at e2
  exact absurd (e2.trans e1.symm) (by decide)

/-- **The two forms are parallel, in the direction that needs three cells** ([Inevitability] §6,
Proposition 6.1(iii)'s erasure disjunct, set beside `Settles` rather than inside it — a host
meeting the disjunct need not settle at all). `cycleU` satisfies `Corrects _ _ 1`, the erasure
disjunct at `c = 1`, yet its reading — read from region `{0}` — alternates forever along the very
`2`-cycle the disjunct is about. -/
theorem corrects_not_settles :
    Corrects cycleU Set.univ 1 ∧ ¬ Settles cycleU cycleRead cycleZero :=
  ⟨cycleU_corrects, not_settles_cycleU⟩

end SettlingGuards

/-! ## The joint-dependence boundary: a guard family at the degenerate radius

`Corrects.hammingDist_image_lt` and its corollaries above hold at every `Corrects`-radius
`c ≥ 1`, but the invariant reading they hand `survives_of_invariant` is worth something only while
`hball c s₀` is a PROPER subset of the state space: past that, the only reading constant on the
ball is a constant reading outright, and a constant reading carries nothing.
The witness below realizes the degenerate case: a constant host on `Mem (Fin 3) Bool`,
at radius `3 = Fintype.card (Fin 3)` — the least radius at which `hball` reaches the whole memory
(`hammingDist_le_card_fintype`) — beside the same reading one radius lower, where it is genuinely
non-constant and still survives. -/

section JointDependenceGuard

/-- **The constant host.** `Corrects` and `HammingNonexpansive` hold at it for a degenerate reason
— nothing ever moves — which is exactly why it is the right witness for the boundary: it is not a
special case the theorems above strain to cover, it is what a `Corrects`-radius reaching the whole
memory forces every witness to look like. -/
def constHost : Mem (Fin 3) Bool → Mem (Fin 3) Bool := fun _ => z

private theorem constHost_corrects (c : ℕ) : Corrects constHost Set.univ c := fun _ _ _ _ => rfl

private theorem constHost_nonexpansive : HammingNonexpansive constHost := fun x y => by
  simp [constHost, hammingDist_self]

/-- **At radius `3`, `hball` about the fixed point is the whole memory** — the degenerate case,
since `3 = Fintype.card (Fin 3)` and no two memories are further apart than that
(`hammingDist_le_card_fintype`). -/
theorem hball_three_eq_univ : hball 3 z = (Set.univ : Set (Mem (Fin 3) Bool)) := by
  ext x
  refine ⟨fun _ => Set.mem_univ x, fun _ => ?_⟩
  change hammingDist z x ≤ 3
  calc hammingDist z x ≤ Fintype.card (Fin 3) := hammingDist_le_card_fintype
    _ = 3 := Fintype.card_fin 3

/-- **The boundary, witnessed** ([Inevitability] §6, Proposition 6.1(iii)'s joint-dependence
mechanism). At radius `3` — the memory's own cell count — the
constant host meets both dynamical repairs, yet the only reading constant on `hball 3 z` is
constant outright: the invariant repair's hypothesis is then met only by a reading that carries
nothing. One radius lower, the implication is restored: `badRead` is genuinely non-constant, and is
constant on `hball 2 z`, since its one distinguished state `o` sits at distance `3` from `z`. -/
theorem joint_dependence_boundary :
    (Corrects constHost Set.univ 3 ∧ HammingNonexpansive constHost ∧
      ∀ v : Mem (Fin 3) Bool → Bool, (∀ x ∈ hball 3 z, ∀ y ∈ hball 3 z, v x = v y) →
        ∀ x y, v x = v y) ∧
      (∀ x ∈ hball 2 z, ∀ y ∈ hball 2 z, badRead x = badRead y) ∧
      (∃ x y, badRead x ≠ badRead y) := by
  refine ⟨⟨constHost_corrects 3, constHost_nonexpansive, fun v hv x y => ?_⟩, ?_, z, o, by decide⟩
  · rw [hball_three_eq_univ] at hv
    exact hv x (Set.mem_univ x) y (Set.mem_univ y)
  · intro x hx y hy
    have hxo : x ≠ o := by
      intro hxeq
      have hd : hammingDist z x ≤ 2 := hx
      rw [hxeq] at hd
      have heq3 : hammingDist z o = 3 := by decide
      omega
    have hyo : y ≠ o := by
      intro hyeq
      have hd : hammingDist z y ≤ 2 := hy
      rw [hyeq] at hd
      have heq3 : hammingDist z o = 3 := by decide
      omega
    change decide (x = o) = decide (y = o)
    exact decide_eq_decide.mpr (iff_of_false hxo hyo)

end JointDependenceGuard

/-! ## The price: what the margin costs in expressiveness -/

section Price

variable {ι V M : Type*} [Fintype ι] [DecidableEq V] [Finite V]

/-- **The margin the debt demands is bought in carried content** ([Inevitability] §6, Proposition
6.1(iv)). By the repair tax ([Persistence] §10.1, `ALT.repair_tax`) a reading whose
margin covers the debt `E` has `E`-ball-disjoint value classes, so the number of settled values it
can distinguish is at most `|Mem| / |Ball_E|`.

How much this costs depends on which margin the guest actually needs, and that is decided by the
host, not by the learning problem. Under `survives_of_margin` the needed margin is the whole debt,
so a guest with more to learn — a longer rule, a finer `ε` — is pushed to a wider margin and, since
the ball grows fast in its radius, to correspondingly fewer distinguishable values: the learning
debt is then paid in expressiveness. Under `Corrects.survives` the needed margin is only the
per-event radius, and the price does **not** scale with what the guest has to learn. The theorem
below is stated for any `E` below the margin and is silent on which regime applies.

Note this needs only `HasMargin` at radius `E`, which `HasMargin.mono` supplies from any larger
margin — so no ball-cardinality monotonicity is involved. -/
theorem capacity_price {U : Mem ι V → Mem ι V} {B : Set (Mem ι V)} {v : Mem ι V → M} {e E : ℕ}
    (hm : HasMargin U B v e) (hEe : E ≤ e) (c : Mem ι V) :
    Nat.card ↥(v '' omegaLimit U B) * Nat.card ↥(hball E c) ≤ Nat.card (Mem ι V) :=
  repair_tax (hm.mono hEe) c

end Price

end ALT
