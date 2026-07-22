/-
Copyright (c) 2026 Mykola Palamarchuk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mykola Palamarchuk
-/
import ALT.SQAlgorithm

-- Formal-check file, not Mathlib-destined: opt out of the house-style header linter.
set_option linter.style.header false

/-!
# The commitment step's selector: which rule the learner commits to ([Discovery] §5)

Provenance: [Discovery] Theorem 5.1(iv), the commitment step — the bridge from the §3 posterior to
the §4 read-only code.

## The boundary this file draws, and does not cross
[Discovery] Theorem 5.1(iv) says: *once the posterior mass on `R` exceeds `1 − δ/2` (after
`T_discover`), the rule `R` is written into the persistent code `s_code`.* The paper is explicit
that this is an **architectural assumption** — it is *not* derived in §3, where the learner's state
is the full mixture rather than a single rule — and that the residual stochastic failure mode is
`s_code` corruption, charged the separate `δ/2` budget.

What is machine-checked here is the step's **selector**, and only that:
* **which** candidate the threshold picks out, and that it picks out *at most one*
  (`commits_unique`) — so "the rule `R`" is a well-defined object rather than a hopeful singular;
* that the selected candidate **is the truth** (`commits_truth`), under the discovery hypotheses;
* that the selection is **time-stable** past the discovery horizon (`commits_stable`) — the
  learner does not commit to one rule and later to another.

What remains an architectural assumption, exactly as the paper states it:
* the **write** itself — that the selected rule is transferred into the persistent code `s_code`.
  No code region, no write operation and no persistence claim appears below; the selector is a
  function of the posterior alone;
* the **`δ/2` corruption budget** for `s_code` — a substrate-reliability premise, with no
  counterpart here.

So this file hardens the *discovery* side of the hand-off (the posterior determines a unique, true,
stable rule) and leaves the *retention* side (writing it, and keeping it) where the paper leaves it.

## The objects
Everything is stated over the algorithm object of [SQ] §4 / Appendix A (FV-K) — `alive`, the
survivor set, and the pruned posterior that `SQAlgorithm.algorithm_discovery` bounds below by
`1 − δ/2`. That quotient is unnamed there (it appears inline in the conclusion); `prunedPosterior`
names it and nothing more, so `algorithm_discovery`'s conclusion *is*
`1 − δ/2 ≤ prunedPosterior … iR` definitionally.

`Commits p S δ i` is a predicate rather than an `Option`-valued selector: the posterior is
real-valued, so a `Finset.filter` at the threshold would have to bake classical decidability into
the definition and carry that instance through every membership rewrite, and extracting an element
from the resulting `Finset ι` — `ι` unordered — would need a further arbitrary choice. The
predicate says the same thing, and the capstone's `↔ i = iR` form states existence, uniqueness and
the identity of the selected rule in a single equivalence.

## Where `δ < 1` is load-bearing
Uniqueness is a normalization argument: the pruned posterior sums to `1` over the survivor set
(`prunedPosterior_sum_alive`), so two candidates both at mass `≥ 1 − δ/2` force `2 − δ ≤ 1`. That
is a contradiction exactly when `δ < 1`. The hypothesis is therefore not cosmetic and is not
weakened to `δ ≤ 1`: at `δ = 1` the threshold is `1/2`, two candidates can tie there, and the
committed rule is genuinely undefined.

The threshold is stated as `1 − δ/2 ≤ p i` where the paper writes "exceeds `1 − δ/2`". The
non-strict form is what `algorithm_discovery` delivers, and it is the *easier* trigger — it commits
at least as often — so uniqueness, the load-bearing direction, is proved against the harder case.
-/

namespace CommitmentSeam

open SQAlgorithm SQMixtureSupermartingale

variable {X : Type*} [DecidableEq X] {ι : Type*} {Q : Type*}

/-! ## The posterior the commitment step reads, and the threshold it applies -/

/-- **The pruned posterior** of the [SQ] §4 algorithm: the Bayes posterior with the normalizer
restricted to the survivor set `alive … n ω`. This is the quantity `SQAlgorithm.algorithm_discovery`
bounds below by `1 − δ/2`; naming it changes nothing (the two are definitionally equal), it only
makes the commitment step's input citable. -/
noncomputable def prunedPosterior [Fintype ι] (pred : ι → (s : ℕ) → (Fin s → X) → X)
    (stat : ι → Q → ℝ) (oracleAns : Q → ℝ) (τ : ℝ) (sched : ℕ → Finset Q) (w : ι → ℝ) (n : ℕ)
    (ω : ℕ → X) (i : ι) : ℝ :=
  w i * L (detFactor pred) i n ω
    / ∑ j ∈ alive pred stat oracleAns τ sched Finset.univ n ω, w j * L (detFactor pred) j n ω

/-- **The commitment predicate** ([Discovery] §5, Theorem 5.1(iv)): candidate `i` is one the
learner would commit to when it is still alive and its posterior mass has reached the threshold
`1 − δ/2`. This is the *selector* of the commitment step — the write into the persistent code is
the architectural assumption the module docstring records, and is not modelled. -/
def Commits (p : ι → ℝ) (S : Finset ι) (δ : ℝ) (i : ι) : Prop :=
  i ∈ S ∧ 1 - δ / 2 ≤ p i

/-! ## The selector is well defined -/

/-- **At most one candidate is ever committed.** A normalization argument, and the only place the
posterior's total mass enters: two candidates at mass `≥ 1 − δ/2` would together carry `2 − δ`,
which exceeds the available mass `1` precisely because `δ < 1`.

Stated for an arbitrary real-valued mass `p` on a finite candidate set `S` with total mass at most
`1`, so it applies to the pruned posterior (whose mass over the survivor set is exactly `1`) without
assuming anything else about the algorithm. -/
theorem commits_unique {p : ι → ℝ} {S : Finset ι} {δ : ℝ} (hδ : δ < 1)
    (hnn : ∀ i ∈ S, 0 ≤ p i) (hsum : ∑ i ∈ S, p i ≤ 1) {i j : ι}
    (hi : Commits p S δ i) (hj : Commits p S δ j) : i = j := by
  classical
  by_contra hne
  have hsub : ({i, j} : Finset ι) ⊆ S := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact hi.1
    · exact hj.1
  have hpair : ∑ x ∈ ({i, j} : Finset ι), p x ≤ ∑ x ∈ S, p x :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub fun x hx _ => hnn x hx
  rw [Finset.sum_pair hne] at hpair
  have hbi := hi.2
  have hbj := hj.2
  linarith

/-! ## The pruned posterior is a probability on the survivor set -/

/-- The survivor set carries positive mass: the truth is alive (`SQAlgorithm.truth_survives`) and,
being realizable, contributes its full prior weight `w iR > 0`. This is the nonemptiness the pruned
posterior is conditioned on — carried as a hypothesis chain rather than assumed. -/
theorem alive_mass_pos [Fintype ι] (pred : ι → (s : ℕ) → (Fin s → X) → X) (stat : ι → Q → ℝ)
    (oracleAns : Q → ℝ) (τ : ℝ) (hτ : 0 ≤ τ) (sched : ℕ → Finset Q) (w : ι → ℝ) (ω : ℕ → X)
    (iR : ι) (hw : ∀ i, 0 ≤ w i) (hwiR : 0 < w iR)
    (hreal : ∀ s, pred iR s (fun k => ω k) = ω s)
    (hclose : ∀ t, ∀ φ ∈ sched t, |oracleAns φ - stat iR φ| ≤ τ) (n : ℕ) :
    0 < ∑ j ∈ alive pred stat oracleAns τ sched Finset.univ n ω,
      w j * L (detFactor pred) j n ω := by
  have hLnn : ∀ i, 0 ≤ L (detFactor pred) i n ω := by
    intro i
    simp only [L]
    exact Finset.prod_nonneg fun s _ => (detFactor_mem_Icc pred i s ω).1
  have hLiR : L (detFactor pred) iR n ω = 1 := by
    rw [L_det_eq_indicator, if_pos fun s _ => hreal s]
  refine Finset.sum_pos' (fun i _ => mul_nonneg (hw i) (hLnn i)) ⟨iR, ?_, ?_⟩
  · exact truth_survives pred stat oracleAns τ hτ sched Finset.univ ω iR (Finset.mem_univ iR)
      hreal hclose n
  · rw [hLiR, mul_one]; exact hwiR

/-- The pruned posterior is nonnegative. -/
theorem prunedPosterior_nonneg [Fintype ι] (pred : ι → (s : ℕ) → (Fin s → X) → X)
    (stat : ι → Q → ℝ) (oracleAns : Q → ℝ) (τ : ℝ) (sched : ℕ → Finset Q) (w : ι → ℝ) (n : ℕ)
    (ω : ℕ → X) (hw : ∀ i, 0 ≤ w i) (i : ι) :
    0 ≤ prunedPosterior pred stat oracleAns τ sched w n ω i := by
  have hLnn : ∀ j, 0 ≤ L (detFactor pred) j n ω := by
    intro j
    simp only [L]
    exact Finset.prod_nonneg fun s _ => (detFactor_mem_Icc pred j s ω).1
  exact div_nonneg (mul_nonneg (hw i) (hLnn i))
    (Finset.sum_nonneg fun j _ => mul_nonneg (hw j) (hLnn j))

/-- **The pruned posterior has total mass `1` on the survivor set** — it is a genuine probability
there, which is what makes `commits_unique` applicable. (Over the *whole* candidate set the same
quotient sums to more than `1`, the normalizer running over survivors only; the survivor set is the
right domain for the commitment step, and the one the paper's "posterior mass on `R`" refers to.) -/
theorem prunedPosterior_sum_alive [Fintype ι] (pred : ι → (s : ℕ) → (Fin s → X) → X)
    (stat : ι → Q → ℝ) (oracleAns : Q → ℝ) (τ : ℝ) (sched : ℕ → Finset Q) (w : ι → ℝ) (n : ℕ)
    (ω : ℕ → X)
    (hden : 0 < ∑ j ∈ alive pred stat oracleAns τ sched Finset.univ n ω,
      w j * L (detFactor pred) j n ω) :
    ∑ i ∈ alive pred stat oracleAns τ sched Finset.univ n ω,
        prunedPosterior pred stat oracleAns τ sched w n ω i = 1 := by
  simp only [prunedPosterior]
  rw [← Finset.sum_div, div_self hden.ne']

/-! ## The selector returns the truth -/

/-- **The truth is committed.** Past the discovery horizon the true rule is alive
(`SQAlgorithm.truth_survives`) and its pruned posterior has reached the threshold
(`SQAlgorithm.algorithm_discovery`) — so it satisfies the commitment predicate. -/
theorem commits_truth [Fintype X] [Fintype ι]
    (pred : ι → (s : ℕ) → (Fin s → X) → X) (stat : ι → Q → ℝ) (oracleAns : Q → ℝ)
    (τ : ℝ) (hτ : 0 ≤ τ) (sched : ℕ → Finset Q) (w : ι → ℝ) (ω : ℕ → X) (iR : ι)
    (hw : ∀ i, 0 ≤ w i) (k : ℕ) (hwR : w iR = (2 : ℝ) ^ (-(k : ℝ))) (hsumw : ∑ i, w i ≤ 1)
    (hreal : ∀ s, pred iR s (fun k => ω k) = ω s)
    (hclose : ∀ t, ∀ φ ∈ sched t, |oracleAns φ - stat iR φ| ≤ τ)
    (δ ε₀ : ℝ) (hδ : 0 < δ) (hε : 0 < ε₀) (n : ℕ)
    (hsep : ∀ i, i ≠ iR → ∀ t ∈ Finset.range n,
      ε₀ ≤ BayesRedundancy.sqHellinger (fun x => if x = ω t then 1 else 0)
             (fun x => if pred i t (fun j => ω j) = x then (1 : ℝ) else 0))
    (hT : ((k : ℝ) * Real.log 2 + Real.log (2 / δ)) / (2 * ε₀) ≤ (n : ℝ)) :
    Commits (prunedPosterior pred stat oracleAns τ sched w n ω)
      (alive pred stat oracleAns τ sched Finset.univ n ω) δ iR := by
  classical
  exact ⟨truth_survives pred stat oracleAns τ hτ sched Finset.univ ω iR (Finset.mem_univ iR)
      hreal hclose n,
    algorithm_discovery pred stat oracleAns τ hτ sched w ω iR hw k hwR hsumw hreal hclose
      δ ε₀ hδ hε n hsep hT⟩

/-! ## The capstone: a well-defined, true, time-stable commitment -/

/-- **The commitment step's selector ([Discovery] §5, Theorem 5.1(iv)).** Past the discovery
horizon, the candidates satisfying the commitment predicate are *exactly* the true rule — at every
such time. The single equivalence carries all three claims the seam needs:
* **existence** — the truth commits (`← ` direction),
* **well-definedness** — nothing else does (`→` direction, via `commits_unique`),
* **time-stability** — the right-hand side `i = iR` does not depend on `n`, so the committed rule
  is the same at every time past the horizon (spelled out in `commits_stable`).

`δ < 1` is required, not cosmetic: it is exactly what makes the threshold `1 − δ/2` exceed half the
available mass, and hence what makes the selection unique. The separation hypothesis is taken at
*all* times rather than below a fixed horizon, since a per-time hypothesis would make the stability
claim vacuous — a fresh premise for every `n` is not a statement about the same learner over time.

The remaining clauses of Theorem 5.1(iv) — that the selected rule is *written into* the persistent
code `s_code`, and the `δ/2` corruption budget for keeping it there — are the architectural
assumptions the paper states as such. They are not established here, and nothing below refers to a
code region. -/
theorem commitment_seam [Fintype X] [Fintype ι]
    (pred : ι → (s : ℕ) → (Fin s → X) → X) (stat : ι → Q → ℝ) (oracleAns : Q → ℝ)
    (τ : ℝ) (hτ : 0 ≤ τ) (sched : ℕ → Finset Q) (w : ι → ℝ) (ω : ℕ → X) (iR : ι)
    (hw : ∀ i, 0 ≤ w i) (k : ℕ) (hwR : w iR = (2 : ℝ) ^ (-(k : ℝ))) (hsumw : ∑ i, w i ≤ 1)
    (hreal : ∀ s, pred iR s (fun k => ω k) = ω s)
    (hclose : ∀ t, ∀ φ ∈ sched t, |oracleAns φ - stat iR φ| ≤ τ)
    (δ ε₀ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) (hε : 0 < ε₀)
    (hsep : ∀ i, i ≠ iR → ∀ t,
      ε₀ ≤ BayesRedundancy.sqHellinger (fun x => if x = ω t then 1 else 0)
             (fun x => if pred i t (fun j => ω j) = x then (1 : ℝ) else 0)) :
    ∀ n : ℕ, ((k : ℝ) * Real.log 2 + Real.log (2 / δ)) / (2 * ε₀) ≤ (n : ℝ) →
      ∀ i, Commits (prunedPosterior pred stat oracleAns τ sched w n ω)
          (alive pred stat oracleAns τ sched Finset.univ n ω) δ i ↔ i = iR := by
  intro n hT i
  have hwiR : 0 < w iR := by rw [hwR]; positivity
  have hden := alive_mass_pos pred stat oracleAns τ hτ sched w ω iR hw hwiR hreal hclose n
  have htruth := commits_truth pred stat oracleAns τ hτ sched w ω iR hw k hwR hsumw hreal hclose
    δ ε₀ hδ hε n (fun j hj t _ => hsep j hj t) hT
  constructor
  · intro hi
    exact commits_unique hδ1
      (fun j _ => prunedPosterior_nonneg pred stat oracleAns τ sched w n ω hw j)
      (le_of_eq (prunedPosterior_sum_alive pred stat oracleAns τ sched w n ω hden)) hi htruth
  · rintro rfl
    exact htruth

/-- **The commitment is time-stable.** Two commitments made at any two times past the discovery
horizon are to the same rule. This is not a separate argument: `commitment_seam` already identifies
the committed candidate as `iR` at each time independently, so stability is that identification
applied twice. Recording it as its own statement is what makes "the learner does not re-commit"
a citable fact rather than a reading of the capstone. -/
theorem commits_stable [Fintype X] [Fintype ι]
    (pred : ι → (s : ℕ) → (Fin s → X) → X) (stat : ι → Q → ℝ) (oracleAns : Q → ℝ)
    (τ : ℝ) (hτ : 0 ≤ τ) (sched : ℕ → Finset Q) (w : ι → ℝ) (ω : ℕ → X) (iR : ι)
    (hw : ∀ i, 0 ≤ w i) (k : ℕ) (hwR : w iR = (2 : ℝ) ^ (-(k : ℝ))) (hsumw : ∑ i, w i ≤ 1)
    (hreal : ∀ s, pred iR s (fun k => ω k) = ω s)
    (hclose : ∀ t, ∀ φ ∈ sched t, |oracleAns φ - stat iR φ| ≤ τ)
    (δ ε₀ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) (hε : 0 < ε₀)
    (hsep : ∀ i, i ≠ iR → ∀ t,
      ε₀ ≤ BayesRedundancy.sqHellinger (fun x => if x = ω t then 1 else 0)
             (fun x => if pred i t (fun j => ω j) = x then (1 : ℝ) else 0))
    {m n : ℕ} (hm : ((k : ℝ) * Real.log 2 + Real.log (2 / δ)) / (2 * ε₀) ≤ (m : ℝ))
    (hn : ((k : ℝ) * Real.log 2 + Real.log (2 / δ)) / (2 * ε₀) ≤ (n : ℝ)) {i j : ι}
    (hi : Commits (prunedPosterior pred stat oracleAns τ sched w m ω)
      (alive pred stat oracleAns τ sched Finset.univ m ω) δ i)
    (hj : Commits (prunedPosterior pred stat oracleAns τ sched w n ω)
      (alive pred stat oracleAns τ sched Finset.univ n ω) δ j) : i = j := by
  have hseam := commitment_seam pred stat oracleAns τ hτ sched w ω iR hw k hwR hsumw hreal hclose
    δ ε₀ hδ hδ1 hε hsep
  rw [(hseam m hm i).1 hi, (hseam n hn j).1 hj]

end CommitmentSeam
