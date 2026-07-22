/-
Copyright (c) 2026 Mykola Palamarchuk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mykola Palamarchuk
-/
import ALT.SQObjects
import ALT.SQVersionSpace

-- Formal-check file, not Mathlib-destined: opt out of the house-style linters (long lines/defs).
set_option linter.style.header false
set_option linter.style.longLine false
-- `SepFam` is an undecidable predicate over abstract types, so the powerset `filter` in `sqDim`
-- (and the maximal-family construction here) needs a classical instance; scope-level
-- `open scoped Classical` (below) is deliberate and matches `ALT/SQObjects.lean`.
set_option linter.style.openClassical false

/-!
# The SQ version-space envelope via Szörényi's maximality + packing ([SQ] App A, FV-L)

Provenance: [SQ], §3.4 (statistical dimension `d_SQ` +
Assumption A), §4 step (b) (SQ-based enumeration of the version space `M_T`), and Appendix A ("the
version-space bound", "the SQ handle", "the truth survives"). Mathematical route: Szörényi,
"Characterizing Statistical Query Learning: Simplified Notions and Proofs" (ALT 2009) — the
elementary maximality/packing argument (Def 2, §3, Prop 1), NOT the Fourier route.

FV-L builds the BFJKMR-style version-space envelope
directly over FV-J's GENUINE statistical dimension (`SQObjects.sqDim`), discharging the MODELED
envelope premise `candidates r ≤ A · (d_SQ r)^m` that FV-A4 (`SQVersionSpace.candidates_polyBounded`)
left as a hypothesis. Two pieces of added content over FV-J's `survivors_card_le_sqDim` (which
already handles the pairwise-SEPARATED survivor case):
  (a) the query schedule / covering family EXISTS — Szörényi's maximality (`exists_sqNet`);
  (b) a version-space size bound WITHOUT assuming the survivors are pairwise separated
      (`subset_card_le_sqDim_of_ident`), gated on a clean CLASS-LEVEL identifiability hypothesis
      instead of a survivor-set-level separation hypothesis.

## The constant chain (matched to FV-A4 / FV-K `τ / 2τ / 3τ` bookkeeping)
* pruning tolerance `2τ` (a survivor obeys `|ans φ i − o φ| ≤ 2τ` on every scheduled query) — the
  FV-A4/FV-K `sqPrune` rule;
* two survivors are therefore pairwise `4τ`-close on the schedule (`close_on_of_prune`, the abstract
  triangle-inequality analogue of Szörényi's Proposition 1 — see the "Departures" note below on the
  `6ε` correlational constant);
* the covering family (`exists_sqNet`) is a MAXIMAL `τ`-separated subfamily, so two candidates
  assigned to the same covering point are `2τ`-close on EVERY query (global triangle);
* identifiability `hident` at scale `2τ` (distinct candidates differ by `> 2τ` on some query) makes
  the covering-point assignment injective, so the version space embeds into the covering family and
  `V.card ≤ sqDim M τ ans`.

## What this DOES establish
* `close_on_of_prune` (§ App A / Prop 1 analogue): survivors of the `2τ`-pruning rule against a
  τ-good oracle are pairwise `4τ`-close on the scheduled queries — they need NOT be pairwise
  separated, so FV-J's pigeonhole does not apply directly.
* `exists_sqNet` (Szörényi's maximality, §3): every finite class `M` has a MAXIMAL `τ`-separated
  subfamily `S` with `S.card = sqDim M τ ans` that COVERS `M` — every candidate is `τ`-close (on
  every query) to some member of `S`. This is the abstract "query schedule exists" residue that FV-J
  and FV-K left open.
* `subset_card_le_sqDim_of_ident` (the envelope proper): under class-level identifiability at scale
  `2τ`, ANY subfamily `V ⊆ M` — in particular the version space — has `V.card ≤ sqDim M τ ans`. The
  covering map `V → S` is injective by identifiability, so `V` embeds into a `τ`-separated family.
* `version_space_card_le` (the App-A "version-space bound", assembled): the `2τ`-pruning survivor
  set is pairwise `4τ`-close on the schedule AND has `card ≤ sqDim M τ ans`.
* `fvA4_envelope_discharged`: instantiates FV-A4's modeled envelope premise
  (`SQVersionSpace.candidates_polyBounded`'s `candidates ≤ A · d_SQ^m`) from the linear envelope
  with `A = m = 1` — closing the loop with the literal `PolyBounded` chain, exactly as FV-J's
  `survivors_polyBounded_of_separated` does, but with class-level identifiability replacing the
  survivor-set separation hypothesis.

## The identifiability hypothesis (named, flagged prominently)
`subset_card_le_sqDim_of_ident` / `fvA4_envelope_discharged` assume
`hident : ∀ i ∈ M, ∀ j ∈ M, (∀ φ, |ans φ i − ans φ j| ≤ 2τ) → i = j` — "distinct candidate rules are
`2τ`-distinguishable on some query". This is where [SQ]'s "deterministic distinct rules are
distinguishable" lives. It is a real hypothesis: with it, the covering map is injective and the
version space collapses onto a separated family; WITHOUT it, bounding the near-duplicate clusters
inside a covering ball by the extra `poly(k)` factor of App A's `poly(d_SQ)·poly(k)` is exactly the
harder BFJKMR clustering argument (which needs the `[−1,1]` answer range and a per-query packing
count), and stays in prose. Flagged, not hidden.

## What this does NOT establish (out of scope / stays in prose; no overclaiming)
* Not the full BFJKMR `poly(d_SQ)·poly(k)` clustering bound WITHOUT identifiability (the harder
  argument above); we deliver the LINEAR envelope `≤ sqDim` under identifiability, which is stronger
  than `poly(d_SQ)` where it applies and suffices to discharge FV-A4.
* Not Szörényi's Theorem 2 query lower bound `(dτ²−1)/2` (a nice-to-have companion needing the
  correlation/ℓ² geometry) — de-scoped.
* Not the concrete schedule for a named class (the `ans`, oracle `o`, and schedule `Qs` are abstract
  data), nor the single-trajectory → SQ-oracle reduction (FV-E/ergodicity), which supply `hident`
  and the τ-good oracle downstream.
-/

namespace SQEnvelope

open SQObjects Filter

open scoped Classical

variable {ι Q : Type*}

/-- Triangle helper: two reals each within `d` of a common `c` are within `2d` of each other. -/
private lemma abs_sub_le_two_mul (a b c d : ℝ) (h1 : |a - c| ≤ d) (h2 : |b - c| ≤ d) :
    |a - b| ≤ 2 * d := by
  have h3 : |a - b| ≤ |a - c| + |c - b| := abs_sub_le a c b
  have h4 : |c - b| = |b - c| := abs_sub_comm c b
  rw [h4] at h3
  linarith

/-- **Closeness transitivity — general constant** (Szörényi Prop 1, abstract form): if `i` and `j`
each answer within `c` of the same oracle answers on every scheduled query `φ ∈ Qs`, then `i` and
`j` are pairwise `2c`-close on `Qs`. Pure triangle inequality (the abstract analogue of the `⟨·,·⟩`
inner-product bound; see the module docstring on the `6ε` correlational constant). -/
theorem pairwise_close_on_of_oracle (c : ℝ) (ans : Q → ι → ℝ) (o : Q → ℝ) (Qs : Finset Q)
    {i j : ι}
    (hi : ∀ φ ∈ Qs, |ans φ i - o φ| ≤ c) (hj : ∀ φ ∈ Qs, |ans φ j - o φ| ≤ c) :
    ∀ φ ∈ Qs, |ans φ i - ans φ j| ≤ 2 * c := fun φ hφ =>
  abs_sub_le_two_mul (ans φ i) (ans φ j) (o φ) c (hi φ hφ) (hj φ hφ)

/-- **Target 2 — the version space is a close cluster on the schedule** (App A): survivors of the
`2τ`-pruning rule (`|ans φ i − o φ| ≤ 2τ` on every scheduled query) are pairwise `4τ`-close on the
schedule. So the version space need NOT be pairwise separated — FV-J's survivor pigeonhole does not
apply directly, and the envelope needs the covering argument below. -/
theorem close_on_of_prune (τ : ℝ) (ans : Q → ι → ℝ) (o : Q → ℝ) (Qs : Finset Q) {i j : ι}
    (hi : ∀ φ ∈ Qs, |ans φ i - o φ| ≤ 2 * τ) (hj : ∀ φ ∈ Qs, |ans φ j - o φ| ≤ 2 * τ) :
    ∀ φ ∈ Qs, |ans φ i - ans φ j| ≤ 4 * τ := by
  intro φ hφ
  have h := pairwise_close_on_of_oracle (2 * τ) ans o Qs hi hj φ hφ
  linarith

/-- **Target 1 — Szörényi's maximality (the covering family exists).** Every finite class `M` has a
MAXIMAL `τ`-separated subfamily `S`: `S` is itself a `SepFam` with `S.card = sqDim M τ ans`, and by
maximality it COVERS `M` — every candidate `i ∈ M` is `τ`-close on EVERY query to some `j ∈ S`
(otherwise `i` could be added to `S`, contradicting maximum cardinality). This discharges the
abstract "query schedule / covering family exists" residue left open by FV-J and FV-K. -/
theorem exists_sqNet (M : Finset ι) (τ : ℝ) (hτ : 0 ≤ τ) (ans : Q → ι → ℝ) :
    ∃ S : Finset ι, S ⊆ M ∧ SepFam M τ ans S ∧ S.card = sqDim M τ ans ∧
      ∀ i ∈ M, ∃ j ∈ S, ∀ φ, |ans φ i - ans φ j| ≤ τ := by
  have hPne : (M.powerset.filter (SepFam M τ ans)).Nonempty := by
    refine ⟨∅, ?_⟩
    rw [Finset.mem_filter, Finset.mem_powerset]
    exact ⟨Finset.empty_subset M, Finset.empty_subset M,
      fun i hi => absurd hi (Finset.notMem_empty i)⟩
  obtain ⟨S, hSmem, hSsup⟩ := Finset.exists_mem_eq_sup _ hPne Finset.card
  rw [Finset.mem_filter, Finset.mem_powerset] at hSmem
  obtain ⟨hSM, hSsep⟩ := hSmem
  have hScard : S.card = sqDim M τ ans := hSsup.symm
  refine ⟨S, hSM, hSsep, hScard, ?_⟩
  intro i hiM
  by_cases hiS : i ∈ S
  · exact ⟨i, hiS, fun φ => by rw [sub_self, abs_zero]; exact hτ⟩
  · by_contra hcon
    simp only [not_exists, not_and, not_forall, not_le] at hcon
    -- hcon : ∀ j ∈ S, ∃ φ, τ < |ans φ i - ans φ j|  (i is separated from every net member)
    have hins : SepFam M τ ans (insert i S) := by
      refine ⟨Finset.insert_subset hiM hSM, ?_⟩
      intro a ha b hb hab
      rw [Finset.mem_insert] at ha hb
      rcases ha with rfl | ha <;> rcases hb with rfl | hb
      · exact absurd rfl hab
      · obtain ⟨φ, hφ⟩ := hcon b hb
        exact ⟨φ, hφ⟩
      · obtain ⟨φ, hφ⟩ := hcon a ha
        refine ⟨φ, ?_⟩
        change τ < |ans φ a - ans φ b|
        rw [abs_sub_comm]
        exact hφ
      · exact hSsep.2 a ha b hb hab
    have hmem : insert i S ∈ M.powerset.filter (SepFam M τ ans) := by
      rw [Finset.mem_filter, Finset.mem_powerset]
      exact ⟨hins.1, hins⟩
    have hle := Finset.le_sup (f := Finset.card) hmem
    rw [Finset.card_insert_of_notMem hiS, hSsup] at hle
    omega

/-- **Target 3 — the version-space envelope proper.** Under class-level identifiability at scale `2τ`
(`hident`: distinct candidates differ by `> 2τ` on some query), ANY subfamily `V ⊆ M` — in
particular the `2τ`-pruning version space — satisfies `V.card ≤ sqDim M τ ans`.

Proof (Szörényi packing): take the maximal `τ`-separated covering family `S` (`exists_sqNet`), with
`S.card = sqDim`. Assign each `v ∈ V` a covering point `f v ∈ S` that it is `τ`-close to. If
`f a = f b`, then `a` and `b` are both `τ`-close to that point, hence `2τ`-close on every query, so
`hident` forces `a = b`: the assignment is injective on `V`, and `V` embeds into `S`.

The identifiability hypothesis is where "distinct rules are distinguishable" lives; removing it and
bounding the covering-ball clusters by an extra `poly(k)` factor is the harder BFJKMR clustering
argument (module docstring). -/
theorem subset_card_le_sqDim_of_ident (M : Finset ι) (τ : ℝ) (hτ : 0 ≤ τ) (ans : Q → ι → ℝ)
    (V : Finset ι) (hVM : V ⊆ M)
    (hident : ∀ i ∈ M, ∀ j ∈ M, (∀ φ, |ans φ i - ans φ j| ≤ 2 * τ) → i = j) :
    V.card ≤ sqDim M τ ans := by
  obtain ⟨S, _hSM, _hSsep, hScard, hcover⟩ := exists_sqNet M τ hτ ans
  -- covering-point assignment
  set f : ι → ι := fun i => if h : i ∈ V then Classical.choose (hcover i (hVM h)) else i with hfdef
  have hfmem : ∀ i ∈ V, f i ∈ S := by
    intro i hi
    have hspec := Classical.choose_spec (hcover i (hVM hi))
    simp only [hfdef, dif_pos hi]
    exact hspec.1
  have hfclose : ∀ i ∈ V, ∀ φ, |ans φ i - ans φ (f i)| ≤ τ := by
    intro i hi φ
    have hspec := Classical.choose_spec (hcover i (hVM hi))
    simp only [hfdef, dif_pos hi]
    exact hspec.2 φ
  have hmaps : Set.MapsTo f ↑V ↑S := by
    intro i hi
    rw [Finset.mem_coe] at hi ⊢
    exact hfmem i hi
  have hinj : Set.InjOn f ↑V := by
    intro a ha b hb hfab
    rw [Finset.mem_coe] at ha hb
    have hca := hfclose a ha
    have hcb := hfclose b hb
    have hclose2 : ∀ φ, |ans φ a - ans φ b| ≤ 2 * τ := by
      intro φ
      have h2 := hcb φ
      rw [← hfab] at h2
      exact abs_sub_le_two_mul (ans φ a) (ans φ b) (ans φ (f a)) τ (hca φ) h2
    exact hident a (hVM ha) b (hVM hb) hclose2
  calc V.card ≤ S.card := Finset.card_le_card_of_injOn f hmaps hinj
    _ = sqDim M τ ans := hScard

/-- **The App-A version-space bound, assembled.** The `2τ`-pruning survivor set `V` (against a
τ-good oracle `o` over schedule `Qs`) is (i) pairwise `4τ`-close on the schedule and (ii) has
`V.card ≤ sqDim M τ ans`, under class-level identifiability at scale `2τ`. Part (i) is
`close_on_of_prune`; part (ii) is `subset_card_le_sqDim_of_ident`. -/
theorem version_space_card_le (M : Finset ι) (τ : ℝ) (hτ : 0 ≤ τ) (ans : Q → ι → ℝ)
    (o : Q → ℝ) (Qs : Finset Q) (V : Finset ι) (hVM : V ⊆ M)
    (hsurv : ∀ i ∈ V, ∀ φ ∈ Qs, |ans φ i - o φ| ≤ 2 * τ)
    (hident : ∀ i ∈ M, ∀ j ∈ M, (∀ φ, |ans φ i - ans φ j| ≤ 2 * τ) → i = j) :
    (∀ i ∈ V, ∀ j ∈ V, ∀ φ ∈ Qs, |ans φ i - ans φ j| ≤ 4 * τ)
      ∧ V.card ≤ sqDim M τ ans :=
  ⟨fun i hi j hj => close_on_of_prune τ ans o Qs (hsurv i hi) (hsurv j hj),
    subset_card_le_sqDim_of_ident M τ hτ ans V hVM hident⟩

/-- **Target 4 — FV-A4's modeled envelope premise, discharged.** Reusing
`SQVersionSpace.candidates_polyBounded` verbatim with the `A = m = 1` envelope supplied by
`subset_card_le_sqDim_of_ident`: if the GENUINE statistical dimension `sqDim (Mfam r) τ (ansfam r)`
is polynomially bounded (Assumption A) and each class `Mfam r` is `2τ`-identifiable, then the version
space `Vfam r ⊆ Mfam r` is `poly(r)`. This is exactly `SQObjects.survivors_polyBounded_of_separated`
with class-level identifiability `hident` in place of the survivor-set separation hypothesis `hsep`,
closing the FV-A4 residue with the literal `PolyBounded` chain. -/
theorem fvA4_envelope_discharged (τ : ℝ) (hτ : 0 ≤ τ)
    (Mfam Vfam : ℝ → Finset ι) (ansfam : ℝ → Q → ι → ℝ)
    (hVM : ∀ r, Vfam r ⊆ Mfam r)
    (hident : ∀ r, ∀ i ∈ Mfam r, ∀ j ∈ Mfam r,
      (∀ φ, |ansfam r φ i - ansfam r φ j| ≤ 2 * τ) → i = j)
    (hpoly : ParityCounterexample.PolyBounded (fun r => (sqDim (Mfam r) τ (ansfam r) : ℝ))) :
    ParityCounterexample.PolyBounded (fun r => ((Vfam r).card : ℝ)) := by
  refine SQVersionSpace.candidates_polyBounded _ _ hpoly 1 1 (by norm_num) ?_ ?_
  · filter_upwards with r
    have hle := subset_card_le_sqDim_of_ident (Mfam r) τ hτ (ansfam r) (Vfam r) (hVM r) (hident r)
    have hcast : ((Vfam r).card : ℝ) ≤ (sqDim (Mfam r) τ (ansfam r) : ℝ) := by exact_mod_cast hle
    simpa using hcast
  · filter_upwards with r
    positivity

end SQEnvelope
