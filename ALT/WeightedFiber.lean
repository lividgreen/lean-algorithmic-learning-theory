module

public import ALT.SkewFiber


/-!
# The weighted fiber: selection that *is* Bayesian update ([Inevitability] §6)

A fiber whose state is a **weight vector** over candidate codes, updated by fitness-proportional
selection on a **frequency-independent** fitness equal to the likelihood the candidate assigns the
observed base transition, does not merely resemble a Bayesian learner: the discrete replicator step
`x'ᵢ = xᵢ·fᵢ / f̄` with `fᵢ = P(E|Hᵢ)` *is* the posterior, term for term. `toDist_bayesStep` is that
identity, exactly. It is the reason to prefer weights to a resampled pool: the winner-take-all fiber
on a fixed pool of slots satisfies neither condition.

## What the identity costs on a finite carrier

The exact step is `bayesStep`, and it involves **no division**: multiply each weight by its
likelihood. Its weights grow, and a finite carrier cannot hold them, so a finite fiber must project
back. The projection here is deliberately the one Bayes' rule is *invariant* under — division of
every coordinate by a **common** divisor — so the correspondence is disturbed by nothing except the
rounding residual. `project` divides by `scaleDiv` and then floors every coordinate at one quantum;
the floor is the uniform reserve, and it makes permanent extinction of a candidate impossible.

The residual is real, and `weighted_fiber_not_exactly_bayes` is the honest statement of it: on a
two-candidate, budget-`2` instance the *exact* step reproduces the Bayes posterior term for term,
while the *projected* step returns the prior **unchanged** — Bayes moves the leading candidate from
`2/3` to `4/5` and the finite fiber moves it nowhere, losing a whole step of evidence to the
rounding. So the identity is discharged by construction for the exact fiber and **not** for the
finite one, and the whole of the gap is the carrier projection — which is what a quantitative bound
on the residual would have to price, and what a redundancy argument for a *floored* process would
have to survive.

## Main results

* `bayesStep` / `toDist_bayesStep` — **the replicator step is Bayes' rule**, exactly, on
  unnormalized integer weights. The design constraint, discharged.
* `predFitPos` — predictive fitness made **strictly positive** (`2` for a hit, `1` for a miss). This
  is the Bayes dictionary's own requirement that a likelihood be positive on the support, not a
  patch: fitness-proportional selection is absorbing at zero.
* `scaleDiv` / `project` / `project_le` / `one_le_project` — the carrier projection: a
  common-divisor rescale that fits the budget, with a one-quantum floor. The budget cap is an
  invariant proved of the step (`raw_wGen`), not a constraint built into the carrier.
* `wGen` / `wFiber` / `wWorld` — one generation, transported onto the numeral carrier
  `Fin ((W+1)^C)`, and the skew product over it.
* `argmax` / `argmaxFrame` — the reading: the heaviest candidate. Note it needs **no fitness
  argument**, where the winner-take-all frame did. `argmax_eq_wMax` and `argmax_le_of_eq_wMax` say
  exactly *which* heaviest candidate: the **least** index attaining the maximum weight, the fold
  keeping the incumbent on ties. That is the form a convergence argument reads the frame by, and
  `argmax_eq_of_strict` — the unique-maximum case — is now a corollary of it.
* `settled` / `wGen_settled` / `surjective_argmaxFrame_of_settled` — the pricing assembly's
  imported **coverage** hypothesis is satisfiable, on the settled configuration the floor forces.
* `wGen_settled_of_faithful` / `iterate_wWorld_settled_of_faithful` — the settled configuration is a
  fixed point of **genuine predictive fitness**, whenever the candidate it is settled on predicts
  the base at the state being stepped. It is held still by *selection*, where `wGen_settled` needs
  an information-free fitness and where the pool fiber's settled populations are imposed by a
  variation rule. `surjective_argmaxFrame_of_all_faithful` is the coverage witness re-run on that
  fitness.
* `wPredFrame` — **the base-reading frame**: the heaviest candidate's *prediction of the base*
  rather than its identity, so the values the reading takes come from the base coordinate, which
  the fiber reads but never writes.
* `surjective_wPredFrame_of_faithful` / `wFrames_separate_of_settled` — the base-reading frame's
  coverage, discharged from a candidate decoding to a surjective base rule; and the two frames
  **separated on one dynamics**, over the family of initial states settled on that candidate.
* `wFiber_emergence_pricing` / `wPredFrame_emergence_pricing` — the pricing assembly, transported
  verbatim, and again under the frame swap at the same constant.
  `wPredFrame_emergence_pricing_of_faithful` is the assembly with its coverage hypothesis
  **discharged rather than imported**: the price follows from the decoder and the base alone.
* `weighted_fiber_not_exactly_bayes` — the exact step is Bayes; the projected step, on a small
  instance, discards the evidence entirely.

## Scope

`toDist_bayesStep` is an identity about the *exact* weight dynamics, and nothing here claims the
finite fiber converges.

The pricing assembly's hypothesis is a **coverage** condition — as the *initial state* ranges over
the state space, the reading must take every value in the frame's codomain — and not a convergence
one; the distinction, and the way the two compete for a candidate-valued frame, is `SkewFiber`'s
Scope section. Under the base-reading frame it is no longer imported: it holds of a candidate
decoding to a surjective base rule (`surjective_wPredFrame_of_faithful`), and
`wPredFrame_emergence_pricing_of_faithful` states the price with no hypothesis about the reading at
all. Under the candidate-valued `argmaxFrame` it is still imported, and
`surjective_argmaxFrame_of_settled` is still its witness — kept, and superseded only in strength:
the newer witness runs on the construction's own predictive fitness rather than on an
information-free one, at the cost of a decoder faithful at every candidate.

Coverage and convergence remain **independent**, and neither is claimed to discharge the other.
Coverage quantifies over all initial weight vectors, and the floored development's settling now does
too (`BasinSettling`) — but the candidate the reading settles on **depends on the start**, and a
seeded run can settle on one that has already missed. What would refute coverage is convergence to
the *same* candidate from every initial state, which is not what is proved; so a settled
configuration and a covering frame coexist here — that is what the base-reading frame buys —
without either condition implying the other.

What is not shown: that selection reaches *this* configuration — the budget on one candidate, one
quantum on each other — from an arbitrary weight vector. The configurations exhibited here are
initial conditions, fixed points of the fitness rather than of a variation rule; that the *reading*
settles from every initial vector is `BasinSettling`'s, and it identifies no settled vector. The
rounding residual is exhibited but not bounded — a quantitative bound, and the tracking form of a
redundancy argument for a *floored* process, are not developed here.
-/


@[expose] public section

namespace ALT

open AdditiveComplexity
open Equiv MulAction

-- `•` on the recurrent-core reading is the relabelling action `U • ℓ = ℓ ∘ U⁻¹`; the same local
-- instance `ALT.emergence` is stated under.
attribute [local instance] arrowAction

/-! ## The exact identity: the replicator step is Bayes' rule -/

section Bayes

variable {C : ℕ}

/-- **The replicator step on unnormalized weights**: multiply each candidate's weight by the
likelihood it assigns the observation. Exact integer arithmetic — no division, no rounding, nothing
to approximate. The fitness `f` does not mention `w`, which is precisely the
*frequency-independence* the correspondence with Bayes' rule requires. -/
def bayesStep (f w : Fin C → ℕ) : Fin C → ℕ := fun i => w i * f i

/-- An integer weight vector read as a distribution. -/
def toDist (w : Fin C → ℕ) : Fin C → ℚ := fun i => (w i : ℚ) / ∑ j, (w j : ℚ)

/-- Bayes' rule: posterior proportional to prior times likelihood. -/
def bayesPost (p : Fin C → ℚ) (f : Fin C → ℕ) : Fin C → ℚ :=
  fun i => p i * f i / ∑ j, p j * f j

/-- **The replicator step is Bayes' rule** ([Inevitability] §6, the design constraint). Normalizing
the multiplicative update of the weights gives exactly the Bayes posterior of the normalized prior
under the likelihood `f`.

This is what makes a weighted, fitness-proportional fiber *be* the mixture rather than resemble it,
and it is an identity, not an approximation: the common normalizer cancels. The two hypotheses are
the ones the dictionary needs — a nonzero prior mass, and a likelihood positive on the support. -/
theorem toDist_bayesStep (f w : Fin C → ℕ) (hw : 0 < ∑ j, w j) (hf : ∀ i, 0 < f i) :
    toDist (bayesStep f w) = bayesPost (toDist w) f := by
  have hS : (∑ j, (w j : ℚ)) ≠ 0 := by
    have : ((∑ j, w j : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hw.ne'
    push_cast at this
    exact this
  obtain ⟨j₀, -, hj₀⟩ : ∃ j ∈ Finset.univ, 0 < w j := by
    by_contra hcon
    refine hw.ne' (Finset.sum_eq_zero fun j hj => ?_)
    by_contra hj
    exact hcon ⟨j, Finset.mem_univ j, Nat.pos_of_ne_zero hj⟩
  have hTpos : (0 : ℚ) < ∑ j, (w j : ℚ) * (f j : ℚ) :=
    Finset.sum_pos' (fun j _ => by positivity)
      ⟨j₀, Finset.mem_univ _, mul_pos (by exact_mod_cast hj₀) (by exact_mod_cast hf j₀)⟩
  have hsum : ∑ j, (w j : ℚ) / (∑ k, (w k : ℚ)) * (f j : ℚ)
      = (∑ j, (w j : ℚ) * (f j : ℚ)) / ∑ k, (w k : ℚ) := by
    have hterm : ∀ j : Fin C, (w j : ℚ) / (∑ k, (w k : ℚ)) * (f j : ℚ)
        = ((w j : ℚ) * (f j : ℚ)) * (∑ k, (w k : ℚ))⁻¹ := by
      intro j; rw [div_eq_mul_inv]; ring
    rw [Finset.sum_congr rfl (fun j _ => hterm j), ← Finset.sum_mul, ← div_eq_mul_inv]
  funext i
  simp only [toDist, bayesPost, bayesStep, Nat.cast_mul, hsum]
  rw [div_mul_eq_mul_div, div_div_div_cancel_right₀]
  exact hS

end Bayes

/-! ## Predictive fitness, made positive -/

section Fitness

variable {n₁ C : ℕ}

/-- **Strictly positive predictive fitness** ([Inevitability] §6): a candidate scores `2` when the
rule it encodes predicts where the base actually goes and `1` when it does not.

Positivity is not a patch. Fitness-proportional selection is absorbing at zero — a candidate whose
likelihood is ever `0` is eliminated for good — and the Bayes dictionary asks a likelihood to be
positive on the support. The `{0,1}` fitness of the winner-take-all fiber would eliminate every
candidate that ever mispredicts, which is not what a posterior does. -/
def predFitPos (S : Fin n₁ → Fin n₁) (dec : Fin C → Fin n₁ → Fin n₁) (x : Fin n₁) (c : Fin C) : ℕ :=
  if dec c x = S x then 2 else 1

theorem predFitPos_pos (S : Fin n₁ → Fin n₁) (dec : Fin C → Fin n₁ → Fin n₁) (x : Fin n₁)
    (c : Fin C) : 0 < predFitPos S dec x c := by
  rw [predFitPos]; split <;> norm_num

end Fitness

/-! ## The carrier projection -/

section Project

variable {C : ℕ}

/-- The heaviest weight in a vector. A `Finset.sup` over `Fin C` — a fold over a finite set, so it
is defined and attained whatever the vector, with no unbounded-supremum convention in play. -/
def wMax (w : Fin C → ℕ) : ℕ := Finset.univ.sup w

theorem le_wMax (w : Fin C → ℕ) (i : Fin C) : w i ≤ wMax w := Finset.le_sup (Finset.mem_univ i)

private theorem le_mul_ceilDiv {a W : ℕ} (hW : 0 < W) : a ≤ W * ((a + W - 1) / W) := by
  have h := Nat.div_add_mod (a + W - 1) W
  have hr : (a + W - 1) % W < W := Nat.mod_lt _ hW
  omega

/-- The common divisor that brings the heaviest weight inside the budget `W`.

Dividing *every* coordinate by the *same* number is exactly the operation Bayes' rule is invariant
under — the posterior depends on the weight vector only through its ray — which is why the
projection below disturbs the correspondence by nothing but its rounding residual. -/
def scaleDiv (W : ℕ) (w : Fin C → ℕ) : ℕ := max 1 ((wMax w + W - 1) / W)

theorem scaleDiv_pos (W : ℕ) (w : Fin C → ℕ) : 0 < scaleDiv W w :=
  lt_of_lt_of_le Nat.one_pos (le_max_left _ _)

/-- **The carrier projection**: rescale by the common divisor, then floor every coordinate at one
quantum.

The floor is the **uniform reserve**. Without it a coordinate that rounds to zero can never recover,
so a candidate — possibly the true one — is permanently extinguished, which exact Bayes never does.
With it, extinction is impossible; the price is one quantum per candidate, the same order as the
rounding already being paid. -/
def project (W : ℕ) (w : Fin C → ℕ) : Fin C → ℕ := fun i => max 1 (w i / scaleDiv W w)

/-- No candidate is ever extinguished. -/
theorem one_le_project (W : ℕ) (w : Fin C → ℕ) (i : Fin C) : 1 ≤ project W w i := le_max_left _ _

/-- **The projection fits the budget.** This is the invariant the carrier needs, proved of the
operation rather than imposed by truncating. -/
theorem project_le {W : ℕ} (hW : 1 ≤ W) (w : Fin C → ℕ) (i : Fin C) : project W w i ≤ W := by
  refine max_le hW ?_
  have h1 : w i ≤ W * ((wMax w + W - 1) / W) := le_trans (le_wMax w i) (le_mul_ceilDiv hW)
  have h2 : w i ≤ W * scaleDiv W w := le_trans h1 (Nat.mul_le_mul_left _ (le_max_right _ _))
  calc w i / scaleDiv W w ≤ W * scaleDiv W w / scaleDiv W w := Nat.div_le_div_right h2
    _ = W := Nat.mul_div_cancel _ (scaleDiv_pos W w)

end Project

/-! ## The finite weighted fiber -/

section Fiber

variable {n₁ C W : ℕ}

/-- A **quantized weight vector**: one weight per candidate, each inside the budget `W`. -/
abbrev WVec (C W : ℕ) := Fin C → Fin (W + 1)

/-- The weights as naturals. -/
def WVec.raw (w : WVec C W) : Fin C → ℕ := fun i => (w i : ℕ)

/-- Package a natural weight vector into the carrier. -/
def pack (W : ℕ) (v : Fin C → ℕ) : WVec C W :=
  fun i => ⟨min (v i) W, Nat.lt_succ_of_le (min_le_right _ _)⟩

/-- **One generation of the weighted fiber**: the exact replicator step, then the carrier
projection. All of the approximation is in the second half. -/
def wGen (W : ℕ) (f : Fin C → ℕ) (w : WVec C W) : WVec C W :=
  pack W (project W (bayesStep f (WVec.raw w)))

/-- **Packing does not clamp**: the projection already fits, so the step's arithmetic is exactly
`project ∘ bayesStep`. The budget cap is an invariant of the step, not a truncation hidden in the
carrier — which is what makes the residual in `weighted_fiber_not_exactly_bayes` attributable to the
rounding alone. -/
theorem raw_wGen (hW : 1 ≤ W) (f : Fin C → ℕ) (w : WVec C W) :
    WVec.raw (wGen W f w) = project W (bayesStep f (WVec.raw w)) := by
  funext i
  exact min_eq_left (project_le hW _ i)

/-- **The weighted fiber**, transported onto the numeral carrier `Fin ((W+1)^C)` the tables index.
The exponent has moved: the state count is exponential in the *candidate* count, where the
winner-take-all fiber's was exponential in the population. Nothing in the pricing scales with it. -/
def wFiber (W : ℕ) (fit : Fin n₁ → Fin C → ℕ) : Fin n₁ → Fin ((W + 1) ^ C) → Fin ((W + 1) ^ C) :=
  fun x y => finFunctionFinEquiv (wGen W (fit x) (finFunctionFinEquiv.symm y))

/-- **The evolving host with a weighted fiber**: a skew product whose base runs `S` and whose fiber
runs one Bayesian update per base step. -/
def wWorld (W : ℕ) (S : Fin n₁ → Fin n₁) (fit : Fin n₁ → Fin C → ℕ) :
    Fin (n₁ * (W + 1) ^ C) → Fin (n₁ * (W + 1) ^ C) := skewWorldFin S (wFiber W fit)

end Fiber

/-! ## The reading: the heaviest candidate -/

section Frame

variable {n₁ C W : ℕ}

/-- One comparison of the reading's fold: take the challenger only if it is *strictly* heavier, so
the incumbent keeps the slot on a tie. -/
private def argmaxStep (w : Fin C → ℕ) (a i : Fin C) : Fin C := if w a < w i then i else a

/-- **The heaviest candidate**, by a left-to-right fold that keeps the incumbent on ties. -/
def argmax [NeZero C] (w : Fin C → ℕ) : Fin C :=
  (List.finRange C).foldl (fun a i => if w a < w i then i else a) 0

/-- The fold's invariant, in the four clauses the readings below need. Over any list the outgoing
accumulator (i) is at least as heavy as the incoming one and (ii) as heavy as everything scanned;
(iii) — the clause that makes the tie-keeping visible — it *is* the incoming accumulator whenever
that already matches its weight; and (iv), on a sorted list whose entries all dominate the incoming
accumulator, it is the **least** index attaining the maximum. -/
private theorem foldl_argmaxStep {w : Fin C → ℕ} :
    ∀ (l : List (Fin C)) (a : Fin C), (∀ i ∈ l, a ≤ i) → l.Pairwise (· ≤ ·) →
      w a ≤ w (l.foldl (argmaxStep w) a)
        ∧ (∀ i ∈ l, w i ≤ w (l.foldl (argmaxStep w) a))
        ∧ (w a = w (l.foldl (argmaxStep w) a) → l.foldl (argmaxStep w) a = a)
        ∧ (∀ i ∈ l, w i = w (l.foldl (argmaxStep w) a) → l.foldl (argmaxStep w) a ≤ i) := by
  intro l
  induction l with
  | nil => exact fun a _ _ => ⟨le_rfl, by simp, fun _ => rfl, by simp⟩
  | cons x l ih =>
      intro a hle hp
      have hxl : ∀ i ∈ l, x ≤ i := (List.pairwise_cons.mp hp).1
      have hpl : l.Pairwise (· ≤ ·) := (List.pairwise_cons.mp hp).2
      have hax : a ≤ x := hle x List.mem_cons_self
      rw [List.foldl_cons]
      by_cases hlt : w a < w x
      · rw [show argmaxStep w a x = x from ite_eq_left hlt]
        obtain ⟨ih1, ih2, ih3, ih4⟩ := ih x hxl hpl
        refine ⟨le_trans hlt.le ih1, ?_, fun heq => absurd heq (by omega), ?_⟩
        · intro i hi
          rcases List.mem_cons.mp hi with rfl | hi
          · exact ih1
          · exact ih2 i hi
        · intro i hi heq
          rcases List.mem_cons.mp hi with rfl | hi
          · exact le_of_eq (ih3 heq)
          · exact ih4 i hi heq
      · rw [show argmaxStep w a x = a from ite_eq_right hlt]
        obtain ⟨ih1, ih2, ih3, ih4⟩ := ih a (fun i hi => hle i (List.mem_cons_of_mem _ hi)) hpl
        refine ⟨ih1, ?_, ih3, ?_⟩
        · intro i hi
          rcases List.mem_cons.mp hi with rfl | hi
          · omega
          · exact ih2 i hi
        · intro i hi heq
          rcases List.mem_cons.mp hi with rfl | hi
          · rw [ih3 (by omega)]; exact hax
          · exact ih4 i hi heq

private theorem argmax_spec [NeZero C] (w : Fin C → ℕ) :
    w (argmax w) = wMax w ∧ ∀ i : Fin C, w i = wMax w → argmax w ≤ i := by
  obtain ⟨-, h2, -, h4⟩ :=
    foldl_argmaxStep (w := w) (List.finRange C) 0 (fun i _ => Fin.zero_le i)
      (List.pairwise_le_finRange C)
  have hmax : w (argmax w) = wMax w :=
    le_antisymm (le_wMax w _) (Finset.sup_le fun i _ => h2 i (List.mem_finRange i))
  exact ⟨hmax, fun i hi => h4 i (List.mem_finRange i) (hi.trans hmax.symm)⟩

/-- **The reading attains the maximum weight.** -/
theorem argmax_eq_wMax [NeZero C] (w : Fin C → ℕ) : w (argmax w) = wMax w := (argmax_spec w).1

/-- **The reading is the *least* heaviest candidate.** The fold keeps the incumbent on ties and
scans in index order, so among the maximizers it returns the first — a tie-breaking convention, made
explicit, rather than an unspecified choice. -/
theorem argmax_le_of_eq_wMax [NeZero C] {w : Fin C → ℕ} {i : Fin C} (h : w i = wMax w) :
    argmax w ≤ i := (argmax_spec w).2 i h

/-- A strictly heaviest candidate is the one the reading returns. Unlike the winner-take-all fold,
no tie-breaking convention is in play: the maximum is unique. -/
theorem argmax_eq_of_strict [NeZero C] {w : Fin C → ℕ} {c : Fin C} (h : ∀ i, i ≠ c → w i < w c) :
    argmax w = c := by
  by_contra hne
  have h1 := argmax_eq_wMax w
  have h2 := le_wMax w c
  have h3 := h (argmax w) hne
  omega

/-- **The weighted reading** ([Inevitability] §6): decode the weight vector out of the fiber
coordinate and hand back its heaviest candidate — the maximum-a-posteriori hypothesis.

Note what is absent: the fitness. The winner-take-all frame had to score the population at the
current base state to read it; a weight vector already carries the posterior, so the reading is a
function of the fiber coordinate alone. -/
def argmaxFrame (n₁ W : ℕ) [NeZero C] : Fin (n₁ * (W + 1) ^ C) → Fin C :=
  fun p => argmax (WVec.raw (finFunctionFinEquiv.symm (finProdFinEquiv.symm p).2))

/-- **The base-reading frame** ([Inevitability] §6): read the fittest candidate's *prediction of the
base*. The weight vector's heaviest candidate is decoded into a rule by `dec`, and that rule is
applied to the current base state, so the frame's value is a base state and not a candidate.

This is `ALT.predFrame`'s shape over the weighted carrier, and the change that matters is the
same one: the codomain. Coverage of `Fin n₁` is a question about the base coordinate — which the
fiber reads and never writes — where coverage of `Fin C` by a candidate-valued reading can only be
charged to the initial weight vector. -/
def wPredFrame (n₁ W : ℕ) [NeZero C] (dec : Fin C → Fin n₁ → Fin n₁) :
    Fin (n₁ * (W + 1) ^ C) → Fin n₁ :=
  fun p => dec (argmaxFrame n₁ W p) (finProdFinEquiv.symm p).1

end Frame

/-! ## The coverage hypothesis is satisfiable

The uniform floor changes what "settled" means: a bare point mass is not reachable, because no
coordinate may be zero. The settled configuration is instead the whole budget on one candidate and
one reserved quantum on each of the others — and it is a genuine fixed point.

`argmaxFrame` is a candidate-valued frame, so — exactly as for `ALT.fittestFrame` — its
coverage has to be charged to the initial condition: each candidate is read off its own settled
vector, on dynamics carrying no information.

Two things then happen to that configuration. It turns out to be a fixed point of the *real*
predictive fitness and not only of an information-free one, so what holds it still is selection; and
under `wPredFrame` the reading over it varies with the base point, which is what lets coverage and a
settled population coexist. Both are below, in that order. -/

section Settled

variable {n₁ C W : ℕ}

/-- The **settled** weight vector: the budget on one candidate, the reserve on every other. -/
def settled (W : ℕ) (c : Fin C) : Fin C → ℕ := fun i => if i = c then W else 1

theorem one_le_settled (hW : 1 ≤ W) (c i : Fin C) : 1 ≤ settled W c i := by
  rw [settled]; split <;> omega

theorem settled_le (hW : 1 ≤ W) (c i : Fin C) : settled W c i ≤ W := by
  rw [settled]; split <;> omega

theorem wMax_settled (hW : 1 ≤ W) (c : Fin C) : wMax (settled W c) = W := by
  refine le_antisymm (Finset.sup_le fun i _ => settled_le hW c i) ?_
  have := le_wMax (settled W c) c
  rwa [settled, ite_eq_left rfl] at this

theorem raw_pack_settled (hW : 1 ≤ W) (c : Fin C) :
    WVec.raw (pack W (settled W c) : WVec C W) = settled W c := by
  funext i
  exact min_eq_left (settled_le hW c i)

/-- **A fixed point.** With the base carrying no information — every candidate equally likely — the
settled vector reproduces itself: the common divisor is `1`, so the rescale is trivial, and every
coordinate is already at or above the reserve. -/
theorem wGen_settled (hW : 1 ≤ W) (f : Fin C → ℕ) (hf : ∀ i, f i = 1) (c : Fin C) :
    wGen W f (pack W (settled W c)) = (pack W (settled W c) : WVec C W) := by
  have hstep : bayesStep f (WVec.raw (pack W (settled W c) : WVec C W)) = settled W c := by
    funext i
    rw [bayesStep, raw_pack_settled hW, hf i, Nat.mul_one]
  have hd : scaleDiv W (settled W c) = 1 := by
    rw [scaleDiv, wMax_settled hW]
    have : (W + W - 1) / W = 1 := Nat.div_eq_of_lt_le (by omega) (by omega)
    omega
  have hproj : project W (settled W c) = settled W c := by
    funext i
    rw [project, hd, Nat.div_one]
    exact max_eq_right (one_le_settled hW c i)
  rw [wGen, hstep, hproj]

/-- The fixed point survives the transport: the fiber coordinate stands still while the base runs
on. -/
theorem iterate_wWorld_settled (hW : 1 ≤ W) (S : Fin n₁ → Fin n₁) (fit : Fin n₁ → Fin C → ℕ)
    (hf : ∀ x i, fit x i = 1) (t : ℕ) (x : Fin n₁) (c : Fin C) :
    (wWorld W S fit)^[t]
        (finProdFinEquiv (x, finFunctionFinEquiv (pack W (settled W c) : WVec C W)))
      = finProdFinEquiv (S^[t] x, finFunctionFinEquiv (pack W (settled W c) : WVec C W)) := by
  have hstep : ∀ y : Fin n₁, wWorld W S fit
      (finProdFinEquiv (y, finFunctionFinEquiv (pack W (settled W c) : WVec C W)))
      = finProdFinEquiv (S y, finFunctionFinEquiv (pack W (settled W c) : WVec C W)) := by
    intro y
    rw [wWorld, skewWorldFin_apply, wFiber]
    simp only [Equiv.symm_apply_apply]
    rw [wGen_settled hW _ (hf y) c]
  induction t generalizing x with
  | zero => rfl
  | succ t ih =>
      rw [Function.iterate_succ_apply, hstep, ih, ← Function.iterate_succ_apply]

/-- The reading returns the settled candidate — with a *unique* maximum, so no tie-breaking is
involved, where the winner-take-all witness needed a fold induction. -/
theorem argmaxFrame_settled [NeZero C] (hW : 2 ≤ W) (x : Fin n₁) (c : Fin C) :
    argmaxFrame n₁ W (finProdFinEquiv (x, finFunctionFinEquiv (pack W (settled W c) : WVec C W)))
      = c := by
  rw [argmaxFrame]
  simp only [Equiv.symm_apply_apply]
  rw [raw_pack_settled (by omega)]
  refine argmax_eq_of_strict fun i hi => ?_
  rw [settled, settled, ite_eq_right hi, ite_eq_left rfl]
  omega

/-- **The imported coverage hypothesis is satisfiable.** Every candidate is read off its own settled
vector, which the information-free dynamics leaves untouched, so the frame is surjective after any
number of steps. `wFiber_emergence_pricing` is therefore not vacuous.

A satisfiability witness and nothing more: it exhibits the settled state, and says nothing about
whether Bayesian update under a real base reaches one. That second question is settled elsewhere —
`FlooredMixture`'s `argmaxFrame_wWorld_eventually_const` and, from every initial weight vector,
`BasinSettling`'s `argmaxFrame_wWorld_eventually_const_wStartFrom`, both under realizability along
the observed trajectory. The two still do not meet: what those settle on depends on the initial
vector, where coverage here asks the reading to take every value as that vector ranges, and neither
implies the other. -/
theorem surjective_argmaxFrame_of_settled [NeZero C] (hW : 2 ≤ W) (S : Fin n₁ → Fin n₁)
    (fit : Fin n₁ → Fin C → ℕ) (hf : ∀ x i, fit x i = 1) (hn₁ : 0 < n₁) :
    Function.Surjective fun s =>
      argmaxFrame n₁ W ((wWorld W S fit)^[n₁ * (W + 1) ^ C] s) := by
  intro c
  refine ⟨finProdFinEquiv (⟨0, hn₁⟩, finFunctionFinEquiv (pack W (settled W c) : WVec C W)), ?_⟩
  change argmaxFrame n₁ W ((wWorld W S fit)^[n₁ * (W + 1) ^ C]
    (finProdFinEquiv (⟨0, hn₁⟩, finFunctionFinEquiv (pack W (settled W c) : WVec C W)))) = c
  rw [iterate_wWorld_settled (by omega) S fit hf, argmaxFrame_settled hW]

/-! ### The settled configuration is a fixed point of *predictive* fitness

`wGen_settled` runs on an information-free fitness — every candidate scoring `1` — which is the
weakest non-vacuity there is. That hypothesis is unnecessary. The settled vector is a fixed point of
the construction's own `predFitPos` as soon as the candidate it is settled on predicts the base at
the state being stepped, and the arithmetic is exact rather than approximate: the faithful candidate
scores `2`, so its budget doubles to `2W`, which is the new maximum, so the common divisor is
exactly `2` and the budget returns to `W`; every competitor holds one quantum, scores `1` or `2`,
and `max 1 (u / 2)` returns it to one quantum whichever it scored.

Two things this changes and one it does not. The fitness is now the real one, so what holds the
configuration still is *selection*, not an absence of information — and, unlike every settled
configuration exhibited over the pool fiber, it is not written in by a variation rule, the weighted
fiber having none. What it does not change is the *reach* question: nothing below shows that
selection arrives at this configuration from an arbitrary weight vector, and `BasinSettling` — which
does settle the reading from every one of them — does not identify the vector reached either.

Faithfulness is consumed only at the state being stepped, so that is how it is stated; the run asks
for it only along the trajectory it visits. -/

/-- **A fixed point of genuine predictive fitness.** The settled vector reproduces itself under
`predFitPos` whenever the candidate it is settled on predicts the base at `x` — a hypothesis about
one state, which is all one step consumes.

The budget needs only its one quantum here (`1 ≤ W`); reading the configuration back needs two
(`argmaxFrame_settled`), and it is there that the degeneracy bites — at `W = 1` every weight is
pinned at one quantum and the fold returns candidate `0` whatever the fitness says. -/
theorem wGen_settled_of_faithful (hW : 1 ≤ W) (S : Fin n₁ → Fin n₁)
    (dec : Fin C → Fin n₁ → Fin n₁) (x : Fin n₁) {c₀ : Fin C} (hc₀ : dec c₀ x = S x) :
    wGen W (predFitPos S dec x) (pack W (settled W c₀)) = (pack W (settled W c₀) : WVec C W) := by
  have hfc₀ : predFitPos S dec x c₀ = 2 := by rw [predFitPos, ite_eq_left hc₀]
  have hfle : ∀ i, predFitPos S dec x i ≤ 2 := by intro i; rw [predFitPos]; split <;> omega
  have hf1 : ∀ i, 1 ≤ predFitPos S dec x i := fun i => predFitPos_pos S dec x i
  have hstep : bayesStep (predFitPos S dec x) (WVec.raw (pack W (settled W c₀) : WVec C W))
      = fun i => settled W c₀ i * predFitPos S dec x i := by
    funext i
    rw [bayesStep, raw_pack_settled hW]
  have hvc₀ : settled W c₀ c₀ * predFitPos S dec x c₀ = 2 * W := by
    rw [settled, ite_eq_left rfl, hfc₀, Nat.mul_comm]
  have hvi : ∀ i, i ≠ c₀ → settled W c₀ i * predFitPos S dec x i = predFitPos S dec x i := by
    intro i hi
    rw [settled, ite_eq_right hi, Nat.one_mul]
  have hmax : wMax (fun i => settled W c₀ i * predFitPos S dec x i) = 2 * W := by
    refine le_antisymm (Finset.sup_le fun i _ => ?_) ?_
    · by_cases hi : i = c₀
      · subst hi; omega
      · have h2 := hfle i
        rw [hvi i hi]
        omega
    · have h := le_wMax (fun i => settled W c₀ i * predFitPos S dec x i) c₀
      omega
  have hd : scaleDiv W (fun i => settled W c₀ i * predFitPos S dec x i) = 2 := by
    rw [scaleDiv, hmax]
    have h : (2 * W + W - 1) / W = 2 := Nat.div_eq_of_lt_le (by omega) (by omega)
    omega
  have hproj : project W (fun i => settled W c₀ i * predFitPos S dec x i) = settled W c₀ := by
    funext i
    rw [project, hd]
    by_cases hi : i = c₀
    · subst hi
      rw [hvc₀, Nat.mul_div_cancel_left W Nat.zero_lt_two, settled, ite_eq_left rfl]
      omega
    · have h2 := hfle i
      rw [hvi i hi, settled, ite_eq_right hi]
      omega
  rw [wGen, hstep, hproj]

/-- The fixed point survives the transport: the base runs on, the fiber stands still. Faithfulness
is asked for along the trajectory the run visits and nowhere else. -/
theorem iterate_wWorld_settled_of_faithful (hW : 1 ≤ W) (S : Fin n₁ → Fin n₁)
    (dec : Fin C → Fin n₁ → Fin n₁) (x : Fin n₁) {c₀ : Fin C}
    (hc₀ : ∀ s, dec c₀ (S^[s] x) = S (S^[s] x)) (t : ℕ) :
    (wWorld W S (predFitPos S dec))^[t]
        (finProdFinEquiv (x, finFunctionFinEquiv (pack W (settled W c₀) : WVec C W)))
      = finProdFinEquiv (S^[t] x, finFunctionFinEquiv (pack W (settled W c₀) : WVec C W)) := by
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [Function.iterate_succ_apply', ih, wWorld, skewWorldFin_apply, wFiber]
      simp only [Equiv.symm_apply_apply]
      rw [wGen_settled_of_faithful hW S dec _ (hc₀ t), ← Function.iterate_succ_apply' S t x]

/-- The candidate reading over the settled configuration is constant, at the faithful candidate it
is settled on — for the whole run, at every base point. -/
theorem argmaxFrame_iterate_settled_of_faithful [NeZero C] (hW : 2 ≤ W) (S : Fin n₁ → Fin n₁)
    (dec : Fin C → Fin n₁ → Fin n₁) (x : Fin n₁) {c₀ : Fin C}
    (hc₀ : ∀ s, dec c₀ (S^[s] x) = S (S^[s] x)) (t : ℕ) :
    argmaxFrame n₁ W ((wWorld W S (predFitPos S dec))^[t]
        (finProdFinEquiv (x, finFunctionFinEquiv (pack W (settled W c₀) : WVec C W))))
      = c₀ := by
  rw [iterate_wWorld_settled_of_faithful (by omega) S dec x hc₀ t, argmaxFrame_settled hW]

/-- **The candidate frame's coverage is satisfiable under the real fitness too**, and this is the
statement that fixes the scope of the separation below.

`surjective_argmaxFrame_of_settled` met the pricing assembly's coverage hypothesis by switching the
information off. It need not be met that way: at a decoder under which *every* candidate predicts
the base, each candidate is read off its own settled vector, which `predFitPos` now holds still by
selection. The dynamics is the construction's own and the coverage is over the whole state space.

What it costs to say precisely: the *fitness function* is genuine while its *values* are still
undiscriminating, since a decoder faithful at every candidate makes them all score alike. So this
strengthens the witness one step and no further — and its real work is negative. Its hypotheses
include those of `wFrames_separate_of_settled` (a faithful `c₀`, any base rule, `2 ≤ C`), so nothing
of that shape may claim the candidate frame's coverage fails over *all* initial states: here it
holds. The separation is therefore stated over the settled family, where it is a fact. -/
theorem surjective_argmaxFrame_of_all_faithful [NeZero C] (hW : 2 ≤ W) (S : Fin n₁ → Fin n₁)
    (dec : Fin C → Fin n₁ → Fin n₁) (hdec : ∀ c, dec c = S) (hn₁ : 0 < n₁) :
    Function.Surjective fun s =>
      argmaxFrame n₁ W ((wWorld W S (predFitPos S dec))^[n₁ * (W + 1) ^ C] s) := by
  intro c
  refine ⟨finProdFinEquiv (⟨0, hn₁⟩, finFunctionFinEquiv (pack W (settled W c) : WVec C W)), ?_⟩
  exact argmaxFrame_iterate_settled_of_faithful hW S dec _ (fun s => by rw [hdec]) _

/-! ### The base-reading frame's coverage, and the two frames separated

The reading `wPredFrame` takes over the settled configuration is the *base's* next state, so it
varies with the base point even though the population is constant — which is the whole difference.
Coverage then follows from the base rule being surjective, over the full state space
(`surjective_wPredFrame_of_faithful`), and the two frames separate on one dynamics
(`wFrames_separate_of_settled`).

The separation's candidate-frame half is stated over the settled family of initial states and not
over all of them, and that is forced rather than convenient:
`surjective_argmaxFrame_of_all_faithful` exhibits the candidate frame's coverage *holding* over the
whole state space under the very same hypotheses. Over the pool fiber a variation rule could
overwrite every slot and make the settled shape reachable from every initial state; the weighted
fiber has no variation rule — the settling
here is a fitness fixed point — so what the settled family supplies is a set of initial states on
which the candidate reading covers nothing and the base reading covers everything.

Neither half touches convergence. That the fiber's reading settles under realizability — from its
own uniform start, and from every initial weight vector — is the floored development's theorem and
`BasinSettling`'s; coverage here asks instead that the reading take every value as the initial
vector ranges, which a start-dependent limit leaves open, so the two conditions are compatible and
neither implies the other. -/

/-- The base-reading frame over the settled configuration reads the base's own next state: the
population contributes only the identity of the rule applied, and it contributes the same one at
every step. -/
theorem wPredFrame_iterate_settled_of_faithful [NeZero C] (hW : 2 ≤ W) (S : Fin n₁ → Fin n₁)
    (dec : Fin C → Fin n₁ → Fin n₁) (x : Fin n₁) {c₀ : Fin C}
    (hc₀ : ∀ s, dec c₀ (S^[s] x) = S (S^[s] x)) (t : ℕ) :
    wPredFrame n₁ W dec ((wWorld W S (predFitPos S dec))^[t]
        (finProdFinEquiv (x, finFunctionFinEquiv (pack W (settled W c₀) : WVec C W))))
      = S^[t + 1] x := by
  rw [wPredFrame, iterate_wWorld_settled_of_faithful (by omega) S dec x hc₀ t,
    argmaxFrame_settled hW]
  simp only [Equiv.symm_apply_apply]
  rw [hc₀ t, Function.iterate_succ_apply']

/-- **The base-reading frame's coverage, over the weighted fiber.** If some candidate decodes to the
base rule itself and that rule is surjective, then from the settled configuration on that candidate
the fiber stands still under `predFitPos`, the frame's reading is the base rule's own next state,
and after `N` steps it is `S^[N + 1]` of the initial base coordinate — surjective as a composite of
surjections.

The coverage comes off the base coordinate, which the fiber reads and never writes. This is
`ALT.surjective_predFrame_of_faithful`'s premise shape and conclusion transported to the
weighted carrier, with one difference in what holds the population still: there a variation rule was
switched off, here the configuration is a fixed point of the fitness itself
(`wGen_settled_of_faithful`).

It says nothing about convergence, and convergence says nothing about it: this quantifies over
initial weight vectors, where the settling proved of this fiber elsewhere runs from the uniform
start. -/
theorem surjective_wPredFrame_of_faithful [NeZero C] (hW : 2 ≤ W) (S : Fin n₁ → Fin n₁)
    (dec : Fin C → Fin n₁ → Fin n₁) {c₀ : Fin C} (hdec : dec c₀ = S)
    (hS : Function.Surjective S) :
    Function.Surjective fun s =>
      wPredFrame n₁ W dec ((wWorld W S (predFitPos S dec))^[n₁ * (W + 1) ^ C] s) := by
  intro z
  obtain ⟨x, hx⟩ := hS.iterate (n₁ * (W + 1) ^ C + 1) z
  refine ⟨finProdFinEquiv (x, finFunctionFinEquiv (pack W (settled W c₀) : WVec C W)), ?_⟩
  simp only [wPredFrame_iterate_settled_of_faithful hW S dec x (fun s => by rw [hdec])]
  exact hx

/-- **The two frames separate on one dynamics.** Fix a candidate that decodes to a surjective base
rule, score by `predFitPos`, and start the fiber from the configuration settled on that candidate.
Over that family of initial states — one member per base point, one world, one fitness, one run
length — the candidate frame's reading is constant, hence covers none of `Fin C` once there are two
candidates, while the base-reading frame's covers all of `Fin n₁`.

So the choice of frame is not presentational here either: what each reading's values come from is
the population, which this configuration has frozen, or the base coordinate, which the fiber cannot
touch.

Two boundaries, both stated in the sub-section above and neither of them incidental. The family is
what the statement quantifies over, because the candidate frame's coverage over *all* initial states
can hold under these hypotheses (`surjective_argmaxFrame_of_all_faithful`) — where over the pool
fiber a variation rule made the settled shape reachable from every initial state. And the settled
configuration is a fixed point of the fitness, not an imposed one, which is what the pool fiber's
separation could not say; but it remains an initial condition, and nothing shows selection reaches
*it* from an arbitrary weight vector, `BasinSettling`'s settling identifying no vector. -/
theorem wFrames_separate_of_settled [NeZero C] (hW : 2 ≤ W) (hC : 2 ≤ C) (S : Fin n₁ → Fin n₁)
    (dec : Fin C → Fin n₁ → Fin n₁) {c₀ : Fin C} (hdec : dec c₀ = S)
    (hS : Function.Surjective S) :
    (¬ Function.Surjective fun x : Fin n₁ =>
        argmaxFrame n₁ W ((wWorld W S (predFitPos S dec))^[n₁ * (W + 1) ^ C]
          (finProdFinEquiv (x, finFunctionFinEquiv (pack W (settled W c₀) : WVec C W))))) ∧
      Function.Surjective fun x : Fin n₁ =>
        wPredFrame n₁ W dec ((wWorld W S (predFitPos S dec))^[n₁ * (W + 1) ^ C]
          (finProdFinEquiv (x, finFunctionFinEquiv (pack W (settled W c₀) : WVec C W)))) := by
  refine ⟨fun hsurj => ?_, fun z => ?_⟩
  · have : Nontrivial (Fin C) := Fin.nontrivial_iff_two_le.mpr hC
    obtain ⟨c₁, hc₁⟩ := exists_ne c₀
    obtain ⟨x, hx⟩ := hsurj c₁
    exact hc₁ (hx.symm.trans
      (argmaxFrame_iterate_settled_of_faithful hW S dec x (fun s => by rw [hdec]) _))
  · obtain ⟨x, hx⟩ := hS.iterate (n₁ * (W + 1) ^ C + 1) z
    refine ⟨x, ?_⟩
    simp only [wPredFrame_iterate_settled_of_faithful hW S dec x (fun s => by rw [hdec])]
    exact hx

end Settled

/-! ## The pricing assembly, transported -/

section Pricing

variable {n₁ C W : ℕ}

/-- **The weighted fiber's guest, priced** ([Inevitability] §6) — the same assembly as for the
winner-take-all fiber, with the fiber rule and the frame swapped and nothing else changed.

That it transports verbatim is the point: the pricing section is parametric in the fiber rule (a
skew product is cheap when its ingredients are, whatever the fiber does) and the emergence theorem
is parametric in the frame, so changing the fiber's state space from `Fin (C^P)` to
`Fin ((W+1)^C)` costs nothing in the budget. The constant is identical: the base rule's code, the
fiber rule's code, the frame's code, and one absolute constant, with nothing scaling in the state
count — which is exponential in the candidate count here.

The hypothesis is imported here exactly as before, and it is a **coverage** condition over initial
states rather than a convergence one: what `emergence` needs is that the reading take every value in
its codomain, which is what makes the guest carry a model worth pricing. For a candidate-valued
frame that coverage can only come from the initial condition, and the witnesses above supply it that
way. Under the base-reading frame it need not be imported at all —
`wPredFrame_emergence_pricing_of_faithful`. -/
theorem wFiber_emergence_pricing [NeZero C] (S : Fin n₁ → Fin n₁) (fit : Fin n₁ → Fin C → ℕ)
    (cS cF cθ : Nat.Partrec.Code)
    (hconv : Function.Surjective fun s =>
      argmaxFrame n₁ W ((wWorld W S fit)^[n₁ * (W + 1) ^ C] s))
    (hS : cS.eval 0 = Part.some (lensCode S))
    (hF : cF.eval 0 = Part.some (lensCode (fiberFlat (wFiber W fit))))
    (hθ : cθ.eval 0 = Part.some (lensCode (argmaxFrame (C := C) n₁ W))) :
    Carries (wWorld W S fit) (emergeLens (wWorld W S fit) (argmaxFrame n₁ W)) ∧
    Nat.card ↥(orbit (Perm ↥(core (wWorld W S fit)))
        (coreLens (wWorld W S fit) (emergeLens (wWorld W S fit) (argmaxFrame n₁ W) 0)))
      ≤ CbHue (wWorld W S fit)
          (elen cS + elen cF + elen cθ + (elen emergeBuilder + elen skewBuilder + 36)) := by
  have hU : (skewCode cS cF).eval 0 = Part.some (lensCode (wWorld W S fit)) :=
    eval_skewCode S (wFiber W fit) cS cF hS hF
  obtain ⟨hcar, hprice⟩ :=
    emergence (wWorld W S fit) (argmaxFrame n₁ W) (skewCode cS cF) cθ hconv hU hθ
  refine ⟨hcar, hprice.trans (CbHue_mono _ ?_)⟩
  rw [elen_skewCode]
  omega

/-- **The weighted fiber's guest, priced through the base-reading frame** ([Inevitability] §6).
`wFiber_emergence_pricing` with `θ := wPredFrame n₁ W dec`: same host, same composed code, same
constant, and the frame swapped.

The transport is the fourth of its kind, and it is the same fact each time: the skew pricing is
parametric in the fiber rule and `emergence` is parametric in the frame, so the assembly never
depended on the reading being candidate-valued. Only the imported coverage hypothesis did, and that
is exactly what the swap moves — onto the base coordinate, where
`surjective_wPredFrame_of_faithful` discharges it outright for a candidate decoding to a surjective
base rule.

The guest is `Fin n₁`-valued rather than `Fin C`-valued: it carries the fittest candidate's
prediction of the base, so what is priced is the host's own orbit as the population models it. -/
theorem wPredFrame_emergence_pricing [NeZero C] (S : Fin n₁ → Fin n₁) (fit : Fin n₁ → Fin C → ℕ)
    (dec : Fin C → Fin n₁ → Fin n₁) (cS cF cθ : Nat.Partrec.Code)
    (hcov : Function.Surjective fun s =>
      wPredFrame n₁ W dec ((wWorld W S fit)^[n₁ * (W + 1) ^ C] s))
    (hS : cS.eval 0 = Part.some (lensCode S))
    (hF : cF.eval 0 = Part.some (lensCode (fiberFlat (wFiber W fit))))
    (hθ : cθ.eval 0 = Part.some (lensCode (wPredFrame (C := C) n₁ W dec))) :
    Carries (wWorld W S fit) (emergeLens (wWorld W S fit) (wPredFrame n₁ W dec)) ∧
    Nat.card ↥(orbit (Perm ↥(core (wWorld W S fit)))
        (coreLens (wWorld W S fit) (emergeLens (wWorld W S fit) (wPredFrame n₁ W dec) 0)))
      ≤ CbHue (wWorld W S fit)
          (elen cS + elen cF + elen cθ + (elen emergeBuilder + elen skewBuilder + 36)) := by
  have hU : (skewCode cS cF).eval 0 = Part.some (lensCode (wWorld W S fit)) :=
    eval_skewCode S (wFiber W fit) cS cF hS hF
  obtain ⟨hcar, hprice⟩ :=
    emergence (wWorld W S fit) (wPredFrame n₁ W dec) (skewCode cS cF) cθ hcov hU hθ
  refine ⟨hcar, hprice.trans (CbHue_mono _ ?_)⟩
  rw [elen_skewCode]
  omega

/-- **The assembly with its coverage discharged, not imported.** The same price, over the
construction's own predictive fitness, from hypotheses about the *decoder and the base* alone: some
candidate decodes to the base rule and that rule is surjective. No condition on the reading, on the
initial state, or on what selection does is assumed.

This is what the frame swap was for. The coverage the assembly needs is a property of the frame's
codomain, and a base-reading frame draws it from the base coordinate, which the fiber cannot write;
`surjective_wPredFrame_of_faithful` supplies it and the hypothesis disappears from the statement.

What remains outside is unchanged and is not hidden here: the coverage witness runs from the settled
configuration on the faithful candidate, and that selection *arrives* at that configuration from an
arbitrary weight vector is shown nowhere — `BasinSettling` settles the reading from every initial
vector without identifying the vector it settles at. -/
theorem wPredFrame_emergence_pricing_of_faithful [NeZero C] (hW : 2 ≤ W) (S : Fin n₁ → Fin n₁)
    (dec : Fin C → Fin n₁ → Fin n₁) {c₀ : Fin C} (hdec : dec c₀ = S)
    (hsurj : Function.Surjective S) (cS cF cθ : Nat.Partrec.Code)
    (hS : cS.eval 0 = Part.some (lensCode S))
    (hF : cF.eval 0 = Part.some (lensCode (fiberFlat (wFiber W (predFitPos S dec)))))
    (hθ : cθ.eval 0 = Part.some (lensCode (wPredFrame (C := C) n₁ W dec))) :
    Carries (wWorld W S (predFitPos S dec))
        (emergeLens (wWorld W S (predFitPos S dec)) (wPredFrame n₁ W dec)) ∧
    Nat.card ↥(orbit (Perm ↥(core (wWorld W S (predFitPos S dec))))
        (coreLens (wWorld W S (predFitPos S dec))
          (emergeLens (wWorld W S (predFitPos S dec)) (wPredFrame n₁ W dec) 0)))
      ≤ CbHue (wWorld W S (predFitPos S dec))
          (elen cS + elen cF + elen cθ + (elen emergeBuilder + elen skewBuilder + 36)) :=
  wPredFrame_emergence_pricing S (predFitPos S dec) dec cS cF cθ
    (surjective_wPredFrame_of_faithful hW S dec hdec hsurj) hS hF hθ

end Pricing

/-! ## What the carrier costs: the residual is real

The identity holds exactly for `bayesStep`. It does **not** survive the projection, and the instance
below is the whole of the difference. -/

section Residual

/-- Two candidates, weights `2` and `1`. -/
def badW : Fin 2 → ℕ := ![2, 1]

/-- The first candidate predicts, the second does not. -/
def badFit : Fin 2 → ℕ := ![2, 1]

/-- The exact step doubles the leading weight; the projection then halves everything back. -/
theorem project_bayesStep_badFit_eq_badW : project 2 (bayesStep badFit badW) = badW := by decide

/-- **Bayes up to the carrier, not Bayes.** On this two-candidate, budget-`2` instance the *exact*
replicator step reproduces the posterior term for term, and the projected step returns the **prior
unchanged** — where Bayes moves the leading candidate from `2/3` to `4/5`, the finite fiber moves it
nowhere. One step of evidence is lost entirely to the rounding.

This is the honest limit of the design constraint. The fiber *is* the mixture as long as its weights
are free to grow; a finite carrier forces a projection, and the projection is not the identity. The
gap is not in the choice of selection rule — that half is exact, by `toDist_bayesStep` — but in the
carrier, and pricing it is what a quantitative residual bound would have to do. -/
theorem weighted_fiber_not_exactly_bayes :
    toDist (bayesStep badFit badW) = bayesPost (toDist badW) badFit ∧
      toDist (project 2 (bayesStep badFit badW)) = toDist badW ∧
      bayesPost (toDist badW) badFit ≠ toDist badW := by
  refine ⟨toDist_bayesStep badFit badW (by decide) (by decide),
    congrArg toDist project_bayesStep_badFit_eq_badW, ?_⟩
  intro hcon
  have h0 := congrFun hcon 0
  norm_num [bayesPost, toDist, badW, badFit, Fin.sum_univ_two] at h0

end Residual

end ALT
