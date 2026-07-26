/-
Copyright (c) 2026 Mykola Palamarchuk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mykola Palamarchuk
-/
import ALT.SkewFiber

-- Formal-check file, not Mathlib-destined: opt out of the house-style header linter.
set_option linter.style.header false

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
  argument**, where the winner-take-all frame did.
* `settled` / `wGen_settled` / `surjective_argmaxFrame_of_settled` — the imported convergence
  hypothesis is satisfiable, on the settled configuration the floor forces.
* `wFiber_emergence_pricing` — the pricing assembly, transported verbatim.
* `weighted_fiber_not_exactly_bayes` — the exact step is Bayes; the projected step, on a small
  instance, discards the evidence entirely.

## Scope

`toDist_bayesStep` is an identity about the *exact* weight dynamics; nothing here claims the finite
fiber converges, and the convergence hypothesis of the pricing assembly is imported exactly as
before. The rounding residual is exhibited but not bounded — a quantitative bound, and the tracking
form of a redundancy argument for a *floored* process, are not developed here.
-/

namespace WeightedFiber

open PersistenceCapacity Decoupling AdditiveComplexity SkewFiber
open Equiv MulAction

-- `•` on the recurrent-core reading is the relabelling action `U • ℓ = ℓ ∘ U⁻¹`; the same local
-- instance `PersistenceCapacity.emergence` is stated under.
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
def raw (w : WVec C W) : Fin C → ℕ := fun i => (w i : ℕ)

/-- Package a natural weight vector into the carrier. -/
def pack (W : ℕ) (v : Fin C → ℕ) : WVec C W :=
  fun i => ⟨min (v i) W, Nat.lt_succ_of_le (min_le_right _ _)⟩

/-- **One generation of the weighted fiber**: the exact replicator step, then the carrier
projection. All of the approximation is in the second half. -/
def wGen (W : ℕ) (f : Fin C → ℕ) (w : WVec C W) : WVec C W :=
  pack W (project W (bayesStep f (raw w)))

/-- **Packing does not clamp**: the projection already fits, so the step's arithmetic is exactly
`project ∘ bayesStep`. The budget cap is an invariant of the step, not a truncation hidden in the
carrier — which is what makes the residual in `weighted_fiber_not_exactly_bayes` attributable to the
rounding alone. -/
theorem raw_wGen (hW : 1 ≤ W) (f : Fin C → ℕ) (w : WVec C W) :
    raw (wGen W f w) = project W (bayesStep f (raw w)) := by
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

/-- **The heaviest candidate**, by a left-to-right fold that keeps the incumbent on ties. -/
def argmax [NeZero C] (w : Fin C → ℕ) : Fin C :=
  (List.finRange C).foldl (fun a i => if w a < w i then i else a) 0

private theorem foldl_argmax [NeZero C] {w : Fin C → ℕ} {c : Fin C} (h : ∀ i, i ≠ c → w i < w c) :
    ∀ (l : List (Fin C)) (a : Fin C), (a = c ∨ c ∈ l) →
      l.foldl (fun a i => if w a < w i then i else a) a = c := by
  intro l
  induction l with
  | nil =>
      intro a ha
      rcases ha with ha | ha
      · exact ha
      · simp at ha
  | cons x l ih =>
      intro a ha
      rw [List.foldl_cons]
      refine ih _ ?_
      rcases ha with ha | ha
      · refine Or.inl ?_
        by_cases hxc : x = c
        · rw [hxc, ha]
          by_cases hlt : w c < w c
          · rw [if_pos hlt]
          · rw [if_neg hlt]
        · rw [if_neg (by rw [ha]; exact not_lt.mpr (h x hxc).le)]
          exact ha
      · rcases List.mem_cons.mp ha with hxc | hl
        · refine Or.inl ?_
          by_cases hax : w a < w x
          · rw [if_pos hax]; exact hxc.symm
          · by_cases hac : a = c
            · rw [if_neg hax]; exact hac
            · have hle : w c ≤ w a := by rw [hxc]; exact not_lt.mp hax
              exact absurd (h a hac) (not_lt.mpr hle)
        · exact Or.inr hl

/-- A strictly heaviest candidate is the one the reading returns. Unlike the winner-take-all fold,
no tie-breaking convention is in play: the maximum is unique. -/
theorem argmax_eq_of_strict [NeZero C] {w : Fin C → ℕ} {c : Fin C} (h : ∀ i, i ≠ c → w i < w c) :
    argmax w = c :=
  foldl_argmax h _ _ (Or.inr (List.mem_finRange c))

/-- **The weighted reading** ([Inevitability] §6): decode the weight vector out of the fiber
coordinate and hand back its heaviest candidate — the maximum-a-posteriori hypothesis.

Note what is absent: the fitness. The winner-take-all frame had to score the population at the
current base state to read it; a weight vector already carries the posterior, so the reading is a
function of the fiber coordinate alone. -/
def argmaxFrame (n₁ W : ℕ) [NeZero C] : Fin (n₁ * (W + 1) ^ C) → Fin C :=
  fun p => argmax (raw (finFunctionFinEquiv.symm (finProdFinEquiv.symm p).2))

end Frame

/-! ## The convergence hypothesis is satisfiable

The uniform floor changes what "settled" means: a bare point mass is not reachable, because no
coordinate may be zero. The settled configuration is instead the whole budget on one candidate and
one reserved quantum on each of the others — and it is a genuine fixed point. -/

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
  rwa [settled, if_pos rfl] at this

theorem raw_pack_settled (hW : 1 ≤ W) (c : Fin C) :
    raw (pack W (settled W c) : WVec C W) = settled W c := by
  funext i
  exact min_eq_left (settled_le hW c i)

/-- **A fixed point.** With the base carrying no information — every candidate equally likely — the
settled vector reproduces itself: the common divisor is `1`, so the rescale is trivial, and every
coordinate is already at or above the reserve. -/
theorem wGen_settled (hW : 1 ≤ W) (f : Fin C → ℕ) (hf : ∀ i, f i = 1) (c : Fin C) :
    wGen W f (pack W (settled W c)) = (pack W (settled W c) : WVec C W) := by
  have hstep : bayesStep f (raw (pack W (settled W c) : WVec C W)) = settled W c := by
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
  rw [settled, settled, if_neg hi, if_pos rfl]
  omega

/-- **The imported hypothesis is satisfiable.** Every candidate is read off its own settled vector,
which the information-free dynamics leaves untouched, so the frame is surjective after any number of
steps. `wFiber_emergence_pricing` is therefore not vacuous.

A satisfiability witness and nothing more: it exhibits the settled state, and says nothing about
whether Bayesian update under a real base reaches one. -/
theorem surjective_argmaxFrame_of_settled [NeZero C] (hW : 2 ≤ W) (S : Fin n₁ → Fin n₁)
    (fit : Fin n₁ → Fin C → ℕ) (hf : ∀ x i, fit x i = 1) (hn₁ : 0 < n₁) :
    Function.Surjective fun s =>
      argmaxFrame n₁ W ((wWorld W S fit)^[n₁ * (W + 1) ^ C] s) := by
  intro c
  refine ⟨finProdFinEquiv (⟨0, hn₁⟩, finFunctionFinEquiv (pack W (settled W c) : WVec C W)), ?_⟩
  change argmaxFrame n₁ W ((wWorld W S fit)^[n₁ * (W + 1) ^ C]
    (finProdFinEquiv (⟨0, hn₁⟩, finFunctionFinEquiv (pack W (settled W c) : WVec C W)))) = c
  rw [iterate_wWorld_settled (by omega) S fit hf, argmaxFrame_settled hW]

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

The convergence hypothesis is imported exactly as before, and is exactly where the weighted fiber
would have to be shown to concentrate on the truth. -/
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
theorem badProject : project 2 (bayesStep badFit badW) = badW := by decide

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
  refine ⟨toDist_bayesStep badFit badW (by decide) (by decide), congrArg toDist badProject, ?_⟩
  intro hcon
  have h0 := congrFun hcon 0
  norm_num [bayesPost, toDist, badW, badFit, Fin.sum_univ_two] at h0

end Residual

end WeightedFiber
