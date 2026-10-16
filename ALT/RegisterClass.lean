module

public import ALT.LogMassEvent


/-!
# The register class: the capacity bound over any step of a level vector

`LogMassEvent` proves the floored mixture's capacity threshold
(`floorSurpriseFrom_card_add_le_capacity`, [Discovery] Proposition 3.5(i), row FV-37) by a
potential argument that reads the mixture's step `expStep` through three step lemmas and nothing
else. This file names what those lemmas use — a handful of properties of an arbitrary update
`step : (Fin C → Bool) → (Fin C → ℕ) → (Fin C → ℕ)` of a level vector capped at a budget `b`,
driven by a miss vector — and proves the bound once, over every step with those properties. The
mixture is one member; a reset learner whose miss rule is no likelihood ratio is another; a
saturating register is not a member, and its count is not bounded by the potential. The file is
registered as [Discovery] §3 Proposition 3.6, rows FV-39 (the class, the bound, the members) and
FV-40 (the two non-members).

## The class

A step is **at a rescale** at a level vector `e` and a miss vector `m` when some hitting candidate
sits at the cap: `∃ j, e j = b ∧ m j = false`. Throughout, the truth `iR` never misses. The
capacity argument reads five properties of the step at every level vector inside the register:

* at a rescale the truth's level does not fall (`truth_le_of_rescale`);
* off a rescale the truth's level rises by exactly one (`truth_succ_of_not_rescale`) and no level
  rises by more than one (`le_succ_of_not_rescale`);
* at a rescale no level rises (`le_of_rescale`), and every missing candidate above the floor loses
  at least one level (`miss_lt_of_rescale`);
* the step keeps the run inside the register (`keeps_register`).

The first four are `RegisterCore`; `RegisterClass` adds the fifth. The fifth is load-bearing and
not implied by the four: the four constrain the step only at level vectors inside the register, and
they let a missing candidate at the cap rise above it off a rescale — after which nothing
constrains the step at all. `liftStep` is such a member of `RegisterCore`, and from a start inside
the register its surprise count is the whole horizon (`liftStep_registerCore_unbounded`).

## Main results

* `RegisterClass.card_add_le_capacity` — **the capacity bound over the class**: under the floor
  condition `C − 1 ≤ θ·(2^b + C − 1)`, from every start inside the register, along every stream on
  which the truth never misses, the surprise count over any horizon plus `C` times the truth's
  start is at most `C·b` plus the competitors' start. The potential is the one
  `floorSurpriseFrom_card_add_le_capacity` runs on, read at the class's properties.
* `expStep_registerClass` and `resetStep_registerClass` — **two members**: the floored mixture at
  every budget, candidate count and truth, and the reset learner, which off a rescale is the
  mixture and at a rescale keeps every hitter and returns every missing candidate to the floor.
* `stepRun_expStep` and `stepSurpriseSet_expStep` — **the mixture's count is the class's**: at
  `expStep` the class's run is `expRunFrom` and its surprise set is `floorSurpriseSetFrom`, so the
  class bound at the mixture is `floorSurpriseFrom_card_add_le_capacity`.
* `saturateStep_not_registerClass` — **the no-rise property is load-bearing**: the saturating
  register (hit one up, capped; miss one down, floored) is not a member, and at two candidates and
  budget `2` its count from the start `(2, 2)` grows without bound on a stream that alternates the
  competitor's miss and hit.
* `liftStep_registerCore_unbounded` — **the register-keeping property is load-bearing**: a step
  with the four step properties and not the fifth, whose count from a start inside the register is
  the whole horizon.

The surprise set is the strict one of `floorSurpriseSetFrom`: a step counts when the missing
mass, two to the level, exceeds `θ` of the total.
-/

@[expose] public section

namespace ALT

open WVec

/-! ## The class -/

section Class

variable {C : ℕ}

/-- **The four step properties.** A step of a level vector `e : Fin C → ℕ`, capped at `b`, driven
by a miss vector `m`, with the truth `iR` never missing, is at a rescale at `e` and `m` when some
hitting candidate is at the cap. At a rescale the truth's level does not fall; off a rescale the
truth's level rises by exactly one and no level rises by more than one; at a rescale no level
rises; at a rescale every missing candidate above the floor loses at least one level. Every
property is read at level vectors inside the register only. -/
structure RegisterCore (b : ℕ) (step : (Fin C → Bool) → (Fin C → ℕ) → (Fin C → ℕ)) (iR : Fin C) :
    Prop where
  truth_le_of_rescale : ∀ m e, (∀ i, e i ≤ b) → m iR = false → (∃ j, e j = b ∧ m j = false) →
    e iR ≤ step m e iR
  truth_succ_of_not_rescale : ∀ m e, (∀ i, e i ≤ b) → m iR = false →
    ¬ (∃ j, e j = b ∧ m j = false) → step m e iR = e iR + 1
  le_succ_of_not_rescale : ∀ m e, (∀ i, e i ≤ b) → m iR = false →
    ¬ (∃ j, e j = b ∧ m j = false) → ∀ i, step m e i ≤ e i + 1
  le_of_rescale : ∀ m e, (∀ i, e i ≤ b) → m iR = false → (∃ j, e j = b ∧ m j = false) →
    ∀ i, step m e i ≤ e i
  miss_lt_of_rescale : ∀ m e, (∀ i, e i ≤ b) → m iR = false → (∃ j, e j = b ∧ m j = false) →
    ∀ i, m i = true → 0 < e i → step m e i + 1 ≤ e i

/-- **The register class.** The four step properties of `RegisterCore`, and the step keeps the
run inside the register: from a level vector inside it, with the truth hitting, every level stays
at most `b`. The capacity argument uses these five properties and nothing else. -/
structure RegisterClass (b : ℕ) (step : (Fin C → Bool) → (Fin C → ℕ) → (Fin C → ℕ)) (iR : Fin C) :
    Prop extends RegisterCore b step iR where
  keeps_register : ∀ m e, (∀ i, e i ≤ b) → m iR = false → ∀ i, step m e i ≤ b

/-- The run of a step from a start. -/
def stepRun (step : (Fin C → Bool) → (Fin C → ℕ) → (Fin C → ℕ)) (e₀ : Fin C → ℕ)
    (M : ℕ → Fin C → Bool) : ℕ → (Fin C → ℕ)
  | 0 => e₀
  | t + 1 => step (M t) (stepRun step e₀ M t)

/-- The surprise set of a run: the steps before `n` at which the missing mass, two to the level,
exceeds `θ` of the total. -/
def stepSurpriseSet (step : (Fin C → Bool) → (Fin C → ℕ) → (Fin C → ℕ)) (e₀ : Fin C → ℕ)
    (M : ℕ → Fin C → Bool) (θ : ℚ) (n : ℕ) : Finset ℕ :=
  (Finset.range n).filter fun t =>
    θ < (∑ j, if M t j = true then (2 : ℚ) ^ stepRun step e₀ M t j else 0) /
        ∑ j, (2 : ℚ) ^ stepRun step e₀ M t j

/-- **The run stays inside the register.** -/
theorem stepRun_le {b : ℕ} {step : (Fin C → Bool) → (Fin C → ℕ) → (Fin C → ℕ)} {iR : Fin C}
    (hcls : RegisterClass b step iR) {e₀ : Fin C → ℕ} (he₀ : ∀ i, e₀ i ≤ b)
    (M : ℕ → Fin C → Bool) (hR : ∀ t, M t iR = false) (t : ℕ) (i : Fin C) :
    stepRun step e₀ M t i ≤ b := by
  induction t generalizing i with
  | zero => exact he₀ i
  | succ t ih => exact hcls.keeps_register (M t) (stepRun step e₀ M t) ih (hR t) i

private theorem stepSurpriseSet_card_succ (step : (Fin C → Bool) → (Fin C → ℕ) → (Fin C → ℕ))
    (e₀ : Fin C → ℕ) (M : ℕ → Fin C → Bool) (θ : ℚ) (n : ℕ) :
    (stepSurpriseSet step e₀ M θ (n + 1)).card
      = (stepSurpriseSet step e₀ M θ n).card
        + (if θ < (∑ j, if M n j = true then (2 : ℚ) ^ stepRun step e₀ M n j else 0) /
            ∑ j, (2 : ℚ) ^ stepRun step e₀ M n j then 1 else 0) := by
  rw [stepSurpriseSet, stepSurpriseSet, Finset.range_add_one, Finset.filter_insert]
  by_cases h : θ < (∑ j, if M n j = true then (2 : ℚ) ^ stepRun step e₀ M n j else 0) /
      ∑ j, (2 : ℚ) ^ stepRun step e₀ M n j
  · rw [ite_eq_left h, Finset.card_insert_of_notMem (by simp), ite_eq_left h]
  · rw [ite_eq_right h, ite_eq_right h, Nat.add_zero]

end Class

/-! ## The potential -/

section Potential

variable {C : ℕ}

/-- The capacity potential of `floorSurpriseFrom_card_add_le_capacity`, read at the class: `C`
copies of the truth's remaining headroom to the cap, plus the competitors' levels outright. -/
private def clsPot (b : ℕ) (iR : Fin C) (e : Fin C → ℕ) : ℕ :=
  C * (b - e iR) + ∑ i ∈ Finset.univ.erase iR, e i

/-- Off a rescale the potential drops by at least one: the truth rises by exactly one below the
cap, costing `C`, against at most `C − 1` competitors rising by at most one each. -/
private theorem clsPot_add_one_le_of_not_rescale {b : ℕ}
    {step : (Fin C → Bool) → (Fin C → ℕ) → (Fin C → ℕ)} {iR : Fin C}
    (hcls : RegisterClass b step iR) {m : Fin C → Bool} {e : Fin C → ℕ} (he : ∀ i, e i ≤ b)
    (hiR : m iR = false) (hδ : ¬ ∃ j, e j = b ∧ m j = false) :
    clsPot b iR (step m e) + 1 ≤ clsPot b iR e := by
  have heiRb : e iR < b := by
    rcases lt_or_eq_of_le (he iR) with h | h
    · exact h
    · exact absurd ⟨iR, h, hiR⟩ hδ
  have heiR' : step m e iR = e iR + 1 := hcls.truth_succ_of_not_rescale m e he hiR hδ
  have hrest : ∀ j ∈ Finset.univ.erase iR, step m e j ≤ e j + 1 := fun j _ =>
    hcls.le_succ_of_not_rescale m e he hiR hδ j
  have hcard : (Finset.univ.erase iR).card = C - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ iR), Finset.card_univ, Fintype.card_fin]
  have hsum : ∑ j ∈ Finset.univ.erase iR, step m e j
      ≤ ∑ j ∈ Finset.univ.erase iR, e j + (C - 1) := by
    calc ∑ j ∈ Finset.univ.erase iR, step m e j
        ≤ ∑ j ∈ Finset.univ.erase iR, (e j + 1) := Finset.sum_le_sum hrest
      _ = ∑ j ∈ Finset.univ.erase iR, e j + (Finset.univ.erase iR).card := by
          rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one]
      _ = ∑ j ∈ Finset.univ.erase iR, e j + (C - 1) := by rw [hcard]
  have hbC : C * (b - (e iR + 1)) + C = C * (b - e iR) := by
    have hd : b - e iR = (b - (e iR + 1)) + 1 := by omega
    rw [hd]; ring
  have hCpos : 0 < C := iR.pos
  rw [clsPot, clsPot, heiR']
  clear heiR' hrest hcard he hδ heiRb
  revert hbC hsum hCpos
  generalize C * (b - (e iR + 1)) = A1
  generalize C * (b - e iR) = A2
  generalize ∑ i ∈ Finset.univ.erase iR, step m e i = S1
  generalize ∑ i ∈ Finset.univ.erase iR, e i = S2
  intro hbC hsum hCpos
  omega

/-- At a rescale the potential never rises: the truth's level does not fall and no competitor's
level rises. -/
private theorem clsPot_le_of_rescale {b : ℕ}
    {step : (Fin C → Bool) → (Fin C → ℕ) → (Fin C → ℕ)} {iR : Fin C}
    (hcls : RegisterClass b step iR) {m : Fin C → Bool} {e : Fin C → ℕ} (he : ∀ i, e i ≤ b)
    (hiR : m iR = false) (hδ : ∃ j, e j = b ∧ m j = false) :
    clsPot b iR (step m e) ≤ clsPot b iR e := by
  have h1 : e iR ≤ step m e iR := hcls.truth_le_of_rescale m e he hiR hδ
  have hrest : ∀ j ∈ Finset.univ.erase iR, step m e j ≤ e j := fun j _ =>
    hcls.le_of_rescale m e he hiR hδ j
  rw [clsPot, clsPot]
  exact Nat.add_le_add (Nat.mul_le_mul_left C (Nat.sub_le_sub_left h1 b))
    (Finset.sum_le_sum hrest)

/-- The potential never rises, combining the two cases. -/
private theorem clsPot_le {b : ℕ}
    {step : (Fin C → Bool) → (Fin C → ℕ) → (Fin C → ℕ)} {iR : Fin C}
    (hcls : RegisterClass b step iR) {m : Fin C → Bool} {e : Fin C → ℕ} (he : ∀ i, e i ≤ b)
    (hiR : m iR = false) :
    clsPot b iR (step m e) ≤ clsPot b iR e := by
  by_cases hδ : ∃ j, e j = b ∧ m j = false
  · exact clsPot_le_of_rescale hcls he hiR hδ
  · have h := clsPot_add_one_le_of_not_rescale hcls he hiR hδ
    omega

/-- **At a rescale that is a surprise, some missing candidate is above the floor.** The mass
argument of `floorSurpriseFrom_card_add_le_capacity`, which reads only the levels and the cap the
rescaling hitter sits at: the total carries at least `2^b + C − 1`, so under the floor condition
missing mass confined to the floor could not exceed `θ` of it. -/
private theorem exists_miss_pos_of_surprise {b : ℕ} {m : Fin C → Bool} {e : Fin C → ℕ}
    {iR : Fin C} (hiR : m iR = false) {θ : ℚ}
    (hfloor : (C : ℚ) - 1 ≤ θ * ((2 : ℚ) ^ b + ((C : ℚ) - 1)))
    (hs : θ < (∑ j, if m j = true then (2 : ℚ) ^ e j else 0) / ∑ j, (2 : ℚ) ^ e j)
    {j₀ : Fin C} (hj₀e : e j₀ = b) : ∃ j, m j = true ∧ 0 < e j := by
  set T : ℚ := ∑ j, (2 : ℚ) ^ e j with hT_def
  have hT : (0 : ℚ) < T :=
    Finset.sum_pos (fun j _ => by positivity) ⟨iR, Finset.mem_univ iR⟩
  have hcardj0 : ((Finset.univ.erase j₀).card : ℚ) = (C : ℚ) - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ j₀), Finset.card_univ, Fintype.card_fin,
      Nat.cast_sub j₀.pos, Nat.cast_one]
  have hTge : (2 : ℚ) ^ b + ((C : ℚ) - 1) ≤ T := by
    have hone : ∀ j ∈ Finset.univ.erase j₀, (1 : ℚ) ≤ (2 : ℚ) ^ e j := fun j _ =>
      one_le_pow₀ (by norm_num)
    calc (2 : ℚ) ^ b + ((C : ℚ) - 1)
        = (2 : ℚ) ^ e j₀ + ∑ _j ∈ Finset.univ.erase j₀, (1 : ℚ) := by
          rw [hj₀e, Finset.sum_const, nsmul_eq_mul, mul_one, hcardj0]
      _ ≤ (2 : ℚ) ^ e j₀ + ∑ j ∈ Finset.univ.erase j₀, (2 : ℚ) ^ e j := by
          gcongr with j hj
          exact hone j hj
      _ = T := by
          rw [hT_def, ← Finset.sum_erase_add _ _ (Finset.mem_univ j₀)]; ring
  have hCQ : (0 : ℚ) ≤ (C : ℚ) - 1 := by
    have : (1 : ℚ) ≤ (C : ℚ) := by exact_mod_cast iR.pos
    linarith
  have hpos2 : (0 : ℚ) < (2 : ℚ) ^ b + ((C : ℚ) - 1) := by
    have h2 : (0 : ℚ) < (2 : ℚ) ^ b := by positivity
    linarith
  have hθ0 : 0 ≤ θ := by
    by_contra hneg
    push Not at hneg
    have : θ * ((2 : ℚ) ^ b + ((C : ℚ) - 1)) < 0 := mul_neg_of_neg_of_pos hneg hpos2
    linarith [hfloor, hCQ]
  by_contra hcon
  push Not at hcon
  have hcardIR : ((Finset.univ.erase iR).card : ℚ) = (C : ℚ) - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ iR), Finset.card_univ, Fintype.card_fin,
      Nat.cast_sub iR.pos, Nat.cast_one]
  have hM0 : (∑ j, if m j = true then (2 : ℚ) ^ e j else 0) ≤ (C : ℚ) - 1 := by
    calc ∑ j, (if m j = true then (2 : ℚ) ^ e j else 0)
        ≤ ∑ j ∈ Finset.univ.erase iR, (if m j = true then (2 : ℚ) ^ e j else 0) := by
          rw [← Finset.sum_erase_add _ _ (Finset.mem_univ iR),
            ite_eq_right (by simp [hiR] : ¬ (m iR = true))]
          linarith [Finset.sum_nonneg (fun j (_ : j ∈ Finset.univ.erase iR) =>
            show (0:ℚ) ≤ if m j = true then (2:ℚ)^e j else 0 by split <;> positivity)]
      _ ≤ ∑ _j ∈ Finset.univ.erase iR, (1 : ℚ) := by
          refine Finset.sum_le_sum fun j _ => ?_
          by_cases hm : m j = true
          · rw [ite_eq_left hm, Nat.le_zero.mp (hcon j hm), pow_zero]
          · rw [ite_eq_right hm]; norm_num
      _ = (C : ℚ) - 1 := by rw [Finset.sum_const, nsmul_eq_mul, mul_one, hcardIR]
  have : (∑ j, if m j = true then (2 : ℚ) ^ e j else 0) / T ≤ θ := by
    rw [div_le_iff₀ hT]
    calc (∑ j, if m j = true then (2 : ℚ) ^ e j else 0) ≤ (C : ℚ) - 1 := hM0
      _ ≤ θ * ((2 : ℚ) ^ b + ((C : ℚ) - 1)) := hfloor
      _ ≤ θ * T := mul_le_mul_of_nonneg_left hTge hθ0
  linarith [hs]

/-- A surprise costs the potential at least one: at a rescale some missing candidate is above the
floor and loses a level while no level rises and the truth's does not fall; off a rescale the
potential falls by one regardless. -/
private theorem clsPot_add_one_le_of_surprise {b : ℕ}
    {step : (Fin C → Bool) → (Fin C → ℕ) → (Fin C → ℕ)} {iR : Fin C}
    (hcls : RegisterClass b step iR) {m : Fin C → Bool} {e : Fin C → ℕ} (he : ∀ i, e i ≤ b)
    (hiR : m iR = false) {θ : ℚ}
    (hfloor : (C : ℚ) - 1 ≤ θ * ((2 : ℚ) ^ b + ((C : ℚ) - 1)))
    (hs : θ < (∑ j, if m j = true then (2 : ℚ) ^ e j else 0) / ∑ j, (2 : ℚ) ^ e j) :
    clsPot b iR (step m e) + 1 ≤ clsPot b iR e := by
  by_cases hδ : ∃ j, e j = b ∧ m j = false
  · obtain ⟨j₀, hj₀e, hj₀m⟩ := hδ
    have hδ' : ∃ j, e j = b ∧ m j = false := ⟨j₀, hj₀e, hj₀m⟩
    obtain ⟨j₁, hj₁m, hj₁pos⟩ := exists_miss_pos_of_surprise hiR hfloor hs hj₀e
    have h1 : e iR ≤ step m e iR := hcls.truth_le_of_rescale m e he hiR hδ'
    have hj₁ne : j₁ ≠ iR := by
      rintro rfl
      rw [hiR] at hj₁m
      exact Bool.noConfusion hj₁m
    have hj₁mem : j₁ ∈ Finset.univ.erase iR := Finset.mem_erase.mpr ⟨hj₁ne, Finset.mem_univ j₁⟩
    have hj₁step : step m e j₁ < e j₁ := hcls.miss_lt_of_rescale m e he hiR hδ' j₁ hj₁m hj₁pos
    have hrest : ∀ j ∈ Finset.univ.erase iR, step m e j ≤ e j := fun j _ =>
      hcls.le_of_rescale m e he hiR hδ' j
    have hlt : ∑ j ∈ Finset.univ.erase iR, step m e j
        < ∑ j ∈ Finset.univ.erase iR, e j :=
      Finset.sum_lt_sum hrest ⟨j₁, hj₁mem, hj₁step⟩
    have hA : C * (b - step m e iR) ≤ C * (b - e iR) :=
      Nat.mul_le_mul_left C (Nat.sub_le_sub_left h1 b)
    rw [clsPot, clsPot]
    omega
  · exact clsPot_add_one_le_of_not_rescale hcls he hiR hδ

/-- The count accumulates against the start's potential: every surprise costs at least one and no
step raises it. -/
private theorem clsPot_run_le {b : ℕ}
    {step : (Fin C → Bool) → (Fin C → ℕ) → (Fin C → ℕ)} {iR : Fin C}
    (hcls : RegisterClass b step iR) {e₀ : Fin C → ℕ} (he₀ : ∀ i, e₀ i ≤ b)
    (M : ℕ → Fin C → Bool) (hR : ∀ t, M t iR = false) {θ : ℚ}
    (hfloor : (C : ℚ) - 1 ≤ θ * ((2 : ℚ) ^ b + ((C : ℚ) - 1))) (n : ℕ) :
    (stepSurpriseSet step e₀ M θ n).card + clsPot b iR (stepRun step e₀ M n)
      ≤ clsPot b iR e₀ := by
  induction n with
  | zero => simp [stepSurpriseSet, stepRun]
  | succ n ih =>
      rw [stepSurpriseSet_card_succ]
      have hen : ∀ i, stepRun step e₀ M n i ≤ b := fun i => stepRun_le hcls he₀ M hR n i
      have heq : stepRun step e₀ M (n + 1) = step (M n) (stepRun step e₀ M n) := rfl
      rw [heq]
      by_cases h : θ < (∑ j, if M n j = true then (2 : ℚ) ^ stepRun step e₀ M n j else 0) /
          ∑ j, (2 : ℚ) ^ stepRun step e₀ M n j
      · rw [ite_eq_left h]
        have hstep := clsPot_add_one_le_of_surprise hcls hen (hR n) hfloor h
        omega
      · rw [ite_eq_right h, Nat.add_zero]
        have hstep := clsPot_le hcls hen (hR n)
        omega

end Potential

/-! ## The capacity bound over the class -/

section CapacityBound

variable {C : ℕ}

/-- **The capacity bound over the class** ([Discovery] Proposition 3.6(i), row FV-39, at every
member; Proposition 3.5(i) is the statement at the mixture it generalizes): under the floor
condition, from every start inside the register, along every stream on which the truth never
misses, the surprise count over the whole run plus `C` times the truth's
start is at most `C · b` plus the competitors' start — the potential argument at the class's
properties and nothing else. -/
theorem RegisterClass.card_add_le_capacity {b : ℕ}
    {step : (Fin C → Bool) → (Fin C → ℕ) → (Fin C → ℕ)} {iR : Fin C}
    (hcls : RegisterClass b step iR) {e₀ : Fin C → ℕ} (he₀ : ∀ i, e₀ i ≤ b)
    (M : ℕ → Fin C → Bool) (hR : ∀ t, M t iR = false) (θ : ℚ)
    (hfloor : (C : ℚ) - 1 ≤ θ * ((2 : ℚ) ^ b + ((C : ℚ) - 1))) (n : ℕ) :
    (stepSurpriseSet step e₀ M θ n).card + C * e₀ iR
      ≤ C * b + ∑ i ∈ Finset.univ.erase iR, e₀ i := by
  have h := clsPot_run_le hcls he₀ M hR hfloor n
  have hiRb := he₀ iR
  have hCeq : C * (b - e₀ iR) + C * e₀ iR = C * b := by
    rw [← Nat.mul_add]
    congr 1
    omega
  rw [clsPot, clsPot] at h
  omega

end CapacityBound

/-! ## The members -/

section Members

variable {C : ℕ}

/-- **The floored mixture is a member**: `expStep` at every budget, every candidate count and
every truth. -/
theorem expStep_registerClass (b : ℕ) (iR : Fin C) : RegisterClass b (expStep b) iR where
  truth_le_of_rescale m e _ hiR hδ := by
    simp only [expStep, ite_eq_left hδ, ite_eq_right (by simp [hiR] : ¬ (m iR = true))]
    omega
  truth_succ_of_not_rescale m e _ hiR hδ := by
    simp only [expStep, ite_eq_right hδ, ite_eq_right (by simp [hiR] : ¬ (m iR = true)),
      Nat.sub_zero]
  le_succ_of_not_rescale m e _ _ hδ i := by
    simp only [expStep, ite_eq_right hδ, Nat.sub_zero]
    split <;> omega
  le_of_rescale m e _ _ hδ i := by
    simp only [expStep, ite_eq_left hδ]
    split <;> omega
  miss_lt_of_rescale m e _ _ hδ i hmi _ := by
    simp only [expStep, ite_eq_left hδ, ite_eq_left hmi]
    omega
  keeps_register m e he _ i := by
    simp only [expStep]
    by_cases hδ : ∃ j, e j = b ∧ m j = false
    · rw [ite_eq_left hδ]
      have := he i
      split <;> omega
    · rw [ite_eq_right hδ]
      by_cases hm : m i = true
      · rw [ite_eq_left hm]
        have := he i
        omega
      · rw [ite_eq_right hm]
        have hne : e i ≠ b := fun hb => hδ ⟨i, hb, by simpa using hm⟩
        have := he i
        omega

/-- **The reset learner**: off a rescale as the mixture; at a rescale every hitter keeps its level
and every missing candidate returns to the floor. Its miss rule is no likelihood ratio. -/
def resetStep (b : ℕ) (m : Fin C → Bool) (e : Fin C → ℕ) : Fin C → ℕ :=
  if ∃ j, e j = b ∧ m j = false then fun i => if m i then 0 else e i
  else fun i => e i + (if m i then 0 else 1)

/-- **The reset learner is a member.** -/
theorem resetStep_registerClass (b : ℕ) (iR : Fin C) : RegisterClass b (resetStep b) iR where
  truth_le_of_rescale m e _ hiR hδ := by
    simp [resetStep, hδ, hiR]
  truth_succ_of_not_rescale m e _ hiR hδ := by
    simp [resetStep, hδ, hiR]
  le_succ_of_not_rescale m e _ _ hδ i := by
    simp only [resetStep, ite_eq_right hδ]
    split <;> omega
  le_of_rescale m e _ _ hδ i := by
    simp only [resetStep, ite_eq_left hδ]
    split <;> omega
  miss_lt_of_rescale m e _ _ hδ i hmi hpos := by
    simp only [resetStep, ite_eq_left hδ, ite_eq_left hmi]
    omega
  keeps_register m e he _ i := by
    by_cases hδ : ∃ j, e j = b ∧ m j = false
    · simp only [resetStep, ite_eq_left hδ]
      have := he i
      split <;> omega
    · simp only [resetStep, ite_eq_right hδ]
      by_cases hm : m i = true
      · rw [ite_eq_left hm]
        have := he i
        omega
      · rw [ite_eq_right hm]
        have hne : e i ≠ b := fun hb => hδ ⟨i, hb, by simpa using hm⟩
        have := he i
        omega

/-- At `expStep` the class's run is the landed `expRunFrom`. -/
theorem stepRun_expStep (b : ℕ) (e₀ : Fin C → ℕ) (M : ℕ → Fin C → Bool) (t : ℕ) :
    stepRun (expStep b) e₀ M t = expRunFrom e₀ M b t := by
  induction t with
  | zero => rfl
  | succ t ih => rw [stepRun, ih]; rfl

/-- The seeded wrong mass is the missing fraction of the exponent automaton's mass, read off the
normal form `raw_wRunFrom_eq_pow_expRunFrom`. -/
private theorem wrongMassFrom_eq_ratio {e₀ : Fin C → ℕ} {b : ℕ} (he₀ : ∀ i, e₀ i ≤ b)
    (M : ℕ → Fin C → Bool) (t : ℕ) :
    wrongMassFrom e₀ M b t
      = (∑ j, if M t j = true then (2 : ℚ) ^ expRunFrom e₀ M b t j else 0) /
          ∑ j, (2 : ℚ) ^ expRunFrom e₀ M b t j := by
  have hsum : ∑ j, ((raw (wRunFrom (2 ^ b) (missFit M) (pack (2 ^ b) fun k => 2 ^ e₀ k) t) j
      : ℕ) : ℚ) = ∑ j, (2 : ℚ) ^ expRunFrom e₀ M b t j := by
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [raw_wRunFrom_eq_pow_expRunFrom he₀]
    push_cast
    ring
  rw [wrongMassFrom, div_eq_mul_inv, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hm : M t i = true
  · rw [ite_eq_left hm, ite_eq_left hm, ← div_eq_mul_inv]
    change ((raw (wRunFrom (2 ^ b) (missFit M) (pack (2 ^ b) fun k => 2 ^ e₀ k) t) i : ℕ) : ℚ)
        / ∑ j, ((raw (wRunFrom (2 ^ b) (missFit M) (pack (2 ^ b) fun k => 2 ^ e₀ k) t) j : ℕ) : ℚ)
      = _
    rw [hsum, raw_wRunFrom_eq_pow_expRunFrom he₀]
    push_cast
    ring
  · rw [ite_eq_right hm, ite_eq_right hm, zero_mul]

/-- **At `expStep` the class's surprise set is the landed `floorSurpriseSetFrom`**, from every
start inside the register, so `RegisterClass.card_add_le_capacity` at the mixture is
`floorSurpriseFrom_card_add_le_capacity`. The start's bound is what the mass identity
`raw_wRunFrom_eq_pow_expRunFrom` needs. -/
theorem stepSurpriseSet_expStep {e₀ : Fin C → ℕ} {b : ℕ} (he₀ : ∀ i, e₀ i ≤ b)
    (M : ℕ → Fin C → Bool) (θ : ℚ) (n : ℕ) :
    stepSurpriseSet (expStep b) e₀ M θ n = floorSurpriseSetFrom e₀ M b θ n := by
  rw [stepSurpriseSet, floorSurpriseSetFrom]
  refine Finset.filter_congr fun t _ => ?_
  rw [wrongMassFrom_eq_ratio he₀, stepRun_expStep]

/-- **Non-vacuity** — for `RegisterClass.card_add_le_capacity`: the mixture at two candidates,
budget `2`, threshold `1/4`, the deficit start `(0, 2)` with the truth first and the stream on
which candidate `1` always misses. The class, the start, the truth and the floor condition all
hold, and the bound at horizon `2` reads `card + 0 ≤ 4 + 2`. -/
theorem RegisterClass.card_add_le_capacity_nonvacuous :
    RegisterClass 2 (expStep 2) (0 : Fin 2) ∧ (∀ i, deficitSeed 2 2 i ≤ 2) ∧
      (∀ t, deficitMiss t (0 : Fin 2) = false) ∧
      ((2 : ℚ) - 1 ≤ (1 / 4 : ℚ) * ((2 : ℚ) ^ 2 + ((2 : ℚ) - 1))) ∧
      (stepSurpriseSet (expStep 2) (deficitSeed 2 2) deficitMiss (1 / 4) 2).card
          + 2 * deficitSeed 2 2 0
        ≤ 2 * 2 + ∑ i ∈ Finset.univ.erase (0 : Fin 2), deficitSeed 2 2 i := by
  have hseed : ∀ i, deficitSeed 2 2 i ≤ 2 := by
    intro i
    fin_cases i <;> simp [deficitSeed]
  refine ⟨expStep_registerClass 2 0, hseed, deficitMiss_realizable, by norm_num, ?_⟩
  exact RegisterClass.card_add_le_capacity (expStep_registerClass 2 0) hseed deficitMiss
    deficitMiss_realizable (1 / 4) (by norm_num) 2

end Members

/-! ## The guards -/

section Guards

variable {C : ℕ}

/-! ### The no-rise property is load-bearing

A register that saturates — a hitter one up, capped at `b`; a misser one down, floored at `0` —
lets a competitor climb back at a rescale, since a hitter at the cap stays put and nothing else
moves at that step. It fails the class's no-rise property, and its count is not bounded by the
potential: at the cap, a competitor alternating miss and hit is a surprise every other step, and
nothing ever lowers it. -/

/-- **The saturating register**: hit one up, capped at `b`, miss one down, floored at `0`; a hitter
at the cap stays, and nothing else moves at that step. -/
def saturateStep (b : ℕ) (m : Fin C → Bool) (e : Fin C → ℕ) : Fin C → ℕ :=
  fun i => if m i then e i - 1 else min b (e i + 1)

/-- The alternating stream: candidate `1` misses at even steps and hits at odd ones. -/
private def alternateMiss : ℕ → Fin 2 → Bool := fun t i => decide (i = 1 ∧ t % 2 = 0)

/-- The saturating register's run from `(2, 2)` on the alternating stream has period two. -/
private theorem saturateStep_run_period (n : ℕ) :
    stepRun (saturateStep 2) ![2, 2] alternateMiss (2 * n) = ![2, 2] ∧
      stepRun (saturateStep 2) ![2, 2] alternateMiss (2 * n + 1) = ![2, 1] := by
  induction n with
  | zero =>
      refine ⟨rfl, ?_⟩
      change saturateStep 2 (alternateMiss 0) ![2, 2] = ![2, 1]
      funext i
      fin_cases i <;> simp [saturateStep, alternateMiss]
  | succ n ih =>
      have h2 : (2 * n + 1) % 2 = 1 := by omega
      have h1 : stepRun (saturateStep 2) ![2, 2] alternateMiss (2 * (n + 1)) = ![2, 2] := by
        change saturateStep 2 (alternateMiss (2 * n + 1))
          (stepRun (saturateStep 2) ![2, 2] alternateMiss (2 * n + 1)) = ![2, 2]
        rw [ih.2]
        funext i
        fin_cases i <;> simp [saturateStep, alternateMiss, h2]
      refine ⟨h1, ?_⟩
      change saturateStep 2 (alternateMiss (2 * (n + 1)))
        (stepRun (saturateStep 2) ![2, 2] alternateMiss (2 * (n + 1))) = ![2, 1]
      rw [h1]
      funext i
      fin_cases i <;> simp [saturateStep, alternateMiss]

/-- **Guard: the no-rise property is load-bearing** (row FV-40). At two candidates and budget `2`,
from the start `(2, 2)` on the stream where candidate `1` misses at even steps and hits at odd
ones, the saturating register is at a rescale at every step, its competitor rises at every odd
step, and every even step is a surprise at threshold `1/4`: the count at horizon `2n` is `n`,
which exceeds the potential `2 · (2 − 2) + 2 = 2` from `n = 3` on. -/
theorem saturateStep_not_registerClass :
    ¬ RegisterClass 2 (saturateStep 2) (0 : Fin 2) ∧
      ∀ n, (stepSurpriseSet (saturateStep 2) ![2, 2] (fun t i => decide (i = 1 ∧ t % 2 = 0))
        (1 / 4) (2 * n)).card = n := by
  refine ⟨fun h => ?_, fun n => ?_⟩
  · have := h.le_of_rescale ![false, false] ![2, 1] (by decide) rfl ⟨0, rfl, rfl⟩ 1
    simp [saturateStep] at this
  · change (stepSurpriseSet (saturateStep 2) ![2, 2] alternateMiss (1 / 4) (2 * n)).card = n
    induction n with
    | zero => rfl
    | succ n ih =>
        rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring, stepSurpriseSet_card_succ,
          stepSurpriseSet_card_succ, ih, (saturateStep_run_period n).1,
          (saturateStep_run_period n).2]
        have h2 : (2 * n + 1) % 2 = 1 := by omega
        simp [alternateMiss, h2, Fin.sum_univ_two]
        norm_num

/-! ### The register-keeping property is load-bearing

The four properties of `RegisterCore` are read at level vectors inside the register only, and they
do not keep the run there: off a rescale a missing candidate at the cap may rise by one, which
none of the four forbids, and at the level vector that results none of them says anything. The
lifting step below is the mixture inside the register except for exactly that rise, and the
identity outside; from the start `(1, 2)` on the stream where candidate `1` always misses, the
competitor is lifted to `3` at the first step and the run is frozen there with two thirds of the
mass on the competitor, so every step is a surprise. -/

/-- **The lifting step**: inside the register the floored mixture, except that off a rescale a
missing candidate at the cap rises by one; outside the register nothing moves. -/
def liftStep (b : ℕ) (m : Fin C → Bool) (e : Fin C → ℕ) : Fin C → ℕ :=
  if ∀ i, e i ≤ b then
    fun i => if m i = true ∧ e i = b ∧ ¬ (∃ j, e j = b ∧ m j = false) then e i + 1
      else expStep b m e i
  else e

/-- The lifting step has the four step properties: at a rescale it is the mixture, and off a
rescale it is the mixture except for one candidate's rise by exactly one. -/
private theorem liftStep_registerCore (b : ℕ) (iR : Fin C) : RegisterCore b (liftStep b) iR where
  truth_le_of_rescale m e he hiR hδ := by
    have h := (expStep_registerClass b iR).truth_le_of_rescale m e he hiR hδ
    simp only [liftStep, ite_eq_left he, ite_eq_right (show ¬ (m iR = true ∧ e iR = b ∧
      ¬ (∃ j, e j = b ∧ m j = false)) from fun h' => h'.2.2 hδ)]
    exact h
  truth_succ_of_not_rescale m e he hiR hδ := by
    have h := (expStep_registerClass b iR).truth_succ_of_not_rescale m e he hiR hδ
    simp only [liftStep, ite_eq_left he, ite_eq_right (show ¬ (m iR = true ∧ e iR = b ∧
      ¬ (∃ j, e j = b ∧ m j = false)) from fun h' => absurd h'.1 (by simp [hiR]))]
    exact h
  le_succ_of_not_rescale m e he hiR hδ i := by
    have h := (expStep_registerClass b iR).le_succ_of_not_rescale m e he hiR hδ i
    simp only [liftStep, ite_eq_left he]
    split
    · exact le_refl _
    · exact h
  le_of_rescale m e he hiR hδ i := by
    have h := (expStep_registerClass b iR).le_of_rescale m e he hiR hδ i
    simp only [liftStep, ite_eq_left he, ite_eq_right (show ¬ (m i = true ∧ e i = b ∧
      ¬ (∃ j, e j = b ∧ m j = false)) from fun h' => h'.2.2 hδ)]
    exact h
  miss_lt_of_rescale m e he hiR hδ i hmi hpos := by
    have h := (expStep_registerClass b iR).miss_lt_of_rescale m e he hiR hδ i hmi hpos
    simp only [liftStep, ite_eq_left he, ite_eq_right (show ¬ (m i = true ∧ e i = b ∧
      ¬ (∃ j, e j = b ∧ m j = false)) from fun h' => h'.2.2 hδ)]
    exact h

/-- The lifting step's run from `(1, 2)` on the always-missing competitor: lifted to `(2, 3)` at
the first step and frozen there. -/
private theorem liftStep_run (t : ℕ) :
    stepRun (liftStep 2) ![1, 2] deficitMiss (t + 1) = ![2, 3] := by
  induction t with
  | zero =>
      change liftStep 2 (deficitMiss 0) ![1, 2] = ![2, 3]
      funext i
      fin_cases i <;> simp [liftStep, deficitMiss, expStep]
  | succ t ih =>
      change liftStep 2 (deficitMiss (t + 1)) (stepRun (liftStep 2) ![1, 2] deficitMiss (t + 1))
        = ![2, 3]
      rw [ih]
      simp [liftStep]

/-- **Guard: the register-keeping property is load-bearing** (row FV-40). At two candidates
and budget `2`, the lifting step has the four step properties and is not a member, and from the
start `(1, 2)` inside the register, on the stream where candidate `1` always misses, every step is
a surprise at threshold `1/4`: the count at horizon `n` is `n`, where the potential is
`2 · (2 − 1) + 2 = 4`. -/
theorem liftStep_registerCore_unbounded :
    RegisterCore 2 (liftStep 2) (0 : Fin 2) ∧ ¬ RegisterClass 2 (liftStep 2) (0 : Fin 2) ∧
      ∀ n, (stepSurpriseSet (liftStep 2) ![1, 2] deficitMiss (1 / 4) n).card = n := by
  refine ⟨liftStep_registerCore 2 0, fun h => ?_, fun n => ?_⟩
  · have := h.keeps_register ![false, true] ![1, 2] (by decide) rfl 1
    simp [liftStep] at this
  · induction n with
    | zero => rfl
    | succ n ih =>
        rw [stepSurpriseSet_card_succ, ih]
        rcases n with _ | n
        · simp [stepRun, deficitMiss, Fin.sum_univ_two]
          norm_num
        · rw [liftStep_run]
          simp [deficitMiss, Fin.sum_univ_two]
          norm_num

end Guards

end ALT

set_option linter.style.longLine false in
/-- info: 'ALT.RegisterClass.card_add_le_capacity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.RegisterClass.card_add_le_capacity

set_option linter.style.longLine false in
/-- info: 'ALT.RegisterClass.card_add_le_capacity_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.RegisterClass.card_add_le_capacity_nonvacuous

/-- info: 'ALT.expStep_registerClass' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.expStep_registerClass

set_option linter.style.longLine false in
/-- info: 'ALT.resetStep_registerClass' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.resetStep_registerClass

set_option linter.style.longLine false in
/-- info: 'ALT.stepSurpriseSet_expStep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.stepSurpriseSet_expStep

set_option linter.style.longLine false in
/-- info: 'ALT.saturateStep_not_registerClass' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.saturateStep_not_registerClass

set_option linter.style.longLine false in
/-- info: 'ALT.liftStep_registerCore_unbounded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.liftStep_registerCore_unbounded
