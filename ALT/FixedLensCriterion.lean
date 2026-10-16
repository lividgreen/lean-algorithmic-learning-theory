module

public import Mathlib.Data.ZMod.QuotientGroup
public import Mathlib.Dynamics.PeriodicPts.Lemmas
public import Mathlib.GroupTheory.Coset.Card
public import Mathlib.GroupTheory.Perm.Cycle.Basic
public import ALT.PersistenceCapacity

/-!
# The fixed-lens factor criterion ([Guests] §2 Proposition 2.5)

`Intertwines.fixed_bijective` already shows that a time-independent reading of a reversible host
forces the guest law bijective. This file sharpens that dichotomy to a criterion for WHICH
bijective laws a fixed lens can realize, entirely in terms of cycle structure.

A fixed reading `ℓ` intertwining a permutation `U` with `F` sends the `U`-orbit of `x` onto the
`F`-orbit of `ℓ x`, and the source orbit's length is a multiple of the image orbit's
(`Intertwines.minimalPeriod_dvd`, `Intertwines.orbit_image_eq`). Conversely, any assignment of
`U`-orbits to `F`-orbits respecting that divisibility is realized by transporting a chosen base
point along each cycle (`Intertwines.exists_fixedLens_of_orbitAssignment`) — this is the
construction [Inevitability] §5 Remark 5.6 applies to build a fixed, non-injective reading of a
decision-shaped guest over a multi-cycle host.

The single-cycle case is the load-bearing corollary: over a host that is one cycle on all of `X`,
a fixed lens forces `F` transitive on `M` (`Intertwines.transitive_of_singleCycle`), so a
nontrivial `F`-invariant partition of `M` rules out a fixed lens entirely
(`Intertwines.not_fixedLens_of_invariantPartition`) — the bar Remark 5.6 draws against reading a
non-degenerate decoupled subsystem through a lens that never moves. Read at the guest's own time
scale `τ`, the permutation that matters is `U^τ`; `zmod_translate_minimalPeriod` and
`zmod_translate_orbitCount` record the arithmetic instance Remark 5.6 uses to cross that bar: on
`ZMod (2^k)` under `+1`, the time scale `τ = 2^j` produces exactly `2^j` cycles of length
`2^(k-j)` each, one per code block.
-/


@[expose] public section

namespace ALT

open Function

variable {X M : Type*}

/-! ## The forward half: a fixed reading forces orbit-onto-orbit divisibility

Along any `U`-orbit the reading advances lockstep with the law
(`h.iterate` specialized to a constant family), so the `ℓ`-image of the orbit of `x` is exactly
the `F`-orbit of `ℓ x`; the source orbit's length — `Function.minimalPeriod U x`, standard for a
finite permutation (`MulAction.minimalPeriod_eq_card`) — is then a multiple of the image orbit's. -/

/-- **The image orbit** ([Guests] §2 Definition 2.2, Proposition 2.5): a fixed
reading carries the `U`-orbit of `x` onto exactly the `F`-orbit of `ℓ x`. -/
theorem Intertwines.orbit_image_eq {U : X → X} {F : M → M} {ℓ : X → M}
    (h : Intertwines U F (fun _ => ℓ)) (x : X) :
    ℓ '' Set.range (fun j : ℕ => U^[j] x) = Set.range (fun j : ℕ => F^[j] (ℓ x)) := by
  have hsemiconj : Function.Semiconj ℓ U F := h 0
  have hiter : ∀ j, ℓ (U^[j] x) = F^[j] (ℓ x) := fun j => hsemiconj.iterate_right j x
  ext y
  simp only [Set.mem_image, Set.mem_range]
  constructor
  · rintro ⟨z, ⟨j, rfl⟩, rfl⟩
    exact ⟨j, (hiter j).symm⟩
  · rintro ⟨j, rfl⟩
    exact ⟨U^[j] x, ⟨j, rfl⟩, hiter j⟩

/-- info: 'ALT.Intertwines.orbit_image_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Intertwines.orbit_image_eq

/-- **The divisibility criterion** ([Guests] §2 Definition 2.2, Proposition 2.5): the
image orbit's length divides the source orbit's — the necessary half of the fixed-lens factor
criterion. -/
theorem Intertwines.minimalPeriod_dvd {U : X → X} {F : M → M} {ℓ : X → M}
    (h : Intertwines U F (fun _ => ℓ)) (x : X) :
    Function.minimalPeriod F (ℓ x) ∣ Function.minimalPeriod U x :=
  ((Function.isPeriodicPt_minimalPeriod U x).map (show Function.Semiconj ℓ U F from h 0))
    |>.minimalPeriod_dvd

set_option linter.style.longLine false in
/-- info: 'ALT.Intertwines.minimalPeriod_dvd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Intertwines.minimalPeriod_dvd

/-- **Surjectivity exhausts `M`** ([Guests] §2 Definition 2.2): a reading's own image orbits,
ranging over every starting point, cover the whole alphabet. -/
theorem Intertwines.iUnion_orbit_image_eq_univ {F : M → M} {ℓ : X → M}
    (hℓ : Function.Surjective ℓ) :
    ⋃ x : X, Set.range (fun j : ℕ => F^[j] (ℓ x)) = Set.univ := by
  refine Set.eq_univ_of_forall fun m => ?_
  obtain ⟨x, rfl⟩ := hℓ m
  exact Set.mem_iUnion.mpr ⟨x, 0, rfl⟩

/-- info: 'ALT.Intertwines.iUnion_orbit_image_eq_univ' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Intertwines.iUnion_orbit_image_eq_univ

/-! ## The converse: transport along the cycles realizes any period-compatible assignment

Given a target `g x` for every `x`, constant along `U`-orbits and dividing-compatible with them,
transporting `g`'s value at a chosen orbit representative forward under `F`, step for step with
`U`, builds a fixed reading realizing exactly that assignment. The representative and the transport
offset are chosen via `Equiv.Perm.SameCycle.setoid` and `Nat.find`; both are internal to the
construction. -/

private noncomputable def orbitRep (U : Equiv.Perm X) (x : X) : X :=
  Quotient.out (s := Equiv.Perm.SameCycle.setoid U) ⟦x⟧

private theorem orbitRep_sameCycle (U : Equiv.Perm X) (x : X) :
    U.SameCycle (orbitRep U x) x := by
  have h : (⟦orbitRep U x⟧ : Quotient (Equiv.Perm.SameCycle.setoid U)) = ⟦x⟧ :=
    Quotient.out_eq (s := Equiv.Perm.SameCycle.setoid U) ⟦x⟧
  exact Quotient.exact h

private theorem orbitRep_const (U : Equiv.Perm X) {x y : X} (h : U.SameCycle x y) :
    orbitRep U x = orbitRep U y := by
  unfold orbitRep; congr 1; exact Quotient.sound h

private theorem orbitRep_idem (U : Equiv.Perm X) (x : X) :
    orbitRep U (orbitRep U x) = orbitRep U x :=
  orbitRep_const U (orbitRep_sameCycle U x)

private theorem orbitRep_exists [Finite X] (U : Equiv.Perm X) (x : X) :
    ∃ i : ℕ, U^[i] (orbitRep U x) = x := by
  obtain ⟨i, hi⟩ := (orbitRep_sameCycle U x).exists_nat_pow_eq
  exact ⟨i, (Equiv.Perm.coe_pow U i) ▸ hi⟩

private theorem orbitRep_apply (U : Equiv.Perm X) (x : X) :
    orbitRep U (U x) = orbitRep U x := by
  refine orbitRep_const U ?_
  have h1 : U.SameCycle x (U x) := ⟨1, by simp⟩
  exact h1.symm

private theorem orbitRep_iterate (U : Equiv.Perm X) (j : ℕ) (x : X) :
    orbitRep U (U^[j] x) = orbitRep U x := by
  induction j with
  | zero => simp
  | succ n ih => rw [Function.iterate_succ_apply', orbitRep_apply]; exact ih

open Classical in
private noncomputable def orbitPos [Finite X] (U : Equiv.Perm X) (x : X) : ℕ :=
  Nat.find (orbitRep_exists U x)

open Classical in
private theorem orbitPos_spec [Finite X] (U : Equiv.Perm X) (x : X) :
    U^[orbitPos U x] (orbitRep U x) = x :=
  Nat.find_spec (orbitRep_exists U x)

open Classical in
private theorem orbitPos_le [Finite X] (U : Equiv.Perm X) (x : X) {i : ℕ}
    (hi : U^[i] (orbitRep U x) = x) : orbitPos U x ≤ i :=
  Nat.find_le hi

private theorem equivPerm_minimalPeriod_pos [Finite X] (U : Equiv.Perm X) (x : X) :
    0 < Function.minimalPeriod U x :=
  Function.minimalPeriod_pos_of_mem_periodicPts (U.injective.mem_periodicPts x)

private theorem orbitPos_lt [Finite X] (U : Equiv.Perm X) (x : X) :
    orbitPos U x < Function.minimalPeriod U (orbitRep U x) := by
  set d := Function.minimalPeriod U (orbitRep U x) with hd_def
  have hd : 0 < d := equivPerm_minimalPeriod_pos U (orbitRep U x)
  have hwit : U^[orbitPos U x % d] (orbitRep U x) = x := by
    rw [Function.iterate_mod_minimalPeriod_eq]; exact orbitPos_spec U x
  have h1 : orbitPos U x ≤ orbitPos U x % d := orbitPos_le U x hwit
  have h2 : orbitPos U x % d ≤ orbitPos U x := Nat.mod_le _ _
  rw [le_antisymm h1 h2]; exact Nat.mod_lt _ hd

private theorem mod_eq_of_iterate_eq {α} {f : α → α} {x : α} {a b : ℕ}
    (hd : 0 < Function.minimalPeriod f x) (h : f^[a] x = f^[b] x) :
    a % Function.minimalPeriod f x = b % Function.minimalPeriod f x := by
  have ha : f^[a % Function.minimalPeriod f x] x = f^[a] x := Function.iterate_mod_minimalPeriod_eq
  have hb : f^[b % Function.minimalPeriod f x] x = f^[b] x := Function.iterate_mod_minimalPeriod_eq
  have heq : f^[a % Function.minimalPeriod f x] x = f^[b % Function.minimalPeriod f x] x := by
    rw [ha, hb, h]
  exact (Function.iterate_eq_iterate_iff_of_lt_minimalPeriod (Nat.mod_lt _ hd)
    (Nat.mod_lt _ hd)).mp heq

private theorem orbitPos_succ_mod [Finite X] (U : Equiv.Perm X) (x : X) :
    orbitPos U (U x) = (orbitPos U x + 1) % Function.minimalPeriod U (orbitRep U x) := by
  set d := Function.minimalPeriod U (orbitRep U x) with hd_def
  have hd : 0 < d := equivPerm_minimalPeriod_pos U (orbitRep U x)
  have h1 : U^[orbitPos U (U x)] (orbitRep U x) = U x := by
    rw [← orbitRep_apply U x]; exact orbitPos_spec U (U x)
  have h2 : U^[orbitPos U x + 1] (orbitRep U x) = U x := by
    rw [Function.iterate_succ_apply']; congr 1; exact orbitPos_spec U x
  have hmod := mod_eq_of_iterate_eq (f := U) (x := orbitRep U x) hd (h1.trans h2.symm)
  have hlt : orbitPos U (U x) < d := by
    have h := orbitPos_lt U (U x); rw [orbitRep_apply U x] at h; rw [hd_def]; exact h
  rwa [Nat.mod_eq_of_lt hlt] at hmod

private theorem g_iterate_eq (U : Equiv.Perm X) {g : X → M} (hg : ∀ x, g (U x) = g x)
    (j : ℕ) (x : X) : g (U^[j] x) = g x := by
  induction j with
  | zero => simp
  | succ n ih => rw [Function.iterate_succ_apply', hg]; exact ih

private theorem g_orbitRep_eq [Finite X] (U : Equiv.Perm X) {g : X → M}
    (hg : ∀ x, g (U x) = g x) (x : X) : g x = g (orbitRep U x) := by
  conv_lhs => rw [← orbitPos_spec U x]
  exact g_iterate_eq U hg (orbitPos U x) (orbitRep U x)

/-- **Transport along the cycle**: the fixed reading built from a period-compatible orbit-target
assignment `g`, by carrying `g`'s value at each orbit's representative forward under `F` in
lockstep with the offset from that representative under `U`. -/
private noncomputable def transportLens [Finite X] (U : Equiv.Perm X) (g : X → M) (F : M → M) :
    X → M :=
  fun x => F^[orbitPos U x] (g (orbitRep U x))

private theorem transportLens_semiconj [Finite X] (U : Equiv.Perm X) {F : M → M} {g : X → M}
    (hdvd : ∀ x, Function.minimalPeriod F (g x) ∣ Function.minimalPeriod U x) :
    ∀ x, transportLens U g F (U x) = F (transportLens U g F x) := by
  intro x
  unfold transportLens
  rw [orbitRep_apply]
  set d := Function.minimalPeriod U (orbitRep U x) with hd_def
  have hper : Function.IsPeriodicPt F d (g (orbitRep U x)) :=
    Function.isPeriodicPt_iff_minimalPeriod_dvd.mpr (hdvd (orbitRep U x))
  rw [orbitPos_succ_mod, ← hd_def, hper.iterate_mod_apply (orbitPos U x + 1),
    Function.iterate_succ_apply']

private theorem transportLens_surjective [Finite X] (U : Equiv.Perm X) {F : M → M} {g : X → M}
    (hg : ∀ x, g (U x) = g x)
    (hdvd : ∀ x, Function.minimalPeriod F (g x) ∣ Function.minimalPeriod U x)
    (honto : ∀ m : M, ∃ x j, F^[j] (g x) = m) :
    Function.Surjective (transportLens U g F) := by
  intro m
  obtain ⟨x, j, hj⟩ := honto m
  refine ⟨U^[j] (orbitRep U x), ?_⟩
  unfold transportLens
  have hrep : orbitRep U (U^[j] (orbitRep U x)) = orbitRep U x := by
    rw [orbitRep_iterate]; exact orbitRep_idem U x
  rw [hrep]
  set d := Function.minimalPeriod U (orbitRep U x) with hd_def
  have hper : Function.IsPeriodicPt F d (g (orbitRep U x)) :=
    Function.isPeriodicPt_iff_minimalPeriod_dvd.mpr (hdvd (orbitRep U x))
  have hspec : U^[orbitPos U (U^[j] (orbitRep U x))] (orbitRep U x) = U^[j] (orbitRep U x) := by
    have h := orbitPos_spec U (U^[j] (orbitRep U x)); rwa [hrep] at h
  have hlt : orbitPos U (U^[j] (orbitRep U x)) < d := by
    have h := orbitPos_lt U (U^[j] (orbitRep U x)); rw [hrep] at h; rw [hd_def]; exact h
  have hmod := mod_eq_of_iterate_eq (f := U) (x := orbitRep U x)
    (equivPerm_minimalPeriod_pos U (orbitRep U x)) hspec
  rw [← hd_def, Nat.mod_eq_of_lt hlt] at hmod
  rw [hmod, hper.iterate_mod_apply j, ← hj]
  exact congrArg F^[j] (g_orbitRep_eq U hg x).symm

/-- **The fixed-lens factor criterion, converse half** ([Guests] §2 Definition 2.2,
Proposition 2.5): an assignment `g` of `U`-orbits to `F`-orbit basepoints — constant
along `U`-orbits, each image period dividing its source's, and jointly onto `M` — is realized by a
genuine fixed reading, surjective and intertwining `U` with `F`. This is the transport construction
Remark 5.6 uses to read a guest through a lens that never moves. The construction itself does not
assume `F` injective — but `Intertwines.fixed_bijective` shows `F` is bijective automatically
whenever `M` is additionally finite, exactly the regime `zmod_translate_minimalPeriod` and
`zmod_translate_orbitCount` instantiate: the dichotomy is not evaded, only its fixed-lens half is
now realized constructively. -/
theorem Intertwines.exists_fixedLens_of_orbitAssignment [Finite X] (U : Equiv.Perm X) {F : M → M}
    {g : X → M} (hg : ∀ x, g (U x) = g x)
    (hdvd : ∀ x, Function.minimalPeriod F (g x) ∣ Function.minimalPeriod U x)
    (honto : ∀ m : M, ∃ x j, F^[j] (g x) = m) :
    ∃ ℓ : X → M, Function.Surjective ℓ ∧ Intertwines (⇑U) F (fun _ => ℓ) :=
  ⟨transportLens U g F, transportLens_surjective U hg hdvd honto,
    fun _ s => transportLens_semiconj U hdvd s⟩

set_option linter.style.longLine false in
/-- info: 'ALT.Intertwines.exists_fixedLens_of_orbitAssignment' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Intertwines.exists_fixedLens_of_orbitAssignment

/-! ## The single-cycle corollary: the load-bearing dichotomy ([Guests] §2 Proposition 2.5)

Over a host that is one cycle on all of `X`, a fixed lens has no room to be lossy in a
partition-respecting way: reading `ℓ(U^j x) = F^j(ℓ x)` from a single `x` already exhausts `M`, so
`F` must connect every pair of labels. A nontrivial `F`-invariant partition therefore rules out a
fixed lens outright — the bar a non-degenerate decoupled subsystem's code-preserving update forces
on any host it survives as a fixed-lens guest of. -/

/-- **Single-cycle forces transitivity** ([Guests] §2 Proposition 2.5): if `U` is one cycle on
all of `X`, a fixed reading forces `F` to connect every pair of labels in `M`. -/
theorem Intertwines.transitive_of_singleCycle {U : X → X} {F : M → M} {ℓ : X → M}
    (hU : ∀ x y : X, ∃ j : ℕ, U^[j] x = y) (hℓ : Function.Surjective ℓ)
    (h : Intertwines U F (fun _ => ℓ)) :
    ∀ m₁ m₂ : M, ∃ j : ℕ, F^[j] m₁ = m₂ := by
  have hsemiconj : Function.Semiconj ℓ U F := h 0
  intro m₁ m₂
  obtain ⟨x₁, rfl⟩ := hℓ m₁
  obtain ⟨x₂, rfl⟩ := hℓ m₂
  obtain ⟨j, hj⟩ := hU x₁ x₂
  have hiter : ℓ (U^[j] x₁) = F^[j] (ℓ x₁) := hsemiconj.iterate_right j x₁
  rw [hj] at hiter
  exact ⟨j, hiter.symm⟩

/-- info: 'ALT.Intertwines.transitive_of_singleCycle' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Intertwines.transitive_of_singleCycle

/-- **No fixed lens over a single cycle survives a nontrivial invariant partition**
([Guests] §2 Proposition 2.5): if `U` is one cycle on all of `X` and `M` carries an
`F`-invariant equivalence with at least two classes, no fixed reading intertwines `U` with `F` at
all — stated over an abstract invariant partition, the shape a non-degenerate decoupled
subsystem's code/work split instantiates without being built into the statement. -/
theorem Intertwines.not_fixedLens_of_invariantPartition {U : X → X} {F : M → M}
    (hU : ∀ x y : X, ∃ j : ℕ, U^[j] x = y) (S : Setoid M) (hFS : ∀ m, S.r m (F m))
    {m₁ m₂ : M} (hne : ¬ S.r m₁ m₂) :
    ¬ ∃ ℓ : X → M, Function.Surjective ℓ ∧ Intertwines U F (fun _ => ℓ) := by
  rintro ⟨ℓ, hℓ, h⟩
  obtain ⟨j, hj⟩ := Intertwines.transitive_of_singleCycle hU hℓ h m₁ m₂
  have hstep : S.r m₁ (F^[j] m₁) := by
    clear hj
    induction j with
    | zero => exact S.refl m₁
    | succ n ih => rw [Function.iterate_succ_apply']; exact S.trans ih (hFS _)
  rw [hj] at hstep
  exact hne hstep

set_option linter.style.longLine false in
/-- info: 'ALT.Intertwines.not_fixedLens_of_invariantPartition' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Intertwines.not_fixedLens_of_invariantPartition

/-! ## The scale instance: `ZMod (2^k)` under `+1` ([Inevitability] §5 Remark 5.6)

A reading intertwines at time scale `τ`, so the permutation that matters is `U^τ`. On `ZMod (2^k)`
under `+1`, taking `τ = 2^j` produces exactly `2^j` cycles of length `2^(k-j)` — one cycle per code
block once `j = |s_code|`, which is what lets a fixed reading transport a work-memory update along
each block without ever touching the code cells. -/

private theorem addConst_iterate {G : Type*} [AddCommGroup G] (c x : G) (n : ℕ) :
    (fun y => y + c)^[n] x = x + n • c := by
  induction n with
  | zero => simp
  | succ k ih => rw [Function.iterate_succ_apply', ih, succ_nsmul]; abel

private theorem translate_minimalPeriod_eq_addOrderOf {G : Type*} [AddCommGroup G] [Finite G]
    (c x : G) : Function.minimalPeriod (fun y => y + c) x = addOrderOf c := by
  have hper : Function.IsPeriodicPt (fun y => y + c) (addOrderOf c) x := by
    change (fun y => y + c)^[addOrderOf c] x = x
    rw [addConst_iterate, addOrderOf_nsmul_eq_zero, add_zero]
  have hdvd1 : Function.minimalPeriod (fun y => y + c) x ∣ addOrderOf c := hper.minimalPeriod_dvd
  have hpos : 0 < Function.minimalPeriod (fun y => y + c) x :=
    Function.minimalPeriod_pos_of_mem_periodicPts ((add_left_injective c).mem_periodicPts x)
  have hper2 : Function.IsPeriodicPt (fun y => y + c)
      (Function.minimalPeriod (fun y => y + c) x) x := Function.isPeriodicPt_minimalPeriod _ x
  have hz : Function.minimalPeriod (fun y => y + c) x • c = 0 := by
    have h2 : (fun y => y + c)^[Function.minimalPeriod (fun y => y + c) x] x = x := hper2
    rw [addConst_iterate] at h2
    have h3 : x + Function.minimalPeriod (fun y => y + c) x • c = x + 0 := by
      rw [add_zero]; exact h2
    exact add_left_cancel h3
  have hdvd2 : addOrderOf c ∣ Function.minimalPeriod (fun y => y + c) x :=
    addOrderOf_dvd_iff_nsmul_eq_zero.mpr hz
  exact Nat.dvd_antisymm hdvd1 hdvd2

private theorem addRight_one_pow_coe {N : ℕ} (n : ℕ) :
    ⇑((Equiv.addRight (1 : ZMod N)) ^ n) = fun y => y + (n : ZMod N) := by
  induction n with
  | zero => funext y; simp
  | succ m ih =>
      funext y
      rw [pow_succ, Equiv.Perm.coe_mul, Function.comp_apply,
        congrFun ih (Equiv.addRight (1 : ZMod N) y), Equiv.coe_addRight]
      push_cast; ring

private theorem gcd_two_pow (k j : ℕ) (hj : j ≤ k) : Nat.gcd (2 ^ k) (2 ^ j) = 2 ^ j :=
  Nat.gcd_eq_right (pow_dvd_pow 2 hj)

/-- **The orbit length at an arbitrary time scale** ([Guests] §2 Proposition 2.5): every cycle
of the `τ`-th power of `+1` on `ZMod N` has length `N / gcd(N, τ)` — raising the scale acts on a
single host cycle by a gcd, exactly the pull the remark's closed form balances. -/
theorem zmod_translate_minimalPeriod_general {N : ℕ} [NeZero N] (τ : ℕ) (x : ZMod N) :
    Function.minimalPeriod ⇑((Equiv.addRight (1 : ZMod N)) ^ τ) x = N / Nat.gcd N τ := by
  rw [addRight_one_pow_coe, translate_minimalPeriod_eq_addOrderOf]
  exact ZMod.addOrderOf_coe τ (NeZero.ne N)

set_option linter.style.longLine false in
/-- info: 'ALT.zmod_translate_minimalPeriod_general' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms zmod_translate_minimalPeriod_general

/-- **The orbit length at time scale `2^j`** ([Inevitability] §5 Remark 5.6): every cycle of the
`2^j`-th power of `+1` on `ZMod (2^k)` has length `2^(k-j)`, the case of
`zmod_translate_minimalPeriod_general` the remark's decoupled-guest instance uses. -/
theorem zmod_translate_minimalPeriod (k j : ℕ) (hj : j ≤ k) (x : ZMod (2 ^ k)) :
    Function.minimalPeriod ⇑((Equiv.addRight (1 : ZMod (2 ^ k))) ^ (2 ^ j)) x = 2 ^ (k - j) := by
  rw [zmod_translate_minimalPeriod_general, gcd_two_pow k j hj, Nat.pow_div hj (by norm_num)]

set_option linter.style.longLine false in
/-- info: 'ALT.zmod_translate_minimalPeriod' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms zmod_translate_minimalPeriod

/-- **The cycle count at an arbitrary time scale** ([Guests] §2 Proposition 2.5): the `τ`-th
power of `+1` on `ZMod N` has exactly `gcd(N, τ)` cycles — the cosets of the subgroup the
surviving offset generates, and the other half of the same gcd split. -/
theorem zmod_translate_orbitCount_general {N : ℕ} [NeZero N] (τ : ℕ) :
    Nat.card (ZMod N ⧸ AddSubgroup.zmultiples ((τ : ℕ) : ZMod N)) = Nat.gcd N τ := by
  have hcard := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup
    (AddSubgroup.zmultiples ((τ : ℕ) : ZMod N))
  rw [Nat.card_zmultiples, ZMod.addOrderOf_coe τ (NeZero.ne N)] at hcard
  have hZmodCard : Nat.card (ZMod N) = N := by rw [Nat.card_eq_fintype_card, ZMod.card]
  rw [hZmodCard] at hcard
  have hDpos : 0 < N / Nat.gcd N τ :=
    Nat.div_gcd_pos_of_pos_left τ (Nat.pos_of_ne_zero (NeZero.ne N))
  have hsplit : N = Nat.gcd N τ * (N / Nat.gcd N τ) :=
    (Nat.mul_div_cancel' (Nat.gcd_dvd_left N τ)).symm
  exact Nat.eq_of_mul_eq_mul_right hDpos (hcard.symm.trans hsplit)

set_option linter.style.longLine false in
/-- info: 'ALT.zmod_translate_orbitCount_general' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms zmod_translate_orbitCount_general

/-- **The cycle count at time scale `2^j`** ([Inevitability] §5 Remark 5.6): the `2^j`-th power of
`+1` on `ZMod (2^k)` has exactly `2^j` cycles, the case of `zmod_translate_orbitCount_general`
the remark's decoupled-guest instance uses. -/
theorem zmod_translate_orbitCount (k j : ℕ) (hj : j ≤ k) :
    Nat.card (ZMod (2 ^ k) ⧸ AddSubgroup.zmultiples ((2 ^ j : ℕ) : ZMod (2 ^ k))) = 2 ^ j := by
  rw [zmod_translate_orbitCount_general, gcd_two_pow k j hj]

set_option linter.style.longLine false in
/-- info: 'ALT.zmod_translate_orbitCount' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms zmod_translate_orbitCount

/-! ## Guard: the divisibility hypothesis is load-bearing

A concrete refuting instance, held beside `Intertwines.exists_fixedLens_of_orbitAssignment`: over
`U` a single 2-cycle and `F` a single 3-cycle, no reading intertwines them at all, since
`Intertwines.minimalPeriod_dvd` would force `3 ∣ 2`. Dropping the assignment's divisibility
hypothesis would therefore let the converse claim something the forward half already refutes. -/

/-- **The divisibility hypothesis is load-bearing**: a 2-cycle host and a 3-cycle guest law admit
no fixed reading whatever, since `3 ∤ 2`. -/
theorem guard_orbitAssignment_dvd_load_bearing :
    ¬ ∃ ℓ : ZMod 2 → ZMod 3, ∀ x, ℓ (x + 1) = ℓ x + 1 := by
  rintro ⟨ℓ, hℓ⟩
  have h : Intertwines (· + (1 : ZMod 2)) (· + (1 : ZMod 3)) (fun _ => ℓ) := fun _ s => hℓ s
  have hdvd := h.minimalPeriod_dvd 0
  rw [translate_minimalPeriod_eq_addOrderOf, translate_minimalPeriod_eq_addOrderOf] at hdvd
  have h2 : addOrderOf (1 : ZMod 2) = 2 := by simp
  have h3 : addOrderOf (1 : ZMod 3) = 3 := by simp
  rw [h2, h3] at hdvd
  omega

set_option linter.style.longLine false in
/-- info: 'ALT.guard_orbitAssignment_dvd_load_bearing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms guard_orbitAssignment_dvd_load_bearing

/-! ## Block-cyclic sufficiency at an explicit scale ([Guests] §2 Proposition 2.5(ii))

The remark's own instance of `Intertwines.exists_fixedLens_of_orbitAssignment`: a guest of `c`
invariant code blocks, each carrying a `w`-cycle work state, is realized over the single-cycle
host `ZMod N` under `+1` at the scale `τ = N / w`, exactly when `w` divides `N` (delivered from
above, by the transport) and the blocks fit, `c * w ≤ N` (forced from below, by surjectivity) —
the remark's own reading of its two clauses. -/

/-- **The block-cyclic guest's own period** ([Guests] §2 Proposition 2.5(ii)): on `Fin c × ZMod w`
with the block index fixed and the work state advancing by `+1`, every point's period under the
law is exactly `w`. -/
private theorem blockCyclic_minimalPeriod {c w : ℕ} [NeZero w] (a : Fin c) (b : ZMod w) :
    Function.minimalPeriod (Prod.map (id : Fin c → Fin c) (· + (1 : ZMod w))) (a, b) = w := by
  rw [Function.minimalPeriod_prodMap, Function.minimalPeriod_id,
    translate_minimalPeriod_eq_addOrderOf, ZMod.addOrderOf_one, Nat.lcm_one_left]

/-- **Block-cyclic sufficiency at an explicit scale** ([Guests] §2 Proposition 2.5(ii)): over the
single-cycle host `ZMod N` under `+1`, a work-cycle length `w` dividing `N` and fitting `c`
nonempty blocks — `c * w ≤ N` — realize the block-cyclic guest `Fin c × ZMod w` as a surjective
fixed reading intertwining the host's own `N / w`-th power. This is the transport construction
`Intertwines.exists_fixedLens_of_orbitAssignment` uses, at the assignment that sends each `ZMod N`
point to its block via reduction mod `N / w` and a fixed work state — the assignment is the
content the remark's closed form prices, not the transport. -/
theorem exists_blockCyclic_fixedLens {N c w : ℕ} [NeZero N] (hw : w ∣ N) (hc : 0 < c)
    (hcw : c * w ≤ N) :
    ∃ ℓ : ZMod N → Fin c × ZMod w, Function.Surjective ℓ ∧
      Intertwines ⇑((Equiv.addRight (1 : ZMod N)) ^ (N / w))
        (Prod.map (id : Fin c → Fin c) (· + (1 : ZMod w))) (fun _ => ℓ) := by
  have hw0 : w ≠ 0 := by
    rintro rfl
    exact NeZero.ne N (zero_dvd_iff.mp hw)
  have : NeZero w := ⟨hw0⟩
  have hτdvd : N / w ∣ N := Nat.div_dvd_of_dvd hw
  have hτ0 : N / w ≠ 0 := fun h => NeZero.ne N (Nat.eq_zero_of_zero_dvd (h ▸ hτdvd))
  have : NeZero (N / w) := ⟨hτ0⟩
  have hgcd : Nat.gcd N (N / w) = N / w := Nat.gcd_eq_right hτdvd
  have hper : ∀ x : ZMod N,
      Function.minimalPeriod ⇑((Equiv.addRight (1 : ZMod N)) ^ (N / w)) x = w := by
    intro x
    rw [zmod_translate_minimalPeriod_general, hgcd, Nat.div_div_self hw (NeZero.ne N)]
  have hcle : c ≤ N / w := (Nat.le_div_iff_mul_le (Nat.pos_of_ne_zero hw0)).mpr hcw
  set π : ZMod N →+* ZMod (N / w) := ZMod.castHom hτdvd (ZMod (N / w)) with hπ_def
  have hπ_const : ∀ x : ZMod N, π (x + ((N / w : ℕ) : ZMod N)) = π x := by
    intro x
    rw [map_add, map_natCast, ZMod.natCast_self, add_zero]
  set red : ZMod (N / w) → Fin c := fun z => if h : z.val < c then ⟨z.val, h⟩ else ⟨0, hc⟩
    with hred_def
  set h : ZMod N → Fin c := red ∘ π with hh_def
  have hh_const : ∀ x : ZMod N,
      h (⇑((Equiv.addRight (1 : ZMod N)) ^ (N / w)) x) = h x := by
    intro x
    change red (π (⇑((Equiv.addRight (1 : ZMod N)) ^ (N / w)) x)) = red (π x)
    rw [addRight_one_pow_coe, hπ_const]
  have hh_surj : Function.Surjective h := by
    intro a
    refine ⟨((a : ℕ) : ZMod N), ?_⟩
    change red (π (((a : ℕ) : ZMod N))) = a
    have hπa : π (((a : ℕ) : ZMod N)) = ((a : ℕ) : ZMod (N / w)) := map_natCast π (a : ℕ)
    have hlt : (((a : ℕ) : ZMod (N / w))).val < c := by
      rw [ZMod.val_natCast_of_lt (lt_of_lt_of_le a.isLt hcle)]
      exact a.isLt
    rw [hπa, hred_def]
    simp only [dite_eq_left hlt]
    ext
    change ((a : ℕ) : ZMod (N / w)).val = a
    rw [ZMod.val_natCast_of_lt (lt_of_lt_of_le a.isLt hcle)]
  set g : ZMod N → Fin c × ZMod w := fun x => (h x, 0) with hg_def
  have hg_const : ∀ x : ZMod N,
      g (⇑((Equiv.addRight (1 : ZMod N)) ^ (N / w)) x) = g x := by
    intro x
    rw [hg_def]
    simp only [hh_const x]
  have hdvd : ∀ x : ZMod N,
      Function.minimalPeriod (Prod.map (id : Fin c → Fin c) (· + (1 : ZMod w))) (g x)
        ∣ Function.minimalPeriod ⇑((Equiv.addRight (1 : ZMod N)) ^ (N / w)) x := by
    intro x
    rw [hg_def, blockCyclic_minimalPeriod, hper]
  have honto : ∀ m : Fin c × ZMod w, ∃ x j,
      (Prod.map (id : Fin c → Fin c) (· + (1 : ZMod w)))^[j] (g x) = m := by
    rintro ⟨a, b⟩
    obtain ⟨x, hx⟩ := hh_surj a
    refine ⟨x, b.val, ?_⟩
    rw [hg_def, Prod.map_iterate, Function.iterate_id]
    change (h x, (fun y => y + (1 : ZMod w))^[b.val] 0) = (a, b)
    rw [addConst_iterate, hx, zero_add, Nat.smul_one_eq_cast, ZMod.natCast_zmod_val]
  exact Intertwines.exists_fixedLens_of_orbitAssignment
    ((Equiv.addRight (1 : ZMod N)) ^ (N / w)) hg_const hdvd honto

set_option linter.style.longLine false in
/-- info: 'ALT.exists_blockCyclic_fixedLens' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms exists_blockCyclic_fixedLens

/-! ## The prime-period bar at every scale ([Guests] §2 Proposition 2.5(iii))

Over a host that is a single cycle of PRIME length, raising the scale buys the covering half
nothing: the remark's own closed form forces `ord(F) ∈ {1, N}`, i.e. `U^τ` is either the identity
(`N ∣ τ`) or again a single `N`-cycle (`N ∤ τ`, since `N` prime forces `gcd(N,τ)=1`) — and the
single-cycle case is already `not_fixedLens_of_invariantPartition`'s bar, applied at `U^τ` in
place of `U`. The identity case needs one more ingredient the abstract dichotomy does not supply
on its own: `F` must actually move something, or the trivial law satisfies every invariant
partition vacuously (`Decoupling` §2.3 names this "memory" case as the triviality its own
threshold does not exclude — which is why it is a hypothesis here rather than derived). -/

/-- **A coprime power of a single cycle is again a single cycle**: if `U` is transitive on all of
`X` and `τ` is coprime to the minimal period at one basepoint, `U^τ` is transitive on all of `X`
too — raising the scale by a step coprime to the host's own length re-covers it exactly. -/
private theorem transitive_pow_of_coprime [Finite X] {U : X → X}
    (hU : ∀ x y : X, ∃ j : ℕ, U^[j] x = y) {x₀ : X} {N τ : ℕ} (hN0 : N ≠ 0)
    (hN : Function.minimalPeriod U x₀ = N) (hcop : Nat.Coprime N τ) :
    ∀ x y : X, ∃ j : ℕ, (U^[τ])^[j] x = y := by
  have : NeZero N := ⟨hN0⟩
  intro x y
  obtain ⟨i, hi⟩ := hU x₀ x
  obtain ⟨i', hi'⟩ := hU x₀ y
  obtain ⟨v, hv⟩ := ((ZMod.isUnit_iff_coprime τ N).mpr hcop.symm).exists_right_inv
  set z : ZMod N := v * ((i' : ZMod N) - (i : ZMod N)) with hz_def
  have hτz : (τ : ZMod N) * z = (i' : ZMod N) - (i : ZMod N) := by
    rw [hz_def, ← mul_assoc, hv, one_mul]
  have hmod : (τ * z.val + i) % N = i' % N := by
    apply (ZMod.natCast_eq_natCast_iff' _ _ _).mp
    push_cast
    rw [ZMod.natCast_zmod_val, hτz]
    ring
  refine ⟨z.val, ?_⟩
  rw [← Function.iterate_mul, ← hi, ← Function.iterate_add_apply,
    ← Function.iterate_mod_minimalPeriod_eq, hN, hmod, ← hN,
    Function.iterate_mod_minimalPeriod_eq, hi']

/-- **The prime-period bar survives raising the scale** ([Guests] §2 Proposition 2.5(iii)): over a
host that is a single cycle of prime length, no surjective fixed reading intertwines `U^τ` with a
law that both moves something and carries a nontrivial invariant partition, at any scale `τ`. The
identity clause (`∃ m, F m ≠ m`) is not in the remark's own statement of the bar — it is exactly
what excludes the "memory" triviality *Decoupling* §2.3 already names as the threshold's one
un-excluded degenerate case, and it is only needed when `N ∣ τ`, where `U^τ` collapses to the
identity and the invariant-partition hypothesis alone is satisfied vacuously by `F = id`. -/
theorem Intertwines.not_fixedLens_prime_period_any_scale [Finite X] {U : X → X} {F : M → M}
    (hU : ∀ x y : X, ∃ j : ℕ, U^[j] x = y) {x₀ : X}
    (hp : Nat.Prime (Function.minimalPeriod U x₀)) (hFid : ∃ m, F m ≠ m) (S : Setoid M)
    (hFS : ∀ m, S.r m (F m)) {m₁ m₂ : M} (hne : ¬ S.r m₁ m₂) (τ : ℕ) :
    ¬ ∃ ℓ : X → M, Function.Surjective ℓ ∧ Intertwines (U^[τ]) F (fun _ => ℓ) := by
  by_cases hdvd : Function.minimalPeriod U x₀ ∣ τ
  · rintro ⟨ℓ, hℓ, h⟩
    have hUid : ∀ x, U^[τ] x = x := by
      intro x
      obtain ⟨j, hj⟩ := hU x₀ x
      have hx0 : U^[τ] x₀ = x₀ := Function.isPeriodicPt_iff_minimalPeriod_dvd.mpr hdvd
      calc U^[τ] x = U^[τ] (U^[j] x₀) := by rw [hj]
        _ = U^[j] (U^[τ] x₀) := by
              rw [← Function.iterate_add_apply, Nat.add_comm, Function.iterate_add_apply]
        _ = U^[j] x₀ := by rw [hx0]
        _ = x := hj
    have hsemiconj : Function.Semiconj ℓ (U^[τ]) F := h 0
    have hFfix : ∀ x : X, ℓ x = F (ℓ x) := fun x => by
      have := hsemiconj x; rwa [hUid x] at this
    have hFid' : ∀ m, F m = m := fun m => by
      obtain ⟨x, rfl⟩ := hℓ m; exact (hFfix x).symm
    obtain ⟨m₀, hm₀⟩ := hFid
    exact hm₀ (hFid' m₀)
  · have hcop : Nat.Coprime (Function.minimalPeriod U x₀) τ := hp.coprime_iff_not_dvd.mpr hdvd
    exact Intertwines.not_fixedLens_of_invariantPartition
      (transitive_pow_of_coprime hU hp.pos.ne' rfl hcop) S hFS hne

set_option linter.style.longLine false in
/-- info: 'ALT.Intertwines.not_fixedLens_prime_period_any_scale' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Intertwines.not_fixedLens_prime_period_any_scale

/-! ## Guard: the capacity condition is load-bearing

A concrete refuting instance, held beside `exists_blockCyclic_fixedLens`: when the blocks overflow
the host, `c * w > N`, no reading of `ZMod N` into `Fin c × ZMod w` is even surjective — a pure
cardinality bound, prior to any question of intertwining. Dropping the capacity hypothesis would
therefore let the sufficiency claim something surjectivity alone already refutes. -/

/-- **The capacity hypothesis is load-bearing**: `c` blocks of `w` work states outnumber the host
the moment `c * w > N`, so no reading `ZMod N → Fin c × ZMod w` is surjective at all. -/
theorem guard_blockCyclic_capacity_load_bearing {N c w : ℕ} [NeZero N] [NeZero w]
    (hcw : N < c * w) :
    ¬ ∃ ℓ : ZMod N → Fin c × ZMod w, Function.Surjective ℓ := by
  rintro ⟨ℓ, hℓ⟩
  have hle : Nat.card (Fin c × ZMod w) ≤ Nat.card (ZMod N) :=
    Nat.card_le_card_of_surjective ℓ hℓ
  rw [Nat.card_prod, Nat.card_eq_fintype_card (α := Fin c), Fintype.card_fin,
    Nat.card_eq_fintype_card (α := ZMod w), ZMod.card, Nat.card_eq_fintype_card (α := ZMod N),
    ZMod.card] at hle
  omega

set_option linter.style.longLine false in
/-- info: 'ALT.guard_blockCyclic_capacity_load_bearing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms guard_blockCyclic_capacity_load_bearing

/-! ## Guard: the primality hypothesis is load-bearing

A concrete refuting instance, held beside `Intertwines.not_fixedLens_prime_period_any_scale`: at
the composite length `4 = 2^2` — the case [Inevitability] §5 Remark 5.6 turns on — the block-index
partition on `Fin 2 × ZMod 2` is nontrivial and `F`-invariant, yet IS realized by a surjective
fixed reading, at scale `τ = 4 / 2`. Dropping primality from the bar would therefore claim
something this instance, built from `exists_blockCyclic_fixedLens` itself, already refutes. -/

/-- **The primality hypothesis is load-bearing**: at the composite length `4`, a nontrivial
`F`-invariant partition on the block-cyclic guest is realized by a surjective fixed reading, the
scale-multiplied cycle count the prime case forbids. -/
theorem guard_primePeriod_composite_load_bearing :
    ∃ (S : Setoid (Fin 2 × ZMod 2)),
      (∀ m, S.r m ((Prod.map (id : Fin 2 → Fin 2) (· + (1 : ZMod 2))) m)) ∧
      (∃ m₁ m₂, ¬ S.r m₁ m₂) ∧
      ∃ ℓ : ZMod 4 → Fin 2 × ZMod 2, Function.Surjective ℓ ∧
        Intertwines ⇑((Equiv.addRight (1 : ZMod 4)) ^ (4 / 2))
          (Prod.map (id : Fin 2 → Fin 2) (· + (1 : ZMod 2))) (fun _ => ℓ) := by
  refine ⟨⟨fun p q => p.1 = q.1, fun _ => rfl, fun h => h.symm, fun h1 h2 => h1.trans h2⟩,
    fun _ => rfl, ⟨(0, 0), (1, 0), show (0 : Fin 2) ≠ 1 by decide⟩, ?_⟩
  exact exists_blockCyclic_fixedLens (N := 4) (c := 2) (w := 2)
    (by norm_num) (by norm_num) (by norm_num)

set_option linter.style.longLine false in
/-- info: 'ALT.guard_primePeriod_composite_load_bearing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms guard_primePeriod_composite_load_bearing

end ALT
