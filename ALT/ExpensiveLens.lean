/-
Copyright (c) 2026 Mykola Palamarchuk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mykola Palamarchuk
-/
import Mathlib.GroupTheory.Perm.Cycle.Basic
import Mathlib.GroupTheory.Perm.Fin
import ALT.PersistenceCapacity

-- Formal-check file, not Mathlib-destined: opt out of the house-style header linter.
set_option linter.style.header false

/-!
# The expensive-lens guard family: a double pigeonhole in the counting currency
([Persistence] §8, Propositions 8.35(iv)–(v) and 8.36(ii), Remark 8.37)

Proposition 8.35 orders the pricing points a reading can be charged against and shows the order's
freedom term is monotone while its address is not (clause (iii)); the crossover this produces
(clause (iv)) is exactly the lens's address in excess of the region's own, against the fibre freedom
the lens removes, and over an incompressible region every descending lens costs its own carried
entropy (clause (v)). Proposition 8.36(ii) realizes the expensive side of that crossover by an
explicit construction: an incompressible cycle read by position modulo `z`, at fibre size
`c ≥ z²`. This module is the *expensive lens* negative family — a witness kept beside the
results it guards, in the style of the library's other load-bearing-hypothesis witnesses: past
the crossover, "the composite is stronger" is false.

The family here is **not** stated against Proposition 8.36(ii)'s own decoder or its reading clauses
(the budget `b`, `E_Z = log₂ z`, the two content comparisons against `2b`): that route is vacuous
in this construction's own regime, since rearranging `ledger_descent`'s display prices the index at
a coefficient of at least sixteen, which alone exceeds the floor's content here. Instead the family
is staged in the **counting currency**: a double pigeonhole over `Equiv.Perm (Fin
N)`, `N := c * z`, with no decoder, no `lensCode` transport of a display, and no two-halves world
(the region-and-complement apparatus of Proposition 8.36(ii) as stated is not built — the guard
works with the cycle as the whole world, where the crossover's content already lives).

**The construction.** `baseWorld z c` is the standard `N`-cycle (`finRotate N`) and `baseLens z c`
reads position modulo `z`; it descends through `baseWorld z c` with law the `z`-shift
(`baseLens_descent`) — the divisibility `z ∣ N` this needs is exactly why `N` is `c * z` — and every
fibre has size `c` (`baseLens_fiber_card`). Conjugating by an arbitrary `V` transports both:
`conjWorld z c V := V * baseWorld z c * V⁻¹` is again an `N`-cycle (`conjWorld_isCycle`),
descending through `conjLens z c V := baseLens z c ∘ ⇑V⁻¹` with the same law
(`conjLens_descent`), and the fibre profile survives (`conjLens_fiber_card`).

**The double pigeonhole.** The lens map `V ↦ conjLens z c V` and the world map `V ↦ conjWorld z c V`
each have few permutations affording a cheap `lensCode` (`AdditiveComplexity.card_KE_le`'s counting
bound, pulled back one fibre at a time): the lens map's fibres are cosets of `baseLens z c`'s
stabilizer, of order `(c !) ^ z`, which is exactly `PersistenceCapacity.collapse_count` read at
`baseLens z c` (`lens_collapse_count`); the world map's fibres are cosets of `baseWorld z c`'s
centralizer, of order at most `N` — a cycle covering the whole domain is determined by the image of
one point, so a centralizing permutation is determined by where it sends that point
(`conj_collapse_count`, the module's own new counting engine). Since fewer than the arithmetic
hypothesis's share of the `N !` permutations clear either floor, some `V` clears both at once
(`expensiveLens_family`) — the guard-family reading of `Proposition 8.35(iv)`: past the crossover a
cheap lens is unavailable *and* a cheap world is unavailable, at once, so no pricing point
recovers the composite's optimism. The lens floor is `Proposition 8.35(v)`'s incompressible-region
clause read at this construction: `card_orbit_mul_prod_fiber` in `PersistenceCapacity.lean` names
the lens's own carried entropy, `N ! / (c !) ^ z`, at the uniform profile.

**What stays open.** Proposition 8.36(ii) as stated — its budget, its `E_Z` display, its two content
comparisons — sits on §8's standing transport boundary and is untouched; so is Proposition 8.35(v)'s
general `∀`-form (only the `∃`-family lands). The two-halves world and FV-21's display and encoding
boundary are deliberately not consumed. Cite `[Persistence] §8` at Propositions 8.35(iv)–(v) and
8.36(ii) with Remark 8.37.
-/

namespace ExpensiveLens

open Equiv Equiv.Perm AdditiveComplexity PersistenceCapacity Nat

variable {z c : ℕ}

/-! ### The constructive lens and its conjugation transport -/

/-- The standard `N`-cycle, `N := c * z`. -/
noncomputable def baseWorld (z c : ℕ) : Equiv.Perm (Fin (c * z)) := finRotate (c * z)

/-- The arithmetic lens reading position modulo `z`. -/
def baseLens (z c : ℕ) : Fin (c * z) → Fin z := Fin.modNat

private theorem finRotate_moves {N : ℕ} (hN : 2 ≤ N) : ∀ x : Fin N, (finRotate N) x ≠ x := by
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  intro x hx
  have hv := coe_finRotate (n := M) x
  simp only [Nat.succ_eq_add_one] at hv
  rcases eq_or_ne x (Fin.last M) with hlast | hlast
  · rw [if_pos hlast] at hv
    have hval : (finRotate (M + 1) x).val = x.val := congrArg Fin.val hx
    rw [hval] at hv
    have hlv : (Fin.last M).val = M := rfl
    rw [hlast, hlv] at hv
    omega
  · rw [if_neg hlast] at hv
    have hval : (finRotate (M + 1) x).val = x.val := congrArg Fin.val hx
    omega

private theorem baseWorld_isCycle (hz : 2 ≤ z) (hc : 2 ≤ c) : (baseWorld z c).IsCycle :=
  isCycle_finRotate_of_le (by nlinarith)

private theorem baseWorld_moves (hz : 2 ≤ z) (hc : 2 ≤ c) : ∀ x, baseWorld z c x ≠ x :=
  finRotate_moves (by nlinarith)

/-- **The descent law** ([Persistence] §8, Proposition 8.36(ii)'s construction): `baseLens`
descends through `baseWorld` with law the `z`-shift. The wrap step is where `z ∣ c * z` bites. -/
theorem baseLens_descent (hz : 2 ≤ z) (hc : 2 ≤ c) (x : Fin (c * z)) :
    baseLens z c (baseWorld z c x) = (finRotate z) (baseLens z c x) := by
  have : NeZero (c * z) := ⟨by positivity⟩
  have : NeZero z := ⟨by omega⟩
  apply Fin.ext
  have hdvd : z ∣ c * z := ⟨c, by ring⟩
  have h1 : ((1 : Fin (c * z)) : ℕ) = 1 := by
    rw [Fin.val_one']; exact Nat.mod_eq_of_lt (by nlinarith)
  have h2 : ((1 : Fin z) : ℕ) = 1 := by rw [Fin.val_one']; exact Nat.mod_eq_of_lt (by omega)
  have hLHS : (baseLens z c (baseWorld z c x) : ℕ) = (x.val + 1) % z := by
    change ((baseWorld z c x).modNat : ℕ) = _
    rw [Fin.coe_modNat]
    change ((finRotate (c * z) x : Fin (c * z)) : ℕ) % z = _
    rw [finRotate_apply, Fin.val_add, h1, Nat.mod_mod_of_dvd _ hdvd]
  have hRHS : ((finRotate z) (baseLens z c x) : ℕ) = ((x.val % z) + 1) % z := by
    change ((finRotate z) (Fin.modNat x) : ℕ) = _
    rw [finRotate_apply, Fin.val_add, h2, Fin.coe_modNat]
  rw [hLHS, hRHS, Nat.add_mod, Nat.mod_eq_of_lt (show 1 < z by omega)]

private def fiberEquiv (z c : ℕ) (i : Fin z) :
    {x : Fin (c * z) // baseLens z c x = i} ≃ Fin c where
  toFun x := x.1.divNat
  invFun j := ⟨j.mkDivMod i, Fin.modNat_mkDivMod j i⟩
  left_inv x := by
    apply Subtype.ext
    have hx2 : x.1.modNat = i := x.2
    have h2 : x.1.divNat.mkDivMod x.1.modNat = x.1 := Fin.divNat_mkDivMod_modNat x.1
    rw [hx2] at h2
    exact h2
  right_inv j := by apply Fin.divNat_mkDivMod

/-- **The fibre profile** ([Persistence] §8, Proposition 8.36(ii)'s construction): every fibre of
`baseLens` has size exactly `c`. -/
theorem baseLens_fiber_card (i : Fin z) :
    Nat.card {x : Fin (c * z) // baseLens z c x = i} = c := by
  rw [Nat.card_congr (fiberEquiv z c i)]; simp

/-- The conjugate world: again an `N`-cycle, by `conjWorld_isCycle`. -/
noncomputable def conjWorld (z c : ℕ) (V : Equiv.Perm (Fin (c * z))) : Equiv.Perm (Fin (c * z)) :=
  V * baseWorld z c * V⁻¹

/-- The transported lens, relabelling `baseLens` by `V`. -/
def conjLens (z c : ℕ) (V : Equiv.Perm (Fin (c * z))) : Fin (c * z) → Fin z :=
  baseLens z c ∘ ⇑V⁻¹

private theorem conjWorld_isCycle (hz : 2 ≤ z) (hc : 2 ≤ c) (V : Equiv.Perm (Fin (c * z))) :
    (conjWorld z c V).IsCycle := (baseWorld_isCycle hz hc).conj

/-- **Conjugation transports the descent law** ([Persistence] §8, Proposition 8.36(ii)'s
construction): `conjLens z c V` descends through `conjWorld z c V` with the same `z`-shift law, for
every `V`. -/
theorem conjLens_descent (hz : 2 ≤ z) (hc : 2 ≤ c) (V : Equiv.Perm (Fin (c * z)))
    (x : Fin (c * z)) :
    conjLens z c V (conjWorld z c V x) = (finRotate z) (conjLens z c V x) := by
  have hrw : (V⁻¹ : Equiv.Perm (Fin (c * z))) ((V * baseWorld z c * V⁻¹) x)
      = baseWorld z c (V⁻¹ x) := by simp [Equiv.Perm.mul_apply]
  change baseLens z c (V⁻¹ ((V * baseWorld z c * V⁻¹) x)) = _
  rw [hrw]
  exact baseLens_descent hz hc (V⁻¹ x)

/-- **Conjugation transports the fibre profile**: every fibre of `conjLens z c V` has size `c`,
for every `V`. -/
theorem conjLens_fiber_card (V : Equiv.Perm (Fin (c * z))) (i : Fin z) :
    Nat.card {x : Fin (c * z) // conjLens z c V x = i} = c := by
  have e : {x : Fin (c * z) // conjLens z c V x = i} ≃ {y : Fin (c * z) // baseLens z c y = i} :=
    Equiv.subtypeEquiv V⁻¹ (fun x => Iff.rfl)
  rw [Nat.card_congr e]
  exact baseLens_fiber_card i

/-! ### The double pigeonhole over `Equiv.Perm (Fin (c * z))` -/

private theorem lensCode_inj' {n m : ℕ} : Function.Injective (lensCode (n := n) (m := m)) := by
  intro ℓ ℓ' h
  have h2 : lensTable ℓ = lensTable ℓ' := Encodable.encode_injective h
  funext x
  have hx : ((ℓ x : Fin m) : ℕ) = ((ℓ' x : Fin m) : ℕ) :=
    (List.map_inj_left.mp h2) x (List.mem_finRange x)
  exact Fin.val_injective hx

/-- **A centralizing permutation is determined by one value** ([Persistence] §8, Proposition
8.36(ii)'s counting floor, the world-side half). A cycle whose orbit covers the whole domain is
determined, on that orbit, by where it sends any single point; a permutation conjugation-fixing it
commutes with it, hence carries its powers through, hence is pinned by the image of one point. No
general cycle-centralizer theorem is used — this is the elementary injection §4.58 recommends. -/
private theorem centralizer_card_le {N : ℕ} [NeZero N] (U₀ : Equiv.Perm (Fin N))
    (hcyc : U₀.IsCycle) (hmove : ∀ x, U₀ x ≠ x) :
    (Finset.univ.filter (fun g : Equiv.Perm (Fin N) => g * U₀ * g⁻¹ = U₀)).card ≤ N := by
  classical
  have hex : ∀ y : Fin N, ∃ k : ℕ, (U₀ ^ k) 0 = y := fun y =>
    hcyc.exists_pow_eq (hmove 0) (hmove y)
  have hcommP : ∀ (g : Equiv.Perm (Fin N)), g * U₀ = U₀ * g →
      ∀ k x, g ((U₀ ^ k) x) = (U₀ ^ k) (g x) := by
    intro g hg k
    induction k with
    | zero => intro x; simp
    | succ n ih =>
      intro x
      have step : ∀ y, g (U₀ y) = U₀ (g y) := fun y => by
        have := congrFun (congrArg (fun (e : Equiv.Perm (Fin N)) => (e : Fin N → Fin N)) hg) y
        simpa [Equiv.Perm.mul_apply] using this
      calc g ((U₀ ^ (n + 1)) x) = g (U₀ ((U₀ ^ n) x)) := by
            rw [_root_.pow_succ', Equiv.Perm.mul_apply]
        _ = U₀ (g ((U₀ ^ n) x)) := step _
        _ = U₀ ((U₀ ^ n) (g x)) := by rw [ih]
        _ = (U₀ ^ (n + 1)) (g x) := by rw [_root_.pow_succ', Equiv.Perm.mul_apply]
  have hinj : Set.InjOn (fun g : Equiv.Perm (Fin N) => g 0)
      ↑(Finset.univ.filter (fun g : Equiv.Perm (Fin N) => g * U₀ * g⁻¹ = U₀)) := by
    intro g hg g' hg' heq
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hg hg'
    have hg2 : g * U₀ = U₀ * g := mul_inv_eq_iff_eq_mul.mp hg
    have hg2' : g' * U₀ = U₀ * g' := mul_inv_eq_iff_eq_mul.mp hg'
    have heq' : g 0 = g' 0 := heq
    apply Equiv.ext
    intro y
    obtain ⟨k, hk⟩ := hex y
    rw [← hk, hcommP g hg2 k 0, heq', ← hcommP g' hg2' k 0]
  have := Finset.card_le_card_of_injOn (fun g : Equiv.Perm (Fin N) => g 0)
    (fun a _ => Finset.mem_univ _) hinj
  simpa using this

/-- **The world floor** ([Persistence] §8, Proposition 8.36(ii)'s counting floor, the world-side
half): at most `2 ^ (L + 1) * N` permutations `V` conjugate a fixed `N`-cycle `U₀` into a world
whose table is `L`-affordable. Mirrors `PersistenceCapacity.collapse_count`, with the world map's
centralizer-coset fibres (`centralizer_card_le`, order at most `N`) in place of the lens map's
stabilizer-coset fibres. -/
theorem conj_collapse_count {N : ℕ} [NeZero N] (U₀ : Equiv.Perm (Fin N)) (hcyc : U₀.IsCycle)
    (hmove : ∀ x, U₀ x ≠ x) (L : ℕ) :
    {V : Equiv.Perm (Fin N) | KE (lensCode (⇑(V * U₀ * V⁻¹))) ≤ L}.ncard ≤ 2 ^ (L + 1) * N := by
  classical
  set f : Equiv.Perm (Fin N) → ℕ := fun V => lensCode (⇑(V * U₀ * V⁻¹)) with hf
  set S : Finset (Equiv.Perm (Fin N)) := Finset.univ.filter fun V => KE (f V) ≤ L with hSdef
  set T : Finset ℕ := (finite_KE_le L).toFinset with hTdef
  have hfib : ∀ v ∈ T, (S.filter fun V => f V = v).card ≤ N := by
    intro v _
    rcases Finset.eq_empty_or_nonempty (S.filter fun V => f V = v) with hemp | ⟨W, hW⟩
    · simp [hemp]
    · have hWv : f W = v := (Finset.mem_filter.mp hW).2
      have hmaps : ∀ U ∈ S.filter fun V => f V = v,
          W⁻¹ * U ∈ Finset.univ.filter fun g : Equiv.Perm (Fin N) => g * U₀ * g⁻¹ = U₀ := by
        intro U hU
        have hUv : f U = v := (Finset.mem_filter.mp hU).2
        have hUW : (⇑(U * U₀ * U⁻¹) : Fin N → Fin N) = ⇑(W * U₀ * W⁻¹) :=
          lensCode_inj' (hUv.trans hWv.symm)
        have hUW' : U * U₀ * U⁻¹ = W * U₀ * W⁻¹ := Equiv.coe_fn_injective hUW
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        calc W⁻¹ * U * U₀ * (W⁻¹ * U)⁻¹
            = W⁻¹ * (U * U₀ * U⁻¹) * W := by group
          _ = W⁻¹ * (W * U₀ * W⁻¹) * W := by rw [hUW']
          _ = U₀ := by group
      have hinj : Set.InjOn (fun U => W⁻¹ * U) ↑(S.filter fun V => f V = v) :=
        fun a _ c _ hac => by
          have : (W⁻¹)⁻¹ * (W⁻¹ * a) = (W⁻¹)⁻¹ * (W⁻¹ * c) := congrArg (fun x => (W⁻¹)⁻¹ * x) hac
          simpa using this
      have hcard := Finset.card_le_card_of_injOn (fun U => W⁻¹ * U) hmaps hinj
      exact le_trans hcard (centralizer_card_le U₀ hcyc hmove)
  have hmapsT : ∀ U ∈ S, f U ∈ T := by
    intro U hU
    simpa [hTdef] using (Finset.mem_filter.mp hU).2
  have hmain := Finset.card_le_mul_card_image_of_maps_to hmapsT N hfib
  have hT : T.card ≤ 2 ^ (L + 1) := by
    have := card_KE_le L
    rwa [Set.ncard_eq_toFinset_card _ (finite_KE_le L)] at this
  have hSset : {V : Equiv.Perm (Fin N) | KE (lensCode (⇑(V * U₀ * V⁻¹))) ≤ L} = ↑S := by
    ext V; simp [hSdef, hf]
  rw [hSset, Set.ncard_coe_finset]
  calc S.card ≤ N * T.card := hmain
    _ ≤ N * 2 ^ (L + 1) := Nat.mul_le_mul_left _ hT
    _ = 2 ^ (L + 1) * N := Nat.mul_comm _ _

attribute [local instance] arrowAction

/-- **The lens floor** ([Persistence] §8, Proposition 8.36(ii)'s counting floor, the lens-side
half): at most `2 ^ (L + 1) * (c !) ^ z` permutations `V` relabel `baseLens` into an `L`-affordable
table. `PersistenceCapacity.collapse_count` read at `baseLens z c`, with the fibre profile
(`baseLens_fiber_card`) collapsing the stabilizer order to `(c !) ^ z`. -/
theorem lens_collapse_count (L : ℕ) :
    {V : Equiv.Perm (Fin (c * z)) | KE (lensCode (conjLens z c V)) ≤ L}.ncard
      ≤ 2 ^ (L + 1) * (c !) ^ z := by
  have h := collapse_count (baseLens z c) L
  have heq : ∀ V : Equiv.Perm (Fin (c * z)), V • (baseLens z c) = conjLens z c V := fun _ => rfl
  have hprod : (∏ i : Fin z, (Nat.card {x : Fin (c * z) // baseLens z c x = i})!) = (c !) ^ z := by
    rw [Finset.prod_congr rfl (fun i _ => by rw [baseLens_fiber_card i])]
    simp
  rw [hprod] at h
  have hset : {V : Equiv.Perm (Fin (c * z)) | KE (lensCode (conjLens z c V)) ≤ L}
      = {V : Equiv.Perm (Fin (c * z)) | KE (lensCode (V • baseLens z c)) ≤ L} := by
    ext V; simp only [Set.mem_ofPred_eq, heq V]
  rw [hset]; exact h

private theorem exists_double_witness {N : ℕ} (Bad1 Bad2 : Set (Equiv.Perm (Fin N)))
    (h : Bad1.ncard + Bad2.ncard < N !) : ∃ V, V ∉ Bad1 ∧ V ∉ Bad2 := by
  have huniv : (Set.univ : Set (Equiv.Perm (Fin N))).ncard = N ! := by
    rw [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
  have hun : (Bad1 ∪ Bad2).ncard ≤ Bad1.ncard + Bad2.ncard := Set.ncard_union_le Bad1 Bad2
  have hne : Bad1 ∪ Bad2 ≠ Set.univ := by
    intro heq
    rw [heq, huniv] at hun
    omega
  have hnall : ¬ ∀ V, V ∈ Bad1 ∪ Bad2 := fun hall => hne (Set.eq_univ_of_forall hall)
  obtain ⟨V, hV⟩ := not_forall.mp hnall
  exact ⟨V, fun h1 => hV (Or.inl h1), fun h2 => hV (Or.inr h2)⟩

/-! ### The capstone -/

/-- **The expensive-lens guard family** ([Persistence] §8, Proposition 8.35(iv)–(v) and
Proposition 8.36(ii), the expensive side of the crossover): whenever the arithmetic hypothesis
clears — the lens floor and the world floor together undercut `(c * z) !` — a conjugate `V` of
the standard cycle carries BOTH an incompressible lens and an incompressible world at once, past
the budgets `L₁` and `L₂`. This is the counting-currency form of the crossover: past it, a cheap
composite pricing point is unavailable together with a cheap lens, so "the composite is stronger"
is refuted at the parameters this family witnesses. Proposition 8.35(v)'s own reading is
`lensCode (conjLens z c V)` costing at least the lens's carried entropy,
`log₂ [(c * z) ! / (c !) ^ z]`
(`PersistenceCapacity.card_orbit_mul_prod_fiber` at the uniform profile) — the family below
states the `∃`-witness this floor forces, not the general `∀`-bound, which stays paper-level. -/
theorem expensiveLens_family (z c L₁ L₂ : ℕ) (hz : 2 ≤ z) (hc : 2 ≤ c)
    (h : 2 ^ (L₁ + 1) * (c !) ^ z + 2 ^ (L₂ + 1) * (c * z) < (c * z)!) :
    ∃ V : Equiv.Perm (Fin (c * z)),
      (conjWorld z c V).IsCycle
      ∧ (∀ x, conjLens z c V (conjWorld z c V x) = (finRotate z) (conjLens z c V x))
      ∧ (∀ i, Nat.card {x : Fin (c * z) // conjLens z c V x = i} = c)
      ∧ L₁ < KE (lensCode (conjLens z c V))
      ∧ L₂ < KE (lensCode (⇑(conjWorld z c V))) := by
  have : NeZero (c * z) := ⟨by positivity⟩
  have hB1 := lens_collapse_count (z := z) (c := c) L₁
  have hB2 := conj_collapse_count (baseWorld z c) (baseWorld_isCycle hz hc)
    (baseWorld_moves hz hc) L₂
  obtain ⟨V, hV1, hV2⟩ := exists_double_witness
    {V : Equiv.Perm (Fin (c * z)) | KE (lensCode (conjLens z c V)) ≤ L₁}
    {V : Equiv.Perm (Fin (c * z)) | KE (lensCode (⇑(V * baseWorld z c * V⁻¹))) ≤ L₂}
    (by omega)
  refine ⟨V, conjWorld_isCycle hz hc V, conjLens_descent hz hc V, conjLens_fiber_card V,
    by simpa using hV1, by simpa [conjWorld] using hV2⟩

/-- **A concrete instance** ([Persistence] §8, Remark 8.37's `Ω(N · log₂ z)`-growing margin):
`z = 3`, `c = 9`, `N = 27`, well inside
the paper's `c ≥ z²` regime. `27 !` clears both floors at budgets `30` bits with a margin of two
orders of magnitude, checked by `decide` on the explicit numerals. -/
theorem expensiveLens_instance :
    ∃ V : Equiv.Perm (Fin (9 * 3)),
      (conjWorld 3 9 V).IsCycle
      ∧ (∀ x, conjLens 3 9 V (conjWorld 3 9 V x) = (finRotate 3) (conjLens 3 9 V x))
      ∧ (∀ i, Nat.card {x : Fin (9 * 3) // conjLens 3 9 V x = i} = 9)
      ∧ 30 < KE (lensCode (conjLens 3 9 V))
      ∧ 30 < KE (lensCode (⇑(conjWorld 3 9 V))) :=
  expensiveLens_family 3 9 30 30 (by norm_num) (by norm_num) (by decide)

end ExpensiveLens

/-- info: 'ExpensiveLens.expensiveLens_family' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ExpensiveLens.expensiveLens_family

/-- info: 'ExpensiveLens.expensiveLens_instance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ExpensiveLens.expensiveLens_instance
