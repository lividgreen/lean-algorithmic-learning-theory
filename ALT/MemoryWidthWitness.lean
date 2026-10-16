module

public import Nonautonomous.ReachabilityWidth
public import ALT.GrowingCore
public import ALT.GrowingCoreCrossing


/-!
# The memory width at the accreting healer world
([Guests] §7 Theorem 7.9)

`ReachabilityWidth.lean` defines the memory width on the merge quotient and proves it monotone, with
the guard families around it. This file evaluates it at the accreting healer world
(`ALT.accUpdate` over `ALT.Mem`) and feeds the result to the crossing.

## Main results

* `mergeStage_accUpdate_isAntichain` — the retained profile is unconditionally an antichain at the
  accreting witness: the habitat's own length strictly advances at every step.
* `memWidth_accreting_ge` — **the witness's lower bound**, unconditional in the environment: the
  accreting healer world's width is at least `2 ^ (t + 1)`.
* `memWidth_accreting_eq_of_trivialEnv` — **the witness's exact value** at a trivial environment,
  matching the certificate's own budget profile `κ = t + 1` exactly.
* `memWidth_accreting_log_eq_of_trivialEnv` — at that witness the width's bit form is exactly
  `t + 1`.
* `eventually_hosts_uniform_of_accreting_memWidth` — **the crossing, from the width**: a direct
  composition with `ALT.eventually_hosts_uniform`, no new content.

The width is a property of the presented world `(X, U, Ω)`; the general statements it is evaluated
from (`width_mono`, `width_eq_encard_of_isAntichain`) are in `ReachabilityWidth.lean`.
-/


@[expose] public section

namespace ALT

open Nonautonomous

variable {X : Type*}

open RealizabilityCCC
open FFL.FirstOrder FFL.FirstOrder.Arithmetic

/-- The habitat's block-list lengthens by exactly one at every accreting step. -/
private theorem accUpdate_length {ι_J : Type*} (k : ℕ) (π : Mem ι_J Bool → Mem ι_J Bool)
    (s : List (Mem (Fin (3 ^ k)) Bool) × Mem ι_J Bool) :
    (accUpdate k π s).1.length = s.1.length + 1 := by
  simp [accUpdate]

/-- Iterated: `n` accreting steps lengthen the habitat by exactly `n`. -/
private theorem accUpdate_iterate_length {ι_J : Type*} (k : ℕ) (π : Mem ι_J Bool → Mem ι_J Bool)
    (s : List (Mem (Fin (3 ^ k)) Bool) × Mem ι_J Bool) (n : ℕ) :
    ((accUpdate k π)^[n] s).1.length = s.1.length + n := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [Function.iterate_succ_apply', accUpdate_length, ih]
    omega

/-- **The retained profile is unconditionally an antichain at the accreting witness**: the
habitat's own length strictly advances at every step, so two DISTINCT classes admitted at the
SAME stage `t` (the same block-list length `t + 1`) can never be `Reaches`-related — reaching in
`j` steps would force the length to shift by `j`, so same-stage `Reaches` forces `j = 0`. -/
theorem mergeStage_accUpdate_isAntichain {ι_J : Type*} (k t : ℕ)
    (π : Mem ι_J Bool → Mem ι_J Bool) :
    IsAntichain (Reaches (accUpdate k π)) (mergeFiber (accUpdate k π) (accStage k) t) := by
  rintro _ ⟨s1, hs1, rfl⟩ _ ⟨s2, hs2, rfl⟩ hne ⟨j, hj⟩
  rw [mergeLaw_iterate_mergeMk] at hj
  obtain ⟨m, hm⟩ := Quotient.exact hj
  have hcomb : (accUpdate k π)^[m + j] s1 = (accUpdate k π)^[m] s2 := by
    rw [Function.iterate_add_apply]; exact hm
  have hlen := congrArg (fun s => s.1.length) hcomb
  simp only [accUpdate_iterate_length] at hlen
  have hs1' : s1.1.length = t + 1 := hs1
  have hs2' : s2.1.length = t + 1 := hs2
  have hj0 : j = 0 := by omega
  subst hj0
  simp only [add_zero] at hcomb
  exact hne (Quotient.sound ⟨m, hcomb⟩)

/-- The witness's extent, in `ℕ∞`: a cast of `ALT.ncard_guestStage_accRead`. -/
private theorem encard_guestStage_accRead (ι_J : Type*) (k t : ℕ) :
    (Nonautonomous.imageFiber (accRead (ι_J := ι_J) k) (accStage k) t).encard = 2 ^ (t + 1) := by
  have hn := ncard_guestStage_accRead ι_J k t
  have hfin := Set.finite_of_ncard_ne_zero (s :=
    Nonautonomous.imageFiber (accRead (ι_J := ι_J) k) (accStage k) t) (by rw [hn]; positivity)
  have hcast := Set.Finite.cast_ncard_eq hfin
  rw [hn] at hcast
  exact_mod_cast hcast.symm

/-- **The witness's lower bound, unconditional in the environment** ([Guests] §7 Theorem
7.9(iv), where `accStage k t` admits every length-`(t + 1)` habitat): the decoded-word
reading already
injects into the merge classes at stage `t` (`Nonautonomous.exists_mergeMk_injective`), giving at
least `2 ^ (t + 1)` of them, at every depth `k`, environment law `π` and environment type. -/
theorem memWidth_accreting_ge {ι_J : Type*} (k t : ℕ) (π : Mem ι_J Bool → Mem ι_J Bool) :
    (2 : ℕ∞) ^ (t + 1) ≤ width (accUpdate k π) (accStage k) t := by
  rw [width_eq_encard_of_isAntichain (mergeStage_accUpdate_isAntichain k t π)]
  obtain ⟨g, hgmem, hginj⟩ :=
    exists_mergeMk_injective accLaw_injective (advances_accUpdate k π) (stagedSquare_accRead k π) t
  have hle : (Nonautonomous.imageFiber (accRead (ι_J := ι_J) k) (accStage k) t).encard ≤
      (mergeFiber (accUpdate k π) (accStage k) t).encard :=
    Function.Embedding.encard_le ⟨fun m => ⟨g m, hgmem m⟩, fun m1 m2 heq =>
      hginj (by simpa using congrArg Subtype.val heq)⟩
  rw [← encard_guestStage_accRead ι_J k t]
  exact hle

/-- **The witness's exact value, at a trivial environment** ([Guests] §7 Theorem 7.9(iv), stated
at a trivial environment for the reason this module's own boundary note gives): two habitats
with the same decoded word heal, in one step, to the
identical state — `healWorld k x = encRec k (decRec k x)` by `healWorld`'s own definition, so the
healed block depends only on the decode — and at a trivial environment (`Mem Empty Bool`, a
one-element type) the environment component always agrees too, so the two habitats merge outright.
So the retained profile is, at this instance, exactly as large as the decoded-word extent: no
larger than `2 ^ (t + 1)` either, matching `memWidth_accreting_ge`'s lower bound with equality —
recovering the certificate's own budget profile `κ = t + 1` on the nose. A general environment can
exceed this (the module boundary note records why), so the restriction is load-bearing, not
cosmetic. -/
theorem memWidth_accreting_eq_of_trivialEnv (k t : ℕ) (π : Mem Empty Bool → Mem Empty Bool) :
    width (accUpdate k π) (accStage k) t = 2 ^ (t + 1) := by
  refine le_antisymm ?_ (memWidth_accreting_ge k t π)
  rw [width_eq_encard_of_isAntichain (mergeStage_accUpdate_isAntichain k t π),
    ← encard_guestStage_accRead Empty k t]
  classical
  choose s hsmem hseq using fun q : ↥(mergeFiber (accUpdate k π) (accStage k) t) => q.2
  refine Function.Embedding.encard_le ⟨fun q =>
    (⟨accRead k t (s q), s q, hsmem q, rfl⟩ :
      ↥(Nonautonomous.imageFiber (accRead (ι_J := Empty) k) (accStage k) t)), ?_⟩
  rintro q1 q2 heq
  have hread : accRead k t (s q1) = accRead k t (s q2) := congrArg Subtype.val heq
  have hheal : (s q1).1.map (healWorld k) = (s q2).1.map (healWorld k) := by
    have e1 : (s q1).1.map (healWorld k) = (accRead k t (s q1)).map (encRec k) := by
      simp [accRead, healWorld, List.map_map, Function.comp]
    have e2 : (s q2).1.map (healWorld k) = (accRead k t (s q2)).map (encRec k) := by
      simp [accRead, healWorld, List.map_map, Function.comp]
    rw [e1, e2, hread]
  have henv : (s q1).2 = (s q2).2 := Subsingleton.elim _ _
  have hstep : accUpdate k π (s q1) = accUpdate k π (s q2) := by
    simp only [accUpdate]; rw [hheal, henv]
  have hmerge : Merges (accUpdate k π) (s q1) (s q2) := ⟨1, by simpa using hstep⟩
  exact Subtype.ext (by rw [← hseq q1, ← hseq q2]; exact Quotient.sound hmerge)

/-! ## The crossing, from the width -/

/-- **The identification**: at the trivial-environment witness, the memory width's bit form —
`Nat.log 2` of the width — is EXACTLY the certificate's own budget profile `κ = t + 1`. -/
theorem memWidth_accreting_log_eq_of_trivialEnv (k t : ℕ) (π : Mem Empty Bool → Mem Empty Bool) :
    Nat.log 2 (width (accUpdate k π) (accStage k) t).toNat = t + 1 := by
  rw [memWidth_accreting_eq_of_trivialEnv]
  have h2 : ((2 : ℕ∞) ^ (t + 1)).toNat = 2 ^ (t + 1) := by
    rw [show ((2 : ℕ∞) = ((2 : ℕ) : ℕ∞)) from rfl, ← Nat.cast_pow, ENat.toNat_natCast]
  rw [h2]
  exact Nat.log_pow (by norm_num) (t + 1)

/-- **The crossing, from the width, at the trivial-environment witness** ([Guests] §7 Theorem
7.9(v)): the budget profile is the memory width's OWN bit form —
`memWidth_accreting_log_eq_of_trivialEnv` identifies it with `t + 1`, from which monotonicity and
unboundedness are trivial nat facts — and the crossing itself is a direct composition of
`ALT.eventually_hosts_uniform` at that profile: no further argument beyond the
identification. This is the sufficiency half of the certificate — see the module boundary note for
the ceiling half this does NOT recover. -/
theorem eventually_hosts_uniform_of_accreting_memWidth (k : ℕ)
    (π : Mem Empty Bool → Mem Empty Bool) :
    ∃ gTS, (∃ t₀, ∀ t, t₀ ≤ t → ALT.hostsAt
        (Nat.log 2 (width (accUpdate k π) (accStage k) t).toNat) gTS) ∧
      ∀ t Mchk, ALT.hostsAt
          (Nat.log 2 (width (accUpdate k π) (accStage k) t).toNat) gTS →
        gTS < Mchk → Mchk ≤ gTS ^ 2 →
        ∃ R : ReflectiveAsm gTS, R.depth = Mchk ∧
          ALT.FitsIn (recursorAsm R.depth)
            (Nat.log 2 (width (accUpdate k π) (accStage k) t).toNat) ∧
          ∃ M, ALT.RepresentsUnderivableTruth (Encodable.encode : Sentence ℒₒᵣ → ℕ)
            (fun δ => (𝗣𝗔⁻ : ArithmeticTheory) ⊢ δ) (fun δ => ℕ↓[ℒₒᵣ] ⊧ δ) M := by
  have hmono : Monotone (fun t => Nat.log 2 (width (accUpdate k π) (accStage k) t).toNat) := by
    intro a b hab
    simp only [memWidth_accreting_log_eq_of_trivialEnv]
    omega
  have hunb : ∀ N, ∃ t, N ≤ Nat.log 2 (width (accUpdate k π) (accStage k) t).toNat := by
    intro N
    refine ⟨N, ?_⟩
    rw [memWidth_accreting_log_eq_of_trivialEnv]
    omega
  exact ALT.eventually_hosts_uniform hmono hunb

end ALT

/-! ## Axiom audit

Every capstone above is `#print axioms`-clean on the standard triple, and the guards below make
that build-enforced. -/


/-- info: 'ALT.memWidth_accreting_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.memWidth_accreting_ge

set_option linter.style.longLine false in
/-- info: 'ALT.memWidth_accreting_eq_of_trivialEnv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.memWidth_accreting_eq_of_trivialEnv

set_option linter.style.longLine false in
/-- info: 'ALT.eventually_hosts_uniform_of_accreting_memWidth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.eventually_hosts_uniform_of_accreting_memWidth
