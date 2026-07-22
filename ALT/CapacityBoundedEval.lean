/-
Copyright (c) 2026 Mykola Palamarchuk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mykola Palamarchuk
-/
import ALT.TimeCost
import ALT.SearchSpace
import ALT.CheckerScratch

-- Formal-check file, not Mathlib-destined: opt out of the house-style header linter.
set_option linter.style.header false

/-!
# Capacity-bounded evaluation: the workspace bound laws for composition and pairing

Provenance: [Decoupling] §4.5 — the *capacity-bounded evaluation* lemma named there as the single
load-bearing step of Conjecture 4.4 (a general representation functor).

## Which half of the crux this is
[Decoupling] §4.5 states the crux as two clauses: the universal evaluator's application combinator
runs within the work memory `{0,1}^{|s_work|}`, **and** a capacity-respecting simulation transports
that realizer without overflowing the budget. This file supplies the **first clause only** — the
evaluator-side half: bound laws saying that a composite computation whose parts each fit a workspace
grade `S` itself fits a workspace grade computed from `S`. The transport clause quantifies over
simulation morphisms between decoupled learners, and no such morphism is defined in this
development; that half waits on that definition and is **not** discharged here. The crux is
therefore *half* discharged, not closed.

## The family
The workspace measure is `TimeCost.spaceCost` (total on the rfind'-free fragment) together with its
extension `TimeCost.spaceCostP` (total over all of `Nat.Partrec.Code`). Its bound laws form one
family, one member per constructor:
* `spaceCost_prec_le` — bounded recursion: a `max`, with the iteration count absent;
* `spaceCostP_rfind'_le` — unbounded search: a `max`, with the probe count absent;
* `spaceCost_comp_le` and `spaceCost_pair_le` — composition and pairing (**here**);
* `spaceCost_comp_within` — the grade-closure corollary (**here**).

The two composite laws need a fact the recursion and search laws did not: that a subcomputation's
*output* is no wider than the workspace it ran in. `comp` feeds one part's output to the other and
`pair` holds both outputs at once, so bounding a composite by its parts' grades is impossible
without it. That is the keystone `size_val_le_spaceCost`, with its unrestricted sibling
`size_valW_le` on all of `Nat.Partrec.Code`; both are proved first.

The keystone genuinely needs the `RfindFree` hypothesis: `spaceCost` leaves `rfind'` a placeholder
`0`, which no output bit-length bounds. The workspace evaluator `evalW` charges the search
honestly — the answer it forms is inside its `max` — so `size_valW_le` is unconditional.

## The grade arithmetic
Reading `S` as a capacity grade, the laws compute the grade of a composite from the grades of its
parts: composition is graded by `max S S'` and pairing by `2 * S`, the factor `2` being the price of
Cantor square pairing (`CheckerScratch.size_pair_le`, where the constant is attained). Grade closure
is then immediate where the two grades agree: **a realizer within grade `S` fed a value produced
within grade `S` runs within the `S`-bit workspace** (`spaceCost_comp_within`) — the "runs within
`{0,1}^{|s_work|}`" shape §4.5 asks for, with no growth across composition.

No grade *predicate* and no graded representation is introduced here: these are flat bound laws
about `spaceCost`. Packaging grades into a structure belongs with the graded category itself, and is
deliberately not taken on here.

## Boundary: the application combinator itself
`Realizability.universal_evaluator` — the code realizing the exponential's evaluation morphism
`[A ⇒ B] × A ⟶ B` — is produced by `Nat.Partrec.Code.exists_code` from a partial recursive function
that decodes its first argument (`Denumerable.ofNat Code`) and hands it to `Code.eval_part`. It is
an *existence* witness with no exposed constructor skeleton, so the laws below cannot be
instantiated at it: they price `comp`/`pair`/`prec`/`rfind'` structure, and this code has none that
the existence theorem reveals. Bounding the application combinator itself therefore needs a
*structurally presented* universal evaluator carrying its own workspace account — a separate
construction, not a corollary of this family.
-/

namespace TimeCost

open Nat.Partrec (Code)
open Nat.Partrec.Code

/-! ## The keystone: an output is no wider than the workspace that produced it -/

/-- **Outputs stay within grade.** The value a code computes never has more bits than the workspace
charged for computing it. Every clause of `spaceCost` accounts for the value formed at that node —
a base node maxes its input with its output, `pair` maxes in the bit-length of the pair it forms,
`comp` and bounded recursion inherit the account of the node that produced the result — so the
bound is structural, one case per constructor.

The `RfindFree` hypothesis is essential rather than incidental: `spaceCost` prices `rfind'` as the
placeholder `0`, and no output bit-length is bounded by `0`. The unrestricted statement is
`size_valW_le`, over the workspace evaluator that does charge the search. -/
theorem size_val_le_spaceCost :
    ∀ {c : Code}, RfindFree c → ∀ n, Nat.size (val c n) ≤ spaceCost c n := by
  intro c
  induction c with
  | zero => intro _ n; exact le_max_right (Nat.size n) (Nat.size 0)
  | succ => intro _ n; exact le_max_right (Nat.size n) (Nat.size (n + 1))
  | left => intro _ n; exact le_max_right (Nat.size n) (Nat.size n.unpair.1)
  | right => intro _ n; exact le_max_right (Nat.size n) (Nat.size n.unpair.2)
  | pair cf cg _ _ =>
      intro _ n
      rw [val_pair, spaceCost_pair]
      exact le_max_right _ _
  | comp cf cg ihf _ =>
      intro hc n
      obtain ⟨hf, _⟩ := hc
      rw [val_comp, spaceCost_comp]
      exact le_max_of_le_right (ihf hf (val cg n))
  | prec cf cg ihf ihg =>
      intro hc n
      obtain ⟨hf, hg⟩ := hc
      obtain ⟨a, m, rfl⟩ : ∃ a m, n = Nat.pair a m :=
        ⟨n.unpair.1, n.unpair.2, (Nat.pair_unpair n).symm⟩
      cases m with
      | zero =>
          rw [val_prec_zero, spaceCost_prec_zero]
          exact ihf hf a
      | succ k =>
          rw [val_prec_succ, spaceCost_prec_succ]
          exact le_max_of_le_right (ihg hg _)
  | rfind' cf _ => intro hc; exact hc.elim

/-- **Outputs stay within grade, on all of `Nat.Partrec.Code`.** The keystone without the
`RfindFree` restriction, stated over the workspace evaluator: whenever `evalW` returns a value and
a workspace, the value fits in that workspace. The `rfind'` case goes through precisely because the
search's account maxes in the bit-length of the answer it forms, exactly as `pair` does. -/
theorem size_valW_le : ∀ (c : Code) (n : ℕ), ∀ p ∈ evalW c n, Nat.size p.1 ≤ p.2 := by
  intro c
  induction c with
  | zero =>
      intro n p hp
      simp only [evalW, Part.mem_some_iff] at hp
      subst hp
      exact le_max_right _ _
  | succ =>
      intro n p hp
      simp only [evalW, Part.mem_some_iff] at hp
      subst hp
      exact le_max_right _ _
  | left =>
      intro n p hp
      simp only [evalW, Part.mem_some_iff] at hp
      subst hp
      exact le_max_right _ _
  | right =>
      intro n p hp
      simp only [evalW, Part.mem_some_iff] at hp
      subst hp
      exact le_max_right _ _
  | pair cf cg _ _ =>
      intro n p hp
      rw [evalW_pair, Part.mem_bind_iff] at hp
      obtain ⟨u, _, hp⟩ := hp
      rw [Part.mem_map_iff] at hp
      obtain ⟨v, _, rfl⟩ := hp
      exact le_max_right _ _
  | comp cf cg ihf _ =>
      intro n p hp
      rw [evalW_comp, Part.mem_bind_iff] at hp
      obtain ⟨q, _, hp⟩ := hp
      rw [Part.mem_map_iff] at hp
      obtain ⟨r, hr, rfl⟩ := hp
      exact le_max_of_le_right (ihf q.1 r hr)
  | prec cf cg ihf ihg =>
      intro n p hp
      obtain ⟨a, m, rfl⟩ : ∃ a m, n = Nat.pair a m :=
        ⟨n.unpair.1, n.unpair.2, (Nat.pair_unpair n).symm⟩
      cases m with
      | zero =>
          rw [evalW_prec_zero] at hp
          exact ihf a p hp
      | succ k =>
          rw [evalW_prec_succ, Part.mem_bind_iff] at hp
          obtain ⟨u, _, hp⟩ := hp
          rw [Part.mem_map_iff] at hp
          obtain ⟨q, hq, rfl⟩ := hp
          exact le_max_of_le_right (ihg _ q hq)
  | rfind' cf _ =>
      intro n p hp
      obtain ⟨a, m, rfl⟩ : ∃ a m, n = Nat.pair a m :=
        ⟨n.unpair.1, n.unpair.2, (Nat.pair_unpair n).symm⟩
      rw [evalW_rfind', Part.mem_bind_iff] at hp
      obtain ⟨k, _, hp⟩ := hp
      rw [Part.mem_map_iff] at hp
      obtain ⟨s, _, rfl⟩ := hp
      exact le_max_right _ _

/-! ## The composite bound laws -/

/-- **The composition law.** If `g` runs within `S` on `n`, and `f` runs within `S'` on every value
of at most `S` bits, then `comp f g` runs within `max S S'` on `n`.

The keystone is what makes the second hypothesis usable: `f` is applied to the value `g` produced,
and `size_val_le_spaceCost` is exactly the guarantee that this value is one of those `f` was assumed
to handle. Without it the hypothesis on `f` would have to be uniform over all inputs, which no space
measure can satisfy (a leaf node holds its input). -/
theorem spaceCost_comp_le {f g : Code} {n S S' : ℕ} (hg : RfindFree g)
    (hgn : spaceCost g n ≤ S) (hf : ∀ v, Nat.size v ≤ S → spaceCost f v ≤ S') :
    spaceCost (comp f g) n ≤ max S S' := by
  rw [spaceCost_comp]
  refine max_le (le_trans hgn (le_max_left _ _)) (le_trans ?_ (le_max_right _ _))
  exact hf (val g n) (le_trans (size_val_le_spaceCost hg n) hgn)

/-- **The pairing law.** If both components run within `S` on `n`, then `pair f g` runs within
`2 * S`. The factor `2` is not slack in the argument but the price of the packing: `Nat.pair` is
Cantor square pairing, whose result can be twice as wide as its wider component
(`CheckerScratch.size_pair_le`, with the constant attained at `Nat.pair 1 0`). The two
sub-workspaces themselves contribute only `S`; the doubling is entirely the cost of *holding the
pair*. -/
theorem spaceCost_pair_le {f g : Code} {n S : ℕ} (hf : RfindFree f) (hg : RfindFree g)
    (hfn : spaceCost f n ≤ S) (hgn : spaceCost g n ≤ S) :
    spaceCost (pair f g) n ≤ 2 * S := by
  rw [spaceCost_pair]
  refine max_le (max_le (by omega) (by omega)) ?_
  have hp := CheckerScratch.size_pair_le (val f n) (val g n)
  have hmax : max (Nat.size (val f n)) (Nat.size (val g n)) ≤ S :=
    max_le (le_trans (size_val_le_spaceCost hf n) hfn)
      (le_trans (size_val_le_spaceCost hg n) hgn)
  omega

/-! ## Grade closure — the "runs within the workspace" shape -/

/-- **Capacity-bounded evaluation, evaluator side ([Decoupling] §4.5).** Grade closure for
composition: if `g` runs within the `S`-bit workspace, and `f` runs within the `S`-bit workspace on
every value of at most `S` bits, then the composite runs within the `S`-bit workspace — the grade
does not grow. This is the `{0,1}^{|s_work|}` clause of Conjecture 4.4's crux at the concrete
carrier: evaluation of a realizer within capacity, on data within capacity, stays within capacity.

Immediate from `spaceCost_comp_le` at `S' = S`, the composite grade `max S S'` collapsing to `S`.
The transport clause of the crux — that a capacity-respecting simulation carries realizers across
without overflowing the budget — is a statement about simulation morphisms, which this development
does not define; it is not established here. -/
theorem spaceCost_comp_within {f g : Code} {n S : ℕ} (hg : RfindFree g)
    (hgn : spaceCost g n ≤ S) (hf : ∀ v, Nat.size v ≤ S → spaceCost f v ≤ S) :
    spaceCost (comp f g) n ≤ S := by
  have h := spaceCost_comp_le hg hgn hf
  rwa [max_self] at h

end TimeCost
