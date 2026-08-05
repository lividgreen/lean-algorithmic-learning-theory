/-
Copyright (c) 2026 Mykola Palamarchuk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mykola Palamarchuk
-/
import Foundation.FirstOrder.Incompleteness.Examples
import Foundation.FirstOrder.Bootstrapping.DerivabilityCondition.D1
import ALT.GodelCore

-- Formal-check file, not Mathlib-destined: opt out of the house-style linters.
set_option linter.style.header false
set_option linter.style.longLine false

/-!
# A SOUND-AND-COMPLETE bounded proof relation over Foundation ([Decoupling] §6.3)

Provenance: [Decoupling] §6.3 (Theorem 6.3, Level L2b) — the
strengthening flagged there as the "research-grade, non-load-bearing refinement": a
decision morphism that decides bounded `T`-non-provability for *arbitrary* `φ`, not merely the
soundness-only verdict on `G` of `ALT/GodelChecker.lean`.

## Why this is the genuine "decides" (not the sound-only checker)
`ALT/GodelChecker.lean` builds a *concrete Hilbert (ax+MP) checker* and proves it **sound**; its
`Decide(G)=true` then rides on soundness + the imported Gödel unprovability. That is honest but
weak: a sound-only checker cannot certify "no bounded proof EXISTS", only "this checker found none".
The completeness direction was open because Foundation's `⊢` is a **Tait sequent calculus**, with no
Hilbert↔Tait completeness theorem to make an `(ax, mp)` script checker complete.

This file takes the faithful route: it uses Foundation's **own arithmetized proof relation**
`Bootstrapping.Proof T d φ` ("`d` is the Gödel number of a `T`-derivation of `φ`"), which is by
construction the *real* proof relation — hence **sound AND complete** for `T ⊢` (no metatheory to
re-prove):
* SOUND   — `Prf_sound`  : `Bootstrapping.Provable.sound` (`Coding.lean:336`), accept ⇒ `T ⊢ φ`;
* COMPLETE — `Prf_complete`: `internalize_provability` (`D1.lean:24`), `T ⊢ φ` ⇒ accept at some code.

So the decision morphism `Decide T M φ = ⋀_{p ≤ M} ¬Prf(φ,p)` satisfies the GENUINE property
`Decide T M φ = true ↔ no T-proof of φ has Gödel number ≤ M` (`decide_correct`): a *sound and
complete* decision of bounded `T`-provability. `Decide(G)=true` (`paMinus_complete_decides`) is then
a correct verdict whose completeness is real, and a bounded proof would force `Decide = false`
(`decide_false_of_bounded_proof`). This is the precise sense in which Rep(S) **decides** — not
merely soundly approximates — bounded non-provability.

## Decidability / what `noncomputable` means here
Foundation ships **no** `Decidable (Bootstrapping.Proof T d φ)` instance, so `Decide` is packaged classically
(`open Classical`) — it carries only `Classical.choice`, already in the accepted axiom set. This is
not a gap: `Theory.proof` is a `𝚫₁.Semisentence 2` (`Proof/Basic.lean`), i.e. the relation is `Δ₁`
(primitive recursive), so a genuine decision *algorithm* exists; the Lean term simply does not
`#eval`. The morphism's EXISTENCE as a total Boolean function — all Rep(S) needs (§4.1) — is what is
certified.

## The computable-AND-complete decider: a documented WALL
Merging FV-8's *computable* checker (`GodelChecker.Prf`, which `#eval`s but is incomplete) with this
file's *complete* decision (`Decide`, over `Bootstrapping.Proof`, but `noncomputable`) into ONE
computable-and-complete bounded decider is **walled**; first probed against Foundation rev
`b47cf447` on Lean 4.31, and the wall stands at every pin since. The two probe routes and their
precise gaps:

* **(a) reflection over the arithmetized predicate.** `Bootstrapping.Proof T p (⌜φ⌝)` unfolds to
  `DerivationOf`, a **`noncomputable` Δ₁ FIXPOINT** — `Derivation T := (construction T).Fixpoint ![]`
  (`Bootstrapping/Syntax/Proof/Basic.lean:459`) — over coded one-sided-sequent (`𝐋𝐊¹`) derivations
  (`fstIdx`, `^⋏`/`^⋎`/`^∀`/`^∃`, `free`, `setShift`, `substs1`, `IsTerm`, coded-set membership).
  Foundation exposes it ONLY as a `𝚫₁-Relation[V]` (a defining `𝚫₁.Semisentence`); it ships **no**
  `Decidable`/`Primrec`/`Computable`/`Bool` instance. Making `Decide` `#eval` would require a new
  executable `Bool` evaluator for that fixpoint + a proof it agrees with `DerivationOf` — i.e. porting
  Foundation's whole coded-derivation checker to executable Lean.
* **(b) complete computable Hilbert checker.** Extending FV-8's Hilbert (ax+MP) checker to a COMPLETE
  one has **no** Foundation completeness bridge: classical first-order `⊢` is the sequent calculus
  `𝐋𝐊¹` (`FirstOrder/Basic/Calculus.lean`), and Foundation exposes **no** classical Hilbert-vs-`𝐋𝐊¹`
  equivalence (its only first-order Hilbert object, `HilbertProofᵢ` in `Hauptsatz.lean`, is
  *intuitionistic* and internal to cut-elimination). `𝗣𝗔⁻`'s finiteness makes non-logical axiom
  recognition trivially decidable, but leaves the *logical*-completeness bottleneck (a complete FO
  Hilbert calculus + the bridge to `𝐋𝐊¹`) untouched.

Precise missing decidability: `Decidable (Bootstrapping.Proof 𝗣𝗔⁻ p (⌜φ⌝))` over `V = ℕ` (an
executable evaluator for the `DerivationOf` fixpoint). This wall is **non-load-bearing** — the §6.3 verdict
`Decide(G) = true` needs only FV-8's soundness + the imported Gödel unprovability
(`GodelChecker.paMinus_decides_bounded_nonprovability`) — so it closes as a **documented wall +
registered upstream follow-on** (a `Decidable`/`Primrec (Bootstrapping.Proof …)` instance, or an
executable complete derivation checker, in Foundation; upstream-PR targets).

## Witness theory and axioms
`paMinus_complete_decides` at `T★ = 𝗣𝗔⁻` (`PeanoMinus`) — **fully axiom-clean** (`#print axioms` =
`propext, Classical.choice, Quot.sound`); `Δ₁` via `Theory.Δ₁.ofFinite`. The parallel `𝗜𝚺₁` witness
`isigma1_complete_decides` (the same statement at `𝗜𝚺₁`) is **also fully axiom-clean**: Foundation's
`𝗜𝚺₁.Δ₁` definability is a *theorem* (`ISigma1_delta1Definable`, discharged upstream), so it carries
no named axiom either. `𝗣𝗔⁻ ⊊ 𝗜𝚺₁`, so the `𝗣𝗔⁻` capstone is the weaker, more faithful (§5.3-class)
statement, and the `𝗜𝚺₁` form is the parallel witness at Foundation's canonical Σ₁-induction theory.
-/

namespace GodelCheckerComplete

open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping

/-- Sentences of the language of ordered rings — the `Formula` object of §6.3. -/
abbrev S : Type := Sentence ℒₒᵣ

/-- The Gödel number of a sentence — the `Encodable` code, hence **computable**. It agrees with
Foundation's quotation `⌜·⌝` at the standard model: `gnum_eq_quote`. -/
abbrev gnum (φ : S) : ℕ := Encodable.encode φ

/-- The two Gödel numberings agree at `V = ℕ`: the `Encodable` code of a sentence *is* its
Foundation quotation. So `gnum` may be used wherever `(⌜·⌝ : ℕ)` is expected, and the switch to the
computable definition costs nothing. -/
theorem gnum_eq_quote (φ : S) : gnum φ = (⌜φ⌝ : ℕ) := by
  simp [gnum, Sentence.quote_eq_encode]

/-- §6.3 L2b — the bounded proof relation, **complete form**: `p` codes a genuine `T`-derivation of
`φ`. This is Foundation's real arithmetized proof predicate `Bootstrapping.Proof`, NOT a hand-rolled
checker — so it is sound and complete for `T ⊢` by construction. -/
def Prf (T : ArithmeticTheory) [T.Δ₁] (φ : S) (p : ℕ) : Prop := Bootstrapping.Proof T p (⌜φ⌝ : ℕ)

/-- SOUNDNESS (accept ⇒ provable): `Theory.Provable.sound`. -/
theorem Prf_sound (T : ArithmeticTheory) [T.Δ₁] {φ : S} {p : ℕ} (h : Prf T φ p) : T ⊢ φ :=
  Bootstrapping.Provable.sound ⟨p, (h : Bootstrapping.Proof T p (⌜φ⌝ : ℕ))⟩

/-- COMPLETENESS (provable ⇒ accepted at some code): `internalize_provability`. This is the direction
the Hilbert (ax+MP) checker of `GodelChecker.lean` cannot supply. -/
theorem Prf_complete (T : ArithmeticTheory) [T.Δ₁] {φ : S} (h : T ⊢ φ) : ∃ p, Prf T φ p := by
  obtain ⟨d, hd⟩ := internalize_provability (V := ℕ) h
  exact ⟨d, hd⟩

/-- §6.3 L2b — the decision morphism `Decide(φ) = ⋀_{p ≤ M} ¬Prf(φ, p)`, total (classical
`Decidable`; the relation is `Δ₁` hence decidable in principle — see module note). -/
noncomputable def Decide (T : ArithmeticTheory) [T.Δ₁] (M : ℕ) (φ : S) : Bool := by
  classical exact decide (∀ p ≤ M, ¬ Prf T φ p)

theorem decide_eq_true_iff (T : ArithmeticTheory) [T.Δ₁] (M : ℕ) (φ : S) :
    Decide T M φ = true ↔ ∀ p ≤ M, ¬ Prf T φ p := by
  classical simp [Decide]

/-- **The genuine decision (sound AND complete for the bound).** Because `Prf = T.Proof` is the real
proof relation, `Decide(φ) = true` is *equivalent* to "no `T`-proof of `φ` has Gödel number `≤ M`" —
not a one-sided over-approximation. This is what licenses the word "decides" in §6.3 L2b. -/
theorem decide_correct (T : ArithmeticTheory) [T.Δ₁] (M : ℕ) (φ : S) :
    Decide T M φ = true ↔ ¬ ∃ p ≤ M, Bootstrapping.Proof T p (⌜φ⌝ : ℕ) := by
  rw [decide_eq_true_iff]
  constructor
  · rintro h ⟨p, hp, hpf⟩; exact h p hp hpf
  · intro h p hp hpf; exact h ⟨p, hp, hpf⟩

/-- **Completeness witness.** A genuine bounded proof forces `Decide = false`: the checker cannot
miss a real proof within budget. (Contrast the sound-only checker, where rejection means only "not
found".) -/
theorem decide_false_of_bounded_proof (T : ArithmeticTheory) [T.Δ₁] (M : ℕ) (φ : S)
    {p : ℕ} (hp : p ≤ M) (h : Bootstrapping.Proof T p (⌜φ⌝ : ℕ)) : Decide T M φ = false := by
  rw [Bool.eq_false_iff]; intro hcon
  exact (decide_eq_true_iff T M φ).mp hcon p hp h

/-! ### Soundness and completeness are load-bearing (not a self-deciding tautology)

`decide_correct` alone is near-definitional (`decide P = true ↔ P`). The two corollaries below make
the *content* explicit — that `Prf = T.Proof` is the genuine, sound *and* complete proof relation:
a **negative** verdict witnesses real `T ⊢ φ` provability (soundness, `provable_of_decide_false`,
uses `Prf_sound`), and `Decide` is **not** trivially always-`true` — every provable sentence is
rejected at a large enough budget (completeness/non-vacuity, `decide_false_of_provable`, uses
`Prf_complete`). So both directions of the proof relation carry weight in the decision. -/

/-- **Soundness is load-bearing.** A *negative* verdict is not merely "the checker failed to find a
proof": by `Prf_sound` it witnesses genuine `T`-provability — if `Decide` rejects `φ` within budget
`M`, some in-budget code is a real `T`-proof, so `T ⊢ φ`. -/
theorem provable_of_decide_false (T : ArithmeticTheory) [T.Δ₁] (M : ℕ) (φ : S)
    (h : Decide T M φ = false) : T ⊢ φ := by
  by_contra hcon
  refine absurd ?_ (by simp [h] : ¬ (Decide T M φ = true))
  rw [decide_eq_true_iff]
  intro p _ hpf
  exact hcon (Prf_sound T hpf)

/-- **Completeness is load-bearing (non-vacuity).** `Decide` is not the trivial always-`true`
function: every `T`-provable `φ` is *rejected* at a large enough budget. `Prf_complete` supplies a
proof code `p`, and `decide_false_of_bounded_proof` flips the verdict at `M = p`. -/
theorem decide_false_of_provable (T : ArithmeticTheory) [T.Δ₁] {φ : S} (h : T ⊢ φ) :
    ∃ M, Decide T M φ = false := by
  obtain ⟨p, hp⟩ := Prf_complete T h
  exact ⟨p, decide_false_of_bounded_proof T p φ (le_refl p) hp⟩

/-- Concrete non-vacuity: `⊤` (provable via `verum!`) is decided `false` at some budget, so `Decide`
genuinely distinguishes provable from unprovable sentences. -/
theorem decide_nonvacuous (T : ArithmeticTheory) [T.Δ₁] : ∃ M, Decide T M (⊤ : S) = false :=
  decide_false_of_provable T LO.Entailment.verum!

/-! ### Capstones — §6.3 L2b for the real Gödel sentence, now a complete decision -/

/-- `𝗣𝗔⁻` is `Δ₁`-definable: it is a finite theory, and a finite theory's axiom
set is decidable outright. This is what lets the capstones below instantiate the
general checker at `𝗣𝗔⁻`. -/
noncomputable local instance : (𝗣𝗔⁻ : ArithmeticTheory).Δ₁ :=
  Theory.Δ₁.ofFinite 𝗣𝗔⁻ PeanoMinus.finite

/-- **§6.3 Theorem 6.3, L2b — complete, FULLY axiom-clean.** For `T★ = 𝗣𝗔⁻`, the real Gödel
sentence `G` (true in `ℕ`, unprovable in `𝗣𝗔⁻`) is decided as bounded-non-provable by the
**sound-and-complete** decision morphism, for every budget `M`. By `decide_correct`, `Decide G =
true` is the *correct* verdict (no `𝗣𝗔⁻`-proof of `G` of code `≤ M` exists — indeed none of any
length); by `decide_false_of_bounded_proof` a bounded proof would have flipped it. `#print axioms` =
`propext, Classical.choice, Quot.sound`. -/
theorem paMinus_complete_decides (M : ℕ) :
    ∃ G : S, (ℕ↓[ℒₒᵣ] ⊧ G) ∧ ((𝗣𝗔⁻ : ArithmeticTheory) ⊬ G) ∧ Decide 𝗣𝗔⁻ M G = true := by
  obtain ⟨G, htrue, hunprov⟩ := exists_true_but_unprovable_sentence 𝗣𝗔⁻
  refine ⟨G, htrue, hunprov, ?_⟩
  rw [decide_eq_true_iff]
  intro p _ hpf
  exact hunprov (Prf_sound 𝗣𝗔⁻ hpf)

/-- **§6.3 Theorem 6.3, L2b — complete, for the real `𝗜𝚺₁` Gödel sentence.** The `𝗜𝚺₁` counterpart of
`paMinus_complete_decides`: the real Gödel sentence `G` of `𝗜𝚺₁` (true in `ℕ`, unprovable in `𝗜𝚺₁`)
is decided as bounded-non-provable by the **sound-and-complete** decision morphism, for every budget
`M`. Foundation's `𝗜𝚺₁.Δ₁` instance is a *theorem* (`ISigma1_delta1Definable`, discharged upstream),
so this witness is **fully axiom-clean**: `#print axioms` = `propext, Classical.choice, Quot.sound`.
`𝗣𝗔⁻ ⊊ 𝗜𝚺₁`, so `paMinus_complete_decides` above is the weaker, more faithful (§5.3-class)
statement. -/
theorem isigma1_complete_decides (M : ℕ) :
    ∃ G : S, (ℕ↓[ℒₒᵣ] ⊧ G) ∧ ((𝗜𝚺₁ : ArithmeticTheory) ⊬ G) ∧ Decide 𝗜𝚺₁ M G = true := by
  obtain ⟨G, htrue, hunprov⟩ := exists_true_but_unprovable_sentence 𝗜𝚺₁
  refine ⟨G, htrue, hunprov, ?_⟩
  rw [decide_eq_true_iff]
  intro p _ hpf
  exact hunprov (Prf_sound 𝗜𝚺₁ hpf)

end GodelCheckerComplete
