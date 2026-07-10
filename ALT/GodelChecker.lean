/-
Copyright (c) 2026 Mykola Palamarchuk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mykola Palamarchuk
-/
import Foundation.FirstOrder.Incompleteness.Examples
import ALT.GodelCore
import ALT.GodelComplete

-- Formal-check file, not Mathlib-destined: opt out of the house-style linters.
set_option linter.style.header false
set_option linter.style.longLine false

/-!
# A concrete sound bounded proof-checker over Foundation (Paper I §6.3, the Level-2 witness)

Provenance: Paper I §6.3 (Theorem 6.3, Levels L2a/L2b). This
discharges the abstract `BoundedChecker` interface of `ALT/GodelInternalization.lean` (FV-8)
with a **concrete decidable sound checker** over Foundation's `Sentence ℒₒᵣ`, so the L2b
decision `Decide(G) = true` holds for a **real** Gödel sentence.

**Opt-in / NOT wired into root `ALT.lean`** (like `ALT/GodelComplete.lean`): build with
`lake build ALT.GodelChecker`.

## Why this lives on the Foundation side (the import divide, again)
The Mathlib-side `BoundedChecker`/`Decide`/`decide_godel` live behind the `import Mathlib` umbrella, whose
`Matrix.map` collides with `Foundation.Vorspiel.Matrix`'s root `Matrix.map`. So a concrete checker
over Foundation's `Sentence ℒₒᵣ` cannot literally instantiate that structure in one file; we
re-prove the (tiny) L2b decision step here directly — exactly the architecture `GodelComplete.lean`
already uses for the incompleteness import. The checker below provides, concretely, every field of
`BoundedChecker`: `Formula := Sentence ℒₒᵣ`, `gnum := Encodable.encode`, `Derivable := (T ⊢ ·)`,
the decidable `Prf`, and the **soundness** `Prf φ p = true → T ⊢ φ` (`Prf_sound`).

## The checker (faithful, NOT degenerate)
A proof code decodes (via `Encodable`) to a `List Step`, a Hilbert-style script over a fixed,
decidable, **provable** axiom list `Ax`:
* `Step.ax c`     — assert `c`, valid iff `c ∈ Ax` (decidable);
* `Step.mp i j b` — modus ponens: valid iff line `i` is `line j 🡒 b` (decidable equality).
`run` folds a script into the list of proven formulas (or `none` on any invalid step); `Prf Ax φ p`
accepts iff the decoded script is valid and proves `φ`. **Soundness** (`Prf_sound`): every accepted
formula is genuinely `T`-provable (`ax` via `Axiomatized.provable_axm`, `mp` via `mdp!`). This is
the forward direction §6.3 L2b needs; we do NOT claim completeness, nor a degenerate
always-`false` checker (`Prf_accepts` exhibits a real accepted proof — non-degeneracy).

## Witness theory and axioms
The checker + soundness are **generic** over any `T : ArithmeticTheory` (axiom-clean). The capstone
instantiates it at `T★ = 𝗣𝗔⁻` (`PeanoMinus`) — `paMinus_decides_bounded_nonprovability`, **fully
axiom-clean** (`#print axioms` = `propext, Classical.choice, Quot.sound`). `𝗣𝗔⁻` is a *finite*
theory, so its `Δ₁`-definability is constructed from `Theory.Δ₁.ofFinite PeanoMinus.finite` with no
named axiom. This is the recommended witness. The earlier obstruction (no `Δ₁` instance
for `𝗥₀`/`𝗤`, both infinite via the `𝗘𝗤` schema) is sidestepped because `𝗣𝗔⁻` — though it extends
`𝗥₀` — is itself finite.

An earlier `𝗜𝚺₁` variant (`isigma1_decides_bounded_nonprovability'`, same statement at `T = 𝗜𝚺₁`)
was **retired**: it carried Foundation's single named axiom `ISigma1_delta1Definable`
(its own Δ₁ TODO), whereas the whole development is now zero-named-axiom. `𝗣𝗔⁻ ⊊ 𝗜𝚺₁`, so the `𝗣𝗔⁻`
capstone is the weaker, more faithful (§5.3-class) statement; restore the `𝗜𝚺₁` form from git history
if upstream proves `ISigma1_delta1Definable` (an upstream-PR target).

## Computable but INCOMPLETE (the other half of the wall)
This checker is **computable** (`Prf` `#eval`s — see `prf_nondegenerate`/`prf_accepts_mp`) but
**incomplete**: it is a Hilbert (ax+MP) script checker over a *fixed finite* axiom list, whereas
Foundation's classical first-order `⊢` is the one-sided sequent calculus `𝐋𝐊¹`, with no exposed
Hilbert-vs-`𝐋𝐊¹` completeness bridge. `ALT/GodelCheckerComplete.lean` (FV-9) supplies the dual —
sound AND complete, but `noncomputable`. Merging the two into a single computable-and-complete bounded
decider is a **documented WALL**; the precise missing object is a runnable
`Decidable`/`Bool` form of Foundation's `noncomputable` Δ₁-fixpoint proof predicate
`Bootstrapping.Proof` — see the wall section of `GodelCheckerComplete.lean` for the full statement.
Non-load-bearing: the §6.3 verdict needs only this checker's soundness.
-/

namespace GodelChecker

open LO LO.Entailment LO.FirstOrder LO.FirstOrder.Arithmetic

/-- Sentences of the language of ordered rings — the `Formula` object of §6.3 (abstractly; the L2a
finite carving is `Formula` below). -/
abbrev S : Type := Sentence ℒₒᵣ

/-- A single proof-script step (§6.3 L2b, the bounded checker's instruction set): assert an axiom,
apply modus ponens. `mp i j b` stores the conclusion `b` explicitly so validity is a decidable
equality `line i = (line j 🡒 b)` — no implication-destructuring needed. -/
inductive Step
  | ax (c : S)
  | mp (i j : ℕ) (b : S)

/-- `Step ≃ S ⊕ (ℕ × ℕ × S)`, giving `Encodable Step` from Foundation's `Encodable S`. -/
def stepEquiv : Step ≃ S ⊕ (ℕ × ℕ × S) where
  toFun
    | .ax c => .inl c
    | .mp i j b => .inr (i, j, b)
  invFun
    | .inl c => .ax c
    | .inr (i, j, b) => .mp i j b
  left_inv := by rintro (_ | _) <;> rfl
  right_inv := by rintro (_ | ⟨_, _, _⟩) <;> rfl

instance : Encodable Step := Encodable.ofEquiv _ stepEquiv

/-- Validate one step against the axiom list `Ax` and the formulas `proven` so far; returns the
proven formula, or `none` if the step is invalid. -/
def checkStep (Ax : List S) (proven : List S) : Step → Option S
  | .ax c => if c ∈ Ax then some c else none
  | .mp i j b =>
      match proven[i]?, proven[j]? with
      | some pi, some pj => if pi = pj 🡒 b then some b else none
      | _, _ => none

/-- Fold a script left-to-right, threading the list of proven formulas; `none` if any step fails. -/
def runAux (Ax : List S) : List Step → List S → Option (List S)
  | [], acc => some acc
  | st :: rest, acc =>
      match checkStep Ax acc st with
      | some φ => runAux Ax rest (acc ++ [φ])
      | none => none

/-- Run a proof script from the empty context. -/
def run (Ax : List S) (steps : List Step) : Option (List S) := runAux Ax steps []

/-- §6.3 L2b — the concrete bounded proof relation `Prf : Formula → ProofCode → Bool`. `Prf Ax φ p`
decodes the code `p` to a script and accepts iff the script is valid and proves `φ`. Decidable and
total. -/
def Prf (Ax : List S) (φ : S) (p : ℕ) : Bool :=
  match (Encodable.decode p : Option (List Step)) with
  | some steps =>
      match run Ax steps with
      | some proven => decide (φ ∈ proven)
      | none => false
  | none => false

/-! ### Soundness: every accepted formula is genuinely `T`-provable -/

/-- Core soundness invariant: if every formula already in `acc` is `T`-provable and the script runs
to `proven`, then every formula in `proven` is `T`-provable. By induction on the script — `ax` via
`Axiomatized.provable_axm`, `mp` via `mdp!`. -/
theorem runAux_sound (T : ArithmeticTheory) (Ax : List S) (hAx : ∀ c ∈ Ax, T ⊢ c) :
    ∀ (steps : List Step) (acc proven : List S), (∀ ψ ∈ acc, T ⊢ ψ) →
      runAux Ax steps acc = some proven → ∀ ψ ∈ proven, T ⊢ ψ := by
  intro steps
  induction steps with
  | nil =>
      intro acc proven hacc h
      simp only [runAux, Option.some.injEq] at h
      subst h; exact hacc
  | cons st rest ih =>
      intro acc proven hacc h
      simp only [runAux] at h
      -- The step must succeed for the run to continue.
      cases hcs : checkStep Ax acc st with
      | none => rw [hcs] at h; exact absurd h (by simp)
      | some φ =>
          rw [hcs] at h
          have hφ : T ⊢ φ := by
            cases st with
            | ax c =>
                simp only [checkStep] at hcs
                by_cases hc : c ∈ Ax
                · simp only [hc, if_true, Option.some.injEq] at hcs
                  subst hcs; exact hAx c hc
                · simp only [hc, if_false, reduceCtorEq] at hcs
            | mp i j b =>
                simp only [checkStep] at hcs
                split at hcs
                · -- some pi, some pj
                  rename_i pi pj hi hj
                  split at hcs
                  · rename_i hpe
                    rw [Option.some.injEq] at hcs
                    rw [← hcs]
                    have hpi : T ⊢ pj 🡒 b := hpe ▸ hacc pi (List.mem_of_getElem? hi)
                    have hpj : T ⊢ pj := hacc pj (List.mem_of_getElem? hj)
                    exact LO.Entailment.mdp! hpi hpj
                  · exact absurd hcs (by simp)
                · exact absurd hcs (by simp)
          exact ih (acc ++ [φ]) proven (by
            intro ψ hψ
            rcases List.mem_append.mp hψ with h1 | h1
            · exact hacc ψ h1
            · simp only [List.mem_singleton] at h1; subst h1; exact hφ) h

/-- §6.3 L2b soundness: `Prf Ax φ p = true → T ⊢ φ` — the `BoundedChecker.sound` field, concretely.
The only direction the decision needs. -/
theorem Prf_sound (T : ArithmeticTheory) (Ax : List S) (hAx : ∀ c ∈ Ax, T ⊢ c)
    (φ : S) (p : ℕ) : Prf Ax φ p = true → T ⊢ φ := by
  intro h
  simp only [Prf] at h
  split at h
  · rename_i steps _
    split at h
    · rename_i proven hrun
      have hmem : φ ∈ proven := by simpa using h
      exact runAux_sound T Ax hAx steps [] proven (by simp) hrun φ hmem
    · simp at h
  · simp at h

/-! ### Non-degeneracy: the checker accepts a genuine proof -/

/-- If a script `steps` validly proves `φ` (under `Ax`), then `Prf` accepts its code. Via
`Encodable.encodek` (`decode (encode steps) = some steps`), avoiding any heavy `decide` on the
encoding. Shows the checker is NOT the degenerate always-`false` one. -/
theorem Prf_accepts (Ax : List S) (steps : List Step) (φ : S) (proven : List S)
    (hrun : run Ax steps = some proven) (hmem : φ ∈ proven) :
    Prf Ax φ (Encodable.encode steps) = true := by
  simp only [Prf, Encodable.encodek, hrun]
  simpa using hmem

/-! ### Capstone — L2b for the real `𝗣𝗔⁻` Gödel sentence -/

/-- **§6.3 Theorem 6.3, L2b — concrete, FULLY axiom-clean.** With witness theory `T★ = 𝗣𝗔⁻`
(`PeanoMinus`). Because `𝗣𝗔⁻` is a *finite* theory (`PeanoMinus.finite`), its `Δ₁`-definability
is obtained constructively from `Theory.Δ₁.ofFinite` — with **no** appeal to Foundation's named
`ISigma1_delta1Definable` axiom (the `𝗜𝚺₁` variant that once accompanied this capstone is retired). So the **actual** Gödel sentence `G` of `𝗣𝗔⁻` (true in `ℕ`,
unprovable in `𝗣𝗔⁻`) is decided as bounded-non-provable for the concrete sound checker over any
provable axiom `Ax`, and `#print axioms` shows only `propext, Classical.choice, Quot.sound`.

`𝗣𝗔⁻ ⊊ 𝗜𝚺₁`, so unprovability in `𝗣𝗔⁻` is the *weaker* (and thus more faithful, §5.3-class)
statement; the three incompleteness instances are `𝗣𝗔⁻.Δ₁` (here, via `ofFinite`), `𝗥₀ ⪯ 𝗣𝗔⁻`
(`PeanoMinus/Basic.lean:352`), and `ℕ↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻` (`PeanoMinus/Basic.lean:140`). -/
theorem paMinus_decides_bounded_nonprovability
    (Ax : List S) (hAx : ∀ c ∈ Ax, (𝗣𝗔⁻ : ArithmeticTheory) ⊢ c) (Mchk : ℕ) :
    ∃ G : S, (ℕ↓[ℒₒᵣ] ⊧ G) ∧ ((𝗣𝗔⁻ : ArithmeticTheory) ⊬ G) ∧
      ∀ p, p ≤ Mchk → Prf Ax G p = false := by
  haveI : (𝗣𝗔⁻ : ArithmeticTheory).Δ₁ := Theory.Δ₁.ofFinite 𝗣𝗔⁻ PeanoMinus.finite
  obtain ⟨δ, htrue, hunprov⟩ := exists_true_but_unprovable_sentence 𝗣𝗔⁻
  refine ⟨δ, htrue, hunprov, fun p _ => ?_⟩
  by_contra h
  rw [Bool.not_eq_false] at h
  exact hunprov (Prf_sound 𝗣𝗔⁻ Ax hAx δ p h)

/-- The singleton axiom list `[⊤]` is genuinely `𝗜𝚺₁`-provable (`verum!`), so it is a legitimate
axiom set for the capstone — the checker is sound over a NON-empty, real axiom set. -/
theorem topAx_provable : ∀ c ∈ [(⊤ : S)], (𝗜𝚺₁ : ArithmeticTheory) ⊢ c := by
  intro c hc
  simp only [List.mem_singleton] at hc
  subst hc
  exact LO.Entailment.verum!

/-- **Non-degeneracy.** The checker accepts a genuine proof: the one-line script `[Step.ax ⊤]`
proves `⊤` under the axiom set `[⊤]`, so `Prf` returns `true` on its code. Hence `Prf` is NOT the
degenerate always-`false` checker, and `Decide(⊤)` would correctly be `false` (a bounded proof
exists). Combined with `topAx_provable`, the axiom set is real and provable. -/
theorem prf_nondegenerate :
    Prf [(⊤ : S)] (⊤ : S) (Encodable.encode [Step.ax (⊤ : S)]) = true :=
  Prf_accepts [(⊤ : S)] [Step.ax (⊤ : S)] ⊤ [⊤]
    (by simp [run, runAux, checkStep]) (by simp)

/-- The axiom set `[⊤🡒⊤, ⊤]` is genuinely `𝗜𝚺₁`-provable (`C!_id` for `⊤🡒⊤`, `verum!` for `⊤`):
a real, non-empty, provable axiom set for the modus-ponens witness below. -/
theorem impTopAx_provable :
    ∀ c ∈ [((⊤ : S) 🡒 ⊤), (⊤ : S)], (𝗜𝚺₁ : ArithmeticTheory) ⊢ c := by
  intro c hc
  rcases List.mem_cons.mp hc with rfl | hc
  · exact C!_id
  · simp only [List.mem_singleton] at hc; subst hc; exact LO.Entailment.verum!

/-- **Non-degeneracy on the `mp` branch (the EXECUTABLE checker accepts a real inference).** The
three-line script `[ax (⊤🡒⊤), ax ⊤, mp 0 1 ⊤]` over the provable axiom set `[⊤🡒⊤, ⊤]` runs validly
and proves `⊤` *by a genuine modus-ponens step* — line 2 reads lines 0,1 and fires MP — so `Prf`
accepts its code. Unlike `prf_nondegenerate` (which exercises only the `ax`/`⊤` path), this drives
the `mp` path of `checkStep`. With `impTopAx_provable` the axiom set is real and `𝗜𝚺₁`-provable, so
this is a non-degenerate acceptance of a derived (non-axiom) theorem, not a trivial restatement. -/
theorem prf_accepts_mp :
    Prf [((⊤ : S) 🡒 ⊤), (⊤ : S)] (⊤ : S)
      (Encodable.encode [Step.ax ((⊤ : S) 🡒 ⊤), Step.ax (⊤ : S), Step.mp 0 1 (⊤ : S)]) = true :=
  Prf_accepts [((⊤ : S) 🡒 ⊤), (⊤ : S)]
    [Step.ax ((⊤ : S) 🡒 ⊤), Step.ax (⊤ : S), Step.mp 0 1 (⊤ : S)]
    ⊤ [((⊤ : S) 🡒 ⊤), (⊤ : S), (⊤ : S)]
    (by simp [run, runAux, checkStep]) (by simp)

/- **The checker is genuinely executable** (the compiler runs it; `Prf` is computable, not
`noncomputable`). Verified outputs (uncomment to reproduce):
`#eval Prf [⊤🡒⊤, ⊤] ⊤ (encode [ax (⊤🡒⊤), ax ⊤, mp 0 1 ⊤])` ⟶ `true`  (accepts the MP-derived `⊤`);
`#eval Prf [⊤🡒⊤, ⊤] ⊥ (encode [ax (⊤🡒⊤), ax ⊤, mp 0 1 ⊤])` ⟶ `false` (rejects `⊥`).
-- #eval Prf [((⊤ : S) 🡒 ⊤), (⊤ : S)] (⊤ : S)
--   (Encodable.encode [Step.ax ((⊤ : S) 🡒 ⊤), Step.ax (⊤ : S), Step.mp 0 1 (⊤ : S)])
-/

/-! ### L2a — the `Formula` object as a finite carving of codes (Theorem 6.3 L2a) -/

/-- §6.3 L2a well-formedness: a code is a well-formed formula iff it decodes to a sentence.
(via `Option.isSome`), as required for the `Formula` subobject to be a base object of Rep(S). -/
def Wff (c : ℕ) : Prop := (Encodable.decode c : Option S).isSome = true

instance : DecidablePred Wff := fun c => by unfold Wff; infer_instance

/-- §6.3 L2a — the `Formula` object: the finite subobject `{c ≤ M_chk : Wff c}` of `S_work`, cut out
by the decidable predicate `Wff`. A `Fintype` (finite products + decidable predicate — a base
no exponential, Proposition 4.5). -/
abbrev Formula (Mchk : ℕ) : Type := {c : ℕ // c ≤ Mchk ∧ Wff c}

instance (Mchk : ℕ) : Fintype (Formula Mchk) :=
  Fintype.subtype ((Finset.Iic Mchk).filter Wff)
    (fun c => by simp [Finset.mem_filter, Finset.mem_Iic])

/-- §6.3 L2a — `G_{T_S}` a global element `1 → Formula`: the Gödel sentence's code `gnum G` lies in
the `Formula` object once the indexing budget reaches it (`gnum G ≤ M_chk`). -/
theorem godel_mem_Formula (δ : S) (Mchk : ℕ) (h : Encodable.encode δ ≤ Mchk) :
    (⟨Encodable.encode δ, h, by simp [Wff, Encodable.encodek]⟩ : Formula Mchk) ∈
      (Finset.univ : Finset (Formula Mchk)) := Finset.mem_univ _

end GodelChecker
