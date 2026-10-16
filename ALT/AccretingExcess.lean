module

public import ALT.AccretingWitness
public import ALT.ExcessOrderComplete


/-!
# The accreting crossing package: uniform excess, eventual hosting, and the assembled witness
([Guests] §7 Theorem 7.5)

`ALT/AccretingWitness.lean` builds the accreting healer world's guest — a growing habitat whose
stage is its own block count, closing the staged square from every state with no codeword
hypothesis, and whose extent doubles at every stage. `ALT/ExcessOrderComplete.lean` discharges the
internalization threshold's incompleteness antecedent at a concrete theory, `𝗣𝗔⁻`. Composed, the
guest's growing budget eventually clears the threshold and stays cleared: a fixed Gödel size,
delivered once from incompleteness, that every later stage hosts.

* `outgrows_paMinus_uniform` — the uniform excess ([Decoupling] §6.3/§6.4):
  `ALT.outgrows_paMinus` states `∃ gTS` *inside* its budget `κ`, so a literal reading lets
  each budget pick its own sentence. Its proof obtains `gTS` from
  `ALT.incompleteness_of_arith` before `κ` is ever consulted, so pulling the witness
  outside the budget quantifier is a restatement, not a strengthening: one `gTS`, fixed with the
  theory, that every hosting budget represents.
* `eventually_hostsAt` — eventual hosting, crossing stage explicit ([Decoupling] §6.3/§6.4): past
  `t₀ := ALT.capacity (Nat.clog 2 (g + 1))`, every later stage `t + 1` hosts `g`.
* `accreting_outgrows_paMinus` — the package: the accreting healer world's landed skeleton clauses
  ([Guests] §3/§5) beside the uniform excess's eventual-hosting crossing, at every stage past
  threshold.

## Main results

* `outgrows_paMinus_uniform` / `eventually_hostsAt` / `accreting_outgrows_paMinus`.

## Scope

The affordability clause — one fixed description for the whole family — is **not** claimed here:
the pricing machinery (`KE`, `packWorld`, the builders) is stated on numeral-packed fixed carriers
and does not reach the list carrier this module accretes over. No pricing statement appears below.
-/


@[expose] public section

namespace ALT

open RealizabilityCCC
open AdditiveComplexity
open FFL.FirstOrder FFL.FirstOrder.Arithmetic

variable {ι_J : Type*}

/-! ## The uniform excess -/

/-- **The excess order at `𝗣𝗔⁻`, with one Gödel size uniform across every budget** ([Decoupling]
§6.3/§6.4). `ALT.outgrows_paMinus` delivers `gTS` inside its `∀ κ`, so read literally each
budget could get its own sentence; this pulls the witness outside the quantifier. The proof is a
restatement, not a strengthening: `ALT.incompleteness_of_arith` already supplies `gTS`
before any budget is consulted, so the same `gTS` serves every `κ`. -/
theorem outgrows_paMinus_uniform :
    ∃ gTS, ∀ κ Mchk, ALT.hostsAt κ gTS → gTS < Mchk → Mchk ≤ gTS ^ 2 →
      ∃ R : ReflectiveAsm gTS, R.depth = Mchk ∧
        ALT.FitsIn (recursorAsm R.depth) κ ∧
        ∃ M, ALT.RepresentsUnderivableTruth (Encodable.encode : Sentence ℒₒᵣ → ℕ)
          (fun δ => (𝗣𝗔⁻ : ArithmeticTheory) ⊢ δ) (fun δ => ℕ↓[ℒₒᵣ] ⊧ δ) M := by
  have : (𝗣𝗔⁻ : ArithmeticTheory).Δ₁ := Theory.Δ₁.ofFinite 𝗣𝗔⁻ PeanoMinus.finite
  obtain ⟨gTS, hInc⟩ := ALT.incompleteness_of_arith 𝗣𝗔⁻
  refine ⟨gTS, fun κ Mchk hhost h1 h2 => ?_⟩
  obtain ⟨R, hdepth, hfits, himp⟩ :=
    ALT.outgrows κ (Encodable.encode : Sentence ℒₒᵣ → ℕ)
      (fun δ => (𝗣𝗔⁻ : ArithmeticTheory) ⊢ δ) (fun δ => ℕ↓[ℒₒᵣ] ⊧ δ) gTS Mchk hhost h1 h2
  exact ⟨R, hdepth, hfits, himp hInc⟩

/-! ## Eventual hosting -/

/-- **Eventual hosting, with the crossing stage explicit** ([Decoupling] §6.3/§6.4). Past
`t₀ := ALT.capacity (Nat.clog 2 (g + 1))`, every later stage `t + 1` hosts `g`:
the budget only grows from `t₀` on, and `t₀` itself already enters
(`ALT.hostsAt_enters`). -/
theorem eventually_hostsAt (g : ℕ) :
    ∃ t₀, ∀ t, t₀ ≤ t → ALT.hostsAt (t + 1) g :=
  ⟨ALT.capacity (Nat.clog 2 (g + 1)), fun t ht =>
    ALT.hostsAt_mono (by omega) (ALT.hostsAt_enters g)⟩

/-! ## The package -/

/-- **The accreting escape witness, packaged**: the accreting healer world's landed skeleton — the
staged square from every state, the one-step erasure margin, and the doubling extent
([Guests] §3/§5, §7 Theorem 7.5) — beside the uniform excess's eventual-hosting crossing:
a Gödel size `gTS`, fixed with the
theory, that every stage past some `t₀` hosts and at which the guest's stage-`(t+1)` budget
delivers a reflective object representing an underivable `𝗣𝗔⁻` truth outright. So "the crossing
holds at every stage past threshold" is a literal quantifier shape here, not a schema to be
instantiated per stage. -/
theorem accreting_outgrows_paMinus (k : ℕ) (π : Mem ι_J Bool → Mem ι_J Bool) :
    (Nonautonomous.PositivelyInvariant (accUpdate k π) (accStage k) ∧
      Nonautonomous.Semiconj (accUpdate k π) accLaw (accRead k) (accStage k) ∧
      (∀ t, (Nonautonomous.imageFiber (accRead (ι_J := ι_J) k) (accStage k) t).ncard
        = 2 ^ (t + 1)) ∧
      (∀ t s, s ∈ accCode k t →
        ∀ s' : List (Mem (Fin (3 ^ k)) Bool) × Mem ι_J Bool, s'.1.length = s.1.length →
          s'.2 = s.2 → (List.zipWith hammingDist s'.1 s.1).sum < 2 ^ k →
            accUpdate k π s' = accUpdate k π s)) ∧
    (∃ gTS, (∃ t₀, ∀ t, t₀ ≤ t → ALT.hostsAt (t + 1) gTS) ∧
      ∀ t Mchk, ALT.hostsAt (t + 1) gTS → gTS < Mchk → Mchk ≤ gTS ^ 2 →
        ∃ R : ReflectiveAsm gTS, R.depth = Mchk ∧
          ALT.FitsIn (recursorAsm R.depth) (t + 1) ∧
          ∃ M, ALT.RepresentsUnderivableTruth (Encodable.encode : Sentence ℒₒᵣ → ℕ)
            (fun δ => (𝗣𝗔⁻ : ArithmeticTheory) ⊢ δ) (fun δ => ℕ↓[ℒₒᵣ] ⊧ δ) M) := by
  obtain ⟨gTS, hInc⟩ := outgrows_paMinus_uniform
  exact ⟨⟨advances_accUpdate k π, stagedSquare_accRead k π, ncard_guestStage_accRead ι_J k,
      fun t s hs s' hlen henv hsum => accUpdate_eq_of_sum_lt k π t hs hlen henv hsum⟩,
    gTS, eventually_hostsAt gTS, fun t => hInc (t + 1)⟩

end ALT
