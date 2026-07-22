/-
Copyright (c) 2026 Mykola Palamarchuk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mykola Palamarchuk
-/
import ALT.SearchCost

-- Formal-check file, not Mathlib-destined: opt out of the house-style linters.
set_option linter.style.header false

/-!
# The search workspace: the native SPACE cost extended to all of `Nat.Partrec.Code`

`ALT/TimeCost.lean` builds a total paired evaluator whose second component is a native *workspace*
measure `spaceCost`, at the price of leaving `rfind'` a placeholder `0`: the space account, like the
step account, is stated only on the `RfindFree` fragment. `ALT/SearchCost.lean` closed that gap for
the step count. This file closes it for the workspace, so that BOTH native cost measures are total
over `Nat.Partrec.Code`.

## What `rfind'` costs in space
On input `Nat.pair a m` the code `rfind' cf` probes `cf` at `Nat.pair a (i + m)` for `i = 0, 1, …`
and halts at the least `i` whose result is `0`, returning `i + m`. In *space* the honest account is
the largest workspace any of those probes needed, joined with the bit-length of the answer the
search forms — the same "form-the-result" convention `pair` uses. **This is the whole point of the
file**: where the step account sums over probes, the space account MAXES over them. The counter is
charged only inside the probe calls, exactly as the bounded recursion charges its own counter only
inside its step calls.

## Why the model must go partial here
`spaceCost` is total because every clause is a structural recursion on `Code` — the `prec` numeric
recursion is `Nat.rec`, not a recursive call. A `rfind'` search has no such bound, so the extended
evaluator `evalW : Code → ℕ →. ℕ × ℕ` is genuinely PARTIAL in its input and its laws carry domain
hypotheses. `evalW_dom` pins the domain to exactly `(eval c n).Dom`, no smaller and no larger.

## One model, not two
`evalW` returns a PAIR — the value and the workspace — and its value component is proved to agree
with `Code.eval` directly (`eval_eq_valW`), not through a projection against the step-count model.
Two further theorems make this an extension rather than a rival account:
* `evalW_coherent` — on the `RfindFree` fragment `evalW c n = Part.some (val c n, spaceCost c n)`,
  so every result proved against `spaceCost` (in particular the magnitude-independent bounded-
  recursion bound `spaceCost_prec_le`) is a statement about this model;
* `eval_eq_valW` — the value component is `Code.eval` on ALL of `Code`, so the workspace is charged
  along the genuine computation for every code, `rfind'` included.

## The payoff
The `rfind'` space law comes in two forms: the exact identity `spaceCostP_rfind'`, and the bound
`spaceCostP_rfind'_le` — if every probe fits in `S`, the whole search fits in
`max S (Nat.size (n + m))`. **The probe count is absent.** Where the step account pays
`(n + 1)·(B + 1)` for `n + 1` probes, the search's workspace does not grow with the number of probes
at all; only *holding the answer* costs bits. As for the step account, the halting witness `n` stays
a hypothesis rather than a constant: an unbounded search admits no bound uniform in its input.
-/

namespace TimeCost

open Nat.Partrec (Code)
open Nat.Partrec.Code

/-! ## The probe-workspace accumulator -/

/-- The largest workspace among the probes `0, 1, …, n` of a partial per-probe workspace `g`.
Defined exactly when every one of those probes is (`probeMax_dom`), which is why the search
workspace inherits `eval`'s domain rather than a smaller one. The contrast with the step account's
`probeSum` is the operation: `max`, not `+`. -/
def probeMax (g : ℕ →. ℕ) : ℕ → Part ℕ
  | 0 => g 0
  | n + 1 => (probeMax g n).bind fun s => (g (n + 1)).map (max s)

/-- The probe maximum is defined as soon as every probe up to `n` is. -/
theorem probeMax_dom {g : ℕ →. ℕ} : ∀ {n : ℕ}, (∀ i ≤ n, (g i).Dom) → (probeMax g n).Dom := by
  intro n
  induction n with
  | zero => intro h; exact h 0 le_rfl
  | succ k ih =>
      intro h
      exact ⟨ih fun i hi => h i (Nat.le_succ_of_le hi), h (k + 1) le_rfl⟩

/-- **A per-probe bound caps the probe maximum outright — no factor of the probe count.** This is
the space account's whole divergence from the step account, already visible at the accumulator:
`probeSum_le` pays `(n + 1) * B`, `probeMax_le` pays `S`. -/
theorem probeMax_le {g : ℕ →. ℕ} {S : ℕ} :
    ∀ {n : ℕ}, (∀ i ≤ n, ∀ s ∈ g i, s ≤ S) → ∀ s ∈ probeMax g n, s ≤ S := by
  intro n
  induction n with
  | zero => intro h s hs; exact h 0 le_rfl s hs
  | succ k ih =>
      intro h s hs
      rw [probeMax, Part.mem_bind_iff] at hs
      obtain ⟨t, ht, hs⟩ := hs
      rw [Part.mem_map_iff] at hs
      obtain ⟨u, hu, rfl⟩ := hs
      have h1 := ih (fun i hi => h i (Nat.le_succ_of_le hi)) t ht
      have h2 := h (k + 1) le_rfl u hu
      omega

/-! ## The extended paired evaluator -/

/-- **The extended workspace evaluator.** `evalW c n = Part.some (value, workspace)` when `c` halts
on `n`, mirroring `Code.eval` node for node and accounting the workspace exactly as
`TimeCost.spaceCost` does — a base node holds its input and its output, `pair` joins its two
sub-workspaces with the bit-length of the result it forms, `comp` runs `cf` on `cg`'s value,
bounded recursion `max`es the running workspace with the step's — now carried in the `Part` monad
so that `rfind'` can be charged honestly: the largest probe workspace, joined with the bit-length of
the answer the search forms. -/
def evalW : Code → ℕ →. ℕ × ℕ
  | zero => fun n => Part.some (0, max (Nat.size n) (Nat.size 0))
  | succ => fun n => Part.some (n + 1, max (Nat.size n) (Nat.size (n + 1)))
  | left => fun n => Part.some (n.unpair.1, max (Nat.size n) (Nat.size n.unpair.1))
  | right => fun n => Part.some (n.unpair.2, max (Nat.size n) (Nat.size n.unpair.2))
  | pair cf cg => fun n =>
      (evalW cf n).bind fun p => (evalW cg n).map fun q =>
        (Nat.pair p.1 q.1, max (max p.2 q.2) (Nat.size (Nat.pair p.1 q.1)))
  | comp cf cg => fun n =>
      (evalW cg n).bind fun q => (evalW cf q.1).map fun p => (p.1, max q.2 p.2)
  | prec cf cg =>
      Nat.unpaired fun a n =>
        n.rec (evalW cf a)
          (fun y IH => IH.bind fun p =>
            (evalW cg (Nat.pair a (Nat.pair y p.1))).map fun q => (q.1, max p.2 q.2))
  | rfind' cf =>
      Nat.unpaired fun a m =>
        (Nat.rfind fun i => (fun p : ℕ × ℕ => p.1 = 0) <$> evalW cf (Nat.pair a (i + m))).bind
          fun n =>
            (probeMax (fun i => (evalW cf (Nat.pair a (i + m))).map Prod.snd) n).map
              fun s => (n + m, max s (Nat.size (n + m)))

/-- The value component of the workspace evaluator (equals `Code.eval` — see `eval_eq_valW`). -/
def valW (c : Code) (n : ℕ) : Part ℕ := (evalW c n).map Prod.fst

/-- The extended native workspace cost: the largest intermediate bit-length `evalW` sees, charging
every probe an unbounded search makes. Total over `Code`; partial in the input exactly where
`Code.eval` is. -/
def spaceCostP (c : Code) (n : ℕ) : Part ℕ := (evalW c n).map Prod.snd

/-! ## Step laws for the extended evaluator -/

theorem evalW_pair (cf cg : Code) (n : ℕ) :
    evalW (pair cf cg) n =
      (evalW cf n).bind fun p => (evalW cg n).map fun q =>
        (Nat.pair p.1 q.1, max (max p.2 q.2) (Nat.size (Nat.pair p.1 q.1))) := rfl

theorem evalW_comp (cf cg : Code) (n : ℕ) :
    evalW (comp cf cg) n =
      (evalW cg n).bind fun q => (evalW cf q.1).map fun p => (p.1, max q.2 p.2) := rfl

theorem evalW_prec_zero (cf cg : Code) (a : ℕ) :
    evalW (prec cf cg) (Nat.pair a 0) = evalW cf a := by
  simp only [evalW, Nat.unpaired, Nat.unpair_pair, Nat.rec_zero]

theorem evalW_prec_succ (cf cg : Code) (a m : ℕ) :
    evalW (prec cf cg) (Nat.pair a (m + 1)) =
      (evalW (prec cf cg) (Nat.pair a m)).bind fun p =>
        (evalW cg (Nat.pair a (Nat.pair m p.1))).map fun q => (q.1, max p.2 q.2) := by
  simp only [evalW, Nat.unpaired, Nat.unpair_pair]

/-- The `rfind'` clause: locate the halting witness, then charge the largest probe workspace,
joined with the bit-length of the answer formed. -/
theorem evalW_rfind' (cf : Code) (a m : ℕ) :
    evalW (rfind' cf) (Nat.pair a m) =
      (Nat.rfind fun i => (fun p : ℕ × ℕ => p.1 = 0) <$> evalW cf (Nat.pair a (i + m))).bind
        fun n =>
          (probeMax (fun i => (evalW cf (Nat.pair a (i + m))).map Prod.snd) n).map
            fun s => (n + m, max s (Nat.size (n + m))) := by
  simp only [evalW, Nat.unpaired, Nat.unpair_pair]

/-! ## Coherence with the total model on the rfind'-free fragment -/

/-- **Coherence.** On the `RfindFree` fragment the extended evaluator returns exactly the total
model's answer, value and workspace together. So the magnitude-independent bounded-recursion bound
`spaceCost_prec_le` — and everything built on it — is a statement about this one workspace model,
not about a separate one that happens to share a name. -/
theorem evalW_coherent :
    ∀ {c : Code}, RfindFree c → ∀ n, evalW c n = Part.some (val c n, spaceCost c n) := by
  intro c
  induction c with
  | zero => intro _ n; rfl
  | succ => intro _ n; rfl
  | left => intro _ n; rfl
  | right => intro _ n; rfl
  | pair cf cg ihf ihg =>
      intro hc n
      obtain ⟨hf, hg⟩ := hc
      rw [evalW_pair, ihf hf n, ihg hg n]
      simp only [Part.bind_some, Part.map_some]
      rw [val_pair, spaceCost_pair]
  | comp cf cg ihf ihg =>
      intro hc n
      obtain ⟨hf, hg⟩ := hc
      rw [evalW_comp, ihg hg n]
      simp only [Part.bind_some]
      rw [ihf hf (val cg n)]
      simp only [Part.map_some]
      rw [val_comp, spaceCost_comp]
  | prec cf cg ihf ihg =>
      intro hc n
      obtain ⟨hf, hg⟩ := hc
      obtain ⟨a, m, rfl⟩ : ∃ a m, n = Nat.pair a m :=
        ⟨n.unpair.1, n.unpair.2, (Nat.pair_unpair n).symm⟩
      induction m with
      | zero =>
          rw [evalW_prec_zero, ihf hf a, val_prec_zero, spaceCost_prec_zero]
      | succ k ihm =>
          rw [evalW_prec_succ, ihm]
          simp only [Part.bind_some]
          rw [ihg hg _]
          simp only [Part.map_some]
          rw [val_prec_succ, spaceCost_prec_succ]
  | rfind' cf _ => intro hc; exact hc.elim

/-- The workspace half of coherence: on the fragment the search workspace is `spaceCost`. -/
theorem spaceCostP_eq_spaceCost {c : Code} (hc : RfindFree c) (n : ℕ) :
    spaceCostP c n = Part.some (spaceCost c n) := by
  rw [spaceCostP, evalW_coherent hc n, Part.map_some]

/-! ## Value-agreement on ALL of `Code` — the model is total -/

/-- **Value-agreement, unrestricted.** The value component of the workspace evaluator is `Code.eval`
on every code, `rfind'` included. This is what `TimeCost.eval_eq_val` could state only on the
`RfindFree` fragment: the workspace `spaceCostP` is charged along the genuine computation for all of
`Nat.Partrec.Code`. -/
theorem eval_eq_valW : ∀ (c : Code) (n : ℕ), eval c n = valW c n := by
  intro c
  induction c with
  | zero => intro n; rfl
  | succ => intro n; rfl
  | left => intro n; rfl
  | right => intro n; rfl
  | pair cf cg ihf ihg =>
      intro n
      rw [eval_pair_bind, ihf n, ihg n]
      ext x
      simp only [valW, evalW_pair, Part.mem_map_iff, Part.mem_bind_iff]
      constructor
      · rintro ⟨u, ⟨p, hp, rfl⟩, v, ⟨q, hq, rfl⟩, rfl⟩
        exact ⟨_, ⟨p, hp, q, hq, rfl⟩, rfl⟩
      · rintro ⟨y, ⟨p, hp, q, hq, rfl⟩, rfl⟩
        exact ⟨p.1, ⟨p, hp, rfl⟩, q.1, ⟨q, hq, rfl⟩, rfl⟩
  | comp cf cg ihf ihg =>
      intro n
      have hcomp : eval (comp cf cg) n = (eval cg n).bind fun u => eval cf u := rfl
      rw [hcomp, ihg n]
      ext x
      simp only [valW, evalW_comp, Part.mem_bind_iff, Part.mem_map_iff]
      constructor
      · rintro ⟨u, ⟨q, hq, rfl⟩, hx⟩
        rw [ihf q.1, valW, Part.mem_map_iff] at hx
        obtain ⟨p, hp, rfl⟩ := hx
        exact ⟨_, ⟨q, hq, p, hp, rfl⟩, rfl⟩
      · rintro ⟨y, ⟨q, hq, p, hp, rfl⟩, rfl⟩
        refine ⟨q.1, ⟨q, hq, rfl⟩, ?_⟩
        rw [ihf q.1, valW, Part.mem_map_iff]
        exact ⟨p, hp, rfl⟩
  | prec cf cg ihf ihg =>
      intro n
      obtain ⟨a, m, rfl⟩ : ∃ a m, n = Nat.pair a m :=
        ⟨n.unpair.1, n.unpair.2, (Nat.pair_unpair n).symm⟩
      induction m with
      | zero =>
          rw [eval_prec_zero, ihf a, valW, valW, evalW_prec_zero]
      | succ k ihm =>
          rw [eval_prec_succ, ihm]
          ext x
          simp only [valW, evalW_prec_succ, Part.bind_eq_bind, Part.mem_bind_iff,
            Part.mem_map_iff]
          constructor
          · rintro ⟨u, hu, hx⟩
            obtain ⟨p, hp, rfl⟩ := hu
            rw [ihg _, valW, Part.mem_map_iff] at hx
            obtain ⟨q, hq, rfl⟩ := hx
            exact ⟨_, ⟨p, hp, q, hq, rfl⟩, rfl⟩
          · rintro ⟨y, ⟨p, hp, q, hq, rfl⟩, rfl⟩
            refine ⟨p.1, ⟨p, hp, rfl⟩, ?_⟩
            rw [ihg _, valW, Part.mem_map_iff]
            exact ⟨q, hq, rfl⟩
  | rfind' cf ih =>
      intro n
      obtain ⟨a, m, rfl⟩ : ∃ a m, n = Nat.pair a m :=
        ⟨n.unpair.1, n.unpair.2, (Nat.pair_unpair n).symm⟩
      have hpred : (fun i => (fun x => decide (x = 0)) <$> eval cf (Nat.pair a (i + m)))
          = fun i => (fun p : ℕ × ℕ => decide (p.1 = 0)) <$> evalW cf (Nat.pair a (i + m)) := by
        funext i
        rw [ih (Nat.pair a (i + m)), valW]
        rfl
      have hlhs : eval (rfind' cf) (Nat.pair a m) =
          (Nat.rfind fun i => (fun x => x = 0) <$> eval cf (Nat.pair a (i + m))).map (· + m) := by
        simp only [eval, Nat.unpaired, Nat.unpair_pair]
      rw [hlhs, hpred, valW, evalW_rfind']
      ext x
      simp only [Part.mem_map_iff, Part.mem_bind_iff]
      constructor
      · rintro ⟨k, hk, rfl⟩
        have hdom : (probeMax
            (fun i => (evalW cf (Nat.pair a (i + m))).map Prod.snd) k).Dom := by
          refine probeMax_dom fun i hi => ?_
          rcases Nat.lt_or_ge i k with hik | hik
          · exact (Nat.rfind_min hk hik).fst
          · have : i = k := le_antisymm hi hik
            subst this
            exact (Nat.rfind_spec hk).fst
        exact ⟨_, ⟨k, hk, ⟨_, Part.get_mem hdom, rfl⟩⟩, rfl⟩
      · rintro ⟨y, ⟨k, hk, s, _, rfl⟩, rfl⟩
        exact ⟨k, hk, rfl⟩

/-- **The domain is exactly `eval`'s.** The extended workspace is defined precisely when the
computation it prices halts — the account neither restricts the domain (as a fuel bound would) nor
extends it (as a placeholder value would). -/
theorem evalW_dom (c : Code) (n : ℕ) : (evalW c n).Dom ↔ (eval c n).Dom := by
  rw [eval_eq_valW, valW]
  exact Iff.rfl

/-- The same statement for the workspace alone: `spaceCostP c n` is defined exactly when `c` halts
on `n`. -/
theorem spaceCostP_dom (c : Code) (n : ℕ) : (spaceCostP c n).Dom ↔ (eval c n).Dom := evalW_dom c n

/-! ## The `rfind'` space laws -/

/-- **The `rfind'` space law: the probe-maximum identity.** Given the halting witness `n` — the
least offset at which `cf` returns `0` — the search on `Nat.pair a m` occupies the largest workspace
any of its probes needed, joined with the bit-length of the answer `n + m` it forms. -/
theorem spaceCostP_rfind' (cf : Code) (a m n : ℕ)
    (hn : n ∈ Nat.rfind fun i => (fun p : ℕ × ℕ => p.1 = 0) <$> evalW cf (Nat.pair a (i + m))) :
    spaceCostP (rfind' cf) (Nat.pair a m) =
      (probeMax (fun i => spaceCostP cf (Nat.pair a (i + m))) n).map
        (max · (Nat.size (n + m))) := by
  have hR : (Nat.rfind fun i => (fun p : ℕ × ℕ => p.1 = 0) <$> evalW cf (Nat.pair a (i + m)))
      = Part.some n := Part.eq_some_iff.2 hn
  rw [spaceCostP, evalW_rfind', hR, Part.bind_some, Part.map_map]
  rfl

/-- **The per-probe workspace bound — and the probe count is ABSENT.** If every probe the search
makes fits in `S`, the whole search fits in `max S (Nat.size (n + m))`, no matter how many probes it
made. Contrast the step account, where `n + 1` probes cost `(n + 1) * (B + 1)`: rerunning a probe
reuses the same workspace, so only *holding the answer* adds to the bill.

As for the step account, the witness `n` is a hypothesis rather than a constant — an unbounded
search has no bound uniform in its input, so no `∀ n`-free version of this statement is true. -/
theorem spaceCostP_rfind'_le {cf : Code} {S : ℕ} (a m n : ℕ)
    (hn : n ∈ Nat.rfind fun i => (fun p : ℕ × ℕ => p.1 = 0) <$> evalW cf (Nat.pair a (i + m)))
    (hS : ∀ i ≤ n, ∀ s ∈ spaceCostP cf (Nat.pair a (i + m)), s ≤ S) :
    ∀ s ∈ spaceCostP (rfind' cf) (Nat.pair a m), s ≤ max S (Nat.size (n + m)) := by
  intro s hs
  rw [spaceCostP_rfind' cf a m n hn, Part.mem_map_iff] at hs
  obtain ⟨t, ht, rfl⟩ := hs
  have hmax := probeMax_le hS t ht
  omega

end TimeCost
