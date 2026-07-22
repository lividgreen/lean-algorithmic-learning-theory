/-
Copyright (c) 2026 Mykola Palamarchuk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mykola Palamarchuk
-/
import ALT.TimeCost

-- Formal-check file, not Mathlib-destined: opt out of the house-style linters.
set_option linter.style.header false

/-!
# The search cost: the native cost model extended to all of `Nat.Partrec.Code`

`ALT/TimeCost.lean` builds a TOTAL paired evaluator `evalT : Code → ℕ → ℕ × ℕ` whose step laws are
unconditional, at the price of leaving `rfind'` a placeholder: its value-agreement theorem
`eval_eq_val` is stated only on the `RfindFree` fragment. This file supplies the missing case — the
cost of an unbounded search — and so closes the cost model over the whole of `Nat.Partrec.Code`.

## What `rfind'` costs
On input `Nat.pair a m` the code `rfind' cf` probes `cf` at `Nat.pair a (i + m)` for
`i = 0, 1, 2, …` and halts at the least `i` whose result is `0`, returning `i + m`. The honest
sequential cost is what the search actually spends: the probes it makes. So the account is the sum
of the probe costs `∑ i ≤ n, tc cf (Nat.pair a (i + m))` over the halting witness `n`, plus one unit
per probe.

## Why the model must go partial here
`evalT` is total because every one of its clauses is a structural recursion on `Code` — the `prec`
numeric recursion is `Nat.rec`, not a recursive call. A `rfind'` search has no such bound: it runs
until it finds a witness, and on an input where no witness exists it does not halt. So the extended
evaluator `evalP : Code → ℕ →. ℕ × ℕ` is genuinely PARTIAL in its input, and its laws carry domain
hypotheses where `TimeCost`'s carry none. That is the mathematics of unbounded search, not a defect
of the accounting: `evalP_dom` pins the domain to exactly `(eval c n).Dom`, no smaller and no
larger.

## The two theorems that make this an extension rather than a second model
* `evalP_eq_evalT` — on the `RfindFree` fragment the extended evaluator returns precisely the total
  one's answer, `Part.some (val c n, tc c n)`. Every result proved against `tc` therefore transfers;
  there is one cost model, not two.
* `eval_eq_valP` — the value component agrees with `Code.eval` on ALL of `Code`, not merely on the
  fragment. This is the sense in which the model is now total: the cost is charged along the genuine
  computation for every code, `rfind'` included.

The `rfind'` step law comes in two forms: the exact probe-sum identity `tcP_rfind'`, and the uniform
bound `tcP_rfind'_le` — if every probe costs at most `B`, a search with witness `n` costs at most
`(n + 1) * (B + 1)`, linear in the number of probes. That is the `rfind'` analogue of `tc_prec_le`,
and it is domain-restricted by construction: the witness `n` appears in the bound, because no bound
uniform in the input exists for an unbounded search.
-/

namespace TimeCost

open Nat.Partrec (Code)
open Nat.Partrec.Code

/-! ## The probe-cost accumulator -/

/-- The total cost of the probes `0, 1, …, n` of a partial per-probe cost `g`. Defined exactly when
every one of those probes is (`probeSum_dom`), which is why the search cost inherits `eval`'s domain
rather than a smaller one. -/
def probeSum (g : ℕ →. ℕ) : ℕ → Part ℕ
  | 0 => g 0
  | n + 1 => (probeSum g n).bind fun s => (g (n + 1)).map (s + ·)

/-- The probe sum is defined as soon as every probe up to `n` is. -/
theorem probeSum_dom {g : ℕ →. ℕ} : ∀ {n : ℕ}, (∀ i ≤ n, (g i).Dom) → (probeSum g n).Dom := by
  intro n
  induction n with
  | zero => intro h; exact h 0 le_rfl
  | succ k ih =>
      intro h
      exact ⟨ih fun i hi => h i (Nat.le_succ_of_le hi), h (k + 1) le_rfl⟩

/-- A uniform per-probe bound caps the probe sum linearly in the number of probes. -/
theorem probeSum_le {g : ℕ →. ℕ} {B : ℕ} :
    ∀ {n : ℕ}, (∀ i ≤ n, ∀ s ∈ g i, s ≤ B) → ∀ s ∈ probeSum g n, s ≤ (n + 1) * B := by
  intro n
  induction n with
  | zero =>
      intro h s hs
      simpa using h 0 le_rfl s hs
  | succ k ih =>
      intro h s hs
      rw [probeSum, Part.mem_bind_iff] at hs
      obtain ⟨t, ht, hs⟩ := hs
      rw [Part.mem_map_iff] at hs
      obtain ⟨u, hu, rfl⟩ := hs
      have h1 := ih (fun i hi => h i (Nat.le_succ_of_le hi)) t ht
      have h2 := h (k + 1) le_rfl u hu
      rw [Nat.succ_mul]
      omega

/-! ## The extended paired evaluator -/

/-- **The extended paired evaluator.** `evalP c n = Part.some (value, cost)` when `c` halts on `n`,
mirroring `Code.eval` node for node and charging one step per constructor unfolding — the same
accounting as `TimeCost.evalT`, now carried in the `Part` monad so that `rfind'` can be charged
honestly. The `rfind'` clause locates the halting witness with `Nat.rfind` and charges the probes
the search actually made, one unit of overhead apiece. -/
def evalP : Code → ℕ →. ℕ × ℕ
  | zero => fun _ => Part.some (0, 1)
  | succ => fun n => Part.some (n + 1, 1)
  | left => fun n => Part.some (n.unpair.1, 1)
  | right => fun n => Part.some (n.unpair.2, 1)
  | pair cf cg => fun n =>
      (evalP cf n).bind fun p => (evalP cg n).map fun q => (Nat.pair p.1 q.1, p.2 + q.2 + 1)
  | comp cf cg => fun n =>
      (evalP cg n).bind fun q => (evalP cf q.1).map fun p => (p.1, q.2 + p.2 + 1)
  | prec cf cg =>
      Nat.unpaired fun a n =>
        n.rec ((evalP cf a).map fun p => (p.1, p.2 + 1))
          (fun y IH => IH.bind fun p =>
            (evalP cg (Nat.pair a (Nat.pair y p.1))).map fun q => (q.1, p.2 + q.2 + 1))
  | rfind' cf =>
      Nat.unpaired fun a m =>
        (Nat.rfind fun i => (fun p : ℕ × ℕ => p.1 = 0) <$> evalP cf (Nat.pair a (i + m))).bind
          fun n =>
            (probeSum (fun i => (evalP cf (Nat.pair a (i + m))).map Prod.snd) n).map
              fun s => (n + m, s + (n + 1))

/-- The value component of the extended evaluator (equals `Code.eval` — see `eval_eq_valP`). -/
def valP (c : Code) (n : ℕ) : Part ℕ := (evalP c n).map Prod.fst

/-- The extended native sequential-time cost: the step count of `evalP`, charging every probe an
unbounded search makes. Total over `Code`; partial in the input exactly where `Code.eval` is. -/
def tcP (c : Code) (n : ℕ) : Part ℕ := (evalP c n).map Prod.snd

/-! ## Step laws for the extended evaluator -/

theorem evalP_pair (cf cg : Code) (n : ℕ) :
    evalP (pair cf cg) n =
      (evalP cf n).bind fun p =>
        (evalP cg n).map fun q => (Nat.pair p.1 q.1, p.2 + q.2 + 1) := rfl

theorem evalP_comp (cf cg : Code) (n : ℕ) :
    evalP (comp cf cg) n =
      (evalP cg n).bind fun q => (evalP cf q.1).map fun p => (p.1, q.2 + p.2 + 1) := rfl

theorem evalP_prec_zero (cf cg : Code) (a : ℕ) :
    evalP (prec cf cg) (Nat.pair a 0) = (evalP cf a).map fun p => (p.1, p.2 + 1) := by
  simp only [evalP, Nat.unpaired, Nat.unpair_pair, Nat.rec_zero]

theorem evalP_prec_succ (cf cg : Code) (a m : ℕ) :
    evalP (prec cf cg) (Nat.pair a (m + 1)) =
      (evalP (prec cf cg) (Nat.pair a m)).bind fun p =>
        (evalP cg (Nat.pair a (Nat.pair m p.1))).map fun q => (q.1, p.2 + q.2 + 1) := by
  simp only [evalP, Nat.unpaired, Nat.unpair_pair]

/-- The `rfind'` clause: locate the halting witness, then charge the probes made. -/
theorem evalP_rfind' (cf : Code) (a m : ℕ) :
    evalP (rfind' cf) (Nat.pair a m) =
      (Nat.rfind fun i => (fun p : ℕ × ℕ => p.1 = 0) <$> evalP cf (Nat.pair a (i + m))).bind
        fun n =>
          (probeSum (fun i => (evalP cf (Nat.pair a (i + m))).map Prod.snd) n).map
            fun s => (n + m, s + (n + 1)) := by
  simp only [evalP, Nat.unpaired, Nat.unpair_pair]

/-! ## Coherence with the total model on the rfind'-free fragment -/

/-- **Coherence.** On the `RfindFree` fragment the extended evaluator returns exactly the total
evaluator's answer. So `TimeCost`'s unconditional step laws and both magnitude-independent bounds
(`tc_prec_le`, `spaceCost_prec_le`) are statements about this one cost model, not about a separate
one that happens to share a name. -/
theorem evalP_eq_evalT :
    ∀ {c : Code}, RfindFree c → ∀ n, evalP c n = Part.some (val c n, tc c n) := by
  intro c
  induction c with
  | zero => intro _ n; rfl
  | succ => intro _ n; rfl
  | left => intro _ n; rfl
  | right => intro _ n; rfl
  | pair cf cg ihf ihg =>
      intro hc n
      obtain ⟨hf, hg⟩ := hc
      rw [evalP_pair, ihf hf n, ihg hg n]
      simp only [Part.bind_some, Part.map_some]
      rw [val_pair, tc_pair]
  | comp cf cg ihf ihg =>
      intro hc n
      obtain ⟨hf, hg⟩ := hc
      rw [evalP_comp, ihg hg n]
      simp only [Part.bind_some]
      rw [ihf hf (val cg n)]
      simp only [Part.map_some]
      rw [val_comp, tc_comp]
  | prec cf cg ihf ihg =>
      intro hc n
      obtain ⟨hf, hg⟩ := hc
      obtain ⟨a, m, rfl⟩ : ∃ a m, n = Nat.pair a m :=
        ⟨n.unpair.1, n.unpair.2, (Nat.pair_unpair n).symm⟩
      induction m with
      | zero =>
          rw [evalP_prec_zero, ihf hf a]
          simp only [Part.map_some]
          rw [val_prec_zero, tc_prec_zero]
      | succ k ihm =>
          rw [evalP_prec_succ, ihm]
          simp only [Part.bind_some]
          rw [ihg hg _]
          simp only [Part.map_some]
          rw [val_prec_succ, tc_prec_succ]
  | rfind' cf _ => intro hc; exact hc.elim

/-- The cost half of coherence: on the fragment the search cost is the total cost. -/
theorem tcP_eq_tc {c : Code} (hc : RfindFree c) (n : ℕ) : tcP c n = Part.some (tc c n) := by
  rw [tcP, evalP_eq_evalT hc n, Part.map_some]

/-! ## Value-agreement on ALL of `Code` — the model is total -/

/-- `eval`'s `pair` clause in bind/map form (upstream states it with `<*>`). -/
theorem eval_pair_bind (cf cg : Code) (n : ℕ) :
    eval (pair cf cg) n = (eval cf n).bind fun u => (eval cg n).map (Nat.pair u) := by
  ext x
  simp [eval, Seq.seq]

/-- **Value-agreement, unrestricted.** The value component of the extended evaluator is `Code.eval`
on every code, `rfind'` included. This is what `TimeCost.eval_eq_val` could only state on the
`RfindFree` fragment: the cost `tcP` is charged along the genuine computation for all of
`Nat.Partrec.Code`. -/
theorem eval_eq_valP : ∀ (c : Code) (n : ℕ), eval c n = valP c n := by
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
      simp only [valP, evalP_pair, Part.mem_map_iff, Part.mem_bind_iff]
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
      simp only [valP, evalP_comp, Part.mem_bind_iff, Part.mem_map_iff]
      constructor
      · rintro ⟨u, ⟨q, hq, rfl⟩, hx⟩
        rw [ihf q.1, valP, Part.mem_map_iff] at hx
        obtain ⟨p, hp, rfl⟩ := hx
        exact ⟨_, ⟨q, hq, p, hp, rfl⟩, rfl⟩
      · rintro ⟨y, ⟨q, hq, p, hp, rfl⟩, rfl⟩
        refine ⟨q.1, ⟨q, hq, rfl⟩, ?_⟩
        rw [ihf q.1, valP, Part.mem_map_iff]
        exact ⟨p, hp, rfl⟩
  | prec cf cg ihf ihg =>
      intro n
      obtain ⟨a, m, rfl⟩ : ∃ a m, n = Nat.pair a m :=
        ⟨n.unpair.1, n.unpair.2, (Nat.pair_unpair n).symm⟩
      induction m with
      | zero =>
          rw [eval_prec_zero, ihf a, valP, valP, evalP_prec_zero, Part.map_map]
          rfl
      | succ k ihm =>
          rw [eval_prec_succ, ihm]
          ext x
          simp only [valP, evalP_prec_succ, Part.bind_eq_bind, Part.mem_bind_iff,
            Part.mem_map_iff]
          constructor
          · rintro ⟨u, hu, hx⟩
            obtain ⟨p, hp, rfl⟩ := hu
            rw [ihg _, valP, Part.mem_map_iff] at hx
            obtain ⟨q, hq, rfl⟩ := hx
            exact ⟨_, ⟨p, hp, q, hq, rfl⟩, rfl⟩
          · rintro ⟨y, ⟨p, hp, q, hq, rfl⟩, rfl⟩
            refine ⟨p.1, ⟨p, hp, rfl⟩, ?_⟩
            rw [ihg _, valP, Part.mem_map_iff]
            exact ⟨q, hq, rfl⟩
  | rfind' cf ih =>
      intro n
      obtain ⟨a, m, rfl⟩ : ∃ a m, n = Nat.pair a m :=
        ⟨n.unpair.1, n.unpair.2, (Nat.pair_unpair n).symm⟩
      have hpred : (fun i => (fun x => decide (x = 0)) <$> eval cf (Nat.pair a (i + m)))
          = fun i => (fun p : ℕ × ℕ => decide (p.1 = 0)) <$> evalP cf (Nat.pair a (i + m)) := by
        funext i
        rw [ih (Nat.pair a (i + m)), valP]
        rfl
      have hlhs : eval (rfind' cf) (Nat.pair a m) =
          (Nat.rfind fun i => (fun x => x = 0) <$> eval cf (Nat.pair a (i + m))).map (· + m) := by
        simp only [eval, Nat.unpaired, Nat.unpair_pair]
      rw [hlhs, hpred, valP, evalP_rfind']
      ext x
      simp only [Part.mem_map_iff, Part.mem_bind_iff]
      constructor
      · rintro ⟨k, hk, rfl⟩
        have hdom : (probeSum
            (fun i => (evalP cf (Nat.pair a (i + m))).map Prod.snd) k).Dom := by
          refine probeSum_dom fun i hi => ?_
          rcases Nat.lt_or_ge i k with hik | hik
          · exact (Nat.rfind_min hk hik).fst
          · have : i = k := le_antisymm hi hik
            subst this
            exact (Nat.rfind_spec hk).fst
        exact ⟨_, ⟨k, hk, ⟨_, Part.get_mem hdom, rfl⟩⟩, rfl⟩
      · rintro ⟨y, ⟨k, hk, s, _, rfl⟩, rfl⟩
        exact ⟨k, hk, rfl⟩

/-- **The domain is exactly `eval`'s.** The extended cost is defined precisely when the computation
it prices halts — the search cost neither restricts the domain (as a fuel bound would) nor extends
it (as a placeholder value would). -/
theorem evalP_dom (c : Code) (n : ℕ) : (evalP c n).Dom ↔ (eval c n).Dom := by
  rw [eval_eq_valP, valP]
  exact Iff.rfl

/-- The same statement for the cost alone: `tcP c n` is defined exactly when `c` halts on `n`. -/
theorem tcP_dom (c : Code) (n : ℕ) : (tcP c n).Dom ↔ (eval c n).Dom := evalP_dom c n

/-! ## The `rfind'` step law -/

/-- **The `rfind'` step law: the probe-sum identity.** Given the halting witness `n` — the least
offset at which `cf` returns `0` — the search on `Nat.pair a m` costs the probes it made, plus one
unit of overhead per probe. -/
theorem tcP_rfind' (cf : Code) (a m n : ℕ)
    (hn : n ∈ Nat.rfind fun i => (fun p : ℕ × ℕ => p.1 = 0) <$> evalP cf (Nat.pair a (i + m))) :
    tcP (rfind' cf) (Nat.pair a m) =
      (probeSum (fun i => tcP cf (Nat.pair a (i + m))) n).map (· + (n + 1)) := by
  have hR : (Nat.rfind fun i => (fun p : ℕ × ℕ => p.1 = 0) <$> evalP cf (Nat.pair a (i + m)))
      = Part.some n := Part.eq_some_iff.2 hn
  rw [tcP, evalP_rfind', hR, Part.bind_some, Part.map_map]
  rfl

/-- **The uniform probe bound — the `rfind'` analogue of `tc_prec_le`.** If every probe the search
makes costs at most `B`, the whole search costs at most `(n + 1) * (B + 1)`: linear in the number of
probes, with no dependence on the magnitude of the values probed.

The witness `n` is a hypothesis, not a constant, and that is the honest form: unlike `prec`, whose
iteration count is read off its own input, an unbounded search has no bound uniform in the input, so
no `∀ n`-free version of this statement is true. -/
theorem tcP_rfind'_le {cf : Code} {B : ℕ} (a m n : ℕ)
    (hn : n ∈ Nat.rfind fun i => (fun p : ℕ × ℕ => p.1 = 0) <$> evalP cf (Nat.pair a (i + m)))
    (hB : ∀ i ≤ n, ∀ s ∈ tcP cf (Nat.pair a (i + m)), s ≤ B) :
    ∀ s ∈ tcP (rfind' cf) (Nat.pair a m), s ≤ (n + 1) * (B + 1) := by
  intro s hs
  rw [tcP_rfind' cf a m n hn, Part.mem_map_iff] at hs
  obtain ⟨t, ht, rfl⟩ := hs
  have hsum := probeSum_le hB t ht
  rw [Nat.mul_succ]
  exact Nat.add_le_add_right hsum (n + 1)

end TimeCost
