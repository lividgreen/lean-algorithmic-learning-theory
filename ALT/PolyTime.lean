/-
Copyright (c) 2026 Mykola Palamarchuk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mykola Palamarchuk
-/
import Mathlib
import ALT.TimeCost

-- Formal-check file, not Mathlib-destined: opt out of the house-style linters.
set_option linter.style.header false
set_option linter.style.longLine false

/-!
# A `PolyTime` predicate on the native cost `tc`, with the closure toolkit

Provenance: the native-cost-model workstream. Builds on `ALT/TimeCost.lean` (`evalT`,
`val`, `tc`, `RfindFree`, the step laws, `tc_prec_le`). Downstream infra for bounding a concrete
algorithm's `tc` (the greedy 1-DL consistency solver, a later stage).

## HONEST FRAMING — unit cost, measured against input BIT-LENGTH
`tc` is a UNIT-cost model: each AST primitive costs `1` regardless of operand magnitude. So "polynomial
`tc`" here means **poly-many AST steps as a function of the INPUT BIT-LENGTH `Nat.size n`** — NOT
bit-complexity (a single AST step may move an arbitrarily large `ℕ`). Every definition and lemma is
stated in those terms; nothing here claims a bit-cost bound.

## The output-size clause is on `Nat.size ∘ f`, not `f`
`PolyTime f` bundles a time bound AND an output-size bound; the output bound is on the **bit-length**
`Nat.size (f n)`, poly in `Nat.size n`. This is forced: the task's alternative "`PolyBounded f`" (bound
the VALUE `f n`) is false already for `succ` — `f n = n + 1` is exponential in `Nat.size n`. Bounding
`Nat.size (f n)` is the honest, composable choice (and it is what a downstream `comp`/`prec` cost proof
actually threads — see `polyTime_comp`, `polyTime_prec`).
-/

namespace TimeCost

open Nat.Partrec (Code)
open Nat.Partrec.Code

/-! ## `val` of the base codes (for the base `PolyTime` witnesses) -/

theorem val_zero (n : ℕ) : val zero n = 0 := rfl
theorem val_succ (n : ℕ) : val succ n = n + 1 := rfl
theorem val_left (n : ℕ) : val left n = n.unpair.1 := rfl
theorem val_right (n : ℕ) : val right n = n.unpair.2 := rfl

/-! ## Two `Nat.size` facts the output-size bounds need -/

/-- `Nat.size (n+1) ≤ Nat.size n + 1`: incrementing lengthens by at most one bit. -/
theorem size_succ_le (n : ℕ) : Nat.size (n + 1) ≤ Nat.size n + 1 := by
  rw [Nat.size_le]
  have h : n < 2 ^ Nat.size n := Nat.lt_size_self n
  have hpos : 0 < 2 ^ Nat.size n := by positivity
  calc n + 1 ≤ 2 ^ Nat.size n := h
    _ < 2 ^ (Nat.size n + 1) := by rw [pow_succ]; omega

/-- `Nat.size (Nat.pair a b) ≤ 2·Nat.size a + 2·Nat.size b + 2`: the pairing's output bit-length is
linear in the inputs' bit-lengths (so pairing preserves poly output size). -/
theorem size_pair_le (a b : ℕ) :
    Nat.size (Nat.pair a b) ≤ 2 * Nat.size a + 2 * Nat.size b + 2 := by
  rw [Nat.size_le]
  have ha : a < 2 ^ Nat.size a := Nat.lt_size_self a
  have hb : b < 2 ^ Nat.size b := Nat.lt_size_self b
  have hpair : Nat.pair a b ≤ (a + b + 1) ^ 2 := by
    unfold Nat.pair; split_ifs <;> nlinarith
  have hab : a + b + 1 < 2 ^ (Nat.size a + Nat.size b + 1) := by
    have e1 : (2 : ℕ) ^ Nat.size a ≤ 2 ^ (Nat.size a + Nat.size b) :=
      Nat.pow_le_pow_right (by norm_num) (Nat.le_add_right _ _)
    have e2 : (2 : ℕ) ^ Nat.size b ≤ 2 ^ (Nat.size a + Nat.size b) :=
      Nat.pow_le_pow_right (by norm_num) (Nat.le_add_left _ _)
    have e3 : (2 : ℕ) ^ (Nat.size a + Nat.size b + 1)
        = 2 ^ (Nat.size a + Nat.size b) + 2 ^ (Nat.size a + Nat.size b) := by
      rw [pow_succ]; ring
    omega
  calc Nat.pair a b ≤ (a + b + 1) ^ 2 := hpair
    _ < (2 ^ (Nat.size a + Nat.size b + 1)) ^ 2 := by
        exact Nat.pow_lt_pow_left hab (by norm_num)
    _ = 2 ^ (2 * Nat.size a + 2 * Nat.size b + 2) := by rw [← pow_mul]; ring_nf

/-! ## `PolyBounded` — the poly-in-input-bit-length function algebra -/

/-- A function is **poly-bounded** if it is `O((Nat.size n + 1)^k)` in the input bit-length. -/
def PolyBounded (t : ℕ → ℕ) : Prop := ∃ C k : ℕ, ∀ n, t n ≤ C * (Nat.size n + 1) ^ k + C

/-- Normal form: the additive `+ C` is absorbed into the multiplicative term (as `(size n+1)^k ≥ 1`),
giving the cleaner `t n ≤ C·(size n+1)^k` shape that `add`/`mul`/`pow` compose through. -/
theorem PolyBounded.exists_mul {t : ℕ → ℕ} (h : PolyBounded t) :
    ∃ C k, ∀ n, t n ≤ C * (Nat.size n + 1) ^ k := by
  obtain ⟨C, k, hC⟩ := h
  refine ⟨2 * C, k, fun n => ?_⟩
  have hp : 1 ≤ (Nat.size n + 1) ^ k := Nat.one_le_pow _ _ (Nat.succ_pos _)
  have hCle : C ≤ C * (Nat.size n + 1) ^ k := Nat.le_mul_of_pos_right C (by omega)
  calc t n ≤ C * (Nat.size n + 1) ^ k + C := hC n
    _ ≤ C * (Nat.size n + 1) ^ k + C * (Nat.size n + 1) ^ k := by omega
    _ = 2 * C * (Nat.size n + 1) ^ k := by ring

/-- Rebuild `PolyBounded` from the multiplicative normal form. -/
theorem PolyBounded.of_mul {t : ℕ → ℕ} {C k : ℕ} (h : ∀ n, t n ≤ C * (Nat.size n + 1) ^ k) :
    PolyBounded t := ⟨C, k, fun n => le_trans (h n) (Nat.le_add_right _ _)⟩

theorem PolyBounded.const (a : ℕ) : PolyBounded (fun _ => a) := ⟨a, 0, fun n => by simp⟩

theorem PolyBounded.size : PolyBounded Nat.size :=
  ⟨1, 1, fun n => by simp only [pow_one, one_mul]; omega⟩

/-- ≤-monotone domination: a function dominated by a poly-bounded one is poly-bounded. -/
theorem PolyBounded.mono {s t : ℕ → ℕ} (hst : ∀ n, s n ≤ t n) (ht : PolyBounded t) :
    PolyBounded s := by
  obtain ⟨C, k, hC⟩ := ht; exact ⟨C, k, fun n => le_trans (hst n) (hC n)⟩

/-- Composition on the inside with a size-non-increasing map (`u n ≤ n`). -/
theorem PolyBounded.comp_le {t u : ℕ → ℕ} (ht : PolyBounded t) (hu : ∀ n, u n ≤ n) :
    PolyBounded (fun n => t (u n)) := by
  obtain ⟨C, k, hC⟩ := ht
  refine ⟨C, k, fun n => le_trans (hC (u n)) ?_⟩
  gcongr
  exact Nat.size_le_size (hu n)

theorem PolyBounded.add {s t : ℕ → ℕ} (hs : PolyBounded s) (ht : PolyBounded t) :
    PolyBounded (fun n => s n + t n) := by
  obtain ⟨C1, k1, h1⟩ := hs.exists_mul
  obtain ⟨C2, k2, h2⟩ := ht.exists_mul
  refine PolyBounded.of_mul (C := C1 + C2) (k := max k1 k2) (fun n => ?_)
  have hb : 1 ≤ Nat.size n + 1 := Nat.succ_le_succ (Nat.zero_le _)
  have e1 : (Nat.size n + 1) ^ k1 ≤ (Nat.size n + 1) ^ max k1 k2 :=
    Nat.pow_le_pow_right hb (le_max_left _ _)
  have e2 : (Nat.size n + 1) ^ k2 ≤ (Nat.size n + 1) ^ max k1 k2 :=
    Nat.pow_le_pow_right hb (le_max_right _ _)
  calc s n + t n ≤ C1 * (Nat.size n + 1) ^ k1 + C2 * (Nat.size n + 1) ^ k2 :=
        Nat.add_le_add (h1 n) (h2 n)
    _ ≤ C1 * (Nat.size n + 1) ^ max k1 k2 + C2 * (Nat.size n + 1) ^ max k1 k2 := by
        gcongr
    _ = (C1 + C2) * (Nat.size n + 1) ^ max k1 k2 := by ring

theorem PolyBounded.mul {s t : ℕ → ℕ} (hs : PolyBounded s) (ht : PolyBounded t) :
    PolyBounded (fun n => s n * t n) := by
  obtain ⟨C1, k1, h1⟩ := hs.exists_mul
  obtain ⟨C2, k2, h2⟩ := ht.exists_mul
  refine PolyBounded.of_mul (C := C1 * C2) (k := k1 + k2) (fun n => ?_)
  calc s n * t n ≤ (C1 * (Nat.size n + 1) ^ k1) * (C2 * (Nat.size n + 1) ^ k2) :=
        Nat.mul_le_mul (h1 n) (h2 n)
    _ = (C1 * C2) * (Nat.size n + 1) ^ (k1 + k2) := by rw [pow_add]; ring

theorem PolyBounded.pow {t : ℕ → ℕ} (h : PolyBounded t) (j : ℕ) :
    PolyBounded (fun n => t n ^ j) := by
  obtain ⟨C, k, hC⟩ := h.exists_mul
  refine PolyBounded.of_mul (C := C ^ j) (k := k * j) (fun n => ?_)
  calc t n ^ j ≤ (C * (Nat.size n + 1) ^ k) ^ j := Nat.pow_le_pow_left (hC n) j
    _ = C ^ j * (Nat.size n + 1) ^ (k * j) := by rw [mul_pow, ← pow_mul]

/-! ## `PolyTime` — the bundled predicate -/

/-- `f` is **poly-time** (native cost): some rfind'-free code computes it, its native step count is
poly in the input bit-length, AND its output bit-length is poly in the input bit-length. The
output-size clause is REQUIRED for `polyTime_comp`/`polyTime_prec` to close (the inner call's cost is
poly in the inner output's bit-length). See the module note on why it is on `Nat.size ∘ f`. -/
def PolyTime (f : ℕ → ℕ) : Prop :=
  ∃ c : Code, RfindFree c ∧ (∀ n, val c n = f n) ∧
    PolyBounded (tc c) ∧ PolyBounded (fun n => Nat.size (f n))

/-! ## Base closure — `zero`, `succ`, `left`, `right` are `PolyTime` -/

theorem polyTime_zero : PolyTime (fun _ => 0) :=
  ⟨zero, trivial, fun _ => rfl,
    PolyBounded.mono (fun n => (tc_zero n).le) (PolyBounded.const 1),
    PolyBounded.mono (fun _ => by simp) (PolyBounded.const 0)⟩

theorem polyTime_succ : PolyTime (fun n => n + 1) :=
  ⟨succ, trivial, fun _ => rfl,
    PolyBounded.mono (fun n => (tc_succ n).le) (PolyBounded.const 1),
    PolyBounded.mono (fun n => size_succ_le n) (PolyBounded.size.add (PolyBounded.const 1))⟩

theorem polyTime_left : PolyTime (fun n => n.unpair.1) :=
  ⟨left, trivial, fun _ => rfl,
    PolyBounded.mono (fun n => (tc_left n).le) (PolyBounded.const 1),
    PolyBounded.mono (fun n => Nat.size_le_size (Nat.unpair_left_le n)) PolyBounded.size⟩

theorem polyTime_right : PolyTime (fun n => n.unpair.2) :=
  ⟨right, trivial, fun _ => rfl,
    PolyBounded.mono (fun n => (tc_right n).le) (PolyBounded.const 1),
    PolyBounded.mono (fun n => Nat.size_le_size (Nat.unpair_right_le n)) PolyBounded.size⟩

/-! ## `pair` closure -/

theorem polyTime_pair {f g : ℕ → ℕ} (hf : PolyTime f) (hg : PolyTime g) :
    PolyTime (fun n => Nat.pair (f n) (g n)) := by
  obtain ⟨cf, hcf, hvf, htf, hsf⟩ := hf
  obtain ⟨cg, hcg, hvg, htg, hsg⟩ := hg
  refine ⟨pair cf cg, ⟨hcf, hcg⟩, fun n => by rw [val_pair, hvf, hvg], ?_, ?_⟩
  · -- native cost: `tc cf + tc cg + 1`
    refine PolyBounded.mono (fun n => (tc_pair cf cg n).le) ?_
    exact (htf.add htg).add (PolyBounded.const 1)
  · -- output bit-length: `size (pair (f n) (g n)) ≤ 2·size(f n) + 2·size(g n) + 2`
    refine PolyBounded.mono (fun n => size_pair_le (f n) (g n)) ?_
    exact (((PolyBounded.const 2).mul hsf).add ((PolyBounded.const 2).mul hsg)).add
      (PolyBounded.const 2)

/-! ## `comp` closure — where the inner output-size clause earns its keep -/

theorem polyTime_comp {f g : ℕ → ℕ} (hf : PolyTime f) (hg : PolyTime g) :
    PolyTime (f ∘ g) := by
  obtain ⟨cf, hcf, hvf, htf, hsf⟩ := hf
  obtain ⟨cg, hcg, hvg, htg, hsg⟩ := hg
  -- `size (val cg n) = size (g n)` is poly in `size n` — the inner output-size bound, reused twice.
  have hsg' : PolyBounded (fun n => Nat.size (val cg n)) :=
    PolyBounded.mono (fun n => (congrArg Nat.size (hvg n)).le) hsg
  refine ⟨comp cf cg, ⟨hcf, hcg⟩, fun n => by rw [val_comp, hvg, hvf]; rfl, ?_, ?_⟩
  · -- native cost: `tc cg n + tc cf (val cg n) + 1`; the middle term is poly ONLY because `hsg'` bounds
    -- the inner output bit-length that `cf`'s cost is measured against.
    obtain ⟨Cf, kf, hCf⟩ := htf.exists_mul
    have hmid : PolyBounded (fun n => tc cf (val cg n)) :=
      PolyBounded.mono (fun n => hCf (val cg n))
        ((PolyBounded.const Cf).mul ((hsg'.add (PolyBounded.const 1)).pow kf))
    refine PolyBounded.mono (fun n => (tc_comp cf cg n).le) ?_
    exact (htg.add hmid).add (PolyBounded.const 1)
  · -- output bit-length: `size ((f ∘ g) n) = size (f (g n)) ≤ Cf·(size (g n) + 1)^kf` — poly via
    -- `hf`'s output clause at argument `g n`, then `hg`'s output clause `hsg`.
    obtain ⟨Cf, kf, hCf⟩ := hsf.exists_mul
    exact PolyBounded.mono (fun n => hCf (g n))
      ((PolyBounded.const Cf).mul ((hsg.add (PolyBounded.const 1)).pow kf))

/-! ## `prec` closure — bounded recursion (the loop cost lemma)

The exact per-iteration cost refinement of `tc_prec_le`: only the ACTUAL iteration inputs need the
per-step bound `B` (not all of `ℕ`), so a per-step cost that grows with the accumulator is fine as
long as it stays `≤ B` on the states the loop visits. -/
theorem tc_prec_le' {cf cg : Code} {a B : ℕ} :
    ∀ n, (∀ i, i < n →
        tc cg (Nat.pair a (Nat.pair i (val (prec cf cg) (Nat.pair a i)))) ≤ B) →
      tc (prec cf cg) (Nat.pair a n) ≤ tc cf a + (B + 1) * n + 1 := by
  intro n
  induction n with
  | zero => intro _; rw [tc_prec_zero]; omega
  | succ m ih =>
      intro hcg
      rw [tc_prec_succ, Nat.mul_succ]
      have hstep := hcg m (Nat.lt_succ_self m)
      have hih := ih (fun i hi => hcg i (Nat.lt_succ_of_lt hi))
      omega

/-- **Bounded-recursion closure.** `prec cf cg` (as a function of its packed input `N = ⟨a, m⟩`) is
`PolyTime` provided the explicit premises hold:
* `hbase` — the base code `cf`'s native cost is poly in its argument's bit-length;
* `hiter` — the iteration count `m = N.unpair.2` is poly in the input bit-length `Nat.size N`
  (a genuine restriction: `m` can be exponential in `Nat.size N` for an unconstrained packing, so the
  caller's loop must arrange a poly step count — see the module notes);
* `Bstep`/`hBstep`/`hstep` — a per-step cost bound `Bstep N` (poly in `Nat.size N`) that holds
  UNIFORMLY over the iterations `i < m` of input `N`; this is where the accumulator matters — the step
  input threads `val (prec cf cg) (⟨a, i⟩)`, so `Bstep` can only be poly because that accumulator is;
* `hacc` — the running accumulator stays poly-bounded in bit-length across all inputs (this IS the
  output-size clause of `PolyTime`).

Total: `tc ≤ tc cf a + (Bstep N + 1)·m + 1`, poly by the `PolyBounded` algebra (via `tc_prec_le'`). -/
theorem polyTime_prec {cf cg : Code} (hcf : RfindFree cf) (hcg : RfindFree cg)
    (hbase : PolyBounded (tc cf))
    (hiter : PolyBounded (fun N => N.unpair.2))
    (Bstep : ℕ → ℕ) (hBstep : PolyBounded Bstep)
    (hstep : ∀ N i, i < N.unpair.2 →
      tc cg (Nat.pair N.unpair.1 (Nat.pair i (val (prec cf cg) (Nat.pair N.unpair.1 i)))) ≤ Bstep N)
    (hacc : PolyBounded (fun N => Nat.size (val (prec cf cg) N))) :
    PolyTime (fun N => val (prec cf cg) N) := by
  refine ⟨prec cf cg, ⟨hcf, hcg⟩, fun _ => rfl, ?_, hacc⟩
  have hcost : ∀ N,
      tc (prec cf cg) N ≤ tc cf N.unpair.1 + (Bstep N + 1) * N.unpair.2 + 1 := by
    intro N
    have key := tc_prec_le' (cf := cf) (cg := cg) (a := N.unpair.1) (B := Bstep N)
      N.unpair.2 (fun i hi => hstep N i hi)
    rwa [Nat.pair_unpair] at key
  refine PolyBounded.mono hcost ?_
  have hb1 : PolyBounded (fun N => tc cf N.unpair.1) := hbase.comp_le Nat.unpair_left_le
  have hb2 : PolyBounded (fun N => (Bstep N + 1) * N.unpair.2) :=
    (hBstep.add (PolyBounded.const 1)).mul hiter
  exact (hb1.add hb2).add (PolyBounded.const 1)

/-! ## Part 1 — the blocker: `polyTime_prec`'s `hiter` premise is undischargeable for a genuine loop

`polyTime_prec` concludes `PolyTime` for the raw `prec cf cg` over ALL packed inputs `N`, but its
premise `hiter : PolyBounded (fun N => N.unpair.2)` is FALSE: a raw second-projection slot is
exponential in the input bit-length `Nat.size N` (the family `N = ⟨0, 2^j⟩` has `size N ≤ 2j+4` yet
`N.unpair.2 = 2^j`). So as stated the lemma is essentially inapplicable — the raw `prec` over all
inputs genuinely is not `PolyTime`. `polyTime_prec` stays as a low-level building block; the usable
loop closure is `polyTime_loop` (Part 2), where the iteration COUNT is a poly-bit function of the
actual input, not a raw slot. -/

open Asymptotics Filter in
/-- Exponential beats every fixed polynomial: for all `C k`, some `j` has `C·(2j+5)^k + C < 2^j`.
The elementary fact behind the blocker (a raw `unpair` slot is exponential in the input bit-length).
Proved by the `=o`-of-itself route (mirrors `ParityCounterexample.dSQ_not_polyBounded`). -/
theorem exists_two_pow_gt_poly (C k : ℕ) : ∃ j, C * (2 * j + 5) ^ k + C < 2 ^ j := by
  by_contra hcon
  simp only [not_exists, not_lt] at hcon
  -- `hcon : ∀ j, 2 ^ j ≤ C * (2 * j + 5) ^ k + C`
  have hnat : ∀ j : ℕ, 1 ≤ j → C * (2 * j + 5) ^ k + C ≤ C * (7 ^ k + 1) * j ^ k := by
    intro j hj
    have h1 : (2 * j + 5) ^ k ≤ 7 ^ k * j ^ k := by
      calc (2 * j + 5) ^ k ≤ (7 * j) ^ k := Nat.pow_le_pow_left (by omega) k
        _ = 7 ^ k * j ^ k := by rw [mul_pow]
    have h2 : 1 ≤ j ^ k := Nat.one_le_pow _ _ (by omega)
    calc C * (2 * j + 5) ^ k + C
        ≤ C * (7 ^ k * j ^ k) + C * j ^ k :=
          Nat.add_le_add (Nat.mul_le_mul (le_refl C) h1) (Nat.le_mul_of_pos_right C (by omega))
      _ = C * (7 ^ k + 1) * j ^ k := by ring
  have hbig : (fun j : ℕ => (2 : ℝ) ^ j) =O[atTop] (fun j : ℕ => (j : ℝ) ^ k) := by
    rw [isBigO_iff]
    refine ⟨((C * (7 ^ k + 1) : ℕ) : ℝ), ?_⟩
    filter_upwards [eventually_ge_atTop 1] with j hj
    have hcast : (2 : ℝ) ^ j ≤ ((C * (7 ^ k + 1) : ℕ) : ℝ) * (j : ℝ) ^ k := by
      have hchain := le_trans (hcon j) (hnat j hj)
      calc (2 : ℝ) ^ j = ((2 ^ j : ℕ) : ℝ) := by push_cast; ring
        _ ≤ ((C * (7 ^ k + 1) * j ^ k : ℕ) : ℝ) := by exact_mod_cast hchain
        _ = ((C * (7 ^ k + 1) : ℕ) : ℝ) * (j : ℝ) ^ k := by push_cast; ring
    rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
    exact hcast
  have hlit : (fun j : ℕ => (j : ℝ) ^ k) =o[atTop] (fun j : ℕ => (2 : ℝ) ^ j) :=
    isLittleO_pow_const_const_pow_of_one_lt k (by norm_num : (1 : ℝ) < 2)
  have hself : (fun j : ℕ => (2 : ℝ) ^ j) =o[atTop] (fun j : ℕ => (2 : ℝ) ^ j) :=
    hbig.trans_isLittleO hlit
  have hhalf := hself.bound (by norm_num : (0 : ℝ) < 1 / 2)
  obtain ⟨j, hj⟩ := hhalf.exists
  have hpos : (0 : ℝ) < 2 ^ j := by positivity
  rw [Real.norm_of_nonneg hpos.le] at hj
  linarith

/-- **The blocker.** A raw second-projection slot is NOT poly-bounded in the input bit-length, so the
`hiter` premise of `polyTime_prec` cannot be discharged for a genuine loop. Witness family:
`N = Nat.pair 0 (2^j)` has `Nat.size N + 1 ≤ 2j+5` (pairing is linear in the parts' bit-lengths,
`size_pair_le`) yet `N.unpair.2 = 2^j`, and `2^j` outgrows every polynomial in `2j+5`
(`exists_two_pow_gt_poly`). -/
theorem unpair_snd_not_polyBounded : ¬ PolyBounded (fun N => N.unpair.2) := by
  rintro ⟨C, k, h⟩
  obtain ⟨j, hj⟩ := exists_two_pow_gt_poly C k
  have hN := h (Nat.pair 0 (2 ^ j))
  simp only [Nat.unpair_pair] at hN
  -- `hN : 2 ^ j ≤ C * (Nat.size (Nat.pair 0 (2^j)) + 1) ^ k + C`
  have hsize : Nat.size (Nat.pair 0 (2 ^ j)) + 1 ≤ 2 * j + 5 := by
    have h1 := size_pair_le 0 (2 ^ j)
    have h2 : Nat.size (2 ^ j) ≤ j + 1 :=
      Nat.size_le.mpr (Nat.pow_lt_pow_right (by norm_num) (Nat.lt_succ_self j))
    rw [Nat.size_zero] at h1
    omega
  have hmono : C * (Nat.size (Nat.pair 0 (2 ^ j)) + 1) ^ k + C ≤ C * (2 * j + 5) ^ k + C := by
    gcongr
  omega

/-! ## Part 2 — the repair: `polyTime_loop`, the usable bounded-recursion closure

The realistic pattern: the loop is `comp (prec cf cg) shaper`, where the shaper computes the packed
input `⟨astart n, count n⟩` from the ACTUAL input `n`, and the iteration count `count n` is a genuine
poly-bit VALUE function of `n` (premise `hCval : PolyBounded count`). This replaces the
undischargeable `hiter` (Part 1): the number of iterations is `count n`, poly in `Nat.size n` because
`hCval` bounds the VALUE `count n` — not a raw slot of the packed input. -/

/-- The identity `n ↦ n` is `PolyTime` (code `pair left right`, reconstructing `n` from its projections
via `Nat.pair_unpair`; native cost a constant `3`). A convenient `astart`/`count` building block. -/
theorem polyTime_id : PolyTime (fun n => n) :=
  ⟨pair left right, ⟨trivial, trivial⟩,
    fun n => by rw [val_pair, val_left, val_right, Nat.pair_unpair],
    PolyBounded.mono (fun n => le_of_eq (by rw [tc_pair, tc_left, tc_right])) (PolyBounded.const 3),
    PolyBounded.size⟩

/-- The `c`-fold successor tower `succ ∘ ⋯ ∘ succ ∘ zero` computing the constant `c`. -/
def constCode : ℕ → Code
  | 0 => zero
  | (c + 1) => comp succ (constCode c)

theorem val_constCode (c n : ℕ) : val (constCode c) n = c := by
  induction c with
  | zero => rfl
  | succ d ih => simp only [constCode, val_comp, val_succ, ih]

theorem rfindFree_constCode (c : ℕ) : RfindFree (constCode c) := by
  induction c with
  | zero => trivial
  | succ d ih => exact ⟨trivial, ih⟩

theorem tc_constCode_le (c n : ℕ) : tc (constCode c) n ≤ 2 * c + 1 := by
  induction c with
  | zero => simp [constCode]
  | succ d ih => simp only [constCode, tc_comp, tc_succ]; omega

/-- Every constant function `n ↦ c` is `PolyTime` (native cost `2c+1`, output bit-length `size c`). -/
theorem polyTime_const (c : ℕ) : PolyTime (fun _ => c) :=
  ⟨constCode c, rfindFree_constCode c, fun n => val_constCode c n,
    PolyBounded.mono (fun n => tc_constCode_le c n) (PolyBounded.const (2 * c + 1)),
    PolyBounded.const (Nat.size c)⟩

/-- **Bounded-recursion closure, usable form.** The loop `n ↦ val (prec cf cg) ⟨astart n, count n⟩`
is `PolyTime` under premises a caller can actually discharge:
* `hA`/`hC` — the input-shaper stages `astart`, `count` are `PolyTime` (so `pair`-ing them is a
  poly-time shaper feeding `prec`);
* `hCval` — the iteration COUNT `count n` is poly-bounded as a VALUE in `Nat.size n`. This is THE
  repair over `polyTime_prec`: the number of loop iterations is `count n`, so it is `hCval` (not the
  size clause of `hC`, which only bounds `Nat.size (count n)`) that makes the loop's linear step-count
  term poly. `hC`'s output clause does NOT suffice — `size (count n)` poly allows `count n` itself to
  be exponential, i.e. exponentially many iterations;
* `hbase` — the base code `cf`'s native cost is poly in its argument's bit-length;
* `Bstep`/`hBstep`/`hstep` — a per-step cost bound `Bstep n` (poly in `Nat.size n`) holding UNIFORMLY
  over the iterations `i < count n` (only the VISITED states, via `tc_prec_le'` — the step cost may be
  unbounded over all of `ℕ`);
* `hacc` — the loop's output bit-length is poly (this IS the `PolyTime` output-size clause).

Realized as `comp (prec cf cg) (pair ca cc)`; cost `tc (pair ca cc) n + tc cf (astart n) +
(Bstep n + 1)·count n + O(1)`, poly by the `PolyBounded` algebra (via `tc_comp`, `tc_prec_le'`). -/
theorem polyTime_loop {cf cg : Code} (hcf : RfindFree cf) (hcg : RfindFree cg)
    {astart count : ℕ → ℕ}
    (hA : PolyTime astart) (hC : PolyTime count) (hCval : PolyBounded count)
    (hbase : PolyBounded (tc cf))
    (Bstep : ℕ → ℕ) (hBstep : PolyBounded Bstep)
    (hstep : ∀ n i, i < count n →
      tc cg (Nat.pair (astart n) (Nat.pair i (val (prec cf cg) (Nat.pair (astart n) i)))) ≤ Bstep n)
    (hacc : PolyBounded (fun n => Nat.size (val (prec cf cg) (Nat.pair (astart n) (count n))))) :
    PolyTime (fun n => val (prec cf cg) (Nat.pair (astart n) (count n))) := by
  obtain ⟨ca, hca_rf, hca_val, hca_tc, hca_size⟩ := hA
  obtain ⟨cc, hcc_rf, hcc_val, hcc_tc, _hcc_size⟩ := hC
  have hsval : ∀ n, val (pair ca cc) n = Nat.pair (astart n) (count n) := by
    intro n; rw [val_pair, hca_val, hcc_val]
  refine ⟨comp (prec cf cg) (pair ca cc), ⟨⟨hcf, hcg⟩, hca_rf, hcc_rf⟩, ?_, ?_, hacc⟩
  · intro n; rw [val_comp, hsval n]
  · obtain ⟨Cf, kf, hCf⟩ := hbase.exists_mul
    have tccf : PolyBounded (fun n => tc cf (astart n)) :=
      PolyBounded.mono (fun n => hCf (astart n))
        ((PolyBounded.const Cf).mul ((hca_size.add (PolyBounded.const 1)).pow kf))
    have hlin : PolyBounded (fun n => (Bstep n + 1) * count n) :=
      (hBstep.add (PolyBounded.const 1)).mul hCval
    have htcs : PolyBounded (fun n => tc (pair ca cc) n) :=
      PolyBounded.mono (fun n => le_of_eq (tc_pair ca cc n))
        ((hca_tc.add hcc_tc).add (PolyBounded.const 1))
    have hcost : ∀ n,
        tc (comp (prec cf cg) (pair ca cc)) n ≤
          tc (pair ca cc) n + tc cf (astart n) + (Bstep n + 1) * count n + 3 := by
      intro n
      have hpc : tc (prec cf cg) (val (pair ca cc) n) ≤
          tc cf (astart n) + (Bstep n + 1) * count n + 1 := by
        rw [hsval n]; exact tc_prec_le' (count n) (fun i hi => hstep n i hi)
      have hc := tc_comp (prec cf cg) (pair ca cc) n
      omega
    exact PolyBounded.mono hcost (((htcs.add tccf).add hlin).add (PolyBounded.const 3))

/-! ## Part 3 — a worked example, fully discharged, exercising `polyTime_loop`

`wloop := prec (pair left right) wcg`: a `3`-iteration loop that CARRIES its seed `a` unchanged
(`wloop_const`), so `wloop ⟨n, 3⟩ = n`. Two features make it a genuine test rather than a triviality:
* NON-CONSTANT STEP. The step `wcg` outputs the accumulator unchanged, but its native cost runs a
  nested inner loop over the iteration INDEX `i` (`comp (prec zero zero) …`), so `tc wcg` GROWS with
  `i` (`wcg_tc_le`). Hence `tc wcg` is unbounded over all of `ℕ`; only `tc_prec_le'` (a bound over the
  visited `i < count n`) applies — the uniform `tc_prec_le` does NOT. This is the point of the repair.
* POLY-BIT ACCUMULATOR OF LARGE VALUE. With `astart = id` the accumulator is the seed `n` itself,
  whose VALUE is exponential in `Nat.size n` yet whose bit-length is `Nat.size n` — so `hacc` is the
  genuinely-scaling `PolyBounded Nat.size`, and the native cost never sees the accumulator magnitude.

Note on the count. `count = fun _ => 3` is a CONSTANT: a prec-free-computable, poly-bit, scaling count
does not exist (any prec-free code produces either a constant or an `n`-magnitude value), so a count
that both scales with `n` and stays poly-bit — the honest C2 template `count = input length` — must
itself be loop-computed. Here the count is constant while the accumulator scales; the two scaling
dimensions cannot both be prec-free. -/

/-- Worked-example step code: outputs the accumulator (`comp left (pair (comp right right) …)`) while
its cost runs a nested `i`-fold loop, making the per-step cost grow with the iteration index `i`. -/
def wcg : Code :=
  comp left (pair (comp right right) (comp (prec zero zero) (pair zero (comp left right))))

theorem rfindFree_wcg : RfindFree wcg := by
  simp only [wcg, RfindFree, and_self]

/-- `wcg` computes the accumulator slot `⟨_, ⟨_, acc⟩⟩ ↦ acc` (its value ignores the nested loop). -/
theorem wcg_val (x : ℕ) : val wcg x = (x.unpair.2).unpair.2 := by
  simp only [wcg, val_comp, val_pair, val_left, val_right, Nat.unpair_pair]

/-- The per-step cost of `wcg` grows LINEARLY with the iteration index `i = (x.unpair.2).unpair.1`
(the nested inner loop runs `i` times), so it is not uniformly bounded over all `x`. -/
theorem wcg_tc_le (x : ℕ) : tc wcg x ≤ 2 * (x.unpair.2).unpair.1 + 14 := by
  have hEi : val (pair zero (comp left right)) x = Nat.pair 0 ((x.unpair.2).unpair.1) := by
    simp only [val_pair, val_zero, val_comp, val_left, val_right]
  have hinner := tc_prec_le (cf := zero) (cg := zero) (B := 1)
    (fun y => le_of_eq (tc_zero y)) 0 ((x.unpair.2).unpair.1)
  simp only [tc_zero] at hinner
  simp only [wcg, tc_comp, tc_pair, tc_zero, tc_right, tc_left, hEi]
  omega

/-- The loop carries its seed unchanged: `prec (pair left right) wcg` on `⟨a, m⟩` returns `a`. -/
theorem wloop_const (a m : ℕ) : val (prec (pair left right) wcg) (Nat.pair a m) = a := by
  induction m with
  | zero => rw [val_prec_zero, val_pair, val_left, val_right, Nat.pair_unpair]
  | succ k ih => rw [val_prec_succ, wcg_val]; simpa only [Nat.unpair_pair] using ih

/-- **Worked example.** The `3`-iteration loop above is `PolyTime` via `polyTime_loop`; every premise
(`hA`, `hC`, `hCval`, `hbase`, `Bstep`/`hBstep`/`hstep`, `hacc`) is discharged concretely. The step
uses `tc_prec_le'` essentially — `wcg_tc_le` grows with `i`, so no uniform `tc_prec_le` bound exists —
and `hacc` is the scaling `PolyBounded Nat.size`. -/
theorem polyTime_loop_worked_example :
    PolyTime (fun n => val (prec (pair left right) wcg) (Nat.pair n 3)) := by
  have hcf : RfindFree (pair left right) := ⟨trivial, trivial⟩
  have hbase : PolyBounded (tc (pair left right)) :=
    PolyBounded.mono (fun n => le_of_eq (by rw [tc_pair, tc_left, tc_right])) (PolyBounded.const 3)
  refine polyTime_loop (cf := pair left right) (cg := wcg) hcf rfindFree_wcg
    (astart := fun n => n) (count := fun _ => 3) polyTime_id (polyTime_const 3)
    (PolyBounded.const 3) hbase (fun _ => 18) (PolyBounded.const 18) ?_ ?_
  · -- `hstep`: the visited per-step cost `≤ 2i + 14 ≤ 18` for `i < 3`
    intro n i hi
    have h := wcg_tc_le (Nat.pair n (Nat.pair i (val (prec (pair left right) wcg) (Nat.pair n i))))
    simp only [Nat.unpair_pair] at h
    omega
  · -- `hacc`: the loop returns its seed `n`, so the output bit-length is `Nat.size n`
    exact PolyBounded.mono (fun n => (congrArg Nat.size (wloop_const n 3)).le) PolyBounded.size

end TimeCost
