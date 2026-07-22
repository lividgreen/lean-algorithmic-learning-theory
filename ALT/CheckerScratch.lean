/-
Copyright (c) 2026 Mykola Palamarchuk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mykola Palamarchuk
-/
import ALT.TimeCost
import ALT.PolyTime
import ALT.GodelInternalization

-- Formal-check file, not Mathlib-destined: opt out of the house-style header linter.
set_option linter.style.header false

/-!
# The checker's scratch account: assembling the bounded-enumeration workspace bound

Provenance: [Decoupling] §5.4 (Remark, the per-constituent capacity bound) and §6.3 (Theorem 6.3,
and the Remark "time to the verdict").

Two accounts meet here.
`ALT/GodelInternalization.lean` bounds the §6.3 checker's memory *per constituent*: `capacity_bound`
hosts the enumerating recursor in `capacity n = 2n` work bits, and `proofcode_workspace_bound` fits
each candidate proof code `p ≤ M_chk` in the same `2n` — both stated as bit-lengths in the form
`Nat.clog 2 (· + 1)`.
`ALT/TimeCost.lean` supplies a native *workspace* measure `spaceCost` on the rfind'-free fragment of
`Nat.Partrec.Code`, whose bounded-recursion bound `spaceCost_prec_le` is a `max` — independent of
the iteration count, where the time bound `tc_prec_le'` is a sum linear in it.

This file assembles the two into the statement §6.3 needs about the enumeration *itself*: the
checker's loop over the `M_chk + 1` candidate proof codes runs in a workspace bounded independently
of `M_chk`, stated in §6.3's own bit-length vocabulary.

## The dictionary
The two accounts speak different dialects of one quantity: `Nat.size p` (the native measure) and
`Nat.clog 2 (p + 1)` (the capacity vocabulary). `size_eq_clog` proves them equal on the nose, so a
§6.3 capacity bound *is* a `spaceCost` hypothesis and conversely — no constant is lost in
translation.

## What enters as a hypothesis, and why
The per-candidate check is **not** modelled here: no checker code over `Nat.Partrec.Code` is
constructed, and the `Δ₀`/poly-time verification of a *held* candidate (Buss 1986) is the
paper-level input flagged in the [Decoupling] §5.4 Remark. It enters as the hypothesis `hstep` of
`checker_scratch_closure`: *given* that one step of the loop runs in `S` workspace whenever the
carried verdict occupies `S` bits, the assembled total is `max (spaceCost cf a) S`, with `M_chk`
absent. That boundary is the paper's own, and it is exactly where this formalization stops.

Note the shape of `hstep`: it is **conditioned** on the carried accumulator's bit-length. The
uniform form `∀ x, spaceCost cg x ≤ S` is unsatisfiable for a space measure — a leaf node holds its
input, so no constant bounds `Nat.size` over all inputs (the discussion at `spaceCost_prec_le`).

## The space/time contrast
`checker_space_time_contrast` puts the two costs of the same loop side by side, which is the
machine-checked form of the §6.3 Remark "time to the verdict": the budget hypothesis `M_chk ≤ g^2`
is consumed by the **time** half alone — `tc ≤ tc cf a + (B + 1)·g² + 1`, exhaustive search,
polynomial in the *value* `g` hence exponential in its bit-length — while the **space** half needs
no budget hypothesis at all and returns a bound in which `M_chk` does not occur.
-/

namespace CheckerScratch

open Nat.Partrec (Code)
open Nat.Partrec.Code
open TimeCost

/-! ## The dictionary: `Nat.size` is the capacity vocabulary's bit-length -/

/-- **The bit-length dictionary.** The native workspace measure counts bits with `Nat.size`; the
capacity account of [Decoupling] §5.4/§6.3 writes the same quantity as `⌈log₂(p+1)⌉`. They agree on
the nose: `Nat.size p ≤ k ↔ p < 2^k ↔ p + 1 ≤ 2^k ↔ Nat.clog 2 (p+1) ≤ k`, and a natural number is
determined by which `k` bound it. -/
theorem size_eq_clog (p : ℕ) : Nat.size p = Nat.clog 2 (p + 1) := by
  have key : ∀ k, Nat.size p ≤ k ↔ Nat.clog 2 (p + 1) ≤ k := by
    intro k
    rw [Nat.size_le, Nat.clog_le_iff_le_pow (by norm_num)]
    omega
  exact le_antisymm ((key _).2 le_rfl) ((key _).1 le_rfl)

/-- The capacity bound on a candidate proof code, in the native measure's vocabulary: for the
concrete budget `M_chk ≤ g²` of [Decoupling] §6.3, every candidate `p ≤ M_chk` occupies at most
`capacity n = 2n` bits, `n := ⌈log₂(g+1)⌉` the size of the Gödel sentence. This is
`GodelInternalization.proofcode_workspace_bound` read through `size_eq_clog`. -/
theorem proofcode_size_le_capacity (g Mchk : ℕ) (hM : Mchk ≤ g ^ 2) {p : ℕ} (hp : p ≤ Mchk) :
    Nat.size p ≤ GodelInternalization.capacity (Nat.clog 2 (g + 1)) := by
  rw [size_eq_clog]
  exact GodelInternalization.proofcode_workspace_bound g Mchk hM hp

/-! ## The closure: the enumeration's workspace does not grow with the budget -/

/-- **The scratch bound of the bounded enumeration ([Decoupling] §6.3).** The checker's loop is the
bounded recursion `prec cf cg` run to the budget `M_chk`. Given
* `hstep` — one step of the loop uses at most `S` workspace on a candidate `p ≤ M_chk` whenever the
  verdict `b` it carries occupies at most `S` bits; and
* `hverdict` — every verdict the loop actually carries does occupy at most `S` bits,

the whole enumeration runs in `max (spaceCost cf a) S` workspace. The content is the `max`: the
budget `M_chk` — the number of candidates enumerated — **does not appear in the bound**. Enumerating
more candidates costs more time (`checker_space_time_contrast`), never more space.

Both hypotheses are stated in the §6.3 vocabulary `⌈log₂(· + 1)⌉`, which is the bit-length in which
`capacity_bound` and `proofcode_workspace_bound` speak; `size_eq_clog` is the whole of the
translation into `spaceCost_prec_le`'s native measure.

The per-candidate `Δ₀`/poly-time check of a *held* candidate (Buss 1986) is not constructed here: it
is the paper-level input of the [Decoupling] §5.4 Remark, and it enters precisely as `hstep`. -/
theorem checker_scratch_closure {cf cg : Code} {S a Mchk : ℕ}
    (hstep : ∀ p b, p ≤ Mchk → Nat.clog 2 (b + 1) ≤ S →
      spaceCost cg (Nat.pair a (Nat.pair p b)) ≤ S)
    (hverdict : ∀ p, p ≤ Mchk →
      Nat.clog 2 (val (prec cf cg) (Nat.pair a p) + 1) ≤ S) :
    spaceCost (prec cf cg) (Nat.pair a Mchk) ≤ max (spaceCost cf a) S :=
  spaceCost_prec_le
    (fun p b hp hb => hstep p b hp (by rwa [← size_eq_clog]))
    (fun p hp => by rw [size_eq_clog]; exact hverdict p hp)

/-- **Space and time for the same enumeration ([Decoupling] §6.3, Remark "time to the verdict").**
The bounded checker's loop, priced twice:
* **space** — `max (spaceCost cf a) S`, the `M_chk`-free bound of `checker_scratch_closure`;
* **time** — `tc cf a + (B + 1)·g² + 1`, one bounded check per candidate.

The asymmetry is the point, and it is visible in the hypotheses: the budget hypothesis
`hM : M_chk ≤ g²` is consumed by the **time** half only. The space half never sees it, so no
polynomial in `g` can enter that bound. The verdict therefore costs a number of steps polynomial in
the *value* `g` — exponential in its bit-length `n = ⌈log₂(g+1)⌉`, there being `2^{Θ(n)}` candidate
codes to rule out — while the workspace stays `poly(n)`: the subsystem affords the verdict in
`poly(n)` space and pays exhaustive-search time for it.

`B` bounds the cost of one check on the states the loop actually visits (`htime`, the visited-states
form), so a step cost that grows with the accumulator is admissible. -/
theorem checker_space_time_contrast {cf cg : Code} {S B a g Mchk : ℕ}
    (hM : Mchk ≤ g ^ 2)
    (hstep : ∀ p b, p ≤ Mchk → Nat.size b ≤ S →
      spaceCost cg (Nat.pair a (Nat.pair p b)) ≤ S)
    (hverdict : ∀ p, p ≤ Mchk → Nat.size (val (prec cf cg) (Nat.pair a p)) ≤ S)
    (htime : ∀ p, p < Mchk →
      tc cg (Nat.pair a (Nat.pair p (val (prec cf cg) (Nat.pair a p)))) ≤ B) :
    spaceCost (prec cf cg) (Nat.pair a Mchk) ≤ max (spaceCost cf a) S ∧
      tc (prec cf cg) (Nat.pair a Mchk) ≤ tc cf a + (B + 1) * g ^ 2 + 1 := by
  refine ⟨spaceCost_prec_le hstep hverdict, ?_⟩
  have ht := tc_prec_le' (cf := cf) (cg := cg) (a := a) (B := B) Mchk htime
  have hmul : (B + 1) * Mchk ≤ (B + 1) * g ^ 2 := Nat.mul_le_mul_left _ hM
  omega

/-! ## Holding the loop's input: the pairing cost -/

/-- **Square pairing costs at most twice the wider component.** `Nat.pair x y` is Cantor's square
pairing (`y² + x` or `x² + x + y`), so it lands strictly below `(2^M)²` where `M` is the larger of
the two bit-lengths: `Nat.size (Nat.pair x y) ≤ 2M`. The constant `2` is attained (`x = 1, y = 0`
gives `Nat.pair 1 0 = 2`, of size `2 = 2·1`). Mathlib bounds `Nat.pair` monotonically but does not
state its bit-length. -/
theorem size_pair_le (x y : ℕ) :
    Nat.size (Nat.pair x y) ≤ 2 * max (Nat.size x) (Nat.size y) := by
  set M := max (Nat.size x) (Nat.size y) with hM
  have hx : x < 2 ^ M :=
    Nat.lt_of_lt_of_le (Nat.lt_size_self x)
      (Nat.pow_le_pow_right (by norm_num) (le_max_left _ _))
  have hy : y < 2 ^ M :=
    Nat.lt_of_lt_of_le (Nat.lt_size_self y)
      (Nat.pow_le_pow_right (by norm_num) (le_max_right _ _))
  rw [Nat.size_le]
  have hpow : (2 : ℕ) ^ (2 * M) = 2 ^ M * 2 ^ M := by rw [two_mul, pow_add]
  rw [hpow, Nat.pair]
  split
  · next h => nlinarith
  · next h => nlinarith

/-- **The loop's step input fits in linear capacity.** One iteration of the §6.3 checker is handed
`⟨a, ⟨p, b⟩⟩`: the sentence data `a`, a candidate code `p ≤ M_chk`, and the one-bit running verdict
`b ≤ 1`. With the sentence data itself within capacity, that packed input occupies
`≤ 4·capacity n + 4` bits — `poly(n)`, indeed linear in `n = ⌈log₂(g+1)⌉`. The additive slack
absorbs the degenerate `g = 0` case, where the capacity is `0` but a held bit still costs one.

*Fidelity note.* This `≈ 8n` figure prices `Nat.pair` — Cantor **square** pairing — applied twice.
It is not the paper's `≈ 4n` for holding the sentence and the current candidate together: that
figure is **concatenation** arithmetic (component bit-lengths add — `prodAsm_fitsIn`, FV-14), a
different packing. The two are not to be identified. -/
theorem checkerInput_size_le {g Mchk a p b : ℕ} (hM : Mchk ≤ g ^ 2) (hp : p ≤ Mchk) (hb : b ≤ 1)
    (ha : Nat.size a ≤ GodelInternalization.capacity (Nat.clog 2 (g + 1))) :
    Nat.size (Nat.pair a (Nat.pair p b)) ≤
      4 * GodelInternalization.capacity (Nat.clog 2 (g + 1)) + 4 := by
  have hpc : Nat.size p ≤ GodelInternalization.capacity (Nat.clog 2 (g + 1)) :=
    proofcode_size_le_capacity g Mchk hM hp
  have hbs : Nat.size b ≤ 1 := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hb with rfl | rfl <;> simp
  have h1 : Nat.size (Nat.pair p b) ≤ 2 * max (Nat.size p) (Nat.size b) := size_pair_le p b
  have h2 : Nat.size (Nat.pair a (Nat.pair p b)) ≤
      2 * max (Nat.size a) (Nat.size (Nat.pair p b)) := size_pair_le a _
  omega

/-! ## The loop's verdict agrees with the decision morphism -/

/-- The running verdict of the enumeration, in closed form. A bounded recursion whose base returns
`1` and whose step multiplies the carried verdict by `¬Prf(φ, p)` computes, at counter `k`, exactly
"no candidate below `k` was accepted". -/
theorem checkerLoop_val (C : GodelInternalization.BoundedChecker) (φ : C.Formula) {cf cg : Code}
    {a : ℕ} (hinit : val cf a = 1)
    (hstep : ∀ p b, val cg (Nat.pair a (Nat.pair p b)) = b * (if C.Prf φ p = true then 0 else 1)) :
    ∀ k, val (prec cf cg) (Nat.pair a k) = if ∀ p < k, C.Prf φ p = false then 1 else 0 := by
  intro k
  induction k with
  | zero => rw [val_prec_zero, hinit]; simp
  | succ m ih =>
      rw [val_prec_succ, hstep, ih]
      by_cases hk : C.Prf φ m = true
      · -- the candidate `m` is accepted: the verdict is extinguished, and stays so
        have hno : ¬ ∀ p < m + 1, C.Prf φ p = false := by
          intro h
          rw [h m (Nat.lt_succ_self m)] at hk
          exact Bool.false_ne_true hk
        rw [if_neg hno, if_pos hk, Nat.mul_zero]
      · have hkf : C.Prf φ m = false := by simpa using hk
        rw [if_neg hk, Nat.mul_one]
        by_cases hm : ∀ p < m, C.Prf φ p = false
        · have hall : ∀ p < m + 1, C.Prf φ p = false := by
            intro p hp
            rcases Nat.lt_succ_iff_lt_or_eq.1 hp with hp' | rfl
            · exact hm p hp'
            · exact hkf
          rw [if_pos hm, if_pos hall]
        · have hno : ¬ ∀ p < m + 1, C.Prf φ p = false :=
            fun h => hm fun p hp => h p (Nat.lt_succ_of_lt hp)
          rw [if_neg hm, if_neg hno]

/-- **The enumeration decides bounded non-provability ([Decoupling] §6.3, L2b).** The loop of
`checkerLoop_val`, run to counter `M_chk + 1`, returns `1` exactly when the decision morphism
`Decide` returns `true`: the native bounded recursion over `Nat.Partrec.Code` computes the same
verdict as the finite fold `⋀_{p ≤ M_chk} ¬Prf(φ, p)`.

The counter is `M_chk + 1`, not `M_chk`: `prec` at `⟨a, k⟩` runs its step at counters `0, …, k-1`,
while `Decide` folds over the `M_chk + 1` codes `p ≤ M_chk`. -/
theorem checkerLoop_val_decides (C : GodelInternalization.BoundedChecker) (φ : C.Formula)
    {cf cg : Code} {a : ℕ} (hinit : val cf a = 1)
    (hstep : ∀ p b, val cg (Nat.pair a (Nat.pair p b)) = b * (if C.Prf φ p = true then 0 else 1)) :
    val (prec cf cg) (Nat.pair a (C.Mchk + 1)) = 1 ↔ GodelInternalization.Decide C φ = true := by
  rw [checkerLoop_val C φ hinit hstep, GodelInternalization.decide_eq_true_iff]
  have hiff : (∀ p < C.Mchk + 1, C.Prf φ p = false) ↔ ∀ p ≤ C.Mchk, C.Prf φ p = false :=
    ⟨fun h p hp => h p (by omega), fun h p hp => h p (by omega)⟩
  by_cases h : ∀ p < C.Mchk + 1, C.Prf φ p = false
  · rw [if_pos h]
    exact ⟨fun _ => hiff.1 h, fun _ => rfl⟩
  · rw [if_neg h]
    exact ⟨fun hc => absurd hc (by omega), fun hc => absurd (hiff.2 hc) h⟩

end CheckerScratch
