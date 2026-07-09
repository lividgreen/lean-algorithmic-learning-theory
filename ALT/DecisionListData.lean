import Mathlib
import ALT.PolyTime

-- Tier-1 formal check, not Mathlib-destined: opt out of the house-style linters.
set_option linter.style.header false
set_option linter.style.longLine false

/-!
# Data layer for the 1-DL consistency solver (F20 Stage C2a)

Provenance: the native-cost-model workstream, stage C2a (parts 1 & 2). Builds on `ALT/PolyTime.lean` (`PolyTime`,
`PolyBounded`, the base/`comp` closures, `polyTime_loop`, `tc_prec_le'`, `exists_two_pow_gt_poly`).
Downstream: the greedy 1-decision-list consistency solver (Stage C2b), whose scan/peel loops iterate
over the `m` examples and `k` features.

## The decode-cost verdict, and the flag-cons PIVOT (Stage C2a-part-2, step 0)
An offset-cons encoding `cons e r = Nat.pair e r + 1` would need a predecessor to decode. There is no
primitive predecessor in the rfind'-free fragment; the smallest `cPred` (`prec`, recursing on the
value) iterates VALUE-many times, so `n ≤ tc cPred n` (`cpred_tc_ge`) and hence `tc cPred` is NOT
poly-bounded (`cPred_tc_not_polyBounded`) — a predecessor-based peel step is value-linear, so route
(a) FAILS. We therefore PIVOT to a **flag cons**: `nil = 0`, `cons e r = Nat.pair 1 (Nat.pair e r)`,
which decodes by pure `unpair` (flag `= left`, head `= left ∘ right`, tail `= right ∘ right`), all
`tc = O(1)`. The flag `1` disambiguates `nil` from `cons` and each cons still strictly grows
`Nat.size` (`size_cons_gt`), so the size bound re-proves cleanly.

## Encoding
`inst = Nat.pair k (Nat.pair m data)` — `k`, `m` are flat slots. `data` is a flag-cons list of `m`
examples; an example is `Nat.pair label fv` with `fv` a flag-cons list of `k` bits.

## What lands (C2a complete)
Part 1: encoding + `WF`, the flat accessors `cReadK`/`cReadM` (`PolyTime`, `tc = O(1)`), and the size
bound `readM/readK inst ≤ Nat.size inst` under `WF` (I2). Part 2: the decode-cost verdict + pivot; the
`peel` loop (`cPeel`, `O(1)`-`tc` step) and the indexed accessors `getExample`/`getLabel`/`getFeature`,
each `PolyTime` GIVEN a poly-bit index (`polyTime_peel`); and List-model correctness
(`getExample_encode`). See the report on the one residual — `polyTime_peel` needs the index's
`PolyBounded` as a HYPOTHESIS, since the natural index (`readM`) is only poly-bit under `WF`; that is
what C2b must thread.
-/

namespace OneDL

open Nat.Partrec (Code)
open Nat.Partrec.Code
open TimeCost

/-! ## Step 0 — the predecessor cost verdict: value-linear, hence the flag-cons pivot -/

/-- Every `prec` runs at least `n` unit steps on `Nat.pair a n` (each of the `n` successor unfoldings
charges `+1`). A magnitude-INDEPENDENT lower bound — the mirror of `tc_prec_le'`'s upper bound. -/
theorem tc_prec_ge (cf cg : Code) (a : ℕ) : ∀ n, n ≤ tc (prec cf cg) (Nat.pair a n) := by
  intro n
  induction n with
  | zero => omega
  | succ m ih => rw [tc_prec_succ]; omega

/-- The identity VALUE is not poly-bit: `¬ PolyBounded (fun n => n)` (the family `n = 2^j` outgrows
every polynomial in `Nat.size n`). Reuses `exists_two_pow_gt_poly`. -/
theorem id_not_polyBounded : ¬ PolyBounded (fun n => n) := by
  rintro ⟨C, k, h⟩
  obtain ⟨j, hj⟩ := exists_two_pow_gt_poly C k
  have hN : (2 : ℕ) ^ j ≤ C * (Nat.size (2 ^ j) + 1) ^ k + C := h (2 ^ j)
  have hsize : Nat.size (2 ^ j) + 1 ≤ 2 * j + 5 := by
    have h2 : Nat.size (2 ^ j) ≤ j + 1 :=
      Nat.size_le.mpr (Nat.pow_lt_pow_right (by norm_num) (Nat.lt_succ_self j))
    omega
  have hmono : C * (Nat.size (2 ^ j) + 1) ^ k + C ≤ C * (2 * j + 5) ^ k + C := by gcongr
  omega

/-- The smallest rfind'-free predecessor: `prec zero (comp left right)` recursing on the value returns
the previous index, i.e. `n - 1`. It first pairs `⟨0, n⟩` (the shaper `pair zero (pair left right)`). -/
def cPred : Code := comp (prec zero (comp left right)) (pair zero (pair left right))

theorem val_precpred (m : ℕ) : val (prec zero (comp left right)) (Nat.pair 0 m) = m - 1 := by
  cases m with
  | zero => rw [val_prec_zero]; rfl
  | succ k => rw [val_prec_succ]; simp [val_comp, val_left, val_right, Nat.unpair_pair]

theorem val_cPred (n : ℕ) : val cPred n = n - 1 := by
  have hval : val (pair zero (pair left right)) n = Nat.pair 0 n := by
    rw [val_pair, val_zero, val_pair, val_left, val_right, Nat.pair_unpair]
  change val (comp (prec zero (comp left right)) (pair zero (pair left right))) n = n - 1
  rw [val_comp, hval, val_precpred]

/-- **The verdict (lower bound).** `n ≤ tc cPred n`: the predecessor costs at least the VALUE of its
input — Θ(n), exponential in `Nat.size n`. -/
theorem cpred_tc_ge (n : ℕ) : n ≤ tc cPred n := by
  have hval : val (pair zero (pair left right)) n = Nat.pair 0 n := by
    rw [val_pair, val_zero, val_pair, val_left, val_right, Nat.pair_unpair]
  change n ≤ tc (comp (prec zero (comp left right)) (pair zero (pair left right))) n
  rw [tc_comp, hval]
  have := tc_prec_ge zero (comp left right) 0 n
  omega

/-- **The verdict.** The predecessor's native cost is NOT poly-bounded — route (a) (a predecessor-based
peel) is value-linear, forcing the flag-cons pivot below. -/
theorem cPred_tc_not_polyBounded : ¬ PolyBounded (tc cPred) :=
  fun h => id_not_polyBounded (PolyBounded.mono cpred_tc_ge h)

/-! ## The flag-cons list predicate and the instance layout -/

/-- `IsList L m`: `L` is a **flag-cons** list of length `m` (`nil = 0`, `cons e r = pair 1 (pair e r)`).
Structural — tracks length, which is all the count bound needs. -/
inductive IsList : ℕ → ℕ → Prop
  | nil : IsList 0 0
  | cons (e r m : ℕ) : IsList r m → IsList (Nat.pair 1 (Nat.pair e r)) (m + 1)

/-- `#features k`, directly readable as `inst.unpair.1`. -/
def readK (inst : ℕ) : ℕ := inst.unpair.1
/-- `#examples m`, directly readable as `(inst.unpair.2).unpair.1`. -/
def readM (inst : ℕ) : ℕ := (inst.unpair.2).unpair.1
/-- The example-list `data`, at `(inst.unpair.2).unpair.2`. -/
def readData (inst : ℕ) : ℕ := (inst.unpair.2).unpair.2

/-- The head example of `data` (flag-cons: `head = left ∘ right`). -/
def firstExample (inst : ℕ) : ℕ := ((readData inst).unpair.2).unpair.1
/-- The feature vector of the head example (`example = ⟨label, fv⟩`). -/
def firstFV (inst : ℕ) : ℕ := (firstExample inst).unpair.2

/-- **Well-formedness.** At least one example; `data` is a genuine length-`m` list; and the head
example's feature vector is a genuine length-`k` list. Under `WF`, both counts are `≤ Nat.size inst`. -/
def WF (inst : ℕ) : Prop :=
  0 < readM inst ∧ IsList (readData inst) (readM inst) ∧ IsList (firstFV inst) (readK inst)

/-! ## Growth: a length-`m` flag-cons list has `Nat.size ≥ m` -/

theorem left_le_pair (a b : ℕ) : a ≤ Nat.pair a b := by
  have := Nat.unpair_left_le (Nat.pair a b); rwa [Nat.unpair_pair] at this

theorem right_le_pair (a b : ℕ) : b ≤ Nat.pair a b := by
  have := Nat.unpair_right_le (Nat.pair a b); rwa [Nat.unpair_pair] at this

/-- Each flag-cons cell is at least twice its tail: `2·r ≤ Nat.pair 1 (Nat.pair e r)`. -/
theorem flagcons_ge (e r : ℕ) : 2 * r ≤ Nat.pair 1 (Nat.pair e r) := by
  have hry : r ≤ Nat.pair e r := right_le_pair e r
  set y := Nat.pair e r with hy
  unfold Nat.pair
  split_ifs with h
  · nlinarith [hry, h]
  · have hy1 : y ≤ 1 := Nat.le_of_not_lt h
    nlinarith [hry, hy1]

/-- Generic strict-`Nat.size` growth: `1 ≤ c` and `2·r ≤ c` give `Nat.size r < Nat.size c`. Via
`Nat.lt_size`: reduces to `2 ^ Nat.size r ≤ c`, and `2 ^ Nat.size r ≤ 2·r ≤ c` for `r ≥ 1`. -/
theorem size_lt_of_two_mul_le {c r : ℕ} (hc : 1 ≤ c) (h : 2 * r ≤ c) : Nat.size r < Nat.size c := by
  apply Nat.lt_size.mpr
  rcases Nat.eq_zero_or_pos r with hr | hr
  · subst hr; simpa using hc
  · have hs : 1 ≤ Nat.size r := Nat.size_pos.mpr hr
    have h1 : 2 ^ (Nat.size r - 1) ≤ r := Nat.lt_size.mp (by omega)
    have hpow : 2 ^ Nat.size r = 2 * 2 ^ (Nat.size r - 1) := by
      rw [← pow_succ', Nat.sub_add_cancel hs]
    omega

/-- **The key growth step.** A flag-cons cell strictly increases `Nat.size`. -/
theorem size_cons_gt (e r : ℕ) : Nat.size r < Nat.size (Nat.pair 1 (Nat.pair e r)) :=
  size_lt_of_two_mul_le (left_le_pair 1 _) (flagcons_ge e r)

/-- **Length ≤ bit-length.** A genuine length-`m` flag-cons list `L` has `m ≤ Nat.size L`. -/
theorem isList_len_le_size : ∀ {L m : ℕ}, IsList L m → m ≤ Nat.size L := by
  intro L m h
  induction h with
  | nil => simp
  | cons e r m _hr ih => have := size_cons_gt e r; omega

/-! ## The load-bearing size bound (I2): the counts are poly-bit under `WF` -/

theorem readData_le (inst : ℕ) : readData inst ≤ inst :=
  le_trans (Nat.unpair_right_le _) (Nat.unpair_right_le _)

theorem firstFV_le (inst : ℕ) : firstFV inst ≤ inst := by
  have e1 : firstFV inst ≤ firstExample inst := Nat.unpair_right_le _
  have e2 : firstExample inst ≤ (readData inst).unpair.2 := Nat.unpair_left_le _
  have e3 : (readData inst).unpair.2 ≤ readData inst := Nat.unpair_right_le _
  have e4 : readData inst ≤ inst := readData_le inst
  omega

/-- **KEY LEMMA (I2), examples.** On a well-formed instance the stored example count is poly-bit:
`readM inst ≤ Nat.size inst` — the value bound that discharges `polyTime_loop`'s `hCval`. -/
theorem readM_le_size (inst : ℕ) (h : WF inst) : readM inst ≤ Nat.size inst := by
  have h1 : readM inst ≤ Nat.size (readData inst) := isList_len_le_size h.2.1
  have h2 : Nat.size (readData inst) ≤ Nat.size inst := Nat.size_le_size (readData_le inst)
  omega

/-- **KEY LEMMA (I2), features.** Symmetrically, `readK inst ≤ Nat.size inst` under `WF`. -/
theorem readK_le_size (inst : ℕ) (h : WF inst) : readK inst ≤ Nat.size inst := by
  have h1 : readK inst ≤ Nat.size (firstFV inst) := isList_len_le_size h.2.2
  have h2 : Nat.size (firstFV inst) ≤ Nat.size inst := Nat.size_le_size (firstFV_le inst)
  omega

/-! ## Flat accessor `Code`s (rfind'-free, `tc = O(1)`), and their `PolyTime` certificates -/

/-- `k`-accessor: `left` (`tc = 1`). -/
def cReadK : Code := left
/-- `m`-accessor: `comp left right` (`tc = 3`). -/
def cReadM : Code := comp left right

theorem rfindFree_cReadK : RfindFree cReadK := trivial
theorem rfindFree_cReadM : RfindFree cReadM := ⟨trivial, trivial⟩

theorem val_cReadK (inst : ℕ) : val cReadK inst = readK inst := rfl
theorem val_cReadM (inst : ℕ) : val cReadM inst = readM inst := rfl

/-- The `k`-accessor is `PolyTime`. The WF-conditional VALUE bound is `readK_le_size`. -/
theorem polyTime_readK : PolyTime readK := by unfold readK; exact polyTime_left

/-- The `m`-accessor is `PolyTime`. The WF-conditional VALUE bound is `readM_le_size`. -/
theorem polyTime_readM : PolyTime readM := by
  unfold readM; exact polyTime_comp polyTime_left polyTime_right

/-! ## The peel loop and the indexed accessors -/

/-- Flag-cons tail: `right ∘ right`. -/
def tailL (L : ℕ) : ℕ := (L.unpair.2).unpair.2
/-- Flag-cons head (the current example): `left ∘ right`. -/
def headL (L : ℕ) : ℕ := (L.unpair.2).unpair.1

/-- `peel L i`: drop `i` list cells (`tailL` iterated `i` times). -/
def peel (L i : ℕ) : ℕ := tailL^[i] L

/-- The step `Code` for the peel loop: apply `tailL` to the accumulator. `tc = 7`, magnitude-INDEPENDENT
(pure `unpair` — the whole point of the flag-cons pivot). -/
def cTailStep : Code := comp (comp right right) (comp right right)
/-- The peel loop `Code`: `prec` with identity base and `cTailStep`. -/
def cPeel : Code := prec (pair left right) cTailStep

theorem tc_cTailStep (x : ℕ) : tc cTailStep x = 7 := rfl

theorem val_cTailStep (L i acc : ℕ) : val cTailStep (Nat.pair L (Nat.pair i acc)) = tailL acc := by
  simp only [cTailStep, val_comp, val_right, Nat.unpair_pair, tailL]

theorem val_cPeel (L i : ℕ) : val cPeel (Nat.pair L i) = peel L i := by
  unfold cPeel peel
  induction i with
  | zero => simp [val_prec_zero, val_pair, val_left, val_right, Nat.pair_unpair]
  | succ k ih => rw [val_prec_succ, val_cTailStep, ih, Function.iterate_succ_apply']

theorem tailL_le (L : ℕ) : tailL L ≤ L :=
  le_trans (Nat.unpair_right_le _) (Nat.unpair_right_le _)

theorem peel_le (L i : ℕ) : peel L i ≤ L := by
  unfold peel
  induction i with
  | zero => simp
  | succ k ih => rw [Function.iterate_succ_apply']; exact le_trans (tailL_le _) ih

/-- **The peel accessor is `PolyTime` given a poly-bit index.** For any `PolyTime` shaper `A` (initial
list) and index `C` that is ALSO poly-bit as a VALUE (`hCval`), `n ↦ peel (A n) (C n)` is `PolyTime`.
A direct `polyTime_loop` instance: `count = C` discharges `hCval`; the accumulator (a suffix) is
`≤ A n` (`peel_le`), so `hacc` is `A`'s size clause; the step cost is the constant `7` (`tc_cTailStep`)
— routed through `tc_prec_le'`. The `hCval` premise is the residual C2b must supply: the natural index
`readM` is poly-bit only under `WF`. -/
theorem polyTime_peel {A C : ℕ → ℕ} (hA : PolyTime A) (hC : PolyTime C) (hCval : PolyBounded C) :
    PolyTime (fun n => peel (A n) (C n)) := by
  obtain ⟨ca, hca_rf, hca_val, hca_tc, hAsize⟩ := hA
  have hA : PolyTime A := ⟨ca, hca_rf, hca_val, hca_tc, hAsize⟩
  have hcf : RfindFree (pair left right) := ⟨trivial, trivial⟩
  have hcg : RfindFree cTailStep := ⟨⟨trivial, trivial⟩, ⟨trivial, trivial⟩⟩
  have hbase : PolyBounded (tc (pair left right)) :=
    PolyBounded.mono (fun n => le_of_eq (by rw [tc_pair, tc_left, tc_right])) (PolyBounded.const 3)
  have hacc : PolyBounded
      (fun n => Nat.size (val (prec (pair left right) cTailStep) (Nat.pair (A n) (C n)))) := by
    refine PolyBounded.mono (fun n => ?_) hAsize
    rw [show val (prec (pair left right) cTailStep) (Nat.pair (A n) (C n)) = peel (A n) (C n) from
        val_cPeel (A n) (C n)]
    exact Nat.size_le_size (peel_le (A n) (C n))
  have key : (fun n => peel (A n) (C n))
      = (fun n => val (prec (pair left right) cTailStep) (Nat.pair (A n) (C n))) := by
    funext n; exact (val_cPeel (A n) (C n)).symm
  rw [key]
  refine polyTime_loop (cf := pair left right) (cg := cTailStep) hcf hcg
    (astart := A) (count := C) hA hC hCval hbase (fun _ => 7) (PolyBounded.const 7) ?_ hacc
  intro n i _hi
  rw [tc_cTailStep]

/-- `headL` is `PolyTime` (a flat `left ∘ right` read). -/
theorem polyTime_headL : PolyTime headL := by
  unfold headL; exact polyTime_comp polyTime_left polyTime_right

/-- **`getExample` is `PolyTime`** given a poly-bit index: `n ↦ headL (peel (A n) (C n))`. -/
theorem polyTime_getExample {A C : ℕ → ℕ} (hA : PolyTime A) (hC : PolyTime C) (hCval : PolyBounded C) :
    PolyTime (fun n => headL (peel (A n) (C n))) :=
  polyTime_comp polyTime_headL (polyTime_peel hA hC hCval)

/-- **`getLabel` is `PolyTime`** given a poly-bit index: the label is `(example).unpair.1`. -/
theorem polyTime_getLabel {A C : ℕ → ℕ} (hA : PolyTime A) (hC : PolyTime C) (hCval : PolyBounded C) :
    PolyTime (fun n => (headL (peel (A n) (C n))).unpair.1) :=
  polyTime_comp polyTime_left (polyTime_getExample hA hC hCval)

/-- **`getFeature` is `PolyTime`** given poly-bit indices `Ci` (example) and `Cj` (feature): peel the
`i`-th example's feature vector `Cj n` times and read the head bit. A second `polyTime_peel`, with the
inner shaper being `getExample`'s feature-vector projection (itself `PolyTime`). -/
theorem polyTime_getFeature {A Ci Cj : ℕ → ℕ}
    (hA : PolyTime A) (hCi : PolyTime Ci) (hCival : PolyBounded Ci)
    (hCj : PolyTime Cj) (hCjval : PolyBounded Cj) :
    PolyTime (fun n => headL (peel ((headL (peel (A n) (Ci n))).unpair.2) (Cj n))) :=
  polyTime_comp polyTime_headL
    (polyTime_peel (polyTime_comp polyTime_right (polyTime_getExample hA hCi hCival)) hCj hCjval)

/-! ## Correctness against a `List` model -/

/-- Encode a `List ℕ` as a flag-cons list. -/
def encodeList : List ℕ → ℕ
  | [] => 0
  | (x :: xs) => Nat.pair 1 (Nat.pair x (encodeList xs))

theorem isList_encode (xs : List ℕ) : IsList (encodeList xs) xs.length := by
  induction xs with
  | nil => exact IsList.nil
  | cons x xs ih => exact IsList.cons x (encodeList xs) xs.length ih

theorem headL_encode_cons (x : ℕ) (xs : List ℕ) : headL (encodeList (x :: xs)) = x := by
  simp [headL, encodeList, Nat.unpair_pair]

theorem tailL_encode_cons (x : ℕ) (xs : List ℕ) : tailL (encodeList (x :: xs)) = encodeList xs := by
  simp [tailL, encodeList, Nat.unpair_pair]

theorem tailL_zero : tailL 0 = 0 := by simp [tailL, Nat.unpair_zero]

theorem peel_zero (i : ℕ) : peel 0 i = 0 := by
  unfold peel; exact Function.iterate_fixed tailL_zero i

/-- **Peel = drop.** Peeling `i` cells off an encoded list drops its first `i` elements. -/
theorem peel_encode (i : ℕ) : ∀ xs : List ℕ, peel (encodeList xs) i = encodeList (xs.drop i) := by
  induction i with
  | zero => intro xs; simp [peel]
  | succ k ih =>
      intro xs
      have hstep : peel (encodeList xs) (k + 1) = peel (tailL (encodeList xs)) k := by
        simp only [peel, Function.iterate_succ_apply]
      rw [hstep]
      cases xs with
      | nil => simp only [encodeList, tailL_zero, peel_zero, List.drop_nil]
      | cons y ys => rw [tailL_encode_cons, ih ys, List.drop_succ_cons]

/-- **`getExample` correctness.** Under the `List` model, `headL (peel (encodeList xs) i)` is the
`i`-th element `xs[i]` (for `i < xs.length`). Label/feature access follow by `unpair`/a second peel. -/
theorem getExample_encode (xs : List ℕ) (i : ℕ) (h : i < xs.length) :
    headL (peel (encodeList xs) i) = xs[i] := by
  rw [peel_encode, List.drop_eq_getElem_cons h, headL_encode_cons]

/-- **`getLabel` correctness.** With each example encoded as `⟨label, fv⟩`, the `i`-th label is
`(xs[i]).unpair.1`. -/
theorem getLabel_encode (xs : List ℕ) (i : ℕ) (h : i < xs.length) :
    (headL (peel (encodeList xs) i)).unpair.1 = (xs[i]).unpair.1 := by
  rw [getExample_encode xs i h]

end OneDL
