/-
Copyright (c) 2026 Mykola Palamarchuk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mykola Palamarchuk
-/
module

public import ALT.HindsightCount

-- Formal-check file, not Mathlib-destined: opt out of the house-style header linter.
set_option linter.style.header false

/-!
# The hindsight count of a reading, and a window's count against its end readings' and columns'

Extends [Guests] §7 Proposition 7.26, clause (ii), the driven interior, and is registered as
[Guests] §7 Proposition 7.27, clauses (ii) and (iii), row GV-39.

`HindsightCount.lean`'s hindsight count answers the next state itself from the last `k` states;
this file answers instead a fixed READING of the next state — a function `π` of it — and compares
the two at a table rule's window. At a positive memory a window's hindsight count is at least each
of its two end readings' counts and at most their sum, which is in turn at most the sum of its two
end columns' hindsight counts. The positive memory is load-bearing in the upper bound, and the end
columns' own counts give the window no lower bound. The same sandwich holds at a window that
translates at a rational speed at most one, once its content is paired with the phase of its own
schedule and the leading end reads two cells.

One new condition is minted here. The **hindsight count of a reading** is the least number of
misses, over the functions of the last `k` states, in answering a fixed function of the next state
(`readingCount`); `HindsightCount.hindsightCount` is its case at the identity reading.

## Main results

* `readingMisses`, `readingCount` — the reading form of `HindsightCount.lawMisses`/`hindsightCount`.
  `readingCount_id` recovers that count at the identity reading;
  `readingCount_le_hindsightCount` and `readingCount_le_hindsightCount_comp` bound a reading's
  count by the state's own hindsight count, directly and through the read sequence.
* `hindsightCount_observedWindow_le_add_readingCount` — at a positive memory, a table rule's window
  hindsight count is at most the sum of its two end readings' counts.
  `hindsightCount_observedWindow_le_add_columns` is the same bound through the end columns'
  hindsight counts, via `readingCount_le_hindsightCount_comp`.
* `hindsightCount_observedWindow_zero_memory_guard` — the guard: the positive-memory hypothesis is
  load-bearing.
* `hindsightCount_observedWindow_lt_column_f170` — the guard: the two end columns give the window's
  hindsight count no lower bound.
* `movingWindow`, `hindsightCount_movingWindow_le_add_readingCount` — the translating window, its
  content paired with the phase `t % q` of its schedule, and at a positive memory and a speed
  `p / q ≤ 1` its hindsight count is at most the sum of its two end readings' counts, the trailing
  cell's and the two leading cells'; `hindsightCount_movingWindow_le_add_readingCount_nonvacuous`
  meets the four hypotheses at table `90`.
* `hindsightCount_movingWindow_zero_memory_guard` — the guard: the positive memory is load-bearing
  at the translating window as well, where at the zero table the phase alone changes.

## Scope

Registered as [Guests] §7 Proposition 7.27, clauses (ii) and (iii), row GV-39; [Guests] §7
Proposition 7.26, clause (ii) is what is extended. The window theorems, the translating window's
included, are stated at a general table rule `tableRule f hq`, never specialized beyond the
witnesses' and guards' own tables.
-/


@[expose] public section

namespace WindowCount

open ExtremeTapWidth EndpointClasses
open ObservedColumn (observedColumn hq90)
open DrivenColumns
open HindsightCount

/-! ## Piece 1: the hindsight count of a reading -/

/-- **How often a fixed law on the last `k` readings misses a fixed reading of the next state**,
before horizon `T`. -/
noncomputable def readingMisses {α β : Type*} [DecidableEq β] (k : ℕ) (π : α → β)
    (L : (Fin k → α) → β) (x : ℕ → α) (T : ℕ) : ℕ :=
  ((Finset.range T).filter fun t => L (fun i => x (t + (i : ℕ))) ≠ π (x (t + k))).card

/-- **The hindsight count of a reading**: the fewest misses any law on the last `k` readings makes
answering a fixed reading of the next state, before `T`. -/
noncomputable def readingCount {α β : Type*} [DecidableEq β] (k : ℕ) (π : α → β)
    (x : ℕ → α) (T : ℕ) : ℕ :=
  ⨅ L : (Fin k → α) → β, readingMisses k π L x T

/-- **The identity reading recovers the hindsight count.** -/
theorem readingCount_id {α : Type*} [DecidableEq α] (k : ℕ) (x : ℕ → α) (T : ℕ) :
    readingCount k (fun a : α => a) x T = hindsightCount k x T := rfl

/-- **A reading never misses more than the state itself does**: a law `L` for the state gives the
law `π ∘ L` for the reading, which misses only where `L` does. -/
theorem readingCount_le_hindsightCount {α β : Type*} [DecidableEq α] [DecidableEq β]
    (k : ℕ) (π : α → β) (x : ℕ → α) (T : ℕ) :
    readingCount k π x T ≤ hindsightCount k x T := by
  have hne : Nonempty α := ⟨x 0⟩
  obtain ⟨L, hL⟩ := ciInf_mem (fun L : (Fin k → α) → α => lawMisses k L x T)
  have hsub : ((Finset.range T).filter fun t => (π ∘ L) (fun i => x (t + (i : ℕ))) ≠ π (x (t + k)))
      ⊆ (Finset.range T).filter fun t => L (fun i => x (t + (i : ℕ))) ≠ x (t + k) := by
    intro t ht
    simp only [Finset.mem_filter, Finset.mem_range, Function.comp_apply] at ht ⊢
    exact ⟨ht.1, fun hEq => ht.2 (by rw [hEq])⟩
  calc readingCount k π x T ≤ readingMisses k π (π ∘ L) x T := ciInf_le' _ (π ∘ L)
    _ ≤ lawMisses k L x T := Finset.card_le_card hsub
    _ = hindsightCount k x T := hL

/-- **A reading of the state's own sequence never misses more than the state's own hindsight count
of the READ sequence**: a law on the read sequence's history is a law on the state's history that
reads it through `π`, with the same misses. -/
theorem readingCount_le_hindsightCount_comp {α β : Type*} [DecidableEq β]
    (k : ℕ) (π : α → β) (x : ℕ → α) (T : ℕ) :
    readingCount k π x T ≤ hindsightCount k (fun t => π (x t)) T := by
  have hne : Nonempty β := ⟨π (x 0)⟩
  obtain ⟨M, hM⟩ := ciInf_mem
    (fun M : (Fin k → β) → β => lawMisses k M (fun t => π (x t)) T)
  calc readingCount k π x T
      ≤ readingMisses k π (fun w : Fin k → α => M (fun i => π (w i))) x T :=
        ciInf_le' _ (fun w : Fin k → α => M (fun i => π (w i)))
    _ = lawMisses k M (fun t => π (x t)) T := rfl
    _ = hindsightCount k (fun t => π (x t)) T := hM

/-! ## Piece 2: the window of a table rule -/

/-- **The window's law, built from an end pair**: cell `0` by `La`, cell `Fin.last m` by `Lb`, and
every interior cell by the table at the LAST content read (the memory hypothesis `hk` names the
index). -/
private noncomputable def windowLawOf (f : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2) {m k : ℕ}
    (hk : 0 < k) (La Lb : (Fin k → (Fin (m + 1) → ZMod 2)) → ZMod 2) :
    (Fin k → (Fin (m + 1) → ZMod 2)) → (Fin (m + 1) → ZMod 2) :=
  fun hist j =>
    if hj0 : (j : ℕ) = 0 then La hist
    else if hjm : (j : ℕ) = m then Lb hist
    else f (hist ⟨k - 1, by omega⟩ ⟨(j : ℕ) - 1, by have := j.isLt; omega⟩)
           (hist ⟨k - 1, by omega⟩ j)
           (hist ⟨k - 1, by omega⟩ ⟨(j : ℕ) + 1, by have := j.isLt; omega⟩)

theorem hindsightCount_observedWindow_le_add_readingCount
    (f : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2) (hq : f 0 0 0 = 0) (s₀ : ℤ →₀ ZMod 2)
    (a : ℤ) (m : ℕ) {k : ℕ} (hk : 0 < k) (T : ℕ) :
    hindsightCount k (observedWindow (tableRule f hq) s₀ a (m + 1)) T ≤
      readingCount k (fun w : Fin (m + 1) → ZMod 2 => w 0)
          (observedWindow (tableRule f hq) s₀ a (m + 1)) T +
      readingCount k (fun w : Fin (m + 1) → ZMod 2 => w (Fin.last m))
          (observedWindow (tableRule f hq) s₀ a (m + 1)) T := by
  classical
  set wseq : ℕ → (Fin (m + 1) → ZMod 2) := observedWindow (tableRule f hq) s₀ a (m + 1)
    with hwseq_def
  obtain ⟨La, hLa⟩ := ciInf_mem
    (fun L : (Fin k → (Fin (m + 1) → ZMod 2)) → ZMod 2 =>
      readingMisses k (fun w : Fin (m + 1) → ZMod 2 => w 0) L wseq T)
  obtain ⟨Lb, hLb⟩ := ciInf_mem
    (fun L : (Fin k → (Fin (m + 1) → ZMod 2)) → ZMod 2 =>
      readingMisses k (fun w : Fin (m + 1) → ZMod 2 => w (Fin.last m)) L wseq T)
  have hmiss : ∀ t ∈ Finset.range T,
      La (fun i => wseq (t + (i : ℕ))) = wseq (t + k) 0 →
      Lb (fun i => wseq (t + (i : ℕ))) = wseq (t + k) (Fin.last m) →
      windowLawOf f hk La Lb (fun i => wseq (t + (i : ℕ))) = wseq (t + k) := by
    intro t _ hAeq hBeq
    have hlast : wseq (t + (k - 1)) = wseq (t + k - 1) := by congr 1; omega
    funext j
    simp only [windowLawOf]
    split_ifs with hj0 hjm
    · have hje : j = 0 := Fin.ext hj0
      rw [hje]; exact hAeq
    · have hje : j = Fin.last m := Fin.ext (by rw [Fin.val_last]; exact hjm)
      rw [hje]; exact hBeq
    · rw [hlast]
      have hjge : 1 ≤ (j : ℕ) := Nat.one_le_iff_ne_zero.mpr hj0
      have hjlt : (j : ℕ) < m := by have := j.isLt; omega
      have e1 : a + ((j : ℕ) : ℤ) - 1 = a + (((j : ℕ) - 1 : ℕ) : ℤ) := by push_cast [hjge]; ring
      have e2 : a + ((j : ℕ) : ℤ) + 1 = a + (((j : ℕ) + 1 : ℕ) : ℤ) := by push_cast; ring
      change f (wseq (t + k - 1) ⟨(j : ℕ) - 1, by omega⟩)
        (wseq (t + k - 1) j) (wseq (t + k - 1) ⟨(j : ℕ) + 1, by omega⟩) = wseq (t + k) j
      change f (((tableRule f hq)^[t + k - 1] s₀) (a + (((j : ℕ) - 1 : ℕ) : ℤ)))
            (((tableRule f hq)^[t + k - 1] s₀) (a + ((j : ℕ) : ℤ)))
            (((tableRule f hq)^[t + k - 1] s₀) (a + (((j : ℕ) + 1 : ℕ) : ℤ)))
        = ((tableRule f hq)^[t + k] s₀) (a + ((j : ℕ) : ℤ))
      rw [← e1, ← e2]
      conv_rhs => rw [show t + k = (t + k - 1) + 1 by omega]
      rw [Function.iterate_succ_apply', tableRule_apply]
  have hsub : ((Finset.range T).filter fun t =>
        windowLawOf f hk La Lb (fun i => wseq (t + (i : ℕ))) ≠ wseq (t + k))
      ⊆ ((Finset.range T).filter fun t =>
            La (fun i => wseq (t + (i : ℕ))) ≠ wseq (t + k) 0) ∪
        ((Finset.range T).filter fun t =>
            Lb (fun i => wseq (t + (i : ℕ))) ≠ wseq (t + k) (Fin.last m)) := by
    intro t ht
    simp only [Finset.mem_filter, Finset.mem_range] at ht
    obtain ⟨htT, htne⟩ := ht
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_range]
    by_contra hc
    push Not at hc
    exact htne (hmiss t (Finset.mem_range.mpr htT) (hc.1 htT) (hc.2 htT))
  have hLa' : readingMisses k (fun w : Fin (m + 1) → ZMod 2 => w 0) La wseq T =
      readingCount k (fun w : Fin (m + 1) → ZMod 2 => w 0) wseq T := hLa
  have hLb' : readingMisses k (fun w : Fin (m + 1) → ZMod 2 => w (Fin.last m)) Lb wseq T =
      readingCount k (fun w : Fin (m + 1) → ZMod 2 => w (Fin.last m)) wseq T := hLb
  calc hindsightCount k wseq T
      ≤ lawMisses k (windowLawOf f hk La Lb) wseq T := ciInf_le' _ (windowLawOf f hk La Lb)
    _ ≤ readingMisses k (fun w : Fin (m + 1) → ZMod 2 => w 0) La wseq T +
        readingMisses k (fun w : Fin (m + 1) → ZMod 2 => w (Fin.last m)) Lb wseq T := by
        calc lawMisses k (windowLawOf f hk La Lb) wseq T
            ≤ (((Finset.range T).filter fun t =>
                  La (fun i => wseq (t + (i : ℕ))) ≠ wseq (t + k) 0) ∪
                ((Finset.range T).filter fun t =>
                  Lb (fun i => wseq (t + (i : ℕ))) ≠ wseq (t + k) (Fin.last m))).card :=
              Finset.card_le_card hsub
          _ ≤ _ + _ := Finset.card_union_le _ _
    _ = readingCount k (fun w : Fin (m + 1) → ZMod 2 => w 0) wseq T +
        readingCount k (fun w : Fin (m + 1) → ZMod 2 => w (Fin.last m)) wseq T := by
        rw [hLa', hLb']

/-- **The window's count-currency form through the columns**: the readings bound followed by
`readingCount_le_hindsightCount_comp` at each end, the end coordinate of the window
being the observed column at that cell. -/
theorem hindsightCount_observedWindow_le_add_columns
    (f : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2) (hq : f 0 0 0 = 0) (s₀ : ℤ →₀ ZMod 2)
    (a : ℤ) (m : ℕ) {k : ℕ} (hk : 0 < k) (T : ℕ) :
    hindsightCount k (observedWindow (tableRule f hq) s₀ a (m + 1)) T ≤
      hindsightCount k (observedColumn (tableRule f hq) s₀ a) T +
      hindsightCount k (observedColumn (tableRule f hq) s₀ (a + (m : ℤ))) T := by
  have h1 := hindsightCount_observedWindow_le_add_readingCount f hq s₀ a m hk T
  have hcolA : (fun t => (fun w : Fin (m + 1) → ZMod 2 => w 0)
      (observedWindow (tableRule f hq) s₀ a (m + 1) t)) = observedColumn (tableRule f hq) s₀ a := by
    funext t
    simp [observedWindow, observedColumn]
  have hcolB : (fun t => (fun w : Fin (m + 1) → ZMod 2 => w (Fin.last m))
      (observedWindow (tableRule f hq) s₀ a (m + 1) t)) =
      observedColumn (tableRule f hq) s₀ (a + (m : ℤ)) := by
    funext t
    simp [observedWindow, observedColumn, Fin.last]
  have h2 := readingCount_le_hindsightCount_comp k (fun w : Fin (m + 1) → ZMod 2 => w 0)
    (observedWindow (tableRule f hq) s₀ a (m + 1)) T
  have h3 := readingCount_le_hindsightCount_comp k
    (fun w : Fin (m + 1) → ZMod 2 => w (Fin.last m))
    (observedWindow (tableRule f hq) s₀ a (m + 1)) T
  rw [hcolA] at h2
  rw [hcolB] at h3
  omega

/-! ## The translating window: the sandwich at a rational speed -/

/-- **The translating window with its phase**: at step `t`, the `n` cells from `a + ⌊p t / q⌋`
read together, paired with the phase `t % q` of the window's own schedule. At `p = 0` the content
is `DrivenColumns.observedWindow`'s. -/
def movingWindow (U : (ℤ →₀ ZMod 2) → (ℤ →₀ ZMod 2)) (s₀ : ℤ →₀ ZMod 2) (a : ℤ) (p q n : ℕ) :
    ℕ → (Fin n → ZMod 2) × ℕ :=
  fun t => (fun j => (U^[t] s₀) (a + ((p * t / q : ℕ) : ℤ) + ((j : ℕ) : ℤ)), t % q)

/-- The position `⌊p t / q⌋` splits along `t = t % q + q (t / q)`. -/
private theorem mul_div_eq_mod (p q t : ℕ) (hq0 : 0 < q) :
    p * t / q = p * (t % q) / q + p * (t / q) := by
  conv_lhs => rw [← Nat.mod_add_div t q]
  rw [Nat.mul_add, mul_left_comm, Nat.add_mul_div_left _ _ hq0]

/-- The next position `⌊p (t + 1) / q⌋` splits along the same phase `t % q`, so the move this
step is read off the phase alone. -/
private theorem mul_succ_div_eq (p q t : ℕ) (hq0 : 0 < q) :
    p * (t + 1) / q = p * (t % q + 1) / q + p * (t / q) := by
  have h : t + 1 = (t % q + 1) + q * (t / q) := by have := Nat.mod_add_div t q; omega
  rw [h, Nat.mul_add, mul_left_comm, Nat.add_mul_div_left _ _ hq0]

/-- At a speed at most one, the position moves by at most one cell a step. -/
private theorem div_succ_le (p q r : ℕ) (hq0 : 0 < q) (hpq : p ≤ q) :
    p * (r + 1) / q ≤ p * r / q + 1 := by
  calc p * (r + 1) / q ≤ (p * r + q) / q := Nat.div_le_div_right (by rw [Nat.mul_succ]; omega)
    _ = p * r / q + 1 := Nat.add_div_right _ hq0

/-- **The translating window's law, built from an end pair**: cell `0` by `La`, the two leading
cells by `Lb`, the move this step read off the LAST state's phase, and every other cell by the
table at the last content — one cell further along when the window moves (the memory hypothesis
`hk` names the index). -/
private noncomputable def movingLawOf (f : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2) {m k : ℕ}
    (hk : 0 < k) (p q : ℕ)
    (La : (Fin k → (Fin (m + 3) → ZMod 2) × ℕ) → ZMod 2)
    (Lb : (Fin k → (Fin (m + 3) → ZMod 2) × ℕ) → ZMod 2 × ZMod 2) :
    (Fin k → (Fin (m + 3) → ZMod 2) × ℕ) → (Fin (m + 3) → ZMod 2) × ℕ :=
  fun hist =>
    (fun j =>
      if hj0 : (j : ℕ) = 0 then La hist
      else if hj1 : (j : ℕ) = m + 1 then (Lb hist).1
      else if hj2 : (j : ℕ) = m + 2 then (Lb hist).2
      else if p * (hist ⟨k - 1, by omega⟩).2 / q < p * ((hist ⟨k - 1, by omega⟩).2 + 1) / q then
        f ((hist ⟨k - 1, by omega⟩).1 j)
          ((hist ⟨k - 1, by omega⟩).1 ⟨(j : ℕ) + 1, by have := j.isLt; omega⟩)
          ((hist ⟨k - 1, by omega⟩).1 ⟨(j : ℕ) + 2, by have := j.isLt; omega⟩)
      else
        f ((hist ⟨k - 1, by omega⟩).1 ⟨(j : ℕ) - 1, by have := j.isLt; omega⟩)
          ((hist ⟨k - 1, by omega⟩).1 j)
          ((hist ⟨k - 1, by omega⟩).1 ⟨(j : ℕ) + 1, by have := j.isLt; omega⟩),
     ((hist ⟨k - 1, by omega⟩).2 + 1) % q)

/-- **The window's count at a rational speed is at most the sum of its two end readings'.** The
window's next content is one fixed function of its last content, its phase and the two end
readings: the phase says whether the window moves this step (`⌊p (t + 1) / q⌋ − ⌊p t / q⌋`
depends on `t % q` alone), every cell strictly inside has its neighbourhood inside either way, the
trailing end's next cell is its own reading, and the leading end's two cells are its
([Guests] §7 Proposition 7.27's sandwich, rows GV-38 and GV-39, at a window whose ends move). -/
theorem hindsightCount_movingWindow_le_add_readingCount
    (f : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2) (hq : f 0 0 0 = 0) (s₀ : ℤ →₀ ZMod 2) (a : ℤ)
    {p q : ℕ} (hq0 : 0 < q) (hpq : p ≤ q) (m : ℕ) {k : ℕ} (hk : 0 < k) (T : ℕ) :
    hindsightCount k (movingWindow (tableRule f hq) s₀ a p q (m + 3)) T ≤
      readingCount k (fun w : (Fin (m + 3) → ZMod 2) × ℕ => w.1 0)
          (movingWindow (tableRule f hq) s₀ a p q (m + 3)) T +
      readingCount k
          (fun w : (Fin (m + 3) → ZMod 2) × ℕ => (w.1 ⟨m + 1, by omega⟩, w.1 (Fin.last (m + 2))))
          (movingWindow (tableRule f hq) s₀ a p q (m + 3)) T := by
  classical
  set wseq : ℕ → (Fin (m + 3) → ZMod 2) × ℕ := movingWindow (tableRule f hq) s₀ a p q (m + 3)
    with hwseq_def
  obtain ⟨La, hLa⟩ := ciInf_mem
    (fun L : (Fin k → (Fin (m + 3) → ZMod 2) × ℕ) → ZMod 2 =>
      readingMisses k (fun w : (Fin (m + 3) → ZMod 2) × ℕ => w.1 0) L wseq T)
  obtain ⟨Lb, hLb⟩ := ciInf_mem
    (fun L : (Fin k → (Fin (m + 3) → ZMod 2) × ℕ) → ZMod 2 × ZMod 2 =>
      readingMisses k
        (fun w : (Fin (m + 3) → ZMod 2) × ℕ => (w.1 ⟨m + 1, by omega⟩, w.1 (Fin.last (m + 2))))
        L wseq T)
  have hmiss : ∀ t ∈ Finset.range T,
      La (fun i => wseq (t + (i : ℕ))) = (wseq (t + k)).1 0 →
      Lb (fun i => wseq (t + (i : ℕ))) =
        ((wseq (t + k)).1 ⟨m + 1, by omega⟩, (wseq (t + k)).1 (Fin.last (m + 2))) →
      movingLawOf f hk p q La Lb (fun i => wseq (t + (i : ℕ))) = wseq (t + k) := by
    intro t _ hAeq hBeq
    obtain ⟨u, hu⟩ : ∃ u, t + k = u + 1 := ⟨t + k - 1, by omega⟩
    rw [hu] at hAeq hBeq ⊢
    have hlast : wseq (t + (k - 1)) = wseq u := by congr 1; omega
    have hpos := mul_succ_div_eq p q u hq0
    have hpos' := mul_div_eq_mod p q u hq0
    have hmono : p * (u % q) / q ≤ p * (u % q + 1) / q :=
      Nat.div_le_div_right (Nat.mul_le_mul_left _ (Nat.le_succ _))
    have hle := div_succ_le p q (u % q) hq0 hpq
    refine Prod.ext ?_ ?_
    · funext j
      simp only [movingLawOf]
      split_ifs with hj0 hj1 hj2 hmv
      · have hje : j = 0 := Fin.ext hj0
        rw [hje]; exact hAeq
      · have hje : j = ⟨m + 1, by omega⟩ := Fin.ext hj1
        rw [hje]; exact congrArg Prod.fst hBeq
      · have hje : j = Fin.last (m + 2) := Fin.ext (by rw [Fin.val_last]; exact hj2)
        rw [hje]; exact congrArg Prod.snd hBeq
      · -- the window moves this step
        rw [hlast] at hmv ⊢
        change p * (u % q) / q < p * (u % q + 1) / q at hmv
        have hstep : p * (u + 1) / q = p * u / q + 1 := by rw [hpos, hpos']; omega
        have hjlt : (j : ℕ) < m + 1 := by have := j.isLt; omega
        change f (((tableRule f hq)^[u] s₀) (a + ((p * u / q : ℕ) : ℤ) + ((j : ℕ) : ℤ)))
            (((tableRule f hq)^[u] s₀) (a + ((p * u / q : ℕ) : ℤ) + (((j : ℕ) + 1 : ℕ) : ℤ)))
            (((tableRule f hq)^[u] s₀) (a + ((p * u / q : ℕ) : ℤ) + (((j : ℕ) + 2 : ℕ) : ℤ)))
          = ((tableRule f hq)^[u + 1] s₀) (a + ((p * (u + 1) / q : ℕ) : ℤ) + ((j : ℕ) : ℤ))
        rw [hstep, Function.iterate_succ_apply', tableRule_apply]
        congr 2 <;> push_cast <;> ring
      · -- the window stays this step
        rw [hlast] at hmv ⊢
        change ¬ p * (u % q) / q < p * (u % q + 1) / q at hmv
        have hstep : p * (u + 1) / q = p * u / q := by rw [hpos, hpos']; omega
        have hjge : 1 ≤ (j : ℕ) := Nat.one_le_iff_ne_zero.mpr hj0
        have hjlt : (j : ℕ) < m + 2 := by have := j.isLt; omega
        change f (((tableRule f hq)^[u] s₀) (a + ((p * u / q : ℕ) : ℤ) + (((j : ℕ) - 1 : ℕ) : ℤ)))
            (((tableRule f hq)^[u] s₀) (a + ((p * u / q : ℕ) : ℤ) + ((j : ℕ) : ℤ)))
            (((tableRule f hq)^[u] s₀) (a + ((p * u / q : ℕ) : ℤ) + (((j : ℕ) + 1 : ℕ) : ℤ)))
          = ((tableRule f hq)^[u + 1] s₀) (a + ((p * (u + 1) / q : ℕ) : ℤ) + ((j : ℕ) : ℤ))
        rw [hstep, Function.iterate_succ_apply', tableRule_apply]
        congr 2 <;> push_cast [hjge] <;> ring
    · simp only [movingLawOf]
      change ((wseq (t + (k - 1))).2 + 1) % q = (u + 1) % q
      rw [hlast]
      exact Nat.mod_add_mod _ _ _
  have hsub : ((Finset.range T).filter fun t =>
        movingLawOf f hk p q La Lb (fun i => wseq (t + (i : ℕ))) ≠ wseq (t + k))
      ⊆ ((Finset.range T).filter fun t =>
            La (fun i => wseq (t + (i : ℕ))) ≠ (wseq (t + k)).1 0) ∪
        ((Finset.range T).filter fun t =>
            Lb (fun i => wseq (t + (i : ℕ))) ≠
              ((wseq (t + k)).1 ⟨m + 1, by omega⟩, (wseq (t + k)).1 (Fin.last (m + 2)))) := by
    intro t ht
    simp only [Finset.mem_filter, Finset.mem_range] at ht
    obtain ⟨htT, htne⟩ := ht
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_range]
    by_contra hc
    push Not at hc
    exact htne (hmiss t (Finset.mem_range.mpr htT) (hc.1 htT) (hc.2 htT))
  have hLa' : readingMisses k (fun w : (Fin (m + 3) → ZMod 2) × ℕ => w.1 0) La wseq T =
      readingCount k (fun w : (Fin (m + 3) → ZMod 2) × ℕ => w.1 0) wseq T := hLa
  have hLb' : readingMisses k
      (fun w : (Fin (m + 3) → ZMod 2) × ℕ => (w.1 ⟨m + 1, by omega⟩, w.1 (Fin.last (m + 2))))
      Lb wseq T =
      readingCount k
        (fun w : (Fin (m + 3) → ZMod 2) × ℕ => (w.1 ⟨m + 1, by omega⟩, w.1 (Fin.last (m + 2))))
        wseq T := hLb
  calc hindsightCount k wseq T
      ≤ lawMisses k (movingLawOf f hk p q La Lb) wseq T :=
        ciInf_le' _ (movingLawOf f hk p q La Lb)
    _ ≤ readingMisses k (fun w : (Fin (m + 3) → ZMod 2) × ℕ => w.1 0) La wseq T +
        readingMisses k
          (fun w : (Fin (m + 3) → ZMod 2) × ℕ => (w.1 ⟨m + 1, by omega⟩, w.1 (Fin.last (m + 2))))
          Lb wseq T := by
        calc lawMisses k (movingLawOf f hk p q La Lb) wseq T
            ≤ (((Finset.range T).filter fun t =>
                  La (fun i => wseq (t + (i : ℕ))) ≠ (wseq (t + k)).1 0) ∪
                ((Finset.range T).filter fun t =>
                  Lb (fun i => wseq (t + (i : ℕ))) ≠
                    ((wseq (t + k)).1 ⟨m + 1, by omega⟩,
                      (wseq (t + k)).1 (Fin.last (m + 2))))).card :=
              Finset.card_le_card hsub
          _ ≤ _ + _ := Finset.card_union_le _ _
    _ = _ := by rw [hLa', hLb']

/-- **Both hypotheses of the translating window's bound are met at once, and the bound holds
there**: table `90`, the single seed, start `0`, speed `1/2`, width `3`, memory `1` and horizon
`4` ([Guests] §7 Proposition 7.27, row GV-39, at a window whose ends move). -/
theorem hindsightCount_movingWindow_le_add_readingCount_nonvacuous :
    f90 0 0 0 = 0 ∧ 0 < 2 ∧ 1 ≤ 2 ∧ 0 < 1 ∧
      hindsightCount 1 (movingWindow (tableRule f90 hq90) (Finsupp.single 0 1) 0 1 2 3) 4 ≤
        readingCount 1 (fun w : (Fin 3 → ZMod 2) × ℕ => w.1 0)
            (movingWindow (tableRule f90 hq90) (Finsupp.single 0 1) 0 1 2 3) 4 +
        readingCount 1 (fun w : (Fin 3 → ZMod 2) × ℕ => (w.1 1, w.1 2))
            (movingWindow (tableRule f90 hq90) (Finsupp.single 0 1) 0 1 2 3) 4 :=
  ⟨hq90, by norm_num, by norm_num, by norm_num,
    hindsightCount_movingWindow_le_add_readingCount f90 hq90 (Finsupp.single 0 1) 0
      (by norm_num) (by norm_num) 0 (by norm_num) 4⟩

/-! ## Piece 3: the guard pair -/

/-- **A repeated context with two different targets forces at least one miss.** -/
private theorem one_le_hindsightCount_of_context_ne {α : Type*} [DecidableEq α]
    (k : ℕ) (x : ℕ → α) (T : ℕ) {t₁ t₂ : ℕ} (ht₁ : t₁ < T) (ht₂ : t₂ < T)
    (hctx : (fun i : Fin k => x (t₁ + (i : ℕ))) = (fun i : Fin k => x (t₂ + (i : ℕ))))
    (hne : x (t₁ + k) ≠ x (t₂ + k)) :
    1 ≤ hindsightCount k x T := by
  have hαne : Nonempty α := ⟨x 0⟩
  by_contra hc
  push Not at hc
  have h0 : hindsightCount k x T = 0 := by omega
  obtain ⟨L, hL0⟩ := ciInf_mem (fun L : (Fin k → α) → α => lawMisses k L x T)
  have hL : lawMisses k L x T = hindsightCount k x T := hL0
  rw [h0] at hL
  unfold lawMisses at hL
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff] at hL
  have hm1 : L (fun i : Fin k => x (t₁ + (i : ℕ))) = x (t₁ + k) :=
    not_not.mp (hL (Finset.mem_range.mpr ht₁))
  have hm2 : L (fun i : Fin k => x (t₂ + (i : ℕ))) = x (t₂ + k) :=
    not_not.mp (hL (Finset.mem_range.mpr ht₂))
  rw [hctx] at hm1
  exact hne (hm1.symm.trans hm2)

/-- **Guard: the positive-memory hypothesis is load-bearing.** At the table sending everything to
zero, from the single seed, the window of cells `-1, 0, 1` holds two different contents at steps
`0` and `1`, so a memory-`0` law that reads nothing misses one of them, while both end columns are
zero throughout. -/
theorem hindsightCount_observedWindow_zero_memory_guard :
    ¬ (hindsightCount 0
          (observedWindow (tableRule (fun _ _ _ => (0 : ZMod 2)) rfl)
            (Finsupp.single (0 : ℤ) (1 : ZMod 2)) (-1) 3) 2 ≤
        hindsightCount 0
          (observedColumn (tableRule (fun _ _ _ => (0 : ZMod 2)) rfl)
            (Finsupp.single (0 : ℤ) (1 : ZMod 2)) (-1)) 2 +
        hindsightCount 0
          (observedColumn (tableRule (fun _ _ _ => (0 : ZMod 2)) rfl)
            (Finsupp.single (0 : ℤ) (1 : ZMod 2)) 1) 2) := by
  classical
  set f₀ : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2 := fun _ _ _ => 0 with hf₀_def
  have hq₀ : f₀ 0 0 0 = 0 := rfl
  set s₀ : ℤ →₀ ZMod 2 := Finsupp.single (0 : ℤ) (1 : ZMod 2) with hs₀_def
  set window : ℕ → (Fin 3 → ZMod 2) := observedWindow (tableRule f₀ hq₀) s₀ (-1) 3 with hwin_def
  set colA : ℕ → ZMod 2 := observedColumn (tableRule f₀ hq₀) s₀ (-1) with hcolA_def
  set colB : ℕ → ZMod 2 := observedColumn (tableRule f₀ hq₀) s₀ 1 with hcolB_def
  have hUzero : ∀ (s : ℤ →₀ ZMod 2) (i : ℤ), tableRule f₀ hq₀ s i = 0 := by
    intro s i; rw [tableRule_apply]
  have hcolAzero : ∀ t, colA t = 0 := by
    intro t
    rw [hcolA_def]
    change ((tableRule f₀ hq₀)^[t] s₀) (-1) = 0
    cases t with
    | zero => change s₀ (-1) = 0; exact Finsupp.single_eq_of_ne (by norm_num)
    | succ n => rw [Function.iterate_succ_apply']; exact hUzero _ _
  have hcolBzero : ∀ t, colB t = 0 := by
    intro t
    rw [hcolB_def]
    change ((tableRule f₀ hq₀)^[t] s₀) 1 = 0
    cases t with
    | zero => change s₀ 1 = 0; exact Finsupp.single_eq_of_ne (by norm_num)
    | succ n => rw [Function.iterate_succ_apply']; exact hUzero _ _
  have hcolA0 : hindsightCount 0 colA 2 = 0 := by
    apply le_antisymm _ (Nat.zero_le _)
    calc hindsightCount 0 colA 2 ≤ lawMisses 0 (fun _ => 0) colA 2 := ciInf_le' _ (fun _ => 0)
      _ = 0 := by
        unfold lawMisses
        rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro t _
        simp [hcolAzero]
  have hcolB0 : hindsightCount 0 colB 2 = 0 := by
    apply le_antisymm _ (Nat.zero_le _)
    calc hindsightCount 0 colB 2 ≤ lawMisses 0 (fun _ => 0) colB 2 := ciInf_le' _ (fun _ => 0)
      _ = 0 := by
        unfold lawMisses
        rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro t _
        simp [hcolBzero]
  have hw0 : window 0 = ![0, 1, 0] := by
    funext j
    change s₀ (-1 + ((j : ℕ) : ℤ)) = ![(0 : ZMod 2), 1, 0] j
    fin_cases j <;> norm_num [hs₀_def, Finsupp.single_apply]
  have hw1 : window 1 = ![0, 0, 0] := by
    funext j
    change ((tableRule f₀ hq₀) s₀) (-1 + ((j : ℕ) : ℤ)) = ![(0 : ZMod 2), 0, 0] j
    rw [hUzero]
    fin_cases j <;> norm_num
  have hne : window 0 ≠ window 1 := by rw [hw0, hw1]; decide
  have h1 := one_le_hindsightCount_of_context_ne 0 window 2
    (show (0 : ℕ) < 2 by norm_num) (show (1 : ℕ) < 2 by norm_num)
    (funext (fun i => i.elim0)) hne
  rw [hcolA0, hcolB0]
  omega

/-- **Guard: the two end columns give the window's hindsight count no lower bound.** At the shift
from the state with cell `1` set, the window of cells `0` and `1` holds three different contents at
steps `0`, `1`, `2`, so a law at memory one never misses in three steps, while the column at cell
`0` reads `0, 1, 0, 0` and has met `0` followed by `1` and by `0`. -/
theorem hindsightCount_observedWindow_lt_column_f170 :
    hindsightCount 1
        (observedWindow (tableRule f170 hq170)
          (Finsupp.single (1 : ℤ) (1 : ZMod 2)) 0 2) 3 = 0 ∧
      0 < hindsightCount 1
        (observedColumn (tableRule f170 hq170)
          (Finsupp.single (1 : ℤ) (1 : ZMod 2)) 0) 3 := by
  classical
  set s₀ : ℤ →₀ ZMod 2 := Finsupp.single (1 : ℤ) (1 : ZMod 2) with hs₀_def
  set window : ℕ → (Fin 2 → ZMod 2) := observedWindow (tableRule f170 hq170) s₀ 0 2 with hwin_def
  set col0 : ℕ → ZMod 2 := observedColumn (tableRule f170 hq170) s₀ 0 with hcol0_def
  have hiter : ∀ (t : ℕ) (s : ℤ →₀ ZMod 2) (j : ℤ),
      ((tableRule f170 hq170)^[t] s) j = s (j + t) := by
    intro t
    induction t with
    | zero => intro s j; simp
    | succ t ih =>
      intro s j
      rw [Function.iterate_succ_apply, ih, tableRule_apply]
      change s (j + (t : ℤ) + 1) = s (j + ((t + 1 : ℕ) : ℤ))
      rw [Nat.cast_succ, add_assoc]
  have hwinval : ∀ (t : ℕ) (j : Fin 2), window t j = s₀ (((j : ℕ) : ℤ) + (t : ℤ)) := by
    intro t j
    rw [hwin_def]
    change ((tableRule f170 hq170)^[t] s₀) (0 + ((j : ℕ) : ℤ)) = s₀ (((j : ℕ) : ℤ) + (t : ℤ))
    rw [zero_add, hiter]
  have hcolval : ∀ t : ℕ, col0 t = s₀ ((t : ℤ)) := by
    intro t
    rw [hcol0_def]
    change ((tableRule f170 hq170)^[t] s₀) 0 = s₀ (t : ℤ)
    rw [hiter, zero_add]
  have hs00 : s₀ 0 = 0 := Finsupp.single_eq_of_ne (by norm_num)
  have hs01 : s₀ 1 = 1 := Finsupp.single_eq_same
  have hs02 : s₀ 2 = 0 := Finsupp.single_eq_of_ne (by norm_num)
  have hs03 : s₀ 3 = 0 := Finsupp.single_eq_of_ne (by norm_num)
  have hs04 : s₀ 4 = 0 := Finsupp.single_eq_of_ne (by norm_num)
  have hw0 : window 0 = ![0, 1] := by
    funext j
    rw [hwinval]
    fin_cases j <;> norm_num [hs00, hs01]
  have hw1 : window 1 = ![1, 0] := by
    funext j
    rw [hwinval]
    fin_cases j <;> norm_num [hs01, hs02]
  have hw2 : window 2 = ![0, 0] := by
    funext j
    rw [hwinval]
    fin_cases j <;> norm_num [hs02, hs03]
  have hw3 : window 3 = ![0, 0] := by
    funext j
    rw [hwinval]
    fin_cases j <;> norm_num [hs03, hs04]
  have hc0 : col0 0 = 0 := by rw [hcolval]; exact hs00
  have hc1 : col0 1 = 1 := by rw [hcolval]; exact hs01
  have hc2 : col0 2 = 0 := by rw [hcolval]; exact hs02
  have hc3 : col0 3 = 0 := by rw [hcolval]; exact hs03
  refine ⟨?_, ?_⟩
  · apply le_antisymm _ (Nat.zero_le _)
    set Lgood : (Fin 1 → (Fin 2 → ZMod 2)) → (Fin 2 → ZMod 2) := fun hist =>
      if hist 0 = (![0, 1] : Fin 2 → ZMod 2) then (![1, 0] : Fin 2 → ZMod 2)
      else if hist 0 = (![1, 0] : Fin 2 → ZMod 2) then (![0, 0] : Fin 2 → ZMod 2)
      else (![0, 0] : Fin 2 → ZMod 2)
      with hLgood_def
    calc hindsightCount 1 window 3 ≤ lawMisses 1 Lgood window 3 := ciInf_le' _ Lgood
      _ = 0 := by
        unfold lawMisses
        rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro t ht
        rw [Finset.mem_range] at ht
        simp only [not_not]
        interval_cases t
        · have hc : (fun i : Fin 1 => window (0 + (i : ℕ))) = fun _ => window 0 := by
            funext i; norm_num
          change Lgood (fun i => window (0 + (i : ℕ))) = window 1
          rw [hc, hw0, hw1]
          decide
        · have hc : (fun i : Fin 1 => window (1 + (i : ℕ))) = fun _ => window 1 := by
            funext i; norm_num
          change Lgood (fun i => window (1 + (i : ℕ))) = window 2
          rw [hc, hw1, hw2]
          decide
        · have hc : (fun i : Fin 1 => window (2 + (i : ℕ))) = fun _ => window 2 := by
            funext i; norm_num
          change Lgood (fun i => window (2 + (i : ℕ))) = window 3
          rw [hc, hw2, hw3]
          decide
  · have hctx : (fun i : Fin 1 => col0 (0 + (i : ℕ))) = (fun i : Fin 1 => col0 (2 + (i : ℕ))) := by
      funext i
      fin_cases i
      change col0 0 = col0 2
      rw [hc0, hc2]
    have hne : col0 (0 + 1) ≠ col0 (2 + 1) := by
      change col0 1 ≠ col0 3
      rw [hc1, hc3]
      decide
    have h1 := one_le_hindsightCount_of_context_ne 1 col0 3
      (show (0 : ℕ) < 3 by norm_num) (show (2 : ℕ) < 3 by norm_num) hctx hne
    omega

/-- **Guard: the positive-memory hypothesis of the translating window's bound is load-bearing.**
At the table sending everything to zero, from the single seed, the window of three cells from `5`
lies in the quiescent region and its content never changes, but its phase does: at speed `1/2` the
states at steps `0` and `1` differ in the phase alone, so a memory-`0` law that reads nothing
misses one of them, while both end readings are zero throughout. -/
theorem hindsightCount_movingWindow_zero_memory_guard :
    ¬ (hindsightCount 0
          (movingWindow (tableRule (fun _ _ _ => (0 : ZMod 2)) rfl)
            (Finsupp.single (0 : ℤ) 1) 5 1 2 3) 2 ≤
        readingCount 0 (fun w : (Fin 3 → ZMod 2) × ℕ => w.1 0)
            (movingWindow (tableRule (fun _ _ _ => (0 : ZMod 2)) rfl)
              (Finsupp.single (0 : ℤ) 1) 5 1 2 3) 2 +
        readingCount 0 (fun w : (Fin 3 → ZMod 2) × ℕ => (w.1 1, w.1 2))
            (movingWindow (tableRule (fun _ _ _ => (0 : ZMod 2)) rfl)
              (Finsupp.single (0 : ℤ) 1) 5 1 2 3) 2) := by
  classical
  set f₀ : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2 := fun _ _ _ => 0 with hf₀_def
  have hq₀ : f₀ 0 0 0 = 0 := rfl
  set s₀ : ℤ →₀ ZMod 2 := Finsupp.single (0 : ℤ) (1 : ZMod 2) with hs₀_def
  set window : ℕ → (Fin 3 → ZMod 2) × ℕ := movingWindow (tableRule f₀ hq₀) s₀ 5 1 2 3
    with hwin_def
  have hUzero : ∀ (s : ℤ →₀ ZMod 2) (i : ℤ), tableRule f₀ hq₀ s i = 0 := by
    intro s i; rw [tableRule_apply]
  have hcontent : ∀ (t : ℕ) (j : Fin 3), (window t).1 j = 0 := by
    intro t j
    change ((tableRule f₀ hq₀)^[t] s₀) (5 + ((1 * t / 2 : ℕ) : ℤ) + ((j : ℕ) : ℤ)) = 0
    cases t with
    | zero =>
      change s₀ (5 + ((1 * 0 / 2 : ℕ) : ℤ) + ((j : ℕ) : ℤ)) = 0
      exact Finsupp.single_eq_of_ne (by have := j.isLt; omega)
    | succ n => rw [Function.iterate_succ_apply']; exact hUzero _ _
  have hA0 : readingCount 0 (fun w : (Fin 3 → ZMod 2) × ℕ => w.1 0) window 2 = 0 := by
    apply le_antisymm _ (Nat.zero_le _)
    calc readingCount 0 (fun w : (Fin 3 → ZMod 2) × ℕ => w.1 0) window 2
        ≤ readingMisses 0 (fun w : (Fin 3 → ZMod 2) × ℕ => w.1 0) (fun _ => 0) window 2 :=
          ciInf_le' _ (fun _ => 0)
      _ = 0 := by
        unfold readingMisses
        rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro t _
        simp [hcontent]
  have hB0 : readingCount 0 (fun w : (Fin 3 → ZMod 2) × ℕ => (w.1 1, w.1 2)) window 2 = 0 := by
    apply le_antisymm _ (Nat.zero_le _)
    calc readingCount 0 (fun w : (Fin 3 → ZMod 2) × ℕ => (w.1 1, w.1 2)) window 2
        ≤ readingMisses 0 (fun w : (Fin 3 → ZMod 2) × ℕ => (w.1 1, w.1 2)) (fun _ => (0, 0))
            window 2 :=
          ciInf_le' _ (fun _ => (0, 0))
      _ = 0 := by
        unfold readingMisses
        rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro t _
        simp [hcontent]
  have hne : window 0 ≠ window 1 := by
    intro h
    have h2 := congrArg Prod.snd h
    change (0 : ℕ) % 2 = 1 % 2 at h2
    omega
  have h1 := one_le_hindsightCount_of_context_ne 0 window 2
    (show (0 : ℕ) < 2 by norm_num) (show (1 : ℕ) < 2 by norm_num)
    (funext (fun i => i.elim0)) hne
  rw [hA0, hB0]
  omega

end WindowCount

/-! ## Axiom audit

Every public theorem above is `#print axioms`-clean on the standard triple, and the guards below
make that build-enforced. -/

set_option linter.style.longLine false

/-- info: 'WindowCount.readingCount_id' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms WindowCount.readingCount_id

/-- info: 'WindowCount.readingCount_le_hindsightCount' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms WindowCount.readingCount_le_hindsightCount

/-- info: 'WindowCount.readingCount_le_hindsightCount_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms WindowCount.readingCount_le_hindsightCount_comp

/-- info: 'WindowCount.hindsightCount_observedWindow_le_add_readingCount' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms WindowCount.hindsightCount_observedWindow_le_add_readingCount

/-- info: 'WindowCount.hindsightCount_observedWindow_le_add_columns' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms WindowCount.hindsightCount_observedWindow_le_add_columns

/-- info: 'WindowCount.hindsightCount_observedWindow_zero_memory_guard' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms WindowCount.hindsightCount_observedWindow_zero_memory_guard

/-- info: 'WindowCount.hindsightCount_observedWindow_lt_column_f170' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms WindowCount.hindsightCount_observedWindow_lt_column_f170

/-- info: 'WindowCount.hindsightCount_movingWindow_le_add_readingCount' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms WindowCount.hindsightCount_movingWindow_le_add_readingCount

/-- info: 'WindowCount.hindsightCount_movingWindow_le_add_readingCount_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms WindowCount.hindsightCount_movingWindow_le_add_readingCount_nonvacuous

/-- info: 'WindowCount.hindsightCount_movingWindow_zero_memory_guard' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms WindowCount.hindsightCount_movingWindow_zero_memory_guard
