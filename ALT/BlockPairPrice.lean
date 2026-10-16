module

public import ALT.BlockPairOverlap


/-!
# The block-pair host's rule as an exhibited program

`BlockPairOverlap.lean` prices the packed host's guest parametrically:
`BlockPairHost.card_orbit_le_cbHue` takes codes `cU`, `cθ` for the host's own table and the frame's
own table as hypotheses, and owns the guest at `elen cU + elen cθ + O(1)` — a design count, not a
machine-priced program, until this module ([Inevitability] §5 Theorem 5.8's boundary, closed there
by citing it). This module closes that gap: it exhibits `cU`, `cθ` as fixed, machine-checked
programs — `hostBuilder`/`frameBuilder`, each taking only `M` and
`Nat.size Π` (`frameBuilder` also `BlockPairHost.frameBits M`) as `bconst`-loaded numerals, no
macro-law code imported — and prices them in the corpus's own `KE` currency, the `KE_flatWorld_le`
pattern of `PersistenceCapacity.lean` instanced at this host.

The step is packed on numerals through the same route `KE_flatWorld_le` uses: `hostStepNum`/
`frameStepNum` are pure `/`, `%`, `*`, `+`, `if`-arithmetic on the packed state (no `ALT.Mem`, no
`Fin`), proved primitive recursive by direct composition, tabulated over every state
(`hostTableFn`/`frameTableFn`), and identified with `BlockPairHost.packed`/`BlockPairHost.frame`'s
own tables (`hostTableFn_eq`/`frameTableFn_eq`) through
`hostStepNum_stateEquiv`/`frameStepNum_stateEquiv` — the bridge theorems that carry the real
content, proved digit-by-digit against `BlockPairHost.subUpdate`'s own case split via
`BlockPairHost.stateEquiv_digit`.

## Main results

* `hostStepNum`, `frameStepNum`, `hostStepNum_stateEquiv`, `frameStepNum_stateEquiv` — the packed
  step and read, and their correctness against `BlockPairHost.packed`/`BlockPairHost.frame`.
* `hostBuilder`, `frameBuilder`, `eval_hostBuilder`, `eval_frameBuilder` — the fixed programs,
  extracted from universality over the primitive-recursive tables.
* `KE_hostPacked_le`, `KE_hostFrame_le` — the host's table and the frame's table are each owned
  within `elen <builder> + O(size M + size (size Π))` bits (`KE_hostFrame_le` additionally pays
  `O(size (BlockPairHost.frameBits M))`) — nothing that scales with the state count
  `2 ^ (16 + size Π)`.
* `BlockPairHost.card_orbit_le_cbHue_cheap` — **the payoff**: `BlockPairHost.card_orbit_le_cbHue` at
  the exhibited codes, so the guest's carried entropy is bounded by `CbHue` at a budget that is an
  absolute constant plus `O(log Π)`, with no imported code parameter at all.

## Scope

`BlockPairHost.GrowsLawfulGuest`, `BlockPairHost.card_orbit_le_cbHue` and
`BlockPairHost.witness_overlap` in `BlockPairOverlap.lean` are untouched;
`BlockPairHost.card_orbit_le_cbHue_cheap` is a corollary beside them, not a restatement. This module
does not revisit survival, the crossing clause, or the `𝒮_L`/`𝒮_E` membership statements — only the
growth clause's own affordability, sharpened from a design count to a machine-checked program.

Anchors: [Inevitability] §5 Theorem 5.8, [Guests] §6 Theorem 6.1, rows IN-38, GV-5.
-/


@[expose] public section

namespace ALT

open AdditiveComplexity KolmogorovComplexity CodeEvalLaws
open Equiv MulAction

attribute [local instance] arrowAction

/-! ## The sign and word supply, as numeral arithmetic -/

/-- The Thue–Morse popcount, as a bounded bit-sum: `tmSign i = (-1) ^ tmBit i`
(`tmSign_eq_tmBit`). List-shaped for `Primrec`. -/
def tmBit (i : ℕ) : ℕ := ((List.range (i + 1)).map (fun j => i / 2 ^ j % 2)).sum

private theorem tmBit_eq_sum (i : ℕ) :
    tmBit i = ∑ j ∈ Finset.range (i + 1), i / 2 ^ j % 2 := by
  rw [tmBit]; simp [Finset.sum, Multiset.range]

theorem tmSign_eq_tmBit (i : ℕ) : tmSign i = (-1 : ℤ) ^ tmBit i := by
  rw [tmBit_eq_sum]; exact tmSign_eq_bitsum i

/-- `tmPrefix`'s own "is `-1`" exponent, closed form on `n` directly: at an even `n = 2t` it is
`t`; at an odd `n = 2t + 1` it is `t + tmBit t`. Matches `tmPrefix_two_mul`/
`tmPrefix_two_mul_add_one` through `tmSign_eq_tmBit`. -/
def tmPrefixBit (n : ℕ) : ℕ := n / 2 + (if n % 2 = 1 then tmBit (n / 2) else 0)

theorem tmPrefix_eq_tmPrefixBit (n : ℕ) : tmPrefix n = (-1 : ℤ) ^ tmPrefixBit n := by
  rcases Nat.even_or_odd n with ⟨t, ht⟩ | ⟨t, ht⟩
  · have hn2 : n = 2 * t := by omega
    have hmod : n % 2 = 0 := by omega
    have hdiv : n / 2 = t := by omega
    rw [tmPrefixBit, hmod, hdiv, ite_eq_right (by norm_num), Nat.add_zero, hn2, tmPrefix_two_mul]
  · have hmod : n % 2 = 1 := by omega
    have hdiv : n / 2 = t := by omega
    rw [tmPrefixBit, hmod, hdiv, ite_eq_left rfl, ht, tmPrefix_two_mul_add_one, tmSign_eq_tmBit,
      pow_add]

/-- `blockSign`'s own exponent, straddling `j` per `blockSign_eq_tmPrefix`. -/
def blockSignBit (j : ℕ) : ℕ := tmPrefixBit ((j + 1) / 2) + tmPrefixBit (j / 2)

theorem blockSign_eq_blockSignBit (m : ℕ) (j : Fin m) :
    blockSign m j = (-1 : ℤ) ^ blockSignBit (j : ℕ) := by
  rw [blockSign_eq_tmPrefix, tmPrefix_eq_tmPrefixBit, tmPrefix_eq_tmPrefixBit, blockSignBit,
    pow_add]

/-- `wordU`'s value at `p < 24`, as a `1`-for-`-1` bit; `0` outside range. -/
def wordUBit (p : ℕ) : ℕ :=
  [1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1, 1, 1, 1, 0, 1, 1, 0, 0, 0].getD p 0

/-- `wordV`'s value at `p < 24`, as a `1`-for-`-1` bit; `0` outside range. -/
def wordVBit (p : ℕ) : ℕ :=
  [0, 0, 1, 0, 1, 0, 0, 0, 1, 1, 0, 1, 0, 1, 1, 1, 0, 0, 1, 0, 1, 0, 0, 0].getD p 0

theorem wordU_eq_wordUBit (p : Fin 24) : wordU p = (-1 : ℤ) ^ wordUBit (p : ℕ) := by
  fin_cases p <;> decide

theorem wordV_eq_wordVBit (p : Fin 24) : wordV p = (-1 : ℤ) ^ wordVBit (p : ℕ) := by
  fin_cases p <;> decide

/-- The word supply's own exponent at block index `j`, position `p`: `wordU` on an even block,
`wordV` on an odd one. -/
def blockWordBit (j p : ℕ) : ℕ := if j % 2 = 0 then wordUBit p else wordVBit p

/-- **The design's own value, as a bounded exponent.** `BlockPairHost.designObs` reads `-1` exactly
when the sign supply and the word supply disagree in parity: `blockSignBit (u/24)` from `blockSign`,
and
`blockWordBit (u/24) (u%24)` from the word at the block's own offset. -/
def designExp (u : ℕ) : ℕ := blockSignBit (u / 24) + blockWordBit (u / 24) (u % 24)

theorem BlockPairHost.designObs_eq (M : ℕ) [NeZero (2 * (2 * M))] (u : ℕ)
    (hu : u < 2 * (2 * M) * 24) :
    BlockPairHost.designObs M (u : ZMod (2 * (2 * M) * 24)) = decide (Odd (designExp u)) := by
  have hval : (u : ZMod (2 * (2 * M) * 24)).val = u := by
    rw [ZMod.val_natCast]; exact Nat.mod_eq_of_lt hu
  have hkey : blockSeq wordU wordV (blockSign (2 * (2 * M))) (u : ZMod (2 * (2 * M) * 24))
      = (-1 : ℤ) ^ designExp u := by
    simp only [blockSeq_val, hval, designExp, blockWordBit]
    by_cases h : Even (u / 24)
    · have hmod : u / 24 % 2 = 0 := by rw [Nat.even_iff] at h; exact h
      rw [ite_eq_left h, ite_eq_left hmod, blockSign_eq_blockSignBit, wordU_eq_wordUBit, pow_add]
    · have hmod : ¬ u / 24 % 2 = 0 := by rw [Nat.even_iff] at h; exact h
      rw [ite_eq_right h, ite_eq_right hmod, blockSign_eq_blockSignBit, wordV_eq_wordVBit, pow_add]
  unfold BlockPairHost.designObs
  rw [hkey]
  by_cases hodd : Odd (designExp u)
  · rw [Odd.neg_one_pow hodd]; simp [hodd]
  · rw [Nat.not_odd_iff_even] at hodd
    rw [Even.neg_one_pow hodd]
    have hno : ¬ Odd (designExp u) := by rw [Nat.not_odd_iff_even]; exact hodd
    simp [hno]

private theorem eight_le_period (M : ℕ) [NeZero (2 * (2 * M))] : 8 ≤ 2 * (2 * M) * 24 := by
  have := Nat.pos_of_ne_zero (NeZero.ne (2 * (2 * M))); omega

private theorem zmod_sub8_eq (M : ℕ) [NeZero (2 * (2 * M))] (u : ℕ) :
    (u : ZMod (2 * (2 * M) * 24)) - 8
      = (((u + 2 * (2 * M) * 24 - 8) % (2 * (2 * M) * 24) : ℕ) : ZMod (2 * (2 * M) * 24)) := by
  have hle : 8 ≤ u + 2 * (2 * M) * 24 := by have := eight_le_period M; omega
  rw [ZMod.natCast_mod, Nat.cast_sub hle, Nat.cast_add, ZMod.natCast_self]
  ring

/-- **The tape's own value, as a bit.** `BlockPairHost.tape` compares the design's value at `u`
against its
value `8` steps back; the comparison is `1` exactly when the two `designExp` values share parity. -/
def hostTapeBit (N u : ℕ) : ℕ := (designExp u + designExp ((u + N - 8) % N) + 1) % 2

/-- **Boolean agreement is a parity fact**: `decide (Odd a) == decide (Odd b)` — the Bool
`decide (Odd ·) == decide (Odd ·)` reads `BlockPairHost.tape`'s `==` verbatim — holds exactly when
`a + b + 1` is even. -/
private theorem decide_odd_beq (a b : ℕ) :
    (decide (Odd a) == decide (Odd b)) = decide ((a + b + 1) % 2 = 1) := by
  by_cases h1 : Odd a <;> by_cases h2 : Odd b
  · rw [decide_eq_true_iff.mpr h1, decide_eq_true_iff.mpr h2]
    rw [Nat.odd_iff] at h1 h2
    rw [decide_eq_true_iff.mpr (show (a + b + 1) % 2 = 1 by omega)]; rfl
  · rw [decide_eq_true_iff.mpr h1, decide_eq_false_iff_not.mpr h2]
    rw [Nat.odd_iff] at h1
    rw [Nat.not_odd_iff_even, Nat.even_iff] at h2
    rw [decide_eq_false_iff_not.mpr (show ¬ (a + b + 1) % 2 = 1 by omega)]; rfl
  · rw [decide_eq_false_iff_not.mpr h1, decide_eq_true_iff.mpr h2]
    rw [Nat.not_odd_iff_even, Nat.even_iff] at h1
    rw [Nat.odd_iff] at h2
    rw [decide_eq_false_iff_not.mpr (show ¬ (a + b + 1) % 2 = 1 by omega)]; rfl
  · rw [decide_eq_false_iff_not.mpr h1, decide_eq_false_iff_not.mpr h2]
    rw [Nat.not_odd_iff_even, Nat.even_iff] at h1 h2
    rw [decide_eq_true_iff.mpr (show (a + b + 1) % 2 = 1 by omega)]; rfl

theorem BlockPairHost.tape_eq_decide_hostTapeBit (M : ℕ) [NeZero (2 * (2 * M))] (u : ℕ)
    (hu : u < 2 * (2 * M) * 24) :
    BlockPairHost.tape M (u : ZMod (2 * (2 * M) * 24))
      = decide (hostTapeBit (2 * (2 * M) * 24) u = 1) := by
  have hP8 : 8 ≤ 2 * (2 * M) * 24 := eight_le_period M
  have hu' : (u + 2 * (2 * M) * 24 - 8) % (2 * (2 * M) * 24) < 2 * (2 * M) * 24 :=
    Nat.mod_lt _ (by omega)
  unfold BlockPairHost.tape
  rw [zmod_sub8_eq, BlockPairHost.designObs_eq M u hu, BlockPairHost.designObs_eq M _ hu']
  rw [hostTapeBit, decide_odd_beq]

/-! ## The packed host's cell positions, and the digit bridge -/

private theorem BlockPairHost.idxEquiv_inl (M : ℕ) [NeZero (2 * (2 * M))] (i : Fin 8) :
    (BlockPairHost.idxEquiv M (Sum.inl i) : ℕ) = i := by
  rw [BlockPairHost.idxEquiv]
  simp

private theorem BlockPairHost.idxEquiv_inr_inl (M : ℕ) [NeZero (2 * (2 * M))] (i : Fin 8) :
    (BlockPairHost.idxEquiv M (Sum.inr (Sum.inl i)) : ℕ) = 8 + (i : ℕ) := by
  rw [BlockPairHost.idxEquiv]
  simp

private theorem BlockPairHost.idxEquiv_inr_inr (M : ℕ) [NeZero (2 * (2 * M))]
    (j : Fin (Nat.size (2 * (2 * M) * 24))) :
    (BlockPairHost.idxEquiv M (Sum.inr (Sum.inr j)) : ℕ) = 16 + (j : ℕ) := by
  rw [BlockPairHost.idxEquiv]
  simp; omega

/-- **The digit bridge**: a packed host state's bit at `BlockPairHost.idxEquiv M i`'s own position
is
exactly cell `i`'s Boolean value — `ALT.stateEquiv_digit`, transported along
`BlockPairHost.idxEquiv`. -/
theorem BlockPairHost.stateEquiv_digit (M : ℕ) [NeZero (2 * (2 * M))] (x : BlockPairHost.Mem M)
    (i : BlockPairHost.Idx M) :
    numBitN ((BlockPairHost.stateEquiv M x : Fin _) : ℕ) (BlockPairHost.idxEquiv M i : ℕ) = if x i
      then 1 else 0 := by
  have heq : BlockPairHost.stateEquiv M x
      = ALT.stateEquiv (8 + (8 + Nat.size (2 * (2 * M) * 24)))
          (fun j => x ((BlockPairHost.idxEquiv M).symm j)) := rfl
  rw [numBitN, heq, ALT.stateEquiv_digit, Equiv.symm_apply_apply]

/-! ## The decode search, as numeral arithmetic -/

/-- The search `BlockPairHost.decodeRule` performs, restated on any Boolean predicate `P` on
`Fin 8`: the
least index with `P` true, else `0`. -/
private theorem decNum_spec (P : Fin 8 → Bool) (hex : ∃ i, P i = true) :
    (if P 0 = true then (0 : ℕ) else if P 1 = true then 1 else if P 2 = true then 2
     else if P 3 = true then 3 else if P 4 = true then 4 else if P 5 = true then 5
     else if P 6 = true then 6 else if P 7 = true then 7 else 0)
      = (Fin.find (fun i => P i = true) hex : ℕ) := by
  have key : ∀ i : Fin 8, (∀ j : Fin 8, j < i → ¬ P j = true) → P i = true →
      (Fin.find (fun i => P i = true) hex : ℕ) = (i : ℕ) := by
    intro i hmin hi
    rw [(Fin.find_eq_iff hex).mpr ⟨hi, hmin⟩]
  by_cases h0 : P 0 = true
  · rw [ite_eq_left h0]
    exact (key 0 (fun j hj => absurd hj (by omega)) h0).symm
  · rw [ite_eq_right h0]
    by_cases h1 : P 1 = true
    · rw [ite_eq_left h1]
      refine (key 1 (fun j hj => ?_) h1).symm
      fin_cases j <;> first | (exact absurd hj (by decide)) | assumption
    · rw [ite_eq_right h1]
      by_cases h2 : P 2 = true
      · rw [ite_eq_left h2]
        refine (key 2 (fun j hj => ?_) h2).symm
        fin_cases j <;> first | (exact absurd hj (by decide)) | assumption
      · rw [ite_eq_right h2]
        by_cases h3 : P 3 = true
        · rw [ite_eq_left h3]
          refine (key 3 (fun j hj => ?_) h3).symm
          fin_cases j <;> first | (exact absurd hj (by decide)) | assumption
        · rw [ite_eq_right h3]
          by_cases h4 : P 4 = true
          · rw [ite_eq_left h4]
            refine (key 4 (fun j hj => ?_) h4).symm
            fin_cases j <;> first | (exact absurd hj (by decide)) | assumption
          · rw [ite_eq_right h4]
            by_cases h5 : P 5 = true
            · rw [ite_eq_left h5]
              refine (key 5 (fun j hj => ?_) h5).symm
              fin_cases j <;> first | (exact absurd hj (by decide)) | assumption
            · rw [ite_eq_right h5]
              by_cases h6 : P 6 = true
              · rw [ite_eq_left h6]
                refine (key 6 (fun j hj => ?_) h6).symm
                fin_cases j <;> first | (exact absurd hj (by decide)) | assumption
              · rw [ite_eq_right h6]
                by_cases h7 : P 7 = true
                · rw [ite_eq_left h7]
                  refine (key 7 (fun j hj => ?_) h7).symm
                  fin_cases j <;> first | (exact absurd hj (by decide)) | assumption
                · rw [ite_eq_right h7]
                  obtain ⟨i, hi⟩ := hex
                  fin_cases i <;> exact absurd hi (by assumption)

/-- **The code decode, as numeral arithmetic**: the least code cell set, else `0` — the same
search `BlockPairHost.decodeRule` performs, restated on the packed state's own bits. -/
def decNum (s : ℕ) : ℕ :=
  if numBitN s 0 = 1 then 0 else if numBitN s 1 = 1 then 1 else if numBitN s 2 = 1 then 2
  else if numBitN s 3 = 1 then 3 else if numBitN s 4 = 1 then 4 else if numBitN s 5 = 1 then 5
  else if numBitN s 6 = 1 then 6 else if numBitN s 7 = 1 then 7 else 0

theorem decNum_eq_hostDecodeRule (M : ℕ) [NeZero (2 * (2 * M))] (x : BlockPairHost.Mem M) :
    decNum ((BlockPairHost.stateEquiv M x : Fin _) : ℕ) = (BlockPairHost.decodeRule M x : ℕ) := by
  have hb : ∀ i : Fin 8, numBitN ((BlockPairHost.stateEquiv M x : Fin _) : ℕ) (i : ℕ) = 1
      ↔ x (Sum.inl i) = true := by
    intro i
    have hd := BlockPairHost.stateEquiv_digit M x (Sum.inl i)
    rw [BlockPairHost.idxEquiv_inl] at hd
    rw [hd]; cases x (Sum.inl i) <;> simp
  have hb0 : numBitN ((BlockPairHost.stateEquiv M x : Fin _) : ℕ) 0 = 1 ↔ x (Sum.inl 0) = true := hb
    0
  have hb1 : numBitN ((BlockPairHost.stateEquiv M x : Fin _) : ℕ) 1 = 1 ↔ x (Sum.inl 1) = true := hb
    1
  have hb2 : numBitN ((BlockPairHost.stateEquiv M x : Fin _) : ℕ) 2 = 1 ↔ x (Sum.inl 2) = true := hb
    2
  have hb3 : numBitN ((BlockPairHost.stateEquiv M x : Fin _) : ℕ) 3 = 1 ↔ x (Sum.inl 3) = true := hb
    3
  have hb4 : numBitN ((BlockPairHost.stateEquiv M x : Fin _) : ℕ) 4 = 1 ↔ x (Sum.inl 4) = true := hb
    4
  have hb5 : numBitN ((BlockPairHost.stateEquiv M x : Fin _) : ℕ) 5 = 1 ↔ x (Sum.inl 5) = true := hb
    5
  have hb6 : numBitN ((BlockPairHost.stateEquiv M x : Fin _) : ℕ) 6 = 1 ↔ x (Sum.inl 6) = true := hb
    6
  have hb7 : numBitN ((BlockPairHost.stateEquiv M x : Fin _) : ℕ) 7 = 1 ↔ x (Sum.inl 7) = true := hb
    7
  simp only [decNum, hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7]
  unfold BlockPairHost.decodeRule
  by_cases hex : ∃ i : Fin 8, x (Sum.inl i) = true
  · rw [dite_eq_left hex]
    exact decNum_spec (fun i => x (Sum.inl i)) hex
  · rw [dite_eq_right hex]
    push Not at hex
    simp [hex]

/-! ## The numeral step, and the bridge -/

private theorem mod_pow_eq_sum (m k : ℕ) :
    m % 2 ^ k = ∑ j ∈ Finset.range k, numBitN m j * 2 ^ j := by
  induction k with
  | zero => simp [Nat.mod_one]
  | succ k ih =>
    rw [Finset.sum_range_succ, ← ih, numBitN, show (2:ℕ) ^ (k + 1) = 2 ^ k * 2 from pow_succ 2 k,
      Nat.mod_mul]
    ring

private theorem numBitN_shift (m a j : ℕ) : numBitN m (a + j) = numBitN (m / 2 ^ a) j := by
  rw [numBitN, numBitN, pow_add, Nat.div_div_eq_div_mul]

private theorem shift_mod_pow_eq_sum (m a k : ℕ) :
    (m / 2 ^ a) % 2 ^ k = ∑ j ∈ Finset.range k, numBitN m (a + j) * 2 ^ j := by
  rw [mod_pow_eq_sum (m / 2 ^ a) k]
  exact Finset.sum_congr rfl (fun j _ => by rw [numBitN_shift])

private theorem div_eq_sum_of_lt (m a k : ℕ) (h : m / 2 ^ a < 2 ^ k) :
    m / 2 ^ a = ∑ j ∈ Finset.range k, numBitN m (a + j) * 2 ^ j := by
  rw [← shift_mod_pow_eq_sum, Nat.mod_eq_of_lt h]

private theorem block3_decomp (m : ℕ) :
    m = (m % 2 ^ 8) + 2 ^ 8 * ((m / 2 ^ 8) % 2 ^ 8) + 2 ^ 16 * (m / 2 ^ 16) := by
  have e1 : m = 2 ^ 8 * (m / 2 ^ 8) + m % 2 ^ 8 := (Nat.div_add_mod m (2 ^ 8)).symm
  have e2 : m / 2 ^ 8 = 2 ^ 8 * (m / 2 ^ 8 / 2 ^ 8) + m / 2 ^ 8 % 2 ^ 8 :=
    (Nat.div_add_mod (m / 2 ^ 8) (2 ^ 8)).symm
  have e3 : m / 2 ^ 8 / 2 ^ 8 = m / 2 ^ 16 := by rw [Nat.div_div_eq_div_mul]; norm_num
  omega

private theorem BlockPairHost.stateEquiv_lt (M : ℕ) [NeZero (2 * (2 * M))] (x : BlockPairHost.Mem M)
    :
    ((BlockPairHost.stateEquiv M x : Fin _) : ℕ) < 2 ^ (16 + Nat.size (2 * (2 * M) * 24)) := by
  have h := (BlockPairHost.stateEquiv M x).isLt
  have hp : (2 : ℕ) ^ (8 + (8 + Nat.size (2 * (2 * M) * 24)))
      = 2 ^ (16 + Nat.size (2 * (2 * M) * 24)) := by congr 1; omega
  omega

/-- **`BlockPairHost.readCounter`'s raw value, read off the packed state's own bits.**
`finFunctionFinEquiv`'s own value law (`finFunctionFinEquiv_apply`) is the same little-endian sum
`stateEquiv_val` gives,
so `BlockPairHost.readCounter`'s underlying `ℕ` value is exactly bits `16 .. 16 + B` of the packed
state. -/
private theorem BlockPairHost.readCounter_raw_eq (M : ℕ) [NeZero (2 * (2 * M))]
    (x : BlockPairHost.Mem M) :
    ((finFunctionFinEquiv (fun i : Fin (Nat.size (2 * (2 * M) * 24)) =>
        if x (Sum.inr (Sum.inr i)) then (1 : Fin 2) else 0)).val : ℕ)
      = ((BlockPairHost.stateEquiv M x : Fin _) : ℕ) / 2 ^ 16 := by
  have hlt : ((BlockPairHost.stateEquiv M x : Fin _) : ℕ) / 2 ^ 16 < 2 ^
    (Nat.size (2 * (2 * M) * 24)) := by
    have hpos : (0 : ℕ) < 2 ^ 16 := by positivity
    rw [Nat.div_lt_iff_lt_mul hpos]
    have h := BlockPairHost.stateEquiv_lt M x
    calc ((BlockPairHost.stateEquiv M x : Fin _) : ℕ)
        < 2 ^ (16 + Nat.size (2 * (2 * M) * 24)) := h
      _ = 2 ^ (Nat.size (2 * (2 * M) * 24)) * 2 ^ 16 := by rw [pow_add]; ring
  rw [finFunctionFinEquiv_apply, div_eq_sum_of_lt _ 16 _ hlt, ← Fin.sum_univ_eq_sum_range
    (fun j => numBitN ((BlockPairHost.stateEquiv M x : Fin _) : ℕ) (16 + j) * 2 ^ j)]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  have hd := BlockPairHost.stateEquiv_digit M x (Sum.inr (Sum.inr j))
  rw [BlockPairHost.idxEquiv_inr_inr] at hd
  rw [hd]
  cases x (Sum.inr (Sum.inr j)) <;> rfl

/-- **`BlockPairHost.readCounter`'s value, as a numeral.** The counter register cast to `ZMod Π`
reduces mod
`Π` (`ZMod.val_natCast`), applied to `BlockPairHost.readCounter_raw_eq`'s raw value. -/
private theorem BlockPairHost.readCounter_val_eq (M : ℕ) [NeZero (2 * (2 * M))]
    (x : BlockPairHost.Mem M) :
    (BlockPairHost.readCounter M x).val
      = ((BlockPairHost.stateEquiv M x : Fin _) : ℕ) / 2 ^ 16 % (2 * (2 * M) * 24) := by
  rw [BlockPairHost.readCounter, ZMod.val_natCast, BlockPairHost.readCounter_raw_eq]

/-- **`BlockPairHost.writeCounter`'s round trip, as a numeral.** `BlockPairHost.writeCounter M c`
packs to `c.val` exactly: by proof irrelevance, `BlockPairHost.writeCounter`'s internal bound proof
is interchangeable with any other proof of the same fact, so the round trip is
`Equiv.apply_symm_apply` read through the
`ALT.stateEquiv`/`finFunctionFinEquiv` identification `BlockPairHost.readCounter_raw_eq` already
established. -/
private theorem BlockPairHost.writeCounter_digit (M : ℕ) [NeZero (2 * (2 * M))]
    (c : ZMod (2 * (2 * M) * 24))
    (j : Fin (Nat.size (2 * (2 * M) * 24))) :
    (if BlockPairHost.writeCounter M c j then 1 else 0) = numBitN c.val (j : ℕ) := by
  have hlt : c.val < 2 ^ Nat.size (2 * (2 * M) * 24) :=
    lt_trans (ZMod.val_lt c) (Nat.lt_size_self _)
  set w : Fin (Nat.size (2 * (2 * M) * 24)) → Fin 2 :=
    finFunctionFinEquiv.symm (⟨c.val, hlt⟩ : Fin (2 ^ Nat.size (2 * (2 * M) * 24))) with hw
  have hwc : ∀ i, BlockPairHost.writeCounter M c i = (w i == 1) := fun i => rfl
  have hy : (fun i => if (w i == 1) then (1 : Fin 2) else 0) = w := by
    funext i
    generalize hgen : w i = z
    fin_cases z <;> decide
  have hround : (finFunctionFinEquiv w : Fin (2 ^ Nat.size (2 * (2 * M) * 24)))
      = ⟨c.val, hlt⟩ := by rw [hw, Equiv.apply_symm_apply]
  have hkey : (ALT.stateEquiv (Nat.size (2 * (2 * M) * 24)) (fun i => w i == 1) : ℕ) = c.val := by
    change (finFunctionFinEquiv (fun i => finTwoEquiv.symm (w i == 1)) : ℕ) = c.val
    have hcond : (fun i => finTwoEquiv.symm (w i == 1))
        = fun i => if (w i == 1) then (1 : Fin 2) else 0 := by
      funext i; cases w i == 1 <;> rfl
    rw [hcond, hy, hround]
  have hd := ALT.stateEquiv_digit (N := Nat.size (2 * (2 * M) * 24)) (fun i => w i == 1) j
  rw [hkey] at hd
  rw [hwc j, numBitN, ← hd]

private theorem BlockPairHost.subUpdate_counter (M : ℕ) [NeZero (2 * (2 * M))]
    (x : BlockPairHost.Mem M)
    (j : Fin (Nat.size (2 * (2 * M) * 24))) :
    BlockPairHost.subUpdate M x (Sum.inr (Sum.inr j))
      = BlockPairHost.writeCounter M (BlockPairHost.readCounter M x + 1) j := rfl

private theorem val_add_one (M : ℕ) [NeZero (2 * (2 * M))] (c : ZMod (2 * (2 * M) * 24)) :
    (c + 1).val = (c.val + 1) % (2 * (2 * M) * 24) := by
  have hP8 : 8 ≤ 2 * (2 * M) * 24 := eight_le_period M
  have h1 : (1 : ZMod (2 * (2 * M) * 24)).val = 1 := by
    rw [← Nat.cast_one, ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
  rw [ZMod.val_add, h1]

/-- **The counter block updates correctly.** `target/2^16`'s own bits are exactly
`BlockPairHost.subUpdate`'s counter cells (`BlockPairHost.stateEquiv_digit`), which are
`BlockPairHost.writeCounter M (BlockPairHost.readCounter M x + 1)`
(`BlockPairHost.subUpdate_counter`), which pack back to `(BlockPairHost.readCounter M x + 1).val`
(`BlockPairHost.writeCounter_digit`, `mod_pow_eq_sum`) — `vNext` in
`BlockPairHost.readCounter_val_eq`'s own currency. -/
private theorem hostStepNum_counter (M : ℕ) [NeZero (2 * (2 * M))]
    (x : BlockPairHost.Mem M) :
    ((BlockPairHost.stateEquiv M (BlockPairHost.subUpdate M x) : Fin _) : ℕ) / 2 ^ 16
      = ((((BlockPairHost.stateEquiv M x : Fin _) : ℕ) / 2 ^ 16 % (2 * (2 * M) * 24)) + 1)
          % (2 * (2 * M) * 24) := by
  have hlt : ((BlockPairHost.stateEquiv M (BlockPairHost.subUpdate M x) : Fin _) : ℕ) / 2 ^ 16
      < 2 ^ (Nat.size (2 * (2 * M) * 24)) := by
    have hpos : (0 : ℕ) < 2 ^ 16 := by positivity
    rw [Nat.div_lt_iff_lt_mul hpos]
    have h := BlockPairHost.stateEquiv_lt M (BlockPairHost.subUpdate M x)
    calc ((BlockPairHost.stateEquiv M (BlockPairHost.subUpdate M x) : Fin _) : ℕ)
        < 2 ^ (16 + Nat.size (2 * (2 * M) * 24)) := h
      _ = 2 ^ (Nat.size (2 * (2 * M) * 24)) * 2 ^ 16 := by rw [pow_add]; ring
  rw [div_eq_sum_of_lt _ 16 _ hlt]
  have heach : ∀ j : Fin (Nat.size (2 * (2 * M) * 24)),
      numBitN ((BlockPairHost.stateEquiv M (BlockPairHost.subUpdate M x) : Fin _) : ℕ)
        (16 + (j : ℕ))
        = numBitN (BlockPairHost.readCounter M x + 1).val (j : ℕ) := by
    intro j
    have hd := BlockPairHost.stateEquiv_digit M (BlockPairHost.subUpdate M x) (Sum.inr (Sum.inr j))
    rw [BlockPairHost.idxEquiv_inr_inr] at hd
    rw [hd, BlockPairHost.subUpdate_counter, ← BlockPairHost.writeCounter_digit]
  rw [show (∑ j ∈ Finset.range (Nat.size (2 * (2 * M) * 24)),
        numBitN ((BlockPairHost.stateEquiv M (BlockPairHost.subUpdate M x) : Fin _) : ℕ) (16 + j)
          * 2 ^ j)
      = ∑ j ∈ Finset.range (Nat.size (2 * (2 * M) * 24)),
        numBitN (BlockPairHost.readCounter M x + 1).val j * 2 ^ j from
    Finset.sum_congr rfl (fun j hj => by rw [heach ⟨j, Finset.mem_range.mp hj⟩])]
  rw [← mod_pow_eq_sum]
  have hfit : (BlockPairHost.readCounter M x + 1).val < 2 ^ Nat.size (2 * (2 * M) * 24) :=
    lt_trans (ZMod.val_lt _) (Nat.lt_size_self _)
  rw [Nat.mod_eq_of_lt hfit, val_add_one, BlockPairHost.readCounter_val_eq]

/-- **The code block is unchanged.** `BlockPairHost.subUpdate`'s code case is `s (Sum.inl i)`
verbatim. -/
private theorem hostStepNum_code (M : ℕ) [NeZero (2 * (2 * M))] (x : BlockPairHost.Mem M) :
    ((BlockPairHost.stateEquiv M (BlockPairHost.subUpdate M x) : Fin _) : ℕ) % 2 ^ 8
      = ((BlockPairHost.stateEquiv M x : Fin _) : ℕ) % 2 ^ 8 := by
  rw [mod_pow_eq_sum, mod_pow_eq_sum]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  have hi8 : i < 8 := Finset.mem_range.mp hi
  have hd1 := BlockPairHost.stateEquiv_digit M (BlockPairHost.subUpdate M x)
    (Sum.inl (⟨i, hi8⟩ : Fin 8))
  have hd2 := BlockPairHost.stateEquiv_digit M x (Sum.inl (⟨i, hi8⟩ : Fin 8))
  rw [BlockPairHost.idxEquiv_inl] at hd1 hd2
  rw [hd1, hd2]
  rfl

private theorem BlockPairHost.readCounter_succ_val (M : ℕ) [NeZero (2 * (2 * M))]
    (x : BlockPairHost.Mem M) :
    (BlockPairHost.readCounter M x + 1).val
      = (((BlockPairHost.stateEquiv M x : Fin _) : ℕ) / 2 ^ 16 % (2 * (2 * M) * 24) + 1)
          % (2 * (2 * M) * 24) := by
  rw [val_add_one, BlockPairHost.readCounter_val_eq]

private theorem bit_decide_eq (k : ℕ) (hk : k < 2) : (if decide (k = 1) then (1 : ℕ) else 0) =
    k := by
  interval_cases k <;> decide

private theorem xor_not_bit (p q : Bool) :
    (if xor (!p) q then (1 : ℕ) else 0)
      = (1 + (if p then 1 else 0) + (if q then 1 else 0)) % 2 := by
  cases p <;> cases q <;> decide

/-- **The window block updates correctly.** Bits `9..15` shift down from `s` unchanged
(`BlockPairHost.subUpdate`'s shift case); bit `15` is the new bit `BlockPairHost.subUpdate` writes —
`xor_not_bit` matches it to `w7` exactly, given the code bit (`decNum_eq_hostDecodeRule`) and the
tape bit
(`BlockPairHost.tape_eq_decide_hostTapeBit`, `BlockPairHost.readCounter_succ_val`). -/
private theorem hostStepNum_window (M : ℕ) [NeZero (2 * (2 * M))] (x : BlockPairHost.Mem M) :
    (((BlockPairHost.stateEquiv M (BlockPairHost.subUpdate M x) : Fin _) : ℕ) / 2 ^ 8) % 2 ^ 8
      = (((BlockPairHost.stateEquiv M x : Fin _) : ℕ) / 2 ^ 9) % 2 ^ 7
        + 2 ^ 7 * ((1 + numBitN ((BlockPairHost.stateEquiv M x : Fin _) : ℕ)
              (8 + decNum ((BlockPairHost.stateEquiv M x : Fin _) : ℕ))
            + hostTapeBit (2 * (2 * M) * 24)
                ((((BlockPairHost.stateEquiv M x : Fin _) : ℕ) / 2 ^ 16 % (2 * (2 * M) * 24) + 1)
                  % (2 * (2 * M) * 24))) % 2) := by
  rw [shift_mod_pow_eq_sum, Finset.sum_range_succ]
  have hlow : ∀ i : Fin 7,
      numBitN ((BlockPairHost.stateEquiv M (BlockPairHost.subUpdate M x) : Fin _) : ℕ) (8 + (i : ℕ))
        = numBitN ((BlockPairHost.stateEquiv M x : Fin _) : ℕ) (9 + (i : ℕ)) := by
    intro i
    have hi7 : (i : ℕ) < 7 := i.isLt
    have hb8 : (i : ℕ) < 8 := by omega
    have hb8' : (i : ℕ) + 1 < 8 := by omega
    have hd1 := BlockPairHost.stateEquiv_digit M (BlockPairHost.subUpdate M x)
      (Sum.inr (Sum.inl (⟨(i : ℕ), hb8⟩ : Fin 8)))
    rw [BlockPairHost.idxEquiv_inr_inl] at hd1
    have hstep : BlockPairHost.subUpdate M x (Sum.inr (Sum.inl (⟨(i : ℕ), hb8⟩ : Fin 8)))
        = x (Sum.inr (Sum.inl (⟨(i : ℕ) + 1, hb8'⟩ : Fin 8))) := by
      simp only [BlockPairHost.subUpdate]
      rw [dite_eq_left hb8']
    have hd2 := BlockPairHost.stateEquiv_digit M x (Sum.inr (Sum.inl (⟨(i : ℕ) + 1, hb8'⟩ : Fin 8)))
    rw [BlockPairHost.idxEquiv_inr_inl] at hd2
    rw [hd1, hstep]
    rw [show (8 : ℕ) + ((i : ℕ) + 1) = 9 + (i : ℕ) from by ring] at hd2
    exact hd2.symm
  have hsumlow : (∑ i ∈ Finset.range 7,
        numBitN ((BlockPairHost.stateEquiv M (BlockPairHost.subUpdate M x) : Fin _) : ℕ) (8 + i)
          * 2 ^ i)
      = ((BlockPairHost.stateEquiv M x : Fin _) : ℕ) / 2 ^ 9 % 2 ^ 7 := by
    rw [shift_mod_pow_eq_sum]
    exact Finset.sum_congr rfl (fun i hi => by rw [hlow ⟨i, Finset.mem_range.mp hi⟩])
  rw [hsumlow]
  congr 1
  have hb8_7 : (7 : ℕ) < 8 := by norm_num
  have hd7 := BlockPairHost.stateEquiv_digit M (BlockPairHost.subUpdate M x)
    (Sum.inr (Sum.inl (⟨7, hb8_7⟩ : Fin 8)))
  rw [BlockPairHost.idxEquiv_inr_inl] at hd7
  have hstep7 : BlockPairHost.subUpdate M x (Sum.inr (Sum.inl (⟨7, hb8_7⟩ : Fin 8)))
      = xor (!(x (Sum.inr (Sum.inl (BlockPairHost.decodeRule M x)))))
          (BlockPairHost.tape M (BlockPairHost.readCounter M x + 1)) := by
    simp only [BlockPairHost.subUpdate]
    rw [dite_eq_right (by norm_num : ¬ (7 : ℕ) + 1 < 8)]
  rw [show (8 : ℕ) + 7 = 15 from rfl] at hd7
  rw [hd7, hstep7, xor_not_bit]
  have ha : (if x (Sum.inr (Sum.inl (BlockPairHost.decodeRule M x))) then (1 : ℕ) else 0)
      = numBitN ((BlockPairHost.stateEquiv M x : Fin _) : ℕ)
          (8 + decNum ((BlockPairHost.stateEquiv M x : Fin _) : ℕ)) := by
    rw [decNum_eq_hostDecodeRule]
    have hd := BlockPairHost.stateEquiv_digit M x (Sum.inr (Sum.inl (BlockPairHost.decodeRule M x)))
    rw [BlockPairHost.idxEquiv_inr_inl] at hd
    exact hd.symm
  have hb : (if BlockPairHost.tape M (BlockPairHost.readCounter M x + 1) then (1 : ℕ) else 0)
      = hostTapeBit (2 * (2 * M) * 24)
          ((((BlockPairHost.stateEquiv M x : Fin _) : ℕ) / 2 ^ 16 % (2 * (2 * M) * 24) + 1)
            % (2 * (2 * M) * 24)) := by
    have hval : (BlockPairHost.readCounter M x + 1 : ZMod (2 * (2 * M) * 24))
        = (((BlockPairHost.readCounter M x + 1).val : ℕ) : ZMod (2 * (2 * M) * 24)) :=
      (ZMod.natCast_zmod_val _).symm
    rw [hval, BlockPairHost.tape_eq_decide_hostTapeBit M _ (ZMod.val_lt _),
      BlockPairHost.readCounter_succ_val]
    exact bit_decide_eq _ (Nat.mod_lt _ (by norm_num))
  rw [ha, hb]
  ring

/-! ## The step, packed: definition and the bridge -/

/-- **The host's own update, packed on the numeral carrier.** `N` is `Π := 2 * (2 * M) * 24`; the
code block (bits `0..7`) is copied, the window shifts with its top bit `w7` the design's
`xor(!(decoded window bit), tape bit)`, and the counter block (from bit `16`) advances by one mod
`N`. Built to match `hostStepNum_code`/`hostStepNum_window`/`hostStepNum_counter` term for term. -/
def hostStepNum (N s : ℕ) : ℕ :=
  (s % 2 ^ 8)
    + 2 ^ 8 * ((s / 2 ^ 9) % 2 ^ 7
        + 2 ^ 7 * ((1 + numBitN s (8 + decNum s)
            + hostTapeBit N ((s / 2 ^ 16 % N + 1) % N)) % 2))
    + 2 ^ 16 * ((s / 2 ^ 16 % N + 1) % N)

/-- **The step is correct**: `hostStepNum`, run on a packed host state, computes the packed
image of `BlockPairHost.subUpdate`'s own step. `block3_decomp` splits the target into its three
blocks;
`hostStepNum_code`/`hostStepNum_window`/`hostStepNum_counter` match each one. -/
theorem hostStepNum_stateEquiv (M : ℕ) [NeZero (2 * (2 * M))] (x : BlockPairHost.Mem M) :
    hostStepNum (2 * (2 * M) * 24) ((BlockPairHost.stateEquiv M x : Fin _) : ℕ)
      = ((BlockPairHost.stateEquiv M (BlockPairHost.subUpdate M x) : Fin _) : ℕ) := by
  rw [hostStepNum, block3_decomp
      ((BlockPairHost.stateEquiv M (BlockPairHost.subUpdate M x) : Fin _) : ℕ),
    hostStepNum_code, hostStepNum_window, hostStepNum_counter]

/-! ## The frame, packed: definition and the bridge -/

/-- **The frame's own read, packed on the numeral carrier.** `BlockPairHost.frame` reads the counter
register back and reduces to its low `κ` bits; `BlockPairHost.readCounter_val_eq` gives the raw
counter value directly off
the packed state's bits `16 .. 16 + Nat.size N`. -/
def frameStepNum (N κ s : ℕ) : ℕ := s / 2 ^ 16 % N % 2 ^ κ

/-- **The frame read is correct.** -/
theorem frameStepNum_stateEquiv (M : ℕ) [NeZero (2 * (2 * M))] (x : BlockPairHost.Mem M) :
    frameStepNum (2 * (2 * M) * 24) (BlockPairHost.frameBits M)
      ((BlockPairHost.stateEquiv M x : Fin _) : ℕ)
      = ((BlockPairHost.frame M (BlockPairHost.stateEquiv M x) : Fin _) : ℕ) := by
  rw [frameStepNum, BlockPairHost.frame]
  simp only [Equiv.symm_apply_apply]
  rw [BlockPairHost.readCounter_val_eq]

/-! ## Primitive recursion -/

private theorem hpow2 : Primrec₂ ((· ^ ·) : ℕ → ℕ → ℕ) := Primrec₂.unpaired'.1 Nat.Primrec.pow

private theorem primrec_list_sum {α : Type*} [Primcodable α] {f : α → List ℕ} (hf : Primrec f) :
    Primrec fun a => (f a).sum :=
  (Primrec.list_foldr hf (Primrec.const 0)
      (Primrec.nat_add.comp (Primrec.fst.comp Primrec.snd)
        (Primrec.snd.comp Primrec.snd)).to₂).of_eq
    fun a => by simp [List.sum_eq_foldr]

private theorem primrec_tmBit : Primrec tmBit := by
  have hinner : Primrec₂ fun (i : ℕ) (j : ℕ) => i / 2 ^ j % 2 :=
    Primrec₂.mk (Primrec.nat_mod.comp
      (Primrec.nat_div.comp Primrec.fst (hpow2.comp (Primrec.const 2) Primrec.snd))
      (Primrec.const 2))
  exact (primrec_list_sum
    (Primrec.list_map (Primrec.list_range.comp (Primrec.succ.comp Primrec.id)) hinner)).of_eq
      fun i => rfl

private theorem primrec_tmPrefixBit : Primrec tmPrefixBit := by
  have hmod : Primrec fun n : ℕ => n % 2 := Primrec.nat_mod.comp Primrec.id (Primrec.const 2)
  have hdiv : Primrec fun n : ℕ => n / 2 := Primrec.nat_div.comp Primrec.id (Primrec.const 2)
  exact (Primrec.nat_add.comp hdiv
    (Primrec.ite (PrimrecRel.comp Primrec.eq hmod (Primrec.const 1))
      (primrec_tmBit.comp hdiv) (Primrec.const 0))).of_eq
    fun n => by rw [tmPrefixBit]

private theorem primrec_blockSignBit : Primrec blockSignBit := by
  have h1 : Primrec fun j : ℕ => (j + 1) / 2 :=
    Primrec.nat_div.comp Primrec.succ (Primrec.const 2)
  have h2 : Primrec fun j : ℕ => j / 2 := Primrec.nat_div.comp Primrec.id (Primrec.const 2)
  exact (Primrec.nat_add.comp (primrec_tmPrefixBit.comp h1) (primrec_tmPrefixBit.comp h2)).of_eq
    fun j => rfl

private theorem primrec_wordUBit : Primrec wordUBit :=
  (Primrec₂.comp (Primrec.list_getD 0)
      (Primrec.const [1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1, 1, 1, 1, 0, 1, 1, 0, 0, 0])
      Primrec.id).of_eq
    fun p => by rw [wordUBit]; rfl

private theorem primrec_wordVBit : Primrec wordVBit :=
  (Primrec₂.comp (Primrec.list_getD 0)
      (Primrec.const [0, 0, 1, 0, 1, 0, 0, 0, 1, 1, 0, 1, 0, 1, 1, 1, 0, 0, 1, 0, 1, 0, 0, 0])
      Primrec.id).of_eq
    fun p => by rw [wordVBit]; rfl

private theorem primrec_blockWordBit : Primrec₂ blockWordBit := by
  have hmod : Primrec fun q : ℕ × ℕ => q.1 % 2 := Primrec.nat_mod.comp Primrec.fst (Primrec.const 2)
  exact Primrec₂.mk (Primrec.ite
    (PrimrecRel.comp Primrec.eq hmod (Primrec.const 0))
    (primrec_wordUBit.comp Primrec.snd) (primrec_wordVBit.comp Primrec.snd))

private theorem primrec_designExp : Primrec designExp := by
  have hdiv : Primrec fun u : ℕ => u / 24 := Primrec.nat_div.comp Primrec.id (Primrec.const 24)
  have hmod : Primrec fun u : ℕ => u % 24 := Primrec.nat_mod.comp Primrec.id (Primrec.const 24)
  exact (Primrec.nat_add.comp (primrec_blockSignBit.comp hdiv)
    (primrec_blockWordBit.comp hdiv hmod)).of_eq fun u => rfl

private theorem primrec_hostTapeBit : Primrec₂ hostTapeBit := by
  have hN : Primrec fun q : ℕ × ℕ => q.1 := Primrec.fst
  have hu : Primrec fun q : ℕ × ℕ => q.2 := Primrec.snd
  have hshift : Primrec fun q : ℕ × ℕ => (q.2 + q.1 - 8) % q.1 :=
    Primrec.nat_mod.comp (Primrec.nat_sub.comp (Primrec.nat_add.comp hu hN) (Primrec.const 8)) hN
  exact Primrec₂.mk (Primrec.nat_mod.comp
    (Primrec.nat_add.comp
      (Primrec.nat_add.comp (primrec_designExp.comp hu) (primrec_designExp.comp hshift))
      (Primrec.const 1))
    (Primrec.const 2))

private theorem primrec_decNum : Primrec decNum := by
  have hb : ∀ k : ℕ, Primrec fun s : ℕ => numBitN s k := fun k =>
    Primrec.nat_mod.comp
      (Primrec.nat_div.comp Primrec.id (Primrec.const (2 ^ k))) (Primrec.const 2)
  have heq : ∀ k : ℕ, PrimrecPred fun s : ℕ => numBitN s k = 1 := fun k =>
    PrimrecRel.comp Primrec.eq (hb k) (Primrec.const 1)
  exact (Primrec.ite (heq 0) (Primrec.const 0)
    (Primrec.ite (heq 1) (Primrec.const 1)
      (Primrec.ite (heq 2) (Primrec.const 2)
        (Primrec.ite (heq 3) (Primrec.const 3)
          (Primrec.ite (heq 4) (Primrec.const 4)
            (Primrec.ite (heq 5) (Primrec.const 5)
              (Primrec.ite (heq 6) (Primrec.const 6)
                (Primrec.ite (heq 7) (Primrec.const 7) (Primrec.const 0))))))))).of_eq
    fun s => by rw [decNum]

private theorem primrec_hostStepNum : Primrec₂ hostStepNum := by
  have hN : Primrec fun q : ℕ × ℕ => q.1 := Primrec.fst
  have hs : Primrec fun q : ℕ × ℕ => q.2 := Primrec.snd
  have hvNext : Primrec fun q : ℕ × ℕ => (q.2 / 2 ^ 16 % q.1 + 1) % q.1 :=
    Primrec.nat_mod.comp
      (Primrec.nat_add.comp
        (Primrec.nat_mod.comp (Primrec.nat_div.comp hs (Primrec.const (2 ^ 16))) hN)
        (Primrec.const 1))
      hN
  have hdec : Primrec fun q : ℕ × ℕ => decNum q.2 := primrec_decNum.comp hs
  have hbit : Primrec fun q : ℕ × ℕ => numBitN q.2 (8 + decNum q.2) :=
    Primrec.nat_mod.comp
      (Primrec.nat_div.comp hs
        (hpow2.comp (Primrec.const 2) (Primrec.nat_add.comp (Primrec.const 8) hdec)))
      (Primrec.const 2)
  have htape : Primrec fun q : ℕ × ℕ => hostTapeBit q.1 ((q.2 / 2 ^ 16 % q.1 + 1) % q.1) :=
    primrec_hostTapeBit.comp hN hvNext
  have hw7 : Primrec fun q : ℕ × ℕ =>
      (1 + numBitN q.2 (8 + decNum q.2)
        + hostTapeBit q.1 ((q.2 / 2 ^ 16 % q.1 + 1) % q.1)) % 2 :=
    Primrec.nat_mod.comp
      (Primrec.nat_add.comp (Primrec.nat_add.comp (Primrec.const 1) hbit) htape)
      (Primrec.const 2)
  have hwinlow : Primrec fun q : ℕ × ℕ => q.2 / 2 ^ 9 % 2 ^ 7 :=
    Primrec.nat_mod.comp (Primrec.nat_div.comp hs (Primrec.const (2 ^ 9))) (Primrec.const (2 ^ 7))
  have hwin : Primrec fun q : ℕ × ℕ => q.2 / 2 ^ 9 % 2 ^ 7 + 2 ^ 7 *
      ((1 + numBitN q.2 (8 + decNum q.2)
        + hostTapeBit q.1 ((q.2 / 2 ^ 16 % q.1 + 1) % q.1)) % 2) :=
    Primrec.nat_add.comp hwinlow (Primrec.nat_mul.comp (Primrec.const (2 ^ 7)) hw7)
  have hcode : Primrec fun q : ℕ × ℕ => q.2 % 2 ^ 8 :=
    Primrec.nat_mod.comp hs (Primrec.const (2 ^ 8))
  exact Primrec₂.mk (Primrec.nat_add.comp
    (Primrec.nat_add.comp hcode (Primrec.nat_mul.comp (Primrec.const (2 ^ 8)) hwin))
    (Primrec.nat_mul.comp (Primrec.const (2 ^ 16)) hvNext))

private theorem primrec_frameStepNum : Primrec fun q : (ℕ × ℕ) × ℕ =>
    frameStepNum q.1.1 q.1.2 q.2 := by
  have hN : Primrec fun q : (ℕ × ℕ) × ℕ => q.1.1 := Primrec.fst.comp Primrec.fst
  have hκ : Primrec fun q : (ℕ × ℕ) × ℕ => q.1.2 := Primrec.snd.comp Primrec.fst
  have hs : Primrec fun q : (ℕ × ℕ) × ℕ => q.2 := Primrec.snd
  exact (Primrec.nat_mod.comp
    (Primrec.nat_mod.comp (Primrec.nat_div.comp hs (Primrec.const (2 ^ 16))) hN)
    (hpow2.comp (Primrec.const 2) hκ)).of_eq fun q => rfl

/-! ## Tabulation and the builders -/

/-- **The host table**: the packed step tabulated over every state, as one function of the paired
input `⟨M, B⟩` (`B := Nat.size Π`). -/
def hostTableFn (a : ℕ) : ℕ :=
  Encodable.encode ((List.range (2 ^ (8 + (8 + a.unpair.2)))).map
    (fun s => hostStepNum (2 * (2 * a.unpair.1) * 24) s))

theorem primrec_hostTableFn : Primrec hostTableFn := by
  have hM : Primrec fun a : ℕ => a.unpair.1 := Primrec.fst.comp Primrec.unpair
  have hB : Primrec fun a : ℕ => a.unpair.2 := Primrec.snd.comp Primrec.unpair
  have hN : Primrec fun a : ℕ => 2 * (2 * a.unpair.1) * 24 :=
    Primrec.nat_mul.comp
      (Primrec.nat_mul.comp (Primrec.const 2) (Primrec.nat_mul.comp (Primrec.const 2) hM))
      (Primrec.const 24)
  have hlen : Primrec fun a : ℕ => 2 ^ (8 + (8 + a.unpair.2)) :=
    hpow2.comp (Primrec.const 2)
      (Primrec.nat_add.comp (Primrec.const 8) (Primrec.nat_add.comp (Primrec.const 8) hB))
  have hinner : Primrec₂ fun (a : ℕ) (s : ℕ) => hostStepNum (2 * (2 * a.unpair.1) * 24) s :=
    Primrec₂.mk (primrec_hostStepNum.comp (hN.comp Primrec.fst) Primrec.snd)
  exact Primrec.encode.comp (Primrec.list_map (Primrec.list_range.comp hlen) hinner)

theorem hostTableFn_eq (M : ℕ) [NeZero (2 * (2 * M))] :
    hostTableFn (Nat.pair M (Nat.size (2 * (2 * M) * 24))) = lensCode (BlockPairHost.packed M) := by
  rw [hostTableFn]
  simp only [Nat.unpair_pair]
  conv_rhs => rw [lensCode, lensTable_range]
  congr 1
  refine List.map_congr_left fun s hs => ?_
  have hsN : s < 2 ^ (8 + (8 + Nat.size (2 * (2 * M) * 24))) := List.mem_range.mp hs
  rw [dite_eq_left hsN, BlockPairHost.packed]
  have hx := hostStepNum_stateEquiv M ((BlockPairHost.stateEquiv M).symm (⟨s, hsN⟩ : Fin _))
  rw [Equiv.apply_symm_apply] at hx
  exact hx

/-- `hostTableFn` is partial recursive. -/
theorem partrec_hostTableFn : Nat.Partrec (fun a : ℕ => (hostTableFn a : ℕ)) :=
  _root_.Partrec.nat_iff.mp (Primrec.to_comp primrec_hostTableFn).partrec

/-- **The fixed host builder code**, extracted from universality: one program taking
`⟨M, Nat.size Π⟩`. -/
noncomputable def hostBuilder : Nat.Partrec.Code :=
  Classical.choose (Nat.Partrec.Code.exists_code.mp partrec_hostTableFn)

theorem eval_hostBuilder (a : ℕ) :
    Nat.Partrec.Code.eval hostBuilder a = Part.some (hostTableFn a) := by
  have h := congrFun (Classical.choose_spec
    (Nat.Partrec.Code.exists_code.mp partrec_hostTableFn)) a
  simpa [hostBuilder] using h

/-- **The frame table**: the frame's own read, tabulated over every state, over the paired input
`⟨M, ⟨B, κ⟩⟩`. -/
def frameTableFn (a : ℕ) : ℕ :=
  Encodable.encode ((List.range (2 ^ (8 + (8 + a.unpair.2.unpair.1)))).map
    (fun s => frameStepNum (2 * (2 * a.unpair.1) * 24) a.unpair.2.unpair.2 s))

theorem primrec_frameTableFn : Primrec frameTableFn := by
  have hM : Primrec fun a : ℕ => a.unpair.1 := Primrec.fst.comp Primrec.unpair
  have hBV : Primrec fun a : ℕ => a.unpair.2 := Primrec.snd.comp Primrec.unpair
  have hB : Primrec fun a : ℕ => a.unpair.2.unpair.1 := Primrec.fst.comp (Primrec.unpair.comp hBV)
  have hκ : Primrec fun a : ℕ => a.unpair.2.unpair.2 := Primrec.snd.comp (Primrec.unpair.comp hBV)
  have hN : Primrec fun a : ℕ => 2 * (2 * a.unpair.1) * 24 :=
    Primrec.nat_mul.comp
      (Primrec.nat_mul.comp (Primrec.const 2) (Primrec.nat_mul.comp (Primrec.const 2) hM))
      (Primrec.const 24)
  have hlen : Primrec fun a : ℕ => 2 ^ (8 + (8 + a.unpair.2.unpair.1)) :=
    hpow2.comp (Primrec.const 2)
      (Primrec.nat_add.comp (Primrec.const 8) (Primrec.nat_add.comp (Primrec.const 8) hB))
  have hinner : Primrec₂ fun (a : ℕ) (s : ℕ) =>
      frameStepNum (2 * (2 * a.unpair.1) * 24) a.unpair.2.unpair.2 s :=
    Primrec₂.mk (primrec_frameStepNum.comp
      (Primrec.pair (Primrec.pair (hN.comp Primrec.fst) (hκ.comp Primrec.fst)) Primrec.snd))
  exact Primrec.encode.comp (Primrec.list_map (Primrec.list_range.comp hlen) hinner)

theorem frameTableFn_eq (M : ℕ) [NeZero (2 * (2 * M))] :
    frameTableFn (Nat.pair M (Nat.pair (Nat.size (2 * (2 * M) * 24)) (BlockPairHost.frameBits M)))
      = lensCode (BlockPairHost.frame M) := by
  rw [frameTableFn]
  simp only [Nat.unpair_pair]
  conv_rhs => rw [lensCode, lensTable_range]
  congr 1
  refine List.map_congr_left fun s hs => ?_
  have hsN : s < 2 ^ (8 + (8 + Nat.size (2 * (2 * M) * 24))) := List.mem_range.mp hs
  rw [dite_eq_left hsN]
  have hx := frameStepNum_stateEquiv M ((BlockPairHost.stateEquiv M).symm (⟨s, hsN⟩ : Fin _))
  rw [Equiv.apply_symm_apply] at hx
  exact hx

/-- `frameTableFn` is partial recursive. -/
theorem partrec_frameTableFn : Nat.Partrec (fun a : ℕ => (frameTableFn a : ℕ)) :=
  _root_.Partrec.nat_iff.mp (Primrec.to_comp primrec_frameTableFn).partrec

/-- **The fixed frame builder code**, extracted from universality: one program taking
`⟨M, ⟨Nat.size Π, BlockPairHost.frameBits M⟩⟩`. -/
noncomputable def frameBuilder : Nat.Partrec.Code :=
  Classical.choose (Nat.Partrec.Code.exists_code.mp partrec_frameTableFn)

theorem eval_frameBuilder (a : ℕ) :
    Nat.Partrec.Code.eval frameBuilder a = Part.some (frameTableFn a) := by
  have h := congrFun (Classical.choose_spec
    (Nat.Partrec.Code.exists_code.mp partrec_frameTableFn)) a
  simpa [frameBuilder] using h

/-! ## The prices -/

/-- **The host's rule is owned at `O(log Π)`, an exhibited program, no import.** `hostBuilder`
takes only `M` and `Nat.size Π` — both fed as `bconst` numerals, no macro-law code `cG` — so the
host's own table is described in `elen hostBuilder + O(size M + size (size Π))` bits, an absolute
constant plus logarithms of the two structural parameters and nothing that scales with the state
count. -/
private theorem hostBuilder_computes (M : ℕ) [NeZero (2 * (2 * M))] : Computes
    (Nat.Partrec.Code.comp hostBuilder
      (Nat.Partrec.Code.pair (bconst M) (bconst (Nat.size (2 * (2 * M) * 24)))))
    (lensCode (BlockPairHost.packed M)) := by
  have hp : Nat.Partrec.Code.eval
      (Nat.Partrec.Code.pair (bconst M) (bconst (Nat.size (2 * (2 * M) * 24)))) 0
      = Part.some (Nat.pair M (Nat.size (2 * (2 * M) * 24))) := by
    change Nat.pair <$> _ <*> _ = _
    rw [eval_bconst M 0, eval_bconst (Nat.size (2 * (2 * M) * 24)) 0]; simp [Seq.seq]
  change Nat.Partrec.Code.eval _ 0 = _
  rw [eval_comp_some hp, eval_hostBuilder, hostTableFn_eq]

private theorem frameBuilder_computes (M : ℕ) [NeZero (2 * (2 * M))] : Computes
    (Nat.Partrec.Code.comp frameBuilder
      (Nat.Partrec.Code.pair (bconst M)
        (Nat.Partrec.Code.pair (bconst (Nat.size (2 * (2 * M) * 24)))
          (bconst (BlockPairHost.frameBits M)))))
    (lensCode (BlockPairHost.frame M)) := by
  have hp2 : Nat.Partrec.Code.eval
      (Nat.Partrec.Code.pair (bconst (Nat.size (2 * (2 * M) * 24)))
        (bconst (BlockPairHost.frameBits M))) 0
      = Part.some (Nat.pair (Nat.size (2 * (2 * M) * 24)) (BlockPairHost.frameBits M)) := by
    change Nat.pair <$> _ <*> _ = _
    rw [eval_bconst (Nat.size (2 * (2 * M) * 24)) 0, eval_bconst (BlockPairHost.frameBits M) 0]
    simp [Seq.seq]
  have hp1 : Nat.Partrec.Code.eval
      (Nat.Partrec.Code.pair (bconst M)
        (Nat.Partrec.Code.pair (bconst (Nat.size (2 * (2 * M) * 24)))
          (bconst (BlockPairHost.frameBits M))))
      0
      = Part.some
          (Nat.pair M (Nat.pair (Nat.size (2 * (2 * M) * 24)) (BlockPairHost.frameBits M))) := by
    change Nat.pair <$> _ <*> _ = _
    rw [eval_bconst M 0, hp2]; simp [Seq.seq]
  change Nat.Partrec.Code.eval _ 0 = _
  rw [eval_comp_some hp1, eval_frameBuilder, frameTableFn_eq]

theorem KE_hostPacked_le (M : ℕ) [NeZero (2 * (2 * M))] :
    KE (lensCode (BlockPairHost.packed M))
      ≤ elen hostBuilder
        + (15 + elen dbl) * (Nat.size M + Nat.size (Nat.size (2 * (2 * M) * 24)))
        + (2 * (15 + elen dbl) + 15) := by
  have hle := KE_le (hostBuilder_computes M)
  have hbM := elen_bconst_le M
  have hbB := elen_bconst_le (Nat.size (2 * (2 * M) * 24))
  simp only [E_len_comp, E_len_pair] at hle
  rw [Nat.mul_add]
  omega

/-- **The frame's own read is owned at `O(log Π + log κ)`, an exhibited program, no import.**
`frameBuilder` takes `M`, `Nat.size Π` and `BlockPairHost.frameBits M` — three `bconst` numerals —
so the
frame's table is described in `elen frameBuilder + O(size M + size (size Π) + size κ)` bits. -/
theorem KE_hostFrame_le (M : ℕ) [NeZero (2 * (2 * M))] :
    KE (lensCode (BlockPairHost.frame M))
      ≤ elen frameBuilder
        + (15 + elen dbl) *
            (Nat.size M + Nat.size (Nat.size (2 * (2 * M) * 24)) + Nat.size
              (BlockPairHost.frameBits M))
        + (3 * (15 + elen dbl) + 30) := by
  have hle := KE_le (frameBuilder_computes M)
  have hbM := elen_bconst_le M
  have hbB := elen_bconst_le (Nat.size (2 * (2 * M) * 24))
  have hbκ := elen_bconst_le (BlockPairHost.frameBits M)
  simp only [E_len_comp, E_len_pair] at hle
  rw [Nat.mul_add, Nat.mul_add]
  omega

/-! ## The payoff -/

/-- **The emergence guest is owned within an absolute constant plus `O(log Π)`, at an exhibited
program — [Guests] §6 Theorem 6.1's affordability input met by a designed host, [Inevitability]
§5 Theorem 5.8's growth clause with its affordability machine-checked.**
`BlockPairHost.card_orbit_le_cbHue`, applied at the codes
`hostBuilder_computes`/`frameBuilder_computes` exhibit, replaces its two parametric
`elen cU`/`elen cθ` terms with the absolute `elen hostBuilder + elen frameBuilder` plus a budget
logarithmic in `M`, `Nat.size Π` and `BlockPairHost.frameBits M` — nothing that scales with the
state
count `2 ^ (16 + Nat.size Π)`. -/
theorem BlockPairHost.card_orbit_le_cbHue_cheap (M : ℕ) [NeZero (2 * (2 * M))] :
    Nat.card ↥(orbit (Equiv.Perm ↥(ALT.core (BlockPairHost.packed M)))
        (ALT.coreLens (BlockPairHost.packed M)
          (ALT.emergeLens (BlockPairHost.packed M) (BlockPairHost.frame M) 0)))
      ≤ ALT.CbHue (BlockPairHost.packed M)
          (AdditiveComplexity.elen ALT.emergeBuilder
            + AdditiveComplexity.elen hostBuilder + AdditiveComplexity.elen frameBuilder
            + 2 * (15 + elen dbl) *
                (Nat.size M + Nat.size (Nat.size (2 * (2 * M) * 24)))
            + (15 + elen dbl) * Nat.size (BlockPairHost.frameBits M)
            + (5 * (15 + elen dbl) + 45)) := by
  have hbase := BlockPairHost.card_orbit_le_cbHue M _ _ (hostBuilder_computes M)
    (frameBuilder_computes M)
  refine hbase.trans (CbHue_mono (BlockPairHost.packed M) ?_)
  set p := (15 + elen dbl) * Nat.size M with hp
  set q := (15 + elen dbl) * Nat.size (Nat.size (2 * (2 * M) * 24)) with hq
  set r := (15 + elen dbl) * Nat.size (BlockPairHost.frameBits M) with hr
  have heU : elen
      (Nat.Partrec.Code.comp hostBuilder
        (Nat.Partrec.Code.pair (bconst M) (bconst (Nat.size (2 * (2 * M) * 24)))))
      ≤ elen hostBuilder + p + q + (2 * (15 + elen dbl) + 6) := by
    have hbM := elen_bconst_le M
    have hbB := elen_bconst_le (Nat.size (2 * (2 * M) * 24))
    simp only [E_len_comp, E_len_pair]
    omega
  have heθ : elen
      (Nat.Partrec.Code.comp frameBuilder
        (Nat.Partrec.Code.pair (bconst M)
          (Nat.Partrec.Code.pair (bconst (Nat.size (2 * (2 * M) * 24)))
              (bconst (BlockPairHost.frameBits M)))))
      ≤ elen frameBuilder + p + q + r + (3 * (15 + elen dbl) + 9) := by
    have hbM := elen_bconst_le M
    have hbB := elen_bconst_le (Nat.size (2 * (2 * M) * 24))
    have hbκ := elen_bconst_le (BlockPairHost.frameBits M)
    simp only [E_len_comp, E_len_pair]
    omega
  rw [show 2 * (15 + elen dbl) * (Nat.size M + Nat.size (Nat.size (2 * (2 * M) * 24)))
      = p + p + q + q from by rw [hp, hq]; ring]
  omega

end ALT
