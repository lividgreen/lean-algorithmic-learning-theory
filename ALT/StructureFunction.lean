import Mathlib
import ALT.PrefixInvariance

-- Tier-1 formal check, not Mathlib-destined: opt out of the house-style linters.
set_option linter.style.header false
set_option linter.style.longLine false

/-!
# Kolmogorov structure function — the 45° / geometric lower bound (Paper II §2.3, FV-14)

Provenance: `02_mdl_dominance_and_discovery.md` §2.3 (the structure-function backdrop of Theorem 2.1)
and Vereshchagin–Vitányi (2004) / Shen–Uspensky–Vereshchagin. This file makes §2.3's load-bearing
inequality genuine on the **additive carrier** (`AdditiveComplexity.KE`, `ALT/AdditiveComplexity.lean`).
Extends `ALT/BinaryConstant.lean` (`bconst`, `eval_bconst`, `elen_bconst_le`, `dbl`) and reuses
`ALT/PrefixInvariance.lean`'s `computes_comp` (the compose eval law).

## The slice proved (the graph "cannot drop faster than 45°")
For a string `x`, the structure function `h_x(α) = min { log|S| : x ∈ S, K(S) ≤ α }` over finite
models `S ∋ x`. Every model on the graph yields a two-part description of `x` as `(model, index-in-S)`,
so `KE x ≤ α + c₁·h_x(α) + c₂` with explicit constants (`KE_le_structFn` / `structFn_ge`). The FULL
sufficient-statistic identity (`K(x) = α + h_x(α) + O(1)` at the minimal sufficient statistic) is OUT
of scope — it needs conditional complexity `KE(·|·)` + Symmetry of Information, which no prover has
(cf. Lee–Romashchenko); a registered follow-on.

## Model encoding (fidelity-sensitive; defended)
A **model containing `x`** is a `Code c` with `c.eval 0 = some (Encodable.encode L)` for a list
`L : List ℕ` that is `Nodup` and contains `x`. Choices:
* **`List ℕ`, not `Finset ℕ`.** Building the universality-extracted extractor needs `Primcodable`
  and the list-computability API (`Primrec.list_getD`, `decode`, `encode`), all present for `List ℕ`;
  `Primcodable (Finset ℕ)` computability is not readily available. Requiring **`L.Nodup`** makes
  `L.length` the genuine cardinality of the underlying set, so "cardinality is of the decoded object".
* **log-cardinality `= Nat.log 2 L.length`** (`⌊log₂|S|⌋`). The `⌊⌋`-vs-`⌈⌉`/real-`log` gap is `O(1)`,
  absorbed into `c₂` (the index needs `Nat.size i ≤ Nat.log 2 L.length + 1` bits).
* **Extraction** is the `nth ∘ (c, bconst i)`-shaped assembly `comp extractor (pair c (bconst i))`
  with `i = L.idxOf x`, all composition additive by `KE_comp_le`. `extractor` (list-index) and
  `mkSingleton` (`n ↦ encode [n]`) are fixed codes extracted from universality (like `dbl`); their
  `elen` are fixed uncontrolled constants.

## `structFn : ℕ∞`
`structFn x α = if (modelLogCards x α).Nonempty then (Nat.sInf … : ℕ∞) else ⊤`. `ℕ∞` for
`structFn_antitone` (⊤ = "no model of length `≤ α`", decreasing as `α` grows); the `if-Nonempty then
Nat.sInf` convention keeps the min at `ℕ` level so `Nat.sInf_mem` returns the achieving model. The
singleton `{x}` gives nonemptiness for `α ≥ KE x + c₀`.

## Constants (honest slopes; `c₁ ≠ 1` is expected)
* `c₀ = 3 + elen mkSingleton` — cost of wrapping the `x`-program into a singleton-list emitter.
* `c₁ = 15 + elen dbl` (`= κ`) — the per-bit cost of the binary index constant `bconst`; NOT `1`.
* `c₂ = 36 + elen extractor + 2·elen dbl` — extractor + two `pair`/`comp` opcodes + the `bconst`
  additive slack. The paper's `O(log)` slack absorbs any fixed `c₁`, `c₂`.

## Boundaries (docstring; reported to the wiring session)
* Full V&V identity / minimal sufficient statistic — needs conditional `KE(·|·)` + Symmetry of
  Information (no prover has either); the contribution-grade follow-on (item 3 remaining scope).
* Evaln-budgeted version — the F20 wall applies identically (eval-level only, like `prop_2_2_eval`).
* Paper II §2.3's use stays backdrop; this slice makes its load-bearing inequality genuine.
-/

namespace StructureFunction

open Nat.Partrec Nat.Partrec.Code KolmogorovComplexity AdditiveComplexity PrefixInvariance

/-! ## The list-index extractor and the singleton emitter (universality-extracted, like `dbl`) -/

/-- The list-index function: decode the first component of a pair to a `List ℕ` and index it by the
second component (junk `0` out of range). `extractFn (Nat.pair (encode L) i) = L.getD i 0`. -/
def extractFn (p : ℕ) : ℕ :=
  List.getD ((Encodable.decode (Nat.unpair p).1 : Option (List ℕ)).getD []) (Nat.unpair p).2 0

/-- `extractFn` is primitive recursive (decode + `List.getD` + `Nat.unpair`, all Primrec). -/
theorem primrec_extractFn : Primrec extractFn := by
  have h1 : Primrec (fun p : ℕ => (Nat.unpair p).1) := Primrec.fst.comp Primrec.unpair
  have h2 : Primrec (fun p : ℕ => (Nat.unpair p).2) := Primrec.snd.comp Primrec.unpair
  have h3 : Primrec (fun p : ℕ => (Encodable.decode (Nat.unpair p).1 : Option (List ℕ))) :=
    Primrec.decode.comp h1
  have h4 : Primrec (fun p : ℕ => ((Encodable.decode (Nat.unpair p).1 : Option (List ℕ)).getD [])) :=
    Primrec.option_getD.comp h3 (Primrec.const [])
  exact (Primrec.list_getD 0).comp h4 h2

theorem partrec_extractFn : Nat.Partrec (fun p : ℕ => (extractFn p : ℕ)) :=
  Partrec.nat_iff.mp primrec_extractFn.to_comp.partrec

/-- A fixed list-index code, extracted from universality. Noncomputable; `elen extractor` is a fixed
uncontrolled constant. -/
noncomputable def extractor : Code := Classical.choose (exists_code.mp partrec_extractFn)

/-- The extractor's eval law: `eval extractor p = extractFn p`. -/
theorem eval_extractor (p : ℕ) : extractor.eval p = Part.some (extractFn p) := by
  have h := congrFun (Classical.choose_spec (exists_code.mp partrec_extractFn)) p
  simpa [extractor] using h

/-- The singleton emitter: `n ↦ encode [n]`. -/
def mkSingletonFn (n : ℕ) : ℕ := Encodable.encode ([n] : List ℕ)

theorem computable_mkSingletonFn : Computable mkSingletonFn :=
  Computable.encode.comp (Computable.list_cons.comp Computable.id (Computable.const []))

theorem partrec_mkSingletonFn : Nat.Partrec (fun n : ℕ => (mkSingletonFn n : ℕ)) :=
  Partrec.nat_iff.mp computable_mkSingletonFn.partrec

/-- A fixed singleton-emitter code, extracted from universality. -/
noncomputable def mkSingleton : Code := Classical.choose (exists_code.mp partrec_mkSingletonFn)

/-- The singleton emitter's eval law: `eval mkSingleton n = encode [n]`. -/
theorem eval_mkSingleton (n : ℕ) : mkSingleton.eval n = Part.some (Encodable.encode [n]) := by
  have h := congrFun (Classical.choose_spec (exists_code.mp partrec_mkSingletonFn)) n
  simpa [mkSingleton, mkSingletonFn] using h

/-! ## The structure function -/

/-- The set of achievable log-cardinalities `Nat.log 2 |L|` over model codes of additive length
`≤ α` whose decoded (nodup) list contains `x`. -/
def modelLogCards (x α : ℕ) : Set ℕ :=
  { l | ∃ (c : Code) (L : List ℕ), elen c ≤ α ∧ c.eval 0 = Part.some (Encodable.encode L) ∧
        L.Nodup ∧ x ∈ L ∧ l = Nat.log 2 L.length }

/-- **The Kolmogorov structure function on the additive carrier.** `structFn x α` is the minimum
log-cardinality `Nat.log 2 |S|` over finite models `S ∋ x` describable by a code of additive length
`≤ α`; `⊤` when no such model exists. -/
noncomputable def structFn (x α : ℕ) : ℕ∞ :=
  open Classical in
  if (modelLogCards x α).Nonempty then ((sInf (modelLogCards x α) : ℕ) : ℕ∞) else ⊤

/-- More budget can only add models. -/
theorem modelLogCards_subset {x α α' : ℕ} (h : α ≤ α') :
    modelLogCards x α ⊆ modelLogCards x α' := by
  rintro l ⟨c, L, hcelen, hceval, hnodup, hxL, rfl⟩
  exact ⟨c, L, le_trans hcelen h, hceval, hnodup, hxL, rfl⟩

/-! ## The two-part description (per model) -/

/-- **Two-part description (per model).** A model code `c` outputting `encode L` (`L ∋ x`) yields a
description of `x` as `(model, index)`: `KE x ≤ elen c + c₁·log₂|L| + c₂` with `c₁ = 15 + elen dbl`,
`c₂ = 36 + elen extractor + 2·elen dbl`. Assembly `comp extractor (pair c (bconst i))`, `i = L.idxOf x`:
`pair` feeds `(encode L, i)` to the list-index `extractor`; `bconst i` costs `O(Nat.size i) = O(log₂|L|)`;
everything additive by `E_len_comp`/`E_len_pair` + `KE_le`. -/
theorem KE_le_of_model {x : ℕ} {c : Code} {L : List ℕ}
    (hceval : c.eval 0 = Part.some (Encodable.encode L)) (hx : x ∈ L) :
    KE x ≤ elen c + (15 + elen dbl) * Nat.log 2 L.length + (36 + elen extractor + 2 * elen dbl) := by
  have hilt : L.idxOf x < L.length := List.idxOf_lt_length_of_mem hx
  have hgetD : L.getD (L.idxOf x) 0 = x := by
    rw [List.getD_eq_getElem _ _ hilt]; exact List.getElem_idxOf hilt
  have h_inner : Computes (pair c (bconst (L.idxOf x))) (Nat.pair (Encodable.encode L) (L.idxOf x)) := by
    rw [Computes]
    change Nat.pair <$> eval c 0 <*> eval (bconst (L.idxOf x)) 0 = _
    rw [hceval, eval_bconst]; simp [Seq.seq]
  have h_ext : extractor.eval (Nat.pair (Encodable.encode L) (L.idxOf x)) = Part.some x := by
    rw [eval_extractor]; congr 1
    simp only [extractFn, Nat.unpair_pair, Encodable.encodek, Option.getD_some]
    exact hgetD
  have hA : Computes (comp extractor (pair c (bconst (L.idxOf x)))) x := computes_comp h_inner h_ext
  have hKEle := KE_le hA
  have e1 : elen (comp extractor (pair c (bconst (L.idxOf x))))
      = 6 + elen extractor + elen c + elen (bconst (L.idxOf x)) := by
    rw [E_len_comp, E_len_pair]; ring
  rw [e1] at hKEle
  have hsize : Nat.size (L.idxOf x) ≤ Nat.log 2 L.length + 1 := by
    rw [Nat.size_le]
    exact lt_of_lt_of_le hilt (le_of_lt (Nat.lt_pow_succ_log_self (by norm_num) _))
  have e2 : elen (bconst (L.idxOf x))
      ≤ (15 + elen dbl) * Nat.log 2 L.length + 2 * (15 + elen dbl) := by
    have hbc := elen_bconst_le (L.idxOf x)
    calc elen (bconst (L.idxOf x))
        ≤ (15 + elen dbl) * Nat.size (L.idxOf x) + (15 + elen dbl) := hbc
      _ ≤ (15 + elen dbl) * (Nat.log 2 L.length + 1) + (15 + elen dbl) := by gcongr
      _ = (15 + elen dbl) * Nat.log 2 L.length + 2 * (15 + elen dbl) := by ring
  calc KE x ≤ 6 + elen extractor + elen c + elen (bconst (L.idxOf x)) := hKEle
    _ ≤ 6 + elen extractor + elen c
          + ((15 + elen dbl) * Nat.log 2 L.length + 2 * (15 + elen dbl)) := by gcongr
    _ = elen c + (15 + elen dbl) * Nat.log 2 L.length
          + (36 + elen extractor + 2 * elen dbl) := by ring

/-! ## The four target theorems -/

/-- **(a) `structFn` is antitone in the budget.** More budget ⇒ smaller-or-equal minimal model. -/
theorem structFn_antitone (x : ℕ) {α α' : ℕ} (h : α ≤ α') : structFn x α' ≤ structFn x α := by
  unfold structFn
  by_cases hm : (modelLogCards x α).Nonempty
  · have hm' : (modelLogCards x α').Nonempty := hm.mono (modelLogCards_subset h)
    rw [if_pos hm, if_pos hm']
    exact_mod_cast Nat.sInf_le (modelLogCards_subset h (Nat.sInf_mem hm))
  · rw [if_neg hm]; exact le_top

/-- **(b) Singleton collapse.** For `α ≥ KE x + (3 + elen mkSingleton)` the singleton model `{x}` is
available, so `structFn x α = 0`. Witness `comp mkSingleton cx` (`cx` the `KE`-optimal code for `x`),
outputting `encode [x]`; `log₂ |[x]| = log₂ 1 = 0`. -/
theorem structFn_singleton (x : ℕ) {α : ℕ} (h : KE x + (3 + elen mkSingleton) ≤ α) :
    structFn x α = 0 := by
  obtain ⟨cx, hcx, hlx⟩ := exists_min_E x
  have hmodel : Computes (comp mkSingleton cx) (Encodable.encode [x]) :=
    computes_comp hcx (eval_mkSingleton x)
  have hlen : elen (comp mkSingleton cx) ≤ α := by rw [E_len_comp, hlx]; omega
  have h0mem : (0 : ℕ) ∈ modelLogCards x α :=
    ⟨comp mkSingleton cx, [x], hlen, hmodel, List.nodup_singleton x, by simp, by simp⟩
  have hm : (modelLogCards x α).Nonempty := ⟨0, h0mem⟩
  unfold structFn
  rw [if_pos hm]
  exact_mod_cast Nat.le_zero.mp (Nat.sInf_le h0mem)

/-- **(c) The 45° slice.** `KE x ≤ α + c₁·structFn x α + c₂` (`c₁ = 15 + elen dbl`,
`c₂ = 36 + elen extractor + 2·elen dbl`): every model on the structure-function graph gives a
two-part description of `x`, so the complexity cannot drop faster than the slope `c₁`. -/
theorem KE_le_structFn (x α : ℕ) :
    (KE x : ℕ∞) ≤ (α : ℕ∞) + ((15 + elen dbl : ℕ) : ℕ∞) * structFn x α
      + ((36 + elen extractor + 2 * elen dbl : ℕ) : ℕ∞) := by
  unfold structFn
  by_cases hm : (modelLogCards x α).Nonempty
  · rw [if_pos hm]
    obtain ⟨c, L, hcelen, hceval, _hnodup, hxL, hlcard⟩ := Nat.sInf_mem hm
    have hpm := KE_le_of_model hceval hxL
    have hfin : KE x ≤ α + (15 + elen dbl) * sInf (modelLogCards x α)
        + (36 + elen extractor + 2 * elen dbl) := by
      rw [hlcard]
      calc KE x ≤ elen c + (15 + elen dbl) * Nat.log 2 L.length
              + (36 + elen extractor + 2 * elen dbl) := hpm
        _ ≤ α + (15 + elen dbl) * Nat.log 2 L.length
              + (36 + elen extractor + 2 * elen dbl) := by gcongr
    exact_mod_cast hfin
  · rw [if_neg hm]
    have hc1 : ((15 + elen dbl : ℕ) : ℕ∞) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    rw [ENat.mul_top hc1]; simp

/-- **(d) The equivalent lower-bound form.** `(KE x − α − c₂)/c₁ ≤ structFn x α` (ℕ-subtraction /
`Nat.log`-division safe): the structure function is bounded below by the two-part-description deficit
divided by the slope. Rearrangement of `KE_le_structFn`. -/
theorem structFn_ge (x α : ℕ) :
    (((KE x - α - (36 + elen extractor + 2 * elen dbl)) / (15 + elen dbl) : ℕ) : ℕ∞)
      ≤ structFn x α := by
  unfold structFn
  by_cases hm : (modelLogCards x α).Nonempty
  · rw [if_pos hm]
    obtain ⟨c, L, hcelen, hceval, _hnodup, hxL, hlcard⟩ := Nat.sInf_mem hm
    have hpm := KE_le_of_model hceval hxL
    have hKE : KE x ≤ α + (15 + elen dbl) * sInf (modelLogCards x α)
        + (36 + elen extractor + 2 * elen dbl) := by
      rw [hlcard]
      calc KE x ≤ elen c + (15 + elen dbl) * Nat.log 2 L.length
              + (36 + elen extractor + 2 * elen dbl) := hpm
        _ ≤ α + (15 + elen dbl) * Nat.log 2 L.length
              + (36 + elen extractor + 2 * elen dbl) := by gcongr
    have hsub : KE x - α - (36 + elen extractor + 2 * elen dbl)
        ≤ (15 + elen dbl) * sInf (modelLogCards x α) := by omega
    have hdiv : (KE x - α - (36 + elen extractor + 2 * elen dbl)) / (15 + elen dbl)
        ≤ sInf (modelLogCards x α) := by
      calc (KE x - α - (36 + elen extractor + 2 * elen dbl)) / (15 + elen dbl)
          ≤ ((15 + elen dbl) * sInf (modelLogCards x α)) / (15 + elen dbl) :=
            Nat.div_le_div_right hsub
        _ = sInf (modelLogCards x α) := Nat.mul_div_cancel_left _ (by omega)
    exact_mod_cast hdiv
  · rw [if_neg hm]; exact le_top

end StructureFunction
