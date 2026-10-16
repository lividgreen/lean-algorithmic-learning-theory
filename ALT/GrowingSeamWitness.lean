module

public import ALT.AccretingExcess
public import ALT.SubstitutionComposite


/-!
# The growing seam, class-level: a fused substitution-fed accreting world at any source

([Growth] §4 Theorem 4.7, §5 Definition 5.1 and Theorem 5.3; [Guests] §7 Theorem 7.5;
[Inevitability] §5 Theorem 5.11 and Proposition 5.12)

`ALT.accUpdate` appends a constant fresh block on every step, so its emergence
skeleton and any observation process it is paired with never interact.
This file fuses the two, PARAMETRICALLY in the fed observation `o : ℕ → Bool`: the appended block
carries `o`'s own next value, read off the habitat's own length rather than a separate counter, so
block `i` of the orbit's habitat decodes to `o i` and the decoded word at stage `t` IS the
observation prefix `o` emits.
`AccretingWitness`'s landed machinery — the square, the erasure margin, the extent, the crossing
package — transports clause by clause with no restatement and **no hypothesis on `o` at all**
([Inevitability] Proposition 5.12(b)): the construction consults `o` only at the two appended-block
sites (`seamUpdate`, `seamLaw`), both a function of the habitat's own length, which the erasure
margin cannot move.
What is new at the class level is `seamUpdate` / `seamLaw` themselves, the trajectory
identification, and a packed realization of the same habitat, folded into one `ALT.Mem`;
the learning route's E1 is now supplied for every `o` satisfying
`EnvelopeProfileNat` ([Growth] Definition 5.1), via
`EnvelopeProfileNat.mixingHoeffding` ([Growth] Theorem 5.3) at that member's own trend
constants, and the window-sufficiency field is carried at a declared budget pair `(η, τ)` rather
than fixed at the degenerate instance.
At `o = subObs`, `subObs_envelopeProfile` supplies the class hypothesis
unconditionally and `growingSeam_overlap_subObs` recovers [Growth] Theorem 4.7 / [Inevitability]
Theorem 5.11 exactly ([Inevitability] Proposition 5.12(c)) — Theorem 5.11 is this file's
`o`-instance and not a separate result.

## Main results

* `seamUpdate` / `seamLaw` — the fused carrier, parametric in `o`: `accUpdate`'s update with the
  constant appended block replaced by `encRec k (o s.1.length)`.
* `advances_seamUpdate` / `stagedSquare_seamRead` / `seamUpdate_eq_of_sum_lt` — the transported
  skeleton clauses, over `ALT.accStage` / `accRead` / `accCode` verbatim, at any `o` and with
  no hypothesis on it.
* `seamOrbit_fst` — **the trajectory identification**: from the seam's own start state, the
  habitat at stage `t` is exactly the healthy codeword list `[encRec k (o 0), …, encRec k (o t)]`
  — the machine-checked sense of "the decoded word is the observation prefix".
* `seam_outgrows_paMinus` — **the assembled emergence package**, `accreting_outgrows_paMinus`'s
  shape at `seamUpdate` / `seamLaw`, at any `o`.
* `SeamHost.Idx` / `SeamHost.Mem` / `SeamHost.codeRegion` / `SeamHost.proj` / `SeamHost.update` —
  **the packed realization**: the seam's own habitat, folded block-by-cell into one
  `ALT.Mem`, built by projecting to `seamUpdate`'s own pair type, stepping it, and
  repacking — the T87–T88 pattern. `SeamHost.proj` itself names no source: it decodes a packed
  memory's cells regardless of what update grew them.
* `SeamHost.proj_update` / `SeamHost.proj_iterate` — the projection commutes with the two
  updates, unconditionally.
* `SeamHost.readObs` / `SeamHost.substrateTraj_eq_obs` — the packed carrier's own observation cell,
  read along its own orbit, reproduces `o` exactly, at every source `o`.
* `SeamHost.substrateTraj_eq_subObs` — the `o = subObs` instance, kept resolving under its
  pre-parametrization name for the row that cites it.
* `SeamHost.witness_substrateL` — **the membership capstone, class-level**: the packed carrier is a
  member of `𝒮_L` at any envelope-profile source, E1 drawn from
  `EnvelopeProfileNat.mixingHoeffding` on its own process, window sufficiency at a declared
  budget pair `(η, τ)`.
* `growingSeam_overlap` — **the overlap bundle, class-level**: the emergence package at
  `seamUpdate` beside the learning membership at the packed realization of the SAME dynamics, tied
  by `SeamHost.proj_iterate` and `seamOrbit_fst`, at any envelope-profile `o`.
* `growingSeam_overlap_subObs` — **the instance**: `growingSeam_overlap` at `o = subObs`,
  recovering [Inevitability] Theorem 5.11 exactly ([Inevitability] Proposition 5.12(c)).
* `SeamHost.GrowsLawfulGuest` / `SeamHost.GrownGuestReachesThreshold` /
  `SeamHost.witness_substrateE` — **the `𝒮_E` membership**: `seam_outgrows_paMinus`'s two conjuncts
  assembled into a `SubstrateE`
  term, at the SAME numerals `SeamHost.witness_substrateL` carries, at any `o` and with no
  hypothesis on it — the emergence side needs no envelope profile at all.

## Scope

The packed realization drops the environment coordinate entirely (`ι_J := Empty`, so `π` is
forced to the identity): `accRead`/`seamLaw` never read it, and Definition 2.3's membership needs
one designated instance, not an arbitrary `π` — a fixed machine cannot realize an arbitrary
environment update. The structural clauses above stay quantified over `π` and `ι_J`, exactly as
`AccretingWitness`'s do. As in `AccretingExcess.lean`: no description-length pricing appears
below, and the reflective reading / budget identification stay at paper level.

`SeamHost.witness_substrateE`'s two emergence fields are `seam_outgrows_paMinus`'s own two
components, verbatim — `SubstrateE`'s `growsLawfulGuest`/`grownGuestReachesThreshold` fields are
CARRIED, uninterpreted `Prop`s, so nothing forces either to be stated about the packed carrier
`SeamHost.update`, and no transport through `SeamHost.proj_update`/`SeamHost.proj_iterate` is
needed. Unlike the finite case (`BlockPairHost.witness_substrateE`), which takes the
crossing clause as a hypothesis fixed once outside any particular host, here it is unconditional:
`seam_outgrows_paMinus` proves it outright, at any `o`. The class term assembled is not itself the
paper's `𝒮_E`-membership reading: [Inevitability] §5 Theorem 5.11's status label is explicit that
the offer still rides *Guests* Theorem 7.5's own two paper-level steps — the witness's
affordability, and the identification of the guest's stage budget with its bit count — which this
theorem retires neither of.
-/


@[expose] public section

namespace ALT


variable {ι_J : Type*}

/-! ## The fused carrier -/

/-- **The fused update**: `ALT.accUpdate`'s shape, with the constant appended block
`encRec k false` replaced by `encRec k (o s.1.length)` — the fed source's next value, read off
the habitat's own length. -/
def seamUpdate (k : ℕ) (o : ℕ → Bool) (π : Mem ι_J Bool → Mem ι_J Bool) :
    List (Mem (Fin (3 ^ k)) Bool) × Mem ι_J Bool →
      List (Mem (Fin (3 ^ k)) Bool) × Mem ι_J Bool :=
  fun s => (s.1.map (healWorld k) ++ [encRec k (o s.1.length)], π s.2)

/-- **The guest's own law**: append the source's next value, read off the decoded word's own
length — autonomous (a fixed function of the word alone) and injective (a conservation guest). -/
def seamLaw (o : ℕ → Bool) : List Bool → List Bool := fun m => m ++ [o m.length]

/-- **The update advances the stage**, `advances_accUpdate`'s proof verbatim: appending lengthens
the habitat by exactly one block. -/
theorem advances_seamUpdate (k : ℕ) (o : ℕ → Bool) (π : Mem ι_J Bool → Mem ι_J Bool) :
    Nonautonomous.PositivelyInvariant (seamUpdate k o π) (accStage k) := by
  intro t s hs
  have hs' : s.1.length = t + 1 := hs
  change (seamUpdate k o π s).1.length = t + 1 + 1
  simp [seamUpdate, hs']

/-! ## Two reproved bridges

`AccretingWitness.lean`'s own `decRec_healWorld_eq` / `healWorld_encRec_eq` are `private` to that
file (Lean privacy is file-scoped); both are two-line consequences of `healWorld`'s public
definition and `decRec_encRec`, so they are reproved here rather than exposed or duplicated by
`open private`. -/

private theorem seam_decRec_healWorld_eq (k : ℕ) (x : Mem (Fin (3 ^ k)) Bool) :
    decRec k (healWorld k x) = decRec k x := by
  change decRec k (encRec k (decRec k x)) = decRec k x
  exact decRec_encRec k (decRec k x)

private theorem seam_healWorld_encRec_eq (k : ℕ) (b : Bool) :
    healWorld k (encRec k b) = encRec k b := by
  change encRec k (decRec k (encRec k b)) = encRec k b
  rw [decRec_encRec]

/-! ## The square, from every state -/

/-- **The staged square, transported.** Both closing identities are `decRec_encRec`'s roundtrip,
exactly as `stagedSquare_accRead`'s proof: healing a block does not move its decode, and the
appended block decodes to the fed source's own next value, at any `o` — the one new step is the
length bridge `(accRead k t s).length = s.1.length`, and the stage hypothesis is not consumed. -/
theorem stagedSquare_seamRead (k : ℕ) (o : ℕ → Bool) (π : Mem ι_J Bool → Mem ι_J Bool) :
    Nonautonomous.Semiconj (seamUpdate k o π) (seamLaw o) (accRead k)
      (accStage k) := by
  intro t s _
  show accRead k (t + 1) (seamUpdate k o π s) = seamLaw o (accRead k t s)
  simp only [accRead, seamUpdate, seamLaw, List.map_append, List.map_map, List.map_singleton,
    decRec_encRec]
  have hlen : (s.1.map (decRec k)).length = s.1.length := List.length_map ..
  rw [hlen]
  congr 1
  exact List.map_congr_left (fun x _ => seam_decRec_healWorld_eq k x)

/-! ## The staged margin, transported -/

/-- The block-by-block healing argument, generalized over a pair of habitats of matching length —
`AccretingWitness.lean`'s own `healWorld_map_eq_of_sum_lt`, reproved: it is `private` there and
content-general (nothing about it is specific to the appended block), so it is reproved verbatim
rather than exposed. -/
private theorem seam_healWorld_map_eq_of_sum_lt {k : ℕ} :
    ∀ (l l' : List (Mem (Fin (3 ^ k)) Bool)) (m : List Bool),
      l = m.map (encRec k) → l'.length = l.length →
      (List.zipWith hammingDist l' l).sum < 2 ^ k →
      l'.map (healWorld k) = l.map (healWorld k) := by
  intro l
  induction l with
  | nil =>
    intro l' m hl hlen _
    have hl' : l' = [] := List.length_eq_zero_iff.mp (by simpa using hlen)
    simp [hl']
  | cons hd tl ih =>
    intro l' m hl hlen hsum
    cases m with
    | nil => simp at hl
    | cons mb mtl =>
      simp only [List.map_cons, List.cons.injEq] at hl
      obtain ⟨hhd, htl⟩ := hl
      cases l' with
      | nil =>
        simp only [List.length_nil, List.length_cons] at hlen
        omega
      | cons hd' tl' =>
        simp only [List.length_cons] at hlen
        have hlen' : tl'.length = tl.length := by omega
        simp only [List.zipWith_cons_cons, List.sum_cons] at hsum
        have hhd_sum : hammingDist hd' hd < 2 ^ k := by omega
        have htl_sum : (List.zipWith hammingDist tl' tl).sum < 2 ^ k := by omega
        have hmapheal : tl'.map (healWorld k) = tl.map (healWorld k) :=
          ih tl' mtl htl hlen' htl_sum
        have hhdheal : healWorld k hd' = healWorld k hd := by
          rw [hhd, healWorld_heals k hd' mb (by rw [hhd] at hhd_sum; exact hhd_sum),
            seam_healWorld_encRec_eq]
        rw [List.map_cons, List.map_cons, hhdheal, hmapheal]

/-- **The staged margin, transported.** `accUpdate_eq_of_sum_lt`'s proof verbatim: the seam update's
appended block is a function of the length alone, so the perturbation hypothesis
`s'.1.length = s.1.length` makes the two appended blocks equal for free, beside the healed-block
equality — at any `o`, since the argument never inspects `o`'s value, only the length it is read
at. -/
theorem seamUpdate_eq_of_sum_lt (k : ℕ) (o : ℕ → Bool) (π : Mem ι_J Bool → Mem ι_J Bool) (t : ℕ)
    {s : List (Mem (Fin (3 ^ k)) Bool) × Mem ι_J Bool} (hs : s ∈ accCode k t)
    {s' : List (Mem (Fin (3 ^ k)) Bool) × Mem ι_J Bool} (hlen : s'.1.length = s.1.length)
    (henv : s'.2 = s.2) (hsum : (List.zipWith hammingDist s'.1 s.1).sum < 2 ^ k) :
    seamUpdate k o π s' = seamUpdate k o π s := by
  obtain ⟨-, m, hm⟩ := hs
  have hmap : s'.1.map (healWorld k) = s.1.map (healWorld k) :=
    seam_healWorld_map_eq_of_sum_lt s.1 s'.1 m hm hlen hsum
  simp only [seamUpdate]
  rw [hmap, henv, hlen]

/-! ## The trajectory identification -/

private theorem ofFn_append_singleton {α : Type*} (n : ℕ) (f : Fin (n + 1) → α) :
    List.ofFn (fun i : Fin n => f i.castSucc) ++ [f (Fin.last n)] = List.ofFn f := by
  rw [List.ofFn_succ', List.concat_eq_append]

/-- **The trajectory identification**: from the seam's own start state, the habitat at stage `t`
is exactly the healthy codeword list `[encRec k (o 0), …, encRec k (o t)]` — block `i` of the
orbit's habitat encodes `o i`, so the decoded word at stage `t` IS the observation prefix
(`accRead`, `stagedSquare_seamRead`'s consequence) — at any `o`. -/
theorem seamOrbit_fst (k : ℕ) (o : ℕ → Bool) (π : Mem ι_J Bool → Mem ι_J Bool) (e₀ : Mem ι_J Bool)
    (t : ℕ) :
    ((seamUpdate k o π)^[t] ([encRec k (o 0)], e₀)).1
      = List.ofFn (fun i : Fin (t + 1) => encRec k (o i)) := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [Function.iterate_succ_apply']
    show (seamUpdate k o π ((seamUpdate k o π)^[t] ([encRec k (o 0)], e₀))).1
      = List.ofFn (fun i : Fin (t + 1 + 1) => encRec k (o i))
    simp only [seamUpdate]
    rw [ih]
    have hlen : (List.ofFn (fun i : Fin (t + 1) => encRec k (o i))).length = t + 1 :=
      List.length_ofFn
    rw [hlen, List.map_ofFn]
    have hcomp : (healWorld k) ∘ (fun i : Fin (t + 1) => encRec k (o i))
        = (fun i : Fin (t + 1) => encRec k (o i)) := by
      funext i
      exact seam_healWorld_encRec_eq k (o i)
    rw [hcomp]
    exact ofFn_append_singleton (t + 1) (fun i : Fin (t + 1 + 1) => encRec k (o i))

/-! ## The assembled emergence package -/

open RealizabilityCCC
open AdditiveComplexity
open FFL.FirstOrder FFL.FirstOrder.Arithmetic

/-- **The seam world's escape witness, packaged**: `accreting_outgrows_paMinus`'s shape at
`seamUpdate` / `seamLaw` — the skeleton clauses transported above, beside the uniform excess's
eventual-hosting crossing. No hypothesis on `o` at all: the crossing is the uniform excess
statement, which mentions no source, and the skeleton clauses above carry none either. -/
theorem seam_outgrows_paMinus (k : ℕ) (o : ℕ → Bool) (π : Mem ι_J Bool → Mem ι_J Bool) :
    (Nonautonomous.PositivelyInvariant (seamUpdate k o π) (accStage k) ∧
      Nonautonomous.Semiconj (seamUpdate k o π) (seamLaw o) (accRead k) (accStage k) ∧
      (∀ t, (Nonautonomous.imageFiber (accRead (ι_J := ι_J) k) (accStage k) t).ncard
        = 2 ^ (t + 1)) ∧
      (∀ t s, s ∈ accCode k t →
        ∀ s' : List (Mem (Fin (3 ^ k)) Bool) × Mem ι_J Bool, s'.1.length = s.1.length →
          s'.2 = s.2 → (List.zipWith hammingDist s'.1 s.1).sum < 2 ^ k →
            seamUpdate k o π s' = seamUpdate k o π s)) ∧
    (∃ gTS, (∃ t₀, ∀ t, t₀ ≤ t → ALT.hostsAt (t + 1) gTS) ∧
      ∀ t Mchk, ALT.hostsAt (t + 1) gTS → gTS < Mchk → Mchk ≤ gTS ^ 2 →
        ∃ R : ReflectiveAsm gTS, R.depth = Mchk ∧
          ALT.FitsIn (recursorAsm R.depth) (t + 1) ∧
          ∃ M, ALT.RepresentsUnderivableTruth (Encodable.encode : Sentence ℒₒᵣ → ℕ)
            (fun δ => (𝗣𝗔⁻ : ArithmeticTheory) ⊢ δ) (fun δ => ℕ↓[ℒₒᵣ] ⊧ δ) M) := by
  obtain ⟨gTS, hInc⟩ := outgrows_paMinus_uniform
  exact ⟨⟨advances_seamUpdate k o π, stagedSquare_seamRead k o π, ncard_guestStage_accRead ι_J k,
      fun t s hs s' hlen henv hsum => seamUpdate_eq_of_sum_lt k o π t hs hlen henv hsum⟩,
    gTS, eventually_hostsAt gTS, fun t => hInc (t + 1)⟩

namespace SeamHost

/-! ## The packed realization -/

/-- The witness's cell index: `8` code cells, one length-counter cell, and the habitat cells
addressed block-by-cell on an ℕ-indexed tail. -/
abbrev Idx (k : ℕ) : Type := Fin 8 ⊕ (Unit ⊕ (ℕ × Fin (3 ^ k)))

/-- The witness's memory: ℕ-valued throughout — the length counter genuinely grows without bound,
so it cannot be compressed into finitely many `Bool` cells. Code and habitat cells carry `0`/`1`.
-/
abbrev Mem (k : ℕ) : Type := ALT.Mem (Idx k) ℕ

/-- The **code region**: `8` read-only cells, present for the code/work split `SubstrateClass`
asks for even though nothing below ever reads them. -/
def codeRegion (k : ℕ) : Set (Idx k) := Set.range (Sum.inl : Fin 8 → Idx k)

/-- **The code region has exactly `8` cells.** -/
private theorem codeRegion_ncard (k : ℕ) : (codeRegion k).ncard = 8 := by
  rw [codeRegion, ← Set.image_univ, Set.ncard_image_of_injective _ Sum.inl_injective,
    Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin]

private theorem decide_toNat_eq_one (b : Bool) : decide (b.toNat = 1) = b := by cases b <;> decide

/-- The `(habitat, environment)` projection of a packed memory — the pair `seamUpdate` itself
acts on, at the trivial (single-point) environment `Mem Empty Bool`. Names no source: it decodes
a packed memory's own cells regardless of what update grew them. -/
def proj (k : ℕ) (s : Mem k) :
    List (ALT.Mem (Fin (3 ^ k)) Bool) × ALT.Mem Empty Bool :=
  (List.ofFn (fun i : Fin (s (Sum.inr (Sum.inl ()))) =>
      fun j : Fin (3 ^ k) => decide (s (Sum.inr (Sum.inr (i.val, j))) = 1)),
    fun x => x.elim)

/-- **One step of the packed carrier's own dynamics**: the habitat and its length counter step by
`seamUpdate k o id`, projected onto the packed memory and repacked; the code cells copy through
untouched. -/
def update (k : ℕ) (o : ℕ → Bool) (s : Mem k) : Mem k :=
  let p := seamUpdate k o (id : ALT.Mem Empty Bool → ALT.Mem Empty Bool) (proj k s)
  fun x => match x with
    | Sum.inl i => s (Sum.inl i)
    | Sum.inr (Sum.inl ()) => p.1.length
    | Sum.inr (Sum.inr (n, j)) => if h : n < p.1.length then ((p.1[n]'h) j).toNat else 0

/-- **(S1) by construction.** -/
private theorem update_fixes (k : ℕ) (o : ℕ → Bool) :
    ALT.Fixes (update k o) (codeRegion k) := by
  rintro s _ ⟨i, rfl⟩
  rfl

/-- **The projection commutes with the two updates, unconditionally**: no code invariant is
needed, since `seamUpdate`'s dynamics reads no code cell at all. -/
theorem proj_update (k : ℕ) (o : ℕ → Bool) (s : Mem k) :
    proj k (update k o s)
      = seamUpdate k o (id : ALT.Mem Empty Bool → ALT.Mem Empty Bool) (proj k s) := by
  set p := seamUpdate k o (id : ALT.Mem Empty Bool → ALT.Mem Empty Bool) (proj k s) with hp
  refine Prod.ext ?_ (Subsingleton.elim _ _)
  change List.ofFn (fun i : Fin p.1.length =>
      fun j : Fin (3 ^ k) => decide (update k o s (Sum.inr (Sum.inr (i.val, j))) = 1))
    = p.1
  have hfun : (fun i : Fin p.1.length => fun j : Fin (3 ^ k) =>
      decide (update k o s (Sum.inr (Sum.inr (i.val, j))) = 1))
      = (fun i : Fin p.1.length => p.1[i.val]) := by
    funext i j
    have h := i.isLt
    change decide ((if h : i.val < p.1.length then ((p.1[i.val]'h) j).toNat else 0) = 1)
      = p.1[i.val] j
    rw [dite_eq_left h]
    exact decide_toNat_eq_one _
  rw [hfun]
  exact List.ofFn_getElem

/-- **Loading the packed carrier's own initial state**: the code cells are all `0` (unread, so
their value carries no meaning); the length counter is `1`; block `0` holds the seam's own start
codeword `encRec k (o 0)`. -/
noncomputable def load (k : ℕ) (o : ℕ → Bool) : Mem k :=
  fun x => match x with
    | Sum.inl _ => 0
    | Sum.inr (Sum.inl ()) => 1
    | Sum.inr (Sum.inr (n, j)) => if n = 0 then (encRec k (o 0) j).toNat else 0

private theorem proj_load (k : ℕ) (o : ℕ → Bool) :
    proj k (load k o) = ([encRec k (o 0)], fun x => x.elim) := by
  refine Prod.ext ?_ (Subsingleton.elim _ _)
  change List.ofFn (fun i : Fin 1 =>
      fun j : Fin (3 ^ k) => decide (load k o (Sum.inr (Sum.inr (i.val, j))) = 1))
    = [encRec k (o 0)]
  simp only [List.ofFn_succ, List.ofFn_zero]
  congr 1
  funext j
  change decide ((if (0 : ℕ) = 0 then (encRec k (o 0) j).toNat else 0) = 1)
    = encRec k (o 0) j
  rw [ite_eq_left rfl]
  exact decide_toNat_eq_one _

/-- **The projection commutes with iteration.** -/
theorem proj_iterate (k : ℕ) (o : ℕ → Bool) (t : ℕ) :
    proj k ((update k o)^[t] (load k o))
      = (seamUpdate k o (id : ALT.Mem Empty Bool → ALT.Mem Empty Bool))^[t]
          (proj k (load k o)) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', proj_update,
      ih]

/-- **The packed carrier's own habitat, at every stage, is the seam's own trajectory**: composing
`proj_iterate` with `proj_load` and the trajectory identification
`seamOrbit_fst`. -/
private theorem proj_iterate_fst (k : ℕ) (o : ℕ → Bool) (t : ℕ) :
    (proj k ((update k o)^[t] (load k o))).1
      = List.ofFn (fun i : Fin (t + 1) => encRec k (o i)) := by
  rw [proj_iterate, proj_load]
  exact seamOrbit_fst k o (id : ALT.Mem Empty Bool → ALT.Mem Empty Bool) (fun x => x.elim) t

private theorem getD_ofFn {α : Type*} {n : ℕ} (f : Fin n → α) (d : α) (t : ℕ) (h : t < n) :
    (List.ofFn f).getD t d = f ⟨t, h⟩ := by
  have hlen : t < (List.ofFn f).length := by rw [List.length_ofFn]; exact h
  rw [List.getD_eq_get (List.ofFn f) d ⟨t, hlen⟩, List.get_ofFn]
  congr 1

/-- **The packed carrier's own observation**: the majority-decode of the habitat's newest block,
read off the carrier's own reconstructed habitat (`proj`). Names no source: it reads
whatever habitat it is given. -/
def readObs (k : ℕ) (s : Mem k) : Bool :=
  decRec k ((proj k s).1.getD (s (Sum.inr (Sum.inl ())) - 1) (encRec k false))

/-- **The packed carrier's own length counter, at every stage of its own orbit.** -/
private theorem update_iterate_counter (k : ℕ) (o : ℕ → Bool) (t : ℕ) :
    ((update k o)^[t] (load k o)) (Sum.inr (Sum.inl ())) = t + 1 := by
  have hb : (proj k ((update k o)^[t] (load k o))).1.length
      = ((update k o)^[t] (load k o)) (Sum.inr (Sum.inl ())) := List.length_ofFn
  rw [proj_iterate_fst, List.length_ofFn] at hb
  exact hb.symm

/-- **The realization theorem.** Reading the packed carrier's own observation off its own orbit,
from its own loaded state, reproduces `o` exactly, at every `t` and at every source `o`. -/
theorem readObs_iterate_load (k : ℕ) (o : ℕ → Bool) (t : ℕ) :
    readObs k ((update k o)^[t] (load k o)) = o t := by
  change decRec k ((proj k ((update k o)^[t] (load k o))).1.getD
      (((update k o)^[t] (load k o)) (Sum.inr (Sum.inl ())) - 1) (encRec k false))
    = o t
  rw [proj_iterate_fst, update_iterate_counter]
  have ht : t + 1 - 1 = t := by omega
  rw [ht, getD_ofFn _ _ t (by omega)]
  exact decRec_encRec k (o t)

/-- The packed carrier's OWN observation process, read along its own orbit from its own loaded
state, at any source `o`. -/
noncomputable def substrateTraj (k : ℕ) (o : ℕ → Bool) : ℕ → Bool :=
  fun t => readObs k ((update k o)^[t] (load k o))

/-- **The packed carrier's own process IS its source `o`**, parametrically. -/
theorem substrateTraj_eq_obs (k : ℕ) (o : ℕ → Bool) : substrateTraj k o = o := by
  funext t
  exact readObs_iterate_load k o t

/-- **The `o = subObs` instance**, kept resolving under its pre-parametrization name: the row
[Growth] GR-12 and [Inevitability] IN-49 cite it directly. -/
theorem substrateTraj_eq_subObs (k : ℕ) : substrateTraj k subObs = subObs :=
  substrateTraj_eq_obs k subObs

/-! ## Realizability, and the membership capstone -/

/-- **Realizability, named on the packed carrier, at any source `o`.** Reading the carrier's own
observation off its own orbit reproduces `o` exactly, at every `t`. -/
def Realizable (k : ℕ) (o : ℕ → Bool) : Prop :=
  ∀ t : ℕ, readObs k ((update k o)^[t] (load k o)) = o t

private theorem realizable (k : ℕ) (o : ℕ → Bool) : Realizable k o :=
  readObs_iterate_load k o

/-- **The membership capstone, class-level.** The packed carrier — the seam's own growing habitat,
folded block-by-cell into one `ALT.Mem`, fed by any source `o` with an envelope profile
([Growth] Definition 5.1) — is a member of `𝒮_L` ([Inevitability] §2 Definition 2.3), with E1 drawn
from its own emitted process: `EnvelopeProfileNat.mixingHoeffding` ([Growth] Theorem 5.3)
rewritten along the realization theorem `substrateTraj_eq_obs`, at that member's own trend
constants `(S, ρ, W)`, and window sufficiency at a declared budget pair `(η, τ)` rather than fixed
at the degenerate instance ([Inevitability] Proposition 5.12(a)).

The three prerequisites and the five learning fields follow
`GrowingHost.witness_substrateL`'s own proof term at the same numerals —
`r = 3`, `K = 8 + 100`, `L = 2K`, `c₀ = 1`, `c₁ = 2`, `c₂ = 3`, `δ = 1/2`, `sCodeSize = 8`
(`codeRegion_ncard`), `g(T_S) = 2` — with `assumptionA` and `benignSeparation` reused
verbatim (both are facts about `Fin 8` alone, not about the memory carrying it). -/
theorem witness_substrateL (k : ℕ) (o : ℕ → Bool)
    {S : ℝ} {ρ W : Fin 8 → ℝ} (h : EnvelopeProfileNat o S ρ W)
    {η τ : ℝ} (hη : 0 ≤ η) (hb : 2 * η ≤ τ) :
    ALT.SubstrateL (update k o) (codeRegion k)
      3 ((8 : ℝ) + 100) (2 * ((8 : ℝ) + 100)) 1 2 3 (1 / 2) 8 2
      True True True True (Realizable k o) (ALT.ChainWindowBudget 8 η τ) := by
  have hlog : Real.log (3 / (1 / 2)) ≤ 3 / (1 / 2) - 1 := Real.log_le_sub_one_of_pos (by norm_num)
  have hcap : ALT.capacity (Nat.clog 2 (2 + 1)) = 4 := by decide
  have he1 : MixingHoeffding
      (MeasureTheory.Measure.dirac (substrateTraj k o))
      (pairEnsemble pairChar 0 8) (ρ 0) ((2 * S + W 0) ^ 2 / (2 * Real.log 2)) := by
    rw [substrateTraj_eq_obs]
    exact EnvelopeProfileNat.mixingHoeffding h 0
  refine
    { s1 := update_fixes k o
      s2 := ⟨by nlinarith, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num,
        by norm_num, by norm_num⟩
      s3 := ⟨by rw [hcap]; norm_num, trivial, trivial, trivial, trivial⟩
      realizability := realizable k o
      windowSufficiency := ALT.chainWindowBudget 8 hη hb
      assumptionA := ?_
      benignSeparation := ⟨1 / 2, 1, by norm_num, by norm_num⟩
      e1 := ⟨Bool, inferInstance, MeasureTheory.Measure.dirac (substrateTraj k o),
        pairEnsemble pairChar 0 8, ρ 0, (2 * S + W 0) ^ 2 / (2 * Real.log 2), he1⟩ }
  refine ⟨Fin 8, Fin 8, fun _ => Finset.univ, fun _ => ALT.singleLiteralAns, 0,
    (8 : ℝ), 0, ?_⟩
  filter_upwards with r'
  have hle := ALT.sqDim_singleLiteral_le (k := 8) (0 : ℝ)
  have hcast : (SQObjects.sqDim (Finset.univ : Finset (Fin 8)) 0
      (ALT.singleLiteralAns (k := 8)) : ℝ) ≤ (8 : ℝ) := by exact_mod_cast hle
  simpa using hcast

end SeamHost

/-! ## The overlap bundle -/

/-- **The overlap bundle, class-level**: the emergence package (`seam_outgrows_paMinus`, [Guests]
Theorem 7.5's clauses at the fused world, no hypothesis on `o`) beside the learning membership
(`SeamHost.witness_substrateL`, at the envelope-profile class), both at the trivial-environment
instance — the identification between the two carriers is machine-checked at the
projection-iterate level (`SeamHost.proj_iterate`, `seamOrbit_fst`: the packed carrier's own
habitat, at every stage, IS the seam's own trajectory), the T87–T88 pattern. No further reflective
reading or budget identification is claimed here — both stay at paper level, exactly as in [Guests]
Theorems 7.5 and 7.7. -/
theorem growingSeam_overlap (k : ℕ) (o : ℕ → Bool)
    {S : ℝ} {ρ W : Fin 8 → ℝ} (h : EnvelopeProfileNat o S ρ W)
    {η τ : ℝ} (hη : 0 ≤ η) (hb : 2 * η ≤ τ) :
    (Nonautonomous.PositivelyInvariant (seamUpdate k o (id : Mem Empty Bool → Mem Empty Bool))
        (accStage k) ∧
      Nonautonomous.Semiconj (seamUpdate k o (id : Mem Empty Bool → Mem Empty Bool))
        (seamLaw o)
        (accRead k) (accStage k) ∧
      (∀ t, (Nonautonomous.imageFiber (accRead (ι_J := Empty) k) (accStage k) t).ncard
        = 2 ^ (t + 1)) ∧
      (∀ t s, s ∈ accCode k t →
        ∀ s' : List (Mem (Fin (3 ^ k)) Bool) × Mem Empty Bool, s'.1.length = s.1.length →
          s'.2 = s.2 → (List.zipWith hammingDist s'.1 s.1).sum < 2 ^ k →
            seamUpdate k o (id : Mem Empty Bool → Mem Empty Bool) s'
              = seamUpdate k o (id : Mem Empty Bool → Mem Empty Bool) s)) ∧
    (∃ gTS, (∃ t₀, ∀ t, t₀ ≤ t → ALT.hostsAt (t + 1) gTS) ∧
      ∀ t Mchk, ALT.hostsAt (t + 1) gTS → gTS < Mchk → Mchk ≤ gTS ^ 2 →
        ∃ R : ReflectiveAsm gTS, R.depth = Mchk ∧
          ALT.FitsIn (recursorAsm R.depth) (t + 1) ∧
          ∃ M, ALT.RepresentsUnderivableTruth (Encodable.encode : Sentence ℒₒᵣ → ℕ)
            (fun δ => (𝗣𝗔⁻ : ArithmeticTheory) ⊢ δ) (fun δ => ℕ↓[ℒₒᵣ] ⊧ δ) M) ∧
    ALT.SubstrateL (SeamHost.update k o) (SeamHost.codeRegion k)
      3 ((8 : ℝ) + 100) (2 * ((8 : ℝ) + 100)) 1 2 3 (1 / 2) 8 2
      True True True True (SeamHost.Realizable k o) (ALT.ChainWindowBudget 8 η τ) :=
  ⟨(seam_outgrows_paMinus (ι_J := Empty) k o id).1, (seam_outgrows_paMinus (ι_J := Empty) k o id).2,
    SeamHost.witness_substrateL k o h hη hb⟩

/-- **The instance**: `growingSeam_overlap` at `o = subObs`, `SubstitutionComposite`'s own envelope
profile, and the degenerate budget pair `(η, τ) = (0, 0)` — [Inevitability] Theorem 5.11 is this
proposition's `o`-instance and not a separate result ([Inevitability] Proposition 5.12(c)). -/
theorem growingSeam_overlap_subObs (k : ℕ) :
    (Nonautonomous.PositivelyInvariant (seamUpdate k subObs (id : Mem Empty Bool → Mem Empty Bool))
        (accStage k) ∧
      Nonautonomous.Semiconj
        (seamUpdate k subObs (id : Mem Empty Bool → Mem Empty Bool))
        (seamLaw subObs) (accRead k) (accStage k) ∧
      (∀ t, (Nonautonomous.imageFiber (accRead (ι_J := Empty) k) (accStage k) t).ncard
        = 2 ^ (t + 1)) ∧
      (∀ t s, s ∈ accCode k t →
        ∀ s' : List (Mem (Fin (3 ^ k)) Bool) × Mem Empty Bool, s'.1.length = s.1.length →
          s'.2 = s.2 → (List.zipWith hammingDist s'.1 s.1).sum < 2 ^ k →
            seamUpdate k subObs (id : Mem Empty Bool → Mem Empty Bool) s'
              = seamUpdate k subObs (id : Mem Empty Bool → Mem Empty Bool) s)) ∧
    (∃ gTS, (∃ t₀, ∀ t, t₀ ≤ t → ALT.hostsAt (t + 1) gTS) ∧
      ∀ t Mchk, ALT.hostsAt (t + 1) gTS → gTS < Mchk → Mchk ≤ gTS ^ 2 →
        ∃ R : ReflectiveAsm gTS, R.depth = Mchk ∧
          ALT.FitsIn (recursorAsm R.depth) (t + 1) ∧
          ∃ M, ALT.RepresentsUnderivableTruth (Encodable.encode : Sentence ℒₒᵣ → ℕ)
            (fun δ => (𝗣𝗔⁻ : ArithmeticTheory) ⊢ δ) (fun δ => ℕ↓[ℒₒᵣ] ⊧ δ) M) ∧
    ALT.SubstrateL (SeamHost.update k subObs) (SeamHost.codeRegion k)
      3 ((8 : ℝ) + 100) (2 * ((8 : ℝ) + 100)) 1 2 3 (1 / 2) 8 2
      True True True True (SeamHost.Realizable k subObs)
      (ALT.ChainWindowBudget 8 0 0) :=
  growingSeam_overlap k subObs subObs_envelopeProfile (le_refl 0)
    (by norm_num)

namespace SeamHost

/-! ## The `𝒮_E` membership -/

/-- **The growth clause, verbatim** ([Inevitability] §5 Theorem 5.11(b)'s first offered clause,
generalized to any source `o`): `seam_outgrows_paMinus`'s own first conjunct at the trivial
environment instance — the advancing square, the staged square, the extent doubling stage by
stage, and the one-step erasure margin. -/
def GrowsLawfulGuest (k : ℕ) (o : ℕ → Bool) : Prop :=
  Nonautonomous.PositivelyInvariant (seamUpdate k o (id : ALT.Mem Empty Bool → ALT.Mem Empty Bool))
    (accStage k) ∧
    Nonautonomous.Semiconj (seamUpdate k o (id : ALT.Mem Empty Bool → ALT.Mem Empty Bool))
      (seamLaw o) (accRead k) (accStage k) ∧
    (∀ t, (Nonautonomous.imageFiber (accRead (ι_J := Empty) k) (accStage k) t).ncard
      = 2 ^ (t + 1)) ∧
    (∀ t s, s ∈ accCode k t →
      ∀ s' : List (ALT.Mem (Fin (3 ^ k)) Bool) × ALT.Mem Empty Bool, s'.1.length = s.1.length →
        s'.2 = s.2 → (List.zipWith hammingDist s'.1 s.1).sum < 2 ^ k →
          seamUpdate k o (id : ALT.Mem Empty Bool → ALT.Mem Empty Bool) s'
            = seamUpdate k o (id : ALT.Mem Empty Bool → ALT.Mem Empty Bool) s)

/-- **The crossing clause, verbatim** ([Inevitability] §5 Theorem 5.11(b)'s second offered clause):
`seam_outgrows_paMinus`'s own second conjunct — a Gödel size that every sufficiently advanced stage
hosts, once past an explicit point. It carries no `k` and no source at all, matching
`seam_outgrows_paMinus`'s own statement: the uniform excess
`ALT.outgrows_paMinus_uniform` this conjunct comes from is already independent of
the guest world it is read at. -/
def GrownGuestReachesThreshold : Prop :=
  ∃ gTS, (∃ t₀, ∀ t, t₀ ≤ t → ALT.hostsAt (t + 1) gTS) ∧
    ∀ t Mchk, ALT.hostsAt (t + 1) gTS → gTS < Mchk → Mchk ≤ gTS ^ 2 →
      ∃ R : ReflectiveAsm gTS, R.depth = Mchk ∧
        ALT.FitsIn (recursorAsm R.depth) (t + 1) ∧
        ∃ M, ALT.RepresentsUnderivableTruth (Encodable.encode : Sentence ℒₒᵣ → ℕ)
          (fun δ => (𝗣𝗔⁻ : ArithmeticTheory) ⊢ δ) (fun δ => ℕ↓[ℒₒᵣ] ⊧ δ) M

/-- **The `𝒮_E` membership, class-level** ([Inevitability] §5 Theorem 5.11(b), generalized to any
source `o`): the packed carrier is a member of `𝒮_E`, at the SAME `(S1)`/`(S2)`/`(S3)` numerals
`witness_substrateL` carries for `𝒮_L`. Both emergence fields are `seam_outgrows_paMinus`'s
two components, discharged with no hypothesis on `o` at all — unlike the finite case,
`BlockPairHost.witness_substrateE`, whose crossing field is a hypothesis `hE` fixed once
outside any particular host. -/
theorem witness_substrateE (k : ℕ) (o : ℕ → Bool) :
    ALT.SubstrateE (update k o) (codeRegion k)
      3 ((8 : ℝ) + 100) (2 * ((8 : ℝ) + 100)) 1 2 3 (1 / 2) 8 2
      True True True True (GrowsLawfulGuest k o) GrownGuestReachesThreshold := by
  have hlog : Real.log (3 / (1 / 2)) ≤ 3 / (1 / 2) - 1 := Real.log_le_sub_one_of_pos (by norm_num)
  have hcap : ALT.capacity (Nat.clog 2 (2 + 1)) = 4 := by decide
  refine
    { s1 := update_fixes k o
      s2 := ⟨by nlinarith, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num,
        by norm_num, by norm_num⟩
      s3 := ⟨by rw [hcap]; norm_num, trivial, trivial, trivial, trivial⟩
      growsLawfulGuest := (seam_outgrows_paMinus (ι_J := Empty) k o id).1
      grownGuestReachesThreshold := (seam_outgrows_paMinus (ι_J := Empty) k o id).2 }

end SeamHost

end ALT

/-! ## Axiom audit

Every capstone above is `#print axioms`-clean on the standard triple, and the guards below make
that build-enforced. -/


/-- info: 'ALT.seamOrbit_fst' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.seamOrbit_fst

/-- info: 'ALT.seam_outgrows_paMinus' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.seam_outgrows_paMinus

set_option linter.style.longLine false in
/-- info: 'ALT.SeamHost.witness_substrateL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.SeamHost.witness_substrateL

/-- info: 'ALT.growingSeam_overlap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.growingSeam_overlap

set_option linter.style.longLine false in
/-- info: 'ALT.growingSeam_overlap_subObs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.growingSeam_overlap_subObs

set_option linter.style.longLine false in
/-- info: 'ALT.SeamHost.witness_substrateE' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ALT.SeamHost.witness_substrateE
