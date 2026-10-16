module

public import ALT.GradedConjugation
public import ALT.DecoupledSimulation


/-!
# Grading a decoupled simulation: the hosting-induced assembly map ([Decoupling] §4.5)

`ALT/DecoupledSimulation.lean` builds the *structural* category of decoupled simulations — a hosting
square plus code-locality — and leaves the resource grade to a sibling. This module is that sibling:
it adds the coded reading data a simulation needs in order to move graded morphisms, and derives the
map a capacity-respecting simulation induces on graded exponentials, per frame.

## The coded reading
`CodedReading encH encG ℓ b` equips a reading `ℓ : H → G` with a coded retraction pair
`(c_read, c_sect)` of index length at most a uniform budget `b`: `c_read` reads a host index to the
guest index it names (`bridge`), and `c_sect` sections it back (`retr`). `bridge` is what makes the
pair a coded reading *of `ℓ`*; its consumers are the future cross-frame statements — the per-frame
boundary is named here. (Remark, not a target: for a surjective reading on finite carriers a
set-level section exists and finiteness realizes both codes, the `Realizability.realizes_of_finite`
mechanism.)

## The graded simulation and its induced map
`GradedSimulates` is the structural `Simulates` together with one `CodedReading` per frame, all
sharing a single budget `b` (uniform across frames). It carries data — the codes — so it is a
structure, not a proposition. For a frame `t` and a pair of `GuestCoded` assemblies (assemblies
whose realizers are `encG`-images, so the reading's retraction discharges the pullback's
hypothesis), `inducedMap` transports a graded morphism `[A ⇒ B]_g` to `[A' ⇒ B']_{4·max g b + 9}`,
where `A'`, `B'` are the guest assemblies pulled back along the frame's reading (`gradedPullback`).
The map does not touch the underlying function (`inducedMap_fn`).

## The price is (g, b), not (g, b, τ)
The dilation `τ` prices *time* — it multiplies along a tower of hosting squares ([Persistence]
§10.2) — and does not enter the per-application realizer grade, exactly as the transport law of
`ALT/GradeTransport.lean` finds. So the induced map's grade is `4 · max g b + 9`: the guest grade
`g` and the reading budget `b`, with no `τ`.

## Non-vacuity
`GradedSimulates.id` enriches `Simulates.id` — the identity reading coded by `Code.id`
(`val Code.id = id`), at budget `bitlen Code.id`. The `example` below inhabits `inducedMap` at that
hosting, so the construction is not vacuous.

## Boundaries
Per-frame only: the induced map is stated at a single frame `t`. Cross-frame persistence of the
pulled-back structure — that the frames cohere along the tower — is [Persistence] §10.2 territory,
named here, not claimed. No functoriality: composing simulations compounds the `×4` factor, so no
composite grade law is asserted. Neither `pullbackAsm` nor `inducedMap` is claimed trackable — the
map is a function on carriers, not a morphism of any category. No tightness is claimed for the
constant `4 · max g b + 9`.
-/


@[expose] public section

namespace ALT

open Nat.Partrec (Code)
open Nat.Partrec.Code
open RealizabilityCCC TimeCost

/-! ## The identity code's value map -/

/-- `Code.id = pair left right` is in the `rfind'`-free fragment. -/
theorem rfindFree_id : RfindFree Code.id := ⟨trivial, trivial⟩

/-- The value map of `Code.id` is the identity: reading an index by `Code.id` returns it unchanged.
Obtained from `Code.eval_id` through value-agreement (`eval_eq_val`) on the `rfind'`-free fragment.
-/
theorem val_id (n : ℕ) : val Code.id n = n :=
  Part.some_inj.mp ((eval_eq_val rfindFree_id n).symm.trans (Code.eval_id n))

/-! ## The coded reading -/

/-- **A coded reading of `ℓ` at budget `b`.** A retraction pair of codes `(c_read, c_sect)`, both in
the `rfind'`-free fragment and both of index length at most `b`: `c_read` reads a host index
`encH x` to the guest index `encG (ℓ x)` it names (`bridge`), and `c_sect` sections a guest index
back so that `c_read` recovers it (`retr`). This is the per-frame datum a capacity-respecting
simulation supplies beyond its structural square. -/
structure CodedReading {H G : Type*} (encH : H → ℕ) (encG : G → ℕ) (ℓ : H → G) (b : ℕ) where
  /-- the reading code: a host index to the guest index it names. -/
  c_read : Code
  /-- the section code: a guest index to a host index reading back to it. -/
  c_sect : Code
  /-- the reading code is `rfind'`-free, so it is run at its `val`. -/
  read_rf : RfindFree c_read
  /-- the section code is `rfind'`-free. -/
  sect_rf : RfindFree c_sect
  /-- the reading code fits the budget. -/
  read_bitlen : ALT.bitlen c_read ≤ b
  /-- the section code fits the budget. -/
  sect_bitlen : ALT.bitlen c_sect ≤ b
  /-- `c_read` reads a host index to the guest index the reading names. -/
  bridge : ∀ x, val c_read (encH x) = encG (ℓ x)
  /-- `c_read` recovers any sectioned guest index — the retraction identity on guest indices. -/
  retr : ∀ xG : G, val c_read (val c_sect (encG xG)) = encG xG

/-- **A `GuestCoded` assembly** names its elements only by `encG`-images: every realizer in use is
`encG x` for some guest state `x`. This is exactly the condition under which a reading's guest-side
retraction (`CodedReading.retr`, stated over `encG`-images) discharges the pullback's hypothesis. -/
def GuestCoded {G : Type*} (encG : G → ℕ) (A : Asm) : Prop :=
  ∀ (a : A.carrier) (m : ℕ), A.realizes m a → ∃ x : G, m = encG x

/-- On a `GuestCoded` assembly, the reading's guest-side retraction holds at *every* realizer in
use: each is an `encG`-image, where `retr` applies. This is what feeds `pullbackAsm`'s hypothesis.
-/
theorem guest_retr {G : Type*} {encG : G → ℕ} {A : Asm} (hA : GuestCoded encG A)
    {c_read c_sect : Code} (retr : ∀ xG : G, val c_read (val c_sect (encG xG)) = encG xG) :
    ∀ (a : A.carrier) (m : ℕ), A.realizes m a → val c_read (val c_sect m) = m :=
  fun a m ham => by obtain ⟨x, rfl⟩ := hA a m ham; exact retr x

/-! ## The graded simulation and its induced assembly map -/

/-- **A graded decoupled simulation.** The structural `Simulates` (`ALT/DecoupledSimulation.lean`)
together with one coded reading per frame, all at a single uniform budget `b`. It carries the
reading codes as data, so it is a structure rather than a proposition. -/
structure GradedSimulates {C W C' W' : Type*} (U' : C' × W' → C' × W') (U : C × W → C × W)
    (ℓ : ℕ → C' × W' → C × W) (τ : ℕ) (encH : C' × W' → ℕ) (encG : C × W → ℕ) (b : ℕ) where
  /-- the underlying structural simulation. -/
  sim : ALT.Simulates U' U ℓ τ
  /-- a coded reading of every frame's reading map, at the uniform budget `b`. -/
  readings : ∀ t, CodedReading encH encG (ℓ t) b

/-- **The assembly map a graded simulation induces, per frame ([Decoupling] §4.5).** At frame `t`, a
graded morphism `[A ⇒ B]_g` between `GuestCoded` guest assemblies is carried to a morphism
`[A' ⇒ B']_{4·max g b + 9}`, where `A'`, `B'` are `A`, `B` pulled back along the frame's coded
reading. It is `gradedPullback` along `readings t`; the guest-coded hypotheses on `A`, `B` discharge
the pullback's retraction obligations (`guest_retr`). The realizer overflow of a capacity-respecting
simulation's transport is bounded by the same one-hop max-affine law — the price is `(g, b)`, not
`(g, b, τ)`. -/
noncomputable def GradedSimulates.inducedMap {C W C' W' : Type*} {U' : C' × W' → C' × W'}
    {U : C × W → C × W} {ℓ : ℕ → C' × W' → C × W} {τ : ℕ} {encH : C' × W' → ℕ} {encG : C × W → ℕ}
    {b : ℕ} (S : GradedSimulates U' U ℓ τ encH encG b) (t : ℕ)
    {A B : Asm} {g : ℕ} (hA : GuestCoded encG A) (hB : GuestCoded encG B)
    (f : (ALT.gradedExp g A B).carrier) :
    (ALT.gradedExp (4 * max g b + 9)
        (ALT.pullbackAsm A (S.readings t).c_read (S.readings t).c_sect
            (guest_retr hA (S.readings t).retr))
        (ALT.pullbackAsm B (S.readings t).c_read (S.readings t).c_sect
            (guest_retr hB (S.readings t).retr))).carrier :=
  ALT.gradedPullback (S.readings t).read_rf (S.readings t).sect_rf
    (S.readings t).read_bitlen (S.readings t).sect_bitlen
    (guest_retr hA (S.readings t).retr) (guest_retr hB (S.readings t).retr) f

/-- **The induced map leaves the underlying function untouched.** It re-encodes realizers along the
frame's reading, not elements, so it computes the same map on carriers as its input. -/
theorem GradedSimulates.inducedMap_fn {C W C' W' : Type*} {U' : C' × W' → C' × W'}
    {U : C × W → C × W} {ℓ : ℕ → C' × W' → C × W} {τ : ℕ} {encH : C' × W' → ℕ} {encG : C × W → ℕ}
    {b : ℕ} (S : GradedSimulates U' U ℓ τ encH encG b) (t : ℕ)
    {A B : Asm} {g : ℕ} (hA : GuestCoded encG A) (hB : GuestCoded encG B)
    (f : (ALT.gradedExp g A B).carrier) :
    ALT.fn (S.inducedMap t hA hB f) = ALT.fn f := rfl

/-! ## Non-vacuity: the identity hosting, graded -/

/-- The identity reading, coded by `Code.id` (`val Code.id = id`), at any encoding. This is the
reading that enriches `Simulates.id`. -/
def CodedReading.id {G : Type*} (encG : G → ℕ) :
    CodedReading encG encG _root_.id (ALT.bitlen Code.id) where
  c_read := Code.id
  c_sect := Code.id
  read_rf := rfindFree_id
  sect_rf := rfindFree_id
  read_bitlen := le_refl _
  sect_bitlen := le_refl _
  bridge := fun x => val_id (encG x)
  retr := fun xG => by rw [val_id, val_id]

/-- **The identity hosting is graded.** Every decoupled map simulates itself by the identity reading
(`Simulates.id`); coding that reading by `Code.id` at budget `bitlen Code.id` enriches it to a
`GradedSimulates`. -/
def GradedSimulates.id {C W : Type*} (U : C × W → C × W) (encG : C × W → ℕ) :
    GradedSimulates U U (fun _ => _root_.id) 1 encG encG (ALT.bitlen Code.id) where
  sim := ALT.Simulates.id U
  readings := fun _ => CodedReading.id encG

/-- **Non-vacuity probe.** At the identity hosting the induced map is inhabited and preserves the
underlying function: a guest-coded pair and any graded morphism yield an element of the pulled-back
graded exponential computing the same map. Stating this forces `inducedMap` to elaborate at the
identity, so the construction is not vacuous. -/
theorem inducedMap_id_fn {C W : Type*} (U : C × W → C × W) (encG : C × W → ℕ)
    {A B : Asm} {g : ℕ} (hA : GuestCoded encG A) (hB : GuestCoded encG B)
    (f : (ALT.gradedExp g A B).carrier) :
    ALT.fn ((GradedSimulates.id U encG).inducedMap 0 hA hB f) = ALT.fn f :=
  (GradedSimulates.id U encG).inducedMap_fn 0 hA hB f

/-- A cheap non-degeneracy check: the identity reading's value map is genuinely the identity, not
the constant-zero map. -/
example : val Code.id 1 ≠ 0 := by rw [val_id]; decide

end ALT
