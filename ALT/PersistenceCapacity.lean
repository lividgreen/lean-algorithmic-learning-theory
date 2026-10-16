module

public import ALT.Persistence.Core
public import ALT.Persistence.MovingLens
public import ALT.Persistence.Counting
public import ALT.Persistence.Robustness


/-!
# Persistence capacity: moving decoders and the price of a frame ([Decoupling] §3.5)

A finite world is a state space `X` with an update `U : X → X`, and the cell-structured case is the
memory `Mem ι V = ι → V` ([Persistence] §2.1). The Decoupling Lemma
([Decoupling] §3, `ALT.decoupling_iff_persists_all`) says a faithfully-encoded model read off
a FIXED region survives iteration exactly when the update is read-only there; total overwrite
therefore excludes a persistent model ([Decoupling] §3, Corollary 3.2). A *time-dependent* decoder
evades that exclusion — on a cyclic string under rotation every cell is rewritten at every step, yet
a decoder tracking the moving window recovers the same model forever. This file states exactly what
the evasion costs ([Decoupling] §3.5).

A **lens family** `ℓ : ℕ → X → M` is a time-indexed decoder subject to no constraint whatever:
not locality, not simplicity, not computability. That is what makes the capacity theorem an
ABSOLUTE bound rather than a statement about some class of observers.

## The four modules

The development lives in four modules under `ALT/Persistence/`, split along its thematic seams;
this umbrella imports all four, so `import ALT.PersistenceCapacity` provides exactly what a single
file would, and everything below declares its names at `ALT`, a theorem under the predicate it
takes.

* `ALT.Persistence.Core` — ω-limit sets and the recurrent core, lens families and the capacity
  theorems, static versus moving, eventual persistence, the effective law, the static hierarchy.
* `ALT.Persistence.MovingLens` — determination on the core, and the observer's ledger in set and
  in complexity form.
* `ALT.Persistence.Counting` — the budgeted, entropic and uniform capacities, the collapse over
  the symmetric group, the marking floor and its price, the graded ledger, the ledger at any
  frames, the paired frame.
* `ALT.Persistence.Robustness` — world constructions (basins, disjoint unions, products, general
  endofunction worlds, time dilation), settling, the tower, the guest ledgers, the robustness
  margin, the witness world, emergence.

The sections below — the capacity names, the main results, the scope — read across all four
parts.

## The capacity names

The capacity objects transliterate the notation of [Persistence] §5, one letter per qualifier and
always in the order `C`, `b`, `H`, `u`, `e`.

* `C` **capacity** at budget `b` — `Cb` is `C_b` ([Persistence] §5, Definition 5.1): the largest
  model carried by a family whose every frame costs at most `b` bits, counted in labels.
* `H` **entropic** — `CbH` is `C_b^H` ([Persistence] §5, Definition 5.4): the same supremum in the
  honest currency, the carried entropy of the reference frame — its relabelling-class size — rather
  than `Cb`'s plain label count. A reading with many labels but few distinguishable ones is priced
  by what it distinguishes, not by how it is written down.
* `u` **uniform** — `CbHu` is `C_b^{H,u}`: one program of `b` bits computes the whole family,
  instead of each frame being paid for separately. An observer that *owns* its reading rather than
  renting it.
* `e` **general endofunction world** — `CbHe`, `CbHue`: the update is not assumed invertible, so the
  entropy is carried on the recurrent core, the only part of the state space persistence constrains.

`CbH` and `CbHe` are ONE definition rendered at two generalities, and so are `CbHu` and `CbHue` —
not four notions. [Persistence] §2.1 already admits an arbitrary endofunction and its Definition 2.2
already values carried entropy on the recurrent core; over a permutation world, where the world *is*
its own core, the `e`-free forms are those same objects, and that is the setting the counting
theorems of [Persistence] §7 are stated in. `CbHe_perm` and `CbHue_perm` check the agreement.

Longer qualifiers ride on the same stem as words: `CbHeOn` values the reading on a given region,
`CbHev` allows a transient before it settles, and `CbHUpTo` / `CbHuUpTo` truncate both conditions
at a finite horizon.

## Main results

* `core_bijOn` — the update restricts to a bijection on the **recurrent core** `⋂ t, U^[t] '' univ`
  (the states surviving every number of steps).
* `Carries.coreLens_eq` / `Carries.frame_eqOn_core` — **the frames are determined on the core**:
  over ANY endofunction world, `U` restricted to the core is a permutation `corePerm`, and a carried
  family satisfies `ℓ t = ℓ 0 ∘ (corePerm U ^ t)⁻¹` there. Off the core the identity constrains
  nothing. This is what [Persistence] §2, Definition 2.2 appeals to in pricing a whole family by its
  reference frame: on the core all frames share one profile.
* `CbHe` / `CbHue` / `CbHe_le_core_factorial` / `CbHe_perm` / `CbHue_perm` — **the budgeted entropic
  capacities over a general endofunction world** ([Persistence] §2, Definitions 2.1–2.2; §5): the
  carried entropy of a reference frame *on the recurrent core*, per-frame-budgeted and uniformly
  budgeted. Capped by the core's factorial — the §3 ceiling in the entropic currency — and equal to
  `CbH` / `CbHu` when the world is a permutation, which `permCarries_iff_carries` explains: the two
  carrying predicates of this file are one predicate.
* `iterate_mem_core` — **the space bounds its own transient**: after `Nat.card X` steps every state
  is in the recurrent core, since the image chain strictly decreases until it stabilizes.
* `CbHev_eq_CbHeOn` — **eventual capacity from a basin IS exact capacity on its attractor**
  ([Persistence] §10.1 read at §5's budget). An observer allowed to be wrong for a while keeps
  exactly what an observer required to be right from the first step keeps over `ω(B)`, at the same
  price per frame: a transient is a shift of the clock and nothing else. Since `ω(B)` is a
  permutation world (`omegaPerm`), §7 applies to it verbatim.
* `hasMargin_iff` / `repair_tax` / `majority_margin` — the **robustness margin** ([Persistence]
  §10.1 + §2). Settling says the reading is right eventually; it says nothing about a *kick*. The
  margin is the largest number of cells that may be corrupted on the attractor with the settled
  value surviving — an attribute of the sub-system, not of the observer, since the condition never
  mentions the family. It **factors** into basin fatness and local constancy (`hasMargin_iff`), and
  it is **paid for in carried content** (`repair_tax`): distinct settled values are `e`-separated,
  so the `e`-balls around one representative per value pack disjointly into the memory,
  `#values * #Ball e ≤ #Mem`. Majority-vote write-back is the worked witness at margin one
  (`majority_margin`), and it saturates the bound exactly (`repair_tax_tight_majWorld`) — three-copy
  redundancy spends its whole capacity buying one cell of margin.
* `Intertwines.comp` / `UniformBudget.comp` / `tower_no_free_lunch` — **the tower** ([Persistence]
  §10.2 + §2). A sub-system is a world, so it hosts sub-systems. The **intertwining square** is the
  time-indexed substitution property, and dilation needs no second definition — a `τ`-dilated square
  is a square over `U^[τ]`. Squares **compose** and dilations **multiply** (`τ₁ * τ₂`); budgets
  **add**, one fixed builder running both levels' programs and composing their tabulations, the
  dilation charged its bit-length `O (Nat.size τ₂)` rather than its magnitude. A tower whose top law
  is `id` is therefore a carrying family of the *iterated base world* (`tower_carries`), so its
  entropy is capped by that world's uniform capacity at the *summed* budget: **stacking buys
  structure, never generic capacity**. `entropy_comp_le` adds that entropy is antitone up the
  levels — coarsening merges fibres, so each level reads no more than the level below.
* `CbHue_le_CbHe` — **owning beats renting by at most the clock, over an arbitrary endofunction**:
  the general-world form of `CbHu_le_CbH`, at `O (log (n + n !))`. The frames of a carried family
  need not repeat off the core, so the period argument is unavailable as stated; what carries the
  proof is that capacity asks which values are ACHIEVABLE, so the uniform family may be replaced by
  a clamped reindexing of itself (`clamp`) that repeats by construction and shares frame zero.
* `eventual_descent_iff` — **eventual descent**: a decoded model obeys the law `F` eventually along
  every orbit from `B` iff it obeys `F` on `ω(B)`. `eventual_decoupling_iff` is its identity-law
  case, as `decoupling_is_identity_law` is `descent_iff`'s.
* `KE_iterate_le` — **time dilation is nearly free on the rule side**: `K (U^[τ])` is `K (U)` plus
  `O (log τ)`, via one fixed self-composition builder, `τ` entering only through its numeral. A
  family
  reading every `τ` steps is a family over `U^[τ]`, so a slower reading is not a cheaper one.
* `capacity_horizon_le` / `capacity_horizon_ge` — the maximal model persistable for `T` steps has
  exactly `|U^[T] '' univ|` elements ([Decoupling] §3.5, Proposition 3.5, the finite-horizon half).
* `capacity_core` / `capacity_core_ge` / `capacity_core_iff` — letting `T → ∞`, a persistent model
  of size `m` exists iff `m ≤ |core U|` ([Decoupling] §3.5, Proposition 3.5). What obstructs memory
  is not overwriting but irreversibility.
* `static_le_moving` / `rotate_gap` — the static capacity of [Decoupling] §3 (Corollary 3.3) never
  exceeds the moving one, and the gap can be total: rotate-left has static capacity `0` (it rewrites
  every cell) and moving capacity the whole memory. Total overwrite precludes persistent content at
  a fixed ADDRESS, not persistent content.
* `lens_bijOn_core` / `ledger` / `ledger_determines` — the price of the escape. If the family
  carries a MAXIMAL model then every frame is a bijection on the core and `U` restricted to the core
  is `ℓ₁⁻¹ ∘ ℓ₀`: the world's recurrent rule is recoverable from the observer's first two frames.
* `ledger_K` — the same in complexity form: `KE (U ↾ core) ≤ KE ℓ₀ + KE ℓ₁ + O(1)`, the constant
  being the length of a single fixed invert-and-compose program (`icode`) that depends on neither
  the world, the lens, the enumerations, nor the size of the memory. The complexity has not
  vanished; it has been relocated, out of the world and into the decoder.
* `eventual_decoupling_iff` — a model correct only EVENTUALLY (a self-repairing code region) settles
  along every orbit from a `U`-closed basin `B` iff `U` is read-only on `R` over the ω-limit set
  `⋂ t, U^[t] '' B`. [Decoupling] §3, Proposition 3.4 is the case `ω B = B`.
* `staticLens_factors` / `hierarchy` — the static stratum between the two ([Persistence] §4): a
  lens with `ℓ ∘ U = ℓ` is exactly a function constant on the components of the transition graph,
  and read-only cells ≤ components ≤ recurrent core. A conserved quantity is what a moving observer
  can be undercut to, and it is strictly less than a runnable code region.
* `Cb` / `capacity_sandwich` — the **budgeted persistence capacity** ([Persistence] §5): the largest
  model carried by a family whose every frame's core table costs at most `b` bits. Monotone in the
  budget, capped by the core at every budget, and above the static levels past a finite one.
* `collapse` / `Balanced.collapse` / `collapse_generic` — **the price is generically unpayable**
  ([Persistence] §7). Over a permutation world the second frame is forced to be `ℓ₀ ∘ U⁻¹`, a budget
  of `b` bits describes at most `2 ^ (b + 1)` frames, and each frame is hit by exactly one coset of
  the lens's stabilizer — so all but a `2 ^ (b + 1) / N_bal` fraction of worlds admit NO affordable
  moving decoder at all, with `N_bal = n ! / ((n / m) !) ^ m` the balanced-lens count.
* `collapse_union` — the same **uniformly over the reference frame** ([Persistence] §7,
  Corollary 7.4): summing the per-frame count by the Kraft inequality, all but a `2 ^ (-d)` fraction
  of worlds price *every* persistent reading at the entropy it carries. There are no discounts.
* `CbH` / `CbH_collapse` / `CbH_ge_marking'` — **the entropic capacity is pinned at `Θ(b)`**
  ([Persistence] §5, Definition 5.4; §7, Corollary 7.5(i)). The honest currency is not the label
  count but the carried entropy of the reference frame — its relabelling-class size. Generically
  `C_b^H (U) ≤ 2b + d + 2` (the cap, from the Kraft union), while over EVERY permutation world `r`
  marks riding along carry `log₂ (n ! / (n − r)!)` (the floor, exact). An observer keeps, to within
  a factor two, exactly the entropy it pays for.
* `KE_markingLens_le` — **the marks are provably cheap** ([Persistence] §5, Proposition 5.3): an
  explicit program of length `O ((r + 1) · log₂ n)`, uniform over where the marks sit, tabulates
  `r` marks on `n` states. It discharges the floor's price hypothesis.

## Scope

`KE` is the additive Kolmogorov complexity of `CodeLayer.AdditiveComplexity` (program length under a
fixed self-delimiting encoding of `Nat.Partrec.Code`), and the finite objects enter it through an
explicit tabulation (`frameTable`, `worldTable`, `coreTable`, `lensTable`) along a chosen
enumeration of the core and of the model.

The capacity objects `Cb`, `CbH` and `CbHe` are stated in **cardinality form** — they are valued in
the reference frame's relabelling-class size, which is `2 ^ E` for the carried entropy `E`. The
`log₂` is applied paper-side; taking the supremum before the logarithm loses nothing, since `log₂`
is monotone and the families are finite.

**Which results need which world.** The ceiling of §3 (`core`, `Carries`, `capacity_core_iff`) and
the core determination (`Carries.coreLens_eq`) hold over an arbitrary finite state type `X` with an
arbitrary `U : X → X`, which is the generality [Persistence] §2.1 states. The cell structure
`Mem ι V` is taken only where it carries the content: the read-only stratum and the static
hierarchy (`Fix`, `static_le_moving`, `rotate_gap`, `hierarchy`), the eventual-persistence
relaxation (`eventual_decoupling_iff`, `majority_selfRepair`), and the complexity-form ledger. The
counting of §7 (`collapse`, `CbH`) is stated over a permutation world, where the world is its own
recurrent core; `CbHe` / `CbHue` are the same budgeted objects over an arbitrary endofunction, and
`CbHe_perm` / `CbHue_perm` check that the two agree exactly where both apply.

Over a general world, value and price are measured on different sets, deliberately: the carried
entropy is valued on the recurrent core, per [Persistence] §2, Definition 2.2, while the budget
prices the ambient table `lensCode` as everywhere else. The reason is given at `CbHe`. The basin
objects (`CbHev`, `CbHeOn`) keep that split for the same reason, and it is what makes their
reduction budget-free: shifting a clock reuses frames, where restricting them to a sub-world would
have to re-index a table.

Two steps of [Persistence] §7 are deliberately left at paper level: the Stirling asymptotic
`log₂ N_bal = κ · n − ((2 ^ κ − 1) / 2) · log₂ n − O(2 ^ κ)`, which converts the exact count
`card_balancedLenses` into the paper's threshold and is presentation, not content; and the paper's
CONDITIONAL form `K (ℓ₁ | ℓ₀)`, of which the plain-`KE` bounds here are the unconditional
first cut. Neither is used by anything proved here.

Nothing here is assumed rather than proved. The per-frame price of the marking family
([Persistence] §5, Proposition 5.3 — `r` marks on `n` states cost `O (r · log₂ n)` bits to
tabulate) was the development's last named hypothesis; it is now discharged as an explicit code
(`KE_markingLens_le`), so the marking floor holds outright (`CbH_ge_marking'`). The hypothesis form
`CbH_ge_marking` is kept: it is the general statement, taking any price bound whatever.
-/


@[expose] public section
