/-
Copyright (c) 2026 Mykola Palamarchuk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mykola Palamarchuk
-/
/-
# Axiom audit for the pointwise Birkhoff integration

CI guard: every `#guard_msgs in #print axioms …` below **fails `lake build`** if the theorem's
axiom set ever drifts from the standard `[propext, Classical.choice, Quot.sound]` triple.  This
pins down that the vendored pointwise ergodic theorem and the trajectory-space Tool (i) / oracle
corollaries carry NO `sorryAx` and NO custom axiom — the vendored dependency's footprint is clean.
-/
import ALT.BirkhoffTool

set_option linter.style.header false
set_option linter.style.longLine false

/-! ## Vendored pointwise Birkhoff ergodic theorem (`ALT/Birkhoff/PointwiseBirkhoff.lean`) -/

/-- info: 'birkhoffErgodicTheorem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms birkhoffErgodicTheorem

/-- info: 'birkhoffErgodicTheorem'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms birkhoffErgodicTheorem'

/-! ## Trajectory-space Tool (i) and the FJS-shaped oracle corollaries (`ALT/BirkhoffTool.lean`) -/

/-- info: 'BirkhoffTool.timeAverage_tendsto_expectation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms BirkhoffTool.timeAverage_tendsto_expectation

/-- info: 'BirkhoffTool.mixing_oracle_sample_complexity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms BirkhoffTool.mixing_oracle_sample_complexity

/-- info: 'BirkhoffTool.mixing_oracle_tail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms BirkhoffTool.mixing_oracle_tail
