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
module

public import ALT.BirkhoffTool

set_option linter.style.header false
set_option linter.style.longLine false

/-! ## Vendored pointwise Birkhoff ergodic theorem (`ALT/Birkhoff/PointwiseBirkhoff.lean`) -/


@[expose] public section

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

/-- info: 'BirkhoffTool.mixing_oracle_tail_to' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms BirkhoffTool.mixing_oracle_tail_to

/-- info: 'BirkhoffTool.mixing_oracle_tail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms BirkhoffTool.mixing_oracle_tail

/-- info: 'BirkhoffTool.mixingHoeffding_of_iid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms BirkhoffTool.mixingHoeffding_of_iid

/-- info: 'BirkhoffTool.mixingHoeffding_of_nonpos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms BirkhoffTool.mixingHoeffding_of_nonpos

/-- info: 'BirkhoffTool.not_mixingHoeffding_pinned' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms BirkhoffTool.not_mixingHoeffding_pinned

/-- info: 'BirkhoffTool.mixing_oracle_truth_survives_noisy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms BirkhoffTool.mixing_oracle_truth_survives_noisy

/-! ## Finite-horizon `MixingHoeffdingTo` (`ALT/BirkhoffTool.lean`) -/

/-- info: 'BirkhoffTool.mixingHoeffdingTo_of_mixingHoeffding' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms BirkhoffTool.mixingHoeffdingTo_of_mixingHoeffding

/-- info: 'BirkhoffTool.mixingHoeffding_iff_forall_mixingHoeffdingTo' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms BirkhoffTool.mixingHoeffding_iff_forall_mixingHoeffdingTo

/-- info: 'BirkhoffTool.mixingHoeffdingTo_of_le_floor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms BirkhoffTool.mixingHoeffdingTo_of_le_floor

/-- info: 'BirkhoffTool.not_mixingHoeffdingTo_pinned' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms BirkhoffTool.not_mixingHoeffdingTo_pinned

/-- info: 'BirkhoffTool.mixingHoeffdingTo_mono_const' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms BirkhoffTool.mixingHoeffdingTo_mono_const

/-- info: 'BirkhoffTool.mixing_oracle_sample_complexity_to' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms BirkhoffTool.mixing_oracle_sample_complexity_to

/-- info: 'BirkhoffTool.mixing_oracle_truth_survives_noisy_to' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms BirkhoffTool.mixing_oracle_truth_survives_noisy_to

/-! ## Finite-horizon SQ oracle over a schedule (`ALT/BirkhoffTool.lean`) -/

/-- info: 'BirkhoffTool.empirical_isSQOracle_of_mixingTo' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms BirkhoffTool.empirical_isSQOracle_of_mixingTo
