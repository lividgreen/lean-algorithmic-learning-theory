/-
Copyright (c) 2026 Mykola Palamarchuk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mykola Palamarchuk
-/
import Mathlib

-- Scratch smoke-test file (not Mathlib-destined), so we opt out of Mathlib's
-- house-style header linter that requires a copyright block.
set_option linter.style.header false

/- Smoke test: confirms Mathlib imports and elaborates against the fetched cache. -/
#check (1 : ℕ) + 1

example : 2 + 2 = 4 := by norm_num
