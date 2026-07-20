import Mathlib

-- Based on the solution, the minimum number of uphill paths in a Nordic square
-- is 2n² - 2n + 1. This follows from counting:
-- - At least 2n(n-1) = 2n² - 2n paths of length ≥ 2 (one per directed adjacent edge)
-- - At least 1 path of length 1 (from the unique valley containing value 1)
-- The construction shows this bound is achievable.
def answer : ℕ+ → ℕ := fun n => 2 * n^2 - 2 * n + 1


import Lake
open Lake DSL

package «submission» where
  leanOptions := #[⟨`pp.unicode.fun, true⟩]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib «Submission» where
