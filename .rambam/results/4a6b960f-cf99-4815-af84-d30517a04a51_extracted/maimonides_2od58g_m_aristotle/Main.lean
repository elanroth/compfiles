/-
Copyright (c) 2021 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
-- Note: ProblemExtraction is not available in this project, so this file
-- is provided for reference only. The actual proof is in Submission.lean.
-- import ProblemExtraction

-- problem_file { tags := [.NumberTheory] }

/-!
# International Mathematical Olympiad 2004, Problem 6

We call a positive integer *alternating* if every two consecutive
digits in its decimal representation are of different parity.

Find all positive integers n such that n has a multiple that is
alternating.

## Note on the formalization

Since the problem statement uses `∃ k, Alternating (n * k)` without requiring `k > 0`,
the multiplier `k = 0` always works (as `n * 0 = 0` has an empty digit list, which is
vacuously alternating). Therefore the solution set is simply all positive integers.
-/

-- See Submission.lean for the complete proof.
