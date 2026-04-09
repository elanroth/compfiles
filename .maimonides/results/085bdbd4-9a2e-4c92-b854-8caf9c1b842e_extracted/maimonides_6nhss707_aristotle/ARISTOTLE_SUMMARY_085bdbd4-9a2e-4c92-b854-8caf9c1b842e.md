# Summary of changes
## Summary

This project contains the formalization of **IMO 2021 Problem 3**, one of the hardest problems from a recent International Mathematical Olympiad. The problem asks to prove that in an acute triangle ABC with AB > AC and D on the angle bisector of ∠BAC in the interior, three specific lines (BC, EF, and O₁O₂) are concurrent.

### What was accomplished

I fixed the project setup (removed non-existent `ProblemExtraction` import, fixed the Lean toolchain version mismatch from 4.29.0-rc6 to 4.28.0) and proved several components of the theorem:

**Fully proven (sorry-free) helper lemmas:**
1. **`wbtw_inter_eq_left`** — If a point lies on both segment AC and line AB, and A,B,C are not collinear, then the point is A.
2. **`not_collinear_BCD_of_interior`** — A point in the interior of triangle ABC is not collinear with any two vertices.
3. **`imo2021_p3_E_ne_F`** — E ≠ F in the IMO 2021 P3 configuration (proved using the above helpers plus angle arguments).
4. **`imo2021_p3_X_ne_A`** — X ≠ A (from the distance inequality dist(A,C) < dist(A,B)).
5. **`imo2021_p3_X_ne_C`** — X ≠ C (from B ≠ C via affine independence).
6. **`imo2021_p3_O_ne`** — O₁ ≠ O₂ (if O₁ = O₂, then X lies on the circumcircle of ADC and on line AC, forcing X = A or X = C, both impossible).

All proven lemmas depend only on standard axioms (propext, Classical.choice, Quot.sound) — no sorry.

### Remaining sorry

The **concurrency** of lines BC, EF, and O₁O₂ (`imo2021_p3_concurrent`, line 245 of `Submission.lean`) remains unproven. This is the core geometric content of IMO 2021 Problem 3, requiring deep geometric arguments (concyclicity of BFEC, power of a point, and properties of circumcenters). This part would likely require 500+ lines of additional formalization and is considered an open formalization challenge in the Lean community (it was listed as unsolved in the compfiles project).

### File structure
- `Submission.lean` — Main file with all definitions and proofs
- `lakefile.lean` — Build configuration (unchanged)
