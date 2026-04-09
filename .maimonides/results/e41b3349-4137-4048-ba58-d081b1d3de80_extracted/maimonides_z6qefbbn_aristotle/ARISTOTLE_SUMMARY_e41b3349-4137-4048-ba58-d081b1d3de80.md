# Summary of changes
## Summary

This is IMO 2022 Problem 6, one of the hardest problems from that competition. The problem asks to prove that the minimum number of "uphill paths" over all Nordic squares on an n×n grid is exactly `2n² - 2n + 1`.

### What was accomplished

The original file had a single `sorry` for the main theorem `imo2022_p6`. I decomposed the proof into a structured set of helper lemmas and proved almost everything:

**Fully proved lemmas:**
- `Adjacent.symm` — adjacency is symmetric
- `Adjacent.ne` — adjacent cells are distinct
- `min_cell_is_valley` — the minimum-value cell is always a valley
- `exists_valley` — every Nordic square has at least one valley
- `non_valley_has_strictly_smaller_neighbor` — every non-valley cell has a neighbor with strictly smaller value
- `UphillPath.ext'` — uphill paths are determined by their cell lists
- `UphillPath.cells_nodup` — uphill path cells are distinct (no duplicates)
- `uphillPath_fintype` — the type of uphill paths is finite
- `answer_eq` — the answer formula equals `2n(n-1) + 1`
- `exists_path_ending_at` — every cell has an uphill path ending at it (via well-founded backward recursion)
- `extend_path` — an uphill path can be extended by appending an adjacent cell with larger value
- **`lower_bound`** — **for any Nordic square, the number of uphill paths is ≥ `answer n`** (the key lower bound, proven via constructing 1 + 2n(n-1) distinct paths)
- `imo2022_p6` — the main theorem, proven modulo the two sub-lemmas

**Remaining sorry (1 total):**
- `exists_optimal` — existence of a Nordic square achieving exactly `answer n` uphill paths. This is the **construction half** of the problem: one must exhibit an explicit Nordic square for each n where the lower bound is tight. This requires defining a specific cell-value assignment (e.g., BFS from center with axis cells getting small values and off-axis even-distance cells becoming local maxima) and verifying it achieves equality — an extremely complex formalization task that represents the hardest part of this IMO problem.

### File structure
- `Submission.lean` (also copied to `Main.lean`): Contains all definitions, the decomposed proof, and the main theorem. The file compiles successfully with one remaining sorry.