# Summary of changes
## Summary

This problem is IMO 2022 Problem 3, one of the hardest competition problems in recent years. I made significant progress but was unable to completely eliminate all `sorry`s.

### Issues with the original statement

The original statement in `Main.lean` had two problems:
1. It imported `ProblemExtraction`, which is not available in the project.
2. The theorem is false for `S = ∅` because the conclusion requires `∃ i : Fin 0, ...`, which is impossible when `S` is empty.

### Work done in `Submission.lean`

I created `Submission.lean` (the default build target) with a corrected version of the statement, adding `(hne : 0 < #S)` as a hypothesis to handle the empty set edge case.

**Fully proved lemmas:**
- `case_one`: Any two equivalences from `Fin 1` to a singleton agree (trivial for 1-element sets).
- `case_two`: Any two equivalences from `Fin 2` to a 2-element set differ by rotation or reflection.
- `cycle_auto`: Automorphisms of the cycle graph on `Fin n` (n ≥ 3) that preserve adjacency are rotations or reflections. This is a non-trivial combinatorial result proved by induction.

**Main theorem structure:**
The main theorem `imo2022_p3` is fully proved modulo one helper lemma:
- For `#S = 1`: uses `case_one`
- For `#S = 2`: uses `case_two`  
- For `#S ≥ 3`: uses `cycle_auto` + `arrangement_preserves_adjacency`

**Remaining sorry (1 total):**
- `arrangement_preserves_adjacency` (line 119): This is the deep number-theoretic core of IMO 2022 P3. It states that the permutation σ = p₂ ∘ p₁⁻¹ maps consecutive elements to consecutive elements in the cycle graph. This encodes the fact that any two valid circular arrangements of odd primes (where consecutive products are of the form x² + x + k) must have the same edge set. This requires sophisticated arguments about quadratic residues modulo primes and global constraints from the cycle structure, which proved too complex for automated theorem proving.