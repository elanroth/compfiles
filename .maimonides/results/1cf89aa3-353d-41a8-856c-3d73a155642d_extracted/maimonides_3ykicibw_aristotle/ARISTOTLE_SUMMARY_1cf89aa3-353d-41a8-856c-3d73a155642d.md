# Summary of changes
I worked on filling the sorry in `Submission.lean` (originally `Main.lean`), which formalizes IMO 1970 Problem 6: among 100 points in general position in the plane, at most 70% of the triangles formed are acute.

**What was accomplished:**

The original file had two sorries:
1. `four_point_algebraic` — already proved in the original file
2. `imo1970_p6` — the main theorem, which was sorry'd

I restructured the proof by decomposing the main theorem into helper lemmas and proved several of them:

- **`angle_lt_pi_div_two_iff_inner_pos`** (proved): Connects the geometric angle condition (∠ p₁ p₂ p₃ < π/2) to the algebraic inner product condition (⟪p₁ - p₂, p₃ - p₂⟫ > 0).

- **`triangles_set_finite`** (proved): The set of all triangles with vertices among the 100 points is finite, using injectivity of the simplex-points map and finiteness of the range.

- **`acute_triangles_set_finite`** (proved): The set of acute triangles is finite (subset of the above).

- **`P_injective`** (proved): The point map P : Fin 100 → Pt is injective, since if P(a) = P(b) for a ≠ b, then {P(a), P(b), P(c)} would be collinear for any c, contradicting the hypothesis.

- **`affineIndependent_of_distinct`** (proved): For any three distinct indices, the corresponding points are affinely independent (equivalently, not collinear).

- **`imo1970_p6`** (proved modulo `main_bound`): The main theorem is reduced to a natural number inequality `10 * cardAcute ≤ 7 * cardAll`, with a clean case split on whether `cardAll = 0`.

**What remains:**

One sorry remains in `main_bound`, which states `10 * Nat.card(acute triangles) ≤ 7 * Nat.card(all triangles)`. This is the deep geometric/combinatorial core of IMO 1970 P6. The file contains a detailed proof outline in comments explaining the three-step argument:

1. **4-point algebraic** (proved): Among 4 points in general position, not all 4 triangles can be acute.
2. **5-point lemma** (follows from step 1 by double counting): Among 5 points, at most 7 of 10 triangles are acute (since each triangle belongs to 2 four-point subsets, and 2A ≤ 3×5 = 15 gives A ≤ 7).
3. **100-point bound** (follows from step 2 by double counting): Each triangle is in C(97,2) five-point subsets, giving C(97,2)×A ≤ 7×C(100,5), which simplifies to 10A ≤ 7T.

Formalizing this chain requires: (a) translating `four_point_algebraic` from coordinates to abstract points via similarity transformations, (b) the double counting infrastructure connecting `Nat.card` to combinatorial counting over index tuples, and (c) the bijection between ordered triples and `Affine.Triangle` objects. This is an extremely complex formalization effort that could not be completed in this session.

**Other changes:**
- Renamed `Main.lean` → `Submission.lean` to match the lakefile's default target
- Fixed `lean-toolchain` from v4.29.0-rc6 to v4.28.0 to match the Mathlib version