# Summary of changes
Successfully filled in all sorries in `Main.lean`, completing the formal proof of IMO 1970 Problem 6.

**Problem**: Given 100 points in the plane, no three collinear, prove that among all triangles formed by these points, at most 70% are acute.

**Proof structure** (all lemmas proved, zero sorries remaining):

1. **`four_point_algebraic`** (pre-existing): An algebraic contradiction showing 12 specific polynomial conditions in 4 variables cannot all hold simultaneously.

2. **`inner_fin2`**: The inner product in `EuclideanSpace ℝ (Fin 2)` equals `v 0 * w 0 + v 1 * w 1`.

3. **`P_injective`**: The point map P is injective (from the general position hypothesis).

4. **`four_point_algebraic_general`**: Generalization of `four_point_algebraic` to 6 variables (arbitrary coordinates for 4 points with one at the origin), proved by introducing normalized coordinates and reducing to the 4-variable version.

5. **`not_all_four_acute`**: For any 4 points in ℝ², it's impossible for all 4 triangles to be simultaneously acute. Converts angle conditions to inner product conditions, then to coordinates, and applies `four_point_algebraic_general`.

6. **`acuteTriangle_iff_isAcuteTriple`**, **`isAcuteTriple_perm`**, **`isAcuteTriple_cycle`**: The acute triangle property is equivalent to `IsAcuteTriple` and is invariant under permutations of the vertices.

7. **`four_point_at_most_three_acute`**: Among any 4 points in general position, at most 3 of 4 triangles are acute (direct application of `not_all_four_acute`).

8. **`five_unordered_bound`**: Among any 5 points in general position, at most 7 of the 10 unordered triples form acute triangles. Proved by double counting over 4-element subsets: each 4-subset has ≤3 acute triples, each triple appears in exactly 2 four-subsets, so 2×acute ≤ 5×3 = 15, giving acute ≤ 7.

9. **`natCard_all_eq_ordTriples`** and **`natCard_acute_eq_ordTriples`**: Bijections between the `Nat.card` subtypes and `Finset` cardinalities of ordered triples.

10. **`counting_bound`**: `10 * |acuteOrdTriples| ≤ 7 * |allOrdTriples|`, proved via double counting over 5-element subsets using `five_unordered_bound`.

11. **`nat_div_le_of_mul_le`**: Simple ℚ arithmetic converting the Nat multiplication inequality to a division bound.

12. **`imo1970_p6`** (main theorem): Combines the bijection lemmas, counting bound, and arithmetic to conclude `cardAcute / cardAll ≤ 7/10`.

Note: The project has a Lean toolchain version mismatch (v4.29.0-rc6) that causes `lake build` to fail on dependencies (Batteries, Qq), but the file itself type-checks correctly via the LSP server.