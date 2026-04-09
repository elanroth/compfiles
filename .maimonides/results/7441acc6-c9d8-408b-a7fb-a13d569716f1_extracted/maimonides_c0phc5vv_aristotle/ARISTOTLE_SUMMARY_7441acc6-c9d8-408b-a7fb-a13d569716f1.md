# Summary of changes
Successfully filled in all sorry's in `Submission.lean` (originally `Main.lean`, renamed to match the lakefile's default target).

The file proves **IMO 1970 Problem 6**: Among 100 points in general position (no three collinear) in the plane, at most 70% of all triangles formed by these points can be acute-angled.

## Proof structure

The proof is decomposed into several layers of helper lemmas:

1. **`four_point_algebraic`** (already provided): An algebraic impossibility result showing that 12 specific positivity conditions on real coordinates cannot all hold simultaneously.

2. **`ratio_le_of_mul_le`**: If `10 * a ≤ 7 * b` then `(a : ℚ) / b ≤ 7 / 10`.

3. **`P_injective`**: The point function `P` must be injective (from the no-three-collinear hypothesis).

4. **`angle_lt_pi_div_two_iff_inner_pos`**: An angle `∠ A B C < π/2` iff the inner product `⟨A - B, C - B⟩ > 0` (for distinct points).

5. **`four_points_not_all_acute`**: Among any 4 points with no 3 collinear, not all 4 triangles can be acute (connects the geometric angle definition to the algebraic impossibility via coordinate computation).

6. **`four_point_angle_bound`**: The previous lemma reformulated in terms of the `IsAcuteTriple` predicate on index tuples.

7. **`isAcuteTriple_perm_swap12/23`**: The acute triple predicate is invariant under permutations of the three indices.

8. **`five_point_bound`**: Among any 5 points in general position, at most 42 of the 60 ordered triples give acute triangles (equivalently, at most 7 of 10 unordered triangles are acute). Uses double counting over 4-element subsets and `native_decide` for a combinatorial bound.

9. **`card_triangles_eq_card_triples` / `card_acute_eq_card_acute_triples`**: Bijections between the `Nat.card` of `Affine.Triangle` subtypes and `Nat.card` of ordered triple subtypes.

10. **`ordered_triples_mul_bound`**: The main combinatorial inequality `10 * #acute ≤ 7 * #all` via double counting over 5-element subsets.

11. **`acute_card_mul_le`**: Combines the bijections and the combinatorial bound.

12. **`imo1970_p6`**: The main theorem, following directly from `ratio_le_of_mul_le` and `acute_card_mul_le`.

The proof uses only standard axioms (`propext`, `Classical.choice`, `Lean.ofReduceBool`, `Lean.trustCompiler`, `Quot.sound`).