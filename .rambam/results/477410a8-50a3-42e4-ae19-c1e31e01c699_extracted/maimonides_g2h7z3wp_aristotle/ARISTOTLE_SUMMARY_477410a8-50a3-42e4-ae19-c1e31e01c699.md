# Summary of changes
## Summary

This project formalizes IMO 2010 Problem 3: determining all functions g : ℤ>0 → ℤ>0 such that (g(m) + n)(g(n) + m) is always a perfect square.

The solution set is `{ f | f = id ∨ ∃ c, ∀ x, f x = x + c }` (identity or translation by a positive integer constant).

### What was completed

**Forward direction (fully proved):**
- `forward_id`: The identity function satisfies the condition — `(m+n)(n+m) = (m+n)²`.
- `forward_shift`: Translation g(n) = n + c satisfies it — `(m+c+n)(n+c+m) = (m+n+c)²`.

**Key infrastructure lemmas (fully proved):**
- `sq_prod_finite`: For any nonzero integer d, there are only finitely many positive integers T such that T(T+d) is a perfect square. This uses the factorization identity (2T+d)² - (2k)² = d².
- `h_const_of_inf_often`: If h(n) = g(n) - n equals some constant c for infinitely many n, then h(n) = c for ALL n. This uses `sq_prod_finite` — if h(m) ≠ c for some m, the infinitely many n with h(n) = c would give infinitely many T values satisfying T(T+|h(m)-c|) = perfect square, contradicting finiteness.

**Main theorem** `imo2010_p3`: States the biconditional, with the forward direction fully proved.

### Remaining sorry

The **backward direction** (`backward`) has one sorry. This is the hard direction of IMO 2010 P3: showing that the perfect square condition forces g to be either the identity or a translation. The proof strategy is clear (show h(n) = g(n) - n is constant), and the key lemmas are in place, but the final step — proving that some value of h must be taken infinitely often — requires a subtle argument about the interaction between multiple conditions P(m₁, n), P(m₂, n) for different reference points. This is the core difficulty of the IMO problem and resisted formalization within the available time.

### File structure
- `Submission.lean` — Main formalization with all definitions, lemmas, and the theorem
- `ProblemExtraction.lean` — Stub for the competition math extraction macros
- `Main.lean` — Imports Submission