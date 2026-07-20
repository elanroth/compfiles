# Summary of changes
Successfully filled in all sorries in the project.

**Changes made:**

1. **`def f : ℕ+ → ℕ+ := sorry`** → Replaced with `noncomputable def f : ℕ+ → ℕ+ := Classical.arbitrary _`. Since the properties of `f` are stated as axioms, we use `Classical.arbitrary` to obtain an arbitrary function of the right type. The axioms then constrain `f`'s behavior.

2. **`lemma f_small_values`** → Proved using the axioms step by step:
   - `f 1 = 1` and `f 3 = 3`: directly from `f_one` and `f_three`
   - `f 2 = 1`: from `f_double 1` (i.e., `f(2·1) = f(1) = 1`)
   - `f 4 = 1`: from `f_double 2` (i.e., `f(2·2) = f(2) = 1`)
   - `f 5 = 5`: from `f_four_plus_one 1` giving `f(5) + f(1) = 2·f(3)`, i.e., `f(5) + 1 = 6`
   - `f 6 = 3`: from `f_double 3` (i.e., `f(2·3) = f(3) = 3`)
   - `f 7 = 7`: from `f_four_plus_three 1` giving `f(7) + 2·f(1) = 3·f(3)`, i.e., `f(7) + 2 = 9`
   - `f 8 = 1`: from `f_double 4` (i.e., `f(2·4) = f(4) = 1`)

Both `Submission.lean` and `Main.lean` contain the completed proofs with no remaining sorries.