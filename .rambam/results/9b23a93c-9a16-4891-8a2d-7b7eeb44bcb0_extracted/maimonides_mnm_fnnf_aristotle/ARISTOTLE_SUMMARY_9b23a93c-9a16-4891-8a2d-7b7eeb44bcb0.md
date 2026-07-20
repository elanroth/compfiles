# Summary of changes
Successfully filled all sorries in the IMO 1998 Problem 6 formalization.

**Problem:** Find the least possible value of f(1998) where f : ℕ+ → ℕ+ satisfies f(t²·f(s)) = s·f(t)² for all positive integers s, t.

**Answer:** 120

**Key changes:**

1. **Fixed the problem statement:** The original formalization (from `Main.lean`) was incorrect — it claimed that for EVERY f satisfying the equation, f(1998) = 120. This is false since the identity function gives f(1998) = 1998. The corrected statement proves that 120 is the *least* value of f(1998) across all valid functions f.

2. **Removed the `ProblemExtraction` dependency** (which was unavailable) and the `problem`/`determine` macros. Created `Submission.lean` with a self-contained formalization using `import Mathlib`.

3. **Fixed the lean-toolchain** (v4.29.0-rc6 → v4.28.0) to match the Mathlib version.

**Proof structure in `Submission.lean`:**

- **Part 1 (Achievability):** Constructed a witness function that swaps prime factors 2↔3 and 5↔37 in the factorization. Proved it is completely multiplicative, an involution, and satisfies the functional equation with f(1998) = 3·2³·5 = 120.

- **Part 2 (Lower bound):** Proved that for ANY valid f, f(1998) ≥ 120. Key steps:
  - Derived f(f(s)) = s·c² and c·f(tu) = f(t)·f(u) where c = f(1)
  - Showed c | f(t) for all t (via p-adic valuation bootstrapping)
  - Defined g = f/c and proved g is a completely multiplicative involution that permutes primes
  - Showed g(2), g(3), g(37) are distinct primes, so g(2)·g(3)³·g(37) ≥ 120 (combinatorial bound)
  - Concluded f(1998) = c·g(2)·g(3)³·g(37) ≥ 1·120 = 120

The proof compiles cleanly with only standard axioms (propext, Classical.choice, Quot.sound).