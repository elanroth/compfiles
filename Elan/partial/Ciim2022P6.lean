import Mathlib

/-!
# Iberoamerican Interuniversity Mathematics Competition 2022, Problem 6

Given a positive integer m, let d(m) be the number of postive
divisors of m. Show that for every positive integer n, one
has
       d((n + 1)!) ≤ 2d(n!).
-/

namespace CIIM2022P6

-- Define the divisor counting function
noncomputable def d : ℕ → ℕ := fun m => (Nat.divisors m).card

-- Helper lemma: (n+1)! = (n+1) * n!
lemma factorial_succ (n : ℕ) : Nat.factorial (n + 1) = (n + 1) * Nat.factorial n := by
  exact Nat.factorial_succ n

-- Key lemma: d(p * M) ≤ 2 * d(M) for any prime p and M > 0.
-- This is because every divisor of p*M either divides M (if coprime to p)
-- or is p times a divisor of M (if divisible by p).
-- This handles the case when n+1 is prime.
lemma card_divisors_prime_mul_le (p M : ℕ) (hp : Nat.Prime p) (hM : 0 < M) :
    (Nat.divisors (p * M)).card ≤ 2 * (Nat.divisors M).card := by
  have h_divisors : Nat.divisors (p * M) = Nat.divisors M ∪ Finset.image (fun d => p * d) (Nat.divisors M) := by
    rw [ Nat.divisors_mul, Finset.union_comm ];
    rw [ hp.divisors, Finset.ext_iff ] ; intro a ; simp +decide [ Finset.mem_mul ] ; aesop;
  grind +ring

-- The main theorem
theorem ciim2022_p6 (n : ℕ) (hn : 0 < n) :
    d (Nat.factorial (n + 1)) ≤ 2 * d (Nat.factorial n) := by
  -- We use the fact that (n+1)! = (n+1) * n!
  rw [factorial_succ]
  sorry

end CIIM2022P6
