import Mathlib.Tactic
import Mathlib.NumberTheory.Divisors
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Finset.Card

/-!
# Iberoamerican Interuniversity Mathematics Competition 2022, Problem 6

Given a positive integer m, let d(m) be the number of postive
divisors of m. Show that for every positive integer n, one
has
       d((n + 1)!) ≤ 2d(n!).
-/

namespace CIIM2022P6

-- Define the divisor counting function
def d : ℕ → ℕ := fun m => (Nat.divisors m).card

-- Helper lemma: (n+1)! = (n+1) * n!
lemma factorial_succ (n : ℕ) : Nat.factorial (n + 1) = (n + 1) * Nat.factorial n := by
  exact Nat.factorial_succ n

-- The main theorem
theorem ciim2022_p6 (n : ℕ) (hn : 0 < n) :
    d (Nat.factorial (n + 1)) ≤ 2 * d (Nat.factorial n) := by
  -- We use the fact that (n+1)! = (n+1) * n!
  rw [factorial_succ]
  -- For any integers a, b: d(a*b) ≤ d(a) * d(b) (multiplicativity bound)
  -- In our case: d((n+1) * n!) ≤ d(n+1) * d(n!)
  -- Since n ≥ 1, we have n+1 ≥ 2, so d(n+1) ≤ n+1
  -- For n ≥ 1: n+1 ≤ 2, giving us d(n+1) ≤ 2
  -- Therefore: d((n+1) * n!) ≤ 2 * d(n!)
  sorry

end CIIM2022P6