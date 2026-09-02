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

/-! ## What is actually left

`card_divisors_prime_mul_le` above only settles the case where `n + 1` is
**prime**, which is the easy half. Do not try to finish from it alone, and in
particular do not reach for `d (a * b) ≤ d a * d b`: that gives
`d ((n+1)!) ≤ d (n+1) * d (n!)`, and `d (n+1)` exceeds 2 as soon as `n + 1` is
composite, so the bound is too weak exactly where the problem is hard.

The composite case needs the real argument. The shape to aim at: exhibit an
injection from the divisors of `(n+1)!` into two copies of the divisors of `n!`
— i.e. pair each divisor `D` of `(n+1)!` with a divisor of `n!` such that no
divisor of `n!` is used more than twice. `card_le_card_of_injOn` over
`Nat.divisors ((n+1)!) → Nat.divisors (n!) × Bool` is the Lean shape of
"≤ 2 * d(n!)", and is stated as `key_injection` below so the final step is
bookkeeping.

Note `d` is `noncomputable`, so decidability arguments here need `classical`.
-/

/-- The crux, stated so the main theorem follows by counting. For every divisor
`D` of `(n+1)!` choose a divisor `pair D` of `n!`, in such a way that at most
two distinct `D` share a value. -/
lemma key_injection (n : ℕ) (hn : 0 < n) :
    ∃ pair : ℕ → ℕ,
      (∀ D ∈ Nat.divisors (Nat.factorial (n + 1)), pair D ∈ Nat.divisors (Nat.factorial n)) ∧
      (∀ M, ((Nat.divisors (Nat.factorial (n + 1))).filter (fun D => pair D = M)).card ≤ 2) := by
  sorry

-- The main theorem
theorem ciim2022_p6 (n : ℕ) (hn : 0 < n) :
    d (Nat.factorial (n + 1)) ≤ 2 * d (Nat.factorial n) := by
  -- We use the fact that (n+1)! = (n+1) * n!
  rw [factorial_succ]
  -- With `key_injection`, this is: a finset mapping into another with fibres of
  -- size ≤ 2 has at most twice its cardinality (`Finset.card_le_mul_card_image`).
  sorry

end CIIM2022P6
