/-
Copyright (c) 2025 The Compfiles Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/

import Mathlib

import ProblemExtraction

problem_file {
  tags := [.NumberTheory]
}

/-!
# International Mathematical Olympiad 1991, Problem 2

Let n > 6 be an integer and a₁, a₂, ..., aₖ be all the
natural numbers less than n and relatively prime to n.
If

  a₂ - a₁ = a₃ - a₂ = ... = aₖ - aₖ₋₁ > 0,

prove that n must either be a prime number of a power
of 2.
-/

namespace Imo1991P2

snip begin

/-!
## Proof strategy (Solution 1, via Bertrand's Postulate)

Let d be the common difference. The sequence a hits exactly
{m | gcd(m,n) = 1 ∧ m < n} in increasing order (since d > 0).
Key facts: a₀ = 1 (smallest coprime to n) and a_{k-1} = n-1.
All AP elements are ≡ 1 (mod d).

- **d = 1:** All of 1, 2, ..., n-1 are coprime to n → n is prime.
- **d = 2:** Odd numbers are exactly the coprimes to n → n is a power of 2.
- **d ≥ 3:** Contradiction. The integers 2, ..., d-1 are not in the AP so none
  are coprime to n, meaning every prime ≤ d-1 divides n. In particular 2 | n.
  By Bertrand, ∃ prime p with n/2 < p < n. Since p prime and p < n, p ∤ n,
  so gcd(p,n) = 1, and p is in the AP: p ≡ 1 (mod d). Also p-1 is not coprime
  to n (since p-1 < p and p-1 ≢ 1 (mod d) for appropriate d), giving a prime
  factor of p-1 that also divides n, ultimately forcing a contradiction.
-/

variable (n : ℕ) (hn : 6 < n)
    (k : ℕ) (a : Fin k → ℕ)
    (ha1 : { a i | i } = { m | Nat.Coprime m n ∧ m < n })
    (d : ℕ) (hd : 0 < d)
    (ha2 : ∀ i : Fin k, (h : i + 1 < k) → a i + d = a ⟨i + 1, h⟩)

/-- k is positive: n > 6 has at least one coprime below n (namely 1). -/
lemma k_pos : 0 < k := by
  by_contra h
  push_neg at h
  have : (1 : ℕ) ∈ { a i | i } := by
    rw [ha1]
    exact ⟨Nat.coprime_one_left n, by omega⟩
  simp [Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (by norm_num) (le_refl k)) h] at this
  sorry

/-- The sequence a is strictly monotone (d > 0). -/
lemma a_strictMono : StrictMono a := by
  sorry

/-- The minimum of the range is 1 (since 1 is always coprime to n). -/
lemma a_zero_eq_one (hk : 0 < k) : a ⟨0, hk⟩ = 1 := by
  sorry

/-- The maximum of the range is n-1 (since gcd(n-1, n) = 1 always). -/
lemma a_last_eq_n_sub_one (hk : 0 < k) : a ⟨k - 1, by omega⟩ = n - 1 := by
  sorry

/-- All AP elements are ≡ 1 (mod d): a i = 1 + i * d. -/
lemma a_formula (hk : 0 < k) (i : Fin k) : a i = 1 + i.val * d := by
  sorry

/-- If d = 1, all integers in [1, n-1] are coprime to n, so n is prime. -/
lemma d_one_imp_prime (hk : 0 < k) (hd1 : d = 1) : n.Prime := by
  sorry

/-- If d = 2, every odd number < n is coprime to n and no even number is,
    so n has no odd prime factors, i.e., n is a power of 2. -/
lemma d_two_imp_pow_two (hk : 0 < k) (hd2 : d = 2) : n.isPowerOfTwo := by
  sorry

/-- If d ≥ 3, we reach a contradiction via Bertrand's postulate. -/
lemma d_ge_three_false (hk : 0 < k) (hd3 : 3 ≤ d) : False := by
  -- All integers 2, ..., d-1 are not coprime to n (not in AP).
  -- So 2 | n (since 2 ≤ d - 1).
  -- By Bertrand, ∃ prime p with n/2 < p < n; then p ∤ n and p ≡ 1 (mod d).
  -- This forces a contradiction with the AP structure.
  sorry

snip end

problem imo1991_p2 (n : ℕ) (hn : 6 < n)
    (k : ℕ) (a : Fin k → ℕ)
    (ha1 : { a i | i } = { m | Nat.Coprime m n ∧ m < n })
    (d : ℕ) (hd : 0 < d)
    (ha2 : ∀ i : Fin k, (h : i + 1 < k) → a i + d = a ⟨i + 1, h⟩) :
    n.Prime ∨ n.isPowerOfTwo := by
  have hk := k_pos n hn k a ha1 d hd ha2
  rcases Nat.lt_or_ge d 2 with h | h
  · -- d = 1
    have hd1 : d = 1 := by omega
    exact Or.inl (d_one_imp_prime n hn k a ha1 d hd ha2 hk hd1)
  · rcases Nat.lt_or_ge d 3 with h2 | h2
    · -- d = 2
      have hd2 : d = 2 := by omega
      exact Or.inr (d_two_imp_pow_two n hn k a ha1 d hd ha2 hk hd2)
    · -- d ≥ 3: contradiction
      exact absurd (d_ge_three_false n hn k a ha1 d hd ha2 hk h2) id

end Imo1991P2
