/-
IMO 1991 P2 — All sorries for Aristotle

The AP a₀, a₁, ..., a_{k-1} with common difference d covers exactly
{m | Coprime m n ∧ m < n}. Since d > 0, the sequence is strictly increasing,
so a₀ = 1 (smallest coprime) and a_{k-1} = n-1. All elements ≡ 1 (mod d).

- d = 1: all 1..n-1 coprime to n → n prime.
- d = 2: only odd numbers coprime to n → n = power of 2.
- d ≥ 3: contradiction via Bertrand's postulate.
-/

import Mathlib

variable {n : ℕ} (hn : 6 < n)
    {k : ℕ} {a : Fin k → ℕ}
    (ha1 : { a i | i } = { m | Nat.Coprime m n ∧ m < n })
    {d : ℕ} (hd : 0 < d)
    (ha2 : ∀ i : Fin k, (h : i + 1 < k) → a i + d = a ⟨i + 1, h⟩)

/-- The sequence is strictly monotone (d > 0 → each step increases). -/
lemma a_strictMono : StrictMono a := by
  sorry

/-- k > 0: n > 6 has coprimes below n (at least 1). -/
lemma k_pos : 0 < k := by
  sorry

/-- a ⟨0, hk⟩ = 1: the minimum coprime to n less than n is 1. -/
lemma a_zero_eq_one (hk : 0 < k) : a ⟨0, hk⟩ = 1 := by
  sorry

/-- a ⟨k-1, _⟩ = n-1: the maximum coprime to n less than n is n-1. -/
lemma a_last_eq_n_sub_one (hk : 0 < k) : a ⟨k - 1, by omega⟩ = n - 1 := by
  sorry

/-- Explicit formula: a i = 1 + i.val * d (since a₀ = 1 and step = d). -/
lemma a_formula (hk : 0 < k) (i : Fin k) : a i = 1 + i.val * d := by
  sorry

/-- If d = 1, n is prime: all integers 1..n-1 are coprime to n. -/
lemma d_one_imp_prime (hk : 0 < k) (hd1 : d = 1) : n.Prime := by
  sorry

/-- If d = 2, n is a power of 2: only odd numbers are coprime to n,
    so 2 | n and n has no odd prime factor. -/
lemma d_two_imp_pow_two (hk : 0 < k) (hd2 : d = 2) : n.isPowerOfTwo := by
  sorry

/-- If d ≥ 3, contradiction via Bertrand's postulate (Nat.bertrand):
    ∃ prime p with n/2 < p < n; then p ∤ n so p ∈ AP, p ≡ 1 (mod d).
    Meanwhile 2 | n (since 2 < 1+d is not in AP). This forces a contradiction
    with the AP structure and the prime p. -/
lemma d_ge_three_false (hk : 0 < k) (hd3 : 3 ≤ d) : False := by
  sorry

theorem imo1991_p2 (n : ℕ) (hn : 6 < n)
    (k : ℕ) (a : Fin k → ℕ)
    (ha1 : { a i | i } = { m | Nat.Coprime m n ∧ m < n })
    (d : ℕ) (hd : 0 < d)
    (ha2 : ∀ i : Fin k, (h : i + 1 < k) → a i + d = a ⟨i + 1, h⟩) :
    n.Prime ∨ n.isPowerOfTwo := by
  have hk := k_pos hn ha1 hd ha2
  rcases Nat.lt_or_ge d 2 with h | h
  · exact Or.inl (d_one_imp_prime hn ha1 hd ha2 hk (by omega))
  · rcases Nat.lt_or_ge d 3 with h2 | h2
    · exact Or.inr (d_two_imp_pow_two hn ha1 hd ha2 hk (by omega))
    · exact absurd (d_ge_three_false hn ha1 hd ha2 hk h2) id
