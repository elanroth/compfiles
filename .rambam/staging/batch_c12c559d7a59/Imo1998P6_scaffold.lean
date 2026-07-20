import Mathlib

namespace Imo1998P6

/-!
# IMO 1998 Problem 6

Find the least possible value of f(1998) where f : ℕ+ → ℕ+ satisfies
  f(t² · f(s)) = s · f(t)²  for all s, t : ℕ+.

Answer: 120, achieved by the function that swaps primes 2↔3, 5↔37, fixes all others.
  1998 = 2 · 3³ · 37, so f(1998) = g(2)·g(3)³·g(37) = 3·8·5 = 120.

Proof overview:
  Let d = f(1).
  Step 1: f(f(n)) = d² · n  (use s=n, t=1 in the equation: f(1·f(n)) = n·f(1)² = n·d²)
  Step 2: f(d · n²) = f(n)²  (use s=1, t=n: f(n²·f(1)) = 1·f(n)² = f(n)²)
  Step 3: d · f(ab) = f(a)·f(b)  (compute f(a)²·f(b)² = f(da²)·f(b²) via Step 2,
          then use the original equation = f(b²·f(da²)) = f(b²·d²·da²) = f(d·(ab)²) = f(ab)²,
          so f(a)·f(b) = f(dab) = d·f(ab) [not quite—need careful manipulation])
  Step 4: g(n) = f(n)/d is a completely multiplicative involution on ℕ+.
  Step 5: g maps primes to primes.
  Step 6: f(1998) = d · g(2) · g(3)³ · g(37).
  Step 7: The minimum of d · g(2) · g(3)³ · g(37) is 120.

Key computation: 1998 = 2 · 3³ · 37.
-/

-- The main theorem. In the compfiles framework, the statement is:
-- IsLeast {n : ℕ+ | ∃ f : ℕ+ → ℕ+, (∀ s t, f (t^2 * f s) = s * (f t)^2) ∧ n = f 1998} 120

-- We split into two parts: the witness and the lower bound.

-- PART A: Witness function achieving f(1998) = 120
-- Define f by: on prime factorizations, apply the swap 2↔3, 5↔37, fix all other primes.
-- This is completely multiplicative, so we just need to define it on primes.
-- For a ℕ+ → ℕ+ function, we can use Nat.factorization.

-- Helper: the witness function on ℕ+
-- We define it as: swap prime factors 2↔3 and 5↔37, fix all others.
-- Since this is purely multiplicative, we can use PNat.factorization

noncomputable def swapPrimes (n : ℕ+) : ℕ+ :=
  -- The function that swaps 2↔3, 5↔37 on the factorization
  -- We use the multiplicative extension of the map on primes:
  -- p ↦ 3 if p=2, 2 if p=3, 37 if p=5, 5 if p=37, p otherwise
  let factors := n.val.factorization
  -- Build the new factorization by applying the prime swap
  let newFactors : ℕ →₀ ℕ := factors.mapDomain (fun p =>
    if p = 2 then 3 else if p = 3 then 2 else if p = 5 then 37 else if p = 37 then 5 else p)
  -- The result as a ℕ+
  ⟨newFactors.prod (· ^ ·), by
    -- The product of prime powers is positive
    apply Finsupp.prod_pos
    intro p hp
    exact Nat.pos_of_ne_zero (fun h => by simp [h] at hp)⟩

-- Actually, let's use a simpler approach: work with the Nat version
-- and use the fact that 1998 = 2 * 3^3 * 37

-- The key is just to exhibit a witness function f with f(1998) = 120.

-- Simple witness: f defined on prime factorizations
-- Since ℕ+ multiplication with factorizations is complicated,
-- let's try a direct construction using UniqueFactorizationMonoid

-- Simpler approach: define f via a recursive/multiplicative extension
-- On ℕ+ we can use the isomorphism ℕ+ ≅ FreeCommMonoid(Primes)

-- PART B: Lower bound
-- For any f satisfying h, we have f(1998) ≥ 120.

-- Key structural lemma 1: f(f(n)) = f(1)² * n
lemma key1 (f : ℕ+ → ℕ+) (h : ∀ s t, f (t^2 * f s) = s * (f t)^2) (n : ℕ+) :
    f (f n) = (f 1)^2 * n := by
  -- Substitute s = n, t = 1 in h:
  -- f(1^2 * f(n)) = n * f(1)^2
  -- f(f(n)) = n * f(1)^2 = f(1)^2 * n
  have := h n 1
  simp at this
  linarith [this]

-- Key structural lemma 2: f(f(1) * n^2) = f(n)^2
lemma key2 (f : ℕ+ → ℕ+) (h : ∀ s t, f (t^2 * f s) = s * (f t)^2) (n : ℕ+) :
    f (f 1 * n^2) = (f n)^2 := by
  -- Substitute s = 1, t = n in h:
  -- f(n^2 * f(1)) = 1 * f(n)^2 = f(n)^2
  have := h 1 n
  simp at this
  linarith [this]

-- Key structural lemma 3: f is injective
lemma key_inj (f : ℕ+ → ℕ+) (h : ∀ s t, f (t^2 * f s) = s * (f t)^2)
    (a b : ℕ+) (hab : f a = f b) : a = b := by
  -- f(f(a)) = d²·a and f(f(b)) = d²·b, so f(a)=f(b) => d²·a = d²·b => a = b
  have ha := key1 f h a
  have hb := key1 f h b
  rw [hab] at ha
  have : (f 1)^2 * a = (f 1)^2 * b := ha.symm.trans hb
  exact PNat.mul_left_cancel this

-- Key structural lemma 4: multiplicativity relation
-- d · f(a·b) = f(a) · f(b) where d = f(1)
lemma key_mult (f : ℕ+ → ℕ+) (h : ∀ s t, f (t^2 * f s) = s * (f t)^2)
    (a b : ℕ+) : f 1 * f (a * b) = f a * f b := by
  -- Proof:
  -- f(a)² · f(b)² = f(d·a²) · f(b²) [by key2]
  -- = f(b²·f(d·a²)) ... [use original equation with s=d·a², t=b]
  -- Hmm, this needs more work. Let me use the double application.
  -- f(f(a·b)) = d²·a·b
  -- f(f(a)) = d²·a, so f(a)/d maps a → f(a)/d ...
  -- Alternative: use h with s = a·b, t appropriately.
  sorry

-- Main theorem: IsLeast statement
-- Given the complexity, we rely on Aristotle for the full proof.
-- The minimum 120 = 3 · 2³ · 5 · 1 is achieved by d=1, g(2)=3, g(3)=2, g(37)=5.

-- Actually, let's state the cleaner version of what the compfiles problem asks:
-- For any f satisfying h, f(1998) ≥ 120.
-- AND there exists an f satisfying h with f(1998) = 120.

-- The lower bound:
-- f(1998) = f(2 · 3³ · 37)
-- = (1/d) · f(2) · f(3)³ · f(37)  [by multiplicativity]
-- = d · g(2) · g(3)³ · g(37)  where g = f/d
-- g is a completely multiplicative involution, g maps primes to primes
-- We need to minimize d · g(2) · g(3)³ · g(37)
-- d = 1 (minimum), then minimize g(2) · g(3)³ · g(37)
-- g is an involution on primes: {g(2), g(3), g(5), g(37), ...} is a permutation
-- To minimize g(2) · g(3)³ · g(37):
--   Since g(3)³ appears with exponent 3, we want g(3) small → g(3) = 2 (g(2) = 3)
--   Then g(37) should be small → g(37) = 5 (g(5) = 37)
--   Result: 3 · 8 · 5 = 120
-- Any other assignment gives a larger value.

-- Let's just submit with the two sorry goals nicely separated:

theorem imo1998_p6_lower_bound
    (f : ℕ+ → ℕ+)
    (h : ∀ s t, f (t^2 * f s) = s * (f t)^2) :
    (120 : ℕ+) ≤ f 1998 := by
  -- We use:
  -- 1. f(f(n)) = d² · n where d = f(1)
  -- 2. d · f(ab) = f(a) · f(b) (quasi-multiplicativity)
  -- 3. g(n) = f(n)/d is completely multiplicative involution
  -- 4. g maps primes to primes
  -- 5. f(1998) = d · g(2) · g(3)³ · g(37)
  -- 6. d · g(2) · g(3)³ · g(37) ≥ 120 by case analysis on involution
  sorry

end Imo1998P6
