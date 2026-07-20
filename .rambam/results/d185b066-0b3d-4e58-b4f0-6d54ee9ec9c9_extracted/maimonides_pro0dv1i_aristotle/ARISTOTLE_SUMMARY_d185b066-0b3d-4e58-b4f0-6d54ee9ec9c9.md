# Summary of changes
Successfully filled all sorries in the IMO 1998 Problem 6 formalization.

**Problem:** For any function f : ℕ+ → ℕ+ satisfying f(t² · f(s)) = s · f(t)² for all s, t, prove that f(1998) ≥ 120.

**Proof structure in `Submission.lean`:**

The proof is decomposed into 7 parts with ~20 helper lemmas:

1. **Basic FE consequences** (`f_f`, `f_sq_d`, `f_inj`, `f_scale`): Direct substitutions (t=1, s=1) give f(f(s)) = s·d², f(t²·d) = f(t)², injectivity, and f(s·d²) = f(s)·d².

2. **Multiplicativity** (`f_key`, `f_d_mul`, `f_sq_nat`, `f_mult_nat`): Through a chain of substitutions, derive that d·f(a·b) = f(a)·f(b) for all a, b (as natural numbers), where d = f(1).

3. **Divisibility** (`d_dvd_f_sq`, `f_pow_nat`, `d_dvd_f`): Show d | f(n) for all n using a p-adic valuation argument: from f(pᵏ)·d^(k-1) = f(p)ᵏ, we get d^(k-1) | f(p)ᵏ for all k, which forces d | f(p) by taking k large enough.

4. **The quotient function g** (`gN_pos`, `f_eq_d_mul_gN`, `gN_mult`, `gN_one`, `gN_involution`): Define g(n) = f(n)/d, show g is completely multiplicative, and g(g(n)) = n (an involution).

5. **g maps primes to primes** (`gN_inj`, `gN_prime`): If g(p) = a·b with a,b ≥ 2, then g(a)·g(b) = p, forcing one factor to be 1, contradicting g(1) = 1 ≠ a ≥ 2.

6. **Computing f(1998)** (`factorization_1998`, `f_1998_eq`): f(1998) = d·g(2)·g(3)³·g(37) since 1998 = 2·3³·37.

7. **Combinatorial bound** (`three_distinct_primes_bound`): For distinct primes p, q, r: p·q³·r ≥ 120 (case analysis on q=2 vs q≥3).

The main theorem follows: f(1998) = d·g(2)·g(3)³·g(37) ≥ 1·120 = 120.

The proof uses only standard axioms (propext, Classical.choice, Quot.sound) — verified via `#print axioms`.