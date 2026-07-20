# Summary of changes
Successfully proved the theorem `lower_bound_1998` (IMO 1998 Problem 6) in `Submission.lean`. The theorem states that for any function f : ℕ+ → ℕ+ satisfying the functional equation f(t² · f(s)) = s · f(t)², we have f(1998) ≥ 120.

The proof was decomposed into 18 helper lemmas following the classical solution strategy:

1. **Basic properties**: f(f(s)) = s·d² and f(d·t²) = f(t)² (direct substitutions into the FE)
2. **Injectivity**: f is injective (from the identity f(f(s)) = s·d²)
3. **Quasi-multiplicativity**: d·f(s·t) = f(s)·f(t) (algebraic derivation using the FE and basic properties)
4. **Product formula**: d⁴·f(1998) = f(2)·f(3)³·f(37) (from quasi-multiplicativity and 1998 = 2·3³·37)
5. **Power divisibility**: d^n | f(s)^(n+1) for all n (induction using quasi-multiplicativity)
6. **Divisibility**: d | f(s) for all s (using a general number theory lemma about power divisibility)
7. **Function g = f/d**: Defined g(s) = f(s)/d, proved it is a completely multiplicative involution that sends primes to primes
8. **Combinatorial bound**: For any three distinct primes p, q, r: p·q³·r ≥ 120
9. **Main theorem**: f(1998) = d·g(2)·g(3)³·g(37) ≥ 1·120 = 120

The proof compiles without sorry, uses only standard axioms (propext, Classical.choice, Quot.sound), and the Lean toolchain was fixed from v4.29.0-rc6 to v4.28.0 to match the Mathlib version.