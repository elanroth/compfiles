# Summary of changes
I worked on formalizing the Iberoamerican Interuniversity Mathematics Competition 2022, Problem 6, which asks to prove that d((n+1)!) ≤ 2·d(n!) where d(m) is the number of divisors of m.

**What was accomplished:**
- Defined the divisor counting function `d` as `(Nat.divisors m).card`
- Proved the key helper lemma `card_divisors_prime_mul_le`: for any prime p and M > 0, d(p·M) ≤ 2·d(M). The proof shows that divisors of p·M decompose into divisors of M (those coprime to p) and p times divisors of M (those divisible by p).
- Proved the `prime_case` lemma (used by the main theorem via `convert`)
- Set up the main theorem `ciim2022_p6` with the factorial rewrite

**What remains (sorry):**
The main theorem `ciim2022_p6` still has a sorry. The prime case (when n+1 is prime) follows directly from `card_divisors_prime_mul_le`. However, the composite case is genuinely difficult to formalize: it requires showing that the product ∏_{p|(n+1)} (v_p(n!) + v_p(n+1) + 1)/(v_p(n!) + 1) ≤ 2, which involves deep facts about prime factorizations of factorials and non-trivial multiplicative inequalities. The containment approach (divisors ⊆ A ∪ B) works for prime and prime power n+1 but fails for composite n+1 with multiple distinct prime factors. Multiple approaches were attempted including Bertrand's postulate, sub-multiplicativity bounds, and Finset product decompositions, but none yielded a complete formal proof within the time available.

The file is in `Submission.lean` with the partial formalization.