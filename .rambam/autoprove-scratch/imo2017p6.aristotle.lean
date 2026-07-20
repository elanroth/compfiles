/-
  IMO 2017 Problem 6

  Given a finite set S of primitive lattice points (gcd(x,y)=1),
  prove there exists n>0 and a : ℕ → ℤ such that
  ∑ i in range n, a(i) * x^i * y^(n-i) = 1 for all (x,y) ∈ S.

  Note: the sum ∑ i in range n gives monomials x^0*y^n, x^1*y^(n-1), ..., x^(n-1)*y^1.
  This is a homogeneous polynomial of degree n that is divisible by y.

  Proof strategy: Induction on |S|.

  Base case (S = ∅): n=1, any a, vacuously true.

  Inductive step: Suppose g works for S' (with degree n, coefficients a).
  For (p,q) with gcd(p,q)=1, by Bézout ∃ u,v: u*p + v*q = 1.
  Key: (q*x - p*y) vanishes at (p,q).

  Construction for S' ∪ {(p,q)}:
  Let h(x,y) = ∑_{i in range n} a(i) * x^i * y^(n-i) (evaluates to 1 on S').
  Let L(x,y) = (q*x - p*y) (vanishes at (p,q)).
  Let Lᵢ(x,y) = L evaluated "at each point in S' " ??? 

  Actually: We want f such that:
  - f(s) = 1 for s ∈ S' (g already does this)
  - f(p,q) = 1

  Approach: f = g^M for large M (keeps f=1 on S') minus a correction.
  Let P = ∏_{s∈S'} (s.2*x - s.1*y) (vanishes on all of S').
  Then f = g^M - C * x^? * P for C chosen to make f(p,q)=1.

  More carefully:
  Take f = g^M + correction, where correction vanishes on S' and equals 1-g(p,q)^M at (p,q).
  correction = [(1 - g(p,q)^M) / P(p,q)] * P(x,y) * x^k
  We need P(p,q) | (1 - g(p,q)^M) for integer C.

  P(p,q) = ∏_{s∈S'} (s.2*p - s.1*q).
  g(p,q)^M - 1 must be divisible by P(p,q).
  By Euler: choose M = φ(|P(p,q)|), then g(p,q)^M ≡ 1 mod P(p,q) if gcd(g(p,q), P(p,q))=1.

  This requires gcd(g(p,q), s.2*p - s.1*q) = 1 for each s=(s.1,s.2) ∈ S'.
  Since g(s.1,s.2) = 1 (inductive hypothesis) and g is homogeneous and gcd(p,q)=1...

  This is quite involved. Let Aristotle handle the full proof.
-/

import Mathlib.Tactic
import Mathlib.Data.Int.GCD
import Mathlib.RingTheory.Coprime.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.Data.ZMod.Basic

namespace Imo2017P6

-- Key lemma: for a single primitive point (p,q), there exist u,v with u*p + v*q = 1
-- This gives a degree-1 homogeneous polynomial taking value 1 at (p,q)
-- But we need a polynomial in ∑ i in range n form (which excludes x^n term)

-- Reformulation: we need ∑ i in range n, a i * x^i * y^(n-i) = 1
-- This polynomial is divisible by y (all terms have y^(n-i) with n-i ≥ 1)
-- So it can only equal 1 at (p,q) with q ≠ 0.

-- Key observation: if q = 0, then gcd(p,0) = |p| = 1, so p = ±1.
-- At (p,0): sum = ∑ a(i) * p^i * 0^(n-i) = 0 ≠ 1. Contradiction!
-- So the statement is ONLY consistent if no point in S has y-coordinate 0.

-- Hmm, but the problem doesn't exclude (1,0) or (-1,0).
-- This suggests either:
-- (a) The Lean statement has a typo (should be range (n+1))
-- (b) There's something clever going on

-- Let's just try to prove it for the case where all points have nonzero y,
-- and see if the empty-S base case plus induction covers the Lean statement.

-- Actually: if S contains a point with y=0 (i.e., (±1, 0)), then the
-- conclusion ∃ n a, ∀ s ∈ S, sum = 1 is FALSE for that point.
-- So the theorem as stated is false in general.

-- HOWEVER: maybe in the Lean formulation, we can derive False from the hypotheses
-- in that case? No, gcd(1,0)=1 in Lean, so the hypothesis holds for S={(1,0)}.

-- The theorem is likely provable using induction, carefully handling the cases,
-- and Aristotle may find a proof by choosing the right n and a combinatorially.

-- Let Aristotle try a direct induction proof:

lemma sum_at_one_zero_eq_zero (n : ℕ) (a : ℕ → ℤ) :
    ∑ i ∈ Finset.range n, a i * (1 : ℤ) ^ i * (0 : ℤ) ^ (n - i) = 0 := by
  apply Finset.sum_eq_zero
  intro i hi
  simp only [Finset.mem_range] at hi
  have hpos : 0 < n - i := Nat.sub_pos_of_lt hi
  simp [ne_of_gt hpos]

lemma no_polynomial_at_one_zero :
    ¬ ∃ n : ℕ, 0 < n ∧ ∃ a : ℕ → ℤ,
      ∀ s ∈ ({(1, 0)} : Finset (ℤ × ℤ)),
        ∑ i ∈ Finset.range n, a i * s.1 ^ i * s.2 ^ (n - i) = 1 := by
  rintro ⟨n, _, a, ha⟩
  have h := ha (1, 0) (by simp)
  rw [sum_at_one_zero_eq_zero] at h
  norm_num at h

lemma claimed_statement_is_false :
    ¬ ∀ S : Finset (ℤ × ℤ), (∀ s ∈ S, gcd s.1 s.2 = 1) →
      ∃ n : ℕ, 0 < n ∧ ∃ a : ℕ → ℤ,
        ∀ s ∈ S, ∑ i ∈ Finset.range n, a i * s.1 ^ i * s.2 ^ (n - i) = 1 := by
  intro h
  apply no_polynomial_at_one_zero
  apply h {(1, 0)}
  intro s hs
  simp only [Finset.mem_singleton] at hs
  subst s
  norm_num

theorem imo2017_p6 (S : Finset (ℤ × ℤ)) (hS : ∀ s ∈ S, gcd s.1 s.2 = 1) :
    ∃ n : ℕ, 0 < n ∧ ∃ a : ℕ → ℤ,
      ∀ s ∈ S, ∑ i ∈ Finset.range n, a i * s.1 ^ i * s.2 ^ (n - i) = 1 := by
  sorry

end Imo2017P6
