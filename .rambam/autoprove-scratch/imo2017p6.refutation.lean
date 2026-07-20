
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

end Imo2017P6
