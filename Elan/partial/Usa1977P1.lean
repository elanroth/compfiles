/-
Scaffold for USAMO 1977, Problem 1 — working notes, not a submission.

Statement (from Compfiles/Usa1977P1.lean):
  determine all (m, n) with  geomSum m ∣ geomSumStep m n,  where
    geomSum m     = 1 + X + ... + X^m
    geomSumStep m n = 1 + X^n + ... + X^(m*n).

THE ANSWER is  { (m, n) | Nat.gcd (m + 1) n = 1 }.

WHY (the mathematical skeleton this file breaks into lemmas):

Over ℂ, `geomSum m` has roots exactly the primitive-or-not (m+1)-th roots of
unity other than 1, each simple, since
    (X - 1) * geomSum m = X^(m+1) - 1.
Likewise
    (X^n - 1) * geomSumStep m n = X^(n*(m+1)) - 1.
So for ζ ≠ 1 with ζ^(m+1) = 1:
    geomSumStep m n (ζ) = 0   ⟺   ζ^n ≠ 1.
Hence divisibility holds iff no (m+1)-th root of unity other than 1 is killed
by `X^n - 1`, i.e. iff the only common solution of ζ^(m+1) = 1 and ζ^n = 1 is
ζ = 1, i.e. iff  gcd(m+1, n) = 1.

An integer-polynomial route that avoids ℂ (probably the better Lean path):
  geomSum m ∣ geomSumStep m n
    ⟺ X^(m+1) - 1 ∣ X^(n*(m+1)) - 1 / (X^n - 1) ... -- see step 3 below
  and the clean fact to lean on is
    X^a - 1 ∣ X^b - 1  ⟺  a ∣ b,
  which is `Polynomial.X_pow_sub_one_dvd_X_pow_sub_one` style; combined with
    gcd(X^a - 1, X^b - 1) = X^gcd(a,b) - 1.

STATUS: every lemma below is `sorry`. They are stated so they compose: given
`key_root_criterion` and `gcd_one_iff`, `usa1977_p1_iff` is bookkeeping.
-/

import Mathlib

namespace Usa1977P1Scaffold

open Polynomial Finset

noncomputable def geomSum (m : ℕ+) : ℤ[X] :=
  ∑ k ∈ range (m + 1), X ^ k

noncomputable def geomSumStep (m n : ℕ+) : ℤ[X] :=
  ∑ k ∈ range (m + 1), X ^ (k * n : ℕ)

/-- The proposed answer set. -/
def solutionSet : Set (ℕ+ × ℕ+) := { p | Nat.gcd (p.1 + 1) p.2 = 1 }

/-! ### Step 1 — the two telescoping identities.
These are the only computational facts needed, and both should be within reach
of `Polynomial.geom_sum_mul` / `mul_geom_sum` in Mathlib. -/

lemma sub_one_mul_geomSum (m : ℕ+) :
    (X - 1) * geomSum m = X ^ ((m : ℕ) + 1) - 1 := by
  sorry

lemma pow_sub_one_mul_geomSumStep (m n : ℕ+) :
    (X ^ (n : ℕ) - 1) * geomSumStep m n = X ^ ((n : ℕ) * ((m : ℕ) + 1)) - 1 := by
  sorry

/-! ### Step 2 — reduce divisibility of the geometric sums to divisibility of
`X^a - 1`s.  This is where the two identities above get cancelled against each
other; the cancellation is legitimate because `ℤ[X]` is a domain and neither
`X - 1` nor `X^n - 1` is a zero divisor. -/

/-- Multiplying through by the non-zero-divisor `X - 1` is harmless in the domain
`ℤ[X]`, and it turns the left side into `X^(m+1) - 1` by Step 1. This is the
division-free form; `ℤ[X]` has no `Div`, so do not phrase it as a quotient. -/
lemma geomSum_dvd_iff (m n : ℕ+) :
    geomSum m ∣ geomSumStep m n ↔
      (X ^ ((m : ℕ) + 1) - 1 : ℤ[X]) ∣ (X - 1) * geomSumStep m n := by
  sorry

/-! ### Step 3 — the arithmetic core.
`X^a - 1 ∣ X^b - 1 ↔ a ∣ b`, and `gcd (X^a - 1) (X^b - 1) = X^(gcd a b) - 1`.
Mathlib has the ℕ analogue (`Nat.sub_one_dvd_sub_of_dvd_sub`, `Nat.gcd`...); the
polynomial version may need to be proved here. -/

lemma X_pow_sub_one_dvd_iff (a b : ℕ) (ha : 0 < a) :
    (X ^ a - 1 : ℤ[X]) ∣ (X ^ b - 1) ↔ a ∣ b := by
  sorry

lemma gcd_X_pow_sub_one (a b : ℕ) :
    EuclideanDomain.gcd (X ^ a - 1 : ℚ[X]) (X ^ b - 1) = X ^ Nat.gcd a b - 1 := by
  sorry

/-! ### Step 4 — the root criterion, stated so it is the only place roots of
unity appear. -/

lemma key_root_criterion (m n : ℕ+) :
    geomSum m ∣ geomSumStep m n ↔ Nat.gcd ((m : ℕ) + 1) (n : ℕ) = 1 := by
  sorry

/-! ### Step 5 — assembly.  Given Step 4 this is definitional unfolding of
`solutionSet`, and is the statement that should be transplanted into
`Compfiles/Usa1977P1.lean` once the pieces above are closed. -/

theorem usa1977_p1_iff (m n : ℕ+) :
    (m, n) ∈ solutionSet ↔ geomSum m ∣ geomSumStep m n := by
  rw [key_root_criterion]
  rfl

end Usa1977P1Scaffold
