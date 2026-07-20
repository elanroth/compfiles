import Mathlib

namespace Imo1998P6

/-- Swap primes: 2↔3, 5↔37, all others fixed -/
def primeSwap : ℕ → ℕ
  | 2 => 3
  | 3 => 2
  | 5 => 37
  | 37 => 5
  | n => n

/-
PROVIDED SOLUTION
Case split on n for values 2, 3, 5, 37, and the default case. Each case is trivial by definition of primeSwap.
-/
lemma primeSwap_invol (n : ℕ) : primeSwap (primeSwap n) = n := by
  unfold primeSwap;
  grind +ring

/-
PROVIDED SOLUTION
We need to show primeSwap p is prime when p is prime. By interval_cases or omega on the prime p, for p = 2 we get 3, for p = 3 we get 2, for p = 5 we get 37, for p = 37 we get 5. For all other primes p, primeSwap p = p which is prime by assumption. Use the fact that for a prime p ≥ 2, we can do interval_cases for p ≤ 37 and for p > 37 (p ≠ 2,3,5,37) primeSwap p = p.
-/
lemma primeSwap_prime {p : ℕ} (hp : p.Prime) : (primeSwap p).Prime := by
  by_cases h₂ : p = 2 ∨ p = 3 ∨ p = 5 ∨ p = 37;
  · rcases h₂ with ( rfl | rfl | rfl | rfl ) <;> native_decide;
  · unfold primeSwap; aesop;

/-
PROVIDED SOLUTION
Since primeSwap is an involution (primeSwap_invol), it is injective. If primeSwap a = primeSwap b, apply primeSwap to both sides and use primeSwap_invol to get a = b. Use Function.Injective.comp or Function.Involutive.injective.
-/
lemma primeSwap_injective : Function.Injective primeSwap := by
  intro a b h;
  unfold primeSwap at h ; aesop;

/-- The completely multiplicative function defined by swapping primes -/
def myFNat (n : ℕ) : ℕ :=
  n.factorization.prod (fun p k => primeSwap p ^ k)

/-
PROVIDED SOLUTION
Unfold myFNat. The factorization of 1 has empty support, so the Finsupp.prod is 1.
-/
lemma myFNat_one : myFNat 1 = 1 := by
  -- The product over the empty set is 1 by definition.
  simp [myFNat]

/-
PROVIDED SOLUTION
myFNat n is a Finsupp.prod of terms primeSwap p ^ k where p is in n.factorization.support (so p is prime and k > 0). primeSwap p is prime (by primeSwap_prime), hence ≥ 2, so primeSwap p ^ k ≥ 1. The product of positive terms is positive. Use Finset.prod_pos and show each factor primeSwap p ^ (n.factorization p) > 0 by pow_pos and Nat.Prime.pos of primeSwap_prime. Also handle the case where the factorization is empty (n=1) giving product = 1 > 0. Actually this should work for all n > 0 since the empty product is 1 > 0 and each nonempty factor is positive.
-/
lemma myFNat_pos {n : ℕ} (hn : 0 < n) : 0 < myFNat n := by
  -- Since $n$ is positive, its factorization is non-empty and consists of positive terms, so the product is positive.
  have h_pos : ∀ p ∈ n.factorization.support, 0 < primeSwap p ^ (n.factorization p) := by
    intro p hp; have := Nat.prime_of_mem_primeFactors hp; rcases p with ( _ | _ | _ | p | p | p | p ) <;> norm_num at * ;
    · exact pow_pos ( by decide ) _;
    · exact pow_pos ( by decide ) _;
    · exact pow_pos ( by decide ) _;
    · exact pow_pos ( Nat.pos_of_ne_zero ( by unfold primeSwap; aesop ) ) _;
  exact Finset.prod_pos h_pos

/-
PROVIDED SOLUTION
Unfold myFNat. Use Nat.factorization_mul (with ha.ne' and hb.ne') to rewrite (a*b).factorization as a.factorization + b.factorization. Then use Finsupp.prod_add_index to split the product. The two conditions for Finsupp.prod_add_index are: (1) for all p, primeSwap p ^ 0 = 1, which is true by pow_zero; (2) for all p k1 k2, primeSwap p ^ (k1 + k2) = primeSwap p ^ k1 * primeSwap p ^ k2, which is pow_add.
-/
lemma myFNat_mul {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    myFNat (a * b) = myFNat a * myFNat b := by
      -- Apply the definition of factorization to rewrite the product.
      have h_factorization : (a * b).factorization = a.factorization + b.factorization := by
        exact Nat.factorization_mul ha.ne' hb.ne';
      unfold myFNat; rw [ h_factorization, Finsupp.prod_add_index' ] ; aesop;
      exact fun a b₁ b₂ => pow_add _ _ _

/-
PROVIDED SOLUTION
By induction on k. Base case k=0: myFNat (a^0) = myFNat 1 = 1 = (myFNat a)^0, using myFNat_one. Inductive step: myFNat (a^(k+1)) = myFNat (a * a^k) = myFNat a * myFNat (a^k) by myFNat_mul (with ha and pow_pos ha k), then by induction hypothesis = myFNat a * (myFNat a)^k = (myFNat a)^(k+1).
-/
lemma myFNat_pow {a : ℕ} (ha : 0 < a) (k : ℕ) :
    myFNat (a ^ k) = myFNat a ^ k := by
      induction' ‹ℕ› with n ih generalizing a <;> simp_all +decide [ pow_succ' ];
      · decide +kernel;
      · rw [ ← ih ha, myFNat_mul ha ( pow_pos ha n ) ]

/-
PROVIDED SOLUTION
Unfold myFNat. The factorization of a prime p is the Finsupp with support {p} and value 1 at p. So the product is primeSwap p ^ 1 = primeSwap p. Use Nat.Prime.factorization and Finsupp.prod_single_index (with pow_zero or similar for the zero case).
-/
lemma myFNat_prime {p : ℕ} (hp : p.Prime) : myFNat p = primeSwap p := by
  unfold myFNat; aesop;

lemma myFNat_prime_pow {p : ℕ} (hp : p.Prime) (k : ℕ) :
    myFNat (p ^ k) = (primeSwap p) ^ k := by
  rw [myFNat_pow hp.pos, myFNat_prime hp]

/-
PROVIDED SOLUTION
By induction on s using Finset.cons_induction. Base case: empty product is 1 on both sides, use myFNat_one. Inductive step: ∏ i ∈ (insert a s), f i = f a * ∏ i ∈ s, f i (with a ∉ s), so myFNat of this equals myFNat (f a) * myFNat (∏ i ∈ s, f i) by myFNat_mul (using hf for positivity and Finset.prod_pos for the product), then by induction hypothesis equals myFNat (f a) * ∏ i ∈ s, myFNat (f i) = ∏ i ∈ (insert a s), myFNat (f i).
-/
lemma myFNat_prod {ι : Type*} (s : Finset ι) (f : ι → ℕ) (hf : ∀ i ∈ s, 0 < f i) :
    myFNat (∏ i ∈ s, f i) = ∏ i ∈ s, myFNat (f i) := by
      induction' s using Finset.cons_induction with a s ha ih;
      · exact myFNat_one;
      · simp +decide [ *, Finset.prod_cons ] at *;
        rw [ ← ih hf.2, myFNat_mul hf.1 ( Finset.prod_pos hf.2 ) ]

/-
PROVIDED SOLUTION
The proof goes as follows:

Step 1: Write n = ∏ p in n.factorization.support, p ^ (n.factorization p) using Nat.factorization_prod_pow_eq_self hn.ne'.

Step 2: Compute myFNat n using myFNat_prod and myFNat_prime_pow:
  myFNat n = myFNat (∏ p in n.factorization.support, p ^ n.factorization p)
           = ∏ p in n.factorization.support, myFNat (p ^ n.factorization p)   [by myFNat_prod, with positivity from pow_pos (Nat.Prime.pos ...)]
           = ∏ p in n.factorization.support, (primeSwap p) ^ n.factorization p   [by myFNat_prime_pow]

Step 3: Compute myFNat (myFNat n) similarly:
  myFNat (myFNat n) = myFNat (∏ p in n.factorization.support, (primeSwap p) ^ n.factorization p)
                    = ∏ p in n.factorization.support, myFNat ((primeSwap p) ^ n.factorization p)   [by myFNat_prod]
                    = ∏ p in n.factorization.support, (primeSwap (primeSwap p)) ^ n.factorization p   [by myFNat_prime_pow using primeSwap_prime]
                    = ∏ p in n.factorization.support, p ^ n.factorization p   [by primeSwap_invol]
                    = n   [by Nat.factorization_prod_pow_eq_self]

The key steps use:
- conv_lhs { rw [← Nat.factorization_prod_pow_eq_self hn.ne'] } to rewrite n as its factorization product
- myFNat_prod to distribute myFNat over products
- myFNat_prime_pow to evaluate myFNat on prime powers
- primeSwap_invol to simplify primeSwap (primeSwap p) = p
- Nat.factorization_prod_pow_eq_self to reassemble
-/
lemma myFNat_invol {n : ℕ} (hn : 0 < n) : myFNat (myFNat n) = n := by
  have h_factorization : myFNat (myFNat n) = ∏ p ∈ n.factorization.support, (primeSwap (primeSwap p)) ^ n.factorization p := by
    have h_factorization : myFNat n = ∏ p ∈ n.factorization.support, (primeSwap p) ^ n.factorization p := by
      exact?;
    rw [ h_factorization, myFNat_prod ];
    · refine' Finset.prod_congr rfl fun p hp => _;
      apply myFNat_prime_pow; exact primeSwap_prime (Nat.prime_of_mem_primeFactors hp);
    · exact fun p hp => pow_pos ( Nat.Prime.pos ( primeSwap_prime ( Nat.prime_of_mem_primeFactors hp ) ) ) _;
  exact h_factorization.trans ( by rw [ Finset.prod_congr rfl fun p hp => by rw [ primeSwap_invol p ] ] ; exact Nat.factorization_prod_pow_eq_self hn.ne' )

/-
PROVIDED SOLUTION
This is a computation. Try native_decide or decide.
-/
lemma myFNat_1998 : myFNat 1998 = 120 := by
  native_decide +revert

/-- Lift to ℕ+ -/
def myF (n : ℕ+) : ℕ+ :=
  ⟨myFNat n, myFNat_pos n.pos⟩

lemma myF_val (n : ℕ+) : (myF n).val = myFNat n := rfl

theorem witness_1998 :
    ∃ f : ℕ+ → ℕ+,
      (∀ s t, f (t^2 * f s) = s * (f t)^2) ∧ f 1998 = 120 := by
  refine ⟨myF, ?_, ?_⟩
  · -- Functional equation
    intro s t
    apply PNat.eq
    simp only [myF_val, PNat.mul_coe, PNat.pow_coe, PNat.mk_ofNat, Nat.cast_ofNat]
    rw [myFNat_mul (by positivity) (myFNat_pos s.pos)]
    rw [myFNat_pow (by positivity)]
    rw [myFNat_invol s.pos]
    ring
  · -- f(1998) = 120
    apply PNat.eq
    exact myFNat_1998

end Imo1998P6