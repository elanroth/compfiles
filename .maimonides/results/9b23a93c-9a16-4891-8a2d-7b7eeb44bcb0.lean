/-
Copyright (c) 2024 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InternLM-MATH LEAN Formalizer v0.1
-/

import Mathlib

/-!
# International Mathematical Olympiad 1998, Problem 6

Consider all functions f from the set of all positive integers into itself satisfying
f(t²f(s)) = sf(t)² for all s and t.
Determine the least possible value of f(1998).

## Solution

The answer is 120.

The key observations are:
1. Setting t = 1: f(f(s)) = s · f(1)².
2. Setting s = 1: f(t² · f(1)) = f(t)².
3. From (1), f is injective.
4. Let c = f(1). One shows c | f(n) for all n, and g = f/c is a completely
   multiplicative involution of ℕ+ that permutes primes and fixes primes dividing c.
5. f(1998) = c · g(2) · g(3)³ · g(37) where g(2), g(3), g(37) are distinct primes.
6. The minimum is achieved at c = 1 with g(3) = 2, g(2) = 3, g(37) = 5, g(5) = 37,
   giving f(1998) = 3 · 8 · 5 = 120.
-/

namespace Imo1998P6

-- The original problem statement was:
-- problem imo1998_p6
--     (f : ℕ+ → ℕ+)
--     (h : ∀ s t, f (t^2 * f s) = s * (f t)^2) :
--     IsLeast {n : ℕ | n = f 1998} solution := by sorry
-- This is incorrect because it claims that for EVERY f satisfying the equation,
-- f(1998) = 120. But the identity function satisfies the equation and gives f(1998) = 1998.
-- The correct statement is that 120 is the LEAST value of f(1998) across all valid f.

/-! ### Part 1: Construction of the witness function achieving f(1998) = 120 -/

/-- Swap primes: 2 ↔ 3, 5 ↔ 37, other primes fixed -/
def swapPrime (p : ℕ) : ℕ :=
  if p = 2 then 3
  else if p = 3 then 2
  else if p = 5 then 37
  else if p = 37 then 5
  else p

lemma swapPrime_invol (p : ℕ) : swapPrime (swapPrime p) = p := by
  unfold swapPrime
  split_ifs <;> omega

lemma swapPrime_prime {p : ℕ} (hp : p.Prime) : (swapPrime p).Prime := by
  unfold swapPrime;
  split_ifs <;> simp_all +decide [ Nat.Prime ]

/-- The witness function: apply swapPrime to each prime factor -/
noncomputable def witnessFun (n : ℕ) : ℕ :=
  if n = 0 then 0
  else n.factorization.prod (fun p k => swapPrime p ^ k)

lemma witnessFun_pos {n : ℕ} (hn : 0 < n) : 0 < witnessFun n := by
  refine' Nat.pos_of_ne_zero _;
  simp [witnessFun, hn.ne'];
  intro p pp dp h; have := swapPrime_prime pp; aesop;

lemma witnessFun_one : witnessFun 1 = 1 := by
  unfold witnessFun; aesop;

lemma witnessFun_mul {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    witnessFun (a * b) = witnessFun a * witnessFun b := by
  unfold witnessFun;
  simp +decide [ ha.ne', hb.ne', Nat.factorization_mul, Finsupp.prod_add_index' ];
  rw [ Finsupp.prod_add_index' ] ; aesop;
  exact fun _ _ _ => pow_add _ _ _

lemma witnessFun_invol {n : ℕ} (hn : 0 < n) : witnessFun (witnessFun n) = n := by
  unfold witnessFun;
  split_ifs <;> simp_all +decide [ Finsupp.prod ];
  · simp_all +decide [ Finset.prod_eq_zero_iff, Nat.factorization_eq_zero_iff ];
    unfold swapPrime at * ; aesop;
  · have h_swapPrime_prime : ∀ p ∈ n.primeFactors, Nat.Prime (swapPrime p) := by
      exact fun p hp => swapPrime_prime <| Nat.prime_of_mem_primeFactors hp;
    have h_prime_factors : (∏ x ∈ n.primeFactors, swapPrime x ^ n.factorization x).primeFactors = Finset.image swapPrime n.primeFactors := by
      ext; simp [h_swapPrime_prime];
      constructor <;> intro h
      all_goals generalize_proofs at *;
      · have := h.1.dvd_iff_not_coprime.mp h.2.1; simp_all +decide [ Nat.coprime_prod_right_iff, Nat.coprime_prod_left_iff ] ;
        obtain ⟨ p, hp₁, hp₂, hp₃ ⟩ := this; use p; simp_all +decide [ Nat.Prime.coprime_iff_not_dvd ] ;
        have := Nat.Prime.dvd_of_dvd_pow h.1 hp₃; ( have := Nat.prime_dvd_prime_iff_eq h.1 ( h_swapPrime_prime p hp₁ hp₂ ) ; aesop; );
      · rcases h with ⟨ p, ⟨ hp₁, hp₂, hp₃ ⟩, rfl ⟩ ; exact ⟨ h_swapPrime_prime p ( by aesop ), dvd_trans ( dvd_pow_self _ ( Finsupp.mem_support_iff.mp ( by aesop ) ) ) ( Finset.dvd_prod_of_mem _ ( by aesop ) ), by aesop ⟩ ;
    have h_factorization : ∀ p ∈ (∏ x ∈ n.primeFactors, swapPrime x ^ n.factorization x).primeFactors, (∏ x ∈ n.primeFactors, swapPrime x ^ n.factorization x).factorization p = n.factorization (swapPrime p) := by
      intro p hp; rw [ Nat.factorization_prod ] <;> simp_all +decide [ Finset.prod_eq_zero_iff, Nat.Prime.ne_zero ] ;
      obtain ⟨ q, ⟨ hq₁, hq₂ ⟩, rfl ⟩ := hp; rw [ Finset.sum_eq_single q ] <;> simp_all +decide [ Nat.factorization_eq_zero_iff, Nat.Prime.ne_zero ] ;
      · rw [ swapPrime_invol ];
      · unfold swapPrime; aesop;
    rw [ h_prime_factors, Finset.prod_image ];
    · conv_rhs => rw [ ← Nat.factorization_prod_pow_eq_self hn.ne' ];
      refine' Finset.prod_congr rfl fun p hp => _;
      rw [ h_factorization _ ( h_prime_factors.symm ▸ Finset.mem_image_of_mem _ hp ), swapPrime_invol ];
    · intro p hp q hq; have := swapPrime_invol p; have := swapPrime_invol q; aesop;

lemma witnessFun_prime {p : ℕ} (hp : p.Prime) : witnessFun p = swapPrime p := by
  unfold witnessFun; aesop;

lemma witnessFun_1998 : witnessFun 1998 = 120 := by
  have h2 : witnessFun 2 = 3 := by rw [witnessFun_prime (by norm_num)]; rfl
  have h3 : witnessFun 3 = 2 := by rw [witnessFun_prime (by norm_num)]; rfl
  have h37 : witnessFun 37 = 5 := by rw [witnessFun_prime (by norm_num)]; rfl
  have : (1998 : ℕ) = 2 * (3 * (3 * (3 * 37))) := by norm_num
  rw [this, witnessFun_mul (by norm_num) (by norm_num), h2,
      witnessFun_mul (by norm_num) (by norm_num), h3,
      witnessFun_mul (by norm_num) (by norm_num), h3,
      witnessFun_mul (by norm_num) (by norm_num), h3, h37]

/-- The witness function on ℕ+ -/
noncomputable def witnessPNat : ℕ+ → ℕ+ := fun n =>
  ⟨witnessFun n, witnessFun_pos n.pos⟩

lemma witnessPNat_val (n : ℕ+) : (witnessPNat n : ℕ) = witnessFun n := rfl

/-- The witness function satisfies the functional equation -/
lemma witness_satisfies (s t : ℕ+) :
    witnessPNat (t ^ 2 * witnessPNat s) = s * (witnessPNat t) ^ 2 := by
  have h1 : witnessFun (t^2 * witnessFun s) = s * (witnessFun t)^2 := by
    convert witnessFun_mul ( pow_pos t.pos 2 ) ( witnessFun_pos s.pos ) using 1;
    rw [ witnessFun_invol s.pos ] ; ring;
    rw [ sq, ← witnessFun_mul ] <;> norm_num;
    rw [ sq ];
  exact PNat.eq h1

/-- There exists a function satisfying the equation with f(1998) = 120 -/
lemma f_1998_achievable :
    ∃ f : ℕ+ → ℕ+, (∀ s t, f (t ^ 2 * f s) = s * (f t) ^ 2) ∧ f 1998 = ⟨120, by norm_num⟩ := by
  exact ⟨witnessPNat, witness_satisfies, by
    apply PNat.eq
    simp [witnessPNat, witnessFun_1998]⟩

/-! ### Part 2: Lower bound — for all valid f, f(1998) ≥ 120 -/

lemma lb_ff (f : ℕ+ → ℕ+) (hf : ∀ s t, f (t ^ 2 * f s) = s * (f t) ^ 2)
    (s : ℕ+) : f (f s) = s * (f 1) ^ 2 := by
  have := hf s 1; simpa using this

lemma lb_f_sq_c (f : ℕ+ → ℕ+) (hf : ∀ s t, f (t ^ 2 * f s) = s * (f t) ^ 2)
    (t : ℕ+) : f (t ^ 2 * f 1) = (f t) ^ 2 := by
  have := hf 1 t; simpa using this

/-
PROVIDED SOLUTION
If f(a) = f(b), then f(f(a)) = f(f(b)), so a * (f 1)^2 = b * (f 1)^2, so a = b (by PNat.mul_right_cancel or similar).
-/
lemma lb_f_inj (f : ℕ+ → ℕ+) (hf : ∀ s t, f (t ^ 2 * f s) = s * (f t) ^ 2) :
    Function.Injective f := by
  intro a b; have := hf a 1; have := hf b 1; aesop;

/-
PROVIDED SOLUTION
From lb_ff: f(f(s)) = s * c². Apply f to both sides: f(s * c²) = f(f(f(s))). But f(f(f(s))) = f(f(u)) where u = f(s), so by lb_ff applied to u: f(f(u)) = u * c² = f(s) * c². Hence f(s * c²) = f(s) * c².
-/
lemma lb_f_sc2 (f : ℕ+ → ℕ+) (hf : ∀ s t, f (t ^ 2 * f s) = s * (f t) ^ 2)
    (s : ℕ+) : f (s * (f 1) ^ 2) = f s * (f 1) ^ 2 := by
  have := hf s 1; have := hf ( f s ) 1; simp_all +decide [ mul_comm, mul_left_comm ] ;

/-
PROVIDED SOLUTION
Replace s by f(s) in hf: f(t² * f(f(s))) = f(s) * f(t)². Since f(f(s)) = s * c² (by lb_ff), we get f(t² * s * c²) = f(s) * f(t)². By lb_f_sc2 applied to n = t²*s: f(t²*s * c²) = f(t²*s) * c². Hence f(t²*s) * c² = f(s) * f(t)², i.e., c² * f(t²*s) = f(s) * f(t)².
-/
lemma lb_c2_f_mul (f : ℕ+ → ℕ+) (hf : ∀ s t, f (t ^ 2 * f s) = s * (f t) ^ 2)
    (s t : ℕ+) : (f 1) ^ 2 * f (t ^ 2 * s) = f s * (f t) ^ 2 := by
  -- From Lemma 2, we know that $f(t^2 f(f(s))) = f(s) f(t)^2$. And since $f(f(s)) = s f(1)^2$, we substitute this into the equation.
  have h_ft2f : f (t ^ 2 * (s * (f 1) ^ 2)) = f s * (f t) ^ 2 := by
    rw [ ← hf, show f s = f s from rfl ];
    simpa using hf ( f s ) t;
  -- By Lemma 2, we know that $f(t^2 s * c^2) = f(t^2 s) * c^2$.
  have h_ft2sc2 : f (t ^ 2 * s * (f 1) ^ 2) = f (t ^ 2 * s) * (f 1) ^ 2 := by
    exact?;
  simp_all +decide [ mul_assoc, mul_comm, mul_left_comm ]

/-
PROVIDED SOLUTION
From lb_c2_f_mul with s = u²: c² * f(t² * u²) = f(u²) * f(t)².
But t² * u² = (tu)², so c² * f((tu)²) = f(u²) * f(t)².
From lb_c2_f_mul with s = 1, t → v: c² * f(v²) = c * f(v)², so c * f(v²) = f(v)².
Using this: f(u²) = f(u)² / c (i.e., c * f(u²) = f(u)²), and f((tu)²) = f(tu)² / c.
So c² * f(tu)² / c = f(u)² * f(t)² / c, giving c * f(tu)² = f(u)² * f(t)².
Hence (c * f(tu))² = c² * f(tu)² = ... wait. Actually:
c² * f((tu)²) = f(u²) * f(t)²
c * f((tu)²) = f(u²) * f(t)² / c  ... need c | f(u²)*f(t)² which follows from c*f(v²) = f(v)².
Actually: c² * f((tu)²) = f(u²) * f(t)². And c * f(v²) = f(v)² for all v.
So c * f((tu)²) = f(tu)², hence c² * f((tu)²) = c * f(tu)².
And c * f(u²) = f(u)², so f(u²) * f(t)² = f(u)² * f(t)² / c.
So c * f(tu)² = f(u)² * f(t)² / c, i.e., c² * f(tu)² = f(t)² * f(u)².
Taking square roots (everything is in ℕ+): c * f(tu) = f(t) * f(u).

Formally: from lb_c2_f_mul with s = 1: c² * f(t²) = c * f(t)².
So we have c * f(t²) = f(t)² (after dividing by c, which is valid in ℕ+ by cancellation).
Then c² * f((tu)²) = f(u²) * f(t)², and c * f((tu)²) = f(tu)², c * f(u²) = f(u)².
So c * f(tu)² = f(u)² * f(t)² / c... working in ℕ+ this means c² * f(tu)² = f(t)² * f(u)².
In PNat, (c * f(tu))² = c² * f(tu)² = f(t)² * f(u)² = (f(t) * f(u))².
Since everything is positive and squares are equal, c * f(tu) = f(t) * f(u).
-/
lemma lb_c_f_mul (f : ℕ+ → ℕ+) (hf : ∀ s t, f (t ^ 2 * f s) = s * (f t) ^ 2)
    (t u : ℕ+) : f 1 * f (t * u) = f t * f u := by
  -- From lb_c2_f_mul with s = u², we get c² * f(t² * u²) = f(u²) * f(t)².
  have h_c2_f_mul_u2 (t u : ℕ+) : (f 1) ^ 2 * f (t ^ 2 * u ^ 2) = f (u ^ 2) * (f t) ^ 2 := by
    convert lb_c2_f_mul f hf ( u ^ 2 ) t using 1;
  -- From lb_c2_f_mul with s = 1, we get c² * f(t²) = c * f(t)².
  have h_c2_f_mul_one (t : ℕ+) : (f 1) ^ 2 * f (t ^ 2) = f 1 * (f t) ^ 2 := by
    simpa using h_c2_f_mul_u2 t 1;
  -- Using the results from lb_c2_f_mul_u2 and lb_c2_f_mul_one, we can derive that $c * f(tu) = f(t) * f(u)$.
  have h_c_f_mul : ∀ t u : ℕ+, (f 1) ^ 2 * f (t * u) ^ 2 = f t ^ 2 * f u ^ 2 := by
    intros t u
    have := h_c2_f_mul_u2 t u
    have := h_c2_f_mul_one (t * u)
    simp_all +decide [ mul_pow, mul_assoc, mul_comm, mul_left_comm ];
    have := h_c2_f_mul_one u; simp_all +decide [ sq, mul_assoc, mul_comm, mul_left_comm ] ;
    simp_all +decide [ ← mul_assoc, ← PNat.coe_inj ];
    grind;
  simp_all +decide [ ← mul_pow ];
  simpa [ ← PNat.coe_inj ] using congr_arg PNat.val ( h_c_f_mul t u )

/-
PROVIDED SOLUTION
From lb_c_f_mul with u = t: c * f(t²) = f(t) * f(t) = f(t)². So c * f(t²) = f(t)² which means c | f(t)² as natural numbers. For any prime p dividing c, p | f(t)², hence p | f(t). We need to show v_p(f(t)) ≥ v_p(c) for all primes p, which gives c | f(t).

From c * f(t²) = f(t)²: at the level of p-adic valuations:
v_p(c) + v_p(f(t²)) = 2 * v_p(f(t)).
From c * f(t²) = f(t)², replacing t by t²: c * f(t⁴) = f(t²)².
v_p(c) + v_p(f(t⁴)) = 2 * v_p(f(t²)) = 2*(2*v_p(f(t)) - v_p(c)) = 4*v_p(f(t)) - 2*v_p(c).
So v_p(f(t⁴)) = 4*v_p(f(t)) - 3*v_p(c).
In general, v_p(f(t^(2^k))) = 2^k * v_p(f(t)) - (2^k - 1)*v_p(c).
Since v_p(f(t^(2^k))) ≥ 0 for all k, we need 2^k * v_p(f(t)) ≥ (2^k - 1)*v_p(c).
Dividing by 2^k: v_p(f(t)) ≥ (1 - 1/2^k)*v_p(c).
Since this holds for all k and v_p(f(t)) is an integer ≥ v_p(c) * (1 - 1/2^k) for all k, we get v_p(f(t)) ≥ v_p(c).

Alternative simpler approach: from c | f(t)², every prime factor of c divides f(t). Then from c * f(t * u) = f(t) * f(u), and since p | f(t) for all primes p | c, we can bootstrap: from c * f(t²) = f(t)², p^a | f(t)² where p^a || c. Since p | f(t), p^a | f(t)² requires just a ≤ 2*v_p(f(t)). We know v_p(f(t)) ≥ 1, so 2*v_p(f(t)) ≥ 2 ≥ a if a ≤ 2. For a > 2, use the iterated argument above.
-/
lemma lb_c_dvd (f : ℕ+ → ℕ+) (hf : ∀ s t, f (t ^ 2 * f s) = s * (f t) ^ 2)
    (t : ℕ+) : (f 1 : ℕ) ∣ (f t : ℕ) := by
  -- From lb_c_f_mul, we have that $f(1) * f(t*u) = f(t) * f(u)$ for all $t$ and $u$.
  have h_mul : ∀ t u : ℕ+, (f 1 : ℕ) * (f (t * u) : ℕ) = (f t : ℕ) * (f u : ℕ) := by
    have h_mul : ∀ t u : ℕ+, (f 1 : ℕ) * f (t * u) = f t * f u := by
      intro t u
      exact (by
      convert congr_arg PNat.val ( lb_c_f_mul f hf t u ) using 1);
    grind;
  -- By induction on $k$, we can show that $f(1)^{2^k - 1} * f(t^{2^k}) = f(t)^{2^k}$.
  have h_ind : ∀ k : ℕ, (f 1 : ℕ) ^ (2 ^ k - 1) * (f (t ^ (2 ^ k)) : ℕ) = (f t : ℕ) ^ (2 ^ k) := by
    intro k
    induction' k with k ih
    generalize_proofs at *;
    aesop
    generalize_proofs at *; (
    rw [ show ( t ^ 2 ^ ( k + 1 ) ) = ( t ^ 2 ^ k ) * ( t ^ 2 ^ k ) by ring, show ( 2 ^ ( k + 1 ) - 1 : ℕ ) = ( 2 ^ k - 1 ) * 2 + 1 by zify ; norm_num ; ring ] ; simp_all +decide [ pow_add, pow_mul', mul_assoc ] ; ring;
    convert congr_arg ( · ^ 2 ) ih using 1 <;> ring);
  -- Let's choose any prime factor $p$ of $f(1)$.
  by_contra h_not_div;
  -- Let $p$ be a prime factor of $f(1)$ such that $v_p(f(1)) > v_p(f(t))$.
  obtain ⟨p, hp⟩ : ∃ p : ℕ, Nat.Prime p ∧ Nat.factorization (f 1) p > Nat.factorization (f t) p := by
    contrapose! h_not_div;
    exact Nat.factorization_le_iff_dvd ( by positivity ) ( by positivity ) |>.1 fun p => by by_cases hp : Nat.Prime p <;> aesop;
  -- Choose $k$ such that $2^k > \frac{v_p(f(1))}{v_p(f(1)) - v_p(f(t))}$.
  obtain ⟨k, hk⟩ : ∃ k : ℕ, 2 ^ k > (Nat.factorization (f 1) p) / ((Nat.factorization (f 1) p) - (Nat.factorization (f t) p)) := by
    exact pow_unbounded_of_one_lt _ one_lt_two;
  replace h_ind := congr_arg ( fun x => x.factorization p ) ( h_ind k ) ; simp_all +decide [ Nat.factorization_mul, hp.1.ne_zero, hp.1.ne_one ] ;
  rw [ Nat.div_lt_iff_lt_mul ] at hk <;> nlinarith [ Nat.sub_add_cancel ( show 1 ≤ 2 ^ k from Nat.one_le_pow _ _ ( by decide ) ), Nat.sub_add_cancel hp.2.le ]

/-
PROBLEM
The minimum value of a * b^3 * c where a, b, c are distinct primes is 120.

PROVIDED SOLUTION
We have three distinct primes a, b, c. Since they are distinct, the set {a, b, c} contains at least three distinct values from {2, 3, 5, 7, ...}.

Case 1: b = 2. Then a, c are distinct primes different from 2, so a ≥ 3 and c ≥ 3, and one of them ≥ 5. So a * c ≥ 15. Hence a * b³ * c = a * 8 * c ≥ 8 * 15 = 120.

Case 2: b = 3. Then a * b³ * c = 27 * a * c. a, c are distinct primes ≠ 3, so at least {2, 5}. a * c ≥ 10. So 27 * 10 = 270 ≥ 120.

Case 3: b ≥ 5. Then b³ ≥ 125. a * c ≥ 2 * 3 = 6 (smallest distinct primes ≠ b). So a * b³ * c ≥ 6 * 125 = 750 ≥ 120.

Actually, we can also just case split more aggressively using interval_cases or omega on the small prime cases.
-/
lemma three_distinct_primes_bound (a b c : ℕ) (ha : Nat.Prime a) (hb : Nat.Prime b) (hc : Nat.Prime c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) : 120 ≤ a * b ^ 3 * c := by
  rcases a with ( _ | _ | _ | a ) <;> rcases b with ( _ | _ | _ | b ) <;> rcases c with ( _ | _ | _ | c ) <;> simp_all +arith +decide;
  · nlinarith [ sq b, sq c, mul_pos ( Nat.succ_pos b ) ( Nat.succ_pos c ) ];
  · rcases a with ( _ | _ | a ) <;> rcases c with ( _ | _ | c ) <;> (norm_num at * <;> nlinarith;);
  · grind +ring;
  · exact Nat.le_trans ( by decide ) ( Nat.mul_le_mul ( Nat.mul_le_mul ( Nat.succ_le_succ ( Nat.succ_le_succ ( Nat.succ_le_succ ( Nat.zero_le _ ) ) ) ) ( Nat.pow_le_pow_left ( Nat.succ_le_succ ( Nat.succ_le_succ ( Nat.succ_le_succ ( Nat.zero_le _ ) ) ) ) 3 ) ) ( Nat.succ_le_succ ( Nat.succ_le_succ ( Nat.succ_le_succ ( Nat.zero_le _ ) ) ) ) )

/-
PROBLEM
For every f satisfying the equation, f(1998) ≥ 120

PROVIDED SOLUTION
Using the helper lemmas lb_c_f_mul and lb_c_dvd, we can define g(t) = f(t) / f(1) (as a natural number, well-defined since f(1) | f(t)). Then:

1. g is completely multiplicative: g(tu) = g(t)*g(u). From lb_c_f_mul: f(1)*f(tu) = f(t)*f(u). Dividing both sides by f(1)²: f(tu)/f(1) = (f(t)/f(1))*(f(u)/f(1)), i.e., g(tu) = g(t)*g(u).

2. g is an involution: g(g(s)) = s. From lb_ff: f(f(s)) = s*(f 1)². Since f(t) = f(1)*g(t), f(f(s)) = f(1)*g(f(s)) = f(1)*g(f(1)*g(s)) = f(1)*g(f(1))*g(g(s)). And g(f(1)) = f(f(1))/f(1) = (f(1))² / f(1) = f(1) (using lb_ff with s = 1). So f(f(s)) = f(1)*f(1)*g(g(s)) = f(1)²*g(g(s)). Since f(f(s)) = s*f(1)², we get g(g(s)) = s.

3. g maps primes to primes: If p is prime and g(p) = a*b with a,b > 1, then g(g(p)) = g(ab) = g(a)*g(b) = p. Since p is prime, wlog g(a) = 1. But g(1) = f(1)/f(1) = 1, and g is injective (involution), so g(n) = 1 iff n = 1. So a = 1, contradiction.

4. g(2), g(3), g(37) are distinct primes (g injective on primes).

5. f(1998) = f(2*3³*37) = f(1)*g(2*3³*37) = f(1)*g(2)*g(3)³*g(37) (using multiplicativity of g). Actually f(1998) = f(1)*g(1998).

6. Since f(1) ≥ 1 and g(2)*g(3)³*g(37) ≥ 120 (by three_distinct_primes_bound), f(1998) ≥ 120.

The key computation: f(1998) as a PNat has value f(1)*g(1998). g(1998) = g(2)*g(3)³*g(37) ≥ 120 (all in ℕ). And f(1) ≥ 1. So f(1998) ≥ 120.

Work in ℕ for the arithmetic. Use PNat.le_def or cast to ℕ.
-/
lemma f_1998_ge (f : ℕ+ → ℕ+) (hf : ∀ s t, f (t ^ 2 * f s) = s * (f t) ^ 2) :
    (120 : ℕ+) ≤ f 1998 := by
  -- By Lemma 2, we know that $f(1998) = f(1) \cdot g(1998)$ where $g$ is a completely multiplicative involution.
  have h_g : ∃ g : ℕ+ → ℕ+, (∀ s t, g (s * t) = g s * g t) ∧ (∀ s, g (g s) = s) ∧ (∀ s, f s = f 1 * g s) := by
    -- Define g(t) := (f t : ℕ) / (f 1 : ℕ), well-defined by lb_c_dvd.
    have hg_def : ∀ t : ℕ+, ∃ g_t : ℕ+, f t = f 1 * g_t := by
      exact fun t => PNat.dvd_iff.mpr ( lb_c_dvd f hf t );
    choose g hg using hg_def;
    have hg_mul : ∀ s t : ℕ+, g (s * t) = g s * g t := by
      -- From lb_c_f_mul, we have c * f(tu) = f(t) * f(u).
      have h_c_f_mul : ∀ t u : ℕ+, f 1 * f (t * u) = f t * f u := by
        exact?;
      intro s t; specialize h_c_f_mul s t; rw [ hg s, hg t, hg ( s * t ) ] at h_c_f_mul; simp +decide [ mul_assoc, mul_comm, mul_left_comm ] at h_c_f_mul ⊢;
      exact PNat.eq ( by { have := congr_arg PNat.val h_c_f_mul; nlinarith [ PNat.pos ( f 1 * f 1 ) ] } )
    have hg_inv : ∀ s : ℕ+, g (g s) = s := by
      intro s
      have := hf s 1
      simp at this
      have := hg (f s)
      simp [this] at *;
      rw [ hg s ] at ‹f 1 * g ( f s ) = s * f 1 ^ 2›; simp +decide [ sq, mul_assoc, mul_comm, mul_left_comm ] at *;
      rw [ hg_mul ] at this; simp +decide [ ← mul_assoc ] at this;
      rw [ show g ( f 1 ) = f 1 from ?_ ] at this;
      · simpa [ mul_assoc, mul_comm, mul_left_comm ] using this;
      · specialize hg ( f 1 ) ; simp +decide [ ← mul_assoc ] at * ;
        have := hf 1 1; simp_all +decide [ mul_assoc, mul_comm, mul_left_comm ] ;
    use g, hg_mul, hg_inv, hg;
  obtain ⟨ g, hg1, hg2, hg3 ⟩ := h_g;
  -- Since $g$ is a completely multiplicative involution, $g(2)$, $g(3)$, and $g(37)$ are distinct primes.
  have h_distinct_primes : Nat.Prime (g 2) ∧ Nat.Prime (g 3) ∧ Nat.Prime (g 37) ∧ g 2 ≠ g 3 ∧ g 2 ≠ g 37 ∧ g 3 ≠ g 37 := by
    -- Since $g$ is a completely multiplicative involution, $g(p)$ is prime for any prime $p$.
    have h_prime_g : ∀ p : ℕ+, Nat.Prime p → Nat.Prime (g p) := by
      intro p hp
      by_contra h_not_prime
      obtain ⟨a, b, ha, hb, hab⟩ : ∃ a b : ℕ+, 1 < a ∧ 1 < b ∧ g p = a * b := by
        have := Nat.exists_dvd_of_not_prime2 ( show 1 < ( g p : ℕ ) from ?_ ) h_not_prime;
        · obtain ⟨ m, hm₁, hm₂, hm₃ ⟩ := this; exact ⟨ ⟨ m, by linarith ⟩, ⟨ g p / m, Nat.div_pos ( by linarith ) ( by linarith ) ⟩, hm₂, by exact Nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨ by nlinarith [ Nat.div_mul_cancel hm₁ ], by nlinarith [ Nat.div_mul_cancel hm₁ ] ⟩, PNat.eq ( Eq.symm <| Nat.mul_div_cancel' hm₁ ) ⟩ ;
        · by_cases h : g p = 1;
          · have := hg2 p; simp +decide [ h ] at this;
            specialize hg1 1 p; simp +decide [ h, this ] at hg1;
            subst hg1; contradiction;
          · exact mod_cast Ne.bot_lt h;
      have := hg2 p; simp +decide [ hab, hg1 ] at this;
      have := hp.isUnit_or_isUnit ( show ( p : ℕ ) = g a * g b from congr_arg PNat.val this.symm ) ; norm_num at this;
      cases this <;> have := hg2 a <;> have := hg2 b <;> simp_all +singlePass;
    refine' ⟨ h_prime_g 2 Nat.prime_two, h_prime_g 3 Nat.prime_three, h_prime_g 37 ( by norm_num : Nat.Prime 37 ), _, _, _ ⟩ <;> intro h <;> have := hg2 2 <;> have := hg2 3 <;> have := hg2 37 <;> simp_all +singlePass;
  -- Therefore, $f(1998) = f(1) \cdot g(1998) \geq 1 \cdot 120 = 120$.
  have h_f1998_ge_120 : f 1998 = f 1 * (g 2 * g 3 ^ 3 * g 37) := by
    rw [ hg3, show ( 1998 : ℕ+ ) = 2 * 3 * 3 * 3 * 37 by decide, hg1, hg1, hg1, hg1 ] ; ring;
  -- Since $g(2)$, $g(3)$, and $g(37)$ are distinct primes, we have $g(2) * g(3)^3 * g(37) \geq 120$.
  have h_g_prod_ge_120 : (g 2 : ℕ) * (g 3 : ℕ) ^ 3 * (g 37 : ℕ) ≥ 120 := by
    have := three_distinct_primes_bound ( g 2 ) ( g 3 ) ( g 37 ) h_distinct_primes.1 h_distinct_primes.2.1 h_distinct_primes.2.2.1 ( by simpa [ ← PNat.coe_inj ] using h_distinct_primes.2.2.2.1 ) ( by simpa [ ← PNat.coe_inj ] using h_distinct_primes.2.2.2.2.1 ) ( by simpa [ ← PNat.coe_inj ] using h_distinct_primes.2.2.2.2.2 ) ; norm_cast at *;
  exact h_f1998_ge_120.symm ▸ Nat.mul_le_mul ( PNat.one_le _ ) h_g_prod_ge_120

/-! ### Main theorem -/

/-- The least possible value of f(1998) is 120. -/
theorem imo1998_p6 :
    IsLeast {n : ℕ+ | ∃ f : ℕ+ → ℕ+, (∀ s t, f (t ^ 2 * f s) = s * (f t) ^ 2) ∧ f 1998 = n}
      (⟨120, by norm_num⟩ : ℕ+) := by
  constructor
  · exact f_1998_achievable
  · intro n ⟨f, hf, hfn⟩
    rw [← hfn]
    exact f_1998_ge f hf

end Imo1998P6

import Lake
open Lake DSL

package «submission» where
  leanOptions := #[⟨`pp.unicode.fun, true⟩]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib «Submission» where


/-
Copyright (c) 2024 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InternLM-MATH LEAN Formalizer v0.1
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Olympiad 1998, Problem 6

Consider all functions f from the set of all positive integers into itself satisfying
f(t^2f(s)) = sf(t)^2 for all s and t.
Determine the least possible value of f(1998).
-/

namespace Imo1998P6

determine solution : ℕ+ := 120

problem imo1998_p6
    (f : ℕ+ → ℕ+)
    (h : ∀ s t, f (t^2 * f s) = s * (f t)^2) :
    IsLeast {n : ℕ | n = f 1998} solution := by
  sorry


end Imo1998P6
