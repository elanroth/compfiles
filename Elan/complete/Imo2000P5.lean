import Mathlib

namespace Imo2000P5

open Nat Finset

/-! ## Basic helper lemmas -/

/-- If m ∣ a + 1 and p is odd, then m ∣ a^p + 1. -/
lemma dvd_pow_add_one_of_dvd_add_one {a m : ℕ} (h : m ∣ a + 1) {p : ℕ} (hp : Odd p) :
    m ∣ a ^ p + 1 := by
  exact dvd_trans h (by simpa using hp.nat_add_dvd_pow_add_pow a 1)

/-
PROBLEM
If n ∣ 2^n + 1 and p is an odd prime dividing 2^n + 1, then n*p ∣ 2^(n*p) + 1.

PROVIDED SOLUTION
2^(np) + 1 = (2^n + 1) * F where F = (2^n)^{p-1} - (2^n)^{p-2} + ... + 1. The factorization comes from (a+1) | (a^p + 1) for odd p, so (2^n+1) | (2^n)^p + 1 = 2^{np}+1 by Odd.nat_add_dvd_pow_add_pow.

We have n | (2^n + 1) [given]. We need to show p | F.

Since p | 2^n + 1, in ZMod p we have (2^n : ZMod p) = -1. The quotient F = ((2^n)^p + 1) / (2^n + 1). Working in ZMod p: (2^n)^p + 1 = (-1)^p + 1 = -1 + 1 = 0, and 2^n + 1 = 0. The alternating sum F = (2^n)^{p-1} - (2^n)^{p-2} + ... + 1 ≡ (-1)^{p-1} - (-1)^{p-2} + ... + 1 = 1+1+...+1 = p ≡ 0 (mod p). So p | F.

Since n | (2^n+1) and p | F, by Nat.mul_dvd_mul we get n*p | (2^n+1)*F = 2^{np}+1.

Alternatively, more directly: n | 2^{np}+1 by dvd_pow_add_one_of_dvd_add_one (since n | 2^n+1 and p is odd). And p | 2^{np}+1 by dvd_pow_add_one_of_dvd_add_one (since p | 2^n+1 and p is odd). But this only gives lcm(n,p) | 2^{np}+1, not n*p.

The cleaner approach uses Nat.mul_dvd_mul: n ∣ (2^n+1), p ∣ F, so n*p ∣ (2^n+1)*F = 2^{np}+1.
-/
lemma extend_divisibility {n : ℕ} (hn : n ∣ 2 ^ n + 1) (p : ℕ) (hp : Nat.Prime p)
    (hpodd : p ≠ 2) (hpdvd : p ∣ 2 ^ n + 1) :
    n * p ∣ 2 ^ (n * p) + 1 := by
  -- We have n | (2^n + 1) [given]. We need to show p | (2^n)^{p-1} - (2^n)^{p-2} + ... + 1.
  have h_even : ∃ k : ℕ, 2 ^ (n * p) + 1 = (2 ^ n + 1) * (∑ i ∈ Finset.range p, (-1 : ℤ) ^ i * (2 ^ n) ^ i) := by
    rcases Nat.even_or_odd' p with ⟨ c, rfl | rfl ⟩ <;> norm_num [ pow_add, pow_mul, ← mul_pow ] at *;
    · simp_all +decide [ Nat.prime_mul_iff ];
    · have := geom_sum_mul_neg ( -2 ^ n : ℤ ) ( 2 * c + 1 ) ; ring_nf at * ; aesop;
  -- Since $p$ is an odd prime, we know that $p \mid \sum_{i=0}^{p-1} (-1)^i (2^n)^i$.
  have h_div : (p : ℤ) ∣ ∑ i ∈ Finset.range p, (-1 : ℤ) ^ i * (2 ^ n) ^ i := by
    haveI := Fact.mk hp; simp_all +decide [ ← ZMod.intCast_zmod_eq_zero_iff_dvd ] ;
    simp_all +decide [ ← ZMod.natCast_eq_zero_iff ];
    simp_all +decide [ ← mul_pow, add_eq_zero_iff_eq_neg ];
  -- Therefore, $n * p \mid (2^n + 1) * (∑ i ∈ Finset.range p, (-1 : ℤ) ^ i * (2 ^ n) ^ i)$.
  have h.mul_dvd : (n * p : ℤ) ∣ (2 ^ n + 1) * (∑ i ∈ Finset.range p, (-1 : ℤ) ^ i * (2 ^ n) ^ i) := by
    exact mul_dvd_mul ( mod_cast hn ) h_div;
  exact_mod_cast h_even.choose_spec.symm ▸ h.mul_dvd

/-- n < 2^n + 1 for all n. -/
lemma two_pow_add_one_gt (n : ℕ) : n < 2 ^ n + 1 := by
  have : n < 2 ^ n := Nat.lt_two_pow_self
  omega

/-- 2^n + 1 is odd for n ≥ 1. -/
lemma two_pow_add_one_odd {n : ℕ} (hn : 0 < n) : ¬ 2 ∣ (2 ^ n + 1) := by
  intro ⟨k, hk⟩
  have h2 : 2 ∣ 2 ^ n := dvd_pow_self 2 hn.ne'
  omega

/-! ## Key number-theoretic lemmas for the inductive step -/

/-
PROBLEM
For n ≥ 3 and q ≥ 3, we have 2^(n*q) + 1 > q * (2^n + 1).

PROVIDED SOLUTION
For n ≥ 3, q ≥ 3: we need q * (2^n + 1) < 2^(n*q) + 1.

Since q ≤ 2^n + 1 (as q is at most 2^n+1, but we don't need this), we have:
q * (2^n + 1) ≤ (2^n + 1)^2 ≤ (2^(n+1))^2 = 2^(2n+2).

And 2^(n*q) ≥ 2^(n*3) = 2^(3n). Since n ≥ 3: 3n ≥ 9 and 2n+2 ≤ 8 < 9 ≤ 3n. So 2^(3n) > 2^(2n+2).

More precisely: n*q ≥ 3*3 = 9. And q*(2^n+1) ≤ q*2^(n+1) (since 2^n+1 ≤ 2^(n+1) for n ≥ 1). Also q ≤ 2^q (for q ≥ 1). So q*2^(n+1) ≤ 2^q * 2^(n+1) = 2^(q+n+1). We need 2^(q+n+1) < 2^(nq), i.e., q+n+1 < nq, i.e., nq - n - q > 1, i.e., (n-1)(q-1) > 2. For n ≥ 3, q ≥ 3: (n-1)(q-1) ≥ 4 > 2. ✓

So 2^(nq) > q * 2^(n+1) ≥ q*(2^n+1), hence 2^(nq)+1 > q*(2^n+1).
-/
lemma pow_mul_gt (n q : ℕ) (hn : 3 ≤ n) (hq : 3 ≤ q) :
    q * (2 ^ n + 1) < 2 ^ (n * q) + 1 := by
  -- Since $2^n + 1 \leq 2^{n+1}$, we have $q * (2^n + 1) \leq q * 2^{n+1}$.
  have h_ineq : q * (2 ^ n + 1) ≤ q * 2 ^ (n + 1) := by
    exact Nat.mul_le_mul_left _ ( by ring_nf; linarith [ Nat.pow_le_pow_right two_pos hn ] );
  -- Since $q \leq 2^q$, we have $q * 2^{n+1} \leq 2^q * 2^{n+1} = 2^{q+n+1}$.
  have h_ineq2 : q * 2 ^ (n + 1) ≤ 2 ^ (q + n + 1) := by
    ring_nf at *;
    gcongr ; linarith [ show q ≤ 2 ^ q by exact le_of_lt ( Nat.recOn q ( by norm_num ) fun n ihn => by rw [ pow_succ' ] ; linarith [ Nat.one_le_pow n 2 zero_lt_two ] ) ] ;
  refine lt_of_le_of_lt h_ineq ( lt_of_le_of_lt h_ineq2 ?_ );
  exact Nat.lt_succ_of_le ( pow_le_pow_right₀ ( by decide ) ( by nlinarith ) )

/-
PROBLEM
For an odd prime p dividing 2^n + 1 with p ≠ q (another odd prime),
    p does not divide (2^(n*q)+1)/(2^n+1).

PROVIDED SOLUTION
Let Φ = (2^(n*q)+1)/(2^n+1). We need ¬ p ∣ Φ.

Since p | 2^n + 1, in ZMod p we have (2^n : ZMod p) = -1.
Φ = (2^n)^{q-1} - (2^n)^{q-2} + ... + 1 (the alternating geometric sum).
In ZMod p: each (2^n)^j = (-1)^j. So the alternating sum with signs:
Φ ≡ (-1)^{q-1} - (-1)^{q-2} + ... + (-1)^0 · 1 = 1 + 1 + ... + 1 = q (mod p).
(Each term contributes 1 because (-1)^j · (-1)^{...} = 1.)

Since p ≠ q and both are primes, p ∤ q. So Φ ≡ q ≢ 0 (mod p), hence p ∤ Φ.

More precisely: Φ ≡ q (mod p). The cast of q to ZMod p is nonzero because p ∤ q (since p and q are distinct primes). So (Φ : ZMod p) ≠ 0, hence p ∤ Φ.

For the computation of Φ in ZMod p: use that 2^(n*q)+1 = (2^n+1) * Φ, and (2^n+1 : ZMod p) = 0. So computing Φ mod p requires the alternating sum formula or use geom_sum₂. Alternatively, work with the formula directly:

(2^n)^q + 1 = (2^n + 1) * Σ_{i=0}^{q-1} (-1)^i * (2^n)^{q-1-i}

So Φ = Σ_{i=0}^{q-1} (-1)^i * (2^n)^{q-1-i}.
In ZMod p: (2^n) = -1, so (2^n)^{q-1-i} = (-1)^{q-1-i}.
(-1)^i * (-1)^{q-1-i} = (-1)^{q-1} = 1 (since q-1 is even for odd prime q).
Sum = q * 1 = q.

So (Φ : ZMod p) = (q : ZMod p). Since p ≠ q primes, (q : ZMod p) ≠ 0, so (Φ : ZMod p) ≠ 0, hence p ∤ Φ.
-/
lemma quotient_not_dvd_of_ne {n q : ℕ} {p : ℕ} (hp : Nat.Prime p) (hpodd : p ≠ 2)
    (hq_prime : Nat.Prime q) (hq_odd : q ≠ 2)
    (hpq : p ≠ q) (hpdvd : p ∣ 2 ^ n + 1) (hdvd : (2 ^ n + 1) ∣ (2 ^ (n * q) + 1)) :
    ¬ p ∣ (2 ^ (n * q) + 1) / (2 ^ n + 1) := by
  -- Therefore, $\Phi_q(2^n) \equiv q \pmod{p}$.
  have h_phi : (2 ^ (n * q) + 1) / (2 ^ n + 1) ≡ q [ZMOD p] := by
    have h_phi : (∑ i ∈ Finset.range q, (-1 : ℤ) ^ i * (2 ^ n) ^ (q - 1 - i)) ≡ q [ZMOD p] := by
      have h_phi : (∑ i ∈ Finset.range q, (-1 : ℤ) ^ i * (2 ^ n) ^ (q - 1 - i)) ≡ (∑ i ∈ Finset.range q, (-1 : ℤ) ^ i * (-1) ^ (q - 1 - i)) [ZMOD p] := by
        exact Int.ModEq.sum fun i hi => Int.ModEq.mul_left _ <| Int.ModEq.pow _ <| Int.ModEq.symm <| Int.modEq_of_dvd <| by simpa [ ← Int.natCast_dvd_natCast ] using hpdvd;
      convert h_phi using 1;
      simp +decide [ ← pow_add, add_comm, ← Finset.sum_range_reflect ];
      cases hq_prime.eq_two_or_odd' <;> simp_all +decide [ Nat.even_sub hq_prime.pos ];
    convert h_phi using 1;
    rw [ Int.ediv_eq_of_eq_mul_right ] <;> norm_cast ; norm_num [ pow_mul ];
    have := geom_sum₂_mul ( -1 : ℤ ) ( 2 ^ n ) q; simp_all +decide [ mul_comm, pow_add ] ;
    linarith [ show ( -1 : ℤ ) ^ q = -1 from by rw [ neg_one_pow_eq_pow_mod_two ] ; norm_num [ hq_prime.eq_two_or_odd.resolve_left hq_odd ] ];
  rw [ ← Int.natCast_dvd_natCast ] ; simp_all +decide [ Int.ModEq ] ;
  exact fun h => hpq <| by have := Int.dvd_of_emod_eq_zero ( h_phi.symm.trans <| Int.emod_eq_zero_of_dvd h ) ; norm_cast at this; have := Nat.prime_dvd_prime_iff_eq hp hq_prime; tauto;

/-
PROBLEM
The q-adic valuation of (2^(n*q)+1)/(2^n+1) is exactly 1, when q is an odd prime
    dividing 2^n+1. This follows from the LTE.

PROVIDED SOLUTION
By the Lifting the Exponent Lemma (Nat.emultiplicity_pow_add_pow in Mathlib):
emultiplicity q ((2^n)^q + 1^q) = emultiplicity q (2^n + 1) + emultiplicity q q.

Since q is prime: emultiplicity q q = 1 (by Nat.Prime.emultiplicity_self).
And (2^n)^q + 1 = 2^(n*q) + 1 (by pow_mul).

So emultiplicity q (2^(n*q) + 1) = emultiplicity q (2^n + 1) + 1.

Now (2^n + 1) | (2^(n*q) + 1), so let Φ = (2^(n*q)+1)/(2^n+1).
2^(n*q)+1 = (2^n+1) * Φ.

By emultiplicity_mul (for positive values):
emultiplicity q ((2^n+1) * Φ) = emultiplicity q (2^n+1) + emultiplicity q Φ.

So emultiplicity q (2^n+1) + emultiplicity q Φ = emultiplicity q (2^n+1) + 1.
Therefore emultiplicity q Φ = 1.

Key conditions for Nat.emultiplicity_pow_add_pow:
- q is a Nat.Prime: given by hq_prime
- Odd q: follows from hq_prime and hq_odd (q ≠ 2)
- q | (2^n + 1): given by hqdvd (note: 2^n + 1 = 2^n + 1^1, so x = 2^n, y = 1, and q | x + y)
- ¬q | x = ¬q | 2^n: since q is odd (q ≥ 3), q does not divide 2^n (a power of 2)
- Odd q (as the exponent): q is odd, given
-/
lemma quotient_val_q {n q : ℕ} (hq_prime : Nat.Prime q) (hq_odd : q ≠ 2)
    (hqdvd : q ∣ 2 ^ n + 1) (hn_pos : 0 < n)
    (hdvd : (2 ^ n + 1) ∣ (2 ^ (n * q) + 1)) :
    emultiplicity q ((2 ^ (n * q) + 1) / (2 ^ n + 1)) = 1 := by
  have h_emultiplicity : emultiplicity q (2 ^ (n * q) + 1) = emultiplicity q (2 ^ n + 1) + 1 := by
    have h_emultiplicity_pow : emultiplicity q ((2 ^ n) ^ q + 1 ^ q) = emultiplicity q (2 ^ n + 1) + emultiplicity q q := by
      apply_rules [ Nat.emultiplicity_pow_add_pow ];
      · exact hq_prime.odd_of_ne_two hq_odd;
      · exact mt hq_prime.dvd_of_dvd_pow <| Nat.not_dvd_of_pos_of_lt Nat.zero_lt_two <| lt_of_le_of_ne hq_prime.two_le <| Ne.symm hq_odd;
      · exact hq_prime.odd_of_ne_two hq_odd;
    simp_all +decide [ pow_mul ];
    rw [ Nat.Prime.emultiplicity_self hq_prime ];
  -- Using emultiplicity_mul, we can split the emultiplicity of the product into the sum of the emultiplicities.
  have h_emultiplicity_mul : emultiplicity q (2 ^ (n * q) + 1) = emultiplicity q (2 ^ n + 1) + emultiplicity q ((2 ^ (n * q) + 1) / (2 ^ n + 1)) := by
    rw [ ← emultiplicity_mul, Nat.mul_div_cancel' hdvd ];
    exact Nat.prime_iff.mp hq_prime;
  simp_all +decide [ emultiplicity ];
  split_ifs at * <;> norm_cast at *;
  · grind;
  · simp_all +decide [ FiniteMultiplicity ];
    rename_i h₁ h₂; specialize h₂ ( Nat.log q ( 2 ^ n + 1 ) ) ; exact absurd h₂ ( Nat.not_dvd_of_pos_of_lt ( by positivity ) ( Nat.lt_pow_succ_log_self hq_prime.one_lt _ ) ) ;
  · simp_all +decide [ FiniteMultiplicity, Nat.finiteMultiplicity_iff ]

/-
PROBLEM
Core lemma: For n ≥ 3 and q an odd prime dividing 2^n + 1,
    the number 2^(n*q) + 1 has a prime factor not dividing 2^n + 1.

PROVIDED SOLUTION
Let Φ = (2^(n*q)+1)/(2^n+1). We have (2^n+1) | (2^(n*q)+1) by Odd.nat_add_dvd_pow_add_pow (since q is odd). Φ > 0 and in fact Φ > q by pow_mul_gt (since n ≥ 3 and q ≥ 3).

By quotient_not_dvd_of_ne: for all primes p ≠ q with p | 2^n+1, we have p ∤ Φ.
By quotient_val_q: emultiplicity q Φ = 1, meaning q | Φ and q^2 ∤ Φ.

So Φ = q * m where m = Φ/q and gcd(m, q) = 1 (since q^2 ∤ Φ). And for all primes p | 2^n+1 with p ≠ q: p ∤ Φ, so p ∤ m.

So m is coprime to every prime dividing 2^n+1.

Since Φ > q, m = Φ/q ≥ 2. So m has a prime factor r. r ∤ 2^n+1 (since m is coprime to 2^n+1). And r | m | Φ | 2^(n*q)+1.

So r is our desired prime: r is prime, r | 2^(n*q)+1, and ¬ r | (2^n+1).

To summarize the proof:
1. hdvd: (2^n+1) | (2^(n*q)+1) from Odd.nat_add_dvd_pow_add_pow.
2. Φ = (2^(n*q)+1)/(2^n+1) > q from pow_mul_gt. So Φ/q ≥ 2.
3. q | Φ (from quotient_val_q, emultiplicity is ≥ 1).
4. For the prime r: any prime factor of Φ/q works.
   If r | 2^n+1, then either r = q or r ≠ q.
   If r = q: r | Φ/q implies q^2 | Φ, contradicting emultiplicity q Φ = 1.
   If r ≠ q: r | Φ contradicts quotient_not_dvd_of_ne.
   So r ∤ 2^n+1. ✓

Use Nat.exists_prime_and_dvd to find a prime factor of Φ/q (which is ≥ 2).
-/
lemma exists_new_prime_factor {n q : ℕ} (hn : 3 ≤ n)
    (hq_prime : Nat.Prime q) (hq_odd : q ≠ 2)
    (hqdvd : q ∣ 2 ^ n + 1) :
    ∃ r, Nat.Prime r ∧ r ∣ 2 ^ (n * q) + 1 ∧ ¬ r ∣ (2 ^ n + 1) := by
  -- Let Φ = (2^(n*q)+1)/(2^n+1). We have (2^n+1) | (2^(n*q)+1) by Odd.nat_add_dvd_pow_add_pow (since q is odd). Φ > 0 and in fact Φ > q by pow_mul_gt (since n ≥ 3 and q ≥ 3).
  set Φ := (2 ^ (n * q) + 1) / (2 ^ n + 1) with hΦ_def
  have hΦ_pos : 0 < Φ := by
    norm_num +zetaDelta at *;
    exact pow_le_pow_right₀ ( by decide ) ( by nlinarith [ hq_prime.two_le ] )
  have hΦ_gt_q : Φ > q := by
    refine' Nat.le_div_iff_mul_le ( Nat.succ_pos _ ) |>.2 _;
    rw [ pow_mul ];
    rcases q with ( _ | _ | q ) <;> simp_all +decide [ pow_succ ];
    nlinarith [ Nat.mul_le_mul_left ( 2 ^ n ) ( show ( 2 ^ n ) ^ q ≥ q + 1 from Nat.recOn q ( by norm_num ) fun q ih => by rw [ pow_succ' ] ; nlinarith [ Nat.pow_le_pow_right ( show 1 ≤ 2 by norm_num ) hn ] ), Nat.pow_le_pow_right ( show 1 ≤ 2 by norm_num ) hn, Nat.mul_le_mul_left ( 2 ^ n ) ( show ( 2 ^ n ) ^ q ≥ 1 from Nat.one_le_pow _ _ ( by norm_num ) ) ]
  have hΦ_dvd : (2 ^ n + 1) * Φ = 2 ^ (n * q) + 1 := by
    rw [ Nat.mul_div_cancel' ] ; exact_mod_cast by have := Nat.odd_iff.mpr ( show ( q : ℕ ) % 2 = 1 from hq_prime.eq_two_or_odd.resolve_left hq_odd ) ; simpa [ *, Nat.pow_mul ] using this.nat_add_dvd_pow_add_pow _ 1;
  -- By quotient_not_dvd_of_ne: for all primes p ≠ q with p | 2^n+1, we have p ∤ Φ.
  have h_not_dvd : ∀ p : ℕ, Nat.Prime p → p ≠ q → p ∣ 2 ^ n + 1 → ¬ p ∣ Φ := by
    intros p hp hpq hpdiv hpdivΦ
    apply quotient_not_dvd_of_ne hp (by
    rintro rfl; simp_all +decide [ ← even_iff_two_dvd, parity_simps ] ;) hq_prime hq_odd hpq hpdiv (by
    exact hΦ_dvd ▸ dvd_mul_right _ _) hpdivΦ;
  -- By quotient_val_q: emultiplicity q Φ = 1, meaning q | Φ and q^2 ∤ Φ.
  have h_emultiplicity_q : emultiplicity q Φ = 1 := by
    apply quotient_val_q hq_prime hq_odd hqdvd (by linarith) (by
    exact dvd_of_mul_right_eq _ hΦ_dvd);
  -- So Φ = q * m where m = Φ/q and gcd(m, q) = 1 (since q^2 ∤ Φ). And for all primes p | 2^n+1 with p ≠ q: p ∤ Φ, so p ∤ m.
  obtain ⟨m, hm⟩ : ∃ m : ℕ, Φ = q * m ∧ ¬ q ∣ m := by
    have h_emultiplicity_q : q ^ 1 ∣ Φ ∧ ¬ q ^ 2 ∣ Φ := by
      simp_all +decide [ emultiplicity ];
      split_ifs at h_emultiplicity_q <;> simp_all +decide [ Nat.find_eq_iff ];
    exact Exists.elim h_emultiplicity_q.1 fun m hm => ⟨ m, by linarith, fun hm' => h_emultiplicity_q.2 <| by exact hm.symm ▸ mul_dvd_mul_left _ hm' ⟩;
  -- So m is coprime to every prime dividing 2^n+1.
  have h_coprime : ∀ p : ℕ, Nat.Prime p → p ∣ 2 ^ n + 1 → ¬ p ∣ m := by
    intro p pp dp; specialize h_not_dvd p pp; by_cases hpq : p = q <;> simp_all +decide [ Nat.Prime.dvd_mul ] ;
    exact fun h => h_not_dvd <| hΦ_def ▸ dvd_mul_of_dvd_right h _;
  -- Since Φ > q, m = Φ/q ≥ 2. So m has a prime factor r.
  obtain ⟨r, hr⟩ : ∃ r : ℕ, Nat.Prime r ∧ r ∣ m := by
    exact Nat.exists_prime_and_dvd ( by nlinarith [ hq_prime.two_le ] );
  exact ⟨ r, hr.1, dvd_trans hr.2 ( hm.1.symm ▸ dvd_mul_left _ _ ) |> fun x => x.trans ( hΦ_dvd ▸ dvd_mul_left _ _ ), fun h => h_coprime r hr.1 h hr.2 ⟩

/-! ## Main inductive argument -/

/-
PROBLEM
For n ≥ 1 with n ∣ 2^n + 1, there exists m > 0 with m ∣ 2^m + 1
    and m.primeFactors.card > n.primeFactors.card.

PROVIDED SOLUTION
Case analysis on n.

**Case n = 1**: Take m = 3. Check: 3 | 2^3 + 1 = 9 (by norm_num). primeFactors(3).card = 1 > 0 = primeFactors(1).card (since primeFactors(1) = ∅).

**Case n = 2**: Impossible since 2 ∤ 2^2 + 1 = 5. (n | 2^n+1 and 2^n+1 is odd for n ≥ 1, so n must be odd, hence n ≠ 2.)

**Case n ≥ 3**: n is odd (since n | 2^n+1 and 2^n+1 is odd).
Since 2^n+1 > n (by two_pow_add_one_gt), (2^n+1)/n ≥ 2. So (2^n+1)/n ≠ 1, hence it has a prime factor q (by Nat.exists_prime_and_dvd). q | (2^n+1)/n, so q | 2^n+1. Since 2^n+1 is odd, q ≠ 2.

**Sub-case q ∤ n**: Take m = n * q.
By extend_divisibility: m | 2^m + 1. m > 0 since n > 0 and q > 0.
primeFactors(n*q) = primeFactors(n) ∪ {q}. Since q ∤ n, q ∉ primeFactors(n). So card increases.
More precisely: since q is prime and q ∤ n, q ∈ primeFactors(n*q) but q ∉ primeFactors(n), so primeFactors(n*q).card > primeFactors(n).card. Use Nat.primeFactors_mul and the fact that for coprime n and q (q prime, q ∤ n), primeFactors(n*q) = primeFactors(n) ∪ primeFactors(q) = primeFactors(n) ∪ {q}.

**Sub-case q | n**: We have n ≥ 3 and q ≥ 3.
By exists_new_prime_factor: ∃ r prime, r | 2^(n*q)+1, ¬ r | (2^n+1).
Since n | 2^n+1 and r ∤ 2^n+1: r ∤ n.

Set n' = n * q. By extend_divisibility: n' | 2^{n'}+1.
Since r | 2^(n*q)+1 = 2^{n'}+1 and r ∤ n: r ∤ n' (because all prime factors of n' = n*q are prime factors of n, since q | n, so primeFactors(n') ⊆ primeFactors(n); and r is a prime not dividing n, hence not in primeFactors(n), hence not in primeFactors(n')).

Wait, primeFactors(n') = primeFactors(n*q). Since q | n, primeFactors(n*q) = primeFactors(n) (since q is already a prime factor of n).

r is prime, r ∤ 2^n+1. Since 2^{n'}+1 is odd (n' = n*q ≥ 9 > 0), r ≠ 2. r | 2^{n'}+1 and r is an odd prime. r ∤ n' (since r ∤ n and primeFactors(n') = primeFactors(n)).

Take m = n' * r. By extend_divisibility applied to n' (n' | 2^{n'}+1) and r (r is odd prime, r | 2^{n'}+1): m | 2^m+1.

primeFactors(m) = primeFactors(n' * r) ⊇ primeFactors(n') ∪ {r} = primeFactors(n) ∪ {r}. Since r ∉ primeFactors(n), card increases.
-/
lemma increase_prime_factors (n : ℕ) (hn : 0 < n) (hd : n ∣ 2 ^ n + 1) :
    ∃ m, 0 < m ∧ m ∣ 2 ^ m + 1 ∧ n.primeFactors.card < m.primeFactors.card := by
  by_cases hn3 : n ≥ 3;
  · obtain ⟨q, hq_prime, hq_odd, hqdvd⟩ : ∃ q, Nat.Prime q ∧ q ∣ 2 ^ n + 1 ∧ q ≠ 2 := by
      exact ⟨ Nat.minFac ( 2 ^ n + 1 ), Nat.minFac_prime ( by norm_num ), Nat.minFac_dvd _, fun h => by simp_all +decide [ ← even_iff_two_dvd, parity_simps ] ⟩;
    by_cases hq : q ∣ n <;> simp_all +decide [ Nat.primeFactors_mul ];
    · -- By exists_new_prime_factor, there exists a prime $r$ such that $r \mid 2^{n*q} + 1$ and $r \nmid 2^n + 1$.
      obtain ⟨r, hr_prime, hr_dvd⟩ : ∃ r, Nat.Prime r ∧ r ∣ 2 ^ (n * q) + 1 ∧ ¬ r ∣ (2 ^ n + 1) := by
        apply exists_new_prime_factor hn3 hq_prime hqdvd hq_odd;
      -- Set $n' = n * q$ and $m = n' * r$.
      set n' := n * q
      set m := n' * r
      use m
      have hm_pos : 0 < m := by
        exact Nat.mul_pos ( Nat.mul_pos hn hq_prime.pos ) hr_prime.pos
      have hm_div : m ∣ 2 ^ m + 1 := by
        apply_rules [ extend_divisibility ];
        · rintro rfl; simp_all +decide [ ← even_iff_two_dvd, parity_simps ] ;
          aesop;
        · exact hr_dvd.1
      have hm_prime_factors : m.primeFactors = n.primeFactors ∪ {r} := by
        rw [ Nat.primeFactors_mul, Nat.primeFactors_mul ] <;> aesop
      have hm_card : m.primeFactors.card > n.primeFactors.card := by
        -- Since $r$ is not in $n$'s prime factors, the cardinality of the union is the sum of the cardinalities of $n$'s prime factors and $\{r\}$.
        have hr_not_in_n : r∉n.primeFactors := by
          exact fun h => hr_dvd.2 <| dvd_trans ( Nat.dvd_of_mem_primeFactors h ) hd |> fun x => by simpa [ ← ZMod.natCast_eq_zero_iff ] using x;
        exact (by
        grind)
      exact ⟨hm_pos, hm_div, hm_card⟩;
    · refine' ⟨ n * q, Nat.mul_pos hn hq_prime.pos, _, _ ⟩;
      · convert extend_divisibility hd q hq_prime hqdvd hq_odd using 1;
      · rw [ Nat.primeFactors_mul ] <;> aesop;
  · interval_cases n <;> simp_all +decide;
    exists 3

/-
PROBLEM
For every k, there exists a positive n with exactly k distinct prime factors
    and n ∣ 2^n + 1.

PROVIDED SOLUTION
By strong induction on k.

Base case k = 0: Take n = 1. 0 < 1, primeFactors(1) = ∅ so card = 0, and 1 ∣ 2^1 + 1 = 3 (trivially). ✓

Inductive step: Assume the result holds for all j < k+1, in particular for j = k.
By IH, ∃ n₀ > 0 with n₀.primeFactors.card = k and n₀ ∣ 2^n₀ + 1.
By increase_prime_factors applied to n₀: ∃ m > 0 with m ∣ 2^m + 1 and m.primeFactors.card > k.

But we need card = k+1 exactly, not just > k. We need to be more careful.

Actually, increase_prime_factors gives card(m) > card(n₀) = k. So card(m) ≥ k+1.

But card(m) might be > k+1. We need to find an n with card exactly k+1.

To handle this: if card(m) = k+1, we're done. If card(m) > k+1, we can take a divisor of m with exactly k+1 prime factors.

Actually, let me think again. From the proof of increase_prime_factors, in most cases card(m) = k+1 (we add exactly one new prime factor). So card(m) = card(n₀) + 1 = k + 1. Let me check...

In the proof:
- Case n=1: m=3, card(3)=1 = 0+1. ✓
- Case q ∤ n: m = n*q, primeFactors(m) = primeFactors(n) ∪ {q}, card = k+1 (since q ∉ primeFactors(n)). ✓
- Case q | n: m = n*q*r, primeFactors(m) = primeFactors(n*q) ∪ {r} = primeFactors(n) ∪ {r} (since q | n), card = k+1 (since r ∉ primeFactors(n)). Wait, but primeFactors(n*q) might not equal primeFactors(n) if n*q has different factors. Actually q | n, so primeFactors(n*q) = primeFactors(n). And primeFactors(n*q*r) = primeFactors(n*q) ∪ {r} = primeFactors(n) ∪ {r}. So card = k+1. ✓

Hmm, but increase_prime_factors doesn't guarantee card = k+1, only card > k. The proof above shows it's actually k+1, but the STATEMENT of increase_prime_factors only says >.

So for the induction, I need: ∃ m with card(m) > k. Then card(m) ≥ k+1.

But I need card(m) = k+1 exactly. I can achieve this by taking a suitable divisor of m.

Actually, here's a cleaner approach: instead of using increase_prime_factors (which gives card > k), use it to get some m₁ with card ≥ k+1 and m₁ | 2^{m₁}+1. Then if card = k+1, done. If card > k+1, take a prime factor p of m₁, and consider m₁/p^{v_p(m₁)}. This has one fewer prime factor. Hmm, but m₁/p^{v_p(m₁)} might not divide 2^{m₁/p^{v_p(m₁)}}+1.

This is a problem. The divisibility n | 2^n+1 is very special and not preserved under taking arbitrary divisors.

So the induction argument needs to be more careful. Let me reconsider.

Actually, looking at my proof of increase_prime_factors more carefully, the proof DOES give card(m) = card(n)+1 in all cases. So I should strengthen the statement of increase_prime_factors to say card(m) = card(n)+1 instead of card(m) > card(n). OR, I should prove the induction differently.

Let me just prove exists_dvd_two_pow_add_one by induction on k, using increase_prime_factors. The IH gives n with card = k. increase_prime_factors gives m with card > k. I need card = k+1.

Hmm, but increase_prime_factors gives card > k which means card ≥ k+1. Card might be k+2 or more.

BUT looking at the actual proof: the m constructed always has card = k+1. The issue is just the statement of increase_prime_factors.

Let me STRENGTHEN increase_prime_factors or add a new lemma.

Actually, I'll just prove a stronger version inline:

Lemma: For n > 0 with n | 2^n+1, ∃ m > 0, m | 2^m+1, n | m, ∃ r prime, r | m, ¬ r | n.

From this: primeFactors(n) ⊆ primeFactors(m) (since n | m) and r ∈ primeFactors(m) \ primeFactors(n). But card(m) could still be more than card(n)+1 because m might introduce multiple new primes.

Hmm, but in the construction: m = n*q (Case 1) or m = n*q*r (Case 2, where q | n). In Case 1, primeFactors(m) = primeFactors(n) ∪ {q}, card = k+1. In Case 2, primeFactors(m) = primeFactors(n*q) ∪ {r} = primeFactors(n) ∪ {r} (since q | n), card = k+1.

So in BOTH cases, card(m) = card(n) + 1.

But the STATEMENT of increase_prime_factors only says card(m) > card(n). This is a flaw.

Let me add a stronger version or modify the proof. Actually, the simplest fix: just use the fact that card(m) ≥ card(n)+1 from increase_prime_factors, and then find a divisor m' of m with card = card(n)+1 and m' | 2^{m'}+1.

But as I noted, divisibility isn't preserved. So I can't take arbitrary divisors.

However, I CAN take m' = n * r where r is a new prime (one that doesn't divide n). Then card(m') = card(n) + 1 and m' | 2^{m'}+1 (by extend_divisibility, since n | 2^n+1 and r | 2^n+1 and r is odd).

Wait, but r | 2^n+1 or r | 2^{n'}+1 (where n' = n*q)? In the construction, r | 2^{n*q}+1, not necessarily r | 2^n+1.

Hmm, so m' = n*r doesn't necessarily work because r might not divide 2^n+1.

OK let me take a different approach. I'll prove that increase_prime_factors gives card = k+1 exactly, not just > k.

Actually, the simplest approach: prove by induction using increase_prime_factors, and note that for a natural number, card ≥ k+1 and card ≤ something... Actually I just need to show ∃ m with card = k+1, and I have ∃ m with card ≥ k+1.

Given m with card ≥ k+1 and m | 2^m+1, I can repeatedly apply the following: if card(m) > k+1, remove a prime from m. But I can't just remove primes from m because the divisibility might not be preserved.

OK, I think the cleanest fix is to change the statement of increase_prime_factors to guarantee card = card(n) + 1. But I already proved it... Let me just add a new lemma `increase_by_one` that gives the exact increment.

OR: I can do the induction DIFFERENTLY. Instead of induction on k with IH for k, use strong induction and the fact that increase_prime_factors gives card ≥ k+1. Then I have m with card ≥ k+1 and m | 2^m+1. If card = k+1, done. If card > k+1... hmm, I'm stuck.

Actually, wait. The proof of increase_prime_factors I have constructs m with EXACTLY one more prime factor. So the card is exactly card(n)+1. But the LEAN PROOF might not establish this rigorously - it just shows card(m) > card(n).

Let me check what the Lean proof actually proves. Let me look at the proof...

Actually, let me just TRY the subagent on exists_dvd_two_pow_add_one with the induction using increase_prime_factors. Maybe the subagent can handle the gap.
-/
theorem exists_dvd_two_pow_add_one (k : ℕ) :
    ∃ n : ℕ, 0 < n ∧ n.primeFactors.card = k ∧ n ∣ 2 ^ n + 1 := by
  induction' k using Nat.strong_induction_on with k ih;
  by_cases hk : k = 0 ∨ k = 1;
  · cases hk <;> [ exact ⟨ 1, by norm_num, by norm_num [ ‹k = 0› ], by norm_num [ ‹k = 0› ] ⟩ ; exact ⟨ 3, by norm_num, by norm_num [ ‹k = 1› ], by norm_num [ ‹k = 1› ] ⟩ ];
  · obtain ⟨ n, hn₁, hn₂, hn₃ ⟩ := ih ( k - 1 ) ( Nat.sub_lt ( Nat.pos_of_ne_zero ( by tauto ) ) zero_lt_one ) ; rcases k with ( _ | _ | k ) <;> simp_all +decide [ Nat.primeFactors_mul ];
    -- Let $q$ be a prime factor of $(2^n + 1) / n$.
    obtain ⟨ q, hq_prime, hq_dvd ⟩ : ∃ q : ℕ, Nat.Prime q ∧ q ∣ (2 ^ n + 1) / n := by
      refine Nat.exists_prime_and_dvd ?_;
      nlinarith [ Nat.div_mul_cancel hn₃, two_pow_add_one_gt n ];
    by_cases hq : q ∣ n <;> simp_all +decide [ Nat.dvd_div_iff_mul_dvd ];
    · -- Let $r$ be a new prime factor of $2^{nq} + 1$ that does not divide $2^n + 1$.
      obtain ⟨ r, hr_prime, hr_dvd ⟩ : ∃ r : ℕ, r.Prime ∧ r ∣ 2 ^ (n * q) + 1 ∧ ¬ r ∣ 2 ^ n + 1 := by
        apply exists_new_prime_factor;
        · contrapose! hn₂; interval_cases n <;> simp_all +decide ;
        · assumption;
        · rintro rfl; have := congr_arg Even hq_dvd.choose_spec; norm_num [ hn₁.ne', parity_simps ] at this;
        · exact dvd_of_mul_left_dvd hq_dvd;
      -- Let $m = n * q * r$.
      use n * q * r; simp_all +decide [ Nat.primeFactors_mul ] ; (
      -- Since $r$ is a new prime factor, the prime factors of $n * q * r$ are the union of the prime factors of $n$ and $\{r\}$.
      have h_prime_factors : (n * q * r).primeFactors = n.primeFactors ∪ {r} := by
        -- Since $q$ divides $n$, the prime factors of $n * q$ are the same as those of $n$.
        have h_prime_factors_nq : (n * q).primeFactors = n.primeFactors := by
          rw [ Nat.primeFactors_mul, Finset.union_eq_left.mpr ] <;> aesop
        generalize_proofs at *; (
        rw [ Nat.primeFactors_mul, h_prime_factors_nq ] <;> aesop;)
      generalize_proofs at *; (
      -- Since $r$ is a new prime factor, we have $n * q * r \mid 2^{n * q * r} + 1$.
      have h_div : n * q * r ∣ 2 ^ (n * q * r) + 1 := by
        have h_div : n * q ∣ 2 ^ (n * q) + 1 := by
          exact dvd_trans hq_dvd ( by have := Nat.Prime.odd_of_ne_two hq_prime ( by rintro rfl; exact absurd ( dvd_trans ( dvd_mul_left _ _ ) hq_dvd ) ( by norm_num [ Nat.dvd_add_right ( dvd_pow_self _ hn₁.ne' ) ] ) ) ; simpa [ *, pow_mul ] using this.nat_add_dvd_pow_add_pow _ 1 ) ;
        generalize_proofs at *; (
        convert Nat.Coprime.mul_dvd_of_dvd_of_dvd _ _ _ using 1 <;> simp_all +decide [ Nat.coprime_mul_iff_left, Nat.coprime_mul_iff_right ];
        · exact ⟨ Nat.Coprime.symm <| hr_prime.coprime_iff_not_dvd.mpr fun h => hr_dvd.2 <| dvd_trans h hn₃, Nat.Coprime.symm <| hr_prime.coprime_iff_not_dvd.mpr fun h => hr_dvd.2 <| dvd_trans h <| dvd_of_mul_left_dvd hq_dvd ⟩ ;
        · exact dvd_trans h_div ( by have := Nat.Prime.odd_of_ne_two hr_prime ( by rintro rfl; simp_all +decide [ ← even_iff_two_dvd, parity_simps ] ) ; simpa [ *, pow_mul ] using this.nat_add_dvd_pow_add_pow _ 1 ) ;
        · haveI := Fact.mk hr_prime; simp_all +decide [ ← ZMod.natCast_eq_zero_iff, pow_mul ] ;)
      generalize_proofs at *; (
      simp_all +decide [ Finset.union_comm, Finset.card_union ];
      exact ⟨ ⟨ hq_prime.pos, hr_prime.pos ⟩, by rw [ Finset.card_insert_of_notMem ( fun h => hr_dvd.2 <| Nat.dvd_trans ( Nat.dvd_of_mem_primeFactors h ) hn₃ ), hn₂ ] ⟩ ;)));
    · refine' ⟨ n * q, Nat.mul_pos hn₁ hq_prime.pos, _, _ ⟩;
      · rw [ Nat.primeFactors_mul, Finset.card_union ] <;> aesop;
      · convert extend_divisibility hn₃ q hq_prime ( by
          rintro rfl; replace hq_dvd := congr_arg Even hq_dvd.choose_spec; simp_all +decide [ parity_simps ] ; ) ( by
          exact dvd_of_mul_left_dvd hq_dvd ) using 1

def solution : Bool := true

theorem imo2000P5 :
    (∃ n, 0 < n ∧ n.primeFactors.card = 2000 ∧ n ∣ 2 ^ n + 1)
    ↔ solution := by
  simp only [solution]
  constructor
  · intro; trivial
  · intro
    exact exists_dvd_two_pow_add_one 2000

end Imo2000P5
