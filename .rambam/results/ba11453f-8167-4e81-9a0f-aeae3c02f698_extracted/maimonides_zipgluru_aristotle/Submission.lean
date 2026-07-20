import Mathlib

namespace Imo1998P6

/-
PROBLEM
General number theory lemma: if a^n | b^(n+1) for all n, then a | b

PROVIDED SOLUTION
If a = 0 or a = 1, trivial. If a ≥ 2: Let g = gcd(a,b), c = a/g. If c = 1, then a = g | b. If c ≥ 2: From a^(n-1) | b^n, derive c^(n-1) | g for all n ≥ 1 (using gcd(c, b/g) = 1 and a = c*g, b = (b/g)*g). But c ≥ 2 and g is fixed, so for large n, c^(n-1) > g, contradiction.
-/
lemma dvd_of_pow_dvd_pow_succ {a b : ℕ} (h : ∀ n : ℕ, a ^ n ∣ b ^ (n + 1)) : a ∣ b := by
  by_contra h_not_div;
  -- Let $p$ be a prime factor of $a$ such that $v_p(a) > v_p(b)$.
  obtain ⟨p, hp⟩ : ∃ p, Nat.Prime p ∧ (Nat.factorization a) p > (Nat.factorization b) p := by
    by_cases ha : a = 0 <;> by_cases hb : b = 0 <;> simp_all +decide [ Nat.factorization_eq_zero_iff ];
    · specialize h 1 ; aesop;
    · contrapose! h_not_div with h_div;
      exact Nat.factorization_le_iff_dvd ( by positivity ) ( by positivity ) |>.1 fun p => by by_cases hp : Nat.Prime p <;> aesop;
  -- Choose $n$ such that $n \cdot v_p(a) > (n+1) \cdot v_p(b)$.
  obtain ⟨n, hn⟩ : ∃ n, n * (Nat.factorization a) p > (n + 1) * (Nat.factorization b) p := by
    exact ⟨ b.factorization p + 1, by nlinarith ⟩;
  have := Nat.factorization_le_iff_dvd ( by aesop ) ( by aesop ) |>.2 ( h n ) ; simp_all +decide [ Nat.factorization_pow ];
  replace := this p; norm_num at this; linarith;

/-
PROBLEM
Three distinct primes bound: p * q³ * r ≥ 120 for distinct primes p, q, r

PROVIDED SOLUTION
Case analysis on the three distinct primes. The key is: among {a,b,c} distinct primes, at least one ≥ 5, and at least two ≥ 3.

If b = 2: then a,c are odd primes ≥ 3, and since they're distinct, one ≥ 5. So a*c ≥ 3*5 = 15, and b³ = 8. Total ≥ 120.

If b = 3: then b³ = 27, and a*c ≥ 2*5 = 10 (distinct primes ≠ 3). Total ≥ 270.

If b ≥ 5: then b³ ≥ 125, a*c ≥ 2*3 = 6. Total ≥ 750.

For the formal proof, use interval_cases or omega after establishing bounds on the primes using Nat.Prime.two_le and the distinctness hypotheses. For b = 2 case: need to show a*c ≥ 15 when a,c are distinct odd primes. Since they're distinct and both ≥ 3, one is ≥ 5, so min(a,c) ≥ 3 and max(a,c) ≥ 5, giving a*c ≥ 15.
-/
lemma three_distinct_primes_bound {a b c : ℕ}
    (ha : Nat.Prime a) (hb : Nat.Prime b) (hc : Nat.Prime c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    120 ≤ a * b ^ 3 * c := by
  by_contra! h_contra;
  -- Consider the possible values of $b$. Since $b$ is prime and $b \geq 3$, we have $b \geq 3$.
  by_cases hb3 : b ≥ 3;
  · -- If $b \geq 3$, then $b^3 \geq 27$. So $a * c * 27 < 120$, which implies $a * c < 4.44$, so $a * c \leq 4$.
    have h_ac_le_4 : a * c ≤ 4 := by
      nlinarith [ Nat.pow_le_pow_left hb3 3 ];
    have : a ≤ 4 := Nat.le_of_lt_succ ( by nlinarith only [ ha.two_le, hc.two_le, h_ac_le_4 ] ) ; ( have : c ≤ 4 := Nat.le_of_lt_succ ( by nlinarith only [ ha.two_le, hc.two_le, h_ac_le_4 ] ) ; interval_cases a <;> interval_cases c <;> norm_num at *; );
  · interval_cases b <;> simp_all +decide;
    have : a ≤ 15 := Nat.le_of_lt_succ ( by nlinarith [ hc.two_le ] ) ; ( have : c ≤ 15 := Nat.le_of_lt_succ ( by nlinarith [ ha.two_le ] ) ; interval_cases a <;> interval_cases c <;> trivial; )

-- Define g(s) = f(s)/d as a natural number
noncomputable def gFunc (f : ℕ+ → ℕ+) (s : ℕ+) : ℕ := (f s : ℕ) / (f 1 : ℕ)

section FunctionalEquation

variable {f : ℕ+ → ℕ+} (hf : ∀ s t : ℕ+, f (t ^ 2 * f s) = s * f t ^ 2)
include hf

/-
PROBLEM
Step 1: f(f(s)) = s * d²

PROVIDED SOLUTION
Set t = 1 in hf: f(1² * f(s)) = s * f(1)², i.e., f(f(s)) = s * (f 1)². Use `simpa using hf s 1` or similar.
-/
lemma fe_ff (s : ℕ+) : f (f s) = s * f 1 ^ 2 := by
  simpa using hf s 1

/-
PROBLEM
Step 2: f(d·t²) = f(t)²

PROVIDED SOLUTION
Set s = 1 in hf: f(t² * f(1)) = 1 * f(t)², i.e., f(f(1) * t²) = (f t)². Use mul_comm and `simpa using hf 1 t` or similar.
-/
lemma fe_fd (t : ℕ+) : f (f 1 * t ^ 2) = (f t) ^ 2 := by
  simpa [ mul_comm ] using hf 1 t

/-
PROBLEM
Step 3: f is injective

PROVIDED SOLUTION
If f(a) = f(b), then f(f(a)) = f(f(b)), so a * (f 1)² = b * (f 1)² by fe_ff. Cancel (f 1)² (which is positive) to get a = b. Use PNat.eq and the fact that PNat.val is positive.
-/
lemma f_injective : Function.Injective f := by
  exact fun a b h => by have := hf a 1; have := hf b 1; aesop;

/-
PROBLEM
Step 4: Quasi-multiplicativity: d·f(s·t) = f(s)·f(t)

PROVIDED SOLUTION
Detailed derivation:

Step A: From hf with s replaced by f(s): f(t² * f(f(s))) = f(s) * (f t)². By fe_ff, f(f(s)) = s * (f 1)², so f(t² * (s * (f 1)²)) = f(s) * (f t)².

Step B: From step A with t = 1: f(s * (f 1)²) = f(s) * (f 1)². So f commutes with multiplication by d²: f(s * d²) = f(s) * d².

Step C: From step A: f(t² * s * d²) = f(s) * (f t)². Using step B on the LHS (viewing t²*s*d² as (t²*s)*d²): f(t²*s) * d² = f(s) * (f t)².

Step D: From step C with s = 1: f(t²) * d² = d * (f t)², so d * f(t²) = (f t)² (cancel one d).

Step E: From step C with s = u²: f(t²*u²) * d² = f(u²) * (f t)². The LHS is f((t*u)²) * d². Using step D: f((t*u)²) = (f(t*u))²/d, so (f(t*u))²/d * d² = (f(t*u))² * d. And the RHS: f(u²) = (f u)²/d, so (f u)²/d * (f t)².

In PNat/ℕ terms: (f(t*u))² * d = (f u)² * (f t)² / d, i.e., (f(t*u))² * d² = (f u)² * (f t)², i.e., (d * f(t*u))² = (f(u) * f(t))². Taking positive square roots: d * f(t*u) = f(u) * f(t).

Key intermediate: need d * f(t²) = (f t)² and d² * f(t²*s) = f(s) * (f t)².

Use PNat.eq to convert to ℕ equalities, then use ring/nlinarith/omega after establishing the ℕ versions of all intermediate results.
-/
lemma quasi_mult (s t : ℕ+) : f 1 * f (s * t) = f s * f t := by
  have h_mul : ∀ s t : ℕ+, f (t^2 * s * f 1^2) = f s * (f t)^2 := by
    intro s t; convert hf ( f s ) t using 1 ; ring;
    rw [ show f ( f s ) = s * f 1 ^ 2 from by simpa using hf s 1 ] ; ring;
    rw [ mul_assoc ];
  -- From step D: d * f(t²) = f(t)².
  have h_stepD : ∀ t : ℕ+, f 1 * f (t^2) = (f t)^2 := by
    intros t
    have := hf 1 t
    simp at this;
    have := h_mul 1 t; simp_all +decide [ mul_assoc, mul_comm, mul_left_comm ] ;
    have := h_mul ( t ^ 2 ) 1; simp_all +decide [ pow_succ, mul_assoc ] ;
    exact PNat.eq ( by { have := congr_arg PNat.val this; nlinarith [ PNat.pos ( f 1 ), PNat.pos ( f t ), PNat.pos ( f ( t * t ) ) ] } );
  -- From step E: (f(t*u))² * d² = (f(u))² * (f(t))².
  have h_stepE : ∀ t u : ℕ+, (f (t * u))^2 * f 1^2 = (f u)^2 * (f t)^2 := by
    intros t u
    have := h_mul (u^2) t
    simp_all +decide [ mul_assoc, mul_comm, mul_left_comm, pow_two ];
    have := h_mul 1 ( t * u ) ; simp_all +decide [ ← mul_assoc ] ;
    have := h_stepD ( t * u ) ; simp_all +decide [ mul_assoc, mul_comm, mul_left_comm ] ;
    simp_all +decide [ ← mul_assoc ];
    simp_all +decide [ mul_assoc, mul_comm, mul_left_comm ];
    grind;
  simp_all +decide [ mul_pow, mul_comm, mul_left_comm ];
  exact PNat.eq ( by { have := h_stepE s t; simpa [ ← mul_pow ] using congr_arg PNat.val this } )

/-
PROBLEM
Step 5: d⁴·f(1998) = f(2)·f(3)³·f(37)

PROVIDED SOLUTION
Use quasi_mult repeatedly. From quasi_mult:
- f 1 * f(2*3) = f 2 * f 3, so f 1 * f 6 = f 2 * f 3
- f 1 * f(6*3) = f 6 * f 3
- f 1 * f(18*3) = f 18 * f 3
- f 1 * f(54*37) = f 54 * f 37

Multiply left sides: f(1)^4 * f(6) * f(18) * f(54) * f(1998) (since 2*3=6, 6*3=18, 18*3=54, 54*37=1998)
Multiply right sides: f(2) * f(3) * f(6) * f(3) * f(18) * f(3) * f(54) * f(37)
= f(2) * f(3)^3 * f(6) * f(18) * f(54) * f(37)

Cancel f(6) * f(18) * f(54) from both sides.

Alternatively, chain the substitutions:
From f 1 * f 6 = f 2 * f 3:
  f 1 * (f 1 * f 18) = f 1 * (f 6 * f 3) = (f 2 * f 3) * f 3 = f 2 * f 3^2
So f 1^2 * f 18 = f 2 * f 3^2.
  f 1 * (f 1^2 * f 54) = f 1^2 * (f 18 * f 3) = (f 2 * f 3^2) * f 3 = f 2 * f 3^3
So f 1^3 * f 54 = f 2 * f 3^3.
  f 1 * (f 1^3 * f 1998) = f 1^3 * (f 54 * f 37) = (f 2 * f 3^3) * f 37
So f 1^4 * f 1998 = f 2 * f 3^3 * f 37.

Key facts: (6 : ℕ+) = 2 * 3, (18 : ℕ+) = 6 * 3, (54 : ℕ+) = 18 * 3, (1998 : ℕ+) = 54 * 37.
These numerical facts can be verified by norm_num or decide after casting to ℕ.

Use PNat.eq to reduce to ℕ, or work directly in PNat using the CommMonoid structure. Use `have h1 := quasi_mult hf 2 3` etc. and chain equalities.
-/
lemma f_1998_prod : (f 1) ^ 4 * f 1998 = f 2 * (f 3) ^ 3 * f 37 := by
  -- Applying the quasi-multiplicative property repeatedly, we get:
  have h1 : f 1 * f 6 = f 2 * f 3 := by
    have := quasi_mult ( hf := hf ) 2 3; ( erw [ show ( 2 * 3 : ℕ+ ) = 6 by decide ] at this; aesop; )
  have h2 : f 1 * f 18 = f 6 * f 3 := by
    have := quasi_mult hf 6 3; aesop;
  have h3 : f 1 * f 54 = f 18 * f 3 := by
    convert quasi_mult _ 18 3 using 1;
    assumption
  have h4 : f 1 * f 1998 = f 54 * f 37 := by
    rw [ show ( 1998 : ℕ+ ) = 54 * 37 by decide ];
    apply quasi_mult;
    assumption;
  simp_all +decide [ pow_succ, mul_assoc ];
  simp_all +decide [ ← mul_assoc ]

/-
PROBLEM
Step 6: Power divisibility: d^n | f(s)^(n+1)

PROVIDED SOLUTION
By induction on n.
Base case n = 0: 1 | f(s), trivially true.
Inductive step: Assume (f 1)^n | (f s)^(n+1). Need (f 1)^(n+1) | (f s)^(n+2).

From quasi_mult with s = t: f 1 * f(s^2) = (f s)^2 (as PNat).
More generally, from quasi_mult applied repeatedly: (f 1)^(n-1) * f(s^n) = (f s)^n.

Actually, the cleanest approach: by induction on n, show (f 1)^n * f(s^(n+1)) = (f s)^(n+1).

Base case n=0: f(s) = f(s). ✓
Inductive step: (f 1)^n * f(s^(n+1)) = (f s)^(n+1) implies (f 1)^(n+1) * f(s^(n+2)) = (f s)^(n+2).
From quasi_mult: f 1 * f(s^(n+1) * s) = f(s^(n+1)) * f(s).
So f 1 * f(s^(n+2)) = f(s^(n+1)) * f(s).
Multiply both sides by (f 1)^n:
(f 1)^(n+1) * f(s^(n+2)) = (f 1)^n * f(s^(n+1)) * f(s) = (f s)^(n+1) * f(s) = (f s)^(n+2). ✓

So we have (f 1)^n * f(s^(n+1)) = (f s)^(n+1) as PNat equality.
In ℕ: (f 1 : ℕ)^n * (f(s^(n+1)) : ℕ) = (f s : ℕ)^(n+1).
Since f(s^(n+1)) ≥ 1, (f 1)^n | (f s)^(n+1). ✓
-/
lemma pow_dvd (s : ℕ+) (n : ℕ) : (f 1 : ℕ) ^ n ∣ (f s : ℕ) ^ (n + 1) := by
  -- By induction on $n$, we can show that $(f 1)^n * f(s^{n+1}) = (f s)^{n+1}$.
  have h_ind : ∀ n : ℕ, (f 1 : ℕ)^n * (f (s^(n+1)) : ℕ) = (f s : ℕ)^(n+1) := by
    intro n
    induction' n with n ih
    · simp [pow_zero];
    -- Using the induction hypothesis and the multiplicative property, we have:
    have h_step : (f 1 : ℕ) * (f (s^(n+1) * s) : ℕ) = (f (s^(n+1)) : ℕ) * (f s : ℕ) := by
      have h_step : ∀ a b : ℕ+, f 1 * f (a * b) = f a * f b := by
        exact?;
      exact congr_arg PNat.val ( h_step _ _ );
    simp_all +decide [ pow_succ, mul_assoc ];
    grind +ring;
  exact dvd_of_mul_right_eq _ ( h_ind n )

/-
PROBLEM
Step 7: d | f(s)

PROVIDED SOLUTION
Apply dvd_of_pow_dvd_pow_succ with a = (f 1 : ℕ) and b = (f s : ℕ). The hypothesis ∀ n, a^n | b^(n+1) is exactly pow_dvd hf s.
-/
lemma d_dvd_f (s : ℕ+) : (f 1 : ℕ) ∣ (f s : ℕ) := by
  convert dvd_of_pow_dvd_pow_succ _ using 1;
  exact?

/-
PROBLEM
Step 8: g(s) > 0

PROVIDED SOLUTION
g(s) = (f s : ℕ) / (f 1 : ℕ). Since (f 1 : ℕ) | (f s : ℕ) (by d_dvd_f) and (f s : ℕ) ≥ 1 (PNat.pos), the quotient is ≥ 1 > 0. Use Nat.div_pos with Nat.le_of_dvd.
-/
lemma gFunc_pos (s : ℕ+) : 0 < gFunc f s := by
  exact Nat.div_pos ( Nat.le_of_dvd ( PNat.pos _ ) ( d_dvd_f hf s ) ) ( PNat.pos _ )

/-
PROBLEM
Step 9: f(s) = d·g(s) in ℕ

PROVIDED SOLUTION
f(s) = d * g(s) is just Nat.div_mul_cancel applied to d_dvd_f. Specifically, (f s : ℕ) = (f 1 : ℕ) * ((f s : ℕ) / (f 1 : ℕ)) by Nat.mul_div_cancel' (d_dvd_f hf s) or similar.
-/
lemma f_eq_d_mul_g (s : ℕ+) : (f s : ℕ) = (f 1 : ℕ) * gFunc f s := by
  exact Eq.symm ( Nat.mul_div_cancel' <| d_dvd_f hf s )

/-
PROBLEM
Step 10: g(1) = 1

PROVIDED SOLUTION
g(1) = (f 1 : ℕ) / (f 1 : ℕ) = 1. Use Nat.div_self (PNat.pos (f 1)).
-/
lemma gFunc_one : gFunc f 1 = 1 := by
  exact Nat.div_self ( PNat.pos _ )

/-
PROBLEM
Step 11: g(s·t) = g(s)·g(t)

PROVIDED SOLUTION
From quasi_mult: (f 1 : ℕ) * (f(s*t) : ℕ) = (f s : ℕ) * (f t : ℕ).
Using f_eq_d_mul_g: (f s : ℕ) = d * g(s), (f t : ℕ) = d * g(t), (f(s*t) : ℕ) = d * g(s*t).
Substituting: d * (d * g(s*t)) = (d * g(s)) * (d * g(t)) = d² * g(s) * g(t).
So d² * g(s*t) = d² * g(s) * g(t).
Cancel d² (which is > 0): g(s*t) = g(s) * g(t).
-/
lemma gFunc_mult (s t : ℕ+) : gFunc f (s * t) = gFunc f s * gFunc f t := by
  -- By definition of $g$, we know that $f(s) = d \cdot g(s)$ and $f(t) = d \cdot g(t)$.
  have h_fs : (f s : ℕ) = (f 1 : ℕ) * gFunc f s := by
    exact?
  have h_ft : (f t : ℕ) = (f 1 : ℕ) * gFunc f t := by
    exact?
  have h_fst : (f (s * t) : ℕ) = (f 1 : ℕ) * gFunc f (s * t) := by
    exact?;
  have h_quasi_mult : (f 1 : ℕ) * f (s * t) = f s * f t := by
    have := quasi_mult hf s t
    exact congr_arg PNat.val this;
  nlinarith [ PNat.pos ( f 1 ), mul_pos ( PNat.pos ( f 1 ) ) ( PNat.pos ( f 1 ) ) ]

/-
PROBLEM
Step 12: f(⟨g(s), _⟩) : ℕ = s * d

PROVIDED SOLUTION
We need: (f ⟨g(s), _⟩ : ℕ) = s * d.

From f(d*t) = d*f(t) (which follows from quasi_mult with one argument being f 1):
quasi_mult hf (f 1) t gives: f 1 * f(f 1 * t) = f(f 1) * f(t).
And fe_ff hf 1 gives f(f 1) = 1 * (f 1)² = (f 1)², so:
f 1 * f(f 1 * t) = (f 1)² * f(t), hence f(f 1 * t) = f 1 * f(t).

Now, f(s) = f 1 * g(s) as ℕ (by f_eq_d_mul_g). So f(s) as PNat equals ⟨f 1 * g(s), _⟩.
Also, f 1 * ⟨g(s), _⟩ = ⟨(f 1 : ℕ) * g(s), _⟩ = ⟨(f s : ℕ), _⟩ = f s as PNat.

From f(f s) = s * (f 1)² (fe_ff):
f(f 1 * ⟨g(s), _⟩) = f(f s) = s * (f 1)².
But f(f 1 * t) = f 1 * f(t) gives:
f(f 1 * ⟨g(s), _⟩) = f 1 * f(⟨g(s), _⟩).

So f 1 * f(⟨g(s), _⟩) = s * (f 1)².
Hence (f ⟨g(s), _⟩ : ℕ) = s * (f 1 : ℕ).

Key: need to show f 1 * ⟨g(s), _⟩ = f s as PNat, which follows from f_eq_d_mul_g.
-/
lemma f_at_gFunc (s : ℕ+) :
    (f ⟨gFunc f s, gFunc_pos hf s⟩ : ℕ) = (s : ℕ) * (f 1 : ℕ) := by
  -- From f(d * t) = d * f(t)
  have f_d_mul_t (t : ℕ+) : f (f 1 * t) = f 1 * f t := by
    have := hf 1 t; have := hf ( f 1 * t ) 1; simp_all +decide [ mul_pow, mul_comm ] ;
    have := hf 1 ( f 1 * t ) ; simp_all +decide [ mul_pow, mul_comm, mul_left_comm ] ;
    simp_all +decide [ ← mul_assoc, sq ];
    have := hf ( t * t * f 1 ) 1; simp_all +decide [ mul_assoc, mul_comm, mul_left_comm ] ;
    have := hf ( f t * f t ) 1; simp_all +decide [ mul_assoc, mul_comm, mul_left_comm ] ;
    exact PNat.eq ( by { have := congr_arg PNat.val this; nlinarith [ PNat.pos ( f ( t * f 1 ) ), PNat.pos ( f t * f 1 ) ] } );
  -- From f(s) = d * g(s)
  have f_s_eq_d_mul_g_s : f s = f 1 * ⟨gFunc f s, by
    exact?⟩ := by
    exact PNat.eq ( f_eq_d_mul_g hf s )
  generalize_proofs at *;
  -- From f(f(s)) = s * d^2
  have f_ff_s : f (f s) = s * (f 1 : ℕ) ^ 2 := by
    simpa using congr_arg PNat.val ( hf s 1 )
  generalize_proofs at *;
  rw [ f_s_eq_d_mul_g_s ] at f_ff_s; simp_all +decide [ sq, mul_assoc ] ;
  nlinarith [ PNat.pos ( f 1 ) ]

/-
PROBLEM
Step 13: g(⟨g(s), _⟩) = s

PROVIDED SOLUTION
g(⟨g(s), _⟩) = (f ⟨g(s), _⟩ : ℕ) / (f 1 : ℕ) = (s * (f 1 : ℕ)) / (f 1 : ℕ) = s, using f_at_gFunc which gives (f ⟨g(s), _⟩ : ℕ) = s * (f 1 : ℕ), and Nat.mul_div_cancel.
-/
lemma gFunc_invol (s : ℕ+) :
    gFunc f ⟨gFunc f s, gFunc_pos hf s⟩ = (s : ℕ) := by
  have := f_at_gFunc hf s;
  exact Nat.div_eq_of_eq_mul_left ( PNat.pos _ ) ( by linarith )

/-
PROBLEM
Step 14: g is injective

PROVIDED SOLUTION
If gFunc f a = gFunc f b, then from f_eq_d_mul_g: (f a : ℕ) = d * g(a) = d * g(b) = (f b : ℕ). So f a = f b as PNat (by PNat.eq). By f_injective, a = b.
-/
lemma gFunc_inj (a b : ℕ+) (h : gFunc f a = gFunc f b) : a = b := by
  have := f_at_gFunc hf a; ( have := f_at_gFunc hf b; aesop; )

/-
PROBLEM
Step 15: g sends primes to primes

PROVIDED SOLUTION
Suppose g(p) is not prime. Since g(p) > 0 (gFunc_pos), either g(p) = 1 or g(p) is composite.

Case 1: g(p) = 1. Then g(⟨1, _⟩) = g(⟨g(p), _⟩) = p (by gFunc_invol). But g(1) = gFunc_one = 1. So p = 1, contradicting hp (Nat.Prime p means p ≥ 2).

Case 2: g(p) is composite, so ∃ a b : ℕ with a > 1 ∧ b > 1 ∧ g(p) = a * b.
Then g(⟨g(p), _⟩) = p, i.e., g(⟨a*b, _⟩) = p.
By gFunc_mult (applied to ⟨a, _⟩ and ⟨b, _⟩): g(⟨a, _⟩ * ⟨b, _⟩) = g(⟨a, _⟩) * g(⟨b, _⟩).
So g(⟨a, _⟩) * g(⟨b, _⟩) = p.
Since p is prime, one of g(⟨a, _⟩), g(⟨b, _⟩) = 1 and the other = p.
WLOG g(⟨a, _⟩) = 1. By gFunc_invol, a = g(⟨g(⟨a, _⟩), _⟩) = g(⟨1, _⟩) = gFunc_one = 1. But a > 1, contradiction.
-/
lemma gFunc_prime (p : ℕ+) (hp : Nat.Prime (p : ℕ)) : Nat.Prime (gFunc f p) := by
  by_contra h_not_prime
  obtain ⟨a, b, ha, hb, hab⟩ : ∃ a b : ℕ+, 1 < a ∧ 1 < b ∧ gFunc f p = a * b := by
    -- Since $g(p)$ is composite, there exist $a, b \in \mathbb{N}$ with $1 < a < g(p)$ and $1 < b < g(p)$ such that $g(p) = a \cdot b$.
    obtain ⟨a, b, ha, hb, hab⟩ : ∃ a b : ℕ, 1 < a ∧ 1 < b ∧ a * b = gFunc f p := by
      have := Nat.exists_dvd_of_not_prime2 ( show 1 < gFunc f p from ?_ ) h_not_prime;
      · exact ⟨ this.choose, gFunc f p / this.choose, this.choose_spec.2.1, by nlinarith [ this.choose_spec.2.2, Nat.div_mul_cancel this.choose_spec.1 ], Nat.mul_div_cancel' this.choose_spec.1 ⟩;
      · by_cases h_eq_one : gFunc f p = 1;
        · have := f_at_gFunc hf p; simp_all +decide [ sq ] ;
        · exact lt_of_le_of_ne ( Nat.succ_le_of_lt ( gFunc_pos hf p ) ) ( Ne.symm h_eq_one );
    exact ⟨ ⟨ a, pos_of_gt ha ⟩, ⟨ b, pos_of_gt hb ⟩, ha, hb, hab.symm ⟩;
  -- Since $g$ is injective, we have $g(a) = 1$ or $g(b) = 1$.
  have h_g_one : gFunc f a = 1 ∨ gFunc f b = 1 := by
    have h_g_one : gFunc f a * gFunc f b = p := by
      have h_g_ab : gFunc f (a * b) = p := by
        convert gFunc_invol hf p;
        exact PNat.eq hab.symm;
      rw [ ← h_g_ab, gFunc_mult ];
      assumption;
    have := hp.isUnit_or_isUnit h_g_one.symm; aesop;
  cases h_g_one <;> have := gFunc_invol hf a <;> have := gFunc_invol hf b <;> simp_all +decide [ gFunc_one ];
  · linarith [ show ( a : ℕ ) > 1 from ha ];
  · exact absurd this ( ne_of_lt hb )

/-
PROBLEM
Step 16: g(2), g(3), g(37) are distinct

PROVIDED SOLUTION
If gFunc f 2 = gFunc f 3, then by gFunc_inj, (2 : ℕ+) = 3, which is false (use decide or norm_num).
-/
lemma gFunc_distinct_23 : gFunc f 2 ≠ gFunc f 3 := by
  exact fun h => by have := gFunc_inj hf 2 3 h; contradiction;

/-
PROVIDED SOLUTION
If gFunc f 2 = gFunc f 37, then by gFunc_inj, (2 : ℕ+) = 37, which is false.
-/
lemma gFunc_distinct_2_37 : gFunc f 2 ≠ gFunc f 37 := by
  by_contra h_eq;
  -- By gFunc_inj, we have 2 = 37.
  have h_contra : (2 : ℕ+) = 37 := by
    exact?;
  contradiction

/-
PROVIDED SOLUTION
If gFunc f 3 = gFunc f 37, then by gFunc_inj, (3 : ℕ+) = 37, which is false.
-/
lemma gFunc_distinct_3_37 : gFunc f 3 ≠ gFunc f 37 := by
  have := gFunc_inj ( hf := hf ) 3 37; aesop;

/-
PROBLEM
Step 17: f(1998) in terms of g

PROVIDED SOLUTION
From f_1998_prod: (f 1)^4 * f 1998 = f 2 * (f 3)^3 * f 37 (in PNat).

In ℕ: (f 1 : ℕ)^4 * (f 1998 : ℕ) = (f 2 : ℕ) * (f 3 : ℕ)^3 * (f 37 : ℕ).

Using f_eq_d_mul_g on each: (f k : ℕ) = (f 1 : ℕ) * gFunc f k.

RHS = (f 1 : ℕ) * gFunc f 2 * ((f 1 : ℕ) * gFunc f 3)^3 * ((f 1 : ℕ) * gFunc f 37)
    = (f 1 : ℕ)^5 * gFunc f 2 * (gFunc f 3)^3 * gFunc f 37.

So (f 1)^4 * (f 1998 : ℕ) = (f 1)^5 * gFunc f 2 * (gFunc f 3)^3 * gFunc f 37.
Cancel (f 1)^4: (f 1998 : ℕ) = (f 1) * gFunc f 2 * (gFunc f 3)^3 * gFunc f 37.

Use nlinarith or omega after establishing the ℕ equations, with PNat.pos for positivity.
-/
lemma f_1998_val :
    (f 1998 : ℕ) = (f 1 : ℕ) * (gFunc f 2 * (gFunc f 3) ^ 3 * gFunc f 37) := by
  have := f_1998_prod hf
  have := f_eq_d_mul_g hf 2
  have := f_eq_d_mul_g hf 3
  have := f_eq_d_mul_g hf 37;
  simp_all +decide [ ← mul_assoc, ← PNat.coe_inj ];
  nlinarith [ pow_pos ( PNat.pos ( f 1 ) ) 4 ]

end FunctionalEquation

-- Main theorem
theorem lower_bound_1998
    (f : ℕ+ → ℕ+)
    (h : ∀ s t, f (t ^ 2 * f s) = s * (f t) ^ 2) :
    120 ≤ (f 1998 : ℕ) := by
  rw [f_1998_val h]
  have hg2 := gFunc_prime h 2 (by norm_num)
  have hg3 := gFunc_prime h 3 (by norm_num)
  have hg37 := gFunc_prime h 37 (by norm_num)
  have hd23 := gFunc_distinct_23 h
  have hd2_37 := gFunc_distinct_2_37 h
  have hd3_37 := gFunc_distinct_3_37 h
  have hbound := three_distinct_primes_bound hg2 hg3 hg37 hd23 hd2_37 hd3_37
  have hd_pos : 0 < (f 1 : ℕ) := PNat.pos (f 1)
  nlinarith

end Imo1998P6