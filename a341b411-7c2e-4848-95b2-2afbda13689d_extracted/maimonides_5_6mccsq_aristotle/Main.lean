import Mathlib

namespace Imo1998P6

lemma functional_injective
    (g : ℕ+ → ℕ+)
    (hg : ∀ s t : ℕ+, g (t ^ 2 * g s) = s * (g t) ^ 2) :
    Function.Injective g := by
  intros s t hst
  have := hg s 1
  have := hg t 1
  aesop

lemma functional_mul
    (g : ℕ+ → ℕ+)
    (hg : ∀ s t : ℕ+, g (t ^ 2 * g s) = s * (g t) ^ 2) :
    ∀ a b : ℕ+, g 1 * g (a * b) = g a * g b := by
  -- From this, we get the quasi-multiplicativity identity: $g(t^2 g(s)) = s g(t)^2$.
  have h1 : ∀ s t : ℕ+, g (t ^ 2 * g s) = s * (g t) ^ 2 := by
    assumption
  have h2 : ∀ s t : ℕ+, g (s ^ 2 * g t) = t * (g s) ^ 2 := by
    exact fun s t => h1 t s;
  -- From the quasi-multiplicativity identity, we get $g(g(n)) = n g(1)^2$.
  have h3 : ∀ n : ℕ+, g (g n) = n * (g 1) ^ 2 := by
    exact fun n => by simpa using h1 n 1;
  -- From the quasi-multiplicativity identity, we get $g(t^2 g(s)) = s g(t)^2$.
  have h4 : ∀ s t : ℕ+, g (t ^ 2 * s * (g 1) ^ 2) = g s * (g t) ^ 2 := by
    intros s t
    have := h1 (g s) t
    simp_all +decide [ mul_assoc, mul_comm, mul_left_comm ];
  -- From the quasi-multiplicativity identity, we get $g(t^2 s) = \frac{g(s) g(t)^2}{g(1)^2}$.
  have h5 : ∀ s t : ℕ+, g (t ^ 2 * s) * (g 1) ^ 2 = g s * (g t) ^ 2 := by
    grind;
  -- From the quasi-multiplicativity identity, we get $g(a b)^2 = \frac{g(a)^2 g(b)^2}{g(1)^2}$.
  have h6 : ∀ a b : ℕ+, g (a * b) ^ 2 * (g 1) ^ 2 = g a ^ 2 * g b ^ 2 := by
    intros a b
    have := h5 (a ^ 2) b
    simp_all +decide [mul_assoc, mul_comm]
    have := h5 a (a * b)
    simp_all +decide [mul_pow]
    have := h5 (a * b ^ 2) a
    simp_all +decide [mul_comm, mul_left_comm]
    simp_all +decide [ ← mul_assoc, ← PNat.coe_inj ];
    nlinarith [ PNat.pos ( g a ), PNat.pos ( g b ), PNat.pos ( g ( a * b ) ), PNat.pos ( g ( a * b ^ 2 ) ), PNat.pos ( g ( a * a ^ 2 ) ), h5 a b, h5 b a, h5 a ( a * b ), h5 b ( a * b ), h5 a ( a * b ^ 2 ), h5 b ( a * b ^ 2 ), h5 a ( a * a ^ 2 ), h5 b ( a * a ^ 2 ) ];
  intro a b; specialize h6 a b; rw [← PNat.coe_inj] at *; simp_all +decide
  rw [ ← sq_eq_sq₀ ] <;> first | positivity | linarith;

lemma functional_normalization
    (g : ℕ+ → ℕ+)
    (hg : ∀ s t : ℕ+, g (t ^ 2 * g s) = s * (g t) ^ 2) :
    ∃ d : ℕ+, ∃ u : ℕ+ → ℕ+,
      (∀ n, g n = d * u n) ∧
      (∀ a b, u (a * b) = u a * u b) ∧
      (∀ n, u (u n) = n) := by
  -- Let's first show that $g(1)$ divides $g(n)$ for all $n$.
  have h_div : ∀ n : ℕ+, g 1 ∣ g n := by
    intro n;
    -- From `functional_mul`, `d * g(ab)=g(a)g(b)`. A standard number-theoretic argument: the identity implies d^(k-1) divides g(n)^k for every k≥1 (iterated multiplication); choosing k larger than every prime-adic valuation of d forces d|g(n).
    have h_divides_pow : ∀ k : ℕ, k > 0 → (g 1) ^ (k - 1) ∣ (g n) ^ k := by
      intro k hk_pos
      have h_divides_pow_step : ∀ m : ℕ+, g 1 ^ (k - 1) * g (n ^ k) = g n ^ k := by
        have h_mul_step : ∀ a b : ℕ+, g 1 * g (a * b) = g a * g b := by
          -- Apply the lemma `functional_mul` with the given hypothesis `hg`.
          apply functional_mul g hg;
        refine' Nat.le_induction _ _ k hk_pos <;> intros <;> simp_all +decide [ pow_succ', mul_assoc ];
        cases ‹1 ≤ _› <;> simp_all +decide [ pow_succ', mul_assoc ];
        grind;
      exact dvd_of_mul_right_eq _ ( h_divides_pow_step n );
    rw [ PNat.dvd_iff ] at *;
    rw [ ← Nat.factorization_le_iff_dvd ] <;> norm_num;
    intro p; specialize h_divides_pow ( Nat.factorization ( g 1 ) p + 1 ) ; simp_all +decide [ PNat.dvd_iff ] ;
    rw [ ← Nat.factorization_le_iff_dvd ] at h_divides_pow <;> simp_all +decide [ Nat.factorization_pow ];
    have := h_divides_pow p; norm_num at this; nlinarith;
  -- Define $u$ such that $u(n) = g(n) / g(1)$.
  obtain ⟨u, hu⟩ : ∃ u : ℕ+ → ℕ+, (∀ n : ℕ+, g n = g 1 * u n) ∧ (∀ a b : ℕ+, u (a * b) = u a * u b) := by
    choose u hu using h_div;
    refine' ⟨ u, hu, _ ⟩;
    intros a b
    have := functional_mul g hg a b
    simp [hu a, hu b] at this;
    rw [ hu ( a * b ) ] at this;
    exact PNat.eq ( by { have := congr_arg PNat.val this; nlinarith [ PNat.pos ( g 1 ), PNat.pos ( g 1 * g 1 ) ] } );
  refine' ⟨ g 1, u, hu.1, hu.2, _ ⟩;
  -- From $g(g(n)) = n * g(1)^2$, we substitute $g(n) = g(1) * u(n)$ to get $g(1) * u(g(n)) = n * g(1)^2$, which simplifies to $u(g(n)) = n * g(1)$.
  have h_u_g : ∀ n : ℕ+, u (g n) = n * g 1 := by
    intro n
    have := hg n 1
    simp at this;
    rw [ hu.1 ( g n ) ] at this;
    exact PNat.eq ( by { have := congr_arg PNat.val this; nlinarith [ PNat.pos ( g 1 ) ] } );
  intro n; specialize h_u_g n; rw [ hu.1 ] at h_u_g; simp +decide [ hu.2 ] at h_u_g;
  -- From $g(g(1)) = 1 * g(1)^2$, we substitute $g(1) = g(1) * u(1)$ to get $g(1) * u(g(1)) = g(1)^2$, which simplifies to $u(g(1)) = g(1)$.
  have h_u_g1 : u (g 1) = g 1 := by
    have := hg 1 1; simp +decide [ hu.1 ( g 1 ) ] at this;
    simpa [ sq ] using this;
  simpa [ h_u_g1, mul_comm ] using h_u_g

lemma multiplicative_involution_1998_lower_bound
    (u : ℕ+ → ℕ+)
    (hu_mul : ∀ a b, u (a * b) = u a * u b)
    (hu_inv : ∀ n, u (u n) = n) :
    120 ≤ u 1998 := by
  -- From functional_normalization, we have u(1998) = u(2) * u(3)^3 * u(37).
  have h_u1998_decomp : u 1998 = u 2 * u 3 ^ 3 * u 37 := by
    exact hu_mul 2 999 ▸ hu_mul 3 333 ▸ hu_mul 3 111 ▸ hu_mul 3 37 ▸ by ring;
  -- Since $u$ is injective, $u(2)$, $u(3)$, and $u(37)$ are distinct primes.
  have h_distinct_primes : Nat.Prime (u 2).val ∧ Nat.Prime (u 3).val ∧ Nat.Prime (u 37).val ∧ (u 2).val ≠ (u 3).val ∧ (u 2).val ≠ (u 37).val ∧ (u 3).val ≠ (u 37).val := by
    -- Since $u$ is injective and multiplicative, $u(p)$ must be prime for any prime $p$.
    have h_prime : ∀ p : ℕ+, Nat.Prime p.val → Nat.Prime (u p).val := by
      intro p hp
      by_contra h_not_prime
      obtain ⟨a, b, ha, hb, hab⟩ : ∃ a b : ℕ+, 1 < a ∧ 1 < b ∧ u p = a * b := by
        have := Nat.exists_dvd_of_not_prime2 ( show 1 < ( u p : ℕ ) from ?_ ) h_not_prime
        generalize_proofs at *; (
        obtain ⟨ m, hm₁, hm₂, hm₃ ⟩ := this; exact ⟨ ⟨ m, by linarith ⟩, ⟨ u p / m, Nat.div_pos ( Nat.le_of_dvd ( PNat.pos _ ) hm₁ ) ( by linarith ) ⟩, hm₂, by exact Nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨ by nlinarith [ Nat.div_mul_cancel hm₁ ], by nlinarith [ Nat.div_mul_cancel hm₁ ] ⟩, PNat.eq ( Eq.symm <| Nat.mul_div_cancel' hm₁ ) ⟩ ;);
        exact mod_cast lt_of_le_of_ne ( PNat.one_le _ ) ( Ne.symm <| by intro t; have := hu_inv p; have := hu_mul p 1; aesop ) ;
      generalize_proofs at *; (
      have := hu_inv p; have := hu_inv (a * b); simp_all +decide
      replace this := congr_arg PNat.val this; simp_all +decide [ Nat.prime_mul_iff ] ;
      have := hp.isUnit_or_isUnit this.symm; aesop;);
    exact ⟨ h_prime 2 Nat.prime_two, h_prime 3 Nat.prime_three, h_prime 37 ( by decide ), fun h => by have := hu_inv 2; have := hu_inv 3; aesop, fun h => by have := hu_inv 2; have := hu_inv 37; aesop, fun h => by have := hu_inv 3; have := hu_inv 37; aesop ⟩;
  -- Since $u(2)$, $u(3)$, and $u(37)$ are distinct primes, we need to find the minimum value of $u(2) * u(3)^3 * u(37)$.
  have h_min : ∀ p q r : ℕ, Nat.Prime p → Nat.Prime q → Nat.Prime r → p ≠ q → p ≠ r → q ≠ r → p * q^3 * r ≥ 120 := by
    intro p q r hp hq hr hpq hpr hqr; rcases p with ( _ | _ | _ | p ) <;> rcases q with ( _ | _ | _ | q ) <;> rcases r with ( _ | _ | _ | r ) <;> simp_all +arith +decide;
    · nlinarith [ sq q, sq r, mul_pos ( Nat.succ_pos q ) ( Nat.succ_pos r ) ];
    · rcases p with ( _ | _ | p ) <;> rcases r with ( _ | _ | r ) <;> norm_num at * <;> nlinarith;
    · nlinarith only [ sq p, sq q, mul_pos ( Nat.succ_pos p ) ( Nat.succ_pos q ) ];
    · lia;
  exact h_u1998_decomp ▸ mod_cast h_min _ _ _ h_distinct_primes.1 h_distinct_primes.2.1 h_distinct_primes.2.2.1 h_distinct_primes.2.2.2.1 h_distinct_primes.2.2.2.2.1 h_distinct_primes.2.2.2.2.2

/-!
# IMO 1998 Problem 6

Find the minimum value of f(1998) where f : ℕ+ → ℕ+ satisfies
  f(t² · f(s)) = s · f(t)²  for all s, t : ℕ+.

Answer: 120.

Mathematical proof outline:
  1) Let d = f(1). From the functional equation:
     - Substituting s=n, t=1: f(f(n)) = d² · n  (so f is injective)
     - Substituting s=1, t=n: f(d · n²) = f(n)²
     - One derives: d · f(a·b) = f(a) · f(b)

  2) Define g : ℕ+ → ℕ+ by g(n) = f(n) / d.
     Then g is completely multiplicative and g(g(n)) = n (an involution).
     Also g maps primes to primes.

  3) 1998 = 2 · 3³ · 37, so f(1998) = d · g(2) · g(3)³ · g(37).

  4) Minimizing d · g(2) · g(3)³ · g(37) over all valid (d, g):
     - d ≥ 1, take d = 1.
     - g(3) should be small → g(3) = 2 (so g(2) = 3).
     - g(37) should be small → g(37) = 5 (so g(5) = 37).
     - Value: 1 · 3 · 2³ · 5 = 3 · 8 · 5 = 120. ✓
     - Any other valid involution gives a larger value.
-/

/-
The statement as it appears in compfiles:
determine solution : ℕ+ := 120
problem imo1998_p6 (f : ℕ+ → ℕ+) (h : ∀ s t, f(t²·f(s)) = s·f(t)²) :
IsLeast {n : ℕ | n = f 1998} solution

With fixed f, the set {n : ℕ | n = ↑(f 1998)} = {↑(f 1998)}.
IsLeast {↑(f 1998)} ↑(120 : ℕ+) means ↑(f 1998) = 120 and 120 ≤ ↑(f 1998).
So the goal is: f(1998) = 120 AND f(1998) ≥ 120, i.e., f(1998) = 120.

But this cannot hold for all f (identity function gives f(1998)=1998).
More likely interpretation: the set ranges over all admissible f.

We formalize the mathematically meaningful version:
-/
theorem imo1998_p6
    (f : ℕ+ → ℕ+)
    (h : ∀ s t : ℕ+, f (t ^ 2 * f s) = s * (f t) ^ 2) :
    IsLeast {n : ℕ+ | ∃ g : ℕ+ → ℕ+, (∀ s t : ℕ+, g (t ^ 2 * g s) = s * (g t) ^ 2) ∧ n = g 1998}
      120 := by
  have hf : Function.Injective f := functional_injective f h
  clear hf
  constructor
  · -- Existence: exhibit a witness with g(1998) = 120.
    -- The witness: swap 2↔3, 5↔37 on prime factorizations, extended multiplicatively.
    -- On key values: g(2)=3, g(3)=2, g(5)=37, g(37)=5.
    -- Since 1998 = 2 · 3³ · 37: g(1998) = g(2)·g(3)³·g(37) = 3·8·5 = 120.
    simp only [Set.mem_setOf_eq]
    -- We construct the witness using the completely multiplicative extension
    -- For a simpler witness: f₀ defined as the multiplicative function
    -- sending each prime p to its swap partner.
    -- This is complex to define directly; instead use norm_num + explicit construction.
    by_contra! h_contra;
    -- Define the prime permutation $\sigma$ that swaps 2 and 3, 5 and 37, and fixes all other primes.
    set σ : ℕ → ℕ := fun p => if p = 2 then 3 else if p = 3 then 2 else if p = 5 then 37 else if p = 37 then 5 else p;
    -- Define the multiplicative function $g$ induced by the prime permutation $\sigma$.
    obtain ⟨g, hg⟩ : ∃ g : ℕ+ → ℕ+, (∀ p : ℕ+, Nat.Prime p → g p = σ p) ∧ (∀ p q : ℕ+, g (p * q) = g p * g q) := by
      -- Define the multiplicative function $g$ induced by the prime permutation $\sigma$ using the `Nat.factorization` function.
      have hg_def : ∃ g : ℕ+ → ℕ, (∀ p : ℕ+, Nat.Prime p → g p = σ p) ∧ (∀ p q : ℕ+, g (p * q) = g p * g q) ∧ (∀ p : ℕ+, g p > 0) := by
        use fun p => ∏ q ∈ Nat.primeFactors p, σ q ^ (Nat.factorization p q);
        refine' ⟨ _, _, _ ⟩ <;> norm_num;
        · intro p hp; simp +decide [ hp ] ;
        · intro p q; rw [ Nat.primeFactors_mul ( by positivity ) ( by positivity ) ] ; simp +decide [ Finset.prod_mul_distrib, pow_add ] ;
          rw [ ← Finset.prod_subset ( Finset.subset_union_left ), ← Finset.prod_subset ( Finset.subset_union_right ) ]; all_goals intro x hx hx'; rw [ Nat.factorization_eq_zero_of_not_dvd ] <;> aesop;
        · intro p i hi hi'; rcases i with ( _ | _ | _ | _ | _ | _ | _ | i ) <;> simp +arith +decide at hi hi' ⊢;
          · exact Nat.one_le_pow _ _ ( by decide );
          · exact Nat.one_le_pow _ _ ( by decide );
          · exact Nat.one_le_pow _ _ ( by decide );
          · exact Nat.one_le_pow _ _ ( by aesop );
      obtain ⟨ g, hg₁, hg₂, hg₃ ⟩ := hg_def; exact ⟨ fun p => ⟨ g p, hg₃ p ⟩, fun p hp => hg₁ p hp, fun p q => PNat.eq ( hg₂ p q ) ⟩ ;
    -- Show that $g$ satisfies the given functional equation.
    have hg_eq : ∀ s t : ℕ+, g (t ^ 2 * g s) = s * g t ^ 2 := by
      -- By definition of $g$, we know that $g(g(s)) = s$ for all $s$.
      have hg_g : ∀ s : ℕ+, g (g s) = s := by
        intro s
        have hg_g_prime : ∀ p : ℕ+, Nat.Prime p → g (g p) = p := by
          intro p hp; rw [← PNat.coe_inj]; simp +decide
          rw [ ← PNat.coe_inj, hg.1, hg.1 ] <;> norm_num [ hp ];
          · grind;
          · rw [ hg.1 p hp ] ; aesop ( simp_config := { decide := true } ) ;
        induction' s using PNat.strongInductionOn with s ih;
        by_cases hs : s = 1;
        · have := hg.2 1 1; aesop;
        · obtain ⟨p, hp⟩ : ∃ p : ℕ+, Nat.Prime p ∧ p ∣ s := by
            exact PNat.exists_prime_and_dvd hs;
          obtain ⟨ q, rfl ⟩ := hp.2;
          simp +decide [ *, ih q ( by { exact ( show ( q : ℕ ) < p * q from lt_mul_of_one_lt_left q.pos hp.1.one_lt ) } ) ];
      simp +decide [*, sq, mul_comm, mul_left_comm]
    -- Calculate $g(1998)$ using the definition of $g$.
    have hg_1998 : g 1998 = g 2 * g 3 ^ 3 * g 37 := by
      exact hg.2 2 999 ▸ hg.2 3 333 ▸ hg.2 3 111 ▸ hg.2 3 37 ▸ by ring;
    exact h_contra g hg_eq ( hg_1998.symm ▸ by erw [ show g 2 = 3 from PNat.eq ( hg.1 2 Nat.prime_two ), show g 3 = 2 from PNat.eq ( hg.1 3 Nat.prime_three ), show g 37 = 5 from PNat.eq ( hg.1 37 ( by norm_num ) ) ] ; decide )
  · -- Lower bound: for any g satisfying the equation, g(1998) ≥ 120.
    intro x hx
    simp only [Set.mem_setOf_eq] at hx
    obtain ⟨g, hg, hx⟩ := hx
    subst hx
    -- We show g(1998) ≥ 120.
    -- Step 1: Let d = g(1). From hg with s=n, t=1: g(g(n)) = d²·n.
    -- Step 2: From hg with s=1, t=n: g(d·n²) = g(n)².
    -- Step 3: d · g(a·b) = g(a) · g(b) (quasi-multiplicativity).
    -- Step 4: g(n) = d · h(n) where h is multiplicative involution.
    -- Step 5: g(1998) = d · h(2) · h(3)³ · h(37) ≥ 120.
    obtain ⟨ d, u, hdu, hu_mul, hu_inv ⟩ := functional_normalization g hg;
    have h_g_1998 : g 1998 = d * u 1998 := by
      exact hdu _;
    exact h_g_1998.symm ▸ Nat.le_trans ( multiplicative_involution_1998_lower_bound u hu_mul hu_inv ) ( Nat.le_mul_of_pos_left _ <| PNat.pos _ )

end Imo1998P6
