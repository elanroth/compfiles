/-
Copyright (c) 2023 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/

import Mathlib.Tactic
import Mathlib.Data.Int.GCD
import Mathlib.NumberTheory.Multiplicity

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Olympiad 2010, Problem 3

Determine all functions g : ℤ>0 → ℤ>0 such that

               (g(m) + n)(g(n) + m)

is always a perfect square.
-/

namespace Imo2010P3

abbrev PosInt : Type := { x : ℤ // 0 < x }

notation "ℤ>0" => PosInt

determine SolutionSet : Set (ℤ>0 → ℤ>0) := { f | f = id ∨ ∃ c, ∀ x, f x = x + c }


/-
Key lemma: if (g(m)+n)(g(n)+m) is always a perfect square, then g is injective
Proof: if g(a) = g(b), then for any m, (g(m)+a)(g(a)+m) and (g(m)+b)(g(b)+m) = (g(m)+b)(g(a)+m)
are both perfect squares. Since g(a)=g(b) the second factors agree, so first factors agree: a=b.
-/
lemma injective_of_sq (g : ℤ>0 → ℤ>0) (h : ∀ m n : ℤ>0, IsSquare ((g m + n) * (g n + m))) :
    Function.Injective g := by
  intro a b hab
  -- (g(a)+a)(g(a)+a) = (g(a)+a)^2 is a square
  -- (g(a)+b)(g(b)+a) = (g(a)+b)(g(a)+a) must be a square
  -- similarly swap m,n: (g(b)+a)(g(a)+b) = (g(a)+b)(g(a)+a)^2... hmm
  -- If g(a)=g(b), then (g(m)+a)(g(a)+m) and (g(m)+b)(g(b)+m)=(g(m)+b)(g(a)+m) are squares
  -- With m=a: (g(a)+a)^2 is a square (trivial) and (g(a)+b)(g(a)+a) must be a square
  -- With m=b: (g(b)+a)(g(a)+b)=(g(a)+a)(g(a)+b) and (g(b)+b)^2=(g(a)+b)^2 are squares
  -- So (g(a)+a)(g(a)+b) is a square and (g(a)+b)(g(a)+a) is a square: consistent
  -- Need a stronger argument. Use: (g(n)+a)(g(a)+n) and (g(n)+b)(g(b)+n) both squares
  -- Since g(a)=g(b): second factors equal. So (g(n)+a)*(X) and (g(n)+b)*(X) both squares
  -- where X=g(a)+n. If X≠0: ratio (g(n)+a)/(g(n)+b) must be a ratio of squares, i.e. a perfect square.
  -- For large n, (g(n)+a)/(g(n)+b) → 1, so it must equal 1 eventually, giving a=b.
  -- Choose a prime $p$ such that $p > \max(a, b)$ and $p > g(a) + \max(a, b)$.
  obtain ⟨p, hp_prime, hp_gt⟩ : ∃ p : ℕ, Nat.Prime p ∧ p > max a.val b.val ∧ p > (g a).val + max a.val b.val := by
    obtain ⟨ p, hp ⟩ := Nat.exists_infinite_primes ( Int.natAbs ( g a + max a b ) + 1 );
    exact ⟨ p, hp.2, by cases max_cases ( a : ℤ ) ( b : ℤ ) <;> cases abs_cases ( g a + max a b : ℤ ) <;> linarith! [ show ( g a : ℤ ) > 0 from mod_cast Subtype.property ( g a ), show ( max a b : ℤ ) > 0 from mod_cast lt_max_iff.mpr ( Or.inl a.prop ) ], by cases max_cases ( a : ℤ ) ( b : ℤ ) <;> cases abs_cases ( g a + max a b : ℤ ) <;> linarith! [ show ( g a : ℤ ) > 0 from mod_cast Subtype.property ( g a ), show ( max a b : ℤ ) > 0 from mod_cast lt_max_iff.mpr ( Or.inl a.prop ) ] ⟩;
  -- Choose $m = p - g(a)$.
  set m : PosInt := ⟨p - (g a).val, by
    grind⟩
  generalize_proofs at *;
  -- Then $(g(m) + a)(g(a) + m) = (g(m) + a)p$ and $(g(m) + b)(g(b) + m) = (g(m) + b)p$ are both perfect squares.
  have h_sq_a : IsSquare ((g m + a).val * p) := by
    obtain ⟨ k, hk ⟩ := h m a;
    use k.val;
    convert congr_arg Subtype.val hk using 1 <;> norm_num [m]
  have h_sq_b : IsSquare ((g m + b).val * p) := by
    obtain ⟨ k, hk ⟩ := h m b;
    use k.val;
    convert congr_arg Subtype.val hk using 1 <;> simp +zetaDelta at *
    grind
  obtain ⟨k, hk⟩ := h_sq_a
  obtain ⟨l, hl⟩ := h_sq_b
  simp_all +decide
  -- Since $p$ is prime, $p$ must divide $k$ and $l$.
  have hp_div_k : (p : ℤ) ∣ k := by
    exact Int.Prime.dvd_pow' hp_prime <| by rw [ sq ] ; exact hk ▸ dvd_mul_left _ _;
  have hp_div_l : (p : ℤ) ∣ l := by
    exact Int.Prime.dvd_pow' hp_prime <| by rw [ sq ] ; exact hl ▸ dvd_mul_left _ _;
  obtain ⟨ k, rfl ⟩ := hp_div_k; obtain ⟨ l, rfl ⟩ := hp_div_l; ring_nf at hk hl;
  -- Dividing both sides of the equations by $p$, we get $g(m) + a = p k^2$ and $g(m) + b = p l^2$.
  have h_div_a : (g m).val + a.val = p * k ^ 2 := by
    nlinarith only [ hk, hp_prime.two_le ]
  have h_div_b : (g m).val + b.val = p * l ^ 2 := by
    nlinarith only [ hl, hp_prime.two_le ];
  -- Since $p$ is prime and $p > \max(a, b)$, we have $k^2 = l^2$.
  have h_kl : k ^ 2 = l ^ 2 := by
    nlinarith [ show ( a : ℤ ) > 0 from mod_cast a.prop, show ( b : ℤ ) > 0 from mod_cast b.prop ];
  grind

lemma padicValInt_eq_of_dvd_not_dvd {p k : ℕ} (hp : Nat.Prime p) {z : ℤ}
    (hk : (p : ℤ) ^ k ∣ z) (hsucc : ¬(p : ℤ) ^ (k + 1) ∣ z) :
    padicValInt p z = k := by
  contrapose! hsucc; haveI := Fact.mk hp; simp_all +decide [ padicValInt_dvd_iff ] ;
  grind

lemma exists_positive_shift_odd_padic {p : ℕ} (hp : Nat.Prime p) {a b : ℤ}
    (ha : 0 < a) (hb : 0 < b) (hab : (p : ℤ) ∣ a - b) :
    ∃ M : ℤ, 0 < M ∧ Odd (padicValInt p (M + a)) ∧ Odd (padicValInt p (M + b)) := by
  -- Set d = a - b. If d = 0, set x = p*(1+p*a), M = x - a; x > a, and p exactly divides x, so both valuations are 1.
  set d := a - b with hd
  by_cases hd_zero : d = 0;
  · refine' ⟨ p * ( 1 + p * a ) - a, _, _, _ ⟩;
    · nlinarith [ hp.two_le, mul_pos ( Nat.cast_pos.mpr hp.pos ) ha ];
    · simp +zetaDelta at *;
      haveI := Fact.mk hp; rw [ padicValInt.mul ] <;> norm_num [ hp.ne_zero, hp.ne_one, ha.ne', hb.ne' ] ;
      · rw [ padicValInt.eq_zero_of_not_dvd ] <;> norm_num;
        exact_mod_cast hp.not_dvd_one;
      · nlinarith [ hp.two_le ];
    · norm_num [ show a = b by linarith ] at *;
      haveI := Fact.mk hp; rw [ padicValInt.mul ] <;> norm_num [ hp.ne_zero, hp.ne_one, ha.ne' ] ;
      · rw [ padicValInt.eq_zero_of_not_dvd ] <;> norm_num [ hp.ne_one, hp.ne_zero, ha.ne' ];
        exact_mod_cast hp.not_dvd_one;
      · finiteness;
  · obtain ⟨t, ht⟩ : ∃ t : ℕ, (p : ℤ) ^ t ∣ d ∧ ¬(p : ℤ) ^ (t + 1) ∣ d := by
      exact ⟨ d.natAbs.factorization p, by simpa using Int.natCast_dvd.mpr ( Nat.ordProj_dvd _ _ ), by simpa using Int.natCast_dvd.not.mpr ( Nat.pow_succ_factorization_not_dvd ( Int.natAbs_ne_zero.mpr hd_zero ) hp ) ⟩
    have ht_pos : 1 ≤ t := by
      contrapose! ht; aesop;
    have ht_odd : Odd t ∨ Even t := by
      exact Nat.even_or_odd t |> Or.symm
    by_cases ht_odd : Odd t;
    · -- If t is odd, set x = p^(t+2)*(1+p*a), M = x - a.
      use p^(t+2)*(1+p*a) - a
      have hx_pos : 0 < p^(t+2)*(1+p*a) - a := by
        ring_nf;
        nlinarith [ show ( p : ℤ ) ^ 2 > 0 by exact pow_pos ( Nat.cast_pos.mpr hp.pos ) 2, show ( p : ℤ ) ^ t > 0 by exact pow_pos ( Nat.cast_pos.mpr hp.pos ) t, show ( p : ℤ ) ^ 3 > 0 by exact pow_pos ( Nat.cast_pos.mpr hp.pos ) 3, show ( p : ℤ ) ^ t * a > 0 by exact mul_pos ( pow_pos ( Nat.cast_pos.mpr hp.pos ) t ) ha, show ( p : ℤ ) ^ 3 * a > 0 by exact mul_pos ( pow_pos ( Nat.cast_pos.mpr hp.pos ) 3 ) ha ]
      have hx_val : padicValInt p (p^(t+2)*(1+p*a)) = t + 2 := by
        convert padicValInt_eq_of_dvd_not_dvd hp _ _ using 1;
        · exact dvd_mul_right _ _;
        · rw [ pow_succ, mul_dvd_mul_iff_left ( by exact pow_ne_zero _ ( Nat.cast_ne_zero.mpr hp.ne_zero ) ) ] ; exact fun h => by have := Int.dvd_sub h ( dvd_mul_right ( p : ℤ ) a ) ; norm_num at this ; exact absurd this ( by exact fun h' => by have := Int.le_of_dvd ( by positivity ) h'; nlinarith [ hp.two_le ] ) ;
      have hy_val : padicValInt p (p^(t+2)*(1+p*a) - d) = t := by
        apply padicValInt_eq_of_dvd_not_dvd hp;
        · exact dvd_sub ( dvd_mul_of_dvd_left ( pow_dvd_pow _ ( by linarith ) ) _ ) ht.1;
        · intro h; have := dvd_sub h ( dvd_mul_of_dvd_left ( pow_dvd_pow _ ( by linarith : t + 1 ≤ t + 2 ) ) ( 1 + p * a ) ) ; simp_all +decide [ pow_succ, mul_assoc ] ;
          exact ht.2 ( by simpa [ dvd_sub_comm ] using this )
      have hM_pos : 0 < p^(t+2)*(1+p*a) - a := by
        exact hx_pos
      have hM_val : Odd (padicValInt p (p^(t+2)*(1+p*a) - a + a)) ∧ Odd (padicValInt p (p^(t+2)*(1+p*a) - a + b)) := by
        grind
      exact ⟨hM_pos, hM_val⟩;
    · -- Set r = t - 1 and x = p^r * (1 + p * a), M = x - a.
      obtain ⟨r, hr⟩ : ∃ r : ℕ, t = r + 1 := by
        exact Nat.exists_eq_succ_of_ne_zero ( ne_bot_of_gt ht_pos )
      obtain ⟨x, hx⟩ : ∃ x : ℤ, (p : ℤ) ^ r ∣ x ∧ ¬(p : ℤ) ^ (r + 1) ∣ x ∧ x > a := by
        use (p : ℤ) ^ r * (1 + p * (a.natAbs + 1));
        norm_num [ pow_add, mul_dvd_mul_iff_left, hp.ne_zero ];
        exact ⟨ mod_cast hp.not_dvd_one, by nlinarith [ abs_of_pos ha, hp.two_le, pow_pos hp.pos r, mul_pos ( pow_pos hp.pos r ) ( hp.pos ) ] ⟩
      obtain ⟨M, hM⟩ : ∃ M : ℤ, M = x - a ∧ 0 < M := by
        exact ⟨ _, rfl, by linarith ⟩
      have hx_div : (p : ℤ) ^ r ∣ x ∧ ¬(p : ℤ) ^ (r + 1) ∣ x := by
        tauto
      have hx_div_b : (p : ℤ) ^ r ∣ (x - d) ∧ ¬(p : ℤ) ^ (r + 1) ∣ (x - d) := by
        simp_all +decide [ pow_succ, mul_assoc ];
        exact ⟨ dvd_sub hx_div ( dvd_of_mul_right_dvd ht.1 ), fun h => hx.1 <| by simpa using dvd_add h ht.1 ⟩
      have hM_pos : 0 < M := by
        linarith
      have hM_val : padicValInt p (M + a) = r ∧ padicValInt p (M + b) = r := by
        haveI := Fact.mk hp; simp_all +decide [ padicValInt_dvd_iff ] ;
        grind
      have hM_odd : Odd (padicValInt p (M + a)) ∧ Odd (padicValInt p (M + b)) := by
        grind
      exact ⟨M, hM_pos, hM_odd⟩

lemma prime_dvd_other_factor_of_square {p : ℕ} (hp : Nat.Prime p) {x y : ℤ}
    (hx : x ≠ 0) (hy : y ≠ 0) (hsq : IsSquare (x * y))
    (hodd : Odd (padicValInt p x)) : (p : ℤ) ∣ y := by
  obtain ⟨ z, hz ⟩ := hsq
  have hz_ne : z ≠ 0 := by
    rintro rfl
    norm_num at hz
    rcases hz with hx0 | hy0
    · exact hx hx0
    · exact hy hy0
  have h_val : padicValInt p x + padicValInt p y = 2 * padicValInt p z := by
    letI := Fact.mk hp
    rw [← padicValInt.mul hx hy, hz, padicValInt.mul hz_ne hz_ne]
    omega
  contrapose! hodd
  simp_all +decide [padicValInt.eq_zero_of_not_dvd]

lemma input_modEq_of_output_modEq (g : ℤ>0 → ℤ>0)
    (hsq : ∀ m n : ℤ>0, IsSquare ((g m + n) * (g n + m)))
    {p : ℕ} (hp : Nat.Prime p) (a b : ℤ>0)
    (hab : (g a).val ≡ (g b).val [ZMOD p]) : a.val ≡ b.val [ZMOD p] := by
  by_contra h_contra;
  obtain ⟨M, hM_pos, hM_odd⟩ : ∃ M : ℤ, 0 < M ∧ Odd (padicValInt p (M + (g a).val)) ∧ Odd (padicValInt p (M + (g b).val)) := by
    apply exists_positive_shift_odd_padic hp (Subtype.property (g a)) (Subtype.property (g b));
    exact hab.symm.dvd;
  -- For each of a,b, the square condition at (M,a) says (g(M)+a)*(g(a)+M) is square; commute factors as needed and use `prime_dvd_other_factor_of_square` with odd valuation of M+g(a) to infer p | g(M)+a, and similarly p | g(M)+b.
  have h_div_a : (p : ℤ) ∣ (g ⟨M, hM_pos⟩).val + a.val := by
    have h_div_a : IsSquare ((g ⟨M, hM_pos⟩ + a) * (g a + ⟨M, hM_pos⟩)) := by
      exact hsq _ _;
    apply prime_dvd_other_factor_of_square hp;
    exact ne_of_gt ( add_pos hM_pos ( mod_cast Subtype.property ( g a ) ) );
    · exact ne_of_gt ( add_pos ( mod_cast Subtype.property _ ) ( mod_cast Subtype.property _ ) );
    · obtain ⟨ k, hk ⟩ := h_div_a; use k; erw [ ← Subtype.coe_inj ] at *; simp_all +decide [ add_comm, mul_comm ] ;
    · exact hM_odd.1
  have h_div_b : (p : ℤ) ∣ (g ⟨M, hM_pos⟩).val + b.val := by
    convert prime_dvd_other_factor_of_square hp _ _ _ _ using 1;
    exact M + ( g b : ℤ );
    · linarith [ show ( g b : ℤ ) > 0 from mod_cast Subtype.property ( g b ) ];
    · grind +splitImp;
    · obtain ⟨ k, hk ⟩ := hsq ⟨ M, hM_pos ⟩ b;
      exact ⟨ k, by simpa [ add_comm, mul_comm ] using congr_arg Subtype.val hk ⟩;
    · exact hM_odd.2;
  apply h_contra
  apply Int.modEq_of_dvd
  obtain ⟨qa, hqa⟩ := h_div_a
  obtain ⟨qb, hqb⟩ := h_div_b
  refine ⟨qb - qa, ?_⟩
  linear_combination hqb - hqa

/-
Key lemma: |g(n+1) - g(n)| = 1
From the functional equation with m and varying n,
once we know g is injective and the sq condition holds,
consecutive values must differ by exactly 1.
-/
lemma step_one (g : ℤ>0 → ℤ>0)
    (hsq : ∀ m n : ℤ>0, IsSquare ((g m + n) * (g n + m)))
    (hinj : Function.Injective g) :
    ∀ n : ℤ>0, (g ⟨n.val + 1, by linarith [n.prop]⟩).val = g n + 1 ∨
               (g ⟨n.val + 1, by linarith [n.prop]⟩).val + 1 = g n := by
  generalize_proofs at *;
  intro n
  generalize_proofs at *;
  -- Show that the absolute difference between consecutive values is 1.
  have h_abs_diff : Int.natAbs ((g ⟨n.val + 1, by linarith⟩).val - (g n).val) = 1 := by
    by_contra h_contra
    generalize_proofs at *;
    -- Let $p$ be a prime divisor of $|g(n+1) - g(n)|$.
    obtain ⟨p, hp_prime, hp_div⟩ : ∃ p : ℕ, Nat.Prime p ∧ (p : ℤ) ∣ (g ⟨n.val + 1, by linarith⟩).val - (g n).val := by
      exact ⟨ Nat.minFac _, Nat.minFac_prime h_contra, Int.natCast_dvd.mpr <| Nat.minFac_dvd _ ⟩
    generalize_proofs at *; (
    -- Apply the input_modEq_of_output_modEq lemma to infer that $n+1 \equiv n \pmod{p}$, which contradicts the fact that $p$ is a prime greater than 1.
    have h_contradiction : (n.val + 1 : ℤ) ≡ n.val [ZMOD p] := by
      apply input_modEq_of_output_modEq g hsq hp_prime ⟨n.val + 1, by linarith⟩ n; exact Int.ModEq.symm <| Int.modEq_of_dvd hp_div;
    generalize_proofs at *; (
    exact absurd h_contradiction ( by rw [ Int.modEq_iff_dvd ] ; norm_num; exact mod_cast hp_prime.not_dvd_one )));
  grind

/-
Main theorem
-/
problem imo2010_p3 (g : ℤ>0 → ℤ>0) :
    g ∈ SolutionSet ↔ ∀ m n, IsSquare ((g m + n) * (g n + m)) := by
  constructor
  · rintro (rfl | ⟨c, hc⟩) m n
    · use m + n; rw [id, id, add_comm m n]
    · use m + n + c; rw [hc m, hc n]; simp only [add_comm, add_left_comm]
  · -- Hard direction: functional equation implies g = id or g(x) = x + c
    -- Step 1: g is injective (proved via sq condition)
    -- Step 2: |g(n+1)-g(n)| = 1 for all n
    -- Step 3: g monotone increasing (slope -1 would give non-positive values)
    -- Step 4: g(n) = n + (g(1) - 1) for all n, where g(1)-1 ≥ 0
    -- If g(1).val = 1 then g = id, else c = g(1) - 1 > 0
    intro hsq
    -- We show g x = x + c where c = g(1) - 1 (as integers), or g = id
    -- Since g(1) ≥ 1 (positive integer), c ≥ 0
    -- Case c = 0: g = id. Case c > 0: g x = x + c.
    revert hsq
    intro hsq
    have hinj : Function.Injective g := injective_of_sq g hsq
    have h_step : ∀ n : PosInt, (g ⟨n.val + 1, by linarith [n.prop]⟩).val = g n + 1 ∨ (g ⟨n.val + 1, by linarith [n.prop]⟩).val + 1 = g n :=
      step_one g hsq hinj
    -- By induction, we can show that $g(n) = g(1) + (n - 1)$ for all $n$.
    have h_ind : ∀ n : PosInt, (g n).val = (g ⟨1, by linarith⟩).val + (n.val - 1) := by
      intro n
      induction' n with n ih;
      induction' n using Int.induction_on with n ihn n ihn <;> norm_num at *;
      · contradiction;
      · rcases n with ( _ | n ) <;> simp_all +decide;
        cases h_step ( n + 1 ) ( by linarith ) <;> simp_all +decide [ add_assoc ];
        contrapose! hsq;
        refine' ⟨ n + 2, by linarith, 1, by linarith, _ ⟩ ; simp_all +decide [ IsSquare ];
        intro x hx; erw [ Subtype.mk_eq_mk ] at *; simp_all +decide [ ← sq ] ;
        exact fun h => by nlinarith only [ show x = g ⟨ 1, by linarith ⟩ + n + 1 by nlinarith only [ hx, h, show ( g ⟨ 1, by linarith ⟩ : ℤ ) > 0 from mod_cast Subtype.property _ ], h, show ( g ⟨ 1, by linarith ⟩ : ℤ ) > 0 from mod_cast Subtype.property _ ] ;
      · linarith;
    -- Let $c = g(1) - 1$. Then $g(n) = n + c$ for all $n$.
    obtain ⟨c, hc⟩ : ∃ c : ℤ, ∀ n : PosInt, (g n).val = n.val + c := by
      exact ⟨ ( g ⟨ 1, by decide ⟩ : ℤ ) - 1, fun n => by linarith [ h_ind n ] ⟩;
    -- Since $g$ maps to positive integers, we must have $c \geq 0$.
    have hc_nonneg : 0 ≤ c := by
      linarith! [ hc ⟨ 1, by decide ⟩, Subtype.property ( g ⟨ 1, by decide ⟩ ) ];
    rcases eq_or_lt_of_le hc_nonneg with hc0 | hcpos
    · refine Or.inl (funext fun x => Subtype.ext ?_)
      have h := hc x
      rw [← hc0, add_zero] at h
      simpa using h
    · refine Or.inr ⟨⟨c, hcpos⟩, fun x => Subtype.ext ?_⟩
      have h := hc x
      simpa [Positive.coe_add] using h


end Imo2010P3
