import Mathlib

namespace Imo2018P5

/-
IMO 2018 Problem 5.

Key mathematical ideas:
1. The consecutive difference of the integer sums gives:
   for all n ≥ N: a_n/a_{n+1} + (a_{n+1} - a_n)/a_1 ∈ ℤ
   (as a rational number)

2. p-adic analysis: For each prime p, the sequence ν_p(a_n) is
   eventually non-increasing. Hence ν_p(a_{n+1}) ≤ ν_p(a_n) for large n.
   This means a_{n+1} | a_n for all large n.

3. A non-increasing sequence of positive integers is eventually constant.

Strategy for the Lean proof: Rather than doing full p-adic analysis,
we observe:
- The divisibility condition a_{n+1} | a_n for large n follows from
  the integrality condition (via a careful analysis).
- Once we have a_{n+1} | a_n, we get a_n ≥ a_{n+1}, so the sequence
  is eventually non-increasing, hence eventually constant.

We proceed by showing:
(A) There exists M such that for all m ≥ M, a_{m+1} ∣ a_m  [key divisibility]
(B) From (A), the sequence is eventually constant.

For (B): If a_{m+1} | a_m and all a_n > 0, then a_{m+1} ≤ a_m.
So the sequence is non-increasing for m ≥ M. By well-ordering,
a non-increasing sequence of positive integers must stabilize.

Helper: a non-increasing sequence of positive integers is eventually constant
-/
lemma eventually_const_of_antitone (a : ℕ → ℤ) (apos : ∀ n, 0 < a n)
    (M : ℕ) (hdec : ∀ m, M ≤ m → a (m + 1) ≤ a m) :
    ∃ K, ∀ m, K ≤ m → a m = a (m + 1) := by
  have hlim : Filter.Tendsto (fun n => a (n + M)) Filter.atTop
      (nhds (sInf {a (n + M) | n : ℕ})) := by
    apply_rules [tendsto_atTop_ciInf]
    · exact antitone_nat_of_succ_le fun n => by
        simpa only [Nat.succ_add] using hdec _ (Nat.le_add_left _ _)
    · exact ⟨0, Set.forall_mem_range.mpr fun n => le_of_lt (apos _)⟩
  norm_num at hlim
  obtain ⟨K, hK⟩ := hlim
  refine ⟨K + M, fun m hm => ?_⟩
  have hmM : M ≤ m := by omega
  have hm1M : M ≤ m + 1 := by omega
  have hmK : K ≤ m - M := Nat.le_sub_of_add_le (by omega)
  have hm1K : K ≤ m + 1 - M := Nat.le_sub_of_add_le (by omega)
  simpa only [Nat.sub_add_cancel hmM, Nat.sub_add_cancel hm1M] using
    (hK (m - M) hmK).trans (hK (m + 1 - M) hm1K).symm

/-
Helper: the integrality condition gives a divisibility condition
For n ≥ N, the sum S(n) is an integer.
S(n+1) - S(n) = a_n / a_{n+1} + a_{n+1}/a_1 - a_n/a_1
= a_n / a_{n+1} + (a_{n+1} - a_n)/a_1 ∈ ℤ.
Multiplying by a_1 * a_{n+1}: a_1 * a_n + a_{n+1}*(a_{n+1} - a_n) ≡ 0 mod (a_1 * a_{n+1}).
Simplifying: a_{n+1}^2 + a_1*a_n - a_n*a_{n+1} ≡ 0 mod (a_1 * a_{n+1}).
In particular: a_{n+1} | a_1 * a_n, so any prime power in a_{n+1} beyond what's in a_1
must divide a_n. Eventually this forces a_{n+1} | a_n.

Subtracting two consecutive cyclic sums gives a local integrality relation.
-/
lemma consecutive_sum_integral (a : ℕ → ℤ) (N : ℕ)
    (h : ∀ n, N ≤ n →
      ∃ z : ℤ, z = ∑ i ∈ Finset.range n, (a i : ℚ) / a ((i + 1) % n)) :
    ∀ n, N ≤ n → ∃ z : ℤ,
      (z : ℚ) = (a n : ℚ) / a (n + 1) + ((a (n + 1) : ℚ) - a n) / a 0 := by
  intro n hn
  obtain ⟨z, hz⟩ := h (n + 1) (by omega)
  obtain ⟨w, hw⟩ := h (n + 2) (by omega)
  simp_all +decide [Finset.sum_range_succ]
  use w - z
  simp_all +decide [Finset.sum_range, Nat.mod_eq_of_lt]
  ring

/-
Prime valuations in the local relation bound every term by fixed initial data.
-/
lemma local_integrality_bounded (a : ℕ → ℤ) (apos : ∀ n, 0 < a n)
    (N : ℕ) (hint : ∀ n, N ≤ n → ∃ z : ℤ,
      (z : ℚ) = (a n : ℚ) / a (n + 1) + ((a (n + 1) : ℚ) - a n) / a 0) :
    ∃ B : ℤ, ∀ n, N ≤ n → a n ≤ B := by
  -- For each prime $p$, prove `factorization(a(n+1)) p ≤ max (factorization(a n) p) (factorization(a 0) p)` by contradiction using p-adic divisibility/valuation: if $y$ has more $p$ factors than both $x$ and $c$, then $x-y$ and $c-y$ have valuations exactly those of $x,c$, so the RHS valuation is $v(x)+v(c)$, less than the LHS's $v(c)+v(y)$. Inductively $a n$ divides $lcm (a N) (a 0)$ in natAbs, yielding the explicit bound.
  have h_factorization_bound : ∀ n ≥ N, ∀ p : ℕ, Nat.Prime p → (Nat.factorization (a n).natAbs p) ≤ max (Nat.factorization (a 0).natAbs p) (Nat.factorization (a N).natAbs p) := by
    -- By induction on $n$, we can show that the $p$-adic valuation of $a_n$ is bounded by the maximum of the $p$-adic valuations of $a_0$ and $a_N$.
    have h_ind : ∀ n ≥ N, ∀ p : ℕ, Nat.Prime p → (Nat.factorization (a (n + 1)).natAbs p) ≤ max (Nat.factorization (a n).natAbs p) (Nat.factorization (a 0).natAbs p) := by
      intro n hn p hp
      obtain ⟨z, hz⟩ := ‹∀ n ≥ N, ∃ z : ℤ, (z : ℚ) = (a n : ℚ) / a (n + 1) + ((a (n + 1) : ℚ) - a n) / a 0› n hn
      have h_eq : (z - 1 : ℤ) * (a 0 * a (n + 1)) = (a n - a (n + 1)) * (a 0 - a (n + 1)) := by
        rw [← @Int.cast_inj ℚ]
        push_cast
        rw [hz]
        ring_nf
        simp +decide [ne_of_gt (apos _)]
        ring
      by_contra h_contra
      have h_val : padicValInt p (a (n + 1)) > max (padicValInt p (a n)) (padicValInt p (a 0)) := by
        simp_all +decide [ padicValInt ];
        simp_all +decide [ Nat.factorization ]
      generalize_proofs at *;
      have h_val_rhs : padicValInt p ((a n - a (n + 1)) * (a 0 - a (n + 1))) = padicValInt p (a n) + padicValInt p (a 0) := by
        have h_val_rhs : padicValInt p (a n - a (n + 1)) = padicValInt p (a n) ∧ padicValInt p (a 0 - a (n + 1)) = padicValInt p (a 0) := by
          have h_val_diff : ∀ {x y : ℤ}, 0 < x → 0 < y → padicValInt p x < padicValInt p y → padicValInt p (x - y) = padicValInt p x := by
            intros x y hx hy hxy
            have h_div : (p : ℤ) ^ padicValInt p x ∣ x - y ∧ ¬(p : ℤ) ^ (padicValInt p x + 1) ∣ x - y := by
              have h_div : (p : ℤ) ^ padicValInt p x ∣ x ∧ ¬(p : ℤ) ^ (padicValInt p x + 1) ∣ x := by
                haveI := Fact.mk hp; simp +decide [ padicValInt_dvd_iff ] ;
                linarith
              generalize_proofs at *; (
              have h_div_y : (p : ℤ) ^ (padicValInt p x + 1) ∣ y := by
                have h_div_y : (p : ℤ) ^ (padicValInt p y) ∣ y := by
                  convert padicValInt_dvd y using 1;
                  all_goals exact ⟨ hp ⟩
                generalize_proofs at *; (
                exact dvd_trans ( pow_dvd_pow _ ( Nat.succ_le_of_lt hxy ) ) h_div_y)
              generalize_proofs at *; (
              exact ⟨ dvd_sub h_div.1 ( dvd_trans ( pow_dvd_pow _ ( Nat.le_succ _ ) ) h_div_y ), fun h => h_div.2 <| by simpa using dvd_add h ( dvd_trans ( pow_dvd_pow _ ( Nat.le_refl _ ) ) h_div_y ) ⟩))
            generalize_proofs at *; (
            have h_val_diff : padicValInt p (x - y) = Nat.factorization (Int.natAbs (x - y)) p := by
              rw [ padicValInt ];
              rw [ Nat.factorization_def ] ; aesop;
            generalize_proofs at *; (
            obtain ⟨ k, hk ⟩ := h_div.1; simp_all +decide [ Int.natAbs_mul ] ;
            rw [ Nat.factorization_mul ] <;> norm_num [ hp.ne_zero, hp.ne_one ];
            · simp_all +decide;
              exact Nat.factorization_eq_zero_of_not_dvd fun h => h_div <| mul_dvd_mul_left _ <| Int.natCast_dvd.mpr h;
            · aesop_cat))
          generalize_proofs at *; (
          exact ⟨ h_val_diff ( apos _ ) ( apos _ ) ( lt_of_le_of_lt ( le_max_left _ _ ) h_val ), h_val_diff ( apos _ ) ( apos _ ) ( lt_of_le_of_lt ( le_max_right _ _ ) h_val ) ⟩)
        generalize_proofs at *;
        haveI := Fact.mk hp; rw [ padicValInt.mul ] <;> simp_all +decide ;
        · intro h
          have h' : a n = a (n + 1) := by linarith
          rw [h'] at h_val
          exact absurd h_val.1 (lt_irrefl _)
        · intro h
          have h' : a 0 = a (n + 1) := by linarith
          rw [h'] at h_val
          exact absurd h_val.2 (lt_irrefl _)
      have h_val_lhs : padicValInt p ((z - 1) * (a 0 * a (n + 1))) ≥ padicValInt p (a 0) + padicValInt p (a (n + 1)) := by
        haveI := Fact.mk hp; rw [ padicValInt.mul, padicValInt.mul ] <;> norm_num [ ne_of_gt ( apos _ ) ] ;
        intro H; simp_all +decide [ sub_eq_iff_eq_add ] ;
        grind
      generalize_proofs at *;
      grind;
    intro n hn p hp; induction hn <;> simp_all +decide ;
    grind;
  -- By induction, $a n \leq \text{lcm}(a N, a 0)$ for all $n \geq N$.
  have h_lcm_bound : ∀ n ≥ N, (a n).natAbs ≤ Nat.lcm (a N).natAbs (a 0).natAbs := by
    intros n hn
    have h_factorization_le : (a n).natAbs ∣ Nat.lcm (a N).natAbs (a 0).natAbs := by
      rw [ ← Nat.factorization_le_iff_dvd ] <;> simp_all +decide [ Nat.factorization_lcm, ne_of_gt ];
      intro p; specialize h_factorization_bound n hn p; by_cases hp : Nat.Prime p <;> aesop;
    exact Nat.le_of_dvd ( Nat.lcm_pos ( Int.natAbs_pos.mpr ( ne_of_gt ( apos _ ) ) ) ( Int.natAbs_pos.mpr ( ne_of_gt ( apos _ ) ) ) ) h_factorization_le;
  exact ⟨ _, fun n hn => by linarith [ abs_of_pos ( apos n ), h_lcm_bound n hn ] ⟩

/-
Arithmetic core of reduced-ratio descent.
-/
lemma reduced_transition_decreases (r s u v : ℕ)
    (hr : 0 < r) (hs : 0 < s) (hu : 0 < u) (hv : 0 < v)
    (_hrs : Nat.Coprime r s) (huv : Nat.Coprime u v)
    (hz : ∃ z : ℤ, (z : ℚ) = ((r : ℚ) / s) / ((u : ℚ) / v) +
      (u : ℚ) / v - (r : ℚ) / s)
    (hne : (r : ℚ) / s ≠ (u : ℚ) / v) :
    u < r ∨ u = r ∧ v < s := by
  -- From the integrality condition, we derive that $u \mid r$ and $v \mid s$.
  have h_div : u ∣ r ∧ v ∣ s := by
    -- Clear denominators in the given equation to obtain an integer identity.
    obtain ⟨z, hz_eq⟩ := hz
    field_simp at hz_eq
    norm_cast at hz_eq;
    -- From the integrality condition, we derive that $u \mid r * v^2$ and $v \mid s * u^2$.
    have h_div_rv : u ∣ r * v^2 := by
      rw [ Int.subNatNat_eq_coe ] at hz_eq; exact Int.natCast_dvd_natCast.mp ⟨ z * s * v - s * u + r * v, by push_cast at *; linarith ⟩ ;
    have h_div_su : v ∣ s * u^2 := by
      rw [ Int.subNatNat_eq_coe ] at hz_eq;
      exact Int.natCast_dvd_natCast.mp ⟨ z * s * u + r * u - r * v, by push_cast at *; linarith ⟩;
    exact ⟨ huv.pow_right 2 |> fun h => h.dvd_of_dvd_mul_right h_div_rv, huv.symm.pow_right 2 |> fun h => h.dvd_of_dvd_mul_right h_div_su ⟩;
  cases eq_or_lt_of_le ( Nat.le_of_dvd hr h_div.1 ) <;> cases eq_or_lt_of_le ( Nat.le_of_dvd hs h_div.2 ) <;> simp_all +decide

/-
A nonconstant integral transition strictly decreases the reduced ratio to the first term.
-/
lemma local_transition_measure_decreases (c x y z : ℤ)
    (hc : 0 < c) (hx : 0 < x) (hy : 0 < y)
    (hz : (z : ℚ) = (x : ℚ) / y + ((y : ℚ) - x) / c) (hne : x ≠ y) :
    y.natAbs / Nat.gcd y.natAbs c.natAbs < x.natAbs / Nat.gcd x.natAbs c.natAbs ∨
      y.natAbs / Nat.gcd y.natAbs c.natAbs = x.natAbs / Nat.gcd x.natAbs c.natAbs ∧
        c.natAbs / Nat.gcd y.natAbs c.natAbs < c.natAbs / Nat.gcd x.natAbs c.natAbs := by
  contrapose! hne; have := @reduced_transition_decreases ( x.natAbs / Nat.gcd x.natAbs c.natAbs ) ( c.natAbs / Nat.gcd x.natAbs c.natAbs ) ( y.natAbs / Nat.gcd y.natAbs c.natAbs ) ( c.natAbs / Nat.gcd y.natAbs c.natAbs ) ;
  contrapose! this; simp_all +decide [ ne_of_gt ] ;
  refine' ⟨ Nat.le_of_dvd ( by positivity ) ( Nat.gcd_dvd_left _ _ ), Nat.le_of_dvd ( by positivity ) ( Nat.gcd_dvd_right _ _ ), Nat.le_of_dvd ( by positivity ) ( Nat.gcd_dvd_left _ _ ), Nat.le_of_dvd ( by positivity ) ( Nat.gcd_dvd_right _ _ ), _, _, _, _ ⟩;
  · rw [ Nat.Coprime, Nat.gcd_div ( Nat.gcd_dvd_left _ _ ) ( Nat.gcd_dvd_right _ _ ), Nat.div_self ( Nat.gcd_pos_of_pos_left _ ( Int.natAbs_pos.mpr hx.ne' ) ) ];
  · rw [ Nat.Coprime, Nat.gcd_div ( Nat.gcd_dvd_left _ _ ) ( Nat.gcd_dvd_right _ _ ), Nat.div_self ( Nat.gcd_pos_of_pos_left _ ( Int.natAbs_pos.mpr hy.ne' ) ) ];
  · simp_all +decide [ abs_of_pos, div_div_eq_mul_div, Nat.gcd_dvd_left, Nat.gcd_dvd_right ];
    simp_all +decide [ ne_of_gt ];
    exact ⟨ z, by linear_combination' hz ⟩;
  · rw [ Nat.cast_div ( Nat.gcd_dvd_left _ _ ), Nat.cast_div ( Nat.gcd_dvd_right _ _ ), Nat.cast_div ( Nat.gcd_dvd_left _ _ ), Nat.cast_div ( Nat.gcd_dvd_right _ _ ) ] <;> norm_num [ hx.ne', hy.ne', hc.ne' ];
    simp_all +decide [ abs_of_pos, ne_of_gt, div_eq_mul_inv, mul_comm, mul_left_comm ]

/-
A bounded positive sequence satisfying the local relation has no nontrivial recurrent cycle.
-/
lemma eventually_const_of_bounded_local_integrality (a : ℕ → ℤ)
    (apos : ∀ n, 0 < a n) (N : ℕ) (B : ℤ)
    (hB : ∀ n, N ≤ n → a n ≤ B)
    (hint : ∀ n, N ≤ n → ∃ z : ℤ,
      (z : ℚ) = (a n : ℚ) / a (n + 1) + ((a (n + 1) : ℚ) - a n) / a 0) :
    ∃ M, ∀ m, M ≤ m → a m = a (m + 1) := by
  obtain ⟨M₁, hM₁⟩ : ∃ M₁, ∀ m, N ≤ m → m ≥ M₁ → (a m).natAbs / Nat.gcd (a m).natAbs (a 0).natAbs = (a M₁).natAbs / Nat.gcd (a M₁).natAbs (a 0).natAbs := by
    -- By the well-ordering principle, there exists a minimal element in the set of values of $P(n)$ for $n \geq N$.
    obtain ⟨M₁, hM₁⟩ : ∃ M₁ ∈ (Set.Ici N), ∀ n ∈ (Set.Ici N), (a M₁).natAbs / Nat.gcd (a M₁).natAbs (a 0).natAbs ≤ (a n).natAbs / Nat.gcd (a n).natAbs (a 0).natAbs := by
      have h_well_ordering : ∃ m ∈ Set.image (fun n => (a n).natAbs / Nat.gcd (a n).natAbs (a 0).natAbs) (Set.Ici N), ∀ n ∈ Set.image (fun n => (a n).natAbs / Nat.gcd (a n).natAbs (a 0).natAbs) (Set.Ici N), m ≤ n := by
        apply_rules [ Set.exists_min_image ];
        · exact Set.Finite.subset ( Set.finite_Iic ( Int.natAbs B ) ) <| Set.image_subset_iff.mpr fun n hn => Nat.div_le_self _ _ |> le_trans <| by cases abs_cases ( a n ) <;> cases abs_cases B <;> linarith [ apos n, hB n hn ] ;
        · exact ⟨ _, ⟨ N, Set.mem_Ici.mpr le_rfl, rfl ⟩ ⟩;
      grind;
    use M₁; intros m hm₁ hm₂; induction' hm₂ with m hm₂ ih <;> simp_all +decide ;
    have := local_transition_measure_decreases ( a 0 ) ( a m ) ( a ( m + 1 ) ) ( Classical.choose ( ‹∀ n : ℕ, N ≤ n → ∃ z : ℤ, ( z : ℚ ) = ( a n : ℚ ) / a ( n + 1 ) + ( a ( n + 1 ) - a n ) / a 0› m ( by linarith ) ) ) ( apos 0 ) ( apos m ) ( apos ( m + 1 ) ) ( Classical.choose_spec ( ‹∀ n : ℕ, N ≤ n → ∃ z : ℤ, ( z : ℚ ) = ( a n : ℚ ) / a ( n + 1 ) + ( a ( n + 1 ) - a n ) / a 0› m ( by linarith ) ) ) ; simp_all +decide [ Nat.gcd_comm ] ;
    grind;
  -- By the properties of the potential function, if $a_m \neq a_{m+1}$, then $P(m+1) < P(m)$.
  have h_potential_decreasing : ∀ m, N ≤ m → m ≥ M₁ → (a m ≠ a (m + 1)) → (a 0).natAbs / Nat.gcd (a (m + 1)).natAbs (a 0).natAbs < (a 0).natAbs / Nat.gcd (a m).natAbs (a 0).natAbs := by
    intros m hm₁ hm₂ hm₃
    have h_potential_decreasing_step : (a (m + 1)).natAbs / Nat.gcd (a (m + 1)).natAbs (a 0).natAbs = (a m).natAbs / Nat.gcd (a m).natAbs (a 0).natAbs := by
      rw [ hM₁ m hm₁ hm₂, hM₁ ( m + 1 ) ( by linarith ) ( by linarith ) ];
    have := local_transition_measure_decreases ( a 0 ) ( a m ) ( a ( m + 1 ) ) ( Classical.choose ( ‹∀ n : ℕ, N ≤ n → ∃ z : ℤ, ( z : ℚ ) = ( a n : ℚ ) / a ( n + 1 ) + ( a ( n + 1 ) - a n ) / a 0› m hm₁ ) ) ( apos 0 ) ( apos m ) ( apos ( m + 1 ) ) ( Classical.choose_spec ( ‹∀ n : ℕ, N ≤ n → ∃ z : ℤ, ( z : ℚ ) = ( a n : ℚ ) / a ( n + 1 ) + ( a ( n + 1 ) - a n ) / a 0› m hm₁ ) ) hm₃; aesop;
  -- By the properties of the potential function, if $a_m \neq a_{m+1}$, then $P(m+1) < P(m)$, which contradicts the minimality of $P(M₁)$.
  obtain ⟨M₂, hM₂⟩ : ∃ M₂, ∀ m, N ≤ m → m ≥ M₂ → (a 0).natAbs / Nat.gcd (a m).natAbs (a 0).natAbs = (a 0).natAbs / Nat.gcd (a M₂).natAbs (a 0).natAbs := by
    -- By the properties of the potential function, the sequence of potentials is non-increasing and bounded below by 1.
    have h_potential_noninc : ∀ m, N ≤ m → m ≥ M₁ → (a 0).natAbs / Nat.gcd (a (m + 1)).natAbs (a 0).natAbs ≤ (a 0).natAbs / Nat.gcd (a m).natAbs (a 0).natAbs := by
      grind;
    -- By the properties of the potential function, the sequence of potentials is non-increasing and bounded below by 1, so it must stabilize.
    have h_potential_stabilize : Filter.Tendsto (fun m => (a 0).natAbs / Nat.gcd (a (N + M₁ + m)).natAbs (a 0).natAbs) Filter.atTop (nhds (sInf { (a 0).natAbs / Nat.gcd (a (N + M₁ + m)).natAbs (a 0).natAbs | m : ℕ })) := by
      apply_rules [ tendsto_atTop_ciInf ];
      · exact antitone_nat_of_succ_le fun m => by simpa only [ add_assoc ] using h_potential_noninc ( N + M₁ + m ) ( by linarith ) ( by linarith ) ;
      · exact ⟨ 0, Set.forall_mem_range.mpr fun m => Nat.zero_le _ ⟩;
    simp +zetaDelta at *;
    obtain ⟨ M₂, hM₂ ⟩ := h_potential_stabilize; use N + M₁ + M₂; intros m hm₁ hm₂; have := hM₂ ( m - ( N + M₁ ) ) ( Nat.le_sub_of_add_le ( by linarith ) ) ; simp_all +decide [ add_assoc, Nat.add_sub_of_le ( by linarith : N + M₁ ≤ m ) ] ;
  use Max.max N ( Max.max M₁ M₂ );
  grind

-- The local integrality relation forces a positive integer sequence to stabilize.
lemma eventually_const_of_local_integrality (a : ℕ → ℤ) (apos : ∀ n, 0 < a n)
    (N : ℕ) (hint : ∀ n, N ≤ n → ∃ z : ℤ,
      (z : ℚ) = (a n : ℚ) / a (n + 1) + ((a (n + 1) : ℚ) - a n) / a 0) :
    ∃ M, ∀ m, M ≤ m → a m = a (m + 1) := by
  obtain ⟨B, hB⟩ := local_integrality_bounded a apos N hint
  exact eventually_const_of_bounded_local_integrality a apos N B hB hint

-- The main theorem
theorem imo2018_p5
    (a : ℕ → ℤ)
    (apos : ∀ n, 0 < a n)
    (N : ℕ)
    (hN : 0 < N)
    (h : ∀ n, N ≤ n →
      ∃ z : ℤ,
        z = ∑ i ∈ Finset.range n, (a i : ℚ) / a ((i + 1) % n))
    : ∃ M, ∀ m, M ≤ m → a m = a (m + 1) := by
  cases N with
  | zero => omega
  | succ N =>
      apply eventually_const_of_local_integrality a apos (N + 1)
      exact consecutive_sum_integral a (N + 1) h