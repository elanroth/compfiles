/-
IMO 2016 Problem 5 — fill in the single sorry.

The construction: erase from left side all j ≡ 2,3 mod 4; erase from right all j ≡ 0,1 mod 4.
Then:
  Left side = ∏_{j ≡ 0,1 mod 4, 1≤j≤2016} (x - j)
  Right side = ∏_{j ≡ 2,3 mod 4, 1≤j≤2016} (x - j)

Key algebraic fact: for each quadruple {4m-3, 4m-2, 4m-1, 4m},
  (x-(4m-3))(x-4m) - (x-(4m-2))(x-(4m-1)) = -2  for ALL real x.

So R_m(x) = L_m(x) + 2 where L_m = (x-(4m-3))(x-4m), R_m = (x-(4m-2))(x-(4m-1)).

The left product is ∏_m L_m, the right product is ∏_m R_m = ∏_m (L_m + 2).

These can never be equal because:
- If all L_m > 0, then R_m = L_m + 2 > L_m, so ∏ R_m > ∏ L_m (both products positive).
- If all L_m < 0, ... more subtle. But the product of all R_m and all L_m depends on signs.

Actually: consider g(t) = ∏_m (L_m + t) for t ∈ [0,2]. We want to show g(2) ≠ g(0).
g'(t) = ∑_m ∏_{k≠m} (L_k + t). This can be zero.

Better approach for Lean: just observe the two index sets are disjoint, and
if x is an integer in {1..2016} ≡ 0,1 mod 4, then left = 0 but right ≠ 0.
If x is an integer in {1..2016} ≡ 2,3 mod 4, then right = 0 but left ≠ 0.
If x is not an integer root of either side, we need another argument.

For non-integer x: use the key algebraic identity per quadruple and a sign argument.
Between integers, the ratio R_m/L_m = 1 + 2/L_m. If all L_m > 0, the product ratio > 1.
The product of L_m has exactly k sign changes as x varies; tracking these shows ∏L_m ≠ ∏R_m.

For Lean, let's try: the two index sets are disjoint (A ∩ B = ∅ where A = {j: j%4=0 or 1}, B = {j: j%4=2 or 3}). If x ∈ A (as a natural number), left = 0, right ≠ 0 (since B is disjoint from A, x ∉ B, so no factor of right vanishes). Similarly for x ∈ B. For non-integer x or x outside {1..2016}, we use the algebraic argument.
-/

import Mathlib.Tactic

open Finset BigOperators

namespace Imo2016P5

-- Helper: the two erased sets cover all residues, so remaining sets are disjoint
lemma sets_disjoint :
    Disjoint
      ((Finset.Icc 1 2016 : Finset ℕ) \ (Finset.Icc 1 2016).filter (fun n ↦ n % 4 = 2 ∨ n % 4 = 3))
      ((Finset.Icc 1 2016 : Finset ℕ) \ (Finset.Icc 1 2016).filter (fun n ↦ n % 4 = 0 ∨ n % 4 = 1)) := by
  simp only [Finset.disjoint_left, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_Icc]
  intro a ⟨ha, hna⟩ ⟨_, hnb⟩
  push Not at hna hnb
  omega

-- Key algebraic identity: for each quadruple, the difference is exactly -2
lemma quad_diff (x : ℝ) (m : ℕ) :
    (x - (4 * m - 3 : ℤ)) * (x - (4 * m : ℤ)) -
    (x - (4 * m - 2 : ℤ)) * (x - (4 * m - 1 : ℤ)) = -2 := by
  push_cast
  ring

lemma left_index_set_eq :
    (Finset.Icc 1 2016 \ (Finset.Icc 1 2016).filter
      (fun n : ℕ ↦ n % 4 = 2 ∨ n % 4 = 3)) =
      Finset.biUnion (Finset.Icc 1 504) (fun m ↦ {4 * m - 3, 4 * m}) := by
  ext i
  simp only [Finset.mem_sdiff, Finset.mem_Icc, Finset.mem_filter, Finset.mem_biUnion,
    Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨⟨hi1, hi2⟩, hres⟩
    have hmod := Nat.mod_lt i (by omega : 0 < 4)
    have hdiv := Nat.mod_add_div i 4
    interval_cases hr : i % 4
    · refine ⟨i / 4, ?_, Or.inr ?_⟩ <;> omega
    · refine ⟨i / 4 + 1, ?_, Or.inl ?_⟩ <;> omega
    · exact False.elim (hres ⟨⟨hi1, hi2⟩, Or.inl rfl⟩)
    · exact False.elim (hres ⟨⟨hi1, hi2⟩, Or.inr rfl⟩)
  · rintro ⟨m, ⟨hm1, hm2⟩, rfl | rfl⟩
    · constructor
      · omega
      · intro hbad
        omega
    · constructor
      · omega
      · intro hbad
        omega

lemma right_index_set_eq :
    (Finset.Icc 1 2016 \ (Finset.Icc 1 2016).filter
      (fun n : ℕ ↦ n % 4 = 0 ∨ n % 4 = 1)) =
      Finset.biUnion (Finset.Icc 1 504) (fun m ↦ {4 * m - 2, 4 * m - 1}) := by
  ext i
  simp only [Finset.mem_sdiff, Finset.mem_Icc, Finset.mem_filter, Finset.mem_biUnion,
    Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨⟨hi1, hi2⟩, hres⟩
    have hmod := Nat.mod_lt i (by omega : 0 < 4)
    have hdiv := Nat.mod_add_div i 4
    interval_cases hr : i % 4
    · exact False.elim (hres ⟨⟨hi1, hi2⟩, Or.inl rfl⟩)
    · exact False.elim (hres ⟨⟨hi1, hi2⟩, Or.inr rfl⟩)
    · refine ⟨i / 4 + 1, ?_, Or.inl ?_⟩ <;> omega
    · refine ⟨i / 4 + 1, ?_, Or.inr ?_⟩ <;> omega
  · rintro ⟨m, ⟨hm1, hm2⟩, rfl | rfl⟩
    · constructor
      · omega
      · intro hbad
        omega
    · constructor
      · omega
      · intro hbad
        omega

lemma ratio_product_bound (n : ℕ) :
    ∏ j ∈ Finset.Icc 1 n,
        (((4 * j - 1 : ℕ) : ℝ) * (4 * j : ℕ)) /
          (((4 * j - 2 : ℕ) : ℝ) * (4 * j + 1 : ℕ)) < 3 := by
  -- By induction, we can show that the product of the terms up to n is less than or equal to 2 * (4n+1) / (4n+2).
  have h_ind : ∀ n : ℕ, (∏ i ∈ Finset.Icc 1 n, ((4 * i - 1) * (4 * i) : ℚ) / ((4 * i - 2) * (4 * i + 1))) ≤ 2 * (4 * n + 1) / (4 * n + 2) := by
    intro n;
    induction' n with n ih <;> norm_num [ Finset.prod_Ioc_succ_top, (Nat.succ_eq_succ ▸ Finset.Icc_succ_left_eq_Ioc) ] at *;
    rw [ mul_div_mul_comm ];
    refine le_trans ( mul_le_mul_of_nonneg_right ih <| div_nonneg ( by nlinarith ) <| by nlinarith ) ?_;
    rw [div_mul_div_comm, div_le_div_iff₀] <;> ring_nf <;> nlinarith
  -- Apply the induction hypothesis to conclude the proof.
  have h_final : (∏ i ∈ Finset.Icc 1 n, ((4 * i - 1) * (4 * i) : ℚ) / ((4 * i - 2) * (4 * i + 1))) < 3 := by
    exact lt_of_le_of_lt ( h_ind n ) ( by rw [ div_lt_iff₀ ] <;> linarith );
  rw [ Finset.prod_congr rfl fun x hx => by rw [ Nat.cast_sub, Nat.cast_sub ] <;> linarith [ Finset.mem_Icc.mp hx ] ] ; norm_cast at *;

lemma prod_Ico_sub_reindex {α : Type*} [CommMonoid α] (f : ℕ → α) (k : ℕ) :
    ∏ m ∈ Finset.Ico 1 k, f (k - m) = ∏ j ∈ Finset.Icc 1 (k - 1), f j := by
  refine' Finset.prod_bij ( fun m hm => k - m ) _ _ _ _;
  · grind;
  · grind;
  · exact fun b hb => ⟨ k - b, Finset.mem_Ico.mpr ⟨ Nat.sub_pos_of_lt ( Finset.mem_Icc.mp hb |>.2.trans_lt ( Nat.pred_lt ( by aesop_cat ) ) ), Nat.sub_lt ( Nat.pos_of_ne_zero ( by aesop_cat ) ) ( Finset.mem_Icc.mp hb |>.1 ) ⟩, Nat.sub_sub_self ( le_trans ( Finset.mem_Icc.mp hb |>.2 ) ( Nat.pred_le _ ) ) ⟩;
  · exact fun _ _ => rfl

lemma prod_Ioc_sub_reindex {α : Type*} [CommMonoid α] (f : ℕ → α) (n k : ℕ)
    (hk : k ≤ n) :
    ∏ m ∈ Finset.Ioc k n, f (m - k) = ∏ j ∈ Finset.Icc 1 (n - k), f j := by
  refine' Finset.prod_bij ( fun m hm => m - k ) _ _ _ _ <;> simp_all +decide;
  · exact fun a ha₁ ha₂ => Nat.sub_pos_of_lt ha₁;
  · intros; omega;
  · exact fun b hb₁ hb₂ => ⟨ b + k, ⟨ by linarith, by omega ⟩, by omega ⟩

lemma left_product_ratio_lt_three (k : ℕ) (hk : 1 ≤ k) (x : ℝ)
    (hx1 : (4 * k - 2 : ℕ) < x) (_hx2 : x < (4 * k - 1 : ℕ)) :
    (∏ m ∈ Finset.Ico 1 k,
        (x - (4 * m - 2 : ℕ)) * (x - (4 * m - 1 : ℕ))) /
      (∏ m ∈ Finset.Ico 1 k,
        (x - (4 * m - 3 : ℕ)) * (x - (4 * m : ℕ))) < 3 := by
  -- By the properties of the product, we can pair terms $(x-(4m-3))(x-(4m))$ and $(x-(4m-2))(x-(4m-1))$ for $1 \le m \le k-1$.
  have h_prod_pair : (∏ m ∈ Finset.Ico 1 k, ((x - (4 * m - 2 : ℕ)) * (x - (4 * m - 1 : ℕ))) / ((x - (4 * m - 3 : ℕ)) * (x - (4 * m : ℕ)))) < 3 := by
    have h_prod_bound : (∏ m ∈ Finset.Ico 1 k, ((x - (4 * m - 2 : ℕ)) * (x - (4 * m - 1 : ℕ))) / ((x - (4 * m - 3 : ℕ)) * (x - (4 * m : ℕ)))) ≤ (∏ m ∈ Finset.Ico 1 k, ((4 * (k - m) - 1 : ℕ) * (4 * (k - m) : ℕ) : ℝ) / ((4 * (k - m) - 2 : ℕ) * (4 * (k - m) + 1 : ℕ))) := by
      apply Finset.prod_le_prod;
      · intro i hi; rw [ le_div_iff₀ ] <;> norm_num at *;
        · exact mul_nonneg ( sub_nonneg.2 <| le_trans ( mod_cast by omega ) hx1.le ) ( sub_nonneg.2 <| le_trans ( mod_cast by omega ) hx1.le );
        · exact mul_pos ( sub_pos.mpr <| lt_of_le_of_lt ( Nat.cast_le.mpr <| by omega ) hx1 ) ( sub_pos.mpr <| lt_of_le_of_lt ( by norm_cast; omega ) hx1 );
      · intro i hi; rw [ div_le_div_iff₀ ] <;> norm_num at *;
        · repeat rw [ Nat.cast_sub ] at * <;> push_cast at * <;> repeat linarith;
          · nlinarith [ sq_nonneg ( x - ( 4 * i - 2 ) ), sq_nonneg ( x - ( 4 * i - 1 ) ), mul_le_mul_of_nonneg_left ( show ( i : ℝ ) + 1 ≤ k by norm_cast; linarith ) ( sub_nonneg.mpr hx1.le ), mul_le_mul_of_nonneg_left ( show ( i : ℝ ) + 1 ≤ k by norm_cast; linarith ) ( sub_nonneg.mpr _hx2.le ) ];
          · omega;
          · omega;
        · exact mul_pos ( sub_pos.mpr <| lt_of_le_of_lt ( mod_cast by omega ) hx1 ) ( sub_pos.mpr <| lt_of_le_of_lt ( mod_cast by omega ) hx1 );
        · exact mul_pos ( Nat.cast_pos.mpr ( Nat.sub_pos_of_lt ( by omega ) ) ) ( by positivity );
    refine lt_of_le_of_lt h_prod_bound ?_;
    have hreindex := prod_Ico_sub_reindex
      (fun j ↦ (((4 * j - 1 : ℕ) : ℝ) * (4 * j : ℕ)) /
        (((4 * j - 2 : ℕ) : ℝ) * (4 * j + 1 : ℕ))) k
    rw [hreindex]
    exact ratio_product_bound (k - 1)
  rwa [ Finset.prod_div_distrib ] at h_prod_pair

lemma right_product_ratio_lt_three (n k : ℕ) (hk : k ≤ n) (x : ℝ)
    (hx1 : (4 * k - 2 : ℕ) < x) (hx2 : x < (4 * k - 1 : ℕ)) :
    (∏ m ∈ Finset.Ioc k n,
        (x - (4 * m - 2 : ℕ)) * (x - (4 * m - 1 : ℕ))) /
      (∏ m ∈ Finset.Ioc k n,
        (x - (4 * m - 3 : ℕ)) * (x - (4 * m : ℕ))) < 3 := by
  -- Apply the lemma `prod_Ioc_sub_reindex` to rewrite the product.
  have h_prod_Ioc_sub : (∏ m ∈ Finset.Ioc k n, ((x - (4 * m - 2 : ℕ)) * (x - (4 * m - 1 : ℕ))) / ((x - (4 * m - 3 : ℕ)) * (x - (4 * m : ℕ)))) ≤ (∏ j ∈ Finset.Icc 1 (n - k), (((4 * j - 1 : ℕ) : ℝ) * (4 * j : ℕ)) / (((4 * j - 2 : ℕ) : ℝ) * (4 * j + 1 : ℕ))) := by
    -- Apply the lemma `prod_Ioc_sub_reindex` to rewrite the product in terms of `j`.
    have h_prod_Ioc_sub : (∏ m ∈ Finset.Ioc k n, ((x - (4 * m - 2 : ℕ)) * (x - (4 * m - 1 : ℕ))) / ((x - (4 * m - 3 : ℕ)) * (x - (4 * m : ℕ)))) ≤ (∏ j ∈ Finset.Icc 1 (n - k), ((x - (4 * (j + k) - 2 : ℕ)) * (x - (4 * (j + k) - 1 : ℕ))) / ((x - (4 * (j + k) - 3 : ℕ)) * (x - (4 * (j + k) : ℕ)))) := by
      rw [ show Ioc k n = Finset.image ( fun j => j + k ) ( Icc 1 ( n - k ) ) from ?_, Finset.prod_image ] <;> norm_num [ add_comm, hk ];
      exact Eq.symm (Icc_add_one_left_eq_Ioc k n)
    refine le_trans h_prod_Ioc_sub <| Finset.prod_le_prod ?_ ?_ <;> norm_num at *;
    · intro i hi₁ hi₂; rw [ div_nonneg_iff ];
      rcases k with ( _ | k ) <;> rcases i with ( _ | i ) <;> norm_num [ Nat.mul_succ ] at *;
      · linarith;
      · rw [ Nat.cast_sub, Nat.cast_sub ] <;> push_cast <;> repeat linarith;
        exact Or.inl ⟨ by nlinarith [ show ( i : ℝ ) + 1 ≤ n - ( k + 1 ) by exact le_tsub_of_add_le_left ( by norm_cast; omega ) ], by nlinarith [ show ( i : ℝ ) + 1 ≤ n - ( k + 1 ) by exact le_tsub_of_add_le_left ( by norm_cast; omega ) ] ⟩;
    · intro i hi₁ hi₂; rcases i with ( _ | i ) <;> rcases k with ( _ | k ) <;> norm_num [ Nat.mul_succ ] at *;
      · linarith;
      · rw [ div_le_iff₀ ] <;> ring_nf at *;
        · rw [ Nat.cast_sub, Nat.cast_sub ] <;> push_cast <;> try linarith;
          field_simp;
          nlinarith [ sq_nonneg ( x - ( 3 + k * 4 ) ), mul_le_mul_of_nonneg_left hx2.le ( sq_nonneg ( i : ℝ ) ), mul_le_mul_of_nonneg_left hx1.le ( sq_nonneg ( i : ℝ ) ), mul_le_mul_of_nonneg_left hx2.le ( sq_nonneg ( k : ℝ ) ), mul_le_mul_of_nonneg_left hx1.le ( sq_nonneg ( k : ℝ ) ) ];
        · rw [ Nat.cast_sub ] <;> push_cast <;> nlinarith only [ hx1, hx2 ] ;
  rw [Finset.prod_div_distrib] at h_prod_Ioc_sub
  exact lt_of_le_of_lt h_prod_Ioc_sub (ratio_product_bound (n - k))

lemma alternating_block_products (n : ℕ) (hn : 0 < n) (x : ℝ) :
    ∏ m ∈ Finset.Icc 1 n,
        (x - (4 * m - 3 : ℕ)) * (x - (4 * m : ℕ)) <
      ∏ m ∈ Finset.Icc 1 n,
        (x - (4 * m - 2 : ℕ)) * (x - (4 * m - 1 : ℕ)) := by
  sorry

/-
The main no-real-solution result
Strategy: if such x exists, consider cases.
Case 1: x = n for some n ∈ {1..2016} with n%4=0 or n%4=1.
Then left product = 0. But right product ≠ 0 since n%4≠2,3.
Case 2: x = n for some n ∈ {1..2016} with n%4=2 or n%4=3.
Then right product = 0. But left product ≠ 0 since n%4≠0,1.
Case 3: x is not of the form n for n ∈ {1..2016}.
Then both products are nonzero. Use the algebraic structure:
Writing P = ∏_m L_m, Q = ∏_m R_m where L_m = (x-(4m-3))(x-4m), R_m = (x-(4m-2))(x-(4m-1)).
R_m = L_m + 2 always. So Q - P = ∑ telescoping terms with factor 2 everywhere.
This is nonzero because all L_m, R_m are nonzero (x not in {1..2016}),
and a product of (L_m+2) ≠ product of L_m when each L_m is nonzero.
(If all L_m > 0: Q > P. If some negative: more careful, but can be handled.)
-/
theorem no_real_solution :
    ¬∃ x : ℝ,
      ∏ i ∈ (Finset.Icc 1 2016 \ (Finset.Icc 1 2016).filter (fun n : ℕ ↦ n % 4 = 2 ∨ n % 4 = 3)),
          (x - (i : ℝ)) =
      ∏ i ∈ (Finset.Icc 1 2016 \ (Finset.Icc 1 2016).filter (fun n : ℕ ↦ n % 4 = 0 ∨ n % 4 = 1)),
          (x - (i : ℝ)) := by
  -- The two index sets (remaining factors) are disjoint.
  -- Left index set A = {j ∈ 1..2016 | j%4 = 0 or j%4 = 1}
  -- Right index set B = {j ∈ 1..2016 | j%4 = 2 or j%4 = 3}
  -- If x ∈ A (as real cast of nat), left = 0 but right ≠ 0 (since j%4 ≠ 2,3 for j in A).
  -- If x ∈ B, right = 0 but left ≠ 0.
  -- If x ∉ A ∪ B: both sides nonzero, use key identity per quadruple.
  rintro ⟨ x, hx ⟩;
  rw [ left_index_set_eq, right_index_set_eq ] at hx;
  rw [ Finset.prod_biUnion, Finset.prod_biUnion ] at hx;
  · convert alternating_block_products 504 ( by norm_num ) x using 1;
    rw [ Finset.prod_congr rfl fun i hi => Finset.prod_pair <| by linarith [ Finset.mem_Icc.mp hi, Nat.sub_add_cancel ( by linarith [ Finset.mem_Icc.mp hi ] : 3 ≤ 4 * i ) ], Finset.prod_congr rfl fun i hi => Finset.prod_pair <| by linarith [ Finset.mem_Icc.mp hi, Nat.sub_add_cancel ( by linarith [ Finset.mem_Icc.mp hi ] : 2 ≤ 4 * i ), Nat.sub_add_cancel ( by linarith [ Finset.mem_Icc.mp hi ] : 1 ≤ 4 * i ) ] ] at hx ; aesop;
  · exact fun a ha b hb hab => Finset.disjoint_left.mpr fun x hx₁ hx₂ => hab <| by norm_num at *; omega;
  · exact fun a ha b hb hab => Finset.disjoint_left.mpr fun x hx₁ hx₂ => hab <| by norm_num at *; omega;

end Imo2016P5