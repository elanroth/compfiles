/-
Copyright (c) 2023 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Olympiad 2016, Problem 5

The equation

  (x - 1)(x - 2) ... (x - 2016) = (x - 1)(x - 2) ... (x - 2016)

is written on the board. What is the least possible value of k
for which it is possible to erase exactly k of these 4032 factors
such that at least one factor remains on each side and the resulting
equation has no real solutions?
-/

namespace Imo2016P5

snip begin

lemma lemma1 {α : Type*} [DecidableEq α] (s : Finset α) (p : α → Prop) [DecidablePred p] :
    Finset.card (s \ s.filter p) + Finset.card (s.filter p) = Finset.card s :=
  Finset.card_sdiff_add_card_eq_card (Finset.filter_subset p s)

snip end

snip begin

open Finset BigOperators

set_option maxHeartbeats 800000

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
    intro n
    induction' n with n ih <;> norm_num [Finset.prod_Ioc_succ_top, (Nat.succ_eq_succ ▸ Finset.Icc_succ_left_eq_Ioc)] at *
    rw [mul_div_mul_comm]
    refine le_trans (mul_le_mul_of_nonneg_right ih <| div_nonneg (by nlinarith) <| by nlinarith) ?_
    rw [div_mul_div_comm, div_le_div_iff₀] <;> ring_nf <;> nlinarith
  -- Apply the induction hypothesis to conclude the proof.
  have h_final : (∏ i ∈ Finset.Icc 1 n, ((4 * i - 1) * (4 * i) : ℚ) / ((4 * i - 2) * (4 * i + 1))) < 3 := by
    exact lt_of_le_of_lt (h_ind n) (by rw [div_lt_iff₀] <;> linarith)
  rw [Finset.prod_congr rfl fun x hx => by rw [Nat.cast_sub, Nat.cast_sub] <;> linarith [Finset.mem_Icc.mp hx]] ; norm_cast at *

lemma prod_Ico_sub_reindex {α : Type*} [CommMonoid α] (f : ℕ → α) (k : ℕ) :
    ∏ m ∈ Finset.Ico 1 k, f (k - m) = ∏ j ∈ Finset.Icc 1 (k - 1), f j := by
  refine Finset.prod_bij (fun m hm => k - m) ?_ ?_ ?_ ?_
  · grind
  · grind
  · exact fun b hb => ⟨k - b, Finset.mem_Ico.mpr ⟨Nat.sub_pos_of_lt (Finset.mem_Icc.mp hb |>.2.trans_lt (Nat.pred_lt (by aesop_cat))), Nat.sub_lt (Nat.pos_of_ne_zero (by aesop_cat)) (Finset.mem_Icc.mp hb |>.1)⟩, Nat.sub_sub_self (le_trans (Finset.mem_Icc.mp hb |>.2) (Nat.pred_le _))⟩
  · exact fun _ _ => rfl

lemma prod_Ioc_sub_reindex {α : Type*} [CommMonoid α] (f : ℕ → α) (n k : ℕ)
    (hk : k ≤ n) :
    ∏ m ∈ Finset.Ioc k n, f (m - k) = ∏ j ∈ Finset.Icc 1 (n - k), f j := by
  refine Finset.prod_bij (fun m hm => m - k) ?_ ?_ ?_ ?_ <;> simp_all +decide
  · exact fun a ha₁ ha₂ => Nat.sub_pos_of_lt ha₁
  · intros; omega
  · exact fun b hb₁ hb₂ => ⟨b + k, ⟨by linarith, by omega⟩, by omega⟩

lemma left_product_ratio_lt_three (k : ℕ) (hk : 1 ≤ k) (x : ℝ)
    (hx1 : (4 * k - 2 : ℕ) < x) (_hx2 : x < (4 * k - 1 : ℕ)) :
    (∏ m ∈ Finset.Ico 1 k,
        (x - (4 * m - 2 : ℕ)) * (x - (4 * m - 1 : ℕ))) /
      (∏ m ∈ Finset.Ico 1 k,
        (x - (4 * m - 3 : ℕ)) * (x - (4 * m : ℕ))) < 3 := by
  -- By the properties of the product, we can pair terms $(x-(4m-3))(x-(4m))$ and $(x-(4m-2))(x-(4m-1))$ for $1 \le m \le k-1$.
  have h_prod_pair : (∏ m ∈ Finset.Ico 1 k, ((x - (4 * m - 2 : ℕ)) * (x - (4 * m - 1 : ℕ))) / ((x - (4 * m - 3 : ℕ)) * (x - (4 * m : ℕ)))) < 3 := by
    have h_prod_bound : (∏ m ∈ Finset.Ico 1 k, ((x - (4 * m - 2 : ℕ)) * (x - (4 * m - 1 : ℕ))) / ((x - (4 * m - 3 : ℕ)) * (x - (4 * m : ℕ)))) ≤ (∏ m ∈ Finset.Ico 1 k, ((4 * (k - m) - 1 : ℕ) * (4 * (k - m) : ℕ) : ℝ) / ((4 * (k - m) - 2 : ℕ) * (4 * (k - m) + 1 : ℕ))) := by
      apply Finset.prod_le_prod
      · intro i hi; rw [le_div_iff₀] <;> norm_num at *
        · exact mul_nonneg (sub_nonneg.2 <| le_trans (mod_cast by omega) hx1.le) (sub_nonneg.2 <| le_trans (mod_cast by omega) hx1.le)
        · exact mul_pos (sub_pos.mpr <| lt_of_le_of_lt (Nat.cast_le.mpr <| by omega) hx1) (sub_pos.mpr <| lt_of_le_of_lt (by norm_cast; omega) hx1)
      · intro i hi; rw [div_le_div_iff₀] <;> norm_num at *
        · repeat rw [Nat.cast_sub] at * <;> push_cast at * <;> repeat linarith
          · nlinarith [sq_nonneg (x - (4 * i - 2)), sq_nonneg (x - (4 * i - 1)), mul_le_mul_of_nonneg_left (show (i : ℝ) + 1 ≤ k by norm_cast; linarith) (sub_nonneg.mpr hx1.le), mul_le_mul_of_nonneg_left (show (i : ℝ) + 1 ≤ k by norm_cast; linarith) (sub_nonneg.mpr _hx2.le)]
          · omega
          · omega
        · exact mul_pos (sub_pos.mpr <| lt_of_le_of_lt (mod_cast by omega) hx1) (sub_pos.mpr <| lt_of_le_of_lt (mod_cast by omega) hx1)
        · exact mul_pos (Nat.cast_pos.mpr (Nat.sub_pos_of_lt (by omega))) (by positivity)
    refine lt_of_le_of_lt h_prod_bound ?_
    have hreindex := prod_Ico_sub_reindex
      (fun j ↦ (((4 * j - 1 : ℕ) : ℝ) * (4 * j : ℕ)) /
        (((4 * j - 2 : ℕ) : ℝ) * (4 * j + 1 : ℕ))) k
    rw [hreindex]
    exact ratio_product_bound (k - 1)
  rwa [Finset.prod_div_distrib] at h_prod_pair

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
      rw [show Ioc k n = Finset.image (fun j => j + k) (Icc 1 (n - k)) from ?_, Finset.prod_image] <;> norm_num [add_comm, hk]
      exact Eq.symm (Icc_add_one_left_eq_Ioc k n)
    refine le_trans h_prod_Ioc_sub <| Finset.prod_le_prod ?_ ?_ <;> norm_num at *
    · intro i hi₁ hi₂; rw [div_nonneg_iff]
      rcases k with (_ | k) <;> rcases i with (_ | i) <;> norm_num [Nat.mul_succ] at *
      · linarith
      · rw [Nat.cast_sub, Nat.cast_sub] <;> push_cast <;> repeat linarith
        exact Or.inl ⟨by nlinarith [show (i : ℝ) + 1 ≤ n - (k + 1) by exact le_tsub_of_add_le_left (by norm_cast; omega)], by nlinarith [show (i : ℝ) + 1 ≤ n - (k + 1) by exact le_tsub_of_add_le_left (by norm_cast; omega)]⟩
    · intro i hi₁ hi₂; rcases i with (_ | i) <;> rcases k with (_ | k) <;> norm_num [Nat.mul_succ] at *
      · linarith
      · rw [div_le_iff₀] <;> ring_nf at *
        · rw [Nat.cast_sub, Nat.cast_sub] <;> push_cast <;> try linarith
          field_simp
          nlinarith [sq_nonneg (x - (3 + k * 4)), mul_le_mul_of_nonneg_left hx2.le (sq_nonneg (i : ℝ)), mul_le_mul_of_nonneg_left hx1.le (sq_nonneg (i : ℝ)), mul_le_mul_of_nonneg_left hx2.le (sq_nonneg (k : ℝ)), mul_le_mul_of_nonneg_left hx1.le (sq_nonneg (k : ℝ))]
        · rw [Nat.cast_sub] <;> push_cast <;> nlinarith only [hx1, hx2]
  rw [Finset.prod_div_distrib] at h_prod_Ioc_sub
  exact lt_of_le_of_lt h_prod_Ioc_sub (ratio_product_bound (n - k))

lemma alternating_block_products_difficult (n k : ℕ) (hk1 : 1 ≤ k) (hkn : k ≤ n)
    (x : ℝ) (hx1 : (4 * k - 2 : ℕ) < x) (hx2 : x < (4 * k - 1 : ℕ)) :
    ∏ m ∈ Finset.Icc 1 n,
        (x - (4 * m - 3 : ℕ)) * (x - (4 * m : ℕ)) <
      ∏ m ∈ Finset.Icc 1 n,
        (x - (4 * m - 2 : ℕ)) * (x - (4 * m - 1 : ℕ)) := by
  -- Split the product into two parts: before k and after k.
  have h_split : (∏ m ∈ Finset.Icc 1 n, (x - (4 * m - 2 : ℕ)) * (x - (4 * m - 1 : ℕ))) /
                  (∏ m ∈ Finset.Icc 1 n, (x - (4 * m - 3 : ℕ)) * (x - (4 * m : ℕ))) =
                  ((∏ m ∈ Finset.Ico 1 k, (x - (4 * m - 2 : ℕ)) * (x - (4 * m - 1 : ℕ))) /
                  (∏ m ∈ Finset.Ico 1 k, (x - (4 * m - 3 : ℕ)) * (x - (4 * m : ℕ)))) *
                  ((x - (4 * k - 2 : ℕ)) * (x - (4 * k - 1 : ℕ))) /
                  ((x - (4 * k - 3 : ℕ)) * (x - (4 * k : ℕ))) *
                  ((∏ m ∈ Finset.Ico (k + 1) (n + 1), (x - (4 * m - 2 : ℕ)) * (x - (4 * m - 1 : ℕ))) /
                  (∏ m ∈ Finset.Ico (k + 1) (n + 1), (x - (4 * m - 3 : ℕ)) * (x - (4 * m : ℕ)))) := by
                    have h_split : Finset.Icc 1 n = Finset.Ico 1 k ∪ {k} ∪ Finset.Ico (k + 1) (n + 1) := by
                      grind
                    rw [h_split, Finset.prod_union, Finset.prod_union, Finset.prod_union] <;> norm_num
                    · grind
                    · exact Finset.disjoint_left.mpr fun x hx₁ hx₂ => by linarith [Finset.mem_Ico.mp hx₁, Finset.mem_Ico.mp hx₂]
                    · exact Finset.disjoint_left.mpr fun x hx₁ hx₂ => by linarith [Finset.mem_Ico.mp hx₁, Finset.mem_Ico.mp hx₂]
  -- By the properties of the product, we can split the inequality into two parts.
  have h_prod_split : ((∏ m ∈ Finset.Ico 1 k, (x - (4 * m - 2 : ℕ)) * (x - (4 * m - 1 : ℕ))) /
                      (∏ m ∈ Finset.Ico 1 k, (x - (4 * m - 3 : ℕ)) * (x - (4 * m : ℕ)))) *
                      ((x - (4 * k - 2 : ℕ)) * (x - (4 * k - 1 : ℕ))) /
                      ((x - (4 * k - 3 : ℕ)) * (x - (4 * k : ℕ))) *
                      ((∏ m ∈ Finset.Ico (k + 1) (n + 1), (x - (4 * m - 2 : ℕ)) * (x - (4 * m - 1 : ℕ))) /
                      (∏ m ∈ Finset.Ico (k + 1) (n + 1), (x - (4 * m - 3 : ℕ)) * (x - (4 * m : ℕ)))) < 1 := by
                        -- By the properties of the product, we can bound each part separately.
                        have h_bound : ((∏ m ∈ Finset.Ico 1 k, (x - (4 * m - 2 : ℕ)) * (x - (4 * m - 1 : ℕ))) /
                                       (∏ m ∈ Finset.Ico 1 k, (x - (4 * m - 3 : ℕ)) * (x - (4 * m : ℕ)))) < 3 ∧
                                       ((∏ m ∈ Finset.Ico (k + 1) (n + 1), (x - (4 * m - 2 : ℕ)) * (x - (4 * m - 1 : ℕ))) /
                                       (∏ m ∈ Finset.Ico (k + 1) (n + 1), (x - (4 * m - 3 : ℕ)) * (x - (4 * m : ℕ)))) < 3 ∧
                                       ((x - (4 * k - 2 : ℕ)) * (x - (4 * k - 1 : ℕ))) /
                                       ((x - (4 * k - 3 : ℕ)) * (x - (4 * k : ℕ))) ≤ 1 / 9 := by
                                         refine ⟨?_, ?_, ?_⟩
                                         · convert left_product_ratio_lt_three k hk1 x hx1 hx2 using 1
                                         · convert right_product_ratio_lt_three n k hkn x hx1 hx2 using 1
                                           grind +suggestions
                                         · rw [div_le_iff_of_neg] <;> norm_num [Nat.cast_sub (by linarith : 2 ≤ 4 * k), Nat.cast_sub (by linarith : 1 ≤ 4 * k), Nat.cast_sub (by linarith : 3 ≤ 4 * k)] at *
                                           · nlinarith [sq_nonneg (x - (4 * k - 2) - 1 / 2)]
                                           · nlinarith
                        simp_all +decide [mul_div_assoc]
                        refine lt_of_le_of_lt (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h_bound.2.2 ?_) ?_) ?_
                        · refine div_nonneg ?_ ?_ <;> refine Finset.prod_nonneg fun m hm => ?_ <;> norm_num at *
                          · exact mul_nonneg (sub_nonneg.2 <| le_trans (Nat.cast_le.2 <| by omega) hx1.le) (sub_nonneg.2 <| le_trans (Nat.cast_le.2 <| by omega) hx1.le)
                          · exact mul_nonneg (sub_nonneg.2 <| le_trans (mod_cast by omega) hx1.le) (sub_nonneg.2 <| le_trans (mod_cast by omega) hx1.le)
                        · refine div_nonneg ?_ ?_ <;> refine Finset.prod_nonneg fun m hm => ?_ <;> norm_num at *
                          · rw [Nat.cast_sub, Nat.cast_sub] at * <;> push_cast at * <;> repeat linarith
                            nlinarith [show (m : ℝ) ≥ k + 1 by norm_cast; linarith]
                          · rw [Nat.cast_sub] at * <;> push_cast at * <;> repeat linarith
                            nlinarith [show (m : ℝ) ≥ k + 1 by norm_cast; linarith]
                        · refine lt_of_le_of_lt (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h_bound.1.le (by norm_num)) (?_)) ?_
                          · refine div_nonneg ?_ ?_
                            · refine Finset.prod_nonneg fun m hm => mul_nonneg_of_nonpos_of_nonpos ?_ ?_ <;> norm_num at *
                              · exact hx2.le.trans (mod_cast by omega)
                              · exact hx2.le.trans (mod_cast Nat.sub_le_sub_right (by linarith) _)
                            · refine Finset.prod_nonneg fun m hm => ?_
                              rw [Nat.cast_sub] <;> push_cast <;> repeat linarith [Finset.mem_Ico.mp hm]
                              rw [Nat.cast_sub] at * <;> push_cast at * <;> repeat linarith
                              nlinarith [show (m : ℝ) ≥ k + 1 by norm_cast; linarith [Finset.mem_Ico.mp hm]]
                          · grind +splitIndPred
  rw [div_eq_iff] at h_split
  · -- By the properties of the product, we can split the inequality into two parts and apply the results from h_prod_split.
    have h_prod_neg : (∏ m ∈ Finset.Icc 1 n, (x - (4 * m - 3 : ℕ)) * (x - (4 * m : ℕ))) < 0 := by
      rw [Finset.prod_eq_prod_diff_singleton_mul
        (Finset.mem_Icc.mpr ⟨hk1, hkn⟩), mul_comm]
      refine mul_neg_of_neg_of_pos ?_ ?_
      · rcases k with (_ | _ | k) <;> norm_num [Nat.mul_succ] at *; all_goals nlinarith
      · refine Finset.prod_pos fun m hm => ?_
        by_cases hmk : m < k
        · rw [Nat.cast_sub, Nat.cast_sub] at * <;> push_cast at *
          any_goals linarith [Finset.mem_Icc.mp (Finset.mem_sdiff.mp hm |>.1)]
          nlinarith [show (m : ℝ) + 1 ≤ k by norm_cast]
        · norm_num at *
          rw [Nat.cast_sub] at * <;> push_cast at * <;> repeat linarith
          nlinarith [show (m : ℝ) ≥ k + 1 by exact_mod_cast lt_of_le_of_ne hmk (Ne.symm hm.2)]
    nlinarith
  · refine Finset.prod_ne_zero_iff.mpr ?_
    intro m hm; rcases lt_trichotomy m k with (H | rfl | H) <;> norm_num at *
    · constructor <;> rw [Nat.cast_sub] at * <;> push_cast at * <;> repeat linarith
      · linarith [show (m : ℝ) + 1 ≤ k by norm_cast]
      · linarith [show (m : ℝ) + 1 ≤ k by norm_cast]
    · constructor <;> rw [Nat.cast_sub] at * <;> push_cast at * <;> linarith
    · constructor <;> rw [Nat.cast_sub] at * <;> push_cast at * <;> linarith [show (m : ℝ) ≥ k + 1 by norm_cast]

lemma alternating_block_products_easy (n : ℕ) (hn : 0 < n) (x : ℝ)
    (hx : ¬∃ k : ℕ, 1 ≤ k ∧ k ≤ n ∧
      (4 * k - 2 : ℕ) < x ∧ x < (4 * k - 1 : ℕ)) :
    ∏ m ∈ Finset.Icc 1 n,
        (x - (4 * m - 3 : ℕ)) * (x - (4 * m : ℕ)) <
      ∏ m ∈ Finset.Icc 1 n,
        (x - (4 * m - 2 : ℕ)) * (x - (4 * m - 1 : ℕ)) := by
  by_cases h : ∃ k : ℕ, 1 ≤ k ∧ k ≤ n ∧ (4 * k - 3 : ℤ) < x ∧ x < (4 * k : ℤ)
  · obtain ⟨k, hk₁, hk₂, hk₃, hk₄⟩ := h; have h_neg : (x - (4 * k - 3 : ℤ)) * (x - (4 * k : ℤ)) < 0 := by
      exact mul_neg_of_pos_of_neg (sub_pos.mpr hk₃) (sub_neg.mpr hk₄); ; (
    -- Since $x$ is in the interval $(4k-3, 4k)$, we have $(x - (4k-2))(x - (4k-1)) \geq 0$.
    have h_nonneg : (x - (4 * k - 2 : ℤ)) * (x - (4 * k - 1 : ℤ)) ≥ 0 := by
      norm_num at *
      contrapose! hx
      exact ⟨k, hk₁, hk₂, by rw [Nat.cast_sub] <;> push_cast <;> nlinarith, by rw [Nat.cast_sub] <;> push_cast <;> nlinarith⟩
    -- Since $x$ is in the interval $(4k-3, 4k)$, we have $(x - (4m-3))(x - 4m) > 0$ for all $m \neq k$.
    have h_pos : ∀ m ∈ Finset.Icc 1 n \ {k}, (x - (4 * m - 3 : ℤ)) * (x - (4 * m : ℤ)) > 0 ∧ (x - (4 * m - 2 : ℤ)) * (x - (4 * m - 1 : ℤ)) > 0 := by
      intro m hm; rcases lt_trichotomy m k with (H | rfl | H) <;> norm_num at *
      · constructor <;> nlinarith [show (m : ℝ) + 1 ≤ k by norm_cast]
      · constructor <;> nlinarith [show (m : ℝ) ≥ k + 1 by norm_cast]
    rw [← Finset.mul_prod_erase _ _ (show k ∈ Finset.Icc 1 n from Finset.mem_Icc.mpr ⟨hk₁, hk₂⟩), ← Finset.mul_prod_erase _ _ (show k ∈ Finset.Icc 1 n from Finset.mem_Icc.mpr ⟨hk₁, hk₂⟩)]
    refine lt_of_lt_of_le ?_ (mul_nonneg ?_ ?_) <;> norm_num at *
    · exact mul_neg_of_neg_of_pos (by rw [Nat.cast_sub (by linarith)] ; push_cast; linarith) (Finset.prod_pos fun m hm => by rw [Nat.cast_sub (by linarith [Finset.mem_Icc.mp (Finset.mem_of_mem_erase hm)])] ; push_cast; linarith [h_pos m (Finset.mem_Icc.mp (Finset.mem_of_mem_erase hm) |>.1) (Finset.mem_Icc.mp (Finset.mem_of_mem_erase hm) |>.2) (by aesop)])
    · rw [Nat.cast_sub, Nat.cast_sub] <;> push_cast <;> linarith
    · exact Finset.prod_nonneg fun m hm => by rw [Nat.cast_sub (by linarith [Finset.mem_Icc.mp (Finset.mem_of_mem_erase hm)]), Nat.cast_sub (by linarith [Finset.mem_Icc.mp (Finset.mem_of_mem_erase hm)])] ; push_cast ; linarith [h_pos m (Finset.mem_Icc.mp (Finset.mem_of_mem_erase hm) |>.1) (Finset.mem_Icc.mp (Finset.mem_of_mem_erase hm) |>.2) (by aesop)] ;)
  · -- Otherwise every left block is nonnegative. Since each right block equals left block + 2, use strict product comparison; carefully handle a zero left factor separately, showing the right product is positive.
    by_cases h_zero_left : ∃ k : ℕ, 1 ≤ k ∧ k ≤ n ∧ (x - (4 * k - 3 : ℕ)) * (x - (4 * k : ℕ)) = 0
    · obtain ⟨k, hk₁, hk₂, hk₃⟩ := h_zero_left; simp_all +decide [Finset.prod_eq_zero (Finset.mem_Icc.mpr ⟨hk₁, hk₂⟩)]
      refine Finset.prod_pos fun m hm => ?_
      rcases hk₃ with (hk₃ | hk₃) <;> rcases eq_or_ne m k with (rfl | hne) <;> simp_all +decide [sub_eq_iff_eq_add]
      · rcases m with (_ | _ | m) <;> norm_num [Nat.mul_succ] at * ; linarith
      · rw [Nat.cast_sub, Nat.cast_sub, Nat.cast_sub] <;> push_cast <;> try linarith
        by_cases hmk : m < k
        · nlinarith [show (m : ℝ) + 1 ≤ k by norm_cast]
        · nlinarith [show (m : ℝ) ≥ k + 1 by exact_mod_cast lt_of_le_of_ne (le_of_not_gt hmk) (Ne.symm hne)]
      · rw [Nat.cast_sub, Nat.cast_sub] <;> push_cast <;> nlinarith [show (m : ℝ) ≥ 1 by norm_cast]
      · rcases m with (_ | _ | m) <;> rcases k with (_ | _ | k) <;> norm_num [Nat.mul_succ] at *
        · nlinarith
        · nlinarith
        · by_cases hmk : m < k
          · nlinarith only [show (m : ℝ) + 1 ≤ k by norm_cast]
          · nlinarith [show (m : ℝ) ≥ k + 1 by exact_mod_cast lt_of_le_of_ne (le_of_not_gt hmk) (Ne.symm hne)]
    · -- Since each left block is nonnegative and not zero, each left block is positive.
      have h_pos_left : ∀ k : ℕ, 1 ≤ k ∧ k ≤ n → 0 < (x - (4 * k - 3 : ℕ)) * (x - (4 * k : ℕ)) := by
        simp +zetaDelta at *
        intro k hk₁ hk₂; specialize h_zero_left k hk₁ hk₂; specialize h k hk₁ hk₂; rcases lt_trichotomy x (4 * k - 3) with hx₁ | rfl | hx₂ <;> norm_num at *
        · rw [Nat.cast_sub] <;> push_cast <;> nlinarith [show (k : ℝ) ≥ 1 by norm_cast]
        · exact False.elim <| h_zero_left <| by rw [Nat.cast_sub] <;> push_cast <;> linarith
        · exact mul_pos (sub_pos.mpr <| by rw [Nat.cast_sub] <;> push_cast <;> linarith) (lt_of_le_of_ne (sub_nonneg.mpr <| h hx₂) <| Ne.symm h_zero_left.2)
      fapply Finset.prod_lt_prod
      · intro k hk
        exact h_pos_left k (Finset.mem_Icc.mp hk)
      · intro k hk
        have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
        rw [Nat.cast_sub (by omega : 3 ≤ 4 * k),
          Nat.cast_sub (by omega : 2 ≤ 4 * k), Nat.cast_sub (by omega : 1 ≤ 4 * k)]
        push_cast
        nlinarith
      · refine ⟨1, Finset.mem_Icc.mpr ⟨by norm_num, hn⟩, ?_⟩
        specialize h_pos_left 1 ⟨by norm_num, hn⟩
        norm_num at h_pos_left ⊢
        nlinarith

lemma alternating_block_products (n : ℕ) (hn : 0 < n) (x : ℝ) :
    ∏ m ∈ Finset.Icc 1 n,
        (x - (4 * m - 3 : ℕ)) * (x - (4 * m : ℕ)) <
      ∏ m ∈ Finset.Icc 1 n,
        (x - (4 * m - 2 : ℕ)) * (x - (4 * m - 1 : ℕ)) := by
  by_cases hx : ∃ k : ℕ, 1 ≤ k ∧ k ≤ n ∧
      (4 * k - 2 : ℕ) < x ∧ x < (4 * k - 1 : ℕ)
  · obtain ⟨k, hk1, hkn, hx1, hx2⟩ := hx
    exact alternating_block_products_difficult n k hk1 hkn x hx1 hx2
  · exact alternating_block_products_easy n hn x hx

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
  rintro ⟨x, hx⟩
  rw [left_index_set_eq, right_index_set_eq] at hx
  rw [Finset.prod_biUnion, Finset.prod_biUnion] at hx
  · convert alternating_block_products 504 (by norm_num) x using 1
    rw [Finset.prod_congr rfl fun i hi => Finset.prod_pair <| by linarith [Finset.mem_Icc.mp hi, Nat.sub_add_cancel (by linarith [Finset.mem_Icc.mp hi] : 3 ≤ 4 * i)], Finset.prod_congr rfl fun i hi => Finset.prod_pair <| by linarith [Finset.mem_Icc.mp hi, Nat.sub_add_cancel (by linarith [Finset.mem_Icc.mp hi] : 2 ≤ 4 * i), Nat.sub_add_cancel (by linarith [Finset.mem_Icc.mp hi] : 1 ≤ 4 * i)]] at hx ; aesop
  · exact fun a ha b hb hab => Finset.disjoint_left.mpr fun x hx₁ hx₂ => hab <| by norm_num at *; omega
  · exact fun a ha b hb hab => Finset.disjoint_left.mpr fun x hx₁ hx₂ => hab <| by norm_num at *; omega

snip end

determine solution_value : ℕ := 2016

problem imo2016_p5 :
    IsLeast { k | ∃ L R : Finset ℕ,
                  L ⊂ Finset.Icc 1 2016 ∧
                  R ⊂ Finset.Icc 1 2016 ∧
                  L.card + R.card = k ∧
                  ¬∃ x : ℝ,
                   ∏ i ∈ Finset.Icc 1 2016 \ L, (x - (i : ℝ)) =
                   ∏ i ∈ Finset.Icc 1 2016 \ R, (x - (i : ℝ)) }
            solution_value := by
  constructor
  · rw [Set.mem_setOf_eq]
    -- We follow the proof from Evan Chen:
    -- https://web.evanchen.cc/exams/IMO-2016-notes.pdf
    use (Finset.Icc 1 2016).filter (fun n ↦ n % 4 = 2 ∨ n % 4 = 3)
    use (Finset.Icc 1 2016).filter (fun n ↦ n % 4 = 0 ∨ n % 4 = 1)
    have hp : ∀ n, (n % 4 = 2 ∨ n % 4 = 3) = ¬(n % 4 = 0 ∨ n % 4 = 1) := by lia
    refine ⟨?_, ?_, ?_, ?_⟩
    · refine ⟨Finset.filter_subset _ _, ?_⟩
      intro h
      have h1 : 1 ∈ Finset.Icc 1 2016 := by decide
      have h2 := h h1
      simp [Finset.mem_Icc, Finset.mem_filter] at h2
    · refine ⟨Finset.filter_subset _ _, ?_⟩
      intro h
      have h1 : 2 ∈ Finset.Icc 1 2016 := by decide
      have h2 := h h1
      simp only [Finset.mem_Icc, Finset.mem_filter] at h2
      norm_num at h2
    · simp_rw [hp]; rw [Finset.filter_not, lemma1]; simp
    · exact no_real_solution
  · rw [mem_lowerBounds]
    intro j hj
    by_contra! H
    rw [Set.mem_setOf_eq] at hj
    obtain ⟨L, R, hL, hR, hcard, hLR⟩ := hj
    have h1 : ∃ i, i ∈ Finset.Icc 1 2016 ∧ i ∉ L ∧ i ∉ R := by
      by_contra! H2
      have h2 : Finset.card (L ∪ R) ≤ L.card + R.card := Finset.card_union_le L R
      have h3 : Finset.Icc 1 2016 ⊆ (L ∪ R) := fun a ha ↦ by
        specialize H2 a ha
        rw [←or_iff_not_imp_left] at H2
        exact Finset.mem_union.mpr H2
      have h4 : (Finset.Icc 1 2016).card ≤ (L ∪ R).card := Finset.card_le_card h3
      rw [Nat.card_Icc, add_tsub_cancel_right] at h4
      rw [←hcard] at H
      exact ((h4.trans h2).trans_lt H).false
    obtain ⟨i, hic, hiL, hiR⟩ := h1
    push Not at hLR
    specialize hLR i
    have hic1 : i ∈ Finset.Icc 1 2016 \ L := by
      rw [Finset.mem_sdiff]; exact ⟨hic, hiL⟩
    have hic2 : i ∈ Finset.Icc 1 2016 \ R := by
      rw [Finset.mem_sdiff]; exact ⟨hic, hiR⟩
    rw [←Finset.prod_erase_mul _ _ hic1, ←Finset.prod_erase_mul _ _ hic2] at hLR
    simp at hLR

end Imo2016P5
