/-
Copyright (c) 2023 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

import Mathlib

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

lemma lemma1 {α : Type*} [DecidableEq α] (s : Finset α) (p : α → Prop) [DecidablePred p] :
    Finset.card (s \ s.filter p) + Finset.card (s.filter p) = Finset.card s :=
  Finset.card_sdiff_add_card_eq_card (Finset.filter_subset p s)

/-- For each block k, the "right pair" minus "left pair" equals 2. -/
lemma block_diff (x : ℝ) (k : ℕ) :
    (x - (4 * (k : ℝ) + 2)) * (x - (4 * k + 3)) -
    (x - (4 * k + 1)) * (x - (4 * k + 4)) = 2 := by
  ring

/-- The product over i%4 ∈ {0,1} equals the product over blocks of (x-4k-1)(x-4k-4). -/
lemma left_prod_eq_block_prod (x : ℝ) :
    ∏ i ∈ (Finset.Icc (1 : ℕ) 2016) \
      (Finset.Icc (1 : ℕ) 2016).filter (fun n ↦ n % 4 = 2 ∨ n % 4 = 3), (x - (i : ℝ)) =
    ∏ k ∈ Finset.range 504, ((x - (4 * (k : ℝ) + 1)) * (x - (4 * k + 4))) := by
  have h_prod_split : Finset.Icc (1 : ℕ) 2016 \ Finset.filter (fun n => n % 4 = 2 ∨ n % 4 = 3) (Finset.Icc 1 2016) = Finset.biUnion (Finset.range 504) (fun k => {4 * k + 1, 4 * k + 4}) := by
    native_decide +revert;
  rw [ h_prod_split, Finset.prod_biUnion ];
  · norm_num +zetaDelta at *;
  · intros k hk l hl hkl; simp [Finset.disjoint_left, Finset.mem_insert, Finset.mem_singleton] at *; omega;

/-- The product over i%4 ∈ {2,3} equals the product over blocks of (x-4k-2)(x-4k-3). -/
lemma right_prod_eq_block_prod (x : ℝ) :
    ∏ i ∈ (Finset.Icc (1 : ℕ) 2016) \
      (Finset.Icc (1 : ℕ) 2016).filter (fun n ↦ n % 4 = 0 ∨ n % 4 = 1), (x - (i : ℝ)) =
    ∏ k ∈ Finset.range 504, ((x - (4 * (k : ℝ) + 2)) * (x - (4 * k + 3))) := by
  have h_prod_split : Finset.Icc (1 : ℕ) 2016 \ Finset.filter (fun n => n % 4 = 0 ∨ n % 4 = 1) (Finset.Icc 1 2016) = Finset.biUnion (Finset.range 504) (fun k => {4 * k + 2, 4 * k + 3}) := by
    native_decide +revert;
  rw [ h_prod_split, Finset.prod_biUnion ] <;> norm_num [ mul_comm ] ; ring;
  exact fun a ha b hb hab => Finset.disjoint_left.2 fun x hx₁ hx₂ => hab <| by norm_num at * ; omega;

-- Helper: abbreviations for the left and right block factors
abbrev Lf (x : ℝ) (k : ℕ) : ℝ := (x - (4 * (k : ℝ) + 1)) * (x - (4 * k + 4))
abbrev Rf (x : ℝ) (k : ℕ) : ℝ := (x - (4 * (k : ℝ) + 2)) * (x - (4 * k + 3))

lemma Rf_eq_Lf_add_two (x : ℝ) (k : ℕ) : Rf x k = Lf x k + 2 := by
  unfold Rf Lf; linarith [block_diff x k]

lemma Lf_lower_bound (x : ℝ) (k : ℕ) : Lf x k ≥ -9/4 := by
  unfold Lf; nlinarith [sq_nonneg (x - (4 * (k : ℝ) + 5 / 2))]

lemma Rf_lower_bound (x : ℝ) (k : ℕ) : Rf x k ≥ -1/4 := by
  linarith [Rf_eq_Lf_add_two x k, Lf_lower_bound x k]

/-- At most one k has Lf x k < 0 (intervals (4k+1, 4k+4) are disjoint) -/
lemma at_most_one_neg (x : ℝ) :
    ∀ j₁ j₂ : ℕ, Lf x j₁ < 0 → Lf x j₂ < 0 → j₁ = j₂ := by
  intro j₁ j₂ h₁ h₂
  have hL_iff : ∀ k : ℕ, Lf x k < 0 → (4 * (k : ℝ) + 1) < x ∧ x < (4 * k + 4) := by
    intro k hk; unfold Lf at hk; constructor <;> nlinarith
  obtain ⟨h₁a, h₁b⟩ := hL_iff j₁ h₁
  obtain ⟨h₂a, h₂b⟩ := hL_iff j₂ h₂
  by_contra h
  rcases Nat.lt_or_gt_of_ne h with hlt | hlt
  · have : (j₁ : ℝ) + 1 ≤ j₂ := by exact_mod_cast hlt
    linarith
  · have : (j₂ : ℝ) + 1 ≤ j₁ := by exact_mod_cast hlt
    linarith

/-- Lf x k < 0 implies bounds on x -/
lemma Lf_neg_range (x : ℝ) (k : ℕ) (h : Lf x k < 0) :
    (4 * (k : ℝ) + 1) < x ∧ x < (4 * k + 4) := by
  unfold Lf at h; constructor <;> nlinarith

/-- When x > 4k+4, Lf is positive -/
lemma Lf_pos_of_gt (x : ℝ) (k : ℕ) (h : x > 4 * (k : ℝ) + 4) : Lf x k > 0 := by
  exact mul_pos (by linarith) (by linarith)

lemma Lf_pos_of_lt (x : ℝ) (k : ℕ) (h : x < 4 * (k : ℝ) + 1) : Lf x k > 0 := by
  exact mul_pos_of_neg_of_neg (by linarith) (by linarith)

/-- The general product bound: ∏(1+aᵢ) ≤ 1/(1-∑aᵢ) for aᵢ > 0 with ∑aᵢ < 1 -/
lemma prod_le_inv_one_sub_sum {ι : Type*} (s : Finset ι) (a : ι → ℝ)
    (ha : ∀ i ∈ s, a i > 0) (hsum : ∑ i ∈ s, a i < 1) :
    ∏ i ∈ s, (1 + a i) ≤ 1 / (1 - ∑ i ∈ s, a i) := by
  rw [le_div_iff₀ (sub_pos.2 hsum)]
  have h_amgm : ∏ i ∈ s, (1 + a i) ≤ Real.exp (∑ i ∈ s, a i) := by
    rw [Real.exp_sum]
    exact Finset.prod_le_prod (fun _ _ => by linarith [ha _ ‹_›])
      fun _ _ => by linarith [ha _ ‹_›, Real.add_one_le_exp (a ‹_›)]
  nlinarith [Real.exp_pos (∑ i ∈ s, a i), Real.exp_neg (∑ i ∈ s, a i),
    mul_inv_cancel₀ (ne_of_gt (Real.exp_pos (∑ i ∈ s, a i))),
    Real.add_one_le_exp (∑ i ∈ s, a i),
    Real.add_one_le_exp (-(∑ i ∈ s, a i))]

/-- Lower bound on Lf when k < n and x ≥ 4n+1 -/
lemma Lf_lower_bound_far (x : ℝ) (k n : ℕ) (hk : k < n) (hx : x ≥ 4 * (n : ℝ) + 1) :
    Lf x k ≥ (4 * ((n : ℝ) - k)) * (4 * (n - k) - 3) := by
  unfold Lf; nlinarith [show (k : ℝ) + 1 ≤ n by norm_cast]

/-
PROBLEM
∑_{d=2}^{n} 1/d² ≤ 3/4

PROVIDED SOLUTION
We need ∑_{d=2}^{n} 1/d² ≤ 3/4 for all n. For d ≥ 2, 1/d² ≤ 1/(d(d-1)) = 1/(d-1) - 1/d (telescoping). So ∑_{d=2}^{n} 1/d² ≤ ∑_{d=2}^{n} (1/(d-1) - 1/d) = 1 - 1/n ≤ 1. But we need a tighter bound of 3/4.

Better: 1/d² ≤ 1/(d(d-1)) for d ≥ 2, so ∑_{d=2}^{n} 1/d² ≤ ∑_{d=2}^{n} 1/(d(d-1)) = 1 - 1/n ≤ 1.

But actually, we can be more precise. 1/4 + ∑_{d=3}^{n} 1/d² ≤ 1/4 + ∑_{d=3}^{n} 1/(d(d-1)) = 1/4 + (1/2 - 1/n) ≤ 1/4 + 1/2 = 3/4.

So: for n ≤ 1, the sum is empty (≤ 0 ≤ 3/4).
For n = 2, the sum is just 1/4 ≤ 3/4.
For n ≥ 3: ∑_{d=2}^{n} 1/d² = 1/4 + ∑_{d=3}^{n} 1/d². Each 1/d² ≤ 1/(d(d-1)). ∑_{d=3}^{n} 1/(d(d-1)) = ∑_{d=3}^{n} (1/(d-1) - 1/d) = 1/2 - 1/n ≤ 1/2. So total ≤ 1/4 + 1/2 = 3/4.
-/
lemma sum_inv_sq_le (n : ℕ) :
    ∑ d ∈ Finset.Icc 2 n, (1 : ℝ) / (d : ℝ) ^ 2 ≤ 3 / 4 := by
  -- For $n \geq 3$, we use the inequality $\sum_{d=2}^{n} \frac{1}{d^2} \leq \frac{1}{4} + \sum_{d=3}^{n} \frac{1}{d(d-1)}$.
  by_cases h : n ≥ 3;
  · -- For $n \geq 3$, we can use the inequality $\sum_{d=2}^{n} \frac{1}{d^2} \leq \frac{1}{4} + \sum_{d=3}^{n} \frac{1}{d(d-1)}$.
    have h_sum_bound : ∑ d ∈ Finset.Icc 2 n, (1 / (d : ℝ) ^ 2) ≤ 1 / 4 + ∑ d ∈ Finset.Icc 3 n, (1 / (d - 1 : ℝ) - 1 / (d : ℝ)) := by
      rw [ Finset.Icc_eq_cons_Ioc ( by linarith ), Finset.sum_cons ] ; norm_num;
      rw [ ← Finset.sum_sub_distrib ] ; exact Finset.sum_le_sum fun x hx => by rw [ inv_sub_inv, inv_eq_one_div, div_le_div_iff₀ ] <;> nlinarith only [ show ( x : ℝ ) ≥ 3 by norm_cast; linarith [ Finset.mem_Ioc.mp hx ] ] ;
    -- Notice that $\sum_{d=3}^{n} \frac{1}{d(d-1)}$ is a telescoping series.
    have h_telescope : ∑ d ∈ Finset.Icc 3 n, (1 / (d - 1 : ℝ) - 1 / (d : ℝ)) = 1 / 2 - 1 / (n : ℝ) := by
      erw [ Finset.sum_Ico_eq_sum_range ];
      convert Finset.sum_range_sub' _ _ using 3 <;> push_cast <;> ring;
      rw [ Nat.cast_sub ] <;> norm_num ; linarith;
    linarith [ show ( 0 : ℝ ) ≤ 1 / n by positivity ];
  · interval_cases n <;> norm_num [ Finset.Icc_eq_cons_Ioc ]

/-
PROBLEM
Sum of 2/Lf over k < n is bounded when x ≥ 4n+1

PROVIDED SOLUTION
We need ∑_{k=0}^{n-1} 2/Lf(x,k) < 1 when x ≥ 4n+1 and all Lf(x,k) > 0.

Step 1: By Lf_lower_bound_far, for each k < n with d = n - k ≥ 1:
Lf(x,k) ≥ 4d(4d-3) where d = n-k.
So 2/Lf(x,k) ≤ 2/(4d(4d-3)) = 1/(2d(4d-3)).

Step 2: For d ≥ 1, 4d-3 ≥ d (since 3d ≥ 3), so 2d(4d-3) ≥ 2d².
Thus 1/(2d(4d-3)) ≤ 1/(2d²).

Step 3: Splitting:
∑_{k=0}^{n-1} 2/Lf ≤ ∑_{d=1}^{n} 1/(2d(4d-3)) ≤ 1/(2·1·1) + ∑_{d=2}^{n} 1/(2d²)
= 1/2 + (1/2)·∑_{d=2}^{n} 1/d²

Step 4: By sum_inv_sq_le, ∑_{d=2}^{n} 1/d² ≤ 3/4.
So total ≤ 1/2 + (1/2)(3/4) = 1/2 + 3/8 = 7/8 < 1.

For the reindexing from k to d = n-k: use the fact that as k ranges over {0,...,n-1}, d = n-k ranges over {1,...,n}. The sum ∑_{k∈range n} f(n-k) = ∑_{d=1}^{n} f(d). Use Finset.sum_range_reflect or similar.

Note: for d=1, 4d-3 = 1, so 1/(2d(4d-3)) = 1/2. For d ≥ 2, use 1/(2d(4d-3)) ≤ 1/(2d²) ≤ (1/2)(1/d²).
-/
lemma sum_ratio_bound (x : ℝ) (n : ℕ) (hn : 0 < n)
    (hx : x ≥ 4 * (n : ℝ) + 1)
    (hpos : ∀ k ∈ Finset.range n, Lf x k > 0) :
    ∑ k ∈ Finset.range n, (2 / Lf x k) < 1 := by
  -- By Lf_lower_bound_far, for each k < n with d = n - k ≥ 1:
  have h_bound (k : ℕ) (hk : k < n) : 2 / (Lf x k) ≤ 1 / (2 * (n - k) ^ 2) := by
    norm_num +zetaDelta at *;
    field_simp;
    rw [ div_le_div_iff₀ ] <;> nlinarith [ show ( k:ℝ ) + 1 ≤ n by norm_cast, hpos k hk ];
  -- So we can bound the sum by $\sum_{d=1}^{n} \frac{1}{2d^2}$.
  have h_sum_bound : ∑ k ∈ Finset.range n, 2 / (Lf x k) ≤ ∑ d ∈ Finset.Icc 1 n, (1 : ℝ) / (2 * d ^ 2) := by
    convert Finset.sum_le_sum fun i hi => h_bound i ( Finset.mem_range.mp hi ) using 1;
    erw [ Finset.sum_Ico_eq_sum_range ] ; norm_num [ add_comm, mul_comm ];
    rw [ ← Finset.sum_range_reflect ];
    exact Finset.sum_congr rfl fun i hi => by rw [ Nat.cast_sub <| Nat.le_sub_one_of_lt <| Finset.mem_range.mp hi ] ; rw [ Nat.cast_sub <| by linarith [ Finset.mem_range.mp hi ] ] ; ring;
  -- By sum_inv_sq_le, we know that $\sum_{d=2}^{n} \frac{1}{d^2} \leq \frac{3}{4}$.
  have h_sum_le : ∑ d ∈ Finset.Icc 2 n, (1 : ℝ) / (d ^ 2) ≤ 3 / 4 := by
    convert sum_inv_sq_le n using 1;
  erw [ Finset.Icc_eq_cons_Ioc ( by linarith ), Finset.sum_cons ] at h_sum_bound ; norm_num at *;
  exact h_sum_bound.trans_lt ( by rw [ ← Finset.sum_mul _ _ _ ] ; linarith! )

/-
PROBLEM
Case when all Lf are nonneg: each Rf > Lf ≥ 0 so product is larger

PROVIDED SOLUTION
Since Rf x k = Lf x k + 2 for all k, and Lf x k ≥ 0 by hypothesis, we have Rf x k ≥ Lf x k + 2 > Lf x k ≥ 0 for all k. Since the finset is nonempty and each factor on the right is strictly larger than the corresponding factor on the left (and all are nonneg), use Finset.prod_lt_prod_of_nonempty or Finset.prod_lt_prod. Specifically: all Lf ≥ 0, all Rf > Lf (strict), so ∏ Rf > ∏ Lf.
-/
lemma case_all_nonneg (x : ℝ) (n : ℕ) (hn : 0 < n)
    (hL : ∀ k ∈ Finset.range n, Lf x k ≥ 0) :
    ∏ k ∈ Finset.range n, Rf x k > ∏ k ∈ Finset.range n, Lf x k := by
  -- Since Rf x k = Lf x k + 2, we have Rf x k > Lf x k for all k.
  have hRf_gt_Lf : ∀ k ∈ Finset.range n, Rf x k > Lf x k := by
    exact fun k hk => by unfold Rf Lf; nlinarith;
  induction hn <;> simp_all +decide [ Finset.prod_range_succ ];
  rename_i k hk ih;
  apply_rules [ mul_lt_mul' ];
  · exact le_of_lt ( ih ( fun i hi => hL i hi.le ) ( fun i hi => hRf_gt_Lf i hi.le ) );
  · linarith;
  · linarith;
  · exact Finset.prod_pos fun i hi => by linarith [ hL i ( Finset.mem_range_le hi ), hRf_gt_Lf i ( Finset.mem_range_le hi ) ] ;

/-
PROBLEM
Case when one Lf < 0 and corresponding Rf ≥ 0: sign argument

PROVIDED SOLUTION
The left product ∏ Lf has factor Lf x j < 0 and all other factors ≥ 0, so ∏ Lf ≤ 0. The right product: for k ≠ j, Rf x k = Lf x k + 2 ≥ 2 > 0; Rf x j ≥ 0. So ∏ Rf ≥ 0. If Rf x j > 0, ∏ Rf > 0 > ∏ Lf (when ∏ Lf < 0 or = 0). If Rf x j = 0, then ∏ Rf = 0. We need ∏ Lf < 0 in this case. ∏ Lf = Lf x j · ∏_{k≠j} Lf x k. Lf x j < 0. Need ∏_{k≠j} Lf > 0, but could be 0 if some Lf x k = 0 for k ≠ j. If Lf x k = 0 for some k ≠ j, then ∏ Lf = 0 but ∏ Rf ≥ 0, so we need to show ∏ Rf > 0. For k ≠ j with Lf x k = 0: Rf x k = 2 > 0, so all Rf factors for k ≠ j are > 0. Rf x j = 0 means Lf x j = -2. We need ∏ Rf = 0 · (positive) = 0 ≠ ∏ Lf. But ∏ Lf = Lf x j · ... = (-2) · 0 · ... = 0. So both = 0, giving ∏R = ∏L = 0, not ∏R > ∏L.

Wait, this is a subtle case. If both Rf x j = 0 and Lf x k₂ = 0 for some k₂ ≠ j, then both products = 0. But can this happen?

Rf x j = 0 means x = 4j+2 or x = 4j+3. Lf x k₂ = 0 for k₂ ≠ j means x = 4k₂+1 or x = 4k₂+4. For these to coincide: 4j+2 = 4k₂+1 (impossible mod 4) or 4j+2 = 4k₂+4 (j = k₂+1/2, impossible) or 4j+3 = 4k₂+1 (j = k₂-1/2, impossible) or 4j+3 = 4k₂+4 (impossible mod 4). So can't happen.

So if Rf x j = 0, all other Lf x k > 0 (≥ 0 and ≠ 0), giving ∏_{k≠j} Lf > 0, hence ∏ Lf = Lf x j · (positive) < 0 < ∏ Rf = 0. But wait ∏ Rf = 0 and ∏ Lf < 0, so 0 > ∏ Lf, meaning ∏ Rf > ∏ Lf. ✓

But actually ∏ Rf = 0 is not > ∏ Lf if ∏ Lf = 0. We showed ∏ Lf < 0 in this case, so ∏ Rf = 0 > ∏ Lf < 0. ✓

Use Finset.prod_eq_prod_compl_mul_prod and sign analysis.
-/
lemma case_sign_diff (x : ℝ) (n : ℕ) (j : ℕ) (hj : j < n)
    (hLj : Lf x j < 0) (hRj : Rf x j ≥ 0)
    (hother : ∀ k ∈ Finset.range n, k ≠ j → Lf x k ≥ 0) :
    ∏ k ∈ Finset.range n, Rf x k > ∏ k ∈ Finset.range n, Lf x k := by
  -- Split the product into the term for j and the product over the rest.
  have h_split : (∏ k ∈ Finset.range n, Lf x k) = Lf x j * (∏ k ∈ Finset.erase (Finset.range n) j, Lf x k) ∧ (∏ k ∈ Finset.range n, Rf x k) = Rf x j * (∏ k ∈ Finset.erase (Finset.range n) j, Rf x k) := by
    exact ⟨ by rw [ mul_comm, Finset.prod_erase_mul _ _ ( Finset.mem_range.mpr hj ) ], by rw [ mul_comm, Finset.prod_erase_mul _ _ ( Finset.mem_range.mpr hj ) ] ⟩;
  -- Since $Lf x j < 0$ and $Rf x j \ge 0$, we have $Lf x j * (∏ k ∈ Finset.erase (Finset.range n) j, Lf x k) \le 0$ and $Rf x j * (∏ k ∈ Finset.erase (Finset.range n) j, Rf x k) \ge 0$.
  have h_prod_neg : Lf x j * (∏ k ∈ Finset.erase (Finset.range n) j, Lf x k) ≤ 0 := by
    exact mul_nonpos_of_nonpos_of_nonneg hLj.le ( Finset.prod_nonneg fun k hk => hother k ( Finset.mem_of_mem_erase hk ) ( Finset.ne_of_mem_erase hk ) )
  have h_prod_pos : Rf x j * (∏ k ∈ Finset.erase (Finset.range n) j, Rf x k) ≥ 0 := by
    exact mul_nonneg hRj <| Finset.prod_nonneg fun k hk => by linarith [ hother k ( Finset.mem_of_mem_erase hk ) ( Finset.ne_of_mem_erase hk ), Rf_eq_Lf_add_two x k ] ;
  -- Since $Lf x j < 0$ and $Rf x j \ge 0$, we have $Lf x j * (∏ k ∈ Finset.erase (Finset.range n) j, Lf x k) < 0$ and $Rf x j * (∏ k ∈ Finset.erase (Finset.range n) j, Rf x k) > 0$.
  by_cases h_eq_zero : Rf x j = 0;
  · -- Since $Lf x j = -2$, we have $Lf x j * (∏ k ∈ Finset.erase (Finset.range n) j, Lf x k) < 0$.
    have h_prod_neg : Lf x j * (∏ k ∈ Finset.erase (Finset.range n) j, Lf x k) < 0 := by
      refine' mul_neg_of_neg_of_pos hLj _;
      refine' Finset.prod_pos fun k hk => lt_of_le_of_ne ( hother k ( Finset.mem_of_mem_erase hk ) ( Finset.ne_of_mem_erase hk ) ) ( Ne.symm _ );
      intro H; simp_all +decide [ sub_eq_iff_eq_add ] ;
      rcases h_eq_zero with ( rfl | rfl ) <;> rcases H with ( H | H ) <;> norm_num [ Lf ] at * <;> ring_nf at * <;> norm_cast at * <;> omega;
    linarith;
  · cases lt_or_gt_of_ne h_eq_zero <;> nlinarith [ show ∏ k ∈ Finset.erase ( Finset.range n ) j, Rf x k > 0 from Finset.prod_pos fun k hk => by nlinarith [ Rf_eq_Lf_add_two x k, hother k ( Finset.mem_of_mem_erase hk ) ( by aesop ) ] ]

/-
PROBLEM
Case when one Lf < 0 and Rf < 0: the hard case using ratio bound

PROVIDED SOLUTION
We have: Lf x (n-1) < 0 (so x ∈ (4(n-1)+1, 4(n-1)+4)), Rf x (n-1) = Lf x (n-1) + 2 < 0 (so Lf x (n-1) < -2), and all k < n-1 have Lf x k > 0 (hence Rf x k > 0).

Split the product: ∏_{k<n} = (∏_{k<n-1}) · (factor at n-1).

Let P_L = ∏_{k<n-1} Lf x k > 0, P_R = ∏_{k<n-1} Rf x k > 0.
∏_{k<n} Lf = P_L · Lf x (n-1) < 0 (since P_L > 0, Lf(n-1) < 0).
∏_{k<n} Rf = P_R · Rf x (n-1) < 0 (since P_R > 0, Rf(n-1) < 0).

We need P_R · Rf(n-1) > P_L · Lf(n-1), i.e., both negative and |P_R · Rf(n-1)| < |P_L · Lf(n-1)|.

|P_R · Rf(n-1)| = P_R · |Rf(n-1)|, |P_L · Lf(n-1)| = P_L · |Lf(n-1)|.
|Rf(n-1)| = -Rf(n-1) = -(Lf(n-1)+2) = |Lf(n-1)| - 2.

So we need: P_R · (|Lf(n-1)| - 2) < P_L · |Lf(n-1)|.
i.e., (P_R/P_L) · (|Lf(n-1)| - 2) < |Lf(n-1)|.
i.e., P_R/P_L < |Lf(n-1)| / (|Lf(n-1)| - 2).

Now |Lf(n-1)| ∈ (2, 9/4] (since Lf(n-1) ∈ [-9/4, -2) by Lf_lower_bound and the hypothesis).
So |Lf(n-1)|/(|Lf(n-1)|-2) ≥ (9/4)/(9/4-2) = (9/4)/(1/4) = 9.

P_R/P_L = ∏_{k<n-1} (Rf x k / Lf x k) = ∏_{k<n-1} (1 + 2/Lf x k).
Each 2/Lf x k > 0 since Lf x k > 0.
By sum_ratio_bound (with hx: x ≥ 4(n-1)+1 since x ∈ (4(n-1)+1, 4(n-1)+4)):
∑_{k<n-1} 2/Lf x k < 1.

∏(1 + 2/Lf x k) ≤ exp(∑ 2/Lf x k) < exp(1) < 3 < 9.

The exp bound: ∏(1+a_k) ≤ ∏ exp(a_k) = exp(∑ a_k) by 1+x ≤ exp(x) (Real.add_one_le_exp).
exp(∑) ≤ exp(1) by monotonicity since ∑ < 1.
exp(1) < 3 by linarith [Real.exp_one_lt_d9].

So P_R/P_L < 3 < 9 ≤ |Lf(n-1)|/(|Lf(n-1)|-2). ✓
-/
lemma case_both_neg (x : ℝ) (n : ℕ) (hn : 1 < n)
    (hLn : Lf x (n-1) < 0) (hRn : Rf x (n-1) < 0)
    (hpos : ∀ k ∈ Finset.range (n-1), Lf x k > 0) :
    ∏ k ∈ Finset.range n, Rf x k > ∏ k ∈ Finset.range n, Lf x k := by
  -- Let $P_L = \prod_{k < n-1} Lf x k$, $P_R = \prod_{k < n-1} Rf x k$.
  set PL := ∏ k ∈ Finset.range (n - 1), Lf x k
  set PR := ∏ k ∈ Finset.range (n - 1), Rf x k;
  have hPL_pos : PL > 0 := by
    exact Finset.prod_pos hpos
  have hPR_pos : PR > 0 := by
    exact Finset.prod_pos fun k hk => by rw [ show Rf x k = Lf x k + 2 by exact Rf_eq_Lf_add_two x k ] ; linarith [ hpos k hk ] ;;
  have h_ratio : PR / PL < 3 := by
    have h_ratio_le_exp : PR / PL ≤ Real.exp (∑ k ∈ Finset.range (n - 1), (2 / Lf x k)) := by
      have h_ratio_le_exp : ∀ k ∈ Finset.range (n - 1), Rf x k / Lf x k ≤ Real.exp (2 / Lf x k) := by
        intros k hk; rw [ show Rf x k / Lf x k = 1 + 2 / Lf x k by rw [ add_div' ] <;> ring ; linarith [ hpos k hk ] ] ; exact le_trans ( by ring_nf; norm_num ) ( Real.add_one_le_exp _ ) ;
      simpa only [ Real.exp_sum, Finset.prod_div_distrib ] using Finset.prod_le_prod ( fun _ _ => div_nonneg ( show 0 ≤ Rf x _ from by unfold Rf; nlinarith [ hpos _ ‹_›, sq_nonneg ( x - ( 4 * ↑‹ℕ› + 2 ) ), sq_nonneg ( x - ( 4 * ↑‹ℕ› + 3 ) ) ] ) ( show 0 ≤ Lf x _ from by unfold Lf; nlinarith [ hpos _ ‹_›, sq_nonneg ( x - ( 4 * ↑‹ℕ› + 1 ) ), sq_nonneg ( x - ( 4 * ↑‹ℕ› + 4 ) ) ] ) ) h_ratio_le_exp;
    have h_sum_lt_one : ∑ k ∈ Finset.range (n - 1), (2 / Lf x k) < 1 := by
      apply sum_ratio_bound x (n - 1) (Nat.sub_pos_of_lt hn) ?_ hpos;
      unfold Lf at *; rcases n with ( _ | _ | n ) <;> norm_num at * ; nlinarith;
    exact h_ratio_le_exp.trans_lt ( lt_of_lt_of_le ( Real.exp_lt_exp.mpr h_sum_lt_one ) ( by have := Real.exp_one_lt_d9; norm_num1 at *; linarith ) );
  -- We need $P_R \cdot Rf(n-1) > P_L \cdot Lf(n-1)$, i.e., $P_R \cdot (Lf(n-1) + 2) > P_L \cdot Lf(n-1)$.
  have h_final : PR * (Lf x (n - 1) + 2) > PL * Lf x (n - 1) := by
    rw [ div_lt_iff₀ hPL_pos ] at h_ratio;
    nlinarith [ Lf_lower_bound x ( n - 1 ) ];
  rcases n <;> simp_all +decide [ Finset.prod_range_succ ];
  convert h_final using 1 ; ring!

/-
PROBLEM
General version: ratio of products is < 1 when one block is negative

PROVIDED SOLUTION
The product ∏_{k<n} Lf has exactly one negative factor (at j), so ∏ Lf < 0.
Similarly ∏_{k<n} Rf has one negative factor (Rf j < 0), so ∏ Rf < 0.
Both products are negative. We need ∏ Rf > ∏ Lf, i.e., |∏ Rf| < |∏ Lf|.

Split: ∏ Rf = Rf j · ∏_{k≠j} Rf, ∏ Lf = Lf j · ∏_{k≠j} Lf.
|∏ Rf| / |∏ Lf| = |Rf j| / |Lf j| · ∏_{k≠j} (Rf k / Lf k).

Step 1: |Rf j| / |Lf j| = |Lf j + 2| / |Lf j| = (|Lf j| - 2) / |Lf j| = 1 - 2/|Lf j|.
Since |Lf j| ≤ 9/4 (by Lf_lower_bound: Lf ≥ -9/4): |Rf j|/|Lf j| ≤ 1 - 2/(9/4) = 1 - 8/9 = 1/9.

Step 2: For k ≠ j: Rf k / Lf k = 1 + 2/Lf k > 1 (since Lf k > 0 by hother).
∏_{k≠j} (Rf k / Lf k) = ∏_{k≠j} (1 + 2/Lf k) ≤ exp(∑_{k≠j} 2/Lf k).

Step 3: Bound ∑_{k≠j} 2/Lf k.
Since Lf j < 0, x ∈ (4j+1, 4j+4) (by Lf_neg_range). For k ≠ j with k < n:
- If k < j: x > 4j+1 > 4k+4 (since k+1 ≤ j), so Lf k = (x-4k-1)(x-4k-4) ≥ 4(j-k)(4(j-k)-3).
- If k > j: x < 4j+4 < 4k+1 (since k ≥ j+1), so Lf k = (4k+1-x)(4k+4-x) ≥ 4(k-j)(4(k-j)-3).
So 2/Lf k ≤ 2/(4d(4d-3)) = 1/(2d(4d-3)) where d = |k-j| ≥ 1.

For d = 1: 1/(2·1·1) = 1/2, and there are at most 2 terms with d=1.
For d ≥ 2: 1/(2d(4d-3)) ≤ 1/(2d²), at most 2 terms.

∑_{k≠j} 2/Lf k ≤ 2·(1/2) + 2·∑_{d=2}^{max} 1/(2d²) = 1 + ∑_{d=2}^{max} 1/d².
By sum_inv_sq_le: ∑_{d=2}^{max} 1/d² ≤ 3/4.
So ∑ ≤ 1 + 3/4 = 7/4.

Step 4: exp(7/4) < exp(2) = exp(1)^2 < 3^2 = 9 (since exp(1) < 3 by Real.exp_one_lt_d9).

Step 5: |∏ Rf| / |∏ Lf| ≤ (1/9) · exp(7/4) < (1/9) · 9 = 1.
So |∏ Rf| < |∏ Lf|, and since both are negative, ∏ Rf > ∏ Lf.
-/
set_option maxHeartbeats 800000 in
lemma ratio_lt_one (x : ℝ) (n : ℕ) (j : ℕ) (hj : j < n) (hn : 1 < n)
    (hLj : Lf x j < -2) (hRj : Rf x j < 0)
    (hother : ∀ k ∈ Finset.range n, k ≠ j → Lf x k > 0) :
    ∏ k ∈ Finset.range n, Rf x k > ∏ k ∈ Finset.range n, Lf x k := by
  by_contra h_contra; contrapose! h_contra with h_contra; simp_all +decide [ Finset.prod_eq_mul_prod_diff_singleton ( Finset.mem_range.mpr hj ) ] ;
  -- By Lemma~\ref{lem:case_both_neg}, we have $\sum_{k \neq j} \frac{2}{Lf(x,k)} < \frac{7}{4}$.
  have hsum_bound : ∑ k ∈ Finset.range n \ {j}, (2 / Lf x k) < 7 / 4 := by
    -- For k ≠ j with k < n, we have Lf x k ≥ 4d(4d-3) where d = |k-j| ≥ 1.
    have hLf_bound : ∀ k ∈ Finset.range n \ {j}, Lf x k ≥ 4 * |(k : ℝ) - j| * (4 * |(k : ℝ) - j| - 3) := by
      intros k hk
      have hLf_bound : Lf x k ≥ 4 * |(k : ℝ) - j| * (4 * |(k : ℝ) - j| - 3) := by
        have h_case1 : k < j → Lf x k ≥ 4 * (j - k) * (4 * (j - k) - 3) := by
          intro hk_lt_j
          have h_case1 : x > 4 * j + 1 := by
            unfold Lf at *; nlinarith [ sq_nonneg ( x - ( 4 * j + 1 ) ), sq_nonneg ( x - ( 4 * j + 4 ) ) ] ;
          have h_case1_bound : Lf x k ≥ 4 * (j - k) * (4 * (j - k) - 3) := by
            exact Lf_lower_bound_far x k j hk_lt_j ( by linarith ) |> le_trans ( by nlinarith [ show ( k : ℝ ) + 1 ≤ j by norm_cast ] ) ;
          exact h_case1_bound
        have h_case2 : k > j → Lf x k ≥ 4 * (k - j) * (4 * (k - j) - 3) := by
          intros hk_gt_j
          have hLf_bound : Lf x k ≥ (4 * (k - j)) * (4 * (k - j) - 3) := by
            have hx_bound : x < 4 * j + 4 := by
              unfold Lf at *; nlinarith;
            unfold Lf; nlinarith [ show ( k : ℝ ) ≥ j + 1 by norm_cast ] ;
          exact hLf_bound
        grind
      exact hLf_bound;
    -- For d ≥ 2, 1/(2d(4d-3)) ≤ 1/(2d²), and there are at most 2 terms with d=1.
    have hsum_bound : ∑ k ∈ Finset.range n \ {j}, (2 / Lf x k) ≤ ∑ d ∈ Finset.Icc 1 (n - 1), (2 / (4 * d * (4 * d - 3) : ℝ)) * (if d = 1 then 2 else 2) := by
      have hsum_bound : ∑ k ∈ Finset.range n \ {j}, (2 / Lf x k) ≤ ∑ d ∈ Finset.Icc 1 (n - 1), ∑ k ∈ Finset.range n \ {j}, (if |(k : ℝ) - j| = d then 2 / (4 * d * (4 * d - 3) : ℝ) else 0) := by
        have hsum_bound : ∀ k ∈ Finset.range n \ {j}, 2 / Lf x k ≤ ∑ d ∈ Finset.Icc 1 (n - 1), (if |(k : ℝ) - j| = d then 2 / (4 * d * (4 * d - 3) : ℝ) else 0) := by
          intros k hk
          have h_abs : |(k : ℝ) - j| ∈ Finset.image (fun d : ℕ => d : ℕ → ℝ) (Finset.Icc 1 (n - 1)) := by
            simp +zetaDelta at *;
            exact ⟨ Int.natAbs ( k - j ), ⟨ Int.natAbs_pos.mpr ( sub_ne_zero.mpr <| mod_cast hk.2 ), Nat.le_sub_one_of_lt <| by cases abs_cases ( k - j : ℤ ) <;> linarith ⟩, by simp +decide [ abs_of_nonneg ] ⟩ ;
          generalize_proofs at *; (
          simp +zetaDelta at *; (
          obtain ⟨ a, ⟨ ha₁, ha₂ ⟩, ha₃ ⟩ := h_abs; rw [ Finset.sum_eq_single a ] <;> simp_all +decide [ div_le_div_iff₀ ] ;
          · exact div_le_div_of_nonneg_left ( by norm_num ) ( mul_pos ( mul_pos ( by norm_num ) ( abs_pos.mpr ( sub_ne_zero.mpr ( by aesop ) ) ) ) ( sub_pos.mpr ( by linarith [ show ( |↑k - ↑j| : ℝ ) ≥ 1 by exact_mod_cast ha₃.symm ▸ Nat.one_le_cast.mpr ha₁ ] ) ) ) ( hLf_bound k hk.1 hk.2 ) |> le_trans <| by norm_num [ ha₃ ] ;
          · intros; norm_cast at *; aesop;));
        exact le_trans ( Finset.sum_le_sum hsum_bound ) ( by rw [ Finset.sum_comm ] );
      refine le_trans hsum_bound ?_;
      refine Finset.sum_le_sum fun d hd => ?_;
      norm_num [ Finset.sum_ite ];
      rw [ mul_comm ] ; gcongr;
      · exact div_nonneg zero_le_two ( mul_nonneg ( mul_nonneg zero_le_four ( Nat.cast_nonneg _ ) ) ( sub_nonneg_of_le ( by norm_cast; linarith [ Finset.mem_Icc.mp hd ] ) ) );
      · norm_cast;
        refine' le_trans ( Finset.card_le_card _ ) _;
        exact { j + d, j - d };
        · grind;
        · exact Finset.card_insert_le _ _;
    -- Simplify the sum $\sum_{d=1}^{n-1} \frac{2}{4d(4d-3)} \cdot 2$.
    have hsum_simplified : ∑ d ∈ Finset.Icc 1 (n - 1), (2 / (4 * d * (4 * d - 3) : ℝ)) * 2 ≤ 1 + ∑ d ∈ Finset.Icc 2 (n - 1), (1 / (2 * d ^ 2 : ℝ)) := by
      erw [ Finset.Icc_eq_cons_Ioc, Finset.sum_cons ] <;> norm_num ; ring_nf ; (
      exact Finset.sum_le_sum fun x hx => by rw [ inv_pow ] ; rw [ inv_mul_eq_div, inv_mul_eq_div, div_le_div_iff₀ ] <;> nlinarith only [ show ( x : ℝ ) ≥ 2 by norm_cast; linarith [ Finset.mem_Ioc.mp hx ] ] ;);
      exact Nat.le_sub_one_of_lt hn;
    -- By sum_inv_sq_le, we have $\sum_{d=2}^{n-1} \frac{1}{d^2} \leq \frac{3}{4}$.
    have hsum_inv_sq_le : ∑ d ∈ Finset.Icc 2 (n - 1), (1 / (d ^ 2 : ℝ)) ≤ 3 / 4 := by
      convert sum_inv_sq_le ( n - 1 ) using 1;
    norm_num [ ← Finset.sum_mul _ _ _ ] at * ; linarith;
  -- By Lemma~\ref{lem:case_both_neg}, we have $\prod_{k \neq j} \frac{Rf(x,k)}{Lf(x,k)} \leq \exp(\sum_{k \neq j} \frac{2}{Lf(x,k)})$.
  have hprod_bound : ∏ k ∈ Finset.range n \ {j}, (Rf x k / Lf x k) ≤ Real.exp (∑ k ∈ Finset.range n \ {j}, (2 / Lf x k)) := by
    have hprod_bound : ∀ k ∈ Finset.range n \ {j}, (Rf x k / Lf x k) ≤ Real.exp (2 / Lf x k) := by
      intro k hk; rw [ div_le_iff₀ ( hother k ( Finset.mem_range.mp ( Finset.mem_sdiff.mp hk |>.1 ) ) ( by aesop ) ) ] ; ring_nf;
      nlinarith [ Real.add_one_le_exp ( ( 4 + ( - ( x * 5 ) - x * k * 8 ) + x ^ 2 + k * 20 + k ^ 2 * 16 : ℝ ) ⁻¹ * 2 ), hother k ( Finset.mem_range.mp ( Finset.mem_sdiff.mp hk |>.1 ) ) ( by aesop ), inv_mul_cancel₀ ( show ( 4 + ( - ( x * 5 ) - x * k * 8 ) + x ^ 2 + k * 20 + k ^ 2 * 16 : ℝ ) ≠ 0 from fun h => by have := hother k ( Finset.mem_range.mp ( Finset.mem_sdiff.mp hk |>.1 ) ) ( by aesop ) ; norm_num [ show Lf x k = 0 by { unfold Lf; nlinarith } ] at this ) ];
    simpa only [ Real.exp_sum ] using Finset.prod_le_prod ( fun _ _ => div_nonneg ( by unfold Rf; nlinarith [ hother _ ( Finset.mem_range.mp ( Finset.mem_sdiff.mp ‹_› |>.1 ) ) ( by aesop ) ] ) ( by unfold Lf; nlinarith [ hother _ ( Finset.mem_range.mp ( Finset.mem_sdiff.mp ‹_› |>.1 ) ) ( by aesop ) ] ) ) hprod_bound;
  -- By Lemma~\ref{lem:case_both_neg}, we have $\frac{|Rf(x,j)|}{|Lf(x,j)|} \cdot \exp(\sum_{k \neq j} \frac{2}{Lf(x,k)}) < 1$.
  have hratio_bound : (abs (Rf x j) / abs (Lf x j)) * Real.exp (∑ k ∈ Finset.range n \ {j}, (2 / Lf x k)) < 1 := by
    -- By Lemma~\ref{lem:case_both_neg}, we have $\frac{|Rf(x,j)|}{|Lf(x,j)|} \leq \frac{1}{9}$.
    have hratio_le_one_ninth : abs (Rf x j) / abs (Lf x j) ≤ 1 / 9 := by
      rw [ div_le_iff₀ ] <;> cases abs_cases ( Rf x j ) <;> cases abs_cases ( Lf x j ) <;> linarith [ Rf_eq_Lf_add_two x j, Lf_lower_bound x j ] ;
    -- By Lemma~\ref{lem:case_both_neg}, we have $\exp(\sum_{k \neq j} \frac{2}{Lf(x,k)}) < \exp(\frac{7}{4})$.
    have hexp_bound : Real.exp (∑ k ∈ Finset.range n \ {j}, (2 / Lf x k)) < Real.exp (7 / 4) := by
      exact Real.exp_lt_exp.mpr hsum_bound;
    -- By Lemma~\ref{lem:case_both_neg}, we have $\exp(\frac{7}{4}) < 9$.
    have hexp_lt_nine : Real.exp (7 / 4) < 9 := by
      rw [ ← Real.log_lt_log_iff ( by positivity ) ] <;> norm_num [ Real.log_exp ];
      rw [ div_lt_iff₀' ] <;> norm_num [ ← Real.log_rpow, Real.lt_log_iff_exp_lt ];
      have := Real.exp_one_lt_d9.le ; norm_num at * ; rw [ show Real.exp 7 = ( Real.exp 1 ) ^ 7 by rw [ ← Real.exp_nat_mul ] ; norm_num ] ; exact lt_of_le_of_lt ( pow_le_pow_left₀ ( by positivity ) this _ ) ( by norm_num ) ;
    nlinarith [ Real.exp_pos ( ∑ k ∈ Finset.range n \ { j }, 2 / Lf x k ) ];
  -- By combining the results from hprod_bound and hratio_bound, we get the desired inequality.
  have h_final : (∏ k ∈ Finset.range n \ {j}, Rf x k / Lf x k) * (abs (Rf x j) / abs (Lf x j)) < 1 := by
    nlinarith [ show 0 ≤ |Rf x j| / |Lf x j| by positivity ];
  simp_all +decide [ Finset.prod_div_distrib, abs_of_neg ];
  rw [ div_mul_div_comm, div_lt_iff₀ ] at h_final <;> norm_num [ Lf, Rf ] at *;
  · rw [ ← abs_mul ] at * ; rw [ abs_of_neg ] at * <;> nlinarith;
  · exact mul_pos ( Finset.prod_pos fun k hk => hother k ( Finset.mem_range.mp ( Finset.mem_sdiff.mp hk |>.1 ) ) ( by aesop ) ) ( mul_pos ( abs_pos.mpr ( by nlinarith ) ) ( abs_pos.mpr ( by nlinarith ) ) )

/-
PROBLEM
The key inequality by induction

PROVIDED SOLUTION
Case analysis based on whether there exists j ∈ range n with Lf x j < 0.

Case 1: No such j exists (all Lf x k ≥ 0 for k ∈ range n).
Apply case_all_nonneg x n hn. For the hypothesis: if all k ∈ range n have ¬(Lf x k < 0), then by push_neg, all have Lf x k ≥ 0.

Case 2: There exists j ∈ range n with Lf x j < 0. By at_most_one_neg, j is unique.
Subcase 2a: Rf x j ≥ 0 (i.e., Lf x j ≥ -2).
Apply case_sign_diff x n j hj hLj hRj. For hother: for k ≠ j, if Lf x k < 0, then by at_most_one_neg k = j, contradiction. So Lf x k ≥ 0.

Subcase 2b: Rf x j < 0 (i.e., Lf x j < -2).
For hother: for k ≠ j, Lf x k cannot be < 0 (by at_most_one_neg), so Lf x k ≥ 0. But we need Lf x k > 0 (strict). If Lf x k = 0, then x = 4k+1 or x = 4k+4. But x ∈ (4j+1, 4j+4) (by Lf_neg_range). If x = 4k+1 with k ≠ j: then 4j+1 < 4k+1 < 4j+4, so j < k < j+3/4, giving k = j (impossible since k ≠ j). Similarly for x = 4k+4: 4j+1 < 4k+4 < 4j+4 gives j-3/4 < k < j, so k = j-1... but then 4(j-1)+4 = 4j and 4j < 4j+1, contradiction since we need 4k+4 > 4j+1. So Lf x k = 0 doesn't happen for k ≠ j.

Need n > 1 for ratio_lt_one. If n = 1, then j = 0 and range 1 = {0}, Rf x 0 = Lf x 0 + 2 > Lf x 0. But we also assumed Lf x 0 < -2, meaning Rf x 0 < 0 and Lf x 0 < -2. Rf x 0 - Lf x 0 = 2 > 0, so Rf x 0 > Lf x 0. ✓

Apply ratio_lt_one x n j hj hn hLj hRj hother (for n > 1). For n = 1, handle directly.
-/
lemma right_gt_left_gen (n : ℕ) (hn : 0 < n) (x : ℝ) :
    ∏ k ∈ Finset.range n, Rf x k >
    ∏ k ∈ Finset.range n, Lf x k := by
  by_cases h_exists_neg : ∃ j ∈ Finset.range n, Lf x j < 0;
  · obtain ⟨ j, hj₁, hj₂ ⟩ := h_exists_neg; have hj₃ := Lf_neg_range x j hj₂; rcases n with ( _ | _ | n ) <;> simp_all +decide ;
    · unfold Lf Rf; linarith;
    · by_cases hRj : Rf x j ≥ 0 <;> simp_all +decide [ Lf, Rf ];
      · -- Apply the case_sign_diff lemma with the given parameters.
        apply case_sign_diff x (n + 2) j (by linarith) hj₂ hRj (fun k hk₁ hk₂ => by
          by_cases hk₃ : k < j <;> simp_all +decide [ Lf ];
          · nlinarith [ show ( k : ℝ ) + 1 ≤ j by norm_cast ];
          · nlinarith [ show ( k : ℝ ) ≥ j + 1 by exact_mod_cast lt_of_le_of_ne hk₃ ( Ne.symm hk₂ ) ]);
      · -- Apply the ratio_lt_one lemma with the given conditions.
        apply ratio_lt_one x (n + 2) j (by
        linarith) (by
        linarith) (by
        unfold Lf; nlinarith;) (by
        exact hRj.trans_le ( by norm_num [ Rf ] )) (by
        intros k hk hk_ne_j; exact (by
        by_cases hk_lt_j : k < j <;> by_cases hk_gt_j : k > j <;> simp_all +decide [ Lf ] <;> try nlinarith;
        · nlinarith [ show ( k : ℝ ) + 1 ≤ j by norm_cast ];
        · nlinarith [ show ( k : ℝ ) ≥ j + 1 by norm_cast ];
        · exact False.elim <| hk_ne_j <| le_antisymm hk_gt_j hk_lt_j););
  · exact case_all_nonneg x n hn fun k hk => le_of_not_gt fun hk' => h_exists_neg ⟨ k, hk, hk' ⟩

/-- The key inequality: the right product is strictly greater than the left product. -/
lemma right_gt_left (x : ℝ) :
    ∏ k ∈ Finset.range 504, Rf x k >
    ∏ k ∈ Finset.range 504, Lf x k :=
  right_gt_left_gen 504 (by norm_num) x

def solution_value : ℕ := 2016

theorem imo2016_p5 :
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
    · simp_rw [hp]; rw [Finset.filter_not, lemma1]; simp [solution_value]
    · push_neg
      intro x
      rw [left_prod_eq_block_prod, right_prod_eq_block_prod]
      show ∏ k ∈ Finset.range 504, ((x - (4 * (k : ℝ) + 1)) * (x - (4 * k + 4))) ≠
           ∏ k ∈ Finset.range 504, ((x - (4 * (k : ℝ) + 2)) * (x - (4 * k + 3)))
      exact ne_of_lt (right_gt_left x)
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
    push_neg at hLR
    specialize hLR i
    have hic1 : i ∈ Finset.Icc 1 2016 \ L := by
      rw [Finset.mem_sdiff]; exact ⟨hic, hiL⟩
    have hic2 : i ∈ Finset.Icc 1 2016 \ R := by
      rw [Finset.mem_sdiff]; exact ⟨hic, hiR⟩
    rw [←Finset.prod_erase_mul _ _ hic1, ←Finset.prod_erase_mul _ _ hic2] at hLR
    simp at hLR


