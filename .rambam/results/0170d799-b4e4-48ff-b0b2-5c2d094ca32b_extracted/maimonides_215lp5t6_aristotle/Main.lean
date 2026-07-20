/-
Copyright (c) 2023 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

import Mathlib

/-!
# International Mathematical Olympiad 2023, Problem 5

Let n be a positive integer. A _Japanese triangle_ is defined as
a set of 1 + 2 + ... + n dots arranged as an equilateral
triangle. Each dot is colored white or red, such that each row
has exactly one red dot.

A _ninja path_ is a sequence of n dots obtained by starting in the
top row (which has length 1), and then at each step going to one of
the dot immediately below the current dot, until the bottom
row is reached.

In terms of n, determine the greatest k such that in each Japanese triangle
there is a ninja path containing at least k red dots.
-/

namespace Imo2023P5

structure JapaneseTriangle (n : ℕ) where
  red : (i : Finset.Icc 1 n) → Fin i.val

def next_row {n} (i : Finset.Icc 1 n) (h : i.val + 1 ≤ n) : Finset.Icc 1 n :=
  ⟨i.val + 1, by aesop⟩

structure NinjaPath (n : ℕ) where
  steps : (i : Finset.Icc 1 n) → Fin i.val
  steps_valid : ∀ i : Finset.Icc 1 n, (h : i.val + 1 ≤ n) →
     ((steps i).val = steps (next_row i h) ∨
      (steps i).val + 1 = steps (next_row i h))

noncomputable def solution_value (n : ℕ) : ℕ := if n = 0 then 0 else Nat.log 2 n + 1

/-! ## Key structural lemmas -/

/-- Ninja path positions are non-decreasing -/
lemma path_nondecreasing {n : ℕ} (p : NinjaPath n)
    (i j : Finset.Icc 1 n) (hij : i.val ≤ j.val) :
    (p.steps i).val ≤ (p.steps j).val := by
  have h_non_decreasing : ∀ k : Finset.Icc 1 n, ∀ h : k.val + 1 ≤ n,
      (p.steps k).val ≤ (p.steps (next_row k h)).val := by
    exact fun k h => by have := p.steps_valid k h; omega
  induction' j with j hj
  induction' j with j ih generalizing i
  · norm_num at hj
  · cases hij.eq_or_lt <;>
      [ aesop
      ; exact le_trans
          (ih i (Finset.mem_Icc.mpr ⟨by linarith [Finset.mem_Icc.mp i.2],
            by linarith [Finset.mem_Icc.mp i.2, Finset.mem_Icc.mp hj]⟩)
            (Nat.le_of_lt_succ ‹_›))
          (h_non_decreasing ⟨j, Finset.mem_Icc.mpr ⟨by linarith [Finset.mem_Icc.mp i.2],
            by linarith [Finset.mem_Icc.mp i.2, Finset.mem_Icc.mp hj]⟩⟩
            (by linarith [Finset.mem_Icc.mp hj])) ]

/-! ## Lower bound

For any Japanese triangle, there exists a ninja path hitting at least
solution_value n red dots.

The "tent path" T_k goes right k times then stays flat:
  p_i = min(i-1, k) for i = 1, ..., n.

Each row i is hit by the tent path T_{red_i} (since min(i-1, red_i) = red_i < i).

The score of tent path T_k equals the number of rows i with min(i-1,k) = red_i,
which can be decomposed as:
  |{i ≤ k+1 : red_i = i-1}| + |{i > k+1 : red_i = k}|

We show max_k Score(T_k) ≥ ⌊log₂(n)⌋ + 1 by a counting argument. -/

/-- A tent path going right k times then staying flat is a valid ninja path -/
noncomputable def tentPath (n : ℕ) (k : ℕ) : NinjaPath n where
  steps := fun i => ⟨min (i.val - 1) k, by
    have hi := (Finset.mem_Icc.mp i.prop).1
    exact lt_of_le_of_lt (min_le_left _ _) (by omega)⟩
  steps_valid := by
    intro i h
    simp [next_row]
    omega

/-- The lower bound: for any Japanese triangle, there exists a ninja path
    hitting at least solution_value n red dots. -/
theorem lower_bound (n : ℕ) :
    ∀ j : JapaneseTriangle n,
      ∃ p : NinjaPath n,
        solution_value n ≤ Fintype.card {i // j.red i = p.steps i} := by
  sorry

/-! ## Upper bound via adversarial construction

The adversarial triangle places red dot at position `2^(⌊log₂(i)⌋+1) - 1 - i` in row i.
Within each "block" `[2^k, 2^(k+1)-1]`, the red positions are strictly decreasing.
Since any ninja path is non-decreasing, it can hit at most 1 red per block.
There are `⌊log₂(n)⌋ + 1` blocks, giving an upper bound of `⌊log₂(n)⌋ + 1`. -/

/-- The adversarial red position for row i: within each block [2^k, 2^(k+1)-1],
    the reds count down from 2^k - 1 to 0. -/
def advRed (i : ℕ) (hi : 1 ≤ i) : Fin i :=
  ⟨2^(Nat.log 2 i + 1) - 1 - i, by
    have h1 : i < 2^(Nat.log 2 i + 1) := Nat.lt_pow_succ_log_self (by omega) i
    have h2 : 2^(Nat.log 2 i + 1) ≤ 2 * i := by
      have := Nat.pow_log_le_self 2 (show i ≠ 0 by omega)
      simp [Nat.pow_succ] at *; omega
    omega⟩

/-- Within a block, the red positions are decreasing -/
lemma advRed_decreasing (i j : ℕ) (hi : 1 ≤ i) (hj : 1 ≤ j)
    (hij : i < j) (hlog : Nat.log 2 i = Nat.log 2 j) :
    (advRed j hj).val < (advRed i hi).val := by
  simp [advRed]
  rw [hlog]
  rw [tsub_lt_tsub_iff_left_of_le]
  · linarith
  · exact Nat.le_sub_one_of_lt (Nat.lt_pow_succ_log_self (by decide) _)

/-- The upper bound: no value greater than solution_value n is in the set. -/
theorem upper_bound (n : ℕ) :
    ∀ k, (∀ j : JapaneseTriangle n,
      ∃ p : NinjaPath n,
        k ≤ Fintype.card {i // j.red i = p.steps i}) →
    k ≤ solution_value n := by
  intro k hk
  contrapose! hk
  use ⟨fun i => advRed i.val (Finset.mem_Icc.mp i.prop).1⟩
  intro p
  have h_card : Fintype.card { i : Finset.Icc 1 n //
      (advRed i.val (Finset.mem_Icc.mp i.prop).1).val = (p.steps i).val } ≤
      Nat.log 2 n + 1 := by
    have h_blocks : ∀ i j : Finset.Icc 1 n, i.val < j.val →
        Nat.log 2 i.val = Nat.log 2 j.val →
        (advRed i.val (Finset.mem_Icc.mp i.prop).1).val ≠ (p.steps i).val ∨
        (advRed j.val (Finset.mem_Icc.mp j.prop).1).val ≠ (p.steps j).val := by
      intro i j hij hlog
      by_contra h_contra
      push_neg at h_contra
      have h_eq := h_contra
      have h_decreasing : (advRed j.val (Finset.mem_Icc.mp j.prop).1).val <
          (advRed i.val (Finset.mem_Icc.mp i.prop).1).val :=
        advRed_decreasing (↑i) (↑j) (Finset.mem_Icc.mp (Subtype.prop i)).left
          (Finset.mem_Icc.mp (Subtype.prop j)).left hij hlog
      have h_nondecreasing : (p.steps i).val ≤ (p.steps j).val :=
        path_nondecreasing p i j hij.le
      linarith [h_eq, h_decreasing, h_nondecreasing]
    have h_card : Finset.card (Finset.filter
        (fun i : Finset.Icc 1 n =>
          (advRed i.val (Finset.mem_Icc.mp i.prop).1).val = (p.steps i).val)
        Finset.univ) ≤
        Finset.card (Finset.image (fun i : Finset.Icc 1 n => Nat.log 2 i.val)
        (Finset.filter (fun i : Finset.Icc 1 n =>
          (advRed i.val (Finset.mem_Icc.mp i.prop).1).val = (p.steps i).val)
        Finset.univ)) := by
      rw [Finset.card_image_of_injOn]
      intros i hi j hj hij
      grind
    rw [Fintype.card_subtype]
    exact h_card.trans (le_trans (Finset.card_le_card <|
      Finset.image_subset_iff.mpr fun i hi =>
        Finset.mem_Icc.mpr ⟨Nat.zero_le _,
          Nat.log_mono_right <| Finset.mem_Icc.mp i.2 |>.2⟩) <|
      by simp +arith +decide)
  unfold solution_value at hk
  split_ifs at hk <;> simp_all +decide [Fin.ext_iff]
  · aesop
  · linarith

theorem imo2023_p5 (n : ℕ) :
    IsGreatest {k | ∀ j : JapaneseTriangle n,
                    ∃ p : NinjaPath n,
                      k ≤ Fintype.card {i // j.red i = p.steps i}}
               (solution_value n) := by
  exact ⟨lower_bound n, upper_bound n⟩

end Imo2023P5
