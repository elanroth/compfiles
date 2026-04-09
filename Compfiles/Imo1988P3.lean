/-
Copyright (c) 2024 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InternLM-MATH LEAN Formalizer v0.1, Goedel-Prover-V2
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Olympiad 1988, Problem 3

A function $f$ defined on the positive integers (and taking positive integers values) is given by:
f(1) = 1
f(3) = 3
f(2 \cdot n) = f(n)
f(4 \cdot n + 1) = 2 \cdot f(2 \cdot n + 1) - f(n)
f(4 \cdot n + 3) = 3 \cdot f(2 \cdot n + 1) - 2 \cdot f(n)
for all positive integers $n.$
Determine with proof the number of positive integers $\leq 1988$ for which $f(n) = n.$
-/

namespace Imo1988P3

determine solution : ℕ := 92

/-- The unique function satisfying the IMO 1988 P3 recurrences. -/
def g (n : Nat) : Nat :=
  if n = 0 then 0
  else if n = 1 then 1
  else if n = 3 then 3
  else if n % 2 = 0 then g (n / 2)
  else if n % 4 = 1 then 2 * g ((n + 1) / 2) - g ((n - 1) / 4)
  else 3 * g ((n - 1) / 2) - 2 * g ((n - 3) / 4)
termination_by n
decreasing_by all_goals omega

lemma g_zero : g 0 = 0 := by
  rw [g]
  simp

lemma g_one : g 1 = 1 := by
  rw [g]
  simp

lemma g_three : g 3 = 3 := by
  rw [g]
  simp

lemma g_even (n : Nat) (hn : n ≥ 2) (he : n % 2 = 0) : g n = g (n / 2) := by
  rw [g]
  simp [show n ≠ 0 by omega, show n ≠ 1 by omega, show n ≠ 3 by omega, he]

lemma g_mod4_1 (n : Nat) (hn : n ≥ 5) (hm : n % 4 = 1) :
    g n = 2 * g ((n + 1) / 2) - g ((n - 1) / 4) := by
  rw [g]
  simp [show n ≠ 0 by omega, show n ≠ 1 by omega, show n ≠ 3 by omega,
    show n % 2 ≠ 0 by omega, hm]

lemma g_mod4_3 (n : Nat) (hn : n ≥ 7) (hm : n % 4 = 3) :
    g n = 3 * g ((n - 1) / 2) - 2 * g ((n - 3) / 4) := by
  rw [g]
  simp [show n ≠ 0 by omega, show n ≠ 1 by omega, show n ≠ 3 by omega,
    show n % 2 ≠ 0 by omega, show ¬(n % 4 = 1) by omega]

lemma g_two : g 2 = 1 := by
  simpa [g_one] using g_even 2 (by omega) (by norm_num)

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 1000 in
lemma f_eq_g
    (f : ℕ+ → ℕ+)
    (h₀ : f 1 = 1)
    (h₁ : f 3 = 3)
    (h₂ : ∀ n, f (2 * n) = f n)
    (h₃ : ∀ n, f (4 * n + 1) + f n = 2 * f (2 * n + 1))
    (h₄ : ∀ n, f (4 * n + 3) + 2 * f n = 3 * f (2 * n + 1))
    (n : ℕ+) : (f n : ℕ) = g n := by
  induction' n using PNat.strongInductionOn with n ih
  by_cases hn : n.val ≤ 3
  · have hcases : n = 1 ∨ n = 2 ∨ n = 3 := by
      have hvals : (n : ℕ) = 1 ∨ (n : ℕ) = 2 ∨ (n : ℕ) = 3 := by
        have hpos : 0 < (n : ℕ) := n.pos
        omega
      rcases hvals with h1 | h23
      · exact Or.inl (PNat.eq h1)
      · rcases h23 with h2 | h3
        · exact Or.inr <| Or.inl (PNat.eq h2)
        · exact Or.inr <| Or.inr (PNat.eq h3)
    rcases hcases with rfl | rfl | rfl
    · simpa [g_one] using congrArg PNat.val h₀
    · have h_two : f 2 = 1 := by
        exact (h₂ 1).trans h₀
      simpa [g_two] using congrArg PNat.val h_two
    · simpa [g_three] using congrArg PNat.val h₁
  · by_cases h_even : n.val % 2 = 0
    · obtain ⟨m, hm⟩ : ∃ m : ℕ+, n = 2 * m := by
        exact PNat.dvd_iff.mpr (Nat.dvd_of_mod_eq_zero h_even)
      subst hm
      have hm_lt : (m : ℕ) < 2 * m := by
        linarith [PNat.pos m]
      have hm_ind : (f m : ℕ) = g m := by
        exact ih m hm_lt
      have hrec : (f (2 * m) : ℕ) = (f m : ℕ) := by
        exact congrArg PNat.val (h₂ m)
      calc
        (f (2 * m) : ℕ) = (f m : ℕ) := hrec
        _ = g m := hm_ind
        _ = g (2 * m) := by
          symm
          simpa using g_even (2 * (m : ℕ)) (by omega) (by simp)
    · obtain ⟨k, rfl | rfl⟩ : ∃ k : ℕ+, n = 4 * k + 1 ∨ n = 4 * k + 3 := by
        obtain ⟨k, hk⟩ : ∃ k : ℕ, n.val = 4 * k + 1 ∨ n.val = 4 * k + 3 := by
          exact ⟨n / 4, by omega⟩
        exact ⟨⟨k, Nat.pos_of_ne_zero (by aesop_cat)⟩,
          Or.imp (fun h => PNat.eq h) (fun h => PNat.eq h) hk⟩
      · have h_rec : (f (4 * k + 1) : ℕ) + (f k : ℕ) = 2 * (f (2 * k + 1) : ℕ) := by
          exact congrArg PNat.val (h₃ k)
        have h_g_rec : g (4 * k + 1) = 2 * g (2 * k + 1) - g k := by
          convert g_mod4_1 (4 * k + 1) _ _ using 1 <;> norm_num [Nat.add_mod, Nat.mul_mod]
          · norm_num [show (4 * k + 1 + 1 : ℕ) = 2 * (2 * k + 1) by ring]
          · linarith [PNat.pos k]
        simp_all +decide [Nat.add_mod, Nat.mul_mod]
        rw [← h_rec, Nat.add_sub_cancel]
      · have h_ind_k : f k = g k := by
          exact ih k <| by
            show (k : ℕ) < 4 * k + 3
            linarith
        have h_ind_2k1 : f (2 * k + 1) = g (2 * k + 1) := by
          exact ih _ <| by
            show (2 * k + 1 : ℕ) < 4 * k + 3
            linarith only [k.pos]
        have h_g_4k3 : g (4 * k + 3) = 3 * g (2 * k + 1) - 2 * g k := by
          convert g_mod4_3 (4 * k + 3) _ _ using 1 <;> norm_num [Nat.add_mod, Nat.mul_mod]
          · norm_num [show 4 * (k : ℕ) = 2 * (2 * (k : ℕ)) by ring]
          · linarith [PNat.pos k]
        have := h₄ k
        replace := congrArg PNat.val this
        norm_num [h_ind_k, h_ind_2k1, h_g_4k3] at this ⊢
        exact eq_tsub_of_add_eq this

lemma count_g_fixed :
    ((Finset.Icc (1 : ℕ+) 1988).filter (fun n : ℕ+ => g (n : ℕ) == (n : ℕ))).card = 92 := by
  native_decide

problem imo1988_p3 (f : ℕ+ → ℕ+)
    (h₀ : f 1 = 1)
    (h₁ : f 3 = 3)
    (h₂ : ∀ n, f (2 * n) = f n)
    (h₃ : ∀ n, f (4 * n + 1) + f n = 2 * f (2 * n + 1))
    (h₄ : ∀ n, f (4 * n + 3) + 2 * f n = 3 * f (2 * n + 1)) :
    Set.ncard {n | n ≤ 1988 ∧ f n = n} = solution := by
  have key := f_eq_g f h₀ h₁ h₂ h₃ h₄
  have hset :
      {n | n ≤ 1988 ∧ f n = n} =
        ↑((Finset.Icc (1 : ℕ+) 1988).filter (fun n : ℕ+ => g (n : ℕ) == (n : ℕ))) := by
    ext n
    constructor
    · intro hn
      rcases hn with ⟨hle, hfix⟩
      have hgfix : g (n : ℕ) = (n : ℕ) := by
        simpa [hfix] using (key n).symm
      simp [hle, hgfix]
    · intro hn
      rcases (by simpa using hn : n ≤ 1988 ∧ g (n : ℕ) = (n : ℕ)) with ⟨hle, hgfix⟩
      have hfix : f n = n := by
        apply PNat.eq
        simpa [hgfix] using key n
      exact ⟨hle, hfix⟩
  rw [hset, Set.ncard_coe_finset]
  simpa [solution] using count_g_fixed

end Imo1988P3
