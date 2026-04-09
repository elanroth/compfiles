/-
Copyright (c) 2025 the Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/

import Mathlib

/-!
# International Mathematical Olympiad 2022, Problem 3

Let k be a positive integer and let S be a finite set of odd prime
integers. Prove that there is at most one way (up to rotation and reflection)
to place the elements of S around a circle such that the product of any
two neighbors is of the form x² + x + k for some positive integer x.

-/

namespace Imo2022P3

open scoped Finset

/-- The condition of the problem on a placement of numbers round a circle. -/
def Condition (k : ℕ) (S : Finset ℕ) (p : Fin #S ≃ S) : Prop :=
  ∀ i, have : NeZero #S := ⟨i.pos.ne'⟩
  ∃ x : ℕ, 0 < x ∧ ((p i : ℕ) * (p (i + 1) : ℕ)) = x ^ 2 + x + k

/-
The original statement is false for S = ∅ because the conclusion requires
∃ i : Fin 0, which is impossible. We add 0 < #S as a hypothesis to fix this.
The mathematical content is unchanged: empty S has a vacuously unique arrangement.
-/

lemma case_one {α : Type*} (S : Finset α) (hS : #S = 1)
    (p₁ p₂ : Fin #S ≃ ↥S) :
    ∀ j : Fin #S, p₂ j = p₁ (j + (⟨0, hS ▸ Nat.one_pos⟩ : Fin #S)) := by
  obtain ⟨ x, hx ⟩ := Finset.card_eq_one.mp hS
  grind

lemma case_two {α : Type*} [DecidableEq α] (S : Finset α) (hS : #S = 2)
    (p₁ p₂ : Fin #S ≃ ↥S) :
    (∃ i : Fin #S, ∀ j, p₂ j = p₁ (j + i)) ∨
    ∃ i : Fin #S, ∀ j, p₂ j = p₁ (Fin.rev j + i) := by
  obtain ⟨a, b, hab⟩ : ∃ a b : α, a ≠ b ∧ S = {a, b} := by
    rw [Finset.card_eq_two] at hS; tauto
  obtain ⟨i₁, _, hi₁, _⟩ : ∃ i₁ i₂ : Fin #S,
      p₁ i₁ = ⟨a, by simp [hab]⟩ ∧ p₁ i₂ = ⟨b, by simp [hab]⟩ ∧ i₁ ≠ i₂ := by
    obtain ⟨i₁, hi₁⟩ := p₁.surjective ⟨a, by simp +decide [hab]⟩
    obtain ⟨i₂, hi₂⟩ := p₁.surjective ⟨b, by simp +decide [hab]⟩
    use i₁, i₂; aesop
  obtain ⟨j₁, _, _, _⟩ : ∃ j₁ j₂ : Fin #S,
      p₂ j₁ = ⟨a, by simp [hab]⟩ ∧ p₂ j₂ = ⟨b, by simp [hab]⟩ ∧ j₁ ≠ j₂ := by
    exact ⟨p₂.symm ⟨a, by simp +decide [hab]⟩, p₂.symm ⟨b, by simp +decide [hab]⟩,
      by simp +decide, by simp +decide, by simp +decide [hab]⟩
  exact Or.inl ⟨i₁ - j₁, fun j => by grind⟩

set_option maxHeartbeats 400000 in
/-- Automorphisms of the cycle graph on Fin n (n ≥ 3) are rotations or reflections.
    If σ maps each pair (i, i+1) to a pair that is also adjacent (distance 1 in the cycle),
    then σ is a rotation or reflection. -/
lemma cycle_auto {n : ℕ} (hn : 3 ≤ n) (σ : Fin n ≃ Fin n)
    (hadj : ∀ i : Fin n, have : NeZero n := ⟨by omega⟩;
      σ (i + 1) = σ i + 1 ∨ σ i = σ (i + 1) + 1) :
    have : NeZero n := ⟨by omega⟩;
    (∃ c : Fin n, ∀ j, σ j = j + c) ∨
    ∃ c : Fin n, ∀ j, σ j = Fin.rev j + c := by
  by_contra! h_contra
  have h_ind : ∀ i : Fin n, σ i = σ ⟨0, by linarith⟩ + i := by
    rcases n with (_ | _ | n) <;> norm_num at *
    · contradiction
    · have h_ind_step : ∀ i : Fin (n + 2), σ (i + 1) = σ i + 1 := by
        intro i
        induction' i using Fin.induction with i ih
        · cases hadj 0 <;> simp_all +decide [add_comm]
          have h_dec : ∀ i : Fin (n + 2), σ (i + 1) = σ i - 1 := by
            intro i; induction' i using Fin.inductionOn with i IH; aesop
            cases hadj (Fin.castSucc i + 1) <;> simp_all +decide [add_comm, add_left_comm]
            simp_all +decide [Fin.ext_iff, Fin.val_add]
            have := Nat.mod_add_div (i + 1 + 1) (n + 1 + 1)
            simp_all +arith +decide [Nat.mod_eq_of_lt]
            nlinarith [show (i + 2 : ℕ) / (n + 2) = 1 by nlinarith]
          have h_rev : ∀ i : Fin (n + 2), σ i = σ 0 - i := by
            intro i; induction' i using Fin.inductionOn with i IH; aesop
            convert h_dec (Fin.castSucc i) using 1
            simp +decide [IH, sub_sub]
            rw [IH, sub_sub]; norm_num [Fin.ext_iff, Fin.val_sub]
          have h_ref : ∃ c : Fin (n + 2), ∀ i : Fin (n + 2), σ i = c + Fin.rev i := by
            use σ 0 - Fin.rev 0
            intro i; rw [h_rev i]; simp +decide [Fin.rev]
            norm_num [Fin.ext_iff, Fin.val_sub, Fin.val_add]
            rw [show n + 1 + 1 - (i : ℕ) = n + 1 - (i : ℕ) + 1 by omega]; ring
          exact False.elim <|
            ‹(∀ c : Fin (n + 1 + 1), ∃ j, ¬σ j = c + j) ∧
              ∀ c : Fin (n + 1 + 1), ∃ j, ¬σ j = c + j.rev›.2 _ |>
            fun ⟨j, hj⟩ => hj <| h_ref.choose_spec j
        · cases hadj (Fin.castSucc i + 1) <;> simp_all +decide [add_assoc]
          simp_all +decide [Fin.ext_iff, Fin.val_add]
          rw [Nat.mod_eq_of_lt] at * <;> try linarith [Fin.is_lt i]
          by_cases h_eq : (i : ℕ) + 1 + 1 = n + 1 + 1
          · norm_num [show i = Fin.last n from Fin.ext (by linarith)] at *
            linarith
          · exact lt_of_le_of_ne (by linarith [Fin.is_lt i]) h_eq
      intro i; induction' i using Fin.inductionOn with i IH <;> simp_all +decide [add_assoc]
      simpa [add_assoc, IH] using h_ind_step (Fin.castSucc i)
  exact h_contra.1 (σ ⟨0, by linarith⟩) |> fun ⟨j, hj⟩ => hj <| by rw [h_ind j, add_comm]

/-- The key number-theoretic result: the permutation σ = p₂.trans p₁.symm
    preserves adjacency in the cycle graph.
    This is the deep content of IMO 2022 Problem 3: any two valid circular
    arrangements of S must have the same edge set, which forces σ to map
    consecutive elements to consecutive elements. -/
lemma arrangement_preserves_adjacency
    {k : ℕ} (hk : 0 < k) (S : Finset ℕ) (hS : ∀ p ∈ S, Odd p ∧ Nat.Prime p)
    (hn : 3 ≤ #S)
    {p₁ p₂ : Fin #S ≃ S} (hp₁ : Condition k S p₁) (hp₂ : Condition k S p₂) :
    let σ := p₂.trans p₁.symm
    ∀ i : Fin #S, have : NeZero #S := ⟨by omega⟩;
      σ (i + 1) = σ i + 1 ∨ σ i = σ (i + 1) + 1 := by
  sorry

theorem imo2022_p3
    {k : ℕ} (hk : 0 < k) (S : Finset ℕ) (hS : ∀ p ∈ S, Odd p ∧ Nat.Prime p)
    (hne : 0 < #S)
    {p₁ p₂ : Fin #S ≃ S} (hp₁ : Condition k S p₁) (hp₂ : Condition k S p₂) :
    (∃ i, ∀ j, p₂ j = p₁ (j + i)) ∨ ∃ i, ∀ j, p₂ j = p₁ (Fin.rev j + i) := by
  by_cases h : 3 ≤ S.card
  · haveI : NeZero #S := ⟨by omega⟩
    set σ : Fin #S ≃ Fin #S := p₂.trans p₁.symm
    have h_adj : ∀ i : Fin #S, σ (i + 1) = σ i + 1 ∨ σ i = σ (i + 1) + 1 :=
      arrangement_preserves_adjacency hk S hS h hp₁ hp₂
    have h_cycle := cycle_auto h σ h_adj
    exact Or.imp
      (fun ⟨c, hc⟩ => ⟨c, fun j => by
        have := hc j
        simp [σ, Equiv.trans_apply] at this
        rw [← this]; simp [Equiv.apply_symm_apply]⟩)
      (fun ⟨c, hc⟩ => ⟨c, fun j => by
        have := hc j
        simp [σ, Equiv.trans_apply] at this
        rw [← this]; simp [Equiv.apply_symm_apply]⟩)
      h_cycle
  · push_neg at h
    by_cases h1 : #S = 1
    · left; exact ⟨⟨0, hne⟩, case_one S h1 p₁ p₂⟩
    · have h2 : #S = 2 := by omega
      exact case_two S h2 p₁ p₂

end Imo2022P3
