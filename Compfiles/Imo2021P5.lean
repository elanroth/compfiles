/-
Copyright (c) 2025 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
import Mathlib

import ProblemExtraction

problem_file {
  problemImportedFrom :=
    "https://github.com/jsm28/IMOLean/blob/main/IMO/IMO2021P5.lean"
}

/-!
# International Mathematical Olympiad 2021, Problem 5

Two squirrels, Bushy and Jumpy, have collected 2001 walnuts for winter.
Jumpy numbers the walnuts from 1 to 2021, and digs 2021 little holes
in a circular pattern around their favorite tree. The next morning,
Jumpy notices that Bushy had placed one walnut into each hole, but
had paid no attention to the numbering. Unhappy, Jumpy decides to
reorder the walnuts by performing a sequence of 2021 moves. In the kth
move, Jump swaps the positions of the two walnuts adjacent to walnut k.

Prove that there exists a value of k such that, on the kth move, Jumpy
swaps some walnuts a and b such that a < k < b.
-/

namespace Imo2021P5

/-- The arrangement of walnuts, as an equiv from holes to walnuts (0-based). -/
abbrev Position : Type := Fin 2021 ≃ Fin 2021

/-- The numbers of the walnuts swapped in move `k` (0-based), given the position. -/
def Position.swapped (p : Position) (k : Fin 2021) : Fin 2021 × Fin 2021 :=
  (p ((p.symm k) - 1), p ((p.symm k) + 1))

/-- A single move, on a pair of position and move number. -/
def move (p : Position × Fin 2021) : Position × Fin 2021 :=
  (p.1.trans (Equiv.swap (p.1.swapped p.2).1 (p.1.swapped p.2).2), p.2 + 1)

/-- The position after `n` moves. -/
def Position.nth (p : Position) (n : Fin 2021) : Position := (move^[n] (p, 0)).1

snip begin

private def state (p : Position) (n : ℕ) : Position × Fin 2021 := move^[n] (p, 0)

private def central (p : Position) (k : Fin 2021) : Fin 2021 := (p.nth k).symm k

private def lowerSwap (p : Position) (k : Fin 2021) : Prop :=
  ((p.nth k).swapped k).1 < k ∧ ((p.nth k).swapped k).2 < k

private lemma state_moveNumber (p : Position) (n : ℕ) (hn : n < 2021) :
    (state p n).2 = ⟨n, hn⟩ := by
  induction n <;> simp_all +decide [Function.iterate_succ_apply', state]
  simp_all +decide [move]
  rename_i k hk; rw [hk (Nat.lt_of_succ_lt hn)] ; norm_num [Fin.add_def, Nat.mod_eq_of_lt hn]

private lemma state_position (p : Position) (k : Fin 2021) : (state p k).1 = p.nth k := by
  rfl

private lemma no_straddle_separates (p : Position)
    (h : ∀ k, ¬((((p.nth k).swapped k).1 < k ∧ k < ((p.nth k).swapped k).2) ∨
      (((p.nth k).swapped k).2 < k ∧ k < ((p.nth k).swapped k).1))) (k : Fin 2021) :
    lowerSwap p k ∨
      (k < ((p.nth k).swapped k).1 ∧ k < ((p.nth k).swapped k).2) := by
  grind +locals

set_option maxHeartbeats 800000 in
private lemma black_position_invariant (p : Position)
    (h : ∀ k, ¬((((p.nth k).swapped k).1 < k ∧ k < ((p.nth k).swapped k).2) ∨
      (((p.nth k).swapped k).2 < k ∧ k < ((p.nth k).swapped k).1))) :
    ∀ m : ℕ, m ≤ 2021 → ∀ x : Fin 2021,
      ((state p m).1 x).val < m ↔
        ∃ k : Fin 2021, k.val < m ∧ central p k = x := by
  -- We proceed by induction on $m$.
  intro m hm
  induction' m with m ih
  · aesop
  · -- By definition of `state`, we know that `(state p (m + 1)).1` is obtained by applying `move` to `(state p m).1`.
    have h_state_succ : (state p (m + 1)).1 = ((state p m).1).trans (Equiv.swap ((state p m).1.swapped ((state p m).2)).1 ((state p m).1.swapped ((state p m).2)).2) := by
      exact congr_arg Prod.fst (Function.iterate_succ_apply' move m (p, 0))
    -- By definition of `central`, we know that `central p m = (state p m).1.symm m`.
    have h_central : central p ⟨m, by linarith⟩ = (state p m).1.symm ⟨m, by linarith⟩ := by
      exact state_position p ⟨m, by linarith⟩ ▸ rfl
    -- By definition of `swapped`, we know that `swapped p m` are the two neighbors of `m` in the current position.
    have h_swapped : ((state p m).1.swapped ((state p m).2)).1 < ⟨m, by linarith⟩ ∧ ((state p m).1.swapped ((state p m).2)).2 < ⟨m, by linarith⟩ ∨ ⟨m, by linarith⟩ < ((state p m).1.swapped ((state p m).2)).1 ∧ ⟨m, by linarith⟩ < ((state p m).1.swapped ((state p m).2)).2 := by
      have := no_straddle_separates p h ⟨m, by linarith⟩
      have := state_moveNumber p m (by linarith) ; have := state_position p ⟨m, by linarith⟩ ; aesop
    cases h_swapped <;> simp_all +decide [Equiv.swap_apply_def]
    · intro x; specialize ih (Nat.le_of_succ_le hm) x; split_ifs <;> simp_all +decide [Fin.ext_iff]
      · grind +extAll
      · grind +qlia
      · grind
    · intro x; split_ifs <;> simp_all +decide [Fin.ext_iff]
      · grind
      · grind +revert
      · grind +qlia

private lemma central_bijective (p : Position)
    (h : ∀ k, ¬((((p.nth k).swapped k).1 < k ∧ k < ((p.nth k).swapped k).2) ∨
      (((p.nth k).swapped k).2 < k ∧ k < ((p.nth k).swapped k).1))) :
    Function.Bijective (central p) := by
  -- By the black position invariant at m=2021, for every hole x, its current occupant is a Fin 2021 and hence has val<2021. Thus, the invariant yields k with central p k=x. Therefore, central is surjective.
  have h_surj : ∀ x : Fin 2021, ∃ k : Fin 2021, central p k = x := by
    intro x
    have := black_position_invariant p h 2021 (by omega) x
    simp at this
    exact this
  generalize_proofs at *; exact ⟨Finite.injective_iff_surjective.mpr h_surj, h_surj⟩

private lemma adjacent_central_opposite (p : Position)
    (h : ∀ k, ¬((((p.nth k).swapped k).1 < k ∧ k < ((p.nth k).swapped k).2) ∨
      (((p.nth k).swapped k).2 < k ∧ k < ((p.nth k).swapped k).1)))
    (a b : Fin 2021) (hab : central p a + 1 = central p b) :
    lowerSwap p a ↔ ¬lowerSwap p b := by
  by_cases hba : b < a
  · -- At state b, central a is previous neighbor of central b, and because a is later, occupant there > b, forcing lowerSwap b false.
    have h_lowerSwap_b_false : ¬lowerSwap p b := by
      have h_central_a_gt_b : (p.nth b) (central p a) > b := by
        have h_central_a_gt_b : ¬∃ k : Fin 2021, k.val < b.val ∧ central p k = central p a := by
          have := central_bijective p h
          exact fun ⟨k, hk₁, hk₂⟩ => by have := this.injective hk₂; exact absurd this (ne_of_lt (lt_trans hk₁ hba))
        have := black_position_invariant p h b (by omega) (central p a)
        simp_all +decide [Fin.ext_iff]
        grind +locals
      grind +locals
    -- Since `central p b` is the next neighbor of `central p a`, the occupant of `central p b` is the second component of `swapped` at `a`.
    have h_second_component : ((state p a).1 (central p b)) = ((p.nth a).swapped a).2 := by
      grind +locals
    grind +suggestions
  · -- At state a, hole central b is not among earlier central holes, so by black_position_invariant its occupant is not <a.
    have h_not_lt_a : ¬(p.nth a (central p b)).val < a := by
      have h_not_lt_a : ¬∃ k : Fin 2021, k.val < a ∧ central p k = central p b := by
        have := central_bijective p h
        exact fun ⟨k, hk₁, hk₂⟩ => by have := this.injective hk₂; exact absurd this (by exact ne_of_lt (lt_of_lt_of_le hk₁ (le_of_not_gt hba)))
      convert black_position_invariant p h a (by omega) (central p b) |>.not.mpr _
      all_goals first
        | rfl
        | exact h_not_lt_a
    -- As central b is adjacent clockwise to central a (`hab`), this occupant equals the second component of swapped at a.
    have h_second_comp : (p.nth a (central p b)) = ((p.nth a).swapped a).2 := by
      simp +decide [← hab, Position.swapped]
      rfl
    have h_lowerSwap_b_true : (p.nth b (central p a)).val < b := by
      convert black_position_invariant p h b (by omega) (central p a) |>.2 _
      all_goals first
        | rfl
        | grind [state_position]
    have h_lowerSwap_b_true : (p.nth b (central p a)) = ((p.nth b).swapped b).1 := by
      unfold Position.swapped
      simp +decide
      rw [show (p.nth b).symm b = central p b from rfl, ← hab]
      simp +decide
    have := no_straddle_separates p h b; simp_all +decide [lowerSwap]
    grind

private lemma odd_cycle_not_two_colorable (color : Fin 2021 → Prop)
    [DecidablePred color] (h : ∀ x, color x ↔ ¬color (x + 1)) : False := by
  have h_ind : ∀ x : Fin 2021, color x ↔ color 0 = (x.val % 2 = 0) := by
    intro x; induction' x using Fin.inductionOn with x ih; norm_num at *
    specialize h (Fin.castSucc x) ; norm_num [Nat.add_mod] at * ; by_cases h₁ : (x : ℕ) % 2 = 0 <;> simp +decide [h₁] at ih h ⊢
    · grind
    · grind
  have := h 2020
  simp +decide [h_ind 2020] at this

snip end

problem imo2021_p5 (p : Position) :
    ∃ k, (((p.nth k).swapped k).1 < k ∧ k < ((p.nth k).swapped k).2) ∨
      (((p.nth k).swapped k).2 < k ∧ k < ((p.nth k).swapped k).1) := by
  revert p
  -- By contradiction, assume there exists a position \( p \) such that no move straddles.
  by_contra h_contra
  push Not at h_contra
  obtain ⟨p, hp⟩ := h_contra
  have := Imo2021P5.central_bijective p (fun k => by
    grind)
  generalize_proofs at *
  set color : Fin 2021 → Prop := fun x => lowerSwap p (Equiv.ofBijective (central p) this |>.symm x)
  have h_adjacent : ∀ x : Fin 2021, color x ↔ ¬color (x + 1) := by
    intro x
    set a := (Equiv.ofBijective (central p) this).symm x
    set b := (Equiv.ofBijective (central p) this).symm (x + 1)
    have h_central_a : central p a = x := by
      exact Equiv.apply_symm_apply (Equiv.ofBijective (central p) this) x
    have h_central_b : central p b = x + 1 := by
      exact Equiv.apply_symm_apply (Equiv.ofBijective (central p) this) _
    have h_adjacent_ab : central p a + 1 = central p b := by
      rw [h_central_a, h_central_b]
    have h_color_ab : lowerSwap p a ↔ ¬lowerSwap p b := by
      apply Imo2021P5.adjacent_central_opposite p (fun k => by
        grind) a b h_adjacent_ab
    simpa [color] using h_color_ab
  letI : DecidablePred color := Classical.decPred color
  exact Imo2021P5.odd_cycle_not_two_colorable color h_adjacent

end Imo2021P5
