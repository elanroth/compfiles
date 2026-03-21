/-
Copyright (c) 2025 Elan Roth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elan Roth
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Set.Card
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.Ring

import Mathlib.Data.Finset.Basic
import ProblemExtraction

problem_file { tags := [.NumberTheory]}

/-!
# International Mathematical Olympiad 2005, Problem 2

Let a1, a2, . . . be a sequence of integers with infinitely many positive and negative
terms. Suppose that for every positive integer n the numbers a1, a2, . . . , an leave
n different remainders upon division by n. Prove that every integer occurs exactly
once in the sequence.
-/

namespace Imo2002P4

def seq := ℕ → ℤ

def finite_seq (f : seq) (n : ℕ) : Fin n → ℤ :=
  fun i => f i

def condition_inf (f : seq) : Prop := Infinite { k // f k < 0 } ∧ Infinite { k // f k > 0 }

def condition_remainders (f : seq) : Prop := ∀ n i j, i < j → j < n → (f i) % n != (f j) % n




theorem main : ∀ f : seq, condition_inf f → condition_remainders f →
               ∀ y : ℤ, ∃ n : ℕ, ∀ k : ℕ, f n = y ∧ (f k = f n → k = n) := by
              intro f Hinf Hrem y
              have claim_1 : ∀ i j, i < j → abs (f i - f j) < j := by
                intro i j
                by_contra
                let n := abs (f i - f j)
                unfold condition_remainders at *
                sorry

              -- have claim_2 : ∀ n, 



              by_contra h
              sorry
