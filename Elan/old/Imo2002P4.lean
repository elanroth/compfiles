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
# International Mathematical Olympiad 2002, Problem 4

Prove that there are infinitely many distinct pairs $(a,b)$ of
relatively prime positive integers $a>1$ and $b>1$ such that
$a^b+b^a$ is divisible by $a+b$.
-/

namespace Imo2002P4



snip begin

snip end

/-!
Minimal helpers: different ways to represent the set of divisors (factors)
of a natural number and a couple of tiny lemmas connecting the
representations.  Two variants are provided below:

- `factors_set n` is the `Set Nat` {d | d ∣ n}.
- `factors_subtype n` is the subtype `{d : Nat // d ∣ n}`.
- `factors_finset n` is a computable `Finset Nat` obtained by filtering
	`Finset.range (n+1)` by divisibility.  The `finset` version is usually
	preferable when you need a finite, iterable collection for computation.
-/

/- set of divisors -/
def factors_set (n : Nat) : Set Nat := { d | d ∣ n }

/- subtype of divisors -/
def factors_subtype (n : Nat) := { d : Nat // d ∣ n }

/- finset of divisors (computable): restrict to `0..n` and filter by `∣ n`. -/
def factors_finset (n : Nat) : Finset Nat := (Finset.range (n + 1)).filter fun d => d ∣ n

def list_of_n (n : Nat) : List Nat :=
  List.finRange n
  -- match n with
  -- | Nat.zero => []
  -- | Nat.succ k => list_of_n k ++ [k + 1]

-- #check List.finRange

def factors_list (n : Nat) : List Nat := (list_of_n n).filter (fun d => d ∣ n && d != n)

def fancy_sum (l : List Nat) : Nat :=
  match l with
  | fst :: snd :: tl => fst * snd + fancy_sum (snd :: tl)
  | _ => 0

def sum10 : List Nat :=
  factors_list 10


problem Imo2002P4 : ∀ n, fancy_sum (factors_list n) < n ^ 2 := by
  sorry

end Imo2002P4
