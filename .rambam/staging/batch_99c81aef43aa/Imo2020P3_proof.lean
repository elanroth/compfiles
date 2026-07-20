/-
Copyright (c) 2025 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/

import Mathlib.Tactic
import Mathlib.Combinatorics.Euler
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic

import ProblemExtraction

problem_file {
  tags := [.Combinatorics]
}

/-!
# International Mathematical Olympiad 2020, Problem 3

There are 4n pebbles of weights 1,2,3,...,4n. Each pebble is colored
in one of n colors and there are four pebbles of each color. Show
that we can arrange the pebbles into two piles such that the total
weights of both piles are the same, and each pile contains two
pebbles of each color.

## Proof sketch

Key idea: pair pebble i (0-indexed: weight i+1) with pebble (4n-1-i) (weight 4n-i).
Each pair {i, 4n-1-i} has total weight (i+1) + (4n-i) = 4n+1.
There are 2n such pairs.

Build a multigraph G on vertex set Fin n (colors), where each pair {i, 4n-1-i}
contributes an edge between c(i) and c(4n-1-i).
Since each color has exactly 4 pebbles, each vertex has degree exactly 4 (4-regular).

We need to 2-color the edges so each vertex gets exactly 2 of each color.
Equivalently: orient edges so each vertex has in-degree 2 and out-degree 2,
then send "forward" edges to pile S and "backward" edges to Sᶜ.

In a 4-regular multigraph, each connected component has an Eulerian circuit.
Alternate coloring along the circuit: each vertex sees edges alternately blue/green,
giving exactly 2 blue and 2 green at each vertex (since degree = 4, even).

For the Lean proof: we use induction on n with a direct combinatorial construction.
-/

namespace Imo2020P3

open scoped Finset

/-- Helper: the pair partner of index i in Fin (4*n) is 4n-1-i -/
private def partner (n : ℕ) (i : Fin (4 * n)) : Fin (4 * n) :=
  ⟨4 * n - 1 - i.val, by omega⟩

/-- The partner is an involution -/
private lemma partner_partner (n : ℕ) (i : Fin (4 * n)) :
    partner n (partner n i) = i := by
  simp [partner]
  omega

/-- Pebble i and its partner have weights summing to 4n+1 -/
private lemma partner_weight_sum (n : ℕ) (i : Fin (4 * n)) :
    (i.val + 1) + ((partner n i).val + 1) = 4 * n + 1 := by
  simp [partner]
  omega

/-- A pile S with its complement have equal sums iff for every complementary pair
    {i, partner i}, exactly one of i, partner i is in S. -/
private lemma equal_sums_iff_balanced_pairs {n : ℕ} (S : Finset (Fin (4 * n)))
    (hbal : ∀ i : Fin (4 * n), (i ∈ S) ↔ (partner n i ∉ S)) :
    ∑ i ∈ S, ((i : ℕ) + 1) = ∑ i ∈ Sᶜ, ((i : ℕ) + 1) := by
  -- Each pair {i, partner i} contributes (4n+1) to the total, split 1:0 or 0:1 between S and Sᶜ.
  -- Sum of all pebbles = 1+2+...+4n = 2n(4n+1). Half = n(4n+1).
  -- hbal says S picks exactly one from each pair, so both halves sum to n(4n+1).
  sorry

/-- Main theorem -/
problem imo2020_p3 {n : ℕ} {c : Fin (4 * n) → Fin n} (h : ∀ i, #{j | c j = i} = 4) :
    ∃ S : Finset (Fin (4 * n)), ∑ i ∈ S, ((i : ℕ) + 1) = ∑ i ∈ Sᶜ, ((i : ℕ) + 1) ∧
      ∀ i, #{j ∈ S | c j = i} = 2 := by
  -- Strategy: use the Eulerian circuit / edge-coloring approach.
  -- For each color i, the 4 pebbles of color i can be paired up in two complementary pairs.
  -- We assign each complementary pair {k, 4n-1-k} to pile S or Sᶜ.
  -- For each color, we put 2 of its pebbles in S and 2 in Sᶜ.
  --
  -- Concretely: we prove by induction on n.
  -- Base case n=0: trivial (empty).
  -- Inductive step: remove the color with the smallest index, find its 4 pebbles,
  --   pair them compatibly, then apply IH to the remaining n-1 colors.
  --
  -- Alternative direct construction: for each color i, let {a1 < a2 < a3 < a4} be the
  -- four pebbles of color i. Put a1 and a4's partner situation in S based on parity.
  -- The Euler-circuit argument handles the most general case.
  --
  -- We use the following constructive approach:
  -- Define a graph where vertices are colors and edges are complementary pairs.
  -- Find a 2-coloring of edges in each Eulerian circuit, then S = blue pairs.
  sorry

end Imo2020P3
