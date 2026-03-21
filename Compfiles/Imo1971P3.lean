/-
Copyright (c) 2024 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InternLM-MATH LEAN Formalizer v0.1
-/

import Mathlib.Tactic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.NumberTheory.LucasPrimality

import ProblemExtraction

problem_file { tags := [.NumberTheory] }

/-!
# International Mathematical Olympiad 1971, Problem 3

Prove that we can find an infinite set of positive integers of the form 2^n - 3
(where n is a positive integer) every pair of which are relatively prime.
-/

namespace Imo1971P3

snip begin

/-!
## Proof strategy

We construct a sequence of exponents n₁, n₂, n₃, ... (all ≥ 3) such that
2^(nᵢ) - 3 and 2^(nⱼ) - 3 are coprime for i ≠ j.

**Key lemma (Fermat):** If p is an odd prime dividing 2^a - 3, and (p-1) ∣ N,
then p does NOT divide 2^N - 3.

*Proof:* By Fermat's little theorem, 2^(p-1) ≡ 1 (mod p), so 2^N ≡ 1 (mod p).
Thus 2^N - 3 ≡ -2 (mod p). If p ∣ 2^N - 3 then p ∣ 2, but p is odd: contradiction.

**Construction:** Let n₁ = 3. Given n₁,...,nₖ, let P be the set of all odd prime
factors of 2^(n₁) - 3, ..., 2^(nₖ) - 3. Choose N divisible by (p-1) for all p ∈ P.
Then 2^N - 3 is coprime to all previous values, so set nₖ₊₁ = N.
-/

/-- For n ≥ 2, 2^n - 3 is positive (as natural numbers). -/
lemma two_pow_sub_three_pos (n : ℕ) (hn : 2 ≤ n) : 0 < 2 ^ n - 3 := by
  have h : 3 < 2 ^ n := by
    calc 3 < 4 := by norm_num
    _ = 2^2 := by norm_num
    _ ≤ 2^n := Nat.pow_le_pow_right (by norm_num) hn
  omega

/-- For n ≥ 2, 2^n - 3 is odd (so all prime factors are odd). -/
lemma two_pow_sub_three_odd (n : ℕ) (hn : 2 ≤ n) : ¬ 2 ∣ (2 ^ n - 3) := by
  intro ⟨k, hk⟩
  have hpos : 3 ≤ 2 ^ n := by
    calc 3 ≤ 4 := by norm_num
    _ = 2^2 := by norm_num
    _ ≤ 2^n := Nat.pow_le_pow_right (by norm_num) hn
  have hodd : 2 ^ n % 2 = 0 := Nat.two_pow_mod_two_eq_zero (by omega)
  omega

/-- Any prime factor of 2^n - 3 (with n ≥ 2) is an odd prime. -/
lemma prime_factor_odd (n : ℕ) (hn : 2 ≤ n) (p : ℕ) (hp : p.Prime)
    (hdvd : p ∣ 2 ^ n - 3) : p ≠ 2 := by
  intro h
  rw [h] at hdvd
  exact two_pow_sub_three_odd n hn hdvd

/-- **Core Fermat lemma:** If p is an odd prime with p ∣ 2^a - 3,
    and (p - 1) ∣ N, then p ∤ 2^N - 3.

    Proof: Fermat gives 2^N ≡ 1 (mod p), so 2^N - 3 ≡ -2 (mod p).
    Since p is odd, p ∤ 2, so p ∤ 2^N - 3. -/
lemma fermat_key (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
    (a : ℕ) (ha : 2 ≤ a) (hdvd : p ∣ 2 ^ a - 3)
    (N : ℕ) (hN : (p - 1) ∣ N) : ¬ p ∣ 2 ^ N - 3 := by
  sorry

/-- Given any finite set S of exponents (each ≥ 3), there exists an exponent N ≥ 3
    with N ∉ S such that 2^N - 3 is coprime to 2^m - 3 for every m ∈ S.

    Proof: Let M = ∏_{s ∈ S} ∏_{p | 2^s - 3, p prime} (p - 1). Set N = M (or any
    large enough multiple). By fermat_key, no prime factor of any 2^s - 3 divides
    2^N - 3. Then 2^N - 3 is coprime to ∏_{s ∈ S} (2^s - 3), hence to each factor. -/
lemma extension_exists (S : Finset ℕ) (hS : ∀ m ∈ S, 3 ≤ m) :
    ∃ N : ℕ, 3 ≤ N ∧ N ∉ S ∧ ∀ m ∈ S, Nat.Coprime (2 ^ N - 3) (2 ^ m - 3) := by
  sorry

/-- From extension_exists, build an injective sequence of exponents that is
    pairwise coprime (all values 2^(seq i) - 3 are mutually coprime). -/
lemma pairwise_coprime_seq :
    ∃ seq : ℕ → ℕ,
      Function.Injective seq ∧
      (∀ i, 3 ≤ seq i) ∧
      ∀ i j, i ≠ j → Nat.Coprime (2 ^ (seq i) - 3) (2 ^ (seq j) - 3) := by
  sorry

snip end

problem imo1971_p3 :
   ∃ s : Set ℕ+,
     s.Infinite ∧
     s.Pairwise fun m n ↦ Nat.Coprime (2 ^ n.val - 3) (2 ^ m.val - 3) := by
  obtain ⟨seq, hseq_inj, hseq_ge, hseq_cop⟩ := pairwise_coprime_seq
  -- Lift seq to ℕ+ (valid since seq i ≥ 3 > 0)
  let seq' : ℕ → ℕ+ := fun i => ⟨seq i, by linarith [hseq_ge i]⟩
  refine ⟨Set.range seq', Set.infinite_range_of_injective ?_, ?_⟩
  · -- seq' is injective because seq is
    intro a b hab
    simp [seq'] at hab
    exact hseq_inj hab
  · -- pairwise coprimality
    rintro ⟨m, hm⟩ ⟨i, rfl⟩ ⟨n, hn⟩ ⟨j, rfl⟩ hmn
    simp only [seq']
    apply hseq_cop
    intro hij
    apply hmn
    simp [seq', hij]

end Imo1971P3
