/-
IMO 1971 P3 — All sorries for Aristotle

Construction: build a sequence of exponents n₁, n₂, ... recursively.
Key: if p odd prime divides 2^a - 3 and (p-1) | N, then p ∤ 2^N - 3
(Fermat: 2^N ≡ 1 mod p, so 2^N - 3 ≡ -2 mod p, and p ∤ 2 since p odd).
-/

import Mathlib.Tactic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.ZMod.Basic

/-- For n ≥ 2, 2^n - 3 is odd. -/
lemma two_pow_sub_three_odd (n : ℕ) (hn : 2 ≤ n) : ¬ 2 ∣ (2 ^ n - 3) := by
  intro ⟨k, hk⟩
  have hpos : 3 ≤ 2 ^ n := by
    calc 3 ≤ 4 := by norm_num
      _ = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  sorry

/-- Core Fermat lemma: if p odd prime, p ∣ 2^a - 3 (a ≥ 2), and (p-1) ∣ N,
    then p ∤ 2^N - 3.
    Proof: 2^N ≡ 1 (mod p) by Fermat → 2^N - 3 ≡ -2 (mod p) → p ∤ -2 since p odd. -/
lemma fermat_key (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
    (a : ℕ) (ha : 2 ≤ a) (hdvd : p ∣ 2 ^ a - 3)
    (N : ℕ) (hN : (p - 1) ∣ N) : ¬ p ∣ 2 ^ N - 3 := by
  sorry

/-- Given any finite set S of exponents (each ≥ 3), there exists N ≥ 3 with
    N ∉ S and Coprime (2^N - 3) (2^m - 3) for all m ∈ S.
    Proof: set N = ∏_{m∈S} ∏_{p|2^m-3} (p-1) (or a suitable multiple ≥ 3).
    Then fermat_key kills every prime factor of every 2^m - 3. -/
lemma extension_exists (S : Finset ℕ) (hS : ∀ m ∈ S, 3 ≤ m) :
    ∃ N : ℕ, 3 ≤ N ∧ N ∉ S ∧ ∀ m ∈ S, Nat.Coprime (2 ^ N - 3) (2 ^ m - 3) := by
  sorry

/-- Build an injective sequence with all exponents ≥ 3 and pairwise-coprime values.
    Proof: iterate extension_exists starting from S = ∅. -/
lemma pairwise_coprime_seq :
    ∃ seq : ℕ → ℕ,
      Function.Injective seq ∧
      (∀ i, 3 ≤ seq i) ∧
      ∀ i j, i ≠ j → Nat.Coprime (2 ^ (seq i) - 3) (2 ^ (seq j) - 3) := by
  sorry

theorem imo1971_p3 :
    ∃ s : Set ℕ+,
      s.Infinite ∧
      s.Pairwise fun m n ↦ Nat.Coprime (2 ^ n.val - 3) (2 ^ m.val - 3) := by
  obtain ⟨seq, hseq_inj, hseq_ge, hseq_cop⟩ := pairwise_coprime_seq
  let seq' : ℕ → ℕ+ := fun i => ⟨seq i, by linarith [hseq_ge i]⟩
  refine ⟨Set.range seq', Set.infinite_range_of_injective ?_, ?_⟩
  · intro a b hab
    simp [seq'] at hab
    apply hseq_inj
    grind
  · sorry
  -- · rintro ⟨_, i, rfl⟩ ⟨_, j, rfl⟩ hmn
  --   simp only [seq']
  --   apply hseq_cop
  --   intro hij
  --   apply hmn
  --   simp [seq', hij]
