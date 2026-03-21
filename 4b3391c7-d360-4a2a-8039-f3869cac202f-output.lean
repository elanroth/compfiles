/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 4b3391c7-d360-4a2a-8039-f3869cac202f

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- lemma two_pow_sub_three_odd (n : ℕ) (hn : 2 ≤ n) : ¬ 2 ∣ (2 ^ n - 3)

- lemma extension_exists (S : Finset ℕ) (hS : ∀ m ∈ S, 3 ≤ m) :
    ∃ N : ℕ, 3 ≤ N ∧ N ∉ S ∧ ∀ m ∈ S, Nat.Coprime (2 ^ N - 3) (2 ^ m - 3)

- lemma pairwise_coprime_seq :
    ∃ seq : ℕ → ℕ,
      Function.Injective seq ∧
      (∀ i, 3 ≤ seq i) ∧
      ∀ i j, i ≠ j → Nat.Coprime (2 ^ (seq i) - 3) (2 ^ (seq j) - 3)

- theorem imo1971_p3 :
    ∃ s : Set ℕ+,
      s.Infinite ∧
      s.Pairwise fun m n ↦ Nat.Coprime (2 ^ n.val - 3) (2 ^ m.val - 3)

The following was negated by Aristotle:

- lemma fermat_key (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
    (a : ℕ) (ha : 2 ≤ a) (hdvd : p ∣ 2 ^ a - 3)
    (N : ℕ) (hN : (p - 1) ∣ N) : ¬ p ∣ 2 ^ N - 3

Here is the code for the `negate_state` tactic, used within these negations:

```lean
import Mathlib
open Lean Meta Elab Tactic in
elab "revert_all" : tactic => do
  let goals ← getGoals
  let mut newGoals : List MVarId := []
  for mvarId in goals do
    newGoals := newGoals.append [(← mvarId.revertAll)]
  setGoals newGoals

open Lean.Elab.Tactic in
macro "negate_state" : tactic => `(tactic|
  (
    guard_goal_nums 1
    revert_all
    refine @(((by admit) : ∀ {p : Prop}, ¬p → p) ?_)
    try (push_neg; guard_goal_nums 1)
  )
)
```
-/

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
  rw [ Nat.sub_eq_iff_eq_add ] at hk <;> try linarith; ; have := congr_arg Even hk ; norm_num [ Nat.one_le_iff_ne_zero, parity_simps ] at this ; aesop;

/- Aristotle found this block to be false. Here is a proof of the negation:



/-
Core Fermat lemma: if p odd prime, p ∣ 2^a - 3 (a ≥ 2), and (p-1) ∣ N,
    then p ∤ 2^N - 3.
    Proof: 2^N ≡ 1 (mod p) by Fermat → 2^N - 3 ≡ -2 (mod p) → p ∤ -2 since p odd.
-/
lemma fermat_key (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
    (a : ℕ) (ha : 2 ≤ a) (hdvd : p ∣ 2 ^ a - 3)
    (N : ℕ) (hN : (p - 1) ∣ N) : ¬ p ∣ 2 ^ N - 3 := by
  -- Wait, there's a mistake. We can actually prove the opposite.
  negate_state;
  -- Proof starts here:
  -- Let's choose $p = 5$.
  use 5
  norm_num +zetaDelta at *;
  use 3
  norm_num +zetaDelta at *;
  use 0
  norm_num +zetaDelta at *;

-/
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
  by_contra! h_contra;
  -- Let's denote the product of all prime factors of $2^m - 3$ for $m \in S$ by $P$.
  set P := ∏ m ∈ S, (2 ^ m - 3) with hP_def
  have hP_pos : 0 < P := by
    exact Finset.prod_pos fun m hm => Nat.sub_pos_of_lt ( lt_of_lt_of_le ( by decide ) ( Nat.pow_le_pow_right ( by decide ) ( hS m hm ) ) );
  -- Let $N = \varphi(P) \cdot k + 2$ for some integer $k$ such that $N \geq 3$ and $N \notin S$.
  obtain ⟨k, hk⟩ : ∃ k : ℕ, 3 ≤ Nat.totient P * k + 2 ∧ Nat.totient P * k + 2 ∉ S := by
    obtain ⟨ k, hk ⟩ := Finset.bddAbove S;
    exact ⟨ k + 3, by nlinarith [ Nat.totient_pos.2 hP_pos ], fun h => by nlinarith [ hk h, Nat.totient_pos.2 hP_pos ] ⟩;
  -- Then $2^N - 3 \equiv 2^2 - 3 \equiv 1 \pmod{P}$.
  have h_cong : 2 ^ (Nat.totient P * k + 2) - 3 ≡ 1 [MOD P] := by
    -- By Euler's theorem, since $P$ is odd, we have $2^{\varphi(P)} \equiv 1 \pmod{P}$.
    have h_euler : 2 ^ Nat.totient P ≡ 1 [MOD P] := by
      refine' Nat.ModEq.pow_totient _;
      exact Nat.Coprime.prod_right fun m hm => Nat.prime_two.coprime_iff_not_dvd.mpr <| by rw [ ← even_iff_two_dvd ] ; rw [ Nat.even_sub <| show 3 ≤ 2 ^ m from le_trans ( by decide ) <| pow_le_pow_right₀ ( by decide ) <| hS m hm ] ; norm_num [ Nat.even_pow ] ; linarith [ hS m hm ] ;
    simp_all +decide [ ← ZMod.natCast_eq_natCast_iff, pow_add, pow_mul ];
    rw [ Nat.cast_sub ] <;> norm_num [ h_euler ];
    exact le_trans ( by norm_num ) ( Nat.mul_le_mul ( Nat.one_le_pow _ _ ( by positivity ) ) le_rfl );
  obtain ⟨ m, hm₁, hm₂ ⟩ := h_contra ( Nat.totient P * k + 2 ) hk.1 hk.2 ; have := h_cong.gcd_eq ; simp_all +decide [ Nat.coprime_prod_right_iff ] ;

/-- Build an injective sequence with all exponents ≥ 3 and pairwise-coprime values.
    Proof: iterate extension_exists starting from S = ∅. -/
lemma pairwise_coprime_seq :
    ∃ seq : ℕ → ℕ,
      Function.Injective seq ∧
      (∀ i, 3 ≤ seq i) ∧
      ∀ i j, i ≠ j → Nat.Coprime (2 ^ (seq i) - 3) (2 ^ (seq j) - 3) := by
  -- We construct the sequence by induction.
  have h_ind : ∀ n : ℕ, ∃ N ≥ 3, N > n ∧ Nat.Coprime (2 ^ N - 3) (∏ i ∈ Finset.Ico 3 (n+3), (2 ^ i - 3)) := by
    intro n
    obtain ⟨N, hN1, hN2, hN3⟩ := extension_exists (Finset.Ico 3 (n+3)) (by
    aesop);
    exact ⟨ N, hN1, not_le.mp fun h => hN2 <| Finset.mem_Ico.mpr ⟨ hN1, by linarith ⟩, Nat.Coprime.prod_right hN3 ⟩;
  -- Define the sequence recursively using the induction hypothesis.
  have h_seq : ∃ seq : ℕ → ℕ, (∀ n, 3 ≤ seq n) ∧ (∀ n, seq (n + 1) > seq n) ∧ (∀ n, Nat.Coprime (2 ^ seq (n + 1) - 3) (∏ i ∈ Finset.Ico 3 (seq n + 3), (2 ^ i - 3))) := by
    choose f hf using h_ind;
    use fun n => Nat.recOn n 3 fun n ih => f ih;
    exact ⟨ fun n => Nat.recOn n ( by norm_num ) fun n ih => by linarith [ hf ( Nat.rec 3 ( fun n ih => f ih ) n ) ], fun n => by linarith [ hf ( Nat.rec 3 ( fun n ih => f ih ) n ) ], fun n => hf _ |>.2.2 ⟩;
  cases' h_seq with seq hseq;
  refine' ⟨ seq, strictMono_nat_of_lt_succ hseq.2.1 |> StrictMono.injective, hseq.1, _ ⟩;
  intro i j hij; cases lt_or_gt_of_ne hij <;> simp_all +decide [ Nat.coprime_prod_right_iff ] ;
  · -- By induction on $j - i$, we can show that $2^{seq i} - 3$ and $2^{seq j} - 3$ are coprime.
    induction' ‹i < j› with j hj ih;
    · exact Nat.Coprime.symm ( hseq.2.2 i ( seq i ) ( hseq.1 i ) ( by linarith [ hseq.1 i ] ) );
    · exact Nat.Coprime.symm ( hseq.2.2 _ _ ( hseq.1 _ ) ( by linarith [ hseq.1 i, hseq.1 j, hseq.2.1 i, hseq.2.1 j, show seq i < seq j from by exact strictMono_nat_of_lt_succ hseq.2.1 ( Nat.lt_of_succ_le hj ) ] ) );
  · have := hseq.2.2 ( i - 1 ) ( seq j ) ( hseq.1 _ ) ?_ <;> rcases i <;> simp_all +decide;
    · exact this;
    · exact lt_of_le_of_lt ( show seq j ≤ seq _ from by exact monotone_nat_of_le_succ ( fun n => le_of_lt ( hseq.2.1 n ) ) ( by linarith ) ) ( Nat.lt_add_of_pos_right ( by norm_num ) )

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
  · intro m hm n hn hmn
    obtain ⟨i, hi⟩ := hm
    obtain ⟨j, hj⟩ := hn
    have h_distinct : i ≠ j := by
      grind +ring;
    -- Substitute m and n with seq' i and seq' j respectively, and apply hseq_cop.
    subst hi
    subst hj
    exact hseq_cop j i h_distinct.symm
