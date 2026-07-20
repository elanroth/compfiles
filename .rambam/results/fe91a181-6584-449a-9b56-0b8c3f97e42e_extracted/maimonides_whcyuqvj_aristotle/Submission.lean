import Mathlib

namespace Imo1988P3

/-- The unique function satisfying the recurrences of IMO 1988 P3.
    This is the binary-digit-reversal function. -/
def g (n : Nat) : Nat :=
  if n = 0 then 0
  else if n = 1 then 1
  else if n = 3 then 3
  else if n % 2 = 0 then g (n / 2)
  else if n % 4 = 1 then 2 * g ((n + 1) / 2) - g ((n - 1) / 4)
  else 3 * g ((n - 1) / 2) - 2 * g ((n - 3) / 4)
termination_by n
decreasing_by all_goals omega

-- Unfolding lemmas for g
lemma g_zero : g 0 = 0 := by rw [g]
lemma g_one : g 1 = 1 := by rw [g]; simp
lemma g_three : g 3 = 3 := by rw [g]; simp

lemma g_even (n : Nat) (hn : n ≥ 2) (he : n % 2 = 0) : g n = g (n / 2) := by
  rw [g]
  simp [show n ≠ 0 by omega, show n ≠ 1 by omega]
  intro h3
  subst h3
  omega

lemma g_mod4_1 (n : Nat) (hn : n ≥ 5) (hm : n % 4 = 1) :
    g n = 2 * g ((n + 1) / 2) - g ((n - 1) / 4) := by
  rw [g]
  simp [show n ≠ 0 by omega, show n ≠ 1 by omega, show n ≠ 3 by omega,
        show n % 2 ≠ 0 by omega, hm]
  split <;> omega

lemma g_mod4_3 (n : Nat) (hn : n ≥ 7) (hm : n % 4 = 3) :
    g n = 3 * g ((n - 1) / 2) - 2 * g ((n - 3) / 4) := by
  rw [g]
  simp [show n ≠ 0 by omega, show n ≠ 1 by omega, show n ≠ 3 by omega,
        show n % 2 ≠ 0 by omega, show ¬(n % 4 = 1) by omega]

/-
PROBLEM
Any function satisfying the IMO 1988 P3 recurrences agrees with g.

PROVIDED SOLUTION
By strong induction on (n : ℕ) = n.val using Nat.strongRecOn (or WellFoundedRelation on ℕ+).

Base cases:
- n = 1: (f 1 : ℕ) = 1 = g 1 by h₀.
- n = 2: (f 2 : ℕ) = (f 1 : ℕ) = 1 = g 2 by h₂ (with PNat 1).
- n = 3: (f 3 : ℕ) = 3 = g 3 by h₁.

Inductive step for n ≥ 4:
Case 1: n is even, n = 2m for some m : ℕ+ with m < n. Then:
  (f n : ℕ) = (f m : ℕ) [by h₂, since f(2m) = f(m)]
  = g m [by IH]
  = g n [by g_even]

Case 2: n ≡ 1 mod 4, n ≥ 5. Then n = 4k + 1 for some k ≥ 1.
  In ℕ+, k is a positive nat with k = ⟨(n-1)/4, ...⟩.
  From h₃ applied to k: f(4k+1) + f(k) = 2 * f(2k+1) in ℕ+.
  Casting to ℕ: (f(4k+1) : ℕ) + (f(k) : ℕ) = 2 * (f(2k+1) : ℕ).
  By IH (k < n and 2k+1 < n): (f(k):ℕ) = g(k) and (f(2k+1):ℕ) = g(2k+1).
  So (f(4k+1):ℕ) = 2*g(2k+1) - g(k).
  By g_mod4_1: g(4k+1) = 2*g(2k+1) - g(k).
  Hence (f n : ℕ) = g n.

Case 3: n ≡ 3 mod 4, n ≥ 7. Then n = 4k + 3 for some k ≥ 1.
  From h₄: f(4k+3) + 2*f(k) = 3*f(2k+1) in ℕ+.
  By IH: (f(k):ℕ) = g(k) and (f(2k+1):ℕ) = g(2k+1).
  So (f(4k+3):ℕ) = 3*g(2k+1) - 2*g(k) = g(4k+3).

Key: use PNat.strongRecOn or similar. Cast ℕ+ equations to ℕ using PNat.val. The key casting facts are:
- PNat.val is injective
- (a + b : ℕ+).val = a.val + b.val
- (a * b : ℕ+).val = a.val * b.val
- (2 : ℕ+).val = 2, (4 : ℕ+).val = 4, etc.

The tricky part is constructing the PNat k from n. If n.val ≡ 1 mod 4 and n.val ≥ 5, then k = ⟨(n.val - 1) / 4, by omega⟩ works, and 4 * k + 1 = n as ℕ+.
-/
lemma f_eq_g
    (f : ℕ+ → ℕ+)
    (h₀ : f 1 = 1)
    (h₁ : f 3 = 3)
    (h₂ : ∀ n, f (2 * n) = f n)
    (h₃ : ∀ n, f (4 * n + 1) + f n = 2 * f (2 * n + 1))
    (h₄ : ∀ n, f (4 * n + 3) + 2 * f n = 3 * f (2 * n + 1))
    (n : ℕ+) : (f n : ℕ) = g n := by
  induction' n using PNat.strongInductionOn with n ih;
  by_cases hn : n.val ≤ 3;
  · rcases n with ( _ | _ | _ | _ | n ) <;> norm_cast ; simp_all +decide [ g ];
    · erw [ h₂ 1, h₀ ] ; simp +decide [ g ];
    · exact h₁.symm ▸ g_three.symm ▸ rfl;
  · -- Consider two cases: $n$ is even or $n$ is odd.
    by_cases h_even : n.val % 2 = 0;
    · -- Since $n$ is even, we can write $n = 2m$ for some $m$.
      obtain ⟨m, hm⟩ : ∃ m : ℕ+, n = 2 * m := by
        exact PNat.dvd_iff.mpr ( Nat.dvd_of_mod_eq_zero h_even );
      simp_all +decide [ Nat.add_mod, Nat.mul_mod ];
      rw [ show g ( 2 * m ) = g m from _ ];
      rw [ g_even ] <;> norm_num ; linarith [ PNat.pos m ];
    · -- Since $n$ is odd, we can write $n = 4k + 1$ or $n = 4k + 3$ for some $k \geq 1$.
      obtain ⟨k, rfl | rfl⟩ : ∃ k : ℕ+, n = 4 * k + 1 ∨ n = 4 * k + 3 := by
        -- Since $n$ is odd, we can write $n = 4k + 1$ or $n = 4k + 3$ for some $k$.
        obtain ⟨k, hk⟩ : ∃ k : ℕ, n.val = 4 * k + 1 ∨ n.val = 4 * k + 3 := by
          exact ⟨ n / 4, by omega ⟩;
        exact ⟨ ⟨ k, Nat.pos_of_ne_zero ( by aesop_cat ) ⟩, Or.imp ( fun h => PNat.eq h ) ( fun h => PNat.eq h ) hk ⟩;
      · -- By Lemma 2, we know that $f(4k+1) + f(k) = 2f(2k+1)$.
        have h_rec : (f (4 * k + 1) : ℕ) + (f k : ℕ) = 2 * (f (2 * k + 1) : ℕ) := by
          exact congr_arg PNat.val ( h₃ k );
        -- By Lemma 2, we know that $g(4k+1) = 2g(2k+1) - g(k)$.
        have h_g_rec : g (4 * k + 1) = 2 * g (2 * k + 1) - g k := by
          convert g_mod4_1 ( 4 * k + 1 ) _ _ using 1 <;> norm_num [ Nat.add_mod, Nat.mul_mod ];
          · norm_num [ show ( 4 * k + 1 + 1 : ℕ ) = 2 * ( 2 * k + 1 ) by ring ];
          · linarith [ PNat.pos k ];
        simp_all +decide [ Nat.add_mod, Nat.mul_mod ];
        rw [ ← h_rec, Nat.add_sub_cancel ];
      · -- By the induction hypothesis, we have $f(k) = g(k)$ and $f(2k+1) = g(2k+1)$.
        have h_ind_k : f k = g k := by
          exact ih k <| by show ( k : ℕ ) < 4 * k + 3; linarith;
        have h_ind_2k1 : f (2 * k + 1) = g (2 * k + 1) := by
          exact ih _ <| by show ( 2 * k + 1 : ℕ ) < 4 * k + 3; linarith only [ k.pos ] ;
        -- By the induction hypothesis, we have $g(4k+3) = 3g(2k+1) - 2g(k)$.
        have h_g_4k3 : g (4 * k + 3) = 3 * g (2 * k + 1) - 2 * g k := by
          convert g_mod4_3 ( 4 * k + 3 ) _ _ using 1 <;> norm_num [ Nat.add_mod, Nat.mul_mod ];
          · norm_num [ show 4 * ( k : ℕ ) = 2 * ( 2 * ( k : ℕ ) ) by ring ];
          · linarith [ PNat.pos k ];
        have := h₄ k; replace := congr_arg PNat.val this; norm_num [ h_ind_k, h_ind_2k1, h_g_4k3 ] at this ⊢;
        exact eq_tsub_of_add_eq this

/-- The counting result via native computation. -/
lemma count_g_fixed :
    ((Finset.Icc (1 : ℕ+) 1988).filter (fun n : ℕ+ => g (n : ℕ) == (n : ℕ))).card = 92 := by
  native_decide

lemma f_small_values
    (f : ℕ+ → ℕ+)
    (h₀ : f 1 = 1)
    (h₁ : f 3 = 3)
    (h₂ : ∀ n, f (2 * n) = f n)
    (h₃ : ∀ n, f (4 * n + 1) + f n = 2 * f (2 * n + 1))
    (h₄ : ∀ n, f (4 * n + 3) + 2 * f n = 3 * f (2 * n + 1)) :
    f 1 = 1 ∧ f 2 = 1 ∧ f 3 = 3 ∧ f 4 = 1 ∧
    f 5 = 5 ∧ f 6 = 3 ∧ f 7 = 7 ∧ f 8 = 1 := by
  have f_two : f 2 = 1 := by simpa using h₂ 1
  have f_four : f 4 = 1 := by rw [h₂ 2, f_two]
  have f_five : f 5 = 5 := by
    have h := h₃ 1; rw [h₀, h₁] at h; norm_num at h ⊢; omega
  have f_six : f 6 = 3 := by simpa using h₂ 3
  have f_seven : f 7 = 7 := by
    have h := h₄ 1; rw [h₀, h₁] at h; norm_num at h ⊢; omega
  have f_eight : f 8 = 1 := by rw [h₂ 4, f_four]
  exact ⟨h₀, f_two, h₁, f_four, f_five, f_six, f_seven, f_eight⟩

/-
PROVIDED SOLUTION
Using key : ∀ n : ℕ+, (f n : ℕ) = g n, convert the set to use g instead of f.

Step 1: Show the set equals the coercion of a Finset.
The set {n : ℕ+ | n ≤ 1988 ∧ f n = n} = {n : ℕ+ | n ≤ 1988 ∧ g n = n} because f n = n ↔ (f n : ℕ) = (n : ℕ) ↔ g n = n (using key and PNat.eq_iff/PNat.val_eq_one etc.).

Step 2: Convert Set.ncard to Finset.card. The set {n : ℕ+ | n ≤ 1988 ∧ g n = n} is finite (bounded by 1988). We can write it as the coe of (Finset.Icc 1 1988).filter (fun n => g n == n). Then Set.ncard of the coe of a Finset equals Finset.card.

Step 3: Apply count_g_fixed (which uses native_decide).

Key conversion approach: use `Set.ncard_coe_Finset` to convert Set.ncard of a Finset coercion to Finset.card. Or use `Set.Finite.ncard_eq_toFinset_card'` and then show the toFinset equals the desired Finset.
-/
theorem imo1988_p3
    (f : ℕ+ → ℕ+)
    (h₀ : f 1 = 1)
    (h₁ : f 3 = 3)
    (h₂ : ∀ n, f (2 * n) = f n)
    (h₃ : ∀ n, f (4 * n + 1) + f n = 2 * f (2 * n + 1))
    (h₄ : ∀ n, f (4 * n + 3) + 2 * f n = 3 * f (2 * n + 1)) :
    Set.ncard {n | n ≤ 1988 ∧ f n = n} = 92 := by
  have key := f_eq_g f h₀ h₁ h₂ h₃ h₄
  rw [ show { n | n ≤ 1988 ∧ f n = n } = Finset.filter ( fun n : ℕ+ => g n = n ) ( Finset.Iic 1988 ) from ?_ ];
  · rw [ Set.ncard_coe_finset ] ; native_decide;
  · simp +decide [ ← key, Set.ext_iff ]

end Imo1988P3