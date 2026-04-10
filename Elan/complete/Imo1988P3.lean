import Mathlib

namespace Imo1988P3

/-- The unique function determined by the IMO 1988 P3 recurrences, computed on ℤ -/
def fRec : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | 2 => 1
  | 3 => 3
  | n + 4 =>
    if (n + 4) % 2 = 0 then fRec ((n + 4) / 2)
    else if (n + 4) % 4 = 1 then 2 * fRec ((n + 4 + 1) / 2) - fRec ((n + 4 - 1) / 4)
    else 3 * fRec ((n + 4 - 1) / 2) - 2 * fRec ((n + 4 - 3) / 4)

@[simp] lemma fRec_zero : fRec 0 = 0 := by native_decide
@[simp] lemma fRec_one : fRec 1 = 1 := by native_decide
@[simp] lemma fRec_two : fRec 2 = 1 := by native_decide
@[simp] lemma fRec_three : fRec 3 = 3 := by native_decide

/-- fRec at even arguments ≥ 4 reduces to half -/
lemma fRec_even (k : ℕ) (hk : k ≥ 2) : fRec (2 * k) = fRec k := by
  have h : 2 * k = (2 * k - 4) + 4 := by omega
  conv_lhs => rw [h, fRec]
  rw [if_pos (by omega : (2 * k - 4 + 4) % 2 = 0)]
  congr 1; omega

/-- fRec at 4k+1 (k ≥ 1) satisfies the recurrence -/
lemma fRec_mod1 (k : ℕ) (hk : k ≥ 1) :
    fRec (4 * k + 1) = 2 * fRec (2 * k + 1) - fRec k := by
  have h : 4 * k + 1 = (4 * k - 3) + 4 := by omega
  conv_lhs => rw [h, fRec]
  rw [if_neg (by omega : ¬((4 * k - 3 + 4) % 2 = 0)),
      if_pos (by omega : (4 * k - 3 + 4) % 4 = 1)]
  have h1 : (4 * k - 3 + 4 + 1) / 2 = 2 * k + 1 := by omega
  have h2 : (4 * k - 3 + 4 - 1) / 4 = k := by omega
  rw [h1, h2]

/-- fRec at 4k+3 (k ≥ 1) satisfies the recurrence -/
lemma fRec_mod3 (k : ℕ) (hk : k ≥ 1) :
    fRec (4 * k + 3) = 3 * fRec (2 * k + 1) - 2 * fRec k := by
  have h : 4 * k + 3 = (4 * k - 1) + 4 := by omega
  conv_lhs => rw [h, fRec]
  rw [if_neg (by omega : ¬((4 * k - 1 + 4) % 2 = 0)),
      if_neg (by omega : ¬((4 * k - 1 + 4) % 4 = 1))]
  have h1 : (4 * k - 1 + 4 - 1) / 2 = 2 * k + 1 := by omega
  have h2 : (4 * k - 1 + 4 - 3) / 4 = k := by omega
  rw [h1, h2]

/-
PROBLEM
Even case of uniqueness: if f agrees with fRec at k, it agrees at 2k

PROVIDED SOLUTION
By h₂, f(2*k) = f(k). So (f(2*k) : ℤ) = (f(k) : ℤ) = fRec(k:ℕ) by ihk.
For fRec(2*(k:ℕ)): if k.val ≥ 2, use fRec_even. If k.val = 1, fRec(2) = 1 = fRec(1).
Key: `have : f (2 * k) = f k := h₂ k` then cast, then rewrite with ihk, then handle fRec(2*k.val) = fRec(k.val).
-/
lemma f_eq_fRec_even_case
    (f : ℕ+ → ℕ+)
    (h₂ : ∀ n, f (2 * n) = f n)
    (k : ℕ+)
    (ihk : (f k : ℤ) = fRec (k : ℕ)) :
    (f (2 * k) : ℤ) = fRec (2 * (k : ℕ)) := by
  by_cases hk : k.val ≥ 2;
  · rw [ h₂, fRec_even _ hk, ihk ];
  · interval_cases k : ( k : ℕ ) <;> simp_all +decide;
    exact h₂ 1 ▸ ihk

/-
PROBLEM
Mod 1 case of uniqueness

PROVIDED SOLUTION
From h₃ k: f(4*k+1) + f(k) = 2 * f(2*k+1). Cast to ℤ with `exact_mod_cast h₃ k` or `exact mod_cast h₃ k`. Then use ihk and ih2k1 to replace f terms with fRec terms, and use fRec_mod1 for the fRec side. Finally linarith.
-/
lemma f_eq_fRec_mod1_case
    (f : ℕ+ → ℕ+)
    (h₃ : ∀ n, f (4 * n + 1) + f n = 2 * f (2 * n + 1))
    (k : ℕ+)
    (ihk : (f k : ℤ) = fRec (k : ℕ))
    (ih2k1 : (f (2 * k + 1) : ℤ) = fRec (2 * (k : ℕ) + 1)) :
    (f (4 * k + 1) : ℤ) = fRec (4 * (k : ℕ) + 1) := by
  rw [ fRec_mod1 ] <;> norm_num at *;
  · have h_cast : (f (4 * k + 1) : ℤ) + (f k : ℤ) = 2 * (f (2 * k + 1) : ℤ) := by
      exact mod_cast h₃ k ▸ rfl;
    exact eq_tsub_of_add_eq <| by linarith;
  · exact PNat.one_le _

/-
PROBLEM
Mod 3 case of uniqueness

PROVIDED SOLUTION
Same as mod1 case but using h₄ and fRec_mod3. Cast h₄ k to ℤ, substitute ihk and ih2k1, use fRec_mod3, and linarith.
-/
lemma f_eq_fRec_mod3_case
    (f : ℕ+ → ℕ+)
    (h₄ : ∀ n, f (4 * n + 3) + 2 * f n = 3 * f (2 * n + 1))
    (k : ℕ+)
    (ihk : (f k : ℤ) = fRec (k : ℕ))
    (ih2k1 : (f (2 * k + 1) : ℤ) = fRec (2 * (k : ℕ) + 1)) :
    (f (4 * k + 3) : ℤ) = fRec (4 * (k : ℕ) + 3) := by
  -- From h₄ k, we have f(4*k+3) + 2 * f(k) = 3 * f(2*k+1). Cast to ℤ with `exact_mod_cast h₄ k` or `exact mod_cast h₄ k`.
  have h_cast : (f (4 * k + 3) : ℤ) + 2 * (f k : ℤ) = 3 * (f (2 * k + 1) : ℤ) := by
    exact_mod_cast h₄ k;
  rw [ fRec_mod3 ];
  · grind;
  · exact PNat.pos k

/-
PROBLEM
Every n : ℕ+ with n ≥ 4 can be written as 2k, 4k+1, or 4k+3 for some k : ℕ+

PROVIDED SOLUTION
Every natural number n ≥ 4 is either even, or odd. If even, n = 2k with k ≥ 2 (so k : ℕ+). If odd, n mod 4 is either 1 or 3. If n mod 4 = 1, n = 4j+1 with j ≥ 1. If n mod 4 = 3, n = 4j+3 with j ≥ 1. Use omega for arithmetic and PNat.eq for conversion.
-/
lemma pnat_cases (n : ℕ+) (hn : 4 ≤ (n : ℕ)) :
    (∃ k : ℕ+, n = 2 * k) ∨
    (∃ k : ℕ+, n = 4 * k + 1) ∨
    (∃ k : ℕ+, n = 4 * k + 3) := by
  rcases Nat.even_or_odd' n with ⟨ k, hk | hk ⟩;
  · exact Or.inl ⟨ ⟨ k, by linarith ⟩, PNat.eq hk ⟩;
  · rcases Nat.even_or_odd' k with ⟨ k, rfl | rfl ⟩ <;> simp_all +decide [ ← PNat.coe_inj ];
    · exact Or.inr <| Or.inl ⟨ ⟨ k, by linarith ⟩, by simp +arith +decide ⟩;
    · exact Or.inr <| Or.inr <| ⟨ ⟨ k, Nat.pos_of_ne_zero <| by rintro rfl; contradiction ⟩, by simp +arith +decide [ mul_add ] ⟩

/-- Any function satisfying the IMO 1988 P3 conditions agrees with fRec -/
lemma f_eq_fRec
    (f : ℕ+ → ℕ+)
    (h₀ : f 1 = 1)
    (h₁ : f 3 = 3)
    (h₂ : ∀ n, f (2 * n) = f n)
    (h₃ : ∀ n, f (4 * n + 1) + f n = 2 * f (2 * n + 1))
    (h₄ : ∀ n, f (4 * n + 3) + 2 * f n = 3 * f (2 * n + 1))
    (n : ℕ+) : (f n : ℤ) = fRec n := by
  induction n using PNat.strongInductionOn with
  | _ n ih =>
    by_cases hn : (n : ℕ) ≤ 3
    · -- Base cases: n = 1, 2, 3
      have h1 := n.pos
      have hcases : n = 1 ∨ n = 2 ∨ n = 3 := by
        have : (n : ℕ) = 1 ∨ (n : ℕ) = 2 ∨ (n : ℕ) = 3 := by omega
        rcases this with h | h | h
        · exact Or.inl (PNat.eq h)
        · exact Or.inr (Or.inl (PNat.eq h))
        · exact Or.inr (Or.inr (PNat.eq h))
      rcases hcases with rfl | rfl | rfl
      · simp [h₀]
      · have hf2 : f 2 = f 1 := by simpa using h₂ 1
        simp [hf2, h₀]
      · simp [h₁]
    · push_neg at hn
      rcases pnat_cases n (by omega) with ⟨k, rfl⟩ | ⟨k, rfl⟩ | ⟨k, rfl⟩
      · -- n = 2k
        have hk_lt : k < 2 * k := by
          exact_mod_cast show (k : ℕ) < 2 * (k : ℕ) from by linarith [k.pos]
        exact f_eq_fRec_even_case f h₂ k (ih k hk_lt)
      · -- n = 4k+1
        have hk_lt : k < 4 * k + 1 := by
          exact_mod_cast show (k : ℕ) < 4 * (k : ℕ) + 1 from by linarith [k.pos]
        have h2k1_lt : 2 * k + 1 < 4 * k + 1 := by
          show (2 * k + 1 : ℕ+).val < (4 * k + 1 : ℕ+).val
          simp only [PNat.mul_coe, PNat.add_coe, PNat.val_ofNat]; linarith [k.pos]
        exact f_eq_fRec_mod1_case f h₃ k (ih k hk_lt) (ih (2 * k + 1) h2k1_lt)
      · -- n = 4k+3
        have hk_lt : k < 4 * k + 3 := by
          exact_mod_cast show (k : ℕ) < 4 * (k : ℕ) + 3 from by linarith [k.pos]
        have h2k1_lt : 2 * k + 1 < 4 * k + 3 := by
          show (2 * k + 1 : ℕ+).val < (4 * k + 3 : ℕ+).val
          simp only [PNat.mul_coe, PNat.add_coe, PNat.val_ofNat]; linarith [k.pos]
        exact f_eq_fRec_mod3_case f h₄ k (ih k hk_lt) (ih (2 * k + 1) h2k1_lt)

theorem imo1988_p3
    (f : ℕ+ → ℕ+)
    (h₀ : f 1 = 1)
    (h₁ : f 3 = 3)
    (h₂ : ∀ n, f (2 * n) = f n)
    (h₃ : ∀ n, f (4 * n + 1) + f n = 2 * f (2 * n + 1))
    (h₄ : ∀ n, f (4 * n + 3) + 2 * f n = 3 * f (2 * n + 1)) :
    Set.ncard {n | n ≤ 1988 ∧ f n = n} = 92 := by
  have hfeq := f_eq_fRec f h₀ h₁ h₂ h₃ h₄
  have fixed_iff : ∀ n : ℕ+, f n = n ↔ fRec (n : ℕ) = (n : ℤ) := by
    intro n; constructor
    · intro h; have := hfeq n; rw [h] at this; exact this.symm
    · intro h; have h1 := hfeq n
      have h2 : (f n : ℤ) = (n : ℤ) := by rw [h1, h]
      exact_mod_cast h2
  have hfin : {n : ℕ+ | n ≤ 1988 ∧ f n = n}.Finite := by
    apply Set.Finite.subset (Finset.Icc 1 1988).finite_toSet
    intro n ⟨hn, _⟩; simp [n.one_le, hn]
  rw [Set.ncard_eq_toFinset_card _ hfin]
  convert_to ((Finset.Icc (1 : ℕ+) 1988).filter
    (fun n : ℕ+ => decide (fRec (n : ℕ) = (n : ℤ)))).card = 92
  · congr 1; ext n
    simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq, Finset.mem_filter,
               Finset.mem_Icc, decide_eq_true_eq]
    exact ⟨fun ⟨hn, hfn⟩ => ⟨⟨n.one_le, hn⟩, (fixed_iff n).mp hfn⟩,
           fun ⟨⟨_, hn⟩, hd⟩ => ⟨hn, (fixed_iff n).mpr hd⟩⟩
  · native_decide

end Imo1988P3