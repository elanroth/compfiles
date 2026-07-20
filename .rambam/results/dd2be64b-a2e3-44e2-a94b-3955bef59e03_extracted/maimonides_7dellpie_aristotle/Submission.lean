import Mathlib

namespace Imo1988P3

/-- Computable version of the function determined by the IMO 1988 P3 recurrences. -/
def imo_f : Nat → Nat
  | 0 => 0
  | 1 => 1
  | 2 => 1
  | 3 => 3
  | (n + 4) =>
    if (n + 4) % 2 = 0 then imo_f ((n + 4) / 2)
    else if (n + 4) % 4 = 1 then
      let k := (n + 3) / 4
      2 * imo_f (2 * k + 1) - imo_f k
    else
      let k := (n + 1) / 4
      3 * imo_f (2 * k + 1) - 2 * imo_f k

/-
PROBLEM
The recurrence imo_f(2k) = imo_f(k) for k ≥ 1

PROVIDED SOLUTION
Unfold imo_f. For k = 1: imo_f 2 = 1 = imo_f 1. For k ≥ 2: 2*k ≥ 4, so 2*k = (2*k - 4) + 4. The definition of imo_f at (n+4) checks if (n+4)%2 = 0. Since 2*k is even, it returns imo_f((2*k)/2) = imo_f(k). Handle k=1 as a special case (by native_decide or direct computation), then for k ≥ 2 use the (n+4) branch.
-/
lemma imo_f_rec_even (k : ℕ) (hk : k ≥ 1) : imo_f (2 * k) = imo_f k := by
  rcases k with ( _ | _ | _ | _ | k ) <;> simp +arith +decide at *;
  · native_decide +revert;
  · native_decide +revert;
  · native_decide +revert;
  · rw [ imo_f ] ; norm_num [ Nat.add_div ] ; ring;
    grind

/-
PROBLEM
The recurrence for 4k+1

PROVIDED SOLUTION
Unfold imo_f. For k ≥ 1, 4*k+1 ≥ 5, so 4*k+1 = (4*k-3) + 4. The definition at (n+4) first checks if (n+4)%2=0 (false since 4k+1 is odd), then checks if (n+4)%4=1 (true since (4k+1)%4=1). It computes let j := (n+3)/4 = ((4k-3)+3)/4 = (4k)/4 = k. So imo_f(4k+1) = 2*imo_f(2k+1) - imo_f(k). Handle k=1 by native_decide or direct computation, then k ≥ 2 by unfolding the definition at the (n+4) branch with n = 4k-3.
-/
lemma imo_f_rec_4k1 (k : ℕ) (hk : k ≥ 1) :
    imo_f (4 * k + 1) = 2 * imo_f (2 * k + 1) - imo_f k := by
      rw [ show 4 * k + 1 = ( 4 * k - 3 ) + 4 by linarith [ Nat.sub_add_cancel ( by linarith : 3 ≤ 4 * k ) ], imo_f ];
      rcases k with ( _ | _ | k ) <;> simp_all +arith +decide;
      grind

/-
PROBLEM
The recurrence for 4k+3

PROVIDED SOLUTION
Unfold imo_f. For k ≥ 1, 4*k+3 ≥ 7, so 4*k+3 = (4*k-1) + 4. The definition at (n+4) first checks if (n+4)%2=0 (false since 4k+3 is odd), then checks if (n+4)%4=1 (false since (4k+3)%4=3). So it goes to the else branch and computes let j := (n+1)/4 = ((4k-1)+1)/4 = (4k)/4 = k. So imo_f(4k+3) = 3*imo_f(2k+1) - 2*imo_f(k). Handle k=1 by native_decide or direct computation, then k ≥ 2 by unfolding.
-/
lemma imo_f_rec_4k3 (k : ℕ) (hk : k ≥ 1) :
    imo_f (4 * k + 3) = 3 * imo_f (2 * k + 1) - 2 * imo_f k := by
      rw [ show 4 * k + 3 = ( 4 * k - 1 ) + 4 by linarith [ Nat.sub_add_cancel ( by linarith : 1 ≤ 4 * k ) ], imo_f ];
      cases k <;> simp +arith +decide [ * ] at * ; omega;

/-- Key lemma: PNat addition equation gives Nat subtraction -/
lemma pnat_add_eq_to_nat_sub {a b c : ℕ+} (h : a + b = c) :
    (a : ℕ) = (c : ℕ) - (b : ℕ) := by
  have := congr_arg PNat.val h
  simp [PNat.add_coe] at this
  omega

/-- Key lemma: PNat addition equation gives Nat subtraction (variant) -/
lemma pnat_add_eq_to_nat_sub' {a b c : ℕ+} (h : a + b = c) :
    (a : ℕ) + (b : ℕ) = (c : ℕ) := by
  have := congr_arg PNat.val h
  simp [PNat.add_coe] at this
  exact this

/-
PROBLEM
Any f : ℕ+ → ℕ+ satisfying the conditions agrees with imo_f.
    Proved by strong induction on n.

PROVIDED SOLUTION
By strong induction on n : ℕ+ using PNat.strongInductionOn.

Given the induction hypothesis (IH): for all m : ℕ+ with m < n, (f m : ℕ) = imo_f (m : ℕ).

Case split on (n : ℕ):
- n = 1: (f 1 : ℕ) = 1 by h₀ (use congr_arg PNat.val h₀). imo_f 1 = 1 by definition. Done.
- n = 2: f 2 = f 1 by h₂ (with PNat 1). So (f 2 : ℕ) = (f 1 : ℕ) = 1 = imo_f 2.
- n = 3: (f 3 : ℕ) = 3 by h₁. imo_f 3 = 3. Done.
- n even, n ≥ 4: Write n = 2*m for some m : ℕ+ with m ≥ 2. Then f(2m) = f(m) by h₂. By IH (m < 2m = n): (f m : ℕ) = imo_f m. By imo_f_rec_even: imo_f(2m) = imo_f(m). So (f n : ℕ) = imo_f n.
- n ≡ 1 mod 4, n ≥ 5: Write n = 4*k + 1 for k : ℕ+ (k ≥ 1). From h₃: f(4k+1) + f(k) = 2*f(2k+1) in PNat. Cast to ℕ using pnat_add_eq_to_nat_sub' (or congr_arg PNat.val): (f(4k+1) : ℕ) + (f(k) : ℕ) = (2*f(2k+1) : ℕ) = 2*(f(2k+1) : ℕ). By IH on k < n and 2k+1 < n: (f k : ℕ) = imo_f k and (f(2k+1) : ℕ) = imo_f(2k+1). So (f(4k+1) : ℕ) = 2*imo_f(2k+1) - imo_f(k). By imo_f_rec_4k1: this equals imo_f(4k+1). Done.
- n ≡ 3 mod 4, n ≥ 7: Write n = 4*k+3 for k : ℕ+ (k ≥ 1). From h₄: f(4k+3) + 2*f(k) = 3*f(2k+1). Cast to ℕ: (f(4k+3) : ℕ) + 2*(f(k) : ℕ) = 3*(f(2k+1) : ℕ). By IH: substitute imo_f values. So (f(4k+3) : ℕ) = 3*imo_f(2k+1) - 2*imo_f(k) = imo_f(4k+3) by imo_f_rec_4k3. Done.

To construct m from n in the even case: use n.val / 2 with a proof it's positive.
To construct k from n in the mod 4 cases: use (n.val - 1) / 4 or (n.val - 3) / 4 with positivity proofs.

Key helper lemmas to use: imo_f_rec_even, imo_f_rec_4k1, imo_f_rec_4k3, pnat_add_eq_to_nat_sub'.
-/
lemma f_eq_imo_f
    (f : ℕ+ → ℕ+)
    (h₀ : f 1 = 1)
    (h₁ : f 3 = 3)
    (h₂ : ∀ n, f (2 * n) = f n)
    (h₃ : ∀ n, f (4 * n + 1) + f n = 2 * f (2 * n + 1))
    (h₄ : ∀ n, f (4 * n + 3) + 2 * f n = 3 * f (2 * n + 1))
    (n : ℕ+) : (f n : ℕ) = imo_f (n : ℕ) := by
      induction' n using PNat.strongInductionOn with n ih;
      rcases Nat.even_or_odd' n.val with ⟨ k, hk | hk ⟩;
      · -- Since $n$ is even, we can write $n = 2k$ for some $k$.
        obtain ⟨k, rfl⟩ : ∃ k : ℕ+, n = 2 * k := by
          exact PNat.dvd_iff.mpr ⟨ k, hk ⟩;
        -- By definition of imo_f, we know that imo_f(2k) = imo_f(k).
        have h_imof_even : imo_f (2 * k) = imo_f k := by
          exact imo_f_rec_even _ k.pos;
        aesop;
      · rcases Nat.even_or_odd' k with ⟨ k, rfl | rfl ⟩ <;> simp_all +decide [ Nat.mul_succ ];
        · rw [ show n = ⟨ 2 * ( 2 * k ) + 1, Nat.succ_pos _ ⟩ from PNat.eq hk ];
          rcases k with ( _ | k ) <;> simp +arith +decide [ * ];
          · native_decide +revert;
          · -- By the induction hypothesis, we know that $f(k+1) = imo_f(k+1)$ and $f(2k+3) = imo_f(2k+3)$.
            have h_ind_k1 : (f (⟨k + 1, by linarith⟩) : ℕ) = imo_f (k + 1) := by
              exact ih _ <| show ( k + 1 : ℕ ) < n from by linarith;
            have h_ind_2k3 : (f (⟨2 * k + 3, by linarith⟩) : ℕ) = imo_f (2 * k + 3) := by
              exact ih ⟨ 2 * k + 3, Nat.succ_pos _ ⟩ ( show ( 2 * k + 3 : ℕ ) < n from by linarith );
            -- By the recurrence relation for $f$, we have $f(4k+5) + f(k+1) = 2f(2k+3)$.
            have h_rec : (f (⟨4 * k + 5, by linarith⟩) : ℕ) + (f (⟨k + 1, by linarith⟩) : ℕ) = 2 * (f (⟨2 * k + 3, by linarith⟩) : ℕ) := by
              exact congr_arg PNat.val ( h₃ ⟨ k + 1, Nat.succ_pos _ ⟩ );
            rw [ show imo_f ( 4 * k + 5 ) = 2 * imo_f ( 2 * k + 3 ) - imo_f ( k + 1 ) from ?_ ];
            · exact eq_tsub_of_add_eq ( by linarith );
            · convert imo_f_rec_4k1 ( k + 1 ) ( Nat.succ_pos _ ) using 1;
        · rcases k with ( _ | k );
          · simp +decide [ show n = 3 from PNat.eq hk, * ];
            native_decide +revert;
          · rw [ show n = ⟨ 2 * ( 2 * ( k + 1 ) ) + 2 + 1, Nat.succ_pos _ ⟩ from PNat.eq hk ];
            -- Using the recurrence relation for $f(4k+3)$, we have $f(4k+3) = 3f(2k+1) - 2f(k)$.
            have h_rec : (f (⟨4 * (k + 1) + 3, by linarith⟩) : ℕ) = 3 * (f (⟨2 * (k + 1) + 1, by linarith⟩) : ℕ) - 2 * (f (⟨k + 1, by linarith⟩) : ℕ) := by
              exact eq_tsub_of_add_eq <| by have := h₄ ⟨ k + 1, Nat.succ_pos _ ⟩ ; exact mod_cast this ▸ rfl;
            convert h_rec using 1;
            · congr 2 ; ring;
            · erw [ ih ⟨ 2 * ( k + 1 ) + 1, by linarith ⟩ ( by { exact_mod_cast ( by linarith : ( 2 * ( k + 1 ) + 1 : ℕ ) < n ) } ), ih ⟨ k + 1, by linarith ⟩ ( by { exact_mod_cast ( by linarith : ( k + 1 : ℕ ) < n ) } ) ];
              convert imo_f_rec_4k3 ( k + 1 ) ( Nat.succ_pos _ ) using 1 ; ring

/-- Counting fixed points computationally -/
lemma count_fixed_points :
    ((Finset.Icc 1 1988).filter (fun n => imo_f n = n)).card = 92 := by
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
  have h₅ : f 2 = 1 := by exact h₂ 1 ▸ h₀
  have h₆ : f 4 = 1 := by exact h₂ 2 ▸ h₅
  have h₇ : f 5 = 5 := by
    specialize h₃ 1; erw [h₀, h₁] at h₃; exact add_right_cancel h₃
  have h₈ : f 6 = 3 := by exact h₂ 3 ▸ h₁
  have h₉ : f 7 = 7 := by
    specialize h₄ 1; simp_all +decide
    erw [h₁] at h₄; exact add_right_cancel h₄
  have h₁₀ : f 8 = 1 := by exact h₂ 4 ▸ h₆
  simp_all +decide [add_comm]

lemma ncard_eq_finset_card
    (f : ℕ+ → ℕ+)
    (h₀ : f 1 = 1)
    (h₁ : f 3 = 3)
    (h₂ : ∀ n, f (2 * n) = f n)
    (h₃ : ∀ n, f (4 * n + 1) + f n = 2 * f (2 * n + 1))
    (h₄ : ∀ n, f (4 * n + 3) + 2 * f n = 3 * f (2 * n + 1)) :
    Set.ncard {n : ℕ+ | n ≤ 1988 ∧ f n = n} =
    ((Finset.Icc 1 1988).filter (fun m => imo_f m = m)).card := by
  have h_set_eq : {n : ℕ+ | n ≤ 1988 ∧ f n = n} =
      {n : ℕ+ | n ≤ 1988 ∧ imo_f (n : ℕ) = (n : ℕ)} := by
    apply Set.ext
    intro n
    simp
    intro hn; erw [← PNat.coe_inj]; erw [f_eq_imo_f f h₀ h₁ h₂ h₃ h₄]
  rw [← Set.ncard_coe_finset]; norm_num [h_set_eq]
  fapply Set.ncard_congr
  use fun a ha => a
  · exact fun n hn => ⟨⟨PNat.pos n, hn.1⟩, hn.2⟩
  · aesop
  · exact fun b hb => ⟨⟨b, hb.1.1⟩, ⟨hb.1.2, hb.2⟩, rfl⟩

theorem imo1988_p3
    (f : ℕ+ → ℕ+)
    (h₀ : f 1 = 1)
    (h₁ : f 3 = 3)
    (h₂ : ∀ n, f (2 * n) = f n)
    (h₃ : ∀ n, f (4 * n + 1) + f n = 2 * f (2 * n + 1))
    (h₄ : ∀ n, f (4 * n + 3) + 2 * f n = 3 * f (2 * n + 1)) :
    Set.ncard {n | n ≤ 1988 ∧ f n = n} = 92 := by
  rw [ncard_eq_finset_card f h₀ h₁ h₂ h₃ h₄, count_fixed_points]

end Imo1988P3