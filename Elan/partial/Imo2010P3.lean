import Mathlib

/-!
# International Mathematical Olympiad 2010, Problem 3

Determine all functions g : ℤ>0 → ℤ>0 such that

               (g(m) + n)(g(n) + m)

is always a perfect square.
-/

namespace Imo2010P3

abbrev PosInt : Type := { x : ℤ // 0 < x }

notation "ℤ>0" => PosInt

def SolutionSet : Set (ℤ>0 → ℤ>0) := { f | f = id ∨ ∃ c, ∀ x, f x = x + c }

/-
## Forward direction helpers
-/

private lemma forward_id (m n : ℤ>0) : IsSquare ((id m + n) * (id n + m)) := by
  use m + n; rw [id, id, add_comm m n]

private lemma forward_shift (c : ℤ>0) (m n : ℤ>0) :
    IsSquare (((m + c) + n) * ((n + c) + m)) := by
  use m + n + c; ext; simp; ring

/-
## Key finiteness lemma

For any nonzero d, there are only finitely many positive T with T*(T+d) a perfect square.
-/

lemma sq_prod_finite (d : ℤ) (hd : d ≠ 0) :
    Set.Finite { T : ℤ | 0 < T ∧ 0 < T + d ∧ IsSquare (T * (T + d)) } := by
  have h_factorization : ∀ T k : ℤ, T * (T + d) = k ^ 2 →
      (2 * T + d - 2 * k) * (2 * T + d + 2 * k) = d ^ 2 :=
    fun T k hk => by linarith
  have h_finite_factors : Set.Finite {p : ℤ × ℤ | p.1 * p.2 = d^2} := by
    have h_divisors_finite : Set.Finite {x : ℤ | x ∣ d^2} :=
      Set.Finite.subset (Set.finite_Icc (-(|d ^ 2| : ℤ)) (|d ^ 2| : ℤ))
        fun x hx => ⟨neg_le_of_abs_le <| Int.le_of_dvd (abs_pos.mpr <| pow_ne_zero 2 hd) <|
          by simpa using hx, le_of_abs_le <| Int.le_of_dvd (abs_pos.mpr <| pow_ne_zero 2 hd) <|
          by simpa using hx⟩
    exact Set.Finite.subset (h_divisors_finite.prod h_divisors_finite)
      fun p hp => ⟨dvd_of_mul_right_eq _ hp, dvd_of_mul_left_eq _ hp⟩
  have h_finite_T : Set.Finite
      {T : ℤ | ∃ p ∈ {p : ℤ × ℤ | p.1 * p.2 = d^2}, T = (p.1 + p.2 - 2 * d) / 4} :=
    Set.Finite.subset (h_finite_factors.image fun p => (p.1 + p.2 - 2 * d) / 4)
      fun x hx => by aesop
  refine h_finite_T.subset ?_
  intros T hT
  obtain ⟨k, hk⟩ := hT.right.right
  use (2 * T + d - 2 * k, 2 * T + d + 2 * k)
  exact ⟨h_factorization T k (by linarith),
    by rw [Int.ediv_eq_of_eq_mul_left] <;> linarith⟩

/-
## If h(n) = g(n) - n equals c for infinitely many n, then h ≡ c
-/

lemma h_const_of_inf_often
    (g : ℤ>0 → ℤ>0)
    (hsq : ∀ m n : ℤ>0, IsSquare ((g m + n) * (g n + m)))
    (c : ℤ)
    (hinf : Set.Infinite { n : ℤ>0 | (g n : ℤ) - (n : ℤ) = c }) :
    ∀ n : ℤ>0, (g n : ℤ) - (n : ℤ) = c := by
  intro m
  by_contra h
  set a := (g m : ℤ) - (m : ℤ) with ha_def
  have ha_ne_c : a ≠ c := h
  set D := c - a
  have hD_ne : D ≠ 0 := sub_ne_zero_of_ne (Ne.symm ha_ne_c)
  have h_sq_TD : ∀ n' : ℤ>0, (g n' : ℤ) - (n' : ℤ) = c →
      IsSquare (((m : ℤ) + (n' : ℤ) + a) * (((m : ℤ) + (n' : ℤ) + a) + D)) := by
    intro n' hn'
    obtain ⟨k, hk⟩ := hsq m n'
    refine ⟨(k : ℤ), ?_⟩
    have h3 : ((g m : ℤ) + (n' : ℤ)) * ((g n' : ℤ) + (m : ℤ)) = (k : ℤ) * (k : ℤ) :=
      congr_arg Subtype.val hk
    have eq2 : (g m : ℤ) + (n' : ℤ) + D = (g n' : ℤ) + (m : ℤ) := by omega
    rw [show (m : ℤ) + (n' : ℤ) + a = (g m : ℤ) + (n' : ℤ) from by omega]
    rw [show (g m : ℤ) + (n' : ℤ) + D = (g n' : ℤ) + (m : ℤ) from eq2]
    exact h3
  have h_fin := sq_prod_finite D hD_ne
  have h_inj : Set.InjOn (fun n' : ℤ>0 => (m : ℤ) + (n' : ℤ) + a)
      { n' : ℤ>0 | (g n' : ℤ) - (n' : ℤ) = c } := by
    intro n1 _ n2 _ heq; ext; push_cast at heq ⊢; omega
  have h_inf := hinf.image h_inj
  have h_sub : (fun n' : ℤ>0 => (m : ℤ) + (n' : ℤ) + a) ''
      { n' : ℤ>0 | (g n' : ℤ) - (n' : ℤ) = c } ⊆
      { T : ℤ | 0 < T ∧ 0 < T + D ∧ IsSquare (T * (T + D)) } := by
    rintro T ⟨n', hn', rfl⟩
    simp only [Set.mem_setOf_eq] at hn' ⊢
    have hm := m.2; have hn := n'.2; have hgm := (g m).2; have hgn := (g n').2
    refine ⟨by omega, by omega, h_sq_TD n' hn'⟩
  exact absurd (h_inf.mono h_sub) h_fin.not_infinite

/-
## Backward direction

The hard direction of IMO 2010 P3: if (g(m)+n)(g(n)+m) is always a perfect square,
then g = id or g(n) = n + c for some positive integer c.

The proof strategy is:
1. Define h(n) = g(n) - n and show the condition means (m+n+h(m))(m+n+h(n)) is always
   a perfect square.
2. Use sq_prod_finite to show that for any value c taken by h, any other value c' ≠ c
   can only be taken finitely many times (since the T values satisfying T(T+|c-c'|) = sq
   are finite).
3. Show some value of h is taken infinitely often (the hardest step, requiring careful
   analysis of the interaction between conditions from multiple reference points).
4. Apply h_const_of_inf_often to conclude h is constant.
5. Translate back to g being in the solution set.
-/

theorem backward (g : ℤ>0 → ℤ>0)
    (hsq : ∀ m n : ℤ>0, IsSquare ((g m + n) * (g n + m))) :
    g ∈ SolutionSet := by
  sorry

/-
## Main theorem
-/

theorem imo2010_p3 (g : ℤ>0 → ℤ>0) :
    g ∈ SolutionSet ↔ ∀ m n, IsSquare ((g m + n) * (g n + m)) := by
  constructor
  · rintro (rfl | ⟨c, hc⟩) m n
    · exact forward_id m n
    · rw [hc m, hc n]; exact forward_shift c m n
  · exact backward g

end Imo2010P3
