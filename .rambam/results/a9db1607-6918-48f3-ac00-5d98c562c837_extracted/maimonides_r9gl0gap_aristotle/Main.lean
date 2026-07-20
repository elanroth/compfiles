import Mathlib

namespace Imo1970P6

open scoped EuclideanGeometry

abbrev Pt := EuclideanSpace ℝ (Fin 2)

def AcuteTriangle (T : Affine.Triangle ℝ Pt) : Prop :=
  ∠ (T.points 1) (T.points 2) (T.points 3) < Real.pi / 2 ∧
  ∠ (T.points 2) (T.points 3) (T.points 1) < Real.pi / 2 ∧
  ∠ (T.points 3) (T.points 1) (T.points 2) < Real.pi / 2

lemma four_point_algebraic (c₁ c₂ d₁ d₂ : ℝ)
    (h1 : c₁ > 0) (h2 : 1 - c₁ > 0)
    (h3 : c₁ * c₁ + c₂ * c₂ - c₁ > 0)
    (h4 : d₁ > 0) (h5 : 1 - d₁ > 0)
    (h6 : d₁ * d₁ + d₂ * d₂ - d₁ > 0)
    (h7 : c₁ * d₁ + c₂ * d₂ > 0)
    (h8 : c₁ * c₁ + c₂ * c₂ - c₁ * d₁ - c₂ * d₂ > 0)
    (h9 : d₁ * d₁ + d₂ * d₂ - c₁ * d₁ - c₂ * d₂ > 0)
    (h10 : c₁ * d₁ - c₁ - d₁ + 1 + c₂ * d₂ > 0)
    (h11 : d₁ - c₁ - c₁ * d₁ + c₁ * c₁ + c₂ * c₂ - c₂ * d₂ > 0)
    (h12 : c₁ - d₁ - c₁ * d₁ + d₁ * d₁ + d₂ * d₂ - c₂ * d₂ > 0) :
    False := by
  obtain ⟨α, β, hα⟩ : ∃ α β : ℝ, d₁ = α + β * c₁ ∧ d₂ = β * c₂ := by
    by_cases hc₂ : c₂ = 0
    · nlinarith
    · exact ⟨d₁ - (d₂ / c₂) * c₁, d₂ / c₂, by ring, by rw [div_mul_cancel₀ _ hc₂]⟩
  norm_num [hα] at *
  by_cases hβ : β > 0
  · by_cases hα : α > 0
    · by_cases hβ' : β < 1
      · by_cases hβ'' : β < 1 / 2
        · nlinarith only [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, hα, hβ'',
            mul_pos hα h1, mul_pos hα (sub_pos.mpr hβ),
            mul_pos h1 (sub_pos.mpr hβ), mul_pos h1 (sub_pos.mpr hβ'),
            mul_pos hα (sub_pos.mpr hβ'), mul_pos h1 (sub_pos.mpr hβ'), hβ]
        · nlinarith only [hα, hβ'', h8, h9, h10, h11, h12, h1, h2, h3, h4, h5, h6, h7,
            mul_le_mul_of_nonneg_left (le_of_not_gt hβ'') hα.le,
            mul_le_mul_of_nonneg_left (le_of_not_gt hβ'') h1.le]
      · nlinarith [mul_le_mul_of_nonneg_left (le_of_not_gt hβ') h1.le]
    · nlinarith [mul_le_mul_of_nonneg_left h2.le hβ.le]
  · norm_num at *
    nlinarith [mul_le_mul_of_nonneg_left hβ h1.le,
               mul_le_mul_of_nonneg_left hβ (sub_nonneg.mpr h2.le)]

lemma inner_fin2 (v w : EuclideanSpace ℝ (Fin 2)) :
    @inner ℝ _ _ v w = v 0 * w 0 + v 1 * w 1 := by
  simp +decide [inner, EuclideanSpace.norm_eq]; ring!

lemma P_injective
    (P : Fin 100 → Pt)
    (hP : ∀ a b c : Fin 100,
             List.Nodup [a, b, c] → ¬ Collinear ℝ {P a, P b, P c}) :
    Function.Injective P := by
  intro a b hab
  by_contra h_neq
  obtain ⟨c, hc⟩ : ∃ c : Fin 100, c ≠ a ∧ c ≠ b := by
    exact Exists.imp (by aesop)
      (Finset.exists_mem_ne (show 1 < Finset.card (Finset.univ.erase a) from by
        rw [Finset.card_erase_of_mem (Finset.mem_univ a), Finset.card_fin]; decide) b)
  specialize hP c a b; simp_all +decide [collinear_pair]

lemma four_point_algebraic_general (b₁ b₂ c₁ c₂ d₁ d₂ : ℝ)
    (hr : b₁ * b₁ + b₂ * b₂ > 0)
    (h1 : b₁ * c₁ + b₂ * c₂ > 0)
    (h2 : b₁ * b₁ + b₂ * b₂ - b₁ * c₁ - b₂ * c₂ > 0)
    (h3 : c₁ * c₁ + c₂ * c₂ - b₁ * c₁ - b₂ * c₂ > 0)
    (h4 : b₁ * d₁ + b₂ * d₂ > 0)
    (h5 : b₁ * b₁ + b₂ * b₂ - b₁ * d₁ - b₂ * d₂ > 0)
    (h6 : d₁ * d₁ + d₂ * d₂ - b₁ * d₁ - b₂ * d₂ > 0)
    (h7 : c₁ * d₁ + c₂ * d₂ > 0)
    (h8 : c₁ * c₁ + c₂ * c₂ - c₁ * d₁ - c₂ * d₂ > 0)
    (h9 : d₁ * d₁ + d₂ * d₂ - c₁ * d₁ - c₂ * d₂ > 0)
    (h10 : (c₁ - b₁) * (d₁ - b₁) + (c₂ - b₂) * (d₂ - b₂) > 0)
    (h11 : (c₁ - b₁) * (c₁ - b₁) + (c₂ - b₂) * (c₂ - b₂) -
           (c₁ - b₁) * (d₁ - b₁) - (c₂ - b₂) * (d₂ - b₂) > 0)
    (h12 : (d₁ - b₁) * (d₁ - b₁) + (d₂ - b₂) * (d₂ - b₂) -
           (c₁ - b₁) * (d₁ - b₁) - (c₂ - b₂) * (d₂ - b₂) > 0) :
    False := by
  convert four_point_algebraic ((b₁ * c₁ + b₂ * c₂) / (b₁ * b₁ + b₂ * b₂))
    ((b₁ * c₂ - b₂ * c₁) / (b₁ * b₁ + b₂ * b₂))
    ((b₁ * d₁ + b₂ * d₂) / (b₁ * b₁ + b₂ * b₂))
    ((b₁ * d₂ - b₂ * d₁) / (b₁ * b₁ + b₂ * b₂))
    _ _ _ _ _ _ _ _ _ _ _ _ using 1 <;>
  ring_nf at * <;> norm_num [hr.ne'] at * <;>
  all_goals nlinarith [mul_inv_cancel₀ (ne_of_gt hr),
    mul_inv_cancel₀ (ne_of_gt (sq_pos_of_pos hr))]

lemma not_all_four_acute (A B C D : Pt)
    (h_ABC : ∠ B A C < Real.pi / 2 ∧ ∠ A B C < Real.pi / 2 ∧ ∠ A C B < Real.pi / 2)
    (h_ABD : ∠ B A D < Real.pi / 2 ∧ ∠ A B D < Real.pi / 2 ∧ ∠ A D B < Real.pi / 2)
    (h_ACD : ∠ C A D < Real.pi / 2 ∧ ∠ A C D < Real.pi / 2 ∧ ∠ A D C < Real.pi / 2)
    (h_BCD : ∠ C B D < Real.pi / 2 ∧ ∠ B C D < Real.pi / 2 ∧ ∠ B D C < Real.pi / 2) :
    False := by
  have h_inner_conditions :
    (inner ℝ (B -ᵥ A) (C -ᵥ A) > 0) ∧
    (inner ℝ (B -ᵥ A) (B -ᵥ A) - inner ℝ (B -ᵥ A) (C -ᵥ A) > 0) ∧
    (inner ℝ (C -ᵥ A) (C -ᵥ A) - inner ℝ (B -ᵥ A) (C -ᵥ A) > 0) ∧
    (inner ℝ (B -ᵥ A) (D -ᵥ A) > 0) ∧
    (inner ℝ (B -ᵥ A) (B -ᵥ A) - inner ℝ (B -ᵥ A) (D -ᵥ A) > 0) ∧
    (inner ℝ (D -ᵥ A) (D -ᵥ A) - inner ℝ (B -ᵥ A) (D -ᵥ A) > 0) ∧
    (inner ℝ (C -ᵥ A) (D -ᵥ A) > 0) ∧
    (inner ℝ (C -ᵥ A) (C -ᵥ A) - inner ℝ (C -ᵥ A) (D -ᵥ A) > 0) ∧
    (inner ℝ (D -ᵥ A) (D -ᵥ A) - inner ℝ (C -ᵥ A) (D -ᵥ A) > 0) ∧
    (inner ℝ (C -ᵥ B) (D -ᵥ B) > 0) ∧
    (inner ℝ (C -ᵥ B) (C -ᵥ B) - inner ℝ (C -ᵥ B) (D -ᵥ B) > 0) ∧
    (inner ℝ (D -ᵥ B) (D -ᵥ B) - inner ℝ (C -ᵥ B) (D -ᵥ B) > 0) := by
      have h_distinct : B ≠ A ∧ C ≠ A ∧ D ≠ A ∧ C ≠ B ∧ D ≠ B ∧ D ≠ C := by
        refine' ⟨_, _, _, _, _, _⟩ <;> intro h <;>
          simp_all +decide [EuclideanGeometry.angle]
      have h_ic : ∀ (p₁ p₂ p₃ : Pt), p₁ ≠ p₂ → p₃ ≠ p₂ →
          (∠ p₁ p₂ p₃ < Real.pi / 2 ↔ inner ℝ (p₁ -ᵥ p₂) (p₃ -ᵥ p₂) > 0) := by
        simp_all +decide [EuclideanGeometry.angle, InnerProductGeometry.angle]
        exact fun p₁ p₂ p₃ hp₁ hp₃ =>
          ⟨fun h => by contrapose! h;
              exact div_nonpos_of_nonpos_of_nonneg h (mul_nonneg (norm_nonneg _) (norm_nonneg _)),
           fun h => div_pos h (mul_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hp₁))
              (norm_pos_iff.mpr (sub_ne_zero.mpr hp₃)))⟩
      norm_num [inner] at *; grind +ring
  have := four_point_algebraic_general (B 0 - A 0) (B 1 - A 1) (C 0 - A 0) (C 1 - A 1)
    (D 0 - A 0) (D 1 - A 1) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
    norm_num [inner] at * <;> all_goals linarith

open Classical in
noncomputable section

def IsAcuteTriple (P : Fin 100 → Pt) (a b c : Fin 100) : Prop :=
  ∠ (P b) (P a) (P c) < Real.pi / 2 ∧
  ∠ (P a) (P b) (P c) < Real.pi / 2 ∧
  ∠ (P a) (P c) (P b) < Real.pi / 2

lemma acuteTriangle_iff_isAcuteTriple (P : Fin 100 → Pt) (a b c : Fin 100)
    (h : AffineIndependent ℝ ![P a, P b, P c]) :
    AcuteTriangle ⟨![P a, P b, P c], h⟩ ↔ IsAcuteTriple P a b c := by
  unfold AcuteTriangle IsAcuteTriple
  simp +decide [EuclideanGeometry.angle_comm]; ring!; aesop

lemma isAcuteTriple_perm (P : Fin 100 → Pt) (a b c : Fin 100) :
    IsAcuteTriple P a b c ↔ IsAcuteTriple P b a c := by
  unfold IsAcuteTriple; simp +decide [EuclideanGeometry.angle_comm]; tauto

lemma isAcuteTriple_cycle (P : Fin 100 → Pt) (a b c : Fin 100) :
    IsAcuteTriple P a b c ↔ IsAcuteTriple P b c a := by
  unfold IsAcuteTriple; simp +decide [EuclideanGeometry.angle_comm]; tauto

lemma four_point_at_most_three_acute (P : Fin 100 → Pt) (a b c d : Fin 100)
    (hP : ∀ x y z : Fin 100, List.Nodup [x, y, z] → ¬Collinear ℝ {P x, P y, P z})
    (hne : a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d)
    (h1 : IsAcuteTriple P a b c)
    (h2 : IsAcuteTriple P a b d)
    (h3 : IsAcuteTriple P a c d)
    (h4 : IsAcuteTriple P b c d) :
    False := by
  apply not_all_four_acute (P a) (P b) (P c) (P d)
  · exact h1
  · exact h2
  · unfold IsAcuteTriple at *; aesop
  · unfold IsAcuteTriple at *; aesop

/-! ## Counting argument

We reformulate the problem in terms of ordered triples from Fin 100.
-/

/-- The Finset of ordered triples of distinct elements of Fin 100. -/
def allOrdTriples : Finset (Fin 100 × Fin 100 × Fin 100) :=
  Finset.univ.filter fun p => p.1 ≠ p.2.1 ∧ p.1 ≠ p.2.2 ∧ p.2.1 ≠ p.2.2

/-- The Finset of acute ordered triples. -/
def acuteOrdTriples (P : Fin 100 → Pt) : Finset (Fin 100 × Fin 100 × Fin 100) :=
  allOrdTriples.filter fun p => IsAcuteTriple P p.1 p.2.1 p.2.2

/-
PROBLEM
Among any 5 distinct points, at most 7 of the 10 unordered triples are acute.
    The proof uses four_point_at_most_three_acute and double counting over
    4-element subsets of the 5 points.

PROVIDED SOLUTION
The proof uses four_point_at_most_three_acute and the double counting over 4-element subsets.

Define indicator variables x₁ through x₁₀ for the 10 triples:
x₁ = if IsAcuteTriple P a b c then 1 else 0
x₂ = if IsAcuteTriple P a b d then 1 else 0
x₃ = if IsAcuteTriple P a b e then 1 else 0
x₄ = if IsAcuteTriple P a c d then 1 else 0
x₅ = if IsAcuteTriple P a c e then 1 else 0
x₆ = if IsAcuteTriple P a d e then 1 else 0
x₇ = if IsAcuteTriple P b c d then 1 else 0
x₈ = if IsAcuteTriple P b c e then 1 else 0
x₉ = if IsAcuteTriple P b d e then 1 else 0
x₁₀ = if IsAcuteTriple P c d e then 1 else 0

The 5 four-element subsets give sums:
S₁ = x₁ + x₂ + x₄ + x₇  (subset {a,b,c,d})
S₂ = x₁ + x₃ + x₅ + x₈  (subset {a,b,c,e})
S₃ = x₂ + x₃ + x₆ + x₉  (subset {a,b,d,e})
S₄ = x₄ + x₅ + x₆ + x₁₀ (subset {a,c,d,e})
S₅ = x₇ + x₈ + x₉ + x₁₀ (subset {b,c,d,e})

Key identity: S₁ + S₂ + S₃ + S₄ + S₅ = 2 * (x₁ + x₂ + ... + x₁₀).

Each Sᵢ ≤ 3 because Sᵢ = 4 would mean all 4 triples in the 4-element subset are acute, contradicting four_point_at_most_three_acute. More precisely: each xᵢ ∈ {0, 1}, so Sᵢ ≤ 4. But Sᵢ = 4 means all 4 indicators are 1, i.e., all 4 triples are acute, which contradicts four_point_at_most_three_acute.

So: 2 * sum ≤ S₁ + S₂ + S₃ + S₄ + S₅ ≤ 5 * 3 = 15.
Hence: sum ≤ 7 (since 15/2 = 7.5 and sum is a natural number).

Implementation hint: set x₁ through x₁₀, show each is 0 or 1 (by split_ifs), show the 5 sums are each ≤ 3 (by showing ≠ 4 using four_point_at_most_three_acute with the right distinctness and if-then-else unfolding), combine with omega.
-/
lemma five_unordered_bound (P : Fin 100 → Pt)
    (hP : ∀ x y z : Fin 100, List.Nodup [x, y, z] → ¬Collinear ℝ {P x, P y, P z})
    (a b c d e : Fin 100)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hae : a ≠ e)
    (hbc : b ≠ c) (hbd : b ≠ d) (hbe : b ≠ e)
    (hcd : c ≠ d) (hce : c ≠ e) (hde : d ≠ e) :
    (if IsAcuteTriple P a b c then 1 else 0) +
    (if IsAcuteTriple P a b d then 1 else 0) +
    (if IsAcuteTriple P a b e then 1 else 0) +
    (if IsAcuteTriple P a c d then 1 else 0) +
    (if IsAcuteTriple P a c e then 1 else 0) +
    (if IsAcuteTriple P a d e then 1 else 0) +
    (if IsAcuteTriple P b c d then 1 else 0) +
    (if IsAcuteTriple P b c e then 1 else 0) +
    (if IsAcuteTriple P b d e then 1 else 0) +
    (if IsAcuteTriple P c d e then 1 else 0) ≤ 7 := by
  -- By the lemma four_point_at_most_three_acute, each four-element subset of {a, b, c, d, e} has at most 3 acute triples.
  have h_four_subset : ∀ (x y z w : Fin 100), x ≠ y ∧ x ≠ z ∧ x ≠ w ∧ y ≠ z ∧ y ≠ w ∧ z ≠ w →
    (if IsAcuteTriple P x y z then 1 else 0) + (if IsAcuteTriple P x y w then 1 else 0) + (if IsAcuteTriple P x z w then 1 else 0) + (if IsAcuteTriple P y z w then 1 else 0) ≤ 3 := by
      intro x y z w hne; intros; split_ifs <;> simp_all +decide only ;
      exact four_point_at_most_three_acute P x y z w ( fun a b c h => hP a b c <| by aesop ) hne ‹_› ‹_› ‹_› ‹_›;
  grind +ring

/-
PROBLEM
A simple ℚ arithmetic lemma.

PROVIDED SOLUTION
Case split on m = 0 vs m > 0. When m = 0: n / 0 = 0 ≤ 7/10. When m > 0: use div_le_div_iff with m > 0 and 10 > 0, then cast the Nat inequality to ℚ.
-/
lemma nat_div_le_of_mul_le {n m : ℕ} (h : 10 * n ≤ 7 * m) :
    (n : ℚ) / m ≤ 7 / 10 := by
  by_cases hm : m = 0 <;> simp_all +decide [ mul_comm, div_le_iff₀ ];
  · norm_num;
  · rw [ div_le_div_iff₀ ] <;> norm_cast ; linarith [ Nat.pos_of_ne_zero hm ];
    positivity

/-
PROBLEM
The Nat.card of the "all triangles" subtype equals the card of allOrdTriples.

PROVIDED SOLUTION
Establish a bijection (Equiv) between the subtype { t : Affine.Triangle ℝ Pt | ∃ a b c : Fin 100, ![P a, P b, P c] = t.points } and the subtype { p : Fin 100 × Fin 100 × Fin 100 | p.1 ≠ p.2.1 ∧ p.1 ≠ p.2.2 ∧ p.2.1 ≠ p.2.2 }, then use Nat.card_congr.

Forward map: Given (t, ⟨a, b, c, h⟩), choose (a, b, c) using Classical.choice. The distinctness follows from the fact that t is a simplex (affinely independent), which means P a, P b, P c are distinct, hence a, b, c are distinct by P_injective.

Backward map: Given (a, b, c, hne), construct the simplex. The points P a, P b, P c are non-collinear (by hP with the nodup hypothesis from hne), hence affinely independent. Define t as ⟨![P a, P b, P c], proof⟩.

Left inverse: Given (a, b, c, hne), the backward map gives a simplex t with t.points = ![P a, P b, P c]. Then the forward map extracts some (a', b', c') such that ![P a', P b', P c'] = ![P a, P b, P c]. Since P is injective, a'=a, b'=b, c'=c.

Right inverse: Given (t, ⟨a, b, c, h⟩), we extract some (a', b', c') with ![P a', P b', P c'] = t.points. Then the backward map gives the simplex with points ![P a', P b', P c'] = t.points, so the simplex is t (simplices are determined by their points).

Then allOrdTriples.card = Fintype.card of the subtype (both count ordered distinct triples). And Nat.card of the subtype = Fintype.card = allOrdTriples.card.

Use Nat.card_congr to transport the equality.
-/
lemma natCard_all_eq_ordTriples (P : Fin 100 → Pt)
    (hP : ∀ a b c : Fin 100, List.Nodup [a, b, c] → ¬ Collinear ℝ {P a, P b, P c}) :
    Nat.card { t : Affine.Triangle ℝ Pt |
      ∃ a b c : Fin 100, ![P a, P b, P c] = t.points } = allOrdTriples.card := by
  have h_equiv : {t : Affine.Triangle ℝ Pt | ∃ a b c : Fin 100, ![P a, P b, P c] = t.points} ≃ {p : Fin 100 × Fin 100 × Fin 100 | p.1 ≠ p.2.1 ∧ p.1 ≠ p.2.2 ∧ p.2.1 ≠ p.2.2} := by
    symm;
    refine' Equiv.ofBijective _ ⟨ _, _ ⟩;
    use fun p => ⟨ ⟨ ![P p.val.1, P p.val.2.1, P p.val.2.2], by
      rw [ affineIndependent_iff_not_collinear ] ; aesop; ⟩, ⟨ p.val.1, p.val.2.1, p.val.2.2, rfl ⟩ ⟩
    all_goals generalize_proofs at *;
    · intro p q h_eq; simp_all +decide [ Function.Injective, Finset.ext_iff ] ;
      have h_inj : Function.Injective P := by
        intro a b hab; specialize hP a b; simp_all +decide [ collinear_pair ] ;
        exact Classical.not_not.1 fun h => by have := hP ( a + 1 ) ( by aesop ) ( by aesop ) ; have := hP ( a + 2 ) ( by aesop ) ( by aesop ) ; aesop;
      generalize_proofs at *; aesop;
    · intro t
      generalize_proofs at *;
      rcases t with ⟨ t, ⟨ a, b, c, h ⟩ ⟩ ; use ⟨ ( a, b, c ), by
        have := t.independent;
        rw [ ← h ] at this;
        exact ⟨ fun h' => by have := this.injective; have := @this 0 1; aesop, fun h' => by have := this.injective; have := @this 0 2; aesop, fun h' => by have := this.injective; have := @this 1 2; aesop ⟩ ⟩ ; aesop;
  rw [ Nat.card_congr h_equiv ];
  simp +zetaDelta at *;
  native_decide +revert

/-
PROBLEM
The Nat.card of the "acute triangles" subtype equals the card of acuteOrdTriples.

PROVIDED SOLUTION
Very similar to natCard_all_eq_ordTriples. Establish a bijection between { t | ∃ a b c, ![P a, P b, P c] = t.points ∧ AcuteTriangle t } and { p ∈ allOrdTriples | IsAcuteTriple P p.1 p.2.1 p.2.2 }.

Forward map: extract (a,b,c) by choice, check IsAcuteTriple using acuteTriangle_iff_isAcuteTriple.
Backward map: construct simplex from (a,b,c), verify AcuteTriangle using acuteTriangle_iff_isAcuteTriple.
Bijectivity: same argument as natCard_all_eq_ordTriples, using P_injective.

Then (acuteOrdTriples P).card = Fintype.card of the filtered subtype.
-/
lemma natCard_acute_eq_ordTriples (P : Fin 100 → Pt)
    (hP : ∀ a b c : Fin 100, List.Nodup [a, b, c] → ¬ Collinear ℝ {P a, P b, P c}) :
    Nat.card { t : Affine.Triangle ℝ Pt |
      ∃ a b c : Fin 100, ![P a, P b, P c] = t.points ∧ AcuteTriangle t } =
    (acuteOrdTriples P).card := by
  have h_equiv : {t : Affine.Triangle ℝ Pt | ∃ a b c, ![P a, P b, P c] = t.points ∧ AcuteTriangle t} ≃ {p : Fin 100 × Fin 100 × Fin 100 | IsAcuteTriple P p.1 p.2.1 p.2.2 ∧ p.1 ≠ p.2.1 ∧ p.1 ≠ p.2.2 ∧ p.2.1 ≠ p.2.2} := by
    symm;
    refine' Equiv.ofBijective _ ⟨ fun x y h => _, fun t => _ ⟩;
    use fun p => ⟨ ⟨ ![P p.val.1, P p.val.2.1, P p.val.2.2], by
      rw [ affineIndependent_iff_not_collinear ] ; aesop; ⟩, by
      all_goals generalize_proofs at *;
      exact ⟨ _, _, _, rfl, by exact acuteTriangle_iff_isAcuteTriple P _ _ _ ‹_› |>.2 p.2.1 ⟩ ⟩
    all_goals generalize_proofs at *;
    · simp +zetaDelta at *;
      have := P_injective P ( fun a b c h => hP a b c ( by aesop ) ( by aesop ) ( by aesop ) ) ; aesop;
    · rcases t with ⟨ t, ⟨ a, b, c, h₁, h₂ ⟩ ⟩
      generalize_proofs at *;
      use ⟨ ( a, b, c ), by
        have h_distinct : a ≠ b ∧ a ≠ c ∧ b ≠ c := by
          have := t.independent; simp_all +decide [ affineIndependent_iff_not_collinear ] ;
          contrapose! this; simp_all +decide [ ← h₁, collinear_pair ] ;
          by_cases ha : a = b <;> by_cases hb : a = c <;> by_cases hc : b = c <;> simp_all +decide [ collinear_pair ];
          exact collinear_singleton _ _
        generalize_proofs at *;
        have h_acute : IsAcuteTriple P a b c := by
          have h_acute : AcuteTriangle ⟨![P a, P b, P c], by
            have := t.independent; aesop;⟩ := by
            convert h₂ using 1
            generalize_proofs at *; aesop;
          generalize_proofs at *;
          exact acuteTriangle_iff_isAcuteTriple P a b c ‹_› |>.1 h_acute
        generalize_proofs at *;
        exact ⟨h_acute, h_distinct⟩ ⟩
      generalize_proofs at *;
      aesop;
  rw [ Nat.card_congr h_equiv ];
  simp +decide [ acuteOrdTriples ];
  rw [ Fintype.subtype_card ];
  exact congr_arg Finset.card ( by ext; unfold allOrdTriples; aesop )

/-
PROBLEM
The key counting bound: 10 * (acute ordered triples) ≤ 7 * (all ordered triples).

PROVIDED SOLUTION
The proof uses double counting over 5-element subsets of Fin 100.

Key steps:
1. acuteOrdTriples P ⊆ allOrdTriples (by definition, since acuteOrdTriples filters allOrdTriples)
2. For each 5-element subset S ⊆ Fin 100, define:
   - tripsIn S = allOrdTriples.filter(fun t => t.1 ∈ S ∧ t.2.1 ∈ S ∧ t.2.2 ∈ S) has card = 60 (= 5*4*3)
   - acuteTripsIn S = (acuteOrdTriples P).filter(same) has card ≤ 42 (= 7*6, using five_unordered_bound)

3. Double counting identity:
   ∑ S ∈ fiveSets, (acuteTripsIn S).card = ∑ t ∈ acuteOrdTriples, (# five-sets containing t)
   = (acuteOrdTriples P).card * C(97,2)
   = (acuteOrdTriples P).card * 4656

4. Similarly:
   ∑ S ∈ fiveSets, (tripsIn S).card = allOrdTriples.card * 4656

5. From step 2:
   (acuteOrdTriples P).card * 4656 ≤ fiveSets.card * 42

6. From step 4:
   allOrdTriples.card * 4656 = fiveSets.card * 60

7. From steps 5 and 6:
   10 * (acuteOrdTriples P).card * 4656 ≤ 10 * fiveSets.card * 42 = fiveSets.card * 420
   7 * allOrdTriples.card * 4656 = 7 * fiveSets.card * 60 = fiveSets.card * 420
   So 10 * (acuteOrdTriples P).card * 4656 ≤ 7 * allOrdTriples.card * 4656
   Since 4656 > 0, divide to get: 10 * (acuteOrdTriples P).card ≤ 7 * allOrdTriples.card.

Use Finset.sum_comm to swap the order of summation in step 3. Use Finset operations and cardinality lemmas.

Actually, a simpler approach: use Finset.card_filter and Finset.sum_le_sum directly. Define the 5-element subsets as (Finset.univ : Finset (Fin 100)).powerset.filter (·.card = 5).
-/
lemma counting_bound (P : Fin 100 → Pt)
    (hP : ∀ a b c : Fin 100, List.Nodup [a, b, c] → ¬ Collinear ℝ {P a, P b, P c}) :
    10 * (acuteOrdTriples P).card ≤ 7 * allOrdTriples.card := by
  -- By the lemma `five_unordered_bound`, for any five distinct points, at most 7 of the 10 possible triangles are acute.
  have h_five_bound : ∀ (a b c d e : Fin 100), a ≠ b → a ≠ c → a ≠ d → a ≠ e → b ≠ c → b ≠ d → b ≠ e → c ≠ d → c ≠ e → d ≠ e →
    (if IsAcuteTriple P a b c then 1 else 0) + (if IsAcuteTriple P a b d then 1 else 0) + (if IsAcuteTriple P a b e then 1 else 0) +
    (if IsAcuteTriple P a c d then 1 else 0) + (if IsAcuteTriple P a c e then 1 else 0) + (if IsAcuteTriple P a d e then 1 else 0) +
    (if IsAcuteTriple P b c d then 1 else 0) + (if IsAcuteTriple P b c e then 1 else 0) + (if IsAcuteTriple P b d e then 1 else 0) +
    (if IsAcuteTriple P c d e then 1 else 0) ≤ 7 := by
      intros a b c d e hab hbc hcd hde hac hbd hce hae hbe hcd'
      apply five_unordered_bound P hP a b c d e hab hbc hcd hde hac hbd hce hae hbe hcd';
  -- Let's choose any five distinct points $a, b, c, d, e$ from the set of 100 points.
  set fiveSets := Finset.powersetCard 5 (Finset.univ : Finset (Fin 100)) with h_fiveSets_def;
  -- By the lemma `five_unordered_bound`, for any five distinct points, the number of acute triangles is at most 7.
  have h_five_bound : ∀ S ∈ fiveSets, ∑ x ∈ S, ∑ y ∈ S, ∑ z ∈ S, (if x ≠ y ∧ x ≠ z ∧ y ≠ z ∧ IsAcuteTriple P x y z then 1 else 0) ≤ 7 * 6 := by
    intros S hS
    obtain ⟨a, b, c, d, e, ha, hb, hc, hd, he, h_distinct⟩ : ∃ a b c d e : Fin 100, a ∈ S ∧ b ∈ S ∧ c ∈ S ∧ d ∈ S ∧ e ∈ S ∧ a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ a ≠ e ∧ b ≠ c ∧ b ≠ d ∧ b ≠ e ∧ c ≠ d ∧ c ≠ e ∧ d ≠ e ∧ S = {a, b, c, d, e} := by
      simp +zetaDelta at *;
      simp +decide [ Finset.card_eq_succ ] at hS;
      rcases hS with ⟨ a, b, c, d, e, h, rfl, h', h'', h''' ⟩ ; use a, by simp +decide, b, by simp +decide, c, by simp +decide, d, by simp +decide, e, by simp +decide ; ; aesop;
    simp_all +decide [ Finset.sum ];
    simp_all +decide [ isAcuteTriple_perm, isAcuteTriple_cycle, eq_comm ];
    have h_symm : ∀ x y z : Fin 100, IsAcuteTriple P x y z ↔ IsAcuteTriple P y x z := by
      exact isAcuteTriple_perm P;
    grind +ring;
  -- By summing over all five-element subsets, we get the total number of acute triangles.
  have h_total_acute : ∑ S ∈ fiveSets, ∑ x ∈ S, ∑ y ∈ S, ∑ z ∈ S, (if x ≠ y ∧ x ≠ z ∧ y ≠ z ∧ IsAcuteTriple P x y z then 1 else 0) = ∑ x ∈ Finset.univ, ∑ y ∈ Finset.univ, ∑ z ∈ Finset.univ, (if x ≠ y ∧ x ≠ z ∧ y ≠ z ∧ IsAcuteTriple P x y z then Nat.choose 97 2 else 0) := by
    have h_total_acute : ∀ x y z : Fin 100, x ≠ y ∧ x ≠ z ∧ y ≠ z → ∑ S ∈ fiveSets, (if x ∈ S ∧ y ∈ S ∧ z ∈ S then 1 else 0) = Nat.choose 97 2 := by
      intros x y z h_distinct
      have h_count : Finset.card (Finset.filter (fun S => x ∈ S ∧ y ∈ S ∧ z ∈ S) fiveSets) = Nat.choose 97 2 := by
        have h_count : Finset.card (Finset.filter (fun S => x ∈ S ∧ y ∈ S ∧ z ∈ S) fiveSets) = Finset.card (Finset.image (fun S => Insert.insert x (Insert.insert y (Insert.insert z S))) (Finset.powersetCard 2 (Finset.univ \ {x, y, z}))) := by
          refine' congr_arg Finset.card ( Finset.ext fun S => _ );
          simp [h_fiveSets_def, Finset.mem_image];
          constructor;
          · intro hS
            use S \ {x, y, z};
            grind +ring;
          · grind;
        rw [ h_count, Finset.card_image_of_injOn ];
        · simp +decide [ Finset.card_sdiff, * ];
        · intro S hS T hT h_eq; simp_all +decide [ Finset.subset_iff, Finset.ext_iff ] ;
          grind +ring;
      rw [ ← h_count, Finset.card_filter ];
    have h_total_acute : ∀ S ∈ fiveSets, ∑ x ∈ S, ∑ y ∈ S, ∑ z ∈ S, (if x ≠ y ∧ x ≠ z ∧ y ≠ z ∧ IsAcuteTriple P x y z then 1 else 0) = ∑ x ∈ Finset.univ, ∑ y ∈ Finset.univ, ∑ z ∈ Finset.univ, (if x ∈ S ∧ y ∈ S ∧ z ∈ S ∧ x ≠ y ∧ x ≠ z ∧ y ≠ z ∧ IsAcuteTriple P x y z then 1 else 0) := by
      intro S hS;
      rw [ ← Finset.sum_subset ( Finset.subset_univ S ) ];
      · refine' Finset.sum_congr rfl fun x hx => _;
        rw [ ← Finset.sum_subset ( Finset.subset_univ S ) ];
        · refine' Finset.sum_congr rfl fun y hy => _;
          rw [ ← Finset.sum_subset ( Finset.subset_univ S ) ] ; aesop;
          grind +ring;
        · simp +contextual [ hx ];
      · simp +contextual [ Finset.sum_ite ];
    rw [ Finset.sum_congr rfl h_total_acute, Finset.sum_comm ];
    refine' Finset.sum_congr rfl fun x hx => _;
    rw [ Finset.sum_comm, Finset.sum_congr rfl ] ; intros ; rw [ Finset.sum_comm ] ; rw [ Finset.sum_congr rfl ] ; intros ; aesop;
  have h_total_acute : ∑ x ∈ Finset.univ, ∑ y ∈ Finset.univ, ∑ z ∈ Finset.univ, (if x ≠ y ∧ x ≠ z ∧ y ≠ z ∧ IsAcuteTriple P x y z then Nat.choose 97 2 else 0) ≤ 7 * 6 * Nat.choose 100 5 := by
    rw [ ← h_total_acute ];
    refine' le_trans ( Finset.sum_le_sum h_five_bound ) _;
    norm_num [ mul_comm, Finset.card_powersetCard ];
    rw [ Finset.card_powersetCard, Finset.card_fin ];
  have h_total_acute : ∑ x ∈ Finset.univ, ∑ y ∈ Finset.univ, ∑ z ∈ Finset.univ, (if x ≠ y ∧ x ≠ z ∧ y ≠ z ∧ IsAcuteTriple P x y z then 1 else 0) = (acuteOrdTriples P).card := by
    rw [ show acuteOrdTriples P = Finset.filter ( fun p : Fin 100 × Fin 100 × Fin 100 => p.1 ≠ p.2.1 ∧ p.1 ≠ p.2.2 ∧ p.2.1 ≠ p.2.2 ∧ IsAcuteTriple P p.1 p.2.1 p.2.2 ) ( Finset.univ : Finset ( Fin 100 × Fin 100 × Fin 100 ) ) from ?_ ];
    · rw [ Finset.card_filter ];
      simp +decide only [← Finset.sum_product'];
      rfl;
    · ext ⟨a, b, c⟩; simp [acuteOrdTriples, allOrdTriples];
      grind;
  have h_total_acute : (acuteOrdTriples P).card * Nat.choose 97 2 ≤ 7 * 6 * Nat.choose 100 5 := by
    simp_all +contextual [ Finset.sum_ite ];
    simp_all +decide [ ← Finset.sum_mul _ _ _ ];
  norm_num [ Nat.choose ] at *;
  exact le_trans ( by linarith ) ( Nat.mul_le_mul_left _ ( show allOrdTriples.card ≥ 970200 by native_decide ) )

/-- The main ratio bound: at most 70% of all triangles are acute. -/
theorem imo1970_p6
    (P : Fin 100 → Pt)
    (hP : ∀ a b c : Fin 100,
             List.Nodup [a, b, c] → ¬ Collinear ℝ {P a, P b, P c}) :
    let cardAll := Nat.card { t : Affine.Triangle ℝ Pt |
                              ∃ a b c : Fin 100, ![P a, P b, P c] = t.points }
    let cardAcute :=
      Nat.card { t : Affine.Triangle ℝ Pt | ∃ a b c : Fin 100, ![P a, P b, P c] = t.points ∧
                                            AcuteTriangle t }
    (cardAcute : ℚ) / cardAll ≤ 7 / 10 := by
  intro cardAll cardAcute
  rw [show cardAll = allOrdTriples.card from natCard_all_eq_ordTriples P hP,
      show cardAcute = (acuteOrdTriples P).card from natCard_acute_eq_ordTriples P hP]
  exact nat_div_le_of_mul_le (counting_bound P hP)

end
end Imo1970P6