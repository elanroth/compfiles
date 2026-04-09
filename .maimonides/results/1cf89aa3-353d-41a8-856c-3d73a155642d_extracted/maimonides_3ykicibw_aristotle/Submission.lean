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

/-! ## Angle-inner product connection -/

/-- The angle ∠ p₁ p₂ p₃ is acute iff the inner product of the vectors p₁ - p₂ and p₃ - p₂
is positive (when the points are distinct). -/
lemma angle_lt_pi_div_two_iff_inner_pos {V P : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P]
    (p₁ p₂ p₃ : P) (h₁₂ : p₁ ≠ p₂) (h₃₂ : p₃ ≠ p₂) :
    ∠ p₁ p₂ p₃ < Real.pi / 2 ↔ (0 : ℝ) < @inner ℝ V _ (p₁ -ᵥ p₂) (p₃ -ᵥ p₂) := by
  have h_arccos : Real.arccos (inner ℝ (p₁ -ᵥ p₂) (p₃ -ᵥ p₂) / (‖p₁ -ᵥ p₂‖ * ‖p₃ -ᵥ p₂‖)) <
      Real.pi / 2 ↔ 0 < inner ℝ (p₁ -ᵥ p₂) (p₃ -ᵥ p₂) / (‖p₁ -ᵥ p₂‖ * ‖p₃ -ᵥ p₂‖) := by
    rw [Real.arccos_lt_pi_div_two]
  convert h_arccos using 1 ; ring! ; aesop

/-! ## Finiteness infrastructure -/

private lemma triangles_set_finite (P : Fin 100 → Pt) :
    Set.Finite {t : Affine.Triangle ℝ Pt | ∃ a b c : Fin 100, ![P a, P b, P c] = t.points} := by
  apply Set.Finite.of_finite_image (f := Affine.Simplex.points)
  · apply Set.Finite.subset (Set.finite_range fun abc : Fin 100 × Fin 100 × Fin 100 =>
      (![P abc.1, P abc.2.1, P abc.2.2] : Fin 3 → Pt))
    rintro f ⟨t, ⟨a, b, c, habc⟩, rfl⟩
    exact ⟨(a, b, c), by simp [habc]⟩
  · intros t1 _ t2 _ h
    exact Affine.Simplex.ext (fun i => congr_fun h i)

private lemma acute_triangles_set_finite (P : Fin 100 → Pt) :
    Set.Finite {t : Affine.Triangle ℝ Pt | ∃ a b c : Fin 100, ![P a, P b, P c] = t.points ∧ AcuteTriangle t} := by
  apply Set.Finite.subset (triangles_set_finite P)
  intro t ⟨a, b, c, h, _⟩
  exact ⟨a, b, c, h⟩

/-! ## P is injective -/

private lemma P_injective (P : Fin 100 → Pt)
    (hP : ∀ a b c : Fin 100, List.Nodup [a, b, c] → ¬Collinear ℝ {P a, P b, P c}) :
    Function.Injective P := by
  intro a b hab;
  contrapose! hP;
  obtain ⟨c, hc⟩ : ∃ c : Fin 100, c ≠ a ∧ c ≠ b := by
    exact Exists.imp ( by aesop ) ( Finset.exists_mem_ne ( show 1 < Finset.card ( Finset.univ.erase a ) from by simp +decide [ Finset.card_erase_of_mem ( Finset.mem_univ a ) ] ) b )
  use a, c, b; simp_all +decide [ collinear_pair ] ;
  tauto

/-- For 3 distinct Fin 100 indices, the points are affinely independent -/
lemma affineIndependent_of_distinct (P : Fin 100 → Pt)
    (hP : ∀ a b c : Fin 100, List.Nodup [a, b, c] → ¬Collinear ℝ {P a, P b, P c})
    {a b c : Fin 100} (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    AffineIndependent ℝ ![P a, P b, P c] := by
  rw [@affineIndependent_iff_not_collinear] ; aesop

/-! ## Main bound

### Proof outline for 10 * |acute| ≤ 7 * |all|

The proof proceeds through a chain of double counting arguments:

**Step 1 (4-point algebraic, proved above):** The system of 12 inequalities asserting
that all 4 triangles formed by 4 points (in normalized coordinates) are acute is
contradictory. This means among any 4 points in general position, at most 3 of the 4
triangles can be acute.

**Step 2 (5-point lemma):** Among any 5 points in general position, at most 7 of the
C(5,3) = 10 triangles are acute.

*Proof:* There are C(5,4) = 5 four-point subsets. By Step 1, each has at most 3 acute
triangles (out of 4). Each triangle belongs to exactly C(2,1) = 2 four-point subsets
(choosing 1 additional point from the remaining 2). By double counting:
  2 × (# acute triangles among 5 points) ≤ 3 × 5 = 15
So the number of acute triangles ≤ 7 (as ⌊15/2⌋ = 7).

**Step 3 (Main bound):** For n = 100 points, at most 7/10 of all triangles are acute.

*Proof:* There are C(100,5) five-point subsets. By Step 2, each has at most 7 acute
triangles (out of 10). Each triangle belongs to exactly C(97,2) = 4656 five-point
subsets (choosing 2 additional points from the remaining 97). Double counting:
  C(97,2) × A ≤ 7 × C(100,5)
  C(97,2) × T = 10 × C(100,5)
Dividing: A/T ≤ 7/10, equivalently 10A ≤ 7T.

For the ordered-triple formulation used in Nat.card:
  cardAcute = 6A, cardAll = 6T (each unordered triangle has 6 orderings)
  10 × 6A ≤ 7 × 6T, i.e., 10 × cardAcute ≤ 7 × cardAll.
-/
private lemma main_bound (P : Fin 100 → Pt)
    (hP : ∀ a b c : Fin 100, List.Nodup [a, b, c] → ¬Collinear ℝ {P a, P b, P c}) :
    10 * Nat.card {t : Affine.Triangle ℝ Pt | ∃ a b c : Fin 100, ![P a, P b, P c] = t.points ∧ AcuteTriangle t} ≤
    7 * Nat.card {t : Affine.Triangle ℝ Pt | ∃ a b c : Fin 100, ![P a, P b, P c] = t.points} := by
  haveI : Finite ↑{t : Affine.Triangle ℝ Pt | ∃ a b c : Fin 100, ![P a, P b, P c] = t.points} :=
    (triangles_set_finite P).to_subtype
  haveI : Finite ↑{t : Affine.Triangle ℝ Pt | ∃ a b c : Fin 100, ![P a, P b, P c] = t.points ∧ AcuteTriangle t} :=
    (acute_triangles_set_finite P).to_subtype
  sorry

/-! ## Main theorem -/

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
  simp only
  set cardAll := Nat.card ↑{t : Affine.Triangle ℝ Pt | ∃ a b c : Fin 100, ![P a, P b, P c] = t.points}
  set cardAcute := Nat.card ↑{t : Affine.Triangle ℝ Pt | ∃ a b c : Fin 100, ![P a, P b, P c] = t.points ∧ AcuteTriangle t}
  by_cases hAll : cardAll = 0
  · simp [hAll]; norm_num
  · rw [div_le_div_iff₀ (by exact_mod_cast Nat.pos_of_ne_zero hAll : (0:ℚ) < cardAll)
        (by norm_num : (0:ℚ) < 10)]
    have h' : cardAcute * 10 ≤ 7 * cardAll := by
      have := main_bound P hP; linarith
    exact_mod_cast h'

end Imo1970P6
