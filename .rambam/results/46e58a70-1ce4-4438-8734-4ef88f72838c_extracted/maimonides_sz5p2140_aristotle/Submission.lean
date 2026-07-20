/-
Copyright (c) 2024 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

import Mathlib

/-!
# International Mathematical Olympiad 1970, Problem 6

In a plane there are 100 points, no three of which are collinear.
Consider all possible triangles having these points as vertices.
Prove that no more that 70% of these triangles are acute.
-/

namespace Imo1970P6

open scoped EuclideanGeometry

abbrev Pt := EuclideanSpace ℝ (Fin 2)

def AcuteTriangle (T : Affine.Triangle ℝ Pt) : Prop :=
  ∠ (T.points 1) (T.points 2) (T.points 3) < Real.pi / 2 ∧
  ∠ (T.points 2) (T.points 3) (T.points 1) < Real.pi / 2 ∧
  ∠ (T.points 3) (T.points 1) (T.points 2) < Real.pi / 2

/-! ## Key algebraic lemma

For 4 points in the plane with coordinates A=(0,0), B=(1,0), C=(c₁,c₂), D=(d₁,d₂),
the 12 inner-product conditions for all 4 triangles to be acute are inconsistent.
-/

/-- The 12 conditions for all 4 triangles formed by (0,0),(1,0),(c₁,c₂),(d₁,d₂) to be
    acute are mutually inconsistent. -/
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
    · by_cases hβ : β < 1
      · by_cases hβ : β < 1 / 2
        · nlinarith only [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, hα, hβ,
            mul_pos hα h1, mul_pos hα (sub_pos.mpr hβ),
            mul_pos h1 (sub_pos.mpr hβ), mul_pos h1 (sub_pos.mpr ‹β < 1›),
            mul_pos hα (sub_pos.mpr ‹β < 1›), mul_pos h1 (sub_pos.mpr ‹β < 1›), ‹β > 0›]
        · nlinarith only [hα, hβ, h8, h9, h10, h11, h12, h1, h2, h3, h4, h5, h6, h7,
            mul_le_mul_of_nonneg_left (le_of_not_gt hβ) hα.le,
            mul_le_mul_of_nonneg_left (le_of_not_gt hβ) h1.le]
      · nlinarith [mul_le_mul_of_nonneg_left (le_of_not_gt hβ) h1.le]
    · nlinarith [mul_le_mul_of_nonneg_left h2.le hβ.le]
  · norm_num at *
    nlinarith [mul_le_mul_of_nonneg_left hβ h1.le,
               mul_le_mul_of_nonneg_left hβ (sub_nonneg.mpr h2.le)]

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
  sorry

end Imo1970P6
