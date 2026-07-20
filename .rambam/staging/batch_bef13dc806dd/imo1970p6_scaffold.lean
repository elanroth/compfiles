import Mathlib.Geometry.Euclidean.Basic
import Mathlib.Geometry.Euclidean.Triangle
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card

open scoped EuclideanGeometry

abbrev Pt := EuclideanSpace ℝ (Fin 2)

def AcuteTriangle (T : Affine.Triangle ℝ Pt) : Prop :=
  ∠ (T.points 1) (T.points 2) (T.points 3) < Real.pi / 2 ∧
  ∠ (T.points 2) (T.points 3) (T.points 1) < Real.pi / 2 ∧
  ∠ (T.points 3) (T.points 1) (T.points 2) < Real.pi / 2

/-- Among any 4 points in general position (no three collinear), 
    at most 3 of the 4 triangles formed are acute. This is the key lemma
    that enables the double-counting argument. -/
lemma four_points_at_most_three_acute
    (A B C D : Pt)
    (h_general : ¬ Collinear ℝ {A, B, C} ∧ ¬ Collinear ℝ {A, B, D} ∧ 
                 ¬ Collinear ℝ {A, C, D} ∧ ¬ Collinear ℝ {B, C, D}) :
    let triangles := [⟨![A, B, C]⟩, ⟨![A, B, D]⟩, ⟨![A, C, D]⟩, ⟨![B, C, D]⟩]
    (triangles.filter (fun t => AcuteTriangle t)).length ≤ 3 := by
  -- The proof splits into two cases: convex position vs one point inside triangle
  -- In convex quadrilateral: at least one angle > 90°, so at least one triangle is obtuse
  -- When one point is inside: the three angles around it sum to 360°, so one > 120° > 90°
  sorry

/-- Double counting argument: count pairs (acute triangle, fourth point) two ways -/
lemma double_counting_bound 
    (P : Fin 100 → Pt)
    (hP : ∀ a b c : Fin 100, List.Nodup [a, b, c] → ¬ Collinear ℝ {P a, P b, P c}) :
    let triangles := { t : Affine.Triangle ℝ Pt | ∃ a b c : Fin 100, ![P a, P b, P c] = t.points }
    let acute_triangles := { t ∈ triangles | AcuteTriangle t }
    97 * (Nat.card acute_triangles) ≤ 3 * (Nat.choose 100 4) := by
  -- Left side: each acute triangle pairs with 97 other points
  -- Right side: each 4-point set contributes ≤ 3 acute triangles by the key lemma
  sorry

/-- Convert the combinatorial bound to the desired fraction bound -/
lemma fraction_bound_from_counting
    (P : Fin 100 → Pt)
    (hP : ∀ a b c : Fin 100, List.Nodup [a, b, c] → ¬ Collinear ℝ {P a, P b, P c}) :
    let cardAll := Nat.card { t : Affine.Triangle ℝ Pt |
                              ∃ a b c : Fin 100, ![P a, P b, P c] = t.points }
    let cardAcute := Nat.card { t : Affine.Triangle ℝ Pt | 
                                ∃ a b c : Fin 100, ![P a, P b, P c] = t.points ∧
                                AcuteTriangle t }
    (cardAcute : ℚ) / cardAll ≤ 3 / 4 := by
  -- Use: Nat.choose 100 4 = Nat.choose 100 3 * 97 / 4
  -- So: 97 * cardAcute ≤ 3 * cardAll * 97 / 4
  -- Therefore: cardAcute ≤ 3 * cardAll / 4
  sorry

/-- For the sharp 7/10 bound, we need to distinguish convex vs non-convex 4-point configurations.
    In convex position, at most 2 (not 3) of the 4 triangles can be acute. -/
lemma sharp_bound_convex_case
    (P : Fin 100 → Pt)
    (hP : ∀ a b c : Fin 100, List.Nodup [a, b, c] → ¬ Collinear ℝ {P a, P b, P c}) :
    let cardAll := Nat.card { t : Affine.Triangle ℝ Pt |
                              ∃ a b c : Fin 100, ![P a, P b, P c] = t.points }
    let cardAcute := Nat.card { t : Affine.Triangle ℝ Pt | 
                                ∃ a b c : Fin 100, ![P a, P b, P c] = t.points ∧
                                AcuteTriangle t }
    (cardAcute : ℚ) / cardAll ≤ 7 / 10 := by
  -- This requires analyzing the proportion of convex vs non-convex 4-point sets
  -- and using that convex sets contribute ≤ 2 acute triangles each
  sorry

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
  exact sharp_bound_convex_case P hP