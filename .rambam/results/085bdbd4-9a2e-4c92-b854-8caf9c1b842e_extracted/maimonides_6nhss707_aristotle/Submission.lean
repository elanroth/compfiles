/-
Copyright (c) 2025 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
import Mathlib

/-!
# International Mathematical Olympiad 2021, Problem 3

Let D be an interior point of the acute triangle $ABC$ with
AB > AC so that ∠DAB = ∠CAD. The point E on the
segment AC satisfies ∠ADE = ∠BCD, the point F on
the segment AB satisfies ∠FDA = ∠DBC, and the point
X on the line AC satisfies CX = BX. Let O₁ and O₂ be
the circumcenters of the triangles ADC and EXD, respectively.
Prove that the lines BC, EF, and O₁O₂ are concurrent.
-/

open scoped EuclideanGeometry
open Affine Module

namespace Imo2021P3

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
variable [NormedAddTorsor V P] [Fact (finrank ℝ V = 2)]

/-
PROBLEM
If a point lies on both segment AC and segment AB (via Wbtw), and
A,B,C are not collinear, then the point must be A.

PROVIDED SOLUTION
E lies on segment AC (Wbtw A E C), so E is on the affine line through A and C (line[ℝ, A, C]). E also lies on affineSpan ℝ {A, B} = line[ℝ, A, B]. Since A, B, C are affinely independent (not collinear), lines AB and AC intersect only at A. Indeed, the affine spans line[ℝ, A, B] and line[ℝ, A, C] are 1-dimensional affine subspaces that both contain A. Their directions are spanned by (B - A) and (C - A) respectively. Since A, B, C are not collinear, these directions are linearly independent, so the two lines have only A in common. Therefore E = A.

Use affineIndependent_iff_not_collinear, and show that if E ∈ line[ℝ, A, C] ∩ line[ℝ, A, B] and E ≠ A, then A, B, C are collinear (since B and C are both in the affine span of {A, E} = line through A and E when E ≠ A).
-/
theorem wbtw_inter_eq_left {A B C E : P}
    (affineIndependent_ABC : AffineIndependent ℝ ![A, B, C])
    (wbtw_A_E_C : Wbtw ℝ A E C)
    (E_mem_AB : E ∈ affineSpan ℝ {A, B}) :
    E = A := by
  obtain ⟨ v₁, hv₁ ⟩ := wbtw_A_E_C;
  -- Since $E$ lies on the line $AB$ and also on the line $AC$, it must be that $E$ is a linear combination of $A$ and $B$ and also a linear combination of $A$ and $C$.
  obtain ⟨v₂, hv₂⟩ : ∃ v₂ : ℝ, (AffineMap.lineMap A B) v₂ = E := by
    exact?
  obtain ⟨v₃, hv₃⟩ : ∃ v₃ : ℝ, (AffineMap.lineMap A C) v₃ = E := by
    exact ⟨ v₁, hv₁.2 ⟩;
  -- Since $E$ lies on the line $AB$ and also on the line $AC$, we have $v₁ \cdot (C - A) = v₂ \cdot (B - A)$.
  have h_eq : v₁ • (C -ᵥ A) = v₂ • (B -ᵥ A) := by
    simp_all +decide [ AffineMap.lineMap_apply ];
    aesop;
  have h_lin_dep : LinearIndependent ℝ ![B -ᵥ A, C -ᵥ A] := by
    rw [ linearIndependent_fin2 ] at *;
    simp_all +decide [ affineIndependent_iff_not_collinear, collinear_pair ];
    refine' ⟨ _, _ ⟩;
    · rintro rfl; simp_all +decide [ collinear_pair ];
    · intro a ha; contrapose! affineIndependent_ABC; simp_all +decide [ collinear_iff_exists_forall_eq_smul_vadd ] ;
      refine' ⟨ A, C -ᵥ A, ⟨ 1, _ ⟩, ⟨ a, _ ⟩, ⟨ 0, _ ⟩ ⟩ <;> simp +decide [ ha ];
  rw [ Fintype.linearIndependent_iff ] at h_lin_dep;
  specialize h_lin_dep ( fun i => if i = 0 then -v₂ else v₁ ) ; simp_all +decide [ Fin.sum_univ_succ ]

/-
PROBLEM
D interior to triangle ABC implies D is not collinear with B and C.

PROVIDED SOLUTION
D is in the interior of triangle ABC, which in Mathlib means D is in the interior of the simplex, i.e., D can be written as a barycentric combination of A, B, C with all strictly positive weights summing to 1. The interior is `Simplex.interior` or `Simplex.setInterior`.

If B, C, D are collinear, then D lies in the affine span of {B, C}. But D is a convex combination of A, B, C with positive coefficient for A, so A must lie in the affine span of {B, C}, which would make A, B, C collinear, contradicting affine independence.

Alternatively: use that the interior of the triangle is an open set in the affine span of {A,B,C}, and that the affine span of {B,C} is a 1-dimensional subspace of this 2-dimensional space. Points in the interior cannot lie on the boundary, and the line through B and C is part of the boundary (it's one of the sides). Actually, the side BC is `{B, C}` edge, but D is in the interior, so D is not on any of the three sides.

Another approach: Simplex.interior is the set of points with all positive barycentric coordinates. The collinearity of B, C, D means D can be written as an affine combination of B and C. But in barycentric coordinates relative to {A, B, C}, this means the A-coordinate is 0, contradicting it being positive.
-/
theorem not_collinear_BCD_of_interior {A B C D : P}
    (affineIndependent_ABC : AffineIndependent ℝ ![A, B, C])
    (D_mem_interior_ABC : D ∈ (⟨_, affineIndependent_ABC⟩ : Triangle ℝ P).interior) :
    ¬Collinear ℝ ({B, C, D} : Set P) := by
  cases' D_mem_interior_ABC with A' A'_mem;
  obtain ⟨h_sum, h_pos, h_comb⟩ := A'_mem;
  rw [ collinear_iff_exists_forall_eq_smul_vadd ] ; simp_all +decide [ Fin.sum_univ_three ];
  intro x y a hx b hy c hc; have := affineIndependent_ABC; simp_all +decide [ Fin.sum_univ_three, affineIndependent_iff_not_collinear ] ;
  contrapose! affineIndependent_ABC; simp_all +decide [ collinear_iff_exists_forall_eq_smul_vadd ] ;
  rw [ Finset.affineCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one ] at h_comb;
  any_goals exact x;
  · simp_all +decide [ Fin.univ_succ ];
    refine' ⟨ x, y, ⟨ b, _ ⟩, ⟨ a, _ ⟩, ⟨ ( A -ᵥ x ) |> fun z => ( A' 0 ) ⁻¹ * ( c - A' 1 * a - A' 2 * b ), _ ⟩ ⟩ <;> simp_all +decide [ ← smul_assoc ];
    -- Rearrange h_comb to solve for A -ᵥ x.
    have h_rearrange : A' 0 • (A -ᵥ x) = (c - A' 1 * a - A' 2 * b) • y := by
      convert eq_sub_of_add_eq h_comb using 1 ; simp +decide [ sub_smul, add_smul ] ; abel_nf;
    rw [ ← smul_smul, ← h_rearrange, inv_smul_smul₀ ( ne_of_gt ( h_pos 0 |>.1 ) ), vsub_vadd ];
  · rwa [ Fin.sum_univ_three ]

/-
PROBLEM
If E = F, then E lies on both segment AC and segment AB, so E = A.
But then ∠ADE = ∠(A,D,A) = 0 while ∠BCD > 0, contradiction.

PROVIDED SOLUTION
Assume E = F for contradiction. Since Wbtw A E C, E lies on segment AC, hence E ∈ line[ℝ, A, C]. Since Wbtw A F B and E = F, E lies on segment AB, hence E ∈ affineSpan ℝ {A, B}. By wbtw_inter_eq_left, E = A. Substituting E = A into angle_ADE_eq_angle_BCD: ∠(A, D, A) = ∠(B, C, D). Now ∠(A, D, A) = 0 since the first and third arguments are equal (use EuclideanGeometry.angle_self_left or angle_eq_zero for equal endpoints). But ∠(B, C, D) > 0 because B, C, D are not collinear (by not_collinear_BCD_of_interior), and the angle is positive for non-collinear points. This gives 0 = positive, a contradiction.

Use `wbtw_inter_eq_left` and `not_collinear_BCD_of_interior` as helper lemmas. For ∠(A,D,A) = 0, use `EuclideanGeometry.angle_self_left` or `EuclideanGeometry.angle_self_right`. For ∠(B,C,D) > 0, use `EuclideanGeometry.angle_pos_of_not_collinear` or show it's nonzero from non-collinearity.
-/
theorem imo2021_p3_E_ne_F {A B C D E F : P}
    (affineIndependent_ABC : AffineIndependent ℝ ![A, B, C])
    (acuteAngled_ABC : (⟨_, affineIndependent_ABC⟩ : Triangle ℝ P).AcuteAngled)
    (AC_lt_AB : dist A C < dist A B)
    (D_mem_interior_ABC : D ∈ (⟨_, affineIndependent_ABC⟩ : Triangle ℝ P).interior)
    (angle_DAB_eq_angle_CAD : ∠ D A B = ∠ C A D) (wbtw_A_E_C : Wbtw ℝ A E C)
    (angle_ADE_eq_angle_BCD : ∠ A D E = ∠ B C D) (wbtw_A_F_B : Wbtw ℝ A F B)
    (angle_FDA_eq_angle_DBC : ∠ F D A = ∠ D B C) :
    E ≠ F := by
  intro h
  have h_eq : E = A := by
    apply wbtw_inter_eq_left affineIndependent_ABC wbtw_A_E_C (by
    rw [ h ] ; exact?;)
  have h_contra : ∠ (A) (D) (A) = ∠ (B) (C) (D) := by
    grind +ring
  have h_zero : ∠ (A) (D) (A) = 0 := by
    simp +decide [ EuclideanGeometry.angle ] at h_contra ⊢;
    rw [ InnerProductGeometry.angle_self ];
    intro h_zero
    have h_contra : D = A := by
      exact eq_of_vsub_eq_zero h_zero ▸ rfl
    simp [h_contra] at *;
    have := acuteAngled_ABC 0 1 2; simp_all +decide [ EuclideanGeometry.angle ] ;
  have h_pos : ∠ (B) (C) (D) > 0 := by
    have h_not_collinear : ¬Collinear ℝ ({B, C, D} : Set P) := by
      exact?
    exact EuclideanGeometry.angle_pos_of_not_collinear h_not_collinear |> fun h => h.trans_le' (by norm_num)
  linarith [h_zero, h_pos]

/-
PROBLEM
X ≠ A in the IMO 2021 P3 configuration: X on line AC with dist(C,X) = dist(B,X),
but dist(A,C) < dist(A,B) so X ≠ A.

PROVIDED SOLUTION
If X = A, then dist(C, A) = dist(B, A) by CX_eq_BX, i.e. dist(A, C) = dist(A, B). But AC_lt_AB says dist(A, C) < dist(A, B), contradiction.
-/
theorem imo2021_p3_X_ne_A {A B C X : P}
    (affineIndependent_ABC : AffineIndependent ℝ ![A, B, C])
    (AC_lt_AB : dist A C < dist A B)
    (X_mem_AC : X ∈ line[ℝ, A, C])
    (CX_eq_BX : dist C X = dist B X) :
    X ≠ A := by
  intro h; simp_all +decide [ dist_comm ] ;

/-
PROBLEM
X ≠ C in the IMO 2021 P3 configuration: X on line AC with dist(C,X) = dist(B,X),
but B ≠ C so X ≠ C.

PROVIDED SOLUTION
If X = C, then dist(C, C) = dist(B, C), so 0 = dist(B, C). This means B = C. But A, B, C are affinely independent, so B ≠ C. Use `affineIndependent_of_ne` or show that affine independence of ![A, B, C] implies B ≠ C (the function ![A,B,C] is injective when points are affinely independent... actually not necessarily, but it implies not collinear, which implies B ≠ C).
-/
theorem imo2021_p3_X_ne_C {A B C X : P}
    (affineIndependent_ABC : AffineIndependent ℝ ![A, B, C])
    (X_mem_AC : X ∈ line[ℝ, A, C])
    (CX_eq_BX : dist C X = dist B X) :
    X ≠ C := by
  intro h_eq_C
  have h_dist_C_C : dist C C = dist B C := by
    aesop
  simp_all +decide [ dist_eq_zero ];
  rw [ affineIndependent_iff_not_collinear ] at affineIndependent_ABC ; simp_all +decide [ collinear_pair ] ;

/-
PROBLEM
O₁ ≠ O₂: If O₁ = O₂, then X lies on circumcircle of ADC and on line AC.
A circle meets a line in at most 2 points, and A, C are already on both.
So X = A or X = C, but both are impossible (X ≠ A by dist inequality, X ≠ C since B ≠ C).

PROVIDED SOLUTION
Assume O₁ = O₂ for contradiction. Then since O₁ is the circumcenter of triangle ADC, we have dist(O₁, A) = dist(O₁, D) = dist(O₁, C) (all equal to circumradius). Since O₂ is the circumcenter of triangle EXD, we have dist(O₂, E) = dist(O₂, X) = dist(O₂, D). With O₁ = O₂, this means dist(O₁, X) = dist(O₁, D) = dist(O₁, A) = dist(O₁, C). So X lies on the circumsphere (circumcircle in 2D) of triangle ADC, centered at O₁. Points A and C also lie on this circle and on line AC. X also lies on line AC (by X_mem_AC). A circle in 2D intersects a line in at most 2 points. Since A ≠ C (from affine independence of A, B, C) and A, C are both on the circle and on line AC, X must be A or C. But X ≠ A by imo2021_p3_X_ne_A and X ≠ C by imo2021_p3_X_ne_C. Contradiction.

For the circle-line intersection fact, use that a metric sphere in a 2D inner product space intersects an affine line in at most 2 points. This can be shown by parametrizing the line and solving a quadratic. Look for Mathlib lemmas about Metric.Sphere or circumsphere membership.
-/
theorem imo2021_p3_O_ne {A B C D E F X O₁ O₂ : P}
    (affineIndependent_ABC : AffineIndependent ℝ ![A, B, C])
    (acuteAngled_ABC : (⟨_, affineIndependent_ABC⟩ : Triangle ℝ P).AcuteAngled)
    (AC_lt_AB : dist A C < dist A B)
    (D_mem_interior_ABC : D ∈ (⟨_, affineIndependent_ABC⟩ : Triangle ℝ P).interior)
    (angle_DAB_eq_angle_CAD : ∠ D A B = ∠ C A D) (wbtw_A_E_C : Wbtw ℝ A E C)
    (angle_ADE_eq_angle_BCD : ∠ A D E = ∠ B C D) (wbtw_A_F_B : Wbtw ℝ A F B)
    (angle_FDA_eq_angle_DBC : ∠ F D A = ∠ D B C) (X_mem_AC : X ∈ line[ℝ, A, C])
    (CX_eq_BX : dist C X = dist B X)
    (affineIndependent_ADC : AffineIndependent ℝ ![A, D, C])
    (O₁_eq_circumcenter_ADC :
      O₁ = (⟨_, affineIndependent_ADC⟩ : Triangle ℝ P).circumcenter)
    (affineIndependent_EXD : AffineIndependent ℝ ![E, X, D])
    (O₂_eq_circumcenter_EXD :
      O₂ = (⟨_, affineIndependent_EXD⟩ : Triangle ℝ P).circumcenter) :
    O₁ ≠ O₂ := by
  intro h_eq;
  -- Since O₁ = O₂, we have dist(O₁, A) = dist(O₁, D) = dist(O₁, C) and dist(O₁, E) = dist(O₁, X) = dist(O₁, D).
  have h_dist_eq : dist O₁ A = dist O₁ D ∧ dist O₁ D = dist O₁ C ∧ dist O₁ E = dist O₁ X ∧ dist O₁ X = dist O₁ D := by
    have := Simplex.dist_circumcenter_eq_circumradius ( Simplex.mk ![A, D, C] affineIndependent_ADC ) 0; have := Simplex.dist_circumcenter_eq_circumradius ( Simplex.mk ![A, D, C] affineIndependent_ADC ) 1; have := Simplex.dist_circumcenter_eq_circumradius ( Simplex.mk ![A, D, C] affineIndependent_ADC ) 2; have := Simplex.dist_circumcenter_eq_circumradius ( Simplex.mk ![E, X, D] affineIndependent_EXD ) 0; have := Simplex.dist_circumcenter_eq_circumradius ( Simplex.mk ![E, X, D] affineIndependent_EXD ) 1; have := Simplex.dist_circumcenter_eq_circumradius ( Simplex.mk ![E, X, D] affineIndependent_EXD ) 2; simp_all +decide [ dist_comm ] ;
  -- Since X lies on the line AC and the circle centered at O₁ with radius dist O₁ A, X must be either A or C.
  have h_X_eq_A_or_C : X = A ∨ X = C := by
    obtain ⟨t, ht⟩ : ∃ t : ℝ, X = t • (C -ᵥ A) +ᵥ A := by
      rw [ affineSpan ] at X_mem_AC;
      simp_all +decide [ spanPoints ];
      rcases X_mem_AC with ( ⟨ v, hv, rfl ⟩ | ⟨ v, hv, rfl ⟩ ) <;> rw [ vectorSpan_pair ] at hv <;> simp_all +decide [ Submodule.mem_span_singleton ];
      · rcases hv with ⟨ t, rfl ⟩ ; exact ⟨ -t, by simp +decide [ neg_smul, ← smul_neg ] ⟩ ;
      · rcases hv with ⟨ t, rfl ⟩;
        refine' ⟨ -t + 1, _ ⟩ ; simp +decide [ add_smul, smul_add, smul_sub, sub_smul ] ; abel_nf;
        simp +decide [ ← smul_assoc, ← vadd_vsub_assoc ];
        rw [ ← smul_neg, neg_vsub_eq_vsub_rev ];
    -- Substitute $X = t • (C -ᵥ A) +ᵥ A$ into the distance equations.
    have h_dist_eq_subst : ‖t • (C -ᵥ A) +ᵥ A -ᵥ O₁‖ ^ 2 = ‖A -ᵥ O₁‖ ^ 2 ∧ ‖t • (C -ᵥ A) +ᵥ A -ᵥ O₁‖ ^ 2 = ‖C -ᵥ O₁‖ ^ 2 := by
      simp_all +decide [ dist_eq_norm_vsub', norm_sub_rev ];
      convert h_dist_eq.2.2.2 using 1;
      · simp +decide [ vadd_vsub_assoc ];
      · linarith;
    have h_dist_eq_subst : t * (t - 1) * ‖C -ᵥ A‖ ^ 2 = 0 := by
      have h_t_eq_zero_or_one : ‖t • (C -ᵥ A) +ᵥ A -ᵥ O₁‖ ^ 2 = t ^ 2 * ‖C -ᵥ A‖ ^ 2 + 2 * t * inner ℝ (C -ᵥ A) (A -ᵥ O₁) + ‖A -ᵥ O₁‖ ^ 2 := by
        rw [ show t • ( C -ᵥ A ) +ᵥ A -ᵥ O₁ = t • ( C -ᵥ A ) + ( A -ᵥ O₁ ) by simp +decide [ vadd_vsub_assoc ] ] ; rw [ @norm_add_sq ℝ ] ; simp +decide [ inner_smul_left, inner_smul_right ] ; ring;
        rw [ norm_smul, mul_pow, Real.norm_eq_abs, sq_abs ] ; ring;
      have h_t_eq_zero_or_one : ‖C -ᵥ O₁‖ ^ 2 = ‖C -ᵥ A‖ ^ 2 + 2 * inner ℝ (C -ᵥ A) (A -ᵥ O₁) + ‖A -ᵥ O₁‖ ^ 2 := by
        rw [ show C -ᵥ O₁ = ( C -ᵥ A ) + ( A -ᵥ O₁ ) by rw [ vsub_add_vsub_cancel ], norm_add_sq_real ];
      grind;
    simp_all +decide [ sub_eq_iff_eq_add ];
    rcases h_dist_eq_subst with ( ( rfl | rfl ) | rfl ) <;> simp +decide;
  rcases h_X_eq_A_or_C with ( rfl | rfl ) <;> simp_all +decide [ dist_comm ]

/-- The concurrency of BC, EF, and O₁O₂ in the IMO 2021 P3 configuration. -/
theorem imo2021_p3_concurrent {A B C D E F X O₁ O₂ : P}
    (affineIndependent_ABC : AffineIndependent ℝ ![A, B, C])
    (acuteAngled_ABC : (⟨_, affineIndependent_ABC⟩ : Triangle ℝ P).AcuteAngled)
    (AC_lt_AB : dist A C < dist A B)
    (D_mem_interior_ABC : D ∈ (⟨_, affineIndependent_ABC⟩ : Triangle ℝ P).interior)
    (angle_DAB_eq_angle_CAD : ∠ D A B = ∠ C A D) (wbtw_A_E_C : Wbtw ℝ A E C)
    (angle_ADE_eq_angle_BCD : ∠ A D E = ∠ B C D) (wbtw_A_F_B : Wbtw ℝ A F B)
    (angle_FDA_eq_angle_DBC : ∠ F D A = ∠ D B C) (X_mem_AC : X ∈ line[ℝ, A, C])
    (CX_eq_BX : dist C X = dist B X)
    (affineIndependent_ADC : AffineIndependent ℝ ![A, D, C])
    (O₁_eq_circumcenter_ADC :
      O₁ = (⟨_, affineIndependent_ADC⟩ : Triangle ℝ P).circumcenter)
    (affineIndependent_EXD : AffineIndependent ℝ ![E, X, D])
    (O₂_eq_circumcenter_EXD :
      O₂ = (⟨_, affineIndependent_EXD⟩ : Triangle ℝ P).circumcenter) :
    (line[ℝ, B, C] ∩ line[ℝ, E, F] ∩ line[ℝ, O₁, O₂] : Set P).Nonempty := by
  sorry

theorem imo2021_p3 {A B C D E F X O₁ O₂ : P}
    (affineIndependent_ABC : AffineIndependent ℝ ![A, B, C])
    (acuteAngled_ABC : (⟨_, affineIndependent_ABC⟩ : Triangle ℝ P).AcuteAngled)
    (AC_lt_AB : dist A C < dist A B)
    (D_mem_interior_ABC : D ∈ (⟨_, affineIndependent_ABC⟩ : Triangle ℝ P).interior)
    (angle_DAB_eq_angle_CAD : ∠ D A B = ∠ C A D) (wbtw_A_E_C : Wbtw ℝ A E C)
    (angle_ADE_eq_angle_BCD : ∠ A D E = ∠ B C D) (wbtw_A_F_B : Wbtw ℝ A F B)
    (angle_FDA_eq_angle_DBC : ∠ F D A = ∠ D B C) (X_mem_AC : X ∈ line[ℝ, A, C])
    (CX_eq_BX : dist C X = dist B X)
    (affineIndependent_ADC : AffineIndependent ℝ ![A, D, C])
    (O₁_eq_circumcenter_ADC :
      O₁ = (⟨_, affineIndependent_ADC⟩ : Triangle ℝ P).circumcenter)
    (affineIndependent_EXD : AffineIndependent ℝ ![E, X, D])
    (O₂_eq_circumcenter_EXD :
      O₂ = (⟨_, affineIndependent_EXD⟩ : Triangle ℝ P).circumcenter) :
    E ≠ F ∧ O₁ ≠ O₂ ∧
    (line[ℝ, B, C] ∩ line[ℝ, E, F] ∩ line[ℝ, O₁, O₂] : Set P).Nonempty := by
  exact ⟨imo2021_p3_E_ne_F affineIndependent_ABC acuteAngled_ABC AC_lt_AB D_mem_interior_ABC
      angle_DAB_eq_angle_CAD wbtw_A_E_C angle_ADE_eq_angle_BCD wbtw_A_F_B angle_FDA_eq_angle_DBC,
    imo2021_p3_O_ne affineIndependent_ABC acuteAngled_ABC AC_lt_AB D_mem_interior_ABC
      angle_DAB_eq_angle_CAD wbtw_A_E_C angle_ADE_eq_angle_BCD wbtw_A_F_B angle_FDA_eq_angle_DBC
      X_mem_AC CX_eq_BX affineIndependent_ADC O₁_eq_circumcenter_ADC affineIndependent_EXD
      O₂_eq_circumcenter_EXD,
    imo2021_p3_concurrent affineIndependent_ABC acuteAngled_ABC AC_lt_AB D_mem_interior_ABC
      angle_DAB_eq_angle_CAD wbtw_A_E_C angle_ADE_eq_angle_BCD wbtw_A_F_B angle_FDA_eq_angle_DBC
      X_mem_AC CX_eq_BX affineIndependent_ADC O₁_eq_circumcenter_ADC affineIndependent_EXD
      O₂_eq_circumcenter_EXD⟩

end Imo2021P3