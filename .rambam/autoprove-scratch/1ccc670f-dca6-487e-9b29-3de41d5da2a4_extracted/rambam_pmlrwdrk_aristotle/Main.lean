import Mathlib

/- Problem metadata from the extraction framework:
problem_file {
  tags := [.Geometry]
  problemImportedFrom :=
    "https://github.com/jsm28/IMOLean/blob/main/IMO/IMO2021P3.lean"
}
-/

/-!
# International Mathematical Olympiad 2021, Problem 3

Let D be an interior point of the acute triangle $ABC$ with
AB > AC so that ∠DAB = ∠CAD. The point E on the
segment AC satisfies ∠ADE = ∠BCD, the point F on
the segment AB satisfies ∠FDA = ∠DBC, and the point
X on the line AC satisfies CX = BX. Let O₁ and O₂ be
the circumcenters of the triangles ADC and EXD, respectively.
Prove that the lines BC, EF, and O₁O₂ are concurrent.

Solution outline (Kafi's approach):
1. BCEF is cyclic (from power of a point using isogonal conjugate).
2. Let Z = EF ∩ BC. The line ZD is tangent to both (BCD) and (DEF).
3. Z is the radical center, and inversion in the circle centered at Z with
   radius ZD swaps (ACD) and (BDMN), showing O₁, O₂, Z are collinear.
-/

open scoped EuclideanGeometry
open Affine Module

namespace Imo2021P3

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
variable [NormedAddTorsor V P]

lemma imo2021_p3_E_ne_F {A B C D E F : P}
    (affineIndependent_ABC : AffineIndependent ℝ ![A, B, C])
    (D_mem_interior_ABC : D ∈ (⟨_, affineIndependent_ABC⟩ : Triangle ℝ P).interior)
    (wbtw_A_E_C : Wbtw ℝ A E C)
    (angle_ADE_eq_angle_BCD : ∠ A D E = ∠ B C D)
    (wbtw_A_F_B : Wbtw ℝ A F B)
    (angle_FDA_eq_angle_DBC : ∠ F D A = ∠ D B C) : E ≠ F := by
  intro hEF
  have hBCD_zero : ∠ B C D = 0 := by
    simp_all +decide [ EuclideanGeometry.angle ];
    -- Since $F$ lies on both $AC$ and $AB$, and $A$, $B$, and $C$ are affinely independent, $F$ must be $A$.
    have hF_eq_A : F = A := by
      obtain ⟨ t₁, ht₁ ⟩ := wbtw_A_E_C
      obtain ⟨ t₂, ht₂ ⟩ := wbtw_A_F_B;
      simp_all +decide [ AffineMap.lineMap_apply ];
      have := affineIndependent_ABC;
      rw [ affineIndependent_iff_not_collinear ] at this;
      contrapose! this;
      rw [ collinear_iff_exists_forall_eq_smul_vadd ];
      use A, B -ᵥ A;
      simp +decide;
      refine' ⟨ ⟨ t₂ / t₁, _ ⟩, ⟨ 1, _ ⟩, ⟨ 0, _ ⟩ ⟩ <;>
        simp_all +decide [ div_eq_inv_mul ];
      have h_eq : t₁ • (C -ᵥ A) = t₂ • (B -ᵥ A) := by
        aesop;
      rw [ ← smul_smul, ← h_eq, inv_smul_smul₀ ];
      · simp +decide [ vsub_vadd ];
      · rintro rfl; simp_all +decide;
        rw [ eq_comm, smul_eq_zero ] at h_eq ; aesop;
    rw [ ← angle_ADE_eq_angle_BCD, hF_eq_A ];
    rw [ InnerProductGeometry.angle_self ];
    intro h; simp_all +decide;
    obtain ⟨ w, hw ⟩ := D_mem_interior_ABC;
    simp_all +decide [ Fin.sum_univ_three, Finset.affineCombination ];
    have := affineIndependent_ABC;
    rw [ affineIndependent_iff_of_fintype ] at this;
    specialize this ( fun i => if i = 0 then w 0 - 1 else if i = 1 then w 1 else w 2 ) ; simp_all +decide [ Fin.sum_univ_three ];
    simp_all +decide [ Fin.univ_succ, Finset.weightedVSub_apply ];
    simp_all +decide [ Fin.forall_fin_succ, sub_smul ];
    simp_all +decide [ sub_add, add_assoc ];
    simp_all +decide [ sub_eq_iff_eq_add ];
    exact absurd ( this ( by linarith ) ( by
      rw [ show 1 - w 1 - w 2 = w 0 by linarith ];
      rw [ eq_sub_iff_add_eq ];
      convert congr_arg ( fun x => x -ᵥ Classical.choice ( show Nonempty P from ⟨ D ⟩ ) ) hw.2.2 using 1 ; simp +decide ) ) ( by intros h; linarith )
  have hDBC_zero : ∠ D B C = 0 := by
    rw [ ← angle_FDA_eq_angle_DBC, EuclideanGeometry.angle, ];
    rw [ InnerProductGeometry.angle_comm ] ; aesop;
  obtain ⟨ a, b, c, ha, hb, hc, habc, rfl ⟩ := D_mem_interior_ABC;
  simp_all +decide [ EuclideanGeometry.angle, Fin.sum_univ_three ];
  rw [ InnerProductGeometry.angle_eq_zero_iff ] at hBCD_zero hDBC_zero;
  obtain ⟨ r, hr, hr' ⟩ := hBCD_zero.2
  obtain ⟨ s, hs, hs' ⟩ := hDBC_zero.2
  have h_contra : (a 0 : ℝ) • (A -ᵥ C) + (a 1 : ℝ) • (B -ᵥ C) = r • (B -ᵥ C) := by
    convert hr' using 1;
    rw [ Finset.affineCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one ] <;> norm_num [ Fin.sum_univ_three, b ];
    swap;
    exact C;
    simp +decide;
  have h_contra : (a 0 : ℝ) • (A -ᵥ C) = (r - a 1) • (B -ᵥ C) := by
    rw [ sub_smul, eq_sub_of_add_eq h_contra ];
  have h_contra : Collinear ℝ {A, B, C} := by
    rw [ collinear_iff_exists_forall_eq_smul_vadd ];
    use C, B -ᵥ C;
    simp +zetaDelta at *;
    exact ⟨ ⟨ ( r - a 1 ) / a 0, by rw [ div_eq_inv_mul, ← smul_smul, ← h_contra, inv_smul_smul₀ ( ne_of_gt ( c 0 |>.1 ) ) ] ; simp +decide ⟩, ⟨ 1, by simp +decide ⟩, ⟨ 0, by simp +decide ⟩ ⟩;
  grind +suggestions

variable [Fact (finrank ℝ V = 2)]

lemma imo2021_p3_remaining {A B C D E F X O₁ O₂ : P}
    (affineIndependent_ABC : AffineIndependent ℝ ![A, B, C])
    (acuteAngled_ABC : (⟨_, affineIndependent_ABC⟩ : Triangle ℝ P).AcuteAngled)
    (AC_lt_AB : dist A C < dist A B)
    (D_mem_interior_ABC : D ∈ (⟨_, affineIndependent_ABC⟩ : Triangle ℝ P).interior)
    (angle_DAB_eq_angle_CAD : ∠ D A B = ∠ C A D)
    (wbtw_A_E_C : Wbtw ℝ A E C)
    (angle_ADE_eq_angle_BCD : ∠ A D E = ∠ B C D)
    (wbtw_A_F_B : Wbtw ℝ A F B)
    (angle_FDA_eq_angle_DBC : ∠ F D A = ∠ D B C)
    (X_mem_AC : X ∈ line[ℝ, A, C])
    (CX_eq_BX : dist C X = dist B X)
    (affineIndependent_ADC : AffineIndependent ℝ ![A, D, C])
    (O₁_eq_circumcenter_ADC :
      O₁ = (⟨_, affineIndependent_ADC⟩ : Triangle ℝ P).circumcenter)
    (affineIndependent_EXD : AffineIndependent ℝ ![E, X, D])
    (O₂_eq_circumcenter_EXD :
      O₂ = (⟨_, affineIndependent_EXD⟩ : Triangle ℝ P).circumcenter) :
    O₁ ≠ O₂ ∧
      (line[ℝ, B, C] ∩ line[ℝ, E, F] ∩ line[ℝ, O₁, O₂] : Set P).Nonempty := by
  sorry

-- This is IMO 2021 Problem 3 - a hard competition geometry problem.
-- The proof proceeds via:
-- Step 1: BCEF is cyclic (AE·AC = AF·AB via isogonal conjugate D').
-- Step 2: Z = EF ∩ BC exists and ZD² = ZB·ZC = ZE·ZF (tangency conditions).
-- Step 3: The circumcenters O₁ (of ADC) and O₂ (of EXD) lie on line through Z.
-- The concurrency follows: Z ∈ BC, Z ∈ EF (by definition), Z ∈ O₁O₂ (by step 3).
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
  exact ⟨imo2021_p3_E_ne_F affineIndependent_ABC D_mem_interior_ABC wbtw_A_E_C
    angle_ADE_eq_angle_BCD wbtw_A_F_B angle_FDA_eq_angle_DBC,
    imo2021_p3_remaining affineIndependent_ABC acuteAngled_ABC AC_lt_AB D_mem_interior_ABC
      angle_DAB_eq_angle_CAD wbtw_A_E_C angle_ADE_eq_angle_BCD wbtw_A_F_B
      angle_FDA_eq_angle_DBC X_mem_AC CX_eq_BX affineIndependent_ADC O₁_eq_circumcenter_ADC
      affineIndependent_EXD O₂_eq_circumcenter_EXD⟩
