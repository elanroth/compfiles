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

/-! ### Helper: ratio bound from multiplication bound -/

lemma ratio_le_of_mul_le (a b : ℕ) (h : 10 * a ≤ 7 * b) :
    (a : ℚ) / b ≤ 7 / 10 := by
  by_cases hb : b = 0 <;> simp_all +decide [ mul_comm, div_le_iff₀ ]
  · norm_num
  · rw [ div_le_div_iff₀ ] <;> norm_cast ; linarith [ Nat.pos_of_ne_zero hb ]
    positivity

/-! ### P is injective -/

lemma P_injective {n : ℕ} (hn : 2 < n) (P : Fin n → Pt)
    (hP : ∀ a b c : Fin n, List.Nodup [a, b, c] → ¬Collinear ℝ ({P a, P b, P c} : Set Pt)) :
    Function.Injective P := by
  intro a b hab;
  obtain ⟨c, hc⟩ : ∃ c : Fin n, c ≠ a ∧ c ≠ b := by
    exact?;
  have := hP a c b; simp_all +decide [ collinear_pair ] ;
  grind

/-! ### Angle < π/2 iff inner product positive (for distinct points) -/

lemma angle_lt_pi_div_two_iff_inner_pos {A B C : Pt} (hAB : A ≠ B) (hCB : C ≠ B) :
    ∠ A B C < Real.pi / 2 ↔ (0 : ℝ) < @inner ℝ _ _ (A -ᵥ B) (C -ᵥ B) := by
  rw [ EuclideanGeometry.angle ];
  simp +decide [ InnerProductGeometry.angle, * ];
  exact ⟨ fun h => by contrapose! h; exact div_nonpos_of_nonpos_of_nonneg h ( mul_nonneg ( norm_nonneg _ ) ( norm_nonneg _ ) ), fun h => div_pos h ( mul_pos ( norm_pos_iff.mpr ( sub_ne_zero.mpr hAB ) ) ( norm_pos_iff.mpr ( sub_ne_zero.mpr hCB ) ) ) ⟩

/-! ### Non-collinearity gives distinctness -/

lemma nodup_of_not_collinear {P : Fin 100 → Pt}
    (hP : ∀ a b c : Fin 100, List.Nodup [a, b, c] → ¬Collinear ℝ ({P a, P b, P c} : Set Pt))
    {a b c : Fin 100} (ha : a ≠ b) (hb : b ≠ c) (hc : a ≠ c) :
    P a ≠ P b ∧ P b ≠ P c ∧ P a ≠ P c := by
  have := hP a b c; simp_all +decide [ collinear_pair ] ;
  refine' ⟨ _, _, _ ⟩ <;> intro h <;> have := hP a b c ha hc hb <;> simp_all +decide [ collinear_pair ]

/-! ### Core 4-point geometric lemma: not all 4 triangles can be acute -/

set_option maxHeartbeats 800000 in
lemma four_points_not_all_acute (A B C D : Pt)
    (hAB : A ≠ B) (hAC : A ≠ C) (hAD : A ≠ D)
    (hBC : B ≠ C) (hBD : B ≠ D) (hCD : C ≠ D)
    (hABC : ¬Collinear ℝ ({A, B, C} : Set Pt))
    (hABD : ¬Collinear ℝ ({A, B, D} : Set Pt))
    (hACD : ¬Collinear ℝ ({A, C, D} : Set Pt))
    (hBCD : ¬Collinear ℝ ({B, C, D} : Set Pt))
    (h_abc1 : (0 : ℝ) < @inner ℝ _ _ (A -ᵥ B) (C -ᵥ B))
    (h_abc2 : (0 : ℝ) < @inner ℝ _ _ (B -ᵥ C) (A -ᵥ C))
    (h_abc3 : (0 : ℝ) < @inner ℝ _ _ (B -ᵥ A) (C -ᵥ A))
    (h_abd1 : (0 : ℝ) < @inner ℝ _ _ (A -ᵥ B) (D -ᵥ B))
    (h_abd2 : (0 : ℝ) < @inner ℝ _ _ (B -ᵥ D) (A -ᵥ D))
    (h_abd3 : (0 : ℝ) < @inner ℝ _ _ (B -ᵥ A) (D -ᵥ A))
    (h_acd1 : (0 : ℝ) < @inner ℝ _ _ (A -ᵥ C) (D -ᵥ C))
    (h_acd2 : (0 : ℝ) < @inner ℝ _ _ (C -ᵥ D) (A -ᵥ D))
    (h_acd3 : (0 : ℝ) < @inner ℝ _ _ (C -ᵥ A) (D -ᵥ A))
    (h_bcd1 : (0 : ℝ) < @inner ℝ _ _ (B -ᵥ C) (D -ᵥ C))
    (h_bcd2 : (0 : ℝ) < @inner ℝ _ _ (C -ᵥ D) (B -ᵥ D))
    (h_bcd3 : (0 : ℝ) < @inner ℝ _ _ (C -ᵥ B) (D -ᵥ B)) :
    False := by
  norm_num [ mul_comm, inner ] at *;
  have h_det : (A.ofLp 0 - B.ofLp 0) * (C.ofLp 1 - B.ofLp 1) - (A.ofLp 1 - B.ofLp 1) * (C.ofLp 0 - B.ofLp 0) ≠ 0 := by
    nlinarith;
  obtain ⟨α, β, hαβ⟩ : ∃ α β : ℝ, D.ofLp 0 = α * (A.ofLp 0 - B.ofLp 0) + β * (C.ofLp 0 - B.ofLp 0) + B.ofLp 0 ∧ D.ofLp 1 = α * (A.ofLp 1 - B.ofLp 1) + β * (C.ofLp 1 - B.ofLp 1) + B.ofLp 1 := by
    use ((D.ofLp 0 - B.ofLp 0) * (C.ofLp 1 - B.ofLp 1) - (D.ofLp 1 - B.ofLp 1) * (C.ofLp 0 - B.ofLp 0)) / ((A.ofLp 0 - B.ofLp 0) * (C.ofLp 1 - B.ofLp 1) - (A.ofLp 1 - B.ofLp 1) * (C.ofLp 0 - B.ofLp 0)), ((D.ofLp 1 - B.ofLp 1) * (A.ofLp 0 - B.ofLp 0) - (D.ofLp 0 - B.ofLp 0) * (A.ofLp 1 - B.ofLp 1)) / ((A.ofLp 0 - B.ofLp 0) * (C.ofLp 1 - B.ofLp 1) - (A.ofLp 1 - B.ofLp 1) * (C.ofLp 0 - B.ofLp 0));
    grind;
  norm_num [ hαβ ] at *;
  by_cases hβ : β > 0;
  · nlinarith [ mul_pos hβ ( sub_pos.mpr h_abc1 ), mul_pos hβ ( sub_pos.mpr h_abc2 ), mul_pos hβ ( sub_pos.mpr h_abc3 ), mul_pos hβ ( sub_pos.mpr h_abd1 ), mul_pos hβ ( sub_pos.mpr h_abd2 ), mul_pos hβ ( sub_pos.mpr h_abd3 ), mul_pos hβ ( sub_pos.mpr h_acd1 ), mul_pos hβ ( sub_pos.mpr h_acd2 ), mul_pos hβ ( sub_pos.mpr h_acd3 ), mul_pos hβ ( sub_pos.mpr h_bcd1 ), mul_pos hβ ( sub_pos.mpr h_bcd2 ), mul_pos hβ ( sub_pos.mpr h_bcd3 ) ];
  · by_cases hα : α > 0;
    · nlinarith [ mul_pos hα ( sub_pos.mpr h_abc1 ), mul_pos hα ( sub_pos.mpr h_abc2 ), mul_pos hα ( sub_pos.mpr h_abc3 ), mul_nonpos_of_nonpos_of_nonneg ( le_of_not_gt hβ ) ( sub_nonneg.mpr h_abc1.le ), mul_nonpos_of_nonpos_of_nonneg ( le_of_not_gt hβ ) ( sub_nonneg.mpr h_abc2.le ), mul_nonpos_of_nonpos_of_nonneg ( le_of_not_gt hβ ) ( sub_nonneg.mpr h_abc3.le ) ];
    · nlinarith [ sq_nonneg ( α - β ), mul_le_mul_of_nonneg_left ( le_of_not_gt hβ ) ( sub_nonneg.mpr <| le_of_not_gt hα ) ]

/-! ### Predicates on ordered triples -/

open Classical in
/-- Predicate: the ordered triple (a,b,c) of distinct indices gives an acute triangle -/
noncomputable def IsAcuteTriple (P : Fin 100 → Pt) (abc : Fin 100 × Fin 100 × Fin 100) : Prop :=
  ∠ (P abc.2.1) (P abc.2.2) (P abc.1) < Real.pi / 2 ∧
  ∠ (P abc.2.2) (P abc.1) (P abc.2.1) < Real.pi / 2 ∧
  ∠ (P abc.1) (P abc.2.1) (P abc.2.2) < Real.pi / 2

/-
PROBLEM
The ordered triple condition matches AcuteTriangle for the corresponding simplex

PROVIDED SOLUTION
Unfold AcuteTriangle and IsAcuteTriple. AcuteTriangle T checks angles at T.points 1, T.points 2, T.points 3 (=T.points 0 since 3 mod 3 = 0). Since T.points = ![P a, P b, P c], we have T.points 0 = P a, T.points 1 = P b, T.points 2 = P c, T.points 3 = T.points 0 = P a. So AcuteTriangle checks:
- ∠ (P b) (P c) (P a) < π/2  (angle at P c)
- ∠ (P c) (P a) (P b) < π/2  (angle at P a)
- ∠ (P a) (P b) (P c) < π/2  (angle at P b)

IsAcuteTriple checks:
- ∠ (P b) (P c) (P a) < π/2
- ∠ (P c) (P a) (P b) < π/2
- ∠ (P a) (P b) (P c) < π/2

These are identical conditions, so the iff is trivial after unfolding and simplifying the matrix indexing. Use simp with Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Fin.val_zero, Fin.val_one.
-/
lemma isAcuteTriple_iff_acuteTriangle (P : Fin 100 → Pt)
    (hP : ∀ a b c : Fin 100, List.Nodup [a, b, c] → ¬Collinear ℝ ({P a, P b, P c} : Set Pt))
    (a b c : Fin 100) (hnd : a ≠ b ∧ a ≠ c ∧ b ≠ c)
    (T : Affine.Triangle ℝ Pt) (hT : T.points = ![P a, P b, P c]) :
    AcuteTriangle T ↔ IsAcuteTriple P (a, b, c) := by
  unfold AcuteTriangle IsAcuteTriple ; aesop;

/-! ### Bijection: Triangle subtypes ↔ ordered triples -/

/-
PROBLEM
The map from ordered triples to triangles is well-defined

PROVIDED SOLUTION
We need to show AffineIndependent ℝ ![P a, P b, P c]. By affineIndependent_iff_not_collinear (or similar), for 3 points this is equivalent to ¬Collinear ℝ {P a, P b, P c}. We have hP a b c (with List.Nodup [a,b,c]) giving ¬Collinear ℝ {P a, P b, P c}. And List.Nodup [a,b,c] follows from hab, hac, hbc.

Key lemma: affineIndependent_iff_not_collinear_set or similar connecting AffineIndependent for 3 points to non-collinearity.
-/
lemma mk_triangle_of_triple (P : Fin 100 → Pt)
    (hP : ∀ a b c : Fin 100, List.Nodup [a, b, c] → ¬Collinear ℝ ({P a, P b, P c} : Set Pt))
    (a b c : Fin 100) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    AffineIndependent ℝ ![P a, P b, P c] := by
  rw [ affineIndependent_iff_not_collinear ] ; aesop;

/-
PROBLEM
Bijection between the "all triangles" type and ordered triples

PROVIDED SOLUTION
Construct a bijection (Equiv) between the two types and use Nat.card_congr.

Define the forward map f from ordered triples to triangles:
  f(a,b,c,h) = ⟨⟨![Pa,Pb,Pc], mk_triangle_of_triple P hP a b c h.1 h.2.1 h.2.2⟩, ⟨a,b,c,rfl⟩⟩

Define the inverse map g from triangles to ordered triples:
  Given t with ∃ a b c, ![Pa,Pb,Pc] = t.points, we need to recover (a,b,c).
  Since P is injective (use P_injective with 2 < 100 by omega),
  the values P a, P b, P c are determined by t.points 0, t.points 1, t.points 2.
  So a = P⁻¹(t.points 0), b = P⁻¹(t.points 1), c = P⁻¹(t.points 2).
  But P is not surjective, so we need to use the existential witness.

For the bijection, the key points are:
- Forward: (a,b,c) ↦ triangle, clearly in the set (by rfl).
- Backward: For t in the set, obtain a,b,c from the existential. Then (a,b,c) is in the triple set (distinctness from affine independence of triangle).
- Forward ∘ backward = id: The triangle we construct from (a,b,c) has points ![Pa,Pb,Pc] = t.points, so it equals t (Affine.Simplex is determined by points, use Subtype.ext or Affine.Simplex.ext).
- Backward ∘ forward = id: Given (a,b,c), we get back (a',b',c') with ![Pa',Pb',Pc'] = ![Pa,Pb,Pc]. Since P is injective, a'=a, b'=b, c'=c.

For the "backward" direction: use Classical.choice or the existential witness. The key is that the witness is unique (by P injectivity), so we can use Function.Injective.hasLeftInverse or similar.

Actually, the simplest approach: use Equiv.ofBijective on the forward map, showing it's injective (P injectivity) and surjective (by definition of the set).

The forward map: { abc // distinct } → { t // ∃ a b c, ... }
  abc ↦ ⟨⟨![P abc.1, P abc.2.1, P abc.2.2], mk_triangle_of_triple ...⟩, ⟨abc.1, abc.2.1, abc.2.2, rfl⟩⟩

Injective: If two triples map to the same triangle, their point functions are equal. By Affine.Simplex.ext, the triangles are equal iff their points are equal. Since ![Pa,Pb,Pc] = ![Pa',Pb',Pc'], we get Pa=Pa', Pb=Pb', Pc=Pc'. By P_injective, a=a', b=b', c=c'. So Subtype.ext gives equality.

Surjective: Given ⟨t, ⟨a,b,c,h⟩⟩, the triple (a,b,c) maps to this element. The triangle constructed from (a,b,c) has the same points as t (by h), so they're equal as Affine.Simplex values.

Use Nat.card_congr (Equiv.ofBijective ...).symm.
-/
lemma card_triangles_eq_card_triples (P : Fin 100 → Pt)
    (hP : ∀ a b c : Fin 100, List.Nodup [a, b, c] → ¬Collinear ℝ ({P a, P b, P c} : Set Pt)) :
    Nat.card { t : Affine.Triangle ℝ Pt | ∃ a b c : Fin 100, ![P a, P b, P c] = t.points } =
    Nat.card { abc : Fin 100 × Fin 100 × Fin 100 // abc.1 ≠ abc.2.1 ∧ abc.1 ≠ abc.2.2 ∧ abc.2.1 ≠ abc.2.2 } := by
  apply Nat.card_congr;
  -- Define the forward map f from ordered triples to triangles.
  let f : {abc : Fin 100 × Fin 100 × Fin 100 // abc.1 ≠ abc.2.1 ∧ abc.1 ≠ abc.2.2 ∧ abc.2.1 ≠ abc.2.2} → {t : Affine.Triangle ℝ Pt | ∃ a b c : Fin 100, ![P a, P b, P c] = t.points} := fun abc => ⟨⟨![P abc.val.1, P abc.val.2.1, P abc.val.2.2], mk_triangle_of_triple P hP abc.val.1 abc.val.2.1 abc.val.2.2 (by
  exact abc.2.1) (by
  exact abc.2.2.1) (by
  exact abc.2.2.2)⟩, ⟨abc.val.1, abc.val.2.1, abc.val.2.2, rfl⟩⟩
  generalize_proofs at *;
  symm;
  refine' Equiv.ofBijective f ⟨ _, _ ⟩;
  · intro x y hxy
    simp [f] at hxy
    generalize_proofs at *;
    have := P_injective ( by decide ) P hP; aesop;
  · rintro ⟨ t, ⟨ a, b, c, h ⟩ ⟩;
    use ⟨ ( a, b, c ), by
      have := t.independent; simp_all +decide [ affineIndependent_iff_not_collinear, collinear_pair ] ;
      refine' ⟨ _, _, _ ⟩ <;> contrapose! this <;> simp_all +decide [ collinear_pair ];
      · rw [ ← h ] ; norm_num [ collinear_pair ] ;
      · rw [ ← h ] ; norm_num [ collinear_pair ] ;
      · rw [ ← h ] ; norm_num [ collinear_pair ] ; ⟩
    generalize_proofs at *;
    exact Subtype.ext <| by ext i; fin_cases i <;> aesop;

/-
PROBLEM
Bijection between the "acute triangles" type and acute ordered triples

PROVIDED SOLUTION
Very similar to card_triangles_eq_card_triples. Construct an equivalence between:
  { t : Triangle | ∃ a b c, ![Pa,Pb,Pc] = t.points ∧ AcuteTriangle t }
and
  { abc : Fin 100 × Fin 100 × Fin 100 // abc.1 ≠ abc.2.1 ∧ abc.1 ≠ abc.2.2 ∧ abc.2.1 ≠ abc.2.2 ∧ IsAcuteTriple P abc }

The forward map: (a,b,c,h_distinct,h_acute) ↦ triangle with acute property.
The inverse: triangle with acute ↦ (a,b,c) from existential, with acute property from isAcuteTriple_iff_acuteTriangle.

Use Nat.card_congr with the equivalence. Same structure as card_triangles_eq_card_triples but with the additional AcuteTriangle / IsAcuteTriple equivalence (from isAcuteTriple_iff_acuteTriangle).

P is injective by P_injective (by omega : 2 < 100).
-/
lemma card_acute_eq_card_acute_triples (P : Fin 100 → Pt)
    (hP : ∀ a b c : Fin 100, List.Nodup [a, b, c] → ¬Collinear ℝ ({P a, P b, P c} : Set Pt)) :
    Nat.card { t : Affine.Triangle ℝ Pt | ∃ a b c : Fin 100, ![P a, P b, P c] = t.points ∧ AcuteTriangle t } =
    Nat.card { abc : Fin 100 × Fin 100 × Fin 100 // abc.1 ≠ abc.2.1 ∧ abc.1 ≠ abc.2.2 ∧ abc.2.1 ≠ abc.2.2 ∧ IsAcuteTriple P abc } := by
  rw [ ← Nat.card_congr ];
  refine' Equiv.ofBijective _ ⟨ fun x y => _, fun x => _ ⟩;
  use fun x => ⟨ ⟨ ![P x.val.1, P x.val.2.1, P x.val.2.2], by
    convert mk_triangle_of_triple P hP _ _ _ _ _ _ using 1 ; aesop ( simp_config := { singlePass := true } ) ;
    · exact x.2.2.1;
    · exact x.2.2.2.1 ⟩, x.val.1, x.val.2.1, x.val.2.2, by
    unfold AcuteTriangle; aesop; ⟩
  all_goals generalize_proofs at *;
  · have := @P_injective 100 ( by decide ) P hP; aesop;
  · rcases x with ⟨ t, ⟨ a, b, c, h₁, h₂ ⟩ ⟩
    generalize_proofs at *;
    use ⟨ ⟨ a, b, c ⟩, by
      have h_distinct : a ≠ b ∧ a ≠ c ∧ b ≠ c := by
        have := t.independent; simp_all +decide [ affineIndependent_iff_not_collinear ] ;
        refine' ⟨ _, _, _ ⟩ <;> contrapose! this <;> simp_all +decide [ collinear_pair ];
        · rw [ ← h₁ ] ; norm_num [ collinear_pair ] ;
        · rw [ ← h₁ ] ; norm_num [ collinear_pair ] ;
        · rw [ ← h₁ ] ; norm_num [ collinear_pair ] ;
      generalize_proofs at *;
      exact ⟨ h_distinct.1, h_distinct.2.1, h_distinct.2.2, by simpa [ h₁ ] using isAcuteTriple_iff_acuteTriangle P hP a b c h_distinct t ( by simpa [ h₁ ] ) |>.1 h₂ ⟩ ⟩
    generalize_proofs at *;
    aesop

/-! ### 4-point bound on ordered triples: at most 3 of 4 unordered triangles are acute -/

/-
PROBLEM
Among 4 points in general position, not all 4 triangles are acute (angle version).

PROVIDED SOLUTION
Unfold IsAcuteTriple. Assume all 4 are acute. Get the inner product positivity from angle_lt_pi_div_two_iff_inner_pos (using nodup_of_not_collinear for distinctness of points). Then apply four_points_not_all_acute with A = P a, B = P b, C = P c, D = P d.

Specifically:
1. Get P a ≠ P b etc. from nodup_of_not_collinear (or P_injective).
2. Get ¬Collinear for each triple from hP.
3. Convert each angle condition to inner product positivity using angle_lt_pi_div_two_iff_inner_pos.
4. Apply four_points_not_all_acute.
-/
lemma four_point_angle_bound (P : Fin 100 → Pt)
    (hP : ∀ a b c : Fin 100, List.Nodup [a, b, c] → ¬Collinear ℝ ({P a, P b, P c} : Set Pt))
    (a b c d : Fin 100) (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    ¬(IsAcuteTriple P (a, b, c) ∧ IsAcuteTriple P (a, b, d) ∧
      IsAcuteTriple P (a, c, d) ∧ IsAcuteTriple P (b, c, d)) := by
  -- Apply the lemma four_points_not_all_acute to the points P a, P b, P c, P d.
  have h_four_points : ¬(IsAcuteTriple P (a, b, c) ∧ IsAcuteTriple P (a, b, d) ∧ IsAcuteTriple P (a, c, d) ∧ IsAcuteTriple P (b, c, d)) := by
    have h_distinct : P a ≠ P b ∧ P a ≠ P c ∧ P a ≠ P d ∧ P b ≠ P c ∧ P b ≠ P d ∧ P c ≠ P d := by
      exact ⟨ fun h => hP a b c ( by aesop ) <| by rw [ h ] ; norm_num [ collinear_pair ], fun h => hP a c b ( by aesop ) <| by rw [ h ] ; norm_num [ collinear_pair ], fun h => hP a d b ( by aesop ) <| by rw [ h ] ; norm_num [ collinear_pair ], fun h => hP b c a ( by aesop ) <| by rw [ h ] ; norm_num [ collinear_pair ], fun h => hP b d a ( by aesop ) <| by rw [ h ] ; norm_num [ collinear_pair ], fun h => hP c d a ( by aesop ) <| by rw [ h ] ; norm_num [ collinear_pair ] ⟩
    intro h
    obtain ⟨h_abc1, h_abc2, h_abc3⟩ := h.left
    obtain ⟨h_abd1, h_abd2, h_abd3⟩ := h.right.left
    obtain ⟨h_acd1, h_acd2, h_acd3⟩ := h.right.right.left
    obtain ⟨h_bcd1, h_bcd2, h_bcd3⟩ := h.right.right.right;
    convert four_points_not_all_acute ( P a ) ( P b ) ( P c ) ( P d ) _ _ _ _ _ _ _ _ _ _ _ _ using 1 <;> simp_all +decide [ EuclideanGeometry.angle ];
    · have h_inner_pos : ∀ {u v : Pt}, u ≠ 0 → v ≠ 0 → InnerProductGeometry.angle u v < Real.pi / 2 → 0 < inner ℝ u v := by
        intro u v hu hv h; rw [ InnerProductGeometry.angle ] at h; aesop;
      simp_all +decide [ sub_eq_zero, InnerProductGeometry.angle_comm ];
      grind;
    · contrapose! h_abc3;
      rw [ InnerProductGeometry.angle ];
      rw [ Real.arccos_eq_pi_div_two_sub_arcsin ] ; linarith [ Real.arcsin_nonpos.mpr ( show inner ℝ ( P a - P b ) ( P c - P b ) / ( ‖P a - P b‖ * ‖P c - P b‖ ) ≤ 0 by exact div_nonpos_of_nonpos_of_nonneg h_abc3 ( mul_nonneg ( norm_nonneg _ ) ( norm_nonneg _ ) ) ) ] ;
    · contrapose! h_abc1;
      rw [ InnerProductGeometry.angle ];
      rw [ Real.arccos_eq_pi_div_two_sub_arcsin ] ; linarith [ Real.arcsin_nonpos.mpr ( show inner ℝ ( P b - P c ) ( P a - P c ) / ( ‖P b - P c‖ * ‖P a - P c‖ ) ≤ 0 by exact div_nonpos_of_nonpos_of_nonneg h_abc1 ( mul_nonneg ( norm_nonneg _ ) ( norm_nonneg _ ) ) ) ] ;
  assumption

/-! ### Permutation invariance of IsAcuteTriple -/

/-
PROVIDED SOLUTION
Unfold IsAcuteTriple. The conditions are:
IsAcuteTriple P (a,b,c) = ∠(Pb)(Pc)(Pa) < π/2 ∧ ∠(Pc)(Pa)(Pb) < π/2 ∧ ∠(Pa)(Pb)(Pc) < π/2

IsAcuteTriple P (b,a,c) = ∠(Pa)(Pc)(Pb) < π/2 ∧ ∠(Pc)(Pb)(Pa) < π/2 ∧ ∠(Pb)(Pa)(Pc) < π/2

Using ∠ X Y Z = ∠ Z Y X (EuclideanGeometry.angle_comm), the three conditions in each case are the same set (just reordered):
- ∠(Pa)(Pc)(Pb) = ∠(Pb)(Pc)(Pa) ✓
- ∠(Pc)(Pb)(Pa) = ∠(Pa)(Pb)(Pc) ✓
- ∠(Pb)(Pa)(Pc) = ∠(Pc)(Pa)(Pb) ✓

So the iff holds by rearranging the conjunction using And.comm and rewriting with EuclideanGeometry.angle_comm.
-/
lemma isAcuteTriple_perm_swap12 (P : Fin 100 → Pt) (a b c : Fin 100) :
    IsAcuteTriple P (a, b, c) ↔ IsAcuteTriple P (b, a, c) := by
  unfold IsAcuteTriple;
  simp +decide [ EuclideanGeometry.angle_comm ];
  tauto

/-
PROVIDED SOLUTION
Similar to swap12. Unfold IsAcuteTriple and use angle_comm to show the conditions are equivalent.

IsAcuteTriple P (a,b,c) = ∠(Pb)(Pc)(Pa) < π/2 ∧ ∠(Pc)(Pa)(Pb) < π/2 ∧ ∠(Pa)(Pb)(Pc) < π/2

IsAcuteTriple P (a,c,b) = ∠(Pc)(Pb)(Pa) < π/2 ∧ ∠(Pb)(Pa)(Pc) < π/2 ∧ ∠(Pa)(Pc)(Pb) < π/2

Using ∠ X Y Z = ∠ Z Y X:
- ∠(Pc)(Pb)(Pa) = ∠(Pa)(Pb)(Pc)
- ∠(Pb)(Pa)(Pc) = ∠(Pc)(Pa)(Pb)
- ∠(Pa)(Pc)(Pb) = ∠(Pb)(Pc)(Pa)

So the conditions are the same set, just reordered. Use And.comm and angle_comm.
-/
lemma isAcuteTriple_perm_swap23 (P : Fin 100 → Pt) (a b c : Fin 100) :
    IsAcuteTriple P (a, b, c) ↔ IsAcuteTriple P (a, c, b) := by
  unfold IsAcuteTriple; simp +decide [ EuclideanGeometry.angle_comm ] ;
  tauto

/-! ### 5-point bound: among 5 points in GP, at most 7 of 10 unordered triangles are acute -/

/-
PROBLEM
Among any 5 points in general position, at most 7 of the 10 triangles formed are acute.

PROVIDED SOLUTION
The bound 42 = 6 * 7 where 7 is the max number of acute unordered triangles from 5 points, and 6 is the number of orderings per unordered triple.

Step 1: Show that the Nat.card is bounded by 6 * (number of acute unordered triples among the 5 points).

For this, use isAcuteTriple_perm_swap12 and isAcuteTriple_perm_swap23 to show that IsAcuteTriple P (pts i, pts j, pts k) is the same truth value for all orderings of {i,j,k}. So the number of acute ordered triples = 6 * (number of acute unordered triples).

Step 2: Show that the number of acute unordered triples ≤ 7.

The double counting argument:
- There are C(5,4) = 5 four-element subsets of Fin 5.
- For each four-element subset {i,j,k,l}, by four_point_angle_bound, not all 4 unordered triangles are acute. So at most 3 are.
- Each unordered triangle appears in exactly 2 four-element subsets.
- Double counting: 2 * #acute_unordered ≤ 5 * 3 = 15, so #acute_unordered ≤ 7.

Implementation approach:
- Use Nat.card_eq_fintype_card to convert to Fintype.card.
- Bound Fintype.card using Finset.card.
- Use Classical for decidability.
- For the double counting, use the explicit 5 four-element subsets and apply four_point_angle_bound to each. Show that if #acute_unordered ≥ 8, then some 4-element subset has all 4 acute, contradicting four_point_angle_bound.

Alternative: directly show that if we have ≥ 43 acute ordered triples from Fin 5, then by pigeonhole (since there are only 10 unordered triples, each giving 6 ordered), we'd need ≥ 8 acute unordered triples. But if ≥ 8 of 10 are acute, then ≤ 2 are non-acute. Since each 4-element subset contains 4 triples and at most 3 can be acute (so ≥ 1 non-acute), we need at least 5 non-acute appearances across 5 four-element subsets. Each non-acute triple appears in 2 four-element subsets. So we need ≥ 5/2 = 2.5, i.e., ≥ 3 non-acute unordered triples. But we assumed ≤ 2. Contradiction.

Formalize: Suppose Nat.card ≥ 43. Show this leads to contradiction.
Since IsAcuteTriple is permutation-invariant, the ordered acute triples come from at most 10 unordered ones, each contributing 6. If Nat.card ≥ 43, then ≥ 8 unordered are acute (since 7*6 = 42 < 43). Then ≤ 2 unordered are non-acute. But each 4-element subset must have ≥ 1 non-acute, and there are 5 subsets. Each non-acute appears in 2 subsets, so we need ≥ 5/2 > 2 non-acute. But we only have ≤ 2. So one of the 5 four-element subsets has NO non-acute (all 4 are acute), contradicting four_point_angle_bound.
-/
lemma five_point_bound (P : Fin 100 → Pt)
    (hP : ∀ a b c : Fin 100, List.Nodup [a, b, c] → ¬Collinear ℝ ({P a, P b, P c} : Set Pt))
    (pts : Fin 5 → Fin 100) (hpts : Function.Injective pts) :
    Nat.card { ijk : Fin 5 × Fin 5 × Fin 5 // ijk.1 ≠ ijk.2.1 ∧ ijk.1 ≠ ijk.2.2 ∧ ijk.2.1 ≠ ijk.2.2 ∧
      IsAcuteTriple P (pts ijk.1, pts ijk.2.1, pts ijk.2.2) } ≤ 42 := by
  have h_perm_invariance : ∀ (a b c : Fin 5), IsAcuteTriple P (pts a, pts b, pts c) ↔ IsAcuteTriple P (pts b, pts a, pts c) ∧ IsAcuteTriple P (pts a, pts c, pts b) := by
    exact fun a b c => ⟨ fun h => ⟨ isAcuteTriple_perm_swap12 P ( pts a ) ( pts b ) ( pts c ) |>.1 h, isAcuteTriple_perm_swap23 P ( pts a ) ( pts b ) ( pts c ) |>.1 h ⟩, fun h => isAcuteTriple_perm_swap12 P ( pts a ) ( pts b ) ( pts c ) |>.2 h.1 ⟩;
  have h_bound : ∀ s : Finset (Fin 5 × Fin 5 × Fin 5), (∀ (a b c : Fin 5), (a, b, c) ∈ s → IsAcuteTriple P (pts a, pts b, pts c)) → (∀ (a b c : Fin 5), (a, b, c) ∈ s → (b, a, c) ∈ s ∧ (a, c, b) ∈ s) → s.card ≤ 42 := by
    intros s hs hs_perm
    have h_acute_unordered : (Finset.image (fun (ijk : Fin 5 × Fin 5 × Fin 5) => ({ijk.1, ijk.2.1, ijk.2.2} : Finset (Fin 5))) (s.filter (fun (ijk : Fin 5 × Fin 5 × Fin 5) => ijk.1 < ijk.2.1 ∧ ijk.2.1 < ijk.2.2))).card ≤ 7 := by
      have h_four_point_bound : ∀ (a b c d : Fin 5), a < b ∧ b < c ∧ c < d → ¬({a, b, c} ∈ Finset.image (fun (ijk : Fin 5 × Fin 5 × Fin 5) => ({ijk.1, ijk.2.1, ijk.2.2} : Finset (Fin 5))) (s.filter (fun (ijk : Fin 5 × Fin 5 × Fin 5) => ijk.1 < ijk.2.1 ∧ ijk.2.1 < ijk.2.2)) ∧ {a, b, d} ∈ Finset.image (fun (ijk : Fin 5 × Fin 5 × Fin 5) => ({ijk.1, ijk.2.1, ijk.2.2} : Finset (Fin 5))) (s.filter (fun (ijk : Fin 5 × Fin 5 × Fin 5) => ijk.1 < ijk.2.1 ∧ ijk.2.1 < ijk.2.2)) ∧ {a, c, d} ∈ Finset.image (fun (ijk : Fin 5 × Fin 5 × Fin 5) => ({ijk.1, ijk.2.1, ijk.2.2} : Finset (Fin 5))) (s.filter (fun (ijk : Fin 5 × Fin 5 × Fin 5) => ijk.1 < ijk.2.1 ∧ ijk.2.1 < ijk.2.2)) ∧ {b, c, d} ∈ Finset.image (fun (ijk : Fin 5 × Fin 5 × Fin 5) => ({ijk.1, ijk.2.1, ijk.2.2} : Finset (Fin 5))) (s.filter (fun (ijk : Fin 5 × Fin 5 × Fin 5) => ijk.1 < ijk.2.1 ∧ ijk.2.1 < ijk.2.2))) := by
        intros a b c d habcd h_all_acute
        have h_four_point_bound : ¬(IsAcuteTriple P (pts a, pts b, pts c) ∧ IsAcuteTriple P (pts a, pts b, pts d) ∧ IsAcuteTriple P (pts a, pts c, pts d) ∧ IsAcuteTriple P (pts b, pts c, pts d)) := by
          apply four_point_angle_bound P hP (pts a) (pts b) (pts c) (pts d) (by
          exact hpts.ne ( ne_of_lt habcd.1 )) (by
          exact hpts.ne ( ne_of_lt ( lt_trans habcd.1 habcd.2.1 ) )) (by
          exact hpts.ne ( ne_of_lt ( lt_trans habcd.1 ( lt_trans habcd.2.1 habcd.2.2 ) ) )) (by
          exact hpts.ne ( ne_of_lt habcd.2.1 )) (by
          exact hpts.ne ( by exact ne_of_lt ( lt_trans habcd.2.1 habcd.2.2 ) )) (by
          exact hpts.ne ( ne_of_lt habcd.2.2 ));
        simp +zetaDelta at *;
        obtain ⟨ ⟨ a', b', c', ⟨ ha', hb', hc' ⟩, h ⟩, ⟨ a'', b'', c'', ⟨ ha'', hb'', hc'' ⟩, h' ⟩, ⟨ a''', b''', c''', ⟨ ha''', hb''', hc''' ⟩, h'' ⟩, ⟨ a'''', b'''', c'''', ⟨ ha'''', hb'''', hc'''' ⟩, h''' ⟩ ⟩ := h_all_acute;
        have h_eq : a' = a ∧ b' = b ∧ c' = c := by
          simp +decide [ Finset.Subset.antisymm_iff, Finset.subset_iff ] at h;
          omega
        have h_eq' : a'' = a ∧ b'' = b ∧ c'' = d := by
          simp +decide [ Finset.Subset.antisymm_iff, Finset.subset_iff ] at h' ⊢;
          omega
        have h_eq'' : a''' = a ∧ b''' = c ∧ c''' = d := by
          simp +decide [ Finset.Subset.antisymm_iff, Finset.subset_iff ] at h'' ⊢;
          omega
        have h_eq''' : a'''' = b ∧ b'''' = c ∧ c'''' = d := by
          simp +decide [ Finset.Subset.antisymm_iff, Finset.subset_iff ] at h''' ⊢;
          omega;
        simp [h_eq, h_eq', h_eq'', h_eq'''] at *;
        exact h_four_point_bound ( hs _ _ _ ha' ) ( hs _ _ _ ha'' ) ( hs _ _ _ ha''' ) ( hs _ _ _ ha'''' );
      have h_four_point_bound : ∀ (t : Finset (Finset (Fin 5))), t ⊆ Finset.powersetCard 3 (Finset.univ : Finset (Fin 5)) → (∀ (a b c d : Fin 5), a < b ∧ b < c ∧ c < d → ¬({a, b, c} ∈ t ∧ {a, b, d} ∈ t ∧ {a, c, d} ∈ t ∧ {b, c, d} ∈ t)) → t.card ≤ 7 := by
        native_decide +revert;
      apply h_four_point_bound;
      · simp +decide [ Finset.subset_iff ];
        rintro _ a b c h₁ h₂ h₃ rfl; simp +decide [ h₂.ne, h₃.ne, show a ≠ b from ne_of_lt h₂, show b ≠ c from ne_of_lt h₃, show a ≠ c from ne_of_lt ( lt_trans h₂ h₃ ) ] ;
      · assumption;
    have h_acute_ordered : s ⊆ Finset.biUnion (Finset.image (fun (ijk : Fin 5 × Fin 5 × Fin 5) => ({ijk.1, ijk.2.1, ijk.2.2} : Finset (Fin 5))) (s.filter (fun (ijk : Fin 5 × Fin 5 × Fin 5) => ijk.1 < ijk.2.1 ∧ ijk.2.1 < ijk.2.2))) (fun (t : Finset (Fin 5)) => Finset.filter (fun (ijk : Fin 5 × Fin 5 × Fin 5) => ({ijk.1, ijk.2.1, ijk.2.2} : Finset (Fin 5)) = t) (Finset.univ : Finset (Fin 5 × Fin 5 × Fin 5))) := by
      intro ijk hi; simp +decide [ Finset.mem_biUnion ] ;
      by_cases h_cases : ijk.1 = ijk.2.1 ∨ ijk.1 = ijk.2.2 ∨ ijk.2.1 = ijk.2.2;
      · rcases h_cases with ( h | h | h ) <;> simp +decide [ h ] at hi ⊢;
        · specialize hs _ _ _ hi ; simp_all +decide [ IsAcuteTriple ];
        · specialize hs _ _ _ hi ; simp_all +decide [ IsAcuteTriple ];
        · specialize hs _ _ _ hi ; simp_all +decide [ IsAcuteTriple ];
      · grind +ring;
    refine le_trans ( Finset.card_le_card h_acute_ordered ) ?_;
    refine' le_trans ( Finset.card_biUnion_le ) _;
    refine' le_trans ( Finset.sum_le_sum fun x hx => show Finset.card _ ≤ 6 from _ ) _;
    · fin_cases x <;> native_decide;
    · norm_num [ h_acute_unordered ];
      linarith;
  convert h_bound ( Finset.filter ( fun ijk => ijk.1 ≠ ijk.2.1 ∧ ijk.1 ≠ ijk.2.2 ∧ ijk.2.1 ≠ ijk.2.2 ∧ IsAcuteTriple P ( pts ijk.1, pts ijk.2.1, pts ijk.2.2 ) ) ( Finset.univ : Finset ( Fin 5 × Fin 5 × Fin 5 ) ) ) _ _ using 1;
  rw [ ← Nat.card_eq_finsetCard ];
  all_goals norm_num;
  · apply_rules [ Classical.decEq, Classical.decPred ];
  · grind +ring

/-! ### Double counting argument -/

/-
PROBLEM
The main combinatorial inequality: 10 * #acute ≤ 7 * #all

PROVIDED SOLUTION
This is the double counting argument. We need to show:
10 * Nat.card {acute ordered triples} ≤ 7 * Nat.card {all ordered triples}

The proof uses the five_point_bound: for any 5 distinct indices, at most 42 of 60 ordered triples from them are acute (ratio 42/60 = 7/10).

Double counting argument:
- Each ordered triple (a,b,c) with distinct indices appears in exactly C(97,2) = 4656 five-element subsets of Fin 100 (choose 2 more distinct indices from the 97 remaining).
- For each five-element subset, at most 42 out of 60 ordered triples within it are acute.
- Sum over five-element subsets: ∑_S #{acute in S} ≤ 42 * C(100,5)
- Left side: 4656 * #{all acute ordered triples}
- Similarly: 4656 * #{all ordered triples} = 60 * C(100,5)
- So: 4656 * #{acute} ≤ 42 * C(100,5) = (42/60) * 60 * C(100,5) = (7/10) * 4656 * #{total}
- Hence: 10 * #{acute} ≤ 7 * #{total}

This argument needs Finset.sum over five-element subsets. With Classical, everything is decidable. Use Fintype.card for the Nat.card values.

Alternative approach: Use Nat.card_le_card with an injection or use the abstract counting principle directly.
-/
set_option maxHeartbeats 1600000 in
lemma ordered_triples_mul_bound (P : Fin 100 → Pt)
    (hP : ∀ a b c : Fin 100, List.Nodup [a, b, c] → ¬Collinear ℝ ({P a, P b, P c} : Set Pt)) :
    10 * Nat.card { abc : Fin 100 × Fin 100 × Fin 100 //
      abc.1 ≠ abc.2.1 ∧ abc.1 ≠ abc.2.2 ∧ abc.2.1 ≠ abc.2.2 ∧ IsAcuteTriple P abc } ≤
    7 * Nat.card { abc : Fin 100 × Fin 100 × Fin 100 //
      abc.1 ≠ abc.2.1 ∧ abc.1 ≠ abc.2.2 ∧ abc.2.1 ≠ abc.2.2 } := by
  obtain ⟨S, hS⟩ : ∃ S : Finset (Fin 100 × Fin 100 × Fin 100), S.card = Nat.card {abc : Fin 100 × Fin 100 × Fin 100 // abc.1 ≠ abc.2.1 ∧ abc.1 ≠ abc.2.2 ∧ abc.2.1 ≠ abc.2.2 ∧ IsAcuteTriple P abc} ∧ ∀ abc ∈ S, abc.1 ≠ abc.2.1 ∧ abc.1 ≠ abc.2.2 ∧ abc.2.1 ≠ abc.2.2 ∧ IsAcuteTriple P abc := by
    refine' ⟨ _, _, _ ⟩;
    exact Finset.image ( fun x : { abc : Fin 100 × Fin 100 × Fin 100 // ¬abc.1 = abc.2.1 ∧ ¬abc.1 = abc.2.2 ∧ ¬abc.2.1 = abc.2.2 ∧ IsAcuteTriple P abc } => x.val ) ( Finset.univ );
    · rw [ Finset.card_image_of_injective _ fun x y hxy => by aesop ] ; simp +decide [ Fintype.card_subtype ] ;
    · aesop;
  obtain ⟨T, hT⟩ : ∃ T : Finset (Fin 100 × Fin 100 × Fin 100), T.card = Nat.card {abc : Fin 100 × Fin 100 × Fin 100 // abc.1 ≠ abc.2.1 ∧ abc.1 ≠ abc.2.2 ∧ abc.2.1 ≠ abc.2.2} ∧ ∀ abc ∈ T, abc.1 ≠ abc.2.1 ∧ abc.1 ≠ abc.2.2 ∧ abc.2.1 ≠ abc.2.2 := by
    use Finset.filter (fun abc => abc.1 ≠ abc.2.1 ∧ abc.1 ≠ abc.2.2 ∧ abc.2.1 ≠ abc.2.2) (Finset.univ : Finset (Fin 100 × Fin 100 × Fin 100));
    simp +zetaDelta at *;
    rw [ Fintype.subtype_card ];
  have h_sum : ∑ s ∈ Finset.powersetCard 5 (Finset.univ : Finset (Fin 100)), (Finset.filter (fun abc => abc.1 ∈ s ∧ abc.2.1 ∈ s ∧ abc.2.2 ∈ s) S).card ≤ 42 * Nat.choose 100 5 := by
    have h_sum : ∀ s ∈ Finset.powersetCard 5 (Finset.univ : Finset (Fin 100)), (Finset.filter (fun abc => abc.1 ∈ s ∧ abc.2.1 ∈ s ∧ abc.2.2 ∈ s) S).card ≤ 42 := by
      intros s hs
      have h_five_point_bound : ∀ (pts : Fin 5 → Fin 100), Function.Injective pts → (Finset.filter (fun abc => abc.1 ∈ Finset.image pts Finset.univ ∧ abc.2.1 ∈ Finset.image pts Finset.univ ∧ abc.2.2 ∈ Finset.image pts Finset.univ) S).card ≤ 42 := by
        intros pts hpts_inj
        have h_five_point_bound : (Finset.filter (fun abc => abc.1 ∈ Finset.image pts Finset.univ ∧ abc.2.1 ∈ Finset.image pts Finset.univ ∧ abc.2.2 ∈ Finset.image pts Finset.univ) S).card ≤ Nat.card { ijk : Fin 5 × Fin 5 × Fin 5 // ijk.1 ≠ ijk.2.1 ∧ ijk.1 ≠ ijk.2.2 ∧ ijk.2.1 ≠ ijk.2.2 ∧ IsAcuteTriple P (pts ijk.1, pts ijk.2.1, pts ijk.2.2) } := by
          rw [ ← Nat.card_eq_finsetCard ];
          apply_rules [ Nat.card_le_card_of_injective ];
          swap;
          use fun x => ⟨ ⟨ Classical.choose ( Finset.mem_image.mp ( x.2 |> Finset.mem_filter.mp |>.2.1 ) ), Classical.choose ( Finset.mem_image.mp ( x.2 |> Finset.mem_filter.mp |>.2.2.1 ) ), Classical.choose ( Finset.mem_image.mp ( x.2 |> Finset.mem_filter.mp |>.2.2.2 ) ) ⟩, by
            grind ⟩
          generalize_proofs at *;
          intro x y hxy;
          grind;
        exact h_five_point_bound.trans ( five_point_bound P hP pts hpts_inj );
      obtain ⟨pts, hpts⟩ : ∃ pts : Fin 5 → Fin 100, Function.Injective pts ∧ Finset.image pts Finset.univ = s := by
        rw [ Finset.mem_powersetCard ] at hs;
        obtain ⟨pts, hpts⟩ : ∃ pts : Fin 5 → Fin 100, Function.Injective pts ∧ ∀ i, pts i ∈ s := by
          exact ⟨ fun i => s.orderEmbOfFin ( by aesop ) i, by aesop_cat, fun i => by aesop ⟩;
        exact ⟨ pts, hpts.1, Finset.eq_of_subset_of_card_le ( Finset.image_subset_iff.mpr fun i _ => hpts.2 i ) ( by simp +decide [ Finset.card_image_of_injective _ hpts.1, hs.2 ] ) ⟩;
      simpa only [ hpts.2 ] using h_five_point_bound pts hpts.1;
    exact le_trans ( Finset.sum_le_sum h_sum ) ( by rw [ Finset.sum_const, Finset.card_powersetCard, Finset.card_fin ] ; norm_num [ mul_comm ] );
  have h_sum : ∑ s ∈ Finset.powersetCard 5 (Finset.univ : Finset (Fin 100)), (Finset.filter (fun abc => abc.1 ∈ s ∧ abc.2.1 ∈ s ∧ abc.2.2 ∈ s) S).card = S.card * Nat.choose 97 2 := by
    have h_sum : ∀ abc ∈ S, (Finset.filter (fun s => abc.1 ∈ s ∧ abc.2.1 ∈ s ∧ abc.2.2 ∈ s) (Finset.powersetCard 5 (Finset.univ : Finset (Fin 100)))).card = Nat.choose 97 2 := by
      intro abc habc
      have h_subset_count : Finset.card (Finset.filter (fun s => abc.1 ∈ s ∧ abc.2.1 ∈ s ∧ abc.2.2 ∈ s) (Finset.powersetCard 5 (Finset.univ : Finset (Fin 100)))) = Finset.card (Finset.powersetCard 2 (Finset.univ \ {abc.1, abc.2.1, abc.2.2})) := by
        refine' Finset.card_bij ( fun s hs => s \ { abc.1, abc.2.1, abc.2.2 } ) _ _ _;
        · grind;
        · simp +contextual [ Finset.ext_iff ];
          grind;
        · intro b hb;
          use Insert.insert abc.1 (Insert.insert abc.2.1 (Insert.insert abc.2.2 b));
          grind;
      simp +decide [ Finset.card_sdiff, * ];
    have h_sum : ∑ s ∈ Finset.powersetCard 5 (Finset.univ : Finset (Fin 100)), (Finset.filter (fun abc => abc.1 ∈ s ∧ abc.2.1 ∈ s ∧ abc.2.2 ∈ s) S).card = ∑ abc ∈ S, (Finset.filter (fun s => abc.1 ∈ s ∧ abc.2.1 ∈ s ∧ abc.2.2 ∈ s) (Finset.powersetCard 5 (Finset.univ : Finset (Fin 100)))).card := by
      simp +decide only [Finset.card_filter];
      exact Finset.sum_comm;
    rw [ h_sum, Finset.sum_congr rfl ‹_›, Finset.sum_const, smul_eq_mul, mul_comm ];
  have h_sum : T.card = Nat.choose 100 3 * 6 := by
    rw [ hT.1, Nat.card_eq_fintype_card ] ; native_decide;
  norm_num [ Nat.choose ] at * ; linarith

/-! ### Main bound combining bijection and counting -/

lemma acute_card_mul_le (P : Fin 100 → Pt)
    (hP : ∀ a b c : Fin 100,
             List.Nodup [a, b, c] → ¬ Collinear ℝ ({P a, P b, P c} : Set Pt)) :
    10 * Nat.card { t : Affine.Triangle ℝ Pt |
        ∃ a b c : Fin 100, ![P a, P b, P c] = t.points ∧ AcuteTriangle t } ≤
    7 * Nat.card { t : Affine.Triangle ℝ Pt |
        ∃ a b c : Fin 100, ![P a, P b, P c] = t.points } := by
  rw [card_acute_eq_card_acute_triples P hP, card_triangles_eq_card_triples P hP]
  exact ordered_triples_mul_bound P hP

theorem imo1970_p6
    (P : Fin 100 → Pt)
    (hP : ∀ a b c : Fin 100,
             List.Nodup [a, b, c] → ¬ Collinear ℝ ({P a, P b, P c} : Set Pt)) :
    let cardAll := Nat.card { t : Affine.Triangle ℝ Pt |
                              ∃ a b c : Fin 100, ![P a, P b, P c] = t.points }
    let cardAcute :=
      Nat.card { t : Affine.Triangle ℝ Pt | ∃ a b c : Fin 100, ![P a, P b, P c] = t.points ∧
                                            AcuteTriangle t }
    (cardAcute : ℚ) / cardAll ≤ 7 / 10 := by
  exact ratio_le_of_mul_le _ _ (acute_card_mul_le P hP)

end Imo1970P6