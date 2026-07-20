import Mathlib

namespace Imo1970P6

open scoped EuclideanGeometry

abbrev Pt := EuclideanSpace ℝ (Fin 2)

/-
The main theorem: among 100 points in general position (no 3 collinear),
at most 70% of all triangles are acute.

Key strategy: double-counting argument.
For any 4-point subset in general position:
- If one point is inside the triangle of the other 3 (non-convex position):
the 3 angles at the interior point sum to 360°, so one is > 90°, giving ≤ 3 acute triangles.
- If the 4 points are in convex position:
in any convex quadrilateral, exactly 0, 1, or 2 of the 4 triangles are acute
(at most 2), because any convex quadrilateral has at least 2 non-acute triangles.
Partition 4-subsets into convex (≤2 acute) and non-convex (≤3 acute).
Since all 4-subsets are convex or non-convex:
97 * A ≤ 3 * C(100,4) gives A/T ≤ 3/4 (coarse bound)
The refined bound: convex 4-subsets give ≤ 2 each, bringing the ratio to ≤ 7/10.
In practice, the bound follows from:
3 * C(100,4) / (97 * C(100,3)) = 3 * 97 / (4 * 97) = 3/4 (too coarse)
The 7/10 bound uses that convex 4-subsets contribute ≤ 2 acute triangles:
Let c = #convex 4-subsets. Then
97*A ≤ 2*c + 3*(C(100,4) - c) = 3*C(100,4) - c
And every 4-tuple of points in the plane in general position is convex
unless one point lies inside the triangle of the other 3.
One shows c ≥ (1/4)*C(100,4) ...
Actually the standard clean proof: in a convex quadrilateral,
the circumscribed circle of the quadrilateral means at least 2 triangles are obtuse.
The bound 7/10 comes from: if ALL 4-subsets were convex, ratio ≤ 2/4 = 1/2;
mixing with non-convex (ratio 3/4) and noting that in the worst case
the ratio is 7/10.

A double-counting principle for a property of triples: if at most seven of the ten
triples in every five-element set are good, then at most seven tenths of all triples are good.
-/
lemma triple_density_of_five_bound {α : Type*} [DecidableEq α]
    (s : Finset α) (hs : s.card = 100) (good : Finset α → Prop) [DecidablePred good]
    (hlocal : ∀ u ∈ s.powersetCard 5,
      ((u.powersetCard 3).filter good).card ≤ 7) :
    10 * ((s.powersetCard 3).filter good).card ≤ 7 * (s.powersetCard 3).card := by
  -- Consider the set of pairs (t, u) where t is a good 3-subset of s and u is a 5-subset of s containing t.
  set T := (Finset.filter good (Finset.powersetCard 3 s)) with hT
  set U := (Finset.powersetCard 5 s) with hU
  set pairs := Finset.biUnion T (fun t => Finset.image (fun u => (t, u)) (Finset.filter (fun u => t ⊆ u) U)) with hpairs;
  -- By double counting, we have $|pairs| \leq 7 \cdot |U|$.
  have h_double_counting : pairs.card ≤ 7 * U.card := by
    have h1 : pairs.card ≤ Finset.sum U (fun u => (Finset.filter good (Finset.powersetCard 3 u)).card) := by
      refine' le_trans ( Finset.card_le_card _ ) _;
      exact Finset.biUnion U fun u => Finset.image ( fun t => ( t, u ) ) ( Finset.filter good ( Finset.powersetCard 3 u ) );
      · grind;
      · exact le_trans ( Finset.card_biUnion_le ) ( Finset.sum_le_sum fun u hu => Finset.card_image_le );
    exact h1.trans ( by simpa [ mul_comm ] using Finset.sum_le_sum hlocal );
  -- On the other hand, each good triple t is contained in exactly $\binom{97}{2}$ 5-subsets u.
  have h_triple_subset : ∀ t ∈ T, (Finset.filter (fun u => t ⊆ u) U).card = Nat.choose 97 2 := by
    intro t ht
    have h_triple_subset : (Finset.filter (fun u => t ⊆ u) U).card = Finset.card (Finset.powersetCard 2 (s \ t)) := by
      refine' Finset.card_bij ( fun u hu => u \ t ) _ _ _;
      · grind;
      · simp +contextual [ Finset.ext_iff ];
        grind;
      · simp +zetaDelta at *;
        intro b hb hb'; use t ∪ b; simp_all +decide [ Finset.subset_iff ] ;
        exact ⟨ ⟨ fun x hx => hx.elim ( fun hx => ht.1.1 hx ) fun hx => hb hx |>.1, by rw [ Finset.card_union_of_disjoint ( Finset.disjoint_left.mpr fun x hx₁ hx₂ => hb hx₂ |>.2 hx₁ ), ht.1.2, hb' ] ⟩, by rw [ Finset.union_sdiff_cancel_left ( Finset.disjoint_left.mpr fun x hx₁ hx₂ => hb hx₂ |>.2 hx₁ ) ] ⟩;
    simp_all +decide [ Finset.card_sdiff ];
    rw [ Finset.inter_eq_left.mpr ht.1.1, ht.1.2 ];
  -- Therefore, $|pairs| = \binom{97}{2} \cdot |T|$.
  have h_pairs_card : pairs.card = Nat.choose 97 2 * T.card := by
    rw [ Finset.card_biUnion ];
    · rw [ Finset.sum_congr rfl fun x hx => Finset.card_image_of_injective _ fun y z h => by injection h, Finset.sum_congr rfl h_triple_subset, Finset.sum_const, smul_eq_mul, mul_comm ];
    · exact fun x hx y hy hxy => Finset.disjoint_left.mpr fun z => by aesop;
  simp_all +decide [ Nat.choose_succ_succ ];
  linarith

lemma acute_configuration_algebra_impossible
    (A B C x y : ℝ)
    (hB : 0 < B) (hdet : C ^ 2 < A * B)
    (hC : 0 < C) (hAB : C < A) (hBA : C < B)
    (hadA : 0 < x * A + y * C)
    (hbdB : 0 < (1 - x) * A - y * C)
    (hadD : 0 < -(x * A + y * C) + x * (x * A + y * C) +
      y * (x * C + y * B))
    (hacA : 0 < x * C + y * B)
    (hcdC : 0 < (1 - y) * B - x * C)
    (hacD : 0 < -(x * C + y * B) + x * (x * A + y * C) +
      y * (x * C + y * B))
    (hbcdB : 0 < (x - 1) * (C - A) + y * (B - C))
    (hbcdC : 0 < x * (A - C) + (y - 1) * (C - B))
    (hbcdD : 0 < C - (x * A + y * C) - (x * C + y * B) +
      x * (x * A + y * C) + y * (x * C + y * B)) : False := by
  -- Consider the four regions determined by x=0, y=0, x+y=1.
  by_cases hx : x ≤ 0
  by_cases hy : y ≤ 0
  by_cases hxy : x + y ≤ 1;
  · nlinarith;
  · linarith;
  · by_cases hy : y ≤ 1; all_goals nlinarith;
  · by_cases hy : y ≤ 0;
    · nlinarith [ mul_le_mul_of_nonneg_left hy hB.le, mul_le_mul_of_nonneg_left hy hC.le, mul_le_mul_of_nonneg_left hy ( sub_nonneg.mpr hAB.le ), mul_le_mul_of_nonneg_left hy ( sub_nonneg.mpr hBA.le ), mul_le_mul_of_nonneg_left hy ( sub_nonneg.mpr hC.le ) ];
    · by_cases hxy : x + y ≥ 1;
      · nlinarith [ mul_le_mul_of_nonneg_left hxy ( sub_nonneg_of_le hAB.le ), mul_le_mul_of_nonneg_left hxy ( sub_nonneg_of_le hBA.le ) ];
      · nlinarith [ mul_pos ( sub_pos.mpr <| lt_of_not_ge hx ) ( sub_pos.mpr <| lt_of_not_ge hy ), mul_pos ( sub_pos.mpr <| lt_of_not_ge hx ) ( sub_pos.mpr <| lt_of_not_ge hxy ), mul_pos ( sub_pos.mpr <| lt_of_not_ge hy ) ( sub_pos.mpr <| lt_of_not_ge hxy ) ]

def AcutePoints (a b c : Pt) : Prop :=
  ∠ a b c < Real.pi / 2 ∧ ∠ b c a < Real.pi / 2 ∧ ∠ c a b < Real.pi / 2

lemma acutePoints_inner_pos {a b c : Pt} (h : AcutePoints a b c) :
    0 < inner ℝ (b - a) (c - a) ∧
    0 < inner ℝ (c - b) (a - b) ∧
    0 < inner ℝ (a - c) (b - c) := by
  unfold AcutePoints at h;
  simp_all +decide [EuclideanGeometry.angle];
  simp_all +decide [ InnerProductGeometry.angle, real_inner_comm ];
  exact ⟨ by exact not_le.mp fun h' => h.2.2.not_ge <| div_nonpos_of_nonpos_of_nonneg h' <| mul_nonneg ( norm_nonneg _ ) ( norm_nonneg _ ), by exact not_le.mp fun h' => h.1.not_ge <| div_nonpos_of_nonpos_of_nonneg h' <| mul_nonneg ( norm_nonneg _ ) ( norm_nonneg _ ), by exact not_le.mp fun h' => h.2.1.not_ge <| div_nonpos_of_nonpos_of_nonneg h' <| mul_nonneg ( norm_nonneg _ ) ( norm_nonneg _ ) ⟩

lemma plane_coordinates_of_not_collinear {a b c d : Pt}
    (h : ¬ Collinear ℝ {a, b, c}) :
    ∃ x y : ℝ, d - a = x • (b - a) + y • (c - a) := by
  -- By definition of affine independence, the vectors $b - a$ and $c - a$ are linearly independent.
  have h_lin_ind : LinearIndependent ℝ ![b - a, c - a] := by
    refine' linearIndependent_fin2.mpr _;
    refine' ⟨ sub_ne_zero.mpr _, fun x hx => h _ ⟩ <;> simp_all +decide [ collinear_iff_exists_forall_eq_smul_vadd ];
    · contrapose! h;
      exact ⟨ a, b - a, 0, by norm_num, 1, by norm_num, 0, by norm_num [ h ] ⟩;
    · exact ⟨ a, c - a, ⟨ 0, by norm_num ⟩, ⟨ x, by simpa [ sub_eq_iff_eq_add ] using hx.symm ⟩, ⟨ 1, by norm_num ⟩ ⟩;
  have h_span : Submodule.span ℝ (Set.range ![b - a, c - a]) = ⊤ := by
    refine' Submodule.eq_top_of_finrank_eq _;
    rw [ finrank_span_eq_card ] <;> norm_num [ h_lin_ind ];
  have := h_span.ge ( Submodule.mem_top : d - a ∈ ⊤ );
  rw [ Submodule.mem_span_range_iff_exists_fun ] at this; obtain ⟨ x, hx ⟩ := this; use x 0, x 1; aesop;

lemma strict_gram_det_of_not_collinear {a b c : Pt}
    (h : ¬ Collinear ℝ {a, b, c}) :
    inner ℝ (b - a) (c - a) ^ 2 <
      inner ℝ (b - a) (b - a) * inner ℝ (c - a) (c - a) := by
  contrapose! h with h;
  rw [ collinear_iff_exists_forall_eq_smul_vadd ];
  -- By definition of inner product, we know that if the inner product of two vectors is zero, then the vectors are orthogonal.
  by_cases h_orth : (b - a) 0 * (c - a) 1 - (b - a) 1 * (c - a) 0 = 0;
  · by_cases h : ( b - a ) 0 = 0 <;> simp_all +decide [ sub_eq_iff_eq_add ];
    · cases h_orth <;> simp_all +decide [ EuclideanSpace.norm_eq ];
      · use a, c - a;
        exact ⟨ ⟨ 0, by norm_num ⟩, ⟨ 0, by ext i; fin_cases i <;> aesop ⟩, ⟨ 1, by norm_num ⟩ ⟩;
      · refine' ⟨ a, EuclideanSpace.single 1 1, ⟨ 0, by norm_num ⟩, ⟨ b.ofLp 1 - a.ofLp 1, _ ⟩, ⟨ c.ofLp 1 - a.ofLp 1, _ ⟩ ⟩ <;> ext i <;> fin_cases i <;> aesop;
    · refine' ⟨ a, b - a, ⟨ 0, by norm_num ⟩, ⟨ 1, by norm_num ⟩, ⟨ ( c.ofLp 0 - a.ofLp 0 ) / ( b.ofLp 0 - a.ofLp 0 ), _ ⟩ ⟩;
      ext i; fin_cases i <;> simp +decide [ *, mul_comm, mul_div_cancel₀, sub_eq_iff_eq_add ] ;
      grind +splitImp;
  · norm_num [ Fin.sum_univ_two, inner ] at *;
    exact False.elim <| h_orth <| by nlinarith [ sq_nonneg ( ( b.ofLp 0 - a.ofLp 0 ) * ( c.ofLp 0 - a.ofLp 0 ) + ( b.ofLp 1 - a.ofLp 1 ) * ( c.ofLp 1 - a.ofLp 1 ) ) ] ;

lemma four_points_not_all_acute (a b c d : Pt)
    (habc : ¬ Collinear ℝ {a, b, c}) :
    ¬ (AcutePoints a b c ∧ AcutePoints a b d ∧
      AcutePoints a c d ∧ AcutePoints b c d) := by
  intro h;
  -- Set A,B,C as Gram entries.
  set A := inner ℝ (b - a) (b - a)
  set B := inner ℝ (c - a) (c - a)
  set C := inner ℝ (b - a) (c - a);
  obtain ⟨x, y, hxy⟩ : ∃ x y : ℝ, d - a = x • (b - a) + y • (c - a) := plane_coordinates_of_not_collinear habc;
  -- Apply the acutePoints_inner_pos lemma to obtain the positivity conditions.
  have h_pos : 0 < A ∧ 0 < B ∧ 0 < C ∧ C < A ∧ C < B ∧ 0 < x * A + y * C ∧ 0 < (1 - x) * A - y * C ∧ 0 < -(x * A + y * C) + x * (x * A + y * C) + y * (x * C + y * B) ∧ 0 < x * C + y * B ∧ 0 < (1 - y) * B - x * C ∧ 0 < -(x * C + y * B) + x * (x * A + y * C) + y * (x * C + y * B) ∧ 0 < (x - 1) * (C - A) + y * (B - C) ∧ 0 < x * (A - C) + (y - 1) * (C - B) ∧ 0 < C - (x * A + y * C) - (x * C + y * B) + x * (x * A + y * C) + y * (x * C + y * B) := by
    have h_pos : 0 < A ∧ 0 < B ∧ 0 < C ∧ C < A ∧ C < B := by
      have := acutePoints_inner_pos h.1;
      simp_all +decide [ A, B, C, inner_sub_left, inner_sub_right ];
      simp_all +decide [ norm_sub_sq_real, real_inner_comm ];
      refine' ⟨ _, _, _, _ ⟩ <;> linarith;
    have h_pos : 0 < inner ℝ (b - a) (d - a) ∧ 0 < inner ℝ (d - b) (a - b) ∧ 0 < inner ℝ (a - d) (b - d) ∧ 0 < inner ℝ (c - a) (d - a) ∧ 0 < inner ℝ (d - c) (a - c) ∧ 0 < inner ℝ (a - d) (c - d) ∧ 0 < inner ℝ (c - b) (d - b) ∧ 0 < inner ℝ (d - c) (b - c) ∧ 0 < inner ℝ (b - d) (c - d) := by
      exact ⟨ acutePoints_inner_pos h.2.1 |>.1, acutePoints_inner_pos h.2.1 |>.2.1, acutePoints_inner_pos h.2.1 |>.2.2, acutePoints_inner_pos h.2.2.1 |>.1, acutePoints_inner_pos h.2.2.1 |>.2.1, acutePoints_inner_pos h.2.2.1 |>.2.2, acutePoints_inner_pos h.2.2.2 |>.1, acutePoints_inner_pos h.2.2.2 |>.2.1, acutePoints_inner_pos h.2.2.2 |>.2.2 ⟩;
    simp_all +decide [ sub_eq_iff_eq_add ];
    simp +zetaDelta at *;
    norm_num [ EuclideanSpace.norm_eq, Real.sq_sqrt <| add_nonneg ( sq_nonneg _ ) ( sq_nonneg _ ) ] at *;
    norm_num [ inner ] at *;
    grind;
  have h_det : C^2 < A * B := by
    convert strict_gram_det_of_not_collinear habc using 1;
  exact acute_configuration_algebra_impossible A B C x y h_pos.2.1 h_det h_pos.2.2.1 h_pos.2.2.2.1 h_pos.2.2.2.2.1 h_pos.2.2.2.2.2.1 h_pos.2.2.2.2.2.2.1 h_pos.2.2.2.2.2.2.2.1 h_pos.2.2.2.2.2.2.2.2.1 h_pos.2.2.2.2.2.2.2.2.2.1 h_pos.2.2.2.2.2.2.2.2.2.2.1 h_pos.2.2.2.2.2.2.2.2.2.2.2.1 h_pos.2.2.2.2.2.2.2.2.2.2.2.2.1 h_pos.2.2.2.2.2.2.2.2.2.2.2.2.2

/-
Among four points in general position, at most three of the four unordered
triangles are acute.
-/
set_option maxHeartbeats 800000 in
lemma four_point_acute_bound
    (P : Fin 4 → Pt)
    (hP : ∀ a b c : Fin 4,
      List.Nodup [a, b, c] → ¬ Collinear ℝ {P a, P b, P c}) :
    Nat.card { t : Affine.Triangle ℝ Pt |
      ∃ a b c : Fin 4, ![P a, P b, P c] = t.points ∧ t.AcuteAngled } ≤ 18 := by
  -- Each_affine.Triangle corresponds to a distinct_triple (a,b,c).
  have h_card : Nat.card {t : Affine.Triangle ℝ Pt | ∃ a b c : Fin 4, ![P a, P b, P c] = t.points ∧ Affine.Simplex.AcuteAngled t} ≤ Nat.card {t : Fin 4 × Fin 4 × Fin 4 | t.1 ≠ t.2.1 ∧ t.1 ≠ t.2.2 ∧ t.2.1 ≠ t.2.2 ∧ AcutePoints (P t.1) (P t.2.1) (P t.2.2)} := by
    have h_card : Nat.card {t : Affine.Triangle ℝ Pt | ∃ a b c : Fin 4, ![P a, P b, P c] = t.points ∧ Affine.Simplex.AcuteAngled t} ≤ Nat.card {t : Fin 4 × Fin 4 × Fin 4 | t.1 ≠ t.2.1 ∧ t.1 ≠ t.2.2 ∧ t.2.1 ≠ t.2.2 ∧ ∃ u : Affine.Triangle ℝ Pt, ![P t.1, P t.2.1, P t.2.2] = u.points ∧ Affine.Simplex.AcuteAngled u} := by
      have h_card : Nat.card (Set.image (fun t : Fin 4 × Fin 4 × Fin 4 => ![P t.1, P t.2.1, P t.2.2]) {t : Fin 4 × Fin 4 × Fin 4 | t.1 ≠ t.2.1 ∧ t.1 ≠ t.2.2 ∧ t.2.1 ≠ t.2.2 ∧ ∃ u : Affine.Triangle ℝ Pt, ![P t.1, P t.2.1, P t.2.2] = u.points ∧ Affine.Simplex.AcuteAngled u}) ≥ Nat.card {t : Affine.Triangle ℝ Pt | ∃ a b c : Fin 4, ![P a, P b, P c] = t.points ∧ Affine.Simplex.AcuteAngled t} := by
        apply Set.ncard_le_ncard_of_injOn;
        case f => exact fun t => t.points;
        · simp +zetaDelta at *;
          intro a x y z h₁ h₂; use x, y, z; simp_all +decide [funext_iff, Fin.forall_fin_succ];
          refine' ⟨ _, _, _, a, ⟨ rfl, rfl, rfl ⟩, h₂ ⟩ <;> intro h <;> simp_all +decide;
          · have := a.independent.injective.ne ( show 0 ≠ 1 from by decide ) ; aesop;
          · have := a.independent.injective.ne ( show 0 ≠ 2 by decide ) ; aesop;
          · have := a.independent.injective.ne ( show 1 ≠ 2 from by decide ) ; aesop;
        · intro t ht t' ht' h; aesop;
        · exact Set.toFinite _;
      refine le_trans h_card ?_;
      apply_rules [ Nat.card_image_le ];
      exact Set.toFinite _;
    refine le_trans h_card ?_;
    apply_rules [ Nat.card_mono ];
    · exact Set.toFinite _;
    · intro t ht; obtain ⟨ u, hu₁, hu₂ ⟩ := ht.2.2.2; simp_all +decide [ Affine.Simplex.AcuteAngled ] ;
      exact ⟨ by simpa [ ← hu₁ ] using hu₂ 0 1 2 ( by decide ) ( by decide ) ( by decide ), by simpa [ ← hu₁ ] using hu₂ 1 2 0 ( by decide ) ( by decide ) ( by decide ), by simpa [ ← hu₁ ] using hu₂ 2 0 1 ( by decide ) ( by decide ) ( by decide ) ⟩;
  refine le_trans h_card ?_;
  -- By examining all possible triples, we can see that at least one of them must be non-acute.
  have h_non_acute : ∃ t : Fin 4 × Fin 4 × Fin 4, t.1 ≠ t.2.1 ∧ t.1 ≠ t.2.2 ∧ t.2.1 ≠ t.2.2 ∧ ¬AcutePoints (P t.1) (P t.2.1) (P t.2.2) := by
    have := four_points_not_all_acute ( P 0 ) ( P 1 ) ( P 2 ) ( P 3 ) ( hP 0 1 2 ( by decide ) ) ; simp_all +decide [ AcutePoints ] ;
    grind;
  obtain ⟨ t, ht₁, ht₂, ht₃, ht₄ ⟩ := h_non_acute;
  have h_card : Nat.card {t : Fin 4 × Fin 4 × Fin 4 | t.1 ≠ t.2.1 ∧ t.1 ≠ t.2.2 ∧ t.2.1 ≠ t.2.2 ∧ AcutePoints (P t.1) (P t.2.1) (P t.2.2)} ≤ Nat.card {t : Fin 4 × Fin 4 × Fin 4 | t.1 ≠ t.2.1 ∧ t.1 ≠ t.2.2 ∧ t.2.1 ≠ t.2.2} - 6 := by
    have h_card : Nat.card {t : Fin 4 × Fin 4 × Fin 4 | t.1 ≠ t.2.1 ∧ t.1 ≠ t.2.2 ∧ t.2.1 ≠ t.2.2 ∧ ¬AcutePoints (P t.1) (P t.2.1) (P t.2.2)} ≥ 6 := by
      have h_card : Nat.card {t : Fin 4 × Fin 4 × Fin 4 | t.1 ≠ t.2.1 ∧ t.1 ≠ t.2.2 ∧ t.2.1 ≠ t.2.2 ∧ ¬AcutePoints (P t.1) (P t.2.1) (P t.2.2)} ≥ Nat.card ({(t.1, t.2.1, t.2.2), (t.1, t.2.2, t.2.1), (t.2.1, t.1, t.2.2), (t.2.1, t.2.2, t.1), (t.2.2, t.1, t.2.1), (t.2.2, t.2.1, t.1)} : Set (Fin 4 × Fin 4 × Fin 4)) := by
        apply_rules [ Nat.card_mono ];
        · exact Set.toFinite _;
        · simp +decide [ Set.insert_subset_iff, ht₁, ht₂, ht₃, ht₄ ];
          unfold AcutePoints at *; simp_all +decide [ EuclideanGeometry.angle_comm ] ;
          grind +ring;
      convert h_card using 1;
      simp +decide;
      grind;
    refine' Nat.le_sub_of_add_le' _;
    convert add_le_add h_card le_rfl using 1;
    simp +decide [Set.setOf_and];
    rw [ ← Finset.card_union_of_disjoint ];
    · congr with x ; by_cases hx : AcutePoints ( P x.1 ) ( P x.2.1 ) ( P x.2.2 ) <;> aesop;
    · simp +contextual [ Finset.disjoint_left ];
  exact h_card.trans (by rw [Nat.card_eq_fintype_card]; decide)

lemma triple_count_of_four_local_bound {α : Type*} [DecidableEq α]
    (s : Finset α) (hs : s.card = 5) (good : Finset α → Prop) [DecidablePred good]
    (hlocal : ∀ u ∈ s.powersetCard 4,
      ((u.powersetCard 3).filter good).card ≤ 3) :
    ((s.powersetCard 3).filter good).card ≤ 7 := by
  set T := (s.powersetCard 3).filter good with hT
  set U := s.powersetCard 4 with hU
  set pairs := T.biUnion (fun t =>
    (U.filter fun u => t ⊆ u).image fun u => (t, u)) with hpairs
  have hpairs_le : pairs.card ≤ 3 * U.card := by
    have h₁ : pairs.card ≤
        ∑ u ∈ U, ((u.powersetCard 3).filter good).card := by
      refine' le_trans (Finset.card_le_card _) _
      exact U.biUnion fun u =>
        ((u.powersetCard 3).filter good).image fun t => (t, u)
      · grind
      · exact le_trans Finset.card_biUnion_le
          (Finset.sum_le_sum fun _ _ => Finset.card_image_le)
    exact h₁.trans (by simpa [mul_comm] using Finset.sum_le_sum hlocal)
  have hcontain : ∀ t ∈ T, (U.filter fun u => t ⊆ u).card = Nat.choose 2 1 := by
    intro t ht
    have htt : t ⊆ s ∧ t.card = 3 := by
      have := (Finset.mem_filter.mp (hT ▸ ht)).1
      exact Finset.mem_powersetCard.mp this
    have heq : (U.filter fun u => t ⊆ u).card =
        (Finset.powersetCard 1 (s \ t)).card := by
      refine' Finset.card_bij (fun u _ => u \ t) _ _ _
      · grind
      · simp +contextual [Finset.ext_iff]
        grind
      · simp +zetaDelta at *
        intro b hb hbcard
        use t ∪ b
        simp_all +decide [Finset.subset_iff]
        exact ⟨⟨fun x hx => hx.elim (fun hx => ht.1.1 hx) fun hx => (hb hx).1,
          by rw [Finset.card_union_of_disjoint
            (Finset.disjoint_left.mpr fun x hx₁ hx₂ => (hb hx₂).2 hx₁), ht.1.2, hbcard]⟩,
          by rw [Finset.union_sdiff_cancel_left
            (Finset.disjoint_left.mpr fun x hx₁ hx₂ => (hb hx₂).2 hx₁)]⟩
    rw [heq, Finset.card_powersetCard, Finset.card_sdiff,
      Finset.inter_eq_left.mpr htt.1, htt.2, hs]
  have hpairs_card : pairs.card = Nat.choose 2 1 * T.card := by
    rw [Finset.card_biUnion]
    · rw [Finset.sum_congr rfl fun x hx =>
          Finset.card_image_of_injective _ fun y z h => by injection h,
        Finset.sum_congr rfl hcontain, Finset.sum_const, smul_eq_mul, mul_comm]
    · exact fun x hx y hy hxy => Finset.disjoint_left.mpr fun z => by aesop
  have hUcard : U.card = 5 := by
    simp [hU, Finset.card_powersetCard, hs]
  have hchoose : Nat.choose 2 1 = 2 := by decide
  rw [hchoose] at hpairs_card
  omega

lemma point_map_injective
    (P : Fin 100 → Pt)
    (hP : ∀ a b c : Fin 100,
      List.Nodup [a, b, c] → ¬ Collinear ℝ {P a, P b, P c}) :
    Function.Injective P := by
  intro a b hab; specialize hP a b; simp_all +decide [ collinear_pair ] ;
  contrapose! hP;
  exact ⟨ if a = b + 1 then b + 2 else b + 1, hP, by aesop ⟩

theorem imo1970_p6
    (P : Fin 100 → Pt)
    (hP : ∀ a b c : Fin 100,
             List.Nodup [a, b, c] → ¬ Collinear ℝ {P a, P b, P c}) :
    let cardAll := Nat.card { t : Affine.Triangle ℝ Pt |
                              ∃ a b c : Fin 100, ![P a, P b, P c] = t.points }
    let cardAcute :=
      Nat.card { t : Affine.Triangle ℝ Pt | ∃ a b c : Fin 100, ![P a, P b, P c] = t.points ∧
                                            t.AcuteAngled }
    (cardAcute : ℚ) / cardAll ≤ 7 / 10 := by
  sorry