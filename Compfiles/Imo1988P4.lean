import Mathlib

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Olympiad 1988, Problem 4

Show that the set of real numbers x which satisfy the inequality
∑_{k=1}^{70} k/(x-k) ≥ 5/4
is a union of disjoint intervals, the sum of whose lengths is 1988.

## Formalization notes

Let `f x = ∑_{k=1}^{70} k/(x-k)`.  Between consecutive poles `f` is continuous and
strictly decreasing, running from `+∞` to `-∞` on each bounded gap `(m, m+1)`
(`1 ≤ m ≤ 69`) and from `+∞` to `0` on the rightmost ray `(70, ∞)`.  Hence on each
of these `70` intervals there is a unique point `r m` with `f (r m) = 5/4`, and the
solution set restricted to the gap is `(m, r m]`.

There is one Lean-specific subtlety: at a pole `x = m` the term `m/(x-m)` is
`m/0 = 0`, so `f m` is finite.  A direct computation shows `f m ≥ 5/4` exactly when
`56 ≤ m ≤ 70`, so those `15` pole points belong to the solution set as well.  Since
the point `m` sits on the left end of `(m, r m]`, the corresponding interval becomes
the closed interval `[m, r m]`; the extra point does not change the length.

The total length is `∑_{m=1}^{70} (r m - m) = 1988`, obtained from Vieta's formulas:
the `r m` are exactly the roots of the degree-`70` polynomial
`P = (5/4)∏(X-k) - ∑_k k ∏_{j≠k}(X-j)`, whose root sum is
`(2485·9/4)/(5/4) = 4473`, and `4473 - ∑_{m=1}^{70} m = 4473 - 2485 = 1988`.
-/

namespace Imo1988P4

open scoped BigOperators
open Set MeasureTheory

/-- The function `f x = ∑_{k=1}^{70} k/(x-k)`. -/
noncomputable def f (x : ℝ) : ℝ := ∑ k ∈ Finset.Icc (1 : ℕ) 70, (k : ℝ) / (x - k)

/-- The rational analogue of `f` at an integer point, used for the pole computation. -/
def gq (m : ℕ) : ℚ := ∑ k ∈ Finset.Icc (1 : ℕ) 70, (k : ℚ) / ((m : ℚ) - k)

/-
For each gap `(m, m+1)` (or `(70,∞)` when `m = 70`) there is a unique solution
`r` of `f = 5/4`, with `f ≥ 5/4` to its left and `f < 5/4` to its right within the
gap.
-/
lemma root_exists (m : ℕ) (hm : 1 ≤ m) (hm' : m ≤ 70) :
    ∃ r : ℝ, (m : ℝ) < r ∧ (m ≤ 69 → r < (m : ℝ) + 1) ∧ f r = 5 / 4 ∧
      (∀ x : ℝ, (m : ℝ) < x → (m ≤ 69 → x < (m : ℝ) + 1) → (5 / 4 ≤ f x ↔ x ≤ r)) := by
  by_cases hm'' : m ≤ 69;
  · -- Let's choose any $r$ in the interval $(m, m+1)$ such that $f(r) = 5/4$.
    obtain ⟨r, hr⟩ : ∃ r ∈ Set.Ioo (m : ℝ) (m + 1), f r = 5 / 4 := by
      -- By the properties of the intermediate value theorem, since $f(x)$ is continuous and strictly decreasing on $(m, m+1)$, and $f(m) > 5/4$ and $f(m+1) < 5/4$, there exists some $r \in (m, m+1)$ such that $f(r) = 5/4$.
      have h_ivt : ∃ r ∈ Set.Ioo (m : ℝ) (m + 1), f r = 5 / 4 := by
        have h_cont : ContinuousOn f (Set.Ioo (m : ℝ) (m + 1)) := by
          refine' continuousOn_finset_sum _ fun k hk => ContinuousOn.div continuousOn_const ( continuousOn_id.sub continuousOn_const ) fun x hx => _;
          by_contra h_contra;
          exact absurd h_contra ( by linarith [ hx.1, hx.2, show ( k : ℝ ) ≤ m by exact_mod_cast Nat.le_of_lt_succ ( by { rw [ ← @Nat.cast_lt ℝ ] ; push_cast; linarith [ hx.1, hx.2 ] } ) ] )
        have h_lim_left : Filter.Tendsto f (nhdsWithin (m : ℝ) (Set.Ioi m)) Filter.atTop := by
          have h_lim_left : Filter.Tendsto (fun x : ℝ => (m : ℝ) / (x - m)) (nhdsWithin (m : ℝ) (Set.Ioi m)) Filter.atTop := by
            refine' Filter.Tendsto.const_mul_atTop ( by positivity ) ( tendsto_inv_nhdsGT_zero.comp _ );
            rw [ Metric.tendsto_nhdsWithin_nhdsWithin ] ; aesop;
          have h_lim_left : Filter.Tendsto (fun x : ℝ => ∑ k ∈ Finset.Icc (1 : ℕ) 70 \ {m}, (k : ℝ) / (x - k)) (nhdsWithin (m : ℝ) (Set.Ioi m)) (nhds (∑ k ∈ Finset.Icc (1 : ℕ) 70 \ {m}, (k : ℝ) / (m - k))) := by
            exact tendsto_finset_sum _ fun i hi => tendsto_const_nhds.div ( continuousWithinAt_id.sub continuousWithinAt_const ) ( sub_ne_zero_of_ne <| by aesop );
          convert h_lim_left.add_atTop ‹Filter.Tendsto ( fun x : ℝ => ( m : ℝ ) / ( x - m ) ) ( nhdsWithin ( m : ℝ ) ( Set.Ioi m ) ) Filter.atTop› using 1;
          ext x; simp +decide [ f, Finset.sum_eq_sum_diff_singleton_add ( show m ∈ Finset.Icc 1 70 from Finset.mem_Icc.mpr ⟨ hm, hm' ⟩ ) ] ;
        have h_lim_right : Filter.Tendsto f (nhdsWithin (m + 1 : ℝ) (Set.Iio (m + 1))) Filter.atBot := by
          have h_lim_right : Filter.Tendsto (fun x : ℝ => (m + 1 : ℝ) / (x - (m + 1))) (nhdsWithin (m + 1 : ℝ) (Set.Iio (m + 1))) Filter.atBot := by
            norm_num [ Filter.atBot, eventually_nhdsWithin_iff ];
            intro i; rw [ Metric.eventually_nhds_iff ] ; norm_num;
            exact ⟨ ( |i| + 1 ) ⁻¹, by positivity, fun y hy₁ hy₂ => by rw [ div_le_iff_of_neg ] <;> cases abs_cases i <;> nlinarith [ mul_inv_cancel₀ ( by linarith : ( |i| + 1 : ℝ ) ≠ 0 ), abs_lt.mp hy₁ ] ⟩;
          have h_lim_right : Filter.Tendsto (fun x : ℝ => ∑ k ∈ Finset.Icc (1 : ℕ) 70 \ {m + 1}, (k : ℝ) / (x - k)) (nhdsWithin (m + 1 : ℝ) (Set.Iio (m + 1))) (nhds (∑ k ∈ Finset.Icc (1 : ℕ) 70 \ {m + 1}, (k : ℝ) / ((m + 1 : ℝ) - k))) := by
            exact tendsto_finset_sum _ fun i hi => tendsto_const_nhds.div ( continuousWithinAt_id.sub continuousWithinAt_const ) ( sub_ne_zero_of_ne <| by norm_cast; aesop );
          convert h_lim_right.add_atBot ‹Filter.Tendsto ( fun x : ℝ => ( m + 1 : ℝ ) / ( x - ( m + 1 ) ) ) ( nhdsWithin ( m + 1 : ℝ ) ( Set.Iio ( m + 1 ) ) ) Filter.atBot› using 2 ; norm_num [ f ];
          rw [ Finset.sum_eq_sum_diff_singleton_add ( show m + 1 ∈ Finset.Icc 1 70 from Finset.mem_Icc.mpr ⟨ by linarith, by linarith ⟩ ) ] ; norm_cast
        obtain ⟨x₁, hx₁⟩ : ∃ x₁ ∈ Set.Ioo (m : ℝ) (m + 1), f x₁ > 5 / 4 := by
          have := h_lim_left.eventually_gt_atTop ( 5 / 4 ) ; have := this.and ( Ioo_mem_nhdsGT_of_mem ⟨ le_rfl, lt_add_one _ ⟩ ) ; obtain ⟨ x, hx₁, hx₂ ⟩ := this.exists; exact ⟨ x, hx₂, hx₁ ⟩ ;
        obtain ⟨x₂, hx₂⟩ : ∃ x₂ ∈ Set.Ioo (m : ℝ) (m + 1), f x₂ < 5 / 4 := by
          have := h_lim_right.eventually ( Filter.eventually_lt_atBot ( 5 / 4 ) ) ; have := this.and ( Ioo_mem_nhdsLT ( show ( m : ℝ ) + 1 > m by norm_num ) ) ; obtain ⟨ x₂, hx₂₁, hx₂₂ ⟩ := this.exists; exact ⟨ x₂, hx₂₂, hx₂₁ ⟩ ;
        have h_ivt : IsConnected (f '' Set.Ioo (m : ℝ) (m + 1)) := by
          exact ⟨ Set.Nonempty.image _ ⟨ x₁, hx₁.1 ⟩, isPreconnected_Ioo.image _ h_cont ⟩;
        exact h_ivt.Icc_subset ( Set.mem_image_of_mem f hx₂.1 ) ( Set.mem_image_of_mem f hx₁.1 ) ⟨ hx₂.2.le, hx₁.2.le ⟩;
      exact h_ivt;
    -- We need to show that $f$ is strictly decreasing on $(m, m+1)$.
    have h_decreasing : StrictAntiOn f (Set.Ioo (m : ℝ) (m + 1)) := by
      refine' fun x hx y hy hxy => Finset.sum_lt_sum _ _;
      · intro i hi; rcases lt_trichotomy i m with hi' | rfl | hi' <;> norm_num at *;
        · rw [ div_le_div_iff₀ ] <;> nlinarith [ show ( i : ℝ ) + 1 ≤ m by norm_cast ];
        · gcongr ; linarith;
        · rw [ div_le_iff_of_neg ];
          · rw [ div_mul_eq_mul_div, div_le_iff_of_neg ] <;> nlinarith [ show ( i : ℝ ) ≥ m + 1 by norm_cast ];
          · linarith [ show ( i : ℝ ) ≥ m + 1 by norm_cast ];
      · exact ⟨ m, Finset.mem_Icc.mpr ⟨ hm, hm' ⟩, by rw [ div_lt_div_iff₀ ] <;> nlinarith [ hx.1, hx.2, hy.1, hy.2, show ( m : ℝ ) ≥ 1 by norm_cast ] ⟩;
    use r;
    simp_all +decide [ StrictAntiOn ];
    intro x hx₁ hx₂; exact ⟨ fun hx₃ => le_of_not_gt fun hx₄ => by linarith [ h_decreasing ( show ( m : ℝ ) < r by linarith ) ( show r < m + 1 by linarith ) ( show ( m : ℝ ) < x by linarith ) ( show x < m + 1 by linarith ) hx₄ ], fun hx₃ => by exact le_of_not_gt fun hx₄ => by linarith [ h_decreasing ( show ( m : ℝ ) < x by linarith ) ( show x < m + 1 by linarith ) ( show ( m : ℝ ) < r by linarith ) ( show r < m + 1 by linarith ) ( lt_of_le_of_ne hx₃ ( by aesop_cat ) ) ] ⟩ ;
  · interval_cases m ; norm_num at *;
    -- Let's choose any $r$ such that $f(r) = \frac{5}{4}$ and $70 < r$.
    obtain ⟨r, hr⟩ : ∃ r : ℝ, 70 < r ∧ f r = 5 / 4 := by
      -- By the intermediate value theorem, since $f(x)$ is continuous and strictly decreasing on $(70, \infty)$, and $f(71) > 5/4$ while $f(x) \to 0$ as $x \to \infty$, there exists some $r \in (71, \infty)$ such that $f(r) = 5/4$.
      have h_ivt : ∃ r ∈ Set.Ioo 71 (10^6), f r = 5 / 4 := by
        apply_rules [ intermediate_value_Ioo' ] <;> norm_num [ f ];
        · exact continuousOn_of_forall_continuousAt fun x hx => by exact tendsto_finset_sum _ fun i hi => ContinuousAt.div continuousAt_const ( continuousAt_id.sub continuousAt_const ) ( by linarith [ hx.1, show ( i : ℝ ) ≤ 70 by exact_mod_cast Finset.mem_Icc.mp hi |>.2 ] ) ;
        · norm_num [ Finset.sum_Ioc_succ_top, (Nat.succ_eq_succ ▸ Finset.Icc_succ_left_eq_Ioc) ];
      exact ⟨ h_ivt.choose, lt_trans ( by norm_num ) h_ivt.choose_spec.1.1, h_ivt.choose_spec.2 ⟩;
    -- We'll use that $f(x)$ is strictly decreasing on $(70, \infty)$ to show that $r$ is unique.
    have h_decreasing : StrictAntiOn f (Set.Ioi 70) := by
      refine' fun x hx y hy hxy => Finset.sum_lt_sum _ _;
      · exact fun i hi => by rw [ div_le_div_iff₀ ] <;> nlinarith [ show ( i : ℝ ) ≤ 70 by norm_cast; linarith [ Finset.mem_Icc.mp hi ], hx.out, hy.out ] ;
      · exact ⟨ 70, by norm_num, by rw [ div_lt_div_iff₀ ] <;> norm_num <;> linarith [ hx.out, hy.out ] ⟩;
    refine' ⟨ r, hr.1, hr.2, fun x hx => ⟨ fun hx' => le_of_not_gt fun hx'' => by linarith [ h_decreasing ( show 70 < r by linarith ) ( show 70 < x by linarith ) hx'' ], fun hx' => _ ⟩ ⟩;
    exact hr.2 ▸ h_decreasing.antitoneOn ( show 70 < x by linarith ) ( show 70 < r by linarith ) hx'

/-- The chosen solution in the gap starting at `m`. -/
noncomputable def r (m : ℕ) : ℝ :=
  if h : 1 ≤ m ∧ m ≤ 70 then (root_exists m h.1 h.2).choose else 0

lemma r_spec (m : ℕ) (hm : 1 ≤ m) (hm' : m ≤ 70) :
    (m : ℝ) < r m ∧ (m ≤ 69 → r m < (m : ℝ) + 1) ∧ f (r m) = 5 / 4 ∧
      (∀ x : ℝ, (m : ℝ) < x → (m ≤ 69 → x < (m : ℝ) + 1) → (5 / 4 ≤ f x ↔ x ≤ r m)) := by
  have h : 1 ≤ m ∧ m ≤ 70 := ⟨hm, hm'⟩
  simpa only [r, dif_pos h] using (root_exists m hm hm').choose_spec

lemma r_gt (m : ℕ) (hm : 1 ≤ m) (hm' : m ≤ 70) : (m : ℝ) < r m :=
  (r_spec m hm hm').1

lemma r_lt (m : ℕ) (hm : 1 ≤ m) (hm' : m ≤ 69) : r m < (m : ℝ) + 1 :=
  (r_spec m hm (by omega)).2.1 hm'

-- The value of `f` at the pole `m` is `≥ 5/4` exactly when `56 ≤ m`.
set_option maxHeartbeats 1000000 in
private lemma pole_mem' (m : ℕ) (hm : 1 ≤ m) (hm' : m ≤ 70) :
    (5 / 4 ≤ f (m : ℝ)) ↔ 56 ≤ m := by
  unfold f
  interval_cases m <;> norm_num [Finset.sum_Icc_succ_top]

lemma pole_mem (m : ℕ) (hm : 1 ≤ m) (hm' : m ≤ 70) :
    (5 / 4 ≤ f (m : ℝ)) ↔ 56 ≤ m :=
  pole_mem' m hm hm'

/-- Below the first pole the inequality never holds. -/
lemma not_mem_below (x : ℝ) (hx : x < 1) : f x < 5 / 4 := by
  have h : f x < 0 := by
    unfold f
    apply Finset.sum_neg
    · intro k hk
      rw [Finset.mem_Icc] at hk
      apply div_neg_of_pos_of_neg
      · exact_mod_cast hk.1
      · have : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk.1
        linarith
    · exact ⟨1, by simp⟩
  linarith

/-- The interval associated with the gap starting at the pole `m`. -/
noncomputable def J (m : ℕ) : Set ℝ :=
  if 56 ≤ m then Set.Icc (m : ℝ) (r m) else Set.Ioc (m : ℝ) (r m)

lemma J_ordConnected (m : ℕ) : (J m).OrdConnected := by
  unfold J; split <;> [exact ordConnected_Icc; exact ordConnected_Ioc]

lemma J_subset (m : ℕ) (hm : 1 ≤ m) (hm' : m ≤ 70) : J m ⊆ Set.Icc (m : ℝ) (r m) := by
  unfold J; split
  · exact subset_rfl
  · exact Ioc_subset_Icc_self

lemma volume_J (m : ℕ) (hm : 1 ≤ m) (hm' : m ≤ 70) :
    volume (J m) = ENNReal.ofReal (r m - m) := by
  unfold J; split <;> simp [Real.volume_Icc, Real.volume_Ioc]

/-
The central characterization of the solution set.
-/
lemma mem_S_iff (x : ℝ) :
    (5 / 4 ≤ f x) ↔ ∃ m : ℕ, 1 ≤ m ∧ m ≤ 70 ∧ x ∈ J m := by
  constructor;
  · intro hx
    by_cases hx1 : x < 1;
    · linarith [ not_mem_below x hx1 ];
    · by_cases hx2 : 70 < x;
      · -- If $70 < x$, take $m = 70$. The 4th part of `r_spec 70` with $70 < x$ (the `m ≤ 69 → ...` hypothesis is vacuous since `70 ≤ 69` is false) gives $x ≤ r 70$. Since $56 ≤ 70$, `J 70 = Set.Icc 70 (r 70)`; and $70 ≤ x ≤ r 70$ so $x ∈ J 70$.
        use 70
        simp [J];
        grind +locals;
      · -- Let $m = \lfloor x \rfloor$. Then $1 \leq m \leq 70$ and $(m : ℝ) \leq x < (m : ℝ) + 1$.
        obtain ⟨m, hm1, hm2⟩ : ∃ m : ℕ, 1 ≤ m ∧ m ≤ 70 ∧ (m : ℝ) ≤ x ∧ x < (m : ℝ) + 1 := by
          exact ⟨ ⌊x⌋₊, Nat.floor_pos.mpr ( by linarith ), Nat.le_of_lt_succ ( by rw [ Nat.floor_lt' ] <;> norm_num ; linarith ), Nat.floor_le ( by linarith ), Nat.lt_floor_add_one _ ⟩;
        by_cases hm3 : x = m <;> simp_all +decide [ J ];
        · use m; simp_all +decide [ pole_mem ] ;
          linarith [ r_gt m hm1 hm2 ];
        · grind +locals;
  · rintro ⟨ m, hm₁, hm₂, hm₃ ⟩;
    by_cases hm₄ : x = m <;> simp_all +decide [ J ];
    · split_ifs at hm₃ <;> norm_num at hm₃;
      exact pole_mem m hm₁ hm₂ |>.2 ‹_›;
    · have := r_spec m hm₁ hm₂; split_ifs at hm₃ <;> simp_all +decide [ Set.Icc_def, Set.Ioc_def ] ;
      · exact this.2.2.2 x ( lt_of_le_of_ne hm₃.1 ( Ne.symm hm₄ ) ) ( fun _ => by linarith [ this.2.1 ‹_› ] ) |>.2 hm₃.2;
      · grind +splitIndPred

/-- Distinct gaps give disjoint intervals. -/
lemma J_disjoint (a b : ℕ) (ha : a ∈ Finset.Icc (1 : ℕ) 70) (hb : b ∈ Finset.Icc (1 : ℕ) 70)
    (hab : a ≠ b) : Disjoint (J a) (J b) := by
  rw [Finset.mem_Icc] at ha hb
  -- It suffices to treat the case `a < b`; the other is symmetric.
  have key : ∀ c d : ℕ, 1 ≤ c → c ≤ 70 → 1 ≤ d → d ≤ 70 → c < d →
      Disjoint (J c) (J d) := by
    intro c d hc1 hc2 hd1 hd2 hcd
    rw [Set.disjoint_left]
    intro y hyc hyd
    have hyc' := J_subset c hc1 hc2 hyc
    have hyd' := J_subset d hd1 hd2 hyd
    have hrc : r c < (c : ℝ) + 1 := r_lt c hc1 (by omega)
    have hcd' : (c : ℝ) + 1 ≤ (d : ℝ) := by exact_mod_cast (by omega : c + 1 ≤ d)
    have h1 : y ≤ r c := hyc'.2
    have h2 : (d : ℝ) ≤ y := hyd'.1
    linarith
  rcases lt_or_gt_of_ne hab with h | h
  · exact key a b ha.1 ha.2 hb.1 hb.2 h
  · exact (key b a hb.1 hb.2 ha.1 ha.2 h).symm

open Polynomial

/-- The monic degree-70 polynomial `∏_{k=1}^{70} (X - k)`. -/
noncomputable def Qpoly : ℝ[X] := ∏ k ∈ Finset.Icc (1 : ℕ) 70, (X - C (k : ℝ))

/-- The degree-69 polynomial `∑_k k · ∏_{j≠k} (X - j)`. -/
noncomputable def Rpoly : ℝ[X] :=
  ∑ k ∈ Finset.Icc (1 : ℕ) 70, C (k : ℝ) * ∏ j ∈ (Finset.Icc (1 : ℕ) 70).erase k, (X - C (j : ℝ))

/-- The cleared polynomial `(5/4)·∏(X-k) - ∑_k k·∏_{j≠k}(X-j)`, whose roots are the `r m`. -/
noncomputable def Ppoly : ℝ[X] := C (5 / 4) * Qpoly - Rpoly

/-
`r m` is never one of the integer poles.
-/
lemma r_ne_cast (m k : ℕ) (hm : 1 ≤ m) (hm' : m ≤ 70) (hk : 1 ≤ k) (hk' : k ≤ 70) :
    r m ≠ (k : ℝ) := by
  by_cases h : m ≤ 69 <;> simp_all +decide [ Finset.prod_eq_prod_diff_singleton_mul ( show k ∈ Finset.Icc 1 70 from Finset.mem_Icc.mpr ⟨ hk, hk' ⟩ ) ];
  · by_cases hk_le_m : k ≤ m;
    · linarith [ r_gt m hm hm', show ( k : ℝ ) ≤ m by norm_cast ];
    · linarith [ show ( k : ℝ ) ≥ m + 1 by exact_mod_cast not_le.mp hk_le_m, r_lt m hm h ];
  · interval_cases m ; norm_num at *;
    exact ne_of_gt ( lt_of_le_of_lt ( Nat.cast_le.mpr hk' ) ( r_gt 70 ( by norm_num ) ( by norm_num ) ) )

lemma Qpoly_monic : Qpoly.Monic := by
  exact Polynomial.monic_prod_of_monic _ _ fun x hx => Polynomial.monic_X_sub_C _

lemma Qpoly_natDegree : Qpoly.natDegree = 70 := by
  unfold Qpoly
  rw [Polynomial.natDegree_prod _ _ fun i _ => Polynomial.X_sub_C_ne_zero _]
  simp only [← Polynomial.C_eq_natCast, Polynomial.natDegree_X_sub_C]
  simp

lemma Qpoly_coeff69 : Qpoly.coeff 69 = -2485 := by
  have h : Qpoly = ∏ k ∈ Finset.Icc (1:ℕ) 70, (X + C (-(k:ℝ))) := by
    unfold Qpoly; refine Finset.prod_congr rfl (fun k _ => ?_); rw [C_neg]; ring
  have hc : (Finset.Icc (1:ℕ) 70).card = 70 := by simp
  rw [h, Finset.prod_X_add_C_coeff _ _ (by rw [hc]; norm_num), hc]
  norm_num
  rw [Finset.powersetCard_one, Finset.sum_map]
  simp only [Function.Embedding.coeFn_mk, Finset.prod_singleton]
  rw [show (∑ k ∈ Finset.Icc (1:ℕ) 70, -(k:ℝ)) = -((∑ k ∈ Finset.Icc (1:ℕ) 70, k : ℕ) : ℝ) from by
    push_cast; rw [← Finset.sum_neg_distrib]]
  rw [show (∑ k ∈ Finset.Icc (1:ℕ) 70, k) = 2485 from by decide]
  norm_num

lemma Rpoly_natDegree_lt : Rpoly.natDegree < 70 := by
  have h_deg : ∀ k ∈ Finset.Icc (1 : ℕ) 70, Polynomial.natDegree (C (k : ℝ) * ∏ j ∈ (Finset.Icc (1 : ℕ) 70).erase k, (X - C (j : ℝ))) ≤ 69 := by
    intro k hk; rw [ Polynomial.natDegree_C_mul, Polynomial.natDegree_prod _ _ fun x hx => Polynomial.X_sub_C_ne_zero _ ] ; simp +decide [ Polynomial.natDegree_sub_eq_left_of_natDegree_lt, * ] ;
    aesop;
  exact lt_of_le_of_lt ( Polynomial.natDegree_sum_le _ _ ) ( lt_of_le_of_lt ( Finset.sup_le h_deg ) ( by norm_num ) )

lemma Rpoly_coeff69 : Rpoly.coeff 69 = 2485 := by
  unfold Rpoly;
  erw [ Polynomial.finset_sum_coeff, Finset.sum_congr rfl fun i hi => ?_ ];
  convert Finset.sum_congr rfl fun i hi => ?_;
  rotate_left;
  use fun i => ( i : ℝ ) * Polynomial.leadingCoeff ( ∏ j ∈ Finset.erase ( Finset.Icc 1 70 ) i, ( Polynomial.X - Polynomial.C ( j : ℝ ) ) );
  use fun i => i;
  · rw [ Polynomial.leadingCoeff_prod, Finset.prod_congr rfl fun _ _ => Polynomial.leadingCoeff_X_sub_C _ ] ; norm_num;
  · rw [ Polynomial.coeff_C_mul, Polynomial.leadingCoeff, Polynomial.natDegree_prod _ _ fun x hx => Polynomial.X_sub_C_ne_zero _ ];
    norm_num [ Polynomial.natDegree_sub_eq_left_of_natDegree_lt ];
    exact Or.inl ( by rw [ Finset.card_erase_of_mem hi ] ; norm_num );
  · norm_num [ Finset.sum_Ioc_succ_top, (Nat.succ_eq_succ ▸ Finset.Icc_succ_left_eq_Ioc) ]

lemma Ppoly_natDegree : Ppoly.natDegree = 70 := by
  erw [ Polynomial.natDegree_sub_eq_left_of_natDegree_lt ];
  · rw [ Polynomial.natDegree_C_mul ] <;> norm_num [ Qpoly_natDegree ];
  · rw [ Polynomial.natDegree_C_mul ] <;> norm_num [ Qpoly_natDegree, Rpoly_natDegree_lt ]

lemma Ppoly_leadingCoeff : Ppoly.leadingCoeff = 5 / 4 := by
  rw [ Polynomial.leadingCoeff, Ppoly_natDegree ];
  unfold Ppoly; norm_num [ Polynomial.coeff_C, Polynomial.coeff_X, mul_sub ] ;
  rw [ show Qpoly.coeff 70 = 1 from ?_, show Rpoly.coeff 70 = 0 from ?_ ] <;> norm_num;
  · exact Polynomial.coeff_eq_zero_of_natDegree_lt <| by linarith [ Rpoly_natDegree_lt ] ;
  · convert Qpoly_monic.coeff_natDegree ; norm_num [ Qpoly_natDegree ]

lemma Ppoly_ne_zero : Ppoly ≠ 0 := by
  exact ne_of_apply_ne Polynomial.natDegree <| by norm_num [ Ppoly_natDegree ]

lemma Ppoly_coeff69 : Ppoly.coeff 69 = -(22365 / 4) := by
  unfold Ppoly; norm_num [ Qpoly_coeff69, Rpoly_coeff69 ] ;

/-
Evaluation of `Ppoly` at any real point.
-/
lemma Ppoly_eval (x : ℝ) :
    Ppoly.eval x = (5 / 4) * (∏ k ∈ Finset.Icc (1 : ℕ) 70, (x - (k : ℝ)))
      - ∑ k ∈ Finset.Icc (1 : ℕ) 70,
          (k : ℝ) * ∏ j ∈ (Finset.Icc (1 : ℕ) 70).erase k, (x - (j : ℝ)) := by
  unfold Ppoly; simp +decide [ Polynomial.eval_finset_sum, Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C ] ;
  unfold Qpoly Rpoly; simp +decide [ Polynomial.eval_prod, Polynomial.eval_finset_sum, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C ] ;

lemma Ppoly_eval_root (m : ℕ) (hm : 1 ≤ m) (hm' : m ≤ 70) : Ppoly.eval (r m) = 0 := by
  convert Ppoly_eval ( r m ) using 1;
  have h_sum : ∑ k ∈ Finset.Icc (1 : ℕ) 70, (k : ℝ) * (∏ j ∈ Finset.Icc (1 : ℕ) 70 \ {k}, (r m - j)) = (∏ k ∈ Finset.Icc (1 : ℕ) 70, (r m - k)) * (∑ k ∈ Finset.Icc (1 : ℕ) 70, (k : ℝ) / (r m - k)) := by
    rw [ Finset.mul_sum _ _ _ ];
    refine' Finset.sum_congr rfl fun x hx => _;
    rw [ Finset.prod_eq_prod_diff_singleton_mul hx ];
    grind +suggestions;
  simp_all +decide [ Finset.sdiff_singleton_eq_erase ];
  rw [ show ( ∑ k ∈ Finset.Icc ( 1 : ℕ ) 70, ( k : ℝ ) / ( r m - k ) ) = 5 / 4 by simpa [ f ] using r_spec m hm hm' |>.2.2.1 ] ; ring

lemma r_injOn : Set.InjOn r (Finset.Icc (1 : ℕ) 70 : Finset ℕ) := by
  intro a ha b hb hab;
  by_contra h_neq;
  cases lt_or_gt_of_ne h_neq <;> simp_all +decide;
  · have := r_lt a ha.1 ( by linarith );
    linarith [ show ( a : ℝ ) + 1 ≤ b by norm_cast, r_gt b hb.1 hb.2 ];
  · have := r_lt b hb.1 ( by linarith );
    linarith [ show ( b : ℝ ) + 1 ≤ a by norm_cast, r_gt a ha.1 ha.2 ]

lemma Ppoly_roots_eq : Ppoly.roots = (Finset.Icc (1 : ℕ) 70).val.map r := by
  refine' Eq.symm ( Multiset.eq_of_le_of_card_le _ _ );
  · refine' Multiset.le_iff_count.mpr fun x => _;
    by_cases hx : x ∈ Finset.image r ( Finset.Icc 1 70 );
    · rw [ Multiset.count_eq_one_of_mem ];
      · refine' Nat.pos_of_ne_zero _;
        simp +zetaDelta at *;
        exact ⟨ by obtain ⟨ a, ⟨ ha₁, ha₂ ⟩, rfl ⟩ := hx; exact Ppoly_eval_root a ha₁ ha₂, Ppoly_ne_zero ⟩;
      · exact Multiset.Nodup.map_on ( fun a ha b hb hab => by simpa using r_injOn ha hb hab ) ( Finset.nodup _ );
      · aesop;
    · rw [ Multiset.count_eq_zero.mpr ] <;> aesop;
  · refine' le_trans ( Polynomial.card_roots' _ ) _;
    rw [ Ppoly_natDegree ] ; norm_num

lemma Ppoly_roots_sum : Ppoly.roots.sum = 4473 := by
  have h_coeff : Ppoly.coeff 69 = Ppoly.leadingCoeff * (-1)^(70 - 69) * Ppoly.roots.sum := by
    rw [ Polynomial.coeff_eq_esymm_roots_of_card ];
    · norm_num [ Ppoly_natDegree, Multiset.esymm ];
      norm_num [ Multiset.powersetCard_one ];
    · rw [ Ppoly_roots_eq ] ; norm_num [ Ppoly_natDegree ] ;
    · rw [ Ppoly_natDegree ];
      norm_num;
  rw [ Ppoly_coeff69, Ppoly_leadingCoeff ] at h_coeff ; norm_num at h_coeff ; linarith

lemma sum_r : ∑ m ∈ Finset.Icc (1 : ℕ) 70, r m = 4473 := by
  rw [Finset.sum_eq_multiset_sum, ← Ppoly_roots_eq, Ppoly_roots_sum]

/-- The Vieta length computation. -/
lemma sum_lengths : ∑ m ∈ Finset.Icc (1 : ℕ) 70, (r m - (m : ℝ)) = 1988 := by
  rw [Finset.sum_sub_distrib, sum_r]
  have hsum : ∑ m ∈ Finset.Icc (1 : ℕ) 70, (m : ℝ) = 2485 := by
    rw [← Nat.cast_sum]
    norm_num [show (∑ m ∈ Finset.Icc (1 : ℕ) 70, m) = 2485 from by decide]
  rw [hsum]; norm_num

problem imo1988_p4 :
    ∃ (n : ℕ) (I : Fin n → Set ℝ),
      (∀ i, (I i).OrdConnected) ∧
      (Pairwise fun i j ↦ Disjoint (I i) (I j)) ∧
      (⋃ i, I i) =
        {x : ℝ | (5 : ℝ) / 4 ≤ ∑ k ∈ Finset.Icc (1 : ℕ) 70, (k : ℝ) / (x - k)} ∧
      ∑ i, MeasureTheory.volume (I i) = 1988 := by
  -- The set in the statement is `{x | 5/4 ≤ f x}`.
  have hfset : {x : ℝ | (5 : ℝ) / 4 ≤ ∑ k ∈ Finset.Icc (1 : ℕ) 70, (k : ℝ) / (x - k)}
      = {x : ℝ | 5 / 4 ≤ f x} := rfl
  refine ⟨70, fun i => J (i.val + 1), ?_, ?_, ?_, ?_⟩
  · intro i; exact J_ordConnected _
  · -- pairwise disjoint
    intro i j hij
    have hi : i.val + 1 ∈ Finset.Icc (1 : ℕ) 70 := by
      simp only [Finset.mem_Icc]; omega
    have hj : j.val + 1 ∈ Finset.Icc (1 : ℕ) 70 := by
      simp only [Finset.mem_Icc]; omega
    have hne : i.val + 1 ≠ j.val + 1 := by
      intro h; exact hij (Fin.ext (by omega))
    exact J_disjoint _ _ hi hj hne
  · -- union = S
    rw [hfset]
    ext x
    simp only [Set.mem_iUnion, Set.mem_setOf_eq]
    rw [mem_S_iff x]
    constructor
    · rintro ⟨i, hxi⟩
      exact ⟨i.val + 1, by omega, by have := i.isLt; omega, hxi⟩
    · rintro ⟨m, hm1, hm2, hxm⟩
      refine ⟨⟨m - 1, by omega⟩, ?_⟩
      show x ∈ J (m - 1 + 1)
      rwa [Nat.sub_add_cancel hm1]
  · -- sum of volumes
    change ∑ i : Fin 70, volume (J (i.val + 1)) = 1988
    have hbij : ∑ i : Fin 70, volume (J (i.val + 1))
        = ∑ m ∈ Finset.Icc (1 : ℕ) 70, volume (J m) := by
      rw [Finset.sum_bij (fun (i : Fin 70) _ => i.val + 1)]
      · intro i _; simp only [Finset.mem_Icc]; omega
      · intro i _ j _ h; exact Fin.ext (by omega)
      · intro m hm; rw [Finset.mem_Icc] at hm
        exact ⟨⟨m - 1, by omega⟩, Finset.mem_univ _, by simp; omega⟩
      · intro i _; rfl
    rw [hbij]
    have step : ∑ m ∈ Finset.Icc (1 : ℕ) 70, volume (J m)
        = ∑ m ∈ Finset.Icc (1 : ℕ) 70, ENNReal.ofReal (r m - m) := by
      apply Finset.sum_congr rfl
      intro m hm; rw [Finset.mem_Icc] at hm; exact volume_J m hm.1 hm.2
    rw [step, ← ENNReal.ofReal_sum_of_nonneg (fun m hm => by
      rw [Finset.mem_Icc] at hm
      have := r_gt m hm.1 hm.2
      linarith), sum_lengths]
    norm_num

end Imo1988P4