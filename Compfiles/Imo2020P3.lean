import Mathlib
import ProblemExtraction

problem_file { tags := [.Combinatorics] }

namespace Imo2020P3

open scoped Finset

private def partner (n : ℕ) (i : Fin (4 * n)) : Fin (4 * n) :=
  ⟨4 * n - 1 - i.val, by omega⟩

private lemma partner_invol (n : ℕ) (i : Fin (4 * n)) :
    partner n (partner n i) = i := by
  apply Fin.ext
  simp only [partner]
  omega

private lemma partner_ne (n : ℕ) (hn : 0 < n) (i : Fin (4 * n)) : partner n i ≠ i := by
  have hn' := Nat.mul_le_mul_left 4 hn
  intro hi
  have := congrArg Fin.val hi
  change 4 * n - 1 - i.val = i.val at this
  omega

private def lowerPebble (n : ℕ) (e : Fin (2 * n)) : Fin (4 * n) :=
  ⟨e.val, by omega⟩

private lemma pebble_eq_lower_or_partner (n : ℕ) (j : Fin (4 * n)) :
    ∃ e : Fin (2 * n), j = lowerPebble n e ∨ j = partner n (lowerPebble n e) := by
  by_cases hj : j.val < 2 * n
  · exact ⟨⟨j, hj⟩, Or.inl (Fin.ext (by simp [lowerPebble]))⟩
  · use ⟨4 * n - 1 - j.val, by omega⟩
    right
    apply Fin.ext
    simp only [lowerPebble, partner]
    omega

private lemma color_pair_hall {n : ℕ} {c : Fin (4 * n) → Fin n}
    (h : ∀ i, #{j | c j = i} = 4) (A : Finset (Fin n × Fin 2)) :
    A.card ≤ #{e : Fin (2 * n) |
      ∃ a ∈ A, c (lowerPebble n e) = a.1 ∨ c (partner n (lowerPebble n e)) = a.1} := by
  -- Let $B = \{i \mid \exists j, (i, j) \in A\}$.
  set B := Finset.image Prod.fst A with hB_def;
  -- The disjoint union of the four-element color fibers over $B$ has cardinality $4 \cdot \text{card}(B)$.
  have h_union : (Finset.biUnion B (fun i => Finset.filter (fun j => c j = i) Finset.univ)).card = 4 * B.card := by
    rw [ Finset.card_biUnion ];
    · simp_all +decide [ mul_comm ];
    · exact fun i hi j hj hij => Finset.disjoint_left.mpr fun x hx₁ hx₂ => hij <| by aesop;
  -- It injects into the union of the two endpoint images of the incident-pair set, whose cardinality is at most $2 \cdot \text{RHS}$.
  have h_inj : (Finset.biUnion B (fun i => Finset.filter (fun j => c j = i) Finset.univ)).card ≤ 2 * (Finset.filter (fun e => ∃ a ∈ A, c (lowerPebble n e) = a.1 ∨ c (partner n (lowerPebble n e)) = a.1) Finset.univ).card := by
    have h_inj : (Finset.biUnion B (fun i => Finset.filter (fun j => c j = i) Finset.univ)) ⊆ Finset.image (fun e => lowerPebble n e) (Finset.filter (fun e => ∃ a ∈ A, c (lowerPebble n e) = a.1 ∨ c (partner n (lowerPebble n e)) = a.1) Finset.univ) ∪ Finset.image (fun e => partner n (lowerPebble n e)) (Finset.filter (fun e => ∃ a ∈ A, c (lowerPebble n e) = a.1 ∨ c (partner n (lowerPebble n e)) = a.1) Finset.univ) := by
      intro j hj; simp_all +decide ;
      rcases pebble_eq_lower_or_partner n j with ⟨ e, he ⟩ ; use Or.imp ( fun h => ⟨ e, ⟨ _, hj, by aesop ⟩, by aesop ⟩ ) ( fun h => ⟨ e, ⟨ _, hj, by aesop ⟩, by aesop ⟩ ) he;
    exact le_trans ( Finset.card_le_card h_inj ) ( by exact le_trans ( Finset.card_union_le _ _ ) ( by exact le_trans ( add_le_add ( Finset.card_image_le ) ( Finset.card_image_le ) ) ( by linarith ) ) );
  have := Finset.card_le_card ( show A ⊆ Finset.image ( fun i : Fin n × Fin 2 => ( i.1, i.2 ) ) ( B ×ˢ Finset.univ ) from fun x hx => Finset.mem_image.mpr ⟨ ( x.1, x.2 ), Finset.mem_product.mpr ⟨ Finset.mem_image_of_mem _ hx, Finset.mem_univ _ ⟩, rfl ⟩ ) ; simp_all +decide ;
  linarith

/-
Orient every complementary pair so exactly two pairs point from each color.
-/
private lemma exists_balanced_orientation {n : ℕ} {c : Fin (4 * n) → Fin n}
    (h : ∀ i, #{j | c j = i} = 4) :
    ∃ O : Finset (Fin (4 * n)),
      (∀ x, x ∈ O ↔ partner n x ∉ O) ∧ ∀ i, #{x ∈ O | c x = i} = 2 := by
  -- Apply Finset.all_card_le_biUnion_card_iff_exists_injective to t(a)={incident pair indices}; color_pair_hall supplies Hall.
  have h_injective : ∃ f : Fin n × Fin 2 → Fin (2 * n), Function.Injective f ∧ ∀ a : Fin n × Fin 2, c (lowerPebble n (f a)) = a.1 ∨ c (partner n (lowerPebble n (f a))) = a.1 := by
    have h_injective : ∀ (A : Finset (Fin n × Fin 2)), A.card ≤ Finset.card (Finset.biUnion A (fun a => Finset.filter (fun e => c (lowerPebble n e) = a.1 ∨ c (partner n (lowerPebble n e)) = a.1) Finset.univ)) := by
      intro A; exact (by
      convert color_pair_hall h A using 1;
      exact congr_arg Finset.card ( by ext; aesop ));
    generalize_proofs at *;
    have := Finset.all_card_le_biUnion_card_iff_exists_injective ( fun a : Fin n × Fin 2 => Finset.filter ( fun e : Fin ( 2 * n ) => c ( lowerPebble n e ) = a.1 ∨ c ( partner n ( lowerPebble n e ) ) = a.1 ) Finset.univ ) ; aesop;
  cases' h_injective with f hf_inj
  have h_surjective : Function.Surjective f := by
    exact ( Fintype.bijective_iff_injective_and_card f ).mpr ⟨ hf_inj.1, by simp +decide [ mul_comm ] ⟩ |>.2;
  -- Define chosen endpoint $g(a)$ to be $lowerPebble(f(a))$ if its color $= a.1$, otherwise $partner$; incidence guarantees $c(g(a)) = a.1$.
  set g : Fin n × Fin 2 → Fin (4 * n) := fun a => if c (lowerPebble n (f a)) = a.1 then lowerPebble n (f a) else partner n (lowerPebble n (f a)) with hg_def
  have hg_color : ∀ a : Fin n × Fin 2, c (g a) = a.1 := by
    grind +ring
  have hg_inj : Function.Injective g := by
    intro a b; have := @hf_inj.1 a b; simp_all +decide [ Function.Injective.eq_iff hf_inj.1 ] ;
    grind +suggestions
  have hg_complement : ∀ x : Fin (4 * n), x ∈ Set.range g ↔ partner n x ∉ Set.range g := by
    intro x
    constructor
    · intro hx
      obtain ⟨a, ha⟩ := hx
      have h_partner : partner n x ∈ Set.range g → False := by
        grind +suggestions
      exact h_partner
    · intro hx
      have h_partner : partner n x ∈ Set.range g → False := by
        exact hx
      have h_exists : ∃ a : Fin n × Fin 2, g a = x ∨ g a = partner n x := by
        obtain ⟨a, ha⟩ : ∃ a : Fin n × Fin 2, lowerPebble n (f a) = x ∨ lowerPebble n (f a) = partner n x := by
          obtain ⟨a, ha⟩ : ∃ a : Fin (2 * n), lowerPebble n a = x ∨ lowerPebble n a = partner n x := by
            obtain ⟨a, ha⟩ : ∃ a : Fin (2 * n), lowerPebble n a = x ∨ lowerPebble n a = partner n x := by
              have h_exists : x.val < 2 * n ∨ (4 * n - 1 - x.val) < 2 * n := by
                exact Classical.or_iff_not_imp_left.2 fun h => by omega;
              cases' h_exists with h_exists h_exists <;> [ exact ⟨ ⟨ x, by linarith ⟩, Or.inl <| Fin.ext <| by simp +decide [ lowerPebble ] ⟩ ; exact ⟨ ⟨ 4 * n - 1 - x, by linarith ⟩, Or.inr <| Fin.ext <| by simp +decide [ lowerPebble, partner ] ⟩ ] ;
            generalize_proofs at *; (
            use a)
          obtain ⟨b, hb⟩ : ∃ b : Fin n × Fin 2, f b = a := h_surjective a
          use b
          simp [ha, hb]
        use a
        simp [hg_def];
        cases ha <;> simp +decide [ * ];
        · grind +ring;
        · simp +decide [ partner_invol ];
          grind +ring
      obtain ⟨a, ha⟩ := h_exists
      have h_choose : g a = x := by
        exact ha.resolve_right fun h => h_partner <| h ▸ Set.mem_range_self a
      exact ⟨a, h_choose⟩
  have hg_card : ∀ i : Fin n, (Finset.filter (fun x => c x = i) (Finset.image g Finset.univ)).card = 2 := by
    intro i; rw [ Finset.card_filter ] ; rw [ Finset.sum_image <| by tauto ] ; simp +decide [ hg_color ] ;
    rw [ show ( Finset.filter ( fun x : Fin n × Fin 2 => x.1 = i ) Finset.univ : Finset ( Fin n × Fin 2 ) ) = Finset.image ( fun j : Fin 2 => ( i, j ) ) Finset.univ from by ext ⟨ x, y ⟩ ; aesop ] ; rw [ Finset.card_image_of_injective ] <;> norm_num [ Function.Injective ] ;
  exact ⟨ Finset.image g Finset.univ, fun x => by simpa using hg_complement x, hg_card ⟩

/-
A finite directed multigraph with indegree and outdegree two has a directed
cycle cover.
-/
private lemma exists_directed_cycle_cover {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] (p : α → α) (c : α → β) (O : Finset α)
    (_hp : Function.Involutive p)
    (hout : ∀ i, #{x ∈ O | c x = i} = 2)
    (hin : ∀ i, #{x ∈ O | c (p x) = i} = 2) :
    ∃ M : Finset α, M ⊆ O ∧ (∀ i, #{x ∈ M | c x = i} = 1) ∧
      ∀ i, #{x ∈ M | c (p x) = i} = 1 := by
  set K := fun i => Finset.filter (fun x => c x = i) O;
  -- By Hall's theorem, there exists a perfect matching in the bipartite graph.
  have h_hall : ∀ S : Finset β, Finset.card (Finset.biUnion S (fun i => Finset.image (fun x => c (p x)) (K i))) ≥ Finset.card S := by
    intro S
    have h_card : ∑ i ∈ S, Finset.card (K i) ≤ ∑ i ∈ Finset.biUnion S (fun i => Finset.image (fun x => c (p x)) (K i)), Finset.card (Finset.filter (fun x => c (p x) = i) O) := by
      have h_card : ∑ i ∈ S, Finset.card (K i) ≤ ∑ i ∈ S, ∑ j ∈ Finset.biUnion S (fun i => Finset.image (fun x => c (p x)) (K i)), Finset.card (Finset.filter (fun x => c (p x) = j) (K i)) := by
        refine' Finset.sum_le_sum fun i hi => _;
        rw [ ← Finset.card_eq_sum_card_fiberwise ];
        exact fun x hx => Finset.mem_biUnion.mpr ⟨ i, hi, Finset.mem_image_of_mem _ hx ⟩;
      refine' le_trans h_card _;
      rw [ Finset.sum_comm ];
      gcongr;
      rw [ ← Finset.card_biUnion ];
      · exact Finset.card_le_card fun x hx => by aesop;
      · exact fun x hx y hy hxy => Finset.disjoint_left.mpr fun z hz₁ hz₂ => hxy <| by aesop;
    simp +zetaDelta at *;
    simp_all +decide;
  obtain ⟨f, hf⟩ : ∃ f : β → α, (∀ i, f i ∈ K i) ∧ (∀ i j, i ≠ j → c (p (f i)) ≠ c (p (f j))) := by
    have h_hall : ∃ f : β → β, (∀ i, f i ∈ Finset.image (fun x => c (p x)) (K i)) ∧ (∀ i j, i ≠ j → f i ≠ f j) := by
      have := Finset.all_card_le_biUnion_card_iff_exists_injective ( fun i => Finset.image ( fun x => c ( p x ) ) ( K i ) ) ; simp_all +decide ;
      exact ⟨ h_hall.choose, h_hall.choose_spec.2, fun i j hij => h_hall.choose_spec.1.ne hij ⟩;
    obtain ⟨ f, hf₁, hf₂ ⟩ := h_hall; choose g hg using fun i => Finset.mem_image.mp ( hf₁ i ) ; use g; aesop;
  refine' ⟨ Finset.image f Finset.univ, _, _, _ ⟩ <;> simp_all +decide [ Finset.subset_iff ];
  · exact fun i => Finset.mem_filter.mp ( hf.1 i ) |>.1;
  · intro i; rw [ Finset.card_eq_one ] ; use f i; ext x; aesop;
  · intro i; rw [ Finset.card_eq_one ] ; use f ( Classical.choose ( show ∃ j, c ( p ( f j ) ) = i from by
                                                                      have h_surj : Finset.image (fun j => c (p (f j))) Finset.univ = Finset.univ := by
                                                                        exact Finset.eq_of_subset_of_card_le ( Finset.subset_univ _ ) ( by rw [ Finset.card_image_of_injective _ fun i j hij => not_imp_not.mp ( hf.2 i j ) hij ] );
                                                                      exact Finset.mem_image.mp ( h_surj.symm ▸ Finset.mem_univ i ) |> Exists.imp fun j hj => hj.2 ) ) ; ext x; simp_all +decide [ Finset.mem_image ] ;
    grind

/-
The edges of a balanced orientation have a directed cycle cover.
-/
private lemma regular_involution_bisection {n : ℕ} {c : Fin (4 * n) → Fin n}
    (h : ∀ i, #{j | c j = i} = 4) :
    ∃ S : Finset (Fin (4 * n)),
      (∀ x, x ∈ S ↔ partner n x ∈ S) ∧ ∀ i, #{x ∈ S | c x = i} = 2 := by
  by_contra h_contra;
  obtain ⟨O, hO⟩ := exists_balanced_orientation h;
  obtain ⟨M, hM⟩ : ∃ M : Finset (Fin (4 * n)), M ⊆ O ∧ (∀ i, #{x ∈ M | c x = i} = 1) ∧ (∀ i, #{x ∈ M | c (partner n x) = i} = 1) := by
    apply exists_directed_cycle_cover (partner n) c O (partner_invol n) (hO.right) (by
    intro i
    have h_card : Finset.card (Finset.filter (fun x => c (partner n x) = i) O) = Finset.card (Finset.filter (fun x => c x = i) (Finset.univ \ O)) := by
      refine' Finset.card_bij ( fun x hx => partner n x ) _ _ _ <;> simp +contextual;
      · exact fun x hx hx' => hO.1 x |>.1 hx;
      · exact fun x hx₁ hx₂ y hy₁ hy₂ hxy => by simpa [ partner_invol ] using congr_arg ( fun z => partner n z ) hxy;
      · grind +suggestions;
    simp_all +decide;
    have h_card : Finset.card (Finset.filter (fun x => c x = i) Finset.univ) = Finset.card (Finset.filter (fun x => c x = i) O) + Finset.card (Finset.filter (fun x => c x = i) (Finset.univ \ O)) := by
      rw [ ← Finset.card_union_of_disjoint ];
      · congr with x ; by_cases hx : x ∈ O <;> simp +decide [ hx ];
      · exact Finset.disjoint_left.mpr fun x hx₁ hx₂ => Finset.mem_sdiff.mp ( Finset.mem_filter.mp hx₂ |>.1 ) |>.2 ( Finset.mem_filter.mp hx₁ |>.1 );
    linarith [ h i, hO.2 i ]);
  refine' h_contra ⟨ M ∪ Finset.image ( fun x => partner n x ) M, _, _ ⟩ <;> simp +decide [ Finset.subset_iff ] at *;
  · grind +suggestions;
  · intro i; rw [ Finset.filter_union, Finset.card_union_of_disjoint ] ; simp +decide [ Finset.filter_image, hM ] ;
    · rw [ Finset.card_image_of_injective _ fun x y hxy => by simpa [ partner_invol ] using congr_arg ( fun z => partner n z ) hxy ] ; simp +decide [ hM.2.2 ];
    · simp +contextual [ Finset.disjoint_left ];
      grind

private lemma selected_pair_sum {n : ℕ} (S : Finset (Fin (4 * n)))
    (hpair : ∀ i, i ∈ S ↔ partner n i ∈ S)
    (hcard : S.card = 2 * n) :
    ∑ i ∈ S, ((i : ℕ) + 1) = n * (4 * n + 1) := by
  have hsum : ∑ i ∈ S, (i.val + 1) = ∑ i ∈ S, ((4 * n - 1 - i.val) + 1) := by
    apply Finset.sum_bij (fun i _ => partner n i)
    · exact fun i hi => (hpair i).1 hi
    · intro i _ j _ hij
      simpa [partner_invol] using congrArg (fun x => partner n x) hij
    · exact fun i hi => ⟨partner n i, (hpair i).1 hi, partner_invol n i⟩
    · simp only [partner]
      exact fun i _ => by
        rw [Nat.sub_sub_self (Nat.le_sub_one_of_lt (Fin.is_lt i))]
  have hadd : ∑ i ∈ S, (i.val + 1) + ∑ i ∈ S, ((4 * n - 1 - i.val) + 1) =
      ∑ _i ∈ S, (4 * n + 1) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by
      linarith [Nat.sub_add_cancel (show 1 ≤ 4 * n from by linarith [Fin.is_lt i]),
        Nat.sub_add_cancel (Nat.le_sub_one_of_lt (Fin.is_lt i))]
  norm_num [hcard] at hadd
  linarith

private lemma total_weight (n : ℕ) :
    ∑ i : Fin (4 * n), ((i : ℕ) + 1) = 2 * n * (4 * n + 1) := by
  have hsum : ∑ i ∈ Finset.range (4 * n), (i + 1) = 2 * n * (4 * n + 1) := by
    induction n with
    | zero => norm_num
    | succ n ih =>
      norm_num [Nat.mul_succ, Finset.sum_range_succ] at *
      linarith
  rw [← hsum, Finset.sum_range]

problem imo2020_p3 {n : ℕ} {c : Fin (4 * n) → Fin n} (h : ∀ i, #{j | c j = i} = 4) :
    ∃ S : Finset (Fin (4 * n)), ∑ i ∈ S, ((i : ℕ) + 1) = ∑ i ∈ Sᶜ, ((i : ℕ) + 1) ∧
      ∀ i, #{j ∈ S | c j = i} = 2 := by
  by_cases hn : n = 0
  · subst hn
    exact ⟨∅, by simp, fun i => Fin.elim0 i⟩
  · obtain ⟨S, hS₁, hS₂⟩ := regular_involution_bisection h
    refine ⟨S, ?_, hS₂⟩
    have hsum : ∑ i ∈ S, (i.val + 1) = n * (4 * n + 1) := by
      apply selected_pair_sum S hS₁
      have hcard : ∑ i : Fin n, (Finset.filter (fun x => c x = i) S).card = S.card := by
        simp only [Finset.card_eq_sum_ones, Finset.sum_fiberwise]
      simp_all [mul_comm]
    have htotal : ∑ i ∈ S, (i.val + 1) + ∑ i ∈ Sᶜ, (i.val + 1) =
        2 * n * (4 * n + 1) := by
      rw [Finset.sum_add_sum_compl]
      exact total_weight n
    nlinarith

end Imo2020P3
