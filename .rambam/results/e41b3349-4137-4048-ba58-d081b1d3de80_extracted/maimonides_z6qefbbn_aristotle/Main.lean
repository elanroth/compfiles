import Mathlib

open scoped Cardinal

namespace Imo2022P6

abbrev Cell (n : ℕ) : Type := Fin n × Fin n

abbrev NordicSquare (n : ℕ) : Type := Cell n ≃ Finset.Icc 1 (n ^ 2)

def Adjacent {n : ℕ} (x y : Cell n) : Prop :=
  Nat.dist x.1 y.1 + Nat.dist x.2 y.2 = 1

def NordicSquare.Valley {n : ℕ} (ns : NordicSquare n) (c : Cell n) : Prop :=
  ∀ c' : Cell n, Adjacent c c' → (ns c : ℕ) < (ns c' : ℕ)

structure NordicSquare.UphillPath {n : ℕ} (ns : NordicSquare n) where
  cells : List (Cell n)
  nonempty : cells ≠ []
  first_valley : ns.Valley (cells.head nonempty)
  adjacent : cells.IsChain Adjacent
  increasing : cells.IsChain fun x y ↦ (ns x : ℕ) < (ns y : ℕ)

def answer : ℕ+ → ℕ := fun n => 2 * n^2 - 2 * n + 1

/-! ## Basic infrastructure -/

lemma Adjacent.symm {n : ℕ} {x y : Cell n} (h : Adjacent x y) : Adjacent y x := by
  unfold Adjacent at h ⊢; simp_all +decide [Nat.dist_comm]

instance {n : ℕ} : DecidableRel (@Adjacent n) :=
  fun x y => inferInstanceAs (Decidable (Nat.dist x.1 y.1 + Nat.dist x.2 y.2 = 1))

/-
PROVIDED SOLUTION
Adjacent means Nat.dist x.1 y.1 + Nat.dist x.2 y.2 = 1. If x = y, then both Nat.dist are 0, so the sum is 0 ≠ 1.
-/
lemma Adjacent.ne {n : ℕ} {x y : Cell n} (h : Adjacent x y) : x ≠ y := by
  unfold Adjacent at h; aesop;

/-
PROVIDED SOLUTION
Given hmin: ∀ c', (ns c : ℕ) ≤ (ns c' : ℕ). Need to show: for all c' adjacent to c, ns c < ns c'. Given adj c c', we have ns c ≤ ns c' by hmin. For strict inequality, note that c ≠ c' (by Adjacent.ne) and ns is injective (it's an Equiv), so ns c ≠ ns c'. Combined with ns c ≤ ns c', this gives ns c < ns c'.
-/
lemma min_cell_is_valley {n : ℕ} [NeZero n] (ns : NordicSquare n) (c : Cell n)
    (hmin : ∀ c' : Cell n, (ns c : ℕ) ≤ (ns c' : ℕ)) : ns.Valley c := by
  intro c' hc';
  refine' lt_of_le_of_ne ( hmin c' ) _;
  have := ns.injective.ne ( show c ≠ c' from by
                              exact? ) ; aesop;

/-
PROVIDED SOLUTION
Find the cell c with minimum ns-value using Finset.exists_min_image on Finset.univ. Then c satisfies hmin : ∀ c', ns c ≤ ns c'. Apply min_cell_is_valley.
-/
lemma exists_valley {n : ℕ} [NeZero n] (ns : NordicSquare n) : ∃ c, ns.Valley c := by
  obtain ⟨c, hc⟩ : ∃ c : Cell n, ∀ c' : Cell n, (ns c : ℕ) ≤ (ns c' : ℕ) := by
    simpa using Finset.exists_min_image Finset.univ ( fun c => ( ns c : ℕ ) ) ⟨ ( 0, 0 ), Finset.mem_univ _ ⟩;
  use c;
  exact?

/-
PROVIDED SOLUTION
¬Valley c means ∃ c', Adjacent c c' ∧ ¬(ns c < ns c'). Since ns values are natural numbers, ¬(ns c < ns c') means ns c' ≤ ns c. Since c ≠ c' (by Adjacent.ne) and ns is injective (Equiv), ns c ≠ ns c'. So ns c' ≤ ns c and ns c' ≠ ns c gives ns c' < ns c.
-/
lemma non_valley_has_strictly_smaller_neighbor {n : ℕ} (ns : NordicSquare n) (c : Cell n)
    (hnv : ¬ns.Valley c) : ∃ c', Adjacent c c' ∧ (ns c' : ℕ) < (ns c : ℕ) := by
  -- By definition of Valley, if ¬ns.Valley c, then there exists a cell c' adjacent to c such that ns c' ≤ ns c.
  obtain ⟨c', hc'⟩ : ∃ c', Adjacent c c' ∧ (ns c' : ℕ) ≤ (ns c : ℕ) := by
    exact not_forall_not.mp fun h => hnv fun c' hc' => not_le.mp fun hle => h c' <| by tauto;
  cases lt_or_eq_of_le hc'.2 <;> simp_all +decide [ Equiv.injective ];
  · exact ⟨ _, _, hc'.1, by assumption ⟩;
  · unfold Adjacent at hc'; aesop;

def valley_path {n : ℕ} (ns : NordicSquare n) (c : Cell n)
    (hv : ns.Valley c) : ns.UphillPath :=
  ⟨[c], List.cons_ne_nil _ _, by simpa using hv,
   List.isChain_singleton _, List.isChain_singleton _⟩

@[ext]
lemma UphillPath.ext' {n : ℕ} {ns : NordicSquare n} (p q : ns.UphillPath)
    (h : p.cells = q.cells) : p = q := by
  cases p; cases q; simp at h; subst h; rfl

/-
PROVIDED SOLUTION
p.increasing says cells.IsChain (fun x y => (ns x : ℕ) < (ns y : ℕ)). IsChain with strict less-than implies Pairwise strict less-than (by List.IsChain.pairwise). Pairwise (· < ·) on the mapped values implies the mapped list is Nodup. Since ns is injective, the original list is also Nodup. Use List.Nodup.of_map.
-/
lemma UphillPath.cells_nodup {n : ℕ} {ns : NordicSquare n} (p : ns.UphillPath) :
    p.cells.Nodup := by
  -- Since the cell values are strictly increasing and the cells are distinct, the list of cells must be nodup.
  have h_values_nodup : List.Pairwise (fun x y => x < y) (List.map (fun c => (ns c : ℕ)) p.cells) := by
    convert p.increasing using 1;
    rw [ List.pairwise_map, List.isChain_iff_get ];
    rw [ List.pairwise_iff_get ];
    constructor;
    · exact fun h i => h _ _ ( Nat.lt_succ_self _ );
    · intro h i j hij;
      induction' j with j ih;
      induction' j with j ih generalizing i;
      · tauto;
      · rcases eq_or_lt_of_le ( show i ≤ ⟨ j, by linarith ⟩ from Nat.le_of_lt_succ hij ) with rfl | hij <;> simp_all +decide [ Fin.add_def, Nat.mod_eq_of_lt ];
        · convert h ⟨ j, Nat.lt_pred_iff.mpr ‹_› ⟩ using 1;
        · exact lt_trans ( ih _ ( by linarith ) hij ) ( h ⟨ j, by omega ⟩ );
  exact List.Nodup.of_map ( fun x => ( ns x : ℕ ) ) ( List.Pairwise.nodup h_values_nodup )

/-
PROVIDED SOLUTION
Show Finite ns.UphillPath by embedding into Finset (Cell n) via p ↦ p.cells.toFinset.

Injectivity: if p.cells.toFinset = q.cells.toFinset, then since both are Nodup (by UphillPath.cells_nodup), they are permutations of each other (use List.Nodup.perm_iff_toFinset_eq or List.perm_iff_count). Since both are sorted by the strict order (fun x y => (ns x : ℕ) < (ns y : ℕ)) (from increasing, which gives Pairwise via IsChain.pairwise), they must be equal (use List.Perm.eq_of_pairwise with the asymmetry of <, or List.Perm.eq_of_sorted_of_sorted).

Then use Fintype.ofFinite.
-/
noncomputable instance uphillPath_fintype {n : ℕ} (ns : NordicSquare n) :
    Fintype ns.UphillPath := by
  suffices Finite ns.UphillPath from Fintype.ofFinite _
  have instTrans : Trans (fun x y : Cell n => (ns x : ℕ) < (ns y : ℕ))
      (fun x y : Cell n => (ns x : ℕ) < (ns y : ℕ))
      (fun x y : Cell n => (ns x : ℕ) < (ns y : ℕ)) := ⟨lt_trans⟩
  exact Finite.of_injective (fun p : ns.UphillPath => p.cells.toFinset) (by
    intro p q h
    exact UphillPath.ext' p q <|
      (List.perm_of_nodup_nodup_toFinset_eq (UphillPath.cells_nodup p) (UphillPath.cells_nodup q) h).eq_of_pairwise
        (fun a b _ _ (hab : (ns a : ℕ) < _) hba => absurd hab (not_lt.mpr (le_of_lt hba)))
        (p.increasing.pairwise) (q.increasing.pairwise))

/-
PROVIDED SOLUTION
answer n = 2 * n^2 - 2 * n + 1. Need to show 2 * n^2 - 2 * n + 1 = 2 * n * (n - 1) + 1. Since n : ℕ+ means (n : ℕ) ≥ 1, we have n * (n-1) = n^2 - n when n ≥ 1. So 2*n*(n-1) = 2*n^2 - 2*n, and 2*n*(n-1)+1 = 2*n^2 - 2*n + 1. Unfold answer and use omega or nlinarith with n.pos.
-/
lemma answer_eq (n : ℕ+) : answer n = 2 * (n : ℕ) * ((n : ℕ) - 1) + 1 := by
  unfold answer; exact by rw [ Nat.mul_sub_left_distrib ] ; ring;

/-! ## Key sub-lemmas for lower bound -/

/-
PROVIDED SOLUTION
By strong induction on (ns c : ℕ).

Base case: if c is a valley, the singleton path [c] (valley_path ns c hv) ends at c.

Inductive step: if c is not a valley, by non_valley_has_strictly_smaller_neighbor, there exists c' adjacent to c with (ns c' : ℕ) < (ns c : ℕ). By the induction hypothesis, there exists an uphill path p ending at c'. By extend_path (or direct construction), append c to p to get a path ending at c.

For the path extension: the new path is p.cells ++ [c]. This is valid because:
- The last cell of p is c', which is adjacent to c
- ns(c') < ns(c) (strictly increasing)
- The path starts at a valley (same as p)
- Adjacent and increasing chains extend correctly
-/
lemma exists_path_ending_at {n : ℕ} [NeZero n] (ns : NordicSquare n) (c : Cell n) :
    ∃ p : ns.UphillPath, p.cells.getLast p.nonempty = c := by
  -- By induction on the value of `ns c`, we can show that there exists an uphill path ending at `c`.
  induction' k : (ns c).val using Nat.strong_induction_on with k ih generalizing c;
  by_cases hc : ns.Valley c;
  · exact ⟨ valley_path ns c hc, rfl ⟩;
  · obtain ⟨c', hc'⟩ : ∃ c' : Cell n, Adjacent c c' ∧ (ns c' : ℕ) < (ns c : ℕ) := by
      exact?;
    obtain ⟨ p, hp ⟩ := ih _ ( by linarith ) _ rfl;
    use ⟨p.cells ++ [c], by
      aesop, by
      cases p ; aesop, by
      simp_all +decide [ List.isChain_iff_get ];
      intro i; rcases i with ⟨ i, hi ⟩ ; rcases lt_trichotomy i ( p.cells.length - 1 ) with hi' | rfl | hi' <;> simp_all +decide [ List.getElem_append ] ;
      · split_ifs <;> simp_all +decide [ List.getElem_append ];
        · have := p.adjacent; simp_all +decide [ List.isChain_iff_get ] ;
          exact this ⟨ i, hi' ⟩;
        · omega;
      · split_ifs <;> simp_all +decide [ Nat.sub_add_cancel ( show 1 ≤ p.cells.length from List.length_pos_iff.mpr p.nonempty ) ];
        · omega;
        · convert hc'.1.symm using 1;
          grind;
      · grind +ring, by
      simp_all +decide [ List.isChain_append ];
      exact ⟨ p.increasing, fun a b hab => by rw [ List.getLast?_eq_some_getLast p.nonempty ] at hab; aesop ⟩⟩
    generalize_proofs at *;
    grind +ring

/-
PROVIDED SOLUTION
Construct q with q.cells = p.cells ++ [b].

Need to verify all UphillPath conditions:
1. nonempty: p.cells ++ [b] is nonempty (p.cells is nonempty, and appending preserves this).
2. first_valley: head of p.cells ++ [b] is head of p.cells (since p.cells is nonempty), which is a valley by p.first_valley.
3. adjacent: p.cells.IsChain Adjacent. Need (p.cells ++ [b]).IsChain Adjacent. Use List.IsChain.append or list chain append. The key is that the last element of p.cells is adjacent to b (given by hadj). Use List.isChain_append_iff or similar.
4. increasing: similarly, use p.increasing and hinc.

For the chain append lemma: (l₁ ++ l₂).IsChain R ↔ l₁.IsChain R ∧ l₂.IsChain R ∧ (if l₁ is nonempty and l₂ is nonempty, then R (l₁.getLast ...) (l₂.head ...)).
-/
lemma extend_path {n : ℕ} (ns : NordicSquare n) (p : ns.UphillPath) (b : Cell n)
    (hadj : Adjacent (p.cells.getLast p.nonempty) b)
    (hinc : (ns (p.cells.getLast p.nonempty) : ℕ) < (ns b : ℕ)) :
    ∃ q : ns.UphillPath, q.cells = p.cells ++ [b] := by
  refine' ⟨ ⟨ p.cells ++ [ b ], _, _, _, _ ⟩, rfl ⟩ <;> simp_all +decide [ List.isChain_append ];
  · cases p ; aesop;
  · exact ⟨ p.adjacent, fun a b h => by rw [ List.getLast?_eq_some_iff ] at h; aesop ⟩;
  · refine' ⟨ p.increasing, _ ⟩;
    grind +ring

/-! ## Lower bound -/

/-
PROVIDED SOLUTION
Convert the Cardinal inequality to a Fintype.card inequality using Cardinal.mk_fintype and Nat.cast_le.

Then show: answer n ≤ Fintype.card ns.UphillPath.

Key insight: we construct a Finset of distinct UphillPaths of size ≥ answer n.

Step 1: Pick any valley v (by exists_valley). valley_path ns v hv is a path of length 1.

Step 2: For each pair (a, b) with Adjacent a b and (ns a : ℕ) < (ns b : ℕ):
  - Get a path p ending at a (by exists_path_ending_at ns a)
  - Extend it: extend_path ns p b gives a path q with q.cells = p.cells ++ [b]
  - q has length ≥ 2 and its last cell is b, second-to-last is a

Step 3: Map each path q to its "last pair" (second-to-last cell, last cell).
  - The singleton valley path maps to "nothing" (length 1)
  - Each edge path maps to (a, b)

This gives an injection from directed increasing edges to UphillPaths of length ≥ 2.
Combined with the singleton path, we get ≥ 1 + |directed edges| distinct paths.

Step 4: |directed edges| = 2n(n-1) because each undirected grid edge produces exactly one directed increasing edge (the endpoints have different values since ns is injective, so exactly one direction has smaller→larger).

Therefore Fintype.card ≥ 1 + 2n(n-1) = answer n.

Alternative: just show there are at least n^2 distinct UphillPaths (one ending at each cell, by exists_path_ending_at), giving #UphillPath ≥ n^2. Then note answer n = 2n^2 - 2n + 1 ≤ n^2 only for n ≤ 1... so this approach won't work for n ≥ 2. Need the full argument.
-/
set_option maxHeartbeats 1600000 in
lemma lower_bound {n : ℕ+} (ns : NordicSquare n) :
    (answer n : Cardinal) ≤ #ns.UphillPath := by
  have h_card : Fintype.card ns.UphillPath ≥ 1 + 2 * (n : ℕ) * ((n : ℕ) - 1) := by
    -- Let's count the number of directed increasing edges in the grid.
    have h_directed_edges : Finset.card (Finset.filter (fun e => (ns e.1 : ℕ) < (ns e.2 : ℕ)) (Finset.filter (fun e => Adjacent e.1 e.2) (Finset.univ : Finset (Cell n × Cell n)))) ≥ 2 * (n : ℕ) * ((n : ℕ) - 1) := by
      -- Each undirected edge in the grid corresponds to exactly one directed increasing edge.
      have h_directed_edges : Finset.card (Finset.filter (fun e => (ns e.1 : ℕ) < (ns e.2 : ℕ)) (Finset.filter (fun e => Adjacent e.1 e.2) (Finset.univ : Finset (Cell n × Cell n)))) = Finset.card (Finset.filter (fun e => (ns e.2 : ℕ) < (ns e.1 : ℕ)) (Finset.filter (fun e => Adjacent e.1 e.2) (Finset.univ : Finset (Cell n × Cell n)))) := by
        rw [ Finset.card_filter, Finset.card_filter ];
        apply Finset.sum_bij (fun p hp => (p.2, p.1));
        · simp +contextual [ Adjacent.symm ];
        · aesop;
        · simp +zetaDelta at *;
          exact?;
        · exact?;
      -- The total number of edges in the grid is $2n(n-1)$.
      have h_total_edges : Finset.card (Finset.filter (fun e => Adjacent e.1 e.2) (Finset.univ : Finset (Cell n × Cell n))) = 4 * (n : ℕ) * ((n : ℕ) - 1) := by
        -- The total number of edges in the grid is $2n(n-1)$ because each row has $n-1$ horizontal edges and each column has $n-1$ vertical edges.
        have h_total_edges : Finset.card (Finset.filter (fun e => Adjacent e.1 e.2) (Finset.univ : Finset (Cell n × Cell n))) = 2 * n * (n - 1) + 2 * n * (n - 1) := by
          have h_horizontal_edges : Finset.card (Finset.filter (fun e => e.1.1 = e.2.1 ∧ Nat.dist e.1.2 e.2.2 = 1) (Finset.univ : Finset (Cell n × Cell n))) = 2 * n * (n - 1) := by
            have h_horizontal_edges : Finset.card (Finset.filter (fun e => e.1.1 = e.2.1 ∧ Nat.dist e.1.2 e.2.2 = 1) (Finset.univ : Finset (Cell n × Cell n))) = Finset.sum (Finset.univ : Finset (Fin n)) (fun i => Finset.card (Finset.filter (fun j => Nat.dist j.1 j.2 = 1) (Finset.univ : Finset (Fin n × Fin n)))) := by
              rw [ show ( Finset.filter ( fun e : Cell n × Cell n => e.1.1 = e.2.1 ∧ Nat.dist e.1.2 e.2.2 = 1 ) Finset.univ ) = Finset.biUnion ( Finset.univ : Finset ( Fin n ) ) ( fun i => Finset.image ( fun j : Fin n × Fin n => ( ( i, j.1 ), ( i, j.2 ) ) ) ( Finset.filter ( fun j : Fin n × Fin n => Nat.dist j.1 j.2 = 1 ) Finset.univ ) ) from ?_, Finset.card_biUnion ];
              · exact Finset.sum_congr rfl fun _ _ => Finset.card_image_of_injective _ fun x y hxy => by aesop;
              · exact fun i _ j _ hij => Finset.disjoint_left.mpr fun x hx₁ hx₂ => hij <| by aesop;
              · ext ⟨⟨i, j⟩, ⟨k, l⟩⟩; simp [Finset.mem_biUnion, Finset.mem_image];
                tauto;
            -- The set of pairs (j, k) where |j - k| = 1 is equivalent to the set of pairs (j, j+1) and (j+1, j) for j in Fin n.
            have h_pairs : Finset.filter (fun j : Fin n × Fin n => Nat.dist j.1 j.2 = 1) (Finset.univ : Finset (Fin n × Fin n)) = Finset.image (fun j : Fin n => (j, j + 1)) (Finset.univ.filter (fun j : Fin n => j.val < n - 1)) ∪ Finset.image (fun j : Fin n => (j + 1, j)) (Finset.univ.filter (fun j : Fin n => j.val < n - 1)) := by
              ext ⟨i, j⟩; simp [Nat.dist];
              constructor <;> intro h <;> rcases lt_trichotomy ( i : ℕ ) j with hij | hij | hij <;> simp_all +decide [ Fin.ext_iff, Nat.dist.eq_def ];
              · exact Or.inl ⟨ lt_tsub_iff_right.mpr ( by linarith [ show ( i : ℕ ) < j from hij, Fin.is_lt i, Fin.is_lt j ] ), by simp +decide [ Fin.val_add, Nat.mod_eq_of_lt ( show ( i : ℕ ) + 1 < n from by linarith [ show ( i : ℕ ) < j from hij, Fin.is_lt i, Fin.is_lt j ] ) ] ; omega ⟩;
              · exact Or.inr ⟨ lt_of_lt_of_le hij ( Nat.le_sub_one_of_lt ( Fin.is_lt _ ) ), by norm_num [ Fin.val_add, Nat.mod_eq_of_lt ( show ( j : ℕ ) + 1 < n from Nat.lt_of_le_of_lt ( Nat.succ_le_of_lt hij ) ( Fin.is_lt _ ) ) ] ; omega ⟩;
              · cases h <;> simp_all +decide [ Fin.val_add, Nat.mod_eq_of_lt ];
                · rw [ Nat.mod_eq_of_lt ] at * <;> omega;
                · rw [ Nat.mod_eq_of_lt ] at * <;> omega;
              · cases h <;> simp_all +decide [ Fin.val_add ];
                · rw [ Nat.mod_eq_of_lt ] at * <;> omega;
                · rw [ Nat.mod_eq_of_lt ] at * <;> omega;
              · cases h <;> simp_all +decide [ Fin.val_add, Nat.mod_eq_of_lt ];
                · rw [ Nat.mod_eq_of_lt ] at * <;> omega;
                · rw [ Nat.mod_eq_of_lt ] at * <;> omega;
            rw [ h_horizontal_edges, Finset.sum_congr rfl fun _ _ => congr_arg Finset.card h_pairs ];
            rw [ Finset.sum_congr rfl fun _ _ => Finset.card_union_of_disjoint <| ?_ ];
            · rw [ Finset.card_image_of_injective, Finset.card_image_of_injective ] <;> norm_num [ Function.Injective ];
              rw [ show ( Finset.filter ( fun j : Fin n => ( j : ℕ ) < n - 1 ) Finset.univ : Finset ( Fin n ) ) = Finset.Iio ⟨ n - 1, Nat.sub_lt n.pos zero_lt_one ⟩ by ext; aesop ] ; norm_num ; ring;
            · norm_num [ Finset.disjoint_left ];
              intro a ha x hx h; rw [ Fin.ext_iff ] at *; simp_all +decide [ Fin.val_add ] ;
              rw [ Nat.mod_eq_of_lt ] at h <;> try linarith [ Nat.sub_add_cancel n.pos ];
              rw [ Nat.mod_eq_of_lt ] <;> linarith [ Nat.sub_add_cancel n.pos ]
          have h_vertical_edges : Finset.card (Finset.filter (fun e => e.1.2 = e.2.2 ∧ Nat.dist e.1.1 e.2.1 = 1) (Finset.univ : Finset (Cell n × Cell n))) = 2 * n * (n - 1) := by
            rw [ ← h_horizontal_edges ];
            rw [ Finset.card_filter, Finset.card_filter ];
            apply Finset.sum_bij (fun e _ => (e.1.swap, e.2.swap));
            · simp;
            · grind;
            · exact fun b _ => ⟨ ( b.1.swap, b.2.swap ), Finset.mem_univ _, by simp +decide ⟩;
            · simp +decide [ Nat.dist_comm ]
          convert congr_arg₂ ( · + · ) h_horizontal_edges h_vertical_edges using 1;
          rw [ ← Finset.card_union_of_disjoint ];
          · congr with e ; simp +decide [ Adjacent ];
            constructor <;> intro h <;> simp_all +decide [ Nat.dist.eq_def ];
            · omega;
            · omega;
          · rw [ Finset.disjoint_left ] ; aesop;
        exact h_total_edges.trans ( by ring );
      have h_total_edges : Finset.card (Finset.filter (fun e => (ns e.1 : ℕ) < (ns e.2 : ℕ)) (Finset.filter (fun e => Adjacent e.1 e.2) (Finset.univ : Finset (Cell n × Cell n)))) + Finset.card (Finset.filter (fun e => (ns e.2 : ℕ) < (ns e.1 : ℕ)) (Finset.filter (fun e => Adjacent e.1 e.2) (Finset.univ : Finset (Cell n × Cell n)))) = Finset.card (Finset.filter (fun e => Adjacent e.1 e.2) (Finset.univ : Finset (Cell n × Cell n))) := by
        rw [ Finset.card_filter, Finset.card_filter, Finset.card_filter ];
        rw [ ← Finset.sum_add_distrib, Finset.sum_filter ];
        refine' Finset.sum_congr rfl fun x hx => _;
        split_ifs <;> simp_all +decide [ lt_asymm ];
        exact absurd ( ns.injective ( le_antisymm ‹_› ‹_› ) ) ( by rintro h; have := ‹Adjacent x.1 x.2›; simp_all +decide [ Adjacent ] );
      grind;
    -- Each directed increasing edge corresponds to an uphill path of length 2.
    have h_uphill_paths : Finset.card (Finset.image (fun e => (exists_path_ending_at ns e.1).choose.cells ++ [e.2]) (Finset.filter (fun e => (ns e.1 : ℕ) < (ns e.2 : ℕ)) (Finset.filter (fun e => Adjacent e.1 e.2) (Finset.univ : Finset (Cell n × Cell n))))) ≥ 2 * (n : ℕ) * ((n : ℕ) - 1) := by
      rwa [ Finset.card_image_of_injOn ];
      intro e he e' he' h_eq;
      replace h_eq := congr_arg List.reverse h_eq ; simp_all +decide [ List.reverse_append ];
      grind;
    have h_uphill_paths : Finset.card (Finset.image (fun e => (exists_path_ending_at ns e.1).choose.cells ++ [e.2]) (Finset.filter (fun e => (ns e.1 : ℕ) < (ns e.2 : ℕ)) (Finset.filter (fun e => Adjacent e.1 e.2) (Finset.univ : Finset (Cell n × Cell n))))) + 1 ≤ Fintype.card ns.UphillPath := by
      refine' Nat.succ_le_of_lt ( lt_of_le_of_lt ( Finset.card_le_card _ ) _ );
      exact Finset.image ( fun p : ns.UphillPath => p.cells ) ( Finset.univ : Finset ns.UphillPath ) \ { [ ( exists_valley ns ).choose ] };
      · simp +decide [ Finset.subset_iff ];
        rintro _ a b c d h₁ h₂ rfl;
        refine' ⟨ _, _ ⟩;
        · have := Exists.choose_spec ( exists_path_ending_at ns ( a, b ) );
          exact extend_path ns _ _ ( by aesop ) ( by aesop );
        · intro h; have := congr_arg List.length h; norm_num at this;
          grind;
      · refine' lt_of_lt_of_le ( Finset.card_lt_card ( Finset.ssubset_iff_subset_ne.mpr _ ) ) _;
        exact Finset.image ( fun p : ns.UphillPath => p.cells ) Finset.univ;
        · simp +decide [ Finset.ext_iff ];
          exact ⟨ valley_path ns _ ( exists_valley ns |> Classical.choose_spec ), rfl ⟩;
        · exact Finset.card_image_le.trans ( by simp +decide );
    linarith;
  convert h_card.le using 1 ; norm_num [ answer_eq ] ; ring!;
  norm_cast

/-! ## Construction achieving equality -/

lemma exists_optimal (n : ℕ+) :
    ∃ ns : NordicSquare n, #ns.UphillPath = (answer n : ℕ) := by
  sorry

/-! ## Main theorem -/

theorem imo2022_p6 {n : ℕ+} :
    IsLeast {k : ℕ | ∃ ns : NordicSquare n, #ns.UphillPath = k} (answer n) := by
  refine ⟨?mem, ?lb⟩
  case mem =>
    obtain ⟨ns, hns⟩ := exists_optimal n
    exact ⟨ns, hns⟩
  case lb =>
    intro k ⟨ns, hk⟩
    have h := lower_bound ns
    rw [hk] at h
    exact_mod_cast h

end Imo2022P6