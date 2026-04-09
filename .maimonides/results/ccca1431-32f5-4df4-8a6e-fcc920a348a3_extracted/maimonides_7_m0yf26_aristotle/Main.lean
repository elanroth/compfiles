import Mathlib

open scoped Cardinal

namespace Imo2022P6

abbrev Cell (n : ℕ) : Type := Fin n × Fin n

abbrev NordicSquare (n : ℕ) : Type := Cell n ≃ Finset.Icc 1 (n ^ 2)

def Adjacent {n : ℕ} (x y : Cell n) : Prop :=
  Nat.dist x.1 y.1 + Nat.dist x.2 y.2 = 1

instance {n : ℕ} : DecidableRel (@Adjacent n) := fun x y => by
  unfold Adjacent; exact decEq _ _

def NordicSquare.Valley {n : ℕ} (ns : NordicSquare n) (c : Cell n) : Prop :=
  ∀ c' : Cell n, Adjacent c c' → (ns c : ℕ) < (ns c' : ℕ)

structure NordicSquare.UphillPath {n : ℕ} (ns : NordicSquare n) where
  cells : List (Cell n)
  nonempty : cells ≠ []
  first_valley : ns.Valley (cells.head nonempty)
  adjacent : cells.IsChain Adjacent
  increasing : cells.IsChain fun x y ↦ (ns x : ℕ) < (ns y : ℕ)

def answer : ℕ+ → ℕ := fun n => 2 * n^2 - 2 * n + 1

lemma Adjacent_symm {n : ℕ} {x y : Cell n} (h : Adjacent x y) : Adjacent y x := by
  unfold Adjacent at *; simp_all +decide [ Nat.dist_comm ]

lemma Adjacent_irrefl {n : ℕ} (x : Cell n) : ¬ Adjacent x x := by
  simp [Adjacent]

lemma min_cell_is_valley {n : ℕ} (ns : NordicSquare n) (c : Cell n)
    (hc : ∀ c' : Cell n, (ns c : ℕ) ≤ (ns c' : ℕ)) : ns.Valley c := by
  intro c' hc';
  refine' lt_of_le_of_ne ( hc c' ) fun h => _;
  unfold Adjacent at hc'; aesop;

lemma exists_valley {n : ℕ} [NeZero n] (ns : NordicSquare n) :
    ∃ c : Cell n, ns.Valley c := by
  have h_min : ∃ c : Cell n, ∀ c' : Cell n, (ns c : ℕ) ≤ (ns c' : ℕ) := by
    simpa using Finset.exists_min_image Finset.univ ( fun c => ( ns c : ℕ ) ) ⟨ ( 0, 0 ), Finset.mem_univ _ ⟩;
  exact ⟨ h_min.choose, min_cell_is_valley ns _ h_min.choose_spec ⟩

def valley_singleton_path {n : ℕ} (ns : NordicSquare n) (c : Cell n) (hv : ns.Valley c) :
    ns.UphillPath where
  cells := [c]
  nonempty := List.cons_ne_nil _ _
  first_valley := by simpa using hv
  adjacent := List.IsChain.singleton _
  increasing := List.IsChain.singleton _

lemma not_valley_has_strictly_smaller_neighbor {n : ℕ} (ns : NordicSquare n) (c : Cell n)
    (hc : ¬ ns.Valley c) : ∃ c' : Cell n, Adjacent c c' ∧ (ns c' : ℕ) < (ns c : ℕ) := by
  contrapose! hc;
  intro c' hc';
  refine' lt_of_le_of_ne ( hc c' hc' ) _;
  have := ns.injective.ne ( show c ≠ c' from by
                              rintro rfl; exact Adjacent_irrefl _ hc' ) ; aesop;

@[ext]
lemma UphillPath.ext' {n : ℕ} {ns : NordicSquare n} (p q : ns.UphillPath)
    (h : p.cells = q.cells) : p = q := by
  cases p ; cases q ; aesop

-- For each cell, there exists an uphill path ending at that cell
lemma exists_path_ending_at {n : ℕ} [NeZero n] (ns : NordicSquare n) (c : Cell n) :
    ∃ p : ns.UphillPath, p.cells.getLast p.nonempty = c := by
  by_contra h;
  obtain ⟨m, hm⟩ : ∃ m, m ∈ Set.image (fun c => (ns c : ℕ)) {c : Cell n | ¬∃ p : ns.UphillPath, p.cells.getLast p.nonempty = c} ∧ ∀ c ∈ Set.image (fun c => (ns c : ℕ)) {c : Cell n | ¬∃ p : ns.UphillPath, p.cells.getLast p.nonempty = c}, m ≤ c := by
    apply_rules [ Set.exists_min_image ];
    · exact Set.toFinite _;
    · exact ⟨ _, ⟨ c, h, rfl ⟩ ⟩;
  obtain ⟨ ⟨ c, hc, rfl ⟩, hm ⟩ := hm;
  obtain ⟨c', hc', hcc'⟩ : ∃ c' : Cell n, Adjacent c c' ∧ (ns c' : ℕ) < (ns c : ℕ) := by
    apply not_valley_has_strictly_smaller_neighbor;
    exact fun h => hc ⟨ valley_singleton_path ns c h, rfl ⟩;
  obtain ⟨p', hp'⟩ : ∃ p' : ns.UphillPath, p'.cells.getLast p'.nonempty = c' := by
    contrapose! hm;
    exact ⟨ _, ⟨ c', fun p => hm p, rfl ⟩, hcc' ⟩;
  set p : ns.UphillPath := ⟨p'.cells ++ [c], by
    aesop, by
    cases p' ; aesop, by
    simp_all +decide [ List.isChain_append ];
    exact ⟨ p'.adjacent, fun a b hab => by rw [ show ( a, b ) = c' from by { rw [ List.getLast?_eq_some_getLast p'.nonempty ] at hab; aesop } ] ; exact Adjacent_symm hc' ⟩, by
    have := p'.increasing; simp_all +decide [ List.isChain_append ] ;
    grind +ring⟩
  generalize_proofs at *;
  exact hc ⟨ p, by aesop ⟩

/-
PROBLEM
The number of adjacent pairs in an n×n grid

PROVIDED SOLUTION
Count adjacent pairs in an n×n grid. Adjacent means Nat.dist on rows + Nat.dist on cols = 1. This means either (same row, adjacent columns) or (adjacent rows, same column).

For horizontal adjacencies (same row, |col diff| = 1): there are n rows, each with n-1 horizontal edges, giving n(n-1) edges. Each gives 2 ordered pairs (left→right and right→left), so 2n(n-1) ordered pairs.

For vertical adjacencies (same column, |row diff| = 1): similarly 2n(n-1) ordered pairs.

Total: 4n(n-1).

Strategy: Show the filter set equals a union of horizontal and vertical pairs, count each half, and add. Use Finset.card_filter and product structure.

Alternative: use decide for small cases and then show a pattern. But n is arbitrary.

Try splitting the filter into two disjoint parts based on whether the row or column differs, then count each part using Finset products.
-/
lemma adj_pairs_card (n : ℕ) [NeZero n] :
    Finset.card (Finset.univ.filter fun e : Cell n × Cell n => Adjacent e.1 e.2) =
    4 * n * (n - 1) := by
  -- Let's count the number of horizontal and vertical adjacencies separately.
  have h_horizontal : Finset.card (Finset.filter (fun (e : Cell n × Cell n) => e.1.1 = e.2.1 ∧ Nat.dist e.1.2 e.2.2 = 1) (Finset.univ : Finset (Cell n × Cell n))) = 2 * n * (n - 1) := by
    rcases n with ( _ | _ | n ) <;> simp_all +decide [ Nat.dist.eq_def ];
    rw [ Finset.card_eq_sum_ones ] ; erw [ Finset.sum_filter ] ; erw [ Finset.sum_product ] ; norm_num ; ring;
    -- Let's simplify the expression inside the sum.
    have h_simplify : ∀ x : Fin (n + 2) × Fin (n + 2), Finset.card (Finset.filter (fun x_1 : Fin (n + 2) × Fin (n + 2) => x.1 = x_1.1 ∧ (x.2 : ℕ) - x_1.2 + (x_1.2 - x.2) = 1) (Finset.univ : Finset (Fin (n + 2) × Fin (n + 2)))) = if x.2.val = 0 ∨ x.2.val = n + 1 then 1 else 2 := by
      intro x; split_ifs <;> simp_all +decide [ Finset.card_eq_one, Finset.card_eq_two ] ;
      · rcases ‹_› with ( h | h ) <;> simp_all +decide [ Finset.ext_iff ];
        · exact ⟨ x.1, 1, by aesop ⟩;
        · use x.1, ⟨ n, by linarith ⟩;
          grind;
      · refine' ⟨ x.1, ⟨ x.2 - 1, _ ⟩, x.1, ⟨ x.2 + 1, _ ⟩, _, _ ⟩ <;> norm_num [ Fin.ext_iff, Finset.ext_iff ];
        · exact lt_of_le_of_lt ( Nat.pred_le _ ) ( Nat.lt_succ_of_le ( Fin.is_le _ ) );
        · exact Nat.le_of_lt_succ ( lt_of_le_of_ne ( Fin.is_le _ ) ( by tauto ) );
        · grind;
    simp_all +decide [ Finset.sum_product ];
    erw [ Finset.sum_product ] ; norm_num [ Finset.sum_add_distrib, Finset.sum_ite ] ; ring;
    rw [ show ( Finset.univ.filter fun x : Fin ( n + 2 ) => x = 0 ∨ ( x : ℕ ) = 1 + n ) = { 0, ⟨ 1 + n, by linarith ⟩ } from ?_, show ( Finset.univ.filter fun x : Fin ( n + 2 ) => ¬x = 0 ∧ ¬ ( x : ℕ ) = 1 + n ) = Finset.univ \ { 0, ⟨ 1 + n, by linarith ⟩ } from ?_ ] ; simp +decide [ Finset.card_sdiff, Finset.card_singleton, Finset.card_insert_of_notMem ] ; ring;
    · ext ⟨ x, hx ⟩ ; aesop;
    · grind;
  -- Similarly, let's count the number of vertical adjacencies.
  have h_vertical : Finset.card (Finset.filter (fun (e : Cell n × Cell n) => e.1.2 = e.2.2 ∧ Nat.dist e.1.1 e.2.1 = 1) (Finset.univ : Finset (Cell n × Cell n))) = 2 * n * (n - 1) := by
    rw [ ← h_horizontal ];
    rw [ Finset.card_filter, Finset.card_filter ];
    apply Finset.sum_bij (fun e _ => (e.1.swap, e.2.swap));
    · simp;
    · aesop;
    · exact fun b _ => ⟨ ( b.1.swap, b.2.swap ), Finset.mem_univ _, by simp +decide ⟩;
    · grind;
  convert congr_arg₂ ( · + · ) h_horizontal h_vertical using 1 <;> ring!;
  rw [ ← Finset.card_union_of_disjoint ] ; congr ; ext ; simp +decide [ Adjacent ] ; ring;
  · cases eq_or_ne ( ‹Cell n × Cell n›.1.1 ) ( ‹Cell n × Cell n›.2.1 ) <;> cases eq_or_ne ( ‹Cell n × Cell n›.1.2 ) ( ‹Cell n × Cell n›.2.2 ) <;> simp_all +decide [ Nat.dist.eq_def ] ; omega;
  · rw [ Finset.disjoint_left ] ; aesop

/-
PROBLEM
The number of directed increasing edges equals half the adjacent pairs

PROVIDED SOLUTION
Each undirected edge gives exactly 2 ordered adjacent pairs. Since ns is a bijection, for each undirected edge, exactly one ordered pair has ns e.1 < ns e.2 and the other has ns e.2 < ns e.1 (they can't be equal since ns is injective and adjacent cells are distinct by Adjacent_irrefl).

So the directed increasing edges are exactly half of all ordered adjacent pairs.
By adj_pairs_card, there are 4n(n-1) ordered adjacent pairs. So there are 2n(n-1) directed increasing edges.

More precisely: partition {(x,y) | Adjacent x y} into {(x,y) | Adjacent x y ∧ ns x < ns y} and {(x,y) | Adjacent x y ∧ ns y < ns x}. These are disjoint (can't have both ns x < ns y and ns y < ns x). Their union is all adjacent pairs (since adjacent cells are distinct, ns x ≠ ns y). The second set bijects to the first via (x,y) ↦ (y,x) using Adjacent_symm.

So both have the same cardinality = 4n(n-1)/2 = 2n(n-1).
-/
lemma directed_edges_card {n : ℕ} [NeZero n] (ns : NordicSquare n) :
    Finset.card (Finset.univ.filter fun e : Cell n × Cell n =>
      Adjacent e.1 e.2 ∧ (ns e.1 : ℕ) < (ns e.2 : ℕ)) = 2 * n * (n - 1) := by
  -- By definition of adjacency, the set of pairs where $ns e.1 < ns e.2$ is exactly half of all adjacent pairs.
  have h_half : Finset.card (Finset.filter (fun e => Adjacent e.1 e.2 ∧ (ns e.1 : ℕ) < (ns e.2 : ℕ)) (Finset.univ : Finset (Cell n × Cell n))) + Finset.card (Finset.filter (fun e => Adjacent e.1 e.2 ∧ (ns e.2 : ℕ) < (ns e.1 : ℕ)) (Finset.univ : Finset (Cell n × Cell n))) = Finset.card (Finset.univ.filter fun e : Cell n × Cell n => Adjacent e.1 e.2) := by
    rw [ ← Finset.card_union_of_disjoint ];
    · congr with e;
      simp +zetaDelta at *;
      exact ⟨ fun h => h.elim ( fun h => h.1 ) fun h => h.1, fun h => if h' : ns e.1 < ns e.2 then Or.inl ⟨ h, h' ⟩ else Or.inr ⟨ h, lt_of_le_of_ne ( le_of_not_gt h' ) ( Ne.symm <| by intro t; exact Adjacent_irrefl e.1 <| by aesop ) ⟩ ⟩;
    · exact Finset.disjoint_filter.mpr fun _ _ _ _ => lt_asymm ( by tauto ) ( by tauto );
  -- Since these two sets are disjoint and their union is the set of all adjacent pairs, they must have the same cardinality.
  have h_eq : Finset.card (Finset.filter (fun e => Adjacent e.1 e.2 ∧ (ns e.1 : ℕ) < (ns e.2 : ℕ)) (Finset.univ : Finset (Cell n × Cell n))) = Finset.card (Finset.filter (fun e => Adjacent e.1 e.2 ∧ (ns e.2 : ℕ) < (ns e.1 : ℕ)) (Finset.univ : Finset (Cell n × Cell n))) := by
    apply Finset.card_bij (fun e he => (e.2, e.1));
    · simp +contextual [ Adjacent_symm ];
    · aesop;
    · simp +contextual [ Adjacent_symm ];
  linarith [ adj_pairs_card n ]

/-
PROBLEM
Key lower bound: there exist at least (answer n) distinct uphill paths
for any Nordic square

PROVIDED SOLUTION
We show ↑(answer n) ≤ #ns.UphillPath by constructing enough distinct uphill paths.

Key construction: For each directed increasing edge (c, c') (adjacent cells with ns(c) < ns(c')), use exists_path_ending_at to get a path p ending at c, then build a new path p' = p.cells ++ [c'] ending at c'. This path p' has length ≥ 2.

Different directed edges give different paths: if (c1, c1') ≠ (c2, c2'), then the corresponding paths differ (they have different last cells or different second-to-last cells).

Additionally, we get one singleton path from the valley.

There are 2n(n-1) directed edges (by directed_edges_card) and 1 valley singleton, totaling 2n(n-1) + 1 = answer n.

To formalize: construct a function from (Fin (2*n*(n-1)) ⊕ Unit) → ns.UphillPath that is injective, then use Cardinal.mk_le_of_injective.

Alternatively: construct a Finset of ns.UphillPath of size ≥ answer n, then use Cardinal.mk_le_of_injective or similar.

Use exists_path_ending_at, exists_valley, valley_singleton_path, directed_edges_card.
-/
set_option maxHeartbeats 800000 in
lemma lb_card {n : ℕ+} (ns : NordicSquare n) :
    ↑(answer n) ≤ #ns.UphillPath := by
  have h_card : ∃ f : Fin (2 * n * (n - 1)) ⊕ Unit → ns.UphillPath, Function.Injective f := by
    choose f hf using exists_path_ending_at ns;
    have h_directed_edges : Finset.card (Finset.filter (fun e : Cell n × Cell n => Adjacent e.1 e.2 ∧ (ns e.1 : ℕ) < (ns e.2 : ℕ)) (Finset.univ : Finset (Cell n × Cell n))) = 2 * n * (n - 1) := by
      convert directed_edges_card ns using 1;
    obtain ⟨g, hg⟩ : ∃ g : Fin (2 * n * (n - 1)) → Cell n × Cell n, Function.Injective g ∧ ∀ i, Adjacent (g i).1 (g i).2 ∧ (ns (g i).1 : ℕ) < (ns (g i).2 : ℕ) := by
      have h_directed_edges : Nonempty (Fin (2 * n * (n - 1)) ≃ {e : Cell n × Cell n | Adjacent e.1 e.2 ∧ (ns e.1 : ℕ) < (ns e.2 : ℕ)}) := by
        exact ⟨ Fintype.equivOfCardEq <| by simpa [ Fintype.card_subtype ] using h_directed_edges.symm ⟩;
      exact ⟨ _, Subtype.val_injective.comp h_directed_edges.some.injective, fun i => h_directed_edges.some i |>.2 ⟩;
    refine' ⟨ fun x => x.elim ( fun i => ⟨ ( f ( g i |>.1 ) ).cells ++ [ ( g i |>.2 ) ], _, _, _, _ ⟩ ) fun _ => ⟨ [ ( Classical.choose ( exists_valley ns ) ) ], _, _, _, _ ⟩, _ ⟩ <;> simp_all +decide [ Function.Injective ];
    · cases h : f ( g i |>.1 ) ; aesop;
    · rw [ List.isChain_iff_get ];
      intro j; by_cases hj : j.val < ( f ( g i |>.1 ) |> NordicSquare.UphillPath.cells |> List.length ) <;> simp_all +decide [ Fin.add_def, Nat.mod_eq_of_lt ] ;
      · have := ( f ( g i |>.1 ) |> NordicSquare.UphillPath.adjacent ) ; simp_all +decide [ List.getElem_append ] ;
        split_ifs <;> simp_all +decide [ List.isChain_iff_get ];
        · exact this ⟨ j, Nat.lt_pred_iff.mpr ‹_› ⟩;
        · grind +ring;
      · grind;
    · rw [ List.isChain_iff_get ] at *;
      intro j; rcases j with ⟨ j, hj ⟩ ; simp_all +decide [ List.getElem_append ] ;
      split_ifs <;> simp_all +decide [ List.length_append ];
      · have := ( f ( g i |>.1 ) ).increasing; simp_all +decide [ List.isChain_iff_get ] ;
        exact this ⟨ j, Nat.lt_pred_iff.mpr ‹_› ⟩;
      · grind +ring;
    · exact Classical.choose_spec ( exists_valley ns );
    · refine' ⟨ fun i => ⟨ fun j hij h => _, _ ⟩, fun i => _ ⟩;
      · have := hf ( g i |>.1 |>.1 ) ( g i |>.1 |>.2 ) ; have := hf ( g j |>.1 |>.1 ) ( g j |>.1 |>.2 ) ; aesop;
      · intro h; have := congr_arg List.length h; simp +decide at this;
        grind;
      · intro h; have := congr_arg List.length h; simp +decide at this;
        have := f ( g i |>.1 ) |>.nonempty; aesop;
  obtain ⟨ f, hf ⟩ := h_card;
  refine' le_trans _ ( Cardinal.mk_le_of_injective hf );
  simp +arith +decide [ answer ];
  norm_cast ; cases n using PNat.recOn <;> norm_num [ Nat.mul_succ, sq ] ; ring_nf ; norm_num

-- Part 1: There exists a Nordic square with exactly answer n uphill paths
theorem imo2022_p6_mem {n : ℕ+} :
    answer n ∈ {k : ℕ | ∃ ns : NordicSquare n, #ns.UphillPath = k} := by
  sorry

-- Part 2: Every Nordic square has at least answer n uphill paths
theorem imo2022_p6_lb {n : ℕ+} :
    ∀ k ∈ {k : ℕ | ∃ ns : NordicSquare n, #ns.UphillPath = k}, answer n ≤ k := by
  intro k ⟨ns, hk⟩
  have h := lb_card ns
  rw [hk] at h
  exact_mod_cast h

theorem imo2022_p6 {n : ℕ+} :
    IsLeast {k : ℕ | ∃ ns : NordicSquare n, #ns.UphillPath = k} (answer n) := by
  exact ⟨imo2022_p6_mem, imo2022_p6_lb⟩

end Imo2022P6