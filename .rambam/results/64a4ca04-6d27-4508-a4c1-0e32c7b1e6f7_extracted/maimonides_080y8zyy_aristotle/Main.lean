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

instance {n : ℕ} : DecidableEq (Cell n) := inferInstance

instance {n : ℕ} (x y : Cell n) : Decidable (Adjacent x y) := by
  unfold Adjacent; exact inferInstance

/-- A directed edge in the grid: adjacent cells where the first has smaller ns-value -/
def DirectedEdge {n : ℕ} (ns : NordicSquare n) (u v : Cell n) : Prop :=
  Adjacent u v ∧ (ns u : ℕ) < (ns v : ℕ)

/-- The cell with minimum value is always a valley -/
lemma valley_of_min_val {n : ℕ} (hn : 0 < n) (ns : NordicSquare n) :
    ∃ c : Cell n, ns.Valley c := by
  obtain ⟨c, hc⟩ : ∃ c : Cell n, ∀ c' : Cell n, (ns c : ℕ) ≤ (ns c' : ℕ) := by
    simpa using Finset.exists_min_image Finset.univ (fun c => (ns c : ℕ))
      ⟨(⟨0, hn⟩, ⟨0, hn⟩), Finset.mem_univ _⟩
  exact ⟨c, fun c' hc' => lt_of_le_of_ne (hc c')
    (by have := ns.injective.ne (show c ≠ c' from by
          rintro rfl; exact absurd hc' (by unfold Adjacent; aesop)); aesop)⟩

/-- For any non-valley cell, there exists an adjacent cell with strictly smaller value -/
lemma exists_smaller_neighbor {n : ℕ} (ns : NordicSquare n) (c : Cell n)
    (hc : ¬ns.Valley c) : ∃ c' : Cell n, Adjacent c c' ∧ (ns c' : ℕ) < (ns c : ℕ) := by
  contrapose! hc
  intro c' hc'
  by_cases h_eq : (ns c : ℕ) = (ns c' : ℕ)
  · unfold Adjacent at hc'; aesop
  · exact lt_of_le_of_ne (hc c' hc') h_eq

/-
PROBLEM
From any cell, we can find an uphill path ending at it

PROVIDED SOLUTION
By strong induction on (ns c : ℕ).

If c is a valley, the singleton path [c] works: getLast [c] = c.

If c is not a valley, by exists_smaller_neighbor there exists c' adjacent to c with ns(c') < ns(c). By the induction hypothesis, there exists an uphill path p' ending at c'. Then p'.cells ++ [c] is an uphill path ending at c.

For the induction, use a helper: for all k, for all c with (ns c : ℕ) ≤ k, there exists such a path. Induct on k using Nat.rec or induction'.

By strong induction on (ns c : ℕ).

Base case: If c is a valley, the singleton path [c] is an uphill path with getLast = c.

Inductive case: If c is not a valley, use exists_smaller_neighbor to get c' adjacent to c with (ns c' : ℕ) < (ns c : ℕ). By induction hypothesis, get an uphill path p ending at c'. Then construct a new UphillPath with cells = p.cells ++ [c].

For the new path:
- nonempty: p.cells ++ [c] is nonempty (obvious)
- first_valley: head of p.cells ++ [c] = head of p.cells = valley of p (since p is nonempty and p's head is a valley)
- adjacent: p.adjacent holds for p.cells, and we need the chain to extend. The last element of p.cells is c' (by hp : getLast = c'), and c' is adjacent to c. Use List.IsChain of append: need p.adjacent and that getLast? relates to c via Adjacent. Use adjacent_symm since we have Adjacent c c' and need Adjacent c' c.
- increasing: similarly, p.increasing holds, and (ns c' : ℕ) < (ns c : ℕ).

Use strong_induction_on or well-founded recursion. Try this pattern:
  suffices h : ∀ k, ∀ c : Cell n, (ns c : ℕ) ≤ k → ∃ p : ns.UphillPath, p.cells.getLast p.nonempty = c by exact h _ c le_rfl
  intro k; induction k with | zero => ... | succ k ih => ...
-/
lemma exists_uphill_path_ending_at {n : ℕ} (hn : 0 < n) (ns : NordicSquare n)
    (c : Cell n) :
    ∃ p : ns.UphillPath, p.cells.getLast p.nonempty = c := by
  by_contra h_contra
  generalize_proofs at *; (
  -- By induction on $k$, we can show that for any cell $c$ with value $k$, there exists an uphill path ending at $c$.
  have h_ind : ∀ k : ℕ, ∀ c : Cell n, (ns c : ℕ) = k → ∃ p : NordicSquare.UphillPath ns, p.cells.getLast p.nonempty = c := by
    intro k c hk
    induction' k using Nat.strong_induction_on with k ih generalizing c
    by_cases h_valley : ns.Valley c
    generalize_proofs at *; (
    refine' ⟨ ⟨ [ c ], _, _, _, _ ⟩, _ ⟩ <;> simp +decide [ h_valley ]);
    obtain ⟨ c', hc₁, hc₂ ⟩ := exists_smaller_neighbor ns c h_valley
    generalize_proofs at *; (
    obtain ⟨ p, hp ⟩ := ih _ ( by linarith ) _ rfl
    generalize_proofs at *; (
    refine' ⟨ ⟨ p.cells ++ [ c ], _, _, _, _ ⟩, _ ⟩ <;> simp_all +decide [ List.isChain_append ];
    · exact p.first_valley;
    · have h_adj : Adjacent c' c := by
        unfold Adjacent at *; simp_all +decide [ Nat.dist_comm ] ;
      generalize_proofs at *; (
      exact ⟨ p.adjacent, fun a b hab => by rw [ List.getLast?_eq_some_iff ] at hab; aesop ⟩);
    · simp_all +decide [ List.getLast?_eq_some_getLast ];
      exact ⟨ p.increasing, fun a b hab => by subst hab; exact_mod_cast hc₂.trans_le ( by linarith ) ⟩))
  generalize_proofs at *; (
  exact h_contra <| h_ind _ _ rfl))

/-
PROBLEM
For each directed edge (u,v), there exists an uphill path ending with [... u, v]

PROVIDED SOLUTION
Use exists_uphill_path_ending_at to get an uphill path p ending at u. Then construct a new UphillPath with cells = p.cells ++ [v].

The new path has:
- nonempty: obvious
- first_valley: same as p's first valley (head of p.cells ++ [v] = head of p.cells)
- adjacent: p.adjacent holds for p.cells. We extend: getLast of p.cells is u, and u is adjacent to v (by hadj). Use list chain append lemma.
- increasing: p.increasing holds, and (ns u : ℕ) < (ns v : ℕ) (by hlt). Extend similarly.

Then the new path has getLast = v and second-to-last element = u (the getLast of the original p.cells).
-/
lemma exists_uphill_path_with_last_edge {n : ℕ} (hn : 0 < n)
    (ns : NordicSquare n) (u v : Cell n)
    (hadj : Adjacent u v) (hlt : (ns u : ℕ) < (ns v : ℕ)) :
    ∃ p : ns.UphillPath, p.cells.getLast p.nonempty = v ∧
      (∃ h : p.cells.length ≥ 2,
        p.cells.get ⟨p.cells.length - 2, by omega⟩ = u) := by
  obtain ⟨ p, hp ⟩ := exists_uphill_path_ending_at hn ns u
  generalize_proofs at *;
  -- Construct the new path by appending $v$ to the end of $p$'s cells.
  use ⟨p.cells ++ [v], by
    aesop, by
    cases p ; aesop, by
    simp_all +decide [ List.isChain_iff_get ];
    intro i; rcases i with ⟨ i, hi ⟩ ; rcases lt_trichotomy i ( p.cells.length - 1 ) with hi' | rfl | hi' <;> simp_all +decide [ List.getElem_append ] ;
    · split_ifs <;> simp_all +decide [ List.length_append ];
      · have := p.adjacent; simp_all +decide [ List.isChain_iff_get ] ;
        exact this ⟨ i, hi' ⟩;
      · omega;
    · grind +ring;
    · grind +ring, by
    simp_all +decide [ List.isChain_iff_get ];
    intro i; rcases i with ⟨ i, hi ⟩ ; rcases lt_trichotomy i ( p.cells.length - 1 ) with h | h | h <;> simp_all +decide [ List.getElem_append ] ;
    · split_ifs <;> simp_all +decide [ Nat.lt_succ_iff ];
      · have := p.increasing; simp_all +decide [ List.isChain_iff_get ] ;
        exact this ⟨ i, h ⟩;
      · omega;
    · grind +ring;
    · grind +ring⟩
  generalize_proofs at *;
  grind

/-- Two uphill paths are equal iff their cell lists are equal -/
lemma uphill_path_ext {n : ℕ} (ns : NordicSquare n)
    (p q : ns.UphillPath) (hp : p.cells = q.cells) : p = q := by
  cases p; cases q; aesop

/-- Adjacent is symmetric -/
lemma adjacent_symm {n : ℕ} (x y : Cell n) : Adjacent x y ↔ Adjacent y x := by
  unfold Adjacent; constructor <;> (intro h; rw [Nat.dist_comm x.1, Nat.dist_comm x.2] at *; exact h)

/-- Self is not adjacent to itself -/
lemma not_adjacent_self {n : ℕ} (x : Cell n) : ¬Adjacent x x := by
  unfold Adjacent; simp [Nat.dist_self]

-- ============================================================
-- Lower bound infrastructure
-- ============================================================

/-- The number of undirected edges in the n×n grid -/
def gridEdgeCount (n : ℕ) : ℕ := 2 * n * (n - 1)

/-
PROBLEM
answer n = 1 + gridEdgeCount n

PROVIDED SOLUTION
Unfold answer and gridEdgeCount. We need 2 * n^2 - 2 * n + 1 = 1 + 2 * n * (n - 1). Since n ≥ 1 (n : ℕ+), 2 * n * (n-1) = 2n² - 2n, so 1 + 2n² - 2n = 2n² - 2n + 1. Use omega or ring after casting n to ℕ and using n ≥ 1.
-/
lemma answer_eq {n : ℕ+} : (answer n : ℕ) = 1 + gridEdgeCount n := by
  unfold answer gridEdgeCount;
  zify ; norm_num ; ring;
  rw [ Nat.cast_sub ] <;> push_cast <;> nlinarith [ PNat.pos n ]

/-
PROBLEM
An UphillPath has at most n^2 cells (since values are strictly increasing in {1,...,n^2})

PROVIDED SOLUTION
The values ns(cells[i]) form a strictly increasing sequence in {1, ..., n²}. A strictly increasing sequence of naturals in {1,...,n²} has length at most n².

More precisely, since the cells list has the IsChain property for the relation (ns x : ℕ) < (ns y : ℕ), the list maps (via ns) to a strictly increasing sequence. The values are all in Finset.Icc 1 (n^2) so they are bounded by n². A strictly increasing sequence of naturals bounded by n² has at most n² elements (by pigeonhole/injection into Fin n²).
-/
lemma uphill_path_length_bound {n : ℕ} (ns : NordicSquare n) (p : ns.UphillPath) :
    p.cells.length ≤ n ^ 2 := by
  -- The values ns(cells[i]) form a strictly increasing sequence in {1, ..., n²}.
  have h_seq : StrictMonoOn (fun i : Fin p.cells.length => (ns (p.cells.get i))) (Finset.univ : Finset (Fin p.cells.length)) := by
    intro i hi j hj hij; have := p.increasing; simp_all +decide [ List.IsChain ] ;
    rw [ List.isChain_iff_get ] at this;
    induction' j with j ih;
    induction' j with j ih generalizing i;
    · tauto;
    · rcases eq_or_lt_of_le ( show i.val ≤ j from Nat.le_of_lt_succ hij ) with h | h <;> simp_all +decide [ Fin.add_def, Nat.mod_eq_of_lt ];
      · convert this ⟨ j, Nat.lt_pred_iff.mpr ‹_› ⟩ using 1;
      · exact lt_trans ( ih ( by linarith ) ( Nat.lt_of_le_of_lt ( Nat.le_refl _ ) h ) ) ( this ⟨ j, Nat.lt_pred_iff.mpr ‹_› ⟩ );
  -- Since the values are strictly increasing and bounded by $n^2$, the length of the sequence cannot exceed $n^2$.
  have h_bound : Finset.card (Finset.image (fun i : Fin p.cells.length => (ns (p.cells.get i)) : Fin p.cells.length → ℕ) Finset.univ) ≤ n^2 := by
    exact le_trans ( Finset.card_le_card <| Finset.image_subset_iff.mpr fun i _ => Finset.mem_Icc.mpr ⟨ mod_cast Finset.mem_Icc.mp ( ns ( p.cells.get i ) |>.2 ) |>.1, mod_cast Finset.mem_Icc.mp ( ns ( p.cells.get i ) |>.2 ) |>.2 ⟩ ) ( by norm_num [ sq ] );
  rw [ Finset.card_image_of_injOn ] at h_bound;
  · simpa using h_bound;
  · exact fun i hi j hj hij => h_seq.eq_iff_eq hi hj |>.1 <| by simpa using hij;

/-
PROBLEM
UphillPath is a Fintype

PROVIDED SOLUTION
The key idea: UphillPath injects into bounded-length lists of cells (via the cells field). By uphill_path_length_bound, p.cells.length ≤ n^2. Since Cell n is finite, bounded-length lists form a finite type.

Approach: Use Fintype.ofInjective. Define the injection:
  f : ns.UphillPath → { l : List (Cell n) // l.length ≤ n^2 }
  f p = ⟨p.cells, uphill_path_length_bound ns p⟩

Show f is injective using uphill_path_ext.

The target type { l : List (Cell n) // l.length ≤ n^2 } is a Fintype because it's a subtype of a fintype. Actually List (Cell n) is NOT a Fintype since it's infinite. But { l : List (Cell n) // l.length ≤ n^2 } IS a Fintype because it's equivalent to the set of lists of length ≤ n^2 over a finite alphabet. This is Fintype by List.instFintypeVector or similar.

Alternative approach: show that the type is finite using Set.Finite or Finite, then derive Fintype. The type is a subtype of lists of bounded length over a finite type, which is finite.

Maybe simpler: use `Fintype.ofFinite` after showing `Finite ns.UphillPath`. To show Finite, note that UphillPath injects into `List (Cell n)` which has the property that strictly increasing values bound the length, and Cell n is finite. So the image is a finite subset.

Try: apply Fintype.ofInjective (fun p => (⟨p.cells, uphill_path_length_bound ns p⟩ : {l : List (Cell n) // l.length ≤ n^2})) and prove injectivity via uphill_path_ext.

The cells are nodup because the values ns(cell) along the path are strictly increasing (by p.increasing). If two cells at positions i < j in the list were equal, they would have the same ns value, contradicting strict increase.

More precisely: p.increasing says the list satisfies IsChain (fun x y => (ns x : ℕ) < (ns y : ℕ)). This means consecutive elements have strictly increasing ns values. By transitivity, for i < j, ns(cells[i]) < ns(cells[j]).

If cells[i] = cells[j] with i ≠ j, then ns(cells[i]) = ns(cells[j]), contradicting ns(cells[i]) < ns(cells[j]) or ns(cells[j]) < ns(cells[i]).

Use List.nodup_iff_injective_get or List.Nodup_iff_getElem. Show that if i ≠ j then cells[i] ≠ cells[j] by showing ns(cells[i]) ≠ ns(cells[j]).
-/
lemma uphill_path_cells_nodup {n : ℕ} (ns : NordicSquare n) (p : ns.UphillPath) :
    p.cells.Nodup := by
  have h_increasing : ∀ i j : Fin p.cells.length, i < j → (ns p.cells[i]) < (ns p.cells[j]) := by
    have := p.increasing;
    intro i j hij;
    induction' j with j hj;
    induction' j with j ih;
    · tauto;
    · cases lt_or_eq_of_le ( show i ≤ ⟨ j, by linarith ⟩ from Nat.le_of_lt_succ hij ) <;> simp_all +decide [ List.isChain_iff_get ];
      · exact lt_trans ( ih ( Nat.lt_of_succ_lt hj ) ) ( this ⟨ j, Nat.lt_pred_iff.mpr hj ⟩ );
      · exact this ⟨ j, Nat.lt_pred_iff.mpr hj ⟩;
  exact List.nodup_iff_injective_get.mpr fun i j hij => le_antisymm ( not_lt.1 fun hi => by have := h_increasing _ _ hi; aesop ) ( not_lt.1 fun hj => by have := h_increasing _ _ hj; aesop )

noncomputable instance {n : ℕ} (ns : NordicSquare n) : Fintype ns.UphillPath :=
  Fintype.ofInjective
    (fun p => (⟨p.cells, uphill_path_cells_nodup ns p⟩ : {l : List (Cell n) // l.Nodup}))
    (fun p q h => uphill_path_ext ns p q (by simpa using h))

/-- The set of directed edges as a Finset -/
noncomputable def directedEdges {n : ℕ} (ns : NordicSquare n) : Finset (Cell n × Cell n) :=
  Finset.filter (fun e => Adjacent e.1 e.2 ∧ (ns e.1 : ℕ) < (ns e.2 : ℕ)) Finset.univ

/-
PROBLEM
The number of directed edges equals the number of undirected edges

PROVIDED SOLUTION
The directed edges are ordered pairs (u,v) with u adj v and ns(u) < ns(v). Since ns is a bijection, for each undirected edge {u,v} with u adj v, exactly one of ns(u) < ns(v) or ns(v) < ns(u) holds (they can't be equal since ns is injective and u ≠ v since adj implies u ≠ v). So the number of directed edges equals the number of undirected edges.

The number of undirected edges in the n×n grid is gridEdgeCount n = 2*n*(n-1). This counts n*(n-1) horizontal edges (n rows, each with n-1 horizontal adjacencies) and n*(n-1) vertical edges (n columns, each with n-1 vertical adjacencies).

To prove this formally: establish a bijection between directedEdges ns and the set of undirected edges. An undirected edge can be represented as an ordered pair (u,v) with u adj v (noting each undirected edge appears once as (u,v) and once as (v,u)). Then directedEdges picks exactly one from each pair.

Alternatively, show directedEdges ns has same card as the set of ordered adjacent pairs divided by 2. The ordered adjacent pairs have cardinality 2 * gridEdgeCount n (each undirected edge gives 2 ordered pairs). directedEdges picks exactly half. So card = gridEdgeCount n.
-/
set_option maxHeartbeats 800000 in
lemma card_directed_edges {n : ℕ} (ns : NordicSquare n) :
    (directedEdges ns).card = gridEdgeCount n := by
  unfold directedEdges gridEdgeCount;
  -- The number of undirected edges in the grid is $2n(n-1)$.
  have h_undirected_edges : Finset.card (Finset.filter (fun e => Adjacent e.1 e.2) (Finset.univ : Finset (Cell n × Cell n))) = 4 * n * (n - 1) := by
    unfold Adjacent;
    -- We can count the number of adjacent pairs by considering each row and column separately.
    have h_adjacent_pairs : Finset.card (Finset.filter (fun e : (Fin n × Fin n) × (Fin n × Fin n) => (e.1.1.val = e.2.1.val ∧ (e.1.2.val = e.2.2.val + 1 ∨ e.1.2.val + 1 = e.2.2.val)) ∨ (e.1.2.val = e.2.2.val ∧ (e.1.1.val = e.2.1.val + 1 ∨ e.1.1.val + 1 = e.2.1.val))) (Finset.univ : Finset ((Fin n × Fin n) × (Fin n × Fin n)))) = 4 * n * (n - 1) := by
      have h_adjacent_pairs : Finset.card (Finset.filter (fun e : (Fin n × Fin n) × (Fin n × Fin n) => (e.1.1.val = e.2.1.val ∧ (e.1.2.val = e.2.2.val + 1 ∨ e.1.2.val + 1 = e.2.2.val))) (Finset.univ : Finset ((Fin n × Fin n) × (Fin n × Fin n)))) = 2 * n * (n - 1) := by
        -- For each row $i$, there are $n-1$ horizontal edges, and there are $n$ rows.
        have h_horizontal_edges : Finset.card (Finset.filter (fun e : (Fin n × Fin n) × (Fin n × Fin n) => e.1.1 = e.2.1 ∧ (e.1.2.val = e.2.2.val + 1 ∨ e.1.2.val + 1 = e.2.2.val)) (Finset.univ : Finset ((Fin n × Fin n) × (Fin n × Fin n)))) = n * (n - 1) * 2 := by
          have h_horizontal_edges : ∀ i : Fin n, Finset.card (Finset.filter (fun e : (Fin n × Fin n) × (Fin n × Fin n) => e.1.1 = i ∧ e.2.1 = i ∧ (e.1.2.val = e.2.2.val + 1 ∨ e.1.2.val + 1 = e.2.2.val)) (Finset.univ : Finset ((Fin n × Fin n) × (Fin n × Fin n)))) = 2 * (n - 1) := by
            intro i
            have h_horizontal_edges_row : Finset.card (Finset.filter (fun e : Fin n × Fin n => (e.1.val = e.2.val + 1 ∨ e.1.val + 1 = e.2.val)) (Finset.univ : Finset (Fin n × Fin n))) = 2 * (n - 1) := by
              rw [ Finset.card_eq_sum_ones ];
              rw [ show ( Finset.filter ( fun x : Fin n × Fin n => ( x.1 : ℕ ) = x.2 + 1 ∨ ( x.1 : ℕ ) + 1 = x.2 ) Finset.univ ) = Finset.image ( fun x : Fin ( n - 1 ) => ( ⟨ x + 1, by omega ⟩, ⟨ x, by omega ⟩ ) ) Finset.univ ∪ Finset.image ( fun x : Fin ( n - 1 ) => ( ⟨ x, by omega ⟩, ⟨ x + 1, by omega ⟩ ) ) Finset.univ from ?_ ];
              · rw [ Finset.sum_union ] <;> norm_num [ Finset.card_image_of_injective, Function.Injective ] ; ring;
                · rw [ Finset.card_image_of_injective, Finset.card_image_of_injective ] <;> norm_num [ Function.Injective ] ; ring;
                  · exact fun a₁ a₂ h => Fin.ext h;
                  · exact fun a₁ a₂ h => Fin.ext h;
                · norm_num [ Finset.disjoint_left ];
                  intros; omega;
              · ext ⟨x, y⟩; simp [Finset.mem_union, Finset.mem_image];
                constructor;
                · rintro ( h | h ) <;> [ exact Or.inl ⟨ ⟨ y, by omega ⟩, by aesop ⟩ ; exact Or.inr ⟨ ⟨ x, by omega ⟩, by aesop ⟩ ];
                · aesop;
            rw [ ← h_horizontal_edges_row ];
            refine' Finset.card_bij ( fun e he => ( e.1.2, e.2.2 ) ) _ _ _ <;> aesop;
          have h_horizontal_edges : Finset.card (Finset.filter (fun e : (Fin n × Fin n) × (Fin n × Fin n) => e.1.1 = e.2.1 ∧ (e.1.2.val = e.2.2.val + 1 ∨ e.1.2.val + 1 = e.2.2.val)) (Finset.univ : Finset ((Fin n × Fin n) × (Fin n × Fin n)))) = Finset.sum Finset.univ (fun i : Fin n => Finset.card (Finset.filter (fun e : (Fin n × Fin n) × (Fin n × Fin n) => e.1.1 = i ∧ e.2.1 = i ∧ (e.1.2.val = e.2.2.val + 1 ∨ e.1.2.val + 1 = e.2.2.val)) (Finset.univ : Finset ((Fin n × Fin n) × (Fin n × Fin n))))) := by
            rw [ ← Finset.card_biUnion ];
            · congr with e ; aesop;
            · exact fun i _ j _ hij => Finset.disjoint_left.mpr fun x => by aesop;
          simp_all +decide [ mul_assoc, mul_comm, mul_left_comm ];
        convert h_horizontal_edges using 1 ; ring;
        · simp +decide [ Fin.ext_iff ];
        · ring;
      have h_adjacent_pairs : Finset.card (Finset.filter (fun e : (Fin n × Fin n) × (Fin n × Fin n) => (e.1.2.val = e.2.2.val ∧ (e.1.1.val = e.2.1.val + 1 ∨ e.1.1.val + 1 = e.2.1.val))) (Finset.univ : Finset ((Fin n × Fin n) × (Fin n × Fin n)))) = 2 * n * (n - 1) := by
        rw [ ← h_adjacent_pairs ];
        rw [ Finset.card_filter, Finset.card_filter ];
        apply Finset.sum_bij (fun e _ => ((e.1.2, e.1.1), (e.2.2, e.2.1)));
        · simp;
        · grind;
        · exact fun b _ => ⟨ ( ( b.1.2, b.1.1 ), ( b.2.2, b.2.1 ) ), Finset.mem_univ _, rfl ⟩;
        · grind;
      rw [ Finset.filter_or, Finset.card_union_of_disjoint ];
      · linarith;
      · rw [ Finset.disjoint_left ] ; aesop;
    convert h_adjacent_pairs using 4 ; simp +decide [ Nat.dist.eq_def ] ; ring;
    omega;
  -- Since these two sets are complementary within the set of all adjacent pairs, their cardinalities add up to the total number of adjacent pairs.
  have h_complementary : Finset.card (Finset.filter (fun e => Adjacent e.1 e.2 ∧ (ns e.1 : ℕ) < (ns e.2 : ℕ)) (Finset.univ : Finset (Cell n × Cell n))) + Finset.card (Finset.filter (fun e => Adjacent e.1 e.2 ∧ (ns e.2 : ℕ) < (ns e.1 : ℕ)) (Finset.univ : Finset (Cell n × Cell n))) = Finset.card (Finset.filter (fun e => Adjacent e.1 e.2) (Finset.univ : Finset (Cell n × Cell n))) := by
    have h_complementary : Finset.filter (fun e => Adjacent e.1 e.2 ∧ (ns e.1 : ℕ) < (ns e.2 : ℕ)) (Finset.univ : Finset (Cell n × Cell n)) ∪ Finset.filter (fun e => Adjacent e.1 e.2 ∧ (ns e.2 : ℕ) < (ns e.1 : ℕ)) (Finset.univ : Finset (Cell n × Cell n)) = Finset.filter (fun e => Adjacent e.1 e.2) (Finset.univ : Finset (Cell n × Cell n)) := by
      ext ⟨x, y⟩; simp [Adjacent];
      cases lt_trichotomy ( ns x ) ( ns y ) <;> aesop;
    rw [ ← Finset.card_union_of_disjoint, h_complementary ];
    exact Finset.disjoint_filter.mpr fun _ _ _ _ => by linarith;
  -- Since these two sets are complementary within the set of all adjacent pairs, their cardinalities are equal.
  have h_equal : Finset.card (Finset.filter (fun e => Adjacent e.1 e.2 ∧ (ns e.1 : ℕ) < (ns e.2 : ℕ)) (Finset.univ : Finset (Cell n × Cell n))) = Finset.card (Finset.filter (fun e => Adjacent e.1 e.2 ∧ (ns e.2 : ℕ) < (ns e.1 : ℕ)) (Finset.univ : Finset (Cell n × Cell n))) := by
    rw [ Finset.card_filter, Finset.card_filter ];
    apply Finset.sum_bij (fun e _ => (e.2, e.1));
    · grind;
    · grind;
    · exact fun b _ => ⟨ ( b.2, b.1 ), Finset.mem_univ _, rfl ⟩;
    · simp +decide [ adjacent_symm ];
  linarith

-- ============================================================
-- Main theorems
-- ============================================================

/-- There exists a Nordic square achieving exactly answer(n) uphill paths -/
theorem imo2022_p6_mem {n : ℕ+} :
    answer n ∈ {k : ℕ | ∃ ns : NordicSquare n, #ns.UphillPath = k} := by
  sorry

/-
PROBLEM
Every Nordic square has at least answer(n) uphill paths

PROVIDED SOLUTION
We need: for any k and ns : NordicSquare n with #ns.UphillPath = k, answer n ≤ k.

Since ns.UphillPath is a Fintype, #ns.UphillPath = Fintype.card ns.UphillPath (as a cardinal = natural number). So k = Fintype.card ns.UphillPath and we need answer n ≤ Fintype.card ns.UphillPath.

By answer_eq, answer n = 1 + gridEdgeCount n = 1 + 2*n*(n-1).

We exhibit 1 + (directedEdges ns).card distinct uphill paths:

1. ONE valley path: by valley_of_min_val, there exists a valley cell v. The singleton path [v] is an uphill path.

2. For each directed edge (u,v) in directedEdges ns: by exists_uphill_path_with_last_edge, there exists an uphill path ending with [..., u, v].

These paths are all distinct:
- The valley path has length 1 (just [v])
- Each edge path has length ≥ 2
- Two edge paths for different edges (u₁,v₁) ≠ (u₂,v₂) have different last two cells, hence different cell lists

By card_directed_edges, (directedEdges ns).card = gridEdgeCount n.

So we have at least 1 + gridEdgeCount n = answer n distinct paths, hence Fintype.card ns.UphillPath ≥ answer n.

The key step is constructing an injection from (Unit ⊕ directedEdges ns) into ns.UphillPath:
- Unit maps to the singleton valley path
- Each edge maps to the corresponding edge path via exists_uphill_path_with_last_edge (use Classical.choice to pick witnesses)

Show injectivity by case analysis: valley path vs edge paths differ by length, and two edge paths for distinct edges differ in their last two cells.

Then Fintype.card ns.UphillPath ≥ card (Unit ⊕ directedEdges ns) = 1 + (directedEdges ns).card = 1 + gridEdgeCount n = answer n.
-/
theorem imo2022_p6_lb {n : ℕ+} :
    ∀ k ∈ {k : ℕ | ∃ ns : NordicSquare n, #ns.UphillPath = k}, answer n ≤ k := by
  simp +zetaDelta at *;
  intro ns
  have h_card : (Fintype.card ns.UphillPath) ≥ 1 + (directedEdges ns).card := by
    have h_min_paths : ∃ (f : (Unit ⊕ (directedEdges ns)) → ns.UphillPath), Function.Injective f := by
      -- Define the function that maps to the singleton valley path and the edge paths.
      obtain ⟨v, hv⟩ : ∃ v : Cell n, ns.Valley v := by
        exact valley_of_min_val n.pos ns
      have h_edge_paths : ∀ e : directedEdges ns, ∃ p : ns.UphillPath, p.cells.getLast p.nonempty = e.val.2 ∧ (∃ h : p.cells.length ≥ 2, p.cells.get ⟨p.cells.length - 2, by omega⟩ = e.val.1) := by
        intro e
        obtain ⟨p, hp⟩ := exists_uphill_path_with_last_edge (by
        exact PNat.pos n) ns e.val.1 e.val.2 (by
        exact e.2 |> Finset.mem_filter.mp |>.2.1) (by
        exact e.2 |> Finset.mem_filter.mp |>.2.2)
        use p;
      choose f hf₁ hf₂ using h_edge_paths;
      use fun x => Sum.elim (fun _ => ⟨[v], by
        norm_num, hv, by
        exact List.isChain_singleton _, by
        simp +decide [ List.IsChain ]⟩) f x
      generalize_proofs at *;
      intro x y hxy; rcases x with ( _ | x ) <;> rcases y with ( _ | y ) <;> simp_all +decide [ Function.Injective ] ;
      · grind;
      · grind;
      · grind;
    obtain ⟨ f, hf ⟩ := h_min_paths; have := Fintype.card_le_of_injective f hf; aesop;
  rw [answer_eq] at *; exact h_card.trans' (by
  rw [ card_directed_edges ])

/-- The main theorem -/
theorem imo2022_p6 {n : ℕ+} :
    IsLeast {k : ℕ | ∃ ns : NordicSquare n, #ns.UphillPath = k} (answer n) :=
  ⟨imo2022_p6_mem, imo2022_p6_lb⟩

end Imo2022P6