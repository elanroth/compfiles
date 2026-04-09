# Summary of changes
## IMO 2022 Problem 6 - Partial Formalization

This is IMO 2022 Problem 6, one of the hardest problems on that year's paper. The problem asks to prove that `2n²-2n+1` is the minimum number of "uphill paths" over all Nordic squares on an n×n grid.

### What was proved

I successfully proved the **lower bound direction** of the `IsLeast` statement — that every Nordic square has at least `answer n = 2n²-2n+1` uphill paths. This involved:

1. **Basic helper lemmas** (all proved):
   - `Adjacent_symm`: adjacency is symmetric
   - `Adjacent_irrefl`: no cell is adjacent to itself
   - `min_cell_is_valley`: the minimum-valued cell is a valley
   - `exists_valley`: every grid has at least one valley
   - `not_valley_has_strictly_smaller_neighbor`: non-valleys have a strictly smaller adjacent cell
   - `UphillPath.ext'`: path extensionality
   - `exists_path_ending_at`: for every cell, there exists an uphill path ending at it (proved by well-founded induction on cell values)

2. **Counting lemmas** (all proved):
   - `adj_pairs_card`: the number of ordered adjacent pairs in an n×n grid is `4n(n-1)`
   - `directed_edges_card`: the number of directed increasing edges is `2n(n-1)`

3. **Key lower bound** (proved):
   - `lb_card`: `↑(answer n) ≤ #ns.UphillPath` for any Nordic square `ns`
   - This constructs an injection from `Fin(2n(n-1)) ⊕ Unit` into `UphillPath` by mapping each directed increasing edge to a specific uphill path, plus one valley singleton path

4. **Lower bound direction** (proved):
   - `imo2022_p6_lb`: every element of `{k | ∃ ns, #ns.UphillPath = k}` is `≥ answer n`

### What remains (1 sorry)

- `imo2022_p6_mem` (line 244): The **construction/existence** part — showing there EXISTS a Nordic square achieving exactly `answer n` uphill paths. This requires constructing an explicit combinatorial object (a specific bijection from grid cells to {1,...,n²}) for arbitrary n, and proving its uphill path count equals exactly `2n²-2n+1`. The construction uses an independent set in the grid whose complement forms a spanning tree, with a DFS numbering of the tree cells. This is the hardest part of the IMO problem and is extremely complex to formalize for general n.

The file is `Main.lean` and builds successfully with the single remaining sorry.