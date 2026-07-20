# Summary of changes
## Summary

This is IMO 2022 Problem 6, which asks to show that the minimum number of uphill paths across all Nordic squares of size n is `2n² - 2n + 1`. The theorem `imo2022_p6` requires proving `IsLeast {k : ℕ | ∃ ns : NordicSquare n, #ns.UphillPath = k} (answer n)`, which has two parts:

### Fully Proved (Lower Bound)
**`imo2022_p6_lb`**: Every Nordic square has at least `answer(n) = 2n² - 2n + 1` uphill paths.

The proof constructs an explicit injection from a type of size `1 + 2n(n-1)` into the type of uphill paths:
- One singleton valley path (the cell with minimum value is always a valley)
- One uphill path for each directed edge (u,v) in the grid (adjacent cells with ns(u) < ns(v))

These paths are all distinct (edge paths differ by their last two cells, and the valley path has length 1).

Supporting lemmas proved:
- `valley_of_min_val`: Every Nordic square has at least one valley
- `exists_smaller_neighbor`: Non-valley cells have a smaller adjacent neighbor
- `exists_uphill_path_ending_at`: Every cell is the endpoint of some uphill path
- `exists_uphill_path_with_last_edge`: For each directed edge, there exists an uphill path using it as the last edge
- `uphill_path_ext`: Uphill paths are determined by their cell lists
- `uphill_path_cells_nodup`: Cells in an uphill path are distinct
- `uphill_path_length_bound`: Uphill paths have length ≤ n²
- `Fintype` instance for `UphillPath`
- `card_directed_edges`: The number of directed edges equals `2n(n-1)`
- `answer_eq`: `answer(n) = 1 + 2n(n-1)`

### Remaining Sorry (Construction/Upper Bound)
**`imo2022_p6_mem`** (line 354): There exists a Nordic square achieving exactly `answer(n)` uphill paths.

This requires constructing an explicit Nordic square for each n where the path count is exactly `2n² - 2n + 1`. The construction needs a filling where exactly one valley exists and each non-peak cell has exactly one smaller grid-neighbor. While such constructions exist for all n (verified manually for n=1,2,3,4), formalizing the general construction in Lean requires defining complex combinatorial objects (induced trees in grid graphs with independent set complements) and is extremely challenging to formalize.