/-
Elan's working area, wired into the build so the P5 prove/integrate/verify cycle
has a real build gate rather than a standalone `lake env lean` check.

`partial` and `end` are Lean keywords, so directory-derived module names under
`Elan/partial/` need «guillemets».

TWO FILES ARE DELIBERATELY EXCLUDED. They have bit-rotted against current
mathlib and fail to elaborate (checked 2026-07-27, Lean 4.31.0-rc1). They are
excluded so this gate is green and meaningful, not so the rot is hidden — each
needs real proof maintenance, not a rename:

  Elan/complete/Imo1970P6.lean   4 errors  (`grind` failed x2; a Fintype instance
                                            for the acute-triple subtype no longer
                                            synthesizes, which then strands :492)
  Elan/complete/Imo2016P5.lean   5 errors  (`rewrite` pattern not found; `linarith`
                                            failed x2; application type mismatch)

Repaired 2026-07-27 and now built:
  Elan/complete/Imo2000P5.lean   `aesop` at :186 no longer closes the goal. The fix
                                 already existed in Elan/Imo2000P5/attempt1/Submission.lean,
                                 whose only difference from this file was `grind` in
                                 that one position; it had never been propagated back.
                                 With the fix applied the two files were byte-identical
                                 and shared a namespace (so they could not both be
                                 imported), and attempt1/ was deleted as redundant.
  Elan/partial/Imo1998P6.lean    `convert ... using 1` left two ℕ+ coercion goals
                                 (`↑(f 1) * ↑(f (t*u)) = ↑(f 1 * f (t*u))`);
                                 discharged with `simp [PNat.mul_coe]`.

Re-add a module here once its file elaborates again.
-/

import Elan.complete.Imo1988P3
import Elan.complete.Imo2000P5
import Elan.«partial».Imo1998P6
import Elan.«partial».Ciim2022P6
import Elan.«partial».Imo2010P3
import Elan.«partial».Imo2021P3
import Elan.«partial».Imo2022P3
import Elan.«partial».Imo2022P6
import Elan.«partial».Imo2023P5
import Elan.unstarted.Imo2004P6_loophole
import Elan.unstarted.Imo2009P6_answer_only
