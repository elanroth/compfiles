/-
Elan's working area, wired into the build so the P5 prove/integrate/verify cycle
has a real build gate rather than a standalone `lake env lean` check.

`partial` and `end` are Lean keywords, so directory-derived module names under
`Elan/partial/` need «guillemets».

FOUR FILES ARE DELIBERATELY EXCLUDED. They have bit-rotted against current
mathlib and fail to elaborate (checked 2026-07-27, Lean 4.31.0-rc1). They are
excluded so this gate is green and meaningful, not so the rot is hidden — each
needs real proof maintenance, not a rename:

  Elan/complete/Imo1970P6.lean   4 errors  (`grind` failed x2; instance synthesis; unsolved goals)
  Elan/complete/Imo2016P5.lean   5 errors  (`rewrite` pattern not found; `linarith` failed x2; type mismatch)
  Elan/complete/Imo2000P5.lean   1 error   (`simp` hits maximum recursion depth at :186)
  Elan/partial/Imo1998P6.lean    1 error   (unsolved goals at :248)

Note Elan/Imo2000P5/attempt1/Submission.lean DOES still elaborate, so it is the
working copy of that proof; complete/Imo2000P5.lean is the rotted one.

Re-add a module here once its file elaborates again.
-/

import Elan.Imo2000P5.attempt1.Submission
import Elan.complete.Imo1988P3
import Elan.«partial».Ciim2022P6
import Elan.«partial».Imo2010P3
import Elan.«partial».Imo2021P3
import Elan.«partial».Imo2022P3
import Elan.«partial».Imo2022P6
import Elan.«partial».Imo2023P5
import Elan.unstarted.Imo2004P6_loophole
import Elan.unstarted.Imo2009P6_answer_only
