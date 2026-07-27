/-
Elan's working area, wired into the build so the P5 prove/integrate/verify cycle
has a real build gate rather than a standalone `lake env lean` check.

`partial` and `end` are Lean keywords, so directory-derived module names under
`Elan/partial/` need «guillemets».

ONE FILE IS DELIBERATELY EXCLUDED. It has bit-rotted against current
mathlib and fails to elaborate (checked 2026-07-27, Lean 4.31.0-rc1). It is
excluded so this gate is green and meaningful, not so the rot is hidden — it
needs real proof maintenance, not a rename:

  Elan/complete/Imo1970P6.lean   2 errors, down from 4. The `Fintype` failure is
                                 FIXED: `IsAcuteTriple` is a `noncomputable def : Prop`
                                 so its subtype has no `DecidablePred`; a `classical`
                                 in `ordered_triples_mul_bound` restores the instance
                                 and also cleared the goal it had stranded at :492.
                                 Still open, both `grind` regressions:
                                   :113 — after `use`, must show the Cramer's-rule
                                          α, β satisfy the two coordinate equations.
                                          `field_simp` leaves a rational identity that
                                          `ring`/`nlinarith` do not close; wants an
                                          explicit `div_eq_iff h_det` derivation.
                                   :312 — a 100-point non-collinearity case split.

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
  Elan/complete/Imo2016P5.lean   four independent regressions: the renamed
                                 `Finset.prod_eq_mul_prod_diff_singleton_of_mem`;
                                 a `convert` now emitting a spurious instance-equality
                                 goal (closed with `try rfl`); a stranded `convert`
                                 side-goal needing `PL`/`PR` unfolded and
                                 `Rf_eq_Lf_add_two`; and an `nlinarith` hint whose
                                 `Real.exp` argument was spelled in a form `ring_nf`
                                 no longer produces, so the two `exp` terms were not
                                 the same atom.

Re-add a module here once its file elaborates again.
-/

import Elan.complete.Imo1988P3
import Elan.complete.Imo2000P5
import Elan.«partial».Imo1998P6
import Elan.complete.Imo2016P5
import Elan.«partial».Ciim2022P6
import Elan.«partial».Imo2010P3
import Elan.«partial».Imo2021P3
import Elan.«partial».Imo2022P3
import Elan.«partial».Imo2022P6
import Elan.«partial».Imo2023P5
import Elan.«partial».Usa1977P1
import Elan.unstarted.Imo2004P6_loophole
import Elan.unstarted.Imo2009P6_answer_only
