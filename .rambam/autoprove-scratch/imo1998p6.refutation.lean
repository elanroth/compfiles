import Mathlib.Tactic

/-!
Refutation of the Compfiles formalization of IMO 1998 P6.

The statement in `Compfiles/Imo1998P6.lean` claims: for EVERY f : ℕ+ → ℕ+
satisfying f(t²·f(s)) = s·f(t)², we have IsLeast {n : ℕ | n = f 1998} 120,
i.e. f(1998) = 120.

But f = id is admissible (t²·s = s·t²) and id 1998 = 1998 ≠ 120.
The intended statement quantifies the set over all admissible f:
  IsLeast {n : ℕ | ∃ f, (∀ s t, f (t^2 * f s) = s * (f t)^2) ∧ n = f 1998} 120
-/

namespace Imo1998P6Refutation

theorem claimed_statement_is_false :
    ¬ ∀ (f : ℕ+ → ℕ+), (∀ s t, f (t ^ 2 * f s) = s * (f t) ^ 2) →
      IsLeast {n : ℕ | n = f 1998} 120 := by
  intro h
  have hid : ∀ s t : ℕ+, id (t ^ 2 * id s) = s * (id t) ^ 2 := by
    intro s t
    simp [mul_comm]
  have h120 := (h id hid).1
  simp only [Set.mem_setOf_eq, id] at h120
  have : (120 : ℕ) = 1998 := by simpa using h120
  norm_num at this

end Imo1998P6Refutation
