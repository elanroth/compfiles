import Mathlib.Tactic

-- exact shape from Compfiles/Imo2017P6.lean: s : ℤ × ℤ, hypothesis gcd s.1 s.2 = 1
example : ∀ s ∈ ({((1 : ℤ), (0 : ℤ))} : Finset (ℤ × ℤ)), gcd s.1 s.2 = 1 := by
  intro s hs
  simp only [Finset.mem_singleton] at hs
  subst hs
  norm_num

#eval gcd (1 : ℤ) (0 : ℤ)  -- expect 1
