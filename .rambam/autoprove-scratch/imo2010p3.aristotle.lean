import Mathlib.Tactic
import Mathlib.Data.Int.GCD
import Mathlib.NumberTheory.Multiplicity

namespace Imo2010P3

abbrev PosInt : Type := { x : ℤ // 0 < x }
notation "ℤ>0" => PosInt

-- Helper: unwrap PosInt addition
instance : Add PosInt where
  add a b := ⟨a.val + b.val, by linarith [a.prop, b.prop]⟩

-- SolutionSet: g = id or g x = x + c for some constant c : ℤ>0
def SolutionSet : Set (ℤ>0 → ℤ>0) := { f | f = id ∨ ∃ c, ∀ x, f x = x + c }

/-
Key lemma: if (g(m)+n)(g(n)+m) is always a perfect square, then g is injective
Proof: if g(a) = g(b), then for any m, (g(m)+a)(g(a)+m) and (g(m)+b)(g(b)+m) = (g(m)+b)(g(a)+m)
are both perfect squares. Since g(a)=g(b) the second factors agree, so first factors agree: a=b.
-/
lemma injective_of_sq (g : ℤ>0 → ℤ>0) (h : ∀ m n : ℤ>0, IsSquare ((g m + n) * (g n + m))) :
    Function.Injective g := by
  intro a b hab
  -- (g(a)+a)(g(a)+a) = (g(a)+a)^2 is a square
  -- (g(a)+b)(g(b)+a) = (g(a)+b)(g(a)+a) must be a square
  -- similarly swap m,n: (g(b)+a)(g(a)+b) = (g(a)+b)(g(a)+a)^2... hmm
  -- If g(a)=g(b), then (g(m)+a)(g(a)+m) and (g(m)+b)(g(b)+m)=(g(m)+b)(g(a)+m) are squares
  -- With m=a: (g(a)+a)^2 is a square (trivial) and (g(a)+b)(g(a)+a) must be a square
  -- With m=b: (g(b)+a)(g(a)+b)=(g(a)+a)(g(a)+b) and (g(b)+b)^2=(g(a)+b)^2 are squares
  -- So (g(a)+a)(g(a)+b) is a square and (g(a)+b)(g(a)+a) is a square: consistent
  -- Need a stronger argument. Use: (g(n)+a)(g(a)+n) and (g(n)+b)(g(b)+n) both squares
  -- Since g(a)=g(b): second factors equal. So (g(n)+a)*(X) and (g(n)+b)*(X) both squares
  -- where X=g(a)+n. If X≠0: ratio (g(n)+a)/(g(n)+b) must be a ratio of squares, i.e. a perfect square.
  -- For large n, (g(n)+a)/(g(n)+b) → 1, so it must equal 1 eventually, giving a=b.
  -- Choose a prime $p$ such that $p > \max(a, b)$ and $p > g(a) + \max(a, b)$.
  obtain ⟨p, hp_prime, hp_gt⟩ : ∃ p : ℕ, Nat.Prime p ∧ p > max a.val b.val ∧ p > (g a).val + max a.val b.val := by
    obtain ⟨ p, hp ⟩ := Nat.exists_infinite_primes ( Int.natAbs ( g a + max a b ) + 1 );
    exact ⟨ p, hp.2, by cases max_cases ( a : ℤ ) ( b : ℤ ) <;> cases abs_cases ( g a + max a b : ℤ ) <;> linarith! [ show ( g a : ℤ ) > 0 from mod_cast Subtype.property ( g a ), show ( max a b : ℤ ) > 0 from mod_cast lt_max_iff.mpr ( Or.inl a.prop ) ], by cases max_cases ( a : ℤ ) ( b : ℤ ) <;> cases abs_cases ( g a + max a b : ℤ ) <;> linarith! [ show ( g a : ℤ ) > 0 from mod_cast Subtype.property ( g a ), show ( max a b : ℤ ) > 0 from mod_cast lt_max_iff.mpr ( Or.inl a.prop ) ] ⟩;
  -- Choose $m = p - g(a)$.
  set m : PosInt := ⟨p - (g a).val, by
    grind⟩
  generalize_proofs at *;
  -- Then $(g(m) + a)(g(a) + m) = (g(m) + a)p$ and $(g(m) + b)(g(b) + m) = (g(m) + b)p$ are both perfect squares.
  have h_sq_a : IsSquare ((g m + a).val * p) := by
    obtain ⟨ k, hk ⟩ := h m a;
    use k.val;
    convert congr_arg Subtype.val hk using 1 <;> norm_num [m]
  have h_sq_b : IsSquare ((g m + b).val * p) := by
    obtain ⟨ k, hk ⟩ := h m b;
    use k.val;
    convert congr_arg Subtype.val hk using 1 <;> simp +zetaDelta at *
    grind
  obtain ⟨k, hk⟩ := h_sq_a
  obtain ⟨l, hl⟩ := h_sq_b
  simp_all +decide
  -- Since $p$ is prime, $p$ must divide $k$ and $l$.
  have hp_div_k : (p : ℤ) ∣ k := by
    exact Int.Prime.dvd_pow' hp_prime <| by rw [ sq ] ; exact hk ▸ dvd_mul_left _ _;
  have hp_div_l : (p : ℤ) ∣ l := by
    exact Int.Prime.dvd_pow' hp_prime <| by rw [ sq ] ; exact hl ▸ dvd_mul_left _ _;
  obtain ⟨ k, rfl ⟩ := hp_div_k; obtain ⟨ l, rfl ⟩ := hp_div_l; ring_nf at hk hl;
  -- Dividing both sides of the equations by $p$, we get $g(m) + a = p k^2$ and $g(m) + b = p l^2$.
  have h_div_a : (g m).val + a.val = p * k ^ 2 := by
    nlinarith only [ hk, hp_prime.two_le ]
  have h_div_b : (g m).val + b.val = p * l ^ 2 := by
    nlinarith only [ hl, hp_prime.two_le ];
  -- Since $p$ is prime and $p > \max(a, b)$, we have $k^2 = l^2$.
  have h_kl : k ^ 2 = l ^ 2 := by
    nlinarith [ show ( a : ℤ ) > 0 from mod_cast a.prop, show ( b : ℤ ) > 0 from mod_cast b.prop ];
  grind

-- Key lemma: |g(n+1) - g(n)| = 1
-- From the functional equation with m and varying n,
-- once we know g is injective and the sq condition holds,
-- consecutive values must differ by exactly 1.
lemma step_one (g : ℤ>0 → ℤ>0)
    (hsq : ∀ m n : ℤ>0, IsSquare ((g m + n) * (g n + m)))
    (hinj : Function.Injective g) :
    ∀ n : ℤ>0, (g ⟨n.val + 1, by linarith [n.prop]⟩).val = g n + 1 ∨
               (g ⟨n.val + 1, by linarith [n.prop]⟩).val + 1 = g n := by
  sorry

/-
Main theorem
-/
theorem imo2010_p3 (g : ℤ>0 → ℤ>0) :
    g ∈ SolutionSet ↔ ∀ m n, IsSquare ((g m + n) * (g n + m)) := by
  constructor
  · rintro (rfl | ⟨c, hc⟩) m n
    · use m + n; rw [id, id, add_comm m n]
    · use m + n + c; rw [hc m, hc n]; simp only [add_comm, add_left_comm]
  · -- Hard direction: functional equation implies g = id or g(x) = x + c
    -- Step 1: g is injective (proved via sq condition)
    -- Step 2: |g(n+1)-g(n)| = 1 for all n
    -- Step 3: g monotone increasing (slope -1 would give non-positive values)
    -- Step 4: g(n) = n + (g(1) - 1) for all n, where g(1)-1 ≥ 0
    -- If g(1).val = 1 then g = id, else c = g(1) - 1 > 0
    intro hsq
    -- We show g x = x + c where c = g(1) - 1 (as integers), or g = id
    -- Since g(1) ≥ 1 (positive integer), c ≥ 0
    -- Case c = 0: g = id. Case c > 0: g x = x + c.
    revert hsq
    intro hsq
    have hinj : Function.Injective g := injective_of_sq g hsq
    have h_step : ∀ n : PosInt, (g ⟨n.val + 1, by linarith [n.prop]⟩).val = g n + 1 ∨ (g ⟨n.val + 1, by linarith [n.prop]⟩).val + 1 = g n :=
      step_one g hsq hinj
    -- By induction, we can show that $g(n) = g(1) + (n - 1)$ for all $n$.
    have h_ind : ∀ n : PosInt, (g n).val = (g ⟨1, by linarith⟩).val + (n.val - 1) := by
      intro n
      induction' n with n ih;
      induction' n using Int.induction_on with n ihn n ihn <;> norm_num at *;
      · contradiction;
      · rcases n with ( _ | n ) <;> simp_all +decide;
        cases h_step ( n + 1 ) ( by linarith ) <;> simp_all +decide [ add_assoc ];
        contrapose! hsq;
        refine' ⟨ n + 2, by linarith, 1, by linarith, _ ⟩ ; simp_all +decide [ IsSquare ];
        intro x hx; erw [ Subtype.mk_eq_mk ] at *; simp_all +decide [ ← sq ] ;
        exact fun h => by nlinarith only [ show x = g ⟨ 1, by linarith ⟩ + n + 1 by nlinarith only [ hx, h, show ( g ⟨ 1, by linarith ⟩ : ℤ ) > 0 from mod_cast Subtype.property _ ], h, show ( g ⟨ 1, by linarith ⟩ : ℤ ) > 0 from mod_cast Subtype.property _ ] ;
      · linarith;
    -- Let $c = g(1) - 1$. Then $g(n) = n + c$ for all $n$.
    obtain ⟨c, hc⟩ : ∃ c : ℤ, ∀ n : PosInt, (g n).val = n.val + c := by
      exact ⟨ ( g ⟨ 1, by decide ⟩ : ℤ ) - 1, fun n => by linarith [ h_ind n ] ⟩;
    -- Since $g$ maps to positive integers, we must have $c \geq 0$.
    have hc_nonneg : 0 ≤ c := by
      linarith! [ hc ⟨ 1, by decide ⟩, Subtype.property ( g ⟨ 1, by decide ⟩ ) ];
    rcases c with ⟨ _ | c ⟩ <;> norm_num at *;
    · exact Or.inl <| funext fun x => Subtype.ext <| hc x x.prop;
    · exact Or.inr ⟨ ⟨ c + 1, by linarith ⟩, fun x => Subtype.ext <| hc x x.prop ⟩

end Imo2010P3