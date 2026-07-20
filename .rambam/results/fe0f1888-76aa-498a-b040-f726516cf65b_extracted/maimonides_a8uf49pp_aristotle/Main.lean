import Mathlib

namespace Imo1998P6

section Setup
variable {f : ℕ+ → ℕ+} (hf : ∀ s t, f (t ^ 2 * f s) = s * (f t) ^ 2)

include hf

-- Step 1: f(f(s)) = s * (f 1)²
lemma h_ffs : ∀ s, f (f s) = s * (f 1) ^ 2 := by
  intro s; simpa using hf s 1

-- Step 2: Substituting f(s) for s in FE and using h_ffs:
lemma h_sub : ∀ s t, f (t ^ 2 * (s * (f 1) ^ 2)) = f s * (f t) ^ 2 := by
  intro s t; rw [← h_ffs hf s]; exact hf (f s) t

-- Step 3: f((f 1)² * s) = (f 1)² * f(s)
lemma h_shift : ∀ s, f ((f 1) ^ 2 * s) = (f 1) ^ 2 * f s := by
  intro s
  have := h_sub hf s 1; simp at this
  have eq1 : s * f 1 ^ 2 = f 1 ^ 2 * s := by ring
  have eq2 : f s * f 1 ^ 2 = f 1 ^ 2 * f s := by ring
  rw [eq1] at this; rw [eq2] at this; exact this

-- Step 4: (f 1)² * f(s * t²) = f(s) * (f t)²
lemma h_key : ∀ s t, (f 1) ^ 2 * f (s * t ^ 2) = f s * (f t) ^ 2 := by
  intro s t
  have key := h_sub hf s t
  have rearr : t ^ 2 * (s * (f 1) ^ 2) = (f 1) ^ 2 * (s * t ^ 2) := by ring
  rw [rearr] at key
  rw [h_shift hf] at key
  exact key

-- Step 5: (f 1) * f(t²) = (f t)²
lemma h_sq : ∀ t, f 1 * f (t ^ 2) = (f t) ^ 2 := by
  intro t
  have h_eq := h_key hf 1 t
  simp at h_eq
  exact PNat.eq (by have := congr_arg PNat.val h_eq; nlinarith [PNat.pos (f 1)])

-- Step 6: (f 1) * f(s * t²) = f(s) * f(t²)
lemma h_sq_mult : ∀ s t, f 1 * f (s * t ^ 2) = f s * f (t ^ 2) := by
  intro s t
  have h1 := h_key hf s t
  have h2 := h_sq hf t
  exact PNat.eq (by
    have := congr_arg PNat.val h1
    have := congr_arg PNat.val h2
    nlinarith [PNat.pos (f 1), PNat.pos (f (s * t ^ 2)), PNat.pos (f s)])

/-
PROBLEM
Step 7: (f(n*m))² = f(n²) * f(m²)

PROVIDED SOLUTION
From h_sq_mult with s = n², t = m: f 1 * f(n² * m²) = f(n²) * f(m²). From h_sq applied to (n*m): f 1 * f((n*m)²) = (f(n*m))². Since (n*m)² = n²*m² in PNat (by ring), combine: (f(n*m))² = f(n²) * f(m²). Use PNat.eq and nlinarith.
-/
lemma h_sq_prod : ∀ n m, (f (n * m)) ^ 2 = f (n ^ 2) * f (m ^ 2) := by
  -- From h_sq_mult with s = n² and t = m: f 1 * f(n² * m²) = f(n²) * f(m²).
  intros n m
  have h_n_sq_ent : f 1 * f (n ^ 2 * m ^ 2) = f (n ^ 2) * f (m ^ 2) := by
    exact?
  have h_sq_nm : f 1 * f ((n * m) ^ 2) = (f (n * m)) ^ 2 := by
    exact?
  have h_eq_n_sq_m_sq : f ((n * m) ^ 2) = f (n ^ 2 * m ^ 2) := by
    rw [ mul_pow ]
  have h_combined : (f (n * m)) ^ 2 = f (n ^ 2) * f (m ^ 2) := by
    rw [ ← h_sq_nm, ← h_n_sq_ent, h_eq_n_sq_m_sq ]
  exact h_combined;

/-
PROBLEM
Step 8: (f 1) * f(n*m) = f(n) * f(m)

PROVIDED SOLUTION
From h_sq: f 1 * f(n²) = (f n)² and f 1 * f(m²) = (f m)².
From h_sq_prod: (f(nm))² = f(n²) * f(m²).

Multiply both sides of h_sq_prod by (f 1)²:
(f(nm))² * (f 1)² = f(n²) * f(m²) * (f 1)²
The RHS = (f 1 * f(n²)) * (f 1 * f(m²)) = (f n)² * (f m)² = (f n * f m)²

So (f(nm) * f 1)² = (f n * f m)² (by ring in PNat).
Since squaring is injective on PNat (or ℕ+): f(nm) * f 1 = f n * f m.

Use PNat.eq and Nat.mul_self_inj or nlinarith to go from a² = b² to a = b for positive naturals.
-/
lemma h_mult : ∀ n m, f 1 * f (n * m) = f n * f m := by
  -- From h_sq: f 1 * f(n²) = (f n)² and f 1 * f(m²) = (f m)².
  have h_sq_n : ∀ n, f 1 * f (n ^ 2) = (f n) ^ 2 := by
    exact?
  have h_sq_m : ∀ m, f 1 * f (m ^ 2) = (f m) ^ 2 := by
    assumption;
  -- From h_sq_prod: (f(nm))² = f(n²) * f(m²).
  have h_sq_prod : ∀ n m, (f (n * m)) ^ 2 = f (n ^ 2) * f (m ^ 2) := by
    exact?;
  intros n m; exact PNat.eq (by
  rw [ ← sq_eq_sq₀ ] <;> norm_cast ; simp_all +decide [ mul_pow ] ;
  · simp +decide only [← h_sq_m, mul_mul_mul_comm];
    norm_num +zetaDelta at *;
  · positivity;
  · positivity)

/-
PROBLEM
f(d) = d²

PROVIDED SOLUTION
This is just h_ffs applied to s = 1: f(f(1)) = 1 * (f 1)² = (f 1)². Use h_ffs hf 1 and simp.
-/
lemma h_f_d : f (f 1) = (f 1) ^ 2 := by
  simpa using hf 1 1

/-
PROBLEM
Step 9: (f 1)^k * f(n^(k+1)) = (f n)^(k+1) by induction

PROVIDED SOLUTION
By induction on k.
Base case k = 0: (f 1 : ℕ)^0 * (f(n^1) : ℕ) = 1 * (f n : ℕ) = (f n : ℕ)^1. Trivial.

Inductive step: Assume (f 1)^k * f(n^(k+1)) = (f n)^(k+1).
Show (f 1)^(k+1) * f(n^(k+2)) = (f n)^(k+2).

From h_mult: f 1 * f(n * m) = f n * f m for all n, m.
In ℕ: (f 1 : ℕ) * (f (n * m) : ℕ) = (f n : ℕ) * (f m : ℕ).

Apply h_mult with n and n^(k+1) (so n * n^(k+1) = n^(k+2)):
(f 1 : ℕ) * (f (n^(k+2)) : ℕ) = (f n : ℕ) * (f (n^(k+1)) : ℕ).

Then (f 1)^(k+1) * f(n^(k+2)) = (f 1)^k * ((f 1) * f(n^(k+2)))
= (f 1)^k * (f n * f(n^(k+1)))
= f n * ((f 1)^k * f(n^(k+1)))
= f n * (f n)^(k+1) (by IH)
= (f n)^(k+2).

Key: use n^(k+2) = n * n^(k+1) as a PNat equation (pow_succ), and h_mult as a ℕ equation via congr_arg PNat.val.

Use PNat.val_ofNat and cast lemmas. The key cast lemma is:
(↑(a * b) : ℕ) = (↑a : ℕ) * (↑b : ℕ) for PNat, i.e., PNat.mul_coe.
And (↑(a ^ n) : ℕ) = (↑a : ℕ) ^ n for PNat.

The h_mult statement gives f 1 * f (n * m) = f n * f m as PNat equality. Convert to ℕ.
-/
lemma h_pow : ∀ (k : ℕ) (n : ℕ+),
    (f 1 : ℕ) ^ k * (f (n ^ (k + 1)) : ℕ) = ((f n : ℕ)) ^ (k + 1) := by
  intro k n; induction k <;> simp_all +decide [ pow_succ, mul_assoc, mul_comm, mul_left_comm ] ;
  rename_i k hk;
  have h_mul_step : (f 1 : ℕ) * (f (n * (n * n ^ k)) : ℕ) = (f n : ℕ) * (f (n * n ^ k) : ℕ) := by
    convert congr_arg PNat.val ( h_mult _ _ _ ) using 1 ; ring;
    simpa only [ sq, mul_assoc ] using hf;
  grind +ring

/-
PROBLEM
Step 10: (f 1 : ℕ) ∣ (f n : ℕ)

PROVIDED SOLUTION
From h_pow: (f 1)^k * f(n^(k+1)) = (f n)^(k+1) for all k, n.
This means (f 1)^k divides (f n)^(k+1) for all k ≥ 0.

We want to show (f 1) divides (f n) for all n.

Suppose for contradiction that (f 1 : ℕ) does not divide (f n : ℕ) for some n.
Let d = (f 1 : ℕ) and x = (f n : ℕ). So d does not divide x.
Let g = Nat.gcd d x, and a = d / g.
Since d does not divide x, we have a ≥ 2 (because if a = 1 then d = g which divides x).
Also Nat.Coprime (a) (x / g) (since gcd(d/gcd(d,x), x/gcd(d,x)) = 1).

From d^k | x^(k+1): (g*a)^k | (g*b)^(k+1) where b = x/g and gcd(a, b) = 1.
g^k * a^k | g^(k+1) * b^(k+1)
So a^k | g * b^(k+1).
Since gcd(a, b) = 1, gcd(a^k, b^(k+1)) = 1, so a^k | g.

This must hold for all k ≥ 0. In particular for k = g + 1: a^(g+1) | g.
But a ≥ 2 and g ≥ 1, so a^(g+1) ≥ 2^(g+1) > g (since 2^(g+1) > g for all g ≥ 1).
This contradicts a^(g+1) | g (which requires a^(g+1) ≤ g).

Key Mathlib lemmas to use:
- Nat.gcd_dvd_left, Nat.gcd_dvd_right for g | d and g | x
- Nat.Coprime.pow_dvd_of_pow_dvd or Nat.Coprime.dvd_mul_right for the coprimality argument
- The key fact: if a^k | g for all k, and a ≥ 2, g ≥ 1, then False (by taking k large enough)
- Nat.div_gcd_coprime or Nat.coprime_div_gcd_div_gcd for showing gcd(a, b) = 1 where a = d/g, b = x/g

Actually, the simplest approach might be by_contra, then use Nat.find to get the contradicting k. Or just instantiate k = (f n : ℕ) + 1 and get a contradiction.

Alternative cleaner approach: By contradiction, if d ∤ x, then d / gcd(d,x) ≥ 2. Call this a. From a^k | gcd(d,x) for all k, but a ≥ 2 means a^k grows without bound while gcd(d,x) is fixed. Contradiction.

For the coprimality step, use Nat.Coprime.dvd_mul_right: if coprime a b^(k+1), and a^k | g * b^(k+1), then a^k | g. Or more precisely, from gcd(a, b) = 1 deduce gcd(a^k, b^(k+1)) = 1 using Nat.Coprime.pow (or coprime_pow_left_iff and coprime_pow_right_iff), then use this to conclude a^k | g from a^k | g * b^(k+1).
-/
lemma h_dvd : ∀ n, (f 1 : ℕ) ∣ (f n : ℕ) := by
  -- Assume that (f 1) does not divide (f n) for some n.
  by_contra h_not_div
  push_neg at h_not_div
  obtain ⟨n, hn⟩ : ∃ n : ℕ+, ¬(f 1 : ℕ) ∣ (f n : ℕ) := by
    exact h_not_div;
  -- Let $d = (f 1 : ℕ)$ and $x = (f n : ℕ)$. So $d$ does not divide $x$.
  set d := (f 1 : ℕ)
  set x := (f n : ℕ)
  have h_not_div_dx : ¬d ∣ x := by
    assumption;
  -- From h_pow: (f 1)^k * f(n^(k+1)) = (f n)^(k+1) for all k, n.
  have h_pow_k : ∀ k : ℕ, d^k * (f (n ^ (k + 1)) : ℕ) = x ^ (k + 1) := by
    exact?;
  -- Since $d$ does not divide $x$, there exists some prime factor $p$ of $d$ such that the $p$-adic valuation of $d$ is greater than the $p$-adic valuation of $x$.
  obtain ⟨p, hp⟩ : ∃ p : ℕ, Nat.Prime p ∧ Nat.factorization d p > Nat.factorization x p := by
    exact not_forall_not.mp fun h => h_not_div_dx <| Nat.factorization_le_iff_dvd ( by aesop ) ( by aesop ) |>.1 <| fun p => by by_cases hp : Nat.Prime p <;> aesop;
  -- Choose $k$ such that $k * (Nat.factorization d p) > (k + 1) * (Nat.factorization x p)$.
  obtain ⟨k, hk⟩ : ∃ k : ℕ, k * (Nat.factorization d p) > (k + 1) * (Nat.factorization x p) := by
    exact ⟨ x.factorization p + 1, by nlinarith ⟩;
  replace h_pow_k := congr_arg ( fun z => z.factorization p ) ( h_pow_k k ) ; simp_all +decide [ Nat.factorization_mul ] ;
  rw [ Nat.factorization_mul ] at h_pow_k <;> simp_all +decide [ Nat.factorization_eq_zero_iff ];
  · linarith [ Nat.zero_le ( Nat.factorization ( f ( n ^ ( k + 1 ) ) ) p ) ];
  · aesop

end Setup

-- Now define g
noncomputable def g' (f : ℕ+ → ℕ+) (h_dvd : ∀ n, (f 1 : ℕ) ∣ (f n : ℕ)) (n : ℕ+) : ℕ+ :=
  ⟨(f n : ℕ) / (f 1 : ℕ), Nat.div_pos (Nat.le_of_dvd (PNat.pos (f n)) (h_dvd n)) (PNat.pos (f 1))⟩

section GProps
variable {f : ℕ+ → ℕ+} (hf : ∀ s t, f (t ^ 2 * f s) = s * (f t) ^ 2)
         (hd : ∀ n, (f 1 : ℕ) ∣ (f n : ℕ))

include hf hd

/-
PROBLEM
f(n) = d * g(n)

PROVIDED SOLUTION
By definition, g' f hd n = ⟨(f n : ℕ) / (f 1 : ℕ), ...⟩. So (g' f hd n : ℕ) = (f n : ℕ) / (f 1 : ℕ). Since (f 1 : ℕ) ∣ (f n : ℕ) (from hd), we have (f 1 : ℕ) * ((f n : ℕ) / (f 1 : ℕ)) = (f n : ℕ) by Nat.mul_div_cancel'. Use Nat.div_mul_cancel or Nat.mul_div_cancel'.
-/
lemma f_eq_d_mul_g :
    ∀ n, (f n : ℕ) = (f 1 : ℕ) * (g' f hd n : ℕ) := by
  exact fun n => by erw [ ← Nat.mul_div_cancel' ( hd n ) ] ; rfl;

/-
PROBLEM
g(1) = 1

PROVIDED SOLUTION
g' f hd 1 = ⟨(f 1 : ℕ) / (f 1 : ℕ), ...⟩. Since (f 1 : ℕ) > 0, (f 1 : ℕ) / (f 1 : ℕ) = 1. So g' f hd 1 = ⟨1, ...⟩ = 1. Use PNat.eq and Nat.div_self.
-/
lemma g_one : g' f hd 1 = 1 := by
  exact PNat.eq ( Nat.div_self ( PNat.pos _ ) )

/-
PROBLEM
g is completely multiplicative

PROVIDED SOLUTION
From h_mult: (f 1) * f(a*b) = f(a) * f(b) for all a, b (as PNat equality).
From f_eq_d_mul_g: (f n : ℕ) = (f 1 : ℕ) * (g' f hd n : ℕ) for all n.

In ℕ: (f 1) * (f 1) * (g' f hd (a*b)) = (f 1) * (g' f hd a) * ((f 1) * (g' f hd b))
which gives (f 1)² * g(a*b) = (f 1)² * g(a) * g(b).
Cancel (f 1)² (which is > 0) to get g(a*b) = g(a) * g(b).

More precisely: from h_mult (using hf), we get f 1 * f (a * b) = f a * f b.
Taking ℕ coercions: (f 1 : ℕ) * (f (a*b) : ℕ) = (f a : ℕ) * (f b : ℕ).
Substitute f_eq_d_mul_g: (f 1 : ℕ) * ((f 1 : ℕ) * (g' f hd (a*b) : ℕ)) = ((f 1 : ℕ) * (g' f hd a : ℕ)) * ((f 1 : ℕ) * (g' f hd b : ℕ)).
So (f 1)² * g(a*b) = (f 1)² * g(a) * g(b).
Cancel (f 1)² to get g(a*b) = g(a) * g(b).
Then use PNat.eq to conclude.
-/
lemma g_mult :
    ∀ a b, g' f hd (a * b) = g' f hd a * g' f hd b := by
  intros a b
  have h_eq : (f 1 : ℕ) * (f (a * b) : ℕ) = (f a : ℕ) * (f b : ℕ) := by
    have h_f_ab : (f 1 : ℕ) * (f (a * b) : ℕ) = (f a : ℕ) * (f b : ℕ) := by
      have := h_mult hf a b
      exact congr_arg PNat.val this;
    exact h_f_ab;
  refine PNat.eq ?_;
  exact mul_left_cancel₀ ( show ( f 1 : ℕ ) ^ 2 ≠ 0 by positivity ) ( by nlinarith! [ Nat.div_mul_cancel ( hd ( a * b ) ), Nat.div_mul_cancel ( hd a ), Nat.div_mul_cancel ( hd b ) ] )

/-
PROBLEM
g(g(n)) = n

PROVIDED SOLUTION
We need to show g(g(n)) = n where g = g' f hd.

From f_eq_d_mul_g: (f n : ℕ) = d * (g n : ℕ) where d = (f 1 : ℕ).
From h_ffs: f(f(s)) = s * (f 1)² = s * d² (as PNat).

So in ℕ: (f(f(s)) : ℕ) = (s : ℕ) * d².

Now f(s) as a PNat value gives: (f(f(s)) : ℕ) = d * (g(f(s)) : ℕ).

But we need g applied to a PNat. f(s) is a PNat, so g(f(s)) is well-defined.

Wait, g is defined for PNat inputs. We need to relate g(f(s)) to g applied to the PNat ⟨d * (g s : ℕ), ...⟩.

Actually, g' f hd n = ⟨(f n : ℕ) / d, ...⟩. So (g(n) : ℕ) = (f n : ℕ) / d.

g(g(n)) requires evaluating g at the PNat g(n). So:
(g(g(n)) : ℕ) = (f(g(n)) : ℕ) / d.

We need to show this equals (n : ℕ).

From h_ffs: f(f(n)) = n * d² (as PNat).
In ℕ: (f(f(n)) : ℕ) = (n : ℕ) * d².
And f(n) = d * g(n) (in ℕ), so f(f(n)) = f(⟨d * (g(n) : ℕ), ...⟩).

Hmm, the issue is that f takes PNat arguments, and f(n) is a PNat. We need to compute f applied to the PNat value g(n).

Actually: g'(n) is a PNat. f(g'(n)) is well-defined. And (g'(g'(n)) : ℕ) = (f(g'(n)) : ℕ) / d.

From h_ffs: f(f(n)) = n * d². In ℕ: d * g(f(n)) = n * d² (using f_eq_d_mul_g applied to f(n)). Wait, (f(f(n)) : ℕ) = d * (g(f(n)) : ℕ). And (f(f(n)) : ℕ) = (n : ℕ) * d². So d * g(f(n)) = n * d², giving g(f(n)) = n * d. Hmm, that's not g(g(n)) = n.

The issue is that g(f(n)) ≠ g(g(n)) because g(n) ≠ f(n) in general.

Let me reconsider. g(n) = f(n)/d as a PNat. So g(g(n)) = f(g(n))/d.

We need: f(g(n)) / d = n, i.e., f(g(n)) = n * d.

From h_ffs: f(f(n)) = n * d².
From f(n) = d * g(n): f(d * g(n)) = n * d².

We need f(g(n)). From h_mult: d * f(a*b) = f(a) * f(b).
Setting a = d, b = g(n): d * f(d * g(n)) = f(d) * f(g(n)).
From h_f_d: f(d) = d².
So d * f(d * g(n)) = d² * f(g(n)).
And f(d * g(n)) = n * d² (from above).
So d * n * d² = d² * f(g(n)).
n * d = f(g(n)).

Wait but we need to be careful: f(d * g(n)) uses f(n) = d * g(n), which means the input to f is the PNat f(n) = ⟨d * (g(n) : ℕ), ...⟩. But d * g(n) might not be the same PNat as f(n) even though their ℕ values are equal.

Actually, since f : ℕ+ → ℕ+, and f(n) is a specific PNat, and d * g(n) has the same ℕ value as f(n), they ARE the same PNat (PNat equality is determined by ℕ value). So f(d * g(n)) = f(f(n)) = n * d² (as PNats, provided d * g(n) = f(n) as PNats).

Hmm, we have (f(n) : ℕ) = d * (g(n) : ℕ). We need f(n) as a PNat equals some specific PNat whose ℕ value is d * (g(n) : ℕ). But f(n) IS that PNat.

OK let me simplify. In ℕ:
1. (f(g(n)) : ℕ) = d * (g(g(n)) : ℕ) [from f_eq_d_mul_g applied to g(n)]
2. d * f(d_pnat * g(n)) = f(d_pnat) * f(g(n)) [from h_mult with a = d_pnat, b = g(n)]
   where d_pnat = f 1 as a PNat.

But this requires f 1 and g(n) as PNat values in h_mult. And the PNat d * g(n) might not equal f(n) as a PNat... unless we construct it properly.

Actually wait: in PNat, if (a : ℕ) = (b : ℕ) then a = b (PNat.eq). So if (f(n) : ℕ) = (f 1 : ℕ) * (g(n) : ℕ), and we define the PNat (f 1) * g(n), then its ℕ value is (f 1 : ℕ) * (g(n) : ℕ) = (f(n) : ℕ). So f(n) = (f 1) * g(n) as PNats.

Then f(f(n)) = f((f 1) * g(n)). By h_mult (PNat equality): f 1 * f((f 1) * g(n)) = f(f 1) * f(g(n)).
So f 1 * f(f(n)) = f(f 1) * f(g(n)).
From h_ffs: f(f(n)) = n * (f 1)².
From h_f_d: f(f 1) = (f 1)².
So f 1 * (n * (f 1)²) = (f 1)² * f(g(n)).
n * (f 1)³ = (f 1)² * f(g(n)).
n * (f 1) = f(g(n)).
So (f(g(n)) : ℕ) = (n : ℕ) * (f 1 : ℕ).

And from f_eq_d_mul_g: (f(g(n)) : ℕ) = (f 1 : ℕ) * (g(g(n)) : ℕ).
So (f 1 : ℕ) * (g(g(n)) : ℕ) = (n : ℕ) * (f 1 : ℕ).
Cancel (f 1 : ℕ) (> 0): (g(g(n)) : ℕ) = (n : ℕ).
So g(g(n)) = n as PNats.

Clean proof:
1. f(n) = (f 1) * g(n) as PNats (from f_eq_d_mul_g and PNat.eq)
2. f 1 * f(f(n)) = f(f 1) * f(g(n)) (from h_mult applied to (f 1) and g(n), using f(n) = (f 1)*g(n))
3. f 1 * n * (f 1)² = (f 1)² * f(g(n)) (from h_ffs and h_f_d)
4. f(g(n)) = n * (f 1) (cancel f 1)
5. (f 1) * g(g(n)) = n * (f 1) (from f_eq_d_mul_g)
6. g(g(n)) = n (cancel f 1)

For step 2, I need: f((f 1) * g(n)) = f(f(n)), using f(n) = (f 1) * g(n). This requires showing f(n) = (f 1) * g(n) as PNat equality, then substituting.
-/
lemma g_inv :
    ∀ n, g' f hd (g' f hd n) = n := by
  intro n
  have h_g_g : f (g' f hd n) = n * (f 1) := by
    -- From h_mult: f 1 * f(f(n)) = f(f(1)) * f(g(n)).
    have h_mult_g : f 1 * f (f n) = f (f 1) * f (g' f hd n) := by
      have h_mult_g : f 1 * f ((f 1) * (g' f hd n)) = f (f 1) * f (g' f hd n) := by
        apply h_mult;
        assumption;
      convert h_mult_g using 3;
      exact PNat.eq ( f_eq_d_mul_g hf hd n );
    -- From h_ffs: f(f(n)) = n * (f 1)² and f(f(1)) = (f 1)².
    have h_ffs : f (f n) = n * (f 1) ^ 2 ∧ f (f 1) = (f 1) ^ 2 := by
      exact ⟨ by simpa using hf n 1, by simpa using hf 1 1 ⟩;
    simp_all +decide [ mul_comm, mul_left_comm, sq ];
    exact PNat.eq ( by { have := congr_arg PNat.val h_mult_g; nlinarith [ PNat.pos ( f 1 ), PNat.pos ( f ( g' f hd n ) ) ] } );
  unfold g' at *; aesop;

/-
PROBLEM
g is injective (from g(g(n)) = n)

PROVIDED SOLUTION
From g_inv: g(g(n)) = n for all n. So if g(a) = g(b), then a = g(g(a)) = g(g(b)) = b. Standard left-inverse implies injective argument: Function.Injective.comp or Function.HasLeftInverse.injective.
-/
lemma g_inj : Function.Injective (g' f hd) := by
  intros a b hab;
  have := @g_inv f hf hd a; have := @g_inv f hf hd b; aesop;

/-
PROBLEM
g maps primes to primes

PROVIDED SOLUTION
We need to show g(p) is prime for every prime p.

Suppose g(p) is not prime. Since g(p) is a PNat, (g(p) : ℕ) ≥ 1. If (g(p) : ℕ) = 1, then g(p) = 1, so g(g(p)) = g(1) = 1 (by g_one), but g(g(p)) = p (by g_inv). So (p : ℕ) = 1, contradicting p prime (Nat.Prime.one_lt).

So (g(p) : ℕ) ≥ 2. Since it's not prime and ≥ 2, it's composite: there exist a, b : ℕ with a ≥ 2, b ≥ 2, (g(p) : ℕ) = a * b.

Define a_pnat = ⟨a, ...⟩ and b_pnat = ⟨b, ...⟩. Then g(p) = a_pnat * b_pnat (as PNats).

From g_mult: g(g(p)) = g(a_pnat * b_pnat) = g(a_pnat) * g(b_pnat).
From g_inv: g(g(p)) = p.
So p = g(a_pnat) * g(b_pnat).

Since p is prime (in ℕ): (p : ℕ) = (g(a_pnat) : ℕ) * (g(b_pnat) : ℕ).
So either (g(a_pnat) : ℕ) = 1 or (g(b_pnat) : ℕ) = 1.

WLOG (g(a_pnat) : ℕ) = 1. Then g(a_pnat) = 1 (as PNat). By g_inv: a_pnat = g(g(a_pnat)) = g(1) = 1. So a = 1, contradicting a ≥ 2.

Use Nat.Prime.eq_one_or_self_of_dvd or similar for the factorization step.
-/
lemma g_prime :
    ∀ p : ℕ+, Nat.Prime (p : ℕ) → Nat.Prime (g' f hd p : ℕ) := by
  intro p hp
  by_contra h_not_prime_g_p
  obtain ⟨a, b, ha, hb, hab⟩ : ∃ a b : ℕ+, 2 ≤ a ∧ 2 ≤ b ∧ g' f hd p = a * b := by
    have := Nat.exists_dvd_of_not_prime2 ( show 1 < ( g' f hd p : ℕ ) from ?_ ) h_not_prime_g_p;
    · obtain ⟨ m, hm₁, hm₂, hm₃ ⟩ := this; exact ⟨ ⟨ m, pos_of_gt hm₂ ⟩, ⟨ ( g' f hd p : ℕ ) / m, Nat.div_pos ( by linarith ) ( pos_of_gt hm₂ ) ⟩, hm₂, by exact Nat.lt_of_le_of_ne ( Nat.div_pos ( by linarith ) ( pos_of_gt hm₂ ) ) ( Ne.symm ( by intro t; have := Nat.div_mul_cancel hm₁; aesop ) ), PNat.eq ( Eq.symm <| Nat.mul_div_cancel' hm₁ ) ⟩ ;
    · refine' Nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨ _, _ ⟩;
      · exact PNat.ne_zero _;
      · intro h; have := g_inv hf hd p; simp_all +decide ;
        have := g_one hf hd; aesop;
  -- From g_mult, we have g(g(p)) = g(a) * g(b). But g(g(p)) = p (by g_inv). So p = g(a) * g(b).
  have h_p_eq_ga_gb : p = g' f hd a * g' f hd b := by
    have h_gg_p : g' f hd (g' f hd p) = p := by
      exact?;
    rw [ ← h_gg_p, hab, g_mult ];
    assumption;
  simp_all +decide [ Nat.prime_mul_iff ];
  cases hp <;> simp_all +decide [ g_inv ]

end GProps

/-
PROBLEM
Distinct primes bound: for distinct primes p, q, r : p * q^3 * r ≥ 120

PROVIDED SOLUTION
Case split on the values of p, q, r. Since they are distinct primes:
- All primes are ≥ 2.
- If q = 2: p, r ≥ 3 and p ≠ r, so one of them ≥ 5 (the primes ≥ 3 are 3, 5, 7, ...; two distinct ones give min product 3*5=15). So p * 8 * r ≥ 120.
- If q ≥ 3: q³ ≥ 27. p and r are distinct primes, at least one ≠ q. If q = 3, p,r are distinct primes ≠ 3, min p*r is 2*5=10, total ≥ 270. If q ≥ 5: q³ ≥ 125, p*r ≥ 2*3=6, total ≥ 750.

Key approach: use Nat.Prime.two_le to get p ≥ 2, q ≥ 2, r ≥ 2.
Then use interval_cases or omega after establishing lower bounds.

More concretely:
- q ≥ 2. If q = 2: p ≥ 2, r ≥ 2, p ≠ 2, r ≠ 2, so p ≥ 3, r ≥ 3 (since 2 is the smallest prime). p ≠ r and both ≥ 3 and prime means one ≥ 5. So p * r ≥ 3 * 5 = 15. Total: 15 * 8 = 120.
- q ≥ 3: If q = 3, then q³ = 27. p,r ≥ 2, p ≠ q, r ≠ q, p ≠ r. Since p ≠ 3 and p prime, p ∈ {2,5,7,...}. Similarly r. Since p ≠ r, min(p*r) = 2*5 = 10. 27*10 = 270 ≥ 120.
- q ≥ 5: q³ ≥ 125. p*r ≥ 2*3 = 6. 125*6 = 750 ≥ 120.

To show "two distinct primes both ≥ 3 have product ≥ 15": if both ≥ 3, one is ≥ 5 (since they're distinct primes and 3 is the only prime equal to 3). Actually no, they could be 3 and 5, or 3 and 7, etc. But they can't both be 3 since distinct. So one ≥ 3 and the other ≥ 5, product ≥ 15.

For formal proof, use omega after establishing enough case splits. Use Nat.Prime.eq_two_or_odd and Nat.Prime.two_le.
-/
lemma distinct_primes_bound (p q r : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q) (hr : Nat.Prime r)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) :
    120 ≤ p * q ^ 3 * r := by
  rcases p with ( _ | _ | _ | p ) <;> rcases q with ( _ | _ | _ | q ) <;> rcases r with ( _ | _ | _ | r ) <;> simp_all! +arith +decide;
  · nlinarith [ sq q, sq r, mul_pos ( Nat.succ_pos q ) ( Nat.succ_pos r ) ];
  · rcases p with ( _ | _ | p ) <;> rcases r with ( _ | _ | r ) <;> (norm_num at * <;> nlinarith;);
  · nlinarith [ sq p, sq q, mul_pos ( Nat.succ_pos p ) ( Nat.succ_pos q ) ];
  · grind +ring

/-
PROBLEM
1998 = 2 * 3^3 * 37

PROVIDED SOLUTION
Just compute: 2 * 3^3 * 37 = 2 * 27 * 37 = 54 * 37 = 1998. Use native_decide or decide or PNat.eq and omega.
-/
lemma factorization_1998 : (1998 : ℕ+) = ⟨2, by omega⟩ * ⟨3, by omega⟩ ^ 3 * ⟨37, by omega⟩ := by
  decide +revert

/-
PROBLEM
The main theorem

PROVIDED SOLUTION
The proof combines all the helper lemmas:

1. Obtain h_dvd: ∀ n, (f 1 : ℕ) ∣ (f n : ℕ) from `h_dvd hf`.
2. Let g = g' f h_dvd. Then:
   - f(n) = (f 1) * g(n) in ℕ  (f_eq_d_mul_g)
   - g is multiplicative (g_mult)
   - g(g(n)) = n (g_inv)
   - g maps primes to primes (g_prime)
   - g is injective (g_inj)
3. 1998 = 2 * 3³ * 37 (factorization_1998).
4. f(1998) = f(2 * 3³ * 37) in ℕ.
   Using f_eq_d_mul_g: (f 1998 : ℕ) = (f 1 : ℕ) * (g 1998 : ℕ).
5. Using g_mult repeatedly:
   g(1998) = g(2 * 3³ * 37) = g(2) * g(3³) * g(37) = g(2) * g(3)³ * g(37).

   More precisely: g(2 * (3^3 * 37)) = g(2) * g(3^3 * 37) = g(2) * g(3^3) * g(37).
   And g(3^3) = g(3*3*3) = g(3)*g(3)*g(3) = g(3)^3.

   Actually, since g_mult gives g(a*b) = g(a)*g(b), apply it step by step.
   Also g(3^3) can be computed: 3^3 = 27 as PNat, and g(27) = g(3*9) = g(3)*g(9) = g(3)*g(3*3) = g(3)*g(3)*g(3).

6. So (f 1998 : ℕ) = (f 1 : ℕ) * (g 2 : ℕ) * (g 3 : ℕ)^3 * (g 37 : ℕ).
   Since (f 1 : ℕ) ≥ 1 (positive), it suffices to show (g 2 : ℕ) * (g 3 : ℕ)^3 * (g 37 : ℕ) ≥ 120.

7. g(2), g(3), g(37) are distinct primes:
   - g(2) prime (g_prime, since 2 is prime)
   - g(3) prime (g_prime, since 3 is prime)
   - g(37) prime (g_prime, since 37 is prime)
   - g(2) ≠ g(3) (from g_inj, since 2 ≠ 3)
   - g(2) ≠ g(37) (from g_inj, since 2 ≠ 37)
   - g(3) ≠ g(37) (from g_inj, since 3 ≠ 37)

8. Apply distinct_primes_bound to conclude (g 2 : ℕ) * (g 3 : ℕ)^3 * (g 37 : ℕ) ≥ 120.

9. Since (f 1 : ℕ) ≥ 1, (f 1998 : ℕ) = (f 1) * ... ≥ 1 * 120 = 120.

For the computation of g(1998) = g(2) * g(3)^3 * g(37) in PNat, use factorization_1998 and g_mult.
-/
theorem lower_bound_1998
    (f : ℕ+ → ℕ+)
    (hf : ∀ s t, f (t ^ 2 * f s) = s * (f t) ^ 2) :
    120 ≤ (f 1998 : ℕ) := by
  -- By definition of $f$, we know that $f(1998) = f(1) \cdot g(1998)$
  set d := f 1
  have hdvd : ∀ n, (d : ℕ) ∣ (f n : ℕ) := by
    exact?
  set g := g' f hdvd
  have h_fg : ∀ n, (f n : ℕ) = d * (g n : ℕ) := by
    exact?
  have h_f1998 : (f 1998 : ℕ) = d * (g 1998 : ℕ) := by
    exact h_fg _;
  -- From Lemma 2, we know that $g(2)$, $g(3)$, and $g(37)$ are distinct primes.
  have h_distinct_primes : Nat.Prime (g 2 : ℕ) ∧ Nat.Prime (g 3 : ℕ) ∧ Nat.Prime (g 37 : ℕ) ∧ g 2 ≠ g 3 ∧ g 2 ≠ g 37 ∧ g 3 ≠ g 37 := by
    refine' ⟨ _, _, _, _, _, _ ⟩;
    exact g_prime hf hdvd 2 Nat.prime_two;
    · exact g_prime hf hdvd 3 Nat.prime_three;
    · exact g_prime hf hdvd 37 ( by decide );
    · exact fun h => absurd ( g_inj hf hdvd h ) ( by decide );
    · exact fun h => by have := g_inj hf hdvd h; contradiction;
    · exact fun h => by have := g_inj hf hdvd h; contradiction;
  -- From Lemma 3, we know that $g(1998) = g(2) \cdot g(3)^3 \cdot g(37)$.
  have h_g1998 : (g 1998 : ℕ) = (g 2 : ℕ) * (g 3 : ℕ) ^ 3 * (g 37 : ℕ) := by
    -- From Lemma 2, we know that $g$ is multiplicative.
    have h_g_mult : ∀ a b : ℕ+, (g (a * b) : ℕ) = (g a : ℕ) * (g b : ℕ) := by
      intros a b
      have := g_mult hf hdvd a b
      exact congr_arg PNat.val this;
    exact h_g_mult 2 999 ▸ h_g_mult 3 333 ▸ h_g_mult 3 111 ▸ h_g_mult 3 37 ▸ by ring;
  -- From Lemma 4, we know that $g(2) \cdot g(3)^3 \cdot g(37) \geq 120$.
  have h_bound : (g 2 : ℕ) * (g 3 : ℕ) ^ 3 * (g 37 : ℕ) ≥ 120 := by
    apply distinct_primes_bound;
    all_goals norm_num [ h_distinct_primes ] at * ;
  nlinarith [ PNat.pos d ]

end Imo1998P6