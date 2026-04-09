import Mathlib

namespace Imo1998P6

section Setup
variable {f : ℕ+ → ℕ+} (hf : ∀ s t, f (t ^ 2 * f s) = s * (f t) ^ 2)
include hf

/-! ## Part 1: Basic consequences of the functional equation -/

/-
PROVIDED SOLUTION
Substitute t=1 in the functional equation: f(1^2 * f(s)) = s * f(1)^2. Since 1^2 * f(s) = f(s), this gives f(f(s)) = s * f(1)^2.
-/
lemma f_f (s : ℕ+) : f (f s) = s * (f 1) ^ 2 := by
  simpa using hf s 1

/-
PROVIDED SOLUTION
Substitute s=1 in the functional equation: f(t^2 * f(1)) = 1 * f(t)^2 = f(t)^2.
-/
lemma f_sq_d (t : ℕ+) : f (t ^ 2 * f 1) = (f t) ^ 2 := by
  simpa using hf 1 t

/-
PROVIDED SOLUTION
From f_f: f(f(a)) = a * d^2 and f(f(b)) = b * d^2. If f(a) = f(b), then f(f(a)) = f(f(b)), so a * d^2 = b * d^2, hence a = b (by cancellation since d > 0).
-/
lemma f_inj : Function.Injective f := by
  intro s t; have := hf s 1; have := hf t 1; aesop;

/-
PROVIDED SOLUTION
Apply f_f to f(s): f(f(f(s))) = f(s) * d^2. But f(f(s)) = s * d^2, so f(s * d^2) = f(s) * d^2.
-/
lemma f_scale (s : ℕ+) : f (s * (f 1) ^ 2) = f s * (f 1) ^ 2 := by
  have := hf s 1; have := hf ( f 1 ) s; simp_all +decide [ ← mul_assoc, ← sq ] ;
  have := hf ( f s ) 1; simp_all +decide [ mul_comm, mul_left_comm ] ;

/-! ## Part 2: Key relation and multiplicativity -/

/-
PROVIDED SOLUTION
Substitute f(s) for s in the FE: f(t^2 * f(f(s))) = f(s) * f(t)^2. Using f_f: f(f(s)) = s * d^2, so f(t^2 * (s * d^2)) = f(s) * f(t)^2. Rewrite t^2 * (s * d^2) = (t^2 * s) * d^2. Using f_scale: f((t^2 * s) * d^2) = f(t^2 * s) * d^2. So f(t^2 * s) * d^2 = f(s) * f(t)^2.
-/
lemma f_key (s t : ℕ+) : f (t ^ 2 * s) * (f 1) ^ 2 = f s * (f t) ^ 2 := by
  -- From f_f: f(f(s)) = s * f(1)^2 and f(f(t)) = t * f(1)^2. If f(s) = f(t), then f(f(s)) = f(f(t)), so s * f(1)^2 = t * f(1)^2, hence s = t (by cancellation since f(1) > 0).
  have h_rel : ∀ s t, f (t^2 * (s * f 1 ^ 2)) = f s * f t ^ 2 := by
    simp_all +decide [ ← f_f ];
  rw [ ← h_rel, mul_comm ];
  simp_all +decide [ mul_assoc ]

/-
PROVIDED SOLUTION
Replace t by (f 1)*t in the FE: f(((f 1)*t)^2 * f(s)) = s * f((f 1)*t)^2. The LHS: ((f 1)*t)^2 * f(s) = (f 1)^2 * t^2 * f(s) = (t^2 * f(s)) * (f 1)^2. So f((t^2*f(s))*(f 1)^2) = s * f((f 1)*t)^2. Using f_scale: f(t^2*f(s)) * (f 1)^2 = s * f((f 1)*t)^2. Using the original FE: f(t^2*f(s)) = s*f(t)^2. So s*f(t)^2*(f 1)^2 = s*f((f 1)*t)^2. Cancel s: f(t)^2*(f 1)^2 = f((f 1)*t)^2, i.e., (f(t)*(f 1))^2 = f((f 1)*t)^2. Since everything is positive: f((f 1)*t) = (f 1)*f(t).
-/
lemma f_d_mul (t : ℕ+) : f (f 1 * t) = f 1 * f t := by
  have := hf 1 ( f 1 * t ) ; simp_all +decide [ mul_comm, mul_assoc, sq, mul_left_comm ] ;
  have := hf ( t * t * f 1 ) 1; simp_all +decide [ mul_assoc, mul_comm, mul_left_comm ] ;
  have := hf ( f t * f t ) 1; simp_all +decide [ mul_assoc, mul_comm, mul_left_comm ] ;
  exact PNat.eq ( by { have := congr_arg PNat.val this; nlinarith [ PNat.pos ( f ( t * f 1 ) ), PNat.pos ( f t * f 1 ) ] } )

/-
PROBLEM
f(t²) * d = f(t)² as natural numbers

PROVIDED SOLUTION
From f_sq_d: f(t^2 * (f 1)) = f(t)^2. From f_d_mul: f((f 1) * t^2) = (f 1) * f(t^2). Since t^2 * (f 1) = (f 1) * t^2 (commutativity), we get (f 1) * f(t^2) = f(t)^2. Casting to ℕ: (f(t^2) : ℕ) * (f 1 : ℕ) = (f t : ℕ)^2.
-/
lemma f_sq_nat (t : ℕ+) : (f (t ^ 2) : ℕ) * (f 1 : ℕ) = (f t : ℕ) ^ 2 := by
  -- From f_sq_d: f(t^2 * (f 1)) = f(t)^2. From f_d_mul: f((f 1) * t^2) = (f 1) * f(t^2). Since t^2 * (f 1) = (f 1) * t^2 (commutativity), we get (f 1) * f(t^2) = f(t)^2.
  have h_comm : f ((f 1) * t ^ 2) = (f 1) * f (t ^ 2) := by
    exact?;
  simp_all +decide [ mul_comm ];
  have := hf 1 t; simp_all +decide [ mul_comm ] ;
  exact congr_arg PNat.val this

/-
PROBLEM
d * f(a*b) = f(a) * f(b) as natural numbers

PROVIDED SOLUTION
From f_key: f(t^2 * s) * d^2 = f(s) * f(t)^2. From f_sq_nat: f(t^2) * d = f(t)^2, i.e., f(t)^2 = d * f(t^2). So f(t^2 * s) * d^2 = f(s) * d * f(t^2), giving f(t^2 * s) * d = f(s) * f(t^2). This shows d * f(a*b) = f(a) * f(b) when a is a perfect square.

Now set s = u^2, t = v: d * f(u^2 * v^2) = f(u^2) * f(v^2). But u^2 * v^2 = (u*v)^2, so d * f((u*v)^2) = f(u^2) * f(v^2).

Using f(x^2) * d = f(x)^2:
- d * f((uv)^2) = d * f(uv)^2 / d = f(uv)^2  (Wait, f((uv)^2) = f(uv)^2/d)
- f(u^2) = f(u)^2/d
- f(v^2) = f(v)^2/d

So d * f(uv)^2/d = f(u)^2/d * f(v)^2/d
f(uv)^2 = f(u)^2 * f(v)^2 / d^2
d^2 * f(uv)^2 = f(u)^2 * f(v)^2
(d * f(uv))^2 = (f(u) * f(v))^2
d * f(uv) = f(u) * f(v) (since all positive).

In ℕ, use the fact that if x^2 = y^2 and x,y > 0 then x = y. Work with casts to ℕ using PNat.val properties.
-/
lemma f_mult_nat (a b : ℕ+) : (f 1 : ℕ) * (f (a * b) : ℕ) = (f a : ℕ) * (f b : ℕ) := by
  -- From f_sq_nat: f(t^2 * (f 1)) = f(t)^2. From f_d_mul: f((f 1) * t^2) = (f 1) * f(t^2). Since t^2 * (f 1) = (f 1) * t^2 (commutativity), we get (f 1) * f(t^2) = f(t)^2.
  have f_d_mul_t : ∀ t, (f 1) * f (t ^ 2) = f t ^ 2 := by
    intro t; exact (by
    convert hf 1 t using 1 ; ring;
    · rw [ ← f_d_mul, mul_comm ];
      assumption;
    · norm_num);
  -- From f_key: f(t^2 * s) * d^2 = f(s) * f(t)^2. From f_sq_nat: f(t^2) * d = f(t)^2, i.e., f(t)^2 = d * f(t^2).
  have f_key_t : ∀ s t, f (t ^ 2 * s) * (f 1) ^ 2 = f s * f t ^ 2 := by
    exact?;
  have := f_d_mul_t ( a * b ) ; simp_all +decide [ mul_pow, mul_comm, mul_left_comm ] ;
  rw [ ← sq_eq_sq₀ ] <;> norm_cast <;> simp_all +decide [ mul_pow, mul_assoc, mul_comm, mul_left_comm ];
  grind

/-! ## Part 3: Divisibility - d divides f(n) -/

/-
PROVIDED SOLUTION
From f_mult_nat with a=b=n: (f 1) * f(n*n) = f(n) * f(n) = f(n)^2. Or directly from f_sq_nat: f(n^2) * (f 1) = f(n)^2, so (f 1) | f(n)^2.
-/
lemma d_dvd_f_sq (n : ℕ+) : (f 1 : ℕ) ∣ (f n : ℕ) ^ 2 := by
  -- From the functional equation, we have $f(n^2) * f(1) = (f(n))^2$.
  have h_fn2 : (f (n ^ 2) : ℕ) * (f 1 : ℕ) = (f n : ℕ) ^ 2 := by
    exact?;
  exact dvd_of_mul_left_eq _ h_fn2

/-
PROBLEM
f(p^k) * d^(k-1) = f(p)^k as natural numbers

PROVIDED SOLUTION
By induction on k (k ≥ 1). Base case k=1: f(p^1) * d^0 = f(p) * 1 = f(p) = f(p)^1. ✓. Inductive step: assume f(p^k) * d^(k-1) = f(p)^k. Need: f(p^(k+1)) * d^k = f(p)^(k+1). From f_mult_nat: d * f(p^k * p) = f(p^k) * f(p). So d * f(p^(k+1)) = f(p^k) * f(p). Thus f(p^(k+1)) = f(p^k) * f(p) / d. And f(p^(k+1)) * d^k = (f(p^k) * f(p) / d) * d^k = f(p^k) * f(p) * d^(k-1) = (f(p^k) * d^(k-1)) * f(p) = f(p)^k * f(p) = f(p)^(k+1). Use the induction hypothesis and f_mult_nat.
-/
lemma f_pow_nat (p : ℕ+) : ∀ k : ℕ, 0 < k →
    (f (p ^ k) : ℕ) * (f 1 : ℕ) ^ (k - 1) = (f p : ℕ) ^ k := by
  intro k hk;
  induction' hk with k hk ih <;> simp_all +decide [ Nat.pow_succ, mul_assoc ];
  -- From f_mult_nat: d * f(p^k * p) = f(p^k) * f(p).
  have h_step : (f 1 : ℕ) * (f (p ^ k * p) : ℕ) = (f (p ^ k) : ℕ) * (f p : ℕ) := by
    exact?;
  cases k <;> simp_all +decide [ pow_succ, mul_assoc, mul_comm, mul_left_comm ];
  simp +decide only [← mul_assoc, ← ih, ← h_step]

/-
PROVIDED SOLUTION
From f_pow_nat: for all k ≥ 1, f(n^k) * d^(k-1) = f(n)^k. So d^(k-1) | f(n)^k for all k ≥ 1.

Now we claim d | f(n). Suppose for contradiction that some prime q divides d but v_q(f(n)) < v_q(d), where v_q is the q-adic valuation. From d^(k-1) | f(n)^k: (k-1)*v_q(d) ≤ k*v_q(f(n)). Let e = v_q(d), r = v_q(f(n)) with r < e. Then (k-1)*e ≤ k*r for all k ≥ 1. But for k = e+1: e*e ≤ (e+1)*r < (e+1)*e, so e^2 < (e+1)*e = e^2+e. This gives e*(e - (e+1)*r/e) ≤ 0... hmm, let me simplify.

(k-1)*e ≤ k*r. Rearranging: k*(e-r) ≤ e. Since e-r ≥ 1 (as e > r): k ≤ e/(e-r) ≤ e. But this must hold for ALL k ≥ 1, including k = e+1. Contradiction!

Actually, a simpler approach: from d_dvd_f_sq, (f 1) | f(n)^2 for all n. If p is a prime factor of (f 1), then p | f(n) for all n (since p | f(n)^2 implies p | f(n)). Now, for higher prime powers: from f_pow_nat with k=2: f(n^2) * d = f(n)^2. So d | f(n)^2 and f(n^2) = f(n)^2/d. With k=3: f(n^3) * d^2 = f(n)^3. So d^2 | f(n)^3. If p^a exactly divides d and p^b exactly divides f(n), then 2a ≤ 3b from d^2 | f(n)^3. Also a ≤ 2b from d | f(n)^2. We want to show a ≤ b.

From (k-1)*a ≤ k*b for all k ≥ 1 (using f_pow_nat), taking k sufficiently large: b ≥ a*(k-1)/k → b ≥ a as k → ∞. Since a, b are integers, use k = a+1: a*a ≤ (a+1)*b, and if b < a then b ≤ a-1, so (a+1)*(a-1) = a²-1 ≥ a² gives contradiction... hmm not quite.

Let me use k=2: a ≤ 2b, so b ≥ a/2. And k=3: 2a ≤ 3b. If a is odd: a ≥ 1 and 2a ≤ 3b means b ≥ 2a/3. With a=1: b ≥ 1. Done. With a=3: b ≥ 2. And k=2: b ≥ 2. And k=4: 3*3 ≤ 4b → b ≥ 3. Done. With a=5: k=2: b≥3, k=3: b≥4, k=5: 4*5≤5b→b≥4, k=6: 5*5≤6b→b≥5. Done.

In general, taking k = a: (a-1)*a ≤ a*b, so b ≥ a-1. Then taking k=a+1: a*a ≤ (a+1)*b. If b = a-1: a² ≤ (a+1)(a-1) = a²-1, contradiction. So b ≥ a.

So the argument is: from f_pow_nat, d^(k-1) | f(n)^k for all k ≥ 1. For any prime power p^a dividing d: (k-1)*a ≤ k*v_p(f(n)) for all k. Taking k=a: (a-1)*a ≤ a*v_p(f(n)), so v_p(f(n)) ≥ a-1. Taking k=a+1: a*a ≤ (a+1)*v_p(f(n)). If v_p(f(n)) = a-1: a² ≤ (a+1)(a-1) = a²-1, contradiction. So v_p(f(n)) ≥ a.

Therefore d | f(n).

In Lean, use Nat.dvd_of_mul_dvd_mul_right or work with prime factorizations. Or more directly, use the characterization via emultiplicity/factorization. Or just use a simple argument.
-/
lemma d_dvd_f (n : ℕ+) : (f 1 : ℕ) ∣ (f n : ℕ) := by
  -- By induction on $k$, we show that for any prime $p$, $v_p(f(n)) \geq v_p(f(1))$.
  have h_induction : ∀ p : ℕ, Nat.Prime p → (Nat.factorization (f n)) p ≥ (Nat.factorization (f 1)) p := by
    -- From f_pow_nat, we know that for any prime $p$, $(f 1)^{k-1} \mid f(n)^k$ for all $k \geq 1$.
    have h_div : ∀ p : ℕ, Nat.Prime p → ∀ k : ℕ, 0 < k → (Nat.factorization (f 1)) p * (k - 1) ≤ (Nat.factorization (f n)) p * k := by
      -- From f_pow_nat, we know that for any prime $p$, $(f 1)^{k-1} \mid f(n)^k$ for all $k \geq 1$. This follows from the fact that $f(n^k) * (f 1)^{k-1} = f(n)^k$.
      intros p hp k hk
      have h_div_eq : (f (n ^ k) : ℕ) * (f 1 : ℕ) ^ (k - 1) = (f n : ℕ) ^ k := by
        exact?;
      apply_fun fun x => x.factorization p at h_div_eq ; simp_all +decide [ Nat.factorization_mul, hp.ne_zero ];
      linarith [ Nat.zero_le ( Nat.factorization ( f ( n ^ k ) ) p ) ];
    contrapose! h_div;
    obtain ⟨ p, hp₁, hp₂ ⟩ := h_div; exact ⟨ p, hp₁, ( Nat.factorization ( f 1 ) p ) + 1, Nat.succ_pos _, by norm_num; nlinarith ⟩ ;
  exact Nat.factorization_le_iff_dvd ( by positivity ) ( by positivity ) |>.1 fun p => by by_cases hp : Nat.Prime p <;> aesop;

/-! ## Part 4: The function g = f/d and its properties -/

noncomputable def gN (f : ℕ+ → ℕ+) (n : ℕ+) : ℕ := (f n : ℕ) / (f 1 : ℕ)

/-
PROVIDED SOLUTION
g(n) = f(n)/d where d = f(1). Since d | f(n) (by d_dvd_f), g(n) = f(n)/d ≥ 1 (since f(n) ≥ d, because f(n) = d*k for some k ≥ 1 — k ≥ 1 since f(n) ≥ 1 and d ≥ 1, and d | f(n) means f(n) = d*k with k ≥ 0, but f(n) ≥ 1 forces k ≥ 1). Use Nat.div_pos with Nat.le_of_dvd.
-/
lemma gN_pos (n : ℕ+) : 0 < gN f n := by
  exact Nat.div_pos ( Nat.le_of_dvd ( PNat.pos _ ) ( d_dvd_f ( f := f ) ( hf := hf ) _ ) ) ( PNat.pos _ )

/-
PROVIDED SOLUTION
f(n) = d * g(n) where g(n) = f(n)/d. Since d | f(n) (by d_dvd_f), Nat.div_mul_cancel gives d * (f(n)/d) = f(n), i.e., f(n) = d * g(n). Use Nat.eq_mul_of_div_eq_right or Nat.div_mul_cancel.
-/
lemma f_eq_d_mul_gN (n : ℕ+) : (f n : ℕ) = (f 1 : ℕ) * gN f n := by
  unfold gN;
  rw [ Nat.mul_div_cancel' ];
  exact?

/-
PROVIDED SOLUTION
From f_mult_nat: d * f(a*b) = f(a) * f(b). And f(n) = d * g(n) (from f_eq_d_mul_gN). So d * (d * g(a*b)) = (d * g(a)) * (d * g(b)) = d^2 * g(a) * g(b). Thus d^2 * g(a*b) = d^2 * g(a) * g(b), so g(a*b) = g(a) * g(b) by cancellation (d > 0).
-/
lemma gN_mult (a b : ℕ+) : gN f (a * b) = gN f a * gN f b := by
  -- Substitute f(n) = d * g(n) into the multiplicativity equation d * f(a*b) = f(a) * f(b).
  have h_subst : (f 1 : ℕ) * (f 1 * gN f (a * b)) = (f 1 * gN f a) * (f 1 * gN f b) := by
    rw [ ← f_eq_d_mul_gN, ← f_eq_d_mul_gN, ← f_eq_d_mul_gN ];
    · exact?;
    · assumption;
    · assumption;
    · assumption;
  nlinarith [ PNat.pos ( f 1 ), mul_pos ( PNat.pos ( f 1 ) ) ( PNat.pos ( f 1 ) ) ]

/-
PROVIDED SOLUTION
g(1) = f(1)/d = d/d = 1. Use Nat.div_self (PNat.pos (f 1)).
-/
lemma gN_one : gN f 1 = 1 := by
  exact Nat.div_self ( PNat.pos _ )

/-
PROBLEM
g(g(n)) = n : requires applying f to g(n), which is a PNat

PROVIDED SOLUTION
We need g(g(n)) = n where g(n) = f(n)/d.

From f(f(n)) = n * d^2 (f_f) and f(n) = d * g(n) (f_eq_d_mul_gN):
f(d * g(n)) = n * d^2.
Using f_d_mul: f(d * g(n)) = d * f(g(n)).
So d * f(g(n)) = n * d^2.
Cancel d: f(g(n)) = n * d.

Here g(n) is a positive integer (by gN_pos), so ⟨g(n), gN_pos⟩ is a PNat.
Then g(g(n)) = f(g(n))/d = (n*d)/d = n.

In Lean, g(n) is gN f n. We need gN f ⟨gN f n, gN_pos hf n⟩ = n.
This equals f(⟨gN f n, _⟩)/d.
f(⟨gN f n, _⟩) = f of g(n) as PNat.
We showed f(g(n)) = n * d (as ℕ).
So gN f ⟨gN f n, _⟩ = (n * d) / d = n (by Nat.mul_div_cancel using PNat.pos).
-/
lemma gN_involution (n : ℕ+) :
    gN f ⟨gN f n, gN_pos hf n⟩ = (n : ℕ) := by
  -- From f_f: f(f(n)) = n * f(1)^2 and f(n) = f(1) * gN f n.
  have h_ffn : f (f n) = n * (f 1 : ℕ) ^ 2 := by
    simpa using congr_arg PNat.val ( hf n 1 )
  have h_fn : f n = (f 1 : ℕ) * gN f n := by
    exact?;
  -- From f_d_mul: f(d * g(n)) = d * f(g(n)).
  have h_f_d_mul : f (f 1 * ⟨gN f n, gN_pos hf n⟩) = (f 1 : ℕ) * f ⟨gN f n, gN_pos hf n⟩ := by
    convert congr_arg PNat.val ( f_d_mul hf _ ) using 1;
  -- Substitute h_fn into h_ffn to get f(d * g(n)) = n * d^2.
  have h_sub : f (f 1 * ⟨gN f n, gN_pos hf n⟩) = n * (f 1 : ℕ) ^ 2 := by
    convert h_ffn using 1;
    exact congr_arg PNat.val ( congr_arg f ( PNat.eq <| by simpa [ mul_comm ] using h_fn.symm ) );
  exact Nat.div_eq_of_eq_mul_left ( PNat.pos _ ) ( by nlinarith [ PNat.pos ( f 1 ) ] )

/-! ## Part 5: g maps primes to primes -/

/-
PROVIDED SOLUTION
g is injective because: if g(a) = g(b) as ℕ, then ⟨g(a), _⟩ = ⟨g(b), _⟩ as PNat, so g(g(a)) = g(g(b)), hence a = b (using gN_involution). More directly: from f_eq_d_mul_gN, f(a) = d*g(a) and f(b) = d*g(b). If g(a) = g(b), then f(a) = f(b) in ℕ, hence a = b by f_inj (since the ℕ coercion is injective).
-/
lemma gN_inj : Function.Injective (fun n : ℕ+ => gN f n) := by
  intro a b h_eq
  have h_f_eq : f a = f b := by
    exact PNat.eq ( by nlinarith! [ f_eq_d_mul_gN hf a, f_eq_d_mul_gN hf b, PNat.pos ( f 1 ) ] )
  exact (by
  have := hf a 1; have := hf b 1; aesop;)

/-
PROVIDED SOLUTION
We need to show that if p is prime then g(p) is prime, where g is completely multiplicative with g(g(n)) = n.

Since p ≥ 2 (prime), g(p) ≥ 1 (gN_pos). And g(p) ≠ 1: if g(p) = 1, then using gN_involution with n = p gives g(g(p)) = p, but g(g(p)) = g(1) = 1 (by gN_one) ≠ p ≥ 2, contradiction.

So g(p) ≥ 2. Suppose g(p) is not prime. Then g(p) = a * b for some a, b ≥ 2 (with a*b = g(p)).

By gN_mult (multiplicativity): g(a*b) = g(a)*g(b). And g(a*b) = g(g(p)). By gN_involution: g(g(p)) = p. So g(a)*g(b) = p.

Since p is prime, one of g(a), g(b) equals 1. Say g(a) = 1. Then by gN_involution: g(g(a)) = a, i.e., g(1) = a. But g(1) = 1 (gN_one), so a = 1, contradicting a ≥ 2.

Note: here a and b are natural numbers ≥ 2. We need to be careful: gN_involution and gN_mult are stated for PNat arguments. Since a, b ≥ 2 > 0, they can be viewed as PNat. And gN_mult requires PNat arguments, so we use ⟨a, _⟩ and ⟨b, _⟩.

The key difficulty is converting between ℕ and ℕ+ in the argument.
-/
lemma gN_prime (p : ℕ+) (hp : Nat.Prime (p : ℕ)) : Nat.Prime (gN f p) := by
  -- By definition of $g$, we know that $g(p) = f(p) / f(1)$.
  set gp := gN f p with hgp
  have hgp_pos : 1 ≤ gp := by
    exact gN_pos hf p
  have hgp_ne_one : gp ≠ 1 := by
    by_contra hgp_eq_one
    have h_contra : p = f 1 := by
      have h_contra : f p = f 1 := by
        exact PNat.eq ( by nlinarith! [ Nat.div_mul_cancel ( show ( f 1 : ℕ ) ∣ ( f p : ℕ ) from d_dvd_f hf p ) ] : ( f p : ℕ ) = f 1 );
      have := hf p 1; have := hf 1 1; aesop;
    have h_contra' : f 1 = 1 := by
      have := hf 1 1; simp_all +decide [ sq ] ;
      rw [ eq_comm, gN ] at hgp ; aesop;
    have h_contra'' : p = 1 := by
      rw [h_contra, h_contra']
    have h_contra''' : Nat.Prime 1 := by
      simpa [ h_contra'' ] using hp
    norm_num at h_contra'''
  have hgp_prime : Nat.Prime gp := by
    -- Suppose $gp = a * b$ for some $a, b \geq 2$.
    by_contra h_contra
    obtain ⟨a, b, ha, hb, hab⟩ : ∃ a b : ℕ, 2 ≤ a ∧ 2 ≤ b ∧ gp = a * b := by
      rcases Nat.exists_dvd_of_not_prime2 ( lt_of_le_of_ne hgp_pos hgp_ne_one.symm ) h_contra with ⟨ a, ha₁, ha₂ ⟩ ; exact ⟨ a, gp / a, by nlinarith [ Nat.div_mul_cancel ha₁ ], by nlinarith [ Nat.div_mul_cancel ha₁ ], by rw [ Nat.mul_div_cancel' ha₁ ] ⟩ ;
    -- By multiplicativity of $g$, we have $g(a) * g(b) = g(a * b) = g(gp) = p$.
    have h_mul : gN f ⟨a, by linarith⟩ * gN f ⟨b, by linarith⟩ = p := by
      have h_mul : gN f (⟨a, by linarith⟩ * ⟨b, by linarith⟩) = p := by
        convert gN_involution hf p using 1;
        exact congr_arg _ ( PNat.eq <| by aesop );
      rw [ ← h_mul, gN_mult ];
      assumption;
    -- Since $p$ is prime, one of $g(a)$ or $g(b)$ must be $1$.
    have h_one : gN f ⟨a, by linarith⟩ = 1 ∨ gN f ⟨b, by linarith⟩ = 1 := by
      have := hp.isUnit_or_isUnit h_mul.symm; aesop;
    cases h_one <;> have := gN_involution hf ⟨ a, by linarith ⟩ <;> have := gN_involution hf ⟨ b, by linarith ⟩ <;> simp_all +decide [ Nat.Prime.ne_one ] ;
    · linarith [ show gN f 1 = 1 from gN_one hf ];
    · linarith [ show gN f 1 = 1 from gN_one hf ]
  exact hgp_prime

/-! ## Part 6: Computing f(1998) -/

/-
PROVIDED SOLUTION
1998 = 2 * 999 = 2 * 3^3 * 37. Use decide or norm_num.
-/
omit hf in
lemma factorization_1998 : (1998 : ℕ+) = 2 * 3 ^ 3 * 37 := by
  rfl

/-
PROVIDED SOLUTION
From f_eq_d_mul_gN: f(n) = d * g(n) as ℕ. And g is multiplicative (gN_mult). So f(1998) = d * g(1998) = d * g(2 * 3^3 * 37) = d * g(2) * g(3^3) * g(37) = d * g(2) * g(3)^3 * g(37).

In detail: use factorization_1998 to rewrite 1998 = 2 * 3^3 * 37. Then apply f_eq_d_mul_gN to get f(1998) = d * gN f 1998. Then use gN_mult repeatedly to decompose gN f 1998.

For g(3^3) = g(3)^3: g(3^3) = g(3*3*3) = g(3)*g(3*3) = g(3)*g(3)*g(3) = g(3)^3. Or note that 3^3 = 3*9, 9 = 3*3, and apply gN_mult twice.
-/
lemma f_1998_eq : (f 1998 : ℕ) = (f 1 : ℕ) * gN f 2 * (gN f 3) ^ 3 * gN f 37 := by
  -- Using the multiplicativity of gN, we can write gN 1998 as gN 2 * gN 3^3 * gN 37.
  have h_gN_1998 : gN f 1998 = gN f 2 * gN f 3 ^ 3 * gN f 37 := by
    rw [ show ( 1998 : ℕ+ ) = 2 * 3 ^ 3 * 37 by decide, gN_mult ];
    · rw [ gN_mult ];
      · rw [ show ( 3 ^ 3 : ℕ+ ) = 3 * 3 * 3 by decide, gN_mult, gN_mult ] ; ring;
        · assumption;
        · assumption;
      · assumption;
    · assumption;
  have := f_eq_d_mul_gN hf 1998; ( have := f_eq_d_mul_gN hf 2; ( have := f_eq_d_mul_gN hf 3; ( have := f_eq_d_mul_gN hf 37; simp_all +decide [ mul_assoc ] ; ) ) )

/-! ## Part 7: The combinatorial bound -/

end Setup

/-
PROVIDED SOLUTION
We need: for distinct primes p, q, r: p * q^3 * r ≥ 120.

The primes are at least 2. Since they're distinct, WLOG they're at least {2, 3, 5} in some order.

Case 1: q = 2. Then q^3 = 8. p and r are distinct primes ≥ 3 (since ≠ 2 and ≠ each other). The minimum of p*r for distinct primes p,r ≥ 3 is 3*5 = 15. So p*q^3*r ≥ 15*8 = 120.

More precisely: p ≥ 2 and r ≥ 2, p ≠ 2 and r ≠ 2 (since they're different from q=2), so p ≥ 3 and r ≥ 3. And p ≠ r, so one of them ≥ 5. So p*r ≥ 3*5 = 15. Thus p*8*r ≥ 120.

Case 2: q ≥ 3. Then q^3 ≥ 27. p ≥ 2, r ≥ 2, and they're distinct, so max(p,r) ≥ 3. Thus p*r ≥ 2*3 = 6. So p*q^3*r ≥ 27*6 = 162 ≥ 120.

To formalize: since p, q, r are primes, they're ≥ 2. Case split on q = 2 vs q ≥ 3.

In the q = 2 case: p ≥ 3 (prime, ≠ 2), r ≥ 3 (prime, ≠ 2), and p ≠ r, so WLOG p < r, p ≥ 3, r ≥ 5 (next prime after 3, or just r ≥ 4 since r is prime and r ≠ p ≥ 3, so r ≥ 5). Actually r could be 3 if p ≥ 5. So min of p*r is 3*5 = 15.

Use interval_cases or omega after establishing the bounds. For primes ≥ 3: the prime is odd and ≥ 3. Two distinct primes ≥ 3: the smaller is ≥ 3 and the larger is ≥ 5 (since 4 is not prime). So product ≥ 15.

This is a finite case analysis. Use Nat.Prime to get ≥ 2, then handle q = 2 and q ≥ 3 separately.
-/
lemma three_distinct_primes_bound (p q r : ℕ)
    (hp : Nat.Prime p) (hq : Nat.Prime q) (hr : Nat.Prime r)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) :
    120 ≤ p * q ^ 3 * r := by
  rcases p with ( _ | _ | _ | p ) <;> rcases q with ( _ | _ | _ | q ) <;> rcases r with ( _ | _ | _ | r ) <;> simp_all +arith +decide [ Nat.pow_succ', mul_assoc ];
  · grind;
  · rcases p with ( _ | _ | p ) <;> rcases r with ( _ | _ | r ) <;> (norm_num at * <;> nlinarith;);
  · grind +ring;
  · grind +ring

/-! ## Main theorem -/

/-
PROVIDED SOLUTION
From f_1998_eq: f(1998) = d * g(2) * g(3)^3 * g(37).

From gN_prime: g(2), g(3), g(37) are primes (since 2, 3, 37 are prime).

From gN_inj: g is injective on PNat, so g(2), g(3), g(37) are distinct (since 2, 3, 37 are distinct PNat values).

From three_distinct_primes_bound: g(2) * g(3)^3 * g(37) ≥ 120.

Since d = f(1) ≥ 1 (PNat): f(1998) = d * g(2) * g(3)^3 * g(37) ≥ 1 * 120 = 120.
-/
theorem lower_bound_1998
    (f : ℕ+ → ℕ+)
    (h : ∀ s t, f (t ^ 2 * f s) = s * (f t) ^ 2) :
    120 ≤ (f 1998 : ℕ) := by
  -- Using the factorization and properties of $g$, we get $f(1998) = d * g(2) * g(3)^3 * g(37)$ as natural numbers.
  have h_f_1998 : (f 1998 : ℕ) = (f 1 : ℕ) * (gN f 2) * (gN f 3)^3 * (gN f 37) := by
    exact?;
  -- From the properties of $g$, we know that $g(2)$, $g(3)$, and $g(37)$ are distinct primes.
  have h_distinct_primes : Nat.Prime (gN f 2) ∧ Nat.Prime (gN f 3) ∧ Nat.Prime (gN f 37) ∧ gN f 2 ≠ gN f 3 ∧ gN f 2 ≠ gN f 37 ∧ gN f 3 ≠ gN f 37 := by
    have h_distinct_primes : Nat.Prime (gN f 2) ∧ Nat.Prime (gN f 3) ∧ Nat.Prime (gN f 37) := by
      have h_g_prime : ∀ p : ℕ+, Nat.Prime (p : ℕ) → Nat.Prime (gN f p) := by
        exact?
      exact ⟨h_g_prime 2 (by decide), h_g_prime 3 (by decide), h_g_prime 37 (by decide)⟩;
    have h_distinct : gN f 2 ≠ gN f 3 ∧ gN f 2 ≠ gN f 37 ∧ gN f 3 ≠ gN f 37 := by
      have h_distinct : Function.Injective (fun n : ℕ+ => gN f n) := by
        exact?;
      exact ⟨ h_distinct.ne <| by decide, h_distinct.ne <| by decide, h_distinct.ne <| by decide ⟩
    exact ⟨h_distinct_primes.left, h_distinct_primes.right.left, h_distinct_primes.right.right, h_distinct.left, h_distinct.right.left, h_distinct.right.right⟩;
  -- Applying the bound from three_distinct_primes_bound, we get $g(2) * g(3)^3 * g(37) \geq 120$.
  have h_bound : (gN f 2) * (gN f 3)^3 * (gN f 37) ≥ 120 := by
    apply three_distinct_primes_bound; exact h_distinct_primes.left; exact h_distinct_primes.right.left; exact h_distinct_primes.right.right.left; exact h_distinct_primes.right.right.right.left; exact h_distinct_primes.right.right.right.right.left; exact h_distinct_primes.right.right.right.right.right;
  nlinarith [ PNat.pos ( f 1 ) ]

end Imo1998P6