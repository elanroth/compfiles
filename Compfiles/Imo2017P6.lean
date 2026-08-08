/-
Copyright (c) 2023 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.NumberTheory] }

/-!
# International Mathematical Olympiad 2017, Problem 6

A point (x,y) ∈ ℤ × ℤ is called primitive if gcd(x,y) = 1.
Let S be a finite set of primitive points.
Prove that there exists n > 0 and integers a₀,a₁,...,aₙ
such that

  a₀xⁿ + a₁xⁿ⁻¹y + a₂xⁿ⁻²y² + ... + aₙ₋₁xyⁿ⁻¹ + aₙyⁿ = 1

for each (x,y) ∈ S.

-/

/-
### Outline of the solution

A binary form `a₀ xⁿ + a₁ xⁿ⁻¹ y + ⋯ + aₙ yⁿ` is encoded by the one-variable polynomial with
coefficients `aᵢ`; `ev n P x y` denotes its value at `(x,y)`.

A form of even degree takes the same value at `p` and at `-p`, so it suffices to construct a form
of even degree taking the value `1` on a set `T` of pairwise non-parallel primitive points which
contains one point of each pair `{p, -p}` with `p ∈ S` (`main_construction`).

For `T = {p₁, …, p_k}` put `Mᵢ(x,y) = ∏_{j ≠ i} (xⱼ y - yⱼ x)`; it vanishes at `pⱼ` for `j ≠ i`
and `dᵢ = Mᵢ(pᵢ) ≠ 0`. Let `D = ∏ᵢ |dᵢ|` and `e = D * φ(D)`. The trinomial form
`x ^ (2e) - x ^ e y ^ e + y ^ (2e)` is congruent to `1` modulo `D` at every primitive point:
modulo a prime power `q ^ a ∣ D` each of `x ^ e`, `y ^ e` is `0` or `1`, and not both are `0`
(`key_congr`). Raising it to a power `s` large enough gives a form `f₀` of even degree `n ≥ k - 1`
with `f₀(pᵢ) ≡ 1 (mod D)`. Since `dᵢ ∣ D`, the corrected form

  `f = f₀ + ∑ᵢ cᵢ Lᵢ ^ (n - k + 1) Mᵢ`,  where `cᵢ = (1 - f₀(pᵢ)) / dᵢ`

and `Lᵢ` is a linear form with `Lᵢ(pᵢ) = 1` (Bézout), takes the value `1` at every `pᵢ`.
-/

namespace Imo2017P6

open Polynomial Finset

/-- `ev n P x y` is the value at `(x,y)` of the binary form of degree `n` whose coefficients
are the coefficients of the one-variable polynomial `P`. -/
noncomputable def ev (n : ℕ) (P : ℤ[X]) (x y : ℤ) : ℤ :=
  ∑ i ∈ Finset.range (n + 1), P.coeff i * x ^ i * y ^ (n - i)

theorem ev_add (n : ℕ) (P Q : ℤ[X]) (x y : ℤ) :
    ev n (P + Q) x y = ev n P x y + ev n Q x y := by
  simp [ev, Finset.sum_add_distrib, add_mul]

theorem ev_sub (n : ℕ) (P Q : ℤ[X]) (x y : ℤ) :
    ev n (P - Q) x y = ev n P x y - ev n Q x y := by
  simp [ev, Finset.sum_sub_distrib, sub_mul]

theorem ev_C_mul (n : ℕ) (c : ℤ) (P : ℤ[X]) (x y : ℤ) :
    ev n (C c * P) x y = c * ev n P x y := by
  simp [ev, Finset.mul_sum, mul_assoc]

theorem ev_sum {ι : Type*} (s : Finset ι) (f : ι → ℤ[X]) (n : ℕ) (x y : ℤ) :
    ev n (∑ i ∈ s, f i) x y = ∑ i ∈ s, ev n (f i) x y := by
  classical
  induction s using Finset.induction with
  | empty => simp [ev]
  | insert a s ha ih => rw [Finset.sum_insert ha, ev_add, ih, Finset.sum_insert ha]

theorem ev_X_pow (n k : ℕ) (hk : k ≤ n) (x y : ℤ) :
    ev n (X ^ k) x y = x ^ k * y ^ (n - k) := by
  rw [ev, Finset.sum_eq_single k]
  · simp
  · intro b _ hb
    simp [coeff_X_pow, hb]
  · intro h
    simp only [Finset.mem_range, not_lt] at h
    omega

theorem ev_one (x y : ℤ) : ev 0 1 x y = 1 := by simp [ev]

theorem ev_mul (m n : ℕ) (P Q : ℤ[X]) (hP : P.natDegree ≤ m) (hQ : Q.natDegree ≤ n) (x y : ℤ) :
    ev (m + n) (P * Q) x y = ev m P x y * ev n Q x y := by
  classical
  set F : ℕ × ℕ → ℤ := fun ab => (P.coeff ab.1 * x ^ ab.1 * y ^ (m - ab.1)) *
    (Q.coeff ab.2 * x ^ ab.2 * y ^ (n - ab.2)) with hF
  have hzero : ∀ ab : ℕ × ℕ, ¬ (ab.1 ≤ m ∧ ab.2 ≤ n) → F ab = 0 := by
    intro ab h
    rcases not_and_or.mp h with h | h
    · have : P.coeff ab.1 = 0 := P.coeff_eq_zero_of_natDegree_lt (by omega)
      simp [hF, this]
    · have : Q.coeff ab.2 = 0 := Q.coeff_eq_zero_of_natDegree_lt (by omega)
      simp [hF, this]
  have hL : ev (m + n) (P * Q) x y
      = ∑ s ∈ Finset.range (m + n + 1), ∑ ab ∈ Finset.antidiagonal s, F ab := by
    rw [ev]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [Polynomial.coeff_mul, Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun ab hab => ?_
    simp only [Finset.mem_antidiagonal] at hab
    by_cases h : ab.1 ≤ m ∧ ab.2 ≤ n
    · have h2 : m + n - (ab.1 + ab.2) = (m - ab.1) + (n - ab.2) := by omega
      simp only [hF, ← hab]
      rw [h2, pow_add]
      ring
    · rw [hzero ab h]
      rcases not_and_or.mp h with h | h
      · have : P.coeff ab.1 = 0 := P.coeff_eq_zero_of_natDegree_lt (by omega)
        simp [this]
      · have : Q.coeff ab.2 = 0 := Q.coeff_eq_zero_of_natDegree_lt (by omega)
        simp [this]
  rw [hL, ev, ev, Finset.sum_mul_sum, ← Finset.sum_product', ← Finset.sum_biUnion]
  · refine (Finset.sum_subset ?_ ?_).symm
    · intro ab hab
      simp only [Finset.mem_product, Finset.mem_range] at hab
      simp only [Finset.mem_biUnion, Finset.mem_range, Finset.mem_antidiagonal]
      exact ⟨ab.1 + ab.2, by omega, rfl⟩
    · intro ab _ hab
      refine hzero ab ?_
      intro h
      exact hab (by simp only [Finset.mem_product, Finset.mem_range]; omega)
  · intro a _ b _ hab
    simp only [Function.onFun, Finset.disjoint_left, Finset.mem_antidiagonal]
    intro p hp hp2
    exact hab (hp ▸ hp2 ▸ rfl)

theorem ev_pow (k m : ℕ) (P : ℤ[X]) (hP : P.natDegree ≤ m) (x y : ℤ) :
    ev (k * m) (P ^ k) x y = (ev m P x y) ^ k := by
  induction k with
  | zero => simpa using ev_one x y
  | succ k ih =>
      rw [show P ^ (k + 1) = P ^ k * P by ring, show (k + 1) * m = k * m + m by ring,
        ev_mul _ _ _ _ ((Polynomial.natDegree_pow_le).trans
          (by simpa using Nat.mul_le_mul_left k hP)) hP, ih, pow_succ]

theorem ev_neg (n : ℕ) (P : ℤ[X]) (x y : ℤ) :
    ev n P (-x) (-y) = (-1) ^ n * ev n P x y := by
  rw [ev, ev, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  simp only [Finset.mem_range] at hi
  have h : ((-1 : ℤ)) ^ i * (-1) ^ (n - i) = (-1) ^ n := by
    rw [← pow_add]; congr 1; omega
  rw [neg_pow, neg_pow, ← h]
  ring

theorem natDegree_prod_le_card {ι : Type*} (s : Finset ι) (f : ι → ℤ[X])
    (h : ∀ i ∈ s, (f i).natDegree ≤ 1) : (∏ i ∈ s, f i).natDegree ≤ s.card :=
  (Polynomial.natDegree_prod_le s f).trans (by simpa using Finset.sum_le_sum h)

theorem ev_prod {ι : Type*} (s : Finset ι) (f : ι → ℤ[X])
    (h : ∀ i ∈ s, (f i).natDegree ≤ 1) (x y : ℤ) :
    ev s.card (∏ i ∈ s, f i) x y = ∏ i ∈ s, ev 1 (f i) x y := by
  classical
  induction s using Finset.induction with
  | empty => simpa using ev_one x y
  | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.card_insert_of_notMem ha, Finset.prod_insert ha,
        show s.card + 1 = 1 + s.card by ring,
        ev_mul _ _ _ _ (h a (Finset.mem_insert_self a s))
          (natDegree_prod_le_card s f fun i hi => h i (Finset.mem_insert_of_mem hi)),
        ih fun i hi => h i (Finset.mem_insert_of_mem hi)]

/-- The linear form `u * x + v * y`. -/
noncomputable def lin (u v : ℤ) : ℤ[X] := C u * X + C v

theorem lin_natDegree (u v : ℤ) : (lin u v).natDegree ≤ 1 :=
  le_trans (Polynomial.natDegree_add_le _ _) (by
    simp only [max_le_iff]
    exact ⟨le_trans (Polynomial.natDegree_C_mul_le _ _) (by simp), by simp⟩)

theorem ev_lin (u v x y : ℤ) : ev 1 (lin u v) x y = u * x + v * y := by
  simp only [lin, ev, Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, coeff_add,
    coeff_C_mul, coeff_X_one, coeff_X_zero, coeff_C, mul_one, mul_zero, zero_add]
  norm_num
  ring

theorem ev_lin_pow (m : ℕ) (u v x y : ℤ) : ev m (lin u v ^ m) x y = (u * x + v * y) ^ m := by
  have := ev_pow m 1 (lin u v) (lin_natDegree u v) x y
  rwa [mul_one, ev_lin] at this

/-! ### The auxiliary form which is `1` modulo `M` at every primitive point -/

theorem int_pow_totient_sub_one (n : ℕ) (t : ℤ) (h : IsCoprime t (n : ℤ)) :
    (n : ℤ) ∣ t ^ n.totient - 1 := by
  obtain ⟨u, hu⟩ := (ZMod.coe_int_isUnit_iff_isCoprime t n).mpr h.symm
  have : ((t ^ n.totient - 1 : ℤ) : ZMod n) = 0 := by
    push_cast
    rw [← hu, ← Units.val_pow_eq_pow_val, ZMod.pow_totient u, Units.val_one, sub_self]
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp this

theorem pow_dvd_or (q a e : ℕ) (hq : q.Prime) (hphi : Nat.totient (q ^ a) ∣ e) (hae : a ≤ e)
    (t : ℤ) : ((q : ℤ) ^ a ∣ t ^ e) ∨ ((q : ℤ) ^ a ∣ t ^ e - 1) := by
  by_cases hdvd : (q : ℤ) ∣ t
  · exact Or.inl (dvd_trans (pow_dvd_pow_of_dvd hdvd a) (pow_dvd_pow t hae))
  · right
    have hcop : IsCoprime t ((q ^ a : ℕ) : ℤ) := by
      have h1 : IsCoprime ((q : ℤ)) t :=
        (Nat.prime_iff_prime_int.mp hq).coprime_iff_not_dvd.mpr hdvd
      push_cast
      exact (h1.symm).pow_right
    obtain ⟨s, hs⟩ := hphi
    have h2 := int_pow_totient_sub_one (q ^ a) t hcop
    have h3 : t ^ e - 1 = (t ^ (q ^ a).totient) ^ s - 1 ^ s := by
      rw [← pow_mul, ← hs]; ring
    rw [h3]
    push_cast at h2 ⊢
    exact dvd_trans h2 (sub_dvd_pow_sub_pow _ _ s)

theorem key_congr (M e : ℕ)
    (hcond : ∀ q a : ℕ, q.Prime → q ^ a ∣ M → Nat.totient (q ^ a) ∣ e ∧ a ≤ e)
    (x y : ℤ) (h : IsCoprime x y) :
    (M : ℤ) ∣ x ^ (2 * e) - x ^ e * y ^ e + y ^ (2 * e) - 1 := by
  set z : ℤ := x ^ (2 * e) - x ^ e * y ^ e + y ^ (2 * e) - 1 with hz
  rw [Int.natCast_dvd, Nat.dvd_iff_prime_pow_dvd_dvd]
  intro q k hq hqk
  rw [← Int.natCast_dvd]
  push_cast
  obtain ⟨hphi, hke⟩ := hcond q k hq hqk
  have hu := pow_dvd_or q k e hq hphi hke x
  have hv := pow_dvd_or q k e hq hphi hke y
  have hzz : z = (x ^ e) ^ 2 - x ^ e * y ^ e + (y ^ e) ^ 2 - 1 := by
    rw [hz, ← pow_mul, ← pow_mul, mul_comm e 2]
  rw [hzz]
  rcases hu with ⟨c, hc⟩ | ⟨c, hc⟩ <;> rcases hv with ⟨d, hd⟩ | ⟨d, hd⟩
  · rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp
    · exfalso
      have hx : (q : ℤ) ∣ x ^ e := hc ▸ Dvd.dvd.mul_right (dvd_pow_self _ (by omega)) c
      have hy : (q : ℤ) ∣ y ^ e := hd ▸ Dvd.dvd.mul_right (dvd_pow_self _ (by omega)) d
      have hqx : (q : ℤ) ∣ x := (Nat.prime_iff_prime_int.mp hq).dvd_of_dvd_pow hx
      have hqy : (q : ℤ) ∣ y := (Nat.prime_iff_prime_int.mp hq).dvd_of_dvd_pow hy
      exact (Nat.prime_iff_prime_int.mp hq).not_unit (h.isUnit_of_dvd' hqx hqy)
  · have hd' : y ^ e = (q : ℤ) ^ k * d + 1 := by linarith
    exact ⟨(q : ℤ) ^ k * c ^ 2 - c - (q : ℤ) ^ k * c * d + 2 * d + (q : ℤ) ^ k * d ^ 2, by
      rw [hc, hd']; ring⟩
  · have hc' : x ^ e = (q : ℤ) ^ k * c + 1 := by linarith
    exact ⟨(q : ℤ) ^ k * d ^ 2 - d - (q : ℤ) ^ k * c * d + 2 * c + (q : ℤ) ^ k * c ^ 2, by
      rw [hc', hd]; ring⟩
  · have hc' : x ^ e = (q : ℤ) ^ k * c + 1 := by linarith
    have hd' : y ^ e = (q : ℤ) ^ k * d + 1 := by linarith
    exact ⟨c + d + (q : ℤ) ^ k * (c ^ 2 - c * d + d ^ 2), by rw [hc', hd']; ring⟩

/-- The trinomial form `x ^ (2e) - x ^ e y ^ e + y ^ (2e)`. -/
noncomputable def tri (e : ℕ) : ℤ[X] := X ^ (2 * e) - X ^ e + 1

theorem tri_natDegree (e : ℕ) : (tri e).natDegree ≤ 2 * e := by
  refine le_trans (Polynomial.natDegree_add_le _ _) ?_
  simp only [max_le_iff]
  refine ⟨le_trans (Polynomial.natDegree_sub_le _ _) ?_, by simp⟩
  simp only [max_le_iff, Polynomial.natDegree_X_pow]
  omega

theorem ev_tri (e : ℕ) (he : 0 < e) (x y : ℤ) :
    ev (2 * e) (tri e) x y = x ^ (2 * e) - x ^ e * y ^ e + y ^ (2 * e) := by
  rw [tri, ev_add, ev_sub, ev_X_pow _ _ le_rfl, ev_X_pow _ _ (by omega),
    show (1 : ℤ[X]) = X ^ 0 by simp, ev_X_pow _ _ (by omega)]
  simp [show 2 * e - e = e by omega]

/-- For any positive `M` there is a positive `e` such that the form `tri e` takes values
congruent to `1` modulo `M` at every primitive point. -/
theorem exists_tri (M : ℕ) (hM : 0 < M) :
    ∃ e : ℕ, 0 < e ∧ ∀ x y : ℤ, IsCoprime x y → (M : ℤ) ∣ ev (2 * e) (tri e) x y - 1 := by
  refine ⟨M * Nat.totient M, Nat.mul_pos hM (Nat.totient_pos.mpr hM), fun x y hxy => ?_⟩
  rw [ev_tri _ (Nat.mul_pos hM (Nat.totient_pos.mpr hM))]
  refine key_congr M _ (fun q a hq hqa => ⟨?_, ?_⟩) x y hxy
  · exact Dvd.dvd.mul_left (Nat.totient_dvd_of_dvd hqa) M
  · have h1 : q ^ a ≤ M := Nat.le_of_dvd hM hqa
    have h2 : 2 ^ a ≤ q ^ a := Nat.pow_le_pow_left hq.two_le a
    have h3 : a < 2 ^ a := Nat.lt_two_pow_self
    have h4 : 1 ≤ Nat.totient M := Nat.totient_pos.mpr hM
    calc a ≤ M := by omega
    _ ≤ M * Nat.totient M := Nat.le_mul_of_pos_right M h4

/-! ### The main construction -/

theorem main_construction (T : Finset (ℤ × ℤ)) (hcop : ∀ p ∈ T, IsCoprime p.1 p.2)
    (hindep : ∀ p ∈ T, ∀ r ∈ T, p ≠ r → p.1 * r.2 - p.2 * r.1 ≠ 0) :
    ∃ n : ℕ, 0 < n ∧ Even n ∧ ∃ P : ℤ[X], ∀ p ∈ T, ev n P p.1 p.2 = 1 := by
  classical
  set k := T.card
  set Mf : ℤ × ℤ → ℤ[X] := fun p => ∏ j ∈ T.erase p, lin (-j.2) j.1 with hMf
  set dd : ℤ × ℤ → ℤ := fun p => ∏ j ∈ T.erase p, (-j.2 * p.1 + j.1 * p.2)
  have hddne : ∀ p ∈ T, dd p ≠ 0 := by
    intro p hp
    refine Finset.prod_ne_zero_iff.mpr fun j hj hc => ?_
    exact hindep j (Finset.mem_of_mem_erase hj) p hp (Finset.ne_of_mem_erase hj) (by linarith)
  set D : ℕ := ∏ p ∈ T, (dd p).natAbs
  have hDpos : 0 < D := Finset.prod_pos fun p hp => Int.natAbs_pos.mpr (hddne p hp)
  obtain ⟨e, hepos, hcongr⟩ := exists_tri D hDpos
  set s := k + 1
  set N := s * (2 * e) with hN
  have hNpos : 0 < N := Nat.mul_pos (by omega) (by omega)
  have hkN : k - 1 ≤ N := by
    calc k - 1 ≤ s := by omega
    _ ≤ N := Nat.le_mul_of_pos_right _ (by omega)
  set m := N - (k - 1)
  have hmN : m + (k - 1) = N := by omega
  set u : ℤ × ℤ → ℤ := fun p => Int.gcdA p.1 p.2 with hu
  set v : ℤ × ℤ → ℤ := fun p => Int.gcdB p.1 p.2 with hv
  have hbez : ∀ p ∈ T, u p * p.1 + v p * p.2 = 1 := by
    intro p hp
    have h1 : Int.gcd p.1 p.2 = 1 := Int.isCoprime_iff_gcd_eq_one.mp (hcop p hp)
    have h2 := Int.gcd_eq_gcd_ab p.1 p.2
    rw [h1] at h2
    push_cast at h2
    rw [hu, hv]
    linarith
  set g : ℤ × ℤ → ℤ := fun p => ev N (tri e ^ s) p.1 p.2 with hg
  have hgD : ∀ p ∈ T, (D : ℤ) ∣ g p - 1 := by
    intro p hp
    have h1 : g p = (ev (2 * e) (tri e) p.1 p.2) ^ s :=
      ev_pow s (2 * e) (tri e) (tri_natDegree e) p.1 p.2
    rw [h1]
    exact dvd_trans (hcongr p.1 p.2 (hcop p hp))
      (by simpa using sub_dvd_pow_sub_pow (ev (2 * e) (tri e) p.1 p.2) 1 s)
  have hddD : ∀ p ∈ T, dd p ∣ (D : ℤ) := fun p hp =>
    dvd_trans (Int.dvd_natAbs.mpr dvd_rfl)
      (Int.natCast_dvd_natCast.mpr (Finset.dvd_prod_of_mem _ hp))
  set cc : ℤ × ℤ → ℤ := fun p => (1 - g p) / dd p
  have hccd : ∀ p ∈ T, cc p * dd p = 1 - g p := fun p hp =>
    Int.ediv_mul_cancel (dvd_trans (hddD p hp) (dvd_sub_comm.mp (hgD p hp)))
  refine ⟨N, hNpos, ⟨s * e, by rw [hN]; ring⟩,
    tri e ^ s + ∑ p ∈ T, C (cc p) * (lin (u p) (v p) ^ m * Mf p), ?_⟩
  intro r hr
  have hterm : ∀ p ∈ T, ev N (C (cc p) * (lin (u p) (v p) ^ m * Mf p)) r.1 r.2
      = cc p * ((u p * r.1 + v p * r.2) ^ m * ∏ j ∈ T.erase p, (-j.2 * r.1 + j.1 * r.2)) := by
    intro p hp
    have hdegL : (lin (u p) (v p) ^ m).natDegree ≤ m := by
      refine le_trans Polynomial.natDegree_pow_le ?_
      simpa using Nat.mul_le_mul_left m (lin_natDegree (u p) (v p))
    have hcard : (T.erase p).card = k - 1 := Finset.card_erase_of_mem hp
    have hdegM : (Mf p).natDegree ≤ k - 1 := by
      rw [← hcard]
      exact natDegree_prod_le_card _ _ fun j _ => lin_natDegree _ _
    rw [ev_C_mul, ← hmN, ev_mul m (k - 1) _ _ hdegL hdegM, ev_lin_pow]
    congr 1
    rw [← hcard, hMf, ev_prod _ _ fun j _ => lin_natDegree _ _]
    congr 1
    exact Finset.prod_congr rfl fun (j : ℤ × ℤ) _ => ev_lin (-j.2) j.1 r.1 r.2
  rw [ev_add, ev_sum, Finset.sum_congr rfl hterm, Finset.sum_eq_single r]
  · have hd1 : (∏ j ∈ T.erase r, (-j.2 * r.1 + j.1 * r.2)) = dd r := rfl
    rw [hbez r hr, one_pow, one_mul, hd1, hccd r hr]
    simp only [hg]
    ring
  · intro p _ hpr
    rw [Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨Ne.symm hpr, hr⟩) (by ring)]
    ring
  · intro h
    exact absurd hr h

/-- Two primitive points with vanishing determinant are equal up to sign. -/
theorem parallel_primitive {a b c d : ℤ} (h1 : IsCoprime a b) (h2 : IsCoprime c d)
    (h : a * d - b * c = 0) : (c = a ∧ d = b) ∨ (c = -a ∧ d = -b) := by
  have key : a * d = b * c := by linarith
  have hac : a ∣ c := h1.dvd_of_dvd_mul_left ⟨d, key.symm⟩
  have hca : c ∣ a := h2.dvd_of_dvd_mul_left ⟨b, by linarith⟩
  rcases Int.associated_iff.mp (associated_of_dvd_dvd hac hca) with rfl | hne
  · rcases mul_eq_zero.mp (show a * (d - b) = 0 by linarith) with rfl | hdb
    · have hb := Int.isUnit_iff.mp (isCoprime_zero_left.mp h1)
      have hd := Int.isUnit_iff.mp (isCoprime_zero_left.mp h2)
      rcases hb with rfl | rfl <;> rcases hd with rfl | rfl <;> simp
    · exact Or.inl ⟨rfl, by linarith⟩
  · subst hne
    rcases mul_eq_zero.mp (show c * (d + b) = 0 by linarith) with rfl | hdb
    · rw [neg_zero] at h1 ⊢
      have hb := Int.isUnit_iff.mp (isCoprime_zero_left.mp h1)
      have hd := Int.isUnit_iff.mp (isCoprime_zero_left.mp h2)
      rcases hb with rfl | rfl <;> rcases hd with rfl | rfl <;> simp
    · exact Or.inr ⟨by ring, by linarith⟩

problem imo2017_p6 (S : Finset (ℤ × ℤ)) (hS : ∀ s ∈ S, gcd s.1 s.2 = 1) :
    ∃ n : ℕ, 0 < n ∧ ∃ a : ℕ → ℤ,
      ∀ s ∈ S, ∑ i ∈ Finset.range (n + 1), a i * s.1 ^ i * s.2 ^ (n - i) = 1 := by
  classical
  have hcop : ∀ s ∈ S, IsCoprime s.1 s.2 := fun s hs =>
    (gcd_isUnit_iff _ _).mp (hS s hs ▸ isUnit_one)
  -- `T` picks one point out of each pair `{p, -p}`
  set T : Finset (ℤ × ℤ) :=
    S.filter (fun p => (0 < p.1 ∨ (p.1 = 0 ∧ 0 < p.2)) ∨ -p ∉ S)
  have hTS : T ⊆ S := Finset.filter_subset _ _
  have hdich : ∀ s ∈ S, s ∈ T ∨ -s ∈ T := by
    intro s hs
    by_cases hpos : 0 < s.1 ∨ (s.1 = 0 ∧ 0 < s.2)
    · exact Or.inl (Finset.mem_filter.mpr ⟨hs, Or.inl hpos⟩)
    by_cases hns : -s ∈ S
    · refine Or.inr (Finset.mem_filter.mpr ⟨hns, Or.inl ?_⟩)
      have hne : s.1 ≠ 0 ∨ s.2 ≠ 0 := by
        by_contra hc
        push_neg at hc
        exact not_isCoprime_zero_zero (hc.1 ▸ hc.2 ▸ hcop s hs)
      simp only [Prod.fst_neg, Prod.snd_neg]
      omega
    · exact Or.inl (Finset.mem_filter.mpr ⟨hs, Or.inr hns⟩)
  have hindep : ∀ p ∈ T, ∀ r ∈ T, p ≠ r → p.1 * r.2 - p.2 * r.1 ≠ 0 := by
    intro p hp r hr hpr hzero
    have hpS := hTS hp
    have hrS := hTS hr
    rcases parallel_primitive (hcop p hpS) (hcop r hrS) hzero with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact hpr (Prod.ext h1.symm h2.symm)
    · have hrp : r = -p := Prod.ext (by simpa using h1) (by simpa using h2)
      have hp' := (Finset.mem_filter.mp hp).2
      have hr' := (Finset.mem_filter.mp hr).2
      rw [hrp] at hrS
      have hpp : -(-p) = p := neg_neg p
      rw [hrp, hpp] at hr'
      simp only [hpS, not_true_eq_false, or_false, Prod.fst_neg, Prod.snd_neg] at hr'
      simp only [hrS, not_true_eq_false, or_false] at hp'
      omega
  obtain ⟨n, hn, hne, P, hP⟩ := main_construction T (fun p hp => hcop p (hTS hp)) hindep
  refine ⟨n, hn, fun i => P.coeff i, fun s hs => ?_⟩
  have hev : ∀ x y : ℤ, ev n P x y = ∑ i ∈ Finset.range (n + 1),
      P.coeff i * x ^ i * y ^ (n - i) := fun _ _ => rfl
  rw [← hev]
  rcases hdich s hs with h | h
  · exact hP s h
  · have h2 : ev n P (-s.1) (-s.2) = 1 := by simpa using hP _ h
    rw [ev_neg n P s.1 s.2, hne.neg_one_pow, one_mul] at h2
    exact h2

end Imo2017P6
