/-
Copyright (c) 2024 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InternLM-MATH LEAN Formalizer v0.1
-/

import Mathlib.Tactic
import Mathlib.Data.Nat.Digits

import ProblemExtraction

problem_file { tags := [.Combinatorics] }

/-!
# International Mathematical Olympiad 1983, Problem 5

Is it possible to choose $1983$ distinct positive integers,
all less than or equal to $10^5$,
no three of which are consecutive terms of an arithmetic progression?
Justify your answer.
-/

namespace Imo1983P5

snip begin

/-!
## Construction

Define `f : ℕ → ℕ` by: take the base-2 digits of `n` and reinterpret them
in base 3. For example, 6 = 110₂, so f(6) = 110₃ = 12.

The set S = f({1, ..., 1983}) satisfies all three conditions.

**Key facts:**
1. f is injective (distinct binary representations → distinct base-3 values).
2. f(n) ≤ f(1983) ≤ 10^5 for n ≤ 1983 (monotone + computable bound).
3. No three values f(i) < f(j) < f(k) can satisfy f(i) + f(k) = 2·f(j):
   since f(j) has only 0s and 1s in base 3, 2·f(j) has only 0s and 2s.
   Digit-by-digit this forces f(i) = f(k), contradicting f(i) < f(k).
-/

/-- Reinterpret base-2 digits of n as a base-3 number. -/
def f (n : ℕ) : ℕ := Nat.ofDigits 3 (Nat.digits 2 n)

/-- Base-2 digits are all 0 or 1 (< 2 < 3). -/
lemma digits_two_bound (n : ℕ) : ∀ d ∈ Nat.digits 2 n, d ≤ 1 := by
  intro d hd
  have := Nat.digits_lt (b := 2) (by norm_num) hd
  omega

/-- The base-3 canonical digits of f(n) equal the base-2 digits of n.
    Proof: `Nat.digits_ofDigits` applies because digits 2 n are all < 3
    and have no trailing zero (canonical base-2 representation). -/
lemma f_digits_eq (n : ℕ) : Nat.digits 3 (f n) = Nat.digits 2 n := by
  sorry

/-- f is injective: equal base-3 values imply equal base-2 digit lists, hence equal n. -/
lemma f_injective : Function.Injective f := by
  intro a b hab
  have hdig : Nat.digits 2 a = Nat.digits 2 b := by
    have : Nat.digits 3 (f a) = Nat.digits 3 (f b) := congr_arg _ hab
    rwa [f_digits_eq, f_digits_eq] at this
  have ha := Nat.ofDigits_digits 2 a
  have hb := Nat.ofDigits_digits 2 b
  rw [hdig] at ha
  linarith [hb.symm.trans ha]

/-- f is monotone: a ≤ b → f a ≤ f b.
    Proof: larger n has a "larger" binary digit list under lexicographic comparison,
    which maps to a larger base-3 value. -/
lemma f_mono : Monotone f := by
  sorry

/-- Computable bound: f(1983) ≤ 10^5.
    (1983 = 11110111111₂, so f(1983) = 11110111111₃ = 88573 < 100000.) -/
lemma f_1983_le : f 1983 ≤ 10 ^ 5 := by
  native_decide

/-!
### Core no-AP lemma

If `a`, `b`, `c` are lists of digits in {0, 1} and
  `ofDigits 3 a + ofDigits 3 c = 2 * ofDigits 3 b`,
then `ofDigits 3 a = ofDigits 3 c`.

**Proof by induction on the lists:**
- Base: 0 + 0 = 0 = 2 * 0. ✓
- Step: the equation mod 3 gives `a₀ + c₀ ≡ 2 * b₀ (mod 3)`.
  Since a₀, c₀, b₀ ∈ {0, 1}:
  - b₀ = 0 → a₀ + c₀ ≡ 0 (mod 3) → a₀ = c₀ = 0 (no carry).
  - b₀ = 1 → a₀ + c₀ ≡ 2 (mod 3) → a₀ = c₀ = 1 (no carry).
  In both cases a₀ = c₀ with no carry, so recurse on the tails.
-/
lemma ofDigits_no_ap (a b c : List ℕ)
    (ha : ∀ x ∈ a, x ≤ 1) (hb : ∀ x ∈ b, x ≤ 1) (hc : ∀ x ∈ c, x ≤ 1)
    (h : Nat.ofDigits 3 a + Nat.ofDigits 3 c = 2 * Nat.ofDigits 3 b) :
    Nat.ofDigits 3 a = Nat.ofDigits 3 c := by
  sorry

snip end

problem imo1983_p5 :
  ∃ S : Finset ℕ, S.card = 1983 ∧
  (∀ x ∈ S, x ≤ 10^5) ∧
  ∀ x ∈ S, ∀ y ∈ S, ∀ z ∈ S, x < y ∧ y < z → x + z ≠ 2 * y := by
  -- The witness is S = f({1, ..., 1983})
  refine ⟨Finset.image f (Finset.Icc 1 1983), ?_, ?_, ?_⟩
  · -- |S| = 1983: injectivity of f on {1,...,1983}
    rw [Finset.card_image_of_injective _ f_injective]
    simp
  · -- All elements ≤ 10^5: monotonicity + f(1983) ≤ 10^5
    intro x hx
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hx
    exact le_trans (f_mono (Finset.mem_Icc.mp hn).2) f_1983_le
  · -- No three elements in AP: the ofDigits_no_ap digit argument
    intro x hx y hy z hz ⟨hxy, hyz⟩
    obtain ⟨i, _hi, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨j, _hj, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨k, _hk, rfl⟩ := Finset.mem_image.mp hz
    intro hadd
    have heq : f i = f k :=
      ofDigits_no_ap (Nat.digits 2 i) (Nat.digits 2 j) (Nat.digits 2 k)
        (digits_two_bound i) (digits_two_bound j) (digits_two_bound k) hadd
    exact absurd heq (ne_of_lt (lt_trans hxy hyz))

end Imo1983P5
