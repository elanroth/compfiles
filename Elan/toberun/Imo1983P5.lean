/-
IMO 1983 P5 — All sorries for Aristotle

Construction: f(n) = reinterpret base-2 digits of n in base 3.
Witness: S = f({1,...,1983}).

Proof of no-AP property:
  If f(i) + f(k) = 2·f(j), since f(j) has only 0s/1s in base 3,
  2·f(j) has only 0s/2s. Digit-by-digit forces f(i) = f(k), contradicting f(i) < f(k).
-/

import Mathlib.Tactic
import Mathlib.Data.Nat.Digits

def f (n : ℕ) : ℕ := Nat.ofDigits 3 (Nat.digits 2 n)

lemma digits_two_bound (n : ℕ) : ∀ d ∈ Nat.digits 2 n, d ≤ 1 := by
  intro d hd
  have := Nat.digits_lt (b := 2) (by norm_num) hd
  omega

/-- The base-3 canonical digits of f(n) equal the base-2 digits of n.
    Apply Nat.digits_ofDigits: digits 2 n are all < 3 and have no trailing zero. -/
lemma f_digits_eq (n : ℕ) : Nat.digits 3 (f n) = Nat.digits 2 n := by
  sorry

/-- f is injective. Follows from f_digits_eq + Nat.ofDigits_digits. -/
lemma f_injective : Function.Injective f := by
  intro a b hab
  have hdig : Nat.digits 2 a = Nat.digits 2 b := by
    have : Nat.digits 3 (f a) = Nat.digits 3 (f b) := congr_arg _ hab
    rwa [f_digits_eq, f_digits_eq] at this
  have ha := Nat.ofDigits_digits 2 a
  have hb := Nat.ofDigits_digits 2 b
  rw [hdig] at ha; linarith [hb.symm.trans ha]

/-- f is monotone: a ≤ b → f a ≤ f b.
    Proof: larger n has larger binary digit sequence (lex order) →
    larger base-3 value. -/
lemma f_mono : Monotone f := by
  sorry

/-- f(1983) ≤ 10^5. (1983 = 11110111111₂, f(1983) = 11110111111₃ = 88573.) -/
lemma f_1983_le : f 1983 ≤ 10 ^ 5 := by
  native_decide

/-- Core no-AP lemma: if all digits of a, b, c are in {0,1} and
    ofDigits 3 a + ofDigits 3 c = 2 * ofDigits 3 b, then ofDigits 3 a = ofDigits 3 c.
    Proof by induction on the lists: mod-3 at each step forces a₀ = c₀, no carry, recurse. -/
lemma ofDigits_no_ap (a b c : List ℕ)
    (ha : ∀ x ∈ a, x ≤ 1) (hb : ∀ x ∈ b, x ≤ 1) (hc : ∀ x ∈ c, x ≤ 1)
    (h : Nat.ofDigits 3 a + Nat.ofDigits 3 c = 2 * Nat.ofDigits 3 b) :
    Nat.ofDigits 3 a = Nat.ofDigits 3 c := by
  sorry

theorem imo1983_p5 :
    ∃ S : Finset ℕ, S.card = 1983 ∧
    (∀ x ∈ S, x ≤ 10^5) ∧
    ∀ x ∈ S, ∀ y ∈ S, ∀ z ∈ S, x < y ∧ y < z → x + z ≠ 2 * y := by
  refine ⟨Finset.image f (Finset.Icc 1 1983), ?_, ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ f_injective]; simp
  · intro x hx
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hx
    exact le_trans (f_mono (Finset.mem_Icc.mp hn).2) f_1983_le
  · intro x hx y hy z hz ⟨hxy, hyz⟩
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hz
    intro hadd
    have heq : f i = f k :=
      ofDigits_no_ap (Nat.digits 2 i) (Nat.digits 2 j) (Nat.digits 2 k)
        (digits_two_bound i) (digits_two_bound j) (digits_two_bound k) hadd
    exact absurd heq (ne_of_lt (lt_trans hxy hyz))
