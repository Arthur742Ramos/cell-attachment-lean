module

public import Lean4.fraction

@[expose] public section


namespace FractionEqualities

lemma one_sub_inverse_of_add_one {n : ℝ} (hn : n + 1 ≠ 0) :
    1 - 1 / (n + 1) = n / (n + 1) := by
  field_simp [hn]
  ring

lemma frac_cancel {a b c : ℝ} (hb : b ≠ 0) : (a / b) * (b / c) = a / c := by
  by_cases hc : c = 0
  · simp [hc]
  · field_simp [hb, hc]

lemma frac_cancel' {a b c : ℝ} (hb : b ≠ 0) : (b / a) * (c / b) = c / a := by
  rw [mul_comm]
  exact frac_cancel hb

lemma one_sub_frac {a b : ℝ} (hb : b + 1 ≠ 0) : (1 - (a + 1)/(b+1)) = (b - a) / (b + 1) := by
  field_simp [hb]
  ring

lemma frac_special {a b c : ℝ} (hbc : b ≠ c) (hc : c + 1 ≠ 0) :
    (a + (b + 1)) / (c + 1) = (1 - (b + 1) / (c + 1)) * (a / (c - b)) + (b + 1) / (c + 1) := by
  rw [one_sub_frac hc, frac_cancel']
  · exact (div_add_div_same _ _ _).symm
  · exact sub_ne_zero_of_ne hbc.symm

/--
  For any `i n : ℕ` with `i > 0` and `i ≤ (n + 1) * i`, we have that `1 / (n + 1) = i / ((n + 1) * i)`.
-/
lemma cancel_common_factor {i n : ℕ} (i_pos : 0 < i) (hi_n : (i - 1).succ ≤ ((n+1) * i - 1).succ) :
    Fraction.ofPos (Nat.succ_pos n) = Fraction (Nat.succ_pos _) hi_n := by
  apply Subtype.ext
  simp only [Fraction.ofPos_coe, Fraction.Fraction_coe]
  have hi : (i : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt i_pos)
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hi_succ : (i - 1).succ = i := Nat.succ_pred_eq_of_pos i_pos
  have hn_succ : ((n + 1) * i - 1).succ = (n + 1) * i :=
    Nat.succ_pred_eq_of_pos (mul_pos (Nat.succ_pos n) i_pos)
  simp only [hi_succ, hn_succ, Nat.cast_succ, Nat.cast_mul]
  field_simp [hi, ne_of_gt hn]
  ring

end FractionEqualities
