import Mathlib.Analysis.Complex.Trigonometric

private theorem abs_sin_nonneg_aux (y : ℝ) (h0 : 0 ≤ y) : |Real.sin y| ≤ y := by
  by_cases h1 : y ≤ 1
  · have hb := Real.sin_bound (x := y) (by rw [abs_of_nonneg h0]; exact h1)
    rw [abs_of_nonneg h0] at hb
    have h3 : y ^ 5 ≤ y ^ 3 := by
      have : y ^ 5 = y ^ 3 * y ^ 2 := by ring
      rw [this]
      have h2 : y ^ 2 ≤ 1 := by nlinarith
      have : 0 ≤ y ^ 3 := by positivity
      nlinarith
    have h4 := abs_sub_le_iff.1 hb
    have h5 : 0 ≤ y ^ 3 := by positivity
    have h6 : y ^ 3 ≤ y := by nlinarith [sq_nonneg y]
    have h7 : 0 ≤ Real.sin y := by linarith [h4.2]
    rw [abs_of_nonneg h7]
    linarith [h4.1]
  · have := Real.abs_sin_le_one y
    linarith

private theorem abs_sin_le_abs_aux (y : ℝ) : |Real.sin y| ≤ |y| := by
  rcases le_total 0 y with h | h
  · rw [abs_of_nonneg h]
    exact abs_sin_nonneg_aux y h
  · rw [abs_of_nonpos h]
    have := abs_sin_nonneg_aux (-y) (by linarith)
    rwa [Real.sin_neg, abs_neg] at this

theorem PEqualNP.Outside.L_goldbach_height_near_phase :
    ∀ a b x : ℝ, ‖Complex.exp ((((a-b)*x : ℝ) : ℂ)*Complex.I)-1‖ ≤ |a-b| * |x| := by
  intro a b x
  rw [mul_comm, Complex.norm_exp_I_mul_ofReal_sub_one, Real.norm_eq_abs, abs_mul]
  have h := abs_sin_le_abs_aux ((a - b) * x / 2)
  rw [abs_div, abs_mul] at h
  have h2 : |(2 : ℝ)| = 2 := abs_of_pos (by norm_num)
  rw [h2] at h ⊢
  linarith
