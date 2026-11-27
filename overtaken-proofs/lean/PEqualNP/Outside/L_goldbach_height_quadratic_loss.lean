import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

private lemma abs_sin_le_abs_aux (z : ℝ) : |Real.sin z| ≤ |z| := by
  by_cases h : |z| ≤ 1
  · have hb := Real.sin_bound h
    have ha : 0 ≤ |z| := abs_nonneg z
    have h3 : |z|^5 ≤ |z|^3 := pow_le_pow_of_le_one ha h (by norm_num)
    have hz : |z|^3 = |z^3| := (abs_pow z 3).symm
    rw [abs_le] at hb ⊢
    rcases le_total 0 z with hz0 | hz0
    · rw [abs_of_nonneg hz0] at h3 hb ⊢
      have : 0 ≤ z^3 := by positivity
      constructor <;> nlinarith [hb.1, hb.2]
    · rw [abs_of_nonpos hz0] at h3 hb ⊢
      have : z^3 ≤ 0 := by nlinarith [sq_nonneg z]
      have h5 : (-z)^3 = -z^3 := by ring
      constructor <;> nlinarith [hb.1, hb.2]
  · have := Real.abs_sin_le_one z
    linarith [not_le.mp h]

theorem PEqualNP.Outside.L_goldbach_height_quadratic_loss :
    ∀ a b x : ℝ, 1-Real.cos ((a-b)*x) ≤ (a-b)^2*x^2/2 := by
  intro a b x
  set y := (a-b)*x with hy
  have h1 : Real.cos y = 1 - 2 * Real.sin (y/2) ^ 2 := by
    have h2 := Real.sin_sq_add_cos_sq (y/2)
    have h3 := Real.cos_two_mul (y/2)
    rw [show 2 * (y/2) = y by ring] at h3
    nlinarith
  have h4 : Real.sin (y/2) ^ 2 ≤ (y/2)^2 := by
    have := abs_sin_le_abs_aux (y/2)
    exact sq_le_sq.mpr (by simpa using this)
  have : (a-b)^2*x^2 = y^2 := by rw [hy]; ring
  rw [this, h1]
  nlinarith
