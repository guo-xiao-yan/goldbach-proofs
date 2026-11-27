import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Linarith

private theorem mixed_aux (a b : ℂ) : ‖a+b‖^2 - ‖a‖^2 - ‖b‖^2 = 2*(a*star b).re := by
  rw [Complex.sq_norm, Complex.sq_norm, Complex.sq_norm, Complex.normSq_add, Complex.star_def]
  ring

theorem PEqualNP.Outside.L_goldbach_cross_tail_error :
    ∀ a b : ℂ, |‖a+b‖^2-‖a‖^2| ≤ 2*‖a‖*‖b‖+‖b‖^2 := by
  intro a b
  have h := mixed_aux a b
  have h1 : |(a * star b).re| ≤ ‖a‖ * ‖b‖ := by
    refine (Complex.abs_re_le_norm _).trans ?_
    rw [norm_mul, norm_star]
  rw [abs_le] at h1 ⊢
  constructor <;> nlinarith [h1.1, h1.2, sq_nonneg ‖b‖]
