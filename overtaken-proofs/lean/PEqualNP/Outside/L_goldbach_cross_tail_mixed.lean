import Mathlib.Analysis.Complex.Basic

theorem PEqualNP.Outside.L_goldbach_cross_tail_mixed :
    ∀ (a b : ℂ), ‖a+b‖^2 - ‖a‖^2 - ‖b‖^2 = 2*(a*star b).re := by
  intro a b
  rw [Complex.sq_norm, Complex.sq_norm, Complex.sq_norm, Complex.normSq_add, Complex.star_def]
  ring
