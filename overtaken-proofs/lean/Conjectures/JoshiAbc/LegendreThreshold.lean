import Mathlib

theorem Conjectures.JoshiAbc.LegendreThreshold :
    ∀ l Q : ℝ, 7 ≤ l → (l*(l+1)/12-1)*Q ≤ (l+5)/4*Real.log Real.pi → 2*l*Q ≤ 126/11*Real.log Real.pi := by
  intro l Q hl h
  have hL : 0 < Real.log Real.pi := Real.log_pos (by linarith [Real.pi_gt_three])
  set L := Real.log Real.pi with hLdef
  have hc : 0 < l*(l+1)/12-1 := by nlinarith
  by_contra hcon
  push_neg at hcon
  have hQ : 0 < Q := by
    by_contra hq
    push_neg at hq
    nlinarith
  have key : 2*l*Q*(l*(l+1)/12-1) ≤ 2*l*((l+5)/4*L) := by
    have := mul_le_mul_of_nonneg_left h (by linarith : (0:ℝ) ≤ 2*l)
    nlinarith
  have key2 : 126/11*L*(l*(l+1)/12-1) < 2*l*Q*(l*(l+1)/12-1) :=
    mul_lt_mul_of_pos_right hcon hc
  have poly : 0 ≤ (60*l^2-204*l-1512) := by nlinarith
  nlinarith [mul_nonneg hL.le poly]
