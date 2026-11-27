import Mathlib

theorem Conjectures.JoshiAbc.FixedPlaceStress :
    ∀ N : ℕ, let x := (N:ℝ); let lo := -(3*x+3)*Real.log 337; let hi := (-4*(3*x+15/7)+3*(6/7)+1)*Real.log 337; lo-hi=(9*x+2)*Real.log 337 ∧ hi<lo := by
  intro N x lo hi
  have hx : 0 ≤ x := Nat.cast_nonneg N
  have hlog : 0 < Real.log 337 := Real.log_pos (by norm_num)
  have e : lo - hi = (9*x+2)*Real.log 337 := by
    simp only [lo, hi]; ring
  refine ⟨e, ?_⟩
  have : 0 < lo - hi := by rw [e]; positivity
  linarith
