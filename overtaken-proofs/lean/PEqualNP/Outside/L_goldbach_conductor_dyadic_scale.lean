import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Positivity

theorem PEqualNP.Outside.L_goldbach_conductor_dyadic_scale :
    ∀ (c ε : ℝ), 0<c → 0<ε → ∀ k : ℕ, 4*c*Real.log 2/ε < (2:ℝ)^k → |4*c*Real.log 2/(2:ℝ)^k|<ε := by
  intro c ε hc hε k h
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hp : (0:ℝ) < (2:ℝ)^k := by positivity
  rw [abs_of_pos (by positivity), div_lt_iff₀ hp]
  rw [div_lt_iff₀ hε] at h
  linarith
