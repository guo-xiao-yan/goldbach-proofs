import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

theorem PEqualNP.Outside.L_goldbach_conductor_high_edge :
    ∀ n d : ℕ, (n^3 < d^4 ↔ (n : ℝ)^((3:ℝ)/4) < (d : ℝ)) := by
  intro n d
  have hx : 0 ≤ (n : ℝ)^((3:ℝ)/4) := Real.rpow_nonneg (Nat.cast_nonneg n) _
  have h4 : ((n : ℝ)^((3:ℝ)/4))^4 = (n : ℝ)^3 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg n)]
    norm_num
  have hd : (0:ℝ) ≤ d := Nat.cast_nonneg d
  have hc : n^3 < d^4 ↔ (n : ℝ)^3 < (d : ℝ)^4 := by
    constructor
    · intro h; exact_mod_cast h
    · intro h; exact_mod_cast h
  rw [hc, ← h4]
  constructor
  · intro h
    exact lt_of_pow_lt_pow_left₀ 4 hd h
  · intro h
    exact pow_lt_pow_left₀ h hx (by norm_num)
