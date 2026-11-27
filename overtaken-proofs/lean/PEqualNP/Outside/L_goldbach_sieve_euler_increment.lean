import Mathlib.Tactic.Ring
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

theorem PEqualNP.Outside.L_goldbach_sieve_euler_increment :
    ∀ p : ℕ, p.Prime → 2<p → (((1+1/((p:ℝ)-2))^2-1)/(p:ℝ)) ≤ 9/(p:ℝ)^2 := by
  intro p hp h2
  have h3 : (3 : ℝ) ≤ p := by exact_mod_cast h2
  have hq : (0 : ℝ) < (p : ℝ) - 2 := by linarith
  have hp : (0 : ℝ) < p := by linarith
  have e : ((1 + 1 / ((p : ℝ) - 2)) ^ 2 - 1) / (p : ℝ) = (2 * ((p : ℝ) - 2) + 1) / (((p : ℝ) - 2) ^ 2 * p) := by
    field_simp
    ring
  rw [e, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_nonneg (sub_nonneg.2 h3) (by linarith : (0 : ℝ) ≤ 7 * (p : ℝ) - 12), pow_pos hp 2, mul_pos hp hq]
