import Mathlib

theorem Conjectures.JoshiAbc.FreyHeight :
    let h := fun (a b : ℕ) => Real.log ((a:ℝ)+b); ∀ a b : ℕ, 0 < a → 0 < b → 2*h a b + Real.log 12 ≤ Real.log (16*((a:ℝ)^2+a*b+(b:ℝ)^2)) := by
  intro h a b ha hb
  have ha' : (0:ℝ) < a := by exact_mod_cast ha
  have hb' : (0:ℝ) < b := by exact_mod_cast hb
  show 2 * Real.log ((a:ℝ)+b) + Real.log 12 ≤ _
  have e : 2 * Real.log ((a:ℝ)+b) + Real.log 12 = Real.log (12*((a:ℝ)+b)^2) := by
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]; push_cast; ring
  rw [e]
  apply Real.log_le_log (by positivity)
  nlinarith [sq_nonneg ((a:ℝ)-b)]
