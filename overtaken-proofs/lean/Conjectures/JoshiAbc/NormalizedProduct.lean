import Mathlib

theorem Conjectures.JoshiAbc.NormalizedProduct :
    ∀ (d e : ℕ) (x y : ℝ), 0 < d → 0 < e → 0 < x → 0 < y → Real.log (x^e*y^d)/((d:ℝ)*e) = Real.log x/d + Real.log y/e := by
  intro d e x y hd he hx hy
  have hd' : (d:ℝ) ≠ 0 := by positivity
  have he' : (e:ℝ) ≠ 0 := by positivity
  rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]
  field_simp
