import Mathlib

theorem Conjectures.JoshiAbc.LossRatio :
    ∀ l : ℝ, 3 < l → (4*l/((l-3)*(l+1))) / (4*l/((l-3)*(l+4))) = 1+3/(l+1) := by
  intro l hl
  have h1 : l - 3 ≠ 0 := by linarith
  have h2 : l + 1 ≠ 0 := by linarith
  have h3 : l + 4 ≠ 0 := by linarith
  have h4 : l ≠ 0 := by linarith
  field_simp
  ring
