import Mathlib

theorem Conjectures.JoshiAbc.ConstantHull :
    ∀ l Q R U δ : ℝ, 3 < l → -Q-δ ≤ R → R ≤ -(l*(l+1)/12)*Q+U → 2*l*Q/6 ≤ 4*l/((l-3)*(l+4))*(U+δ) := by
  intro l Q R U δ hl h1 h2
  have hD : 0 < (l-3)*(l+4) := mul_pos (by linarith) (by linarith)
  have h3 : (l-3)*(l+4)/12*Q ≤ U+δ := by nlinarith
  have h4 : 4*l/((l-3)*(l+4))*(U+δ) - 2*l*Q/6 = 4*l/((l-3)*(l+4))*((U+δ) - (l-3)*(l+4)/12*Q) := by
    field_simp
    ring
  have h5 : 0 ≤ 4*l/((l-3)*(l+4))*((U+δ) - (l-3)*(l+4)/12*Q) :=
    mul_nonneg (div_nonneg (by linarith) hD.le) (by linarith)
  linarith
