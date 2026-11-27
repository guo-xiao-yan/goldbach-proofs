import Mathlib

theorem Conjectures.JoshiAbc.MeasurableDensity :
    ∀ (w v ρ : ℝ) (d : ℕ), 0 < w → 0 < ρ → ρ ≤ 1 → 0 < d → ρ*w ≤ v → (Real.log w + Real.log ρ)/d ≤ Real.log v/d := by
  intro w v ρ d hw hρ _ hd h
  have h1 : Real.log (ρ*w) ≤ Real.log v := Real.log_le_log (by positivity) h
  rw [Real.log_mul hρ.ne' hw.ne'] at h1
  have : (0:ℝ) < d := by exact_mod_cast hd
  apply div_le_div_of_nonneg_right _ this.le
  linarith
