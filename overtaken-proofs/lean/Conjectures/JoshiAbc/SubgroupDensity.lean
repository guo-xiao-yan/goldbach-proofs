import Mathlib

theorem Conjectures.JoshiAbc.SubgroupDensity :
    ∀ (w v : ℝ) (d i : ℕ), 0 < w → 0 < d → 0 < i → w/i ≤ v → Real.log w/d-Real.log i/d ≤ Real.log v/d := by
  intro w v d i hw hd hi h
  have hi' : (0:ℝ) < i := by exact_mod_cast hi
  have hd' : (0:ℝ) < d := by exact_mod_cast hd
  have h1 : Real.log (w/i) ≤ Real.log v := Real.log_le_log (by positivity) h
  rw [Real.log_div hw.ne' hi'.ne'] at h1
  rw [← sub_div]
  exact div_le_div_of_nonneg_right (by linarith) hd'.le
