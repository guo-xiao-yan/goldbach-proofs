import Mathlib

theorem Conjectures.Goldbach.BeaumontPerturbedClockGap :
    ∀ (n : ℕ) (s : ℤ) (x : ℝ), |x-(s:ℝ)| < 1/2 → |x-(n:ℝ)| ≤ 1/2 → s=(n:ℤ) := by
  intro n s x h1 h2
  rw [abs_lt] at h1
  rw [abs_le] at h2
  have h3 : ((s:ℤ):ℝ) - (n:ℤ) < 1 := by push_cast; linarith [h1.1, h1.2, h2.1, h2.2]
  have h4 : ((n:ℤ):ℝ) - (s:ℤ) < 1 := by push_cast; linarith [h1.1, h1.2, h2.1, h2.2]
  have h3' : s - (n:ℤ) < 1 := by exact_mod_cast h3
  have h4' : (n:ℤ) - s < 1 := by exact_mod_cast h4
  omega
