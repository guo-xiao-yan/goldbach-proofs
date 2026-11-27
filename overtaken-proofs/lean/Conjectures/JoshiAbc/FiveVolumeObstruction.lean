import Mathlib

theorem Conjectures.JoshiAbc.FiveVolumeObstruction :
    ∀ (V : ℤ → ℝ), ¬ (V 5 = (1:ℝ)/5 ∧ V 5 = (1:ℝ)/25) := by
  intro V ⟨h1, h2⟩
  rw [h1] at h2
  norm_num at h2
