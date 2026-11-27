import Mathlib.Analysis.Complex.Basic

theorem PEqualNP.Outside.L_goldbach_reflection_conjugate_phase :
    ∀ (z : ℂ) (k : ℕ), ‖z‖=1 → (z⁻¹)^k=star (z^k) := by
  intro z k hz
  have h : z⁻¹ = star z := by
    rw [Complex.inv_def, Complex.normSq_eq_norm_sq, hz]
    simp
  rw [h, star_pow]
