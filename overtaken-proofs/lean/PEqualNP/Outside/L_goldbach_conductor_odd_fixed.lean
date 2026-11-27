import Mathlib.Tactic.Ring
import Mathlib.Analysis.Complex.Basic

theorem PEqualNP.Outside.L_goldbach_conductor_odd_fixed :
    ∀ (m : ℕ) (r : Fin m → Fin m) (v : Fin m → ℂ), (∀ i, v (r i)= -v i) → ∀ i, r i=i → v i=0 := by
  intro m r v h i hi
  have h1 := h i
  rw [hi] at h1
  have h2 : (2:ℂ) * v i = 0 := by linear_combination h1
  simpa using h2
