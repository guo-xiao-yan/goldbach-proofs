import Mathlib

theorem Conjectures.Goldbach.BeaumontDenseExactObstruction :
    ∃ A : Set ℝ, Dense A ∧ (0:ℝ) ∈ closure A ∧ (0:ℝ) ∉ A := by
  refine ⟨{x | x ≠ 0}, ?_, ?_, ?_⟩
  · exact dense_compl_singleton (0:ℝ)
  · have h : Dense ({x : ℝ | x ≠ 0}) := dense_compl_singleton (0:ℝ)
    rw [h.closure_eq]; trivial
  · simp
