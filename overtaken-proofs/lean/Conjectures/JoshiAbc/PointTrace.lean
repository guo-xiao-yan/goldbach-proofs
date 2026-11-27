import Mathlib

theorem Conjectures.JoshiAbc.PointTrace :
    let A : Matrix (Fin 2) (Fin 2) ℚ := !![0,5;1,0]; A.trace=0 ∧ A.det ≠ 0 := by
  intro A
  constructor
  · simp [A, Matrix.trace, Fin.sum_univ_two]
  · simp [A, Matrix.det_fin_two]
