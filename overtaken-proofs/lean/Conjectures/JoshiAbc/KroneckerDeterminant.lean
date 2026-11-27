import Mathlib

theorem Conjectures.JoshiAbc.KroneckerDeterminant :
    ∀ (m n : ℕ) (A : Matrix (Fin m) (Fin m) ℚ) (B : Matrix (Fin n) (Fin n) ℚ), (Matrix.kronecker A B).det = A.det^n * B.det^m := by
  intro m n A B
  have h := Matrix.det_kronecker A B
  simp only [Fintype.card_fin] at h
  exact h
