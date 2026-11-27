import Mathlib

theorem Conjectures.Goldbach.DynWindowTrap :
    ∀ (A B : Set ℤ), (∀ x ∈ A, 0 < x) → (∀ x ∈ B, x < 0) → ∀ i j k : ℤ, i+k ∈ A → j+k ∈ B → -i < k ∧ k < -j := by
  intro A B hA hB i j k hi hj
  have h1 := hA _ hi
  have h2 := hB _ hj
  constructor <;> omega
