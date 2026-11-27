import Mathlib

theorem Conjectures.JoshiAbc.AdelicErrorSum :
    ∀ (n : ℕ) (w q r h : Fin n → ℝ), (∀ i, 0 ≤ w i ∧ -q i-h i ≤ r i) → -(∑ i, w i*q i)-(∑ i, w i*h i) ≤ ∑ i, w i*r i := by
  intro n w q r h H
  have : 0 ≤ ∑ i, (w i * r i + w i * q i + w i * h i) :=
    Finset.sum_nonneg fun i _ => by
      obtain ⟨a, b⟩ := H i
      nlinarith
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at this
  linarith
