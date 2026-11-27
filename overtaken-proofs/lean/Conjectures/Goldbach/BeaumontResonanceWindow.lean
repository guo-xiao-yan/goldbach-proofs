import Mathlib

theorem Conjectures.Goldbach.BeaumontResonanceWindow :
    ∀ n p q : ℕ, 0 < n → n ≤ p+q → p+q < 2*n → (n ∣ p+q ↔ p+q=n) := by
  intro n p q hn h1 h2
  constructor
  · rintro ⟨k, hk⟩
    have : k = 1 := by
      rcases k with _ | _ | k <;> simp_all <;> nlinarith
    subst this; omega
  · intro h; rw [h]
