import Mathlib

theorem Conjectures.Goldbach.BeaumontQuotientObstruction :
    ∀ m : ℕ, 1 < m → ∃ a b : ℕ, a ≠ b ∧ a % m=b % m ∧ Nat.Prime a ∧ ¬ Nat.Prime b := by
  intro m hm
  refine ⟨2, 2 * (m + 1), by omega, ?_, Nat.prime_two, ?_⟩
  · have : 2 * (m + 1) = 2 + m * 2 := by ring
    rw [this, Nat.add_mul_mod_self_left]
  · intro hp
    have := (Nat.prime_mul_iff.mp hp)
    rcases this with ⟨_, h⟩ | ⟨_, h⟩ <;> omega
