import Mathlib

theorem Conjectures.Goldbach.BeaumontMarginalObstruction :
    ∀ m : ℕ, 2 ≤ m → ∃ a b : Fin m → ZMod m, Function.Bijective a ∧ Function.Bijective b ∧ ∀ t, a t ≠ b t := by
  intro m hm
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 2 := ⟨m - 2, by omega⟩
  show ∃ a b : Fin (n+2) → Fin (n+2), Function.Bijective a ∧ Function.Bijective b ∧ ∀ t, a t ≠ b t
  refine ⟨id, fun t => t + 1, Function.bijective_id, (Equiv.addRight (1 : Fin (n+2))).bijective, ?_⟩
  intro t h
  have h2 : (t : Fin (n+2)) + 1 = t := h.symm
  have : (1 : Fin (n+2)) = 0 := by simpa using h2
  exact absurd this (by simp [Fin.ext_iff])
