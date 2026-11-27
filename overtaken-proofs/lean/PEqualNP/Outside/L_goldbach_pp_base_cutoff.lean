import Mathlib.Data.Nat.Prime.Basic

theorem PEqualNP.Outside.L_goldbach_pp_base_cutoff :
    ∀ p a n : ℕ, 2≤p → 2≤a → p^a≤n → p≤Nat.sqrt n := by
  intro p a n hp ha h
  apply Nat.le_sqrt.mpr
  calc p * p = p ^ 2 := (sq p).symm
    _ ≤ p ^ a := Nat.pow_le_pow_right (by omega) ha
    _ ≤ n := h
