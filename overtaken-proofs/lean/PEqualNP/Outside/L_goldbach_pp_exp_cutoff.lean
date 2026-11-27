import Mathlib.Data.Nat.Log

theorem PEqualNP.Outside.L_goldbach_pp_exp_cutoff :
    ∀ p a n : ℕ, 2≤p → p^a≤n → a≤Nat.log 2 n := by
  intro p a n hp h
  apply Nat.le_log_of_pow_le Nat.one_lt_two
  exact le_trans (Nat.pow_le_pow_left hp a) h
