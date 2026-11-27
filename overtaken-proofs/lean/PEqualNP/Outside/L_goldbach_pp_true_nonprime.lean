import Mathlib.Data.Nat.Prime.Basic

theorem PEqualNP.Outside.L_goldbach_pp_true_nonprime :
    ∀ p a : ℕ, p.Prime → 2≤a → ¬ Nat.Prime (p^a) := by
  intro p a hp ha
  exact Nat.Prime.not_prime_pow ha
