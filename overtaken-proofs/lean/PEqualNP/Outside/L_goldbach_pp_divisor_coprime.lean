import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.Prime.Basic

theorem PEqualNP.Outside.L_goldbach_pp_divisor_coprime :
    ∀ p a n : ℕ, 0<a → ((p^a).Coprime n ↔ p.Coprime n) := by
  intro p a n ha
  exact Nat.coprime_pow_left_iff ha p n
