import Mathlib.Data.Nat.Prime.Basic

theorem PEqualNP.Outside.L_goldbach_unit_diagonal_disjoint :
    ∀ n a : ℕ, 2<n → Nat.Coprime a n → ¬ n ∣ a+a := by
  intro n a hn hc hd
  have h2 : n ∣ 2 * a := by rw [two_mul]; exact hd
  have h3 : n ∣ 2 := (Nat.Coprime.dvd_of_dvd_mul_right hc.symm h2)
  have := Nat.le_of_dvd Nat.two_pos h3
  omega
