import Mathlib

theorem Conjectures.Goldbach.FareySpacingLower :
    ∀ (Q a b q r : ℕ), 1 ≤ q → q ≤ Q → 1 ≤ r → r ≤ Q → Nat.Coprime a q → Nat.Coprime b r → (q ≠ r ∨ a % q ≠ b % r) → ∀ m : ℤ, 1 / (Q : ℝ) ^ 2 ≤ |(a : ℝ) / q - (b : ℝ) / r - (m : ℝ)| := by
  intro Q a b q r hq hqQ hr hrQ ha hb hne m
  have hqpos : (0:ℝ) < q := by exact_mod_cast hq
  have hrpos : (0:ℝ) < r := by exact_mod_cast hr
  have key : (a : ℝ) / q - (b : ℝ) / r - (m : ℝ)
      = (((a:ℤ) * r - b * q - m * q * r : ℤ) : ℝ) / ((q:ℝ) * r) := by
    push_cast
    field_simp
  rw [key, abs_div, abs_of_pos (mul_pos hqpos hrpos)]
  by_cases hN : ((a:ℤ) * r - b * q - m * q * r) = 0
  · exfalso
    have h1 : (q:ℤ) ∣ ((a * r : ℕ) : ℤ) := ⟨b + m * r, by push_cast; linarith⟩
    have h2 : (r:ℤ) ∣ ((b * q : ℕ) : ℤ) := ⟨a - m * q, by push_cast; linarith⟩
    have h1' : q ∣ a * r := Int.natCast_dvd_natCast.mp h1
    have h2' : r ∣ b * q := Int.natCast_dvd_natCast.mp h2
    have h3 : q ∣ r := (Nat.Coprime.symm ha).dvd_of_dvd_mul_left h1'
    have h4 : r ∣ q := (Nat.Coprime.symm hb).dvd_of_dvd_mul_left h2'
    have hqr : q = r := Nat.dvd_antisymm h3 h4
    subst hqr
    have h5 : (a:ℤ) = b + m * q := by
      have : (q:ℤ) * (a - b - m * q) = 0 := by linarith
      rcases mul_eq_zero.mp this with h | h
      · exfalso; have : (q:ℤ) ≠ 0 := by exact_mod_cast (by omega : q ≠ 0)
        exact this h
      · linarith
    have h6 : (a:ℤ) % q = (b:ℤ) % q := by
      rw [h5, Int.add_mul_emod_self_right]
    have h7 : a % q = b % q := by exact_mod_cast h6
    rcases hne with h | h
    · exact h rfl
    · exact h h7
  · have h1 : (1:ℝ) ≤ |(((a:ℤ) * r - b * q - m * q * r : ℤ) : ℝ)| := by
      have : (1:ℤ) ≤ |((a:ℤ) * r - b * q - m * q * r)| := Int.one_le_abs hN
      exact_mod_cast this
    have hQ : (0:ℝ) < Q := by
      have : (0:ℝ) < q := hqpos
      have : (q:ℝ) ≤ Q := by exact_mod_cast hqQ
      linarith
    have hqr : (q:ℝ) * r ≤ (Q:ℝ)^2 := by
      have : (q:ℝ) ≤ Q := by exact_mod_cast hqQ
      have : (r:ℝ) ≤ Q := by exact_mod_cast hrQ
      nlinarith
    calc 1 / (Q:ℝ)^2 ≤ 1 / ((q:ℝ) * r) := one_div_le_one_div_of_le (mul_pos hqpos hrpos) hqr
      _ ≤ _ := by
        apply div_le_div_of_nonneg_right h1 (mul_pos hqpos hrpos).le
