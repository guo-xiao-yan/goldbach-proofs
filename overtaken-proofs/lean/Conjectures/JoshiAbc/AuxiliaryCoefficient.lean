import Mathlib

theorem Conjectures.JoshiAbc.AuxiliaryCoefficient :
    ∀ ε : ℝ, 0 < ε → ∃ l : ℕ, l.Prime ∧ 7 ≤ l ∧ 4*(l:ℝ)/(((l:ℝ)-3)*(l+1)) ≤ ε := by
  intro ε hε
  obtain ⟨l, hl, hp⟩ := Nat.exists_infinite_primes (7 + ⌈4/ε⌉₊)
  refine ⟨l, hp, by omega, ?_⟩
  have h1 : (4/ε : ℝ) ≤ (⌈4/ε⌉₊ : ℝ) := Nat.le_ceil _
  have h2 : ((7 + ⌈4/ε⌉₊ : ℕ) : ℝ) ≤ l := by exact_mod_cast hl
  push_cast at h2
  have h3 : (4:ℝ)/ε ≤ (l:ℝ) - 7 := by linarith
  have hl3 : (0:ℝ) < (l:ℝ) - 3 := by
    have : (0:ℝ) ≤ (⌈4/ε⌉₊ : ℝ) := Nat.cast_nonneg _
    linarith
  have hl0 : (0:ℝ) < l + 1 := by linarith
  rw [div_le_iff₀ (mul_pos hl3 hl0)]
  rw [div_le_iff₀ hε] at h3
  nlinarith [mul_pos hl3 hl0]
