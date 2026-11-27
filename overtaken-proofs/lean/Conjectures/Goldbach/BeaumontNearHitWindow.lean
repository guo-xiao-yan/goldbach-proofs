import Mathlib

theorem Conjectures.Goldbach.BeaumontNearHitWindow :
    ∀ (n p q r : ℕ) (k : ℤ), 0 < n → 2*r < n → r < p+q → p+q+r < 2*n → |(p:ℤ)+(q:ℤ)-k*(n:ℤ)| ≤ (r:ℤ) → |(p:ℤ)+(q:ℤ)-(n:ℤ)| ≤ (r:ℤ) := by
  intro n p q r k hn h2 h3 h4 h5
  have hn' : (0:ℤ) < n := by exact_mod_cast hn
  rw [abs_le] at h5 ⊢
  have h2' : 2*(r:ℤ) < n := by exact_mod_cast h2
  have h3' : (r:ℤ) < p+q := by exact_mod_cast h3
  have h4' : (p:ℤ)+q+r < 2*n := by exact_mod_cast h4
  have hk1 : 1 ≤ k := by
    by_contra h
    have : k ≤ 0 := by omega
    nlinarith [h5.2]
  have hk2 : k ≤ 1 := by
    by_contra h
    have : 2 ≤ k := by omega
    nlinarith [h5.1]
  have : k = 1 := by omega
  subst this
  simpa using h5
