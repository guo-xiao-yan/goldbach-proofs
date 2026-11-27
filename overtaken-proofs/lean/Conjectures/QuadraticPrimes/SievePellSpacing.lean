import Mathlib

theorem Conjectures.QuadraticPrimes.SievePellSpacing :
    ∀ (m a b u v : ℕ), (0 < m) → (0 < a) → (a < b) → (a^2 + 1 = m*u^2) → (b^2 + 1 = m*v^2) → 2*a < b := by
  intro m a b u v hm ha hab h1 h2
  have hu : 0 < u := by
    rcases Nat.eq_zero_or_pos u with h | h
    · subst h; simp at h1
    · exact h
  have hv : 0 < v := by
    rcases Nat.eq_zero_or_pos v with h | h
    · subst h; simp at h2
    · exact h
  zify at *
  have key : (m*u*v - a*b : ℤ)^2 - m*(b*u - a*v)^2 = 1 := by
    linear_combination (-((m:ℤ)*v^2-b^2))*h1 - h2
  have hb : (b:ℤ) = a*(m*u*v - a*b) + m*u*(b*u - a*v) := by
    linear_combination (b:ℤ)*h1
  have hB : 0 < (b*u - a*v : ℤ) := by
    by_contra hc
    push_neg at hc
    have h3 : (b*u:ℤ) ≥ 0 := by positivity
    have h4 : ((b:ℤ)*u)^2 ≤ (a*v)^2 := by nlinarith
    have h5 : (m:ℤ)*((b*u)^2 - (a*v)^2) = b^2 - a^2 := by
      linear_combination (-(b:ℤ)^2)*h1 + (a:ℤ)^2*h2
    nlinarith
  have hA : 0 < (m*u*v - a*b : ℤ) := by
    by_contra hc
    push_neg at hc
    have h3 : ((m:ℤ)*u*v) ≥ 0 := by positivity
    have h4 : ((m:ℤ)*u*v)^2 ≤ (a*b)^2 := by nlinarith
    have h5 : ((m:ℤ)*u*v)^2 = (a^2+1)*(b^2+1) := by
      rw [h1, h2]; ring
    nlinarith [sq_nonneg (a:ℤ), sq_nonneg (b:ℤ)]
  have hm2 : (2:ℤ) ≤ m := by
    by_contra hc
    have : (m:ℤ) = 1 := by omega
    rw [this] at h1
    have : (a:ℤ) < u := by nlinarith
    nlinarith
  have hA2 : (2:ℤ) ≤ m*u*v - a*b := by
    by_contra hc
    have : (m*u*v - a*b : ℤ) = 1 := by omega
    rw [this] at key
    nlinarith
  have hu1 : (1:ℤ) ≤ u := by exact_mod_cast hu
  have : (m:ℤ)*u ≥ 1 := by nlinarith
  nlinarith
