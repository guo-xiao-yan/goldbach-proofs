import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic

theorem PEqualNP.Outside.L_goldbach_central_window_units :
    ∀ (n : ℕ) (w : ℕ → ℝ), (∀ k, ¬Nat.Prime k → w k=0) → 0 < (∑ k ∈ (Finset.range (n+1)).filter (fun k => n≤3*k ∧ 3*k≤2*n ∧ k.Coprime n), w k*w (n-k)) → ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p+q=n ∧ n≤3*p ∧ 3*p≤2*n ∧ p.Coprime n := by
  intro n w hw hpos
  obtain ⟨k, hk, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hpos.ne'
  rw [Finset.mem_filter, Finset.mem_range] at hk
  obtain ⟨hkn, h1, h2, h3⟩ := hk
  have hk1 : w k ≠ 0 := left_ne_zero_of_mul hne
  have hk2 : w (n - k) ≠ 0 := right_ne_zero_of_mul hne
  have hpk : k.Prime := by
    by_contra h
    exact hk1 (hw k h)
  have hpq : (n - k).Prime := by
    by_contra h
    exact hk2 (hw _ h)
  exact ⟨k, n - k, hpk, hpq, by omega, h1, h2, h3⟩
