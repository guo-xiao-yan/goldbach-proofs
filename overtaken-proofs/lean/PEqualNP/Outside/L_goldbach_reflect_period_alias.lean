import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

theorem PEqualNP.Outside.L_goldbach_reflect_period_alias :
    ∀ (n : ℕ) (b : ℕ → ℝ), 0<n → (∑ k ∈ Finset.range (n+1), b k*b (n-k)) = (∑ k ∈ Finset.range n, b k*b ((n-k)%n)) + 2*b 0*b n-(b 0)^2 := by
  intro n b hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [Finset.sum_range_succ, Finset.sum_range_succ' _ m, Finset.sum_range_succ' _ m]
  have h : ∑ k ∈ Finset.range m, b (k+1) * b (m+1-(k+1)) = ∑ k ∈ Finset.range m, b (k+1) * b ((m+1-(k+1)) % (m+1)) := by
    apply Finset.sum_congr rfl
    intro k hk
    have hk' := Finset.mem_range.mp hk
    rw [Nat.mod_eq_of_lt (by omega)]
  rw [h]
  simp
  ring
