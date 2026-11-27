import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

theorem PEqualNP.Outside.L_goldbach_reflection_even_odd_energy :
    ∀ (n : ℕ) (b : ℕ → ℝ), (∑ k ∈ Finset.range (n+1), (b k+b (n-k))^2) + (∑ k ∈ Finset.range (n+1), (b k-b (n-k))^2) = 4*∑ k ∈ Finset.range (n+1), (b k)^2 := by
  intro n b
  have h : ∑ k ∈ Finset.range (n+1), (b (n-k))^2 = ∑ k ∈ Finset.range (n+1), (b k)^2 := by
    have := Finset.sum_range_reflect (fun k => (b k)^2) (n+1)
    simpa using this
  rw [← Finset.sum_add_distrib, Finset.mul_sum]
  have h2 : ∑ k ∈ Finset.range (n+1), ((b k+b (n-k))^2 + (b k-b (n-k))^2) = ∑ k ∈ Finset.range (n+1), (2*(b k)^2 + 2*(b (n-k))^2) := by
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [h2, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, h, Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  ring
