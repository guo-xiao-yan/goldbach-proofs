import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

theorem PEqualNP.Outside.L_goldbach_odd_kernel_quadratic :
    ∀ (n : ℕ) (a : ℕ → ℝ), (∑ i ∈ Finset.range (n+1), ∑ j ∈ Finset.range (n+1), a i*a j*((if i=j then 1 else 0)-(if i+j=n then 1 else 0))) = (∑ i ∈ Finset.range (n+1), (a i)^2) - ∑ i ∈ Finset.range (n+1), a i*a (n-i) := by
  intro n a
  have h1 : ∀ i ∈ Finset.range (n+1), ∑ j ∈ Finset.range (n+1), a i*a j*((if i=j then 1 else 0)-(if i+j=n then 1 else 0)) = (a i)^2 - a i * a (n-i) := by
    intro i hi
    have hi' := Finset.mem_range.mp hi
    simp only [mul_sub, Finset.sum_sub_distrib, mul_ite, mul_one, mul_zero]
    have e1 : ∑ j ∈ Finset.range (n+1), (if i=j then a i*a j else 0) = (a i)^2 := by
      rw [Finset.sum_ite_eq]
      simp [Finset.mem_range, hi', sq]
    have e2 : ∑ j ∈ Finset.range (n+1), (if i+j=n then a i*a j else 0) = a i * a (n-i) := by
      have : ∀ j, (i + j = n ↔ n - i = j) := fun j => by omega
      simp only [this]
      rw [Finset.sum_ite_eq]
      simp [Finset.mem_range]
    rw [e1, e2]
  rw [Finset.sum_congr rfl h1, Finset.sum_sub_distrib]
