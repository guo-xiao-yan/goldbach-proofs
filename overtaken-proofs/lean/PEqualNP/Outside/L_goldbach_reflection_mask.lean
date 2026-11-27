import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

theorem PEqualNP.Outside.L_goldbach_reflection_mask :
    ∀ (n : ℕ) (a : ℕ → ℝ), (let b := fun k => if Nat.Prime k then a k else 0; (∑ k ∈ Finset.range (n+1), a k*a (n-k)) - (∑ k ∈ Finset.range (n+1), b k*b (n-k)) = ∑ k ∈ Finset.range (n+1), if Nat.Prime k ∧ Nat.Prime (n-k) then 0 else a k*a (n-k)) := by
  intro n a
  show (∑ k ∈ Finset.range (n+1), a k*a (n-k)) - (∑ k ∈ Finset.range (n+1), (fun k => if Nat.Prime k then a k else 0) k * (fun k => if Nat.Prime k then a k else 0) (n-k)) = _
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k _
  by_cases hk : Nat.Prime k <;> by_cases h2 : Nat.Prime (n-k) <;> simp [hk, h2]
