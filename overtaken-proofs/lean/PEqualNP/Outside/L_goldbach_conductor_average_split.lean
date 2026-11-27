import Mathlib.Tactic.Ring
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Fin

theorem PEqualNP.Outside.L_goldbach_conductor_average_split :
    ∀ (n m : ℕ) (d : Fin m → ℕ) (u : Fin m → ℝ), (2/(Nat.totient n : ℝ))*(∑ j, u j) = (2/(Nat.totient n : ℝ))*(∑ j ∈ Finset.univ.filter (fun j => n^3 < (d j)^4), u j) + (2/(Nat.totient n : ℝ))*(∑ j ∈ Finset.univ.filter (fun j => (d j)^4 ≤ n^3), u j) := by
  intro n m d u
  rw [← mul_add]
  congr 1
  have h : (Finset.univ.filter (fun j : Fin m => (d j)^4 ≤ n^3)) = Finset.univ.filter (fun j : Fin m => ¬ (n^3 < (d j)^4)) := by
    ext j; simp
  rw [h, Finset.sum_filter_add_sum_filter_not]
