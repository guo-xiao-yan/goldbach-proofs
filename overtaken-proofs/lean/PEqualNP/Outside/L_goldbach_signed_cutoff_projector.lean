import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith

theorem PEqualNP.Outside.L_goldbach_signed_cutoff_projector :
    ∀ (m : ℕ) (μ c : Fin m → ℝ) (t : ℝ), (∑ j, μ j*(c j)^2) ≤ t*(∑ j, (c j)^2) + ∑ j ∈ Finset.univ.filter (fun j => t<μ j), (μ j-t)*(c j)^2 := by
  intro m μ c t
  rw [Finset.mul_sum, ← Finset.sum_filter_add_sum_filter_not Finset.univ (fun j => t<μ j) (fun j => t*(c j)^2)]
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun j => t<μ j) (fun j => μ j*(c j)^2)]
  have h1 : ∑ j ∈ Finset.univ.filter (fun j => t<μ j), μ j*(c j)^2 = ∑ j ∈ Finset.univ.filter (fun j => t<μ j), (t*(c j)^2 + (μ j-t)*(c j)^2) :=
    Finset.sum_congr rfl (fun j _ => by ring)
  have h2 : ∑ j ∈ Finset.univ.filter (fun j => ¬ t<μ j), μ j*(c j)^2 ≤ ∑ j ∈ Finset.univ.filter (fun j => ¬ t<μ j), t*(c j)^2 :=
    Finset.sum_le_sum (fun j hj => by
      have : μ j ≤ t := not_lt.mp (Finset.mem_filter.mp hj).2
      nlinarith [sq_nonneg (c j)])
  rw [h1, Finset.sum_add_distrib] at *
  linarith
