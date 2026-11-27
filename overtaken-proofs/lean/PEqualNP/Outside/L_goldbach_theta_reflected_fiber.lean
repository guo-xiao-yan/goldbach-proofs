import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Linarith

theorem PEqualNP.Outside.L_goldbach_theta_reflected_fiber :
    ∀ (m r : ℕ) (c : Fin m → Fin r) (R : Fin m ≃ Fin m) (S : Fin r ≃ Fin r) (a : Fin m → ℝ), (∀ i, c (R i) = S (c i)) → let F := fun j => Finset.univ.filter (fun i => c i = j); ∀ j, (∑ i ∈ F j, a (R i))/((F j).card:ℝ) = (∑ i ∈ F (S j), a i)/((F (S j)).card:ℝ) := by
  intro m r c R S a hc F j
  have hmem : ∀ i, i ∈ F j ↔ R i ∈ F (S j) := by
    intro i
    simp only [F, Finset.mem_filter, Finset.mem_univ, true_and, hc]
    exact S.injective.eq_iff.symm
  have h1 : ∑ i ∈ F j, a (R i) = ∑ i ∈ F (S j), a i :=
    Finset.sum_equiv R hmem (fun i _ => rfl)
  have h2 : ∑ i ∈ F j, (1 : ℝ) = ∑ i ∈ F (S j), (1 : ℝ) :=
    Finset.sum_equiv R hmem (fun i _ => rfl)
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at h2
  rw [h1, h2]
