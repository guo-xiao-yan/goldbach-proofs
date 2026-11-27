import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.GCongr

theorem PEqualNP.Outside.L_goldbach_cluster_coherent_energy :
    ∀ (m : ℕ) (u : Fin m → ℂ), ‖∑ i, u i‖^2 ≤ (m : ℝ)*∑ i, ‖u i‖^2 := by
  intro m u
  have h1 : ‖∑ i, u i‖ ≤ ∑ i, ‖u i‖ := norm_sum_le _ _
  have h2 := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin m)) (fun _ => (1:ℝ)) (fun i => ‖u i‖)
  simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] at h2
  have h3 : ‖∑ i, u i‖^2 ≤ (∑ i, ‖u i‖)^2 := by
    gcongr
  linarith
