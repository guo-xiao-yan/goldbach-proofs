import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.BigOperators.Fin

private theorem real_var_aux (m : ℕ) (a : Fin m → ℝ) :
    ∑ i, ∑ j, (a i - a j) ^ 2 = 2 * ((m : ℝ) * (∑ i, a i ^ 2) - (∑ i, a i) ^ 2) := by
  have h1 : ∀ i j, (a i - a j) ^ 2 = a i ^ 2 + a j ^ 2 - 2 * (a i * a j) := by
    intro i j; ring
  simp only [h1, Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum, ← Finset.sum_mul, sq]
  ring

theorem PEqualNP.Outside.L_goldbach_cluster_balanced_energy :
    ∀ (m : ℕ) (u : Fin m → ℂ), (m : ℝ)*(∑ i, ‖u i‖^2)-‖∑ i, u i‖^2 = (∑ i, ∑ j, ‖u i-u j‖^2)/2 := by
  intro m u
  have e : ∀ z : ℂ, ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
    intro z
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have hr := real_var_aux m (fun i => (u i).re)
  have hi := real_var_aux m (fun i => (u i).im)
  simp only [e, Complex.sub_re, Complex.sub_im, Complex.re_sum, Complex.im_sum,
    Finset.sum_add_distrib] at *
  linarith
