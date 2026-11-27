import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.BigOperators.Fin

theorem PEqualNP.Outside.L_goldbach_cross_repeated_height :
    ∀ (m : ℕ) (v : ℂ), (∑ i : Fin m, ∑ _j ∈ Finset.univ.erase i, (v * star v).re) = (m : ℝ)*((m : ℝ)-1)*‖v‖^2 := by
  intro m v
  have h : (v * star v).re = ‖v‖^2 := by
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    rw [Complex.ofReal_re]
  simp only [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin, h, nsmul_eq_mul]
  cases m with
  | zero => simp
  | succ n => simp; ring
