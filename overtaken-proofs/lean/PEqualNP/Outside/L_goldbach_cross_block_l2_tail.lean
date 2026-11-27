import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.GCongr

theorem PEqualNP.Outside.L_goldbach_cross_block_l2_tail :
    ∀ (m : ℕ) (a b : Fin m → ℂ), |∑ i, ((a i+b i)*star (a i+b i)-a i*star (a i)-b i*star (b i)).re|^2 ≤ 4*(∑ i, ‖a i‖^2)*(∑ i, ‖b i‖^2) := by
  intro m a b
  have key : ∀ i, ((a i+b i)*star (a i+b i)-a i*star (a i)-b i*star (b i)).re
      = 2 * ((a i).re * (b i).re + (a i).im * (b i).im) := by
    intro i
    simp only [Complex.sub_re, Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im, Complex.add_re, Complex.add_im]
    ring
  have bd : ∀ i, |(a i).re * (b i).re + (a i).im * (b i).im| ≤ ‖a i‖ * ‖b i‖ := by
    intro i
    have h := Complex.abs_re_le_norm (a i * star (b i))
    have e : (a i * star (b i)).re = (a i).re * (b i).re + (a i).im * (b i).im := by
      simp only [Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im]
      ring
    rw [e, norm_mul, norm_star] at h
    exact h
  simp only [key]
  rw [← Finset.mul_sum]
  have h1 : |∑ i, ((a i).re * (b i).re + (a i).im * (b i).im)| ≤ ∑ i, ‖a i‖ * ‖b i‖ :=
    (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun i _ => bd i))
  have h2 := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin m)) (fun i => ‖a i‖) (fun i => ‖b i‖)
  have h3 : |∑ i, ((a i).re * (b i).re + (a i).im * (b i).im)|^2 ≤ (∑ i, ‖a i‖ * ‖b i‖)^2 := by
    gcongr
  rw [abs_mul, mul_pow, abs_two]
  nlinarith
