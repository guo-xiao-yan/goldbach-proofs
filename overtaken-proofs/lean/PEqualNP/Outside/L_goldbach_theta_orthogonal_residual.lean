import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

private lemma key_orth (m r : ℕ) (c : Fin m → Fin r) (a : Fin m → ℝ) (g : Fin r → ℝ) :
    ∑ i, (a i - (∑ k ∈ Finset.univ.filter (fun k => c k = c i), a k) /
      ((Finset.univ.filter (fun k => c k = c i)).card : ℝ)) * g (c i) = 0 := by
  rw [← Finset.sum_fiberwise Finset.univ c]
  apply Finset.sum_eq_zero
  intro j _
  have h1 : ∀ i ∈ Finset.univ.filter (fun i => c i = j),
      (a i - (∑ k ∈ Finset.univ.filter (fun k => c k = c i), a k) /
        ((Finset.univ.filter (fun k => c k = c i)).card : ℝ)) * g (c i)
      = (a i - (∑ k ∈ Finset.univ.filter (fun k => c k = j), a k) /
        ((Finset.univ.filter (fun k => c k = j)).card : ℝ)) * g j := by
    intro i hi
    rw [(Finset.mem_filter.mp hi).2]
  rw [Finset.sum_congr rfl h1, ← Finset.sum_mul, Finset.sum_sub_distrib, Finset.sum_const,
    nsmul_eq_mul]
  by_cases h : (Finset.univ.filter (fun k => c k = j)).card = 0
  · rw [Finset.card_eq_zero] at h
    rw [h]; simp
  · have h' : ((Finset.univ.filter (fun k => c k = j)).card : ℝ) ≠ 0 := by exact_mod_cast h
    rw [mul_div_cancel₀ _ h']
    simp

theorem PEqualNP.Outside.L_goldbach_theta_orthogonal_residual :
    ∀ (m r : ℕ) (c : Fin m → Fin r) (R : Fin m ≃ Fin m) (S : Fin r ≃ Fin r) (a : Fin m → ℝ), (∀ i, c (R i) = S (c i)) → let F := fun j => Finset.univ.filter (fun i => c i = j); let b := fun i => (∑ k ∈ F (c i), a k)/((F (c i)).card:ℝ); (∑ i, a i*a (R i)) - (∑ i, b i*b (R i)) = ∑ i, (a i-b i)*(a (R i)-b (R i)) := by
  intro m r c R S a hc F b
  set μ : Fin r → ℝ := fun j => (∑ k ∈ Finset.univ.filter (fun k => c k = j), a k) /
        ((Finset.univ.filter (fun k => c k = j)).card : ℝ) with hμ
  have hb : ∀ i, b i = μ (c i) := fun i => rfl
  have e1 : ∑ i, (a i - b i) * b (R i) = 0 := by
    have := key_orth m r c a (fun j => μ (S j))
    simp only [hb, hc]
    exact this
  have hcs : ∀ j, c (R.symm j) = S.symm (c j) := by
    intro j
    apply S.injective
    rw [Equiv.apply_symm_apply, ← hc, Equiv.apply_symm_apply]
  have e2 : ∑ i, b i * (a (R i) - b (R i)) = 0 := by
    rw [← Equiv.sum_comp R.symm]
    have := key_orth m r c a (fun j => μ (S.symm j))
    have h3 : ∀ i, b (R.symm i) * (a (R (R.symm i)) - b (R (R.symm i))) =
        (a i - b i) * μ (S.symm (c i)) := by
      intro i
      rw [hb, hcs, Equiv.apply_symm_apply, mul_comm]
    simp only [h3]
    exact this
  have e4 : ∀ i, (a i - b i) * (a (R i) - b (R i)) =
      (a i * a (R i) - b i * b (R i)) - (a i - b i) * b (R i) - b i * (a (R i) - b (R i)) := by
    intro i; ring
  simp only [e4, Finset.sum_sub_distrib, e1, e2]
  ring
