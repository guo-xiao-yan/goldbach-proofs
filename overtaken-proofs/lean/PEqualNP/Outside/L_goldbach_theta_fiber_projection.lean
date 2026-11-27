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

private lemma pyth (m r : ℕ) (c : Fin m → Fin r) (a : Fin m → ℝ) (b : Fin r → ℝ) :
    ∑ i, (a i - b (c i)) ^ 2 =
      ∑ i, (a i - (∑ k ∈ Finset.univ.filter (fun k => c k = c i), a k) /
        ((Finset.univ.filter (fun k => c k = c i)).card : ℝ)) ^ 2
      + ∑ i, ((∑ k ∈ Finset.univ.filter (fun k => c k = c i), a k) /
        ((Finset.univ.filter (fun k => c k = c i)).card : ℝ) - b (c i)) ^ 2 := by
  set μ : Fin m → ℝ := fun i => (∑ k ∈ Finset.univ.filter (fun k => c k = c i), a k) /
        ((Finset.univ.filter (fun k => c k = c i)).card : ℝ) with hμ
  have hk := key_orth m r c a (fun j => (∑ k ∈ Finset.univ.filter (fun k => c k = j), a k) /
        ((Finset.univ.filter (fun k => c k = j)).card : ℝ) - b j)
  have hk' : ∑ i, (a i - μ i) * (μ i - b (c i)) = 0 := hk
  have : ∀ i, (a i - b (c i)) ^ 2 = (a i - μ i) ^ 2 + (μ i - b (c i)) ^ 2
      + 2 * ((a i - μ i) * (μ i - b (c i))) := by intro i; ring
  simp only [this, Finset.sum_add_distrib, ← Finset.mul_sum, hk']
  ring

theorem PEqualNP.Outside.L_goldbach_theta_fiber_projection :
    ∀ (m r : ℕ) (c : Fin m → Fin r) (a : Fin m → ℝ) (b : Fin r → ℝ), let F := fun j => Finset.univ.filter (fun i => c i = j); let μ := fun j => (∑ i ∈ F j, a i)/((F j).card:ℝ); (∑ i, (a i-μ (c i))^2) ≤ ∑ i, (a i-b (c i))^2 := by
  intro m r c a b F μ
  have h := pyth m r c a b
  have h2 : 0 ≤ ∑ i, ((∑ k ∈ Finset.univ.filter (fun k => c k = c i), a k) /
        ((Finset.univ.filter (fun k => c k = c i)).card : ℝ) - b (c i)) ^ 2 :=
    Finset.sum_nonneg (fun i _ => sq_nonneg _)
  show _ ≤ _
  linarith
