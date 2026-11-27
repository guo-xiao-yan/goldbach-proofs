import Mathlib

theorem Conjectures.Goldbach.Type2CornerMoebiusTruncation :
    let μ := fun d : ℕ => ((ArithmeticFunction.moebius d : ℤ) : ℝ); ∀ (a U : ℕ), 1 < a → (∑ d ∈ (Nat.divisors a).filter (fun d => U < d), μ d) = - ∑ d ∈ (Nat.divisors a).filter (fun d => d ≤ U), μ d := by
  intro μ a U ha
  have h0 : (∑ d ∈ Nat.divisors a, μ d) = 0 := by
    have h := ArithmeticFunction.coe_mul_zeta_apply (f := (ArithmeticFunction.moebius : ArithmeticFunction ℤ)) (x := a)
    rw [ArithmeticFunction.moebius_mul_coe_zeta] at h
    have h1 : ∑ i ∈ Nat.divisors a, ArithmeticFunction.moebius i = 0 := by
      rw [← h]; simp [ArithmeticFunction.one_apply, show a ≠ 1 by omega]
    have h2 := congrArg (fun z : ℤ => (z : ℝ)) h1
    simpa [μ] using h2
  have hs := Finset.sum_filter_add_sum_filter_not (Nat.divisors a) (fun d => d ≤ U) μ
  have : (Nat.divisors a).filter (fun d => ¬ d ≤ U) = (Nat.divisors a).filter (fun d => U < d) := by
    apply Finset.filter_congr; intro x _; omega
  rw [this, h0] at hs
  linarith
