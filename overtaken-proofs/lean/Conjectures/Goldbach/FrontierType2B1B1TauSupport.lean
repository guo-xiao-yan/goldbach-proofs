import Mathlib

theorem Conjectures.Goldbach.FrontierType2B1B1TauSupport :
    let U := fun n : ℕ => ⌊(n:ℝ)^(1/16:ℝ)⌋₊; let B₁ := fun n : ℕ => ⌊(n:ℝ)^(1/4:ℝ)⌋₊; let τ₁ := fun (n m : ℕ) => ∑ a ∈ (Nat.divisors m).filter (fun a => U n < a ∧ a ≤ B₁ n ∧ U n < m / a), (∑ d ∈ (Nat.divisors a).filter (fun d => U n < d), ((ArithmeticFunction.moebius d : ℤ) : ℝ)) * ArithmeticFunction.vonMangoldt (m / a); ∀ n m : ℕ, m ≤ (U n)^2 → τ₁ n m = 0 := by
  intro U B₁ τ₁ n m hm
  show (∑ a ∈ (Nat.divisors m).filter (fun a => U n < a ∧ a ≤ B₁ n ∧ U n < m / a), (∑ d ∈ (Nat.divisors a).filter (fun d => U n < d), ((ArithmeticFunction.moebius d : ℤ) : ℝ)) * ArithmeticFunction.vonMangoldt (m / a)) = 0
  apply Finset.sum_eq_zero
  intro a ha
  exfalso
  rw [Finset.mem_filter] at ha
  obtain ⟨_, h1, _, h3⟩ := ha
  have h4 : a * (m / a) ≤ m := Nat.mul_div_le m a
  have h5 : (U n + 1) * (U n + 1) ≤ a * (m / a) := Nat.mul_le_mul h1 h3
  nlinarith
