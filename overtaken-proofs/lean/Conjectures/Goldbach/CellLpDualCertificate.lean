import Mathlib

theorem Conjectures.Goldbach.CellLpDualCertificate :
    ∀ (C K : ℕ) (M s t : ℕ → ℝ) (y B : ℕ → ℝ) (A : ℕ → ℕ → ℝ) (U : ℝ), (∀ c ∈ Finset.range C, 0 ≤ M c) → (∀ c ∈ Finset.range C, (∑ k ∈ Finset.range K, y k * A k c) - s c ≤ t c) → (∀ k ∈ Finset.range K, B k ≤ y k * ∑ c ∈ Finset.range C, M c * A k c) → (∑ c ∈ Finset.range C, M c * s c ≤ U) → ∑ k ∈ Finset.range K, B k - U ≤ ∑ c ∈ Finset.range C, M c * t c := by
  intro C K M s t y B A U hM hd hB hU
  have h1 : ∑ k ∈ Finset.range K, B k ≤ ∑ k ∈ Finset.range K, y k * ∑ c ∈ Finset.range C, M c * A k c :=
    Finset.sum_le_sum hB
  have h2 : ∑ k ∈ Finset.range K, y k * ∑ c ∈ Finset.range C, M c * A k c
      = ∑ c ∈ Finset.range C, M c * ∑ k ∈ Finset.range K, y k * A k c := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun k _ => by ring
  have h3 : ∑ c ∈ Finset.range C, M c * ∑ k ∈ Finset.range K, y k * A k c
      ≤ ∑ c ∈ Finset.range C, M c * (t c + s c) := by
    refine Finset.sum_le_sum fun c hc => mul_le_mul_of_nonneg_left ?_ (hM c hc)
    linarith [hd c hc]
  have h4 : ∑ c ∈ Finset.range C, M c * (t c + s c)
      = ∑ c ∈ Finset.range C, M c * t c + ∑ c ∈ Finset.range C, M c * s c := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun c _ => by ring
  linarith
