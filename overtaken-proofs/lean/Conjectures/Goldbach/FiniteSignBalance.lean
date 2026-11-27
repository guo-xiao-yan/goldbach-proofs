import Mathlib

theorem Conjectures.Goldbach.FiniteSignBalance :
    ∀ (n m : ℕ) (b : ℕ → Fin m → ℝ), ∃ s : ℕ → ℝ, (∀ k, s k = 1 ∨ s k = -1) ∧ (∑ j, (∑ k ∈ Finset.range n, s k * b k j)^2) ≤ ∑ j, ∑ k ∈ Finset.range n, (b k j)^2 := by
  intro n m b
  induction n with
  | zero => exact ⟨fun _ => 1, fun _ => Or.inl rfl, by simp⟩
  | succ n ih =>
    obtain ⟨s, hs, h⟩ := ih
    have hsum : ∀ (σ : ℝ), (∑ j, (∑ k ∈ Finset.range (n+1), (Function.update s n σ) k * b k j)^2)
        = ∑ j, ((∑ k ∈ Finset.range n, s k * b k j) + σ * b n j)^2 := by
      intro σ
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.sum_range_succ]
      congr 2
      · refine Finset.sum_congr rfl fun k hk => ?_
        rw [Function.update_of_ne (by have := Finset.mem_range.mp hk; omega)]
      · simp
    have hb : ∀ j, ∑ k ∈ Finset.range (n+1), (b k j)^2 = ∑ k ∈ Finset.range n, (b k j)^2 + (b n j)^2 :=
      fun j => Finset.sum_range_succ _ _
    simp only [hb, Finset.sum_add_distrib]
    have key : ∑ j, ((∑ k ∈ Finset.range n, s k * b k j) + 1 * b n j)^2
        + ∑ j, ((∑ k ∈ Finset.range n, s k * b k j) + (-1) * b n j)^2
        = 2 * ∑ j, (∑ k ∈ Finset.range n, s k * b k j)^2 + 2 * ∑ j, (b n j)^2 := by
      rw [← Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    by_cases hc : ∑ j, ((∑ k ∈ Finset.range n, s k * b k j) + 1 * b n j)^2 ≤ ∑ j, (∑ k ∈ Finset.range n, s k * b k j)^2 + ∑ j, (b n j)^2
    · refine ⟨Function.update s n 1, fun k => ?_, ?_⟩
      · by_cases hk : k = n
        · subst hk; simp
        · rw [Function.update_of_ne hk]; exact hs k
      · rw [hsum]; linarith
    · refine ⟨Function.update s n (-1), fun k => ?_, ?_⟩
      · by_cases hk : k = n
        · subst hk; simp
        · rw [Function.update_of_ne hk]; exact hs k
      · rw [hsum]
        have : 0 ≤ ∑ j, ((∑ k ∈ Finset.range n, s k * b k j) + (-1) * b n j)^2 := Finset.sum_nonneg fun j _ => sq_nonneg _
        linarith
