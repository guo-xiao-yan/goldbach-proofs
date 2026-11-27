import Mathlib

theorem Conjectures.Goldbach.MovingCutoffFreezeBudget :
    ∀ (I : Finset ℕ) (K : ℕ) (b : ℕ → ℕ) (f : ℕ → ℂ) (r y : ℕ → ℝ) (G : ℕ → ℝ → ℂ), (∀ m ∈ I, b m < K) → (∀ m ∈ I, ‖f m‖ ≤ 1) → let B : ℕ → Finset ℕ := fun j => I.filter (fun m => b m = j); ‖∑ m ∈ I, f m * G m (r m)‖ ≤ ∑ j ∈ Finset.range K, ‖∑ m ∈ B j, f m * G m (y j)‖ + ∑ j ∈ Finset.range K, ∑ m ∈ B j, ‖G m (r m) - G m (y j)‖ ∧ (∑ j ∈ Finset.range K, Real.sqrt ((B j).card : ℝ)) ≤ Real.sqrt (K : ℝ) * Real.sqrt (I.card : ℝ) := by
  intro I K b f r y G hb hf B
  have hmaps : ∀ m ∈ I, b m ∈ Finset.range K := fun m hm => Finset.mem_range.2 (hb m hm)
  constructor
  · have h1 : ∑ m ∈ I, f m * G m (r m) = ∑ j ∈ Finset.range K, ∑ m ∈ B j, f m * G m (r m) :=
      (Finset.sum_fiberwise_of_maps_to hmaps _).symm
    rw [h1, ← Finset.sum_add_distrib]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    have h2 : ∑ m ∈ B j, f m * G m (r m)
        = ∑ m ∈ B j, f m * G m (y j) + ∑ m ∈ B j, f m * (G m (r m) - G m (y j)) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun m _ => by ring
    rw [h2]
    refine (norm_add_le _ _).trans (add_le_add le_rfl ?_)
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun m hm => ?_)
    rw [norm_mul]
    have hm' : m ∈ I := (Finset.mem_filter.1 hm).1
    calc ‖f m‖ * ‖G m (r m) - G m (y j)‖ ≤ 1 * ‖G m (r m) - G m (y j)‖ :=
          mul_le_mul_of_nonneg_right (hf m hm') (norm_nonneg _)
      _ = _ := one_mul _
  · have h := Real.sum_sqrt_mul_sqrt_le (Finset.range K) (f := fun _ => (1:ℝ)) (g := fun j => ((B j).card : ℝ)) (fun _ => zero_le_one) (fun j => Nat.cast_nonneg _)
    have hc : ∑ j ∈ Finset.range K, ((B j).card : ℝ) = I.card := by
      have := Finset.card_eq_sum_card_fiberwise hmaps
      exact_mod_cast this.symm
    simpa [hc] using h
