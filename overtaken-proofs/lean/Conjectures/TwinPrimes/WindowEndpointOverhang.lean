import Mathlib

theorem Conjectures.TwinPrimes.WindowEndpointOverhang :
    let w := fun (X : ℕ) => (Finset.range (2*X+1)).filter (fun n => X < n ∧ 50*n < 51*X); ∀ (X : ℕ) (f : ℕ → ℝ) (A : ℝ), 2 ≤ X → 0 ≤ A → (∀ n : ℕ, n ≤ 2*X+2 → 0 ≤ f n ∧ f n ≤ A) → 0 ≤ (w X).sum (fun n => f n * f (n+2)) - ((w X).filter (fun n => n+2 ∈ w X)).sum (fun n => f n * f (n+2)) ∧ (w X).sum (fun n => f n * f (n+2)) - ((w X).filter (fun n => n+2 ∈ w X)).sum (fun n => f n * f (n+2)) ≤ 2*A^2 := by
  intro w X f A hX hA hf
  have key : (w X).sum (fun n => f n * f (n+2)) - ((w X).filter (fun n => n+2 ∈ w X)).sum (fun n => f n * f (n+2))
      = ((w X).filter (fun n => n+2 ∉ w X)).sum (fun n => f n * f (n+2)) := by
    rw [← Finset.sum_filter_add_sum_filter_not (w X) (fun n => n+2 ∈ w X)]
    ring
  rw [key]
  have hmem : ∀ n ∈ (w X).filter (fun n => n+2 ∉ w X), n ≤ 2*X ∧ 51*X ≤ 50*(n+2) ∧ 50*n < 51*X := by
    intro n hn
    simp only [w, Finset.mem_filter, Finset.mem_range] at hn
    omega
  have hsub : (w X).filter (fun n => n+2 ∉ w X) ⊆ Finset.Ico ((51*X+49)/50 - 2) ((51*X+49)/50 - 2 + 2) := by
    intro n hn
    have := hmem n hn
    simp only [Finset.mem_Ico]
    omega
  have hcard : ((w X).filter (fun n => n+2 ∉ w X)).card ≤ 2 := by
    have := Finset.card_le_card hsub
    simpa using this
  constructor
  · apply Finset.sum_nonneg
    intro n hn
    have := hmem n hn
    exact mul_nonneg (hf n (by omega)).1 (hf (n+2) (by omega)).1
  · calc _ ≤ ∑ n ∈ (w X).filter (fun n => n+2 ∉ w X), A^2 := by
          apply Finset.sum_le_sum
          intro n hn
          have := hmem n hn
          have h1 := hf n (by omega)
          have h2 := hf (n+2) (by omega)
          rw [sq]
          exact mul_le_mul h1.2 h2.2 h2.1 hA
      _ = (((w X).filter (fun n => n+2 ∉ w X)).card : ℝ) * A^2 := by simp
      _ ≤ 2 * A^2 := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact_mod_cast hcard
