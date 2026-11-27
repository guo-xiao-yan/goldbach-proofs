import Mathlib.Tactic.Linarith
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Positivity
import Mathlib.Data.Real.Basic

theorem PEqualNP.Outside.L_goldbach_bulk_exception_budget :
    ∀ (s : Finset ℕ) (r m : ℕ → ℝ) (L : ℝ), 0<L → (∀ n ∈ s, L ≤ m n) → (((s.filter (fun n => r n=0)).card : ℝ)*L^2) ≤ ∑ n ∈ s, (r n-m n)^2 := by
  intro s r m L hL h
  have h1 : ((s.filter (fun n => r n = 0)).card : ℝ) * L ^ 2 = ∑ n ∈ s.filter (fun n => r n = 0), L ^ 2 := by
    simp
  rw [h1]
  calc ∑ n ∈ s.filter (fun n => r n = 0), L ^ 2 ≤ ∑ n ∈ s.filter (fun n => r n = 0), (r n - m n) ^ 2 := by
        apply Finset.sum_le_sum
        intro n hn
        rw [Finset.mem_filter] at hn
        have := h n hn.1
        have h0 := hn.2
        rw [h0]
        nlinarith
    _ ≤ ∑ n ∈ s, (r n - m n) ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun i _ _ => sq_nonneg _)
