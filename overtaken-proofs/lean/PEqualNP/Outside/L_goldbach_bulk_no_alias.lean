import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Real.Basic

theorem PEqualNP.Outside.L_goldbach_bulk_no_alias :
    ∀ (x n : ℕ) (w : ℕ → ℝ), n≤2*x → (∑ p ∈ Finset.range (x+1), ∑ q ∈ Finset.range (x+1), if (p+q)%(2*x+1)=n then w p*w q else 0) = ∑ p ∈ (Finset.range (x+1)).filter (fun p => p≤n ∧ n-p≤x), w p*w (n-p) := by
  intro x n w hn
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro p hp
  have hp' : p < x + 1 := Finset.mem_range.mp hp
  have key : ∀ q ∈ Finset.range (x+1), (if (p+q)%(2*x+1)=n then w p*w q else 0) =
      if p ≤ n ∧ n - p = q then w p * w (n - p) else 0 := by
    intro q hq
    have hq' : q < x + 1 := Finset.mem_range.mp hq
    have hlt : p + q < 2 * x + 1 := by omega
    rw [Nat.mod_eq_of_lt hlt]
    by_cases h : p + q = n
    · have h2 : p ≤ n ∧ n - p = q := by omega
      rw [if_pos h, if_pos h2]
      have : q = n - p := by omega
      subst this
      rfl
    · have h2 : ¬ (p ≤ n ∧ n - p = q) := by omega
      rw [if_neg h, if_neg h2]
  rw [Finset.sum_congr rfl key]
  by_cases h : p ≤ n ∧ n - p ≤ x
  · rw [if_pos h]
    have : (∑ q ∈ Finset.range (x+1), if p ≤ n ∧ n - p = q then w p * w (n - p) else 0)
        = ∑ q ∈ Finset.range (x+1), if n - p = q then w p * w (n - p) else 0 := by
      apply Finset.sum_congr rfl
      intro q _
      simp only [h.1, true_and]
    rw [this, Finset.sum_ite_eq]
    rw [if_pos (Finset.mem_range.mpr (by omega))]
  · rw [if_neg h]
    apply Finset.sum_eq_zero
    intro q hq
    have hq' : q < x + 1 := Finset.mem_range.mp hq
    have h2 : ¬ (p ≤ n ∧ n - p = q) := by omega
    rw [if_neg h2]
