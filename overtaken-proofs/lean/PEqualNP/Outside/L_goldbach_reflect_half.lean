import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Data.Real.Basic

theorem PEqualNP.Outside.L_goldbach_reflect_half :
    ∀ (n : ℕ) (w : ℕ → ℝ), (∑ k ∈ Finset.range (n+1), w k*w (n-k)) = 2*(∑ k ∈ (Finset.range (n+1)).filter (fun k => 2*k<n), w k*w (n-k)) + (if Even n then (w (n/2))^2 else 0) := by
  intro n w
  have h1 := Finset.sum_filter_add_sum_filter_not (Finset.range (n+1)) (fun k => 2*k<n) (fun k => w k * w (n-k))
  have h2 := Finset.sum_filter_add_sum_filter_not ((Finset.range (n+1)).filter (fun k => ¬ 2*k<n)) (fun k => 2*k=n) (fun k => w k * w (n-k))
  have h3 : ∑ k ∈ ((Finset.range (n+1)).filter (fun k => ¬ 2*k<n)).filter (fun k => ¬ 2*k=n), w k * w (n-k)
      = ∑ k ∈ (Finset.range (n+1)).filter (fun k => 2*k<n), w k * w (n-k) := by
    refine Finset.sum_nbij' (fun k => n-k) (fun k => n-k) ?_ ?_ ?_ ?_ ?_
    · intro k hk
      simp only [Finset.mem_filter, Finset.mem_range] at hk ⊢
      omega
    · intro k hk
      simp only [Finset.mem_filter, Finset.mem_range] at hk ⊢
      omega
    · intro k hk
      simp only [Finset.mem_filter, Finset.mem_range] at hk
      omega
    · intro k hk
      simp only [Finset.mem_filter, Finset.mem_range] at hk
      omega
    · intro k hk
      simp only [Finset.mem_filter, Finset.mem_range] at hk
      have : n - (n - k) = k := by omega
      rw [this]; ring
  have h4 : ∑ k ∈ ((Finset.range (n+1)).filter (fun k => ¬ 2*k<n)).filter (fun k => 2*k=n), w k * w (n-k)
      = if Even n then (w (n/2))^2 else 0 := by
    split_ifs with he
    · obtain ⟨r, hr⟩ := he
      have : ((Finset.range (n+1)).filter (fun k => ¬ 2*k<n)).filter (fun k => 2*k=n) = {r} := by
        ext k
        simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
        omega
      rw [this, Finset.sum_singleton]
      have e : n / 2 = r := by omega
      have e2 : n - r = r := by omega
      rw [e, e2]; ring
    · refine Finset.sum_eq_zero (fun k hk => ?_)
      simp only [Finset.mem_filter, Finset.mem_range] at hk
      exact absurd ⟨k, by omega⟩ he
  linarith
