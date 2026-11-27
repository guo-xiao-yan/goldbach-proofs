import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Positivity

theorem PEqualNP.Outside.L_goldbach_sieve_square_majorant :
    ∀ (P m : ℕ) (D : Finset ℕ) (weights : ℕ → ℝ), 1∈D → weights 1=1 → (∀ d ∈ D, d∣P) → (if m.Coprime P then (1:ℝ) else 0) ≤ (∑ d ∈ D.filter (fun d => d∣m), weights d)^2 := by
  intro P m D weights h1 hw hD
  by_cases hc : m.Coprime P
  · rw [if_pos hc]
    have : D.filter (fun d => d ∣ m) = {1} := by
      ext d
      simp only [Finset.mem_filter, Finset.mem_singleton]
      constructor
      · rintro ⟨hd, hdm⟩
        have hdp := hD d hd
        have : d ∣ Nat.gcd m P := Nat.dvd_gcd hdm hdp
        rw [hc] at this
        exact Nat.dvd_one.mp this
      · rintro rfl
        exact ⟨h1, one_dvd _⟩
    rw [this, Finset.sum_singleton, hw]
    norm_num
  · rw [if_neg hc]
    exact sq_nonneg _
