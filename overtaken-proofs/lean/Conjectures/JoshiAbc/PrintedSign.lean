import Mathlib

theorem Conjectures.JoshiAbc.PrintedSign :
    ∀ (n : ℕ) (a : Fin (n+1) → ℝ) (m V : ℝ), 0 < m → (∀ i, 0 < a i ∧ a i < 1) → -|V|/m < -∑ i, Real.log (a i) := by
  intro n a m V hm ha
  have h1 : ∑ i, Real.log (a i) < 0 :=
    Finset.sum_neg (fun i _ => Real.log_neg (ha i).1 (ha i).2) Finset.univ_nonempty
  have h2 : -|V|/m ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by simp) hm.le
  linarith
