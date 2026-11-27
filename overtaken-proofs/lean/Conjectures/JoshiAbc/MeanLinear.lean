import Mathlib

theorem Conjectures.JoshiAbc.MeanLinear :
    ∀ m : ℕ, 0 < m → ((Finset.Icc 1 m).sum (fun j => (j:ℝ)))/(m:ℝ) = ((2*(m:ℝ)+1)+1)/4 := by
  intro m hm
  have h : ∀ n : ℕ, ((Finset.Icc 1 n).sum (fun j => (j:ℝ))) = (n:ℝ) * (n+1) / 2 := by
    intro n
    induction n with
    | zero => simp
    | succ k ih =>
      rw [Finset.sum_Icc_succ_top (by omega), ih]
      push_cast; ring
  rw [h]
  have : (m:ℝ) ≠ 0 := by positivity
  field_simp
  ring
