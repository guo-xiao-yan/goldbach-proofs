import Mathlib

private lemma sumsq_aux (m : ℕ) :
    ((Finset.Icc 1 m).sum (fun j => (j:ℝ)^2)) = (m:ℝ) * ((m:ℝ)+1) * (2*(m:ℝ)+1) / 6 := by
  induction m with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih]
    push_cast
    ring

theorem Conjectures.JoshiAbc.MeanSquare :
    ∀ m : ℕ, 0 < m → ((Finset.Icc 1 m).sum (fun j => (j:ℝ)^2))/(m:ℝ) = (2*(m:ℝ)+1)*(2*(m:ℝ)+2)/12 := by
  intro m hm
  have : (m:ℝ) ≠ 0 := by positivity
  rw [sumsq_aux]
  field_simp
  ring
