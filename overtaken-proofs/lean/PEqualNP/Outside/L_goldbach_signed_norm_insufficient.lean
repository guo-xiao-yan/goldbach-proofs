import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

theorem PEqualNP.Outside.L_goldbach_signed_norm_insufficient :
    ∀ M : ℝ, 0<M → ∃ a b u v : ℝ, max |a| |b|=M ∧ u^2+v^2=1 ∧ a*u^2+b*v^2= -M := by
  intro M hM
  refine ⟨-M, 0, 1, 0, ?_, by norm_num, by norm_num⟩
  simp [abs_of_pos hM, hM.le]
