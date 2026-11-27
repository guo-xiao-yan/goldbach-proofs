import Mathlib

theorem Conjectures.JoshiAbc.CodifferentRounding :
    ∀ (n d : ℤ) (e : ℕ), 0 < e → ((n-d)+d)/(e:ℤ) = n/(e:ℤ) ∧ 0 ≤ (⌈(n:ℝ)/e⌉:ℝ)-(n:ℝ)/e ∧ (⌈(n:ℝ)/e⌉:ℝ)-(n:ℝ)/e < 1 := by
  intro n d e _
  refine ⟨by simp, ?_, ?_⟩
  · linarith [Int.le_ceil ((n:ℝ)/e)]
  · linarith [Int.ceil_lt_add_one ((n:ℝ)/e)]
