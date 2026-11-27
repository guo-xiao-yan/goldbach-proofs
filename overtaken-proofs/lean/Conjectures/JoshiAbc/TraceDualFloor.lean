import Mathlib

theorem Conjectures.JoshiAbc.TraceDualFloor :
    ∀ (n d e t : ℤ), 0 < e → (∀ a : ℤ, a ≤ t ↔ -d ≤ n-e*a) → t = (n+d)/e := by
  intro n d e t he h
  apply le_antisymm
  · rw [Int.le_ediv_iff_mul_le he]
    have := (h t).1 le_rfl
    linarith
  · apply (h _).2
    have := (Int.le_ediv_iff_mul_le he).1 (le_refl ((n+d)/e))
    linarith
