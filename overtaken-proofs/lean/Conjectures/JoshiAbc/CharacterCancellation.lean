import Mathlib

theorem Conjectures.JoshiAbc.CharacterCancellation :
    ∀ (p n : ℕ) [Fact p.Prime] (H : Submodule (ZMod p) (Fin n → ZMod p)) [Fintype H] (χ : (Fin n → ZMod p) → ℂ) (b : Fin n → ZMod p), (∀ x y, χ (x+y)=χ x*χ y) → (∃ h : H, χ h.val ≠ 1) → (∑ h : H, χ (b+h.val)) = 0 := by
  intro p n _ H _ χ b hχ ⟨h0, hh0⟩
  have key : (∑ h : H, χ (b+h.val)) = χ h0.val * (∑ h : H, χ (b+h.val)) := by
    rw [Finset.mul_sum]
    refine (Fintype.sum_equiv (Equiv.addLeft h0) _ _ ?_).symm
    intro h
    simp only [Equiv.coe_addLeft, AddMemClass.coe_add]
    rw [← hχ]; congr 1; abel
  have : (χ h0.val - 1) * (∑ h : H, χ (b+h.val)) = 0 := by
    rw [sub_mul, ← key]; ring
  rcases mul_eq_zero.mp this with h | h
  · exact absurd (sub_eq_zero.mp h) hh0
  · exact h
