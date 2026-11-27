import Mathlib

theorem Conjectures.JoshiAbc.FiniteAffineTransform :
    ∀ (G : Type) [AddCommGroup G] [Fintype G] (H : AddSubgroup G) [Fintype H] (b : G) (χ : AddChar G ℂ) [Decidable (∀ h : H, χ h.val=1)], (∑ h : H, χ (b+h.val)) = if (∀ h : H, χ h.val=1) then (Nat.card H:ℂ)*χ b else 0 := by
  classical
  intro G _ _ H _ b χ _
  let ψ : AddChar H ℂ := χ.compAddMonoidHom H.subtype
  have h1 : (∑ h : H, χ (b+h.val)) = χ b * ∑ h : H, ψ h := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun h _ => ?_
    rw [AddChar.map_add_eq_mul]
    rfl
  have h2 := AddChar.sum_eq_ite ψ
  have h3 : (ψ = 0) ↔ (∀ h : H, χ h.val = 1) := by
    constructor
    · intro h x
      have := DFunLike.congr_fun h x
      simpa [ψ] using this
    · intro h
      ext x
      simpa [ψ] using h x
  rw [h1, h2]
  by_cases hc : ∀ h : H, χ h.val = 1
  · rw [if_pos (h3.2 hc), if_pos hc, mul_comm]
    simp [Nat.card_eq_fintype_card]
  · rw [if_neg (fun h => hc (h3.1 h)), if_neg hc]
    simp
