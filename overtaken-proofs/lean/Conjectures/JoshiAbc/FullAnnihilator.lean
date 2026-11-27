import Mathlib

theorem Conjectures.JoshiAbc.FullAnnihilator :
    ∀ (G : Type) [AddCommGroup G] [Fintype G] (H : AddSubgroup G), Nat.card {χ : AddChar G ℂ // ∀ h : H, χ h.val=1} = H.index := by
  intro G _ _ H
  classical
  let f : AddChar (G ⧸ H) ℂ → {χ : AddChar G ℂ // ∀ h : H, χ h.val=1} := fun ψ =>
    ⟨ψ.compAddMonoidHom (QuotientAddGroup.mk' H), fun h => by
      have h0 : QuotientAddGroup.mk' H h.val = 0 := (QuotientAddGroup.eq_zero_iff _).mpr h.2
      show ψ (QuotientAddGroup.mk' H h.val) = 1
      rw [h0, AddChar.map_zero_eq_one]⟩
  have hf : Function.Bijective f := by
    constructor
    · intro ψ₁ ψ₂ h
      ext q
      obtain ⟨g, rfl⟩ := QuotientAddGroup.mk_surjective q
      have := congrArg (fun χ : {χ : AddChar G ℂ // ∀ h : H, χ h.val=1} => χ.1 g) h
      simpa [f] using this
    · rintro ⟨χ, hχ⟩
      have hresp : ∀ a b : G, QuotientAddGroup.leftRel H a b → χ a = χ b := by
        intro a b hab
        have hmem : -a + b ∈ H := QuotientAddGroup.leftRel_apply.mp hab
        have h2 : χ (-a + b) = 1 := hχ ⟨-a + b, hmem⟩
        have e : χ b = χ a * χ (-a + b) := by rw [← AddChar.map_add_eq_mul]; congr 1; abel
        rw [e, h2, mul_one]
      refine ⟨⟨fun q => Quotient.liftOn' q χ hresp, ?_, ?_⟩, ?_⟩
      · exact (by simp [AddChar.map_zero_eq_one] : χ 0 = 1)
      · intro x y
        induction x using Quotient.inductionOn'
        induction y using Quotient.inductionOn'
        exact AddChar.map_add_eq_mul χ _ _
      · apply Subtype.ext
        ext g
        rfl
  have h1 : Nat.card (AddChar (G ⧸ H) ℂ) = Nat.card {χ : AddChar G ℂ // ∀ h : H, χ h.val=1} :=
    Nat.card_eq_of_bijective f hf
  rw [← h1]
  have : Fintype (G ⧸ H) := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card, AddChar.card_eq]
  exact Nat.card_eq_fintype_card.symm
