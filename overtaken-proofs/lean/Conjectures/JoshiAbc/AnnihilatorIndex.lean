import Mathlib

theorem Conjectures.JoshiAbc.AnnihilatorIndex :
    ∀ (p n : ℕ) [Fact p.Prime] (H : Submodule (ZMod p) (Fin n → ZMod p)), Nat.card H.dualAnnihilator = Nat.card ((Fin n → ZMod p) ⧸ H) := by
  intro p n _ H
  have e1 := (Submodule.dualQuotEquivDualAnnihilator H).toEquiv
  have e2 := (Module.finBasis (ZMod p) ((Fin n → ZMod p) ⧸ H)).toDualEquiv.toEquiv
  rw [← Nat.card_congr e1, Nat.card_congr e2.symm]
