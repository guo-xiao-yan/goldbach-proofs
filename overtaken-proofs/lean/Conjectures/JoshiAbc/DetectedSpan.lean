import Mathlib

private theorem ann_index :
    ∀ (p n : ℕ) [Fact p.Prime] (H : Submodule (ZMod p) (Fin n → ZMod p)), Nat.card H.dualAnnihilator = Nat.card ((Fin n → ZMod p) ⧸ H) := by
  intro p n _ H
  have e1 := (Submodule.dualQuotEquivDualAnnihilator H).toEquiv
  have e2 := (Module.finBasis (ZMod p) ((Fin n → ZMod p) ⧸ H)).toDualEquiv.toEquiv
  rw [← Nat.card_congr e1, Nat.card_congr e2.symm]

theorem Conjectures.JoshiAbc.DetectedSpan :
    ∀ (p n : ℕ) [Fact p.Prime] (S : Set (Fin n → ZMod p)) (M : ℕ), Nat.card {f : Module.Dual (ZMod p) (Fin n → ZMod p) // ∀ v ∈ S, f v=0} ≤ M → Nat.card ((Fin n → ZMod p) ⧸ Submodule.span (ZMod p) S) ≤ M := by
  intro p n _ S M h
  rw [← ann_index p n]
  have : Nat.card {f : Module.Dual (ZMod p) (Fin n → ZMod p) // ∀ v ∈ S, f v=0} = Nat.card (Submodule.span (ZMod p) S).dualAnnihilator := by
    apply Nat.card_congr
    refine Equiv.subtypeEquivRight ?_
    intro f
    rw [Submodule.mem_dualAnnihilator]
    constructor
    · intro hf w hw
      induction hw using Submodule.span_induction with
      | mem x hx => exact hf x hx
      | zero => simp
      | add x y _ _ hx hy => simp [hx, hy]
      | smul a x _ hx => simp [hx]
    · intro hf v hv
      exact hf v (Submodule.subset_span hv)
  omega
