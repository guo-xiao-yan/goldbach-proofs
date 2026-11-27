import Mathlib

theorem Conjectures.Goldbach.DynCarryEdgeBudget :
    let W := fun (A B : Finset ℕ) (n : ℕ) => ((A ×ˢ B).filter (fun t => t.1+t.2=n)).card; ∀ (m n : ℕ) (A B : Finset ℕ), n < m → (∀ a ∈ A, a < m) → (∀ b ∈ B, b < m) → W A B (n+m) ≤ min ((A.filter (fun a => n < a)).card) ((B.filter (fun b => n < b)).card) := by
  intro W m n A B hnm hA hB
  simp only [W]
  apply le_min
  · apply Finset.card_le_card_of_injOn (fun t => t.1)
    · intro t ht
      simp only [Finset.coe_filter, Finset.mem_product, Set.mem_setOf_eq] at ht
      have := hB t.2 ht.1.2
      simp only [Finset.coe_filter, Set.mem_setOf_eq]
      exact ⟨ht.1.1, by omega⟩
    · intro s hs t ht h
      simp only [Finset.coe_filter, Set.mem_setOf_eq] at hs ht
      ext <;> simp at h ⊢ <;> omega
  · apply Finset.card_le_card_of_injOn (fun t => t.2)
    · intro t ht
      simp only [Finset.coe_filter, Finset.mem_product, Set.mem_setOf_eq] at ht
      have := hA t.1 ht.1.1
      simp only [Finset.coe_filter, Set.mem_setOf_eq]
      exact ⟨ht.1.2, by omega⟩
    · intro s hs t ht h
      simp only [Finset.coe_filter, Set.mem_setOf_eq] at hs ht
      ext <;> simp at h ⊢ <;> omega
