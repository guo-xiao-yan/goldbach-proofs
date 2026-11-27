import Mathlib

theorem Conjectures.Goldbach.DynCarryReflection :
    let W := fun (A B : Finset ℕ) (n : ℕ) => ((A ×ˢ B).filter (fun t => t.1+t.2=n)).card; ∀ (m n : ℕ) (A B : Finset ℕ), 2 ≤ m → n+2 ≤ m → (∀ a ∈ A, a < m) → (∀ b ∈ B, b < m) → W A B (n+m) = W (A.image (fun a => m-1-a)) (B.image (fun b => m-1-b)) (m-2-n) := by
  intro W m n A B hm hn hA hB
  simp only [W]
  symm
  apply Finset.card_bij (fun t _ => (m-1-t.1, m-1-t.2))
  · rintro ⟨a, b⟩ h
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_image] at h ⊢
    obtain ⟨⟨⟨x, hx, rfl⟩, ⟨y, hy, rfl⟩⟩, h2⟩ := h
    have := hA x hx
    have := hB y hy
    have e1 : m - 1 - (m - 1 - x) = x := by omega
    have e2 : m - 1 - (m - 1 - y) = y := by omega
    rw [e1, e2]
    exact ⟨⟨hx, hy⟩, by omega⟩
  · rintro ⟨a, b⟩ h ⟨c, d⟩ h' e
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_image, Prod.mk.injEq] at h h' e
    obtain ⟨⟨⟨x, hx, rfl⟩, ⟨y, hy, rfl⟩⟩, h2⟩ := h
    obtain ⟨⟨⟨x', hx', rfl⟩, ⟨y', hy', rfl⟩⟩, h2'⟩ := h'
    have := hA x hx
    have := hB y hy
    have := hA x' hx'
    have := hB y' hy'
    simp only [Prod.mk.injEq]
    omega
  · rintro ⟨a, b⟩ h
    simp only [Finset.mem_filter, Finset.mem_product] at h
    obtain ⟨⟨ha, hb⟩, h2⟩ := h
    have := hA a ha
    have := hB b hb
    refine ⟨(m-1-a, m-1-b), ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_image]
      refine ⟨⟨⟨a, ha, rfl⟩, ⟨b, hb, rfl⟩⟩, ?_⟩
      omega
    · simp only [Prod.mk.injEq]
      omega
