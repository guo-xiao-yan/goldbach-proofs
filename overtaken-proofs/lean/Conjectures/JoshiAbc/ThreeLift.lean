import Mathlib

theorem Conjectures.JoshiAbc.ThreeLift :
    ∀ (G : Type) [AddCommGroup G] (C L : AddSubgroup G), L ≤ C → (∀ x : G, ∃ y ∈ C, x-y ∈ L) → C=⊤ := by
  intro G _ C L hL h
  rw [eq_top_iff]
  intro x _
  obtain ⟨y, hy, hxy⟩ := h x
  have := C.add_mem hy (hL hxy)
  simpa using this

