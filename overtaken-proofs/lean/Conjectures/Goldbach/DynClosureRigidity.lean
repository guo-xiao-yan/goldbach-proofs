import Mathlib

theorem Conjectures.Goldbach.DynClosureRigidity :
    ∀ (A B : Set ℤ), (∀ x ∈ A, 0 < x) → (∀ x ∈ B, x < 0) → ∀ (P Q : Set ℤ), P.Nonempty → Q.Nonempty → (∀ F : Finset ℤ, ∃ k : ℤ, ∀ i ∈ F, (i ∈ P ↔ i+k ∈ A) ∧ (i ∈ Q ↔ i+k ∈ B)) → ∃ k : ℤ, ∀ i : ℤ, (i ∈ P ↔ i+k ∈ A) ∧ (i ∈ Q ↔ i+k ∈ B) := by
  intro A B hA hB P Q ⟨p, hp⟩ ⟨q, hq⟩ h
  by_contra hc
  have hc' : ∀ k : ℤ, ∃ i : ℤ, ¬((i ∈ P ↔ i+k ∈ A) ∧ (i ∈ Q ↔ i+k ∈ B)) := fun k => by
    by_contra hh
    exact hc ⟨k, fun i => by
      by_contra hi
      exact hh ⟨i, hi⟩⟩
  choose w hw using hc'
  obtain ⟨k, hk⟩ := h ({p, q} ∪ (Finset.Ioo (-p) (-q)).image w)
  have hpk := (hk p (by simp)).1.1 hp
  have hqk := (hk q (by simp)).2.1 hq
  have h1 := hA _ hpk
  have h2 := hB _ hqk
  have hmem : k ∈ Finset.Ioo (-p) (-q) := by
    simp only [Finset.mem_Ioo]; omega
  have := hk (w k) (by
    apply Finset.mem_union_right
    exact Finset.mem_image_of_mem w hmem)
  exact hw k this
