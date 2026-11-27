import Mathlib

theorem Conjectures.Goldbach.DynDeletionLoss :
    ∀ (A B D E : Finset ℕ) (t : ℕ), let r := fun (B' : Finset ℕ) (n : ℕ) => (A.filter (fun p => p≤n ∧ n-p ∈ B')).card; t * (E.filter (fun n => t ≤ r B n ∧ r (B \ D) n = 0)).card ≤ A.card * (B ∩ D).card := by
  intro A B D E t r
  set S := E.filter (fun n => t ≤ r B n ∧ r (B \ D) n = 0) with hS
  have h1 : ∀ n ∈ S, t ≤ ((A ×ˢ (B ∩ D)).filter (fun x => x.1 + x.2 = n)).card := by
    intro n hn
    rw [hS, Finset.mem_filter] at hn
    obtain ⟨_, ht, h0⟩ := hn
    refine ht.trans ?_
    show (A.filter (fun p => p ≤ n ∧ n - p ∈ B)).card ≤ _
    apply Finset.card_le_card_of_injOn (fun p => (p, n - p))
    · intro p hp
      simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_coe] at hp ⊢
      obtain ⟨hpA, hpn, hpB⟩ := hp
      have : n - p ∈ D := by
        by_contra hD
        have : p ∈ A.filter (fun p => p ≤ n ∧ n - p ∈ B \ D) :=
          Finset.mem_filter.2 ⟨hpA, hpn, Finset.mem_sdiff.2 ⟨hpB, hD⟩⟩
        have h0' : (A.filter (fun p => p ≤ n ∧ n - p ∈ B \ D)).card = 0 := h0
        rw [Finset.card_eq_zero] at h0'
        rw [h0'] at this
        exact absurd this (Finset.notMem_empty _)
      simp only [Finset.mem_product, Finset.mem_inter]
      exact ⟨⟨hpA, hpB, this⟩, by omega⟩
    · intro a _ b _ h
      exact (Prod.mk.inj h).1
  have h2 : ∑ n ∈ S, ((A ×ˢ (B ∩ D)).filter (fun x => x.1 + x.2 = n)).card
      = ((A ×ˢ (B ∩ D)).filter (fun x => x.1 + x.2 ∈ S)).card := by
    rw [Finset.card_eq_sum_card_fiberwise (s := (A ×ˢ (B ∩ D)).filter (fun x => x.1 + x.2 ∈ S)) (f := fun x : ℕ × ℕ => x.1 + x.2) (t := S)
      (fun x hx => (Finset.mem_filter.1 hx).2)]
    apply Finset.sum_congr rfl
    intro n hn
    congr 1
    ext x
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨h, rfl⟩; exact ⟨⟨h, hn⟩, rfl⟩
    · rintro ⟨⟨h, _⟩, rfl⟩; exact ⟨h, rfl⟩
  calc t * S.card = ∑ _n ∈ S, t := by simp [mul_comm]
    _ ≤ ∑ n ∈ S, ((A ×ˢ (B ∩ D)).filter (fun x => x.1 + x.2 = n)).card := Finset.sum_le_sum h1
    _ = _ := h2
    _ ≤ (A ×ˢ (B ∩ D)).card := Finset.card_filter_le _ _
    _ = A.card * (B ∩ D).card := Finset.card_product _ _
