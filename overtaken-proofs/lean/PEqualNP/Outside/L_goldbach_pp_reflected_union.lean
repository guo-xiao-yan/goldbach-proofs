import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.BigOperators.Intervals

theorem PEqualNP.Outside.L_goldbach_pp_reflected_union :
    ∀ (n : ℕ) (s : Finset ℕ), ((Finset.range (n+1)).filter (fun k => k∈s ∨ n-k∈s)).card ≤ 2*s.card := by
  intro n s
  have hsub : ((Finset.range (n+1)).filter (fun k => k∈s ∨ n-k∈s)) ⊆ s ∪ s.image (fun j => n - j) := by
    intro k hk
    simp only [Finset.mem_filter, Finset.mem_range] at hk
    simp only [Finset.mem_union, Finset.mem_image]
    rcases hk.2 with h | h
    · exact Or.inl h
    · exact Or.inr ⟨n - k, h, by omega⟩
  calc _ ≤ (s ∪ s.image (fun j => n - j)).card := Finset.card_le_card hsub
    _ ≤ s.card + (s.image (fun j => n - j)).card := Finset.card_union_le _ _
    _ ≤ s.card + s.card := Nat.add_le_add_left Finset.card_image_le _
    _ = 2 * s.card := by omega
