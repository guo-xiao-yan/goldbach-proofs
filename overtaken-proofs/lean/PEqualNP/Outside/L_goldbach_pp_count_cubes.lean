import Mathlib.Data.Finset.Max
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Order.Interval.Finset.Nat

theorem PEqualNP.Outside.L_goldbach_pp_count_cubes :
    ∀ n : ℕ, let s := (Finset.range (n+1)).filter (fun p => p.Prime ∧ p^3≤n); s.card^3 ≤ n := by
  intro n s
  rcases s.eq_empty_or_nonempty with he | hne
  · rw [he]; simp
  · obtain ⟨q, hq, hmax⟩ : ∃ q ∈ s, ∀ x ∈ s, x ≤ q := ⟨s.max' hne, s.max'_mem hne, fun x hx => s.le_max' x hx⟩
    have hqs : q ^ 3 ≤ n := by
      have := hq
      simp only [s, Finset.mem_filter] at this
      exact this.2.2
    have hsub : s ⊆ Finset.Icc 1 q := by
      intro x hx
      have hx' := hx
      simp only [s, Finset.mem_filter] at hx'
      simp only [Finset.mem_Icc]
      exact ⟨hx'.2.1.one_lt.le, hmax x hx⟩
    have hc : s.card ≤ q := by
      have := Finset.card_le_card hsub
      simpa using this
    calc s.card ^ 3 ≤ q ^ 3 := Nat.pow_le_pow_left hc 3
      _ ≤ n := hqs
