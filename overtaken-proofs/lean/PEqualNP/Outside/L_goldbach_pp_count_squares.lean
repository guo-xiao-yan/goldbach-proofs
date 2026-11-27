import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.BigOperators.Intervals

theorem PEqualNP.Outside.L_goldbach_pp_count_squares :
    ∀ n : ℕ, ((Finset.range (n+1)).filter (fun m => (Nat.sqrt m).Prime ∧ (Nat.sqrt m)^2=m)).card ≤ Nat.sqrt n := by
  intro n
  have h : ((Finset.range (n+1)).filter (fun m => (Nat.sqrt m).Prime ∧ (Nat.sqrt m)^2=m)).card ≤ (Finset.Icc 1 (Nat.sqrt n)).card := by
    apply Finset.card_le_card_of_injOn Nat.sqrt
    · intro m hm
      simp only [Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq] at hm
      simp only [Finset.coe_Icc, Set.mem_Icc]
      exact ⟨hm.2.1.one_lt.le, Nat.sqrt_le_sqrt (by omega)⟩
    · intro a ha b hb hab
      simp only [Finset.coe_filter, Set.mem_setOf_eq] at ha hb
      rw [← ha.2.2, ← hb.2.2]
      rw [hab]
  simpa using h
