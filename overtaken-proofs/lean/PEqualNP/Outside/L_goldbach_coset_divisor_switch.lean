import Mathlib.NumberTheory.Divisors
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

theorem PEqualNP.Outside.L_goldbach_coset_divisor_switch :
    ∀ d Q : ℕ, 0<d → (∑ q ∈ (Finset.Ioc Q (2*Q)).filter (fun q => q∣d), (q:ℝ)) = (d:ℝ)* ∑ h ∈ d.divisors.filter (fun h => Q*h<d ∧ d≤2*Q*h), 1/(h:ℝ) := by
  intro d Q hd
  rw [Finset.mul_sum]
  refine Finset.sum_nbij' (fun q => d / q) (fun h => d / h) ?_ ?_ ?_ ?_ ?_
  · intro q hq
    simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_coe, Nat.mem_divisors] at hq ⊢
    obtain ⟨⟨h1, h2⟩, c, hc⟩ := hq
    have hq0 : 0 < q := by
      rcases Nat.eq_zero_or_pos q with h | h
      · subst h; simp at hc; omega
      · exact h
    have hc0 : 0 < c := by
      rcases Nat.eq_zero_or_pos c with h | h
      · subst h; simp at hc; omega
      · exact h
    have e : d / q = c := by rw [hc]; exact Nat.mul_div_cancel_left c hq0
    rw [e]
    refine ⟨⟨⟨q, by rw [hc]; ring⟩, by omega⟩, ?_, ?_⟩
    · rw [hc]; nlinarith
    · rw [hc]; nlinarith
  · intro h hh
    simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_coe, Nat.mem_divisors] at hh ⊢
    obtain ⟨⟨⟨c, hc⟩, _⟩, h1, h2⟩ := hh
    have hh0 : 0 < h := by
      rcases Nat.eq_zero_or_pos h with e | e
      · subst e; simp at hc; omega
      · exact e
    have e : d / h = c := by rw [hc]; exact Nat.mul_div_cancel_left c hh0
    rw [e]
    refine ⟨⟨?_, ?_⟩, ⟨h, by rw [hc]; ring⟩⟩
    · rw [hc] at h1; nlinarith
    · rw [hc] at h2; nlinarith
  · intro q hq
    simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_coe] at hq
    obtain ⟨⟨h1, h2⟩, c, hc⟩ := hq
    have hq0 : 0 < q := by
      rcases Nat.eq_zero_or_pos q with h | h
      · subst h; simp at hc; omega
      · exact h
    have e : d / q = c := by rw [hc]; exact Nat.mul_div_cancel_left c hq0
    have hc0 : 0 < c := by
      rcases Nat.eq_zero_or_pos c with h | h
      · subst h; simp at hc; omega
      · exact h
    simp only [e]
    rw [hc]; exact Nat.mul_div_cancel q hc0
  · intro h hh
    simp only [Finset.mem_filter, Nat.mem_divisors, Finset.mem_coe] at hh
    obtain ⟨⟨⟨c, hc⟩, _⟩, _, _⟩ := hh
    have hh0 : 0 < h := by
      rcases Nat.eq_zero_or_pos h with e | e
      · subst e; simp at hc; omega
      · exact e
    have e : d / h = c := by rw [hc]; exact Nat.mul_div_cancel_left c hh0
    simp only [e]
    rw [hc]; exact Nat.mul_div_cancel h (by
      rcases Nat.eq_zero_or_pos c with e | e
      · subst e; simp at hc; omega
      · exact e)
  · intro q hq
    simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_coe] at hq
    obtain ⟨⟨h1, h2⟩, c, hc⟩ := hq
    have hq0 : 0 < q := by
      rcases Nat.eq_zero_or_pos q with h | h
      · subst h; simp at hc; omega
      · exact h
    have hc0 : 0 < c := by
      rcases Nat.eq_zero_or_pos c with h | h
      · subst h; simp at hc; omega
      · exact h
    have e : d / q = c := by rw [hc]; exact Nat.mul_div_cancel_left c hq0
    rw [e, hc]
    have : (c:ℝ) ≠ 0 := by exact_mod_cast hc0.ne'
    push_cast
    field_simp
