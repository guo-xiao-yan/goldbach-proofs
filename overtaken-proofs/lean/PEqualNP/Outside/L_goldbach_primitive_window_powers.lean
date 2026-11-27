import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Data.Finset.Max

theorem PEqualNP.Outside.L_goldbach_primitive_window_powers :
    let B := fun n p : ℕ => (Finset.Icc 1 (Nat.log 2 n)).filter (fun a => n≤3*p^a ∧ 3*p^a≤2*n); ∀ n p : ℕ, 0<n → p.Prime → (B n p).card ≤ (if p=2 then 2 else 1) := by
  intro B n p hn hp
  have hp2 := hp.two_le
  have key : ∀ a b : ℕ, a < b → n ≤ 3*p^a → 3*p^b ≤ 2*n → p = 2 ∧ b = a + 1 := by
    intro a b hab h1 h2
    have h3 : p^(a+1) ≤ p^b := Nat.pow_le_pow_right (by omega) hab
    have h4 : p^(a+1) = p * p^a := by ring
    have hpa : 0 < p^a := Nat.pow_pos (by omega)
    have h5 : 2 * p^a ≤ p * p^a := Nat.mul_le_mul_right _ hp2
    have h6 : p * p^a ≤ p^b := by omega
    have h7 : 3 * (p * p^a) ≤ 3 * p^b := by omega
    have h8 : p = 2 := by
      by_contra hne
      have : 3 ≤ p := by omega
      have h9 : 3 * p^a ≤ p * p^a := Nat.mul_le_mul_right _ this
      nlinarith
    subst h8
    refine ⟨rfl, ?_⟩
    by_contra hne
    have h10 : 2^(a+2) ≤ 2^b := Nat.pow_le_pow_right (by omega) (by omega)
    have h11 : 2^(a+2) = 4 * 2^a := by ring
    have : 2 ^ (a+1) = 2 * 2^a := by ring
    omega
  have mem : ∀ a, a ∈ B n p → n ≤ 3*p^a ∧ 3*p^a ≤ 2*n := by
    intro a ha
    simp only [B, Finset.mem_filter] at ha
    exact ha.2
  have pair : ∀ a b, a ∈ B n p → b ∈ B n p → a < b → p = 2 ∧ b = a + 1 := by
    intro a b ha hb hab
    exact key a b hab (mem a ha).1 (mem b hb).2
  by_cases h2 : p = 2
  · rw [if_pos h2]
    by_cases hne : (B n p).Nonempty
    · set a0 := (B n p).min' hne with ha0
      have ha0m : a0 ∈ B n p := Finset.min'_mem _ _
      have hsub : B n p ⊆ {a0, a0 + 1} := by
        intro b hb
        have hle : a0 ≤ b := Finset.min'_le _ _ hb
        rcases Nat.eq_or_lt_of_le hle with h | h
        · simp [h]
        · have := (pair a0 b ha0m hb h).2
          simp [this]
      exact (Finset.card_le_card hsub).trans Finset.card_le_two
    · rw [Finset.not_nonempty_iff_eq_empty.mp hne]; simp
  · rw [if_neg h2]
    apply Finset.card_le_one.mpr
    intro a ha b hb
    rcases lt_trichotomy a b with h | h | h
    · exact absurd (pair a b ha hb h).1 h2
    · exact h
    · exact absurd (pair b a hb ha h).1 h2
