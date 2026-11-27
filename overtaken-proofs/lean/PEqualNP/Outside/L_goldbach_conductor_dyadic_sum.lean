import Mathlib.Data.Nat.Totient
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

private theorem geom_aux (m : ℕ) :
    ∑ j ∈ Finset.Icc 1 m, ((1:ℝ)/2)^j = 1 - ((1:ℝ)/2)^m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih]
    ring

private theorem term_aux (m j : ℕ) (hj : j ∈ Finset.Icc 1 m) :
    (if 2 < 2^(m+2)/2^j then (Nat.totient (2^(m+2)/2^j) : ℝ)/Nat.totient (2^(m+2)) else 0)
      = ((1:ℝ)/2)^j := by
  obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hj
  have hq : 2^(m+2)/2^j = 2^(m+2-j) := Nat.pow_div (by omega) (by norm_num)
  have hk : m + 2 - j = (m + 1 - j) + 1 := by omega
  have hbig : 2 < 2^(m+2-j) := by
    have : 2^2 ≤ 2^(m+2-j) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  rw [hq, if_pos hbig, hk, Nat.totient_prime_pow_succ Nat.prime_two,
    show m + 2 = (m + 1) + 1 by ring, Nat.totient_prime_pow_succ Nat.prime_two]
  have e : (2:ℝ)^(m+1) = 2^(m+1-j) * 2^j := by
    rw [← pow_add]
    congr 1
    omega
  push_cast
  simp only [mul_one, Nat.cast_ofNat]
  rw [e, one_div, inv_pow]
  field_simp

theorem PEqualNP.Outside.L_goldbach_conductor_dyadic_sum :
    ∀ k : ℕ, 2≤k → (∑ j ∈ Finset.Icc 1 k, if 2 < 2^k/2^j then (Nat.totient (2^k/2^j) : ℝ)/Nat.totient (2^k) else 0) = 1-4/(2:ℝ)^k := by
  intro k hk
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 2 := ⟨k - 2, by omega⟩
  rw [Finset.sum_Icc_succ_top (by omega), Finset.sum_Icc_succ_top (by omega),
    Finset.sum_congr rfl (term_aux m), geom_aux]
  have h1 : ¬ (2 < 2^(m+2)/2^(m+1)) := by
    rw [Nat.pow_div (by omega) (by norm_num)]
    norm_num
  have h2 : ¬ (2 < 2^(m+2)/2^(m+1+1)) := by
    rw [Nat.pow_div (by omega) (by norm_num)]
    norm_num
  rw [if_neg h1, if_neg h2, one_div, inv_pow]
  field_simp
  ring
