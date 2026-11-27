import Mathlib.NumberTheory.Divisors
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Cast.Order.Field
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

private theorem card_le_aux (x d : ℕ) (hd : d ∈ Finset.Icc 1 x) :
    (((Finset.Icc 1 x).filter (fun n => d ∣ n)).card : ℝ) ≤ (x : ℝ) / d := by
  have h1 : (Finset.Icc 1 x).filter (fun n => d ∣ n) = (Finset.Ioc 0 x).filter (fun n => d ∣ n) := by
    ext n; simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc]; omega
  rw [h1, Nat.Ioc_filter_dvd_card_eq_div]
  have hd0 : (0 : ℝ) < d := by
    have := (Finset.mem_Icc.mp hd).1
    exact_mod_cast this
  rw [le_div_iff₀ hd0]
  exact_mod_cast Nat.div_mul_le_self x d

theorem PEqualNP.Outside.L_goldbach_sieve_squarefree_average :
    ∀ (x : ℕ) (b : ℕ → ℝ), (∀ d, 0≤b d) → (∑ n ∈ Finset.Icc 1 x, ∑ d ∈ n.divisors, b d) ≤ (x:ℝ)*∑ d ∈ Finset.Icc 1 x, b d/(d:ℝ) := by
  intro x b hb
  have hswap : (∑ n ∈ Finset.Icc 1 x, ∑ d ∈ n.divisors, b d)
      = ∑ d ∈ Finset.Icc 1 x, ∑ n ∈ (Finset.Icc 1 x).filter (fun n => d ∣ n), b d := by
    refine Finset.sum_comm' ?_
    intro n d
    simp only [Finset.mem_Icc, Finset.mem_filter, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨h1, hn⟩, hd, h0⟩
      have hle := Nat.le_of_dvd (by omega) hd
      have hpos : 0 < d := Nat.pos_of_dvd_of_pos hd (by omega)
      exact ⟨⟨⟨h1, hn⟩, hd⟩, hpos, by omega⟩
    · rintro ⟨⟨⟨h1, hn⟩, hd⟩, _, _⟩
      exact ⟨⟨h1, hn⟩, hd, by omega⟩
  rw [hswap, Finset.mul_sum]
  refine Finset.sum_le_sum (fun d hd => ?_)
  rw [Finset.sum_const, nsmul_eq_mul]
  have := card_le_aux x d hd
  have hbd := hb d
  calc (((Finset.Icc 1 x).filter (fun n => d ∣ n)).card : ℝ) * b d ≤ ((x : ℝ) / d) * b d :=
        mul_le_mul_of_nonneg_right this hbd
    _ = (x : ℝ) * (b d / d) := by ring
