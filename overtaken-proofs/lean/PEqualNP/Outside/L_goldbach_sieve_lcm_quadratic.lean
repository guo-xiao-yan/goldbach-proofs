import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Real.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Linarith

theorem PEqualNP.Outside.L_goldbach_sieve_lcm_quadratic :
    ∀ (x : ℕ) (m : ℕ → ℕ) (D : Finset ℕ) (w : ℕ → ℝ), (∑ k ∈ Finset.range x, (∑ d ∈ D.filter (fun d => d∣m k), w d)^2) = ∑ a ∈ D, ∑ b ∈ D, w a*w b*(((Finset.range x).filter (fun k => Nat.lcm a b∣m k)).card : ℝ) := by
  intro x m D w
  have h1 : ∀ k, (∑ d ∈ D.filter (fun d => d ∣ m k), w d)^2
      = ∑ a ∈ D, ∑ b ∈ D, if Nat.lcm a b ∣ m k then w a * w b else 0 := by
    intro k
    rw [Finset.sum_filter, sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
    by_cases ha : a ∣ m k <;> by_cases hb : b ∣ m k <;>
      simp [Nat.lcm_dvd_iff, ha, hb]
  simp_rw [h1]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [Finset.card_filter]
  push_cast
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  split_ifs <;> simp
