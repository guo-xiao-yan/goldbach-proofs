import Mathlib.NumberTheory.Divisors
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic.Ring

theorem PEqualNP.Outside.L_goldbach_sieve_divisor_expansion :
    let S := fun n : ℕ => ∏ p ∈ n.primeFactors.filter (fun p => 2<p), (1+1/((p:ℝ)-2)); ∀ n : ℕ, (S n)^2 = ∑ t ∈ (n.primeFactors.filter (fun p => 2<p)).powerset, ∏ p ∈ t, ((1+1/((p:ℝ)-2))^2-1) := by
  intro S n
  show (∏ p ∈ n.primeFactors.filter (fun p => 2<p), (1+1/((p:ℝ)-2)))^2 = _
  rw [← Finset.prod_pow, ← Finset.prod_one_add]
  refine Finset.prod_congr rfl (fun p _ => by ring)
