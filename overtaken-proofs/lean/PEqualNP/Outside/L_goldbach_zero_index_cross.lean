import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.BigOperators.Fin

theorem PEqualNP.Outside.L_goldbach_zero_index_cross :
    ∀ (m : ℕ) (u : Fin m → ℂ), (∑ j, u j) * (∑ j, star (u j)) - (∑ j, u j * star (u j)) = ∑ j, ∑ l ∈ Finset.univ.erase j, u j * star (u l) := by
  intro m u
  rw [Finset.sum_mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.add_sum_erase Finset.univ (fun l => u j * star (u l)) (Finset.mem_univ j)]
  ring
