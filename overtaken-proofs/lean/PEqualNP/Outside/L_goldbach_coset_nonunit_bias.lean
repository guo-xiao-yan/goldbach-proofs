import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.ZMod.Basic


theorem PEqualNP.Outside.L_goldbach_coset_nonunit_bias :
    let w := fun k : ℕ => if k.Prime then Real.log (k:ℝ) else 0; let F := fun n q r : ℕ => (Finset.range (n+1)).filter (fun k => k % q=r); let A := fun n q r : ℕ => ∑ k ∈ F n q r, w k; ∀ n q r : ℕ, 0<q → r<q → ¬r.Coprime q → A n q r ≤ ∑ p ∈ q.primeFactors, Real.log (p:ℝ) := by
  intro w F A n q r hq hr hnc
  have hmem : ∀ k ∈ F n q r, k.Prime → k ∈ q.primeFactors := by
    intro k hk hkp
    have hkr : k % q = r := (Finset.mem_filter.mp hk).2
    rw [Nat.mem_primeFactors]
    refine ⟨hkp, ?_, hq.ne'⟩
    by_contra hdiv
    apply hnc
    rw [← hkr, ZMod.coprime_mod_iff_coprime]
    exact (Nat.Prime.coprime_iff_not_dvd hkp).mpr hdiv
  have h1 : A n q r = ∑ k ∈ (F n q r).filter Nat.Prime, Real.log (k : ℝ) := by
    show ∑ k ∈ F n q r, w k = _
    refine Eq.trans ?_ (Finset.sum_filter _ _).symm
    refine Finset.sum_congr rfl ?_
    intro k _
    simp only [w]
  rw [h1]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
  · intro k hk
    rw [Finset.mem_filter] at hk
    exact hmem k hk.1 hk.2
  · intro k hk _
    have hkp : k.Prime := (Nat.mem_primeFactors.mp hk).1
    exact Real.log_nonneg (by exact_mod_cast hkp.one_lt.le)
