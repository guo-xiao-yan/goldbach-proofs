import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.ZMod.Basic

private theorem aux (n q r : ℕ) (hq : 0 < q) (hnc : ¬ r.Coprime q) :
    ∑ k ∈ (Finset.range (n+1)).filter (fun k => k % q = r),
      (if k.Prime then Real.log (k : ℝ) else 0)
      ≤ ∑ p ∈ q.primeFactors.filter (fun p => p % q = r), Real.log (p : ℝ) := by
  calc _ = ∑ k ∈ ((Finset.range (n+1)).filter (fun k => k % q = r)).filter Nat.Prime,
          Real.log (k : ℝ) := (Finset.sum_filter _ _).symm
    _ ≤ _ := by
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
      · intro k hk
        rw [Finset.mem_filter, Finset.mem_filter] at hk
        obtain ⟨⟨_, hkr⟩, hkp⟩ := hk
        rw [Finset.mem_filter, Nat.mem_primeFactors]
        refine ⟨⟨hkp, ?_, hq.ne'⟩, hkr⟩
        by_contra hdiv
        apply hnc
        rw [← hkr, ZMod.coprime_mod_iff_coprime]
        exact (Nat.Prime.coprime_iff_not_dvd hkp).mpr hdiv
      · intro k hk _
        have hkp : k.Prime := (Nat.mem_primeFactors.mp (Finset.mem_filter.mp hk).1).1
        exact Real.log_nonneg (by exact_mod_cast hkp.one_lt.le)


theorem PEqualNP.Outside.L_goldbach_coset_nonunit_l2 :
    let F := fun n q r : ℕ => (Finset.range (n+1)).filter (fun k => k % q=r); let w := fun k : ℕ => if k.Prime then Real.log (k:ℝ) else 0; let A := fun n q r : ℕ => ∑ k ∈ F n q r, w k; ∀ n q : ℕ, 0<q → (∑ r ∈ (Finset.range q).filter (fun r => ¬r.Coprime q), (A n q r)^2) ≤ (∑ p ∈ q.primeFactors, Real.log (p:ℝ))^2 := by
  intro F w A n q hq
  have hA : ∀ r ∈ (Finset.range q).filter (fun r => ¬r.Coprime q),
      A n q r ≤ ∑ p ∈ q.primeFactors.filter (fun p => p % q = r), Real.log (p : ℝ) := by
    intro r hr
    have hnc : ¬ r.Coprime q := (Finset.mem_filter.mp hr).2
    exact aux n q r hq hnc
  have hA0 : ∀ r, 0 ≤ A n q r := by
    intro r
    refine Finset.sum_nonneg ?_
    intro k _
    simp only [w]
    split_ifs with h
    · exact Real.log_nonneg (by exact_mod_cast h.one_lt.le)
    · exact le_rfl
  have hnn : ∀ p ∈ q.primeFactors, 0 ≤ Real.log (p : ℝ) := by
    intro k hk
    have hkp : k.Prime := (Nat.mem_primeFactors.mp hk).1
    exact Real.log_nonneg (by exact_mod_cast hkp.one_lt.le)
  have hS : ∀ r, 0 ≤ ∑ p ∈ q.primeFactors.filter (fun p => p % q = r), Real.log (p : ℝ) := by
    intro r
    exact Finset.sum_nonneg (fun p hp => hnn p (Finset.mem_filter.mp hp).1)
  calc (∑ r ∈ (Finset.range q).filter (fun r => ¬r.Coprime q), (A n q r)^2)
      ≤ ∑ r ∈ (Finset.range q).filter (fun r => ¬r.Coprime q),
          (∑ p ∈ q.primeFactors.filter (fun p => p % q = r), Real.log (p : ℝ))^2 := by
        refine Finset.sum_le_sum ?_
        intro r hr
        exact pow_le_pow_left₀ (hA0 r) (hA r hr) 2
    _ ≤ (∑ r ∈ (Finset.range q).filter (fun r => ¬r.Coprime q),
          ∑ p ∈ q.primeFactors.filter (fun p => p % q = r), Real.log (p : ℝ))^2 :=
        Finset.sum_sq_le_sq_sum_of_nonneg (fun r _ => hS r)
    _ ≤ (∑ p ∈ q.primeFactors, Real.log (p : ℝ))^2 := by
        have hfib : (∑ r ∈ (Finset.range q).filter (fun r => ¬r.Coprime q),
            ∑ p ∈ q.primeFactors.filter (fun p => p % q = r), Real.log (p : ℝ))
            = ∑ p ∈ q.primeFactors, Real.log (p : ℝ) := by
          refine Finset.sum_fiberwise_of_maps_to (g := fun p => p % q) ?_ _
          intro p hp
          have hpp : p.Prime := (Nat.mem_primeFactors.mp hp).1
          have hpq : p ∣ q := (Nat.mem_primeFactors.mp hp).2.1
          rw [Finset.mem_filter, Finset.mem_range]
          refine ⟨Nat.mod_lt _ hq, ?_⟩
          rw [ZMod.coprime_mod_iff_coprime]
          rw [hpp.coprime_iff_not_dvd]
          exact not_not.mpr hpq
        rw [hfib]
