import Mathlib

theorem Conjectures.JoshiAbc.MarkedTransport :
    ∀ (K F : Type) [NontriviallyNormedField K] [NontriviallyNormedField F] [CompleteSpace K] [CompleteSpace F] (e : K ≃+* F), Continuous e → Continuous e.symm → ∀ q u : K, e (∑' n : ℤ, q^(n*(n+1)/2)*u^(2*n+1)) = ∑' n : ℤ, (e q)^(n*(n+1)/2)*(e u)^(2*n+1) := by
  intro K F _ _ _ _ e he he' q u
  have hterm : ∀ n : ℤ, e (q^(n*(n+1)/2)*u^(2*n+1)) = (e q)^(n*(n+1)/2)*(e u)^(2*n+1) := by
    intro n
    rw [map_mul, map_zpow₀, map_zpow₀]
  simp_rw [← hterm]
  by_cases h : Summable (fun n : ℤ => q^(n*(n+1)/2)*u^(2*n+1))
  · exact (h.hasSum.map (e : K →+* F) he).tsum_eq.symm
  · have h2 : ¬ Summable (fun n : ℤ => e (q^(n*(n+1)/2)*u^(2*n+1))) := by
      intro hs
      apply h
      have := hs.hasSum.map (e.symm : F →+* K) he'
      have h4 := this.summable
      exact h4.congr fun n => by simp
    rw [tsum_eq_zero_of_not_summable h, tsum_eq_zero_of_not_summable h2]
    simp
