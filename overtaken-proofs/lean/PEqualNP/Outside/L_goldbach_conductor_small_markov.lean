import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

theorem PEqualNP.Outside.L_goldbach_conductor_small_markov :
    ∀ (n : ℕ) [NeZero n], 2<n → let odd := (Finset.univ : Finset (DirichletCharacter ℂ n)).filter (fun χ => χ (-1) = -1); ((odd.filter (fun χ => χ.conductor^4≤n^3)).card : ℝ)*Real.log (n:ℝ) ≤ 4*∑ χ ∈ odd, Real.log ((n:ℝ)/(χ.conductor:ℝ)) := by
  intro n _ hn odd
  have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have hcpos : ∀ χ : DirichletCharacter ℂ n, (0 : ℝ) < χ.conductor := by
    intro χ
    exact_mod_cast Nat.pos_of_ne_zero (DirichletCharacter.conductor_ne_zero χ)
  have hcle : ∀ χ : DirichletCharacter ℂ n, (χ.conductor : ℝ) ≤ n := by
    intro χ
    exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne n)) (DirichletCharacter.conductor_dvd_level χ)
  have hlog : ∀ χ : DirichletCharacter ℂ n, Real.log ((n:ℝ)/(χ.conductor:ℝ))
      = Real.log (n:ℝ) - Real.log (χ.conductor : ℝ) := fun χ =>
    Real.log_div hnpos.ne' (hcpos χ).ne'
  have hnn : ∀ χ ∈ odd, 0 ≤ Real.log ((n:ℝ)/(χ.conductor:ℝ)) := by
    intro χ _
    apply Real.log_nonneg
    rw [le_div_iff₀ (hcpos χ)]
    simpa using hcle χ
  have hsmall : ∀ χ ∈ odd.filter (fun χ => χ.conductor^4≤n^3),
      Real.log (n:ℝ) / 4 ≤ Real.log ((n:ℝ)/(χ.conductor:ℝ)) := by
    intro χ hχ
    have h4 : χ.conductor ^ 4 ≤ n ^ 3 := (Finset.mem_filter.mp hχ).2
    have h4' : ((χ.conductor : ℝ)) ^ 4 ≤ (n : ℝ) ^ 3 := by exact_mod_cast h4
    have h5 : Real.log ((χ.conductor : ℝ) ^ 4) ≤ Real.log ((n : ℝ) ^ 3) :=
      Real.log_le_log (pow_pos (hcpos χ) 4) h4'
    rw [Real.log_pow, Real.log_pow] at h5
    rw [hlog]
    push_cast at h5
    linarith
  have h1 : ((odd.filter (fun χ => χ.conductor^4≤n^3)).card : ℝ) * (Real.log (n:ℝ) / 4)
      ≤ ∑ χ ∈ odd.filter (fun χ => χ.conductor^4≤n^3), Real.log ((n:ℝ)/(χ.conductor:ℝ)) := by
    have := Finset.card_nsmul_le_sum _ _ _ hsmall
    simpa [nsmul_eq_mul] using this
  have h2 : ∑ χ ∈ odd.filter (fun χ => χ.conductor^4≤n^3), Real.log ((n:ℝ)/(χ.conductor:ℝ))
      ≤ ∑ χ ∈ odd, Real.log ((n:ℝ)/(χ.conductor:ℝ)) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun χ hχ _ => hnn χ hχ
  linarith
