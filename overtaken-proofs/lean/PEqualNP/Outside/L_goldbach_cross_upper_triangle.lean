import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

theorem PEqualNP.Outside.L_goldbach_cross_upper_triangle :
    ∀ (m : ℕ) (u : Fin m → ℂ), (∑ i, ∑ j ∈ Finset.univ.erase i, (u i*star (u j)).re) = 2*∑ i, ∑ j ∈ Finset.univ.filter (fun j => i<j), (u i*star (u j)).re := by
  intro m u
  have e : ∀ i : Fin m, ∑ j ∈ Finset.univ.erase i, (u i*star (u j)).re
      = ∑ j ∈ Finset.univ.filter (fun j => i<j), (u i*star (u j)).re
        + ∑ j ∈ Finset.univ.filter (fun j => j < i), (u i*star (u j)).re := by
    intro i
    have : Finset.univ.erase i = Finset.univ.filter (fun j => i<j) ∪ Finset.univ.filter (fun j => j < i) := by
      ext j
      simp only [Finset.mem_erase, Finset.mem_univ, and_true, Finset.mem_union, Finset.mem_filter, true_and]
      constructor
      · intro h; exact (lt_or_gt_of_ne h).symm
      · rintro (h | h)
        · exact ne_of_gt h
        · exact ne_of_lt h
    rw [this, Finset.sum_union]
    rw [Finset.disjoint_left]
    intro j h1 h2
    simp only [Finset.mem_filter] at h1 h2
    exact absurd h1.2 (not_lt_of_gt h2.2)
  simp only [e, Finset.sum_add_distrib]
  have swap : ∑ i, ∑ j ∈ Finset.univ.filter (fun j => j < i), (u i*star (u j)).re
      = ∑ i, ∑ j ∈ Finset.univ.filter (fun j => i<j), (u i*star (u j)).re := by
    rw [Finset.sum_sigma', Finset.sum_sigma']
    refine Finset.sum_nbij' (fun x => ⟨x.2, x.1⟩) (fun x => ⟨x.2, x.1⟩) ?_ ?_ ?_ ?_ ?_
    · rintro ⟨i, j⟩ h
      simp only [Finset.mem_sigma, Finset.mem_filter, Finset.mem_univ, true_and] at h ⊢
      exact h
    · rintro ⟨i, j⟩ h
      simp only [Finset.mem_sigma, Finset.mem_filter, Finset.mem_univ, true_and] at h ⊢
      exact h
    · rintro ⟨i, j⟩ _; rfl
    · rintro ⟨i, j⟩ _; rfl
    · rintro ⟨i, j⟩ _
      simp only [Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im]
      ring
  rw [swap]; ring
