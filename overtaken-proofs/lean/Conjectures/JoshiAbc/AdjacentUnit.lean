import Mathlib

theorem Conjectures.JoshiAbc.AdjacentUnit :
    ∀ (K : Type) [NormedField K] (r : K) (ξ : ℕ → K) (j : ℕ), 0 < j → r ≠ 0 → ‖ξ j‖=‖r‖^j → ‖ξ (j-1)‖=‖r‖^(j-1) → ‖ξ j/ξ (j-1)‖=‖r‖ := by
  intro K _ r ξ j hj hr h1 h2
  have hr' : ‖r‖ ≠ 0 := norm_ne_zero_iff.mpr hr
  rw [norm_div, h1, h2]
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  simp only [Nat.add_sub_cancel, pow_succ]
  field_simp
