import Mathlib

theorem Conjectures.JoshiAbc.ThetaMinimum :
    ∀ (l j : ℚ), 0 < j → j < l → let b := fun (n : ℤ) => (n:ℚ)*(n+1)/2+(2*(n:ℚ)+1)*j/(2*l); ∀ n : ℤ, n ≠ -1 → b (-1) < b n := by
  intro l j hj hjl b n hn
  have hl : 0 < l := hj.trans hjl
  have hjl' : j / l < 1 := (div_lt_one hl).2 hjl
  have hjl0 : 0 < j / l := div_pos hj hl
  have key : b n - b (-1) = ((n:ℚ)+1) * ((n:ℚ)/2 + j/l) := by
    simp only [b]
    push_cast
    field_simp
    ring
  have : 0 < b n - b (-1) := by
    rw [key]
    rcases lt_or_gt_of_ne hn with h | h
    · have h' : n ≤ -2 := by omega
      have : (n:ℚ) ≤ -2 := by exact_mod_cast h'
      nlinarith
    · have h' : 0 ≤ n := by omega
      have : (0:ℚ) ≤ n := by exact_mod_cast h'
      nlinarith
  linarith
