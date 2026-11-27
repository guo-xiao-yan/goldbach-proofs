import Mathlib

theorem Conjectures.JoshiAbc.ThetaExponent :
    ∀ (l j : ℚ), l ≠ 0 → let b := fun (n : ℤ) => (n:ℚ)*(n+1)/2+(2*(n:ℚ)+1)*j/(2*l); ∀ n : ℤ, b (n+1)-b n = (n:ℚ)+1+j/l := by
  intro l j hl b n
  simp only [b]
  push_cast
  field_simp
  ring
