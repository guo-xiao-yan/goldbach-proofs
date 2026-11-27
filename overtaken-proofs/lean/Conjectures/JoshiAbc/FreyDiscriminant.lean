import Mathlib

theorem Conjectures.JoshiAbc.FreyDiscriminant :
    ∀ a b : ℕ, let E : WeierstrassCurve ℚ := ⟨0,(b:ℚ)-a,0,-(a:ℚ)*b,0⟩; E.Δ = 16*(a:ℚ)^2*(b:ℚ)^2*((a:ℚ)+b)^2 := by
  intro a b E
  simp only [E, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  ring
