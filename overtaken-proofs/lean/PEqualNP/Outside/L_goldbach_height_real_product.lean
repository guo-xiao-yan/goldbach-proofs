import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Tactic.Ring

theorem PEqualNP.Outside.L_goldbach_height_real_product :
    ∀ (u v : ℂ) (x : ℝ), (u * star v * Complex.exp ((x:ℂ)*Complex.I)).re = (u*star v).re*Real.cos x - (u*star v).im*Real.sin x := by
  intro u v x
  rw [Complex.exp_mul_I, Complex.mul_re]
  simp [← Complex.ofReal_cos, ← Complex.ofReal_sin]
