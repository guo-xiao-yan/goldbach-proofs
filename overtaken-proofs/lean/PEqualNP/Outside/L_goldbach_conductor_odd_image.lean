import Mathlib.Tactic.Ring
import Mathlib.Analysis.Complex.Basic

theorem PEqualNP.Outside.L_goldbach_conductor_odd_image :
    ∀ (m : ℕ) (r : Fin m → Fin m) (v : Fin m → ℂ), Function.Involutive r → ∀ i, (v (r i)-v (r (r i)))/2 = -((v i-v (r i))/2) := by
  intro m r v hr i
  rw [hr i]
  ring
