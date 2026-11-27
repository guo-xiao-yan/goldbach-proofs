import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.Complex.Basic

theorem PEqualNP.Outside.L_goldbach_conductor_odd_split :
    ∀ (m : ℕ) (r : Fin m → Fin m) (v : Fin m → ℂ), Function.Involutive r → let p := fun x i => (x i-x (r i))/2; ∀ i, p (p v) i=p v i := by
  intro m r v hr p i
  show ((v i - v (r i))/2 - (v (r i) - v (r (r i)))/2)/2 = (v i - v (r i))/2
  rw [hr i]
  ring
