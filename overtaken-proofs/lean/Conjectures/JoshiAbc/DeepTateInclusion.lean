import Mathlib

theorem Conjectures.JoshiAbc.DeepTateInclusion :
    ∀ t : ℕ, 1 ≤ t → 14+(14*t+1) ≤ 4*(14*t+1) := by
  intro t ht
  omega
