import Mathlib

theorem Conjectures.Goldbach.BeaumontDenseOpenHit :
    ∀ {X : Type} [TopologicalSpace X] (O U : Set X), Dense O → IsOpen U → U.Nonempty → (O ∩ U).Nonempty := by
  intro X _ O U hO hU hne
  rw [Set.inter_comm]
  exact hO.inter_open_nonempty U hU hne
