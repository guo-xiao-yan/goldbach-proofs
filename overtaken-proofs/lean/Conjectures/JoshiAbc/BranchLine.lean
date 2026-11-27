import Mathlib

theorem Conjectures.JoshiAbc.BranchLine :
    let g := fun (u : ZMod 29) => (![u,0,0] : Fin 3 → ZMod 29); let S := {v | ∃ u : ZMod 29, u^14=1 ∧ v=g u}; Submodule.span (ZMod 29) S = Submodule.span (ZMod 29) ({g 1} : Set (Fin 3 → ZMod 29)) := by
  intro g S
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro v ⟨u, -, rfl⟩
    apply Submodule.mem_span_singleton.mpr
    refine ⟨u, ?_⟩
    ext i
    fin_cases i <;> simp [g]
  · apply Submodule.span_mono
    intro v hv
    rw [Set.mem_singleton_iff] at hv
    exact ⟨1, by simp, hv⟩
