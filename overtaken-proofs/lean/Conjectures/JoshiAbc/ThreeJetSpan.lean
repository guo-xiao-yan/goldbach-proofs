import Mathlib

theorem Conjectures.JoshiAbc.ThreeJetSpan :
    let z : ZMod 29 := 7; let v : Fin 3 → Fin 3 → ZMod 29 := ![![1,0,0],![0,1+z^2,0],![1,0,z^2]]; Submodule.span (ZMod 29) (Set.range v) = ⊤ := by
  intro z v
  rw [eq_top_iff]
  intro x _
  have h0 : v 0 ∈ Submodule.span (ZMod 29) (Set.range v) := Submodule.subset_span ⟨0, rfl⟩
  have h1 : v 1 ∈ Submodule.span (ZMod 29) (Set.range v) := Submodule.subset_span ⟨1, rfl⟩
  have h2 : v 2 ∈ Submodule.span (ZMod 29) (Set.range v) := Submodule.subset_span ⟨2, rfl⟩
  have h900 : (900 : ZMod 29) = 1 := by decide
  have h784 : (784 : ZMod 29) = 1 := by decide
  have : x = (x 0 - 16 * x 2) • v 0 + (18 * x 1) • v 1 + (16 * x 2) • v 2 := by
    funext i
    fin_cases i <;> simp [v, z] <;> ring_nf <;> simp [h900, h784]
  rw [this]
  exact Submodule.add_mem _ (Submodule.add_mem _ (Submodule.smul_mem _ _ h0) (Submodule.smul_mem _ _ h1)) (Submodule.smul_mem _ _ h2)
