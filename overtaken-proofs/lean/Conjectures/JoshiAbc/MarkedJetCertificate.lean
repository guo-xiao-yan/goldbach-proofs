import Mathlib

theorem Conjectures.JoshiAbc.MarkedJetCertificate :
    let z : ZMod 29 := 7; let v : Fin 3 → Fin 3 → ZMod 29 := ![![1,0,0],![0,1+z^2,0],![1,0,z^2]]; ∀ (I : Type) (allowed : I → Set (Fin 3 → ZMod 29)) (i : I), (∀ j, v j ∈ allowed i) → Submodule.span (ZMod 29) (allowed i)=⊤ := by
  have h1' : (1 + (7 : ZMod 29)^2) ≠ 0 := by decide +kernel
  have h2' : ((7 : ZMod 29)^2) ≠ 0 := by decide +kernel
  have h3' : (7 : ZMod 29) ≠ 0 := by decide +kernel
  intro z v I allowed i h
  have : Fact (Nat.Prime 29) := ⟨by norm_num⟩
  have h1 : (1 + z^2 : ZMod 29) ≠ 0 := h1'
  have h2 : (z^2 : ZMod 29) ≠ 0 := h2'
  have h3 : (z : ZMod 29) ≠ 0 := h3'
  have hsub : Submodule.span (ZMod 29) (Set.range v) ≤ Submodule.span (ZMod 29) (allowed i) :=
    Submodule.span_mono (by rintro _ ⟨j, rfl⟩; exact h j)
  rw [eq_top_iff]
  refine le_trans ?_ hsub
  intro x _
  have m0 : v 0 ∈ Submodule.span (ZMod 29) (Set.range v) := Submodule.subset_span ⟨0, rfl⟩
  have m1 : v 1 ∈ Submodule.span (ZMod 29) (Set.range v) := Submodule.subset_span ⟨1, rfl⟩
  have m2 : v 2 ∈ Submodule.span (ZMod 29) (Set.range v) := Submodule.subset_span ⟨2, rfl⟩
  have e : x = (x 0 - x 2 * (z^2)⁻¹) • v 0 + (x 1 * (1+z^2)⁻¹) • v 1 + (x 2 * (z^2)⁻¹) • v 2 := by
    funext k
    fin_cases k
    · simp [v]
    · simp [v]; field_simp
    · simp [v]; field_simp
  rw [e]
  exact add_mem (add_mem (Submodule.smul_mem _ _ m0) (Submodule.smul_mem _ _ m1)) (Submodule.smul_mem _ _ m2)
