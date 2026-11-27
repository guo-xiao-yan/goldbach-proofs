import Mathlib

theorem Conjectures.JoshiAbc.FourierDetection :
    ∀ (p n : ℕ) [Fact p.Prime] (S : Set (Fin n → ZMod p)), Submodule.span (ZMod p) S = ⊤ ↔ ∀ f : Module.Dual (ZMod p) (Fin n → ZMod p), f ≠ 0 → ∃ v ∈ S, f v ≠ 0 := by
  intro p n _ S
  constructor
  · intro h f hf
    by_contra hc
    apply hf
    refine LinearMap.ext fun v => ?_
    have hv : v ∈ Submodule.span (ZMod p) S := by rw [h]; trivial
    have : Submodule.span (ZMod p) S ≤ LinearMap.ker f := by
      rw [Submodule.span_le]
      intro x hx
      by_contra h'
      exact hc ⟨x, hx, h'⟩
    simpa using this hv
  · intro h
    by_contra hne
    obtain ⟨f, hf, hfs⟩ := Submodule.exists_dual_map_eq_bot_of_lt_top (lt_top_iff_ne_top.mpr hne) inferInstance
    obtain ⟨v, hv, hfv⟩ := h f hf
    apply hfv
    have : v ∈ Submodule.span (ZMod p) S := Submodule.subset_span hv
    have h2 : f v ∈ Submodule.map f (Submodule.span (ZMod p) S) := ⟨v, this, rfl⟩
    rw [hfs] at h2
    simpa using h2
