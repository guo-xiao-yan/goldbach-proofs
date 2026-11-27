import Mathlib

theorem Conjectures.Goldbach.QuadraticGaussNormPrime :
    let E (x : ℝ) := Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I); ∀ p a : ℕ, Nat.Prime p → 2 < p → Nat.Coprime a p → ‖∑ b ∈ Finset.range p, (jacobiSym (b : ℤ) p : ℂ) * E ((b : ℝ) * ((a : ℝ) / p))‖ = Real.sqrt (p : ℝ) := by
  intro E p a hp hp2 hcop
  have : Fact p.Prime := ⟨hp⟩
  have hring : ringChar (ZMod p) ≠ 2 := by
    rw [ZMod.ringChar_zmod_n]; omega
  set χ : MulChar (ZMod p) ℂ := (quadraticChar (ZMod p)).ringHomComp (Int.castRingHom ℂ) with hχ
  have hχ1 : χ ≠ 1 := by
    intro h
    apply quadraticChar_ne_one hring
    ext x
    have := congrArg (fun f : MulChar (ZMod p) ℂ => f x) h
    simp only [hχ, MulChar.ringHomComp_apply, MulChar.one_apply_coe] at this ⊢
    simpa using this
  have hχ2 : χ.IsQuadratic := by
    intro x
    have := (quadraticChar_isQuadratic (ZMod p)) x
    simp only [hχ, MulChar.ringHomComp_apply]
    rcases this with h | h | h <;> simp [h]
  have hne : ∀ x : (ZMod p)ˣ, χ (x : ZMod p) ≠ 0 := by
    intro x h
    have := χ.map_mul (x : ZMod p) ((x⁻¹ : (ZMod p)ˣ) : ZMod p)
    simp only [MulChar.coe_toMonoidHom, Units.mul_inv, h, zero_mul, MulChar.map_one] at this
    exact one_ne_zero this
  have hsq := gaussSum_sq hχ1 hχ2 (ψ := ZMod.stdAddChar) (ZMod.isPrimitive_stdAddChar p)
  have hau : IsUnit (a : ZMod p) := by
    rw [ZMod.isUnit_iff_coprime]; exact hcop
  obtain ⟨u, hu⟩ := hau
  have hshift := gaussSum_mulShift_eq χ (ZMod.stdAddChar : AddChar (ZMod p) ℂ) u
  have hsum : ∑ b ∈ Finset.range p, (jacobiSym (b : ℤ) p : ℂ) * E ((b : ℝ) * ((a : ℝ) / p))
      = gaussSum χ (ZMod.stdAddChar.mulShift (u : ZMod p)) := by
    unfold gaussSum
    symm
    refine Finset.sum_bij (fun (x : ZMod p) _ => x.val) (fun x _ => Finset.mem_range.mpr (ZMod.val_lt x))
      (fun x _ y _ h => ZMod.val_injective p h) (fun b hb => ⟨(b : ZMod p), Finset.mem_univ _, ?_⟩) ?_
    · exact ZMod.val_cast_of_lt (Finset.mem_range.mp hb)
    · intro x _
      have h1 : (jacobiSym (x.val : ℤ) p : ℂ) = χ x := by
        rw [← jacobiSym.legendreSym.to_jacobiSym]
        simp [hχ, legendreSym]
      rw [h1]
      congr 1
      rw [AddChar.mulShift_apply, hu]
      have := ZMod.stdAddChar_coe (N := p) ((a * x.val : ℕ) : ℤ)
      have hc : (((a * x.val : ℕ) : ℤ) : ZMod p) = (a : ZMod p) * x := by
        push_cast; rw [ZMod.natCast_zmod_val]
      rw [hc] at this
      rw [this]
      simp only [E]
      congr 1
      have : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
      push_cast
      field_simp
  rw [hsum, hshift]
  have hn : ‖gaussSum χ ZMod.stdAddChar‖ = Real.sqrt p := by
    have h2 : ‖gaussSum χ ZMod.stdAddChar‖ ^ 2 = p := by
      rw [← norm_pow, hsq]
      have : χ (-1) = 1 ∨ χ (-1) = -1 := by
        have h0 := hne (-1)
        rcases hχ2 (-1) with h | h | h
        · exact absurd (by simpa using h) h0
        · exact Or.inl h
        · exact Or.inr h
      rcases this with h | h <;> simp [h, ZMod.card]
    rw [← h2, Real.sqrt_sq (norm_nonneg _)]
  have hu1 : ‖(χ⁻¹) (u : ZMod p)‖ = 1 := by
    have : (χ⁻¹) (u : ZMod p) = χ u := by rw [hχ2.inv]
    rw [this]
    have h0 := hne u
    rcases hχ2 (u : ZMod p) with h | h | h
    · exact absurd h h0
    · simp [h]
    · simp [h]
  rw [norm_mul, hu1, one_mul, hn]
