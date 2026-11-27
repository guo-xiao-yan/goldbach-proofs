import Mathlib

private lemma pbos_range_sum (q : ℕ) [NeZero q] (f : ZMod q → ℂ) :
    ∑ a ∈ Finset.range q, f (a : ZMod q) = ∑ x : ZMod q, f x := by
  symm
  refine Finset.sum_bij (fun (x : ZMod q) _ => x.val) (fun x _ => Finset.mem_range.mpr (ZMod.val_lt x))
    (fun x _ y _ h => ZMod.val_injective q h) (fun b hb => ⟨(b : ZMod q), Finset.mem_univ _, ?_⟩) ?_
  · exact ZMod.val_cast_of_lt (Finset.mem_range.mp hb)
  · intro x _
    simp

private lemma pbos_E (q : ℕ) [NeZero q] (n : ℕ) (a : ℕ) :
    Complex.exp (((2 * Real.pi * ((n : ℝ) * (a : ℝ) / (q : ℝ)) : ℝ) : ℂ) * Complex.I)
      = ZMod.stdAddChar (N := q) ((n : ZMod q) * (a : ZMod q)) := by
  have := ZMod.stdAddChar_coe (N := q) ((n * a : ℕ) : ℤ)
  have hc : (((n * a : ℕ) : ℤ) : ZMod q) = (n : ZMod q) * (a : ZMod q) := by push_cast; rfl
  rw [hc] at this
  rw [this]
  congr 1
  have : (q : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne q
  push_cast
  field_simp

theorem Conjectures.Goldbach.PacketBinaryOrbitSecondMoment :
    let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); ∀ q m : ℕ, 0<q → (∑ a ∈ Finset.range q, ‖∑ j ∈ Finset.range m, E ((((2:ℕ)^(j+1):ℕ):ℝ)*(a:ℝ)/(q:ℝ))‖^2) = (q:ℝ)*(((Finset.range m ×ˢ Finset.range m).filter (fun ij => (2:ℕ)^(ij.1+1)%q = (2:ℕ)^(ij.2+1)%q)).card:ℝ) := by
  intro E q m hq
  have : NeZero q := ⟨hq.ne'⟩
  have hE : ∀ j a : ℕ, E ((((2:ℕ)^(j+1):ℕ):ℝ)*(a:ℝ)/(q:ℝ))
      = ZMod.stdAddChar (N := q) (((2:ℕ)^(j+1) : ℕ) * (a : ZMod q)) := by
    intro j a
    exact pbos_E q _ a
  simp only [hE]
  apply Complex.ofReal_injective
  have h1 : ∀ a : ℕ, ((‖∑ j ∈ Finset.range m, ZMod.stdAddChar (N := q) (((2:ℕ)^(j+1) : ℕ) * (a : ZMod q))‖ ^ 2 : ℝ) : ℂ)
      = ∑ i ∈ Finset.range m, ∑ j ∈ Finset.range m,
        ZMod.stdAddChar (N := q) ((a : ZMod q) * ((((2:ℕ)^(i+1) : ℕ) : ZMod q) - (((2:ℕ)^(j+1) : ℕ) : ZMod q))) := by
    intro a
    rw [← Complex.normSq_eq_norm_sq, ← Complex.mul_conj, map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [← AddChar.map_neg_eq_conj, ← AddChar.map_add_eq_mul]
    congr 1
    ring
  have h2 : ∀ i j : ℕ, ∑ a ∈ Finset.range q,
      ZMod.stdAddChar (N := q) ((a : ZMod q) * ((((2:ℕ)^(i+1) : ℕ) : ZMod q) - (((2:ℕ)^(j+1) : ℕ) : ZMod q)))
      = if (2:ℕ)^(i+1) % q = (2:ℕ)^(j+1) % q then (q : ℂ) else 0 := by
    intro i j
    rw [pbos_range_sum q (fun x => ZMod.stdAddChar (N := q) (x * ((((2:ℕ)^(i+1) : ℕ) : ZMod q) - (((2:ℕ)^(j+1) : ℕ) : ZMod q))))]
    rw [AddChar.sum_mulShift _ (ZMod.isPrimitive_stdAddChar q)]
    simp only [sub_eq_zero, ZMod.natCast_eq_natCast_iff', ZMod.card]
    split_ifs <;> simp
  rw [Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_natCast, Complex.ofReal_natCast,
    Finset.sum_congr rfl (fun a _ => h1 a)]
  calc _ = ∑ i ∈ Finset.range m, ∑ j ∈ Finset.range m, ∑ a ∈ Finset.range q,
        ZMod.stdAddChar (N := q) ((a : ZMod q) * ((((2:ℕ)^(i+1) : ℕ) : ZMod q) - (((2:ℕ)^(j+1) : ℕ) : ZMod q))) := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ i ∈ Finset.range m, ∑ j ∈ Finset.range m, if (2:ℕ)^(i+1) % q = (2:ℕ)^(j+1) % q then (q : ℂ) else 0 := by
        simp only [h2]
    _ = _ := by
        rw [← Finset.sum_product' (f := fun i j => if (2:ℕ)^(i+1) % q = (2:ℕ)^(j+1) % q then (q : ℂ) else 0),
          Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, mul_comm]
