import Mathlib

private lemma ocm_star {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (a : (ZMod N)ˣ) :
    star (χ (a : ZMod N)) = χ ((a⁻¹ : (ZMod N)ˣ) : ZMod N) := by
  have h1 : χ (a : ZMod N) * χ ((a⁻¹ : (ZMod N)ˣ) : ZMod N) = 1 := by
    rw [← map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, map_one]
  have h2 : ‖χ (a : ZMod N)‖ = 1 := by
    apply Complex.norm_eq_one_of_pow_eq_one (n := Fintype.card (ZMod N)ˣ)
    · rw [← map_pow, ← Units.val_pow_eq_pow_val, pow_card_eq_one, Units.val_one, map_one]
    · exact Fintype.card_ne_zero
  have h3 : χ (a : ZMod N) * star (χ (a : ZMod N)) = 1 := by
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, h2]
    simp
  have hne : χ (a : ZMod N) ≠ 0 := by
    intro h; rw [h, zero_mul] at h1; exact zero_ne_one h1
  exact mul_left_cancel₀ hne (h3.trans h1.symm)

theorem Conjectures.Goldbach.OddCharacterMixedMoment :
    ∀ (N : ℕ) [NeZero N] (F G : (ZMod N)ˣ → ℂ), let oddChars := @Finset.filter (DirichletCharacter ℂ N) (fun χ => χ.Odd) (fun χ => Classical.propDecidable χ.Odd) Finset.univ; let T := fun (W : (ZMod N)ˣ → ℂ) (χ : DirichletCharacter ℂ N) => Finset.univ.sum (fun a : (ZMod N)ˣ => W a * χ (a : ZMod N)); 2 * oddChars.sum (fun χ => star (T F χ) * T G χ) = (N.totient : ℂ) * Finset.univ.sum (fun a : (ZMod N)ˣ => star (F a) * (G a - G (-a))) := by
  intro N _ F G oddChars T
  classical
  have hind : 2 * oddChars.sum (fun χ => star (T F χ) * T G χ) =
      ∑ χ : DirichletCharacter ℂ N, (1 - χ (-1 : ZMod N)) * (star (T F χ) * T G χ) := by
    rw [Finset.mul_sum]
    show _ = _
    have : oddChars = Finset.univ.filter (fun χ : DirichletCharacter ℂ N => χ.Odd) := by
      ext χ; simp [oddChars]
    rw [this, Finset.sum_filter]
    refine Finset.sum_congr rfl fun χ _ => ?_
    by_cases h : χ.Odd
    · have : χ (-1 : ZMod N) = -1 := h
      rw [if_pos h, this]; ring
    · have he : χ.Even := (DirichletCharacter.even_or_odd χ).resolve_right h
      have : χ (-1 : ZMod N) = 1 := he
      rw [if_neg h, this]; ring
  rw [hind]
  have hexp : ∀ χ : DirichletCharacter ℂ N, (1 - χ (-1 : ZMod N)) * (star (T F χ) * T G χ) =
      ∑ a : (ZMod N)ˣ, ∑ b : (ZMod N)ˣ, star (F a) * G b *
        (χ ((a⁻¹ : (ZMod N)ˣ) : ZMod N) * χ (b : ZMod N) -
          χ ((a⁻¹ : (ZMod N)ˣ) : ZMod N) * χ (((-b : (ZMod N)ˣ)) : ZMod N)) := by
    intro χ
    simp only [T]
    rw [star_sum, Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [star_mul', ocm_star]
    have : χ (((-b : (ZMod N)ˣ)) : ZMod N) = χ (-1 : ZMod N) * χ (b : ZMod N) := by
      rw [← map_mul]; congr 1; simp
    rw [this]; ring
  have hort : ∀ a b : (ZMod N)ˣ, ∑ χ : DirichletCharacter ℂ N,
      χ ((a⁻¹ : (ZMod N)ˣ) : ZMod N) * χ (b : ZMod N) = if a = b then (N.totient : ℂ) else 0 := by
    intro a b
    rw [← ZMod.inv_coe_unit, DirichletCharacter.sum_char_inv_mul_char_eq ℂ a.isUnit]
    simp only [Units.val_inj]
  have hort2 : ∀ a b : (ZMod N)ˣ, ∑ χ : DirichletCharacter ℂ N,
      χ ((a⁻¹ : (ZMod N)ˣ) : ZMod N) * χ (((-b : (ZMod N)ˣ)) : ZMod N) =
        if a = -b then (N.totient : ℂ) else 0 := by
    intro a b
    rw [← ZMod.inv_coe_unit, DirichletCharacter.sum_char_inv_mul_char_eq ℂ a.isUnit]
    simp only [Units.val_inj]
  simp_rw [hexp]
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  have : ∀ b : (ZMod N)ˣ, ∑ χ : DirichletCharacter ℂ N, star (F a) * G b *
        (χ ((a⁻¹ : (ZMod N)ˣ) : ZMod N) * χ (b : ZMod N) -
          χ ((a⁻¹ : (ZMod N)ˣ) : ZMod N) * χ (((-b : (ZMod N)ˣ)) : ZMod N)) =
      star (F a) * G b * ((if a = b then (N.totient : ℂ) else 0) - (if a = -b then (N.totient : ℂ) else 0)) := by
    intro b
    rw [← Finset.mul_sum, Finset.sum_sub_distrib, hort, hort2]
  simp_rw [this]
  have e2 : ∀ b : (ZMod N)ˣ, (a = -b) ↔ (b = -a) := fun b => by
    constructor <;> intro h <;> simp [h]
  simp only [e2, mul_sub, mul_ite, mul_zero, Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  ring
