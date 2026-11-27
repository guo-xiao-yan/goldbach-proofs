import Mathlib

private lemma tf_E_add (E : ℝ → ℂ) (hE : ∀ x, E x = Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I))
    (x y : ℝ) : E (x + y) = E x * E y := by
  rw [hE, hE, hE, ← Complex.exp_add]
  congr 1
  push_cast
  ring

private lemma tf_E_conj (E : ℝ → ℂ) (hE : ∀ x, E x = Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I))
    (x : ℝ) : (starRingEnd ℂ) (E x) = E (-x) := by
  rw [hE, hE, ← Complex.exp_conj]
  congr 1
  rw [map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

private lemma tf_E_cont (E : ℝ → ℂ) (hE : ∀ x, E x = Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)) :
    Continuous E := by
  have : E = fun x => Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I) := funext hE
  rw [this]
  fun_prop

private lemma tf_orth (E : ℝ → ℂ) (hE : ∀ x, E x = Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I))
    (m : ℤ) : ∫ b in (-1/2:ℝ)..(1/2), E ((m : ℝ) * b) = if m = 0 then 1 else 0 := by
  by_cases hm : m = 0
  · subst hm
    simp [hE]
    norm_num
  · rw [if_neg hm]
    have hc : (((2 * Real.pi * (m : ℝ) : ℝ) : ℂ) * Complex.I) ≠ 0 := by
      have : (m : ℝ) ≠ 0 := by exact_mod_cast hm
      have : ((2 * Real.pi * (m : ℝ) : ℝ) : ℂ) ≠ 0 := by
        exact_mod_cast (by positivity : (2 * Real.pi * (m : ℝ)) ≠ 0)
      exact mul_ne_zero this Complex.I_ne_zero
    have h1 : (fun b : ℝ => E ((m : ℝ) * b))
        = fun b : ℝ => Complex.exp ((((2 * Real.pi * (m : ℝ) : ℝ) : ℂ) * Complex.I) * (b : ℂ)) := by
      funext b
      rw [hE]
      congr 1
      push_cast
      ring
    rw [h1, integral_exp_mul_complex hc]
    have h2 : Complex.exp ((((2 * Real.pi * (m : ℝ) : ℝ) : ℂ) * Complex.I) * ((1/2 : ℝ) : ℂ))
        = Complex.exp ((((2 * Real.pi * (m : ℝ) : ℝ) : ℂ) * Complex.I) * ((-1/2 : ℝ) : ℂ)) := by
      rw [Complex.exp_eq_exp_iff_exists_int]
      refine ⟨m, ?_⟩
      push_cast
      ring
    rw [h2]
    simp

private lemma tf_norm_E (E : ℝ → ℂ) (hE : ∀ x, E x = Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I))
    (x : ℝ) : ‖E x‖ = 1 := by
  rw [hE]
  have := Complex.norm_exp_ofReal_mul_I (2 * Real.pi * x)
  exact this

private lemma tf_pow (E : ℝ → ℂ) (hE : ∀ x, E x = Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I))
    (k : ℕ) (b : ℝ) : E ((k : ℝ) * b) = (E b) ^ k := by
  rw [hE, hE, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

private lemma tf_conj_K (E : ℝ → ℂ) (hE : ∀ x, E x = Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I))
    (N : ℕ) (b : ℝ) :
    (starRingEnd ℂ) (∑ k ∈ Finset.range (N + 1), E ((k : ℝ) * b))
      = E (-(N : ℝ) * b) * ∑ k ∈ Finset.range (N + 1), E ((k : ℝ) * b) := by
  rw [map_sum, Finset.mul_sum]
  simp_rw [tf_E_conj E hE]
  rw [← Finset.sum_range_reflect (fun k => E (-((k : ℝ) * b))) (N + 1)]
  apply Finset.sum_congr rfl
  intro j hj
  have hj' : j ≤ N := by simpa [Nat.lt_succ_iff] using hj
  rw [← tf_E_add E hE]
  congr 1
  rw [show N + 1 - 1 - j = N - j by omega, Nat.cast_sub hj']
  ring

private lemma tf_tail (E : ℝ → ℂ) (hE : ∀ x, E x = Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I))
    (N : ℕ) (b : ℝ) (hb0 : b ≠ 0) (hb : |b| ≤ 1 / 2) :
    ‖∑ k ∈ Finset.range (N + 1), E ((k : ℝ) * b)‖ ^ 2 ≤ 1 / (4 * b ^ 2) := by
  set K := ∑ k ∈ Finset.range (N + 1), E ((k : ℝ) * b) with hK
  have hgeom : K * (E b - 1) = E (((N + 1 : ℕ) : ℝ) * b) - 1 := by
    rw [hK, tf_pow E hE]
    simp_rw [tf_pow E hE]
    rw [geom_sum_mul]
  have hnum : ‖E (((N + 1 : ℕ) : ℝ) * b) - 1‖ ≤ 2 := by
    calc ‖E (((N + 1 : ℕ) : ℝ) * b) - 1‖ ≤ ‖E (((N + 1 : ℕ) : ℝ) * b)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by rw [tf_norm_E E hE]; norm_num
  have hden : 4 * |b| ≤ ‖E b - 1‖ := by
    have h1 : E b = Complex.exp (Complex.I * ((2 * Real.pi * b : ℝ) : ℂ)) := by
      rw [hE, mul_comm]
    rw [h1, Complex.norm_exp_I_mul_ofReal_sub_one]
    have h2 : 2 * (Real.pi * |b|) / Real.pi = 2 * |b| := by
      field_simp
    have h3 : 2 / Real.pi * (Real.pi * |b|) ≤ Real.sin (Real.pi * |b|) := by
      apply Real.mul_le_sin (by positivity)
      have := Real.pi_pos
      nlinarith [abs_nonneg b]
    have h4 : 2 / Real.pi * (Real.pi * |b|) = 2 * |b| := by
      field_simp
    have h5 : |Real.sin (2 * Real.pi * b / 2)| = Real.sin (Real.pi * |b|) := by
      have : 2 * Real.pi * b / 2 = Real.pi * b := by ring
      rw [this]
      rcases le_or_gt 0 b with h | h
      · rw [abs_of_nonneg h]
        apply abs_of_nonneg
        apply Real.sin_nonneg_of_nonneg_of_le_pi (by positivity)
        have := Real.pi_pos
        rw [abs_of_nonneg h] at hb
        nlinarith
      · have hb' : -b ≤ 1 / 2 := by rw [abs_of_neg h] at hb; exact hb
        calc |Real.sin (Real.pi * b)| = |-Real.sin (Real.pi * b)| := (abs_neg _).symm
          _ = |Real.sin (Real.pi * (-b))| := by rw [mul_neg, Real.sin_neg]
          _ = Real.sin (Real.pi * (-b)) := by
            apply abs_of_nonneg
            apply Real.sin_nonneg_of_nonneg_of_le_pi (by nlinarith [Real.pi_pos])
            nlinarith [Real.pi_pos]
          _ = Real.sin (Real.pi * |b|) := by rw [abs_of_neg h]
    rw [Real.norm_eq_abs, abs_mul, abs_two, h5]
    linarith
  have hprod : ‖K‖ * ‖E b - 1‖ ≤ 2 := by
    rw [← norm_mul, hgeom]; exact hnum
  have hbpos : 0 < |b| := abs_pos.2 hb0
  have hK2 : ‖K‖ * (4 * |b|) ≤ 2 := by
    calc ‖K‖ * (4 * |b|) ≤ ‖K‖ * ‖E b - 1‖ := by
          exact mul_le_mul_of_nonneg_left hden (norm_nonneg _)
      _ ≤ 2 := hprod
  have hsq : b ^ 2 = |b| ^ 2 := (sq_abs b).symm
  have hsq' : (‖K‖ * (4 * |b|)) ^ 2 ≤ 2 ^ 2 := pow_le_pow_left₀ (by positivity) hK2 2
  rw [hsq, le_div_iff₀ (by positivity)]
  nlinarith [hsq']

private lemma tf_anti (x : ℝ) (hx : x ≠ 0) :
    HasDerivAt (fun y : ℝ => -(1 / 4 : ℝ) * y⁻¹) (1 / (4 * x ^ 2)) x := by
  have := (hasDerivAt_inv hx).const_mul (-(1 / 4 : ℝ))
  convert this using 1
  field_simp

private lemma tf_cont (s : Set ℝ) (hs : ∀ x ∈ s, x ≠ 0) :
    ContinuousOn (fun x : ℝ => 1 / (4 * x ^ 2)) s := by
  intro x hx
  have := hs x hx
  apply ContinuousAt.continuousWithinAt
  have h1 : ContinuousAt (fun x : ℝ => 4 * x ^ 2) x := by fun_prop
  exact continuousAt_const.div h1 (by show 4 * x ^ 2 ≠ 0; positivity)

private lemma tf_int_right (W : ℝ) (hW0 : 0 < W) (hW1 : W ≤ 1 / 2) :
    ∫ x in W..(1 / 2 : ℝ), 1 / (4 * x ^ 2) = 1 / (4 * W) - 1 / 2 := by
  have hne : ∀ x ∈ Set.uIcc W (1 / 2 : ℝ), x ≠ 0 := by
    intro x hx
    rw [Set.uIcc_of_le hW1] at hx
    exact (lt_of_lt_of_le hW0 hx.1).ne'
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x hx => tf_anti x (hne x hx))]
  · field_simp
    ring
  · exact (tf_cont _ hne).intervalIntegrable

private lemma tf_int_left (W : ℝ) (hW0 : 0 < W) (hW1 : W ≤ 1 / 2) :
    ∫ x in (-1 / 2 : ℝ)..(-W), 1 / (4 * x ^ 2) = 1 / (4 * W) - 1 / 2 := by
  have hne : ∀ x ∈ Set.uIcc (-1 / 2 : ℝ) (-W), x ≠ 0 := by
    intro x hx
    rw [Set.uIcc_of_le (by linarith)] at hx
    exact (lt_of_le_of_lt hx.2 (by linarith)).ne
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x hx => tf_anti x (hne x hx))]
  · field_simp
    ring
  · exact (tf_cont _ hne).intervalIntegrable

private lemma tf_main (E : ℝ → ℂ)
    (hE : ∀ x, E x = Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I))
    (K : ℕ → ℝ → ℂ) (hK : ∀ N b, K N b = ∑ k ∈ Finset.range (N + 1), E ((k : ℝ) * b))
    (N : ℕ) (W : ℝ) (hW0 : 0 < W) (hW1 : W ≤ 1 / 2) :
    ((N + 1 : ℕ) : ℝ) - 1 / (2 * W) ≤ (intervalIntegral (fun b => (K N b)^2 * E (-(N : ℝ) * b)) (-W) W MeasureTheory.volume).re := by
  have hEc : Continuous E := tf_E_cont E hE
  have hKc : Continuous (K N) := by
    have : K N = fun b : ℝ => ∑ k ∈ Finset.range (N + 1), E ((k : ℝ) * b) := funext (hK N)
    rw [this]
    exact continuous_finsetSum _ fun k _ => hEc.comp (continuous_const.mul continuous_id)
  have hconj : ∀ b, (starRingEnd ℂ) (K N b) = E (-(N : ℝ) * b) * K N b := by
    intro b
    rw [hK N b]
    exact tf_conj_K E hE N b
  have hmc : ∀ b, K N b * (starRingEnd ℂ) (K N b) = (((‖K N b‖ ^ 2 : ℝ)) : ℂ) := by
    intro b
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hint : ∀ b, (K N b) ^ 2 * E (-(N : ℝ) * b) = (((‖K N b‖ ^ 2 : ℝ)) : ℂ) := by
    intro b
    rw [← hmc b, hconj b]
    ring
  have hfun : (fun b => (K N b) ^ 2 * E (-(N : ℝ) * b)) = fun b => (((‖K N b‖ ^ 2 : ℝ)) : ℂ) :=
    funext hint
  rw [hfun, intervalIntegral.integral_ofReal, Complex.ofReal_re]
  have hfc : Continuous (fun b => ‖K N b‖ ^ 2) := hKc.norm.pow 2
  have hexp : ∀ b, (((‖K N b‖ ^ 2 : ℝ)) : ℂ)
      = ∑ j ∈ Finset.range (N + 1), ∑ k ∈ Finset.range (N + 1),
          E ((((j : ℤ) - (k : ℤ) : ℤ) : ℝ) * b) := by
    intro b
    rw [← hmc b]
    rw [hK N b]
    rw [map_sum, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    rw [tf_E_conj E hE, ← tf_E_add E hE]
    congr 1
    push_cast
    ring
  have hA : ∫ b in (-1 / 2 : ℝ)..(1 / 2), ‖K N b‖ ^ 2 = ((N + 1 : ℕ) : ℝ) := by
    have h1 : (∫ b in (-1 / 2 : ℝ)..(1 / 2), (((‖K N b‖ ^ 2 : ℝ)) : ℂ)) = (((N + 1 : ℕ) : ℝ) : ℂ) := by
      rw [show (fun b => (((‖K N b‖ ^ 2 : ℝ)) : ℂ)) = fun b => ∑ j ∈ Finset.range (N + 1),
          ∑ k ∈ Finset.range (N + 1), E ((((j : ℤ) - (k : ℤ) : ℤ) : ℝ) * b) from funext hexp]
      rw [intervalIntegral.integral_finsetSum]
      · have : ∀ j ∈ Finset.range (N + 1), (∫ b in (-1 / 2 : ℝ)..(1 / 2), ∑ k ∈ Finset.range (N + 1),
            E ((((j : ℤ) - (k : ℤ) : ℤ) : ℝ) * b)) = 1 := by
          intro j hj
          rw [intervalIntegral.integral_finsetSum]
          · simp_rw [tf_orth E hE]
            simp [sub_eq_zero, Finset.mem_range] at hj ⊢
            omega
          · intro k _
            exact (hEc.comp (continuous_const.mul continuous_id)).intervalIntegrable _ _
        rw [Finset.sum_congr rfl this]
        simp
      · intro j _
        apply Continuous.intervalIntegrable
        exact continuous_finsetSum _ fun k _ => hEc.comp (continuous_const.mul continuous_id)
    have h2 : (((∫ b in (-1 / 2 : ℝ)..(1 / 2), ‖K N b‖ ^ 2 : ℝ)) : ℂ) = (((N + 1 : ℕ) : ℝ) : ℂ) := by
      rw [← h1, intervalIntegral.integral_ofReal]
    exact_mod_cast h2
  have hR : ∫ b in W..(1 / 2 : ℝ), ‖K N b‖ ^ 2 ≤ 1 / (4 * W) - 1 / 2 := by
    rw [← tf_int_right W hW0 hW1]
    apply intervalIntegral.integral_mono_on hW1 (hfc.intervalIntegrable _ _)
    · refine (tf_cont _ ?_).intervalIntegrable
      intro x hx
      rw [Set.uIcc_of_le hW1] at hx
      exact (lt_of_lt_of_le hW0 hx.1).ne'
    · intro x hx
      have hx0 : 0 < x := lt_of_lt_of_le hW0 hx.1
      have := tf_tail E hE N x hx0.ne' (by rw [abs_of_pos hx0]; exact hx.2)
      rw [hK N x]; exact this
  have hL : ∫ b in (-1 / 2 : ℝ)..(-W), ‖K N b‖ ^ 2 ≤ 1 / (4 * W) - 1 / 2 := by
    rw [← tf_int_left W hW0 hW1]
    apply intervalIntegral.integral_mono_on (by linarith) (hfc.intervalIntegrable _ _)
    · refine (tf_cont _ ?_).intervalIntegrable
      intro x hx
      rw [Set.uIcc_of_le (by linarith)] at hx
      exact (lt_of_le_of_lt hx.2 (by linarith)).ne
    · intro x hx
      have hx0 : x < 0 := lt_of_le_of_lt hx.2 (by linarith)
      have := tf_tail E hE N x hx0.ne (by rw [abs_of_neg hx0]; linarith [hx.1])
      rw [hK N x]; exact this
  have hs1 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
    (hfc.intervalIntegrable (-1 / 2 : ℝ) (-W)) (hfc.intervalIntegrable (-W) W)
  have hs2 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
    (hfc.intervalIntegrable (-1 / 2 : ℝ) W) (hfc.intervalIntegrable W (1 / 2 : ℝ))
  have hs3 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
    (hfc.intervalIntegrable (-W) W) (hfc.intervalIntegrable W (1 / 2 : ℝ))
  have hs4 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
    (hfc.intervalIntegrable (-1 / 2 : ℝ) (-W)) (hfc.intervalIntegrable (-W) (1 / 2 : ℝ))
  have hh : 1 / (2 * W) = 2 * (1 / (4 * W)) := by field_simp; ring
  linarith

theorem Conjectures.Goldbach.TruncatedFejerArcFloor :
    let E (x : ℝ) := Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I); let K (N : ℕ) (b : ℝ) := ∑ k ∈ Finset.range (N + 1), E ((k : ℝ) * b); ∀ (N : ℕ) (W : ℝ), 0 < W → W ≤ 1 / 2 → ((N + 1 : ℕ) : ℝ) - 1 / (2 * W) ≤ (intervalIntegral (fun b => (K N b)^2 * E (-(N : ℝ) * b)) (-W) W MeasureTheory.volume).re := by
  intro E K N W hW0 hW1
  exact tf_main E (fun _ => rfl) K (fun _ _ => rfl) N W hW0 hW1
