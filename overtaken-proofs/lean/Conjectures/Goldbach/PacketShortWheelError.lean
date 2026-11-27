import Mathlib

open Real

private lemma orth_aux (m : ℕ) (hm : 1 ≤ m) :
    ∫ t in (0:ℝ)..1, Real.cos (2 * π * (m:ℝ) * t) = 0 := by
  have h2 : (2 * π * (m:ℝ)) ≠ 0 := by positivity
  have := intervalIntegral.integral_comp_mul_left (a := (0:ℝ)) (b := 1) (fun x => Real.cos x) h2
  simp only [mul_zero, mul_one] at this
  rw [this, integral_cos]
  have : Real.sin (2 * π * (m:ℝ)) = 0 := by
    have := Real.sin_nat_mul_pi (2 * m)
    rw [show 2 * π * (m:ℝ) = ((2*m : ℕ):ℝ) * π by push_cast; ring]
    exact this
  simp [this]

private abbrev VS (D : ℕ) : Submodule ℝ (ℝ → ℝ) :=
  Submodule.span ℝ {f | ∃ k ≤ D, f = fun t => Real.cos (2 * π * (k:ℝ) * t)}

private lemma VS_mono {D D' : ℕ} (h : D ≤ D') : VS D ≤ VS D' := by
  apply Submodule.span_mono
  rintro f ⟨k, hk, rfl⟩
  exact ⟨k, hk.trans h, rfl⟩

private lemma VS_orth {D M : ℕ} (hDM : D < M) {f : ℝ → ℝ} (hf : f ∈ VS D) :
    Continuous f ∧ ∫ t in (0:ℝ)..1, f t * Real.cos (2 * π * (M:ℝ) * t) = 0 := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨k, hk, rfl⟩ := hf
    refine ⟨by fun_prop, ?_⟩
    have e : ∀ t : ℝ, Real.cos (2 * π * (k:ℝ) * t) * Real.cos (2 * π * (M:ℝ) * t)
        = (Real.cos (2 * π * ((M - k : ℕ):ℝ) * t) + Real.cos (2 * π * ((M + k : ℕ):ℝ) * t)) / 2 := by
      intro t
      rw [Nat.cast_sub (by omega)]; push_cast
      rw [show 2 * π * ((M:ℝ) - k) * t = 2 * π * M * t - 2 * π * k * t by ring,
        show 2 * π * ((M:ℝ) + k) * t = 2 * π * M * t + 2 * π * k * t by ring,
        Real.cos_sub, Real.cos_add]
      ring
    simp only [e]
    rw [intervalIntegral.integral_div, intervalIntegral.integral_add (by apply Continuous.intervalIntegrable; fun_prop) (by apply Continuous.intervalIntegrable; fun_prop),
      orth_aux _ (by omega), orth_aux _ (by omega)]
    simp
  | zero => exact ⟨continuous_const, by simp⟩
  | add f g _ _ hf hg =>
    refine ⟨hf.1.add hg.1, ?_⟩
    simp only [Pi.add_apply, add_mul]
    rw [intervalIntegral.integral_add (by apply Continuous.intervalIntegrable; have := hf.1; fun_prop) (by apply Continuous.intervalIntegrable; have := hg.1; fun_prop), hf.2, hg.2]; simp
  | smul c f _ hf =>
    refine ⟨hf.1.const_smul c, ?_⟩
    simp only [Pi.smul_apply, smul_eq_mul, mul_assoc c]
    rw [intervalIntegral.integral_const_mul, hf.2]; simp

private lemma VS_mul {D M : ℕ} (hDM : D ≤ M) {f : ℝ → ℝ} (hf : f ∈ VS D) :
    (fun t => f t * Real.cos (2 * π * (M:ℝ) * t)) ∈ VS (D + M) := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨k, hk, rfl⟩ := hf
    have e : (fun t : ℝ => Real.cos (2 * π * (k:ℝ) * t) * Real.cos (2 * π * (M:ℝ) * t))
        = (1/2 : ℝ) • (fun t => Real.cos (2 * π * ((M - k : ℕ):ℝ) * t)) + (1/2 : ℝ) • (fun t => Real.cos (2 * π * ((M + k : ℕ):ℝ) * t)) := by
      funext t
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rw [Nat.cast_sub (by omega)]; push_cast
      rw [show 2 * π * ((M:ℝ) - k) * t = 2 * π * M * t - 2 * π * k * t by ring,
        show 2 * π * ((M:ℝ) + k) * t = 2 * π * M * t + 2 * π * k * t by ring,
        Real.cos_sub, Real.cos_add]
      ring
    rw [e]
    refine Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨M - k, by omega, rfl⟩))
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨M + k, by omega, rfl⟩))
  | zero =>
    have : (fun t => (0:ℝ→ℝ) t * Real.cos (2 * π * (M:ℝ) * t)) = 0 := by funext t; simp
    rw [this]; exact Submodule.zero_mem _
  | add f g _ _ hf hg =>
    have : (fun t => (f + g) t * Real.cos (2 * π * (M:ℝ) * t)) = (fun t => f t * Real.cos (2 * π * (M:ℝ) * t)) + (fun t => g t * Real.cos (2 * π * (M:ℝ) * t)) := by
      funext t; simp [add_mul]
    rw [this]; exact Submodule.add_mem _ hf hg
  | smul c f _ hf =>
    have : (fun t => (c • f) t * Real.cos (2 * π * (M:ℝ) * t)) = c • (fun t => f t * Real.cos (2 * π * (M:ℝ) * t)) := by
      funext t; simp [mul_assoc]
    rw [this]; exact Submodule.smul_mem _ _ hf

private lemma riesz (a b : ℝ) (m : ℕ) :
    (fun t : ℝ => ∏ j ∈ Finset.range m, (a + b * Real.cos (2 * π * (2:ℝ)^(j+1) * t))) ∈ VS (2^(m+1) - 1) ∧
    ∫ t in (0:ℝ)..1, ∏ j ∈ Finset.range m, (a + b * Real.cos (2 * π * (2:ℝ)^(j+1) * t)) = a ^ m := by
  induction m with
  | zero =>
    refine ⟨?_, by simp⟩
    simp only [Finset.range_zero, Finset.prod_empty]
    have : (fun _ : ℝ => (1:ℝ)) = (fun t => Real.cos (2 * π * ((0:ℕ):ℝ) * t)) := by funext t; simp
    rw [this]; exact Submodule.subset_span ⟨0, by omega, rfl⟩
  | succ m ih =>
    obtain ⟨h1, h2⟩ := ih
    have hp : (2:ℕ)^(m+1) ≥ 1 := Nat.one_le_two_pow
    have hM : (2^(m+1) - 1 : ℕ) ≤ 2^(m+1) := by omega
    have hmul := VS_mul hM h1
    have e : (fun t : ℝ => ∏ j ∈ Finset.range (m+1), (a + b * Real.cos (2 * π * (2:ℝ)^(j+1) * t)))
        = a • (fun t : ℝ => ∏ j ∈ Finset.range m, (a + b * Real.cos (2 * π * (2:ℝ)^(j+1) * t)))
          + b • (fun t => (∏ j ∈ Finset.range m, (a + b * Real.cos (2 * π * (2:ℝ)^(j+1) * t))) * Real.cos (2 * π * ((2^(m+1) : ℕ):ℝ) * t)) := by
      funext t
      simp only [Finset.prod_range_succ, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      push_cast
      ring
    have hle : (2^(m+1) - 1 + 2^(m+1) : ℕ) = 2^(m+1+1) - 1 := by
      rw [pow_succ 2 (m+1)]; omega
    have hmem : (fun t : ℝ => ∏ j ∈ Finset.range (m+1), (a + b * Real.cos (2 * π * (2:ℝ)^(j+1) * t))) ∈ VS (2^(m+1+1) - 1) := by
      rw [e]
      refine Submodule.add_mem _ (Submodule.smul_mem _ _ (VS_mono (by rw [pow_succ 2 (m+1)]; omega) h1))
        (Submodule.smul_mem _ _ ?_)
      rw [← hle]; exact hmul
    refine ⟨hmem, ?_⟩
    have horth := (VS_orth (D := 2^(m+1) - 1) (M := 2^(m+1)) (by omega) h1)
    have hc := horth.1
    have hfun := congrFun e
    have : ∫ t in (0:ℝ)..1, ∏ j ∈ Finset.range (m+1), (a + b * Real.cos (2 * π * (2:ℝ)^(j+1) * t))
        = ∫ t in (0:ℝ)..1, (a * ∏ j ∈ Finset.range m, (a + b * Real.cos (2 * π * (2:ℝ)^(j+1) * t))
          + b * ((∏ j ∈ Finset.range m, (a + b * Real.cos (2 * π * (2:ℝ)^(j+1) * t))) * Real.cos (2 * π * ((2^(m+1) : ℕ):ℝ) * t))) := by
      refine intervalIntegral.integral_congr (fun t _ => ?_)
      have := hfun t
      simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] using this
    rw [this, intervalIntegral.integral_add (by apply Continuous.intervalIntegrable; have := hc; fun_prop) (by apply Continuous.intervalIntegrable; have := hc; fun_prop),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
    have h3 : ∫ t in (0:ℝ)..1, (∏ j ∈ Finset.range m, (a + b * Real.cos (2 * π * (2:ℝ)^(j+1) * t))) * Real.cos (2 * π * ((2^(m+1) : ℕ):ℝ) * t) = 0 := horth.2
    rw [h3, h2]; ring

private lemma exp_half_le (c : ℝ) (h1 : -1 ≤ c) (h2 : c ≤ 1) :
    Real.exp (c / 2) ≤ Real.cosh (1/2) + Real.sinh (1/2) * c := by
  have := convexOn_exp.2 (Set.mem_univ (1/2 : ℝ)) (Set.mem_univ (-(1/2) : ℝ))
    (show (0:ℝ) ≤ (1 + c)/2 by linarith) (show (0:ℝ) ≤ (1 - c)/2 by linarith) (by ring)
  simp only [smul_eq_mul] at this
  have e : (1 + c) / 2 * (1/2) + (1 - c) / 2 * (-(1/2)) = c / 2 := by ring
  rw [e] at this
  refine this.trans (le_of_eq ?_)
  rw [Real.cosh_eq, Real.sinh_eq, Real.exp_neg]
  have : Real.exp (-(1/2:ℝ)) = (Real.exp (1/2))⁻¹ := Real.exp_neg _
  rw [Real.exp_neg] at *
  ring

private lemma V_bound (B : Set ℝ) (L : ℕ) (hL : 1 ≤ L)
    (hB : ∀ t ∈ B, 1/2 < (∑ j ∈ Finset.range L, Real.cos (2 * π * (2:ℝ)^(j+1) * t)) / (L:ℝ))
    (f : ℝ → ℝ) (hf : ∀ t, |f t| ≤ 1) :
    |∫ t in (0:ℝ)..1, B.indicator f t| ≤ Real.exp (-(L:ℝ)/8) := by
  obtain ⟨hmem, hint⟩ := riesz (Real.cosh (1/2)) (Real.sinh (1/2)) L
  have hcont := (VS_orth (D := 2^(L+1) - 1) (M := 2^(L+1)) (by have := @Nat.one_le_two_pow (L+1); omega) hmem).1
  have hLpos : (0:ℝ) < L := by exact_mod_cast hL
  have hpt : ∀ t, ‖B.indicator f t‖ ≤ Real.exp (-(L:ℝ)/4) *
      ∏ j ∈ Finset.range L, (Real.cosh (1/2) + Real.sinh (1/2) * Real.cos (2 * π * (2:ℝ)^(j+1) * t)) := by
    intro t
    have hprod : 0 ≤ ∏ j ∈ Finset.range L, (Real.cosh (1/2) + Real.sinh (1/2) * Real.cos (2 * π * (2:ℝ)^(j+1) * t)) := by
      apply Finset.prod_nonneg
      intro j _
      exact (Real.exp_pos _).le.trans (exp_half_le _ (Real.neg_one_le_cos _) (Real.cos_le_one _))
    by_cases ht : t ∈ B
    · rw [Set.indicator_of_mem ht, Real.norm_eq_abs]
      refine (hf t).trans ?_
      have hs := hB t ht
      rw [lt_div_iff₀ hLpos] at hs
      have h1 : Real.exp ((L:ℝ)/4) ≤ ∏ j ∈ Finset.range L, Real.exp (Real.cos (2 * π * (2:ℝ)^(j+1) * t) / 2) := by
        rw [← Real.exp_sum, Real.exp_le_exp, ← Finset.sum_div]
        linarith
      have h2 : ∏ j ∈ Finset.range L, Real.exp (Real.cos (2 * π * (2:ℝ)^(j+1) * t) / 2) ≤ ∏ j ∈ Finset.range L, (Real.cosh (1/2) + Real.sinh (1/2) * Real.cos (2 * π * (2:ℝ)^(j+1) * t)) := by
        gcongr with j hj
        exact exp_half_le _ (Real.neg_one_le_cos _) (Real.cos_le_one _)
      have h3 := h1.trans h2
      have h4 : (1:ℝ) = Real.exp (-(L:ℝ)/4) * Real.exp ((L:ℝ)/4) := by
        have : -(L:ℝ)/4 + L/4 = 0 := by ring
        rw [← Real.exp_add, this, Real.exp_zero]
      calc (1:ℝ) = Real.exp (-(L:ℝ)/4) * Real.exp ((L:ℝ)/4) := h4
        _ ≤ _ := mul_le_mul_of_nonneg_left h3 (Real.exp_pos _).le
    · rw [Set.indicator_of_notMem ht]
      try simp only [norm_zero]
      positivity
  have hQc : Continuous (fun t : ℝ => ∏ j ∈ Finset.range L, (Real.cosh (1/2) + Real.sinh (1/2) * Real.cos (2 * π * (2:ℝ)^(j+1) * t))) := hcont
  have := intervalIntegral.norm_integral_le_of_norm_le (a := (0:ℝ)) (b := 1) (μ := MeasureTheory.volume)
    (f := fun t => B.indicator f t)
    (g := fun t => Real.exp (-(L:ℝ)/4) * ∏ j ∈ Finset.range L, (Real.cosh (1/2) + Real.sinh (1/2) * Real.cos (2 * π * (2:ℝ)^(j+1) * t)))
    zero_le_one (Filter.Eventually.of_forall (fun t _ => hpt t))
    (by apply Continuous.intervalIntegrable; exact continuous_const.mul hQc)
  rw [intervalIntegral.integral_const_mul, hint] at this
  rw [← Real.norm_eq_abs]
  refine this.trans ?_
  have ha : Real.cosh (1/2) ≤ Real.exp (1/8) := by
    refine (Real.cosh_le_exp_half_sq _).trans (le_of_eq ?_)
    norm_num
  have hpos : 0 ≤ Real.cosh (1/2) := (Real.cosh_pos _).le
  calc Real.exp (-(L:ℝ)/4) * Real.cosh (1/2) ^ L ≤ Real.exp (-(L:ℝ)/4) * (Real.exp (1/8)) ^ L := by gcongr
    _ = Real.exp (-(L:ℝ)/8) := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]; congr 1; ring

private lemma short_bound (n m : ℕ) (hm : m ≤ n) (a : ℕ → ℝ) (C β : ℝ) (hC : 0 ≤ C)
    (ha : ∀ k ≤ n, |a k| ≤ C) (V : ℕ → ℝ) (hV : ∀ h, |V h| ≤ β) :
    |(∑ k ∈ Finset.range (n+1-0), a k * a (k+0)) * V 0 +
      2 * (∑ h ∈ Finset.Icc 1 m, (∑ k ∈ Finset.range (n+1-h), a k * a (k+h)) * V h)|
      ≤ β * (1 + 2 * m) * ((n+1) * C^2) := by
  have hβ : 0 ≤ β := (abs_nonneg _).trans (hV 0)
  have hA : ∀ h, h ≤ n → |∑ k ∈ Finset.range (n+1-h), a k * a (k+h)| ≤ (n+1) * C^2 := by
    intro h hh
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ k ∈ Finset.range (n+1-h), |a k * a (k+h)| ≤ ∑ k ∈ Finset.range (n+1-h), C^2 := by
          apply Finset.sum_le_sum
          intro k hk
          rw [Finset.mem_range] at hk
          rw [abs_mul, sq]
          exact mul_le_mul (ha k (by omega)) (ha (k+h) (by omega)) (abs_nonneg _) hC
      _ = ((n+1-h : ℕ):ℝ) * C^2 := by simp
      _ ≤ (n+1) * C^2 := by
          gcongr
          have : n + 1 - h ≤ n + 1 := Nat.sub_le _ _
          exact_mod_cast this
  have h0 : |(∑ k ∈ Finset.range (n+1-0), a k * a (k+0)) * V 0| ≤ β * ((n+1) * C^2) := by
    rw [abs_mul]
    calc _ ≤ ((n+1) * C^2) * β := mul_le_mul (hA 0 (Nat.zero_le _)) (hV 0) (abs_nonneg _) (by positivity)
      _ = _ := by ring
  have hs : |∑ h ∈ Finset.Icc 1 m, (∑ k ∈ Finset.range (n+1-h), a k * a (k+h)) * V h| ≤ m * (β * ((n+1) * C^2)) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc _ ≤ ∑ h ∈ Finset.Icc 1 m, β * ((n+1) * C^2) := by
          apply Finset.sum_le_sum
          intro h hh
          rw [Finset.mem_Icc] at hh
          rw [abs_mul]
          calc _ ≤ ((n+1) * C^2) * β := mul_le_mul (hA h (by omega)) (hV h) (abs_nonneg _) (by positivity)
            _ = _ := by ring
      _ = m * (β * ((n+1) * C^2)) := by simp
  calc _ ≤ |(∑ k ∈ Finset.range (n+1-0), a k * a (k+0)) * V 0| + |2 * (∑ h ∈ Finset.Icc 1 m, (∑ k ∈ Finset.range (n+1-h), a k * a (k+h)) * V h)| := abs_add_le _ _
    _ ≤ β * ((n+1) * C^2) + 2 * (m * (β * ((n+1) * C^2))) := by
        have h2 : |2 * ∑ h ∈ Finset.Icc 1 m, (∑ k ∈ Finset.range (n+1-h), a k * a (k+h)) * V h| = 2 * |∑ h ∈ Finset.Icc 1 m, (∑ k ∈ Finset.range (n+1-h), a k * a (k+h)) * V h| := by
          rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2)]
        linarith
    _ = _ := by ring

private lemma num_bound : ∃ N : ℕ, 2 ≤ N ∧ ∀ n ≥ N,
    Real.exp (-((max 1 (Nat.log 2 n / 2) : ℕ):ℝ)/8) * (1 + 2 * (((max 1 (Nat.log 2 n / 2))^2 : ℕ):ℝ)) *
      ((n+1) * ((Real.log n)^2 + 16)) ≤ (n:ℝ) / 2304 / 2 := by
  have ht := tendsto_pow_const_mul_const_pow_of_abs_lt_one 4 (r := Real.exp (-1/8)) (by
    rw [abs_of_pos (Real.exp_pos _)]
    rw [← Real.exp_zero]; exact Real.exp_lt_exp.2 (by norm_num))
  have hev := (ht.eventually (gt_mem_nhds (show (0:ℝ) < 1/(200 * 2304 * 2) by norm_num)))
  rw [Filter.eventually_atTop] at hev
  obtain ⟨K0, hK0⟩ := hev
  refine ⟨max 2 (2^(2*K0)), le_max_left _ _, ?_⟩
  intro n hn
  have hn2 : 2 ≤ n := (le_max_left _ _).trans hn
  have hn3 : 2^(2*K0) ≤ n := (le_max_right _ _).trans hn
  set ℓ := Nat.log 2 n with hℓ
  have hℓK : 2 * K0 ≤ ℓ := Nat.le_log_of_pow_le (by norm_num) hn3
  set L := max 1 (ℓ / 2) with hL
  have hLK : K0 ≤ L := by omega
  have hL1 : 1 ≤ L := by omega
  have hlogn : Real.log n ≤ 4 * (L:ℝ) := by
    have h1 : n < 2^(ℓ+1) := Nat.lt_pow_succ_log_self (by norm_num) n
    have h2 : Real.log n ≤ ((ℓ+1 : ℕ):ℝ) * Real.log 2 := by
      rw [← Real.log_pow]
      apply Real.log_le_log (by positivity)
      exact_mod_cast h1.le
    have h3 : Real.log 2 ≤ 1 := by
      have := Real.log_two_lt_d9; linarith
    have h4 : ((ℓ+1 : ℕ):ℝ) ≤ 4 * (L:ℝ) := by
      have : ℓ + 1 ≤ 4 * L := by omega
      exact_mod_cast this
    have h5 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    calc Real.log n ≤ ((ℓ+1 : ℕ):ℝ) * Real.log 2 := h2
      _ ≤ ((ℓ+1 : ℕ):ℝ) * 1 := by gcongr
      _ ≤ _ := by linarith
  have hlog0 : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n))
  have hx : (1:ℝ) ≤ L := by exact_mod_cast hL1
  have hk := hK0 L hLK
  have hexp : Real.exp (-1/8) ^ L = Real.exp (-(L:ℝ)/8) := by
    rw [← Real.exp_nat_mul]; congr 1; ring
  rw [hexp] at hk
  have hnR : (2:ℝ) ≤ n := by exact_mod_cast hn2
  have hE := Real.exp_pos (-(L:ℝ)/8)
  have hsq : (((L)^2 : ℕ):ℝ) = (L:ℝ)^2 := by push_cast; ring
  rw [hsq]
  have hl2 : (Real.log n)^2 + 16 ≤ 32 * (L:ℝ)^2 := by nlinarith
  have hA : 1 + 2 * (L:ℝ)^2 ≤ 3 * (L:ℝ)^2 := by nlinarith
  have hB : ((n:ℝ)+1) ≤ 2 * n := by linarith
  calc Real.exp (-(L:ℝ)/8) * (1 + 2 * (L:ℝ)^2) * ((n+1) * ((Real.log n)^2 + 16))
      ≤ Real.exp (-(L:ℝ)/8) * (3 * (L:ℝ)^2) * ((2 * n) * (32 * (L:ℝ)^2)) := by
        gcongr
    _ = (192 * ((L:ℝ)^4 * Real.exp (-(L:ℝ)/8))) * n := by ring
    _ ≤ (192 * (1/(200 * 2304 * 2))) * n := by gcongr
    _ ≤ _ := by
        have : (0:ℝ) ≤ n := by positivity
        nlinarith

theorem Conjectures.Goldbach.PacketShortWheelError :
    let w := fun k : ℕ => if Nat.Prime k then Real.log (k:ℝ) else 0; let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let S := fun (n : ℕ) (w : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (w k:ℂ)*E ((k:ℝ)*t)); let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let arcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (Q n:ℝ)/((q:ℝ)*(n:ℝ))}; let low := fun (n k : ℕ) => if k^3≤n then w k else 0; let high := fun (n k : ℕ) => w k-low n k; let I := fun (n:ℕ) (a b:ℕ→ℝ) => intervalIntegral (fun t => (arcs n)ᶜ.indicator (fun u => S n a u*S n b u*E (-(n:ℝ)*u)) t) (0:ℝ) 1 MeasureTheory.volume; let L := fun n : ℕ => max 1 (Nat.log 2 n / 2); let K := fun (n : ℕ) (t : ℝ) => (∑ j ∈ Finset.range (L n), Real.cos (2*Real.pi*(2:ℝ)^(j+1)*t))/(L n:ℝ); let B := fun n : ℕ => {t : ℝ | t ∉ arcs n ∧ (1:ℝ)/2 < K n t}; let U := fun (n : ℕ) (a : ℕ → ℝ) => intervalIntegral ((B n).indicator (fun t => ‖S n a t‖^2)) (0:ℝ) 1 MeasureTheory.volume; let V := fun (n h : ℕ) => intervalIntegral ((B n).indicator (fun t => Real.cos (2*Real.pi*(h:ℝ)*t))) (0:ℝ) 1 MeasureTheory.volume; let A := fun (n h : ℕ) (a : ℕ → ℝ) => ∑ k ∈ Finset.range (n+1-h), a k * a (k+h); let model := fun k : ℕ => if Nat.Coprime k 30 then (30:ℝ)/8 else 0; let short := fun (n : ℕ) (a : ℕ → ℝ) => A n 0 a * V n 0 + 2*(∑ h ∈ Finset.Icc 1 (min n ((L n)^2)), A n h a * V n h); let long := fun (n : ℕ) (a : ℕ → ℝ) => 2*(∑ h ∈ Finset.Icc ((L n)^2+1) n, A n h a * V n h); ∃ N : ℕ, ∀ n ≥ N, Even n → |short n (high n) - short n model| ≤ (n:ℝ)/2304 := by
  intro w E S Q arcs low high I L K B U V A model short long
  obtain ⟨N, hN2, hN⟩ := num_bound
  refine ⟨N, fun n hn _ => ?_⟩
  have hn2 : 2 ≤ n := hN2.trans hn
  have hLn : 1 ≤ L n := le_max_left _ _
  have hVb : ∀ h, |V n h| ≤ Real.exp (-((L n : ℕ):ℝ)/8) := fun h =>
    V_bound (B n) (L n) hLn (fun t ht => ht.2) (fun t => Real.cos (2 * π * (h:ℝ) * t)) (fun t => Real.abs_cos_le_one _)
  have hm : min n ((L n)^2) ≤ n := min_le_left _ _
  have hmL : (min n ((L n)^2) : ℕ) ≤ (L n)^2 := min_le_right _ _
  have hhigh : ∀ k ≤ n, |high n k| ≤ Real.log n := by
    intro k hk
    have : high n k = if k^3 ≤ n then 0 else w k := by
      simp only [high, low]
      split_ifs <;> simp
    rw [this]
    have hlog : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n))
    split_ifs
    · simpa using hlog
    · simp only [w]
      split_ifs with hp
      · have := hp.two_le
        rw [abs_of_nonneg (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ k)))]
        exact Real.log_le_log (by positivity) (by exact_mod_cast hk)
      · simpa using hlog
  have hmod : ∀ k ≤ n, |model k| ≤ 4 := by
    intro k _
    simp only [model]
    split_ifs
    · rw [abs_of_pos (by norm_num)]; norm_num
    · norm_num
  have h1 := short_bound n _ hm (high n) (Real.log n) (Real.exp (-((L n : ℕ):ℝ)/8))
    (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n))) hhigh (V n) hVb
  have h2 := short_bound n _ hm model 4 (Real.exp (-((L n : ℕ):ℝ)/8)) (by norm_num) hmod (V n) hVb
  have hN' := hN n hn
  have hE := Real.exp_pos (-((L n : ℕ):ℝ)/8)
  have hmR : ((min n ((L n)^2) : ℕ):ℝ) ≤ (((L n)^2 : ℕ):ℝ) := by exact_mod_cast hmL
  have hlog : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n))
  have key : |short n (high n) - short n model| ≤ |short n (high n)| + |short n model| := abs_sub _ _
  have e1 : |short n (high n)| ≤ Real.exp (-((L n : ℕ):ℝ)/8) * (1 + 2 * (((L n)^2 : ℕ):ℝ)) * ((n+1) * (Real.log n)^2) := by
    refine h1.trans ?_
    have : (0:ℝ) ≤ (n+1) * (Real.log n)^2 := by positivity
    gcongr
  have e2 : |short n model| ≤ Real.exp (-((L n : ℕ):ℝ)/8) * (1 + 2 * (((L n)^2 : ℕ):ℝ)) * ((n+1) * 4^2) := by
    refine h2.trans ?_
    gcongr
  have hsum : Real.exp (-((L n : ℕ):ℝ)/8) * (1 + 2 * (((L n)^2 : ℕ):ℝ)) * ((n+1) * (Real.log n)^2) +
      Real.exp (-((L n : ℕ):ℝ)/8) * (1 + 2 * (((L n)^2 : ℕ):ℝ)) * ((n+1) * 4^2)
      = Real.exp (-((L n : ℕ):ℝ)/8) * (1 + 2 * (((L n)^2 : ℕ):ℝ)) * ((n+1) * ((Real.log n)^2 + 16)) := by ring
  have : (n:ℝ) / 2304 / 2 + (n:ℝ) / 2304 / 2 = (n:ℝ)/2304 := by ring
  linarith
