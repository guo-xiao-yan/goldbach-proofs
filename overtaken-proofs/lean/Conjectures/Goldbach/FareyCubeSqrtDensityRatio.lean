import Mathlib

open Finset Real Chebyshev

private lemma hasDeriv_f (t : ℝ) (ht : 1 < t) :
    HasDerivAt (fun x : ℝ => (x * Real.log x)⁻¹) (-((Real.log t + 1) / (t * Real.log t)^2)) t := by
  have h0 : t ≠ 0 := by linarith
  have hl : Real.log t ≠ 0 := (Real.log_pos ht).ne'
  have h1 : HasDerivAt (fun x : ℝ => x * Real.log x) (Real.log t + 1) t := by
    have := (hasDerivAt_id t).mul (Real.hasDerivAt_log h0)
    convert this using 1
    all_goals first | rfl | (simp only [id]; rw [mul_inv_cancel₀ h0]; ring)
  have := h1.inv (mul_ne_zero h0 hl)
  convert this using 1
  ring

private lemma abel_block (a b : ℕ) (ha : 2 ≤ a) (hab : a ≤ b) :
    ∑ p ∈ (Ioc a b).filter Nat.Prime, (1 / (p:ℝ)) =
      θ b / (b * Real.log b) - θ a / (a * Real.log a)
        + ∫ t in (a:ℝ)..b, θ t * ((Real.log t + 1) / (t * Real.log t)^2) := by
  have ha' : (2:ℝ) ≤ a := by exact_mod_cast ha
  have hab' : (a:ℝ) ≤ b := by exact_mod_cast hab
  have key := sum_mul_eq_sub_sub_integral_mul (fun k : ℕ => if k.Prime then Real.log k else 0)
    (f := fun x : ℝ => (x * Real.log x)⁻¹) (a := (a:ℝ)) (b := (b:ℝ)) (by positivity) hab'
    (fun t ht => (hasDeriv_f t (by linarith [ht.1])).differentiableAt) (by
      apply ContinuousOn.integrableOn_Icc
      have : ∀ t ∈ Set.Icc (a:ℝ) b, deriv (fun x : ℝ => (x * Real.log x)⁻¹) t = -((Real.log t + 1) / (t * Real.log t)^2) :=
        fun t ht => (hasDeriv_f t (by linarith [ht.1])).deriv
      refine ContinuousOn.congr ?_ this
      have : ∀ t ∈ Set.Icc (a:ℝ) b, t ≠ 0 ∧ Real.log t ≠ 0 := fun t ht =>
        ⟨by linarith [ht.1], (Real.log_pos (by linarith [ht.1])).ne'⟩
      apply ContinuousOn.neg
      apply ContinuousOn.div
      · exact (Real.continuousOn_log.mono (fun t ht => (this t ht).1)).add continuousOn_const
      · exact (continuousOn_id.mul (Real.continuousOn_log.mono (fun t ht => (this t ht).1))).pow 2
      · intro t ht; show (t * Real.log t)^2 ≠ 0; exact pow_ne_zero _ (mul_ne_zero (this t ht).1 (this t ht).2))
  simp only [Nat.floor_natCast] at key
  have h1 : ∀ m : ℕ, ∑ k ∈ Icc 0 m, (if k.Prime then Real.log k else 0) = θ m := by
    intro m
    rw [theta_eq_sum_Icc]; simp [Nat.floor_natCast, sum_filter]
  have h2 : ∀ t : ℝ, ∑ k ∈ Icc 0 ⌊t⌋₊, (if k.Prime then Real.log k else 0) = θ t := by
    intro t
    rw [theta_eq_sum_Icc]; simp [sum_filter]
  simp only [h1, ← theta_eq_theta_coe_floor] at key
  have h3 : ∑ k ∈ Ioc a b, (↑k * Real.log ↑k)⁻¹ * (if k.Prime then Real.log k else 0)
      = ∑ p ∈ (Ioc a b).filter Nat.Prime, (1 / (p:ℝ)) := by
    rw [sum_filter]
    refine sum_congr rfl fun k hk => ?_
    split_ifs with h
    · have : Real.log k ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one (by exact_mod_cast h.pos) (by exact_mod_cast h.ne_one)
      have : (k:ℝ) ≠ 0 := by exact_mod_cast h.ne_zero
      field_simp
    · simp
  rw [h3] at key
  rw [key, intervalIntegral.integral_of_le hab']
  have h4 : ∫ t in Set.Ioc (a:ℝ) b, deriv (fun x : ℝ => (x * Real.log x)⁻¹) t * θ t
      = -∫ t in Set.Ioc (a:ℝ) b, θ t * ((Real.log t + 1) / (t * Real.log t)^2) := by
    rw [← MeasureTheory.integral_neg]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioc fun t ht => ?_
    rw [(hasDeriv_f t (by linarith [ht.1])).deriv]; ring
  rw [h4]; ring
private lemma hasDeriv_G (t : ℝ) (ht : 1 < t) :
    HasDerivAt (fun x : ℝ => Real.log (Real.log x) - (Real.log x)⁻¹)
      (t * ((Real.log t + 1) / (t * Real.log t)^2)) t := by
  have h0 : t ≠ 0 := by linarith
  have hl : Real.log t ≠ 0 := (Real.log_pos ht).ne'
  have h1 := Real.hasDerivAt_log h0
  have h2 := h1.log hl
  have h3 := h1.inv hl
  have h4 := h2.sub h3
  convert h4 using 1
  field_simp
  ring

private lemma block_est (a b : ℕ) (ha : 2 ≤ a) (hab : a ≤ b) (δ : ℝ) (hδ : 0 ≤ δ)
    (hθ : ∀ t : ℝ, (a:ℝ) ≤ t → |θ t / t - 1| ≤ δ) :
    (1 - δ) * ((Real.log (Real.log b) - (Real.log b)⁻¹) - (Real.log (Real.log a) - (Real.log a)⁻¹))
      ≤ ∫ t in (a:ℝ)..b, θ t * ((Real.log t + 1) / (t * Real.log t)^2) ∧
    ∫ t in (a:ℝ)..b, θ t * ((Real.log t + 1) / (t * Real.log t)^2) ≤
      (1 + δ) * ((Real.log (Real.log b) - (Real.log b)⁻¹) - (Real.log (Real.log a) - (Real.log a)⁻¹)) := by
  have ha' : (2:ℝ) ≤ a := by exact_mod_cast ha
  have hab' : (a:ℝ) ≤ b := by exact_mod_cast hab
  have hpos : ∀ t ∈ Set.uIcc (a:ℝ) b, 1 < t := by
    intro t ht
    rw [Set.uIcc_of_le hab'] at ht
    linarith [ht.1]
  have hcont : ContinuousOn (fun t : ℝ => (Real.log t + 1) / (t * Real.log t)^2) (Set.uIcc (a:ℝ) b) := by
    have : ∀ t ∈ Set.uIcc (a:ℝ) b, t ≠ 0 ∧ Real.log t ≠ 0 := fun t ht =>
      ⟨by linarith [hpos t ht], (Real.log_pos (hpos t ht)).ne'⟩
    apply ContinuousOn.div
    · exact (Real.continuousOn_log.mono (fun t ht => (this t ht).1)).add continuousOn_const
    · exact (continuousOn_id.mul (Real.continuousOn_log.mono (fun t ht => (this t ht).1))).pow 2
    · intro t ht; show (t * Real.log t)^2 ≠ 0; exact pow_ne_zero _ (mul_ne_zero (this t ht).1 (this t ht).2)
  have hint1 : IntervalIntegrable (fun t : ℝ => θ t * ((Real.log t + 1) / (t * Real.log t)^2))
      MeasureTheory.volume (a:ℝ) b :=
    (Chebyshev.theta_mono.intervalIntegrable).mul_continuousOn hcont
  have hcont2 : ContinuousOn (fun t : ℝ => t * ((Real.log t + 1) / (t * Real.log t)^2)) (Set.uIcc (a:ℝ) b) :=
    continuousOn_id.mul hcont
  have hint2 : IntervalIntegrable (fun t : ℝ => t * ((Real.log t + 1) / (t * Real.log t)^2))
      MeasureTheory.volume (a:ℝ) b := hcont2.intervalIntegrable
  have hG := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun x : ℝ => Real.log (Real.log x) - (Real.log x)⁻¹)
    (fun t ht => hasDeriv_G t (hpos t ht)) hint2
  have hnn : ∀ t ∈ Set.Icc (a:ℝ) b, 0 ≤ (Real.log t + 1) / (t * Real.log t)^2 := by
    intro t ht
    have : 0 < Real.log t := Real.log_pos (by linarith [ht.1])
    positivity
  have hb : ∀ t ∈ Set.Icc (a:ℝ) b, (1 - δ) * t ≤ θ t ∧ θ t ≤ (1 + δ) * t := by
    intro t ht
    have h := hθ t ht.1
    have tp : 0 < t := by linarith [ht.1]
    rw [abs_le] at h
    have e : θ t = (θ t / t) * t := by field_simp
    constructor
    · rw [e]; nlinarith [h.1]
    · rw [e]; nlinarith [h.2]
  constructor
  · rw [← hG, ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on hab' (hint2.const_mul _) hint1
    intro t ht
    have := (hb t ht).1
    have h2 := hnn t ht
    calc (1 - δ) * (t * ((Real.log t + 1) / (t * Real.log t)^2))
        = ((1 - δ) * t) * ((Real.log t + 1) / (t * Real.log t)^2) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right this h2
  · rw [← hG, ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on hab' hint1 (hint2.const_mul _)
    intro t ht
    have := (hb t ht).2
    have h2 := hnn t ht
    calc _ ≤ ((1 + δ) * t) * ((Real.log t + 1) / (t * Real.log t)^2) :=
          mul_le_mul_of_nonneg_right this h2
      _ = _ := by ring

private lemma mertens_block (η : ℝ) (hη : 0 < η) : ∃ X : ℕ, ∀ a b : ℕ, X ≤ a → a ≤ b →
    |∑ p ∈ (Ioc a b).filter Nat.Prime, (1 / (p:ℝ)) -
      (Real.log (Real.log b) - Real.log (Real.log a))| ≤
      η * (Real.log (Real.log b) - Real.log (Real.log a)) + η := by
  set δ : ℝ := min (η/2) (1/2) with hδdef
  have hδ0 : 0 < δ := lt_min (by linarith) (by norm_num)
  have hδη : δ ≤ η/2 := min_le_left _ _
  have hδ2 : δ ≤ 1/2 := min_le_right _ _
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 tendsto_theta_div_atTop δ hδ0
  refine ⟨max (max 2 ⌈N⌉₊) ⌈Real.exp (3/η)⌉₊, ?_⟩
  intro a b hXa hab
  have ha2 : 2 ≤ a := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hXa
  have haN : N ≤ (a:ℝ) := by
    have : ⌈N⌉₊ ≤ a := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hXa
    exact le_trans (Nat.le_ceil N) (by exact_mod_cast this)
  have haE : Real.exp (3/η) ≤ (a:ℝ) := by
    have : ⌈Real.exp (3/η)⌉₊ ≤ a := le_trans (le_max_right _ _) hXa
    exact le_trans (Nat.le_ceil _) (by exact_mod_cast this)
  have ha' : (2:ℝ) ≤ a := by exact_mod_cast ha2
  have hab' : (a:ℝ) ≤ b := by exact_mod_cast hab
  have hθ : ∀ t : ℝ, (a:ℝ) ≤ t → |θ t / t - 1| ≤ δ := by
    intro t ht
    have := hN t (le_trans haN ht)
    rw [Real.dist_eq] at this
    exact this.le
  obtain ⟨hlo, hhi⟩ := block_est a b ha2 hab δ hδ0.le hθ
  have hS := abel_block a b ha2 hab
  rw [hS]
  have hLa : 3/η ≤ Real.log a := by
    have := Real.log_le_log (Real.exp_pos _) haE
    rwa [Real.log_exp] at this
  have hLa0 : 0 < Real.log a := lt_of_lt_of_le (by positivity) hLa
  have hLab : Real.log a ≤ Real.log b := Real.log_le_log (by linarith) hab'
  have hLb0 : 0 < Real.log b := lt_of_lt_of_le hLa0 hLab
  have hD : Real.log (Real.log a) ≤ Real.log (Real.log b) := Real.log_le_log hLa0 hLab
  set D := Real.log (Real.log b) - Real.log (Real.log a) with hDdef
  have hD0 : 0 ≤ D := by linarith
  have hinv : (Real.log b)⁻¹ ≤ (Real.log a)⁻¹ := inv_anti₀ hLa0 hLab
  have hinv0 : 0 ≤ (Real.log b)⁻¹ := by positivity
  have hinva : (Real.log a)⁻¹ ≤ η/3 := by
    rw [inv_le_comm₀ hLa0 (by positivity)]
    simpa [inv_div] using hLa
  have hθb := hθ b hab'
  have hθa := hθ a le_rfl
  have hb0 : (0:ℝ) < b := by linarith
  have ha0 : (0:ℝ) < a := by linarith
  have hθb0 : 0 ≤ θ b := Chebyshev.theta_nonneg _
  have hθa0 : 0 ≤ θ a := Chebyshev.theta_nonneg _
  have eb : θ b / (b * Real.log b) = (θ b / b) * (Real.log b)⁻¹ := by field_simp
  have ea : θ a / (a * Real.log a) = (θ a / a) * (Real.log a)⁻¹ := by field_simp
  have hb1 : 0 ≤ θ b / b := by positivity
  have ha1 : 0 ≤ θ a / a := by positivity
  rw [abs_le] at hθb hθa
  rw [eb, ea]
  rw [abs_le]
  constructor
  · nlinarith [mul_le_mul_of_nonneg_right hθa.2 (inv_nonneg.2 hLa0.le), mul_nonneg hb1 hinv0,
      mul_nonneg hδ0.le (sub_nonneg.2 hinv)]
  · nlinarith [mul_le_mul_of_nonneg_right hθb.2 hinv0, mul_nonneg ha1 (inv_nonneg.2 hLa0.le),
      mul_nonneg hδ0.le hD0, mul_nonneg hδ0.le hinv0]

private lemma S_tendsto (a b : ℕ → ℕ) (L : ℝ) (ha : Filter.Tendsto a Filter.atTop Filter.atTop)
    (hab : ∀ᶠ n in Filter.atTop, a n ≤ b n)
    (hD : Filter.Tendsto (fun n => Real.log (Real.log (b n)) - Real.log (Real.log (a n))) Filter.atTop (nhds L)) :
    Filter.Tendsto (fun n => ∑ p ∈ (Ioc (a n) (b n)).filter Nat.Prime, (1 / (p:ℝ))) Filter.atTop (nhds L) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  set K : ℝ := |L| + 2 with hK
  have hK0 : 0 < K := by positivity
  set η : ℝ := ε / (4 * K) with hη
  have hη0 : 0 < η := by positivity
  obtain ⟨X, hX⟩ := mertens_block η hη0
  have h1 : ∀ᶠ n in Filter.atTop, X ≤ a n := ha.eventually_ge_atTop X
  have h2 : ∀ᶠ n in Filter.atTop, dist (Real.log (Real.log (b n)) - Real.log (Real.log (a n))) L < min 1 (ε/2) :=
    (Metric.tendsto_nhds.1 hD) _ (lt_min one_pos (by linarith))
  filter_upwards [h1, hab, h2] with n h1 h2 h3
  have h4 := hX (a n) (b n) h1 h2
  rw [Real.dist_eq] at h3 ⊢
  have h5 := lt_min_iff.1 h3
  have h6 := abs_lt.1 h5.1
  have hLK : L ≤ |L| := le_abs_self L
  have h7 : η * (Real.log (Real.log (b n)) - Real.log (Real.log (a n))) + η ≤ η * K := by
    have : Real.log (Real.log (b n)) - Real.log (Real.log (a n)) ≤ K - 1 := by
      simp only [hK]; linarith [h6.2]
    nlinarith
  have h8 : η * K = ε / 4 := by rw [hη]; field_simp
  calc |∑ p ∈ (Ioc (a n) (b n)).filter Nat.Prime, (1 / (p:ℝ)) - L|
      ≤ |∑ p ∈ (Ioc (a n) (b n)).filter Nat.Prime, (1 / (p:ℝ)) -
          (Real.log (Real.log (b n)) - Real.log (Real.log (a n)))| +
        |(Real.log (Real.log (b n)) - Real.log (Real.log (a n))) - L| := abs_sub_le _ _ _
    _ < ε := by
      have := (abs_lt.1 h5.2)
      have : |(Real.log (Real.log (b n)) - Real.log (Real.log (a n))) - L| < ε/2 := h5.2
      linarith

private lemma Z_cube_le (n : ℕ) : (⌊(n:ℝ)^(1/3:ℝ)⌋₊)^3 ≤ n := by
  have h0 : (0:ℝ) ≤ (n:ℝ)^(1/3:ℝ) := by positivity
  have h1 : ((⌊(n:ℝ)^(1/3:ℝ)⌋₊ : ℕ):ℝ) ≤ (n:ℝ)^(1/3:ℝ) := Nat.floor_le h0
  have h2 : (((⌊(n:ℝ)^(1/3:ℝ)⌋₊ : ℕ):ℝ))^3 ≤ ((n:ℝ)^(1/3:ℝ))^3 := pow_le_pow_left₀ (by positivity) h1 3
  have h3 : ((n:ℝ)^(1/3:ℝ))^3 = n := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]; norm_num
  rw [h3] at h2
  exact_mod_cast h2

private lemma Z_lt_cube (n : ℕ) : n < (⌊(n:ℝ)^(1/3:ℝ)⌋₊ + 1)^3 := by
  have h0 : (0:ℝ) ≤ (n:ℝ)^(1/3:ℝ) := by positivity
  have h1 : (n:ℝ)^(1/3:ℝ) < ((⌊(n:ℝ)^(1/3:ℝ)⌋₊ : ℕ):ℝ) + 1 := Nat.lt_floor_add_one _
  have h2 : ((n:ℝ)^(1/3:ℝ))^3 < (((⌊(n:ℝ)^(1/3:ℝ)⌋₊ : ℕ):ℝ) + 1)^3 := pow_lt_pow_left₀ h1 h0 (by norm_num)
  have h3 : ((n:ℝ)^(1/3:ℝ))^3 = n := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]; norm_num
  rw [h3] at h2
  exact_mod_cast h2

private lemma Z_tendsto : Filter.Tendsto (fun n : ℕ => ⌊(n:ℝ)^(1/3:ℝ)⌋₊) Filter.atTop Filter.atTop := by
  rw [Filter.tendsto_atTop_atTop]
  intro b
  refine ⟨b^3, fun n hn => ?_⟩
  by_contra h
  push_neg at h
  have := Z_lt_cube n
  have h2 : (⌊(n:ℝ)^(1/3:ℝ)⌋₊ + 1)^3 ≤ b^3 := Nat.pow_le_pow_left h 3
  omega

private lemma y_tendsto : Filter.Tendsto (fun n : ℕ => Nat.sqrt n) Filter.atTop Filter.atTop := by
  rw [Filter.tendsto_atTop_atTop]
  intro b
  exact ⟨b*b, fun n hn => Nat.le_sqrt.2 hn⟩

private lemma logn_tendsto : Filter.Tendsto (fun n : ℕ => Real.log n) Filter.atTop Filter.atTop :=
  Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop

private lemma ratio_y : Filter.Tendsto (fun n : ℕ => Real.log (Nat.sqrt n) / Real.log n) Filter.atTop (nhds (1/2)) := by
  have hlo : Filter.Tendsto (fun n : ℕ => (1/2:ℝ) - Real.log 2 / Real.log n) Filter.atTop (nhds (1/2)) := by
    have := (tendsto_const_nhds (x := Real.log 2)).div_atTop logn_tendsto
    simpa using (tendsto_const_nhds (x := (1/2:ℝ))).sub this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo tendsto_const_nhds ?_ ?_
  · filter_upwards [Filter.eventually_ge_atTop 4] with n hn
    have hn0 : (0:ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have hy1 : 1 ≤ Nat.sqrt n := Nat.le_sqrt.2 (by omega)
    have hlt : n < (Nat.sqrt n + 1) * (Nat.sqrt n + 1) := Nat.lt_succ_sqrt n
    have h4 : (n:ℝ) ≤ 4 * (Nat.sqrt n : ℝ)^2 := by
      have : n ≤ 4 * (Nat.sqrt n)^2 := by nlinarith
      exact_mod_cast this
    have hy0 : (0:ℝ) < Nat.sqrt n := by exact_mod_cast hy1
    have hlog := Real.log_le_log hn0 h4
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow] at hlog
    have h4' : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4:ℝ) = 2^2 by norm_num, Real.log_pow]; norm_num
    have hl : 0 < Real.log n := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
    have e : (1/2:ℝ) - Real.log 2 / Real.log n = (Real.log n / 2 - Real.log 2) / Real.log n := by
      field_simp
    rw [e]
    apply div_le_div_of_nonneg_right _ hl.le
    push_cast at hlog
    linarith
  · filter_upwards [Filter.eventually_ge_atTop 2] with n hn
    have hn0 : (0:ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have hy1 : 1 ≤ Nat.sqrt n := Nat.le_sqrt.2 (by omega)
    have hy0 : (0:ℝ) < Nat.sqrt n := by exact_mod_cast hy1
    have hle : (Nat.sqrt n : ℝ)^2 ≤ n := by exact_mod_cast (Nat.sqrt_le' n)
    have hlog := Real.log_le_log (by positivity) hle
    rw [Real.log_pow] at hlog
    have hl : 0 < Real.log n := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
    rw [div_le_iff₀ hl]
    push_cast at hlog
    linarith

private lemma ratio_Z : Filter.Tendsto (fun n : ℕ => Real.log (⌊(n:ℝ)^(1/3:ℝ)⌋₊) / Real.log n) Filter.atTop (nhds (1/3)) := by
  have hlo : Filter.Tendsto (fun n : ℕ => (1/3:ℝ) - Real.log 2 / Real.log n) Filter.atTop (nhds (1/3)) := by
    have := (tendsto_const_nhds (x := Real.log 2)).div_atTop logn_tendsto
    simpa using (tendsto_const_nhds (x := (1/3:ℝ))).sub this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo tendsto_const_nhds ?_ ?_
  · filter_upwards [Filter.eventually_ge_atTop 8] with n hn
    have hn0 : (0:ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have hz1 : 1 ≤ ⌊(n:ℝ)^(1/3:ℝ)⌋₊ := by
      by_contra h
      have h0 : ⌊(n:ℝ)^(1/3:ℝ)⌋₊ = 0 := by omega
      have := Z_lt_cube n
      rw [h0] at this
      omega
    have hlt := Z_lt_cube n
    have h4 : (n:ℝ) ≤ 8 * ((⌊(n:ℝ)^(1/3:ℝ)⌋₊ : ℕ) : ℝ)^3 := by
      have : n ≤ 8 * (⌊(n:ℝ)^(1/3:ℝ)⌋₊)^3 := by
        have : (⌊(n:ℝ)^(1/3:ℝ)⌋₊ + 1)^3 ≤ (2 * ⌊(n:ℝ)^(1/3:ℝ)⌋₊)^3 := Nat.pow_le_pow_left (by omega) 3
        rw [mul_pow] at this
        omega
      exact_mod_cast this
    have hy0 : (0:ℝ) < ((⌊(n:ℝ)^(1/3:ℝ)⌋₊ : ℕ) : ℝ) := by exact_mod_cast hz1
    have hlog := Real.log_le_log hn0 h4
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow] at hlog
    have h4' : Real.log 8 = 3 * Real.log 2 := by
      rw [show (8:ℝ) = 2^3 by norm_num, Real.log_pow]; norm_num
    have hl : 0 < Real.log n := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
    have e : (1/3:ℝ) - Real.log 2 / Real.log n = (Real.log n / 3 - Real.log 2) / Real.log n := by
      field_simp
    rw [e]
    apply div_le_div_of_nonneg_right _ hl.le
    push_cast at hlog
    linarith
  · filter_upwards [Filter.eventually_ge_atTop 8] with n hn
    have hn0 : (0:ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have hz1 : 1 ≤ ⌊(n:ℝ)^(1/3:ℝ)⌋₊ := by
      by_contra h
      have h0 : ⌊(n:ℝ)^(1/3:ℝ)⌋₊ = 0 := by omega
      have := Z_lt_cube n
      rw [h0] at this
      omega
    have hy0 : (0:ℝ) < ((⌊(n:ℝ)^(1/3:ℝ)⌋₊ : ℕ) : ℝ) := by exact_mod_cast hz1
    have hle : ((⌊(n:ℝ)^(1/3:ℝ)⌋₊ : ℕ) : ℝ)^3 ≤ n := by exact_mod_cast Z_cube_le n
    have hlog := Real.log_le_log (by positivity) hle
    rw [Real.log_pow] at hlog
    have hl : 0 < Real.log n := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
    rw [div_le_iff₀ hl]
    push_cast at hlog
    linarith

private lemma D_tendsto : Filter.Tendsto (fun n : ℕ => Real.log (Real.log (Nat.sqrt n)) - Real.log (Real.log (⌊(n:ℝ)^(1/3:ℝ)⌋₊)))
    Filter.atTop (nhds (Real.log (3/2))) := by
  have h := ratio_y.div ratio_Z (by norm_num)
  have h2 := (Real.continuousAt_log (x := (1/2) / (1/3)) (by norm_num)).tendsto.comp h
  have h3 : (1/2 : ℝ) / (1/3) = 3/2 := by norm_num
  rw [h3] at h2
  refine h2.congr' ?_
  filter_upwards [Filter.eventually_ge_atTop 8, Z_tendsto.eventually_ge_atTop 2,
    y_tendsto.eventually_ge_atTop 2] with n hn hZ hy
  have hl : 0 < Real.log n := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
  have hZ' : 0 < Real.log (⌊(n:ℝ)^(1/3:ℝ)⌋₊ : ℕ) := Real.log_pos (by exact_mod_cast hZ)
  have hy' : 0 < Real.log (Nat.sqrt n : ℕ) := Real.log_pos (by exact_mod_cast hy)
  simp only [Function.comp, Pi.div_apply]
  rw [div_div_div_cancel_right₀ hl.ne', Real.log_div hy'.ne' hZ'.ne']

private lemma prod_bounds (F : Finset ℕ) (z : ℕ) (hz : 3 ≤ z) (hF : ∀ p ∈ F, p.Prime ∧ z + 1 ≤ p) :
    Real.exp (-(2 * (1 + 4 / ((z:ℝ) + 1)) * ∑ p ∈ F, 1 / (p:ℝ))) ≤ ∏ p ∈ F, (1 - 2 / (p:ℝ)) ∧
    ∏ p ∈ F, (1 - 2 / (p:ℝ)) ≤ Real.exp (-(2 * ∑ p ∈ F, 1 / (p:ℝ))) := by
  have hz' : (3:ℝ) ≤ z := by exact_mod_cast hz
  constructor
  · rw [Finset.mul_sum, ← Finset.sum_neg_distrib, Real.exp_sum]
    refine Finset.prod_le_prod₀ (fun p _ => (Real.exp_pos _).le) fun p hp => ?_
    obtain ⟨hpp, hzp⟩ := hF p hp
    have hp' : (z:ℝ) + 1 ≤ p := by exact_mod_cast hzp
    have hp0 : (0:ℝ) < p := by linarith
    have h1 : 0 < 1 - 2 / (p:ℝ) := by
      rw [sub_pos, div_lt_one hp0]; linarith
    rw [← Real.le_log_iff_exp_le h1]
    have h2 := Real.one_sub_inv_le_log_of_pos h1
    refine le_trans ?_ h2
    have e : 1 - (1 - 2 / (p:ℝ))⁻¹ = -(2 / ((p:ℝ) - 2)) := by
      have : (p:ℝ) - 2 ≠ 0 := by linarith
      field_simp
      ring
    rw [e, neg_le_neg_iff]
    rw [div_le_iff₀ (by linarith)]
    have : 2 * (1 + 4 / ((z:ℝ) + 1)) * (1 / (p:ℝ)) * ((p:ℝ) - 2) = 2 * (1 + 4 / ((z:ℝ) + 1)) * (((p:ℝ) - 2) / p) := by
      field_simp
    have h3 : 1 ≤ (1 + 4 / ((z:ℝ) + 1)) * (((p:ℝ) - 2) / p) := by
      rw [← sub_nonneg]
      have : (1 + 4 / ((z:ℝ) + 1)) * (((p:ℝ) - 2) / p) - 1
          = (4 * (p - 2) - (z + 1) * 2 ) / ((z + 1) * p) := by
        field_simp; ring
      rw [this]
      apply div_nonneg _ (by positivity)
      linarith
    nlinarith
  · rw [Finset.mul_sum, ← Finset.sum_neg_distrib, Real.exp_sum]
    refine Finset.prod_le_prod₀ (fun p hp => ?_) fun p hp => ?_
    · obtain ⟨hpp, hzp⟩ := hF p hp
      have hp' : (z:ℝ) + 1 ≤ p := by exact_mod_cast hzp
      have hp0 : (0:ℝ) < p := by linarith
      rw [sub_nonneg, div_le_one hp0]; linarith
    · have := Real.add_one_le_exp (-(2 * (1 / (p:ℝ))))
      have e : -(2 * (1 / (p:ℝ))) + 1 = 1 - 2 / p := by ring
      linarith
private lemma split_prod (z y : ℕ) (hzy : z ≤ y) (hz : 2 ≤ z) (g : ℕ → ℝ) (R : ℕ → Prop) [DecidablePred R] :
    ∏ p ∈ (Finset.Icc 2 y).filter R, g p =
      (∏ p ∈ (Finset.Icc 2 z).filter R, g p) * ∏ p ∈ (Finset.Ioc z y).filter R, g p := by
  have hU : Finset.Icc 2 y = Finset.Icc 2 z ∪ Finset.Ioc z y := by
    ext a
    simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_Ioc]
    omega
  rw [hU, Finset.filter_union, Finset.prod_union]
  refine Finset.disjoint_filter_filter ?_
  rw [Finset.disjoint_left]
  intro a ha hb
  simp only [Finset.mem_Icc, Finset.mem_Ioc] at ha hb
  omega


private lemma R_bound (n z y : ℕ) (hn : 0 < n) (hc : n < (z + 1)^3) :
    0 ≤ ∑ p ∈ (Ioc z y).filter (fun p => p.Prime ∧ p ∣ n), (1 / (p:ℝ)) ∧
    ∑ p ∈ (Ioc z y).filter (fun p => p.Prime ∧ p ∣ n), (1 / (p:ℝ)) ≤ 2 / ((z:ℝ) + 1) := by
  set F := (Ioc z y).filter (fun p => p.Prime ∧ p ∣ n) with hF
  have hmem : ∀ p ∈ F, p.Prime ∧ p ∣ n ∧ z + 1 ≤ p := by
    intro p hp
    simp only [hF, mem_filter, mem_Ioc] at hp
    exact ⟨hp.2.1, hp.2.2, hp.1.1⟩
  refine ⟨Finset.sum_nonneg fun p hp => by
      have := (hmem p hp).1.pos; positivity, ?_⟩
  have hcard : F.card ≤ 2 := by
    by_contra h
    push_neg at h
    have h1 : (z + 1)^F.card ≤ ∏ p ∈ F, p := by
      rw [← Finset.prod_const]
      exact Finset.prod_le_prod' (fun p hp => (hmem p hp).2.2)
    have h2 : ∏ p ∈ F, p ∣ n := by
      refine dvd_trans (Finset.prod_dvd_prod_of_subset _ _ _ ?_) (Nat.prod_primeFactors_dvd n)
      intro p hp
      exact Nat.mem_primeFactors.2 ⟨(hmem p hp).1, (hmem p hp).2.1, hn.ne'⟩
    have h3 : ∏ p ∈ F, p ≤ n := Nat.le_of_dvd hn h2
    have h4 : (z + 1)^3 ≤ (z + 1)^F.card := Nat.pow_le_pow_right (by omega) h
    omega
  calc ∑ p ∈ F, (1 / (p:ℝ)) ≤ ∑ p ∈ F, (1 / ((z:ℝ) + 1)) := by
        apply Finset.sum_le_sum
        intro p hp
        have : ((z:ℝ) + 1) ≤ p := by exact_mod_cast (hmem p hp).2.2
        exact one_div_le_one_div_of_le (by positivity) this
    _ = F.card * (1 / ((z:ℝ) + 1)) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ 2 * (1 / ((z:ℝ) + 1)) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact_mod_cast hcard
    _ = 2 / ((z:ℝ) + 1) := by ring

private lemma core (C : ℝ) (hC : 0 < C) (n z y : ℕ) (hn : 0 < n) (he : Even n) (hz : 3 ≤ z) (hzy : z ≤ y)
    (hc : n < (z + 1)^3) :
    Real.exp (2 * (∑ p ∈ (Ioc z y).filter Nat.Prime, (1 / (p:ℝ)) - 2 / ((z:ℝ) + 1))) ≤
      (C * ∏ p ∈ ((Icc 2 z).filter Nat.Prime).filter (fun p => ¬ p ∣ n), (1 - 2 / (p:ℝ))) /
      (C * ∏ p ∈ ((Icc 2 y).filter Nat.Prime).filter (fun p => ¬ p ∣ n), (1 - 2 / (p:ℝ))) ∧
    (C * ∏ p ∈ ((Icc 2 z).filter Nat.Prime).filter (fun p => ¬ p ∣ n), (1 - 2 / (p:ℝ))) /
      (C * ∏ p ∈ ((Icc 2 y).filter Nat.Prime).filter (fun p => ¬ p ∣ n), (1 - 2 / (p:ℝ))) ≤
    Real.exp (2 * (1 + 4 / ((z:ℝ) + 1)) * ∑ p ∈ (Ioc z y).filter Nat.Prime, (1 / (p:ℝ))) := by
  have h2n : 2 ∣ n := even_iff_two_dvd.1 he
  simp only [Finset.filter_filter]
  rw [split_prod z y hzy (by omega) (fun p => 1 - 2 / (p:ℝ)) (fun p => p.Prime ∧ ¬ p ∣ n)]
  set A := ∏ p ∈ (Icc 2 z).filter (fun p => p.Prime ∧ ¬ p ∣ n), (1 - 2 / (p:ℝ)) with hA
  set F := (Ioc z y).filter (fun p => p.Prime ∧ ¬ p ∣ n) with hFdef
  set B := ∏ p ∈ F, (1 - 2 / (p:ℝ)) with hB
  have hz' : (3:ℝ) ≤ z := by exact_mod_cast hz
  have hApos : 0 < A := by
    refine Finset.prod_pos fun p hp => ?_
    simp only [mem_filter, mem_Icc] at hp
    have h3 : 3 ≤ p := by
      have := hp.2.1.two_le
      rcases Nat.lt_or_ge p 3 with h | h
      · have : p = 2 := by omega
        exact absurd (this ▸ h2n) hp.2.2
      · exact h
    have : (3:ℝ) ≤ p := by exact_mod_cast h3
    rw [sub_pos, div_lt_one (by linarith)]; linarith
  have hFmem : ∀ p ∈ F, p.Prime ∧ z + 1 ≤ p := by
    intro p hp
    simp only [hFdef, mem_filter, mem_Ioc] at hp
    exact ⟨hp.2.1, hp.1.1⟩
  obtain ⟨hB1, hB2⟩ := prod_bounds F z hz hFmem
  set T := ∑ p ∈ F, (1 / (p:ℝ)) with hT
  have hBpos : 0 < B := lt_of_lt_of_le (Real.exp_pos _) hB1
  have hsplit := Finset.sum_filter_add_sum_filter_not ((Ioc z y).filter Nat.Prime) (fun p => p ∣ n)
    (fun p => (1 / (p:ℝ)))
  simp only [Finset.filter_filter] at hsplit
  obtain ⟨hR0, hR1⟩ := R_bound n z y hn hc
  have hTS : T ≤ ∑ p ∈ (Ioc z y).filter Nat.Prime, (1 / (p:ℝ)) := by linarith
  have hTS2 : ∑ p ∈ (Ioc z y).filter Nat.Prime, (1 / (p:ℝ)) - 2 / ((z:ℝ) + 1) ≤ T := by linarith
  have hT0 : 0 ≤ T := Finset.sum_nonneg fun p hp => by
    have := (hFmem p hp).1.pos; positivity
  have hrat : C * A / (C * (A * B)) = 1 / B := by
    field_simp
  rw [hrat]
  have hc0 : 0 ≤ 1 + 4 / ((z:ℝ) + 1) := by positivity
  constructor
  · rw [le_div_iff₀ hBpos]
    have h1 : Real.exp (2 * T) * B ≤ 1 := by
      calc Real.exp (2 * T) * B ≤ Real.exp (2 * T) * Real.exp (-(2 * T)) :=
            mul_le_mul_of_nonneg_left hB2 (Real.exp_pos _).le
        _ = 1 := by rw [← Real.exp_add]; simp
    have h2 : Real.exp (2 * (∑ p ∈ (Ioc z y).filter Nat.Prime, (1 / (p:ℝ)) - 2 / ((z:ℝ) + 1))) ≤ Real.exp (2 * T) :=
      Real.exp_le_exp.2 (by linarith)
    calc _ ≤ Real.exp (2 * T) * B := mul_le_mul_of_nonneg_right h2 hBpos.le
      _ ≤ 1 := h1
  · rw [div_le_iff₀ hBpos]
    have h1 : 1 ≤ Real.exp (2 * (1 + 4 / ((z:ℝ) + 1)) * T) * B := by
      calc (1:ℝ) = Real.exp (2 * (1 + 4 / ((z:ℝ) + 1)) * T) * Real.exp (-(2 * (1 + 4 / ((z:ℝ) + 1)) * T)) := by
            rw [← Real.exp_add]; simp
        _ ≤ _ := mul_le_mul_of_nonneg_left hB1 (Real.exp_pos _).le
    have h2 : Real.exp (2 * (1 + 4 / ((z:ℝ) + 1)) * T) ≤
        Real.exp (2 * (1 + 4 / ((z:ℝ) + 1)) * ∑ p ∈ (Ioc z y).filter Nat.Prime, (1 / (p:ℝ))) :=
      Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hTS (by positivity))
    calc (1:ℝ) ≤ _ := h1
      _ ≤ _ := mul_le_mul_of_nonneg_right h2 hBpos.le

theorem Conjectures.Goldbach.FareyCubeSqrtDensityRatio :
    let I := fun n : ℕ => Finset.Icc ((n+2)/3) ((2*n)/3); let P := fun z : ℕ => (Finset.Icc 2 z).filter Nat.Prime; let V := fun n z : ℕ => ((I n).card:ℝ)*(n.totient:ℝ)/n * ∏ p ∈ (P z).filter (fun p => ¬ p ∣ n), (1-2/(p:ℝ)); let Z₁ := fun n : ℕ => ⌊(n:ℝ)^(1/3:ℝ)⌋₊; ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, 64 ≤ N ∧ ∀ n : ℕ, N ≤ n → Even n → |V n (Z₁ n) / V n n.sqrt - 9/4| ≤ ε := by
  intro I P V Z₁ ε hε
  have hZy : ∀ᶠ n : ℕ in Filter.atTop, ⌊(n:ℝ)^(1/3:ℝ)⌋₊ ≤ Nat.sqrt n := by
    filter_upwards [Filter.eventually_ge_atTop 1, Z_tendsto.eventually_ge_atTop 1] with n hn hz
    apply Nat.le_sqrt.2
    have := Z_cube_le n
    calc ⌊(n:ℝ)^(1/3:ℝ)⌋₊ * ⌊(n:ℝ)^(1/3:ℝ)⌋₊ ≤ ⌊(n:ℝ)^(1/3:ℝ)⌋₊ ^ 3 := by
          rw [pow_succ, pow_two]
          exact Nat.le_mul_of_pos_right _ hz
      _ ≤ n := this
  have hS := S_tendsto (fun n : ℕ => ⌊(n:ℝ)^(1/3:ℝ)⌋₊) Nat.sqrt (Real.log (3/2)) Z_tendsto hZy D_tendsto
  have hz0 : Filter.Tendsto (fun n : ℕ => 2 / (((⌊(n:ℝ)^(1/3:ℝ)⌋₊ : ℕ) : ℝ) + 1)) Filter.atTop (nhds 0) := by
    apply Filter.Tendsto.div_atTop tendsto_const_nhds
    exact Filter.tendsto_atTop_add_const_right _ _ (tendsto_natCast_atTop_atTop.comp Z_tendsto)
  have hz4 : Filter.Tendsto (fun n : ℕ => 4 / (((⌊(n:ℝ)^(1/3:ℝ)⌋₊ : ℕ) : ℝ) + 1)) Filter.atTop (nhds 0) := by
    apply Filter.Tendsto.div_atTop tendsto_const_nhds
    exact Filter.tendsto_atTop_add_const_right _ _ (tendsto_natCast_atTop_atTop.comp Z_tendsto)
  have hE : Real.exp (2 * Real.log (3/2)) = 9/4 := by
    rw [show (2:ℝ) * Real.log (3/2) = Real.log (3/2) + Real.log (3/2) by ring, Real.exp_add,
      Real.exp_log (by norm_num)]
    norm_num
  have hlo : Filter.Tendsto (fun n : ℕ => Real.exp (2 * (∑ p ∈ (Ioc ⌊(n:ℝ)^(1/3:ℝ)⌋₊ (Nat.sqrt n)).filter Nat.Prime, (1 / (p:ℝ)) - 2 / (((⌊(n:ℝ)^(1/3:ℝ)⌋₊ : ℕ) : ℝ) + 1))))
      Filter.atTop (nhds (9/4)) := by
    rw [← hE]
    apply (Real.continuous_exp.tendsto _).comp
    have := (hS.sub hz0).const_mul 2
    simpa using this
  have hhi : Filter.Tendsto (fun n : ℕ => Real.exp (2 * (1 + 4 / (((⌊(n:ℝ)^(1/3:ℝ)⌋₊ : ℕ) : ℝ) + 1)) * ∑ p ∈ (Ioc ⌊(n:ℝ)^(1/3:ℝ)⌋₊ (Nat.sqrt n)).filter Nat.Prime, (1 / (p:ℝ))))
      Filter.atTop (nhds (9/4)) := by
    rw [← hE]
    apply (Real.continuous_exp.tendsto _).comp
    have := ((tendsto_const_nhds (x := (1:ℝ))).add hz4).const_mul 2 |>.mul hS
    simpa using this
  have e1 := (Metric.tendsto_nhds.1 hlo) ε hε
  have e2 := (Metric.tendsto_nhds.1 hhi) ε hε
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (e1.and (e2.and ((Filter.eventually_ge_atTop 64).and
    ((Z_tendsto.eventually_ge_atTop 3).and hZy))))
  refine ⟨max N 64, le_max_right _ _, fun n hn hev => ?_⟩
  obtain ⟨h1, h2, h3, h4, h5⟩ := hN n (le_trans (le_max_left _ _) hn)
  have hn64 : 64 ≤ n := le_trans (le_max_right _ _) hn
  have hC : 0 < ((I n).card:ℝ)*(n.totient:ℝ)/n := by
    have hcard : 0 < (I n).card := by
      apply Finset.card_pos.2
      refine ⟨(n+2)/3, ?_⟩
      simp only [I, Finset.mem_Icc]
      omega
    have : 0 < n.totient := Nat.totient_pos.2 (by omega)
    have hn0 : (0:ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    positivity
  obtain ⟨c1, c2⟩ := core _ hC n _ _ (by omega) hev h4 h5 (Z_lt_cube n)
  rw [Real.dist_eq, abs_lt] at h1 h2
  show |(((I n).card:ℝ)*(n.totient:ℝ)/n * ∏ p ∈ ((Finset.Icc 2 ⌊(n:ℝ)^(1/3:ℝ)⌋₊).filter Nat.Prime).filter (fun p => ¬ p ∣ n), (1-2/(p:ℝ))) /
    (((I n).card:ℝ)*(n.totient:ℝ)/n * ∏ p ∈ ((Finset.Icc 2 (Nat.sqrt n)).filter Nat.Prime).filter (fun p => ¬ p ∣ n), (1-2/(p:ℝ))) - 9/4| ≤ ε
  rw [abs_le]
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
