import Mathlib

private theorem put_key (A B : ℝ → ℝ) (hA : Continuous A) (hB : Continuous B)
    (hper : ∀ x, B (x + 1) = B x) (hB0 : ∀ x, 0 ≤ B x) (K : ℝ)
    (hK : ∀ v, A v + A (v + 1/2) ≤ 2 * K) :
    ∫ v in (0:ℝ)..1, A v * B (2 * v) ≤ K * ∫ w in (0:ℝ)..1, B w := by
  have hc1 : Continuous fun v => A v * B (2 * v) := hA.mul (hB.comp (continuous_const.mul continuous_id))
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (hc1.intervalIntegrable (μ := MeasureTheory.volume) (0:ℝ) (1/2)) (hc1.intervalIntegrable (μ := MeasureTheory.volume) (1/2:ℝ) 1)
  have hshift : ∫ v in (1/2:ℝ)..1, A v * B (2 * v)
      = ∫ v in (0:ℝ)..(1/2), A (v + 1/2) * B (2 * v) := by
    have := intervalIntegral.integral_comp_add_right (a := (0:ℝ)) (b := 1/2)
      (fun v => A v * B (2 * v)) (1/2)
    have h2 : ∫ v in (0:ℝ)..(1/2), A (v + 1/2) * B (2 * (v + 1/2))
        = ∫ v in (0:ℝ)..(1/2), A (v + 1/2) * B (2 * v) := by
      apply intervalIntegral.integral_congr
      intro v _
      simp only
      have : 2 * (v + 1/2) = 2 * v + 1 := by ring
      rw [this, hper]
    rw [← h2, this]
    norm_num
  have hcomb : (∫ v in (0:ℝ)..(1/2), A v * B (2 * v)) + ∫ v in (0:ℝ)..(1/2), A (v + 1/2) * B (2 * v)
      = ∫ v in (0:ℝ)..(1/2), (A v + A (v + 1/2)) * B (2 * v) := by
    rw [← intervalIntegral.integral_add]
    · apply intervalIntegral.integral_congr
      intro v _
      simp only
      ring
    · exact (hc1).intervalIntegrable _ _
    · exact ((hA.comp (continuous_id.add continuous_const)).mul
        (hB.comp (continuous_const.mul continuous_id))).intervalIntegrable _ _
  have hmono : ∫ v in (0:ℝ)..(1/2), (A v + A (v + 1/2)) * B (2 * v)
      ≤ ∫ v in (0:ℝ)..(1/2), (2 * K) * B (2 * v) := by
    apply intervalIntegral.integral_mono_on (by norm_num)
    · exact ((hA.add (hA.comp (continuous_id.add continuous_const))).mul
        (hB.comp (continuous_const.mul continuous_id))).intervalIntegrable _ _
    · exact (continuous_const.mul (hB.comp (continuous_const.mul continuous_id))).intervalIntegrable _ _
    · intro v _
      exact mul_le_mul_of_nonneg_right (hK v) (hB0 _)
  have hscale : ∫ v in (0:ℝ)..(1/2), B (2 * v) = (1/2) * ∫ w in (0:ℝ)..1, B w := by
    rw [intervalIntegral.integral_comp_mul_left (fun w => B w) (by norm_num : (2:ℝ) ≠ 0)]
    norm_num
  rw [intervalIntegral.integral_const_mul, hscale] at hmono
  linarith

private noncomputable def putP (m : ℕ) (v : ℝ) : ℝ :=
  ∑ j ∈ Finset.range m, Real.cos (2 * Real.pi * (2:ℝ) ^ j * v)

private theorem putP_cont (m : ℕ) : Continuous (putP m) := by
  unfold putP
  fun_prop

private theorem putP_per (m : ℕ) (x : ℝ) : putP m (x + 1) = putP m x := by
  unfold putP
  apply Finset.sum_congr rfl
  intro j _
  have : 2 * Real.pi * (2:ℝ) ^ j * (x + 1) = 2 * Real.pi * (2:ℝ) ^ j * x + ((2:ℕ) ^ j : ℕ) * (2 * Real.pi) := by
    push_cast; ring
  rw [this, Real.cos_add_nat_mul_two_pi]

private theorem putP_succ (m : ℕ) (v : ℝ) :
    putP (m + 1) v = Real.cos (2 * Real.pi * v) + putP m (2 * v) := by
  unfold putP
  rw [Finset.sum_range_succ', add_comm]
  refine congrArg₂ (· + ·) (by simp) (Finset.sum_congr rfl fun j _ => ?_)
  congr 1
  ring

private theorem put_mgf (s : ℝ) (m : ℕ) :
    ∫ v in (0:ℝ)..1, Real.exp (s * putP m v) ≤ Real.exp (m * (s ^ 2 / 2)) := by
  induction m with
  | zero => simp [putP]
  | succ m ih =>
    have h1 : ∀ v, Real.exp (s * putP (m + 1) v)
        = Real.exp (s * Real.cos (2 * Real.pi * v)) * Real.exp (s * putP m (2 * v)) := by
      intro v
      rw [putP_succ, mul_add, Real.exp_add]
    simp_rw [h1]
    have := put_key (fun v => Real.exp (s * Real.cos (2 * Real.pi * v)))
      (fun w => Real.exp (s * putP m w)) (by fun_prop)
      (by have := putP_cont m; fun_prop)
      (fun x => by rw [putP_per])
      (fun x => (Real.exp_pos _).le) (Real.exp (s ^ 2 / 2)) (by
        intro v
        have hc : Real.cos (2 * Real.pi * (v + 1/2)) = - Real.cos (2 * Real.pi * v) := by
          have : 2 * Real.pi * (v + 1/2) = 2 * Real.pi * v + Real.pi := by ring
          rw [this, Real.cos_add_pi]
        rw [hc, mul_neg, Real.exp_neg]
        have hcosh : Real.exp (s * Real.cos (2 * Real.pi * v)) + (Real.exp (s * Real.cos (2 * Real.pi * v)))⁻¹
            = 2 * Real.cosh (s * Real.cos (2 * Real.pi * v)) := by
          rw [Real.cosh_eq, Real.exp_neg]; ring
        rw [hcosh]
        have h2 := Real.cosh_le_exp_half_sq (s * Real.cos (2 * Real.pi * v))
        have h3 : (s * Real.cos (2 * Real.pi * v)) ^ 2 / 2 ≤ s ^ 2 / 2 := by
          have := Real.cos_sq_le_one (2 * Real.pi * v)
          have h4 : (s * Real.cos (2 * Real.pi * v)) ^ 2 = s ^ 2 * Real.cos (2 * Real.pi * v) ^ 2 := by ring
          rw [h4]
          nlinarith [sq_nonneg s]
        have := Real.exp_le_exp.mpr h3
        linarith)
    refine this.trans ?_
    rw [Nat.cast_succ, add_mul, one_mul, Real.exp_add, mul_comm (Real.exp (m * (s ^ 2 / 2)))]
    exact mul_le_mul_of_nonneg_left ih (Real.exp_pos _).le

theorem Conjectures.Goldbach.PacketUpperTailHalf :
    let T := fun (m : ℕ) (t : ℝ) => ∑ j ∈ Finset.range m, Real.cos (2*Real.pi*(2:ℝ)^(j+1)*t); ∀ m : ℕ, 0 < m → intervalIntegral (fun t => if (m:ℝ)/2 < T m t then (1:ℝ) else 0) (0:ℝ) 1 MeasureTheory.volume ≤ Real.exp (-(m:ℝ)/8) := by
  intro T m hm
  have hT : ∀ t, T m t = putP m (2 * t) := by
    intro t
    show ∑ j ∈ Finset.range m, Real.cos (2*Real.pi*(2:ℝ)^(j+1)*t) = _
    unfold putP
    apply Finset.sum_congr rfl
    intro j _
    congr 1
    ring
  have hTc : Continuous (T m) := by
    have : T m = fun t => putP m (2 * t) := funext hT
    rw [this]
    exact (putP_cont m).comp (continuous_const.mul continuous_id)
  have hpt : ∀ t, (if (m:ℝ)/2 < T m t then (1:ℝ) else 0)
      ≤ Real.exp (-(m:ℝ)/4) * Real.exp ((1/2) * putP m (2 * t)) := by
    intro t
    rw [← Real.exp_add]
    split_ifs with h
    · apply Real.one_le_exp
      rw [hT] at h
      linarith
    · exact (Real.exp_pos _).le
  have hint : IntervalIntegrable (fun t => if (m:ℝ)/2 < T m t then (1:ℝ) else 0)
      MeasureTheory.volume 0 1 := by
    have hmeas : Measurable (fun t => if (m:ℝ)/2 < T m t then (1:ℝ) else 0) :=
      Measurable.ite (measurableSet_lt measurable_const hTc.measurable) measurable_const measurable_const
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
    refine MeasureTheory.Measure.integrableOn_of_bounded (M := 1) (by simp) hmeas.aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall fun t => ?_
    split_ifs <;> simp
  have hcont2 : Continuous fun t => Real.exp ((1/2) * putP m (2 * t)) := by
    have := putP_cont m
    fun_prop
  calc intervalIntegral (fun t => if (m:ℝ)/2 < T m t then (1:ℝ) else 0) (0:ℝ) 1 MeasureTheory.volume
      ≤ ∫ t in (0:ℝ)..1, Real.exp (-(m:ℝ)/4) * Real.exp ((1/2) * putP m (2 * t)) := by
        apply intervalIntegral.integral_mono_on zero_le_one hint
        · exact (continuous_const.mul hcont2).intervalIntegrable _ _
        · intro t _; exact hpt t
    _ = Real.exp (-(m:ℝ)/4) * ∫ t in (0:ℝ)..1, (1:ℝ) * Real.exp ((1/2) * putP m (2 * t)) := by
        rw [intervalIntegral.integral_const_mul]; simp only [one_mul]
    _ ≤ Real.exp (-(m:ℝ)/4) * (Real.exp (((1/2:ℝ))^2 / 2 * m) ) := by
        apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
        have := put_key (fun _ => (1:ℝ)) (fun w => Real.exp ((1/2) * putP m w)) continuous_const
          (by have := putP_cont m; fun_prop)
          (fun x => by rw [putP_per])
          (fun x => (Real.exp_pos _).le) 1 (by intro v; norm_num)
        calc _ ≤ _ := this
          _ = ∫ w in (0:ℝ)..1, Real.exp ((1/2) * putP m w) := one_mul _
          _ ≤ Real.exp (m * ((1/2:ℝ) ^ 2 / 2)) := put_mgf (1/2) m
          _ = _ := by rw [mul_comm]
    _ = Real.exp (-(m:ℝ)/8) := by
        rw [← Real.exp_add]
        congr 1
        ring
