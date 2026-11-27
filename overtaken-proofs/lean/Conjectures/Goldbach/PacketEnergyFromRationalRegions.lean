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

private theorem put_tail :
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


private lemma ii_ind (s : Set ℝ) (hs : MeasurableSet s) (f : ℝ → ℝ) (hf : Continuous f) :
    IntervalIntegrable (s.indicator f) MeasureTheory.volume 0 1 := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
  have : MeasureTheory.IntegrableOn f (Set.Ioc (0:ℝ) 1) :=
    (hf.integrableOn_Icc (a := 0) (b := 1)).mono_set Set.Ioc_subset_Icc_self
  exact this.indicator hs

private lemma meas_rat (P : ℕ → ℕ → Prop) (r : ℕ → ℕ → ℝ) :
    MeasurableSet {t : ℝ | ∃ q a : ℕ, P q a ∧ |t - (a:ℝ)/(q:ℝ)| ≤ r q a} := by
  have : {t : ℝ | ∃ q a : ℕ, P q a ∧ |t - (a:ℝ)/(q:ℝ)| ≤ r q a}
      = ⋃ q : ℕ, ⋃ a : ℕ, ⋃ _ : P q a, {t : ℝ | |t - (a:ℝ)/(q:ℝ)| ≤ r q a} := by
    ext t
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, exists_prop]
  rw [this]
  refine MeasurableSet.iUnion (fun q => MeasurableSet.iUnion (fun a => MeasurableSet.iUnion (fun _ => ?_)))
  exact measurableSet_le (by fun_prop) measurable_const

private lemma split4 (B W Wo : Set ℝ) (hB : MeasurableSet B) (hW : MeasurableSet W)
    (hWo : MeasurableSet Wo) (F : ℝ → ℝ) (hF : Continuous F)
    (T R : ℝ) (hT : 0 ≤ T)
    (hR : intervalIntegral (B.indicator (fun _ => (1:ℝ))) 0 1 MeasureTheory.volume ≤ R) :
    intervalIntegral (B.indicator F) 0 1 MeasureTheory.volume ≤
      intervalIntegral (((B ∩ W) ∩ Wo).indicator F) 0 1 MeasureTheory.volume
      + intervalIntegral (((B ∩ W) \ Wo).indicator F) 0 1 MeasureTheory.volume
      + intervalIntegral (((B \ W) ∩ {t : ℝ | T < F t}).indicator F) 0 1 MeasureTheory.volume
      + T * R := by
  have hS : MeasurableSet {t : ℝ | T < F t} := measurableSet_lt measurable_const hF.measurable
  have i1 := ii_ind B hB F hF
  have i2 := ii_ind ((B ∩ W) ∩ Wo) ((hB.inter hW).inter hWo) F hF
  have i3 := ii_ind ((B ∩ W) \ Wo) ((hB.inter hW).diff hWo) F hF
  have i4 := ii_ind ((B \ W) ∩ {t : ℝ | T < F t}) ((hB.diff hW).inter hS) F hF
  have i5 := ii_ind B hB (fun _ => (1:ℝ)) continuous_const
  have hmono : intervalIntegral (B.indicator F) 0 1 MeasureTheory.volume ≤
      intervalIntegral (fun t => ((((B ∩ W) ∩ Wo).indicator F t
      + ((B ∩ W) \ Wo).indicator F t) + ((B \ W) ∩ {t : ℝ | T < F t}).indicator F t)
      + T * B.indicator (fun _ => (1:ℝ)) t) 0 1 MeasureTheory.volume := by
    apply intervalIntegral.integral_mono_on zero_le_one i1
    · exact ((i2.add i3).add i4).add (i5.const_mul T)
    · intro t _
      by_cases hb : t ∈ B
      · by_cases hw : t ∈ W
        · by_cases ho : t ∈ Wo
          · have e1 : t ∈ (B ∩ W) ∩ Wo := ⟨⟨hb, hw⟩, ho⟩
            have e2 : t ∉ (B ∩ W) \ Wo := fun h => h.2 ho
            have e3 : t ∉ (B \ W) ∩ {t : ℝ | T < F t} := fun h => h.1.2 hw
            simp only [Set.indicator_of_mem e1, Set.indicator_of_notMem e2, Set.indicator_of_notMem e3,
              Set.indicator_of_mem hb]
            nlinarith
          · have e1 : t ∉ (B ∩ W) ∩ Wo := fun h => ho h.2
            have e2 : t ∈ (B ∩ W) \ Wo := ⟨⟨hb, hw⟩, ho⟩
            have e3 : t ∉ (B \ W) ∩ {t : ℝ | T < F t} := fun h => h.1.2 hw
            simp only [Set.indicator_of_notMem e1, Set.indicator_of_mem e2, Set.indicator_of_notMem e3,
              Set.indicator_of_mem hb]
            nlinarith
        · by_cases hf : T < F t
          · have e1 : t ∉ (B ∩ W) ∩ Wo := fun h => hw h.1.2
            have e2 : t ∉ (B ∩ W) \ Wo := fun h => hw h.1.2
            have e3 : t ∈ (B \ W) ∩ {t : ℝ | T < F t} := ⟨⟨hb, hw⟩, hf⟩
            simp only [Set.indicator_of_notMem e1, Set.indicator_of_notMem e2, Set.indicator_of_mem e3,
              Set.indicator_of_mem hb]
            nlinarith
          · have e1 : t ∉ (B ∩ W) ∩ Wo := fun h => hw h.1.2
            have e2 : t ∉ (B ∩ W) \ Wo := fun h => hw h.1.2
            have e3 : t ∉ (B \ W) ∩ {t : ℝ | T < F t} := fun h => hf h.2
            simp only [Set.indicator_of_notMem e1, Set.indicator_of_notMem e2, Set.indicator_of_notMem e3,
              Set.indicator_of_mem hb]
            have := not_lt.mp hf
            nlinarith
      · have e1 : t ∉ (B ∩ W) ∩ Wo := fun h => hb h.1.1
        have e2 : t ∉ (B ∩ W) \ Wo := fun h => hb h.1.1
        have e3 : t ∉ (B \ W) ∩ {t : ℝ | T < F t} := fun h => hb h.1.1
        simp only [Set.indicator_of_notMem e1, Set.indicator_of_notMem e2, Set.indicator_of_notMem e3,
          Set.indicator_of_notMem hb]
        simp
  refine hmono.trans ?_
  rw [intervalIntegral.integral_add ((i2.add i3).add i4) (i5.const_mul T),
    intervalIntegral.integral_add (i2.add i3) i4, intervalIntegral.integral_add i2 i3,
    intervalIntegral.integral_const_mul]
  have := mul_le_mul_of_nonneg_left hR hT
  linarith


private lemma meas_arc (M n : ℕ) (R : ℝ) : MeasurableSet {t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ M ∧ a ≤ q ∧
    Nat.Coprime a q ∧ |t - (a:ℝ)/(q:ℝ)| ≤ R/((q:ℝ)*(n:ℝ))} := by
  have := meas_rat (fun q a => 1 ≤ q ∧ q ≤ M ∧ a ≤ q ∧ Nat.Coprime a q) (fun q a => R/((q:ℝ)*(n:ℝ)))
  simpa only [and_assoc] using this

private lemma meas_W (M n : ℕ) (R : ℝ) (p : ℕ → Prop) : MeasurableSet {t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ M ∧ a ≤ q ∧
    Nat.Coprime a q ∧ p q ∧ |t - (a:ℝ)/(q:ℝ)| ≤ R/((q:ℝ)*(n:ℝ))} := by
  have := meas_rat (fun q a => 1 ≤ q ∧ q ≤ M ∧ a ≤ q ∧ Nat.Coprime a q ∧ p q) (fun q a => R/((q:ℝ)*(n:ℝ)))
  simpa only [and_assoc] using this

private lemma meas_B (A : Set ℝ) (hA : MeasurableSet A) (L : ℕ) :
    MeasurableSet {t : ℝ | t ∉ A ∧ (1:ℝ)/2 <
      (∑ j ∈ Finset.range L, Real.cos (2*Real.pi*(2:ℝ)^(j+1)*t))/(L:ℝ)} := by
  have h : Measurable (fun t : ℝ => (∑ j ∈ Finset.range L, Real.cos (2*Real.pi*(2:ℝ)^(j+1)*t))/(L:ℝ)) := by
    have : Continuous (fun t : ℝ => (∑ j ∈ Finset.range L, Real.cos (2*Real.pi*(2:ℝ)^(j+1)*t))/(L:ℝ)) := by
      fun_prop
    exact this.measurable
  exact hA.compl.inter (measurableSet_lt (measurable_const (a := (1:ℝ)/2)) h)

private lemma B_bound (A : Set ℝ) (hA : MeasurableSet A) (L : ℕ) (hL : 0 < L) :
    intervalIntegral ({t : ℝ | t ∉ A ∧ (1:ℝ)/2 <
      (∑ j ∈ Finset.range L, Real.cos (2*Real.pi*(2:ℝ)^(j+1)*t))/(L:ℝ)}.indicator (fun _ => (1:ℝ)))
      0 1 MeasureTheory.volume ≤ Real.exp (-(L:ℝ)/8) := by
  have h := put_tail
  dsimp only at h
  have h := h L hL
  have hc : Continuous (fun t : ℝ => ∑ j ∈ Finset.range L, Real.cos (2*Real.pi*(2:ℝ)^(j+1)*t)) := by
    fun_prop
  have hR : (fun t : ℝ => if (L:ℝ)/2 < ∑ j ∈ Finset.range L, Real.cos (2*Real.pi*(2:ℝ)^(j+1)*t) then (1:ℝ) else 0)
      = {t : ℝ | (L:ℝ)/2 < ∑ j ∈ Finset.range L, Real.cos (2*Real.pi*(2:ℝ)^(j+1)*t)}.indicator (fun _ => (1:ℝ)) := by
    funext t
    simp only [Set.indicator_apply, Set.mem_setOf_eq]
  have iR : IntervalIntegrable (fun t : ℝ => if (L:ℝ)/2 < ∑ j ∈ Finset.range L, Real.cos (2*Real.pi*(2:ℝ)^(j+1)*t) then (1:ℝ) else 0)
      MeasureTheory.volume 0 1 := by
    rw [hR]
    exact ii_ind _ (measurableSet_lt measurable_const hc.measurable) _ continuous_const
  refine le_trans (intervalIntegral.integral_mono_on zero_le_one (ii_ind _ (meas_B A hA L) _ continuous_const) iR ?_) h
  intro t _
  by_cases hb : t ∈ {t : ℝ | t ∉ A ∧ (1:ℝ)/2 <
      (∑ j ∈ Finset.range L, Real.cos (2*Real.pi*(2:ℝ)^(j+1)*t))/(L:ℝ)}
  · rw [Set.indicator_of_mem hb]
    have h2 : (1:ℝ)/2 < (∑ j ∈ Finset.range L, Real.cos (2*Real.pi*(2:ℝ)^(j+1)*t))/(L:ℝ) := hb.2
    have hLp : (0:ℝ) < L := by exact_mod_cast hL
    rw [lt_div_iff₀ hLp] at h2
    rw [if_pos (by linarith)]
  · rw [Set.indicator_of_notMem hb]
    split_ifs <;> norm_num

private lemma tail_small : ∃ N : ℕ, ∀ n ≥ N, (n:ℝ) * (1 + Real.log (n:ℝ))^4 *
    Real.exp (-((max 1 (Nat.log 2 n / 2) : ℕ) : ℝ)/8) ≤ (n:ℝ)/2304 := by
  have hlim : Filter.Tendsto (fun x : ℝ => 8 * Real.exp (-(x/16)) + 8 * 65536 * ((x/16)^4 * Real.exp (-(x/16))))
      Filter.atTop (nhds 0) := by
    have h0 := Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 0
    have h4 := Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 4
    have hd : Filter.Tendsto (fun x : ℝ => x/16) Filter.atTop Filter.atTop :=
      Filter.tendsto_id.atTop_div_const (by norm_num)
    have g0 := h0.comp hd
    have g4 := h4.comp hd
    have := (g0.const_mul 8).add (g4.const_mul (8 * 65536))
    simp only [Function.comp_def, pow_zero, one_mul, mul_zero, add_zero] at this
    exact this
  have hpos : (0:ℝ) < 1 / (2304 * Real.exp (1/8)) := by positivity
  obtain ⟨X, hX⟩ := Filter.eventually_atTop.mp (hlim.eventually (gt_mem_nhds hpos))
  refine ⟨max 1 ⌈Real.exp (max X 0)⌉₊, fun n hn => ?_⟩
  have hn1 : 1 ≤ n := le_trans (le_max_left _ _) hn
  have hnpos : (0:ℝ) < n := by exact_mod_cast hn1
  have hn2 : Real.exp (max X 0) ≤ (n:ℝ) := by
    have := le_trans (le_max_right _ _) hn
    exact (Nat.le_ceil _).trans (by exact_mod_cast this)
  have hx : max X 0 ≤ Real.log n := by
    rw [Real.le_log_iff_exp_le hnpos]; exact hn2
  have hx0 : 0 ≤ Real.log n := le_trans (le_max_right _ _) hx
  have hxX : X ≤ Real.log n := le_trans (le_max_left _ _) hx
  set x := Real.log (n:ℝ) with hxdef
  set k := Nat.log 2 n with hk
  have hk1 : x < (k:ℝ) + 1 := by
    have h1 : (n:ℝ) < (2:ℝ)^(k+1) := by exact_mod_cast Nat.lt_pow_succ_log_self (by norm_num) n
    have h2 : x < Real.log ((2:ℝ)^(k+1)) := Real.log_lt_log hnpos h1
    rw [Real.log_pow] at h2
    have h3 : Real.log 2 < 1 := by
      have := Real.log_two_lt_d9; linarith
    have h4 : ((k+1:ℕ):ℝ) * Real.log 2 ≤ ((k+1:ℕ):ℝ) := by
      have : (0:ℝ) ≤ ((k+1:ℕ):ℝ) := by positivity
      nlinarith
    push_cast at h2 h4
    linarith
  have hL : x/2 - 1 ≤ ((max 1 (k / 2) : ℕ) : ℝ) := by
    have h1 : k ≤ 2 * (k/2) + 1 := by omega
    have h2 : (k:ℝ) ≤ 2 * ((k/2 : ℕ):ℝ) + 1 := by exact_mod_cast h1
    have h3 : ((k/2 : ℕ):ℝ) ≤ ((max 1 (k / 2) : ℕ) : ℝ) := by exact_mod_cast le_max_right _ _
    linarith
  have hexp : Real.exp (-((max 1 (k / 2) : ℕ) : ℝ)/8) ≤ Real.exp (1/8) * Real.exp (-(x/16)) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    linarith
  have hb := hX x hxX
  have hpoly : (1 + x)^4 ≤ 8 * (1 + x^4) := by
    nlinarith [mul_nonneg (sq_nonneg (x-1)) (by nlinarith [sq_nonneg (x + 5/7)] : (0:ℝ) ≤ 7*x^2 + 10*x + 7)]
  have hE : 0 < Real.exp (-(x/16)) := Real.exp_pos _
  have hE2 : 0 < Real.exp (1/8) := Real.exp_pos _
  have key : (1 + x)^4 * Real.exp (-((max 1 (k / 2) : ℕ) : ℝ)/8) ≤ 1/2304 := by
    calc (1 + x)^4 * Real.exp (-((max 1 (k / 2) : ℕ) : ℝ)/8)
        ≤ (8 * (1 + x^4)) * (Real.exp (1/8) * Real.exp (-(x/16))) := by
          apply mul_le_mul hpoly hexp (Real.exp_pos _).le (by positivity)
      _ = Real.exp (1/8) * (8 * Real.exp (-(x/16)) + 8 * 65536 * ((x/16)^4 * Real.exp (-(x/16)))) := by ring
      _ ≤ Real.exp (1/8) * (1 / (2304 * Real.exp (1/8))) := by
          apply mul_le_mul_of_nonneg_left hb.le hE2.le
      _ = 1/2304 := by field_simp
  calc (n:ℝ) * (1 + x)^4 * Real.exp (-((max 1 (k / 2) : ℕ) : ℝ)/8)
      = (n:ℝ) * ((1 + x)^4 * Real.exp (-((max 1 (k / 2) : ℕ) : ℝ)/8)) := by ring
    _ ≤ (n:ℝ) * (1/2304) := mul_le_mul_of_nonneg_left key hnpos.le
    _ = (n:ℝ)/2304 := by ring

private lemma split4' (B W Wo : Set ℝ) (hB : MeasurableSet B) (hW : MeasurableSet W)
    (hWo : MeasurableSet Wo) (F : ℝ → ℝ) (hF : Continuous F)
    (T R : ℝ) (hT : 0 ≤ T)
    (hR : intervalIntegral (B.indicator (fun _ => (1:ℝ))) 0 1 MeasureTheory.volume ≤ R)
    (c1 c2 c3 c4 : ℝ)
    (h1 : intervalIntegral (((B ∩ W) ∩ Wo).indicator F) 0 1 MeasureTheory.volume ≤ c1)
    (h2 : intervalIntegral (((B ∩ W) \ Wo).indicator F) 0 1 MeasureTheory.volume ≤ c2)
    (h3 : intervalIntegral (((B \ W) ∩ {t : ℝ | T < F t}).indicator F) 0 1 MeasureTheory.volume ≤ c3)
    (h4 : T * R ≤ c4) :
    intervalIntegral (B.indicator F) 0 1 MeasureTheory.volume ≤ c1 + c2 + c3 + c4 := by
  have := split4 B W Wo hB hW hWo F hF T R hT hR
  linarith

theorem Conjectures.Goldbach.PacketEnergyFromRationalRegions :
    (let w := fun k : ℕ => if Nat.Prime k then Real.log (k:ℝ) else 0; let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let S := fun (n : ℕ) (w : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (w k:ℂ)*E ((k:ℝ)*t)); let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let arcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (Q n:ℝ)/((q:ℝ)*(n:ℝ))}; let low := fun (n k : ℕ) => if k^3≤n then w k else 0; let high := fun (n k : ℕ) => w k-low n k; let L := fun n : ℕ => max 1 (Nat.log 2 n / 2); let K := fun (n : ℕ) (t : ℝ) => (∑ j ∈ Finset.range (L n), Real.cos (2*Real.pi*(2:ℝ)^(j+1)*t))/(L n:ℝ); let B := fun n : ℕ => {t : ℝ | t ∉ arcs n ∧ (1:ℝ)/2 < K n t}; let W := fun (n : ℕ) (p : ℕ → Prop) => {t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ (Q n)^2 ∧ a ≤ q ∧ Nat.Coprime a q ∧ p q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ ((Q n:ℝ)^2)/((q:ℝ)*(n:ℝ))}; let o := fun n q : ℕ => Odd q ∧ ∃ j : ℕ, 1 ≤ j ∧ j ≤ (Nat.log 2 (Q n)+1)^2 ∧ q ∣ 2^j-1; let F := fun (n : ℕ) (t : ℝ) => ‖S n (high n) t‖^2; let m := fun (s : Set ℝ) (f : ℝ → ℝ) => intervalIntegral (s.indicator f) (0:ℝ) 1 MeasureTheory.volume; ∃ N : ℕ, ∀ n ≥ N, Even n → m ((B n ∩ (W n (fun _ => True))) ∩ W n (o n)) (F n) ≤ (n:ℝ)/2304) → (let w := fun k : ℕ => if Nat.Prime k then Real.log (k:ℝ) else 0; let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let S := fun (n : ℕ) (w : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (w k:ℂ)*E ((k:ℝ)*t)); let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let arcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (Q n:ℝ)/((q:ℝ)*(n:ℝ))}; let low := fun (n k : ℕ) => if k^3≤n then w k else 0; let high := fun (n k : ℕ) => w k-low n k; let L := fun n : ℕ => max 1 (Nat.log 2 n / 2); let K := fun (n : ℕ) (t : ℝ) => (∑ j ∈ Finset.range (L n), Real.cos (2*Real.pi*(2:ℝ)^(j+1)*t))/(L n:ℝ); let B := fun n : ℕ => {t : ℝ | t ∉ arcs n ∧ (1:ℝ)/2 < K n t}; let W := fun (n : ℕ) (p : ℕ → Prop) => {t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ (Q n)^2 ∧ a ≤ q ∧ Nat.Coprime a q ∧ p q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ ((Q n:ℝ)^2)/((q:ℝ)*(n:ℝ))}; let o := fun n q : ℕ => Odd q ∧ ∃ j : ℕ, 1 ≤ j ∧ j ≤ (Nat.log 2 (Q n)+1)^2 ∧ q ∣ 2^j-1; let F := fun (n : ℕ) (t : ℝ) => ‖S n (high n) t‖^2; let m := fun (s : Set ℝ) (f : ℝ → ℝ) => intervalIntegral (s.indicator f) (0:ℝ) 1 MeasureTheory.volume; ∃ N : ℕ, ∀ n ≥ N, Even n → m ((B n ∩ (W n (fun _ => True))) \ W n (o n)) (F n) ≤ (n:ℝ)/2304) → (let w := fun k : ℕ => if Nat.Prime k then Real.log (k:ℝ) else 0; let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let S := fun (n : ℕ) (w : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (w k:ℂ)*E ((k:ℝ)*t)); let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let arcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (Q n:ℝ)/((q:ℝ)*(n:ℝ))}; let low := fun (n k : ℕ) => if k^3≤n then w k else 0; let high := fun (n k : ℕ) => w k-low n k; let L := fun n : ℕ => max 1 (Nat.log 2 n / 2); let K := fun (n : ℕ) (t : ℝ) => (∑ j ∈ Finset.range (L n), Real.cos (2*Real.pi*(2:ℝ)^(j+1)*t))/(L n:ℝ); let B := fun n : ℕ => {t : ℝ | t ∉ arcs n ∧ (1:ℝ)/2 < K n t}; let W := fun (n : ℕ) (p : ℕ → Prop) => {t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ (Q n)^2 ∧ a ≤ q ∧ Nat.Coprime a q ∧ p q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ ((Q n:ℝ)^2)/((q:ℝ)*(n:ℝ))}; let F := fun (n : ℕ) (t : ℝ) => ‖S n (high n) t‖^2; let T := fun n : ℕ => (n:ℝ)*(1+Real.log (n:ℝ))^4; let m := fun (s : Set ℝ) (f : ℝ → ℝ) => intervalIntegral (s.indicator f) (0:ℝ) 1 MeasureTheory.volume; ∃ N : ℕ, ∀ n ≥ N, Even n → m ((B n \ (W n (fun _ => True))) ∩ {t : ℝ | T n < F n t}) (F n) ≤ (n:ℝ)/2304) → (let w := fun k : ℕ => if Nat.Prime k then Real.log (k:ℝ) else 0; let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let S := fun (n : ℕ) (w : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (w k:ℂ)*E ((k:ℝ)*t)); let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let arcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (Q n:ℝ)/((q:ℝ)*(n:ℝ))}; let low := fun (n k : ℕ) => if k^3≤n then w k else 0; let high := fun (n k : ℕ) => w k-low n k; let I := fun (n:ℕ) (a b:ℕ→ℝ) => intervalIntegral (fun t => (arcs n)ᶜ.indicator (fun u => S n a u*S n b u*E (-(n:ℝ)*u)) t) (0:ℝ) 1 MeasureTheory.volume; let L := fun n : ℕ => max 1 (Nat.log 2 n / 2); let K := fun (n : ℕ) (t : ℝ) => (∑ j ∈ Finset.range (L n), Real.cos (2*Real.pi*(2:ℝ)^(j+1)*t))/(L n:ℝ); let B := fun n : ℕ => {t : ℝ | t ∉ arcs n ∧ (1:ℝ)/2 < K n t}; let U := fun (n : ℕ) (a : ℕ → ℝ) => intervalIntegral ((B n).indicator (fun t => ‖S n a t‖^2)) (0:ℝ) 1 MeasureTheory.volume; ∃ N : ℕ, ∀ n ≥ N, Even n → U n (high n) ≤ (n:ℝ)/576) := by
  intro h1 h2 h3
  dsimp only at h1 h2 h3 ⊢
  obtain ⟨N1, hN1⟩ := h1
  obtain ⟨N2, hN2⟩ := h2
  obtain ⟨N3, hN3⟩ := h3
  obtain ⟨N4, hN4⟩ := tail_small
  refine ⟨max (max N1 N2) (max N3 N4), fun n hn he => ?_⟩
  have a1 := hN1 n (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn) he
  have a2 := hN2 n (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn) he
  have a3 := hN3 n (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hn) he
  have a4 := hN4 n (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hn)
  have key := split4' _ _ _ (meas_B _ (meas_arc _ _ _) _) (meas_W _ _ _ _) (meas_W _ _ _ _) _ (by fun_prop)
    ((n:ℝ) * (1 + Real.log (n:ℝ))^4) (Real.exp (-((max 1 (Nat.log 2 n / 2) : ℕ) : ℝ)/8))
    (by positivity) (B_bound _ (meas_arc _ _ _) _ (by omega)) _ _ _ _ a1 a2 a3 a4
  linarith
