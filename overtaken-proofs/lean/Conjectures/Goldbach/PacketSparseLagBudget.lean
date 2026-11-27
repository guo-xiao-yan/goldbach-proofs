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

private theorem tail_half (m : ℕ) (hm : 0 < m) :
    intervalIntegral (fun t => if (m:ℝ)/2 < ∑ j ∈ Finset.range m, Real.cos (2*Real.pi*(2:ℝ)^(j+1)*t) then (1:ℝ) else 0) (0:ℝ) 1 MeasureTheory.volume ≤ Real.exp (-(m:ℝ)/8) := by
  let T := fun (m : ℕ) (t : ℝ) => ∑ j ∈ Finset.range m, Real.cos (2*Real.pi*(2:ℝ)^(j+1)*t)
  show intervalIntegral (fun t => if (m:ℝ)/2 < T m t then (1:ℝ) else 0) (0:ℝ) 1 MeasureTheory.volume ≤ _
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

private theorem vb (m : ℕ) (hm : 0 < m) (Bs : Set ℝ)
    (hB : ∀ t ∈ Bs, (m:ℝ)/2 < ∑ j ∈ Finset.range m, Real.cos (2*Real.pi*(2:ℝ)^(j+1)*t)) (h : ℕ) :
    |intervalIntegral (Bs.indicator (fun t => Real.cos (2*Real.pi*(h:ℝ)*t))) (0:ℝ) 1 MeasureTheory.volume|
      ≤ Real.exp (-(m:ℝ)/8) := by
  let T := fun (m : ℕ) (t : ℝ) => ∑ j ∈ Finset.range m, Real.cos (2*Real.pi*(2:ℝ)^(j+1)*t)
  have hTc : Continuous (T m) := by
    simp only [T]; fun_prop
  have hint : IntervalIntegrable (fun t => if (m:ℝ)/2 < T m t then (1:ℝ) else 0)
      MeasureTheory.volume 0 1 := by
    have hmeas : Measurable (fun t => if (m:ℝ)/2 < T m t then (1:ℝ) else 0) :=
      Measurable.ite (measurableSet_lt measurable_const hTc.measurable) measurable_const measurable_const
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
    refine MeasureTheory.Measure.integrableOn_of_bounded (M := 1) (by simp) hmeas.aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall fun t => ?_
    split_ifs <;> simp
  rw [← Real.norm_eq_abs]
  refine (intervalIntegral.norm_integral_le_of_norm_le zero_le_one
    (Filter.Eventually.of_forall fun t _ => ?_) hint).trans (tail_half m hm)
  by_cases ht : t ∈ Bs
  · rw [Set.indicator_of_mem ht, if_pos (hB t ht)]
    simpa using Real.abs_cos_le_one _
  · rw [Set.indicator_of_notMem ht]
    split_ifs <;> simp

private theorem ab (n h : ℕ) (a : ℕ → ℝ) (M : ℝ) (hM : ∀ k ≤ n, |a k| ≤ M) :
    |∑ k ∈ Finset.range (n+1-h), a k * a (k+h)| ≤ ((n:ℝ)+1) * M^2 := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have : ∀ k ∈ Finset.range (n+1-h), |a k * a (k+h)| ≤ M^2 := by
    intro k hk
    rw [Finset.mem_range] at hk
    rw [abs_mul, sq]
    exact mul_le_mul (hM k (by omega)) (hM (k+h) (by omega)) (abs_nonneg _) ((abs_nonneg _).trans (hM k (by omega)))
  refine (Finset.sum_le_card_nsmul _ _ _ this).trans ?_
  rw [nsmul_eq_mul, Finset.card_range]
  have h1 : ((n+1-h : ℕ):ℝ) ≤ (n:ℝ)+1 := by
    have : n+1-h ≤ n+1 := Nat.sub_le _ _
    exact_mod_cast this
  exact mul_le_mul_of_nonneg_right h1 (sq_nonneg _)

private theorem decay (δ : ℝ) (hδ : 0 < δ) :
    ∃ N : ℕ, ∀ n ≥ N, (Real.log n)^2 * Real.exp (-(Real.log n)/32) ≤ δ := by
  have h1 := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 2 (1/32) (by norm_num)
  have h2 : ∀ᶠ u : ℝ in Filter.atTop, u^(2:ℝ) * Real.exp (-(1/32) * u) < δ :=
    h1.eventually (gt_mem_nhds hδ)
  obtain ⟨U, hU⟩ := Filter.eventually_atTop.mp h2
  refine ⟨⌈Real.exp (max U 0)⌉₊ + 1, fun n hn => ?_⟩
  have hn' : Real.exp (max U 0) ≤ n := by
    have := Nat.le_ceil (Real.exp (max U 0))
    have : ((⌈Real.exp (max U 0)⌉₊ : ℕ):ℝ) ≤ n := by exact_mod_cast (by omega : ⌈Real.exp (max U 0)⌉₊ ≤ n)
    linarith [Nat.le_ceil (Real.exp (max U 0))]
  have hnpos : (0:ℝ) < n := lt_of_lt_of_le (Real.exp_pos _) hn'
  have hlog : max U 0 ≤ Real.log n := by
    rw [Real.le_log_iff_exp_le hnpos]; exact hn'
  have := hU (Real.log n) ((le_max_left _ _).trans hlog)
  have e : (Real.log n)^(2:ℝ) = (Real.log n)^2 := by norm_cast
  rw [e] at this
  have e2 : -(1/32:ℝ) * Real.log n = -(Real.log n)/32 := by ring
  rw [e2] at this
  exact this.le

theorem Conjectures.Goldbach.PacketSparseLagBudget :
    let w := fun k : ℕ => if Nat.Prime k then Real.log (k:ℝ) else 0; let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let S := fun (n : ℕ) (w : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (w k:ℂ)*E ((k:ℝ)*t)); let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let arcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (Q n:ℝ)/((q:ℝ)*(n:ℝ))}; let low := fun (n k : ℕ) => if k^3≤n then w k else 0; let high := fun (n k : ℕ) => w k-low n k; let I := fun (n:ℕ) (a b:ℕ→ℝ) => intervalIntegral (fun t => (arcs n)ᶜ.indicator (fun u => S n a u*S n b u*E (-(n:ℝ)*u)) t) (0:ℝ) 1 MeasureTheory.volume; let L := fun n : ℕ => max 1 (Nat.log 2 n / 2); let K := fun (n : ℕ) (t : ℝ) => (∑ j ∈ Finset.range (L n), Real.cos (2*Real.pi*(2:ℝ)^(j+1)*t))/(L n:ℝ); let B := fun n : ℕ => {t : ℝ | t ∉ arcs n ∧ (1:ℝ)/2 < K n t}; let U := fun (n : ℕ) (a : ℕ → ℝ) => intervalIntegral ((B n).indicator (fun t => ‖S n a t‖^2)) (0:ℝ) 1 MeasureTheory.volume; let V := fun (n h : ℕ) => intervalIntegral ((B n).indicator (fun t => Real.cos (2*Real.pi*(h:ℝ)*t))) (0:ℝ) 1 MeasureTheory.volume; let A := fun (n h : ℕ) (a : ℕ → ℝ) => ∑ k ∈ Finset.range (n+1-h), a k * a (k+h); ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, ∀ (F : Finset ℕ) (a : ℕ → ℝ), (F.card:ℝ) ≤ Real.exp ((L n:ℝ)/16) → (∀ k ≤ n, |a k| ≤ 4*(1+Real.log (n:ℝ))) → (∑ h ∈ F, |A n h a * V n h|) ≤ ε*(n:ℝ) := by
  intro w E S Q arcs low high I L K B U V A ε hε
  obtain ⟨N0, hN0⟩ := decay (ε/384) (by positivity)
  refine ⟨max N0 3, fun n hn F a hF ha => ?_⟩
  have hn3 : 3 ≤ n := le_trans (le_max_right _ _) hn
  have hnN0 : N0 ≤ n := le_trans (le_max_left _ _) hn
  have hnr : (3:ℝ) ≤ n := by exact_mod_cast hn3
  have hLpos : 0 < L n := lt_of_lt_of_le one_pos (le_max_left _ _)
  have hLr : (0:ℝ) < (L n : ℝ) := by exact_mod_cast hLpos
  have hVb : ∀ h, |V n h| ≤ Real.exp (-(L n : ℝ)/8) := by
    intro h
    refine vb (L n) hLpos (B n) ?_ h
    intro t ht
    have h2 : (1:ℝ)/2 < (∑ j ∈ Finset.range (L n), Real.cos (2*Real.pi*(2:ℝ)^(j+1)*t))/(L n:ℝ) := ht.2
    rw [lt_div_iff₀ hLr] at h2
    linarith
  set u := Real.log (n:ℝ) with hu
  have hu1 : 1 ≤ u := by
    rw [hu, Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_d9
    linarith
  have hM : ∀ k ≤ n, |a k| ≤ 4*(1+u) := ha
  have hAb : ∀ h, |A n h a| ≤ ((n:ℝ)+1) * (4*(1+u))^2 := fun h => ab n h a _ hM
  have hL : (u - 2)/2 ≤ (L n : ℝ) := by
    have hlt : n < 2^(Nat.log 2 n + 1) := Nat.lt_pow_succ_log_self (by norm_num) n
    have h1 : u < ((Nat.log 2 n : ℕ):ℝ) + 1 := by
      have : (n:ℝ) < 2^(Nat.log 2 n + 1) := by exact_mod_cast hlt
      have h3 := Real.log_lt_log (by linarith) this
      rw [Real.log_pow] at h3
      have h4 := Real.log_two_lt_d9
      push_cast at h3
      have h5 : (0:ℝ) ≤ ((Nat.log 2 n : ℕ):ℝ) + 1 := by positivity
      nlinarith
    have h2 : (((Nat.log 2 n : ℕ):ℝ) - 1)/2 ≤ ((Nat.log 2 n / 2 : ℕ):ℝ) := by
      have : Nat.log 2 n ≤ 2 * (Nat.log 2 n / 2) + 1 := by omega
      have : ((Nat.log 2 n : ℕ):ℝ) ≤ 2 * ((Nat.log 2 n / 2 : ℕ):ℝ) + 1 := by exact_mod_cast this
      linarith
    have h3 : ((Nat.log 2 n / 2 : ℕ):ℝ) ≤ (L n : ℝ) := by
      have : Nat.log 2 n / 2 ≤ L n := le_max_right _ _
      exact_mod_cast this
    linarith
  have hexp : Real.exp (-(L n:ℝ)/16) ≤ 3 * Real.exp (-u/32) := by
    have h1 : Real.exp (-(L n:ℝ)/16) ≤ Real.exp (-(u-2)/32) := by
      apply Real.exp_le_exp.mpr; linarith
    have h2 : Real.exp (-(u-2)/32) = Real.exp (1/16) * Real.exp (-u/32) := by
      rw [← Real.exp_add]; congr 1; ring
    have h3 : Real.exp (1/16) ≤ 3 := by
      have : Real.exp (1/16) ≤ Real.exp 1 := Real.exp_le_exp.mpr (by norm_num)
      have := Real.exp_one_lt_d9
      linarith
    rw [h2] at h1
    have := Real.exp_pos (-u/32)
    nlinarith
  have hterm : ∀ h ∈ F, |A n h a * V n h| ≤ ((n:ℝ)+1) * (4*(1+u))^2 * Real.exp (-(L n : ℝ)/8) := by
    intro h _
    rw [abs_mul]
    exact mul_le_mul (hAb h) (hVb h) (abs_nonneg _) (by positivity)
  have hsum := Finset.sum_le_card_nsmul F _ _ hterm
  rw [nsmul_eq_mul] at hsum
  have hdec := hN0 n hnN0
  have hexpL : Real.exp ((L n:ℝ)/16) * Real.exp (-(L n : ℝ)/8) = Real.exp (-(L n : ℝ)/16) := by
    rw [← Real.exp_add]; congr 1; ring
  have hpos : 0 ≤ ((n:ℝ)+1) * (4*(1+u))^2 * Real.exp (-(L n : ℝ)/8) := by positivity
  have h1 : (F.card:ℝ) * (((n:ℝ)+1) * (4*(1+u))^2 * Real.exp (-(L n : ℝ)/8))
      ≤ Real.exp ((L n:ℝ)/16) * (((n:ℝ)+1) * (4*(1+u))^2 * Real.exp (-(L n : ℝ)/8)) :=
    mul_le_mul_of_nonneg_right hF hpos
  have h2 : Real.exp ((L n:ℝ)/16) * (((n:ℝ)+1) * (4*(1+u))^2 * Real.exp (-(L n : ℝ)/8))
      = ((n:ℝ)+1) * (4*(1+u))^2 * Real.exp (-(L n : ℝ)/16) := by
    rw [← hexpL]; ring
  have h3 : ((n:ℝ)+1) * (4*(1+u))^2 * Real.exp (-(L n : ℝ)/16)
      ≤ (2 * n) * (64 * u^2) * (3 * Real.exp (-u/32)) := by
    have hu2 : (1+u)^2 ≤ 4 * u^2 := by nlinarith
    have e1 : (4*(1+u))^2 ≤ 64 * u^2 := by nlinarith
    have e2 : (n:ℝ)+1 ≤ 2 * n := by linarith
    have hc : 0 ≤ Real.exp (-(L n : ℝ)/16) := (Real.exp_pos _).le
    calc ((n:ℝ)+1) * (4*(1+u))^2 * Real.exp (-(L n : ℝ)/16)
        ≤ (2 * n) * (64 * u^2) * Real.exp (-(L n : ℝ)/16) := by
          apply mul_le_mul_of_nonneg_right _ hc
          exact mul_le_mul e2 e1 (by positivity) (by positivity)
      _ ≤ (2 * n) * (64 * u^2) * (3 * Real.exp (-u/32)) :=
          mul_le_mul_of_nonneg_left hexp (by positivity)
  have h4 : (2 * (n:ℝ)) * (64 * u^2) * (3 * Real.exp (-u/32)) = 384 * n * (u^2 * Real.exp (-u/32)) := by ring
  have h5 : 384 * (n:ℝ) * (u^2 * Real.exp (-u/32)) ≤ 384 * n * (ε/384) :=
    mul_le_mul_of_nonneg_left hdec (by positivity)
  have h6 : 384 * (n:ℝ) * (ε/384) = ε * n := by ring
  linarith
