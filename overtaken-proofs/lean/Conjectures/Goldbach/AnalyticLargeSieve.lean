import Mathlib

namespace GbLS

noncomputable def E (x : ℝ) : ℂ := Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)

theorem E_add (x y : ℝ) : E (x + y) = E x * E y := by
  unfold E
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem E_norm (x : ℝ) : ‖E x‖ = 1 := by
  unfold E
  exact Complex.norm_exp_ofReal_mul_I _

theorem E_neg (x : ℝ) : E (-x) = (starRingEnd ℂ) (E x) := by
  unfold E
  rw [← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I]
  congr 1
  push_cast
  ring

theorem E_cont : Continuous E := by
  unfold E
  fun_prop

theorem integral_E (m : ℤ) :
    ∫ t in (0:ℝ)..1, E ((m : ℝ) * t) = if m = 0 then 1 else 0 := by
  by_cases hm : m = 0
  · subst hm
    simp [E]
  · rw [if_neg hm]
    have hc : (2 * Real.pi * (m:ℝ) : ℂ) * Complex.I ≠ 0 := by
      have : (m:ℂ) ≠ 0 := by exact_mod_cast hm
      simp [Real.pi_ne_zero, Complex.I_ne_zero, this]
    have : ∀ t : ℝ, E ((m : ℝ) * t) = Complex.exp (((2 * Real.pi * (m:ℝ) : ℂ) * Complex.I) * (t:ℂ)) := by
      intro t
      unfold E
      congr 1
      push_cast
      ring
    simp_rw [this]
    rw [integral_exp_mul_complex hc]
    have h1 : Complex.exp (((2 * Real.pi * (m:ℝ) : ℂ) * Complex.I) * ((1:ℝ):ℂ)) = 1 := by
      have : ((2 * Real.pi * (m:ℝ) : ℂ) * Complex.I) * ((1:ℝ):ℂ) = (m:ℂ) * (2 * Real.pi * Complex.I) := by
        push_cast; ring
      rw [this, Complex.exp_int_mul_two_pi_mul_I]
    rw [h1]
    simp

theorem parseval (s : Finset ℕ) (d : ℕ → ℂ) :
    ∫ t in (0:ℝ)..1, ‖∑ k ∈ s, d k * E ((k : ℝ) * t)‖ ^ 2 = ∑ k ∈ s, ‖d k‖ ^ 2 := by
  apply Complex.ofReal_injective
  have key : ∀ t : ℝ, (((‖∑ k ∈ s, d k * E ((k : ℝ) * t)‖ ^ 2 : ℝ)) : ℂ) =
      ∑ k ∈ s, ∑ l ∈ s, d k * (starRingEnd ℂ) (d l) * E ((k:ℝ) * t - (l:ℝ) * t) := by
    intro t
    push_cast
    rw [← Complex.mul_conj', map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    have : E ((k:ℝ) * t - (l:ℝ) * t) = E ((k:ℝ) * t) * (starRingEnd ℂ) (E ((l:ℝ) * t)) := by
      rw [sub_eq_add_neg, E_add, ← E_neg]
    rw [this, map_mul]
    ring
  rw [← intervalIntegral.integral_ofReal]
  simp_rw [key]
  have hint : ∀ k l : ℕ, IntervalIntegrable (fun t : ℝ => d k * (starRingEnd ℂ) (d l) * E ((k:ℝ) * t - (l:ℝ) * t)) MeasureTheory.volume 0 1 := by
    intro k l
    exact (continuous_const.mul (E_cont.comp (by fun_prop))).intervalIntegrable 0 1
  have hc : ∀ k l : ℕ, Continuous (fun t : ℝ => d k * (starRingEnd ℂ) (d l) * E ((k:ℝ) * t - (l:ℝ) * t)) := by
    intro k l
    exact continuous_const.mul (E_cont.comp (by fun_prop))
  rw [intervalIntegral.integral_finsetSum (fun k _ =>
    (continuous_finsetSum _ fun l _ => hc k l).intervalIntegrable 0 1)]
  push_cast
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [intervalIntegral.integral_finsetSum (fun l _ => (hc k l).intervalIntegrable 0 1)]
  have : ∀ l ∈ s, ∫ t in (0:ℝ)..1, d k * (starRingEnd ℂ) (d l) * E ((k:ℝ) * t - (l:ℝ) * t)
      = if k = l then d k * (starRingEnd ℂ) (d k) else 0 := by
    intro l _
    rw [intervalIntegral.integral_const_mul]
    have e : ∀ t : ℝ, E ((k:ℝ) * t - (l:ℝ) * t) = E ((((k:ℤ) - (l:ℤ) : ℤ) : ℝ) * t) := by
      intro t; congr 1; push_cast; ring
    simp_rw [e]
    rw [integral_E]
    by_cases h : k = l
    · subst h; simp
    · have : ((k:ℤ) - (l:ℤ)) ≠ 0 := by omega
      simp [h, this]
  rw [Finset.sum_congr rfl this]
  simp [hk, Complex.mul_conj']

theorem E_nat_one (k : ℕ) : E (k : ℝ) = 1 := by
  unfold E
  have : ((2 * Real.pi * (k : ℝ) : ℝ) : ℂ) * Complex.I = (k : ℂ) * (2 * Real.pi * Complex.I) := by
    push_cast; ring
  rw [this]
  exact Complex.exp_nat_mul_two_pi_mul_I k

theorem E_hasDeriv (x : ℝ) : HasDerivAt E ((2 * Real.pi * Complex.I) * E x) x := by
  have h1 : HasDerivAt (fun y : ℝ => ((2 * Real.pi * y : ℝ) : ℂ) * Complex.I)
      (((2 * Real.pi : ℝ) : ℂ) * Complex.I) x := by
    have h0 : HasDerivAt (fun y : ℝ => 2 * Real.pi * y) (2 * Real.pi) x := by
      simpa using (hasDerivAt_id x).const_mul (2 * Real.pi)
    have := (h0.ofReal_comp).mul_const Complex.I
    simpa using this
  have := h1.cexp
  unfold E
  convert this using 1
  push_cast
  ring

noncomputable def SS (M N : ℕ) (c : ℕ → ℂ) (t : ℝ) : ℂ :=
  ∑ k ∈ Finset.Ico M (M + N), c k * E ((k : ℝ) * t)

noncomputable def c0 (M N : ℕ) : ℝ := (M : ℝ) + ((N : ℝ) - 1) / 2

noncomputable def TT (M N : ℕ) (c : ℕ → ℂ) (t : ℝ) : ℂ :=
  ∑ k ∈ Finset.Ico M (M + N),
    (c k * (2 * Real.pi * Complex.I * (((k : ℝ) - c0 M N : ℝ) : ℂ))) * E ((k : ℝ) * t)

theorem SS_cont (M N : ℕ) (c : ℕ → ℂ) : Continuous (SS M N c) := by
  unfold SS
  exact continuous_finsetSum _ fun k _ => continuous_const.mul (E_cont.comp (by fun_prop))

theorem TT_cont (M N : ℕ) (c : ℕ → ℂ) : Continuous (TT M N c) := by
  unfold TT
  exact continuous_finsetSum _ fun k _ => continuous_const.mul (E_cont.comp (by fun_prop))

theorem SS_per (M N : ℕ) (c : ℕ → ℂ) (t : ℝ) : SS M N c (t + 1) = SS M N c t := by
  unfold SS
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_add, mul_one, E_add, E_nat_one, mul_one]

theorem TT_per (M N : ℕ) (c : ℕ → ℂ) (t : ℝ) : TT M N c (t + 1) = TT M N c t := by
  unfold TT
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_add, mul_one, E_add, E_nat_one, mul_one]

theorem SS_deriv (M N : ℕ) (c : ℕ → ℂ) (t : ℝ) :
    HasDerivAt (SS M N c)
      (TT M N c t + 2 * Real.pi * Complex.I * ((c0 M N : ℝ) : ℂ) * SS M N c t) t := by
  have h : ∀ k ∈ Finset.Ico M (M + N), HasDerivAt (fun t : ℝ => c k * E ((k : ℝ) * t))
      (c k * (2 * Real.pi * Complex.I * (k : ℂ) * E ((k : ℝ) * t))) t := by
    intro k _
    have h1 : HasDerivAt (fun t : ℝ => (k : ℝ) * t) (k : ℝ) t := by
      simpa using (hasDerivAt_id t).const_mul (k : ℝ)
    have h2 := (E_hasDeriv ((k : ℝ) * t)).scomp t h1
    have h3 := h2.const_mul (c k)
    refine h3.congr_deriv ?_
    rw [Complex.real_smul]
    push_cast
    ring
  have := HasDerivAt.fun_sum h
  have hfun : SS M N c = fun t : ℝ => ∑ k ∈ Finset.Ico M (M + N), c k * E ((k : ℝ) * t) := rfl
  rw [hfun]
  convert this using 1
  beta_reduce
  unfold TT
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  push_cast
  ring

theorem f_deriv (M N : ℕ) (c : ℕ → ℂ) (t : ℝ) :
    HasDerivAt (fun t => ‖SS M N c t‖ ^ 2)
      (2 * ((TT M N c t * (starRingEnd ℂ) (SS M N c t)).re)) t := by
  have h := (SS_deriv M N c t).norm_sq
  convert h using 2
  rw [Complex.inner]
  rw [add_mul, Complex.add_re]
  have : (2 * Real.pi * Complex.I * ((c0 M N : ℝ) : ℂ) * SS M N c t * (starRingEnd ℂ) (SS M N c t)).re = 0 := by
    rw [mul_assoc, Complex.mul_conj]
    simp [Complex.mul_re]
  rw [this, add_zero]

theorem f_deriv_bound (M N : ℕ) (c : ℕ → ℂ) (t : ℝ) :
    |2 * ((TT M N c t * (starRingEnd ℂ) (SS M N c t)).re)| ≤ 2 * (‖SS M N c t‖ * ‖TT M N c t‖) := by
  rw [abs_mul, abs_two]
  have := Complex.abs_re_le_norm (TT M N c t * (starRingEnd ℂ) (SS M N c t))
  rw [norm_mul, Complex.norm_conj] at this
  nlinarith

theorem half_bound (f f' : ℝ → ℝ) (hf : ∀ x, HasDerivAt f (f' x) x) (hf' : Continuous f')
    (a b x : ℝ) (hab : a ≤ b) (hxa : a ≤ x) (hxb : x ≤ b) :
    (b - a) * f x ≤ (∫ y in a..b, f y) + (b - a) * ∫ y in a..b, |f' y| := by
  have hcf : Continuous f := continuous_iff_continuousAt.2 fun x => (hf x).continuousAt
  have hi : ∀ p q : ℝ, IntervalIntegrable (fun y => |f' y|) MeasureTheory.volume p q :=
    fun p q => (hf'.abs).intervalIntegrable p q
  have hnn : 0 ≤ᵐ[MeasureTheory.volume.restrict (Set.Ioc a b)] fun y => |f' y| :=
    Filter.Eventually.of_forall fun y => abs_nonneg _
  have key : ∀ y ∈ Set.Icc a b, f x ≤ f y + ∫ z in a..b, |f' z| := by
    intro y hy
    rcases le_total y x with hyx | hxy
    · have h1 : ∫ z in y..x, f' z = f x - f y :=
        intervalIntegral.integral_eq_sub_of_hasDerivAt (fun z _ => hf z) (hf'.intervalIntegrable _ _)
      have h2 : ∫ z in y..x, f' z ≤ ∫ z in y..x, |f' z| :=
        intervalIntegral.integral_mono_on hyx (hf'.intervalIntegrable _ _) (hi _ _)
          (fun z _ => le_abs_self _)
      have h3 : ∫ z in y..x, |f' z| ≤ ∫ z in a..b, |f' z| :=
        intervalIntegral.integral_mono_interval hy.1 hyx hxb hnn (hi _ _)
      linarith
    · have h1 : ∫ z in x..y, f' z = f y - f x :=
        intervalIntegral.integral_eq_sub_of_hasDerivAt (fun z _ => hf z) (hf'.intervalIntegrable _ _)
      have h2 : -(∫ z in x..y, f' z) ≤ ∫ z in x..y, |f' z| := by
        rw [← intervalIntegral.integral_neg]
        exact intervalIntegral.integral_mono_on hxy (hf'.neg.intervalIntegrable _ _) (hi _ _)
          (fun z _ => neg_le_abs _)
      have h3 : ∫ z in x..y, |f' z| ≤ ∫ z in a..b, |f' z| :=
        intervalIntegral.integral_mono_interval hxa hxy hy.2 hnn (hi _ _)
      linarith
  have hc1 : IntervalIntegrable (fun _ : ℝ => f x) MeasureTheory.volume a b :=
    continuous_const.intervalIntegrable a b
  have hc3 : IntervalIntegrable (fun _ : ℝ => ∫ z in a..b, |f' z|) MeasureTheory.volume a b :=
    continuous_const.intervalIntegrable a b
  have hc2 : IntervalIntegrable (fun y => f y + ∫ z in a..b, |f' z|) MeasureTheory.volume a b :=
    (hcf.add continuous_const).intervalIntegrable a b
  have := intervalIntegral.integral_mono_on hab hc1 hc2 (fun y hy => key y hy)
  rw [intervalIntegral.integral_add (hcf.intervalIntegrable a b) hc3] at this
  simp at this
  linarith

theorem local_bound (f f' : ℝ → ℝ) (hf : ∀ x, HasDerivAt f (f' x) x) (hf' : Continuous f')
    (x0 δ : ℝ) (hδ : 0 < δ) :
    δ * f x0 ≤ (∫ y in (x0 - δ / 2)..(x0 + δ / 2), f y) +
      (δ / 2) * ∫ y in (x0 - δ / 2)..(x0 + δ / 2), |f' y| := by
  have hcf : Continuous f := continuous_iff_continuousAt.2 fun x => (hf x).continuousAt
  have h1 := half_bound f f' hf hf' (x0 - δ / 2) x0 x0 (by linarith) (by linarith) le_rfl
  have h2 := half_bound f f' hf hf' x0 (x0 + δ / 2) x0 (by linarith) le_rfl (by linarith)
  have e1 : x0 - (x0 - δ / 2) = δ / 2 := by ring
  have e2 : x0 + δ / 2 - x0 = δ / 2 := by ring
  rw [e1] at h1
  rw [e2] at h2
  have hs1 : ∫ y in (x0 - δ / 2)..(x0 + δ / 2), f y =
      (∫ y in (x0 - δ / 2)..x0, f y) + ∫ y in x0..(x0 + δ / 2), f y :=
    (intervalIntegral.integral_add_adjacent_intervals (hcf.intervalIntegrable _ _)
      (hcf.intervalIntegrable _ _)).symm
  have hs2 : ∫ y in (x0 - δ / 2)..(x0 + δ / 2), |f' y| =
      (∫ y in (x0 - δ / 2)..x0, |f' y|) + ∫ y in x0..(x0 + δ / 2), |f' y| :=
    (intervalIntegral.integral_add_adjacent_intervals (hf'.abs.intervalIntegrable _ _)
      (hf'.abs.intervalIntegrable _ _)).symm
  rw [hs1, hs2]
  nlinarith [h1, h2]

theorem sum_windows {ι : Type*} (s : Finset ι) (x : ι → ℝ) (δ : ℝ) (hδ : 0 < δ) (F : ℝ → ℝ)
    (hF : Continuous F) (hF0 : ∀ t, 0 ≤ F t) (hper : Function.Periodic F 1)
    (hx0 : ∀ i ∈ s, 0 ≤ x i) (hx1 : ∀ i ∈ s, x i ≤ 1 - δ)
    (hsp : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → δ ≤ |x i - x j|) :
    ∑ i ∈ s, ∫ y in (x i - δ / 2)..(x i + δ / 2), F y ≤ ∫ y in (0:ℝ)..1, F y := by
  have hW : ∀ i ∈ s, ∫ y in (x i - δ / 2)..(x i + δ / 2), F y =
      ∫ y in Set.Ioc (x i - δ / 2) (x i + δ / 2), F y :=
    fun i _ => intervalIntegral.integral_of_le (by linarith)
  rw [Finset.sum_congr rfl hW]
  have hdisj : Set.Pairwise (↑s : Set ι) (Function.onFun Disjoint
      (fun i => Set.Ioc (x i - δ / 2) (x i + δ / 2))) := by
    intro i hi j hj hij
    rw [Function.onFun, Set.disjoint_left]
    intro z hz1 hz2
    have h := hsp i hi j hj hij
    have : |x i - x j| < δ := abs_lt.mpr ⟨by
      simp only [Set.mem_Ioc] at hz1 hz2; linarith, by simp only [Set.mem_Ioc] at hz1 hz2; linarith⟩
    linarith
  rw [← MeasureTheory.integral_biUnion_finset s (fun i _ => measurableSet_Ioc) hdisj
    (fun i _ => (hF.intervalIntegrable _ _).1)]
  have hsub : (⋃ i ∈ s, Set.Ioc (x i - δ / 2) (x i + δ / 2)) ⊆ Set.Ioc (-(δ / 2)) (-(δ / 2) + 1) := by
    refine Set.iUnion₂_subset fun i hi => ?_
    intro z hz
    have := hx0 i hi
    have := hx1 i hi
    simp only [Set.mem_Ioc] at hz ⊢
    constructor <;> linarith [hz.1, hz.2]
  calc ∫ y in ⋃ i ∈ s, Set.Ioc (x i - δ / 2) (x i + δ / 2), F y
      ≤ ∫ y in Set.Ioc (-(δ / 2)) (-(δ / 2) + 1), F y :=
        MeasureTheory.setIntegral_mono_set (hF.intervalIntegrable _ _).1
          (Filter.Eventually.of_forall fun y => hF0 y) (Filter.Eventually.of_forall fun y hy => hsub hy)
    _ = ∫ y in (-(δ / 2))..(-(δ / 2) + 1), F y :=
        (intervalIntegral.integral_of_le (by linarith)).symm
    _ = ∫ y in (0:ℝ)..(0 + 1), F y := hper.intervalIntegral_add_eq _ _
    _ = ∫ y in (0:ℝ)..1, F y := by rw [zero_add]

theorem spacing (Q q a q' a' : ℕ) (hq : 1 ≤ q) (hq' : 1 ≤ q') (hqQ : q ≤ Q) (hq'Q : q' ≤ Q)
    (hc : Nat.Coprime a q) (hc' : Nat.Coprime a' q') (hne : q ≠ q' ∨ a ≠ a') :
    (1 : ℝ) / (Q : ℝ) ^ 2 ≤ |(a : ℝ) / q - (a' : ℝ) / q'| := by
  have hne' : a * q' ≠ a' * q := by
    intro h
    have h1 : q ∣ q' := by
      have : q ∣ a * q' := ⟨a', by rw [h]; ring⟩
      exact (Nat.Coprime.symm hc).dvd_of_dvd_mul_left this
    have h2 : q' ∣ q := by
      have : q' ∣ a' * q := ⟨a, by rw [← h]; ring⟩
      exact (Nat.Coprime.symm hc').dvd_of_dvd_mul_left this
    have hqq : q = q' := Nat.dvd_antisymm h1 h2
    subst hqq
    rcases hne with h3 | h3
    · exact h3 rfl
    · exact h3 (Nat.eq_of_mul_eq_mul_right hq h)
  have hz : (a : ℤ) * q' - a' * q ≠ 0 := by
    intro h
    apply hne'
    have : (a : ℤ) * q' = a' * q := by linarith
    exact_mod_cast this
  have h1 : (1 : ℝ) ≤ |(((a : ℤ) * q' - a' * q : ℤ) : ℝ)| := by
    have := Int.one_le_abs hz
    exact_mod_cast this
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq
  have hq'pos : (0 : ℝ) < q' := by exact_mod_cast hq'
  have e : (a : ℝ) / q - (a' : ℝ) / q' = (((a : ℤ) * q' - a' * q : ℤ) : ℝ) / ((q : ℝ) * q') := by
    push_cast
    field_simp
  rw [e, abs_div, abs_of_pos (mul_pos hqpos hq'pos)]
  have hQ : (q : ℝ) * q' ≤ (Q : ℝ) ^ 2 := by
    have : (q : ℝ) ≤ Q := by exact_mod_cast hqQ
    have : (q' : ℝ) ≤ Q := by exact_mod_cast hq'Q
    nlinarith
  calc (1 : ℝ) / (Q : ℝ) ^ 2 ≤ 1 / ((q : ℝ) * q') :=
        one_div_le_one_div_of_le (mul_pos hqpos hq'pos) hQ
    _ ≤ _ := by
        rw [div_le_div_iff_of_pos_right (mul_pos hqpos hq'pos)]
        exact h1

theorem TT_energy (M N : ℕ) (c : ℕ → ℂ) :
    ∫ t in (0:ℝ)..1, ‖TT M N c t‖ ^ 2 ≤
      (Real.pi * N) ^ 2 * ∑ k ∈ Finset.Ico M (M + N), ‖c k‖ ^ 2 := by
  have hp := parseval (Finset.Ico M (M + N))
    (fun k => c k * (2 * Real.pi * Complex.I * (((k : ℝ) - c0 M N : ℝ) : ℂ)))
  have hT : ∫ t in (0:ℝ)..1, ‖TT M N c t‖ ^ 2 = ∑ k ∈ Finset.Ico M (M + N),
      ‖c k * (2 * Real.pi * Complex.I * (((k : ℝ) - c0 M N : ℝ) : ℂ))‖ ^ 2 := hp
  rw [hT, Finset.mul_sum]
  refine Finset.sum_le_sum fun k hk => ?_
  rw [Finset.mem_Ico] at hk
  have hk1 : (M : ℝ) ≤ k := by exact_mod_cast hk.1
  have hk2 : (k : ℝ) + 1 ≤ M + N := by exact_mod_cast hk.2
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hu : |(k : ℝ) - c0 M N| ≤ (N : ℝ) / 2 := by
    unfold c0
    rw [abs_le]
    constructor <;> linarith
  have hn : ‖c k * (2 * Real.pi * Complex.I * (((k : ℝ) - c0 M N : ℝ) : ℂ))‖ =
      ‖c k‖ * (2 * Real.pi * |(k : ℝ) - c0 M N|) := by
    rw [norm_mul, norm_mul, norm_mul, norm_mul, Complex.norm_real ((k : ℝ) - c0 M N), Complex.norm_I]
    simp [abs_of_pos Real.pi_pos]
  rw [hn]
  have h2 : 2 * Real.pi * |(k : ℝ) - c0 M N| ≤ Real.pi * N := by
    have := Real.pi_pos
    nlinarith
  have h3 : (2 * Real.pi * |(k : ℝ) - c0 M N|) ^ 2 ≤ (Real.pi * N) ^ 2 :=
    pow_le_pow_left₀ (by positivity) h2 2
  calc (‖c k‖ * (2 * Real.pi * |(k : ℝ) - c0 M N|)) ^ 2
      = ‖c k‖ ^ 2 * (2 * Real.pi * |(k : ℝ) - c0 M N|) ^ 2 := by ring
    _ ≤ ‖c k‖ ^ 2 * (Real.pi * N) ^ 2 := mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = _ := by ring

theorem P_energy (M N : ℕ) (c : ℕ → ℂ) (hN : 0 < N) :
    ∫ t in (0:ℝ)..1, ‖SS M N c t‖ * ‖TT M N c t‖ ≤
      Real.pi * N * ∑ k ∈ Finset.Ico M (M + N), ‖c k‖ ^ 2 := by
  set l : ℝ := Real.pi * N with hl
  have hlpos : 0 < l := by
    have : (0 : ℝ) < N := by exact_mod_cast hN
    positivity
  have hpar : ∫ t in (0:ℝ)..1, ‖SS M N c t‖ ^ 2 = ∑ k ∈ Finset.Ico M (M + N), ‖c k‖ ^ 2 :=
    parseval _ c
  have hS : Continuous fun t => ‖SS M N c t‖ ^ 2 := ((SS_cont M N c).norm).pow 2
  have hT : Continuous fun t => ‖TT M N c t‖ ^ 2 := ((TT_cont M N c).norm).pow 2
  have hP : Continuous fun t => ‖SS M N c t‖ * ‖TT M N c t‖ :=
    (SS_cont M N c).norm.mul (TT_cont M N c).norm
  have hpt : ∀ t, ‖SS M N c t‖ * ‖TT M N c t‖ ≤
      (l / 2) * ‖SS M N c t‖ ^ 2 + (1 / (2 * l)) * ‖TT M N c t‖ ^ 2 := by
    intro t
    rw [← sub_nonneg]
    have : (l / 2) * ‖SS M N c t‖ ^ 2 + (1 / (2 * l)) * ‖TT M N c t‖ ^ 2 -
        ‖SS M N c t‖ * ‖TT M N c t‖ = (l * ‖SS M N c t‖ - ‖TT M N c t‖) ^ 2 / (2 * l) := by
      field_simp
      ring
    rw [this]
    positivity
  have hE := TT_energy M N c
  calc ∫ t in (0:ℝ)..1, ‖SS M N c t‖ * ‖TT M N c t‖
      ≤ ∫ t in (0:ℝ)..1, ((l / 2) * ‖SS M N c t‖ ^ 2 + (1 / (2 * l)) * ‖TT M N c t‖ ^ 2) :=
        intervalIntegral.integral_mono_on zero_le_one (hP.intervalIntegrable 0 1)
          (((continuous_const.mul hS).add (continuous_const.mul hT)).intervalIntegrable 0 1)
          (fun t _ => hpt t)
    _ = (l / 2) * (∫ t in (0:ℝ)..1, ‖SS M N c t‖ ^ 2) +
          (1 / (2 * l)) * ∫ t in (0:ℝ)..1, ‖TT M N c t‖ ^ 2 := by
        have i1 : IntervalIntegrable (fun t : ℝ => (l / 2) * ‖SS M N c t‖ ^ 2)
            MeasureTheory.volume 0 1 := (continuous_const.mul hS).intervalIntegrable 0 1
        have i2 : IntervalIntegrable (fun t : ℝ => (1 / (2 * l)) * ‖TT M N c t‖ ^ 2)
            MeasureTheory.volume 0 1 := (continuous_const.mul hT).intervalIntegrable 0 1
        rw [intervalIntegral.integral_add i1 i2,
          intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
    _ ≤ (l / 2) * (∑ k ∈ Finset.Ico M (M + N), ‖c k‖ ^ 2) +
          (1 / (2 * l)) * (l ^ 2 * ∑ k ∈ Finset.Ico M (M + N), ‖c k‖ ^ 2) := by
        rw [hpar]
        gcongr
    _ = l * ∑ k ∈ Finset.Ico M (M + N), ‖c k‖ ^ 2 := by
        field_simp
        ring

theorem main (M N Q : ℕ) (c : ℕ → ℂ) :
    (∑ q ∈ Finset.Icc 1 Q, ∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
      ‖SS M N c ((a : ℝ) / q)‖ ^ 2) ≤
      (Real.pi * (N : ℝ) + (Q : ℝ) ^ 2) * ∑ k ∈ Finset.Ico M (M + N), ‖c k‖ ^ 2 := by
  set Ec := ∑ k ∈ Finset.Ico M (M + N), ‖c k‖ ^ 2 with hEc
  have hEc0 : 0 ≤ Ec := Finset.sum_nonneg fun _ _ => by positivity
  rcases Nat.eq_zero_or_pos Q with hQ | hQ
  · subst hQ
    simp only [Finset.Icc_eq_empty_of_lt Nat.zero_lt_one, Finset.sum_empty]
    positivity
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    have hE0 : Ec = 0 := by simp [hEc]
    rw [hE0]
    simp [SS]
  have hQr : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hQ2 : (1 : ℝ) ≤ (Q : ℝ) ^ 2 := by nlinarith
  set δ : ℝ := 1 / (Q : ℝ) ^ 2 with hδdef
  have hδ : 0 < δ := by positivity
  have hQδ : (Q : ℝ) ^ 2 * δ = 1 := by
    rw [hδdef]; field_simp
  set f : ℝ → ℝ := fun t => ‖SS M N c t‖ ^ 2 with hf
  set f' : ℝ → ℝ := fun t => 2 * ((TT M N c t * (starRingEnd ℂ) (SS M N c t)).re) with hf'
  set P : ℝ → ℝ := fun t => ‖SS M N c t‖ * ‖TT M N c t‖ with hP
  have hfd : ∀ x, HasDerivAt f (f' x) x := fun x => f_deriv M N c x
  have hf'c : Continuous f' :=
    continuous_const.mul (Complex.continuous_re.comp
      ((TT_cont M N c).mul (Complex.continuous_conj.comp (SS_cont M N c))))
  have hfc : Continuous f := ((SS_cont M N c).norm).pow 2
  have hPc : Continuous P := (SS_cont M N c).norm.mul (TT_cont M N c).norm
  have hf0 : ∀ t, 0 ≤ f t := fun t => by positivity
  have hP0 : ∀ t, 0 ≤ P t := fun t => by positivity
  have hfper : Function.Periodic f 1 := fun t => by simp only [hf, SS_per]
  have hPper : Function.Periodic P 1 := fun t => by simp only [hP, SS_per, TT_per]
  have hpt : ∀ x0 : ℝ, f x0 ≤ (Q : ℝ) ^ 2 * (∫ y in (x0 - δ / 2)..(x0 + δ / 2), f y) +
      ∫ y in (x0 - δ / 2)..(x0 + δ / 2), P y := by
    intro x0
    have h1 := local_bound f f' hfd hf'c x0 δ hδ
    have hle : ∫ y in (x0 - δ / 2)..(x0 + δ / 2), |f' y| ≤
        2 * ∫ y in (x0 - δ / 2)..(x0 + δ / 2), P y := by
      rw [← intervalIntegral.integral_const_mul]
      exact intervalIntegral.integral_mono_on (by linarith) (hf'c.abs.intervalIntegrable _ _)
        ((continuous_const.mul hPc).intervalIntegrable _ _)
        (fun y _ => f_deriv_bound M N c y)
    have h2 : δ * f x0 ≤ (∫ y in (x0 - δ / 2)..(x0 + δ / 2), f y) +
        δ * ∫ y in (x0 - δ / 2)..(x0 + δ / 2), P y := by nlinarith
    calc f x0 = (Q : ℝ) ^ 2 * (δ * f x0) := by rw [← mul_assoc, hQδ, one_mul]
      _ ≤ (Q : ℝ) ^ 2 * ((∫ y in (x0 - δ / 2)..(x0 + δ / 2), f y) +
            δ * ∫ y in (x0 - δ / 2)..(x0 + δ / 2), P y) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = _ := by
          have : (Q : ℝ) ^ 2 * δ * (∫ y in (x0 - δ / 2)..(x0 + δ / 2), P y) =
              ∫ y in (x0 - δ / 2)..(x0 + δ / 2), P y := by rw [hQδ, one_mul]
          nlinarith [this]
  set s : Finset (Σ _ : ℕ, ℕ) :=
    (Finset.Icc 1 Q).sigma (fun q => (Finset.range q).filter (fun a => Nat.Coprime a q)) with hs
  set x : (Σ _ : ℕ, ℕ) → ℝ := fun i => (i.2 : ℝ) / (i.1 : ℝ) with hx
  have hL : ∑ i ∈ s, f (x i) = ∑ q ∈ Finset.Icc 1 Q, ∑ a ∈ (Finset.range q).filter
      (fun a => Nat.Coprime a q), ‖SS M N c ((a : ℝ) / q)‖ ^ 2 := by
    rw [hs, Finset.sum_sigma]
  have hmem : ∀ i ∈ s, 1 ≤ i.1 ∧ i.1 ≤ Q ∧ i.2 < i.1 ∧ Nat.Coprime i.2 i.1 := by
    rintro ⟨q, a⟩ hi
    simp only [hs, Finset.mem_sigma, Finset.mem_Icc, Finset.mem_filter, Finset.mem_range] at hi
    exact ⟨hi.1.1, hi.1.2, hi.2.1, hi.2.2⟩
  have hx0 : ∀ i ∈ s, 0 ≤ x i := fun i _ => by positivity
  have hx1 : ∀ i ∈ s, x i ≤ 1 - δ := by
    intro i hi
    obtain ⟨h1, h2, h3, h4⟩ := hmem i hi
    have hqpos : (0 : ℝ) < i.1 := by exact_mod_cast h1
    have ha : (i.2 : ℝ) + 1 ≤ i.1 := by exact_mod_cast h3
    have hqQ : (i.1 : ℝ) ≤ Q := by exact_mod_cast h2
    have hdq : δ * i.1 ≤ 1 := by
      rw [hδdef, one_div, inv_mul_le_iff₀ (by positivity)]
      nlinarith
    simp only [hx]
    rw [div_le_iff₀ hqpos]
    nlinarith
  have hsp : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → δ ≤ |x i - x j| := by
    rintro ⟨q, a⟩ hi ⟨q', a'⟩ hj hij
    obtain ⟨h1, h2, h3, h4⟩ := hmem _ hi
    obtain ⟨h1', h2', h3', h4'⟩ := hmem _ hj
    simp only at h1 h2 h3 h4 h1' h2' h3' h4'
    have hne : q ≠ q' ∨ a ≠ a' := by
      by_contra hcon
      push_neg at hcon
      obtain ⟨rfl, rfl⟩ := hcon
      exact hij rfl
    exact spacing Q q a q' a' h1 h1' h2 h2' h4 h4' hne
  have hW1 := sum_windows s x δ hδ f hfc hf0 hfper hx0 hx1 hsp
  have hW2 := sum_windows s x δ hδ P hPc hP0 hPper hx0 hx1 hsp
  have hpar : ∫ t in (0:ℝ)..1, f t = Ec := parseval _ c
  have hPE : ∫ t in (0:ℝ)..1, P t ≤ Real.pi * N * Ec := P_energy M N c hN
  rw [← hL]
  calc ∑ i ∈ s, f (x i)
      ≤ ∑ i ∈ s, ((Q : ℝ) ^ 2 * (∫ y in (x i - δ / 2)..(x i + δ / 2), f y) +
          ∫ y in (x i - δ / 2)..(x i + δ / 2), P y) :=
        Finset.sum_le_sum fun i _ => hpt (x i)
    _ = (Q : ℝ) ^ 2 * (∑ i ∈ s, ∫ y in (x i - δ / 2)..(x i + δ / 2), f y) +
          ∑ i ∈ s, ∫ y in (x i - δ / 2)..(x i + δ / 2), P y := by
        rw [Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ (Q : ℝ) ^ 2 * (∫ t in (0:ℝ)..1, f t) + ∫ t in (0:ℝ)..1, P t :=
        by exact add_le_add (mul_le_mul_of_nonneg_left hW1 (sq_nonneg (Q : ℝ))) hW2
    _ ≤ (Q : ℝ) ^ 2 * Ec + Real.pi * N * Ec := by
        have h3 := mul_le_mul_of_nonneg_left hpar.le (sq_nonneg (Q : ℝ))
        linarith
    _ = _ := by ring

end GbLS

theorem Conjectures.Goldbach.AnalyticLargeSieve :
    let E (x : ℝ) := Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I); ∀ (M N Q : ℕ) (c : ℕ → ℂ), let S (t : ℝ) := ∑ k ∈ Finset.Ico M (M + N), c k * E ((k : ℝ) * t); (∑ q ∈ Finset.Icc 1 Q, ∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q), ‖S ((a : ℝ) / q)‖ ^ 2) ≤ (Real.pi * (N : ℝ) + (Q : ℝ) ^ 2) * ∑ k ∈ Finset.Ico M (M + N), ‖c k‖ ^ 2 := by
  intro E M N Q c S
  exact GbLS.main M N Q c
