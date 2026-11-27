import Mathlib

private noncomputable def phase (x : ℝ) : ℂ := Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I)

section PartFold
open Finset
private def units (q : ℕ) := (range q).filter (fun a => Nat.Coprime a q)

private theorem complete_phase_sum (m a : ℕ) (hm : 0 < m) :
    ∑ b ∈ range m, phase ((a : ℝ) * (b : ℝ) / m) =
      if m ∣ a then (m : ℂ) else 0 := by
  let z : ℂ := Complex.exp (2 * Real.pi * Complex.I * a / m)
  have hz : z = 1 ↔ m ∣ a :=
    Complex.exp_two_pi_mul_I_mul_div_eq_one_iff hm.ne'
  have hm' : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  have hpow (b : ℕ) : phase ((a : ℝ) * (b : ℝ) / m) = z ^ b := by
    rw [← Complex.exp_nat_mul]
    unfold phase
    push_cast
    congr 1
    field_simp
  simp_rw [hpow]
  by_cases h : m ∣ a
  · simp [h, hz.mpr h]
  · simp only [h, ite_false]
    have hzm : z ^ m = 1 := by
      rw [← Complex.exp_nat_mul]
      have harg : (m : ℂ) * (2 * Real.pi * Complex.I * a / m) =
          a * (2 * Real.pi * Complex.I) := by
        field_simp
      rw [harg]
      exact Complex.exp_nat_mul_two_pi_mul_I a
    have hsum := geom_sum_mul z m
    rw [hzm, sub_self] at hsum
    exact (mul_eq_zero.mp hsum).resolve_right
      (sub_ne_zero.mpr (fun hz1 => h (hz.mp hz1)))

private theorem coprime_indicator (q b : ℕ) (hq : 0 < q) :
    (∑ d ∈ q.divisors, if d ∣ b then (ArithmeticFunction.moebius d : ℂ) else 0) =
      if Nat.Coprime b q then 1 else 0 := by
  have hg : Nat.gcd b q ≠ 0 := (Nat.gcd_pos_of_pos_right b hq).ne'
  have hs : q.divisors.filter (fun d => d ∣ b) = (Nat.gcd b q).divisors := by
    ext d
    simp [Nat.mem_divisors, hq.ne', hg, Nat.dvd_gcd_iff, and_comm]
  rw [← sum_filter, hs]
  have h := DFunLike.congr_fun
    (ArithmeticFunction.coe_zeta_mul_coe_moebius (R := ℂ)) (Nat.gcd b q)
  simpa only [ArithmeticFunction.coe_zeta_mul_apply, ArithmeticFunction.one_apply,
    ArithmeticFunction.intCoe_apply, Nat.Coprime] using h

private theorem multiples_phase_sum (q a d : ℕ) (hq : 0 < q) (hd : d ∣ q) :
    ∑ b ∈ (range q).filter (fun b => d ∣ b), phase ((a : ℝ) * (b : ℝ) / q) =
      if q / d ∣ a then ((q / d : ℕ) : ℂ) else 0 := by
  obtain ⟨m, rfl⟩ := hd
  have hd : 0 < d := Nat.pos_of_mul_pos_right hq
  have hm : 0 < m := Nat.pos_of_mul_pos_left hq
  rw [Nat.mul_div_cancel_left _ hd, ← complete_phase_sum m a hm]
  symm
  apply sum_nbij' (d * ·) (· / d)
  · intro j hj
    exact mem_filter.mpr
      ⟨mem_range.mpr (Nat.mul_lt_mul_of_pos_left (mem_range.mp hj) hd),
        dvd_mul_right d j⟩
  · intro k hk
    apply mem_range.mpr
    exact (Nat.div_lt_iff_lt_mul hd).mpr
      (by simpa [Nat.mul_comm] using mem_range.mp (mem_filter.mp hk).1)
  · intro j _
    exact Nat.mul_div_cancel_left j hd
  · intro k hk
    exact Nat.mul_div_cancel' (mem_filter.mp hk).2
  · intro j _
    unfold phase
    push_cast
    congr 1
    have hd' : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
    have hm' : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
    field_simp

private theorem ramanujan_sum (q a : ℕ) (hq : 0 < q) :
    ∑ b ∈ units q, phase ((a : ℝ) * (b : ℝ) / q) =
      ∑ d ∈ q.divisors, ((ArithmeticFunction.moebius d : ℤ) : ℂ) *
        (if q / d ∣ a then ((q / d : ℕ) : ℂ) else 0) := by
  calc
    _ = ∑ b ∈ range q,
        (∑ d ∈ q.divisors,
          if d ∣ b then (ArithmeticFunction.moebius d : ℂ) else 0) *
          phase ((a : ℝ) * (b : ℝ) / q) := by
      simp only [coprime_indicator q _ hq, units, sum_filter]
      apply sum_congr rfl
      intro b _
      by_cases h : Nat.Coprime b q <;> simp [h]
    _ = ∑ d ∈ q.divisors, ∑ b ∈ range q,
        (if d ∣ b then (ArithmeticFunction.moebius d : ℂ) else 0) *
          phase ((a : ℝ) * (b : ℝ) / q) := by
      simp only [sum_mul]
      rw [sum_comm]
    _ = _ := by
      apply sum_congr rfl
      intro d hd
      rw [← multiples_phase_sum q a d hq (Nat.dvd_of_mem_divisors hd),
        mul_sum, sum_filter]
      apply sum_congr rfl
      intro b _
      by_cases h : d ∣ b <;> simp [h]


end PartFold

private theorem ram_coprime (q a : ℕ) (hq : 0 < q) (ha : Nat.Coprime a q) :
    ∑ b ∈ (Finset.range q).filter (fun b => Nat.Coprime b q), phase ((a : ℝ) * (b : ℝ) / q) =
      ((ArithmeticFunction.moebius q : ℤ) : ℂ) := by
  have h := ramanujan_sum q a hq
  unfold units at h
  rw [h]
  rw [Finset.sum_eq_single q]
  · have : q / q ∣ a := by rw [Nat.div_self hq]; exact one_dvd _
    simp [this, Nat.div_self hq]
  · intro d hd hne
    have hdq : d ∣ q := Nat.dvd_of_mem_divisors hd
    have : ¬ (q / d ∣ a) := by
      intro hdiv
      have h1 : q / d ∣ Nat.gcd a q := Nat.dvd_gcd hdiv (Nat.div_dvd_of_dvd hdq)
      rw [ha] at h1
      have : q / d = 1 := Nat.dvd_one.mp h1
      have : d = q := by
        have := Nat.div_mul_cancel hdq
        rw [‹q / d = 1›] at this
        omega
      exact hne this
    simp [this]
  · intro h; exact absurd (Nat.mem_divisors.mpr ⟨dvd_refl q, hq.ne'⟩) h

private theorem phase_norm' (x : ℝ) : ‖phase x‖ = 1 := Complex.norm_exp_ofReal_mul_I _

private theorem phase_add' (x y : ℝ) : phase (x + y) = phase x * phase y := by
  simp only [phase, mul_add, Complex.ofReal_add, add_mul, Complex.exp_add]

private noncomputable def pw (k : ℕ) : ℝ := if Nat.Prime k then Real.log (k : ℝ) else 0

private noncomputable def SS (n : ℕ) (t : ℝ) : ℂ :=
  ∑ k ∈ Finset.range (n+1), (pw k : ℂ) * phase ((k:ℝ) * t)

private theorem pw_nonneg (k : ℕ) : 0 ≤ pw k := by
  unfold pw
  split_ifs with h
  · exact Real.log_nonneg (by exact_mod_cast h.one_lt.le)
  · exact le_refl _

private theorem sum_pw (n : ℕ) : ∑ k ∈ Finset.range (n+1), pw k = Chebyshev.theta (n:ℝ) := by
  rw [Chebyshev.theta_eq_sum_Icc]
  simp only [Nat.floor_natCast]
  rw [Finset.sum_filter]
  rw [← Nat.range_succ_eq_Icc_zero]
  rfl

private theorem SS_continuous (n : ℕ) : Continuous (SS n) := by
  unfold SS phase
  fun_prop

private theorem re_SS_ge (n : ℕ) (h : ℝ) (h0 : 0 ≤ h) (h1 : h ≤ 1 / (6 * (n:ℝ))) (hn : 0 < n) :
    Chebyshev.theta (n:ℝ) / 2 ≤ ‖SS n h‖ := by
  have hre : (SS n h).re = ∑ k ∈ Finset.range (n+1), pw k * Real.cos (2 * Real.pi * ((k:ℝ) * h)) := by
    unfold SS phase
    rw [Complex.re_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]
  have hle : Chebyshev.theta (n:ℝ) / 2 ≤ (SS n h).re := by
    rw [hre, ← sum_pw, Finset.sum_div]
    apply Finset.sum_le_sum
    intro k hk
    have hk' : (k:ℝ) ≤ n := by exact_mod_cast Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have hnr : (0:ℝ) < n := by exact_mod_cast hn
    have hkh : (k:ℝ) * h ≤ 1/6 := by
      calc (k:ℝ) * h ≤ n * (1 / (6 * n)) := by
            apply mul_le_mul hk' h1 h0 hnr.le
        _ = 1/6 := by field_simp
    have hc : (1:ℝ)/2 ≤ Real.cos (2 * Real.pi * ((k:ℝ) * h)) := by
      rw [← Real.cos_pi_div_three]
      apply Real.cos_le_cos_of_nonneg_of_le_pi
      · positivity
      · linarith [Real.pi_pos]
      · nlinarith [Real.pi_pos, mul_nonneg (Nat.cast_nonneg k : (0:ℝ) ≤ k) h0]
    have := pw_nonneg k
    nlinarith
  exact hle.trans ((Complex.re_le_norm _))

private theorem amp_sum_eq (n q : ℕ) (h : ℝ) :
    ∑ a ∈ units q, SS n ((a:ℝ) / q + h) =
      ∑ k ∈ Finset.range (n+1), (pw k : ℂ) * phase ((k:ℝ) * h) *
        ∑ a ∈ units q, phase ((k:ℝ) * (a:ℝ) / q) := by
  unfold SS
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  have : (k:ℝ) * ((a:ℝ) / q + h) = (k:ℝ) * (a:ℝ) / q + (k:ℝ) * h := by ring
  rw [this, phase_add']
  ring

private theorem units_card_le (q : ℕ) : (units q).card ≤ q := by
  unfold units
  exact (Finset.card_filter_le _ _).trans (by simp)

private theorem amp (n q : ℕ) (hn : 0 < n) (hq : Squarefree q) (hq1 : 1 < q)
    (h : ℝ) (h0 : 0 ≤ h) (h1 : h ≤ 1 / (6 * (n:ℝ)))
    (hθ : (n:ℝ) / 2 ≤ Chebyshev.theta (n:ℝ)) (hL : 2 * (q:ℝ) * Real.log q ≤ n / 8) :
    (n:ℝ) / 8 ≤ ‖∑ a ∈ units q, SS n ((a:ℝ) / q + h)‖ := by
  have hq0 : 0 < q := by omega
  set m : ℂ := ((ArithmeticFunction.moebius q : ℤ) : ℂ) with hmdef
  have hm : ‖m‖ = 1 := by
    have hne : ArithmeticFunction.moebius q ≠ 0 :=
      (ArithmeticFunction.moebius_ne_zero_iff_squarefree).mpr hq
    rcases ArithmeticFunction.moebius_eq_or q with h0 | h0 | h0
    · exact absurd h0 hne
    · simp [hmdef, h0]
    · simp [hmdef, h0]
  set c : ℕ → ℂ := fun k => ∑ a ∈ units q, phase ((k:ℝ) * (a:ℝ) / q) with hc
  have hcnorm : ∀ k, ‖c k‖ ≤ q := by
    intro k
    refine (norm_sum_le _ _).trans ?_
    simp only [phase_norm', Finset.sum_const, nsmul_eq_mul, mul_one]
    exact_mod_cast units_card_le q
  have hcm : ∀ k, Nat.Coprime k q → c k = m := fun k hk => ram_coprime q k hq0 hk
  have hsplit : ∑ a ∈ units q, SS n ((a:ℝ) / q + h) =
      m * SS n h + ∑ k ∈ Finset.range (n+1), (pw k : ℂ) * phase ((k:ℝ) * h) * (c k - m) := by
    rw [amp_sum_eq]
    unfold SS
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    simp only [hc]
    ring
  set R := ∑ k ∈ Finset.range (n+1), (pw k : ℂ) * phase ((k:ℝ) * h) * (c k - m) with hR
  have hRle : ‖R‖ ≤ 2 * (q:ℝ) * Real.log q := by
    have hterm : ∀ k ∈ Finset.range (n+1), ‖(pw k : ℂ) * phase ((k:ℝ) * h) * (c k - m)‖ ≤
        if k ∈ q.primeFactors then Real.log k * (q + 1) else 0 := by
      intro k _
      by_cases hk : k ∈ q.primeFactors
      · simp only [hk, ↓reduceIte]
        have hkp : k.Prime := Nat.prime_of_mem_primeFactors hk
        rw [norm_mul, norm_mul, phase_norm', mul_one]
        have hk1 : (1:ℝ) ≤ k := by exact_mod_cast hkp.one_lt.le
        have hpw : ‖(pw k : ℂ)‖ = Real.log k := by
          rw [show pw k = Real.log k by simp [pw, hkp], Complex.norm_real,
            Real.norm_of_nonneg (Real.log_nonneg hk1)]
        rw [hpw]
        apply mul_le_mul_of_nonneg_left _ (Real.log_nonneg hk1)
        calc ‖c k - m‖ ≤ ‖c k‖ + ‖m‖ := norm_sub_le _ _
          _ ≤ q + 1 := by linarith [hcnorm k]
      · simp only [hk, ↓reduceIte]
        by_cases hkp : k.Prime
        · have hcop : Nat.Coprime k q := by
            rw [Nat.Prime.coprime_iff_not_dvd hkp]
            intro hd
            exact hk (Nat.mem_primeFactors.mpr ⟨hkp, hd, hq0.ne'⟩)
          rw [hcm k hcop]
          simp
        · have : pw k = 0 := by simp [pw, hkp]
          simp [this]
    have h1 := (norm_sum_le _ _).trans (Finset.sum_le_sum hterm)
    refine h1.trans ?_
    rw [Finset.sum_ite_mem]
    have hsub : (Finset.range (n+1) ∩ q.primeFactors) ⊆ q.primeFactors := Finset.inter_subset_right
    refine (Finset.sum_le_sum_of_subset_of_nonneg hsub ?_).trans ?_
    · intro k hk _
      have hkp : k.Prime := Nat.prime_of_mem_primeFactors hk
      have hk1 : (1:ℝ) ≤ k := by exact_mod_cast hkp.one_lt.le
      have := Real.log_nonneg hk1
      positivity
    · rw [← Finset.sum_mul]
      have hprod : ∑ k ∈ q.primeFactors, Real.log k = Real.log (∏ k ∈ q.primeFactors, (k:ℝ)) := by
        rw [Real.log_prod]
        intro k hk
        exact_mod_cast (Nat.prime_of_mem_primeFactors hk).pos.ne'
      have hle : (∏ k ∈ q.primeFactors, (k:ℝ)) ≤ q := by
        have := Nat.le_of_dvd hq0 (Nat.prod_primeFactors_dvd q)
        have h2 : ((∏ k ∈ q.primeFactors, k : ℕ) : ℝ) ≤ q := by exact_mod_cast this
        rwa [Nat.cast_prod] at h2
      have hpos : 0 < ∏ k ∈ q.primeFactors, (k:ℝ) :=
        Finset.prod_pos (fun k hk => by exact_mod_cast (Nat.prime_of_mem_primeFactors hk).pos)
      have hlog : Real.log (∏ k ∈ q.primeFactors, (k:ℝ)) ≤ Real.log q := Real.log_le_log hpos hle
      rw [hprod]
      have hq1' : (1:ℝ) ≤ q := by exact_mod_cast hq0
      have hlq : 0 ≤ Real.log q := Real.log_nonneg hq1'
      nlinarith
  have hS := re_SS_ge n h h0 h1 hn
  have : ‖m * SS n h‖ = ‖SS n h‖ := by rw [norm_mul, hm, one_mul]
  rw [hsplit]
  have h3 : ‖m * SS n h‖ - ‖R‖ ≤ ‖m * SS n h + R‖ := by
    have := norm_sub_norm_le (m * SS n h) (-R)
    simpa [sub_eq_add_neg] using this
  linarith

private theorem energy_pt (n q : ℕ) (hn : 0 < n) (hq : Squarefree q) (hq1 : 1 < q)
    (h : ℝ) (h0 : 0 ≤ h) (h1 : h ≤ 1 / (6 * (n:ℝ)))
    (hθ : (n:ℝ) / 2 ≤ Chebyshev.theta (n:ℝ)) (hL : 2 * (q:ℝ) * Real.log q ≤ n / 8) :
    (n:ℝ) ^ 2 / (64 * (q:ℝ)) ≤ ∑ a ∈ units q, ‖SS n ((a:ℝ) / q + h)‖ ^ 2 := by
  have hamp := amp n q hn hq hq1 h h0 h1 hθ hL
  have hq0 : (0:ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hn0 : (0:ℝ) ≤ n := Nat.cast_nonneg n
  have hsum := hamp.trans (norm_sum_le (units q) (fun a => SS n ((a:ℝ) / q + h)))
  have hsq := pow_le_pow_left₀ (by positivity : 0 ≤ (n:ℝ) / 8) hsum 2
  have hcs := sq_sum_le_card_mul_sum_sq (s := units q) (f := fun a => ‖SS n ((a:ℝ) / q + h)‖)
  have hc : ((units q).card : ℝ) ≤ q := by exact_mod_cast units_card_le q
  have henergy : 0 ≤ ∑ a ∈ units q, ‖SS n ((a:ℝ) / q + h)‖ ^ 2 :=
    Finset.sum_nonneg fun a _ => sq_nonneg _
  apply (div_le_iff₀ (by positivity : 0 < 64 * (q : ℝ))).2
  nlinarith only [hsq, hcs, mul_le_mul_of_nonneg_right hc henergy]

private theorem energy_window (n q : ℕ) (hn : 0 < n) (hq : Squarefree q) (hq1 : 1 < q)
    (hθ : (n:ℝ) / 2 ≤ Chebyshev.theta (n:ℝ)) (hL : 2 * (q:ℝ) * Real.log q ≤ n / 8) :
    (n:ℝ) / (384 * (q:ℝ)) ≤
      ∫ h in (0:ℝ)..1 / (6 * (n:ℝ)), ∑ a ∈ units q, ‖SS n ((a:ℝ) / q + h)‖ ^ 2 := by
  have hnr : (0:ℝ) < n := by exact_mod_cast hn
  have hq0 : (0:ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hcont : Continuous (fun h => ∑ a ∈ units q, ‖SS n ((a:ℝ) / q + h)‖ ^ 2) :=
    continuous_finsetSum _ fun a _ => ((SS_continuous n).comp (continuous_const.add continuous_id)).norm.pow 2
  calc (n:ℝ) / (384 * (q:ℝ)) = ∫ _ in (0 : ℝ)..1 / (6 * (n:ℝ)), (n:ℝ) ^ 2 / (64 * (q:ℝ)) := by
        rw [intervalIntegral.integral_const, sub_zero, smul_eq_mul]
        field_simp
        ring
    _ ≤ _ := by
        apply intervalIntegral.integral_mono_on (by positivity) intervalIntegrable_const
          (hcont.intervalIntegrable ..)
        intro h hh
        exact energy_pt n q hn hq hq1 h hh.1 hh.2 hθ hL

private theorem window_integral (n : ℕ) (W : Set ℝ) (hW : MeasurableSet W) (hn : 0 < n)
    (Sq : Finset ℕ)
    (hSq : ∀ q ∈ Sq, Squarefree q ∧ 1 < q ∧ 2 * (q:ℝ) * Real.log q ≤ n / 8)
    (hθ : (n:ℝ) / 2 ≤ Chebyshev.theta (n:ℝ))
    (hsub : ∀ q ∈ Sq, ∀ a ∈ units q,
      Set.Icc ((a:ℝ) / q) ((a:ℝ) / q + 1 / (6 * (n:ℝ))) ⊆ Wᶜ ∩ Set.Ioc 0 1)
    (hdisj : ∀ q ∈ Sq, ∀ a ∈ units q, ∀ q' ∈ Sq, ∀ a' ∈ units q', (q ≠ q' ∨ a ≠ a') →
      Disjoint (Set.Icc ((a:ℝ) / q) ((a:ℝ) / q + 1 / (6 * (n:ℝ))))
        (Set.Icc ((a':ℝ) / q') ((a':ℝ) / q' + 1 / (6 * (n:ℝ))))) :
    ∑ q ∈ Sq, (n:ℝ) / (384 * (q:ℝ)) ≤
      ∫ t in (0:ℝ)..1, Wᶜ.indicator (fun u => ‖SS n u‖ ^ 2) t := by
  have hnr : (0:ℝ) < n := by exact_mod_cast hn
  set δ : ℝ := 1 / (6 * (n:ℝ)) with hδ
  have hδ0 : 0 < δ := by positivity
  set F : ℝ → ℝ := Wᶜ.indicator (fun u => ‖SS n u‖ ^ 2) with hF
  have hG : Continuous (fun u => ‖SS n u‖ ^ 2) := ((SS_continuous n).norm).pow 2
  have hFnn : ∀ x, 0 ≤ F x := by
    intro x
    simp only [hF, Set.indicator]
    split_ifs
    · positivity
    · exact le_refl _
  have hFint : MeasureTheory.IntegrableOn F (Set.Ioc 0 1) := by
    have h1 : MeasureTheory.IntegrableOn (fun u => ‖SS n u‖ ^ 2) (Set.Ioc 0 1) :=
      hG.integrableOn_Ioc
    refine MeasureTheory.Integrable.mono' h1 ?_ ?_
    · exact (hG.measurable.indicator hW.compl).aestronglyMeasurable
    · refine Filter.Eventually.of_forall (fun x => ?_)
      rw [Real.norm_of_nonneg (hFnn x)]
      simp only [hF, Set.indicator]
      split_ifs
      · exact le_refl _
      · positivity
  let P : Finset (Σ _ : ℕ, ℕ) := Sq.sigma (fun q => units q)
  let I : (Σ _ : ℕ, ℕ) → Set ℝ := fun p => Set.Icc ((p.2:ℝ) / p.1) ((p.2:ℝ) / p.1 + δ)
  have hIint : ∀ p ∈ P, MeasureTheory.IntegrableOn F (I p) := by
    intro p hp
    have hp' := Finset.mem_sigma.mp hp
    exact hFint.mono_set ((hsub p.1 hp'.1 p.2 hp'.2).trans Set.inter_subset_right)
  have hunion : (⋃ p ∈ P, I p) ⊆ Set.Ioc 0 1 := by
    intro x hx
    simp only [Set.mem_iUnion] at hx
    obtain ⟨p, hp, hxp⟩ := hx
    have hp' := Finset.mem_sigma.mp hp
    exact (hsub p.1 hp'.1 p.2 hp'.2 hxp).2
  have h1 : ∫ x in (⋃ p ∈ P, I p), F x = ∑ p ∈ P, ∫ x in I p, F x := by
    apply MeasureTheory.integral_biUnion_finset P (fun p _ => measurableSet_Icc)
    · intro p hp p' hp' hne
      have hp1 := Finset.mem_sigma.mp hp
      have hp2 := Finset.mem_sigma.mp hp'
      refine hdisj p.1 hp1.1 p.2 hp1.2 p'.1 hp2.1 p'.2 hp2.2 ?_
      by_contra hcon
      push_neg at hcon
      apply hne
      exact Sigma.ext hcon.1 (heq_of_eq hcon.2)
    · exact hIint
  have h2 : ∫ x in (⋃ p ∈ P, I p), F x ≤ ∫ x in Set.Ioc (0:ℝ) 1, F x := by
    apply MeasureTheory.setIntegral_mono_set hFint
    · exact Filter.Eventually.of_forall hFnn
    · exact Filter.Eventually.of_forall hunion
  have h3 : ∀ p ∈ P, ∫ x in I p, F x = ∫ h in (0:ℝ)..δ, ‖SS n ((p.2:ℝ) / p.1 + h)‖ ^ 2 := by
    intro p hp
    have hp' := Finset.mem_sigma.mp hp
    have hcongr : ∫ x in I p, F x = ∫ x in I p, ‖SS n x‖ ^ 2 := by
      apply MeasureTheory.setIntegral_congr_fun measurableSet_Icc
      intro x hx
      have : x ∈ Wᶜ := (hsub p.1 hp'.1 p.2 hp'.2 hx).1
      simp only [hF, Set.indicator_of_mem this]
    rw [hcongr, MeasureTheory.integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by linarith [show (0:ℝ) ≤ (p.2:ℝ) / p.1 by positivity])]
    rw [intervalIntegral.integral_comp_add_left (fun x => ‖SS n x‖ ^ 2) ((p.2:ℝ) / p.1)]
    simp
  have h4 : ∑ p ∈ P, ∫ x in I p, F x =
      ∑ q ∈ Sq, ∫ h in (0:ℝ)..δ, ∑ a ∈ units q, ‖SS n ((a:ℝ) / q + h)‖ ^ 2 := by
    rw [Finset.sum_congr rfl h3, Finset.sum_sigma]
    apply Finset.sum_congr rfl
    intro q hq
    rw [intervalIntegral.integral_finsetSum]
    intro a _
    exact (hG.comp (continuous_const.add continuous_id)).intervalIntegrable _ _
  have h5 : ∑ q ∈ Sq, (n:ℝ) / (384 * (q:ℝ)) ≤
      ∑ q ∈ Sq, ∫ h in (0:ℝ)..δ, ∑ a ∈ units q, ‖SS n ((a:ℝ) / q + h)‖ ^ 2 := by
    apply Finset.sum_le_sum
    intro q hq
    obtain ⟨h1, h2, h3⟩ := hSq q hq
    exact energy_window n q hn h1 h2 hθ h3
  rw [intervalIntegral.integral_of_le zero_le_one]
  linarith

private theorem frac_gap (a q a' q' : ℕ) (hq : 0 < q) (hq' : 0 < q') (hne : a * q' ≠ a' * q) :
    1 / ((q:ℝ) * q') ≤ |(a:ℝ) / q - (a':ℝ) / q'| := by
  have hqr : (0:ℝ) < q := by exact_mod_cast hq
  have hqr' : (0:ℝ) < q' := by exact_mod_cast hq'
  have h1 : (a:ℝ) / q - (a':ℝ) / q' = ((a:ℤ) * q' - (a':ℤ) * q : ℤ) / ((q:ℝ) * q') := by
    push_cast
    field_simp
  have hz : (1:ℤ) ≤ |(a:ℤ) * q' - (a':ℤ) * q| := by
    have : (a:ℤ) * q' - (a':ℤ) * q ≠ 0 := by
      intro h
      apply hne
      have : (a:ℤ) * q' = (a':ℤ) * q := by linarith
      exact_mod_cast this
    exact Int.one_le_abs this
  have hz' : (1:ℝ) ≤ |(((a:ℤ) * q' - (a':ℤ) * q : ℤ) : ℝ)| := by exact_mod_cast hz
  rw [h1, abs_div, abs_of_pos (by positivity : (0:ℝ) < (q:ℝ) * q')]
  exact div_le_div_of_nonneg_right hz' (by positivity)

private theorem coprime_ne (a q a' q' : ℕ) (hq : 0 < q) (hq' : 0 < q')
    (ha : Nat.Coprime a q) (ha' : Nat.Coprime a' q') (hne : q ≠ q' ∨ a ≠ a') :
    a * q' ≠ a' * q := by
  intro h
  have h1 : q ∣ q' := by
    have : q ∣ a * q' := ⟨a', by rw [h]; ring⟩
    exact (Nat.Coprime.dvd_of_dvd_mul_left ha.symm this)
  have h2 : q' ∣ q := by
    have : q' ∣ a' * q := ⟨a, by rw [← h]; ring⟩
    exact (Nat.Coprime.dvd_of_dvd_mul_left ha'.symm this)
  have hqq : q = q' := Nat.dvd_antisymm h1 h2
  subst hqq
  rcases hne with hne | hne
  · exact hne rfl
  · apply hne
    exact Nat.eq_of_mul_eq_mul_right hq h

private theorem window_disjoint (n L : ℕ) (hn : 0 < n) (hL : (L:ℝ) * L * 16 ≤ n)
    (a q a' q' : ℕ) (hq : 0 < q) (hq' : 0 < q') (hqL : q ≤ L) (hqL' : q' ≤ L)
    (ha : Nat.Coprime a q) (ha' : Nat.Coprime a' q') (hne : q ≠ q' ∨ a ≠ a') :
    Disjoint (Set.Icc ((a:ℝ) / q) ((a:ℝ) / q + 1 / (6 * (n:ℝ))))
      (Set.Icc ((a':ℝ) / q') ((a':ℝ) / q' + 1 / (6 * (n:ℝ)))) := by
  rw [Set.disjoint_left]
  intro t ht ht'
  have hgap := frac_gap a q a' q' hq hq' (coprime_ne a q a' q' hq hq' ha ha' hne)
  have hnr : (0:ℝ) < n := by exact_mod_cast hn
  have hqL1 : (q:ℝ) ≤ L := by exact_mod_cast hqL
  have hqL2 : (q':ℝ) ≤ L := by exact_mod_cast hqL'
  have hqr : (0:ℝ) < q := by exact_mod_cast hq
  have hqr' : (0:ℝ) < q' := by exact_mod_cast hq'
  have habs : |(a:ℝ) / q - (a':ℝ) / q'| ≤ 1 / (6 * (n:ℝ)) := by
    rw [abs_le]
    obtain ⟨h1, h2⟩ := ht
    obtain ⟨h3, h4⟩ := ht'
    constructor <;> linarith
  have hprod : (q:ℝ) * q' ≤ L * L := mul_le_mul hqL1 hqL2 hqr'.le (by positivity)
  have h6 : 1 / (6 * (n:ℝ)) < 1 / ((q:ℝ) * q') := by
    apply one_div_lt_one_div_of_lt (by positivity)
    nlinarith
  linarith

private theorem window_avoid (n : ℕ) (hn : 0 < n) (D L : ℕ) (Hv : ℝ)
    (hL : (L:ℝ) * L * 16 ≤ n) (hH : (L:ℝ) * Hv ≤ n / 2)
    (a q r b : ℕ) (hr : 1 ≤ r) (hrD : r ≤ D) (hDq : D < q) (hqL : q ≤ L)
    (ha : Nat.Coprime a q) (h : ℝ) (h0 : 0 ≤ h) (h1 : h ≤ 1 / (6 * (n:ℝ)))
    (hHv : 0 ≤ Hv) :
    ¬ (|((a:ℝ) / q + h) - (b:ℝ) / r| ≤ Hv / ((r:ℝ) * n)) := by
  intro hcon
  have hnr : (0:ℝ) < n := by exact_mod_cast hn
  have hr0 : 0 < r := hr
  have hq0 : 0 < q := by omega
  have hne : a * r ≠ b * q := by
    intro heq
    have h1 : q ∣ a * r := ⟨b, by rw [heq]; ring⟩
    have h2 : q ∣ r := Nat.Coprime.dvd_of_dvd_mul_left ha.symm h1
    have := Nat.le_of_dvd hr0 h2
    omega
  have hgap := frac_gap a q b r hq0 hr0 hne
  have hqr : (0:ℝ) < q := by exact_mod_cast hq0
  have hrr : (0:ℝ) < r := by exact_mod_cast hr0
  have hqL1 : (q:ℝ) ≤ L := by exact_mod_cast hqL
  have hrL : (r:ℝ) ≤ L := by exact_mod_cast (hrD.trans (hDq.le.trans hqL))
  have hprod : (q:ℝ) * r ≤ L * L := mul_le_mul hqL1 hrL hrr.le (by positivity)
  have hb : |(a:ℝ) / q - (b:ℝ) / r| ≤ Hv / ((r:ℝ) * n) + 1 / (6 * (n:ℝ)) := by
    have : (a:ℝ) / q - (b:ℝ) / r = (((a:ℝ) / q + h) - (b:ℝ) / r) - h := by ring
    rw [this]
    calc |(((a:ℝ) / q + h) - (b:ℝ) / r) - h| ≤ |((a:ℝ) / q + h) - (b:ℝ) / r| + |h| := abs_sub _ _
      _ ≤ _ := by rw [abs_of_nonneg h0]; linarith
  have hc : 1 / ((q:ℝ) * r) ≤ Hv / ((r:ℝ) * n) + 1 / (6 * (n:ℝ)) := hgap.trans hb
  have hmul : (n:ℝ) ≤ q * Hv + (q:ℝ) * r / 6 := by
    have h1 := mul_le_mul_of_nonneg_left hc (by positivity : (0:ℝ) ≤ q * r * n)
    have e1 : (q:ℝ) * r * n * (1 / ((q:ℝ) * r)) = n := by field_simp
    have e2 : (q:ℝ) * r * n * (Hv / ((r:ℝ) * n) + 1 / (6 * (n:ℝ))) = q * Hv + (q:ℝ) * r / 6 := by
      field_simp
    rw [e1, e2] at h1
    exact h1
  have : (q:ℝ) * Hv ≤ L * Hv := mul_le_mul_of_nonneg_right hqL1 hHv
  nlinarith

private theorem window_in_unit (n : ℕ) (hn : 0 < n) (q a : ℕ) (hq1 : 1 < q) (hqn : q ≤ n)
    (ha : Nat.Coprime a q) (haq : a < q) :
    Set.Icc ((a:ℝ) / q) ((a:ℝ) / q + 1 / (6 * (n:ℝ))) ⊆ Set.Ioc 0 1 := by
  have hnr : (0:ℝ) < n := by exact_mod_cast hn
  have hqr : (0:ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have ha0 : 1 ≤ a := by
    rcases Nat.eq_zero_or_pos a with h | h
    · subst h
      simp at ha
      omega
    · exact h
  have har : (1:ℝ) ≤ a := by exact_mod_cast ha0
  have haq' : (a:ℝ) + 1 ≤ q := by exact_mod_cast haq
  have hqn' : (q:ℝ) ≤ n := by exact_mod_cast hqn
  intro t ht
  obtain ⟨h1, h2⟩ := ht
  have hpos : 0 < (a:ℝ) / q := by positivity
  constructor
  · linarith
  · have : (a:ℝ) / q + 1 / (6 * (n:ℝ)) ≤ 1 := by
      have e : (a:ℝ) / q ≤ 1 - 1 / q := by
        rw [div_le_iff₀ hqr]
        field_simp
        linarith
      have : 1 / (6 * (n:ℝ)) ≤ 1 / q := by
        apply one_div_le_one_div_of_le hqr
        linarith
      linarith
    linarith

private theorem card_mult_Ioc (T m : ℕ) (hm : 0 < m) :
    ((Finset.Ioc T (2 * T)).filter (fun x => m ∣ x)).card ≤ T / m + 1 := by
  have hinj : ((Finset.Ioc T (2 * T)).filter (fun x => m ∣ x)).card ≤
      (Finset.Ioc (T / m) (2 * T / m)).card := by
    apply Finset.card_le_card_of_injOn (fun x => x / m)
    · intro x hx
      simp only [Finset.coe_filter, Finset.mem_Ioc, Set.mem_setOf_eq] at hx
      obtain ⟨⟨h1, h2⟩, ⟨k, rfl⟩⟩ := hx
      simp only [Finset.coe_Ioc, Set.mem_Ioc]
      rw [Nat.mul_div_cancel_left _ hm]
      constructor
      · rw [Nat.div_lt_iff_lt_mul hm]
        nlinarith
      · rw [Nat.le_div_iff_mul_le hm]
        nlinarith
    · intro x hx y hy hxy
      simp only [Finset.coe_filter, Finset.mem_Ioc, Set.mem_setOf_eq] at hx hy
      obtain ⟨_, ⟨k, rfl⟩⟩ := hx
      obtain ⟨_, ⟨l, rfl⟩⟩ := hy
      simp only [Nat.mul_div_cancel_left _ hm] at hxy
      rw [hxy]
  refine hinj.trans ?_
  rw [Nat.card_Ioc]
  have h1 : 2 * T / m ≤ 2 * (T / m) + 1 := by
    have : 2 * T < (2 * (T / m) + 2) * m := by
      have := Nat.lt_mul_div_succ T hm
      nlinarith [Nat.div_add_mod T m, Nat.mod_lt T hm]
    have := (Nat.div_lt_iff_lt_mul hm).mpr this
    omega
  omega

private theorem harm_bound (M : ℕ) :
    ∑ i ∈ Finset.range M, (1:ℝ) / (((i:ℝ) + 2) ^ 2) ≤ 2 / 3 - 1 / ((M:ℝ) + 3 / 2) := by
  induction M with
  | zero => norm_num
  | succ M ih =>
    rw [Finset.sum_range_succ]
    have hM : (0:ℝ) ≤ M := Nat.cast_nonneg M
    have : (1:ℝ) / (((M:ℝ) + 2) ^ 2) ≤ 1 / ((M:ℝ) + 3 / 2) - 1 / (((M + 1 : ℕ) : ℝ) + 3 / 2) := by
      push_cast
      rw [div_sub_div _ _ (by positivity) (by positivity)]
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    linarith

private theorem sqf_block_count (T : ℕ) (hT : 72 ≤ T) :
    (T:ℝ) / 6 ≤ ((Finset.Ioc T (2 * T)).filter (fun x => Squarefree x)).card := by
  set M := Nat.sqrt (2 * T) with hM
  have hTr : (72:ℝ) ≤ T := by exact_mod_cast hT
  have hcover : (Finset.Ioc T (2 * T)).filter (fun x => ¬ Squarefree x) ⊆
      (Finset.range M).biUnion (fun i => (Finset.Ioc T (2 * T)).filter (fun x => (i + 2) * (i + 2) ∣ x)) := by
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_Ioc] at hx
    obtain ⟨⟨h1, h2⟩, hns⟩ := hx
    rw [Nat.squarefree_iff_prime_squarefree] at hns
    push_neg at hns
    obtain ⟨y, hy, hyd⟩ := hns
    have hy2 := hy.two_le
    have hyx : y * y ≤ x := Nat.le_of_dvd (by omega) hyd
    have hyM : y ≤ M := by
      rw [hM]
      apply Nat.le_sqrt.mpr
      nlinarith
    simp only [Finset.mem_biUnion, Finset.mem_range, Finset.mem_filter, Finset.mem_Ioc]
    refine ⟨y - 2, by omega, ⟨h1, h2⟩, ?_⟩
    have : y - 2 + 2 = y := by omega
    rw [this]
    exact hyd
  have hcard : (((Finset.Ioc T (2 * T)).filter (fun x => ¬ Squarefree x)).card : ℝ) ≤
      ∑ i ∈ Finset.range M, ((T:ℝ) / (((i:ℝ) + 2) ^ 2) + 1) := by
    have h1 := (Finset.card_le_card hcover).trans Finset.card_biUnion_le
    have h2 : ((Finset.range M).sum fun i => ((Finset.Ioc T (2 * T)).filter
        (fun x => (i + 2) * (i + 2) ∣ x)).card) ≤
        (Finset.range M).sum fun i => (T / ((i + 2) * (i + 2)) + 1) :=
      Finset.sum_le_sum (fun i _ => card_mult_Ioc T _ (by positivity))
    have h3 := h1.trans h2
    have h4 : (((Finset.Ioc T (2 * T)).filter (fun x => ¬ Squarefree x)).card : ℝ) ≤
        ((∑ i ∈ Finset.range M, (T / ((i + 2) * (i + 2)) + 1) : ℕ) : ℝ) := by exact_mod_cast h3
    refine h4.trans ?_
    push_cast
    apply Finset.sum_le_sum
    intro i _
    have : ((T / ((i + 2) * (i + 2)) : ℕ) : ℝ) ≤ (T:ℝ) / (((i:ℝ) + 2) ^ 2) := by
      have := Nat.cast_div_le (α := ℝ) (m := T) (n := (i + 2) * (i + 2))
      push_cast at this
      calc _ ≤ _ := this
        _ = _ := by ring
    linarith
  have hsum : ∑ i ∈ Finset.range M, ((T:ℝ) / (((i:ℝ) + 2) ^ 2) + 1) ≤ 2 * (T:ℝ) / 3 + (M:ℝ) := by
    rw [Finset.sum_add_distrib]
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    have : ∑ i ∈ Finset.range M, (T:ℝ) / (((i:ℝ) + 2) ^ 2) =
        (T:ℝ) * ∑ i ∈ Finset.range M, (1:ℝ) / (((i:ℝ) + 2) ^ 2) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [this]
    have h1 := harm_bound M
    have h2 : (0:ℝ) < 1 / ((M:ℝ) + 3 / 2) := by positivity
    nlinarith
  have hMT : (M:ℝ) ≤ T / 6 := by
    have h1 : M * M ≤ 2 * T := Nat.sqrt_le (2 * T)
    have h2 : (M:ℝ) * M ≤ 2 * T := by exact_mod_cast h1
    by_contra hcon
    push_neg at hcon
    nlinarith
  have htot : ((Finset.Ioc T (2 * T)).filter (fun x => Squarefree x)).card +
      ((Finset.Ioc T (2 * T)).filter (fun x => ¬ Squarefree x)).card = T := by
    rw [Finset.card_filter_add_card_filter_not]
    simp
    omega
  have htot' : (((Finset.Ioc T (2 * T)).filter (fun x => Squarefree x)).card : ℝ) +
      (((Finset.Ioc T (2 * T)).filter (fun x => ¬ Squarefree x)).card : ℝ) = T := by
    exact_mod_cast htot
  linarith

private theorem block_sum (T : ℕ) (hT : 72 ≤ T) :
    (1:ℝ) / 12 ≤ ∑ q ∈ (Finset.Ioc T (2 * T)).filter (fun x => Squarefree x), (1:ℝ) / q := by
  have hTr : (72:ℝ) ≤ T := by exact_mod_cast hT
  have hc := sqf_block_count T hT
  have : ∑ q ∈ (Finset.Ioc T (2 * T)).filter (fun x => Squarefree x), (1:ℝ) / (2 * T) ≤
      ∑ q ∈ (Finset.Ioc T (2 * T)).filter (fun x => Squarefree x), (1:ℝ) / q := by
    apply Finset.sum_le_sum
    intro q hq
    have hq' := Finset.mem_Ioc.mp (Finset.mem_filter.mp hq).1
    have : (q:ℝ) ≤ 2 * T := by exact_mod_cast hq'.2
    have : (0:ℝ) < q := by exact_mod_cast (show 0 < q by omega)
    apply one_div_le_one_div_of_le this
    assumption
  refine le_trans ?_ this
  rw [Finset.sum_const, nsmul_eq_mul]
  rw [mul_one_div, le_div_iff₀ (by positivity)]
  nlinarith

private theorem dyadic_sum (D : ℕ) (hD : 72 ≤ D) (J : ℕ) :
    (J:ℝ) / 12 ≤ ∑ q ∈ (Finset.Ioc D (2 ^ J * D)).filter (fun x => Squarefree x), (1:ℝ) / q := by
  induction J with
  | zero => simp
  | succ J ih =>
    have hT : 72 ≤ 2 ^ J * D := by
      have : 1 ≤ 2 ^ J := Nat.one_le_two_pow
      nlinarith
    have hb := block_sum (2 ^ J * D) hT
    have hle : D ≤ 2 ^ J * D := by
      have : 1 ≤ 2 ^ J := Nat.one_le_two_pow
      nlinarith
    have hle2 : 2 ^ J * D ≤ 2 * (2 ^ J * D) := by omega
    have e : 2 ^ (J + 1) * D = 2 * (2 ^ J * D) := by ring
    rw [e]
    simp only [Finset.sum_filter] at ih hb ⊢
    rw [← Finset.sum_Ioc_consecutive _ hle hle2]
    push_cast
    linarith
private def wide (n : ℕ) : Set ℝ :=
  {t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ ⌊Real.sqrt (n:ℝ) / ((Nat.log 2 (n+2) : ℕ) : ℝ) ^ 4⌋₊ ∧ a ≤ q ∧ Nat.Coprime a q ∧
    |t - (a:ℝ)/(q:ℝ)| ≤ ((256 * ⌊Real.sqrt (n:ℝ) / ((Nat.log 2 (n+2) : ℕ) : ℝ) ^ 4⌋₊ * (Nat.log 2 (n+2))^2 : ℕ):ℝ)/((q:ℝ)*(n:ℝ))}

private theorem wide_meas (n : ℕ) : MeasurableSet (wide n) := by
  have hset : wide n = ⋃ q : ℕ, ⋃ a : ℕ,
      {t : ℝ | 1 ≤ q ∧ q ≤ ⌊Real.sqrt (n:ℝ) / ((Nat.log 2 (n+2) : ℕ) : ℝ) ^ 4⌋₊ ∧ a ≤ q ∧ Nat.Coprime a q ∧
        |t - (a:ℝ)/(q:ℝ)| ≤ ((256 * ⌊Real.sqrt (n:ℝ) / ((Nat.log 2 (n+2) : ℕ) : ℝ) ^ 4⌋₊ * (Nat.log 2 (n+2))^2 : ℕ):ℝ)/((q:ℝ)*(n:ℝ))} := by
    ext t
    simp only [wide, Set.mem_iUnion, Set.mem_setOf_eq]
  rw [hset]
  refine MeasurableSet.iUnion (fun q => MeasurableSet.iUnion (fun a => ?_))
  by_cases h : 1 ≤ q ∧ q ≤ ⌊Real.sqrt (n:ℝ) / ((Nat.log 2 (n+2) : ℕ) : ℝ) ^ 4⌋₊ ∧ a ≤ q ∧ Nat.Coprime a q
  · have heq : {t : ℝ | 1 ≤ q ∧ q ≤ ⌊Real.sqrt (n:ℝ) / ((Nat.log 2 (n+2) : ℕ) : ℝ) ^ 4⌋₊ ∧ a ≤ q ∧ Nat.Coprime a q ∧
        |t - (a:ℝ)/(q:ℝ)| ≤ ((256 * ⌊Real.sqrt (n:ℝ) / ((Nat.log 2 (n+2) : ℕ) : ℝ) ^ 4⌋₊ * (Nat.log 2 (n+2))^2 : ℕ):ℝ)/((q:ℝ)*(n:ℝ))}
        = Set.Icc ((a:ℝ)/(q:ℝ) - ((256 * ⌊Real.sqrt (n:ℝ) / ((Nat.log 2 (n+2) : ℕ) : ℝ) ^ 4⌋₊ * (Nat.log 2 (n+2))^2 : ℕ):ℝ)/((q:ℝ)*(n:ℝ)))
            ((a:ℝ)/(q:ℝ) + ((256 * ⌊Real.sqrt (n:ℝ) / ((Nat.log 2 (n+2) : ℕ) : ℝ) ^ 4⌋₊ * (Nat.log 2 (n+2))^2 : ℕ):ℝ)/((q:ℝ)*(n:ℝ))) := by
      ext t
      constructor
      · intro ht
        obtain ⟨-, -, -, -, habs⟩ := ht
        obtain ⟨h1, h2⟩ := abs_le.mp habs
        exact ⟨by linarith, by linarith⟩
      · intro ht
        rw [Set.mem_Icc] at ht
        exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2,
          abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩⟩
    rw [heq]
    exact measurableSet_Icc
  · have heq : {t : ℝ | 1 ≤ q ∧ q ≤ ⌊Real.sqrt (n:ℝ) / ((Nat.log 2 (n+2) : ℕ) : ℝ) ^ 4⌋₊ ∧ a ≤ q ∧ Nat.Coprime a q ∧
        |t - (a:ℝ)/(q:ℝ)| ≤ ((256 * ⌊Real.sqrt (n:ℝ) / ((Nat.log 2 (n+2) : ℕ) : ℝ) ^ 4⌋₊ * (Nat.log 2 (n+2))^2 : ℕ):ℝ)/((q:ℝ)*(n:ℝ))} = ∅ := by
      ext t
      constructor
      · intro ht
        exact h ⟨ht.1, ht.2.1, ht.2.2.1, ht.2.2.2.1⟩
      · intro ht
        exact absurd ht (by simp)
    rw [heq]
    exact MeasurableSet.empty

set_option maxHeartbeats 1000000 in

private theorem poly_exp : ∃ M : ℕ, 1024 ≤ M ∧ ∀ l : ℕ, M ≤ l → 1000000 * (l:ℝ) ^ 8 + 2 ≤ 2 ^ l := by
  have h := tendsto_pow_const_div_const_pow_of_one_lt 8 (by norm_num : (1:ℝ) < 2)
  have h2 : ∀ᶠ l : ℕ in Filter.atTop, (l:ℝ) ^ 8 / 2 ^ l < 1 / 2000000 :=
    h.eventually (gt_mem_nhds (by norm_num))
  obtain ⟨M0, hM0⟩ := Filter.eventually_atTop.mp h2
  refine ⟨max M0 1024, le_max_right _ _, ?_⟩
  intro l hl
  have hl0 : M0 ≤ l := le_trans (le_max_left _ _) hl
  have hl1 : 1024 ≤ l := le_trans (le_max_right _ _) hl
  have h3 := hM0 l hl0
  have hp : (0:ℝ) < 2 ^ l := by positivity
  rw [div_lt_iff₀ hp] at h3
  have h4 : (2:ℝ) ^ 2 ≤ 2 ^ l := pow_le_pow_right₀ (by norm_num) (by omega)
  have h5 : (4:ℝ) = 2 ^ 2 := by norm_num
  linarith

set_option maxHeartbeats 1000000 in
private theorem main_bound : ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    c * (n:ℝ) * Real.log (Real.log (n:ℝ)) ≤
      ∫ t in (0:ℝ)..1, (wide n)ᶜ.indicator (fun u => ‖SS n u‖ ^ 2) t := by
  have hθ : ∀ᶠ n : ℕ in Filter.atTop, (n:ℝ) / 2 ≤ Chebyshev.theta (n:ℝ) := by
    have h := Chebyshev.tendsto_theta_div_atTop
    have h2 : ∀ᶠ x : ℝ in Filter.atTop, (1:ℝ) / 2 < Chebyshev.theta x / x :=
      h.eventually (lt_mem_nhds (by norm_num))
    have h3 : ∀ᶠ n : ℕ in Filter.atTop, (1:ℝ) / 2 < Chebyshev.theta (n:ℝ) / n :=
      tendsto_natCast_atTop_atTop.eventually h2
    filter_upwards [h3, Filter.eventually_gt_atTop 0] with n h1 h2
    have hn : (0:ℝ) < n := by exact_mod_cast h2
    rw [lt_div_iff₀ hn] at h1
    linarith
  obtain ⟨N1, hN1⟩ := Filter.eventually_atTop.mp hθ
  obtain ⟨M, hM1024, hM⟩ := poly_exp
  refine ⟨1 / 4000, by norm_num, max N1 (2 ^ M), ?_⟩
  intro n hn
  have hnN1 : N1 ≤ n := le_trans (le_max_left _ _) hn
  have hnM : 2 ^ M ≤ n := le_trans (le_max_right _ _) hn
  have hθn := hN1 n hnN1
  set ℓ : ℕ := Nat.log 2 (n + 2) with hℓdef
  have hℓM : M ≤ ℓ := Nat.le_log_of_pow_le (by norm_num) (by omega)
  have hℓ1024 : (1024:ℝ) ≤ ℓ := by exact_mod_cast hM1024.trans hℓM
  have h2l : 2 ^ ℓ ≤ n + 2 := Nat.pow_log_le_self 2 (by omega)
  have h2lr : (2:ℝ) ^ ℓ ≤ n + 2 := by exact_mod_cast h2l
  have hnlt : n + 2 < 2 ^ (ℓ + 1) := Nat.lt_pow_succ_log_self (by norm_num) (n + 2)
  have hnltr : (n:ℝ) + 2 < 2 ^ (ℓ + 1) := by exact_mod_cast hnlt
  have hpoly := hM ℓ hℓM
  have hn8 : 1000000 * (ℓ:ℝ) ^ 8 ≤ n := by linarith
  have hnpos : 0 < n := by
    have : (0:ℝ) < n := by
      have : (0:ℝ) < (ℓ:ℝ) ^ 8 := by positivity
      linarith
    exact_mod_cast this
  have hnr : (0:ℝ) < n := by exact_mod_cast hnpos
  set s : ℝ := Real.sqrt n with hsdef
  have hs2 : s ^ 2 = n := Real.sq_sqrt hnr.le
  have hs0 : 0 < s := Real.sqrt_pos.mpr hnr
  have hℓ0 : (0:ℝ) < ℓ := by linarith
  have hℓ4 : (0:ℝ) < (ℓ:ℝ) ^ 4 := by positivity
  have hs1000 : 1000 * (ℓ:ℝ) ^ 4 ≤ s := by
    have h1 : (1000 * (ℓ:ℝ) ^ 4) ^ 2 ≤ s ^ 2 := by rw [hs2]; nlinarith
    exact (pow_le_pow_iff_left₀ (by positivity) hs0.le (by norm_num : (2:ℕ) ≠ 0)).mp h1
  have hℓ4big : (1024:ℝ) ≤ (ℓ:ℝ) ^ 4 := by nlinarith [pow_le_pow_left₀ (by norm_num) hℓ1024 4]
  have hsbig : (1000000:ℝ) ≤ s := by linarith
  set D : ℕ := ⌊s / (ℓ:ℝ) ^ 4⌋₊ with hDdef
  set L : ℕ := Nat.sqrt n / 4 with hLdef
  have hDle : (D:ℝ) * (ℓ:ℝ) ^ 4 ≤ s := by
    have := Nat.floor_le (div_nonneg hs0.le hℓ4.le)
    rw [le_div_iff₀ hℓ4] at this
    exact this
  have hDlt : s < ((D:ℝ) + 1) * (ℓ:ℝ) ^ 4 := by
    have := Nat.lt_floor_add_one (s / (ℓ:ℝ) ^ 4)
    rw [div_lt_iff₀ hℓ4] at this
    exact this
  have hD72 : 72 ≤ D := by
    have : (71:ℝ) < D := by nlinarith
    have : 71 < D := by exact_mod_cast this
    omega
  have hL16n : L * L * 16 ≤ n := by
    have h1 : 4 * L ≤ Nat.sqrt n := by
      rw [hLdef]
      omega
    have h2 : Nat.sqrt n * Nat.sqrt n ≤ n := Nat.sqrt_le n
    nlinarith
  have hL16 : (L:ℝ) * L * 16 ≤ n := by exact_mod_cast hL16n
  have hLs : 4 * (L:ℝ) ≤ s := by
    have h1 : 4 * L ≤ Nat.sqrt n := by
      rw [hLdef]
      omega
    have h1r : (4 * L : ℝ) ≤ (Nat.sqrt n : ℝ) := by exact_mod_cast h1
    have := Real.nat_sqrt_le_real_sqrt (a := n)
    linarith
  have hsL : s < 4 * (L:ℝ) + 4 := by
    have h1 : Nat.sqrt n ≤ 4 * L + 3 := by
      rw [hLdef]
      omega
    have h1r : (Nat.sqrt n : ℝ) ≤ 4 * (L:ℝ) + 3 := by exact_mod_cast h1
    have := Real.real_sqrt_lt_nat_sqrt_succ (a := n)
    linarith
  have hDsL : (D:ℝ) * 8 ≤ s := by nlinarith
  have hDL : D ≤ L := by
    have : (D:ℝ) ≤ L := by nlinarith
    exact_mod_cast this
  have hD0 : 0 < D := by omega
  have hLD : L / D ≠ 0 := by
    have := Nat.div_pos hDL hD0
    omega
  set J : ℕ := Nat.log 2 (L / D) with hJdef
  have hJ1 : 2 ^ J * D ≤ L := by
    have h1 : 2 ^ J ≤ L / D := Nat.pow_log_le_self 2 hLD
    calc 2 ^ J * D ≤ (L / D) * D := Nat.mul_le_mul_right D h1
      _ ≤ L := Nat.div_mul_le_self L D
  have hJ2 : (ℓ:ℝ) ^ 4 < 8 * 2 ^ (J + 1) := by
    have h1 : L / D < 2 ^ (J + 1) := Nat.lt_pow_succ_log_self (by norm_num) (L / D)
    have h2 : L < D * (L / D + 1) := Nat.lt_mul_div_succ L hD0
    have h3 : L < D * 2 ^ (J + 1) := by
      calc L < D * (L / D + 1) := h2
        _ ≤ D * 2 ^ (J + 1) := Nat.mul_le_mul_left D h1
    have h3r : (L:ℝ) < (D:ℝ) * 2 ^ (J + 1) := by exact_mod_cast h3
    have hp : (0:ℝ) < 2 ^ (J + 1) := by positivity
    have h4 : s / 8 ≤ (L:ℝ) := by linarith
    have h5 : s / 8 < (D:ℝ) * 2 ^ (J + 1) := by linarith
    have h6 : s * (ℓ:ℝ) ^ 4 < 8 * 2 ^ (J + 1) * s := by
      have := mul_lt_mul_of_pos_right h5 hℓ4
      nlinarith
    nlinarith
  have hℓ2 : (40000:ℝ) ≤ (ℓ:ℝ) ^ 2 := by nlinarith
  have hLH : (L:ℝ) * ((256 * D * ℓ ^ 2 : ℕ) : ℝ) ≤ n / 2 := by
    push_cast
    have hX : (D:ℝ) * (ℓ:ℝ) ^ 2 * 40000 ≤ s := by
      have : (D:ℝ) * (ℓ:ℝ) ^ 2 * (ℓ:ℝ) ^ 2 ≤ s := by nlinarith
      have h0 : (0:ℝ) ≤ (D:ℝ) * (ℓ:ℝ) ^ 2 := by positivity
      nlinarith
    have h0 : (0:ℝ) ≤ (D:ℝ) * (ℓ:ℝ) ^ 2 := by positivity
    have h1 : (L:ℝ) * ((D:ℝ) * (ℓ:ℝ) ^ 2) ≤ s / 4 * ((D:ℝ) * (ℓ:ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_right (by linarith) h0
    have h2 : s / 4 * ((D:ℝ) * (ℓ:ℝ) ^ 2) ≤ s / 4 * (s / 40000) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    rw [← hs2]
    nlinarith
  have hH0 : (0:ℝ) ≤ ((256 * D * ℓ ^ 2 : ℕ) : ℝ) := Nat.cast_nonneg _
  set Sq := (Finset.Ioc D (2 ^ J * D)).filter (fun x => Squarefree x) with hSqdef
  have hmem : ∀ q ∈ Sq, Squarefree q ∧ D < q ∧ q ≤ L := by
    intro q hq
    rw [hSqdef, Finset.mem_filter, Finset.mem_Ioc] at hq
    exact ⟨hq.2, hq.1.1, hq.1.2.trans hJ1⟩
  have hunit : ∀ q a : ℕ, a ∈ units q → a < q ∧ Nat.Coprime a q := by
    intro q a ha
    have := Finset.mem_filter.mp ha
    exact ⟨Finset.mem_range.mp this.1, this.2⟩
  have hint := window_integral n (wide n) (wide_meas n) hnpos Sq
    (by
      intro q hq
      obtain ⟨h1, h2, h3⟩ := hmem q hq
      have hq1 : 1 < q := by omega
      refine ⟨h1, hq1, ?_⟩
      have hq3 : (q:ℝ) ≤ L := by exact_mod_cast h3
      have hq4 : (q:ℝ) ≤ s / 4 := by linarith
      have hq5 : (1:ℝ) ≤ q := by exact_mod_cast (show 1 ≤ q by omega)
      have hq6 : Real.log q ≤ s / 4 := by
        have := Real.log_le_sub_one_of_pos (show (0:ℝ) < q by linarith)
        linarith
      have hq7 : 0 ≤ Real.log q := Real.log_nonneg hq5
      have hq8 : 2 * (q:ℝ) * Real.log q ≤ 2 * (s / 4) * (s / 4) := by
        apply mul_le_mul _ hq6 hq7 (by positivity)
        linarith
      rw [← hs2]
      nlinarith)
    hθn
    (by
      intro q hq a ha
      obtain ⟨h1, h2, h3⟩ := hmem q hq
      obtain ⟨haq, hacop⟩ := hunit q a ha
      have hq1 : 1 < q := by omega
      have hqn : q ≤ n := by
        have : (q:ℝ) ≤ n := by
          have hq3 : (q:ℝ) ≤ L := by exact_mod_cast h3
          nlinarith
        exact_mod_cast this
      intro x hx
      refine ⟨?_, window_in_unit n hnpos q a hq1 hqn hacop haq hx⟩
      intro hxw
      obtain ⟨r, b, hr1, hrD, hbr, hbc, habs⟩ := hxw
      have key := window_avoid n hnpos D L ((256 * D * ℓ ^ 2 : ℕ) : ℝ) hL16 hLH a q r b hr1 hrD h2 h3
        hacop (x - (a:ℝ) / q) (by linarith [hx.1]) (by linarith [hx.2]) hH0
      have hrw : (a:ℝ) / q + (x - (a:ℝ) / q) = x := by ring
      rw [hrw] at key
      exact key habs)
    (by
      intro q hq a ha q' hq' a' ha' hne
      obtain ⟨h1, h2, h3⟩ := hmem q hq
      obtain ⟨h1', h2', h3'⟩ := hmem q' hq'
      exact window_disjoint n L hnpos hL16 a q a' q' (by omega) (by omega) h3 h3'
        (hunit q a ha).2 (hunit q' a' ha').2 hne)
  have hsum : ∑ q ∈ Sq, (n:ℝ) / (384 * (q:ℝ)) = (n:ℝ) / 384 * ∑ q ∈ Sq, (1:ℝ) / q := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro q hq
    have : (0:ℝ) < q := by
      have := (hmem q hq).2.1
      exact_mod_cast (show 0 < q by omega)
    field_simp
  have hdy := dyadic_sum D hD72 J
  have hlog2a := Real.log_two_lt_d9
  have hlog2b := Real.log_two_gt_d9
  have hlogℓ : 6 ≤ Real.log ℓ := by
    have h1 : (2:ℝ) ^ 10 ≤ ℓ := by
      have : (2:ℝ) ^ 10 = 1024 := by norm_num
      linarith
    have h2 := Real.log_le_log (by positivity) h1
    rw [Real.log_pow] at h2
    push_cast at h2
    linarith
  have hJlog : 3 * Real.log ℓ ≤ (J:ℝ) := by
    have h2 := Real.log_lt_log hℓ4 hJ2
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow, Real.log_pow] at h2
    have h8 : Real.log 8 = 3 * Real.log 2 := by
      rw [show (8:ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
      norm_num
    push_cast at h2
    rw [h8] at h2
    nlinarith
  have hlogn : Real.log (n:ℝ) ≤ (ℓ:ℝ) + 1 := by
    have h1 : Real.log (n:ℝ) ≤ Real.log (2 ^ (ℓ + 1)) :=
      Real.log_le_log hnr (by linarith)
    rw [Real.log_pow] at h1
    push_cast at h1
    nlinarith
  have hn3 : (3:ℝ) ≤ n := by
    have : (3:ℝ) ≤ (ℓ:ℝ) ^ 8 := by nlinarith [pow_le_pow_left₀ (by norm_num) hℓ1024 8]
    linarith
  have hlogpos : 0 < Real.log (n:ℝ) := Real.log_pos (by linarith)
  have hll : Real.log (Real.log (n:ℝ)) ≤ 2 * Real.log ℓ := by
    have h1 := Real.log_le_log hlogpos hlogn
    have h2 : Real.log ((ℓ:ℝ) + 1) ≤ Real.log (2 * ℓ) :=
      Real.log_le_log (by linarith) (by linarith)
    rw [Real.log_mul (by norm_num) hℓ0.ne'] at h2
    linarith
  rw [hsum] at hint
  have hint2 : (n:ℝ) / 384 * ((J:ℝ) / 12) ≤ ∫ t in (0:ℝ)..1, (wide n)ᶜ.indicator (fun u => ‖SS n u‖ ^ 2) t := by
    refine le_trans ?_ hint
    apply mul_le_mul_of_nonneg_left hdy (by positivity)
  refine le_trans ?_ hint2
  have hn0 : (0:ℝ) ≤ n := hnr.le
  have h1 := mul_le_mul_of_nonneg_left hJlog hn0
  have h2 := mul_le_mul_of_nonneg_left hll hn0
  nlinarith

theorem Conjectures.Goldbach.SqrtArcSecondMomentFloor :
    let w := fun k : ℕ => if Nat.Prime k then Real.log (k:ℝ) else 0; let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let S := fun (n : ℕ) (u : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (u k:ℂ)*E ((k:ℝ)*t)); let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let Q₂ := fun n : ℕ => ⌊Real.sqrt (n : ℝ) / ((Nat.log 2 (n + 2) : ℝ) ^ 4)⌋₊; let sqrtArcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ Q₂ n ∧ a ≤ q ∧ Nat.Coprime a q ∧ |t - (a : ℝ) / (q : ℝ)| ≤ ((256 * Q₂ n * Q n : ℕ) : ℝ) / ((q : ℝ) * (n : ℝ))}; ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n → c * (n : ℝ) * Real.log (Real.log (n : ℝ)) ≤ intervalIntegral (fun t => (sqrtArcs n)ᶜ.indicator (fun u => ‖S n w u‖ ^ 2) t) (0 : ℝ) 1 MeasureTheory.volume := by
  intro w E S Q Q₂ sqrtArcs
  exact main_bound
