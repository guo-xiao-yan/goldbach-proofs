import Mathlib

open MeasureTheory

private lemma pdml_geom (x : ℝ) (M : ℕ) (hx : Int.fract x ≠ 0) :
    ‖∑ j ∈ Finset.range M, (Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I))^(j+1)‖
      ≤ 1 / Real.sin (Real.pi * Int.fract x) := by
  have hfr0 : 0 < Int.fract x := lt_of_le_of_ne (Int.fract_nonneg x) (Ne.symm hx)
  have hfr1 : Int.fract x < 1 := Int.fract_lt_one x
  have hsin : 0 < Real.sin (Real.pi * Int.fract x) :=
    Real.sin_pos_of_pos_of_lt_pi (by positivity) (by nlinarith [Real.pi_pos])
  have habs : |Real.sin (Real.pi * x)| = Real.sin (Real.pi * Int.fract x) := by
    have h := Int.floor_add_fract x
    have e : Real.pi * x = Real.pi * Int.fract x + (⌊x⌋ : ℤ) * Real.pi := by
      calc Real.pi * x = Real.pi * ((⌊x⌋ : ℝ) + Int.fract x) := by rw [h]
        _ = _ := by ring
    rw [e, Real.sin_add_int_mul_pi, abs_mul, abs_zpow, abs_neg, abs_one, one_zpow, one_mul,
      abs_of_pos hsin]
  have hw_norm : ‖Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I)‖ = 1 :=
    Complex.norm_exp_ofReal_mul_I _
  have hnorm : ‖Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I) - 1‖
      = 2 * Real.sin (Real.pi * Int.fract x) := by
    have h := Complex.norm_exp_I_mul_ofReal_sub_one (2*Real.pi*x)
    rw [mul_comm _ Complex.I, h, Real.norm_eq_abs, abs_mul, abs_two]
    have e : 2*Real.pi*x/2 = Real.pi*x := by ring
    rw [e, habs]
  generalize Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I) = w at hw_norm hnorm ⊢
  have hw1 : w ≠ 1 := by
    intro h; rw [h] at hnorm; simp at hnorm; linarith
  have hsum : ∑ j ∈ Finset.range M, w^(j+1) = w * ((w^M - 1)/(w-1)) := by
    rw [← geom_sum_eq hw1, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro j _; ring
  rw [hsum, norm_mul, norm_div, hnorm, hw_norm, one_mul]
  have h2 : ‖w^M - 1‖ ≤ 2 := (norm_sub_le _ _).trans (by
    rw [norm_pow, hw_norm, one_pow, norm_one]; norm_num)
  calc ‖w^M - 1‖ / (2 * Real.sin (Real.pi * Int.fract x))
      ≤ 2 / (2 * Real.sin (Real.pi * Int.fract x)) :=
        div_le_div_of_nonneg_right h2 (by positivity)
    _ = 1 / Real.sin (Real.pi * Int.fract x) := by field_simp

private lemma pdml_sin (s : ℝ) (h0 : 0 < s) (h1 : s < 1) :
    1 / Real.sin (Real.pi * s) ^ 2 ≤ 1 / (4 * s^2) + 1 / (4 * (1-s)^2) := by
  have key : ∀ u : ℝ, 0 < u → u ≤ 1/2 → 1 / Real.sin (Real.pi*u)^2 ≤ 1/(4*u^2) := by
    intro u hu hu2
    have h := Real.mul_le_sin (x := Real.pi*u) (by positivity) (by nlinarith [Real.pi_pos])
    have h2 : 2*u ≤ Real.sin (Real.pi*u) := by
      have e : 2/Real.pi*(Real.pi*u) = 2*u := by field_simp
      linarith
    apply one_div_le_one_div_of_le (by positivity)
    nlinarith
  rcases le_or_gt s (1/2) with h | h
  · have := key s h0 h
    have : 0 ≤ 1 / (4 * (1-s)^2) := by positivity
    linarith
  · have e : Real.sin (Real.pi * s) = Real.sin (Real.pi * (1-s)) := by
      rw [mul_sub, mul_one, Real.sin_pi_sub]
    rw [e]
    have := key (1-s) (by linarith) (by linarith)
    have : 0 ≤ 1 / (4 * s^2) := by positivity
    linarith

private lemma pdml_ii (f : ℝ → ℝ) (hf : Measurable f) (K : ℝ) (hK : ∀ x, |f x| ≤ K) (d : ℝ) :
    IntervalIntegrable (fun t => f (d*t)) volume 0 1 := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
  exact Measure.integrableOn_of_bounded (M := K) (by simp)
    (hf.comp (measurable_const_mul d)).aestronglyMeasurable
    (ae_of_all _ fun x => by simpa using hK _)

private lemma pdml_intF1 (ε : ℝ) (hε : 0 < ε) :
    ∫ s in (0:ℝ)..1, (Set.Ioi ε).indicator (fun u : ℝ => 1/(4*u^2)) s ≤ 1/(4*ε) := by
  rw [intervalIntegral.integral_of_le zero_le_one, setIntegral_indicator measurableSet_Ioi]
  have hset : Set.Ioc (0:ℝ) 1 ∩ Set.Ioi ε = Set.Ioc ε 1 := by
    ext u; simp only [Set.mem_inter_iff, Set.mem_Ioc, Set.mem_Ioi]; constructor
    · rintro ⟨⟨_, h2⟩, h3⟩; exact ⟨h3, h2⟩
    · rintro ⟨h3, h2⟩; exact ⟨⟨by linarith, h2⟩, h3⟩
  rw [hset]
  rcases le_or_gt 1 ε with h | h
  · rw [Set.Ioc_eq_empty (not_lt.2 h)]; simp; positivity
  · rw [← intervalIntegral.integral_of_le h.le]
    have hc : ∀ u ∈ Set.uIcc ε 1, 1/(4*u^2) = (1/4) * u^(-2:ℤ) := by
      intro u _
      rw [zpow_neg, zpow_ofNat]; field_simp
    rw [intervalIntegral.integral_congr hc, intervalIntegral.integral_const_mul,
      integral_zpow (Or.inr ⟨by norm_num, by
        rw [Set.uIcc_of_le h.le]; intro hm; exact absurd hm.1 (by linarith [hm.1, hε])⟩)]
    have : (1:ℝ)^((-2:ℤ)+1) = 1 := one_zpow _
    rw [this]
    have e : ε^((-2:ℤ)+1) = ε⁻¹ := by norm_num
    rw [e]
    have : 1/(4*ε) = (1/4) * ε⁻¹ := by field_simp
    rw [this]
    have : 0 ≤ (1/4:ℝ) := by norm_num
    apply mul_le_mul_of_nonneg_left _ this
    norm_num
    rw [div_neg, div_one]; linarith [inv_pos.2 hε]

private lemma pdml_F1_meas (ε : ℝ) :
    Measurable ((Set.Ioi ε).indicator (fun u : ℝ => 1/(4*u^2))) :=
  Measurable.indicator (by fun_prop) measurableSet_Ioi

private lemma pdml_F1_bdd (ε : ℝ) (hε : 0 < ε) (s : ℝ) :
    |(Set.Ioi ε).indicator (fun u : ℝ => 1/(4*u^2)) s| ≤ 1/(4*ε^2) := by
  by_cases h : s ∈ Set.Ioi ε
  · rw [Set.indicator_of_mem h]
    have hs : ε < s := h
    rw [abs_of_nonneg (by positivity)]
    apply one_div_le_one_div_of_le (by positivity)
    nlinarith
  · rw [Set.indicator_of_notMem h]; simp; positivity

private lemma pdml_psi (ε : ℝ) (hε : 0 < ε) (d : ℕ) (hd : 1 ≤ d) :
    ∫ t in (0:ℝ)..1,
      ((Set.Ioi ε).indicator (fun u : ℝ => 1/(4*u^2)) (Int.fract ((d:ℝ)*t))
        + (Set.Ioi ε).indicator (fun u : ℝ => 1/(4*u^2)) (1 - Int.fract ((d:ℝ)*t)))
      ≤ 1/(2*ε) := by
  set F := (Set.Ioi ε).indicator (fun u : ℝ => 1/(4*u^2)) with hF
  set ψ : ℝ → ℝ := fun u => F (Int.fract u) + F (1 - Int.fract u) with hψ
  have hmeas : Measurable ψ :=
    ((pdml_F1_meas ε).comp measurable_fract).add
      ((pdml_F1_meas ε).comp (measurable_const.sub measurable_fract))
  have hbd : ∀ x, |ψ x| ≤ 1/(4*ε^2) + 1/(4*ε^2) := fun x =>
    (abs_add_le _ _).trans (add_le_add (pdml_F1_bdd ε hε _) (pdml_F1_bdd ε hε _))
  have hper : Function.Periodic ψ 1 := by
    intro x; simp only [hψ, Int.fract_add_one]
  have hint : ∀ a b, IntervalIntegrable ψ volume a b := fun a b =>
    hper.intervalIntegrable (t := 0) one_ne_zero (by simpa using pdml_ii ψ hmeas _ hbd 1) a b
  have h1 : (d:ℝ) * ∫ t in (0:ℝ)..1, ψ ((d:ℝ)*t) = (d:ℤ) * ∫ t in (0:ℝ)..1, ψ t := by
    have e1 := intervalIntegral.smul_integral_comp_mul_left (a := (0:ℝ)) (b := 1) ψ (d:ℝ)
    have e2 := hper.intervalIntegral_add_zsmul_eq (d:ℤ) 0 hint
    simp only [smul_eq_mul, zsmul_eq_mul, mul_zero, mul_one, zero_add] at e1 e2
    simp only [Int.cast_natCast] at e2 ⊢
    rw [e1]; exact e2
  have hd0 : (d:ℝ) ≠ 0 := by positivity
  have h2 : ∫ t in (0:ℝ)..1, ψ ((d:ℝ)*t) = ∫ t in (0:ℝ)..1, ψ t := by
    simp only [Int.cast_natCast] at h1
    exact mul_left_cancel₀ hd0 h1
  show ∫ t in (0:ℝ)..1, ψ ((d:ℝ)*t) ≤ _
  rw [h2]
  have h3 : ∫ t in (0:ℝ)..1, ψ t = ∫ t in (0:ℝ)..1, (F t + F (1 - t)) := by
    apply intervalIntegral.integral_congr
    intro u hu
    rw [Set.uIcc_of_le zero_le_one] at hu
    simp only [hψ]
    rcases eq_or_lt_of_le hu.2 with h | h
    · subst h; simp [add_comm]
    · rw [Int.fract_eq_self.2 ⟨hu.1, h⟩]
  rw [h3]
  have hi1 : IntervalIntegrable F volume 0 1 := by
    simpa using pdml_ii F (pdml_F1_meas ε) _ (pdml_F1_bdd ε hε) 1
  have hi2 : IntervalIntegrable (fun t => F (1 - t)) volume 0 1 := by
    have := pdml_ii (fun s => F (1 - s)) ((pdml_F1_meas ε).comp (measurable_const.sub measurable_id))
      _ (fun x => pdml_F1_bdd ε hε _) 1
    simpa using this
  rw [intervalIntegral.integral_add hi1 hi2]
  have h4 : ∫ t in (0:ℝ)..1, F (1 - t) = ∫ t in (0:ℝ)..1, F t := by
    rw [intervalIntegral.integral_comp_sub_left F 1]; simp
  rw [h4]
  have := pdml_intF1 ε hε
  have e : 1/(2*ε) = 1/(4*ε) + 1/(4*ε) := by field_simp; ring
  rw [e]; linarith

private lemma pdml_near (n Q d : ℕ) (hn : 0 < n) (hd1 : 1 ≤ d) (hdQ : d ≤ Q) (t : ℝ) (b : ℕ)
    (hb : b ≤ d) (h : |(d:ℝ)*t - b| ≤ (Q:ℝ)/n) :
    ∃ q a : ℕ, 1≤q ∧ q≤Q ∧ a≤q ∧ Nat.Coprime a q ∧
      |t-(a:ℝ)/(q:ℝ)| ≤ (Q:ℝ)/((q:ℝ)*(n:ℝ)) := by
  have hg : 0 < Nat.gcd b d := Nat.gcd_pos_of_pos_right _ (by omega)
  have hq1 : 1 ≤ d / Nat.gcd b d := Nat.div_pos (Nat.gcd_le_right _ (by omega)) hg
  have hqd : d / Nat.gcd b d ≤ d := Nat.div_le_self _ _
  refine ⟨d / Nat.gcd b d, b / Nat.gcd b d, hq1, hqd.trans hdQ, Nat.div_le_div_right hb,
    Nat.coprime_div_gcd_div_gcd hg, ?_⟩
  have hgR : (Nat.gcd b d : ℝ) ≠ 0 := by positivity
  have hqR : ((d / Nat.gcd b d : ℕ) : ℝ) = (d:ℝ) / Nat.gcd b d :=
    Nat.cast_div (Nat.gcd_dvd_right _ _) hgR
  have haR : ((b / Nat.gcd b d : ℕ) : ℝ) = (b:ℝ) / Nat.gcd b d :=
    Nat.cast_div (Nat.gcd_dvd_left _ _) hgR
  have hdR : (0:ℝ) < d := by exact_mod_cast hd1
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have hq1R : (0:ℝ) < ((d / Nat.gcd b d : ℕ) : ℝ) := by exact_mod_cast hq1
  have hqdR : ((d / Nat.gcd b d : ℕ) : ℝ) ≤ d := by exact_mod_cast hqd
  have e : ((b / Nat.gcd b d : ℕ) : ℝ) / ((d / Nat.gcd b d : ℕ) : ℝ) = (b:ℝ)/d := by
    rw [haR, hqR]; field_simp
  rw [e]
  have e2 : t - (b:ℝ)/d = ((d:ℝ)*t - b)/d := by field_simp
  rw [e2, abs_div, abs_of_pos hdR]
  have hQ0 : (0:ℝ) ≤ Q := Nat.cast_nonneg _
  calc |(d:ℝ)*t - b| / d ≤ ((Q:ℝ)/n)/d := div_le_div_of_nonneg_right h hdR.le
    _ = (Q:ℝ)/((d:ℝ)*n) := by rw [div_div, mul_comm]
    _ ≤ _ := div_le_div_of_nonneg_left hQ0 (by positivity)
        (mul_le_mul_of_nonneg_right hqdR hnR.le)

private lemma pdml_psi_ii (ε : ℝ) (hε : 0 < ε) (d : ℝ) :
    IntervalIntegrable (fun t : ℝ =>
      (Set.Ioi ε).indicator (fun u : ℝ => 1/(4*u^2)) (Int.fract (d*t))
        + (Set.Ioi ε).indicator (fun u : ℝ => 1/(4*u^2)) (1 - Int.fract (d*t))) volume 0 1 :=
  pdml_ii (fun u => (Set.Ioi ε).indicator (fun u : ℝ => 1/(4*u^2)) (Int.fract u)
        + (Set.Ioi ε).indicator (fun u : ℝ => 1/(4*u^2)) (1 - Int.fract u))
    (((pdml_F1_meas ε).comp measurable_fract).add
      ((pdml_F1_meas ε).comp (measurable_const.sub measurable_fract)))
    (1/(4*ε^2) + 1/(4*ε^2))
    (fun x => (abs_add_le _ _).trans (add_le_add (pdml_F1_bdd ε hε _) (pdml_F1_bdd ε hε _))) d

private lemma pdml_range (n Q d : ℕ) (hn : 0 < n) (hd1 : 1 ≤ d) (hdQ : d ≤ Q) (t : ℝ)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hna : ¬ ∃ q a : ℕ, 1≤q ∧ q≤Q ∧ a≤q ∧ Nat.Coprime a q ∧
      |t-(a:ℝ)/(q:ℝ)| ≤ (Q:ℝ)/((q:ℝ)*(n:ℝ))) :
    (Q:ℝ)/n < Int.fract ((d:ℝ)*t) ∧ Int.fract ((d:ℝ)*t) < 1 - (Q:ℝ)/n := by
  have hdR : (0:ℝ) ≤ d := Nat.cast_nonneg _
  have hx0 : 0 ≤ (d:ℝ)*t := mul_nonneg hdR ht0
  have hx1 : (d:ℝ)*t ≤ d := by
    calc (d:ℝ)*t ≤ d*1 := mul_le_mul_of_nonneg_left ht1 hdR
      _ = d := mul_one _
  have hfl : 0 ≤ ⌊(d:ℝ)*t⌋ := Int.floor_nonneg.2 hx0
  obtain ⟨b, hb⟩ := Int.eq_ofNat_of_zero_le hfl
  have hbR : (b:ℝ) = ⌊(d:ℝ)*t⌋ := by rw [hb]; simp
  have hfx : Int.fract ((d:ℝ)*t) = (d:ℝ)*t - b := by rw [hbR]; rfl
  have hfl1 : (b:ℝ) ≤ (d:ℝ)*t := by rw [hbR]; exact Int.floor_le _
  have hf0 : 0 ≤ Int.fract ((d:ℝ)*t) := Int.fract_nonneg _
  have hf1 : Int.fract ((d:ℝ)*t) < 1 := Int.fract_lt_one _
  have first : (Q:ℝ)/n < Int.fract ((d:ℝ)*t) := by
    by_contra hcon
    push_neg at hcon
    apply hna
    apply pdml_near n Q d hn hd1 hdQ t b
    · have : (b:ℝ) ≤ d := hfl1.trans hx1
      exact_mod_cast this
    · rw [abs_of_nonneg (by linarith)]
      linarith
  refine ⟨first, ?_⟩
  by_contra hcon
  push_neg at hcon
  have hfp : 0 < Int.fract ((d:ℝ)*t) := lt_of_le_of_lt (by positivity) first
  apply hna
  have hbd : b + 1 ≤ d := by
    have : (b:ℝ) < d := by
      linarith
    have : b < d := by exact_mod_cast this
    omega
  apply pdml_near n Q d hn hd1 hdQ t (b+1) hbd
  push_cast
  rw [abs_of_nonpos (by linarith)]
  linarith

set_option maxHeartbeats 2000000 in
private lemma pdml_main (n R Q : ℕ) (c : ℕ → ℝ) (M : ℕ → ℕ) (hn : 0 < n) (hQ : 1 ≤ Q)
    (hR : R ≤ Q) :
    ∫ t in (0:ℝ)..1, ({t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q ∧ a≤q ∧ Nat.Coprime a q ∧
        |t-(a:ℝ)/(q:ℝ)| ≤ (Q:ℝ)/((q:ℝ)*(n:ℝ))}ᶜ).indicator
      (fun t => ‖∑ d ∈ Finset.Icc 1 R, (c d:ℂ) * ∑ j ∈ Finset.range (M d),
        (Complex.exp (((2*Real.pi*((d:ℝ)*t):ℝ):ℂ)*Complex.I))^(j+1)‖^2) t
      ≤ (2*Real.pi*(n:ℝ)/(Q:ℝ)) * (∑ d ∈ Finset.Icc 1 R, |c d|)^2 := by
  have hQR : (0:ℝ) < Q := by exact_mod_cast hQ
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have hε0 : 0 < (Q:ℝ)/n := by positivity
  generalize hε : (Q:ℝ)/n = ε at hε0
  set F : ℝ → ℝ := (Set.Ioi ε).indicator (fun u : ℝ => 1/(4*u^2)) with hF
  have hF0 : ∀ u, 0 ≤ F u := fun u => Set.indicator_nonneg (fun _ _ => by positivity) u
  set S : ℝ := ∑ d ∈ Finset.Icc 1 R, |c d| with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hpt : ∀ t ∈ Set.Ioc (0:ℝ) 1,
      ({t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q ∧ a≤q ∧ Nat.Coprime a q ∧
        |t-(a:ℝ)/(q:ℝ)| ≤ (Q:ℝ)/((q:ℝ)*(n:ℝ))}ᶜ).indicator
      (fun t => ‖∑ d ∈ Finset.Icc 1 R, (c d:ℂ) * ∑ j ∈ Finset.range (M d),
        (Complex.exp (((2*Real.pi*((d:ℝ)*t):ℝ):ℂ)*Complex.I))^(j+1)‖^2) t
      ≤ S * ∑ d ∈ Finset.Icc 1 R, |c d| * (F (Int.fract ((d:ℝ)*t)) + F (1 - Int.fract ((d:ℝ)*t))) := by
    intro t ht
    have hrhs : 0 ≤ S * ∑ d ∈ Finset.Icc 1 R,
        |c d| * (F (Int.fract ((d:ℝ)*t)) + F (1 - Int.fract ((d:ℝ)*t))) :=
      mul_nonneg hS0 (Finset.sum_nonneg (fun d _ =>
        mul_nonneg (abs_nonneg _) (add_nonneg (hF0 _) (hF0 _))))
    by_cases hta : t ∈ ({t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q ∧ a≤q ∧ Nat.Coprime a q ∧
        |t-(a:ℝ)/(q:ℝ)| ≤ (Q:ℝ)/((q:ℝ)*(n:ℝ))}ᶜ)
    · rw [Set.indicator_of_mem hta]
      have hne : ∀ d ∈ Finset.Icc 1 R,
          ‖∑ j ∈ Finset.range (M d),
            (Complex.exp (((2*Real.pi*((d:ℝ)*t):ℝ):ℂ)*Complex.I))^(j+1)‖^2
          ≤ F (Int.fract ((d:ℝ)*t)) + F (1 - Int.fract ((d:ℝ)*t)) := by
        intro d hd
        rw [Finset.mem_Icc] at hd
        obtain ⟨hlo, hhi⟩ := pdml_range n Q d hn hd.1 (hd.2.trans hR) t ht.1.le ht.2 hta
        rw [hε] at hlo hhi
        have hfp : 0 < Int.fract ((d:ℝ)*t) := lt_trans hε0 hlo
        have h1 := pdml_geom ((d:ℝ)*t) (M d) hfp.ne'
        have h2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
        rw [one_div_pow] at h2
        have h3 := pdml_sin (Int.fract ((d:ℝ)*t)) hfp (by linarith)
        have e1 : F (Int.fract ((d:ℝ)*t)) = 1 / (4 * Int.fract ((d:ℝ)*t)^2) :=
          Set.indicator_of_mem (show Int.fract ((d:ℝ)*t) ∈ Set.Ioi ε from hlo) _
        have e2 : F (1 - Int.fract ((d:ℝ)*t)) = 1 / (4 * (1 - Int.fract ((d:ℝ)*t))^2) :=
          Set.indicator_of_mem (show 1 - Int.fract ((d:ℝ)*t) ∈ Set.Ioi ε from
            (by have h5 : ε < 1 - Int.fract ((d:ℝ)*t) := by linarith
                exact h5)) _
        rw [e1, e2]
        exact h2.trans h3
      have hnorm : ‖∑ d ∈ Finset.Icc 1 R, (c d:ℂ) * ∑ j ∈ Finset.range (M d),
          (Complex.exp (((2*Real.pi*((d:ℝ)*t):ℝ):ℂ)*Complex.I))^(j+1)‖
          ≤ ∑ d ∈ Finset.Icc 1 R, |c d| * ‖∑ j ∈ Finset.range (M d),
          (Complex.exp (((2*Real.pi*((d:ℝ)*t):ℝ):ℂ)*Complex.I))^(j+1)‖ := by
        refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun d _ => ?_))
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      have hsq := pow_le_pow_left₀ (norm_nonneg _) hnorm 2
      have hCS := Finset.sum_mul_sq_le_sq_mul_sq (Finset.Icc 1 R) (fun d => Real.sqrt |c d|)
        (fun d => Real.sqrt |c d| * ‖∑ j ∈ Finset.range (M d),
          (Complex.exp (((2*Real.pi*((d:ℝ)*t):ℝ):ℂ)*Complex.I))^(j+1)‖)
      have e3 : ∀ d, Real.sqrt |c d| * (Real.sqrt |c d| * ‖∑ j ∈ Finset.range (M d),
          (Complex.exp (((2*Real.pi*((d:ℝ)*t):ℝ):ℂ)*Complex.I))^(j+1)‖)
          = |c d| * ‖∑ j ∈ Finset.range (M d),
          (Complex.exp (((2*Real.pi*((d:ℝ)*t):ℝ):ℂ)*Complex.I))^(j+1)‖ := fun d => by
        rw [← mul_assoc, Real.mul_self_sqrt (abs_nonneg _)]
      have e4 : ∀ d, (Real.sqrt |c d|)^2 = |c d| := fun d => Real.sq_sqrt (abs_nonneg _)
      have e5 : ∀ d, (Real.sqrt |c d| * ‖∑ j ∈ Finset.range (M d),
          (Complex.exp (((2*Real.pi*((d:ℝ)*t):ℝ):ℂ)*Complex.I))^(j+1)‖)^2
          = |c d| * ‖∑ j ∈ Finset.range (M d),
          (Complex.exp (((2*Real.pi*((d:ℝ)*t):ℝ):ℂ)*Complex.I))^(j+1)‖^2 := fun d => by
        rw [mul_pow, e4]
      simp only [e3, e4, e5] at hCS
      refine hsq.trans (hCS.trans ?_)
      exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun d hd =>
        mul_le_mul_of_nonneg_left (hne d hd) (abs_nonneg _)) hS0
    · rw [Set.indicator_of_notMem hta]; exact hrhs
  have hint : ∀ d : ℕ, IntervalIntegrable (fun t : ℝ => F (Int.fract ((d:ℝ)*t))
      + F (1 - Int.fract ((d:ℝ)*t))) volume 0 1 := fun d => pdml_psi_ii ε hε0 d
  have hhint : Integrable (fun t : ℝ => S * ∑ d ∈ Finset.Icc 1 R,
      |c d| * (F (Int.fract ((d:ℝ)*t)) + F (1 - Int.fract ((d:ℝ)*t))))
      (volume.restrict (Set.Ioc (0:ℝ) 1)) := by
    have hterm : ∀ d ∈ Finset.Icc 1 R, Integrable (fun t : ℝ =>
        |c d| * (F (Int.fract ((d:ℝ)*t)) + F (1 - Int.fract ((d:ℝ)*t))))
        (volume.restrict (Set.Ioc (0:ℝ) 1)) := fun d _ =>
      Integrable.const_mul
        ((intervalIntegrable_iff_integrableOn_Ioc_of_le (zero_le_one : (0:ℝ) ≤ 1)).1 (hint d)) _
    exact Integrable.const_mul (integrable_finsetSum (f := fun (d : ℕ) (t : ℝ) =>
      |c d| * (F (Int.fract ((d:ℝ)*t)) + F (1 - Int.fract ((d:ℝ)*t)))) _ hterm) S
  have hcomp : ∫ t in (0:ℝ)..1, S * ∑ d ∈ Finset.Icc 1 R,
      |c d| * (F (Int.fract ((d:ℝ)*t)) + F (1 - Int.fract ((d:ℝ)*t)))
      ≤ S * (S * (1/(2*ε))) := by
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_finsetSum (fun d _ => (hint d).const_mul _)]
    simp_rw [intervalIntegral.integral_const_mul]
    apply mul_le_mul_of_nonneg_left _ hS0
    rw [hS, Finset.sum_mul]
    exact Finset.sum_le_sum fun d hd => mul_le_mul_of_nonneg_left
      (pdml_psi ε hε0 d (Finset.mem_Icc.1 hd).1) (abs_nonneg _)
  have key : 1/(2*ε) ≤ 2*Real.pi*(n:ℝ)/(Q:ℝ) := by
    have e : 1/(2*ε) = (n:ℝ)/(2*Q) := by rw [← hε]; field_simp
    rw [e, div_le_div_iff₀ (by positivity) (by positivity)]
    have := mul_pos hnR hQR
    nlinarith [Real.pi_gt_three]
  rw [intervalIntegral.integral_of_le zero_le_one]
  calc _ ≤ ∫ t in Set.Ioc (0:ℝ) 1, S * ∑ d ∈ Finset.Icc 1 R,
        |c d| * (F (Int.fract ((d:ℝ)*t)) + F (1 - Int.fract ((d:ℝ)*t))) :=
        integral_mono_of_nonneg
          (ae_of_all _ fun t => Set.indicator_nonneg (fun _ _ => by positivity) t)
          hhint ((ae_restrict_iff' measurableSet_Ioc).2 (ae_of_all _ fun t ht => hpt t ht))
    _ = ∫ t in (0:ℝ)..1, S * ∑ d ∈ Finset.Icc 1 R,
        |c d| * (F (Int.fract ((d:ℝ)*t)) + F (1 - Int.fract ((d:ℝ)*t))) :=
        (intervalIntegral.integral_of_le zero_le_one).symm
    _ ≤ S * (S * (1/(2*ε))) := hcomp
    _ ≤ _ := by
      have := mul_le_mul_of_nonneg_left key (sq_nonneg S)
      nlinarith

theorem Conjectures.Goldbach.PacketDivisorMixtureLeakage :
    let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let arcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (Q n:ℝ)/((q:ℝ)*(n:ℝ))}; let P := fun (d M : ℕ) (t : ℝ) => ∑ j ∈ Finset.range M, (E ((d:ℝ)*t))^(j+1); let m := fun (s : Set ℝ) (f : ℝ → ℝ) => intervalIntegral (s.indicator f) (0:ℝ) 1 MeasureTheory.volume; ∀ (n R : ℕ) (c : ℕ → ℝ) (M : ℕ → ℕ), 0<n → R ≤ Q n → m (arcs n)ᶜ (fun t => ‖∑ d ∈ Finset.Icc 1 R, (c d:ℂ)*P d (M d) t‖^2) ≤ (2*Real.pi*(n:ℝ)/(Q n:ℝ))*(∑ d ∈ Finset.Icc 1 R, |c d|)^2 := by
  intro E Q arcs P m n R c M hn hR
  have hQ : 1 ≤ (Nat.log 2 (n+2))^2 :=
    Nat.one_le_pow _ _ (Nat.log_pos (by norm_num) (by omega))
  exact pdml_main n R ((Nat.log 2 (n+2))^2) c M hn hQ hR
