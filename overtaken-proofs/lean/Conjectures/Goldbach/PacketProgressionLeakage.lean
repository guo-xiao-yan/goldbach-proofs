import Mathlib

open MeasureTheory Set

private noncomputable def tailA (δ K : ℝ) : ℝ → ℝ :=
  (Ioi δ).indicator (fun s => K * s ^ (-2 : ℝ))

private lemma tailA_int (δ K : ℝ) (hδ : 0 < δ) :
    Integrable (tailA δ K) ∧ ∫ s, tailA δ K s = K / δ := by
  have hi : IntegrableOn (fun s : ℝ => K * s ^ (-2 : ℝ)) (Ioi δ) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num) hδ).const_mul K
  refine ⟨(integrable_indicator_iff measurableSet_Ioi).2 hi, ?_⟩
  unfold tailA
  rw [integral_indicator measurableSet_Ioi, integral_const_mul,
    integral_Ioi_rpow_of_lt (by norm_num) hδ]
  have : δ ^ ((-2 : ℝ) + 1) = δ⁻¹ := by
    rw [show (-2 : ℝ) + 1 = -1 by norm_num, Real.rpow_neg_one]
  rw [this]; field_simp; ring

private lemma tailA_nonneg (δ K : ℝ) (hδ : 0 < δ) (hK : 0 ≤ K) (s : ℝ) : 0 ≤ tailA δ K s := by
  unfold tailA
  apply Set.indicator_nonneg
  intro x hx
  have : 0 < x := lt_trans hδ hx
  positivity

private lemma tailG_int (δ K c : ℝ) (hδ : 0 < δ) :
    Integrable (fun t => tailA δ K (t - c) + tailA δ K (c - t)) ∧
    ∫ t, (tailA δ K (t - c) + tailA δ K (c - t)) = 2 * (K / δ) := by
  obtain ⟨h1, h2⟩ := tailA_int δ K hδ
  have i1 : Integrable (fun t => tailA δ K (t - c)) := h1.comp_sub_right c
  have i2 : Integrable (fun t => tailA δ K (c - t)) := h1.comp_sub_left c
  refine ⟨i1.add i2, ?_⟩
  rw [integral_add i1 i2, integral_sub_right_eq_self (tailA δ K) c,
    integral_sub_left_eq_self (tailA δ K) volume c, h2]
  ring

private lemma sin_lb (y : ℝ) (hy : |y| ≤ 1 / 2) : 2 * |y| ≤ |Real.sin (Real.pi * y)| := by
  have h := Real.mul_le_sin (x := Real.pi * |y|) (by positivity)
    (by have := Real.pi_pos; nlinarith [abs_nonneg y])
  have e : 2 / Real.pi * (Real.pi * |y|) = 2 * |y| := by
    field_simp
  rw [e] at h
  rcases le_total 0 y with h0 | h0
  · rw [abs_of_nonneg h0] at h ⊢
    exact h.trans (le_abs_self _)
  · rw [abs_of_nonpos h0] at h ⊢
    rw [← abs_neg, ← Real.sin_neg]
    have : -(Real.pi * y) = Real.pi * -y := by ring
    rw [this]
    exact h.trans (le_abs_self _)

private lemma packet_sq (d M : ℕ) (t : ℝ) (k : ℤ) (hy : |(d : ℝ) * t - k| ≤ 1 / 2)
    (hy0 : (d : ℝ) * t - k ≠ 0) :
    ‖∑ j ∈ Finset.range M,
      (Complex.exp (((2 * Real.pi * ((d : ℝ) * t) : ℝ) : ℂ) * Complex.I)) ^ (j + 1)‖ ^ 2
      ≤ 1 / (4 * ((d : ℝ) * t - k) ^ 2) := by
  set y : ℝ := (d : ℝ) * t - k with hydef
  set z : ℂ := Complex.exp (((2 * Real.pi * ((d : ℝ) * t) : ℝ) : ℂ) * Complex.I) with hz
  have hzn : ‖z‖ = 1 := by
    rw [hz, Complex.norm_exp_ofReal_mul_I]
  have hz1 : ‖z - 1‖ = 2 * |Real.sin (Real.pi * y)| := by
    have : z = Complex.exp (Complex.I * ((2 * Real.pi * ((d : ℝ) * t) : ℝ) : ℂ)) := by
      rw [hz, mul_comm]
    rw [this, Complex.norm_exp_I_mul_ofReal_sub_one, norm_mul]
    have e : 2 * Real.pi * ((d : ℝ) * t) / 2 = Real.pi * y + k * Real.pi := by
      rw [hydef]; ring
    rw [e, Real.sin_add_int_mul_pi]
    simp
  have hs : 2 * |y| ≤ |Real.sin (Real.pi * y)| := sin_lb y hy
  have hypos : 0 < |y| := abs_pos.2 hy0
  have hP : ‖∑ j ∈ Finset.range M, z ^ (j + 1)‖ * ‖z - 1‖ ≤ 2 := by
    have : (∑ j ∈ Finset.range M, z ^ (j + 1)) * (z - 1) = z * (z ^ M - 1) := by
      have h2 : ∑ j ∈ Finset.range M, z ^ (j + 1) = z * ∑ j ∈ Finset.range M, z ^ j := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun j _ => by ring)
      rw [h2, ← geom_sum_mul]
      ring
    rw [← norm_mul, this, norm_mul, hzn, one_mul]
    calc ‖z ^ M - 1‖ ≤ ‖z ^ M‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ ≤ 2 := by rw [norm_pow, hzn]; simp; norm_num
  rw [hz1] at hP
  have hN : ‖∑ j ∈ Finset.range M, z ^ (j + 1)‖ * (4 * |y|) ≤ 2 := by
    refine le_trans ?_ hP
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    linarith
  have hN2 : ‖∑ j ∈ Finset.range M, z ^ (j + 1)‖ ≤ 1 / (2 * |y|) := by
    rw [le_div_iff₀ (by positivity)]
    linarith
  calc ‖∑ j ∈ Finset.range M, z ^ (j + 1)‖ ^ 2 ≤ (1 / (2 * |y|)) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hN2 2
    _ = 1 / (4 * y ^ 2) := by
        rw [div_pow, mul_pow, ← sq_abs y]; norm_num

private lemma tailA_val (δ K s : ℝ) (hδ : 0 < δ) (hs : δ < |s|) :
    tailA δ K s + tailA δ K (-s) = K / s ^ 2 := by
  have h2 : (-s) ^ 2 = s ^ 2 := by ring
  rcases lt_abs.1 hs with h | h
  · have e1 : tailA δ K s = K * s ^ (-2 : ℝ) := by
      unfold tailA; rw [Set.indicator_of_mem (show s ∈ Ioi δ from h)]
    have e2 : tailA δ K (-s) = 0 := by
      unfold tailA; apply Set.indicator_of_notMem
      simp only [mem_Ioi, not_lt]; linarith
    rw [e1, e2, Real.rpow_neg (by linarith), Real.rpow_two]; ring
  · have e1 : tailA δ K (-s) = K * (-s) ^ (-2 : ℝ) := by
      unfold tailA; rw [Set.indicator_of_mem (show -s ∈ Ioi δ from h)]
    have e2 : tailA δ K s = 0 := by
      unfold tailA; apply Set.indicator_of_notMem
      simp only [mem_Ioi, not_lt]; linarith
    rw [e1, e2, Real.rpow_neg (by linarith), Real.rpow_two, h2]; ring

private lemma pt (n d M Qn : ℕ) (hn : 0 < n) (hd : 0 < d) (hQ1 : 1 ≤ Qn) (hdQ : d ≤ Qn)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1)
    (hnot : t ∉ {t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ Qn ∧ a ≤ q ∧ Nat.Coprime a q ∧
      |t - (a : ℝ) / (q : ℝ)| ≤ (Qn : ℝ) / ((q : ℝ) * (n : ℝ))}) :
    ‖∑ j ∈ Finset.range M,
      (Complex.exp (((2 * Real.pi * ((d : ℝ) * t) : ℝ) : ℂ) * Complex.I)) ^ (j + 1)‖ ^ 2
      ≤ ∑ k ∈ Finset.range (d + 1),
        (tailA ((Qn : ℝ) / ((d : ℝ) * (n : ℝ))) (1 / (4 * (d : ℝ) ^ 2)) (t - (k : ℝ) / (d : ℝ))
        + tailA ((Qn : ℝ) / ((d : ℝ) * (n : ℝ))) (1 / (4 * (d : ℝ) ^ 2)) ((k : ℝ) / (d : ℝ) - t)) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hQR : (0 : ℝ) < Qn := by exact_mod_cast hQ1
  set δ : ℝ := (Qn : ℝ) / ((d : ℝ) * (n : ℝ)) with hδdef
  set K : ℝ := 1 / (4 * (d : ℝ) ^ 2) with hKdef
  have hδ : 0 < δ := by positivity
  have hK : 0 ≤ K := by positivity
  obtain ⟨ht0, ht1⟩ := ht
  have hy := abs_sub_round ((d : ℝ) * t)
  set k : ℤ := round ((d : ℝ) * t) with hkdef
  have hy' := abs_le.1 hy
  have hdt0 : 0 ≤ (d : ℝ) * t := by positivity
  have hdt1 : (d : ℝ) * t ≤ d := by nlinarith
  have hk0 : 0 ≤ k := by
    by_contra h
    have : k ≤ -1 := by omega
    have : (k : ℝ) ≤ -1 := by exact_mod_cast this
    linarith [hy'.1, hy'.2]
  have hkd : k ≤ d := by
    by_contra h
    have : (d : ℤ) + 1 ≤ k := by omega
    have : (d : ℝ) + 1 ≤ k := by exact_mod_cast this
    linarith [hy'.1, hy'.2]
  obtain ⟨kn, hkn⟩ : ∃ kn : ℕ, (kn : ℤ) = k := ⟨k.toNat, Int.toNat_of_nonneg hk0⟩
  have hknd : kn ≤ d := by omega
  have hkR : (kn : ℝ) = (k : ℝ) := by rw [← hkn]; simp
  have hgd : Nat.gcd kn d ∣ d := Nat.gcd_dvd_right _ _
  have hg : 0 < Nat.gcd kn d := Nat.gcd_pos_of_pos_right _ hd
  have hq_mul : d / Nat.gcd kn d * Nat.gcd kn d = d := Nat.div_mul_cancel hgd
  have ha_mul : kn / Nat.gcd kn d * Nat.gcd kn d = kn := Nat.div_mul_cancel (Nat.gcd_dvd_left _ _)
  have hqpos : 0 < d / Nat.gcd kn d := Nat.div_pos (Nat.le_of_dvd hd hgd) hg
  have hcop : Nat.Coprime (kn / Nat.gcd kn d) (d / Nat.gcd kn d) := Nat.coprime_div_gcd_div_gcd hg
  have ha_le : kn / Nat.gcd kn d ≤ d / Nat.gcd kn d := Nat.div_le_div_right hknd
  have hq_le : d / Nat.gcd kn d ≤ d := Nat.div_le_self _ _
  set q := d / Nat.gcd kn d with hqdef
  set a := kn / Nat.gcd kn d with hadef
  have hqR : (0 : ℝ) < q := by exact_mod_cast hqpos
  have hc : (a : ℝ) / q = (kn : ℝ) / d := by
    have e1 : (kn : ℝ) = a * (Nat.gcd kn d : ℝ) := by exact_mod_cast ha_mul.symm
    have e2 : (d : ℝ) = q * (Nat.gcd kn d : ℝ) := by exact_mod_cast hq_mul.symm
    have hgR : (0 : ℝ) < (Nat.gcd kn d : ℝ) := by exact_mod_cast hg
    rw [e1, e2]; field_simp
  have hlt : (Qn : ℝ) / ((q : ℝ) * (n : ℝ)) < |t - (a : ℝ) / (q : ℝ)| := by
    by_contra h
    rw [not_lt] at h
    exact hnot ⟨q, a, hqpos, hq_le.trans hdQ, ha_le, hcop, h⟩
  have hδle : δ ≤ (Qn : ℝ) / ((q : ℝ) * (n : ℝ)) := by
    rw [hδdef]
    apply div_le_div_of_nonneg_left hQR.le (by positivity)
    have : (q : ℝ) ≤ d := by exact_mod_cast hq_le
    exact mul_le_mul_of_nonneg_right this hnR.le
  have hlt2 : δ < |t - (kn : ℝ) / d| := by rw [← hc]; exact lt_of_le_of_lt hδle hlt
  have hyeq : (d : ℝ) * t - k = d * (t - (kn : ℝ) / d) := by
    rw [← hkR]; field_simp
  have hy0 : (d : ℝ) * t - k ≠ 0 := by
    rw [hyeq]
    exact mul_ne_zero hdR.ne' (abs_pos.1 (lt_trans hδ hlt2))
  have hP := packet_sq d M t k hy hy0
  have hv := tailA_val δ K (t - (kn : ℝ) / d) hδ hlt2
  rw [neg_sub] at hv
  have hfin : 1 / (4 * ((d : ℝ) * t - k) ^ 2) = K / (t - (kn : ℝ) / d) ^ 2 := by
    have : t - (kn : ℝ) / d ≠ 0 := abs_pos.1 (lt_trans hδ hlt2)
    rw [hyeq, hKdef]; field_simp
  refine hP.trans ?_
  rw [hfin, ← hv]
  have hmem : kn ∈ Finset.range (d + 1) := Finset.mem_range.2 (by omega)
  exact Finset.single_le_sum (f := fun k : ℕ => tailA δ K (t - (k : ℝ) / d)
    + tailA δ K ((k : ℝ) / d - t))
    (fun i _ => add_nonneg (tailA_nonneg δ K hδ hK _) (tailA_nonneg δ K hδ hK _)) hmem

private lemma mainbound (n d M Qn : ℕ) (hn : 0 < n) (hd : 0 < d) (hQ1 : 1 ≤ Qn) (hdQ : d ≤ Qn) :
    intervalIntegral
      (({t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ Qn ∧ a ≤ q ∧ Nat.Coprime a q ∧
        |t - (a : ℝ) / (q : ℝ)| ≤ (Qn : ℝ) / ((q : ℝ) * (n : ℝ))}ᶜ).indicator
        (fun t => ‖∑ j ∈ Finset.range M,
      (Complex.exp (((2 * Real.pi * ((d : ℝ) * t) : ℝ) : ℂ) * Complex.I)) ^ (j + 1)‖ ^ 2))
      (0 : ℝ) 1 MeasureTheory.volume ≤ 2 * Real.pi * (n : ℝ) / (Qn : ℝ) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hQR : (0 : ℝ) < Qn := by exact_mod_cast hQ1
  set δ : ℝ := (Qn : ℝ) / ((d : ℝ) * (n : ℝ)) with hδdef
  set K : ℝ := 1 / (4 * (d : ℝ) ^ 2) with hKdef
  have hδ : 0 < δ := by positivity
  have hK : 0 ≤ K := by positivity
  set G : ℝ → ℝ := fun t => ∑ k ∈ Finset.range (d + 1),
    (tailA δ K (t - (k : ℝ) / (d : ℝ)) + tailA δ K ((k : ℝ) / (d : ℝ) - t)) with hG
  have hGi : Integrable G := by
    apply integrable_finsetSum
    intro k _
    exact (tailG_int δ K ((k : ℝ) / d) hδ).1
  have hGint : ∫ t, G t = ((d : ℝ) + 1) * (2 * (K / δ)) := by
    show ∫ t, ∑ k ∈ Finset.range (d + 1),
      (tailA δ K (t - (k : ℝ) / d) + tailA δ K ((k : ℝ) / d - t)) = _
    rw [integral_finsetSum (f := fun (k : ℕ) (t : ℝ) =>
      tailA δ K (t - (k : ℝ) / d) + tailA δ K ((k : ℝ) / d - t)) _ (fun k _ => (tailG_int δ K ((k : ℝ) / d) hδ).1)]
    have hc : ∀ k ∈ Finset.range (d + 1), ∫ t : ℝ,
        (tailA δ K (t - (k : ℝ) / d) + tailA δ K ((k : ℝ) / d - t)) = 2 * (K / δ) :=
      fun k _ => (tailG_int δ K ((k : ℝ) / d) hδ).2
    rw [Finset.sum_congr rfl hc]
    simp
  have hGnn : ∀ t, 0 ≤ G t := fun t =>
    Finset.sum_nonneg (fun i _ => add_nonneg (tailA_nonneg δ K hδ hK _) (tailA_nonneg δ K hδ hK _))
  rw [intervalIntegral.integral_of_le zero_le_one]
  calc _ ≤ ∫ t in Ioc (0 : ℝ) 1, G t := by
        apply integral_mono_of_nonneg
        · exact Filter.Eventually.of_forall (fun t => by
            apply Set.indicator_nonneg
            intro x _; positivity)
        · exact hGi.integrableOn
        · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
          by_cases hm : t ∈ ({t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ Qn ∧ a ≤ q ∧ Nat.Coprime a q ∧
            |t - (a : ℝ) / (q : ℝ)| ≤ (Qn : ℝ) / ((q : ℝ) * (n : ℝ))}ᶜ)
          · rw [Set.indicator_of_mem hm]
            exact pt n d M Qn hn hd hQ1 hdQ t ⟨ht.1.le, ht.2⟩ hm
          · rw [Set.indicator_of_notMem hm]; exact hGnn t
    _ ≤ ∫ t, G t := setIntegral_le_integral hGi (Filter.Eventually.of_forall hGnn)
    _ = ((d : ℝ) + 1) * (2 * (K / δ)) := hGint
    _ ≤ 2 * Real.pi * (n : ℝ) / (Qn : ℝ) := by
        have h1 : ((d : ℝ) + 1) / d ≤ 2 := by
          rw [div_le_iff₀ hdR]
          have : (1 : ℝ) ≤ d := by exact_mod_cast hd
          linarith
        have h2 : ((d : ℝ) + 1) * (2 * (K / δ)) ≤ 2 * ((n : ℝ) / Qn) := by
          rw [hKdef, hδdef]
          have : ((d : ℝ) + 1) * (2 * (1 / (4 * (d : ℝ) ^ 2) / ((Qn : ℝ) / ((d : ℝ) * (n : ℝ)))))
              = ((d : ℝ) + 1) / d * ((n : ℝ) / Qn) / 2 := by
            field_simp; ring
          rw [this]
          have h3 : 0 ≤ (n : ℝ) / Qn := by positivity
          nlinarith
        have h4 : 2 * ((n : ℝ) / Qn) ≤ 2 * Real.pi * (n : ℝ) / (Qn : ℝ) := by
          have := Real.pi_gt_three
          rw [mul_div_assoc, mul_assoc]
          have h3 : 0 ≤ (n : ℝ) / Qn := by positivity
          nlinarith
        exact h2.trans h4

theorem Conjectures.Goldbach.PacketProgressionLeakage :
    let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let arcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (Q n:ℝ)/((q:ℝ)*(n:ℝ))}; let P := fun (d M : ℕ) (t : ℝ) => ∑ j ∈ Finset.range M, (E ((d:ℝ)*t))^(j+1); let m := fun (s : Set ℝ) (f : ℝ → ℝ) => intervalIntegral (s.indicator f) (0:ℝ) 1 MeasureTheory.volume; ∀ n d M : ℕ, 0<n → 0<d → d ≤ Q n → m (arcs n)ᶜ (fun t => ‖P d M t‖^2) ≤ 2*Real.pi*(n:ℝ)/(Q n:ℝ) := by
  intro E Q arcs P m n d M hn hd hdQ
  have hQ1 : 1 ≤ Nat.log 2 (n + 2) ^ 2 := by
    have : 1 ≤ Nat.log 2 (n + 2) := Nat.le_log_of_pow_le (by norm_num) (by omega)
    exact Nat.one_le_pow _ _ this
  exact mainbound n d M _ hn hd hQ1 hdQ
