import Mathlib

private lemma sj_term_norm {K : Type} [NontriviallyNormedField K] (r u : K) (m : ℤ)
    (hr : 0 < ‖r‖) (hu : ‖u‖ = ‖r‖ ^ m) (n : ℤ) :
    ‖(r ^ 14) ^ (n * (n + 1) / 2) * u ^ (2 * n + 1)‖
      = ‖r‖ ^ (7 * (n * (n + 1)) + m * (2 * n + 1)) := by
  have h2 : 2 * (n * (n + 1) / 2) = n * (n + 1) :=
    Int.mul_ediv_cancel' (even_iff_two_dvd.mp (Int.even_mul_succ_self n))
  have e1 : ‖(r ^ 14)‖ = ‖r‖ ^ (14 : ℤ) := by
    rw [norm_pow]; norm_cast
  rw [norm_mul, norm_zpow, norm_zpow, hu, e1, ← zpow_mul, ← zpow_mul, ← zpow_add₀ hr.ne']
  congr 1
  linarith

private lemma sj_natAbs_tendsto : Filter.Tendsto (fun n : ℤ => n.natAbs) Filter.cofinite Filter.atTop := by
  rw [Filter.tendsto_atTop]
  intro b
  rw [Filter.eventually_cofinite]
  refine (Set.finite_Icc (-(b : ℤ)) b).subset ?_
  intro n hn
  simp only [Set.mem_ofPred_eq, not_le] at hn
  simp only [Set.mem_Icc]
  omega

private lemma sj_summable {K : Type} [NontriviallyNormedField K] [CompleteSpace K]
    [IsUltrametricDist K] (r u : K) (m : ℤ) (hm0 : 0 ≤ m) (hm2 : m ≤ 2)
    (hr0 : 0 < ‖r‖) (hr1 : ‖r‖ < 1) (hu : ‖u‖ = ‖r‖ ^ m) :
    Summable (fun n : ℤ => (r ^ 14) ^ (n * (n + 1) / 2) * u ^ (2 * n + 1)) := by
  apply NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hb : ∀ n : ℤ, ((n.natAbs : ℤ) - 3) ≤ 7 * (n * (n + 1)) + m * (2 * n + 1) := by
    intro n
    rcases le_or_gt 0 n with h | h
    · have : (n.natAbs : ℤ) = n := Int.natAbs_of_nonneg h
      rw [this]; nlinarith
    · have : (n.natAbs : ℤ) = -n := by omega
      rw [this]; nlinarith
  have hT : Filter.Tendsto (fun n : ℤ => ‖r‖ ^ n.natAbs / ‖r‖ ^ 3) Filter.cofinite (nhds 0) := by
    have := ((tendsto_pow_atTop_nhds_zero_of_lt_one hr0.le hr1).comp sj_natAbs_tendsto).div_const (‖r‖ ^ 3)
    simpa using this
  refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hT
  rw [sj_term_norm r u m hr0 hu n]
  calc ‖r‖ ^ (7 * (n * (n + 1)) + m * (2 * n + 1))
      ≤ ‖r‖ ^ ((n.natAbs : ℤ) - 3) :=
        zpow_le_zpow_right_of_le_one₀ hr0 hr1.le (hb n)
    _ = ‖r‖ ^ n.natAbs / ‖r‖ ^ 3 := by
        rw [zpow_sub₀ hr0.ne']; norm_cast

private lemma sj_tail {K : Type} [NontriviallyNormedField K] [CompleteSpace K]
    [IsUltrametricDist K] (r u : K) (m B : ℤ) (hm0 : 0 ≤ m) (hm2 : m ≤ 2)
    (hr0 : 0 < ‖r‖) (hr1 : ‖r‖ < 1) (hu : ‖u‖ = ‖r‖ ^ m)
    (hB : ∀ n : ℤ, n ≠ 0 → n ≠ -1 → B ≤ 7 * (n * (n + 1)) + m * (2 * n + 1)) :
    ‖(∑' n : ℤ, (r ^ 14) ^ (n * (n + 1) / 2) * u ^ (2 * n + 1)) - (u + u⁻¹)‖ ≤ ‖r‖ ^ B := by
  have hs := sj_summable r u m hm0 hm2 hr0 hr1 hu
  have hsplit := hs.sum_add_tsum_compl (s := ({0, -1} : Finset ℤ))
  have hfin : ∑ n ∈ ({0, -1} : Finset ℤ), (r ^ 14) ^ (n * (n + 1) / 2) * u ^ (2 * n + 1) = u + u⁻¹ := by
    rw [Finset.sum_pair (by norm_num)]
    simp
  rw [← hsplit, hfin, add_sub_cancel_left]
  apply IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg (by positivity)
  rintro ⟨n, hn⟩
  simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_compl_iff, Set.mem_insert_iff,
    Set.mem_singleton_iff, not_or] at hn
  show ‖(r ^ 14) ^ (n * (n + 1) / 2) * u ^ (2 * n + 1)‖ ≤ _
  rw [sj_term_norm r u m hr0 hu n]
  exact zpow_le_zpow_right_of_le_one₀ hr0 hr1.le (hB n hn.1 hn.2)

theorem Conjectures.JoshiAbc.SingleJet :
    ∀ (K : Type) [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K] [CharZero K], let theta := fun (q u : K) => ∑' n : ℤ, q^(n*(n+1)/2) * u^(2*n+1); ∀ (r z : K), r^14=(29:K) → 0 < ‖r‖ → ‖r‖ < 1 → z^7=1 → ‖z‖=1 → ‖1+z^2‖=1 → ‖theta (r^14) z / theta (r^14) (r^2*z) - (1+z^2)*r^2‖ ≤ ‖r‖^4 := by
  intro K _ _ _ _ theta r z _ hr0 hr1 _ hz hz2
  have hrne : r ≠ 0 := norm_pos_iff.mp hr0
  have hzne : z ≠ 0 := norm_pos_iff.mp (by rw [hz]; norm_num)
  have hz' : ‖z‖ = ‖r‖ ^ (0 : ℤ) := by rw [hz]; simp
  have hu : ‖r ^ 2 * z‖ = ‖r‖ ^ (2 : ℤ) := by
    rw [norm_mul, norm_pow, hz]; norm_cast; ring
  have hT1 := sj_tail r z 0 14 le_rfl (by norm_num) hr0 hr1 hz' (by
    intro n h0 h1
    rcases le_or_gt 1 n with h | h
    · nlinarith
    · have : n ≤ -2 := by omega
      nlinarith)
  have hT2 := sj_tail r (r ^ 2 * z) 2 8 (by norm_num) le_rfl hr0 hr1 hu (by
    intro n h0 h1
    rcases le_or_gt 1 n with h | h
    · nlinarith
    · have : n ≤ -2 := by omega
      nlinarith)
  show ‖(∑' n : ℤ, (r ^ 14) ^ (n * (n + 1) / 2) * z ^ (2 * n + 1)) /
      (∑' n : ℤ, (r ^ 14) ^ (n * (n + 1) / 2) * (r ^ 2 * z) ^ (2 * n + 1)) - (1 + z ^ 2) * r ^ 2‖ ≤ ‖r‖ ^ 4
  generalize (∑' n : ℤ, (r ^ 14) ^ (n * (n + 1) / 2) * z ^ (2 * n + 1)) = N at hT1 ⊢
  generalize (∑' n : ℤ, (r ^ 14) ^ (n * (n + 1) / 2) * (r ^ 2 * z) ^ (2 * n + 1)) = D at hT2 ⊢
  set a := ‖r‖ with ha
  have ha0 : 0 ≤ a := hr0.le
  have p14 : a ^ (14 : ℤ) = a ^ 14 := by norm_cast
  have p8 : a ^ (8 : ℤ) = a ^ 8 := by norm_cast
  rw [p14] at hT1
  rw [p8] at hT2
  set T1 := N - (z + z⁻¹) with hT1d
  set T2 := D - (r ^ 2 * z + (r ^ 2 * z)⁻¹) with hT2d
  set w := r ^ 4 * z ^ 2 + r ^ 2 * z * T2 with hw
  have hwn : ‖w‖ ≤ a ^ 4 := by
    have e1 : ‖r ^ 4 * z ^ 2‖ = a ^ 4 := by rw [norm_mul, norm_pow, norm_pow, hz, one_pow, mul_one]
    have e2 : ‖r ^ 2 * z * T2‖ ≤ a ^ 4 := by
      rw [norm_mul, hu]
      have : (a : ℝ) ^ (2 : ℤ) = a ^ 2 := by norm_cast
      rw [this]
      calc a ^ 2 * ‖T2‖ ≤ a ^ 2 * a ^ 8 := by gcongr
        _ ≤ a ^ 4 := by
          have : a ^ 2 * a ^ 8 = a ^ 4 * a ^ 6 := by ring
          rw [this]
          have : a ^ 6 ≤ 1 := pow_le_one₀ ha0 hr1.le
          nlinarith [pow_nonneg ha0 4]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le e1.le e2)
  have ha4 : a ^ 4 < 1 := pow_lt_one₀ ha0 hr1 (by norm_num)
  have hDeq : D = (r ^ 2 * z)⁻¹ * (1 + w) := by
    have : D = (r ^ 2 * z + (r ^ 2 * z)⁻¹) + T2 := by rw [hT2d]; ring
    rw [this, hw]
    field_simp
    ring
  have h1w : ‖1 + w‖ = 1 := by
    have : ‖w‖ ≠ ‖(1:K)‖ := by rw [norm_one]; exact (lt_of_le_of_lt hwn ha4).ne
    rw [add_comm, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm this, norm_one]
    exact max_eq_right (by rw [norm_one] at this; exact (lt_of_le_of_lt hwn ha4).le)
  have hDn : ‖D‖ = (a ^ 2)⁻¹ := by
    rw [hDeq, norm_mul, h1w, norm_inv, hu]; norm_cast; simp
  have hDne : D ≠ 0 := by
    intro h; rw [h, norm_zero] at hDn
    have : (0:ℝ) < (a ^ 2)⁻¹ := by positivity
    linarith
  have hnum : N - (1 + z ^ 2) * r ^ 2 * D = T1 - (1 + z ^ 2) * z⁻¹ * w := by
    rw [hDeq, hT1d, hw]
    field_simp
    ring
  have hX : ‖N - (1 + z ^ 2) * r ^ 2 * D‖ ≤ a ^ 4 := by
    rw [hnum, sub_eq_add_neg]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · calc ‖T1‖ ≤ a ^ 14 := hT1
        _ ≤ a ^ 4 := pow_le_pow_of_le_one ha0 hr1.le (by norm_num)
    · rw [norm_neg, norm_mul, norm_mul, norm_inv, hz, hz2]; simpa using hwn
  have : N / D - (1 + z ^ 2) * r ^ 2 = (N - (1 + z ^ 2) * r ^ 2 * D) / D := by
    field_simp
  rw [this, norm_div, hDn, div_inv_eq_mul]
  calc ‖N - (1 + z ^ 2) * r ^ 2 * D‖ * a ^ 2 ≤ a ^ 4 * a ^ 2 := by gcongr
    _ ≤ a ^ 4 * 1 := by
        have : a ^ 2 ≤ 1 := pow_le_one₀ ha0 hr1.le
        gcongr
    _ = a ^ 4 := mul_one _
