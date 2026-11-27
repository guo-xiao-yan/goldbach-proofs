import Mathlib

private lemma pwgt_norm (y : ℝ) :
    ‖1 - Complex.exp (((2 * Real.pi * y : ℝ) : ℂ) * Complex.I)‖ = 2 * |Real.sin (Real.pi * y)| := by
  rw [norm_sub_rev, mul_comm _ Complex.I, Complex.norm_exp_I_mul_ofReal_sub_one, Real.norm_eq_abs,
    abs_mul]
  have : 2 * Real.pi * y / 2 = Real.pi * y := by ring
  rw [this]; simp

private lemma pwgt_sin_lb (y : ℝ) : 2 * |y - round y| ≤ |Real.sin (Real.pi * y)| := by
  have h1 : Real.pi * y = Real.pi * (y - round y) + (round y : ℤ) * Real.pi := by ring
  have h2 : |Real.sin (Real.pi * y)| = |Real.sin (Real.pi * (y - round y))| := by
    rw [h1, Real.sin_add_int_mul_pi, abs_mul]
    simp
  rw [h2]
  have hb := abs_sub_round y
  have hpi := Real.pi_pos
  have key : ∀ d : ℝ, 0 ≤ d → d ≤ 1 / 2 → 2 * d ≤ Real.sin (Real.pi * d) := by
    intro d hd hd2
    have := Real.mul_le_sin (x := Real.pi * d) (by positivity) (by nlinarith)
    have e : 2 / Real.pi * (Real.pi * d) = 2 * d := by field_simp
    linarith
  rcases le_total 0 (y - round y) with h | h
  · rw [abs_of_nonneg h, abs_of_nonneg (by have := key _ h (by rwa [abs_of_nonneg h] at hb); linarith)]
    exact key _ h (by rwa [abs_of_nonneg h] at hb)
  · have h' : 0 ≤ -(y - round y) := by linarith
    have hk := key _ h' (by rwa [abs_of_nonpos h] at hb)
    have e : Real.sin (Real.pi * (y - round y)) = - Real.sin (Real.pi * (-(y - round y))) := by
      rw [← Real.sin_neg]; ring_nf
    rw [abs_of_nonpos h, e, abs_neg, abs_of_nonneg (by linarith)]
    exact hk

private lemma pwgt_cont (c0 r : ℝ) (hr : 0 < r) :
    Continuous (fun t : ℝ => 1 / ((t - c0) ^ 2 + r ^ 2)) := by
  have hg : Continuous (fun t : ℝ => (t - c0) ^ 2 + r ^ 2) := by fun_prop
  have hne : ∀ x : ℝ, (x - c0) ^ 2 + r ^ 2 ≠ 0 := fun x => by positivity
  exact Continuous.div continuous_const hg hne

private lemma pwgt_int (c0 r : ℝ) (hr : 0 < r) :
    ∫ t in (0 : ℝ)..1, 1 / ((t - c0) ^ 2 + r ^ 2) ≤ Real.pi / r := by
  have hd : ∀ x ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt (fun t : ℝ => (1 / r) * Real.arctan ((t - c0) / r)) (1 / ((x - c0) ^ 2 + r ^ 2)) x := by
    intro x _
    have h1 : HasDerivAt (fun t : ℝ => (t - c0) / r) (1 / r) x := by
      simpa using ((hasDerivAt_id x).sub_const c0).div_const r
    have h2 := (h1.arctan).const_mul (1 / r)
    convert h2 using 1
    field_simp
    ring
  have hi : IntervalIntegrable (fun t : ℝ => 1 / ((t - c0) ^ 2 + r ^ 2)) MeasureTheory.volume 0 1 := by
    exact (pwgt_cont c0 r hr).intervalIntegrable _ _
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi]
  have a1 := Real.arctan_lt_pi_div_two ((1 - c0) / r)
  have a2 := Real.neg_pi_div_two_lt_arctan ((0 - c0) / r)
  have : 0 < 1 / r := by positivity
  have e : Real.pi / r = (1 / r) * Real.pi := by ring
  rw [e, ← mul_sub]
  exact mul_le_mul_of_nonneg_left (by linarith) this.le

theorem Conjectures.Goldbach.PacketWheelGridTail :
    let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let arcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (Q n:ℝ)/((q:ℝ)*(n:ℝ))}; let D := fun (n : ℕ) (t : ℝ) => ((n:ℝ)+1)^2/(1+((n:ℝ)+1)^2*‖E (30*t)-1‖^2); ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, intervalIntegral ((arcs n)ᶜ.indicator (D n)) (0:ℝ) 1 MeasureTheory.volume ≤ ε*(n:ℝ) := by
  intro E Q arcs D ε hε
  set K : ℕ := ⌈1 / ε⌉₊ + 30 with hK
  refine ⟨2 ^ K, fun n hn => ?_⟩
  have hn1 : 1 ≤ n := le_trans (Nat.one_le_two_pow) hn
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hlog : K ≤ Nat.log 2 (n + 2) := Nat.le_log_of_pow_le (by norm_num) (by omega)
  have hQK : K ≤ Q n := by
    show K ≤ (Nat.log 2 (n + 2)) ^ 2
    nlinarith
  have hQ30 : 30 ≤ Q n := by omega
  have hQe : 1 / ε ≤ (Q n : ℝ) := by
    have h1 : 1 / ε ≤ (⌈1 / ε⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : (K : ℝ) ≤ (Q n : ℝ) := by exact_mod_cast hQK
    have h3 : (⌈1 / ε⌉₊ : ℝ) ≤ K := by rw [hK]; push_cast; linarith
    linarith
  have hQpos : (0 : ℝ) < Q n := by
    have : (30 : ℝ) ≤ Q n := by exact_mod_cast hQ30
    linarith
  set r : ℝ := (Q n : ℝ) / (30 * n) with hr
  have hrpos : 0 < r := by positivity
  set G : ℝ → ℝ := fun t => ∑ j ∈ Finset.range 31, (2 / 14400) * (1 / ((t - (j : ℝ) / 30) ^ 2 + r ^ 2)) with hG
  have hpt : ∀ t ∈ Set.Icc (0 : ℝ) 1, (arcs n)ᶜ.indicator (D n) t ≤ G t := by
    intro t ht
    have hGnn : 0 ≤ G t := by
      apply Finset.sum_nonneg; intro j _; positivity
    by_cases hta : t ∈ arcs n
    · rw [Set.indicator_of_notMem (by simpa using hta)]
      exact hGnn
    · rw [Set.indicator_of_mem (by simpa using hta)]
      set y : ℝ := 30 * t with hy
      have hk0 : 0 ≤ round y := by
        rw [round_eq]; apply Int.floor_nonneg.mpr; rw [hy]; linarith [ht.1]
      have hk30 : round y ≤ 30 := by
        rw [round_eq]
        have : ⌊y + 1 / 2⌋ < 31 := by
          rw [Int.floor_lt]; push_cast; rw [hy]; linarith [ht.2]
        omega
      set j : ℕ := (round y).toNat with hj
      have hjk : (j : ℤ) = round y := by rw [hj]; exact Int.toNat_of_nonneg hk0
      have hjR : (j : ℝ) = (round y : ℝ) := by exact_mod_cast hjk
      have hj30 : j ≤ 30 := by omega
      set u : ℝ := t - (j : ℝ) / 30 with hu
      have hyu : y - round y = 30 * u := by rw [hy, hu, ← hjR]; ring
      -- not in arcs gives |u| > r
      have hur : r < |u| := by
        by_contra hcon
        rw [not_lt] at hcon
        apply hta
        obtain ⟨a', q', hco, h1, h2⟩ := Nat.exists_coprime j 30
        have hg : 0 < Nat.gcd j 30 := Nat.gcd_pos_of_pos_right _ (by norm_num)
        have hq1 : 1 ≤ q' := by
          rcases Nat.eq_zero_or_pos q' with h | h
          · rw [h] at h2; omega
          · exact h
        have hq30 : q' ≤ 30 := by
          rw [h2]; exact Nat.le_mul_of_pos_right _ hg
        have ha : a' ≤ q' := by
          have : a' * Nat.gcd j 30 ≤ q' * Nat.gcd j 30 := by rw [← h1, ← h2]; exact hj30
          exact Nat.le_of_mul_le_mul_right this hg
        refine ⟨q', a', hq1, le_trans hq30 hQ30, ha, hco, ?_⟩
        have hq'R : (1 : ℝ) ≤ q' := by exact_mod_cast hq1
        have hq30R : (q' : ℝ) ≤ 30 := by exact_mod_cast hq30
        have heq : (a' : ℝ) / q' = (j : ℝ) / 30 := by
          have h1' : (j : ℝ) = a' * (Nat.gcd j 30 : ℕ) := by exact_mod_cast h1
          have h2' : (30 : ℝ) = q' * (Nat.gcd j 30 : ℕ) := by exact_mod_cast h2
          have hgR : (0 : ℝ) < (Nat.gcd j 30 : ℕ) := by exact_mod_cast hg
          rw [div_eq_div_iff (by positivity) (by norm_num), h1', h2']
          ring
        rw [heq]
        calc |t - (j : ℝ) / 30| = |u| := rfl
          _ ≤ r := hcon
          _ ≤ (Q n : ℝ) / ((q' : ℝ) * (n : ℝ)) := by
            rw [hr]
            apply div_le_div_of_nonneg_left hQpos.le (by positivity)
            nlinarith
      have hu2 : r ^ 2 < u ^ 2 := by
        have := sq_lt_sq' (by linarith [abs_nonneg u, neg_abs_le u]) (abs_lt.mp (show |u| < |u| + 1 by linarith) |>.2) 
        nlinarith [sq_abs u, abs_nonneg u]
      have hnorm : ‖E (30 * t) - 1‖ = 2 * |Real.sin (Real.pi * y)| := by
        rw [norm_sub_rev]; exact pwgt_norm y
      have hlb : 4 * |y - round y| ≤ ‖E (30 * t) - 1‖ := by
        rw [hnorm]; linarith [pwgt_sin_lb y]
      have hδ : 14400 * u ^ 2 ≤ ‖E (30 * t) - 1‖ ^ 2 := by
        have h0 : 0 ≤ 4 * |y - round y| := by positivity
        have := pow_le_pow_left₀ h0 hlb 2
        have e : (4 * |y - round y|) ^ 2 = 14400 * u ^ 2 := by
          rw [mul_pow, sq_abs, hyu]; ring
        linarith
      have hupos : 0 < u ^ 2 := lt_of_le_of_lt (by positivity) hu2
      have hMpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      have hDle : D n t ≤ 1 / (14400 * u ^ 2) := by
        show ((n : ℝ) + 1) ^ 2 / (1 + ((n : ℝ) + 1) ^ 2 * ‖E (30 * t) - 1‖ ^ 2) ≤ _
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        have := mul_le_mul_of_nonneg_left hδ (sq_nonneg ((n : ℝ) + 1))
        nlinarith [sq_nonneg ((n : ℝ) + 1)]
      have hterm : 1 / (14400 * u ^ 2) ≤ (2 / 14400) * (1 / (u ^ 2 + r ^ 2)) := by
        rw [div_mul_div_comm, div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith
      have hmem : j ∈ Finset.range 31 := Finset.mem_range.mpr (by omega)
      have hsingle := Finset.single_le_sum (f := fun j : ℕ => (2 / 14400 : ℝ) * (1 / ((t - (j : ℝ) / 30) ^ 2 + r ^ 2)))
        (fun i _ => by positivity) hmem
      exact hDle.trans (hterm.trans hsingle)
  by_cases hint : IntervalIntegrable ((arcs n)ᶜ.indicator (D n)) MeasureTheory.volume 0 1
  · have hGi : IntervalIntegrable G MeasureTheory.volume 0 1 := by
      apply Continuous.intervalIntegrable
      apply continuous_finsetSum; intro j _
      exact Continuous.mul continuous_const (pwgt_cont _ r hrpos)
    have h1 := intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ) ≤ 1) hint hGi hpt
    refine h1.trans ?_
    have h2 : ∫ t in (0 : ℝ)..1, G t ≤ ∑ j ∈ Finset.range 31, (2 / 14400) * (Real.pi / r) := by
      rw [hG]
      rw [intervalIntegral.integral_finsetSum]
      · apply Finset.sum_le_sum
        intro j _
        rw [intervalIntegral.integral_const_mul]
        exact mul_le_mul_of_nonneg_left (pwgt_int _ r hrpos) (by norm_num)
      · intro j _
        apply Continuous.intervalIntegrable
        exact Continuous.mul continuous_const (pwgt_cont _ r hrpos)
    refine h2.trans ?_
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have hpi : Real.pi ≤ 4 := Real.pi_le_four
    have e : Real.pi / r = Real.pi * (30 * n) / Q n := by rw [hr]; field_simp
    rw [e]
    have hεQ : 1 ≤ ε * Q n := by
      have := mul_le_mul_of_nonneg_left hQe hε.le
      rwa [mul_one_div_cancel hε.ne'] at this
    have hb : Real.pi * (30 * n) / Q n ≤ 120 * n * ε := by
      rw [div_le_iff₀ hQpos]
      have hn0 : (0 : ℝ) ≤ n := by positivity
      nlinarith [mul_le_mul_of_nonneg_left hεQ hn0, Real.pi_pos]
    have hnε : 0 ≤ ε * n := by positivity
    push_cast
    nlinarith
  · rw [intervalIntegral.integral_undef hint]
    positivity
