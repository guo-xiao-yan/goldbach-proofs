import Mathlib

private lemma exp_int_integral (m : ℤ) :
    ∫ t in (0:ℝ)..1, Complex.exp (((2*Real.pi*((m:ℝ)*t):ℝ):ℂ)*Complex.I) = if m = 0 then 1 else 0 := by
  by_cases hm : m = 0
  · subst hm; simp
  · rw [if_neg hm]
    have hc : (2*Real.pi*(m:ℂ)*Complex.I) ≠ 0 := by
      simp [Real.pi_ne_zero, hm]
    have : ∀ t:ℝ, Complex.exp (((2*Real.pi*((m:ℝ)*t):ℝ):ℂ)*Complex.I) = Complex.exp ((2*Real.pi*(m:ℂ)*Complex.I) * (t:ℂ)) := by
      intro t; congr 1; push_cast; ring
    simp_rw [this]
    rw [integral_exp_mul_complex hc]
    have h1 : Complex.exp ((2*Real.pi*(m:ℂ)*Complex.I) * ((1:ℝ):ℂ)) = 1 := by
      simp only [Complex.ofReal_one, mul_one]
      have := Complex.exp_int_mul_two_pi_mul_I m
      rw [← this]; congr 1; ring
    rw [h1]; simp

private lemma arcs_meas (Q n : ℕ) :
    MeasurableSet {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (Q:ℝ)/((q:ℝ)*(n:ℝ))} := by
  have : {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (Q:ℝ)/((q:ℝ)*(n:ℝ))}
      = ⋃ q : ℕ, ⋃ a : ℕ, ⋃ _ : (1≤q ∧ q≤Q ∧ a≤q ∧ Nat.Coprime a q), {t : ℝ | |t-(a:ℝ)/(q:ℝ)| ≤ (Q:ℝ)/((q:ℝ)*(n:ℝ))} := by
    ext t; simp only [Set.mem_setOf_eq, Set.mem_iUnion]
    constructor
    · rintro ⟨q, a, h1, h2, h3, h4, h5⟩; exact ⟨q, a, ⟨h1, h2, h3, h4⟩, h5⟩
    · rintro ⟨q, a, ⟨h1, h2, h3, h4⟩, h5⟩; exact ⟨q, a, h1, h2, h3, h4, h5⟩
  rw [this]
  refine MeasurableSet.iUnion fun q => MeasurableSet.iUnion fun a => MeasurableSet.iUnion fun _ => ?_
  exact measurableSet_le (by fun_prop) (by fun_prop)

private lemma sq_integral (a : ℕ → ℂ) (n : ℕ) :
    ∫ t in (0:ℝ)..1, (∑ k ∈ Finset.range (n+1), a k * Complex.exp (((2*Real.pi*((k:ℝ)*t):ℝ):ℂ)*Complex.I))^2
        * Complex.exp (((2*Real.pi*(-(n:ℝ)*t):ℝ):ℂ)*Complex.I)
      = ∑ j ∈ Finset.range (n+1), ∑ k ∈ Finset.range (n+1), a j * a k * (if j + k = n then 1 else 0) := by
  have key : ∀ t : ℝ, (∑ k ∈ Finset.range (n+1), a k * Complex.exp (((2*Real.pi*((k:ℝ)*t):ℝ):ℂ)*Complex.I))^2
        * Complex.exp (((2*Real.pi*(-(n:ℝ)*t):ℝ):ℂ)*Complex.I)
      = ∑ j ∈ Finset.range (n+1), ∑ k ∈ Finset.range (n+1), a j * a k *
          Complex.exp (((2*Real.pi*((((j:ℤ)+k-n : ℤ):ℝ)*t):ℝ):ℂ)*Complex.I) := by
    intro t
    rw [pow_two, Finset.sum_mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    have : Complex.exp (((2*Real.pi*((((j:ℤ)+k-n : ℤ):ℝ)*t):ℝ):ℂ)*Complex.I)
      = Complex.exp (((2*Real.pi*((j:ℝ)*t):ℝ):ℂ)*Complex.I) * Complex.exp (((2*Real.pi*((k:ℝ)*t):ℝ):ℂ)*Complex.I)
        * Complex.exp (((2*Real.pi*(-(n:ℝ)*t):ℝ):ℂ)*Complex.I) := by
      rw [← Complex.exp_add, ← Complex.exp_add]; congr 1; push_cast; ring
    rw [this]; ring
  simp_rw [key]
  rw [intervalIntegral.integral_finsetSum]
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [intervalIntegral.integral_finsetSum]
    · refine Finset.sum_congr rfl fun k _ => ?_
      rw [intervalIntegral.integral_const_mul, exp_int_integral]
      by_cases h : j + k = n
      · have : ((j:ℤ)+k-n) = 0 := by omega
        simp [h, this]
      · have : ((j:ℤ)+k-n) ≠ 0 := by omega
        simp [h, this]
    · intro k _
      apply Continuous.intervalIntegrable
      fun_prop
  · intro j _
    apply Continuous.intervalIntegrable
    fun_prop

theorem Conjectures.Goldbach.ExceptionFourSeventhsCountingBridge :
    let w := fun k : ℕ => if Nat.Prime k then Real.log (k:ℝ) else 0; let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let S := fun (n : ℕ) (w : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (w k:ℂ)*E ((k:ℝ)*t)); let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let arcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (Q n:ℝ)/((q:ℝ)*(n:ℝ))}; let f := fun (n : ℕ) (t : ℝ) => (S n w t)^2*E (-(n:ℝ)*t); let major := fun n : ℕ => intervalIntegral (fun t => (arcs n).indicator (f n) t) (0:ℝ) 1 MeasureTheory.volume; let minor := fun n : ℕ => (intervalIntegral (fun t => (arcs n)ᶜ.indicator (f n) t) (0:ℝ) 1 MeasureTheory.volume).re; let bad := fun n : ℕ => 4 ≤ n ∧ Even n ∧ ¬ ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p+q=n; (∃ (c : ℝ) (N : ℕ), 0<c ∧ ∀ n : ℕ, N≤n → Even n → c*(n:ℝ) ≤ (major n).re) → (∀ e : ℝ, 0 < e → ∃ (C : ℝ) (N : ℕ), 0 < C ∧ ∀ X : ℕ, N ≤ X → (Finset.sum ((Finset.Icc X (2*X)).filter Even) (fun n => (max 0 (-minor n))^2)) ≤ C * (X:ℝ) ^ (18/7 + e)) → (∀ e : ℝ, 0 < e → ∃ (C : ℝ) (N : ℕ), 0 < C ∧ ∀ X : ℕ, N ≤ X → ((@Finset.filter ℕ bad (Classical.decPred bad) (Finset.Icc X (2*X))).card : ℝ) ≤ C * (X:ℝ) ^ (4/7 + e)) := by
  classical
  intro w E S Q arcs f major minor bad hmaj hmin e he
  obtain ⟨c, N0, hc, hmaj'⟩ := hmaj
  obtain ⟨C, N1, hC, hmin'⟩ := hmin e he
  have hneg : ∀ n : ℕ, bad n → minor n = - (major n).re := by
    intro n hn
    have hcont : Continuous (f n) := by
      show Continuous (fun t : ℝ => (S n w t)^2*E (-(n:ℝ)*t))
      simp only [S, E]
      fun_prop
    have hm := arcs_meas (Q n) n
    have hI : ∀ s : Set ℝ, MeasurableSet s →
        IntervalIntegrable (fun t => s.indicator (f n) t) MeasureTheory.volume 0 1 := by
      intro s hs
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
      exact ((hcont.integrableOn_Icc (a := 0) (b := 1)).mono_set Set.Ioc_subset_Icc_self).indicator hs
    have hsum := intervalIntegral.integral_add (hI _ hm) (hI _ hm.compl)
    have htot : ∫ t in (0:ℝ)..1, f n t = 0 := by
      have h1 : ∀ t, f n t = (∑ k ∈ Finset.range (n+1), (w k : ℂ) * Complex.exp (((2*Real.pi*((k:ℝ)*t):ℝ):ℂ)*Complex.I))^2
        * Complex.exp (((2*Real.pi*(-(n:ℝ)*t):ℝ):ℂ)*Complex.I) := fun t => rfl
      simp_rw [h1]
      rw [sq_integral (fun k => (w k : ℂ)) n]
      refine Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun k _ => ?_
      by_cases h : j + k = n
      · have : (w j : ℂ) * (w k : ℂ) = 0 := by
          by_contra hne
          have hj : (w j : ℂ) ≠ 0 := left_ne_zero_of_mul hne
          have hk : (w k : ℂ) ≠ 0 := right_ne_zero_of_mul hne
          apply hn.2.2
          refine ⟨j, k, ?_, ?_, h⟩
          · by_contra hp; apply hj; simp [w, hp]
          · by_contra hp; apply hk; simp [w, hp]
        simp [this]
      · simp [h]
    have hsplit : ∀ t, (arcs n).indicator (f n) t + (arcs n)ᶜ.indicator (f n) t = f n t := by
      intro t; exact congrFun (Set.indicator_self_add_compl (arcs n) (f n)) t
    have hsum2 : ∫ t in (0:ℝ)..1, f n t = (∫ t in (0:ℝ)..1, (arcs n).indicator (f n) t) + ∫ t in (0:ℝ)..1, (arcs n)ᶜ.indicator (f n) t := by
      rw [← hsum]; exact intervalIntegral.integral_congr (fun t _ => (hsplit t).symm)
    clear hsum
    have hsum := hsum2
    rw [htot] at hsum
    have h3 := congrArg Complex.re hsum
    rw [Complex.add_re] at h3
    show (∫ t in (0:ℝ)..1, (arcs n)ᶜ.indicator (f n) t).re = -(∫ t in (0:ℝ)..1, (arcs n).indicator (f n) t).re
    simp only [Complex.zero_re] at h3
    linarith
  have hX : ∀ X : ℕ, max (max N0 N1) 1 ≤ X →
      ((@Finset.filter ℕ bad (Classical.decPred bad) (Finset.Icc X (2*X))).card : ℝ) * (c * X)^2 ≤ C * (X:ℝ) ^ (18/7 + e) := by
    intro X hX
    have hN0 : N0 ≤ X := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hX
    have hN1 : N1 ≤ X := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hX
    refine le_trans ?_ (hmin' X hN1)
    set B := @Finset.filter ℕ bad (Classical.decPred bad) (Finset.Icc X (2*X)) with hB
    calc (B.card : ℝ) * (c * X)^2 = ∑ n ∈ B, (c * X)^2 := by simp
      _ ≤ ∑ n ∈ B, (max 0 (-minor n))^2 := by
          refine Finset.sum_le_sum fun n hn => ?_
          obtain ⟨hn1, hbad⟩ := (@Finset.mem_filter ℕ bad (Classical.decPred bad) _ _).mp hn
          obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hn1
          have h4 := hmaj' n (le_trans hN0 h1) hbad.2.1
          have h5 : (X:ℝ) ≤ n := by exact_mod_cast h1
          have h6 : c * X ≤ max 0 (-minor n) := by
            refine le_trans ?_ (le_max_right _ _)
            rw [hneg n hbad]
            have : c * (X:ℝ) ≤ c * n := mul_le_mul_of_nonneg_left h5 hc.le
            linarith
          have h7 : 0 ≤ c * (X:ℝ) := by positivity
          exact pow_le_pow_left₀ h7 h6 2
      _ ≤ ∑ n ∈ (Finset.Icc X (2*X)).filter Even, (max 0 (-minor n))^2 := by
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun n _ _ => sq_nonneg _)
          intro n hn
          obtain ⟨hn1, hbad⟩ := (@Finset.mem_filter ℕ bad (Classical.decPred bad) _ _).mp hn
          exact Finset.mem_filter.mpr ⟨hn1, hbad.2.1⟩
  refine ⟨C / c^2, max (max N0 N1) 1, by positivity, fun X hXN => ?_⟩
  have hXpos : (0:ℝ) < X := by
    have : 1 ≤ X := le_trans (le_max_right _ _) hXN
    exact_mod_cast this
  have h := hX X hXN
  have hpow : (X:ℝ) ^ (18/7 + e) = (X:ℝ)^2 * (X:ℝ) ^ (4/7 + e) := by
    rw [show (18/7 + e : ℝ) = 2 + (4/7 + e) by ring, Real.rpow_add hXpos]
    norm_cast
  rw [hpow] at h
  have hcX : 0 < (c * X)^2 := by positivity
  rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
  nlinarith [h, hcX]
