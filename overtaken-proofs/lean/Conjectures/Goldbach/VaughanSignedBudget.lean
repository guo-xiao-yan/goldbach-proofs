import Mathlib


private noncomputable def E (x : ℝ) : ℂ := Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)

private theorem E_add (x y : ℝ) : E (x + y) = E x * E y := by
  unfold E
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

private theorem E_norm (x : ℝ) : ‖E x‖ = 1 := by
  unfold E
  exact Complex.norm_exp_ofReal_mul_I _

private theorem E_neg (x : ℝ) : E (-x) = (starRingEnd ℂ) (E x) := by
  unfold E
  rw [← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I]
  congr 1
  push_cast
  ring

private theorem E_cont : Continuous E := by
  unfold E
  fun_prop

private theorem integral_E (m : ℤ) :
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

private theorem parseval (s : Finset ℕ) (d : ℕ → ℂ) :
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


private noncomputable def SS (n : ℕ) (u : ℕ → ℝ) (t : ℝ) : ℂ :=
  ∑ k ∈ Finset.range (n+1), (u k : ℂ) * E ((k : ℝ)*t)

private def QQ (n : ℕ) : ℕ := (Nat.log 2 (n+2))^2

private def AA (n : ℕ) : Set ℝ := {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤QQ n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (QQ n:ℝ)/((q:ℝ)*(n:ℝ))}

private noncomputable def BB (n : ℕ) (u v : ℕ → ℝ) : ℝ :=
  (intervalIntegral ((AA n)ᶜ.indicator (fun t => SS n u t * SS n v t * E (-(n : ℝ)*t))) (0:ℝ) 1 MeasureTheory.volume).re

private theorem SS_cont (n : ℕ) (u : ℕ → ℝ) : Continuous (SS n u) := by
  unfold SS
  exact continuous_finsetSum _ fun k _ => continuous_const.mul (E_cont.comp (by fun_prop))

private theorem SS_add (n : ℕ) (u v : ℕ → ℝ) (t : ℝ) :
    SS n (fun k => u k + v k) t = SS n u t + SS n v t := by
  unfold SS
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  push_cast
  ring

private theorem SS_sub (n : ℕ) (u v : ℕ → ℝ) (t : ℝ) :
    SS n (fun k => u k - v k) t = SS n u t - SS n v t := by
  unfold SS
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  push_cast
  ring

private theorem AA_meas (n : ℕ) : MeasurableSet (AA n) := by
  have : AA n = ⋃ q : ℕ, ⋃ a : ℕ, ⋃ (_ : 1≤q ∧ q≤QQ n ∧ a≤q ∧ Nat.Coprime a q),
      Metric.closedBall ((a:ℝ)/(q:ℝ)) ((QQ n:ℝ)/((q:ℝ)*(n:ℝ))) := by
    ext t
    simp only [AA, Set.mem_setOf_eq, Set.mem_iUnion, Metric.mem_closedBall, Real.dist_eq]
    constructor
    · rintro ⟨q, a, h1, h2, h3, h4, h5⟩
      exact ⟨q, a, ⟨h1, h2, h3, h4⟩, h5⟩
    · rintro ⟨q, a, ⟨h1, h2, h3, h4⟩, h5⟩
      exact ⟨q, a, h1, h2, h3, h4, h5⟩
  rw [this]
  exact MeasurableSet.iUnion fun q => MeasurableSet.iUnion fun a => MeasurableSet.iUnion fun _ =>
    Metric.isClosed_closedBall.measurableSet

private theorem ind_int (n : ℕ) (u v : ℕ → ℝ) :
    IntervalIntegrable ((AA n)ᶜ.indicator (fun t => SS n u t * SS n v t * E (-(n : ℝ)*t)))
      MeasureTheory.volume 0 1 := by
  have cF : Continuous (fun t : ℝ => SS n u t * SS n v t * E (-(n : ℝ)*t)) :=
    ((SS_cont n u).mul (SS_cont n v)).mul (E_cont.comp (by fun_prop))
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
  exact ((cF.intervalIntegrable 0 1).1).indicator (AA_meas n).compl

private theorem BB_add_left (n : ℕ) (u v w : ℕ → ℝ) :
    BB n (fun k => u k + v k) w = BB n u w + BB n v w := by
  unfold BB
  have : (AA n)ᶜ.indicator (fun t => SS n (fun k => u k + v k) t * SS n w t * E (-(n : ℝ)*t)) =
      fun t => (AA n)ᶜ.indicator (fun t => SS n u t * SS n w t * E (-(n : ℝ)*t)) t + (AA n)ᶜ.indicator (fun t => SS n v t * SS n w t * E (-(n : ℝ)*t)) t := by
    funext t
    by_cases h : t ∈ (AA n)ᶜ
    · simp only [Set.indicator_of_mem h]
      rw [SS_add]
      ring
    · simp only [Set.indicator_of_notMem h]
      simp
  rw [this, intervalIntegral.integral_add (ind_int n u w) (ind_int n v w), Complex.add_re]

private theorem BB_sub_left (n : ℕ) (u v w : ℕ → ℝ) :
    BB n (fun k => u k - v k) w = BB n u w - BB n v w := by
  unfold BB
  have : (AA n)ᶜ.indicator (fun t => SS n (fun k => u k - v k) t * SS n w t * E (-(n : ℝ)*t)) =
      fun t => (AA n)ᶜ.indicator (fun t => SS n u t * SS n w t * E (-(n : ℝ)*t)) t - (AA n)ᶜ.indicator (fun t => SS n v t * SS n w t * E (-(n : ℝ)*t)) t := by
    funext t
    by_cases h : t ∈ (AA n)ᶜ
    · simp only [Set.indicator_of_mem h]
      rw [SS_sub]
      ring
    · simp only [Set.indicator_of_notMem h]
      simp
  rw [this, intervalIntegral.integral_sub (ind_int n u w) (ind_int n v w), Complex.sub_re]

private theorem BB_sub_right (n : ℕ) (u v w : ℕ → ℝ) :
    BB n u (fun k => v k - w k) = BB n u v - BB n u w := by
  unfold BB
  have : (AA n)ᶜ.indicator (fun t => SS n u t * SS n (fun k => v k - w k) t * E (-(n : ℝ)*t)) =
      fun t => (AA n)ᶜ.indicator (fun t => SS n u t * SS n v t * E (-(n : ℝ)*t)) t - (AA n)ᶜ.indicator (fun t => SS n u t * SS n w t * E (-(n : ℝ)*t)) t := by
    funext t
    by_cases h : t ∈ (AA n)ᶜ
    · simp only [Set.indicator_of_mem h]
      rw [SS_sub]
      ring
    · simp only [Set.indicator_of_notMem h]
      simp
  rw [this, intervalIntegral.integral_sub (ind_int n u v) (ind_int n u w), Complex.sub_re]

private theorem SS_par (n : ℕ) (u : ℕ → ℝ) :
    ∫ t in (0:ℝ)..1, ‖SS n u t‖ ^ 2 = ∑ k ∈ Finset.range (n+1), (u k)^2 := by
  have := parseval (Finset.range (n+1)) (fun k => (u k : ℂ))
  simpa [SS] using this

private theorem BB_sq_le (n : ℕ) (u v : ℕ → ℝ) :
    (BB n u v)^2 ≤ (∑ k ∈ Finset.range (n+1), (u k)^2) * (∑ k ∈ Finset.range (n+1), (v k)^2) := by
  set U := ∑ k ∈ Finset.range (n+1), (u k)^2 with hU
  set V := ∑ k ∈ Finset.range (n+1), (v k)^2 with hV
  have hU0 : 0 ≤ U := Finset.sum_nonneg fun k _ => sq_nonneg _
  have hV0 : 0 ≤ V := Finset.sum_nonneg fun k _ => sq_nonneg _
  have h1 : |BB n u v| ≤ ∫ t in (0:ℝ)..1, ‖(AA n)ᶜ.indicator
      (fun t => SS n u t * SS n v t * E (-(n : ℝ)*t)) t‖ := by
    unfold BB
    exact (Complex.abs_re_le_norm _).trans (intervalIntegral.norm_integral_le_integral_norm zero_le_one)
  have key : ∀ l : ℝ, 0 ≤ U * (l * l) + (-2 * |BB n u v|) * l + V := by
    intro l
    by_cases hl : l ≤ 0
    · nlinarith [mul_nonneg hU0 (mul_self_nonneg l), mul_nonneg (abs_nonneg (BB n u v)) (neg_nonneg.2 hl)]
    · push_neg at hl
      have hint2 : IntervalIntegrable (fun t : ℝ => l^2 * ‖SS n u t‖ ^ 2 + ‖SS n v t‖ ^ 2)
          MeasureTheory.volume 0 1 :=
        ((continuous_const.mul ((SS_cont n u).norm.pow 2)).add ((SS_cont n v).norm.pow 2)).intervalIntegrable 0 1
      have hint3 : IntervalIntegrable (fun t : ℝ => 2 * l * ‖(AA n)ᶜ.indicator
          (fun t => SS n u t * SS n v t * E (-(n : ℝ)*t)) t‖) MeasureTheory.volume 0 1 :=
        ((ind_int n u v).norm).const_mul _
      have h2 : ∫ t in (0:ℝ)..1, 2 * l * ‖(AA n)ᶜ.indicator
          (fun t => SS n u t * SS n v t * E (-(n : ℝ)*t)) t‖ ≤
          ∫ t in (0:ℝ)..1, (l^2 * ‖SS n u t‖ ^ 2 + ‖SS n v t‖ ^ 2) := by
        refine intervalIntegral.integral_mono_on zero_le_one hint3 hint2 ?_
        intro t _
        have h3 := norm_indicator_le_norm_self (s := (AA n)ᶜ)
          (f := fun t => SS n u t * SS n v t * E (-(n : ℝ)*t)) (a := t)
        rw [norm_mul, norm_mul, E_norm, mul_one] at h3
        nlinarith [sq_nonneg (l * ‖SS n u t‖ - ‖SS n v t‖)]
      have hA1 : IntervalIntegrable (fun t : ℝ => l^2 * ‖SS n u t‖ ^ 2) MeasureTheory.volume 0 1 :=
        (continuous_const.mul ((SS_cont n u).norm.pow 2)).intervalIntegrable 0 1
      have hB1 : IntervalIntegrable (fun t : ℝ => ‖SS n v t‖ ^ 2) MeasureTheory.volume 0 1 :=
        ((SS_cont n v).norm.pow 2).intervalIntegrable 0 1
      rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add hA1 hB1,
        intervalIntegral.integral_const_mul, SS_par, SS_par] at h2
      nlinarith
  have := discrim_le_zero key
  unfold discrim at this
  nlinarith [sq_abs (BB n u v)]

private noncomputable def wf (k : ℕ) : ℝ := if Nat.Prime k then Real.log (k : ℝ) else 0

private theorem vaughan_id (a b : ArithmeticFunction ℝ) :
    ArithmeticFunction.vonMangoldt =
      b + (a * ArithmeticFunction.log - a * b * (ArithmeticFunction.zeta : ArithmeticFunction ℝ))
        + ((ArithmeticFunction.moebius : ArithmeticFunction ℝ) - a) *
          ((ArithmeticFunction.vonMangoldt - b) * (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) := by
  have h1 : (ArithmeticFunction.vonMangoldt : ArithmeticFunction ℝ) *
      (ArithmeticFunction.zeta : ArithmeticFunction ℝ) = ArithmeticFunction.log :=
    ArithmeticFunction.vonMangoldt_mul_zeta
  have h2 : (ArithmeticFunction.moebius : ArithmeticFunction ℝ) *
      (ArithmeticFunction.zeta : ArithmeticFunction ℝ) = 1 :=
    ArithmeticFunction.coe_moebius_mul_coe_zeta
  linear_combination (a : ArithmeticFunction ℝ) * h1 - ((ArithmeticFunction.vonMangoldt : ArithmeticFunction ℝ) - b) * h2

private theorem sq_sum_le (n : ℕ) (g : ℕ → ℝ) (c : ℝ) (T : Finset ℕ)
    (hT : ∀ k ∈ Finset.range (n+1), g k ≠ 0 → k ∈ T)
    (hg : ∀ k ∈ Finset.range (n+1), |g k| ≤ c) :
    ∑ k ∈ Finset.range (n+1), (g k)^2 ≤ (T.card : ℝ) * c^2 := by
  have hsub : Finset.range (n+1) ∩ T ⊆ Finset.range (n+1) := Finset.inter_subset_left
  have h1 : ∑ k ∈ Finset.range (n+1) ∩ T, (g k)^2 = ∑ k ∈ Finset.range (n+1), (g k)^2 := by
    refine Finset.sum_subset hsub ?_
    intro k hk hkn
    have : g k = 0 := by
      by_contra hne
      exact hkn (Finset.mem_inter.2 ⟨hk, hT k hk hne⟩)
    simp [this]
  rw [← h1]
  calc ∑ k ∈ Finset.range (n+1) ∩ T, (g k)^2 ≤ ∑ k ∈ Finset.range (n+1) ∩ T, c^2 := by
        refine Finset.sum_le_sum fun k hk => ?_
        have := hg k (Finset.mem_inter.1 hk).1
        have h0 := abs_nonneg (g k)
        nlinarith [sq_abs (g k)]
    _ = ((Finset.range (n+1) ∩ T).card : ℝ) * c^2 := by simp
    _ ≤ (T.card : ℝ) * c^2 := by
        have : (Finset.range (n+1) ∩ T).card ≤ T.card := Finset.card_le_card Finset.inter_subset_right
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast this) (sq_nonneg c)

private theorem vm_abs_le (n k : ℕ) (hn : 1 ≤ n) (hk : k ≤ n) :
    |ArithmeticFunction.vonMangoldt k| ≤ Real.log (n : ℝ) := by
  rw [abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
  rcases Nat.eq_zero_or_pos k with h | h
  · subst h
    simp
    exact Real.log_nonneg (by exact_mod_cast hn)
  · exact ArithmeticFunction.vonMangoldt_le_log.trans
      (Real.log_le_log (by exact_mod_cast h) (by exact_mod_cast hk))

private theorem wf_abs_le (n k : ℕ) (hn : 1 ≤ n) (hk : k ≤ n) :
    |wf k| ≤ Real.log (n : ℝ) := by
  unfold wf
  split_ifs with hp
  · rw [abs_of_nonneg (Real.log_nonneg (by exact_mod_cast hp.one_lt.le))]
    exact Real.log_le_log (by exact_mod_cast hp.pos) (by exact_mod_cast hk)
  · simp
    exact Real.log_nonneg (by exact_mod_cast hn)

private theorem Lw_support (k : ℕ) (hk : ArithmeticFunction.vonMangoldt k - wf k ≠ 0) :
    ∃ p j : ℕ, Nat.Prime p ∧ 2 ≤ j ∧ p ^ j = k := by
  by_cases hp : Nat.Prime k
  · exfalso
    apply hk
    simp [wf, hp, ArithmeticFunction.vonMangoldt_apply_prime]
  · have h0 : ArithmeticFunction.vonMangoldt k ≠ 0 := by
      intro h
      apply hk
      simp [wf, hp, h]
    obtain ⟨p, j, hpp, hj, hpk⟩ := (isPrimePow_nat_iff k).1 (ArithmeticFunction.vonMangoldt_ne_zero_iff.1 h0)
    refine ⟨p, j, hpp, ?_, hpk⟩
    by_contra hj2
    have : j = 1 := by omega
    subst this
    apply hp
    rw [← hpk]
    simpa using hpp

private theorem sum_bounds (n : ℕ) (hn : 1 ≤ n) (h : ℕ) (hh : h ≤ n) (hhs : h ≤ Nat.sqrt n) :
    (∑ k ∈ Finset.range (n+1), (ArithmeticFunction.vonMangoldt k)^2 ≤ ((n:ℝ)+1) * Real.log (n:ℝ)^2) ∧
    (∑ k ∈ Finset.range (n+1), (wf k)^2 ≤ ((n:ℝ)+1) * Real.log (n:ℝ)^2) ∧
    (∑ k ∈ Finset.range (n+1), ((if k ≤ h then ArithmeticFunction.vonMangoldt k else 0))^2 ≤
        ((Nat.sqrt n : ℝ)+1) * ((Nat.log 2 n : ℝ)+1) * Real.log (n:ℝ)^2) ∧
    (∑ k ∈ Finset.range (n+1), (ArithmeticFunction.vonMangoldt k - wf k)^2 ≤
        ((Nat.sqrt n : ℝ)+1) * ((Nat.log 2 n : ℝ)+1) * Real.log (n:ℝ)^2) := by
  have hl : 0 ≤ Real.log (n:ℝ) := Real.log_nonneg (by exact_mod_cast hn)
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := sq_sum_le n (fun k => ArithmeticFunction.vonMangoldt k) (Real.log n) (Finset.range (n+1))
      (fun k hk _ => hk) (fun k hk => vm_abs_le n k hn (by simpa [Nat.lt_succ_iff] using hk))
    simpa using this
  · have := sq_sum_le n wf (Real.log n) (Finset.range (n+1))
      (fun k hk _ => hk) (fun k hk => wf_abs_le n k hn (by simpa [Nat.lt_succ_iff] using hk))
    simpa using this
  · have := sq_sum_le n (fun k => if k ≤ h then ArithmeticFunction.vonMangoldt k else 0) (Real.log n)
      (Finset.range (h+1))
      (fun k hk hne => by
        simp only [Finset.mem_range]
        by_contra hc
        apply hne
        rw [if_neg (by omega)])
      (fun k hk => by
        split_ifs
        · exact vm_abs_le n k hn (by simpa [Nat.lt_succ_iff] using hk)
        · simpa using hl)
    refine this.trans ?_
    simp only [Finset.card_range]
    have h1 : ((h + 1 : ℕ) : ℝ) ≤ ((Nat.sqrt n : ℝ) + 1) * ((Nat.log 2 n : ℝ) + 1) := by
      have : (Nat.sqrt n : ℝ) + 1 ≤ ((Nat.sqrt n : ℝ) + 1) * ((Nat.log 2 n : ℝ) + 1) := by
        nlinarith [(Nat.cast_nonneg (Nat.log 2 n) : (0:ℝ) ≤ (Nat.log 2 n : ℝ)), (Nat.cast_nonneg (Nat.sqrt n) : (0:ℝ) ≤ (Nat.sqrt n : ℝ))]
      have h2 : ((h + 1 : ℕ) : ℝ) ≤ (Nat.sqrt n : ℝ) + 1 := by exact_mod_cast Nat.succ_le_succ hhs
      exact h2.trans this
    exact mul_le_mul_of_nonneg_right h1 (sq_nonneg _)
  · let T : Finset ℕ := ((Finset.range (Nat.sqrt n + 1)) ×ˢ (Finset.range (Nat.log 2 n + 1))).image
      (fun p => p.1 ^ p.2)
    have := sq_sum_le n (fun k => ArithmeticFunction.vonMangoldt k - wf k) (Real.log n) T
      (fun k hk hne => by
        obtain ⟨p, j, hp, hj, hpk⟩ := Lw_support k hne
        have hkn : k ≤ n := by simpa [Nat.lt_succ_iff] using hk
        refine Finset.mem_image.2 ⟨(p, j), ?_, hpk⟩
        simp only [Finset.mem_product, Finset.mem_range]
        constructor
        · have : p ^ 2 ≤ n := by
            calc p ^ 2 ≤ p ^ j := Nat.pow_le_pow_right hp.pos hj
              _ = k := hpk
              _ ≤ n := hkn
          have := Nat.le_sqrt'.2 this
          omega
        · have : 2 ^ j ≤ n := by
            calc 2 ^ j ≤ p ^ j := Nat.pow_le_pow_left hp.two_le j
              _ = k := hpk
              _ ≤ n := hkn
          have := Nat.le_log_of_pow_le (by norm_num) this
          omega)
      (fun k hk => by
        have h1 := vm_abs_le n k hn (by simpa [Nat.lt_succ_iff] using hk)
        have h2 := wf_abs_le n k hn (by simpa [Nat.lt_succ_iff] using hk)
        have h3 : 0 ≤ ArithmeticFunction.vonMangoldt k := ArithmeticFunction.vonMangoldt_nonneg
        have h4 : wf k ≤ ArithmeticFunction.vonMangoldt k := by
          unfold wf
          split_ifs with hp
          · rw [ArithmeticFunction.vonMangoldt_apply_prime hp]
          · exact h3
        have h5 : 0 ≤ wf k := by
          unfold wf
          split_ifs with hp
          · exact Real.log_nonneg (by exact_mod_cast hp.one_lt.le)
          · exact le_rfl
        rw [abs_le]
        rw [abs_le] at h1
        constructor <;> linarith [h1.1, h1.2])
    refine this.trans ?_
    have hc : T.card ≤ (Nat.sqrt n + 1) * (Nat.log 2 n + 1) := by
      refine Finset.card_image_le.trans ?_
      simp
    have : (T.card : ℝ) ≤ ((Nat.sqrt n : ℝ)+1) * ((Nat.log 2 n : ℝ)+1) := by exact_mod_cast hc
    exact mul_le_mul_of_nonneg_right this (sq_nonneg _)

private theorem asym (ε : ℝ) (hε : 0 < ε) : ∃ N : ℕ, ∀ n ≥ N, 3 ≤ n ∧
    (((Nat.sqrt n:ℝ)+1)*((Nat.log 2 n:ℝ)+1)*Real.log (n:ℝ)^2) * (((n:ℝ)+1)*Real.log (n:ℝ)^2)
      ≤ ε^2 * (n:ℝ)^2 := by
  have hc : (0:ℝ) < ε^2 / 384 := by positivity
  have h1 := (Real.isLittleO_pow_log_id_atTop (n := 5)).def hc
  have h2 : ∀ᶠ n : ℕ in Filter.atTop, ‖Real.log (Real.sqrt (n:ℝ)) ^ 5‖ ≤ ε^2/384 * ‖id (Real.sqrt (n:ℝ))‖ :=
    (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop).eventually h1
  have h3 := h2.and (Filter.eventually_ge_atTop 3)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 h3
  refine ⟨N, fun n hn => ⟨(hN n hn).2, ?_⟩⟩
  have hn3 : 3 ≤ n := (hN n hn).2
  have hk := (hN n hn).1
  have hn3r : (3:ℝ) ≤ n := by exact_mod_cast hn3
  set x := Real.sqrt (n:ℝ) with hx
  have hxsq : x ^ 2 = (n:ℝ) := Real.sq_sqrt (by linarith)
  have hx1 : 1 ≤ x := by
    rw [hx]; exact Real.one_le_sqrt.2 (by linarith)
  have hlx : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hℓ : Real.log (n:ℝ) = 2 * Real.log x := by
    rw [hx, Real.log_sqrt (by linarith)]; ring
  have hℓ1 : 1 ≤ Real.log (n:ℝ) := by
    have h3' : Real.exp 1 < 3 := lt_trans Real.exp_one_lt_d9 (by norm_num)
    have := Real.log_lt_log (Real.exp_pos 1) (h3'.trans_le hn3r)
    rw [Real.log_exp] at this
    exact this.le
  have hk' : Real.log x ^ 5 ≤ ε^2/384 * x := by
    rw [Real.norm_of_nonneg (pow_nonneg hlx 5)] at hk
    simpa [abs_of_nonneg (by linarith : 0 ≤ x)] using hk
  have hm : (Nat.log 2 n : ℝ) ≤ 2 * Real.log (n:ℝ) := by
    have h0 : 2 ^ Nat.log 2 n ≤ n := Nat.pow_log_le_self 2 (by omega)
    have h0' : (2:ℝ) ^ Nat.log 2 n ≤ n := by exact_mod_cast h0
    have := Real.log_le_log (by positivity) h0'
    rw [Real.log_pow] at this
    have h2 := Real.log_two_gt_d9
    nlinarith [(Nat.cast_nonneg (Nat.log 2 n) : (0:ℝ) ≤ (Nat.log 2 n : ℝ))]
  have hs : (Nat.sqrt n : ℝ) ≤ x := Real.nat_sqrt_le_real_sqrt
  set ℓ := Real.log (n:ℝ) with hℓdef
  have hA : (Nat.sqrt n : ℝ) + 1 ≤ 2 * x := by linarith
  have hB : (Nat.log 2 n : ℝ) + 1 ≤ 3 * ℓ := by linarith
  have hC : (n:ℝ) + 1 ≤ 2 * x^2 := by nlinarith
  have hA0 : 0 ≤ (Nat.sqrt n : ℝ) + 1 := by positivity
  have hB0 : 0 ≤ (Nat.log 2 n : ℝ) + 1 := by positivity
  have hC0 : 0 ≤ (n:ℝ) + 1 := by positivity
  have hl0 : 0 ≤ ℓ := by linarith
  calc (((Nat.sqrt n:ℝ)+1)*((Nat.log 2 n:ℝ)+1)*ℓ^2) * (((n:ℝ)+1)*ℓ^2)
      ≤ ((2*x)*(3*ℓ)*ℓ^2) * ((2*x^2)*ℓ^2) := by gcongr
    _ = 12 * x^3 * (ℓ^5) := by ring
    _ = 12 * x^3 * (32 * Real.log x ^ 5) := by rw [hℓ]; ring
    _ ≤ 12 * x^3 * (32 * (ε^2/384 * x)) := by gcongr
    _ = ε^2 * (x^2)^2 := by ring
    _ = ε^2 * (n:ℝ)^2 := by rw [hxsq]

private theorem abs_bound (B U V X Y ε n : ℝ) (hB : B^2 ≤ U*V) (hU : U ≤ X) (hV : V ≤ Y)
    (hU0 : 0 ≤ U) (hV0 : 0 ≤ V) (hXY : X*Y ≤ ε^2*n^2) (hε : 0 ≤ ε) (hn : 0 ≤ n) :
    |B| ≤ ε * n := by
  have h1 : U * V ≤ X * Y := mul_le_mul hU hV hV0 (hU0.trans hU)
  have h2 : B^2 ≤ (ε*n)^2 := by nlinarith
  exact abs_le_of_sq_le_sq' h2 (mul_nonneg hε hn) |> fun h => abs_le.2 h

theorem Conjectures.Goldbach.VaughanSignedBudget :
    let cut (h : ℕ) (f : ArithmeticFunction ℝ) : ArithmeticFunction ℝ := ⟨fun k => if k ≤ h then f k else 0, (ite_eq_left (Nat.zero_le h)).trans f.map_zero⟩; let L := ArithmeticFunction.vonMangoldt; let m : ArithmeticFunction ℝ := ArithmeticFunction.moebius; let z : ArithmeticFunction ℝ := ArithmeticFunction.zeta; let h (n : ℕ) := Nat.sqrt (Nat.sqrt n); let a (n : ℕ) := cut (h n) m; let b (n : ℕ) := cut (h n) L; let I (n : ℕ) := a n * ArithmeticFunction.log - a n * b n * z; let J (n : ℕ) := (m-a n) * ((L-b n) * z); let w (k : ℕ) := if Nat.Prime k then Real.log (k : ℝ) else 0; let E (x : ℝ) := Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I); let S (n : ℕ) (u : ℕ → ℝ) (t : ℝ) := ∑ k ∈ Finset.range (n+1), (u k : ℂ) * E ((k : ℝ)*t); let Q (n : ℕ) := (Nat.log 2 (n+2))^2; let A (n : ℕ) := {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (Q n:ℝ)/((q:ℝ)*(n:ℝ))}; let B (n : ℕ) (u v : ℕ → ℝ) := (intervalIntegral ((A n)ᶜ.indicator (fun t => S n u t * S n v t * E (-(n : ℝ)*t))) (0:ℝ) 1 MeasureTheory.volume).re; let lower (F : ℕ → ℝ) := ∀ e : ℝ, 0 < e → ∃ N : ℕ, ∀ n ≥ N, Even n → -(e*(n:ℝ)) ≤ F n; lower (fun n => B n (I n) L) → lower (fun n => B n (J n) L) → lower (fun n => B n w w) := by
  intro cut L m z h a b I J w E S Q A B lower hI hJ e he
  have hBB : ∀ n u v, B n u v = BB n u v := fun _ _ _ => rfl
  have hε : 0 < e / 5 := by positivity
  obtain ⟨N1, h1⟩ := hI (e/5) hε
  obtain ⟨N2, h2⟩ := hJ (e/5) hε
  obtain ⟨N3, h3⟩ := asym (e/5) hε
  refine ⟨max (max N1 N2) N3, fun n hn hev => ?_⟩
  have hn1 : N1 ≤ n := by omega
  have hn2 : N2 ≤ n := by omega
  have hn3 := h3 n (by omega)
  obtain ⟨hn3', hasym⟩ := hn3
  have hn1' : 1 ≤ n := by omega
  have hI1 : -((e/5) * (n:ℝ)) ≤ BB n (I n) L := h1 n hn1 hev
  have hJ1 : -((e/5) * (n:ℝ)) ≤ BB n (J n) L := h2 n hn2 hev
  have hhn : h n ≤ Nat.sqrt n := Nat.sqrt_le_self _
  have hhn' : h n ≤ n := hhn.trans (Nat.sqrt_le_self _)
  obtain ⟨sL, sw, sb, sLw⟩ := sum_bounds n hn1' (h n) hhn' hhn
  have hid : ∀ k, L k = b n k + I n k + J n k := by
    have e0 : (L : ArithmeticFunction ℝ) = b n + I n + J n := vaughan_id (a n) (b n)
    intro k
    have e1 := congrArg (fun f : ArithmeticFunction ℝ => f k) e0
    simpa only [ArithmeticFunction.add_apply] using e1
  have hfun : (⇑L : ℕ → ℝ) = fun k => (b n k + I n k) + J n k := funext hid
  have eLL : BB n L L = BB n (b n) L + BB n (I n) L + BB n (J n) L := by
    have : BB n (fun k => (b n k + I n k) + J n k) L = BB n (b n) L + BB n (I n) L + BB n (J n) L := by
      rw [BB_add_left, BB_add_left]
    rw [← this]
    exact congrArg (fun u => BB n u (⇑L)) hfun
  have eW : BB n w w = BB n L L - BB n (fun k => L k - wf k) L - BB n wf (fun k => L k - wf k) := by
    have e0 : BB n w w = BB n wf wf := rfl
    rw [e0, BB_sub_left, BB_sub_right]
    ring
  have hL0 : 0 ≤ ∑ k ∈ Finset.range (n+1), (L k)^2 := Finset.sum_nonneg fun k _ => sq_nonneg _
  have hw0 : 0 ≤ ∑ k ∈ Finset.range (n+1), (wf k)^2 := Finset.sum_nonneg fun k _ => sq_nonneg _
  have hb0 : 0 ≤ ∑ k ∈ Finset.range (n+1), (b n k)^2 := Finset.sum_nonneg fun k _ => sq_nonneg _
  have hd0 : 0 ≤ ∑ k ∈ Finset.range (n+1), (L k - wf k)^2 := Finset.sum_nonneg fun k _ => sq_nonneg _
  have hnn : (0:ℝ) ≤ n := Nat.cast_nonneg n
  have hb : |BB n (b n) L| ≤ (e/5) * n :=
    abs_bound _ _ _ _ _ _ _ (BB_sq_le n (b n) L) sb sL hb0 hL0 hasym hε.le hnn
  have hd1 : |BB n (fun k => L k - wf k) L| ≤ (e/5) * n :=
    abs_bound _ _ _ _ _ _ _ (BB_sq_le n _ L) sLw sL hd0 hL0 hasym hε.le hnn
  have hd2 : |BB n wf (fun k => L k - wf k)| ≤ (e/5) * n :=
    abs_bound _ _ _ _ _ _ _ (BB_sq_le n wf _) sw sLw hw0 hd0 (by rw [mul_comm]; exact hasym) hε.le hnn
  rw [abs_le] at hb hd1 hd2
  show -(e * (n:ℝ)) ≤ BB n w w
  rw [eW, eLL]
  linarith [hb.1, hb.2, hd1.1, hd1.2, hd2.1, hd2.2]
