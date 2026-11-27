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

theorem ternary_main (n : ℕ) (u v : ℕ → ℝ) (A : Set ℝ) (U : ℝ) (hA : MeasurableSet A) (hU : 0 ≤ U)
    (h : ∀ t ∈ Set.Icc (0 : ℝ) 1, t ∉ A →
      ‖∑ k ∈ Finset.range (n+1), (u k : ℂ) * E ((k : ℝ) * t)‖ ≤ U) :
    ‖intervalIntegral (Aᶜ.indicator (fun t : ℝ =>
        (∑ k ∈ Finset.range (n+1), (u k : ℂ) * E ((k : ℝ) * t)) *
        (∑ k ∈ Finset.range (n+1), (v k : ℂ) * E ((k : ℝ) * t))^2 * E (-(n : ℝ)*t))) (0 : ℝ) 1
        MeasureTheory.volume‖ ≤ U * ∑ k ∈ Finset.range (n+1), (v k)^2 := by
  set Su : ℝ → ℂ := fun t => ∑ k ∈ Finset.range (n+1), (u k : ℂ) * E ((k : ℝ) * t) with hSu
  set Sv : ℝ → ℂ := fun t => ∑ k ∈ Finset.range (n+1), (v k : ℂ) * E ((k : ℝ) * t) with hSv
  have cSu : Continuous Su := by
    rw [hSu]
    exact continuous_finsetSum _ fun k _ => continuous_const.mul (E_cont.comp (by fun_prop))
  have cSv : Continuous Sv := by
    rw [hSv]
    exact continuous_finsetSum _ fun k _ => continuous_const.mul (E_cont.comp (by fun_prop))
  have cF : Continuous (fun t : ℝ => Su t * (Sv t)^2 * E (-(n : ℝ)*t)) :=
    (cSu.mul (cSv.pow 2)).mul (E_cont.comp (by fun_prop))
  have hint : IntervalIntegrable (Aᶜ.indicator (fun t : ℝ => Su t * (Sv t)^2 * E (-(n : ℝ)*t)))
      MeasureTheory.volume 0 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
    exact ((cF.intervalIntegrable 0 1).1).indicator hA.compl
  have hint2 : IntervalIntegrable (fun t : ℝ => U * ‖Sv t‖ ^ 2) MeasureTheory.volume 0 1 :=
    (continuous_const.mul (cSv.norm.pow 2)).intervalIntegrable 0 1
  calc ‖intervalIntegral (Aᶜ.indicator (fun t : ℝ => Su t * (Sv t)^2 * E (-(n : ℝ)*t))) 0 1
        MeasureTheory.volume‖
      ≤ ∫ t in (0:ℝ)..1, ‖Aᶜ.indicator (fun t : ℝ => Su t * (Sv t)^2 * E (-(n : ℝ)*t)) t‖ :=
        intervalIntegral.norm_integral_le_integral_norm zero_le_one
    _ ≤ ∫ t in (0:ℝ)..1, U * ‖Sv t‖ ^ 2 := by
        refine intervalIntegral.integral_mono_on zero_le_one hint.norm hint2 ?_
        intro t ht
        by_cases htA : t ∈ A
        · rw [Set.indicator_of_notMem (by simpa using htA)]
          simp only [norm_zero]
          positivity
        · rw [Set.indicator_of_mem (by simpa using htA)]
          rw [norm_mul, norm_mul, norm_pow, E_norm, mul_one]
          have := h t ht htA
          have h0 : 0 ≤ ‖Sv t‖ ^ 2 := by positivity
          exact mul_le_mul_of_nonneg_right this h0
    _ = U * ∑ k ∈ Finset.range (n+1), (v k)^2 := by
        rw [intervalIntegral.integral_const_mul]
        congr 1
        have := parseval (Finset.range (n+1)) (fun k => (v k : ℂ))
        simpa [hSv] using this

end GbLS

theorem Conjectures.Goldbach.TernaryMinorSaving :
    let E (x : ℝ) := Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I); let S (n : ℕ) (w : ℕ → ℝ) (t : ℝ) := ∑ k ∈ Finset.range (n+1), (w k : ℂ) * E ((k : ℝ)*t); ∀ (n : ℕ) (u v : ℕ → ℝ) (A : Set ℝ) (U : ℝ), MeasurableSet A → 0 ≤ U → (∀ t ∈ Set.Icc (0 : ℝ) 1, t ∉ A → ‖S n u t‖ ≤ U) → ‖intervalIntegral (Aᶜ.indicator (fun t => S n u t * (S n v t)^2 * E (-(n : ℝ)*t))) (0 : ℝ) 1 MeasureTheory.volume‖ ≤ U * ∑ k ∈ Finset.range (n+1), (v k)^2 := by
  intro E S n u v A U hA hU h
  exact GbLS.ternary_main n u v A U hA hU h
