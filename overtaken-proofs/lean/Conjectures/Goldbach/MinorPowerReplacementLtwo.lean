import Mathlib

namespace GbMPR

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

open Classical in
private lemma pe_pp_card (n : ℕ) :
    ((Finset.range (n+1)).filter (fun k => ∃ b a : ℕ, 2 ≤ b ∧ 2 ≤ a ∧ b^a = k)).card
      ≤ Nat.sqrt n * Nat.log 2 n := by
  have hsub : (Finset.range (n+1)).filter (fun k => ∃ b a : ℕ, 2 ≤ b ∧ 2 ≤ a ∧ b^a = k) ⊆
      (Finset.Icc 2 (Nat.sqrt n) ×ˢ Finset.Icc 2 (Nat.log 2 n)).image (fun p : ℕ × ℕ => p.1 ^ p.2) := by
    intro k hk
    simp only [Finset.mem_filter, Finset.mem_range] at hk
    obtain ⟨hkn, b, a, hb, ha, rfl⟩ := hk
    have hkn' : b ^ a ≤ n := by omega
    rw [Finset.mem_image]
    refine ⟨(b, a), ?_, rfl⟩
    rw [Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc]
    refine ⟨⟨hb, ?_⟩, ha, ?_⟩
    · rw [Nat.le_sqrt']
      exact le_trans (Nat.pow_le_pow_right (by omega) ha) hkn'
    · apply Nat.le_log_of_pow_le Nat.one_lt_two
      exact le_trans (Nat.pow_le_pow_left hb a) hkn'
  calc _ ≤ _ := Finset.card_le_card hsub
    _ ≤ _ := Finset.card_image_le
    _ = (Nat.sqrt n + 1 - 2) * (Nat.log 2 n + 1 - 2) := by simp
    _ ≤ Nat.sqrt n * Nat.log 2 n := Nat.mul_le_mul (by omega) (by omega)


open Classical in
private lemma pe_pt (n k : ℕ) (hk : k ∈ Finset.range (n+1)) :
    ArithmeticFunction.vonMangoldt k - (if k.Prime then Real.log (k:ℝ) else 0)
        ≤ if (∃ b a : ℕ, 2 ≤ b ∧ 2 ≤ a ∧ b^a = k) then Real.log (n : ℝ) else 0 := by
  have hkn : k ≤ n := by simp only [Finset.mem_range] at hk; omega
  by_cases hp : k.Prime
  · rw [if_pos hp, ArithmeticFunction.vonMangoldt_apply_prime hp, sub_self]
    split_ifs
    · exact Real.log_natCast_nonneg n
    · exact le_refl _
  · rw [if_neg hp, sub_zero]
    by_cases h0 : ArithmeticFunction.vonMangoldt k = 0
    · rw [h0]; split_ifs with h
      · exact Real.log_natCast_nonneg n
      · exact le_refl _
    · have hpp : IsPrimePow k := ArithmeticFunction.vonMangoldt_ne_zero_iff.mp h0
      obtain ⟨p, a, hpr, ha, hpa⟩ := (isPrimePow_nat_iff k).mp hpp
      have ha2 : 2 ≤ a := by
        by_contra hlt
        have : a = 1 := by omega
        subst this
        have hkp : k = p := by simpa using hpa.symm
        exact hp (hkp ▸ hpr)
      rw [if_pos ⟨p, a, hpr.two_le, ha2, hpa⟩]
      have hk0 : 0 < k := hpp.pos
      calc ArithmeticFunction.vonMangoldt k ≤ Real.log (k : ℝ) := ArithmeticFunction.vonMangoldt_le_log
        _ ≤ Real.log (n : ℝ) := Real.log_le_log (by exact_mod_cast hk0) (by exact_mod_cast hkn)

open Classical in
private lemma pe_cnt (n : ℕ) :
    ∑ k ∈ Finset.range (n+1), (ArithmeticFunction.vonMangoldt k -
        ((if k.Prime then Real.log (k:ℝ) else 0) - (if k^3 ≤ n then (if k.Prime then Real.log (k:ℝ) else 0) else 0))) ^ 2
      ≤ ((Nat.sqrt n * Nat.log 2 n + Nat.sqrt n + 1 : ℕ) : ℝ) * (Real.log (n:ℝ)) ^ 2 := by
  have hL : 0 ≤ Real.log (n : ℝ) := Real.log_natCast_nonneg n
  have hpt : ∀ k ∈ Finset.range (n+1),
      (ArithmeticFunction.vonMangoldt k -
        ((if k.Prime then Real.log (k:ℝ) else 0) - (if k^3 ≤ n then (if k.Prime then Real.log (k:ℝ) else 0) else 0))) ^ 2
      ≤ if (k^3 ≤ n ∨ ∃ b a : ℕ, 2 ≤ b ∧ 2 ≤ a ∧ b^a = k) then (Real.log (n:ℝ)) ^ 2 else 0 := by
    intro k hk
    have hkn : k ≤ n := by simp only [Finset.mem_range] at hk; omega
    have hlam : ArithmeticFunction.vonMangoldt k ≤ Real.log (n : ℝ) := by
      rcases Nat.eq_zero_or_pos k with h0 | h0
      · subst h0; simpa using hL
      · exact ArithmeticFunction.vonMangoldt_le_log.trans
          (Real.log_le_log (by exact_mod_cast h0) (by exact_mod_cast hkn))
    have hlam0 := (ArithmeticFunction.vonMangoldt_nonneg : 0 ≤ ArithmeticFunction.vonMangoldt k)
    have hd0 : 0 ≤ ArithmeticFunction.vonMangoldt k - (if k.Prime then Real.log (k:ℝ) else 0) := by
      by_cases hp : k.Prime
      · simp only [if_pos hp, ArithmeticFunction.vonMangoldt_apply_prime hp]; simp
      · simp only [if_neg hp, sub_zero]; exact hlam0
    by_cases h3 : k^3 ≤ n
    · rw [if_pos h3, sub_self, sub_zero, if_pos (Or.inl h3)]
      exact pow_le_pow_left₀ hlam0 hlam 2
    · rw [if_neg h3, sub_zero]
      have := pe_pt n k hk
      by_cases hpp : ∃ b a : ℕ, 2 ≤ b ∧ 2 ≤ a ∧ b^a = k
      · rw [if_pos (Or.inr hpp)]
        rw [if_pos hpp] at this
        exact pow_le_pow_left₀ hd0 this 2
      · rw [if_neg (not_or.mpr ⟨h3, hpp⟩)]
        rw [if_neg hpp] at this
        have : ArithmeticFunction.vonMangoldt k - (if k.Prime then Real.log (k:ℝ) else 0) = 0 := le_antisymm this hd0
        rw [this]; norm_num
  have hsub : (Finset.range (n+1)).filter (fun k => k^3 ≤ n) ⊆ Finset.range (Nat.sqrt n + 1) := by
    intro k hk
    simp only [Finset.mem_filter, Finset.mem_range] at hk ⊢
    have : k ≤ Nat.sqrt n := by
      rw [Nat.le_sqrt]
      rcases Nat.eq_zero_or_pos k with h0 | h0
      · subst h0; simp
      · have : k * k ≤ k ^ 3 := by nlinarith [Nat.mul_pos h0 h0]
        omega
    omega
  have hcard : ((Finset.range (n+1)).filter (fun k => k^3 ≤ n ∨ ∃ b a : ℕ, 2 ≤ b ∧ 2 ≤ a ∧ b^a = k)).card ≤
      Nat.sqrt n * Nat.log 2 n + Nat.sqrt n + 1 := by
    rw [Finset.filter_or]
    refine (Finset.card_union_le _ _).trans ?_
    have h1 := Finset.card_le_card hsub
    have h2 := pe_pp_card n
    simp only [Finset.card_range] at h1
    omega
  calc _ ≤ ∑ k ∈ Finset.range (n+1), (if (k^3 ≤ n ∨ ∃ b a : ℕ, 2 ≤ b ∧ 2 ≤ a ∧ b^a = k) then (Real.log (n:ℝ)) ^ 2 else 0) :=
        Finset.sum_le_sum hpt
    _ = (((Finset.range (n+1)).filter (fun k => k^3 ≤ n ∨ ∃ b a : ℕ, 2 ≤ b ∧ 2 ≤ a ∧ b^a = k)).card : ℝ) * (Real.log (n:ℝ)) ^ 2 := by
        rw [← Finset.sum_filter]; simp
    _ ≤ _ := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact_mod_cast hcard


private noncomputable def SS (n : ℕ) (x : ℕ → ℝ) (t : ℝ) : ℂ :=
  ∑ k ∈ Finset.range (n+1), (x k : ℂ) * E ((k:ℝ) * t)

private lemma SS_cont (n : ℕ) (x : ℕ → ℝ) : Continuous (SS n x) := by
  unfold SS
  exact continuous_finsetSum _ fun k _ => continuous_const.mul (E_cont.comp (by fun_prop))

private lemma SS_add (n : ℕ) (a r c : ℕ → ℝ) (h : ∀ k, c k = a k + r k) (t : ℝ) :
    SS n c t = SS n a t + SS n r t := by
  unfold SS
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [h k]; push_cast; ring

private lemma pars (n : ℕ) (x : ℕ → ℝ) :
    ∫ t in (0:ℝ)..1, ‖SS n x t‖ ^ 2 = ∑ k ∈ Finset.range (n+1), (x k) ^ 2 := by
  have := parseval (Finset.range (n+1)) (fun k => ((x k : ℝ) : ℂ))
  unfold SS
  rw [this]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]

private lemma gen (n : ℕ) (A : Set ℝ) (hA : MeasurableSet A) (a r c : ℕ → ℝ)
    (hc : ∀ k, c k = a k + r k) (lam : ℝ) (hlam : 0 < lam) :
    ‖(∫ t in (0:ℝ)..1, A.indicator (fun u => SS n c u * SS n c u * E (-(n:ℝ)*u)) t) -
      (∫ t in (0:ℝ)..1, A.indicator (fun u => SS n a u * SS n a u * E (-(n:ℝ)*u)) t)‖ ≤
      (lam + 1) * ∑ k ∈ Finset.range (n+1), (r k) ^ 2 +
        (1/lam) * ∑ k ∈ Finset.range (n+1), (a k) ^ 2 := by
  have hint : ∀ x y : ℕ → ℝ, IntervalIntegrable
      (A.indicator (fun u => SS n x u * SS n y u * E (-(n:ℝ)*u))) MeasureTheory.volume (0:ℝ) 1 := by
    intro x y
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
    have hcont : Continuous (fun u => SS n x u * SS n y u * E (-(n:ℝ)*u)) :=
      ((SS_cont n x).mul (SS_cont n y)).mul (E_cont.comp (by fun_prop))
    exact (hcont.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self).indicator hA
  rw [← intervalIntegral.integral_sub (hint c c) (hint a a)]
  have hr : Continuous (fun t => ‖SS n r t‖ ^ 2) := (SS_cont n r).norm.pow 2
  have ha : Continuous (fun t => ‖SS n a t‖ ^ 2) := (SS_cont n a).norm.pow 2
  have hg : IntervalIntegrable (fun t => (lam+1) * ‖SS n r t‖ ^ 2 + (1/lam) * ‖SS n a t‖ ^ 2)
      MeasureTheory.volume (0:ℝ) 1 :=
    ((hr.const_mul _).add (ha.const_mul _)).intervalIntegrable 0 1
  refine (intervalIntegral.norm_integral_le_of_norm_le zero_le_one
    (Filter.Eventually.of_forall fun t _ => ?_) hg).trans (le_of_eq ?_)
  · by_cases ht : t ∈ A
    · simp only [Pi.sub_apply, Set.indicator_of_mem ht]
      have e1 : SS n c t * SS n c t * E (-(n:ℝ)*t) - SS n a t * SS n a t * E (-(n:ℝ)*t)
          = SS n r t * (2 * SS n a t + SS n r t) * E (-(n:ℝ)*t) := by
        rw [SS_add n a r c hc t]; ring
      rw [e1, norm_mul, norm_mul, E_norm, mul_one]
      have h1 : ‖2 * SS n a t + SS n r t‖ ≤ 2 * ‖SS n a t‖ + ‖SS n r t‖ := by
        refine (norm_add_le _ _).trans ?_
        rw [norm_mul]; simp
      set x := ‖SS n r t‖
      set y := ‖SS n a t‖
      have hx : 0 ≤ x := norm_nonneg _
      have hy : 0 ≤ y := norm_nonneg _
      have h2 : x * ‖2 * SS n a t + SS n r t‖ ≤ x * (2 * y + x) := mul_le_mul_of_nonneg_left h1 hx
      have h3 : 2 * x * y ≤ lam * x ^ 2 + (1/lam) * y ^ 2 := by
        have : 0 ≤ (lam * x - y) ^ 2 / lam := by positivity
        have e : (lam * x - y) ^ 2 / lam = lam * x ^ 2 + (1/lam) * y ^ 2 - 2 * x * y := by
          field_simp
          ring
        linarith
      nlinarith
    · simp only [Pi.sub_apply, Set.indicator_of_notMem ht, sub_self, norm_zero]
      positivity
  · rw [intervalIntegral.integral_add ((hr.const_mul (lam+1)).intervalIntegrable 0 1)
      ((ha.const_mul (1/lam)).intervalIntegrable 0 1),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, pars, pars]

private lemma arcs_meas (n : ℕ) :
    MeasurableSet {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤(Nat.log 2 (n+2))^2 ∧ a≤q ∧ Nat.Coprime a q ∧
      |t-(a:ℝ)/(q:ℝ)| ≤ (((Nat.log 2 (n+2))^2 : ℕ):ℝ)/((q:ℝ)*(n:ℝ))} := by
  have : {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤(Nat.log 2 (n+2))^2 ∧ a≤q ∧ Nat.Coprime a q ∧
      |t-(a:ℝ)/(q:ℝ)| ≤ (((Nat.log 2 (n+2))^2 : ℕ):ℝ)/((q:ℝ)*(n:ℝ))} =
        ⋃ q : ℕ, ⋃ a : ℕ, {t : ℝ | (1≤q ∧ q≤(Nat.log 2 (n+2))^2 ∧ a≤q ∧ Nat.Coprime a q) ∧
      |t-(a:ℝ)/(q:ℝ)| ≤ (((Nat.log 2 (n+2))^2 : ℕ):ℝ)/((q:ℝ)*(n:ℝ))} := by
    ext t; simp only [Set.mem_setOf_eq, Set.mem_iUnion]
    constructor
    · rintro ⟨q, a, h1, h2, h3, h4, h5⟩; exact ⟨q, a, ⟨h1, h2, h3, h4⟩, h5⟩
    · rintro ⟨q, a, ⟨h1, h2, h3, h4⟩, h5⟩; exact ⟨q, a, h1, h2, h3, h4, h5⟩
  rw [this]
  refine MeasurableSet.iUnion fun q => MeasurableSet.iUnion fun a => ?_
  rw [Set.setOf_and]
  refine MeasurableSet.inter (MeasurableSet.const _) ?_
  exact measurableSet_le (by fun_prop) measurable_const

open Classical in
private lemma sumR (n : ℕ) :
    ∑ k ∈ Finset.range (n+1), ((if k^3 ≤ n then 0 else ArithmeticFunction.vonMangoldt k) -
      ((if k.Prime then Real.log (k:ℝ) else 0) - (if k^3 ≤ n then (if k.Prime then Real.log (k:ℝ) else 0) else 0))) ^ 2
      ≤ ((Nat.sqrt n * Nat.log 2 n + Nat.sqrt n + 1 : ℕ) : ℝ) * (Real.log (n:ℝ)) ^ 2 := by
  refine le_trans (Finset.sum_le_sum fun k _ => ?_) (pe_cnt n)
  by_cases h3 : k^3 ≤ n
  · simp [h3]
  · simp [h3]

open Classical in
private lemma sumH (n : ℕ) :
    ∑ k ∈ Finset.range (n+1),
      ((if k.Prime then Real.log (k:ℝ) else 0) - (if k^3 ≤ n then (if k.Prime then Real.log (k:ℝ) else 0) else 0)) ^ 2
      ≤ ((n:ℝ) + 1) * (Real.log (n:ℝ)) ^ 2 := by
  have : ∀ k ∈ Finset.range (n+1),
      ((if k.Prime then Real.log (k:ℝ) else 0) - (if k^3 ≤ n then (if k.Prime then Real.log (k:ℝ) else 0) else 0)) ^ 2
      ≤ (Real.log (n:ℝ)) ^ 2 := by
    intro k hk
    have hkn : k ≤ n := by simp only [Finset.mem_range] at hk; omega
    have hL : 0 ≤ Real.log (n : ℝ) := Real.log_natCast_nonneg n
    by_cases h3 : k^3 ≤ n
    · simp [h3]; positivity
    · by_cases hp : k.Prime
      · simp only [h3, hp, if_true, if_false, sub_zero]
        have h0 : 0 ≤ Real.log (k:ℝ) := Real.log_natCast_nonneg k
        have : Real.log (k:ℝ) ≤ Real.log (n:ℝ) :=
          Real.log_le_log (by exact_mod_cast hp.pos) (by exact_mod_cast hkn)
        exact pow_le_pow_left₀ h0 this 2
      · simp [h3, hp]; positivity
  refine (Finset.sum_le_sum this).trans ?_
  simp

private lemma est (n : ℕ) (hn : 3 ≤ n) (X Y : ℝ)
    (hX : X ≤ ((Nat.sqrt n * Nat.log 2 n + Nat.sqrt n + 1 : ℕ) : ℝ) * (Real.log (n:ℝ)) ^ 2)
    (hY : Y ≤ ((n:ℝ) + 1) * (Real.log (n:ℝ)) ^ 2) :
    ((n:ℝ) ^ ((1:ℝ)/4) + 1) * X + 1 / ((n:ℝ) ^ ((1:ℝ)/4)) * Y ≤
      20 * (n:ℝ) ^ (3 / 4 : ℝ) * (Real.log (n:ℝ)) ^ 3 := by
  have hn0 : (3:ℝ) ≤ n := by exact_mod_cast hn
  have hn1 : (0:ℝ) < n := by linarith
  set u : ℝ := (n:ℝ) ^ ((1:ℝ)/4) with hu
  set L : ℝ := Real.log (n:ℝ) with hLdef
  have hu0 : 0 < u := Real.rpow_pos_of_pos hn1 _
  have hu4 : u ^ 4 = n := by
    rw [hu, ← Real.rpow_natCast, ← Real.rpow_mul hn1.le]; norm_num
  have hu3 : (n:ℝ) ^ (3 / 4 : ℝ) = u ^ 3 := by
    rw [hu, ← Real.rpow_natCast, ← Real.rpow_mul hn1.le]; norm_num
  have hu1 : 1 ≤ u := by
    by_contra h
    push_neg at h
    have : u ^ 4 < 1 := pow_lt_one₀ hu0.le h (by norm_num)
    linarith
  have hL1 : 1 ≤ L := by
    rw [hLdef, Real.le_log_iff_exp_le hn1]
    have := Real.exp_one_lt_d9
    linarith
  have hsq : (Nat.sqrt n : ℝ) ≤ u ^ 2 := by
    refine Real.nat_sqrt_le_real_sqrt.trans ?_
    rw [Real.sqrt_le_left (by positivity)]
    nlinarith [hu4]
  have hlg : (Nat.log 2 n : ℝ) ≤ 2 * L := by
    have h1 := Real.natLog_le_logb n 2
    rw [Real.logb] at h1
    have hl2 : (1:ℝ)/2 < Real.log 2 := by have := Real.log_two_gt_d9; linarith
    have h2 : Real.log (n:ℝ) / Real.log 2 ≤ 2 * Real.log (n:ℝ) := by
      rw [div_le_iff₀ (by linarith)]
      nlinarith
    linarith
  have hsq0 : (0:ℝ) ≤ Nat.sqrt n := Nat.cast_nonneg _
  have hlg0 : (0:ℝ) ≤ Nat.log 2 n := Nat.cast_nonneg _
  have hu2 : 1 ≤ u ^ 2 := one_le_pow₀ hu1
  have hM : ((Nat.sqrt n * Nat.log 2 n + Nat.sqrt n + 1 : ℕ) : ℝ) ≤ 4 * u ^ 2 * L := by
    push_cast
    have h1 : (Nat.sqrt n : ℝ) * Nat.log 2 n ≤ u ^ 2 * (2 * L) := mul_le_mul hsq hlg hlg0 (by positivity)
    nlinarith
  have hL2 : 0 ≤ L ^ 2 := by positivity
  have hX' : X ≤ 4 * u ^ 2 * L * L ^ 2 :=
    hX.trans (mul_le_mul_of_nonneg_right hM hL2)
  have hY' : Y ≤ 2 * u ^ 4 * L ^ 2 := by
    refine hY.trans ?_
    rw [hu4]
    nlinarith
  rw [hu3]
  have hZ : 0 ≤ 4 * u ^ 2 * L * L ^ 2 := by positivity
  have e1 : (u + 1) * X ≤ (u + 1) * (4 * u ^ 2 * L * L ^ 2) :=
    mul_le_mul_of_nonneg_left hX' (by linarith)
  have e2 : 1 / u * Y ≤ 1 / u * (2 * u ^ 4 * L ^ 2) :=
    mul_le_mul_of_nonneg_left hY' (by positivity)
  have e3 : 1 / u * (2 * u ^ 4 * L ^ 2) = 2 * u ^ 3 * L ^ 2 := by
    field_simp
  have e4 : (u + 1) * (4 * u ^ 2 * L * L ^ 2) ≤ 2 * u * (4 * u ^ 2 * L * L ^ 2) :=
    mul_le_mul_of_nonneg_right (by linarith) hZ
  have e5 : L ^ 2 ≤ L ^ 3 := by nlinarith [sq_nonneg L]
  have e6 : 0 ≤ u ^ 3 := by positivity
  nlinarith [mul_le_mul_of_nonneg_left e5 e6]

end GbMPR

theorem Conjectures.Goldbach.MinorPowerReplacementLtwo :
    (let w := fun k : ℕ => if Nat.Prime k then Real.log (k:ℝ) else 0; let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let S := fun (n : ℕ) (w : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (w k:ℂ)*E ((k:ℝ)*t)); let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let arcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (Q n:ℝ)/((q:ℝ)*(n:ℝ))}; let low := fun (n k : ℕ) => if k^3≤n then w k else 0; let high := fun (n k : ℕ) => w k-low n k; let highLambda := fun (n k : ℕ) => if k^3≤n then 0 else ArithmeticFunction.vonMangoldt k; let I := fun (n:ℕ) (a b:ℕ→ℝ) => intervalIntegral (fun t => (arcs n)ᶜ.indicator (fun u => S n a u*S n b u*E (-(n:ℝ)*u)) t) (0:ℝ) 1 MeasureTheory.volume; ∃ (C : ℝ) (N : ℕ), 0 < C ∧ ∀ n : ℕ, N ≤ n → ‖I n (highLambda n) (highLambda n) - I n (high n) (high n)‖ ≤ C * (n : ℝ) ^ (3 / 4 : ℝ) * (Real.log (n : ℝ)) ^ 3) := by
  intro w E S Q arcs low high highLambda I
  refine ⟨20, 3, by norm_num, fun n hn => ?_⟩
  have hA : MeasurableSet (arcs n) := GbMPR.arcs_meas n
  have hu0 : 0 < (n:ℝ) ^ ((1:ℝ)/4) :=
    Real.rpow_pos_of_pos (by have : (3:ℝ) ≤ n := by exact_mod_cast hn
                             linarith) _
  have key : ‖I n (highLambda n) (highLambda n) - I n (high n) (high n)‖ ≤
      ((n:ℝ) ^ ((1:ℝ)/4) + 1) * ∑ k ∈ Finset.range (n+1), (highLambda n k - high n k) ^ 2 +
        1 / ((n:ℝ) ^ ((1:ℝ)/4)) * ∑ k ∈ Finset.range (n+1), (high n k) ^ 2 :=
    GbMPR.gen n (arcs n)ᶜ hA.compl (high n) (fun k => highLambda n k - high n k) (highLambda n)
      (fun k => by ring) _ hu0
  refine key.trans ?_
  exact GbMPR.est n hn _ _ (GbMPR.sumR n) (GbMPR.sumH n)
