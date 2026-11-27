import Mathlib

namespace GbPE

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


private lemma pe_gen (n : ℕ) (B : Set ℝ) (hB : MeasurableSet B) (x y : ℕ → ℝ) :
    intervalIntegral (B.indicator (fun t : ℝ => ‖∑ k ∈ Finset.range (n+1), (y k : ℂ) * E ((k:ℝ) * t)‖ ^ 2))
        (0:ℝ) 1 MeasureTheory.volume ≤
      17/16 * intervalIntegral (B.indicator (fun t : ℝ => ‖∑ k ∈ Finset.range (n+1), (x k : ℂ) * E ((k:ℝ) * t)‖ ^ 2))
        (0:ℝ) 1 MeasureTheory.volume +
      17 * ∑ k ∈ Finset.range (n+1), (x k - y k) ^ 2 := by
  have hc : ∀ c : ℕ → ℝ, Continuous (fun t : ℝ => ‖∑ k ∈ Finset.range (n+1), (c k : ℂ) * E ((k:ℝ) * t)‖ ^ 2) := by
    intro c
    exact (continuous_finsetSum _ fun k _ => continuous_const.mul (E_cont.comp (by fun_prop))).norm.pow 2
  have hi : ∀ c : ℕ → ℝ, IntervalIntegrable (B.indicator (fun t : ℝ => ‖∑ k ∈ Finset.range (n+1), (c k : ℂ) * E ((k:ℝ) * t)‖ ^ 2))
      MeasureTheory.volume (0:ℝ) 1 := by
    intro c
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
    exact ((hc c).integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self).indicator hB
  have hd : IntervalIntegrable (fun t : ℝ => ‖∑ k ∈ Finset.range (n+1), ((x k - y k : ℝ) : ℂ) * E ((k:ℝ) * t)‖ ^ 2)
      MeasureTheory.volume (0:ℝ) 1 := (hc _).intervalIntegrable 0 1
  have hpar := parseval (Finset.range (n+1)) (fun k => ((x k - y k : ℝ) : ℂ))
  have hpar' : ∫ t in (0:ℝ)..1, ‖∑ k ∈ Finset.range (n+1), ((x k - y k : ℝ) : ℂ) * E ((k:ℝ) * t)‖ ^ 2
      = ∑ k ∈ Finset.range (n+1), (x k - y k) ^ 2 := by
    rw [hpar]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hmono : intervalIntegral (B.indicator (fun t : ℝ => ‖∑ k ∈ Finset.range (n+1), (y k : ℂ) * E ((k:ℝ) * t)‖ ^ 2))
        (0:ℝ) 1 MeasureTheory.volume ≤
      ∫ t in (0:ℝ)..1, (17/16 * B.indicator (fun t : ℝ => ‖∑ k ∈ Finset.range (n+1), (x k : ℂ) * E ((k:ℝ) * t)‖ ^ 2) t +
        17 * ‖∑ k ∈ Finset.range (n+1), ((x k - y k : ℝ) : ℂ) * E ((k:ℝ) * t)‖ ^ 2) := by
    refine intervalIntegral.integral_mono_on zero_le_one (hi y) (((hi x).const_mul (17/16)).add (hd.const_mul 17)) ?_
    intro t _
    have hsy : ∑ k ∈ Finset.range (n+1), (y k : ℂ) * E ((k:ℝ) * t) =
        ∑ k ∈ Finset.range (n+1), (x k : ℂ) * E ((k:ℝ) * t) -
          ∑ k ∈ Finset.range (n+1), ((x k - y k : ℝ) : ℂ) * E ((k:ℝ) * t) := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      push_cast; ring
    have hnorm : ‖∑ k ∈ Finset.range (n+1), (y k : ℂ) * E ((k:ℝ) * t)‖ ^ 2 ≤
        17/16 * ‖∑ k ∈ Finset.range (n+1), (x k : ℂ) * E ((k:ℝ) * t)‖ ^ 2 +
        17 * ‖∑ k ∈ Finset.range (n+1), ((x k - y k : ℝ) : ℂ) * E ((k:ℝ) * t)‖ ^ 2 := by
      rw [hsy]
      set a := ‖∑ k ∈ Finset.range (n+1), (x k : ℂ) * E ((k:ℝ) * t)‖
      set b := ‖∑ k ∈ Finset.range (n+1), ((x k - y k : ℝ) : ℂ) * E ((k:ℝ) * t)‖
      have h1 := norm_sub_le (∑ k ∈ Finset.range (n+1), (x k : ℂ) * E ((k:ℝ) * t))
        (∑ k ∈ Finset.range (n+1), ((x k - y k : ℝ) : ℂ) * E ((k:ℝ) * t))
      have ha : 0 ≤ a := norm_nonneg _
      have hb : 0 ≤ b := norm_nonneg _
      have h2 : ‖(∑ k ∈ Finset.range (n+1), (x k : ℂ) * E ((k:ℝ) * t)) -
        (∑ k ∈ Finset.range (n+1), ((x k - y k : ℝ) : ℂ) * E ((k:ℝ) * t))‖ ^ 2 ≤ (a + b) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h1 2
      nlinarith [sq_nonneg (a / 4 - 4 * b)]
    by_cases ht : t ∈ B
    · rw [Set.indicator_of_mem ht, Set.indicator_of_mem ht]
      exact hnorm
    · rw [Set.indicator_of_notMem ht, Set.indicator_of_notMem ht]
      have := sq_nonneg ‖∑ k ∈ Finset.range (n+1), ((x k - y k : ℝ) : ℂ) * E ((k:ℝ) * t)‖
      simp only [mul_zero, zero_add]
      nlinarith
  refine hmono.trans (le_of_eq ?_)
  rw [intervalIntegral.integral_add ((hi x).const_mul (17/16)) (hd.const_mul 17),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, hpar']

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

private lemma pe_asym : ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    ((Nat.sqrt n * Nat.log 2 n + Nat.sqrt n + 1 : ℕ) : ℝ) * (Real.log (n:ℝ)) ^ 2 ≤ (n:ℝ) / 300000 := by
  refine ⟨1100 ^ 12, fun n hn => ?_⟩
  have hX : (1100:ℝ) ^ 12 ≤ (n:ℝ) := by exact_mod_cast hn
  have hX0 : 0 < (n:ℝ) := lt_of_lt_of_le (by positivity) hX
  set X : ℝ := (n:ℝ) with hXdef
  set Y : ℝ := X ^ ((1:ℝ)/12) with hY
  have hY0 : 0 < Y := Real.rpow_pos_of_pos hX0 _
  have hY12 : Y ^ 12 = X := by
    rw [hY, ← Real.rpow_natCast, ← Real.rpow_mul hX0.le]; norm_num
  have hY1100 : 1100 ≤ Y := by
    by_contra hlt
    push_neg at hlt
    have : Y ^ 12 < 1100 ^ 12 := pow_lt_pow_left₀ hlt hY0.le (by norm_num)
    linarith
  have hlogX : Real.log X ≤ 12 * Y := by
    have := Real.log_le_rpow_div hX0.le (show (0:ℝ) < 1/12 by norm_num)
    rw [← hY] at this
    linarith
  have hlogpos : 0 ≤ Real.log X := Real.log_nonneg (by linarith)
  have hsq : (Nat.sqrt n : ℝ) ≤ Y ^ 6 := by
    refine Real.nat_sqrt_le_real_sqrt.trans ?_
    rw [Real.sqrt_le_left (by positivity)]
    nlinarith [hY12]
  have hlg : (Nat.log 2 n : ℝ) ≤ 24 * Y := by
    have h1 := Real.natLog_le_logb n 2
    rw [Real.logb] at h1
    have hl2 : (1:ℝ)/2 < Real.log 2 := by have := Real.log_two_gt_d9; linarith
    have h2 : Real.log X / Real.log 2 ≤ 2 * Real.log X := by
      rw [div_le_iff₀ (by linarith)]
      nlinarith
    push_cast at h1
    linarith
  have hsq0 : (0:ℝ) ≤ Nat.sqrt n := Nat.cast_nonneg _
  have hlg0 : (0:ℝ) ≤ Nat.log 2 n := Nat.cast_nonneg _
  have hY6 : 1 ≤ Y ^ 6 := one_le_pow₀ (by linarith)
  have hcnt : ((Nat.sqrt n * Nat.log 2 n + Nat.sqrt n + 1 : ℕ) : ℝ) ≤ 26 * Y ^ 7 := by
    push_cast
    have h1 : (Nat.sqrt n : ℝ) * Nat.log 2 n ≤ Y ^ 6 * (24 * Y) := mul_le_mul hsq hlg hlg0 (by positivity)
    have h2 : Y ^ 6 ≤ Y ^ 6 * Y := by nlinarith
    have h3 : (1:ℝ) ≤ Y ^ 6 * Y := by nlinarith
    nlinarith
  have hlog2 : Real.log X ^ 2 ≤ 144 * Y ^ 2 := by
    nlinarith
  calc _ ≤ 26 * Y ^ 7 * (144 * Y ^ 2) :=
        mul_le_mul hcnt hlog2 (by positivity) (by positivity)
    _ ≤ X / 300000 := by
        rw [← hY12]
        have : (1100:ℝ) ^ 3 ≤ Y ^ 3 := pow_le_pow_left₀ (by norm_num) hY1100 3
        have h9 : 0 < Y ^ 9 := by positivity
        have : Y ^ 12 = Y ^ 9 * Y ^ 3 := by ring
        nlinarith

private lemma pe_meas (n : ℕ) :
    MeasurableSet {t : ℝ | t ∉ {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤(Nat.log 2 (n+2))^2 ∧ a≤q ∧ Nat.Coprime a q ∧
      |t-(a:ℝ)/(q:ℝ)| ≤ (((Nat.log 2 (n+2))^2 : ℕ):ℝ)/((q:ℝ)*(n:ℝ))} ∧
      (1:ℝ)/2 < (∑ j ∈ Finset.range (max 1 (Nat.log 2 n / 2)),
        Real.cos (2*Real.pi*(2:ℝ)^(j+1)*t))/((max 1 (Nat.log 2 n / 2) : ℕ):ℝ)} := by
  rw [Set.setOf_and]
  refine MeasurableSet.inter ?_ ?_
  · refine MeasurableSet.compl ?_
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
  · exact measurableSet_lt measurable_const (by fun_prop)

end GbPE

theorem Conjectures.Goldbach.PacketEnergyFromMangoldt :
    (let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let S := fun (n : ℕ) (w : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (w k:ℂ)*E ((k:ℝ)*t)); let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let arcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (Q n:ℝ)/((q:ℝ)*(n:ℝ))}; let L := fun n : ℕ => max 1 (Nat.log 2 n / 2); let K := fun (n : ℕ) (t : ℝ) => (∑ j ∈ Finset.range (L n), Real.cos (2*Real.pi*(2:ℝ)^(j+1)*t))/(L n:ℝ); let B := fun n : ℕ => {t : ℝ | t ∉ arcs n ∧ (1:ℝ)/2 < K n t}; let m := fun (s : Set ℝ) (f : ℝ → ℝ) => intervalIntegral (s.indicator f) (0:ℝ) 1 MeasureTheory.volume; ∃ N : ℕ, ∀ n ≥ N, Even n → m (B n) (fun t => ‖S n (fun k => ArithmeticFunction.vonMangoldt k) t‖^2) ≤ (n:ℝ)/640) → (let w := fun k : ℕ => if Nat.Prime k then Real.log (k:ℝ) else 0; let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let S := fun (n : ℕ) (w : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (w k:ℂ)*E ((k:ℝ)*t)); let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let arcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (Q n:ℝ)/((q:ℝ)*(n:ℝ))}; let low := fun (n k : ℕ) => if k^3≤n then w k else 0; let high := fun (n k : ℕ) => w k-low n k; let I := fun (n:ℕ) (a b:ℕ→ℝ) => intervalIntegral (fun t => (arcs n)ᶜ.indicator (fun u => S n a u*S n b u*E (-(n:ℝ)*u)) t) (0:ℝ) 1 MeasureTheory.volume; let L := fun n : ℕ => max 1 (Nat.log 2 n / 2); let K := fun (n : ℕ) (t : ℝ) => (∑ j ∈ Finset.range (L n), Real.cos (2*Real.pi*(2:ℝ)^(j+1)*t))/(L n:ℝ); let B := fun n : ℕ => {t : ℝ | t ∉ arcs n ∧ (1:ℝ)/2 < K n t}; let U := fun (n : ℕ) (a : ℕ → ℝ) => intervalIntegral ((B n).indicator (fun t => ‖S n a t‖^2)) (0:ℝ) 1 MeasureTheory.volume; ∃ N : ℕ, ∀ n ≥ N, Even n → U n (high n) ≤ (n:ℝ)/576) := by
  intro H
  dsimp only at H
  obtain ⟨N1, hN1⟩ := H
  obtain ⟨N2, hN2⟩ := GbPE.pe_asym
  dsimp only
  refine ⟨max N1 N2, fun n hn he => ?_⟩
  have h1 := hN1 n (le_trans (le_max_left _ _) hn) he
  have h3 := hN2 n (le_trans (le_max_right _ _) hn)
  have key := GbPE.pe_gen n _ (GbPE.pe_meas n) (fun k => ArithmeticFunction.vonMangoldt k)
    (fun k => (if Nat.Prime k then Real.log (k:ℝ) else 0) - (if k^3 ≤ n then (if Nat.Prime k then Real.log (k:ℝ) else 0) else 0))
  have hc := GbPE.pe_cnt n
  refine key.trans ?_
  have h2 := add_le_add (mul_le_mul_of_nonneg_left h1 (by norm_num : (0:ℝ) ≤ 17/16))
    (mul_le_mul_of_nonneg_left hc (by norm_num : (0:ℝ) ≤ 17))
  refine h2.trans ?_
  nlinarith [h3]
