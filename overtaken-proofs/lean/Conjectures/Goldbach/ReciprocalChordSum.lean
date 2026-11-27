import Mathlib

private lemma rcs_norm (y : ℝ) :
    ‖1 - Complex.exp (((2 * Real.pi * y : ℝ) : ℂ) * Complex.I)‖ = 2 * |Real.sin (Real.pi * y)| := by
  rw [norm_sub_rev, mul_comm _ Complex.I, Complex.norm_exp_I_mul_ofReal_sub_one, Real.norm_eq_abs,
    abs_mul]
  have : 2 * Real.pi * y / 2 = Real.pi * y := by ring
  rw [this]; simp

private lemma rcs_sin_lb (y : ℝ) : 2 * |y - round y| ≤ |Real.sin (Real.pi * y)| := by
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

private lemma rcs_cap (H y : ℝ) (hH : 0 ≤ H) :
    (if Complex.exp (((2 * Real.pi * y : ℝ) : ℂ) * Complex.I) = 1 then H
      else min H (2 / ‖1 - Complex.exp (((2 * Real.pi * y : ℝ) : ℂ) * Complex.I)‖)) ≤ H ∧
    (0 < |y - round y| →
      (if Complex.exp (((2 * Real.pi * y : ℝ) : ℂ) * Complex.I) = 1 then H
      else min H (2 / ‖1 - Complex.exp (((2 * Real.pi * y : ℝ) : ℂ) * Complex.I)‖))
        ≤ 1 / (2 * |y - round y|)) := by
  constructor
  · split_ifs
    · exact le_rfl
    · exact min_le_left _ _
  · intro hc
    have hlb := rcs_sin_lb y
    have hn := rcs_norm y
    have hne : Complex.exp (((2 * Real.pi * y : ℝ) : ℂ) * Complex.I) ≠ 1 := by
      intro h
      rw [h, sub_self, norm_zero] at hn
      have : 0 < |Real.sin (Real.pi * y)| := by linarith
      linarith
    rw [if_neg hne]
    refine (min_le_right _ _).trans ?_
    rw [hn]
    have : 0 < |Real.sin (Real.pi * y)| := by linarith
    rw [div_le_div_iff₀ (by linarith) (by linarith)]
    nlinarith

private lemma rcs_psi_sum (q : ℕ) (hq : 1 ≤ q) :
    ∑ k ∈ Finset.range (2 * q + 1), (2 : ℝ) * (if 3 ≤ k then (q : ℝ) / k else 0)
      ≤ 2 * q * (1 + Real.log (2 * q)) := by
  rw [Finset.sum_range_succ' _ (2 * q)]
  have h0 : (2 : ℝ) * (if 3 ≤ 0 then (q : ℝ) / (0 : ℕ) else 0) = 0 := by simp
  rw [h0, add_zero]
  have hh := harmonic_le_one_add_log (2 * q)
  have hh2 : ((harmonic (2 * q) : ℚ) : ℝ) = ∑ i ∈ Finset.range (2 * q), (((i + 1 : ℕ) : ℝ))⁻¹ := by
    unfold harmonic
    push_cast
    rfl
  rw [hh2] at hh
  have : ∑ k ∈ Finset.range (2 * q), (2 : ℝ) * (if 3 ≤ k + 1 then (q : ℝ) / ((k + 1 : ℕ) : ℝ) else 0)
      ≤ ∑ k ∈ Finset.range (2 * q), 2 * q * (((k + 1 : ℕ) : ℝ))⁻¹ := by
    apply Finset.sum_le_sum
    intro k _
    split_ifs
    · rw [div_eq_mul_inv]; nlinarith [inv_nonneg.mpr (Nat.cast_nonneg (α := ℝ) (k + 1))]
    · have : (0:ℝ) ≤ 2 * q * (((k + 1 : ℕ) : ℝ))⁻¹ := by positivity
      linarith
  refine this.trans ?_
  rw [← Finset.mul_sum]
  have hq0 : (0 : ℝ) ≤ 2 * q := by positivity
  push_cast at hh ⊢
  exact mul_le_mul_of_nonneg_left (by push_cast at hh; exact hh) hq0

theorem Conjectures.Goldbach.ReciprocalChordSum :
    let E (y : ℝ) := Complex.exp (((2 * Real.pi * y : ℝ) : ℂ) * Complex.I); let cap (H y : ℝ) := if E y = 1 then H else min H (2 / ‖1 - E y‖); ∀ (a q : ℕ) (t x H : ℝ), 1 ≤ q → Nat.Coprime a q → 0 ≤ H → |t - (a : ℝ) / q| ≤ 1 / (q : ℝ)^2 → (∑ r ∈ Finset.range q, cap H (x + (r : ℝ)*t)) ≤ 6 * (H + (q : ℝ) * Real.log (2 * q)) := by
  intro E cap a q t x H hq hco hH ht
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hqpos : (0 : ℝ) < q := by linarith
  set s : ℤ := round ((q : ℝ) * x) with hs
  set n : ℕ → ℤ := fun r => round (x + (r : ℝ) * t) with hn
  set m : ℕ → ℤ := fun r => s + (a : ℤ) * r - (q : ℤ) * n r with hm
  have hbound : ∀ r ∈ Finset.range q,
      |(q : ℝ) * (x + (r : ℝ) * t - n r) - (m r : ℝ)| ≤ 3 / 2 := by
    intro r hr
    have hrq : (r : ℝ) ≤ q := by exact_mod_cast (Finset.mem_range.mp hr).le
    have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
    have e : (q : ℝ) * (x + (r : ℝ) * t - n r) - (m r : ℝ)
        = ((q : ℝ) * x - s) + (q : ℝ) * r * (t - (a : ℝ) / q) := by
      simp only [hm]; push_cast; field_simp; ring
    have h1 : |(q : ℝ) * x - s| ≤ 1 / 2 := abs_sub_round _
    have h2 : |(q : ℝ) * r * (t - (a : ℝ) / q)| ≤ 1 := by
      rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ q * r)]
      calc (q : ℝ) * r * |t - (a : ℝ) / q| ≤ (q : ℝ) * r * (1 / (q : ℝ) ^ 2) :=
            mul_le_mul_of_nonneg_left ht (by positivity)
        _ ≤ 1 := by
            rw [mul_one_div, div_le_one (by positivity)]
            nlinarith
    rw [e]
    calc _ ≤ |(q : ℝ) * x - s| + |(q : ℝ) * r * (t - (a : ℝ) / q)| := abs_add_le _ _
      _ ≤ 3 / 2 := by linarith
  have hinj : Set.InjOn m (Finset.range q : Set ℕ) := by
    intro r hr r' hr' h
    have hr1 : r < q := Finset.mem_range.mp hr
    have hr2 : r' < q := Finset.mem_range.mp hr'
    simp only [hm] at h
    have hd : (q : ℤ) ∣ (a : ℤ) * ((r : ℤ) - r') := ⟨n r - n r', by linarith⟩
    have hc : IsCoprime (q : ℤ) (a : ℤ) := Nat.isCoprime_iff_coprime.mpr hco.symm
    have hd2 : (q : ℤ) ∣ ((r : ℤ) - r') := hc.dvd_of_dvd_mul_left hd
    have : ((r : ℤ) - r') = 0 := by
      apply Int.eq_zero_of_abs_lt_dvd hd2
      rw [abs_lt]; constructor <;> omega
    omega
  -- termwise bound
  have hterm : ∀ r ∈ Finset.range q, cap H (x + (r : ℝ) * t) ≤
      (if |m r| < 3 then H else 0) + (if 3 ≤ (m r).natAbs then (q : ℝ) / (m r).natAbs else 0) := by
    intro r hr
    have hb := hbound r hr
    have hc := rcs_cap H (x + (r : ℝ) * t) hH
    have hcn : |x + (r : ℝ) * t - round (x + (r : ℝ) * t)| ≤ 1 / 2 := abs_sub_round _
    by_cases h3 : |m r| < 3
    · rw [if_pos h3]
      have : 0 ≤ (if 3 ≤ (m r).natAbs then (q : ℝ) / (m r).natAbs else 0) := by
        split_ifs <;> positivity
      have := hc.1
      show (if E (x + (r:ℝ) * t) = 1 then H else _) ≤ _
      linarith
    · rw [if_neg h3, zero_add]
      have h3' : 3 ≤ (m r).natAbs := by rw [Int.abs_eq_natAbs] at h3; omega
      rw [if_pos h3']
      have hmabs : ((m r).natAbs : ℝ) = |(m r : ℝ)| := by
        rw [Nat.cast_natAbs, Int.cast_abs]
      have hm3 : (3 : ℝ) ≤ |(m r : ℝ)| := by rw [← hmabs]; exact_mod_cast h3'
      set c := |x + (r : ℝ) * t - round (x + (r : ℝ) * t)| with hcdef
      have hqc : |(m r : ℝ)| - 3 / 2 ≤ q * c := by
        have : (q : ℝ) * c = |(q : ℝ) * (x + (r : ℝ) * t - n r)| := by
          rw [abs_mul, abs_of_pos hqpos]
        rw [this]
        have := abs_sub_abs_le_abs_sub (q * (x + (r : ℝ) * t - n r)) (m r : ℝ)
        have := abs_sub_abs_le_abs_sub (m r : ℝ) (q * (x + (r : ℝ) * t - n r))
        rw [abs_sub_comm] at this
        linarith
      have hcpos : 0 < c := by nlinarith
      have h2 := hc.2 hcpos
      show (if E (x + (r:ℝ) * t) = 1 then H else _) ≤ _
      refine h2.trans ?_
      rw [hmabs, div_le_div_iff₀ (by positivity) (by linarith)]
      nlinarith
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [Finset.sum_add_distrib]
  -- part A
  have hA : ∑ r ∈ Finset.range q, (if |m r| < 3 then H else 0) ≤ 5 * H := by
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    have hcard : ((Finset.range q).filter (fun r => |m r| < 3)).card ≤ 5 := by
      have : ((Finset.range q).filter (fun r => |m r| < 3)).card ≤ (Finset.Icc (-2 : ℤ) 2).card := by
        apply Finset.card_le_card_of_injOn m
        · intro r hr
          simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_coe, Finset.mem_Icc] at hr ⊢
          have := hr.2
          rw [abs_lt] at this
          constructor <;> omega
        · intro r hr r' hr' h
          exact hinj (Finset.mem_filter.mp (Finset.mem_coe.mp hr)).1
            (Finset.mem_filter.mp (Finset.mem_coe.mp hr')).1 h
      simpa using this
    have : ((((Finset.range q).filter (fun r => |m r| < 3)).card : ℕ) : ℝ) ≤ 5 := by exact_mod_cast hcard
    nlinarith
  -- part B
  have hB : ∑ r ∈ Finset.range q, (if 3 ≤ (m r).natAbs then (q : ℝ) / (m r).natAbs else 0)
      ≤ ∑ k ∈ Finset.range (2 * q + 1), (2 : ℝ) * (if 3 ≤ k then (q : ℝ) / k else 0) := by
    rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.range q) (t := Finset.range (2 * q + 1))
      (g := fun r => (m r).natAbs)]
    · apply Finset.sum_le_sum
      intro k hk
      have hfib : ∑ r ∈ (Finset.range q).filter (fun r => (m r).natAbs = k),
          (if 3 ≤ (m r).natAbs then (q : ℝ) / (m r).natAbs else 0)
          = (((Finset.range q).filter (fun r => (m r).natAbs = k)).card : ℝ) *
            (if 3 ≤ k then (q : ℝ) / k else 0) := by
        rw [← nsmul_eq_mul, ← Finset.sum_const]
        apply Finset.sum_congr rfl
        intro r hr
        rw [(Finset.mem_filter.mp hr).2]
      rw [hfib]
      have hcard : ((Finset.range q).filter (fun r => (m r).natAbs = k)).card ≤ 2 := by
        have : ((Finset.range q).filter (fun r => (m r).natAbs = k)).card ≤ ({(k : ℤ), -(k : ℤ)} : Finset ℤ).card := by
          apply Finset.card_le_card_of_injOn m
          · intro r hr
            have := (Finset.mem_filter.mp (Finset.mem_coe.mp hr)).2
            simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff]
            omega
          · intro r hr r' hr' h
            exact hinj (Finset.mem_filter.mp (Finset.mem_coe.mp hr)).1
              (Finset.mem_filter.mp (Finset.mem_coe.mp hr')).1 h
        exact this.trans (Finset.card_le_two)
      have hnn : 0 ≤ (if 3 ≤ k then (q : ℝ) / k else 0) := by split_ifs <;> positivity
      have : (((Finset.range q).filter (fun r => (m r).natAbs = k)).card : ℝ) ≤ 2 := by exact_mod_cast hcard
      nlinarith
    · intro r hr
      have hb := hbound r hr
      have hcn : |x + (r : ℝ) * t - round (x + (r : ℝ) * t)| ≤ 1 / 2 := abs_sub_round _
      have hqc : |(m r : ℝ)| ≤ q * |x + (r : ℝ) * t - round (x + (r : ℝ) * t)| + 3 / 2 := by
        have : (q : ℝ) * |x + (r : ℝ) * t - round (x + (r : ℝ) * t)| = |(q : ℝ) * (x + (r : ℝ) * t - n r)| := by
          rw [abs_mul, abs_of_pos hqpos]
        rw [this]
        have := abs_sub_abs_le_abs_sub (m r : ℝ) (q * (x + (r : ℝ) * t - n r))
        rw [abs_sub_comm] at this
        linarith
      have hmabs : ((m r).natAbs : ℝ) = |(m r : ℝ)| := by
        rw [Nat.cast_natAbs, Int.cast_abs]
      have : ((m r).natAbs : ℝ) < ((2 * q + 1 : ℕ) : ℝ) := by
        rw [hmabs]; push_cast; nlinarith
      simpa using (by exact_mod_cast this : (m r).natAbs < 2 * q + 1)
  have hC := rcs_psi_sum q hq
  have hlog : (1 : ℝ) / 2 ≤ Real.log (2 * q) := by
    have h2 : Real.log 2 ≤ Real.log (2 * q) := Real.log_le_log (by norm_num) (by linarith)
    have := Real.log_two_gt_d9
    linarith
  nlinarith
