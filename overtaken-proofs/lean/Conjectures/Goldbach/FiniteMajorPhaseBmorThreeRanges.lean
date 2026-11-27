import Mathlib

private lemma bmor3_abel (a e : ℕ → ℂ) (n : ℕ) :
    ∑ k ∈ Finset.Icc 1 n, a k * e k =
      (∑ k ∈ Finset.Icc 1 n, a k) * e n -
        ∑ m ∈ Finset.range n, (∑ k ∈ Finset.Icc 1 m, a k) * (e (m+1) - e m) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega), Finset.sum_Icc_succ_top (by omega),
      Finset.sum_range_succ, ih]
    ring

private lemma bmor3_sum_id (N : ℕ) : ∑ m ∈ Finset.range N, (m:ℝ) ≤ (N:ℝ)^2/2 := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ]
    push_cast
    nlinarith

private lemma bmor3_ite_le (N n : ℕ) (c : ℝ) (hc : 0 ≤ c) :
    ∑ m ∈ Finset.range n, (if m < N then c * (m:ℝ) else 0) ≤ c * ((N:ℝ)^2/2) := by
  rw [← Finset.sum_filter]
  calc ∑ m ∈ (Finset.range n).filter (fun m => m < N), c * (m:ℝ)
      ≤ ∑ m ∈ Finset.range N, c * (m:ℝ) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro m hm
          simp only [Finset.mem_filter, Finset.mem_range] at hm ⊢
          exact hm.2
        · intro i _ _
          positivity
    _ = c * ∑ m ∈ Finset.range N, (m:ℝ) := by rw [Finset.mul_sum]
    _ ≤ c * ((N:ℝ)^2/2) := by
        apply mul_le_mul_of_nonneg_left (bmor3_sum_id N) hc

private lemma bmor3_exp_diff (x β : ℝ) :
    ‖Complex.exp (((2*Real.pi*(x+β):ℝ):ℂ)*Complex.I) - Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I)‖
      ≤ 2*Real.pi*|β| := by
  have h1 : Complex.exp (((2*Real.pi*(x+β):ℝ):ℂ)*Complex.I) =
      Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I) * Complex.exp (((2*Real.pi*β:ℝ):ℂ)*Complex.I) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have h2 : Complex.exp (((2*Real.pi*(x+β):ℝ):ℂ)*Complex.I) - Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I)
      = Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I) *
        (Complex.exp (Complex.I * ((2*Real.pi*β:ℝ):ℂ)) - 1) := by
    rw [h1, mul_sub, mul_comm Complex.I]
    ring
  rw [h2, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
  refine le_trans Real.norm_exp_I_mul_ofReal_sub_one_le ?_
  rw [Real.norm_eq_abs, abs_mul, abs_mul]
  simp [abs_of_pos Real.pi_pos]

private lemma bmor3_log_ge_42 (n : ℕ) (hn : 4000000000000000000 ≤ n) : (42:ℝ) ≤ Real.log (n:ℝ) := by
  have h1 : Real.exp 42 < 4000000000000000000 := by
    have := Real.exp_one_lt_d9
    have h : Real.exp 42 = (Real.exp 1)^42 := by rw [← Real.exp_nat_mul]; norm_num
    rw [h]
    calc (Real.exp 1)^42 ≤ (2.7182818286:ℝ)^42 := by gcongr
      _ < 4000000000000000000 := by norm_num
  have h2 : (4000000000000000000:ℝ) ≤ n := by exact_mod_cast hn
  exact ((Real.le_log_iff_exp_le (by linarith)).2 (by linarith))

private lemma bmor3_log_ge_34 (n : ℕ) (hn : 600000000000000 ≤ n) : (34:ℝ) ≤ Real.log (n:ℝ) := by
  have h1 : Real.exp 34 < 600000000000000 := by
    have := Real.exp_one_lt_d9
    have h : Real.exp 34 = (Real.exp 1)^34 := by rw [← Real.exp_nat_mul]; norm_num
    rw [h]
    calc (Real.exp 1)^34 ≤ (2.7182818286:ℝ)^34 := by gcongr
      _ < 600000000000000 := by norm_num
  have h2 : (600000000000000:ℝ) ≤ n := by exact_mod_cast hn
  exact ((Real.le_log_iff_exp_le (by linarith)).2 (by linarith))

private lemma bmor3_log_ge_22 (n : ℕ) (hn : 8000000000 ≤ n) : (22:ℝ) ≤ Real.log (n:ℝ) := by
  have h1 : Real.exp 22 < 8000000000 := by
    have := Real.exp_one_lt_d9
    have h : Real.exp 22 = (Real.exp 1)^22 := by rw [← Real.exp_nat_mul]; norm_num
    rw [h]
    calc (Real.exp 1)^22 ≤ (2.7182818286:ℝ)^22 := by gcongr
      _ < 8000000000 := by norm_num
  have h2 : (8000000000:ℝ) ≤ n := by exact_mod_cast hn
  exact ((Real.le_log_iff_exp_le (by linarith)).2 (by linarith))

private lemma bmor3_log_le_23 (n : ℕ) (hn : n < 8000000000) : Real.log (n:ℝ) ≤ 23 := by
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; simp
  have h1 : (8000000000:ℝ) < Real.exp 23 := by
    have := Real.exp_one_gt_d9
    have h : Real.exp 23 = (Real.exp 1)^23 := by rw [← Real.exp_nat_mul]; norm_num
    rw [h]
    calc (8000000000:ℝ) < (2.7182818283:ℝ)^23 := by norm_num
      _ ≤ (Real.exp 1)^23 := by gcongr
  have h2 : (n:ℝ) < 8000000000 := by exact_mod_cast hn
  have h3 : (0:ℝ) < n := by exact_mod_cast h
  exact ((Real.log_le_iff_le_exp h3).2 (by linarith))

private lemma bmor3_icc_eq_range (g : ℕ → ℝ) (h0 : g 0 = 0) (m : ℕ) :
    ∑ k ∈ Finset.Icc 1 m, g k = ∑ k ∈ Finset.range (m+1), g k := by
  induction m with
  | zero => simp [h0]
  | succ m ih => rw [Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_range_succ _ (m+1)]

private lemma bmor3_hsum (q a m : ℕ) (ha : a < q) :
    ∑ k ∈ Finset.Icc 1 m, ((if k % q = a then ArithmeticFunction.vonMangoldt k else 0) - 1/(Nat.totient q:ℝ))
      = (∑ k ∈ (Finset.range (m+1)).filter (fun k => k % q = a % q), ArithmeticFunction.vonMangoldt k)
        - (m:ℝ)/Nat.totient q := by
  rw [Finset.sum_sub_distrib]
  congr 1
  · rw [bmor3_icc_eq_range (fun k => if k % q = a then ArithmeticFunction.vonMangoldt k else 0)
      (by simp), Finset.sum_filter, Nat.mod_eq_of_lt ha]
  · simp [div_eq_mul_inv]

private lemma bmor3_pm_bound
    (H : ∀ (q a m : ℕ), 3 ≤ q → q ≤ 105 → a < q → Nat.Coprime a q → 8000000000 ≤ m →
      |(∑ k ∈ (Finset.range (m+1)).filter (fun k => k % q = a % q), ArithmeticFunction.vonMangoldt k)
        - (m:ℝ)/Nat.totient q| ≤ (m:ℝ)/(840*Real.log (m:ℝ)))
    (q a : ℕ) (hq3 : 3 ≤ q) (hq105 : q ≤ 105) (ha : a < q) (hcop : Nat.Coprime a q) (m : ℕ) :
    |∑ k ∈ Finset.Icc 1 m, ((if k % q = a then ArithmeticFunction.vonMangoldt k else 0) - 1/(Nat.totient q:ℝ))|
      ≤ (if m < 8000000000 then 48 * (m:ℝ) else 0) + (if m < 600000000000000 then (1/(840*22)) * (m:ℝ) else 0)
        + (1/(840*34)) * (m:ℝ) := by
  have hphi : (1:ℝ) ≤ Nat.totient q := by
    have : 0 < Nat.totient q := Nat.totient_pos.2 (by omega)
    exact_mod_cast this
  have hsum : ∑ k ∈ Finset.Icc 1 m, ((if k % q = a then ArithmeticFunction.vonMangoldt k else 0) - 1/(Nat.totient q:ℝ))
      = (∑ k ∈ (Finset.range (m+1)).filter (fun k => k % q = a % q), ArithmeticFunction.vonMangoldt k)
        - (m:ℝ)/Nat.totient q := by
    rw [Finset.sum_sub_distrib]
    congr 1
    · rw [bmor3_icc_eq_range (fun k => if k % q = a then ArithmeticFunction.vonMangoldt k else 0)
        (by simp), Finset.sum_filter, Nat.mod_eq_of_lt ha]
    · simp [div_eq_mul_inv]
  rw [hsum]
  have hm0 : (0:ℝ) ≤ m := Nat.cast_nonneg m
  have hnn : (0:ℝ) ≤ (if m < 600000000000000 then (1/(840*22)) * (m:ℝ) else 0) := by
    split_ifs <;> positivity
  have hnn1 : (0:ℝ) ≤ (if m < 8000000000 then 48 * (m:ℝ) else 0) := by
    split_ifs <;> positivity
  have hnn2 : (0:ℝ) ≤ (1/(840*34)) * (m:ℝ) := by positivity
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    simp [Finset.sum_filter]
  by_cases h1 : m < 8000000000
  · simp only [h1, ite_true]
    have hl := bmor3_log_le_23 m h1
    have hlm : 0 ≤ Real.log (m:ℝ) := Real.log_natCast_nonneg m
    have hm1 : (1:ℝ) ≤ m := by exact_mod_cast hm
    have hA : 0 ≤ ∑ k ∈ (Finset.range (m+1)).filter (fun k => k % q = a % q), ArithmeticFunction.vonMangoldt k :=
      Finset.sum_nonneg (fun k _ => ArithmeticFunction.vonMangoldt_nonneg)
    have hA2 : ∑ k ∈ (Finset.range (m+1)).filter (fun k => k % q = a % q), ArithmeticFunction.vonMangoldt k
        ≤ ((m:ℝ)+1) * Real.log m := by
      calc _ ≤ ∑ k ∈ (Finset.range (m+1)).filter (fun k => k % q = a % q), Real.log (m:ℝ) := by
            apply Finset.sum_le_sum
            intro k hk
            have hk' : k ≤ m := by
              have := (Finset.mem_filter.1 hk).1
              simp only [Finset.mem_range] at this
              omega
            refine le_trans ArithmeticFunction.vonMangoldt_le_log ?_
            rcases Nat.eq_zero_or_pos k with h0 | h0
            · subst h0; simpa using hlm
            · exact Real.log_le_log (by exact_mod_cast h0) (by exact_mod_cast hk')
        _ ≤ ((Finset.range (m+1)).card : ℝ) * Real.log m := by
            rw [Finset.sum_const, nsmul_eq_mul]
            apply mul_le_mul_of_nonneg_right
            · exact_mod_cast Finset.card_filter_le _ _
            · exact hlm
        _ = _ := by simp
    have hB : (m:ℝ)/Nat.totient q ≤ m := div_le_self hm0 hphi
    have hB0 : 0 ≤ (m:ℝ)/Nat.totient q := by positivity
    have hC : ((m:ℝ)+1) * Real.log m ≤ 46 * m := by nlinarith
    rw [abs_le]
    constructor <;> nlinarith
  · simp only [h1, ite_false]
    have h1' : 8000000000 ≤ m := by omega
    have hH := H q a m hq3 hq105 ha hcop h1'
    refine le_trans hH ?_
    have hl22 := bmor3_log_ge_22 m h1'
    by_cases h2 : m < 600000000000000
    · simp only [h2, ite_true]
      have : (m:ℝ)/(840*Real.log m) ≤ (m:ℝ)/(840*22) := by
        apply div_le_div_of_nonneg_left hm0 (by norm_num) (by linarith)
      have e : (1/(840*22):ℝ) * m = (m:ℝ)/(840*22) := by ring
      linarith
    · simp only [h2, ite_false]
      have h2' : 600000000000000 ≤ m := by omega
      have hl34 := bmor3_log_ge_34 m h2'
      have : (m:ℝ)/(840*Real.log m) ≤ (m:ℝ)/(840*34) := by
        apply div_le_div_of_nonneg_left hm0 (by norm_num) (by linarith)
      have e : (1/(840*34):ℝ) * m = (m:ℝ)/(840*34) := by ring
      linarith

theorem Conjectures.Goldbach.FiniteMajorPhaseBmorThreeRanges :
    (∀ (q a m : ℕ), 3 ≤ q → q ≤ 105 → a < q → Nat.Coprime a q → 8000000000 ≤ m → |(∑ k ∈ (Finset.range (m+1)).filter (fun k => k % q = a % q), ArithmeticFunction.vonMangoldt k) - (m:ℝ)/Nat.totient q| ≤ (m:ℝ)/(840*Real.log (m:ℝ))) → let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); ∀ (q a n : ℕ) (β : ℝ), 3≤q → q≤105 → a<q → Nat.Coprime a q → 4000000000000000000≤n → |β|≤105/(n:ℝ) → ‖∑ k ∈ Finset.Icc 1 n, (((if k % q = a then ArithmeticFunction.vonMangoldt k else 0) - 1/(Nat.totient q:ℝ):ℝ):ℂ)*E ((k:ℝ)*β)‖ ≤ (n:ℝ)*(1/(10^9:ℝ)+1/(840*42)) + Real.pi * |β| * (n:ℝ)^2/(840*34) := by
  intro H E q a n β hq3 hq105 ha hcop hn hβ
  have hn0 : (0:ℝ) < n := by
    have : (4000000000000000000:ℝ) ≤ n := by exact_mod_cast hn
    linarith
  set cr : ℕ → ℝ := fun k => (if k % q = a then ArithmeticFunction.vonMangoldt k else 0) - 1/(Nat.totient q:ℝ) with hcr
  set P : ℕ → ℝ := fun m => ∑ k ∈ Finset.Icc 1 m, cr k with hP
  have hab := bmor3_abel (fun k => ((cr k:ℝ):ℂ)) (fun k => E ((k:ℝ)*β)) n
  have hPc : ∀ m, ∑ k ∈ Finset.Icc 1 m, ((cr k:ℝ):ℂ) = ((P m:ℝ):ℂ) := by
    intro m
    simp only [hP]
    push_cast
    rfl
  simp only [hPc] at hab
  have hEn : ∀ x : ℝ, ‖E x‖ = 1 := by
    intro x
    simp only [E]
    exact Complex.norm_exp_ofReal_mul_I _
  have hdiff : ∀ m : ℕ, ‖E (((m+1:ℕ):ℝ)*β) - E ((m:ℝ)*β)‖ ≤ 2*Real.pi*|β| := by
    intro m
    have h := bmor3_exp_diff ((m:ℝ)*β) β
    have e : ((m+1:ℕ):ℝ)*β = (m:ℝ)*β+β := by push_cast; ring
    simp only [E]
    rw [e]
    exact h
  have hpi : Real.pi < 3.15 := Real.pi_lt_d2
  have hpi0 : 0 < Real.pi := Real.pi_pos
  have hgoal_eq : ∑ k ∈ Finset.Icc 1 n, (((if k % q = a then ArithmeticFunction.vonMangoldt k else 0) - 1/(Nat.totient q:ℝ):ℝ):ℂ) * E ((k:ℝ)*β)
      = ∑ k ∈ Finset.Icc 1 n, ((cr k:ℝ):ℂ) * E ((k:ℝ)*β) := rfl
  rw [hgoal_eq, hab]
  let g : ℕ → ℝ := fun m => (if m < 8000000000 then 48 * (m:ℝ) else 0)
      + (if m < 600000000000000 then (1/(840*22)) * (m:ℝ) else 0) + (1/(840*34)) * (m:ℝ)
  have hPg : ∀ m, |P m| ≤ g m := fun m =>
    bmor3_pm_bound H q a hq3 hq105 ha hcop m
  have hPn : |P n| ≤ (n:ℝ)/(840*42) := by
    have h1 : P n = (∑ k ∈ (Finset.range (n+1)).filter (fun k => k % q = a % q), ArithmeticFunction.vonMangoldt k)
        - (n:ℝ)/Nat.totient q := bmor3_hsum q a n ha
    rw [h1]
    have hH := H q a n hq3 hq105 ha hcop (by omega)
    refine le_trans hH ?_
    have hl := bmor3_log_ge_42 n hn
    apply div_le_div_of_nonneg_left hn0.le (by norm_num) (by linarith)
  have hsumS : ∑ m ∈ Finset.range n, g m ≤
      48 * ((8000000000:ℕ)^2/2 : ℝ) + (1/(840*22)) * ((600000000000000:ℕ)^2/2 : ℝ)
        + (1/(840*34)) * ((n:ℝ)^2/2) := by
    have e1 := bmor3_ite_le 8000000000 n 48 (by norm_num)
    have e2 := bmor3_ite_le 600000000000000 n (1/(840*22)) (by norm_num)
    have e3 : ∑ m ∈ Finset.range n, (1/(840*34):ℝ) * (m:ℝ) ≤ (1/(840*34)) * ((n:ℝ)^2/2) := by
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left (bmor3_sum_id n) (by norm_num)
    simp only [g, Finset.sum_add_distrib]
    push_cast at e1 e2 ⊢
    linarith
  have hnorm : ‖(P n:ℂ) * E ((n:ℝ)*β) - ∑ m ∈ Finset.range n, (P m:ℂ) * (E (((m+1:ℕ):ℝ)*β) - E ((m:ℝ)*β))‖
      ≤ |P n| + (2*Real.pi*|β|) * ∑ m ∈ Finset.range n, g m := by
    refine le_trans (norm_sub_le _ _) ?_
    have h1 : ‖(P n:ℂ) * E ((n:ℝ)*β)‖ = |P n| := by
      rw [norm_mul, hEn, mul_one, Complex.norm_real, Real.norm_eq_abs]
    rw [h1]
    gcongr
    refine le_trans (norm_sum_le _ _) ?_
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro m _
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_comm]
    exact mul_le_mul (hdiff m) (hPg m) (abs_nonneg _) (by positivity)
  refine le_trans hnorm ?_
  have hb0 : 0 ≤ 2*Real.pi*|β| := by positivity
  have hmul := mul_le_mul_of_nonneg_left hsumS hb0
  have hT : 2*Real.pi*|β| * (48 * ((8000000000:ℕ)^2/2 : ℝ) + (1/(840*22)) * ((600000000000000:ℕ)^2/2 : ℝ))
      ≤ (n:ℝ)/10^9 := by
    have hx : |β| * n ≤ 105 := by
      have := mul_le_mul_of_nonneg_right hβ hn0.le
      rwa [div_mul_cancel₀ _ hn0.ne'] at this
    have hn2 : (4000000000000000000:ℝ) ≤ n := by exact_mod_cast hn
    have hx0 : 0 ≤ |β| * n := by positivity
    set T0 : ℝ := 48 * ((8000000000:ℕ)^2/2 : ℝ) + (1/(840*22)) * ((600000000000000:ℕ)^2/2 : ℝ) with hT0
    have hT0v : T0 ≤ 10^25 := by rw [hT0]; norm_num
    have hT00 : 0 ≤ T0 := by rw [hT0]; positivity
    rw [← mul_le_mul_iff_of_pos_right hn0]
    have e : 2*Real.pi*|β| * T0 * n = 2*Real.pi*(|β| * n)*T0 := by ring
    rw [e]
    have h1 : 2*Real.pi*(|β| * n)*T0 ≤ 2*3.15*105*10^25 := by
      have a1 : 2*Real.pi*(|β| * n) ≤ 2*3.15*105 := by nlinarith
      have a2 : 0 ≤ 2*Real.pi*(|β| * n) := by positivity
      calc _ ≤ (2*3.15*105) * T0 := mul_le_mul_of_nonneg_right a1 hT00
        _ ≤ _ := by nlinarith
    have h2 : (n:ℝ)/10^9 * n = (n:ℝ)*n/10^9 := by ring
    rw [h2]
    have : (16000000000000000000000000000000000000:ℝ) ≤ (n:ℝ)*n := by nlinarith
    nlinarith
  have hfin : (n:ℝ)/(840*42) + 2*Real.pi*|β| * (48 * ((8000000000:ℕ)^2/2 : ℝ) + (1/(840*22)) * ((600000000000000:ℕ)^2/2 : ℝ)
        + (1/(840*34)) * ((n:ℝ)^2/2)) ≤ (n:ℝ)*(1/(10^9:ℝ)+1/(840*42)) + Real.pi * |β| * (n:ℝ)^2/(840*34) := by
    nlinarith
  linarith
