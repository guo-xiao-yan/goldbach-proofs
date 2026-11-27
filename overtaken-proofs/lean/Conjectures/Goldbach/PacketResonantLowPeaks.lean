import Mathlib

open MeasureTheory

private noncomputable def PP (l : ℝ) (m : ℕ) (t : ℝ) : ℝ :=
  Real.exp (l * ∑ j ∈ Finset.range m, Real.cos (2 * Real.pi * (2:ℝ)^j * t))

private lemma PP_cont (l : ℝ) (m : ℕ) : Continuous (PP l m) := by
  unfold PP; fun_prop

private lemma PP_pos (l : ℝ) (m : ℕ) (t : ℝ) : 0 < PP l m t := Real.exp_pos _

private lemma PP_per (l : ℝ) (m : ℕ) (t : ℝ) : PP l m (t + 1) = PP l m t := by
  unfold PP
  have h : ∑ j ∈ Finset.range m, Real.cos (2 * Real.pi * (2:ℝ)^j * (t+1)) =
      ∑ j ∈ Finset.range m, Real.cos (2 * Real.pi * (2:ℝ)^j * t) := by
    refine Finset.sum_congr rfl fun j _ => ?_
    have : 2 * Real.pi * (2:ℝ)^j * (t+1) = 2 * Real.pi * (2:ℝ)^j * t + ((2^j : ℕ) : ℝ) * (2 * Real.pi) := by
      push_cast; ring
    rw [this, Real.cos_add_nat_mul_two_pi]
  rw [h]

private lemma PP_succ (l : ℝ) (m : ℕ) (t : ℝ) :
    PP l (m+1) t = Real.exp (l * Real.cos (2 * Real.pi * t)) * PP l m (2 * t) := by
  unfold PP
  rw [← Real.exp_add, Finset.sum_range_succ']
  have h : ∑ j ∈ Finset.range m, Real.cos (2 * Real.pi * (2:ℝ)^(j+1) * t) =
      ∑ j ∈ Finset.range m, Real.cos (2 * Real.pi * (2:ℝ)^j * (2 * t)) := by
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [pow_succ]; ring_nf
  rw [h]
  have h0 : Real.cos (2 * Real.pi * (2:ℝ)^0 * t) = Real.cos (2 * Real.pi * t) := by simp
  rw [h0]; ring_nf

private lemma pair_le (l : ℝ) (u : ℝ) :
    Real.exp (l * Real.cos (2 * Real.pi * (u/2))) + Real.exp (l * Real.cos (2 * Real.pi * ((u+1)/2)))
      ≤ 2 * Real.exp (l^2/2) := by
  have h1 : 2 * Real.pi * (u/2) = Real.pi * u := by ring
  have h2 : 2 * Real.pi * ((u+1)/2) = Real.pi * u + Real.pi := by ring
  rw [h1, h2, Real.cos_add_pi, mul_neg, Real.exp_neg]
  set x := l * Real.cos (Real.pi * u)
  have hc := Real.cosh_le_exp_half_sq x
  have hx : x^2/2 ≤ l^2/2 := by
    have : x^2 ≤ l^2 := by
      simp only [x, mul_pow]
      have := Real.cos_sq_le_one (Real.pi * u)
      nlinarith [sq_nonneg l]
    linarith
  have := Real.exp_le_exp.mpr hx
  rw [Real.cosh_eq] at hc
  have h3 : Real.exp x + (Real.exp x)⁻¹ = Real.exp x + Real.exp (-x) := by rw [Real.exp_neg]
  linarith

private lemma key (l : ℝ) (m : ℕ) :
    ∫ t in (0:ℝ)..1, PP l m t ≤ Real.exp (m * (l^2/2)) := by
  induction m with
  | zero => simp [PP]
  | succ m ih =>
    set g : ℝ → ℝ := fun t => Real.exp (l * Real.cos (2 * Real.pi * t)) with hg
    set f1 : ℝ → ℝ := fun s => g (s/2) * PP l m s with hf1
    have hgc : Continuous g := by simp only [hg]; fun_prop
    have hf1c : Continuous f1 := by
      simp only [hf1]; exact (hgc.comp (by fun_prop)).mul (PP_cont l m)
    have hP : ∀ t, PP l (m+1) t = f1 (2 * t) := by
      intro t
      rw [PP_succ]
      have h2 : 2 * t / 2 = t := by ring
      simp only [hf1, hg, h2]
    simp_rw [hP]
    have hsplit := intervalIntegral.integral_add_adjacent_intervals
      (f := fun t => f1 (2*t)) (μ := volume) (a := 0) (b := 1/2) (c := 1)
      ((hf1c.comp (by fun_prop)).intervalIntegrable _ _) ((hf1c.comp (by fun_prop)).intervalIntegrable _ _)
    rw [← hsplit]
    have e1 := intervalIntegral.integral_comp_mul_left (a := 0) (b := 1/2) f1 (c := 2) (by norm_num)
    have e2 := intervalIntegral.integral_comp_mul_left (a := 1/2) (b := 1) f1 (c := 2) (by norm_num)
    rw [e1, e2]
    have e3 : ∫ x in (1:ℝ)..2, f1 x = ∫ x in (0:ℝ)..1, f1 (x+1) := by
      rw [intervalIntegral.integral_comp_add_right]; norm_num
    have e4 : (2:ℝ) * (1/2) = 1 := by norm_num
    have e5 : (2:ℝ) * 1 = 2 := by norm_num
    have e6 : (2:ℝ) * 0 = 0 := by norm_num
    rw [e4, e5, e6, e3]
    simp only [smul_eq_mul]
    have e7 : ∫ x in (0:ℝ)..1, f1 (x+1) = ∫ x in (0:ℝ)..1, g ((x+1)/2) * PP l m x := by
      refine intervalIntegral.integral_congr fun x _ => ?_
      simp only [hf1]; rw [PP_per]
    rw [e7, ← mul_add, ← intervalIntegral.integral_add]
    · have : ∫ x in (0:ℝ)..1, (f1 x + g ((x+1)/2) * PP l m x)
          ≤ ∫ x in (0:ℝ)..1, (2 * Real.exp (l^2/2)) * PP l m x := by
        refine intervalIntegral.integral_mono_on (by norm_num) ?_ ?_ ?_
        · exact (hf1c.add ((hgc.comp (by fun_prop)).mul (PP_cont l m))).intervalIntegrable _ _
        · exact (continuous_const.mul (PP_cont l m)).intervalIntegrable _ _
        · intro x _
          simp only [hf1]
          rw [← add_mul]
          exact mul_le_mul_of_nonneg_right (pair_le l x) (PP_pos l m x).le
      rw [intervalIntegral.integral_const_mul] at this
      have h2 : (2⁻¹ : ℝ) * (2 * Real.exp (l^2/2) * ∫ x in (0:ℝ)..1, PP l m x)
          ≤ Real.exp (l^2/2) * Real.exp (m * (l^2/2)) := by
        have := mul_le_mul_of_nonneg_left ih (Real.exp_pos (l^2/2)).le
        nlinarith [intervalIntegral.integral_nonneg (μ := volume) (a := (0:ℝ)) (b := 1) (by norm_num) (fun x _ => (PP_pos l m x).le), Real.exp_pos (l^2/2)]
      calc _ ≤ (2⁻¹ : ℝ) * (2 * Real.exp (l^2/2) * ∫ x in (0:ℝ)..1, PP l m x) := by
            exact mul_le_mul_of_nonneg_left this (by norm_num)
        _ ≤ _ := h2
        _ = _ := by rw [← Real.exp_add]; congr 1; push_cast; ring
    · exact (hf1c).intervalIntegrable _ _
    · exact ((hgc.comp (by fun_prop)).mul (PP_cont l m)).intervalIntegrable _ _

private lemma tail (L : ℕ) :
    ∫ t in (0:ℝ)..1, ({t : ℝ | (L:ℝ)/2 < ∑ j ∈ Finset.range L, Real.cos (2 * Real.pi * (2:ℝ)^(j+1) * t)}).indicator (fun _ => (1:ℝ)) t
      ≤ Real.exp (5/8) * Real.exp (-(L:ℝ)/8) := by
  set A : Set ℝ := {t : ℝ | (L:ℝ)/2 < ∑ j ∈ Finset.range L, Real.cos (2 * Real.pi * (2:ℝ)^(j+1) * t)} with hA
  have hAm : MeasurableSet A := by
    apply measurableSet_lt measurable_const
    exact (Continuous.measurable (by fun_prop))
  have hk := key (1/2) (L+1)
  have hmono : ∫ t in (0:ℝ)..1, A.indicator (fun _ => (1:ℝ)) t
      ≤ ∫ t in (0:ℝ)..1, Real.exp (-((L:ℝ)/4 - 1/2)) * PP (1/2) (L+1) t := by
    refine intervalIntegral.integral_mono_on (by norm_num) ?_ ?_ ?_
    · rw [intervalIntegrable_iff]
      exact (integrable_indicator_iff hAm).mpr (integrableOn_const (ne_top_of_le_ne_top (b := volume (Set.Ioc (0:ℝ) 1)) (by simp) (by rw [Measure.restrict_apply hAm, Set.uIoc_of_le zero_le_one]; exact measure_mono Set.inter_subset_right)))
    · exact (continuous_const.mul (PP_cont _ _)).intervalIntegrable _ _
    · intro t _
      by_cases ht : t ∈ A
      · rw [Set.indicator_of_mem ht]
        have h1 : (L:ℝ)/2 < ∑ j ∈ Finset.range L, Real.cos (2 * Real.pi * (2:ℝ)^(j+1) * t) := ht
        have h2 : PP (1/2) (L+1) t = Real.exp (1/2 * (∑ j ∈ Finset.range L, Real.cos (2 * Real.pi * (2:ℝ)^(j+1) * t) + Real.cos (2 * Real.pi * t))) := by
          unfold PP
          rw [Finset.sum_range_succ']
          simp
        have h3 : Real.cos (2 * Real.pi * t) ≥ -1 := Real.neg_one_le_cos _
        rw [h2, ← Real.exp_add]
        apply Real.one_le_exp
        linarith
      · rw [Set.indicator_of_notMem ht]
        exact mul_nonneg (Real.exp_pos _).le (PP_pos _ _ _).le
  rw [intervalIntegral.integral_const_mul] at hmono
  have h := mul_le_mul_of_nonneg_left hk (Real.exp_pos (-((L:ℝ)/4 - 1/2))).le
  refine hmono.trans (h.trans ?_)
  rw [← Real.exp_add, ← Real.exp_add]
  apply le_of_eq; congr 1; push_cast; ring

private lemma asymR (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ x : ℝ in Filter.atTop, (1 + Real.log x)^4 * x^(-(1/32:ℝ)) ≤ δ := by
  have h1 : ∀ᶠ x : ℝ in Filter.atTop, Real.log x ≤ x^(1/256:ℝ) / 2 := by
    have := (isLittleO_log_rpow_atTop (r := 1/256) (by norm_num)).bound (c := 1/2) (by norm_num)
    filter_upwards [this, Filter.eventually_ge_atTop 1] with x hx hx1
    have hp : 0 ≤ x^(1/256:ℝ) := Real.rpow_nonneg (by linarith) _
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hp] at hx
    have := le_abs_self (Real.log x)
    linarith
  have h2 : ∀ᶠ x : ℝ in Filter.atTop, 2 ≤ x^(1/256:ℝ) :=
    (tendsto_rpow_atTop (by norm_num : (0:ℝ) < 1/256)).eventually_ge_atTop 2
  have h3 : ∀ᶠ x : ℝ in Filter.atTop, x^(-(1/64:ℝ)) ≤ δ :=
    (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ) < 1/64)).eventually_le_const hδ
  filter_upwards [h1, h2, h3, Filter.eventually_ge_atTop 1] with x a b c d
  have hx0 : 0 ≤ x := by linarith
  have hl : 0 ≤ 1 + Real.log x := by
    have := Real.log_nonneg d; linarith
  have e1 : 1 + Real.log x ≤ x^(1/256:ℝ) := by linarith
  have e2 : (1 + Real.log x)^4 ≤ x^(1/64:ℝ) := by
    calc (1 + Real.log x)^4 ≤ (x^(1/256:ℝ))^4 := pow_le_pow_left₀ hl e1 4
      _ = x^(1/64:ℝ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hx0]; norm_num
  calc (1 + Real.log x)^4 * x^(-(1/32:ℝ)) ≤ x^(1/64:ℝ) * x^(-(1/32:ℝ)) :=
        mul_le_mul_of_nonneg_right e2 (Real.rpow_nonneg hx0 _)
    _ = x^(-(1/64:ℝ)) := by rw [← Real.rpow_add (by linarith)]; norm_num
    _ ≤ δ := c

private lemma Lbound (n : ℕ) (hn : 1 ≤ n) :
    Real.log n / 2 - 1 ≤ (max 1 (Nat.log 2 n / 2) : ℕ) := by
  have h1 : (n:ℝ) < 2^(Nat.log 2 n + 1) := by exact_mod_cast Nat.lt_pow_succ_log_self (by norm_num) n
  have h2 : Real.log n < (Nat.log 2 n + 1 : ℕ) * Real.log 2 := by
    have := Real.log_lt_log (by positivity) h1
    rwa [Real.log_pow] at this
  have h3 : Real.log 2 < 1 := by have := Real.log_two_lt_d9; linarith
  have h4 : ((Nat.log 2 n : ℕ):ℝ) ≤ 2 * ((Nat.log 2 n / 2 : ℕ):ℝ) + 1 := by
    have := Nat.lt_mul_div_succ (Nat.log 2 n) (by norm_num : 0 < 2)
    have : Nat.log 2 n ≤ 2 * (Nat.log 2 n / 2) + 1 := by omega
    exact_mod_cast this
  have h5 : ((Nat.log 2 n / 2 : ℕ):ℝ) ≤ (max 1 (Nat.log 2 n / 2) : ℕ) := by
    exact_mod_cast le_max_right _ _
  have h6 : Real.log n < (Nat.log 2 n : ℝ) + 1 := by
    push_cast at h2
    nlinarith [Nat.cast_nonneg (α := ℝ) (Nat.log 2 n), Real.log_pos (by norm_num : (1:ℝ) < 2)]
  linarith

private lemma asymN (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n ≥ N, Real.exp (5/8) * Real.exp (-((max 1 (Nat.log 2 n / 2) : ℕ):ℝ)/8) *
      ((2:ℝ)^((max 1 (Nat.log 2 n / 2)) / 16) * ((n:ℝ) * (1 + Real.log n)^4)) ≤ ε * n := by
  set δ := ε / Real.exp (5/8 + 1/16) with hδ
  have hδp : 0 < δ := div_pos hε (Real.exp_pos _)
  obtain ⟨N0, hN0⟩ := Filter.eventually_atTop.mp (asymR δ hδp)
  refine ⟨max 1 (⌈N0⌉₊), fun n hn => ?_⟩
  have hn1 : 1 ≤ n := le_trans (le_max_left _ _) hn
  have hnR : N0 ≤ (n:ℝ) := le_trans (Nat.le_ceil N0) (by exact_mod_cast le_trans (le_max_right _ _) hn)
  have hnpos : (0:ℝ) < n := by exact_mod_cast hn1
  have hk := hN0 n hnR
  set L := max 1 (Nat.log 2 n / 2) with hL
  have hLb := Lbound n hn1
  have e2 : (2:ℝ)^(L/16) ≤ Real.exp ((L:ℝ)/16) := by
    have h3 : Real.log 2 < 1 := by have := Real.log_two_lt_d9; linarith
    have : (2:ℝ)^(L/16) = Real.exp (((L/16 : ℕ):ℝ) * Real.log 2) := by
      rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by norm_num), mul_comm]
    rw [this]
    apply Real.exp_le_exp.mpr
    have h4 : ((L/16 : ℕ):ℝ) ≤ (L:ℝ)/16 := Nat.cast_div_le
    have h5 : (0:ℝ) ≤ ((L/16 : ℕ):ℝ) := Nat.cast_nonneg _
    nlinarith
  have e3 : Real.exp (-(L:ℝ)/8) * Real.exp ((L:ℝ)/16) ≤ Real.exp (1/16) * (n:ℝ)^(-(1/32:ℝ)) := by
    rw [← Real.exp_add]
    have : (n:ℝ)^(-(1/32:ℝ)) = Real.exp (-(1/32) * Real.log n) := by
      rw [Real.rpow_def_of_pos hnpos]; ring_nf
    rw [this, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    linarith
  have hP : 0 ≤ (n:ℝ) * (1 + Real.log n)^4 := by
    have : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn1)
    positivity
  have key2 : Real.exp (5/8) * Real.exp (-(L:ℝ)/8) * ((2:ℝ)^(L/16) * ((n:ℝ) * (1 + Real.log n)^4))
      ≤ Real.exp (5/8) * (Real.exp (-(L:ℝ)/8) * Real.exp ((L:ℝ)/16)) * ((n:ℝ) * (1 + Real.log n)^4) := by
    have := mul_le_mul_of_nonneg_left e2 (Real.exp_pos (-(L:ℝ)/8)).le
    have := mul_le_mul_of_nonneg_right this hP
    nlinarith [Real.exp_pos (5/8)]
  refine key2.trans ?_
  have := mul_le_mul_of_nonneg_left e3 (Real.exp_pos (5/8)).le
  have := mul_le_mul_of_nonneg_right this hP
  refine this.trans ?_
  have hE : Real.exp (5/8) * Real.exp (1/16) = Real.exp (5/8 + 1/16) := (Real.exp_add _ _).symm
  have : Real.exp (5/8 + 1/16) * ((1 + Real.log n)^4 * (n:ℝ)^(-(1/32:ℝ))) ≤ ε := by
    have := mul_le_mul_of_nonneg_left hk (Real.exp_pos (5/8 + 1/16)).le
    rw [hδ, mul_div_cancel₀ _ (Real.exp_pos _).ne'] at this
    exact this
  calc Real.exp (5/8) * (Real.exp (1/16) * (n:ℝ)^(-(1/32:ℝ))) * ((n:ℝ) * (1 + Real.log n)^4)
      = (Real.exp (5/8) * Real.exp (1/16)) * ((1 + Real.log n)^4 * (n:ℝ)^(-(1/32:ℝ))) * n := by ring
    _ = Real.exp (5/8 + 1/16) * ((1 + Real.log n)^4 * (n:ℝ)^(-(1/32:ℝ))) * n := by rw [hE]
    _ ≤ ε * n := mul_le_mul_of_nonneg_right this hnpos.le

theorem Conjectures.Goldbach.PacketResonantLowPeaks :
    let w := fun k : ℕ => if Nat.Prime k then Real.log (k:ℝ) else 0; let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let S := fun (n : ℕ) (w : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (w k:ℂ)*E ((k:ℝ)*t)); let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let arcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (Q n:ℝ)/((q:ℝ)*(n:ℝ))}; let low := fun (n k : ℕ) => if k^3≤n then w k else 0; let high := fun (n k : ℕ) => w k-low n k; let L := fun n : ℕ => max 1 (Nat.log 2 n / 2); let K := fun (n : ℕ) (t : ℝ) => (∑ j ∈ Finset.range (L n), Real.cos (2*Real.pi*(2:ℝ)^(j+1)*t))/(L n:ℝ); let B := fun n : ℕ => {t : ℝ | t ∉ arcs n ∧ (1:ℝ)/2 < K n t}; let F := fun (n : ℕ) (t : ℝ) => ‖S n (high n) t‖^2; let T := fun n : ℕ => (n:ℝ)*(1+Real.log (n:ℝ))^4; let m := fun (s : Set ℝ) (f : ℝ → ℝ) => intervalIntegral (s.indicator f) (0:ℝ) 1 MeasureTheory.volume; ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, m (B n ∩ {t : ℝ | F n t ≤ (2:ℝ)^(L n / 16)*T n}) (F n) ≤ ε*(n:ℝ) := by
  intro w E S Q arcs low high L K B F T m ε hε
  obtain ⟨N, hN⟩ := asymN ε hε
  refine ⟨N, fun n hn => ?_⟩
  have hLpos : (0:ℝ) < (L n : ℝ) := by
    have : 1 ≤ L n := le_max_left _ _
    exact_mod_cast this
  set A : Set ℝ := {t : ℝ | ((L n : ℕ):ℝ)/2 < ∑ j ∈ Finset.range (L n), Real.cos (2 * Real.pi * (2:ℝ)^(j+1) * t)} with hA
  have hAm : MeasurableSet A := by
    apply measurableSet_lt measurable_const
    exact (Continuous.measurable (by fun_prop))
  set C : ℝ := (2:ℝ)^(L n / 16) * T n with hC
  have hC0 : 0 ≤ C := by
    have : 0 ≤ T n := by
      show 0 ≤ (n:ℝ)*(1+Real.log (n:ℝ))^4
      positivity
    positivity
  have hI : IntervalIntegrable (fun t => C * A.indicator (fun _ => (1:ℝ)) t) MeasureTheory.volume 0 1 := by
    apply IntervalIntegrable.const_mul
    rw [intervalIntegrable_iff]
    exact (integrable_indicator_iff hAm).mpr (integrableOn_const (ne_top_of_le_ne_top (b := MeasureTheory.volume (Set.Ioc (0:ℝ) 1)) (by simp) (by rw [MeasureTheory.Measure.restrict_apply hAm, Set.uIoc_of_le zero_le_one]; exact MeasureTheory.measure_mono Set.inter_subset_right)))
  have h1 : m (B n ∩ {t : ℝ | F n t ≤ (2:ℝ)^(L n / 16)*T n}) (F n) ≤ ∫ t in (0:ℝ)..1, C * A.indicator (fun _ => (1:ℝ)) t := by
    refine le_trans (le_abs_self _) ?_
    refine le_trans (le_of_eq (Real.norm_eq_abs _).symm) ?_
    refine intervalIntegral.norm_integral_le_of_norm_le zero_le_one ?_ hI
    refine Filter.Eventually.of_forall fun t _ => ?_
    by_cases ht : t ∈ B n ∩ {t : ℝ | F n t ≤ (2:ℝ)^(L n / 16)*T n}
    · rw [Set.indicator_of_mem ht]
      have hF0 : 0 ≤ F n t := by show 0 ≤ ‖_‖^2; positivity
      have hA' : t ∈ A := by
        have h := ht.1.2
        have h' : (1:ℝ)/2 < (∑ j ∈ Finset.range (L n), Real.cos (2*Real.pi*(2:ℝ)^(j+1)*t))/(L n:ℝ) := h
        rw [lt_div_iff₀ hLpos] at h'
        have h'' : ((L n : ℕ):ℝ)/2 < ∑ j ∈ Finset.range (L n), Real.cos (2*Real.pi*(2:ℝ)^(j+1)*t) := by linarith
        exact h''
      rw [Set.indicator_of_mem hA', mul_one, Real.norm_eq_abs, abs_of_nonneg hF0]
      exact ht.2
    · rw [Set.indicator_of_notMem ht]
      have : 0 ≤ C * A.indicator (fun _ => (1:ℝ)) t := by
        apply mul_nonneg hC0
        apply Set.indicator_nonneg; intros; norm_num
      simpa using this
  refine h1.trans ?_
  rw [intervalIntegral.integral_const_mul]
  have h2 := tail (L n)
  have h3 := hN n hn
  have h4 := mul_le_mul_of_nonneg_left h2 hC0
  refine h4.trans ?_
  have : C * (Real.exp (5/8) * Real.exp (-((L n : ℕ):ℝ)/8)) = Real.exp (5/8) * Real.exp (-((max 1 (Nat.log 2 n / 2) : ℕ):ℝ)/8) *
      ((2:ℝ)^((max 1 (Nat.log 2 n / 2)) / 16) * ((n:ℝ) * (1 + Real.log n)^4)) := by
    simp only [hC, T, L]; ring
  rw [this]; exact h3
