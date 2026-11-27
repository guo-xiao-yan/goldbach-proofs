import Mathlib

private lemma gbk_norm_E (E : ℝ → ℂ)
    (hE : ∀ x, E x = Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I)) (x : ℝ) : ‖E x‖ = 1 := by
  rw [hE]; exact Complex.norm_exp_ofReal_mul_I _

private lemma gbk_E_add (E : ℝ → ℂ)
    (hE : ∀ x, E x = Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I)) (a b : ℝ) :
    E (a+b) = E a * E b := by
  rw [hE, hE, hE, ← Complex.exp_add]; congr 1; push_cast; ring

private lemma gbk_E_cont (E : ℝ → ℂ)
    (hE : ∀ x, E x = Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I)) : Continuous E := by
  have : E = fun x => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I) := funext hE
  rw [this]; fun_prop

private lemma gbk_E_lip (E : ℝ → ℂ)
    (hE : ∀ x, E x = Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I)) (x y : ℝ) :
    ‖E x - E y‖ ≤ 2*Real.pi*|x-y| := by
  have h1 : E x = E y * E (x-y) := by
    rw [← gbk_E_add E hE]; congr 1; ring
  have h2 : E x - E y = E y * (E (x-y) - 1) := by rw [h1]; ring
  rw [h2, norm_mul, gbk_norm_E E hE, one_mul]
  have h3 : E (x-y) = Complex.exp (Complex.I * ((2*Real.pi*(x-y):ℝ):ℂ)) := by
    rw [hE, mul_comm]
  rw [h3]
  have := Real.norm_exp_I_mul_ofReal_sub_one_le (x := 2*Real.pi*(x-y))
  refine this.trans (le_of_eq ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2*Real.pi)]

private theorem gbk_reindex (F : ℕ → ℂ) (n : ℕ) :
    ∑ k ∈ Finset.Icc 1 n, F k = ∑ k ∈ Finset.range n, F (k + 1) := by
  induction n with
  | zero => simp
  | succ m ih => rw [Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_range_succ]

private theorem gbk_term (h : ℝ → ℂ) (hc : Continuous h) (Lc : ℝ)
    (hL : ∀ x y, ‖h x - h y‖ ≤ Lc * |x - y|)
    (n : ℕ) (hn' : (0:ℝ) < n) (k : ℕ) (hk : k < n) :
    ‖h (((k + 1 : ℕ) : ℝ) / n) / (n:ℂ) - ∫ u in ((k:ℝ) / n)..(((k + 1 : ℕ) : ℝ) / n), h u‖
      ≤ Lc / (n:ℝ)^2 := by
  have hk0 : (0:ℝ) ≤ k := Nat.cast_nonneg k
  have hab : (k:ℝ) / n ≤ ((k + 1 : ℕ) : ℝ) / n := by
    push_cast
    exact div_le_div_of_nonneg_right (by linarith) hn'.le
  have hba : ((k + 1 : ℕ) : ℝ) / n - (k:ℝ) / n = 1 / n := by
    push_cast; field_simp; ring
  have e : h (((k + 1 : ℕ) : ℝ) / n) / (n:ℂ) - ∫ u in ((k:ℝ) / n)..(((k + 1 : ℕ) : ℝ) / n), h u
      = ∫ u in ((k:ℝ) / n)..(((k + 1 : ℕ) : ℝ) / n), (h (((k + 1 : ℕ) : ℝ) / n) - h u) := by
    rw [intervalIntegral.integral_sub intervalIntegrable_const (hc.intervalIntegrable _ _),
      intervalIntegral.integral_const, hba, Complex.real_smul]
    push_cast
    ring
  rw [e]
  have hLc : 0 ≤ Lc := by
    have := hL 0 1
    rw [show |(0:ℝ) - 1| = 1 by norm_num, mul_one] at this
    linarith [norm_nonneg (h 0 - h 1)]
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (k:ℝ) / n) (b := ((k + 1 : ℕ) : ℝ) / n)
    (f := fun u => h (((k + 1 : ℕ) : ℝ) / n) - h u) (C := Lc / n) (by
      intro u hu
      rw [Set.uIoc_of_le hab] at hu
      obtain ⟨hu1, hu2⟩ := hu
      have h1 := hL (((k + 1 : ℕ) : ℝ) / n) u
      have h2 : |((k + 1 : ℕ) : ℝ) / n - u| ≤ 1 / n := by
        rw [abs_of_nonneg (by linarith)]
        linarith
      calc _ ≤ Lc * |((k + 1 : ℕ) : ℝ) / n - u| := h1
        _ ≤ Lc * (1 / n) := mul_le_mul_of_nonneg_left h2 hLc
        _ = Lc / n := by ring)
  have : |((k + 1 : ℕ) : ℝ) / n - (k:ℝ) / n| = 1 / n := by
    rw [abs_of_nonneg (by linarith)]; exact hba
  rw [this] at hb
  calc _ ≤ _ := hb
    _ = Lc / (n:ℝ)^2 := by field_simp

private theorem gbk_riemann (h : ℝ → ℂ) (hc : Continuous h) (Lc : ℝ)
    (hL : ∀ x y, ‖h x - h y‖ ≤ Lc * |x - y|) (n : ℕ) (hn : 1 ≤ n) :
    ‖(∑ k ∈ Finset.Icc 1 n, h ((k:ℝ) / n)) / (n:ℂ) - ∫ u in (0:ℝ)..1, h u‖ ≤ Lc / n := by
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  have h1 : ∫ u in (0:ℝ)..1, h u
      = ∑ k ∈ Finset.range n, ∫ u in ((k:ℝ) / n)..(((k + 1 : ℕ) : ℝ) / n), h u := by
    have := intervalIntegral.sum_integral_adjacent_intervals (f := h)
      (μ := MeasureTheory.volume) (a := fun k : ℕ => (k:ℝ) / n) (n := n)
      (fun k _ => hc.intervalIntegrable _ _)
    simp only [Nat.cast_zero, zero_div, div_self hn'.ne'] at this
    exact this.symm
  rw [gbk_reindex (fun k => h ((k:ℝ) / n)), Finset.sum_div, h1, ← Finset.sum_sub_distrib]
  calc _ ≤ ∑ k ∈ Finset.range n, ‖h (((k + 1 : ℕ) : ℝ) / n) / (n:ℂ)
          - ∫ u in ((k:ℝ) / n)..(((k + 1 : ℕ) : ℝ) / n), h u‖ := norm_sum_le _ _
    _ ≤ ∑ k ∈ Finset.range n, Lc / (n:ℝ)^2 :=
        Finset.sum_le_sum (fun k hk => gbk_term h hc Lc hL n hn' k (Finset.mem_range.mp hk))
    _ = Lc / n := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        field_simp

private lemma gbk_int (E : ℝ → ℂ)
    (hE : ∀ x, E x = Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I)) (t : ℝ) :
    ∫ u in (0:ℝ)..1, E (t*u) = E (t/2) * ((Real.sinc (Real.pi*t) : ℝ) : ℂ) := by
  by_cases ht : t = 0
  · subst ht
    have h0 : E 0 = 1 := by rw [hE]; simp
    simp [h0]
  · have hpt : Real.pi * t ≠ 0 := mul_ne_zero Real.pi_ne_zero ht
    have hc : (2*(Real.pi*t : ℝ) : ℂ) * Complex.I ≠ 0 := by
      have : ((Real.pi*t : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hpt
      simp [this, Complex.I_ne_zero, ht]
    have h1 : ∀ u:ℝ, E (t*u) = Complex.exp (((2*(Real.pi*t : ℝ) : ℂ) * Complex.I) * (u:ℂ)) := by
      intro u; rw [hE]; congr 1; push_cast; ring
    simp_rw [h1]
    rw [integral_exp_mul_complex hc]
    have h2 : E (t/2) = Complex.exp (((Real.pi*t : ℝ) : ℂ) * Complex.I) := by
      rw [hE]; congr 1; push_cast; ring
    rw [h2, Real.sinc_apply, if_neg hpt]
    have hs := Complex.two_sin ((Real.pi*t : ℝ) : ℂ)
    have hmul : Complex.exp (((Real.pi*t : ℝ) : ℂ) * Complex.I)
        * Complex.exp (-((Real.pi*t : ℝ) : ℂ) * Complex.I) = 1 := by
      rw [← Complex.exp_add]; ring_nf; simp
    have hsq : Complex.exp ((2*(Real.pi*t : ℝ) : ℂ) * Complex.I * ((1:ℝ):ℂ))
        = Complex.exp (((Real.pi*t : ℝ) : ℂ) * Complex.I) * Complex.exp (((Real.pi*t : ℝ) : ℂ) * Complex.I) := by
      rw [← Complex.exp_add]; congr 1; push_cast; ring
    rw [hsq]
    simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, Complex.ofReal_div, Complex.ofReal_sin]
    have hpt' : ((Real.pi*t : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hpt
    set w := Complex.exp (((Real.pi*t : ℝ) : ℂ) * Complex.I)
    set w' := Complex.exp (-((Real.pi*t : ℝ) : ℂ) * Complex.I)
    set θ : ℂ := ((Real.pi*t : ℝ) : ℂ)
    have hs' : Complex.sin θ = (w' - w) * Complex.I / 2 := by
      rw [eq_div_iff (two_ne_zero), mul_comm]; exact hs
    rw [hs']
    field_simp
    have hI : Complex.I ^ 2 = -1 := Complex.I_sq
    linear_combination hmul + (w ^ 2 - w * w') * hI

private lemma gbk_abs_int (h : ℝ) (hh : 0 ≤ h) :
    ∫ t in (-h)..h, |t| = h^2 := by
  have h0 : ∫ t in (0:ℝ)..h, |t| = h^2/2 := by
    rw [intervalIntegral.integral_congr (g := fun x => x)
      (fun x hx => by rw [Set.uIcc_of_le hh] at hx; exact abs_of_nonneg hx.1)]
    rw [integral_id]; ring
  have h1 : ∫ t in (-h)..(0:ℝ), |t| = h^2/2 := by
    have := intervalIntegral.integral_comp_neg (a := 0) (b := h) (fun x : ℝ => |x|)
    simp only [abs_neg, neg_zero] at this
    rw [← this, h0]
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := 0)
    (continuous_abs.intervalIntegrable _ _) (continuous_abs.intervalIntegrable _ _), h0, h1]
  ring

private lemma gbk_int_bound (φ ψ : ℝ → ℝ) (hφ : Continuous φ) (hψ : Continuous ψ) (n : ℕ)
    (hn : (0:ℝ) < n) (h : ℝ) (hh : 0 ≤ h) (hb : ∀ t, |φ t - ψ t| ≤ 4*Real.pi*|t|/n) :
    |(∫ t in (-h)..h, φ t) - ∫ t in (-h)..h, ψ t| ≤ 4*Real.pi*h^2/n := by
  rw [← intervalIntegral.integral_sub (hφ.intervalIntegrable _ _) (hψ.intervalIntegrable _ _)]
  have := intervalIntegral.norm_integral_le_of_norm_le (a := -h) (b := h)
    (f := fun t => φ t - ψ t) (g := fun t => 4*Real.pi/n*|t|) (by linarith)
    (Filter.Eventually.of_forall (fun t _ => by
      rw [Real.norm_eq_abs]
      have := hb t
      calc _ ≤ _ := this
        _ = _ := by ring))
    (Continuous.intervalIntegrable (μ := MeasureTheory.volume) (continuous_const.mul continuous_abs) _ _)
  rw [Real.norm_eq_abs] at this
  rw [intervalIntegral.integral_const_mul, gbk_abs_int h hh] at this
  calc _ ≤ _ := this
    _ = _ := by ring

theorem Conjectures.Goldbach.FiniteMajorRescaledIntervalKernel :
    let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let _J := fun (h : ℝ) (f : ℝ → ℂ) => intervalIntegral f (-h) h MeasureTheory.volume; let Jr := fun (h : ℝ) (f : ℝ → ℝ) => intervalIntegral f (-h) h MeasureTheory.volume; let V := fun (n : ℕ) (β : ℝ) => ∑ k ∈ Finset.Icc 1 n, E ((k:ℝ)*β); ∀ (n : ℕ) (h : ℝ), 0<n → 0≤h → (let f := fun t : ℝ => V n (t/n)/(n:ℂ); (∀ t : ℝ, ‖f t - E (t/2)*(Real.sinc (Real.pi*t):ℂ)‖ ≤ 2*Real.pi*|t|/(n:ℝ)) ∧ |((_J (h/n) (fun β => (V n β)^2*E (-(n:ℝ)*β))).re/(n:ℝ)) - Jr h (fun t => Real.sinc (Real.pi*t)^2)| ≤ 4*Real.pi*h^2/(n:ℝ) ∧ |Jr (h/n) (fun β => ‖V n β‖^2)/(n:ℝ) - Jr h (fun t => Real.sinc (Real.pi*t)^2)| ≤ 4*Real.pi*h^2/(n:ℝ)) := by
  intro E _J Jr V n h hn hh f
  have hE : ∀ x, E x = Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I) := fun x => rfl
  have hn0 : (0:ℝ) < n := by exact_mod_cast hn
  have hn1 : 1 ≤ n := hn
  have hEc := gbk_E_cont E hE
  have hVc : Continuous (V n) := by
    show Continuous (fun β : ℝ => ∑ k ∈ Finset.Icc 1 n, E ((k:ℝ)*β))
    fun_prop
  have hfc : Continuous f := by
    show Continuous (fun t : ℝ => V n (t/(n:ℝ))/(n:ℂ))
    exact (hVc.comp (continuous_id.div_const _)).div_const _
  obtain ⟨g, hgdef⟩ : ∃ g : ℝ → ℂ, g = fun t => E (t/2) * ((Real.sinc (Real.pi*t) : ℝ) : ℂ) :=
    ⟨_, rfl⟩
  have hgc : Continuous g := by
    rw [hgdef]
    exact (hEc.comp (continuous_id.div_const _)).mul
      (Complex.continuous_ofReal.comp (Real.continuous_sinc.comp (continuous_const.mul continuous_id)))
  have hg1 : ∀ t : ℝ, ‖g t‖ ≤ 1 := by
    intro t
    rw [hgdef]
    show ‖E (t/2) * ((Real.sinc (Real.pi*t) : ℝ) : ℂ)‖ ≤ 1
    rw [norm_mul, gbk_norm_E E hE, one_mul, Complex.norm_real, Real.norm_eq_abs]
    exact Real.abs_sinc_le_one _
  have hfeq : ∀ t : ℝ, f t = (∑ k ∈ Finset.Icc 1 n, E (t * ((k:ℝ)/n)))/(n:ℂ) := by
    intro t
    show V n (t/n)/(n:ℂ) = _
    congr 1
    apply Finset.sum_congr rfl
    intro k _
    congr 1
    ring
  have ha : ∀ t : ℝ, ‖f t - g t‖ ≤ 2*Real.pi*|t|/(n:ℝ) := by
    intro t
    rw [hfeq, hgdef]
    show ‖_ - E (t/2) * ((Real.sinc (Real.pi*t) : ℝ) : ℂ)‖ ≤ _
    rw [← gbk_int E hE t]
    exact gbk_riemann (fun u => E (t*u)) (hEc.comp (continuous_const.mul continuous_id))
      (2*Real.pi*|t|) (fun x y => by
        have := gbk_E_lip E hE (t*x) (t*y)
        calc _ ≤ _ := this
          _ = _ := by rw [← mul_sub, abs_mul]; ring) n hn1
  have hf1 : ∀ t, ‖f t‖ ≤ 1 := by
    intro t
    rw [hfeq, norm_div, Complex.norm_natCast, div_le_one hn0]
    calc _ ≤ ∑ k ∈ Finset.Icc 1 n, ‖E (t * ((k:ℝ)/n))‖ := norm_sum_le _ _
      _ = n := by simp [gbk_norm_E E hE]
  have hsq : ∀ t : ℝ, ‖f t ^ 2 - g t ^ 2‖ ≤ 4*Real.pi*|t|/(n:ℝ) := by
    intro t
    have e : f t ^ 2 - g t ^ 2 = (f t - g t) * (f t + g t) := by ring
    rw [e, norm_mul]
    have h1 : ‖f t + g t‖ ≤ 2 := (norm_add_le _ _).trans (by linarith [hf1 t, hg1 t])
    calc _ ≤ (2*Real.pi*|t|/(n:ℝ)) * 2 :=
          mul_le_mul (ha t) h1 (norm_nonneg _) (by positivity)
      _ = _ := by ring
  have hgE : ∀ t : ℝ, g t ^ 2 * E (-t) = (((Real.sinc (Real.pi*t))^2 : ℝ) : ℂ) := by
    intro t
    have h1 : E (t/2) ^ 2 = E t := by
      rw [sq, ← gbk_E_add E hE]; congr 1; ring
    have h2 : E t * E (-t) = 1 := by
      rw [← gbk_E_add E hE, add_neg_cancel, hE]; simp
    rw [hgdef]
    show (E (t/2) * ((Real.sinc (Real.pi*t) : ℝ) : ℂ)) ^ 2 * E (-t) = _
    have : (E (t/2) * ((Real.sinc (Real.pi*t) : ℝ) : ℂ)) ^ 2 * E (-t)
        = (E (t/2)^2 * E (-t)) * ((Real.sinc (Real.pi*t) : ℝ) : ℂ)^2 := by ring
    rw [this, h1, h2]; push_cast; ring
  have hF : ∀ t : ℝ, (V n (t/n))^2 * E (-(n:ℝ)*(t/n)) = (n:ℂ)^2 * (f t ^2 * E (-t)) := by
    intro t
    have h1 : V n (t/n) = (n:ℂ) * f t := by
      show V n (t/n) = (n:ℂ) * (V n (t/n)/(n:ℂ))
      have : (n:ℂ) ≠ 0 := by exact_mod_cast hn0.ne'
      field_simp
    have h2 : -(n:ℝ)*(t/n) = -t := by field_simp
    rw [h1, h2]; ring
  have hG : ∀ t : ℝ, ‖V n (t/n)‖^2 = (n:ℝ)^2 * ‖f t‖^2 := by
    intro t
    have h1 : V n (t/n) = (n:ℂ) * f t := by
      show V n (t/n) = (n:ℂ) * (V n (t/n)/(n:ℂ))
      have : (n:ℂ) ≠ 0 := by exact_mod_cast hn0.ne'
      field_simp
    rw [h1, norm_mul, Complex.norm_natCast]; ring
  have hψc : Continuous (fun t : ℝ => Real.sinc (Real.pi*t)^2) :=
    (Real.continuous_sinc.comp (continuous_const.mul continuous_id)).pow 2
  refine ⟨fun t => by have := ha t; rw [hgdef] at this; exact this, ?_, ?_⟩
  · show |(∫ β in (-(h/n))..(h/n), V n β ^2 * E (-(n:ℝ)*β)).re / (n:ℝ)
      - ∫ t in (-h)..h, Real.sinc (Real.pi*t)^2| ≤ _
    have hint := intervalIntegral.integral_comp_div (a := -h) (b := h) (c := (n:ℝ))
      (fun β => V n β ^2 * E (-(n:ℝ)*β)) hn0.ne'
    simp only [hF] at hint
    rw [intervalIntegral.integral_const_mul, neg_div] at hint
    have hJ : (∫ β in (-(h/n))..(h/n), V n β ^2 * E (-(n:ℝ)*β))
        = (n:ℂ) * ∫ t in (-h)..h, (f t ^2 * E (-t)) := by
      rw [Complex.real_smul] at hint
      have hn' : (n:ℂ) ≠ 0 := by exact_mod_cast hn0.ne'
      apply mul_left_cancel₀ hn'
      push_cast at hint
      linear_combination (-1:ℂ) * hint
    have hIc : Continuous (fun t : ℝ => f t ^ 2 * E (-t)) :=
      (hfc.pow 2).mul (hEc.comp continuous_neg)
    have hre : (∫ t in (-h)..h, (f t ^2 * E (-t))).re = ∫ t in (-h)..h, (f t ^2 * E (-t)).re := by
      have := Complex.reCLM.intervalIntegral_comp_comm (a := -h) (b := h)
        (μ := MeasureTheory.volume) (f := fun t : ℝ => f t ^ 2 * E (-t))
        (hIc.intervalIntegrable _ _)
      simpa using this.symm
    have h3 : (((n:ℂ) * ∫ t in (-h)..h, (f t ^2 * E (-t))).re) / (n:ℝ)
        = (∫ t in (-h)..h, (f t ^2 * E (-t))).re := by
      rw [show ((n:ℂ) * ∫ t in (-h)..h, (f t ^2 * E (-t)))
        = ((n:ℝ):ℂ) * ∫ t in (-h)..h, (f t ^2 * E (-t)) by push_cast; rfl, Complex.re_ofReal_mul]
      field_simp
    rw [hJ, h3, hre]
    refine gbk_int_bound (fun t => (f t ^2 * E (-t)).re) (fun t => Real.sinc (Real.pi*t)^2)
      (Complex.continuous_re.comp hIc) hψc n hn0 h hh ?_
    intro t
    show |(f t ^2 * E (-t)).re - Real.sinc (Real.pi*t)^2| ≤ _
    have e1 : (Real.sinc (Real.pi*t))^2 = (g t ^ 2 * E (-t)).re := by
      rw [hgE, Complex.ofReal_re]
    rw [e1, ← Complex.sub_re, ← sub_mul]
    refine (Complex.abs_re_le_norm _).trans ?_
    rw [norm_mul, gbk_norm_E E hE, mul_one]
    exact hsq t
  · show |(∫ β in (-(h/n))..(h/n), ‖V n β‖^2) / (n:ℝ)
      - ∫ t in (-h)..h, Real.sinc (Real.pi*t)^2| ≤ _
    have hint := intervalIntegral.integral_comp_div (a := -h) (b := h) (c := (n:ℝ))
      (fun β => ‖V n β‖^2) hn0.ne'
    simp only [hG] at hint
    rw [intervalIntegral.integral_const_mul, neg_div, smul_eq_mul] at hint
    have h3 : (∫ β in (-(h/n))..(h/n), ‖V n β‖^2) / (n:ℝ) = ∫ t in (-h)..h, ‖f t‖^2 := by
      field_simp
      nlinarith [hint]
    rw [h3]
    refine gbk_int_bound (fun t => ‖f t‖^2) (fun t => Real.sinc (Real.pi*t)^2)
      ((hfc.norm).pow 2) hψc n hn0 h hh ?_
    intro t
    show |‖f t‖^2 - Real.sinc (Real.pi*t)^2| ≤ _
    have e1 : (Real.sinc (Real.pi*t))^2 = ‖g t‖^2 := by
      rw [hgdef]
      show _ = ‖E (t/2) * ((Real.sinc (Real.pi*t) : ℝ) : ℂ)‖^2
      rw [norm_mul, gbk_norm_E E hE, one_mul, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    rw [e1]
    have h1 : |‖f t‖ - ‖g t‖| ≤ 2*Real.pi*|t|/(n:ℝ) := (abs_norm_sub_norm_le _ _).trans (ha t)
    have h2 : ‖f t‖ + ‖g t‖ ≤ 2 := by linarith [hf1 t, hg1 t]
    have e : ‖f t‖^2 - ‖g t‖^2 = (‖f t‖ - ‖g t‖) * (‖f t‖ + ‖g t‖) := by ring
    rw [e, abs_mul, abs_of_nonneg (by positivity : 0 ≤ ‖f t‖ + ‖g t‖)]
    calc _ ≤ (2*Real.pi*|t|/(n:ℝ)) * 2 :=
          mul_le_mul h1 h2 (by positivity) (by positivity)
      _ = _ := by ring
