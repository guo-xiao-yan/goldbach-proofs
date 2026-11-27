import Mathlib

private lemma zat_nonstat (σ β γ a b H : ℝ) (ha : 0 < a) (hab : a ≤ b) (hσ : 0 ≤ σ) (hH : 0 < H)
    (hg : ∀ x ∈ Set.Icc a b, H ≤ |β*x+γ|) :
    ‖∫ x in a..b, ((x^(σ-1):ℝ):ℂ) * Complex.exp (((β*x+γ*Real.log x:ℝ):ℂ)*Complex.I)‖
      ≤ 4*b^σ/H := by
  have hIcc : Set.uIcc a b = Set.Icc a b := Set.uIcc_of_le hab
  have hxpos : ∀ x ∈ Set.Icc a b, 0 < x := fun x hx => lt_of_lt_of_le ha hx.1
  have hgne : ∀ x ∈ Set.Icc a b, β*x+γ ≠ 0 := by
    intro x hx h0
    have := hg x hx
    rw [h0, abs_zero] at this
    linarith
  have hbpos : 0 < b := lt_of_lt_of_le ha hab
  obtain ⟨u, hu⟩ : ∃ u : ℝ → ℝ, ∀ x, u x = x^σ/(β*x+γ) := ⟨_, fun _ => rfl⟩
  obtain ⟨u', hu'⟩ : ∃ u' : ℝ → ℝ, ∀ x, u' x = (σ*x^(σ-1)*(β*x+γ) - x^σ*β)/(β*x+γ)^2 :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨E, hE⟩ : ∃ E : ℝ → ℂ, ∀ x,
      E x = Complex.exp (((β*x+γ*Real.log x:ℝ):ℂ)*Complex.I) := ⟨_, fun _ => rfl⟩
  obtain ⟨E', hE'⟩ : ∃ E' : ℝ → ℂ, ∀ x,
      E' x = E x * (((β+γ*x⁻¹:ℝ):ℂ)*Complex.I) := ⟨_, fun _ => rfl⟩
  have hEn : ∀ x, ‖E x‖ = 1 := by
    intro x
    rw [hE]
    exact Complex.norm_exp_ofReal_mul_I _
  have hdu : ∀ x ∈ Set.Icc a b, HasDerivAt (fun y : ℝ => (u y : ℂ)) ((u' x : ℝ) : ℂ) x := by
    intro x hx
    have h1 := (Real.hasDerivAt_rpow_const (p := σ) (Or.inl (hxpos x hx).ne')).div
      (((hasDerivAt_id x).const_mul β).add_const γ) (hgne x hx)
    have h2 : HasDerivAt u (u' x) x := by
      convert h1 using 1
      · funext y; simp [hu]
      · rw [hu']; simp
    exact h2.ofReal_comp
  have hdE : ∀ x ∈ Set.Icc a b, HasDerivAt E (E' x) x := by
    intro x hx
    have h1 : HasDerivAt (fun y : ℝ => β*y+γ*Real.log y) (β + γ*x⁻¹) x := by
      have := (((hasDerivAt_id x).const_mul β).add
        ((Real.hasDerivAt_log (hxpos x hx).ne').const_mul γ))
      convert this using 1 <;> first | (funext y; simp) | simp
    have h2 := ((h1.ofReal_comp).mul_const Complex.I).cexp
    have h3 : E = fun y : ℝ => Complex.exp (((β*y+γ*Real.log y:ℝ):ℂ)*Complex.I) := by
      funext y; exact hE y
    rw [h3, hE']
    rw [hE]
    exact h2
  have hcu : ∀ x ∈ Set.Icc a b, ContinuousAt u' x := by
    intro x hx
    have hx0 := (hxpos x hx).ne'
    have hg0 := hgne x hx
    have e : u' = fun x => (σ*x^(σ-1)*(β*x+γ) - x^σ*β)/(β*x+γ)^2 := funext hu'
    rw [e]
    have c1 := Real.continuousAt_rpow_const x (σ-1) (Or.inl hx0)
    have c2 := Real.continuousAt_rpow_const x σ (Or.inl hx0)
    have hgc : ContinuousAt (fun y : ℝ => β*y+γ) x :=
      (continuousAt_const.mul continuousAt_id).add continuousAt_const
    exact ContinuousAt.div (ContinuousAt.sub (ContinuousAt.mul (continuousAt_const.mul c1)
      hgc) (c2.mul continuousAt_const)) (hgc.pow 2) (pow_ne_zero 2 hg0)
  have hcE' : ∀ x ∈ Set.Icc a b, ContinuousAt E' x := by
    intro x hx
    have hx0 := (hxpos x hx).ne'
    have e : E' = fun y => E y * (((β+γ*y⁻¹:ℝ):ℂ)*Complex.I) := funext hE'
    rw [e]
    refine (hdE x hx).continuousAt.mul ?_
    have : ContinuousAt (fun y : ℝ => β+γ*y⁻¹) x :=
      continuousAt_const.add (continuousAt_const.mul (continuousAt_inv₀ hx0))
    exact (Complex.continuous_ofReal.continuousAt.comp this).mul continuousAt_const
  have hint_u'r : IntervalIntegrable u' MeasureTheory.volume a b := by
    apply ContinuousOn.intervalIntegrable
    rw [hIcc]
    exact fun x hx => (hcu x hx).continuousWithinAt
  have hint_u'c : IntervalIntegrable (fun x => ((u' x:ℝ):ℂ)) MeasureTheory.volume a b := by
    apply ContinuousOn.intervalIntegrable
    rw [hIcc]
    exact fun x hx => (Complex.continuous_ofReal.continuousAt.comp (hcu x hx)).continuousWithinAt
  have hint_E' : IntervalIntegrable E' MeasureTheory.volume a b := by
    apply ContinuousOn.intervalIntegrable
    rw [hIcc]
    exact fun x hx => (hcE' x hx).continuousWithinAt
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    (u := fun y => ((u y:ℝ):ℂ)) (v := E) (u' := fun x => ((u' x:ℝ):ℂ)) (v' := E') (a := a) (b := b)
    (by rw [hIcc]; exact fun x hx => (hdu x hx).continuousAt.continuousWithinAt)
    (by rw [hIcc]; exact fun x hx => (hdE x hx).continuousAt.continuousWithinAt)
    (fun x hx => hdu x (by rw [min_eq_left hab, max_eq_right hab] at hx; exact Set.Ioo_subset_Icc_self hx))
    (fun x hx => hdE x (by rw [min_eq_left hab, max_eq_right hab] at hx; exact Set.Ioo_subset_Icc_self hx))
    hint_u'c hint_E'
  have hint : ∫ x in a..b, ((x^(σ-1):ℝ):ℂ) * Complex.exp (((β*x+γ*Real.log x:ℝ):ℂ)*Complex.I)
      = -Complex.I * ∫ x in a..b, ((u x:ℝ):ℂ) * E' x := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x hx
    rw [hIcc] at hx
    have hx0 := (hxpos x hx).ne'
    have hg0 := hgne x hx
    have hr : ((x^(σ-1):ℝ):ℂ) = ((u x:ℝ):ℂ) * (((β+γ*x⁻¹:ℝ)):ℂ) := by
      rw [← Complex.ofReal_mul]
      congr 1
      have hg1 : x*β+γ ≠ 0 := by rw [mul_comm]; exact hg0
      rw [hu, Real.rpow_sub_one hx0]
      field_simp
    show ((x^(σ-1):ℝ):ℂ) * Complex.exp (((β*x+γ*Real.log x:ℝ):ℂ)*Complex.I) = -Complex.I * (((u x:ℝ):ℂ) * E' x)
    rw [hr, hE', hE]
    linear_combination (((u x:ℝ):ℂ) * (((β+γ*x⁻¹:ℝ)):ℂ) *
      Complex.exp (((β*x+γ*Real.log x:ℝ):ℂ)*Complex.I)) * Complex.I_sq
  have hibp' : ∫ x in a..b, ((u x:ℝ):ℂ) * E' x = ((u b:ℝ):ℂ) * E b - ((u a:ℝ):ℂ) * E a
      - ∫ x in a..b, ((u' x:ℝ):ℂ) * E x := hibp
  have hnorm : ∀ x, ‖((u' x:ℝ):ℂ) * E x‖ = |u' x| := by
    intro x; rw [norm_mul, hEn, mul_one, Complex.norm_real, Real.norm_eq_abs]
  have hnormu : ∀ x, ‖((u x:ℝ):ℂ) * E x‖ = |u x| := by
    intro x; rw [norm_mul, hEn, mul_one, Complex.norm_real, Real.norm_eq_abs]
  have hga := hg a ⟨le_refl a, hab⟩
  have hgb := hg b ⟨hab, le_refl b⟩
  have hsame : (0 < β*a+γ ∧ 0 < β*b+γ) ∨ (β*a+γ < 0 ∧ β*b+γ < 0) := by
    have hcont : ContinuousOn (fun x : ℝ => β*x+γ) (Set.uIcc a b) := by fun_prop
    have key : ∀ c ∈ Set.uIcc a b, c ∈ Set.Icc a b := fun c hc => by rwa [hIcc] at hc
    rcases le_abs'.1 hga with ha2 | ha2 <;> rcases le_abs'.1 hgb with hb2 | hb2
    · right; constructor <;> linarith
    · exfalso
      have h0 : (0:ℝ) ∈ Set.uIcc (β*a+γ) (β*b+γ) :=
        Set.mem_uIcc.2 (Or.inl ⟨by linarith, by linarith⟩)
      obtain ⟨c, hc, hc0⟩ := intermediate_value_uIcc hcont h0
      have := hg c (key c hc)
      simp only at hc0
      rw [hc0, abs_zero] at this
      linarith
    · exfalso
      have h0 : (0:ℝ) ∈ Set.uIcc (β*a+γ) (β*b+γ) :=
        Set.mem_uIcc.2 (Or.inr ⟨by linarith, by linarith⟩)
      obtain ⟨c, hc, hc0⟩ := intermediate_value_uIcc hcont h0
      have := hg c (key c hc)
      simp only at hc0
      rw [hc0, abs_zero] at this
      linarith
    · left; constructor <;> linarith
  obtain ⟨s, hs1, hs2⟩ : ∃ s : ℝ, (s = 1 ∨ s = -1) ∧ s*β = |β| := by
    rcases le_or_gt 0 β with h | h
    · exact ⟨1, Or.inl rfl, by rw [abs_of_nonneg h]; ring⟩
    · exact ⟨-1, Or.inr rfl, by rw [abs_of_neg h]; ring⟩
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : ℝ → ℝ, ∀ x, Φ x = x^σ/H - s*b^σ*(β*x+γ)⁻¹ := ⟨_, fun _ => rfl⟩
  obtain ⟨Φ', hΦ'⟩ : ∃ Φ' : ℝ → ℝ, ∀ x, Φ' x = σ*x^(σ-1)/H + s*b^σ*β/(β*x+γ)^2 :=
    ⟨_, fun _ => rfl⟩
  have hdΦ : ∀ x ∈ Set.Icc a b, HasDerivAt Φ (Φ' x) x := by
    intro x hx
    have h1 := ((Real.hasDerivAt_rpow_const (p := σ) (Or.inl (hxpos x hx).ne')).div_const H).sub
      (((((hasDerivAt_id x).const_mul β).add_const γ).inv (hgne x hx)).const_mul (s*b^σ))
    convert h1 using 1
    · funext y; simp [hΦ]
    · rw [hΦ']; simp; ring
  have hcΦ' : IntervalIntegrable Φ' MeasureTheory.volume a b := by
    apply ContinuousOn.intervalIntegrable
    rw [hIcc]
    intro x hx
    have hx0 := (hxpos x hx).ne'
    have hg0 := hgne x hx
    have e : Φ' = fun x => σ*x^(σ-1)/H + s*b^σ*β/(β*x+γ)^2 := funext hΦ'
    rw [e]
    have c1 := Real.continuousAt_rpow_const x (σ-1) (Or.inl hx0)
    have hgc : ContinuousAt (fun y : ℝ => β*y+γ) x :=
      (continuousAt_const.mul continuousAt_id).add continuousAt_const
    exact (((continuousAt_const.mul c1).div_const H).add
      (continuousAt_const.div (hgc.pow 2) (pow_ne_zero 2 hg0))).continuousWithinAt
  have hΦint : ∫ x in a..b, Φ' x = Φ b - Φ a :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (by rw [hIcc]; exact hdΦ) hcΦ'
  have hpt : ∀ x ∈ Set.Icc a b, |u' x| ≤ Φ' x := by
    intro x hx
    have hx0 := (hxpos x hx).ne'
    have hg0 := hgne x hx
    have hgabs : H ≤ |β*x+γ| := hg x hx
    have hxb : x^σ ≤ b^σ := Real.rpow_le_rpow (hxpos x hx).le hx.2 hσ
    have hxs : 0 ≤ x^(σ-1) := Real.rpow_nonneg (hxpos x hx).le _
    have hxs' : 0 ≤ x^σ := Real.rpow_nonneg (hxpos x hx).le _
    rw [hu', hΦ']
    have e : (σ*x^(σ-1)*(β*x+γ) - x^σ*β)/(β*x+γ)^2
        = σ*x^(σ-1)/(β*x+γ) - x^σ*β/(β*x+γ)^2 := by field_simp
    rw [e]
    have t1 : |σ*x^(σ-1)/(β*x+γ)| ≤ σ*x^(σ-1)/H := by
      rw [abs_div, abs_of_nonneg (mul_nonneg hσ hxs)]
      exact div_le_div_of_nonneg_left (mul_nonneg hσ hxs) hH hgabs
    have t2 : |x^σ*β/(β*x+γ)^2| ≤ s*b^σ*β/(β*x+γ)^2 := by
      rw [abs_div, abs_mul, abs_of_nonneg hxs', abs_of_nonneg (sq_nonneg (β*x+γ))]
      have : s*b^σ*β = b^σ*|β| := by rw [← hs2]; ring
      rw [this]
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hxb (abs_nonneg _)) (sq_nonneg _)
    exact (abs_sub _ _).trans (add_le_add t1 t2)
  have hmono : ∫ x in a..b, |u' x| ≤ ∫ x in a..b, Φ' x :=
    intervalIntegral.integral_mono_on hab hint_u'r.abs hcΦ' hpt
  have hinv : ∀ x ∈ Set.Icc a b, |(β*x+γ)⁻¹| ≤ H⁻¹ := by
    intro x hx; rw [abs_inv]; exact inv_anti₀ hH (hg x hx)
  have hkey : s*((β*a+γ)⁻¹ - (β*b+γ)⁻¹) ≤ H⁻¹ := by
    have h1 := abs_le.1 (hinv a ⟨le_refl a, hab⟩)
    have h2 := abs_le.1 (hinv b ⟨hab, le_refl b⟩)
    rcases hsame with ⟨p1, p2⟩ | ⟨p1, p2⟩
    · have := inv_pos.2 p1
      have := inv_pos.2 p2
      rcases hs1 with rfl | rfl <;> linarith
    · have := inv_lt_zero.2 p1
      have := inv_lt_zero.2 p2
      rcases hs1 with rfl | rfl <;> linarith
  have hu_le : ∀ x ∈ Set.Icc a b, |u x| ≤ x^σ/H := by
    intro x hx
    rw [hu, abs_div, abs_of_nonneg (Real.rpow_nonneg (hxpos x hx).le _)]
    exact div_le_div_of_nonneg_left (Real.rpow_nonneg (hxpos x hx).le _) hH (hg x hx)
  have hbσ : 0 < b^σ := Real.rpow_pos_of_pos hbpos _
  have haσ : 0 ≤ a^σ := Real.rpow_nonneg ha.le _
  have hΦd : Φ b - Φ a ≤ (b^σ - a^σ)/H + b^σ/H := by
    rw [hΦ, hΦ]
    have := mul_le_mul_of_nonneg_left hkey hbσ.le
    have e1 : b^σ * (s*((β*a+γ)⁻¹ - (β*b+γ)⁻¹)) = s*b^σ*(β*a+γ)⁻¹ - s*b^σ*(β*b+γ)⁻¹ := by ring
    have e2 : b^σ * H⁻¹ = b^σ/H := by rw [div_eq_mul_inv]
    have e3 : b^σ/H - a^σ/H = (b^σ - a^σ)/H := by rw [sub_div]
    nlinarith
  have hbdd : ‖∫ x in a..b, ((u' x:ℝ):ℂ) * E x‖ ≤ (b^σ - a^σ)/H + b^σ/H := by
    calc ‖∫ x in a..b, ((u' x:ℝ):ℂ) * E x‖ ≤ ∫ x in a..b, ‖((u' x:ℝ):ℂ) * E x‖ :=
          intervalIntegral.norm_integral_le_integral_norm hab
      _ = ∫ x in a..b, |u' x| := by simp_rw [hnorm]
      _ ≤ _ := by rw [← hΦint] at hΦd; exact hmono.trans hΦd
  have hub : ‖((u b:ℝ):ℂ) * E b‖ ≤ b^σ/H := by
    rw [hnormu]; exact hu_le b ⟨hab, le_refl b⟩
  have hua : ‖((u a:ℝ):ℂ) * E a‖ ≤ a^σ/H := by
    rw [hnormu]; exact hu_le a ⟨le_refl a, hab⟩
  calc ‖∫ x in a..b, ((x^(σ-1):ℝ):ℂ) * Complex.exp (((β*x+γ*Real.log x:ℝ):ℂ)*Complex.I)‖
      = ‖∫ x in a..b, ((u x:ℝ):ℂ) * E' x‖ := by
        rw [hint, norm_mul, norm_neg, Complex.norm_I, one_mul]
    _ = ‖((u b:ℝ):ℂ) * E b - ((u a:ℝ):ℂ) * E a - ∫ x in a..b, ((u' x:ℝ):ℂ) * E x‖ := by
        rw [hibp']
    _ ≤ ‖((u b:ℝ):ℂ) * E b‖ + ‖((u a:ℝ):ℂ) * E a‖ + ‖∫ x in a..b, ((u' x:ℝ):ℂ) * E x‖ :=
        (norm_sub_le _ _).trans (add_le_add_left (norm_sub_le _ _) _)
    _ ≤ b^σ/H + a^σ/H + ((b^σ - a^σ)/H + b^σ/H) := add_le_add (add_le_add hub hua) hbdd
    _ ≤ 4*b^σ/H := by
        have : b^σ/H + a^σ/H + ((b^σ - a^σ)/H + b^σ/H) = 3*b^σ/H := by ring
        rw [this]
        exact div_le_div_of_nonneg_right (by linarith) hH.le

private lemma zat_triv (σ β γ X c d : ℝ) (hX : 0 < X) (hc : X ≤ c) (hcd : c ≤ d) (hσ1 : σ ≤ 1) :
    ‖∫ x in c..d, ((x^(σ-1):ℝ):ℂ) * Complex.exp (((β*x+γ*Real.log x:ℝ):ℂ)*Complex.I)‖
      ≤ X^(σ-1)*(d-c) := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := c) (b := d) (C := X^(σ-1))
    (f := fun x : ℝ => ((x^(σ-1):ℝ):ℂ) * Complex.exp (((β*x+γ*Real.log x:ℝ):ℂ)*Complex.I)) (by
      intro x hx
      rw [Set.uIoc_of_le hcd] at hx
      have hx0 : 0 < x := lt_of_lt_of_le hX (hc.trans hx.1.le)
      rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.rpow_nonneg hx0.le _)]
      exact Real.rpow_le_rpow_of_nonpos hX (hc.trans hx.1.le) (by linarith))
  rwa [abs_of_nonneg (by linarith)] at h

private lemma zat_cuts (a b p q : ℝ) (hab : a ≤ b) (hpq : p ≤ q) :
    ∃ c d : ℝ, a ≤ c ∧ c ≤ d ∧ d ≤ b ∧ (a < c → c ≤ p) ∧ (d < b → q ≤ d) ∧ d - c ≤ q - p ∧
      (c < d → p < b ∧ a < q) := by
  refine ⟨max a (min b p), max (max a (min b p)) (min b q), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals simp only [max_def, min_def]
  all_goals split_ifs <;> intros <;> first | linarith | (constructor <;> linarith)

private lemma zat_curv (σ β γ X a b : ℝ) (hX : 0 < X) (hXa : X ≤ a) (hab : a ≤ b) (hb : b ≤ 2*X)
    (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) (hγ : 0 < |γ|) :
    ‖∫ x in a..b, ((x^(σ-1):ℝ):ℂ) * Complex.exp (((β*x+γ*Real.log x:ℝ):ℂ)*Complex.I)‖
      ≤ X^σ*((3+5*Real.pi)/Real.sqrt |γ|) := by
  have ha : 0 < a := lt_of_lt_of_le hX hXa
  have hS : 18.7 < 3 + 5*Real.pi := by have := Real.pi_gt_d2; linarith
  obtain ⟨S, hSdef⟩ : ∃ S, S = 3+5*Real.pi := ⟨_, rfl⟩
  rw [← hSdef] at hS ⊢
  obtain ⟨s, hs⟩ : ∃ s, s = Real.sqrt |γ| := ⟨_, rfl⟩
  have hspos : 0 < s := by rw [hs]; exact Real.sqrt_pos.2 hγ
  have hs2 : s^2 = |γ| := by rw [hs]; exact Real.sq_sqrt hγ.le
  rw [← hs]
  have hXσ : 0 < X^σ := Real.rpow_pos_of_pos hX _
  have hXs : X^(σ-1)*X = X^σ := by
    rw [Real.rpow_sub_one hX.ne']; field_simp
  have hbσ : b^σ ≤ 2*X^σ := by
    calc b^σ ≤ (2*X)^σ := Real.rpow_le_rpow (by linarith) hb hσ0
      _ = 2^σ * X^σ := Real.mul_rpow (by norm_num) hX.le
      _ ≤ 2*X^σ := by
        have : (2:ℝ)^σ ≤ 2 := by
          simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2) hσ1
        nlinarith
  have hfull : ‖∫ x in a..b, ((x^(σ-1):ℝ):ℂ) * Complex.exp (((β*x+γ*Real.log x:ℝ):ℂ)*Complex.I)‖
      ≤ X^σ := by
    refine (zat_triv σ β γ X a b hX hXa hab hσ1).trans ?_
    rw [← hXs]
    exact mul_le_mul_of_nonneg_left (by linarith) (Real.rpow_nonneg hX.le _)
  by_cases hsS : s ≤ S
  · calc _ ≤ X^σ := hfull
      _ ≤ X^σ*(S/s) := by
        have : 1 ≤ S/s := (one_le_div hspos).2 hsS
        nlinarith
  · rw [not_le] at hsS
    have hs18 : 18.7 < s := lt_trans hS hsS
    obtain ⟨h, hh⟩ : ∃ h, h = 2*s := ⟨_, rfl⟩
    have hhpos : 0 < h := by rw [hh]; linarith
    have hhγ : h < |γ| := by rw [← hs2, hh]; nlinarith
    have key : 4*h/(|γ|-h) + 16/h ≤ S/s := by
      have e : 4*h/(|γ|-h) + 16/h = 8/(s-2) + 8/s := by
        rw [hh, ← hs2]
        have : s - 2 ≠ 0 := by linarith
        have : s^2 - 2*s = s*(s-2) := by ring
        rw [this]
        field_simp
        ring
      rw [e, div_add_div _ _ (by linarith) hspos.ne', div_le_div_iff₀ (by nlinarith) hspos]
      nlinarith
    have hfc : ContinuousOn (fun x : ℝ => ((x^(σ-1):ℝ):ℂ) *
        Complex.exp (((β*x+γ*Real.log x:ℝ):ℂ)*Complex.I)) (Set.Icc a b) := by
      intro x hx
      have hx0 : x ≠ 0 := (lt_of_lt_of_le ha hx.1).ne'
      apply ContinuousAt.continuousWithinAt
      have c1 := Real.continuousAt_rpow_const x (σ-1) (Or.inl hx0)
      have c2 : ContinuousAt (fun y : ℝ => β*y+γ*Real.log y) x :=
        (continuousAt_const.mul continuousAt_id).add
          (continuousAt_const.mul (Real.continuousAt_log hx0))
      exact (Complex.continuous_ofReal.continuousAt.comp c1).mul
        ((Complex.continuous_exp.continuousAt).comp
          ((Complex.continuous_ofReal.continuousAt.comp c2).mul continuousAt_const))
    have hI : ∀ p q, a ≤ p → p ≤ b → a ≤ q → q ≤ b → IntervalIntegrable (fun x : ℝ =>
        ((x^(σ-1):ℝ):ℂ) * Complex.exp (((β*x+γ*Real.log x:ℝ):ℂ)*Complex.I))
        MeasureTheory.volume p q := by
      intro p q h1 h2 h3 h4
      apply ContinuousOn.intervalIntegrable
      exact hfc.mono (Set.uIcc_subset_Icc ⟨h1, h2⟩ ⟨h3, h4⟩)
    by_cases hβ : β = 0
    · subst hβ
      have := zat_nonstat σ 0 γ a b h ha hab hσ0 hhpos (by
        intro x _; simp only [zero_mul, zero_add]; exact hhγ.le)
      calc _ ≤ 4*b^σ/h := this
        _ ≤ X^σ*(4*h/(|γ|-h) + 16/h) := by
          have h1 : 0 ≤ 4*h/(|γ|-h) := div_nonneg (by linarith) (by linarith)
          have h2 : 4*b^σ/h ≤ X^σ*(16/h) := by
            rw [mul_div_assoc', div_le_div_iff_of_pos_right hhpos]
            nlinarith
          nlinarith
        _ ≤ X^σ*(S/s) := mul_le_mul_of_nonneg_left key hXσ.le
    · have hβpos : 0 < |β| := abs_pos.2 hβ
      obtain ⟨r, hr⟩ : ∃ r, r = h/|β| := ⟨_, rfl⟩
      have hrpos : 0 < r := by rw [hr]; exact div_pos hhpos hβpos
      have hβr : |β| *r = h := by rw [hr]; field_simp
      obtain ⟨x0, hx0⟩ : ∃ x0, x0 = -γ/β := ⟨_, rfl⟩
      have hg : ∀ x, |β*x+γ| = |β| *|x-x0| := by
        intro x
        rw [← abs_mul]
        congr 1
        rw [hx0]; field_simp; ring
      have hγx0 : |γ| = |β| *|x0| := by
        rw [hx0, abs_div, abs_neg]; field_simp
      obtain ⟨c, d, hac, hcd, hdb, hc1, hd1, hdc, hmid⟩ :=
        zat_cuts a b (x0 - r) (x0 + r) hab (by linarith)
      have hcb : c ≤ b := hcd.trans hdb
      have hbσ' : ∀ y, y ≤ b → 0 < y → y^σ ≤ 2*X^σ := fun y hy hy0 =>
        (Real.rpow_le_rpow hy0.le hy hσ0).trans hbσ
      have hA : ‖∫ x in a..c, ((x^(σ-1):ℝ):ℂ) * Complex.exp (((β*x+γ*Real.log x:ℝ):ℂ)*Complex.I)‖
          ≤ 8*X^σ/h := by
        rcases eq_or_lt_of_le hac with e | e
        · rw [← e, intervalIntegral.integral_same, norm_zero]
          positivity
        · have := zat_nonstat σ β γ a c h ha hac hσ0 hhpos (by
            intro x hx
            rw [hg x]
            have h1 : x ≤ x0 - r := hx.2.trans (hc1 e)
            have : r ≤ |x - x0| := by
              rw [abs_sub_comm]; exact le_trans (by linarith) (le_abs_self _)
            calc h = |β| *r := hβr.symm
              _ ≤ |β| *|x-x0| := mul_le_mul_of_nonneg_left this hβpos.le)
          refine this.trans ?_
          have h2 := hbσ' c hcb (lt_of_lt_of_le ha hac)
          rw [div_le_div_iff_of_pos_right hhpos]
          linarith
      have hC : ‖∫ x in d..b, ((x^(σ-1):ℝ):ℂ) * Complex.exp (((β*x+γ*Real.log x:ℝ):ℂ)*Complex.I)‖
          ≤ 8*X^σ/h := by
        rcases eq_or_lt_of_le hdb with e | e
        · rw [e, intervalIntegral.integral_same, norm_zero]
          positivity
        · have hd0 : 0 < d := lt_of_lt_of_le ha (hac.trans hcd)
          have := zat_nonstat σ β γ d b h hd0 hdb hσ0 hhpos (by
            intro x hx
            rw [hg x]
            have h1 : x0 + r ≤ x := (hd1 e).trans hx.1
            have : r ≤ |x - x0| := le_trans (by linarith) (le_abs_self _)
            calc h = |β| *r := hβr.symm
              _ ≤ |β| *|x-x0| := mul_le_mul_of_nonneg_left this hβpos.le)
          refine this.trans ?_
          have h2 := hbσ' b le_rfl (lt_of_lt_of_le ha hab)
          rw [div_le_div_iff_of_pos_right hhpos]
          linarith
      have hB : ‖∫ x in c..d, ((x^(σ-1):ℝ):ℂ) * Complex.exp (((β*x+γ*Real.log x:ℝ):ℂ)*Complex.I)‖
          ≤ X^σ*(4*h/(|γ|-h)) := by
        have hcX : X ≤ c := hXa.trans hac
        refine (zat_triv σ β γ X c d hX hcX hcd hσ1).trans ?_
        rcases eq_or_lt_of_le hcd with e | e
        · rw [← e, sub_self, mul_zero]
          have : 0 ≤ 4*h/(|γ|-h) := div_nonneg (by linarith) (by linarith)
          positivity
        · obtain ⟨hp, hq⟩ := hmid e
          have hx0b : |x0| ≤ b + r := by
            rw [abs_le]; constructor <;> linarith
          have hγle : |γ| - h ≤ 2*X*|β| := by
            rw [hγx0]
            nlinarith
          have hpos : 0 < |γ| - h := by linarith
          have hdc' : d - c ≤ 4*X*h/(|γ|-h) := by
            calc d - c ≤ 2*r := by linarith
              _ = 2*h/|β| := by rw [hr]; ring
              _ ≤ 4*X*h/(|γ|-h) := by
                rw [div_le_div_iff₀ hβpos hpos]
                nlinarith
          calc X^(σ-1)*(d-c) ≤ X^(σ-1)*(4*X*h/(|γ|-h)) :=
                mul_le_mul_of_nonneg_left hdc' (Real.rpow_nonneg hX.le _)
            _ = X^σ*(4*h/(|γ|-h)) := by rw [← hXs]; ring
      have e1 := intervalIntegral.integral_add_adjacent_intervals
        (hI a c le_rfl hab hac hcb) (hI c b hac hcb hab le_rfl)
      have e2 := intervalIntegral.integral_add_adjacent_intervals
        (hI c d hac hcb (hac.trans hcd) hdb) (hI d b (hac.trans hcd) hdb hab le_rfl)
      have tri : ∀ A B C : ℂ, ‖A + (B + C)‖ ≤ ‖A‖ + (‖B‖ + ‖C‖) := fun A B C =>
        (norm_add_le _ _).trans (add_le_add_right (norm_add_le _ _) _)
      rw [← e1, ← e2]
      refine (tri _ _ _).trans ?_
      have e3 : 8*X^σ/h + (X^σ*(4*h/(|γ|-h)) + 8*X^σ/h) = X^σ*(4*h/(|γ|-h) + 16/h) := by ring
      have h3 := mul_le_mul_of_nonneg_left key hXσ.le
      linarith

private lemma zat_sqrt_sum (n : ℕ) : ∑ j ∈ Finset.range (n+1), 1/Real.sqrt (j:ℝ) ≤ 2*Real.sqrt n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have hu : 0 ≤ Real.sqrt (n:ℝ) := Real.sqrt_nonneg _
    have hv : 0 < Real.sqrt ((n+1:ℕ):ℝ) := Real.sqrt_pos.2 (by positivity)
    have hu2 : Real.sqrt (n:ℝ)^2 = n := Real.sq_sqrt (by positivity)
    have hv2 : Real.sqrt ((n+1:ℕ):ℝ)^2 = n+1 := by
      rw [Real.sq_sqrt (by positivity)]; push_cast; ring
    have : 1/Real.sqrt ((n+1:ℕ):ℝ) ≤ 2*Real.sqrt ((n+1:ℕ):ℝ) - 2*Real.sqrt (n:ℝ) := by
      rw [div_le_iff₀ hv]
      nlinarith [sq_nonneg (Real.sqrt (n:ℝ) - Real.sqrt ((n+1:ℕ):ℝ))]
    linarith

private lemma zat_harm (N : ℕ) : ∑ j ∈ Finset.range (N+1), 1/(j:ℝ) ≤ 1 + Real.log (N+1:ℝ) := by
  rw [Finset.sum_range_succ']
  have h1 : (∑ i ∈ Finset.range N, 1/(((i+1:ℕ)):ℝ)) = ((harmonic N : ℚ) : ℝ) := by
    simp [harmonic]
  simp only [Nat.cast_zero, div_zero, add_zero]
  rw [h1]
  refine (harmonic_le_one_add_log N).trans ?_
  have : Real.log (N:ℝ) ≤ Real.log (N+1:ℝ) := by
    rcases Nat.eq_zero_or_pos N with h | h
    · subst h; simp
    · exact Real.log_le_log (by exact_mod_cast h) (by linarith)
  linarith

theorem Conjectures.Goldbach.ZeroAdditiveTwistDyadic :
    ∀ (X a b σ β : ℝ), 0 < X → X ≤ a → a ≤ b → b ≤ 2*X → 0 ≤ σ → σ ≤ 1 →
      let K := fun γ : ℝ => ∫ x in a..b, ((x^(σ-1):ℝ):ℂ) *
        Complex.exp (((β*x+γ*Real.log x:ℝ):ℂ)*Complex.I)
      (∀ γ : ℝ, ‖K γ‖ ≤ X^σ ∧
        (γ ≠ 0 → ‖K γ‖ ≤ X^σ*((3+5*Real.pi)/Real.sqrt |γ|)) ∧
        ∀ H : ℝ, 0 < H → (∀ x ∈ Set.Icc a b, H ≤ |β*x+γ|) → ‖K γ‖ ≤ 5*b^σ/H) ∧
      ∀ (I : Finset ℕ) (g : ℕ → ℝ) (J N : ℕ) (M : ℝ),
        0 ≤ M → 4*|β| * X ≤ J → (∀ i ∈ I, |g i| < (N:ℝ)+1) →
        (∀ j ≤ N, (((I.filter (fun i => ⌊|g i|⌋₊ = j)).card : ℕ) : ℝ) ≤ M) →
        (∑ i ∈ I, ‖K (g i)‖) ≤
          X^σ*M*(1 + 2*(3+5*Real.pi)*Real.sqrt J + 20*(1+Real.log (N+1:ℝ))) := by
  intro X a b σ β hX hXa hab hb hσ0 hσ1 K
  have ha : 0 < a := lt_of_lt_of_le hX hXa
  have hbpos : 0 < b := lt_of_lt_of_le ha hab
  have hXσ : 0 < X^σ := Real.rpow_pos_of_pos hX _
  have hXs : X^(σ-1)*X = X^σ := by
    rw [Real.rpow_sub_one hX.ne']; field_simp
  have hbσ : b^σ ≤ 2*X^σ := by
    calc b^σ ≤ (2*X)^σ := Real.rpow_le_rpow (by linarith) hb hσ0
      _ = 2^σ * X^σ := Real.mul_rpow (by norm_num) hX.le
      _ ≤ 2*X^σ := by
        have : (2:ℝ)^σ ≤ 2 := by
          simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2) hσ1
        nlinarith
  have hS : 0 < 3 + 5*Real.pi := by positivity
  have P1 : ∀ γ : ℝ, ‖K γ‖ ≤ X^σ := by
    intro γ
    refine (zat_triv σ β γ X a b hX hXa hab hσ1).trans ?_
    rw [← hXs]
    exact mul_le_mul_of_nonneg_left (by linarith) (Real.rpow_nonneg hX.le _)
  have P2 : ∀ γ : ℝ, γ ≠ 0 → ‖K γ‖ ≤ X^σ*((3+5*Real.pi)/Real.sqrt |γ|) := fun γ hγ =>
    zat_curv σ β γ X a b hX hXa hab hb hσ0 hσ1 (abs_pos.2 hγ)
  have P3 : ∀ γ H : ℝ, 0 < H → (∀ x ∈ Set.Icc a b, H ≤ |β*x+γ|) → ‖K γ‖ ≤ 5*b^σ/H := by
    intro γ H hH hg
    refine (zat_nonstat σ β γ a b H ha hab hσ0 hH hg).trans ?_
    exact div_le_div_of_nonneg_right (by nlinarith [Real.rpow_pos_of_pos hbpos σ]) hH.le
  refine ⟨fun γ => ⟨P1 γ, P2 γ, P3 γ⟩, ?_⟩
  intro I g J N M hM hJ hgN hcount
  obtain ⟨F, hF⟩ : ∃ F : ℕ → ℝ, ∀ j, F j = X^σ * ((if j = 0 then (1:ℝ) else 0) +
      (if j ≤ J then (3+5*Real.pi)/Real.sqrt (j:ℝ) else 0) + 20/(j:ℝ)) := ⟨_, fun _ => rfl⟩
  have hper : ∀ i ∈ I, ‖K (g i)‖ ≤ F ⌊|g i|⌋₊ := by
    intro i hi
    obtain ⟨j, hjdef⟩ : ∃ j, j = ⌊|g i|⌋₊ := ⟨_, rfl⟩
    rw [← hjdef]
    have hjle : (j:ℝ) ≤ |g i| := by rw [hjdef]; exact Nat.floor_le (abs_nonneg _)
    have hnn1 : ∀ j : ℕ, 0 ≤ (3+5*Real.pi)/Real.sqrt (j:ℝ) := fun j => by positivity
    rcases Nat.eq_zero_or_pos j with hj0 | hj0
    · rw [hF, hj0]
      have := P1 (g i)
      simp only [ite_true, Nat.zero_le, Nat.cast_zero, Real.sqrt_zero, div_zero]
      nlinarith
    · have hjR : (1:ℝ) ≤ j := by exact_mod_cast hj0
      have hjpos : (0:ℝ) < j := by linarith
      have hjne : j ≠ 0 := hj0.ne'
      by_cases hjJ : j ≤ J
      · have hγ : g i ≠ 0 := by
          intro h0; rw [h0, abs_zero] at hjle; linarith
        have h1 := P2 (g i) hγ
        have h2 : (3+5*Real.pi)/Real.sqrt |g i| ≤ (3+5*Real.pi)/Real.sqrt (j:ℝ) :=
          div_le_div_of_nonneg_left hS.le (Real.sqrt_pos.2 hjpos) (Real.sqrt_le_sqrt hjle)
        have h3 : 0 ≤ 20/(j:ℝ) := by positivity
        rw [hF, if_neg hjne, if_pos hjJ]
        have h4 := mul_le_mul_of_nonneg_left h2 hXσ.le
        nlinarith
      · have hJj : (J:ℝ) < j := by exact_mod_cast not_le.1 hjJ
        have hH : 0 < (j:ℝ)/2 := by positivity
        have h1 := P3 (g i) ((j:ℝ)/2) hH (by
          intro x hx
          have hx2 : x ≤ 2*X := hx.2.trans hb
          have hx0 : 0 ≤ x := (hX.trans_le (hXa.trans hx.1)).le
          have h5 : |β*x| ≤ |β| *(2*X) := by
            rw [abs_mul, abs_of_nonneg hx0]
            exact mul_le_mul_of_nonneg_left hx2 (abs_nonneg _)
          have h6 : |g i| - |β*x| ≤ |β*x+g i| := by
            have := abs_sub_abs_le_abs_sub (g i) (-(β*x))
            rw [abs_neg] at this
            have e : g i - -(β*x) = β*x + g i := by ring
            rw [e] at this
            exact this
          nlinarith)
        have h7 : 5*b^σ/((j:ℝ)/2) ≤ 20*X^σ/j := by
          rw [div_div_eq_mul_div, div_le_div_iff_of_pos_right hjpos]
          nlinarith
        have h8 : 20*X^σ/j = X^σ*(20/j) := by ring
        have h9 : 0 ≤ (3+5*Real.pi)/Real.sqrt (j:ℝ) := by positivity
        rw [hF, if_neg hjne, if_neg hjJ]
        nlinarith
  have hmaps : ∀ i ∈ I, ⌊|g i|⌋₊ ∈ Finset.range (N+1) := by
    intro i hi
    rw [Finset.mem_range]
    exact (Nat.floor_lt (abs_nonneg _)).2 (by push_cast; exact hgN i hi)
  have hFnn : ∀ j, 0 ≤ F j := by
    intro j; rw [hF]
    have : 0 ≤ (3+5*Real.pi)/Real.sqrt (j:ℝ) := by positivity
    split_ifs <;> positivity
  calc (∑ i ∈ I, ‖K (g i)‖) ≤ ∑ i ∈ I, F ⌊|g i|⌋₊ := Finset.sum_le_sum hper
    _ = ∑ j ∈ Finset.range (N+1), ∑ i ∈ I.filter (fun i => ⌊|g i|⌋₊ = j), F ⌊|g i|⌋₊ :=
        (Finset.sum_fiberwise_of_maps_to hmaps _).symm
    _ = ∑ j ∈ Finset.range (N+1), ((I.filter (fun i => ⌊|g i|⌋₊ = j)).card : ℝ) * F j := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [Finset.sum_congr rfl (fun i hi => by rw [(Finset.mem_filter.1 hi).2])]
        simp
    _ ≤ ∑ j ∈ Finset.range (N+1), M * F j := by
        apply Finset.sum_le_sum
        intro j hj
        exact mul_le_mul_of_nonneg_right (hcount j (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)))
          (hFnn j)
    _ = X^σ*M*(∑ j ∈ Finset.range (N+1), ((if j = 0 then (1:ℝ) else 0) +
      (if j ≤ J then (3+5*Real.pi)/Real.sqrt (j:ℝ) else 0) + 20/(j:ℝ))) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        rw [hF]; ring
    _ ≤ X^σ*M*(1 + 2*(3+5*Real.pi)*Real.sqrt J + 20*(1+Real.log (N+1:ℝ))) := by
        apply mul_le_mul_of_nonneg_left _ (mul_nonneg hXσ.le hM)
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
        have s1 : (∑ j ∈ Finset.range (N+1), (if j = 0 then (1:ℝ) else 0)) = 1 := by
          simp
        have s2 : (∑ j ∈ Finset.range (N+1),
            (if j ≤ J then (3+5*Real.pi)/Real.sqrt (j:ℝ) else 0))
            ≤ 2*(3+5*Real.pi)*Real.sqrt J := by
          rw [← Finset.sum_filter]
          calc _ ≤ ∑ j ∈ Finset.range (J+1), (3+5*Real.pi)/Real.sqrt (j:ℝ) := by
                apply Finset.sum_le_sum_of_subset_of_nonneg
                · intro j hj
                  simp only [Finset.mem_filter, Finset.mem_range] at hj ⊢
                  omega
                · intro j _ _; positivity
            _ = (3+5*Real.pi) * ∑ j ∈ Finset.range (J+1), 1/Real.sqrt (j:ℝ) := by
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro j _; ring
            _ ≤ (3+5*Real.pi) * (2*Real.sqrt J) :=
                mul_le_mul_of_nonneg_left (zat_sqrt_sum J) hS.le
            _ = 2*(3+5*Real.pi)*Real.sqrt J := by ring
        have s3 : (∑ j ∈ Finset.range (N+1), 20/(j:ℝ)) ≤ 20*(1+Real.log (N+1:ℝ)) := by
          have : (∑ j ∈ Finset.range (N+1), 20/(j:ℝ)) = 20 * ∑ j ∈ Finset.range (N+1), 1/(j:ℝ) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j _; ring
          rw [this]
          exact mul_le_mul_of_nonneg_left (zat_harm N) (by norm_num)
        linarith
