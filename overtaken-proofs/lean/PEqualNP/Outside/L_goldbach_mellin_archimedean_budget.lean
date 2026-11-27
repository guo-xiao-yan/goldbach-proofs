import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.Calculus.Deriv.Support

private lemma gbma_hasDerivAt_exp (t x : ℝ) :
    HasDerivAt (fun x : ℝ => Complex.exp (((t*x:ℝ):ℂ)*Complex.I))
      (((t:ℂ)*Complex.I) * Complex.exp (((t*x:ℝ):ℂ)*Complex.I)) x := by
  have h1 : HasDerivAt (fun x : ℝ => t * x) (t * 1) x := (hasDerivAt_id x).const_mul t
  have h2 := (h1.ofReal_comp.mul_const Complex.I).cexp
  convert h2 using 1
  simp only [Complex.ofReal_mul, mul_one]
  ring

private lemma gbma_cont_exp (t : ℝ) :
    Continuous (fun x : ℝ => Complex.exp (((t*x:ℝ):ℂ)*Complex.I)) := by
  fun_prop

private lemma gbma_ibp (G : ℝ → ℝ) (hG : ContDiff ℝ 1 G) (hc : HasCompactSupport G) (t : ℝ) :
    ∫ x, ((deriv G x : ℝ) : ℂ) * Complex.exp (((t*x:ℝ):ℂ)*Complex.I)
      = -((t:ℂ) * Complex.I) * ∫ x, (G x : ℂ) * Complex.exp (((t*x:ℝ):ℂ)*Complex.I) := by
  have hGc : Continuous G := hG.continuous
  have hdc : Continuous (deriv G) := hG.continuous_deriv le_rfl
  have hsupp : HasCompactSupport (fun x => (G x : ℂ)) :=
    hc.comp_left Complex.ofReal_zero
  have hsupp' : HasCompactSupport (fun x => ((deriv G x : ℝ) : ℂ)) :=
    (hc.deriv).comp_left Complex.ofReal_zero
  have hv : ∀ x, HasDerivAt (fun x => (G x : ℂ)) ((deriv G x : ℝ) : ℂ) x := fun x =>
    ((hG.differentiable one_ne_zero) x).hasDerivAt.ofReal_comp
  have hE := gbma_cont_exp t
  have i1 : MeasureTheory.Integrable
      ((fun x : ℝ => Complex.exp (((t*x:ℝ):ℂ)*Complex.I)) * (fun x => ((deriv G x : ℝ) : ℂ))) := by
    refine Continuous.integrable_of_hasCompactSupport (hE.mul (by fun_prop)) ?_
    exact hsupp'.mul_left
  have i2 : MeasureTheory.Integrable
      ((fun x : ℝ => ((t:ℂ)*Complex.I) * Complex.exp (((t*x:ℝ):ℂ)*Complex.I))
        * (fun x => (G x : ℂ))) := by
    refine Continuous.integrable_of_hasCompactSupport ((continuous_const.mul hE).mul (by fun_prop)) ?_
    exact hsupp.mul_left
  have i3 : MeasureTheory.Integrable
      ((fun x : ℝ => Complex.exp (((t*x:ℝ):ℂ)*Complex.I)) * (fun x => (G x : ℂ))) := by
    refine Continuous.integrable_of_hasCompactSupport (hE.mul (by fun_prop)) ?_
    exact hsupp.mul_left
  have := MeasureTheory.integral_mul_deriv_eq_deriv_mul_of_integrable
    (u := fun x : ℝ => Complex.exp (((t*x:ℝ):ℂ)*Complex.I))
    (u' := fun x : ℝ => ((t:ℂ)*Complex.I) * Complex.exp (((t*x:ℝ):ℂ)*Complex.I))
    (v := fun x => (G x : ℂ)) (v' := fun x => ((deriv G x : ℝ) : ℂ))
    (fun x _ => gbma_hasDerivAt_exp t x) (fun x _ => hv x) i1 i2 i3
  have e1 : ∫ x, ((deriv G x : ℝ) : ℂ) * Complex.exp (((t*x:ℝ):ℂ)*Complex.I)
      = ∫ x, Complex.exp (((t*x:ℝ):ℂ)*Complex.I) * ((deriv G x : ℝ) : ℂ) := by
    congr 1; ext x; ring
  rw [e1]
  rw [this]
  have e2 : ∫ x, ((t:ℂ)*Complex.I) * Complex.exp (((t*x:ℝ):ℂ)*Complex.I) * (G x : ℂ)
      = ((t:ℂ)*Complex.I) * ∫ x, (G x : ℂ) * Complex.exp (((t*x:ℝ):ℂ)*Complex.I) := by
    rw [← MeasureTheory.integral_const_mul]
    congr 1; ext x; ring
  rw [e2]
  ring

private lemma gbma_norm_le (G : ℝ → ℝ) (t : ℝ) :
    ‖∫ x, (G x : ℂ) * Complex.exp (((t*x:ℝ):ℂ)*Complex.I)‖ ≤ ∫ x, |G x| := by
  refine (MeasureTheory.norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  congr 1; ext x
  rw [norm_mul, Complex.norm_exp_ofReal_mul_I, Complex.norm_real, Real.norm_eq_abs, mul_one]

private lemma gbma_cont_W (f : ℝ → ℝ) (hf : Continuous f) (hc : HasCompactSupport f) :
    Continuous (fun t : ℝ => ∫ x, (f x : ℂ) * Complex.exp (((t*x:ℝ):ℂ)*Complex.I)) := by
  have hi : MeasureTheory.Integrable f := hf.integrable_of_hasCompactSupport hc
  refine MeasureTheory.continuous_of_dominated (bound := fun x => |f x|) ?_ ?_ hi.abs ?_
  · intro t
    exact (by fun_prop : Continuous fun x : ℝ => (f x : ℂ) * Complex.exp (((t*x:ℝ):ℂ)*Complex.I)).aestronglyMeasurable
  · intro t
    refine Filter.Eventually.of_forall fun x => ?_
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, Complex.norm_real, Real.norm_eq_abs, mul_one]
  · refine Filter.Eventually.of_forall fun x => ?_
    fun_prop

theorem PEqualNP.Outside.L_goldbach_mellin_archimedean_budget :
    let W := fun (f : ℝ → ℝ) (t : ℝ) => ∫ x : ℝ, (f x:ℂ)*Complex.exp (((t*x:ℝ):ℂ)*Complex.I); ∀ (f J : ℝ → ℝ), (∀ j : ℕ, ContDiff ℝ j f) → HasCompactSupport f → Continuous J → (∃ K : ℝ, ∀ t, |J t| ≤ K*(1+Real.log (2+|t|))) → MeasureTheory.Integrable (fun t : ℝ => ‖W f t‖^2*J t) MeasureTheory.volume := by
  intro W f J hf hc hJ ⟨K, hK⟩
  have hf1 : ContDiff ℝ 1 f := hf 1
  have hf2 : ContDiff ℝ 2 f := hf 2
  have hd1 : ContDiff ℝ 1 (deriv f) := by
    have := (contDiff_succ_iff_deriv (n := 1)).1 hf2
    exact this.2.2
  have hcd : HasCompactSupport (deriv f) := hc.deriv
  set C0 := ∫ x, |f x| with hC0
  set C2 := ∫ x, |deriv (deriv f) x| with hC2
  have hC0n : 0 ≤ C0 := MeasureTheory.integral_nonneg fun x => abs_nonneg _
  have hC2n : 0 ≤ C2 := MeasureTheory.integral_nonneg fun x => abs_nonneg _
  have hb : ∀ t : ℝ, (1 + t^2) * ‖W f t‖ ≤ C0 + C2 := by
    intro t
    have h0 : ‖W f t‖ ≤ C0 := gbma_norm_le f t
    have h1 := gbma_ibp f hf1 hc t
    have h2 := gbma_ibp (deriv f) hd1 hcd t
    have h3 : ‖∫ x, ((deriv (deriv f) x : ℝ) : ℂ) * Complex.exp (((t*x:ℝ):ℂ)*Complex.I)‖ ≤ C2 :=
      gbma_norm_le _ t
    have hn : ‖-((t:ℂ) * Complex.I)‖ = |t| := by
      rw [norm_neg, norm_mul, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs]
    rw [h2, h1, norm_mul, norm_mul, hn] at h3
    have h4 : |t| * (|t| * ‖W f t‖) = t^2 * ‖W f t‖ := by
      rw [← mul_assoc, ← sq, sq_abs]
    have h3' : t^2 * ‖W f t‖ ≤ C2 := by
      rw [← h4]; exact h3
    show _ ≤ _
    nlinarith [norm_nonneg (W f t)]
  have hcont : Continuous (fun t => W f t) := gbma_cont_W f hf1.continuous hc
  have hmeas : Continuous (fun t : ℝ => ‖W f t‖^2 * J t) :=
    ((continuous_norm.comp hcont).pow 2).mul hJ
  set K' := |K| with hK'
  have hint : MeasureTheory.Integrable (fun t : ℝ => (3 * K' * (C0 + C2)^2) * (1 + t^2)⁻¹) :=
    integrable_inv_one_add_sq.const_mul _
  refine hint.mono' hmeas.aestronglyMeasurable (Filter.Eventually.of_forall fun t => ?_)
  have hp : 0 < 1 + t^2 := by positivity
  have hW : ‖W f t‖ ≤ (C0 + C2) / (1 + t^2) := by
    rw [le_div_iff₀ hp]; linarith [hb t]
  have hW2 : ‖W f t‖^2 ≤ ((C0 + C2) / (1 + t^2))^2 :=
    pow_le_pow_left₀ (norm_nonneg _) hW 2
  have hlog : 1 + Real.log (2 + |t|) ≤ 3 * (1 + t^2) := by
    have := Real.log_le_sub_one_of_pos (show 0 < 2 + |t| by positivity)
    have h5 : |t| ≤ 1 + t^2 := by nlinarith [sq_abs t, sq_nonneg (|t| - 1)]
    nlinarith
  have hlog0 : 0 ≤ 1 + Real.log (2 + |t|) := by
    have : (1:ℝ) ≤ 2 + |t| := by linarith [abs_nonneg t]
    have := Real.log_nonneg this
    linarith
  have hJt : |J t| ≤ K' * (3 * (1 + t^2)) := by
    calc |J t| ≤ K * (1 + Real.log (2 + |t|)) := hK t
      _ ≤ K' * (1 + Real.log (2 + |t|)) := by
          gcongr; exact le_abs_self K
      _ ≤ K' * (3 * (1 + t^2)) := by gcongr
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity : 0 ≤ ‖W f t‖^2)]
  calc ‖W f t‖^2 * |J t| ≤ ((C0 + C2) / (1 + t^2))^2 * (K' * (3 * (1 + t^2))) := by
        gcongr
    _ = (3 * K' * (C0 + C2)^2) * (1 + t^2)⁻¹ := by
        field_simp
