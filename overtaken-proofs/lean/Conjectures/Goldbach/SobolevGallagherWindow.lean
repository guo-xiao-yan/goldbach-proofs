import Mathlib

private lemma gw_key (S S' : ℝ → ℂ) (hS : ∀ t, HasDerivAt S (S' t) t) (hS' : Continuous S')
    (a δ : ℝ) (hδ : 0 < δ) :
    ‖S a‖ ^ 2 ≤ (intervalIntegral (fun t => ‖S t‖ ^ 2) (a-δ) (a+δ) MeasureTheory.volume) / (2 * δ)
      + intervalIntegral (fun t => ‖S t‖ * ‖S' t‖) (a-δ) (a+δ) MeasureTheory.volume := by
  have hSc : Continuous S := continuous_iff_continuousAt.2 fun t => (hS t).continuousAt
  have hg : ∀ t, HasDerivAt (fun s => ‖S s‖ ^ 2) (2 * inner ℝ (S t) (S' t)) t :=
    fun t => (hS t).norm_sq
  have hgc : Continuous (fun s => ‖S s‖ ^ 2) := (hSc.norm).pow 2
  have hwc : Continuous (fun s => ‖S s‖ * ‖S' s‖) := hSc.norm.mul hS'.norm
  have hg'c : Continuous (fun t => 2 * inner ℝ (S t) (S' t)) :=
    continuous_const.mul (hSc.inner hS')
  have hg2c : Continuous (fun s => 2 * (‖S s‖ * ‖S' s‖)) := continuous_const.mul hwc
  have hw0 : ∀ t, 0 ≤ ‖S t‖ * ‖S' t‖ := fun t => by positivity
  have hbd : ∀ t, |2 * inner ℝ (S t) (S' t)| ≤ 2 * (‖S t‖ * ‖S' t‖) := by
    intro t
    rw [abs_mul, abs_two]
    have := abs_real_inner_le_norm (S t) (S' t)
    linarith
  set IR := intervalIntegral (fun t => ‖S t‖ * ‖S' t‖) a (a+δ) MeasureTheory.volume with hIR
  set IL := intervalIntegral (fun t => ‖S t‖ * ‖S' t‖) (a-δ) a MeasureTheory.volume with hIL
  have hsplit : intervalIntegral (fun t => ‖S t‖ * ‖S' t‖) (a-δ) (a+δ) MeasureTheory.volume
      = IL + IR := by
    rw [hIL, hIR]
    exact (intervalIntegral.integral_add_adjacent_intervals (hwc.intervalIntegrable _ _)
      (hwc.intervalIntegrable _ _)).symm
  have hsplit2 : intervalIntegral (fun t => ‖S t‖ ^ 2) (a-δ) (a+δ) MeasureTheory.volume
      = intervalIntegral (fun t => ‖S t‖ ^ 2) (a-δ) a MeasureTheory.volume
        + intervalIntegral (fun t => ‖S t‖ ^ 2) a (a+δ) MeasureTheory.volume :=
    (intervalIntegral.integral_add_adjacent_intervals (hgc.intervalIntegrable _ _)
      (hgc.intervalIntegrable _ _)).symm
  have hR : ∀ t ∈ Set.Icc a (a+δ), ‖S a‖ ^ 2 ≤ ‖S t‖ ^ 2 + 2 * IR := by
    intro t ht
    have hat : a ≤ t := ht.1
    have h1 : intervalIntegral (fun s => 2 * inner ℝ (S s) (S' s)) a t MeasureTheory.volume
        = ‖S t‖ ^ 2 - ‖S a‖ ^ 2 :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hg x)
        (hg'c.intervalIntegrable _ _)
    have h2 : -(intervalIntegral (fun s => 2 * inner ℝ (S s) (S' s)) a t MeasureTheory.volume)
        ≤ intervalIntegral (fun s => 2 * (‖S s‖ * ‖S' s‖)) a t MeasureTheory.volume := by
      rw [← intervalIntegral.integral_neg]
      apply intervalIntegral.integral_mono_on hat (hg'c.neg.intervalIntegrable _ _)
        (hg2c.intervalIntegrable _ _)
      intro x _
      simp only [Pi.neg_apply]
      have := hbd x
      have := neg_abs_le (2 * inner ℝ (S x) (S' x))
      linarith
    simp only [intervalIntegral.integral_const_mul] at h1 h2
    have h3 : intervalIntegral (fun s => 2 * (‖S s‖ * ‖S' s‖)) a t MeasureTheory.volume
        ≤ intervalIntegral (fun s => 2 * (‖S s‖ * ‖S' s‖)) a (a+δ) MeasureTheory.volume :=
      intervalIntegral.integral_mono_interval le_rfl hat ht.2
        (Filter.Eventually.of_forall fun s => by have := hw0 s; simp only [Pi.zero_apply]; linarith)
        (hg2c.intervalIntegrable _ _)
    simp only [intervalIntegral.integral_const_mul] at h3
    linarith
  have hL : ∀ t ∈ Set.Icc (a-δ) a, ‖S a‖ ^ 2 ≤ ‖S t‖ ^ 2 + 2 * IL := by
    intro t ht
    have hat : t ≤ a := ht.2
    have h1 : intervalIntegral (fun s => 2 * inner ℝ (S s) (S' s)) t a MeasureTheory.volume
        = ‖S a‖ ^ 2 - ‖S t‖ ^ 2 :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hg x)
        (hg'c.intervalIntegrable _ _)
    have h2 : intervalIntegral (fun s => 2 * inner ℝ (S s) (S' s)) t a MeasureTheory.volume
        ≤ intervalIntegral (fun s => 2 * (‖S s‖ * ‖S' s‖)) t a MeasureTheory.volume := by
      apply intervalIntegral.integral_mono_on hat (hg'c.intervalIntegrable _ _)
        (hg2c.intervalIntegrable _ _)
      intro x _
      have := hbd x
      have := le_abs_self (2 * inner ℝ (S x) (S' x))
      linarith
    simp only [intervalIntegral.integral_const_mul] at h1 h2
    have h3 : intervalIntegral (fun s => 2 * (‖S s‖ * ‖S' s‖)) t a MeasureTheory.volume
        ≤ intervalIntegral (fun s => 2 * (‖S s‖ * ‖S' s‖)) (a-δ) a MeasureTheory.volume :=
      intervalIntegral.integral_mono_interval ht.1 hat le_rfl
        (Filter.Eventually.of_forall fun s => by have := hw0 s; simp only [Pi.zero_apply]; linarith)
        (hg2c.intervalIntegrable _ _)
    simp only [intervalIntegral.integral_const_mul] at h3
    linarith
  have hR' : intervalIntegral (fun _ => ‖S a‖ ^ 2) a (a+δ) MeasureTheory.volume
      ≤ intervalIntegral (fun t => ‖S t‖ ^ 2 + 2 * IR) a (a+δ) MeasureTheory.volume :=
    intervalIntegral.integral_mono_on (by linarith) intervalIntegrable_const
      ((hgc.add continuous_const).intervalIntegrable _ _) hR
  have hL' : intervalIntegral (fun _ => ‖S a‖ ^ 2) (a-δ) a MeasureTheory.volume
      ≤ intervalIntegral (fun t => ‖S t‖ ^ 2 + 2 * IL) (a-δ) a MeasureTheory.volume :=
    intervalIntegral.integral_mono_on (by linarith) intervalIntegrable_const
      ((hgc.add continuous_const).intervalIntegrable _ _) hL
  rw [intervalIntegral.integral_add (hgc.intervalIntegrable _ _) intervalIntegrable_const]
    at hR' hL'
  simp only [intervalIntegral.integral_const, smul_eq_mul] at hR' hL'
  rw [hsplit, hsplit2, div_add' _ _ _ (by positivity), le_div_iff₀ (by positivity)]
  have e1 : a + δ - a = δ := by ring
  have e2 : a - (a - δ) = δ := by ring
  rw [e1] at hR'
  rw [e2] at hL'
  nlinarith [hR', hL']

private lemma gw_main (E : ℝ → ℂ)
    (hE : ∀ x, E x = Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I))
    (M N : ℕ) (c : ℕ → ℂ) (S : ℝ → ℂ)
    (hSd : ∀ t, S t = ∑ k ∈ Finset.Ico M (M + N), c k * E ((k : ℝ) * t)) (a δ : ℝ) (hδ : 0 < δ) :
    ‖S a‖ ^ 2 ≤ (intervalIntegral (fun t => ‖S t‖ ^ 2) (a-δ) (a+δ) MeasureTheory.volume) / (2 * δ)
      + intervalIntegral (fun t => ‖S t‖ * ‖deriv S t‖) (a-δ) (a+δ) MeasureTheory.volume := by
  have hEc : Continuous E := by
    have : E = fun x => Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I) := funext hE
    rw [this]
    fun_prop
  have hSeq : S = fun t => ∑ k ∈ Finset.Ico M (M + N), c k * E ((k : ℝ) * t) := funext hSd
  subst hSeq
  let S' : ℝ → ℂ := fun t => ∑ k ∈ Finset.Ico M (M + N),
    c k * (E ((k : ℝ) * t) * (((2 * Real.pi * (k : ℝ) : ℝ) : ℂ) * Complex.I))
  have hS : ∀ t, HasDerivAt (fun t => ∑ k ∈ Finset.Ico M (M + N), c k * E ((k : ℝ) * t)) (S' t) t := by
    intro t
    apply HasDerivAt.fun_sum
    intro k _
    apply HasDerivAt.const_mul
    have h1 : HasDerivAt (fun s : ℝ => (2 * Real.pi * ((k : ℝ) * s) : ℝ)) (2 * Real.pi * (k : ℝ)) t := by
      simpa using ((hasDerivAt_id t).const_mul (k : ℝ)).const_mul (2 * Real.pi)
    have h2 := ((h1.ofReal_comp).mul_const Complex.I).cexp
    have e : (fun s : ℝ => E ((k : ℝ) * s))
        = fun s : ℝ => Complex.exp (((2 * Real.pi * ((k : ℝ) * s) : ℝ) : ℂ) * Complex.I) :=
      funext fun s => hE _
    rw [e, hE]
    exact h2
  have hS'c : Continuous S' := by
    apply continuous_finsetSum
    intro k _
    exact continuous_const.mul ((hEc.comp (continuous_const.mul continuous_id)).mul continuous_const)
  have hd : deriv (fun t => ∑ k ∈ Finset.Ico M (M + N), c k * E ((k : ℝ) * t)) = S' :=
    funext fun t => (hS t).deriv
  rw [hd]
  exact gw_key _ S' hS hS'c a δ hδ

theorem Conjectures.Goldbach.SobolevGallagherWindow :
    let E (x : ℝ) := Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I); ∀ (M N : ℕ) (c : ℕ → ℂ) (a δ : ℝ), 0 < δ → let S (t : ℝ) := ∑ k ∈ Finset.Ico M (M + N), c k * E ((k : ℝ) * t); ‖S a‖ ^ 2 ≤ (intervalIntegral (fun t => ‖S t‖ ^ 2) (a-δ) (a+δ) MeasureTheory.volume) / (2 * δ) + intervalIntegral (fun t => ‖S t‖ * ‖deriv S t‖) (a-δ) (a+δ) MeasureTheory.volume := by
  intro E M N c a δ hδ S
  exact gw_main E (fun _ => rfl) M N c S (fun _ => rfl) a δ hδ
