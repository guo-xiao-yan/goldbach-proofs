import Mathlib

private theorem vbound (B : Set ℝ) (hB : MeasurableSet B) (h : ℕ) :
    |intervalIntegral (B.indicator (fun t => Real.cos (2*Real.pi*(h:ℝ)*t))) (0:ℝ) 1 MeasureTheory.volume|
      ≤ intervalIntegral (B.indicator (fun _ => (1:ℝ))) (0:ℝ) 1 MeasureTheory.volume := by
  have hint : IntervalIntegrable (B.indicator (fun _ => (1:ℝ))) MeasureTheory.volume 0 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
    exact (MeasureTheory.integrableOn_const (by simp)).indicator hB
  have h1 := intervalIntegral.norm_integral_le_integral_norm
    (μ := MeasureTheory.volume) (f := B.indicator (fun t => Real.cos (2*Real.pi*(h:ℝ)*t))) (zero_le_one)
  rw [Real.norm_eq_abs] at h1
  refine h1.trans ?_
  apply intervalIntegral.integral_mono_on zero_le_one
  · have hm : Measurable (B.indicator (fun t => Real.cos (2*Real.pi*(h:ℝ)*t))) :=
      (Real.continuous_cos.comp (continuous_const.mul continuous_id)).measurable.indicator hB
    refine hint.mono_fun' hm.norm.aestronglyMeasurable (MeasureTheory.ae_of_all _ ?_)
    intro t
    by_cases ht : t ∈ B <;> simp [ht, Real.abs_cos_le_one]
  · exact hint
  · intro t _
    by_cases ht : t ∈ B <;> simp [ht, Real.abs_cos_le_one]

private theorem arcs_meas (Q : ℕ) (n : ℕ) :
    MeasurableSet {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (Q:ℝ)/((q:ℝ)*(n:ℝ))} := by
  have : {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (Q:ℝ)/((q:ℝ)*(n:ℝ))}
      = ⋃ q : ℕ, ⋃ a : ℕ, ⋃ (_ : 1≤q ∧ q≤Q ∧ a≤q ∧ Nat.Coprime a q),
        {t : ℝ | |t-(a:ℝ)/(q:ℝ)| ≤ (Q:ℝ)/((q:ℝ)*(n:ℝ))} := by
    ext t
    simp only [Set.mem_setOf_eq, Set.mem_iUnion]
    constructor
    · rintro ⟨q, a, h1, h2, h3, h4, h5⟩
      exact ⟨q, a, ⟨h1, h2, h3, h4⟩, h5⟩
    · rintro ⟨q, a, ⟨h1, h2, h3, h4⟩, h5⟩
      exact ⟨q, a, h1, h2, h3, h4, h5⟩
  rw [this]
  refine MeasurableSet.iUnion fun q => MeasurableSet.iUnion fun a => MeasurableSet.iUnion fun _ => ?_
  exact measurableSet_le (by fun_prop) measurable_const

theorem Conjectures.Goldbach.PacketShortLagEnvelope :
    let w := fun k : ℕ => if Nat.Prime k then Real.log (k:ℝ) else 0; let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let S := fun (n : ℕ) (w : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (w k:ℂ)*E ((k:ℝ)*t)); let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let arcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (Q n:ℝ)/((q:ℝ)*(n:ℝ))}; let low := fun (n k : ℕ) => if k^3≤n then w k else 0; let high := fun (n k : ℕ) => w k-low n k; let I := fun (n:ℕ) (a b:ℕ→ℝ) => intervalIntegral (fun t => (arcs n)ᶜ.indicator (fun u => S n a u*S n b u*E (-(n:ℝ)*u)) t) (0:ℝ) 1 MeasureTheory.volume; let L := fun n : ℕ => max 1 (Nat.log 2 n / 2); let K := fun (n : ℕ) (t : ℝ) => (∑ j ∈ Finset.range (L n), Real.cos (2*Real.pi*(2:ℝ)^(j+1)*t))/(L n:ℝ); let B := fun n : ℕ => {t : ℝ | t ∉ arcs n ∧ (1:ℝ)/2 < K n t}; let U := fun (n : ℕ) (a : ℕ → ℝ) => intervalIntegral ((B n).indicator (fun t => ‖S n a t‖^2)) (0:ℝ) 1 MeasureTheory.volume; let V := fun (n h : ℕ) => intervalIntegral ((B n).indicator (fun t => Real.cos (2*Real.pi*(h:ℝ)*t))) (0:ℝ) 1 MeasureTheory.volume; let A := fun (n h : ℕ) (a : ℕ → ℝ) => ∑ k ∈ Finset.range (n+1-h), a k * a (k+h); let model := fun k : ℕ => if Nat.Coprime k 30 then (30:ℝ)/8 else 0; let short := fun (n : ℕ) (a : ℕ → ℝ) => A n 0 a * V n 0 + 2*(∑ h ∈ Finset.Icc 1 (min n ((L n)^2)), A n h a * V n h); let long := fun (n : ℕ) (a : ℕ → ℝ) => 2*(∑ h ∈ Finset.Icc ((L n)^2+1) n, A n h a * V n h); ∀ (n : ℕ) (a : ℕ → ℝ) (M : ℝ), 0 ≤ M → (∀ k ≤ n, |a k| ≤ M) → |short n a| ≤ (1+2*((L n:ℝ)^2))*((n:ℝ)+1)*M^2*V n 0 := by
  intro w E S Q arcs low high I L K B U V A model short long n a M hM ha
  have hKm : Measurable (K n) := by
    show Measurable (fun t : ℝ => (∑ j ∈ Finset.range (L n), Real.cos (2*Real.pi*(2:ℝ)^(j+1)*t))/(L n:ℝ))
    fun_prop
  have hBm : MeasurableSet (B n) :=
    (arcs_meas (Q n) n).compl.inter (measurableSet_lt (measurable_const (a := (1:ℝ)/2)) hKm :
      MeasurableSet {t : ℝ | (1:ℝ)/2 < K n t})
  have hV : ∀ h, |V n h| ≤ V n 0 := by
    intro h
    have := vbound (B n) hBm h
    have e : V n 0 = intervalIntegral ((B n).indicator (fun _ => (1:ℝ))) (0:ℝ) 1 MeasureTheory.volume := by
      show intervalIntegral ((B n).indicator (fun t => Real.cos (2*Real.pi*((0:ℕ):ℝ)*t))) (0:ℝ) 1 MeasureTheory.volume = _
      simp
    rw [e]
    exact this
  have hV0 : 0 ≤ V n 0 := (abs_nonneg _).trans (hV 0)
  have hA : ∀ h, |A n h a| ≤ ((n:ℝ)+1) * M^2 := by
    intro h
    have h1 : |A n h a| ≤ ∑ k ∈ Finset.range (n+1-h), |a k * a (k+h)| := Finset.abs_sum_le_sum_abs _ _
    have h2 : ∀ k ∈ Finset.range (n+1-h), |a k * a (k+h)| ≤ M^2 := by
      intro k hk
      have hk' := Finset.mem_range.mp hk
      rw [abs_mul, sq]
      exact mul_le_mul (ha k (by omega)) (ha (k+h) (by omega)) (abs_nonneg _) hM
    have h3 := Finset.sum_le_sum h2
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h3
    have h4 : ((n+1-h : ℕ):ℝ) ≤ (n:ℝ)+1 := by
      have : n+1-h ≤ n+1 := Nat.sub_le _ _
      exact_mod_cast this
    have hM2 : 0 ≤ M^2 := sq_nonneg _
    nlinarith
  have hM2 : 0 ≤ ((n:ℝ)+1) * M^2 := by positivity
  show |A n 0 a * V n 0 + 2 * ∑ h ∈ Finset.Icc 1 (min n (L n ^ 2)), A n h a * V n h| ≤ _
  have hs : ∀ h, |A n h a * V n h| ≤ ((n:ℝ)+1) * M^2 * V n 0 := by
    intro h
    rw [abs_mul]
    exact mul_le_mul (hA h) (hV h) (abs_nonneg _) hM2
  have hsum : |∑ h ∈ Finset.Icc 1 (min n (L n ^ 2)), A n h a * V n h|
      ≤ ((L n:ℝ)^2) * (((n:ℝ)+1) * M^2 * V n 0) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_sum (fun h _ => hs h)).trans ?_
    rw [Finset.sum_const, nsmul_eq_mul]
    have hc : ((Finset.Icc 1 (min n (L n ^ 2))).card : ℝ) ≤ (L n:ℝ)^2 := by
      rw [Nat.card_Icc]
      have : min n (L n ^ 2) + 1 - 1 ≤ L n ^ 2 := by omega
      exact_mod_cast this
    exact mul_le_mul_of_nonneg_right hc (by positivity)
  have h0 := hs 0
  calc |A n 0 a * V n 0 + 2 * ∑ h ∈ Finset.Icc 1 (min n (L n ^ 2)), A n h a * V n h|
      ≤ |A n 0 a * V n 0| + 2 * |∑ h ∈ Finset.Icc 1 (min n (L n ^ 2)), A n h a * V n h| := by
        refine (abs_add_le _ _).trans ?_
        rw [abs_mul]; norm_num
    _ ≤ ((n:ℝ)+1) * M^2 * V n 0 + 2 * (((L n:ℝ)^2) * (((n:ℝ)+1) * M^2 * V n 0)) := by linarith
    _ = _ := by ring
