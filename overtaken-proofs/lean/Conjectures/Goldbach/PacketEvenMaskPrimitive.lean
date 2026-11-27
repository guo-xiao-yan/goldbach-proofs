import Mathlib

private theorem geom_cos (a m : ℕ) (θ : ℝ) :
    2 * Real.sin θ * ∑ j ∈ Finset.range m, Real.cos (2 * ((a + j : ℕ) : ℝ) * θ)
      = Real.sin ((2 * ((a + m : ℕ) : ℝ) - 1) * θ) - Real.sin ((2 * (a : ℝ) - 1) * θ) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, mul_add, ih]
    have h1 : (2 * ((a + (m + 1) : ℕ) : ℝ) - 1) * θ = (2 * ((a + m : ℕ) : ℝ) + 1) * θ := by
      push_cast; ring
    have h2 : (2 * ((a + m : ℕ) : ℝ) - 1) * θ = 2 * ((a + m : ℕ) : ℝ) * θ - θ := by ring
    have h3 : (2 * ((a + m : ℕ) : ℝ) + 1) * θ = 2 * ((a + m : ℕ) : ℝ) * θ + θ := by ring
    have h1' : (2 * ((a + (m + 1) : ℕ) : ℝ) - 1) * θ = 2 * ((a + m : ℕ) : ℝ) * θ + θ := by
      rw [h1, h3]
    rw [h1', h2, Real.sin_add, Real.sin_sub]
    ring

private theorem cos_bound (a m : ℕ) (t : ℝ) :
    |∑ j ∈ Finset.range m, Real.cos (2 * Real.pi * ((2 * (a + j) : ℕ) : ℝ) * t)|
      ≤ (if Real.sin (2 * Real.pi * t) = 0 then (m : ℝ)
          else min (m : ℝ) (1 / |Real.sin (2 * Real.pi * t)|)) := by
  have hm : |∑ j ∈ Finset.range m, Real.cos (2 * Real.pi * ((2 * (a + j) : ℕ) : ℝ) * t)| ≤ m := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ j ∈ Finset.range m, |Real.cos (2 * Real.pi * ((2 * (a + j) : ℕ) : ℝ) * t)|
        ≤ ∑ j ∈ Finset.range m, (1 : ℝ) := Finset.sum_le_sum (fun j _ => Real.abs_cos_le_one _)
      _ = m := by simp
  split_ifs with hs
  · exact hm
  · refine le_min hm ?_
    have key := geom_cos a m (2 * Real.pi * t)
    have hrew : ∀ j : ℕ, Real.cos (2 * Real.pi * ((2 * (a + j) : ℕ) : ℝ) * t)
        = Real.cos (2 * ((a + j : ℕ) : ℝ) * (2 * Real.pi * t)) := by
      intro j; congr 1; push_cast; ring
    simp only [hrew]
    have hpos : 0 < |Real.sin (2 * Real.pi * t)| := abs_pos.mpr hs
    rw [le_div_iff₀ hpos]
    have h2 : |2 * Real.sin (2 * Real.pi * t) * ∑ j ∈ Finset.range m,
        Real.cos (2 * ((a + j : ℕ) : ℝ) * (2 * Real.pi * t))| ≤ 2 := by
      rw [key]
      calc _ ≤ |Real.sin _| + |Real.sin _| := abs_sub _ _
        _ ≤ 1 + 1 := add_le_add (Real.abs_sin_le_one _) (Real.abs_sin_le_one _)
        _ = 2 := by norm_num
    rw [abs_mul, abs_mul] at h2
    have : |(2:ℝ)| = 2 := abs_of_pos (by norm_num)
    rw [this] at h2
    nlinarith [abs_nonneg (∑ j ∈ Finset.range m,
        Real.cos (2 * ((a + j : ℕ) : ℝ) * (2 * Real.pi * t)))]

private theorem key (B : Set ℝ) (hB : MeasurableSet B) (a m : ℕ) :
    |∑ j ∈ Finset.range m, intervalIntegral (B.indicator (fun t =>
        Real.cos (2 * Real.pi * ((2 * (a + j) : ℕ) : ℝ) * t))) (0:ℝ) 1 MeasureTheory.volume|
    ≤ intervalIntegral (B.indicator (fun t => if Real.sin (2 * Real.pi * t) = 0 then (m : ℝ)
          else min (m : ℝ) (1 / |Real.sin (2 * Real.pi * t)|))) (0:ℝ) 1 MeasureTheory.volume := by
  have hint : ∀ j : ℕ, IntervalIntegrable (B.indicator (fun t =>
        Real.cos (2 * Real.pi * ((2 * (a + j) : ℕ) : ℝ) * t))) MeasureTheory.volume 0 1 := by
    intro j
    have hc : Continuous (fun t : ℝ => Real.cos (2 * Real.pi * ((2 * (a + j) : ℕ) : ℝ) * t)) := by
      fun_prop
    have := (hc.intervalIntegrable (μ := MeasureTheory.volume) 0 1)
    rw [intervalIntegrable_iff] at this ⊢
    exact this.indicator hB
  have hsum := intervalIntegral.integral_finsetSum (s := Finset.range m) (a := (0:ℝ)) (b := 1)
    (μ := MeasureTheory.volume) (f := fun j => B.indicator (fun t =>
        Real.cos (2 * Real.pi * ((2 * (a + j) : ℕ) : ℝ) * t))) (fun j _ => hint j)
  rw [← hsum]
  refine (intervalIntegral.norm_integral_le_integral_norm (E := ℝ) (a := (0:ℝ)) (b := 1) (by norm_num)).trans ?_
  have hmeas : Measurable (fun t : ℝ => if Real.sin (2 * Real.pi * t) = 0 then (m : ℝ)
          else min (m : ℝ) (1 / |Real.sin (2 * Real.pi * t)|)) := by
    refine Measurable.ite ?_ measurable_const ?_
    · exact measurableSet_eq_fun (by fun_prop) measurable_const
    · fun_prop
  have hbd : ∀ t : ℝ, ‖(if Real.sin (2 * Real.pi * t) = 0 then (m : ℝ)
          else min (m : ℝ) (1 / |Real.sin (2 * Real.pi * t)|))‖ ≤ m := by
    intro t
    have h0 : (0:ℝ) ≤ m := Nat.cast_nonneg _
    split_ifs with hs
    · simp
    · have : 0 ≤ min (m : ℝ) (1 / |Real.sin (2 * Real.pi * t)|) :=
        le_min h0 (by positivity)
      rw [Real.norm_eq_abs, abs_of_nonneg this]
      exact min_le_left _ _
  have hint2 : IntervalIntegrable (B.indicator (fun t => if Real.sin (2 * Real.pi * t) = 0
      then (m : ℝ) else min (m : ℝ) (1 / |Real.sin (2 * Real.pi * t)|)))
      MeasureTheory.volume 0 1 := by
    rw [intervalIntegrable_iff]
    have : MeasureTheory.IntegrableOn (fun t : ℝ => if Real.sin (2 * Real.pi * t) = 0
      then (m : ℝ) else min (m : ℝ) (1 / |Real.sin (2 * Real.pi * t)|))
        (Set.uIoc 0 1) MeasureTheory.volume := by
      refine MeasureTheory.Measure.integrableOn_of_bounded (M := m) (by simp) hmeas.aestronglyMeasurable ?_
      exact Filter.Eventually.of_forall hbd
    exact this.indicator hB
  have hint3 : IntervalIntegrable (fun t => ‖(∑ j ∈ Finset.range m, B.indicator (fun t =>
        Real.cos (2 * Real.pi * ((2 * (a + j) : ℕ) : ℝ) * t))) t‖) MeasureTheory.volume 0 1 :=
    (IntervalIntegrable.sum (Finset.range m) (fun j _ => hint j)).norm
  refine intervalIntegral.integral_mono_on (by norm_num) (by simpa only [Finset.sum_apply] using hint3) hint2 ?_
  intro t _
  by_cases ht : t ∈ B
  · simp only [Set.indicator_of_mem ht]
    rw [Real.norm_eq_abs]; exact cos_bound a m t
  · simp [Set.indicator_of_notMem ht]

private theorem meas_arcs (Q n : ℕ) : MeasurableSet {t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ Q ∧ a ≤ q ∧
    Nat.Coprime a q ∧ |t - (a:ℝ)/(q:ℝ)| ≤ (Q:ℝ)/((q:ℝ)*(n:ℝ))} := by
  have : {t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ Q ∧ a ≤ q ∧
    Nat.Coprime a q ∧ |t - (a:ℝ)/(q:ℝ)| ≤ (Q:ℝ)/((q:ℝ)*(n:ℝ))}
      = ⋃ q : ℕ, ⋃ a : ℕ, ({t : ℝ | 1 ≤ q ∧ q ≤ Q ∧ a ≤ q ∧ Nat.Coprime a q} ∩
          {t : ℝ | |t - (a:ℝ)/(q:ℝ)| ≤ (Q:ℝ)/((q:ℝ)*(n:ℝ))}) := by
    ext t; simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_inter_iff]
    constructor
    · rintro ⟨q, a, h1, h2, h3, h4, h5⟩; exact ⟨q, a, ⟨h1, h2, h3, h4⟩, h5⟩
    · rintro ⟨q, a, ⟨h1, h2, h3, h4⟩, h5⟩; exact ⟨q, a, h1, h2, h3, h4, h5⟩
  rw [this]
  refine MeasurableSet.iUnion fun q => MeasurableSet.iUnion fun a => ?_
  exact (MeasurableSet.const _).inter (measurableSet_le (by fun_prop) measurable_const)

theorem Conjectures.Goldbach.PacketEvenMaskPrimitive :
    let w := fun k : ℕ => if Nat.Prime k then Real.log (k:ℝ) else 0; let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let S := fun (n : ℕ) (w : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (w k:ℂ)*E ((k:ℝ)*t)); let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let arcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (Q n:ℝ)/((q:ℝ)*(n:ℝ))}; let low := fun (n k : ℕ) => if k^3≤n then w k else 0; let high := fun (n k : ℕ) => w k-low n k; let I := fun (n:ℕ) (a b:ℕ→ℝ) => intervalIntegral (fun t => (arcs n)ᶜ.indicator (fun u => S n a u*S n b u*E (-(n:ℝ)*u)) t) (0:ℝ) 1 MeasureTheory.volume; let L := fun n : ℕ => max 1 (Nat.log 2 n / 2); let K := fun (n : ℕ) (t : ℝ) => (∑ j ∈ Finset.range (L n), Real.cos (2*Real.pi*(2:ℝ)^(j+1)*t))/(L n:ℝ); let B := fun n : ℕ => {t : ℝ | t ∉ arcs n ∧ (1:ℝ)/2 < K n t}; let U := fun (n : ℕ) (a : ℕ → ℝ) => intervalIntegral ((B n).indicator (fun t => ‖S n a t‖^2)) (0:ℝ) 1 MeasureTheory.volume; let V := fun (n h : ℕ) => intervalIntegral ((B n).indicator (fun t => Real.cos (2*Real.pi*(h:ℝ)*t))) (0:ℝ) 1 MeasureTheory.volume; let A := fun (n h : ℕ) (a : ℕ → ℝ) => ∑ k ∈ Finset.range (n+1-h), a k * a (k+h); let model := fun k : ℕ => if Nat.Coprime k 30 then (30:ℝ)/8 else 0; let short := fun (n : ℕ) (a : ℕ → ℝ) => A n 0 a * V n 0 + 2*(∑ h ∈ Finset.Icc 1 (min n ((L n)^2)), A n h a * V n h); let long := fun (n : ℕ) (a : ℕ → ℝ) => 2*(∑ h ∈ Finset.Icc ((L n)^2+1) n, A n h a * V n h); ∀ (n a m : ℕ), |∑ j ∈ Finset.range m, V n (2*(a+j))| ≤ intervalIntegral ((B n).indicator (fun t => if Real.sin (2*Real.pi*t) = 0 then (m:ℝ) else min (m:ℝ) (1/|Real.sin (2*Real.pi*t)|))) (0:ℝ) 1 MeasureTheory.volume := by
  intro w E S Q arcs low high I L K B U V A model short long
  intro n a m
  have hB : MeasurableSet (B n) := by
    have h1 : MeasurableSet (arcs n) := meas_arcs (Q n) n
    have h2 : MeasurableSet {t : ℝ | (1:ℝ)/2 < K n t} :=
      measurableSet_lt measurable_const (Continuous.measurable (by fun_prop))
    exact h1.compl.inter h2
  exact key (B n) hB a m
