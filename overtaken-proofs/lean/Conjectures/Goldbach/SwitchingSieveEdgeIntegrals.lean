import Mathlib

private noncomputable def ssei_P (y : ℝ) : ℝ :=
  ∑ k ∈ Finset.range 17, ((-1 : ℝ) ^ k / ((k : ℝ) + 1)) * y ^ (k + 1)

private theorem ssei_P_deriv (x : ℝ) :
    HasDerivAt ssei_P (∑ k ∈ Finset.range 17, (-x) ^ k) x := by
  unfold ssei_P
  apply HasDerivAt.fun_sum (A := fun (k : ℕ) (y : ℝ) => ((-1 : ℝ) ^ k / ((k : ℝ) + 1)) * y ^ (k + 1))
  intro k _
  have h := (hasDerivAt_pow (k + 1) x).const_mul ((-1 : ℝ) ^ k / ((k : ℝ) + 1))
  convert h using 1
  have hk : ((k : ℝ) + 1) ≠ 0 := by positivity
  push_cast
  rw [neg_pow x k]
  field_simp

private theorem ssei_geom (x : ℝ) :
    (1 + x) * ∑ k ∈ Finset.range 17, (-x) ^ k = 1 + x ^ 17 := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  ring

private theorem ssei_log_le (s : ℝ) (hs : 0 ≤ s) :
    Real.log (1 + s) ≤ ssei_P s := by
  have hcont : ContinuousOn (fun y => ssei_P y - Real.log (1 + y)) (Set.Ici 0) := by
    apply ContinuousOn.sub
    · exact fun x _ => (ssei_P_deriv x).continuousAt.continuousWithinAt
    · apply ContinuousOn.log
      · fun_prop
      · intro x hx
        have : (0 : ℝ) ≤ x := hx
        linarith
  have hmono : MonotoneOn (fun y => ssei_P y - Real.log (1 + y)) (Set.Ici 0) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0) hcont
      (f' := fun x => (∑ k ∈ Finset.range 17, (-x) ^ k) - 1 / (1 + x))
    · intro x hx
      rw [interior_Ici] at hx
      have hx0 : (0 : ℝ) < x := hx
      have h2 : HasDerivAt (fun y : ℝ => Real.log (1 + y)) (1 / (1 + x)) x := by
        have := ((hasDerivAt_id x).const_add 1).log (by simp; linarith)
        simpa using this
      exact ((ssei_P_deriv x).sub h2).hasDerivWithinAt
    · intro x hx
      rw [interior_Ici] at hx
      have hx0 : (0 : ℝ) < x := hx
      have e := ssei_geom x
      have hp : 0 ≤ x ^ 17 := by positivity
      rw [sub_nonneg, div_le_iff₀ (by linarith)]
      nlinarith
  have := hmono (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hs) hs
  have h0 : ssei_P 0 = 0 := by simp [ssei_P]
  simp only [h0] at this
  simpa using this

private noncomputable def ssei_J (k : ℕ) : ℝ := ∫ t in (2 : ℝ)..(8 / 3 : ℝ), (t - 2) ^ k / t

private theorem ssei_cont (k : ℕ) :
    ContinuousOn (fun t : ℝ => (t - 2) ^ k / t) (Set.uIcc 2 (8 / 3)) := by
  apply ContinuousOn.div
  · exact ((continuous_id.sub continuous_const).pow k).continuousOn
  · fun_prop
  · intro t ht
    rw [Set.uIcc_of_le (by norm_num)] at ht
    have : (2 : ℝ) ≤ t := ht.1
    linarith

private theorem ssei_int (k : ℕ) :
    IntervalIntegrable (fun t : ℝ => (t - 2) ^ k / t) MeasureTheory.volume 2 (8 / 3) :=
  (ssei_cont k).intervalIntegrable

private theorem ssei_J0 : ssei_J 0 = Real.log (4 / 3) := by
  unfold ssei_J
  simp only [pow_zero]
  rw [integral_one_div_of_pos (by norm_num) (by norm_num)]
  norm_num

private theorem ssei_Jrec (k : ℕ) :
    ssei_J (k + 1) = (2 / 3 : ℝ) ^ (k + 1) / ((k : ℝ) + 1) - 2 * ssei_J k := by
  unfold ssei_J
  have h1 : ∫ t in (2 : ℝ)..(8 / 3 : ℝ), (t - 2) ^ (k + 1) / t
      = ∫ t in (2 : ℝ)..(8 / 3 : ℝ), ((t - 2) ^ k - 2 * ((t - 2) ^ k / t)) := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le (by norm_num)] at ht
    have : (2 : ℝ) ≤ t := ht.1
    have ht0 : t ≠ 0 := by linarith
    field_simp
    ring
  rw [h1, intervalIntegral.integral_sub, intervalIntegral.integral_const_mul]
  · congr 1
    have := intervalIntegral.integral_comp_sub_right (a := (2 : ℝ)) (b := 8 / 3)
      (fun x : ℝ => x ^ k) 2
    beta_reduce at this
    rw [this, integral_pow]
    norm_num
  · exact ((continuous_id.sub continuous_const).pow k).intervalIntegrable _ _
  · exact (ssei_int k).const_mul 2

theorem Conjectures.Goldbach.SwitchingSieveEdgeIntegrals :
    8 * Real.log (10 / 9) ≤ (0.84289 : ℝ) ∧ 8 * ∫ t in (2 : ℝ)..(8 / 3 : ℝ), Real.log (t - 1) / t ≤ (0.60962 : ℝ) := by
  constructor
  · have h : Real.log (10 / 9) ≤ 0.84289 / 8 := by
      rw [Real.log_le_iff_le_exp (by norm_num)]
      have := Real.sum_le_exp_of_nonneg (x := (0.84289 / 8 : ℝ)) (by norm_num) 8
      refine le_trans ?_ this
      norm_num [Finset.sum_range_succ, Nat.factorial]
    linarith
  · have hL : ∑ k ∈ Finset.range 24, (1 / 4 : ℝ) ^ (k + 1) / ((k : ℝ) + 1) ≤ Real.log (4 / 3) := by
      have h := Real.hasSum_pow_div_log_of_abs_lt_one (x := (1 / 4 : ℝ)) (by norm_num [abs_of_pos])
      have e : Real.log (4 / 3) = -Real.log (1 - 1 / 4) := by
        rw [← Real.log_inv]; norm_num
      rw [e]
      have h' : HasSum (fun n : ℕ => (1 / 4 : ℝ) ^ (n + 1) / ((n : ℝ) + 1)) (-Real.log (1 - 1 / 4)) := h
      exact sum_le_hasSum (Finset.range 24) (fun i _ => by positivity) h'
    have hle : ∫ t in (2 : ℝ)..(8 / 3 : ℝ), Real.log (t - 1) / t ≤
        ∫ t in (2 : ℝ)..(8 / 3 : ℝ), ∑ k ∈ Finset.range 17,
          ((-1 : ℝ) ^ k / ((k : ℝ) + 1)) * ((t - 2) ^ (k + 1) / t) := by
      apply intervalIntegral.integral_mono_on (by norm_num)
      · apply ContinuousOn.intervalIntegrable
        apply ContinuousOn.div
        · apply ContinuousOn.log
          · fun_prop
          · intro t ht
            rw [Set.uIcc_of_le (by norm_num)] at ht
            have : (2 : ℝ) ≤ t := ht.1
            linarith
        · fun_prop
        · intro t ht
          rw [Set.uIcc_of_le (by norm_num)] at ht
          have : (2 : ℝ) ≤ t := ht.1
          linarith
      · apply ContinuousOn.intervalIntegrable
        apply continuousOn_finsetSum
        intro k _
        exact continuousOn_const.mul (ssei_cont (k + 1))
      · intro t ht
        have h2 : (2 : ℝ) ≤ t := ht.1
        have ht0 : 0 < t := by linarith
        have hp := ssei_log_le (t - 2) (by linarith)
        have e : Real.log (t - 1) = Real.log (1 + (t - 2)) := by ring_nf
        rw [e]
        have e2 : ∑ k ∈ Finset.range 17, ((-1 : ℝ) ^ k / ((k : ℝ) + 1)) * ((t - 2) ^ (k + 1) / t)
            = (∑ k ∈ Finset.range 17, ((-1 : ℝ) ^ k / ((k : ℝ) + 1)) * (t - 2) ^ (k + 1)) / t := by
          rw [Finset.sum_div]
          apply Finset.sum_congr rfl
          intro k _
          ring
        rw [e2]
        exact div_le_div_of_nonneg_right hp ht0.le
    have hsum : ∫ t in (2 : ℝ)..(8 / 3 : ℝ), ∑ k ∈ Finset.range 17,
          ((-1 : ℝ) ^ k / ((k : ℝ) + 1)) * ((t - 2) ^ (k + 1) / t)
        = ∑ k ∈ Finset.range 17, ((-1 : ℝ) ^ k / ((k : ℝ) + 1)) * ssei_J (k + 1) := by
      rw [intervalIntegral.integral_finsetSum]
      · apply Finset.sum_congr rfl
        intro k _
        rw [intervalIntegral.integral_const_mul]
        rfl
      · intro k _
        exact (ssei_int (k + 1)).const_mul _
    rw [hsum] at hle
    have hJ0 := ssei_J0
    have e1 := ssei_Jrec 0
    have e2 := ssei_Jrec 1
    have e3 := ssei_Jrec 2
    have e4 := ssei_Jrec 3
    have e5 := ssei_Jrec 4
    have e6 := ssei_Jrec 5
    have e7 := ssei_Jrec 6
    have e8 := ssei_Jrec 7
    have e9 := ssei_Jrec 8
    have e10 := ssei_Jrec 9
    have e11 := ssei_Jrec 10
    have e12 := ssei_Jrec 11
    have e13 := ssei_Jrec 12
    have e14 := ssei_Jrec 13
    have e15 := ssei_Jrec 14
    have e16 := ssei_Jrec 15
    have e17 := ssei_Jrec 16
    norm_num [Finset.sum_range_succ] at hle e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 hL
    norm_num
    linarith
