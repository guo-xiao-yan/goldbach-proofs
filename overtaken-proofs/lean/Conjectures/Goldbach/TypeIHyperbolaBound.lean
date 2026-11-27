import Mathlib

private lemma tih_geom (y : ℝ) (M : ℕ) :
    ‖∑ k ∈ Finset.Icc 1 M, Complex.exp (((2 * Real.pi * ((k : ℝ) * y) : ℝ) : ℂ) * Complex.I)‖ ≤
      if Complex.exp (((2 * Real.pi * y : ℝ) : ℂ) * Complex.I) = 1 then (M : ℝ)
      else min (M : ℝ) (2 / ‖1 - Complex.exp (((2 * Real.pi * y : ℝ) : ℂ) * Complex.I)‖) := by
  set z : ℂ := Complex.exp (((2 * Real.pi * y : ℝ) : ℂ) * Complex.I) with hz
  have hpow : ∀ k : ℕ, Complex.exp (((2 * Real.pi * ((k : ℝ) * y) : ℝ) : ℂ) * Complex.I) = z ^ k := by
    intro k
    rw [hz, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  simp_rw [hpow]
  have hn : ‖z‖ = 1 := by
    rw [hz]; exact Complex.norm_exp_ofReal_mul_I _
  have h1 : ‖∑ k ∈ Finset.Icc 1 M, z ^ k‖ ≤ (M : ℝ) := by
    calc ‖∑ k ∈ Finset.Icc 1 M, z ^ k‖ ≤ ∑ k ∈ Finset.Icc 1 M, ‖z ^ k‖ := norm_sum_le _ _
      _ = (M : ℝ) := by simp [norm_pow, hn]
  split_ifs with h
  · exact h1
  · refine le_min h1 ?_
    have hne : z - 1 ≠ 0 := sub_ne_zero.mpr h
    have key : ∀ m : ℕ, (z - 1) * ∑ k ∈ Finset.Icc 1 m, z ^ k = z ^ (m + 1) - z := by
      intro m
      induction m with
      | zero => simp
      | succ m ih =>
        rw [Finset.sum_Icc_succ_top (by omega), mul_add, ih]
        ring
    have hb : ‖z - 1‖ * ‖∑ k ∈ Finset.Icc 1 M, z ^ k‖ ≤ 2 := by
      rw [← norm_mul, key]
      calc ‖z ^ (M + 1) - z‖ ≤ ‖z ^ (M + 1)‖ + ‖z‖ := norm_sub_le _ _
        _ = 2 := by simp [norm_pow, hn]; norm_num
    have hpos : 0 < ‖z - 1‖ := norm_pos_iff.mpr hne
    have hpos' : 0 < ‖1 - z‖ := by rw [norm_sub_rev]; exact hpos
    rw [le_div_iff₀ hpos', norm_sub_rev 1 z]
    linarith [mul_comm ‖z - 1‖ ‖∑ k ∈ Finset.Icc 1 M, z ^ k‖]

theorem Conjectures.Goldbach.TypeIHyperbolaBound :
    let E (x : ℝ) := Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I); let cap (H : ℕ) (x : ℝ) := if E x = 1 then (H : ℝ) else min (H : ℝ) (2 / ‖1 - E x‖); ∀ (N D : ℕ) (a : ℕ → ℂ) (t : ℝ), ‖∑ d ∈ Finset.Icc 1 D, a d * ∑ k ∈ Finset.Icc 1 (N / d), E ((d : ℝ) * (k : ℝ) * t)‖ ≤ ∑ d ∈ Finset.Icc 1 D, ‖a d‖ * cap (N / d) ((d : ℝ) * t) := by
  intro E cap N D a t
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun d _ => ?_)
  rw [norm_mul]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  have h := tih_geom ((d : ℝ) * t) (N / d)
  have e : ∀ k : ℕ, E ((d : ℝ) * (k : ℝ) * t) =
      Complex.exp (((2 * Real.pi * ((k : ℝ) * ((d : ℝ) * t)) : ℝ) : ℂ) * Complex.I) := by
    intro k
    show Complex.exp _ = _
    congr 3
    ring
  simp_rw [e]
  exact h
