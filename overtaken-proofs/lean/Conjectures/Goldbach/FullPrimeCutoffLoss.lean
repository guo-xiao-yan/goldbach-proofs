import Mathlib

private theorem fpcl_sum_w_le (m : ℕ) :
    Finset.sum (Finset.range (m + 1)) (fun k => if Nat.Prime k then Real.log (k : ℝ) else 0)
      ≤ Real.log 4 * (m : ℝ) := by
  have h := Chebyshev.theta_le_log4_mul_x (x := (m : ℝ)) (Nat.cast_nonneg m)
  have h2 : Chebyshev.theta (m : ℝ) = Finset.sum (Finset.range (m + 1))
      (fun k => if Nat.Prime k then Real.log (k : ℝ) else 0) := by
    unfold Chebyshev.theta
    rw [Nat.floor_natCast, ← Finset.sum_filter]
    have : (Finset.Ioc 0 m).filter Nat.Prime = (Finset.range (m + 1)).filter Nat.Prime := by
      ext p
      simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_range]
      constructor
      · rintro ⟨⟨_, h⟩, hp⟩; exact ⟨by omega, hp⟩
      · rintro ⟨h, hp⟩; exact ⟨⟨hp.pos, by omega⟩, hp⟩
    rw [this, Finset.sum_filter]
  rw [← h2]; exact h

theorem Conjectures.Goldbach.FullPrimeCutoffLoss :
    let w := fun k : ℕ => if Nat.Prime k then Real.log (k : ℝ) else 0; let high := fun m k : ℕ => if k ≤ m then 0 else w k; let R := fun (a : ℕ → ℝ) (n : ℕ) => Finset.sum (Finset.range (n + 1)) (fun k => a k * a (n - k)); ∀ n m : ℕ, 2 * m < n → R w n - R (high m) n = 2 * Finset.sum (Finset.range (m + 1)) (fun k => w k * w (n - k)) ∧ 0 ≤ R w n - R (high m) n ∧ R w n - R (high m) n ≤ 2 * Real.log 4 * (m : ℝ) * Real.log (n : ℝ) := by
  intro w high R n m h
  have hw0 : ∀ k, 0 ≤ w k := by
    intro k
    simp only [w]
    split_ifs with hk
    · exact Real.log_nonneg (by exact_mod_cast hk.one_lt.le)
    · exact le_rfl
  have hwle : ∀ k, k ≤ n → w k ≤ Real.log (n : ℝ) := by
    intro k hk
    simp only [w]
    split_ifs with hp
    · exact Real.log_le_log (by exact_mod_cast hp.pos) (by exact_mod_cast hk)
    · exact Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n))
  set A : ℕ → ℝ := fun k => if k ≤ m then w k * w (n - k) else 0 with hA
  have hpt : ∀ k ∈ Finset.range (n + 1),
      w k * w (n - k) - high m k * high m (n - k) = A k + A (n - k) := by
    intro k hk
    rw [Finset.mem_range] at hk
    simp only [hA, high]
    have e : n - (n - k) = k := by omega
    rw [e]
    by_cases h1 : k ≤ m
    · have h2 : ¬ (n - k ≤ m) := by omega
      simp [h1, h2]
    · by_cases h2 : n - k ≤ m
      · simp [h1, h2, mul_comm]
      · simp [h1, h2]
  have hsumA : Finset.sum (Finset.range (n + 1)) A
      = Finset.sum (Finset.range (m + 1)) (fun k => w k * w (n - k)) := by
    simp only [hA]
    rw [← Finset.sum_filter]
    have : (Finset.range (n + 1)).filter (fun k => k ≤ m) = Finset.range (m + 1) := by
      ext p; simp only [Finset.mem_filter, Finset.mem_range]; omega
    rw [this]
  have hrefl : Finset.sum (Finset.range (n + 1)) (fun k => A (n - k))
      = Finset.sum (Finset.range (n + 1)) A := by
    have := Finset.sum_range_reflect A (n + 1)
    simpa using this
  have hdiff : R w n - R (high m) n = 2 * Finset.sum (Finset.range (m + 1)) (fun k => w k * w (n - k)) := by
    simp only [R]
    rw [← Finset.sum_sub_distrib, Finset.sum_congr rfl hpt, Finset.sum_add_distrib, hrefl, hsumA]
    ring
  refine ⟨hdiff, ?_, ?_⟩
  · rw [hdiff]
    have : 0 ≤ Finset.sum (Finset.range (m + 1)) (fun k => w k * w (n - k)) :=
      Finset.sum_nonneg (fun k _ => mul_nonneg (hw0 _) (hw0 _))
    linarith
  · rw [hdiff]
    have hb : Finset.sum (Finset.range (m + 1)) (fun k => w k * w (n - k))
        ≤ Finset.sum (Finset.range (m + 1)) (fun k => w k * Real.log (n : ℝ)) :=
      Finset.sum_le_sum (fun k _ => mul_le_mul_of_nonneg_left (hwle _ (by omega)) (hw0 k))
    rw [← Finset.sum_mul] at hb
    have hc : Finset.sum (Finset.range (m + 1)) w ≤ Real.log 4 * (m : ℝ) := fpcl_sum_w_le m
    have hl : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n))
    have := mul_le_mul_of_nonneg_right hc hl
    nlinarith
