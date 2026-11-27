import Mathlib

theorem Conjectures.TwinPrimes.ShiftedSquareWindowLoss :
    let w := fun (X : ℕ) => (Finset.range (2*X+1)).filter (fun n => X < n ∧ 50*n < 51*X); let Q := fun (X : ℕ) => ((w X).filter (fun p => p.Prime ∧ (Nat.sqrt (p+2)).Prime ∧ p+2=(Nat.sqrt (p+2))^2)); let L := fun (p : ℕ) => Real.log p * Real.log (p+2); ∃ C : ℝ, 0 < C ∧ ∀ X : ℕ, 2 ≤ X → (Q X).sum L ≤ C*Real.sqrt X*Real.log (2+(X:ℝ)) := by
  intro w Q L
  refine ⟨24, by norm_num, ?_⟩
  intro X hX
  set R := Nat.sqrt (2*X+2) with hR
  have hXr : (2:ℝ) ≤ X := by exact_mod_cast hX
  have hmem : ∀ p ∈ Q X, p ≤ 2*X ∧ 0 < p ∧ (Nat.sqrt (p+2)).Prime ∧ p+2 = (Nat.sqrt (p+2))^2 := by
    intro p hp
    simp only [Q, w, Finset.mem_filter, Finset.mem_range] at hp
    exact ⟨by omega, hp.2.1.pos, hp.2.2.1, hp.2.2.2⟩
  have hterm : ∀ p ∈ Q X, L p ≤ 2 * Real.log (2*X) * Real.log (Nat.sqrt (p+2) : ℕ) := by
    intro p hp
    obtain ⟨h1, h2, h3, h4⟩ := hmem p hp
    have hp0 : (0:ℝ) < p := by exact_mod_cast h2
    have hr0 : (0:ℝ) < (Nat.sqrt (p+2) : ℕ) := by exact_mod_cast h3.pos
    have e : Real.log ((p:ℝ)+2) = 2 * Real.log (Nat.sqrt (p+2) : ℕ) := by
      have : ((p:ℝ)+2) = ((Nat.sqrt (p+2) : ℕ):ℝ)^2 := by exact_mod_cast h4
      rw [this, Real.log_pow]; norm_num
    have hl : Real.log p ≤ Real.log (2*X) := by
      apply Real.log_le_log hp0
      exact_mod_cast h1
    have hlr : 0 ≤ Real.log (Nat.sqrt (p+2) : ℕ) := Real.log_nonneg (by exact_mod_cast h3.one_lt.le)
    show Real.log p * Real.log ((p:ℝ)+2) ≤ _
    rw [e]
    nlinarith
  have hinj : Set.InjOn (fun p => Nat.sqrt (p+2)) (Q X : Set ℕ) := by
    intro a ha b hb hab
    have h1 := (hmem a ha).2.2.2
    have h2 := (hmem b hb).2.2.2
    simp only at hab
    rw [hab] at h1
    omega
  have himg : (Q X).image (fun p => Nat.sqrt (p+2)) ⊆ (Finset.Ioc 0 R).filter Nat.Prime := by
    intro r hr
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hr
    obtain ⟨h1, h2, h3, h4⟩ := hmem p hp
    simp only [Finset.mem_filter, Finset.mem_Ioc]
    refine ⟨⟨h3.pos, ?_⟩, h3⟩
    rw [hR]
    apply Nat.sqrt_le_sqrt
    omega
  have hsum : ∑ p ∈ Q X, Real.log (Nat.sqrt (p+2) : ℕ) ≤ Chebyshev.theta (R:ℝ) := by
    rw [Chebyshev.theta]
    simp only [Nat.floor_natCast]
    rw [← Finset.sum_image (f := fun r : ℕ => Real.log r) hinj]
    apply Finset.sum_le_sum_of_subset_of_nonneg himg
    intro i hi _
    exact Real.log_natCast_nonneg i
  have hth : Chebyshev.theta (R:ℝ) ≤ Real.log 4 * R := Chebyshev.theta_le_log4_mul_x (by positivity)
  have hRle : (R:ℝ) ≤ 2 * Real.sqrt X := by
    have h1 : (R:ℝ) ≤ Real.sqrt ((2*X+2 : ℕ):ℝ) := Real.nat_sqrt_le_real_sqrt
    have h2 : Real.sqrt ((2*X+2 : ℕ):ℝ) ≤ Real.sqrt (4 * X) := by
      apply Real.sqrt_le_sqrt
      push_cast
      linarith
    have h3 : Real.sqrt (4 * (X:ℝ)) = 2 * Real.sqrt X := by
      rw [Real.sqrt_mul (by norm_num), show (4:ℝ) = 2^2 by norm_num, Real.sqrt_sq (by norm_num)]
    linarith
  have hlog4 : Real.log 4 ≤ 3 := by
    have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 4 by norm_num)
    linarith
  have hlog4n : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hl2 : Real.log (2*X) ≤ 2 * Real.log (2+(X:ℝ)) := by
    rw [← Real.log_rpow (by linarith)]
    apply Real.log_le_log (by linarith)
    rw [show ((2:ℝ)) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]
    nlinarith
  have hl2n : 0 ≤ Real.log (2*(X:ℝ)) := Real.log_nonneg (by linarith)
  have hsq : 0 ≤ Real.sqrt X := Real.sqrt_nonneg _
  have hLn : 0 ≤ Real.log (2+(X:ℝ)) := Real.log_nonneg (by linarith)
  calc (Q X).sum L ≤ ∑ p ∈ Q X, 2 * Real.log (2*X) * Real.log (Nat.sqrt (p+2) : ℕ) :=
        Finset.sum_le_sum hterm
    _ = 2 * Real.log (2*X) * ∑ p ∈ Q X, Real.log (Nat.sqrt (p+2) : ℕ) := by rw [Finset.mul_sum]
    _ ≤ 2 * Real.log (2*X) * (Real.log 4 * R) := by
        apply mul_le_mul_of_nonneg_left (hsum.trans hth) (by positivity)
    _ ≤ 2 * Real.log (2*X) * (3 * (2 * Real.sqrt X)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact mul_le_mul hlog4 hRle (by positivity) (by norm_num)
    _ ≤ 2 * (2 * Real.log (2+(X:ℝ))) * (3 * (2 * Real.sqrt X)) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        linarith
    _ = 24 * Real.sqrt X * Real.log (2+(X:ℝ)) := by ring
