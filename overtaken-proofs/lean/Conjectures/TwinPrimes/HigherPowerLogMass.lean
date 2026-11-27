import Mathlib

theorem Conjectures.TwinPrimes.HigherPowerLogMass :
    let Λ := ArithmeticFunction.vonMangoldt; ∃ C : ℝ, 0 < C ∧ ∀ Y : ℕ, 2 ≤ Y → (@Finset.filter ℕ (fun n => ∃ p k : ℕ, p.Prime ∧ 3 ≤ k ∧ n = p^k) (fun _ => Classical.propDecidable _) (Finset.range (Y+1))).sum (fun n => Λ n) ≤ C*(Y:ℝ)^(1/3:ℝ)*Real.log (2+(Y:ℝ)) := by
  intro Λ
  classical
  refine ⟨2 * Real.log 4, by positivity, ?_⟩
  intro Y hY
  set L := Nat.log 2 Y with hL
  set T : Finset ℕ := (Finset.Icc 0 ⌊(Y:ℝ)^(1/3:ℝ)⌋₊).filter Nat.Prime with hT
  have hY0 : (0:ℝ) ≤ Y := by positivity
  have hsub : (@Finset.filter ℕ (fun n => ∃ p k : ℕ, p.Prime ∧ 3 ≤ k ∧ n = p^k)
      (fun _ => Classical.propDecidable _) (Finset.range (Y+1))) ⊆
      (Finset.Icc 3 L ×ˢ T).image (fun x : ℕ × ℕ => x.2 ^ x.1) := by
    intro n hn
    rw [Finset.mem_filter, Finset.mem_range] at hn
    obtain ⟨hnY, p, k, hp, hk, rfl⟩ := hn
    rw [Finset.mem_image]
    refine ⟨(k, p), ?_, rfl⟩
    have hp2 := hp.two_le
    have hpk : p ^ k ≤ Y := by omega
    have h3 : p ^ 3 ≤ Y := le_trans (Nat.pow_le_pow_right (by omega) hk) hpk
    have hkL : k ≤ L := Nat.le_log_of_pow_le (by norm_num) (le_trans (Nat.pow_le_pow_left hp2 k) hpk)
    rw [Finset.mem_product, Finset.mem_Icc, hT, Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨hk, hkL⟩, ⟨Nat.zero_le _, ?_⟩, hp⟩
    rw [Nat.le_floor_iff (by positivity)]
    have : (p:ℝ)^3 ≤ Y := by exact_mod_cast h3
    have h1 : ((p:ℝ)^3)^(1/3:ℝ) ≤ (Y:ℝ)^(1/3:ℝ) :=
      Real.rpow_le_rpow (by positivity) this (by norm_num)
    have h2 : ((p:ℝ)^3)^(1/3:ℝ) = p := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
      norm_num
    rwa [h2] at h1
  have hnn : ∀ n, 0 ≤ Λ n := fun n => ArithmeticFunction.vonMangoldt_nonneg
  have h1 := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => hnn i)
  have h2 := Finset.sum_image_le_of_nonneg (s := Finset.Icc 3 L ×ˢ T)
    (g := fun x : ℕ × ℕ => x.2 ^ x.1) (f := fun n => Λ n) (fun u _ => hnn u)
  refine h1.trans (h2.trans ?_)
  have h3 : ∑ x ∈ Finset.Icc 3 L ×ˢ T, Λ (x.2 ^ x.1) = ∑ x ∈ Finset.Icc 3 L ×ˢ T, Real.log x.2 := by
    apply Finset.sum_congr rfl
    intro x hx
    rw [Finset.mem_product, hT, Finset.mem_filter] at hx
    have hk : x.1 ≠ 0 := by have := (Finset.mem_Icc.mp hx.1).1; omega
    show ArithmeticFunction.vonMangoldt (x.2 ^ x.1) = _
    rw [ArithmeticFunction.vonMangoldt_apply_pow hk, ArithmeticFunction.vonMangoldt_apply_prime hx.2.2]
  rw [h3, Finset.sum_product]
  have hth : ∀ k : ℕ, ∑ p ∈ T, Real.log p ≤ Real.log 4 * (Y:ℝ)^(1/3:ℝ) := by
    intro k
    have := Chebyshev.theta_le_log4_mul_x (x := (Y:ℝ)^(1/3:ℝ)) (by positivity)
    rwa [Chebyshev.theta_eq_sum_Icc] at this
  have h4 : ∑ k ∈ Finset.Icc 3 L, ∑ p ∈ T, Real.log p ≤
      ∑ k ∈ Finset.Icc 3 L, Real.log 4 * (Y:ℝ)^(1/3:ℝ) :=
    Finset.sum_le_sum (fun k _ => hth k)
  refine h4.trans ?_
  rw [Finset.sum_const, nsmul_eq_mul]
  have hc : ((Finset.Icc 3 L).card : ℝ) ≤ L := by
    rw [Nat.card_Icc]; exact_mod_cast (by omega : L + 1 - 3 ≤ L)
  have hpow : 2 ^ L ≤ Y := Nat.pow_log_le_self 2 (by omega)
  have hlog2 : (L:ℝ) * Real.log 2 ≤ Real.log Y := by
    rw [← Real.log_pow]
    apply Real.log_le_log (by positivity)
    exact_mod_cast hpow
  have hl2 : (1/2:ℝ) ≤ Real.log 2 := by
    have := Real.log_two_gt_d9; linarith
  have hLle : (L:ℝ) ≤ 2 * Real.log (2 + Y) := by
    have h5 : Real.log Y ≤ Real.log (2 + Y) :=
      Real.log_le_log (by have : (2:ℝ) ≤ Y := by exact_mod_cast hY
                          linarith) (by linarith)
    have : (0:ℝ) ≤ L := by positivity
    nlinarith
  have hc4 : 0 ≤ Real.log 4 * (Y:ℝ)^(1/3:ℝ) := by positivity
  calc ((Finset.Icc 3 L).card : ℝ) * (Real.log 4 * (Y:ℝ)^(1/3:ℝ))
      ≤ (2 * Real.log (2 + Y)) * (Real.log 4 * (Y:ℝ)^(1/3:ℝ)) :=
        mul_le_mul_of_nonneg_right (hc.trans hLle) hc4
    _ = 2 * Real.log 4 * (Y:ℝ)^(1/3:ℝ) * Real.log (2 + Y) := by ring
