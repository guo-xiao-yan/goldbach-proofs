import Mathlib

private lemma prcs_eventually : ∃ M : ℕ, ∀ m : ℕ, M ≤ m → 5776 * m ^ 8 + 2 ≤ 2 ^ m := by
  have h := tendsto_pow_const_div_const_pow_of_one_lt 8 (r := (2:ℝ)) (by norm_num)
  have h2 := (h.eventually (gt_mem_nhds (show (0:ℝ) < 1 / 5778 by norm_num)))
  rw [Filter.eventually_atTop] at h2
  obtain ⟨M, hM⟩ := h2
  refine ⟨max M 1, fun m hm => ?_⟩
  have h1 := hM m (le_trans (le_max_left _ _) hm)
  have hm1 : (1:ℝ) ≤ m := by exact_mod_cast le_trans (le_max_right _ _) hm
  have hp : (0:ℝ) < 2 ^ m := by positivity
  rw [div_lt_iff₀ hp] at h1
  have h8 : (1:ℝ) ≤ (m:ℝ) ^ 8 := one_le_pow₀ hm1
  have : (5776 * m ^ 8 + 2 : ℝ) ≤ 2 ^ m := by nlinarith
  exact_mod_cast this

private lemma prcs_sum (L : ℕ) : (∑ j ∈ Finset.range L, (2:ℝ) ^ (j + 1)) ≤ 2 ^ (L + 1) := by
  induction L with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ]
    have : (2:ℝ) ^ (k + 1 + 1) = 2 * 2 ^ (k + 1) := by ring
    have h2 : (0:ℝ) < 2 ^ (k + 1) := by positivity
    nlinarith

theorem Conjectures.Goldbach.PacketRationalCenterStability :
    let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let L := fun n : ℕ => max 1 (Nat.log 2 n / 2); let K := fun (n : ℕ) (t : ℝ) => (∑ j ∈ Finset.range (L n), Real.cos (2*Real.pi*(2:ℝ)^(j+1)*t))/(L n:ℝ); ∃ N : ℕ, ∀ n ≥ N, ∀ x y : ℝ, |x-y| ≤ (Q n:ℝ)^2/(n:ℝ) → (1:ℝ)/2 < K n x → (1:ℝ)/3 < K n y := by
  intro Q L K
  obtain ⟨M, hM⟩ := prcs_eventually
  refine ⟨max 4 (2 ^ M), fun n hn x y hxy hx => ?_⟩
  have hn4 : 4 ≤ n := le_trans (le_max_left _ _) hn
  have hnM : 2 ^ M ≤ n := le_trans (le_max_right _ _) hn
  set m := Nat.log 2 (n+2) with hm
  have hmM : M ≤ m := Nat.le_log_of_pow_le (by norm_num) (by omega)
  have h1 := hM m hmM
  have h2 : 2 ^ m ≤ n + 2 := Nat.pow_log_le_self 2 (by omega)
  have h3 : 5776 * m ^ 8 ≤ n := by omega
  have h3r : (5776 * (m:ℝ) ^ 8) ≤ n := by exact_mod_cast h3
  have hLdef : L n = Nat.log 2 n / 2 := by
    have : 2 ≤ Nat.log 2 n := by
      have := Nat.le_log_of_pow_le (b := 2) (x := 2) (y := n) (by norm_num) (by omega)
      exact this
    show max 1 (Nat.log 2 n / 2) = _
    omega
  have hL1 : 1 ≤ L n := le_max_left _ _
  have hT : (2:ℕ) ^ (L n) * 2 ^ (L n) ≤ n := by
    rw [← pow_add]
    calc 2 ^ (L n + L n) ≤ 2 ^ (Nat.log 2 n) := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ ≤ n := Nat.pow_log_le_self 2 (by omega)
  have hTr : (2:ℝ) ^ (L n) * 2 ^ (L n) ≤ n := by exact_mod_cast hT
  set T : ℝ := 2 ^ (L n) with hTdef
  have hTpos : 0 < T := by positivity
  have hnpos : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hQ : (Q n : ℝ) ^ 2 = (m:ℝ) ^ 4 := by
    show (((Nat.log 2 (n+2))^2 : ℕ) : ℝ) ^ 2 = _
    push_cast; ring
  rw [hQ] at hxy
  have hLpos : (0:ℝ) < L n := by exact_mod_cast hL1
  have hd : |K n x - K n y| ≤ 4 * Real.pi * T * ((m:ℝ) ^ 4 / n) := by
    have e : K n x - K n y = (∑ j ∈ Finset.range (L n), (Real.cos (2*Real.pi*(2:ℝ)^(j+1)*x) - Real.cos (2*Real.pi*(2:ℝ)^(j+1)*y))) / (L n : ℝ) := by
      show (∑ j ∈ Finset.range (L n), Real.cos (2*Real.pi*(2:ℝ)^(j+1)*x))/(L n:ℝ) - (∑ j ∈ Finset.range (L n), Real.cos (2*Real.pi*(2:ℝ)^(j+1)*y))/(L n:ℝ) = _
      rw [← sub_div, Finset.sum_sub_distrib]
    rw [e, abs_div, abs_of_pos hLpos, div_le_iff₀ hLpos]
    have hs : |∑ j ∈ Finset.range (L n), (Real.cos (2*Real.pi*(2:ℝ)^(j+1)*x) - Real.cos (2*Real.pi*(2:ℝ)^(j+1)*y))| ≤ ∑ j ∈ Finset.range (L n), 2 * Real.pi * (2:ℝ)^(j+1) * |x - y| := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
      refine (Real.abs_cos_sub_cos_le _ _).trans (le_of_eq ?_)
      rw [← mul_sub, abs_mul, abs_of_pos (by positivity)]
    refine hs.trans ?_
    have hre : ∑ j ∈ Finset.range (L n), 2 * Real.pi * (2:ℝ)^(j+1) * |x - y| = 2 * Real.pi * (∑ j ∈ Finset.range (L n), (2:ℝ) ^ (j + 1)) * |x - y| := by
      rw [Finset.mul_sum, Finset.sum_mul]
    rw [hre]
    have hsum := prcs_sum (L n)
    have hxy' : |x - y| ≤ (m:ℝ)^4 / n := hxy
    have hpi := Real.pi_pos
    have hP : (0:ℝ) ≤ (m:ℝ)^4 / n := by positivity
    have hL1r : (1:ℝ) ≤ L n := by exact_mod_cast hL1
    have hpow : (2:ℝ) ^ (L n + 1) = 2 * T := by rw [pow_succ]; ring
    calc 2 * Real.pi * (∑ j ∈ Finset.range (L n), (2:ℝ) ^ (j + 1)) * |x - y|
        ≤ 2 * Real.pi * (2 * T) * ((m:ℝ)^4 / n) := by
          apply mul_le_mul _ hxy' (abs_nonneg _) (by positivity)
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          rw [← hpow]; exact hsum
      _ ≤ 4 * Real.pi * T * ((m:ℝ) ^ 4 / n) * L n := by
          have : 0 ≤ 4 * Real.pi * T * ((m:ℝ) ^ 4 / n) := by positivity
          nlinarith
  have hfin : 4 * Real.pi * T * ((m:ℝ) ^ 4 / n) ≤ 1 / 6 := by
    have hpi := Real.pi_lt_d2
    have hA : (76 * (m:ℝ)^4) * (76 * (m:ℝ)^4) ≤ n := by nlinarith [h3r, pow_nonneg (Nat.cast_nonneg m : (0:ℝ) ≤ m) 8]
    have hAT : (76 * (m:ℝ)^4) * T ≤ n := by
      have hA0 : (0:ℝ) ≤ 76 * (m:ℝ)^4 := by positivity
      by_contra hc
      push_neg at hc
      have : (n:ℝ) * n < (76 * (m:ℝ)^4 * T) * (76 * (m:ℝ)^4 * T) := mul_self_lt_mul_self hnpos.le hc
      have h5 : (76 * (m:ℝ)^4 * T) * (76 * (m:ℝ)^4 * T) = ((76 * (m:ℝ)^4) * (76 * (m:ℝ)^4)) * (T * T) := by ring
      have h6 : ((76 * (m:ℝ)^4) * (76 * (m:ℝ)^4)) * (T * T) ≤ (n:ℝ) * n :=
        mul_le_mul hA hTr (by positivity) hnpos.le
      linarith
    rw [← mul_div_assoc, div_le_iff₀ hnpos]
    have : 4 * Real.pi * T * (m:ℝ)^4 ≤ 4 * 3.15 * T * (m:ℝ)^4 := by
      have : (0:ℝ) ≤ T * (m:ℝ)^4 := by positivity
      nlinarith
    nlinarith
  have habs := abs_le.mp (hd.trans hfin)
  linarith [habs.1, habs.2]
