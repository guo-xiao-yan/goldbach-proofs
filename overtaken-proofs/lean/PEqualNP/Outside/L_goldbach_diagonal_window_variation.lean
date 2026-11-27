import Mathlib.NumberTheory.LSeries.WeakPNT

private lemma dwv_lip (φ : ℝ → ℝ) (h : ContDiff ℝ 1 φ) :
    ∃ M B : ℝ, 0 ≤ M ∧ 0 ≤ B ∧ (∀ x ∈ Set.Icc (0:ℝ) 1, |φ x| ≤ M) ∧
      ∀ x ∈ Set.Icc (0:ℝ) 1, ∀ y ∈ Set.Icc (0:ℝ) 1, |φ y ^ 2 - φ x ^ 2| ≤ B * |y - x| := by
  have hc : Continuous φ := h.continuous
  have hdc : Continuous (deriv φ) := h.continuous_deriv le_rfl
  have hd : Differentiable ℝ φ := h.differentiable one_ne_zero
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn (f := φ) (s := Set.Icc (0:ℝ) 1) hc.continuousOn
  obtain ⟨M', hM'⟩ := isCompact_Icc.exists_bound_of_continuousOn (f := deriv φ) (s := Set.Icc (0:ℝ) 1) hdc.continuousOn
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM 0 (by simp))
  have hM'0 : 0 ≤ M' := le_trans (norm_nonneg _) (hM' 0 (by simp))
  have hder : ∀ x, HasDerivAt (fun u => φ u ^ 2) (2 * φ x * deriv φ x) x := by
    intro x
    have := ((hd x).hasDerivAt).mul ((hd x).hasDerivAt)
    have e : (fun u => φ u ^ 2) = fun u => φ u * φ u := by funext u; ring
    rw [e]
    convert this using 1; ring
  refine ⟨M, 2 * M * M', hM0, by positivity, fun x hx => by simpa using hM x hx, ?_⟩
  intro x hx y hy
  have := Convex.norm_image_sub_le_of_norm_deriv_le (f := fun u => φ u ^ 2) (s := Set.Icc (0:ℝ) 1)
    (C := 2 * M * M') (fun x _ => (hder x).differentiableAt)
    (fun x hx => by
      rw [(hder x).deriv, Real.norm_eq_abs, abs_mul, abs_mul]
      have h1 := hM x hx
      have h2 := hM' x hx
      simp only [Real.norm_eq_abs] at h1 h2
      have : |(2:ℝ)| = 2 := by norm_num
      rw [this]
      calc 2 * |φ x| * |deriv φ x| ≤ 2 * M * M' := by gcongr)
    (convex_Icc 0 1) hx hy
  simpa using this

private lemma dwv_term (φ : ℝ → ℝ) (M B : ℝ) (hM0 : 0 ≤ M) (hB : 0 ≤ B)
    (hφ : ∀ x ∈ Set.Icc (0:ℝ) 1, |φ x| ≤ M)
    (hL : ∀ x ∈ Set.Icc (0:ℝ) 1, ∀ y ∈ Set.Icc (0:ℝ) 1, |φ y ^ 2 - φ x ^ 2| ≤ B * |y - x|)
    (n k : ℕ) (hk : k < n) :
    |Real.log (((k+1 : ℕ) : ℝ)) * (φ (((k+1 : ℕ) : ℝ) / n)) ^ 2
        - Real.log (k : ℝ) * (φ ((k : ℝ) / n)) ^ 2|
      ≤ (Real.log ((k:ℝ) + 1) - Real.log (k:ℝ)) * M ^ 2 + Real.log n * (B / n) := by
  have hn : (0:ℝ) < n := by exact_mod_cast (lt_of_le_of_lt (Nat.zero_le k) hk)
  have hkn : (k:ℝ) + 1 ≤ n := by exact_mod_cast hk
  have hk0 : (0:ℝ) ≤ k := Nat.cast_nonneg k
  push_cast
  have hmem1 : ((k:ℝ) + 1) / n ∈ Set.Icc (0:ℝ) 1 :=
    ⟨by positivity, (div_le_one hn).2 hkn⟩
  have hmem0 : (k:ℝ) / n ∈ Set.Icc (0:ℝ) 1 :=
    ⟨by positivity, (div_le_one hn).2 (by linarith)⟩
  have hlip := hL _ hmem0 _ hmem1
  have hdiff : ((k:ℝ) + 1) / n - (k:ℝ) / n = 1 / n := by field_simp; ring
  have habs : |1 / (n:ℝ)| = 1 / n := abs_of_pos (by positivity)
  rw [hdiff, habs] at hlip
  have hψ : φ (((k:ℝ) + 1) / n) ^ 2 ≤ M ^ 2 := by
    have := hφ _ hmem1
    calc φ (((k:ℝ) + 1) / n) ^ 2 = |φ (((k:ℝ) + 1) / n)| ^ 2 := (sq_abs _).symm
      _ ≤ M ^ 2 := by gcongr
  have hψ0 : 0 ≤ φ (((k:ℝ) + 1) / n) ^ 2 := sq_nonneg _
  have hlogk : 0 ≤ Real.log (k:ℝ) := by
    rcases Nat.eq_zero_or_pos k with h | h
    · subst h; simp
    · exact Real.log_nonneg (by exact_mod_cast h)
  have hlogkn : Real.log (k:ℝ) ≤ Real.log n := by
    rcases Nat.eq_zero_or_pos k with h | h
    · subst h
      rw [Nat.cast_zero, Real.log_zero]
      exact Real.log_nonneg (by exact_mod_cast hk)
    · exact Real.log_le_log (by exact_mod_cast h) (by linarith)
  have hmono : 0 ≤ Real.log ((k:ℝ) + 1) - Real.log (k:ℝ) := by
    rcases Nat.eq_zero_or_pos k with h | h
    · subst h; simp
    · have := Real.log_le_log (by exact_mod_cast h : (0:ℝ) < k) (by linarith : (k:ℝ) ≤ k + 1)
      linarith
  have key : Real.log ((k:ℝ) + 1) * φ (((k:ℝ) + 1) / n) ^ 2 - Real.log (k:ℝ) * φ ((k:ℝ) / n) ^ 2
      = (Real.log ((k:ℝ) + 1) - Real.log (k:ℝ)) * φ (((k:ℝ) + 1) / n) ^ 2
        + Real.log (k:ℝ) * (φ (((k:ℝ) + 1) / n) ^ 2 - φ ((k:ℝ) / n) ^ 2) := by ring
  rw [key]
  have hl2 : |φ (((k:ℝ) + 1) / n) ^ 2 - φ ((k:ℝ) / n) ^ 2| ≤ B / n := by
    calc _ ≤ B * (1 / n) := hlip
      _ = B / n := by ring
  calc _ ≤ |(Real.log ((k:ℝ) + 1) - Real.log (k:ℝ)) * φ (((k:ℝ) + 1) / n) ^ 2|
        + |Real.log (k:ℝ) * (φ (((k:ℝ) + 1) / n) ^ 2 - φ ((k:ℝ) / n) ^ 2)| := abs_add_le _ _
    _ ≤ _ := by
      rw [abs_mul, abs_mul, abs_of_nonneg hmono, abs_of_nonneg hlogk]
      have a1 : (Real.log ((k:ℝ) + 1) - Real.log (k:ℝ)) * |φ (((k:ℝ) + 1) / n) ^ 2|
          ≤ (Real.log ((k:ℝ) + 1) - Real.log (k:ℝ)) * M ^ 2 := by
        rw [abs_of_nonneg hψ0]; exact mul_le_mul_of_nonneg_left hψ hmono
      have a2 : Real.log (k:ℝ) * |φ (((k:ℝ) + 1) / n) ^ 2 - φ ((k:ℝ) / n) ^ 2|
          ≤ Real.log n * (B / n) :=
        mul_le_mul hlogkn hl2 (abs_nonneg _) (hlogk.trans hlogkn)
      linarith

theorem PEqualNP.Outside.L_goldbach_diagonal_window_variation :
    let g := fun (φ : ℝ → ℝ) (n k : ℕ) => Real.log (k:ℝ)*(φ ((k:ℝ)/n))^2; ∀ φ : ℝ → ℝ, ContDiff ℝ 1 φ → (∀ u : ℝ, u < 1/3 ∨ 2/3 < u → φ u=0) → ∃ K : ℝ, 0<K ∧ ∀ n : ℕ, 2≤n → (∑ k ∈ Finset.range n, |g φ n (k+1)-g φ n k|) ≤ K*Real.log (2*(n:ℝ)) := by
  intro g φ hφ _
  obtain ⟨M, B, hM0, hB, hφM, hL⟩ := dwv_lip φ hφ
  refine ⟨M ^ 2 + B + 1, by positivity, ?_⟩
  intro n hn
  have hn0 : (0:ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hterm : ∀ k ∈ Finset.range n, |g φ n (k+1) - g φ n k|
      ≤ (Real.log ((k:ℝ) + 1) - Real.log (k:ℝ)) * M ^ 2 + Real.log n * (B / n) := by
    intro k hk
    exact dwv_term φ M B hM0 hB hφM hL n k (Finset.mem_range.1 hk)
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [Finset.sum_add_distrib, ← Finset.sum_mul]
  have htel : ∑ k ∈ Finset.range n, (Real.log ((k:ℝ) + 1) - Real.log (k:ℝ)) = Real.log n := by
    have := Finset.sum_range_sub (fun k : ℕ => Real.log (k:ℝ)) n
    simpa using this
  rw [htel, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have e : (n:ℝ) * (Real.log n * (B / n)) = B * Real.log n := by field_simp
  rw [e]
  have h1 : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n))
  have h2 : Real.log n ≤ Real.log (2 * n) :=
    Real.log_le_log hn0 (by linarith)
  have hs : 0 ≤ M ^ 2 + B := by positivity
  nlinarith [mul_le_mul_of_nonneg_left h2 hs]
