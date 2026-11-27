import Mathlib.NumberTheory.LSeries.WeakPNT

private theorem gbdr_reindex (F : ℕ → ℝ) (n : ℕ) :
    ∑ k ∈ Finset.Icc 1 n, F k = ∑ k ∈ Finset.range n, F (k + 1) := by
  induction n with
  | zero => simp
  | succ m ih => rw [Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_range_succ]

private theorem gbdr_term (h : ℝ → ℝ) (hc : Continuous h) (Lc : ℝ)
    (hL : ∀ x ∈ Set.Icc (0:ℝ) 1, ∀ y ∈ Set.Icc (0:ℝ) 1, |h x - h y| ≤ Lc * |x - y|)
    (n : ℕ) (hn' : (0:ℝ) < n) (k : ℕ) (hk : k < n) :
    |h (((k + 1 : ℕ) : ℝ) / n) / n - ∫ u in ((k:ℝ) / n)..(((k + 1 : ℕ) : ℝ) / n), h u|
      ≤ Lc / (n:ℝ)^2 := by
  have hkn : (k:ℝ) + 1 ≤ n := by exact_mod_cast hk
  have hk0 : (0:ℝ) ≤ k := Nat.cast_nonneg k
  have hab : (k:ℝ) / n ≤ ((k + 1 : ℕ) : ℝ) / n := by
    push_cast
    exact div_le_div_of_nonneg_right (by linarith) hn'.le
  have e : h (((k + 1 : ℕ) : ℝ) / n) / n - ∫ u in ((k:ℝ) / n)..(((k + 1 : ℕ) : ℝ) / n), h u
      = ∫ u in ((k:ℝ) / n)..(((k + 1 : ℕ) : ℝ) / n), (h (((k + 1 : ℕ) : ℝ) / n) - h u) := by
    rw [intervalIntegral.integral_sub intervalIntegrable_const (hc.intervalIntegrable _ _),
      intervalIntegral.integral_const]
    push_cast
    simp only [smul_eq_mul]
    field_simp
    ring
  rw [e]
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (k:ℝ) / n) (b := ((k + 1 : ℕ) : ℝ) / n)
    (f := fun u => h (((k + 1 : ℕ) : ℝ) / n) - h u) (C := Lc / n) (by
      intro u hu
      rw [Set.uIoc_of_le hab] at hu
      obtain ⟨hu1, hu2⟩ := hu
      have hu0 : 0 ≤ u := le_trans (div_nonneg hk0 hn'.le) hu1.le
      have hb1 : ((k + 1 : ℕ) : ℝ) / n ≤ 1 := by
        rw [div_le_one hn']; push_cast; exact hkn
      have h1 := hL _ ⟨by positivity, hb1⟩ u ⟨hu0, le_trans hu2 hb1⟩
      have h2 : |((k + 1 : ℕ) : ℝ) / n - u| ≤ 1 / n := by
        rw [abs_of_nonneg (by linarith)]
        have : ((k + 1 : ℕ) : ℝ) / n - (k:ℝ) / n = 1 / n := by
          push_cast; field_simp; ring
        linarith
      have hLc : 0 ≤ Lc := by
        have := hL 0 ⟨le_refl _, zero_le_one⟩ 1 ⟨zero_le_one, le_refl _⟩
        have h3 : 0 ≤ |h 0 - h 1| := abs_nonneg _
        norm_num at this
        linarith
      rw [Real.norm_eq_abs]
      calc _ ≤ Lc * |((k + 1 : ℕ) : ℝ) / n - u| := h1
        _ ≤ Lc * (1 / n) := mul_le_mul_of_nonneg_left h2 hLc
        _ = Lc / n := by ring)
  rw [Real.norm_eq_abs] at hb
  have : |((k + 1 : ℕ) : ℝ) / n - (k:ℝ) / n| = 1 / n := by
    rw [abs_of_nonneg (by linarith)]
    push_cast; field_simp; ring
  rw [this] at hb
  calc _ ≤ _ := hb
    _ = Lc / (n:ℝ)^2 := by field_simp

private theorem gbdr_riemann (h : ℝ → ℝ) (hc : Continuous h) (Lc : ℝ)
    (hL : ∀ x ∈ Set.Icc (0:ℝ) 1, ∀ y ∈ Set.Icc (0:ℝ) 1, |h x - h y| ≤ Lc * |x - y|)
    (n : ℕ) (hn : 1 ≤ n) :
    |(∑ k ∈ Finset.Icc 1 n, h ((k:ℝ) / n)) / n - ∫ u in (0:ℝ)..1, h u| ≤ Lc / n := by
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  have h1 : ∫ u in (0:ℝ)..1, h u
      = ∑ k ∈ Finset.range n, ∫ u in ((k:ℝ) / n)..(((k + 1 : ℕ) : ℝ) / n), h u := by
    have := intervalIntegral.sum_integral_adjacent_intervals (f := h)
      (μ := MeasureTheory.volume) (a := fun k : ℕ => (k:ℝ) / n) (n := n)
      (fun k _ => hc.intervalIntegrable _ _)
    simp only [Nat.cast_zero, zero_div, div_self hn'.ne'] at this
    exact this.symm
  rw [gbdr_reindex (fun k => h ((k:ℝ) / n)), Finset.sum_div, h1, ← Finset.sum_sub_distrib]
  calc _ ≤ ∑ k ∈ Finset.range n, |h (((k + 1 : ℕ) : ℝ) / n) / n
          - ∫ u in ((k:ℝ) / n)..(((k + 1 : ℕ) : ℝ) / n), h u| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ Finset.range n, Lc / (n:ℝ)^2 :=
        Finset.sum_le_sum (fun k hk => gbdr_term h hc Lc hL n hn' k (Finset.mem_range.mp hk))
    _ = Lc / n := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        field_simp

private theorem gbdr_phi (φ : ℝ → ℝ) (hφ : ContDiff ℝ 1 φ) :
    ∃ M L : ℝ, 0 ≤ M ∧ 0 ≤ L ∧ (∀ x ∈ Set.Icc (0:ℝ) 1, |φ x| ≤ M) ∧
      ∀ x ∈ Set.Icc (0:ℝ) 1, ∀ y ∈ Set.Icc (0:ℝ) 1, |φ x - φ y| ≤ L * |x - y| := by
  have hd : Continuous (deriv φ) := hφ.continuous_deriv le_rfl
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn (f := φ) (s := Set.Icc (0:ℝ) 1)
    hφ.continuous.continuousOn
  obtain ⟨L, hLb⟩ := isCompact_Icc.exists_bound_of_continuousOn (f := deriv φ)
    (s := Set.Icc (0:ℝ) 1) hd.continuousOn
  refine ⟨max M 0, max L 0, le_max_right _ _, le_max_right _ _, ?_, ?_⟩
  · intro x hx
    have := hM x hx
    rw [Real.norm_eq_abs] at this
    exact this.trans (le_max_left _ _)
  · intro x hx y hy
    have := Convex.norm_image_sub_le_of_norm_deriv_le (f := φ) (C := max L 0) (s := Set.Icc (0:ℝ) 1)
      (fun z _ => (hφ.differentiable one_ne_zero) z)
      (fun z hz => (hLb z hz).trans (le_max_left _ _)) (convex_Icc 0 1) hy hx
    simpa [Real.norm_eq_abs] using this

private theorem gbdr_logmax_lip (a b : ℝ) :
    |Real.log (max a (1/3)) - Real.log (max b (1/3))| ≤ 3 * |a - b| := by
  have key : ∀ a' b' : ℝ, 1/3 ≤ a' → a' ≤ b' → Real.log b' - Real.log a' ≤ 3 * (b' - a') := by
    intro a' b' ha hab
    have ha0 : 0 < a' := by linarith
    have hb0 : 0 < b' := by linarith
    have h1 := Real.log_le_sub_one_of_pos (div_pos hb0 ha0)
    rw [Real.log_div hb0.ne' ha0.ne'] at h1
    have h2 : b' / a' - 1 ≤ 3 * (b' - a') := by
      rw [div_sub_one ha0.ne', div_le_iff₀ ha0]
      nlinarith
    linarith
  have hm : |max a (1/3) - max b (1/3)| ≤ |a - b| := abs_max_sub_max_le_abs a b (1/3)
  have ha : 1/3 ≤ max a (1/3) := le_max_right _ _
  have hb : 1/3 ≤ max b (1/3) := le_max_right _ _
  rcases le_total (max a (1/3)) (max b (1/3)) with h | h
  · have := key _ _ ha h
    rw [abs_sub_comm, abs_of_nonneg (by
      have := Real.log_le_log (by linarith) h; linarith)]
    rw [abs_sub_comm] at hm
    rw [abs_of_nonneg (by linarith)] at hm
    nlinarith [abs_nonneg (a - b), le_abs_self (b - a), abs_sub_comm a b]
  · have := key _ _ hb h
    rw [abs_of_nonneg (by
      have := Real.log_le_log (by linarith) h; linarith)]
    rw [abs_of_nonneg (by linarith)] at hm
    nlinarith [abs_nonneg (a - b)]

private theorem gbdr_ell_bound (x : ℝ) (hx : x ∈ Set.Icc (0:ℝ) 1) :
    |Real.log (max x (1/3))| ≤ Real.log 3 := by
  obtain ⟨_, hx1⟩ := hx
  have h1 : (1:ℝ)/3 ≤ max x (1/3) := le_max_right _ _
  have h2 : max x (1/3) ≤ 1 := max_le hx1 (by norm_num)
  have h3 : Real.log (max x (1/3)) ≤ 0 := Real.log_nonpos (by linarith) h2
  have h4 : Real.log (1/3) ≤ Real.log (max x (1/3)) := Real.log_le_log (by norm_num) h1
  have h5 : Real.log (1/3 : ℝ) = - Real.log 3 := by
    rw [one_div, Real.log_inv]
  rw [abs_le]
  constructor <;> linarith

theorem PEqualNP.Outside.L_goldbach_diagonal_riemann_constant :
    let g := fun (φ : ℝ → ℝ) (n k : ℕ) => Real.log (k:ℝ)*(φ ((k:ℝ)/n))^2; let c := fun φ : ℝ → ℝ => intervalIntegral (fun u : ℝ => (φ u)^2) 0 1 MeasureTheory.volume; let b := fun φ : ℝ → ℝ => intervalIntegral (fun u : ℝ => (φ u)^2*Real.log u) 0 1 MeasureTheory.volume; ∀ φ : ℝ → ℝ, ContDiff ℝ 1 φ → (∀ u : ℝ, u < 1/3 ∨ 2/3 < u → φ u=0) → ∃ K : ℝ, 0<K ∧ ∀ n : ℕ, 2≤n → |(∑ k ∈ Finset.Icc 1 n, g φ n k)/(n:ℝ) - (c φ*Real.log (n:ℝ)+b φ)| ≤ K*Real.log (2*(n:ℝ))/(n:ℝ) := by
  intro g c b φ hφ hz
  obtain ⟨M, L, hM0, hL0, hM, hLip⟩ := gbdr_phi φ hφ
  have hg : ∀ n k : ℕ, g φ n k = Real.log (k:ℝ) * (φ ((k:ℝ)/n))^2 := fun _ _ => rfl
  have hc : c φ = ∫ u in (0:ℝ)..1, (φ u)^2 := rfl
  have hb : b φ = ∫ u in (0:ℝ)..1, (φ u)^2 * Real.log u := rfl
  have hfeq : ∀ u : ℝ, (φ u)^2 * Real.log u = (φ u)^2 * Real.log (max u (1/3)) := by
    intro u
    by_cases hu : 1/3 ≤ u
    · rw [max_eq_left hu]
    · have : φ u = 0 := hz u (Or.inl (not_le.mp hu))
      simp [this]
  have hb2 : b φ = ∫ u in (0:ℝ)..1, (φ u)^2 * Real.log (max u (1/3)) := by
    rw [hb]
    have : (fun u : ℝ => (φ u)^2 * Real.log u) = fun u => (φ u)^2 * Real.log (max u (1/3)) :=
      funext hfeq
    rw [this]
  set B : ℝ := 2 * M * L with hBdef
  have hB0 : 0 ≤ B := by positivity
  have hlog3 : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  set C2 : ℝ := B * Real.log 3 + 3 * M^2 with hC2def
  have hC20 : 0 ≤ C2 := by positivity
  have hpsi_lip : ∀ x ∈ Set.Icc (0:ℝ) 1, ∀ y ∈ Set.Icc (0:ℝ) 1,
      |(φ x)^2 - (φ y)^2| ≤ B * |x - y| := by
    intro x hx y hy
    have e : (φ x)^2 - (φ y)^2 = (φ x + φ y) * (φ x - φ y) := by ring
    rw [e, abs_mul]
    have h1 : |φ x + φ y| ≤ 2 * M := by
      calc _ ≤ |φ x| + |φ y| := abs_add_le _ _
        _ ≤ M + M := add_le_add (hM x hx) (hM y hy)
        _ = 2 * M := by ring
    have h2 := hLip x hx y hy
    calc _ ≤ (2 * M) * (L * |x - y|) :=
          mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
      _ = B * |x - y| := by rw [hBdef]; ring
  have hell_cont : Continuous (fun u : ℝ => Real.log (max u (1/3))) :=
    Continuous.log (continuous_id.max continuous_const)
      (fun x => ne_of_gt (lt_of_lt_of_le (by norm_num) (le_max_right _ _)))
  have hh2_cont : Continuous (fun u : ℝ => (φ u)^2 * Real.log (max u (1/3))) :=
    (hφ.continuous.pow 2).mul hell_cont
  have hh2_lip : ∀ x ∈ Set.Icc (0:ℝ) 1, ∀ y ∈ Set.Icc (0:ℝ) 1,
      |(φ x)^2 * Real.log (max x (1/3)) - (φ y)^2 * Real.log (max y (1/3))| ≤ C2 * |x - y| := by
    intro x hx y hy
    have e : (φ x)^2 * Real.log (max x (1/3)) - (φ y)^2 * Real.log (max y (1/3))
        = ((φ x)^2 - (φ y)^2) * Real.log (max x (1/3))
          + (φ y)^2 * (Real.log (max x (1/3)) - Real.log (max y (1/3))) := by ring
    rw [e]
    have t1 : |((φ x)^2 - (φ y)^2) * Real.log (max x (1/3))| ≤ (B * |x - y|) * Real.log 3 := by
      rw [abs_mul]
      exact mul_le_mul (hpsi_lip x hx y hy) (gbdr_ell_bound x hx) (abs_nonneg _)
        (by positivity)
    have t2 : |(φ y)^2 * (Real.log (max x (1/3)) - Real.log (max y (1/3)))|
        ≤ M^2 * (3 * |x - y|) := by
      rw [abs_mul]
      have hy2 : |(φ y)^2| ≤ M^2 := by
        rw [abs_pow]
        exact pow_le_pow_left₀ (abs_nonneg _) (hM y hy) 2
      exact mul_le_mul hy2 (gbdr_logmax_lip x y) (abs_nonneg _) (by positivity)
    calc _ ≤ _ := abs_add_le _ _
      _ ≤ (B * |x - y|) * Real.log 3 + M^2 * (3 * |x - y|) := add_le_add t1 t2
      _ = C2 * |x - y| := by rw [hC2def]; ring
  have hpsi_cont : Continuous (fun u : ℝ => (φ u)^2) := hφ.continuous.pow 2
  refine ⟨B + C2 + 1, by positivity, ?_⟩
  intro n hn
  have hn1 : 1 ≤ n := by omega
  have hn' : (0:ℝ) < n := by exact_mod_cast hn1
  have hn2 : (2:ℝ) ≤ n := by exact_mod_cast hn
  have R1 := gbdr_riemann (fun u : ℝ => (φ u)^2) hpsi_cont B hpsi_lip n hn1
  have R2 := gbdr_riemann (fun u : ℝ => (φ u)^2 * Real.log (max u (1/3))) hh2_cont C2 hh2_lip n hn1
  have hsum : ∑ k ∈ Finset.Icc 1 n, g φ n k
      = Real.log n * ∑ k ∈ Finset.Icc 1 n, (φ ((k:ℝ)/n))^2
        + ∑ k ∈ Finset.Icc 1 n, (φ ((k:ℝ)/n))^2 * Real.log (max ((k:ℝ)/n) (1/3)) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
    have hk0 : (0:ℝ) < k := by exact_mod_cast hk1
    rw [hg, ← hfeq, Real.log_div hk0.ne' hn'.ne']
    ring
  set S1 := ∑ k ∈ Finset.Icc 1 n, (φ ((k:ℝ)/n))^2 with hS1
  set S2 := ∑ k ∈ Finset.Icc 1 n, (φ ((k:ℝ)/n))^2 * Real.log (max ((k:ℝ)/n) (1/3)) with hS2
  rw [hsum, hc, hb2]
  set I1 := ∫ u in (0:ℝ)..1, (φ u)^2 with hI1
  set I2 := ∫ u in (0:ℝ)..1, (φ u)^2 * Real.log (max u (1/3)) with hI2
  have hlogn0 : 0 ≤ Real.log n := Real.log_nonneg (by linarith)
  have hlogle : Real.log n ≤ Real.log (2 * n) :=
    Real.log_le_log hn' (by linarith)
  have hlog1 : 1 ≤ Real.log (2 * n) := by
    have h4 : Real.log 4 ≤ Real.log (2 * n) := Real.log_le_log (by norm_num) (by linarith)
    have h5 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4:ℝ) = 2 * 2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
      ring
    have := Real.log_two_gt_d9
    linarith
  have e : (Real.log n * S1 + S2) / n - (I1 * Real.log n + I2)
      = Real.log n * (S1 / n - I1) + (S2 / n - I2) := by ring
  rw [e]
  have hA : |Real.log n * (S1 / n - I1)| ≤ Real.log n * (B / n) := by
    rw [abs_mul, abs_of_nonneg hlogn0]
    exact mul_le_mul_of_nonneg_left R1 hlogn0
  have hfin : Real.log n * (B / n) + C2 / n ≤ (B + C2 + 1) * Real.log (2 * n) / n := by
    rw [← mul_div_assoc, ← add_div]
    apply div_le_div_of_nonneg_right _ hn'.le
    nlinarith [mul_le_mul_of_nonneg_right hlogle hB0, mul_le_mul_of_nonneg_left hlog1 hC20]
  calc _ ≤ |Real.log n * (S1 / n - I1)| + |S2 / n - I2| := abs_add_le _ _
    _ ≤ Real.log n * (B / n) + C2 / n := add_le_add hA R2
    _ ≤ _ := hfin
