import Mathlib

open MeasureTheory Set

private noncomputable def ee (x : ℝ) : ℂ := Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)

private lemma ee_cont : Continuous ee := by
  unfold ee; fun_prop

private lemma ee_int (m : ℤ) :
    ∫ t in (0 : ℝ)..1, ee ((m : ℝ) * t) = if m = 0 then 1 else 0 := by
  by_cases hm : m = 0
  · subst hm; simp [ee]
  · rw [if_neg hm]
    set c : ℂ := ((2 * Real.pi * (m : ℝ) : ℝ) : ℂ) * Complex.I with hc
    have hc0 : c ≠ 0 := by
      rw [hc]
      refine mul_ne_zero ?_ Complex.I_ne_zero
      have : (2 * Real.pi * (m : ℝ)) ≠ 0 := by
        have : (m : ℝ) ≠ 0 := by exact_mod_cast hm
        positivity
      exact_mod_cast this
    have e1 : ∀ t : ℝ, ee ((m : ℝ) * t) = Complex.exp (c * (t : ℂ)) := by
      intro t; unfold ee; rw [hc]; congr 1; push_cast; ring
    simp_rw [e1]
    rw [integral_exp_mul_complex hc0]
    have : Complex.exp (c * ((1 : ℝ) : ℂ)) = 1 := by
      rw [hc]
      have := Complex.exp_int_mul_two_pi_mul_I m
      rw [← this]; congr 1; push_cast; ring
    rw [this]; simp

private lemma ee_mul_conj (x y : ℝ) :
    ee x * (starRingEnd ℂ) (ee y) = ee (x - y) := by
  unfold ee
  rw [← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast; ring

private lemma parseval (N : ℕ) (c : ℕ → ℂ) :
    ∫ t in (0 : ℝ)..1, ‖∑ k ∈ Finset.range N, c k * ee ((k : ℝ) * t)‖ ^ 2
      = ∑ k ∈ Finset.range N, ‖c k‖ ^ 2 := by
  have h1 : ∀ t : ℝ, (((‖∑ k ∈ Finset.range N, c k * ee ((k : ℝ) * t)‖ ^ 2 : ℝ)) : ℂ)
      = ∑ k ∈ Finset.range N, ∑ l ∈ Finset.range N,
          c k * (starRingEnd ℂ) (c l) * ee (((k : ℤ) - (l : ℤ) : ℤ) * t) := by
    intro t
    set z := ∑ k ∈ Finset.range N, c k * ee ((k : ℝ) * t) with hz
    have : (((‖z‖ ^ 2 : ℝ)) : ℂ) = z * (starRingEnd ℂ) z := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    rw [this, hz, map_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro l _
    rw [map_mul]
    have := ee_mul_conj ((k : ℝ) * t) ((l : ℝ) * t)
    have e2 : (((k : ℤ) - (l : ℤ) : ℤ) : ℝ) * t = (k : ℝ) * t - (l : ℝ) * t := by
      push_cast; ring
    rw [e2, ← this]; ring
  have h2 : ((∫ t in (0 : ℝ)..1, ‖∑ k ∈ Finset.range N, c k * ee ((k : ℝ) * t)‖ ^ 2 : ℝ) : ℂ)
      = ((∑ k ∈ Finset.range N, ‖c k‖ ^ 2 : ℝ) : ℂ) := by
    rw [← intervalIntegral.integral_ofReal]
    simp_rw [h1]
    rw [intervalIntegral.integral_finsetSum]
    · have : ∀ k ∈ Finset.range N, ∫ t in (0 : ℝ)..1, ∑ l ∈ Finset.range N,
          c k * (starRingEnd ℂ) (c l) * ee (((k : ℤ) - (l : ℤ) : ℤ) * t)
          = ((‖c k‖ ^ 2 : ℝ) : ℂ) := by
        intro k hk
        rw [intervalIntegral.integral_finsetSum]
        · have : ∀ l ∈ Finset.range N, ∫ t in (0 : ℝ)..1,
              c k * (starRingEnd ℂ) (c l) * ee (((k : ℤ) - (l : ℤ) : ℤ) * t)
              = if l = k then ((‖c k‖ ^ 2 : ℝ) : ℂ) else 0 := by
            intro l hl
            rw [intervalIntegral.integral_const_mul, ee_int]
            by_cases hlk : l = k
            · subst hlk
              simp [Complex.mul_conj, Complex.normSq_eq_norm_sq]
            · have : ((k : ℤ) - (l : ℤ)) ≠ 0 := by
                intro h; apply hlk; omega
              simp [this, hlk]
          rw [Finset.sum_congr rfl this]
          simp [hk]
        · intro l _
          apply Continuous.intervalIntegrable
          have := ee_cont
          fun_prop
      rw [Finset.sum_congr rfl this]
      push_cast; rfl
    · intro k _
      apply Continuous.intervalIntegrable
      have := ee_cont
      fun_prop
  exact_mod_cast h2

private lemma ee_deriv (k t : ℝ) :
    HasDerivAt (fun t : ℝ => ee (k * t)) (((2 * Real.pi * k : ℝ) : ℂ) * Complex.I * ee (k * t)) t := by
  have h1 : HasDerivAt (fun x : ℝ => (x : ℂ)) 1 t := (hasDerivAt_id t).ofReal_comp
  have h2 := (h1.const_mul (((2 * Real.pi * k : ℝ) : ℂ) * Complex.I)).cexp
  have e : (fun t : ℝ => ee (k * t))
      = fun x : ℝ => Complex.exp ((((2 * Real.pi * k : ℝ) : ℂ) * Complex.I) * (x : ℂ)) := by
    funext x; unfold ee; congr 1; push_cast; ring
  rw [e]
  convert h2 using 1
  unfold ee; rw [mul_one]; push_cast; ring_nf

private lemma gall (S D : ℝ → ℂ) (hS : ∀ t, HasDerivAt S (D t) t) (hD : Continuous D)
    (a b : ℝ) (hab : a < b) (t0 : ℝ) (h0 : t0 ∈ Icc a b) :
    ‖S t0‖ ^ 2 ≤ (b - a)⁻¹ * (∫ t in a..b, ‖S t‖ ^ 2)
      + ∫ t in a..b, 2 * ‖S t‖ * ‖D t‖ := by
  have hSc : Continuous S := continuous_iff_continuousAt.2 (fun t => (hS t).continuousAt)
  have hf : ∀ t, HasDerivAt (fun t => ‖S t‖ ^ 2) (2 * inner ℝ (S t) (D t)) t :=
    fun t => (hS t).norm_sq
  have hfc : Continuous fun t => 2 * inner ℝ (S t) (D t) := by fun_prop
  have hgc : Continuous fun t => 2 * ‖S t‖ * ‖D t‖ := by fun_prop
  set J := ∫ t in a..b, 2 * ‖S t‖ * ‖D t‖ with hJ
  have hg0 : ∀ t, 0 ≤ 2 * ‖S t‖ * ‖D t‖ := fun t => by positivity
  have hfg : ∀ t, |2 * inner ℝ (S t) (D t)| ≤ 2 * ‖S t‖ * ‖D t‖ := by
    intro t
    rw [abs_mul, abs_two, mul_assoc]
    have := abs_real_inner_le_norm (S t) (D t)
    linarith
  have step : ∀ s r, s ∈ Icc a b → r ∈ Icc a b → s ≤ r → ‖S r‖ ^ 2 - ‖S s‖ ^ 2 ≤ J := by
    intro s r hs hr hsr
    have e := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := s) (b := r)
      (f := fun t => ‖S t‖ ^ 2) (f' := fun t => 2 * inner ℝ (S t) (D t))
      (fun x _ => hf x) (hfc.intervalIntegrable _ _)
    rw [← e]
    calc ∫ x in s..r, 2 * inner ℝ (S x) (D x)
        ≤ ∫ x in s..r, 2 * ‖S x‖ * ‖D x‖ := by
          apply intervalIntegral.integral_mono_on hsr (hfc.intervalIntegrable _ _)
            (hgc.intervalIntegrable _ _)
          intro x _
          exact (le_abs_self _).trans (hfg x)
      _ ≤ J := intervalIntegral.integral_mono_interval hs.1 hsr hr.2
          (Filter.Eventually.of_forall hg0) (hgc.intervalIntegrable _ _)
  have step2 : ∀ s r, s ∈ Icc a b → r ∈ Icc a b → s ≤ r → ‖S s‖ ^ 2 - ‖S r‖ ^ 2 ≤ J := by
    intro s r hs hr hsr
    have e := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := s) (b := r)
      (f := fun t => ‖S t‖ ^ 2) (f' := fun t => 2 * inner ℝ (S t) (D t))
      (fun x _ => hf x) (hfc.intervalIntegrable _ _)
    have : ‖S s‖ ^ 2 - ‖S r‖ ^ 2 = ∫ x in s..r, -(2 * inner ℝ (S x) (D x)) := by
      rw [intervalIntegral.integral_neg, e]; ring
    rw [this]
    calc ∫ x in s..r, -(2 * inner ℝ (S x) (D x))
        ≤ ∫ x in s..r, 2 * ‖S x‖ * ‖D x‖ := by
          apply intervalIntegral.integral_mono_on hsr (hfc.neg.intervalIntegrable _ _)
            (hgc.intervalIntegrable _ _)
          intro x _
          exact (neg_le_abs _).trans (hfg x)
      _ ≤ J := intervalIntegral.integral_mono_interval hs.1 hsr hr.2
          (Filter.Eventually.of_forall hg0) (hgc.intervalIntegrable _ _)
  have pt : ∀ t ∈ Icc a b, ‖S t0‖ ^ 2 ≤ ‖S t‖ ^ 2 + J := by
    intro t ht
    rcases le_total t t0 with h | h
    · linarith [step t t0 ht h0 h]
    · linarith [step2 t0 t h0 ht h]
  have hI : (∫ t in a..b, ‖S t0‖ ^ 2) ≤ ∫ t in a..b, (‖S t‖ ^ 2 + J) := by
    apply intervalIntegral.integral_mono_on hab.le (by simp)
    · exact (by fun_prop : Continuous fun t => ‖S t‖ ^ 2 + J).intervalIntegrable _ _
    · intro t ht; exact pt t ht
  rw [intervalIntegral.integral_add ((by fun_prop : Continuous fun t => ‖S t‖ ^ 2).intervalIntegrable _ _)
    (by simp)] at hI
  simp only [intervalIntegral.integral_const, smul_eq_mul] at hI
  have hba : 0 < b - a := by linarith
  rw [← sub_nonneg] at hI ⊢
  have : (b - a)⁻¹ * (∫ t in a..b, ‖S t‖ ^ 2) + J - ‖S t0‖ ^ 2
      = (b - a)⁻¹ * ((∫ t in a..b, ‖S t‖ ^ 2) + (b - a) * J - (b - a) * ‖S t0‖ ^ 2) := by
    field_simp
  rw [this]
  apply mul_nonneg (by positivity)
  linarith

private noncomputable def Sf (n : ℕ) (u : ℕ → ℝ) (t : ℝ) : ℂ :=
  ∑ k ∈ Finset.range (n + 1), (u k : ℂ) * ee ((k : ℝ) * t)

private noncomputable def Df (n : ℕ) (u : ℕ → ℝ) (t : ℝ) : ℂ :=
  ∑ k ∈ Finset.range (n + 1), ((u k : ℂ) * ((2 * Real.pi * (k : ℝ) : ℝ) : ℂ) * Complex.I)
    * ee ((k : ℝ) * t)

private lemma Sf_deriv (n : ℕ) (u : ℕ → ℝ) (t : ℝ) : HasDerivAt (Sf n u) (Df n u t) t := by
  unfold Sf Df
  have := HasDerivAt.fun_sum (u := Finset.range (n + 1)) (x := t)
    (A := fun k t => (u k : ℂ) * ee ((k : ℝ) * t))
    (A' := fun k => ((u k : ℂ) * ((2 * Real.pi * (k : ℝ) : ℝ) : ℂ) * Complex.I) * ee ((k : ℝ) * t))
    (fun k _ => by
      have := (ee_deriv (k : ℝ) t).const_mul (u k : ℂ)
      convert this using 1; ring)
  exact this

private lemma Df_cont (n : ℕ) (u : ℕ → ℝ) : Continuous (Df n u) := by
  unfold Df
  have := ee_cont
  fun_prop

private lemma Sf_cont (n : ℕ) (u : ℕ → ℝ) : Continuous (Sf n u) := by
  unfold Sf
  have := ee_cont
  fun_prop

private lemma parseval_S (n : ℕ) (u : ℕ → ℝ) :
    ∫ t in (0 : ℝ)..1, ‖Sf n u t‖ ^ 2 = ∑ k ∈ Finset.range (n + 1), (u k) ^ 2 := by
  have := parseval (n + 1) (fun k => (u k : ℂ))
  unfold Sf
  rw [this]
  apply Finset.sum_congr rfl
  intro k _
  simp

private lemma parseval_D (n : ℕ) (u : ℕ → ℝ) :
    ∫ t in (0 : ℝ)..1, ‖Df n u t‖ ^ 2
      ≤ (2 * Real.pi * n) ^ 2 * ∑ k ∈ Finset.range (n + 1), (u k) ^ 2 := by
  have := parseval (n + 1)
    (fun k => ((u k : ℂ) * ((2 * Real.pi * (k : ℝ) : ℝ) : ℂ) * Complex.I))
  unfold Df
  rw [this, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k hk
  have hkn : (k : ℝ) ≤ n := by
    have : k ≤ n := by simpa [Nat.lt_succ_iff] using hk
    exact_mod_cast this
  have e : ‖(u k : ℂ) * ((2 * Real.pi * (k : ℝ) : ℝ) : ℂ) * Complex.I‖ ^ 2
      = (2 * Real.pi * k) ^ 2 * (u k) ^ 2 := by
    rw [norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs, mul_pow, abs_of_nonneg (by positivity : 0 ≤ 2 * Real.pi * (k : ℝ))]
    rw [sq_abs]; ring
  rw [e]
  have : (2 * Real.pi * (k : ℝ)) ^ 2 ≤ (2 * Real.pi * n) ^ 2 := by
    apply pow_le_pow_left₀ (by positivity)
    have := Real.pi_pos
    nlinarith
  exact mul_le_mul_of_nonneg_right this (sq_nonneg _)

private lemma g_bound (n : ℕ) (hn : 0 < n) (u : ℕ → ℝ) :
    ∫ t in (0 : ℝ)..1, 2 * ‖Sf n u t‖ * ‖Df n u t‖
      ≤ 4 * Real.pi * n * ∑ k ∈ Finset.range (n + 1), (u k) ^ 2 := by
  set lam : ℝ := 2 * Real.pi * n with hlam
  have hl : 0 < lam := by
    have : (0 : ℝ) < n := by exact_mod_cast hn
    positivity
  have hSc := Sf_cont n u
  have hDc := Df_cont n u
  have h1 : ∫ t in (0 : ℝ)..1, 2 * ‖Sf n u t‖ * ‖Df n u t‖
      ≤ ∫ t in (0 : ℝ)..1, (lam * ‖Sf n u t‖ ^ 2 + lam⁻¹ * ‖Df n u t‖ ^ 2) := by
    apply intervalIntegral.integral_mono_on zero_le_one
    · exact (by fun_prop : Continuous fun t => 2 * ‖Sf n u t‖ * ‖Df n u t‖).intervalIntegrable _ _
    · exact (by fun_prop : Continuous fun t =>
        lam * ‖Sf n u t‖ ^ 2 + lam⁻¹ * ‖Df n u t‖ ^ 2).intervalIntegrable _ _
    · intro t _
      have : 0 ≤ (Real.sqrt lam * ‖Sf n u t‖ - ‖Df n u t‖ / Real.sqrt lam) ^ 2 := sq_nonneg _
      have hs : 0 < Real.sqrt lam := Real.sqrt_pos.2 hl
      have hss : Real.sqrt lam * Real.sqrt lam = lam := Real.mul_self_sqrt hl.le
      have e : (Real.sqrt lam * ‖Sf n u t‖ - ‖Df n u t‖ / Real.sqrt lam) ^ 2
          = lam * ‖Sf n u t‖ ^ 2 + lam⁻¹ * ‖Df n u t‖ ^ 2 - 2 * ‖Sf n u t‖ * ‖Df n u t‖ := by
        have key : ∀ s x y : ℝ, 0 < s → (s * x - y / s) ^ 2
            = s ^ 2 * x ^ 2 + (s ^ 2)⁻¹ * y ^ 2 - 2 * x * y := by
          intro s x y hs; field_simp; ring
        rw [key _ _ _ hs, Real.sq_sqrt hl.le]
      linarith
  rw [intervalIntegral.integral_add
    ((by fun_prop : Continuous fun t => lam * ‖Sf n u t‖ ^ 2).intervalIntegrable _ _)
    ((by fun_prop : Continuous fun t => lam⁻¹ * ‖Df n u t‖ ^ 2).intervalIntegrable _ _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    parseval_S] at h1
  have h2 := parseval_D n u
  have h3 : lam⁻¹ * ∫ t in (0 : ℝ)..1, ‖Df n u t‖ ^ 2
      ≤ lam⁻¹ * (lam ^ 2 * ∑ k ∈ Finset.range (n + 1), (u k) ^ 2) :=
    mul_le_mul_of_nonneg_left h2 (by positivity)
  have h4 : lam⁻¹ * (lam ^ 2 * ∑ k ∈ Finset.range (n + 1), (u k) ^ 2)
      = lam * ∑ k ∈ Finset.range (n + 1), (u k) ^ 2 := by
    field_simp
  have h5 : 4 * Real.pi * n * ∑ k ∈ Finset.range (n + 1), (u k) ^ 2
      = lam * ∑ k ∈ Finset.range (n + 1), (u k) ^ 2 + lam * ∑ k ∈ Finset.range (n + 1), (u k) ^ 2 := by
    rw [hlam]; ring
  linarith

private lemma wsq_le (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), (if Nat.Prime k then Real.log (k : ℝ) else 0) ^ 2
      ≤ Real.log 4 * (n : ℝ) * Real.log (n : ℝ) := by
  have hθ : ∑ k ∈ Finset.range (n + 1), (if Nat.Prime k then Real.log (k : ℝ) else 0)
      = Chebyshev.theta (n : ℝ) := by
    unfold Chebyshev.theta
    rw [Nat.floor_natCast, ← Finset.sum_filter]
    apply Finset.sum_congr
    · ext p
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ioc]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨⟨h2.pos, by omega⟩, h2⟩
      · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨by omega, h3⟩
    · intros; rfl
  have hle : ∀ k ∈ Finset.range (n + 1),
      (if Nat.Prime k then Real.log (k : ℝ) else 0) ^ 2
        ≤ Real.log (n : ℝ) * (if Nat.Prime k then Real.log (k : ℝ) else 0) := by
    intro k hk
    have hkn : k ≤ n := by simpa [Nat.lt_succ_iff] using hk
    by_cases hp : Nat.Prime k
    · simp only [hp, ite_true]
      have h2 : (2 : ℝ) ≤ k := by exact_mod_cast hp.two_le
      have hk0 : 0 ≤ Real.log (k : ℝ) := Real.log_nonneg (by linarith)
      have : Real.log (k : ℝ) ≤ Real.log (n : ℝ) :=
        Real.log_le_log (by linarith) (by exact_mod_cast hkn)
      nlinarith
    · simp [hp]
  calc _ ≤ ∑ k ∈ Finset.range (n + 1), Real.log (n : ℝ) *
          (if Nat.Prime k then Real.log (k : ℝ) else 0) := Finset.sum_le_sum hle
    _ = Real.log (n : ℝ) * Chebyshev.theta (n : ℝ) := by rw [← Finset.mul_sum, hθ]
    _ ≤ Real.log (n : ℝ) * (Real.log 4 * (n : ℝ)) := by
        apply mul_le_mul_of_nonneg_left (Chebyshev.theta_le_log4_mul_x (by positivity))
        rcases Nat.eq_zero_or_pos n with h | h
        · subst h; simp
        · exact Real.log_nonneg (by exact_mod_cast h)
    _ = _ := by ring

private lemma cell_card (n : ℕ) (hn : 0 < n) (c : ℝ) (B : Finset (ℕ × ℕ))
    (hB : ∀ p ∈ B, 0 < p.1 ∧ (p.1 : ℝ) ≤ Real.sqrt n ∧ Nat.Coprime p.2 p.1 ∧
      ∃ t : ℝ, c ≤ t ∧ t ≤ c + 1 / (n : ℝ) ∧ |t - (p.2 : ℝ) / p.1| ≤ 1 / ((p.1 : ℝ) * Real.sqrt n)) :
    B.card ≤ 7 := by
  rcases B.eq_empty_or_nonempty with h | hne
  · simp [h]
  obtain ⟨p', hp'B, hp'max⟩ := Finset.exists_max_image B (fun p => p.1) hne
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hs : 0 < Real.sqrt n := Real.sqrt_pos.2 hnR
  have hss : Real.sqrt n * Real.sqrt n = n := Real.mul_self_sqrt hnR.le
  set D : ℕ × ℕ → ℤ := fun p => (p.2 : ℤ) * p'.1 - (p'.2 : ℤ) * p.1 with hD
  have hcard : (B.erase p').card ≤ (Finset.Icc (-3 : ℤ) 3 |>.erase 0).card := by
    apply Finset.card_le_card_of_injOn D
    · intro p hp
      have hpp : p ≠ p' := (Finset.mem_erase.1 hp).1
      have hpB := (Finset.mem_erase.1 hp).2
      obtain ⟨hq, hqs, hcop, t, ht1, ht2, ht3⟩ := hB p hpB
      obtain ⟨hq', hqs', hcop', t', ht1', ht2', ht3'⟩ := hB p' hp'B
      have hqq : p.1 ≤ p'.1 := hp'max p hpB
      simp only [Finset.coe_erase, Finset.coe_Icc, Set.mem_diff, Set.mem_Icc, Set.mem_singleton_iff]
      constructor
      · have hqR : (0 : ℝ) < p.1 := by exact_mod_cast hq
        have hqR' : (0 : ℝ) < p'.1 := by exact_mod_cast hq'
        have e1 : |(p.2 : ℝ) - p.1 * t| ≤ 1 / Real.sqrt n := by
          have : (p.2 : ℝ) - p.1 * t = -((p.1 : ℝ) * (t - p.2 / p.1)) := by field_simp; ring
          rw [this, abs_neg, abs_mul, abs_of_pos hqR]
          calc (p.1 : ℝ) * |t - p.2 / p.1| ≤ p.1 * (1 / (p.1 * Real.sqrt n)) :=
                mul_le_mul_of_nonneg_left ht3 hqR.le
            _ = 1 / Real.sqrt n := by field_simp
        have e2 : |(p'.1 : ℝ) * t' - p'.2| ≤ 1 / Real.sqrt n := by
          have : (p'.1 : ℝ) * t' - p'.2 = (p'.1 : ℝ) * (t' - p'.2 / p'.1) := by field_simp
          rw [this, abs_mul, abs_of_pos hqR']
          calc (p'.1 : ℝ) * |t' - p'.2 / p'.1| ≤ p'.1 * (1 / (p'.1 * Real.sqrt n)) :=
                mul_le_mul_of_nonneg_left ht3' hqR'.le
            _ = 1 / Real.sqrt n := by field_simp
        have e3 : |t - t'| ≤ 1 / n := by
          rw [abs_le]; constructor <;> linarith
        have hqs1 : (p.1 : ℝ) ≤ Real.sqrt n := hqs
        have hqs2 : (p'.1 : ℝ) ≤ Real.sqrt n := hqs'
        have key : ((p.2 : ℝ) * p'.1 - (p'.2 : ℝ) * p.1) =
            p'.1 * ((p.2 : ℝ) - p.1 * t) + (p.1 * p'.1) * (t - t')
              + p.1 * ((p'.1 : ℝ) * t' - p'.2) := by ring
        have bnd : |((p.2 : ℝ) * p'.1 - (p'.2 : ℝ) * p.1)| ≤ 3 := by
          rw [key]
          have b1 : |(p'.1 : ℝ) * ((p.2 : ℝ) - p.1 * t)| ≤ 1 := by
            rw [abs_mul, abs_of_pos hqR']
            calc (p'.1 : ℝ) * |(p.2 : ℝ) - p.1 * t| ≤ Real.sqrt n * (1 / Real.sqrt n) :=
                  mul_le_mul hqs2 e1 (abs_nonneg _) hs.le
              _ = 1 := by field_simp
          have b2 : |((p.1 : ℝ) * p'.1) * (t - t')| ≤ 1 := by
            rw [abs_mul, abs_of_pos (mul_pos hqR hqR')]
            calc ((p.1 : ℝ) * p'.1) * |t - t'| ≤ (Real.sqrt n * Real.sqrt n) * (1 / n) :=
                  mul_le_mul (mul_le_mul hqs1 hqs2 hqR'.le hs.le) e3 (abs_nonneg _)
                    (by positivity)
              _ = 1 := by rw [hss]; field_simp
          have b3 : |(p.1 : ℝ) * ((p'.1 : ℝ) * t' - p'.2)| ≤ 1 := by
            rw [abs_mul, abs_of_pos hqR]
            calc (p.1 : ℝ) * |(p'.1 : ℝ) * t' - p'.2| ≤ Real.sqrt n * (1 / Real.sqrt n) :=
                  mul_le_mul hqs1 e2 (abs_nonneg _) hs.le
              _ = 1 := by field_simp
          calc _ ≤ |(p'.1 : ℝ) * ((p.2 : ℝ) - p.1 * t) + (p.1 * p'.1) * (t - t')|
                  + |(p.1 : ℝ) * ((p'.1 : ℝ) * t' - p'.2)| := abs_add_le _ _
            _ ≤ (|(p'.1 : ℝ) * ((p.2 : ℝ) - p.1 * t)| + |((p.1 : ℝ) * p'.1) * (t - t')|)
                  + |(p.1 : ℝ) * ((p'.1 : ℝ) * t' - p'.2)| := by
                gcongr; exact abs_add_le _ _
            _ ≤ 3 := by linarith
        have bnd' : |D p| ≤ 3 := by
          have : ((|D p| : ℤ) : ℝ) ≤ 3 := by
            rw [Int.cast_abs]; simpa [hD] using bnd
          exact_mod_cast this
        exact abs_le.1 bnd'
      · intro h0
        apply hpp
        have h0' : (p.2 : ℤ) * p'.1 = (p'.2 : ℤ) * p.1 := by
          simp only [hD] at h0; linarith
        have h0n : p.2 * p'.1 = p'.2 * p.1 := by exact_mod_cast h0'
        have d1 : p.1 ∣ p'.1 := by
          have : p.1 ∣ p.2 * p'.1 := ⟨p'.2, by rw [h0n]; ring⟩
          exact (Nat.Coprime.symm hcop).dvd_of_dvd_mul_left this
        have d2 : p'.1 ∣ p.1 := by
          have : p'.1 ∣ p'.2 * p.1 := ⟨p.2, by rw [← h0n]; ring⟩
          exact (Nat.Coprime.symm (hB p' hp'B).2.2.1).dvd_of_dvd_mul_left this
        have hq : p.1 = p'.1 := Nat.dvd_antisymm d1 d2
        have : p.2 = p'.2 := by
          rw [hq] at h0n
          exact Nat.eq_of_mul_eq_mul_right (hB p' hp'B).1 h0n
        exact Prod.ext hq this
    · intro p1 hp1 p2 hp2 heq
      have hp1B := (Finset.mem_erase.1 hp1).2
      have hp2B := (Finset.mem_erase.1 hp2).2
      have hq1 := (hB p1 hp1B).1
      have hq2 := (hB p2 hp2B).1
      have hq1' : p1.1 ≤ p'.1 := hp'max p1 hp1B
      have hq2' : p2.1 ≤ p'.1 := hp'max p2 hp2B
      have hq' := (hB p' hp'B).1
      have hcop' : Nat.Coprime p'.2 p'.1 := (hB p' hp'B).2.2.1
      simp only [hD] at heq
      have h1 : ((p'.1 : ℤ)) ∣ (p'.2 : ℤ) * ((p1.1 : ℤ) - p2.1) := by
        refine ⟨(p1.2 : ℤ) - p2.2, ?_⟩
        linarith
      have hcz : IsCoprime ((p'.1 : ℕ) : ℤ) ((p'.2 : ℕ) : ℤ) :=
        Nat.isCoprime_iff_coprime.2 hcop'.symm
      have h2 : ((p'.1 : ℤ)) ∣ ((p1.1 : ℤ) - p2.1) := hcz.dvd_of_dvd_mul_left h1
      have h3 : ((p1.1 : ℤ) - p2.1) = 0 := by
        apply Int.eq_zero_of_abs_lt_dvd h2
        rw [abs_lt]; constructor <;> omega
      have hqe : p1.1 = p2.1 := by omega
      have hae : p1.2 = p2.2 := by
        have : (p1.2 : ℤ) * p'.1 = (p2.2 : ℤ) * p'.1 := by
          have : (p'.2 : ℤ) * p1.1 = (p'.2 : ℤ) * p2.1 := by rw [hqe]
          linarith
        have h4 : (p1.2 : ℤ) = p2.2 := mul_right_cancel₀ (by exact_mod_cast hq'.ne') this
        exact_mod_cast h4
      exact Prod.ext hqe hae
  have h6 : (Finset.Icc (-3 : ℤ) 3 |>.erase 0).card = 6 := by decide
  have := Finset.card_erase_add_one hp'B
  omega

private lemma main_ineq (n : ℕ) (hn : 0 < n) (u : ℕ → ℝ) (A : Finset (ℕ × ℕ)) (T : ℝ)
    (hT : 0 ≤ T)
    (hA : ∀ p ∈ A, 0 < p.1 ∧ (p.1 : ℝ) ≤ Real.sqrt n ∧ Nat.Coprime p.2 p.1 ∧
      ∃ t ∈ Icc (0 : ℝ) 1, |t - (p.2 : ℝ) / p.1| ≤ 1 / ((p.1 : ℝ) * Real.sqrt n)
        ∧ T ≤ ‖Sf n u t‖) :
    (A.card : ℝ) * T ^ 2 ≤ 7 * (1 + 4 * Real.pi) * n * ∑ k ∈ Finset.range (n + 1), (u k) ^ 2 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hA' : ∀ p ∈ A, ∃ t : ℝ, t ∈ Icc (0 : ℝ) 1 ∧
      |t - (p.2 : ℝ) / p.1| ≤ 1 / ((p.1 : ℝ) * Real.sqrt n) ∧ T ≤ ‖Sf n u t‖ := by
    intro p hp
    obtain ⟨_, _, _, t, ht, h1, h2⟩ := hA p hp
    exact ⟨t, ht, h1, h2⟩
  choose! tt htt using hA'
  set cell : ℕ × ℕ → ℕ := fun p => min ⌊(n : ℝ) * tt p⌋₊ (n - 1) with hcell
  have hcellmem : ∀ p ∈ A, cell p ∈ Finset.range n := by
    intro p _
    simp only [Finset.mem_range, hcell]
    omega
  have hcellpos : ∀ p ∈ A, (cell p : ℝ) / n ≤ tt p ∧ tt p ≤ (cell p : ℝ) / n + 1 / n := by
    intro p hp
    obtain ⟨⟨h0, h1⟩, _, _⟩ := htt p hp
    have hnt0 : 0 ≤ (n : ℝ) * tt p := by positivity
    have hnt1 : (n : ℝ) * tt p ≤ n := by nlinarith
    have hf1 := Nat.floor_le hnt0
    have hf2 := Nat.lt_floor_add_one ((n : ℝ) * tt p)
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hcle : (cell p : ℝ) ≤ ⌊(n : ℝ) * tt p⌋₊ := by
      exact_mod_cast min_le_left _ _
    have hc2 : (n : ℝ) * tt p ≤ cell p + 1 := by
      rcases le_total ⌊(n : ℝ) * tt p⌋₊ (n - 1) with h | h
      · have e : cell p = ⌊(n : ℝ) * tt p⌋₊ := min_eq_left h
        rw [e]; linarith
      · have e : cell p = n - 1 := min_eq_right h
        have e2 : (cell p : ℝ) = n - 1 := by rw [e, Nat.cast_sub hn]; simp
        rw [e2]; linarith
    constructor
    · rw [div_le_iff₀ hnR]; nlinarith
    · rw [← add_div, le_div_iff₀ hnR]
      nlinarith
  set f : ℝ → ℝ := fun t => ‖Sf n u t‖ ^ 2 with hf
  set g : ℝ → ℝ := fun t => 2 * ‖Sf n u t‖ * ‖Df n u t‖ with hg
  have hSc := Sf_cont n u
  have hDc := Df_cont n u
  have hfc : Continuous f := by simp only [hf]; fun_prop
  have hgc : Continuous g := by simp only [hg]; fun_prop
  set B : ℕ → ℝ := fun c => (n : ℝ) * (∫ t in ((c : ℕ) : ℝ) / n..((c + 1 : ℕ) : ℝ) / n, f t)
    + ∫ t in ((c : ℕ) : ℝ) / n..((c + 1 : ℕ) : ℝ) / n, g t with hB
  have hab : ∀ c : ℕ, ((c : ℕ) : ℝ) / n < ((c + 1 : ℕ) : ℝ) / n := by
    intro c
    apply div_lt_div_of_pos_right _ hnR
    push_cast; linarith
  have hBnn : ∀ c : ℕ, 0 ≤ B c := by
    intro c
    have h1 : 0 ≤ ∫ t in ((c : ℕ) : ℝ) / n..((c + 1 : ℕ) : ℝ) / n, f t :=
      intervalIntegral.integral_nonneg (hab c).le (fun t _ => by simp only [hf]; positivity)
    have h2 : 0 ≤ ∫ t in ((c : ℕ) : ℝ) / n..((c + 1 : ℕ) : ℝ) / n, g t :=
      intervalIntegral.integral_nonneg (hab c).le (fun t _ => by simp only [hg]; positivity)
    simp only [hB]; positivity
  have hpt : ∀ p ∈ A, T ^ 2 ≤ B (cell p) := by
    intro p hp
    obtain ⟨⟨h0, h1⟩, _, hT'⟩ := htt p hp
    obtain ⟨hc1, hc2⟩ := hcellpos p hp
    have hmem : tt p ∈ Icc (((cell p : ℕ) : ℝ) / n) (((cell p + 1 : ℕ) : ℝ) / n) := by
      refine ⟨hc1, ?_⟩
      push_cast
      rw [add_div]; exact hc2
    have := gall (Sf n u) (Df n u) (Sf_deriv n u) hDc _ _ (hab (cell p)) (tt p) hmem
    have e : ((((cell p + 1 : ℕ) : ℝ) / n) - ((cell p : ℕ) : ℝ) / n)⁻¹ = n := by
      push_cast; field_simp; ring
    rw [e] at this
    calc T ^ 2 ≤ ‖Sf n u (tt p)‖ ^ 2 := pow_le_pow_left₀ hT hT' 2
      _ ≤ _ := this
  have hfib : ∀ c ∈ Finset.range n, (A.filter (fun p => cell p = c)).card ≤ 7 := by
    intro c _
    apply cell_card n hn ((c : ℝ) / n)
    intro p hp
    have hpA := (Finset.mem_filter.1 hp)
    obtain ⟨hq, hqs, hcop, _⟩ := hA p hpA.1
    obtain ⟨_, hw, _⟩ := htt p hpA.1
    obtain ⟨hc1, hc2⟩ := hcellpos p hpA.1
    rw [hpA.2] at hc1 hc2
    exact ⟨hq, hqs, hcop, tt p, hc1, hc2, hw⟩
  have hsum : ∑ c ∈ Finset.range n, B c
      = (n : ℝ) * (∫ t in (0 : ℝ)..1, f t) + ∫ t in (0 : ℝ)..1, g t := by
    have e1 := intervalIntegral.sum_integral_adjacent_intervals (a := fun c : ℕ => (c : ℝ) / n)
      (n := n) (f := f) (μ := volume) (fun k _ => hfc.intervalIntegrable _ _)
    have e2 := intervalIntegral.sum_integral_adjacent_intervals (a := fun c : ℕ => (c : ℝ) / n)
      (n := n) (f := g) (μ := volume) (fun k _ => hgc.intervalIntegrable _ _)
    simp only [Nat.cast_zero, zero_div, div_self hnR.ne'] at e1 e2
    simp only [hB]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, e1, e2]
  have hcalc : (A.card : ℝ) * T ^ 2 ≤ ∑ p ∈ A, B (cell p) := by
    have : (A.card : ℝ) * T ^ 2 = ∑ p ∈ A, T ^ 2 := by simp
    rw [this]
    exact Finset.sum_le_sum hpt
  have hfiber : ∑ p ∈ A, B (cell p)
      = ∑ c ∈ Finset.range n, ((A.filter (fun p => cell p = c)).card : ℝ) * B c := by
    rw [← Finset.sum_fiberwise_of_maps_to hcellmem]
    apply Finset.sum_congr rfl
    intro c _
    rw [Finset.sum_congr rfl (fun p hp => by rw [(Finset.mem_filter.1 hp).2])]
    simp
  have hle7 : ∑ c ∈ Finset.range n, ((A.filter (fun p => cell p = c)).card : ℝ) * B c
      ≤ ∑ c ∈ Finset.range n, 7 * B c := by
    apply Finset.sum_le_sum
    intro c hc
    have : ((A.filter (fun p => cell p = c)).card : ℝ) ≤ 7 := by exact_mod_cast hfib c hc
    exact mul_le_mul_of_nonneg_right this (hBnn c)
  rw [← Finset.mul_sum, hsum] at hle7
  have hP := parseval_S n u
  have hG := g_bound n hn u
  have hf' : (∫ t in (0 : ℝ)..1, f t) = ∑ k ∈ Finset.range (n + 1), (u k) ^ 2 := hP
  have hg' : (∫ t in (0 : ℝ)..1, g t) ≤ 4 * Real.pi * n * ∑ k ∈ Finset.range (n + 1), (u k) ^ 2 := hG
  rw [hf'] at hle7
  calc (A.card : ℝ) * T ^ 2 ≤ _ := hcalc
    _ = _ := hfiber
    _ ≤ _ := hle7
    _ ≤ 7 * ((n : ℝ) * ∑ k ∈ Finset.range (n + 1), (u k) ^ 2
          + 4 * Real.pi * n * ∑ k ∈ Finset.range (n + 1), (u k) ^ 2) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        linarith
    _ = _ := by ring

private noncomputable def wt (k : ℕ) : ℝ := if Nat.Prime k then Real.log (k : ℝ) else 0

private lemma part1 (n : ℕ) (hn : 0 < n) (η : ℝ) (A : Finset (ℕ × ℕ))
    (hA : ∀ p ∈ A, 0 < p.1 ∧ (p.1 : ℝ) ≤ Real.sqrt n ∧ Nat.Coprime p.2 p.1 ∧
      ∃ t ∈ Icc (0 : ℝ) 1, |t - (p.2 : ℝ) / p.1| ≤ 1 / ((p.1 : ℝ) * Real.sqrt n)
        ∧ (n : ℝ) ^ (3 / 4 + η) ≤ ‖Sf n wt t‖) :
    (A.card : ℝ) ≤ 7 * (1 + 4 * Real.pi) * Real.log 4 * (n : ℝ) ^ (1 / 2 - 2 * η) * Real.log n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hT0 : 0 < (n : ℝ) ^ (3 / 4 + η) := Real.rpow_pos_of_pos hnR _
  have h1 := main_ineq n hn wt A _ hT0.le hA
  have h2 : ∑ k ∈ Finset.range (n + 1), (wt k) ^ 2 ≤ Real.log 4 * (n : ℝ) * Real.log (n : ℝ) :=
    wsq_le n
  have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn)
  set T : ℝ := (n : ℝ) ^ (3 / 4 + η) with hTdef
  have hTT : T ^ 2 * (n : ℝ) ^ (1 / 2 - 2 * η) = (n : ℝ) ^ 2 := by
    have e1 : T ^ 2 = (n : ℝ) ^ ((3 / 4 + η) * 2) := by
      rw [Real.rpow_mul hnR.le, Real.rpow_two]
    calc T ^ 2 * (n : ℝ) ^ (1 / 2 - 2 * η)
        = (n : ℝ) ^ ((3 / 4 + η) * 2) * (n : ℝ) ^ (1 / 2 - 2 * η) := by rw [e1]
      _ = (n : ℝ) ^ ((3 / 4 + η) * 2 + (1 / 2 - 2 * η)) := (Real.rpow_add hnR _ _).symm
      _ = (n : ℝ) ^ (2 : ℝ) := by congr 1; ring
      _ = (n : ℝ) ^ 2 := Real.rpow_two _
  have h3 : (A.card : ℝ) * T ^ 2 ≤
      (7 * (1 + 4 * Real.pi) * Real.log 4 * (n : ℝ) ^ (1 / 2 - 2 * η) * Real.log n) * T ^ 2 := by
    calc (A.card : ℝ) * T ^ 2 ≤ 7 * (1 + 4 * Real.pi) * n * ∑ k ∈ Finset.range (n + 1), (wt k) ^ 2 := h1
      _ ≤ 7 * (1 + 4 * Real.pi) * n * (Real.log 4 * (n : ℝ) * Real.log (n : ℝ)) := by
          apply mul_le_mul_of_nonneg_left h2
          have := Real.pi_pos
          positivity
      _ = 7 * (1 + 4 * Real.pi) * Real.log 4 * Real.log n * ((n : ℝ) ^ 2) := by ring
      _ = _ := by rw [← hTT]; ring
  exact le_of_mul_le_mul_right h3 (by positivity)

theorem Conjectures.Goldbach.ThreeQuartersExceptionalDirichletWindows :
    let w := fun k : ℕ => if Nat.Prime k then Real.log (k:ℝ) else 0
    let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I)
    let S := fun (n : ℕ) (u : ℕ→ℝ) (t : ℝ) => ∑ k ∈ Finset.range (n+1), (u k:ℂ)*E ((k:ℝ)*t)
    (∀ n : ℕ, 0<n → ∀ η : ℝ, ∀ A : Finset (ℕ×ℕ),
      (∀ p ∈ A, 0<p.1 ∧ (p.1:ℝ)≤Real.sqrt n ∧ p.2.Coprime p.1 ∧
        ∃ t ∈ Set.Icc (0:ℝ) 1, |t-(p.2:ℝ)/p.1|≤1/((p.1:ℝ)*Real.sqrt n) ∧ (n:ℝ)^(3/4+η)≤‖S n w t‖) →
      (A.card:ℝ) ≤ 7*(1+4*Real.pi)*Real.log 4*(n:ℝ)^(1/2-2*η)*Real.log n) ∧
    (∀ η : ℝ, 0<η → ∃ N : ℕ, ∀ n : ℕ, N≤n →
      ∃ bad : Finset ℕ, (bad.card:ℝ) ≤ (n:ℝ)^(1/2-η) ∧
        ∀ q : ℕ, 0<q → (q:ℝ)≤Real.sqrt n → q ∉ bad → ∀ a : ℕ, a≤q → a.Coprime q →
        ∀ t ∈ Set.Icc (0:ℝ) 1, |t-(a:ℝ)/q|≤1/((q:ℝ)*Real.sqrt n) → ‖S n w t‖ < (n:ℝ)^(3/4+η)) := by
  intro w E S
  have hw : w = wt := rfl
  refine ⟨?_, ?_⟩
  · intro n hn η A hA
    exact part1 n hn η A hA
  · intro η hη
    set K : ℝ := 7 * (1 + 4 * Real.pi) * Real.log 4 with hK
    have hKpos : 0 < K := by
      have := Real.pi_pos
      have : 0 < Real.log 4 := Real.log_pos (by norm_num)
      positivity
    have hev := (isLittleO_log_rpow_atTop hη).bound (c := 1 / (K + 1)) (by positivity)
    obtain ⟨X0, hX0⟩ := Filter.eventually_atTop.1 hev
    refine ⟨max 1 ⌈X0⌉₊, ?_⟩
    intro n hnN
    have hn1 : 1 ≤ n := le_trans (le_max_left _ _) hnN
    have hn : 0 < n := hn1
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have hX : X0 ≤ (n : ℝ) := by
      have : ⌈X0⌉₊ ≤ n := le_trans (le_max_right _ _) hnN
      exact (Nat.le_ceil X0).trans (by exact_mod_cast this)
    have hlogle := hX0 (n : ℝ) hX
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg (by exact_mod_cast hn1)),
      abs_of_nonneg (Real.rpow_nonneg hnR.le _)] at hlogle
    have hKlog : K * Real.log (n : ℝ) ≤ (n : ℝ) ^ η := by
      have h1 : Real.log (n : ℝ) * (K + 1) ≤ (n : ℝ) ^ η := by
        have := mul_le_mul_of_nonneg_right hlogle (by positivity : (0 : ℝ) ≤ K + 1)
        calc Real.log (n : ℝ) * (K + 1) ≤ 1 / (K + 1) * (n : ℝ) ^ η * (K + 1) := this
          _ = (n : ℝ) ^ η := by field_simp
      have hl : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn1)
      nlinarith
    classical
    set T : ℝ := (n : ℝ) ^ (3 / 4 + η) with hT
    set A : Finset (ℕ × ℕ) :=
      ((Finset.Icc 1 ⌊Real.sqrt n⌋₊) ×ˢ Finset.range (⌊Real.sqrt n⌋₊ + 2)).filter
        (fun p => Nat.Coprime p.2 p.1 ∧ ∃ t ∈ Icc (0 : ℝ) 1,
          |t - (p.2 : ℝ) / p.1| ≤ 1 / ((p.1 : ℝ) * Real.sqrt n) ∧ T ≤ ‖Sf n wt t‖) with hAdef
    have hAmem : ∀ p ∈ A, 0 < p.1 ∧ (p.1 : ℝ) ≤ Real.sqrt n ∧ Nat.Coprime p.2 p.1 ∧
        ∃ t ∈ Icc (0 : ℝ) 1, |t - (p.2 : ℝ) / p.1| ≤ 1 / ((p.1 : ℝ) * Real.sqrt n)
          ∧ (n : ℝ) ^ (3 / 4 + η) ≤ ‖Sf n wt t‖ := by
      intro p hp
      simp only [hAdef, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hp
      obtain ⟨⟨⟨h1, h2⟩, _⟩, h3, h4⟩ := hp
      exact ⟨h1, (Nat.le_floor_iff (Real.sqrt_nonneg _)).1 h2, h3, h4⟩
    have hcard := part1 n hn η A hAmem
    refine ⟨A.image Prod.fst, ?_, ?_⟩
    · refine le_trans (by exact_mod_cast Finset.card_image_le) (hcard.trans ?_)
      have hp : (0 : ℝ) < (n : ℝ) ^ (1 / 2 - 2 * η) := Real.rpow_pos_of_pos hnR _
      have e : (n : ℝ) ^ (1 / 2 - η) = (n : ℝ) ^ (1 / 2 - 2 * η) * (n : ℝ) ^ η := by
        rw [← Real.rpow_add hnR]; congr 1; ring
      rw [e]
      calc 7 * (1 + 4 * Real.pi) * Real.log 4 * (n : ℝ) ^ (1 / 2 - 2 * η) * Real.log n
          = (n : ℝ) ^ (1 / 2 - 2 * η) * (K * Real.log (n : ℝ)) := by rw [hK]; ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hKlog hp.le
    · intro q hq hqs hqb a haq hcop t ht hwin
      by_contra hcon
      rw [not_lt] at hcon
      apply hqb
      rw [Finset.mem_image]
      refine ⟨(q, a), ?_, rfl⟩
      simp only [hAdef, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_range]
      have hfl : q ≤ ⌊Real.sqrt n⌋₊ := (Nat.le_floor_iff (Real.sqrt_nonneg _)).2 hqs
      exact ⟨⟨⟨hq, hfl⟩, by omega⟩, hcop, t, ht, hwin, hcon⟩
