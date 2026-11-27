import Mathlib

private theorem u1n_orth (N : ℕ) (hN : 0 < N) (k : ℤ) :
    ∑ ξ ∈ Finset.range N, Complex.exp (2 * Real.pi * Complex.I * (k : ℂ) * (ξ : ℂ) / (N : ℂ))
      = if (N : ℤ) ∣ k then (N : ℂ) else 0 := by
  have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  set r : ℂ := Complex.exp (2 * Real.pi * Complex.I * (k : ℂ) / (N : ℂ)) with hr
  have h1 : ∀ ξ : ℕ, Complex.exp (2 * Real.pi * Complex.I * (k : ℂ) * (ξ : ℂ) / (N : ℂ)) = r ^ ξ := by
    intro ξ
    rw [hr, ← Complex.exp_nat_mul]
    congr 1
    ring
  simp_rw [h1]
  have hrN : r ^ N = 1 := by
    rw [hr, ← Complex.exp_nat_mul]
    have : (N : ℂ) * (2 * Real.pi * Complex.I * (k : ℂ) / (N : ℂ)) = (k : ℂ) * (2 * Real.pi * Complex.I) := by
      field_simp
    rw [this]
    exact Complex.exp_int_mul_two_pi_mul_I k
  split_ifs with h
  · obtain ⟨j, rfl⟩ := h
    have : r = 1 := by
      rw [hr]
      have : 2 * (Real.pi : ℂ) * Complex.I * (((N : ℤ) * j : ℤ) : ℂ) / (N : ℂ) = (j : ℂ) * (2 * Real.pi * Complex.I) := by
        push_cast
        field_simp
      rw [this]
      exact Complex.exp_int_mul_two_pi_mul_I j
    rw [this]
    simp
  · have hr1 : r ≠ 1 := by
      intro h1
      rw [hr, Complex.exp_eq_one_iff] at h1
      obtain ⟨j, hj⟩ := h1
      apply h
      refine ⟨j, ?_⟩
      have h2 : (k : ℂ) = (N : ℂ) * (j : ℂ) := by
        have hpi : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
          simp [Real.pi_ne_zero, Complex.I_ne_zero]
        field_simp at hj
        exact_mod_cast hj
      exact_mod_cast h2
    rw [geom_sum_eq hr1, hrN]
    simp

private theorem u1n_pair_add (N n m : ℕ) (hn : n ∈ Finset.Ico 1 N) (hm : m ∈ Finset.Ico 1 N) :
    (N : ℤ) ∣ -((n : ℤ) + m) ↔ m = N - n := by
  rw [Finset.mem_Ico] at hn hm
  rw [dvd_neg, ← Nat.cast_add, Int.natCast_dvd_natCast]
  constructor
  · rintro ⟨c, hc⟩
    rcases c with _ | _ | c
    · omega
    · omega
    · have : N * (c + 1 + 1) ≥ N * 2 := Nat.mul_le_mul_left _ (by omega)
      omega
  · intro h
    exact ⟨1, by omega⟩

private theorem u1n_pair_sub (N n m : ℕ) (hn : n ∈ Finset.Ico 1 N) (hm : m ∈ Finset.Ico 1 N) :
    (N : ℤ) ∣ ((m : ℤ) - n) ↔ m = n := by
  rw [Finset.mem_Ico] at hn hm
  constructor
  · intro h
    have := Int.eq_zero_of_abs_lt_dvd h (by rw [abs_lt]; constructor <;> omega)
    omega
  · intro h
    subst h
    simp

theorem Conjectures.Goldbach.U1nLorentzReflection :
    ∀ (N : ℕ) (a : ℕ → ℝ), 2 ≤ N → let z : ℕ → ℂ := fun ξ => ((N : ℝ).sqrt : ℂ)⁻¹ * ∑ n ∈ Finset.Ico 1 N, (a n : ℂ) * Complex.exp (-2 * Real.pi * Complex.I * (n : ℂ) * (ξ : ℂ) / (N : ℂ)); (∑ ξ ∈ Finset.Ico 1 N, (z ξ) ^ 2 + (z 0) ^ 2 = ((∑ n ∈ Finset.Ico 1 N, a n * a (N - n) : ℝ) : ℂ)) ∧ (‖z 0‖ ^ 2 - ∑ ξ ∈ Finset.Ico 1 N, ‖z ξ‖ ^ 2 = 2 / (N : ℝ) * (∑ n ∈ Finset.Ico 1 N, a n) ^ 2 - ∑ n ∈ Finset.Ico 1 N, (a n) ^ 2) := by
  intro N a hN z
  have hN0 : 0 < N := by omega
  have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast hN0.ne'
  have hc2 : (((N : ℝ).sqrt : ℂ)⁻¹) ^ 2 = (N : ℂ)⁻¹ := by
    rw [inv_pow, ← Complex.ofReal_pow, Real.sq_sqrt (by positivity)]
    simp
  have hrange : ∀ f : ℕ → ℂ, ∑ ξ ∈ Finset.range N, f ξ = f 0 + ∑ ξ ∈ Finset.Ico 1 N, f ξ := by
    intro f
    rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot hN0]
  have hrangeR : ∀ f : ℕ → ℝ, ∑ ξ ∈ Finset.range N, f ξ = f 0 + ∑ ξ ∈ Finset.Ico 1 N, f ξ := by
    intro f
    rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot hN0]
  have hz : ∀ ξ, z ξ = ((N : ℝ).sqrt : ℂ)⁻¹ * ∑ n ∈ Finset.Ico 1 N, (a n : ℂ) * Complex.exp (-2 * Real.pi * Complex.I * (n : ℂ) * (ξ : ℂ) / (N : ℂ)) := fun ξ => rfl
  have hzc : ∀ ξ, (starRingEnd ℂ) (z ξ) = ((N : ℝ).sqrt : ℂ)⁻¹ * ∑ n ∈ Finset.Ico 1 N, (a n : ℂ) * Complex.exp (2 * Real.pi * Complex.I * (n : ℂ) * (ξ : ℂ) / (N : ℂ)) := by
    intro ξ
    rw [hz, map_mul, map_sum, map_inv₀, Complex.conj_ofReal]
    refine congrArg _ (Finset.sum_congr rfl ?_)
    intro n _
    rw [map_mul, Complex.conj_ofReal, ← Complex.exp_conj]
    have hh : (starRingEnd ℂ) (-2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (ξ : ℂ) / (N : ℂ)) = 2 * Real.pi * Complex.I * (n : ℂ) * (ξ : ℂ) / (N : ℂ) := by
      simp only [map_mul, map_div₀, map_neg, map_ofNat, Complex.conj_ofReal, Complex.conj_I, map_natCast]
      ring
    rw [hh]
  have hexp1 : ∀ (n m ξ : ℕ), Complex.exp (-2 * Real.pi * Complex.I * (n : ℂ) * (ξ : ℂ) / (N : ℂ)) * Complex.exp (-2 * Real.pi * Complex.I * (m : ℂ) * (ξ : ℂ) / (N : ℂ)) = Complex.exp (2 * Real.pi * Complex.I * ((-((n : ℤ) + m) : ℤ) : ℂ) * (ξ : ℂ) / (N : ℂ)) := by
    intro n m ξ
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hexp2 : ∀ (n m ξ : ℕ), Complex.exp (-2 * Real.pi * Complex.I * (n : ℂ) * (ξ : ℂ) / (N : ℂ)) * Complex.exp (2 * Real.pi * Complex.I * (m : ℂ) * (ξ : ℂ) / (N : ℂ)) = Complex.exp (2 * Real.pi * Complex.I * (((m : ℤ) - n : ℤ) : ℂ) * (ξ : ℂ) / (N : ℂ)) := by
    intro n m ξ
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hS1 : ∑ ξ ∈ Finset.range N, (z ξ) ^ 2 = ((∑ n ∈ Finset.Ico 1 N, a n * a (N - n) : ℝ) : ℂ) := by
    have h1 : ∀ ξ, (z ξ) ^ 2 = (N : ℂ)⁻¹ * ∑ n ∈ Finset.Ico 1 N, ∑ m ∈ Finset.Ico 1 N, (a n : ℂ) * (a m : ℂ) * Complex.exp (2 * Real.pi * Complex.I * ((-((n : ℤ) + m) : ℤ) : ℂ) * (ξ : ℂ) / (N : ℂ)) := by
      intro ξ
      rw [hz, mul_pow, hc2, sq, Finset.sum_mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro n _
      apply Finset.sum_congr rfl
      intro m _
      rw [← hexp1 n m ξ]
      ring
    simp_rw [h1]
    rw [← Finset.mul_sum, Finset.sum_comm]
    have h2 : ∀ n ∈ Finset.Ico 1 N, ∑ ξ ∈ Finset.range N, ∑ m ∈ Finset.Ico 1 N, (a n : ℂ) * (a m : ℂ) * Complex.exp (2 * Real.pi * Complex.I * ((-((n : ℤ) + m) : ℤ) : ℂ) * (ξ : ℂ) / (N : ℂ)) = (N : ℂ) * ((a n * a (N - n) : ℝ) : ℂ) := by
      intro n hn
      rw [Finset.sum_comm]
      have : ∀ m ∈ Finset.Ico 1 N, ∑ ξ ∈ Finset.range N, (a n : ℂ) * (a m : ℂ) * Complex.exp (2 * Real.pi * Complex.I * ((-((n : ℤ) + m) : ℤ) : ℂ) * (ξ : ℂ) / (N : ℂ)) = (a n : ℂ) * (a m : ℂ) * (if m = N - n then (N : ℂ) else 0) := by
        intro m hm
        rw [← Finset.mul_sum, u1n_orth N hN0]
        simp only [u1n_pair_add N n m hn hm]
      rw [Finset.sum_congr rfl this, Finset.sum_eq_single (N - n)]
      · try simp only [if_true]
        push_cast
        ring
      · intro m hm hne
        simp [hne]
      · intro h
        exfalso
        apply h
        rw [Finset.mem_Ico] at hn ⊢
        omega
    rw [Finset.sum_congr rfl h2, ← Finset.mul_sum, ← mul_assoc, inv_mul_cancel₀ hNc, one_mul]
    push_cast
    rfl
  have hS2 : ∑ ξ ∈ Finset.range N, ‖z ξ‖ ^ 2 = ∑ n ∈ Finset.Ico 1 N, (a n) ^ 2 := by
    have h0 : ∀ ξ, ((‖z ξ‖ ^ 2 : ℝ) : ℂ) = (N : ℂ)⁻¹ * ∑ n ∈ Finset.Ico 1 N, ∑ m ∈ Finset.Ico 1 N, (a n : ℂ) * (a m : ℂ) * Complex.exp (2 * Real.pi * Complex.I * (((m : ℤ) - n : ℤ) : ℂ) * (ξ : ℂ) / (N : ℂ)) := by
      intro ξ
      have : ((‖z ξ‖ ^ 2 : ℝ) : ℂ) = z ξ * (starRingEnd ℂ) (z ξ) := by
        rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
      rw [this, hzc, hz]
      rw [mul_mul_mul_comm, ← sq, hc2, Finset.sum_mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro n _
      apply Finset.sum_congr rfl
      intro m _
      rw [← hexp2 n m ξ]
      ring
    apply Complex.ofReal_injective
    rw [Complex.ofReal_sum, Finset.sum_congr rfl (fun ξ _ => h0 ξ), ← Finset.mul_sum, Finset.sum_comm]
    have h2 : ∀ n ∈ Finset.Ico 1 N, ∑ ξ ∈ Finset.range N, ∑ m ∈ Finset.Ico 1 N, (a n : ℂ) * (a m : ℂ) * Complex.exp (2 * Real.pi * Complex.I * (((m : ℤ) - n : ℤ) : ℂ) * (ξ : ℂ) / (N : ℂ)) = (N : ℂ) * ((a n ^ 2 : ℝ) : ℂ) := by
      intro n hn
      rw [Finset.sum_comm]
      have : ∀ m ∈ Finset.Ico 1 N, ∑ ξ ∈ Finset.range N, (a n : ℂ) * (a m : ℂ) * Complex.exp (2 * Real.pi * Complex.I * (((m : ℤ) - n : ℤ) : ℂ) * (ξ : ℂ) / (N : ℂ)) = (a n : ℂ) * (a m : ℂ) * (if m = n then (N : ℂ) else 0) := by
        intro m hm
        rw [← Finset.mul_sum, u1n_orth N hN0]
        simp only [u1n_pair_sub N n m hn hm]
      rw [Finset.sum_congr rfl this, Finset.sum_eq_single n]
      · try simp only [if_true]
        push_cast
        ring
      · intro m hm hne
        simp [hne]
      · intro h
        exact absurd hn h
    rw [Finset.sum_congr rfl h2, ← Finset.mul_sum, ← mul_assoc, inv_mul_cancel₀ hNc, one_mul]
    push_cast
    rfl
  have hz0 : ‖z 0‖ ^ 2 = (∑ n ∈ Finset.Ico 1 N, a n) ^ 2 / (N : ℝ) := by
    have : z 0 = ((((∑ n ∈ Finset.Ico 1 N, a n) / (N : ℝ).sqrt : ℝ)) : ℂ) := by
      rw [hz]
      push_cast
      simp [div_eq_inv_mul]
    rw [this, Complex.norm_real, Real.norm_eq_abs, sq_abs, div_pow, Real.sq_sqrt (by positivity)]
  constructor
  · have := hS1
    rw [hrange] at this
    rw [← this]
    ring
  · have h3 := hS2
    rw [hrangeR] at h3
    have h4 : 2 / (N : ℝ) * (∑ n ∈ Finset.Ico 1 N, a n) ^ 2 = 2 * ((∑ n ∈ Finset.Ico 1 N, a n) ^ 2 / (N : ℝ)) := by ring
    rw [h4, ← hz0]
    linarith
