import Mathlib

namespace JoshiQJ

variable {K : Type} [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]

private lemma tail1 (f : ℤ → K) (hs : Summable f) (i : ℤ) (C : ℝ) (hC : 0 ≤ C)
    (h : ∀ n, n ≠ i → ‖f n‖ ≤ C) : ‖∑' n, f n - f i‖ ≤ C := by
  classical
  have h1 := hasSum_ite_sub_hasSum hs.hasSum i
  rw [← h1.tsum_eq]
  apply IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg hC
  intro n
  by_cases hn : n = i
  · simp [hn, hC]
  · simp [hn, h n hn]

private lemma tail2 (f : ℤ → K) (hs : Summable f) (i j : ℤ) (hij : j ≠ i) (C : ℝ) (hC : 0 ≤ C)
    (h : ∀ n, n ≠ i → n ≠ j → ‖f n‖ ≤ C) : ‖∑' n, f n - f i - f j‖ ≤ C := by
  classical
  have h1 := hasSum_ite_sub_hasSum hs.hasSum i
  have h2 := tail1 (fun n => if n = i then 0 else f n) h1.summable j C hC (by
    intro n hn
    by_cases hni : n = i
    · simp [hni, hC]
    · simp [hni]; exact h n hni hn)
  rw [h1.tsum_eq] at h2
  simpa [hij] using h2

private lemma expand (r z u : K) (hr0 : 0 < ‖r‖) (hr1 : ‖r‖ < 1) (hz : ‖z‖ = 1) (s : ℤ)
    (hs1 : 1 ≤ s) (hs2 : s ≤ 2) (hu : u = r ^ s * z) :
    Summable (fun n : ℤ => r ^ (7 * (n * (n + 1)) + s * (2 * n + 1)) * z ^ (2 * n + 1)) ∧
    ∀ n : ℤ, (r ^ 14) ^ (n * (n + 1) / 2) * u ^ (2 * n + 1)
      = r ^ (7 * (n * (n + 1)) + s * (2 * n + 1)) * z ^ (2 * n + 1) := by
  have hr : r ≠ 0 := norm_pos_iff.mp hr0
  have hz0 : z ≠ 0 := by intro h; simp [h] at hz
  refine ⟨?_, ?_⟩
  · have hnorm : ∀ n : ℤ, ‖r ^ (7 * (n * (n + 1)) + s * (2 * n + 1)) * z ^ (2 * n + 1)‖
        = ‖r‖ ^ (7 * (n * (n + 1)) + s * (2 * n + 1)) := by
      intro n; rw [norm_mul, norm_zpow, norm_zpow, hz, one_zpow, mul_one]
    have hg : Summable (fun n : ℤ => ‖r‖ ^ n.natAbs) := by
      apply Summable.of_nat_of_neg
      · simpa using summable_geometric_of_lt_one hr0.le hr1
      · simpa using summable_geometric_of_lt_one hr0.le hr1
    refine Summable.of_norm_bounded_eventually hg ?_
    rw [Filter.eventually_cofinite]
    refine (Set.finite_singleton (-1 : ℤ)).subset ?_
    intro n hn
    simp only [Set.mem_setOf_eq, hnorm] at hn
    by_contra hne
    have hne' : n ≠ -1 := hne
    apply hn
    have hb : (n.natAbs : ℤ) ≤ 7 * (n * (n + 1)) + s * (2 * n + 1) := by
      rcases lt_or_ge n 0 with h | h
      · have h2 : n ≤ -2 := by omega
        have : -n ≤ 7 * (n * (n + 1)) + s * (2 * n + 1) := by nlinarith
        omega
      · have : n ≤ 7 * (n * (n + 1)) + s * (2 * n + 1) := by nlinarith
        omega
    calc ‖r‖ ^ (7 * (n * (n + 1)) + s * (2 * n + 1)) ≤ ‖r‖ ^ (n.natAbs : ℤ) :=
          zpow_le_zpow_right_of_le_one₀ hr0 hr1.le hb
      _ = ‖r‖ ^ n.natAbs := zpow_natCast _ _
  · intro n
    have hk : Even (n * (n + 1)) := Int.even_mul_succ_self n
    obtain ⟨k, hk⟩ := hk
    have e1 : (r ^ 14) ^ (n * (n + 1) / 2) = r ^ (7 * (n * (n + 1))) := by
      rw [← zpow_natCast, ← zpow_mul]
      congr 1
      generalize n * (n + 1) = m at *
      omega
    rw [e1, hu, mul_zpow, ← zpow_mul, zpow_add₀ hr, mul_assoc]

end JoshiQJ

theorem Conjectures.JoshiAbc.QuotientJet :
    ∀ (K : Type) [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K] [CharZero K], let theta := fun (q u : K) => ∑' n : ℤ, q^(n*(n+1)/2) * u^(2*n+1); ∀ (r z : K), r^14=(29:K) → 0 < ‖r‖ → ‖r‖ < 1 → z^7=1 → ‖z‖=1 → ‖1+z^2‖=1 → ‖theta (r^14) (r*z) / theta (r^14) (r^2*z) - (r+z^2*r^3)‖ ≤ ‖r‖^4 := by
  intro K i1 i2 i3 i4 theta r z hr14 hr0 hr1 hz7 hz hz2
  have hr : r ≠ 0 := norm_pos_iff.mp hr0
  have hz0 : z ≠ 0 := by intro h; simp [h] at hz
  obtain ⟨hs1, ht1⟩ := JoshiQJ.expand r z (r * z) hr0 hr1 hz 1 le_rfl (by norm_num) (by simp)
  obtain ⟨hs2, ht2⟩ := JoshiQJ.expand r z (r ^ 2 * z) hr0 hr1 hz 2 (by norm_num) le_rfl (by simp)
  have hnorm : ∀ (e m : ℤ), ‖r ^ e * z ^ m‖ = ‖r‖ ^ e := by
    intro e m; rw [norm_mul, norm_zpow, norm_zpow, hz, one_zpow, mul_one]
  have hT1 : theta (r ^ 14) (r * z)
      = ∑' n : ℤ, r ^ (7 * (n * (n + 1)) + 1 * (2 * n + 1)) * z ^ (2 * n + 1) := tsum_congr ht1
  have hT2 : theta (r ^ 14) (r ^ 2 * z)
      = ∑' n : ℤ, r ^ (7 * (n * (n + 1)) + 2 * (2 * n + 1)) * z ^ (2 * n + 1) := tsum_congr ht2
  have hR1 := JoshiQJ.tail2 _ hs1 (-1) 0 (by norm_num) (‖r‖ ^ 2) (by positivity) (by
    intro n h1 h2
    rw [hnorm]
    calc ‖r‖ ^ (7 * (n * (n + 1)) + 1 * (2 * n + 1)) ≤ ‖r‖ ^ ((2:ℕ):ℤ) := by
          apply zpow_le_zpow_right_of_le_one₀ hr0 hr1.le
          rcases lt_or_ge n 0 with h | h
          · have h3 : n ≤ -2 := by omega
            push_cast
            nlinarith [sq_nonneg (n + 2)]
          · have h3 : 1 ≤ n := by omega
            push_cast
            nlinarith
      _ = ‖r‖ ^ 2 := zpow_natCast _ _)
  have hR2 := JoshiQJ.tail1 _ hs2 (-1) (‖r‖) (by positivity) (by
    intro n h1
    rw [hnorm]
    calc ‖r‖ ^ (7 * (n * (n + 1)) + 2 * (2 * n + 1)) ≤ ‖r‖ ^ (1:ℤ) := by
          apply zpow_le_zpow_right_of_le_one₀ hr0 hr1.le
          rcases lt_or_ge n 0 with h | h
          · have h3 : n ≤ -2 := by omega
            nlinarith [sq_nonneg (n + 2)]
          · nlinarith
      _ = ‖r‖ := zpow_one _)
  have e1 : r ^ (7 * ((-1:ℤ) * (-1 + 1)) + 1 * (2 * (-1) + 1)) * z ^ (2 * (-1:ℤ) + 1)
      = r⁻¹ * z⁻¹ := by norm_num
  have e0 : r ^ (7 * ((0:ℤ) * (0 + 1)) + 1 * (2 * 0 + 1)) * z ^ (2 * (0:ℤ) + 1) = r * z := by
    norm_num
  have e2 : r ^ (7 * ((-1:ℤ) * (-1 + 1)) + 2 * (2 * (-1) + 1)) * z ^ (2 * (-1:ℤ) + 1)
      = (r ^ 2)⁻¹ * z⁻¹ := by norm_num
  beta_reduce at hR1 hR2
  rw [e1, e0] at hR1
  rw [e2] at hR2
  rw [hT1, hT2]
  generalize hN : ∑' n : ℤ, r ^ (7 * (n * (n + 1)) + 1 * (2 * n + 1)) * z ^ (2 * n + 1) = N at hR1 ⊢
  generalize hD : ∑' n : ℤ, r ^ (7 * (n * (n + 1)) + 2 * (2 * n + 1)) * z ^ (2 * n + 1) = D at hR2 ⊢
  have hrz : ‖r * z‖ = ‖r‖ := by rw [norm_mul, hz, mul_one]
  have hr2z : ‖r ^ 2 * z‖ = ‖r‖ ^ 2 := by rw [norm_mul, norm_pow, hz, mul_one]
  obtain ⟨E1, hE1, hNE⟩ : ∃ E1 : K, ‖E1‖ ≤ ‖r‖ ^ 3 ∧
      N = r⁻¹ * z⁻¹ * (1 + r ^ 2 * z ^ 2 + E1) := by
    refine ⟨r * z * (N - r⁻¹ * z⁻¹ - r * z), ?_, ?_⟩
    · rw [norm_mul, hrz]
      calc ‖r‖ * ‖N - r⁻¹ * z⁻¹ - r * z‖ ≤ ‖r‖ * ‖r‖ ^ 2 :=
            mul_le_mul_of_nonneg_left hR1 (norm_nonneg _)
        _ = ‖r‖ ^ 3 := by ring
    · field_simp
      ring
  obtain ⟨E2, hE2, hDE⟩ : ∃ E2 : K, ‖E2‖ ≤ ‖r‖ ^ 3 ∧
      D = (r ^ 2)⁻¹ * z⁻¹ * (1 + E2) := by
    refine ⟨r ^ 2 * z * (D - (r ^ 2)⁻¹ * z⁻¹), ?_, ?_⟩
    · rw [norm_mul, hr2z]
      calc ‖r‖ ^ 2 * ‖D - (r ^ 2)⁻¹ * z⁻¹‖ ≤ ‖r‖ ^ 2 * ‖r‖ :=
            mul_le_mul_of_nonneg_left hR2 (by positivity)
        _ = ‖r‖ ^ 3 := by ring
    · field_simp
      ring
  have hE2lt : ‖E2‖ < ‖(1:K)‖ := by
    rw [norm_one]
    calc ‖E2‖ ≤ ‖r‖ ^ 3 := hE2
      _ < 1 := pow_lt_one₀ hr0.le hr1 (by norm_num)
  have h1E2 : ‖1 + E2‖ = 1 := by
    rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hE2lt.ne', norm_one]
    exact max_eq_left (by rw [← norm_one (α := K)]; exact hE2lt.le)
  have hne : (1 + E2) ≠ 0 := by
    intro h; rw [h, norm_zero] at h1E2; exact zero_ne_one h1E2
  have key : N / D - (r + z ^ 2 * r ^ 3)
      = r * (E1 - E2 * (1 + r ^ 2 * z ^ 2)) / (1 + E2) := by
    rw [hNE, hDE]
    field_simp
    ring
  have hu : ‖1 + r ^ 2 * z ^ 2‖ ≤ 1 := by
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (by simp) ?_)
    rw [norm_mul, norm_pow, norm_pow, hz]
    have : ‖r‖ ^ 2 ≤ 1 := pow_le_one₀ hr0.le hr1.le
    simpa using this
  have hin : ‖E1 - E2 * (1 + r ^ 2 * z ^ 2)‖ ≤ ‖r‖ ^ 3 := by
    rw [sub_eq_add_neg]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hE1 ?_)
    rw [norm_neg, norm_mul]
    calc ‖E2‖ * ‖1 + r ^ 2 * z ^ 2‖ ≤ ‖E2‖ * 1 :=
          mul_le_mul_of_nonneg_left hu (norm_nonneg _)
      _ ≤ ‖r‖ ^ 3 := by rw [mul_one]; exact hE2
  rw [key, norm_div, h1E2, div_one, norm_mul]
  calc ‖r‖ * ‖E1 - E2 * (1 + r ^ 2 * z ^ 2)‖ ≤ ‖r‖ * ‖r‖ ^ 3 :=
        mul_le_mul_of_nonneg_left hin (norm_nonneg _)
    _ = ‖r‖ ^ 4 := by ring
