import Mathlib

private lemma geomInt (ρ : ℝ) (h0 : 0 < ρ) (h1 : ρ < 1) (a : ℤ) :
    Summable (fun n : ℤ => ρ ^ (n - a).natAbs) := by
  have hg : Summable (fun n : ℕ => ρ ^ n) := summable_geometric_of_lt_one h0.le h1
  have base : Summable (fun n : ℤ => ρ ^ n.natAbs) := by
    apply Summable.of_nat_of_neg_add_one
    · simpa using hg
    · have := (summable_nat_add_iff 1).2 hg
      refine this.congr fun n => ?_
      show ρ ^ (n + 1) = ρ ^ (-((n : ℤ) + 1)).natAbs
      congr 1
  exact (Equiv.subRight a).summable_iff.2 base

private lemma summ_of_bound {K : Type} [NontriviallyNormedField K] [CompleteSpace K]
    (f : ℤ → K) (ρ c : ℝ) (h0 : 0 < ρ) (h1 : ρ < 1) (a : ℤ)
    (h : ∀ n, ‖f n‖ ≤ c * ρ ^ (n - a).natAbs) : Summable f :=
  Summable.of_norm_bounded ((geomInt ρ h0 h1 a).mul_left c) h

private lemma tsum_dom {K : Type} [NontriviallyNormedField K] [CompleteSpace K]
    [IsUltrametricDist K] (f : ℤ → K) (S : Finset ℤ) (A C : ℝ) (hf : Summable f)
    (hC0 : 0 ≤ C) (hC : C < A) (hS : ‖∑ i ∈ S, f i‖ = A) (hrest : ∀ n, n ∉ S → ‖f n‖ ≤ C) :
    ‖∑' n, f n‖ = A := by
  rw [← hf.sum_add_tsum_compl (s := S)]
  have h1 : ‖∑' i : ↥(S : Set ℤ)ᶜ, f i‖ ≤ C :=
    IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg hC0 (fun i => hrest i.1 (fun h => i.2 (Finset.mem_coe.2 h)))
  rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [hS]; exact (h1.trans_lt hC).ne'),
    hS, max_eq_left (h1.trans hC.le)]

private lemma tri (n : ℤ) : 2 * (n * (n + 1) / 2) = n * (n + 1) :=
  Int.mul_ediv_cancel' (Int.even_mul_succ_self n).two_dvd

private lemma tnorm {K : Type} [NontriviallyNormedField K] (r z : K) (l : ℕ) (hr : 0 < ‖r‖)
    (hz : ‖z‖ = 1) (n : ℤ) :
    ‖(r ^ (2 * l)) ^ (n * (n + 1) / 2) * z ^ (2 * n + 1)‖ = ‖r‖ ^ ((l : ℤ) * (n * (n + 1))) := by
  rw [norm_mul, norm_zpow, norm_zpow, norm_pow, hz, one_zpow, mul_one, ← zpow_natCast,
    ← zpow_mul]
  congr 1
  push_cast
  linear_combination (l : ℤ) * tri n

private lemma snorm {K : Type} [NontriviallyNormedField K] (r z : K) (l j : ℕ) (hr : 0 < ‖r‖)
    (hz : ‖z‖ = 1) (n : ℤ) :
    ‖(r ^ (2 * l)) ^ (n * (n + 1) / 2) * (r ^ j * z) ^ (2 * n + 1)‖
      = ‖r‖ ^ ((l : ℤ) * (n * (n + 1)) + (j : ℤ) * (2 * n + 1)) := by
  rw [norm_mul, norm_zpow, norm_zpow, norm_pow, norm_mul, norm_pow, hz, mul_one, ← zpow_natCast,
    ← zpow_mul, ← zpow_natCast, ← zpow_mul, ← zpow_add₀ hr.ne']
  congr 1
  push_cast
  linear_combination (l : ℤ) * tri n

theorem Conjectures.JoshiAbc.ThetaRatioNorm :
    ∀ (K : Type) [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K], let theta := fun (q u : K) => ∑' n : ℤ, q^(n*(n+1)/2) * u^(2*n+1); ∀ (r z : K) (l j : ℕ), 0 < ‖r‖ → ‖r‖ < 1 → ‖z‖=1 → ‖z+z⁻¹‖=1 → 0 < j → j < l → ‖theta (r^(2*l)) z / theta (r^(2*l)) (r^j*z)‖ = ‖r‖^j := by
  intro K _ _ _ theta r z l j hr0 hr1 hz hzz hj hjl
  set ρ := ‖r‖ with hρ
  have hz0 : z ≠ 0 := by intro h; rw [h, norm_zero] at hz; exact zero_ne_one hz
  have hl : (2 : ℤ) ≤ l := by exact_mod_cast (by omega : 2 ≤ l)
  have hj1 : (1 : ℤ) ≤ j := by exact_mod_cast hj
  have hjl' : (j : ℤ) + 1 ≤ l := by exact_mod_cast hjl
  -- numerator
  have hnum : ‖theta (r ^ (2 * l)) z‖ = 1 := by
    simp only [theta]
    have hsum : Summable (fun n : ℤ => (r ^ (2 * l)) ^ (n * (n + 1) / 2) * z ^ (2 * n + 1)) := by
      apply summ_of_bound _ ρ (ρ⁻¹) hr0 hr1 0
      intro n
      rw [tnorm r z l hr0 hz n]
      have e : ρ⁻¹ * ρ ^ (n - 0).natAbs = ρ ^ (((n - 0).natAbs : ℤ) - 1) := by
        rw [zpow_sub₀ hr0.ne', zpow_one, zpow_natCast]; ring
      rw [e]
      apply zpow_le_zpow_right_of_le_one₀ hr0 hr1.le
      have h1 : (0 : ℤ) ≤ n * (n + 1) := by
        rcases le_total 0 n with h | h
        · nlinarith
        · have : n + 1 ≤ 0 ∨ n = 0 := by omega
          rcases this with h' | h'
          · nlinarith
          · subst h'; norm_num
      have h3 : n * (n + 1) ≤ (l : ℤ) * (n * (n + 1)) := by nlinarith
      rcases le_total 0 n with h | h
      · rw [sub_zero, Int.natCast_natAbs, abs_of_nonneg h]; nlinarith
      · rw [sub_zero, Int.natCast_natAbs, abs_of_nonpos h]; nlinarith [sq_nonneg (n + 1)]
    apply tsum_dom _ {0, -1} 1 ρ hsum hr0.le hr1
    · rw [Finset.sum_pair (by norm_num)]
      have : (r ^ (2 * l)) ^ (0 * (0 + 1) / 2 : ℤ) * z ^ (2 * (0:ℤ) + 1)
          + (r ^ (2 * l)) ^ (-1 * (-1 + 1) / 2 : ℤ) * z ^ (2 * (-1 : ℤ) + 1) = z + z⁻¹ := by
        norm_num
      rw [this, hzz]
    · intro n hn
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hn
      rw [tnorm r z l hr0 hz n]
      calc ρ ^ ((l : ℤ) * (n * (n + 1))) ≤ ρ ^ (1 : ℤ) := by
            apply zpow_le_zpow_right_of_le_one₀ hr0 hr1.le
            have : 1 ≤ n * (n + 1) := by
              rcases lt_trichotomy n 0 with h | h | h
              · have : n ≤ -2 := by omega
                nlinarith
              · exact absurd h hn.1
              · nlinarith
            nlinarith
        _ = ρ := zpow_one _
  have hden : ‖theta (r ^ (2 * l)) (r ^ j * z)‖ = ρ ^ (-(j : ℤ)) := by
    simp only [theta]
    have key : ∀ n : ℤ, n ≠ -1 →
        -(j : ℤ) + |n + 1| ≤ (l : ℤ) * (n * (n + 1)) + (j : ℤ) * (2 * n + 1) := by
      intro n hn
      have hid : (l : ℤ) * (n * (n + 1)) + (j : ℤ) * (2 * n + 1) - (-(j : ℤ))
          = (n + 1) * ((l : ℤ) * n + 2 * j) := by ring
      rcases lt_trichotomy n (-1) with h | h | h
      · rw [abs_of_neg (by omega)]
        have a' : n + 1 ≤ 0 := by omega
        have b' : (l : ℤ) * n + 2 * j + 1 ≤ 0 := by nlinarith
        nlinarith [mul_nonneg (neg_nonneg.2 a') (neg_nonneg.2 b')]
      · exact absurd h hn
      · rw [abs_of_nonneg (by omega)]
        have a' : 0 ≤ n + 1 := by omega
        have b' : 0 ≤ (l : ℤ) * n + 2 * j := by nlinarith
        nlinarith [mul_nonneg a' b']
    have hsum : Summable
        (fun n : ℤ => (r ^ (2 * l)) ^ (n * (n + 1) / 2) * (r ^ j * z) ^ (2 * n + 1)) := by
      apply summ_of_bound _ ρ (ρ ^ (-(j : ℤ))) hr0 hr1 (-1)
      intro n
      rw [snorm r z l j hr0 hz n]
      have e : ρ ^ (-(j : ℤ)) * ρ ^ (n - -1).natAbs = ρ ^ (-(j : ℤ) + |n + 1|) := by
        rw [← zpow_natCast, ← zpow_add₀ hr0.ne']
        congr 1
        rw [sub_neg_eq_add, Int.natCast_natAbs]
      rw [e]
      apply zpow_le_zpow_right_of_le_one₀ hr0 hr1.le
      by_cases hn : n = -1
      · subst hn; norm_num
      · exact key n hn
    apply tsum_dom _ {-1} _ (ρ ^ (-(j : ℤ)) * ρ) hsum (by positivity) _ _ _
    · have : 0 < ρ ^ (-(j : ℤ)) := zpow_pos hr0 _
      nlinarith
    · rw [Finset.sum_singleton, snorm r z l j hr0 hz]
      congr 1
      ring
    · intro n hn
      simp only [Finset.mem_singleton] at hn
      rw [snorm r z l j hr0 hz n]
      calc ρ ^ ((l : ℤ) * (n * (n + 1)) + (j : ℤ) * (2 * n + 1))
          ≤ ρ ^ (-(j : ℤ) + 1) := by
            apply zpow_le_zpow_right_of_le_one₀ hr0 hr1.le
            have := key n hn
            have : 1 ≤ |n + 1| := Int.one_le_abs (by omega)
            omega
        _ = _ := by rw [zpow_add₀ hr0.ne', zpow_one]
  show ‖(∑' n : ℤ, (r ^ (2 * l)) ^ (n * (n + 1) / 2) * z ^ (2 * n + 1)) /
      ∑' n : ℤ, (r ^ (2 * l)) ^ (n * (n + 1) / 2) * (r ^ j * z) ^ (2 * n + 1)‖ = ρ ^ j
  have hnum' : ‖∑' n : ℤ, (r ^ (2 * l)) ^ (n * (n + 1) / 2) * z ^ (2 * n + 1)‖ = 1 := hnum
  have hden' : ‖∑' n : ℤ, (r ^ (2 * l)) ^ (n * (n + 1) / 2) * (r ^ j * z) ^ (2 * n + 1)‖
      = ρ ^ (-(j : ℤ)) := hden
  rw [norm_div, hnum', hden', zpow_neg, zpow_natCast, one_div, inv_inv]
