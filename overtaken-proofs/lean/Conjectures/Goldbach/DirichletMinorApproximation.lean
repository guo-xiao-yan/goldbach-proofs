import Mathlib

theorem Conjectures.Goldbach.DirichletMinorApproximation :
    let Q (n : ℕ) := (Nat.log 2 (n + 2)) ^ 2; let arcs (n : ℕ) := {t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ Q n ∧ a ≤ q ∧ Nat.Coprime a q ∧ |t - (a : ℝ) / q| ≤ (Q n : ℝ) / ((q : ℝ) * n)}; ∀ (n : ℕ) (t : ℝ), 1 ≤ Q n → Q n ≤ n → t ∈ Set.Icc (0 : ℝ) 1 → t ∉ arcs n → ∃ q a : ℕ, Q n < q ∧ q ≤ n / Q n ∧ a ≤ q ∧ Nat.Coprime a q ∧ |t - (a : ℝ) / q| ≤ 1 / ((q : ℝ) * (((n / Q n : ℕ) : ℝ) + 1)) := by
  intro Q arcs n t hQ1 hQn ht hnot
  obtain ⟨ht0, ht1⟩ := ht
  have hH : 1 ≤ n / Q n := (Nat.div_pos hQn hQ1)
  obtain ⟨q', hq', hden⟩ := Real.exists_rat_abs_sub_le_and_den_le t (n := n / Q n) hH
  set H := n / Q n with hHdef
  set d := q'.den with hd
  set m := q'.num with hm
  have hdpos : 0 < d := q'.den_pos
  have hdR : (0 : ℝ) < d := by exact_mod_cast hdpos
  have hqr : (q' : ℝ) = (m : ℝ) / d := by
    rw [Rat.cast_def]
  have hHR : (1 : ℝ) ≤ H := by exact_mod_cast hH
  rw [hqr] at hq'
  have hb : |t * d - m| ≤ 1 / 2 := by
    have : t * d - m = d * (t - m / d) := by field_simp
    rw [this, abs_mul, abs_of_pos hdR]
    calc (d : ℝ) * |t - m / d| ≤ d * (1 / ((d : ℝ) * (H + 1))) := by
          apply mul_le_mul_of_nonneg_left _ hdR.le
          have : (((H : ℝ) + 1) * d) = d * (H + 1) := by ring
          rw [this] at hq'; exact hq'
      _ = 1 / (H + 1) := by field_simp
      _ ≤ 1 / 2 := by
          apply one_div_le_one_div_of_le (by norm_num); linarith
  have hb' := abs_le.mp hb
  have htd0 : 0 ≤ t * d := by positivity
  have htd1 : t * d ≤ d := by nlinarith
  have hm0 : 0 ≤ m := by
    by_contra h
    push Not at h
    have : (m : ℝ) ≤ -1 := by exact_mod_cast (by omega : m ≤ -1)
    linarith
  have hmd : m ≤ d := by
    by_contra h
    push Not at h
    have : (d : ℝ) + 1 ≤ m := by exact_mod_cast (by omega : (d : ℤ) + 1 ≤ m)
    linarith
  have hmcast : ((m.toNat : ℕ) : ℝ) = (m : ℝ) := by
    have : ((m.toNat : ℕ) : ℤ) = m := Int.toNat_of_nonneg hm0
    exact_mod_cast this
  have hcop : Nat.Coprime m.toNat d := by
    have h5 : m.toNat = m.natAbs := by omega
    rw [h5]
    exact q'.reduced
  have hmle : m.toNat ≤ d := by omega
  refine ⟨d, m.toNat, ?_, hden, hmle, hcop, ?_⟩
  · by_contra hle
    push Not at hle
    apply hnot
    refine ⟨d, m.toNat, hdpos, hle, hmle, hcop, ?_⟩
    rw [hmcast]
    refine le_trans hq' ?_
    have hn : n < Q n * (H + 1) := by
      rw [hHdef]; exact Nat.lt_mul_div_succ n (by omega)
    have hnR : (n : ℝ) ≤ (Q n : ℝ) * (H + 1) := by exact_mod_cast hn.le
    have hnpos : (0 : ℝ) < n := by
      have : 0 < n := by omega
      exact_mod_cast this
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  · rw [hmcast]
    have : (d : ℝ) * (H + 1) = ((H : ℝ) + 1) * d := by ring
    rw [this]; exact hq'
