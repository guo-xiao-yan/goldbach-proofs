import Mathlib

private theorem qp_step (P : ℕ → Prop) [DecidablePred P] (h : ℕ → ℝ) (z : ℕ) (hz : 4 ≤ z) :
    ∏ p ∈ (Finset.Icc 5 (z + 1)).filter P, h p
      = (∏ p ∈ (Finset.Icc 5 z).filter P, h p) * (if P (z + 1) then h (z + 1) else 1) := by
  have hs : Finset.Icc 5 (z + 1) = insert (z + 1) (Finset.Icc 5 z) := by
    ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
  have hn : z + 1 ∉ Finset.Icc 5 z := by simp
  rw [hs, Finset.filter_insert]
  by_cases hP : P (z + 1)
  · rw [if_pos hP, if_pos hP, Finset.prod_insert (by simp), mul_comm]
  · rw [if_neg hP, if_neg hP, mul_one]

private theorem qp_factor (p : ℕ) (hp : 5 ≤ p) :
    (1 - 2 / (p : ℝ)) / (1 - 1 / (p : ℝ)) ^ 2 = 1 - 1 / ((p : ℝ) - 1) ^ 2 := by
  have h1 : (p : ℝ) ≥ 5 := by exact_mod_cast hp
  have h2 : (p : ℝ) ≠ 0 := by linarith
  have h3 : (p : ℝ) - 1 ≠ 0 := by linarith
  field_simp
  ring

private theorem qp_lower (P : ℕ → Prop) [DecidablePred P] (z : ℕ) (hz : 4 ≤ z) :
    (3 / 4 : ℝ) * ((z : ℝ) / ((z : ℝ) - 1)) ≤
      ∏ p ∈ (Finset.Icc 5 z).filter P, ((1 - 2 / (p : ℝ)) / (1 - 1 / (p : ℝ)) ^ 2) := by
  induction z, hz using Nat.le_induction with
  | base =>
    have : (Finset.Icc 5 4).filter P = ∅ := by
      ext x; simp only [Finset.mem_filter, Finset.mem_Icc, Finset.notMem_empty, iff_false]; omega
    rw [this]; norm_num
  | succ z hz ih =>
    rw [qp_step P _ z hz]
    have hz' : (4 : ℝ) ≤ z := by exact_mod_cast hz
    have hz1 : (0 : ℝ) < (z : ℝ) - 1 := by linarith
    have hfac := qp_factor (z + 1) (by omega)
    have hpos : 0 ≤ (3 / 4 : ℝ) * ((z : ℝ) / ((z : ℝ) - 1)) := by positivity
    have key : (3 / 4 : ℝ) * (((z + 1 : ℕ) : ℝ) / (((z + 1 : ℕ) : ℝ) - 1)) ≤
        (3 / 4 : ℝ) * ((z : ℝ) / ((z : ℝ) - 1)) * (1 - 1 / (((z + 1 : ℕ) : ℝ) - 1) ^ 2) := by
      push_cast
      have : (z : ℝ) + 1 - 1 = z := by ring
      rw [this]
      have hz0 : (z : ℝ) ≠ 0 := by linarith
      have hz2 : (z : ℝ) - 1 ≠ 0 := by linarith
      rw [show (3 / 4 : ℝ) * (((z : ℝ) + 1) / z) = (3/4) * (z / (z - 1)) * ((z - 1) * (z + 1) / z ^ 2) by
        field_simp]
      rw [show (1 : ℝ) - 1 / (z : ℝ) ^ 2 = (z - 1) * (z + 1) / z ^ 2 by field_simp; ring]
    split_ifs with hP
    · rw [hfac]
      exact key.trans (by
        apply mul_le_mul_of_nonneg_right ih
        have : (0 : ℝ) < 1 - 1 / (((z + 1 : ℕ) : ℝ) - 1) ^ 2 := by
          push_cast
          have : (z : ℝ) + 1 - 1 = z := by ring
          rw [this]
          have : (1 : ℝ) / (z : ℝ) ^ 2 < 1 := by
            rw [div_lt_one (by positivity)]; nlinarith
          linarith
        exact this.le)
    · rw [mul_one]
      refine le_trans ?_ ih
      push_cast
      have : (z : ℝ) + 1 - 1 = z := by ring
      rw [this]
      rw [← mul_div_assoc, ← mul_div_assoc, div_le_div_iff₀ (by positivity) hz1]
      nlinarith

theorem Conjectures.QuadraticPrimes.SieveEulerCorrection :
    let split := fun z : ℕ => (Finset.Icc 5 z).filter (fun p => Nat.Prime p ∧ p % 4 = 1); let correction := fun z : ℕ => ∏ p ∈ split z, (1 - 2/(p : ℝ)) / (1 - 1/(p : ℝ))^2;
    ∃ c : ℝ, 0<c ∧ Filter.Tendsto correction Filter.atTop (nhds c) := by
  intro split correction
  have hanti : Antitone correction := by
    apply antitone_nat_of_succ_le
    intro z
    by_cases hz : 4 ≤ z
    · show ∏ p ∈ split (z+1), _ ≤ ∏ p ∈ split z, _
      simp only [split]
      rw [qp_step _ _ z hz]
      have hpos : 0 ≤ ∏ p ∈ (Finset.Icc 5 z).filter (fun p => Nat.Prime p ∧ p % 4 = 1),
          ((1 - 2 / (p : ℝ)) / (1 - 1 / (p : ℝ)) ^ 2) := by
        apply Finset.prod_nonneg
        intro p hp
        have hp5 : 5 ≤ p := (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).1
        rw [qp_factor p hp5]
        have h1 : (5 : ℝ) ≤ p := by exact_mod_cast hp5
        have : 1 / ((p : ℝ) - 1) ^ 2 ≤ 1 := by
          rw [div_le_one (by nlinarith)]; nlinarith
        linarith
      split_ifs with hP
      · rw [qp_factor _ (by omega)]
        have h1 : (4 : ℝ) ≤ z := by exact_mod_cast hz
        have : 0 ≤ 1 / (((z + 1 : ℕ) : ℝ) - 1) ^ 2 := by positivity
        nlinarith
      · rw [mul_one]
    · have h1 : split (z+1) = ∅ := by
        ext x; simp only [split, Finset.mem_filter, Finset.mem_Icc, Finset.notMem_empty, iff_false]; omega
      have h2 : split z = ∅ := by
        ext x; simp only [split, Finset.mem_filter, Finset.mem_Icc, Finset.notMem_empty, iff_false]; omega
      show ∏ p ∈ split (z+1), _ ≤ ∏ p ∈ split z, _
      rw [h1, h2]
  have hlow : ∀ z, (3 / 4 : ℝ) ≤ correction z := by
    intro z
    by_cases hz : 4 ≤ z
    · refine le_trans ?_ (qp_lower (fun p => Nat.Prime p ∧ p % 4 = 1) z hz)
      have hz' : (4 : ℝ) ≤ z := by exact_mod_cast hz
      have hz1 : (0 : ℝ) < (z : ℝ) - 1 := by linarith
      have : (1 : ℝ) ≤ z / ((z : ℝ) - 1) := by
        rw [le_div_iff₀ hz1]; linarith
      nlinarith
    · have h2 : split z = ∅ := by
        ext x; simp only [split, Finset.mem_filter, Finset.mem_Icc, Finset.notMem_empty, iff_false]; omega
      show (3/4 : ℝ) ≤ ∏ p ∈ split z, _
      rw [h2]; norm_num
  have hbdd : BddBelow (Set.range correction) := ⟨3 / 4, by rintro _ ⟨z, rfl⟩; exact hlow z⟩
  refine ⟨⨅ z, correction z, ?_, tendsto_atTop_ciInf hanti hbdd⟩
  exact lt_of_lt_of_le (by norm_num) (le_ciInf hlow)
